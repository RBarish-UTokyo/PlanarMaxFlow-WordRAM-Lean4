module

public import PlanarFlow.BKMNW.ReadMach
public import PlanarFlow.NegSSSP.CornerProg
public import PlanarFlow.NegSSSP.FaceKleinEnc
public import PlanarFlow.NegSSSP.NodeRunA

/-!
# One part of a node as one run: corners, Klein's program from memory, the reading

At a node of the decomposition by simple cycles (`SplitF`), the part `X` (`P₀` or `P₁`) needs
the dense distance graph `childDDG N mssp X ℓ δ B` of the step in the row-major layout of
`NegSSSP.bfStartP`, in the order of the face of its one-face instance. `kPart` does it in **one
run**, in a configuration holding the inputs above the work space of Klein's program:

1. `kpC ; cornerProg`: the boundary (listed by vertex number at `Lb`, any order) sorted along the
   face of the instance from the positions on the face (a table at `Pb` by vertex number, an
   input): the order `β'` (vertex numbers at `Ob`) and the source indices (at `Sb`);
2. `kpK ; cpyProg`: the real constants of Klein's encoding copied from `Rk` to the low real
   memory `[0, 3 nD + 3)` (the natural cells copied go to a scratch region);
3. `zeroRegs (List.range 201)`: the registers of Klein's program cleared;
4. `kleinProgMem`: Klein's program reading the input words of the encoding at `β`
   (`NegSSSP.splitF_exec_enc`);
5. `kpR ; rdProg`: the answers read into the flags and lengths of `bfStartP` (`NegSSSP.rdProg`).

The encoding of the one-face instance in memory (`KSlot`: the input words at `β`, the real
constants at `Rk`) and the positions of the boundary vertices on the face are **inputs**.

* `KSlot.enc`: after the copy, the configuration holds `Klein.KleinEnc`.
* `exec_frame`: a run of a statement naming only registers in `U` (no input, no random word)
  also has a run keeping the other registers (by `WordRAM.Machine.Exec.lift`).
* `rdProg_exec'`: `rdProg_exec` with the registers `≥ 341` kept.
* `kpart_exec`: **the run of one part**: there are the instance `fd` and its encoding with
  `KPartRun` (the layout `KLay`): the order `β'` of the boundary (an enumeration, the crossing
  inequality of `childDDG` in this order), the flags `finB (arcOf H β')` and the lengths
  `matOf H β'` of `H = childDDG N mssp X ℓ δ B` at `Ys + 3 S + (s b + t)`; within
  `3 · 32886 · 2372500000 · m lg m + rdCost b L nD + 19 k + 10 b + 33 nD + 300` steps; the
  registers `752 … 899` and `≥ 919`, the natural memory above the work space of Klein's program
  outside the five regions of the part, the real memory there and above `3 nD + 3`, and the
  output are kept; the natural memory of the work space stays bounded by its bound
  (`Kw = Bw + 16 (n + 1)`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge

/-! ### The encoding of a one-face instance in a slot -/

section Enc

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **The encoding of a one-face instance in a slot**: the input words at `β` (as in
`Klein.KleinEnc`), and the real constants of `Klein.KleinEnc` at `Rk + a` instead of `a`. -/
structure KSlot (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ) {nD : ℕ}
    (σ : D ≃ Fin nD) (B n β Rk W' : ℕ) (P : Input) (d : Config) : Prop where
  dat : InData P (B + 16 * (n + 1)) β P.data.length W' d
  wt : ∀ x, d.rmem (Rk + (Klein.aWT + σ x)) = Klein.tripWt M k g S ℓ 0 x
  ph : ∀ x, d.rmem (Rk + (Klein.aPH nD + σ x)) = Klein.tripφ S ℓ x
  tl : d.rmem (Rk + Klein.aTL nD) = Klein.tripL V S ℓ
  th : d.rmem (Rk + Klein.aTH nD) = Klein.tripTh V S ℓ
  h0 : d.rmem (Rk + Klein.aH0 nD) = Klein.tripH0 V S ℓ k

/-- After the real constants are copied down: `Klein.KleinEnc`. -/
theorem KSlot.enc {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ} {nD : ℕ}
    {σ : D ≃ Fin nD} {B n β Rk W' : ℕ} {P : Input} {c d : Config}
    (h : KSlot M k g S ℓ σ B n β Rk W' P c)
    (hr : ∀ i < 3 * nD + 3, d.rmem i = c.rmem (Rk + i))
    (hn : ∀ i ≤ B + 16 * (n + 1), d.nmem (β + i) = c.nmem (β + i)) :
    Klein.KleinEnc M k g S ℓ σ B n β W' P d where
  dat := ⟨h.dat.lt, h.dat.le, h.dat.len, fun i hi => (hn i hi).trans (h.dat.mem i hi)⟩
  wt x := by
    have := (σ x).2
    rw [hr _ (by unfold Klein.aWT; omega)]; exact h.wt x
  ph x := by
    have := (σ x).2
    rw [hr _ (by unfold Klein.aPH; omega)]; exact h.ph x
  tl := by rw [hr _ (by unfold Klein.aTL; omega)]; exact h.tl
  th := by rw [hr _ (by unfold Klein.aTH; omega)]; exact h.th
  h0 := by rw [hr _ (by unfold Klein.aH0; omega)]; exact h.h0

end Enc

/-! ### A frame for the registers -/

variable {I : Input} {W : ℕ}

/-- **A register frame for free**: a run of a statement naming only the registers in `U`, with
no input and no random word, is matched by a run (to a configuration agreeing with the end on
`U` and the memory `≤ W`) keeping the registers outside `U` and the memory above `W`. -/
theorem exec_frame {s : Stmt} {c c' : Config} {k : ℕ} {U : ℕ → Bool} (h : Exec I W s c c' k)
    (hs : s.regsOK U = true) (hn : s.noInp = true) (hr : s.noRand = true) :
    ∃ d', Exec I W s c d' k ∧ Agree U W c' d' ∧ Keep U W c d' ∧
      d'.output = c'.output := by
  obtain ⟨d', e, hA, hK, L, o, o'⟩ :=
    Exec.lift (P' := I) h hs hn hr le_rfl
      ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ h.wb_left
  exact ⟨d', e, hA, hK, by rw [o', o]⟩

/-- The registers of `rdProg` are below `341`. -/
theorem rdProg_regsOK : rdProg.regsOK (fun r => decide (r < 341)) = true := by kernel_rfl

theorem rdProg_noInp : rdProg.noInp = true := by kernel_rfl

theorem rdProg_noRand : rdProg.noRand = true := by kernel_rfl

/-- **`rdProg_exec` with the registers `≥ 341` kept.** -/
theorem rdProg_exec' {R : Rd} (hL : RdLay R W) (hWL : R.Wr ≤ (2 : ℝ) ^ R.L) (c : Config)
    (hc : WordsBounded W c) (hI : RdIn R c) :
    ∃ c' k, Exec I W rdProg c c' k ∧ k ≤ rdCost R.b R.L R.M ∧
      (∀ s < R.b, ∀ t < R.b, R.Out c c' s t) ∧
      (∀ a, (a < R.Fb ∨ R.Fb + R.b * R.b ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < R.Lb ∨ R.Lb + R.b * R.b ≤ a) → c'.rmem a = c.rmem a) ∧
      (∀ r, r < 311 ∨ 341 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  obtain ⟨c', k, e, hk, hO, hn, hr, hreg, ho⟩ := rdProg_exec (P := I) hL hWL c hc hI
  obtain ⟨d', e', hA, hK, ho'⟩ := exec_frame e rdProg_regsOK rdProg_noInp rdProg_noRand
  have hnm : ∀ a, d'.nmem a = c'.nmem a := fun a => by
    by_cases ha : a ≤ W
    · exact hA.nmem a ha
    · rw [hK.nmem a (by omega), hn a (Or.inr (by have := hL.wF; omega))]
  have hrm : ∀ a, d'.rmem a = c'.rmem a := fun a => by
    by_cases ha : a ≤ W
    · exact hA.rmem a ha
    · rw [hK.rmem a (by omega), hr a (Or.inr (by have := hL.wL; omega))]
  refine ⟨d', k, e', hk, fun s hs t ht => ?_, fun a ha => by rw [hnm]; exact hn a ha,
    fun a ha => by rw [hrm]; exact hr a ha, fun r hr' => ?_, by rw [ho', ho]⟩
  · obtain ⟨o1, o2, o3⟩ := hO s hs t ht
    exact ⟨by rw [hnm]; exact o1, fun h => by rw [hrm]; exact o2 h,
      fun h h' => by rw [hrm]; exact o3 h h'⟩
  · rcases hr' with hr' | hr'
    · rw [hA.nreg r (by simp; omega)]; exact hreg r hr'
    · exact hK.nreg r (by simp; omega)

/-! ### The setting of the registers -/

/-- Before `cornerProg`: `r10 = 1`, the size `k` of the face, `b` (from `r802`), the bases of
the list (`r960`), of the positions (`Pb`), of the table (`r961`) and of the outputs (`r962`,
`r963`). -/
def kpC (k Pb : ℕ) : Stmt :=
  block [.constN 10 1, .constN 740 k, .copyN 741 802, .copyN 742 960, .constN 743 Pb,
    .copyN 744 961, .copyN 745 962, .copyN 746 963]

/-- Before the copy of the real constants: `3 nD + 3` cells from `Rk` to `0` (real), the
natural cells to the scratch region `r965`. -/
def kpK (nD Rk : ℕ) : Stmt :=
  block [.constN 910 (3 * nD + 3), .copyN 911 965, .constN 912 Rk, .constN 913 0, .constN 914 Rk]

/-- Before `rdProg`: the data of `RdIn`. -/
def kpR (k nD n L : ℕ) (Wr : ℤ) : Stmt :=
  block [.copyN 300 802, .copyN 301 963, .copyN 302 962, .copyN 303 966, .constN 304 n,
    .constN 305 (3 * nD + 3), .constN 306 k, .copyN 307 964, .copyN 308 964, .constN 309 L,
    .constN 310 nD, .constR 301 Wr]

/-- **One part of a node** (see the module docstring). -/
def kPart (k nD n Bw len β Rk Pb L : ℕ) (Wr : ℤ) : Stmt :=
  .seq (kpC k Pb) <| .seq cornerProg <| .seq (kpK nD Rk) <| .seq cpyProg <|
  .seq (zeroRegs (List.range 201)) <| .seq (Klein.kleinProgMem Bw nD n k k β len) <|
  .seq (kpR k nD n L Wr) rdProg

theorem kpC_exec {k Pb : ℕ} (hk : k ≤ W) (hP : Pb ≤ W) (c : Config) (hc : WordsBounded W c)
    (h1 : 1 ≤ W) :
    ∃ c' t, Exec I W (kpC k Pb) c c' t ∧ t = 8 ∧ c'.nreg 10 = 1 ∧ c'.nreg 740 = k ∧
      c'.nreg 741 = c.nreg 802 ∧ c'.nreg 742 = c.nreg 960 ∧ c'.nreg 743 = Pb ∧
      c'.nreg 744 = c.nreg 961 ∧ c'.nreg 745 = c.nreg 962 ∧ c'.nreg 746 = c.nreg 963 ∧
      (∀ r, r ≠ 10 → (r < 740 ∨ 746 < r) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kpC
  exec_block
  all_goals try omega
  config_simp
  intro r h1 h2; simp (disch := omega) only [upd_other]

theorem kpK_exec {nD Rk : ℕ} (hn : 3 * nD + 3 ≤ W) (hR : Rk ≤ W) (c : Config)
    (hc : WordsBounded W c) :
    ∃ c' t, Exec I W (kpK nD Rk) c c' t ∧ t = 5 ∧ c'.nreg 910 = 3 * nD + 3 ∧
      c'.nreg 911 = c.nreg 965 ∧ c'.nreg 912 = Rk ∧ c'.nreg 913 = 0 ∧ c'.nreg 914 = Rk ∧
      (∀ r, (r < 910 ∨ 914 < r) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kpK
  exec_block
  all_goals try omega
  config_simp
  intro r h1; simp (disch := omega) only [upd_other]

theorem kpR_exec {k nD n L : ℕ} {Wr : ℤ} (hk : k ≤ W) (hnD : 3 * nD + 3 ≤ W) (hn : n ≤ W)
    (hL : L ≤ W) (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec I W (kpR k nD n L Wr) c c' t ∧ t = 12 ∧ c'.nreg 300 = c.nreg 802 ∧
      c'.nreg 301 = c.nreg 963 ∧ c'.nreg 302 = c.nreg 962 ∧ c'.nreg 303 = c.nreg 966 ∧
      c'.nreg 304 = n ∧ c'.nreg 305 = 3 * nD + 3 ∧ c'.nreg 306 = k ∧
      c'.nreg 307 = c.nreg 964 ∧ c'.nreg 308 = c.nreg 964 ∧ c'.nreg 309 = L ∧
      c'.nreg 310 = nD ∧ c'.rreg 301 = Wr ∧
      (∀ r, (r < 300 ∨ 310 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kpR
  exec_block
  all_goals try omega
  config_simp
  intro r h1; simp (disch := omega) only [upd_other]

/-! ### The layout of a part -/

/-- **The layout of `kPart`**: the five regions of the part `Ys + i S` (`i < 5`: the table and
the two outputs of `cornerProg`, the output of `rdProg`, the scratch of the copy), above the
work space `[0, Kw]` of Klein's program and the arrays it leaves (`n + k²`, `3 nD + 3 + k²`);
the inputs (the list `Lb` of `b` vertex numbers, the positions `Pb` and the potentials `δb` by
vertex number, the input words at `β`, the real constants at `Rk`) above the work space and
apart from the regions; everything below the word bound `W'`. -/
structure KLay (b w k nD n Kw L Lb Pb δb Ys S β Rk W' : ℕ) : Prop where
  sk : k ≤ S
  sb : b ≤ S
  sbb : b * b ≤ S
  snD : 3 * nD + 3 ≤ S
  kY : Kw < Ys
  rbY : n + k * k ≤ Ys
  outY : 3 * nD + 3 + k * k ≤ Ys
  yW : Ys + 5 * S ≤ W'
  lK : Kw < Lb
  lY : Lb + b ≤ Ys ∨ Ys + 5 * S ≤ Lb
  lW : Lb + b ≤ W'
  pK : Kw < Pb
  pY : Pb + w ≤ Ys ∨ Ys + 5 * S ≤ Pb
  pW : Pb + w ≤ W'
  dK : Kw < δb
  dnD : 3 * nD + 3 ≤ δb
  dY : δb + w ≤ Ys ∨ Ys + 5 * S ≤ δb
  dW : δb + w ≤ W'
  bY : β + Kw < Ys ∨ Ys + 5 * S ≤ β
  rK : Kw < Rk
  rnD : 3 * nD + 3 ≤ Rk
  rY : Rk + (3 * nD + 3) ≤ Ys ∨ Ys + 5 * S ≤ Rk
  rW : Rk + (3 * nD + 3) ≤ W'
  bbW : b * b + 1 ≤ W'
  lLW : L + 1 ≤ W'
  wW : w + 1 ≤ W'

section Part

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- **The run of one part** (the conclusion of `kpart_exec` for the instance `fd` and its
encoding): from every configuration holding the inputs in the layout `KLay`, `kPart` runs to the
order `β'` of the boundary and the matrices of `bfStartP` for `childDDG N mssp X ℓ δ B`. -/
def KPartRun (N : CombMap D V F) (P P₀ P₁ X : Finset D) (ℓ : D → ℤ) (δ : V → ℤ)
    (mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ)
    (fd : FaceData N X (bdry N P₀ P₁)) (n Bw : ℕ)
    (σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k))) (Pk : Input) :
    Prop :=
  ∀ {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}, NodeEnc N P₀ P₁ m w e ν ι →
  ∀ {src : ℕ → V}, IsEnum b src (bdry N P₀ P₁) →
  ∀ (L Lb Pb δb Ys S β Rk W' : ℕ) (I : Input) (c : Config),
    KLay b w fd.k (Fintype.card (Klein.SrcD fd.DQ fd.k)) n (Bw + 16 * (n + 1)) L Lb Pb δb
      Ys S β Rk W' →
    ((Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ)) : ℤ) : ℝ) ≤
      2 ^ L →
    WordsBounded W' c →
    c.nreg 802 = b → c.nreg 960 = Lb → c.nreg 961 = Ys → c.nreg 962 = Ys + S →
    c.nreg 963 = Ys + 2 * S → c.nreg 964 = Ys + 3 * S → c.nreg 965 = Ys + 4 * S →
    c.nreg 966 = δb →
    (∀ i < b, c.nmem (Lb + i) = ν (src i)) →
    (∀ x ∈ bdry N P₀ P₁, c.nmem (Pb + ν x) < fd.k ∧
      fd.Q.tail (fd.g (c.nmem (Pb + ν x))) = fd.j x) →
    (∀ v < w, c.rmem (δb + v) = δ (ι v)) →
    KSlot (Klein.srcMap fd.inst.cycle) fd.k (Klein.srcG fd.inst.cycle)
      (Klein.srcPiece fd.k (fd.P'.image fd.e))
      (MSSP.pert (Klein.srcLen (faceLen fd.P' fd.e (redLen N ℓ δ))
        (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ))))) σ Bw n β Rk
      W' Pk c →
    (∀ a ≤ Bw + 16 * (n + 1), c.nmem a ≤ Bw + 16 * (n + 1)) →
    ∃ c' t, ∃ β' : ℕ → V,
      Exec I W' (kPart fd.k (Fintype.card (Klein.SrcD fd.DQ fd.k)) n Bw Pk.data.length β Rk
        Pb L (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ)))) c c' t ∧
      t ≤ 3 * (32886 * 2372500000 * P.card * lg P.card) +
        rdCost b L (Fintype.card (Klein.SrcD fd.DQ fd.k)) + 19 * fd.k + 10 * b +
        33 * Fintype.card (Klein.SrcD fd.DQ fd.k) + 300 ∧
      IsEnum b β' (bdry N P₀ P₁) ∧ (∀ x < b, c'.nmem (Ys + S + x) = ν (β' x)) ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp X ℓ δ (bdry N P₀ P₁)).len (β' i)
        (β' i')) ∧
      (∀ s < b, ∀ t < b,
        c'.nmem (Ys + 3 * S + (s * b + t)) =
            finB (arcOf (childDDG N mssp X ℓ δ (bdry N P₀ P₁)) β') s t ∧
          c'.rmem (Ys + 3 * S + (s * b + t)) =
            (matOf (childDDG N mssp X ℓ δ (bdry N P₀ P₁)) β' s t : ℝ)) ∧
      (∀ r, (752 ≤ r ∧ r < 900) ∨ 919 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, Bw + 16 * (n + 1) < a → (a < Ys ∨ Ys + 5 * S ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, Bw + 16 * (n + 1) < a → 3 * Fintype.card (Klein.SrcD fd.DQ fd.k) + 3 ≤ a →
        (a < Ys ∨ Ys + 5 * S ≤ a) → c'.rmem a = c.rmem a) ∧
      (∀ a ≤ Bw + 16 * (n + 1), c'.nmem a ≤ Bw + 16 * (n + 1)) ∧
      c'.output = c.output

set_option maxHeartbeats 4000000 in
/-- **One part of a node as one run** (see the module docstring): for the part `X` of a node
meeting `SplitF`, with the reduced lengths `redLen N ℓ δ` nonnegative, there are the one-face
instance `fd` of `splitF_exec_enc` and its encoding (`n`, `Bw`, `σ`, `Pk`) such that, from
every configuration holding the inputs in the layout `KLay` (the bases in the registers
`960 … 966`, `b` in `r802`), with the encoding in a slot (`KSlot`), the positions on the face
at `Pb`, the cut of the instance below `2 ^ L`, and the natural memory of the work space bounded
by its bound, `kPart` runs to the order `β'` (vertex numbers at `Ys + S`) and the matrices of
`bfStartP` for `childDDG N mssp X ℓ δ B` in this order at `Ys + 3 S`. -/
theorem kpart_exec {P P₀ P₁ : Finset D} (h : SplitF N P P₀ P₁)
    (hB : (bdry N P₀ P₁).Nonempty) {ℓ : D → ℤ} {δ : V → ℤ} {X : Finset D}
    (hX : X = P₀ ∨ X = P₁) (hnn : ∀ d ∈ X, 0 ≤ redLen N ℓ δ d)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp) :
    ∃ fd : FaceData N X (bdry N P₀ P₁), ∃ (n Bw : ℕ)
      (σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k))) (Pk : Input),
      fd.q = 18 * P.card ∧
      KPartRun N P P₀ P₁ X ℓ δ mssp fd n Bw σ Pk := by
  classical
  obtain ⟨fd, n, Bw, σ, Pk, hq, hrun⟩ := splitF_exec_enc (ℓ := redLen N ℓ δ) h hB hX hnn
  refine ⟨fd, n, Bw, σ, Pk, hq, ?_⟩
  unfold KPartRun
  intro m w b e ν ι hN src hsrc L Lb Pb δb Ys S β Rk W' I c hL hWL hc r802 r960 r961 r962 r963
    r964 r965 r966 hsl hpos hδ hK hlow
  set nD := Fintype.card (Klein.SrcD fd.DQ fd.k) with hnD
  set Kw := Bw + 16 * (n + 1) with hKw
  set Wr := Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ)) with hWr
  obtain ⟨sk, sb, sbb, snD, kY, rbY, outY, yW, lK, lY, lW, pK, pY, pW, dK, dnD, dY, dW, bY, rK, rnD,
    rY, rW, bbW, lLW, wW⟩ := hL
  have hνlt : ∀ i < b, ν (src i) < w := fun i hi => hN.lt _ (bdry_sub_verts (hsrc.mem i hi))
  -- 1. the registers of `cornerProg`
  obtain ⟨c₁, t₁, e₁, ht₁, g10, g740, g741, g742, g743, g744, g745, g746, gn₁, -, gnm₁, grm₁,
    go₁⟩ := kpC_exec (I := I) (k := fd.k) (Pb := Pb) (by pomega) (by pomega) c hc (by pomega)
  -- 2. the corners
  have hCL : CornerLay fd.k b w Lb Pb Ys (Ys + S) (Ys + 2 * S) W' (fun i => ν (src i)) :=
    ⟨hνlt, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega,
      by pomega, by pomega, by pomega, by pomega, by pomega, by pomega⟩
  have hCI : CornerIn fd.k b Lb Pb Ys (Ys + S) (Ys + 2 * S) (fun i => ν (src i)) c₁ :=
    ⟨g10, g740, by rw [g741, r802], by rw [g742, r960], g743, by rw [g744, r961],
      by rw [g745, r962], by rw [g746, r963], fun i hi => by rw [gnm₁]; exact hsl i hi⟩
  obtain ⟨c₂, t₂, β', e₂, ht₂, -, hen, hO₂, hS₂, hcr, hfr₂, hcf₂⟩ :=
    cornerProg_crossingO (P := I) fd.inst hsrc hCL c₁ e₁.wb_right hCI
      (fun i hi => by rw [gnm₁]; exact hpos _ (hsrc.mem i hi))
  have hR₂ : ∀ r, (752 ≤ r ∧ r < 900) ∨ 919 ≤ r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [hcf₂.nreg r (by pomega), gn₁ r (by pomega) (by pomega)]
  -- 3., 4. the real constants copied down
  obtain ⟨c₃, t₃, e₃, ht₃, k910, k911, k912, k913, k914, gn₃, -, gnm₃, grm₃, go₃⟩ :=
    kpK_exec (I := I) (nD := nD) (Rk := Rk) (by pomega) (by pomega) c₂ e₂.wb_right
  have hCp : CpyLay (3 * nD + 3) (Ys + 4 * S) Rk 0 Rk W' :=
    ⟨by pomega, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega⟩
  obtain ⟨c₄, t₄, e₄, ht₄, hcp₄, hn₄, hr₄, hreg₄, -, ho₄⟩ := cpyProg_exec (P := I) hCp c₃
    e₃.wb_right k910 (by rw [k911, hR₂ 965 (by pomega), r965]) k912 k913 k914
  have hR₄ : ∀ r, (752 ≤ r ∧ r < 900) ∨ 919 ≤ r → c₄.nreg r = c.nreg r := fun r hr => by
    rw [hreg₄ r (by pomega), gn₃ r (by pomega), hR₂ r hr]
  -- 5. the registers of Klein's program cleared
  obtain ⟨c₅, t₅, e₅, ht₅, hz₅, -, hnm₅, hrm₅, ho₅⟩ :=
    zeroRegs_exec (P := I) (List.range 201) c₄ e₄.wb_right
  have hR₅ : ∀ r, (752 ≤ r ∧ r < 900) ∨ 919 ≤ r → c₅.nreg r = c.nreg r := fun r hr => by
    rw [hz₅ r, ite_eq_right_of_eq_false _ _ (eq_false (by simp; pomega)), hR₄ r hr]
  -- the natural memory outside the regions, up to here
  have hm₅ : ∀ a, (a < Ys ∨ Ys + 5 * S ≤ a) → c₅.nmem a = c.nmem a := fun a ha => by
    rw [hnm₅, hn₄ a (by pomega), gnm₃, hfr₂ a (by pomega) (by pomega) (by pomega), gnm₁]
  -- 6. Klein's program
  have hE := hK.enc (d := c₅)
    (fun i hi => by
      have := (hcp₄ i hi).2; rw [zero_add] at this
      rw [hrm₅, this, grm₃, hcf₂.rmem, grm₁])
    (fun i hi => hm₅ _ (by pomega))
  obtain ⟨d', s₆, e₆, hs₆, hR₆, ho₆, h1₆, -, h3₆, h4₆, h5₆⟩ := hrun I W' β c₅ e₅.wb_right
    (fun r hr => by rw [hz₅ r, ite_eq_left_of_eq_true _ _ (eq_true (by simp; omega))]; exact Nat.zero_le _)
    (fun a ha => by rw [hm₅ a (by pomega)]; exact hlow a ha) hE
  have hQ₆ : ∀ r, (752 ≤ r ∧ r < 900) ∨ 919 ≤ r → d'.nreg r = c.nreg r := fun r hr => by
    rw [h1₆ r (by pomega), hR₅ r hr]
  -- 7. the registers of `rdProg`
  obtain ⟨c₇, t₇, e₇, ht₇, q300, q301, q302, q303, q304, q305, q306, q307, q308, q309, q310,
    w301, gn₇, gnm₇, grm₇, go₇⟩ := kpR_exec (I := I) (k := fd.k) (nD := nD) (n := n) (L := L)
      (Wr := Wr) (by pomega) (by pomega) (by pomega) (by pomega) d' e₆.wb_right
  -- 8. the reading
  let R : Rd := ⟨b, fd.k, w, Ys + 2 * S, Ys + S, δb, n, 3 * nD + 3, Ys + 3 * S, Ys + 3 * S, L,
    nD, fun s => c₂.nmem (Ys + 2 * S + s), fun s => ν (β' s), (Wr : ℝ)⟩
  have hm₇ : ∀ a, Kw < a → a < Ys + 4 * S → c₇.nmem a = c₂.nmem a :=
    fun a ha ha' => by rw [gnm₇, h3₆ a ha, hnm₅, hn₄ a (by pomega), gnm₃]
  have hRL : RdLay R W' := by
    refine ⟨fun s hs => (hS₂ s hs).1, fun s hs => hN.lt _ (bdry_sub_verts (hen.mem s hs)),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [R]; pomega
  have hR₇ : ∀ r, (752 ≤ r ∧ r < 900) ∨ 919 ≤ r → c₇.nreg r = c.nreg r := fun r hr => by
    rw [gn₇ r (by pomega), hQ₆ r hr]
  have hRI : RdIn R c₇ := by
    refine ⟨?_, ?_, ?_, ?_, q304, q305, q306, ?_, ?_, q309, q310, w301, fun s hs => ?_,
      fun s hs => ?_⟩
    · rw [q300, hQ₆ 802 (by pomega), r802]
    · rw [q301, hQ₆ 963 (by pomega), r963]
    · rw [q302, hQ₆ 962 (by pomega), r962]
    · rw [q303, hQ₆ 966 (by pomega), r966]
    · rw [q307, hQ₆ 964 (by pomega), r964]
    · rw [q308, hQ₆ 964 (by pomega), r964]
    · dsimp only [R] at hs ⊢; exact hm₇ _ (by pomega) (by pomega)
    · dsimp only [R] at hs ⊢; rw [hm₇ _ (by pomega) (by pomega)]; exact hO₂ s hs
  obtain ⟨c₈, t₈, e₈, ht₈, hO₈, hn₈, hr₈, hreg₈, ho₈⟩ :=
    rdProg_exec' (I := I) hRL hWL c₇ e₇.wb_right hRI
  have hn₈' : ∀ a, (a < Ys + 3 * S ∨ Ys + 3 * S + b * b ≤ a) → c₈.nmem a = c₇.nmem a := hn₈
  have hr₈' : ∀ a, (a < Ys + 3 * S ∨ Ys + 3 * S + b * b ≤ a) → c₈.rmem a = c₇.rmem a := hr₈
  clear hn₈ hr₈
  refine ⟨c₈, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (s₆ + (t₇ + t₈)))))), β',
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ e₈)))))), ?_, hen, fun x hx => ?_, hcr hmssp hnn, fun s hs t ht => ?_,
    fun r hr => ?_, fun a ha ha'' => ?_, fun a ha ha' ha'' => ?_, fun a ha => ?_, ?_⟩
  · -- the cost
    have : t₈ ≤ rdCost b L nD := ht₈
    simp only [List.length_range] at ht₅
    pomega
  · -- the order
    rw [hn₈' _ (Or.inl (by pomega)), hm₇ _ (by pomega) (by pomega)]; exact hO₂ x hx
  · -- the matrices
    have hsB := hen.mem s hs
    have htB := hen.mem t ht
    obtain ⟨i, hi, hib, hK'⟩ := hR₆ (β' s) hsB
    obtain ⟨i', hi', hib', hK''⟩ := hK' (β' t) htB
    have hii : i = R.σ s :=
      fd.inst.cycle.inj i hi (R.σ s) (hS₂ s hs).1 (hib.trans (hS₂ s hs).2)
    have hii' : i' = R.σ t :=
      fd.inst.cycle.inj i' hi' (R.σ t) (hS₂ t ht).1 (hib'.trans (hS₂ t ht).2)
    subst hii hii'
    have hnn' : ∀ a, 0 ≤ (MSSP.pieceGraph N X (redLen N ℓ δ)).len a := fun a => hnn a.1 a.2
    have hms : mssp X (redLen N ℓ δ) (bdry N P₀ P₁) (β' s) (β' t) =
        MSSP.odist (MSSP.pieceGraph N X (redLen N ℓ δ)) (β' s) (β' t) := by
      have := odist_eq_of_isDist hnn' (hmssp X (redLen N ℓ δ) (bdry N P₀ P₁) hnn (β' s) hsB)
      exact congrFun this (β' t)
    have hk7 : Klein.kOut nD n R.k c₇ (R.σ s) (R.σ t) = Klein.kOut nD n fd.k d' (R.σ s) (R.σ t) := by
      unfold Klein.kOut; rw [gnm₇, grm₇]
    have hA : Klein.srcOut Wr R.M (Klein.kOut nD n R.k c₇ (R.σ s) (R.σ t)) =
        MSSP.odist (MSSP.pieceGraph N X (redLen N ℓ δ)) (β' s) (β' t) := by
      rw [hk7]; exact hK''
    have hd : ∀ x < b, c₇.rmem (R.δb + R.ν x) = δ (β' x) := fun x hx => by
      have hv := bdry_sub_verts (hen.mem x hx)
      show c₇.rmem (δb + ν (β' x)) = δ (β' x)
      rw [grm₇, h4₆ _ (by pomega), hrm₅, hr₄ _ (Or.inr (by pomega)), grm₃, hcf₂.rmem, grm₁,
        hδ _ (hN.lt _ hv), hN.inv _ hv]
    refine rdOut_child (R := R) (Wc := Wr) rfl rfl rfl ?_ ?_ (hd s hs) (hd t ht)
      (hO₈ s hs t ht)
    · show (mssp X (redLen N ℓ δ) (bdry N P₀ P₁) (β' s) (β' t)).map
        (· + (δ (β' t) - δ (β' s))) = _
      rw [hms, hA]
    · intro z hz
      rw [hA] at hz
      unfold MSSP.odist at hz
      split_ifs at hz with hr
      · cases hz; exact MSSP.dist_nonneg hnn' hr
  · -- the registers
    rw [hreg₈ r (by pomega)]; exact hR₇ r hr
  · -- the memory
    rw [hn₈' a (by pomega), gnm₇, h3₆ a ha, hm₅ a ha'']
  · rw [hr₈' a (by pomega), grm₇, h4₆ a ha, hrm₅, hr₄ a (Or.inr (by pomega)), grm₃,
      hcf₂.rmem, grm₁]
  · -- the work space
    rw [hn₈' a (Or.inl (by pomega)), gnm₇]; exact h5₆ a ha
  · rw [ho₈, go₇, ho₆, ho₅, ho₄, go₃, hcf₂.out, go₁]

end Part

end NegSSSP

end PlanarFlow
