module

public import PlanarFlow.NegSSSP.FaceDist
public import PlanarFlow.NegSSSP.FaceDec
public import PlanarFlow.Klein.SourcesExec

/-!
# Multiple-source shortest paths in the pieces by Klein's algorithm

At every node of the decomposition by simple cycles (`PlanarFlow.NegSSSP.negDecF`) the vertices
shared by the two parts lie on one face of a plane map containing each part (`OneFace`,
`FaceInst`). Klein's algorithm, as verified (`PlanarFlow.MSSP.Hyp`), asks moreover that no dart of
the piece enter a source; the map with the sources copied inside the face
(`PlanarFlow.Klein.srcMap`, `PlanarFlow/Klein/Sources.lean`) meets this, and its answers are the
distances from the vertices of the face (`PlanarFlow.Klein.srcAns_eq`).

* `FaceData N P B`: a one-face instance (`FaceInst`) bundled with its map; `faceLen`: the lengths
  carried to the darts of its map.
* `msspK`: **multiple-source shortest paths in a piece by Klein's trip**: when the piece has a
  one-face instance for its sources, the answers of the trip on the map with the sources copied
  (`PlanarFlow.Klein.srcAns`), read back through the embedding of the instance; otherwise (no call
  of the recursion on `negDecF` is of this kind on the maps it is used on, see below) the
  reference distances `msspRef`.
* `msspK_spec`: **`msspK` meets `PieceMSSPSpec` on every map** (`FaceInst.isDist`,
  `PlanarFlow.Klein.srcAns_isDist`).
* `msspK_eq`: on a piece with a one-face instance, `msspK` is given by Klein's answers;
  `splitF_faceData`: **at every node of a decomposition meeting `SplitF` with shared vertices,
  both parts have a one-face instance**, so on every plane map with transitive rotations and
  faces every call of the recursion `negSSSPDecF` on `negDecF` (`negDecF_fDec`) is answered by
  Klein's trip.
* `faceInst_exec`: **the machine program `kleinProg` on the map with the sources copied of a
  one-face instance runs within `2372500000 (q lg q + k² lg q)` steps** (`q` the bound on the
  size of the instance, `k` the length of its face), with the copies of the vertices of the face
  as targets (`k²` path-sum queries), **and ends with the distances in the piece between the
  sources in its output** (`PlanarFlow.Klein.kOut`, read back by `PlanarFlow.Klein.srcOut`;
  `FaceInst.isDist`); `splitF_exec`: at a node of `m` darts (`SplitF`: `q ≤ 18 m`,
  `k² ≤ 1200 m`), within `32886 · 2372500000 · m lg m` steps, for both parts.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset BKMNW CombMap

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-! ### The lengths on the map of an instance -/

section Len

variable {DQ : Type u} [DecidableEq DQ]

open Classical in
/-- **The lengths carried to the darts of the map of an instance**: the length of the dart of `P'`
mapped to it (raised to `0` if negative), `0` off the image of `P'`. -/
noncomputable def faceLen (P' : Finset D) (e : D → DQ) (ℓ : D → ℤ) (x : DQ) : ℤ :=
  if h : ∃ d ∈ P', e d = x then max 0 (ℓ h.choose) else 0

lemma faceLen_nonneg (P' : Finset D) (e : D → DQ) (ℓ : D → ℤ) (x : DQ) :
    0 ≤ faceLen P' e ℓ x := by
  unfold faceLen; split_ifs <;> simp

lemma faceLen_e {P' : Finset D} {e : D → DQ} {ℓ : D → ℤ} (hinj : Set.InjOn e P')
    (hnn : ∀ d ∈ P', 0 ≤ ℓ d) {d : D} (hd : d ∈ P') : faceLen P' e ℓ (e d) = ℓ d := by
  have h : ∃ d' ∈ P', e d' = e d := ⟨d, hd, rfl⟩
  unfold faceLen
  simp only [h, ↓reduceDIte]
  have e1 : h.choose = d := hinj h.choose_spec.1 hd h.choose_spec.2
  rw [e1, max_eq_right (hnn d hd)]

end Len

/-! ### The instances, bundled -/

section Data

variable (N) in
/-- **A one-face instance, bundled**: the plane map `Q` (types, instances), its face `g` of `k`
darts, the embedding `e`, `j` of the reached darts `P'`, with `FaceInst N P B q k Q g P' e j`. -/
structure FaceData (P : Finset D) (B : Finset V) : Type (max u v + 1) where
  /-- The bound on the size of the map. -/
  q : ℕ
  /-- The number of darts of the face. -/
  k : ℕ
  /-- The darts of the map. -/
  DQ : Type u
  /-- The vertices of the map. -/
  VQ : Type u
  /-- The faces of the map. -/
  FQ : Type u
  [fD : Fintype DQ]
  [dD : DecidableEq DQ]
  [fV : Fintype VQ]
  [dV : DecidableEq VQ]
  [fF : Fintype FQ]
  [dF : DecidableEq FQ]
  /-- The map. -/
  Q : CombMap DQ VQ FQ
  /-- The face. -/
  g : ℕ → DQ
  /-- The darts of the piece reached from the sources. -/
  P' : Finset D
  /-- The embedding of the darts. -/
  e : D → DQ
  /-- The embedding of the vertices. -/
  j : V → VQ
  /-- The instance. -/
  inst : FaceInst N P B q k Q g P' e j

attribute [instance] FaceData.fD FaceData.dD FaceData.fV FaceData.dV FaceData.fF FaceData.dF

lemma OneFace.faceData {P : Finset D} {B : Finset V} {q k : ℕ} (h : OneFace N P B q k) :
    Nonempty (FaceData N P B) := by
  obtain ⟨DQ, VQ, FQ, i1, i2, i3, i4, i5, i6, Q, g, P', e, j, h⟩ := h
  exact ⟨⟨q, k, DQ, VQ, FQ, Q, g, P', e, j, h⟩⟩

end Data

/-! ### Multiple-source shortest paths by Klein's trip -/

section MSSP

variable (N) in
open Classical in
/-- **Multiple-source shortest paths in the piece `P` from the source `b` by Klein's trip**: for
a one-face instance of the piece (chosen when there is one) in which `b` is the vertex `j b` of
the face `g` of its map `Q`, the answers of the trip on `Q` with the sources copied
(`PlanarFlow.Klein.srcAns`, with the lengths `faceLen`) from the first index `i` with
`tail (g i) = j b`, at the images of the vertices of `P'` and of `B` (`none` elsewhere);
otherwise the reference distances `msspRef`. -/
noncomputable def msspK (P : Finset D) (ℓ : D → ℤ) (B : Finset V) (b : V) : V → Option ℤ :=
  if h : Nonempty (FaceData N P B) then
    if hb : ∃ i < (Classical.choice h).k,
        (Classical.choice h).Q.tail ((Classical.choice h).g i) = (Classical.choice h).j b then
      fun x => if x ∈ verts N (Classical.choice h).P' ∪ B then
        Klein.srcAns (Classical.choice h).inst.cycle (Classical.choice h).inst.plane
          (Classical.choice h).inst.rot
          (S := (Classical.choice h).P'.image (Classical.choice h).e)
          (ℓ := faceLen (Classical.choice h).P' (Classical.choice h).e ℓ)
          (fun y _ => faceLen_nonneg _ _ _ y) (Nat.find hb) ((Classical.choice h).j x)
      else none
    else msspRef N P ℓ B b
  else msspRef N P ℓ B b

/-- **For a one-face instance, Klein's answers give the distances in the piece**: from a source
`b` with `tail (g i) = j b`, the answers of the trip from `i` at the images of the vertices of
`P'` and of `B`. -/
theorem FaceData.isDist {P : Finset D} {B : Finset V} (fd : FaceData N P B) {ℓ : D → ℤ}
    (hnn : ∀ d ∈ P, 0 ≤ ℓ d) {b : V} (hb : b ∈ B) {i : ℕ} (hi : i < fd.k)
    (hib : fd.Q.tail (fd.g i) = fd.j b) :
    IsDist (MSSP.pieceGraph N P ℓ) b (fun x => if x ∈ verts N fd.P' ∪ B then
      Klein.srcAns fd.inst.cycle fd.inst.plane fd.inst.rot (S := fd.P'.image fd.e)
        (ℓ := faceLen fd.P' fd.e ℓ) (fun y _ => faceLen_nonneg _ _ _ y) i (fd.j x)
      else none) := by
  have hℓ : ∀ d ∈ fd.P', faceLen fd.P' fd.e ℓ (fd.e d) = ℓ d := fun d hd =>
    faceLen_e fd.inst.injE (fun d' hd' => hnn d' (fd.inst.sub hd')) hd
  refine fd.inst.isDist hℓ hb ?_
  rw [← hib]
  exact Klein.srcAns_isDist _ _ _ _ hi

/-- **Multiple-source shortest paths by Klein's trip meet `PieceMSSPSpec`**, on every map. -/
theorem msspK_spec : PieceMSSPSpec N (msspK N) := by
  intro P ℓ B hnn b hb
  unfold msspK
  split_ifs with h hb'
  · exact (Classical.choice h).isDist hnn hb (Nat.find_spec hb').1 (Nat.find_spec hb').2
  · exact absurd ((Classical.choice h).inst.src b hb) hb'
  · exact msspRef_spec N P ℓ B hnn b hb

/-- **On a piece with a one-face instance, `msspK` is given by Klein's answers** (on the chosen
instance), from every source. -/
theorem msspK_eq {P : Finset D} {B : Finset V} (h : Nonempty (FaceData N P B)) (ℓ : D → ℤ)
    {b : V} (hb : b ∈ B) :
    ∃ i < (Classical.choice h).k, (Classical.choice h).Q.tail ((Classical.choice h).g i) =
      (Classical.choice h).j b ∧ msspK N P ℓ B b = fun x =>
        if x ∈ verts N (Classical.choice h).P' ∪ B then
          Klein.srcAns (Classical.choice h).inst.cycle (Classical.choice h).inst.plane
            (Classical.choice h).inst.rot
            (S := (Classical.choice h).P'.image (Classical.choice h).e)
            (ℓ := faceLen (Classical.choice h).P' (Classical.choice h).e ℓ)
            (fun y _ => faceLen_nonneg _ _ _ y) i ((Classical.choice h).j x)
        else none := by
  have hb' := (Classical.choice h).inst.src b hb
  refine ⟨Nat.find hb', (Nat.find_spec hb').1, (Nat.find_spec hb').2, ?_⟩
  unfold msspK
  simp only [h, hb', ↓reduceDIte]

/-- **At a node of a decomposition meeting `SplitF` with shared vertices, both parts have a
one-face instance** for the shared vertices: the calls of multiple-source shortest paths of the
recursion at that node are answered by Klein's trip (`msspK_eq`). -/
theorem splitF_faceData {P P₀ P₁ : Finset D} (h : SplitF N P P₀ P₁)
    (hB : (bdry N P₀ P₁).Nonempty) :
    Nonempty (FaceData N P₀ (bdry N P₀ P₁)) ∧ Nonempty (FaceData N P₁ (bdry N P₀ P₁)) := by
  obtain ⟨-, -, -, -, -, -, -, -, hw⟩ := h
  obtain ⟨k, -, h₀, h₁⟩ := hw hB
  exact ⟨h₀.faceData, h₁.faceData⟩

end MSSP

/-! ### The machine program on an instance -/

section Exec

open WordRAM WordRAM.Machine

variable {P : Finset D} {B : Finset V} {q k : ℕ} {DQ VQ FQ : Type u} [Fintype DQ]
  [DecidableEq DQ] [Fintype VQ] [DecidableEq VQ] [Fintype FQ] [DecidableEq FQ]
  {Q : CombMap DQ VQ FQ} {g : ℕ → DQ} {P' : Finset D} {e : D → DQ} {j : V → VQ}

/-- **Klein's program on a one-face instance**: on the map of the instance with the sources
copied (`PlanarFlow.Klein.srcMap`, the lengths `faceLen` perturbed), with the copies of the `k`
vertices of the face as targets, `kleinProg` runs from an input and a starting configuration (as
in `PlanarFlow.Klein.klein_exec_exists`) within `2372500000 (q lg q + k² lg q)` steps, prints
nothing, and ends with the answers in its output: for all sources `b`, `b'` (with
`tail (g i) = j b`, `tail (g i') = j b'`), the answer `kOut i i'` of the program read back
(`PlanarFlow.Klein.srcOut`) is the distance in the piece `P` from `b` to `b'`, none when `b'` is
not reached. -/
theorem faceInst_exec (h : FaceInst N P B q k Q g P' e j) {ℓ : D → ℤ}
    (hnn : ∀ d ∈ P, 0 ≤ ℓ d) :
    ∃ (n Bw : ℕ) (I : Input) (c₀ c' : Config) (steps : ℕ),
      Exec I (Bw + 16 * (n + 1)) (Klein.kleinProg Bw (Fintype.card (Klein.SrcD DQ k)) n k k) c₀ c'
        steps ∧
      steps ≤ 2372500000 * (q * lg q + k ^ 2 * lg q) ∧
      (∀ b ∈ B, ∃ i < k, Q.tail (g i) = j b ∧ ∀ b' ∈ B, ∃ i' < k, Q.tail (g i') = j b' ∧
        Klein.srcOut (Klein.srcW (P'.image e) (faceLen P' e ℓ)) (Fintype.card (Klein.SrcD DQ k))
          (Klein.kOut (Fintype.card (Klein.SrcD DQ k)) n k c' i i') =
          MSSP.odist (MSSP.pieceGraph N P ℓ) b b') ∧
      c'.output = c₀.output := by
  have hnnQ : ∀ y ∈ P'.image e, 0 ≤ faceLen P' e ℓ y := fun y _ => faceLen_nonneg _ _ _ y
  obtain ⟨n, Bw, I, c₀, c', steps, -, hE, hs, hd, hout⟩ :=
    Klein.src_exec h.cycle h.plane h.rot hnnQ k fun i => Q.tail (g i)
  have hℓ : ∀ d ∈ P', faceLen P' e ℓ (e d) = ℓ d := fun d hd =>
    faceLen_e h.injE (fun d' hd' => hnn d' (h.sub hd')) hd
  refine ⟨n, Bw, I, c₀, c', steps, hE, hs.trans ?_, fun b hb => ?_, hout⟩
  · have hN := h.card
    have hl := lg_mono hN
    have h1 : (Fintype.card VQ + Fintype.card FQ + Fintype.card DQ) *
        lg (Fintype.card VQ + Fintype.card FQ + Fintype.card DQ) ≤ q * lg q :=
      Nat.mul_le_mul hN hl
    have h2 : k * k * lg (Fintype.card VQ + Fintype.card FQ + Fintype.card DQ) ≤ k ^ 2 * lg q := by
      rw [← sq]; exact Nat.mul_le_mul_left _ hl
    exact Nat.mul_le_mul_left _ (Nat.add_le_add h1 h2)
  · obtain ⟨i, hi, hib⟩ := h.src b hb
    have hD := h.isDist hℓ hb (isDist_odist (fun a => faceLen_nonneg _ _ _ a.1) _)
    have hE' := odist_eq_of_isDist (fun a => hnn a.1 a.2) hD
    refine ⟨i, hi, hib, fun b' hb' => ?_⟩
    obtain ⟨i', hi', hib'⟩ := h.src b' hb'
    refine ⟨i', hi', hib', ?_⟩
    rw [hd i hi i' hi', hib, hib', ← hE']
    simp [hb']

/-- **Klein's program at a node of the decomposition by simple cycles**: at a node of `m` darts
meeting `SplitF` with shared vertices, for each part there is a one-face instance on which
`kleinProg` runs within `32886 · 2372500000 · m lg m` steps and ends with the distances in the
part between the shared vertices in its output (`faceInst_exec`, `oneFace_cost_le`). -/
theorem splitF_exec {P P₀ P₁ : Finset D} (h : SplitF N P P₀ P₁) (hB : (bdry N P₀ P₁).Nonempty)
    {ℓ : D → ℤ} {X : Finset D} (hX : X = P₀ ∨ X = P₁) (hnn : ∀ d ∈ X, 0 ≤ ℓ d) :
    ∃ fd : FaceData N X (bdry N P₀ P₁), ∃ (n Bw : ℕ) (I : Input) (c₀ c' : Config) (steps : ℕ),
      Exec I (Bw + 16 * (n + 1))
        (Klein.kleinProg Bw (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k fd.k) c₀ c' steps ∧
      steps ≤ 32886 * 2372500000 * P.card * lg P.card ∧
      (∀ b ∈ bdry N P₀ P₁, ∃ i < fd.k, fd.Q.tail (fd.g i) = fd.j b ∧
        ∀ b' ∈ bdry N P₀ P₁, ∃ i' < fd.k, fd.Q.tail (fd.g i') = fd.j b' ∧
          Klein.srcOut (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ))
            (Fintype.card (Klein.SrcD fd.DQ fd.k))
            (Klein.kOut (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k c' i i') =
          MSSP.odist (MSSP.pieceGraph N X ℓ) b b') ∧
      c'.output = c₀.output := by
  have h' := h
  obtain ⟨-, -, -, -, -, -, -, -, hw⟩ := h'
  obtain ⟨k, hk, h₀, h₁⟩ := hw hB
  have hX' : OneFace N X (bdry N P₀ P₁) (18 * P.card) k := by
    rcases hX with rfl | rfl
    · exact h₀
    · exact h₁
  obtain ⟨DQ, VQ, FQ, i1, i2, i3, i4, i5, i6, Q, g, P', e, j, hI⟩ := hX'
  obtain ⟨n, Bw, I, c₀, c', steps, hE, hs, hR, hout⟩ := faceInst_exec hI hnn
  refine ⟨⟨18 * P.card, k, DQ, VQ, FQ, Q, g, P', e, j, hI⟩, n, Bw, I, c₀, c', steps, hE,
    hs.trans ?_, hR, hout⟩
  exact oneFace_cost_le (f := fun q k => 2372500000 * (q * lg q + k ^ 2 * lg q))
    (fun _ _ => le_rfl) le_rfl hk

end Exec

end NegSSSP

end PlanarFlow
