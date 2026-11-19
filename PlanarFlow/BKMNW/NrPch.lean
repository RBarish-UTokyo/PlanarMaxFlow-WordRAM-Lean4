module

public import PlanarFlow.BKMNW.NrPchE

/-!
# The push-back program `pchP`: the machine's push-back `pchCall` at a call

**`pchP = pchA ; pchB ; pchC ; pchD ; pchE`** (`pchP_natOnly`): from the frame of a call `x` at
`d` (`r3004`), a scratch base `A` (`r9200`), the bounds `β` as words `Kd + β(tail)` at `BT`
(`r9201`, one per dart), the free flags (`0` off `Fr`) at `FR` (`r9202`) and the offset `Kd`
(`r9203`):

1. `pchA`: vertex labels `olab SG`, net outflows `Kd + div g` per label (`dvP`);
2. `pchB`: compact face keys (`olab (SG ∘ RV)`, prefix counts), keys of the reverse darts;
3. `pchC`: out-lists of all darts by vertex label (`osProg`), the number of vertices;
4. `pchD`: the cancellation `cancelR` from the face of the first dart (`nrPass` twice, FR-Dijkstra
   on the dual with the compact keys);
5. `pchE`: Kahn's order of the cancelled flow (`kahnP`) and the visits (`pushP`).

**`pchP_exec`**: on a plane piece map with `m > 0` darts and an antisymmetric flow `g` in the
frame's flow array, within **`pchCost m nf = 2 · nrPassCost m nf + 420 m + 400`** steps
(`nf ≤ #faces`, `Lay.rcnt_le_card`) the flow array holds
**`Z + pchCall gid x h β Fr g`**; memory changed only in `FL` and `[A, A + 30 m + 1)`; registers
outside `pchU` (`3004`, `1500…1520`, `2500…2547`, `6210…6217`, `7350…7405`, `8430…8447`,
`9000…9299`) kept, `r3004` too. Word bounds: `m Z + Z ≤ Kd`, `Kd + 2 m Z + 2 Z + 1 ≤ W`,
`A + d + 30 m + 10 ≤ W`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv NegSSSP Orbit

/-- **The machine's push-back** (see the module docstring). -/
def pchP : Stmt := .seq pchA (.seq pchB (.seq pchC (.seq pchD pchE)))

theorem pchP_natOnly : Klein.natOnly pchP = true := by kernel_rfl

/-- The registers named by `pchP`. -/
def pchU (r : ℕ) : Bool :=
  decide (r = 3004 ∨ (1500 ≤ r ∧ r ≤ 1520) ∨ (2500 ≤ r ∧ r ≤ 2547) ∨ (6210 ≤ r ∧ r ≤ 6217) ∨
    (7350 ≤ r ∧ r ≤ 7405) ∨ (8430 ≤ r ∧ r ≤ 8447) ∨ (9000 ≤ r ∧ r ≤ 9299))

theorem pchP_regsOK : pchP.regsOK pchU = true := by decide +kernel

theorem pchP_noRand : pchP.noRand = true := by decide +kernel

/-- The registers named by phase C. -/
def pchCU (r : ℕ) : Bool :=
  decide ((1500 ≤ r ∧ r ≤ 1520) ∨ (9204 ≤ r ∧ r ≤ 9224) ∨ (9250 ≤ r ∧ r ≤ 9278))

theorem pchC_regsOK : pchC.regsOK pchCU = true := by decide +kernel

theorem pchC_noRand : pchC.noRand = true := by decide +kernel

/-- The registers named by phase E. -/
def pchEU (r : ℕ) : Bool := decide ((1400 ≤ r ∧ r ≤ 1520) ∨ (9000 ≤ r ∧ r ≤ 9299))

theorem pchE_regsOK : pchE.regsOK pchEU = true := by decide +kernel

theorem pchE_noRand : pchE.noRand = true := by decide +kernel

/-- The steps of `pchP`. -/
def pchCost (m n : ℕ) : ℕ := 2 * nrPassCost m n + 420 * m + 400

lemma rkey_congr {f g : ℕ → ℕ} {m : ℕ} (hp : PermOn f m) (h : ∀ x < m, f x = g x) {i : ℕ}
    (hi : i < m) : rkey f i = rkey g i := by
  unfold rkey
  rw [← nr_olab_congr hp h hi]
  exact nr_rcnt_congr fun j hj => nr_olab_congr hp h (by have := olab_lt hp hi; omega)

lemma rcnt_olab_congr {f g : ℕ → ℕ} {m : ℕ} (hp : PermOn f m) (h : ∀ x < m, f x = g x) :
    rcnt (olab f) m = rcnt (olab g) m :=
  nr_rcnt_congr fun j hj => nr_olab_congr hp h hj

namespace MfDrv

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- The flow of the frame is bounded by `Z` (antisymmetric, `Z + g ≥ 0` in the array). -/
lemma flHas_bnd {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    {g : SDart (pdarts M x.1.piece x.2.1) → ℤ} (hg : (pmap h).IsAntisymm g)
    (hfl : FLHas Z m d en mem g) : ∀ e, -(Z : ℤ) ≤ g e ∧ g e ≤ Z := by
  have lo : ∀ e, -(Z : ℤ) ≤ g e := fun e => by
    obtain ⟨i, hi, he⟩ := hL.en_surj e.1 e.2
    have := hfl i hi
    rw [fext_mem g (by rw [he]; exact e.2)] at this
    have e' : (⟨en i, by rw [he]; exact e.2⟩ : SDart (pdarts M x.1.piece x.2.1)) = e :=
      Subtype.ext he
    rw [e'] at this; omega
  intro e
  refine ⟨lo e, ?_⟩
  have := lo ((pmap h).rev e)
  rw [hg e] at this; omega

/-- The flow array as `GRep` along `edF`. -/
lemma flHas_gRep {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem mem' : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (hm : 0 < m)
    {g : SDart (pdarts M x.1.piece x.2.1) → ℤ} :
    FLHas Z m d en mem' g ↔ GRep mem' (d + 4 + 6 * m) Z m (edF hL hm) g := by
  constructor
  · intro hf i hi
    rw [hf i hi, edF_lt hL hm hi, fext_mem g (hL.en_mem i hi)]; rfl
  · intro hf i hi
    rw [hf i hi, edF_lt hL hm hi, fext_mem g (hL.en_mem i hi)]; rfl

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The machine's push-back at a call** (see the module docstring). -/
theorem pchP_exec {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} (c : Config)
    (hc : WordsBounded W c) (hL : Lay M gid u S T Z x m en d c.nmem)
    (h : PieceInv M x.1.piece x.2.1 x.2.2) (hpl : (pmap h).IsPlane) (hm : 0 < m)
    {g : SDart (pdarts M x.1.piece x.2.1) → ℤ} (hg : (pmap h).IsAntisymm g)
    (hfl : FLHas Z m d en c.nmem g)
    {β : SVert x.2.2 (pdarts M x.1.piece x.2.1) → ℤ}
    {Fr : Finset (SVert x.2.2 (pdarts M x.1.piece x.2.1))}
    {A BT FR Kd : ℕ} (r3004 : c.nreg 3004 = d) (r00 : c.nreg 9200 = A) (r01 : c.nreg 9201 = BT)
    (r02 : c.nreg 9202 = FR) (r03 : c.nreg 9203 = Kd)
    (hBT : ∀ i (hi : i < m), (c.nmem (BT + i) : ℤ) = Kd + β ((pmap h).tail (vDart hL hi)))
    (hFR : ∀ i (hi : i < m), c.nmem (FR + i) = 0 ↔ (pmap h).tail (vDart hL hi) ∉ Fr)
    (hA : d + 4 + 7 * m ≤ A)
    (sBT : BT + m ≤ d + 4 + 6 * m ∨ d + 4 + 7 * m ≤ BT) (tBT : BT + m ≤ A ∨ A + 30 * m + 1 ≤ BT)
    (sFR : FR + m ≤ d + 4 + 6 * m ∨ d + 4 + 7 * m ≤ FR) (tFR : FR + m ≤ A ∨ A + 30 * m + 1 ≤ FR)
    (wBT : BT + m ≤ W) (wFR : FR + m ≤ W) (w : A + 30 * m + 10 ≤ W)
    (hKd : m * Z + Z ≤ Kd) (wKd : Kd + 2 * (m * Z) + 2 * Z + 1 ≤ W) :
    ∃ c' t, Exec P W pchP c c' t ∧ t ≤ pchCost m (rcnt (olab (nxFP d m c.nmem)) m) ∧
      FLHas Z m d en c'.nmem (NsStep.pchCall gid x h β Fr g) ∧
      (∀ a, (a < d + 4 + 6 * m ∨ d + 4 + 7 * m ≤ a) → (a < A ∨ A + 30 * m + 1 ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, pchU r = false → c'.nreg r = c.nreg r) ∧ c'.nreg 3004 = d ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  set ed := edF hL hm with hed
  set f := nxFP d m c.nmem with hf
  have hZg := flHas_bnd hL h hg hfl
  have hG0 : GRep c.nmem (d + 4 + 6 * m) Z m ed g := (flHas_gRep hL hm).1 hfl
  have hFLle : ∀ j < m, c.nmem (d + 6 * m + 4 + j) ≤ 2 * Z := fun j hj => by
    have := hG0 j hj; have := hZg (ed j)
    rw [show d + 6 * m + 4 + j = d + 4 + 6 * m + j by omega]; omega
  have hFLs : ∑ j ∈ range m, c.nmem (d + 6 * m + 4 + j) ≤ 2 * m * Z := by
    calc ∑ j ∈ range m, c.nmem (d + 6 * m + 4 + j) ≤ ∑ _j ∈ range m, 2 * Z :=
          sum_le_sum fun j hj => hFLle j (mem_range.1 hj)
      _ = 2 * m * Z := by rw [sum_const, card_range, smul_eq_mul]; ring
  have hmZ : m * Z = Z * m := Nat.mul_comm _ _
  have h2mZ : 2 * m * Z = 2 * (m * Z) := by ring
  -- A
  obtain ⟨c₁, t₁, e₁, ht₁, R₁, vl₁, dv₁, k₁, rr₁, rm₁, o₁⟩ :=
    pchA_exec (P := P) c hc r3004 r00 r03 hL.hm hL.hz hL.permOn_sg hA w hFLs
      (by rw [h2mZ]; clear * - wKd; omega) (by rw [← hmZ]; clear * - wKd; omega)
  rw [r01, r02] at R₁
  -- B
  have fr₁ : ∀ a, a < A → c₁.nmem a = c.nmem a := fun a ha => k₁ a (Or.inl ha)
  have hnx : ∀ i < m, nxFP d m c₁.nmem i = f i := fun i hi => by
    have := (hL.rv i hi).1
    unfold nxFP; rw [fr₁ (d + 4 + m + i) (by clear * - hi hA; omega), fr₁ _ (by clear * - this hA; omega)]
    rw [hf]; rfl
  have hpf : PermOn f m := hL.permOn_face hL.faceArr_nx
  have hp₁ : PermOn (nxFP d m c₁.nmem) m :=
    ⟨fun i hi => by rw [hnx i hi]; exact hpf.lt i hi,
      fun i hi j hj e => hpf.inj i hi j hj (by rw [← hnx i hi, ← hnx j hj]; exact e)⟩
  obtain ⟨c₂, t₂, e₂, ht₂, R₂, nf₂, ky₂, nh₂, k₂, rr₂, rm₂, o₂⟩ :=
    pchB_exec (P := P) c₁ e₁.wb_right R₁
      (fun i hi => by rw [fr₁ _ (by clear * - hi hA; omega)]; exact (hL.rv i hi).1) hp₁ hA w
  rw [rcnt_olab_congr hp₁ hnx] at nf₂
  have ky₂' : ∀ i < m, c₂.nmem (A + 9 * m + i) = rkey f i := fun i hi => by
    rw [ky₂ i hi, rkey_congr hp₁ hnx hi]
  have nh₂' : ∀ i < m, c₂.nmem (A + 10 * m + i) = rkey f (c.nmem (d + 4 + m + i)) := fun i hi => by
    have := (hL.rv i hi).1
    rw [nh₂ i hi, fr₁ _ (by clear * - hi hA; omega), rkey_congr hp₁ hnx this]
  clear ky₂ nh₂
  have mem₂ : ∀ a, (a < A + 5 * m ∨ A + 11 * m ≤ a) → c₂.nmem a = c₁.nmem a := k₂
  -- C
  have vl₂ : ∀ i < m, c₂.nmem (A + 3 * m + i) = olab (sgF d m c.nmem) i := fun i hi => by
    rw [mem₂ _ (by clear * - hi; omega)]; exact vl₁ i hi
  obtain ⟨c₃, t₃, e₃, ht₃, R₃, nv₃, os₃, k₃, rr₃, rm₃, o₃⟩ :=
    pchC_exec (P := P) c₂ e₂.wb_right R₂
      (fun i hi => by rw [vl₂ i hi]; exact olab_lt hL.permOn_sg hi) hm w
  have q₃ : ∀ r, pchCU r = false → c₃.nreg r = c₂.nreg r :=
    NcStep.Exec.nreg_frame e₃ pchC_regsOK pchC_noRand
  have nf₃ : c₃.nreg 9226 = rcnt (olab f) m := by
    rw [q₃ 9226 (by decide)]; exact nf₂
  have nvq : rcnt (fun j => c₂.nmem (A + 3 * m + j)) m = rcnt (olab (sgF d m c.nmem)) m :=
    nr_rcnt_congr fun j hj => vl₂ j hj
  rw [nvq] at nv₃
  have mem₃ : ∀ a, (a < A + 11 * m ∨ A + 19 * m ≤ a) → c₃.nmem a = c₂.nmem a := k₃
  -- D
  have hcard := (hL.ixMap h hm (rv := fun i => c.nmem (d + 4 + m + i))
    (vl := olab (sgF d m c.nmem)) (fun _ _ => rfl) (fun _ _ => rfl)).card_le
  have hK := hL.fKey h hm hL.faceArr_nx (rv := fun i => c.nmem (d + 4 + m + i))
    (key := rkey f) (fun _ _ => rfl) (fun _ _ => rfl)
  have mfr₃ : ∀ a, a < A → c₃.nmem a = c.nmem a := fun a ha => by
    rw [mem₃ a (by clear * - ha; omega), mem₂ a (by clear * - ha; omega), fr₁ a ha]
  obtain ⟨c₄, t₄, e₄, ht₄, R₄, nv₄, FL₄, k₄, rr₄, rm₄, o₄⟩ :=
    pchD_exec (P := P) hpl (frRef_spec _) hK hcard c₃ e₃.wb_right R₃ hm (rcnt_le _ _) nf₃
      (fun i hi => by rw [mem₃ _ (by clear * - hi; omega)]; exact ky₂' i hi)
      (fun i hi => by rw [mem₃ _ (by clear * - hi; omega)]; exact nh₂' i hi)
      hg hZg (fun i hi => by rw [mfr₃ _ (by clear * - hi hA; omega)]; exact hG0 i hi) hA w
      (by clear * - wKd; omega)
  rw [nv₃] at nv₄
  set g₁ := cancelR (pmap h) (frRef _) ((pmap h).face (ed 0)) g with hg₁
  obtain ⟨a₁, cf₁, dv₁', ac₁⟩ := cancelR_spec hpl (frRef_spec _) ((pmap h).face (ed 0)) hg
  have hZ₁ := nr_conf_bnd hg a₁ cf₁ hZg
  -- E
  have mem₄ : ∀ a, (a < d + 4 + 6 * m ∨ d + 4 + 7 * m ≤ a) → (a < A + 19 * m ∨ A + 30 * m + 1 ≤ a) →
      c₄.nmem a = c₃.nmem a := k₄
  have vl₄ : ∀ i < m, c₄.nmem (A + 3 * m + i) = olab (sgF d m c.nmem) i := fun i hi => by
    rw [mem₄ _ (by clear * - hA; omega) (by clear * - hi; omega),
      mem₃ _ (by clear * - hi; omega)]; exact vl₂ i hi
  have rv₄ : ∀ i < m, c₄.nmem (d + 4 + m + i) = c.nmem (d + 4 + m + i) := fun i hi => by
    rw [mem₄ _ (by clear * - hi; omega) (by clear * - hi hA; omega)]
    exact mfr₃ _ (by clear * - hi hA; omega)
  have hI₄ : IxMap (pmap h) m ed (fun i => c₄.nmem (d + 4 + m + i))
      (fun i => c₄.nmem (A + 3 * m + i)) :=
    hL.ixMap h hm (fun i hi => rv₄ i hi) (fun i hi => vl₄ i hi)
  have hDV : DRep (pmap h) c₄.nmem (A + 4 * m) Kd m ed (fun i => c₄.nmem (A + 3 * m + i)) g₁ := by
    intro v hv hvv
    have hvv' : olab (sgF d m c.nmem) v = v := by rw [← vl₄ v hv]; exact hvv
    rw [mem₄ _ (by clear * - hA; omega) (by clear * - hv; omega),
      mem₃ _ (by clear * - hv; omega), mem₂ _ (by clear * - hv; omega), dv₁ v hv,
      dv₁' _, show ed v = vDart hL hv from edF_lt hL hm hv, ← dvP_div hL h hfl hv, hvv']
    have hc := dvC_le (olab (sgF d m c.nmem)) m v
    have hcz : Z * dvC (olab (sgF d m c.nmem)) m v ≤ Z * m := Nat.mul_le_mul_left _ hc
    clear * - hcz hKd hmZ
    push_cast
    omega
  have mfr₄ : ∀ a, (a < d + 4 + 6 * m ∨ d + 4 + 7 * m ≤ a) → (a < A ∨ A + 30 * m + 1 ≤ a) →
      c₄.nmem a = c.nmem a := fun a h1 h2 => by
    rw [mem₄ a h1 (by clear * - h2; omega), mem₃ a (by clear * - h2; omega),
      mem₂ a (by clear * - h2; omega), k₁ a (by clear * - h2; omega)]
  have hO₄ : ∀ y < m, c₄.nmem (A + 13 * m + y) = c₄.nmem (A + 12 * m + y) +
        (nrF (fun i => c₄.nmem (A + 3 * m + i)) (fun _ => 1) m y).length ∧
      c₄.nmem (A + 13 * m + y) ≤ m ∧
      ∀ t (ht : t < (nrF (fun i => c₄.nmem (A + 3 * m + i)) (fun _ => 1) m y).length),
        c₄.nmem (A + 14 * m + (c₄.nmem (A + 12 * m + y) + t)) =
          (nrF (fun i => c₄.nmem (A + 3 * m + i)) (fun _ => 1) m y)[t] := by
    intro y hy
    have e : nrF (fun i => c₄.nmem (A + 3 * m + i)) (fun _ => 1) m y =
        nrF (fun i => c₂.nmem (A + 3 * m + i)) (fun _ => 1) m y :=
      nrF_congr (fun i hi => by rw [vl₄ i hi, vl₂ i hi]) (fun _ _ => rfl) y
    rw [e]
    obtain ⟨u1, u2, u3⟩ := os₃ y hy
    have m4 : ∀ a, A + 12 * m ≤ a → a < A + 15 * m → c₄.nmem a = c₃.nmem a := fun a h1 h2 =>
      mem₄ a (by clear * - h1 hA; omega) (by clear * - h2; omega)
    refine ⟨(by rw [m4 _ (by clear * -; omega) (by clear * - hy; omega),
              m4 _ (by clear * -; omega) (by clear * - hy; omega)]; exact u1),
      (by rw [m4 _ (by clear * -; omega) (by clear * - hy; omega)]; exact u2), fun t ht => ?_⟩
    have hle : c₃.nmem (A + 12 * m + y) + t < m := by
      have := u2; rw [u1] at this; clear * - this ht; omega
    rw [m4 (A + 12 * m + y) (by clear * -; omega) (by clear * - hy; omega),
      m4 _ (by clear * -; omega) (by clear * - hle; omega)]
    exact u3 t ht
  have hmZi : ((m : ℤ) + 1) * (Z : ℤ) = ((m * Z + Z : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨c₅, t₅, e₅, ht₅, ⟨Q, IND, ps, t', hk, hps, GR₅⟩, k₅, rr₅, rm₅, o₅⟩ :=
    pchE_exec (P := P) (Mp := pmap h) (ed := ed) (g := g₁) (β := β) (Fr := Fr) c₄ e₄.wb_right
      R₄ hm hI₄ (by rw [nv₄]; exact (nr_rcnt_congr fun j hj => vl₄ j hj).symm) a₁ ac₁ hZ₁
      (fun i hi => FL₄ i hi) hDV
      (fun v hv hvv => by
        rw [mfr₄ _ (by clear * - sBT hv; omega) (by clear * - tBT hv; omega), hBT v hv,
          show ed v = vDart hL hv from edF_lt hL hm hv])
      (fun v hv hvv => by
        rw [mfr₄ _ (by clear * - sFR hv; omega) (by clear * - tFR hv; omega), hFR v hv,
          show ed v = vDart hL hv from edF_lt hL hm hv])
      hO₄ (by rw [hmZi]; exact_mod_cast hKd) (by rw [hmZi]; clear * - wKd; push_cast; omega)
      (by clear * - wKd; omega) sBT tBT sFR tFR wBT wFR hA w
  have hEU : ∀ r, ¬ (1400 ≤ r ∧ r ≤ 1520) → ¬ (9000 ≤ r ∧ r ≤ 9299) → c₅.nreg r = c₄.nreg r :=
    fun r h1 h2 => NcStep.Exec.nreg_frame e₅ pchE_regsOK pchE_noRand r
      (by unfold pchEU; simp only [decide_eq_false_iff_not]; clear * - h1 h2; omega)
  have ex : Exec P W pchP c c₅ (t₁ + (t₂ + (t₃ + (t₄ + t₅)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  refine ⟨c₅, _, ex, ?_, ?_, fun a h1 h2 => ?_, NcStep.Exec.nreg_frame ex pchP_regsOK pchP_noRand,
    by rw [hEU 3004 (by decide) (by decide)]; exact R₄.r3004,
    by rw [rr₅, rr₄, rr₃, rr₂, rr₁], by rw [rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₅, o₄, o₃, o₂, o₁]⟩
  · unfold pchCost; unfold osCost at ht₃
    generalize nrPassCost m (rcnt (olab f) m) = NP at ht₄ ⊢
    clear * - ht₁ ht₂ ht₃ ht₄ ht₅; omega
  · rw [← nrGt_eq_pchCall hL h hm hpl hI₄ hg hps hk β Fr]
    exact (flHas_gRep hL hm).2 GR₅
  · rw [k₅ a h1 (by clear * - h2; omega) (by clear * - h2; omega), mfr₄ a h1 h2]

end MfDrv

end BKMNW

end PlanarFlow
