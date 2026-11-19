module

public import PlanarFlow.BKMNW.NcPbR
public import PlanarFlow.BKMNW.NrCost
public import PlanarFlow.BKMNW.NcChs

/-!
# `pbP` meets `PbPSpec'`

* `lay_reZ` (a frame is a frame at a larger offset `Z'` once its header cell `d + 3` holds `Z'`),
  `layEn_of_lt`;
* **`pbRZ Z m = 33 m + 20 + 6 (m Z) + 6 Z`** (the room: the scratch of `pchP`, `BT'`, `FR`, `SV`,
  and the words of `pchP` at offset `2Z`: `Kd + 2 m (2Z) + 2 (2Z) + 1 ≤ W`, `Kd = 2 m Z + 2 Z`);
* **`pbTN x j = pchCost m (nfOf x) + 65 m + 87`** (`m` the darts of the piece, `nfOf x` its faces);
* **`pbP_spec'`**: `PbPSpec' M gid u S T Z I W pbP pbTN (pbRZ Z)` for every `gid u S T Z I W`;
* **`pbTN_le_pushRun`**: `1 ≤ C`, `1 ≤ m`, `nf ≤ m ≤ N` ⇒ `pchCost m nf + 65 m + 87 ≤
  (cMachS C C₀).pushRun m nf N`; **`pbTN_le`** (at a call, `m ≤ N`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap MfDrv NsStep StCall WordRAM WordRAM.Machine
  WordRAM.Machine.Stmt WordRAM.Programs NegSSSP OrbLab

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- **A frame at a larger offset**: the frame with its header cell `d + 3` set to `Z' ≥ Z`. -/
lemma lay_reZ {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem mem' : ℕ → ℕ}
    (h : Lay M gid u S T Z x m en d mem) {Z' : ℕ} (hZ : Z ≤ Z')
    (he : ∀ a, d ≤ a → a < d + 4 + 6 * m → a ≠ d + 3 → mem' a = mem a)
    (h3 : mem' (d + 3) = Z') : Lay M gid u S T Z' x m en d mem' where
  hm := by rw [he _ le_rfl (by omega) (by omega)]; exact h.hm
  hk := by rw [he _ (by omega) (by omega) (by omega)]; exact h.hk
  tag := by rw [he _ (by omega) (by omega) (by omega)]; exact h.tag
  hz := h3
  en_mem := h.en_mem
  en_surj := h.en_surj
  en_mono := h.en_mono
  gd i hi := by rw [he _ (by omega) (by omega) (by omega)]; exact h.gd i hi
  rv i hi := by rw [he _ (by omega) (by omega) (by omega)]; exact h.rv i hi
  sg i hi := by rw [he _ (by omega) (by omega) (by omega)]; exact h.sg i hi
  cp i hi := by
    rw [he _ (by omega) (by omega) (by omega)]
    exact ⟨(h.cp i hi).1, (h.cp i hi).2.trans hZ⟩
  kr i hi := by rw [he _ (by omega) (by omega) (by omega)]; exact h.kr i hi
  hl i hi := by rw [he _ (by omega) (by omega) (by omega)]; exact h.hl i hi

lemma layEn_of_lt {B : Finset D} {en : ℕ → D} {m : ℕ} {hen : ∀ i < m, en i ∈ B} {hm : 0 < m}
    {i : ℕ} (hi : i < m) : layEn B en m hen hm i = ⟨en i, hen i hi⟩ :=
  Subtype.ext (layEn_val hi)

/-- **The room of `pbP`** at the offset `Z`. -/
def pbRZ (Z m : ℕ) : ℕ := 33 * m + 20 + 6 * (m * Z) + 6 * Z

/-- **The steps of `pbP`** at a call. -/
noncomputable def pbTN (x : MCall M) (j : ℕ) : ℕ :=
  pchCost (pdarts M x.1.piece x.2.1).card (nfOf x) + 65 * (pdarts M x.1.piece x.2.1).card + 87

lemma pchCost_mono' {m n n' : ℕ} (h : n ≤ n') : pchCost m n ≤ pchCost m n' := by
  have := nrPassCost_mono (m := m) h
  unfold pchCost; omega

set_option maxHeartbeats 4000000 in
/-- **`pbP` meets `PbPSpec'`** (with the room `pbRZ Z` and the steps `pbTN`). -/
theorem pbP_spec' (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) :
    PbPSpec' M gid u S T Z I W pbP pbTN (pbRZ Z) := by
  intro l r π Hs σ h d e b m en hm j β g' BTb Gb PBb Sb Wz c hL hok hSeg hde heb l1 l2 l3 s1 s2
    s3 d1 d2 wS oD hz hc r04 r05 r06 r6800 r05' r06' r07 r08 hβ hanti hg' hres hBT hG
  unfold fsz at hde
  unfold pbRZ at wS
  have hpl := (lay_plane h.1 hok hL hm).1
  have eK : (Z + Z) * m = 2 * (m * Z) := by ring
  have hBTle : ∀ i < m, c.nmem (BTb + i) ≤ m * Z := fun i hi => by
    have h1 := hBT i hi
    have h2 := (hβ ((pmap h.1).tail (layEn _ en m hL.en_mem hm i))).2
    rw [← h1] at h2
    exact_mod_cast h2
  obtain ⟨c₁, k₁, e₁, hk₁, p00, p01, p02, p03, q01, q02, q06, q08, q12, q14, sv₁, fl₁, bt₁, fr₁,
    z₁, o₁, rr₁, rm₁, oo₁⟩ :=
    pbS1_exec (P := I) c hc r04 hL.hm hL.hz r05' r06' r07 r08 (by omega) (by omega) s2 s1
      (by omega) (by rw [eK]; omega) (by omega)
      (fun i hi => by rw [eK]; have := hBTle i hi; omega)
  have r3004₁ : c₁.nreg 3004 = d := by
    rw [keepW_of_all e₁ pbS1_dests 3004 (by decide)]; exact r04
  -- the frame at offset `2Z`
  have hL₂ : Lay M gid u S T (2 * Z) (.node l r π, Hs, σ) m en d c₁.nmem :=
    lay_reZ hL (by omega) (fun a h1 h2 h3 => o₁ a h3 (Or.inl (by omega)) (Or.inl (by omega)))
      (by rw [z₁]; omega)
  have hfl : FLHas (2 * Z) m d en c₁.nmem g' := fun i hi => by
    rw [show d + 4 + 6 * m + i = 6 * m + d + 4 + i by omega, fl₁ i hi, hG i hi,
      fext_mem g' (hL.en_mem i hi)]
    push_cast; congr 1; exact congrArg g' (Subtype.ext (layEn_val hi))
  obtain ⟨c₂, t₂, e₂, ht₂, FL₂, k₂, kr₂, r3004₂, rr₂, rm₂, oo₂⟩ :=
    pchP_exec (P := I) c₁ e₁.wb_right hL₂ h.1 hpl hm hanti hfl (β := β) (Fr := ∅) (A := Sb)
      (BT := 30 * m + Sb + 1) (FR := 30 * m + Sb + 1 + m) (Kd := (Z + Z) * m + (Z + Z))
      r3004₁ p00 p01 p02 p03
      (fun i hi => by
        rw [bt₁ i hi]; push_cast; rw [hBT i hi]; congr 1
        exact congrArg (fun y => β ((pmap h.1).tail y)) (Subtype.ext (layEn_val hi)))
      (fun i hi => by simp [fr₁ i hi])
      (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
      (by omega) (by omega) (by omega)
      (by rw [eK]; clear * -; ring_nf; omega)
      (by rw [eK]; clear * - wS; ring_nf; ring_nf at wS; omega)
  have kq : ∀ r, 9900 ≤ r → r ≤ 9915 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    kr₂ r (by unfold pchU; simp only [decide_eq_false_iff_not]; omega)
  obtain ⟨c₃, k₃, e₃, hk₃, pb₃, fl₃, z₃, o₃, rr₃, rm₃, oo₃⟩ :=
    pbS3_exec (P := I) (m := m) (Z := Z) (a := d + 3) (FL := 6 * m + d + 4) (PBb := PBb)
      (SV := 30 * m + Sb + 1 + m + m) c₂ e₂.wb_right
      (by rw [kq _ (by omega) (by omega)]; exact q01) (by rw [kq _ (by omega) (by omega)]; exact q02)
      (by rw [kq _ (by omega) (by omega)]; exact q06) (by rw [kq _ (by omega) (by omega)]; exact q08)
      (by rw [kq _ (by omega) (by omega)]; exact q12) (by rw [kq _ (by omega) (by omega)]; exact q14)
      (by omega) (by omega) (by omega) (by omega)
  have ex : Exec I W pbP c c₃ (k₁ + (t₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  have hcard := hL.card_eq
  refine ⟨c₃, _, ex, ?_, fun i hi => ?_, fun a ha hpb => ?_, fun r hr => ?_,
    by rw [oo₃, oo₂, oo₁]⟩
  · -- the steps
    have hnf : rcnt (olab (nxFP d m c₁.nmem)) m ≤ nfOf (.node l r π, Hs, σ) := by
      unfold nfOf; rw [← card_sFace]; exact hL₂.rcnt_le_card h.1 hm hL₂.faceArr_nx
    have := pchCost_mono' (m := m) hnf
    unfold pbTN; rw [hcard]; omega
  · -- the output
    rw [pb₃ i hi, show 6 * m + d + 4 + i = d + 4 + 6 * m + i by omega, FL₂ i hi,
      fext_mem _ (hL.en_mem i hi)]
    push_cast; congr 1; exact congrArg _ (Subtype.ext (layEn_val hi)).symm
  · -- the memory below `Sb` off `PB`
    refine ⟨?_, by rw [rm₃, rm₂, rm₁]⟩
    by_cases h3 : a = d + 3
    · rw [h3, z₃, hL.hz]
    by_cases hF : 6 * m + d + 4 ≤ a ∧ a < 6 * m + d + 4 + m
    · obtain ⟨i, rfl⟩ : ∃ i, a = 6 * m + d + 4 + i := ⟨a - (6 * m + d + 4), by omega⟩
      have hi : i < m := by omega
      rw [fl₃ i hi, k₂ _ (Or.inr (by omega)) (Or.inr (by omega)), sv₁ i hi]
    · have hF' : a < 6 * m + d + 4 ∨ 6 * m + d + 4 + m ≤ a := by
        by_contra hc'; push_neg at hc'; exact hF hc'
      rw [o₃ a h3 hpb hF', k₂ a (by omega) (Or.inl (by omega)),
        o₁ a h3 hF' (Or.inl (by omega))]
  · -- the registers
    by_cases h4 : r = 3004
    · subst h4
      rw [keepW_of_all e₃ pbS3_dests 3004 (by decide), r3004₂, r04]
    · exact keepW_of_all ex pbP_dests r (by unfold PKeep at hr; omega)

/-- **The steps of `pbP` within the push-back budget of `cMachS`.** -/
theorem pbTN_le_pushRun {C C₀ m nf N : ℕ} (hC : 1 ≤ C) (hm : 1 ≤ m) (hnf : nf ≤ m)
    (hN : m ≤ N) :
    pchCost m nf + 65 * m + 87 ≤ (cMachS C C₀).pushRun m nf N := by
  unfold pchCost
  rw [nrPassCost_eq]
  unfold SubCosts.pushRun
  simp only [cMachS]
  obtain ⟨H, hH⟩ : ∃ H, Heap.lg (2 * nf) = H := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, lg nf = g := ⟨_, rfl⟩
  rw [hH, hg]
  have hHg : H ≤ 2 * g := by rw [← hH, ← hg]; exact heapLg2_le nf
  have hg1 : 1 ≤ g := by rw [← hg]; exact one_le_lg nf
  have e1 : nf * H ≤ 2 * (nf * g) := by
    calc nf * H ≤ nf * (2 * g) := Nat.mul_le_mul_left _ hHg
      _ = 2 * (nf * g) := by ring
  have e2 : H * m ≤ 2 * (m * g) := by
    calc H * m ≤ (2 * g) * m := Nat.mul_le_mul_right _ hHg
      _ = 2 * (m * g) := by ring
  have e3 : m ≤ m * g := Nat.le_mul_of_pos_right _ hg1
  have e4 : nf * g ≤ nf * g ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
  have e5 : g ≤ m * g := Nat.le_mul_of_pos_left _ hm
  have e6 : N ≤ C * N := Nat.le_mul_of_pos_left _ hC
  have hK : 1 ≤ csK := by unfold csK; norm_num
  have f1 : 6300 * (nf * g ^ 2 + m * g) ≤ csK * (6300 * (nf * g ^ 2 + m * g)) :=
    Nat.le_mul_of_pos_left _ hK
  have f2 : 1000 * (C * N) ≤ csK * (C * N) := by
    have : 1000 ≤ csK := by unfold csK; norm_num
    exact Nat.mul_le_mul_right _ this
  omega

/-- **The steps of `pbP` at a call** with at least one dart and at most `N` darts. -/
theorem pbTN_le (C C₀ : ℕ) (x : MCall M) (j : ℕ) {N : ℕ} (hC : 1 ≤ C)
    (hm : 1 ≤ (pdarts M x.1.piece x.2.1).card) (hN : (pdarts M x.1.piece x.2.1).card ≤ N) :
    pbTN x j ≤ (cMachS C C₀).pushRun (pdarts M x.1.piece x.2.1).card (nfOf x) N := by
  unfold pbTN
  refine pbTN_le_pushRun hC hm ?_ hN
  unfold nfOf
  exact nOrb_le_card _ _

end NcStep

end BKMNW

end PlanarFlow
