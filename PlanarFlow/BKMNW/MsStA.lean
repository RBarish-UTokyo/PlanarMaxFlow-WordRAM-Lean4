module

public import PlanarFlow.BKMNW.MsLay
public import PlanarFlow.BKMNW.MsCutK
public import PlanarFlow.BKMNW.MsKB

/-!
# The MSSP encoder, stage A1: the corners and Klein's encoding of the cut map

**`msA1`** `= msLay ; fcSet ; fcProg ; ckSet ; cutKin`: from the input of an MSSP call (`MsIn`),
the layout registers, the corner order of the path (`fcProg_spec`) in `[p, p + 10m)`, the ranks
`RE`, `RK` of the cut and Klein's encoding of the cut map (`StEnc.KInM`, no piece yet) at
`aIM m p = p + 41 m` (`cutKin_specX`). **`msA1_exec`** (`StA1`).

Notation: `cD0 Pa hk` (the dart of the order of the cut), `cQ`, `cQ'` (its `EnumOK`), the
numbering `σ = StEnc.enEq (cQ …)` of the darts of the cut (`= cutIx`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- The dart of the order of the cut. -/
noncomputable abbrev cD0 (Pa : SPath M) (hk : 0 < Pa.k) : CutD M Pa.darts :=
  cutG Pa.rev_mem_darts' (fixT0 Pa hk) 0

theorem cQ {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) :
    EnumOK (cutMap Pa.rev_mem_darts').dual (cutEn M Pa.darts en m (cD0 Pa hk))
      (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) :=
  enumOK_cut Pa.rev_mem_darts' h (cD0 Pa hk)

theorem cut_faceTrans (hM : M.IsPlane) (hrot : M.RotTrans) (Pa : SPath M) (hk : 0 < Pa.k) :
    (cutMap Pa.rev_mem_darts').FaceTrans := by
  have : Nonempty (CutD M Pa.darts) := ⟨cD0 Pa hk⟩
  exact faceTrans_of_plane (fixCut hM hrot Pa hk 0 fun _ _ => le_rfl).hyp.plane
    (fixCut hM hrot Pa hk 0 fun _ _ => le_rfl).hyp.rot

theorem cQ' (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) :
    EnumOK (cutMap Pa.rev_mem_darts').dual.dual (cutEn M Pa.darts en m (cD0 Pa hk))
      (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) :=
  enumOK_cutDD Pa.rev_mem_darts' h (cD0 Pa hk) (fixT0 Pa hk)
    (fun v => (enumOK_dual_of hM hrot h (Pa.d 0)).fsurj v) (cut_faceTrans hM hrot Pa hk)

/-- The period of the walk around the path is at most the number of darts. -/
lemma fixPer_le {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (Pa : SPath M) : fixPer M Pa ≤ m := by
  rw [← StEnc.card_eq h]
  unfold fixPer
  have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := tour M Pa.darts) (x := Pa.d 0)
  calc minimalPeriod (tour M Pa.darts) (Pa.d 0)
      = (Finset.range (minimalPeriod (tour M Pa.darts) (Pa.d 0))).card := by simp
    _ ≤ (Finset.univ : Finset D).card :=
        Finset.card_le_card_of_injOn (fun n => (tour M Pa.darts)^[n] (Pa.d 0))
          (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
          (fun a ha b hb e => hinj (by simpa using ha) (by simpa using hb) e)
    _ = Fintype.card D := Finset.card_univ

lemma fixCornerL_le {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (Pa : SPath M) :
    (fixCornerL M Pa).length ≤ m := by
  have := fixPer_le h Pa
  have : (fixCornerL M Pa).length ≤ fixPer M Pa := by
    unfold fixCornerL
    exact (List.length_filter_le _ _).trans (by simp)
  omega

variable {P : Input} {W : ℕ}

/-- **Stage A1.** -/
def msA1 : Stmt := .seq msLay (.seq fcSet (.seq fcProg (.seq ckSet cutKin)))

/-- The registers that the stages of the encoder may change. -/
def EScr (r : ℕ) : Prop := r < 8000 ∨ (8010 ≤ r ∧ r < 8300)

/-- **What stage A1 leaves.** -/
structure StA1 (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) (p q : ℕ) (c e : Config) : Prop where
  lay : ∀ j < 17, e.nreg (8280 + j) = (msLayV m p q).getD j 0
  per : e.nreg 8156 = fixPer M Pa
  ncl : e.nreg 8157 = (fixCornerL M Pa).length
  r28 : e.nreg 8228 = nEc Pa.darts en m
  r30 : e.nreg 8230 = nEc Pa.darts en m + nTc M Pa.darts en m
  tr : ∀ s < fixPer M Pa, e.nmem (p + 6 * m + s) = ixOf en m ((tour M Pa.darts)^[s] (Pa.d 0))
  fl : ∀ i < m, e.nmem (p + m + i) = labI M en m i + 1
  lf : ∀ i < m, e.nmem (p + 2 * m + i) = if en i ∈ Pa.darts then 1 else 0
  cs : ∀ r < (fixCornerL M Pa).length,
    e.nmem (p + 8 * m + r) = (fixCornerL M Pa).getD r 0 ∧
      e.nmem (p + 7 * m + r) =
        ixOf en m ((tour M Pa.darts)^[(fixCornerL M Pa).getD r 0] (Pa.d 0))
  cn : ∀ i < m, M.face (en i) ∈ Pa.faces → ∃ r < (fixCornerL M Pa).length,
    e.nmem (p + 9 * m - 1 + (labI M en m i + 1)) = r ∧
      fixCorner M Pa ((fixCornerL M Pa).getD r 0) = M.face (en i)
  rk : ∀ i < m, e.nmem (p + 13 * m + i) = cE Pa.darts en i ∧
    e.nmem (p + 14 * m + i) = cT M Pa.darts en i
  kin : StEnc.KInM (cutMap Pa.rev_mem_darts') (StEnc.enEq (cQ h Pa hk))
    (StEnc.ιF _ (cQ h Pa hk)) (StEnc.ιG _ (cQ h Pa hk)) (StEnc.ιV _ (cQ' hM hrot h Pa hk))
    (StEnc.ιE _ (cQ h Pa hk)) e.nmem (aIM m p)
  mem : ∀ a, (a < p ∨ aIM m p + 12 * (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) + 1 ≤ a) →
    e.nmem a = c.nmem a
  reg : ∀ r, ¬ EScr r → e.nreg r = c.nreg r
  rr : e.rreg = c.rreg
  rm : e.rmem = c.rmem
  out : e.output = c.output

/-- The step bound of stage A1. -/
def costA1 (m k : ℕ) : ℕ :=
  hpCost msLayL + hpCost fcL + fcCost m k + hpCost ckL + (cutCost m + 8 + (140 * (5 * m) + 150))

set_option maxHeartbeats 2000000 in
/-- **Stage A1 on the machine.** -/
theorem msA1_exec (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} {Lmax q : ℕ} {ts : ℕ → D}
    {RVb RTb Pb Lb Qb Ob p : ℕ} (c : Config) (hc : WordsBounded W c)
    (hI : MsCall.MsIn M en m Pa ℓ Lmax q ts RVb RTb Pb Lb Qb Ob p c)
    (hRV : RVb + m ≤ p) (hRT : RTb + m ≤ p) (hPb : Pb + Pa.k ≤ p)
    (hW : p + 860 * m + 100 + 2 * q ≤ W) (h860 : 860 ≤ W) :
    ∃ e t, Exec P W msA1 c e t ∧ t ≤ costA1 m Pa.k ∧ StA1 hM hrot h Pa hk p q c e := by
  have h' := enumOK_dual_of hM hrot h (Pa.d 0)
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  have hpW : p ≤ W := by omega
  -- 1. the layout
  obtain ⟨c₁, e₁, v₁, f₁, m₁, r₁, rm₁, o₁⟩ := msLay_exec (P := P) c hc hI.r00 hI.r06 hI.r09 hW h860
  have k₁ : ∀ r, 8000 ≤ r → r ≤ 8009 → c₁.nreg r = c.nreg r := fun r a b =>
    f₁ r (by omega) (by omega) (by omega)
  -- 2. the registers of `fcProg`
  obtain ⟨c₂, e₂, s50, s51, s52, s53, s54, s55, f₂, m₂, r₂, rm₂, o₂⟩ := fcSet_exec (P := P) c₁
    e₁.wb_right (by rw [k₁ _ (by omega) (by omega), hI.r00])
    (by rw [k₁ _ (by omega) (by omega), hI.r01]) (by rw [k₁ _ (by omega) (by omega), hI.r02])
    (by rw [k₁ _ (by omega) (by omega), hI.r03]) (by rw [k₁ _ (by omega) (by omega), hI.r04])
    (by rw [k₁ _ (by omega) (by omega), hI.r09]) (by omega)
  have mc₂ : c₂.nmem = c.nmem := by rw [m₂, m₁]
  -- 3. the corner order
  obtain ⟨c₃, t₃, e₃, ht₃, per₃, tr₃, fl₃, lf₃, ta₃, ncl₃, cs₃, cn₃, m₃, R₃, r₃, rm₃, o₃⟩ :=
    fcProg_spec (P := P) hrot h Pa hk c₂ e₂.wb_right s50 s51 s52 s53 s54 s55
    (fun i hi => by rw [mc₂]; exact hI.rv i hi) (fun i hi => by rw [mc₂]; exact hI.rt i hi)
    (fun j hj => by rw [mc₂]; exact hI.pd j hj) (Or.inl hRV) (Or.inl hRT) (Or.inl hPb)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have k₃ : ∀ r, 8000 ≤ r → r ≤ 8009 → c₃.nreg r = c.nreg r := fun r a b => by
    rw [R₃ r (by simp only [FcScr]; omega), f₂ r (by omega) (by omega) (by omega), k₁ r a b]
  -- 4. the registers of `cutKin`
  obtain ⟨c₄, e₄, q50, q51, q52, q53, q54, q55, q56, q57, q58, q59, f₄, m₄, r₄, rm₄, o₄⟩ :=
    ckSet_exec (P := P) c₃ e₃.wb_right (by rw [k₃ _ (by omega) (by omega), hI.r00])
    (by rw [k₃ _ (by omega) (by omega), hI.r01]) (by rw [k₃ _ (by omega) (by omega), hI.r02])
    (by rw [k₃ _ (by omega) (by omega), hI.r09]) (by omega)
  have mc₄ : ∀ a, (a < p ∨ p + 10 * m ≤ a) → c₄.nmem a = c.nmem a := fun a ha => by
    rw [m₄, m₃ a ha, mc₂]
  have hCp : CpIn c₄ m RVb RTb (p + 2 * m) (p + 5 * m) (p + 10 * m) (p + 16 * m) (p + 21 * m) :=
    ⟨q50, q51, q52, q53, q54, q55, q56, q57⟩
  -- 5. Klein's encoding of the cut map
  have hrv4 : ∀ i < m, c₄.nmem (RVb + i) < m ∧ en (c₄.nmem (RVb + i)) = M.rev (en i) :=
    fun i hi => by rw [mc₄ _ (Or.inl (by omega))]; exact hI.rv i hi
  have hrt4 : ∀ i < m, c₄.nmem (RTb + i) < m ∧ en (c₄.nmem (RTb + i)) = M.rot (en i) :=
    fun i hi => by rw [mc₄ _ (Or.inl (by omega))]; exact hI.rt i hi
  have hlf4 : ∀ i < m, c₄.nmem (p + 2 * m + i) = if en i ∈ Pa.darts then 1 else 0 :=
    fun i hi => by rw [m₄]; exact lf₃ i hi
  have hta4 : ∀ i < m, c₄.nmem (p + 5 * m + i) = ixOf en m (tour M Pa.darts (en i)) :=
    fun i hi => by rw [m₄]; exact ta₃ i hi
  obtain ⟨c₅, t₅, e₅, ht₅, K₅, r28, r30, rk₅, M₅, R₅, rr₅, rrm₅, o₅⟩ :=
    cutKin_specX (P := P) h h' Pa (cD0 Pa hk) (cQ h Pa hk) (cQ' hM hrot h Pa hk) c₄ e₄.wb_right
    hCp q58 q59 hrv4 hrt4 hlf4 hta4
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  -- the facts
  have hm45 : ∀ a, (a < p + 10 * m) → c₅.nmem a = c₃.nmem a := fun a ha => by
    rw [M₅ a (Or.inl ha), m₄]
  have nS : ∀ r, ¬ EScr r → ¬ CpScr r ∧ ¬ StEnc.SmScr r ∧ (r < 7700 ∨ 7704 < r) ∧ r ≠ 8260 ∧
      r ≠ 8261 := fun r hr => by
    simp only [EScr, CpScr, StEnc.SmScr] at hr ⊢; omega
  have g5 : ∀ r, 8150 ≤ r → r ≤ 8299 → ¬ CpScr r → ¬ StEnc.SmScr r → (r < 7700 ∨ 7704 < r) →
      r ≠ 8260 → r ≠ 8261 → c₅.nreg r = c₄.nreg r := fun r _ _ a b d e f => R₅ r a b d e f
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_, ⟨fun j hj => ?_, ?_, ?_, r28, r30,
    fun s hs => ?_, fun i hi => ?_, fun i hi => ?_, fun r hr => ?_, fun i hi hf => ?_,
    fun i hi => ?_, K₅, fun a ha => ?_, fun r hr => ?_, ?_, ?_, ?_⟩⟩
  · unfold costA1
    omega
  · rw [g5 _ (by omega) (by omega) (by simp only [CpScr]; omega)
      (by simp only [StEnc.SmScr]; omega) (by omega) (by omega) (by omega),
      f₄ _ (by omega) (by omega) (by omega), R₃ _ (by simp only [FcScr]; omega),
      f₂ _ (by omega) (by omega) (by omega)]
    exact v₁ j hj
  · rw [g5 _ (by omega) (by omega) (by simp only [CpScr]; omega)
      (by simp only [StEnc.SmScr]; omega) (by omega) (by omega) (by omega),
      f₄ _ (by omega) (by omega) (by omega), per₃]
  · rw [g5 _ (by omega) (by omega) (by simp only [CpScr]; omega)
      (by simp only [StEnc.SmScr]; omega) (by omega) (by omega) (by omega),
      f₄ _ (by omega) (by omega) (by omega), ncl₃]
  · have := fixPer_le h Pa
    rw [hm45 _ (by omega)]; exact tr₃ s hs
  · rw [hm45 _ (by omega)]; exact fl₃ i hi
  · rw [hm45 _ (by omega)]; exact lf₃ i hi
  · have := fixCornerL_le h Pa
    rw [hm45 _ (by omega), hm45 _ (by omega)]; exact cs₃ r hr
  · obtain ⟨r, hr, e1, e2⟩ := cn₃ i hi hf
    have hl := NsStep.labI_lt (M := M) h hi
    refine ⟨r, hr, ?_, e2⟩
    rw [hm45 _ (by omega)]; exact e1
  · have := rk₅ i hi
    rwa [show p + 10 * m + 3 * m + i = p + 13 * m + i by ring,
      show p + 10 * m + 4 * m + i = p + 14 * m + i by ring] at this
  · rcases ha with ha | ha
    · rw [M₅ a (Or.inl (by omega)), mc₄ _ (Or.inl ha)]
    · rw [M₅ a (Or.inr ha), mc₄ _ (Or.inr (by unfold aIM at ha; omega))]
  · obtain ⟨a1, a2, a3, a4, a5⟩ := nS r hr
    simp only [EScr] at hr
    rw [R₅ r a1 a2 a3 a4 a5, f₄ r (by omega) (by omega) (by omega),
      R₃ r (by simp only [FcScr]; omega), f₂ r (by omega) (by omega) (by omega),
      f₁ r (by omega) (by omega) (by omega)]
  · rw [rr₅, r₄, r₃, r₂, r₁]
  · rw [rrm₅, rm₄, rm₃, rm₂, rm₁]
  · rw [o₅, o₄, o₃, o₂, o₁]

end MsEnc

end BKMNW

end PlanarFlow
