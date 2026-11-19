module

public import PlanarFlow.BKMNW.MsEncG

/-!
# The composed MSSP encoder, part H: stages C3, D, E from the state after stage C

**`msR_run`** (`msC3 ; msD ; msE2` from `StC`): the words the final state holds (Klein's image
clipped at `β'`, the flags, the real words at `β`, the slots), on the words of the state after
stage C, the frames of the low and the high memory, the registers of the call.
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

variable {P : Input} {W : ℕ}

/-- The rest of the encoder. -/
def msR : Stmt := .seq msC3 (.seq msD msE2)

/-- The step bound of stage D at the maxima. -/
def costD (m : ℕ) : ℕ :=
  (13 + 4 + hpCost dh1L + hpCost dh2L + hpCost dh3L + (3 + hpCost dh4L + hpCost dh5L)) +
    (hpCost twSL + hpCost twWL + (19 + 8) * (5 * m) + 5 + 6)

set_option maxHeartbeats 16000000 in
/-- **Stages C3, D, E on the machine** (see the module docstring). -/
theorem msR_run (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e)
    {p q Qb Wz nF nV : ℕ} (τv : CutV M Pa.darts ≃ Fin nF) (τf : CutF M Pa.darts ≃ Fin nV)
    {Ct : STFlow.DTree (mN Pa)} {T₀ : STFlow.DTree (cutMap Pa.rev_mem_darts').dual}
    {C₀ : STFlow.DTree (mN Pa)} {ts : List (CutV M Pa.darts)} {cs : List (CutF M Pa.darts)}
    (c₀ c : Config) (hc : WordsBounded W c)
    (hC : StC hM hrot h Pa hk ℓ hnn p q c₀ c τv τf Ct T₀ C₀ ts cs)
    (r00 : c₀.nreg 8000 = m) (r06 : c₀.nreg 8006 = q) (r07 : c₀.nreg 8007 = Qb)
    (hqd : ∀ i < q, c₀.nmem (Qb + i) < m) (lQ : Qb + q ≤ p) (hWzQ : Wz < Qb)
    (hKW : 10 * Klein.kleinWN (dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
      (fixCornerL M Pa).length) (4 * mnD Pa en m + 1)
        (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa)) + 1000 ≤ Wz)
    (hN1 : MSSP.isoN1 nF (mnD Pa en m) nV ≤ Wz)
    (hWW : p + 860 * m + 1000 + 2 * q ≤ W) :
    ∃ (e : Config) (tt : ℕ) (c₅ : Config), Exec P W msR c e tt ∧ tt ≤ costC3 m q + costD m + costE2 (dLen (5 * m) m m) ∧
      (∀ a, aIM m p ≤ a → a < aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 →
        c₅.nmem a = c.nmem a) ∧
      (∀ r < (fixCornerL M Pa).length,
        c₅.nmem (aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 + r) =
          xtN c.nmem (p + 8 * m) (p + 6 * m) (p + 14 * m) (nEc Pa.darts en m)
            (aIM m p + 5 * mnD Pa en m) r ∧
        c₅.nmem (aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 + (fixCornerL M Pa).length + r) =
          if c.nmem (aA0 m p + 21 * mnD Pa en m + 6 + xtN c.nmem (p + 8 * m) (p + 6 * m)
            (p + 14 * m) (nEc Pa.darts en m) (aIM m p + 5 * mnD Pa en m) r) <
              mw hM hrot h Pa hk ℓ hnn Ct + 1 then 1 else 0) ∧
      (∀ i < dLen (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length,
        e.nmem (dBeta' (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) (fixCornerL M Pa).length
          (mnD Pa en m) + i) = min (c₅.nmem (aIM m p + i))
            (dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
              (fixCornerL M Pa).length + 16 * (4 * mnD Pa en m + 1 + 1))) ∧
      (∀ r < (fixCornerL M Pa).length,
        e.nmem (4 * mnD Pa en m + 1 + (fixCornerL M Pa).getD r 0) = 1) ∧
      (∀ j < mnD Pa en m,
        e.nmem (dBeta (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
            (fixCornerL M Pa).length + j) =
          (if c.nmem (aIM m p + 6 * mnD Pa en m + j) = 1 ∧
              c.nmem (aA1 m p + 21 * mnD Pa en m + 6 + c.nmem (aIM m p + 4 * mnD Pa en m + j)) <
                mw hM hrot h Pa hk ℓ hnn Ct + 1 then
            c.nmem (aIM m p + 7 * mnD Pa en m + j)
          else msL (mw hM hrot h Pa hk ℓ hnn Ct) nF) ∧
        e.nmem (dBeta (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
            (fixCornerL M Pa).length + mnD Pa en m + j) =
          if c.nmem (aIM m p + 6 * mnD Pa en m + j) = 1 then
            c.nmem (aIM m p + 7 * mnD Pa en m + j) else 0) ∧
      e.nmem (dBeta (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
        (fixCornerL M Pa).length + 3 * mnD Pa en m) = msL (mw hM hrot h Pa hk ℓ hnn Ct) nF ∧
      e.nmem (dBeta (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
        (fixCornerL M Pa).length + 3 * mnD Pa en m + 1) = msTh (mw hM hrot h Pa hk ℓ hnn Ct) nF ∧
      e.nmem (dBeta (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
        (fixCornerL M Pa).length + 3 * mnD Pa en m + 2) =
          msH0 (mw hM hrot h Pa hk ℓ hnn Ct) nF (fixPer M Pa) ∧
      (∀ i < q, e.nmem (aSL m p + i) = slV c.nmem Qb (p + m) (p + 9 * m - 1) i ∧
        e.nmem (aTI m p q + i) = slV c.nmem Qb (p + m) (p + 9 * m - 1) i) ∧
      (∀ a, a ≤ Wz → (∀ r < (fixCornerL M Pa).length,
          a ≠ 4 * mnD Pa en m + 1 + (fixCornerL M Pa).getD r 0) →
        (a < dBeta (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
            (fixCornerL M Pa).length ∨
          dBeta (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
            (fixCornerL M Pa).length + 2 * mnD Pa en m ≤ a) →
        (a < dBeta (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
            (fixCornerL M Pa).length + 3 * mnD Pa en m ∨
          dBeta (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
            (fixCornerL M Pa).length + 3 * mnD Pa en m + 3 ≤ a) →
        (a < dBeta' (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) (fixCornerL M Pa).length
            (mnD Pa en m) ∨
          dBeta' (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) (fixCornerL M Pa).length
            (mnD Pa en m) + dLen (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length ≤ a) →
        e.nmem a = c.nmem a) ∧
      (∀ a, Wz < a → (a < p ∨ p + 860 * m + 100 + 2 * q ≤ a) → e.nmem a = c.nmem a) ∧
      (∀ r < 1000, e.nreg r = 0) ∧
      (∀ j < 48, e.nreg (1000 + j) = KleinFix.knVM
        (dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length)
        (mnD Pa en m) (4 * mnD Pa en m + 1) (fixPer M Pa) (fixCornerL M Pa).length
        (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa))
        (dBeta' (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) (fixCornerL M Pa).length
          (mnD Pa en m)) (dLen (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length) j) ∧
      e.nreg 8010 = (fixCornerL M Pa).length ∧ e.nreg 8011 = 4 * mnD Pa en m + 1 + fixPer M Pa ∧
      e.nreg 8012 = dBeta (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
        (fixCornerL M Pa).length + 3 * mnD Pa en m + 3 ∧
      e.nreg 8013 = MSSP.isoN1 nF (mnD Pa en m) nV ∧ e.nreg 8014 = aSL m p ∧
      e.nreg 8015 = aTI m p q ∧ e.nreg 8016 = 4 * mnD Pa en m + 1 + fixPer M Pa ∧
      e.nreg 8017 = dBeta' (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa)
        (fixCornerL M Pa).length (mnD Pa en m) ∧
      e.nreg 8018 = dLen (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length ∧
      e.nreg 8019 = aLg m p q ∧
      e.nreg 8033 = dBeta (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
        (fixCornerL M Pa).length ∧ e.nreg 8034 = 3 * mnD Pa en m + 3 ∧
      (∀ r, ¬ EScr r → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  have hB := hC.b
  have lay := hB.lay
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  have eD : mnD Pa en m = nEc Pa.darts en m + 4 * nTc M Pa.darts en m := rfl
  have hper := fixPer_le h Pa
  have hcl := fixCornerL_le h Pa
  obtain ⟨-, hlt, -, -, -⟩ := fixCornerL_spec hrot Pa
  have hcV : nF ≤ mnD Pa en m := by
    have := cV_le_nD h Pa; rwa [Fintype.card_congr τv, Fintype.card_fin] at this
  have hKWd : ∀ B n Hc : ℕ, Klein.kleinWN B n Hc = 2 * (B + 16 * (n + 1)) + 1 +
      (2 * Hc + 1) * (2 * Hc + 1) + (2 * Hc + 1) := fun _ _ _ => rfl
  set w := mw hM hrot h Pa hk ℓ hnn Ct with hw
  set Hc := msHI w nF nV (fixPer M Pa) with hHc
  set B := dB w (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length with hBd
  have hBdef : B = w + 40 * mnD Pa en m + 2 * fixPer M Pa + 2 * (fixCornerL M Pa).length +
    (fixCornerL M Pa).length * (fixCornerL M Pa).length + 20 := rfl
  have hHcb : msL w nF + w + 1 ≤ Hc := by
    have h1 : 1 ≤ msK w nF := by unfold msK; omega
    rw [hHc]; unfold msHI; omega
  have hMo := Nat.le_mul_self (2 * Hc + 1)
  have hKW' := hKWd B (4 * mnD Pa en m + 1) Hc
  have hlen : dLen (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length =
    37 * mnD Pa en m + fixPer M Pa + 2 * (fixCornerL M Pa).length + 11 := rfl
  have hkw2 : 2 * (B + 16 * (4 * mnD Pa en m + 1 + 1)) + 1 + 2 * Hc + 1 +
      Klein.kleinWN B (4 * mnD Pa en m + 1) Hc ≤ Wz := by
    rw [hKW'] at hKW ⊢; omega
  -- stage C3
  obtain ⟨c₄, t₄, ex₄, ht₄, hxt, hfl, hsl, M₄, R₄, rr₄, rm₄, o₄⟩ :=
    msC3_run (P := P) hM hrot h Pa hk hnn τv τf c₀ c hc hC r00 r06 r07 hqd lQ
      (by omega) (by omega) hWW
  have k4 : ∀ r, (r < 7336 ∨ 7349 ≤ r ∨ (7340 ≤ r ∧ r < 7346)) → (r < 7370 ∨ 7371 < r) →
      (r < 8180 ∨ 8273 ≤ r ∨ (8220 ≤ r ∧ r < 8270)) → c₄.nreg r = c.nreg r :=
    fun r h1 h2 h3 => R₄ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  have hIMp : Wz < aIM m p := by unfold aIM; omega
  have m4 : ∀ a, Wz < a → a < aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 →
      c₄.nmem a = c.nmem a := fun a h1 h2 =>
    M₄ a (Or.inl h2) (fun r hr => by have := hlt r hr; omega)
      (by unfold aDU aIM at *; omega) (Or.inl (by unfold aSL aIM at *; omega))
      (Or.inl (by unfold aTI aIM at *; omega))
  have hσl : ∀ d : CutD M Pa.darts, (mσ h Pa hk d : ℕ) < mnD Pa en m := fun d => (mσ h Pa hk d).2
  have eKW : Klein.kleinWN (dB w (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length)
      (4 * mnD Pa en m + 1) (msHI w nF nV (fixPer M Pa)) = Klein.kleinWN B (4 * mnD Pa en m + 1) Hc :=
    rfl
  have eB : dB w (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length = B := rfl
  have eH : msHI w nF nV (fixPer M Pa) = Hc := rfl
  obtain ⟨c₅, u₅, ex₅, hu₅, hD, hb5, h5L, h5T, h5H, M₅, R₅, rr₅, rm₅, o₅⟩ :=
    msD_run (P := P) c₄ ex₄.wb_right (w := w) (cV := nF) (cF := nV) (k := fixPer M Pa)
      (t := (fixCornerL M Pa).length) (nD := mnD Pa en m) (IM := aIM m p) (A1 := aA1 m p)
      (H := w + 1) (N1 := MSSP.isoN1 nF (mnD Pa en m) nV) (SL := aSL m p) (TI := aTI m p q)
      (Lg := aLg m p q)
      (by rw [k4 _ (by omega) (by omega) (by omega)]; exact hB.rw)
      (by rw [k4 _ (by omega) (by omega) (by omega)]; exact hB.r98)
      (by rw [k4 _ (by omega) (by omega) (by omega)]; exact hB.r99)
      (by rw [k4 _ (by omega) (by omega) (by omega)]; exact hB.per)
      (by rw [k4 _ (by omega) (by omega) (by omega)]; exact hB.ncl)
      (by rw [k4 _ (by omega) (by omega) (by omega)]; exact hB.r97)
      (by rw [k4 _ (by omega) (by omega) (by omega)]; exact lay 2 (by omega))
      (by rw [k4 _ (by omega) (by omega) (by omega)]; exact lay 11 (by omega))
      (by rw [k4 _ (by omega) (by omega) (by omega)]; exact hB.rH)
      (by rw [k4 _ (by omega) (by omega) (by omega)]; exact hB.rN1)
      (by rw [k4 _ (by omega) (by omega) (by omega)]; exact lay 14 (by omega))
      (by rw [k4 _ (by omega) (by omega) (by omega)]; exact lay 15 (by omega))
      (by rw [k4 _ (by omega) (by omega) (by omega)]; exact lay 16 (by omega))
      (fun j hj => by
        obtain ⟨d, rfl⟩ : ∃ d, (mσ h Pa hk d : ℕ) = j := ⟨(mσ h Pa hk).symm ⟨j, hj⟩, by simp⟩
        rw [m4 _ (by omega) (by unfold aIM; omega)]
        have := hB.kin.is d; simp only [Klein.iIS] at this
        rw [this]; split_ifs <;> omega)
      (fun j hj => by
        obtain ⟨d, rfl⟩ : ∃ d, (mσ h Pa hk d : ℕ) = j := ⟨(mσ h Pa hk).symm ⟨j, hj⟩, by simp⟩
        rw [m4 _ (by omega) (by unfold aIM; omega)]
        have := hB.kin.nt d; simp only [Klein.iNT] at this
        rw [this]; have := (τv ((mN Pa).tail d)).2; omega)
      (by unfold dBeta; omega) (by unfold aIM aA1; omega)
      (by omega) (by unfold aIM aA1; omega) (by unfold aA1; omega)
  have m4' : ∀ a, Wz < a → (a < aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 ∨
      aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 + 2 * (fixCornerL M Pa).length ≤ a) →
      (a < aDU m p ∨ aDU m p + fixPer M Pa ≤ a) → (a < aSL m p ∨ aSL m p + q ≤ a) →
      (a < aTI m p q ∨ aTI m p q + q ≤ a) → c₄.nmem a = c.nmem a := fun a h0 h1 h2 h3 h4 =>
    M₄ a h1 (fun r hr => by have := hlt r hr; omega) h2 h3 h4
  have k5 : ∀ r, (r < 8200 ∨ 8262 ≤ r) → (r < 7360 ∨ 7361 < r) → (r < 7370 ∨ 7371 < r) →
      (r < 8273 ∨ 8279 ≤ r) → c₅.nreg r = c₄.nreg r := fun r h1 h2 h3 h4 =>
    R₅ r h1 (by omega) (by omega) (by omega) (by omega) h4
  have m5 : ∀ a, Wz < a → c₅.nmem a = c₄.nmem a := fun a ha =>
    M₅ a (Or.inr (by unfold dBeta; omega)) (Or.inr (by unfold dBeta; omega))
  obtain ⟨e, u₆, ex₆, hu₆, hcp, M₆, z6, kv6, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
      s33, s34, R₆, rr₆, rm₆, o₆⟩ :=
    msE2_execW (P := P) c₅ ex₅.wb_right hD (by unfold dBeta'; omega) (by unfold aIM aA1; omega)
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [dBeta', aA1, aSL, aTI, aLg, dLen]) <;> omega)
  have m6 : ∀ a, (a < dBeta' w nF nV (fixPer M Pa) (fixCornerL M Pa).length (mnD Pa en m) ∨
      dBeta' w nF nV (fixPer M Pa) (fixCornerL M Pa).length (mnD Pa en m) +
        dLen (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length ≤ a) →
      (a < aA1 m p ∨ aA1 m p + dLen (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length ≤ a) →
      e.nmem a = c₅.nmem a := M₆
  refine ⟨e, t₄ + (u₅ + u₆), c₅, ex₄.seq (ex₅.seq ex₆), ?_, fun a h1 h2 => ?_, fun r hr => ?_,
    hcp, fun r hr => ?_, fun j hj => ?_, ?_, ?_, ?_, fun i hi => ?_, fun a h0 h1 h2 h3 h4 => ?_,
    fun a h0 h1 => ?_, z6, kv6, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s33, s34,
    fun r hr => ?_, by rw [rr₆, rr₅, rr₄], by rw [rm₆, rm₅, rm₄], by rw [o₆, o₅, o₄]⟩
  · have : costE2 (dLen (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length) ≤
        costE2 (dLen (5 * m) m m) := by unfold costE2 dLen; omega
    unfold costD; omega
  · rw [m5 a (by unfold aIM at h1; omega)]; exact m4 a (by unfold aIM at h1; omega) h2
  · rw [m5 _ (by unfold aIM; omega), m5 _ (by unfold aIM; omega)]; exact hxt r hr
  · have := hlt r hr
    rw [m6 _ (Or.inl (by unfold dBeta'; omega)) (Or.inl (by unfold aA1; omega)),
      M₅ _ (Or.inl (by unfold dBeta; omega)) (Or.inl (by unfold dBeta; omega))]
    exact hfl r hr
  · have hb := hb5 j hj
    rw [m6 _ (Or.inl (by unfold dBeta dBeta'; omega)) (Or.inl (by unfold dBeta aA1; omega)),
      m6 _ (Or.inl (by unfold dBeta dBeta'; omega)) (Or.inl (by unfold dBeta aA1; omega))]
    have e1 : c₄.nmem (aIM m p + 6 * mnD Pa en m + j) = c.nmem (aIM m p + 6 * mnD Pa en m + j) :=
      m4 _ (by unfold aIM; omega) (by unfold aIM; omega)
    have e2 : c₄.nmem (aIM m p + 7 * mnD Pa en m + j) = c.nmem (aIM m p + 7 * mnD Pa en m + j) :=
      m4 _ (by unfold aIM; omega) (by unfold aIM; omega)
    have e3 : c₄.nmem (aIM m p + 4 * mnD Pa en m + j) = c.nmem (aIM m p + 4 * mnD Pa en m + j) :=
      m4 _ (by unfold aIM; omega) (by unfold aIM; omega)
    have e4 : ∀ x, x < 4 * mnD Pa en m + 1 → c₄.nmem (aA1 m p + 21 * mnD Pa en m + 6 + x) =
        c.nmem (aA1 m p + 21 * mnD Pa en m + 6 + x) := fun x hx =>
      m4' _ (by unfold aA1; omega) (Or.inr (by unfold aIM aA1; omega))
        (Or.inr (by unfold aDU aA1; omega)) (Or.inl (by unfold aSL aA1; omega))
        (Or.inl (by unfold aTI aA1; omega))
    have hnt : c.nmem (aIM m p + 4 * mnD Pa en m + j) < 4 * mnD Pa en m + 1 := by
      obtain ⟨d, rfl⟩ : ∃ d, (mσ h Pa hk d : ℕ) = j := ⟨(mσ h Pa hk).symm ⟨j, hj⟩, by simp⟩
      have := hB.kin.nt d; simp only [Klein.iNT] at this
      rw [this]; have := (τv ((mN Pa).tail d)).2; omega
    rw [e1, e2, e3, e4 _ hnt] at hb
    exact hb
  · rw [m6 _ (Or.inl (by unfold dBeta dBeta'; omega)) (Or.inl (by unfold dBeta aA1; omega))]
    exact h5L
  · rw [m6 _ (Or.inl (by unfold dBeta dBeta'; omega)) (Or.inl (by unfold dBeta aA1; omega))]
    exact h5T
  · rw [m6 _ (Or.inl (by unfold dBeta dBeta'; omega)) (Or.inl (by unfold dBeta aA1; omega))]
    exact h5H
  · rw [m6 _ (Or.inr (by unfold dBeta' aSL; omega)) (Or.inr (by unfold aA1 aSL; omega)),
      m6 _ (Or.inr (by unfold dBeta' aTI; omega)) (Or.inr (by unfold aA1 aTI; omega)),
      m5 _ (by unfold aSL; omega), m5 _ (by unfold aTI; omega)]
    exact hsl i hi
  · rw [m6 a h4 (Or.inl (by unfold aA1; omega)), M₅ a h2 h3,
      M₄ a (Or.inl (by unfold aIM; omega)) h1 (Or.inl (by unfold aDU; omega))
        (Or.inl (by unfold aSL; omega)) (Or.inl (by unfold aTI; omega))]
  · rw [m6 a (Or.inr (by unfold dBeta'; omega)) (by unfold aA1 at *; omega), m5 a h0,
      m4' a h0 (by unfold aIM at *; omega) (by unfold aDU at *; omega)
        (by unfold aSL at *; omega) (by unfold aTI at *; omega)]
  · simp only [EScr] at hr
    rw [R₆ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), k5 r (by omega) (by omega) (by omega) (by omega),
      k4 r (by omega) (by omega) (by omega)]

end MsEnc

end BKMNW

end PlanarFlow
