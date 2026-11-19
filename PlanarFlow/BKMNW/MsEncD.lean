module

public import PlanarFlow.BKMNW.MsEncC

/-!
# The composed MSSP encoder, part D: targets, flags, slots, the constants, the real words, the copy

From the state after stage C (`StC`):

* **`msC3_run`** (`msC3a ; msC3b ; msC3c`, with `msC3a_execW'`): the target words and their reach
  bits after Klein's image, the flags `1` at `4 nD + 1 + CS[r]` in the low memory, the slots
  `SL[i] = TI[i] = CN[FL[Q[i]]]`, on the words of the state after stage C;
* **`msD_run`** (`msD1 ; msD2`): the constants of the start (`DReg`) and the real words of the
  start in the low memory at `β`;
* **`msE_run`** (`msE2`): the clipped image at `β'`, the zero registers, `knVM`, the registers
  of the call.
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

/-- The step bound of stage C3 at the maxima. -/
def costC3 (m q : ℕ) : ℕ :=
  (14 + hpCost xtAL + hpCost xtBL + hpCost xtWL + (16 + 8) * m + 5) +
    (hpCost mkWL + (5 + 8) * m + 5) + (hpCost slAL + hpCost slWL + (9 + 8) * q + 5)

set_option maxHeartbeats 8000000 in
/-- **Stage C3 on the machine** (on the words of the state after stage C). -/
theorem msC3_run (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e)
    {p q Qb nF nV : ℕ} (τv : CutV M Pa.darts ≃ Fin nF) (τf : CutF M Pa.darts ≃ Fin nV)
    {Ct : STFlow.DTree (mN Pa)} {T₀ : STFlow.DTree (cutMap Pa.rev_mem_darts').dual}
    {C₀ : STFlow.DTree (mN Pa)} {ts : List (CutV M Pa.darts)} {cs : List (CutF M Pa.darts)}
    (c₀ c : Config) (hc : WordsBounded W c)
    (hC : StC hM hrot h Pa hk ℓ hnn p q c₀ c τv τf Ct T₀ C₀ ts cs)
    (r00 : c₀.nreg 8000 = m) (r06 : c₀.nreg 8006 = q) (r07 : c₀.nreg 8007 = Qb)
    (hqd : ∀ i < q, c₀.nmem (Qb + i) < m) (lQ : Qb + q ≤ p)
    (hl0 : 4 * mnD Pa en m + 1 + fixPer M Pa ≤ Qb) (hHp : mw hM hrot h Pa hk ℓ hnn Ct + 1 ≤ p)
    (hWW : p + 860 * m + 1000 + 2 * q ≤ W) :
    ∃ e t, Exec P W msC3 c e t ∧ t ≤ costC3 m q ∧
      (∀ r < (fixCornerL M Pa).length,
        e.nmem (aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 + r) =
          xtN c.nmem (p + 8 * m) (p + 6 * m) (p + 14 * m) (nEc Pa.darts en m)
            (aIM m p + 5 * mnD Pa en m) r ∧
        e.nmem (aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 + (fixCornerL M Pa).length + r) =
          if c.nmem (aA0 m p + 21 * mnD Pa en m + 6 + xtN c.nmem (p + 8 * m) (p + 6 * m)
            (p + 14 * m) (nEc Pa.darts en m) (aIM m p + 5 * mnD Pa en m) r) <
              mw hM hrot h Pa hk ℓ hnn Ct + 1 then 1 else 0) ∧
      (∀ r < (fixCornerL M Pa).length,
        e.nmem (4 * mnD Pa en m + 1 + (fixCornerL M Pa).getD r 0) = 1) ∧
      (∀ i < q, e.nmem (aSL m p + i) = slV c.nmem Qb (p + m) (p + 9 * m - 1) i ∧
        e.nmem (aTI m p q + i) = slV c.nmem Qb (p + m) (p + 9 * m - 1) i) ∧
      (∀ a, (a < aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 ∨
          aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 + 2 * (fixCornerL M Pa).length ≤ a) →
        (∀ r < (fixCornerL M Pa).length, a ≠ 4 * mnD Pa en m + 1 + (fixCornerL M Pa).getD r 0) →
        (a < aDU m p ∨ aDU m p + fixPer M Pa ≤ a) → (a < aSL m p ∨ aSL m p + q ≤ a) →
        (a < aTI m p q ∨ aTI m p q + q ≤ a) → e.nmem a = c.nmem a) ∧
      (∀ r, (r < 7336 ∨ 7340 ≤ r) → (r < 7346 ∨ 7349 ≤ r) → r ≠ 7370 → r ≠ 7371 →
        (r < 8180 ∨ 8194 ≤ r) → (r < 8200 ∨ 8220 ≤ r) → (r < 8270 ∨ 8273 ≤ r) →
        e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  have eD : mnD Pa en m = nEc Pa.darts en m + 4 * nTc M Pa.darts en m := rfl
  have hper := fixPer_le h Pa
  have hcl := fixCornerL_le h Pa
  have hB := hC.b
  have lay := hB.lay
  obtain ⟨hinc, hlt, -, -, -⟩ := fixCornerL_spec hrot Pa
  have hm1 : 1 ≤ m := by have := ixOf_lt h (Pa.d 0); omega
  have hcV : nF ≤ mnD Pa en m := by
    have := cV_le_nD h Pa; rwa [Fintype.card_congr τv, Fintype.card_fin] at this
  have rq : ∀ r, 8000 ≤ r → r ≤ 8009 → c.nreg r = c₀.nreg r := fun r h1 h2 =>
    hB.reg r (by simp only [EScr]; omega)
  -- the bounds of the target words
  have hb : ∀ r < (fixCornerL M Pa).length, c.nmem (p + 8 * m + r) < fixPer M Pa ∧
      c.nmem (p + 6 * m + c.nmem (p + 8 * m + r)) < m ∧
      nEc Pa.darts en m + c.nmem (p + 14 * m + c.nmem (p + 6 * m + c.nmem (p + 8 * m + r))) <
        mnD Pa en m ∧
      xtN c.nmem (p + 8 * m) (p + 6 * m) (p + 14 * m) (nEc Pa.darts en m)
        (aIM m p + 5 * mnD Pa en m) r < 4 * mnD Pa en m + 1 := by
    intro r hr
    have hcs := (hB.cs r hr).1
    have hl := hlt r hr
    have htr := hB.tr ((fixCornerL M Pa).getD r 0) hl
    have hix := ixOf_lt h ((tour M Pa.darts)^[(fixCornerL M Pa).getD r 0] (Pa.d 0))
    rw [hcs, htr]
    have hrk := (hB.rk _ hix).2
    rw [hrk]
    have hT : M.tail ((tour M Pa.darts)^[(fixCornerL M Pa).getD r 0] (Pa.d 0)) ∈
        cutS M Pa.darts := by
      rw [show Pa.d 0 = (fixT0 Pa hk).1 from rfl, ← tourT_iterate_val Pa.rev_mem_darts' _ (fixT0 Pa hk)]
      exact ((tourT _)^[_] _).2
    have hcT : cT M Pa.darts en (ixOf en m ((tour M Pa.darts)^[(fixCornerL M Pa).getD r 0]
        (Pa.d 0))) < nTc M Pa.darts en m :=
      cnt_lt (fun j => M.tail (en j) ∈ cutS M Pa.darts) hix (by rw [en_ixOf h]; exact hT)
    refine ⟨hl, hix, by omega, ?_⟩
    unfold xtN
    rw [hcs, htr, hrk]
    have hjl : nEc Pa.darts en m + cT M Pa.darts en (ixOf en m ((tour M Pa.darts)^[
        (fixCornerL M Pa).getD r 0] (Pa.d 0))) < mnD Pa en m := by omega
    obtain ⟨d, hd⟩ : ∃ d, (mσ h Pa hk d : ℕ) =
        nEc Pa.darts en m + cT M Pa.darts en (ixOf en m ((tour M Pa.darts)^[(fixCornerL M Pa).getD
          r 0] (Pa.d 0))) := ⟨(mσ h Pa hk).symm ⟨_, hjl⟩, by simp⟩
    have := hB.kin.nh d
    simp only [Klein.iNH] at this
    rw [← hd, this]
    have := (τv ((mN Pa).head d)).2
    omega
  obtain ⟨e₁, t₁, ex₁, ht₁, hS₁, hxt, M₁, r36, R₁, rr₁, rm₁, o₁⟩ :=
    msC3a_execW' (P := P) c hc (H := mw hM hrot h Pa hk ℓ hnn Ct + 1) (IM := aIM m p)
      (nD := mnD Pa en m) (A0 := aA0 m p) (p := p) (nE := nEc Pa.darts en m) (k := fixPer M Pa)
      (t := (fixCornerL M Pa).length) (m := m) (DU := aDU m p) (Qb := Qb) (q := q)
      (SL := aSL m p) (TI := aTI m p q) hB.rH (lay 2 (by omega)) hB.r97 (lay 10 (by omega))
      (lay 0 (by omega)) hB.r28 hB.per hB.ncl (by rw [rq _ (by omega) (by omega)]; exact r00)
      (lay 9 (by omega)) (by rw [rq _ (by omega) (by omega)]; exact r07)
      (by rw [rq _ (by omega) (by omega)]; exact r06) (lay 14 (by omega)) (lay 15 (by omega))
      hb hcl hper (by unfold aIM; omega) (by unfold aIM aA0; omega)
      (by unfold aA0; have : nEc Pa.darts en m ≤ m := cnt_le_self _ m; omega)
  have m1 : ∀ a, a < aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 → e₁.nmem a = c.nmem a :=
    fun a ha => M₁ a (Or.inl ha)
  have hcs1 : ∀ r < (fixCornerL M Pa).length, e₁.nmem (p + 8 * m + r) = (fixCornerL M Pa).getD r 0 :=
    fun r hr => by rw [m1 _ (by unfold aIM; omega)]; exact (hB.cs r hr).1
  obtain ⟨e₂, t₂, ex₂, ht₂, hS₂, hfl, M₂, R₂, rr₂, rm₂, o₂⟩ :=
    msC3b_exec (P := P) e₁ ex₁.wb_right hS₁ r36
      (fun r hr => by rw [hcs1 r hr]; exact hlt r hr)
      (fun r hr r' hr' e => by
        rw [hcs1 r hr, hcs1 r' hr'] at e
        rcases Nat.lt_trichotomy r r' with h1 | h1 | h1
        · have := hinc r r' h1 hr'; omega
        · exact h1
        · have := hinc r' r h1 hr; omega)
      (by omega) hcl (by unfold aDU; omega) (by unfold aDU; omega)
  have m2 : ∀ a, (∀ r < (fixCornerL M Pa).length,
      a ≠ 4 * mnD Pa en m + 1 + (fixCornerL M Pa).getD r 0) →
      (a < aDU m p ∨ aDU m p + fixPer M Pa ≤ a) → e₂.nmem a = e₁.nmem a := fun a h1 h2 =>
    M₂ a (fun r hr => by rw [hcs1 r hr]; exact h1 r hr) h2
  have mlow : ∀ a, Qb ≤ a → a < p + 16 * m → e₂.nmem a = c.nmem a := fun a h1 h2 => by
    rw [m2 a (fun r hr => by have := hlt r hr; omega) (Or.inl (by unfold aDU; omega)),
      m1 a (by unfold aIM; omega)]
  have hq2 : ∀ i < q, e₂.nmem (Qb + i) < m ∧ e₂.nmem (p + m + e₂.nmem (Qb + i)) ≤ m := by
    intro i hi
    have e1 : e₂.nmem (Qb + i) = c₀.nmem (Qb + i) := by
      rw [mlow _ (by omega) (by omega), hB.mem _ (Or.inl (by omega))]
    have hx := hqd i hi
    rw [e1, mlow _ (by omega) (by omega), hB.fl _ hx]
    have := NsStep.labI_lt (M := M) h hx
    exact ⟨hx, by omega⟩
  obtain ⟨e₃, t₃, ex₃, ht₃, hS₃, hsl, M₃, R₃, rr₃, rm₃, o₃⟩ :=
    msC3c_execW (P := P) e₂ ex₂.wb_right hS₂ hq2 hm1 lQ (by unfold aSL; omega)
      (by unfold aSL aTI; omega) (by unfold aTI; omega)
  have hslv : ∀ i < q, slV e₂.nmem Qb (p + m) (p + 9 * m - 1) i =
      slV c.nmem Qb (p + m) (p + 9 * m - 1) i := fun i hi => by
    obtain ⟨b1, b2⟩ := hq2 i hi
    unfold slV
    have e1 : e₂.nmem (Qb + i) = c.nmem (Qb + i) := mlow _ (by omega) (by omega)
    have e2 : e₂.nmem (p + m + e₂.nmem (Qb + i)) = c.nmem (p + m + c.nmem (Qb + i)) := by
      rw [← e1]; exact mlow _ (by omega) (by omega)
    rw [e2, mlow _ (by omega) (by omega)]
  have m31 : ∀ a, Qb ≤ a → (a < aDU m p ∨ aDU m p + fixPer M Pa ≤ a) →
      (a < aSL m p ∨ aSL m p + q ≤ a) → (a < aTI m p q ∨ aTI m p q + q ≤ a) →
      e₃.nmem a = e₁.nmem a := fun a h0 h1 h2 h3 => by
    rw [M₃ a h2 h3, m2 a (fun r hr => by have := hlt r hr; omega) h1]
  have hxt' := fun r (hr : r < (fixCornerL M Pa).length) => by
    have := hxt r hr
    rwa [← m31 (aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 + r) (by unfold aIM; omega)
      (Or.inl (by unfold aIM aDU; omega)) (Or.inl (by unfold aIM aSL; omega))
      (Or.inl (by unfold aIM aTI; omega)),
      ← m31 (aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 + (fixCornerL M Pa).length + r)
      (by unfold aIM; omega) (Or.inl (by unfold aIM aDU; omega))
      (Or.inl (by unfold aIM aSL; omega)) (Or.inl (by unfold aIM aTI; omega))] at this
  refine ⟨e₃, t₁ + (t₂ + t₃), ex₁.seq (ex₂.seq ex₃), ?_, hxt', fun r hr => ?_, fun i hi => ?_,
    fun a h1 h2 h3 h4 h5 => ?_, fun r h1 h2 h3 h4 h5 h6 h7 => ?_, by rw [rr₃, rr₂, rr₁],
    by rw [rm₃, rm₂, rm₁], by rw [o₃, o₂, o₁]⟩
  · unfold costC3
    have : (16 + 8) * (fixCornerL M Pa).length ≤ (16 + 8) * m := Nat.mul_le_mul_left _ hcl
    have : (5 + 8) * (fixCornerL M Pa).length ≤ (5 + 8) * m := Nat.mul_le_mul_left _ hcl
    omega
  · rw [M₃ _ (Or.inl (by have := hlt r hr; unfold aSL; omega))
      (Or.inl (by have := hlt r hr; unfold aTI; omega)), ← hcs1 r hr]
    exact hfl r hr
  · rw [← hslv i hi]; exact hsl i hi
  · rw [M₃ a h4 h5, m2 a h2 h3, M₁ a h1]
  · rw [R₃ r h3 h4 h6 h7, R₂ r h3 h4 h6, R₁ r h1 h2 h3 h4 h5 h6]

/-- **Stage D.** -/
def msD : Stmt := .seq msD1 msD2

set_option maxHeartbeats 4000000 in
/-- **Stage D on the machine** (`msD1a_exec`, `msD1b_execW`, `msD2_execW`). -/
theorem msD_run (c : Config) (hc : WordsBounded W c)
    {w cV cF k t nD IM A1 H N1 SL TI Lg : ℕ}
    (r42 : c.nreg 7342 = w) (r98 : c.nreg 8298 = cV) (r99 : c.nreg 8299 = cF)
    (r56 : c.nreg 8156 = k) (r57 : c.nreg 8157 = t) (r97 : c.nreg 8297 = nD)
    (r82 : c.nreg 8282 = IM) (r91 : c.nreg 8291 = A1) (r35 : c.nreg 7335 = H)
    (r28 : c.nreg 7328 = N1) (r94 : c.nreg 8294 = SL) (r95 : c.nreg 8295 = TI)
    (r96 : c.nreg 8296 = Lg)
    (his : ∀ j < nD, c.nmem (IM + 6 * nD + j) ≤ 1)
    (hnt : ∀ j < nD, c.nmem (IM + 4 * nD + j) < 4 * nD + 1)
    (l1 : dBeta w nD k t + 3 * nD + 3 ≤ IM) (l2 : IM + 8 * nD ≤ A1)
    (hW0 : 8 * MsEnc.msHI w cV cF k + 20 ≤ W)
    (hW1 : 8 * Klein.kleinWN (dB w nD k t) (4 * nD + 1) (MsEnc.msHI w cV cF k) + 300 * nD +
      4 * k + 8 * t + 500 ≤ W ∧ IM + 8 * nD + 500 ≤ W ∧ A1 + 21 * nD + 500 ≤ W)
    (hW2 : A1 + 40 * nD + 50 ≤ W ∧ H + MsEnc.msL w cV + 50 ≤ W) :
    ∃ e u, Exec P W msD c e u ∧
      u ≤ (13 + 4 + hpCost dh1L + hpCost dh2L + hpCost dh3L + (3 + hpCost dh4L + hpCost dh5L)) +
        (hpCost twSL + hpCost twWL + (19 + 8) * nD + 5 + 6) ∧
      DReg e w cV cF k t nD IM A1 H N1 SL TI Lg ∧
      (∀ j < nD, e.nmem (dBeta w nD k t + j) =
          (if c.nmem (IM + 6 * nD + j) = 1 ∧
              c.nmem (A1 + 21 * nD + 6 + c.nmem (IM + 4 * nD + j)) < H then
            c.nmem (IM + 7 * nD + j) else MsEnc.msL w cV) ∧
        e.nmem (dBeta w nD k t + nD + j) =
          if c.nmem (IM + 6 * nD + j) = 1 then c.nmem (IM + 7 * nD + j) else 0) ∧
      e.nmem (dBeta w nD k t + 3 * nD) = MsEnc.msL w cV ∧
      e.nmem (dBeta w nD k t + 3 * nD + 1) = MsEnc.msTh w cV ∧
      e.nmem (dBeta w nD k t + 3 * nD + 2) = MsEnc.msH0 w cV k ∧
      (∀ a, (a < dBeta w nD k t ∨ dBeta w nD k t + 2 * nD ≤ a) →
        (a < dBeta w nD k t + 3 * nD ∨ dBeta w nD k t + 3 * nD + 3 ≤ a) → e.nmem a = c.nmem a) ∧
      (∀ r, (r < 8200 ∨ 8262 ≤ r) → r ≠ 7360 → r ≠ 7361 → r ≠ 7370 → r ≠ 7371 →
        (r < 8273 ∨ 8279 ≤ r) → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  obtain ⟨c₀', u₀, x₀, hu₀, hA, R0, m0, r0, rm0, o0⟩ := msD1a_exec (P := P) c hc r42 r98 r99 r56
    r57 r97 r82 r91 r35 r28 r94 r95 r96 hW0
  obtain ⟨c₁, u₁', x₁', hu₁', hD, R1', m1', r1', rm1', o1'⟩ :=
    msD1b_execW (P := P) c₀' x₀.wb_right hA hW1
  have x₁ : Exec P W msD1 c c₁ (u₀ + u₁') := x₀.seq x₁'
  have m1 : c₁.nmem = c.nmem := by rw [m1', m0]
  have R1 : ∀ r, (r < 8220 ∨ 8262 ≤ r) → r ≠ 7370 → r ≠ 7371 → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => by rw [R1' r h1 h2 h3, R0 r (by omega) h2 h3]
  have r1 : c₁.rreg = c.rreg := by rw [r1', r0]
  have rm1 : c₁.rmem = c.rmem := by rw [rm1', rm0]
  have o1 : c₁.output = c.output := by rw [o1', o0]
  have hu₁ : u₀ + u₁' ≤ 13 + 4 + hpCost dh1L + hpCost dh2L + hpCost dh3L +
      (3 + hpCost dh4L + hpCost dh5L) := by omega
  obtain ⟨c₂, u₂, x₂, hu₂, hD2, hb, h3, h4, h5, M2, R2, rr2, rm2, o2⟩ :=
    msD2_execW (P := P) c₁ x₁.wb_right hD (by rw [m1]; exact his) (by rw [m1]; exact hnt) l1 l2 hW2
  rw [m1] at hb
  exact ⟨c₂, u₀ + u₁' + u₂, x₁.seq x₂, by omega, hD2, hb, h3, h4, h5,
    fun a h1 h2 => by rw [M2 a h1 h2, m1], fun r h1 h2 h3 h4 h5 h6 => by
      rw [R2 r h2 h3 h4 h5 (by omega) h6, R1 r (by omega) h4 h5],
    by rw [rr2, r1], by rw [rm2, rm1], by rw [o2, o1]⟩

end MsEnc

end BKMNW

end PlanarFlow
