module

public import PlanarFlow.BKMNW.MsEncI

/-!
# The composed MSSP encoder `msEnc` and its specification

**`msEnc`** `= msA ; msB ; msC ; msR` (`msA1 ; msA2 ; svSet ; msB1 ; rsSet ; msB2 ; msB3 ; msB4 ;
msC1 ; msC2 ; msC3 ; msD1 ; msD2 ; msE2`).

**`msEnc_out`**: under the hypotheses of `MsCall.MsEncSpec'` (with `R = Rm`, `wz = wzm`), `msEnc` runs within `msEncCost m k q` steps to
`MsCall.MsEncOut'` (Klein's explicit start `KStart` of the call, the low memory `kMem`, the
registers of the call, the slots and targets of the queries), keeping the registers outside `EScr`.
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

/-- **The encoder of the MSSP call.** -/
def msEnc : Stmt := .seq msA (.seq msB (.seq msC msR))

/-- The real words of the start are values below the modulus `2 Hc + 1`. -/
lemma trip_vals (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e) {nF nV : ℕ}
    (τv : CutV M Pa.darts ≃ Fin nF) (Ct : STFlow.DTree (mN Pa)) :
    (∀ d, 0 ≤ Klein.tripWt (mN Pa) (ccut hM hrot Pa hk ℓ fun e _ => hnn e).k
        (cutG Pa.rev_mem_darts' (fixT0 Pa hk)) (cutPiece M Pa.darts)
        (mkl hM hrot h Pa hk ℓ hnn Ct) 0 d ∧
      Klein.tripWt (mN Pa) (ccut hM hrot Pa hk ℓ fun e _ => hnn e).k
        (cutG Pa.rev_mem_darts' (fixT0 Pa hk)) (cutPiece M Pa.darts)
        (mkl hM hrot h Pa hk ℓ hnn Ct) 0 d <
          2 * (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) : ℤ) + 1) ∧
    (∀ d, 0 ≤ Klein.tripφ (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct) d ∧
      Klein.tripφ (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct) d <
          2 * (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) : ℤ) + 1) ∧
    Klein.tripL (CutV M Pa.darts) (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct) =
      (msL (mw hM hrot h Pa hk ℓ hnn Ct) nF : ℤ) ∧
    Klein.tripTh (CutV M Pa.darts) (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct) =
      (msTh (mw hM hrot h Pa hk ℓ hnn Ct) nF : ℤ) ∧
    Klein.tripH0 (CutV M Pa.darts) (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct)
      (ccut hM hrot Pa hk ℓ fun e _ => hnn e).k =
      (msH0 (mw hM hrot h Pa hk ℓ hnn Ct) nF (fixPer M Pa) : ℤ) ∧
    msL (mw hM hrot h Pa hk ℓ hnn Ct) nF + mw hM hrot h Pa hk ℓ hnn Ct <
      2 * msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) + 1 ∧
    msTh (mw hM hrot h Pa hk ℓ hnn Ct) nF < 2 * msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) + 1 ∧
    msH0 (mw hM hrot h Pa hk ℓ hnn Ct) nF (fixPer M Pa) <
      2 * msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) + 1 := by
  have eV : Fintype.card (CutV M Pa.darts) = nF := by rw [Fintype.card_congr τv, Fintype.card_fin]
  have hkk : (ccut hM hrot Pa hk ℓ fun e _ => hnn e).k = fixPer M Pa := ccut_k _ _ _ _ _ _
  have eL : Klein.tripL (CutV M Pa.darts) (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct) =
      (msL (mw hM hrot h Pa hk ℓ hnn Ct) nF : ℤ) := by rw [tripL_eq, eV]
  have hI := msHI_dec (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa)
  have hTh : msTh (mw hM hrot h Pa hk ℓ hnn Ct) nF ≤ msH0 (mw hM hrot h Pa hk ℓ hnn Ct) nF
      (fixPer M Pa) := by rw [msH0_dec]; omega
  have hb : msL (mw hM hrot h Pa hk ℓ hnn Ct) nF + mw hM hrot h Pa hk ℓ hnn Ct <
      2 * msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) + 1 := by omega
  have hb2 : msH0 (mw hM hrot h Pa hk ℓ hnn Ct) nF (fixPer M Pa) <
      2 * msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) + 1 := by omega
  have hkl : ∀ d, 0 < mkl hM hrot h Pa hk ℓ hnn Ct d := mkl_pos hM hrot h Pa hk hnn Ct
  have hklw : ∀ d ∈ cutPiece M Pa.darts, mkl hM hrot h Pa hk ℓ hnn Ct d ≤
      (mw hM hrot h Pa hk ℓ hnn Ct : ℤ) := fun d hd => mkl_le_mw hM hrot h Pa hk hnn Ct hd
  have hbz : ((msL (mw hM hrot h Pa hk ℓ hnn Ct) nF + mw hM hrot h Pa hk ℓ hnn Ct : ℕ) : ℤ) <
      2 * (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) : ℤ) + 1 := by exact_mod_cast hb
  push_cast at hbz
  refine ⟨fun d => ?_, fun d => ?_, eL, by rw [tripTh_eq, eV], by rw [tripH0_eq, eV, hkk],
    hb, by omega, hb2⟩
  · unfold Klein.tripWt
    split_ifs with hd
    · have := hkl d; have := hklw d hd.1; omega
    · rw [eL]; omega
  · unfold Klein.tripφ
    split_ifs with hd
    · have := hkl d; have := hklw d hd; omega
    · omega

lemma msEnc_natOnly : Klein.natOnly msEnc = true := by decide +kernel

set_option maxHeartbeats 40000000 in
/-- **The encoder meets `MsEncOut'`.** -/
theorem msEnc_out (hM : M.IsPlane) (hrot : M.RotTrans) (en : ℕ → D) (m : ℕ) (Pa : SPath M)
    (ℓ : D → ℤ) (Lmax q : ℕ) (ts : ℕ → D) (RVb RTb Pb Lb Qb Ob p Wz W : ℕ) (I : Input)
    (c : Config) (h : EnumOK M en m) (hk : 0 < Pa.k) (hnn : ∀ e, 0 ≤ ℓ e)
    (hq : ∀ i < q, M.face (ts i) ∈ Pa.faces) (hc : WordsBounded W c)
    (hIn : MsCall.MsIn M en m Pa ℓ Lmax q ts RVb RTb Pb Lb Qb Ob p c)
    (hPl : MsCall.MsPlace m Pa.k q Wz W RVb RTb Pb Lb Qb Ob p (Rm m Pa.k q))
    (hz : ∀ a ≤ Wz, c.nmem a = 0) (hwz : wzm m Lmax ≤ Wz) :
    ∃ e t, Exec I W msEnc c e t ∧ t ≤ msEncCost m Pa.k q ∧
      MsCall.MsEncOut' Pa ℓ q ts Wz Ob p (Rm m Pa.k q) (KCf m Pa.k) (ZCf m) c e ∧
      (∀ r, ¬ EScr r → e.nreg r = c.nreg r) ∧
      (∀ r, 8000 ≤ r → r ≤ 8009 → e.nreg r = c.nreg r) := by
  classical
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  have eD : mnD Pa en m = nEc Pa.darts en m + 4 * nTc M Pa.darts en m := rfl
  have hper := fixPer_le h Pa
  have hcl := fixCornerL_le h Pa
  have hm1 : 1 ≤ m := by have := ixOf_lt h (Pa.d 0); omega
  have hL : ∀ e, ℓ e ≤ Lmax := len_le_of_in h (fun i hi => hIn.ln i hi)
  obtain ⟨hRV1, hRV2⟩ := hPl.rv
  obtain ⟨hRT1, hRT2⟩ := hPl.rt
  obtain ⟨hPb1, hPb2⟩ := hPl.pb
  obtain ⟨hLb1, hLb2⟩ := hPl.lb
  obtain ⟨hQb1, hQb2⟩ := hPl.qb
  obtain ⟨hOb1, hOb2⟩ := hPl.ob
  have hpW := hPl.pw
  have hRm : Rm m Pa.k q = 860 * m + 100 + 2 * q + 3 * KCf m Pa.k + 1 := rfl
  have hKC : 1000 ≤ KCf m Pa.k := by unfold KCf MsCall.kSteps; omega
  have hwz' : 100 * (KM m Lmax + 1) + 4 * ((5 * m + 2) * (N1M m * (Lmax + 1))) +
      100 * ((m + 1) * (m + 1)) ≤ Wz := by
    have : wzm m Lmax = 100 * (KM m Lmax + 1) + 4 * ((5 * m + 2) * (N1M m * (Lmax + 1))) +
      100 * ((m + 1) * (m + 1)) := by unfold wzm; ring
    omega
  -- stage A
  obtain ⟨c₁, t₁, nF, nV, τv, τf, ex₁, ht₁, hA⟩ :=
    msA_exec (P := I) hM hrot h Pa hk c hc hIn (by omega) (by omega) (by omega) (by omega)
      (by omega)
  have hcV2 : nF ≤ 2 * m := by
    have := card_cutV_le h Pa.darts; rwa [Fintype.card_congr τv, Fintype.card_fin] at this
  have hcF2 : nV ≤ 2 * m + 1 := by
    have := card_cutF_le hM hrot h Pa.darts (Pa.d 0)
    rwa [Fintype.card_congr τf, Fintype.card_fin] at this
  have hnD5 : mnD Pa en m ≤ 5 * m := by omega
  have eV : Fintype.card (CutV M Pa.darts) = nF := by rw [Fintype.card_congr τv, Fintype.card_fin]
  have eF : Fintype.card (CutF M Pa.darts) = nV := by rw [Fintype.card_congr τf, Fintype.card_fin]
  have eDc : Fintype.card (CutD M Pa.darts) = mnD Pa en m := card_cutD h
  have hN1 : MSSP.isoN1 nF (mnD Pa en m) nV ≤ N1M m := isoN1_mono hcV2 hnD5 hcF2
  have hWzp : wzm m Lmax < p := by omega
  have hN1L : MSSP.isoN1 nF (mnD Pa en m) nV * (Lmax + 1) ≤ N1M m * (Lmax + 1) :=
    Nat.mul_le_mul_right _ hN1
  have hNL2 : mnD Pa en m * (MSSP.isoN1 nF (mnD Pa en m) nV * (Lmax + 1)) ≤
      (5 * m + 2) * (N1M m * (Lmax + 1)) := Nat.mul_le_mul (by omega) hN1L
  have hnVF : nV * nF ≤ (m + 1) * (m + 1) * 4 := by
    have := Nat.mul_le_mul hcF2 hcV2; nlinarith
  have hN1b : MSSP.isoN1 nF (mnD Pa en m) nV ≤ N1M m * (Lmax + 1) :=
    hN1.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hN1c : N1M m * (Lmax + 1) ≤ (5 * m + 2) * (N1M m * (Lmax + 1)) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hVb : 2 * (mnD Pa en m * (MSSP.isoN1 nF (mnD Pa en m) nV * (Lmax + 1)) + 1) +
      MSSP.isoN1 nF (mnD Pa en m) nV + nF + 2 * (nV * nF) ≤ p := by
    have hmE : m + 1 ≤ (m + 1) * (m + 1) := Nat.le_mul_self _
    generalize mnD Pa en m * (MSSP.isoN1 nF (mnD Pa en m) nV * (Lmax + 1)) = A at hNL2 ⊢
    generalize (5 * m + 2) * (N1M m * (Lmax + 1)) = B at hNL2 hN1c hwz'
    generalize nV * nF = C at hnVF ⊢
    generalize (m + 1) * (m + 1) = E at hnVF hwz' hmE
    generalize N1M m * (Lmax + 1) = G at hN1b hN1c
    omega
  -- stage B
  obtain ⟨c₂, t₂, Ct, ex₂, ht₂, hB⟩ :=
    msB_exec (P := I) hM hrot h Pa hk hnn τv τf c c₁ ex₁.wb_right hA hIn.r00 hIn.r05 hIn.r09
      (fun i hi => hIn.ln i hi) (by omega) hVb (by omega)
  have hw0 := mw_le hM hrot h Pa hk hnn hL Ct
  rw [eV, eDc, eF] at hw0
  obtain ⟨-, hwM, hHM, hKM⟩ := sizes_le (L := Lmax) hcV2 hcF2 hnD5 hper hcl hw0
  have hHK := le_KM m Lmax
  have hHge := HM_ge m Lmax
  have hwF : nF * mw hM hrot h Pa hk ℓ hnn Ct ≤ 2 * m * wM m Lmax := Nat.mul_le_mul hcV2 hwM
  have hwF' : 2 * m * wM m Lmax ≤ HM m Lmax := by
    have : 2 * m * wM m Lmax ≤ 30 * (2 * (2 * m) * wM m Lmax) := by nlinarith
    omega
  -- stage C
  obtain ⟨c₃, t₃, T₀, C₀, tsl, cs, ex₃, ht₃, hC⟩ :=
    msC_exec (P := I) hM hrot h Pa hk hnn τv τf Ct c c₂ ex₂.wb_right hB hIn.r00
      (by
        have : nF * ((mw hM hrot h Pa hk ℓ hnn Ct + 1) + (mw hM hrot h Pa hk ℓ hnn Ct + 1)) =
          2 * (nF * mw hM hrot h Pa hk ℓ hnn Ct) + 2 * nF := by ring
        omega) (by omega)
  -- stages C3, D, E
  obtain ⟨e, t₄, c₅, ex₄, ht₄, hm5, hxt, hcp, hfl, hb, hbL, hbT, hbH, hsl, hlow, hhigh, z6, kv6,
      s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s33, s34, hreg, rr, rm, oo⟩ :=
    msR_run (P := I) hM hrot h Pa hk hnn τv τf (Wz := Wz) c c₃ ex₃.wb_right hC hIn.r00 hIn.r06
      hIn.r07 (fun i hi => (hIn.qd i hi).1) (by omega) hQb1
      (by
        have : 64 ≤ Klein.kleinWN (dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
          (fixCornerL M Pa).length) (4 * mnD Pa en m + 1)
          (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa)) := by
          unfold Klein.kleinWN; omega
        omega) (by omega) (by omega)
  -- the input words of Klein's run
  have hkk : (ccut hM hrot Pa hk ℓ fun e _ => hnn e).k = fixPer M Pa := ccut_k _ _ _ _ _ _
  have hBb := hC.b
  obtain ⟨hinc, hlt, -, -, -⟩ := fixCornerL_spec hrot Pa
  set Pin : Input := ⟨List.ofFn (fun i : Fin (dLen (mnD Pa en m) (fixPer M Pa)
    (fixCornerL M Pa).length) => e.nmem (dBeta' (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa)
      (fixCornerL M Pa).length (mnD Pa en m) + i)), fun _ => 0⟩ with hPind
  have hPinL : Pin.data.length = dLen (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length := by
    simp [hPind]
  have hPinG : ∀ i, Pin.data.getD i 0 = if i < dLen (mnD Pa en m) (fixPer M Pa)
      (fixCornerL M Pa).length then e.nmem (dBeta' (mw hM hrot h Pa hk ℓ hnn Ct) nF nV
        (fixPer M Pa) (fixCornerL M Pa).length (mnD Pa en m) + i) else 0 := by
    intro i
    split_ifs with hi
    · simp [hPind, List.getD_eq_getElem?_getD, hi]
    · simp [hPind, List.getD_eq_getElem?_getD, hi]
  have hPin : ∀ i, Pin.data.getD i 0 = if i < dLen (mnD Pa en m) (fixPer M Pa)
      (fixCornerL M Pa).length then min (c₅.nmem (aIM m p + i))
        (dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
          (fixCornerL M Pa).length + 16 * (4 * mnD Pa en m + 1 + 1)) else 0 := by
    intro i; rw [hPinG i]; split_ifs with hi
    · exact hcp i hi
    · rfl
  have hKS := kstart_of hM hrot h Pa hk hnn hC c₅.nmem hm5 hxt Pin hPin
  have hdB : dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length =
      mw hM hrot h Pa hk ℓ hnn Ct + 40 * mnD Pa en m + 2 * fixPer M Pa +
        2 * (fixCornerL M Pa).length + (fixCornerL M Pa).length * (fixCornerL M Pa).length + 20 := rfl
  have hdLen : dLen (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length =
      37 * mnD Pa en m + fixPer M Pa + 2 * (fixCornerL M Pa).length + 11 := rfl
  have hKWe : Klein.kleinWN (dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
      (fixCornerL M Pa).length) (4 * mnD Pa en m + 1) (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV
        (fixPer M Pa)) = 2 * (dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
      (fixCornerL M Pa).length + 16 * (4 * mnD Pa en m + 1 + 1)) + 1 +
      (2 * msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) + 1) *
        (2 * msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) + 1) +
      (2 * msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) + 1) := rfl
  have hMo := Nat.le_mul_self (2 * msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) + 1)
  have hdBe : dBeta (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
      (fixCornerL M Pa).length = dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
      (fixCornerL M Pa).length + 16 * (4 * mnD Pa en m + 1 + 1) + 1 := rfl
  have hdBe' : dBeta' (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa)
      (fixCornerL M Pa).length (mnD Pa en m) = Klein.kleinWN (dB (mw hM hrot h Pa hk ℓ hnn Ct)
      (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length) (4 * mnD Pa en m + 1)
        (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa)) + 1 := rfl
  obtain ⟨tW, tP, tL, tT, tH, bL, bT, bH⟩ := trip_vals hM hrot h Pa hk hnn τv Ct
  -- the low memory below `Wz` that the encoder does not write is zero
  have hlow0 : ∀ a ≤ Wz, (∀ r < (fixCornerL M Pa).length,
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
      e.nmem a = 0 := fun a ha h1 h2 h3 h4 => by
    rw [hlow a ha h1 h2 h3 h4, hBb.mem a (Or.inl (by omega))]; exact hz a ha
  -- the low memory is `kMem`
  have hkmem : ∀ a ≤ Wz, e.nmem a = MsCall.kMem (dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m)
      (fixPer M Pa) (fixCornerL M Pa).length) (4 * mnD Pa en m + 1)
      (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa)) (mc0 hM hrot h Pa hk ℓ hnn Ct) Pin a := by
    have bL' : (msL (mw hM hrot h Pa hk ℓ hnn Ct) nF : ℤ) <
        2 * (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) : ℤ) + 1 := by
      have : msL (mw hM hrot h Pa hk ℓ hnn Ct) nF <
        2 * msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) + 1 :=
        lt_of_le_of_lt (Nat.le_add_right _ _) bL
      exact_mod_cast this
    have bT' : (msTh (mw hM hrot h Pa hk ℓ hnn Ct) nF : ℤ) <
        2 * (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) : ℤ) + 1 := by exact_mod_cast bT
    have bH' : (msH0 (mw hM hrot h Pa hk ℓ hnn Ct) nF (fixPer M Pa) : ℤ) <
        2 * (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) : ℤ) + 1 := by exact_mod_cast bH
    unfold mc0
    refine kmem_of (by rw [hkk]; omega) (by omega) (fun j hj => ?_) (fun d => ?_) (fun d => ?_)
      ⟨by rw [tL]; omega, by rw [tL]; exact bL', by rw [tL, Int.toNat_natCast]; exact hbL⟩
      ⟨by rw [tT]; omega, by rw [tT]; exact bT', by rw [tT, Int.toNat_natCast]; exact hbT⟩
      ⟨by rw [tH]; omega, by rw [tH]; exact bH', by rw [tH, Int.toNat_natCast]; exact hbH⟩
      (fun i hi => by rw [hPinG i]; rw [hPinL] at hi; simp only [hi, ↓reduceIte]) (fun a ha hr => ?_)
    · rw [hkk] at hj
      unfold mfl
      by_cases hjL : j ∈ fixCornerL M Pa
      · obtain ⟨r, hr, hrj⟩ := List.getElem_of_mem hjL
        have := hfl r hr
        rw [List.getD_eq_getElem _ _ hr, hrj] at this
        simp only [hjL, decide_true, ↓reduceIte]; exact this
      · simp only [hjL, decide_false, Bool.false_eq_true, ↓reduceIte]
        refine hlow0 _ (by omega) (fun r hr e => hjL ?_) (Or.inl (by omega)) (Or.inl (by omega))
          (Or.inl (by omega))
        rw [show j = (fixCornerL M Pa).getD r 0 by omega, List.getD_eq_getElem _ _ hr]
        exact List.getElem_mem _
    · obtain ⟨g0, g1⟩ := tW d
      refine ⟨g0, g1, ?_⟩
      have := (hb _ (mσ h Pa hk d).2).1
      rw [hdBe] at this
      rw [this]; exact wt_word hM hrot h Pa hk hnn hC d
    · obtain ⟨g0, g1⟩ := tP d
      refine ⟨g0, g1, ?_⟩
      have := (hb _ (mσ h Pa hk d).2).2
      rw [hdBe] at this
      rw [this]; exact ph_word hM hrot h Pa hk hnn hBb d
    · rw [hPinL] at hr
      refine hlow0 a ha (fun r' hr' => ?_) ?_ ?_ ?_
      · have := hlt r' hr'; rw [hkk] at hr; omega
      · rw [hdBe]; omega
      · rw [hdBe]; omega
      · rw [hdBe']; omega
  have hKWle : Klein.kleinWN (dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
      (fixCornerL M Pa).length) (4 * mnD Pa en m + 1)
        (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa)) ≤ KM m Lmax := hKM
  have hHc1 : 1 ≤ msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) := by
    have h1 : 1 ≤ msK (mw hM hrot h Pa hk ℓ hnn Ct) nF := by unfold msK; omega
    rw [msHI_dec]; omega
  -- the slots of the queries
  have hslot : ∀ i < q, ∃ r < (fixCornerL M Pa).length,
      slV c₃.nmem Qb (p + m) (p + 9 * m - 1) i = r ∧
        fixCorner M Pa ((fixCornerL M Pa).getD r 0) = M.face (ts i) := by
    intro i hi
    obtain ⟨hx, hen⟩ := hIn.qd i hi
    have e1 : c₃.nmem (Qb + i) = c.nmem (Qb + i) := hBb.mem _ (Or.inl (by omega))
    have hf : M.face (en (c.nmem (Qb + i))) ∈ Pa.faces := by rw [hen]; exact hq i hi
    obtain ⟨r, hr, e2, e3⟩ := hBb.cn _ hx hf
    refine ⟨r, hr, ?_, by rw [e3, hen]⟩
    unfold slV
    rw [e1, hBb.fl _ hx, e2]
  refine ⟨e, t₁ + (t₂ + (t₃ + t₄)), ex₁.seq (ex₂.seq (ex₃.seq ex₄)), ?_, ?_, fun r hr => ?_,
    fun r h1 h2 => ?_⟩
  · unfold msEncCost
    unfold costB costC3 costD at *
    omega
  · refine ⟨ccut hM hrot Pa hk ℓ fun e _ => hnn e, MSSP.treeW Ct, mnD Pa en m, mσ h Pa hk,
      4 * mnD Pa en m + 1, dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
        (fixCornerL M Pa).length, (fixCornerL M Pa).length, fun x => 1 + (τv x : ℕ),
      StEnc.ιG _ (cQ h Pa hk), fun y => 2 * mnD Pa en m + 1 + (τf y : ℕ), StEnc.ιE _ (cQ h Pa hk),
      mX Pa, mfl Pa, Pin, STFlow.toDD T₀, C₀, (List.finRange nF).map τv.symm, tsl,
      (List.finRange nV).map τf.symm, cs, mc0 hM hrot h Pa hk ℓ hnn Ct,
      msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa), aSL m p, aTI m p q, aLg m p q,
      4 * mnD Pa en m + 1 + fixPer M Pa, dBeta (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m)
        (fixPer M Pa) (fixCornerL M Pa).length, 3 * mnD Pa en m + 3, hKS, ?_, hHc1, by omega,
      by rw [hPinL]; omega, by rw [hPinL]; unfold ZCf dLen; omega, by omega, by rw [hdBe]; omega,
      hkmem, fun a ha => ?_, fun a ha h1 h2 h3 => ?_, fun r hr => ?_, ?_, fun r hr => ?_,
      s10, by rw [s11, hkk]; rfl, by rw [s12, hdBe]; rfl, ?_, s14, s15, s16, s17,
      by rw [s18, hPinL], s19, s33, s34, fun i hi => ?_, fun i hi => ?_, by unfold aSL; omega,
      by unfold aSL aLg; omega, by unfold aTI; omega, by unfold aTI aLg; omega,
      by unfold aLg; omega, by unfold aLg; omega, fun a h1 h2 => ?_, rr.trans hBb.rr,
      rm.trans hBb.rm, oo.trans hBb.out⟩
    · -- Klein's run bound
      rw [hkk, kRank_len hrot Pa]
      have c1 : Fintype.card (CutV M Pa.darts) ≤ 2 * m := by rw [eV]; exact hcV2
      have c2 : Fintype.card (CutF M Pa.darts) ≤ 2 * m + 1 := by rw [eF]; exact hcF2
      have c3 : (cutPiece M Pa.darts).card ≤ 5 * m := by
        have := card_le_univ (cutPiece M Pa.darts); rw [eDc] at this; omega
      exact kSteps_le_KCf c1 c2 hnD5 c3 (by omega) hper
        (fixCornerL_len_le hrot Pa) (fixCornerL_len_le hrot Pa)
    · -- the low words are below `Wz`
      rw [hkmem a ha]
      unfold mc0
      rw [kMem_mkC0]
      have hr := Klein.resW_lt (M := 2 * msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) + 1)
        (by omega)
      split_ifs
      all_goals first
        | omega
        | exact (hr _).le.trans (by omega)
        | (rw [hPin]; split_ifs <;> omega)
    · -- zero outside the regions
      exact hlow0 a ha (fun r hr' => by have := hlt r hr'; omega) (by rw [hdBe] at h2 ⊢; omega)
        (by rw [hdBe] at h2 ⊢; omega) (by rw [hPinL] at h3; rw [hdBe']; omega)
    · rw [z6 r (by omega)]; unfold mc0; rw [natCfg_mkC0_nreg]
    · intro j hj; rw [kv6 j hj, hkk, hPinL]
    · by_cases hr' : r < 1000
      · rw [z6 r hr']; omega
      · have hj : r - 1000 < 48 := by omega
        have := kv6 (r - 1000) hj
        rw [show 1000 + (r - 1000) = r by omega] at this
        rw [this]
        have := knVM_le (dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
          (fixCornerL M Pa).length) (mnD Pa en m) (4 * mnD Pa en m + 1) (fixPer M Pa)
          (fixCornerL M Pa).length (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa))
          (dBeta' (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) (fixCornerL M Pa).length
            (mnD Pa en m)) (dLen (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length) hj
        have hKbig : dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
            (fixCornerL M Pa).length + 16 * (4 * mnD Pa en m + 1 + 1) +
            msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa) ≤
            Klein.kleinWN (dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
              (fixCornerL M Pa).length) (4 * mnD Pa en m + 1)
              (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa)) := by rw [hKWe]; omega
        omega
    · rw [s13]; unfold MsCall.kN1; rw [eV, eDc, eF]
    · -- the slots
      obtain ⟨r, hr, e1, e2⟩ := hslot i hi
      refine ⟨(fixCornerL M Pa).getD r 0, by rw [hkk]; exact hlt r hr, ?_, ?_, ?_⟩
      · unfold mfl; rw [List.getD_eq_getElem _ _ hr]; simp
      · rw [ccut_root]; exact e2
      · rw [(hsl i hi).1, e1]; exact (kRank_corner hinc hr).symm
    · obtain ⟨r, hr, e1, e2⟩ := hslot i hi
      rw [(hsl i hi).2, e1]
      exact ⟨hr, by unfold mX; rw [e2]; rfl⟩
    · rw [hhigh a h1 (by rw [hRm] at h2; omega)]
      exact hBb.mem a (by omega)
  · rw [hreg r hr]; exact hBb.reg r hr
  · rw [hreg r (by simp only [EScr]; omega)]; exact hBb.reg r (by simp only [EScr]; omega)

/-- **The encoder of the MSSP call meets its specification**, on every plane map:
`MsEncSpec' M msEnc EScr msEncCost KCf ZCf Rm wzm` (`Rm m k q = 860 m + 100 + 2 q + 3 KCf m k + 1`,
`wzm m L = 100 (KM m L + 1) + 4 (5 m + 2) (N1M m (L + 1)) + 100 (m + 1)²`, explicit polynomials). -/
theorem msEnc_spec : MsCall.MsEncSpec' M msEnc EScr msEncCost (fun m k _ => KCf m k)
    (fun m _ _ => ZCf m) Rm wzm := by
  intro hM hrot en m P ℓ Lmax q ts RVb RTb Pb Lb Qb Ob p Wz W I c hEn hk hnn hq hc hIn hPl hz hwz
  exact msEnc_out hM hrot en m P ℓ Lmax q ts RVb RTb Pb Lb Qb Ob p Wz W I c hEn hk hnn hq hc hIn
    hPl hz hwz

/-- **The MSSP call `msspCall' msEnc` meets `MsspCallSpec` unconditionally**, within
`msCostS C C₀` steps (`(cMachS C C₀).mssp m k` for `1 ≤ m`, `q ≤ 2 k`). -/
theorem msspCall'_cMachS_msEnc (C C₀ : ℕ) :
    MsCall.MsspCallSpec M (MsCall.msspCall' msEnc) (fun r => EScr r ∨ MsCall.msScr r)
      (msCostS C C₀) Rm wzm :=
  msspCall'_cMachS C C₀ msEnc_spec

end MsEnc

end BKMNW

end PlanarFlow
