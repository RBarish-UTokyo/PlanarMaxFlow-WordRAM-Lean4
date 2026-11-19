module

public import PlanarFlow.BKMNW.MsEncH

/-!
# The composed MSSP encoder, part I: the words of the real start, the size bounds

* `mw_le` (`w ≤ nD · N₁ (L + 1)`), **`sizes_le`** (the constants of the call are below the maxima
  `N1M`, `wM`, `HM`, `KM`);
* **`wt_word`**, **`ph_word`** (the words stage D2 writes are the natural values of Klein's trip
  words `tripWt`, `tripφ`);
* `kMem_le` (the low memory of a start is bounded).
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

lemma mw_le (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e) {Lmax : ℕ}
    (hL : ∀ e, ℓ e ≤ Lmax) (Ct : STFlow.DTree (mN Pa)) :
    mw hM hrot h Pa hk ℓ hnn Ct ≤ mnD Pa en m * (MSSP.isoN1 (Fintype.card (CutV M Pa.darts))
      (Fintype.card (CutD M Pa.darts)) (Fintype.card (CutF M Pa.darts)) * (Lmax + 1)) := by
  unfold mw
  rw [tripW_toNat_sum fun d _ => (mkl_pos hM hrot h Pa hk hnn Ct d).le]
  have h1 := Finset.sum_le_card_nsmul (cutPiece M Pa.darts)
    (fun d => (mkl hM hrot h Pa hk ℓ hnn Ct d).toNat)
    (MSSP.isoN1 (Fintype.card (CutV M Pa.darts)) (Fintype.card (CutD M Pa.darts))
      (Fintype.card (CutF M Pa.darts)) * (Lmax + 1)) (fun d _ => by
        have := mkl_bound hM hrot h Pa hk hnn hL Ct d
        have h2 : ((mkl hM hrot h Pa hk ℓ hnn Ct d).toNat : ℤ) < ((MSSP.isoN1 (Fintype.card
          (CutV M Pa.darts)) (Fintype.card (CutD M Pa.darts)) (Fintype.card (CutF M Pa.darts)) *
            (Lmax + 1) : ℕ) : ℤ) := by push_cast; omega
        exact_mod_cast h2.le)
  have h3 : (cutPiece M Pa.darts).card ≤ mnD Pa en m := by
    have := card_cutD (L := Pa.darts) h
    have := card_le_univ (cutPiece M Pa.darts)
    have eD : mnD Pa en m = nEc Pa.darts en m + 4 * nTc M Pa.darts en m := rfl
    omega
  simp only [smul_eq_mul] at h1
  exact h1.trans (Nat.mul_le_mul_right _ h3)

/-- **The constants of the call are below the maxima.** -/
lemma sizes_le {m L nF nV nD k t w : ℕ} (h1 : nF ≤ 2 * m) (h2 : nV ≤ 2 * m + 1)
    (h3 : nD ≤ 5 * m) (h4 : k ≤ m) (h5 : t ≤ m)
    (h6 : w ≤ nD * (MSSP.isoN1 nF nD nV * (L + 1))) :
    MSSP.isoN1 nF nD nV ≤ N1M m ∧ w ≤ wM m L ∧ msHI w nF nV k ≤ HM m L ∧
      Klein.kleinWN (dB w nD k t) (4 * nD + 1) (msHI w nF nV k) ≤ KM m L := by
  have a1 : MSSP.isoN1 nF nD nV ≤ N1M m := isoN1_mono h1 h3 h2
  have a2 : w ≤ wM m L := by
    unfold wM
    exact h6.trans (Nat.mul_le_mul h3 (Nat.mul_le_mul_right _ a1))
  have a3 : msHI w nF nV k ≤ HM m L := msHI_mono a2 h1 h2 h4
  refine ⟨a1, a2, a3, kleinWN_mono (dB_mono a2 h3 h4 h5) (by omega) a3⟩

/-- **The trip weight words of stage D2.** -/
lemma wt_word (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e) {p q nF nV : ℕ}
    {τv : CutV M Pa.darts ≃ Fin nF} {τf : CutF M Pa.darts ≃ Fin nV}
    {Ct : STFlow.DTree (mN Pa)} {T₀ : STFlow.DTree (cutMap Pa.rev_mem_darts').dual}
    {C₀ : STFlow.DTree (mN Pa)} {ts : List (CutV M Pa.darts)} {cs : List (CutF M Pa.darts)}
    {c₀ c : Config} (hC : StC hM hrot h Pa hk ℓ hnn p q c₀ c τv τf Ct T₀ C₀ ts cs)
    (d : CutD M Pa.darts) :
    (if c.nmem (aIM m p + 6 * mnD Pa en m + mσ h Pa hk d) = 1 ∧
        c.nmem (aA1 m p + 21 * mnD Pa en m + 6 + c.nmem (aIM m p + 4 * mnD Pa en m + mσ h Pa hk d)) <
          mw hM hrot h Pa hk ℓ hnn Ct + 1 then
      c.nmem (aIM m p + 7 * mnD Pa en m + mσ h Pa hk d)
    else msL (mw hM hrot h Pa hk ℓ hnn Ct) nF) =
      (Klein.tripWt (mN Pa) (ccut hM hrot Pa hk ℓ fun e _ => hnn e).k
        (cutG Pa.rev_mem_darts' (fixT0 Pa hk)) (cutPiece M Pa.darts)
        (mkl hM hrot h Pa hk ℓ hnn Ct) 0 d).toNat := by
  classical
  have hB := hC.b
  have eV : Fintype.card (CutV M Pa.darts) = nF := by rw [Fintype.card_congr τv, Fintype.card_fin]
  have his := hB.kin.is d
  have hnt := hB.kin.nt d
  have hln := hB.kin.ln d
  simp only [Klein.iIS, Klein.iNT, Klein.iLN] at his hnt hln
  rw [his, hnt, hC.d1]
  have hall : ∀ u y, MSSP.Reach (MSSP.pieceGraph (mN Pa) univ (mℓD hM hrot h Pa hk ℓ hnn Ct)) u y :=
    fun u y => STFlow.reach_dual (cut_isPlane hM hrot Pa hk).dual _ u y
  have hsrc : Klein.srcW (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct) ≤
      ((mw hM hrot h Pa hk ℓ hnn Ct + 1 : ℕ) : ℤ) := by
    unfold Klein.srcW; rw [← mw_cast]; push_cast; omega
  have hr := reach_iff_lt (N := mN Pa) (S := cutPiece M Pa.darts)
    (kl := mkl hM hrot h Pa hk ℓ hnn Ct) (ℓD := mℓD hM hrot h Pa hk ℓ hnn Ct)
    (H := mw hM hrot h Pa hk ℓ hnn Ct + 1)
    (fun d _ => (mkl_pos hM hrot h Pa hk hnn Ct d).le)
    (fun d => (mℓD_pos hM hrot h Pa hk hnn Ct d).le)
    (fun d hd => by unfold mℓD mLD; simp only [hd, ↓reduceIte])
    (fun d hd => by unfold mℓD mLD; simp only [hd, ↓reduceIte]; split_ifs <;> push_cast <;> omega)
    hsrc hall ((mN Pa).tail (cutG Pa.rev_mem_darts' (fixT0 Pa hk) (1 % fixPer M Pa)))
    ((mN Pa).tail d)
  have hdst : Klein.tripDst (mN Pa) (ccut hM hrot Pa hk ℓ fun e _ => hnn e).k
      (cutG Pa.rev_mem_darts' (fixT0 Pa hk)) 0 =
      (mN Pa).tail (cutG Pa.rev_mem_darts' (fixT0 Pa hk) (1 % fixPer M Pa)) := by
    unfold Klein.tripDst; rw [Nat.zero_add, ccut_k]
  unfold Klein.tripWt
  rw [hdst]
  have hLe : Klein.tripL (CutV M Pa.darts) (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct) =
      (msL (mw hM hrot h Pa hk ℓ hnn Ct) nF : ℤ) := by rw [tripL_eq, eV]
  by_cases hd : d ∈ cutPiece M Pa.darts
  · by_cases hR : MSSP.Reach (MSSP.pieceGraph (mN Pa) (cutPiece M Pa.darts)
        (mkl hM hrot h Pa hk ℓ hnn Ct))
        ((mN Pa).tail (cutG Pa.rev_mem_darts' (fixT0 Pa hk) (1 % fixPer M Pa))) ((mN Pa).tail d)
    · have := hr.1 hR
      simp only [hd, hR, this, and_self, ↓reduceIte]
      exact hln hd
    · have : ¬ (MSSP.dist (MSSP.pieceGraph (mN Pa) univ (mℓD hM hrot h Pa hk ℓ hnn Ct))
          ((mN Pa).tail (cutG Pa.rev_mem_darts' (fixT0 Pa hk) (1 % fixPer M Pa)))
          ((mN Pa).tail d)).toNat < mw hM hrot h Pa hk ℓ hnn Ct + 1 := fun h' => hR (hr.2 h')
      simp only [hd, hR, this, and_false, ↓reduceIte, and_self, hLe, Int.toNat_natCast]
  · simp only [hd, ↓reduceIte, false_and, hLe, Int.toNat_natCast]
    simp

/-- **The weight words of stage D2.** -/
lemma ph_word (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e) {p q nF nV : ℕ}
    {τv : CutV M Pa.darts ≃ Fin nF} {τf : CutF M Pa.darts ≃ Fin nV}
    {Ct : STFlow.DTree (mN Pa)} {c₀ c : Config}
    (hB : StB hM hrot h Pa hk ℓ hnn p q c₀ c τv τf Ct) (d : CutD M Pa.darts) :
    (if c.nmem (aIM m p + 6 * mnD Pa en m + mσ h Pa hk d) = 1 then
      c.nmem (aIM m p + 7 * mnD Pa en m + mσ h Pa hk d) else 0) =
      (Klein.tripφ (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct) d).toNat := by
  have his := hB.kin.is d
  have hln := hB.kin.ln d
  simp only [Klein.iIS, Klein.iLN] at his hln
  rw [his]
  unfold Klein.tripφ
  by_cases hd : d ∈ cutPiece M Pa.darts
  · simp only [hd, ↓reduceIte]; exact hln hd
  · simp [hd]

end MsEnc

end BKMNW

end PlanarFlow
