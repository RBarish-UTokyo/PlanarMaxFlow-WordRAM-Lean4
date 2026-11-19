module

public import PlanarFlow.BKMNW.MsEncE

/-!
# The composed MSSP encoder, part F: Klein's start from the words (`KStart`)

* the start objects of the call: the targets `mX` (the copies of the corner faces), the flags
  `mfl` (the positions `fixCornerL`), the real start configuration `mc0` (`mkC0` with Klein's trip
  words of the cut `ccut`);
* `kRank_len`, **`xtN_eq`** (the target word of the `r`-th corner is the node of its copy);
* **`kstart_of`**: from the state after stage C (`StC`), a memory agreeing with it on Klein's image,
  with the target words of stage C3, and an input holding the image clipped at `Wb`, the full
  explicit start **`MsCall.KStart`** of the call.
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

/-- The targets: the copies of the corner faces. -/
noncomputable def mX (Pa : SPath M) (r : ℕ) : CutV M Pa.darts :=
  Sum.inl (fixCorner M Pa ((fixCornerL M Pa).getD r 0))

/-- The flags: the positions of the corners. -/
noncomputable def mfl (Pa : SPath M) (j : ℕ) : Bool := decide (j ∈ fixCornerL M Pa)

/-- **The real start configuration of the call.** -/
noncomputable def mc0 (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) (ℓ : D → ℤ) (hnn : ∀ e, 0 ≤ ℓ e)
    (Ct : STFlow.DTree (mN Pa)) : Config :=
  mkC0 (mnD Pa en m) (4 * mnD Pa en m + 1) (ccut hM hrot Pa hk ℓ fun e _ => hnn e).k (mfl Pa)
    (mσ h Pa hk)
    (Klein.tripWt (mN Pa) (ccut hM hrot Pa hk ℓ fun e _ => hnn e).k
      (cutG Pa.rev_mem_darts' (fixT0 Pa hk)) (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct) 0)
    (Klein.tripφ (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct))
    (Klein.tripL (CutV M Pa.darts) (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct))
    (Klein.tripTh (CutV M Pa.darts) (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct))
    (Klein.tripH0 (CutV M Pa.darts) (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct)
      (ccut hM hrot Pa hk ℓ fun e _ => hnn e).k)

/-- The number of flags below `K` is the number of corners. -/
lemma kRank_len (hrot : M.RotTrans) (Pa : SPath M) :
    Klein.kRank (mfl Pa) (fixPer M Pa) = (fixCornerL M Pa).length := by
  unfold Klein.kRank mfl
  have hnd : (fixCornerL M Pa).Nodup := (List.nodup_range).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext j
  simp only [mem_filter, mem_range, decide_eq_true_eq, List.mem_toFinset]
  constructor
  · exact fun h => h.2
  · intro hj
    refine ⟨?_, hj⟩
    unfold fixCornerL at hj
    exact List.mem_range.1 (List.mem_of_mem_filter hj)

/-- **The target word of the `r`-th corner is the node of the copy of its face.** -/
lemma xtN_eq (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} {hnn : ∀ e, 0 ≤ ℓ e} {p q nF nV : ℕ}
    {τv : CutV M Pa.darts ≃ Fin nF} {τf : CutF M Pa.darts ≃ Fin nV} {Ct : STFlow.DTree (mN Pa)}
    {c₀ c : Config} (hB : StB hM hrot h Pa hk ℓ hnn p q c₀ c τv τf Ct) {r : ℕ}
    (hr : r < (fixCornerL M Pa).length) :
    xtN c.nmem (p + 8 * m) (p + 6 * m) (p + 14 * m) (nEc Pa.darts en m)
      (aIM m p + 5 * mnD Pa en m) r = 1 + (τv (mX Pa r) : ℕ) := by
  obtain ⟨-, hlt, -, -, -⟩ := fixCornerL_spec hrot Pa
  have hcs := (hB.cs r hr).1
  have hl := hlt r hr
  set j := (fixCornerL M Pa).getD r 0 with hj
  have htr := hB.tr j hl
  have hix := ixOf_lt h ((tour M Pa.darts)^[j] (Pa.d 0))
  have hrk := (hB.rk _ hix).2
  set t : CutT M Pa.darts := (tourT Pa.rev_mem_darts')^[j] (fixT0 Pa hk) with ht
  have htv : t.1 = (tour M Pa.darts)^[j] (Pa.d 0) := tourT_iterate_val Pa.rev_mem_darts' _ _
  have hσ := mσ_pend h Pa hk t
  have hnh := hB.kin.nh (Sum.inr (Sum.inl t))
  simp only [Klein.iNH] at hnh
  unfold xtN
  rw [hcs, htr, hrk, ← htv, ← hσ, hnh, pend_head]
  unfold mX fixCorner
  rw [htv]

set_option maxHeartbeats 8000000 in
/-- **Klein's explicit start of the call from the words** (see the module docstring). -/
theorem kstart_of (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e)
    {p q nF nV : ℕ} {τv : CutV M Pa.darts ≃ Fin nF} {τf : CutF M Pa.darts ≃ Fin nV}
    {Ct : STFlow.DTree (mN Pa)} {T₀ : STFlow.DTree (cutMap Pa.rev_mem_darts').dual}
    {C₀ : STFlow.DTree (mN Pa)} {ts : List (CutV M Pa.darts)} {cs : List (CutF M Pa.darts)}
    {c₀ c₃ : Config} (hC : StC hM hrot h Pa hk ℓ hnn p q c₀ c₃ τv τf Ct T₀ C₀ ts cs)
    (mem5 : ℕ → ℕ)
    (hm5 : ∀ a, aIM m p ≤ a → a < aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 →
      mem5 a = c₃.nmem a)
    (hxt : ∀ r < (fixCornerL M Pa).length,
        mem5 (aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 + r) =
          xtN c₃.nmem (p + 8 * m) (p + 6 * m) (p + 14 * m) (nEc Pa.darts en m)
            (aIM m p + 5 * mnD Pa en m) r ∧
        mem5 (aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 + (fixCornerL M Pa).length + r) =
          if c₃.nmem (aA0 m p + 21 * mnD Pa en m + 6 + xtN c₃.nmem (p + 8 * m) (p + 6 * m)
            (p + 14 * m) (nEc Pa.darts en m) (aIM m p + 5 * mnD Pa en m) r) <
              mw hM hrot h Pa hk ℓ hnn Ct + 1 then 1 else 0)
    (Pin : Input)
    (hPin : ∀ i, Pin.data.getD i 0 =
      if i < dLen (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length then
        min (mem5 (aIM m p + i)) (dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa)
          (fixCornerL M Pa).length + 16 * (4 * mnD Pa en m + 1 + 1))
      else 0) :
    MsCall.KStart Pa ℓ (ccut hM hrot Pa hk ℓ fun e _ => hnn e) (MSSP.treeW Ct) (mnD Pa en m)
      (mσ h Pa hk) (4 * mnD Pa en m + 1)
      (dB (mw hM hrot h Pa hk ℓ hnn Ct) (mnD Pa en m) (fixPer M Pa) (fixCornerL M Pa).length)
      (fixCornerL M Pa).length (fun x => 1 + (τv x : ℕ)) (StEnc.ιG _ (cQ h Pa hk))
      (fun y => 2 * mnD Pa en m + 1 + (τf y : ℕ)) (StEnc.ιE _ (cQ h Pa hk)) (mX Pa) (mfl Pa) Pin
      (STFlow.toDD T₀) C₀ ((List.finRange nF).map τv.symm) ts ((List.finRange nV).map τf.symm) cs
      (mc0 hM hrot h Pa hk ℓ hnn Ct) (msHI (mw hM hrot h Pa hk ℓ hnn Ct) nF nV (fixPer M Pa)) := by
  classical
  have hB := hC.b
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  have eD : mnD Pa en m = nEc Pa.darts en m + 4 * nTc M Pa.darts en m := rfl
  have hkk : (ccut hM hrot Pa hk ℓ fun e _ => hnn e).k = fixPer M Pa := ccut_k _ _ _ _ _ _
  have hcV : nF ≤ mnD Pa en m := by
    have := cV_le_nD h Pa; rwa [Fintype.card_congr τv, Fintype.card_fin] at this
  have hcF : nV ≤ mnD Pa en m := by
    have := cF_le_nD' hM hrot h Pa hk; rwa [Fintype.card_congr τf, Fintype.card_fin] at this
  have eV : Fintype.card (CutV M Pa.darts) = nF := by rw [Fintype.card_congr τv, Fintype.card_fin]
  have eF : Fintype.card (CutF M Pa.darts) = nV := by rw [Fintype.card_congr τf, Fintype.card_fin]
  have hnD1 : 1 ≤ mnD Pa en m := by have := (mσ h Pa hk (cD0 Pa hk)).2; omega
  have hkr := kRank_len hrot Pa
  set w := mw hM hrot h Pa hk ℓ hnn Ct with hw
  set nD := mnD Pa en m with hnD
  set k := fixPer M Pa with hkd
  set t := (fixCornerL M Pa).length with htd
  set Wb := dB w nD k t + 16 * (4 * nD + 1 + 1) with hWb
  have hBdef : dB w nD k t = w + 40 * nD + 2 * k + 2 * t + t * t + 20 := rfl
  have hlen : dLen nD k t = 37 * nD + k + 2 * t + 11 := rfl
  have hWb1 : nD + 4 * nD + 1 + w + 1 ≤ Wb := by omega
  -- the clipped memory
  set memc : ℕ → ℕ := fun a => min (mem5 a) Wb with hmemc
  have hPc : ∀ i, i < dLen nD k t → Pin.data.getD i 0 = memc (aIM m p + i) := fun i hi => by
    rw [hPin i]; simp only [hi, ↓reduceIte, hmemc]
  -- the full image input
  set Pf : Input := ⟨List.ofFn (fun i : Fin (dLen nD k t) => mem5 (aIM m p + i)), fun _ => 0⟩ with hPf
  have hPf' : ∀ i, Pf.data.getD i 0 = if i < dLen nD k t then mem5 (aIM m p + i) else 0 := by
    intro i
    split_ifs with hi
    · simp [hPf, List.getD_eq_getElem?_getD, hi]
    · simp [hPf, List.getD_eq_getElem?_getD, hi]
  have hcl : ∀ i, Pin.data.getD i 0 = min (Pf.data.getD i 0) Wb := fun i => by
    rw [hPin i, hPf' i]; split_ifs <;> simp
  have hmw : ∀ d ∈ cutPiece M Pa.darts, (mkl hM hrot h Pa hk ℓ hnn Ct d).toNat ≤ w := fun d hd => by
    have := mkl_le_mw hM hrot h Pa hk hnn Ct hd; omega
  -- Klein's words with the piece in the clipped memory
  have hK5 : KInMS (mN Pa) (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct) (mσ h Pa hk)
      (fun x => 1 + (τv x : ℕ)) (StEnc.ιG _ (cQ h Pa hk))
      (fun y => 2 * mnD Pa en m + 1 + (τf y : ℕ)) (StEnc.ιE _ (cQ h Pa hk)) memc (aIM m p) := by
    refine KInMS.clip (KInMS.frame hB.kin (E := 4 * nD + 1) (StEnc.ιE_lt (cQ h Pa hk))
      (fun a h1 h2 => hm5 a h1 (by omega))) (by omega) (fun x => ?_) (fun d => ?_) (fun y => ?_)
      (fun d => ?_) (by omega) (fun d hd => by have := hmw d hd; omega)
    · have := (τv x).2; omega
    · have := NegSSSP.eIx_lt (M := (cutMap Pa.rev_mem_darts').dual) (StEnc.enEq (cQ h Pa hk)) d
      unfold StEnc.ιG; omega
    · have := (τf y).2; omega
    · have := StEnc.ιE_lt (cQ h Pa hk) d; omega
  have hlenI : Klein.iHD nD (4 * nD + 1) k + 4 ≤ dLen nD k t := by
    simp only [Klein.iHD, Klein.iIV]; omega
  have hXT : Klein.iXT nD (4 * nD + 1) k = 37 * nD + k + 11 := by simp only [Klein.iXT]; ring
  have hxtv : ∀ r < t, xtN c₃.nmem (p + 8 * m) (p + 6 * m) (p + 14 * m) (nEc Pa.darts en m)
      (aIM m p + 5 * mnD Pa en m) r = 1 + (τv (mX Pa r) : ℕ) := fun r hr => xtN_eq hM hrot h Pa hk hB hr
  have hall : ∀ u y, MSSP.Reach (MSSP.pieceGraph (mN Pa) univ (mℓD hM hrot h Pa hk ℓ hnn Ct)) u y :=
    fun u y => STFlow.reach_dual (cut_isPlane hM hrot Pa hk).dual _ u y
  have hsrc : Klein.srcW (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct) ≤ ((w + 1 : ℕ) : ℤ) := by
    unfold Klein.srcW; rw [hw, ← mw_cast]; push_cast; omega
  have hreach := fun y => reach_iff_lt (N := mN Pa) (S := cutPiece M Pa.darts)
    (kl := mkl hM hrot h Pa hk ℓ hnn Ct) (ℓD := mℓD hM hrot h Pa hk ℓ hnn Ct) (H := w + 1)
    (fun d _ => (mkl_pos hM hrot h Pa hk hnn Ct d).le)
    (fun d => (mℓD_pos hM hrot h Pa hk hnn Ct d).le)
    (fun d hd => by unfold mℓD mLD; simp only [hd, ↓reduceIte])
    (fun d hd => by unfold mℓD mLD; simp only [hd, ↓reduceIte]; split_ifs <;> push_cast <;> omega)
    hsrc hall ((mN Pa).tail (cD0 Pa hk)) y
  have hBdef2 : dB w (mnD Pa en m) k t = w + 40 * mnD Pa en m + 2 * k + 2 * t + t * t + 20 := rfl
  refine ⟨ccut_sameReach hM hrot Pa hk ℓ _ _, ?_, MSSP.abs_treeW_le Ct, (card_cutD h).symm,
    ?_, ?_, ?_, ?_, fun i => ?_, ?_, ?_, ?_, ?_, ?_, ?_, hC.hoff, hC.c0root, ?_, mkC0_wb (by omega),
    fun d => mkC0_wt d, fun d => mkC0_ph d, mkC0_tl, mkC0_th, mkC0_h0,
    fun j hj => mkC0_mk hj, mkC0_rr, mkC0_rm, ?_⟩
  · have := MSSP.treeW_isoW Ct; rwa [hB.ctr] at this
  · rw [hkk]; omega
  · omega
  · rw [hkk, hkr]; simp only [Klein.aOUT]; omega
  · rw [hkk, hkr]; simp only [Klein.aRBM]; omega
  · rw [hPin i]; split_ifs
    · exact min_le_right _ _
    · exact Nat.zero_le _
  · exact StEnc.smLayoutC (cQ h Pa hk) (gv := fun x => (τv x : ℕ)) (gf := fun y => (τf y : ℕ))
      (fun x y e => τv.injective (Fin.ext e)) (fun x y e => τf.injective (Fin.ext e))
      (fun x => by have := (τv x).2; omega) (fun y => by have := (τf y).2; omega) le_rfl
  · exact KInMS.kInput hK5 (StEnc.ιE_lt (cQ h Pa hk)) Pin
      (fun i hi => hPc i (by omega))
  · rw [hkk]
    refine kBnd_of (mem := memc) (β := aIM m p) (fun i hi => ?_) Pin
      (fun i hi => hPc i (by simp only [Klein.iGB] at hi; omega))
    have hg := hB.g i hi
    simp only [hmemc, Klein.iGB]
    rw [show aIM m p + (8 * nD + (4 * nD + 1)) + i = aIM m p + 12 * nD + 1 + i by ring,
      hm5 _ (by omega) (by omega), hg]
    have := (mσ h Pa hk (cutG Pa.rev_mem_darts' (fixT0 Pa hk) i)).2
    exact min_of_le (by omega)
  · rw [hkk]
    exact KOut.clip (hC.kout Pf fun i hi => by
      rw [hPf' i]; simp only [Klein.iOL] at hi
      simp only [show i < dLen nD k t by omega, ↓reduceIte]
      exact hm5 _ (by omega) (by omega)) hcl (by omega)
  · rw [hkk]
    refine kTgt_of (mem := memc) (β := aIM m p) (fun i hi hroot => ?_) (fun i hi => ?_)
      (fun i hi => ?_) Pin (fun i hi => hPc i (by rw [hXT] at hi; omega))
    · obtain ⟨j, hj, e⟩ := hroot
      exact (ccut hM hrot Pa hk ℓ fun e _ => hnn e).root_ne j (by rw [hkk]; exact hj) _ e
    · rw [hXT]; simp only [hmemc]
      rw [show aIM m p + (37 * nD + k + 11) + i = aIM m p + 37 * nD + k + 11 + i by ring,
        (hxt i hi).1, hxtv i hi]
      have := (τv (mX Pa i)).2; exact min_of_le (by omega)
    · rw [hXT]; simp only [hmemc]
      change min (mem5 _) Wb = if MSSP.Reach (MSSP.pieceGraph (mN Pa) (cutPiece M Pa.darts)
        (mkl hM hrot h Pa hk ℓ hnn Ct)) ((mN Pa).tail (cD0 Pa hk)) (mX Pa i) then 1 else 0
      rw [show aIM m p + (37 * nD + k + 11) + t + i = aIM m p + 37 * nD + k + 11 + t + i by ring,
        (hxt i hi).2, hxtv i hi, hC.d0 (mX Pa i)]
      have hr := hreach (mX Pa i)
      by_cases hc : MSSP.Reach (MSSP.pieceGraph (mN Pa) (cutPiece M Pa.darts)
          (mkl hM hrot h Pa hk ℓ hnn Ct)) ((mN Pa).tail (cD0 Pa hk)) (mX Pa i)
      · have := hr.1 hc
        simp only [this, ↓reduceIte, hc]; exact min_of_le (by omega)
      · have : ¬ (MSSP.dist (MSSP.pieceGraph (mN Pa) univ (mℓD hM hrot h Pa hk ℓ hnn Ct))
            ((mN Pa).tail (cD0 Pa hk)) (mX Pa i)).toNat < w + 1 := fun h' => hc (hr.2 h')
        simp only [this, ↓reduceIte, hc]; exact min_of_le (by omega)
  · rw [hkk]
    have hOT := (hC.kinit mem5 (fun a h1 h2 => hm5 a (by omega) h2) Pf (fun j hj => by
      rw [hPf' j]; simp only [lt_of_lt_of_le hj hlenI, ↓reduceIte])).oT
    have hOC := (hC.kinit mem5 (fun a h1 h2 => hm5 a (by omega) h2) Pf (fun j hj => by
      rw [hPf' j]; simp only [lt_of_lt_of_le hj hlenI, ↓reduceIte])).oC
    have l1 := hOT.ylen
    have l3 := hOC.ylen
    rw [eV] at l1
    rw [show Fintype.card (CutF M Pa.darts) = nV from eF] at l3
    refine KInit.clip (hC.kinit mem5 (fun a h1 h2 => hm5 a (by omega) h2) Pf (fun j hj => by
      rw [hPf' j]; simp only [lt_of_lt_of_le hj hlenI, ↓reduceIte])) hcl (by omega)
      (fun x => by have := (τv x).2; omega) (fun y => by have := (τf y).2; omega)
      (by simp; omega) (by omega) (by simp; omega) (by omega)
  · have hst : Klein.tripSrc (ccut hM hrot Pa hk ℓ fun e _ => hnn e).map
        (ccut hM hrot Pa hk ℓ fun e _ => hnn e).k (ccut hM hrot Pa hk ℓ fun e _ => hnn e).g 0 =
        (cutMap Pa.rev_mem_darts').dual.face (cD0 Pa hk) := by
      unfold Klein.tripSrc; rw [Nat.zero_mod]; rfl
    have hdt : Klein.tripDst (ccut hM hrot Pa hk ℓ fun e _ => hnn e).map
        (ccut hM hrot Pa hk ℓ fun e _ => hnn e).k (ccut hM hrot Pa hk ℓ fun e _ => hnn e).g 0 =
        (cutMap Pa.rev_mem_darts').dual.face ((cutMap Pa.rev_mem_darts').dual.rev (cD0 Pa hk)) := by
      unfold Klein.tripDst; rw [Nat.zero_add, hkk]; exact (ring_head hM hrot Pa hk).symm
    rw [hst, hdt, Nat.zero_mod]
    exact hC.comp
  · have := kleinHI_eq (V := CutV M Pa.darts) (F := CutF M Pa.darts)
      (S := cutPiece M Pa.darts) (ℓ := mkl hM hrot h Pa hk ℓ hnn Ct)
      (ccut hM hrot Pa hk ℓ fun e _ => hnn e).k
    refine le_of_eq (this.trans ?_)
    rw [eV, eF, hkk]

end MsEnc

end BKMNW

end PlanarFlow
