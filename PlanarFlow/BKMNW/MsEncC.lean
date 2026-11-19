module

public import PlanarFlow.BKMNW.MsEncB

/-!
# The composed MSSP encoder, part C: Dijkstra's runs, Klein's initial trees, the out-lists

* sizes: `m_le_nEnT` (`m ≤ nE + nT`), **`cV_le_nD`**, **`cF_le_nD`** (`#CutV ≤ nD`,
  `#CutF ≤ nD + 1`);
* the ring of the cut: `ring_head` (`head (g 0) = tail (g (1 mod k))`), `cD0_not_mem`;
* **`reach_iff_lt`**: in the piece, a vertex is reached from `u` iff its distance with all the
  darts and Dijkstra's lengths `mLD` is below `H` (natural words);
* **`msC1_run`** (`msC1` and `ms_tree`): the two Dijkstra runs and Klein's initial tree `T₀`
  (`Compat`), **`StC`**, **`msC_exec`** (`msC1 ; msC2`).
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

/-! ### Sizes -/

/-- Every dart is off the path or leaves it. -/
lemma m_le_nEnT {en : ℕ → D} {m : ℕ} (Pa : SPath M) :
    m ≤ nEc Pa.darts en m + nTc M Pa.darts en m := by
  unfold nEc nTc cE cT
  have h1 : (range m).filter (fun j => en j ∉ Pa.darts ∨ M.tail (en j) ∈ cutS M Pa.darts) =
      range m := by
    refine Finset.filter_true_of_mem fun j _ => ?_
    by_cases hj : en j ∈ Pa.darts
    · exact Or.inr (tail_mem_cutS hj)
    · exact Or.inl hj
  have h2 := Finset.card_union_le ((range m).filter fun j => en j ∉ Pa.darts)
    ((range m).filter fun j => M.tail (en j) ∈ cutS M Pa.darts)
  rw [← Finset.filter_or, h1, card_range] at h2
  exact h2

lemma card_cutT_eq {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (Pa : SPath M) :
    Fintype.card (CutT M Pa.darts) = nTc M Pa.darts en m := by
  rw [Fintype.card_subtype, card_filter_en h]; rfl

/-- **`#CutV ≤ nD`.** -/
lemma cV_le_nD {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (Pa : SPath M) :
    Fintype.card (CutV M Pa.darts) ≤ mnD Pa en m := by
  have hF : Fintype.card F ≤ m := by
    rw [← StEnc.card_eq h]
    exact Fintype.card_le_of_surjective M.face fun f => h.fsurj f
  have := m_le_nEnT (en := en) (m := m) Pa
  have hT := card_cutT_eq h Pa
  have eD : mnD Pa en m = nEc Pa.darts en m + 4 * nTc M Pa.darts en m := rfl
  simp only [CutV, Fintype.card_sum]
  omega

/-- **`#CutF ≤ nD + 1`.** -/
lemma cF_le_nD (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) : Fintype.card (CutF M Pa.darts) ≤ mnD Pa en m + 1 := by
  have h' := enumOK_dual_of hM hrot h (Pa.d 0)
  have hV : Fintype.card V ≤ m := by
    rw [← StEnc.card_eq h]
    exact Fintype.card_le_of_surjective M.tail fun v => h'.fsurj v
  have hS : Fintype.card {v : V // v ∉ cutS M Pa.darts} ≤ m :=
    (Fintype.card_subtype_le _).trans hV
  have := m_le_nEnT (en := en) (m := m) Pa
  have hT := card_cutT_eq h Pa
  have eD : mnD Pa en m = nEc Pa.darts en m + 4 * nTc M Pa.darts en m := rfl
  simp only [CutF, Fintype.card_sum, Fintype.card_unit]
  omega

/-! ### The ring of the cut -/

/-- The boundary walk of the ring is a face cycle of the cut. -/
lemma mN_face (hM : M.IsPlane) (hrot : M.RotTrans) (Pa : SPath M) (hk : 0 < Pa.k) :
    MSSP.FaceCycle (mN Pa) (fixPer M Pa) (cutG Pa.rev_mem_darts' (fixT0 Pa hk)) := by
  have := (ccut hM hrot Pa hk (fun _ => 0) fun _ _ => le_rfl).hyp.face
  rwa [ccut_k] at this

lemma ring_head (hM : M.IsPlane) (hrot : M.RotTrans) (Pa : SPath M) (hk : 0 < Pa.k) :
    (mN Pa).head (cD0 Pa hk) =
      (mN Pa).tail (cutG Pa.rev_mem_darts' (fixT0 Pa hk) (1 % fixPer M Pa)) := by
  have hf := mN_face hM hrot Pa hk
  have h1 := hf.next 0 (fixPer_pos Pa)
  rw [Nat.zero_add] at h1
  rw [← h1, (mN Pa).tail_next]; rfl

lemma ring_ne (hM : M.IsPlane) (hrot : M.RotTrans) (Pa : SPath M) (hk : 0 < Pa.k) :
    (mN Pa).tail (cutG Pa.rev_mem_darts' (fixT0 Pa hk) (1 % fixPer M Pa)) ≠
      (mN Pa).tail (cD0 Pa hk) := by
  have hf := mN_face hM hrot Pa hk
  have h2 := hf.two_le
  intro e
  have := hf.inj (1 % fixPer M Pa) (Nat.mod_lt _ (by omega)) 0 (by omega) e
  rw [Nat.mod_eq_of_lt (by omega)] at this
  omega

lemma cD0_not_mem (Pa : SPath M) (hk : 0 < Pa.k) : cD0 Pa hk ∉ cutPiece M Pa.darts := by
  simp [cD0, cutG, mem_cutPiece, inPiece]

lemma ring_noIn (hM : M.IsPlane) (hrot : M.RotTrans) (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ}
    (hnn : ∀ e, e ∉ Pa.darts → 0 ≤ ℓ e) {d : CutD M Pa.darts} (hd : d ∈ cutPiece M Pa.darts) :
    (mN Pa).head d ≠ (mN Pa).tail (cutG Pa.rev_mem_darts' (fixT0 Pa hk) (1 % fixPer M Pa)) := by
  have := (ccut hM hrot Pa hk ℓ hnn).hyp.noIn d hd
  have h0 := fixPer_pos Pa
  intro e
  refine this ⟨1 % fixPer M Pa, ?_, ?_⟩
  · rw [ccut_k]; exact Nat.mod_lt _ h0
  · exact e.symm

/-! ### Reach in the piece from Dijkstra's distances -/

/-- **A vertex is reached in the piece iff its distance with all the darts is below `H`.** -/
lemma reach_iff_lt {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V']
    [DecidableEq V'] [Fintype F'] [DecidableEq F'] {N : CombMap D' V' F'} {S : Finset D'}
    {kl ℓD : D' → ℤ} {H : ℕ} (hkl : ∀ d ∈ S, 0 ≤ kl d) (hpos : ∀ d, 0 ≤ ℓD d)
    (hS : ∀ d ∈ S, ℓD d = kl d) (hH : ∀ d ∉ S, (H : ℤ) ≤ ℓD d)
    (hsrc : Klein.srcW S kl ≤ H) (hall : ∀ u y, MSSP.Reach (MSSP.pieceGraph N univ ℓD) u y)
    (u y : V') :
    MSSP.Reach (MSSP.pieceGraph N S kl) u y ↔
      (MSSP.dist (MSSP.pieceGraph N univ ℓD) u y).toNat < H := by
  have hnnF : ∀ a, 0 ≤ (MSSP.pieceGraph N univ ℓD).len a := fun a => hpos a.1
  constructor
  · intro hr
    have hlt := Klein.dist_lt_srcW hkl hr
    have e := dist_eq_of_reach (H := (H : ℤ)) hpos hS hH hr (by omega)
    have h0 := MSSP.dist_nonneg hnnF (hall u y)
    omega
  · intro hlt
    have h0 := MSSP.dist_nonneg hnnF (hall u y)
    exact (reach_of_dist_lt (H := (H : ℤ)) hpos hS hH (hall u y) (by omega)).1

/-! ### Frames -/

/-- Klein's words with the piece only depend on `[β, β + 8 nD + E)` (`ιe < E`). -/
lemma KInMS.frame {D' X Y : Type*} [Fintype D'] [DecidableEq D'] [Fintype X] [DecidableEq X]
    {Q : CombMap D' X Y} {S : Finset D'} {ℓ : D' → ℤ} {nD : ℕ} {σ : D' ≃ Fin nD} {ιv : X → ℕ}
    {ιg : D' → ℕ} {ιf : Y → ℕ} {ιe : D' → ℕ} {mem mem' : ℕ → ℕ} {β E : ℕ}
    (h : KInMS Q S ℓ σ ιv ιg ιf ιe mem β) (hE : ∀ d, ιe d < E)
    (hm : ∀ a, β ≤ a → a < β + 8 * nD + E → mem' a = mem a) :
    KInMS Q S ℓ σ ιv ιg ιf ιe mem' β := by
  have e : ∀ (o : ℕ) (d : D'), o + nD ≤ 8 * nD → mem' (β + o + σ d) = mem (β + o + σ d) :=
    fun o d ho => by have := (σ d).2; exact hm _ (by omega) (by omega)
  refine ⟨fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_,
    fun d => ?_, fun d hd => ?_, fun d => ?_⟩
  · rw [e _ d (by simp [Klein.iRV]; omega)]; exact h.rv d
  · rw [e _ d (by simp [Klein.iNF]; omega)]; exact h.nf d
  · rw [e _ d (by simp [Klein.iNE]; omega)]; exact h.ne d
  · rw [e _ d (by simp [Klein.iNG]; omega)]; exact h.ng d
  · rw [e _ d (by simp [Klein.iNT]; omega)]; exact h.nt d
  · rw [e _ d (by simp [Klein.iNH]; omega)]; exact h.nh d
  · rw [e _ d (by simp [Klein.iIS]; omega)]; exact h.is d
  · rw [e _ d (by simp [Klein.iLN]; omega)]; exact h.ln d hd
  · have := hE d
    have e' : mem' (β + Klein.iED nD + ιe d) = mem (β + Klein.iED nD + ιe d) :=
      hm _ (by omega) (by simp [Klein.iED]; omega)
    rw [e']; exact h.ed d

/-- **Stages A and B's facts survive later stages** that keep their registers and the memory
`[p, p + 16 m)`, the image words `[IM, IM + 12 nD + 1 + k)`, `GG` and `LD`. -/
lemma StB.congr {hM : M.IsPlane} {hrot : M.RotTrans} {en : ℕ → D} {m : ℕ} {h : EnumOK M en m}
    {Pa : SPath M} {hk : 0 < Pa.k} {ℓ : D → ℤ} {hnn : ∀ e, 0 ≤ ℓ e} {p q : ℕ} {c₀ c e : Config}
    {nF nV : ℕ} {τv : CutV M Pa.darts ≃ Fin nF} {τf : CutF M Pa.darts ≃ Fin nV}
    {Ct : STFlow.DTree (mN Pa)} (hB : StB hM hrot h Pa hk ℓ hnn p q c₀ c τv τf Ct)
    (hr : ∀ r, (8000 ≤ r ∧ (r < 8200 ∨ 8220 ≤ r) ∧ (r < 8264 ∨ 8268 < r)) ∨ r = 7950 ∨
      r = 7957 ∨ r = 7959 ∨ r = 7342 ∨ r = 7335 ∨ r = 7328 → e.nreg r = c.nreg r)
    (hm : ∀ a, (a < p + 16 * m ∨ (aIM m p ≤ a ∧ a < aIM m p + 12 * mnD Pa en m + 1 + fixPer M Pa) ∨
      (aGG m p ≤ a ∧ a < aGG m p + 2) ∨ (aLD m p ≤ a ∧ a < aLD m p + mnD Pa en m) ∨
      p + 860 * m + 100 + 2 * q ≤ a) → e.nmem a = c.nmem a)
    (hrr : e.rreg = c.rreg) (hrm : e.rmem = c.rmem) (ho : e.output = c.output) :
    StB hM hrot h Pa hk ℓ hnn p q c₀ e τv τf Ct := by
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  have eD : mnD Pa en m = nEc Pa.darts en m + 4 * nTc M Pa.darts en m := rfl
  have hper := fixPer_le h Pa
  have hcl := fixCornerL_le h Pa
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun s hs => ?_,
    fun i hi => ?_, fun r hr' => ?_, fun i hi hf => ?_, fun i hi => ?_, ?_, fun i hi => ?_, ?_,
    ?_, fun d => ?_, hB.ctr, fun a ha => ?_, fun r hr' => ?_, hrr.trans hB.rr, hrm.trans hB.rm,
    ho.trans hB.out⟩
  · rw [hr _ (Or.inl ⟨by omega, by omega, by omega⟩)]; exact hB.lay j hj
  · rw [hr _ (Or.inl ⟨by omega, by omega, by omega⟩)]; exact hB.per
  · rw [hr _ (Or.inl ⟨by omega, by omega, by omega⟩)]; exact hB.ncl
  · rw [hr _ (Or.inl ⟨by omega, by omega, by omega⟩)]; exact hB.r28
  · rw [hr _ (by omega)]; exact hB.r50
  · rw [hr _ (by omega)]; exact hB.r57
  · rw [hr _ (by omega)]; exact hB.r59
  · rw [hr _ (Or.inl ⟨by omega, by omega, by omega⟩)]; exact hB.r97
  · rw [hr _ (Or.inl ⟨by omega, by omega, by omega⟩)]; exact hB.r98
  · rw [hr _ (Or.inl ⟨by omega, by omega, by omega⟩)]; exact hB.r99
  · rw [hr _ (by omega)]; exact hB.rw
  · rw [hr _ (by omega)]; exact hB.rH
  · rw [hr _ (by omega)]; exact hB.rN1
  · rw [hm _ (Or.inl (by omega))]; exact hB.tr s hs
  · rw [hm _ (Or.inl (by omega))]; exact hB.fl i hi
  · rw [hm _ (Or.inl (by omega)), hm _ (Or.inl (by omega))]; exact hB.cs r hr'
  · obtain ⟨r, hr', e1, e2⟩ := hB.cn i hi hf
    have hl := NsStep.labI_lt (M := M) h hi
    exact ⟨r, hr', by rw [hm _ (Or.inl (by omega))]; exact e1, e2⟩
  · rw [hm _ (Or.inl (by omega)), hm _ (Or.inl (by omega))]; exact hB.rk i hi
  · exact KInMS.frame hB.kin (E := 4 * mnD Pa en m + 1) (StEnc.ιE_lt (cQ h Pa hk))
      (fun a h1 h2 => hm a (Or.inr (Or.inl ⟨h1, by omega⟩)))
  · rw [hm _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hB.g i hi
  · rw [hm _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]; exact hB.gg0
  · rw [hm _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]; exact hB.gg1
  · have := (mσ h Pa hk d).2
    rw [hm _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))]; exact hB.ld d
  · rcases ha with ha | ha
    · rw [hm _ (Or.inl (by omega))]; exact hB.mem a (Or.inl ha)
    · rw [hm _ (Or.inr (Or.inr (Or.inr (Or.inr ha))))]; exact hB.mem a (Or.inr ha)
  · simp only [EScr] at hr'
    rw [hr _ (Or.inl ⟨by omega, by omega, by omega⟩)]; exact hB.reg r (by simp only [EScr]; omega)

lemma lg_mono {a b : ℕ} (h : a ≤ b) : Heap.lg a ≤ Heap.lg b := by
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · subst h0; unfold Heap.lg; simp
  · rw [Heap.lg_eq_log (by omega), Heap.lg_eq_log (by omega)]
    have := Nat.log_mono_right (b := 2) h
    omega

lemma stdCost_mono {n n' nD nD' : ℕ} (h1 : n ≤ n') (h2 : nD ≤ nD') :
    stdCost n nD ≤ stdCost n' nD' := by
  unfold stdCost osCost
  have hl := lg_mono (show 2 * n ≤ 2 * n' by omega)
  have a1 : n * (23 * Heap.lg (2 * n) + 21) ≤ n' * (23 * Heap.lg (2 * n') + 21) :=
    Nat.mul_le_mul h1 (by omega)
  have a2 : (13 * Heap.lg (2 * n) + 20) * nD ≤ (13 * Heap.lg (2 * n') + 20) * nD' :=
    Nat.mul_le_mul (by omega) h2
  omega

/-! ### Stage C1: Dijkstra's runs and Klein's initial tree -/

/-- The sum `w` of the isolating lengths on the piece. -/
noncomputable abbrev mw (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) (ℓ : D → ℤ) (hnn : ∀ e, 0 ≤ ℓ e)
    (Ct : STFlow.DTree (mN Pa)) : ℕ :=
  (Klein.tripW (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct)).toNat

/-- Dijkstra's lengths of the call. -/
noncomputable abbrev mℓD (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) (ℓ : D → ℤ) (hnn : ∀ e, 0 ≤ ℓ e)
    (Ct : STFlow.DTree (mN Pa)) : CutD M Pa.darts → ℤ :=
  mLD (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct) (cD0 Pa hk)
    ((mw hM hrot h Pa hk ℓ hnn Ct + 1 : ℕ) : ℤ)

lemma mkl_pos (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e)
    (Ct : STFlow.DTree (mN Pa)) (d : CutD M Pa.darts) : 0 < mkl hM hrot h Pa hk ℓ hnn Ct d := by
  have hn1 : 1 ≤ Fintype.card (CutV M Pa.darts) :=
    Fintype.card_pos_iff.2 ⟨Sum.inl (M.face (Pa.d 0))⟩
  have hι : ∀ d : CutD M Pa.darts, ((mσ h Pa hk d : ℕ)) < Fintype.card (CutD M Pa.darts) :=
    fun d => by rw [card_cutD h]; exact (mσ h Pa hk d).2
  have hcl0 : 0 ≤ cutLen M Pa.darts ℓ d := by
    rcases d with e | t <;> simp only [cutLen]
    · exact hnn e.1
    · exact le_rfl
  exact (MSSP.isoLen_lt (D := CutD M Pa.darts) (w := MSSP.treeW Ct) (ℓ := cutLen M Pa.darts ℓ)
    (ι := fun d => (mσ h Pa hk d : ℕ)) (MSSP.abs_treeW_le Ct) hι hn1 (d := d) hcl0).1

lemma mw_cast (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e)
    (Ct : STFlow.DTree (mN Pa)) :
    ((mw hM hrot h Pa hk ℓ hnn Ct : ℕ) : ℤ) =
      ∑ d ∈ cutPiece M Pa.darts, mkl hM hrot h Pa hk ℓ hnn Ct d := by
  unfold mw
  rw [Int.toNat_of_nonneg Klein.tripW_nonneg, tripW_eq fun d _ => (mkl_pos hM hrot h Pa hk hnn Ct d).le]

lemma mkl_le_mw (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e)
    (Ct : STFlow.DTree (mN Pa)) {d : CutD M Pa.darts} (hd : d ∈ cutPiece M Pa.darts) :
    mkl hM hrot h Pa hk ℓ hnn Ct d ≤ (mw hM hrot h Pa hk ℓ hnn Ct : ℤ) := by
  rw [mw_cast]
  exact Finset.single_le_sum (fun d _ => (mkl_pos hM hrot h Pa hk hnn Ct d).le) hd

lemma mℓD_pos (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e)
    (Ct : STFlow.DTree (mN Pa)) (d : CutD M Pa.darts) : 0 < mℓD hM hrot h Pa hk ℓ hnn Ct d := by
  unfold mℓD mLD
  have := mkl_pos hM hrot h Pa hk hnn Ct d
  split_ifs <;> push_cast <;> omega

lemma mℓD_le (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e)
    (Ct : STFlow.DTree (mN Pa)) (d : CutD M Pa.darts) :
    (mℓD hM hrot h Pa hk ℓ hnn Ct d).toNat ≤
      (mw hM hrot h Pa hk ℓ hnn Ct + 1) + (mw hM hrot h Pa hk ℓ hnn Ct + 1) := by
  unfold mℓD mLD
  split_ifs with h1 h2
  · have := mkl_le_mw hM hrot h Pa hk hnn Ct h1; omega
  · rw [Int.toNat_natCast]; omega
  · rw [show (2 : ℤ) * ((mw hM hrot h Pa hk ℓ hnn Ct + 1 : ℕ) : ℤ) =
      ((2 * (mw hM hrot h Pa hk ℓ hnn Ct + 1) : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
    omega

set_option maxHeartbeats 8000000 in
/-- **Stage C1 and Klein's initial tree**: the two Dijkstra runs (`msC1_exec'`) from the tails of
the first two ring darts, and the tree `T₀` of `ms_tree` (Klein's `Compat`). -/
theorem msC1_run (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e)
    {p q nF nV : ℕ} (τv : CutV M Pa.darts ≃ Fin nF) (τf : CutF M Pa.darts ≃ Fin nV)
    (Ct : STFlow.DTree (mN Pa)) (c₀ c : Config) (hc : WordsBounded W c)
    (hB : StB hM hrot h Pa hk ℓ hnn p q c₀ c τv τf Ct)
    (hWI : nF * ((mw hM hrot h Pa hk ℓ hnn Ct + 1) + (mw hM hrot h Pa hk ℓ hnn Ct + 1)) + 1 +
      ((mw hM hrot h Pa hk ℓ hnn Ct + 1) + (mw hM hrot h Pa hk ℓ hnn Ct + 1)) ≤ W)
    (hW : p + 860 * m + 100 + 2 * q ≤ W) :
    ∃ e t, Exec P W msC1 c e t ∧ t ≤ 10 + 2 * (15 + stdCost (4 * (5 * m) + 1) (5 * m)) ∧
      StB hM hrot h Pa hk ℓ hnn p q c₀ e τv τf Ct ∧
      (∀ x, e.nmem (aA0 m p + 21 * mnD Pa en m + 6 + (1 + (τv x : ℕ))) =
        (MSSP.dist (MSSP.pieceGraph (mN Pa) univ (mℓD hM hrot h Pa hk ℓ hnn Ct))
          ((mN Pa).tail (cD0 Pa hk)) x).toNat) ∧
      (∀ x, e.nmem (aA1 m p + 21 * mnD Pa en m + 6 + (1 + (τv x : ℕ))) =
        (MSSP.dist (MSSP.pieceGraph (mN Pa) univ (mℓD hM hrot h Pa hk ℓ hnn Ct))
          ((mN Pa).tail (cutG Pa.rev_mem_darts' (fixT0 Pa hk) (1 % fixPer M Pa))) x).toNat) ∧
      (∃ T₀ : STFlow.DTree (cutMap Pa.rev_mem_darts').dual,
        T₀.root = (cutMap Pa.rev_mem_darts').dual.face (cD0 Pa hk) ∧
        (∀ x, x ≠ T₀.root → e.nmem (aA0 m p + 37 * mnD Pa en m + 10 + 1 + (τv x : ℕ)) =
          mσ h Pa hk (T₀.par x)) ∧
        Klein.Compat (STFlow.toDD T₀) ((cutMap Pa.rev_mem_darts').dual.face (cD0 Pa hk))
          ((cutMap Pa.rev_mem_darts').dual.face ((cutMap Pa.rev_mem_darts').dual.rev (cD0 Pa hk)))
          (cD0 Pa hk) (Klein.tpar (MSSP.pieceGraph (mN Pa) (cutPiece M Pa.darts)
            (mkl hM hrot h Pa hk ℓ hnn Ct)) ((cutMap Pa.rev_mem_darts').dual.face (cD0 Pa hk)))) ∧
      (∀ a, (a < aA0 m p ∨ aA1 m p + 10 * (4 * mnD Pa en m + 1) + 1 + mnD Pa en m ≤ a) →
        e.nmem a = c.nmem a) ∧
      (∀ r, (r < 1500 ∨ 2548 ≤ r) → (r < 7860 ∨ 7877 ≤ r) → (r < 7360 ∨ 7362 < r) →
        (r < 8264 ∨ 8268 < r) → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  have eD : mnD Pa en m = nEc Pa.darts en m + 4 * nTc M Pa.darts en m := rfl
  have lay := hB.lay
  have hper := fixPer_le h Pa
  have h0 := fixPer_pos Pa
  have hcV : nF ≤ mnD Pa en m := by
    have := cV_le_nD h Pa; rwa [Fintype.card_congr τv, Fintype.card_fin] at this
  have hQ : (cutMap Pa.rev_mem_darts').dual.IsPlane := (cut_isPlane hM hrot Pa hk).dual
  have hall : ∀ u x, MSSP.Reach (MSSP.pieceGraph (mN Pa) univ (mℓD hM hrot h Pa hk ℓ hnn Ct)) u x :=
    fun u x => STFlow.reach_dual hQ _ u x
  have h1k : 1 % fixPer M Pa < fixPer M Pa := Nat.mod_lt _ h0
  have hg1 := hB.g _ h1k
  obtain ⟨e, t, ex, ht, d0, p0, d1, M₁, R₁, rr₁, rm₁, o₁⟩ :=
    msC1_exec' (P := P) (N := mN Pa) (mσ h Pa hk) τv (ℓD := mℓD hM hrot h Pa hk ℓ hnn Ct)
      (IM := aIM m p) (LD := aLD m p) (A0 := aA0 m p) (A1 := aA1 m p)
      (H := mw hM hrot h Pa hk ℓ hnn Ct + 1) (GG := aGG m p) (k := fixPer M Pa)
      (u₀ := (mN Pa).tail (cD0 Pa hk))
      (u₁ := (mN Pa).tail (cutG Pa.rev_mem_darts' (fixT0 Pa hk) (1 % fixPer M Pa))) c hc
      hB.kin.nt hB.kin.nh (mℓD_pos hM hrot h Pa hk hnn Ct) hB.ld (mℓD_le hM hrot h Pa hk hnn Ct)
      hall (by rw [hB.gg0]; exact hB.kin.nt _) (by rw [hg1]; exact hB.kin.nt _) hB.r50
      (lay 2 (by omega)) (lay 8 (by omega)) (lay 10 (by omega)) (lay 11 (by omega)) hB.rH hB.r57
      (lay 4 (by omega)) hB.per h0 hcV
      (by rw [hB.gg0]; exact (mσ h Pa hk _).2) (by rw [hg1]; exact (mσ h Pa hk _).2)
      (by unfold aIM aA0; omega) (by unfold aLD aA0; omega) (by unfold aGG aA0; omega)
      (by unfold aA0 aA1; omega) (by unfold aA1; omega) hWI (by unfold aIM; omega)
  have hU : MSSP.UniqTight (MSSP.pieceGraph (mN Pa) (cutPiece M Pa.darts)
      (mkl hM hrot h Pa hk ℓ hnn Ct)) :=
    ((ccut hM hrot Pa hk ℓ fun e _ => hnn e).hyp.hypIso (MSSP.treeW_isoW Ct)
      (MSSP.abs_treeW_le Ct) le_rfl (ι := fun d => (mσ h Pa hk d : ℕ))
      (fun a b e => (mσ h Pa hk).injective (Fin.ext e))
      (fun d => by rw [card_cutD h]; exact (mσ h Pa hk d).2)).uniq
  have hsrc : Klein.srcW (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct) =
      ((mw hM hrot h Pa hk ℓ hnn Ct + 1 : ℕ) : ℤ) := by
    unfold Klein.srcW; rw [← mw_cast]; push_cast; ring
  have hnot := cD0_not_mem Pa hk
  obtain ⟨T₀, hroot, hpar, hcomp⟩ :=
    ms_tree (Q := (cutMap Pa.rev_mem_darts').dual) (S := cutPiece M Pa.darts)
      (ℓ := mkl hM hrot h Pa hk ℓ hnn Ct) (ℓD := mℓD hM hrot h Pa hk ℓ hnn Ct)
      (H := ((mw hM hrot h Pa hk ℓ hnn Ct + 1 : ℕ) : ℤ)) hQ hU (mℓD_pos hM hrot h Pa hk hnn Ct)
      (fun d hd => by unfold mℓD mLD; simp only [hd, ↓reduceIte])
      (fun d hd => by
        unfold mℓD mLD
        simp only [hd, ↓reduceIte]
        split_ifs <;> omega)
      ((cutMap Pa.rev_mem_darts').dual.face (cD0 Pa hk))
      (fun x hx => (Klein.dist_lt_srcW (fun d _ => (mkl_pos hM hrot h Pa hk hnn Ct d).le) hx).trans_le
        (le_of_eq hsrc))
      (cD0 Pa hk) hnot rfl
      (by
        show (mN Pa).head (cD0 Pa hk) ≠ (mN Pa).tail (cD0 Pa hk)
        rw [ring_head hM hrot Pa hk]; exact ring_ne hM hrot Pa hk)
      (by unfold mℓD mLD; simp only [hnot, ↓reduceIte, ite_true])
      (fun d hd hd0 => by unfold mℓD mLD; simp only [hd, hd0, ↓reduceIte]; exact le_rfl)
      (by omega)
      (fun d hd => by
        show (mN Pa).head d ≠ (mN Pa).head (cD0 Pa hk)
        rw [ring_head hM hrot Pa hk]; exact ring_noIn hM hrot Pa hk (fun e _ => hnn e) hd)
      (mσ h Pa hk) (ιF := fun x => 1 + (τv x : ℕ)) (mem := e.nmem)
      (Pb := aA0 m p + 9 * (4 * mnD Pa en m + 1) + 1 + mnD Pa en m) (fun x hx => p0 x hx)
  refine ⟨e, t, ex, ht.trans ?_, ?_, fun x => ?_, fun x => ?_, ⟨T₀, hroot, fun x hx => ?_, hcomp⟩,
    M₁, R₁, rr₁, rm₁, o₁⟩
  · have := stdCost_mono (show 4 * mnD Pa en m + 1 ≤ 4 * (5 * m) + 1 by omega)
      (show mnD Pa en m ≤ 5 * m by omega)
    omega
  · refine StB.congr hB (fun r hr => R₁ r (by omega) (by omega) (by omega) (by omega))
      (fun a ha => M₁ a (by simp only [aIM, aGG, aLD, aA0, aA1] at ha ⊢; omega)) rr₁ rm₁ o₁
  · rw [show aA0 m p + 21 * mnD Pa en m + 6 + (1 + (τv x : ℕ)) =
      aA0 m p + 5 * (4 * mnD Pa en m + 1) + 1 + mnD Pa en m + (1 + (τv x : ℕ)) by ring]
    exact d0 x
  · rw [show aA1 m p + 21 * mnD Pa en m + 6 + (1 + (τv x : ℕ)) =
      aA1 m p + 5 * (4 * mnD Pa en m + 1) + 1 + mnD Pa en m + (1 + (τv x : ℕ)) by ring]
    exact d1 x
  · rw [show aA0 m p + 37 * mnD Pa en m + 10 + 1 + (τv x : ℕ) =
      aA0 m p + 9 * (4 * mnD Pa en m + 1) + 1 + mnD Pa en m + (1 + (τv x : ℕ)) by ring]
    exact hpar x (by rw [← hroot]; exact hx)

/-! ### Stage C2: `KInit`, `KOut` -/

/-- **What stages A–C2 leave.** -/
structure StC (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) (ℓ : D → ℤ) (hnn : ∀ e, 0 ≤ ℓ e) (p q : ℕ) (c₀ e : Config)
    {nF nV : ℕ} (τv : CutV M Pa.darts ≃ Fin nF) (τf : CutF M Pa.darts ≃ Fin nV)
    (Ct : STFlow.DTree (mN Pa)) (T₀ : STFlow.DTree (cutMap Pa.rev_mem_darts').dual)
    (C₀ : STFlow.DTree (mN Pa)) (ts : List (CutV M Pa.darts)) (cs : List (CutF M Pa.darts)) :
    Prop where
  b : StB hM hrot h Pa hk ℓ hnn p q c₀ e τv τf Ct
  d0 : ∀ x, e.nmem (aA0 m p + 21 * mnD Pa en m + 6 + (1 + (τv x : ℕ))) =
    (MSSP.dist (MSSP.pieceGraph (mN Pa) univ (mℓD hM hrot h Pa hk ℓ hnn Ct))
      ((mN Pa).tail (cD0 Pa hk)) x).toNat
  d1 : ∀ x, e.nmem (aA1 m p + 21 * mnD Pa en m + 6 + (1 + (τv x : ℕ))) =
    (MSSP.dist (MSSP.pieceGraph (mN Pa) univ (mℓD hM hrot h Pa hk ℓ hnn Ct))
      ((mN Pa).tail (cutG Pa.rev_mem_darts' (fixT0 Pa hk) (1 % fixPer M Pa))) x).toNat
  troot : T₀.root = (cutMap Pa.rev_mem_darts').dual.face (cD0 Pa hk)
  comp : Klein.Compat (STFlow.toDD T₀) ((cutMap Pa.rev_mem_darts').dual.face (cD0 Pa hk))
    ((cutMap Pa.rev_mem_darts').dual.face ((cutMap Pa.rev_mem_darts').dual.rev (cD0 Pa hk)))
    (cD0 Pa hk) (Klein.tpar (MSSP.pieceGraph (mN Pa) (cutPiece M Pa.darts)
      (mkl hM hrot h Pa hk ℓ hnn Ct)) ((cutMap Pa.rev_mem_darts').dual.face (cD0 Pa hk)))
  c0root : C₀.root = (cutMap Pa.rev_mem_darts').dual.tail (cD0 Pa hk)
  hoff : ∀ x, x ≠ C₀.root → ¬ (STFlow.toDD T₀).InT (C₀.par x)
  kinit : ∀ mem : ℕ → ℕ, (∀ a, aIM m p + 21 * mnD Pa en m + fixPer M Pa + 3 ≤ a →
      a < aIM m p + 37 * mnD Pa en m + fixPer M Pa + 11 → mem a = e.nmem a) →
    ∀ Pk : Input, (∀ j, j < Klein.iHD (mnD Pa en m) (4 * mnD Pa en m + 1) (fixPer M Pa) + 4 →
      Pk.data.getD j 0 = mem (aIM m p + j)) →
    Klein.KInit (mN Pa) (mσ h Pa hk) (fun x => 1 + (τv x : ℕ))
      (fun v => 2 * mnD Pa en m + 1 + (τf v : ℕ)) (4 * mnD Pa en m + 1) (fixPer M Pa)
      (STFlow.toDD T₀) C₀ ((List.finRange nF).map τv.symm) ts ((List.finRange nV).map τf.symm)
      cs Pk
  kout : ∀ Pk : Input, (∀ i < Klein.iOL (mnD Pa en m) (4 * mnD Pa en m + 1) (fixPer M Pa) +
      mnD Pa en m, Pk.data.getD i 0 = e.nmem (aIM m p + i)) →
    Klein.KOut (mN Pa) (cutPiece M Pa.darts) (mσ h Pa hk) (fun x => 1 + (τv x : ℕ))
      (4 * mnD Pa en m + 1) (fixPer M Pa) Pk

/-- **Stage C.** -/
def msC : Stmt := .seq msC1 msC2

set_option maxHeartbeats 8000000 in
/-- **Stage C on the machine** (`msC1 ; msC2a ; msC2b`): `StB → StC`. The sloppy W-sums of
`msC2a_execW`/`msC2b_execW` are per-entry. -/
theorem msC_exec (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e)
    {p q nF nV : ℕ} (τv : CutV M Pa.darts ≃ Fin nF) (τf : CutF M Pa.darts ≃ Fin nV)
    (Ct : STFlow.DTree (mN Pa)) (c₀ c : Config) (hc : WordsBounded W c)
    (hB : StB hM hrot h Pa hk ℓ hnn p q c₀ c τv τf Ct) (r00 : c₀.nreg 8000 = m)
    (hWI : nF * ((mw hM hrot h Pa hk ℓ hnn Ct + 1) + (mw hM hrot h Pa hk ℓ hnn Ct + 1)) + 1 +
      ((mw hM hrot h Pa hk ℓ hnn Ct + 1) + (mw hM hrot h Pa hk ℓ hnn Ct + 1)) ≤ W)
    (hWW : p + 860 * m + 1000 + 2 * q ≤ W) :
    ∃ e t, ∃ (T₀ : STFlow.DTree (cutMap Pa.rev_mem_darts').dual) (C₀ : STFlow.DTree (mN Pa))
      (ts : List (CutV M Pa.darts)) (cs : List (CutF M Pa.darts)),
      Exec P W msC c e t ∧
      t ≤ (10 + 2 * (15 + stdCost (4 * (5 * m) + 1) (5 * m))) + costC2 (5 * m) (2 * m) (2 * m + 1) ∧
      StC hM hrot h Pa hk ℓ hnn p q c₀ e τv τf Ct T₀ C₀ ts cs := by
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  have eD : mnD Pa en m = nEc Pa.darts en m + 4 * nTc M Pa.darts en m := rfl
  have hper := fixPer_le h Pa
  have h0 := fixPer_pos Pa
  have hcV : nF ≤ mnD Pa en m := by
    have := cV_le_nD h Pa; rwa [Fintype.card_congr τv, Fintype.card_fin] at this
  have hcF : nV ≤ mnD Pa en m + 1 := by
    have := cF_le_nD hM hrot h Pa; rwa [Fintype.card_congr τf, Fintype.card_fin] at this
  have hcV2 : nF ≤ 2 * m := by
    have := card_cutV_le h Pa.darts; rwa [Fintype.card_congr τv, Fintype.card_fin] at this
  have hcF2 : nV ≤ 2 * m + 1 := by
    have := card_cutF_le hM hrot h Pa.darts (Pa.d 0)
    rwa [Fintype.card_congr τf, Fintype.card_fin] at this
  have hnD1 : 1 ≤ mnD Pa en m := by have := (mσ h Pa hk (cD0 Pa hk)).2; omega
  have hQ : (cutMap Pa.rev_mem_darts').dual.IsPlane := (cut_isPlane hM hrot Pa hk).dual
  have : Nonempty (CutD M Pa.darts) := ⟨cD0 Pa hk⟩
  obtain ⟨e₁, t₁, ex₁, ht₁, hB1, d0, d1, ⟨T₀, troot, tpar, comp⟩, M₁, R₁, rr₁, rm₁, o₁⟩ :=
    msC1_run (P := P) hM hrot h Pa hk hnn τv τf Ct c₀ c hc hB hWI (by omega)
  have lay := hB1.lay
  have r00' : e₁.nreg 8000 = m := by
    rw [hB1.reg _ (by simp only [EScr]; omega)]; exact r00
  obtain ⟨e₂, t₂, ex₂, ht₂, ts, C₀, cs, c0root, hoff, hKI, M₂, R₂, rr₂, rm₂, o₂⟩ :=
    msC2a_execW (P := P) (M := (cutMap Pa.rev_mem_darts').dual) hQ (mσ h Pa hk) τv τf (T₀ := T₀)
      (cD0 Pa hk) troot (IM := aIM m p) (A0 := aA0 m p) (Z := aZk m p) (p := p) (m := m)
      (k := fixPer M Pa) (GG := aGG m p) e₁ ex₁.wb_right hB1.r97 hB1.r98 hB1.r99
      (lay 2 (by omega)) hB1.per (lay 10 (by omega)) (lay 12 (by omega)) (lay 0 (by omega)) r00'
      (lay 4 (by omega))
      (fun d => by have := hB1.kin.nt d; simp only [Klein.iNT] at this; exact this)
      (fun d => by have := hB1.kin.nf d; simp only [Klein.iNF] at this; exact this)
      (fun d => by have := hB1.kin.rv d; simp only [Klein.iRV, Nat.add_zero] at this; exact this)
      tpar hB1.gg0 hB1.gg1 (by omega) (by omega) (by unfold aIM; omega)
      (by unfold aIM aGG; omega) (by unfold aGG aA0; omega) (by unfold aA0 aZk; omega)
      (by unfold aZk; have : 1 ≤ m := by { have := ixOf_lt h (Pa.d 0); omega }; omega)
  have m2 : ∀ a, (a < aIM m p + 21 * mnD Pa en m + fixPer M Pa + 3 ∨
      aIM m p + 37 * mnD Pa en m + fixPer M Pa + 13 ≤ a) → a ≠ p + 16 * m →
      a ≠ p + 16 * m + 1 → (a < aA0 m p + 37 * mnD Pa en m + 11 ∨
        aA0 m p + 37 * mnD Pa en m + 11 + nF ≤ a) →
      (a < aZk m p ∨ aZk m p + 8 * nF + 4 * mnD Pa en m + 15 * nV + 3 ≤ a) →
      e₂.nmem a = e₁.nmem a := M₂
  have k2 : ∀ r, (r < 1400 ∨ 1720 ≤ r) → (r < 7360 ∨ 7372 ≤ r) → (r < 7980 ∨ 8000 ≤ r) →
      e₂.nreg r = e₁.nreg r := R₂
  have hσl : ∀ d : CutD M Pa.darts, (mσ h Pa hk d : ℕ) < mnD Pa en m := fun d => (mσ h Pa hk d).2
  obtain ⟨e₃, t₃, ex₃, ht₃, hKO, M₃, R₃, rr₃, rm₃, o₃⟩ :=
    msC2b_execW (P := P) (N := mN Pa) (S := cutPiece M Pa.darts) (mσ h Pa hk)
      (ιv := fun x => 1 + (τv x : ℕ)) (fun x y e => τv.injective (Fin.ext (by simp only at e; omega)))
      (fun x => by have := (τv x).2; omega) (IM := aIM m p) (k := fixPer M Pa) (Ob := aOs m p)
      e₂ ex₂.wb_right (by rw [k2 _ (by omega) (by omega) (by omega)]; exact hB1.r97)
      (by rw [k2 _ (by omega) (by omega) (by omega)]; exact lay 2 (by omega))
      (by rw [k2 _ (by omega) (by omega) (by omega)]; exact hB1.per)
      (by rw [k2 _ (by omega) (by omega) (by omega)]; exact lay 13 (by omega))
      (fun d => by
        have := hσl d
        rw [m2 _ (Or.inl (by simp only [Klein.iNT]; omega)) (by unfold aIM; simp only [Klein.iNT]; omega)
          (by unfold aIM; simp only [Klein.iNT]; omega) (Or.inl (by unfold aIM aA0; simp only [Klein.iNT]; omega))
          (Or.inl (by unfold aIM aZk; simp only [Klein.iNT]; omega))]
        exact hB1.kin.nt d)
      (fun d => by
        have := hσl d
        rw [m2 _ (Or.inl (by simp only [Klein.iIS]; omega)) (by unfold aIM; simp only [Klein.iIS]; omega)
          (by unfold aIM; simp only [Klein.iIS]; omega) (Or.inl (by unfold aIM aA0; simp only [Klein.iIS]; omega))
          (Or.inl (by unfold aIM aZk; simp only [Klein.iIS]; omega))]
        exact hB1.kin.is d)
      (by unfold aIM aOs; omega) (by unfold aOs; omega)
  have m3 : ∀ a, (a < aOs m p ∨ aOs m p + 2 * (4 * mnD Pa en m + 1) + 1 ≤ a) →
      (a < aIM m p + 12 * mnD Pa en m + 1 + fixPer M Pa ∨
        aIM m p + 21 * mnD Pa en m + fixPer M Pa + 3 ≤ a) → e₃.nmem a = e₂.nmem a := M₃
  have k3 : ∀ r, (r < 1500 ∨ 1521 ≤ r) → r ≠ 7370 → r ≠ 7371 → e₃.nreg r = e₂.nreg r := R₃
  refine ⟨e₃, t₁ + (t₂ + t₃), T₀, C₀, ts, cs, ex₁.seq (ex₂.seq ex₃), ?_, ⟨?_, fun x => ?_,
    fun x => ?_, troot, comp, c0root, hoff, fun mem hmem Pk hPk => ?_, hKO⟩⟩
  · unfold costC2 at *
    unfold StEnc.kiCost osCost at *
    omega
  · refine StB.congr hB1 (fun r hr => ?_) (fun a ha => ?_) (by rw [rr₃, rr₂]) (by rw [rm₃, rm₂])
      (by rw [o₃, o₂])
    · rw [k3 r (by omega) (by omega) (by omega), k2 r (by omega) (by omega) (by omega)]
    · rw [m3 a (by unfold aOs aIM aGG aLD at *; omega) (by unfold aOs aIM aGG aLD at *; omega),
        m2 a (by unfold aOs aIM aGG aLD at *; omega) (by unfold aOs aIM aGG aLD at *; omega)
          (by unfold aOs aIM aGG aLD at *; omega)
          (by unfold aA0 aOs aIM aGG aLD at *; omega) (by unfold aZk aOs aIM aGG aLD at *; omega)]
  · have := (τv x).2
    rw [m3 _ (Or.inl (by unfold aOs aA0; omega)) (Or.inr (by unfold aA0 aIM; omega)),
      m2 _ (Or.inr (by unfold aA0 aIM; omega)) (by unfold aA0; omega) (by unfold aA0; omega)
        (Or.inl (by omega)) (Or.inl (by unfold aA0 aZk; omega))]
    exact d0 x
  · have := (τv x).2
    rw [m3 _ (Or.inl (by unfold aOs aA1; omega)) (Or.inr (by unfold aA1 aIM; omega)),
      m2 _ (Or.inr (by unfold aA1 aIM; omega)) (by unfold aA1; omega) (by unfold aA1; omega)
        (Or.inr (by unfold aA0 aA1; omega)) (Or.inl (by unfold aA1 aZk; omega))]
    exact d1 x
  · exact hKI mem (fun a h1 h2 => (hmem a h1 h2).trans
      (m3 a (Or.inl (by unfold aIM aOs at *; omega)) (Or.inr h1))) Pk hPk

end MsEnc

end BKMNW

end PlanarFlow
