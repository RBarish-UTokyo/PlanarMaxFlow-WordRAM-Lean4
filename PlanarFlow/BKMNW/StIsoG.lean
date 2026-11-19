module

public import PlanarFlow.BKMNW.StNat

/-!
# The word-size perturbation of the s-t flow for **any** isolating weight

The perturbation `isoEps M t = isoL + isoW M t` of `STFlow.pstflowW` uses the classically chosen
isolating weight `isoW M t` (`h.choose` of `exists_isIsoW`); a machine computes its own weight
(e.g. the subtree counts of a spanning tree rooted at `t`). Every proof about `isoEps` uses only
`IsIsoW M t (isoW M t)`; here they are restated for **any** `w` with `IsIsoW M t w`
(copies of `IsoEps.lean`, `IsoCover.lean`, `IsoCost.lean`, `IsoExec.lean` with `w` a parameter):

* `isoEpsG w = isoL + w`, `isoEpsG_bounds` (between `1` and `(4 F + 6) #V`);
* `lred_isoEpsG`, `lred_isoWG`, **`lred_isoEpsG_inj`** (the perturbation separates the darts of
  the path);
* `covLenWG`, `covLenWG_eq`, `sum_covLenWG`, **`tight_parWG`** (the parent darts are tight in the
  cut of the cover);
* `covLenWG_nonneg`, `tightLev_isoG`, **`lstepsWG_le`** (at most `m + 1` steps);
* **`pertOK_isoG`**: `PertOK M c (isoEpsG w) s t d₀` (so `STFlow.pcore_exec` applies with the
  machine's weight); `lexR_isoG_le`, **`kH0_isoG_le`** (`kH0 ≤ isoW_bound`, the word size).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW MSSP Klein Function

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

variable (V F) in
/-- **The word-size perturbation of an isolating weight** `w`: `isoL + w`. -/
def isoEpsG (w : D → ℤ) (d : D) : ℤ := isoL V F + w d

lemma card_V_pos_of (M : CombMap D V F) (d : D) : 0 < Fintype.card V :=
  Fintype.card_pos_iff.2 ⟨M.tail d⟩

lemma isoEpsG_bounds (_hM : M.IsPlane) {w : D → ℤ} {t : V} (hw : IsIsoW M t w) (d : D) :
    1 ≤ isoEpsG V F w d ∧ isoEpsG V F w d ≤ (4 * Fintype.card F + 6) * Fintype.card V := by
  have h := (abs_le.1 (hw.2.2 d))
  have hV : (1 : ℤ) ≤ Fintype.card V := by exact_mod_cast (card_V_pos_of M d)
  unfold isoEpsG isoL
  constructor <;> nlinarith

/-! ### The perturbation separates the darts of the path -/

lemma lred_isoEpsG (w : D → ℤ) (T : DTree M) (d : D) :
    lred (isoEpsG V F w) T d = isoL V F * lred (fun _ => 1) T d + lred (w) T d := by
  have e : isoEpsG V F w = (fun d => isoL V F * (fun _ => (1 : ℤ)) d) + w := by
    funext d; simp [isoEpsG]
  rw [e, lred_add]
  congr 1
  simp only [lred, cob, T.psum_smul]; ring


/-- **On a dart of the path, `lred w T` is the number of vertices on its side.** -/
theorem lred_isoWG (hM : M.IsPlane) {w : D → ℤ} {s t : V} (hw : IsIsoW M t w) {T : DTree M} {d : D}
    (h : T.chi s t d = 1) : lred (w) T d = (T.side d).card := by
  obtain ⟨hwa, hdiv, -⟩ := hw
  obtain ⟨ha, hoff, hd⟩ := lred_flow hwa T
  rw [DTree.flow_eq_side hM ha hoff (not_inT_of_chi hM h)]
  have ht := (side_of_chi hM h).2
  have h1 : ∀ v ∈ T.side d, M.div (lred (w) T) v = 1 := fun v hv => by
    have hvt : v ≠ t := fun e => ht (e ▸ hv)
    rw [hd, hdiv]; simp [hvt]
  rw [sum_congr rfl h1]; simp


/-- **The perturbation separates the darts of the path**: two darts of the path of the cotree
from `s` to `t` with the same `lred (isoEpsG V F w) T` are equal. -/
theorem lred_isoEpsG_inj (hM : M.IsPlane) {w : D → ℤ} {s t : V} (hw : IsIsoW M t w) {T : DTree M} {d₁ d₂ : D}
    (h₁ : T.chi s t d₁ = 1) (h₂ : T.chi s t d₂ = 1)
    (h : lred (isoEpsG V F w) T d₁ = lred (isoEpsG V F w) T d₂) : d₁ = d₂ := by
  rw [lred_isoEpsG, lred_isoEpsG, lred_isoWG hM hw h₁, lred_isoWG hM hw h₂] at h
  have hb : ∀ {d}, T.chi s t d = 1 → 1 ≤ ((T.side d).card : ℤ) ∧
      ((T.side d).card : ℤ) + 1 ≤ Fintype.card V := by
    intro d hd
    obtain ⟨hs, ht⟩ := side_of_chi hM hd
    have h1 : 1 ≤ (T.side d).card := card_pos.2 ⟨s, hs⟩
    have h2 : (T.side d).card < (univ : Finset V).card :=
      card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨subset_univ _, fun e => ht (e ▸ mem_univ t)⟩)
    rw [card_univ] at h2
    constructor <;> [exact_mod_cast h1; exact_mod_cast h2]
  obtain ⟨a1, a2⟩ := hb h₁
  obtain ⟨b1, b2⟩ := hb h₂
  have hL : (Fintype.card V : ℤ) ≤ isoL V F := by
    unfold isoL; nlinarith [(by positivity : (0 : ℤ) ≤ Fintype.card V)]
  set k := lred (fun _ => (1 : ℤ)) T d₁ - lred (fun _ => (1 : ℤ)) T d₂
  have hk : isoL V F * k = ((T.side d₂).card : ℤ) - (T.side d₁).card := by
    simp only [k]; linarith
  have hk0 : k = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : isoL V F * k ≤ - isoL V F := by nlinarith
      linarith
    · have : isoL V F ≤ isoL V F * k := by nlinarith
      linarith
  rw [hk0, mul_zero] at hk
  have hc : (T.side d₁).card = (T.side d₂).card := by omega
  rcases side_nested hM h₁ h₂ with hs | hs
  · exact side_inj hM h₁ h₂ (eq_of_subset_of_card_le hs hc.symm.le)
  · exact side_inj hM h₁ h₂ (eq_of_subset_of_card_le hs hc.le).symm


/-! ### The parent darts are tight in the cut of the cover -/

variable (V F) in
/-- **The lengths of the darts of the cover** for the perturbation `isoEpsG V F w`:
`N c + isoL + isoW`, with `N = covNW`. -/
noncomputable def covLenWG (K : ℕ) (c : D → ℤ) (w : D → ℤ) (x : D × ZMod K) : ℤ :=
  covNW V F (isoEpsG V F w) K * c x.1 + isoL V F + w x.1

lemma covLenWG_eq (K : ℕ) (c : D → ℤ) (w : D → ℤ) (x : D × ZMod K) :
    covLenWG V F K c w x = covNW V F (isoEpsG V F w) K * c x.1 + isoEpsG V F w x.1 := by
  simp only [covLenWG, isoEpsG]; ring

lemma sum_covLenWG (K : ℕ) (c : D → ℤ) (w : D → ℤ) (l : List (D × ZMod K)) :
    (l.map (covLenWG V F K c w)).sum = covNW V F (isoEpsG V F w) K * dsum c (l.map Prod.fst) +
      dsum (isoEpsG V F w) (l.map Prod.fst) := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, dsum_cons, covLenWG_eq]; ring

section Tight

variable (hrot : M.RotTrans) (π : SPath M) (hk : 0 < π.k) (K : ℕ) [NeZero K]

local notation "𝓜" => cover (pathCov hrot π) K
local notation "𝓛" => (liftPath hrot π K hk).darts
local notation "hL" => (liftPath hrot π K hk).rev_mem_darts'

/-- **The parent darts of the run with the word-size perturbation are tight arcs of the cut of
the cover**: for a state of the run rooted at the face of `d₀` (a dart leaving `t`), a face `b`
other than the root and a sheet `σ` such that the lift of the path of the tree to `b` from the
sheet `σ` stays in the sheets `1, …, K - 2`, the lift of the parent dart of `b` is tight for the
root of `(d₀, σ)` in the cut with the perturbed lengths `pert (cutLen (covLenWG …))`. -/
theorem tight_parWG (hM : M.IsPlane) {w : D → ℤ} (hw : IsIsoW M (π.p π.k) w) (hface : M.FaceTrans) (hK : 2 ≤ K) (hKB : K < lexBase F)
    {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) {st : LSt M}
    (hI : LInv c (isoEpsG V F w) (π.p 0) (π.p π.k) st) {d₀ : D}
    (hd₀ : M.tail d₀ = π.p π.k)
    (hroot : st.T.root = M.face d₀) {b : F} (hb : b ≠ st.T.root) (σ : ZMod K)
    (hrange : ∀ y, st.T.Anc y b → 1 ≤ (σ.val : ℤ) + st.T.psum (pflow π) y ∧
      (σ.val : ℤ) + st.T.psum (pflow π) y + 2 ≤ K) :
    Tight (pieceGraph (cutMap hL) (cutPiece 𝓜 𝓛)
        (pert (cutLen 𝓜 𝓛 (covLenWG V F K c w))))
      (.inr (rootAt hrot π hk K hd₀ σ))
      (toArc hrot π hk K
        (st.T.par b, σ + ((st.T.psum (pflow π) (st.T.up b) : ℤ) : ZMod K))) := by
  classical
  have : Nonempty D := ⟨d₀⟩
  have hPu : IsUnit (M := M) (s := π.p 0) (t := π.p π.k) (pflow π) :=
    ⟨pflow_antisymm π, div_pflow π, fun d => by
      by_cases hd : d ∈ π.darts
      · obtain ⟨j, hj, rfl | rfl⟩ := π.mem_darts.1 hd
        · rw [pflow_d π hj]
        · rw [pflow_rev_d π hj]; omega
      · rw [pflow_of_not_mem π hd]; omega⟩
  set P := pflow π with hPdef
  set tt := π.p π.k with htt
  set ε := isoEpsG V F w with hεdef
  set ℓ := covLenWG V F K c w with hℓdef
  set N : ℤ := covNW V F ε K with hNdef
  set T := st.T with hTdef
  have hε0 : ∀ d, 0 ≤ ε d := fun d => (zero_le_one.trans (isoEpsG_bounds hM hw d).1)
  have hE0 : 0 ≤ ∑ d, ε d := sum_nonneg fun d _ => hε0 d
  have hV1 : (1 : ℤ) ≤ Fintype.card V := by exact_mod_cast card_V_pos M
  have hLpos : 0 < isoL V F := by unfold isoL; positivity
  have hN0 : (Fintype.card F : ℤ) * ∑ d, ε d < N := by
    simp only [hNdef, covNW]
    have : 0 ≤ isoL V F * (Fintype.card F * K) := by positivity
    linarith
  have hNpos : 0 < N := by simp only [hNdef, covNW]; positivity
  have hℓpos : ∀ x, 0 < ℓ x := fun x => by
    rw [hℓdef, covLenWG_eq]
    have := (isoEpsG_bounds hM hw x.1).1
    have : 0 ≤ N * c x.1 := mul_nonneg hNpos.le (hc x.1)
    linarith
  have hnn : ∀ e, e ∉ 𝓛 → 0 ≤ ℓ e := fun e _ => (hℓpos e).le
  have H := cutCover_hyp hrot π hk K hM hface hK ℓ hnn
  have hpos := H.pos'
  have hnn' := nonneg_of_pos hpos
  have hPp := isPerturb_pert (cutMap hL) (cutPiece 𝓜 𝓛) (cutLen 𝓜 𝓛 ℓ)
  -- the lift of the path of the tree
  set tp := T.tpath b with htp
  set Wt := liftList π K σ tp with hWt
  have hWtw : DWalk 𝓜 (M.face d₀, σ) Wt (b, σ + ((T.psum P b : ℤ) : ZMod K)) := by
    have := dWalk_liftList hrot π K (T.dWalk_tpath b) σ
    rw [T.dsum_tpath, hroot] at this
    exact this
  have hWtL : ∀ x ∈ Wt, x ∉ 𝓛 := by
    intro x hx hmem
    obtain ⟨y, hy, ha, rfl⟩ := mem_liftList_tpath π K T σ hx
    have hup : T.Anc (T.up y) b := by
      obtain ⟨n, hn⟩ := ha
      exact ⟨n + 1, by rw [iterate_succ_apply', hn]⟩
    obtain ⟨h1, h2⟩ := hrange _ hup
    have hv := val_add_int σ (n := T.psum P (T.up y)) (by omega) (by omega)
    obtain ⟨hne0, hne1⟩ := ne_of_val_range K (a := σ + ((T.psum P (T.up y) : ℤ) : ZMod K))
      (by omega) (by omega)
    obtain ⟨j, -, h | h⟩ := (CombMap.mem_liftPath_darts hrot π K hk).1 hmem
    · exact hne1 (congrArg Prod.snd h)
    · exact hne0 (congrArg Prod.snd h)
  -- the walk of the cut along it
  set r : CutT 𝓜 𝓛 := rootAt hrot π hk K hd₀ σ
  set G := pieceGraph (cutMap hL) (cutPiece 𝓜 𝓛) (pert (cutLen 𝓜 𝓛 ℓ))
  set G₀ := pieceGraph (cutMap hL) (cutPiece 𝓜 𝓛) (cutLen 𝓜 𝓛 ℓ)
  set pend : {d // d ∈ cutPiece 𝓜 𝓛} := ⟨.inr (.inl r), by simp [mem_cutPiece, inPiece]⟩
  set zf : F × ZMod K := (b, σ + ((T.psum P b : ℤ) : ZMod K))
  set z : CutV 𝓜 𝓛 := .inl zf
  set W := pend :: Wt.map (toArc hrot π hk K) with hW
  have hWw : LWalk G (.inr r) z W :=
    LWalk.cons (G := G) (a := pend) (lwalk_toArc hrot π hk K _ hWtw hWtL)
  -- a shortest walk
  obtain ⟨L0, hL0⟩ := exists_isSP hnn' ⟨W, hWw⟩
  obtain ⟨L1, rfl, hL1⟩ := rootWalk hrot π hk K _ hL0.1
  obtain ⟨hcop, z', hz', hdw⟩ := copyWalk hrot π hk K _ hL1
  have hz'eq : z' = zf := by
    have := hz'.symm; simpa [z] using this
  subst hz'eq
  set lt := L1.map fun a => arcProj hrot π hk K a.1 with hlt
  have hltL := arcProj_not_mem hrot π hk K hcop
  have hL1eq := eq_map_toArc hrot π hk K hcop
  set l := lt.map Prod.fst with hl
  have hlw : DWalk M T.root l b := by rw [hroot]; exact dWalk_proj hrot π K hdw
  obtain ⟨hb1, hb2⟩ := hrange b (T.anc_self b)
  have hvb := val_add_int σ (n := T.psum P b) (by omega) (by omega)
  -- every walk of the cover avoiding the lift of `π` to `zf` is at the level of `b`
  have hlevel : ∀ l' : List (D × ZMod K), DWalk 𝓜 (M.face d₀, σ) l' zf → (∀ x ∈ l', x ∉ 𝓛) →
      dsum P (l'.map Prod.fst) = T.psum P b := by
    intro l' hl' hl'L
    have hsheet := dWalk_sheet hrot π hk K hl' hl'L
    change _ = _ + dsum P (l'.map Prod.fst) at hsheet
    simp only [zf] at hsheet
    rw [hvb] at hsheet; linarith
  -- the lengths
  have hlenWt : (Wt.map ℓ).sum = N * T.psum c b + T.psum ε b := by
    rw [sum_covLenWG, hWt, map_fst_liftList, T.dsum_tpath, T.dsum_tpath]
  -- the lift of the path of the tree is a least walk avoiding the lift of `π`
  have hWtmin : ∀ l' : List (D × ZMod K), DWalk 𝓜 (M.face d₀, σ) l' zf → (∀ x ∈ l', x ∉ 𝓛) →
      (Wt.map ℓ).sum ≤ (l'.map ℓ).sum := by
    intro l' hl' hl'L
    have hlw' : DWalk M T.root (l'.map Prod.fst) b := by
      rw [hroot]; exact dWalk_proj hrot π K hl'
    obtain ⟨hx1, hx2⟩ := linv_shortest_level hM (p0_ne_pk π hk) hI hPu hlw' (hlevel l' hl' hl'L)
    rw [← hTdef] at hx1 hx2
    rw [hlenWt, sum_covLenWG]
    have hεl : 0 ≤ dsum ε (l'.map Prod.fst) := dsum_nonneg fun d _ => hε0 d
    have hεb := T.psum_le hε0 b
    rcases hx1.lt_or_eq with hlt | heq
    · have : T.psum c b + 1 ≤ dsum c (l'.map Prod.fst) := by omega
      have := mul_le_mul_of_nonneg_left this hNpos.le
      linarith
    · rw [← heq]
      have := hx2 heq.symm
      linarith
  -- the walk found is at most as long
  have hWnd : W.Nodup := by
    rw [hW, List.nodup_cons]
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨x, hx, e⟩ := List.mem_map.1 h
      rw [toArc_of_not_mem hrot π hk K (hWtL x hx)] at e
      exact absurd (congrArg Subtype.val e) (by simp [copyA, pend])
    · refine List.Nodup.map_on (fun x hx y hy e => ?_) (nodup_liftList π K (T.nodup_tpath b))
      rw [toArc_of_not_mem hrot π hk K (hWtL x hx), toArc_of_not_mem hrot π hk K (hWtL y hy)]
        at e
      have := congrArg Subtype.val e
      simp only [copyA, Sum.inl.injEq, Subtype.mk.injEq] at this
      exact this
  have hcmp : MSSP.wlen G (pend :: L1) ≤ MSSP.wlen G W := by
    rw [hL0.2]; exact dist_le hnn' hWw
  have hlen0 : MSSP.wlen G₀ (pend :: L1) = (lt.map ℓ).sum := by
    rw [MSSP.wlen_cons, hL1eq, wlen_toArc hrot π hk K ℓ hltL]
    simp [G₀, pieceGraph, pend, cutLen, hlt, List.map_map]
  have hlenW : MSSP.wlen G₀ W = (Wt.map ℓ).sum := by
    rw [hW, MSSP.wlen_cons, wlen_toArc hrot π hk K ℓ hWtL]
    simp [G₀, pieceGraph, pend, cutLen]
  rw [hPp.wlen_eq, hPp.wlen_eq, hlen0, hlenW] at hcmp
  have hps := hPp.psum_lt hWnd
  have h2c : (0 : ℤ) < 2 ^ Fintype.card (CutD 𝓜 𝓛) := by positivity
  have hcomp : (lt.map ℓ).sum ≤ (Wt.map ℓ).sum := by
    by_contra hcon
    push Not at hcon
    have : (2 : ℤ) ^ Fintype.card (CutD 𝓜 𝓛) * ((Wt.map ℓ).sum + 1) ≤
        2 ^ Fintype.card (CutD 𝓜 𝓛) * (lt.map ℓ).sum :=
      mul_le_mul_of_nonneg_left (by omega) h2c.le
    have : (0 : ℤ) ≤ (psum (fun a => (Fintype.equivFin (CutD 𝓜 𝓛) a.1 : ℕ)) (pend :: L1) : ℤ) :=
      Nat.cast_nonneg _
    have : ((psum (fun a => (Fintype.equivFin (CutD 𝓜 𝓛) a.1 : ℕ)) W : ℕ) : ℤ) <
        2 ^ Fintype.card (CutD 𝓜 𝓛) := by exact_mod_cast hps
    nlinarith
  -- both are least walks of the dual of the cover: they are equal
  set N' := (𝓜).dual
  set w' : D × ZMod K → ℤ := fun x => w x.1
  set t' : CovV V (π.p 0) (π.p π.k) K := Sum.inl ⟨π.p π.k, Or.inr rfl⟩
  have hcovP : (𝓜).IsPlane := cover_isPlane hM hrot (p0_ne_pk π hk) (div_pflow_s π hk)
  have hNP : N'.IsPlane := hcovP.dual
  have hNR : N'.RotTrans := dual_rotTrans' (cover_faceTrans hface)
  obtain ⟨hwa, hwdiv, -⟩ := hw
  have hw' : N'.IsAntisymm w' := fun x => hwa x.1
  have hcurl_eq : ∀ a, N'.curl w' a = (𝓜).div w' a := fun a => rfl
  have hcurl : ∀ a, a ≠ t' → 0 < N'.curl w' a := by
    intro a ha
    rw [hcurl_eq]
    rcases a with ⟨v, hv⟩ | ⟨⟨v, hv⟩, j⟩
    · rw [cover_div_inl (pathCov hrot π) K _ v hv, hwdiv]
      have hvt : v ≠ tt := fun e => ha (by simp only [t']; congr)
      simp only [hvt, ↓reduceIte]
      have : (0 : ℤ) < K := by have := NeZero.pos K; exact_mod_cast this
      linarith
    · rw [cover_div_inr (pathCov hrot π) K _ v hv j, hwdiv]; simp [htt, hv.2]
  have hcurl_t : N'.curl w' t' = K * (1 - Fintype.card V) := by
    rw [hcurl_eq, cover_div_inl (pathCov hrot π) K _ _ _, hwdiv]
    simp [htt]
  have hsumL : ∑ a ∈ univ.erase t', N'.curl w' a < isoL V F := by
    have h0 := sum_curl_univ (M := N') hw'
    rw [← sum_erase_add _ _ (mem_univ t'), hcurl_t] at h0
    have hKle : (K : ℤ) ≤ 4 * Fintype.card F + 4 := by
      have := hKB; unfold lexBase at this; omega
    unfold isoL
    nlinarith [mul_le_mul_of_nonneg_right hKle (by linarith : (0:ℤ) ≤ Fintype.card V - 1)]
  have hcardN : isoL V F * (Fintype.card (F × ZMod K) : ℤ) ≤ N := by
    simp only [hNdef, covNW, Fintype.card_prod, ZMod.card]
    push_cast
    have : 0 ≤ ((Fintype.card F : ℤ) + 1) * ∑ d, ε d := by positivity
    linarith
  have hℓform : ℓ = fun x => N * c x.1 + isoL V F + w' x := by
    funext x; rfl
  have hGeq : ∀ y z (l' : List (D × ZMod K)), DWalk 𝓜 y l' z ↔
      BKMNW.IsWalk (N'.graph fun x => N * c x.1 + isoL V F + w' x) y l' z :=
    fun y z l' => by unfold DWalk; refine isWalk_congr ?_ ?_ <;> rfl
  have hmin : ∀ l₀, DWalk 𝓜 (M.face d₀, σ) l₀ zf → (∀ x ∈ l₀, x ∉ 𝓛) →
      (l₀.map ℓ).sum ≤ (Wt.map ℓ).sum →
      IsMinW (N'.graph fun x => N * c x.1 + isoL V F + w' x) (fun x => x ∉ 𝓛)
        (M.face d₀, σ) zf l₀ := by
    intro l₀ h₀ h₀L hle
    refine ⟨(hGeq _ _ _).1 h₀, h₀L, fun l' hl' hl'L => ?_⟩
    have := hWtmin l' ((hGeq _ _ _).2 hl') hl'L
    change (l₀.map ℓ).sum ≤ (l'.map ℓ).sum
    linarith
  have hltWt : lt = Wt := curl_unique hNP hNR hw' hcurl hsumL hcardN (fun x => c x.1)
    (fun x _ => by have := hℓpos x; rw [hℓform] at this; exact this) (hmin lt hdw hltL hcomp)
    (hmin Wt hWtw hWtL le_rfl)
  have hltp : l = tp := by rw [hl, hltWt, hWt, map_fst_liftList]
  -- the last arc
  rcases List.eq_nil_or_concat' L1 with rfl | ⟨L2, a, rfl⟩
  · exfalso
    have : l = [] := by simp [hl, hlt]
    rw [this, htp, T.tpath_of_ne hb] at hltp
    simp at hltp
  obtain ⟨x, hx, rfl⟩ := hcop a (by simp)
  have hlast : x.1 = T.par b := by
    have := hltp
    rw [htp, T.tpath_of_ne hb] at this
    simp only [hl, hlt, List.map_append, List.map_cons, List.map_nil] at this
    exact (List.append_inj' this rfl).2 |> List.singleton_inj.1
  obtain ⟨-, hdst⟩ := LWalk.concat_iff.1 (by simpa using hL1)
  rw [copyA_dst] at hdst
  have hx2' : x.2 = σ + ((T.psum P (T.up b) : ℤ) : ZMod K) := by
    have e := congrArg Prod.snd (Sum.inl_injective hdst)
    simp only [zf] at e
    rw [hlast, T.psum_of_ne P hb] at e
    push_cast at e
    linear_combination e
  have hxe : x = (T.par b, σ + ((T.psum P (T.up b) : ℤ) : ZMod K)) := Prod.ext hlast hx2'
  subst hxe
  rw [toArc_of_not_mem hrot π hk K hx]
  exact tight_of_last hnn' (l := pend :: L2) (by simpa using hL0.1) (by simpa using hL0.2)

end Tight


/-! ### At most `m + 1` steps; the properties used by the program -/

lemma covLenWG_nonneg (hM : M.IsPlane) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) (K : ℕ)
    {w : D → ℤ} {t : V} (hw : IsIsoW M t w) (x : D × ZMod K) : 0 ≤ covLenWG V F K c w x := by
  rw [covLenWG_eq]
  have h1 := (isoEpsG_bounds hM hw x.1).1
  have h2 : 0 ≤ covNW V F (isoEpsG V F w) K := by
    have : 0 ≤ ∑ d, isoEpsG V F w d := sum_nonneg fun d _ => (zero_le_one.trans (isoEpsG_bounds hM hw d).1)
    unfold covNW isoL; positivity
  have := mul_nonneg h2 (hc x.1)
  linarith

/-- The parent darts of the run with the perturbation `isoEpsG w` are tight in the cut of the
cover with the lengths `covLenWG`. -/
lemma tightLev_isoG (hrot : M.RotTrans) (π : SPath M) (hk : 0 < π.k) (hM : M.IsPlane)
    (hface : M.FaceTrans) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) {w : D → ℤ}
    (hw : IsIsoW M (π.p π.k) w) :
    TightLev c (isoEpsG V F w) hrot π hk (covLenWG V F (nSheets F) c w) := by
  intro st hI d₀ hd₀ hroot b hb
  have := tight_parWG hrot π hk (nSheets F) hM hw hface (by unfold nSheets; omega)
    (by unfold nSheets lexBase; omega) hc hI hd₀ hroot hb _ (range_sheetOf π st.T)
  rwa [liftEnd_eq_par π st.T hb] at this

/-- **Every run with the perturbation `isoEpsG w` takes at most `m + 1` steps** (`IsIsoW M t w`). -/
theorem lstepsWG_le (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {c : D → ℤ}
    (hc : ∀ d, 0 ≤ c d) {s t : V} (hst : s ≠ t) {w : D → ℤ} (hw : IsIsoW M t w) {d₀ : D}
    (hd₀ : M.tail d₀ = t) {st : LSt M}
    (hI : LInv c (isoEpsG V F w) s t st) (hroot : st.T.root = M.face d₀) (n : ℕ) :
    (lrun M c (isoEpsG V F w) s t n st).2.1 ≤ Fintype.card D + 1 := by
  refine lsteps_le_of hM hrot hface hc hst (fun π hk _ ht => ?_) hd₀ hI hroot n
  subst ht
  exact ⟨_, covLenWG_nonneg hM hc _ hw, tightLev_isoG hrot π hk hM hface hc hw⟩

/-- **The perturbation `isoEpsG w` has the properties used by the program** (`PertOK`), for every
isolating weight `w` of the sink. -/
theorem pertOK_isoG (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {c : D → ℤ}
    (hc : ∀ d, 0 ≤ c d) {s t : V} (hst : s ≠ t) {w : D → ℤ} (hw : IsIsoW M t w) {d₀ : D}
    (hd₀ : M.tail d₀ = t) : PertOK M c (isoEpsG V F w) s t d₀ where
  nonneg d := (zero_le_one.trans (isoEpsG_bounds hM hw d).1)
  sep _ _ _ h₁ h₂ h := lred_isoEpsG_inj hM hw h₁ h₂ h
  steps _ hI hroot n := lstepsWG_le hM hrot hface hc hst hw hd₀ hI hroot n

lemma lexR_isoG_le (hM : M.IsPlane) {w : D → ℤ} {t : V} (hw : IsIsoW M t w) :
    0 ≤ lexR F (isoEpsG V F w) ∧ lexR F (isoEpsG V F w) ≤ isoR D V F := by
  have h1 : ∑ d, isoEpsG V F w d ≤ ∑ _d : D, (4 * Fintype.card F + 6) * (Fintype.card V : ℤ) :=
    sum_le_sum fun d _ => (isoEpsG_bounds hM hw d).2
  have h0 : 0 ≤ ∑ d, isoEpsG V F w d := sum_nonneg fun d _ => (zero_le_one.trans (isoEpsG_bounds hM hw d).1)
  simp only [sum_const, card_univ, nsmul_eq_mul] at h1
  unfold lexR isoR
  constructor
  · positivity
  · have : (0 : ℤ) ≤ Fintype.card F + 1 := by positivity
    nlinarith

/-- **`kH0` is polynomially bounded** for the perturbation `isoEpsG w` (`N = 2 lexR + 1`). -/
theorem kH0_isoG_le (hM : M.IsPlane) {w : D → ℤ} {t : V} (hw : IsIsoW M t w) {c : D → ℤ}
    (hc : ∀ d, 0 ≤ c d) :
    kH0 D F (2 * lexR F (isoEpsG V F w) + 1) c (isoEpsG V F w) ≤ isoW_bound D V F c := by
  obtain ⟨h0, h1⟩ := lexR_isoG_le hM hw
  have hS : 0 ≤ ∑ d, c d := sum_nonneg fun d _ => hc d
  set R := lexR F (isoEpsG V F w)
  have hZ : kZ D F (2 * R + 1) c (isoEpsG V F w) ≤ (2 * isoR D V F + 1) * (∑ d, c d + 1) := by
    unfold kZ; nlinarith
  have hZ0 : 0 ≤ kZ D F (2 * R + 1) c (isoEpsG V F w) := by unfold kZ; positivity
  unfold kH0 kTh isoW_bound
  have hR0 : 0 ≤ isoR D V F := le_trans h0 h1
  have : (0 : ℤ) ≤ (2 * isoR D V F + 1) * (∑ d, c d + 1) := by positivity
  nlinarith


/-! ### An isolating weight from a spanning tree of the vertices -/

/-- **The tree weight of a spanning tree of the vertices is an isolating weight of its root**
(`MSSP.treeW` on the dual map: `tsz y` on `rev (par y)`, `- tsz y` on `par y`): what the
machine computes from the parent darts of any spanning tree rooted at the sink. -/
theorem isIsoW_treeW (C : DTree M.dual) : IsIsoW M C.root (MSSP.treeW C) := by
  classical
  have hw := MSSP.treeW_isoW C
  refine ⟨hw.antisymm, fun v => ?_, fun d => MSSP.abs_treeW_le C d⟩
  have e1 : M.div (MSSP.treeW C) v = MSSP.curl M.dual (MSSP.treeW C) v := rfl
  rw [e1, ← funext (MSSP.sum_dflow_tpath C)]
  have e2 : MSSP.curl M.dual (fun d => ∑ y, MSSP.dflow M.dual (MSSP.tpath C y) d) v =
      ∑ y, MSSP.curl M.dual (MSSP.dflow M.dual (MSSP.tpath C y)) v := by
    simp only [MSSP.curl]; rw [Finset.sum_comm]
  rw [e2]
  simp only [MSSP.curl_dflow (MSSP.tpath_walk C _ _ rfl), Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  by_cases h : v = C.root
  · subst h; simp
  · simp [h, Ne.symm h]

end STFlow

end PlanarFlow
