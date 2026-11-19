module

public import PlanarFlow.STFlow.CoverTight
public import PlanarFlow.STFlow.IsoWalk
public import PlanarFlow.STFlow.IsoEps

/-!
# The parent darts are tight in the cut of the cover, for the word-size perturbation

`PlanarFlow/STFlow/CoverTight.lean` proves, for the perturbation `lexEps`, that the lift of the
parent dart of a face `b` is a tight arc of the cut of the cyclic cover (`tight_par`), the fact
behind the pivot bound (`PlanarFlow/STFlow/LexCount.lean`). The key step there is that the lift
of the path of the dual tree is **the unique** shortest walk of the cut for the lengths
`N c + ε`; with `lexEps` this follows from base-`(4 F + 5)` digits. This file proves it for the
word-size perturbation `isoEps M t = isoL + isoW M t` (`PlanarFlow/STFlow/IsoEps.lean`), by the
isolation of `PlanarFlow/STFlow/IsoWalk.lean` in the dual of the cover:

* the cover of a plane map is a plane map (`cover_isPlane`), its dual has transitive rotations;
* the lift of `w = isoW M t` has net flow `1` out of every vertex of the cover but the branch
  point above `t`, where it is `K (1 - #V)` (`cover_div_inl`, `cover_div_inr`): its curl in the
  dual of the cover is positive off one face, with total `K (#V - 1) < isoL`;
* with `N = (F + 1) Σ ε + isoL · #F · K + 1` (`covLenW`), the lengths of the dual of the cover
  have the form `N c + isoL + w` of `curl_unique`: least walks avoiding the lift of `π` are unique.

* `tight_parW`: **the lift of the parent dart of `b` is tight** for the root of `(d₀, σ)`, in
  the cut with the perturbed lengths `pert (cutLen (covLenW …))`, for every state of the run
  with the perturbation `isoEps M t` (`LInv`).
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

/-! ### The dual of a map -/

lemma dual_rot_eq (N : CombMap D V F) : N.dual.rot = N.next := by
  funext d
  show N.rot (N.rev d) = N.next d
  simp only [CombMap.rot, N.rev_rev]

lemma dual_rotTrans' {N : CombMap D V F} (hface : N.FaceTrans) : N.dual.RotTrans := by
  intro d d' h
  rw [dual_rot_eq]
  exact hface d d' h

lemma isWalk_congr {X A : Type*} {G G' : Digraph X A} (hs : G.src = G'.src)
    (hd : G.dst = G'.dst) {x y : X} {l : List A} :
    BKMNW.IsWalk G x l y ↔ BKMNW.IsWalk G' x l y := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simp only [isWalk_cons, hs, hd, ih]

/-! ### The net flows of a lifted function -/

section Lift

variable {s t : V} (C : CovData M s t) (K : ℕ) [NeZero K]

/-- At a branch point the net flow of a lifted function is `K` times the net flow below. -/
lemma cover_div_inl (w : D → ℤ) (v : V) (hv : v = s ∨ v = t) :
    (cover C K).div (fun x => w x.1) (Sum.inl ⟨v, hv⟩) = K * M.div w v := by
  unfold CombMap.div
  have e : (univ.filter fun x : D × ZMod K => (cover C K).tail x = Sum.inl ⟨v, hv⟩) =
      (univ.filter fun d => M.tail d = v) ×ˢ univ := by
    ext ⟨d, i⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, and_true, cover_tail, covTail]
    by_cases h : M.tail d = s ∨ M.tail d = t
    · simp only [h, ↓reduceDIte, Sum.inl.injEq, Subtype.mk.injEq]
    · simp only [h, ↓reduceDIte, reduceCtorEq, false_iff]
      intro e; exact h (e ▸ hv)
  rw [e, sum_product]
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_sum]

/-- At a lift of a vertex other than the branch points the net flow of a lifted function is the
net flow below. -/
lemma cover_div_inr (w : D → ℤ) (v : V) (hv : v ≠ s ∧ v ≠ t) (j : ZMod K) :
    (cover C K).div (fun x => w x.1) (Sum.inr (⟨v, hv⟩, j)) = M.div w v := by
  unfold CombMap.div
  have e : (univ.filter fun x : D × ZMod K => (cover C K).tail x = Sum.inr (⟨v, hv⟩, j)) =
      (univ.filter fun d => M.tail d = v).image fun d => (d, j + (C.pos d : ZMod K)) := by
    ext ⟨d, i⟩
    rw [Finset.mem_filter, Finset.mem_image]
    simp only [Finset.mem_univ, true_and, cover_tail, covTail, Prod.mk.injEq, Finset.mem_filter]
    by_cases h : M.tail d = s ∨ M.tail d = t
    · simp only [h, ↓reduceDIte, reduceCtorEq, false_iff, not_exists, not_and]
      rintro d' hd' rfl -
      rcases h with h | h
      · exact hv.1 (hd' ▸ h)
      · exact hv.2 (hd' ▸ h)
    · simp only [h, ↓reduceDIte, Sum.inr.injEq, Prod.mk.injEq, Subtype.mk.injEq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨d, h1, rfl, by rw [← h2]; ring⟩
      · rintro ⟨d', h1, rfl, h2⟩
        exact ⟨h1, by rw [← h2]; ring⟩
  rw [e, sum_image (fun a _ b _ h => (Prod.mk.inj h).1)]

end Lift

/-! ### The lengths of the cover -/

variable (V F) in
/-- The scale of the capacities in the lengths of the cover: `(F + 1) Σ ε + isoL · #F · K + 1`.
-/
noncomputable def covNW (ε : D → ℤ) (K : ℕ) : ℤ :=
  (Fintype.card F + 1) * ∑ d, ε d + isoL V F * (Fintype.card F * K) + 1

variable (M) in
/-- **The lengths of the darts of the cover** for the perturbation `isoEps M t`:
`N c + isoL + isoW`, with `N = covNW`. -/
noncomputable def covLenW (K : ℕ) (c : D → ℤ) (t : V) (x : D × ZMod K) : ℤ :=
  covNW V F (isoEps M t) K * c x.1 + isoL V F + isoW M t x.1

lemma covLenW_eq (K : ℕ) (c : D → ℤ) (t : V) (x : D × ZMod K) :
    covLenW M K c t x = covNW V F (isoEps M t) K * c x.1 + isoEps M t x.1 := by
  simp only [covLenW, isoEps]; ring

lemma sum_covLenW (K : ℕ) (c : D → ℤ) (t : V) (l : List (D × ZMod K)) :
    (l.map (covLenW M K c t)).sum = covNW V F (isoEps M t) K * dsum c (l.map Prod.fst) +
      dsum (isoEps M t) (l.map Prod.fst) := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, dsum_cons, covLenW_eq]; ring

section Tight

variable (hrot : M.RotTrans) (π : SPath M) (hk : 0 < π.k) (K : ℕ) [NeZero K]

local notation "𝓜" => cover (pathCov hrot π) K
local notation "𝓛" => (liftPath hrot π K hk).darts
local notation "hL" => (liftPath hrot π K hk).rev_mem_darts'

/-- **The parent darts of the run with the word-size perturbation are tight arcs of the cut of
the cover**: for a state of the run rooted at the face of `d₀` (a dart leaving `t`), a face `b`
other than the root and a sheet `σ` such that the lift of the path of the tree to `b` from the
sheet `σ` stays in the sheets `1, …, K - 2`, the lift of the parent dart of `b` is tight for the
root of `(d₀, σ)` in the cut with the perturbed lengths `pert (cutLen (covLenW …))`. -/
theorem tight_parW (hM : M.IsPlane) (hface : M.FaceTrans) (hK : 2 ≤ K) (hKB : K < lexBase F)
    {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) {st : LSt M}
    (hI : LInv c (isoEps M (π.p π.k)) (π.p 0) (π.p π.k) st) {d₀ : D}
    (hd₀ : M.tail d₀ = π.p π.k)
    (hroot : st.T.root = M.face d₀) {b : F} (hb : b ≠ st.T.root) (σ : ZMod K)
    (hrange : ∀ y, st.T.Anc y b → 1 ≤ (σ.val : ℤ) + st.T.psum (pflow π) y ∧
      (σ.val : ℤ) + st.T.psum (pflow π) y + 2 ≤ K) :
    Tight (pieceGraph (cutMap hL) (cutPiece 𝓜 𝓛)
        (pert (cutLen 𝓜 𝓛 (covLenW M K c (π.p π.k)))))
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
  set ε := isoEps M tt with hεdef
  set ℓ := covLenW M K c tt with hℓdef
  set N : ℤ := covNW V F ε K with hNdef
  set T := st.T with hTdef
  have hε0 : ∀ d, 0 ≤ ε d := fun d => isoEps_nonneg hM tt d
  have hE0 : 0 ≤ ∑ d, ε d := sum_nonneg fun d _ => hε0 d
  have hV1 : (1 : ℤ) ≤ Fintype.card V := by exact_mod_cast card_V_pos M
  have hLpos : 0 < isoL V F := by unfold isoL; positivity
  have hN0 : (Fintype.card F : ℤ) * ∑ d, ε d < N := by
    simp only [hNdef, covNW]
    have : 0 ≤ isoL V F * (Fintype.card F * K) := by positivity
    linarith
  have hNpos : 0 < N := by simp only [hNdef, covNW]; positivity
  have hℓpos : ∀ x, 0 < ℓ x := fun x => by
    rw [hℓdef, covLenW_eq]
    have := (isoEps_bounds hM tt x.1).1
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
    rw [sum_covLenW, hWt, map_fst_liftList, T.dsum_tpath, T.dsum_tpath]
  -- the lift of the path of the tree is a least walk avoiding the lift of `π`
  have hWtmin : ∀ l' : List (D × ZMod K), DWalk 𝓜 (M.face d₀, σ) l' zf → (∀ x ∈ l', x ∉ 𝓛) →
      (Wt.map ℓ).sum ≤ (l'.map ℓ).sum := by
    intro l' hl' hl'L
    have hlw' : DWalk M T.root (l'.map Prod.fst) b := by
      rw [hroot]; exact dWalk_proj hrot π K hl'
    obtain ⟨hx1, hx2⟩ := linv_shortest_level hM (p0_ne_pk π hk) hI hPu hlw' (hlevel l' hl' hl'L)
    rw [← hTdef] at hx1 hx2
    rw [hlenWt, sum_covLenW]
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
  set w' : D × ZMod K → ℤ := fun x => isoW M tt x.1
  set t' : CovV V (π.p 0) (π.p π.k) K := Sum.inl ⟨π.p π.k, Or.inr rfl⟩
  have hcovP : (𝓜).IsPlane := cover_isPlane hM hrot (p0_ne_pk π hk) (div_pflow_s π hk)
  have hNP : N'.IsPlane := hcovP.dual
  have hNR : N'.RotTrans := dual_rotTrans' (cover_faceTrans hface)
  obtain ⟨hwa, hwdiv, -⟩ := isoW_spec hM tt
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

end STFlow

end PlanarFlow
