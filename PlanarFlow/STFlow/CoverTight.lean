module

public import PlanarFlow.STFlow.CoverRing

/-!
# The parent darts of the perturbed run are tight arcs in the cut of the cover

Let `st` be a state of the perturbed run (`LInv`), with the root of the dual tree the face `o` of
a dart `d₀` leaving `t`, and `P = pflow π` the unit flow of a simple path `π` from `s` to `t`.
The path of the tree from `o` to a face `b`, lifted to the cyclic cover from the sheet `σ`, ends
in the sheet `σ + psum P b`; if it stays in the sheets `1, …, K - 2`, it is a walk of the cut of
the cover (`PlanarFlow/STFlow/CoverCut.lean`). With the lengths `N c + ε` on the copies of the
darts (`covLen`), it is **the shortest walk** from the root of `(d₀, σ)` to the copy of
`(b, σ + psum P b)`: a shortest walk projects to a dual walk of `M` from `o` to `b` at the level
of `b`, at least as long for `(c, ε)` lexicographically as the path of the tree
(`PlanarFlow.STFlow.linv_shortest_level`); equality forces the same multiset of darts (the base
of the perturbation exceeds the number of sheets, `count_eq_of_dsum_eq`), hence the path of the
tree (`DTree.eq_tpath_of_count`).

* `tight_par`: **the lift of the parent dart of `b` is tight** for the root of `(d₀, σ)`, in the
  cut with the perturbed lengths `pert (cutLen …)` of `PlanarFlow/STFlow/CoverRing.lean`.
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

variable (hrot : M.RotTrans) (π : SPath M) (hk : 0 < π.k) (K : ℕ) [NeZero K]

local notation "𝓜" => cover (pathCov hrot π) K
local notation "𝓛" => (liftPath hrot π K hk).darts
local notation "hL" => (liftPath hrot π K hk).rev_mem_darts'

/-! ### Lifting the paths of the tree -/

lemma mem_liftList_tpath (T : DTree M) (σ : ZMod K) {b : F} {x : D × ZMod K}
    (hx : x ∈ liftList π K σ (T.tpath b)) :
    ∃ y, y ≠ T.root ∧ T.Anc y b ∧
      x = (T.par y, σ + ((T.psum (pflow π) (T.up y) : ℤ) : ZMod K)) := by
  refine T.depth_induction (p := fun b => x ∈ liftList π K σ (T.tpath b) →
    ∃ y, y ≠ T.root ∧ T.Anc y b ∧
      x = (T.par y, σ + ((T.psum (pflow π) (T.up y) : ℤ) : ZMod K))) ?_ ?_ b hx
  · intro h; rw [T.tpath_root] at h; simp [liftList] at h
  · intro b hb ih h
    rw [T.tpath_of_ne hb, liftList_append, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨y, hy, ha, rfl⟩ := ih h
      exact ⟨y, hy, T.anc_of_up ha, rfl⟩
    · simp only [liftList, List.mem_singleton] at h
      exact ⟨b, hb, T.anc_self b, by rw [h, T.dsum_tpath]⟩

lemma nodup_liftList {σ : ZMod K} {l : List D} (h : l.Nodup) : (liftList π K σ l).Nodup := by
  rw [← map_fst_liftList π K σ l] at h
  exact h.of_map _

/-- The number of lifts of a dart in a list of distinct darts of the cover is at most `K`. -/
lemma count_fst_le {l : List (D × ZMod K)} (hl : l.Nodup) (d : D) :
    (l.map Prod.fst).count d ≤ K := by
  have e : (l.map Prod.fst).count d = (l.filter fun x => x.1 = d).length := by
    rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
    congr 1
  rw [e]
  have hnd : ((l.filter fun x => x.1 = d).map Prod.snd).Nodup := by
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) (hl.filter _)
    have h1 := (List.mem_filter.1 hx).2
    have h2 := (List.mem_filter.1 hy).2
    simp only [decide_eq_true_eq] at h1 h2
    exact Prod.ext (h1.trans h2.symm) hxy
  have := hnd.length_le_card
  simpa [ZMod.card] using this

/-! ### Arcs of the cut -/

/-- The arc of the cut copying a dart of the cover (a pendant arc, for a deleted dart). -/
noncomputable def toArc (x : D × ZMod K) : {d // d ∈ cutPiece 𝓜 𝓛} :=
  if h : x ∉ 𝓛 then copyA hrot π hk K h else ⟨.inr (.inl (t0T hrot π hk K)), by
    simp [mem_cutPiece, inPiece]⟩

lemma toArc_of_not_mem {x : D × ZMod K} (h : x ∉ 𝓛) :
    toArc hrot π hk K x = copyA hrot π hk K h := by
  simp [toArc, h]

variable (ℓ' : CutD (cover (pathCov hrot π) K) (liftPath hrot π K hk).darts → ℤ)

local notation "𝒢" =>
  pieceGraph (cutMap (liftPath hrot π K hk).rev_mem_darts') (cutPiece 𝓜 𝓛) ℓ'

lemma lwalk_toArc {y z : F × ZMod K} {l : List (D × ZMod K)} (h : DWalk 𝓜 y l z)
    (hl : ∀ x ∈ l, x ∉ 𝓛) : LWalk 𝒢 (.inl y) (.inl z) (l.map (toArc hrot π hk K)) := by
  induction l generalizing y with
  | nil => obtain rfl := dWalk_nil.1 h; exact .nil _
  | cons x l ih =>
    obtain ⟨h1, h2⟩ := h
    have hx := hl x (by simp)
    rw [List.map_cons, toArc_of_not_mem hrot π hk K hx]
    have := LWalk.cons (G := 𝒢) (a := copyA hrot π hk K hx)
      (ih h2 fun x' hx' => hl x' (List.mem_cons_of_mem _ hx'))
    rw [copyA_src] at this
    have e : (M.face x.1, x.2) = y := h1
    rw [e] at this
    exact this

/-- A list of copies is the list of arcs of its darts. -/
lemma eq_map_toArc {l : List {d // d ∈ cutPiece 𝓜 𝓛}}
    (h : ∀ a ∈ l, ∃ x hx, a = copyA hrot π hk K (x := x) hx) :
    l = (l.map fun a => arcProj hrot π hk K a.1).map (toArc hrot π hk K) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨x, hx, rfl⟩ := h a (by simp)
    simp only [List.map_cons]
    rw [← ih fun a ha => h a (List.mem_cons_of_mem _ ha)]
    congr 1
    exact (toArc_of_not_mem hrot π hk K hx).symm

/-- The darts of a walk of copies are off the lift of `π`. -/
lemma arcProj_not_mem {l : List {d // d ∈ cutPiece 𝓜 𝓛}}
    (h : ∀ a ∈ l, ∃ x hx, a = copyA hrot π hk K (x := x) hx) :
    ∀ x ∈ l.map (fun a => arcProj hrot π hk K a.1), x ∉ 𝓛 := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  obtain ⟨y, hy, rfl⟩ := h a ha
  exact hy

variable (ℓ : D × ZMod K → ℤ)

lemma wlen_toArc {l : List (D × ZMod K)} (hl : ∀ x ∈ l, x ∉ 𝓛) :
    MSSP.wlen (pieceGraph (cutMap hL) (cutPiece 𝓜 𝓛) (cutLen 𝓜 𝓛 ℓ)) (l.map (toArc hrot π hk K)) =
      (l.map ℓ).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx := hl x (by simp)
    rw [List.map_cons, MSSP.wlen_cons, toArc_of_not_mem hrot π hk K hx,
      ih fun x' hx' => hl x' (List.mem_cons_of_mem _ hx')]
    simp only [List.map_cons, List.sum_cons]
    rfl

/-! ### The lengths of the cut and the main lemma -/

variable (F) in
/-- The lengths of the darts of the cover: `N c + ε` with `N = (F + 1) Σ ε + 1`. -/
noncomputable def covLen (c ε : D → ℤ) (x : D × ZMod K) : ℤ :=
  ((Fintype.card F + 1) * ∑ d, ε d + 1) * c x.1 + ε x.1

lemma covLen_nonneg {c ε : D → ℤ} (hc : ∀ d, 0 ≤ c d) (hε : ∀ d, 0 ≤ ε d) (x : D × ZMod K) :
    0 ≤ covLen F K c ε x := by
  have : 0 ≤ ∑ d, ε d := sum_nonneg fun d _ => hε d
  unfold covLen
  have := hc x.1; have := hε x.1
  positivity

lemma dsum_covLen (c ε : D → ℤ) (l : List (D × ZMod K)) :
    (l.map (covLen F K c ε)).sum = ((Fintype.card F + 1) * ∑ d, ε d + 1) *
      dsum c (l.map Prod.fst) + dsum ε (l.map Prod.fst) := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, dsum_cons, covLen]; ring

lemma mem_cutS_d0 {d₀ : D} (hd₀ : M.tail d₀ = π.p π.k) (σ : ZMod K) :
    (𝓜).tail (d₀, σ) ∈ cutS 𝓜 𝓛 := by
  have e : (𝓜).tail (d₀, σ) = (𝓜).tail (xT π K) := by
    simp only [cover_tail, xT]
    rw [covTail_branch _ (Or.inr hd₀), covTail_branch _ (Or.inr (tail_yT π hk))]
    simp [hd₀, tail_yT π hk]
  rw [e]
  exact tail_mem_cutS (xT_mem hrot π hk K)

/-- The root of the ring standing for the lift `(d₀, σ)`. -/
def rootAt {d₀ : D} (hd₀ : M.tail d₀ = π.p π.k) (σ : ZMod K) : CutT 𝓜 𝓛 :=
  ⟨(d₀, σ), mem_cutS_d0 hrot π hk K hd₀ σ⟩

lemma ne_of_val_range {a : ZMod K} (h1 : 1 ≤ a.val) (h2 : a.val + 2 ≤ K) : a ≠ 0 ∧ a ≠ -1 := by
  refine ⟨fun h => by rw [h, ZMod.val_zero] at h1; omega, fun h => ?_⟩
  have := val_add_int a (n := 1) (by omega) (by push_cast; omega)
  rw [h] at this
  push_cast at this
  rw [neg_add_cancel, ZMod.val_zero] at this
  omega

/-- **The parent darts of the perturbed run are tight arcs of the cut of the cover**: for a state
of the perturbed run rooted at the face of `d₀` (a dart leaving `t`), a face `b` other than the
root and a sheet `σ` such that the lift of the path of the tree to `b` from the sheet `σ` stays in
the sheets `1, …, K - 2`, the lift of the parent dart of `b` is tight for the root of `(d₀, σ)` in
the cut with the perturbed lengths. -/
theorem tight_par (hM : M.IsPlane) (hface : M.FaceTrans) (hK : 2 ≤ K) (hKB : K < lexBase F)
    {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) {st : LSt M}
    (hI : LInv c (lexEps D F) (π.p 0) (π.p π.k) st) {d₀ : D} (hd₀ : M.tail d₀ = π.p π.k)
    (hroot : st.T.root = M.face d₀) {b : F} (hb : b ≠ st.T.root) (σ : ZMod K)
    (hrange : ∀ y, st.T.Anc y b → 1 ≤ (σ.val : ℤ) + st.T.psum (pflow π) y ∧
      (σ.val : ℤ) + st.T.psum (pflow π) y + 2 ≤ K) :
    Tight (pieceGraph (cutMap hL) (cutPiece 𝓜 𝓛)
        (pert (cutLen 𝓜 𝓛 (covLen F K c (lexEps D F)))))
      (.inr (rootAt hrot π hk K hd₀ σ))
      (toArc hrot π hk K
        (st.T.par b, σ + ((st.T.psum (pflow π) (st.T.up b) : ℤ) : ZMod K))) := by
  classical
  have hPu : IsUnit (M := M) (s := π.p 0) (t := π.p π.k) (pflow π) :=
    ⟨pflow_antisymm π, div_pflow π, fun d => by
      by_cases hd : d ∈ π.darts
      · obtain ⟨j, hj, rfl | rfl⟩ := π.mem_darts.1 hd
        · rw [pflow_d π hj]
        · rw [pflow_rev_d π hj]; omega
      · rw [pflow_of_not_mem π hd]; omega⟩
  set P := pflow π with hPdef
  set ε := lexEps D F with hεdef
  set ℓ := covLen F K c ε with hℓdef
  set N : ℤ := (Fintype.card F + 1) * ∑ d, ε d + 1 with hNdef
  set T := st.T with hTdef
  have hε0 : ∀ d, 0 ≤ ε d := fun d => lexEps_nonneg d
  have hnn : ∀ e, e ∉ 𝓛 → 0 ≤ ℓ e := fun e _ => covLen_nonneg K hc hε0 e
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
  set z : CutV 𝓜 𝓛 := .inl (b, σ + ((T.psum P b : ℤ) : ZMod K))
  set W := pend :: Wt.map (toArc hrot π hk K) with hW
  have hWw : LWalk G (.inr r) z W :=
    LWalk.cons (G := G) (a := pend) (lwalk_toArc hrot π hk K _ hWtw hWtL)
  -- a shortest walk
  obtain ⟨L0, hL0⟩ := exists_isSP hnn' ⟨W, hWw⟩
  have hnd0 : L0.Nodup := (IsSP.nodup_src hpos hL0).of_map _
  obtain ⟨L1, rfl, hL1⟩ := rootWalk hrot π hk K _ hL0.1
  obtain ⟨hcop, z', hz', hdw⟩ := copyWalk hrot π hk K _ hL1
  have hz'eq : z' = (b, σ + ((T.psum P b : ℤ) : ZMod K)) := by
    have := hz'.symm; simpa [z] using this
  subst hz'eq
  set lt := L1.map fun a => arcProj hrot π hk K a.1 with hlt
  have hltL := arcProj_not_mem hrot π hk K hcop
  have hL1eq := eq_map_toArc hrot π hk K hcop
  set l := lt.map Prod.fst with hl
  have hlw : DWalk M T.root l b := by rw [hroot]; exact dWalk_proj hrot π K hdw
  have hsheet := dWalk_sheet hrot π hk K hdw hltL
  obtain ⟨hb1, hb2⟩ := hrange b (T.anc_self b)
  have hvb := val_add_int σ (n := T.psum P b) (by omega) (by omega)
  have hr2 : ((r : D × ZMod K)).2 = σ := rfl
  rw [hr2] at hsheet
  change _ = _ + dsum P l at hsheet
  have hlev : dsum P l = T.psum P b := by rw [hvb] at hsheet; linarith
  -- the lengths
  have hlen0 : MSSP.wlen G₀ (pend :: L1) = N * dsum c l + dsum ε l := by
    rw [MSSP.wlen_cons, hL1eq, wlen_toArc hrot π hk K ℓ hltL, dsum_covLen]
    simp [G₀, pieceGraph, pend, cutLen, N, l, lt]
  have hlenW : MSSP.wlen G₀ W = N * T.psum c b + T.psum ε b := by
    rw [hW, MSSP.wlen_cons, wlen_toArc hrot π hk K ℓ hWtL, dsum_covLen, hWt, map_fst_liftList,
      T.dsum_tpath, T.dsum_tpath]
    simp [G₀, pieceGraph, pend, cutLen, N]
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
  rw [hPp.wlen_eq, hPp.wlen_eq, hlen0, hlenW] at hcmp
  have hps := hPp.psum_lt hWnd
  have h2c : (0 : ℤ) < 2 ^ Fintype.card (CutD 𝓜 𝓛) := by positivity
  have hcomp : N * dsum c l + dsum ε l ≤ N * T.psum c b + T.psum ε b := by
    by_contra hcon
    push Not at hcon
    have : (2 : ℤ) ^ Fintype.card (CutD 𝓜 𝓛) * (N * T.psum c b + T.psum ε b + 1) ≤
        2 ^ Fintype.card (CutD 𝓜 𝓛) * (N * dsum c l + dsum ε l) :=
      mul_le_mul_of_nonneg_left (by omega) h2c.le
    have : (0 : ℤ) ≤ (psum (fun a => (Fintype.equivFin (CutD 𝓜 𝓛) a.1 : ℕ)) (pend :: L1) : ℤ) :=
      Nat.cast_nonneg _
    have : ((psum (fun a => (Fintype.equivFin (CutD 𝓜 𝓛) a.1 : ℕ)) W : ℕ) : ℤ) <
        2 ^ Fintype.card (CutD 𝓜 𝓛) := by exact_mod_cast hps
    nlinarith
  -- the lexicographic comparison
  obtain ⟨hx1, hx2⟩ := linv_shortest_level hM (p0_ne_pk π hk) hI hPu hlw hlev
  rw [← hTdef] at hx1 hx2
  have hεl : 0 ≤ dsum ε l := dsum_nonneg fun d _ => hε0 d
  have hεb : T.psum ε b < N := by
    have := T.psum_le hε0 b
    have : 0 ≤ ∑ d, ε d := sum_nonneg fun d _ => hε0 d
    simp only [hNdef]; nlinarith
  have hceq : dsum c l = T.psum c b := by
    by_contra hne
    have : T.psum c b + 1 ≤ dsum c l := by omega
    have hN0 : 0 < N := by linarith [T.psum_nonneg hε0 b]
    nlinarith
  have heeq : dsum ε l = T.psum ε b := by
    have := hx2 hceq; rw [hceq] at hcomp; linarith
  -- the same multiset of darts, hence the path of the tree
  have hltnd : lt.Nodup := by
    rw [hL1eq] at hnd0
    have := (List.nodup_cons.1 hnd0).2
    exact this.of_map _
  have hcount : ∀ d, l.count d = tp.count d := by
    refine count_eq_of_dsum_eq (B := lexBase F) (fun d => ?_) (fun d => ?_) ?_
    · exact lt_of_le_of_lt (count_fst_le K hltnd d) hKB
    · have := List.nodup_iff_count_le_one.1 (T.nodup_tpath b) d
      rw [← htp] at this
      have : 1 < lexBase F := by unfold lexBase; omega
      omega
    · exact (show dsum ε l = dsum ε tp by rw [heeq, htp, T.dsum_tpath])
  have hltp : l = tp := T.eq_tpath_of_count hlw hcount
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
    simp only at e
    rw [hlast, T.psum_of_ne P hb] at e
    push_cast at e
    linear_combination e
  have hxe : x = (T.par b, σ + ((T.psum P (T.up b) : ℤ) : ZMod K)) := Prod.ext hlast hx2'
  subst hxe
  rw [toArc_of_not_mem hrot π hk K hx]
  exact tight_of_last hnn' (l := pend :: L2) (by simpa using hL0.1) (by simpa using hL0.2)

end STFlow

end PlanarFlow
