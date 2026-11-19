module

public import PlanarFlow.BKMNW.Headline
public import PlanarFlow.BKMNW.DecA

/-!
# The headline with the decomposition of split functions

`PlanarFlow.BKMNW.maxflow_plane_cost` states that **some** decomposition `τ` meeting `BalDecA`
gives a maximum flow at cost `O(n lg³ n)`. Here the decomposition is **the decomposition of the
split subroutines** (`PlanarFlow.BKMNW.decA`): for every three subroutines meeting `SplitFns` on
the pieces of the recursion of the preprocessed map without loops (pieces meeting `PcOK` and the
invariant `CInv` with the pendant vertices `pendQ`), the algorithm on `decA` is a maximum flow,
at the cost bound of the headline. This is the interface of a separator program: it must answer,
on each piece of the recursion, a split meeting `SplitOK` with the balance of its kind.

* `maxflow_pre_cost_of`, `maxflow_cost_of`: `maxflow_pre_cost` and `maxflow_cost` **for every
  given decomposition meeting `BalDecA`** (the existing statements give an existence);
* `splitFns_cinv`: the subroutines chosen from the existence statements (`spSC`, `spHC`, `smC`)
  meet `SplitFns` for the invariant `CInv` (from `split_size`, `split_hole`, `exists_decOK_small`);
* `decA_balDecA_pre`: on the preprocessed map of a plane map without loops, `decA` of subroutines
  meeting `SplitFns` meets `BalDecA` (`κ = 9`, `η = 6`, `s = 100000`);
* **`maxflow_plane_cost_decA`**: the headline for `τ = decA … univ [] true`, for every
  subroutines meeting `SplitFns` on `lpreMap M`; **`splitFns_lpre`**: such subroutines exist
  (the choices), so that **`maxflow_plane_cost_decAC`** is the headline with one explicit term
  `τ` (no existential), its splits chosen piece by piece.

What is *not* done here: subroutines meeting `SplitFns` as machine programs. The split of a large
piece is the chain `PlanarFlow.BKMNW.split_size` / `split_hole` (core piece map, pruning of the
holes that are cut vertices, Miller's cycle on the stellar subdivision `exists_core_cycle`,
passages through face centres replaced by darts, cut into parts off the holes, classes grouped
into two children); each step is a finite construction, but only Miller's cycle has a machine
program (`PlanarSeparator.MillerProg.millerFull_spec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace BKMNW

open Finset CombMap Orbit Function Equiv Relation PlanarSeparator.StDart

universe w

/-! ### The subroutines chosen by the existence proofs meet `SplitFns` -/

section Cinv

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The chosen subroutines meet `SplitFns` for `CInv`** on a map without loops whose terminals
are among the vertices `Q` of degree one, no dart joining two of them (the hypotheses of
`exists_balDecA_of_cinv`, without the invariant at the root). -/
theorem splitFns_cinv (hloop : ∀ d, M.head d ≠ M.tail d) {S T Q : Finset V} (hSTQ : S ∪ T ⊆ Q)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) :
    SplitFns M S T 9 100000 (CInv M Q) (spSC M S T 9 (CInv M Q)) (spHC M S T 9 (CInv M Q))
      (smC M S T 9 100000) :=
  splitFns_choose (CInv M Q)
    (fun P Hs hP hs ht => exists_decOK_small (by norm_num) (by norm_num) hloop
      (fun t ht => hQdeg t (hSTQ ht)) _ P Hs rfl hP hs ht)
    (fun _ _ hP hI hs ht => split_size hSTQ hloop hQdeg hQ5 hP hI hs ht)
    (fun _ _ hP hI hs ht => split_hole hSTQ hloop hQdeg hQ5 hP hI hs ht)

end Cinv

section Pre

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The pendant vertices of the preprocessed map meet the hypotheses on `Q` of `splitFns_cinv`. -/
lemma pendQ_hyps {hrot : M.RotTrans} {e₀ : V → D} (he₀ : ∀ v, M.tail (e₀ v) = v)
    (S T : Finset V) :
    preTerm (hrot := hrot) S ∪ preTerm (hrot := hrot) T ⊆ pendQ _ ∧
    (∀ q ∈ pendQ _, ∀ d d', (preMap hrot he₀).tail d = q → (preMap hrot he₀).tail d' = q →
      d = d') ∧
    (∀ d, ¬ ((preMap hrot he₀).tail d ∈ pendQ _ ∧ (preMap hrot he₀).head d ∈ pendQ _)) := by
  have he := triE_tail (hrot := hrot) he₀
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    simp only [preTerm, mem_union, mem_image] at hw
    rcases hw with ⟨_, -, rfl⟩ | ⟨_, -, rfl⟩ <;> exact inr_mem_pendQ _
  · intro q hq d d' hd hd'
    obtain ⟨w, -, rfl⟩ := mem_image.1 hq
    rw [(pendant_tail_eq_inr he d w).1 hd, (pendant_tail_eq_inr he d' w).1 hd']
  · rintro d ⟨h1, h2⟩
    obtain ⟨w, -, hw⟩ := mem_image.1 h1
    have hd := (pendant_tail_eq_inr he d w).1 hw.symm
    subst hd
    exact inl_not_mem_pendQ w h2

/-- **The chosen subroutines meet `SplitFns` on the preprocessed map** of a map without loops. -/
theorem splitFns_pre {hrot : M.RotTrans} (hl : ∀ d, M.head d ≠ M.tail d) {e₀ : V → D}
    (he₀ : ∀ v, M.tail (e₀ v) = v) (S T : Finset V) :
    SplitFns (preMap hrot he₀) (preTerm S) (preTerm T) 9 100000 (CInv (preMap hrot he₀) (pendQ _))
      (spSC (preMap hrot he₀) (preTerm S) (preTerm T) 9 (CInv (preMap hrot he₀) (pendQ _)))
      (spHC (preMap hrot he₀) (preTerm S) (preTerm T) 9 (CInv (preMap hrot he₀) (pendQ _)))
      (smC (preMap hrot he₀) (preTerm S) (preTerm T) 9 100000) := by
  obtain ⟨h1, h2, h3⟩ := pendQ_hyps (hrot := hrot) he₀ S T
  exact splitFns_cinv (preMap_loopless hl he₀) h1 h2 h3

/-- **`BalDecA` for the decomposition of split functions on the preprocessed map**: on a plane map
without loops with transitive rotations and faces, for subroutines meeting `SplitFns` with the
invariant `CInv` (pendant vertices `pendQ`), `decA` from the whole map meets `BalDecA` with
`κ = 9`, `η = 6`, `s = 100000`. -/
theorem decA_balDecA_pre (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (hl : ∀ d, M.head d ≠ M.tail d) {e₀ : V → D} (he₀ : ∀ v, M.tail (e₀ v) = v) {S T : Finset V}
    {spS spH : Finset _ → List (Finset _) → SplitAns (preMap hrot he₀)}
    {sm : Finset _ → List (Finset _) → ADec (preMap hrot he₀)}
    (hF : SplitFns (preMap hrot he₀) (preTerm S) (preTerm T) 9 100000 (CInv (preMap hrot he₀) (pendQ _))
      spS spH sm) :
    BalDecA (preMap hrot he₀) (preTerm S) (preTerm T) 9 6 100000
      (decA (preMap hrot he₀) spS spH sm 100000 univ [] true) := by
  have : Nonempty D := ⟨e₀ hM.nonempty.some⟩
  have hP := triMap_isPlane hM hrot hface
  have he := triE_tail (hrot := hrot) he₀
  exact decA_balDecA (CombMap.pendant_isPlane he hP)
    (CombMap.pendant_rotTrans he (triMap_rotTrans hrot))
    (CombMap.pendant_faceTrans he (triMap_faceTrans hrot)) hF
    (cinv_pendant he hP (triMap_rotTrans hrot) (triMap_faceTrans hrot)
      fun d => (triMap_isTriangle hrot hl d).φ_three)

/-- **`maxflow_pre_cost` for a given decomposition**: on a plane map without loops with transitive
rotations and faces, nonnegative capacities and disjoint terminals, for **every** decomposition
`τ` of the preprocessed map meeting `BalDecA` (`κ = 9`, `η = 6`, `s = 100000`), the algorithm
`runL` on it restricted to the darts of `M` is a maximum flow, at the cost bound of
`maxflow_pre_cost`. -/
theorem maxflow_pre_cost_of (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V}
    (hST : Disjoint S T) {e₀ : V → D} (he₀ : ∀ v, M.tail (e₀ v) = v)
    {O : PlaneOracles.{w}} (hO : O.Spec) {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    {τ : ADec (preMap hrot he₀)}
    (hτ : BalDecA (preMap hrot he₀) (preTerm S) (preTerm T) 9 6 100000 τ) :
    IsMax M u S T (fun d =>
        runL (preMap hrot he₀) (preCap u S T) τ O (preTerm S) (preTerm T) (.inl (old d))) ∧
      runLCost (preMap hrot he₀) c τ ≤ (100000 + 11) ^ 2 * ((27 * ((6 + 1) * (25 + 7 * 9 ^ 2 +
        2 * 6 * (34 + 14 * 9 ^ 2))) + 25) * K * (7 * Fintype.card D) *
          lg (7 * Fintype.card D) ^ 3 + K₀ * (7 * Fintype.card D) * lg (7 * Fintype.card D)) := by
  have : Nonempty D := ⟨e₀ hM.nonempty.some⟩
  have hP := triMap_isPlane hM hrot hface
  have he := triE_tail (hrot := hrot) he₀
  have hcard := (card_preMap_darts (hrot := hrot) hM hface he₀).2
  have hpos : 0 < Fintype.card (PlanarSeparator.StDart D ⊕ ((V ⊕ (M.toSep hrot).Face) × Bool)) :=
    Fintype.card_pos_iff.2 ⟨Sum.inl (old (Classical.arbitrary D))⟩
  obtain ⟨h1, h2⟩ := runL_isMax_costA (CombMap.pendant_isPlane he hP)
    (CombMap.pendant_rotTrans he (triMap_rotTrans hrot))
    (CombMap.pendant_faceTrans he (triMap_faceTrans hrot))
    (pendCap_nonneg (triCap_nonneg hu) _ _ (sum_nonneg fun x _ => triCap_nonneg hu x))
    ((disjoint_image Sum.inr_injective).2 ((disjoint_image Sum.inl_injective).2 hST)) hτ hO hc
    hpos
  refine ⟨isMax_restrict (triMap_embeds hrot) (fun _ => rfl) (triCap_out u)
    (isMax_pendant he (triCap_nonneg hu) h1), h2.trans ?_⟩
  have hlg := lg_mono hcard
  gcongr

end Pre

section Loops

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- A decomposition meeting `BalDecA` of a map without darts is the leaf of the whole map. -/
lemma eq_leaf_of_balDecA {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V']
    [DecidableEq V'] [Fintype F'] [DecidableEq F'] {N : CombMap D' V' F'} [IsEmpty D']
    {S T : Finset V'} {κ η s : ℕ} {τ : ADec N} (hτ : BalDecA N S T κ η s τ) :
    τ = .leaf univ := by
  cases τ with
  | leaf Q => rw [show Q = univ from hτ.1]
  | node l r π =>
    exfalso
    obtain ⟨-, h2, -⟩ := hτ.2.2.2.2
    obtain ⟨x, -⟩ := card_pos.1 h2
    exact isEmptyElim x

/-- **`maxflow_cost` for a given decomposition**: on every plane map with transitive rotations
and faces (loops allowed), nonnegative capacities and disjoint terminals, for **every**
decomposition `τ` of `lpreMap M` meeting `BalDecA` (`κ = 9`, `η = 6`, `s = 100000`), `nlRun` is
a maximum flow of `M`, at the cost bound of `maxflow_cost`. -/
theorem maxflow_cost_of (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {O : PlaneOracles.{w}} (hO : O.Spec) {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    {τ : ADec (lpreMap M)}
    (hτ : BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ) :
    IsMax M u S T (nlRun M u S T τ O) ∧
      runLCost (lpreMap M) c τ ≤ (100000 + 11) ^ 2 * ((27 * ((6 + 1) * (25 + 7 * 9 ^ 2 +
        2 * 6 * (34 + 14 * 9 ^ 2))) + 25) * K * (7 * Fintype.card D) *
          lg (7 * Fintype.card D) ^ 3 + K₀ * (7 * Fintype.card D) * lg (7 * Fintype.card D)) := by
  have hST' : Disjoint (nlTerm M S) (nlTerm M T) := by
    rw [disjoint_left]
    intro w h1 h2
    simp only [nlTerm, mem_filter, mem_univ, true_and] at h1 h2
    exact disjoint_left.1 hST h1 h2
  have hcard : Fintype.card (SDart (nlDarts M)) ≤ Fintype.card D := by
    rw [Fintype.card_coe]; exact card_le_univ _
  by_cases hB : (nlDarts M).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hB
    obtain ⟨h1, h2⟩ := maxflow_pre_cost_of (nlMap_isPlane hM hrot hface hx₀) nlMap_rotTrans
      nlMap_faceTrans (u := fun x => u x.1) (fun x => hu x.1) hST' nlE_tail hO hc hτ
    exact ⟨isMax_nlExt hrot hu h1, h2.trans (lg_le_of_le hcard K K₀ _)⟩
  · -- every dart is a loop: the preprocessed map is empty
    rw [not_nonempty_iff_eq_empty] at hB
    have hD0 : Fintype.card (SDart (nlDarts M)) = 0 := by rw [Fintype.card_coe, hB]; rfl
    have : IsEmpty (SDart (nlDarts M)) := Fintype.card_eq_zero_iff.1 hD0
    have hV0 : Fintype.card (SVert (nlRot M) (nlDarts M)) = 0 :=
      le_zero_iff.1 (hD0 ▸ Fintype.card_le_of_surjective (nlMap M).tail
        fun w => ⟨nlE M w, nlE_tail w⟩)
    have hF0 : Fintype.card ((nlMap M).toSep nlMap_rotTrans).Face = 0 :=
      le_zero_iff.1 (hD0 ▸ Fintype.card_le_of_surjective _
        ((nlMap M).toSep nlMap_rotTrans).face_surjective)
    have hS0 : Fintype.card (PlanarSeparator.StDart (SDart (nlDarts M))) = 0 := by
      rw [card_triMap_darts, hD0]
    have hG0 : Fintype.card ((nlMap M).toSep nlMap_rotTrans).stellar.Face = 0 :=
      le_zero_iff.1 (hS0 ▸ Fintype.card_le_of_surjective _
        ((nlMap M).toSep nlMap_rotTrans).stellar.face_surjective)
    have hP0 : Fintype.card (PlanarSeparator.StDart (SDart (nlDarts M)) ⊕
        ((SVert (nlRot M) (nlDarts M) ⊕ ((nlMap M).toSep nlMap_rotTrans).Face) × Bool)) = 0 := by
      simp only [Fintype.card_sum, Fintype.card_prod, hS0, hV0, hF0, zero_add, zero_mul]
    have : IsEmpty (PlanarSeparator.StDart (SDart (nlDarts M)) ⊕
        ((SVert (nlRot M) (nlDarts M) ⊕ ((nlMap M).toSep nlMap_rotTrans).Face) × Bool)) :=
      Fintype.card_eq_zero_iff.1 hP0
    obtain rfl := eq_leaf_of_balDecA hτ
    refine ⟨isMax_nlExt hrot hu (isMax_of_isEmpty _ _ _ _), ?_⟩
    have hmap : mapSize (lpreMap M) = 0 := by
      unfold mapSize
      simp only [Fintype.card_sum, hP0, hV0, hF0, hG0]
    have h1 := hc.leaf (pdarts (lpreMap M) univ []).card
    have h2 := hc.lin 0
    have h3 : (pdarts (lpreMap M) univ []).card = 0 :=
      le_zero_iff.1 ((card_le_univ _).trans hP0.le)
    unfold runLCost arunLCost
    rw [h3] at h1
    rw [h3, hmap, card_univ, hP0]
    simp only [List.length_nil, add_zero, mul_zero] at h1 h2 ⊢
    omega

/-- **`BalDecA` for the decomposition of split functions on `lpreMap M`**, for every plane map
with transitive rotations and faces (loops allowed): subroutines meeting `SplitFns` on the
pieces of the recursion (`PcOK`, `CInv` with the pendant vertices) give a decomposition meeting
`BalDecA`; on a map all of whose darts are loops the preprocessed map is empty and `decA` is the
small decomposition `sm` of the empty piece. -/
theorem decA_balDecA_lpre (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {S T : Finset V} {spS spH : Finset _ → List (Finset _) → SplitAns (lpreMap M)}
    {sm : Finset _ → List (Finset _) → ADec (lpreMap M)}
    (hF : SplitFns (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 100000
      (CInv (lpreMap M) (pendQ _)) spS spH sm) :
    BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000
      (decA (lpreMap M) spS spH sm 100000 univ [] true) := by
  by_cases hB : (nlDarts M).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hB
    exact decA_balDecA_pre (nlMap_isPlane hM hrot hface hx₀) nlMap_rotTrans nlMap_faceTrans
      nlMap_loopless nlE_tail hF
  · rw [not_nonempty_iff_eq_empty] at hB
    have hD0 : Fintype.card (SDart (nlDarts M)) = 0 := by rw [Fintype.card_coe, hB]; rfl
    have : IsEmpty (SDart (nlDarts M)) := Fintype.card_eq_zero_iff.1 hD0
    have hV0 : Fintype.card (SVert (nlRot M) (nlDarts M)) = 0 :=
      le_zero_iff.1 (hD0 ▸ Fintype.card_le_of_surjective (nlMap M).tail
        fun w => ⟨nlE M w, nlE_tail w⟩)
    have hF0 : Fintype.card ((nlMap M).toSep nlMap_rotTrans).Face = 0 :=
      le_zero_iff.1 (hD0 ▸ Fintype.card_le_of_surjective _
        ((nlMap M).toSep nlMap_rotTrans).face_surjective)
    have hS0 : Fintype.card (PlanarSeparator.StDart (SDart (nlDarts M))) = 0 := by
      rw [card_triMap_darts, hD0]
    have hP0 : Fintype.card (PlanarSeparator.StDart (SDart (nlDarts M)) ⊕
        ((SVert (nlRot M) (nlDarts M) ⊕ ((nlMap M).toSep nlMap_rotTrans).Face) × Bool)) = 0 := by
      simp only [Fintype.card_sum, Fintype.card_prod, hS0, hV0, hF0, zero_add, zero_mul]
    have : IsEmpty (PlanarSeparator.StDart (SDart (nlDarts M)) ⊕
        ((SVert (nlRot M) (nlDarts M) ⊕ ((nlMap M).toSep nlMap_rotTrans).Face) × Bool)) :=
      Fintype.card_eq_zero_iff.1 hP0
    exact decA_balDecA_of_isEmpty hF

/-- **The chosen subroutines meet `SplitFns` on `lpreMap M`**, for every map. -/
theorem splitFns_lpre (S T : Finset V) :
    SplitFns (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 100000
      (CInv (lpreMap M) (pendQ _))
      (spSC (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9
        (CInv (lpreMap M) (pendQ _)))
      (spHC (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9
        (CInv (lpreMap M) (pendQ _)))
      (smC (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 100000) :=
  splitFns_pre nlMap_loopless nlE_tail _ _

end Loops

/-! ### The headline -/

section Main

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **Maximum flow in plane graphs in `O(n log³ n)` on the decomposition of split
subroutines**: on every plane map with transitive rotations and faces, with `n` darts (loops
allowed), nonnegative capacities and disjoint sources and sinks, for **every** three subroutines
`spS`, `spH`, `sm` meeting `SplitFns` on the pieces of the recursion of the preprocessed map
without loops (`PcOK` and `CInv` with the pendant vertices; `κ = 9`, `s = 100000`), the
decomposition `τ = decA (lpreMap M) spS spH sm 100000 univ [] true` meets `BalDecA` (`η = 6`),
the algorithm with the planar subroutines `planeOracles` on it (`nlRun`) computes a maximum flow
of `M`, at a cost at most `C K n lg³ n + C₀ K₀ n lg n` for every family of subroutine costs
meeting `SubCosts.Bounds K K₀`, with `C = (s + 11)² · 448 · (27 · 102256 + 25)` and
`C₀ = (s + 11)² · 28` (the constants of `maxflow_plane_cost`). -/
theorem maxflow_plane_cost_decA (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {spS spH : Finset _ → List (Finset _) → SplitAns (lpreMap M)}
    {sm : Finset _ → List (Finset _) → ADec (lpreMap M)}
    (hF : SplitFns (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 100000
      (CInv (lpreMap M) (pendQ _)) spS spH sm) {c : SubCosts} {K K₀ : ℕ}
    (hc : c.Bounds K K₀) :
    BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000
        (decA (lpreMap M) spS spH sm 100000 univ [] true) ∧
      IsMax M u S T (nlRun M u S T (decA (lpreMap M) spS spH sm 100000 univ [] true)
        (planeOracles fun X => frRef X)) ∧
      runLCost (lpreMap M) c (decA (lpreMap M) spS spH sm 100000 univ [] true) ≤
        (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) := by
  have hτ := decA_balDecA_lpre hM hrot hface hF
  obtain ⟨h1, h2⟩ := maxflow_cost_of hM hrot hface hu hST
    (planeOracles_spec _ fun X => frRef_spec X) hc hτ
  exact ⟨hτ, h1, h2.trans (cost_bound_le K K₀ _)⟩

/-- **The headline with one explicit decomposition**: `maxflow_plane_cost_decA` for the
subroutines chosen piece by piece from the existence proofs (`spSC`, `spHC`, `smC`), which meet
`SplitFns` on every map (`splitFns_lpre`). Unlike `maxflow_plane_cost` (an existential `∃ τ`), the
decomposition is the term `decA (lpreMap M) spSC spHC smC 100000 univ [] true`; its splits are
still chosen by `Classical.choose`, piece by piece, not computed by a program. -/
theorem maxflow_plane_cost_decAC (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) {c : SubCosts}
    {K K₀ : ℕ} (hc : c.Bounds K K₀) :
    let τ := decA (lpreMap M)
      (spSC (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9
        (CInv (lpreMap M) (pendQ _)))
      (spHC (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9
        (CInv (lpreMap M) (pendQ _)))
      (smC (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 100000) 100000 univ [] true
    BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) ∧
      runLCost (lpreMap M) c τ ≤
        (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) :=
  maxflow_plane_cost_decA hM hrot hface hu hST (splitFns_lpre S T) hc

end Main

end BKMNW

end PlanarFlow
