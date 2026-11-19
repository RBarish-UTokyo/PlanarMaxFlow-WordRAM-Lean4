module

public import PlanarFlow.BKMNW.ExistRoot

/-!
# Balanced decompositions of the preprocessed map

The preprocessed map `preMap` (the triangulation `triMap` with a pendant edge at every vertex, the
terminals replaced by their pendant neighbours) of a plane map without loops with transitive
rotations and faces has a decomposition meeting `BalDecA` with the constants `κ = 9`, `η = 6`
and `s = 100000`, independent of the map (`exists_balDecA_pre`). So the cost bound of the
algorithm `runL` holds without hypothesis on decompositions (`maxflow_pre_cost`): it computes a
maximum flow of the map, at a cost `O(n lg³ n)` in the number `n` of its darts, for subroutine
costs meeting `SubCosts.Bounds`. The hypothesis that the map has no loop is removed in
`PlanarFlow.BKMNW.maxflow_cost` (`PlanarFlow/BKMNW/Loops.lean`), which deletes the loops first;
the headline, with the planar subroutines `planeOracles` and the constants in closed form, is
`PlanarFlow.BKMNW.maxflow_plane_cost` (`PlanarFlow/BKMNW/Headline.lean`). Correctness is
unconditional; the cost bound holds in the abstract subroutine-cost model, for every family of
subroutine costs meeting `SubCosts.Bounds`, which machine implementations have yet to meet.

The decompositions are built in `PlanarFlow.BKMNW.Exist` and the files after it: the large pieces
are split by Miller's theorem on the stellar subdivision of the piece map of their core (the darts
with no end at a pendant vertex), the holes that are cut vertices pruned first; with weight on the
holes when the piece touches six holes (`split_hole`), on the darts otherwise (`split_size`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap PlanarSeparator.StDart

universe w

section Pre

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The triangulated map has no loop when `M` has none. -/
lemma triMap_loopless (hrot : M.RotTrans) (hl : ∀ d, M.head d ≠ M.tail d)
    (x : PlanarSeparator.StDart D) : (M.triMap hrot).head x ≠ (M.triMap hrot).tail x := by
  cases x with
  | old d =>
    show (Sum.inl (M.head d) : V ⊕ (M.toSep hrot).Face) ≠ Sum.inl (M.tail d)
    exact fun h => hl d (Sum.inl.inj h)
  | up d =>
    show (Sum.inr ((M.toSep hrot).face d) : V ⊕ (M.toSep hrot).Face) ≠ Sum.inl (M.tail d)
    simp
  | down d =>
    show (Sum.inl (M.tail d) : V ⊕ (M.toSep hrot).Face) ≠ Sum.inr ((M.toSep hrot).face d)
    simp

/-- The preprocessed map has no loop when `M` has none. -/
lemma preMap_loopless {hrot : M.RotTrans} (hl : ∀ d, M.head d ≠ M.tail d) {e₀ : V → D}
    (he₀ : ∀ v, M.tail (e₀ v) = v) (x : PlanarSeparator.StDart D ⊕
      ((V ⊕ (M.toSep hrot).Face) × Bool)) :
    (preMap hrot he₀).head x ≠ (preMap hrot he₀).tail x := by
  rcases x with t | ⟨w, _ | _⟩
  · exact fun h => triMap_loopless hrot hl t (Sum.inl.inj h)
  · exact fun h => by cases h
  · exact fun h => by cases h

/-- **Balanced decompositions of the preprocessed map**: on a plane map without loops with
transitive rotations and faces, the preprocessed map has a decomposition meeting `BalDecA` with
`κ = 9`, `η = 6` and `s = 100000`, for any terminals. -/
theorem exists_balDecA_pre (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (hl : ∀ d, M.head d ≠ M.tail d) {e₀ : V → D} (he₀ : ∀ v, M.tail (e₀ v) = v)
    (S T : Finset V) :
    ∃ τ : ADec (preMap hrot he₀), BalDecA (preMap hrot he₀) (preTerm S) (preTerm T) 9 6 100000 τ
    := by
  have : Nonempty D := ⟨e₀ hM.nonempty.some⟩
  have hP := triMap_isPlane hM hrot hface
  have he := triE_tail (hrot := hrot) he₀
  refine exists_balDecA_of_cinv (Q := pendQ _) (CombMap.pendant_isPlane he hP)
    (CombMap.pendant_rotTrans he (triMap_rotTrans hrot))
    (CombMap.pendant_faceTrans he (triMap_faceTrans hrot)) (preMap_loopless hl he₀) ?_ ?_ ?_
    (cinv_pendant he hP (triMap_rotTrans hrot) (triMap_faceTrans hrot)
      fun d => (triMap_isTriangle hrot hl d).φ_three)
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

/-- **Maximum flow through the preprocessing at cost `O(n lg³ n)`, unconditionally**: on a plane
map without loops with transitive rotations and faces, with `n` darts, nonnegative capacities and
disjoint sources and sinks, there is a decomposition `τ` of the preprocessed map meeting
`BalDecA` (with `κ = 9`, `η = 6`, `s = 100000`) such that the algorithm `runL` on it, restricted to
the darts of `M`, is a maximum flow of `M`, and its cost for subroutine costs meeting
`SubCosts.Bounds K K₀` is at most
`(s + 11)² ((27 Cₙ + 25) K (7 n) lg³ (7 n) + K₀ (7 n) lg (7 n))`,
`Cₙ = (η + 1) (25 + 7 κ² + 2 η (34 + 14 κ²))`. -/
theorem maxflow_pre_cost (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (hl : ∀ d, M.head d ≠ M.tail d) {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V}
    (hST : Disjoint S T) {e₀ : V → D} (he₀ : ∀ v, M.tail (e₀ v) = v)
    {O : PlaneOracles.{w}} (hO : O.Spec) {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀) :
    ∃ τ : ADec (preMap hrot he₀),
      BalDecA (preMap hrot he₀) (preTerm S) (preTerm T) 9 6 100000 τ ∧
      IsMax M u S T (fun d =>
        runL (preMap hrot he₀) (preCap u S T) τ O (preTerm S) (preTerm T) (.inl (old d))) ∧
      runLCost (preMap hrot he₀) c τ ≤ (100000 + 11) ^ 2 * ((27 * ((6 + 1) * (25 + 7 * 9 ^ 2 +
        2 * 6 * (34 + 14 * 9 ^ 2))) + 25) * K * (7 * Fintype.card D) *
          lg (7 * Fintype.card D) ^ 3 + K₀ * (7 * Fintype.card D) * lg (7 * Fintype.card D)) := by
  have : Nonempty D := ⟨e₀ hM.nonempty.some⟩
  have hP := triMap_isPlane hM hrot hface
  have he := triE_tail (hrot := hrot) he₀
  obtain ⟨τ, hτ⟩ := exists_balDecA_pre hM hrot hface hl he₀ S T
  have hcard := (card_preMap_darts (hrot := hrot) hM hface he₀).2
  have hpos : 0 < Fintype.card (PlanarSeparator.StDart D ⊕ ((V ⊕ (M.toSep hrot).Face) × Bool)) :=
    Fintype.card_pos_iff.2 ⟨Sum.inl (old (Classical.arbitrary D))⟩
  obtain ⟨h1, h2⟩ := runL_isMax_costA (CombMap.pendant_isPlane he hP)
    (CombMap.pendant_rotTrans he (triMap_rotTrans hrot))
    (CombMap.pendant_faceTrans he (triMap_faceTrans hrot))
    (pendCap_nonneg (triCap_nonneg hu) _ _ (sum_nonneg fun x _ => triCap_nonneg hu x))
    ((disjoint_image Sum.inr_injective).2 ((disjoint_image Sum.inl_injective).2 hST)) hτ hO hc
    hpos
  refine ⟨τ, hτ, isMax_restrict (triMap_embeds hrot) (fun _ => rfl) (triCap_out u)
    (isMax_pendant he (triCap_nonneg hu) h1), h2.trans ?_⟩
  have hlg := lg_mono hcard
  gcongr

end Pre

/-- **The hypotheses of `exists_balDecA_pre` and `maxflow_pre_cost` can be met**: the map of a
single edge is plane, without loops, with transitive rotations and faces and a dart at every
vertex. -/
theorem exists_balDecA_pre_hyps : (CombMap.ofRotation edgeRot).IsPlane ∧
    (CombMap.ofRotation edgeRot).RotTrans ∧ (CombMap.ofRotation edgeRot).FaceTrans ∧
    (∀ d, (CombMap.ofRotation edgeRot).head d ≠ (CombMap.ofRotation edgeRot).tail d) ∧
    ∃ e : Fin 2 → (⊤ : SimpleGraph (Fin 2)).Dart,
      ∀ v, (CombMap.ofRotation edgeRot).tail (e v) = v := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ofRotation_edgeRot_hyps
  refine ⟨h1, h2, h3, fun d h => ?_, h5⟩
  have := h4 d
  rw [h] at this
  exact iff_not_self this

end BKMNW

end PlanarFlow
