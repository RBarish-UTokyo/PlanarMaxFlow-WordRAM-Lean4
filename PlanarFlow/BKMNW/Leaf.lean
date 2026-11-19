module

public import PlanarFlow.BKMNW.Algorithm

/-!
# The leaves of the recursion

The recursion of Algorithm 1 (Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen, SIAM J.
Comput. 46(4), 2017) stops at pieces of constant size. Here the leaves are pieces of at most one
edge (at most two darts), and the leaf solver (`leafSolve`) decides the flow dart by dart: rank the
sources `0`, the holes `1`, the sinks `2`; on a dart between two ranked vertices, saturate it if
it goes up in rank, saturate its reverse if it goes down, and put no flow on the other darts.
The work is constant per dart.

`leafSolve_spec`: on a piece of at most one edge, with nonnegative capacities, the result meets
the specification `MSOut` of the recursion: the vertices of other ranks carry no flow, so they are
balanced, and from a vertex only the other end of the edge can be reached, and only if it does
not have a higher rank.

`leafSolve_spec_ranked`: the same on a piece of **any size all of whose vertices are sources,
sinks or holes**: a residual dart of such a piece never goes up in rank, so the vertices of rank
at most `i` form a closed set. These are the leaves of the decompositions in which every vertex
that is not a terminal has become a hole (`PlanarFlow/BKMNW/Chain.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable {M : CombMap D V F}

/-- The rank of a vertex: `0` for the sources, `1` for the holes, `2` for the sinks, `3` for the
other vertices. -/
def lrk (S T A : Finset V) (v : V) : ℕ :=
  if v ∈ S then 0 else if v ∈ A then 1 else if v ∈ T then 2 else 3

lemma lrk_le (S T A : Finset V) (v : V) : lrk S T A v ≤ 3 := by
  unfold lrk; split_ifs <;> omega

variable (M) in
/-- **The leaf solver.** -/
def leafSolve (U : D → ℤ) (S T A : Finset V) (d : D) : ℤ :=
  if lrk S T A (M.tail d) < 3 ∧ lrk S T A (M.head d) < 3 then
    (if lrk S T A (M.tail d) < lrk S T A (M.head d) then U d
      else if lrk S T A (M.head d) < lrk S T A (M.tail d) then - U (M.rev d) else 0)
  else 0

lemma leafSolve_antisymm (U : D → ℤ) (S T A : Finset V) :
    M.IsAntisymm (leafSolve M U S T A) := by
  intro d
  simp only [leafSolve, CombMap.tail_rev, CombMap.head_rev, M.rev_rev]
  split_ifs <;> first | rfl | omega

lemma leafSolve_le (U : D → ℤ) (hU : ∀ d, 0 ≤ U d) (S T A : Finset V) (d : D) :
    leafSolve M U S T A d ≤ U d := by
  have := hU d; have := hU (M.rev d)
  simp only [leafSolve]
  split_ifs <;> omega

/-- The other darts of the map carry nothing. -/
lemma leafSolve_zero {u : D → ℤ} {Q : Finset D} (hQ : RevClosed M Q) {S T A : Finset V} {d : D}
    (hd : d ∉ Q) : leafSolve M (capOn u Q) S T A d = 0 := by
  have hr : M.rev d ∉ Q := fun h => hd (by simpa [M.rev_rev] using hQ _ h)
  simp only [leafSolve, capOn, hd, hr, ite_false, neg_zero]
  split_ifs <;> rfl

/-- **No residual path from a rank to a higher rank** in a piece of at most one edge. -/
lemma leaf_noPath {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {Q : Finset D} (hQ : RevClosed M Q)
    (hQ2 : Q.card ≤ 2) {S T A : Finset V} {X Z : Finset V} {i j : ℕ} (hij : i < j) (hj : j < 3)
    (hX : ∀ x ∈ X, lrk S T A x = i) (hZ : ∀ z ∈ Z, lrk S T A z = j) :
    NoPath M (capOn u Q) (leafSolve M (capOn u Q) S T A) X Z := by
  classical
  -- the endpoints of the darts of the piece
  have hpair : ∀ x ∈ Q, ∀ y ∈ Q, x = y ∨ x = M.rev y := by
    intro x hx y hy
    by_contra h
    push Not at h
    have hsub : ({x, y, M.rev y} : Finset D) ⊆ Q := by
      intro z hz; simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hQ _ hy
    have := card_le_card hsub
    rw [card_insert_of_notMem (by simp [h.1, h.2]), card_insert_of_notMem (by simp [(M.rev_ne y).symm]),
      card_singleton] at this
    omega
  have hres : ∀ x, leafSolve M (capOn u Q) S T A x < capOn u Q x → x ∈ Q := by
    intro x hx; by_contra h
    rw [leafSolve_zero hQ h] at hx; simp [capOn, h] at hx
  -- the vertices reached in one residual step
  let N : Finset V := univ.filter fun v => ∃ x ∈ Q, M.tail x ∈ X ∧ M.head x = v ∧
    leafSolve M (capOn u Q) S T A x < capOn u Q x
  refine ⟨X ∪ N, subset_union_left, ?_, fun d hd1 hd2 => ?_⟩
  · rw [disjoint_union_left]
    refine ⟨disjoint_left.2 fun v hvX hvZ => by have := hX v hvX; have := hZ v hvZ; omega, ?_⟩
    rw [disjoint_left]
    intro v hv hvZ
    simp only [N, mem_filter, mem_univ, true_and] at hv
    obtain ⟨x, hxQ, hx1, rfl, hx2⟩ := hv
    have h1 := hX _ hx1; have h2 := hZ _ hvZ
    simp only [leafSolve, h1, h2, show i < 3 by omega, hj, and_self, ite_true, hij] at hx2
    omega
  · by_contra hne
    have hlt : leafSolve M (capOn u Q) S T A d < capOn u Q d :=
      lt_of_le_of_ne (leafSolve_le _ (fun d => by unfold capOn; split_ifs <;> simp [hu]) S T A d)
        hne
    have hdQ := hres d hlt
    rw [mem_union] at hd1 hd2
    push Not at hd2
    rcases hd1 with h | h
    · exact hd2.2 (by simp only [N, mem_filter, mem_univ, true_and]; exact ⟨d, hdQ, h, rfl, hlt⟩)
    · simp only [N, mem_filter, mem_univ, true_and] at h
      obtain ⟨x, hxQ, hx1, hx2, -⟩ := h
      rcases hpair d hdQ x hxQ with rfl | rfl
      · exact hd2.2 (by simp only [N, mem_filter, mem_univ, true_and]; exact ⟨d, hdQ, hx1, rfl, hlt⟩)
      · apply hd2.1
        simp only [CombMap.head_rev]
        exact hx1

/-- **The leaf solver meets the specification of the recursion** on a piece of at most one
edge. -/
theorem leafSolve_spec {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {Q : Finset D} (hQ : RevClosed M Q)
    (hQ2 : Q.card ≤ 2) {S T A : Finset V} (hST : Disjoint S T) (hSA : Disjoint S A)
    (hTA : Disjoint T A) : MSOut M (capOn u Q) S T A (leafSolve M (capOn u Q) S T A) := by
  have hrS : ∀ v ∈ S, lrk S T A v = 0 := fun v hv => by simp [lrk, hv]
  have hrA : ∀ v ∈ A, lrk S T A v = 1 := fun v hv => by
    simp [lrk, hv, disjoint_right.1 hSA hv]
  have hrT : ∀ v ∈ T, lrk S T A v = 2 := fun v hv => by
    simp [lrk, hv, disjoint_right.1 hST hv, disjoint_left.1 hTA hv]
  refine ⟨⟨leafSolve_antisymm _ S T A, leafSolve_le _ (fun d => by
      unfold capOn; split_ifs <;> simp [hu]) S T A⟩, fun v h1 h2 h3 => ?_,
    leaf_noPath hu hQ hQ2 (by omega : 0 < 2) (by omega) hrS hrT,
    leaf_noPath hu hQ hQ2 (by omega : 0 < 1) (by omega) hrS hrA,
    leaf_noPath hu hQ hQ2 (by omega : 1 < 2) (by omega) hrA hrT⟩
  have hv : lrk S T A v = 3 := by simp [lrk, h1, h2, h3]
  refine sum_eq_zero fun d hd => ?_
  simp only [mem_filter, mem_univ, true_and] at hd
  simp [leafSolve, hd, hv]

lemma lrk_lt_three {S T A : Finset V} {v : V} (h : v ∈ S ∪ T ∪ A) : lrk S T A v < 3 := by
  simp only [mem_union] at h
  unfold lrk; split_ifs <;> first | omega | tauto

/-- **No residual path from a rank to a higher rank** in a piece of any size all of whose vertices
are ranked: a residual dart of the piece never goes up in rank. -/
lemma leaf_noPath_ranked {u : D → ℤ} {Q : Finset D} (hQ : RevClosed M Q)
    {S T A : Finset V} (hall : ∀ d ∈ Q, lrk S T A (M.tail d) < 3) {X Z : Finset V} {i j : ℕ}
    (hij : i < j) (hX : ∀ x ∈ X, lrk S T A x = i) (hZ : ∀ z ∈ Z, lrk S T A z = j) :
    NoPath M (capOn u Q) (leafSolve M (capOn u Q) S T A) X Z := by
  classical
  refine ⟨univ.filter fun v => lrk S T A v ≤ i, fun x hx => by simp [hX x hx],
    disjoint_left.2 fun v hv hvZ => by simp only [mem_filter] at hv; have := hZ v hvZ; omega,
    fun d hd1 hd2 => ?_⟩
  simp only [mem_filter, mem_univ, true_and, not_le] at hd1 hd2
  by_cases hdQ : d ∈ Q
  · have h1 := hall d hdQ
    have h2 := hall _ (hQ d hdQ)
    rw [tail_rev] at h2
    simp only [leafSolve, h1, h2, and_self, ite_true, show lrk S T A (M.tail d) <
      lrk S T A (M.head d) by omega]
  · rw [leafSolve_zero hQ hdQ]; simp [capOn, hdQ]

/-- **The leaf solver meets the specification of the recursion on a piece of any size all of
whose vertices are sources, sinks or holes.** -/
theorem leafSolve_spec_ranked {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {Q : Finset D}
    (hQ : RevClosed M Q) {S T A : Finset V} (hall : ∀ d ∈ Q, M.tail d ∈ S ∪ T ∪ A)
    (hST : Disjoint S T) (hSA : Disjoint S A) (hTA : Disjoint T A) :
    MSOut M (capOn u Q) S T A (leafSolve M (capOn u Q) S T A) := by
  have hrS : ∀ v ∈ S, lrk S T A v = 0 := fun v hv => by simp [lrk, hv]
  have hrA : ∀ v ∈ A, lrk S T A v = 1 := fun v hv => by
    simp [lrk, hv, disjoint_right.1 hSA hv]
  have hrT : ∀ v ∈ T, lrk S T A v = 2 := fun v hv => by
    simp [lrk, hv, disjoint_right.1 hST hv, disjoint_left.1 hTA hv]
  have hall' : ∀ d ∈ Q, lrk S T A (M.tail d) < 3 := fun d hd => lrk_lt_three (hall d hd)
  refine ⟨⟨leafSolve_antisymm _ S T A, leafSolve_le _ (fun d => by
      unfold capOn; split_ifs <;> simp [hu]) S T A⟩, fun v h1 h2 h3 => ?_,
    leaf_noPath_ranked hQ hall' (by omega : 0 < 2) hrS hrT,
    leaf_noPath_ranked hQ hall' (by omega : 0 < 1) hrS hrA,
    leaf_noPath_ranked hQ hall' (by omega : 1 < 2) hrA hrT⟩
  have hv : lrk S T A v = 3 := by simp [lrk, h1, h2, h3]
  refine sum_eq_zero fun d hd => ?_
  simp only [mem_filter, mem_univ, true_and] at hd
  simp [leafSolve, hd, hv]

end BKMNW

end PlanarFlow
