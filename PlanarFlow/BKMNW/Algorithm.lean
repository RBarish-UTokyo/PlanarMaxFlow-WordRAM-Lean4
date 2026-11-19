module

public import PlanarFlow.BKMNW.FixPath

/-!
# Algorithm 1: MultipleSourceMultipleSinkMaxFlow

This file formalizes the recursion of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen
(SIAM J. Comput. 46(4), 2017, Section 2, Algorithm 1) and its correctness proof (Appendix A).

## The problem solved recursively (Section 2)

On a piece `P` (a set of darts closed under reversal, with the capacities `capOn u P`), with
sources `S`, sinks `T` and a set `A` of *hole* vertices (the vertices of the separators of the
ancestors; the article contracts each of them to a single node), compute a pseudoflow `f`
(`MSOut`):

* conserved everywhere except at `S ∪ T ∪ A`;
* with no residual path from `S` to `T`, from `S` to `A`, from `A` to `T`.

## One recursive step (`nodeStep`, lines 6–14 of Algorithm 1)

The piece is split into two pieces by a separator (`HSep`): a simple path through the holes
(`HPath`, the cycle of the article without one edge, in the graph with the earlier separators
contracted), which may pass through holes; the vertices shared by the two pieces are terminals,
hole vertices or vertices of the path. The vertices of the path that are not in a hole form
simple paths of `M`, its *parts* (`HSep.segs`); the path with the holes it meets is the new hole
(`newHole`).

1. Lines 6–7: solve both pieces recursively, the holes met by the separator merged with it into
   the new hole (`childHoles`); add the two pseudoflows.
2. Lines 9–13, on each part `π` in turn, the later parts as holes (`sepStep`):
   * line 9: FixConservationOnPath on `π` (`FixOut`, implemented in
     `PlanarFlow/BKMNW/FixPath.lean`);
   * lines 10–12: for every hole `H`: CycleToSingleSinkLimitedMaxFlow from the vertices `C` of
     `π` to `H` (`C2SOut`), then SingleSourceToCycleLimitedMaxFlow from `H` to `C` (`S2COut`).
     Holes that no dart of the piece touches are skipped (nothing can be pushed to them);
   * line 13: push the positive excess of `C` back to `S` (`RetOut`), then the negative excess
     of `C` back from `T` (`FromOut`).

## Correctness (Appendix A)

All the statements "no residual path from `X` to `Y`" are closed sets (`NoPath`), and every lemma
of Appendix A is an instance of two facts on closed sets (`Closed.src`, `Closed.snk`): a closed
set `Y` stays closed when a flow is added whose net outflow changes only on `X ∪ Z`, if either
`X ⊆ Y` and the outflow does not increase on `Z` (*sources lemma*, Lemma A.2), or `X` is
disjoint from `Y` and the outflow does not decrease on `Z` (*sinks lemma*, Lemma A.3).

* `combine`: after the recursive calls, no residual path from `S` to `T ∪ A ∪ C` and none from
  `A ∪ C ∪ S` to `T` (Lemma A.4): the closed sets of the two pieces glue along the shared
  vertices, which all belong to `S ∪ T ∪ A ∪ C`.
* `NInv`: the invariant of lines 9–12 (Lemmas A.4–A.8, Corollary A.9): Lemma A.4, the absence of
  residual paths from the vertices of `C` with positive inflow (`posSet`) to those with negative
  inflow (`negSet`), and, for the holes already processed, none from `posSet` to the hole and none
  from the hole to `negSet`. `NInv.hole` is one iteration of lines 11–12; it uses the sets
  `C⁺` (`fwdReach`) and `C⁻` (`bwdReach`) of the article.
* `NInv.finish`: line 13 (Lemma A.10).
* `nodeStep_core`: lines 9–13 on one part give the output of the recursion, from the state
  after the recursive calls; `sepStep_spec`: the same for the parts one after the other (each
  step's output is the state after the recursive calls for the next part, with one hole fewer).
* `arun_spec`: **the recursion meets the specification**, by induction on the decomposition,
  for decompositions whose new holes are simple paths of `M` (`ADec.PathHoles`, needed by the
  specifications of Section 4 on `M`; on the piece maps every hole is one vertex and this is not
  needed). The correctness theorem for maximum flow whose hypotheses are all shown to be
  satisfiable is `PlanarFlow.BKMNW.maxflow_plane` (`PlanarFlow/BKMNW/MaxFlow.lean`), for the
  recursion `runL` on the decomposition `PlanarFlow.BKMNW.chainDec`.

The subroutines are given as functions with their specifications (`NodeOracles.Spec`); all of
them are implemented and proved to meet these specifications from the specifications of the planar
subroutines (`PlanarFlow.BKMNW.impl_spec`, `PlanarFlow/BKMNW/Main.lean`): FixConservationOnPath by
`PlanarFlow.BKMNW.fixPath`, lines 11–12 by `PlanarFlow.BKMNW.c2sImpl` and
`PlanarFlow.BKMNW.s2cImpl`, line 13 by `PlanarFlow.BKMNW.retImpl` and `PlanarFlow.BKMNW.frmImpl`,
and the leaves (pieces of at most one edge, `ADec.LeafLe 2`) by `PlanarFlow.BKMNW.leafSolve`.

## Deviations from the article

* **Holes instead of contraction** (Section 2, lines 3–5). The article contracts the separator
  cycle, with the nodes of `A` on it, into one node `v` and adds `v` to `A`. Here pieces are sets
  of darts and a hole is a set of vertices of `M` (`newHole`: the vertices of the separator with
  the holes it meets); the statements "no residual path from `S` to `A`" and "from `A` to `T`"
  are statements about sets, so they are the same with or without the contraction. The
  contraction matters for the planarity of the single-sink maximum flow inside
  CycleToSingleSinkLimitedMaxFlow, which is part of that subroutine's specification here, and the
  recursion that runs as the article does contracts the holes (`PlanarFlow.BKMNW.runL`, on the
  piece maps).
* **Holes the piece does not touch are skipped** in the loop of lines 10–12: nothing can be pushed
  to them (`noPath_untouched`). The article removes them from `A` (`A ∩ G₁`); the effect is the
  same, and the number of iterations is the number of holes touching the piece (at most six in the
  article), which is what the cost analysis counts (`PlanarFlow/BKMNW/Cost.lean`).
* **Line 13 is two subroutines** (`RetOut`, `FromOut`), each specified by the change of the net
  outflows it makes; their preconditions are the facts that make the push-back of Appendix C
  possible, and they are proved to hold at line 13.
* **The holes are the vertex sets of the separators of the ancestors, merged** when a separator
  passes through them, and lines 11–12 receive a part of the separator, a simple path (the
  single-source single-sink maximum flow inside them contracts it, and the hole).
* **The recursion stops at pieces of at most one edge** (`ADec.LeafLe 2`), solved directly.
* **A separator through holes is processed one part at a time.** The article runs lines 9–13
  once, on the whole cycle `C`, with the hole nodes on `C` part of `C`. Its proof does not cover
  this case, and line 13 as stated would fail there: it pushes the excess of every node of `C`
  back to `S`, and pushing a positive excess of a hole node `a` back to `S` creates a residual
  path from `S` to `a`, whereas the output must have none from `S` to the holes. Here the hole
  vertices keep their excess (they are holes of the output), and lines 9–13 run on each part of
  the separator off the holes, the later parts as holes. A separator meeting no hole has one
  part, and the step is that of the article. With `j` holes met there are at most `j + 1` parts,
  and the cost of the step is multiplied by at most `j + 1` (`PlanarFlow.BKMNW.ADec.Bal`).
* **The separator avoids the terminals** (`ADec.Good`), as the article assumes (footnote 4: a
  source or sink on the separator is replaced by a pendant copy).

## Conventions

The article's *inflow* is minus the net outflow `M.div`. A vertex with positive inflow has
`M.div f v < 0`. The decomposition must satisfy `Good`: the shared vertices of two siblings are
terminals, hole vertices or separator vertices, and the separator vertices are not terminals (the
article assumes the latter for the sources and sinks, footnote 4).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-! ### The specifications -/

variable (M) in
/-- **The output of the recursion** (Section 2): a pseudoflow conserved off `S ∪ T ∪ A` with no
residual path from `S` to `T`, from `S` to `A`, from `A` to `T`. -/
structure MSOut (U : D → ℤ) (S T A : Finset V) (f : D → ℤ) : Prop where
  pseudo : IsPseudo M U f
  cons : ∀ v, v ∉ S → v ∉ T → v ∉ A → M.div f v = 0
  st : NoPath M U f S T
  sa : NoPath M U f S A
  at' : NoPath M U f A T

variable (M) in
/-- The vertices of `C` with positive inflow. -/
def posSet (f : D → ℤ) (C : Finset V) : Finset V := C.filter fun v => M.div f v < 0

variable (M) in
/-- The vertices of `C` with negative inflow. -/
def negSet (f : D → ℤ) (C : Finset V) : Finset V := C.filter fun v => 0 < M.div f v

variable (M) in
/-- The vertices of `C` reachable by residual paths from `X` (`C⁺` for `X` the vertices of `C`
with positive inflow). -/
noncomputable def fwdReach (U f : D → ℤ) (X C : Finset V) : Finset V := by
  classical exact C.filter fun v => ∃ x ∈ X, Relation.ReflTransGen (ResAdj M U f) x v

variable (M) in
/-- The vertices of `C` from which a residual path leads to `X` (`C⁻`). -/
noncomputable def bwdReach (U f : D → ℤ) (X C : Finset V) : Finset V := by
  classical exact C.filter fun v => ∃ x ∈ X, Relation.ReflTransGen (ResAdj M U f) v x

variable (M) in
/-- **CycleToSingleSinkLimitedMaxFlow** (Section 4, Algorithm 5), with the sink a hole `H`: the
net outflow changes only on `C⁺` and `H`, stays nonpositive on `C⁺`, does not increase on `H`,
and no residual path leads from the vertices of `C` with positive inflow to `H`. -/
structure C2SOut (U f f' : D → ℤ) (C H : Finset V) : Prop where
  pseudo : IsPseudo M U f'
  eq : ∀ v, v ∉ fwdReach M U f (posSet M f C) C → v ∉ H → M.div f' v = M.div f v
  nonpos : ∀ v ∈ fwdReach M U f (posSet M f C) C, M.div f' v ≤ 0
  sink : ∀ v ∈ H, M.div f' v ≤ M.div f v
  noPath : NoPath M U f' (posSet M f' C) H

variable (M) in
/-- **SingleSourceToCycleLimitedMaxFlow**, symmetric to `C2SOut`. -/
structure S2COut (U f f' : D → ℤ) (C H : Finset V) : Prop where
  pseudo : IsPseudo M U f'
  eq : ∀ v, v ∉ bwdReach M U f (negSet M f C) C → v ∉ H → M.div f' v = M.div f v
  nonneg : ∀ v ∈ bwdReach M U f (negSet M f C) C, 0 ≤ M.div f' v
  source : ∀ v ∈ H, M.div f v ≤ M.div f' v
  noPath : NoPath M U f' H (negSet M f' C)

variable (M) in
/-- **Pushing excess back to the sources** (line 13): the vertices of `X` become balanced, the
net outflow changes only on `X ∪ S` and does not increase on `S`. -/
structure RetOut (U f f' : D → ℤ) (X S : Finset V) : Prop where
  pseudo : IsPseudo M U f'
  zero : ∀ v ∈ X, M.div f' v = 0
  eq : ∀ v, v ∉ X → v ∉ S → M.div f' v = M.div f v
  src : ∀ v ∈ S, M.div f' v ≤ M.div f v

variable (M) in
/-- **Pushing flow back from the sinks** (line 13): the vertices of `X` become balanced, the net
outflow changes only on `X ∪ T` and does not decrease on `T`. -/
structure FromOut (U f f' : D → ℤ) (T X : Finset V) : Prop where
  pseudo : IsPseudo M U f'
  zero : ∀ v ∈ X, M.div f' v = 0
  eq : ∀ v, v ∉ X → v ∉ T → M.div f' v = M.div f v
  snk : ∀ v ∈ T, M.div f v ≤ M.div f' v

/-! ### Sources and sinks lemmas -/

/-- **The sources lemma** (Lemma A.2): a closed set containing the sources `X` of the change stays
closed, if the outflow does not increase on the other changed vertices `Z`. -/
theorem Closed.src {U f f' : D → ℤ} {Y X Z : Finset V} (hf : IsPseudo M U f)
    (hf' : IsPseudo M U f') (hY : Closed M U f Y) (hXY : X ⊆ Y)
    (h0 : ∀ v, v ∉ X → v ∉ Z → M.div f' v = M.div f v) (hZ : ∀ v ∈ Z, M.div f' v ≤ M.div f v) :
    Closed M U f' Y := by
  classical
  refine hY.of_sum_le hf hf' ?_
  have htot : ∑ v, (M.div f' v - M.div f v) = 0 := by
    rw [sum_sub_distrib, M.sum_div hf'.antisymm, M.sum_div hf.antisymm, sub_self]
  have hout : ∑ v ∈ univ \ Y, (M.div f' v - M.div f v) ≤ 0 := sum_nonpos fun v hv => by
    have hvY : v ∉ Y := (mem_sdiff.1 hv).2
    by_cases hvZ : v ∈ Z
    · have := hZ v hvZ; omega
    · rw [h0 v (fun h => hvY (hXY h)) hvZ]; omega
  have := sum_sdiff (s₁ := Y) (s₂ := univ) (f := fun v => M.div f' v - M.div f v) (subset_univ Y)
  rw [htot] at this
  have h2 : 0 ≤ ∑ v ∈ Y, (M.div f' v - M.div f v) := by linarith
  rw [sum_sub_distrib] at h2; linarith

/-- **The sinks lemma** (Lemma A.3): a closed set disjoint from the sinks `X` of the change stays
closed, if the outflow does not decrease on the other changed vertices `Z`. -/
theorem Closed.snk {U f f' : D → ℤ} {Y X Z : Finset V} (hf : IsPseudo M U f)
    (hf' : IsPseudo M U f') (hY : Closed M U f Y) (hXY : Disjoint X Y)
    (h0 : ∀ v, v ∉ X → v ∉ Z → M.div f' v = M.div f v) (hZ : ∀ v ∈ Z, M.div f v ≤ M.div f' v) :
    Closed M U f' Y := by
  refine hY.of_sum_le hf hf' (sum_le_sum fun v hv => ?_)
  have hvX : v ∉ X := disjoint_right.1 hXY hv
  by_cases hvZ : v ∈ Z
  · exact hZ v hvZ
  · rw [h0 v hvX hvZ]

lemma NoPath.src {U f f' : D → ℤ} {A B X Z : Finset V} (hf : IsPseudo M U f)
    (hf' : IsPseudo M U f') (h : NoPath M U f (A ∪ X) B)
    (h0 : ∀ v, v ∉ X → v ∉ Z → M.div f' v = M.div f v) (hZ : ∀ v ∈ Z, M.div f' v ≤ M.div f v) :
    NoPath M U f' A B := by
  obtain ⟨Y, h1, h2, h3⟩ := h
  exact ⟨Y, subset_union_left.trans h1, h2,
    h3.src hf hf' (subset_union_right.trans h1) h0 hZ⟩

lemma NoPath.snk {U f f' : D → ℤ} {A B X Z : Finset V} (hf : IsPseudo M U f)
    (hf' : IsPseudo M U f') (h : NoPath M U f A (B ∪ X))
    (h0 : ∀ v, v ∉ X → v ∉ Z → M.div f' v = M.div f v) (hZ : ∀ v ∈ Z, M.div f v ≤ M.div f' v) :
    NoPath M U f' A B := by
  obtain ⟨Y, h1, h2, h3⟩ := h
  exact ⟨Y, h1, disjoint_of_subset_right subset_union_left h2,
    h3.snk hf hf' (disjoint_of_subset_right subset_union_right h2).symm h0 hZ⟩

lemma NoPath.union_left {U f : D → ℤ} {A A' B : Finset V} (h : NoPath M U f A B)
    (h' : NoPath M U f A' B) : NoPath M U f (A ∪ A') B := by
  obtain ⟨Y, h1, h2, h3⟩ := h
  obtain ⟨Y', h1', h2', h3'⟩ := h'
  exact ⟨Y ∪ Y', union_subset_union h1 h1', disjoint_union_left.2 ⟨h2, h2'⟩, h3.union h3'⟩

lemma NoPath.union_right {U f : D → ℤ} {A B B' : Finset V} (h : NoPath M U f A B)
    (h' : NoPath M U f A B') : NoPath M U f A (B ∪ B') := by
  obtain ⟨Y, h1, h2, h3⟩ := h
  obtain ⟨Y', h1', h2', h3'⟩ := h'
  exact ⟨Y ∩ Y', subset_inter h1 h1',
    disjoint_union_right.2 ⟨disjoint_of_subset_left inter_subset_left h2,
      disjoint_of_subset_left inter_subset_right h2'⟩, h3.inter h3'⟩

lemma NoPath.mono {U f : D → ℤ} {A A' B B' : Finset V} (h : NoPath M U f A B) (hA : A' ⊆ A)
    (hB : B' ⊆ B) : NoPath M U f A' B' := by
  obtain ⟨Y, h1, h2, h3⟩ := h
  exact ⟨Y, hA.trans h1, disjoint_of_subset_right hB h2, h3⟩

/-- A closed set containing `X` contains every vertex reachable from `X`. -/
lemma fwdReach_sub {U f : D → ℤ} {X C Y : Finset V} (hY : Closed M U f Y) (hX : X ⊆ Y) :
    fwdReach M U f X C ⊆ Y := by
  classical
  intro v hv
  simp only [fwdReach, mem_filter] at hv
  obtain ⟨x, hx, hr⟩ := hv.2
  exact hY.not_reach (hX hx) hr

/-- A closed set disjoint from `X` contains no vertex from which `X` is reachable. -/
lemma bwdReach_disj {U f : D → ℤ} {X C Y : Finset V} (hY : Closed M U f Y) (hX : Disjoint Y X) :
    Disjoint (bwdReach M U f X C) Y := by
  classical
  rw [disjoint_left]
  intro v hv hvY
  simp only [bwdReach, mem_filter] at hv
  obtain ⟨x, hx, hr⟩ := hv.2
  exact disjoint_left.1 hX (hY.not_reach hvY hr) hx

lemma sub_fwdReach {U f : D → ℤ} {X C : Finset V} (h : X ⊆ C) : X ⊆ fwdReach M U f X C := by
  classical
  intro v hv; simp only [fwdReach, mem_filter]; exact ⟨h hv, v, hv, .refl⟩

lemma sub_bwdReach {U f : D → ℤ} {X C : Finset V} (h : X ⊆ C) : X ⊆ bwdReach M U f X C := by
  classical
  intro v hv; simp only [bwdReach, mem_filter]; exact ⟨h hv, v, hv, .refl⟩

lemma fwdReach_subset {U f : D → ℤ} {X C : Finset V} : fwdReach M U f X C ⊆ C := by
  classical exact filter_subset _ _

lemma bwdReach_subset {U f : D → ℤ} {X C : Finset V} : bwdReach M U f X C ⊆ C := by
  classical exact filter_subset _ _

lemma posSet_subset {f : D → ℤ} {C : Finset V} : posSet M f C ⊆ C := filter_subset _ _

lemma negSet_subset {f : D → ℤ} {C : Finset V} : negSet M f C ⊆ C := filter_subset _ _

lemma mem_posSet {f : D → ℤ} {C : Finset V} {v : V} : v ∈ posSet M f C ↔ v ∈ C ∧ M.div f v < 0 :=
  mem_filter

lemma mem_negSet {f : D → ℤ} {C : Finset V} {v : V} : v ∈ negSet M f C ↔ v ∈ C ∧ 0 < M.div f v :=
  mem_filter

/-! ### Untouched vertices -/

/-- A set of vertices touched by no dart of the piece: no residual path enters or leaves it. -/
lemma noPath_untouched {u f : D → ℤ} {P : Finset D} (hP : RevClosed M P)
    (hf : IsPseudo M (capOn u P) f) {H : Finset V} (hH : ∀ v ∈ H, ¬ Touch M P v) :
    (∀ X, Disjoint X H → NoPath M (capOn u P) f X H) ∧
      (∀ Y, Disjoint H Y → NoPath M (capOn u P) f H Y) := by
  have hz : ∀ d, d ∉ P → f d = capOn u P d := fun d hd => by
    rw [hf.eq_zero_of_not_mem hP hd]; simp [capOn, hd]
  constructor
  · intro X hX
    refine ⟨univ \ H, fun v hv => mem_sdiff.2 ⟨mem_univ v, disjoint_left.1 hX hv⟩,
      disjoint_sdiff_self_left, fun d _ hd2 => hz d fun hd => ?_⟩
    have : M.head d ∈ H := by simpa using hd2
    exact hH _ this ⟨M.rev d, hP d hd, rfl⟩
  · intro Y hY
    exact ⟨H, subset_rfl, hY, fun d hd1 _ => hz d fun h => hH _ hd1 ⟨d, h, rfl⟩⟩

/-! ### Gluing the two pieces (Lemma A.4) -/

/-- The closed sets of two pieces agreeing on the shared vertices glue into a closed set of the
union. -/
lemma closed_glue {u : D → ℤ} {P Q : Finset D} (hP : RevClosed M P) (hQ : RevClosed M Q)
    (hPQ : Disjoint P Q) {f g : D → ℤ} (hf : IsPseudo M (capOn u P) f)
    (hg : IsPseudo M (capOn u Q) g) {Y Z : Finset V} (hY : Closed M (capOn u P) f Y)
    (hZ : Closed M (capOn u Q) g Z) (hagree : ∀ v ∈ bd M P Q, (v ∈ Y ↔ v ∈ Z)) :
    ∃ W, (∀ v, v ∈ Y → v ∈ Z → v ∈ W) ∧ (∀ v, v ∉ Y → v ∉ Z → v ∉ W) ∧
      Closed M (capOn u (P ∪ Q)) (f + g) W := by
  classical
  refine ⟨univ.filter fun v => if Touch M P v then v ∈ Y else v ∈ Z, fun v h1 h2 => ?_,
    fun v h1 h2 => ?_, fun d hd1 hd2 => ?_⟩
  · simp only [mem_filter, mem_univ, true_and]; split_ifs <;> assumption
  · simp only [mem_filter, mem_univ, true_and]; split_ifs <;> assumption
  · simp only [mem_filter, mem_univ, true_and] at hd1 hd2
    simp only [Pi.add_apply]
    by_cases hdP : d ∈ P
    · have hdQ : d ∉ Q := disjoint_left.1 hPQ hdP
      have ht : Touch M P (M.tail d) := ⟨d, hdP, rfl⟩
      have hh : Touch M P (M.head d) := ⟨M.rev d, hP d hdP, rfl⟩
      simp only [ht, hh, ↓reduceIte] at hd1 hd2
      rw [hg.eq_zero_of_not_mem hQ hdQ, add_zero, hY d hd1 hd2]
      simp [capOn, hdP]
    · by_cases hdQ : d ∈ Q
      · have ht : Touch M Q (M.tail d) := ⟨d, hdQ, rfl⟩
        have hh : Touch M Q (M.head d) := ⟨M.rev d, hQ d hdQ, rfl⟩
        have h1 : M.tail d ∈ Z := by
          split_ifs at hd1 with h
          · exact (hagree _ (mem_bd.2 ⟨h, ht⟩)).1 hd1
          · exact hd1
        have h2 : M.head d ∉ Z := by
          split_ifs at hd2 with h
          · exact fun h' => hd2 ((hagree _ (mem_bd.2 ⟨h, hh⟩)).2 h')
          · exact hd2
        rw [hf.eq_zero_of_not_mem hP hdP, zero_add, hZ d h1 h2]
        simp [capOn, hdQ]
      · rw [hf.eq_zero_of_not_mem hP hdP, hg.eq_zero_of_not_mem hQ hdQ]
        simp [capOn, hdP, hdQ]

/-- **After the recursive calls** (Lemma A.4): the sum of the outputs of the two pieces, with the
separator vertices `C` as holes, is conserved off `S ∪ T ∪ A ∪ C`, and no residual path leads from
`S` to `T ∪ A ∪ C` nor from `A ∪ C ∪ S` to `T`. -/
theorem combine {u : D → ℤ} {P Q : Finset D} (hP : RevClosed M P) (hQ : RevClosed M Q)
    (hPQ : Disjoint P Q) {S T A C : Finset V} (hST : Disjoint S T) (hSA : Disjoint S (A ∪ C))
    (hbd : bd M P Q ⊆ S ∪ T ∪ (A ∪ C)) {f g : D → ℤ}
    (hf : MSOut M (capOn u P) S T (A ∪ C) f) (hg : MSOut M (capOn u Q) S T (A ∪ C) g) :
    IsPseudo M (capOn u (P ∪ Q)) (f + g) ∧
      (∀ v, v ∉ S → v ∉ T → v ∉ A ∪ C → M.div (f + g) v = 0) ∧
      NoPath M (capOn u (P ∪ Q)) (f + g) S (T ∪ (A ∪ C)) ∧
      NoPath M (capOn u (P ∪ Q)) (f + g) ((A ∪ C) ∪ S) T := by
  classical
  have hps := hf.pseudo.add_piece hP hQ hPQ hg.pseudo
  refine ⟨hps, fun v h1 h2 h3 => ?_, ?_, ?_⟩
  · rw [div_add']
    by_cases ht : Touch M P v
    · by_cases ht' : Touch M Q v
      · exfalso
        rcases mem_union.1 (hbd (mem_bd.2 ⟨ht, ht'⟩)) with h | h
        · rcases mem_union.1 h with h | h
          · exact h1 h
          · exact h2 h
        · exact h3 h
      · rw [hf.cons v h1 h2 h3, hg.pseudo.div_eq_zero hQ ht', add_zero]
    · rw [hf.pseudo.div_eq_zero hP ht, hg.cons v h1 h2 h3, zero_add]
  · obtain ⟨Y, hY1, hY2, hY3⟩ := hf.st.union_right hf.sa
    obtain ⟨Z, hZ1, hZ2, hZ3⟩ := hg.st.union_right hg.sa
    have hag : ∀ v ∈ bd M P Q, (v ∈ Y ↔ v ∈ Z) := fun v hv => by
      rcases mem_union.1 (hbd hv) with h | h
      · rcases mem_union.1 h with h | h
        · exact ⟨fun _ => hZ1 h, fun _ => hY1 h⟩
        · exact ⟨fun h' => absurd h (disjoint_left.1 hY2 h' |> fun h'' => by simp_all),
            fun h' => absurd h (disjoint_left.1 hZ2 h' |> fun h'' => by simp_all)⟩
      · exact ⟨fun h' => absurd (mem_union_right _ h) (disjoint_left.1 hY2 h'),
          fun h' => absurd (mem_union_right _ h) (disjoint_left.1 hZ2 h')⟩
    obtain ⟨W, hW1, hW2, hW3⟩ := closed_glue hP hQ hPQ hf.pseudo hg.pseudo hY3 hZ3 hag
    exact ⟨W, fun v hv => hW1 v (hY1 hv) (hZ1 hv), disjoint_left.2 fun v hvW hv =>
      hW2 v (disjoint_right.1 hY2 hv) (disjoint_right.1 hZ2 hv) hvW, hW3⟩
  · obtain ⟨Y, hY1, hY2, hY3⟩ := hf.at'.union_left hf.st
    obtain ⟨Z, hZ1, hZ2, hZ3⟩ := hg.at'.union_left hg.st
    have hag : ∀ v ∈ bd M P Q, (v ∈ Y ↔ v ∈ Z) := fun v hv => by
      rcases mem_union.1 (hbd hv) with h | h
      · rcases mem_union.1 h with h | h
        · exact ⟨fun _ => hZ1 (mem_union_right _ h), fun _ => hY1 (mem_union_right _ h)⟩
        · exact ⟨fun h' => absurd h (disjoint_left.1 hY2 h'),
            fun h' => absurd h (disjoint_left.1 hZ2 h')⟩
      · exact ⟨fun _ => hZ1 (mem_union_left _ h), fun _ => hY1 (mem_union_left _ h)⟩
    obtain ⟨W, hW1, hW2, hW3⟩ := closed_glue hP hQ hPQ hf.pseudo hg.pseudo hY3 hZ3 hag
    exact ⟨W, fun v hv => hW1 v (hY1 hv) (hZ1 hv), disjoint_left.2 fun v hvW hv =>
      hW2 v (disjoint_right.1 hY2 hv) (disjoint_right.1 hZ2 hv) hvW, hW3⟩

/-! ### The invariant of lines 9–12 -/

variable (M) in
/-- The invariant of lines 9–12 after the holes `Hd` have been processed (Lemmas A.4–A.8). -/
structure NInv (U f : D → ℤ) (S T A C : Finset V) (Hd : List (Finset V)) : Prop where
  pseudo : IsPseudo M U f
  cons : ∀ v, v ∉ S → v ∉ T → v ∉ A ∪ C → M.div f v = 0
  sTAC : NoPath M U f S (T ∪ (A ∪ C))
  acsT : NoPath M U f ((A ∪ C) ∪ S) T
  pn : NoPath M U f (posSet M f C) (negSet M f C)
  done : ∀ H ∈ Hd, NoPath M U f (posSet M f C) H ∧ NoPath M U f H (negSet M f C)

/-- A change supported in `A ∪ C` keeps the two statements of Lemma A.4. -/
lemma keep_A4 {U f f' : D → ℤ} {S T A C X : Finset V} (hf : IsPseudo M U f)
    (hf' : IsPseudo M U f') (hX : X ⊆ A ∪ C) (h0 : ∀ v, v ∉ X → M.div f' v = M.div f v)
    (h1 : NoPath M U f S (T ∪ (A ∪ C))) (h2 : NoPath M U f ((A ∪ C) ∪ S) T) :
    NoPath M U f' S (T ∪ (A ∪ C)) ∧ NoPath M U f' ((A ∪ C) ∪ S) T :=
  ⟨NoPath.snk (X := X) (Z := ∅) hf hf' (h1.mono subset_rfl
      (union_subset subset_rfl (hX.trans subset_union_right)))
      (fun v hv _ => h0 v hv) (by simp),
    NoPath.src (X := X) (Z := ∅) hf hf' (h2.mono
      (union_subset subset_rfl (hX.trans subset_union_left)) subset_rfl)
      (fun v hv _ => h0 v hv) (by simp)⟩

/-- **After line 9**: the invariant holds with no hole processed. -/
theorem NInv.ofFix {U f f₁ : D → ℤ} {S T A : Finset V} {C : Finset V}
    (hps : IsPseudo M U f) (hcons : ∀ v, v ∉ S → v ∉ T → v ∉ A ∪ C → M.div f v = 0)
    (h1 : NoPath M U f S (T ∪ (A ∪ C))) (h2 : NoPath M U f ((A ∪ C) ∪ S) T)
    (hfix : FixOut M U f C f₁) : NInv M U f₁ S T A C [] := by
  obtain ⟨k1, k2⟩ := keep_A4 hps hfix.pseudo subset_union_right hfix.eq h1 h2
  refine ⟨hfix.pseudo, fun v hS hT hAC => ?_, k1, k2, hfix.noPath, by simp⟩
  rw [hfix.eq v fun h => hAC (mem_union_right _ h)]; exact hcons v hS hT hAC

/-- **One hole** (lines 11–12, Lemmas A.5–A.8). -/
theorem NInv.hole {U f f' g : D → ℤ} {S T A C H : Finset V} {Hd : List (Finset V)}
    (h : NInv M U f S T A C Hd) (hHA : H ⊆ A) (hCH : Disjoint C H)
    (h1 : (∀ v ∈ fwdReach M U f (posSet M f C) C, M.div f v ≤ 0) → C2SOut M U f f' C H)
    (h2 : (∀ v ∈ bwdReach M U f' (negSet M f' C) C, 0 ≤ M.div f' v) → S2COut M U f' g C H) :
    NInv M U g S T A C (Hd ++ [H]) := by
  classical
  -- the call to CycleToSingleSinkLimitedMaxFlow
  obtain ⟨Y₀, hY₀1, hY₀2, hY₀3⟩ := h.pn
  have hCp : fwdReach M U f (posSet M f C) C ⊆ Y₀ := fwdReach_sub hY₀3 hY₀1
  have pre1 : ∀ v ∈ fwdReach M U f (posSet M f C) C, M.div f v ≤ 0 := fun v hv => by
    by_contra hpos
    exact disjoint_left.1 hY₀2 (hCp hv) (mem_negSet.2 ⟨fwdReach_subset hv, by omega⟩)
  obtain ⟨o1ps, o1eq, o1np, o1sink, o1nopath⟩ := h1 pre1
  generalize hCp' : fwdReach M U f (posSet M f C) C = Cp at hCp o1eq o1np pre1
  have hCpC : Cp ⊆ C := hCp' ▸ fwdReach_subset
  have hposCp : posSet M f C ⊆ Cp := hCp' ▸ sub_fwdReach posSet_subset
  have hpos' : posSet M f' C ⊆ Cp := fun v hv => by
    obtain ⟨hvC, hlt⟩ := mem_posSet.1 hv
    by_contra hn
    rw [o1eq v hn (disjoint_left.1 hCH hvC)] at hlt
    exact hn (hposCp (mem_posSet.2 ⟨hvC, hlt⟩))
  have hneg' : negSet M f' C ⊆ negSet M f C := fun v hv => by
    obtain ⟨hvC, hlt⟩ := mem_negSet.1 hv
    have hn : v ∉ Cp := fun h' => by have := o1np v h'; omega
    rw [o1eq v hn (disjoint_left.1 hCH hvC)] at hlt
    exact mem_negSet.2 ⟨hvC, hlt⟩
  have h0₁ : ∀ v, v ∉ Cp ∪ H → M.div f' v = M.div f v := fun v hv =>
    o1eq v (fun h' => hv (mem_union_left _ h')) (fun h' => hv (mem_union_right _ h'))
  obtain ⟨k1, k2⟩ := keep_A4 h.pseudo o1ps
    (union_subset (hCpC.trans subset_union_right) (hHA.trans subset_union_left)) h0₁ h.sTAC h.acsT
  have pn₁ : NoPath M U f' (posSet M f' C) (negSet M f' C) :=
    ⟨Y₀, hpos'.trans hCp, disjoint_of_subset_right hneg' hY₀2,
      hY₀3.src h.pseudo o1ps hCp o1eq o1sink⟩
  have done₁ : ∀ H' ∈ Hd, NoPath M U f' (posSet M f' C) H' ∧ NoPath M U f' H' (negSet M f' C) := by
    intro H' hH'
    obtain ⟨⟨Y, hY1, hY2, hY3⟩, ⟨Z, hZ1, hZ2, hZ3⟩⟩ := h.done H' hH'
    have hCpY : Cp ⊆ Y := hCp' ▸ fwdReach_sub hY3 hY1
    refine ⟨⟨Y, hpos'.trans hCpY, hY2, hY3.src h.pseudo o1ps hCpY o1eq o1sink⟩,
      ⟨Z ∪ Y₀, hZ1.trans subset_union_left,
        disjoint_of_subset_right hneg' (disjoint_union_left.2 ⟨hZ2, hY₀2⟩),
        (hZ3.union hY₀3).src h.pseudo o1ps (hCp.trans subset_union_right) o1eq o1sink⟩⟩
  -- the call to SingleSourceToCycleLimitedMaxFlow
  obtain ⟨Y₁, hY₁1, hY₁2, hY₁3⟩ := pn₁
  have hCm : Disjoint (bwdReach M U f' (negSet M f' C) C) Y₁ := bwdReach_disj hY₁3 hY₁2
  have pre2 : ∀ v ∈ bwdReach M U f' (negSet M f' C) C, 0 ≤ M.div f' v := fun v hv => by
    by_contra hneg
    exact disjoint_left.1 hCm hv (hY₁1 (mem_posSet.2 ⟨bwdReach_subset hv, by omega⟩))
  obtain ⟨o2ps, o2eq, o2nn, o2src, o2nopath⟩ := h2 pre2
  generalize hCm' : bwdReach M U f' (negSet M f' C) C = Cm at hCm o2eq o2nn pre2
  have hCmC : Cm ⊆ C := hCm' ▸ bwdReach_subset
  have hnegCm : negSet M f' C ⊆ Cm := hCm' ▸ sub_bwdReach negSet_subset
  have hpos'' : posSet M g C ⊆ posSet M f' C := fun v hv => by
    obtain ⟨hvC, hlt⟩ := mem_posSet.1 hv
    have hn : v ∉ Cm := fun h' => by have := o2nn v h'; omega
    rw [o2eq v hn (disjoint_left.1 hCH hvC)] at hlt
    exact mem_posSet.2 ⟨hvC, hlt⟩
  have hneg'' : negSet M g C ⊆ Cm := fun v hv => by
    obtain ⟨hvC, hlt⟩ := mem_negSet.1 hv
    by_contra hn
    rw [o2eq v hn (disjoint_left.1 hCH hvC)] at hlt
    exact hn (hnegCm (mem_negSet.2 ⟨hvC, hlt⟩))
  have h0₂ : ∀ v, v ∉ Cm ∪ H → M.div g v = M.div f' v := fun v hv =>
    o2eq v (fun h' => hv (mem_union_left _ h')) (fun h' => hv (mem_union_right _ h'))
  obtain ⟨k3, k4⟩ := keep_A4 o1ps o2ps
    (union_subset (hCmC.trans subset_union_right) (hHA.trans subset_union_left)) h0₂ k1 k2
  refine ⟨o2ps, fun v hS hT hAC => ?_, k3, k4,
    ⟨Y₁, hpos''.trans hY₁1, disjoint_of_subset_right hneg'' hCm.symm,
      hY₁3.snk o1ps o2ps hCm o2eq o2src⟩, fun H' hH' => ?_⟩
  · rw [h0₂ v fun h' => hAC (by
      rcases mem_union.1 h' with h' | h'
      · exact mem_union_right _ (hCmC h')
      · exact mem_union_left _ (hHA h')), h0₁ v fun h' => hAC (by
      rcases mem_union.1 h' with h' | h'
      · exact mem_union_right _ (hCpC h')
      · exact mem_union_left _ (hHA h'))]
    exact h.cons v hS hT hAC
  · have hpos_to : ∀ H'', NoPath M U f' (posSet M f' C) H'' →
        NoPath M U g (posSet M g C) H'' := by
      intro H'' ⟨Y, hY1, hY2, hY3⟩
      have hd : Disjoint Cm (Y ∩ Y₁) :=
        disjoint_of_subset_right inter_subset_right hCm
      exact ⟨Y ∩ Y₁, subset_inter (hpos''.trans hY1) (hpos''.trans hY₁1),
        disjoint_of_subset_left inter_subset_left hY2,
        (hY3.inter hY₁3).snk o1ps o2ps hd o2eq o2src⟩
    rcases List.mem_append.1 hH' with hH' | hH'
    · obtain ⟨d1, ⟨Z, hZ1, hZ2, hZ3⟩⟩ := done₁ H' hH'
      have hd : Disjoint Cm Z := hCm' ▸ bwdReach_disj hZ3 hZ2
      exact ⟨hpos_to H' d1, ⟨Z, hZ1, disjoint_of_subset_right hneg'' hd.symm,
        hZ3.snk o1ps o2ps hd o2eq o2src⟩⟩
    · rw [List.mem_singleton] at hH'; subst hH'
      exact ⟨hpos_to H' o1nopath, o2nopath⟩

/-- A hole touched by no dart of the piece is skipped. -/
theorem NInv.skip {u f : D → ℤ} {P : Finset D} (hP : RevClosed M P) {S T A C H : Finset V}
    {Hd : List (Finset V)} (h : NInv M (capOn u P) f S T A C Hd) (hCH : Disjoint C H)
    (hH : ∀ v ∈ H, ¬ Touch M P v) : NInv M (capOn u P) f S T A C (Hd ++ [H]) := by
  obtain ⟨n1, n2⟩ := noPath_untouched hP h.pseudo hH
  refine ⟨h.pseudo, h.cons, h.sTAC, h.acsT, h.pn, fun H' hH' => ?_⟩
  rcases List.mem_append.1 hH' with hH' | hH'
  · exact h.done H' hH'
  · rw [List.mem_singleton] at hH'; subst hH'
    exact ⟨n1 _ (disjoint_of_subset_left posSet_subset hCH),
      n2 _ (disjoint_of_subset_right negSet_subset hCH.symm)⟩

/-- The union of a list of holes. -/
def hunion (Hs : List (Finset V)) : Finset V := Hs.foldr (· ∪ ·) ∅

lemma hunion_append (Hs : List (Finset V)) (C : Finset V) :
    hunion (Hs ++ [C]) = hunion Hs ∪ C := by
  induction Hs with
  | nil => simp [hunion]
  | cons H Hs ih =>
    simp only [List.cons_append, hunion, List.foldr_cons] at ih ⊢; rw [ih, union_assoc]

lemma subset_hunion {Hs : List (Finset V)} {H : Finset V} (h : H ∈ Hs) : H ⊆ hunion Hs := by
  induction Hs with
  | nil => simp at h
  | cons H' Hs ih =>
    simp only [hunion, List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact subset_union_left
    · exact (ih h).trans subset_union_right

lemma noPath_hunion_right {U f : D → ℤ} {X : Finset V} :
    ∀ {Hs : List (Finset V)}, (∀ H ∈ Hs, NoPath M U f X H) → NoPath M U f X (hunion Hs)
  | [], _ => ⟨univ, subset_univ _, by simp [hunion], fun d h1 h2 => absurd (mem_univ _) h2⟩
  | H :: Hs, h => (h H (List.mem_cons_self ..)).union_right
      (noPath_hunion_right fun H' hH' => h H' (List.mem_cons_of_mem _ hH'))

lemma noPath_hunion_left {U f : D → ℤ} {Y : Finset V} :
    ∀ {Hs : List (Finset V)}, (∀ H ∈ Hs, NoPath M U f H Y) → NoPath M U f (hunion Hs) Y
  | [], _ => ⟨∅, by simp [hunion], by simp, fun d h1 _ => absurd h1 (by simp)⟩
  | H :: Hs, h => (h H (List.mem_cons_self ..)).union_left
      (noPath_hunion_left fun H' hH' => h H' (List.mem_cons_of_mem _ hH'))

/-! ### Line 13 -/

/-- **Line 13** (Lemma A.10): with all the holes processed, pushing the positive excess of `C`
back to `S` and the negative excess back from `T` gives the output of the recursion. -/
theorem NInv.finish {U f f₁ f₂ : D → ℤ} {S T C : Finset V} {Hs : List (Finset V)}
    (h : NInv M U f S T (hunion Hs) C Hs) (hSC : Disjoint S C) (hTC : Disjoint T C)
    (o1 : RetOut M U f f₁ (posSet M f C) S) (o2 : FromOut M U f₁ f₂ T (negSet M f₁ C)) :
    MSOut M U S T (hunion Hs) f₂ := by
  classical
  generalize hA : hunion Hs = A at h
  have hpA : NoPath M U f (posSet M f C) A :=
    hA ▸ noPath_hunion_right fun H hH => (h.done H hH).1
  have hAn : NoPath M U f A (negSet M f C) :=
    hA ▸ noPath_hunion_left fun H hH => (h.done H hH).2
  -- pushing back to the sources
  have hz1 : ∀ v, v ∉ posSet M f C → v ∉ S → M.div f₁ v = M.div f v := o1.eq
  have hsrc := o1.src
  have hneg1 : negSet M f₁ C = negSet M f C := by
    ext v
    simp only [mem_negSet]
    constructor
    · rintro ⟨hvC, hlt⟩
      have hn : v ∉ posSet M f C := fun h' => by rw [o1.zero v h'] at hlt; omega
      rw [hz1 v hn (disjoint_right.1 hSC hvC)] at hlt
      exact ⟨hvC, hlt⟩
    · rintro ⟨hvC, hlt⟩
      have hn : v ∉ posSet M f C := fun h' => by have := (mem_posSet.1 h').2; omega
      rw [hz1 v hn (disjoint_right.1 hSC hvC)]
      exact ⟨hvC, hlt⟩
  rw [hneg1] at o2
  have hST : NoPath M U f (S ∪ posSet M f C) T :=
    h.acsT.mono (union_subset subset_union_right
      (posSet_subset.trans (subset_union_right.trans subset_union_left))) subset_rfl
  have st1 : NoPath M U f₁ S T := hST.src h.pseudo o1.pseudo hz1 hsrc
  have sa1 : NoPath M U f₁ S A :=
    ((h.sTAC.mono subset_rfl (subset_union_left.trans subset_union_right)).union_left hpA).src
      h.pseudo o1.pseudo hz1 hsrc
  have at1 : NoPath M U f₁ A T :=
    (h.acsT.mono (union_subset (subset_union_left.trans subset_union_left)
      (posSet_subset.trans (subset_union_right.trans subset_union_left))) subset_rfl).src
      h.pseudo o1.pseudo hz1 hsrc
  have sn1 : NoPath M U f₁ S (negSet M f C) :=
    ((h.sTAC.mono subset_rfl
      (negSet_subset.trans (subset_union_right.trans subset_union_right))).union_left
      h.pn).src h.pseudo o1.pseudo hz1 hsrc
  have an1 : NoPath M U f₁ A (negSet M f C) :=
    (hAn.union_left h.pn).src h.pseudo o1.pseudo hz1 hsrc
  -- pushing back from the sinks
  have hz2 : ∀ v, v ∉ negSet M f C → v ∉ T → M.div f₂ v = M.div f₁ v := o2.eq
  refine ⟨o2.pseudo, fun v hS hT hAv => ?_,
    (st1.union_right sn1).snk o1.pseudo o2.pseudo hz2 o2.snk,
    (sa1.union_right sn1).snk o1.pseudo o2.pseudo hz2 o2.snk,
    (at1.union_right an1).snk o1.pseudo o2.pseudo hz2 o2.snk⟩
  by_cases hn : v ∈ negSet M f C
  · exact o2.zero v hn
  · rw [hz2 v hn hT]
    by_cases hp : v ∈ posSet M f C
    · exact o1.zero v hp
    · rw [hz1 v hp hS]
      by_cases hvC : v ∈ C
      · by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact hp (mem_posSet.2 ⟨hvC, hlt⟩)
        · exact hn (mem_negSet.2 ⟨hvC, hlt⟩)
      · exact h.cons v hS hT (by simp [hAv, hvC])

/-! ### Separators through the holes -/

lemma mem_hunion {Hs : List (Finset V)} {v : V} : v ∈ hunion Hs ↔ ∃ H ∈ Hs, v ∈ H := by
  induction Hs with
  | nil => simp [hunion]
  | cons H Hs ih =>
    rw [show hunion (H :: Hs) = H ∪ hunion Hs from rfl, mem_union, ih]
    simp

lemma hunion_append' (Hs Ks : List (Finset V)) : hunion (Hs ++ Ks) = hunion Hs ∪ hunion Ks := by
  ext v; simp only [mem_hunion, List.mem_append, mem_union]
  constructor
  · rintro ⟨H, hH | hH, hv⟩
    · exact Or.inl ⟨H, hH, hv⟩
    · exact Or.inr ⟨H, hH, hv⟩
  · rintro (⟨H, hH, hv⟩ | ⟨H, hH, hv⟩)
    · exact ⟨H, Or.inl hH, hv⟩
    · exact ⟨H, Or.inr hH, hv⟩

lemma hunion_cons (H : Finset V) (Hs : List (Finset V)) : hunion (H :: Hs) = H ∪ hunion Hs := rfl

variable (M) in
/-- **A path through the holes**: darts `d 0, …, d (k - 1)` and vertices `p 0, …, p k` with
`p j` the tail of `d j`. The head of `d j` is `p (j + 1)`, or lies in the same hole as
`p (j + 1)`: the path crosses a hole (an earlier separator, contracted into one node in the
article) from the head of `d j` to the tail of `d (j + 1)` (`PlanarFlow.BKMNW.HPath.Simple`).
A path of the piece map, where the holes are contracted, is such a path. -/
structure HPath where
  /-- The number of darts. -/
  k : ℕ
  /-- The darts. -/
  d : ℕ → D
  /-- The vertices: `p j` is the tail of `d j`, and `p k` the last vertex. -/
  p : ℕ → V
  tail_d : ∀ j < k, M.tail (d j) = p j

namespace HPath

variable (ρ : HPath M)

/-- The darts of the path and their reverses. -/
def darts : List D := (List.range ρ.k).flatMap fun j => [ρ.d j, M.rev (ρ.d j)]

lemma mem_darts {e : D} : e ∈ ρ.darts ↔ ∃ j < ρ.k, e = ρ.d j ∨ e = M.rev (ρ.d j) := by
  simp only [darts, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]

/-- The vertices of `M` on the path: the vertices `p j` and the heads of the darts. -/
def mverts : Finset V :=
  (range (ρ.k + 1)).image ρ.p ∪ (range ρ.k).image fun j => M.head (ρ.d j)

lemma p_mem_mverts {j : ℕ} (hj : j ≤ ρ.k) : ρ.p j ∈ ρ.mverts :=
  mem_union_left _ (mem_image.2 ⟨j, mem_range.2 (by omega), rfl⟩)

lemma head_mem_mverts {j : ℕ} (hj : j < ρ.k) : M.head (ρ.d j) ∈ ρ.mverts :=
  mem_union_right _ (mem_image.2 ⟨j, mem_range.2 hj, rfl⟩)

lemma mem_mverts {v : V} :
    v ∈ ρ.mverts ↔ (∃ j ≤ ρ.k, ρ.p j = v) ∨ ∃ j < ρ.k, M.head (ρ.d j) = v := by
  simp only [mverts, mem_union, mem_image, mem_range, Nat.lt_succ_iff]

/-- Both ends of a dart of the path are vertices of the path. -/
lemma ends_mem {e : D} (he : e ∈ ρ.darts) : M.tail e ∈ ρ.mverts ∧ M.head e ∈ ρ.mverts := by
  obtain ⟨j, hj, rfl | rfl⟩ := ρ.mem_darts.1 he
  · exact ⟨ρ.tail_d j hj ▸ ρ.p_mem_mverts hj.le, ρ.head_mem_mverts hj⟩
  · rw [tail_rev, head_rev]
    exact ⟨ρ.head_mem_mverts hj, ρ.tail_d j hj ▸ ρ.p_mem_mverts hj.le⟩

end HPath

/-- A simple path of `M`, as a path through the holes. -/
def SPath.toH (π : SPath M) : HPath M := ⟨π.k, π.d, π.p, π.tail_d⟩

lemma SPath.toH_darts (π : SPath M) : π.toH.darts = π.darts := rfl

lemma SPath.toH_mverts (π : SPath M) : π.toH.mverts = π.verts := by
  ext v
  rw [HPath.mem_mverts, SPath.verts, SPath.mem_init]
  constructor
  · rintro (⟨j, hj, e⟩ | ⟨j, hj, e⟩)
    · exact ⟨j, hj, e⟩
    · exact ⟨j + 1, hj, by rw [← π.head_d j hj]; exact e⟩
  · rintro ⟨j, hj, e⟩; exact Or.inl ⟨j, hj, e⟩

variable (M) in
/-- **The separator of a recursive step**: a path through the holes (the cycle separator of the
article without one edge, in the graph with the earlier separators contracted), and its parts off
the holes (`segs`): simple paths of `M` whose vertices are the vertices of the path that are not in
a hole (`HSep.SegOK`). The holes the path meets are merged with it into the new hole
(`childHoles`); FixConservationOnPath, the calls of Section 4 and the push-backs run on the
parts (`sepStep`). -/
structure HSep where
  /-- The path through the holes. -/
  path : HPath M
  /-- Its parts off the holes. -/
  segs : List (SPath M)

/-- **A separator that meets no hole**: one simple path, its own only part. -/
def SPath.toSep (π : SPath M) : HSep M := ⟨π.toH, [π]⟩

/-- **The new hole**: the vertices of the path with the holes it meets (the supernode of the
article, which contracts the cycle with the nodes of the earlier separators on it). -/
def newHole (Hs : List (Finset V)) (C : Finset V) : Finset V :=
  C ∪ hunion (Hs.filter fun H => ¬ Disjoint H C)

/-- **The holes of the children**: the holes the separator does not meet, and the new hole. -/
def childHoles (Hs : List (Finset V)) (C : Finset V) : List (Finset V) :=
  Hs.filter (fun H => Disjoint H C) ++ [newHole Hs C]

lemma subset_newHole {Hs : List (Finset V)} {C : Finset V} : C ⊆ newHole Hs C :=
  subset_union_left

lemma mem_newHole {Hs : List (Finset V)} {C : Finset V} {v : V} :
    v ∈ newHole Hs C ↔ v ∈ C ∨ ∃ H ∈ Hs, ¬ Disjoint H C ∧ v ∈ H := by
  rw [newHole, mem_union, mem_hunion]
  simp only [List.mem_filter, decide_eq_true_eq, and_assoc]

lemma hunion_childHoles (Hs : List (Finset V)) (C : Finset V) :
    hunion (childHoles Hs C) = hunion Hs ∪ C := by
  rw [childHoles, hunion_append, newHole]
  ext v
  simp only [mem_union, mem_hunion, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (⟨H, ⟨hH, -⟩, hv⟩ | hv | ⟨H, ⟨hH, -⟩, hv⟩)
    · exact Or.inl ⟨H, hH, hv⟩
    · exact Or.inr hv
    · exact Or.inl ⟨H, hH, hv⟩
  · rintro (⟨H, hH, hv⟩ | hv)
    · by_cases hd : Disjoint H C
      · exact Or.inl ⟨H, ⟨hH, hd⟩, hv⟩
      · exact Or.inr (Or.inr ⟨H, ⟨hH, hd⟩, hv⟩)
    · exact Or.inr (Or.inl hv)

/-- Every hole lies in a hole of the children. -/
lemma exists_childHoles {Hs : List (Finset V)} {C : Finset V} {H : Finset V} (hH : H ∈ Hs) :
    ∃ H' ∈ childHoles Hs C, H ⊆ H' := by
  by_cases hd : Disjoint H C
  · exact ⟨H, List.mem_append_left _ (List.mem_filter.2 ⟨hH, by simpa using hd⟩), subset_rfl⟩
  · refine ⟨newHole Hs C, List.mem_append_right _ (List.mem_singleton_self _), fun v hv => ?_⟩
    exact mem_newHole.2 (Or.inr ⟨H, hH, hd, hv⟩)

lemma subset_hunion_childHoles {Hs : List (Finset V)} {C H : Finset V} (hH : H ∈ Hs) :
    H ⊆ hunion (childHoles Hs C) := by
  obtain ⟨H', h1, h2⟩ := exists_childHoles (C := C) hH
  exact h2.trans (subset_hunion h1)

lemma length_childHoles (Hs : List (Finset V)) (C : Finset V) :
    (childHoles Hs C).length ≤ Hs.length + 1 := by
  rw [childHoles, List.length_append, List.length_singleton]
  have := List.length_filter_le (fun H => decide (Disjoint H C)) Hs
  omega

/-- A separator meeting no hole: the hole is the separator. -/
lemma childHoles_of_disjoint {Hs : List (Finset V)} {C : Finset V}
    (h : Disjoint C (hunion Hs)) : childHoles Hs C = Hs ++ [C] := by
  have h1 : ∀ H ∈ Hs, Disjoint H C := fun H hH =>
    (disjoint_of_subset_right (subset_hunion hH) h).symm
  have e1 : Hs.filter (fun H => Disjoint H C) = Hs :=
    List.filter_eq_self.2 fun H hH => by simpa using h1 H hH
  have e2 : Hs.filter (fun H => ¬ Disjoint H C) = [] :=
    List.filter_eq_nil_iff.2 fun H hH => by simpa using h1 H hH
  rw [childHoles, e1, newHole, e2]
  simp [hunion]

/-- Two distinct holes of a list of pairwise disjoint holes are disjoint. -/
lemma disjoint_of_pairwise {Hs : List (Finset V)} (h : Hs.Pairwise Disjoint) {H H' : Finset V}
    (hH : H ∈ Hs) (hH' : H' ∈ Hs) (hne : H ≠ H') : Disjoint H H' :=
  h.forall hH hH' hne

/-- The holes of the children are pairwise disjoint if the holes are. -/
lemma pairwise_childHoles {Hs : List (Finset V)} {C : Finset V} (h : Hs.Pairwise Disjoint) :
    (childHoles Hs C).Pairwise Disjoint := by
  rw [childHoles, List.pairwise_append]
  refine ⟨h.filter _, List.pairwise_singleton _ _, fun H hH H' hH' => ?_⟩
  rw [List.mem_singleton] at hH'
  subst hH'
  obtain ⟨hH, hd⟩ := List.mem_filter.1 hH
  simp only [decide_eq_true_eq] at hd
  rw [newHole, disjoint_union_right]
  refine ⟨hd, disjoint_left.2 fun v hv hv' => ?_⟩
  obtain ⟨H₂, hH₂, hv₂⟩ := mem_hunion.1 hv'
  obtain ⟨hH₂, hd₂⟩ := List.mem_filter.1 hH₂
  simp only [decide_eq_true_eq] at hd₂
  -- `H₂` meets `C`, `H` does not: they are distinct holes, hence disjoint
  exact disjoint_left.1 (disjoint_of_pairwise h hH hH₂ fun e => hd₂ (e ▸ hd)) hv hv₂

namespace HSep

/-- **The parts of a separator off the holes**: simple paths avoiding the holes, pairwise
disjoint, whose vertices together with the holes are the vertices of the path with the holes. -/
def SegOK (π : HSep M) (Hs : List (Finset V)) : Prop :=
  (∀ σ ∈ π.segs, Disjoint σ.verts (hunion Hs)) ∧ (π.segs.map SPath.verts).Pairwise Disjoint ∧
    hunion Hs ∪ hunion (π.segs.map SPath.verts) = hunion Hs ∪ π.path.mverts

lemma SegOK.subset {π : HSep M} {Hs : List (Finset V)} (h : π.SegOK Hs) {σ : SPath M}
    (hσ : σ ∈ π.segs) : σ.verts ⊆ π.path.mverts := fun v hv => by
  have h1 : v ∈ hunion Hs ∪ hunion (π.segs.map SPath.verts) :=
    mem_union_right _ (subset_hunion (List.mem_map_of_mem hσ) hv)
  rw [h.2.2] at h1
  rcases mem_union.1 h1 with h1 | h1
  · exact absurd h1 (disjoint_left.1 (h.1 σ hσ) hv)
  · exact h1

end HSep

lemma SPath.toSep_segOK (π : SPath M) {Hs : List (Finset V)} (h : Disjoint π.verts (hunion Hs)) :
    π.toSep.SegOK Hs := by
  refine ⟨fun σ hσ => ?_, List.pairwise_singleton _ _, ?_⟩
  · rw [List.mem_singleton.1 hσ]; exact h
  · simp [SPath.toSep, SPath.toH_mverts, hunion]

/-! ### The recursion -/

variable (M) in
/-- A recursive decomposition by separators: a binary tree whose leaves carry pieces and whose
inner nodes carry the separator, a path through the holes with its parts off the holes. -/
inductive ADec where
  | leaf (Q : Finset D)
  | node (l r : ADec) (π : HSep M)

namespace ADec

/-- The piece of a node: the darts of its leaves. -/
def piece : ADec M → Finset D
  | leaf Q => Q
  | node l r _ => l.piece ∪ r.piece

variable (M) in
/-- **The hypotheses on the decomposition**, with the sources `S`, the sinks `T` and the holes
`Hs` of the root: the leaves are closed under reversal, siblings are disjoint, the vertices they
share are terminals, hole vertices or separator vertices, the separator vertices are not
terminals, and its parts off the holes are as in `HSep.SegOK`. The children get the holes
`childHoles`: the holes met by the separator are merged with it. -/
def Good (S T : Finset V) : ADec M → List (Finset V) → Prop
  | leaf Q, _ => RevClosed M Q
  | node l r π, Hs => l.Good S T (childHoles Hs π.path.mverts) ∧
      r.Good S T (childHoles Hs π.path.mverts) ∧
      Disjoint l.piece r.piece ∧ bd M l.piece r.piece ⊆ S ∪ T ∪ (hunion Hs ∪ π.path.mverts) ∧
      Disjoint π.path.mverts (S ∪ T) ∧ π.SegOK Hs

/-- Every leaf of the decomposition has at most `n` darts. -/
def LeafLe (n : ℕ) : ADec M → Prop
  | leaf Q => Q.card ≤ n
  | node l r _ => l.LeafLe n ∧ r.LeafLe n

lemma LeafLe.mono {n n' : ℕ} (h : n ≤ n') : ∀ {τ : ADec M}, τ.LeafLe n → τ.LeafLe n'
  | leaf _, hτ => le_trans hτ h
  | node _ _ _, hτ => ⟨hτ.1.mono h, hτ.2.mono h⟩

lemma Good.revClosed {S T : Finset V} :
    ∀ {τ : ADec M} {Hs : List (Finset V)}, τ.Good M S T Hs → RevClosed M τ.piece
  | leaf _, _, h => h
  | node _ _ _, _, h => RevClosed.union h.1.revClosed h.2.1.revClosed

variable (M) in
/-- **The new holes are simple paths of `M`**: what the subroutines of Section 4 need when they
run on `M` itself (`arun`), with the holes not contracted. It holds when no separator meets a hole
(the new hole is then the separator path); on the piece maps every hole is one vertex, and this
is not needed (`PlanarFlow.BKMNW.arunL_spec`). -/
def PathHoles : ADec M → List (Finset V) → Prop
  | leaf _, _ => True
  | node l r π, Hs => (∃ πH : SPath M, πH.verts = newHole Hs π.path.mverts) ∧
      l.PathHoles (childHoles Hs π.path.mverts) ∧ r.PathHoles (childHoles Hs π.path.mverts)

end ADec

variable (M) in
/-- **The subroutines of Algorithm 1**, as functions to be supplied by an implementation. The
first argument of each is the capacity function of the piece. -/
structure NodeOracles where
  /-- The solver at the leaves (sources, sinks, holes). -/
  leaf : (D → ℤ) → Finset V → Finset V → Finset V → D → ℤ
  /-- FixConservationOnPath (line 9). -/
  fix : (D → ℤ) → (D → ℤ) → SPath M → D → ℤ
  /-- CycleToSingleSinkLimitedMaxFlow (line 11), from the vertices of the separator path to the
  hole `H`. -/
  c2s : (D → ℤ) → (D → ℤ) → SPath M → Finset V → D → ℤ
  /-- SingleSourceToCycleLimitedMaxFlow (line 12), from the hole `H` to the vertices of the
  separator path. -/
  s2c : (D → ℤ) → (D → ℤ) → SPath M → Finset V → D → ℤ
  /-- Pushing the excess of `X` back to the sources `S` (line 13). -/
  ret : (D → ℤ) → (D → ℤ) → Finset V → Finset V → D → ℤ
  /-- Pushing flow back from the sinks `T` to `X` (line 13). -/
  frm : (D → ℤ) → (D → ℤ) → Finset V → Finset V → D → ℤ

/-- **The specifications of the subroutines of Algorithm 1**, on the pieces of the map `M` with
capacities `u` (each under the preconditions under which the article calls it). -/
structure NodeOracles.Spec (O : NodeOracles M) (u : D → ℤ) : Prop where
  leaf : ∀ Q S T A, RevClosed M Q → Q.card ≤ 2 → Disjoint S T → Disjoint S A → Disjoint T A →
    MSOut M (capOn u Q) S T A (O.leaf (capOn u Q) S T A)
  fix : ∀ P f π, IsPseudo M (capOn u P) f →
    FixOut M (capOn u P) f π.verts (O.fix (capOn u P) f π)
  c2s : ∀ P f (π : SPath M) H, IsPseudo M (capOn u P) f → Disjoint π.verts H →
    (∃ πH : SPath M, πH.verts = H) →
    (∀ v ∈ fwdReach M (capOn u P) f (posSet M f π.verts) π.verts, M.div f v ≤ 0) →
    C2SOut M (capOn u P) f (O.c2s (capOn u P) f π H) π.verts H
  s2c : ∀ P f (π : SPath M) H, IsPseudo M (capOn u P) f → Disjoint π.verts H →
    (∃ πH : SPath M, πH.verts = H) →
    (∀ v ∈ bwdReach M (capOn u P) f (negSet M f π.verts) π.verts, 0 ≤ M.div f v) →
    S2COut M (capOn u P) f (O.s2c (capOn u P) f π H) π.verts H
  ret : ∀ P f X S, IsPseudo M (capOn u P) f → Disjoint X S → (∀ v ∈ X, M.div f v ≤ 0) →
    (∃ W, X ⊆ W ∧ Closed M (capOn u P) f W ∧ ∀ v ∈ W, v ∉ S → v ∉ X → M.div f v = 0) →
    RetOut M (capOn u P) f (O.ret (capOn u P) f X S) X S
  frm : ∀ P f T X, IsPseudo M (capOn u P) f → Disjoint X T → (∀ v ∈ X, 0 ≤ M.div f v) →
    (∃ W, X ⊆ W ∧ Closed M (capOn u P) f (univ \ W) ∧ ∀ v ∈ W, v ∉ T → v ∉ X → M.div f v = 0) →
    FromOut M (capOn u P) f (O.frm (capOn u P) f T X) T X

open Classical in
/-- The loop of lines 10–12 over the holes, skipping the holes that the piece does not touch. -/
noncomputable def holeLoop (O : NodeOracles M) (U : D → ℤ) (P : Finset D) (π : SPath M) :
    List (Finset V) → (D → ℤ) → D → ℤ
  | [], g => g
  | H :: Hs, g => holeLoop O U P π Hs
      (if ∃ v ∈ H, Touch M P v then O.s2c U (O.c2s U g π H) π H else g)

/-- **One recursive step** (lines 9–13 of Algorithm 1), from the sum of the outputs of the two
pieces. -/
noncomputable def nodeStep (O : NodeOracles M) (U : D → ℤ) (S T : Finset V)
    (Hs : List (Finset V)) (P : Finset D) (π : SPath M) (f : D → ℤ) : D → ℤ :=
  let f₂ := holeLoop O U P π Hs (O.fix U f π)
  let f₃ := O.ret U f₂ (posSet M f₂ π.verts) S
  O.frm U f₃ T (negSet M f₃ π.verts)

/-- **One recursive step with a separator in several parts** (lines 9–13 of Algorithm 1 on each
part off the holes in turn): the step `nodeStep` on the first part, with the later parts as holes,
then the same on the later parts. -/
noncomputable def sepStep (O : NodeOracles M) (U : D → ℤ) (S T : Finset V)
    (Hs : List (Finset V)) (P : Finset D) : List (SPath M) → (D → ℤ) → D → ℤ
  | [], f => f
  | π :: πs, f => sepStep O U S T Hs P πs (nodeStep O U S T (Hs ++ πs.map SPath.verts) P π f)

/-- **Algorithm 1**: at a leaf, the leaf solver; at a node, the two recursive calls with the
holes met by the separator merged with it (`childHoles`), then `sepStep` on the parts of the
separator off the holes. -/
noncomputable def arun (O : NodeOracles M) (u : D → ℤ) :
    ADec M → Finset V → Finset V → List (Finset V) → D → ℤ
  | .leaf Q, S, T, Hs => O.leaf (capOn u Q) S T (hunion Hs)
  | .node l r π, S, T, Hs =>
    sepStep O (capOn u (l.piece ∪ r.piece)) S T Hs (l.piece ∪ r.piece) π.segs
      (arun O u l S T (childHoles Hs π.path.mverts) + arun O u r S T (childHoles Hs π.path.mverts))

/-- The loop over the holes preserves the invariant. -/
theorem NInv.loop {O : NodeOracles M} {u : D → ℤ} (hO : O.Spec u) {P : Finset D}
    (hP : RevClosed M P) {S T A : Finset V} {π : SPath M} :
    ∀ (L : List (Finset V)) (Hd : List (Finset V)) (g : D → ℤ), (∀ H ∈ L, H ⊆ A) →
      (∀ H ∈ L, ∃ πH : SPath M, πH.verts = H) →
      Disjoint π.verts A → NInv M (capOn u P) g S T A π.verts Hd →
      NInv M (capOn u P) (holeLoop O (capOn u P) P π L g) S T A π.verts (Hd ++ L) := by
  classical
  intro L
  induction L with
  | nil => intro Hd g _ _ _ h; simpa [holeLoop] using h
  | cons H L ih =>
    intro Hd g hL hLp hCA h
    have hHA : H ⊆ A := hL H (List.mem_cons_self ..)
    have hHp := hLp H (List.mem_cons_self ..)
    have hCH : Disjoint π.verts H := disjoint_of_subset_right hHA hCA
    have h' : NInv M (capOn u P) (if ∃ v ∈ H, Touch M P v then
        O.s2c (capOn u P) (O.c2s (capOn u P) g π H) π H else g) S T A π.verts (Hd ++ [H]) := by
      split_ifs with ht
      · exact h.hole hHA hCH (hO.c2s P g π H h.pseudo hCH hHp)
          (hO.s2c P _ π H (hO.c2s P g π H h.pseudo hCH hHp (by
            intro v hv; obtain ⟨Y, hY1, hY2, hY3⟩ := h.pn
            by_contra hpos
            exact disjoint_left.1 hY2 (fwdReach_sub hY3 hY1 hv)
              (mem_negSet.2 ⟨fwdReach_subset hv, by omega⟩))).pseudo hCH hHp)
      · push Not at ht
        exact h.skip hP hCH ht
    have := ih (Hd ++ [H]) _ (fun H' hH' => hL H' (List.mem_cons_of_mem _ hH'))
      (fun H' hH' => hLp H' (List.mem_cons_of_mem _ hH')) hCA h'
    simpa [holeLoop] using this

/-- **Correctness of one recursive step, from the state after the recursive calls** (Lemmas
A.4–A.10): from a pseudoflow conserved off `S ∪ T ∪ A ∪ C` with no residual path from `S` to
`T ∪ A ∪ C` nor from `A ∪ C ∪ S` to `T` (`A` the holes, `C` the vertices of the separator path),
lines 9–13 give the output of the recursion. -/
theorem nodeStep_core {O : NodeOracles M} {u : D → ℤ} (hO : O.Spec u) {P : Finset D}
    (hP : RevClosed M P) {S T : Finset V} {Hs : List (Finset V)} (π : SPath M)
    (hHs : ∀ H ∈ Hs, ∃ πH : SPath M, πH.verts = H)
    (hC : Disjoint π.verts (S ∪ T ∪ hunion Hs)) {f : D → ℤ}
    (hps : IsPseudo M (capOn u P) f)
    (hcons : ∀ v, v ∉ S → v ∉ T → v ∉ hunion Hs ∪ π.verts → M.div f v = 0)
    (h1 : NoPath M (capOn u P) f S (T ∪ (hunion Hs ∪ π.verts)))
    (h2 : NoPath M (capOn u P) f ((hunion Hs ∪ π.verts) ∪ S) T) :
    MSOut M (capOn u P) S T (hunion Hs) (nodeStep O (capOn u P) S T Hs P π f) := by
  classical
  generalize hCdef : π.verts = C at hC hcons h1 h2
  have hSC : Disjoint S C :=
    (disjoint_of_subset_right (subset_union_left.trans subset_union_left) hC).symm
  have hTC : Disjoint T C :=
    (disjoint_of_subset_right (subset_union_right.trans subset_union_left) hC).symm
  have hCA : Disjoint C (hunion Hs) := disjoint_of_subset_right subset_union_right hC
  have hfix := hO.fix P f π hps
  rw [hCdef] at hfix
  have n0 := NInv.ofFix (A := hunion Hs) hps hcons h1 h2 hfix
  have n1 := NInv.loop (π := π) hO hP Hs [] _ (fun H hH => subset_hunion hH) hHs
    (hCdef ▸ hCA) (hCdef ▸ n0)
  rw [hCdef] at n1
  simp only [List.nil_append] at n1
  unfold nodeStep
  rw [hCdef]
  generalize hf₂ :
    holeLoop O (capOn u P) P π Hs (O.fix (capOn u P) f π) = f₂ at n1
  -- the preconditions of line 13
  have o1 := hO.ret P f₂ (posSet M f₂ C) S n1.pseudo
    (disjoint_of_subset_left posSet_subset hSC.symm)
    (fun v hv => (mem_posSet.1 hv).2.le) (by
      obtain ⟨W, hW1, hW2, hW3⟩ := ((n1.acsT.mono (posSet_subset.trans
        (subset_union_right.trans subset_union_left)) subset_rfl).union_right
        (noPath_hunion_right fun H hH => (n1.done H hH).1)).union_right n1.pn
      refine ⟨W, hW1, hW3, fun v hv hvS hvX => ?_⟩
      have hvT : v ∉ T := fun h => disjoint_left.1 hW2 hv (by simp [h])
      have hvA : v ∉ hunion Hs := fun h => disjoint_left.1 hW2 hv (by simp [h])
      by_cases hvC : v ∈ C
      · by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact hvX (mem_posSet.2 ⟨hvC, hlt⟩)
        · exact disjoint_left.1 hW2 hv (by simp [mem_negSet.2 ⟨hvC, hlt⟩])
      · exact n1.cons v hvS hvT (by simp [hvA, hvC]))
  generalize hf₃ : O.ret (capOn u P) f₂ (posSet M f₂ C) S = f₃ at o1
  -- the preconditions of the push back from the sinks
  have hz1 := o1.eq
  have hneg_eq : negSet M f₃ C = negSet M f₂ C := by
    ext v; simp only [mem_negSet]
    constructor
    · rintro ⟨hvC, hlt⟩
      have hn : v ∉ posSet M f₂ C := fun h' => by rw [o1.zero v h'] at hlt; omega
      rw [hz1 v hn (disjoint_right.1 hSC hvC)] at hlt; exact ⟨hvC, hlt⟩
    · rintro ⟨hvC, hlt⟩
      have hn : v ∉ posSet M f₂ C := fun h' => by have := (mem_posSet.1 h').2; omega
      rw [hz1 v hn (disjoint_right.1 hSC hvC)]; exact ⟨hvC, hlt⟩
  have o2 := hO.frm P f₃ T (negSet M f₃ C) o1.pseudo
    (disjoint_of_subset_left negSet_subset hTC.symm)
    (fun v hv => (mem_negSet.1 hv).2.le) (by
      -- after the first push, no residual path from `S ∪ A` to the vertices with negative inflow
      have hsn : NoPath M (capOn u P) f₃ (S ∪ hunion Hs) (negSet M f₂ C) := by
        have a1 : NoPath M (capOn u P) f₂ ((S ∪ hunion Hs) ∪ posSet M f₂ C)
            (negSet M f₂ C) :=
          ((n1.sTAC.mono subset_rfl (negSet_subset.trans (subset_union_right.trans
            subset_union_right))).union_left
            (noPath_hunion_left fun H hH => (n1.done H hH).2)).union_left
            n1.pn
        exact a1.src n1.pseudo o1.pseudo o1.eq o1.src
      obtain ⟨Y, hY1, hY2, hY3⟩ := hsn
      refine ⟨univ \ Y, ?_, by simpa using hY3, fun v hv hvT hvX => ?_⟩
      · rw [hneg_eq]; intro v hv; simp only [mem_sdiff, mem_univ, true_and]
        exact disjoint_right.1 hY2 hv
      · have hvY : v ∉ Y := by simpa using hv
        have hvS : v ∉ S := fun h => hvY (hY1 (mem_union_left _ h))
        have hvA : v ∉ hunion Hs := fun h => hvY (hY1 (mem_union_right _ h))
        by_cases hp : v ∈ posSet M f₂ C
        · exact o1.zero v hp
        · rw [hz1 v hp hvS]
          by_cases hvC : v ∈ C
          · by_contra hne
            rcases lt_or_gt_of_ne hne with hlt | hlt
            · exact hp (mem_posSet.2 ⟨hvC, hlt⟩)
            · rw [hneg_eq] at hvX; exact hvX (mem_negSet.2 ⟨hvC, hlt⟩)
          · exact n1.cons v hvS hvT (by simp [hvA, hvC]))
  simp only [hf₃]
  exact n1.finish hSC hTC o1 o2

/-- **Correctness of one recursive step**, with the two pieces `P`, `Q` solved recursively with
the separator path as a new hole. -/
theorem nodeStep_spec {O : NodeOracles M} {u : D → ℤ} (hO : O.Spec u) {P Q : Finset D}
    (hP : RevClosed M P) (hQ : RevClosed M Q) (hPQ : Disjoint P Q) {S T : Finset V}
    {Hs : List (Finset V)} (π : SPath M) (hST : Disjoint S T)
    (hSA : Disjoint S (hunion Hs)) (hTA : Disjoint T (hunion Hs))
    (hHs : ∀ H ∈ Hs, ∃ πH : SPath M, πH.verts = H)
    (hbd : bd M P Q ⊆ S ∪ T ∪ (hunion Hs ∪ π.verts))
    (hC : Disjoint π.verts (S ∪ T ∪ hunion Hs)) {f g : D → ℤ}
    (hf : MSOut M (capOn u P) S T (hunion Hs ∪ π.verts) f)
    (hg : MSOut M (capOn u Q) S T (hunion Hs ∪ π.verts) g) :
    MSOut M (capOn u (P ∪ Q)) S T (hunion Hs) (nodeStep O (capOn u (P ∪ Q)) S T Hs (P ∪ Q) π
      (f + g)) := by
  have hSC : Disjoint S π.verts :=
    (disjoint_of_subset_right (subset_union_left.trans subset_union_left) hC).symm
  obtain ⟨hps, hcons, h1, h2⟩ := combine hP hQ hPQ hST
    (disjoint_union_right.2 ⟨hSA, hSC⟩) hbd hf hg
  exact nodeStep_core hO (hP.union hQ) π hHs hC hps hcons h1 h2

/-- **Correctness of a recursive step with a separator in several parts** (`sepStep`): from the
state after the recursive calls, with the parts `πs` (simple paths avoiding the terminals and the
holes, pairwise disjoint) and `C` the union of their vertices, the output of the recursion. -/
theorem sepStep_spec {O : NodeOracles M} {u : D → ℤ} (hO : O.Spec u) {P : Finset D}
    (hP : RevClosed M P) {S T : Finset V} :
    ∀ (πs : List (SPath M)) (Hs : List (Finset V)) (f : D → ℤ),
      (∀ H ∈ Hs, ∃ πH : SPath M, πH.verts = H) →
      (∀ π ∈ πs, Disjoint π.verts (S ∪ T ∪ hunion Hs)) → (πs.map SPath.verts).Pairwise Disjoint →
      IsPseudo M (capOn u P) f →
      (∀ v, v ∉ S → v ∉ T → v ∉ hunion Hs ∪ hunion (πs.map SPath.verts) → M.div f v = 0) →
      NoPath M (capOn u P) f S (T ∪ (hunion Hs ∪ hunion (πs.map SPath.verts))) →
      NoPath M (capOn u P) f ((hunion Hs ∪ hunion (πs.map SPath.verts)) ∪ S) T →
      MSOut M (capOn u P) S T (hunion Hs) (sepStep O (capOn u P) S T Hs P πs f)
  | [], Hs, f, _, _, _, hps, hcons, h1, h2 => by
    have e : hunion Hs ∪ hunion (([] : List (SPath M)).map SPath.verts) = hunion Hs := by
      simp [hunion]
    rw [e] at hcons h1 h2
    exact ⟨hps, hcons, h1.mono subset_rfl subset_union_left,
      h1.mono subset_rfl subset_union_right, h2.mono subset_union_left subset_rfl⟩
  | π :: πs, Hs, f, hHs, hπs, hpw, hps, hcons, h1, h2 => by
    rw [List.map_cons, List.pairwise_cons] at hpw
    have hπ : Disjoint π.verts (S ∪ T ∪ hunion Hs) := hπs π (List.mem_cons_self ..)
    have hπs' : ∀ π' ∈ πs, Disjoint π'.verts (S ∪ T ∪ hunion Hs) := fun π' h =>
      hπs π' (List.mem_cons_of_mem _ h)
    have hR : Disjoint π.verts (hunion (πs.map SPath.verts)) :=
      disjoint_left.2 fun v hv hv' => by
        obtain ⟨H, hH, hvH⟩ := mem_hunion.1 hv'
        exact disjoint_left.1 (hpw.1 H hH) hv hvH
    have e : hunion (Hs ++ πs.map SPath.verts) ∪ π.verts =
        hunion Hs ∪ hunion ((π :: πs).map SPath.verts) := by
      rw [hunion_append', List.map_cons, hunion_cons]
      ext v; simp only [mem_union]; tauto
    have hHs' : ∀ H ∈ Hs ++ πs.map SPath.verts, ∃ πH : SPath M, πH.verts = H := by
      intro H hH
      rcases List.mem_append.1 hH with hH | hH
      · exact hHs H hH
      · obtain ⟨π', -, rfl⟩ := List.mem_map.1 hH; exact ⟨π', rfl⟩
    have hC : Disjoint π.verts (S ∪ T ∪ hunion (Hs ++ πs.map SPath.verts)) := by
      rw [hunion_append', ← union_assoc]
      exact disjoint_union_right.2 ⟨hπ, hR⟩
    rw [← e] at hcons h1 h2
    have o := nodeStep_core hO hP π hHs' hC hps hcons h1 h2
    have e' : hunion (Hs ++ πs.map SPath.verts) = hunion Hs ∪ hunion (πs.map SPath.verts) :=
      hunion_append' _ _
    rw [e'] at o
    exact sepStep_spec hO hP πs Hs _ hHs hπs' hpw.2 o.pseudo o.cons (o.st.union_right o.sa)
      (o.at'.union_left o.st)

/-- **Correctness of Algorithm 1**: if the subroutines meet their specifications, the
decomposition is good and every new hole is a simple path of `M` (`ADec.PathHoles`, needed by
the subroutines of Section 4 on `M`), the recursion meets the specification `MSOut` at every
node. -/
theorem arun_spec {O : NodeOracles M} {u : D → ℤ} (hO : O.Spec u) {S T : Finset V}
    (hST : Disjoint S T) :
    ∀ (τ : ADec M) (Hs : List (Finset V)), τ.Good M S T Hs → τ.PathHoles M Hs → τ.LeafLe 2 →
      Disjoint S (hunion Hs) → Disjoint T (hunion Hs) →
      (∀ H ∈ Hs, ∃ πH : SPath M, πH.verts = H) →
      MSOut M (capOn u τ.piece) S T (hunion Hs) (arun O u τ S T Hs)
  | .leaf Q, Hs, h, _, hl2, hSA, hTA, _ => hO.leaf Q S T _ h hl2 hST hSA hTA
  | .node l r π, Hs, h, hph, hl2, hSA, hTA, hHs => by
    obtain ⟨hl, hr, hlr, hbd, hC, hseg⟩ := h
    obtain ⟨hph0, hphl, hphr⟩ := hph
    have hSC : Disjoint S π.path.mverts :=
      (disjoint_of_subset_right subset_union_left hC).symm
    have hTC : Disjoint T π.path.mverts :=
      (disjoint_of_subset_right subset_union_right hC).symm
    have hSA' : Disjoint S (hunion (childHoles Hs π.path.mverts)) := by
      rw [hunion_childHoles]; exact disjoint_union_right.2 ⟨hSA, hSC⟩
    have hTA' : Disjoint T (hunion (childHoles Hs π.path.mverts)) := by
      rw [hunion_childHoles]; exact disjoint_union_right.2 ⟨hTA, hTC⟩
    have hHs' : ∀ H ∈ childHoles Hs π.path.mverts, ∃ πH : SPath M, πH.verts = H := by
      intro H hH
      rcases List.mem_append.1 hH with hH | hH
      · exact hHs H (List.mem_filter.1 hH).1
      · obtain ⟨πH, e⟩ := hph0; exact ⟨πH, e.trans (List.mem_singleton.1 hH).symm⟩
    have il := arun_spec hO hST l _ hl hphl hl2.1 hSA' hTA' hHs'
    have ir := arun_spec hO hST r _ hr hphr hl2.2 hSA' hTA' hHs'
    rw [hunion_childHoles, ← hseg.2.2] at il ir
    rw [← hseg.2.2] at hbd
    have hSC' : Disjoint S (hunion Hs ∪ hunion (π.segs.map SPath.verts)) := by
      rw [hseg.2.2]; exact disjoint_union_right.2 ⟨hSA, hSC⟩
    obtain ⟨hps, hcons, h1, h2⟩ := combine hl.revClosed hr.revClosed hlr hST hSC' hbd il ir
    refine sepStep_spec hO (hl.revClosed.union hr.revClosed) π.segs Hs _ hHs
      (fun σ hσ => ?_) hseg.2.1 hps hcons h1 h2
    have h1 := hseg.subset hσ
    exact disjoint_union_right.2 ⟨disjoint_union_right.2
      ⟨disjoint_of_subset_left h1 hSC.symm, disjoint_of_subset_left h1 hTC.symm⟩, hseg.1 σ hσ⟩

end BKMNW

end PlanarFlow
