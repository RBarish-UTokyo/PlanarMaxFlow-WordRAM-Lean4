module

public import PlanarFlow.Plane.Feasible

/-!
# Flows on darts with several sources and sinks

This file sets up the problem solved by the algorithm of Borradaile, Klein, Mozes, Nussbaum and
Wulff-Nilsen (SIAM J. Comput. 46(4), 2017): a maximum flow from a set `S` of sources to a set `T`
of sinks in a directed plane graph with integer capacities.

The graph is a combinatorial map `M` on darts (`PlanarFlow.CombMap`), with a capacity `u d` on
every dart; an arc `a → b` of capacity `c` is a dart of capacity `c` whose reverse has capacity
`0`. As in the article, a flow is an antisymmetric function on the darts.

* `IsPseudo u f`: `f` is antisymmetric and `f ≤ u` (a *pseudoflow*: conservation is not required).
  The residual capacity of a dart is `u d - f d`; the residual graph of `f` is the same map with
  the capacities `u - f`.
* `IsFlow u S T f`: a pseudoflow conserved at every vertex that is neither a source nor a sink.
* `val S f`: the net flow out of the sources.
* `cutCap u X`: the total capacity of the darts leaving `X`.
* `Closed u f X`: every dart leaving `X` is saturated, i.e. no residual dart leaves `X`.
* `Solves u S T f`: `f` is a flow, a closed set separates the sources from the sinks (so `f` is
  a maximum flow, `Solves.isMax`), and no sink has positive net outflow.
* `Realizable u b`: some pseudoflow has net outflow `b v` at every vertex `v`.
* `Tight u b X`: the total of `b` over `X` equals the capacity of `X`.

A set is closed for a pseudoflow exactly when it is tight for its net outflows
(`tight_iff_closed`): the absence of residual paths depends on the net outflows only. In the
correctness proof of the algorithm (`PlanarFlow/BKMNW/Hassin.lean`, `PlanarFlow/BKMNW/Algorithm.lean`)
this is the form in which the article's statements "no residual path from `X` to `Y`" are
proved, and it contains Lemma A.1 of the article (adding a circulation changes no residual
reachability).

## Main results

* `sum_div_eq_out`: the net outflow of a set is the flow on the darts leaving it.
* `sum_div_le_cutCap`, `val_le_cutCap`: weak duality.
* `tight_iff_closed`.
* `Solves.isMax`: a certified flow is a maximum flow.
* `tight_of_le`, `Tight.union`: tightness is preserved by any change of the net outflows that
  does not decrease the total over the set; tight sets are closed under union.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable (M : CombMap D V F)

/-- The capacities restricted to a set `P` of darts: `0` outside `P`. -/
def capOn (u : D → ℤ) (P : Finset D) (d : D) : ℤ := if d ∈ P then u d else 0

/-- A set of darts closed under reversal (a set of edges). -/
def RevClosed (P : Finset D) : Prop := ∀ d ∈ P, M.rev d ∈ P

/-- A pseudoflow: antisymmetric and within the capacities. -/
structure IsPseudo (u f : D → ℤ) : Prop where
  antisymm : M.IsAntisymm f
  le_cap : ∀ d, f d ≤ u d

/-- A flow from the sources `S` to the sinks `T`. -/
structure IsFlow (u : D → ℤ) (S T : Finset V) (f : D → ℤ) : Prop extends IsPseudo M u f where
  conserve : ∀ v, v ∉ S → v ∉ T → M.div f v = 0

/-- The value of a flow: the net flow out of the sources. -/
def val (S : Finset V) (f : D → ℤ) : ℤ := ∑ v ∈ S, M.div f v

/-- The capacity of a set of vertices: the total capacity of the darts leaving it. -/
def cutCap (u : D → ℤ) (X : Finset V) : ℤ := ∑ d with M.tail d ∈ X ∧ M.head d ∉ X, u d

/-- No residual dart leaves `X`: every dart leaving `X` is saturated. -/
def Closed (u f : D → ℤ) (X : Finset V) : Prop :=
  ∀ d, M.tail d ∈ X → M.head d ∉ X → f d = u d

/-- A maximum flow. -/
def IsMax (u : D → ℤ) (S T : Finset V) (f : D → ℤ) : Prop :=
  IsFlow M u S T f ∧ ∀ g, IsFlow M u S T g → val M S g ≤ val M S f

/-- A certified maximum flow: a flow, a closed set containing the sources and no sink, and no
sink with positive net outflow. -/
structure Solves (u : D → ℤ) (S T : Finset V) (f : D → ℤ) : Prop where
  flow : IsFlow M u S T f
  cert : ∃ X, S ⊆ X ∧ Disjoint X T ∧ Closed M u f X
  sink : ∀ t ∈ T, M.div f t ≤ 0

/-- The net outflows `b` are those of a pseudoflow. -/
def Realizable (u : D → ℤ) (b : V → ℤ) : Prop :=
  ∃ h, IsPseudo M u h ∧ ∀ v, M.div h v = b v

/-- The total of `b` over `X` is the capacity of `X`. -/
def Tight (u : D → ℤ) (b : V → ℤ) (X : Finset V) : Prop := ∑ v ∈ X, b v = cutCap M u X

variable {M}

/-! ### Net outflows of sets -/

lemma div_add' (f g : D → ℤ) (v : V) : M.div (f + g) v = M.div f v + M.div g v := by
  simp [CombMap.div, sum_add_distrib]

lemma div_sub' (f g : D → ℤ) (v : V) : M.div (f - g) v = M.div f v - M.div g v := by
  simp [CombMap.div, sum_sub_distrib]

/-- The sum of an antisymmetric function over a set of darts closed under reversal vanishes. -/
lemma sum_antisymm_eq_zero {f : D → ℤ} (hf : M.IsAntisymm f) (A : Finset D)
    (hA : ∀ d ∈ A, M.rev d ∈ A) : ∑ d ∈ A, f d = 0 :=
  sum_involution (fun d _ => M.rev d) (fun d _ => by rw [hf d]; ring)
    (fun d _ _ => M.rev_ne d) (fun d hd => hA d hd) (fun d _ => M.rev_rev d)

lemma sum_div_eq_tail (f : D → ℤ) (X : Finset V) :
    ∑ v ∈ X, M.div f v = ∑ d with M.tail d ∈ X, f d := by
  unfold CombMap.div
  rw [← sum_fiberwise_of_maps_to (s := univ.filter (fun d => M.tail d ∈ X)) (t := X)
    (g := M.tail) (by simp)]
  refine sum_congr rfl fun v hv => ?_
  congr 1; ext d; simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro rfl; exact ⟨hv, rfl⟩
  · exact fun h => h.2

/-- **The net outflow of a set** of an antisymmetric function is the flow on the darts leaving
it: the darts inside the set cancel. -/
theorem sum_div_eq_out {f : D → ℤ} (hf : M.IsAntisymm f) (X : Finset V) :
    ∑ v ∈ X, M.div f v = ∑ d with M.tail d ∈ X ∧ M.head d ∉ X, f d := by
  rw [sum_div_eq_tail]
  have h : ∑ d with M.tail d ∈ X, f d =
      ∑ d with M.tail d ∈ X ∧ M.head d ∈ X, f d + ∑ d with M.tail d ∈ X ∧ M.head d ∉ X, f d := by
    rw [← sum_union]
    · congr 1; ext d; simp only [mem_filter, mem_univ, true_and, mem_union]; tauto
    · rw [disjoint_filter]; intro d _ h; tauto
  rw [h, sum_antisymm_eq_zero hf _ (fun d hd => by
    simp only [mem_filter, mem_univ, true_and, CombMap.tail_rev, CombMap.head_rev] at hd ⊢
    exact ⟨hd.2, hd.1⟩), zero_add]

/-- **Weak duality** for pseudoflows: the net outflow of a set is at most its capacity. -/
theorem sum_div_le_cutCap {u f : D → ℤ} (hf : IsPseudo M u f) (X : Finset V) :
    ∑ v ∈ X, M.div f v ≤ cutCap M u X := by
  rw [sum_div_eq_out hf.antisymm]
  exact sum_le_sum fun d _ => hf.le_cap d

/-- A set is closed for a pseudoflow exactly when its net outflow equals its capacity. -/
theorem tight_iff_closed {u f : D → ℤ} (hf : IsPseudo M u f) (X : Finset V) :
    ∑ v ∈ X, M.div f v = cutCap M u X ↔ Closed M u f X := by
  rw [sum_div_eq_out hf.antisymm, cutCap]
  constructor
  · intro h d hd1 hd2
    have h0 : ∑ d with M.tail d ∈ X ∧ M.head d ∉ X, (u d - f d) = 0 := by
      rw [sum_sub_distrib, h, sub_self]
    have := (sum_eq_zero_iff_of_nonneg (fun d _ => sub_nonneg.2 (hf.le_cap d))).1 h0 d
      (by simp [hd1, hd2])
    linarith
  · intro h
    exact sum_congr rfl fun d hd => by
      simp only [mem_filter, mem_univ, true_and] at hd; exact h d hd.1 hd.2

/-- The value of a flow is the net outflow of any set containing the sources and no sink. -/
theorem val_eq_sum {u f : D → ℤ} {S T X : Finset V} (hf : IsFlow M u S T f) (hSX : S ⊆ X)
    (hXT : Disjoint X T) : val M S f = ∑ v ∈ X, M.div f v :=
  sum_subset hSX fun v hvX hvS => hf.conserve v hvS (disjoint_left.1 hXT hvX)

/-- **Weak duality**: the value of a flow is at most the capacity of a cut. -/
theorem val_le_cutCap {u f : D → ℤ} {S T X : Finset V} (hf : IsFlow M u S T f) (hSX : S ⊆ X)
    (hXT : Disjoint X T) : val M S f ≤ cutCap M u X := by
  rw [val_eq_sum hf hSX hXT]; exact sum_div_le_cutCap hf.toIsPseudo X

/-- **A certified flow is maximum**, and its value is the capacity of the certifying cut. -/
theorem Solves.isMax {u f : D → ℤ} {S T : Finset V} (h : Solves M u S T f) : IsMax M u S T f := by
  obtain ⟨X, hSX, hXT, hX⟩ := h.cert
  refine ⟨h.flow, fun g hg => ?_⟩
  rw [val_eq_sum h.flow hSX hXT, (tight_iff_closed h.flow.toIsPseudo X).2 hX]
  exact val_le_cutCap hg hSX hXT

/-- The value of a certified flow is the capacity of a cut. -/
theorem Solves.val_eq {u f : D → ℤ} {S T : Finset V} (h : Solves M u S T f) :
    ∃ X, S ⊆ X ∧ Disjoint X T ∧ val M S f = cutCap M u X := by
  obtain ⟨X, hSX, hXT, hX⟩ := h.cert
  exact ⟨X, hSX, hXT, by rw [val_eq_sum h.flow hSX hXT, (tight_iff_closed h.flow.toIsPseudo X).2 hX]⟩

/-! ### Net outflows -/

lemma Realizable.sum_le {u : D → ℤ} {b : V → ℤ} (hb : Realizable M u b) (X : Finset V) :
    ∑ v ∈ X, b v ≤ cutCap M u X := by
  obtain ⟨h, hh, hdiv⟩ := hb
  simp only [← hdiv]; exact sum_div_le_cutCap hh X

lemma Realizable.sum_eq_zero {u : D → ℤ} {b : V → ℤ} (hb : Realizable M u b) :
    ∑ v, b v = 0 := by
  obtain ⟨h, hh, hdiv⟩ := hb
  simp only [← hdiv]; exact M.sum_div hh.antisymm

lemma realizable_div {u f : D → ℤ} (hf : IsPseudo M u f) : Realizable M u (M.div f) :=
  ⟨f, hf, fun _ => rfl⟩

/-- A tight set for the net outflows of a pseudoflow is closed for it. -/
lemma Tight.closed {u f : D → ℤ} {X : Finset V} (hf : IsPseudo M u f)
    (h : Tight M u (M.div f) X) : Closed M u f X := (tight_iff_closed hf X).1 h

/-- **Tightness is preserved** by any realizable change of the net outflows that does not
decrease their total over the set. -/
theorem tight_of_le {u : D → ℤ} {b b' : V → ℤ} {X : Finset V} (hb' : Realizable M u b')
    (h : Tight M u b X) (hle : ∑ v ∈ X, b v ≤ ∑ v ∈ X, b' v) : Tight M u b' X :=
  le_antisymm (hb'.sum_le X) (h ▸ hle)

/-- The union of two closed sets is closed. -/
lemma Closed.union {u f : D → ℤ} {X Y : Finset V} (hX : Closed M u f X) (hY : Closed M u f Y) :
    Closed M u f (X ∪ Y) := by
  intro d hd1 hd2
  rw [mem_union] at hd1 hd2
  push Not at hd2
  rcases hd1 with h | h
  · exact hX d h hd2.1
  · exact hY d h hd2.2

/-- The union of two tight sets is tight. -/
theorem Tight.union {u : D → ℤ} {b : V → ℤ} {X Y : Finset V} (hb : Realizable M u b)
    (hX : Tight M u b X) (hY : Tight M u b Y) : Tight M u b (X ∪ Y) := by
  obtain ⟨h, hh, hdiv⟩ := hb
  have e : b = M.div h := funext fun v => (hdiv v).symm
  subst e
  exact (tight_iff_closed hh _).2 (((tight_iff_closed hh X).1 hX).union ((tight_iff_closed hh Y).1 hY))

/-- The change of a total when the function changes at one point only. -/
lemma sum_eq_add_single {b b' : V → ℤ} {c : V} {X : Finset V}
    (h : ∀ v ∈ X, v ≠ c → b' v = b v) :
    ∑ v ∈ X, b' v = ∑ v ∈ X, b v + if c ∈ X then b' c - b c else 0 := by
  rw [← sub_eq_iff_eq_add', ← sum_sub_distrib]
  split_ifs with hc
  · rw [sum_eq_single c (fun v hv hvc => by rw [h v hv hvc, sub_self]) (fun h => absurd hc h)]
  · exact sum_eq_zero fun v hv => by rw [h v hv (fun e => hc (e ▸ hv)), sub_self]

/-! ### Pieces -/

variable {u : D → ℤ}

/-- A pseudoflow within the capacities of a piece closed under reversal vanishes outside it. -/
lemma IsPseudo.eq_zero_of_not_mem {P : Finset D} (hP : RevClosed M P) {f : D → ℤ}
    (hf : IsPseudo M (capOn u P) f) {d : D} (hd : d ∉ P) : f d = 0 := by
  have h1 := hf.le_cap d
  have h2 := hf.le_cap (M.rev d)
  have hrd : M.rev d ∉ P := fun h => hd (by simpa [M.rev_rev] using hP _ h)
  simp only [capOn, hd, hrd, ite_false] at h1 h2
  rw [hf.antisymm d] at h2
  linarith

/-- A vertex touched by a set of darts: the tail of one of them. -/
def Touch (M : CombMap D V F) (P : Finset D) (v : V) : Prop := ∃ d ∈ P, M.tail d = v

/-- The boundary vertices of two pieces: those touched by both. -/
noncomputable def bd (M : CombMap D V F) (P Q : Finset D) : Finset V := by
  classical exact univ.filter fun v => Touch M P v ∧ Touch M Q v

lemma mem_bd {P Q : Finset D} {v : V} : v ∈ bd M P Q ↔ Touch M P v ∧ Touch M Q v := by
  classical
  unfold bd; simp

/-- The net outflow, at a vertex not touched by the piece, of a pseudoflow within the capacities
of the piece is zero. -/
lemma IsPseudo.div_eq_zero {P : Finset D} (hP : RevClosed M P) {f : D → ℤ}
    (hf : IsPseudo M (capOn u P) f) {v : V} (hv : ¬ Touch M P v) : M.div f v = 0 :=
  sum_eq_zero fun d hd => hf.eq_zero_of_not_mem hP fun h => hv ⟨d, h, by simpa using hd⟩

lemma RevClosed.union {P Q : Finset D} (hP : RevClosed M P) (hQ : RevClosed M Q) :
    RevClosed M (P ∪ Q) := fun d hd => by
  rcases mem_union.1 hd with h | h
  · exact mem_union_left _ (hP d h)
  · exact mem_union_right _ (hQ d h)

lemma capOn_univ : capOn u (univ : Finset D) = u := funext fun d => by simp [capOn]

/-- The sum of pseudoflows within the capacities of two disjoint pieces is a pseudoflow within
the capacities of their union. -/
lemma IsPseudo.add_piece {P Q : Finset D} (hP : RevClosed M P) (hQ : RevClosed M Q)
    (hPQ : Disjoint P Q) {f g : D → ℤ} (hf : IsPseudo M (capOn u P) f)
    (hg : IsPseudo M (capOn u Q) g) : IsPseudo M (capOn u (P ∪ Q)) (f + g) := by
  refine ⟨fun d => by simp [hf.antisymm d, hg.antisymm d]; ring, fun d => ?_⟩
  simp only [Pi.add_apply]
  by_cases hdP : d ∈ P
  · have hdQ : d ∉ Q := disjoint_left.1 hPQ hdP
    rw [hg.eq_zero_of_not_mem hQ hdQ, add_zero]
    have := hf.le_cap d
    simp only [capOn, hdP, ite_true, mem_union, true_or] at this ⊢
    exact this
  · by_cases hdQ : d ∈ Q
    · rw [hf.eq_zero_of_not_mem hP hdP, zero_add]
      have := hg.le_cap d
      simp only [capOn, hdQ, ite_true, mem_union, or_true] at this ⊢
      exact this
    · rw [hf.eq_zero_of_not_mem hP hdP, hg.eq_zero_of_not_mem hQ hdQ]
      simp [capOn, hdP, hdQ]

end BKMNW

end PlanarFlow
