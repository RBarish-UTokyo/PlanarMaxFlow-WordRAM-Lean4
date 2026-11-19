module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Shortest paths with negative lengths: potentials and the Bellman–Ford bound

Let `X` be a finite set of vertices and `A` a finite set of arcs, the arc `a` going from `src a`
to `dst a` with an integer length `len a` (possibly negative). A *feasible potential* is a
function `p` on the vertices with `p (dst a) ≤ p (src a) + len a` for every arc.

* `PlanarFlow.Digraph.bf k`: the Bellman–Ford values after `k` rounds, started from `0` at every
  vertex (equivalently, from a virtual source joined to every vertex by an arc of length `0`):
  `bf k y` is the least length of a walk with at most `k` arcs ending at `y`.
* `PlanarFlow.Digraph.bf_succ_card`: **if a feasible potential exists, the values are stable after
  `|X|` rounds**, and `bf |X|` is itself a feasible potential (`isPot_bf_card`). The proof
  follows a vertex whose value still improves at round `k` back through vertices improved at
  every earlier round; after more than `|X|` rounds two of them coincide, and the potential shows
  that the closed walk between them cannot have improved anything.
* `PlanarFlow.Digraph.exists_pot_iff`: **a feasible potential exists if and only if there is no
  closed walk of negative length.**
* `relax`: the relaxation of an arc, and the facts that make the in-place (Gauss–Seidel) variant
  used by programs at least as fast as the rounds `bf`: during round `k + 1`, relaxing the arcs in
  any order, the values stay between `bf |X|` (when a potential exists) and `bf k`, and at the end
  of the round they are at most `bf (k + 1)` (`le_bf_succ_of_round`).

## References

* R. Bellman, *On a routing problem*, Quart. Appl. Math. 16 (1958), 87–90.
* L. R. Ford, *Network flow theory*, RAND Corporation P-923 (1956).
* E. F. Moore, *The shortest path through a maze*, Proc. Internat. Sympos. Switching Theory
  (1959), 285–292.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

open Finset

/-- A digraph with integer arc lengths: arcs `A` between vertices `X`. -/
structure Digraph (X A : Type*) where
  /-- The start of an arc. -/
  src : A → X
  /-- The end of an arc. -/
  dst : A → X
  /-- The length of an arc. -/
  len : A → ℤ

namespace Digraph

variable {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A]
variable (G : Digraph X A)

/-- A feasible potential. -/
def IsPot (p : X → ℤ) : Prop := ∀ a, p (G.dst a) ≤ p (G.src a) + G.len a

/-- The candidates for the value of `y` in the next round. -/
def cand (b : X → ℤ) (y : X) : Finset ℤ :=
  insert (b y) ((univ.filter fun a => G.dst a = y).image fun a => b (G.src a) + G.len a)

/-- The Bellman–Ford values after `k` rounds, from `0` everywhere. -/
def bf : ℕ → X → ℤ
  | 0 => fun _ => 0
  | k + 1 => fun y => (G.cand (bf k) y).min' (insert_nonempty _ _)

lemma bf_succ_le (k : ℕ) (y : X) : G.bf (k + 1) y ≤ G.bf k y :=
  min'_le _ _ (mem_insert_self _ _)

lemma bf_succ_le_arc (k : ℕ) (a : A) : G.bf (k + 1) (G.dst a) ≤ G.bf k (G.src a) + G.len a :=
  min'_le _ _ (mem_insert_of_mem (mem_image.2 ⟨a, by simp, rfl⟩))

lemma bf_succ_cases (k : ℕ) (y : X) : G.bf (k + 1) y = G.bf k y ∨
    ∃ a, G.dst a = y ∧ G.bf (k + 1) y = G.bf k (G.src a) + G.len a := by
  have h := min'_mem (G.cand (G.bf k) y) (insert_nonempty _ _)
  change G.bf (k + 1) y ∈ _ at h
  rcases mem_insert.1 h with h | h
  · exact Or.inl h
  · obtain ⟨a, ha, he⟩ := mem_image.1 h
    exact Or.inr ⟨a, (mem_filter.1 ha).2, he.symm⟩

/-- `bf (k + 1)` is the largest function below `bf k` and below `bf k (src a) + len a` at the end
of every arc. -/
lemma le_bf_succ {k : ℕ} {E : X → ℤ} (h1 : ∀ y, E y ≤ G.bf k y)
    (h2 : ∀ a, E (G.dst a) ≤ G.bf k (G.src a) + G.len a) (y : X) : E y ≤ G.bf (k + 1) y := by
  rcases G.bf_succ_cases k y with h | ⟨a, rfl, h⟩
  · rw [h]; exact h1 y
  · rw [h]; exact h2 a

lemma bf_anti {i j : ℕ} (h : i ≤ j) (y : X) : G.bf j y ≤ G.bf i y := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (G.bf_succ_le _ y).trans ih

lemma bf_nonpos (k : ℕ) (y : X) : G.bf k y ≤ 0 := G.bf_anti (Nat.zero_le k) y

/-- A vertex improved at round `k ≥ 1` is the end of a chain of tight arcs through vertices
improved at every earlier round. -/
lemma exists_chain {k : ℕ} (hk : 1 ≤ k) {y : X} (hy : G.bf k y < G.bf (k - 1) y) :
    ∃ w : ℕ → X, ∃ c : ℕ → A, w k = y ∧
      (∀ t, 1 ≤ t → t ≤ k → G.bf t (w t) < G.bf (t - 1) (w t)) ∧
      (∀ t, 1 ≤ t → t < k → G.src (c t) = w t ∧ G.dst (c t) = w (t + 1) ∧
        G.bf (t + 1) (w (t + 1)) = G.bf t (w t) + G.len (c t)) := by
  induction k, hk using Nat.le_induction generalizing y with
  | base =>
    obtain ⟨a, -⟩ : ∃ a, G.dst a = y ∧ G.bf (0 + 1) y = G.bf 0 (G.src a) + G.len a :=
      (G.bf_succ_cases 0 y).resolve_left (fun h => by
        have h' : G.bf 1 y = G.bf 0 y := h
        have hy' : G.bf 1 y < G.bf 0 y := hy
        omega)
    exact ⟨fun _ => y, fun _ => a, rfl, fun t h1 h2 => by
        have : t = 1 := by omega
        subst this; exact hy, fun t h1 h2 => by omega⟩
  | succ k hk ih =>
    simp only [Nat.add_sub_cancel] at hy
    rcases G.bf_succ_cases k y with h | ⟨a, rfl, ha⟩
    · omega
    · -- the start of `a` was improved at round `k`
      have hx : G.bf k (G.src a) < G.bf (k - 1) (G.src a) := by
        have h1 := G.bf_succ_le_arc (k - 1) a
        rw [show k - 1 + 1 = k by omega] at h1
        omega
      obtain ⟨w, c, hw, himp, harc⟩ := ih hx
      refine ⟨fun t => if t ≤ k then w t else G.dst a, fun t => if t < k then c t else a,
        by simp, fun t h1 h2 => ?_, fun t h1 h2 => ?_⟩
      · by_cases htk : t ≤ k
        · simp only [htk, ite_true]; exact himp t h1 htk
        · have : t = k + 1 := by omega
          subst this; simp only [show ¬ k + 1 ≤ k by omega, ite_false, Nat.add_sub_cancel]
          exact hy
      · by_cases htk : t < k
        · simp only [htk, ite_true, show t ≤ k by omega, show t + 1 ≤ k by omega]
          exact harc t h1 htk
        · have : t = k := by omega
          subst this
          refine ⟨by simp [hw], by simp, by simpa [hw] using ha⟩

/-- **Stabilization.** If a feasible potential exists, the Bellman–Ford values do not change
after `|X|` rounds. -/
theorem bf_succ_card {p : X → ℤ} (hp : G.IsPot p) (y : X) :
    G.bf (Fintype.card X + 1) y = G.bf (Fintype.card X) y := by
  by_contra hne
  have hlt : G.bf (Fintype.card X + 1) y < G.bf (Fintype.card X + 1 - 1) y := by
    have := G.bf_succ_le (Fintype.card X) y
    simp only [Nat.add_sub_cancel]; omega
  obtain ⟨w, c, -, himp, harc⟩ := G.exists_chain (by omega) hlt
  -- along the chain, `bf t (w t) - p (w t)` does not decrease
  have hmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ Fintype.card X + 1 →
      G.bf i (w i) - p (w i) ≤ G.bf j (w j) - p (w j) := by
    intro i j hi hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih =>
      obtain ⟨hs, hd, ht⟩ := harc j (by omega) (by omega)
      have := hp (c j)
      rw [hs, hd] at this
      have := ih (by omega)
      omega
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Icc 1 (Fintype.card X + 1)) (t := univ) (f := w) (by simp) (fun _ _ => mem_coe.2 (mem_univ _))
  simp only [mem_Icc] at hi hj
  have key : ∀ i j, 1 ≤ i → j ≤ Fintype.card X + 1 → i < j → w i = w j → False := by
    intro i j hi hj hlt' heq
    have h1 := hmono i j hi hlt'.le hj
    have h2 := himp j (by omega) hj
    have h3 := G.bf_anti (show i ≤ j - 1 by omega) (w j)
    rw [heq] at h1
    omega
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j hi.1 hj.2 h heq
  · exact key j i hj.1 hi.2 h heq.symm

/-- After `|X|` rounds the values form a feasible potential, if one exists. -/
theorem isPot_bf_card {p : X → ℤ} (hp : G.IsPot p) : G.IsPot (G.bf (Fintype.card X)) := by
  intro a
  rw [← G.bf_succ_card hp]
  exact G.bf_succ_le_arc _ a

/-- If a feasible potential exists, the values after `|X|` rounds are below the values after any
number of rounds (they are the limit). -/
lemma bf_card_le (k : ℕ) {p : X → ℤ} (hp : G.IsPot p) (y : X) :
    G.bf (Fintype.card X) y ≤ G.bf k y := by
  rcases le_total k (Fintype.card X) with h | h
  · exact G.bf_anti h y
  · induction k, h using Nat.le_induction generalizing y with
    | base => exact le_rfl
    | succ k hk ih =>
      exact G.le_bf_succ (fun z => ih z) (fun a => (G.isPot_bf_card hp a).trans
        (by have := ih (G.src a); omega)) y

/-! ### Negative cycles -/

/-- A closed walk of `m ≥ 1` arcs `c 0, …, c (m - 1)`. -/
def IsClosedWalk (m : ℕ) (c : ℕ → A) : Prop :=
  0 < m ∧ (∀ t, t + 1 < m → G.dst (c t) = G.src (c (t + 1))) ∧ G.dst (c (m - 1)) = G.src (c 0)

/-- The length of a walk of `m` arcs. -/
def walkLen (m : ℕ) (c : ℕ → A) : ℤ := ∑ t ∈ range m, G.len (c t)

/-- A feasible potential gives every closed walk a nonnegative length. -/
theorem walkLen_nonneg {p : X → ℤ} (hp : G.IsPot p) {m : ℕ} {c : ℕ → A}
    (hc : G.IsClosedWalk m c) : 0 ≤ G.walkLen m c := by
  obtain ⟨hm, hstep, hclose⟩ := hc
  have h : ∀ t ∈ range m, p (G.src (c ((t + 1) % m))) - p (G.src (c t)) ≤ G.len (c t) := by
    intro t ht
    rw [mem_range] at ht
    have := hp (c t)
    by_cases htm : t + 1 < m
    · rw [Nat.mod_eq_of_lt htm, ← hstep t htm]; omega
    · have : t + 1 = m := by omega
      rw [this, Nat.mod_self, ← hclose, show m - 1 = t by omega]; omega
  have htel : ∑ t ∈ range m, (p (G.src (c ((t + 1) % m))) - p (G.src (c t))) = 0 := by
    rw [sum_sub_distrib]
    have : ∑ t ∈ range m, p (G.src (c ((t + 1) % m))) = ∑ t ∈ range m, p (G.src (c t)) := by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [sum_range_succ, sum_range_succ', Nat.mod_self]
      congr 1
      refine sum_congr rfl fun t ht => ?_
      rw [mem_range] at ht
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [this, sub_self]
  unfold walkLen
  linarith [sum_le_sum h]

/-- **A feasible potential exists if and only if no closed walk has negative length.** -/
theorem exists_pot_iff : (∃ p, G.IsPot p) ↔ ∀ m c, G.IsClosedWalk m c → 0 ≤ G.walkLen m c := by
  constructor
  · rintro ⟨p, hp⟩ m c hc
    exact G.walkLen_nonneg hp hc
  · intro hneg
    refine ⟨G.bf (Fintype.card X), fun a => ?_⟩
    by_contra hcon
    -- some vertex still improves at round `|X| + 1`
    have hlt : G.bf (Fintype.card X + 1) (G.dst a) <
        G.bf (Fintype.card X + 1 - 1) (G.dst a) := by
      have := G.bf_succ_le_arc (Fintype.card X) a
      simp only [Nat.add_sub_cancel]; omega
    obtain ⟨w, c, -, himp, harc⟩ := G.exists_chain (by omega) hlt
    obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Icc 1 (Fintype.card X + 1)) (t := univ) (f := w) (by simp)
      (fun _ _ => mem_coe.2 (mem_univ _))
    simp only [mem_Icc] at hi hj
    wlog hlt' : i < j generalizing i j
    · exact this j i (Ne.symm hij) heq.symm hj hi (by omega)
    -- the closed walk `c i, …, c (j - 1)` has negative length
    have hlen : ∀ k, i ≤ k → k ≤ j → G.bf k (w k) = G.bf i (w i) +
        ∑ t ∈ range (k - i), G.len (c (i + t)) := by
      intro k hik hkj
      induction k, hik using Nat.le_induction with
      | base => simp
      | succ k hik ih =>
        obtain ⟨-, -, ht⟩ := harc k (by omega) (by omega)
        rw [ht, ih (by omega), show k + 1 - i = k - i + 1 by omega, sum_range_succ,
          show i + (k - i) = k by omega]
        ring
    have hcw : G.IsClosedWalk (j - i) (fun t => c (i + t)) := by
      refine ⟨by omega, fun t ht => ?_, ?_⟩
      · show G.dst (c (i + t)) = G.src (c (i + (t + 1)))
        rw [(harc (i + t) (by omega) (by omega)).2.1, show i + (t + 1) = i + t + 1 by omega,
          ← (harc (i + t + 1) (by omega) (by omega)).1]
      · simp only [Nat.add_zero]
        rw [show i + (j - i - 1) = j - 1 by omega, (harc (j - 1) (by omega) (by omega)).2.1,
          (harc i hi.1 (by omega)).1, show j - 1 + 1 = j by omega, heq]
    have := hneg _ _ hcw
    have h1 := hlen j hlt'.le le_rfl
    have h2 := himp j (by omega) hj.2
    have h3 := G.bf_anti (show i ≤ j - 1 by omega) (w j)
    rw [← heq] at h1 h2 h3
    simp only [walkLen] at this
    omega

/-! ### In-place relaxation -/

/-- Relax the arc `a`: lower the value at its end to the value at its start plus its length, if
that is smaller. -/
def relax (E : X → ℤ) (a : A) : X → ℤ :=
  if E (G.src a) + G.len a < E (G.dst a) then Function.update E (G.dst a) (E (G.src a) + G.len a)
  else E

lemma relax_le (E : X → ℤ) (a : A) (y : X) : G.relax E a y ≤ E y := by
  unfold relax
  split_ifs with h
  · rw [Function.update_apply]; split_ifs with h' <;> [subst h'; skip] <;> omega
  · exact le_rfl

lemma relax_dst (E : X → ℤ) (a : A) : G.relax E a (G.dst a) ≤ E (G.src a) + G.len a := by
  unfold relax
  split_ifs with h
  · simp
  · omega

/-- Relaxation never goes below a feasible potential that lies below the values. -/
lemma le_relax {P E : X → ℤ} (hP : G.IsPot P) (h : ∀ y, P y ≤ E y) (a : A) (y : X) :
    P y ≤ G.relax E a y := by
  unfold relax
  split_ifs with h'
  · rw [Function.update_apply]
    split_ifs with h''
    · subst h''; exact (hP a).trans (by have := h (G.src a); omega)
    · exact h y
  · exact h y

/-- A relaxation value is a value plus a length (or unchanged). -/
lemma relax_cases (E : X → ℤ) (a : A) (y : X) :
    G.relax E a y = E y ∨ G.relax E a y = E (G.src a) + G.len a := by
  unfold relax
  split_ifs
  · rw [Function.update_apply]; split_ifs <;> simp
  · exact Or.inl rfl

/-- The end of a round of in-place relaxations: if the values are at most `bf k` and, for every
arc, the value at its end is at most `bf k` at its start plus its length, they are at most
`bf (k + 1)`. -/
lemma le_bf_succ_of_round {k : ℕ} {E : X → ℤ} (h1 : ∀ y, E y ≤ G.bf k y)
    (h2 : ∀ a, E (G.dst a) ≤ G.bf k (G.src a) + G.len a) (y : X) : E y ≤ G.bf (k + 1) y :=
  G.le_bf_succ h1 h2 y

end Digraph

end PlanarFlow
