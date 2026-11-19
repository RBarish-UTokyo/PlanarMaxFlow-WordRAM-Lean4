module

public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# A binary tournament tree (a binary heap over fixed slots)

An array `t` indexed by `1 … 2n - 1` is a complete binary tree: node `i` has the children `2i`
and `2i + 1`, the nodes `n … 2n - 1` are the leaves (one for each of the `n` slots) and
`1 … n - 1` the internal nodes. It is a *tournament tree* (`PlanarFlow.Heap.IsTour`) if every
internal node holds the minimum of its two children; then the root holds the minimum of all
leaves (`PlanarFlow.Heap.root_le`), and following the smaller child from the root leads to a leaf
holding it.

Changing a leaf breaks the property only at the ancestors of the leaf; recomputing them bottom-up
restores it (`PlanarFlow.Heap.IsTourExc`, `isTourExc_set`, `isTourExc_step`). Every operation
touches `O(log n)` nodes: the number of halvings of `j` until `0` is `lg j`, with
`lg j = Nat.log 2 j + 1` for `j ≥ 1` (`PlanarFlow.Heap.lg_eq_log`).

This is the binary heap with decrease-key used by Dijkstra's algorithm, in the array form of a
tournament (winner) tree.
-/

@[expose] public section

namespace PlanarFlow

namespace Heap

/-- The number of halvings of `j` until `0`. -/
def lg (j : ℕ) : ℕ := if j = 0 then 0 else lg (j / 2) + 1
termination_by j
decreasing_by omega

lemma lg_zero : lg 0 = 0 := by rw [lg]; simp

lemma lg_pos {j : ℕ} (h : 1 ≤ j) : lg j = lg (j / 2) + 1 := by
  rw [lg]; simp [show j ≠ 0 by omega]

lemma lg_mono {a b : ℕ} (h : a ≤ b) : lg a ≤ lg b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [lg_zero]; exact Nat.zero_le _
    · rw [lg_pos ha, lg_pos (by omega : 1 ≤ b)]
      have := ih (b / 2) (by omega) (Nat.div_le_div_right (c := 2) h)
      omega

lemma lg_two_mul {i : ℕ} (h : 1 ≤ i) : lg (2 * i) = lg i + 1 := by
  rw [lg_pos (by omega : 1 ≤ 2 * i)]; congr 2; omega

lemma lg_two_mul_add_one (i : ℕ) : lg (2 * i + 1) = lg i + 1 := by
  rw [lg_pos (by omega : 1 ≤ 2 * i + 1)]; congr 2; omega

lemma lg_eq_log {j : ℕ} (h : 1 ≤ j) : lg j = Nat.log 2 j + 1 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rw [lg_pos h]
    rcases Nat.lt_or_ge j 2 with hj | hj
    · have : j = 1 := by omega
      subst this; simp [lg_zero]
    · rw [ih (j / 2) (by omega) (by omega), Nat.log_div_base]
      have : 1 ≤ Nat.log 2 j := Nat.le_log_of_pow_le (by norm_num) (by simpa using hj)
      omega

/-- `i` is `j` or an ancestor of `j`. -/
def Anc (i j : ℕ) : Prop := ∃ k, j / 2 ^ k = i

lemma anc_self (j : ℕ) : Anc j j := ⟨0, by simp⟩

lemma anc_of_half {i j : ℕ} (h : Anc i (j / 2)) : Anc i j := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by rw [pow_succ', ← Nat.div_div_eq_div_mul]; exact hk⟩

lemma not_anc_of {i j : ℕ} (h1 : i ≠ j) (h2 : ¬ Anc i (j / 2)) : ¬ Anc i j := by
  rintro ⟨k, hk⟩
  rcases k with _ | k
  · simp at hk; exact h1 hk.symm
  · rw [pow_succ', ← Nat.div_div_eq_div_mul] at hk; exact h2 ⟨k, hk⟩

lemma not_anc_zero {i : ℕ} (hi : 1 ≤ i) : ¬ Anc i 0 := by
  rintro ⟨k, hk⟩; simp at hk; omega

/-- The tournament property everywhere except at the ancestors of `j` (and `j` itself). -/
def IsTourExc (n : ℕ) (t : ℕ → ℕ) (j : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i < n → ¬ Anc i j → t i = min (t (2 * i)) (t (2 * i + 1))

/-- The tournament property. -/
def IsTour (n : ℕ) (t : ℕ → ℕ) : Prop :=
  ∀ i, 1 ≤ i → i < n → t i = min (t (2 * i)) (t (2 * i + 1))

lemma isTour_of_exc {n : ℕ} {t : ℕ → ℕ} (h : IsTourExc n t 0) : IsTour n t :=
  fun i h1 h2 => h i h1 h2 (not_anc_zero h1)

/-- Changing the value at `l` breaks the property at most at the ancestors of `l / 2`. -/
lemma isTourExc_set {n : ℕ} {t t' : ℕ → ℕ} (h : IsTour n t) {l : ℕ} (hl : n ≤ l)
    (ht : ∀ a, a ≠ l → t' a = t a) : IsTourExc n t' (l / 2) := by
  intro i h1 h2 h3
  have e1 : i ≠ l := by omega
  have e2 : 2 * i ≠ l := fun e => h3 ⟨0, by simp; omega⟩
  have e3 : 2 * i + 1 ≠ l := fun e => h3 ⟨0, by simp; omega⟩
  rw [ht i e1, ht _ e2, ht _ e3]; exact h i h1 h2

/-- Recomputing `j` from its children moves the exception to `j / 2`. -/
lemma isTourExc_step {n : ℕ} {t t' : ℕ → ℕ} {j : ℕ} (h : IsTourExc n t j) (hj : 1 ≤ j)
    (hjn : j < n) (ht : ∀ a, a ≠ j → t' a = t a)
    (htj : t' j = min (t (2 * j)) (t (2 * j + 1))) : IsTourExc n t' (j / 2) := by
  intro i h1 h2 h3
  by_cases hij : i = j
  · subst hij
    rw [htj, ht _ (by omega), ht _ (by omega)]
  · have e2 : 2 * i ≠ j := fun e => h3 ⟨0, by simp; omega⟩
    have e3 : 2 * i + 1 ≠ j := fun e => h3 ⟨0, by simp; omega⟩
    rw [ht i hij, ht _ e2, ht _ e3]
    exact h i h1 h2 (not_anc_of hij h3)

/-- The root holds the minimum of the tree. -/
lemma root_le {n : ℕ} {t : ℕ → ℕ} (h : IsTour n t) {l : ℕ} (h1 : 1 ≤ l) (h2 : l < 2 * n) :
    t 1 ≤ t l := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    rcases Nat.lt_or_ge l 2 with hl | hl
    · have : l = 1 := by omega
      subst this; exact le_rfl
    · have hp := h (l / 2) (by omega) (by omega)
      have := ih (l / 2) (by omega) (by omega) (by omega)
      rcases Nat.even_or_odd l with ⟨r, hr⟩ | ⟨r, hr⟩
      · have e : 2 * (l / 2) = l := by omega
        rw [e] at hp; have := min_le_left (t l) (t (2 * (l / 2) + 1)); omega
      · have e : 2 * (l / 2) + 1 = l := by omega
        rw [e] at hp; have := min_le_right (t (2 * (l / 2))) (t l); omega

end Heap

end PlanarFlow
