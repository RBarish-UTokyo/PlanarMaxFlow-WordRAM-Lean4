module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel

/-!
# Monge matrices, total monotonicity and leftmost row minima

A matrix is a function `A : ℕ → ℕ → α` read on the rows `i < m` and the columns `j < n`, with
entries in a linearly ordered additive commutative group `α` (in this library `ℤ` for the
mathematics of distances and `ℝ` for the values held in the real memory of the machine). Entries
are finite: an infinite distance is never needed, because the blocks of a dense distance graph
used here (`PlanarFlow.Monge.Crossing`) are full rectangles of finite distances.

* `IsMonge m n A`: `A i j + A i' j' ≤ A i j' + A i' j` for `i < i'`, `j < j'`.
* `IsTotMono m n A`: in every `2 × 2` submatrix, if the right entry of the upper row is smaller
  (resp. not larger) than its left entry, then so is the right entry of the lower row.
* `IsMonge.totMono`: **Monge matrices are totally monotone.** `IsMonge.add_row`,
  `IsMonge.add_col`: adding a function of the row or of the column keeps the Monge property (so
  `d i + A i j` is Monge when `A` is).
* `IsLMin f lo hi j`: `j` is the leftmost position of a minimum of `f` on `lo ≤ j ≤ hi`;
  `IsLMin.unique`, `exists_isLMin`, `lmin m n A i` (the leftmost minimum of row `i`).
* `IsTotMono.lmin_mono`: **the leftmost row minima of a totally monotone matrix are
  nondecreasing**; `IsLMin.restrict`: the minimum on a window containing it is the same. These
  two facts are what the row-minima algorithms use: the leftmost minimum of row `i` lies between
  those of any two rows around it.
* `IsLMin.scan_succ_lt`, `IsLMin.scan_succ_ge`: the step of a left-to-right scan.

## References

* A. Aggarwal, M. M. Klawe, S. Moran, P. Shor, R. Wilber, *Geometric applications of a
  matrix-searching algorithm*, Algorithmica 2 (1987), 195–208.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- The Monge property on the rows `< m` and the columns `< n`. -/
def IsMonge (m n : ℕ) (A : ℕ → ℕ → α) : Prop :=
  ∀ i i' j j', i < i' → i' < m → j < j' → j' < n → A i j + A i' j' ≤ A i j' + A i' j

/-- Total monotonicity on the rows `< m` and the columns `< n`. -/
def IsTotMono (m n : ℕ) (A : ℕ → ℕ → α) : Prop :=
  ∀ i i' j j', i < i' → i' < m → j < j' → j' < n →
    (A i j' < A i j → A i' j' < A i' j) ∧ (A i j' ≤ A i j → A i' j' ≤ A i' j)

/-- **Monge matrices are totally monotone.** -/
theorem IsMonge.totMono {m n : ℕ} {A : ℕ → ℕ → α} (h : IsMonge m n A) : IsTotMono m n A := by
  intro i i' j j' hi hi' hj hj'
  have key := h i i' j j' hi hi' hj hj'
  constructor
  · intro hlt
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd key (not_le.2 (add_lt_add_of_lt_of_le hlt hcon))
  · intro hle
    by_contra hcon
    rw [not_le] at hcon
    exact absurd key (not_le.2 (add_lt_add_of_le_of_lt hle hcon))

/-- Adding a function of the row keeps the Monge property. -/
theorem IsMonge.add_row {m n : ℕ} {A : ℕ → ℕ → α} (h : IsMonge m n A) (f : ℕ → α) :
    IsMonge m n (fun i j => f i + A i j) := by
  intro i i' j j' hi hi' hj hj'
  have := h i i' j j' hi hi' hj hj'
  show f i + A i j + (f i' + A i' j') ≤ f i + A i j' + (f i' + A i' j)
  rw [show f i + A i j + (f i' + A i' j') = (f i + f i') + (A i j + A i' j') by abel,
    show f i + A i j' + (f i' + A i' j) = (f i + f i') + (A i j' + A i' j) by abel]
  exact add_le_add le_rfl this

/-- Adding a function of the column keeps the Monge property. -/
theorem IsMonge.add_col {m n : ℕ} {A : ℕ → ℕ → α} (h : IsMonge m n A) (g : ℕ → α) :
    IsMonge m n (fun i j => A i j + g j) := by
  intro i i' j j' hi hi' hj hj'
  have := h i i' j j' hi hi' hj hj'
  show A i j + g j + (A i' j' + g j') ≤ A i j' + g j' + (A i' j + g j)
  rw [show A i j + g j + (A i' j' + g j') = (A i j + A i' j') + (g j + g j') by abel,
    show A i j' + g j' + (A i' j + g j) = (A i j' + A i' j) + (g j + g j') by abel]
  exact add_le_add this le_rfl

/-- The transpose of a Monge matrix is Monge. -/
theorem IsMonge.transpose {m n : ℕ} {A : ℕ → ℕ → α} (h : IsMonge m n A) :
    IsMonge n m (fun j i => A i j) := by
  intro j j' i i' hj hj' hi hi'
  have := h i i' j j' hi hi' hj hj'
  simpa [add_comm] using this

/-- The Monge property is a property of the entries in the rectangle only. -/
theorem IsMonge.congr {m n : ℕ} {A B : ℕ → ℕ → α} (h : IsMonge m n A)
    (hAB : ∀ i j, i < m → j < n → A i j = B i j) : IsMonge m n B := by
  intro i i' j j' hi hi' hj hj'
  rw [← hAB i j (by omega) (by omega), ← hAB i' j' hi' hj', ← hAB i j' (by omega) hj',
    ← hAB i' j hi' (by omega)]
  exact h i i' j j' hi hi' hj hj'

/-- Integer Monge matrices stay Monge in `ℝ`. -/
theorem IsMonge.cast {m n : ℕ} {A : ℕ → ℕ → ℤ} (h : IsMonge m n A) :
    IsMonge m n (fun i j => (A i j : ℝ)) := by
  intro i i' j j' hi hi' hj hj'
  show (A i j : ℝ) + A i' j' ≤ A i j' + A i' j
  exact_mod_cast h i i' j j' hi hi' hj hj'

/-! ### Leftmost minima -/

/-- `j` is the leftmost position of a minimum of `f` on the window `lo ≤ j ≤ hi`. -/
def IsLMin (f : ℕ → α) (lo hi j : ℕ) : Prop :=
  lo ≤ j ∧ j ≤ hi ∧ (∀ j', lo ≤ j' → j' ≤ hi → f j ≤ f j') ∧ (∀ j', lo ≤ j' → j' < j → f j < f j')

theorem IsLMin.unique {f : ℕ → α} {lo hi j j' : ℕ} (h : IsLMin f lo hi j) (h' : IsLMin f lo hi j') :
    j = j' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h1', h2', h3', h4'⟩ := h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd (h3 j' h1' h2') (not_le.2 (h4' j h1 hlt))
  · exact absurd (h3' j h1 h2) (not_le.2 (h4 j' h1' hlt))

/-- A single position is its own leftmost minimum. -/
theorem isLMin_self (f : ℕ → α) (j : ℕ) : IsLMin f j j j :=
  ⟨le_rfl, le_rfl, fun j' h1 h2 => by rw [show j' = j by omega], fun j' h1 h2 => by omega⟩

/-- The step of a left-to-right scan when the new entry is strictly smaller. -/
theorem IsLMin.scan_succ_lt {f : ℕ → α} {lo hi j : ℕ} (h : IsLMin f lo hi j)
    (hlt : f (hi + 1) < f j) : IsLMin f lo (hi + 1) (hi + 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, le_rfl, fun j' a b => ?_, fun j' a b => ?_⟩
  · rcases Nat.lt_or_ge j' (hi + 1) with c | c
    · exact hlt.le.trans (h3 j' a (by omega))
    · rw [show j' = hi + 1 by omega]
  · exact lt_of_lt_of_le hlt (h3 j' a (by omega))

/-- The step of a left-to-right scan when the new entry is not smaller. -/
theorem IsLMin.scan_succ_ge {f : ℕ → α} {lo hi j : ℕ} (h : IsLMin f lo hi j)
    (hge : ¬ f (hi + 1) < f j) : IsLMin f lo (hi + 1) j := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, by omega, fun j' a b => ?_, h4⟩
  rcases Nat.lt_or_ge j' (hi + 1) with c | c
  · exact h3 j' a (by omega)
  · rw [show j' = hi + 1 by omega]; exact not_lt.1 hge

/-- Every nonempty window has a leftmost minimum. -/
theorem exists_isLMin (f : ℕ → α) {lo hi : ℕ} (hle : lo ≤ hi) : ∃ j, IsLMin f lo hi j := by
  induction hi, hle using Nat.le_induction with
  | base => exact ⟨lo, isLMin_self f lo⟩
  | succ hi _ ih =>
    obtain ⟨j, hj⟩ := ih
    by_cases hlt : f (hi + 1) < f j
    · exact ⟨hi + 1, hj.scan_succ_lt hlt⟩
    · exact ⟨j, hj.scan_succ_ge hlt⟩

/-- A minimum on a window is the minimum on every smaller window containing it. -/
theorem IsLMin.restrict {f : ℕ → α} {lo hi j lo' hi' : ℕ} (h : IsLMin f lo hi j) (h1 : lo ≤ lo')
    (h2 : lo' ≤ j) (h3 : j ≤ hi') (h4 : hi' ≤ hi) : IsLMin f lo' hi' j :=
  ⟨h2, h3, fun j' a b => h.2.2.1 j' (by omega) (by omega), fun j' a b => h.2.2.2 j' (by omega) b⟩

/-- The leftmost minimum of row `i` of `A` on the columns `< n` (`0` if `n = 0`). -/
noncomputable def lmin (n : ℕ) (A : ℕ → ℕ → α) (i : ℕ) : ℕ :=
  Classical.choose (exists_isLMin (A i) (Nat.zero_le (n - 1)))

theorem isLMin_lmin {n : ℕ} (A : ℕ → ℕ → α) (i : ℕ) (_hn : 0 < n) :
    IsLMin (A i) 0 (n - 1) (lmin n A i) := Classical.choose_spec (exists_isLMin (A i) (Nat.zero_le (n - 1)))

theorem lmin_lt {n : ℕ} (A : ℕ → ℕ → α) (i : ℕ) (hn : 0 < n) : lmin n A i < n := by
  have := (isLMin_lmin A i hn).2.1; omega

theorem lmin_eq {n : ℕ} {A : ℕ → ℕ → α} {i j : ℕ} (hn : 0 < n) (h : IsLMin (A i) 0 (n - 1) j) :
    lmin n A i = j :=
  (isLMin_lmin A i hn).unique h

/-- **The leftmost row minima of a totally monotone matrix are nondecreasing.** -/
theorem IsTotMono.lmin_mono {m n : ℕ} {A : ℕ → ℕ → α} (h : IsTotMono m n A) {i i' : ℕ}
    (hi : i ≤ i') (hi' : i' < m) (hn : 0 < n) : lmin n A i ≤ lmin n A i' := by
  rcases Nat.eq_or_lt_of_le hi with rfl | hlt
  · exact le_rfl
  by_contra hcon
  rw [not_le] at hcon
  have h1 := isLMin_lmin A i hn
  have h2 := isLMin_lmin A i' hn
  -- in row `i` the entry at `lmin i'` is strictly larger than at `lmin i`
  have hs : A i (lmin n A i) < A i (lmin n A i') := h1.2.2.2 _ (Nat.zero_le _) hcon
  have := (h i i' (lmin n A i') (lmin n A i) hlt hi' hcon (lmin_lt A i hn)).1 hs
  exact absurd (h2.2.2.1 _ (Nat.zero_le _) (by have := lmin_lt A i hn; omega)) (not_le.2 this)

/-- The leftmost minimum of a row on any window containing it. -/
theorem isLMin_lmin_window {n : ℕ} (A : ℕ → ℕ → α) (i : ℕ) (hn : 0 < n) {lo hi : ℕ}
    (h1 : lo ≤ lmin n A i) (h2 : lmin n A i ≤ hi) (h3 : hi < n) :
    IsLMin (A i) lo hi (lmin n A i) :=
  (isLMin_lmin A i hn).restrict (Nat.zero_le _) h1 h2 (by omega)

/-- If the leftmost minimum of row `i` on the window `[lo, hi]` is `j`, and the leftmost minimum
of the whole row lies in the window, they coincide. -/
theorem lmin_eq_of_window {n : ℕ} {A : ℕ → ℕ → α} {i lo hi j : ℕ} (hn : 0 < n)
    (h1 : lo ≤ lmin n A i) (h2 : lmin n A i ≤ hi) (h3 : hi < n) (h : IsLMin (A i) lo hi j) :
    lmin n A i = j :=
  (isLMin_lmin_window A i hn h1 h2 h3).unique h

/-- The value at the leftmost minimum is below every entry of the row. -/
theorem lmin_le {n : ℕ} (A : ℕ → ℕ → α) (i : ℕ) {j : ℕ} (hj : j < n) :
    A i (lmin n A i) ≤ A i j :=
  (isLMin_lmin A i (by omega)).2.2.1 j (Nat.zero_le _) (by omega)

end Monge

end PlanarFlow
