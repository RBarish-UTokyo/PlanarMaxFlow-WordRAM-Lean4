module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The pivot lemma

Parametric shortest-path algorithms (Karp and Orlin; Klein's multiple-source shortest paths in
the form of Cabello, Chambers and Erickson, SIAM J. Comput. 42, 2013; the maximum-flow algorithm
of Borradaile and Klein in the form of Erickson, SODA 2010) maintain a tree that changes by
*pivots*: one node `y` gets a new parent dart `e`. Their running time is the number of pivots
times the cost of one pivot. This file bounds the number of pivots, abstractly, in the three
forms used in this library.

## Monotone colours (Cabello, Chambers and Erickson, Corollary 3.3)

A sequence of pivots (`IsPivotSeq`): `par (i + 1) = update (par i) (y i) (e i)`. If there is a
monotone family of *blue* sets `B i` such that the node `y i` of every pivot is red (not blue)
before the pivot and blue after it, then

* `IsPivotSeq.stays`: **a dart that pivots in never pivots out**: `par j (y i) = e i` for all
  `j > i`;
* `IsPivotSeq.card_le`: **the number of pivots is at most the number of nodes**.

## Darts entering a sequence of trees

For a sequence of dart sets `T 0, T 1, …` (the darts of the trees), the darts entering at time
`i` are `T (i + 1) \ T i`; double counting gives `∑ i < n, #(T (i + 1) \ T i) = ∑ a, #(entries a)`
(`sum_card_sdiff_eq`). Hence:

* `sum_card_sdiff_le`: if **every dart enters at most once**, at most `#darts` entries in total;
* `entries_card_le_one_of_mono`: every dart enters at most once if each entry of `a` turns a
  monotone predicate `B · a` from false to true;
* `card_cycEntries_le_one`, `sum_card_cyc_le`: **moving around a face**: for a periodic sequence
  of `k` trees, if the times at which a dart is in the tree form a *cyclic interval*
  (`CycInterval`; Cabello, Chambers and Erickson, Lemma 3.7, by the Jordan curve theorem), the
  dart enters at most once per period, and the total number of entries over a period is at most
  the number of darts.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Pivot

open Finset

/-! ### Monotone colours -/

section Seq

variable {β γ : Type*} [DecidableEq β]

/-- **A sequence of `n` pivots**: at step `i` the node `y i` gets the parent `e i`. -/
structure IsPivotSeq (par : ℕ → β → γ) (y : ℕ → β) (e : ℕ → γ) (n : ℕ) : Prop where
  step : ∀ i < n, par (i + 1) = Function.update (par i) (y i) (e i)

variable {par : ℕ → β → γ} {y : ℕ → β} {e : ℕ → γ} {n : ℕ}

/-- **The colours of a pivot sequence**: a monotone family of blue sets, the node of each pivot
red before the pivot and blue after it. -/
structure Colours (B : ℕ → Set β) (y : ℕ → β) (n : ℕ) : Prop where
  mono : ∀ i < n, B i ⊆ B (i + 1)
  red : ∀ i < n, y i ∉ B i
  blue : ∀ i < n, y i ∈ B (i + 1)

lemma Colours.mono_le {B : ℕ → Set β} (hC : Colours B y n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    B i ⊆ B j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (hC.mono j (by omega))

/-- Distinct pivots move distinct nodes. -/
lemma Colours.y_ne {B : ℕ → Set β} (hC : Colours B y n) {i j : ℕ} (hij : i < j) (hj : j < n) :
    y j ≠ y i := fun h =>
  hC.red j hj (h ▸ hC.mono_le (by omega : i + 1 ≤ j) hj.le (hC.blue i (by omega)))

/-- **A dart that pivots in never pivots out** (Cabello, Chambers and Erickson, Corollary 3.3). -/
theorem IsPivotSeq.stays (hP : IsPivotSeq par y e n) {B : ℕ → Set β} (hC : Colours B y n)
    {i j : ℕ} (hij : i < j) (hj : j ≤ n) : par j (y i) = e i := by
  induction j, (show i + 1 ≤ j by omega) using Nat.le_induction with
  | base => rw [hP.step i (by omega), Function.update_self]
  | succ j hij' ih =>
    rw [hP.step j (by omega), Function.update_of_ne (hC.y_ne (by omega) (by omega)).symm,
      ih (by omega) (by omega)]

/-- **The number of pivots is at most the number of nodes.** -/
theorem Colours.card_le [Fintype β] {B : ℕ → Set β} (hC : Colours B y n) : n ≤ Fintype.card β := by
  have hinj : Function.Injective fun i : Fin n => y i := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h' | h'
    · exact hC.y_ne h' j.2 h.symm
    · exact hC.y_ne h' i.2 h
  simpa using Fintype.card_le_of_injective _ hinj

end Seq

/-! ### Darts entering a sequence of trees -/

section Entries

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The times `i < n` at which `a` enters the sequence `T`. -/
def entries (T : ℕ → Finset α) (n : ℕ) (a : α) : Finset ℕ :=
  (range n).filter fun i => a ∈ T (i + 1) ∧ a ∉ T i

/-- **Double counting**: the entries, counted by time or by dart. -/
theorem sum_card_sdiff_eq (T : ℕ → Finset α) (n : ℕ) :
    ∑ i ∈ range n, (T (i + 1) \ T i).card = ∑ a, (entries T n a).card := by
  simp only [card_eq_sum_ones, entries, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_filter]
  congr 1
  ext a; simp

/-- **If every dart enters at most once, there are at most `#darts` entries.** -/
theorem sum_card_sdiff_le {T : ℕ → Finset α} {n : ℕ} (h : ∀ a, (entries T n a).card ≤ 1) :
    ∑ i ∈ range n, (T (i + 1) \ T i).card ≤ Fintype.card α := by
  rw [sum_card_sdiff_eq]
  calc ∑ a, (entries T n a).card ≤ ∑ _a : α, 1 := sum_le_sum fun a _ => h a
    _ = Fintype.card α := by simp

/-- **A dart enters at most once** if each of its entries turns a monotone predicate on. -/
theorem entries_card_le_one_of_mono {T : ℕ → Finset α} {n : ℕ} {a : α} (B : ℕ → Prop)
    (hmono : ∀ i j, i ≤ j → B i → B j)
    (hin : ∀ i < n, a ∈ T (i + 1) → a ∉ T i → ¬ B i ∧ B (i + 1)) :
    (entries T n a).card ≤ 1 := by
  rw [card_le_one]
  intro i hi j hj
  simp only [entries, mem_filter, mem_range] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (hin j hj.1 hj.2.1 hj.2.2).1 (hmono _ _ h (hin i hi.1 hi.2.1 hi.2.2).2)
  · exact (hin i hi.1 hi.2.1 hi.2.2).1 (hmono _ _ h (hin j hj.1 hj.2.1 hj.2.2).2)

/-! ### Moving around a face -/

/-- **A cyclic interval** of `{0, …, k - 1}`: with two members `i < j`, it contains all of
`[i, j]` or all of `[j, k) ∪ [0, i]`. -/
def CycInterval (k : ℕ) (A : ℕ → Prop) : Prop :=
  ∀ i j, i < j → j < k → A i → A j →
    (∀ l, i ≤ l → l ≤ j → A l) ∨ (∀ l, l < k → (j ≤ l ∨ l ≤ i) → A l)

/-- The times `i < k` at which `A` is entered, cyclically. -/
def cycEntries (k : ℕ) (A : ℕ → Prop) [DecidablePred A] : Finset ℕ :=
  (range k).filter fun i => ¬ A i ∧ A ((i + 1) % k)

/-- **A cyclic interval is entered at most once.** -/
theorem card_cycEntries_le_one {k : ℕ} {A : ℕ → Prop} [DecidablePred A] (hA : CycInterval k A) :
    (cycEntries k A).card ≤ 1 := by
  rw [card_le_one]
  intro i hi i' hi'
  simp only [cycEntries, mem_filter, mem_range] at hi hi'
  by_contra hne
  have hk : 0 < k := by omega
  -- the two entry points
  have key : ∀ i i', i < k → i' < k → ¬ A i → ¬ A i' → A ((i + 1) % k) → A ((i' + 1) % k) →
      (i + 1) % k < (i' + 1) % k → False := by
    intro i i' hi hi' ni ni' ai ai' hlt
    generalize ha : (i + 1) % k = a at ai hlt
    generalize hb : (i' + 1) % k = b at ai' hlt
    have hbk : b < k := hb ▸ Nat.mod_lt _ hk
    -- `i' = b - 1`
    have hi'b : i' = b - 1 := by
      rcases Nat.lt_or_ge (i' + 1) k with h | h
      · rw [Nat.mod_eq_of_lt h] at hb; omega
      · have : i' + 1 = k := by omega
        rw [this, Nat.mod_self] at hb; omega
    rcases hA a b hlt hbk ai ai' with h | h
    · exact ni' (hi'b ▸ h (b - 1) (by omega) (by omega))
    · rcases Nat.lt_or_ge (i + 1) k with h' | h'
      · rw [Nat.mod_eq_of_lt h'] at ha
        exact ni (h i hi (by omega))
      · have : i = k - 1 := by omega
        exact ni (h i hi (by omega))
  have hne' : (i + 1) % k ≠ (i' + 1) % k := by
    intro h
    apply hne
    rcases Nat.lt_or_ge (i + 1) k with h1 | h1 <;> rcases Nat.lt_or_ge (i' + 1) k with h2 | h2
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
    · rw [Nat.mod_eq_of_lt h1, show i' + 1 = k by omega, Nat.mod_self] at h; omega
    · rw [Nat.mod_eq_of_lt h2, show i + 1 = k by omega, Nat.mod_self] at h; omega
    · omega
  rcases lt_or_gt_of_ne hne' with h | h
  · exact key i i' hi.1 hi'.1 hi.2.1 hi'.2.1 hi.2.2 hi'.2.2 h
  · exact key i' i hi'.1 hi.1 hi'.2.1 hi.2.1 hi'.2.2 hi.2.2 h

/-- **Moving around a face**: for `k` trees `T 0, …, T (k - 1)` visited cyclically, if the times
at which each dart is in the tree form a cyclic interval, the total number of darts entering
(from `T i` to `T ((i + 1) % k)`) over the period is at most the number of darts. -/
theorem sum_card_cyc_le {T : ℕ → Finset α} {k : ℕ}
    (hA : ∀ a, CycInterval k fun i => a ∈ T i) :
    ∑ i ∈ range k, (T ((i + 1) % k) \ T i).card ≤ Fintype.card α := by
  have e : ∑ i ∈ range k, (T ((i + 1) % k) \ T i).card =
      ∑ a, (cycEntries k fun i => a ∈ T i).card := by
    simp only [card_eq_sum_ones, cycEntries, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_filter]
    congr 1
    ext a; simp [and_comm]
  rw [e]
  calc ∑ a, (cycEntries k fun i => a ∈ T i).card ≤ ∑ _a : α, 1 :=
        sum_le_sum fun a _ => card_cycEntries_le_one (hA a)
    _ = Fintype.card α := by simp

end Entries

end Pivot

end PlanarFlow
