module

public import PlanarSeparator.Machine.OrderProg

/-!
# Sorting a list of vertices in `O(k + √N)` steps

The splits of the separator tree need the sorted list of a vertex set (`lv`, `lvs`), and the
programs of `PlanarSeparator/Machine/` obtain it by a pass over all `N` flags. Here a two-digit
radix sort (LSD, base `β` with `β² ≥ N`) produces it from an unsorted list of `k` distinct
vertices in `O(k + β)` steps, with a count array of `β` words which it leaves zero.

* `csBlk`, `csS`: the blocks of a list by a key, and their concatenation in key order (the
  output of a stable counting sort); `csS_getElem`, `perm_csS`.
* `radix_sorted`: the two passes (keys `x mod β`, then `x / β`) sort a list of distinct
  numbers `< β²`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset

/-! ### Blocks by a key -/

section blocks

variable (κ : ℕ → ℕ) (L : List ℕ)

/-- The elements of `L` of key `t`, in order. -/
def csBlk (t : ℕ) : List ℕ := L.filter (fun x => κ x = t)

/-- The blocks of the keys `< t`, in key order. -/
def csS (t : ℕ) : List ℕ := (List.range t).flatMap (csBlk κ L)

theorem csS_succ (t : ℕ) : csS κ L (t + 1) = csS κ L t ++ csBlk κ L t := by
  simp [csS, List.range_succ, List.flatMap_append]

theorem csS_getElem {t j : ℕ} (hj : j < (csBlk κ L t).length) {β : ℕ} (ht : t < β) :
    (csS κ L β).getD ((csS κ L t).length + j) 0 = (csBlk κ L t).getD j 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, β = t + 1 + r := ⟨β - (t + 1), by omega⟩
  have : csS κ L (t + 1 + r) = csS κ L (t + 1) ++
      (List.range' (t + 1) r).flatMap (csBlk κ L) := by
    simp [csS, List.range_add, List.flatMap_append, List.range'_eq_map_range]
  rw [this, csS_succ, List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
    Nat.add_sub_cancel_left, List.getD_append _ _ _ _ hj]

theorem length_csS_le (t : ℕ) : (csS κ L t).length ≤ (csS κ L (t + 1)).length := by
  rw [csS_succ, List.length_append]; omega

theorem mem_csS {β x : ℕ} : x ∈ csS κ L β ↔ x ∈ L ∧ κ x < β := by
  simp [csS, csBlk, and_comm]

theorem nodup_csS (hL : L.Nodup) (β : ℕ) : (csS κ L β).Nodup := by
  unfold csS
  rw [List.nodup_flatMap]
  refine ⟨fun t _ => hL.filter _, List.nodup_range.pairwise_of_forall_ne fun a _ b _ hab => ?_⟩
  intro x hx hx'
  simp only [csBlk, List.mem_filter, decide_eq_true_eq] at hx hx'
  exact hab (hx.2.symm.trans hx'.2)

theorem perm_csS (hL : L.Nodup) {β : ℕ} (hκ : ∀ x ∈ L, κ x < β) : (csS κ L β).Perm L :=
  (List.perm_ext_iff_of_nodup (nodup_csS κ L hL β) hL).2 fun x => by
    rw [mem_csS]; exact ⟨fun h => h.1, fun h => ⟨h, hκ x h⟩⟩

theorem length_csS (hL : L.Nodup) {β : ℕ} (hκ : ∀ x ∈ L, κ x < β) :
    (csS κ L β).length = L.length := (perm_csS κ L hL hκ).length_eq

/-- Within the concatenation, the keys are nondecreasing. -/
theorem csS_pairwise_key (β : ℕ) : (csS κ L β).Pairwise (fun x y => κ x ≤ κ y) := by
  unfold csS
  rw [List.pairwise_flatMap]
  refine ⟨fun t _ => ?_, ?_⟩
  · refine List.Pairwise.imp_of_mem (R := fun _ _ => True) ?_ (List.pairwise_of_forall (by simp))
    intro x y hx hy _
    simp only [csBlk, List.mem_filter, decide_eq_true_eq] at hx hy
    omega
  · refine (List.pairwise_lt_range).imp_of_mem ?_
    intro a b _ _ hab x hx y hy
    simp only [csBlk, List.mem_filter, decide_eq_true_eq] at hx hy
    omega

/-- A prefix of the input gives a prefix of every block. -/
theorem csBlk_take_succ (i t : ℕ) (hi : i < L.length) :
    csBlk κ (L.take (i + 1)) t = csBlk κ (L.take i) t ++
      (if κ L[i] = t then [L[i]] else []) := by
  unfold csBlk
  rw [List.take_succ, List.getElem?_eq_getElem hi, Option.toList_some, List.filter_append]
  congr 1
  by_cases h : κ L[i] = t <;> simp [h]

theorem csBlk_take_prefix (i t : ℕ) : csBlk κ (L.take i) t <+: csBlk κ L t := by
  unfold csBlk
  exact (List.take_prefix i L).filter _

end blocks

/-! ### The two passes -/

/-- **The two passes of the radix sort** (stable, keys `x mod β`, then `x / β mod β`) sort a
list of distinct numbers `< β²`. -/
theorem radix_sorted (L : List ℕ) (hL : L.Nodup) {β : ℕ} (hβ : ∀ x ∈ L, x < β * β) :
    (csS (fun x => x / β % β) (csS (fun x => x / 1 % β) L β) β).Pairwise (· < ·) ∧
      (csS (fun x => x / β % β) (csS (fun x => x / 1 % β) L β) β).Perm L := by
  set A := csS (fun x => x / 1 % β) L β with hA
  rcases Nat.eq_zero_or_pos β with h0 | hβ0
  · subst h0
    have : L = [] := List.eq_nil_iff_forall_not_mem.2 fun x hx => by simpa using hβ x hx
    subst this
    simp [csS]
  have hpA : A.Perm L := perm_csS _ L hL (fun x _ => Nat.mod_lt _ hβ0)
  have hndA : A.Nodup := hpA.nodup_iff.2 hL
  have hAβ : ∀ x ∈ A, x < β * β := fun x hx => hβ x (hpA.subset hx)
  have hpB := perm_csS (fun x => x / β % β) A hndA (fun x _ => Nat.mod_lt _ hβ0)
  refine ⟨?_, hpB.trans hpA⟩
  have hdiv : ∀ x ∈ A, x / β % β = x / β := fun x hx =>
    Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by have := hAβ x hx; rwa [Nat.mul_comm] at this))
  have hkA : A.Pairwise (fun x y => x % β ≤ y % β ∧ x ≠ y) := by
    have := (csS_pairwise_key (fun x => x / 1 % β) L β).and hndA
    rw [hA]; simpa [Nat.div_one] using this
  unfold csS
  rw [List.pairwise_flatMap]
  refine ⟨fun t _ => ?_, ?_⟩
  · unfold csBlk
    refine (hkA.filter _).imp_of_mem ?_
    intro x y hx hy ⟨h1, h2⟩
    simp only [List.mem_filter, decide_eq_true_eq] at hx hy
    rw [hdiv x hx.1] at hx; rw [hdiv y hy.1] at hy
    have ex := Nat.div_add_mod x β
    have ey := Nat.div_add_mod y β
    rw [hx.2] at ex; rw [hy.2] at ey
    omega
  · refine (List.pairwise_lt_range).imp_of_mem ?_
    intro a b _ _ hab x hx y hy
    simp only [csBlk, List.mem_filter, decide_eq_true_eq] at hx hy
    rw [hdiv x hx.1] at hx; rw [hdiv y hy.1] at hy
    by_contra hxy
    have := Nat.div_le_div_right (c := β) (not_lt.1 hxy)
    omega

/-! ### Positions in the concatenation -/

section pos

variable (κ : ℕ → ℕ) (L : List ℕ)

theorem csS_mono {t t' : ℕ} (h : t ≤ t') : (csS κ L t).length ≤ (csS κ L t').length := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (length_csS_le κ L _)

theorem csS_start_lt {t t' : ℕ} (h : t < t') :
    (csS κ L t).length + (csBlk κ L t).length ≤ (csS κ L t').length := by
  have := csS_mono κ L (show t + 1 ≤ t' by omega)
  rw [csS_succ, List.length_append] at this; exact this

/-- Every position of the concatenation lies in a block. -/
theorem csS_find {β p : ℕ} (hp : p < (csS κ L β).length) :
    ∃ t < β, (csS κ L t).length ≤ p ∧ p < (csS κ L t).length + (csBlk κ L t).length := by
  induction β with
  | zero => simp [csS] at hp
  | succ β ih =>
    by_cases h : p < (csS κ L β).length
    · obtain ⟨t, ht, h1, h2⟩ := ih h; exact ⟨t, by omega, h1, h2⟩
    · rw [csS_succ, List.length_append] at hp
      exact ⟨β, by omega, by omega, hp⟩

theorem csS_value {β p : ℕ} (hp : p < (csS κ L β).length) {f : ℕ → ℕ}
    (hf : ∀ t < β, ∀ j < (csBlk κ L t).length,
      f ((csS κ L t).length + j) = (csBlk κ L t).getD j 0) :
    f p = (csS κ L β).getD p 0 := by
  obtain ⟨t, ht, h1, h2⟩ := csS_find κ L hp
  obtain ⟨j, rfl⟩ : ∃ j, p = (csS κ L t).length + j := ⟨p - (csS κ L t).length, by omega⟩
  rw [hf t ht j (by omega), csS_getElem κ L (by omega) ht]

end pos

end Piece

end PlanarSeparator
