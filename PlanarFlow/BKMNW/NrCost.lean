module

public import PlanarFlow.BKMNW.NrSpec
public import PlanarFlow.BKMNW.CsScale

/-!
# The steps of `retP`, `frmP` within the scaled push-back budget

* `nrPassCost_eq`, `heapLg2_le` (`Heap.lg (2 n) ≤ 2 lg n`);
* **`retCost_le_cMachS`**, **`frmCost_le_cMachS`**: for `1 ≤ C`, `1 ≤ m`, `nf ≤ m ≤ L`,
  `retCost m nf`, `frmCost m nf ≤ (cMachS C C₀).pushRun m nf L + (cMachS C C₀).lin L` (the budget
  of `retP`/`frmP` in `mfMain_cMachSGEG`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open NegSSSP

lemma nrPassCost_eq (m n : ℕ) : nrPassCost m n = 75 * m + 70 * n + 13 * Heap.lg (2 * n) +
    23 * (n * Heap.lg (2 * n)) + 13 * (Heap.lg (2 * n) * m) + 83 := by
  unfold nrPassCost osCost; ring

lemma heapLg2_le (n : ℕ) : Heap.lg (2 * n) ≤ 2 * lg n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Heap.lg_zero]
  · rw [Heap.lg_pos (by omega), show 2 * n / 2 = n by omega]
    have := heap_lg_le n; have := one_le_lg n; omega

/-- **The steps of `retP` within the push-back budget of `cMachS`.** -/
theorem retCost_le_cMachS {C C₀ m nf L : ℕ} (hC : 1 ≤ C) (hm : 1 ≤ m) (hnf : nf ≤ m)
    (hL : m ≤ L) :
    retCost m nf ≤ (cMachS C C₀).pushRun m nf L + (cMachS C C₀).lin L := by
  unfold retCost fcCost pchCost
  rw [nrPassCost_eq]
  unfold SubCosts.pushRun
  simp only [cMachS]
  obtain ⟨H, hH⟩ : ∃ H, Heap.lg (2 * nf) = H := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, lg nf = g := ⟨_, rfl⟩
  rw [hH, hg]
  have hHg : H ≤ 2 * g := by rw [← hH, ← hg]; exact heapLg2_le nf
  have hg1 : 1 ≤ g := by rw [← hg]; exact one_le_lg nf
  have e1 : nf * H ≤ 2 * (nf * g) := by
    calc nf * H ≤ nf * (2 * g) := Nat.mul_le_mul_left _ hHg
      _ = 2 * (nf * g) := by ring
  have e2 : H * m ≤ 2 * (m * g) := by
    calc H * m ≤ (2 * g) * m := Nat.mul_le_mul_right _ hHg
      _ = 2 * (m * g) := by ring
  have e3 : m ≤ m * g := Nat.le_mul_of_pos_right _ hg1
  have e4 : nf * g ≤ nf * g ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
  have e5 : g ≤ m * g := Nat.le_mul_of_pos_left _ hm
  have e6 : L ≤ C * L := Nat.le_mul_of_pos_left _ hC
  have hK : 1 ≤ csK := by unfold csK; norm_num
  have f1 : 6300 * (nf * g ^ 2 + m * g) ≤ csK * (6300 * (nf * g ^ 2 + m * g)) :=
    Nat.le_mul_of_pos_left _ hK
  have f2 : 1000 * (C * L) ≤ csK * (C * L) := by
    have : 1000 ≤ csK := by unfold csK; norm_num
    exact Nat.mul_le_mul_right _ this
  omega

/-- **The steps of `frmP` within the push-back budget of `cMachS`.** -/
theorem frmCost_le_cMachS {C C₀ m nf L : ℕ} (hC : 1 ≤ C) (hm : 1 ≤ m) (hnf : nf ≤ m)
    (hL : m ≤ L) :
    frmCost m nf ≤ (cMachS C C₀).pushRun m nf L + (cMachS C C₀).lin L := by
  have := retCost_le_cMachS (C₀ := C₀) hC hm hnf hL
  unfold frmCost; unfold retCost at this; omega

end BKMNW

end PlanarFlow
