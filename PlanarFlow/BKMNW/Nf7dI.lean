module

public import PlanarFlow.BKMNW.Nf7dH

/-!
# The cost of `fixP7` within `(cMachS C C₀).fixRun`

* **`posT_le_fixRun`**: `posT C C₀ cost m k b + 9 ≤ (cMachS C C₀).fixRun m b k L` whenever
  `1 ≤ C`, `1 ≤ m`, `1 ≤ b ≤ 2k`, `k ≤ m` and the MSSP call costs at most the `mssp` field
  (`cost m k b ≤ (cMachS C C₀).mssp m k`). **No slack in the MSSP field is needed**: the image
  (`O(b²)`, `b ≤ 2k`) is paid by the `k · lin b` term of the stages (`lin b = 10¹⁵ C b`), the
  linear parts by `negsssp` (`cMachS_negsssp_negT`, `negsssp_ge`).
* **`zT_le_fixRun`**: `zT C C₀ m + 9 ≤ (cMachS C C₀).fixRun m b k L` (`1 ≤ m`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

/-- **The steps of the branch `0 < k` fit the scaled budget** (see the module docstring). -/
theorem posT_le_fixRun {C C₀ : ℕ} (hC : 1 ≤ C) {cost : ℕ → ℕ → ℕ → ℕ} {m k b L : ℕ}
    (hm : 1 ≤ m) (hb : 1 ≤ b) (hbk : b ≤ 2 * k) (hkm : k ≤ m)
    (hcost : cost m k b ≤ (cMachS C C₀).mssp m k) :
    posT C C₀ cost m k b + 9 ≤ (cMachS C C₀).fixRun m b k L := by
  have hloop := loopT_le_cMachS C C₀ (k := k) hb
  have hneg := cMachS_negsssp_negT (C := C) (C₀ := C₀) hm
  have hge := negsssp_ge C C₀ m
  have hlin : (cMachS C C₀).lin b = csK * (C * b) := rfl
  have hCb : b ≤ C * b := Nat.le_mul_of_pos_left b hC
  have hbb : b * b ≤ 2 * (k * b) := by
    have := Nat.mul_le_mul_right b hbk; rw [Nat.mul_assoc] at this; exact this
  have hkl : k * b ≤ k * (C * b) := Nat.mul_le_mul_left k hCb
  have hkL : 1000 * (k * (C * b)) ≤ k * (cMachS C C₀).lin b := by
    rw [hlin]
    have e : k * (csK * (C * b)) = csK * (k * (C * b)) := by ring
    rw [e]
    exact Nat.mul_le_mul_right _ (by unfold csK; norm_num)
  have hfr : k * (cMachS C C₀).fr b (2 * k) + k * (cMachS C C₀).lin b ≤
      k * ((cMachS C C₀).fr b (2 * k) + (cMachS C C₀).lin b) := by rw [Nat.mul_add]
  unfold SubCosts.fixRun posT finT st2T lySb
  generalize (cMach C C₀).negsssp m = NS at hneg hge
  generalize MfDrv.negT C C₀ m = NT at hneg
  generalize (cMachS C C₀).negsssp m = NSS at hneg ⊢
  generalize (cMachS C C₀).fr b (2 * k) = FR at hloop hfr ⊢
  generalize (cMachS C C₀).lin b = LB at hkL hfr ⊢
  generalize k * (C * b) = KCB at hkl hkL
  generalize b * b = BB at hbb ⊢
  generalize k * b = KB at hbb hkl
  have h1 : 10 ^ 19 * m ≤ NS := hge
  omega

/-- **The steps of the branch `k = 0` fit the scaled budget.** -/
theorem zT_le_fixRun {C C₀ : ℕ} {m b k L : ℕ} (hm : 1 ≤ m) :
    zT C C₀ m + 9 ≤ (cMachS C C₀).fixRun m b k L := by
  have hneg := cMachS_negsssp_negT (C := C) (C₀ := C₀) hm
  have hge := negsssp_ge C C₀ m
  unfold SubCosts.fixRun zT finT
  generalize (cMach C C₀).negsssp m = NS at hneg hge
  generalize MfDrv.negT C C₀ m = NT at hneg
  generalize (cMachS C C₀).negsssp m = NSS at hneg ⊢
  omega

end BKMNW

end PlanarFlow
