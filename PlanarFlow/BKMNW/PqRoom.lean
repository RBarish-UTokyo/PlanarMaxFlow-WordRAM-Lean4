module

public import PlanarFlow.BKMNW.PqTop

/-!
# The word bound of the pipeline as one polynomial

`PipeRoomS R a p d W` (`PqPipe.lean`) follows from a single polynomial bound on `W` when the room
per call is polynomial, `R N Z ≤ r (N + Z + 1) ^ q`:

**`pipeRoomS_of_pow`**: `(20 (r + a) + 1000000) · (7 (n + K + zb d + 2)) ^ (p + q + 4) ≤ W`
gives `PipeRoomS R a p d W` (`n = nd d`, `K = nv d`, `zb d = ∑ cp`); so the maximum-flow theorem holds
for every word size polynomial in `n + K + ∑ cp`, with the degree `p + q + 4`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Feas

/-- **The word bound of the pipeline, one polynomial.** -/
def pipeW (r a p q : ℕ) (d : List ℕ) : ℕ :=
  (20 * (r + a) + 1000000) * (7 * (nd d + nv d + zb d + 2)) ^ (p + q + 4)

theorem pipeRoomS_of_pow {R : ℕ → ℕ → ℕ} {r a p q : ℕ} (hR : ∀ N Z, R N Z ≤ r * (N + Z + 1) ^ q)
    {d : List ℕ} {W : ℕ} (hW : pipeW r a p q d ≤ W) : PipeRoomS R a p d W := by
  unfold pipeW at hW
  set X := nd d + nv d + zb d + 2 with hX
  set Y := 7 * X with hYd
  set k := p + q + 4 with hk
  set A := Y ^ k with hA
  clear_value A k Y X
  have hY : 14 ≤ Y := by omega
  have hY1 : 1 ≤ Y := by omega
  have pw : ∀ i, i ≤ k → Y ^ i ≤ A := fun i hi => hA ▸ Nat.pow_le_pow_right hY1 hi
  have hA1 : 1 ≤ A := hA ▸ (Nat.one_le_pow _ _ (by omega))
  have hYA : Y ≤ A := by have := pw 1 (by omega); simpa using this
  have hY2 : Y * Y ≤ A := by have := pw 2 (by omega); rw [pow_two] at this; exact this
  have hYp : Y ^ p ≤ A := pw p (by omega)
  have hYq1 : Y * Y ^ q ≤ A := by
    have := pw (q + 1) (by omega); rw [pow_succ, Nat.mul_comm] at this; exact this
  have hYp2 : Y * Y * Y ^ p ≤ A := by
    have := pw (p + 2) (by omega); rw [pow_add, pow_two, Nat.mul_comm] at this; exact this
  -- the main factor
  have hF : (20 * (r + a) + 1000000) * A ≤ W := hW
  have hFa : a * A ≤ (20 * (r + a) + 1000000) * A := Nat.mul_le_mul_right _ (by omega)
  have hFr : r * A ≤ (20 * (r + a) + 1000000) * A := Nat.mul_le_mul_right _ (by omega)
  have hF1 : 1000000 * A ≤ (20 * (r + a) + 1000000) * A := Nat.mul_le_mul_right _ (by omega)
  have hFsum : 10 * (a * A) + 15 * (r * A) + 1000000 * A ≤ (20 * (r + a) + 1000000) * A := by
    have : (20 * (r + a) + 1000000) * A = 20 * (r * A) + 20 * (a * A) + 1000000 * A := by ring
    omega
  -- the base and the power
  have hb : 7 * nd d + zb d + 1 ≤ Y := by omega
  have hbp : (7 * nd d + zb d + 1) ^ p ≤ Y ^ p := Nat.pow_le_pow_left hb p
  have hzB : zB a p d ≤ a * A + 1 := by
    unfold zB; have := Nat.mul_le_mul_left a (hbp.trans hYp); omega
  have hR7 : R (7 * nd d) (zb d) ≤ r * Y ^ q := by
    refine (hR _ _).trans (Nat.mul_le_mul_left r (Nat.pow_le_pow_left (by omega) q))
  -- the products
  have hnK : (2 * (nv d + nd d) + 1) * (7 * nd d) ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
  have hnz : (7 * nd d + 2) * (zb d + 1) ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
  have hlast : (14 * nd d + 1) * (770 * nd d + 80 + R (7 * nd d) (zb d)) ≤
      2 * Y * (110 * Y + r * Y ^ q) := Nat.mul_le_mul (by omega) (by omega)
  have hlast' : 2 * Y * (110 * Y + r * Y ^ q) ≤ 220 * A + 2 * (r * A) := by
    have e : 2 * Y * (110 * Y + r * Y ^ q) = 220 * (Y * Y) + 2 * (r * (Y * Y ^ q)) := by
      rw [Nat.mul_add]; ring
    have := Nat.mul_le_mul_left r hYq1
    omega
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

end Pp

end BKMNW

end PlanarFlow
