module

public import PlanarFlow.BKMNW.Nf9aB

/-!
# Bounds of the variables of the envelope expressions

For `X ≥ 1`, `m, Z ≤ X`: `spWs m ≤ 327 X²` (`spWs_le'`), `rtLM m Z ≤ 832 X⁵` (`rtLM_le'`),
`WNb m L ≤ 10³¹ X³²` (`WNb_le'`), `fxWB m L ≤ 10⁴⁰ X³²` (`fxWB_le'`) for `L ≤ 832 X⁵`, and the
logarithms (`logs_le`, `m + 1 ≤ X`). Each bound is `eval_le_of` (`Nf9aA`) on the expressions of
`Nf9aB`, the coefficient and the degree computed by the kernel. Used by `Nf9aG` (`fixP7`) and
`Nf9aF` (the frozen fix), which are independent of each other.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace P9

open Finset NegSSSP NegSSSP.PE NegSSSP.Frame MsEnc

/-- `fP2 b ≤ 2 b fLv b + 2`. -/
lemma fP2_le (b : ℕ) : MsCall.fP2 b ≤ 2 * (b * MsCall.fLv b) + 2 := by
  unfold MsCall.fP2
  rw [pow_succ]
  rcases Nat.eq_zero_or_pos (b * MsCall.fLv b) with h | h
  · rw [h]; simp
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.1 h)
    omega

/-- **`spWs n ≤ 327 X²`.** -/
theorem spWs_le' {n X : ℕ} (hX : 1 ≤ X) (hn : n ≤ X) : spWs n ≤ 327 * X ^ 2 := by
  have hl := log2_le (3 * n)
  have hB : AllB X [n, Nat.log 2 (3 * n)] [1, 3] [1, 1] :=
    .cons (by simpa using hn) (.cons (by rw [pow_one]; omega) .nil)
  calc spWs n = eval (lv [n, Nat.log 2 (3 * n)]) (spWsP (var 0) (var 1)) :=
        (eval_spWsP (lv [n, Nat.log 2 (3 * n)]) (var 0) (var 1) rfl).symm
    _ ≤ 327 * X ^ 2 := eval_le_of hX (AllB.get hB) _ (by decide +kernel) (by decide +kernel)

/-- **`rtLM m Z ≤ 832 X⁵`.** -/
theorem rtLM_le' {m Z X : ℕ} (hX : 1 ≤ X) (hm : m ≤ X) (hZ : Z ≤ X) :
    rtLM m Z ≤ 832 * X ^ 5 := by
  have hB : AllB X [m, Z] [1, 1] [1, 1] :=
    .cons (by simpa using hm) (.cons (by simpa using hZ) .nil)
  calc rtLM m Z = eval (lv [m, Z]) (rtLMP (var 0) (var 1)) := rfl
    _ ≤ 832 * X ^ 5 := eval_le_of hX (AllB.get hB) _ (by decide +kernel) (by decide +kernel)

/-- **`WNb m L ≤ 10³¹ X³²`** for `L ≤ 832 X⁵`. -/
theorem WNb_le' {m L X : ℕ} (hX : 1 ≤ X) (hm : m ≤ X) (hL : L ≤ 832 * X ^ 5) :
    WNb m L ≤ 10 ^ 31 * X ^ 32 := by
  have hB : AllB X [m, L, spWs m] [1, 832, 327] [1, 5, 2] :=
    .cons (by simpa using hm) (.cons hL (.cons (spWs_le' hX hm) .nil))
  calc WNb m L = eval (fxρ m L) WNbE := (eval_WNbE (fxρ m L) rfl).symm
    _ ≤ 10 ^ 31 * X ^ 32 := eval_le_of hX (AllB.get hB) _ (by decide +kernel) (by decide +kernel)

/-- **`fxWB m L ≤ 10⁴⁰ X³²`** for `L ≤ 832 X⁵`. -/
theorem fxWB_le' {m L X : ℕ} (hX : 1 ≤ X) (hm : m ≤ X) (hL : L ≤ 832 * X ^ 5) :
    fxWB m L ≤ 10 ^ 40 * X ^ 32 := by
  have hB : AllB X [m, L, spWs m] [1, 832, 327] [1, 5, 2] :=
    .cons (by simpa using hm) (.cons hL (.cons (spWs_le' hX hm) .nil))
  show evalU (fxρ m L) WNbE ≤ 10 ^ 40 * X ^ 32
  exact evalU_le_of hX (AllB.get hB) _ (by decide +kernel) (by decide +kernel)

/-- `fLv (2m) ≤ 2 X`, `fP2 (2m) ≤ 14 X²`, `lg m ≤ X`, `lg (2m) ≤ 2X` for `m + 1 ≤ X`. -/
lemma logs_le {m X : ℕ} (hm : m + 1 ≤ X) :
    MsCall.fLv (2 * m) ≤ 2 * X ^ 1 ∧ MsCall.fP2 (2 * m) ≤ 14 * X ^ 2 ∧ lg m ≤ 1 * X ^ 1 ∧
      lg (2 * m) ≤ 2 * X ^ 1 ∧ Nat.log 2 (20 * m + 1) ≤ 21 * X ^ 1 := by
  have h1 : MsCall.fLv (2 * m) ≤ 2 * m + 1 := by
    unfold MsCall.fLv; have := log2_le (2 * m); omega
  have h2 := fP2_le (2 * m)
  have h3 : 2 * m * MsCall.fLv (2 * m) ≤ 2 * m * (2 * m + 1) := Nat.mul_le_mul_left _ h1
  have h4 : m * m ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
  have h5 : X ≤ X * X := Nat.le_mul_self X
  have e : 2 * m * (2 * m + 1) = 4 * (m * m) + 2 * m := by ring
  have h6 := lg_le m
  have h7 := lg_le (2 * m)
  have h8 := log2_le (20 * m + 1)
  simp only [pow_one, one_mul, sq]
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

end P9

end BKMNW

end PlanarFlow
