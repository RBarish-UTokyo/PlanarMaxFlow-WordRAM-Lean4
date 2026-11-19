module

public import PlanarFlow.BKMNW.Nf9aC

/-!
# Explicit polynomial bounds of the envelopes of `fixP7` for the MSSP encoder

With `X = m + Z + 1` (resp. `N + Z + 1`):

* **`wzF7_wzm_le`**: `wzF7 MsEnc.wzm m Z ≤ 10 ^ 41 * (m + Z + 1) ^ 32`;
* **`rOF7_Rm_le`**: `rOF7 3200000 C₀ MsEnc.Rm m Z ≤ 10 ^ 41 * (m + Z + 1) ^ 32`;
* **`rF7_Rm_le`**: `rF7 3200000 C₀ MsEnc.Rm N Z ≤ 10 ^ 41 * (N + Z + 1) ^ 33`.

`eval_le_of` on `wzF7P`, `rOF7P` (`Nf9aB`) with the variable bounds of `Nf9aC`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace P9

open Finset NegSSSP NegSSSP.PE NegSSSP.Frame MsEnc

/-- **The zero area of `fixP7` for the MSSP encoder**: `wzF7 MsEnc.wzm m Z ≤ 10⁴¹ (m + Z + 1)³²`. -/
theorem wzF7_wzm_le (m Z : ℕ) : wzF7 MsEnc.wzm m Z ≤ 10 ^ 41 * (m + Z + 1) ^ 32 := by
  have hX : 1 ≤ m + Z + 1 := by omega
  have hm : m ≤ m + Z + 1 := by omega
  have hZ : Z ≤ m + Z + 1 := by omega
  have hL := rtLM_le' hX hm hZ
  obtain ⟨l1, l2, l3, l4, -⟩ := logs_le (m := m) (X := m + Z + 1) (by omega)
  have hB : AllB (m + Z + 1) [m, Z, MsCall.fLv (2 * m), MsCall.fP2 (2 * m), spWs m,
      WNb m (rtLM m Z), fxWB m (rtLM m Z), lg m, lg (2 * m)]
      [1, 1, 2, 14, 327, 10 ^ 31, 10 ^ 40, 1, 2] [1, 1, 1, 2, 2, 32, 32, 1, 1] :=
     .cons (by simpa using hm) (.cons (by simpa using hZ) (.cons l1 (.cons l2
      (.cons (spWs_le' hX hm) (.cons (WNb_le' hX hm hL) (.cons (fxWB_le' hX hm hL)
      (.cons l3 (.cons l4 .nil))))))))
  rw [eval_wzF7P rfl rfl rfl rfl rfl rfl rfl]
  exact eval_le_of hX (AllB.get hB) _ (by decide +kernel) (by decide +kernel)

/-- **The room of `fixP7` at a frame of `m` darts for the MSSP encoder**:
`rOF7 3200000 C₀ MsEnc.Rm m Z ≤ 10⁴¹ (m + Z + 1)³²`. -/
theorem rOF7_Rm_le (C₀ m Z : ℕ) : rOF7 3200000 C₀ MsEnc.Rm m Z ≤ 10 ^ 41 * (m + Z + 1) ^ 32 := by
  have hX : 1 ≤ m + Z + 1 := by omega
  have hm : m ≤ m + Z + 1 := by omega
  have hZ : Z ≤ m + Z + 1 := by omega
  have hL := rtLM_le' hX hm hZ
  obtain ⟨-, -, l3, l4, l5⟩ := logs_le (m := m) (X := m + Z + 1) (by omega)
  have hB : AllB (m + Z + 1) (rOρ m Z) [1, 1, 2, 21, 1, 327, 10 ^ 40] [1, 1, 1, 1, 1, 2, 32] := by
    unfold rOρ
    exact .cons (by simpa using hm) (.cons (by simpa using hZ) (.cons l4 (.cons l5
      (.cons l3 (.cons (spWs_le' hX hm) (.cons (fxWB_le' hX hm hL) .nil))))))
  exact (rOF7_le_eval C₀ m Z).trans
    (eval_le_of hX (AllB.get hB) _ (by decide +kernel) (by decide +kernel))

/-- **The room of `fixP7` for the MSSP encoder**:
`rF7 3200000 C₀ MsEnc.Rm N Z ≤ 10⁴¹ (N + Z + 1)³³`. -/
theorem rF7_Rm_le (C₀ N Z : ℕ) : rF7 3200000 C₀ MsEnc.Rm N Z ≤ 10 ^ 41 * (N + Z + 1) ^ 33 := by
  unfold rF7
  calc ∑ m ∈ range (N + 1), rOF7 3200000 C₀ MsEnc.Rm m Z
      ≤ ∑ _m ∈ range (N + 1), 10 ^ 41 * (N + Z + 1) ^ 32 :=
        sum_le_sum fun m hm => (rOF7_Rm_le C₀ m Z).trans (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left (by have := mem_range.1 hm; omega) _))
    _ = (N + 1) * (10 ^ 41 * (N + Z + 1) ^ 32) := by
        simp only [sum_const, card_range, smul_eq_mul]
    _ ≤ (N + Z + 1) * (10 ^ 41 * (N + Z + 1) ^ 32) := Nat.mul_le_mul_right _ (by omega)
    _ = 10 ^ 41 * (N + Z + 1) ^ 33 :=
        (fun (X : ℕ) => (by ring : X * (10 ^ 41 * X ^ 32) = 10 ^ 41 * X ^ 33)) _

end P9

end BKMNW

end PlanarFlow
