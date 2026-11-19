module

public import PlanarFlow.BKMNW.MsCost

/-!
# The step bound of the MSSP call with slack

**`msCost'_slack_cMachS`**: for `1 ≤ m` and `q ≤ 2 k`,
`msCost' msEncCost KCf ZCf m k q + 200 k² + 2000 k + 2000 ≤ (cMachS C C₀).mssp m k`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset Klein NegSSSP

set_option maxHeartbeats 2000000 in
/-- **The step bound of the MSSP call is within `cMachS.mssp` with slack** `200 k² + 2000 k + 2000`
(`1 ≤ m`, `q ≤ 2 k`): room for the FR image written once per call by the node step. -/
theorem msCost'_slack_cMachS (C C₀ : ℕ) {m k q : ℕ} (hm : 1 ≤ m) (hq : q ≤ 2 * k) :
    MsCall.msCost' msEncCost (fun m k _ => KCf m k) (fun m _ _ => ZCf m) m k q +
      200 * k ^ 2 + 2000 * k + 2000 ≤ (cMachS C C₀).mssp m k := by
  have hL1 := BKMNW.one_le_lg m
  have hstd := stdCost_le hm
  have hlog : Nat.log 2 (20 * m + 1) ≤ BKMNW.lg m + 7 := by
    have := log_le_256 hm (x := 20 * m + 1) (by omega); unfold BKMNW.lg; omega
  set L := BKMNW.lg m with hLd
  have hX : m ≤ m * L := Nat.le_mul_of_pos_right m (by omega)
  have hkk : k ≤ k * k := Nat.le_mul_self k
  have hY : k * k ≤ k ^ 2 * L := by rw [sq]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hqq : q * q ≤ 2 * k * (2 * k) := Nat.mul_le_mul hq hq
  -- Klein's run
  have hop : DynTree.opCostE (20 * m + 1) ≤ 3000000 * L := by
    unfold DynTree.opCostE; omega
  have hops : kleinOpsM (2 * m) (2 * m + 1) (5 * m) (5 * m) m (2 * k) (2 * k) ≤
      391 * m + 4 * (k * k) := by
    unfold kleinOpsM
    have : 2 * k * (2 * k) = 4 * (k * k) := by ring
    omega
  have hext : kleinExtM (2 * m) (2 * m + 1) (5 * m) (5 * m) m (2 * k) (2 * k) ≤
      1000 * m + 56 * (k * k) + 120 := by
    unfold kleinExtM
    have : 2 * k * (2 * k) = 4 * (k * k) := by ring
    omega
  have hprod := Nat.mul_le_mul hops hop
  have e1 : (391 * m + 4 * (k * k)) * (3000000 * L) =
      1173000000 * (m * L) + 12000000 * (k * k * L) := by ring
  have hY' : k * k * L = k ^ 2 * L := by ring
  have hKC : KCf m k ≤ 5000000000 * (m * L) + 50000001000 * (k ^ 2 * L) := by
    unfold KCf MsCall.kSteps
    omega
  -- the encoder
  have cxtAL : hpCost xtAL = 40 := by decide +kernel
  have cxtBL : hpCost xtBL = 33 := by decide +kernel
  have cxtWL : hpCost xtWL = 49 := by decide +kernel
  have cmkWL : hpCost mkWL = 25 := by decide +kernel
  have cslAL : hpCost slAL = 29 := by decide +kernel
  have cslWL : hpCost slWL = 21 := by decide +kernel
  have cdh1L : hpCost dh1L = 45 := by decide +kernel
  have cdh2L : hpCost dh2L = 11 := by decide +kernel
  have cdh3L : hpCost dh3L = 38 := by decide +kernel
  have cdh4L : hpCost dh4L = 254 := by decide +kernel
  have cdh5L : hpCost dh5L = 45 := by decide +kernel
  have ctwSL : hpCost twSL = 42 := by decide +kernel
  have ctwWL : hpCost twWL = 25 := by decide +kernel
  have ckiL : hpCost kiL = 124 := by decide +kernel
  have cosL : hpCost osL = 122 := by decide +kernel
  have cceSL : hpCost ceSL = 14 := by decide +kernel
  have cceWL : hpCost ceWL = 21 := by decide +kernel
  have ckpSL : hpCost kpSL = 56 := by decide +kernel
  have ckPrmL : hpCost kPrmL = 556 := by decide +kernel
  have cfnAL : hpCost fnAL = 70 := by decide +kernel
  have cfnBL : hpCost fnBL = 14 := by decide +kernel
  have cmsLayL : hpCost msLayL = 247 := by decide +kernel
  have cfcL : hpCost fcL = 42 := by decide +kernel
  have cckL : hpCost ckL = 98 := by decide +kernel
  have hEnc : msEncCost m k q ≤ 2100000 * (m * L) + 11 * k + 17 * q + 200000 := by
    unfold msEncCost costA1 costA2 fcCost cutCost StEnc.ivCost costC2 StEnc.kiCost osCost
      costE2 dLen
    omega
  have hZ : ZCf m ≤ 300 * m + 20 := by unfold ZCf dLen; omega
  unfold MsCall.msCost'
  show msEncCost m k q + 27 * KCf m k + 5 * ZCf m + 23 * (q * q) + 40 + 200 * k ^ 2 + 2000 * k +
    2000 ≤ csK * (24637500000 * (m * L + k ^ 2 * L))
  have hk2 : k ≤ k ^ 2 := by rw [sq]; exact Nat.le_mul_self k
  have hk3 : k ^ 2 ≤ k ^ 2 * L := Nat.le_mul_of_pos_right _ (by omega)
  unfold csK
  have e2 : 2 * k * (2 * k) = 4 * (k * k) := by ring
  omega

end MsEnc

end BKMNW

end PlanarFlow
