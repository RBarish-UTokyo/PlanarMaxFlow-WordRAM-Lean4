module

public import PlanarFlow.BKMNW.Nf9aC

/-!
# Explicit polynomial bounds of the envelopes of the frozen fix

The envelopes `F9b.wzF9 wzm m Z`, `F9b.rOF9 C C₀ Rm m Z` (`Nf9bL`) are copied
verbatim (up to the equal names `KM = KM9`, `LM = LM9`, `shwM = shw9`, `lgT = lgT9`,
`RmS = RmS9`) as **`wzF9c`**, **`valM9c`**, **`rOF9c`**, so that this file does not depend on the
`Nf9b*` files; `F9b.wzF9 wzm m Z = wzF9c wzm m Z` and `F9b.rOF9 C C₀ Rm m Z = rOF9c C C₀ Rm m Z` hold by
`rfl` (see `Nf9aH`, which imports `Nf9bO`). With `X = m + Z + 1`:

* **`wzF9c_wzm_le`**: `wzF9c MsEnc.wzm m Z ≤ 10 ^ 42 * (m + Z + 1) ^ 33`;
* **`rOF9c_Rm_le`**: `rOF9c 3200000 C₀ MsEnc.Rm m Z ≤ 10 ^ 42 * (m + Z + 1) ^ 33`.

The summands (`n ≤ m`) are bounded by `eval_le_of` on `tP9P` (`≤ 10⁴¹ X³²`), `rnP`
(`≤ 10⁴¹ X³²`), the rest by `shwMP` (`≤ 10⁹ X¹⁰`) and `restP` (`≤ 10⁶ X⁵`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace P9

open Finset NegSSSP NegSSSP.PE NegSSSP.Frame MsEnc MfDrv NsStep

/-! ### Copies of the envelopes -/

/-- `wzF9` (the zero area of the frozen fix). -/
def wzF9c (wzm : ℕ → ℕ → ℕ) (m Z : ℕ) : ℕ :=
  ∑ n ∈ range (m + 1), (wzm n (2 * Z) + (9 * n + 1 + tsz n) + rtW n (n * BKMNW.KM m Z) n) +
    shwM m Z

/-- `valM9`. -/
def valM9c (m Z : ℕ) : ℕ :=
  4 * (m * Z) + 20 * BKMNW.KM m Z + 2 * BKMNW.LM m Z + 2 * moOf (2 * m) (BKMNW.LM m Z) +
    3 * (m * BKMNW.KM m Z) + 3 * Z + m + 300 +
    ∑ n ∈ range (m + 1), (spWs n + fxWB n (n * BKMNW.KM m Z))

/-- `rOF9` (the room of the frozen fix). -/
def rOF9c (C C₀ : ℕ) (Rm : ℕ → ℕ → ℕ → ℕ) (m Z : ℕ) : ℕ :=
  100 + 100 * m + lyP 0 (2 * m) m + lgT (2 * m) m +
    ∑ n ∈ range (m + 1), (RmS Rm n + MfDrv.negT C C₀ n) + valM9c m Z

/-! ### The expressions -/

def tP9P (n Z L S WN FX lgn lg2n : PE) : PE :=
  wzmP n (2 * Z) + (9 * n + 1 + tszP n) + rtWP n L n S WN FX lgn lg2n
def rnP (n l lgn S FX : PE) : PE := RmSP n l + negTP n lgn + (S + FX)
def restP (m Z lg2m : PE) : PE :=
  100 + 100 * m + lyPP 0 (2 * m) m + lgTP (2 * m) m lg2m +
    (4 * (m * Z) + 20 * KMfP m Z + 2 * LMP m Z + 2 * moOfP (2 * m) (LMP m Z) + 3 * rtLMP m Z +
      3 * Z + m + 300)

/-- The value of `tP9P` (the variables given by equations, see `eval_wzF7P`). -/
theorem eval_tP9P {n Z L S WN FX l1 l2 : ℕ} (hS : S = spWs n) (hW : WN = WNb n L)
    (hF : FX = fxWB n L) (h1 : l1 = lg n) (h2 : l2 = lg (2 * n)) :
    MsEnc.wzm n (2 * Z) + (9 * n + 1 + tsz n) + rtW n L n =
      eval (lv [n, Z, L, S, WN, FX, l1, l2])
        (tP9P (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) := by
  have e1 := eval_wzmP (lv [n, Z, L, S, WN, FX, l1, l2]) (var 0) (2 * var 1)
  have e3 := eval_rtWP (lv [n, Z, L, S, WN, FX, l1, l2]) (var 0) (var 2) (var 3) (var 4)
    (var 5) (var 6) (var 7) hS hW hF h1 h2
  have e4 : eval (lv [n, Z, L, S, WN, FX, l1, l2])
      (tP9P (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) =
      eval (lv [n, Z, L, S, WN, FX, l1, l2]) (wzmP (var 0) (2 * var 1)) +
      (9 * n + 1 + 2 * ((n + 1) * (n + 1))) +
      eval (lv [n, Z, L, S, WN, FX, l1, l2])
        (rtWP (var 0) (var 2) (var 0) (var 3) (var 4) (var 5) (var 6) (var 7)) := rfl
  rw [e4, e1, e3]
  rfl

/-- **A summand of `wzF9c`**: `≤ 10⁴¹ X³²` for `n + 1 ≤ X`, `Z ≤ X`, `L ≤ 832 X⁵`. -/
theorem tP9_le {n Z L X : ℕ} (hn : n + 1 ≤ X) (hZ : Z ≤ X) (hL : L ≤ 832 * X ^ 5) :
    MsEnc.wzm n (2 * Z) + (9 * n + 1 + tsz n) + rtW n L n ≤ 10 ^ 41 * X ^ 32 := by
  have hX : 1 ≤ X := by omega
  have hn' : n ≤ X := by omega
  obtain ⟨-, -, l3, l4, -⟩ := logs_le hn
  have hB : AllB X [n, Z, L, spWs n, WNb n L, fxWB n L, lg n, lg (2 * n)]
      [1, 1, 832, 327, 10 ^ 31, 10 ^ 40, 1, 2] [1, 1, 5, 2, 32, 32, 1, 1] :=
    .cons (by simpa using hn') (.cons (by simpa using hZ) (.cons hL (.cons (spWs_le' hX hn')
      (.cons (WNb_le' hX hn' hL) (.cons (fxWB_le' hX hn' hL) (.cons l3 (.cons l4 .nil)))))))
  rw [eval_tP9P rfl rfl rfl rfl rfl]
  exact eval_le_of hX (AllB.get hB) _ (by decide +kernel) (by decide +kernel)

/-- `shwM m Z ≤ 10⁹ X¹⁰` for `m + 1 ≤ X`, `Z ≤ X`. -/
theorem shwM_le' {m Z X : ℕ} (hm : m + 1 ≤ X) (hZ : Z ≤ X) : shwM m Z ≤ 10 ^ 9 * X ^ 10 := by
  have hX : 1 ≤ X := by omega
  obtain ⟨l1, l2, -⟩ := logs_le hm
  have hB : AllB X [m, Z, MsCall.fLv (2 * m), MsCall.fP2 (2 * m)] [1, 1, 2, 14] [1, 1, 1, 2] :=
    .cons (by simpa using (show m ≤ X by omega)) (.cons (by simpa using hZ) (.cons l1
      (.cons l2 .nil)))
  calc shwM m Z = eval (lv [m, Z, MsCall.fLv (2 * m), MsCall.fP2 (2 * m)])
        (shwMP (var 0) (var 1) (var 2) (var 3)) :=
      (eval_shwMP (lv [m, Z, MsCall.fLv (2 * m), MsCall.fP2 (2 * m)]) (var 0) (var 1) (var 2)
        (var 3) rfl rfl).symm
    _ ≤ 10 ^ 9 * X ^ 10 := eval_le_of hX (AllB.get hB) _ (by decide +kernel) (by decide +kernel)

/-- **The zero area of the frozen fix for the MSSP encoder**:
`wzF9c MsEnc.wzm m Z ≤ 10⁴² (m + Z + 1)³³`. -/
theorem wzF9c_wzm_le (m Z : ℕ) : wzF9c MsEnc.wzm m Z ≤ 10 ^ 42 * (m + Z + 1) ^ 33 := by
  have hX : 1 ≤ m + Z + 1 := by omega
  have hL0 := rtLM_le' hX (show m ≤ m + Z + 1 by omega) (show Z ≤ m + Z + 1 by omega)
  have hs : ∑ n ∈ range (m + 1), (MsEnc.wzm n (2 * Z) + (9 * n + 1 + tsz n) +
      rtW n (n * BKMNW.KM m Z) n) ≤ ∑ _n ∈ range (m + 1), 10 ^ 41 * (m + Z + 1) ^ 32 :=
    sum_le_sum fun n hn => by
      have hn' := mem_range.1 hn
      have hLn : n * BKMNW.KM m Z ≤ 832 * (m + Z + 1) ^ 5 :=
        (Nat.mul_le_mul_right _ (by omega)).trans hL0
      exact tP9_le (by omega) (by omega) hLn
  rw [sum_const, card_range, smul_eq_mul] at hs
  have hsh := shwM_le' (m := m) (Z := Z) (X := m + Z + 1) (by omega) (by omega)
  have e1 : (m + Z + 1) ^ 10 ≤ (m + Z + 1) ^ 33 := Nat.pow_le_pow_right hX (by omega)
  have e2 : (m + 1) * (10 ^ 41 * (m + Z + 1) ^ 32) ≤ 10 ^ 41 * (m + Z + 1) ^ 33 := by
    calc (m + 1) * (10 ^ 41 * (m + Z + 1) ^ 32) ≤ (m + Z + 1) * (10 ^ 41 * (m + Z + 1) ^ 32) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 41 * (m + Z + 1) ^ 33 :=
        (fun (X : ℕ) => (by ring : X * (10 ^ 41 * X ^ 32) = 10 ^ 41 * X ^ 33)) _
  unfold wzF9c
  generalize (m + Z + 1) ^ 10 = A at hsh e1
  generalize (m + Z + 1) ^ 33 = Y at e1 e2 ⊢
  have f1 : 10 ^ 9 * A ≤ 10 ^ 9 * Y := Nat.mul_le_mul_left _ e1
  have f2 : 10 ^ 41 * Y + 10 ^ 9 * Y ≤ 10 ^ 42 * Y := by
    have : 10 ^ 41 * Y + 10 ^ 9 * Y = (10 ^ 41 + 10 ^ 9) * Y := by ring
    rw [this]; exact Nat.mul_le_mul_right _ (by norm_num)
  omega

/-- The summand of `rOF9c` (with that of `valM9c`) below the value of `rnP` (the variables
`S`, `FX` abstract, see `eval_wzF7P`). -/
theorem rn_le_eval (C₀ n S FX : ℕ) :
    RmS MsEnc.Rm n + MfDrv.negT 3200000 C₀ n + (S + FX) ≤
      eval (lv [n, Nat.log 2 (20 * n + 1), lg n, S, FX])
        (rnP (var 0) (var 1) (var 2) (var 3) (var 4)) := by
  have h1 := RmS_Rm_le n
  have h2 := eval_KCfP (lv [n, Nat.log 2 (20 * n + 1), lg n, S, FX]) (var 0) (var 1) rfl
  have h3 := eval_negTP (lv [n, Nat.log 2 (20 * n + 1), lg n, S, FX]) (var 0) (var 2) rfl C₀
  have e : eval (lv [n, Nat.log 2 (20 * n + 1), lg n, S, FX])
      (rnP (var 0) (var 1) (var 2) (var 3) (var 4)) =
      (n + 1) * ((2 * n + 1) * (860 * n + 100 + 2 * (2 * n) +
        3 * eval (lv [n, Nat.log 2 (20 * n + 1), lg n, S, FX]) (KCfP (var 0) (var 0) (var 1)) +
          1)) +
      eval (lv [n, Nat.log 2 (20 * n + 1), lg n, S, FX]) (negTP (var 0) (var 2)) + (S + FX) := rfl
  rw [e, h2, h3]
  exact Nat.add_le_add_right (Nat.add_le_add_right h1 _) _

/-- **A summand of `rOF9c`** (with the summand of `valM9c`): `≤ 10⁴¹ X³²`. -/
theorem rn_le {n X : ℕ} (C₀ : ℕ) {L : ℕ} (hn : n + 1 ≤ X) (hL : L ≤ 832 * X ^ 5) :
    RmS MsEnc.Rm n + MfDrv.negT 3200000 C₀ n + (spWs n + fxWB n L) ≤ 10 ^ 41 * X ^ 32 := by
  have hX : 1 ≤ X := by omega
  have hn' : n ≤ X := by omega
  obtain ⟨-, -, l3, -, l5⟩ := logs_le hn
  have hB : AllB X [n, Nat.log 2 (20 * n + 1), lg n, spWs n, fxWB n L] [1, 21, 1, 327, 10 ^ 40]
      [1, 1, 1, 2, 32] :=
    .cons (by simpa using hn') (.cons l5 (.cons l3 (.cons (spWs_le' hX hn')
      (.cons (fxWB_le' hX hn' hL) .nil))))
  exact (rn_le_eval C₀ n _ _).trans
    (eval_le_of hX (AllB.get hB) _ (by decide +kernel) (by decide +kernel))

/-- The rest of `rOF9c`: `≤ 10⁶ X⁵`. -/
theorem rest_le {m Z X : ℕ} (hm : m + 1 ≤ X) (hZ : Z ≤ X) :
    100 + 100 * m + lyP 0 (2 * m) m + lgT (2 * m) m +
      (4 * (m * Z) + 20 * BKMNW.KM m Z + 2 * BKMNW.LM m Z + 2 * moOf (2 * m) (BKMNW.LM m Z) +
        3 * (m * BKMNW.KM m Z) + 3 * Z + m + 300) ≤ 10 ^ 6 * X ^ 5 := by
  have hX : 1 ≤ X := by omega
  have e : 100 + 100 * m + lyP 0 (2 * m) m + lgT (2 * m) m +
      (4 * (m * Z) + 20 * BKMNW.KM m Z + 2 * BKMNW.LM m Z + 2 * moOf (2 * m) (BKMNW.LM m Z) +
        3 * (m * BKMNW.KM m Z) + 3 * Z + m + 300) =
      eval (lv [m, Z, lg (2 * m)]) (restP (var 0) (var 1) (var 2)) := by
    unfold lgT
    rw [sq]
    rfl
  obtain ⟨-, -, -, l4, -⟩ := logs_le hm
  have hB : AllB X [m, Z, lg (2 * m)] [1, 1, 2] [1, 1, 1] :=
    .cons (by simpa using (show m ≤ X by omega)) (.cons (by simpa using hZ) (.cons l4 .nil))
  rw [e]
  exact eval_le_of hX (AllB.get hB) _ (by decide +kernel) (by decide +kernel)

/-- **The room of the frozen fix for the MSSP encoder**:
`rOF9c 3200000 C₀ MsEnc.Rm m Z ≤ 10⁴² (m + Z + 1)³³`. -/
theorem rOF9c_Rm_le (C₀ m Z : ℕ) :
    rOF9c 3200000 C₀ MsEnc.Rm m Z ≤ 10 ^ 42 * (m + Z + 1) ^ 33 := by
  have hX : 1 ≤ m + Z + 1 := by omega
  have hL0 := rtLM_le' hX (show m ≤ m + Z + 1 by omega) (show Z ≤ m + Z + 1 by omega)
  have hsum : ∑ n ∈ range (m + 1), (RmS MsEnc.Rm n + MfDrv.negT 3200000 C₀ n) +
      ∑ n ∈ range (m + 1), (spWs n + fxWB n (n * BKMNW.KM m Z)) =
      ∑ n ∈ range (m + 1), (RmS MsEnc.Rm n + MfDrv.negT 3200000 C₀ n +
        (spWs n + fxWB n (n * BKMNW.KM m Z))) := sum_add_distrib.symm
  have hs : ∑ n ∈ range (m + 1), (RmS MsEnc.Rm n + MfDrv.negT 3200000 C₀ n +
      (spWs n + fxWB n (n * BKMNW.KM m Z))) ≤
      ∑ _n ∈ range (m + 1), 10 ^ 41 * (m + Z + 1) ^ 32 :=
    sum_le_sum fun n hn => by
      have hn' := mem_range.1 hn
      have hLn : n * BKMNW.KM m Z ≤ 832 * (m + Z + 1) ^ 5 :=
        (Nat.mul_le_mul_right _ (by omega)).trans hL0
      exact rn_le C₀ (by omega) hLn
  rw [sum_const, card_range, smul_eq_mul] at hs
  have hr := rest_le (m := m) (Z := Z) (X := m + Z + 1) (by omega) (by omega)
  have e1 : (m + Z + 1) ^ 5 ≤ (m + Z + 1) ^ 33 := Nat.pow_le_pow_right hX (by omega)
  have e2 : (m + 1) * (10 ^ 41 * (m + Z + 1) ^ 32) ≤ 10 ^ 41 * (m + Z + 1) ^ 33 := by
    calc (m + 1) * (10 ^ 41 * (m + Z + 1) ^ 32) ≤ (m + Z + 1) * (10 ^ 41 * (m + Z + 1) ^ 32) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 41 * (m + Z + 1) ^ 33 :=
        (fun (X : ℕ) => (by ring : X * (10 ^ 41 * X ^ 32) = 10 ^ 41 * X ^ 33)) _
  unfold rOF9c valM9c
  generalize (m + Z + 1) ^ 5 = A at hr e1
  generalize (m + Z + 1) ^ 33 = Y at e1 e2 ⊢
  have f1 : 10 ^ 6 * A ≤ 10 ^ 6 * Y := Nat.mul_le_mul_left _ e1
  have f2 : 10 ^ 41 * Y + 10 ^ 6 * Y ≤ 10 ^ 42 * Y := by
    have : 10 ^ 41 * Y + 10 ^ 6 * Y = (10 ^ 41 + 10 ^ 6) * Y := by ring
    rw [this]; exact Nat.mul_le_mul_right _ (by norm_num)
  omega

end P9

end BKMNW

end PlanarFlow
