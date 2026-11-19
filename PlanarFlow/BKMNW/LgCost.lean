module

public import PlanarFlow.BKMNW.LgNf

/-!
# The cost of stages 5 and 6 of the large-piece separator in `O(n lg n + k)`

* `s5Wv_le`: with at most `6` touched holes, `W₀ = #P + K nTouch ≤ 223 #P + 84`;
* `lg2_two_mul_le` (`log₂ (2 x) ≤ log₂ n + 10` for `x ≤ 223 n + 84`, `1 ≤ n`);
* **`s5T_le`**: the bound of `lgS5_exec`,
  `9700 n + 70 k + 5 log₂ (2 W₀) + mbT n' (encB' W₀) W₀ + 3800 ≤ 10⁶ n lg n + 70 k`
  (`1 ≤ n`, `n' ≤ n`, `W₀ ≤ 223 n + 84`);
* **`s56T_le`**: with stage 6 (`70 n + 7 k + 40`): `≤ 1000200 n lg n + 77 k`.

(`lg n = log₂ n + 1`, `Cost.lean`.) This is the stage-5/6 part of the bound
`sTL n k ≤ c n lg n + c k` required of `sepL`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- `W₀ = #P + K nTouch ≤ 223 #P + 84` when at most `6` holes are touched. -/
lemma s5Wv_le {P : Finset D} {Hs : List (Finset V)} {bb : Bool} (hnt : nTouch M P Hs ≤ 6) :
    s5Wv M P Hs bb ≤ 223 * P.card + 84 := by
  have hs : Nat.sqrt (2 * P.card) ≤ 2 * P.card := Nat.sqrt_le_self _
  have hK : s5Kv M P Hs bb ≤ 37 * P.card + 14 := by
    unfold s5Kv kH lS
    split_ifs <;> omega
  unfold s5Wv
  have : s5Kv M P Hs bb * nTouch M P Hs ≤ (37 * P.card + 14) * 6 := Nat.mul_le_mul hK hnt
  omega

/-- `log₂ (2 x) ≤ log₂ n + 10` for `x ≤ 223 n + 84`, `1 ≤ n`. -/
lemma lg2_two_mul_le {n x : ℕ} (hn : 1 ≤ n) (hx : x ≤ 223 * n + 84) :
    Nat.log 2 (2 * x) ≤ Nat.log 2 n + 10 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx0
  · simp
  have h1 : n < 2 ^ (Nat.log 2 n).succ := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2 : 2 * x < 2 ^ (Nat.log 2 n + 11) := by
    have e : 2 ^ (Nat.log 2 n + 11) = 2 ^ (Nat.log 2 n).succ * 1024 := by
      rw [show Nat.log 2 n + 11 = (Nat.log 2 n).succ + 10 by omega, pow_add]; norm_num
    rw [e]
    have : 1024 * n < 1024 * 2 ^ (Nat.log 2 n).succ := by omega
    omega
  have := Nat.log_lt_of_lt_pow (by omega) h2
  omega

/-- `log₂ (2 n') ≤ log₂ n + 1` for `n' ≤ n`. -/
lemma lg2_two_mul_le' {n n' : ℕ} (h : n' ≤ n) : Nat.log 2 (2 * n') ≤ Nat.log 2 n + 1 := by
  rcases Nat.eq_zero_or_pos n' with rfl | hn'
  · simp
  have h1 : n < 2 ^ (Nat.log 2 n).succ := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2 : 2 * n' < 2 ^ (Nat.log 2 n + 2) := by
    rw [pow_succ]
    have : 2 ^ (Nat.log 2 n + 1) = 2 ^ (Nat.log 2 n).succ := rfl
    omega
  have := Nat.log_lt_of_lt_pow (by omega) h2
  omega

/-- **The bound of stage 5 in `O(n lg n + k)`.** -/
theorem s5T_le {n n' k W₀ : ℕ} (hn : 1 ≤ n) (hn' : n' ≤ n) (hW : W₀ ≤ 223 * n + 84) :
    9700 * n + 70 * k + 5 * Nat.log 2 (2 * W₀) + mbT n' (encB' W₀) W₀ + 3800 ≤
      1000000 * n * lg n + 70 * k := by
  have ha := lg2_two_mul_le hn hW
  have hb := lg2_two_mul_le' (n := n) (n' := n') hn'
  have hL : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  generalize hLd : Nat.log 2 n = L at ha hb hL
  generalize hAd : Nat.log 2 (2 * W₀) = a at ha
  have e1 : encB' W₀ = 102 * W₀ + 7 + (a + 2) * (2 * W₀) := by rw [encB'_eq, hAd]
  have p1 : (a + 2) * (2 * W₀) ≤ (L + 12) * (446 * n + 168) :=
    Nat.mul_le_mul (by omega) (by omega)
  have p2 : (231 * n' + 60 * (2 * n') + 156) * Nat.log 2 (2 * n') ≤ (351 * n + 156) * (L + 1) :=
    Nat.mul_le_mul (by omega) hb
  have q1 : (L + 12) * (446 * n + 168) = 446 * (n * L) + 168 * L + 5352 * n + 2016 := by ring
  have q2 : (351 * n + 156) * (L + 1) = 351 * (n * L) + 156 * L + 351 * n + 156 := by ring
  have q3 : 1000000 * n * lg n = 1000000 * (n * L) + 1000000 * n := by
    unfold lg; rw [hLd]; ring
  unfold mbT msT encT
  rw [e1, q3]
  rw [q1] at p1
  rw [q2] at p2
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
  omega

/-- **The bound of stages 5 and 6 in `O(n lg n + k)`.** -/
theorem s56T_le {n n' k W₀ : ℕ} (hn : 1 ≤ n) (hn' : n' ≤ n) (hW : W₀ ≤ 223 * n + 84) :
    9700 * n + 70 * k + 5 * Nat.log 2 (2 * W₀) + mbT n' (encB' W₀) W₀ + 3800 +
      (70 * n + 7 * k + 40) ≤ 1000200 * n * lg n + 77 * k := by
  have h := s5T_le (k := k) hn hn' hW
  have : n ≤ n * lg n := Nat.le_mul_of_pos_right n (by unfold lg; omega)
  have e : 1000200 * n * lg n = 1000200 * (n * lg n) := by ring
  have e' : 1000000 * n * lg n = 1000000 * (n * lg n) := by ring
  rw [e'] at h
  omega

end MfDrv

end BKMNW

end PlanarFlow
