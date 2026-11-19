module

public import PlanarFlow.NegSSSP.FixWN
public import PlanarFlow.BKMNW.Cost

/-!
# Polynomial bounds of expressions

For an expression `e : PE` (`NegSSSP.FixPoly`), variables bounded by `ρ i ≤ A i · X ^ p i` with
`1 ≤ X` give

  **`eval_le_pow`**: `eval ρ e ≤ eval A e · X ^ pdeg p e`,
  **`evalU_le_pow`**: `evalU ρ e ≤ evalU A e · X ^ pdeg p e`,

with `pdeg p` the degree when the variable `i` has degree `p i`. The coefficients `eval A e`,
`evalU A e` and the degree `pdeg p e` of a closed expression are numerals the kernel computes
(`decide +kernel`), which is how the explicit polynomial bounds of `Nf9aB … Nf9aD` are obtained.
`AllB X ρs As ps` packages the variable bounds of lists (`AllB.get`), `lv l i = l.getD i 0`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace NegSSSP

namespace PE

/-- **The degree of an expression**, the variable `i` having degree `p i`. -/
def pdeg (p : ℕ → ℕ) : PE → ℕ
  | cst _ => 0
  | var i => p i
  | add a b => max (pdeg p a) (pdeg p b)
  | mul a b => pdeg p a + pdeg p b

/-- **The value of an expression is at most its coefficient bound times `X ^ pdeg`.** -/
theorem eval_le_pow {ρ A p : ℕ → ℕ} {X : ℕ} (hX : 1 ≤ X) (h : ∀ i, ρ i ≤ A i * X ^ p i) :
    ∀ e : PE, eval ρ e ≤ eval A e * X ^ pdeg p e
  | cst k => by simp [eval, pdeg]
  | var i => h i
  | add a b => by
      have h1 := eval_le_pow hX h a
      have h2 := eval_le_pow hX h b
      have e1 : X ^ pdeg p a ≤ X ^ max (pdeg p a) (pdeg p b) :=
        Nat.pow_le_pow_right hX (le_max_left _ _)
      have e2 : X ^ pdeg p b ≤ X ^ max (pdeg p a) (pdeg p b) :=
        Nat.pow_le_pow_right hX (le_max_right _ _)
      show eval ρ a + eval ρ b ≤ (eval A a + eval A b) * X ^ max (pdeg p a) (pdeg p b)
      calc eval ρ a + eval ρ b ≤ eval A a * X ^ pdeg p a + eval A b * X ^ pdeg p b :=
            Nat.add_le_add h1 h2
        _ ≤ eval A a * X ^ max (pdeg p a) (pdeg p b) +
            eval A b * X ^ max (pdeg p a) (pdeg p b) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
        _ = _ := by ring
  | mul a b => by
      have h1 := eval_le_pow hX h a
      have h2 := eval_le_pow hX h b
      show eval ρ a * eval ρ b ≤ (eval A a * eval A b) * X ^ (pdeg p a + pdeg p b)
      calc eval ρ a * eval ρ b ≤ (eval A a * X ^ pdeg p a) * (eval A b * X ^ pdeg p b) :=
            Nat.mul_le_mul h1 h2
        _ = _ := by ring

/-- **The same for `evalU`** (constants and variables increased by one). -/
theorem evalU_le_pow {ρ A p : ℕ → ℕ} {X : ℕ} (hX : 1 ≤ X) (h : ∀ i, ρ i ≤ A i * X ^ p i) :
    ∀ e : PE, evalU ρ e ≤ evalU A e * X ^ pdeg p e
  | cst k => by simp [evalU, pdeg]
  | var i => by
      have h1 := h i
      have h2 : 1 ≤ X ^ p i := Nat.one_le_pow _ _ hX
      show ρ i + 1 ≤ (A i + 1) * X ^ p i
      rw [Nat.add_mul, one_mul]
      omega
  | add a b => by
      have h1 := evalU_le_pow hX h a
      have h2 := evalU_le_pow hX h b
      have e1 : X ^ pdeg p a ≤ X ^ max (pdeg p a) (pdeg p b) :=
        Nat.pow_le_pow_right hX (le_max_left _ _)
      have e2 : X ^ pdeg p b ≤ X ^ max (pdeg p a) (pdeg p b) :=
        Nat.pow_le_pow_right hX (le_max_right _ _)
      show evalU ρ a + evalU ρ b ≤ (evalU A a + evalU A b) * X ^ max (pdeg p a) (pdeg p b)
      calc evalU ρ a + evalU ρ b ≤ evalU A a * X ^ pdeg p a + evalU A b * X ^ pdeg p b :=
            Nat.add_le_add h1 h2
        _ ≤ evalU A a * X ^ max (pdeg p a) (pdeg p b) +
            evalU A b * X ^ max (pdeg p a) (pdeg p b) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
        _ = _ := by ring
  | mul a b => by
      have h1 := evalU_le_pow hX h a
      have h2 := evalU_le_pow hX h b
      show evalU ρ a * evalU ρ b ≤ (evalU A a * evalU A b) * X ^ (pdeg p a + pdeg p b)
      calc evalU ρ a * evalU ρ b ≤ (evalU A a * X ^ pdeg p a) * (evalU A b * X ^ pdeg p b) :=
            Nat.mul_le_mul h1 h2
        _ = _ := by ring

/-- **The bound with numerals**: `eval A e ≤ c` and `pdeg p e ≤ d` (checked by the kernel). -/
theorem eval_le_of {ρ A p : ℕ → ℕ} {X : ℕ} (hX : 1 ≤ X) (h : ∀ i, ρ i ≤ A i * X ^ p i)
    (e : PE) {c d : ℕ} (hc : eval A e ≤ c) (hd : pdeg p e ≤ d) : eval ρ e ≤ c * X ^ d :=
  (eval_le_pow hX h e).trans (Nat.mul_le_mul hc (Nat.pow_le_pow_right hX hd))

/-- **The bound with numerals for `evalU`.** -/
theorem evalU_le_of {ρ A p : ℕ → ℕ} {X : ℕ} (hX : 1 ≤ X) (h : ∀ i, ρ i ≤ A i * X ^ p i)
    (e : PE) {c d : ℕ} (hc : evalU A e ≤ c) (hd : pdeg p e ≤ d) : evalU ρ e ≤ c * X ^ d :=
  (evalU_le_pow hX h e).trans (Nat.mul_le_mul hc (Nat.pow_le_pow_right hX hd))

end PE

end NegSSSP

namespace BKMNW

namespace P9

/-- The entries of a list (`0` outside). -/
def lv (l : List ℕ) (i : ℕ) : ℕ := l.getD i 0

/-- **Bounds of the entries of lists**: `ρs[i] ≤ As[i] · X ^ ps[i]`. -/
def AllB (X : ℕ) : List ℕ → List ℕ → List ℕ → Prop
  | [], _, _ => True
  | _ :: _, [], _ => False
  | _ :: _, _ :: _, [] => False
  | r :: rs, a :: as, q :: qs => r ≤ a * X ^ q ∧ AllB X rs as qs

theorem AllB.get {X : ℕ} : ∀ {rs as qs : List ℕ}, AllB X rs as qs →
    ∀ i, lv rs i ≤ lv as i * X ^ lv qs i
  | [], _, _, _, i => by simp [lv]
  | _ :: _, [], _, h, _ => by simp [AllB] at h
  | _ :: _, _ :: _, [], h, _ => by simp [AllB] at h
  | r :: rs, a :: as, q :: qs, h, i => by
      simp only [AllB] at h
      cases i with
      | zero => simpa [lv] using h.1
      | succ i => simpa [lv] using AllB.get h.2 i

theorem AllB.nil {X : ℕ} {as qs : List ℕ} : AllB X [] as qs := by simp [AllB]

theorem AllB.cons {X r a q : ℕ} {rs as qs : List ℕ} (h : r ≤ a * X ^ q)
    (hs : AllB X rs as qs) : AllB X (r :: rs) (a :: as) (q :: qs) := by
  simp only [AllB]; exact ⟨h, hs⟩

/-- `Nat.log 2 n ≤ n`. -/
lemma log2_le (n : ℕ) : Nat.log 2 n ≤ n := Nat.log_le_self 2 n

/-- `lg n ≤ n + 1`. -/
lemma lg_le (n : ℕ) : lg n ≤ n + 1 := by unfold lg; have := log2_le n; omega

end P9

end BKMNW

end PlanarFlow
