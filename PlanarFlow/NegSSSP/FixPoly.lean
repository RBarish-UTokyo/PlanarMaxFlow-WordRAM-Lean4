module

public import WordRAM

/-!
# Polynomial expressions evaluated by a fixed straight-line program

A small language `PE` of polynomial expressions with natural coefficients (constants, variables
`var i`, sums, products), its value `PE.eval ρ e` (`ρ i` the value of the variable `i`), and a
**compiler** `PE.comp VB e r` to a fixed straight-line program: the variable `i` is read from the
register `VB + i`, the value is left in `r`, and only the registers `≥ r` are written (the
registers `r + 1, r + 2, …` as a stack of intermediate values).

**`PE.comp_exec`**: if every variable index of `e` is `< nv` (`PE.VarsLt nv e`) and
`VB + nv ≤ r`, the program runs in exactly `PE.cost e` steps, leaves `PE.eval ρ e` in `r`
(`ρ i = c.nreg (VB + i)`), keeps every register `< r`, the memories, the reals and the output,
under the word bound `PE.evalU ρ e ≤ W`, where `PE.evalU` is the value of the same expression
with every constant and every variable increased by one (every intermediate value is at most
`evalU`; `evalU` is again a polynomial with natural coefficients in the variables).
-/

@[expose] public section

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-- **Polynomial expressions** with natural coefficients. -/
inductive PE where
  | cst (k : ℕ)
  | var (i : ℕ)
  | add (a b : PE)
  | mul (a b : PE)

namespace PE

/-- The value of an expression (`ρ i`: the value of the variable `i`). -/
def eval (ρ : ℕ → ℕ) : PE → ℕ
  | cst k => k
  | var i => ρ i
  | add a b => eval ρ a + eval ρ b
  | mul a b => eval ρ a * eval ρ b

/-- The value with every constant and every variable increased by one (the word bound). -/
def evalU (ρ : ℕ → ℕ) : PE → ℕ
  | cst k => k + 1
  | var i => ρ i + 1
  | add a b => evalU ρ a + evalU ρ b
  | mul a b => evalU ρ a * evalU ρ b

/-- Every variable index is `< n`. -/
def VarsLt (n : ℕ) : PE → Prop
  | cst _ => True
  | var i => i < n
  | add a b => VarsLt n a ∧ VarsLt n b
  | mul a b => VarsLt n a ∧ VarsLt n b

/-- Every variable index is `< n` (decidable form). -/
def vl (n : ℕ) : PE → Bool
  | cst _ => true
  | var i => decide (i < n)
  | add a b => vl n a && vl n b
  | mul a b => vl n a && vl n b

theorem varsLt_of_vl {n : ℕ} : ∀ {e : PE}, vl n e = true → VarsLt n e
  | cst _, _ => trivial
  | var _, h => by simpa [vl, VarsLt] using h
  | add _ _, h => by
      simp only [vl, Bool.and_eq_true] at h; exact ⟨varsLt_of_vl h.1, varsLt_of_vl h.2⟩
  | mul _ _, h => by
      simp only [vl, Bool.and_eq_true] at h; exact ⟨varsLt_of_vl h.1, varsLt_of_vl h.2⟩

instance (k : ℕ) : OfNat PE k := ⟨cst k⟩
instance : Add PE := ⟨add⟩
instance : Mul PE := ⟨mul⟩

/-- The number of instructions of the compiled program. -/
def cost : PE → ℕ
  | cst _ => 1
  | var _ => 1
  | add a b => cost a + cost b + 1
  | mul a b => cost a + cost b + 1

/-- **The compiled program**: the value of `e` into `r`, the variable `i` read from `VB + i`,
the intermediate values in `r + 1, r + 2, …`. -/
def comp (VB : ℕ) : PE → ℕ → Stmt
  | cst k, r => .instr (.constN r k)
  | var i, r => .instr (.copyN r (VB + i))
  | add a b, r => .seq (comp VB a r) (.seq (comp VB b (r + 1)) (.instr (.addN r r (r + 1))))
  | mul a b, r => .seq (comp VB a r) (.seq (comp VB b (r + 1)) (.instr (.mulN r r (r + 1))))

theorem one_le_evalU (ρ : ℕ → ℕ) : ∀ e : PE, 1 ≤ evalU ρ e
  | cst _ => by simp [evalU]
  | var _ => by simp [evalU]
  | add a b => by have := one_le_evalU ρ a; simp only [evalU]; omega
  | mul a b => by
      have h1 := one_le_evalU ρ a; have h2 := one_le_evalU ρ b
      simp only [evalU]; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))

theorem eval_le_evalU (ρ : ℕ → ℕ) : ∀ e : PE, eval ρ e ≤ evalU ρ e
  | cst _ => by simp [eval, evalU]
  | var _ => by simp [eval, evalU]
  | add a b => by
      have := eval_le_evalU ρ a; have := eval_le_evalU ρ b; simp only [eval, evalU]; omega
  | mul a b => by
      simp only [eval, evalU]; exact Nat.mul_le_mul (eval_le_evalU ρ a) (eval_le_evalU ρ b)

theorem evalU_add_left (ρ : ℕ → ℕ) (a b : PE) : evalU ρ a ≤ evalU ρ (add a b) := by
  simp only [evalU]; omega

theorem evalU_add_right (ρ : ℕ → ℕ) (a b : PE) : evalU ρ b ≤ evalU ρ (add a b) := by
  simp only [evalU]; omega

theorem evalU_mul_left (ρ : ℕ → ℕ) (a b : PE) : evalU ρ a ≤ evalU ρ (mul a b) := by
  simp only [evalU]; exact Nat.le_mul_of_pos_right _ (one_le_evalU ρ b)

theorem evalU_mul_right (ρ : ℕ → ℕ) (a b : PE) : evalU ρ b ≤ evalU ρ (mul a b) := by
  simp only [evalU]; exact Nat.le_mul_of_pos_left _ (one_le_evalU ρ a)

theorem eval_congr {ρ ρ' : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, ρ' i = ρ i) :
    ∀ {e : PE}, VarsLt n e → eval ρ' e = eval ρ e ∧ evalU ρ' e = evalU ρ e
  | cst _, _ => ⟨rfl, rfl⟩
  | var i, hv => by simp only [eval, evalU, h i hv, and_self]
  | add a b, hv => by
      obtain ⟨h1, h2⟩ := eval_congr h hv.1; obtain ⟨h3, h4⟩ := eval_congr h hv.2
      simp only [eval, evalU, h1, h2, h3, h4, and_self]
  | mul a b, hv => by
      obtain ⟨h1, h2⟩ := eval_congr h hv.1; obtain ⟨h3, h4⟩ := eval_congr h hv.2
      simp only [eval, evalU, h1, h2, h3, h4, and_self]

variable {P : Input} {W : ℕ}

/-- **The compiled program computes the value** (see the module docstring). -/
theorem comp_exec (VB nv : ℕ) :
    ∀ (e : PE) (r : ℕ), VarsLt nv e → VB + nv ≤ r → ∀ (c : Config), WordsBounded W c →
      evalU (fun i => c.nreg (VB + i)) e ≤ W →
      ∃ c', Exec P W (comp VB e r) c c' (cost e) ∧
        c'.nreg r = eval (fun i => c.nreg (VB + i)) e ∧ (∀ x < r, c'.nreg x = c.nreg x) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  | .cst k, r, _, _, c, hc, hW => by
      refine ⟨_, Exec.constN (P := P) hc r k (by simp only [evalU] at hW; omega), ?_, fun x hx => ?_,
        rfl, rfl, rfl, rfl⟩
      · simp [upd, eval]
      · simp only [upd_apply]; split_ifs <;> omega
  | .var i, r, hv, hr, c, hc, _ => by
      refine ⟨_, Exec.copyN (P := P) hc r (VB + i), ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
      · simp [upd, eval]
      · simp only [upd_apply]; split_ifs <;> omega
  | .add a b, r, hv, hr, c, hc, hW => by
      have hWa := (evalU_add_left _ a b).trans hW
      have hWb := (evalU_add_right _ a b).trans hW
      obtain ⟨c₁, e₁, g1, k1, m1, rr1, rm1, o1⟩ := comp_exec VB nv a r hv.1 hr c hc hWa
      have hρ : ∀ i < nv, c₁.nreg (VB + i) = c.nreg (VB + i) := fun i hi => k1 _ (by omega)
      have hWb' : evalU (fun i => c₁.nreg (VB + i)) b ≤ W := by
        rw [(eval_congr hρ hv.2).2]; exact hWb
      obtain ⟨c₂, e₂, g2, k2, m2, rr2, rm2, o2⟩ :=
        comp_exec VB nv b (r + 1) hv.2 (by omega) c₁ e₁.wb_right hWb'
      have hv1 : c₂.nreg r = eval (fun i => c.nreg (VB + i)) a := by rw [k2 r (by omega), g1]
      have hv2 : c₂.nreg (r + 1) = eval (fun i => c.nreg (VB + i)) b := by
        rw [g2, (eval_congr hρ hv.2).1]
      have hsum : c₂.nreg r + c₂.nreg (r + 1) ≤ W := by
        rw [hv1, hv2]
        have := eval_le_evalU (fun i => c.nreg (VB + i)) (add a b)
        simp only [eval] at this; omega
      have e₃ := Exec.addN (P := P) e₂.wb_right r r (r + 1) hsum
      refine ⟨_, (Exec.seq e₁ (Exec.seq e₂ e₃)).cast (by simp only [cost]; omega), ?_,
        fun x hx => ?_, m2.trans m1, rr2.trans rr1, rm2.trans rm1, o2.trans o1⟩
      · simp only [upd_apply, ite_true, hv1, hv2, eval]
      · simp only [upd_apply]; split_ifs
        · omega
        · rw [k2 x (by omega), k1 x hx]
  | .mul a b, r, hv, hr, c, hc, hW => by
      have hWa := (evalU_mul_left _ a b).trans hW
      have hWb := (evalU_mul_right _ a b).trans hW
      obtain ⟨c₁, e₁, g1, k1, m1, rr1, rm1, o1⟩ := comp_exec VB nv a r hv.1 hr c hc hWa
      have hρ : ∀ i < nv, c₁.nreg (VB + i) = c.nreg (VB + i) := fun i hi => k1 _ (by omega)
      have hWb' : evalU (fun i => c₁.nreg (VB + i)) b ≤ W := by
        rw [(eval_congr hρ hv.2).2]; exact hWb
      obtain ⟨c₂, e₂, g2, k2, m2, rr2, rm2, o2⟩ :=
        comp_exec VB nv b (r + 1) hv.2 (by omega) c₁ e₁.wb_right hWb'
      have hv1 : c₂.nreg r = eval (fun i => c.nreg (VB + i)) a := by rw [k2 r (by omega), g1]
      have hv2 : c₂.nreg (r + 1) = eval (fun i => c.nreg (VB + i)) b := by
        rw [g2, (eval_congr hρ hv.2).1]
      have hsum : c₂.nreg r * c₂.nreg (r + 1) ≤ W := by
        rw [hv1, hv2]
        exact (eval_le_evalU (fun i => c.nreg (VB + i)) (mul a b)).trans hW
      have e₃ := Exec.mulN (P := P) e₂.wb_right r r (r + 1) hsum
      refine ⟨_, (Exec.seq e₁ (Exec.seq e₂ e₃)).cast (by simp only [cost]; omega), ?_,
        fun x hx => ?_, m2.trans m1, rr2.trans rr1, rm2.trans rm1, o2.trans o1⟩
      · simp only [upd_apply, ite_true, hv1, hv2, eval]
      · simp only [upd_apply]; split_ifs
        · omega
        · rw [k2 x (by omega), k1 x hx]

end PE

end NegSSSP

end PlanarFlow
