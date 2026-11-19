module

public import PlanarFlow.BKMNW.PpPrB

/-!
# The base of the preprocessing above a zero area

The in-place subroutine calls of the node step need the memory `≤ Wz` zero (`MemZ Wz`), with
`Wz` at least a bound `WZ N Z` of the subroutines (a polynomial in the number of darts `N` and the
capacity bound `Z`). The preprocessing is therefore run at a base `B` computed from the input:

* `zb d = ∑_{i < n} cp i` (all capacities: a bound of `Z = bigN`);
* **`zB a p d = a · (7 n + zb d + 1) ^ p + 1`** (`n = nd d`), for constants `a`, `p` of the program.

`zP a p` reads `n`, sums the capacities from the input (`sumL (vbW 7)`), raises
`7 n + zb + 1` to the power `p` by `p` multiplications (`zPow p`) and leaves `zB a p d` in
`r8730` (the base register of the preprocessing). **`zP_exec`**: `≤ 9 n + p + 20` steps, the
memory and the output unchanged. Registers used: `8704`, `8738`, `8740`, `8741`, the scratch of the
value blocks (`8744–8779`), `8790`, `8801`, `8802`, `8730`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Feas

variable {P : Input} {W : ℕ}

/-- The sum of all capacities of the input (a bound of `bigN`). -/
def zb (d : List ℕ) : ℕ := ∑ j ∈ range (nd d), cp d j

/-- **The base of the preprocessing**: `a · (7 n + zb d + 1) ^ p + 1`. -/
def zB (a p : ℕ) (d : List ℕ) : ℕ := a * (7 * nd d + zb d + 1) ^ p + 1

/-- `n` into `r8741`, the constant `1` into `r8704`. -/
def zPre : Stmt := block [.constN 8778 2, .readIn 8741 8778, .constN 8704 1]

/-- The base of the power: `r8790 = 7 n + r8738 + 1`. -/
def zBase : Stmt := block [.constN 8778 7, .mulN 8790 8741 8778, .addN 8790 8790 8738,
  .addN 8790 8790 8704]

/-- `r8801 = r8790 ^ k` by `k` multiplications. -/
def zPow : ℕ → Stmt
  | 0 => block [.constN 8801 1]
  | k + 1 => .seq (zPow k) (block [.mulN 8801 8801 8790])

/-- `r8730 = a · r8801 + 1`. -/
def zEnd (a : ℕ) : Stmt := block [.constN 8778 a, .mulN 8802 8801 8778, .addN 8730 8802 8704]

/-- **The base program**: `r8730 = zB a p d`. -/
def zP (a p : ℕ) : Stmt := .seq zPre (.seq (sumL (vbW 7)) (.seq zBase (.seq (zPow p) (zEnd a))))

theorem zPow_exec (c : Config) (hc : WordsBounded W c) {b : ℕ} (hb : c.nreg 8790 = b)
    (hb1 : 1 ≤ b) : ∀ k, b ^ k ≤ W →
    ∃ c' t, Exec P W (zPow k) c c' t ∧ t = k + 1 ∧ c'.nreg 8801 = b ^ k ∧
      (∀ x, x ≠ 8801 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output
  | 0, h0 => by
    have h1 : 1 ≤ W := by simpa using h0
    unfold zPow
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp
    · config_simp; simp (disch := omega) only [upd_other]
  | k + 1, hk => by
    have hk' : b ^ k ≤ W := (Nat.pow_le_pow_right hb1 (Nat.le_succ k)).trans hk
    obtain ⟨c₁, t₁, e₁, ht₁, v1, f1, m1, rr1, rm1, o1⟩ := zPow_exec c hc hb hb1 k hk'
    have hb' : c₁.nreg 8790 = b := by rw [f1 _ (by omega)]; exact hb
    have hw₁ := e₁.wb_right
    obtain ⟨c₂, t₂, e₂, ht₂, v2, f2, m2, rr2, rm2, o2⟩ : ∃ c₂ t₂,
        Exec P W (block [.mulN 8801 8801 8790]) c₁ c₂ t₂ ∧ t₂ = 1 ∧ c₂.nreg 8801 = b ^ (k + 1) ∧
        (∀ x, x ≠ 8801 → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧
        c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
      exec_block
      all_goals try omega
      · config_simp; rw [v1, hb', ← pow_succ]; exact hk
      refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [v1, hb', ← pow_succ]
      · config_simp; simp (disch := omega) only [upd_other]
    refine ⟨c₂, t₁ + t₂, by unfold zPow; exact .seq e₁ e₂, by omega, v2,
      fun x hx => by rw [f2 x hx, f1 x hx], by rw [m2, m1], by rw [rr2, rr1], by rw [rm2, rm1],
      by rw [o2, o1]⟩

set_option maxHeartbeats 1000000 in
/-- **The base program** leaves `zB a p d` in `r8730` within `9 n + p + 20` steps. -/
theorem zP_exec {d : List ℕ} (hP : P.data = d) (hwd : ∀ i, word d i ≤ W) (a p : ℕ)
    (c : Config) (hc : WordsBounded W c) (hW1 : 7 * nd d + zb d + 20 ≤ W)
    (hW2 : 5 * nd d + 20 ≤ W) (hW3 : zB a p d ≤ W)
    (hW4 : (7 * nd d + zb d + 1) ^ p ≤ W) :
    ∃ c' t, Exec P W (zP a p) c c' t ∧ t ≤ 9 * nd d + p + 20 ∧ c'.nreg 8730 = zB a p d ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have e2 : d.getD 2 0 = nd d := rfl
  obtain ⟨c₁, t₁, e₁, ht₁, v41, v04, m1, rr1, rm1, o1⟩ : ∃ c₁ t₁,
      Exec P W zPre c c₁ t₁ ∧ t₁ = 3 ∧ c₁.nreg 8741 = nd d ∧ c₁.nreg 8704 = 1 ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold zPre
    exec_block
    all_goals try omega
    all_goals try (config_simp; rw [hP]; exact hwd 2)
    refine ⟨rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    rw [hP, e2]
  have hsum : ∑ j ∈ range (nd d), word d (j * 5 + 7) = zb d := by
    unfold zb
    refine sum_congr rfl fun j _ => ?_
    unfold cp
    congr 1
  obtain ⟨c₂, t₂, e₂, ht₂, v38, m2, f2, rr2, rm2, o2⟩ := sumL_exec (P := P) c₁ e₁.wb_right
    (vb := vbW 7) (m := nd d) (B := 5) (fun j => word d (j * 5 + 7)) v41 v04
    (by rw [hsum]; omega) (by omega)
    (fun i hi c' hc' hx _ _ => vbW_exec hP c' hc' hx (by omega) (hwd _))
  rw [hsum] at v38
  have k2 : ∀ x, ¬ pscr x → x ≠ 8738 → x ≠ 8740 → c₂.nreg x = c₁.nreg x := f2
  obtain ⟨c₃, t₃, e₃, ht₃, v90, f3, m3, rr3, rm3, o3⟩ : ∃ c₃ t₃,
      Exec P W zBase c₂ c₃ t₃ ∧ t₃ = 4 ∧ c₃.nreg 8790 = 7 * nd d + zb d + 1 ∧
      (∀ x, x ≠ 8790 → x ≠ 8778 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have h41 : c₂.nreg 8741 = nd d := by rw [k2 _ (by unfold pscr; omega) (by omega) (by omega)]; exact v41
    have h04 : c₂.nreg 8704 = 1 := by rw [k2 _ (by unfold pscr; omega) (by omega) (by omega)]; exact v04
    have hw₂ := e₂.wb_right
    unfold zBase
    exec_block
    all_goals try omega
    all_goals try (config_simp; rw [h41]; omega)
    all_goals try (config_simp; rw [h41, v38]; omega)
    all_goals try (config_simp; rw [h41, v38, h04]; omega)
    refine ⟨rfl, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [h41, v38, h04]; ring
    · config_simp; simp (disch := omega) only [upd_other]
  have hpow : (7 * nd d + zb d + 1) ^ p ≤ W := by
    have h1 : (7 * nd d + zb d + 1) ^ p ≤ a * (7 * nd d + zb d + 1) ^ p ∨ a = 0 := by
      rcases Nat.eq_zero_or_pos a with h | h
      · exact Or.inr h
      · exact Or.inl (Nat.le_mul_of_pos_left _ h)
    rcases h1 with h1 | h1
    · unfold zB at hW3; omega
    · exact hW4
  obtain ⟨c₄, t₄, e₄, ht₄, v01, f4, m4, rr4, rm4, o4⟩ := zPow_exec (P := P) c₃ e₃.wb_right v90
    (by omega) p hpow
  obtain ⟨c₅, t₅, e₅, ht₅, v30, m5, rr5, rm5, o5⟩ : ∃ c₅ t₅,
      Exec P W (zEnd a) c₄ c₅ t₅ ∧ t₅ = 3 ∧ c₅.nreg 8730 = zB a p d ∧ c₅.nmem = c₄.nmem ∧
      c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    have h04 : c₄.nreg 8704 = 1 := by
      rw [f4 _ (by omega), f3 _ (by omega) (by omega),
        k2 _ (by unfold pscr; omega) (by omega) (by omega)]; exact v04
    have hw₄ := e₄.wb_right
    have hm : (7 * nd d + zb d + 1) ^ p * a ≤ W := by unfold zB at hW3; rw [Nat.mul_comm]; omega
    have ha : a ≤ W := by
      have : 1 ≤ (7 * nd d + zb d + 1) ^ p := Nat.one_le_pow _ _ (by omega)
      have := Nat.le_mul_of_pos_left a this
      unfold zB at hW3; rw [Nat.mul_comm] at this; omega
    unfold zEnd
    exec_block
    all_goals try omega
    all_goals try (config_simp; omega)
    all_goals try (config_simp; rw [v01]; exact hm)
    all_goals try (config_simp; rw [v01, h04]; unfold zB at hW3; rw [Nat.mul_comm]; omega)
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
    config_simp; rw [v01, h04]; unfold zB; ring
  refine ⟨c₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))), by unfold zP; exact .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))),
    by omega, v30, by rw [m5, m4, m3, m2, m1], by rw [rr5, rr4, rr3, rr2, rr1],
    by rw [rm5, rm4, rm3, rm2, rm1], by rw [o5, o4, o3, o2, o1]⟩

end Pp

end BKMNW

end PlanarFlow
