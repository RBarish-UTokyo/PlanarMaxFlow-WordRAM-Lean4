module

public import PlanarFlow.BKMNW.ScFrame

/-!
# The base `Bz = encB' x` of Miller's program on the machine (a doubling loop for `Nat.log`)

`mfMain_cMachXGE` uses Miller's separator `sepC M e n (encB' W)` at the base `encB' W` of the
weight bound `W = #P + K nTouch` of the call; `encB' x = 102 x + 7 + (log₂ (2x) + 2) · 2x`
(`aEnd10 x (2x)`) has a `Nat.log`, so the separator program computes it: **`ebProg`** (registers:
input `5850 = x`, output `5858 = encB' x`, written `5851 … 5859`), a doubling loop
`p := 1; L := 0; while 2p ≤ 2x: p := 2p, L := L + 1` then the arithmetic.

* `encB'_eq` (the closed form), `ebInv`, **`ebProg_exec`**: within `5 log₂ (2x) + 22` steps
  `r5858 = encB' x`; registers outside `5851 … 5859`, memory, reals, output kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs PlanarSeparator.MillerProg

lemma encB'_eq (x : ℕ) : encB' x = 102 * x + 7 + (Nat.log 2 (2 * x) + 2) * (2 * x) := by
  simp only [encB', aEnd10, aEnd]; ring

/-- The start of the loop. -/
def eb0 : Stmt := block [.constN 5851 1, .constN 5852 0, .addN 5853 5850 5850, .constN 5859 1,
  .addN 5855 5853 5859, .addN 5856 5851 5851]

/-- One doubling. -/
def ebBody : Stmt := block [.copyN 5851 5856, .addN 5852 5852 5859, .addN 5856 5851 5851]

/-- The arithmetic of `encB'`. -/
def eb2 : Stmt := block [.constN 5854 2, .addN 5857 5852 5854, .mulN 5858 5857 5853,
  .constN 5854 102, .mulN 5854 5854 5850, .addN 5858 5858 5854, .constN 5854 7,
  .addN 5858 5858 5854]

/-- **The base of Miller's program**, `r5858 := encB' r5850`. -/
def ebProg : Stmt := .seq eb0 (.seq (.whileLtN 5856 5855 ebBody) eb2)

section Exec

variable {P : Input} {W : ℕ}

/-- The invariant of the doubling loop. -/
def ebInv (c₀ : Config) (W x : ℕ) (c : Config) : Prop :=
  WordsBounded W c ∧ ∃ L, c.nreg 5851 = 2 ^ L ∧ c.nreg 5852 = L ∧ c.nreg 5856 = 2 * 2 ^ L ∧
    c.nreg 5853 = 2 * x ∧ c.nreg 5855 = 2 * x + 1 ∧ c.nreg 5859 = 1 ∧
    (2 ^ L ≤ 2 * x ∨ L = 0) ∧
    (∀ r, (r < 5851 ∨ 5859 < r) → c.nreg r = c₀.nreg r) ∧ c.nmem = c₀.nmem ∧
    c.rreg = c₀.rreg ∧ c.rmem = c₀.rmem ∧ c.output = c₀.output

theorem ebBody_exec (c : Config) (hc : WordsBounded W c) {L : ℕ} (r1 : c.nreg 5856 = 2 * 2 ^ L)
    (r2 : c.nreg 5852 = L) (r9 : c.nreg 5859 = 1) (w : 4 * 2 ^ L ≤ W) (wL : L + 1 ≤ W) :
    ∃ c' t, Exec P W ebBody c c' t ∧ t = 3 ∧ c'.nreg 5851 = 2 ^ (L + 1) ∧
      c'.nreg 5852 = L + 1 ∧ c'.nreg 5856 = 2 * 2 ^ (L + 1) ∧
      (∀ r, r ≠ 5851 → r ≠ 5852 → r ≠ 5856 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hp : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
  unfold ebBody
  exec_block
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r1, r2, r9]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r1, r2, r9])
    try omega

theorem eb0_exec (c : Config) (hc : WordsBounded W c) {x : ℕ} (r0 : c.nreg 5850 = x)
    (w : 2 * x + 2 ≤ W) :
    ∃ c' t, Exec P W eb0 c c' t ∧ t = 6 ∧ c'.nreg 5851 = 1 ∧ c'.nreg 5852 = 0 ∧
      c'.nreg 5856 = 2 ∧ c'.nreg 5853 = 2 * x ∧ c'.nreg 5855 = 2 * x + 1 ∧ c'.nreg 5859 = 1 ∧
      (∀ r, (r < 5851 ∨ 5859 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold eb0
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r0]; omega)
  all_goals try (simp only [Config.nreg_mk, upd_apply]; simp only [r0]; omega)
  all_goals try (simp only [Config.nreg_mk, upd_apply]; norm_num; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r0])
    try omega

theorem eb2_exec (c : Config) (hc : WordsBounded W c) {x L : ℕ} (r0 : c.nreg 5850 = x)
    (r2 : c.nreg 5852 = L) (r3 : c.nreg 5853 = 2 * x)
    (w : 102 * x + 7 + (L + 2) * (2 * x) ≤ W) (w1 : 102 ≤ W) (w2 : L + 2 ≤ W) :
    ∃ c' t, Exec P W eb2 c c' t ∧ t = 8 ∧ c'.nreg 5858 = 102 * x + 7 + (L + 2) * (2 * x) ∧
      (∀ r, (r < 5851 ∨ 5859 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h1 : (L + 2) * (2 * x) ≤ W := by omega
  have h2 : 102 * x ≤ W := by omega
  unfold eb2
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r0, r2, r3]; omega)
  all_goals try (simp only [Config.nreg_mk, upd_apply]; simp only [r0, r2, r3]; omega)
  all_goals try (simp only [Config.nreg_mk, upd_apply]; norm_num; simp only [r0, r2, r3]; omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r0, r2, r3]; nlinarith)
  refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r0, r2, r3])
    try omega

/-- **The base of Miller's program on the machine**: within `5 log₂ (2x) + 22` steps
`r5858 = encB' x`. -/
theorem ebProg_exec (c : Config) (hc : WordsBounded W c) {x : ℕ} (r0 : c.nreg 5850 = x)
    (w : 4 * x + 4 ≤ W) (wB : encB' x ≤ W) (w1 : 102 ≤ W) :
    ∃ c' t, Exec P W ebProg c c' t ∧ t ≤ 5 * Nat.log 2 (2 * x) + 22 ∧
      c'.nreg 5858 = encB' x ∧ (∀ r, (r < 5851 ∨ 5859 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a1, a2, a6, a3, a5, a9, ar, am, arr, arm, ao⟩ :=
    eb0_exec (P := P) c hc r0 (by omega)
  have hI₁ : ebInv c W x c₁ := ⟨e₁.wb_right, 0, by rw [a1]; rfl, a2, by rw [a6]; rfl, a3, a5, a9,
    Or.inr rfl, ar, am, arr, arm, ao⟩
  set lg := Nat.log 2 (2 * x) with hlg
  have hpow : ∀ L, 2 ^ L ≤ 2 * x → L ≤ lg := fun L h => by
    have hx : 2 * x ≠ 0 := by have := Nat.one_le_two_pow (n := L); omega
    exact Nat.le_log_of_pow_le (by norm_num) h
  obtain ⟨c₂, t₂, e₂, hI₂, hex, ht₂⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 5856)
    (b := 5855) (body := ebBody) (ebInv c W x) (fun c' => 5 * (lg + 1 - c'.nreg 5852))
    (fun c' h => h.1) (fun c' hI hlt => by
      obtain ⟨hw, L, p1, p2, p6, p3, p5, p9, hle, hr, hm, hrr, hrm, ho⟩ := hI
      rw [p6, p5] at hlt
      have hL1 : 2 ^ (L + 1) ≤ 2 * x := by rw [pow_succ]; omega
      have hLl := hpow _ hL1
      obtain ⟨c', t, e, ht, q1, q2, q6, qr, qm, qrr, qrm, qo⟩ := ebBody_exec (P := P) c' hw p6 p2 p9
        (by rw [pow_succ] at hL1; omega) (by have := Nat.lt_two_pow_self (n := L); omega)
      refine ⟨c', t, e, ⟨e.wb_right, L + 1, q1, q2, q6, by rw [qr _ (by omega) (by omega)
        (by omega), p3], by rw [qr _ (by omega) (by omega) (by omega), p5],
        by rw [qr _ (by omega) (by omega) (by omega), p9], Or.inl hL1, fun r h => by
          rw [qr r (by omega) (by omega) (by omega), hr r h], by rw [qm, hm], by rw [qrr, hrr],
        by rw [qrm, hrm], by rw [qo, ho]⟩, ?_⟩
      rw [q2, p2]; omega) hI₁
  obtain ⟨hw₂, L, p1, p2, p6, p3, p5, p9, hle, hr, hm, hrr, hrm, ho⟩ := hI₂
  rw [p6, p5] at hex
  -- the loop computed the logarithm
  have hL : L = lg := by
    rcases hle with h | h
    · have h2 : 2 * x < 2 ^ (L + 1) := by rw [pow_succ]; omega
      have hx : 2 * x ≠ 0 := by have := Nat.one_le_two_pow (n := L); omega
      exact (Nat.log_eq_of_pow_le_of_lt_pow h h2).symm
    · subst h
      have : 2 * x < 2 := by simp at hex; omega
      rw [hlg, show 2 * x = 0 by omega]; simp
  subst hL
  obtain ⟨c₃, t₃, e₃, ht₃, h58, q3, m3, rr3, rm3, o3⟩ := eb2_exec (P := P) c₂ hw₂ (x := x)
    (by rw [hr _ (by omega), r0]) p2 p3 (by rw [encB'_eq] at wB; exact wB) w1
    (by have := Nat.log_le_self 2 (2 * x); omega)
  have hΦ : 5 * (Nat.log 2 (2 * x) + 1 - c₁.nreg 5852) ≤ 5 * Nat.log 2 (2 * x) + 5 := by
    rw [a2]; omega
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, by rw [h58, encB'_eq],
    fun r h => by rw [q3 r h, hr r h], by rw [m3, hm], by rw [rr3, hrr], by rw [rm3, hrm],
    by rw [o3, ho]⟩

end Exec

end BKMNW

end PlanarFlow
