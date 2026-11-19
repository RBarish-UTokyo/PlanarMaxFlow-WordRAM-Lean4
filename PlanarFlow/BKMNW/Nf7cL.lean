module

public import PlanarFlow.BKMNW.Nf7cK

/-!
# Clearing the resident image

**`clrP_exec`**: `clrP` zeroes the `sb = r7607` cells at `0` (`r9475 = 0`), `SH = r9471`,
`Wf + 1 = r7612` and `SH + Wf + 1 = r9474` (the resident FR image and its shadow), within
`20 sb + 32` steps; every other cell kept; registers outside `5030 … 5035` kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

theorem clrK_exec (c : Config) (hc : WordsBounded W c) {rb sb Zb : ℕ}
    (hrb : rb < 5030 ∨ 5035 < rb) (r07 : c.nreg 7607 = sb) (rB : c.nreg rb = Zb)
    (hW : Zb + sb + sb + 1 ≤ W) :
    ∃ c' t, Exec P W (clrK rb) c c' t ∧ t ≤ 5 * sb + 7 ∧
      (∀ i < sb, c'.nmem (Zb + i) = 0) ∧ (∀ a, (a < Zb ∨ Zb + sb ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 5030 ∨ 5035 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a30, a31, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.copyN 5030 7607, .copyN 5031 rb]) c c₁ t₁ ∧ t₁ = 2 ∧
        c₁.nreg 5030 = sb ∧ c₁.nreg 5031 = Zb ∧
        (∀ r, r ≠ 5030 → r ≠ 5031 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals (try simp only [upd_apply]); all_goals (try split_ifs); all_goals omega
  obtain ⟨c₂, t₂, e₂, ht₂, z1, zk, zn, zr, zrm, zo⟩ :=
    mzFill_exec (P := P) c₁ e₁.wb_right a30 a31 (by omega) (by omega)
  refine ⟨c₂, _, e₁.seq e₂, by omega, z1, fun a ha => by rw [zk a ha, am], fun r hr => ?_,
    by rw [zr, ar], by rw [zrm, arm], by rw [zo, ao]⟩
  rw [zn r (by omega), ak r (by omega) (by omega)]

/-- **Clearing the resident image and its shadow.** -/
theorem clrP_exec (c : Config) (hc : WordsBounded W c) {sb SH w1 : ℕ}
    (r07 : c.nreg 7607 = sb) (r75 : c.nreg 9475 = 0) (r71 : c.nreg 9471 = SH)
    (r12 : c.nreg 7612 = w1) (r74 : c.nreg 9474 = SH + w1)
    (hW : SH + w1 + sb + sb + 1 ≤ W) :
    ∃ c' t, Exec P W clrP c c' t ∧ t ≤ 20 * sb + 32 ∧
      (∀ i < sb, c'.nmem i = 0 ∧ c'.nmem (SH + i) = 0 ∧ c'.nmem (w1 + i) = 0 ∧
        c'.nmem (SH + w1 + i) = 0) ∧
      (∀ a, ¬ a < sb → ¬ (SH ≤ a ∧ a < SH + sb) → ¬ (w1 ≤ a ∧ a < w1 + sb) →
        ¬ (SH + w1 ≤ a ∧ a < SH + w1 + sb) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 5030 ∨ 5035 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, z1, k1, n1, r1, rm1, o1⟩ :=
    clrK_exec (P := P) c hc (rb := 9475) (by omega) r07 r75 (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, z2, k2, n2, r2, rm2, o2⟩ :=
    clrK_exec (P := P) c₁ e₁.wb_right (rb := 9471) (by omega) (by rw [n1 _ (by omega), r07])
      (by rw [n1 _ (by omega), r71]) (by omega)
  obtain ⟨c₃, t₃, e₃, ht₃, z3, k3, n3, r3, rm3, o3⟩ :=
    clrK_exec (P := P) c₂ e₂.wb_right (rb := 7612) (by omega)
      (by rw [n2 _ (by omega), n1 _ (by omega), r07]) (by rw [n2 _ (by omega), n1 _ (by omega), r12])
      (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, z4, k4, n4, r4, rm4, o4⟩ :=
    clrK_exec (P := P) c₃ e₃.wb_right (rb := 9474) (by omega)
      (by rw [n3 _ (by omega), n2 _ (by omega), n1 _ (by omega), r07])
      (by rw [n3 _ (by omega), n2 _ (by omega), n1 _ (by omega), r74]) (by omega)
  have zl : ∀ i < sb, c₄.nmem (0 + i) = 0 ∧ c₄.nmem (SH + i) = 0 ∧ c₄.nmem (w1 + i) = 0 ∧
      c₄.nmem (SH + w1 + i) = 0 := fun i hi => by
    refine ⟨?_, ?_, ?_, z4 i hi⟩
    · by_cases h4 : SH + w1 ≤ 0 + i ∧ 0 + i < SH + w1 + sb
      · rw [show 0 + i = SH + w1 + (0 + i - (SH + w1)) by omega]; exact z4 _ (by omega)
      by_cases h3 : w1 ≤ 0 + i ∧ 0 + i < w1 + sb
      · rw [k4 _ (by omega), show 0 + i = w1 + (0 + i - w1) by omega]; exact z3 _ (by omega)
      by_cases h2 : SH ≤ 0 + i ∧ 0 + i < SH + sb
      · rw [k4 _ (by omega), k3 _ (by omega), show 0 + i = SH + (0 + i - SH) by omega]
        exact z2 _ (by omega)
      · rw [k4 _ (by omega), k3 _ (by omega), k2 _ (by omega)]; exact z1 i hi
    · by_cases h4 : SH + w1 ≤ SH + i ∧ SH + i < SH + w1 + sb
      · rw [show SH + i = SH + w1 + (SH + i - (SH + w1)) by omega]; exact z4 _ (by omega)
      by_cases h3 : w1 ≤ SH + i ∧ SH + i < w1 + sb
      · rw [k4 _ (by omega), show SH + i = w1 + (SH + i - w1) by omega]; exact z3 _ (by omega)
      · rw [k4 _ (by omega), k3 _ (by omega)]; exact z2 i hi
    · by_cases h4 : SH + w1 ≤ w1 + i ∧ w1 + i < SH + w1 + sb
      · rw [show w1 + i = SH + w1 + (w1 + i - (SH + w1)) by omega]; exact z4 _ (by omega)
      · rw [k4 _ (by omega)]; exact z3 i hi
  refine ⟨c₄, _, e₁.seq (e₂.seq (e₃.seq e₄)), by omega, fun i hi => by
      have := zl i hi; rw [Nat.zero_add] at this; exact this,
    fun a n1' n2' n3' n4' => ?_, fun r hr => ?_, by rw [r4, r3, r2, r1],
    by rw [rm4, rm3, rm2, rm1], by rw [o4, o3, o2, o1]⟩
  · rw [k4 a (by omega), k3 a (by omega), k2 a (by omega), k1 a (by omega)]
  · rw [n4 r hr, n3 r hr, n2 r hr, n1 r hr]

end BKMNW

end PlanarFlow
