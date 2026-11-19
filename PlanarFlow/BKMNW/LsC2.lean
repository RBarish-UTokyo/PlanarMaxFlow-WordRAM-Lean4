module

public import PlanarFlow.BKMNW.LsC

/-!
# `sepL`: the core's flags (`lsCC`)

**`lsCC_exec`**: `CC[i] = 1` iff `i` is one of the first `#B` cells of `IX'` (at `E`), else `0`,
at `CCb` (`n` cells); memory outside `[CCb, CCb + n)` kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

section Exec

variable {I : Input} {W : ℕ}

theorem lsCC_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb U nB : ℕ}
    (hR : LsR c m k R n Sb) (hL : LsL c n k U) (r58 : c.nreg 8558 = nB) (hnB : nB ≤ n)
    (hU : Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 = U)
    (hkey : ∀ q < nB, c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q) < n)
    (w : U + 46 * n + 9 * k + 15 ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsCC c c' t ∧ t ≤ 13 * n + 20 ∧
      (∀ i < n, c'.nmem (U + 45 * n + 9 * k + 15 + i) =
        if ∃ q < nB, c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q) = i then 1 else 0) ∧
      (∀ a, ¬ (U + 45 * n + 9 * k + 15 ≤ a ∧ a < U + 45 * n + 9 * k + 15 + n) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6030 ∨ (6035 < x ∧ x < 6520) ∨ 6529 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  unfold lsCC
  obtain ⟨c₀, t₀, e₀, ht₀, a21, n0, m0, rr0, rm0, o0⟩ : ∃ c₀ t₀,
      Exec I W (block [.constN 6521 1]) c c₀ t₀ ∧ t₀ = 1 ∧ c₀.nreg 6521 = 1 ∧
      (∀ x, x ≠ 6521 → c₀.nreg x = c.nreg x) ∧ c₀.nmem = c.nmem ∧
      c₀.rreg = c.rreg ∧ c₀.rmem = c.rmem ∧ c₀.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same])
  have hR0 : LsR c₀ m k R n Sb := hR.congr fun x hx => n0 x (by omega)
  have hL0 : LsL c₀ n k U := hL.congr fun x hx => n0 x (by omega)
  obtain ⟨c₁, t₁, e₁, ht₁, z1, m1, n1, rr1, rm1, o1⟩ := zfill_exec (P := I) c₀ e₀.wb_right
    (bnd := 8553) (ob := 8585) (m := n) (Ob := U + 45 * n + 9 * k + 15) hR0.r53 a21 hL0.r85
    (by omega) (by omega) (by unfold vscr; decide) (by unfold vscr; decide) (by decide)
    (by decide) (by decide) (by decide)
  have q1 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → x ≠ 6521 → c₁.nreg x = c.nreg x :=
    fun x h1 h2 h3 h4 => by rw [n1 x h1 h2 h3, n0 x h4]
  obtain ⟨c₂, t₂, e₂, ht₂, b30, b31, b32, n2, m2, rr2, rm2, o2⟩ : ∃ c₂ t₂,
      Exec I W (block [.copyN 6030 8558, .copyN 6031 8555, .copyN 6032 8585]) c₁ c₂ t₂ ∧
      t₂ = 3 ∧ c₂.nreg 6030 = c₁.nreg 8558 ∧ c₂.nreg 6031 = c₁.nreg 8555 ∧
      c₂.nreg 6032 = c₁.nreg 8585 ∧ (∀ x, (x < 6030 ∨ 6032 < x) → c₂.nreg x = c₁.nreg x) ∧
      c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have hw1 := e₁.wb_right
    have := e₁.wb_right.1 8558; have := e₁.wb_right.1 8555; have := e₁.wb_right.1 8585
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same])
  have e58 : c₁.nreg 8558 = nB := by rw [q1 _ (by unfold vscr; omega) (by omega) (by omega) (by omega)]; exact r58
  have e55 : c₁.nreg 8555 = Sb + 21 * m + 38 * n + 8 * k + 24 := by
    rw [q1 _ (by unfold vscr; omega) (by omega) (by omega) (by omega)]; exact hR.r55
  have e85 : c₁.nreg 8585 = U + 45 * n + 9 * k + 15 := by
    rw [q1 _ (by unfold vscr; omega) (by omega) (by omega) (by omega)]; exact hL.r85
  rw [e58] at b30; rw [e55] at b31; rw [e85] at b32
  have hk2 : ∀ q < nB, c₂.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q) =
      c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q) := fun q hq => by
    rw [m2, m1 _ (by omega), m0]
  obtain ⟨c₃, t₃, e₃, ht₃, T3, m3, n3, rr3, rm3, o3⟩ := pfMk_exec (P := I) c₂ e₂.wb_right
    (m := nB) (nk := n) b30 b31 b32 (fun q hq => by rw [hk2 q hq]; exact hkey q hq)
    (fun q hq => by omega) (by omega) (by omega) (by omega)
  refine ⟨c₃, t₀ + (t₁ + (t₂ + t₃)), .seq e₀ (.seq e₁ (.seq e₂ e₃)), by omega, fun i hi => ?_,
    fun a ha => ?_, fun x hx => ?_, by rw [rr3, rr2, rr1, rr0], by rw [rm3, rm2, rm1, rm0],
    by rw [o3, o2, o1, o0]⟩
  · have hk1 : ∀ q < nB, c₁.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q) =
        c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q) := fun q hq => by rw [← m2]; exact hk2 q hq
    rw [T3 i hi, m2, z1 i hi]
    by_cases h : ∃ q < nB, c₁.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q) = i
    · rw [iteT h]
      obtain ⟨q, hq, e⟩ := h
      rw [iteT ⟨q, hq, by rw [← hk1 q hq]; exact e⟩]
    · rw [iteF h, iteF (fun ⟨q, hq, e⟩ => h ⟨q, hq, by rw [hk1 q hq]; exact e⟩)]
  · rw [m3 a ha, m2, m1 a ha, m0]
  · rw [n3 x (by omega), n2 x (by omega), q1 x (by unfold vscr; omega) (by omega) (by omega)
      (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
