module

public import PlanarFlow.BKMNW.PpFin

/-!
# Printing arrays

`prL`: print `mem (A + s i)` for `i < m` (`A = r8775`, `s = r8776`, `m = r8741`).
**`prL_exec`**: the output grows by `(List.range m).map (fun i => mem (A + s i))`.
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

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv

variable {P : Input} {W : ℕ}

/-- **The print loop.** -/
def prL : Stmt := .seq (block [.constN 8740 0]) (.whileLtN 8740 8741
  (block [.mulN 8743 8740 8776, .addN 8743 8743 8775, .loadN 8744 8743, .outN 8744,
    .addN 8740 8740 8704]))

theorem prL_exec (c : Config) (hc : WordsBounded W c) {m Ab s : ℕ}
    (r41 : c.nreg 8741 = m) (r04 : c.nreg 8704 = 1) (r75 : c.nreg 8775 = Ab)
    (r76 : c.nreg 8776 = s) (hW : Ab + s * m + m + 1 ≤ W) :
    ∃ c' t, Exec P W prL c c' t ∧ t ≤ 7 * m + 3 ∧
      c'.output = c.output ++ (List.range m).map (fun i => c.nmem (Ab + s * i)) ∧
      c'.nmem = c.nmem ∧ (∀ x, x ≠ 8740 → x ≠ 8743 → x ≠ 8744 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem := by
  obtain ⟨c₁, k₁, e₁, hk₁, v1, n1, m1, rr1, rm1, o1⟩ := cst_exec (P := P) (r := 8740) (v := 0)
    c hc (Nat.zero_le _)
  let J : ℕ → Config → Prop := fun i d =>
    d.output = c.output ++ (List.range i).map (fun j => c.nmem (Ab + s * j)) ∧
      d.nmem = c.nmem ∧ (∀ x, x ≠ 8740 → x ≠ 8743 → x ≠ 8744 → d.nreg x = c.nreg x) ∧
      d.rreg = c.rreg ∧ d.rmem = c.rmem
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h40, j1, j2, j3, j4, j5⟩ := lnRange (P := P) (a := 8740)
    (b := 8741) (body := block [.mulN 8743 8740 8776, .addN 8743 8743 8775, .loadN 8744 8743,
      .outN 8744, .addN 8740 8740 8704]) J (B := 5) c₁ e₁.wb_right v1
    (by rw [n1 _ (by omega)]; exact r41) (Nat.zero_le m)
    ⟨by rw [o1]; simp, m1, fun x h1 _ _ => n1 x h1, rr1, rm1⟩
    (fun i d hlo hhi hw hci hbn ⟨j1, j2, j3, j4, j5⟩ => by
      have q76 : d.nreg 8776 = s := by rw [j3 _ (by omega) (by omega) (by omega), r76]
      have q75 : d.nreg 8775 = Ab := by rw [j3 _ (by omega) (by omega) (by omega), r75]
      have q04 : d.nreg 8704 = 1 := by rw [j3 _ (by omega) (by omega) (by omega), r04]
      have hsi : s * i ≤ s * m := Nat.mul_le_mul_left _ (by omega)
      exec_block
      · config_simp; rw [hci, q76]; nlinarith
      · config_simp; rw [hci, q76, q75]; nlinarith
      · config_simp; rw [hci, q04]; omega
      refine ⟨by omega, ?_, ?_, ⟨?_, ?_, fun x h1 h2 h3 => ?_, ?_, ?_⟩⟩
      · config_simp; rw [hci, q04]
      · config_simp; exact hbn
      · config_simp; rw [hci, q76, q75, j1, j2, List.range_succ, List.map_append,
          List.append_assoc]
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
        rw [Nat.mul_comm, Nat.add_comm]
      · config_simp; exact j2
      · config_simp; simp (disch := omega) only [upd_other]; exact j3 x h1 h2 h3
      · config_simp; exact j4
      · config_simp; exact j5)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by rw [Nat.sub_zero] at hk₂; omega, j1, j2, j3, j4, j5⟩

end Pp

end BKMNW

end PlanarFlow
