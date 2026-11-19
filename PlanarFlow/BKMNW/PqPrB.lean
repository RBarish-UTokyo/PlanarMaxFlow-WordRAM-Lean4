module

public import PlanarFlow.BKMNW.PqPP
public import PlanarFlow.BKMNW.PqSpec

/-!
# Reading the flow at the base `B`

`prB` (`PpPrB.lean`) prints the root frame of the preprocessing at the base `0`. Here the frame
is at `B + frB d` with `B = zB a p d` (`PqZ.lean`): `prBB a p = zP a p ; prBSB ; prL`
recomputes the base from the input (nothing of the registers after the max-flow program is
needed), then prints `Z = mem[B + frB + 3]` and the `N = mem[B + frB]` cells from
`B + frB + 4 + 6 N`. **`prBB_exec`** (`≤ 9 n + p + 7 N + 60` steps).
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

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv Feas
  NegSSSP.Driver

variable {P : Input} {W : ℕ}

/-- `prBS` at the base `r8730`. -/
def prBSB : Stmt :=
  block [.constN 8778 2, .readIn 8700 8778, .constN 8778 0, .readIn 8707 8778,
    .constN 8778 128, .mulN 8750 8700 8778, .constN 8778 2, .mulN 8751 8707 8778,
    .addN 8750 8750 8751, .constN 8778 8, .addN 8750 8750 8778, .addN 8750 8750 8730,
    .loadN 8741 8750,
    .constN 8778 3, .addN 8752 8750 8778, .loadN 8753 8752, .outN 8753,
    .constN 8778 6, .mulN 8775 8741 8778, .addN 8775 8775 8750, .constN 8778 4,
    .addN 8775 8775 8778, .constN 8776 1, .constN 8704 1]

/-- **The print of the flow at the base `zB a p d`**. -/
def prBB (a p : ℕ) : Stmt := .seq (zP a p) (.seq prBSB prL)

theorem prBSB_exec {d : List ℕ} (hP : P.data = d) (hwd : ∀ i, word d i ≤ W) (c : Config)
    (hc : WordsBounded W c) {B N Z : ℕ} (r30 : c.nreg 8730 = B)
    (hN : c.nmem (B + frB d) = N) (hZ : c.nmem (B + frB d + 3) = Z)
    (hW : B + frB d + 8 * N + 200 ≤ W) :
    ∃ c' t, Exec P W prBSB c c' t ∧ t = 24 ∧ c'.nreg 8741 = N ∧
      c'.nreg 8775 = B + frB d + 4 + 6 * N ∧ c'.nreg 8776 = 1 ∧ c'.nreg 8704 = 1 ∧
      c'.nmem = c.nmem ∧ c'.output = c.output ++ [Z] := by
  have e2 : d.getD 2 0 = nd d := rfl
  have e0 : d.getD 0 0 = nv d := rfl
  unfold frB at hN hZ hW
  have k1 : nd d * 128 + nv d * 2 + 8 + B = B + (128 * nd d + 2 * nv d + 8) := by ring
  have hN' : c.nmem (nd d * 128 + nv d * 2 + 8 + B) = N := by rw [k1]; exact hN
  have hZ' : c.nmem (nd d * 128 + nv d * 2 + 8 + B + 3) = Z := by rw [k1]; exact hZ
  unfold prBSB
  exec_block
  all_goals try omega
  all_goals try (config_simp; rw [hP]; first | exact hwd 2 | exact hwd 0)
  all_goals try (config_simp; rw [hP, e2]; omega)
  all_goals try (config_simp; rw [hP, e0]; omega)
  all_goals try (config_simp; rw [hP, e2, e0]; omega)
  all_goals try (config_simp; rw [hP, e2, e0, r30]; omega)
  all_goals try (config_simp; rw [hP, e2, e0, r30, hN']; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, ?_⟩
  all_goals config_simp
  all_goals try (rw [hP, e2, e0, r30, hN'])
  all_goals try (rw [hP, e2, e0, r30, hZ'])
  all_goals try (rw [hP, e2, e0, r30, hN']; unfold frB; ring)
  all_goals try (unfold frB; ring)

/-- **The print of the flow at the base**: `Z`, then the `N` cells from `B + frB + 4 + 6 N`. -/
theorem prBB_exec {d : List ℕ} (hP : P.data = d) (hwd : ∀ i, word d i ≤ W) (a p : ℕ)
    (c : Config) (hc : WordsBounded W c) {N Z : ℕ} (hN : c.nmem (zB a p d + frB d) = N)
    (hZ : c.nmem (zB a p d + frB d + 3) = Z) (hW1 : 7 * nd d + zb d + 20 ≤ W)
    (hW3 : (7 * nd d + zb d + 1) ^ p ≤ W)
    (hW : zB a p d + frB d + 8 * N + 200 ≤ W) :
    ∃ c' t, Exec P W (prBB a p) c c' t ∧ t ≤ 9 * nd d + p + 7 * N + 60 ∧
      c'.output = c.output ++ Z :: (List.range N).map
        (fun i => c.nmem (zB a p d + frB d + 4 + 6 * N + i)) := by
  obtain ⟨c₀, t₀, e₀, ht₀, r30, m0, -, -, o0⟩ := zP_exec hP hwd a p c hc hW1
    (by unfold frB at hW; omega) (by omega) hW3
  rw [← m0] at hN hZ
  obtain ⟨c₁, t₁, e₁, ht₁, r41, r75, r76, r04, m1, o1⟩ := prBSB_exec hP hwd c₀ e₀.wb_right r30
    hN hZ hW
  obtain ⟨c₂, t₂, e₂, ht₂, o2, -, -, -, -⟩ := prL_exec (P := P) c₁ e₁.wb_right r41 r04 r75 r76
    (by omega)
  refine ⟨c₂, t₀ + (t₁ + t₂), .seq e₀ (.seq e₁ e₂), by omega, ?_⟩
  rw [o2, o1, m1, o0, m0, List.append_assoc]
  simp only [List.singleton_append, one_mul]

end Pp

end BKMNW

end PlanarFlow
