module

public import PlanarFlow.BKMNW.PqPipe

/-!
# The maximum-flow program for every input size (`nd d = 0` included)

`mfTopS a p … = (r8900 := 0 ; r8901 := n) ; if 0 < n then mfFullS a p … else print 0`.
**`mf_pipelineT`**: `mf_pipelineS` without the hypothesis `0 < nd d` (for `n = 0` the program
prints `[0]`: `p = []`, `Z = 0`, `q = []`, and every flow of a map without darts is maximum).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv Feas

/-- **The maximum-flow program for every input size.** -/
def mfTopS (a p : ℕ) (sepL sepX fixP c2sP s2cP retP frmP : Stmt) : Stmt :=
  .seq (block [.constN 8900 0, .constN 8778 2, .readIn 8901 8778])
    (.ifLtN 8900 8901 (mfFullS a p sepL sepX fixP c2sP s2cP retP frmP)
      (block [.constN 8902 0, .outN 8902]))

set_option maxHeartbeats 1000000 in
/-- **The maximum-flow pipeline against `MfMainSpecS`, every input size**: `mf_pipelineS` for
`mfTopS` without `0 < nd d`, within `ppHeadS C C₀ n + 31200 n + 50 K + 2 p + 3210` steps. -/
theorem mf_pipelineT {sepL sepX fixP c2sP s2cP retP frmP : Stmt} {C C₀ : ℕ}
    {R WZ : ℕ → ℕ → ℕ} {a p : ℕ}
    (hspec : MfMainSpecS sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ) (hC : 1 ≤ C)
    (hE1 : Stmt.noEmit sepL = true) (hE2 : Stmt.noEmit sepX = true)
    (hE3 : Stmt.noEmit fixP = true) (hE4 : Stmt.noEmit c2sP = true)
    (hE5 : Stmt.noEmit s2cP = true) (hE6 : Stmt.noEmit retP = true)
    (hE7 : Stmt.noEmit frmP = true)
    (hRm : ∀ N N' Z Z', N ≤ N' → Z ≤ Z' → R N Z ≤ R N' Z')
    (hWZ : ∀ N Z, WZ N Z ≤ a * (N + Z + 1) ^ p)
    {d : List ℕ} {W : ℕ} (h : MEnc d W) (hroom : PipeRoomS R a p d W) :
    ∃ (pp : List ℕ) (Z : ℕ) (q : List ℕ), pp.length = nd d ∧
      RunsWithin (compile (mfTopS a p sepL sepX fixP c2sP s2cP retP frmP) 0 ++ [Instr.halt])
        (inp d) W (ppHeadS C C₀ (nd d) + 31200 * nd d + 50 * nv d + 2 * p + 3210) (pp ++ Z :: q) ∧
      IsMax (map h.wf) (ucap d) (srcF d) (snkF d)
        (fun x => ((q.getD (pp.getD x 0) 0 : ℕ) : ℤ) - Z) := by
  have hW1 := hroom.1
  have e2 : d.getD 2 0 = nd d := rfl
  obtain ⟨c₁, t₁, e₁, ht₁, v0, v1, m1, o1⟩ : ∃ c₁ t₁,
      Exec (inp d) W (block [.constN 8900 0, .constN 8778 2, .readIn 8901 8778]) initConfig c₁ t₁ ∧
      t₁ = 3 ∧ c₁.nreg 8900 = 0 ∧ c₁.nreg 8901 = nd d ∧ c₁.nmem = initConfig.nmem ∧
      c₁.output = initConfig.output := by
    have hw := wordsBounded_initConfig W
    exec_block
    all_goals try omega
    all_goals try (config_simp; exact h.word_le 2)
    refine ⟨rfl, ?_, ?_, rfl, rfl⟩
    all_goals config_simp
    rfl
  rcases Nat.eq_zero_or_pos (nd d) with hn | hn
  · -- no darts: print `0`
    have : IsEmpty (Fin (nd d)) := ⟨fun x => by have := x.2; omega⟩
    obtain ⟨c₂, t₂, e₂, ht₂, o2⟩ : ∃ c₂ t₂,
        Exec (inp d) W (block [.constN 8902 0, .outN 8902]) c₁ c₂ t₂ ∧ t₂ = 2 ∧
        c₂.output = c₁.output ++ [0] := by
      have hw := e₁.wb_right
      exec_block
      all_goals try omega
      refine ⟨rfl, ?_⟩
      config_simp
    have ex : Exec (inp d) W (mfTopS a p sepL sepX fixP c2sP s2cP retP frmP) initConfig c₂
        (t₁ + (t₂ + 2)) := .seq e₁ (.ifLtN_false (by omega) e₂)
    obtain ⟨k, hk, rest⟩ := runsWithin_of_exec_output (out := [] ++ 0 :: []) ex
      (by rw [o2, o1]; rfl)
    exact ⟨[], 0, [], by simp [hn], ⟨k, by omega, rest⟩, isMax_of_isEmpty _ _ _ _⟩
  · obtain ⟨pp, Z, q, hl, ⟨c', t, ex, ht, ho⟩, hmax⟩ := mf_execS hspec hC hE1 hE2 hE3 hE4 hE5
      hE6 hE7 hRm hWZ h hn hroom c₁ e₁.wb_right (fun x => by rw [m1]; rfl)
    have ex' : Exec (inp d) W (mfTopS a p sepL sepX fixP c2sP s2cP retP frmP) initConfig c'
        (t₁ + (t + 1)) := .seq e₁ (.ifLtN_true (by omega) ex)
    obtain ⟨k, hk, rest⟩ := runsWithin_of_exec_output (out := pp ++ Z :: q) ex'
      (by rw [ho, o1]; rfl)
    exact ⟨pp, Z, q, hl, ⟨k, by omega, rest⟩, hmax⟩

end Pp

end BKMNW

end PlanarFlow
