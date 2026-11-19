module

public import PlanarFlow.BKMNW.Nf7cN
public import PlanarFlow.BKMNW.Nf7cP
public import PlanarFlow.BKMNW.Nf7bI
public import PlanarFlow.BKMNW.NoEmit

/-!
# The program `fixP` assembled

* `kTst` (the number of darts `k` of the part `j`, read from the parts of the separator:
  `r9437 := mem[Gb + 1 + j + mem[Gb]]`, `r9438 := 0`), `p7dG` (the registers of the final step
  after step 2: `9469 := r7615` (`T = p`), `9471 := r7616` (`SH`), `9474 := r9361`
  (`SH + Wf + 1`), `9475 := 0`), `z0Blk` (`9469 := r9418` for an empty part);
* **`fixPos msP = fpPro ; st2 msP ; p7dG ; loopP ; clrP ; finP`** (a part with `0 < k`: the
  prologue, step 2, the stage loop, the final step);
* **`fixZero = proP1a ; proP1b ; proP3a ; z0Blk ; finP`** (a part with `k = 0`: the face labels,
  the offset `K`, then the final step alone);
* **`fixP7 msP = kTst ; if r9438 < r9437 then fixPos msP else fixZero`**;
* `kTst_exec`, `p7dG_exec`, `z0Blk_exec`; `fixP7_noEmit`.
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

/-- The number of darts of the part `j = r6800`: `r9437 := k`, `r9438 := 0`. -/
def kTst : Stmt := block [.loadN 9437 6807, .addN 9438 6807 6800, .addN 9438 9438 9437,
  .constN 9439 1, .addN 9438 9438 9439, .loadN 9437 9438, .constN 9438 0]

/-- The registers of the final step after step 2. -/
def p7dG : Stmt := block [.copyN 9469 7615, .copyN 9471 7616, .copyN 9474 9361, .constN 9475 0]

/-- The base of the final step for an empty part. -/
def z0Blk : Stmt := block [.copyN 9469 9418]

/-- **`fixP` on a part with `0 < k`.** -/
def fixPos (msP : Stmt) : Stmt :=
  .seq fpPro (.seq (st2 msP) (.seq p7dG (.seq loopP (.seq clrP finP))))

/-- **`fixP` on a part with `k = 0`.** -/
def fixZero : Stmt := .seq proP1a (.seq proP1b (.seq proP3a (.seq z0Blk finP)))

/-- **The program `fixP`** (FixConservationOnPath on the part `r6800`), with the MSSP call
program `msP`. -/
def fixP7 (msP : Stmt) : Stmt := .seq kTst (.ifLtN 9438 9437 (fixPos msP) fixZero)

theorem fixP7_noEmit {msP : Stmt} (h : BKMNW.Stmt.noEmit msP = true) :
    BKMNW.Stmt.noEmit (fixP7 msP) = true := by
  have h1 : BKMNW.Stmt.noEmit kTst = true := by decide +kernel
  have h2 : BKMNW.Stmt.noEmit fpPro = true := by decide +kernel
  have h3 : BKMNW.Stmt.noEmit p7cA = true := by decide +kernel
  have h4 : BKMNW.Stmt.noEmit p7cM = true := by decide +kernel
  have h5 : BKMNW.Stmt.noEmit p7cSv = true := by decide +kernel
  have h6 : BKMNW.Stmt.noEmit p7cRs = true := by decide +kernel
  have h7 : BKMNW.Stmt.noEmit st2b = true := by decide +kernel
  have h8 : BKMNW.Stmt.noEmit st2c = true := by decide +kernel
  have h9 : BKMNW.Stmt.noEmit p7dG = true := by decide +kernel
  have h10 : BKMNW.Stmt.noEmit loopP = true := by decide +kernel
  have h11 : BKMNW.Stmt.noEmit clrP = true := by decide +kernel
  have h12 : BKMNW.Stmt.noEmit finP = true := by decide +kernel
  have h13 : BKMNW.Stmt.noEmit fixZero = true := by decide +kernel
  simp only [fixP7, fixPos, st2, st2ab, st2a, BKMNW.Stmt.noEmit, h, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, Bool.and_self]

variable {P : Input} {W : ℕ}

theorem kTst_exec (c : Config) (hc : WordsBounded W c) {Gb j ns k : ℕ}
    (r07 : c.nreg 6807 = Gb) (r00 : c.nreg 6800 = j) (hns : c.nmem Gb = ns)
    (hk : c.nmem (Gb + 1 + j + ns) = k) (hW : Gb + 1 + j + ns ≤ W) :
    ∃ c' t, Exec P W kTst c c' t ∧ t = 7 ∧ c'.nreg 9437 = k ∧ c'.nreg 9438 = 0 ∧
      (∀ r, (r < 9437 ∨ 9439 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hc' := hc
  unfold kTst
  exec_block
  all_goals try ((try config_simp) <;> (try simp only [r07, r00, hns, hk]) <;>
    first | omega | exact hc.2.1 _)
  refine ⟨rfl, ?_, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  rotate_left 2
  · config_simp
    have a1 : r ≠ 9437 := by omega
    have a2 : r ≠ 9438 := by omega
    have a3 : r ≠ 9439 := by omega
    simp only [upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3]
  all_goals config_simp
  all_goals try (simp only [r07, r00, hns])
  all_goals first | omega | rfl | (rw [show Gb + j + ns + 1 = Gb + 1 + j + ns by omega, hk]) |
    (repeat rw [upd_other _ _ _ (by omega)])

theorem p7dG_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W p7dG c c' t ∧ t = 4 ∧ c'.nreg 9469 = c.nreg 7615 ∧
      c'.nreg 9471 = c.nreg 7616 ∧ c'.nreg 9474 = c.nreg 9361 ∧ c'.nreg 9475 = 0 ∧
      (∀ r, r ≠ 9469 → r ≠ 9471 → r ≠ 9474 → r ≠ 9475 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold p7dG
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first | rfl | (repeat rw [upd_other _ _ _ (by omega)])

theorem z0Blk_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W z0Blk c c' t ∧ t = 1 ∧ c'.nreg 9469 = c.nreg 9418 ∧
      (∀ r, r ≠ 9469 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold z0Blk
  exec_block
  refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first | rfl | (repeat rw [upd_other _ _ _ (by omega)])

end BKMNW

end PlanarFlow
