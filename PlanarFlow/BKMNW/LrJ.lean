module

public import PlanarFlow.BKMNW.LrI

/-!
# The children's records of the large split: both children

**`lrec = smXA0 ; lrIni ; lrSetL ; lrOne ; lrSetR ; lrOne ; lrFin`**: the registers of stage B
from the frame (`smXA0`), the set-up (`lrIni`), the left child's record at `Xb + 2`
(`Xb = Sb + 21 m + 24 n + 8 k + 4`), the right child's at `Xb + 2 + zl`, the sizes `zl`, `zr` at
`Xb`, `Xb + 1` and `r6501 := Xb`.

**`lrec_rec`**: at a node `(.node l r π, Hs, σ)` whose parent record (`RArr`, `n` darts, state
`st` on the core's piece map `B`) is at `R` below `Sb`, from the flags of the left piece `LF`, of
the path's vertices `CV`, of the holes meeting the path `HM`, of the path's darts `PF` and of `B`
(`CC`) over the record (at bases `≥ E = Sb + 21 m + 38 n + 8 k + 24`, registers `8500 … 8504`),
the bit `hb` (`8505`), and the children's calls
`l = ds.dec S T l.piece Hs' (childRot st B π.path.darts (pdarts (core Q l.piece) Hs'))
(decide (1 - hb = 1))` (`Hs' = childHoles Hs π.path.mverts`; the same for `r`): within
**`900 n + 50 k + 800`** steps, **`RecsOut`** from `r6501` between `Sb + 21 m + 4 k + 2` and `E`;
memory below `Sb` and from `E` on kept; registers `< 3013` and `≥ 8520` kept.
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

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

/-- The left child's parameters. -/
def lrSetL : Stmt := block [.constN 8508 0, .copyN 8509 8507]

/-- The right child's parameters (the left record's size saved in `8511`). -/
def lrSetR : Stmt := block [.copyN 8511 8510, .constN 8508 1, .addN 8509 8507 8510]

/-- The sizes and the base of the records. -/
def lrFin : Stmt := block [.storeN 8507 8511, .constN 8518 1, .addN 8519 8507 8518,
  .storeN 8519 8510, .copyN 6501 8507]

/-- **The children's records of the large split.** -/
def lrec : Stmt := .seq smXA0 (.seq lrIni (.seq lrSetL (.seq lrOne (.seq lrSetR
  (.seq lrOne lrFin)))))

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {ν : V → ℕ} {S T : Finset V} {ds : DSys M}

section Exec

variable {I : Input} {W : ℕ}

theorem lrSetL_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec I W lrSetL c c' t ∧ t = 2 ∧ c'.nreg 8508 = 0 ∧ c'.nreg 8509 = c.nreg 8507 ∧
      (∀ x, (x < 8508 ∨ 8509 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hc.1 8507
  unfold lrSetL
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])
    try omega

theorem lrSetR_exec (c : Config) (hc : WordsBounded W c) (w : c.nreg 8507 + c.nreg 8510 ≤ W)
    (hW : 2 ≤ W) :
    ∃ c' t, Exec I W lrSetR c c' t ∧ t = 3 ∧ c'.nreg 8511 = c.nreg 8510 ∧ c'.nreg 8508 = 1 ∧
      c'.nreg 8509 = c.nreg 8507 + c.nreg 8510 ∧
      (∀ x, (x < 8508 ∨ (8509 < x ∧ x ≠ 8511)) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hc.1 8510; have := hc.1 6521
  unfold lrSetR
  exec_block
  all_goals try omega
  all_goals try (show _ ≤ W; simp (disch := omega) only [Config.nreg_mk, upd_other, upd_same]; omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])
    try omega

theorem lrFin_exec (c : Config) (hc : WordsBounded W c) {Xb zl zr : ℕ}
    (r07 : c.nreg 8507 = Xb) (r11 : c.nreg 8511 = zl) (r10 : c.nreg 8510 = zr)
    (w : Xb + 2 ≤ W) :
    ∃ c' t, Exec I W lrFin c c' t ∧ t = 5 ∧ c'.nmem Xb = zl ∧ c'.nmem (Xb + 1) = zr ∧
      c'.nreg 6501 = Xb ∧ (∀ a, (a < Xb ∨ Xb + 1 < a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6501 ∨ (6501 < x ∧ x < 8518) ∨ 8519 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hc.1 8510; have := hc.1 8511
  unfold lrFin
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r07, r11, r10]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun a ha => ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r07, r11, r10])
    try omega

end Exec

end MfDrv

end BKMNW

end PlanarFlow
