module

public import PlanarFlow.BKMNW.SepSplit

/-!
# The small separator program, stage A: one step of `smD` on the record, the outputs of
`SepPSpec`

At a node call `x = (.node l r π, Hs, σ)` of the small decomposition (`x.1 = smD pk S T P Hs`,
`P = x.1.piece`) in the extended frame (`m` frame darts at `d`, the record at `R` with `n` darts
of the piece enumerated by `g` increasingly in `gid`), **`smXA`**:

* `smA0`, `smA1`, `smA2`: the registers (`SmRegs`: `d m k R n Sb`, the bases
  `A = Sb + 21 m + 4 k + 2` (the ones), `Ob = A + n` (the outputs of `smStep`),
  `Wb' = A + 4 n + k + 2` (the flags of stage B), `B2`, `B3`, `Xb` (the children's records), the
  record's arrays `GP RP HP KP VP FX`), and the inputs `5300 … 5307` of `smStep`;
* `smFill`: the ones `PF[j] = 1` at `A` (`mapRunS`);
* `smStep` on the record's arrays: the flags of `l.piece`, of the path's darts and
  vertices **on all the darts of the piece**, the holes meeting the path, the tags, from `Ob`;
* `smAG`: three gathers through `FX` and a copy give the outputs of `SepPSpec` at `Sb`.

* `PkMin` (the choice picks the dart of least `gid`), `SmRegs`, `smA0_exec`, `smA1_exec`,
  `smA2_exec`, **`smXA_exec`** (within `300 n + 27 m + 26 k + 300` steps).
Registers `5500 … 5531` (and the loops' own: `5300 … 5440` of `smStep`, `6520 … 6523` of
`mapRunS`, `6210 … 6217` of `ggProg`, `4910 … 4916` of `cpArr`).
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

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The choice picks the dart of least `gid`** of a nonempty set. -/
def PkMin (gid : D → ℕ) (pk : Finset D → D) : Prop :=
  ∀ X : Finset D, X.Nonempty → pk X ∈ X ∧ ∀ y ∈ X, gid (pk X) ≤ gid y

/-! ### The programs -/

/-- `d m k R n Sb`. -/
def smA0 : Stmt := block [.copyN 5500 3004, .loadN 5501 5500, .constN 5519 1,
  .addN 5520 5500 5519, .loadN 5502 5520, .constN 5519 7, .mulN 5520 5519 5501,
  .addN 5520 5520 5500, .constN 5519 4, .addN 5520 5520 5519, .loadN 5503 5520,
  .loadN 5504 5503, .copyN 5505 6500]

/-- The bases of the scratch. -/
def smA1 : Stmt := block [.constN 5519 21, .mulN 5520 5519 5501, .addN 5506 5505 5520,
  .constN 5519 4, .mulN 5520 5519 5502, .addN 5506 5506 5520, .constN 5519 2,
  .addN 5506 5506 5519, .addN 5507 5506 5504, .addN 5521 5507 5504, .addN 5522 5521 5504,
  .addN 5523 5522 5504, .addN 5508 5523 5502, .addN 5508 5508 5519, .constN 5519 7,
  .mulN 5520 5519 5504, .addN 5509 5508 5520, .constN 5519 3, .mulN 5520 5519 5502,
  .addN 5509 5509 5520, .addN 5528 5509 5504, .addN 5510 5528 5504, .addN 5530 5510 5504,
  .addN 5531 5530 5504, .addN 5511 5531 5504]

/-- The record's arrays, the output bases, the inputs of `smStep`. -/
def smA2 : Stmt := block [.constN 5519 3, .addN 5517 5503 5519, .addN 5512 5517 5504,
  .addN 5513 5512 5504, .addN 5514 5513 5504, .addN 5515 5514 5504, .addN 5516 5515 5504,
  .addN 5516 5516 5504, .addN 5524 5505 5501, .addN 5525 5524 5501, .addN 5526 5525 5501,
  .constN 5519 2, .addN 5527 5502 5519, .copyN 5300 5504, .copyN 5301 5506, .copyN 5302 5512,
  .copyN 5303 5513, .copyN 5304 5514, .copyN 5305 5515, .copyN 5306 5507, .copyN 5307 5502,
  .constN 6521 1]

/-- The ones at `A`. -/
def smFill : Stmt := mapRunS (block [.constN 6523 1]) 5504 5506

/-- The outputs of `SepPSpec` at `Sb`: three gathers through `FX`, a copy of the hole flags and
the tags. -/
def smAG : Stmt := .seq (ggProg 5501 5516 5507 5505) (.seq (ggProg 5501 5516 5521 5524)
  (.seq (ggProg 5501 5516 5522 5525)
    (.seq (block [.copyN 4910 5527, .copyN 4911 5523, .copyN 4912 5526]) cpArr)))

/-- The set-up of stage A: the registers and the ones. -/
def smXA0 : Stmt := .seq smA0 (.seq smA1 (.seq smA2 smFill))

/-- **Stage A of the small separator program.** -/
def smXA : Stmt := .seq smXA0 (.seq smStep smAG)

/-- **The registers of the small separator program** (`A` the first scratch base). -/
structure SmRegs (c : Config) (d m k R n Sb A : ℕ) : Prop where
  hA : A = Sb + 21 * m + 4 * k + 2
  r00 : c.nreg 5500 = d
  r01 : c.nreg 5501 = m
  r02 : c.nreg 5502 = k
  r03 : c.nreg 5503 = R
  r04 : c.nreg 5504 = n
  r05 : c.nreg 5505 = Sb
  r06 : c.nreg 5506 = A
  r07 : c.nreg 5507 = A + n
  r21 : c.nreg 5521 = A + 2 * n
  r22 : c.nreg 5522 = A + 3 * n
  r23 : c.nreg 5523 = A + 4 * n
  r08 : c.nreg 5508 = A + 4 * n + k + 2
  r09 : c.nreg 5509 = A + 11 * n + 4 * k + 2
  r28 : c.nreg 5528 = A + 12 * n + 4 * k + 2
  r10 : c.nreg 5510 = A + 13 * n + 4 * k + 2
  r30 : c.nreg 5530 = A + 14 * n + 4 * k + 2
  r31 : c.nreg 5531 = A + 15 * n + 4 * k + 2
  r11 : c.nreg 5511 = A + 16 * n + 4 * k + 2
  r17 : c.nreg 5517 = R + 3
  r12 : c.nreg 5512 = R + 3 + n
  r13 : c.nreg 5513 = R + 3 + 2 * n
  r14 : c.nreg 5514 = R + 3 + 3 * n
  r15 : c.nreg 5515 = R + 3 + 4 * n
  r16 : c.nreg 5516 = R + 3 + 6 * n
  r24 : c.nreg 5524 = Sb + m
  r25 : c.nreg 5525 = Sb + 2 * m
  r26 : c.nreg 5526 = Sb + 3 * m
  r27 : c.nreg 5527 = k + 2

/-- The registers of `SmRegs`. -/
def smReg (x : ℕ) : Prop := (5500 ≤ x ∧ x ≤ 5517) ∨ (5521 ≤ x ∧ x ≤ 5528) ∨ x = 5530 ∨ x = 5531

lemma SmRegs.congr {c c' : Config} {d m k R n Sb A : ℕ} (h : SmRegs c d m k R n Sb A)
    (hr : ∀ x, smReg x → c'.nreg x = c.nreg x) : SmRegs c' d m k R n Sb A where
  hA := h.hA
  r00 := by rw [hr _ (by unfold smReg; omega)]; exact h.r00
  r01 := by rw [hr _ (by unfold smReg; omega)]; exact h.r01
  r02 := by rw [hr _ (by unfold smReg; omega)]; exact h.r02
  r03 := by rw [hr _ (by unfold smReg; omega)]; exact h.r03
  r04 := by rw [hr _ (by unfold smReg; omega)]; exact h.r04
  r05 := by rw [hr _ (by unfold smReg; omega)]; exact h.r05
  r06 := by rw [hr _ (by unfold smReg; omega)]; exact h.r06
  r07 := by rw [hr _ (by unfold smReg; omega)]; exact h.r07
  r21 := by rw [hr _ (by unfold smReg; omega)]; exact h.r21
  r22 := by rw [hr _ (by unfold smReg; omega)]; exact h.r22
  r23 := by rw [hr _ (by unfold smReg; omega)]; exact h.r23
  r08 := by rw [hr _ (by unfold smReg; omega)]; exact h.r08
  r09 := by rw [hr _ (by unfold smReg; omega)]; exact h.r09
  r28 := by rw [hr _ (by unfold smReg; omega)]; exact h.r28
  r10 := by rw [hr _ (by unfold smReg; omega)]; exact h.r10
  r30 := by rw [hr _ (by unfold smReg; omega)]; exact h.r30
  r31 := by rw [hr _ (by unfold smReg; omega)]; exact h.r31
  r11 := by rw [hr _ (by unfold smReg; omega)]; exact h.r11
  r17 := by rw [hr _ (by unfold smReg; omega)]; exact h.r17
  r12 := by rw [hr _ (by unfold smReg; omega)]; exact h.r12
  r13 := by rw [hr _ (by unfold smReg; omega)]; exact h.r13
  r14 := by rw [hr _ (by unfold smReg; omega)]; exact h.r14
  r15 := by rw [hr _ (by unfold smReg; omega)]; exact h.r15
  r16 := by rw [hr _ (by unfold smReg; omega)]; exact h.r16
  r24 := by rw [hr _ (by unfold smReg; omega)]; exact h.r24
  r25 := by rw [hr _ (by unfold smReg; omega)]; exact h.r25
  r26 := by rw [hr _ (by unfold smReg; omega)]; exact h.r26
  r27 := by rw [hr _ (by unfold smReg; omega)]; exact h.r27

section Exec

variable {I : Input} {W : ℕ}

theorem smA0_exec (c : Config) (hc : WordsBounded W c) {d m k R n Sb : ℕ}
    (r4 : c.nreg 3004 = d) (r50 : c.nreg 6500 = Sb) (hm : c.nmem d = m)
    (hk : c.nmem (d + 1) = k) (hR : c.nmem (d + 7 * m + 4) = R) (hn : c.nmem R = n)
    (w : d + 7 * m + 4 ≤ W) (hW : 21 ≤ W) :
    ∃ c' t, Exec I W smA0 c c' t ∧ t = 13 ∧ c'.nreg 5500 = d ∧ c'.nreg 5501 = m ∧
      c'.nreg 5502 = k ∧ c'.nreg 5503 = R ∧ c'.nreg 5504 = n ∧ c'.nreg 5505 = Sb ∧
      (∀ x, (x < 5500 ∨ (5505 < x ∧ x ≠ 5519 ∧ x ≠ 5520)) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smA0
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r4, r50, hm]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r4, r50, hm, hk])
    try omega
  all_goals (rw [show 7 * m + d + 4 = d + 7 * m + 4 by omega, hR]; try rw [hn])

theorem smA1_exec (c : Config) (hc : WordsBounded W c) {m k n Sb : ℕ}
    (r01 : c.nreg 5501 = m) (r02 : c.nreg 5502 = k) (r04 : c.nreg 5504 = n)
    (r05 : c.nreg 5505 = Sb) (w : Sb + 21 * m + 4 * k + 2 + 16 * n + 4 * k + 2 ≤ W)
    (hW : 21 ≤ W) :
    ∃ c' t, Exec I W smA1 c c' t ∧ t = 25 ∧
      c'.nreg 5506 = Sb + 21 * m + 4 * k + 2 ∧
      c'.nreg 5507 = Sb + 21 * m + 4 * k + 2 + n ∧
      c'.nreg 5521 = Sb + 21 * m + 4 * k + 2 + 2 * n ∧
      c'.nreg 5522 = Sb + 21 * m + 4 * k + 2 + 3 * n ∧
      c'.nreg 5523 = Sb + 21 * m + 4 * k + 2 + 4 * n ∧
      c'.nreg 5508 = Sb + 21 * m + 4 * k + 2 + 4 * n + k + 2 ∧
      c'.nreg 5509 = Sb + 21 * m + 4 * k + 2 + 11 * n + 4 * k + 2 ∧
      c'.nreg 5528 = Sb + 21 * m + 4 * k + 2 + 12 * n + 4 * k + 2 ∧
      c'.nreg 5510 = Sb + 21 * m + 4 * k + 2 + 13 * n + 4 * k + 2 ∧
      c'.nreg 5530 = Sb + 21 * m + 4 * k + 2 + 14 * n + 4 * k + 2 ∧
      c'.nreg 5531 = Sb + 21 * m + 4 * k + 2 + 15 * n + 4 * k + 2 ∧
      c'.nreg 5511 = Sb + 21 * m + 4 * k + 2 + 16 * n + 4 * k + 2 ∧
      (∀ x, (x < 5506 ∨ (5511 < x ∧ x < 5519) ∨ (5523 < x ∧ x ≠ 5528 ∧ x ≠ 5530 ∧
        x ≠ 5531)) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smA1
  exec_block
  all_goals try omega
  all_goals
    try (config_simp; simp (disch := omega) only [upd_other, upd_same, r01, r02, r04, r05]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl,
    rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r01, r02, r04, r05])
    try omega

theorem smA2_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb A : ℕ}
    (r01 : c.nreg 5501 = m) (r02 : c.nreg 5502 = k) (r03 : c.nreg 5503 = R)
    (r04 : c.nreg 5504 = n) (r05 : c.nreg 5505 = Sb) (r06 : c.nreg 5506 = A)
    (r07 : c.nreg 5507 = A + n) (w : R + 3 + 6 * n ≤ W) (w' : Sb + 3 * m + k + 2 ≤ W)
    (hW : 21 ≤ W) :
    ∃ c' t, Exec I W smA2 c c' t ∧ t = 22 ∧ c'.nreg 5517 = R + 3 ∧
      c'.nreg 5512 = R + 3 + n ∧ c'.nreg 5513 = R + 3 + 2 * n ∧ c'.nreg 5514 = R + 3 + 3 * n ∧
      c'.nreg 5515 = R + 3 + 4 * n ∧ c'.nreg 5516 = R + 3 + 6 * n ∧ c'.nreg 5524 = Sb + m ∧
      c'.nreg 5525 = Sb + 2 * m ∧ c'.nreg 5526 = Sb + 3 * m ∧ c'.nreg 5527 = k + 2 ∧
      c'.nreg 5300 = n ∧ c'.nreg 5301 = A ∧ c'.nreg 5302 = R + 3 + n ∧
      c'.nreg 5303 = R + 3 + 2 * n ∧ c'.nreg 5304 = R + 3 + 3 * n ∧
      c'.nreg 5305 = R + 3 + 4 * n ∧ c'.nreg 5306 = A + n ∧ c'.nreg 5307 = k ∧
      c'.nreg 6521 = 1 ∧
      (∀ x, (x < 5300 ∨ (5307 < x ∧ x < 5512) ∨ (5527 < x ∧ x ≠ 6521) ∨
        (5519 < x ∧ x < 5524)) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h6 : A ≤ W := r06 ▸ hc.1 5506
  have h7 : A + n ≤ W := r07 ▸ hc.1 5507
  unfold smA2
  exec_block
  all_goals try omega
  all_goals
    try (config_simp; simp (disch := omega) only [upd_other, upd_same, r01, r02, r03, r04, r05, r06, r07]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r01, r02, r03, r04, r05, r06, r07])
    try omega

end Exec

end MfDrv

end BKMNW

end PlanarFlow
