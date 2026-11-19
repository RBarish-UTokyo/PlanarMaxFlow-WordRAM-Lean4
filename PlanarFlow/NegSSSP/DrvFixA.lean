module

public import PlanarFlow.NegSSSP.NdFullDrive
public import PlanarFlow.NegSSSP.Enc.HoistGen

/-!
# The recursion's program with its two instance constants hoisted

The program of `Driver.drive_negsssp_machine`,
`driver testS (leafS Gt) splitS0 (nodeS Gt (Fs WN Gt))`, depends on the instance through two
constants only: the table base `Gt` (in `lfSet`, `ndB1`, `ndB2`) and the node's word bound `WN`
(in `fbW`). Constant hoisting (`HoistGen.lean`) at the parameter base `fxPB = 3100`:

* `fxTbl`: the markers `fxMG ↦ 0`, `fxMW ↦ 1`; the hoisted pieces `lfT` (the leaf), `ndBT` (the
  node's middle), `fbOutT` (after the node) and the kernel-checked equations `lfT_eq`, `ndBT_eq`,
  `fbOutT_eq` (`hsUn fxPB (fxV Gt WN) piece = piece of the instance`, for **all** `Gt`, `WN`);
* **`drvT`** `= driver testS lfT splitS0 (nodeST (FsT))`: **one fixed statement**, reading `Gt`
  from `r3100` and `WN` from `r3101`;
* **`drvT_eq`**: `hsUn fxPB (fxV Gt WN) drvT = driver testS (leafS Gt) splitS0
  (nodeS Gt (Fs WN Gt))` (the fixed pieces are their own `hsUn`: they name only registers
  `< 3100`, `hsUn_id`; Klein's node `nodeFullR` by `nodeFullR_ok`);
* **`drvT_ok`**: `hsOK fxPB 2 drvT` (registers `< 3100`, the parameters `3100`, `3101` read by
  `copyN` only);
* **`drvT_exec`**: a run of the instance's program from a configuration holding `Gt`, `WN` in
  `r3100`, `r3101` is a run of `drvT` between the same configurations in the same steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt PlanarFlow.NegSSSP.Driver PlanarFlow.NegSSSP.Frame

/-! ### Statements naming only registers below the parameter base -/

theorem hsUnI_id {PB : ℕ} {v : ℕ → ℕ} {i : Instr}
    (h : i.regsOK (fun r => decide (r < PB)) = true) : hsUnI PB v i = i := by
  refine hsUnI_of_not fun r a he => ?_
  subst he
  have := List.all_eq_true.1 h a (by simp [Instr.regs])
  simpa using this

/-- A statement naming only registers `< PB` is its own `hsUn`. -/
theorem hsUn_id {PB : ℕ} {v : ℕ → ℕ} :
    ∀ s : Stmt, s.regsOK (fun r => decide (r < PB)) = true → hsUn PB v s = s
  | .skip, _ => rfl
  | .instr i, h => by simp only [hsUn, hsUnI_id h]
  | .seq s t, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true] at h
    simp only [hsUn, hsUn_id s h.1, hsUn_id t h.2]
  | .ifLtN a b s t, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true] at h
    simp only [hsUn, hsUn_id s h.1.2, hsUn_id t h.2]
  | .ifLtR a b s t, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true] at h
    simp only [hsUn, hsUn_id s h.1.2, hsUn_id t h.2]
  | .whileLtN a b s, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true] at h
    simp only [hsUn, hsUn_id s h.2]
  | .whileLtR a b s, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true] at h
    simp only [hsUn, hsUn_id s h.2]

theorem hsOKI_of_regsOK {PB np : ℕ} {i : Instr}
    (h : i.regsOK (fun r => decide (r < PB)) = true) : hsOKI PB np i = true := by
  cases i with
  | copyN r a =>
    have h1 := List.all_eq_true.1 h r (by simp [Instr.regs])
    have h2 := List.all_eq_true.1 h a (by simp [Instr.regs])
    simp only [decide_eq_true_eq] at h1 h2
    simp [hsOKI, h1, h2]
  | _ => exact h

/-- A statement naming only registers `< PB` meets the register condition of hoisting. -/
theorem hsOK_of_regsOK {PB np : ℕ} :
    ∀ s : Stmt, s.regsOK (fun r => decide (r < PB)) = true → hsOK PB np s = true
  | .skip, _ => rfl
  | .instr i, h => hsOKI_of_regsOK h
  | .seq s t, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true] at h
    simp only [hsOK, hsOK_of_regsOK s h.1, hsOK_of_regsOK t h.2, Bool.and_self]
  | .ifLtN a b s t, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true] at h
    simp only [hsOK, hsOK_of_regsOK s h.1.2, hsOK_of_regsOK t h.2, h.1.1.1, h.1.1.2,
      Bool.and_self]
  | .ifLtR a b s t, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true] at h
    simp only [hsOK, hsOK_of_regsOK s h.1.2, hsOK_of_regsOK t h.2, Bool.and_self]
  | .whileLtN a b s, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true] at h
    simp only [hsOK, hsOK_of_regsOK s h.2, h.1.1, h.1.2, Bool.and_self]
  | .whileLtR a b s, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true] at h
    simp only [hsOK, hsOK_of_regsOK s h.2]

/-! ### The markers and the hoisted pieces -/

/-- The parameter base: `Gt` in `r3100`, `WN` in `r3101`. -/
def fxPB : ℕ := 3100

/-- The marker of `Gt`. -/
def fxMG : ℕ := 7000000000000001

/-- The marker of `WN`. -/
def fxMW : ℕ := 7000000000000013

/-- The table of the markers. -/
def fxTbl : List (ℕ × ℕ) := [(fxMG, 0), (fxMW, 1)]

/-- The parameter values. -/
def fxV (Gt WN : ℕ) (j : ℕ) : ℕ := [Gt, WN].getD j 0

/-- The hoisted leaf. -/
def lfT : Stmt := hsHoist fxPB fxTbl (leafS fxMG)

/-- The hoisted middle of the node step. -/
def ndBT : Stmt := hsHoist fxPB fxTbl (ndB fxMG)

/-- The hoisted end of the full branch. -/
def fbOutT : Stmt := hsHoist fxPB fxTbl (fbOut fxMW)

theorem lfT_eq (Gt WN : ℕ) : hsUn fxPB (fxV Gt WN) lfT = leafS Gt := by kernel_rfl

theorem ndBT_eq (Gt WN : ℕ) : hsUn fxPB (fxV Gt WN) ndBT = ndB Gt := by kernel_rfl

theorem fbOutT_eq (Gt WN : ℕ) : hsUn fxPB (fxV Gt WN) fbOutT = fbOut WN := by kernel_rfl

theorem lfT_ok : hsOK fxPB 2 lfT = true := by kernel_rfl

theorem ndBT_ok : hsOK fxPB 2 ndBT = true := by kernel_rfl

theorem fbOutT_ok : hsOK fxPB 2 fbOutT = true := by kernel_rfl

/-! ### The fixed pieces -/

/-- Register condition below the parameter base. -/
abbrev fxU : ℕ → Bool := fun r => decide (r < fxPB)

theorem testS_rk : testS.regsOK fxU = true := by decide +kernel
theorem splitS0_rk : splitS0.regsOK fxU = true := by decide +kernel
theorem peekB_rk : peekB.regsOK fxU = true := by decide +kernel
theorem popB_rk : popB.regsOK fxU = true := by decide +kernel
theorem pushB_rk : pushB.regsOK fxU = true := by decide +kernel
theorem coB_rk : coB.regsOK fxU = true := by decide +kernel
theorem coPost_rk : coPost.regsOK fxU = true := by decide +kernel
theorem ndFront_rk : ndFront.regsOK fxU = true := by decide +kernel
theorem ndNone_rk : ndNone.regsOK fxU = true := by decide +kernel
theorem ndC_rk : ndC.regsOK fxU = true := by decide +kernel
theorem resProg_rk : resProg.regsOK fxU = true := by decide +kernel
theorem spStage_rk : spStage.regsOK fxU = true := by decide +kernel
theorem fbA_rk : fbA.regsOK fxU = true := by decide +kernel
theorem fbMid_rk : fbMid.regsOK fxU = true := by decide +kernel
theorem fbR_rk : fbR.regsOK fxU = true := by decide +kernel

/-- Klein's node, logged, names only registers `< 3100`. -/
theorem lgNode_rk : (lgS 2925 2926 nodeFullR).regsOK fxU = true :=
  lgS_regsOK (U := fun r => decide (r < 2920)) (fun r hr => by
      have : r < 2920 := by simpa using hr
      show decide (r < 3100) = true
      exact decide_eq_true (by omega)) (by decide) (by decide)
    nodeFullR nodeFullR_ok.1

/-! ### The fixed program -/

/-- The node step with the hoisted middle. -/
def nodeST (F : Stmt) : Stmt :=
  .seq ndFront (.ifLtN 2473 2486 ndNone (.seq ndBT (.ifLtN 2473 2496 F (.seq ndC resProg))))

/-- The full branch with the hoisted middle and end. -/
def FsT : Stmt :=
  .seq (.seq ndFront (.seq ndBT spStage)) (.seq fbA (.seq fbMid
    (.seq fbR (.seq (lgS 2925 2926 nodeFullR) fbOutT))))

/-- **The recursion's fixed program** (`Gt` read from `r3100`, `WN` from `r3101`). -/
def drvT : Stmt := driver testS lfT splitS0 (nodeST FsT)

/-- **The fixed program is the instance's program with its two constants put back.** -/
theorem drvT_eq (Gt WN : ℕ) :
    hsUn fxPB (fxV Gt WN) drvT = driver testS (leafS Gt) splitS0 (nodeS Gt (Fs WN Gt)) := by
  simp only [drvT, driver, body, nodeST, FsT, hsUn, lfT_eq, ndBT_eq, fbOutT_eq,
    hsUn_id _ testS_rk, hsUn_id _ splitS0_rk, hsUn_id _ peekB_rk, hsUn_id _ popB_rk,
    hsUn_id _ pushB_rk, hsUn_id _ coB_rk, hsUn_id _ coPost_rk, hsUn_id _ ndFront_rk,
    hsUn_id _ ndNone_rk, hsUn_id _ ndC_rk, hsUn_id _ resProg_rk, hsUn_id _ spStage_rk,
    hsUn_id _ fbA_rk, hsUn_id _ fbMid_rk, hsUn_id _ fbR_rk, hsUn_id _ lgNode_rk]
  rfl

/-- **The register condition of the fixed program.** -/
theorem drvT_ok : hsOK fxPB 2 drvT = true := by
  simp only [drvT, driver, body, nodeST, FsT, hsOK, lfT_ok, ndBT_ok, fbOutT_ok,
    hsOK_of_regsOK _ testS_rk, hsOK_of_regsOK _ splitS0_rk, hsOK_of_regsOK _ peekB_rk,
    hsOK_of_regsOK _ popB_rk, hsOK_of_regsOK _ pushB_rk, hsOK_of_regsOK _ coB_rk,
    hsOK_of_regsOK _ coPost_rk, hsOK_of_regsOK _ ndFront_rk, hsOK_of_regsOK _ ndNone_rk,
    hsOK_of_regsOK _ ndC_rk, hsOK_of_regsOK _ resProg_rk, hsOK_of_regsOK _ spStage_rk,
    hsOK_of_regsOK _ fbA_rk, hsOK_of_regsOK _ fbMid_rk, hsOK_of_regsOK _ fbR_rk,
    hsOK_of_regsOK _ lgNode_rk, Bool.and_true]
  decide

/-- **Transport**: a run of the instance's program from a configuration holding `Gt` in `r3100`
and `WN` in `r3101` is a run of the fixed program `drvT` (same configurations, same steps); the
registers `≥ 3100` are kept. -/
theorem drvT_exec {I : Input} {W Gt WN : ℕ} {c c' : Config} {t : ℕ}
    (h : Exec I W (driver testS (leafS Gt) splitS0 (nodeS Gt (Fs WN Gt))) c c' t)
    (h0 : c.nreg 3100 = Gt) (h1 : c.nreg 3101 = WN) :
    Exec I W drvT c c' t ∧ ∀ a, 3100 ≤ a → c'.nreg a = c.nreg a :=
  hs_exec' (drvT_eq Gt WN) h drvT_ok fun j hj => by
    interval_cases j
    · exact h0
    · exact h1

end NegSSSP

end PlanarFlow
