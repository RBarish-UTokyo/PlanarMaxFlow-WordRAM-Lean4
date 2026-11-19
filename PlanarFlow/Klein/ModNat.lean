module

public import PlanarFlow.Klein.ExecEnc
public import PlanarFlow.Klein.ProgTripMask
public import WordRAM.Machine.RealsModNat
public import WordRAM.Machine.KernelRfl

/-!
# Klein's programs meet the syntactic conditions of the simulation modulo `M`

`WordRAM.Machine.ModNat.ExecCmp.toNat` runs a statement on natural words, its integer reals
kept modulo `M`, when the statement names only registers `< R` and has no `divR`, and its run
is compare-bounded. The syntactic conditions hold for Klein's programs (checked by the kernel):

* `kleinProgM_regsOK`: the masked program `kleinProgM` names only the registers `< 201`
  (`kleinProg_regsOK` for the unmasked one);
* `kleinProg_noDivR`, `kleinProgM_noDivR`: neither uses `divR` (their real instructions are
  `constR`, `copyR`, `addR`, `subR`, `mulR`, `loadR`, `storeR`; their real tests are the
  conditional moves of the aggregates of the dynamic trees, `DynTree.cmov1`/`cmov2` in
  `DynTree.recompS`, and the comparison bit `DynTree.bitS` of the queries `min`/`min2`);
* `kleinProgMem_regsOK`, `kleinProgMem_noDivR`: the same for the program reading its encoding
  from memory (registers `< 202`).

The remaining condition, the bound of the compared differences along the run
(`WordRAM.Machine.ModNat.CmpOK`), is a property of the run, not of the program.
-/

@[expose] public section

namespace PlanarFlow

namespace Klein

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-- `kleinProg` uses no `divR` (checked by the kernel). -/
theorem kleinProg_noDivR (B nD n k t : ℕ) : (kleinProg B nD n k t).noDivR = true := by
  kernel_rfl

/-- `kleinProgM` names only the registers `< 201` (checked by the kernel). -/
theorem kleinProgM_regsOK (B nD n k t : ℕ) :
    (kleinProgM B nD n k t).regsOK (fun r => decide (r < 201)) = true := by
  kernel_rfl

/-- `kleinProgM` uses no `divR` (checked by the kernel). -/
theorem kleinProgM_noDivR (B nD n k t : ℕ) : (kleinProgM B nD n k t).noDivR = true := by
  kernel_rfl

/-- `kleinProgMem` names only the registers `< 202` (checked by the kernel). -/
theorem kleinProgMem_regsOK (B nD n k t β len : ℕ) :
    (kleinProgMem B nD n k t β len).regsOK (fun r => decide (r < 202)) = true := by
  kernel_rfl

/-- `kleinProgMem` uses no `divR` (checked by the kernel). -/
theorem kleinProgMem_noDivR (B nD n k t β len : ℕ) :
    (kleinProgMem B nD n k t β len).noDivR = true := by
  kernel_rfl

end Klein

end PlanarFlow
