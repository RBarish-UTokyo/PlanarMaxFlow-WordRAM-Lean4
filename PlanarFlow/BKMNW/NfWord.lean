module

public import PlanarFlow.BKMNW.Nf9aH
public import PlanarFlow.BKMNW.ThPipeV

/-!
# The subroutine programs of the maximum-flow program have no real instruction

`Klein.natOnly s`: the statement `s` has no real instruction and no real test. The maximum-flow
program `mfTopV` (`ThPipeV.lean`) is a word program when its five subroutine programs are
(`Pp.mfTopV_isWord`); this file checks them, in the pattern of the `noEmit` lemmas
(`Nf7dB.lean`, `Nf9aE.lean`, `Nf9bJ.lean`, `ThFinalB.lean`, `ThFinal.lean`): every closed piece
by `decide +kernel`, the program parameters by hypothesis.

* `sepL_natOnly`, `sepX_natOnly`: the separator programs;
* `fixP7_natOnly`, `F9b.fixC_natOnly`: the fix programs, given the MSSP call program;
* `Pp.msspCall'_msEnc_natOnly`: the MSSP call program with its encoder;
* `Pp.fzP_natOnly`, `Pp.c2sP_natOnly`, `Pp.s2cP_natOnly`: the frozen-fix wrapper and the two
  push programs.
-/

@[expose] public section

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv NcStep

/-- The separator program `sepL` has no real instruction. -/
theorem sepL_natOnly : Klein.natOnly MfDrv.sepL = true := by decide +kernel

/-- The separator program `sepX` has no real instruction. -/
theorem sepX_natOnly : Klein.natOnly MfDrv.sepX = true := by decide +kernel

/-- `fixP7 msP` has no real instruction when `msP` has none. -/
theorem fixP7_natOnly {msP : Stmt} (h : Klein.natOnly msP = true) :
    Klein.natOnly (fixP7 msP) = true := by
  have h1 : Klein.natOnly kTst = true := by decide +kernel
  have h2 : Klein.natOnly fpPro = true := by decide +kernel
  have h3 : Klein.natOnly p7cA = true := by decide +kernel
  have h4 : Klein.natOnly p7cM = true := by decide +kernel
  have h5 : Klein.natOnly p7cSv = true := by decide +kernel
  have h6 : Klein.natOnly p7cRs = true := by decide +kernel
  have h7 : Klein.natOnly st2b = true := by decide +kernel
  have h8 : Klein.natOnly st2c = true := by decide +kernel
  have h9 : Klein.natOnly p7dG = true := by decide +kernel
  have h10 : Klein.natOnly loopP = true := by decide +kernel
  have h11 : Klein.natOnly clrP = true := by decide +kernel
  have h12 : Klein.natOnly finP = true := by decide +kernel
  have h13 : Klein.natOnly fixZero = true := by decide +kernel
  simp only [fixP7, fixPos, st2, st2ab, st2a, Klein.natOnly, h, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, Bool.and_self]

namespace F9b

open NcFz

/-- `fixC msP` has no real instruction when `msP` has none. -/
theorem fixC_natOnly {msP : Stmt} (h : Klein.natOnly msP = true) :
    Klein.natOnly (fixC msP) = true := by
  have h1 : Klein.natOnly kTst = true := by decide +kernel
  have h2 : Klein.natOnly fpPro = true := by decide +kernel
  have h3 : Klein.natOnly p7cA = true := by decide +kernel
  have h4 : Klein.natOnly p7cM = true := by decide +kernel
  have h5 : Klein.natOnly p7cSv = true := by decide +kernel
  have h6 : Klein.natOnly p7cRs = true := by decide +kernel
  have h7 : Klein.natOnly st2b = true := by decide +kernel
  have h8 : Klein.natOnly st2c = true := by decide +kernel
  have h9 : Klein.natOnly p7dG = true := by decide +kernel
  have h10 : Klein.natOnly loopP = true := by decide +kernel
  have h11 : Klein.natOnly clrP = true := by decide +kernel
  have h12 : Klein.natOnly finP = true := by decide +kernel
  have h13 : Klein.natOnly fxZero = true := by decide +kernel
  have h14 : Klein.natOnly swB = true := by decide +kernel
  have h15 : Klein.natOnly qbP = true := by decide +kernel
  simp only [fixC, fxPos, st2, st2ab, st2a, Klein.natOnly, h, h1, h2, h3, h4, h5, h6, h7, h8,
    h9, h10, h11, h12, h13, h14, h15, Bool.and_self]

end F9b

namespace Pp

/-- The MSSP call with the encoder has no real instruction. -/
theorem msspCall'_msEnc_natOnly : Klein.natOnly (MsCall.msspCall' MsEnc.msEnc) = true :=
  MsCall.msspCall'_natOnly MsEnc.msEnc_natOnly

/-- `fzP fixC` has no real instruction when `fixC` has none. -/
theorem fzP_natOnly {fixC : Stmt} (h : Klein.natOnly fixC = true) :
    Klein.natOnly (NcFz.fzP fixC) = true := by
  have h1 : Klein.natOnly NcFz.pfP = true := by decide +kernel
  have h2 : Klein.natOnly NcFz.fxG = true := by decide +kernel
  have h3 : Klein.natOnly NcFz.cbP = true := by decide +kernel
  simp only [NcFz.fzP, Klein.natOnly, h, h1, h2, h3, Bool.and_self]

/-- `c2sP fzP pbP` has no real instruction when `fzP` has none. -/
theorem c2sP_natOnly {fzP : Stmt} (h : Klein.natOnly fzP = true) :
    Klein.natOnly (c2sP fzP pbP) = true := by
  simp only [c2sP, c2cP, c2tP, Klein.natOnly, h, pbP_natOnly, Bool.true_and]
  decide +kernel

/-- `s2cP fzP pbP` has no real instruction when `fzP` has none. -/
theorem s2cP_natOnly {fzP : Stmt} (h : Klein.natOnly fzP = true) :
    Klein.natOnly (s2cP fzP pbP) = true := by
  simp only [s2cP, c2cP, c2tP, Klein.natOnly, h, pbP_natOnly, Bool.true_and]
  decide +kernel

end Pp

end BKMNW

end PlanarFlow

end
