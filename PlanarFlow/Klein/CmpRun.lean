module

public import PlanarFlow.Klein.ProgPivot
public import PlanarFlow.DynTree.CmpRun

/-!
# Klein's algorithm on the machine: glue code in runs with bounded comparisons

`ORunC.ofGFr`: the glue rule `ORun.ofGFr` of `PlanarFlow/Klein/ProgPivot.lean` for the runs
whose real comparisons are bounded (`DynTree.ORunC`), for glue code without real tests.
-/

@[expose] public section

namespace PlanarFlow

namespace Klein

open DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt

section
variable {P : Input} {W H B n : ℕ}

/-- Glue code without real tests keeping the registers outside `[lo, hi)` (with `r151` outside),
the memory and the output performs no operation. -/
lemma ORunC.ofGFr {s : Stmt} {c c' : Config} {F : Forest} {G : List VT} {k lo hi : ℕ}
    (e : Exec P W s c c' k) (hS : LCTE B n F G c) (h : GFr lo hi c c')
    (h151 : 151 < lo ∨ hi ≤ 151) (hs : s.noTestR = true) :
    ORunC P W H B n s c F G c' [] G 0 k :=
  ORunC.of_noTestR (ORun.ofGFr e hS h h151) hs

end

end Klein

end PlanarFlow
