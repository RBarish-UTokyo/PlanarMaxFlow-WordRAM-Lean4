module

public import PlanarFlow.BKMNW.StMapF

/-!
# The map part of the s-t flow encoding at a max-flow call

At a call `x` of the max-flow recursion with its frame `Lay M gid u S T Z x m en d mem` (the `m`
darts of the piece map `pmap hP` numbered by increasing `gid`, the arrays `RV` at `d + 4 + m` and
`SG` at `d + 4 + 2m`), on a piece map with transitive faces and rotations:

* `lay_enumOKd`: the frame order is a dart order of the **dual** of the piece map as well;
* **`smP_lay`**: `smP` with `r7701 = d + 4 + m`, `r7702 = d + 4 + 2m` writes at `β` (above the
  scratch `[S', S' + 3m)`, itself above the frame's arrays) **Klein's encoding of the dual of the
  piece map with no piece** (`KInM`, so `Klein.KInput (pmap hP).dual ∅ 0` for any input holding
  these words, `KInM.kInput`), for the dart numbering `enEq` of the frame order and the node
  layout `smLayout` (`Klein.Layout (pmap hP).dual n …`, `4 m + 1 ≤ n`), within `140 m + 150`
  steps; the scratch zero again; memory outside the scratch and `[β, β + 12 m + 1)` kept;
  registers outside `SmScr` kept (so the driver's `3000 … 3012` and the step's `6800 … 6819`).

This is the map part of the input of the s-t flow program `PlanarFlow.STFlow.pcore_exec` for the
piece map of the call (`hL : Layout M.dual n ιF ιG ιV ιE`, `hK : KInput M.dual ∅ 0 σ …`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

open Finset Function CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  OrbLab NsStep MfDrv

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ} {mem : ℕ → ℕ}

/-- **The frame's dart order is a dart order of the dual of the piece map.** -/
theorem lay_enumOKd (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem)
    (hm : 0 < m) (hft : (pmap hP).FaceTrans) (hrt : (pmap hP).RotTrans) :
    EnumOK (pmap hP).dual (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm) m where
  inj := (lay_enumOK hP hl hm hft).inj
  surj := (lay_enumOK hP hl hm hft).surj
  fsurj v := Quotient.inductionOn v fun y => ⟨y, rfl⟩
  ft := NegSSSP.dual_faceTrans hrt

variable {P : Input} {W : ℕ}

/-- **The map part of the s-t flow encoding at a max-flow call** (see the module docstring). -/
theorem smP_lay (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hft : (pmap hP).FaceTrans)
    (hrt : (pmap hP).RotTrans) (c : Config) (hc : WordsBounded W c)
    (hl : Lay M gid u S T Z x m en d c.nmem) (hm : 0 < m) {S' β : ℕ}
    (r00 : c.nreg 7700 = m) (r01 : c.nreg 7701 = d + 4 + m) (r02 : c.nreg 7702 = d + 4 + 2 * m)
    (r03 : c.nreg 7703 = S') (r04 : c.nreg 7704 = β)
    (l1 : d + 4 + 3 * m ≤ S') (l3 : S' + 3 * m ≤ β) (w : β + 12 * m + 1 ≤ W) :
    ∃ c' t, Exec P W smP c c' t ∧ t ≤ 140 * m + 150 ∧
      KInM (pmap hP).dual (enEq (lay_enumOK hP hl hm hft))
        (ιF (pmap hP) (lay_enumOK hP hl hm hft)) (ιG (pmap hP) (lay_enumOK hP hl hm hft))
        (ιV (pmap hP) (lay_enumOKd hP hl hm hft hrt)) (ιE (pmap hP) (lay_enumOK hP hl hm hft))
        c'.nmem β ∧
      (∀ i < 3 * m, c'.nmem (S' + i) = 0) ∧
      (∀ a, ¬ (S' ≤ a ∧ a < S' + 3 * m) → ¬ (β ≤ a ∧ a < β + 12 * m + 1) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ SmScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  smP_kin (lay_enumOK hP hl hm hft) (lay_enumOKd hP hl hm hft hrt) c hc r00 r01 r02 r03 r04
    (fun i hi => lay_rv hP hl hm hft hi) (fun i hi => lay_rt hP hl hm hft hi) (by omega)
    (by omega) l3 w

/-- **The node layout at a call** (`4 m + 1 ≤ n`). -/
theorem smLayout_lay (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hft : (pmap hP).FaceTrans)
    (hrt : (pmap hP).RotTrans) (hl : Lay M gid u S T Z x m en d mem) (hm : 0 < m) {n : ℕ}
    (hn : 4 * m + 1 ≤ n) :
    Klein.Layout (pmap hP).dual n (ιF (pmap hP) (lay_enumOK hP hl hm hft))
      (ιG (pmap hP) (lay_enumOK hP hl hm hft)) (ιV (pmap hP) (lay_enumOKd hP hl hm hft hrt))
      (ιE (pmap hP) (lay_enumOK hP hl hm hft)) :=
  smLayout _ _ hn

/-- The nodes of the cotree edges are below `4 m + 1`. -/
lemma ιE_lt (h : EnumOK M en m) (e : D) : ιE M h e < 4 * m + 1 := by
  have := NegSSSP.eIx_lt (M := M) (enEq h) e
  unfold ιE; omega

end StEnc

end BKMNW

end PlanarFlow
