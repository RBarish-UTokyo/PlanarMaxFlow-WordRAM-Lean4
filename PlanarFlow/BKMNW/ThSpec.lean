module

public import PlanarFlow.BKMNW.NcSpec
public import PlanarFlow.BKMNW.NcPar
public import PlanarFlow.BKMNW.NpNode

/-!
# The node-step specifications with the start vertices of the parts and the zero-area bound

The step chain (`stepPO_specN`, `stepX_spec`) gives the subroutine programs the parts of the
separator as **`SegsAt`** (`SegsOut` from `r6807`: the darts of each part only) and the zero
memory `MemZ Wz` with only `Wz < d`. Two gaps: a part with `k = 0` (a single vertex) is
recorded nowhere, and `c2sP` cannot place the zero area of its s-t flow call (`stCallZ` needs a
base `ib` with `pstWN … < ib`, `ib + pstWN … ≤ Wz`), since nothing bounds `Wz` from below. Here
the specifications are restated with

* **`SegsAt'`** (`NcPar.lean`: `SegsOut'` from `r6807`, the parts **with their start vertices**)
  in place of `SegsAt`, in the precondition of every node-step subroutine;
* **the zero-area bound `wzc m Z ≤ Wz`** for a function `wzc` fixed by the subroutine programs
  (`m` the number of darts of the piece, read from the frame: `mem d = m`, `mem (d + 3) = Z`), so
  that a program can compute a base in the zero area from `m` and `Z` alone (the
  chain asks `wzc m Z ≤ Wz` for every `m ≤ N`).

Definitions:
* **`SegPSpec'`** (`SegPSpec` writing `SegsAt'`), `SegPSpec'.toSegPSpec`;
* **`CntPSpecS'`** (`CntPSpecS` with `SegsAt'`), `CntPSpecS.toS'`;
* **`FixPSpecN'`, `RetPSpecN'`, `FrmPSpecN'`** (with `SegsAt'` and `wzc m Z ≤ Wz`);
* **`C2SPSpecNA`, `S2CPSpecNA`** (`C2SPSpecN`/`S2CPSpecN` with `SegsAt'` and `wzc m Z ≤ Wz`) and
  **`C2SPSpecN''`, `S2CPSpecN''`** (the same plus the hole invariants `HoleC2S`/`HoleS2C` of
  `C2SPSpecN'`/`S2CPSpecN'`); `C2SPSpecN''.toNA`, `S2CPSpecN''.toNA` (the hole invariants
  hold at the reachable calls);
* **`StepPSpecCS'`** (`StepPSpecCS` with `SegsAt'` and `wzc m Z ≤ Wz`);
* the old specifications give the new ones (`FixPSpecN.toN'`, `C2SPSpecN.toNA`,
  `C2SPSpecN'.toN''`, …): the new ones only add hypotheses.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs NegSSSP.Driver NcStep

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- `SegsAt'` forgets to `SegsAt`. -/
lemma SegsAt'.toSegsAt {en : ℕ → D} {m : ℕ} {π : HSep M} {e b : ℕ} {c : Config}
    (h : SegsAt' M en m π e b c) : SegsAt M en m π e b c := h.1

/-- `SegsAt'` depends only on `r6807` and the memory in `[e, b)`. -/
lemma SegsAt'.congr {en : ℕ → D} {m : ℕ} {π : HSep M} {e b : ℕ} {c c' : Config}
    (h : SegsAt' M en m π e b c) (hr : c'.nreg 6807 = c.nreg 6807)
    (he : ∀ a, e ≤ a → a < b → c'.nmem a = c.nmem a) : SegsAt' M en m π e b c' := by
  unfold SegsAt' at h ⊢
  rw [hr]
  exact h.congr fun a h1 h2 => he a (by have := h.1.1; omega) h2

section Spec

variable (M) in
/-- **`SegPSpec` with the start vertices of the parts**: the program run at the node writes
`SegsAt'` (the parts with their start vertices) in `[e, b')`. -/
def SegPSpec' (ds : DSys M) (Reach : MCall M → Prop) (gid : D → ℕ) (ν : V → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (segP : Stmt) (sgT sgR : MCall M → ℕ) :
    Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e b m : ℕ)
    (en : ℕ → D) (c : Config),
    FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem → d + fsz m ≤ e → e ≤ b →
    b + sgR (.node l r π, Hs, σ) ≤ W → WordsBounded W c → c.nreg 3004 = d →
    c.nreg 3005 = e → c.nreg 3006 = b + 5 →
    ∃ c' t b', Exec I W segP c c' t ∧ t ≤ sgT (.node l r π, Hs, σ) ∧ b ≤ b' ∧
      b' ≤ b + sgR (.node l r π, Hs, σ) ∧
      (∀ x, 3000 ≤ x → x ≤ 3012 → x ≠ 3006 → c'.nreg x = c.nreg x) ∧
      c'.nreg 3006 = b' + 5 ∧ c'.nreg 6808 = b + 5 ∧
      (∀ a, a < b → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      SegsAt' M en m π e b' c'

variable (M) in
/-- **`CntPSpecS` with the start vertices** (`SegsAt'` in place of `SegsAt`). -/
def CntPSpecS' (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ)
    (I : Input) (W : ℕ) (cntP : Stmt) (cnT rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e b m : ℕ)
    (en : ℕ → D) (c : Config),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem → SegsAt' M en m π e b c →
    d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → WordsBounded W c → c.nreg 3004 = d →
    c.nreg 3005 = e → c.nreg 3006 = b + 5 →
    ∃ c' t, Exec I W cntP c c' t ∧ t ≤ cnT (.node l r π, Hs, σ) ∧
      DRegKeep c c' ∧
      (∀ a, a < b → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ x, 6807 ≤ x → x ≤ 6819 → c'.nreg x = c.nreg x) ∧ c'.nreg 6801 = π.segs.length ∧
      c'.nreg 6806 = (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length + π.segs.length

variable (M) in
/-- **FixConservationOnPath on the part `j`** (`FixPSpecN`) with the start vertices of the parts
(`SegsAt'`) and the zero-area bound `wzc m Z ≤ Wz`. -/
def FixPSpecN' (NF : NFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (wzc : ℕ → ℕ → ℕ) (fixP : Stmt)
    (fT : MCall M → ℕ → ℕ) (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j : ℕ) (πj : SPath (pmap h.1)),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d → wzc m Z ≤ Wz →
    (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj →
    FlowProg M gid u S T Z I W fixP (.node l r π, Hs, σ) m en d e b
      (fun c => (c.nreg 6800 = j ∧ MemZ Wz c) ∧ SegsAt' M en m π e b c)
      ((xCtxN M NF u S T l r π Hs σ h).seg j)
      ((xCtxN M NF u S T l r π Hs σ h).O.fix (xCtxN M NF u S T l r π Hs σ h).U
        ((xCtxN M NF u S T l r π Hs σ h).seg j) πj) (fT (.node l r π, Hs, σ) j)

variable (M) in
/-- **CycleToSingleSinkLimitedMaxFlow on the hole `i` of the part `j`** (`C2SPSpecN`) with the
start vertices of the parts (`SegsAt'`) and the zero-area bound `wzc m Z ≤ Wz` (no hole
invariant; see `C2SPSpecN''`). -/
def C2SPSpecNA (NF : NFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (wzc : ℕ → ℕ → ℕ) (c2sP : Stmt)
    (cT : MCall M → ℕ → ℕ → ℕ) (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j i : ℕ) (πj : SPath (pmap h.1))
    (H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d → wzc m Z ≤ Wz →
    (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj →
    ((xCtxN M NF u S T l r π Hs σ h).holes j)[i]? = some H →
    FlowProg M gid u S T Z I W c2sP (.node l r π, Hs, σ) m en d e b
      (fun c => ((c.nreg 6800 = j ∧ c.nreg 6802 = i) ∧ MemZ Wz c) ∧ SegsAt' M en m π e b c)
      ((xCtxN M NF u S T l r π Hs σ h).hole j πj i)
      ((xCtxN M NF u S T l r π Hs σ h).c2s j πj i H) (cT (.node l r π, Hs, σ) j i)

variable (M) in
/-- **SingleSourceToCycleLimitedMaxFlow on the hole `i` of the part `j`** (`S2CPSpecN`) with the
start vertices of the parts (`SegsAt'`) and the zero-area bound `wzc m Z ≤ Wz` (no hole
invariant; see `S2CPSpecN''`). -/
def S2CPSpecNA (NF : NFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (wzc : ℕ → ℕ → ℕ) (s2cP : Stmt)
    (sT : MCall M → ℕ → ℕ → ℕ) (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j i : ℕ) (πj : SPath (pmap h.1))
    (H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d → wzc m Z ≤ Wz →
    (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj →
    ((xCtxN M NF u S T l r π Hs σ h).holes j)[i]? = some H →
    FlowProg M gid u S T Z I W s2cP (.node l r π, Hs, σ) m en d e b
      (fun c => ((c.nreg 6800 = j ∧ c.nreg 6802 = i) ∧ MemZ Wz c) ∧ SegsAt' M en m π e b c)
      ((xCtxN M NF u S T l r π Hs σ h).c2s j πj i H)
      ((xCtxN M NF u S T l r π Hs σ h).O.s2c (xCtxN M NF u S T l r π Hs σ h).U
        ((xCtxN M NF u S T l r π Hs σ h).c2s j πj i H) πj H) (sT (.node l r π, Hs, σ) j i)

variable (M) in
/-- **CycleToSingleSinkLimitedMaxFlow on the hole `i` of the part `j`, with everything a machine
program needs**: the step invariants at the hole flow (`HoleC2S`, as in `C2SPSpecN'`), the parts
with their start vertices (`SegsAt'`) and the zero-area bound `wzc m Z ≤ Wz`. -/
def C2SPSpecN'' (NF : NFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (wzc : ℕ → ℕ → ℕ) (c2sP : Stmt)
    (cT : MCall M → ℕ → ℕ → ℕ) (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j i : ℕ) (πj : SPath (pmap h.1))
    (H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d → wzc m Z ≤ Wz →
    (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj →
    ((xCtxN M NF u S T l r π Hs σ h).holes j)[i]? = some H →
    HoleC2S (pmap h.1) (xCtxN M NF u S T l r π Hs σ h).U
      ((xCtxN M NF u S T l r π Hs σ h).hole j πj i) πj H →
    FlowProg M gid u S T Z I W c2sP (.node l r π, Hs, σ) m en d e b
      (fun c => ((c.nreg 6800 = j ∧ c.nreg 6802 = i) ∧ MemZ Wz c) ∧ SegsAt' M en m π e b c)
      ((xCtxN M NF u S T l r π Hs σ h).hole j πj i)
      ((xCtxN M NF u S T l r π Hs σ h).c2s j πj i H) (cT (.node l r π, Hs, σ) j i)

variable (M) in
/-- **SingleSourceToCycleLimitedMaxFlow on the hole `i` of the part `j`, with everything a machine
program needs**: the step invariants at the flow after `c2s` (`HoleS2C`, as in `S2CPSpecN'`), the
parts with their start vertices (`SegsAt'`) and the zero-area bound `wzc m Z ≤ Wz`. -/
def S2CPSpecN'' (NF : NFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (wzc : ℕ → ℕ → ℕ) (s2cP : Stmt)
    (sT : MCall M → ℕ → ℕ → ℕ) (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j i : ℕ) (πj : SPath (pmap h.1))
    (H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d → wzc m Z ≤ Wz →
    (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj →
    ((xCtxN M NF u S T l r π Hs σ h).holes j)[i]? = some H →
    HoleS2C (pmap h.1) (xCtxN M NF u S T l r π Hs σ h).U
      ((xCtxN M NF u S T l r π Hs σ h).c2s j πj i H) πj H →
    FlowProg M gid u S T Z I W s2cP (.node l r π, Hs, σ) m en d e b
      (fun c => ((c.nreg 6800 = j ∧ c.nreg 6802 = i) ∧ MemZ Wz c) ∧ SegsAt' M en m π e b c)
      ((xCtxN M NF u S T l r π Hs σ h).c2s j πj i H)
      ((xCtxN M NF u S T l r π Hs σ h).O.s2c (xCtxN M NF u S T l r π Hs σ h).U
        ((xCtxN M NF u S T l r π Hs σ h).c2s j πj i H) πj H) (sT (.node l r π, Hs, σ) j i)

variable (M) in
/-- **The push-back of the excess to the sources** on the part `j` (`RetPSpecN`) with the start
vertices of the parts (`SegsAt'`) and the zero-area bound `wzc m Z ≤ Wz`. -/
def RetPSpecN' (NF : NFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (wzc : ℕ → ℕ → ℕ) (retP : Stmt)
    (rtT : MCall M → ℕ → ℕ) (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j : ℕ) (πj : SPath (pmap h.1)),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d → wzc m Z ≤ Wz →
    (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj →
    FlowProg M gid u S T Z I W retP (.node l r π, Hs, σ) m en d e b
      (fun c => (c.nreg 6800 = j ∧ MemZ Wz c) ∧ SegsAt' M en m π e b c)
      ((xCtxN M NF u S T l r π Hs σ h).hole j πj ((xCtxN M NF u S T l r π Hs σ h).holes j).length)
      ((xCtxN M NF u S T l r π Hs σ h).ret j πj) (rtT (.node l r π, Hs, σ) j)

variable (M) in
/-- **The push-back from the sinks** on the part `j` (`FrmPSpecN`) with the start vertices of the
parts (`SegsAt'`) and the zero-area bound `wzc m Z ≤ Wz`. -/
def FrmPSpecN' (NF : NFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (wzc : ℕ → ℕ → ℕ) (frmP : Stmt)
    (fmT : MCall M → ℕ → ℕ) (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j : ℕ) (πj : SPath (pmap h.1)),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d → wzc m Z ≤ Wz →
    (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj →
    FlowProg M gid u S T Z I W frmP (.node l r π, Hs, σ) m en d e b
      (fun c => (c.nreg 6800 = j ∧ MemZ Wz c) ∧ SegsAt' M en m π e b c)
      ((xCtxN M NF u S T l r π Hs σ h).ret j πj)
      ((xCtxN M NF u S T l r π Hs σ h).O.frm (xCtxN M NF u S T l r π Hs σ h).U
        ((xCtxN M NF u S T l r π Hs σ h).ret j πj) (xCtxN M NF u S T l r π Hs σ h).T
        (negSet (pmap h.1) ((xCtxN M NF u S T l r π Hs σ h).ret j πj) πj.verts))
      (fmT (.node l r π, Hs, σ) j)

variable (M) in
/-- **The step with the parts and their start vertices and the zero-area bound**:
`StepPSpecCS` with `SegsAt'` and `wzc m Z ≤ Wz`. -/
def StepPSpecCS' (cf : CFlow M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (wzc : ℕ → ℕ → ℕ) (stepP : Stmt)
    (stT rT : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e b m : ℕ)
    (en : ℕ → D) (c : Config),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem → SegsAt' M en m π e b c →
    d + fsz m ≤ e →
    (∀ i < m, (c.nmem (d + 4 + 6 * m + i) : ℤ) =
      Z + fext (joinFlow (B := pdarts M (l.piece ∪ r.piece) Hs)
        (cf (chL M l r π Hs σ)) (cf (chR M l r π Hs σ))) (en i)) →
    WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = b + 5 → e ≤ b →
    b + rT (.node l r π, Hs, σ) ≤ W → Wz < d → wzc m Z ≤ Wz → MemZ Wz c →
    ∃ c' t, Exec I W stepP c c' t ∧ t ≤ stT (.node l r π, Hs, σ) ∧ DRegKeep c c' ∧
      (∀ x, 6807 ≤ x → x ≤ 6819 → c'.nreg x = c.nreg x) ∧
      (∀ a, a < b → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      ∀ i < m, (c'.nmem (d + 4 + 6 * m + i) : ℤ) =
        Z + fext (cf (.node l r π, Hs, σ)) (en i)

end Spec

section Conv

variable {ds : DSys M} {Reach : MCall M → Prop} {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ}
  {S T : Finset V} {Z : ℕ} {I : Input} {W Wz : ℕ} {wzc : ℕ → ℕ → ℕ} {NF : NFam M}
  {segP cntP fixP c2sP s2cP retP frmP : Stmt} {sgT sgR cnT rO : MCall M → ℕ}
  {fT rtT fmT : MCall M → ℕ → ℕ} {cT sT : MCall M → ℕ → ℕ → ℕ}

/-- **The primed parts' program gives the unprimed one** (forgetting the start vertices). -/
theorem SegPSpec'.toSegPSpec (h : SegPSpec' M ds Reach gid ν u S T Z I W segP sgT sgR) :
    SegPSpec M ds Reach gid ν u S T Z I W segP sgT sgR := by
  intro l r π Hs σ d e b m en c h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨c', t, b', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ :=
    h l r π Hs σ d e b m en c h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨c', t, b', a1, a2, a3, a4, a5, a6, a7, a8, a9, (SegsAt'.toSegsAt a10)⟩

/-- The counts' specification with `SegsAt` gives the one with `SegsAt'`. -/
theorem CntPSpecS.toS' (h : CntPSpecS M Reach gid u S T Z I W cntP cnT rO) :
    CntPSpecS' M Reach gid u S T Z I W cntP cnT rO :=
  fun l r π Hs σ d e b m en c h1 h2 h3 h4 =>
    h l r π Hs σ d e b m en c h1 h2 h3 (SegsAt'.toSegsAt h4)

/-- A `FlowProg` for a precondition gives one for any stronger precondition. -/
lemma FlowProg.mono_pre {p : Stmt} {x : MCall M} {m : ℕ} {en : ℕ → D} {d e b : ℕ}
    {pre pre' : Config → Prop} {B : Finset D} {gin gout : SDart B → ℤ} {t : ℕ}
    (h : FlowProg M gid u S T Z I W p x m en d e b pre gin gout t)
    (hp : ∀ c, pre' c → pre c) : FlowProg M gid u S T Z I W p x m en d e b pre' gin gout t :=
  fun c hc => h c (hp c hc)

theorem FixPSpecN.toN' (h : FixPSpecN M NF Reach gid u S T Z I W Wz fixP fT rO) :
    FixPSpecN' M NF Reach gid u S T Z I W Wz wzc fixP fT rO :=
  fun l r π Hs σ hs d e b m en j πj a1 a2 a3 a4 a5 a6 _ a7 =>
    (h l r π Hs σ hs d e b m en j πj a1 a2 a3 a4 a5 a6 a7).mono_pre
      fun _ hc => ⟨hc.1, (SegsAt'.toSegsAt hc.2)⟩

theorem C2SPSpecN.toNA (h : C2SPSpecN M NF Reach gid u S T Z I W Wz c2sP cT rO) :
    C2SPSpecNA M NF Reach gid u S T Z I W Wz wzc c2sP cT rO :=
  fun l r π Hs σ hs d e b m en j i πj H a1 a2 a3 a4 a5 a6 _ a7 a8 =>
    (h l r π Hs σ hs d e b m en j i πj H a1 a2 a3 a4 a5 a6 a7 a8).mono_pre
      fun _ hc => ⟨hc.1, (SegsAt'.toSegsAt hc.2)⟩

theorem S2CPSpecN.toNA (h : S2CPSpecN M NF Reach gid u S T Z I W Wz s2cP sT rO) :
    S2CPSpecNA M NF Reach gid u S T Z I W Wz wzc s2cP sT rO :=
  fun l r π Hs σ hs d e b m en j i πj H a1 a2 a3 a4 a5 a6 _ a7 a8 =>
    (h l r π Hs σ hs d e b m en j i πj H a1 a2 a3 a4 a5 a6 a7 a8).mono_pre
      fun _ hc => ⟨hc.1, (SegsAt'.toSegsAt hc.2)⟩

theorem C2SPSpecN'.toN'' (h : C2SPSpecN' M NF Reach gid u S T Z I W Wz c2sP cT rO) :
    C2SPSpecN'' M NF Reach gid u S T Z I W Wz wzc c2sP cT rO :=
  fun l r π Hs σ hs d e b m en j i πj H a1 a2 a3 a4 a5 a6 _ a7 a8 a9 =>
    (h l r π Hs σ hs d e b m en j i πj H a1 a2 a3 a4 a5 a6 a7 a8 a9).mono_pre
      fun _ hc => ⟨hc.1, (SegsAt'.toSegsAt hc.2)⟩

theorem S2CPSpecN'.toN'' (h : S2CPSpecN' M NF Reach gid u S T Z I W Wz s2cP sT rO) :
    S2CPSpecN'' M NF Reach gid u S T Z I W Wz wzc s2cP sT rO :=
  fun l r π Hs σ hs d e b m en j i πj H a1 a2 a3 a4 a5 a6 _ a7 a8 a9 =>
    (h l r π Hs σ hs d e b m en j i πj H a1 a2 a3 a4 a5 a6 a7 a8 a9).mono_pre
      fun _ hc => ⟨hc.1, (SegsAt'.toSegsAt hc.2)⟩

theorem RetPSpecN.toN' (h : RetPSpecN M NF Reach gid u S T Z I W Wz retP rtT rO) :
    RetPSpecN' M NF Reach gid u S T Z I W Wz wzc retP rtT rO :=
  fun l r π Hs σ hs d e b m en j πj a1 a2 a3 a4 a5 a6 _ a7 =>
    (h l r π Hs σ hs d e b m en j πj a1 a2 a3 a4 a5 a6 a7).mono_pre
      fun _ hc => ⟨hc.1, (SegsAt'.toSegsAt hc.2)⟩

theorem FrmPSpecN.toN' (h : FrmPSpecN M NF Reach gid u S T Z I W Wz frmP fmT rO) :
    FrmPSpecN' M NF Reach gid u S T Z I W Wz wzc frmP fmT rO :=
  fun l r π Hs σ hs d e b m en j πj a1 a2 a3 a4 a5 a6 _ a7 =>
    (h l r π Hs σ hs d e b m en j πj a1 a2 a3 a4 a5 a6 a7).mono_pre
      fun _ hc => ⟨hc.1, (SegsAt'.toSegsAt hc.2)⟩

/-- **The `c2s` specification with the hole invariants gives the one without** at the reachable
calls (the invariants hold there: `holeInvN_of_callOk`). -/
theorem C2SPSpecN''.toNA (hu : ∀ d, 0 ≤ u d) (hST : Disjoint S T) (hO : NSpecOn M NF Reach)
    (hR : ∀ x y, Reach x → Calls M x.1 x.2.1 x.2.2 y → Reach y)
    (h' : C2SPSpecN'' M NF Reach gid u S T Z I W Wz wzc c2sP cT rO) :
    C2SPSpecNA M NF Reach gid u S T Z I W Wz wzc c2sP cT rO :=
  fun l r π Hs σ h d e b m en j i πj H hx hok hde heb hroom hWd hwz hj hi =>
    h' l r π Hs σ h d e b m en j i πj H hx hok hde heb hroom hWd hwz hj hi
      (holeInvN_of_callOk NF hu hST (nSpecOn_calls hO hR hx) hok h j i πj H hj hi).1

/-- **The `s2c` specification with the hole invariants gives the one without** at the reachable
calls. -/
theorem S2CPSpecN''.toNA (hu : ∀ d, 0 ≤ u d) (hST : Disjoint S T) (hO : NSpecOn M NF Reach)
    (hR : ∀ x y, Reach x → Calls M x.1 x.2.1 x.2.2 y → Reach y)
    (h' : S2CPSpecN'' M NF Reach gid u S T Z I W Wz wzc s2cP sT rO) :
    S2CPSpecNA M NF Reach gid u S T Z I W Wz wzc s2cP sT rO :=
  fun l r π Hs σ h d e b m en j i πj H hx hok hde heb hroom hWd hwz hj hi =>
    h' l r π Hs σ h d e b m en j i πj H hx hok hde heb hroom hWd hwz hj hi
      (holeInvN_of_callOk NF hu hST (nSpecOn_calls hO hR hx) hok h j i πj H hj hi).2

end Conv

end MfDrv

end BKMNW

end PlanarFlow
