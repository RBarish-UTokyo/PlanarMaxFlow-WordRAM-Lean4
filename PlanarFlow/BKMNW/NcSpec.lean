module

public import PlanarFlow.BKMNW.NcHoleN

/-!
# The primed specifications of `c2sP`/`s2cP` with the step invariants at the holes

`C2SPSpecN`/`S2CPSpecN` ask a program to compute `c2s`/`s2c` at every hole of a reachable node
call with no precondition on the hole flow, while any machine program needs the bounds that the
step invariants give (the flow a pseudoflow, the part off the hole, the hole a path, the
precondition of `c2sG_spec`). Here:

* **`C2SPSpecN'`, `S2CPSpecN'`**: the specifications with the extra hypotheses `HoleC2S` (at the
  hole flow `hole j πj i`) and `HoleS2C` (at `c2s j πj i H`);
* `holeInvN_of_callOk` (the invariants at a node call from `CallOk` and `NSpecOn` on its calls);
* **`C2SPSpecN'.toN`, `S2CPSpecN'.toN`**: a primed specification gives the unprimed one when the
  subroutines meet their specifications at the reachable calls (`NSpecOn M NF Reach`), `Reach` is
  closed under the calls of its calls, the capacities are nonnegative and `S`, `T` disjoint;
* **`stepPO_specN'`**: `stepPO_specN` with the primed specifications.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **CycleToSingleSinkLimitedMaxFlow on the hole `i` of the part `j`**, with the step invariants
at the hole flow (`HoleC2S`) as a precondition (otherwise `C2SPSpecN`). -/
def C2SPSpecN' (NF : NFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (c2sP : Stmt) (cT : MCall M → ℕ → ℕ → ℕ)
    (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j i : ℕ) (πj : SPath (pmap h.1))
    (H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d →
    (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj →
    ((xCtxN M NF u S T l r π Hs σ h).holes j)[i]? = some H →
    HoleC2S (pmap h.1) (xCtxN M NF u S T l r π Hs σ h).U
      ((xCtxN M NF u S T l r π Hs σ h).hole j πj i) πj H →
    FlowProg M gid u S T Z I W c2sP (.node l r π, Hs, σ) m en d e b
      (fun c => ((c.nreg 6800 = j ∧ c.nreg 6802 = i) ∧ MemZ Wz c) ∧ SegsAt M en m π e b c)
      ((xCtxN M NF u S T l r π Hs σ h).hole j πj i)
      ((xCtxN M NF u S T l r π Hs σ h).c2s j πj i H) (cT (.node l r π, Hs, σ) j i)

variable (M) in
/-- **SingleSourceToCycleLimitedMaxFlow on the hole `i` of the part `j`**, with the step
invariants at the flow after `c2s` (`HoleS2C`) as a precondition (otherwise `S2CPSpecN`). -/
def S2CPSpecN' (NF : NFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (s2cP : Stmt) (sT : MCall M → ℕ → ℕ → ℕ)
    (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j i : ℕ) (πj : SPath (pmap h.1))
    (H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d →
    (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj →
    ((xCtxN M NF u S T l r π Hs σ h).holes j)[i]? = some H →
    HoleS2C (pmap h.1) (xCtxN M NF u S T l r π Hs σ h).U
      ((xCtxN M NF u S T l r π Hs σ h).c2s j πj i H) πj H →
    FlowProg M gid u S T Z I W s2cP (.node l r π, Hs, σ) m en d e b
      (fun c => ((c.nreg 6800 = j ∧ c.nreg 6802 = i) ∧ MemZ Wz c) ∧ SegsAt M en m π e b c)
      ((xCtxN M NF u S T l r π Hs σ h).c2s j πj i H)
      ((xCtxN M NF u S T l r π Hs σ h).O.s2c (xCtxN M NF u S T l r π Hs σ h).U
        ((xCtxN M NF u S T l r π Hs σ h).c2s j πj i H) πj H) (sT (.node l r π, Hs, σ) j i)

/-- **The step invariants at the holes of a node call with the invariants `CallOk`**, when the
subroutines meet their specifications at its calls. -/
theorem holeInvN_of_callOk (NF : NFam M) {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V}
    (hST : Disjoint S T) {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    (hO : NSpecOn M NF (Calls M (.node l r π) Hs σ))
    (hok : CallOk M S T (.node l r π, Hs, σ)) : HoleInvN M NF u S T l r π Hs σ :=
  arunLN_holeInv_node NF hu hST l r π Hs σ hO hok.1 hok.2.1 hok.2.2.1 hok.2.2.2.1
    hok.2.2.2.2.1 hok.2.2.2.2.2.1

/-- `NSpecOn` passes to the calls of a reachable call when `Reach` is closed under them. -/
lemma nSpecOn_calls {NF : NFam M} {Reach : MCall M → Prop} (hO : NSpecOn M NF Reach)
    (hR : ∀ x y, Reach x → Calls M x.1 x.2.1 x.2.2 y → Reach y) {x : MCall M} (hx : Reach x) :
    NSpecOn M NF (Calls M x.1 x.2.1 x.2.2) :=
  fun y hy => hO y (hR x y hx hy)

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {I : Input} {W Wz : ℕ}
  {NF : NFam M} {Reach : MCall M → Prop}

/-- **A primed `c2s` specification gives the unprimed one** at the reachable calls. -/
theorem C2SPSpecN'.toN {c2sP : Stmt} {cT : MCall M → ℕ → ℕ → ℕ} {rO : MCall M → ℕ}
    (hu : ∀ d, 0 ≤ u d) (hST : Disjoint S T) (hO : NSpecOn M NF Reach)
    (hR : ∀ x y, Reach x → Calls M x.1 x.2.1 x.2.2 y → Reach y)
    (h' : C2SPSpecN' M NF Reach gid u S T Z I W Wz c2sP cT rO) :
    C2SPSpecN M NF Reach gid u S T Z I W Wz c2sP cT rO :=
  fun l r π Hs σ h d e b m en j i πj H hx hok hde heb hroom hWd hj hi =>
    h' l r π Hs σ h d e b m en j i πj H hx hok hde heb hroom hWd hj hi
      (holeInvN_of_callOk NF hu hST (nSpecOn_calls hO hR hx) hok h j i πj H hj hi).1

/-- **A primed `s2c` specification gives the unprimed one** at the reachable calls. -/
theorem S2CPSpecN'.toN {s2cP : Stmt} {sT : MCall M → ℕ → ℕ → ℕ} {rO : MCall M → ℕ}
    (hu : ∀ d, 0 ≤ u d) (hST : Disjoint S T) (hO : NSpecOn M NF Reach)
    (hR : ∀ x y, Reach x → Calls M x.1 x.2.1 x.2.2 y → Reach y)
    (h' : S2CPSpecN' M NF Reach gid u S T Z I W Wz s2cP sT rO) :
    S2CPSpecN M NF Reach gid u S T Z I W Wz s2cP sT rO :=
  fun l r π Hs σ h d e b m en j i πj H hx hok hde heb hroom hWd hj hi =>
    h' l r π Hs σ h d e b m en j i πj H hx hok hde heb hroom hWd hj hi
      (holeInvN_of_callOk NF hu hST (nSpecOn_calls hO hR hx) hok h j i πj H hj hi).2

/-- **The step program with the primed specifications of `c2sP` and `s2cP`** meets
`StepPSpecCS` (`stepPO_specN` through `C2SPSpecN'.toN`, `S2CPSpecN'.toN`). -/
theorem stepPO_specN' {cntP fixP c2sP s2cP retP frmP : Stmt} {cnT rO : MCall M → ℕ}
    {fT rtT fmT : MCall M → ℕ → ℕ} {cT sT : MCall M → ℕ → ℕ → ℕ}
    (hu : ∀ d, 0 ≤ u d) (hST : Disjoint S T) (hO : NSpecOn M NF Reach)
    (hR : ∀ x y, Reach x → Calls M x.1 x.2.1 x.2.2 y → Reach y)
    (hcn : CntPSpecS M Reach gid u S T Z I W cntP cnT rO)
    (hfx : FixPSpecN M NF Reach gid u S T Z I W Wz fixP fT rO)
    (hc2 : C2SPSpecN' M NF Reach gid u S T Z I W Wz c2sP cT rO)
    (hs2 : S2CPSpecN' M NF Reach gid u S T Z I W Wz s2cP sT rO)
    (hrt : RetPSpecN M NF Reach gid u S T Z I W Wz retP rtT rO)
    (hfm : FrmPSpecN M NF Reach gid u S T Z I W Wz frmP fmT rO) :
    StepPSpecCS M (cflowN M NF u S T) Reach gid u S T Z I W Wz
      (stepPO cntP fixP c2sP s2cP retP frmP) (stTO M cnT fT cT sT rtT fmT) rO :=
  stepPO_specN hcn hfx (hc2.toN hu hST hO hR) (hs2.toN hu hST hO hR) hrt hfm

/-- The calls of `Calls M τ Hs σ` are closed under their calls. -/
lemma calls_closed (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D) :
    ∀ x y, Calls M τ Hs σ x → Calls M x.1 x.2.1 x.2.2 y → Calls M τ Hs σ y :=
  fun x y hx hy => calls_trans τ Hs σ x y hx hy

end MfDrv

end BKMNW

end PlanarFlow
