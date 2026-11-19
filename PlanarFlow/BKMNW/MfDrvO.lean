module

public import PlanarFlow.BKMNW.LocalO

/-!
# The max-flow driver for any flow of the calls, and for `arunLO`

The driver theorems `mfDriveR`, `mfSpecR_frame`, `mfDriveFrame`, `nodeSF_spec` are stated for the
flows `cflow M O u S T` of `arunL` with one family of subroutines `O`. Their proofs use nothing of
these flows but their values at the leaf calls; here they are restated for **any flow of the calls**
`cf : CFlow M` (`MfSpecRC`, `MfSpecRC.dspec`, **`mfDriveRC`**, `NodeSpecFC`, `StepPSpecC`,
**`nodeSF_specC`**), and for the flows `cflowO` of `arunLO` (subroutines depending on the call):
`cflowO_leaf`, **`mfSpecR_frameO`**, **`mfDriveFrameO`**. The proofs are those of the originals.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs NegSSSP.Driver

universe w

section Gen

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **A flow of the calls**: a flow on the darts of the piece map of every call. -/
abbrev CFlow := (x : MCall M) → Orbit.SDart (pdarts M x.1.piece x.2.1) → ℤ

variable (M) in
/-- The flow computed by a call of `arunLO`. -/
noncomputable def cflowO (NO : MOFam M) (u : D → ℤ) (S T : Finset V) : CFlow M :=
  fun x => arunLO M NO u S T x.1 x.2.1 x.2.2

/-- At a leaf call the flow of `arunLO` is that of `arunL` (the leaf solver, no subroutine). -/
lemma cflowO_leaf (O : PlaneOracles.{w}) {NO : MOFam M} {u : D → ℤ} {S T : Finset V}
    {Q : Finset D} {Hs : List (Finset V)} {σ : Perm D} :
    cflowO M NO u S T (.leaf Q, Hs, σ) = cflow M O u S T (.leaf Q, Hs, σ) := by
  show arunLO M NO u S T (.leaf Q) Hs σ = arunL M O u S T (.leaf Q) Hs σ
  rw [arunLO, arunL]

/-- The output predicate of the driver on the tree of the calls, for a flow of the calls. -/
def ROutC (cf : CFlow M) (FOut : FOutT M) (t : LTree (MCall M) (MCall M)) (d e : ℕ)
    (c : Config) : Prop :=
  ∃ x, t = rtr x ∧ FOut x (cf x) d e c

section RoomC

variable (M) in
/-- **The specifications of the four subprograms of the max-flow driver, with room** (`MfSpec`
with the hypotheses `h + rL x ≤ W` at a leaf call, `h + rS x ≤ W` at the split, which must end
with `er ≤ h + rS x`, and `bl + rS x + rN x ≤ W` at the combination). -/
structure MfSpecRC (cf : CFlow M) (I : Input) (W Hb : ℕ)
    (testS leafS splitS nodeS : Stmt) (G : Config → Prop) (FIn : MCall M → ℕ → ℕ → Config → Prop)
    (FOut : FOutT M) (tc lc sc nc : MCall M → ℕ) (rL rS rN : MCall M → ℕ) : Prop where
  g_stab : ∀ c c', G c → (∀ r < 3000, c'.nreg r = c.nreg r) → c'.rreg = c.rreg →
    MemEq c c' 0 Hb → G c'
  in_stab : ∀ x d e c c', FIn x d e c → MemEq c c' d e → FIn x d e c'
  out_stab : ∀ x f d e c c', FOut x f d e c → MemEq c c' d e → FOut x f d e c'
  test : ∀ x d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → FIn x d e c →
    ∃ c' t, Exec I W testS c c' t ∧ t ≤ tc x ∧ G c' ∧ DRegKeep c c' ∧ HeapKeep Hb h h h c c' ∧
      c'.output = c.output ∧ (c'.nreg 2997 < 1 ↔ ∃ Q, x.1 = .leaf Q)
  leaf : ∀ Q Hs σ d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → h + rL (.leaf Q, Hs, σ) ≤ W →
    FIn (.leaf Q, Hs, σ) d e c →
    ∃ c' t, Exec I W leafS c c' t ∧ t ≤ lc (.leaf Q, Hs, σ) ∧ G c' ∧ DRegKeep c c' ∧
      HeapKeep Hb h d e c c' ∧ c'.output = c.output ∧
      FOut (.leaf Q, Hs, σ) (cf (.leaf Q, Hs, σ)) d e c'
  split : ∀ l r π Hs σ d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → h + rS (.node l r π, Hs, σ) ≤ W →
    FIn (.node l r π, Hs, σ) d e c →
    ∃ c' t el er, Exec I W splitS c c' t ∧ t ≤ sc (.node l r π, Hs, σ) ∧ G c' ∧
      DRegKeep c c' ∧ HeapKeep Hb h h h c c' ∧ c'.output = c.output ∧ c'.nreg 2998 = el ∧
      c'.nreg 2999 = er ∧ h + 5 ≤ el ∧ el + 5 ≤ er ∧ er ≤ h + rS (.node l r π, Hs, σ) ∧
      FIn (chL M l r π Hs σ) (h + 5) el c' ∧ FIn (chR M l r π Hs σ) (el + 5) er c'
  node : ∀ l r π Hs σ d e bl el er c, G c → WordsBounded W c → c.nreg 3004 = d →
    c.nreg 3005 = e → c.nreg 3006 = bl + 5 → c.nreg 3007 = el → c.nreg 3008 = el + 5 →
    c.nreg 3009 = er → c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e → e ≤ bl → bl + 5 ≤ el →
    el + 5 ≤ er → bl + rS (.node l r π, Hs, σ) + rN (.node l r π, Hs, σ) ≤ W →
    FIn (.node l r π, Hs, σ) d e c →
    FOut (chL M l r π Hs σ) (cf (chL M l r π Hs σ)) (bl + 5) el c →
    FOut (chR M l r π Hs σ) (cf (chR M l r π Hs σ)) (el + 5) er c →
    ∃ c' t, Exec I W nodeS c c' t ∧ t ≤ nc (.node l r π, Hs, σ) ∧ G c' ∧ DRegKeep c c' ∧
      HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧
      FOut (.node l r π, Hs, σ) (cf (.node l r π, Hs, σ)) d e c'

variable {cf : CFlow M} {I : Input} {W Hb : ℕ}
  {testS leafS splitS nodeS : Stmt} {G : Config → Prop} {FIn : MCall M → ℕ → ℕ → Config → Prop}
  {FOut : FOutT M} {tc lc sc nc : MCall M → ℕ} {rL rS rN : MCall M → ℕ}

/-- **The specifications with room meet those of the driver with room** on the tree of the
calls, with `room t = roomX (lab t)`. -/
theorem MfSpecRC.dspec
    (hS : MfSpecRC M cf I W Hb testS leafS splitS nodeS G FIn FOut tc lc sc nc rL rS rN) :
    DSpecLR I W Hb testS leafS splitS nodeS G (RIn FIn) (ROutC cf FOut) (fun t => tc (lab t))
      (fun t => lc (lab t)) (fun t => sc (lab t)) (fun t => nc (lab t))
      (fun t => roomX rL rS rN (lab t)) := by
  refine ⟨hS.g_stab, fun t d e c c' ⟨x, hx, h⟩ hm => ⟨x, hx, hS.in_stab _ _ _ _ _ h hm⟩,
    fun t d e c c' ⟨x, hx, h⟩ hm => ⟨x, hx, hS.out_stab _ _ _ _ _ _ h hm⟩, ?_, ?_, ?_, ?_⟩
  · intro t d e h c hg hc r4 r5 r3 h1 h2 h3 _ ⟨x, hx, hin⟩
    subst hx
    obtain ⟨c', k, ex, hk, g', rk, hk', ho, hf⟩ := hS.test x d e h c hg hc r4 r5 r3 h1 h2 h3 hin
    exact ⟨c', k, ex, by rw [lab_rtr]; exact hk, g', rk, hk', ho, hf.trans (rtr_isLeaf x).symm⟩
  · intro a d e h c hg hc r4 r5 r3 h1 h2 h3 hrm ⟨x, hx, hin⟩
    obtain ⟨Q, Hs, σ, rfl, rfl⟩ := rtr_eq_leaf hx
    obtain ⟨c', k, ex, hk, g', rk, hk', ho, hout⟩ :=
      hS.leaf Q Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hrm hin
    exact ⟨c', k, ex, hk, g', rk, hk', ho, _, hx, hout⟩
  · intro lt rt b d e h c hg hc r4 r5 r3 h1 h2 h3 hrm ⟨x, hx, hin⟩
    obtain ⟨l, r, π, Hs, σ, rfl, rfl, rfl, rfl⟩ := rtr_eq_node hx
    have hrm' : h + roomX rL rS rN ((.node l r π, Hs, σ) : MCall M) ≤ W := hrm
    rw [roomX_rtr_node] at hrm'
    obtain ⟨c', k, el, er, ex, hk, g', rk, hk', ho, s8, s9, e1, e2, e3, il, ir⟩ :=
      hS.split l r π Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 (by omega) hin
    refine ⟨c', k, el, er, ex, hk, g', rk, hk', ho, s8, s9, e1, e2, ?_, ?_, ⟨_, rfl, il⟩,
      ⟨_, rfl, ir⟩⟩
    all_goals
      rw [lab_rtr]
      change _ ≤ h + roomX rL rS rN ((.node l r π, Hs, σ) : MCall M)
      rw [roomX_rtr_node]
      have := le_max_left (roomX rL rS rN (chL M l r π Hs σ)) (roomX rL rS rN (chR M l r π Hs σ))
      have := le_max_right (roomX rL rS rN (chL M l r π Hs σ)) (roomX rL rS rN (chR M l r π Hs σ))
      omega
  · intro lt rt b d e bl el er c hg hc r4 r5 r6 r7 r8 r9 r3 h1 h2 h3 h4 h5 hrm ⟨x, hx, hin⟩
      ⟨y, hy, hol⟩ ⟨z, hz, hor⟩
    obtain ⟨l, r, π, Hs, σ, rfl, rfl, rfl, rfl⟩ := rtr_eq_node hx
    obtain rfl := rtr_inj hy
    obtain rfl := rtr_inj hz
    have hrm' : bl + roomX rL rS rN ((.node l r π, Hs, σ) : MCall M) ≤ W := hrm
    rw [roomX_rtr_node] at hrm'
    obtain ⟨c', k, ex, hk, g', rk, hk', ho, hout⟩ :=
      hS.node l r π Hs σ d e bl el er c hg hc r4 r5 r6 r7 r8 r9 r3 h1 h2 h3 h4 h5 (by omega) hin
        hol hor
    exact ⟨c', k, ex, hk, g', rk, hk', ho, _, hx, hout⟩

/-- **The max-flow driver with room**: as `mfDrive`, for subprograms meeting `MfSpecR`, with the
room `h + roomC τ Hs σ ≤ W` above the heap top at the root. -/
theorem mfDriveRC
    (hS : MfSpecRC M cf I W Hb testS leafS splitS nodeS G FIn FOut tc lc sc nc rL rS rN)
    (hHb : 0 < Hb) (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D) {e h : ℕ} (c : Config)
    (hc : WordsBounded W c) (hg : G c) (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1)
    (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h) (m0 : c.nmem Hb = 0)
    (m1 : c.nmem (Hb + 1) = 0) (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hr : h + roomC M rL rS rN τ Hs σ ≤ W) (hin : FIn (τ, Hs, σ) (Hb + 5) e c) :
    ∃ c' t, Exec I W (driver testS leafS splitS nodeS) c c' t ∧
      t ≤ mcost M tc lc sc nc τ Hs σ + 2 ∧ G c' ∧
      FOut (τ, Hs, σ) (cf (τ, Hs, σ)) (Hb + 5) e c' ∧ c'.nreg 3002 = 0 ∧
      c'.nreg 3003 = h ∧ HeapKeep Hb h Hb e c c' ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, g', ⟨x, hx, hout⟩, p2, p3, pk, po⟩ :=
    driveLR hS.dspec hHb (rtree M τ Hs σ) c hc hg r0 r1 r2 r3 m0 m1 m2 he hh
      (by rw [show lab (rtree M τ Hs σ) = (τ, Hs, σ) from lab_rtr (τ, Hs, σ)]; exact hr)
      ⟨(τ, Hs, σ), rfl, hin⟩
  obtain rfl := rtr_inj (show rtr (τ, Hs, σ) = rtr x from hx)
  rw [dcostL_rtree] at ht
  exact ⟨c', t, ex, ht, g', hout, p2, p3, pk, po⟩


end RoomC

section FrameC

variable (M) in
/-- **The specification of the combination** on the frames (`MfSpecR.node` with `G = True`,
`FIn = FInL Reach`, `FOut = FOutL`). -/
def NodeSpecFC (cf : CFlow M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Hb : ℕ) (nodeS : Stmt) (nc rS rN : MCall M → ℕ) :
    Prop :=
  ∀ l r π Hs σ d e bl el er c, True → WordsBounded W c → c.nreg 3004 = d →
    c.nreg 3005 = e → c.nreg 3006 = bl + 5 → c.nreg 3007 = el → c.nreg 3008 = el + 5 →
    c.nreg 3009 = er → c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e → e ≤ bl → bl + 5 ≤ el →
    el + 5 ≤ er → bl + rS (.node l r π, Hs, σ) + rN (.node l r π, Hs, σ) ≤ W →
    FInL M Reach gid u S T Z (.node l r π, Hs, σ) d e c →
    FOutL M gid u S T Z (chL M l r π Hs σ) (cf (chL M l r π Hs σ)) (bl + 5) el c →
    FOutL M gid u S T Z (chR M l r π Hs σ) (cf (chR M l r π Hs σ)) (el + 5) er c →
    ∃ c' t, Exec I W nodeS c c' t ∧ t ≤ nc (.node l r π, Hs, σ) ∧ True ∧ DRegKeep c c' ∧
      HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧
      FOutL M gid u S T Z (.node l r π, Hs, σ) (cf (.node l r π, Hs, σ)) d e c'

variable {NO : MOFam M} {cf : CFlow M} {Reach : MCall M → Prop} {gid : D → ℕ} {u : D → ℤ}
  {S T : Finset V} {Z : ℕ} {I : Input} {W Hb : ℕ} {sepP nodeS : Stmt} {sT : ℕ → ℕ}
  {sR : ℕ → ℕ → ℕ} {nc rN : MCall M → ℕ}

/-- **`mfSpecR_frame` for `arunLO`**: the concrete test, leaf solver and split, with `sepP` and
`nodeS` meeting their specifications, meet `MfSpecRC` for the flows of `arunLO`. -/
theorem mfSpecR_frameO (hsep : SepPSpec M Reach gid u S T Z I W sepP sT sR)
    (hReach : ∀ l r π Hs σ, Reach ((.node l r π, Hs, σ) : MCall M) →
      Reach (chL M l r π Hs σ) ∧ Reach (chR M l r π Hs σ)) (hZ : 2 * Z ≤ W)
    (hnode : NodeSpecFC M (cflowO M NO u S T) Reach gid u S T Z I W Hb nodeS nc (rSp M sR) rN) :
    MfSpecRC M (cflowO M NO u S T) I W Hb mtProg mlProg (splitS sepP) nodeS (fun _ => True)
      (FInL M Reach gid u S T Z) (FOutL M gid u S T Z) (fun _ => 3)
      (fun x => 20 * (pdarts M x.1.piece x.2.1).card + 17) (scp M sT) nc (fun _ => 0)
      (rSp M sR) rN where
  g_stab _ _ _ _ _ _ := trivial
  in_stab _ _ _ _ _ h hm := h.stab hm
  out_stab _ _ _ _ _ _ h hm := h.stab hm
  test x d e h c hg hc r4 r5 r3 h1 h2 h3 hin := mtProg_spec x d e h c hg hc r4 r5 r3 h1 h2 h3 hin
  leaf Q Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 _ hin := by
    rw [cflowO_leaf (planeOracles fun X => frRef X)]
    exact mlProg_spec _ hZ Q Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hin
  split l r π Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hrm hin :=
    mfSplit_spec hsep hReach l r π Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hrm hin
  node := hnode

/-- **`mfDriveFrame` for `arunLO`**: from the root frame holding `FInL` of the call
`(τ, Hs, σ)`, `driver mtProg mlProg (splitS sepP) nodeS` ends with `FOutL` of the flow `arunLO`
of the recursion within `mcost + 2` steps. -/
theorem mfDriveFrameO (hsep : SepPSpec M Reach gid u S T Z I W sepP sT sR)
    (hReach : ∀ l r π Hs σ, Reach ((.node l r π, Hs, σ) : MCall M) →
      Reach (chL M l r π Hs σ) ∧ Reach (chR M l r π Hs σ)) (hZ : 2 * Z ≤ W)
    (hnode : NodeSpecFC M (cflowO M NO u S T) Reach gid u S T Z I W Hb nodeS nc (rSp M sR) rN)
    (hHb : 0 < Hb) (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D) {e h : ℕ} (c : Config)
    (hc : WordsBounded W c) (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1)
    (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h) (m0 : c.nmem Hb = 0)
    (m1 : c.nmem (Hb + 1) = 0) (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hr : h + roomC M (fun _ => 0) (rSp M sR) rN τ Hs σ ≤ W)
    (hin : FInL M Reach gid u S T Z (τ, Hs, σ) (Hb + 5) e c) :
    ∃ c' t, Exec I W (driver mtProg mlProg (splitS sepP) nodeS) c c' t ∧
      t ≤ mcost M (fun _ => 3) (fun x => 20 * (pdarts M x.1.piece x.2.1).card + 17) (scp M sT) nc
        τ Hs σ + 2 ∧
      FOutL M gid u S T Z (τ, Hs, σ) (arunLO M NO u S T τ Hs σ) (Hb + 5) e c' ∧
      HeapKeep Hb h Hb e c c' ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, -, hout, -, -, hk, ho⟩ :=
    mfDriveRC (mfSpecR_frameO hsep hReach hZ hnode) hHb τ Hs σ c hc trivial r0 r1 r2 r3 m0 m1 m2
      he hh hr hin
  exact ⟨c', t, ex, ht, hout, hk, ho⟩


end FrameC

section StepC

variable (M) in
/-- **The specification of the step** (see the module docstring): at a node call of `Reach` with
the invariants of the calls, from the parent's frame holding the sum of the children's flows,
the flow `cf x` of the call in the parent's array `FL`. -/
def StepPSpecC (cf : CFlow M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (stepP : Stmt) (stT rT : MCall M → ℕ) :
    Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e b m : ℕ)
    (en : ℕ → D) (c : Config),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem → d + fsz m ≤ e →
    (∀ i < m, (c.nmem (d + 4 + 6 * m + i) : ℤ) =
      Z + fext (joinFlow (B := pdarts M (l.piece ∪ r.piece) Hs)
        (cf (chL M l r π Hs σ)) (cf (chR M l r π Hs σ))) (en i)) →
    WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = b + 5 → e ≤ b →
    b + rT (.node l r π, Hs, σ) ≤ W →
    ∃ c' t, Exec I W stepP c c' t ∧ t ≤ stT (.node l r π, Hs, σ) ∧ DRegKeep c c' ∧
      (∀ a, a < b → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      ∀ i < m, (c'.nmem (d + 4 + 6 * m + i) : ℤ) =
        Z + fext (cf (.node l r π, Hs, σ)) (en i)

variable {cf : CFlow M} {Reach : MCall M → Prop} {gid : D → ℕ} {u : D → ℤ}
  {S T : Finset V} {Z : ℕ} {I : Input} {W Hb : ℕ} {stepP : Stmt} {stT rT rS : MCall M → ℕ}

/-- **`nodeSF_spec` for any call flow**: the combination meets `NodeSpecFC` for a step meeting
`StepPSpecC`. -/
theorem nodeSF_specC (hst : StepPSpecC M cf Reach gid u S T Z I W stepP stT rT) :
    NodeSpecFC M cf Reach gid u S T Z I W Hb (nodeSF stepP) (ncF M stT) rS rT := by
  intro l r π Hs σ d e bl el er c _ hc r4 r5 r6 r7 r8 r9 r3 hd1 hde hebl hbl hel hroom hin hl hr
  have hR := hin.1
  have hok := hin.2.1
  obtain ⟨c₁, t₁, m, en, e₁, ht₁, hL₁, hfs, hfl₁, hm₁, hr₁, hrr₁, hrm₁, ho₁⟩ :=
    njProg_join (I := I) l r π Hs σ c hc r4 r6 r8 r9 hebl hbl hel hin hl hr
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, t₂, e₂, ht₂, dk₂, hm₂, ho₂, hfl₂⟩ := hst l r π Hs σ d e bl m en c₁ hR hok hL₁ hfs
    hfl₁ hw₁ (by rw [hr₁ _ (by omega), r4]) (by rw [hr₁ _ (by omega), r5])
    (by rw [hr₁ _ (by omega), r6]) hebl (by omega)
  have hm : m = (pdarts M (l.piece ∪ r.piece) Hs).card := hL₁.card
  unfold fsz at hfs
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, ?_, trivial, fun x hx1 hx2 => ?_, fun a ha1 ha2 ha3 => ?_,
    by rw [ho₂, ho₁], m, en, hL₁.congr fun a h1 h2 => (hm₂ a (by omega) (by omega)).1,
    by unfold fsz; omega, hfl₂⟩
  · unfold ncF; simp only [ADec.piece]; rw [← hm]; omega
  · rw [dk₂ x hx1 hx2, hr₁ x (by omega)]
  · have hnot : ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) := fun h => by omega
    obtain ⟨a1, a2⟩ := hm₂ a ha2 hnot
    exact ⟨by rw [a1, hm₁ a (by omega) hnot], by rw [a2, hrm₁]⟩

end StepC

end Gen

end MfDrv

end BKMNW

end PlanarFlow
