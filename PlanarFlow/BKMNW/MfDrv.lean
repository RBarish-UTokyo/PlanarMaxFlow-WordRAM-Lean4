module

public import PlanarFlow.BKMNW.MfDrvCore
public import PlanarFlow.BKMNW.LocalCost

/-!
# The max-flow driver: Algorithm 1 on the piece maps, as one explicit-stack loop

The recursion `PlanarFlow.BKMNW.arunL` (Algorithm 1 with every recursive step on its piece map)
runs on a decomposition `τ : ADec M`, with the holes `Hs` and the rotation `σ` of the piece map
carried down the calls (`childHoles`, `childRot`). Here it is run by **the fixed driver program**
`NegSSSP.Driver.driver testS leafS splitS nodeS` (`PlanarFlow/BKMNW/MfDrvCore.lean`): one loop
over a stack of frames, one frame per call.

* `MCall M` (a call: subtree, holes, rotation), `chL`, `chR` (the calls of the two children),
  **`rtree`** (the tree of the calls, labelled by the calls), `rtree_inj`, `cflow` (the flow of a
  call, `arunL`).
* **`MfSpec`**: the specifications of the four subprograms, on frames encoded by two predicates
  `FIn x d e c` (the input of the call `x` in the frame data `[d, e)`) and `FOut x f d e c` (the
  output flow `f` of the call `x`), as in the article: the test (leaf or node); the leaf solver
  (output `arunL` of the leaf call); the split (the frames of the two child calls, with their holes
  and rotations: the separator, `childHoles`, `childRot`); the combination (output `arunL` of the
  node call from the outputs of the children: `joinFlow`, then `sepStep` on the piece map).
* **`MfSpec.dspec`**: they meet the specifications `DSpecL` of the driver on `rtree`.
* **`mfDrive`**: from the root frame holding `FIn (τ, Hs, σ)`, the driver ends with
  `FOut (τ, Hs, σ) (arunL M O u S T τ Hs σ)` in the root frame within `mcost τ Hs σ + 2` steps.
* `mcost` (the steps per call), `asize` (the calls), **`mcost_le`**: if every leaf call costs at
  most `A · (its charge in arunLCost) + B` and every node call `A · (its charge) + B`, then
  `mcost ≤ A · arunLCost + B · asize`.

**What is a parameter here**: the four subprograms and the frame encodings `FIn`, `FOut`, with
their specifications (`MfSpec`). The programs of the bookkeeping exist separately
(`crProg_childRot`: the rotations of the child piece maps; `jfProg_joinFlow`: the sum of the
children's flows; `cbLoop_cob`: `f + cob χ`), as do the leaf solver (`cMach_leaf_exec`), the
s-t flow, FR-Dijkstra, MSSP and the negative-length recursion; their composition into `leafS`,
`splitS`, `nodeS` on one concrete frame layout is not done.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- A call of the recursion: the subtree, the holes, the rotation of the piece map. -/
abbrev MCall := ADec M × List (Finset V) × Perm D

variable (M) in
/-- The call of the left child. -/
noncomputable def chL (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) :
    MCall M :=
  (l, childHoles Hs π.path.mverts, childRot M σ (pdarts M (l.piece ∪ r.piece) Hs) π.path.darts
    (pdarts M l.piece (childHoles Hs π.path.mverts)))

variable (M) in
/-- The call of the right child. -/
noncomputable def chR (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) :
    MCall M :=
  (r, childHoles Hs π.path.mverts, childRot M σ (pdarts M (l.piece ∪ r.piece) Hs) π.path.darts
    (pdarts M r.piece (childHoles Hs π.path.mverts)))

variable (M) in
/-- **The tree of the calls** of the recursion from the call `(τ, Hs, σ)`, every leaf and node
labelled by its call. -/
noncomputable def rtree : ADec M → List (Finset V) → Perm D → LTree (MCall M) (MCall M)
  | .leaf Q, Hs, σ => .leaf (.leaf Q, Hs, σ)
  | .node l r π, Hs, σ =>
    .node (rtree l (chL M l r π Hs σ).2.1 (chL M l r π Hs σ).2.2)
      (rtree r (chR M l r π Hs σ).2.1 (chR M l r π Hs σ).2.2) (.node l r π, Hs, σ)

/-- The tree of the calls from a call. -/
noncomputable abbrev rtr (x : MCall M) : LTree (MCall M) (MCall M) := rtree M x.1 x.2.1 x.2.2

/-- The label of the root. -/
def lab {X : Type*} : LTree X X → X
  | .leaf a => a
  | .node _ _ b => b

lemma lab_rtr (x : MCall M) : lab (rtr x) = x := by
  obtain ⟨τ, Hs, σ⟩ := x
  cases τ <;> rfl

lemma rtr_inj {x y : MCall M} (h : rtr x = rtr y) : x = y := by
  rw [← lab_rtr x, ← lab_rtr y, h]

lemma rtr_leaf {Q : Finset D} {Hs : List (Finset V)} {σ : Perm D} :
    rtr ((.leaf Q, Hs, σ) : MCall M) = .leaf (.leaf Q, Hs, σ) := rfl

lemma rtr_node {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D} :
    rtr ((.node l r π, Hs, σ) : MCall M) =
      .node (rtr (chL M l r π Hs σ)) (rtr (chR M l r π Hs σ)) (.node l r π, Hs, σ) := rfl

/-- The tree of a call is a leaf exactly at a leaf call. -/
lemma rtr_isLeaf (x : MCall M) : (∃ a, rtr x = .leaf a) ↔ ∃ Q, x.1 = .leaf Q := by
  obtain ⟨τ, Hs, σ⟩ := x
  cases τ with
  | leaf Q => exact ⟨fun _ => ⟨Q, rfl⟩, fun _ => ⟨_, rfl⟩⟩
  | node l r π =>
    refine ⟨fun ⟨a, h⟩ => ?_, fun ⟨Q, h⟩ => ?_⟩
    · rw [rtr_node] at h; cases h
    · cases h

/-- A leaf of the tree of a call is the tree of a leaf call. -/
lemma rtr_eq_leaf {x a : MCall M} (h : LTree.leaf a = rtr x) :
    ∃ Q Hs σ, x = (.leaf Q, Hs, σ) ∧ a = x := by
  obtain ⟨τ, Hs, σ⟩ := x
  cases τ with
  | leaf Q => exact ⟨Q, Hs, σ, rfl, by cases h; rfl⟩
  | node l r π => rw [rtr_node] at h; cases h

/-- A node of the tree of a call is the tree of a node call. -/
lemma rtr_eq_node {x b : MCall M} {lt rt : LTree (MCall M) (MCall M)}
    (h : LTree.node lt rt b = rtr x) :
    ∃ l r π Hs σ, x = (.node l r π, Hs, σ) ∧ b = x ∧ lt = rtr (chL M l r π Hs σ) ∧
      rt = rtr (chR M l r π Hs σ) := by
  obtain ⟨τ, Hs, σ⟩ := x
  cases τ with
  | leaf Q => rw [rtr_leaf] at h; cases h
  | node l r π =>
    rw [rtr_node] at h
    cases h
    exact ⟨l, r, π, Hs, σ, rfl, rfl, rfl, rfl⟩

variable (M) in
/-- The flow computed by a call (`arunL`), on the darts of its piece map. -/
noncomputable def cflow (O : PlaneOracles.{w}) (u : D → ℤ) (S T : Finset V) (x : MCall M) :
    Orbit.SDart (pdarts M x.1.piece x.2.1) → ℤ :=
  arunL M O u S T x.1 x.2.1 x.2.2

/-- The type of the output predicate of a frame: a call, a flow on its piece map, the frame. -/
abbrev FOutT (M : CombMap D V F) :=
  (x : MCall M) → (Orbit.SDart (pdarts M x.1.piece x.2.1) → ℤ) → ℕ → ℕ → Config → Prop

/-- The input predicate of the driver on the tree of the calls. -/
def RIn (FIn : MCall M → ℕ → ℕ → Config → Prop) (t : LTree (MCall M) (MCall M)) (d e : ℕ)
    (c : Config) : Prop :=
  ∃ x, t = rtr x ∧ FIn x d e c

/-- The output predicate of the driver on the tree of the calls. -/
def ROut (O : PlaneOracles.{w}) (u : D → ℤ) (S T : Finset V) (FOut : FOutT M)
    (t : LTree (MCall M) (MCall M)) (d e : ℕ) (c : Config) : Prop :=
  ∃ x, t = rtr x ∧ FOut x (cflow M O u S T x) d e c

variable (M) in
/-- **The specifications of the four subprograms of the max-flow driver** on frames encoded by
`FIn` (the input of a call) and `FOut` (the output flow of a call), with costs per call. -/
structure MfSpec (O : PlaneOracles.{w}) (u : D → ℤ) (S T : Finset V) (I : Input) (W Hb : ℕ)
    (testS leafS splitS nodeS : Stmt) (G : Config → Prop) (FIn : MCall M → ℕ → ℕ → Config → Prop)
    (FOut : FOutT M) (tc lc sc nc : MCall M → ℕ) : Prop where
  g_stab : ∀ c c', G c → (∀ r < 3000, c'.nreg r = c.nreg r) → c'.rreg = c.rreg →
    MemEq c c' 0 Hb → G c'
  in_stab : ∀ x d e c c', FIn x d e c → MemEq c c' d e → FIn x d e c'
  out_stab : ∀ x f d e c c', FOut x f d e c → MemEq c c' d e → FOut x f d e c'
  /-- The test: `r2997 < 1` exactly at a leaf call. -/
  test : ∀ x d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → FIn x d e c →
    ∃ c' t, Exec I W testS c c' t ∧ t ≤ tc x ∧ G c' ∧ DRegKeep c c' ∧ HeapKeep Hb h h h c c' ∧
      c'.output = c.output ∧ (c'.nreg 2997 < 1 ↔ ∃ Q, x.1 = .leaf Q)
  /-- The leaf solver: the flow `arunL` of the leaf call. -/
  leaf : ∀ Q Hs σ d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → FIn (.leaf Q, Hs, σ) d e c →
    ∃ c' t, Exec I W leafS c c' t ∧ t ≤ lc (.leaf Q, Hs, σ) ∧ G c' ∧ DRegKeep c c' ∧
      HeapKeep Hb h d e c c' ∧ c'.output = c.output ∧
      FOut (.leaf Q, Hs, σ) (cflow M O u S T (.leaf Q, Hs, σ)) d e c'
  /-- The split: the frames of the two child calls above the heap top. -/
  split : ∀ l r π Hs σ d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → FIn (.node l r π, Hs, σ) d e c →
    ∃ c' t el er, Exec I W splitS c c' t ∧ t ≤ sc (.node l r π, Hs, σ) ∧ G c' ∧
      DRegKeep c c' ∧ HeapKeep Hb h h h c c' ∧ c'.output = c.output ∧ c'.nreg 2998 = el ∧
      c'.nreg 2999 = er ∧ h + 5 ≤ el ∧ el + 5 ≤ er ∧ FIn (chL M l r π Hs σ) (h + 5) el c' ∧
      FIn (chR M l r π Hs σ) (el + 5) er c'
  /-- The combination: the flow `arunL` of the node call from the flows of the children. -/
  node : ∀ l r π Hs σ d e bl el er c, G c → WordsBounded W c → c.nreg 3004 = d →
    c.nreg 3005 = e → c.nreg 3006 = bl + 5 → c.nreg 3007 = el → c.nreg 3008 = el + 5 →
    c.nreg 3009 = er → c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e → e ≤ bl → bl + 5 ≤ el →
    el + 5 ≤ er → FIn (.node l r π, Hs, σ) d e c →
    FOut (chL M l r π Hs σ) (cflow M O u S T (chL M l r π Hs σ)) (bl + 5) el c →
    FOut (chR M l r π Hs σ) (cflow M O u S T (chR M l r π Hs σ)) (el + 5) er c →
    ∃ c' t, Exec I W nodeS c c' t ∧ t ≤ nc (.node l r π, Hs, σ) ∧ G c' ∧ DRegKeep c c' ∧
      HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧
      FOut (.node l r π, Hs, σ) (cflow M O u S T (.node l r π, Hs, σ)) d e c'

variable {O : PlaneOracles.{w}} {u : D → ℤ} {S T : Finset V} {I : Input} {W Hb : ℕ}
  {testS leafS splitS nodeS : Stmt} {G : Config → Prop} {FIn : MCall M → ℕ → ℕ → Config → Prop}
  {FOut : FOutT M} {tc lc sc nc : MCall M → ℕ}

/-- **The subprograms meet the specifications of the driver** on the tree of the calls. -/
theorem MfSpec.dspec (hS : MfSpec M O u S T I W Hb testS leafS splitS nodeS G FIn FOut tc lc sc nc) :
    DSpecL I W Hb testS leafS splitS nodeS G (RIn FIn) (ROut O u S T FOut) (fun t => tc (lab t))
      (fun t => lc (lab t)) (fun t => sc (lab t)) (fun t => nc (lab t)) := by
  refine ⟨hS.g_stab, fun t d e c c' ⟨x, hx, h⟩ hm => ⟨x, hx, hS.in_stab _ _ _ _ _ h hm⟩,
    fun t d e c c' ⟨x, hx, h⟩ hm => ⟨x, hx, hS.out_stab _ _ _ _ _ _ h hm⟩, ?_, ?_, ?_, ?_⟩
  · intro t d e h c hg hc r4 r5 r3 h1 h2 h3 ⟨x, hx, hin⟩
    subst hx
    obtain ⟨c', k, ex, hk, g', rk, hk', ho, hf⟩ := hS.test x d e h c hg hc r4 r5 r3 h1 h2 h3 hin
    exact ⟨c', k, ex, by rw [lab_rtr]; exact hk, g', rk, hk', ho, hf.trans (rtr_isLeaf x).symm⟩
  · intro a d e h c hg hc r4 r5 r3 h1 h2 h3 ⟨x, hx, hin⟩
    obtain ⟨Q, Hs, σ, rfl, rfl⟩ := rtr_eq_leaf hx
    obtain ⟨c', k, ex, hk, g', rk, hk', ho, hout⟩ :=
      hS.leaf Q Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hin
    exact ⟨c', k, ex, hk, g', rk, hk', ho, _, hx, hout⟩
  · intro lt rt b d e h c hg hc r4 r5 r3 h1 h2 h3 ⟨x, hx, hin⟩
    obtain ⟨l, r, π, Hs, σ, rfl, rfl, rfl, rfl⟩ := rtr_eq_node hx
    obtain ⟨c', k, el, er, ex, hk, g', rk, hk', ho, s8, s9, e1, e2, il, ir⟩ :=
      hS.split l r π Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hin
    exact ⟨c', k, el, er, ex, hk, g', rk, hk', ho, s8, s9, e1, e2, ⟨_, rfl, il⟩, ⟨_, rfl, ir⟩⟩
  · intro lt rt b d e bl el er c hg hc r4 r5 r6 r7 r8 r9 r3 h1 h2 h3 h4 h5 ⟨x, hx, hin⟩
      ⟨y, hy, hol⟩ ⟨z, hz, hor⟩
    obtain ⟨l, r, π, Hs, σ, rfl, rfl, rfl, rfl⟩ := rtr_eq_node hx
    obtain rfl := rtr_inj hy
    obtain rfl := rtr_inj hz
    obtain ⟨c', k, ex, hk, g', rk, hk', ho, hout⟩ :=
      hS.node l r π Hs σ d e bl el er c hg hc r4 r5 r6 r7 r8 r9 r3 h1 h2 h3 h4 h5 hin hol hor
    exact ⟨c', k, ex, hk, g', rk, hk', ho, _, hx, hout⟩

variable (M) in
/-- **The steps of the driver per call**: the subprograms, plus `20` per leaf and `80` per
node. -/
noncomputable def mcost (tc lc sc nc : MCall M → ℕ) :
    ADec M → List (Finset V) → Perm D → ℕ
  | .leaf Q, Hs, σ => tc (.leaf Q, Hs, σ) + lc (.leaf Q, Hs, σ) + 20
  | .node l r π, Hs, σ => tc (.node l r π, Hs, σ) + sc (.node l r π, Hs, σ) +
      nc (.node l r π, Hs, σ) + mcost tc lc sc nc l (chL M l r π Hs σ).2.1 (chL M l r π Hs σ).2.2 +
      mcost tc lc sc nc r (chR M l r π Hs σ).2.1 (chR M l r π Hs σ).2.2 + 80

lemma dcostL_rtree (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D) :
    dcostL (fun t => tc (lab t)) (fun t => lc (lab t)) (fun t => sc (lab t))
      (fun t => nc (lab t)) (rtree M τ Hs σ) = mcost M tc lc sc nc τ Hs σ := by
  induction τ generalizing Hs σ with
  | leaf Q => rfl
  | node l r π ihl ihr =>
    simp only [rtree, dcostL, mcost]
    rw [ihl, ihr]
    rfl

/-- **The max-flow driver** (see the module docstring): from the root frame `[Hb, e)` holding
the input of the call `(τ, Hs, σ)`, the fixed driver program ends with the flow
`arunL M O u S T τ Hs σ` of the recursion in the root frame, within `mcost τ Hs σ + 2` steps. -/
theorem mfDrive (hS : MfSpec M O u S T I W Hb testS leafS splitS nodeS G FIn FOut tc lc sc nc)
    (hHb : 0 < Hb) (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D) {e h : ℕ} (c : Config)
    (hc : WordsBounded W c) (hg : G c) (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1)
    (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h) (m0 : c.nmem Hb = 0)
    (m1 : c.nmem (Hb + 1) = 0) (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hin : FIn (τ, Hs, σ) (Hb + 5) e c) :
    ∃ c' t, Exec I W (driver testS leafS splitS nodeS) c c' t ∧
      t ≤ mcost M tc lc sc nc τ Hs σ + 2 ∧ G c' ∧
      FOut (τ, Hs, σ) (arunL M O u S T τ Hs σ) (Hb + 5) e c' ∧ c'.nreg 3002 = 0 ∧
      c'.nreg 3003 = h ∧ HeapKeep Hb h Hb e c c' ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, g', ⟨x, hx, hout⟩, p2, p3, pk, po⟩ :=
    driveL hS.dspec hHb (rtree M τ Hs σ) c hc hg r0 r1 r2 r3 m0 m1 m2 he hh ⟨(τ, Hs, σ), rfl, hin⟩
  obtain rfl := rtr_inj (show rtr (τ, Hs, σ) = rtr x from hx)
  rw [dcostL_rtree] at ht
  exact ⟨c', t, ex, ht, g', hout, p2, p3, pk, po⟩

/-! ### The steps against the charges of `arunLCost` -/

/-- The number of calls. -/
def asize : ADec M → ℕ
  | .leaf _ => 1
  | .node l r _ => asize l + asize r + 1

variable (M) in
open Classical in
/-- The charge of `arunLCost` at a node call, without the children. -/
noncomputable def nodeCharge (c : SubCosts) (l r : ADec M) (π : HSep M) (Hs : List (Finset V))
    (σ : Perm D) : ℕ :=
  (if h : PieceInv M (l.piece ∪ r.piece) Hs σ ∧
      ∀ s ∈ π.segs, SegIn M (l.piece ∪ r.piece) Hs s then
    c.sep (l.piece ∪ r.piece).card +
      c.nodeRuns (pdarts M (l.piece ∪ r.piece) Hs).card
        (nOrb (σ * revPerm M) (pdarts M (l.piece ∪ r.piece) Hs))
        (psize M σ (pdarts M (l.piece ∪ r.piece) Hs))
        (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length
        (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length
        ((segsP h.1 π.segs h.2).map fun s => (s.faces.card, s.k))
  else 0) + 8 * c.lin ((l.piece ∪ r.piece).card + Hs.length)

lemma arunLCost_node (c : SubCosts) (l r : ADec M) (π : HSep M) (Hs : List (Finset V))
    (σ : Perm D) :
    arunLCost M c (.node l r π) Hs σ = arunLCost M c l (chL M l r π Hs σ).2.1
      (chL M l r π Hs σ).2.2 + arunLCost M c r (chR M l r π Hs σ).2.1 (chR M l r π Hs σ).2.2 +
      nodeCharge M c l r π Hs σ := by
  simp only [arunLCost, nodeCharge, chL, chR]
  omega

/-- **The steps of the driver against `arunLCost`**: if every leaf call costs at most
`A · (c.leaf + 4 c.lin)` (its charge) plus `B`, and every node call at most `A · nodeCharge`
plus `B`, the driver takes at most `A · arunLCost + B · asize` steps (before the final `2`). -/
theorem mcost_le (c : SubCosts) {A B : ℕ}
    (hl : ∀ Q Hs σ, tc ((.leaf Q, Hs, σ) : MCall M) + lc (.leaf Q, Hs, σ) + 20 ≤
      A * (c.leaf (pdarts M Q Hs).card + 4 * c.lin (Q.card + Hs.length)) + B)
    (hn : ∀ l r π Hs σ, tc ((.node l r π, Hs, σ) : MCall M) + sc (.node l r π, Hs, σ) +
      nc (.node l r π, Hs, σ) + 80 ≤ A * nodeCharge M c l r π Hs σ + B) :
    ∀ (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D),
      mcost M tc lc sc nc τ Hs σ ≤ A * arunLCost M c τ Hs σ + B * asize τ
  | .leaf Q, Hs, σ => by
    simp only [mcost, arunLCost, asize, mul_one]
    exact hl Q Hs σ
  | .node l r π, Hs, σ => by
    have il := mcost_le c hl hn l (chL M l r π Hs σ).2.1 (chL M l r π Hs σ).2.2
    have ir := mcost_le c hl hn r (chR M l r π Hs σ).2.1 (chR M l r π Hs σ).2.2
    have h0 := hn l r π Hs σ
    rw [arunLCost_node]
    simp only [mcost, asize]
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega

/-- On a decomposition meeting `Core` (siblings disjoint and nonempty), a nonempty piece of `m`
darts has at most `2 m - 1` calls. -/
lemma asize_succ_le {κ η : ℕ} :
    ∀ {τ : ADec M} {Hs : List (Finset V)}, τ.Core M κ η Hs → 0 < τ.piece.card →
      asize τ + 1 ≤ 2 * τ.piece.card
  | .leaf _, _, _, h => by simp only [asize, ADec.piece] at h ⊢; omega
  | .node l r _, _, ⟨hl, hr, hlr, hl0, hr0, _⟩, _ => by
    have il := asize_succ_le hl hl0
    have ir := asize_succ_le hr hr0
    simp only [asize, ADec.piece, card_union_of_disjoint hlr]
    omega

/-- **The number of calls**: at most `2 m + 1` on a decomposition meeting `Core` of `m` darts. -/
lemma asize_le {κ η : ℕ} {τ : ADec M} {Hs : List (Finset V)} (h : τ.Core M κ η Hs) :
    asize τ ≤ 2 * τ.piece.card + 1 := by
  rcases Nat.eq_zero_or_pos τ.piece.card with h0 | h0
  · cases τ with
    | leaf Q => simp [asize]
    | node l r π =>
      obtain ⟨-, -, hlr, hl0, -, -⟩ := h
      simp only [ADec.piece, card_union_of_disjoint hlr] at h0
      omega
  · have := asize_succ_le h h0
    omega

end MfDrv

end BKMNW

end PlanarFlow
