module

public import PlanarFlow.BKMNW.MfSplitSpec
public import PlanarFlow.BKMNW.MfDrvHead

/-!
# The max-flow driver on the concrete frames: one fixed program, `sepP` and `nodeS` parameters

* `Calls τ Hs σ` (the calls of the recursion from the call `(τ, Hs, σ)`), `calls_self`,
  **`calls_child`** (closed under the child calls).
* `NodeSpecF` (the field `node` of `MfSpecR` on the frames `FInL`/`FOutL`, `G = True`).
* **`mfSpecR_frame`**: `mtProg`, `mlProg`, `splitS sepP` and any `nodeS` meeting `NodeSpecF` meet
  `MfSpecR` on the frames (test `3`, leaf `20 m + 17`, split `scp sT`; rooms `0`, `rSp sR`, `rN`).
* **`mfDriveFrame`**: the fixed program `driver mtProg mlProg (splitS sepP) nodeS` runs from the
  root frame of any call to its flow `arunL` in the frame, within `mcost + 2` steps.
* **`mfDriveFrame_decM`**: on the decomposition of `maxflow_plane_cost_decM`, with the calls of
  that decomposition as `Reach`, per-call costs against the charges of `arunLCost`, the room
  `h + (2 m + 1) R ≤ W`: the same program reaches `FOutL` of the root call within
  `A · (headline) + B · (2 m + 1) + 2` steps, and the flow is a maximum flow (`IsMax`).

**Parameters left**: the separator program `sepP` (specification `SepPSpec`, restricted to the
calls of the decomposition) and the combination `nodeS` (specification `NodeSpecF`), with the
per-call cost hypotheses `hl` (the leaf: `3 + (20 m + 17) + 20 ≤ A · charge + B`) and `hn`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver

universe w

section Gen

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **The calls of the recursion** from the call `(τ, Hs, σ)`. -/
def Calls : ADec M → List (Finset V) → Perm D → MCall M → Prop
  | .leaf Q, Hs, σ, x => x = (.leaf Q, Hs, σ)
  | .node l r π, Hs, σ, x => x = (.node l r π, Hs, σ) ∨
      Calls l (chL M l r π Hs σ).2.1 (chL M l r π Hs σ).2.2 x ∨
      Calls r (chR M l r π Hs σ).2.1 (chR M l r π Hs σ).2.2 x

lemma calls_self : ∀ (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D), Calls M τ Hs σ (τ, Hs, σ)
  | .leaf _, _, _ => rfl
  | .node _ _ _, _, _ => Or.inl rfl

/-- **The calls are closed under the child calls.** -/
theorem calls_child : ∀ (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D) (l r : ADec M)
    (π : HSep M) (Hs' : List (Finset V)) (σ' : Perm D), Calls M τ Hs σ (.node l r π, Hs', σ') →
    Calls M τ Hs σ (chL M l r π Hs' σ') ∧ Calls M τ Hs σ (chR M l r π Hs' σ')
  | .leaf Q, Hs, σ, l, r, π, Hs', σ', h => by cases h
  | .node l₀ r₀ π₀, Hs, σ, l, r, π, Hs', σ', h => by
    rcases h with h | h | h
    · cases h
      exact ⟨Or.inr (Or.inl (calls_self _ _ _)), Or.inr (Or.inr (calls_self _ _ _))⟩
    · obtain ⟨a, b⟩ := calls_child l₀ _ _ l r π Hs' σ' h
      exact ⟨Or.inr (Or.inl a), Or.inr (Or.inl b)⟩
    · obtain ⟨a, b⟩ := calls_child r₀ _ _ l r π Hs' σ' h
      exact ⟨Or.inr (Or.inr a), Or.inr (Or.inr b)⟩

variable (M) in
/-- **The specification of the combination** on the frames (`MfSpecR.node` with `G = True`,
`FIn = FInL Reach`, `FOut = FOutL`). -/
def NodeSpecF (O : PlaneOracles.{w}) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Hb : ℕ) (nodeS : Stmt) (nc rS rN : MCall M → ℕ) :
    Prop :=
  ∀ l r π Hs σ d e bl el er c, True → WordsBounded W c → c.nreg 3004 = d →
    c.nreg 3005 = e → c.nreg 3006 = bl + 5 → c.nreg 3007 = el → c.nreg 3008 = el + 5 →
    c.nreg 3009 = er → c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e → e ≤ bl → bl + 5 ≤ el →
    el + 5 ≤ er → bl + rS (.node l r π, Hs, σ) + rN (.node l r π, Hs, σ) ≤ W →
    FInL M Reach gid u S T Z (.node l r π, Hs, σ) d e c →
    FOutL M gid u S T Z (chL M l r π Hs σ) (cflow M O u S T (chL M l r π Hs σ)) (bl + 5) el c →
    FOutL M gid u S T Z (chR M l r π Hs σ) (cflow M O u S T (chR M l r π Hs σ)) (el + 5) er c →
    ∃ c' t, Exec I W nodeS c c' t ∧ t ≤ nc (.node l r π, Hs, σ) ∧ True ∧ DRegKeep c c' ∧
      HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧
      FOutL M gid u S T Z (.node l r π, Hs, σ) (cflow M O u S T (.node l r π, Hs, σ)) d e c'

variable {O : PlaneOracles.{w}} {Reach : MCall M → Prop} {gid : D → ℕ} {u : D → ℤ}
  {S T : Finset V} {Z : ℕ} {I : Input} {W Hb : ℕ} {sepP nodeS : Stmt} {sT : ℕ → ℕ}
  {sR : ℕ → ℕ → ℕ} {nc rN : MCall M → ℕ}

/-- **The concrete test, leaf solver and split, with `sepP` and `nodeS` meeting their
specifications, meet `MfSpecR` on the frames.** -/
theorem mfSpecR_frame (hsep : SepPSpec M Reach gid u S T Z I W sepP sT sR)
    (hReach : ∀ l r π Hs σ, Reach ((.node l r π, Hs, σ) : MCall M) →
      Reach (chL M l r π Hs σ) ∧ Reach (chR M l r π Hs σ)) (hZ : 2 * Z ≤ W)
    (hnode : NodeSpecF M O Reach gid u S T Z I W Hb nodeS nc (rSp M sR) rN) :
    MfSpecR M O u S T I W Hb mtProg mlProg (splitS sepP) nodeS (fun _ => True)
      (FInL M Reach gid u S T Z) (FOutL M gid u S T Z) (fun _ => 3)
      (fun x => 20 * (pdarts M x.1.piece x.2.1).card + 17) (scp M sT) nc (fun _ => 0)
      (rSp M sR) rN where
  g_stab _ _ _ _ _ _ := trivial
  in_stab _ _ _ _ _ h hm := h.stab hm
  out_stab _ _ _ _ _ _ h hm := h.stab hm
  test x d e h c hg hc r4 r5 r3 h1 h2 h3 hin := mtProg_spec x d e h c hg hc r4 r5 r3 h1 h2 h3 hin
  leaf Q Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 _ hin :=
    mlProg_spec O hZ Q Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hin
  split l r π Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hrm hin :=
    mfSplit_spec hsep hReach l r π Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hrm hin
  node := hnode

/-- **The fixed driver program on the frames**: from the root frame holding `FInL` of the call
`(τ, Hs, σ)`, `driver mtProg mlProg (splitS sepP) nodeS` ends with `FOutL` of the flow `arunL`
of the recursion within `mcost + 2` steps. -/
theorem mfDriveFrame (hsep : SepPSpec M Reach gid u S T Z I W sepP sT sR)
    (hReach : ∀ l r π Hs σ, Reach ((.node l r π, Hs, σ) : MCall M) →
      Reach (chL M l r π Hs σ) ∧ Reach (chR M l r π Hs σ)) (hZ : 2 * Z ≤ W)
    (hnode : NodeSpecF M O Reach gid u S T Z I W Hb nodeS nc (rSp M sR) rN)
    (hHb : 0 < Hb) (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D) {e h : ℕ} (c : Config)
    (hc : WordsBounded W c) (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1)
    (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h) (m0 : c.nmem Hb = 0)
    (m1 : c.nmem (Hb + 1) = 0) (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hr : h + roomC M (fun _ => 0) (rSp M sR) rN τ Hs σ ≤ W)
    (hin : FInL M Reach gid u S T Z (τ, Hs, σ) (Hb + 5) e c) :
    ∃ c' t, Exec I W (driver mtProg mlProg (splitS sepP) nodeS) c c' t ∧
      t ≤ mcost M (fun _ => 3) (fun x => 20 * (pdarts M x.1.piece x.2.1).card + 17) (scp M sT) nc
        τ Hs σ + 2 ∧
      FOutL M gid u S T Z (τ, Hs, σ) (arunL M O u S T τ Hs σ) (Hb + 5) e c' ∧
      HeapKeep Hb h Hb e c c' ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, -, hout, -, -, hk, ho⟩ :=
    mfDriveR (mfSpecR_frame hsep hReach hZ hnode) hHb τ Hs σ c hc trivial r0 r1 r2 r3 m0 m1 m2
      he hh hr hin
  exact ⟨c', t, ex, ht, hout, hk, ho⟩

end Gen

section Head

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The fixed driver program on the frames, on the decomposition of the headline theorem**
(see the module docstring). -/
theorem mfDriveFrame_decM (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _)
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    {I : Input} {W Hb Z : ℕ} {gid : _ → ℕ} {sepP nodeS : Stmt} {sT : ℕ → ℕ} {sR : ℕ → ℕ → ℕ}
    {nc rN : MCall (lpreMap M) → ℕ} {A B R : ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepM (lpreMap M)) e n Hs A W
    let τ := decS (lpreMap M) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMap M) τ [] (rotPerm (lpreMap M))
    SepPSpec (lpreMap M) Reach gid u' S' T' Z I W sepP sT sR →
    NodeSpecF (lpreMap M) (planeOracles fun X => frRef X) Reach gid u' S' T' Z I W Hb nodeS nc
      (rSp (lpreMap M) sR) rN →
    (∀ Q Hs, 3 + (20 * (pdarts (lpreMap M) Q Hs).card + 17) + 20 ≤
      A * (c.leaf (pdarts (lpreMap M) Q Hs).card + 4 * c.lin (Q.card + Hs.length)) + B) →
    (∀ l r π Hs σ, 3 + scp (lpreMap M) sT (.node l r π, Hs, σ) + nc (.node l r π, Hs, σ) + 80 ≤
      A * nodeCharge (lpreMap M) c l r π Hs σ + B) →
    (∀ x, rSp (lpreMap M) sR x + rN x ≤ R) →
    0 < Hb → ∀ {eF h : ℕ} (c₀ : Config), WordsBounded W c₀ → c₀.nreg 3000 = 0 →
    c₀.nreg 3001 = 1 → c₀.nreg 3002 = Hb → c₀.nreg 3003 = h → c₀.nmem Hb = 0 →
    c₀.nmem (Hb + 1) = 0 → c₀.nmem (Hb + 2) = eF → Hb + 5 ≤ eF → eF ≤ h →
    h + (2 * τ.piece.card + 1) * R ≤ W →
    FInL (lpreMap M) Reach gid u' S' T' Z (τ, [], rotPerm (lpreMap M)) (Hb + 5) eF c₀ →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (driver mtProg mlProg (splitS sepP) nodeS) c₀ c' t ∧
      t ≤ A * ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D)) +
        B * (2 * τ.piece.card + 1) + 2 ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunL (lpreMap M) (planeOracles fun X => frRef X) u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) eF c' ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) := by
  intro pc sc τ u' S' T' Reach hsep hnode hl hn hR hHb eF h c₀ hc₀ r0 r1 r2 r3 m0 m1 m2 he hh
    hroom hin
  obtain ⟨hbal, hmax, hcost⟩ := maxflow_plane_cost_decM hM hrot hface hu hST e hsurj d₀ hc
  have hsz := asize_le (ADec.BalA.core hbal.2.2.2.2)
  have hrm := roomC_le (M := lpreMap M) (rL := fun _ => 0) (fun _ => Nat.zero_le R) hR τ []
    (rotPerm (lpreMap M))
  have hsz' := Nat.mul_le_mul_right R hsz
  obtain ⟨c', t, ex, ht, hout, -, -⟩ := mfDriveFrame hsep
    (fun l r π Hs σ hx => calls_child τ [] _ l r π Hs σ hx) hZ hnode hHb τ []
    (rotPerm (lpreMap M)) c₀ hc₀ r0 r1 r2 r3 m0 m1 m2 he hh
    ((Nat.add_le_add_left (hrm.trans hsz') h).trans hroom) hin
  have hm := mcost_le (M := lpreMap M) (tc := fun _ => 3)
    (lc := fun x => 20 * (pdarts (lpreMap M) x.1.piece x.2.1).card + 17)
    (sc := scp (lpreMap M) sT) (nc := nc) c (fun Q Hs σ => hl Q Hs) hn τ [] (rotPerm (lpreMap M))
  have ha : arunLCost (lpreMap M) c τ [] (rotPerm (lpreMap M)) ≤ runLCost (lpreMap M) c τ := by
    unfold runLCost; omega
  have hA := Nat.mul_le_mul_left A (ha.trans hcost)
  have hB : B * asize τ ≤ B * (2 * τ.piece.card + 1) := Nat.mul_le_mul_left B hsz
  have hA' : A * arunLCost (lpreMap M) c τ [] (rotPerm (lpreMap M)) ≤
      A * ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D)) := hA
  exact ⟨hbal.1, c', t, ex, by omega, hout, hmax⟩

end Head

end MfDrv

end BKMNW

end PlanarFlow
