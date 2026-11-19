module

public import PlanarFlow.BKMNW.MfJoin

/-!
# The combination `nodeS` of the max-flow driver: the join, then the step

At a node call `x = (.node l r π, Hs, σ)` the flow of the recursion is (`arunL`)

  `cflow x = sepStep (impl …) u S T (pholes …) univ (segsP …) (joinFlow (cflow chL) (cflow chR))`

on the piece map of `x` (when `PieceInv` and `SegIn` hold, `0` otherwise). The combination is
split in two:

* the **join** `njProg` (`PlanarFlow/BKMNW/MfJoin.lean`, `njProg_join`): the sum
  `joinFlow (cflow chL) (cflow chR)` of the children's flows into the parent's array `FL`
  (`44 m + 59` steps);
* the **step** `stepP`, a parameter with the specification **`StepPSpec`**: from the parent's frame
  (`Lay`) holding the joined flow in `FL`, write `cflow x` into `FL` within `stT x` steps, using
  memory from `b` on (`b + rT x ≤ W`, `b` the heap top above the parent's frame), memory and reals
  below `b` kept off `FL`, the registers of the driver (`3000 … 3012`) and the output kept.
  `stepP` is the `sepStep` of the article: FixConservationOnPath, the hole loop and the two
  push-backs on each part of the separator; it can recompute the separator by `sepP`
  (`SepPSpec` holds at the parent's frame, still `FInL`).

**`nodeSF_spec`**: `nodeSF stepP = njProg ; stepP` meets `NodeSpecF` (the field `node` of
`MfSpecR` on the frames) with `nc x = 44 m + 59 + stT x` and the room `rN = rT`.
**`mfDriveFrame_decM2`**: the fixed program `driver mtProg mlProg (splitS sepP) (nodeSF stepP)`
on the decomposition of the headline theorem, with `SepPSpec sepP` and `StepPSpec stepP` the
hypotheses on the two parameters.
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
/-- **The specification of the step** (see the module docstring): at a node call of `Reach` with
the invariants of the calls, from the parent's frame holding the sum of the children's flows,
the flow `cflow x` of the call in the parent's array `FL`. -/
def StepPSpec (O : PlaneOracles.{w}) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (stepP : Stmt) (stT rT : MCall M → ℕ) :
    Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e b m : ℕ)
    (en : ℕ → D) (c : Config),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem → d + fsz m ≤ e →
    (∀ i < m, (c.nmem (d + 4 + 6 * m + i) : ℤ) =
      Z + fext (joinFlow (B := pdarts M (l.piece ∪ r.piece) Hs)
        (cflow M O u S T (chL M l r π Hs σ)) (cflow M O u S T (chR M l r π Hs σ))) (en i)) →
    WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = b + 5 → e ≤ b →
    b + rT (.node l r π, Hs, σ) ≤ W →
    ∃ c' t, Exec I W stepP c c' t ∧ t ≤ stT (.node l r π, Hs, σ) ∧ DRegKeep c c' ∧
      (∀ a, a < b → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      ∀ i < m, (c'.nmem (d + 4 + 6 * m + i) : ℤ) =
        Z + fext (cflow M O u S T (.node l r π, Hs, σ)) (en i)

/-- **The combination**: the join, then the step. -/
def nodeSF (stepP : Stmt) : Stmt := .seq njProg stepP

variable (M) in
/-- The steps of the combination: `44 m + 59` for the join, `stT x` for the step. -/
noncomputable def ncF (stT : MCall M → ℕ) (x : MCall M) : ℕ :=
  44 * (pdarts M x.1.piece x.2.1).card + 59 + stT x

variable {O : PlaneOracles.{w}} {Reach : MCall M → Prop} {gid : D → ℕ} {u : D → ℤ}
  {S T : Finset V} {Z : ℕ} {I : Input} {W Hb : ℕ} {stepP : Stmt} {stT rT rS : MCall M → ℕ}

/-- **The combination meets its field of `MfSpecR`** on the frames, for any step meeting
`StepPSpec`. -/
theorem nodeSF_spec (hst : StepPSpec M O Reach gid u S T Z I W stepP stT rT) :
    NodeSpecF M O Reach gid u S T Z I W Hb (nodeSF stepP) (ncF M stT) rS rT := by
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

end Gen

section Head

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The fixed driver program with the concrete join, on the decomposition of the headline
theorem**: `driver mtProg mlProg (splitS sepP) (nodeSF stepP)`, with `SepPSpec sepP` and
`StepPSpec stepP` (the separator program and the step `sepStep` of each node call), the per-call
costs against the charges of `arunLCost` (`hl` at the leaves; `hn` at the nodes, with the
`44 m + 59` steps of the join), the room `rSp sR x + rT x ≤ R`, `h + (2 m + 1) R ≤ W` and the
root frame: the program reaches `FOutL` of the root flow within `A · (headline) + B · (2 m + 1) +
2` steps, and the flow is a maximum flow. -/
theorem mfDriveFrame_decM2 (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _)
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    {I : Input} {W Hb Z : ℕ} {gid : _ → ℕ} {sepP stepP : Stmt} {sT : ℕ → ℕ} {sR : ℕ → ℕ → ℕ}
    {stT rT : MCall (lpreMap M) → ℕ} {A B R : ℕ} (hZ : 2 * Z ≤ W) :
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
    StepPSpec (lpreMap M) (planeOracles fun X => frRef X) Reach gid u' S' T' Z I W stepP stT rT →
    (∀ Q Hs, 3 + (20 * (pdarts (lpreMap M) Q Hs).card + 17) + 20 ≤
      A * (c.leaf (pdarts (lpreMap M) Q Hs).card + 4 * c.lin (Q.card + Hs.length)) + B) →
    (∀ l r π Hs σ, 3 + scp (lpreMap M) sT (.node l r π, Hs, σ) +
      (44 * (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card + 59 + stT (.node l r π, Hs, σ)) +
      80 ≤ A * nodeCharge (lpreMap M) c l r π Hs σ + B) →
    (∀ x, rSp (lpreMap M) sR x + rT x ≤ R) →
    0 < Hb → ∀ {eF h : ℕ} (c₀ : Config), WordsBounded W c₀ → c₀.nreg 3000 = 0 →
    c₀.nreg 3001 = 1 → c₀.nreg 3002 = Hb → c₀.nreg 3003 = h → c₀.nmem Hb = 0 →
    c₀.nmem (Hb + 1) = 0 → c₀.nmem (Hb + 2) = eF → Hb + 5 ≤ eF → eF ≤ h →
    h + (2 * τ.piece.card + 1) * R ≤ W →
    FInL (lpreMap M) Reach gid u' S' T' Z (τ, [], rotPerm (lpreMap M)) (Hb + 5) eF c₀ →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (driver mtProg mlProg (splitS sepP) (nodeSF stepP)) c₀ c' t ∧
      t ≤ A * ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D)) +
        B * (2 * τ.piece.card + 1) + 2 ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunL (lpreMap M) (planeOracles fun X => frRef X) u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) eF c' ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) := by
  intro pc sc τ u' S' T' Reach hsep hstep hl hn hR
  exact mfDriveFrame_decM hM hrot hface hu hST e hsurj d₀ hc (nodeS := nodeSF stepP)
    (nc := ncF (lpreMap M) stT) (rN := rT) hZ hsep (nodeSF_spec hstep) hl
    (fun l r π Hs σ => by have := hn l r π Hs σ; unfold ncF; simp only [ADec.piece]; omega) hR

end Head

end MfDrv

end BKMNW

end PlanarFlow
