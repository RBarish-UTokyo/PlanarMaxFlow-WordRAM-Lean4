module

public import PlanarFlow.BKMNW.NpNode

/-!
# The driver on the extended frame for any family of node subroutines, zero memory below `Wz`

* `cflowN_leaf` (at a leaf call the flow of `arunLN` is the leaf solver's, as for `arunL`);
* **`mfSpecRC_frameXN`**: the test, the leaf solver, the extended split (`SepPSpecX sepP`) and
  any combination meeting `NodeFieldZ` on `FInLX` meet `MfSpecRC` for the flows `cflowN NF` with
  `G = MemZ Wz` (`Wz < Hb`);
* **`mfDriveFrameXN`**: the fixed driver `driver mtProg mlProg (splitSX sepP) nodeS` from the
  root's extended frame and `MemZ Wz` ends with `FOutL` of `arunLN NF` and `MemZ Wz`, within
  `mcost + 2` steps;
* **`mfDriveFrameXN_step`**: the same with `nodeS = nodeSF (stepX segP (stepPO cntP fixP c2sP
  s2cP retP frmP))` and the hypotheses `SegPSpec segP`, the five `…PSpecN` (with `cntP` the
  program of `NpCnt.lean`, `CntPSpecS` discharged).
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

/-- At a leaf call the flow of `arunLN` is that of `arunL` (the leaf solver, no subroutine). -/
lemma cflowN_leaf (O : PlaneOracles.{w}) {NF : NFam M} {u : D → ℤ} {S T : Finset V}
    {Q : Finset D} {Hs : List (Finset V)} {σ : Perm D} :
    cflowN M NF u S T (.leaf Q, Hs, σ) = cflow M O u S T (.leaf Q, Hs, σ) := by
  show arunLN M NF u S T (.leaf Q) Hs σ = arunL M O u S T (.leaf Q) Hs σ
  rw [arunLN, arunL]

variable {NF : NFam M} {ds : DSys M} {Reach : MCall M → Prop} {gid : D → ℕ} {ν : V → ℕ}
  {u : D → ℤ} {S T : Finset V} {Z : ℕ} {I : Input} {W Wz Hb : ℕ} {sepP nodeS : Stmt}
  {sT : ℕ → ℕ → ℕ} {sR : ℕ → ℕ → ℕ → ℕ} {nc rN : MCall M → ℕ}

/-- **The test, the leaf solver and the extended split with the zero-memory invariant, any
combination meeting `NodeFieldZ`**, for the flows of `arunLN NF`. -/
theorem mfSpecRC_frameXN (hsep : SepPSpecX M ds Reach gid ν u S T Z I W sepP sT sR)
    (hReach : ∀ l r π Hs σ, Reach ((.node l r π, Hs, σ) : MCall M) →
      Reach (chL M l r π Hs σ) ∧ Reach (chR M l r π Hs σ)) (hZ : 2 * Z ≤ W) (hWz : Wz < Hb)
    (hnode : NodeFieldZ M (cflowN M NF u S T) I W Hb Wz nodeS (FInLX M ds Reach gid ν u S T Z)
      (FOutL M gid u S T Z) nc (rSpX M sR) rN) :
    MfSpecRC M (cflowN M NF u S T) I W Hb mtProg mlProg (splitSX sepP) nodeS (MemZ Wz)
      (FInLX M ds Reach gid ν u S T Z) (FOutL M gid u S T Z) (fun _ => 3)
      (fun x => 20 * (pdarts M x.1.piece x.2.1).card + 17) (scpX M sT) nc (fun _ => 0)
      (rSpX M sR) rN := by
  refine mfSpecRC_memZ (nodeS₀ := .skip) (nc₀ := fun _ => 0) (rN₀ := fun _ => W + 1) ?_ hWz
    hnode
  exact
    { g_stab := fun _ _ _ _ _ _ => trivial
      in_stab := fun _ _ _ _ _ h hm => h.stab hm
      out_stab := fun _ _ _ _ _ _ h hm => h.stab hm
      test := fun x d e h c hg hc r4 r5 r3 h1 h2 h3 hin =>
        mtProg_spec (Hb := 0) x d e h c hg hc r4 r5 r3 h1 h2 h3 hin.finL
      leaf := fun Q Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 _ hin => by
        rw [cflowN_leaf (planeOracles fun X => frRef X)]
        exact mlProg_spec (Hb := 0) _ hZ Q Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hin.finL
      split := fun l r π Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hrm hin =>
        mfSplit_specX (Hb := 0) hsep hReach l r π Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hrm hin
      node := fun l r π Hs σ d e bl el er c _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrm => by omega }

/-- **The fixed driver on the extended frame for any family of node subroutines**, from the
root's extended frame and `MemZ Wz` (`Wz < Hb`): `FOutL` of `arunLN NF` and `MemZ Wz`, within
`mcost + 2` steps. -/
theorem mfDriveFrameXN (hsep : SepPSpecX M ds Reach gid ν u S T Z I W sepP sT sR)
    (hReach : ∀ l r π Hs σ, Reach ((.node l r π, Hs, σ) : MCall M) →
      Reach (chL M l r π Hs σ) ∧ Reach (chR M l r π Hs σ)) (hZ : 2 * Z ≤ W) (hWz : Wz < Hb)
    (hnode : NodeFieldZ M (cflowN M NF u S T) I W Hb Wz nodeS (FInLX M ds Reach gid ν u S T Z)
      (FOutL M gid u S T Z) nc (rSpX M sR) rN)
    (hHb : 0 < Hb) (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D) {e h : ℕ} (c : Config)
    (hc : WordsBounded W c) (hz : MemZ Wz c) (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1)
    (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h) (m0 : c.nmem Hb = 0)
    (m1 : c.nmem (Hb + 1) = 0) (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hr : h + roomC M (fun _ => 0) (rSpX M sR) rN τ Hs σ ≤ W)
    (hin : FInLX M ds Reach gid ν u S T Z (τ, Hs, σ) (Hb + 5) e c) :
    ∃ c' t, Exec I W (driver mtProg mlProg (splitSX sepP) nodeS) c c' t ∧
      t ≤ mcost M (fun _ => 3) (fun x => 20 * (pdarts M x.1.piece x.2.1).card + 17) (scpX M sT) nc
        τ Hs σ + 2 ∧ MemZ Wz c' ∧
      FOutL M gid u S T Z (τ, Hs, σ) (arunLN M NF u S T τ Hs σ) (Hb + 5) e c' ∧
      HeapKeep Hb h Hb e c c' ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, g', hout, -, -, hk, ho⟩ :=
    mfDriveRC (mfSpecRC_frameXN hsep hReach hZ hWz hnode) hHb τ Hs σ c hc hz r0 r1 r2 r3 m0 m1
      m2 he hh hr hin
  exact ⟨c', t, ex, ht, g', hout, hk, ho⟩

variable {segP fixP c2sP s2cP retP frmP : Stmt} {sgT sgR rO : MCall M → ℕ}
  {fT rtT fmT : MCall M → ℕ → ℕ} {cT sTh : MCall M → ℕ → ℕ → ℕ}

/-- **The fixed driver with the node step `stepX segP (stepPO cntP …)`**: the remaining program
hypotheses are the separator (`SepPSpecX`), the parts (`SegPSpec`) and the five subroutine
specifications for the family `NF` (`cntP`, `NpCnt.lean`, meets its own). Steps: `mcost` with
`ncF` of `sgT + stTO … + 1`; room `sgR + rO` per node (`rO ≥ #Hs + 1`). -/
theorem mfDriveFrameXN_step (hsep : SepPSpecX M ds Reach gid ν u S T Z I W sepP sT sR)
    (hReach : ∀ l r π Hs σ, Reach ((.node l r π, Hs, σ) : MCall M) →
      Reach (chL M l r π Hs σ) ∧ Reach (chR M l r π Hs σ)) (hZ : 2 * Z ≤ W) (hWz : Wz < Hb)
    (hseg : SegPSpec M ds Reach gid ν u S T Z I W segP sgT sgR)
    (hrO : ∀ x : MCall M, x.2.1.length + 1 ≤ rO x)
    (hfx : FixPSpecN M NF Reach gid u S T Z I W Wz fixP fT rO)
    (hc2 : C2SPSpecN M NF Reach gid u S T Z I W Wz c2sP cT rO)
    (hs2 : S2CPSpecN M NF Reach gid u S T Z I W Wz s2cP sTh rO)
    (hrt : RetPSpecN M NF Reach gid u S T Z I W Wz retP rtT rO)
    (hfm : FrmPSpecN M NF Reach gid u S T Z I W Wz frmP fmT rO)
    (hHb : 0 < Hb) (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D) {e h : ℕ} (c : Config)
    (hc : WordsBounded W c) (hz : MemZ Wz c) (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1)
    (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h) (m0 : c.nmem Hb = 0)
    (m1 : c.nmem (Hb + 1) = 0) (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hr : h + roomC M (fun _ => 0) (rSpX M sR) (fun x => sgR x + rO x) τ Hs σ ≤ W)
    (hin : FInLX M ds Reach gid ν u S T Z (τ, Hs, σ) (Hb + 5) e c) :
    ∃ c' t, Exec I W (driver mtProg mlProg (splitSX sepP)
        (nodeSF (stepX segP (stepPO cntP fixP c2sP s2cP retP frmP)))) c c' t ∧
      t ≤ mcost M (fun _ => 3) (fun x => 20 * (pdarts M x.1.piece x.2.1).card + 17) (scpX M sT)
        (ncF M (fun x => sgT x + stTO M (cntT M) fT cT sTh rtT fmT x + 1)) τ Hs σ + 2 ∧
      MemZ Wz c' ∧
      FOutL M gid u S T Z (τ, Hs, σ) (arunLN M NF u S T τ Hs σ) (Hb + 5) e c' ∧
      HeapKeep Hb h Hb e c c' ∧ c'.output = c.output :=
  mfDriveFrameXN hsep hReach hZ hWz
    (nodeSF_specCX (stepX_spec hseg (stepPO_specN (cntP_spec Reach rO hrO) hfx hc2 hs2 hrt hfm))
      hWz) hHb τ Hs σ c hc hz r0 r1 r2 r3 m0 m1 m2 he hh hr hin

end MfDrv

end BKMNW

end PlanarFlow
