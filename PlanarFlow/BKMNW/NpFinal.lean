module

public import PlanarFlow.BKMNW.NpMain
public import PlanarFlow.BKMNW.NpPushC
public import PlanarFlow.BKMNW.NpSeg

/-!
# The whole max-flow program with the machine's node subroutines and the parts by `segP`

**`mfMain_cMachXGEF`**: `mfMain_cMachXGEN` with
* the parts of the separator by **`segP sepX`** (`NpSeg.lean`: rerun the separator `sepX` at the
  node, copy its `SegsOut`; `SegPSpec` from **`SepPSpecXS sepX`**, `segP_spec`, steps
  `segT = sTX n k + 13 sRX n m k + 30`, room `segR = 1 + sRX n m k`);
* the family **`NsStep.machNF gid I₀ chs pch`** (Klein's MSSP, `frRef`, the machine's
  negative-length shortest paths, the s-t flow and the push-back of explicit choices;
  `NSpecOn` by `nSpecOn_machNF` from the validity of the choices).

The program `(rfProg ; rxProg) ; driver mtProg mlProg (splitSX (sepPX 100000 sepL))
(nodeSF (stepX (segP sepX) (stepPO cntP fixP c2sP s2cP retP frmP)))` within
`95 N + 200 + headline(cMach C C₀) + 2000 (2 N + 1) + 2` steps computes a maximum flow
(`IsMax M u S T (nlRunN M u S T τ (machNF …))`). Remaining hypotheses: the two separator programs
(`SepPSpecXL sepL`, `SepPSpecXS sepX`), the validity of the machine's choices (`StChoice.OK`,
`PushSpec`), and the five subroutine programs (`FixPSpecN` … `FrmPSpecN` relative to `machNF`)
with their costs in `cMach`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver

universe w

section Head

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The whole program with the machine's node subroutines and the parts by `segP`** (see the
module docstring). -/
theorem mfMain_cMachXGEF (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) (I₀ : Input)
    {C C₀ : ℕ} (hC : 200 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Wz Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ}
    {sepL sepX fixP c2sP s2cP retP frmP : Stmt}
    {chs : (x : MCall (lpreMap M)) → (h : PieceInv (lpreMap M) x.1.piece x.2.1 x.2.2) →
      STFlow.StChoice (pmap h)}
    {pch : (x : MCall (lpreMap M)) → (h : PieceInv (lpreMap M) x.1.piece x.2.1 x.2.2) →
      PushFn (Orbit.SDart (pdarts (lpreMap M) x.1.piece x.2.1))
        (Orbit.SVert x.2.2 (pdarts (lpreMap M) x.1.piece x.2.1))}
    {sTL sTX : ℕ → ℕ → ℕ} {sRL sRX : ℕ → ℕ → ℕ → ℕ} {rO : MCall (lpreMap M) → ℕ}
    {fT rtT fmT : MCall (lpreMap M) → ℕ → ℕ} {cT s2T : MCall (lpreMap M) → ℕ → ℕ → ℕ}
    {RS RT : ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepC (lpreMap M) e n (encB' W)) e n Hs A W
    let gS := gSz (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMap M) (pendQ _))
    let gH := gHl (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMap M) (pendQ _))
    let ds : DSys (lpreMap M) := ⟨guardS (lpreMap M) gS (spSR (lpreMap M) pc sc (pendQ _)),
      guardS (lpreMap M) gH (spHR (lpreMap M) pc sc (pendQ _)),
      chRot (lpreMap M) (pendQ _), 100000, pendQ _, pc.pick⟩
    let τ := decS (lpreMap M) (guardS (lpreMap M) gS (spSR (lpreMap M) pc sc (pendQ _)))
      (guardS (lpreMap M) gH (spHR (lpreMap M) pc sc (pendQ _)))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMap M) τ [] (rotPerm (lpreMap M))
    let N := τ.piece.card
    let c := cMach C C₀
    SepPSpecXL (lpreMap M) ds Reach gid ν u' S' T' Z I W sepL sTL sRL →
    SepPSpecXS (lpreMap M) ds Reach gid ν u' S' T' Z I W sepX sTX sRX →
    (∀ x, Reach x → ∀ h, (chs x h).OK) →
    (∀ x, Reach x → ∀ h, (pmap h).IsPlane → PushSpec (pmap h) (pch x h)) →
    FixPSpecN (lpreMap M) (NsStep.machNF gid I₀ chs pch)
      Reach gid u' S' T' Z I W Wz fixP fT rO →
    C2SPSpecN (lpreMap M) (NsStep.machNF gid I₀ chs pch)
      Reach gid u' S' T' Z I W Wz c2sP cT rO →
    S2CPSpecN (lpreMap M) (NsStep.machNF gid I₀ chs pch)
      Reach gid u' S' T' Z I W Wz s2cP s2T rO →
    RetPSpecN (lpreMap M) (NsStep.machNF gid I₀ chs pch)
      Reach gid u' S' T' Z I W Wz retP rtT rO →
    FrmPSpecN (lpreMap M) (NsStep.machNF gid I₀ chs pch)
      Reach gid u' S' T' Z I W Wz frmP fmT rO →
    (∀ x : MCall (lpreMap M), x.2.1.length + 1 ≤ rO x) →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMap M).head y ≠ (lpreMap M).tail y) →
    100000 ≤ W →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      sTL (l.piece ∪ r.piece).card Hs.length + segT (lpreMap M) sTX sRX (.node l r π, Hs, σ) ≤
        C * (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card + C * Hs.length) →
    (∀ l r π Hs σ (h : SCond (lpreMap M) l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN (lpreMap M) (NsStep.machNF gid I₀ chs pch) u' S' T' l r π Hs σ h).L[j]? = some πj →
      fT (.node l r π, Hs, σ) j ≤ c.fixRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
        πj.faces.card πj.k (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) ∧
      (∀ i, cT (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      (∀ i, s2T (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      rtT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) ∧
      fmT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))) →
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) → (∀ x, Reach x → segR (lpreMap M) sRX x + rO x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb VTb RTb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 2 ≤ Hb → Wz + 2 < Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    MemZ Wz c₀ →
    c₀.nreg 6700 = N → c₀.nreg 6701 = REVb → c₀.nreg 6702 = SIGb → c₀.nreg 6703 = CAPb →
    c₀.nreg 6704 = KRb → c₀.nreg 6705 = ntag τ → c₀.nreg 6706 = Z → c₀.nreg 6707 = Hb →
    c₀.nmem (Hb - 1) = VTb → c₀.nmem (Hb - 1 - 1) = RTb →
    (∀ i < N, c₀.nmem (REVb + i) < N ∧ en (c₀.nmem (REVb + i)) = (lpreMap M).rev (en i)) →
    (∀ i < N, c₀.nmem (SIGb + i) < N ∧
      en (c₀.nmem (SIGb + i)) = rotPerm (lpreMap M) (en i)) →
    (∀ i < N, (c₀.nmem (CAPb + i) : ℤ) = u' (en i) ∧ c₀.nmem (CAPb + i) ≤ Z) →
    (∀ i < N, c₀.nmem (KRb + i) = lrk S' T' (hunion []) ((lpreMap M).tail (en i))) →
    (∀ i < N, c₀.nmem (VTb + i) = ν ((lpreMap M).tail (en i))) →
    (∀ i < N, en i ∈ pdarts (lpreMap M) (core (lpreMap M) (pendQ _) univ) [] →
      c₀.nmem (RTb + i) < N ∧ en (c₀.nmem (RTb + i)) = rootRot (lpreMap M) (pendQ _) (en i)) →
    REVb + N ≤ Hb → SIGb + N ≤ Hb → CAPb + N ≤ Hb → KRb + N ≤ Hb → VTb + N ≤ Hb - 2 →
    RTb + N ≤ Hb - 2 →
    Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N + (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq (.seq rfProg rxProg) (driver mtProg mlProg
        (splitSX (sepPX 100000 sepL))
        (nodeSF (stepX (segP sepX) (stepPO cntP fixP c2sP s2cP retP frmP))))) c₀ c' t ∧
      t ≤ 95 * N + 200 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2) ∧ MemZ Wz c' ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunLN (lpreMap M) (NsStep.machNF gid I₀ chs pch) u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) (Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N) c' ∧
      IsMax M u S T (nlRunN M u S T τ (NsStep.machNF gid I₀ chs pch)) := by
  intro pc sc gS gH ds τ u' S' T' Reach N c hsL hsX hok hpush
  exact mfMain_cMachXGEN hM hrot hface hu hST e hsurj d₀ hx₀ hC hC₀ hZ hsL (segP_spec hsX)
    (NsStep.nSpecOn_machNF gid I₀ chs pch Reach hok hpush)


/-- **The whole program with the machine's node subroutines, the push-back of `NsStep.pchCall`
and the parts by `segP`** (`mfMain_cMachXGEF` with `pch = NsStep.pchCall gid`; its `PushSpec`
hypothesis discharged by `NsStep.pushSpec_pchCall`). -/
theorem mfMain_cMachXGEP (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) (I₀ : Input)
    {C C₀ : ℕ} (hC : 200 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Wz Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ}
    {sepL sepX fixP c2sP s2cP retP frmP : Stmt}
    {chs : (x : MCall (lpreMap M)) → (h : PieceInv (lpreMap M) x.1.piece x.2.1 x.2.2) →
      STFlow.StChoice (pmap h)}
    {sTL sTX : ℕ → ℕ → ℕ} {sRL sRX : ℕ → ℕ → ℕ → ℕ} {rO : MCall (lpreMap M) → ℕ}
    {fT rtT fmT : MCall (lpreMap M) → ℕ → ℕ} {cT s2T : MCall (lpreMap M) → ℕ → ℕ → ℕ}
    {RS RT : ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepC (lpreMap M) e n (encB' W)) e n Hs A W
    let gS := gSz (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMap M) (pendQ _))
    let gH := gHl (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMap M) (pendQ _))
    let ds : DSys (lpreMap M) := ⟨guardS (lpreMap M) gS (spSR (lpreMap M) pc sc (pendQ _)),
      guardS (lpreMap M) gH (spHR (lpreMap M) pc sc (pendQ _)),
      chRot (lpreMap M) (pendQ _), 100000, pendQ _, pc.pick⟩
    let τ := decS (lpreMap M) (guardS (lpreMap M) gS (spSR (lpreMap M) pc sc (pendQ _)))
      (guardS (lpreMap M) gH (spHR (lpreMap M) pc sc (pendQ _)))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMap M) τ [] (rotPerm (lpreMap M))
    let N := τ.piece.card
    let c := cMach C C₀
    SepPSpecXL (lpreMap M) ds Reach gid ν u' S' T' Z I W sepL sTL sRL →
    SepPSpecXS (lpreMap M) ds Reach gid ν u' S' T' Z I W sepX sTX sRX →
    (∀ x, Reach x → ∀ h, (chs x h).OK) →
    FixPSpecN (lpreMap M) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz fixP fT rO →
    C2SPSpecN (lpreMap M) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz c2sP cT rO →
    S2CPSpecN (lpreMap M) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz s2cP s2T rO →
    RetPSpecN (lpreMap M) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz retP rtT rO →
    FrmPSpecN (lpreMap M) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz frmP fmT rO →
    (∀ x : MCall (lpreMap M), x.2.1.length + 1 ≤ rO x) →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMap M).head y ≠ (lpreMap M).tail y) →
    100000 ≤ W →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      sTL (l.piece ∪ r.piece).card Hs.length + segT (lpreMap M) sTX sRX (.node l r π, Hs, σ) ≤
        C * (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card + C * Hs.length) →
    (∀ l r π Hs σ (h : SCond (lpreMap M) l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN (lpreMap M) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid)) u' S' T' l r π Hs σ
        h).L[j]? = some πj →
      fT (.node l r π, Hs, σ) j ≤ c.fixRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
        πj.faces.card πj.k (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) ∧
      (∀ i, cT (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      (∀ i, s2T (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      rtT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) ∧
      fmT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))) →
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) → (∀ x, Reach x → segR (lpreMap M) sRX x + rO x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb VTb RTb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 2 ≤ Hb → Wz + 2 < Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    MemZ Wz c₀ →
    c₀.nreg 6700 = N → c₀.nreg 6701 = REVb → c₀.nreg 6702 = SIGb → c₀.nreg 6703 = CAPb →
    c₀.nreg 6704 = KRb → c₀.nreg 6705 = ntag τ → c₀.nreg 6706 = Z → c₀.nreg 6707 = Hb →
    c₀.nmem (Hb - 1) = VTb → c₀.nmem (Hb - 1 - 1) = RTb →
    (∀ i < N, c₀.nmem (REVb + i) < N ∧ en (c₀.nmem (REVb + i)) = (lpreMap M).rev (en i)) →
    (∀ i < N, c₀.nmem (SIGb + i) < N ∧
      en (c₀.nmem (SIGb + i)) = rotPerm (lpreMap M) (en i)) →
    (∀ i < N, (c₀.nmem (CAPb + i) : ℤ) = u' (en i) ∧ c₀.nmem (CAPb + i) ≤ Z) →
    (∀ i < N, c₀.nmem (KRb + i) = lrk S' T' (hunion []) ((lpreMap M).tail (en i))) →
    (∀ i < N, c₀.nmem (VTb + i) = ν ((lpreMap M).tail (en i))) →
    (∀ i < N, en i ∈ pdarts (lpreMap M) (core (lpreMap M) (pendQ _) univ) [] →
      c₀.nmem (RTb + i) < N ∧ en (c₀.nmem (RTb + i)) = rootRot (lpreMap M) (pendQ _) (en i)) →
    REVb + N ≤ Hb → SIGb + N ≤ Hb → CAPb + N ≤ Hb → KRb + N ≤ Hb → VTb + N ≤ Hb - 2 →
    RTb + N ≤ Hb - 2 →
    Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N + (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq (.seq rfProg rxProg) (driver mtProg mlProg
        (splitSX (sepPX 100000 sepL))
        (nodeSF (stepX (segP sepX) (stepPO cntP fixP c2sP s2cP retP frmP))))) c₀ c' t ∧
      t ≤ 95 * N + 200 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2) ∧ MemZ Wz c' ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunLN (lpreMap M) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid)) u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) (Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N) c' ∧
      IsMax M u S T (nlRunN M u S T τ (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))) := by
  intro pc sc gS gH ds τ u' S' T' Reach N c hsL hsX hok
  exact mfMain_cMachXGEF hM hrot hface hu hST e hsurj d₀ hx₀ I₀ hC hC₀ hZ hsL hsX hok
    (fun x _ h hpl => NsStep.pushSpec_pchCall gid x h hpl)

end Head

end MfDrv

end BKMNW

end PlanarFlow
