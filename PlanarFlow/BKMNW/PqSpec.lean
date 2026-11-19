module

public import PlanarFlow.BKMNW.PqChain

/-!
# `MfMainSpecS`: the hypothesis on the separator and node-step programs, scaled chain

`MfMainSpec` (`PpHyp.lean`) was stated against `mfMain_cMachXGE` (the costs `cMach C C₀` and one
node-step program `stepP`), and as the *conclusion* of that theorem. Here it is restated against
the successor of the chain, **`mfMain_cMachSGEPX`** (`PqChain.lean`: explicit pendant darts, the
scaled costs `cMachS C C₀`, the node step `stepX (segP sepX) (stepPO cntP fixP c2sP s2cP retP
frmP)`, the zero memory `≤ Wz` in and out), and as a hypothesis **only on the separator and
node-step programs**:

* **`SubSpecS … sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ`** (one instance): for every input,
  word bound `W ≥ 100000`, capacity bound `Z` (`2 Z ≤ W`, `(N + 2)(Z + 1) ≤ W`: the push-back programs need words of
  size about `(m + 1) Z`) and zero area `Wz ≥ WZ N Z`, there are
  an s-t flow choice `chs` (meeting `StChoice.OK`), an input `I₀` of the machine oracles, and
  cost and room functions such that the seven programs meet their specifications
  (`SepPSpecXL`, `SepPSpecXS`, `FixPSpecN`, `C2SPSpecN`, `S2CPSpecN`, `RetPSpecN`, `FrmPSpecN`),
  the separator steps cost `C n lg n + C h`, the node subroutines the budgets of `cMachS C C₀`,
  and the room per call is at most `R N Z`;
* **`MfMainSpecS`**: `SubSpecS` for every instance meeting the input conventions;
* `ntag_root_lpreX` (the root of the guarded decomposition of `lpreMapX` is a node);
* **`MfMainGoalS`** (the conclusion for one instance) and **`mfMainGoalS_of_sub`**: `SubSpecS`
  gives `MfMainGoalS` by `mfMain_cMachSGEPX` (`PkMin`, the looplessness of the preprocessed map and
  `ntag` are discharged).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver MfDrv
  PlanarSeparator.StDart

/-- **The max-flow program with the node-step programs** (the program of `mfMain_cMachSGEPX`). -/
def mfProgS (sepL sepX fixP c2sP s2cP retP frmP : Stmt) : Stmt :=
  .seq (.seq rfProg rxProg) (driver mtProg mlProg (splitSX (sepPX 100000 sepL))
    (nodeSF (stepX (segP sepX) (stepPO cntP fixP c2sP s2cP retP frmP))))

/-- **The root of the decomposition of `lpreMapX M ep hep` is a node** (a dart of `M` that is not
a loop given): `ntag_root_lpre` with explicit pendant darts. -/
theorem ntag_root_lpreX {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) (ep : PVert M → TDart M) (hep : ∀ w, (tnlMap M).tail (ep w) = w)
    (S T : Finset V) {x₀ : D} (hx₀ : x₀ ∈ nlDarts M)
    (pc : PcChoice _ _) (hpc : ∀ P Hs, pc.OK (lpreMapX M ep hep) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMapX M ep hep))
    (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W) :
    let L := lpreMapX M ep hep
    let gS := gSz L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000 (CInvS L (pendQ _))
    let gH := gHl L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000 (CInvS L (pendQ _))
    ntag (decS L (guardS L gS (spSR L pc sc (pendQ _))) (guardS L gH (spHR L pc sc (pendQ _)))
      (smD L pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot L (pendQ _)) 100000 univ [] (rootRot L (pendQ _)) true) = 1 := by
  intro L gS gH
  set y₀ : SDart (nlDarts M) := ⟨x₀, hx₀⟩
  have hloop := preP_loopless (nlMap_loopless (M := M)) hep
  by_cases hs : (univ : Finset (TDart M ⊕ (PVert M × Bool))).card ≤ 100000
  · rw [decS, ppIteT hs]
    rw [smD_ntag (hpc univ []).pick hloop univ []]
    refine ⟨⟨?_, ?_⟩, Or.inr (Or.inl ?_)⟩
    · have h3 : ({.inl (old y₀), .inl (up y₀), .inl (down y₀)} :
          Finset (TDart M ⊕ (PVert M × Bool))).card = 3 := by
        rw [card_insert_of_notMem (by simp), card_pair (by simp)]
      have := Finset.card_le_card (Finset.subset_univ ({.inl (old y₀), .inl (up y₀),
        .inl (down y₀)} : Finset (TDart M ⊕ (PVert M × Bool))))
      omega
    · refine ⟨.inr (.inr (((nlMap M).toSep nlMap_rotTrans).face y₀), false), ?_⟩
      simp only [smB, Finset.mem_filter, pdarts_nil, mem_univ, true_and]
      show Sum.inr (Sum.inr (((nlMap M).toSep nlMap_rotTrans).face y₀)) ∉ _
      simp [preTerm, hunion_nil']
    · simp [smY, hunion_nil']
  · have hne : Nonempty (SDart (nlDarts M)) := ⟨y₀⟩
    have hP := nlMap_isPlane hM hrot hface hx₀
    have hT := triMap_isPlane hP nlMap_rotTrans nlMap_faceTrans
    have hL : L.IsPlane := CombMap.pendant_isPlane hep hT
    have hLr : L.RotTrans := CombMap.pendant_rotTrans hep (triMap_rotTrans nlMap_rotTrans)
    have hLf : L.FaceTrans := CombMap.pendant_faceTrans hep (triMap_faceTrans nlMap_rotTrans)
    have hI := cinvS_pendant hep hT (triMap_rotTrans nlMap_rotTrans)
      (triMap_faceTrans nlMap_rotTrans)
      (fun x => PlanarSeparator.Map.stellar_φ_three _ x)
    obtain ⟨lt, rt, π, h⟩ := decS_guard_isNode (splitFnsS_lpreRX ep hep S T pc hpc sc hsc)
      (pcOK_univ hL hLr hLf _ _) hI (by omega) (by simp [nTouch]) (b := true)
    have := congrArg ntag h
    exact this

/-- **The hypothesis on the separator and node-step programs, for one instance** (see the module
docstring). `R N Z`: the room per call; `WZ N Z`: the least zero area the in-place subroutine calls
may ask for. -/
def SubSpecS {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] (M : CombMap D V F) (ep : PVert M → TDart M)
    (hep : ∀ w, (tnlMap M).tail (ep w) = w) (u : D → ℤ) (S T : Finset V) (N : ℕ)
    (en : ℕ → TDart M ⊕ (PVert M × Bool)) (d₀ : TDart M ⊕ (PVert M × Bool))
    (gid : TDart M ⊕ (PVert M × Bool) → ℕ) (ν : PVert M ⊕ PVert M → ℕ)
    (sepL sepX fixP c2sP s2cP retP frmP : Stmt) (C C₀ : ℕ) (R WZ : ℕ → ℕ → ℕ) : Prop :=
  let L := lpreMapX M ep hep
  let pc := pcChoiceE L (pendQ _) en N d₀
  let sc := fun Hs A W => scChoiceE L (sepC L en N (encB' W)) en N Hs A W
  let gS := gSz L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000 (CInvS L (pendQ _))
  let gH := gHl L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000 (CInvS L (pendQ _))
  let ds : DSys L := ⟨guardS L gS (spSR L pc sc (pendQ _)), guardS L gH (spHR L pc sc (pendQ _)),
    chRot L (pendQ _), 100000, pendQ _, pc.pick⟩
  let τ := decS L (guardS L gS (spSR L pc sc (pendQ _))) (guardS L gH (spHR L pc sc (pendQ _)))
    (smD L pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
    (chRot L (pendQ _)) 100000 univ [] (rootRot L (pendQ _)) true
  let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
  let S' := preTerm (nlTerm M S)
  let T' := preTerm (nlTerm M T)
  let Reach := Calls L τ [] (rotPerm L)
  let c := cMachS C C₀
  ∀ {I : Input} {W Z Wz : ℕ}, 100000 ≤ W → 2 * Z ≤ W → (N + 2) * (Z + 1) ≤ W → WZ N Z ≤ Wz →
  ∃ (I₀ : Input) (chs : (x : MCall L) → (h : PieceInv L x.1.piece x.2.1 x.2.2) →
      STFlow.StChoice (pmap h))
    (sTL sTX : ℕ → ℕ → ℕ) (sRL sRX : ℕ → ℕ → ℕ → ℕ) (rO : MCall L → ℕ)
    (fT rtT fmT : MCall L → ℕ → ℕ) (cT s2T : MCall L → ℕ → ℕ → ℕ) (RS RT : ℕ),
    SepPSpecXL L ds Reach gid ν u' S' T' Z I W sepL sTL sRL ∧
    SepPSpecXS L ds Reach gid ν u' S' T' Z I W sepX sTX sRX ∧
    (∀ x, Reach x → ∀ h, (chs x h).OK) ∧
    FixPSpecN L (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz fixP fT rO ∧
    C2SPSpecN L (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz c2sP cT rO ∧
    S2CPSpecN L (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz s2cP s2T rO ∧
    RetPSpecN L (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz retP rtT rO ∧
    FrmPSpecN L (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz frmP fmT rO ∧
    (∀ x : MCall L, x.2.1.length + 1 ≤ rO x) ∧
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      sTL (l.piece ∪ r.piece).card Hs.length + segT L sTX sRX (.node l r π, Hs, σ) ≤
        C * (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card + C * Hs.length) ∧
    (∀ l r π Hs σ (h : SCond L l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN L (NsStep.machNF gid I₀ chs (NsStep.pchCall gid)) u' S' T' l r π Hs σ
        h).L[j]? = some πj →
      fT (.node l r π, Hs, σ) j ≤ c.fixRun (pdarts L (l.piece ∪ r.piece) Hs).card
        πj.faces.card πj.k (psize L σ (pdarts L (l.piece ∪ r.piece) Hs)) ∧
      (∀ i, cT (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts L (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm L) (pdarts L (l.piece ∪ r.piece) Hs))
          (psize L σ (pdarts L (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      (∀ i, s2T (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts L (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm L) (pdarts L (l.piece ∪ r.piece) Hs))
          (psize L σ (pdarts L (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      rtT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts L (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm L) (pdarts L (l.piece ∪ r.piece) Hs))
          (psize L σ (pdarts L (l.piece ∪ r.piece) Hs)) +
        c.lin (psize L σ (pdarts L (l.piece ∪ r.piece) Hs)) ∧
      fmT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts L (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm L) (pdarts L (l.piece ∪ r.piece) Hs))
          (psize L σ (pdarts L (l.piece ∪ r.piece) Hs)) +
        c.lin (psize L σ (pdarts L (l.piece ∪ r.piece) Hs))) ∧
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) ∧
    (∀ x, Reach x → segR L sRX x + rO x ≤ RT) ∧ RS + RT ≤ R N Z

/-- **The hypothesis on the separator and node-step programs** (`SubSpecS` for every instance
meeting the input conventions: a plane map with transitive rotations and faces and a dart that
is not a loop, any pendant darts, nonnegative capacities, disjoint terminals, an enumeration `en`
of the `N` darts of `lpreMapX M ep hep` with `gid (en i) = i`, an injective vertex numbering `ν`
with the pendant vertices odd (`QPar`) and the darts listed by tails (`TailSorted`)). -/
def MfMainSpecS (sepL sepX fixP c2sP s2cP retP frmP : Stmt) (C C₀ : ℕ) (R WZ : ℕ → ℕ → ℕ) :
    Prop :=
  ∀ {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
    [DecidableEq F] (M : CombMap D V F), M.IsPlane → M.RotTrans → M.FaceTrans →
  ∀ (ep : PVert M → TDart M) (hep : ∀ w, (tnlMap M).tail (ep w) = w) {u : D → ℤ},
    (∀ d, 0 ≤ u d) → ∀ {S T : Finset V}, Disjoint S T → (nlDarts M).Nonempty →
  ∀ {N : ℕ} (en : ℕ → TDart M ⊕ (PVert M × Bool)) (d₀ : TDart M ⊕ (PVert M × Bool))
    {gid : TDart M ⊕ (PVert M × Bool) → ℕ} {ν : PVert M ⊕ PVert M → ℕ},
    Fintype.card (TDart M ⊕ (PVert M × Bool)) = N →
    (∀ y, ∃ i < N, en i = y) → (∀ i < N, gid (en i) = i) → Injective ν →
    QPar (pendQ (PVert M)) ν → TailSorted (lpreMapX M ep hep) gid ν →
    SubSpecS M ep hep u S T N en d₀ gid ν sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ

/-- **The conclusion of the max-flow program's theorem for one instance**, scaled chain, explicit
pendant darts: from a configuration holding the index arrays (as in `mfMain_cMachSGEPX`) with the
memory `≤ Wz` zero (`WZ N Z ≤ Wz`, `Wz + 2 < Hb`), the program `mfProgS …` runs within
`95 N + 200 + headline(machKS C, C₀) + 2000 (2N + 1) + 2` steps, leaves the memory `≤ Wz` zero
and the root's output frame `FOutL` of the flow `arunLN` of some node family `NF`, and
`nlRunNX … NF` is a maximum flow of `M`. -/
def MfMainGoalS {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] (M : CombMap D V F) (ep : PVert M → TDart M)
    (hep : ∀ w, (tnlMap M).tail (ep w) = w) (u : D → ℤ) (S T : Finset V) (N : ℕ)
    (en : ℕ → TDart M ⊕ (PVert M × Bool)) (d₀ : TDart M ⊕ (PVert M × Bool))
    (gid : TDart M ⊕ (PVert M × Bool) → ℕ) (ν : PVert M ⊕ PVert M → ℕ)
    (sepL sepX fixP c2sP s2cP retP frmP : Stmt) (C C₀ : ℕ) (R WZ : ℕ → ℕ → ℕ) : Prop :=
  let L := lpreMapX M ep hep
  let pc := pcChoiceE L (pendQ _) en N d₀
  let sc := fun Hs A W => scChoiceE L (sepC L en N (encB' W)) en N Hs A W
  let gS := gSz L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000 (CInvS L (pendQ _))
  let gH := gHl L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000 (CInvS L (pendQ _))
  let τ := decS L (guardS L gS (spSR L pc sc (pendQ _))) (guardS L gH (spHR L pc sc (pendQ _)))
    (smD L pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
    (chRot L (pendQ _)) 100000 univ [] (rootRot L (pendQ _)) true
  let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
  let S' := preTerm (nlTerm M S)
  let T' := preTerm (nlTerm M T)
  ∀ {I : Input} {W Hb Wz Z REVb SIGb CAPb KRb VTb RTb : ℕ}, 100000 ≤ W → 2 * Z ≤ W →
  (N + 2) * (Z + 1) ≤ W → WZ N Z ≤ Wz → 2 ≤ Hb → Wz + 2 < Hb →
  ∀ (c₀ : Config), WordsBounded W c₀ → MemZ Wz c₀ →
    c₀.nreg 6700 = N → c₀.nreg 6701 = REVb → c₀.nreg 6702 = SIGb → c₀.nreg 6703 = CAPb →
    c₀.nreg 6704 = KRb → c₀.nreg 6705 = 1 → c₀.nreg 6706 = Z → c₀.nreg 6707 = Hb →
    c₀.nmem (Hb - 1) = VTb → c₀.nmem (Hb - 1 - 1) = RTb →
    (∀ i < N, c₀.nmem (REVb + i) < N ∧ en (c₀.nmem (REVb + i)) = L.rev (en i)) →
    (∀ i < N, c₀.nmem (SIGb + i) < N ∧ en (c₀.nmem (SIGb + i)) = rotPerm L (en i)) →
    (∀ i < N, (c₀.nmem (CAPb + i) : ℤ) = u' (en i) ∧ c₀.nmem (CAPb + i) ≤ Z) →
    (∀ i < N, c₀.nmem (KRb + i) = lrk S' T' (hunion []) (L.tail (en i))) →
    (∀ i < N, c₀.nmem (VTb + i) = ν (L.tail (en i))) →
    (∀ i < N, en i ∈ pdarts L (core L (pendQ _) univ) [] →
      c₀.nmem (RTb + i) < N ∧ en (c₀.nmem (RTb + i)) = rootRot L (pendQ _) (en i)) →
    REVb + N ≤ Hb → SIGb + N ≤ Hb → CAPb + N ≤ Hb → KRb + N ≤ Hb → VTb + N ≤ Hb - 2 →
    RTb + N ≤ Hb - 2 →
    Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N + (2 * N + 1) * (110 * N + 80 + R N Z) ≤ W →
    τ.piece = univ ∧
    ∃ (NF : NFam L) (c' : Config) (t : ℕ),
      Exec I W (mfProgS sepL sepX fixP c2sP s2cP retP frmP) c₀ c' t ∧
      t ≤ 95 * N + 200 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machKS C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2) ∧ MemZ Wz c' ∧
      FOutL L gid u' S' T' Z (τ, [], rotPerm L) (arunLN L NF u' S' T' τ [] (rotPerm L))
        (Hb + 5) (Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N) c' ∧
      IsMax M u S T (nlRunNX M ep hep u S T τ NF)

set_option maxHeartbeats 4000000 in
/-- **`SubSpecS` gives `MfMainGoalS`** (by `mfMain_cMachSGEPX`; `PkMin`, the looplessness of
`lpreMapX` and the root tag are discharged here). -/
theorem mfMainGoalS_of_sub {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) (ep : PVert M → TDart M) (hep : ∀ w, (tnlMap M).tail (ep w) = w)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {x₀ : D} (hx₀ : x₀ ∈ nlDarts M) {N : ℕ} (en : ℕ → _) (d₀ : _) {gid : _ → ℕ} {ν : _ → ℕ}
    (hN : Fintype.card (TDart M ⊕ (PVert M × Bool)) = N)
    (hsurj : ∀ y, ∃ i < N, en i = y) (hgid : ∀ i < N, gid (en i) = i) (hν : Injective ν)
    {C C₀ : ℕ} (hC : 1 ≤ C) {sepL sepX fixP c2sP s2cP retP frmP : Stmt} {R WZ : ℕ → ℕ → ℕ}
    (hsub : SubSpecS M ep hep u S T N en d₀ gid ν sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ) :
    MfMainGoalS M ep hep u S T N en d₀ gid ν sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ := by
  unfold MfMainGoalS
  intro L pc sc gS gH τ u' S' T' I W Hb Wz Z REVb SIGb CAPb KRb VTb RTb hW hZ hNZ hWZ hHb hWz c₀ hc₀
    hz r0 r1 r2 r3 r4 r5 r6 r7 hv hrt hrev hsig hcap hkr hvt hst i1 i2 i3 i4 i5 i6 hroom
  obtain ⟨I₀, chs, sTL, sTX, sRL, sRX, rO, fT, rtT, fmT, cT, s2T, RS, RT, hsL, hsX, hok, hfx,
    hc2, hs2, hrt', hfm, hrO, hsT, hcost, hsR, hrT, hR⟩ :=
    hsub (I := I) (W := W) (Z := Z) (Wz := Wz) hW hZ hNZ hWZ
  have hpc : ∀ P Hs, pc.OK L (pendQ _) P Hs := fun P Hs => pcChoiceE_ok hsurj d₀ _ P Hs
  have hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W := fun Hs A W => scChoiceE_ok hsurj
    (sepC_ok (preP_loopless nlMap_loopless hep) en N (encB' W) Hs) A W
  have hbal := (maxflow_plane_cost_decGX hM hrot hface hx₀ ep hep hu hST pc hpc sc hsc
    (cMachS_bounds C C₀)).1
  have hNc : τ.piece.card = N := by
    have h1 : τ.piece = univ := hbal.1
    rw [h1, card_univ]; exact hN
  have hroom' : Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N + (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ W := by
    have : (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ (2 * N + 1) * (110 * N + 80 + R N Z) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hpk := pkMin_pcChoiceE (M := L) (Q := pendQ _) hsurj hgid d₀
  have hsurj' : ∀ y, ∃ i < N, en i = y := hsurj
  rw [← hNc] at hsurj' hgid r0 hrev hsig hcap hkr hvt hst i1 i2 i3 i4 i5 i6 hroom' hsR
  have r5' : c₀.nreg 6705 = ntag τ := by
    rw [r5]; exact (ntag_root_lpreX hM hrot hface ep hep S T hx₀ pc hpc sc hsc).symm
  have key := mfMain_cMachSGEPX hM hrot hface ep hep hu hST en hsurj d₀ hx₀ I₀ hC
    (I := I) (W := W) (Hb := Hb) (Wz := Wz) (Z := Z) (gid := gid) (ν := ν) (sepL := sepL)
    (sepX := sepX) (fixP := fixP) (c2sP := c2sP) (s2cP := s2cP) (retP := retP) (frmP := frmP)
    (chs := chs) hZ hsL hsX hok hfx hc2 hs2 hrt' hfm hrO hpk hν
    (preP_loopless nlMap_loopless hep) hW hsT hcost hsR hrT
    hsurj' hgid hHb hWz c₀ hc₀ hz r0 r1 r2 r3 r4 r5' r6 r7 hv hrt hrev hsig hcap hkr hvt hst
    i1 i2 i3 i4 i5 i6 hroom'
  obtain ⟨hp, c', t, ex, ht, hz', hout, hmax⟩ := key
  refine ⟨hp, _, c', t, ex, ?_, hz', ?_, hmax⟩
  · rw [← hNc]; exact ht
  · rw [← hNc]; exact hout

end Pp

end BKMNW

end PlanarFlow
