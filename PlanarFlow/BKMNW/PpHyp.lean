module

public import PlanarFlow.BKMNW.PpMap
public import PlanarFlow.BKMNW.LgWtF
public import PlanarFlow.BKMNW.PkMinE

/-!
# The max-flow program's theorem, as a hypothesis on explicit pendant darts

The maximum-flow pipeline (`PpPipe.lean`) runs the preprocessing programs, then the max-flow program
`rfProg ; rxProg ; driver … (splitSX (sepPX 100000 sepL)) (nodeSF stepP)` of `mfMain_cMachXGE`.
Its theorem is not yet unconditional: `SepPSpecXL` (the large-piece separator `sepL`) and
`StepPSpec` (the node step `stepP`) are being discharged. This file states, as a `Prop`, what that
theorem gives once they are, **for the preprocessed map with explicit pendant darts**
(`lpreMapX`, `PpMap.lean`: the arrays of `lpreMap M` itself cannot be written by a program,
because its pendant darts are chosen by `Quotient.out`):

* **`MfMainSpec sepL stepP C C₀ R`**: for every plane map with transitive rotations and faces and a
  dart that is not a loop, every choice `e` of the pendant darts, nonnegative capacities and
  disjoint terminals, every enumeration `en` of the darts of `lpreMapX M e he` with `gid (en i) = i`
  and every injective vertex numbering `ν` meeting the conventions of the large-piece separator
  (`QPar (pendQ _) ν`: the pendant vertices odd; `TailSorted`: the darts listed by tails), from a
  configuration holding the index arrays as in `mfMain_cMachXGE`, the program runs within
  `95 N + 200 + headline(machK C, C₀) + 2000 (2N + 1) + 2` steps, leaves the root's output frame
  `FOutL` (the flow `arunL` of the decomposition), and `nlRunX` is a maximum flow of `M`. The
  room of the subroutines is `R N` words per call (`RS + RT` of `mfMain_cMachXGE`). The hypotheses
  `PkMin` and the looplessness of the preprocessed map of `mfMain_cMachXGE` are dropped: they
  follow (`pkMin_pcChoiceE`, `lpreMapX_loopless`).
* **`mfMainSpec_out`** (consistency): for the choices of `Quotient.out`, the conclusion of
  `MfMainSpec` follows from `mfMain_cMachXGE` and its two remaining hypotheses (`SepPSpecXL`,
  `StepPSpec` and their cost bounds); so `MfMainSpec` is `mfMain_cMachXGE`'s conclusion with the
  pendant darts made explicit, `QPar` and `TailSorted` added to the input conventions, and the
  two subroutine hypotheses discharged.
* `lpreMapX_loopless`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver MfDrv
  PlanarSeparator.StDart

/-- **The preprocessed map with explicit pendant darts has no loop.** -/
theorem lpreMapX_loopless {D V : Type} {F : Type} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] (M : CombMap D V F) (e : PVert M → TDart M)
    (he : ∀ w, (tnlMap M).tail (e w) = w) (y : _) :
    (lpreMapX M e he).head y ≠ (lpreMapX M e he).tail y := by
  rcases y with t | ⟨w, _ | _⟩
  · exact fun h => triMap_loopless nlMap_rotTrans nlMap_loopless t (Sum.inl.inj h)
  · exact fun h => by cases h
  · exact fun h => by cases h

/-- **The root of the decomposition of `lpreMap M` is a node** (for a map with a dart that is not
a loop): when it is small, `smD` splits it (`smD_ntag`: more than two darts, and a dart leaving the
centre of a face, which is not a terminal); when it is large, the guarded split answers
(`decS_guard_isNode`). -/
theorem ntag_root_lpre {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) (S T : Finset V) {x₀ : D} (hx₀ : x₀ ∈ nlDarts M)
    (pc : PcChoice _ _) (hpc : ∀ P Hs, pc.OK (lpreMap M) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMap M)) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W) :
    let L := lpreMap M
    let gS := gSz L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000 (CInvS L (pendQ _))
    let gH := gHl L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000 (CInvS L (pendQ _))
    ntag (decS L (guardS L gS (spSR L pc sc (pendQ _))) (guardS L gH (spHR L pc sc (pendQ _)))
      (smD L pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot L (pendQ _)) 100000 univ [] (rootRot L (pendQ _)) true) = 1 := by
  intro L gS gH
  set y₀ : SDart (nlDarts M) := ⟨x₀, hx₀⟩
  have hloop := preMap_loopless (hrot := nlMap_rotTrans) (nlMap_loopless (M := M)) (nlE_tail (M := M))
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
    have he := triE_tail (hrot := nlMap_rotTrans) (nlE_tail (M := M))
    have hL : L.IsPlane := CombMap.pendant_isPlane he hT
    have hLr : L.RotTrans := CombMap.pendant_rotTrans he (triMap_rotTrans nlMap_rotTrans)
    have hLf : L.FaceTrans := CombMap.pendant_faceTrans he (triMap_faceTrans nlMap_rotTrans)
    have hI := cinvS_pendant he hT (triMap_rotTrans nlMap_rotTrans) (triMap_faceTrans nlMap_rotTrans)
      (fun x => PlanarSeparator.Map.stellar_φ_three _ x)
    obtain ⟨lt, rt, π, h⟩ := decS_guard_isNode (splitFnsS_lpreR S T pc hpc sc hsc)
      (pcOK_univ hL hLr hLf _ _) hI (by omega) (by simp [nTouch]) (b := true)
    have := congrArg ntag h
    exact this

/-- **The conclusion of the max-flow program's theorem for one instance**, with explicit pendant
darts (see the module docstring). -/
def MfMainGoal {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] (M : CombMap D V F) (e : PVert M → TDart M)
    (he : ∀ w, (tnlMap M).tail (e w) = w) (u : D → ℤ) (S T : Finset V) (N : ℕ)
    (en : ℕ → TDart M ⊕ (PVert M × Bool)) (d₀ : TDart M ⊕ (PVert M × Bool))
    (gid : TDart M ⊕ (PVert M × Bool) → ℕ) (ν : PVert M ⊕ PVert M → ℕ) (sepL stepP : Stmt)
    (C C₀ : ℕ) (R : ℕ → ℕ) : Prop :=
  let L := lpreMapX M e he
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
  ∀ {I : Input} {W Hb Z REVb SIGb CAPb KRb VTb RTb : ℕ}, 100000 ≤ W → 2 * Z ≤ W → 2 ≤ Hb →
  ∀ (c₀ : Config), WordsBounded W c₀ →
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
    Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N + (2 * N + 1) * (110 * N + 80 + R N) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq (.seq rfProg rxProg)
        (driver mtProg mlProg (splitSX (sepPX 100000 sepL)) (nodeSF stepP))) c₀ c' t ∧
      t ≤ 95 * N + 200 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2) ∧
      FOutL L gid u' S' T' Z (τ, [], rotPerm L)
        (arunL L (planeOracles fun X => frRef X) u' S' T' τ [] (rotPerm L))
        (Hb + 5) (Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N) c' ∧
      IsMax M u S T (nlRunX M e he u S T τ (planeOracles fun X => frRef X))

/-- **The max-flow program's theorem, unconditional form, with explicit pendant darts**: the
programs `sepL`, `stepP` (constants `C`, `C₀`, room `R N` per call) meet `MfMainGoal` on every
instance meeting the input conventions. -/
def MfMainSpec (sepL stepP : Stmt) (C C₀ : ℕ) (R : ℕ → ℕ) : Prop :=
  ∀ {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
    [DecidableEq F] (M : CombMap D V F), M.IsPlane → M.RotTrans → M.FaceTrans →
  ∀ (e : PVert M → TDart M) (he : ∀ w, (tnlMap M).tail (e w) = w) {u : D → ℤ}, (∀ d, 0 ≤ u d) →
  ∀ {S T : Finset V}, Disjoint S T → (nlDarts M).Nonempty →
  ∀ {N : ℕ} (en : ℕ → TDart M ⊕ (PVert M × Bool)) (d₀ : TDart M ⊕ (PVert M × Bool))
    {gid : TDart M ⊕ (PVert M × Bool) → ℕ} {ν : PVert M ⊕ PVert M → ℕ},
    Fintype.card (TDart M ⊕ (PVert M × Bool)) = N →
    (∀ y, ∃ i < N, en i = y) → (∀ i < N, gid (en i) = i) → Injective ν →
    QPar (pendQ (PVert M)) ν → TailSorted (lpreMapX M e he) gid ν →
    MfMainGoal M e he u S T N en d₀ gid ν sepL stepP C C₀ R

set_option maxHeartbeats 4000000 in
/-- **Consistency of `MfMainSpec` with `mfMain_cMachXGE`**: for the pendant darts chosen by
`Quotient.out` (the instance `lpreMap M`), `MfMainGoal` follows from `mfMain_cMachXGE` and its
remaining hypotheses (the large-piece separator `SepPSpecXL`, the node step `StepPSpec` and their
cost bounds). -/
theorem mfMainSpec_out {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] (M : CombMap D V F) (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {x₀ : D} (hx₀ : x₀ ∈ nlDarts M) {N : ℕ} (en : ℕ → _) (d₀ : _) {gid : _ → ℕ} {ν : _ → ℕ}
    (hN : Fintype.card (TDart M ⊕ (PVert M × Bool)) = N)
    (hsurj : ∀ y, ∃ i < N, en i = y) (hgid : ∀ i < N, gid (en i) = i) (hν : Injective ν)
    {C C₀ : ℕ} (hC : 200 ≤ C) (hC₀ : 20 ≤ C₀) {sepL stepP : Stmt} {R : ℕ → ℕ}
    (hsub : ∀ {I : Input} {W Z : ℕ}, 100000 ≤ W → 2 * Z ≤ W →
      let L := lpreMap M
      let pc := pcChoiceE L (pendQ _) en N d₀
      let sc := fun Hs A W => scChoiceE L (sepC L en N (encB' W)) en N Hs A W
      let gS := gSz L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000 (CInvS L (pendQ _))
      let gH := gHl L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000 (CInvS L (pendQ _))
      let ds : DSys L := ⟨guardS L gS (spSR L pc sc (pendQ _)),
        guardS L gH (spHR L pc sc (pendQ _)), chRot L (pendQ _), 100000, pendQ _, pc.pick⟩
      let τ := decS L (guardS L gS (spSR L pc sc (pendQ _))) (guardS L gH (spHR L pc sc (pendQ _)))
        (smD L pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
        (chRot L (pendQ _)) 100000 univ [] (rootRot L (pendQ _)) true
      let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
      let S' := preTerm (nlTerm M S)
      let T' := preTerm (nlTerm M T)
      let Reach := Calls L τ [] (rotPerm L)
      ∃ (sTL : ℕ → ℕ → ℕ) (cs : ℕ → ℕ) (sRL : ℕ → ℕ → ℕ → ℕ) (stT rT : MCall L → ℕ) (RS RT : ℕ),
        SepPSpecXL L ds Reach gid ν u' S' T' Z I W sepL sTL sRL ∧
        StepPSpec L (planeOracles fun X => frRef X) Reach gid u' S' T' Z I W stepP stT rT ∧
        (∀ n m k, m ≤ n → sTL n k + cs m ≤ C * n * lg n + C * k) ∧
        (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
          stT (.node l r π, Hs, σ) ≤ runsCharge L (cMach C C₀) l r π Hs σ +
            cs (pdarts L (l.piece ∪ r.piece) Hs).card +
            100 * (pdarts L (l.piece ∪ r.piece) Hs).card + 100 * Hs.length + 106) ∧
        (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) ∧ (∀ x, Reach x → rT x ≤ RT) ∧
        RS + RT ≤ R N) :
    MfMainGoal M (triE nlMap_rotTrans (nlE M)) (triE_tail (nlE_tail (M := M))) u S T N en d₀ gid
      ν sepL stepP C C₀ R := by
  unfold MfMainGoal
  intro L pc sc gS gH τ u' S' T' I W Hb Z REVb SIGb CAPb KRb VTb RTb hW hZ hHb c₀ hc₀ r0 r1 r2 r3
    r4 r5 r6 r7 hv hrt hrev hsig hcap hkr hvt hst i1 i2 i3 i4 i5 i6 hroom
  obtain ⟨sTL, cs, sRL, stT, rT, RS, RT, hsL, hstep, hsT, hstT, hsR, hrT, hR⟩ :=
    hsub (I := I) (W := W) (Z := Z) hW hZ
  have hbal := (maxflow_plane_cost_decG hM hrot hface hu hST pc
    (fun P Hs => pcChoiceE_ok hsurj d₀ _ P Hs) sc
    (fun Hs A W => scChoiceE_ok hsurj
      (sepC_ok (preMap_loopless nlMap_loopless nlE_tail) en N (encB' W) Hs) A W)
    (cMach_bounds C C₀)).1
  have hNc : τ.piece.card = N := by
    have h1 : τ.piece = univ := hbal.1
    rw [h1, card_univ]; exact hN
  have hroom' : Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N + (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ W := by
    have : (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ (2 * N + 1) * (110 * N + 80 + R N) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hpk := pkMin_pcChoiceE (M := L) (Q := pendQ _) hsurj hgid d₀
  have hsurj' : ∀ y, ∃ i < N, en i = y := hsurj
  rw [← hNc] at hsurj' hgid r0 hrev hsig hcap hkr hvt hst i1 i2 i3 i4 i5 i6 hroom' hsR
  have r5' : c₀.nreg 6705 = ntag τ := by
    rw [r5]; exact (ntag_root_lpre hM hrot hface S T hx₀ pc
      (fun P Hs => pcChoiceE_ok hsurj d₀ _ P Hs) sc
      (fun Hs A W => scChoiceE_ok hsurj
        (sepC_ok (preMap_loopless nlMap_loopless nlE_tail) en N (encB' W) Hs) A W)).symm
  have key := mfMain_cMachXGE hM hrot hface hu hST en hsurj d₀ hx₀ hC hC₀ hZ hsL hstep
    hpk hν (preMap_loopless nlMap_loopless nlE_tail) hW hsT hstT hsR hrT
    (en := en) hsurj' hgid hHb c₀ hc₀ r0 r1 r2 r3 r4 r5' r6 r7 hv hrt hrev hsig hcap hkr hvt hst
    i1 i2 i3 i4 i5 i6 hroom'
  obtain ⟨hp, c', t, ex, ht, hout, hmax⟩ := key
  refine ⟨hp, c', t, ex, ?_, ?_, hmax⟩
  · rw [← hNc]; exact ht
  · rw [← hNc]; exact hout

end Pp

end BKMNW

end PlanarFlow
