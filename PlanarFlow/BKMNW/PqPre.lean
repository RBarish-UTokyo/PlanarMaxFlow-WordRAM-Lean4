module

public import PlanarFlow.BKMNW.CsScale
public import PlanarFlow.BKMNW.PpHyp

/-!
# The headline facts for the preprocessed map with explicit pendant darts

The chain of the max-flow program (`maxflow_plane_cost_decG`, `mfMain_XGEPGen`, …) is stated for
`lpreMap M`, whose pendant darts are chosen by `Quotient.out` (`PpMap.lean`). Its proofs use the
pendant darts only through their tail property, so they hold for **any** choice. Here the facts
they rest on are restated for the triangulated map with a pendant edge drawn before any dart
`e w` leaving `w` (generic level, a loop-free plane map `M`), and then for
`lpreMapX M ep hep` (`PpMap.lean`):

* generic level (`(M.triMap hrot).pendant e he`): `preP_loopless`, `pendQ_hypsP`,
  `decS_balDecA_preP`, `maxflow_pre_cost_ofP`, `runLN_pre_isMaxP`;
* for `lpreMapX` (a dart of `M` that is not a loop given): `decS_balDecA_lpreX`,
  `splitFnsS_lpreRX`, `maxflow_cost_ofX`, **`maxflow_plane_cost_decGX`** (the headline of the
  guarded decomposition), `nlRunNX` and **`nlRunNX_isMax`**, `lpreMapX_hyps`, **`callOk_rootX`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Function Equiv Orbit CombMap Relation PlanarSeparator.StDart MfDrv

universe w

section Gen

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F} {hrot : M.RotTrans}
  {e : V ⊕ (M.toSep hrot).Face → PlanarSeparator.StDart D}

/-- The triangulated map with pendant edges before the darts `e w` has no loop when `M` has
none. -/
lemma preP_loopless (hl : ∀ d, M.head d ≠ M.tail d) (he : ∀ w, (M.triMap hrot).tail (e w) = w)
    (x : PlanarSeparator.StDart D ⊕ ((V ⊕ (M.toSep hrot).Face) × Bool)) :
    ((M.triMap hrot).pendant e he).head x ≠ ((M.triMap hrot).pendant e he).tail x := by
  rcases x with t | ⟨w, _ | _⟩
  · exact fun h => triMap_loopless hrot hl t (Sum.inl.inj h)
  · exact fun h => by cases h
  · exact fun h => by cases h

/-- `pendQ_hyps` for any pendant darts. -/
lemma pendQ_hypsP (he : ∀ w, (M.triMap hrot).tail (e w) = w) (S T : Finset V) :
    preTerm (hrot := hrot) S ∪ preTerm (hrot := hrot) T ⊆ pendQ _ ∧
    (∀ q ∈ pendQ _, ∀ d d', ((M.triMap hrot).pendant e he).tail d = q →
      ((M.triMap hrot).pendant e he).tail d' = q → d = d') ∧
    (∀ d, ¬ (((M.triMap hrot).pendant e he).tail d ∈ pendQ _ ∧
      ((M.triMap hrot).pendant e he).head d ∈ pendQ _)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    simp only [preTerm, mem_union, mem_image] at hw
    rcases hw with ⟨_, -, rfl⟩ | ⟨_, -, rfl⟩ <;> exact inr_mem_pendQ _
  · intro q hq d d' hd hd'
    obtain ⟨w, -, rfl⟩ := mem_image.1 hq
    rw [(pendant_tail_eq_inr he d w).1 hd, (pendant_tail_eq_inr he d' w).1 hd']
  · rintro d ⟨h1, h2⟩
    obtain ⟨w, -, hw⟩ := mem_image.1 h1
    have hd := (pendant_tail_eq_inr he d w).1 hw.symm
    subst hd
    exact inl_not_mem_pendQ w h2

/-- `decS_balDecA_pre` for any pendant darts. -/
theorem decS_balDecA_preP [Nonempty D] (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) (hl : ∀ d, M.head d ≠ M.tail d)
    {e : V ⊕ (M.toSep hrot).Face → PlanarSeparator.StDart D}
    (he : ∀ w, (M.triMap hrot).tail (e w) = w) {S T : Finset V}
    {spS spH : Finset _ → List (Finset _) → Perm _ → SplitAns ((M.triMap hrot).pendant e he)}
    {sm : Finset _ → List (Finset _) → ADec ((M.triMap hrot).pendant e he)}
    {chS : Finset _ → List (Finset _) → Perm _ → HSep ((M.triMap hrot).pendant e he) →
      Finset _ → Perm _}
    (hF : SplitFnsS ((M.triMap hrot).pendant e he) (preTerm S) (preTerm T) 9 100000
      (CInvS ((M.triMap hrot).pendant e he) (pendQ _)) spS spH sm chS) :
    BalDecA ((M.triMap hrot).pendant e he) (preTerm S) (preTerm T) 9 6 100000
      (decS ((M.triMap hrot).pendant e he) spS spH sm chS 100000 univ []
        (rootRot ((M.triMap hrot).pendant e he) (pendQ _)) true) := by
  have hP := triMap_isPlane hM hrot hface
  exact decS_balDecA (CombMap.pendant_isPlane he hP)
    (CombMap.pendant_rotTrans he (triMap_rotTrans hrot))
    (CombMap.pendant_faceTrans he (triMap_faceTrans hrot)) hF
    (cinvS_pendant he hP (triMap_rotTrans hrot) (triMap_faceTrans hrot)
      fun d => (triMap_isTriangle hrot hl d).φ_three)

/-- `maxflow_pre_cost_of` for any pendant darts (`e₀`, `he₀`: every vertex has a dart). -/
theorem maxflow_pre_cost_ofP (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V}
    (hST : Disjoint S T) {e₀ : V → D} (he₀ : ∀ v, M.tail (e₀ v) = v)
    {e : V ⊕ (M.toSep hrot).Face → PlanarSeparator.StDart D}
    (he : ∀ w, (M.triMap hrot).tail (e w) = w)
    {O : PlaneOracles.{w}} (hO : O.Spec) {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    {τ : ADec ((M.triMap hrot).pendant e he)}
    (hτ : BalDecA ((M.triMap hrot).pendant e he) (preTerm S) (preTerm T) 9 6 100000 τ) :
    IsMax M u S T (fun d =>
        runL ((M.triMap hrot).pendant e he) (preCap u S T) τ O (preTerm S) (preTerm T)
          (.inl (old d))) ∧
      runLCost ((M.triMap hrot).pendant e he) c τ ≤ (100000 + 11) ^ 2 * ((27 * ((6 + 1) *
        (25 + 7 * 9 ^ 2 + 2 * 6 * (34 + 14 * 9 ^ 2))) + 25) * K * (7 * Fintype.card D) *
          lg (7 * Fintype.card D) ^ 3 + K₀ * (7 * Fintype.card D) * lg (7 * Fintype.card D)) := by
  have : Nonempty D := ⟨e₀ hM.nonempty.some⟩
  have hP := triMap_isPlane hM hrot hface
  have hcard := (card_preMap_darts (hrot := hrot) hM hface he₀).2
  have hpos : 0 < Fintype.card (PlanarSeparator.StDart D ⊕ ((V ⊕ (M.toSep hrot).Face) × Bool)) :=
    Fintype.card_pos_iff.2 ⟨Sum.inl (old (Classical.arbitrary D))⟩
  obtain ⟨h1, h2⟩ := runL_isMax_costA (CombMap.pendant_isPlane he hP)
    (CombMap.pendant_rotTrans he (triMap_rotTrans hrot))
    (CombMap.pendant_faceTrans he (triMap_faceTrans hrot))
    (pendCap_nonneg (triCap_nonneg hu) _ _ (sum_nonneg fun x _ => triCap_nonneg hu x))
    ((disjoint_image Sum.inr_injective).2 ((disjoint_image Sum.inl_injective).2 hST)) hτ hO hc
    hpos
  refine ⟨isMax_restrict (triMap_embeds hrot) (fun _ => rfl) (triCap_out u)
    (isMax_pendant he (triCap_nonneg hu) h1), h2.trans ?_⟩
  have hlg := lg_mono hcard
  gcongr

/-- `runLN_pre_isMax` for any pendant darts. -/
theorem runLN_pre_isMaxP [Nonempty D] (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {e : V ⊕ (M.toSep hrot).Face → PlanarSeparator.StDart D}
    (he : ∀ w, (M.triMap hrot).tail (e w) = w)
    {τ : ADec ((M.triMap hrot).pendant e he)}
    (hτ : BalDecA ((M.triMap hrot).pendant e he) (preTerm S) (preTerm T) 9 6 100000 τ)
    {NF : NFam ((M.triMap hrot).pendant e he)}
    (hO : NSpecOn ((M.triMap hrot).pendant e he) NF (Calls ((M.triMap hrot).pendant e he) τ []
      (rotPerm ((M.triMap hrot).pendant e he)))) :
    IsMax M u S T (fun d =>
        runLN ((M.triMap hrot).pendant e he) (preCap u S T) τ NF (preTerm S) (preTerm T)
          (.inl (old d))) := by
  have hP := triMap_isPlane hM hrot hface
  exact isMax_restrict (triMap_embeds hrot) (fun _ => rfl) (triCap_out u)
    (isMax_pendant he (triCap_nonneg hu) (runLN_isMax (CombMap.pendant_isPlane he hP)
      (CombMap.pendant_rotTrans he (triMap_rotTrans hrot))
      (CombMap.pendant_faceTrans he (triMap_faceTrans hrot))
      (pendCap_nonneg (triCap_nonneg hu) _ _ (sum_nonneg fun x _ => triCap_nonneg hu x))
      ((disjoint_image Sum.inr_injective).2 ((disjoint_image Sum.inl_injective).2 hST))
      hτ.1 hτ.2.1 hτ.2.2.1 hτ.2.2.2.1 hO))

end Gen

section X

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **`BalDecA` for the decomposition with the rotation as a state on `lpreMapX M ep hep`** (a dart
of `M` that is not a loop given). -/
theorem decS_balDecA_lpreX (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {x₀ : D} (hx₀ : x₀ ∈ nlDarts M) (ep : PVert M → TDart M)
    (hep : ∀ w, (tnlMap M).tail (ep w) = w) {S T : Finset V}
    {spS spH : Finset _ → List (Finset _) → Perm _ → SplitAns (lpreMapX M ep hep)}
    {sm : Finset _ → List (Finset _) → ADec (lpreMapX M ep hep)}
    {chS : Finset _ → List (Finset _) → Perm _ → HSep (lpreMapX M ep hep) → Finset _ → Perm _}
    (hF : SplitFnsS (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 100000
      (CInvS (lpreMapX M ep hep) (pendQ _)) spS spH sm chS) :
    BalDecA (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000
      (decS (lpreMapX M ep hep) spS spH sm chS 100000 univ []
        (rootRot (lpreMapX M ep hep) (pendQ _)) true) := by
  have : Nonempty (SDart (nlDarts M)) := ⟨⟨x₀, hx₀⟩⟩
  exact decS_balDecA_preP (nlMap_isPlane hM hrot hface hx₀) nlMap_rotTrans nlMap_faceTrans
    nlMap_loopless hep hF

/-- `splitFnsS_lpreR` on `lpreMapX M ep hep`. -/
theorem splitFnsS_lpreRX (ep : PVert M → TDart M) (hep : ∀ w, (tnlMap M).tail (ep w) = w)
    (S T : Finset V) (pc : PcChoice _ _)
    (hpc : ∀ P Hs, pc.OK (lpreMapX M ep hep) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMapX M ep hep))
    (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W) :
    SplitFnsS (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 100000
      (CInvS (lpreMapX M ep hep) (pendQ _)) (spSR (lpreMapX M ep hep) pc sc (pendQ _))
      (spHR (lpreMapX M ep hep) pc sc (pendQ _))
      (smD (lpreMapX M ep hep) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMapX M ep hep) (pendQ _)) := by
  obtain ⟨h1, h2, h3⟩ := pendQ_hypsP (hrot := nlMap_rotTrans) hep (nlTerm M S) (nlTerm M T)
  exact splitFnsS_R (preP_loopless nlMap_loopless hep) h1 h2 h3 pc hpc sc hsc

/-- **`maxflow_cost_of` on `lpreMapX M ep hep`**: for every decomposition meeting `BalDecA`,
`nlRunX` is a maximum flow, at the cost bound of `maxflow_cost`. -/
theorem maxflow_cost_ofX (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {x₀ : D} (hx₀ : x₀ ∈ nlDarts M) (ep : PVert M → TDart M)
    (hep : ∀ w, (tnlMap M).tail (ep w) = w)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {O : PlaneOracles.{w}} (hO : O.Spec) {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    {τ : ADec (lpreMapX M ep hep)}
    (hτ : BalDecA (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000
      τ) :
    IsMax M u S T (nlRunX M ep hep u S T τ O) ∧
      runLCost (lpreMapX M ep hep) c τ ≤ (100000 + 11) ^ 2 * ((27 * ((6 + 1) * (25 + 7 * 9 ^ 2 +
        2 * 6 * (34 + 14 * 9 ^ 2))) + 25) * K * (7 * Fintype.card D) *
          lg (7 * Fintype.card D) ^ 3 + K₀ * (7 * Fintype.card D) * lg (7 * Fintype.card D)) := by
  have hST' : Disjoint (nlTerm M S) (nlTerm M T) := by
    rw [disjoint_left]
    intro w h1 h2
    simp only [nlTerm, mem_filter, mem_univ, true_and] at h1 h2
    exact disjoint_left.1 hST h1 h2
  have hcard : Fintype.card (SDart (nlDarts M)) ≤ Fintype.card D := by
    rw [Fintype.card_coe]; exact card_le_univ _
  obtain ⟨h1, h2⟩ := maxflow_pre_cost_ofP (nlMap_isPlane hM hrot hface hx₀) nlMap_rotTrans
    nlMap_faceTrans (u := fun x => u x.1) (fun x => hu x.1) hST' nlE_tail hep hO hc hτ
  exact ⟨isMax_nlExt hrot hu h1, h2.trans (lg_le_of_le hcard K K₀ _)⟩

/-- **The headline for the guarded decomposition of `lpreMapX M ep hep`** with any choices `pc`,
`sc` meeting their specifications (`maxflow_plane_cost_decG` with explicit pendant darts). -/
theorem maxflow_plane_cost_decGX (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {x₀ : D} (hx₀ : x₀ ∈ nlDarts M) (ep : PVert M → TDart M)
    (hep : ∀ w, (tnlMap M).tail (ep w) = w)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) (pc : PcChoice _ _)
    (hpc : ∀ P Hs, pc.OK (lpreMapX M ep hep) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMapX M ep hep))
    (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W)
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀) :
    let L := lpreMapX M ep hep
    let gS := gSz L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000 (CInvS L (pendQ _))
    let gH := gHl L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000 (CInvS L (pendQ _))
    let τ := decS L (guardS L gS (spSR L pc sc (pendQ _))) (guardS L gH (spHR L pc sc (pendQ _)))
      (smD L pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot L (pendQ _)) 100000 univ [] (rootRot L (pendQ _)) true
    BalDecA L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ ∧
      IsMax M u S T (nlRunX M ep hep u S T τ (planeOracles fun X => frRef X)) ∧
      runLCost L c τ ≤
        (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) := by
  intro L gS gH τ
  have hτ : BalDecA L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ :=
    decS_balDecA_lpreX hM hrot hface hx₀ ep hep
      (splitFnsS_guard (splitFnsS_lpreRX ep hep S T pc hpc sc hsc))
  obtain ⟨h1, h2⟩ := maxflow_cost_ofX hM hrot hface hx₀ ep hep hu hST
    (planeOracles_spec _ fun X => frRef_spec X) hc hτ
  exact ⟨hτ, h1, h2.trans (cost_bound_le K K₀ _)⟩

variable (M) in
/-- **The algorithm with subroutines depending on the call on `lpreMapX M ep hep`**, restricted
to the darts of `M` (`nlRunN` with explicit pendant darts). -/
noncomputable def nlRunNX (ep : PVert M → TDart M) (hep : ∀ w, (tnlMap M).tail (ep w) = w)
    (u : D → ℤ) (S T : Finset V) (τ : ADec (lpreMapX M ep hep))
    (NF : NFam (lpreMapX M ep hep)) : D → ℤ :=
  nlExt M fun x => runLN (lpreMapX M ep hep) (preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T))
    τ NF (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) (.inl (old x))

/-- **Correctness of `nlRunNX`** (`nlRunN_isMax` with explicit pendant darts). -/
theorem nlRunNX_isMax (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {u : D → ℤ}
    (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) {x₀ : D} (hx₀ : x₀ ∈ nlDarts M)
    (ep : PVert M → TDart M) (hep : ∀ w, (tnlMap M).tail (ep w) = w)
    {τ : ADec (lpreMapX M ep hep)}
    (hτ : BalDecA (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000
      τ)
    {NF : NFam (lpreMapX M ep hep)}
    (hO : NSpecOn (lpreMapX M ep hep) NF (Calls (lpreMapX M ep hep) τ []
      (rotPerm (lpreMapX M ep hep)))) :
    IsMax M u S T (nlRunNX M ep hep u S T τ NF) := by
  have hST' : Disjoint (nlTerm M S) (nlTerm M T) := by
    rw [disjoint_left]
    intro w h1 h2
    simp only [nlTerm, mem_filter, mem_univ, true_and] at h1 h2
    exact disjoint_left.1 hST h1 h2
  have : Nonempty (SDart (nlDarts M)) := ⟨⟨x₀, hx₀⟩⟩
  have h1 := runLN_pre_isMaxP (nlMap_isPlane hM hrot hface hx₀) nlMap_rotTrans nlMap_faceTrans
    (u := fun x => u x.1) (fun x => hu x.1) hST' hep hτ hO
  exact isMax_nlExt hrot hu h1

/-- **`lpreMapX M ep hep` is plane with transitive rotations and faces**, and has a dart. -/
lemma lpreMapX_hyps (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) (ep : PVert M → TDart M) (hep : ∀ w, (tnlMap M).tail (ep w) = w) :
    (lpreMapX M ep hep).IsPlane ∧ (lpreMapX M ep hep).RotTrans ∧
      (lpreMapX M ep hep).FaceTrans ∧ Nonempty (TDart M ⊕ (PVert M × Bool)) := by
  have hP1 := nlMap_isPlane hM hrot hface hx₀
  have : Nonempty (SDart (nlDarts M)) := ⟨⟨x₀, hx₀⟩⟩
  have hP2 := triMap_isPlane hP1 nlMap_rotTrans nlMap_faceTrans
  exact ⟨CombMap.pendant_isPlane _ hP2, CombMap.pendant_rotTrans _ (triMap_rotTrans _),
    CombMap.pendant_faceTrans _ (triMap_faceTrans _), ⟨Sum.inl (old ⟨x₀, hx₀⟩)⟩⟩

/-- **The invariants at the root call** of a decomposition of `lpreMapX M ep hep` meeting
`BalDecA` (`callOk_root` with explicit pendant darts). -/
lemma callOk_rootX (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) (ep : PVert M → TDart M) (hep : ∀ w, (tnlMap M).tail (ep w) = w)
    {S T : Finset _} {κ η s : ℕ} {τ : ADec (lpreMapX M ep hep)}
    (hbal : BalDecA (lpreMapX M ep hep) S T κ η s τ) :
    CallOk (lpreMapX M ep hep) S T (τ, [], rotPerm (lpreMapX M ep hep)) := by
  obtain ⟨hP, hr, hf, hD⟩ := lpreMapX_hyps hM hrot hface hx₀ ep hep
  obtain ⟨hall, hgood, hpg, hleaf, -⟩ := hbal
  have h0 : PieceInv (lpreMapX M ep hep) τ.piece [] (rotPerm (lpreMapX M ep hep)) := by
    rw [hall]; exact pieceInv_root hP hr hf hD
  exact ⟨ADec.PMOk.of_pieceInv τ [] _ List.Pairwise.nil hgood hpg h0, hgood, hpg, hleaf,
    by simp [hunion], by simp [hunion], List.Pairwise.nil⟩

end X

end Pp

end BKMNW

end PlanarFlow
