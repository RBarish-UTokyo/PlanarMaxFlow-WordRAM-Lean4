module

public import PlanarFlow.BKMNW.NcHole
public import PlanarFlow.BKMNW.NpStep

/-!
# The step invariants at the holes of the reachable node calls

* `HoleInvN NF u S T l r π Hs σ`: at the node call `(.node l r π, Hs, σ)` of `arunLN`, for every
  part `j` and hole `i` of the unrolled step (`xCtxN`), the preconditions of
  CycleToSingleSinkLimitedMaxFlow at the hole flow `hole j πj i` (`HoleC2S`) and of
  SingleSourceToCycleLimitedMaxFlow at `c2s j πj i H` (`HoleS2C`).
* **`arunLN_holeInv_node`**: under the hypotheses of `arunLN_spec` at a node call (the proof of
  `arunLN_spec` up to the call of `sepStep_spec`, then `SCtx.holeInv`).
* **`arunLN_holeInv`**: the same at **every node call reachable** from a call meeting the
  hypotheses of `arunLN_spec` (`Calls`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv CombMap Relation Orbit PlanarSeparator.StDart

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **The step invariants at the holes of a node call** (see the module docstring). -/
def HoleInvN (NF : NFam M) (u : D → ℤ) (S T : Finset V) (l r : ADec M) (π : HSep M)
    (Hs : List (Finset V)) (σ : Perm D) : Prop :=
  ∀ (h : SCond M l r π Hs σ) (j i : ℕ) (πj : SPath (pmap h.1))
    (H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))),
    (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj →
    ((xCtxN M NF u S T l r π Hs σ h).holes j)[i]? = some H →
    HoleC2S (pmap h.1) (xCtxN M NF u S T l r π Hs σ h).U
      ((xCtxN M NF u S T l r π Hs σ h).hole j πj i) πj H ∧
    HoleS2C (pmap h.1) (xCtxN M NF u S T l r π Hs σ h).U
      ((xCtxN M NF u S T l r π Hs σ h).c2s j πj i H) πj H

/-- **The step invariants at the holes of a node call** meeting the hypotheses of
`arunLN_spec`. -/
theorem arunLN_holeInv_node (NF : NFam M) {u : D → ℤ} (hu : ∀ d, 0 ≤ u d)
    {S T : Finset V} (hST : Disjoint S T) (l r : ADec M) (π : HSep M) (Hs : List (Finset V))
    (σ : Perm D) (hO : NSpecOn M NF (Calls M (.node l r π) Hs σ))
    (hp : (ADec.node l r π).PMOk M Hs σ) (hg : (ADec.node l r π).Good M S T Hs)
    (hpg : (ADec.node l r π).PGood M Hs) (hl : (ADec.node l r π).LeafOK M S T Hs)
    (hSA : Disjoint S (hunion Hs)) (hTA : Disjoint T (hunion Hs)) :
    HoleInvN M NF u S T l r π Hs σ := by
  obtain ⟨h, hpl, hpr⟩ := hp
  obtain ⟨gl, gr, hlr, hbd, hC, hseg⟩ := hg
  obtain ⟨hcon, -, -, pgl, pgr, hsegP⟩ := hpg
  have hSC : Disjoint S π.path.mverts := (disjoint_of_subset_right subset_union_left hC).symm
  have hTC : Disjoint T π.path.mverts := (disjoint_of_subset_right subset_union_right hC).symm
  -- the parts of the separator are in the piece map
  have hin : ∀ s ∈ π.segs, SegIn M (l.piece ∪ r.piece) Hs s := fun s hs => by
    obtain ⟨hsd, x, hx, ex⟩ := hsegP s hs
    have hav := hseg.1 s hs
    refine ⟨⟨⟨x, mem_pdarts.2 ⟨hx, fun ⟨H, hH, ht, _⟩ => ?_⟩⟩, ex⟩,
      fun e he => mem_pdarts.2 ⟨hsd e he, fun ⟨H, hH, ht, _⟩ => ?_⟩, hav⟩
    · exact disjoint_left.1 hav (by rw [ex]; exact s.p_mem_init le_rfl) (subset_hunion hH ht)
    · obtain ⟨i, hi, hti⟩ := SPath.tail_mem_darts s he
      exact disjoint_left.1 hav (by rw [hti]; exact s.p_mem_init hi) (subset_hunion hH ht)
  have hcond : PieceInv M (l.piece ∪ r.piece) Hs σ ∧
      ∀ s ∈ π.segs, SegIn M (l.piece ∪ r.piece) Hs s := ⟨h, hin⟩
  set Hs' := childHoles Hs π.path.mverts with hHs'
  have eHs' : hunion Hs' = hunion Hs ∪ π.path.mverts := by
    rw [hHs', hunion_childHoles]
  have hSA' : Disjoint S (hunion Hs') := by
    rw [eHs']; exact disjoint_union_right.2 ⟨hSA, hSC⟩
  have hTA' : Disjoint T (hunion Hs') := by
    rw [eHs']; exact disjoint_union_right.2 ⟨hTA, hTC⟩
  have il := arunLN_spec NF hu hST l Hs'
    (childRot M σ (pdarts M (l.piece ∪ r.piece) Hs) π.path.darts (pdarts M l.piece Hs'))
    (fun x hx => hO x (Or.inr (Or.inl hx))) hpl gl pgl hl.1 hSA' hTA'
  have ir := arunLN_spec NF hu hST r Hs'
    (childRot M σ (pdarts M (l.piece ∪ r.piece) Hs) π.path.darts (pdarts M r.piece Hs'))
    (fun x hx => hO x (Or.inr (Or.inr hx))) hpr gr pgr hl.2 hSA' hTA'
  set fl := arunLN M NF u S T l Hs' (childRot M σ (pdarts M (l.piece ∪ r.piece) Hs) π.path.darts (pdarts M l.piece Hs')) with hfl_def
  set fr := arunLN M NF u S T r Hs' (childRot M σ (pdarts M (l.piece ∪ r.piece) Hs) π.path.darts (pdarts M r.piece Hs')) with hfr_def
  have hsubl : pdarts M l.piece Hs' ⊆ pdarts M (l.piece ∪ r.piece) Hs :=
    pdarts_childHoles_subset subset_union_left
  have hsubr : pdarts M r.piece Hs' ⊆ pdarts M (l.piece ∪ r.piece) Hs :=
    pdarts_childHoles_subset subset_union_right
  have hHsr : ∀ a b, HRel Hs a b → HRel Hs' a b := fun a b e => e.childHoles
  have hsubH : ∀ H ∈ Hs, H ⊆ hunion Hs' := fun H hH => subset_hunion_childHoles hH
  have hmerge : ∀ a b, HRel Hs' a b → HRel Hs a b ∨ (a ∈ hunion Hs' ∧ b ∈ hunion Hs') := by
    rintro a b (e | ⟨H, hH, ha, hb⟩)
    · exact Or.inl (Or.inl e)
    · exact Or.inr ⟨subset_hunion hH ha, subset_hunion hH hb⟩
  by_cases hB : pdarts M (l.piece ∪ r.piece) Hs = ∅
  · intro h' j i πj H hj hi
    exact ((isEmpty_sVert hB).false (πj.p 0)).elim
  obtain ⟨x₀, hx₀⟩ := nonempty_iff_ne_empty.2 hB
  obtain ⟨hpl', hrot, hface⟩ := h.isPlane hcon hx₀
  have hO' : (NF (.node l r π, Hs, σ) h : NodeOracles (pmap h)).Spec
      (fun x : SDart (pdarts M (l.piece ∪ r.piece) Hs) => u x.1) :=
    hO _ (Or.inl rfl) h hpl' hrot hface _ (fun _ => hu _)
  -- the two pieces of the piece map
  obtain ⟨Pl, hPl⟩ : ∃ Pl : Finset (SDart (pdarts M (l.piece ∪ r.piece) Hs)),
      Pl = univ.filter fun x => x.1 ∈ pdarts M l.piece Hs' := ⟨_, rfl⟩
  obtain ⟨Ql, hQl⟩ : ∃ Ql : Finset (SDart (pdarts M (l.piece ∪ r.piece) Hs)),
      Ql = univ.filter fun x => x.1 ∉ pdarts M l.piece Hs' := ⟨_, rfl⟩
  obtain ⟨Pr, hPr⟩ : ∃ Pr : Finset (SDart (pdarts M (l.piece ∪ r.piece) Hs)),
      Pr = univ.filter fun x => x.1 ∈ pdarts M r.piece Hs' := ⟨_, rfl⟩
  have hdisj : ∀ d, d ∈ pdarts M l.piece Hs' → d ∉ pdarts M r.piece Hs' := fun d h1 h2 =>
    disjoint_left.1 hlr (pdarts_subset _ _ h1) (pdarts_subset _ _ h2)
  have revl := stable_pdarts hpl.pieceInv.rev Hs'
  have revr := stable_pdarts hpr.pieceInv.rev Hs'
  have hPlrev : RevClosed (pmap h) Pl := fun x hx => by
    rw [hPl, mem_filter] at hx ⊢; exact ⟨mem_univ _, revl _ hx.2⟩
  have hPrrev : RevClosed (pmap h) Pr := fun x hx => by
    rw [hPr, mem_filter] at hx ⊢; exact ⟨mem_univ _, revr _ hx.2⟩
  have hQlrev : RevClosed (pmap h) Ql := fun x hx => by
    rw [hQl, mem_filter] at hx ⊢
    refine ⟨mem_univ _, fun hc => hx.2 ?_⟩
    have := revl _ hc
    rwa [pmap_rev, revPerm_apply, M.rev_rev] at this
  have hPQ : Disjoint Pl Ql := by
    rw [hPl, hQl]; exact disjoint_filter.2 fun _ _ h1 h2 => h2 h1
  have hPrQ : Pr ⊆ Ql := fun x hx => by
    rw [hPr, mem_filter] at hx; rw [hQl, mem_filter]
    exact ⟨mem_univ _, fun hc => hdisj _ hc hx.2⟩
  have hunivPQ : Pl ∪ Ql = univ := by
    rw [hPl, hQl]; exact filter_union_filter_not_eq _ _
  -- terminals and holes of the piece map
  have eA : vimg M σ (pdarts M (l.piece ∪ r.piece) Hs) (hunion Hs') =
      hunion (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs) ∪
        hunion ((segsP h π.segs hin).map SPath.verts) := by
    rw [eHs', ← hseg.2.2, vimg_union, hunion_pholes, segsP_verts]
    congr 1
    rw [vimg_hunion, List.map_map]
    rfl
  have dST := disjoint_vimg h hST hSA
  have dSA := disjoint_vimg h hSA' hSA
  have dAT := (disjoint_vimg h hTA' hTA).symm
  -- the flows of the children, on the piece map
  have hfl : MSOut (pmap h) (capOn (fun x => u x.1) Pl)
      (vimg M σ _ S) (vimg M σ _ T) (vimg M σ _ (hunion Hs'))
      (fun x => if hx : x.1 ∈ pdarts M l.piece Hs' then fl ⟨x.1, hx⟩ else 0) := by
    by_cases h0 : pdarts M l.piece Hs' = ∅
    · have e1 : capOn (fun x : SDart (pdarts M (l.piece ∪ r.piece) Hs) => u x.1) Pl = 0 :=
        funext fun x => by simp [capOn, hPl, h0]
      have e2 : (fun x : SDart (pdarts M (l.piece ∪ r.piece) Hs) =>
          if hx : x.1 ∈ pdarts M l.piece Hs' then fl ⟨x.1, hx⟩ else 0) = 0 :=
        funext fun x => by simp [h0]
      rw [e1, e2]; exact msOut_zero dST dSA dAT
    · obtain ⟨x₁, hx₁⟩ := nonempty_iff_ne_empty.2 h0
      have := msOut_child h hpl.pieceInv hsubl hHsr ⟨x₁, hx₁⟩ hSA' hTA' hST hsubH hmerge il
      rw [childEmb_ext_eq] at this
      rw [hPl]; exact this
  have hfr' : MSOut (pmap h) (capOn (fun x => u x.1) Pr)
      (vimg M σ _ S) (vimg M σ _ T) (vimg M σ _ (hunion Hs'))
      (fun x => if hx : x.1 ∈ pdarts M r.piece Hs' then fr ⟨x.1, hx⟩ else 0) := by
    by_cases h0 : pdarts M r.piece Hs' = ∅
    · have e1 : capOn (fun x : SDart (pdarts M (l.piece ∪ r.piece) Hs) => u x.1) Pr = 0 :=
        funext fun x => by simp [capOn, hPr, h0]
      have e2 : (fun x : SDart (pdarts M (l.piece ∪ r.piece) Hs) =>
          if hx : x.1 ∈ pdarts M r.piece Hs' then fr ⟨x.1, hx⟩ else 0) = 0 :=
        funext fun x => by simp [h0]
      rw [e1, e2]; exact msOut_zero dST dSA dAT
    · obtain ⟨x₁, hx₁⟩ := nonempty_iff_ne_empty.2 h0
      have := msOut_child h hpr.pieceInv hsubr hHsr ⟨x₁, hx₁⟩ hSA' hTA' hST hsubH hmerge ir
      rw [childEmb_ext_eq] at this
      rw [hPr]; exact this
  have hfr : MSOut (pmap h) (capOn (fun x => u x.1) Ql)
      (vimg M σ _ S) (vimg M σ _ T) (vimg M σ _ (hunion Hs'))
      (fun x => if hx : x.1 ∈ pdarts M r.piece Hs' then fr ⟨x.1, hx⟩ else 0) := by
    refine MSOut.widen hPrrev hPrQ (fun d hdQ hdP => ?_) (fun _ => hu _) hfr'
    rw [hQl, mem_filter] at hdQ
    rw [hPr, mem_filter] at hdP
    obtain ⟨h1, h2⟩ := inner_sep (pdarts_subset _ _ d.2) hdQ.2
      (fun hc => hdP ⟨mem_univ _, hc⟩)
    exact ⟨mem_vimg.2 ⟨d, h1, rfl⟩, mem_vimg.2 ⟨(pmap h).rev d, h2, rfl⟩⟩
  rw [eA] at hfl hfr
  -- the vertices shared by the two pieces
  have hbdB : bd (pmap h) Pl Ql ⊆ vimg M σ _ S ∪ vimg M σ _ T ∪
      (hunion (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs) ∪
        hunion ((segsP h π.segs hin).map SPath.verts)) := by
    rw [← eA, ← vimg_union, ← vimg_union]
    intro w hw
    obtain ⟨⟨x, hxP, rfl⟩, ⟨y, hyQ, hyw⟩⟩ := mem_bd.1 hw
    rw [hPl, mem_filter] at hxP
    rw [hQl, mem_filter] at hyQ
    refine mem_vimg.2 ⟨x, ?_, rfl⟩
    have hxy := (h.vert _ y.2 _ x.2).1 (Quotient.exact hyw)
    rw [eHs']
    rcases hxy with e | ⟨H, hH, -, h2⟩
    · by_cases hyr : y.1 ∈ pdarts M r.piece Hs'
      · have hv : M.tail x.1 ∈ bd M l.piece r.piece :=
          mem_bd.2 ⟨⟨x.1, pdarts_subset _ _ hxP.2, rfl⟩, ⟨y.1, pdarts_subset _ _ hyr, e⟩⟩
        have := hbd hv
        simp only [mem_union] at this ⊢; tauto
      · have := (inner_sep (pdarts_subset _ _ y.2) hyQ.2 hyr).1
        rw [e, eHs'] at this
        exact mem_union_right _ this
    · exact mem_union_right _ (mem_union_left _ (subset_hunion hH h2))
  have hSAB : Disjoint (vimg M σ (pdarts M (l.piece ∪ r.piece) Hs) S)
      (hunion (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs) ∪
        hunion ((segsP h π.segs hin).map SPath.verts)) := by
    rw [← eA]; exact dSA
  obtain ⟨hps, hcons, h1, h2⟩ := combine hPlrev hQlrev hPQ dST hSAB hbdB hfl hfr
  rw [hunivPQ] at hps h1 h2
  -- the parts of the separator in the piece map
  have hmemP : ∀ π' ∈ segsP h π.segs hin, ∃ s ∈ π.segs,
      π'.verts = vimg M σ (pdarts M (l.piece ∪ r.piece) Hs) s.verts := by
    intro π' hπ'
    have : π'.verts ∈ (segsP h π.segs hin).map SPath.verts := List.mem_map_of_mem hπ'
    rw [segsP_verts] at this
    obtain ⟨s, hs, e⟩ := List.mem_map.1 this
    exact ⟨s, hs, e.symm⟩
  have hπs : ∀ π' ∈ segsP h π.segs hin, Disjoint π'.verts (vimg M σ _ S ∪ vimg M σ _ T ∪
      hunion (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs)) := by
    intro π' hπ'
    obtain ⟨s, hs, e⟩ := hmemP π' hπ'
    rw [e, hunion_pholes, ← vimg_union, ← vimg_union]
    have hsm := hseg.subset hs
    exact disjoint_vimg h (disjoint_union_right.2 ⟨disjoint_union_right.2
      ⟨disjoint_of_subset_left hsm hSC.symm, disjoint_of_subset_left hsm hTC.symm⟩,
        hseg.1 s hs⟩) (hseg.1 s hs)
  have hpw : ((segsP h π.segs hin).map SPath.verts).Pairwise Disjoint := by
    rw [segsP_verts, List.pairwise_map]
    have := hseg.2.1
    rw [List.pairwise_map] at this
    exact this.imp_of_mem fun ha _ hab => disjoint_vimg h hab (hseg.1 _ ha)

  have hcap : capOn (fun x : SDart (pdarts M (l.piece ∪ r.piece) Hs) => u x.1) univ =
      fun x => u x.1 := capOn_univ
  rw [hcap] at hps h1 h2
  intro h' j i πj H hj hi
  exact SCtx.holeInv (xCtxN M NF u S T l r π Hs σ h') hO' rfl
    (fun H hH => pholes_path h hH) hπs hpw hps hcons h1 h2 hj hi

/-- **The step invariants at the holes of every node call reachable** from a call meeting the
hypotheses of `arunLN_spec`. -/
theorem arunLN_holeInv (NF : NFam M) {u : D → ℤ} (hu : ∀ d, 0 ≤ u d)
    {S T : Finset V} (hST : Disjoint S T) :
    ∀ (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D), NSpecOn M NF (Calls M τ Hs σ) →
      τ.PMOk M Hs σ → τ.Good M S T Hs → τ.PGood M Hs → τ.LeafOK M S T Hs →
      Disjoint S (hunion Hs) → Disjoint T (hunion Hs) →
      ∀ (l r : ADec M) (π : HSep M) (Hs₁ : List (Finset V)) (σ₁ : Perm D),
        Calls M τ Hs σ (.node l r π, Hs₁, σ₁) → HoleInvN M NF u S T l r π Hs₁ σ₁
  | .leaf Q, Hs, σ, _, _, _, _, _, _, _, l, r, π, Hs₁, σ₁, hc => by cases hc
  | .node l₀ r₀ π₀, Hs, σ, hO, hp, hg, hpg, hl, hSA, hTA, l, r, π, Hs₁, σ₁, hc => by
    rcases hc with hc | hc | hc
    · cases hc
      exact arunLN_holeInv_node NF hu hST _ _ _ _ _ hO hp hg hpg hl hSA hTA
    · obtain ⟨h, hpl, hpr⟩ := hp
      obtain ⟨gl, gr, hlr, hbd, hC, hseg⟩ := hg
      obtain ⟨hcon, -, -, pgl, pgr, hsegP⟩ := hpg
      have hSC : Disjoint S π₀.path.mverts :=
        (disjoint_of_subset_right subset_union_left hC).symm
      have hTC : Disjoint T π₀.path.mverts :=
        (disjoint_of_subset_right subset_union_right hC).symm
      have eHs' : hunion (childHoles Hs π₀.path.mverts) = hunion Hs ∪ π₀.path.mverts := by
        rw [hunion_childHoles]
      have hSA' : Disjoint S (hunion (childHoles Hs π₀.path.mverts)) := by
        rw [eHs']; exact disjoint_union_right.2 ⟨hSA, hSC⟩
      have hTA' : Disjoint T (hunion (childHoles Hs π₀.path.mverts)) := by
        rw [eHs']; exact disjoint_union_right.2 ⟨hTA, hTC⟩
      exact arunLN_holeInv NF hu hST l₀ _ _ (fun x hx => hO x (Or.inr (Or.inl hx))) hpl gl pgl
        hl.1 hSA' hTA' l r π Hs₁ σ₁ hc
    · obtain ⟨h, hpl, hpr⟩ := hp
      obtain ⟨gl, gr, hlr, hbd, hC, hseg⟩ := hg
      obtain ⟨hcon, -, -, pgl, pgr, hsegP⟩ := hpg
      have hSC : Disjoint S π₀.path.mverts :=
        (disjoint_of_subset_right subset_union_left hC).symm
      have hTC : Disjoint T π₀.path.mverts :=
        (disjoint_of_subset_right subset_union_right hC).symm
      have eHs' : hunion (childHoles Hs π₀.path.mverts) = hunion Hs ∪ π₀.path.mverts := by
        rw [hunion_childHoles]
      have hSA' : Disjoint S (hunion (childHoles Hs π₀.path.mverts)) := by
        rw [eHs']; exact disjoint_union_right.2 ⟨hSA, hSC⟩
      have hTA' : Disjoint T (hunion (childHoles Hs π₀.path.mverts)) := by
        rw [eHs']; exact disjoint_union_right.2 ⟨hTA, hTC⟩
      exact arunLN_holeInv NF hu hST r₀ _ _ (fun x hx => hO x (Or.inr (Or.inr hx))) hpr gr pgr
        hl.2 hSA' hTA' l r π Hs₁ σ₁ hc

end MfDrv

end BKMNW

end PlanarFlow
