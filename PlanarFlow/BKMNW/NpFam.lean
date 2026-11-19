module

public import PlanarFlow.BKMNW.NpPushL
public import PlanarFlow.BKMNW.MfStepZ

/-!
# Algorithm 1 with node subroutines depending on the call (any `NodeOracles` family)

`arunLO` (`LocalO.lean`) runs at every node call the subroutines `impl` of a `MapOracles` family
(MSSP, FR, negSSSP, s-t flow per call). Because `impl`'s push-backs make classical choices
(`NpPushG.lean`), a machine needs its own `NodeOracles` at every call (e.g. `implG` with
`pushFwdL` and the machine's orders). This file restates `LocalO.lean` for **any family of node
subroutines** `NF : NFam M` (`(x : MCall M) → PieceInv … → NodeOracles (pmap h)`), with the
specification required at the calls only (**`NSpecOn`**, for every nonnegative capacity); the
proofs are those of `LocalO.lean`, mechanically adapted:

* **`arunLN`**, **`arunLN_spec`**, `runLN`, **`runLN_isMax`**, `runLN_pre_isMax`, `nlRunN`,
  **`nlRunN_isMax`**;
* `arunLO_eq_arunLN` (`arunLO` is `arunLN` of the family `(NO x h).nodes`), `nSpecOn_of_mo`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv CombMap Relation Orbit PlanarSeparator.StDart

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **A family of node subroutines, one for every call** and every proof of the invariant of its
piece map. -/
abbrev NFam := (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → NodeOracles (pmap h)

variable (M) in
open Classical in
/-- **Algorithm 1 on the piece maps with subroutines depending on the call**: `arunL`, the node
call `x` running the subroutines `NF x`. -/
noncomputable def arunLN (NF : NFam M) (u : D → ℤ) (S T : Finset V) :
    (τ : ADec M) → (Hs : List (Finset V)) → (σ : Perm D) → SDart (pdarts M τ.piece Hs) → ℤ
  | .leaf Q, Hs, σ =>
    if h : PieceInv M Q Hs σ then
      leafSolve (pmap h) (fun x => u x.1) (vimg M σ _ S) (vimg M σ _ T) (vimg M σ _ (hunion Hs))
    else 0
  | .node l r π, Hs, σ =>
    if h : PieceInv M (l.piece ∪ r.piece) Hs σ ∧ ∀ s ∈ π.segs, SegIn M (l.piece ∪ r.piece) Hs s then
      sepStep (M := pmap h.1) (NF (.node l r π, Hs, σ) h.1 : NodeOracles (pmap h.1))
        (fun x => u x.1) (vimg M σ _ S) (vimg M σ _ T) (pholes M σ _ Hs) univ
        (segsP h.1 π.segs h.2)
        (joinFlow
          (arunLN NF u S T l (childHoles Hs π.path.mverts)
            (childRot M σ (pdarts M (l.piece ∪ r.piece) Hs) π.path.darts
              (pdarts M l.piece (childHoles Hs π.path.mverts))))
          (arunLN NF u S T r (childHoles Hs π.path.mverts)
            (childRot M σ (pdarts M (l.piece ∪ r.piece) Hs) π.path.darts
              (pdarts M r.piece (childHoles Hs π.path.mverts)))))
    else 0

variable (M) in
/-- **The subroutines meet their specifications at the calls of `Reach`**, on the plane piece
maps with transitive rotations and faces. -/
def NSpecOn (NF : NFam M) (Reach : MCall M → Prop) : Prop :=
  ∀ x, Reach x → ∀ h : PieceInv M x.1.piece x.2.1 x.2.2, (pmap h).IsPlane → (pmap h).RotTrans →
    (pmap h).FaceTrans → ∀ u : Orbit.SDart (pdarts M x.1.piece x.2.1) → ℤ, (∀ y, 0 ≤ u y) →
      (NF x h).Spec u

/-- **Correctness of Algorithm 1 on the piece maps with subroutines depending on the call**: as
`arunL_spec`, when the subroutines meet their specifications at the calls of the recursion. -/
theorem arunLN_spec (NF : NFam M) {u : D → ℤ} (hu : ∀ d, 0 ≤ u d)
    {S T : Finset V} (hST : Disjoint S T) :
    ∀ (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D), NSpecOn M NF (Calls M τ Hs σ) →
      ∀ (hp : τ.PMOk M Hs σ),
      τ.Good M S T Hs → τ.PGood M Hs → τ.LeafOK M S T Hs →
      Disjoint S (hunion Hs) → Disjoint T (hunion Hs) →
      MSOut (pmap hp.pieceInv) (fun x => u x.1) (vimg M σ _ S) (vimg M σ _ T)
        (vimg M σ _ (hunion Hs)) (arunLN M NF u S T τ Hs σ)
  | .leaf Q, Hs, σ, _, hp, _, _, hl, hSA, hTA => by
    have h : PieceInv M Q Hs σ := hp
    rw [arunLN, dite_of_pos h]
    rcases hl with hl | hl
    · have hcard : (univ : Finset (SDart (pdarts M Q Hs))).card ≤ 2 := by
        rw [card_univ, Fintype.card_coe]
        exact (card_le_card (pdarts_subset Q Hs)).trans hl
      have := leafSolve_spec (M := pmap h) (u := fun x => u x.1) (fun _ => hu _)
        (Q := univ) (fun _ _ => mem_univ _) hcard (disjoint_vimg h hST hSA)
        (disjoint_vimg h hSA hSA) (disjoint_vimg h hTA hTA)
      rwa [capOn_univ] at this
    · have hall : ∀ x ∈ (univ : Finset (SDart (pdarts M Q Hs))), (pmap h).tail x ∈
          vimg M σ _ S ∪ vimg M σ _ T ∪ vimg M σ _ (hunion Hs) := fun x _ => by
        rw [← vimg_union, ← vimg_union]; exact mem_vimg.2 ⟨x, hl x.1 x.2, rfl⟩
      have := leafSolve_spec_ranked (M := pmap h) (u := fun x => u x.1) (fun _ => hu _)
        (Q := univ) (fun _ _ => mem_univ _) hall (disjoint_vimg h hST hSA)
        (disjoint_vimg h hSA hSA) (disjoint_vimg h hTA hTA)
      rwa [capOn_univ] at this
  | .node l r π, Hs, σ, hO, hp, hg, hpg, hl, hSA, hTA => by
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
    rw [arunLN, dite_of_pos hcond]
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
    generalize arunLN M NF u S T l Hs' _ = fl at il ⊢
    generalize arunLN M NF u S T r Hs' _ = fr at ir ⊢
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
    · exact @msOut_of_isEmpty _ _ _ _ _ _ _ _ _ _ (isEmpty_sDart hB) (isEmpty_sVert hB) _ _ _ _ _
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
    have key := sepStep_spec hO' (P := univ) (fun _ _ => mem_univ _) (segsP h π.segs hin)
      (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs) _ (fun H hH => pholes_path h hH) hπs hpw
      hps hcons h1 h2
    erw [capOn_univ, hunion_pholes] at key
    exact key

/-! ### The algorithm on a decomposition -/

variable (M) in
open Classical in
/-- **Algorithm 1 on a decomposition with subroutines depending on the call** (`runL` with
`arunLN`). -/
noncomputable def runLN (u : D → ℤ) (τ : ADec M) (NF : NFam M) (S T : Finset V) : D → ℤ :=
  if h : PieceInv M τ.piece [] (rotPerm M) ∧ (∀ d, d ∈ τ.piece) ∧ Nonempty D then
    (rootEmb h.1 ⟨Classical.choice h.2.2, mem_pdarts_nil h.2.1 _⟩).ext
      (arunLN M NF u S T τ [] (rotPerm M))
  else 0

/-- **Correctness of `runLN`** (as `runL_isMax`), when the subroutines meet their specifications
at the calls of the recursion from the root. -/
theorem runLN_isMax (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {u : D → ℤ}
    (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) {τ : ADec M}
    (hall : τ.piece = univ) (hgood : τ.Good M S T []) (hpg : τ.PGood M [])
    (hleaf : τ.LeafOK M S T []) {NF : NFam M} (hO : NSpecOn M NF (Calls M τ [] (rotPerm M))) :
    IsMax M u S T (runLN M u τ NF S T) := by
  by_cases hD : Nonempty D
  · have hall' : ∀ d, d ∈ τ.piece := fun d => by rw [hall]; exact mem_univ d
    have h0 : PieceInv M τ.piece [] (rotPerm M) := by
      rw [hall]; exact pieceInv_root hM hrot hface hD
    have hPM : τ.PMOk M [] (rotPerm M) :=
      ADec.PMOk.of_pieceInv τ [] _ List.Pairwise.nil hgood hpg h0
    have hcond : PieceInv M τ.piece [] (rotPerm M) ∧ (∀ d, d ∈ τ.piece) ∧ Nonempty D :=
      ⟨h0, hall', hD⟩
    rw [runLN, dite_of_pos hcond]
    refine (msOut_root hcond.1 hall' _ hST ?_).isMax
    exact arunLN_spec NF hu hST _ [] _ hO hPM hgood hpg hleaf (by simp [hunion])
      (by simp [hunion])
  · rw [not_nonempty_iff] at hD
    have h0 : ∀ g : D → ℤ, g = runLN M u τ NF S T := fun g => funext fun d => isEmptyElim d
    refine ⟨⟨⟨fun d => isEmptyElim d, fun d => isEmptyElim d⟩, fun v _ _ => ?_⟩,
      fun g _ => by rw [h0 g]⟩
    simp [CombMap.div]

/-! ### On the preprocessed map without loops -/

section Pre

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **`runLN` on the preprocessed map, restricted to the map** (the correctness part of
`maxflow_pre_cost_of`). -/
theorem runLN_pre_isMax (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V}
    (hST : Disjoint S T) {e₀ : V → D} (he₀ : ∀ v, M.tail (e₀ v) = v)
    {τ : ADec (preMap hrot he₀)}
    (hτ : BalDecA (preMap hrot he₀) (preTerm S) (preTerm T) 9 6 100000 τ)
    {NF : NFam (preMap hrot he₀)}
    (hO : NSpecOn (preMap hrot he₀) NF (Calls (preMap hrot he₀) τ [] (rotPerm (preMap hrot he₀)))) :
    IsMax M u S T (fun d =>
        runLN (preMap hrot he₀) (preCap u S T) τ NF (preTerm S) (preTerm T) (.inl (old d))) := by
  have : Nonempty D := ⟨e₀ hM.nonempty.some⟩
  have hP := triMap_isPlane hM hrot hface
  have he := triE_tail (hrot := hrot) he₀
  exact isMax_restrict (triMap_embeds hrot) (fun _ => rfl) (triCap_out u)
    (isMax_pendant he (triCap_nonneg hu) (runLN_isMax (CombMap.pendant_isPlane he hP)
      (CombMap.pendant_rotTrans he (triMap_rotTrans hrot))
      (CombMap.pendant_faceTrans he (triMap_faceTrans hrot))
      (pendCap_nonneg (triCap_nonneg hu) _ _ (sum_nonneg fun x _ => triCap_nonneg hu x))
      ((disjoint_image Sum.inr_injective).2 ((disjoint_image Sum.inl_injective).2 hST))
      hτ.1 hτ.2.1 hτ.2.2.1 hτ.2.2.2.1 hO))

variable (M) in
/-- **The algorithm with subroutines depending on the call, on the preprocessed map without
loops**, restricted to the darts of `M` (`nlRun` with `runLN`). -/
noncomputable def nlRunN (u : D → ℤ) (S T : Finset V) (τ : ADec (lpreMap M))
    (NF : NFam (lpreMap M)) : D → ℤ :=
  nlExt M fun x => runLN (lpreMap M) (preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)) τ NF
    (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) (.inl (old x))

/-- **Correctness of `nlRunN`**: on a plane map with transitive rotations and faces and a dart that
is not a loop, nonnegative capacities and disjoint terminals, for a decomposition of `lpreMap M`
meeting `BalDecA` and subroutines meeting their specifications at its calls, a maximum flow. -/
theorem nlRunN_isMax (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {u : D → ℤ}
    (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) {x₀ : D} (hx₀ : x₀ ∈ nlDarts M)
    {τ : ADec (lpreMap M)}
    (hτ : BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ)
    {NF : NFam (lpreMap M)}
    (hO : NSpecOn (lpreMap M) NF (Calls (lpreMap M) τ [] (rotPerm (lpreMap M)))) :
    IsMax M u S T (nlRunN M u S T τ NF) := by
  have hST' : Disjoint (nlTerm M S) (nlTerm M T) := by
    rw [disjoint_left]
    intro w h1 h2
    simp only [nlTerm, mem_filter, mem_univ, true_and] at h1 h2
    exact disjoint_left.1 hST h1 h2
  have h1 := runLN_pre_isMax (nlMap_isPlane hM hrot hface hx₀) nlMap_rotTrans nlMap_faceTrans
    (u := fun x => u x.1) (fun x => hu x.1) hST' nlE_tail hτ hO
  exact isMax_nlExt hrot hu h1

end Pre


section Bridge

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **`arunLO` is `arunLN` of the family of the implemented subroutines.** -/
theorem arunLO_eq_arunLN (NO : MOFam M) (u : D → ℤ) (S T : Finset V) :
    ∀ (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D),
      arunLO M NO u S T τ Hs σ = arunLN M (fun x h => (NO x h).nodes) u S T τ Hs σ
  | .leaf Q, Hs, σ => by rw [arunLO, arunLN]
  | .node l r π, Hs, σ => by
    rw [arunLO, arunLN, arunLO_eq_arunLN NO u S T l, arunLO_eq_arunLN NO u S T r]

/-- The family of the implemented subroutines meets `NSpecOn` where `NO` meets `OSpecOn`. -/
lemma nSpecOn_of_mo {NO : MOFam M} {Reach : MCall M → Prop} (hO : OSpecOn M NO Reach) :
    NSpecOn M (fun x h => (NO x h).nodes) Reach :=
  fun x hx h hpl hrot hface _ hu => MapOracles.nodes_spec (hO x hx h hpl hrot hface) hpl hu

end Bridge

end MfDrv

end BKMNW

end PlanarFlow
