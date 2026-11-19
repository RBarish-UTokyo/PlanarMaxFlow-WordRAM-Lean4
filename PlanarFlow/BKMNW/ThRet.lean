module

public import PlanarFlow.BKMNW.ThSpec
public import PlanarFlow.BKMNW.NcHoleN
public import PlanarFlow.BKMNW.NrSpec

/-!
# The inputs of the push-backs are antisymmetric at the reachable calls; one start-vertex layout;
# the `retP`/`frmP` specifications bridged to the primed chain

Three layouts of the parts with their start vertices exist: `MfDrv.SegsOut'`
(`SgSem.lean`, with `NcStep.SegsAt'` from `r6807`, `NcPar.lean`) and `MfDrv.SegsOutV`/
`SegsAtV` (`NrFrM.lean`). They store the same words; they differ only in how the size bound is
written (`Gb + 1 + 3 s + L` vs `Gb + 1 + 2 s + L + s`). **The primed chain uses `SegsAt'`**;
here `segsOutV_iff`, `segsAtV_iff` (the layouts are equivalent), `SegsAt'.toV`, `SegsAtV.toA`.

`RetPSpecNV`/`FrmPSpecNV` (`NrSpec.lean`, met by `retP`/`frmP`: `retP_specNV`,
`frmP_specNV`) ask, besides `SegsAtV`, that the input flow be antisymmetric. The invariant
`arunLN_holeInv` covers only the holes; here the inputs of the two push-backs:

* `spec_ret_univ`; **`SCtx.retInv`**: from the hypotheses of `sepStep_spec` (`P = univ`), at every
  part `j`, the flow after the last hole (the input of `ret`) and the flow after `ret` (the input
  of `frm`) are pseudoflows (hence antisymmetric);
* `RetInvN`, **`arunLN_retInv_node`** (at a node call meeting the hypotheses of `arunLN_spec`),
  `retInvN_of_callOk` (from `CallOk` and `NSpecOn` on its calls);
* **`RetPSpecNV.toN'`**, **`FrmPSpecNV.toN'`**: these specifications give `RetPSpecN'`/`FrmPSpecN'`
  (the primed chain's) at the reachable calls (`u ≥ 0`, `Disjoint S T`, `NSpecOn`, `Reach` closed
  under calls).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv CombMap Relation Orbit PlanarSeparator.StDart WordRAM WordRAM.Machine
  NcStep

universe w

section Layout

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The two layouts of the parts with their start vertices are the same.** -/
theorem segsOutV_iff {en : ℕ → D} {m : ℕ} {π : HSep M} {lo hi Gb : ℕ} {mem : ℕ → ℕ} :
    SegsOutV M en m π lo hi Gb mem ↔ SegsOut' M en m π lo hi Gb mem :=
  ⟨fun h => ⟨h.1, by have := h.2.1; omega, h.2.2⟩,
    fun h => ⟨h.1, by have := h.2.1; omega, h.2.2⟩⟩

theorem segsAtV_iff {en : ℕ → D} {m : ℕ} {π : HSep M} {e b : ℕ} {c : Config} :
    SegsAtV M en m π e b c ↔ SegsAt' M en m π e b c := segsOutV_iff

lemma SegsAt'.toV {en : ℕ → D} {m : ℕ} {π : HSep M} {e b : ℕ} {c : Config}
    (h : SegsAt' M en m π e b c) : SegsAtV M en m π e b c := segsAtV_iff.2 h

lemma SegsAtV.toA {en : ℕ → D} {m : ℕ} {π : HSep M} {e b : ℕ} {c : Config}
    (h : SegsAtV M en m π e b c) : SegsAt' M en m π e b c := segsAtV_iff.1 h

end Layout

section Inv

variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F'] {M' : CombMap D' V' F'} {u : D' → ℤ}

/-- The specification of `ret` at `P = univ`. -/
lemma spec_ret_univ {O : NodeOracles M'} (hO : O.Spec u) {f : D' → ℤ} {X S : Finset V'}
    (hf : IsPseudo M' u f) (hXS : Disjoint X S) (hX : ∀ v ∈ X, M'.div f v ≤ 0)
    (hW : ∃ W, X ⊆ W ∧ Closed M' u f W ∧ ∀ v ∈ W, v ∉ S → v ∉ X → M'.div f v = 0) :
    RetOut M' u f (O.ret u f X S) X S := by
  have := hO.ret univ f X S
  rw [capOn_univ] at this
  exact this hf hXS hX hW

/-- **The inputs of the two push-backs of the part `j` are pseudoflows** (from the hypotheses of
`sepStep_spec` with `P = univ`): the flow after the last hole and the flow after `ret`. -/
theorem SCtx.retInv (C : SCtx M') (hO : C.O.Spec C.U) (hP : C.P = univ)
    (hHs : ∀ H ∈ C.Hs, ∃ πH : SPath M', πH.verts = H)
    (hπs : ∀ π ∈ C.L, Disjoint π.verts (C.S ∪ C.T ∪ hunion C.Hs))
    (hpw : (C.L.map SPath.verts).Pairwise Disjoint)
    (hps : IsPseudo M' C.U C.f)
    (hcons : ∀ v, v ∉ C.S → v ∉ C.T → v ∉ hunion C.Hs ∪ hunion (C.L.map SPath.verts) →
      M'.div C.f v = 0)
    (h1 : NoPath M' C.U C.f C.S (C.T ∪ (hunion C.Hs ∪ hunion (C.L.map SPath.verts))))
    (h2 : NoPath M' C.U C.f ((hunion C.Hs ∪ hunion (C.L.map SPath.verts)) ∪ C.S) C.T)
    {j : ℕ} {πj : SPath M'} (hj : C.L[j]? = some πj) :
    IsPseudo M' C.U (C.hole j πj (C.holes j).length) ∧ IsPseudo M' C.U (C.ret j πj) := by
  classical
  have hlt : j < C.L.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  have h0 : SegPre C.U C.S C.T C.Hs C.L 0 C.f := ⟨hps, hcons, h1, h2⟩
  obtain ⟨sps, scons, s1, s2⟩ := segPre_all hO hHs hπs hpw h0 j hlt.le
  have hseg : C.seg j = sst C.O C.U C.S C.T C.Hs univ C.L C.f j := by
    rw [SCtx.seg, hP]
  rw [← hseg] at sps scons s1 s2
  have hC := seg_disj hπs hpw hj
  have hHl := sHoles_path hHs C.L j
  have e : hunion (sHoles C.Hs C.L j) ∪ πj.verts = hunion C.Hs ∪ segRest C.L j := by
    rw [hunion_sHoles, segRest_eq hj]
    ext v; simp only [mem_union]; tauto
  rw [← e] at scons s1 s2
  have n0 := NInv.ofFix (A := hunion (sHoles C.Hs C.L j)) sps scons s1 s2
    (spec_fix_univ hO πj sps)
  have n1 := ninv_hole hO hHl hC n0 _ le_rfl
  rw [List.take_length] at n1
  have ehole : C.hole j πj (C.holes j).length =
      hst C.O C.U πj (sHoles C.Hs C.L j) (C.O.fix C.U (C.seg j) πj) (sHoles C.Hs C.L j).length :=
    rfl
  rw [← ehole] at n1
  refine ⟨n1.pseudo, ?_⟩
  have hSC : Disjoint C.S πj.verts :=
    (disjoint_of_subset_right (subset_union_left.trans subset_union_left) hC).symm
  have o1 := spec_ret_univ hO (X := posSet M' (C.hole j πj (C.holes j).length) πj.verts) (S := C.S)
    n1.pseudo (disjoint_of_subset_left posSet_subset hSC.symm)
    (fun v hv => (mem_posSet.1 hv).2.le) (by
      obtain ⟨W, hW1, hW2, hW3⟩ := ((n1.acsT.mono (posSet_subset.trans
        (subset_union_right.trans subset_union_left)) subset_rfl).union_right
        (noPath_hunion_right fun H hH => (n1.done H hH).1)).union_right n1.pn
      refine ⟨W, hW1, hW3, fun v hv hvS hvX => ?_⟩
      have hvT : v ∉ C.T := fun h => disjoint_left.1 hW2 hv (by simp [h])
      have hvA : v ∉ hunion (sHoles C.Hs C.L j) := fun h => disjoint_left.1 hW2 hv (by simp [h])
      by_cases hvC : v ∈ πj.verts
      · by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact hvX (mem_posSet.2 ⟨hvC, hlt⟩)
        · exact disjoint_left.1 hW2 hv (by simp [mem_negSet.2 ⟨hvC, hlt⟩])
      · exact n1.cons v hvS hvT (by simp [hvA, hvC]))
  exact o1.pseudo

end Inv

section Node

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **The inputs of the push-backs at a node call are antisymmetric**: for every part `j` of the
unrolled step (`xCtxN`), the flow after the last hole (the input of `ret`) and the flow after `ret`
(the input of `frm`). -/
def RetInvN (NF : NFam M) (u : D → ℤ) (S T : Finset V) (l r : ADec M) (π : HSep M)
    (Hs : List (Finset V)) (σ : Perm D) : Prop :=
  ∀ (h : SCond M l r π Hs σ) (j : ℕ) (πj : SPath (pmap h.1)),
    (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj →
    (pmap h.1).IsAntisymm ((xCtxN M NF u S T l r π Hs σ h).hole j πj
      ((xCtxN M NF u S T l r π Hs σ h).holes j).length) ∧
    (pmap h.1).IsAntisymm ((xCtxN M NF u S T l r π Hs σ h).ret j πj)

/-- **The flows before and after the push-back to the sources are pseudoflows** at a node call
meeting the hypotheses of `arunLN_spec` (the proof of `arunLN_holeInv_node`, then `SCtx.retInv`). -/
theorem arunLN_retInv_node (NF : NFam M) {u : D → ℤ} (hu : ∀ d, 0 ≤ u d)
    {S T : Finset V} (hST : Disjoint S T) (l r : ADec M) (π : HSep M) (Hs : List (Finset V))
    (σ : Perm D) (hO : NSpecOn M NF (Calls M (.node l r π) Hs σ))
    (hp : (ADec.node l r π).PMOk M Hs σ) (hg : (ADec.node l r π).Good M S T Hs)
    (hpg : (ADec.node l r π).PGood M Hs) (hl : (ADec.node l r π).LeafOK M S T Hs)
    (hSA : Disjoint S (hunion Hs)) (hTA : Disjoint T (hunion Hs)) :
    RetInvN M NF u S T l r π Hs σ := by
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
  · intro h' j πj hj
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
  intro h' j πj hj
  have := SCtx.retInv (xCtxN M NF u S T l r π Hs σ h') hO' rfl
    (fun H hH => pholes_path h hH) hπs hpw hps hcons h1 h2 hj
  exact ⟨this.1.antisymm, this.2.antisymm⟩


/-- **The inputs of the push-backs at a node call with the invariants `CallOk`** are
antisymmetric, when the subroutines meet their specifications at its calls. -/
theorem retInvN_of_callOk (NF : NFam M) {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V}
    (hST : Disjoint S T) {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    (hO : NSpecOn M NF (Calls M (.node l r π) Hs σ))
    (hok : CallOk M S T (.node l r π, Hs, σ)) : RetInvN M NF u S T l r π Hs σ :=
  arunLN_retInv_node NF hu hST l r π Hs σ hO hok.1 hok.2.1 hok.2.2.1 hok.2.2.2.1
    hok.2.2.2.2.1 hok.2.2.2.2.2.1

end Node

section Bridge

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {Reach : MCall M → Prop} {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}
  {I : Input} {W Wz : ℕ} {wzc : ℕ → ℕ → ℕ} {NF : NFam M} {retP frmP : Stmt}
  {rtT fmT : MCall M → ℕ → ℕ} {rO : MCall M → ℕ}

/-- **The specification of `retP` gives the primed chain's** at the reachable calls (the input
of `ret` is antisymmetric there, `retInvN_of_callOk`; `SegsAt'` gives `SegsAtV`). -/
theorem RetPSpecNV.toN' (hu : ∀ d, 0 ≤ u d) (hST : Disjoint S T) (hO : NSpecOn M NF Reach)
    (hR : ∀ x y, Reach x → Calls M x.1 x.2.1 x.2.2 y → Reach y)
    (h : RetPSpecNV M NF Reach gid u S T Z I W Wz retP rtT rO) :
    RetPSpecN' M NF Reach gid u S T Z I W Wz wzc retP rtT rO :=
  fun l r π Hs σ hs d e b m en j πj hx hok a3 a4 a5 a6 _ hj =>
    (h l r π Hs σ hs d e b m en j πj hx hok a3 a4 a5 a6 hj
      (retInvN_of_callOk NF hu hST (nSpecOn_calls hO hR hx) hok hs j πj hj).1).mono_pre
      fun _ hc => ⟨hc.1, SegsAt'.toV hc.2⟩

/-- **The specification of `frmP` gives the primed chain's** at the reachable calls. -/
theorem FrmPSpecNV.toN' (hu : ∀ d, 0 ≤ u d) (hST : Disjoint S T) (hO : NSpecOn M NF Reach)
    (hR : ∀ x y, Reach x → Calls M x.1 x.2.1 x.2.2 y → Reach y)
    (h : FrmPSpecNV M NF Reach gid u S T Z I W Wz frmP fmT rO) :
    FrmPSpecN' M NF Reach gid u S T Z I W Wz wzc frmP fmT rO :=
  fun l r π Hs σ hs d e b m en j πj hx hok a3 a4 a5 a6 _ hj =>
    (h l r π Hs σ hs d e b m en j πj hx hok a3 a4 a5 a6 hj
      (retInvN_of_callOk NF hu hST (nSpecOn_calls hO hR hx) hok hs j πj hj).2).mono_pre
      fun _ hc => ⟨hc.1, SegsAt'.toV hc.2⟩

end Bridge

end MfDrv

end BKMNW

end PlanarFlow
