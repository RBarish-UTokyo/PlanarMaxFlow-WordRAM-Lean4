module

public import PlanarFlow.BKMNW.PieceRun
public import PlanarFlow.BKMNW.Main
public import PlanarFlow.Klein.Bridge

/-!
# Algorithm 1 on the piece maps

This file runs Algorithm 1 of the article as the article does: **every recursive step runs its
subroutines on the piece map** (`PlanarFlow.BKMNW.pmap`: the darts of the piece outside its
holes, the holes contracted into single vertices), of the size of the piece, and the flows are
functions on the darts of the piece maps.

* `PlaneOracles`: the planar subroutines as **families over all maps** (FR-Dijkstra on every finite
  type; shortest paths with negative lengths and single-source single-sink maximum flow on every
  map), and `PlaneOracles.Spec` their specifications on every plane map with transitive rotations
  and faces. Multiple-source shortest paths is Klein's trip on the cut of the dual graph along
  the separator (`PlanarFlow.Klein.msspPlaneK`), which meets its specification on these maps
  (`PlanarFlow.Klein.msspPlaneK_spec`); the data structure `msspPlane` of Das, Kipouridis,
  Probst Gutenberg and Wulff-Nilsen, which meets it too (`PlanarFlow.BKMNW.msspPlane_spec`), is
  kept in the library.
* `arunL`: **Algorithm 1 on the piece maps.** At a leaf, the leaf solver on the piece map; at a
  node with separator `π` (a simple path through the holes), the two recursive calls on the child
  piece maps (computed from the piece map by `PlanarFlow.BKMNW.childRot`, which contracts the
  separator with the holes it meets), the sum of their flows on the darts of the piece map
  (`joinFlow`), and the recursive step `PlanarFlow.BKMNW.sepStep` on the piece map with its
  terminals, its holes (`PlanarFlow.BKMNW.pholes`, one vertex each) and the parts of the separator
  off the holes (`PlanarFlow.BKMNW.segsP`, simple paths of the piece map), with the implemented
  subroutines `PlanarFlow.BKMNW.impl` of the piece map.
* `arunL_spec`: **the recursion meets the specification `MSOut` on every piece map**, by
  `PlanarFlow.BKMNW.combine` and `PlanarFlow.BKMNW.sepStep_spec` on the piece map, the outputs of
  the children transferred to it (`PlanarFlow.BKMNW.msOut_child`, `PlanarFlow.BKMNW.MSOut.widen`).
* `runL`, `runL_isMax`: **the algorithm on a decomposition and its correctness**: the output on
  the piece map of the whole map, transferred to the map (`PlanarFlow.BKMNW.msOut_root`), is a
  maximum flow, for every decomposition that is good (`ADec.Good`), has its pieces connected after
  contracting their holes with their separators in them (`ADec.PGood`), and leaves solved by the
  leaf solver (`ADec.LeafOK`: at most one edge, or only terminals and holes as vertices). Separators
  may pass through the holes, and may be paths of one vertex. Such decompositions exist on every
  plane map (`PlanarFlow.BKMNW.exists_dec`, `PlanarFlow/BKMNW/Chain.lean`), so the theorem is not
  vacuous.
* The decomposition `PlanarFlow.BKMNW.chainDec` and the planar subroutines
  `PlanarFlow.BKMNW.planeOracles` give the algorithm `PlanarFlow.BKMNW.algo`, correct on every
  plane map (`PlanarFlow.BKMNW.maxflow_plane`, `PlanarFlow/BKMNW/MaxFlow.lean`). This supersedes
  `bkmnwL_isMax` (removed), which assumed a separator subroutine meeting a specification over all
  connected pieces that cannot be met.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv CombMap Relation Orbit

universe w

/-! ### The planar subroutines, for every map -/

/-- **The planar subroutines, as families over all maps**: FR-Dijkstra on every finite type,
shortest paths with negative lengths and single-source single-sink maximum flow on every map. -/
structure PlaneOracles : Type (w + 1) where
  /-- FR-Dijkstra. -/
  fr : (X : Type w) → [Fintype X] → [DecidableEq X] → FRFun X
  /-- Shortest paths with negative lengths in the dual graph. -/
  negSSSP : {D V F : Type w} → [Fintype D] → [DecidableEq D] → [Fintype V] → [DecidableEq V] →
    [Fintype F] → [DecidableEq F] → CombMap D V F → (D → ℤ) → Option (F → ℤ)
  /-- Single-source single-sink maximum flow. -/
  stflow : {D V F : Type w} → [Fintype D] → [DecidableEq D] → [Fintype V] → [DecidableEq V] →
    [Fintype F] → [DecidableEq F] → CombMap D V F → (D → ℤ) → Finset V → Finset V → D → ℤ

/-- **The specifications of the planar subroutines**, on every plane map with transitive rotations
and faces. -/
structure PlaneOracles.Spec (O : PlaneOracles.{w}) : Prop where
  fr : ∀ (X : Type w) [Fintype X] [DecidableEq X], FRSpec (O.fr X)
  negSSSP : ∀ {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] (M : CombMap D V F), M.IsPlane → M.RotTrans → M.FaceTrans →
    NegSSSPSpec M (O.negSSSP M)
  stflow : ∀ {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] (M : CombMap D V F), M.IsPlane → M.RotTrans → M.FaceTrans →
    STFlowSpec M (O.stflow M)

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-! ### The recursion -/

/-- The sum of the flows of the two children, on the darts of the parent piece map. -/
def joinFlow {B Bl Br : Finset D} (fl : SDart Bl → ℤ) (fr : SDart Br → ℤ) (x : SDart B) : ℤ :=
  (if hx : x.1 ∈ Bl then fl ⟨x.1, hx⟩ else 0) + (if hx : x.1 ∈ Br then fr ⟨x.1, hx⟩ else 0)

variable (M) in
open Classical in
/-- **Algorithm 1 on the piece maps**: the flow it computes on the darts of the piece map of the
piece of `τ` with holes `Hs`, from the rotation `σ` of that piece map. -/
noncomputable def arunL (O : PlaneOracles.{w}) (u : D → ℤ) (S T : Finset V) :
    (τ : ADec M) → (Hs : List (Finset V)) → (σ : Perm D) → SDart (pdarts M τ.piece Hs) → ℤ
  | .leaf Q, Hs, σ =>
    if h : PieceInv M Q Hs σ then
      leafSolve (pmap h) (fun x => u x.1) (vimg M σ _ S) (vimg M σ _ T) (vimg M σ _ (hunion Hs))
    else 0
  | .node l r π, Hs, σ =>
    if h : PieceInv M (l.piece ∪ r.piece) Hs σ ∧ ∀ s ∈ π.segs, SegIn M (l.piece ∪ r.piece) Hs s then
      sepStep (impl (pmap h.1) (Klein.msspPlaneK (pmap h.1)) (O.fr _) (O.negSSSP (pmap h.1))
          (O.stflow (pmap h.1)))
        (fun x => u x.1) (vimg M σ _ S) (vimg M σ _ T) (pholes M σ _ Hs) univ
        (segsP h.1 π.segs h.2)
        (joinFlow
          (arunL O u S T l (childHoles Hs π.path.mverts)
            (childRot M σ (pdarts M (l.piece ∪ r.piece) Hs) π.path.darts
              (pdarts M l.piece (childHoles Hs π.path.mverts))))
          (arunL O u S T r (childHoles Hs π.path.mverts)
            (childRot M σ (pdarts M (l.piece ∪ r.piece) Hs) π.path.darts
              (pdarts M r.piece (childHoles Hs π.path.mverts)))))
    else 0

/-! ### Correctness -/

namespace ADec

variable (M) in
/-- **The leaves solved by the leaf solver** (`PlanarFlow.BKMNW.leafSolve`): a leaf of at most one
edge, or a leaf every dart of whose piece map has its tail among the sources, the sinks and the
holes (`PlanarFlow.BKMNW.leafSolve_spec_ranked`). -/
def LeafOK (S T : Finset V) : ADec M → List (Finset V) → Prop
  | leaf Q, Hs => Q.card ≤ 2 ∨ ∀ d ∈ pdarts M Q Hs, M.tail d ∈ S ∪ T ∪ hunion Hs
  | node l r π, Hs => l.LeafOK S T (childHoles Hs π.path.mverts) ∧
      r.LeafOK S T (childHoles Hs π.path.mverts)

/-- Leaves of at most one edge are solved by the leaf solver. -/
lemma LeafLe.leafOK {S T : Finset V} :
    ∀ {τ : ADec M} {Hs : List (Finset V)}, τ.LeafLe 2 → τ.LeafOK M S T Hs
  | leaf _, _, h => Or.inl h
  | node _ _ _, _, h => ⟨h.1.leafOK, h.2.leafOK⟩

end ADec

lemma dite_of_pos {α : Sort*} {c : Prop} {_ : Decidable c} (h : c) {t : c → α} {e : ¬ c → α} :
    dite c t e = t h := by simp [h]

/-- With no darts and no vertices, everything is an output of the recursion. -/
lemma msOut_of_isEmpty {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V']
    [DecidableEq V'] [Fintype F'] [DecidableEq F'] {M' : CombMap D' V' F'} [IsEmpty D']
    [IsEmpty V'] (U f : D' → ℤ) (S T A : Finset V') : MSOut M' U S T A f := by
  have hX : ∀ X : Finset V', X = ∅ := fun X => eq_empty_of_isEmpty X
  have np : ∀ X Y : Finset V', NoPath M' U f X Y := fun X Y =>
    ⟨X, subset_rfl, by rw [hX Y]; exact disjoint_empty_right _, fun d => isEmptyElim d⟩
  exact ⟨⟨fun d => isEmptyElim d, fun d => isEmptyElim d⟩, fun v => isEmptyElim v, np _ _,
    np _ _, np _ _⟩

/-- With no capacities and no flow, every set is closed. -/
lemma msOut_zero {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V']
    [DecidableEq V'] [Fintype F'] [DecidableEq F'] {M' : CombMap D' V' F'} {S T A : Finset V'}
    (hST : Disjoint S T) (hSA : Disjoint S A) (hAT : Disjoint A T) :
    MSOut M' 0 S T A 0 := by
  have np : ∀ X Y : Finset V', Disjoint X Y → NoPath M' 0 0 X Y := fun X Y h =>
    ⟨X, subset_rfl, h, fun _ _ _ => rfl⟩
  exact ⟨⟨fun _ => by simp, fun _ => le_rfl⟩, fun v _ _ _ => by simp [CombMap.div],
    np _ _ hST, np _ _ hSA, np _ _ hAT⟩

lemma isEmpty_sVert {σ : Perm D} {B : Finset D} (hB : B = ∅) : IsEmpty (SVert σ B) :=
  ⟨fun w => Quotient.inductionOn w fun x => by have := x.2; simp [hB] at this⟩

lemma isEmpty_sDart {B : Finset D} (hB : B = ∅) : IsEmpty (SDart B) :=
  ⟨fun x => by have := x.2; simp [hB] at this⟩

/-- A dart of a piece in neither child piece map lies inside a hole of the children. -/
lemma inner_sep {l r : Finset D} {Hs' : List (Finset V)} {d : D} (hd : d ∈ l ∪ r)
    (hl : d ∉ pdarts M l Hs') (hr : d ∉ pdarts M r Hs') :
    M.tail d ∈ hunion Hs' ∧ M.head d ∈ hunion Hs' := by
  have hin : Inner M Hs' d := by
    rcases mem_union.1 hd with h | h
    · by_contra hc; exact hl (mem_pdarts.2 ⟨h, hc⟩)
    · by_contra hc; exact hr (mem_pdarts.2 ⟨h, hc⟩)
  obtain ⟨H, hH, h1, h2⟩ := hin
  exact ⟨subset_hunion hH h1, subset_hunion hH h2⟩

/-- **Correctness of Algorithm 1 on the piece maps**: on every piece map of a good decomposition
with its pieces as in the article, the recursion meets the specification `MSOut`. -/
theorem arunL_spec (O : PlaneOracles.{w}) (hO : O.Spec) {u : D → ℤ} (hu : ∀ d, 0 ≤ u d)
    {S T : Finset V} (hST : Disjoint S T) :
    ∀ (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D) (hp : τ.PMOk M Hs σ),
      τ.Good M S T Hs → τ.PGood M Hs → τ.LeafOK M S T Hs →
      Disjoint S (hunion Hs) → Disjoint T (hunion Hs) →
      MSOut (pmap hp.pieceInv) (fun x => u x.1) (vimg M σ _ S) (vimg M σ _ T)
        (vimg M σ _ (hunion Hs)) (arunL M O u S T τ Hs σ)
  | .leaf Q, Hs, σ, hp, _, _, hl, hSA, hTA => by
    have h : PieceInv M Q Hs σ := hp
    rw [arunL, dite_of_pos h]
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
  | .node l r π, Hs, σ, hp, hg, hpg, hl, hSA, hTA => by
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
    rw [arunL, dite_of_pos hcond]
    set Hs' := childHoles Hs π.path.mverts with hHs'
    have eHs' : hunion Hs' = hunion Hs ∪ π.path.mverts := by
      rw [hHs', hunion_childHoles]
    have hSA' : Disjoint S (hunion Hs') := by
      rw [eHs']; exact disjoint_union_right.2 ⟨hSA, hSC⟩
    have hTA' : Disjoint T (hunion Hs') := by
      rw [eHs']; exact disjoint_union_right.2 ⟨hTA, hTC⟩
    have il := arunL_spec O hO hu hST l _ _ hpl gl pgl hl.1 hSA' hTA'
    have ir := arunL_spec O hO hu hST r _ _ hpr gr pgr hl.2 hSA' hTA'
    generalize arunL M O u S T l Hs' _ = fl at il ⊢
    generalize arunL M O u S T r Hs' _ = fr at ir ⊢
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
    have hO' := impl_spec hpl' (u := fun x : SDart (pdarts M (l.piece ∪ r.piece) Hs) => u x.1)
      (fun _ => hu _) (Klein.msspPlaneK_spec hpl' hrot hface) (hO.fr _)
      (hO.negSSSP _ hpl' hrot hface)
      (hO.stflow _ hpl' hrot hface)
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
    rw [capOn_univ, hunion_pholes] at key
    exact key

/-! ### The algorithm -/

variable (M) in
open Classical in
/-- **Algorithm 1 with every recursive step on its piece map, on a given decomposition** `τ` of
the darts of `M`: the recursion `arunL` from the piece map of the whole map, with the implemented
subroutines; the flow computed on the piece map of the whole map, as a flow on the map. -/
noncomputable def runL (u : D → ℤ) (τ : ADec M) (O : PlaneOracles.{w}) (S T : Finset V) :
    D → ℤ :=
  if h : PieceInv M τ.piece [] (rotPerm M) ∧ (∀ d, d ∈ τ.piece) ∧ Nonempty D then
    (rootEmb h.1 ⟨Classical.choice h.2.2, mem_pdarts_nil h.2.1 _⟩).ext
      (arunL M O u S T τ [] (rotPerm M))
  else 0

/-- **Correctness of Algorithm 1 with every recursive step on its piece map**: on a plane map with
transitive rotations and faces and nonnegative capacities, for every decomposition of its darts
that is good for the correctness proof (`ADec.Good`: shared vertices on the separators or in the
holes, separators avoiding the terminals, the holes met by a separator merged with it), whose
pieces are connected after contracting their holes and contain their separators, simple paths
through the holes (`ADec.PGood`), and whose leaves are solved by the leaf solver
(`ADec.LeafOK`), and with the planar subroutines meeting their specifications on every plane map,
the result is a maximum flow from `S` to `T`. The hypotheses on the decomposition can be met on
every such map (`PlanarFlow.BKMNW.exists_dec`), and those on the subroutines too
(`PlanarFlow.BKMNW.exists_planeOracles`). -/
theorem runL_isMax (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {u : D → ℤ}
    (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) {τ : ADec M}
    (hall : τ.piece = univ) (hgood : τ.Good M S T []) (hpg : τ.PGood M [])
    (hleaf : τ.LeafOK M S T [])
    {O : PlaneOracles.{w}} (hO : O.Spec) : IsMax M u S T (runL M u τ O S T) := by
  by_cases hD : Nonempty D
  · have hall' : ∀ d, d ∈ τ.piece := fun d => by rw [hall]; exact mem_univ d
    have h0 : PieceInv M τ.piece [] (rotPerm M) := by
      rw [hall]; exact pieceInv_root hM hrot hface hD
    have hPM : τ.PMOk M [] (rotPerm M) :=
      ADec.PMOk.of_pieceInv τ [] _ List.Pairwise.nil hgood hpg h0
    have hcond : PieceInv M τ.piece [] (rotPerm M) ∧ (∀ d, d ∈ τ.piece) ∧ Nonempty D :=
      ⟨h0, hall', hD⟩
    rw [runL, dite_of_pos hcond]
    refine (msOut_root hcond.1 hall' _ hST ?_).isMax
    exact arunL_spec O hO hu hST _ [] _ hPM hgood hpg hleaf (by simp [hunion]) (by simp [hunion])
  · rw [not_nonempty_iff] at hD
    have h0 : ∀ g : D → ℤ, g = runL M u τ O S T := fun g => funext fun d => isEmptyElim d
    refine ⟨⟨⟨fun d => isEmptyElim d, fun d => isEmptyElim d⟩, fun v _ _ => ?_⟩,
      fun g _ => by rw [h0 g]⟩
    simp [CombMap.div]

end BKMNW

end PlanarFlow
