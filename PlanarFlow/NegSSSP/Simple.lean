module

public import PlanarFlow.NegSSSP.Rec
public import NestedDissection.Spec

/-!
# The recursion on a simple graph, on the decomposition of a separator tree

The recursion `PlanarFlow.NegSSSP.run` is correct on every decomposition. This file fixes the
decomposition it runs on, from a separator tree of Lipton, Rose and Tarjan, after making the
graph simple (the assumption of Klein, Mozes and Weimann and of Mozes and Wulff-Nilsen, the
article, Section 2):

* **the simple graph** (`reps`): of the darts joining a vertex `u` to a vertex `v ≠ u`, only one
  is kept (`reps N`, closed under reversal, one dart for every ordered pair of adjacent vertices),
  with the least length of these darts (`minLen`); the loops are checked for a negative length
  (`negSSSPS`). A feasible potential of the simple graph is a feasible potential of the graph
  (`negSSSPS_potOut`);
* **the simple graph as a `SimpleGraph`** (`sgraph N`): `u` and `v` adjacent when a kept dart joins
  them;
* **the decomposition of a separator tree** (`conv`): a separator tree `t` of `sgraph N`
  (`NestedDissection.SepTree`: at every node a separator `s` and two parts `a` and `b` with no edge
  between them) gives the decomposition of the kept darts with an end in the vertices of `t`
  (`eset`): at a node, the darts of the part `a`, those with an end in `s` and none in `a` or `b`,
  and those of the part `b`, with the empty pieces left out (`NTree.mk`);
* `negDec N`: a decomposition of a separator tree of `sgraph N` with separators and
  boundaries of at most `50000 √m` vertices and parts of at most two thirds of the vertices, which
  exists on the maps the maximum-flow algorithm calls the subroutine on
  (`PlanarFlow/NegSSSP/SepCost.lean`), and the leaf of all kept darts otherwise;
  `negSSSPDec`: the recursion on it, which is correct on every map (`negSSSPDec_potOut`). Its
  boundaries need not lie on few faces; the maximum-flow algorithm uses instead the decomposition
  by simple cycles `PlanarFlow.NegSSSP.negDecF` (`PlanarFlow/NegSSSP/FaceDec.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset BKMNW CombMap NestedDissection NestedDissection.SepTree

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable (N : CombMap D V F)

/-! ### One dart for every ordered pair of adjacent vertices -/

/-- The key of the edge of a dart: the smaller index of its two darts. -/
noncomputable def ekey (d : D) : ℕ :=
  min (Fintype.equivFin D d).1 (Fintype.equivFin D (N.rev d)).1

lemma ekey_rev (d : D) : ekey N (N.rev d) = ekey N d := by
  unfold ekey; rw [N.rev_rev, min_comm]

/-- **The kept darts**: the darts that are not loops and whose edge has the least key among the
darts with the same ends. -/
noncomputable def reps : Finset D := by
  classical exact univ.filter fun d => N.tail d ≠ N.head d ∧
    ∀ x, N.tail x = N.tail d → N.head x = N.head d → ekey N d ≤ ekey N x

variable {N}

lemma mem_reps {d : D} : d ∈ reps N ↔ N.tail d ≠ N.head d ∧
    ∀ x, N.tail x = N.tail d → N.head x = N.head d → ekey N d ≤ ekey N x := by
  classical
  unfold reps; simp

lemma reps_loop {d : D} (h : d ∈ reps N) : N.tail d ≠ N.head d := (mem_reps.1 h).1

lemma reps_rev {d : D} (h : d ∈ reps N) : N.rev d ∈ reps N := by
  obtain ⟨h1, h2⟩ := mem_reps.1 h
  refine mem_reps.2 ⟨fun e => h1 (by simpa using e.symm), fun x hx1 hx2 => ?_⟩
  rw [ekey_rev, ← ekey_rev N x]
  refine h2 _ ?_ ?_
  · simp only [tail_rev, head_rev] at hx1 hx2 ⊢; exact hx2
  · simp only [tail_rev, head_rev] at hx1 hx2 ⊢; exact hx1

/-- **The kept darts are simple**: two of them with the same ends are equal. -/
lemma reps_simple {d d' : D} (h : d ∈ reps N) (h' : d' ∈ reps N) (ht : N.tail d = N.tail d')
    (hh : N.head d = N.head d') : d = d' := by
  have e1 := (mem_reps.1 h).2 d' ht.symm hh.symm
  have e2 := (mem_reps.1 h').2 d ht hh
  have hk : ekey N d = ekey N d' := le_antisymm e1 e2
  have hl := reps_loop h
  have key : ∀ {x y : D}, (Fintype.equivFin D x).1 = (Fintype.equivFin D y).1 → x = y :=
    fun e => (Fintype.equivFin D).injective (Fin.ext e)
  unfold ekey at hk
  rcases min_choice (Fintype.equivFin D d).1 (Fintype.equivFin D (N.rev d)).1 with h1 | h1 <;>
    rcases min_choice (Fintype.equivFin D d').1 (Fintype.equivFin D (N.rev d')).1 with h2 | h2 <;>
    rw [h1, h2] at hk
  · exact key hk
  · have e := key hk
    exact absurd (show N.tail d = N.head d by rw [hh, e, tail_rev]) hl
  · have e := key hk
    exact absurd (show N.tail d = N.head d by rw [ht, ← e, tail_rev]) hl
  · exact N.rev_injective (key hk)

/-- **Every dart that is not a loop has a kept dart with the same ends.** -/
lemma exists_reps {x : D} (hx : N.tail x ≠ N.head x) :
    ∃ d ∈ reps N, N.tail d = N.tail x ∧ N.head d = N.head x := by
  classical
  obtain ⟨d, hd, hmin⟩ := exists_min_image
    (univ.filter fun y => N.tail y = N.tail x ∧ N.head y = N.head x) (ekey N) ⟨x, by simp⟩
  simp only [mem_filter, mem_univ, true_and] at hd hmin
  refine ⟨d, mem_reps.2 ⟨by rw [hd.1, hd.2]; exact hx, fun y hy1 hy2 => ?_⟩, hd⟩
  exact hmin y ⟨hy1.trans hd.1, hy2.trans hd.2⟩

/-! ### The least lengths -/

variable (N) in
/-- The darts with the same ends as `d`. -/
noncomputable def par (d : D) : Finset D := by
  classical exact univ.filter fun x => N.tail x = N.tail d ∧ N.head x = N.head d

lemma mem_par {d x : D} : x ∈ par N d ↔ N.tail x = N.tail d ∧ N.head x = N.head d := by
  classical
  unfold par; simp

lemma mem_par_self (d : D) : d ∈ par N d := mem_par.2 ⟨rfl, rfl⟩

variable (N) in
/-- **The least length** of the darts with the same ends. -/
noncomputable def minLen (ℓ : D → ℤ) (d : D) : ℤ := (par N d).inf' ⟨d, mem_par_self d⟩ ℓ

lemma minLen_le (ℓ : D → ℤ) {d x : D} (ht : N.tail x = N.tail d) (hh : N.head x = N.head d) :
    minLen N ℓ d ≤ ℓ x :=
  inf'_le _ (mem_par.2 ⟨ht, hh⟩)

lemma exists_minLen (ℓ : D → ℤ) (d : D) :
    ∃ x, N.tail x = N.tail d ∧ N.head x = N.head d ∧ minLen N ℓ d = ℓ x := by
  obtain ⟨x, hx, e⟩ := exists_mem_eq_inf' ⟨d, mem_par_self d⟩ ℓ (s := par N d)
  exact ⟨x, (mem_par.1 hx).1, (mem_par.1 hx).2, e⟩

/-! ### The recursion on the simple graph -/

variable (N) in
/-- **Shortest paths with negative lengths through the simple graph**: `none` if a loop has a
negative length, otherwise the recursion on the decomposition `τ` (of the kept darts) with the
least lengths. -/
noncomputable def negSSSPS (mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ)
    (bf : DDG V → DDG V → Option (V → ℤ))
    (fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V → (Option V → ℤ) →
      Option V → Option ℤ) (τ : NTree D) (ℓ : D → ℤ) : Option (V → ℤ) := by
  classical exact
    if ∃ d, N.tail d = N.head d ∧ ℓ d < 0 then none else run N mssp bf fr τ (minLen N ℓ)

/-- **Correctness through the simple graph**: on a decomposition of the kept darts, the result is
a feasible potential of the graph of `N`, or `none` and the graph has no feasible potential. -/
theorem negSSSPS_potOut {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}
    (hmssp : PieceMSSPSpec N mssp) {bf : DDG V → DDG V → Option (V → ℤ)} (hbf : BFDDGSpec bf)
    {fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V → (Option V → ℤ) →
      Option V → Option ℤ} (hfr : FRSpec fr) {τ : NTree D} (hτ : τ.piece = reps N)
    (ℓ : D → ℤ) : PotOut (N.graph ℓ) (negSSSPS N mssp bf fr τ ℓ) := by
  classical
  unfold negSSSPS
  split_ifs with hneg
  · obtain ⟨d, hd, hl⟩ := hneg
    rintro ⟨p, hp⟩
    have := hp d
    simp only [graph, ← hd] at this
    omega
  push Not at hneg
  have h := run_potOut hmssp hbf hfr (minLen N ℓ) τ
  rw [hτ] at h
  rcases ho : run N mssp bf fr τ (minLen N ℓ) with _ | p
  · rw [ho] at h
    rintro ⟨p, hp⟩
    refine h ⟨p, fun a => ?_⟩
    obtain ⟨x, h1, h2, e⟩ := exists_minLen (N := N) ℓ a.1
    have := hp x
    simp only [graph] at this
    show p (N.head a.1) ≤ p (N.tail a.1) + minLen N ℓ a.1
    rw [e, ← h1, ← h2]; exact this
  · rw [ho] at h
    intro d
    show p (N.head d) ≤ p (N.tail d) + ℓ d
    by_cases hl : N.tail d = N.head d
    · rw [hl]; have := hneg d hl; omega
    · obtain ⟨d', hd', h1, h2⟩ := exists_reps hl
      have := h ⟨d', hd'⟩
      have hm := minLen_le (N := N) ℓ h1.symm h2.symm
      simp only [MSSP.pieceGraph] at this
      rw [h1, h2] at this
      omega

/-! ### The simple graph -/

variable (N) in
/-- **The simple graph**: two vertices are adjacent when a kept dart joins them. -/
def sgraph : SimpleGraph V where
  Adj u v := ∃ d ∈ reps N, N.tail d = u ∧ N.head d = v
  symm := ⟨fun _ _ ⟨d, hd, h1, h2⟩ =>
    ⟨N.rev d, reps_rev hd, by simpa using h2, by simpa using h1⟩⟩
  loopless := ⟨fun _ ⟨d, hd, h1, h2⟩ => reps_loop hd (h1.trans h2.symm)⟩

noncomputable instance : DecidableRel (sgraph N).Adj := Classical.decRel _

/-! ### The decomposition of a separator tree -/

variable (N) in
/-- The kept darts with an end in `U`. -/
noncomputable def eset (U : Finset V) : Finset D := by
  classical exact (reps N).filter fun d => N.tail d ∈ U ∨ N.head d ∈ U

lemma mem_eset {U : Finset V} {d : D} :
    d ∈ eset N U ↔ d ∈ reps N ∧ (N.tail d ∈ U ∨ N.head d ∈ U) := by
  classical
  unfold eset; simp

lemma eset_mono {U U' : Finset V} (h : U ⊆ U') : eset N U ⊆ eset N U' := fun d hd => by
  rw [mem_eset] at hd ⊢
  exact ⟨hd.1, hd.2.imp (fun x => h x) (fun x => h x)⟩

lemma eset_univ : eset N (univ : Finset V) = reps N := by
  ext d; simp [mem_eset]

namespace NTree

/-- **A node with the empty pieces left out**: the other child if one child is empty. -/
def mk (l r : NTree D) : NTree D :=
  if l.piece = ∅ then r else if r.piece = ∅ then l else .node l r

lemma piece_mk (l r : NTree D) : (mk l r).piece = l.piece ∪ r.piece := by
  unfold mk
  split_ifs with h1 h2
  · rw [h1, empty_union]
  · rw [h2, union_empty]
  · rfl

end NTree

variable (N) in
/-- The darts of a node of a separator tree, with vertices `U = s ∪ a ∪ b`, with an end in the
separator `s` and none in the parts `a` and `b`. -/
noncomputable def extra (U a b : Finset V) : Finset D := eset N U \ (eset N a ∪ eset N b)

variable (N) in
/-- **The decomposition of a separator tree**: at a node with separator `s` and parts `a` and
`b`, the decomposition of the part `a`, the darts `extra` with an end in `s` and none in the
parts, and the decomposition of the part `b`; at a leaf, the kept darts with an end in its
vertices. -/
noncomputable def conv : SepTree V → NTree D
  | .leaf s => .leaf (eset N s)
  | .node s a b => NTree.mk (NTree.mk (conv a) (.leaf (extra N (s ∪ a.verts ∪ b.verts) a.verts
      b.verts))) (conv b)

/-- The decomposition of a separator tree covers the kept darts with an end in its vertices. -/
theorem piece_conv : ∀ t : SepTree V, (conv N t).piece = eset N t.verts
  | .leaf s => rfl
  | .node s a b => by
    simp only [conv, NTree.piece_mk, NTree.piece, piece_conv a, piece_conv b, extra]
    have ha : eset N a.verts ⊆ eset N (s ∪ a.verts ∪ b.verts) :=
      eset_mono fun x hx => mem_union_left _ (mem_union_right _ hx)
    have hb : eset N b.verts ⊆ eset N (s ∪ a.verts ∪ b.verts) := eset_mono subset_union_right
    ext d
    simp only [mem_union, mem_sdiff]
    constructor
    · rintro ((h | ⟨h, -⟩) | h)
      · exact ha h
      · exact h
      · exact hb h
    · intro h
      by_cases h1 : d ∈ eset N a.verts
      · exact Or.inl (Or.inl h1)
      by_cases h2 : d ∈ eset N b.verts
      · exact Or.inr h2
      · exact Or.inl (Or.inr ⟨h, by tauto⟩)

variable (N) in
/-- The separator trees of `sgraph N` used: separators and boundaries of at most `50000 √m`
vertices at every subtree with `m` vertices, parts of at most two thirds of the vertices
(`PlanarSeparator.exists_sepTree`). -/
def GoodTree (t : SepTree V) : Prop :=
  t.verts = univ ∧ IsDissection (sgraph N) t ∧ AllNodes (SqrtBound (sgraph N) 50000 50000) t ∧
    AllNodes Shrinks t

variable (N) in
/-- **The decomposition of a separator tree**: of a separator tree meeting `GoodTree` if there is
one (on every plane map with transitive rotations and faces there is one,
`PlanarFlow.NegSSSP.exists_goodTree`), the leaf of all kept darts otherwise. -/
noncomputable def negDec : NTree D := by
  classical exact if h : ∃ t, GoodTree N t then conv N h.choose else .leaf (reps N)

lemma piece_negDec : (negDec N).piece = reps N := by
  classical
  unfold negDec
  split_ifs with h
  · rw [piece_conv, h.choose_spec.1, eset_univ]
  · rfl

variable (N) in
/-- **Shortest paths with negative lengths** in the graph of `N`: the recursion through the
simple graph on the decomposition `negDec N`. -/
noncomputable def negSSSPDec (mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ)
    (bf : DDG V → DDG V → Option (V → ℤ))
    (fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V → (Option V → ℤ) →
      Option V → Option ℤ) (ℓ : D → ℤ) : Option (V → ℤ) :=
  negSSSPS N mssp bf fr (negDec N) ℓ

/-- **Correctness of `negSSSPDec`**, on every map. -/
theorem negSSSPDec_potOut {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}
    (hmssp : PieceMSSPSpec N mssp) {bf : DDG V → DDG V → Option (V → ℤ)} (hbf : BFDDGSpec bf)
    {fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V → (Option V → ℤ) →
      Option V → Option ℤ} (hfr : FRSpec fr) (ℓ : D → ℤ) :
    PotOut (N.graph ℓ) (negSSSPDec N mssp bf fr ℓ) :=
  negSSSPS_potOut hmssp hbf hfr piece_negDec ℓ

/-- **The recursion on the dual map meets `NegSSSPSpec`**, on every map. -/
theorem negSSSPDec_spec_dual [Fintype F] [DecidableEq F] (M : CombMap D V F)
    {mssp : Finset D → (D → ℤ) → Finset F → F → F → Option ℤ}
    (hmssp : PieceMSSPSpec M.dual mssp) {bf : DDG F → DDG F → Option (F → ℤ)}
    (hbf : BFDDGSpec bf)
    {fr : DDG (Option F) → List (Option F × Option F × ℤ) → Option F → (Option F → ℤ) →
      Option F → Option ℤ} (hfr : FRSpec fr) :
    NegSSSPSpec M (negSSSPDec M.dual mssp bf fr) := fun ℓ => by
  rw [← dual_graph]
  exact negSSSPOut_of_potOut (negSSSPDec_potOut hmssp hbf hfr ℓ)

end NegSSSP

end PlanarFlow
