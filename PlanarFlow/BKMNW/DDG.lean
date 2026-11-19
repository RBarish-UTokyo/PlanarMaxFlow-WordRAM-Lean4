module

public import PlanarFlow.BKMNW.Dist

/-!
# Dense distance graphs, FR-Dijkstra, and the decomposition of walks

In the algorithm of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J. Comput. 46(4),
2017, Section 3.2), the shortest-path computations of the fixing procedure are carried out on a
*dense distance graph*: a table `D` of the distances, in a graph `H`, between the vertices of a
set `X`, together with a set of explicit arcs between vertices of `X`. FR-Dijkstra
(Fakcharoenphol and Rao, J. Comput. System Sci. 72(5), 2006, with the price-function variant of
Section 3.2.2 of the article) computes the distances from a vertex of `X` in this union.

* `DDG`: a dense distance graph (the vertices `bdry` and a length, or no arc, for every ordered
  pair of them); `IsDDGOf G H`: its lengths are the distances in `G` between its vertices.
* `DDG.union H E`: the union of `H` with the explicit arcs `E` (source, target, length), as a
  digraph. This is the input of FR-Dijkstra in the article.
* `FRSpec`: **the specification of FR-Dijkstra**: given a feasible potential of the union (the
  price function), the distances from a root in the union.
* `isDist_union`: **the decomposition of walks.** Let the arcs of `G` be split into the arcs of
  `H` (`inH`) and explicit arcs (the list `L`), every explicit arc having both ends in `B`. If the
  dense distance graph of `H` on `B` is known, then for `x, y ∈ B` the distance from `x` to `y`
  in `G` is the distance in the union of the dense distance graph and the explicit arcs. A walk of
  `G` between vertices of `B` splits into maximal subwalks in `H`, whose ends are in `B`, and
  explicit arcs (`exists_union_walk`); conversely every arc of the union is a walk of `G` of the
  same length (`exists_walk_of_union`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset

variable {X A : Type*}

/-- A dense distance graph on the vertices `bdry`: a length (or `none`, no arc) for every ordered
pair of them. -/
structure DDG (X : Type*) where
  /-- The vertices. -/
  bdry : Finset X
  /-- The lengths. -/
  len : X → X → Option ℤ

/-- `H` is **the dense distance graph of `G` on its vertices**: its lengths are the distances in
`G` between them. -/
def IsDDGOf (G : Digraph X A) (H : DDG X) : Prop :=
  ∀ b ∈ H.bdry, ∃ δ, IsDist G b δ ∧ ∀ b' ∈ H.bdry, H.len b b' = δ b'

/-- The arcs of a dense distance graph: the ordered pairs of its vertices with a length. -/
def DDG.Arc (H : DDG X) : Type _ :=
  {p : X × X // p.1 ∈ H.bdry ∧ p.2 ∈ H.bdry ∧ (H.len p.1 p.2).isSome}

/-- **The union of a dense distance graph `H` and the explicit arcs `E`** (source, target,
length), as a digraph: the input of FR-Dijkstra. -/
def DDG.union (H : DDG X) (E : List (X × X × ℤ)) : Digraph X (H.Arc ⊕ Fin E.length) where
  src := Sum.elim (fun p => p.1.1) fun i => (E.get i).1
  dst := Sum.elim (fun p => p.1.2) fun i => (E.get i).2.1
  len := Sum.elim (fun p => (H.len p.1.1 p.1.2).getD 0) fun i => (E.get i).2.2

@[simp] lemma DDG.union_src_inl (H : DDG X) (E : List (X × X × ℤ)) (p : H.Arc) :
    (H.union E).src (.inl p) = p.1.1 := rfl
@[simp] lemma DDG.union_dst_inl (H : DDG X) (E : List (X × X × ℤ)) (p : H.Arc) :
    (H.union E).dst (.inl p) = p.1.2 := rfl
@[simp] lemma DDG.union_len_inl (H : DDG X) (E : List (X × X × ℤ)) (p : H.Arc) :
    (H.union E).len (.inl p) = (H.len p.1.1 p.1.2).getD 0 := rfl
@[simp] lemma DDG.union_src_inr (H : DDG X) (E : List (X × X × ℤ)) (i : Fin E.length) :
    (H.union E).src (.inr i) = E[i.1].1 := rfl
@[simp] lemma DDG.union_dst_inr (H : DDG X) (E : List (X × X × ℤ)) (i : Fin E.length) :
    (H.union E).dst (.inr i) = E[i.1].2.1 := rfl
@[simp] lemma DDG.union_len_inr (H : DDG X) (E : List (X × X × ℤ)) (i : Fin E.length) :
    (H.union E).len (.inr i) = E[i.1].2.2 := rfl

/-- **The specification of FR-Dijkstra**: given a dense distance graph `H`, explicit arcs `E`, a
root `r` and a feasible potential `p` of their union (the price function, which makes the
reduced lengths nonnegative), the distances from `r` in the union. -/
def FRSpec (fr : DDG X → List (X × X × ℤ) → X → (X → ℤ) → X → Option ℤ) : Prop :=
  ∀ H E r p, (DDG.union H E).IsPot p → IsDist (DDG.union H E) r (fr H E r p)

/-! ### The decomposition of walks -/

section Decomp

variable {G : Digraph X A} {inH : A → Prop} {L : List A} {B : Finset X} {H : DDG X}

/-- The explicit arcs of `G` listed by `L`, as triples. -/
def explicitArcs (G : Digraph X A) (L : List A) : List (X × X × ℤ) :=
  L.map fun a => (G.src a, G.dst a, G.len a)

lemma length_explicitArcs (G : Digraph X A) (L : List A) :
    (explicitArcs G L).length = L.length := by simp [explicitArcs]

@[simp] lemma explicitArcs_getElem (G : Digraph X A) (L : List A) (k : ℕ)
    (hk : k < (explicitArcs G L).length) :
    (explicitArcs G L)[k] =
      (G.src (L[k]'(by simpa [explicitArcs] using hk)),
        G.dst (L[k]'(by simpa [explicitArcs] using hk)),
        G.len (L[k]'(by simpa [explicitArcs] using hk))) := by
  simp [explicitArcs]

/-- The hypotheses of the decomposition: the arcs not in `H` are listed by `L` and have both ends
in `B`, and `H` is the dense distance graph of `G` restricted to `inH` on `B`. -/
structure DecompHyp (G : Digraph X A) (inH : A → Prop) (L : List A) (B : Finset X) (H : DDG X) :
    Prop where
  mem : ∀ a, a ∈ L ↔ ¬ inH a
  src : ∀ a ∈ L, G.src a ∈ B
  dst : ∀ a ∈ L, G.dst a ∈ B
  bdry : H.bdry = B
  ddg : IsDDGOf (G.restrict inH) H

/-- A walk in `H` between vertices of `B` gives an arc of the dense distance graph, no longer. -/
lemma DecompHyp.arc (hyp : DecompHyp G inH L B H) {x y : X} (hx : x ∈ B) (hy : y ∈ B)
    {h : List {a // inH a}} (hh : IsWalk (G.restrict inH) x h y) :
    ∃ a : H.Arc, a.1 = (x, y) ∧ (H.len x y).getD 0 ≤ wlen (G.restrict inH) h := by
  obtain ⟨δ, hδ, hlen⟩ := hyp.ddg x (hyp.bdry ▸ hx)
  obtain ⟨ℓ, h1, h2⟩ := hδ.exists_le hh
  have e : H.len x y = some ℓ := by rw [hlen y (hyp.bdry ▸ hy), h1]
  exact ⟨⟨(x, y), hyp.bdry ▸ hx, hyp.bdry ▸ hy, by simp [e]⟩, rfl, by simp [e, h2]⟩

/-- **From walks of `G` to walks of the union**: a walk of `G` between vertices of `B`, preceded
by a walk in `H` from a vertex of `B`, gives a walk of the union no longer than both. -/
theorem exists_union_walk (hyp : DecompHyp G inH L B H) :
    ∀ (l : List A) (x z y : X) (h : List {a // inH a}), x ∈ B → y ∈ B →
      IsWalk (G.restrict inH) x h z → IsWalk G z l y →
      ∃ l', IsWalk (H.union (explicitArcs G L)) x l' y ∧
        wlen (H.union (explicitArcs G L)) l' ≤ wlen (G.restrict inH) h + wlen G l := by
  classical
  intro l
  induction l with
  | nil =>
    intro x z y h hx hy hh hl
    simp only [isWalk_nil] at hl; subst hl
    obtain ⟨a, ha, hle⟩ := hyp.arc hx hy hh
    refine ⟨[.inl a], ?_, ?_⟩
    · simp [ha]
    · simp only [wlen_cons, wlen_nil, add_zero, DDG.union_len_inl, ha]; exact hle
  | cons a l ih =>
    intro x z y h hx hy hh hl
    obtain ⟨hsrc, hl⟩ := hl
    by_cases haH : inH a
    · obtain ⟨l', hl', hle⟩ := ih x (G.dst a) y (h ++ [⟨a, haH⟩]) hx hy
        (hh.append ((isWalk_singleton (G := G.restrict inH) (a := ⟨a, haH⟩)).2 ⟨hsrc, rfl⟩)) hl
      refine ⟨l', hl', ?_⟩
      rw [wlen_append] at hle
      simp only [wlen_cons, wlen_nil, add_zero] at hle ⊢
      simpa [Digraph.restrict, add_assoc] using hle
    · have haL : a ∈ L := (hyp.mem a).2 haH
      have hz : z ∈ B := hsrc ▸ hyp.src a haL
      obtain ⟨b, hb, hble⟩ := hyp.arc hx hz hh
      obtain ⟨l', hl', hle⟩ := ih (G.dst a) (G.dst a) y [] (hyp.dst a haL) hy rfl hl
      obtain ⟨i, hi⟩ := List.get_of_mem haL
      have hi' : L[i.1] = a := by simpa using hi
      let j : Fin (explicitArcs G L).length := ⟨i.1, by simp [length_explicitArcs]⟩
      refine ⟨.inl b :: .inr j :: l', ⟨by simp [hb], ?_, ?_⟩, ?_⟩
      · simp only [DDG.union_dst_inl, DDG.union_src_inr, explicitArcs_getElem, hb, j, hi', hsrc]
      · simpa only [DDG.union_dst_inr, explicitArcs_getElem, j, hi'] using hl'
      · simp only [wlen_nil, zero_add] at hle
        have e1 : (H.union (explicitArcs G L)).len (.inl b) = (H.len x z).getD 0 := by simp [hb]
        have e2 : (H.union (explicitArcs G L)).len (.inr j) = G.len a := by
          simp only [DDG.union_len_inr, explicitArcs_getElem, j, hi']
        simp only [wlen_cons, e1, e2]
        linarith

/-- **From walks of the union to walks of `G`**, of the same length. -/
theorem exists_walk_of_union (hyp : DecompHyp G inH L B H) :
    ∀ (l : List (H.Arc ⊕ Fin (explicitArcs G L).length)) (x y : X),
      IsWalk (H.union (explicitArcs G L)) x l y →
      ∃ l', IsWalk G x l' y ∧ wlen G l' = wlen (H.union (explicitArcs G L)) l := by
  intro l
  induction l with
  | nil => intro x y h; exact ⟨[], h, rfl⟩
  | cons a l ih =>
    intro x y h
    obtain ⟨hsrc, hl⟩ := h
    obtain ⟨l₂, hl₂, hlen₂⟩ := ih _ y hl
    match a with
    | .inl p =>
      obtain ⟨hu, hv, hs⟩ := p.2
      simp only [DDG.union_src_inl, DDG.union_dst_inl] at hsrc hl₂
      obtain ⟨δ, hδ, hlen⟩ := hyp.ddg _ hu
      obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.1 hs
      obtain ⟨l₁, hl₁, hlen₁⟩ := hδ.some_walk _ ℓ (by rw [← hlen _ hv, hℓ])
      refine ⟨l₁.map Subtype.val ++ l₂, (hsrc ▸ hl₁.of_restrict).append hl₂, ?_⟩
      rw [wlen_append, ← wlen_restrict, hlen₁, hlen₂, wlen_cons]
      simp [hℓ]
    | .inr i =>
      have hi : i.1 < L.length := by simpa [length_explicitArcs] using i.2
      simp only [DDG.union_src_inr, DDG.union_dst_inr, explicitArcs_getElem] at hsrc hl₂
      refine ⟨L[i.1] :: l₂, ⟨hsrc, hl₂⟩, ?_⟩
      rw [wlen_cons, wlen_cons, hlen₂]; simp only [DDG.union_len_inr, explicitArcs_getElem]

/-- **The distances in the union are the distances in `G`**: for `x, y ∈ B`, the distance from
`x` to `y` in the union of the dense distance graph of `H` on `B` and the explicit arcs is the
distance in `G`. -/
theorem isDist_union (hyp : DecompHyp G inH L B H) {x : X} (hx : x ∈ B) {δ δ' : X → Option ℤ}
    (hδ : IsDist G x δ) (hδ' : IsDist (H.union (explicitArcs G L)) x δ') {y : X} (hy : y ∈ B) :
    δ' y = δ y := by
  cases h : δ y with
  | none =>
    cases h' : δ' y with
    | none => rfl
    | some ℓ' =>
      obtain ⟨l, hl, -⟩ := hδ'.some_walk y ℓ' h'
      obtain ⟨l', hl', -⟩ := exists_walk_of_union hyp l x y hl
      exact absurd hl' (hδ.none y h l')
  | some ℓ =>
    obtain ⟨l, hl, hlen⟩ := hδ.some_walk y ℓ h
    obtain ⟨l', hl', hle⟩ := exists_union_walk hyp l x x y [] hx hy rfl hl
    obtain ⟨ℓ', h', hle'⟩ := hδ'.exists_le hl'
    obtain ⟨l'', hl'', hlen''⟩ := hδ'.some_walk y ℓ' h'
    obtain ⟨m, hm, hmlen⟩ := exists_walk_of_union hyp l'' x y hl''
    have := hδ.some_le y ℓ h m hm
    rw [h']; congr 1
    simp only [wlen_nil, zero_add] at hle
    omega

/-- A feasible potential of `G` is a feasible potential of the union. -/
theorem isPot_union (hyp : DecompHyp G inH L B H) {p : X → ℤ} (hp : G.IsPot p) :
    (H.union (explicitArcs G L)).IsPot p := by
  intro a
  match a with
  | .inl q =>
    obtain ⟨hu, hv, hs⟩ := q.2
    simp only [DDG.union_src_inl, DDG.union_dst_inl, DDG.union_len_inl]
    obtain ⟨δ, hδ, hlen⟩ := hyp.ddg _ hu
    obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨l, hl, hlen'⟩ := hδ.some_walk _ ℓ (by rw [← hlen _ hv, hℓ])
    have := hl.of_restrict.le_wlen hp
    rw [← wlen_restrict, hlen'] at this
    simp only [hℓ, Option.getD_some]; omega
  | .inr i =>
    have hi : i.1 < L.length := by simpa [length_explicitArcs] using i.2
    have := hp L[i.1]
    simpa only [DDG.union_src_inr, DDG.union_dst_inr, DDG.union_len_inr, explicitArcs_getElem]
      using this

end Decomp

end BKMNW

end PlanarFlow
