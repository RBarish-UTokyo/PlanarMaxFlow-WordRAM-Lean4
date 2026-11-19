module

public import PlanarFlow.NegSSSP.Spec

/-!
# One step of the recursion: from the potentials of two pieces to a potential of their union

A piece is a set `P` of darts of a map `N`, with the digraph `MSSP.pieceGraph N P ℓ` (an arc
from the tail to the head of every dart of `P`). Let `P = P₀ ∪ P₁`, and let `δ₀`, `δ₁` be
feasible potentials of the two pieces (computed recursively). Following Klein, Mozes and Weimann
(ACM Trans. Algorithms 6 (2010), 30) and Mozes and Wulff-Nilsen (ESA 2010, the article,
Section 3), `step` computes a feasible potential of `P`, or reports that there is none:

1. the boundary `B = bdry N P₀ P₁`, the vertices of both pieces;
2. in each piece, **multiple-source shortest paths** (`PieceMSSPSpec`) from `B` with the reduced
   lengths `ℓ d + δᵢ (tail d) - δᵢ (head d)`, which are nonnegative, and the dense distance graph
   `Hᵢ` of the piece on `B` (`childDDG`), the distances shifted back by `δᵢ`;
3. **Bellman–Ford over the union of the dense distance graphs** (`BFDDGSpec`): a feasible
   potential `E` of the union, or `none`, and then the union of the pieces has no feasible
   potential either (`isPot_join`); `E` is lowered by a constant so that it lies below `δ₀`
   and `δ₁` on `B`;
4. in each piece, **Dijkstra with a price function** (FR-Dijkstra on an empty dense distance
   graph, `FRSpec`) from a virtual root (`none` in `Option V`) with an arc of length `E b` to
   every boundary vertex and of length `δᵢ v` to every other vertex of the piece; the price
   function is `δᵢ`, and at the root the sum `∑ |δᵢ b - E b|`;
5. at every vertex, the least of the two distances.

`step_potOut`: **the result is a feasible potential of the union, or `none` and the union has no
feasible potential.** The key facts: on `B` both runs of Dijkstra return `E`
(`dijk_bdry`: a walk from the root enters the piece at a vertex `v` and then stays in the piece;
if `v ∈ B` the dense distance graph bounds it below by `E`, otherwise `δᵢ` does), and a vertex
reached by the run in the other piece is a boundary vertex (`dijk_mem`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset BKMNW CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable (N : CombMap D V F)

/-! ### The objects of a step -/

/-- The vertices of a piece: the tails and the heads of its darts. -/
def verts (P : Finset D) : Finset V := P.image N.tail ∪ P.image N.head

/-- The boundary of two pieces: the vertices of both. -/
def bdry (P₀ P₁ : Finset D) : Finset V := verts N P₀ ∩ verts N P₁

/-- The lengths reduced by a potential `δ`. -/
def redLen (ℓ : D → ℤ) (δ : V → ℤ) (d : D) : ℤ := ℓ d + (δ (N.tail d) - δ (N.head d))

/-- **The dense distance graph of a piece on `B`**, from multiple-source shortest paths with the
reduced lengths, shifted back by `δ`. -/
def childDDG (mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ) (P : Finset D)
    (ℓ : D → ℤ) (δ : V → ℤ) (B : Finset V) : DDG V :=
  ⟨B, fun b b' => (mssp P (redLen N ℓ δ) B b b').map (· + (δ b' - δ b))⟩

/-- The length of the arc from the virtual root to `v`: `E v` on the boundary, `δ v` elsewhere. -/
def initLen (B : Finset V) (E δ : V → ℤ) (v : V) : ℤ := if v ∈ B then E v else δ v

/-- **The explicit arcs of Dijkstra in a piece**: the darts of the piece, and an arc from the
virtual root `none` to every vertex of `W`. -/
noncomputable def dijArcs (P : Finset D) (ℓ : D → ℤ) (W : Finset V) (init : V → ℤ) :
    List (Option V × Option V × ℤ) :=
  P.toList.map (fun d => (some (N.tail d), some (N.head d), ℓ d)) ++
    W.toList.map fun v => (none, some v, init v)

/-- The price function: `δ` on the vertices, and at the root a bound on `δ b - E b`. -/
def price (B : Finset V) (E δ : V → ℤ) : Option V → ℤ
  | none => ∑ b ∈ B, |δ b - E b|
  | some v => δ v

/-- **Dijkstra with a price function in a piece** from the virtual root, by FR-Dijkstra on an
empty dense distance graph. -/
noncomputable def dijk (fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V →
    (Option V → ℤ) → Option V → Option ℤ) (P : Finset D) (ℓ : D → ℤ) (B : Finset V)
    (E δ : V → ℤ) : Option V → Option ℤ :=
  fr emptyDDG (dijArcs N P ℓ (verts N P) (initLen B E δ)) none (price B E δ)

/-- The least of two optional values. -/
def omin : Option ℤ → Option ℤ → Option ℤ
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, o => o

lemma omin_comm (o o' : Option ℤ) : omin o o' = omin o' o := by
  cases o <;> cases o' <;> simp [omin, min_comm]

lemma omin_le {o : Option ℤ} {x : ℤ} (o' : Option ℤ) (h : o = some x) :
    (omin o o').getD 0 ≤ x := by
  subst h; cases o' <;> simp [omin]

lemma omin_eq {o' : Option ℤ} {x : ℤ} (h : ∀ y, o' = some y → x ≤ y) :
    (omin (some x) o').getD 0 = x := by
  cases o' with
  | none => rfl
  | some y => simp [omin, h y rfl]

/-- **One step of the recursion** (steps 1–5 above). -/
noncomputable def step (mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ)
    (bf : DDG V → DDG V → Option (V → ℤ))
    (fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V → (Option V → ℤ) →
      Option V → Option ℤ)
    (P₀ P₁ : Finset D) (ℓ : D → ℤ) (δ₀ δ₁ : V → ℤ) : Option (V → ℤ) :=
  match bf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) with
  | none => none
  | some E =>
    let C := ∑ b ∈ bdry N P₀ P₁, (|E b - δ₀ b| + |E b - δ₁ b|)
    some fun v => (omin (dijk N fr P₀ ℓ (bdry N P₀ P₁) (fun x => E x - C) δ₀ (some v))
      (dijk N fr P₁ ℓ (bdry N P₀ P₁) (fun x => E x - C) δ₁ (some v))).getD 0

variable {N}

/-! ### Pieces -/

/-- The digraph of a piece. -/
abbrev pg (N : CombMap D V F) (P : Finset D) (ℓ : D → ℤ) : Digraph V {d // d ∈ P} :=
  MSSP.pieceGraph N P ℓ

lemma isPot_mono {P P' : Finset D} (h : P ⊆ P') {ℓ : D → ℤ} {p : V → ℤ}
    (hp : (pg N P' ℓ).IsPot p) : (pg N P ℓ).IsPot p :=
  fun a => hp ⟨a.1, h a.2⟩

lemma not_pot_mono {P P' : Finset D} (h : P ⊆ P') {ℓ : D → ℤ}
    (hp : ¬ ∃ p, (pg N P ℓ).IsPot p) : ¬ ∃ p, (pg N P' ℓ).IsPot p :=
  fun ⟨p, hp'⟩ => hp ⟨p, isPot_mono h hp'⟩

lemma tail_mem_verts {P : Finset D} {d : D} (hd : d ∈ P) : N.tail d ∈ verts N P :=
  mem_union_left _ (mem_image_of_mem _ hd)

lemma head_mem_verts {P : Finset D} {d : D} (hd : d ∈ P) : N.head d ∈ verts N P :=
  mem_union_right _ (mem_image_of_mem _ hd)

/-- A walk of a piece from a vertex of the piece ends at a vertex of the piece. -/
lemma walk_mem_verts {P : Finset D} {ℓ : D → ℤ} :
    ∀ {l : List {d // d ∈ P}} {x y : V}, IsWalk (pg N P ℓ) x l y → x ∈ verts N P →
      y ∈ verts N P
  | [], _, _, h, hx => by simp only [isWalk_nil] at h; exact h ▸ hx
  | a :: _, _, _, h, _ => walk_mem_verts h.2 (head_mem_verts a.2)

/-! ### The dense distance graphs -/

/-- The reduced lengths are nonnegative on a piece with a feasible potential. -/
lemma redLen_nonneg {P : Finset D} {ℓ : D → ℤ} {δ : V → ℤ} (hδ : (pg N P ℓ).IsPot δ) :
    ∀ d ∈ P, 0 ≤ redLen N ℓ δ d := fun d hd => by
  have : δ (N.head d) ≤ δ (N.tail d) + ℓ d := hδ ⟨d, hd⟩
  unfold redLen; linarith

lemma addPot_redLen (P : Finset D) (ℓ : D → ℤ) (δ : V → ℤ) :
    (pg N P (redLen N ℓ δ)).addPot δ = pg N P ℓ := by
  simp only [Digraph.addPot, MSSP.pieceGraph, redLen]
  congr 1; funext a; ring

/-- **The dense distance graph of a piece** (`IsDDGOf`), from multiple-source shortest paths
with the reduced lengths. -/
theorem isDDGOf_child {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}
    (hmssp : PieceMSSPSpec N mssp) {P : Finset D} {ℓ : D → ℤ} {δ : V → ℤ}
    (hδ : (pg N P ℓ).IsPot δ) (B : Finset V) : IsDDGOf (pg N P ℓ) (childDDG N mssp P ℓ δ B) := by
  intro b hb
  have h := isDist_addPot (p := δ) (hmssp P (redLen N ℓ δ) B (redLen_nonneg hδ) b hb)
  rw [addPot_redLen] at h
  exact ⟨_, h, fun _ _ => rfl⟩

/-- An arc of a dense distance graph is no shorter than the walks of the digraph between its
ends. -/
lemma ddg_arc_le {X A : Type*} {G : Digraph X A} {H : DDG X} (hH : IsDDGOf G H) {x y : X}
    (hx : x ∈ H.bdry) (hy : y ∈ H.bdry) {l : List A} (hl : IsWalk G x l y) :
    ∃ a : H.Arc, a.1 = (x, y) ∧ (H.len x y).getD 0 ≤ wlen G l := by
  obtain ⟨δ, hδ, hlen⟩ := hH x hx
  obtain ⟨ℓ, h1, h2⟩ := hδ.exists_le hl
  have e : H.len x y = some ℓ := by rw [hlen y hy, h1]
  exact ⟨⟨(x, y), hx, hy, by simp [e]⟩, rfl, by simp [e, h2]⟩

/-- An arc of a dense distance graph is the length of a walk of the digraph. -/
lemma ddg_arc_walk {X A : Type*} {G : Digraph X A} {H : DDG X} (hH : IsDDGOf G H) (a : H.Arc) :
    ∃ l, IsWalk G a.1.1 l a.1.2 ∧ wlen G l = (H.len a.1.1 a.1.2).getD 0 := by
  obtain ⟨hu, hv, hs⟩ := a.2
  obtain ⟨δ, hδ, hlen⟩ := hH _ hu
  obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨l, hl, hlen'⟩ := hδ.some_walk _ ℓ (by rw [← hlen _ hv, hℓ])
  exact ⟨l, hl, by rw [hlen', hℓ]; rfl⟩

/-- **A feasible potential of the union of the pieces is feasible for the union of their dense
distance graphs.** -/
theorem isPot_join {P₀ P₁ : Finset D} {ℓ : D → ℤ} {H₀ H₁ : DDG V}
    (h₀ : IsDDGOf (pg N P₀ ℓ) H₀) (h₁ : IsDDGOf (pg N P₁ ℓ) H₁) {p : V → ℤ}
    (hp : (pg N (P₀ ∪ P₁) ℓ).IsPot p) : (H₀.join H₁).IsPot p := by
  rintro (a | a)
  · obtain ⟨l, hl, he⟩ := ddg_arc_walk h₀ a
    have := hl.le_wlen (isPot_mono subset_union_left hp)
    simp only [DDG.join, Sum.elim_inl]; omega
  · obtain ⟨l, hl, he⟩ := ddg_arc_walk h₁ a
    have := hl.le_wlen (isPot_mono subset_union_right hp)
    simp only [DDG.join, Sum.elim_inr]; omega

/-- A feasible potential of the union bounds the walks of the first piece between boundary
vertices. -/
lemma join_le_left {H₀ H₁ : DDG V} {E : V → ℤ} (hE : (H₀.join H₁).IsPot E) {A : Type*}
    {G : Digraph V A} (hH : IsDDGOf G H₀) {x y : V} (hx : x ∈ H₀.bdry) (hy : y ∈ H₀.bdry)
    {l : List A} (hl : IsWalk G x l y) : E y ≤ E x + wlen G l := by
  obtain ⟨a, ha, hle⟩ := ddg_arc_le hH hx hy hl
  have := hE (.inl a)
  simp only [DDG.join, Sum.elim_inl, ha] at this
  omega

lemma join_le_right {H₀ H₁ : DDG V} {E : V → ℤ} (hE : (H₀.join H₁).IsPot E) {A : Type*}
    {G : Digraph V A} (hH : IsDDGOf G H₁) {x y : V} (hx : x ∈ H₁.bdry) (hy : y ∈ H₁.bdry)
    {l : List A} (hl : IsWalk G x l y) : E y ≤ E x + wlen G l := by
  obtain ⟨a, ha, hle⟩ := ddg_arc_le hH hx hy hl
  have := hE (.inr a)
  simp only [DDG.join, Sum.elim_inr, ha] at this
  omega

/-! ### Dijkstra from the virtual root -/

section Dijk

variable {P : Finset D} {ℓ : D → ℤ} {W : Finset V} {init : V → ℤ}

/-- The digraph of Dijkstra in a piece. -/
noncomputable abbrev dg (N : CombMap D V F) (P : Finset D) (ℓ : D → ℤ) (W : Finset V) (init : V → ℤ) :=
  (emptyDDG (F := Option V)).union (dijArcs N P ℓ W init)

lemma mem_dijArcs {t : Option V × Option V × ℤ} :
    t ∈ dijArcs N P ℓ W init ↔ (∃ d ∈ P, (some (N.tail d), some (N.head d), ℓ d) = t) ∨
      ∃ v ∈ W, (none, some v, init v) = t := by
  simp [dijArcs]

/-- The arcs of the digraph of Dijkstra: the darts of the piece and the arcs from the root. -/
lemma dg_arc (a : (emptyDDG (F := Option V)).Arc ⊕ Fin (dijArcs N P ℓ W init).length) :
    (∃ d ∈ P, (dg N P ℓ W init).src a = some (N.tail d) ∧
      (dg N P ℓ W init).dst a = some (N.head d) ∧ (dg N P ℓ W init).len a = ℓ d) ∨
    ∃ v ∈ W, (dg N P ℓ W init).src a = none ∧ (dg N P ℓ W init).dst a = some v ∧
      (dg N P ℓ W init).len a = init v := by
  rcases a with ⟨p, hp, -⟩ | i
  · simp [emptyDDG] at hp
  · have hm : (dijArcs N P ℓ W init)[i.1] ∈ dijArcs N P ℓ W init := List.getElem_mem _
    simp only [DDG.union_src_inr, DDG.union_dst_inr, DDG.union_len_inr]
    rcases mem_dijArcs.1 hm with ⟨d, hd, e⟩ | ⟨v, hv, e⟩
    · exact Or.inl ⟨d, hd, by rw [← e], by rw [← e], by rw [← e]⟩
    · exact Or.inr ⟨v, hv, by rw [← e], by rw [← e], by rw [← e]⟩

lemma dg_arc_of_mem {t : Option V × Option V × ℤ} (ht : t ∈ dijArcs N P ℓ W init) :
    ∃ a, (dg N P ℓ W init).src a = t.1 ∧ (dg N P ℓ W init).dst a = t.2.1 ∧
      (dg N P ℓ W init).len a = t.2.2 := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 ht
  exact ⟨.inr ⟨i, hi⟩, by simp [e], by simp [e], by simp [e]⟩

lemma dg_arc_dart {d : D} (hd : d ∈ P) :
    ∃ a, (dg N P ℓ W init).src a = some (N.tail d) ∧
      (dg N P ℓ W init).dst a = some (N.head d) ∧ (dg N P ℓ W init).len a = ℓ d :=
  dg_arc_of_mem (mem_dijArcs.2 (Or.inl ⟨d, hd, rfl⟩))

lemma dg_arc_root {v : V} (hv : v ∈ W) :
    ∃ a, (dg N P ℓ W init).src a = none ∧ (dg N P ℓ W init).dst a = some v ∧
      (dg N P ℓ W init).len a = init v :=
  dg_arc_of_mem (mem_dijArcs.2 (Or.inr ⟨v, hv, rfl⟩))

/-- **A walk from a vertex stays in the piece.** -/
lemma dg_walk_some : ∀ (l : List ((emptyDDG (F := Option V)).Arc ⊕
      Fin (dijArcs N P ℓ W init).length)) (v : V) (y : Option V),
    IsWalk (dg N P ℓ W init) (some v) l y → ∃ y', y = some y' ∧
      ∃ l' : List {d // d ∈ P}, IsWalk (pg N P ℓ) v l' y' ∧
        wlen (pg N P ℓ) l' = wlen (dg N P ℓ W init) l
  | [], v, y, h => ⟨v, by simp only [isWalk_nil] at h; exact h.symm, [], rfl, rfl⟩
  | a :: l, v, y, h => by
    obtain ⟨hs, hl⟩ := h
    rcases dg_arc a with ⟨d, hd, h1, h2, h3⟩ | ⟨w, -, h1, -, -⟩
    · rw [h1, Option.some_inj] at hs
      rw [h2] at hl
      obtain ⟨y', rfl, l', hl', he⟩ := dg_walk_some l _ y hl
      refine ⟨y', rfl, ⟨d, hd⟩ :: l', ⟨hs, hl'⟩, ?_⟩
      rw [wlen_cons, wlen_cons, he, h3]; rfl
    · rw [h1] at hs; exact absurd hs (by simp)

/-- **A walk from the root** enters the piece by an arc from the root and stays in the piece. -/
lemma dg_walk_none {l : List ((emptyDDG (F := Option V)).Arc ⊕
      Fin (dijArcs N P ℓ W init).length)} {y : V}
    (h : IsWalk (dg N P ℓ W init) none l (some y)) :
    ∃ v ∈ W, ∃ l' : List {d // d ∈ P}, IsWalk (pg N P ℓ) v l' y ∧
      wlen (dg N P ℓ W init) l = init v + wlen (pg N P ℓ) l' := by
  rcases l with _ | ⟨a, l⟩
  · simp at h
  · obtain ⟨hs, hl⟩ := h
    rcases dg_arc a with ⟨d, -, h1, -, -⟩ | ⟨v, hv, -, h2, h3⟩
    · rw [h1] at hs; exact absurd hs (by simp)
    · rw [h2] at hl
      obtain ⟨y', hy', l', hl', he⟩ := dg_walk_some l v _ hl
      rw [Option.some_inj] at hy'
      subst hy'
      exact ⟨v, hv, l', hl', by rw [wlen_cons, h3, he]⟩

end Dijk

/-! ### Correctness of a step -/

section Correct

variable {fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V → (Option V → ℤ) →
  Option V → Option ℤ}
variable {P : Finset D} {ℓ : D → ℤ} {B : Finset V} {E δ : V → ℤ}

/-- The price function is feasible when `δ` is a feasible potential of the piece and `E ≤ δ` on
the boundary. -/
lemma isPot_price (hδ : (pg N P ℓ).IsPot δ) :
    (dg N P ℓ (verts N P) (initLen B E δ)).IsPot (price B E δ) := by
  intro a
  rcases dg_arc a with ⟨d, hd, h1, h2, h3⟩ | ⟨v, -, h1, h2, h3⟩
  · rw [h1, h2, h3]
    exact hδ ⟨d, hd⟩
  · rw [h1, h2, h3]
    simp only [price, initLen]
    have h0 : 0 ≤ ∑ b ∈ B, |δ b - E b| := sum_nonneg fun _ _ => abs_nonneg _
    split_ifs with hv
    · have h1 : |δ v - E v| ≤ ∑ b ∈ B, |δ b - E b| :=
        single_le_sum (f := fun b => |δ b - E b|) (fun _ _ => abs_nonneg _) hv
      have := le_abs_self (δ v - E v)
      linarith
    · linarith

lemma isDist_dijk (hfr : FRSpec fr) (hδ : (pg N P ℓ).IsPot δ) :
    IsDist (dg N P ℓ (verts N P) (initLen B E δ)) none (dijk N fr P ℓ B E δ) :=
  hfr _ _ none _ (isPot_price hδ)

/-- Every vertex of the piece is reached, within its arc from the root. -/
lemma dijk_some (hfr : FRSpec fr) (hδ : (pg N P ℓ).IsPot δ) {v : V} (hv : v ∈ verts N P) :
    ∃ x, dijk N fr P ℓ B E δ (some v) = some x ∧ x ≤ initLen B E δ v := by
  obtain ⟨a, h1, h2, h3⟩ := dg_arc_root (N := N) (P := P) (ℓ := ℓ) (init := initLen B E δ) hv
  obtain ⟨x, hx, hle⟩ := (isDist_dijk (B := B) (E := E) hfr hδ).exists_le
    (l := [a]) (isWalk_singleton.2 ⟨h1, h2⟩)
  exact ⟨x, hx, by simpa [wlen, h3] using hle⟩

/-- **Only the vertices of the piece are reached.** -/
lemma dijk_mem (hfr : FRSpec fr) (hδ : (pg N P ℓ).IsPot δ) {y : V} {x : ℤ}
    (h : dijk N fr P ℓ B E δ (some y) = some x) : y ∈ verts N P := by
  obtain ⟨l, hl, -⟩ := (isDist_dijk hfr hδ).some_walk _ x h
  obtain ⟨v, hv, l', hl', -⟩ := dg_walk_none hl
  exact walk_mem_verts hl' hv

/-- The triangle inequality along a dart of the piece. -/
lemma dijk_arc (hfr : FRSpec fr) (hδ : (pg N P ℓ).IsPot δ) {d : D} (hd : d ∈ P) {x : ℤ}
    (h : dijk N fr P ℓ B E δ (some (N.tail d)) = some x) :
    ∃ x', dijk N fr P ℓ B E δ (some (N.head d)) = some x' ∧ x' ≤ x + ℓ d := by
  obtain ⟨a, h1, h2, h3⟩ := dg_arc_dart (N := N) (ℓ := ℓ) (W := verts N P)
    (init := initLen B E δ) hd
  have := (isDist_dijk hfr hδ).le_arc (a := a) (by rw [h1]; exact h)
  rwa [h2, h3] at this

/-- **On the boundary, Dijkstra returns `E`**: the arc from the root gives `E b`, and a walk from
the root enters the piece at a vertex `v` and then stays in the piece, so its length is at least
`E b`, by the dense distance graph if `v ∈ B` and by `δ` otherwise. -/
lemma dijk_bdry (hfr : FRSpec fr) (hδ : (pg N P ℓ).IsPot δ) (hB : B ⊆ verts N P)
    (hEδ : ∀ b ∈ B, E b ≤ δ b)
    (hEP : ∀ x ∈ B, ∀ y ∈ B, ∀ l, IsWalk (pg N P ℓ) x l y → E y ≤ E x + wlen (pg N P ℓ) l)
    {b : V} (hb : b ∈ B) : dijk N fr P ℓ B E δ (some b) = some (E b) := by
  obtain ⟨x, hx, hle⟩ := dijk_some (B := B) (E := E) hfr hδ (hB hb)
  simp only [initLen, hb, ↓reduceIte] at hle
  rw [hx]; congr 1
  refine le_antisymm hle ?_
  obtain ⟨l, hl, rfl⟩ := (isDist_dijk hfr hδ).some_walk _ x hx
  obtain ⟨v, -, l', hl', he⟩ := dg_walk_none hl
  rw [he]
  unfold initLen
  by_cases hvB : v ∈ B
  · have := hEP v hvB b hb l' hl'
    simp only [hvB, ↓reduceIte]; linarith
  · have := hl'.le_wlen hδ
    have := hEδ b hb
    simp only [hvB, ↓reduceIte]; linarith

/-- **Correctness of a step**: from feasible potentials of the two pieces, a feasible potential
of their union, or `none` and the union has no feasible potential. -/
theorem step_potOut {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}
    (hmssp : PieceMSSPSpec N mssp) {bf : DDG V → DDG V → Option (V → ℤ)} (hbf : BFDDGSpec bf)
    (hfr : FRSpec fr) {P₀ P₁ : Finset D} {δ₀ δ₁ : V → ℤ} (h₀ : (pg N P₀ ℓ).IsPot δ₀)
    (h₁ : (pg N P₁ ℓ).IsPot δ₁) :
    PotOut (pg N (P₀ ∪ P₁) ℓ) (step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁) := by
  generalize hB : bdry N P₀ P₁ = B
  have hD₀ := isDDGOf_child hmssp h₀ B
  have hD₁ := isDDGOf_child hmssp h₁ B
  have hbfo := hbf (childDDG N mssp P₀ ℓ δ₀ B) (childDDG N mssp P₁ ℓ δ₁ B)
  unfold step
  rw [hB]
  rcases hE : bf (childDDG N mssp P₀ ℓ δ₀ B) (childDDG N mssp P₁ ℓ δ₁ B) with _ | E
  · rw [hE] at hbfo
    exact fun ⟨p, hp⟩ => hbfo ⟨p, isPot_join hD₀ hD₁ hp⟩
  rw [hE] at hbfo
  simp only
  generalize hC : ∑ b ∈ B, (|E b - δ₀ b| + |E b - δ₁ b|) = C
  generalize hE' : (fun x => E x - C) = E'
  have hB₀ : B ⊆ verts N P₀ := hB ▸ inter_subset_left
  have hB₁ : B ⊆ verts N P₁ := hB ▸ inter_subset_right
  -- the lowered potential of the union of the dense distance graphs
  have hE'pot : (DDG.join (childDDG N mssp P₀ ℓ δ₀ B) (childDDG N mssp P₁ ℓ δ₁ B)).IsPot E' := by
    intro a; have := hbfo a; rw [← hE']; simp only; linarith
  have hle : ∀ b ∈ B, E' b ≤ δ₀ b ∧ E' b ≤ δ₁ b := by
    intro b hb
    have := single_le_sum (f := fun b => |E b - δ₀ b| + |E b - δ₁ b|)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hb
    have := le_abs_self (E b - δ₀ b)
    have := le_abs_self (E b - δ₁ b)
    have := abs_nonneg (E b - δ₀ b)
    have := abs_nonneg (E b - δ₁ b)
    rw [← hE']; simp only at this ⊢; constructor <;> linarith
  have hEP₀ : ∀ x ∈ B, ∀ y ∈ B, ∀ l, IsWalk (pg N P₀ ℓ) x l y →
      E' y ≤ E' x + wlen (pg N P₀ ℓ) l :=
    fun x hx y hy l hl => join_le_left hE'pot hD₀ hx hy hl
  have hEP₁ : ∀ x ∈ B, ∀ y ∈ B, ∀ l, IsWalk (pg N P₁ ℓ) x l y →
      E' y ≤ E' x + wlen (pg N P₁ ℓ) l :=
    fun x hx y hy l hl => join_le_right hE'pot hD₁ hx hy hl
  have hb₀ := fun b hb => dijk_bdry (N := N) (fr := fr) (ℓ := ℓ) hfr h₀ hB₀
    (fun b hb => (hle b hb).1) hEP₀ (b := b) hb
  have hb₁ := fun b hb => dijk_bdry (N := N) (fr := fr) (ℓ := ℓ) hfr h₁ hB₁
    (fun b hb => (hle b hb).2) hEP₁ (b := b) hb
  -- a vertex of a piece reached in the other piece is a boundary vertex, where both agree
  have hcomp : ∀ {Pi Pj : Finset D} {δi δj : V → ℤ}, (pg N Pi ℓ).IsPot δi →
      (pg N Pj ℓ).IsPot δj → (∀ b ∈ B, dijk N fr Pi ℓ B E' δi (some b) = some (E' b)) →
      (∀ b ∈ B, dijk N fr Pj ℓ B E' δj (some b) = some (E' b)) →
      (∀ u, u ∈ verts N Pi → u ∈ verts N Pj → u ∈ B) → ∀ d ∈ Pi,
      (omin (dijk N fr Pi ℓ B E' δi (some (N.head d))) (dijk N fr Pj ℓ B E' δj
        (some (N.head d)))).getD 0 ≤ (omin (dijk N fr Pi ℓ B E' δi (some (N.tail d)))
        (dijk N fr Pj ℓ B E' δj (some (N.tail d)))).getD 0 + ℓ d := by
    intro Pi Pj δi δj hi hj hbi hbj hmem d hd
    obtain ⟨x, hx, -⟩ := dijk_some (B := B) (E := E') hfr hi (tail_mem_verts hd)
    obtain ⟨x', hx', hle'⟩ := dijk_arc hfr hi hd hx
    have h1 := omin_le (dijk N fr Pj ℓ B E' δj (some (N.head d))) hx'
    rw [hx, omin_eq]
    · linarith
    · intro y hy
      have hu := hmem _ (tail_mem_verts hd) (dijk_mem hfr hj hy)
      rw [hbi _ hu, Option.some_inj] at hx
      rw [hbj _ hu, Option.some_inj] at hy
      omega
  rintro ⟨d, hd⟩
  show (omin _ _).getD 0 ≤ (omin _ _).getD 0 + ℓ d
  rcases mem_union.1 hd with hd | hd
  · exact hcomp h₀ h₁ hb₀ hb₁ (fun u h h' => hB ▸ mem_inter.2 ⟨h, h'⟩) d hd
  · rw [omin_comm, omin_comm (dijk N fr P₀ ℓ B E' δ₀ _)]
    exact hcomp h₁ h₀ hb₁ hb₀ (fun u h h' => hB ▸ mem_inter.2 ⟨h', h⟩) d hd

end Correct

end NegSSSP

end PlanarFlow
