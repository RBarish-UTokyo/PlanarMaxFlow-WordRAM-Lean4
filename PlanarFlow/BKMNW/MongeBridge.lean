module

public import PlanarFlow.BKMNW.DKPW
public import PlanarFlow.Monge.FRDijkstra

/-!
# The Monge library and the specifications of the algorithm

The Monge library (`PlanarFlow/Monge`) states FR-Dijkstra with indexed walks (`Monge.GWalk`,
`Monge.GDist`) on one dense distance graph given by the vertices `β 0, …, β (b - 1)` of a face and
the lengths `D i j`, together with explicit arcs (`Monge.ddgPlus`, `Monge.FRDijkSpec`). This file
relates them to the list walks and distances and to the union `DDG.union` of the specifications of
the algorithm of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen.

* `isDist_of_arcsIn`: two digraphs on the same vertices, each of whose arcs has a copy in the
  other (same ends, same length), have the same distances.
* `gdist_iff`: on a nonempty type of arcs, `Monge.GDist` is `IsDist` (`Monge.GWalk` is the indexed
  walk `MSSP.IsWalk`).
* `faceDDG β b D`: the dense distance graph on the vertices `β i` with the lengths `D i j`
  (`i ≠ j`); for `β` injective on `0, …, b - 1`, `Monge.ddgPlus β b D Ex` and
  `(faceDDG β b D).union Ex` have the same distances (`isDist_ddgPlus_iff`, `gdist_ddgPlus_iff`)
  and the same feasible potentials (`isPot_ddgPlus_iff`).
* `isDist_of_frDijkSpec`: an implementation meeting `Monge.FRDijkSpec` gives the distances `IsDist`
  in `(faceDDG β b D).union Ex`, the input of FR-Dijkstra in `FRSpec`.

`FRSpec` itself asks for more: an arbitrary dense distance graph (missing arcs, arcs from a vertex
to itself, no order of the vertices), which `Monge.ddgPlus` does not represent.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset

/-! ### Digraphs with the same arcs -/

section Congr

variable {X A B : Type*}

/-- Every arc of `G` has a copy in `G'`: the same ends and the same length. -/
def ArcsIn (G : Digraph X A) (G' : Digraph X B) : Prop :=
  ∀ a, ∃ b, G'.src b = G.src a ∧ G'.dst b = G.dst a ∧ G'.len b = G.len a

variable {G : Digraph X A} {G' : Digraph X B}

lemma ArcsIn.walk (h : ArcsIn G G') {x y : X} {l : List A} (hl : IsWalk G x l y) :
    ∃ l', IsWalk G' x l' y ∧ wlen G' l' = wlen G l := by
  choose f hf using h
  exact ⟨_, (IsWalk.embed (vx := id) (arc := f) (fun a => (hf a).1) (fun a => (hf a).2.1)
    (fun a => (hf a).2.2) hl).1, (IsWalk.embed (vx := id) (arc := f) (fun a => (hf a).1)
    (fun a => (hf a).2.1) (fun a => (hf a).2.2) hl).2⟩

/-- **Digraphs with the same arcs have the same distances.** -/
theorem isDist_of_arcsIn (h₁ : ArcsIn G G') (h₂ : ArcsIn G' G) {r : X} {δ : X → Option ℤ}
    (h : IsDist G r δ) : IsDist G' r δ where
  some_walk y ℓ hy := by
    obtain ⟨l, hl, he⟩ := h.some_walk y ℓ hy
    obtain ⟨l', hl', he'⟩ := h₁.walk hl
    exact ⟨l', hl', he'.trans he⟩
  some_le y ℓ hy l hl := by
    obtain ⟨l', hl', he'⟩ := h₂.walk hl
    rw [← he']; exact h.some_le y ℓ hy l' hl'
  none y hy l hl := by
    obtain ⟨l', hl', -⟩ := h₂.walk hl
    exact h.none y hy l' hl'

/-- Feasible potentials of a digraph are feasible for a digraph whose arcs it contains. -/
lemma isPot_of_arcsIn (h : ArcsIn G G') {p : X → ℤ} (hp : G'.IsPot p) : G.IsPot p := by
  intro a
  obtain ⟨b, h1, h2, h3⟩ := h a
  have := hp b
  rwa [h1, h2, h3] at this

end Congr

/-! ### Indexed distances -/

/-- **The distances of the Monge library are the distances of the specification**, on a nonempty
type of arcs. -/
theorem gdist_iff {X A : Type*} [Nonempty A] {G : Digraph X A} {r : X} {δ : X → Option ℤ} :
    Monge.GDist G r δ ↔ IsDist G r δ := by
  rw [isDist_iff_mssp]
  exact ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2, h.3⟩⟩

/-! ### One dense distance graph and explicit arcs -/

section Face

variable {X : Type*} [DecidableEq X]

open Classical in
/-- The dense distance graph on the vertices `β 0, …, β (b - 1)` with the lengths `D i j` between
distinct indices. -/
noncomputable def faceDDG (β : ℕ → X) (b : ℕ) (D : ℕ → ℕ → ℤ) : DDG X where
  bdry := (range b).image β
  len x y := if h : ∃ p : Monge.Arc b, β p.1.1 = x ∧ β p.1.2 = y then
    some (D h.choose.1.1 h.choose.1.2) else none

variable {β : ℕ → X} {b : ℕ} {D : ℕ → ℕ → ℤ} {Ex : List (X × X × ℤ)}

lemma arcsIn_ddgPlus (hβ : ∀ i < b, ∀ j < b, β i = β j → i = j) :
    ArcsIn (Monge.ddgPlus β b D Ex) ((faceDDG β b D).union Ex) := by
  classical
  rintro (p | e)
  · have hex : ∃ q : Monge.Arc b, β q.1.1 = β p.1.1 ∧ β q.1.2 = β p.1.2 := ⟨p, rfl, rfl⟩
    have hlen : (faceDDG β b D).len (β p.1.1) (β p.1.2) = some (D p.1.1 p.1.2) := by
      simp only [faceDDG, hex, ↓reduceDIte]
      obtain ⟨e1, e2⟩ := hex.choose_spec
      rw [hβ _ hex.choose.1.1.isLt _ p.1.1.isLt e1, hβ _ hex.choose.1.2.isLt _ p.1.2.isLt e2]
    refine ⟨.inl ⟨(β p.1.1, β p.1.2), mem_image.2 ⟨p.1.1, mem_range.2 p.1.1.isLt, rfl⟩,
      mem_image.2 ⟨p.1.2, mem_range.2 p.1.2.isLt, rfl⟩, by rw [hlen]; rfl⟩, rfl, rfl, ?_⟩
    show ((faceDDG β b D).len (β p.1.1) (β p.1.2)).getD 0 = D p.1.1 p.1.2
    rw [hlen]; rfl
  · exact ⟨.inr e, rfl, rfl, rfl⟩

lemma arcsIn_union : ArcsIn ((faceDDG β b D).union Ex) (Monge.ddgPlus β b D Ex) := by
  classical
  rintro (⟨⟨x, y⟩, hx, hy, hs⟩ | e)
  · have hex : ∃ q : Monge.Arc b, β q.1.1 = x ∧ β q.1.2 = y := by
      by_contra hn
      have e : (faceDDG β b D).len x y = none := by
        simp only [faceDDG, hn, ↓reduceDIte]
      change ((faceDDG β b D).len x y).isSome = true at hs
      rw [e] at hs
      exact absurd hs (by decide)
    refine ⟨.inl hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
    show D _ _ = ((faceDDG β b D).len x y).getD 0
    have e : (faceDDG β b D).len x y = some (D hex.choose.1.1 hex.choose.1.2) := by
      simp only [faceDDG, hex, ↓reduceDIte]
    rw [e]; rfl
  · exact ⟨.inr e, rfl, rfl, rfl⟩

/-- **One dense distance graph with explicit arcs, in both libraries, has the same distances**
(for vertices `β i` distinct). -/
theorem isDist_ddgPlus_iff (hβ : ∀ i < b, ∀ j < b, β i = β j → i = j) {r : X}
    {δ : X → Option ℤ} :
    IsDist (Monge.ddgPlus β b D Ex) r δ ↔ IsDist ((faceDDG β b D).union Ex) r δ :=
  ⟨isDist_of_arcsIn (arcsIn_ddgPlus hβ) arcsIn_union,
    isDist_of_arcsIn arcsIn_union (arcsIn_ddgPlus hβ)⟩

/-- The same feasible potentials. -/
theorem isPot_ddgPlus_iff (hβ : ∀ i < b, ∀ j < b, β i = β j → i = j) {p : X → ℤ} :
    (Monge.ddgPlus β b D Ex).IsPot p ↔ ((faceDDG β b D).union Ex).IsPot p :=
  ⟨isPot_of_arcsIn arcsIn_union, isPot_of_arcsIn (arcsIn_ddgPlus hβ)⟩

/-- **The distances of the Monge library in one dense distance graph with explicit arcs are the
distances of the specification in the union.** -/
theorem gdist_ddgPlus_iff (hβ : ∀ i < b, ∀ j < b, β i = β j → i = j)
    [Nonempty (Monge.Arc b ⊕ Fin Ex.length)] {r : X} {δ : X → Option ℤ} :
    Monge.GDist (Monge.ddgPlus β b D Ex) r δ ↔ IsDist ((faceDDG β b D).union Ex) r δ := by
  rw [gdist_iff, isDist_ddgPlus_iff hβ]

/-- **An implementation meeting the specification of FR-Dijkstra of the Monge library gives the
distances of the specification** in the union of one dense distance graph (on distinct vertices)
and explicit arcs. -/
theorem isDist_of_frDijkSpec [Fintype X]
    {fr : (ℕ → X) → (b : ℕ) → (ℕ → ℕ → ℤ) → List (X × X × ℤ) → X → (X → ℤ) → X → Option ℤ}
    (hfr : Monge.FRDijkSpec fr) (hβ : ∀ i < b, ∀ j < b, β i = β j → i = j)
    (hE : Nonempty (Monge.Arc b ⊕ Fin Ex.length)) {r : X} {p : X → ℤ}
    (hp : ((faceDDG β b D).union Ex).IsPot p) :
    IsDist ((faceDDG β b D).union Ex) r (fr β b D Ex r p) :=
  (gdist_ddgPlus_iff hβ).1 (hfr β b D Ex r p hE ((isPot_ddgPlus_iff hβ).2 hp))

end Face

end BKMNW

end PlanarFlow
