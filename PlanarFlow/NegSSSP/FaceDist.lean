module

public import PlanarFlow.NegSSSP.FaceSplit

/-!
# Multiple-source shortest paths in a piece from one face of another map

`PlanarFlow.NegSSSP.OneFace N P B q k` puts the sources `B` of the piece `P` on a face of a plane
map `Q`, into which the darts of `P` reached from `B` embed. This file proves that the distances
in the piece are then read off the distances in the embedded piece of `Q` (Klein's setting,
`PlanarFlow.MSSP.pieceGraph`), from the vertex of the face that represents the source:

* `FaceInst.isDist`: **if `δQ` are the distances in the piece `e '' P'` of `Q` from `j b`, with
  the lengths of `P'` carried over by `e`, then `v ↦ δQ (j v)` on the vertices of `P'` and of `B`
  (and `none` elsewhere) are the distances in the piece `P` of `N` from `b`.** A walk from a source
  stays in `P'` (`FaceInst.closed`) and maps to a walk of `Q` (`walk_to`); a walk of the embedded
  piece of `Q` from `j b` comes back, `j` being injective on the vertices of `P'` and `B`
  (`walk_from`).

So a multiple-source shortest path structure for the face `g` of `Q` (Klein's algorithm,
`PlanarFlow.Klein.klein_exec`) answers the calls of the recursion in the piece `P`
(`PlanarFlow.NegSSSP.PieceMSSPSpec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset BKMNW CombMap

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F} {P : Finset D} {B : Finset V} {q k : ℕ}
  {DQ VQ FQ : Type u} [Fintype DQ] [DecidableEq DQ] [Fintype VQ] [DecidableEq VQ]
  [Fintype FQ] [DecidableEq FQ] {Q : CombMap DQ VQ FQ} {g : ℕ → DQ} {P' : Finset D}
  {e : D → DQ} {j : V → VQ}

namespace FaceInst

variable (h : FaceInst N P B q k Q g P' e j) {ℓ : D → ℤ} {ℓQ : DQ → ℤ}
  (hℓ : ∀ d ∈ P', ℓQ (e d) = ℓ d)

lemma injJ' (h : FaceInst N P B q k Q g P' e j) {a b : V} (ha : a ∈ verts N P' ∪ B)
    (hb : b ∈ verts N P' ∪ B) (hab : j a = j b) : a = b :=
  h.injJ (by simp only [Set.mem_union, mem_coe]; exact mem_union.1 ha)
    (by simp only [Set.mem_union, mem_coe]; exact mem_union.1 hb) hab

include h hℓ in
/-- **A walk of the piece from a vertex of `P'` or of `B` is a walk of the embedded piece of
`Q`**, of the same length, ending at a vertex of `P'` or of `B`. -/
lemma walk_to : ∀ (l : List {d // d ∈ P}) (x y : V), x ∈ verts N P' ∪ B →
    IsWalk (MSSP.pieceGraph N P ℓ) x l y →
    y ∈ verts N P' ∪ B ∧ ∃ lQ : List {x // x ∈ P'.image e},
      IsWalk (MSSP.pieceGraph Q (P'.image e) ℓQ) (j x) lQ (j y) ∧
      wlen (MSSP.pieceGraph Q (P'.image e) ℓQ) lQ = wlen (MSSP.pieceGraph N P ℓ) l
  | [], x, y, hx, hw => by
    rw [isWalk_nil] at hw
    subst hw
    exact ⟨hx, [], rfl, rfl⟩
  | a :: l, x, y, hx, hw => by
    rw [isWalk_cons] at hw
    obtain ⟨hs, hw⟩ := hw
    have ha : a.1 ∈ P' := h.closed a.1 a.2 (by rw [show N.tail a.1 = x from hs]; exact hx)
    have hh : N.head a.1 ∈ verts N P' ∪ B := mem_union_left _ (head_mem_verts ha)
    obtain ⟨hy, lQ, hwQ, hlen⟩ := walk_to l _ y hh hw
    refine ⟨hy, ⟨e a.1, mem_image_of_mem e ha⟩ :: lQ, ?_, ?_⟩
    · rw [isWalk_cons]
      refine ⟨(h.tail a.1 ha).trans (congrArg j hs), ?_⟩
      show IsWalk _ (Q.head (e a.1)) lQ (j y)
      rw [h.head a.1 ha]; exact hwQ
    · simp only [wlen, List.map_cons, List.sum_cons] at hlen ⊢
      rw [hlen]
      exact congrArg (· + _) (hℓ a.1 ha)

include h hℓ in
/-- **A walk of the embedded piece of `Q` from the image of a vertex of `P'` or of `B` comes from
a walk of the piece**, of the same length. -/
lemma walk_from : ∀ (lQ : List {x // x ∈ P'.image e}) (x : V) (y' : VQ),
    x ∈ verts N P' ∪ B → IsWalk (MSSP.pieceGraph Q (P'.image e) ℓQ) (j x) lQ y' →
    ∃ y ∈ verts N P' ∪ B, j y = y' ∧ ∃ l : List {d // d ∈ P},
      IsWalk (MSSP.pieceGraph N P ℓ) x l y ∧
      wlen (MSSP.pieceGraph N P ℓ) l = wlen (MSSP.pieceGraph Q (P'.image e) ℓQ) lQ
  | [], x, y', hx, hw => by
    rw [isWalk_nil] at hw
    exact ⟨x, hx, hw, [], rfl, rfl⟩
  | a :: lQ, x, y', hx, hw => by
    rw [isWalk_cons] at hw
    obtain ⟨hs, hw⟩ := hw
    obtain ⟨d, hd, hde⟩ := mem_image.1 a.2
    have ht : N.tail d = x := h.injJ' (mem_union_left _ (tail_mem_verts hd)) hx
      ((h.tail d hd).symm.trans (hde ▸ hs))
    have hh : N.head d ∈ verts N P' ∪ B := mem_union_left _ (head_mem_verts hd)
    have hw' : IsWalk (MSSP.pieceGraph Q (P'.image e) ℓQ) (j (N.head d)) lQ y' := by
      have : (MSSP.pieceGraph Q (P'.image e) ℓQ).dst a = j (N.head d) := by
        show Q.head a.1 = _
        rw [← hde]; exact h.head d hd
      rwa [this] at hw
    obtain ⟨y, hy, hjy, l, hwl, hlen⟩ := walk_from lQ _ y' hh hw'
    refine ⟨y, hy, hjy, ⟨d, h.sub hd⟩ :: l, ⟨ht, hwl⟩, ?_⟩
    simp only [wlen, List.map_cons, List.sum_cons] at hlen ⊢
    rw [hlen]
    show ℓ d + _ = ℓQ a.1 + _
    rw [← hde, hℓ d hd]

include h hℓ in
/-- **The distances in the piece from a source are those of the embedded piece of `Q` from the
vertex of the face representing it.** -/
theorem isDist {b : V} (hb : b ∈ B) {δQ : VQ → Option ℤ}
    (hδ : IsDist (MSSP.pieceGraph Q (P'.image e) ℓQ) (j b) δQ) :
    IsDist (MSSP.pieceGraph N P ℓ) b
      (fun v => if v ∈ verts N P' ∪ B then δQ (j v) else none) := by
  have hbS : b ∈ verts N P' ∪ B := mem_union_right _ hb
  refine ⟨fun y z hz => ?_, fun y z hz l hl => ?_, fun y hz l hl => ?_⟩
  · by_cases hy : y ∈ verts N P' ∪ B
    · simp only [hy, ↓reduceIte] at hz
      obtain ⟨lQ, hwQ, hlen⟩ := hδ.some_walk _ z hz
      obtain ⟨y₁, hy₁, hj, l, hwl, hlen'⟩ := walk_from h hℓ lQ b _ hbS hwQ
      rw [h.injJ' hy₁ hy hj] at hwl
      exact ⟨l, hwl, hlen'.trans hlen⟩
    · simp only [hy, ↓reduceIte] at hz; exact absurd hz (by simp)
  · obtain ⟨hy, lQ, hwQ, hlen⟩ := walk_to h hℓ l b y hbS hl
    simp only [hy, ↓reduceIte] at hz
    rw [← hlen]
    exact hδ.some_le _ z hz lQ hwQ
  · obtain ⟨hy, lQ, hwQ, -⟩ := walk_to h hℓ l b y hbS hl
    simp only [hy, ↓reduceIte] at hz
    exact hδ.none _ hz lQ hwQ

end FaceInst

end NegSSSP

end PlanarFlow
