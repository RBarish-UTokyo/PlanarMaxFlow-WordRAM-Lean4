module

public import PlanarFlow.Plane.NegCycle

/-!
# Walks, distances and pieces for multiple-source shortest paths

The objects in which the multiple-source shortest path algorithm of Das, Kipouridis, Probst
Gutenberg and Wulff-Nilsen (SOSA 2022) is specified, kept here so that this library does not
depend on the algorithm in which it is used.

* `IsWalk G x y m c`: the arcs `c 0, …, c (m - 1)` form a walk from `x` to `y` (the indexed
  form; the list form `PlanarFlow.MSSP.LWalk` is in `PlanarFlow/MSSP/Walk.lean`).
* `IsDist G r δ`: `δ y = some ℓ` when `ℓ` is the least length of a walk from `r` to `y`,
  `δ y = none` when there is no such walk.
* `MSSPOut G B δ`: the distances from every vertex of `B`.
* `DDG`, `IsDDGOf`: a dense distance graph on boundary vertices, and the condition that its
  lengths are the distances of a digraph between them.
* `pieceGraph M P ℓ`: a set `P` of darts of a map, as a digraph on the vertices; `OnFace`,
  `MSSPSpec`: the specification of multiple-source shortest paths in a piece from vertices on one
  face (Klein).

The list walks and distances of `PlanarFlow/BKMNW/Dist.lean` are the same notions: see
`PlanarFlow/BKMNW/DKPW.lean`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace MSSP

open Finset CombMap

section ShortestPaths

variable {X A : Type*}

/-- A walk of `m` arcs `c 0, …, c (m - 1)` from `x` to `y` (for `m = 0`, the empty walk at
`x = y`). -/
def IsWalk (G : Digraph X A) (x y : X) (m : ℕ) (c : ℕ → A) : Prop :=
  (m = 0 ∧ x = y) ∨ (0 < m ∧ G.src (c 0) = x ∧ G.dst (c (m - 1)) = y ∧
    ∀ t, t + 1 < m → G.dst (c t) = G.src (c (t + 1)))

/-- **Shortest-path distances** from `r` (indexed walks): `δ y = some ℓ` when `ℓ` is the least
length of a walk from `r` to `y`, `δ y = none` when there is no walk from `r` to `y`. -/
structure IsDist (G : Digraph X A) (r : X) (δ : X → Option ℤ) : Prop where
  some_walk : ∀ y ℓ, δ y = some ℓ → ∃ m c, IsWalk G r y m c ∧ G.walkLen m c = ℓ
  some_le : ∀ y ℓ, δ y = some ℓ → ∀ m c, IsWalk G r y m c → ℓ ≤ G.walkLen m c
  none : ∀ y, δ y = none → ∀ m c, ¬ IsWalk G r y m c

/-- Distances are unique. -/
theorem IsDist.unique {G : Digraph X A} {r : X} {δ δ' : X → Option ℤ} (h : IsDist G r δ)
    (h' : IsDist G r δ') : δ = δ' := by
  funext y
  cases hy : δ y with
  | none =>
    cases hy' : δ' y with
    | none => rfl
    | some ℓ' =>
      obtain ⟨m, c, hw, -⟩ := h'.some_walk y ℓ' hy'
      exact absurd hw (h.none y hy m c)
  | some ℓ =>
    obtain ⟨m, c, hw, hl⟩ := h.some_walk y ℓ hy
    cases hy' : δ' y with
    | none => exact absurd hw (h'.none y hy' m c)
    | some ℓ' =>
      obtain ⟨m', c', hw', hl'⟩ := h'.some_walk y ℓ' hy'
      have h1 := h.some_le y ℓ hy m' c' hw'
      have h2 := h'.some_le y ℓ' hy' m c hw
      congr 1; omega

/-- **The output of multiple-source shortest paths**: the distances from every vertex of `B`. -/
def MSSPOut (G : Digraph X A) (B : Finset X) (δ : X → X → Option ℤ) : Prop :=
  ∀ b ∈ B, IsDist G b (δ b)

/-- A dense distance graph on the boundary vertices `bdry`: a length (or `none`, no arc) for
every ordered pair of them. -/
structure DDG (X : Type*) where
  /-- The boundary vertices. -/
  bdry : Finset X
  /-- The lengths. -/
  len : X → X → Option ℤ

/-- `H` is **the dense distance graph of `G` on its boundary**: its lengths are the distances in
`G` between the boundary vertices. -/
def IsDDGOf (G : Digraph X A) (H : DDG X) : Prop :=
  ∀ b ∈ H.bdry, ∃ δ, IsDist G b δ ∧ ∀ b' ∈ H.bdry, H.len b b' = δ b'

end ShortestPaths

/-! ### Pieces of a plane map as digraphs -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- A piece `P` of the map `M` with lengths `ℓ`, as a digraph on the vertices: the darts of `P`
are its arcs. -/
def pieceGraph (M : CombMap D V F) (P : Finset D) (ℓ : D → ℤ) : Digraph V {d // d ∈ P} where
  src d := M.tail d.1
  dst d := M.head d.1
  len d := ℓ d.1

/-- The vertices `B` all lie on the boundary of the face `φ`. -/
def OnFace (M : CombMap D V F) (φ : F) (B : Finset V) : Prop :=
  ∀ b ∈ B, ∃ d, M.face d = φ ∧ M.tail d = b

/-- **The specification of MSSP in a piece** (Klein): for a piece with nonnegative lengths and
vertices `B` on one face, the distances in the piece from every vertex of `B`. -/
def MSSPSpec (M : CombMap D V F) (mssp : Finset D → (D → ℤ) → F → Finset V → V → V → Option ℤ) :
    Prop :=
  ∀ P ℓ φ B, (∀ d ∈ P, 0 ≤ ℓ d) → OnFace M φ B → MSSPOut (pieceGraph M P ℓ) B (mssp P ℓ φ B)

end MSSP

end PlanarFlow
