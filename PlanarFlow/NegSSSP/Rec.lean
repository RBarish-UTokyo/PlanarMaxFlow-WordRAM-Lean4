module

public import PlanarFlow.NegSSSP.Step
public import PlanarFlow.BKMNW.Sep

/-!
# The recursion of Klein–Mozes–Weimann and Mozes–Wulff-Nilsen

The algorithm for shortest paths with negative lengths of Klein, Mozes and Weimann (ACM Trans.
Algorithms 6 (2010), 30), in the form described by Mozes and Wulff-Nilsen (ESA 2010, the article,
Section 3), on the graph of a map `N` with lengths `ℓ` on the darts:

* **split** the piece by a separator (`sep`, meeting `PlanarFlow.BKMNW.SepSpec` for the cost
  bound of `PlanarFlow/NegSSSP/Cost.lean`, which cannot be met in general), into two pieces; the
  build of the decomposition (`NTree.build`) checks that the two pieces are smaller and cover the
  piece, and otherwise makes the piece a leaf. The decomposition used by the maximum-flow
  algorithm is instead one by simple cycle separators (`PlanarFlow.NegSSSP.negDecF`,
  `PlanarFlow/NegSSSP/FaceDec.lean`), with the shared vertices of every node on one face and a
  cost bound without hypothesis on separators;
* **recurse** on both pieces, each on its own darts;
* **combine** (`step`, `PlanarFlow/NegSSSP/Step.lean`): the dense distance graphs of both pieces
  on the boundary by multiple-source shortest paths, Bellman–Ford over their union, Dijkstra with
  a price function in both pieces;
* at a **leaf**, Bellman–Ford on the piece (`leafBF`: `|W|` rounds over the vertices `W` of the
  piece, then a check of feasibility);
* **negative cycles**: a piece without a feasible potential (reported by a leaf, or by
  Bellman–Ford over the dense distance graphs) makes the whole graph without one.

The output is a feasible potential of the graph, or `none` when there is none; then the graph has
a closed walk of negative length.

## Main results

* `run_potOut`: on every decomposition, the result is a feasible potential of the piece, or
  `none` and the piece has none, from the specifications of multiple-source shortest paths
  (`PieceMSSPSpec`), Bellman–Ford over dense distance graphs (`BFDDGSpec`) and FR-Dijkstra
  (`PlanarFlow.BKMNW.FRSpec`, at the vertices with a virtual root, `Option V`).
* `negSSSP_potOut`: the same for the whole graph `N.graph ℓ`; no hypothesis on the separator is
  needed for correctness.
* `negSSSPSpec_dual`: **the algorithm, run on the dual map `M.dual`, meets
  `PlanarFlow.BKMNW.NegSSSPSpec M`**, the specification used by the maximum-flow algorithm.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset BKMNW CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable {N : CombMap D V F}

/-! ### The leaves: Bellman–Ford on the piece -/

variable (N) in
/-- The digraph of a piece on its own vertices. -/
def leafGraph (P : Finset D) (ℓ : D → ℤ) : Digraph {x // x ∈ verts N P} {d // d ∈ P} where
  src d := ⟨N.tail d.1, tail_mem_verts d.2⟩
  dst d := ⟨N.head d.1, head_mem_verts d.2⟩
  len d := ℓ d.1

variable (N) in
/-- **The leaf solver**: Bellman–Ford on the vertices of the piece, then a check of
feasibility; the potential is extended by `0` outside the piece. -/
noncomputable def leafBF (P : Finset D) (ℓ : D → ℤ) : Option (V → ℤ) :=
  (bfCheck (leafGraph N P ℓ)).map fun E v => if h : v ∈ verts N P then E ⟨v, h⟩ else 0

theorem leafBF_potOut (P : Finset D) (ℓ : D → ℤ) : PotOut (pg N P ℓ) (leafBF N P ℓ) := by
  have h := potOut_bf (leafGraph N P ℓ)
  unfold leafBF
  rcases hc : bfCheck (leafGraph N P ℓ) with _ | E
  · rw [hc] at h
    exact fun ⟨p, hp⟩ => h ⟨fun x => p x.1, fun a => hp a⟩
  · rw [hc] at h
    intro a
    have := h a
    simp only [leafGraph] at this
    show (if h : N.head a.1 ∈ verts N P then E ⟨_, h⟩ else 0) ≤
      (if h : N.tail a.1 ∈ verts N P then E ⟨_, h⟩ else 0) + ℓ a.1
    simp only [head_mem_verts a.2, tail_mem_verts a.2, ↓reduceDIte]
    exact this

/-! ### The decomposition -/

/-- **A recursive decomposition**: a binary tree whose leaves carry pieces. -/
inductive NTree (D : Type*) where
  | leaf (P : Finset D)
  | node (l r : NTree D)

namespace NTree

/-- The piece of a node: the darts of its leaves. -/
def piece : NTree D → Finset D
  | leaf P => P
  | node l r => l.piece ∪ r.piece

/-- **The decomposition computed by a separator subroutine**: a piece of more than `s` darts is
split by the separator, called on the piece alone (no holes), when both parts are smaller and
cover the piece. -/
noncomputable def build (sep : Finset D → List (Finset V) → Finset D × Finset D × SPath N)
    (s : ℕ) (P : Finset D) : NTree D :=
  if _h : s < P.card ∧ (sep P []).1.card < P.card ∧ (sep P []).2.1.card < P.card ∧
      (sep P []).1 ∪ (sep P []).2.1 = P then
    node (build sep s (sep P []).1) (build sep s (sep P []).2.1)
  else leaf P
termination_by P.card
decreasing_by
  · exact _h.2.1
  · exact _h.2.2.1

theorem piece_build (sep : Finset D → List (Finset V) → Finset D × Finset D × SPath N)
    (s : ℕ) : ∀ (n : ℕ) (P : Finset D), P.card ≤ n → (build sep s P).piece = P := by
  intro n
  induction n with
  | zero =>
    intro P hP
    rw [build]
    split_ifs with h
    · omega
    · rfl
  | succ n ih =>
    intro P hP
    rw [build]
    split_ifs with h
    · simp only [piece]
      rw [ih _ (by omega), ih _ (by omega), h.2.2.2]
    · rfl

end NTree

/-! ### The algorithm -/

variable (N) in
/-- **The recursion** on a decomposition: Bellman–Ford at the leaves, `step` at the inner nodes,
`none` as soon as a piece has no feasible potential. -/
noncomputable def run (mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ)
    (bf : DDG V → DDG V → Option (V → ℤ))
    (fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V → (Option V → ℤ) →
      Option V → Option ℤ) : NTree D → (D → ℤ) → Option (V → ℤ)
  | .leaf P, ℓ => leafBF N P ℓ
  | .node l r, ℓ =>
    match run mssp bf fr l ℓ, run mssp bf fr r ℓ with
    | some δ₀, some δ₁ => step N mssp bf fr l.piece r.piece ℓ δ₀ δ₁
    | _, _ => none

/-- **Correctness of the recursion**, on every decomposition. -/
theorem run_potOut {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}
    (hmssp : PieceMSSPSpec N mssp) {bf : DDG V → DDG V → Option (V → ℤ)} (hbf : BFDDGSpec bf)
    {fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V → (Option V → ℤ) →
      Option V → Option ℤ} (hfr : FRSpec fr) (ℓ : D → ℤ) :
    ∀ τ : NTree D, PotOut (pg N τ.piece ℓ) (run N mssp bf fr τ ℓ)
  | .leaf P => leafBF_potOut P ℓ
  | .node l r => by
    have il := run_potOut hmssp hbf hfr ℓ l
    have ir := run_potOut hmssp hbf hfr ℓ r
    simp only [run, NTree.piece]
    rcases hl : run N mssp bf fr l ℓ with _ | δ₀
    · rw [hl] at il
      exact not_pot_mono subset_union_left il
    rcases hr : run N mssp bf fr r ℓ with _ | δ₁
    · rw [hr] at ir
      exact not_pot_mono subset_union_right ir
    rw [hl] at il; rw [hr] at ir
    exact step_potOut hmssp hbf hfr il ir

variable (N) in
/-- **Shortest paths with negative lengths** in the graph of `N`: the recursion on the
decomposition of all the darts computed by the separator subroutine. -/
noncomputable def negSSSP (sep : Finset D → List (Finset V) → Finset D × Finset D × SPath N)
    (s : ℕ) (mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ)
    (bf : DDG V → DDG V → Option (V → ℤ))
    (fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V → (Option V → ℤ) →
      Option V → Option ℤ) (ℓ : D → ℤ) : Option (V → ℤ) :=
  run N mssp bf fr (NTree.build sep s univ) ℓ

/-- **Correctness**: the result is a feasible potential of the graph of `N`, or `none` and the
graph has no feasible potential. -/
theorem negSSSP_potOut (sep : Finset D → List (Finset V) → Finset D × Finset D × SPath N)
    (s : ℕ) {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}
    (hmssp : PieceMSSPSpec N mssp) {bf : DDG V → DDG V → Option (V → ℤ)} (hbf : BFDDGSpec bf)
    {fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V → (Option V → ℤ) →
      Option V → Option ℤ} (hfr : FRSpec fr) (ℓ : D → ℤ) :
    PotOut (N.graph ℓ) (negSSSP N sep s mssp bf fr ℓ) := by
  have h := run_potOut hmssp hbf hfr ℓ (NTree.build sep s univ)
  rw [NTree.piece_build sep s _ univ le_rfl] at h
  unfold negSSSP
  rcases ho : run N mssp bf fr (NTree.build sep s univ) ℓ with _ | p
  · rw [ho] at h
    exact fun ⟨p, hp⟩ => h ⟨p, fun a => hp a.1⟩
  · rw [ho] at h
    exact fun d => h ⟨d, mem_univ d⟩

/-- **Shortest paths with negative lengths, with negative cycles**: a feasible potential of the
graph of `N`, or a closed walk of negative length. -/
theorem negSSSP_out (sep : Finset D → List (Finset V) → Finset D × Finset D × SPath N)
    (s : ℕ) {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}
    (hmssp : PieceMSSPSpec N mssp) {bf : DDG V → DDG V → Option (V → ℤ)} (hbf : BFDDGSpec bf)
    {fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V → (Option V → ℤ) →
      Option V → Option ℤ} (hfr : FRSpec fr) (ℓ : D → ℤ) :
    NegSSSPOut (N.graph ℓ) (negSSSP N sep s mssp bf fr ℓ) :=
  negSSSPOut_of_potOut (negSSSP_potOut sep s hmssp hbf hfr ℓ)

/-- **The algorithm on the dual map meets the specification `NegSSSPSpec`** of shortest paths
with negative lengths in the dual graph, used by the maximum-flow algorithm. -/
theorem negSSSPSpec_dual [Fintype F] [DecidableEq F] (M : CombMap D V F)
    (sep : Finset D → List (Finset F) → Finset D × Finset D × SPath M.dual) (s : ℕ)
    {mssp : Finset D → (D → ℤ) → Finset F → F → F → Option ℤ}
    (hmssp : PieceMSSPSpec M.dual mssp) {bf : DDG F → DDG F → Option (F → ℤ)}
    (hbf : BFDDGSpec bf)
    {fr : DDG (Option F) → List (Option F × Option F × ℤ) → Option F → (Option F → ℤ) →
      Option F → Option ℤ} (hfr : FRSpec fr) :
    NegSSSPSpec M (negSSSP M.dual sep s mssp bf fr) := fun ℓ => by
  rw [← dual_graph]
  exact negSSSP_out sep s hmssp hbf hfr ℓ

end NegSSSP

end PlanarFlow
