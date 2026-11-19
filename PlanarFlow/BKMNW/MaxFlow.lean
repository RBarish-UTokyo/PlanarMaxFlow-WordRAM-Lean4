module

public import PlanarFlow.BKMNW.Alternate
public import PlanarFlow.BKMNW.Chain
public import PlanarFlow.BKMNW.LocalCost
public import PlanarFlow.STFlow.Main
public import PlanarFlow.STFlow.Lex
public import PlanarFlow.STFlow.IsoRun
public import PlanarFlow.NegSSSP.FaceKlein

/-!
# Maximum flow in plane graphs: the unconditional correctness theorem

The algorithm of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J. Comput. 46(4),
2017), with every recursive step on its piece map (`PlanarFlow.BKMNW.runL`), as a function of the
map, the capacities, the sources and the sinks only:

* the decomposition is `PlanarFlow.BKMNW.chainDec` (`PlanarFlow/BKMNW/Chain.lean`), which meets
  the hypotheses of the correctness theorem `PlanarFlow.BKMNW.runL_isMax` on every plane map;
* the planar subroutines are `planeOracles fr`: multiple-source shortest paths by Klein's trip on
  the cut of the dual graph along the separator (`PlanarFlow.Klein.msspPlaneK`, inside `runL`;
  the data structure `PlanarFlow.BKMNW.msspPlane` of Das, Kipouridis, Probst Gutenberg and
  Wulff-Nilsen is kept in the library); shortest paths with negative lengths by
  the recursion of Klein–Mozes–Weimann and Mozes–Wulff-Nilsen on the dual map
  (`PlanarFlow.NegSSSP.negSSSPDecF`, `negSSSPImpl`), through its simple graph, on a
  decomposition by simple cycle separators with the shared vertices of every node on one face
  (`PlanarFlow.NegSSSP.negDecF`), of counted cost `O(n log² n)` (`negSSSPImpl_cost`), with
  multiple-source shortest paths in its pieces by Klein's trip on the map with the sources
  copied inside that face (`PlanarFlow.NegSSSP.msspK`) and Bellman–Ford over dense distance
  graphs by its reference version (`bfRef`);
  single-source single-sink maximum flow by the algorithm of Borradaile and Klein with the
  capacities perturbed by a word-size isolating perturbation (`PlanarFlow.STFlow.pstflowW`, the
  perturbation `isoEps` of polynomial size, whose pivot bound is proved:
  `PlanarFlow.STFlow.pstflowWCost_le`; the lexicographic variant `PlanarFlow.STFlow.pstflow`
  has the same bound, `PlanarFlow.STFlow.pstflowCost_le`, with keys of `O(m log m)` bits); and
  FR-Dijkstra by the family `fr`.

The algorithm calls the s-t flow subroutine only inside `PlanarFlow.BKMNW.c2sImpl` (lines 2–7
of Algorithm 5), on the map it runs on: in `runL`, the piece map `pmap` (a `subMap`, whose
rotations and faces are transitive, `PlanarFlow.Orbit.subMap_rotTrans`,
`PlanarFlow.Orbit.subMap_faceTrans`, and which is plane when the piece is connected after
contracting its holes, `PlanarFlow.BKMNW.PieceInv.isPlane`), with the capacities `c2sCap`, which
are nonnegative whenever the current flow is a pseudoflow (`c2sCap_nonneg`). These are the
hypotheses of `pstflowWCost_le`. Correctness only uses `pstflowW_spec`, which needs planarity
alone, so no fallback to another implementation is needed.

FR-Dijkstra is given here only by its specification `PlanarFlow.BKMNW.FRSpec`; its machine
implementation is not connected to this file. It is therefore a parameter: `algoWith fr` and
`maxflow_plane_of_frSpec` take a family `fr` meeting `FRSpec`, and `frRef` is a family that meets
it (the distances themselves, `PlanarFlow.BKMNW.exists_frSpec`; a witness, not an algorithm).

## Main results

* `planeOracles_spec`, `exists_planeOracles`: the planar subroutines meet `PlaneOracles.Spec`.
* `maxflow_plane_of_frSpec`: for every family `fr` meeting `FRSpec`, `algoWith fr` computes a
  maximum flow on every plane map with transitive rotations and faces, nonnegative capacities and
  disjoint sources and sinks.
* `maxflow_plane`: **the same for `algo = algoWith frRef`, with no other hypothesis.**
* `maxflow_plane_ofRotation`, `maxflow_plane_ofRotation_of_frSpec`: for the maps of plane
  rotation systems.

## The cost

`runL_isMax_cost`: correctness and the bound `O(n log³ n)` of `PlanarFlow.BKMNW.runL_cost` for
`runL` on every decomposition meeting `BalDec` (the hypotheses of correctness and
`PlanarFlow.BKMNW.ADec.Bal`), **with `BalDec` an explicit hypothesis**. As in the article, the
separators may pass through the holes (the earlier separators, contracted in the piece maps), and
the holes they meet are merged with them. `BalDec` holds on maps all of whose darts leave
terminals (`balDec_leaf`); on other maps its satisfiability is open (see `BalDec`). `chainDec` is
not balanced, so no `O(n log³ n)` bound is claimed for `algo`.

`runL_isMax_costA`: the same with the weaker balance of the article (`BalDecA`,
`PlanarFlow.BKMNW.ADec.BalA`: splits balanced in size alternate with splits that need not be,
three quarters, small pieces exempt), still with the decomposition as an explicit hypothesis.

## The headline

`PlanarFlow.BKMNW.maxflow_plane_cost` (`PlanarFlow/BKMNW/Headline.lean`) removes that hypothesis:
on every plane map with transitive rotations and faces (loops allowed), nonnegative capacities
and disjoint terminals, `runL` with `planeOracles` on the preprocessed map without loops, on a
decomposition meeting `BalDecA` (which exists, `PlanarFlow.BKMNW.exists_balDecA_pre`), computes a
maximum flow (**correctness unconditional**) at a cost `C K n lg³ n + C₀ K₀ n lg n` with explicit
constants (**unconditional in the abstract subroutine-cost model**). What remains a hypothesis is
`SubCosts.Bounds`, the costs of the subroutines, to be met by machine implementations; none of
the subroutines is yet a machine implementation connected to the algorithm and proved to meet
its bound (the status of each is listed in `PlanarFlow/BKMNW/Headline.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

universe w

/-! ### The planar subroutines -/

/-- **FR-Dijkstra, a reference family**: the distances themselves, which meet `FRSpec`
(`PlanarFlow.BKMNW.exists_frSpec`); a witness that the specification can be met, not an
algorithm. -/
noncomputable def frRef (X : Type*) [Fintype X] [DecidableEq X] : FRFun X :=
  (exists_frSpec X).choose

theorem frRef_spec (X : Type*) [Fintype X] [DecidableEq X] : FRSpec (frRef X) :=
  (exists_frSpec X).choose_spec

variable (fr : (X : Type w) → [Fintype X] → [DecidableEq X] → FRFun X)

/-- **Shortest paths with negative lengths in the dual graph**: the recursion of
Klein–Mozes–Weimann and Mozes–Wulff-Nilsen on the dual map, through its simple graph, on a
decomposition by simple cycle separators with the shared vertices of every node on one face
(`PlanarFlow.NegSSSP.negSSSPDecF`, `PlanarFlow.NegSSSP.negDecF`), with FR-Dijkstra from `fr` and
multiple-source shortest paths in the pieces by Klein's trip (`PlanarFlow.NegSSSP.msspK`: on the
maps it is called on, every call of the recursion is one call from a face, answered by the trip
on the map with the sources copied inside the face, `PlanarFlow.NegSSSP.splitF_faceData`), and
the reference version of Bellman–Ford over dense distance graphs (`bfRef`). Its counted cost is
`O(n log² n)` on the maps it is called on (`negSSSPImpl_cost`). -/
noncomputable def negSSSPImpl {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] (M : CombMap D V F) :
    (D → ℤ) → Option (F → ℤ) :=
  NegSSSP.negSSSPDecF M.dual (NegSSSP.msspK M.dual) NegSSSP.bfRef (fr (Option F))

theorem negSSSPImpl_spec (hfr : ∀ (X : Type w) [Fintype X] [DecidableEq X], FRSpec (fr X))
    {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
    [DecidableEq F] (M : CombMap D V F) : NegSSSPSpec M (negSSSPImpl fr M) :=
  NegSSSP.negSSSPDecF_spec_dual M NegSSSP.msspK_spec NegSSSP.bfRef_spec (hfr _)

/-- **The counted cost of `negSSSPImpl` is `O(n log² n)`** on every plane map with transitive
rotations and faces and `n` darts (the piece maps on which the algorithm calls it), in the cost
model `PlanarFlow.NegSSSP.NegCosts.Bounds`, and its decomposition is by simple cycles with the
shared vertices of every node on one face (`PlanarFlow.NegSSSP.NTree.FDec`,
`PlanarFlow.NegSSSP.negSSSPDecF_dual`). -/
theorem negSSSPImpl_cost {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] {M : CombMap D V F} (hM : M.IsPlane)
    (hrot : M.RotTrans) (hface : M.FaceTrans) {c : NegSSSP.NegCosts} {K : ℕ}
    (hc : c.Bounds K) :
    negSSSPImpl fr M = NegSSSP.negSSSPDecF M.dual (NegSSSP.msspK M.dual) NegSSSP.bfRef
        (fr (Option F)) ∧ (NegSSSP.negDecF M.dual).FDec M.dual ∧
      NegSSSP.negDecFCost M.dual c ≤
        10920 * K * Fintype.card D * lg (Fintype.card D) ^ 2 + 1000001 * K * Fintype.card D :=
  ⟨rfl, NegSSSP.negDecF_fDec hM.dual (NegSSSP.dual_rotTrans hface) (NegSSSP.dual_faceTrans hrot),
    NegSSSP.negDecFCost_le hM.dual (NegSSSP.dual_rotTrans hface)
      (NegSSSP.dual_faceTrans hrot) hc⟩

/-- **The planar subroutines**: FR-Dijkstra from `fr`, shortest paths with negative lengths by
`negSSSPImpl`, single-source single-sink maximum flow by the perturbed algorithm with the
word-size perturbation `PlanarFlow.STFlow.pstflowW` (at most `m + 1` steps and cost
`36 K m lg m` on every plane map with transitive rotations and faces and nonnegative capacities,
`PlanarFlow.STFlow.pstflowWCost_le`; on the machine with keys of polynomial size,
`PlanarFlow.STFlow.pstflowW_exec_exists`). -/
noncomputable def planeOracles : PlaneOracles.{w} where
  fr X := fr X
  negSSSP M := negSSSPImpl fr M
  stflow M := STFlow.pstflowW M

/-- **The planar subroutines meet their specifications** when `fr` does. -/
theorem planeOracles_spec (hfr : ∀ (X : Type w) [Fintype X] [DecidableEq X], FRSpec (fr X)) :
    (planeOracles fr).Spec :=
  ⟨hfr, fun M _ _ _ => negSSSPImpl_spec fr hfr M, fun _ hM _ _ => STFlow.pstflowW_spec hM⟩

/-- **`PlaneOracles.Spec` can be met.** -/
theorem exists_planeOracles : ∃ O : PlaneOracles.{w}, O.Spec :=
  ⟨planeOracles fun X => frRef X, planeOracles_spec _ fun X => frRef_spec X⟩

/-! ### The algorithm -/

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

variable (M : CombMap D V F)

/-- **The algorithm, with FR-Dijkstra from `fr`**: Algorithm 1 with every recursive step on its
piece map (`runL`), on the decomposition `chainDec`, with the planar subroutines `planeOracles fr`.
-/
noncomputable def algoWith (u : D → ℤ) (S T : Finset V) : D → ℤ :=
  runL M u (chainDec M S T) (planeOracles fr) S T

/-- **The algorithm**: `algoWith` with the reference family `frRef` for FR-Dijkstra. -/
noncomputable def algo (u : D → ℤ) (S T : Finset V) : D → ℤ :=
  algoWith (fun X => frRef X) M u S T

variable {M}

/-- **Correctness, with FR-Dijkstra a parameter**: for every family `fr` meeting `FRSpec` (one
exists, `frRef_spec`), on a plane map with transitive rotations and faces, nonnegative capacities
and disjoint sources and sinks, the algorithm computes a maximum flow. -/
theorem maxflow_plane_of_frSpec
    (hfr : ∀ (X : Type w) [Fintype X] [DecidableEq X], FRSpec (fr X)) (hM : M.IsPlane)
    (hrot : M.RotTrans) (hface : M.FaceTrans) {u : D → ℤ} (hu : ∀ d, 0 ≤ u d)
    {S T : Finset V} (hST : Disjoint S T) : IsMax M u S T (algoWith fr M u S T) := by
  obtain ⟨h1, h2, h3, h4⟩ := chainDec_spec hM hrot hface S T
  exact runL_isMax hM hrot hface hu hST h1 h2 h3 h4 (planeOracles_spec fr hfr)

/-- **Maximum flow in plane graphs, unconditionally**: on a plane map with transitive rotations
and faces, with nonnegative capacities and disjoint sources and sinks, the algorithm computes a
maximum flow from `S` to `T`. -/
theorem maxflow_plane (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {u : D → ℤ}
    (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) : IsMax M u S T (algo M u S T) :=
  maxflow_plane_of_frSpec _ (fun X => frRef_spec X) hM hrot hface hu hST

/-! ### Plane rotation systems -/

/-- **Correctness for plane rotation systems, with FR-Dijkstra a parameter.** -/
theorem maxflow_plane_ofRotation_of_frSpec
    (hfr : ∀ (X : Type w) [Fintype X] [DecidableEq X], FRSpec (fr X)) {W : Type w} [Fintype W]
    [DecidableEq W] {Γ : SimpleGraph W} [DecidableRel Γ.Adj] {R : Kasteleyn.RotationSystem Γ}
    (hR : R.IsPlane) {u : Γ.Dart → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset W} (hST : Disjoint S T) :
    IsMax (CombMap.ofRotation R) u S T (algoWith fr (CombMap.ofRotation R) u S T) :=
  maxflow_plane_of_frSpec fr hfr (CombMap.ofRotation_isPlane hR) (MSSP.ofRotation_rotTrans R)
    (ofRotation_faceTrans R) hu hST

/-- **Maximum flow for plane rotation systems, unconditionally**: for the map of a plane rotation
system, with nonnegative capacities and disjoint sources and sinks, the algorithm computes a
maximum flow from `S` to `T`. -/
theorem maxflow_plane_ofRotation {W : Type w} [Fintype W] [DecidableEq W] {Γ : SimpleGraph W}
    [DecidableRel Γ.Adj] {R : Kasteleyn.RotationSystem Γ} (hR : R.IsPlane) {u : Γ.Dart → ℤ}
    (hu : ∀ d, 0 ≤ u d) {S T : Finset W} (hST : Disjoint S T) :
    IsMax (CombMap.ofRotation R) u S T (algo (CombMap.ofRotation R) u S T) :=
  maxflow_plane (CombMap.ofRotation_isPlane hR) (MSSP.ofRotation_rotTrans R)
    (ofRotation_faceTrans R) hu hST

/-! ### The cost -/

variable (M) in
/-- **The decompositions for the bound `O(n log³ n)`**: covering the darts, good, with pieces as
in the article and leaves solved by the leaf solver (the hypotheses of correctness), and balanced
(`ADec.Bal`: siblings nonempty with at most two thirds of the darts of their parent each,
separators with at most `η + 1` parts off the holes, of `k ≤ κ √m` darts each with `2 k ≤ m`, at
most `η` holes touching every piece). The separators are simple paths through the holes
(`ADec.PGood`): as in the article, where every earlier separator is one contracted node, a
separator may pass through the holes, and the holes it meets are merged with it into the new hole
(`PlanarFlow.BKMNW.childHoles`); its parts off the holes are simple paths of `M`
(`PlanarFlow.BKMNW.HSep.SegOK`).

`BalDec` can be met on maps all of whose darts leave terminals (`balDec_leaf`). Whether a
decomposition meeting `BalDec` exists for every plane map (or every triangulation with pendant
terminals, the class on which the article runs) and some constants `κ`, `η` is **open**: it is
neither proved nor refuted here. `chainDec` meets every condition but balance (its right children
are empty, its depth is the number of vertices).

The obstruction of the earlier definition, in which separators had to avoid the holes, is gone: on
a round annulus bounded by two holes, two radial cuts joined through the two holes are a short
separator through the holes. `BalDec` is still stronger than what the article constructs in two
ways, both removed by `BalDecA` (`PlanarFlow.BKMNW.ADec.BalA`, with the cost theorem
`runL_isMax_costA`):

* **every node is balanced in size**, whereas the article alternates splits balanced in size and
  splits balanced in the number of holes (Fakcharoenphol–Rao), and the latter need not balance
  size;
* **the two thirds are exact at every size**, whereas Miller's theorem balances the weight
  strictly on each side of the cycle, and distributing the darts along the cycle gives
  `2 m / 3 + O(√m)`.

What remains for an existence proof, beyond the alternation of the article (which bounds the holes
touching a piece): Miller's simple cycle separator
(`PlanarSeparator.Map.exists_short_cycle_separator`, at most `6 √n + 4` darts) is a theorem on
triangulations, and the article re-triangulates every piece with arcs of capacity zero (line 1 of
Algorithm 1). Here the map is fixed: it can be triangulated once, before the recursion
(`PlanarFlow/BKMNW/Triangulate.lean`), but the piece maps, with the earlier separators contracted
and the chords inside the holes left out, have faces of any size along the holes. The version with
weights on vertices and faces (`PlanarSeparator.Map.exists_short_cycle_separator_stellar`) gives a
cycle of the graph with a vertex added in every face, which may pass through these added vertices;
they are not vertices of the piece map. For the weaker `BalDecA` this is done
(`PlanarFlow.BKMNW.exists_balDecA_pre`, on the preprocessed map): with the holes that are cut
vertices pruned first, the faces of the piece maps of the cores are small, and a passage of the
cycle through an added vertex is replaced by darts of the face. -/
def BalDec (S T : Finset V) (κ η : ℕ) (τ : ADec M) : Prop :=
  τ.piece = univ ∧ τ.Good M S T [] ∧ τ.PGood M [] ∧ τ.LeafOK M S T [] ∧ τ.Bal M κ η []

/-- **`BalDec` can be met**, for all `κ` and `η`, on every plane map with transitive rotations
and faces all of whose darts leave terminals: the whole map is one leaf. This is the witness that
the hypothesis of `runL_isMax_cost` is satisfiable (for instance with `S = univ`, `T = ∅`); on
maps with a dart leaving a vertex that is not a terminal, the existence of a decomposition meeting
`BalDec` is open (see `BalDec`). -/
theorem balDec_leaf (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {S T : Finset V}
    (hcov : ∀ d, M.tail d ∈ S ∪ T) (κ η : ℕ) : BalDec M S T κ η (.leaf univ) := by
  refine ⟨rfl, fun d _ => mem_univ _, ?_, Or.inr fun d _ => ?_, trivial⟩
  · by_cases hD : Nonempty D
    · exact ADec.hConn_univ hM hrot hface hD
    · intro x; exact absurd ⟨x⟩ hD
  · simpa [hunion] using hcov d

/-- **Correctness and the bound `O(n log³ n)`, with a balanced decomposition as an explicit
hypothesis**: on a plane map with `n ≥ 1` darts, transitive rotations and faces, nonnegative
capacities and disjoint sources and sinks, for a decomposition `τ` meeting `BalDec` and planar
subroutines meeting their specifications (`exists_planeOracles`), `runL` computes a maximum flow,
and under the cost bounds `SubCosts.Bounds` of the subroutines its cost (every call charged at the
size of its piece map) is at most `(54 Cₙ + 58) K n lg³ n + 2 K₀ n lg n` with `Cₙ = (η + 1) (25 + 7
κ² + 2 η (34 + 14 κ²))` (`PlanarFlow.BKMNW.runL_cost`). The existence of a decomposition meeting
`BalDec` is not proved (see `BalDec`), so the bound is **conditional**. -/
theorem runL_isMax_cost (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {u : D → ℤ}
    (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) {κ η : ℕ} {τ : ADec M}
    (hτ : BalDec M S T κ η τ) {O : PlaneOracles.{w}} (hO : O.Spec) {c : SubCosts} {K K₀ : ℕ}
    (hc : c.Bounds K K₀) (hD : 0 < Fintype.card D) :
    IsMax M u S T (runL M u τ O S T) ∧
      runLCost M c τ ≤ (54 * ((η + 1) * (25 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2))) + 58) * K *
        Fintype.card D * lg (Fintype.card D) ^ 3 + 2 * K₀ * Fintype.card D * lg (Fintype.card D) :=
  ⟨runL_isMax hM hrot hface hu hST hτ.1 hτ.2.1 hτ.2.2.1 hτ.2.2.2.1 hO,
    runL_cost hM hτ.1 hτ.2.2.2.2 hc hD⟩

variable (M) in
/-- **The decompositions for the bound `O(n log³ n)`, with the balance of the article**: as
`BalDec`, with the balance `ADec.Bal` replaced by the weaker `ADec.BalA` (splits balanced in size
alternating with splits that need not be, three quarters instead of two thirds, no balance in
size below `s` darts). Every decomposition meeting `BalDec` meets `BalDecA` (`BalDec.balDecA`).

This removes the two differences with the article listed at `BalDec`; the separators pass through
the holes and merge them, as in the article. Decompositions meeting `BalDecA` exist, with
`κ = 9`, `η = 6` and `s = 100000`, on the preprocessed map (`PlanarFlow.CombMap.preMap`: the
triangulation with pendant terminals, the class on which the article runs) of every plane map
without loops with transitive rotations and faces (`PlanarFlow.BKMNW.exists_balDecA_pre`). Their
existence on every plane map itself (with terminals of any degree) is not proved. -/
def BalDecA (S T : Finset V) (κ η s : ℕ) (τ : ADec M) : Prop :=
  τ.piece = univ ∧ τ.Good M S T [] ∧ τ.PGood M [] ∧ τ.LeafOK M S T [] ∧ τ.BalA M κ η s true []

/-- A decomposition meeting `BalDec` meets `BalDecA`, for every `s`. -/
theorem BalDec.balDecA {S T : Finset V} {κ η : ℕ} {τ : ADec M} (h : BalDec M S T κ η τ) (s : ℕ) :
    BalDecA M S T κ η s τ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.balA s true⟩

/-- **`BalDecA` can be met**, for all `κ`, `η` and `s`, on every plane map with transitive
rotations and faces all of whose darts leave terminals (`balDec_leaf`). -/
theorem balDecA_leaf (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {S T : Finset V}
    (hcov : ∀ d, M.tail d ∈ S ∪ T) (κ η s : ℕ) : BalDecA M S T κ η s (.leaf univ) :=
  (balDec_leaf hM hrot hface hcov κ η).balDecA s

/-- **Correctness and the bound `O(n log³ n)` with the balance of the article, with the
decomposition as an explicit hypothesis**: on a plane map with `n ≥ 1` darts, transitive
rotations and faces, nonnegative capacities and disjoint sources and sinks, for a decomposition `τ`
meeting `BalDecA` and planar subroutines meeting their specifications (`exists_planeOracles`),
`runL` computes a maximum flow, and under the cost bounds `SubCosts.Bounds` of the subroutines its
cost is at most `(s + 11)² ((27 Cₙ + 25) K n lg³ n + K₀ n lg n)` with `Cₙ = (η + 1) (25 + 7 κ² + 2 η
(34 + 14 κ²))` (`PlanarFlow.BKMNW.runL_costA`). The hypothesis `BalDecA` is weaker than `BalDec`, so
this theorem implies `runL_isMax_cost` up to the constants. It is met on the preprocessed map of
every plane map without loops (`PlanarFlow.BKMNW.exists_balDecA_pre`), which gives the
unconditional bound `PlanarFlow.BKMNW.maxflow_pre_cost`; on the map itself the hypothesis is
explicit. -/
theorem runL_isMax_costA (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {u : D → ℤ}
    (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) {κ η s : ℕ} {τ : ADec M}
    (hτ : BalDecA M S T κ η s τ) {O : PlaneOracles.{w}} (hO : O.Spec) {c : SubCosts}
    {K K₀ : ℕ} (hc : c.Bounds K K₀) (hD : 0 < Fintype.card D) :
    IsMax M u S T (runL M u τ O S T) ∧
      runLCost M c τ ≤ (s + 11) ^ 2 * ((27 * ((η + 1) * (25 + 7 * κ ^ 2 +
        2 * η * (34 + 14 * κ ^ 2))) + 25) * K * Fintype.card D * lg (Fintype.card D) ^ 3 +
          K₀ * Fintype.card D * lg (Fintype.card D)) :=
  ⟨runL_isMax hM hrot hface hu hST hτ.1 hτ.2.1 hτ.2.2.1 hτ.2.2.2.1 hO,
    runL_costA hM hτ.1 hτ.2.2.2.2 hc hD⟩

end BKMNW

end PlanarFlow
