module

public import PlanarFlow.BKMNW.Loops

/-!
# Maximum flow in plane graphs in `O(n log³ n)`: the headline

The algorithm of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J. Comput. 46(4),
2017) on a plane map `M` with `n` darts:

1. delete the loops (`PlanarFlow.BKMNW.nlMap`, `PlanarFlow/BKMNW/Loops.lean`);
2. preprocess (line 1 and footnote 4 of the article): triangulate by spokes of capacity zero and
   attach a pendant edge at every vertex, the terminals replaced by their pendant neighbours
   (`PlanarFlow.BKMNW.lpreMap`, at most `7 n` darts);
3. run Algorithm 1 with every recursive step on its piece map (`PlanarFlow.BKMNW.runL`) on a
   decomposition `τ` meeting `BalDecA` with `κ = 9`, `η = 6`, `s = 100000`, with the planar
   subroutines `planeOracles` (single-source single-sink maximum flow by the perturbed algorithm
   with the word-size perturbation, `PlanarFlow.STFlow.pstflowW`);
4. restrict to the darts of `M`, zero on the loops (`PlanarFlow.BKMNW.nlRun`).

`maxflow_plane_cost`: **for every plane map with transitive rotations and faces, nonnegative
capacities and disjoint sources and sinks, the result is a maximum flow, and its cost is at most
`C K n lg³ n + C₀ K₀ n lg n`** for subroutine costs meeting `SubCosts.Bounds K K₀`, with
`C = (s + 11)² · 448 · (27 Cₙ + 25)`, `C₀ = (s + 11)² · 28`, `Cₙ = 102256`.
`maxflow_plane_ofRotation_cost`: the same for the maps of plane rotation systems.

## What is proved and what is assumed

* **Correctness is unconditional**: the hypotheses are planarity, transitive rotations and faces,
  nonnegative capacities and disjoint terminals; the planar subroutines meet their specifications
  (`planeOracles_spec`).
* **The cost bound is unconditional in the abstract subroutine-cost model**: the decomposition
  exists for every such map (`PlanarFlow.BKMNW.exists_balDecA_pre`), and the counted cost of
  `runL` (`PlanarFlow.BKMNW.runLCost`, every call charged at the size of the piece map it runs on)
  is bounded for every family of costs meeting `SubCosts.Bounds K K₀`.
* **What remains a hypothesis** is `SubCosts.Bounds`: the costs of the subroutines (leaf solver
  `K₀ m`; separator `K m lg m`; linear bookkeeping `K m`; MSSP `K (m lg m + k² lg m)`; FR-Dijkstra
  `K (x lg² x + p lg x)`; shortest paths with negative lengths `K m lg² m`; single-source
  single-sink maximum flow `K m lg² m`), to be met by machine implementations. The decomposition
  `τ` is given by an existence proof, not computed by a program with a proved cost; computing it
  is charged as the separator calls `c.sep`.
* **The machine costs** (`PlanarFlow/BKMNW/MachCost.lean`, with a status table): the family
  `PlanarFlow.BKMNW.cMach C C₀` of the step bounds of the machine programs meets
  `SubCosts.Bounds (machK C) C₀` (`cMach_bounds`), and `maxflow_plane_cost_mach` is
  `maxflow_plane_cost` with these costs; the constants `C`, `C₀` of the separator, the bookkeeping
  and the leaf solver, which have no program yet, are parameters. Realized by machine runs within
  the step count of their field: every call of the s-t flow oracle on a piece map
  (`cMach_stflow_exec_piece`, with numbers of polynomial size); in the recursion for negative
  lengths, Dijkstra on explicit arcs by FR-Dijkstra with one corner (`NegSSSP.cNegMach_dij_exec`)
  and multiple-source shortest paths by Klein's program, at the size of the node
  (`NegSSSP.cNegMach_mssp_exec`). FR-Dijkstra runs within its field given the crossing inequality
  (`cMach_fr_exec`). Not yet realized: FR-Dijkstra and Bellman–Ford on the dense distance graphs of
  the algorithm (their Monge property is not proved), MSSP of the maximum-flow recursion (the
  masks of the queries), the separator (Miller's algorithm on the machine, budgeted `K m lg m`),
  the leaf solver and the bookkeeping.
* **Status of the subroutines**, in detail:
  - single-source single-sink maximum flow: the implementation used (`pstflowW`, the perturbed
    algorithm with the isolating perturbation `isoEps` of polynomial size) has the counted cost
    `36 K m lg m` (`PlanarFlow.STFlow.pstflowWCost_le`) in its own model `STCosts.Bounds`
    (`O(log n)` per dynamic-tree operation, Dijkstra in `O(m log m)`). It runs as a verified
    machine program (`PlanarFlow.STFlow.pstflowW_exec_exists`: at most `504000000 m lg m` steps,
    the perturbed lengths in real memory), whose numbers (keys, lengths, amounts, constants:
    `PlanarFlow.STFlow.isoKeys_bounded`, and the real memory of its start) are integers of
    absolute value at most `(m + 4) (2 R + 1) (Σ c + 1)`, `R = (F + 1) m (4 F + 6) #V`, kept in
    real registers as the rest of the algorithm keeps capacities and lengths. The lexicographic
    variant `pstflow` (keys of `O(m log m)` bits) has the same bounds (`pstflowCost_le`,
    `pstflow_exec_exists`);
  - FR-Dijkstra: a machine program computes the distances (`PlanarFlow.BKMNW.frProg_isDist`) in
    at most `6300 (N lg² N + m lg N)` steps (`PlanarFlow.Monge.FR.frCost_le_fr`), the form of the
    bound assumed; the oracle used for correctness is still the reference family `frRef`;
  - MSSP: the oracle used is Klein's trip on the cut of the dual graph along the separator
    (`PlanarFlow.Klein.msspPlaneK`, `msspPlaneK_spec`); the trip runs as a verified machine
    program (`PlanarFlow.Klein.klein_exec`, `klein_exec_exists`: at most
    `36500000 (N lg N + k t lg N)` steps for `t` target vertices, with the lengths in real memory,
    the initial trees and the reach bits of the targets in the input as preconditions), which
    reads out the answers: its output holds the distances from every root to every target
    (`PlanarFlow.Klein.kOut`), and the answers of `msspPlaneK` on the cut are those of the output
    divided by `2^|D'|` (`PlanarFlow.Klein.msspCutK_eq_out`). The
    data structure of Das, Kipouridis, Probst Gutenberg and Wulff-Nilsen (`msspPlane`, whose
    preprocessing count `PlanarFlow.MSSP.prep_cost_le` assumes the per-level bound of its
    Lemma 5.8) is kept in the library;
  - shortest paths with negative lengths: the oracle used (`negSSSPImpl`) is the recursion of
    Klein–Mozes–Weimann and Mozes–Wulff-Nilsen on a decomposition by simple cycle separators of
    the simple graph of the dual map, with the shared vertices of every node on one face of a
    plane map of `O(m)` darts containing each part, along a face of `O(√m)` darts
    (`NegSSSP.NTree.FDec`, `NegSSSP.OneFace`); on the piece maps it has the counted cost
    `O(m lg² m)` with explicit constants and no hypothesis on separators
    (`PlanarFlow.BKMNW.negSSSPImpl_cost`), in its own model `NegSSSP.NegCosts.Bounds`, which
    is not formally connected to the budget `K m lg² m` of `SubCosts.Bounds`. Multiple-source
    shortest paths in its pieces are Klein's trip (`NegSSSP.msspK`, meeting `PieceMSSPSpec` on
    every map): at a node, each part is one call from a face, run on the map of the instance with
    the sources copied inside the face (`PlanarFlow.Klein.srcMap`, which meets the hypotheses of
    the trip), and the program `kleinProg` runs there within `32886 · 2372500000 · m lg m` steps
    (`NegSSSP.splitF_exec`, `k²` path-sum queries counted), ending with the distances in the part
    between the shared vertices in its output. The hypotheses of `NegCosts.Bounds` are still not met
    by proved implementations in that model: Bellman–Ford over dense distance graphs is the
    reference version `bfRef`, the decomposition is given by an existence proof (its
    computation charged as the separator calls), and the cost of `msspK` as a function is not
    connected to the counted model;
  - the leaf solver, the separator and the bookkeeping: no implementation with a cost bound.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace BKMNW

open Finset CombMap PlanarSeparator.StDart

universe w

/-- `lg (7 n) ≤ 4 lg n`. -/
lemma lg_seven_mul (n : ℕ) : lg (7 * n) ≤ 4 * lg n := by
  unfold lg
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : Nat.log 2 (7 * n) ≤ Nat.log 2 n + 3 :=
      calc Nat.log 2 (7 * n) ≤ Nat.log 2 (n * 2 * 2 * 2) := Nat.log_mono_right (by omega)
        _ = Nat.log 2 n + 3 := by
          rw [Nat.log_mul_base (by norm_num) (by positivity),
            Nat.log_mul_base (by norm_num) (by positivity),
            Nat.log_mul_base (by norm_num) (by omega)]
    omega

/-- The bound of `maxflow_cost` in the form `C K n lg³ n + C₀ K₀ n lg n`. -/
lemma cost_bound_le (K K₀ n : ℕ) :
    (100000 + 11) ^ 2 * ((27 * ((6 + 1) * (25 + 7 * 9 ^ 2 + 2 * 6 * (34 + 14 * 9 ^ 2))) + 25) *
        K * (7 * n) * lg (7 * n) ^ 3 + K₀ * (7 * n) * lg (7 * n)) ≤
      (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * n * lg n ^ 3 +
        (100000 + 11) ^ 2 * 28 * K₀ * n * lg n := by
  have h := lg_seven_mul n
  have h3 : lg (7 * n) ^ 3 ≤ 64 * lg n ^ 3 :=
    (Nat.pow_le_pow_left h 3).trans (by ring_nf; exact le_rfl)
  have e : (27 * ((6 + 1) * (25 + 7 * 9 ^ 2 + 2 * 6 * (34 + 14 * 9 ^ 2))) + 25) =
      27 * 102256 + 25 := by norm_num
  rw [e]
  have h1 : (27 * 102256 + 25) * K * (7 * n) * lg (7 * n) ^ 3 ≤
      448 * (27 * 102256 + 25) * K * n * lg n ^ 3 :=
    calc (27 * 102256 + 25) * K * (7 * n) * lg (7 * n) ^ 3
        ≤ (27 * 102256 + 25) * K * (7 * n) * (64 * lg n ^ 3) := Nat.mul_le_mul_left _ h3
      _ = 448 * (27 * 102256 + 25) * K * n * lg n ^ 3 := by ring
  have h2 : K₀ * (7 * n) * lg (7 * n) ≤ 28 * K₀ * n * lg n :=
    calc K₀ * (7 * n) * lg (7 * n) ≤ K₀ * (7 * n) * (4 * lg n) := Nat.mul_le_mul_left _ h
      _ = 28 * K₀ * n * lg n := by ring
  calc (100000 + 11) ^ 2 * ((27 * 102256 + 25) * K * (7 * n) * lg (7 * n) ^ 3 +
        K₀ * (7 * n) * lg (7 * n))
      ≤ (100000 + 11) ^ 2 * (448 * (27 * 102256 + 25) * K * n * lg n ^ 3 +
        28 * K₀ * n * lg n) := Nat.mul_le_mul_left _ (Nat.add_le_add h1 h2)
    _ = _ := by ring

section Main

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **Maximum flow in plane graphs in `O(n log³ n)`**: on every plane map with transitive
rotations and faces, with `n` darts (loops allowed), nonnegative capacities and disjoint sources
and sinks, there is a decomposition `τ` of the preprocessed map without loops meeting `BalDecA`
(`κ = 9`, `η = 6`, `s = 100000`) such that the algorithm with the planar subroutines
`planeOracles` (`nlRun`) computes a maximum flow of `M`, at a cost at most
`C K n lg³ n + C₀ K₀ n lg n` for every family of subroutine costs meeting
`SubCosts.Bounds K K₀`, with `C = (s + 11)² · 448 · (27 · 102256 + 25)` and
`C₀ = (s + 11)² · 28`. -/
theorem maxflow_plane_cost (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) {c : SubCosts}
    {K K₀ : ℕ} (hc : c.Bounds K K₀) :
    ∃ τ : ADec (lpreMap M),
      BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) ∧
      runLCost (lpreMap M) c τ ≤
        (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) := by
  obtain ⟨τ, h1, h2, h3⟩ := maxflow_cost hM hrot hface hu hST
    (planeOracles_spec _ fun X => frRef_spec X) hc
  exact ⟨τ, h1, h2, h3.trans (cost_bound_le K K₀ _)⟩

end Main

/-- **The same for the maps of plane rotation systems**, which have transitive rotations and
faces. -/
theorem maxflow_plane_ofRotation_cost {W : Type w} [Fintype W] [DecidableEq W]
    {Γ : SimpleGraph W} [DecidableRel Γ.Adj] {R : Kasteleyn.RotationSystem Γ} (hR : R.IsPlane)
    {u : Γ.Dart → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset W} (hST : Disjoint S T) {c : SubCosts}
    {K K₀ : ℕ} (hc : c.Bounds K K₀) :
    ∃ τ : ADec (lpreMap (CombMap.ofRotation R)),
      BalDecA (lpreMap (CombMap.ofRotation R)) (preTerm (nlTerm (CombMap.ofRotation R) S))
        (preTerm (nlTerm (CombMap.ofRotation R) T)) 9 6 100000 τ ∧
      IsMax (CombMap.ofRotation R) u S T
        (nlRun (CombMap.ofRotation R) u S T τ (planeOracles fun X => frRef X)) ∧
      runLCost (lpreMap (CombMap.ofRotation R)) c τ ≤
        (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card Γ.Dart *
            lg (Fintype.card Γ.Dart) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card Γ.Dart * lg (Fintype.card Γ.Dart) :=
  maxflow_plane_cost (CombMap.ofRotation_isPlane hR) (MSSP.ofRotation_rotTrans R)
    (ofRotation_faceTrans R) hu hST hc

/-- The zero costs meet `SubCosts.Bounds K K₀` for all `K` and `K₀`. -/
theorem zeroCosts_bounds (K K₀ : ℕ) : SubCosts.Bounds ⟨0, 0, 0, 0, 0, 0, 0⟩ K K₀ :=
  ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _, fun _ _ => Nat.zero_le _,
    fun _ _ => Nat.zero_le _, fun _ => Nat.zero_le _, fun _ => Nat.zero_le _,
    fun _ => Nat.zero_le _⟩

/-- **The hypotheses of `maxflow_plane_cost` can be met, also by a map with a loop**: the map
`loopMap` (one vertex, one loop) is plane with transitive rotations and faces, the map of a
single edge too (`exists_balDecA_pre_hyps`), and cost families meeting `SubCosts.Bounds` exist. -/
theorem maxflow_plane_cost_hyps :
    (loopMap.IsPlane ∧ loopMap.RotTrans ∧ loopMap.FaceTrans ∧
      ∀ d, loopMap.head d = loopMap.tail d) ∧
    ((CombMap.ofRotation edgeRot).IsPlane ∧ (CombMap.ofRotation edgeRot).RotTrans ∧
      (CombMap.ofRotation edgeRot).FaceTrans) ∧
    ∀ K K₀, ∃ c : SubCosts, c.Bounds K K₀ := by
  obtain ⟨h1, h2, h3, -⟩ := exists_balDecA_pre_hyps
  exact ⟨loopMap_hyps, ⟨h1, h2, h3⟩, fun K K₀ => ⟨_, zeroCosts_bounds K K₀⟩⟩

end BKMNW

end PlanarFlow
