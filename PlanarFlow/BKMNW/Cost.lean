module

public import PlanarFlow.BKMNW.Algorithm
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Sqrt

/-!
# The cost of Algorithm 1

The cost of the algorithm of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J.
Comput. 46(4), 2017) is counted as an explicit recurrence following the calls of
`PlanarFlow.BKMNW.arun` (`arunCost`), with the costs of the planar subroutines as hypotheses
(`SubCosts.Bounds`, the bounds quoted in the article). With `lg m = ⌊log₂ m⌋ + 1`, `m` the size
of the input of a call and `k` the number of darts of a part of the separator off the holes (a
separator through `j` holes has at most `j + 1` parts, and lines 9–13 of Algorithm 1 run on each,
`PlanarFlow.BKMNW.sepStep`):

* MSSP (Klein; Cabello–Chambers–Erickson) on `m` darts: `K (m lg m + k² lg m)`;
* FR-Dijkstra on `x` vertices with `p` explicit arcs: `K (x lg² x + p lg x)`;
* shortest paths with negative lengths (Mozes–Wulff-Nilsen) on `m` darts: `K m lg² m`;
* single-source single-sink maximum flow (Borradaile–Klein) on `m` darts: `K m lg² m`. The
  article quotes `O(m log m)`; the extra factor `lg m` leaves room for a machine implementation
  of the perturbation that makes the pivots generic (`PlanarFlow.STFlow.pstflow`): its
  perturbed capacities are pairs whose second coordinates are integers of `O(m log F)` bits, and
  the deterministic scheme of Cabello, Chambers and Erickson (Section 6) costs an extra factor
  `O(log n)`. The per-step budget already allows `O(m lg² m)`, so the bound `O(n log³ n)` is
  unchanged;
* the separator on `m` darts: `K m lg m` (the article quotes `O(m)`; the extra factor `lg m`
  leaves room for a machine implementation of Miller's cycle separator, within the per-step
  budget `O(m lg² m)`);
* the bookkeeping on `m` elements: `K m`; the leaf solver on `m` darts: `K₀ m`.

## What `arun` does, and what it costs (`arunCost`, `arunCost_le`)

`arun` runs **every subroutine on the whole map `M`**, with the capacities zeroed outside the
piece (`capOn u P`): the flows are functions on all the darts of `M`; MSSP, the negative-length
shortest paths and the maximum flow run on `M` (or on `M` with a pendant edge at every vertex);
the push-back runs FR-Dijkstra on the whole dual of `M`; the separator is given `M` and the
piece. `arunCost` charges every call at the size of the map it runs on: `n` darts and `nf` faces
for the subroutines, and `N = mapSize M` (darts, vertices and faces) for every linear pass
(`SubCosts.fixRun`, `SubCosts.pushRun`, `SubCosts.c2sRun`, `SubCosts.nodeRun`,
`SubCosts.leafRun`). Only the FR-Dijkstra runs in the stages of FixConservationOnPath are on a
graph of the size of a part of the separator: the `x ≤ 2 k` faces along it, with its `2 k` darts
as explicit arcs.

A recursive step on one part therefore costs `O(N lg² N)` whatever the size of its piece
(`SubCosts.nodeRun_le`), a recursive step `O(η N lg² N)` with at most `η + 1` parts
(`SubCosts.nodeRuns_le`), and a balanced decomposition has fewer than `n` recursive steps and at
most `n` leaves: **the cost of `arun` is `O(n N log² N)`** (`arunCost_le`), that is
`O(n² log² n)` on a plane map (`N ≤ 2 n + 2`). This is weaker than Theorem 1.1 of the article.

## The recurrence of the article (`pieceCost`, `pieceCost_le_cube`)

The article runs the subroutines of a recursive step on the *piece* (its subgraph, with the
separators of the ancestors contracted into the hole nodes), of the size of the piece.
`pieceCost` is that recurrence: every call is charged at the size `m` of the piece. **It is not
the cost of `arun`**, whose subroutines run on the whole map; it is the bound that an
implementation running the subroutines on maps of the size of the pieces would have to meet:

* the push-back of Appendix C (`SubCosts.pushback`): two runs of FR-Dijkstra to cancel the flow
  cycles, and linear visits, `O(m lg² m)` (`SubCosts.pushback_le`);
* FixConservationOnPath (Section 3.2, "Running time analysis", `SubCosts.fix`): one MSSP, `k`
  stages of one FR-Dijkstra each on the `≤ 2k` faces along the path with the `2k` explicit
  darts, one negative-length shortest-path computation, and linear bookkeeping. One stage costs
  `fr (2k) (2k) ≤ 4 K k lg² m` (`SubCosts.stage_le`), the bound `O(√m log² m)` per stage that the
  recurrence needs when `k ≤ κ √m`; hence FixConservationOnPath costs `O(m lg² m)`
  (`SubCosts.fix_le`);
* CycleToSingleSinkLimitedMaxFlow (Section 4, `SubCosts.c2s`): one maximum flow, one
  FixConservationOnPath and one push-back; a recursive step (`SubCosts.node`): the separator, one
  FixConservationOnPath, two calls of Section 4 for each hole touching the piece (at most `η`),
  and two push-backs, `O(m lg² m)` (`SubCosts.node_le`), for each of the at most `η + 1` parts of
  the separator (`SubCosts.nodes`, `SubCosts.nodes_le`).

As in the article, the pieces at one depth of the decomposition are disjoint, so a depth costs
`O(n lg² n)`, and a balanced decomposition has depth at most `2 log₂ n + 1`; hence
`pieceCost_le_cube`: the recurrence is `O(n log³ n)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset

/-- `lg m = ⌊log₂ m⌋ + 1`. -/
def lg (m : ℕ) : ℕ := Nat.log 2 m + 1

lemma lg_mono {m n : ℕ} (h : m ≤ n) : lg m ≤ lg n := by
  unfold lg; have := Nat.log_mono_right (b := 2) h; omega

lemma one_le_lg (m : ℕ) : 1 ≤ lg m := by unfold lg; omega

lemma lg_three_mul (m : ℕ) : lg (3 * m) ≤ 3 * lg m := by
  unfold lg
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have : Nat.log 2 (3 * m) ≤ Nat.log 2 m + 2 :=
      calc Nat.log 2 (3 * m) ≤ Nat.log 2 (m * 2 * 2) := Nat.log_mono_right (by omega)
        _ = Nat.log 2 m + 2 := by
          rw [Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega)]
    omega

/-- The costs of the subroutines. -/
structure SubCosts where
  /-- The leaf solver, on `m` darts. -/
  leaf : ℕ → ℕ
  /-- The separator. -/
  sep : ℕ → ℕ
  /-- MSSP on `m` darts with a path of `k` darts. -/
  mssp : ℕ → ℕ → ℕ
  /-- FR-Dijkstra on `x` vertices with `p` explicit arcs. -/
  fr : ℕ → ℕ → ℕ
  /-- Shortest paths with negative lengths. -/
  negsssp : ℕ → ℕ
  /-- Single-source single-sink maximum flow. -/
  stflow : ℕ → ℕ
  /-- Linear bookkeeping. -/
  lin : ℕ → ℕ

namespace SubCosts

variable (c : SubCosts)

/-! #### The recurrence of the article: every call on a map of the size `m` of the piece -/

/-- **FixConservationOnPath in the recurrence of the article**, on `m` darts along a path of `k`
darts: MSSP, `k` stages of FR-Dijkstra, negative-length shortest paths, and linear bookkeeping. -/
def fix (m k : ℕ) : ℕ := c.mssp m k + k * c.fr (2 * k) (2 * k) + c.negsssp m + c.lin m

/-- **The push-back of Appendix C in the recurrence of the article** (`PlanarFlow.BKMNW.pushFwd`)
on `m` darts: the cancellation of the flow cycles by two runs of FR-Dijkstra in the dual (at
most `m` faces, `m` explicit arcs), and the visits, linear. -/
def pushback (m : ℕ) : ℕ := 2 * c.fr m m + c.lin m

/-- CycleToSingleSinkLimitedMaxFlow (or SingleSourceToCycle, `PlanarFlow.BKMNW.c2sImpl`) in the
recurrence of the article: a maximum flow, FixConservationOnPath on the piece with a pendant
edge at each of its vertices (at most `3 m` darts), and a push-back. -/
def c2s (m k : ℕ) : ℕ := c.stflow m + c.fix (3 * m) k + c.pushback m

/-- **A recursive step in the recurrence of the article** (on one part of the separator), on a
piece of `m` darts, with a part of `k` darts and `h` holes touching the piece. -/
def node (m k h : ℕ) : ℕ := c.sep m + c.fix m k + h * (2 * c.c2s m k) + 2 * c.pushback m

/-! #### The calls of `arun`: every call on the map it runs on

The sizes: `n` darts and `nf` faces of the map `M`, `N` its darts, vertices and faces
(`PlanarFlow.BKMNW.mapSize`), `k` darts of a part of the separator and `x` faces along it. -/

/-- **FixConservationOnPath as `PlanarFlow.BKMNW.fixPath` runs it**: MSSP on the map (`n` darts)
along the path of `k` darts; `k` stages, each one FR-Dijkstra on the dense distance graph of the
`x` faces along the path with the `2 k` darts of the path as explicit arcs, and the update of the
prices on these `x` faces; negative-length shortest paths in the dual of the map (`n` darts);
linear bookkeeping on the map it runs on (`L` elements). -/
def fixRun (n x k L : ℕ) : ℕ :=
  c.mssp n k + k * (c.fr x (2 * k) + c.lin x) + c.negsssp n + c.lin L

/-- **The push-back as `PlanarFlow.BKMNW.pushFwd` runs it**, on the map: two passes of the
cancellation, each one FR-Dijkstra in the whole dual (`nf` vertices, the `n` darts as explicit
arcs) and a linear pass; the order of the visits and the visits, linear in `N`. -/
def pushRun (n nf N : ℕ) : ℕ := 2 * (c.fr nf n + c.lin N) + 2 * c.lin N

/-- **CycleToSingleSinkLimitedMaxFlow as `PlanarFlow.BKMNW.c2sImpl` runs it** (or
`PlanarFlow.BKMNW.s2cImpl`): the maximum flow on the map (`n` darts); FixConservationOnPath on the
map with a pendant edge at every vertex (`PlanarFlow.BKMNW.fixFrozen`: MSSP and the
negative-length shortest paths run on the map, the bookkeeping on the map with the pendant edges,
at most `3 N` elements); the push-back on the map; linear bookkeeping (the reachable vertices
`C⁺`, the capacities, the sum). -/
def c2sRun (n nf N x k : ℕ) : ℕ :=
  c.stflow n + c.fixRun n x k (3 * N) + c.pushRun n nf N + 2 * c.lin N
/-- **A recursive step on one part of the separator as `PlanarFlow.BKMNW.arun` runs it** (with the
call of the separator that built it): the separator on the map and the piece, the sum of the two
flows and the capacities of the piece, FixConservationOnPath on the map, the test of each of the `a`
holes, the two calls of Section 4 for each of the `h` holes touching the piece
(`PlanarFlow.BKMNW.s2cImpl` is `PlanarFlow.BKMNW.c2sImpl` on the reversed flow, with two more linear
passes), and the two push-backs of line 13 with their bookkeeping. -/
def nodeRun (n nf N x k h a : ℕ) : ℕ :=
  c.sep n + c.lin N + c.fixRun n x k N + a * c.lin N +
    h * (2 * c.c2sRun n nf N x k + c.lin N) + 2 * (c.pushRun n nf N + c.lin N)

/-- **A leaf as `PlanarFlow.BKMNW.arun` runs it**: the leaf solver, which writes a flow on the
`n` darts of the map, the union of the `a` holes, and the capacities of the leaf. -/
def leafRun (n N a : ℕ) : ℕ := c.leaf n + (a + 1) * c.lin N

/-- **The steps on the parts of a separator in the recurrence of the article** (`sepStep`): a
recursive step `node` on each part of `k` darts, with the `h` holes touching the piece and the
later parts as holes (each charged as touching the piece). -/
def nodes (m h : ℕ) : List ℕ → ℕ
  | [] => 0
  | k :: ks => c.node m k (h + ks.length) + nodes m h ks

/-- **The steps on the parts of a separator as `PlanarFlow.BKMNW.sepStep` runs them**: `nodeRun`
on each part, given by the number of faces along it and its number of darts, with the `h` holes
touching the piece and the `a` holes, and the later parts as holes (each charged as touching the
piece). -/
def nodeRuns (n nf N h a : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | xk :: l => c.nodeRun n nf N xk.1 xk.2 (h + l.length) (a + l.length) + nodeRuns n nf N h a l

/-- **The hypotheses on the subroutine costs** (the bounds quoted in the article). -/
structure Bounds (K K₀ : ℕ) : Prop where
  leaf : ∀ m, c.leaf m ≤ K₀ * m
  /-- The separator: `O(m log m)`, the cost of a machine implementation of Miller's cycle
  separator (a spanning tree, the fundamental cycles, a search over them); the article quotes
  `O(m)`. The per-step budget allows `O(m lg² m)`, so the bound `O(n log³ n)` is unchanged. -/
  sep : ∀ m, c.sep m ≤ K * m * lg m
  mssp : ∀ m k, c.mssp m k ≤ K * (m * lg m + k ^ 2 * lg m)
  fr : ∀ x p, c.fr x p ≤ K * (x * lg x ^ 2 + p * lg x)
  negsssp : ∀ m, c.negsssp m ≤ K * m * lg m ^ 2
  /-- Single-source single-sink maximum flow: `O(m lg² m)`, an extra factor `lg m` over the
  `O(m log m)` of Borradaile and Klein, for the perturbation of the capacities. -/
  stflow : ∀ m, c.stflow m ≤ K * m * lg m ^ 2
  lin : ∀ m, c.lin m ≤ K * m

variable {c} {K K₀ : ℕ}

/-- The separator within the per-step budget `K m lg² m`. -/
lemma sep_le_sq (hc : c.Bounds K K₀) (m : ℕ) : c.sep m ≤ K * m * lg m ^ 2 :=
  (hc.sep m).trans (Nat.mul_le_mul_left _ (by have := one_le_lg m; nlinarith))

/-- **One stage of FixConservationOnPath** costs `O(k lg² m)`, hence `O(√m lg² m)` when
`k ≤ κ √m`. -/
theorem stage_le (hc : c.Bounds K K₀) {m k : ℕ} (hk : 2 * k ≤ m) :
    c.fr (2 * k) (2 * k) ≤ 4 * K * k * lg m ^ 2 := by
  have h1 := hc.fr (2 * k) (2 * k)
  have hl : lg (2 * k) ≤ lg m := lg_mono hk
  have hl1 := one_le_lg m
  have h2 : 2 * k * lg (2 * k) ^ 2 + 2 * k * lg (2 * k) ≤ 2 * k * lg m ^ 2 + 2 * k * lg m ^ 2 := by
    have : lg (2 * k) ≤ lg m ^ 2 := hl.trans (by nlinarith)
    have : lg (2 * k) ^ 2 ≤ lg m ^ 2 := Nat.pow_le_pow_left hl 2
    nlinarith
  calc c.fr (2 * k) (2 * k) ≤ K * (2 * k * lg (2 * k) ^ 2 + 2 * k * lg (2 * k)) := h1
    _ ≤ K * (2 * k * lg m ^ 2 + 2 * k * lg m ^ 2) := Nat.mul_le_mul_left _ h2
    _ = 4 * K * k * lg m ^ 2 := by ring

/-- The per-stage bound `O(√m lg² m)` (what the recurrence of the article needs), from
`k ≤ κ √m`. -/
theorem stage_le_sqrt (hc : c.Bounds K K₀) {m k κ : ℕ} (hk : 2 * k ≤ m) (hκ : k ≤ κ * Nat.sqrt m) :
    c.fr (2 * k) (2 * k) ≤ 4 * K * κ * Nat.sqrt m * lg m ^ 2 :=
  (stage_le hc hk).trans (by
    have := Nat.mul_le_mul_left (4 * K) hκ
    have := Nat.mul_le_mul_right (lg m ^ 2) this
    nlinarith)

/-- **The push-back costs `O(m lg² m)`.** -/
theorem pushback_le (hc : c.Bounds K K₀) (m : ℕ) : c.pushback m ≤ 5 * K * m * lg m ^ 2 := by
  have hl1 := one_le_lg m
  have hlg : lg m ≤ lg m ^ 2 := by nlinarith
  have h1 := hc.fr m m
  have h2 := hc.lin m
  have h3 : K * m ≤ K * m * lg m ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have h4 : K * (m * lg m) ≤ K * (m * lg m ^ 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlg)
  unfold pushback
  nlinarith

/-- **FixConservationOnPath costs `O(m lg² m)`** when `k² ≤ κ² m`. -/
theorem fix_le (hc : c.Bounds K K₀) {m k κ : ℕ} (hk : 2 * k ≤ m) (hκ : k ^ 2 ≤ κ ^ 2 * m) :
    c.fix m k ≤ (3 + 5 * κ ^ 2) * K * m * lg m ^ 2 := by
  have hl1 := one_le_lg m
  have hlg : lg m ≤ lg m ^ 2 := by nlinarith
  have h1 := hc.mssp m k
  have h2 : k * c.fr (2 * k) (2 * k) ≤ 4 * K * κ ^ 2 * m * lg m ^ 2 := by
    calc k * c.fr (2 * k) (2 * k) ≤ k * (4 * K * k * lg m ^ 2) :=
          Nat.mul_le_mul_left _ (stage_le hc hk)
      _ = 4 * K * k ^ 2 * lg m ^ 2 := by ring
      _ ≤ 4 * K * (κ ^ 2 * m) * lg m ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hκ)
      _ = 4 * K * κ ^ 2 * m * lg m ^ 2 := by ring
  have h3 := hc.negsssp m
  have h4 := hc.lin m
  have h5 : K * (m * lg m + k ^ 2 * lg m) ≤ K * (m * lg m ^ 2 + κ ^ 2 * m * lg m ^ 2) := by
    apply Nat.mul_le_mul_left
    have : k ^ 2 * lg m ≤ κ ^ 2 * m * lg m ^ 2 :=
      (Nat.mul_le_mul_right _ hκ).trans (Nat.mul_le_mul_left _ hlg)
    have : m * lg m ≤ m * lg m ^ 2 := Nat.mul_le_mul_left _ hlg
    omega
  have h6 : K * m ≤ K * m * lg m ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  unfold fix
  nlinarith

/-- **A recursive step costs `O(m lg² m)`**. -/
theorem node_le (hc : c.Bounds K K₀) {m k h κ η : ℕ} (hk : 2 * k ≤ m) (hκ : k ^ 2 ≤ κ ^ 2 * m)
    (hh : h ≤ η) :
    c.node m k h ≤ (14 + 5 * κ ^ 2 + 2 * η * (87 + 135 * κ ^ 2)) * K * m * lg m ^ 2 := by
  have hl1 := one_le_lg m
  have hlg : lg m ≤ lg m ^ 2 := by nlinarith
  have hfix := fix_le hc hk hκ
  have h6 : K * m ≤ K * m * lg m ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have hpb := pushback_le hc m
  have hfix3 : c.fix (3 * m) k ≤ 27 * (3 + 5 * κ ^ 2) * K * m * lg m ^ 2 := by
    have h1 := fix_le hc (m := 3 * m) (k := k) (κ := κ) (by omega) (by nlinarith)
    have h2 : lg (3 * m) ^ 2 ≤ 9 * lg m ^ 2 := by
      have := lg_three_mul m; nlinarith
    calc c.fix (3 * m) k ≤ (3 + 5 * κ ^ 2) * K * (3 * m) * lg (3 * m) ^ 2 := h1
      _ ≤ (3 + 5 * κ ^ 2) * K * (3 * m) * (9 * lg m ^ 2) := Nat.mul_le_mul_left _ h2
      _ = 27 * (3 + 5 * κ ^ 2) * K * m * lg m ^ 2 := by ring
  have hc2s : c.c2s m k ≤ (87 + 135 * κ ^ 2) * K * m * lg m ^ 2 := by
    unfold c2s
    have := hc.stflow m
    nlinarith
  have hh' : h * (2 * c.c2s m k) ≤ η * (2 * ((87 + 135 * κ ^ 2) * K * m * lg m ^ 2)) :=
    Nat.mul_le_mul hh (Nat.mul_le_mul_left _ hc2s)
  unfold node
  have := sep_le_sq hc m
  nlinarith

/-- **The steps on the parts of a separator cost `O(m lg² m)` each** in the recurrence of the
article, with at most `2 η` holes and later parts. -/
theorem nodes_le (hc : c.Bounds K K₀) {m h κ η : ℕ} :
    ∀ ks : List ℕ, (∀ k ∈ ks, 2 * k ≤ m ∧ k ^ 2 ≤ κ ^ 2 * m) → h + ks.length ≤ 2 * η + 1 →
      c.nodes m h ks ≤
        ks.length * ((14 + 5 * κ ^ 2 + 4 * η * (87 + 135 * κ ^ 2)) * K * m * lg m ^ 2)
  | [], _, _ => by simp [nodes]
  | k :: ks, hl, hh => by
    simp only [List.length_cons] at hh
    obtain ⟨h1, h2⟩ := hl k (List.mem_cons_self ..)
    have i := nodes_le hc (h := h) (κ := κ) (η := η) ks
      (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (by omega)
    have e := node_le hc (h := h + ks.length) (η := 2 * η) h1 h2 (by omega)
    rw [show 2 * (2 * η) = 4 * η by ring] at e
    simp only [nodes, List.length_cons]
    nlinarith

/-! #### Bounds on the calls of `arun` -/

lemma lg_le_sq (m : ℕ) : lg m ≤ lg m ^ 2 := by have := one_le_lg m; nlinarith

lemma lin_le_of_le (hc : c.Bounds K K₀) {m N : ℕ} (h : m ≤ N) : c.lin m ≤ K * N * lg N ^ 2 :=
  (hc.lin m).trans ((Nat.mul_le_mul_left K h).trans (Nat.le_mul_of_pos_right _ (by
    have := one_le_lg N; positivity)))

lemma sep_le_of_le (hc : c.Bounds K K₀) {m N : ℕ} (h : m ≤ N) : c.sep m ≤ K * N * lg N ^ 2 :=
  (sep_le_sq hc m).trans (Nat.mul_le_mul (Nat.mul_le_mul_left K h)
    (Nat.pow_le_pow_left (lg_mono h) 2))

/-- **FixConservationOnPath on the map costs `O(N lg² N)`.** -/
theorem fixRun_le (hc : c.Bounds K K₀) {n x k L N κ : ℕ} (hn : n ≤ N) (hx : x ≤ 2 * k)
    (hk : 2 * k ≤ N) (hκ : k ^ 2 ≤ κ ^ 2 * N) (hL : L ≤ 3 * N) :
    c.fixRun n x k L ≤ (5 + 7 * κ ^ 2) * K * N * lg N ^ 2 := by
  have hl1 := one_le_lg N
  have hlg := lg_le_sq N
  have hln : lg n ≤ lg N := lg_mono hn
  have hlx : lg x ≤ lg N := lg_mono (hx.trans hk)
  have h1 : c.mssp n k ≤ K * (N * lg N ^ 2 + κ ^ 2 * N * lg N ^ 2) := by
    refine (hc.mssp n k).trans (Nat.mul_le_mul_left _ ?_)
    have a1 : n * lg n ≤ N * lg N ^ 2 := Nat.mul_le_mul hn (hln.trans hlg)
    have a2 : k ^ 2 * lg n ≤ κ ^ 2 * N * lg N ^ 2 := Nat.mul_le_mul hκ (hln.trans hlg)
    omega
  have h2 : c.fr x (2 * k) + c.lin x ≤ 6 * K * k * lg N ^ 2 := by
    have b1 := hc.fr x (2 * k)
    have b2 := hc.lin x
    have b3 : x * lg x ^ 2 ≤ 2 * k * lg N ^ 2 := Nat.mul_le_mul hx (Nat.pow_le_pow_left hlx 2)
    have b4 : 2 * k * lg x ≤ 2 * k * lg N ^ 2 := Nat.mul_le_mul_left _ (hlx.trans hlg)
    have b5 : x ≤ 2 * k * lg N ^ 2 := hx.trans (Nat.le_mul_of_pos_right _ (by positivity))
    have : K * (x * lg x ^ 2 + 2 * k * lg x) ≤ K * (4 * k * lg N ^ 2) :=
      Nat.mul_le_mul_left _ (by
        rw [show 4 * k * lg N ^ 2 = 2 * k * lg N ^ 2 + 2 * k * lg N ^ 2 by ring]; omega)
    have : K * x ≤ K * (2 * k * lg N ^ 2) := Nat.mul_le_mul_left _ b5
    nlinarith
  have h3 : k * (c.fr x (2 * k) + c.lin x) ≤ 6 * K * κ ^ 2 * N * lg N ^ 2 := by
    calc k * (c.fr x (2 * k) + c.lin x) ≤ k * (6 * K * k * lg N ^ 2) :=
          Nat.mul_le_mul_left _ h2
      _ = 6 * K * k ^ 2 * lg N ^ 2 := by ring
      _ ≤ 6 * K * (κ ^ 2 * N) * lg N ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hκ)
      _ = 6 * K * κ ^ 2 * N * lg N ^ 2 := by ring
  have h4 : c.negsssp n ≤ K * N * lg N ^ 2 :=
    (hc.negsssp n).trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hn) (Nat.pow_le_pow_left hln 2))
  have h5 : c.lin L ≤ 3 * (K * N * lg N ^ 2) := by
    refine (hc.lin L).trans ?_
    have : K * L ≤ K * (3 * N) := Nat.mul_le_mul_left _ hL
    have : K * N ≤ K * N * lg N ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    nlinarith
  unfold fixRun
  nlinarith

/-- **The push-back on the map costs `O(N lg² N)`.** -/
theorem pushRun_le (hc : c.Bounds K K₀) {n nf N : ℕ} (hn : n ≤ N) (hf : nf ≤ N) :
    c.pushRun n nf N ≤ 8 * K * N * lg N ^ 2 := by
  have hl1 := one_le_lg N
  have hlg := lg_le_sq N
  have hlf : lg nf ≤ lg N := lg_mono hf
  have h1 : c.fr nf n ≤ 2 * (K * N * lg N ^ 2) := by
    refine (hc.fr nf n).trans ?_
    have : nf * lg nf ^ 2 ≤ N * lg N ^ 2 := Nat.mul_le_mul hf (Nat.pow_le_pow_left hlf 2)
    have : n * lg nf ≤ N * lg N ^ 2 := Nat.mul_le_mul hn (hlf.trans hlg)
    have : K * (nf * lg nf ^ 2 + n * lg nf) ≤ K * (2 * (N * lg N ^ 2)) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have h2 := lin_le_of_le hc (le_refl N)
  unfold pushRun
  nlinarith

/-- **CycleToSingleSinkLimitedMaxFlow on the map costs `O(N lg² N)`.** -/
theorem c2sRun_le (hc : c.Bounds K K₀) {n nf N x k κ : ℕ} (hn : n ≤ N) (hf : nf ≤ N)
    (hx : x ≤ 2 * k) (hk : 2 * k ≤ N) (hκ : k ^ 2 ≤ κ ^ 2 * N) :
    c.c2sRun n nf N x k ≤ (16 + 7 * κ ^ 2) * K * N * lg N ^ 2 := by
  have hl1 := one_le_lg N
  have hlg := lg_le_sq N
  have h1 : c.stflow n ≤ K * N * lg N ^ 2 :=
    (hc.stflow n).trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hn)
      (Nat.pow_le_pow_left (lg_mono hn) 2))
  have h2 := fixRun_le hc hn hx hk hκ (le_refl (3 * N))
  have h3 := pushRun_le hc hn hf
  have h4 := lin_le_of_le hc (le_refl N)
  unfold c2sRun
  nlinarith

/-- **A recursive step of `arun` costs `O(N lg² N)`**, whatever the size of its piece, with
`a ≤ 2 lg N + η` holes. -/
theorem nodeRun_le (hc : c.Bounds K K₀) {n nf N x k h a κ η : ℕ} (hn : n ≤ N) (hf : nf ≤ N)
    (hx : x ≤ 2 * k) (hk : 2 * k ≤ N) (hκ : k ^ 2 ≤ κ ^ 2 * N) (hh : h ≤ η)
    (ha : a ≤ 2 * lg N + η) :
    c.nodeRun n nf N x k h a ≤
      (27 + 7 * κ ^ 2 + η * (34 + 14 * κ ^ 2)) * K * N * lg N ^ 2 := by
  have hl1 := one_le_lg N
  have hlg := lg_le_sq N
  have h0 : K * N ≤ K * N * lg N ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have h1 : c.sep n ≤ K * N * lg N ^ 2 := sep_le_of_le hc hn
  have h2 := fixRun_le hc hn hx hk hκ (by omega : N ≤ 3 * N)
  have h3 := pushRun_le hc hn hf
  have h4 := lin_le_of_le hc (le_refl N)
  have h5 := c2sRun_le hc hn hf hx hk hκ
  have h6 : a * c.lin N ≤ 2 * (K * N * lg N ^ 2) + η * (K * N * lg N ^ 2) := by
    have := Nat.mul_le_mul ha (hc.lin N)
    have : 2 * lg N * (K * N) ≤ 2 * (K * N * lg N ^ 2) := by nlinarith
    have : η * (K * N) ≤ η * (K * N * lg N ^ 2) := Nat.mul_le_mul_left _ h0
    nlinarith
  have h7 : h * (2 * c.c2sRun n nf N x k + c.lin N) ≤
      η * ((33 + 14 * κ ^ 2) * K * N * lg N ^ 2) :=
    Nat.mul_le_mul hh (by nlinarith)
  unfold nodeRun
  nlinarith

/-- **The steps on the parts of a separator cost `O(N lg² N)`** each, with at most `2 η` holes
and later parts, and `a ≤ 2 lg N + 2 η`. -/
theorem nodeRuns_le (hc : c.Bounds K K₀) {n nf N h a κ η : ℕ} (hn : n ≤ N) (hf : nf ≤ N) :
    ∀ l : List (ℕ × ℕ), (∀ xk ∈ l, xk.1 ≤ 2 * xk.2 ∧ 2 * xk.2 ≤ N ∧ xk.2 ^ 2 ≤ κ ^ 2 * N) →
      h + l.length ≤ 2 * η + 1 → a + l.length ≤ 2 * lg N + 2 * η + 1 →
      c.nodeRuns n nf N h a l ≤
        l.length * ((27 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2)) * K * N * lg N ^ 2)
  | [], _, _, _ => by simp [nodeRuns]
  | xk :: l, hl, hh, ha => by
    simp only [List.length_cons] at hh ha
    obtain ⟨h1, h2, h3⟩ := hl xk (List.mem_cons_self ..)
    have i := nodeRuns_le hc (h := h) (a := a) (κ := κ) (η := η) hn hf l
      (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (by omega)
      (by omega)
    have e := nodeRun_le hc (h := h + l.length) (a := a + l.length) (η := 2 * η) hn hf h1 h2 h3
      (by omega) (by omega)
    simp only [nodeRuns, List.length_cons]
    nlinarith

/-- **A leaf of `arun` costs `O(N lg N)`**, with `a ≤ 2 lg N` holes. -/
theorem leafRun_le (hc : c.Bounds K K₀) {n N a : ℕ} (hn : n ≤ N) (ha : a ≤ 2 * lg N) :
    c.leafRun n N a ≤ 3 * K * N * lg N ^ 2 + K₀ * N := by
  have hl1 := one_le_lg N
  have hlg := lg_le_sq N
  have h1 : c.leaf n ≤ K₀ * N := (hc.leaf n).trans (Nat.mul_le_mul_left _ hn)
  have h2 : (a + 1) * c.lin N ≤ 3 * K * N * lg N ^ 2 := by
    have := Nat.mul_le_mul (by omega : a + 1 ≤ 3 * lg N) (hc.lin N)
    have : 3 * lg N * (K * N) ≤ 3 * K * N * lg N ^ 2 := by
      calc 3 * lg N * (K * N) = 3 * K * N * lg N := by ring
        _ ≤ 3 * K * N * lg N ^ 2 := Nat.mul_le_mul_left _ hlg
    omega
  unfold leafRun
  omega

end SubCosts

/-! ### The recurrence -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

open Classical in
/-- The number of holes touching a piece. -/
noncomputable def nTouch (M : CombMap D V F) (P : Finset D) (Hs : List (Finset V)) : ℕ :=
  (Hs.filter fun H => ∃ v ∈ H, Touch M P v).length

variable (M) in
/-- **The recurrence of the article**: the calls of `PlanarFlow.BKMNW.arun`, each charged at the
size of the piece, as if it ran on a map of that size. This is **not** the cost of `arun`, whose
subroutines run on the whole map (`arunCost`). -/
noncomputable def pieceCost (c : SubCosts) : ADec M → List (Finset V) → ℕ
  | .leaf Q, _ => c.leaf Q.card
  | .node l r π, Hs =>
    pieceCost c l (childHoles Hs π.path.mverts) + pieceCost c r (childHoles Hs π.path.mverts) +
      c.nodes (l.piece ∪ r.piece).card (nTouch M (l.piece ∪ r.piece) Hs) (π.segs.map SPath.k)

/-- **A short separator** of a piece of `m` darts: at most `η + 1` parts off the holes, each of
`k ≤ κ √m` darts (and `2 k ≤ m`). A separator through `j` holes has at most `j + 1` parts. -/
def HSep.Short (κ η m : ℕ) (π : HSep M) : Prop :=
  π.segs.length ≤ η + 1 ∧ ∀ σ ∈ π.segs, σ.k ^ 2 ≤ κ ^ 2 * m ∧ 2 * σ.k ≤ m

namespace ADec

/-- The depth of a decomposition. -/
def depth : ADec M → ℕ
  | leaf _ => 0
  | node l r _ => max l.depth r.depth + 1

variable (M) in
/-- **A balanced decomposition** for the cost: siblings are disjoint and nonempty, each has at
most two thirds of the darts of their parent, the separator is short (`HSep.Short`: at most
`η + 1` parts off the holes, of `k ≤ κ √m` darts each, `2 k ≤ m`), and every piece touches at
most `η` holes (the holes met by a separator count as one, merged with it). -/
def Bal (κ η : ℕ) : ADec M → List (Finset V) → Prop
  | leaf _, _ => True
  | node l r π, Hs => l.Bal κ η (childHoles Hs π.path.mverts) ∧
      r.Bal κ η (childHoles Hs π.path.mverts) ∧
      Disjoint l.piece r.piece ∧ 0 < l.piece.card ∧ 0 < r.piece.card ∧
      3 * l.piece.card ≤ 2 * (l.piece ∪ r.piece).card ∧
      3 * r.piece.card ≤ 2 * (l.piece ∪ r.piece).card ∧
      π.Short κ η (l.piece ∪ r.piece).card ∧ nTouch M (l.piece ∪ r.piece) Hs ≤ η

variable (M) in
/-- **The conditions of `Bal` other than the balance**: siblings disjoint and nonempty, short
separators (`HSep.Short`), at most `η` holes touching every piece. The cost of the recursion on
the piece maps is bounded under these conditions and a bound on the depth
(`PlanarFlow.BKMNW.arunLCost_le`). -/
def Core (κ η : ℕ) : ADec M → List (Finset V) → Prop
  | leaf _, _ => True
  | node l r π, Hs => l.Core κ η (childHoles Hs π.path.mverts) ∧
      r.Core κ η (childHoles Hs π.path.mverts) ∧
      Disjoint l.piece r.piece ∧ 0 < l.piece.card ∧ 0 < r.piece.card ∧
      π.Short κ η (l.piece ∪ r.piece).card ∧ nTouch M (l.piece ∪ r.piece) Hs ≤ η

/-- A balanced decomposition meets the conditions `Core`. -/
lemma Bal.core {κ η : ℕ} : ∀ {τ : ADec M} {Hs : List (Finset V)}, τ.Bal M κ η Hs → τ.Core M κ η Hs
  | leaf _, _, _ => trivial
  | node _ _ _, _, ⟨hl, hr, h1, h2, h3, _, _, h4, h6⟩ =>
    ⟨hl.core, hr.core, h1, h2, h3, h4, h6⟩

/-- In a decomposition meeting `Core`, every child has fewer darts than its parent, so the depth
is less than the number of darts. -/
lemma Core.depth_lt {κ η : ℕ} :
    ∀ {τ : ADec M} {Hs : List (Finset V)}, τ.Core M κ η Hs → 0 < τ.piece.card →
      τ.depth < τ.piece.card
  | leaf _, _, _, h => by simpa [depth] using h
  | node l r _, _, ⟨hl, hr, hlr, hl0, hr0, _⟩, _ => by
    have il := Core.depth_lt hl hl0
    have ir := Core.depth_lt hr hr0
    simp only [depth, piece, card_union_of_disjoint hlr]
    omega

lemma two_pow_mul_two_pow_half_le (d : ℕ) : 2 ^ d * 2 ^ (d / 2) ≤ 3 ^ d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d with
    | 0 => norm_num
    | 1 => norm_num
    | d + 2 =>
      have h := ih d (by omega)
      rw [show (d + 2) / 2 = d / 2 + 1 by omega]
      calc 2 ^ (d + 2) * 2 ^ (d / 2 + 1) = 8 * (2 ^ d * 2 ^ (d / 2)) := by ring
        _ ≤ 8 * 3 ^ d := Nat.mul_le_mul_left 8 h
        _ ≤ 9 * 3 ^ d := Nat.mul_le_mul_right _ (by norm_num)
        _ = 3 ^ (d + 2) := by ring

/-- **The depth of a balanced decomposition**: `(3/2)^depth ≤ n`. -/
theorem Bal.pow_depth {κ η : ℕ} :
    ∀ {τ : ADec M} {Hs : List (Finset V)}, τ.Bal M κ η Hs → 0 < τ.piece.card →
      3 ^ τ.depth ≤ 2 ^ τ.depth * τ.piece.card
  | leaf _, _, _, hpos => by simp only [depth, pow_zero, one_mul]; exact hpos
  | node l r _, _, h, _ => by
    obtain ⟨hl, hr, -, hl0, hr0, b0, b1, -⟩ := h
    have il := Bal.pow_depth hl hl0
    have ir := Bal.pow_depth hr hr0
    simp only [depth, piece] at il ir ⊢
    rcases le_total l.depth r.depth with hle | hle
    · rw [max_eq_right hle, pow_succ, pow_succ]
      nlinarith [Nat.zero_le (2 ^ r.depth)]
    · rw [max_eq_left hle, pow_succ, pow_succ]
      nlinarith [Nat.zero_le (2 ^ l.depth)]

/-- The depth of a balanced decomposition of `n` darts is at most `2 log₂ n + 1`. -/
theorem Bal.depth_le {κ η : ℕ} {τ : ADec M} {Hs : List (Finset V)} (h : τ.Bal M κ η Hs)
    (hpos : 0 < τ.piece.card) : τ.depth ≤ 2 * Nat.log 2 τ.piece.card + 1 := by
  have h1 := h.pow_depth hpos
  have h2 := two_pow_mul_two_pow_half_le τ.depth
  have h3 : 2 ^ (τ.depth / 2) ≤ τ.piece.card :=
    Nat.le_of_mul_le_mul_left (h2.trans h1) (by positivity)
  have := Nat.le_log_of_pow_le (by norm_num) h3
  omega

end ADec

/-- **The recurrence per depth**: every depth of the decomposition costs `O(n lg² n)` in the
recurrence of the article. -/
theorem pieceCost_le {c : SubCosts} {K K₀ κ η N : ℕ} (hc : c.Bounds K K₀) :
    ∀ {τ : ADec M} {Hs : List (Finset V)}, τ.Bal M κ η Hs → τ.piece.card ≤ N →
      pieceCost M c τ Hs ≤
        ((η + 1) * (14 + 5 * κ ^ 2 + 4 * η * (87 + 135 * κ ^ 2))) * K * lg N ^ 2 *
          (τ.piece.card * τ.depth) + K₀ * τ.piece.card
  | .leaf Q, _, _, _ => by
    simp only [pieceCost, ADec.piece, ADec.depth, mul_zero, zero_add]; exact hc.leaf _
  | .node l r π, Hs, h, hN => by
    obtain ⟨hl, hr, hlr, -, -, -, -, ⟨hlen, hk⟩, hη⟩ := h
    have hcard : (l.piece ∪ r.piece).card = l.piece.card + r.piece.card :=
      card_union_of_disjoint hlr
    simp only [ADec.piece] at hN
    have il := pieceCost_le hc hl (by omega : l.piece.card ≤ N)
    have ir := pieceCost_le hc hr (by omega : r.piece.card ≤ N)
    have hn := SubCosts.nodes_le hc (h := nTouch M (l.piece ∪ r.piece) Hs) (η := η)
      (π.segs.map SPath.k) (fun k hk' => by
        obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hk'
        exact ⟨(hk σ hσ).2, (hk σ hσ).1⟩) (by rw [List.length_map]; omega)
    rw [List.length_map] at hn
    have hn2 : c.nodes (l.piece ∪ r.piece).card (nTouch M (l.piece ∪ r.piece) Hs)
        (π.segs.map SPath.k) ≤ ((η + 1) * (14 + 5 * κ ^ 2 + 4 * η * (87 + 135 * κ ^ 2))) * K *
          (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card ^ 2 := by
      refine hn.trans ?_
      have := Nat.mul_le_mul_right ((14 + 5 * κ ^ 2 + 4 * η * (87 + 135 * κ ^ 2)) * K *
        (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card ^ 2) hlen
      calc _ ≤ _ := this
        _ = _ := by ring
    have hlg : lg (l.piece ∪ r.piece).card ^ 2 ≤ lg N ^ 2 :=
      Nat.pow_le_pow_left (lg_mono hN) 2
    generalize ((η + 1) * (14 + 5 * κ ^ 2 + 4 * η * (87 + 135 * κ ^ 2))) * K = B at il ir hn2 ⊢
    have hn' : c.nodes (l.piece ∪ r.piece).card (nTouch M (l.piece ∪ r.piece) Hs)
        (π.segs.map SPath.k) ≤ B * lg N ^ 2 * (l.piece ∪ r.piece).card := by
      calc _ ≤ B * (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card ^ 2 := hn2
        _ ≤ B * (l.piece ∪ r.piece).card * lg N ^ 2 := Nat.mul_le_mul_left _ hlg
        _ = _ := by ring
    simp only [pieceCost, ADec.piece, ADec.depth]
    rw [hcard] at hn' ⊢
    generalize B * lg N ^ 2 = A at il ir hn' ⊢
    have hw : l.piece.card * l.depth + r.piece.card * r.depth + (l.piece.card + r.piece.card) ≤
        (l.piece.card + r.piece.card) * (max l.depth r.depth + 1) := by
      nlinarith [Nat.mul_le_mul_left l.piece.card (le_max_left l.depth r.depth),
        Nat.mul_le_mul_left r.piece.card (le_max_right l.depth r.depth)]
    have := Nat.mul_le_mul_left A hw
    nlinarith

/-- **The recurrence of the article is `O(n log³ n)`** (the bound of Theorem 1.1 of the article): on
a balanced decomposition of a nonempty piece of `n` darts, it is at most `2 B K n lg³ n + K₀ n` with
`B = (η + 1) (14 + 5 κ² + 4 η (87 + 135 κ²))`. This bounds `pieceCost`, not the cost of `arun`
(`arunCost_le`). -/
theorem pieceCost_le_cube {c : SubCosts} {K K₀ κ η : ℕ} (hc : c.Bounds K K₀) {τ : ADec M}
    {Hs : List (Finset V)} (h : τ.Bal M κ η Hs) (hpos : 0 < τ.piece.card) :
    pieceCost M c τ Hs ≤ 2 * ((η + 1) * (14 + 5 * κ ^ 2 + 4 * η * (87 + 135 * κ ^ 2))) * K *
      τ.piece.card * lg τ.piece.card ^ 3 + K₀ * τ.piece.card := by
  have h1 := pieceCost_le hc h le_rfl
  have h2 : τ.depth ≤ 2 * lg τ.piece.card := by
    have := h.depth_le hpos; unfold lg; omega
  generalize hB : ((η + 1) * (14 + 5 * κ ^ 2 + 4 * η * (87 + 135 * κ ^ 2))) * K = B at h1
  have h3 : B * lg τ.piece.card ^ 2 * (τ.piece.card * τ.depth) ≤
      B * lg τ.piece.card ^ 2 * (τ.piece.card * (2 * lg τ.piece.card)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
  calc _ ≤ _ := h1
    _ ≤ B * lg τ.piece.card ^ 2 * (τ.piece.card * (2 * lg τ.piece.card)) +
        K₀ * τ.piece.card := Nat.add_le_add_right h3 _
    _ = _ := by rw [← hB]; ring

/-! ### The cost of `arun` -/

/-- The size of a map: its darts, vertices and faces. -/
def mapSize (_ : CombMap D V F) : ℕ := Fintype.card D + Fintype.card V + Fintype.card F

variable (M) in
/-- **The cost of `PlanarFlow.BKMNW.arun`**, every call charged at the size of the map it runs on
(the whole map `M`, see `SubCosts.leafRun` and `SubCosts.nodeRun`): `n` darts and `nf` faces for
the subroutines, `N = mapSize M` for the linear passes, for each part of the separator the `x`
faces along it and its `2 k` darts for the stages of FixConservationOnPath, the holes touching the
piece and the later parts for the calls of Section 4, and all the holes and the later parts for
the tests and their union (`SubCosts.nodeRuns`). -/
noncomputable def arunCost (c : SubCosts) : ADec M → List (Finset V) → ℕ
  | .leaf _, Hs => c.leafRun (Fintype.card D) (mapSize M) Hs.length
  | .node l r π, Hs =>
    arunCost c l (childHoles Hs π.path.mverts) + arunCost c r (childHoles Hs π.path.mverts) +
      c.nodeRuns (Fintype.card D) (Fintype.card F) (mapSize M) (nTouch M (l.piece ∪ r.piece) Hs)
        Hs.length (π.segs.map fun σ => (σ.faces.card, σ.k))

/-- The bound on one call of the recursion of `arun`: `B K N lg² N + K₀ N` with
`B = (η + 1) (27 + 7 κ² + 2 η (34 + 14 κ²))`. -/
def stepBound (K K₀ κ η N : ℕ) : ℕ :=
  (η + 1) * (27 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2)) * K * N * lg N ^ 2 + K₀ * N

lemma card_le_mapSize : Fintype.card D ≤ mapSize M := by unfold mapSize; omega

lemma card_face_le_mapSize : Fintype.card F ≤ mapSize M := by unfold mapSize; omega

/-- **Every call of the recursion of `arun` costs at most `stepBound`**, so the cost is at most
`2 m` times `stepBound` on a balanced decomposition of a piece of `m ≥ 1` darts, if the holes and
the depth together are at most `2 lg N`. -/
theorem arunCost_add_le {c : SubCosts} {K K₀ κ η : ℕ} (hc : c.Bounds K K₀) :
    ∀ {τ : ADec M} {Hs : List (Finset V)}, τ.Bal M κ η Hs → 0 < τ.piece.card →
      Hs.length + τ.depth ≤ 2 * lg (mapSize M) →
      arunCost M c τ Hs + stepBound K K₀ κ η (mapSize M) ≤
        2 * stepBound K K₀ κ η (mapSize M) * τ.piece.card
  | .leaf Q, Hs, _, hpos, hd => by
    simp only [ADec.depth, add_zero] at hd
    have h1 := SubCosts.leafRun_le hc (card_le_mapSize (M := M)) hd
    have h2 : 3 * K * mapSize M * lg (mapSize M) ^ 2 ≤
        (η + 1) * (27 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2)) * K * mapSize M *
          lg (mapSize M) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
        ((by omega : 3 ≤ 27 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2)).trans
          (Nat.le_mul_of_pos_left _ (by omega)))))
    have hL : c.leafRun (Fintype.card D) (mapSize M) Hs.length ≤
        stepBound K K₀ κ η (mapSize M) := h1.trans (by unfold stepBound; omega)
    simp only [ADec.piece] at hpos
    simp only [arunCost, ADec.piece]
    generalize stepBound K K₀ κ η (mapSize M) = W at hL ⊢
    nlinarith
  | .node l r π, Hs, h, _, hd => by
    obtain ⟨hl, hr, hlr, hl0, hr0, -, -, ⟨hlen, hk⟩, hη⟩ := h
    have hcard : (l.piece ∪ r.piece).card = l.piece.card + r.piece.card :=
      card_union_of_disjoint hlr
    have hm : (l.piece ∪ r.piece).card ≤ mapSize M :=
      (card_le_univ _).trans card_le_mapSize
    simp only [ADec.depth] at hd
    have hHl := length_childHoles Hs π.path.mverts
    have hdl : (childHoles Hs π.path.mverts).length + l.depth ≤ 2 * lg (mapSize M) := by
      have := le_max_left l.depth r.depth; omega
    have hdr : (childHoles Hs π.path.mverts).length + r.depth ≤ 2 * lg (mapSize M) := by
      have := le_max_right l.depth r.depth; omega
    have il := arunCost_add_le hc hl hl0 hdl
    have ir := arunCost_add_le hc hr hr0 hdr
    have hn := SubCosts.nodeRuns_le hc (h := nTouch M (l.piece ∪ r.piece) Hs) (a := Hs.length)
      (κ := κ) (η := η) (card_le_mapSize (M := M)) (card_face_le_mapSize (M := M))
      (π.segs.map fun σ => (σ.faces.card, σ.k)) (fun xk hxk => by
        obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hxk
        exact ⟨σ.card_faces_le, (hk σ hσ).2.trans hm,
          (hk σ hσ).1.trans (Nat.mul_le_mul_left _ hm)⟩)
      (by rw [List.length_map]; omega) (by rw [List.length_map]; omega)
    rw [List.length_map] at hn
    have hW : c.nodeRuns (Fintype.card D) (Fintype.card F) (mapSize M)
        (nTouch M (l.piece ∪ r.piece) Hs) Hs.length (π.segs.map fun σ => (σ.faces.card, σ.k)) ≤
        stepBound K K₀ κ η (mapSize M) := by
      refine hn.trans ?_
      have := Nat.mul_le_mul_right ((27 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2)) * K *
        mapSize M * lg (mapSize M) ^ 2) hlen
      unfold stepBound
      calc _ ≤ _ := this
        _ = (η + 1) * (27 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2)) * K * mapSize M *
            lg (mapSize M) ^ 2 := by ring
        _ ≤ _ := Nat.le_add_right _ _
    simp only [arunCost, ADec.piece]
    rw [hcard]
    generalize stepBound K K₀ κ η (mapSize M) = W at il ir hW ⊢
    nlinarith

/-- **The cost of `arun` is `O(n N lg² N)`** on a balanced decomposition of a piece of
`n ≥ 1` darts, `N = mapSize M`: at most `2 n` calls, each at most `stepBound`. -/
theorem arunCost_le {c : SubCosts} {K K₀ κ η : ℕ} (hc : c.Bounds K K₀) {τ : ADec M}
    (h : τ.Bal M κ η []) (hpos : 0 < τ.piece.card) :
    arunCost M c τ [] ≤ 2 * τ.piece.card * stepBound K K₀ κ η (mapSize M) := by
  have hd := h.depth_le hpos
  have hN : τ.piece.card ≤ mapSize M := (card_le_univ _).trans card_le_mapSize
  have hlog := Nat.log_mono_right (b := 2) hN
  have := arunCost_add_le hc h hpos (by simp only [List.length_nil, zero_add, lg]; omega)
  calc arunCost M c τ [] ≤ 2 * stepBound K K₀ κ η (mapSize M) * τ.piece.card := by omega
    _ = _ := by ring

end BKMNW

end PlanarFlow
