module

public import PlanarFlow.Klein.Trip
public import PlanarFlow.MSSP.Cost
public import PlanarFlow.BKMNW.Cost

/-!
# The cost allowances of the trip

The trip of Klein's algorithm (`PlanarFlow.Klein.IsTrip`) on the machine: Dijkstra's algorithm
from the first root (`PlanarFlow.MSSP.dijkCost`), then a run of the evertable link-cut tree
(`PlanarFlow.DynTree.lctE_run`: `140 (n + 1) + 21` steps for the initialisation of `n` nodes and
`311600 ⌊log₂ n⌋ + 42220` amortised steps per operation) on the `n ≤ 2 N` nodes of the vertices,
the faces and two copies of the edges (`N = #V + #F + #D`). The operations are counted with
the following allowances:

* `opsInit N = 8 N`: storing the initial tree and cotree (two links and two value settings per
  node);
* `opsPivot = 24` per pivot: the query `min2` and the parent of the printed node, the four
  additions along the two root paths of the cotree, the two cuts, the evert and the two links of
  the cotree, the two reads and settings of the values of the new edge node, and the two cuts,
  two settings and two links of the primal tree;
* `opsMove = 40` per move: the last query `min2`, the evert re-rooting the primal tree at the next
  source, and the reparenting of the next target (as a pivot);
* `opsWt = 8` per dart of the piece: the changes of the weights `tripWt` between two moves, on
  the darts of the piece leaving the two roots involved (each dart of the piece leaves one
  vertex, so it changes at most twice);
* one operation `sum` per distance query (`q = k²` for the distances between the `k` roots).

`tripCost_le`: **with at most `#S` pivots in total (`IsTrip.pivots`), the trip costs
`O(N log N + k² log N)`**, the form `K (m lg m + k² lg m)` of `PlanarFlow.BKMNW.SubCosts.Bounds`
when the number `k` of roots is of the order of the length of the path (see below for the cuts,
where it need not be).

**Status: no longer a counted cost.** The trip is a verified WordRAM program:
`PlanarFlow.Klein.klein_exec` (`PlanarFlow/Klein/ProgTrip.lean`) is an execution of
`kleinProg` (the evertable link-cut trees initialised, the initial trees stored, then the `k`
moves: the answers at the `t` requested target vertices, the pivot loop, the trees and the
weights of the next move), every executed step counted (the operations of the link-cut trees at
their amortised cost, `PlanarFlow.DynTree.lctE_adaptive_exec`), within
`140 (n + 1) + 21 + kleinOps · opCostE n + kleinExt` steps, which on `n = 2 N` nodes is at most
`36500000 (N lg N + k t lg N)` (`klein_steps_le`): `k t` path-sum queries, `k²` for the boundary
vertices as targets. **The answers are read out by the program**: at the end, for every move `j`
and target `X i`, the real word `OUT[j t + i]` and the natural reach bit `RB[j t + i]` give
(`kOut`) the distance in the piece from `tail (g j)` to `X i`, none when it is not reached
(`odist`; `klein_out_ans`: these are the answers `kleinAns`, from which `msspPlaneK` and
`PlanarFlow.Klein.srcAns` are built, `msspCutK_eq_out`, `PlanarFlow.Klein.src_exec`).

**The preconditions** of `klein_exec` (what the caller provides; their cost is not counted
there):

* the input describing the map, the boundary and the piece (`KInput`, `KBnd`, `KOut`: arrays of
  words, read in place), and the targets (`KTgt`: not roots, by their nodes, with their reach
  bits from the roots, copied by the program into `RB`);
* the initial spanning tree, compatible with the first move (the shortest-path tree from the
  first root, which Dijkstra's algorithm computes: the separate term `dijkCost` of `tripCost`
  above), and a cotree of it rooted at the face of `g 0`, with orders of their nodes and depth
  orders, in the input (`KInit`; they exist, `klein_init_exists`);
* in the real memory: the weights `tripWt 0` of the first move (from the reach bits of the first
  target), the weights `tripφ`, and the constants `tripL`, `tripL - 2 #V tripW` and `tripH0`
  (the machine has no conversion from naturals to reals; the maximum-flow algorithm computes
  these in real registers).

They can be met for every map, boundary, piece and lengths meeting the hypotheses of the trip
(`klein_exec_pre`, `PlanarFlow/Klein/ProgExists.lean`); `klein_exec_exists` is the resulting
end-to-end statement.

**The roots of the cuts.** In `tripCost_le` and `klein_steps_le`, `k` is the number of roots of
the trip. On the cut along a simple path of `p` darts on which the maximum-flow algorithm calls
multiple-source shortest paths (`PlanarFlow/BKMNW/CutBuild.lean`) there is one root per dart
leaving the path, so `k` can be of the order of `N`, not of `p`: the unmasked program
`kleinProg`, answering all `k` roots at the `O(p)` faces along the path, costs `O(N p log N)`,
which is not the form `K (m lg m + p² lg m)` of `PlanarFlow.BKMNW.SubCosts.Bounds.mssp` (with
`p` the length of the path). The masked program `kleinProgM`
(`PlanarFlow/Klein/ProgTripMask.lean`) answers only flagged moves, within
`36500000 (N lg N + f t lg N)` steps for `f` flagged moves and `t` targets
(`kleinM_exec`, `kleinM_steps_le`, `kleinM_exec_exists`); with the first move of each face along
the path flagged (`cutFlag`, at most `2 p` of them) its output holds `msspPlaneK` at every pair of
faces along the path, within `1642500000 (N lg N + p² lg N)` steps (`msspPlaneK_masked`,
`PlanarFlow/Klein/ProgExistsMask.lean`).

The allowances above (`tripOps`) are kept for the existing statements; they also bound the list
of operations of the trip on the stored data (`klein_trip_cost`, `PlanarFlow/Klein/LCTTrip.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset BKMNW

/-- Operations to store the initial trees, per vertex, face and dart. -/
def opsInit (N : ℕ) : ℕ := 8 * N

/-- Operations per pivot. -/
def opsPivot : ℕ := 24

/-- Operations per move. -/
def opsMove : ℕ := 40

/-- Operations per dart of the piece for the changes of the weights. -/
def opsWt : ℕ := 8

/-- The operations of a trip with `N` vertices, faces and darts, `s` darts in the piece, `k`
moves, `p` pivots and `q` distance queries. -/
def tripOps (N s k p q : ℕ) : ℕ := opsInit N + opsPivot * p + opsMove * k + opsWt * s + q

/-- **The counted cost of a trip**: Dijkstra's algorithm on `nV` vertices and `nD` arcs, and the
link-cut tree on `2 N` nodes running `tripOps` operations. -/
def tripCost (nV nD N s k p q : ℕ) : ℕ :=
  MSSP.dijkCost nV nD + (140 * (2 * N + 1) + 21 +
    tripOps N s k p q * (311600 * Nat.log 2 (2 * N) + 42220))

/-- **The counted cost is `O(N log N + k² log N)`.** -/
theorem tripCost_le {nV nD N s k p : ℕ} (hN : 1 ≤ N) (hV : nV ≤ N) (hD : nD ≤ N)
    (hs : s ≤ N) (hk : k ≤ N) (hp : p ≤ s) :
    tripCost nV nD N s k p (k ^ 2) ≤ 28400000 * (N * lg N + k ^ 2 * lg N) := by
  have hl1 : 1 ≤ lg N := one_le_lg N
  have hlog2 : Nat.log 2 (2 * N) = lg N := by
    unfold lg
    rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
  have hlogV : Nat.log 2 nV ≤ Nat.log 2 N := Nat.log_mono_right hV
  have hlogN : Nat.log 2 N + 1 = lg N := rfl
  have hops : tripOps N s k p (k ^ 2) ≤ 80 * N + k ^ 2 := by
    unfold tripOps opsInit opsPivot opsMove opsWt; omega
  have hdij : MSSP.dijkCost nV nD ≤ 3 * N * (179 * lg N) := by
    unfold MSSP.dijkCost
    have h1 : nV + nD + 1 ≤ 2 * N + 1 := by omega
    have h2 : 36 * Nat.log 2 nV + 143 ≤ 179 * lg N := by omega
    calc (nV + nD + 1) * (36 * Nat.log 2 nV + 143) ≤ (2 * N + 1) * (179 * lg N) :=
          Nat.mul_le_mul h1 h2
      _ ≤ 3 * N * (179 * lg N) := Nat.mul_le_mul_right _ (by omega)
  unfold tripCost
  rw [hlog2]
  have hper : 311600 * lg N + 42220 ≤ 353820 * lg N := by omega
  have hrun : tripOps N s k p (k ^ 2) * (311600 * lg N + 42220) ≤
      (80 * N + k ^ 2) * (353820 * lg N) := Nat.mul_le_mul hops hper
  have hinit : 140 * (2 * N + 1) + 21 ≤ 450 * N * lg N := by nlinarith
  nlinarith

section Trip

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

/-- The number of roots is at most the number of vertices. -/
lemma _root_.PlanarFlow.MSSP.Hyp.k_le_card (H : MSSP.Hyp M k g S ℓ) : k ≤ Fintype.card V := by
  have hinj : Function.Injective fun i : Fin k => M.tail (g i) := fun i j h =>
    Fin.ext (H.face.inj _ i.2 _ j.2 h)
  simpa using Fintype.card_le_of_injective _ hinj

/-- **The counted cost of a trip around the face is `O(N log N + k² log N)`** with `N` the
number of vertices, faces and darts, the `k²` distance queries included: the pivot bound
`IsTrip.pivots`. -/
theorem IsTrip.cost_le (H : MSSP.Hyp M k g S ℓ) (hR : SameReach M k g S ℓ)
    {R : ℕ → MoveData M S} (hT : IsTrip M k g S ℓ R) :
    tripCost (Fintype.card V) (Fintype.card D)
        (Fintype.card V + Fintype.card F + Fintype.card D) S.card k
        (∑ j ∈ range k, (R j).m) (k ^ 2) ≤
      28400000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        k ^ 2 * lg (Fintype.card V + Fintype.card F + Fintype.card D)) := by
  have hk := H.k_le_card
  have h2 := H.face.two_le
  have hS : S.card ≤ Fintype.card D := card_le_univ S
  exact tripCost_le (by omega) (by omega) (by omega) (by omega) (by omega) (hT.pivots H hR)

end Trip

end Klein

end PlanarFlow
