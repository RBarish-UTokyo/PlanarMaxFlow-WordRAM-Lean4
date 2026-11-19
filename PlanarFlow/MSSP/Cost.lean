module

public import PlanarFlow.Dijkstra.Run
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The counted cost of the divide-and-conquer

The preprocessing of Das, Kipouridis, Probst Gutenberg and Wulff-Nilsen (SOSA 2022, Algorithm 1)
is a recursion on intervals `[i₁, i₂]` of roots: at every node it runs three single-source
shortest path computations in the contracted graph of the node and builds the contracted graphs
of its two children; it splits `[i₁, i₂]` at `(i₁ + i₂) / 2` while `i₁ + 1 < i₂`.

* `level h i₁ i₂`: the intervals of the recursion at depth `h`; `recCost c i₁ i₂`: the total cost
  when the node `I` costs `c I`.
* `recCost_eq_sum`: the total cost is the sum over the `⌈log₂ (i₂ - i₁)⌉ + 1` levels of the
  costs of their nodes; `recCost_le`: a bound `B` on every level gives
  `(⌈log₂ (i₂ - i₁)⌉ + 1) · B`.
* `dijkCost`: the step bound `(n + m + 1) (36 log₂ n + 143)` of Dijkstra's algorithm with a binary
  heap on the machine (`PlanarFlow.Dijk.dijkstra_runsWithin`, restated as
  `dijkstra_runsWithin_dijkCost`).
* `prep_cost_le`: **the preprocessing bound**. If the contracted graph of the node `I` has `n I`
  vertices and `m I` arcs, with `n I ≤ N`, the work at a node besides the three runs of Dijkstra is
  at most `κ (n I + m I + 1)`, and the graphs of every level have at most `K N` vertices and arcs
  in total (`Σ (n I + m I + 1) ≤ K N`, the article's Lemma 5.8 with the sparsity of plane graphs),
  then the preprocessing costs at most
  `(⌈log₂ (k - 1)⌉ + 1) · K N · (108 log₂ N + 429 + κ)`,
  that is `O(N log N log k)` with a binary heap, for `k` roots on the face.

The per-level bound is a hypothesis here: it is the article's Lemma 5.8 (every arc lies in the
shortest path trees of `O(1)` nodes per level, by planarity) combined with the sparsity of the
contracted graphs (simple plane graphs, parallel arcs merged).
-/

@[expose] public section

namespace PlanarFlow

namespace MSSP

open Finset

/-- The intervals of the recursion at depth `h` below `[i₁, i₂]`. -/
def level : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, i₁, i₂ => [(i₁, i₂)]
  | h + 1, i₁, i₂ =>
    if i₁ + 1 < i₂ then level h i₁ ((i₁ + i₂) / 2) ++ level h ((i₁ + i₂) / 2) i₂ else []

/-- The total cost of the recursion on `[i₁, i₂]` when the node `[a, b]` costs `c a b`. -/
def recCost (c : ℕ → ℕ → ℕ) (i₁ i₂ : ℕ) : ℕ :=
  c i₁ i₂ +
    if i₁ + 1 < i₂ then recCost c i₁ ((i₁ + i₂) / 2) + recCost c ((i₁ + i₂) / 2) i₂ else 0
termination_by i₂ - i₁
decreasing_by all_goals omega

/-- The cost of the nodes of a level. -/
def levelCost (c : ℕ → ℕ → ℕ) (h i₁ i₂ : ℕ) : ℕ := ((level h i₁ i₂).map fun I => c I.1 I.2).sum

lemma levelCost_zero (c : ℕ → ℕ → ℕ) (i₁ i₂ : ℕ) : levelCost c 0 i₁ i₂ = c i₁ i₂ := by
  simp [levelCost, level]

lemma levelCost_succ (c : ℕ → ℕ → ℕ) (h i₁ i₂ : ℕ) : levelCost c (h + 1) i₁ i₂ =
    if i₁ + 1 < i₂ then levelCost c h i₁ ((i₁ + i₂) / 2) + levelCost c h ((i₁ + i₂) / 2) i₂
    else 0 := by
  unfold levelCost
  rw [level]
  split_ifs <;> simp

/-- **The cost of the recursion is the sum of the costs of its levels**, for any number of levels
at least `⌈log₂ (i₂ - i₁)⌉ + 1`. -/
theorem recCost_eq_sum (c : ℕ → ℕ → ℕ) : ∀ i₁ i₂ L, Nat.clog 2 (i₂ - i₁) + 1 ≤ L →
    recCost c i₁ i₂ = ∑ h ∈ range L, levelCost c h i₁ i₂ := by
  intro i₁ i₂
  induction hw : i₂ - i₁ using Nat.strong_induction_on generalizing i₁ i₂ with
  | _ w ih =>
    intro L hL
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [recCost, sum_range_succ', levelCost_zero]
    simp only [levelCost_succ]
    split_ifs with hs
    · have hc : Nat.clog 2 w = Nat.clog 2 ((w + 1) / 2) + 1 :=
        Nat.clog_of_two_le (by norm_num) (by omega)
      have h1 := Nat.clog_mono_right 2 (show (i₁ + i₂) / 2 - i₁ ≤ (w + 1) / 2 by omega)
      have h2 := Nat.clog_mono_right 2 (show i₂ - (i₁ + i₂) / 2 ≤ (w + 1) / 2 by omega)
      rw [ih _ (by omega) i₁ ((i₁ + i₂) / 2) rfl L (by omega),
        ih _ (by omega) ((i₁ + i₂) / 2) i₂ rfl L (by omega), ← sum_add_distrib]
      ring
    · simp

/-- **A bound on every level bounds the recursion.** -/
theorem recCost_le (c : ℕ → ℕ → ℕ) {i₁ i₂ B : ℕ} (hB : ∀ h, levelCost c h i₁ i₂ ≤ B) :
    recCost c i₁ i₂ ≤ (Nat.clog 2 (i₂ - i₁) + 1) * B := by
  rw [recCost_eq_sum c i₁ i₂ _ le_rfl]
  calc ∑ h ∈ range (Nat.clog 2 (i₂ - i₁) + 1), levelCost c h i₁ i₂
      ≤ ∑ _h ∈ range (Nat.clog 2 (i₂ - i₁) + 1), B := sum_le_sum fun h _ => hB h
    _ = _ := by simp

/-- The step bound of Dijkstra's algorithm with a binary heap on the machine, for `n` vertices and
`m` arcs. -/
def dijkCost (n m : ℕ) : ℕ := (n + m + 1) * (36 * Nat.log 2 n + 143)

/-- `PlanarFlow.Dijk.dijkstra_runsWithin` in terms of `dijkCost`. -/
theorem dijkstra_runsWithin_dijkCost {d : List ℕ} {W : ℕ} (he : Dijk.DEnc d W) :
    ∃ D : ℕ → ℕ, (∀ v < Dijk.nn d, D v ≤ Dijk.inf d ∧ (D v < Dijk.inf d → Dijk.Reach d v (D v)) ∧
        ∀ ℓ, Dijk.Reach d v ℓ → D v ≤ ℓ) ∧
      WordRAM.RunsWithin (WordRAM.Machine.Stmt.compile Dijk.prog 0 ++ [WordRAM.Instr.halt])
        (Dijk.inp d) W (dijkCost (Dijk.nn d) (Dijk.mm d)) ((List.range (Dijk.nn d)).map D) :=
  Dijk.dijkstra_runsWithin he

/-- The cost of a node: three runs of Dijkstra's algorithm and `κ` steps per vertex and arc for
building the contracted graphs of the children. -/
def nodeCost (κ : ℕ) (n m : ℕ → ℕ → ℕ) (a b : ℕ) : ℕ :=
  3 * dijkCost (n a b) (m a b) + κ * (n a b + m a b + 1)

/-- **The preprocessing bound**: with at most `N` vertices in every contracted graph and at most
`K N` vertices and arcs on every level (the article's Lemma 5.8), the recursion on the `k` roots
`[0, k - 1]` costs at most `(⌈log₂ (k - 1)⌉ + 1) · K N · (108 log₂ N + 429 + κ)`. -/
theorem prep_cost_le {κ K N k : ℕ} {n m : ℕ → ℕ → ℕ} (hn : ∀ a b, n a b ≤ N)
    (hlev : ∀ h, ((level h 0 (k - 1)).map fun I => n I.1 I.2 + m I.1 I.2 + 1).sum ≤ K * N) :
    recCost (nodeCost κ n m) 0 (k - 1) ≤
      (Nat.clog 2 (k - 1) + 1) * (K * N * (108 * Nat.log 2 N + 429 + κ)) := by
  have hnode : ∀ a b, nodeCost κ n m a b ≤
      (n a b + m a b + 1) * (108 * Nat.log 2 N + 429 + κ) := by
    intro a b
    have := Nat.log_mono_right (b := 2) (hn a b)
    unfold nodeCost dijkCost
    generalize Nat.log 2 (n a b) = x at *
    generalize Nat.log 2 N = y at *
    generalize n a b + m a b + 1 = s
    nlinarith
  have := recCost_le (nodeCost κ n m) (i₁ := 0) (i₂ := k - 1)
    (B := K * N * (108 * Nat.log 2 N + 429 + κ)) (fun h => ?_)
  · simpa using this
  unfold levelCost
  calc ((level h 0 (k - 1)).map fun I => nodeCost κ n m I.1 I.2).sum
      ≤ ((level h 0 (k - 1)).map fun I =>
          (n I.1 I.2 + m I.1 I.2 + 1) * (108 * Nat.log 2 N + 429 + κ)).sum :=
        List.sum_le_sum fun I _ => hnode I.1 I.2
    _ = ((level h 0 (k - 1)).map fun I => n I.1 I.2 + m I.1 I.2 + 1).sum *
          (108 * Nat.log 2 N + 429 + κ) := by rw [List.sum_map_mul_right]
    _ ≤ _ := Nat.mul_le_mul_right _ (hlev h)

end MSSP

end PlanarFlow
