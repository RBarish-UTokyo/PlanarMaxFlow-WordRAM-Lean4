module

public import PlanarFlow.Monge.Meet

/-!
# FR-Dijkstra: the mathematics

FR-Dijkstra (Fakcharoenphol and Rao) computes the distances from a root `r` in a union of dense
distance graphs and explicit arcs, given a feasible potential `p` (a *price function*: the reduced
lengths `ℓ a + p (src a) - p (dst a)` are nonnegative). It is Dijkstra's algorithm in which the
vertices are *settled* one at a time, each time a vertex minimizing the reduced key over the arcs
leaving the settled vertices. The Monge structure of the dense distance graphs is only used to
find that vertex quickly; for correctness, any procedure that settles vertices in this way
computes the distances. This file proves both halves of the mathematics:

* **Correctness of Dijkstra with a price function** (`DijkRun`, `DijkRun.gdist`): a run is a
  sequence `v 0 = r, v 1, …, v (K - 1)` of distinct vertices with values `d k`, each reached by an
  arc from an earlier one (`parent`), minimizing the reduced key among the arcs leaving the
  earlier vertices to the later ones (`least`), and such that no arc leaves the settled set at the
  end (`closed`). Then `d k` is the distance from `r` to `v k`, and the vertices never settled
  are unreachable: the distances are `GDist`, the bridge-friendly specification of
  `PlanarFlow.Monge.Meet` (`δ y = some ℓ` for a least walk length `ℓ`, `none` if unreachable).
  The reduced values `d k - p (v k)` are nondecreasing (`DijkRun.mono`), which gives the lower
  bound by induction along a walk (`DijkRun.le_walkLen`).
* **The invariant of the Monge heap** (`IsTotMono.beats_interval`): in a totally monotone
  matrix whose rows are the targets and whose columns are the sources of a block (entry
  `d i + D i t`), the targets where a new source beats every source of a set `S` form an
  interval. Hence the targets of a block are partitioned into intervals, one for each active
  source, ordered like the sources (`IsTotMono.lmin_mono` for the columns of the active sources);
  activating a source replaces an interval of this partition, and the minimum over the block is
  the minimum, over the intervals, of a range minimum of a row. This is the bipartite Monge heap
  of Fakcharoenphol and Rao (in the form of Gawrychowski and Karczmarz, §3).

## References

* J. Fakcharoenphol, S. Rao, *Planar graphs, negative weight edges, shortest paths, and near
  linear time*, J. Comput. Syst. Sci. 72 (2006), 868–889, §3.
* P. Gawrychowski, A. Karczmarz, *Improved bounds for shortest paths in dense distance graphs*,
  ICALP 2018, §3.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open Finset

/-! ### Dijkstra with a price function -/

section Dijkstra

variable {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A] {G : Digraph X A}

/-- A walk of `m + 1` arcs is a walk of `m` arcs followed by the arc `c m`. -/
lemma GWalk.snoc {x y : X} {m : ℕ} {c : ℕ → A} (h : GWalk G x y (m + 1) c) :
    GWalk G x (G.src (c m)) m c ∧ G.dst (c m) = y := by
  rcases h with ⟨h, -⟩ | ⟨-, h0, hz, hs⟩
  · omega
  · refine ⟨?_, by simpa using hz⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl ⟨rfl, h0.symm⟩
    · refine Or.inr ⟨hm, h0, ?_, fun t ht => hs t (by omega)⟩
      have := hs (m - 1) (by omega)
      rwa [show m - 1 + 1 = m by omega] at this

lemma walkLen_succ (m : ℕ) (c : ℕ → A) : G.walkLen (m + 1) c = G.walkLen m c + G.len (c m) := by
  unfold Digraph.walkLen; rw [sum_range_succ]

/-- **A run of Dijkstra's algorithm with the price function `p`** from `r`: the settled vertices
`v 0 = r, …, v (K - 1)` with their values `d`. -/
structure DijkRun (G : Digraph X A) (p : X → ℤ) (r : X) (K : ℕ) (v : ℕ → X) (d : ℕ → ℤ) :
    Prop where
  pos : 0 < K
  root : v 0 = r
  root_d : d 0 = 0
  inj : ∀ i j, i < K → j < K → v i = v j → i = j
  parent : ∀ k, 0 < k → k < K → ∃ i < k, ∃ a, G.src a = v i ∧ G.dst a = v k ∧
    d k = d i + G.len a
  least : ∀ k < K, ∀ i < k, ∀ a, G.src a = v i → (∀ j < k, G.dst a ≠ v j) →
    d k - p (v k) ≤ d i + G.len a - p (G.dst a)
  closed : ∀ i < K, ∀ a, G.src a = v i → ∃ j < K, G.dst a = v j

variable {p : X → ℤ} {r : X} {K : ℕ} {v : ℕ → X} {d : ℕ → ℤ}

/-- **The reduced values of the settled vertices are nondecreasing.** -/
theorem DijkRun.mono_succ (h : DijkRun G p r K v d) (hp : G.IsPot p) {k : ℕ} (hk : k + 1 < K) :
    d k - p (v k) ≤ d (k + 1) - p (v (k + 1)) := by
  obtain ⟨i, hi, a, hs, hd, he⟩ := h.parent (k + 1) (by omega) hk
  have hpa := hp a
  rw [hs, hd] at hpa
  rcases Nat.lt_or_ge i k with hik | hik
  · have := h.least k (by omega) i hik a hs (fun j hj e => by
      rw [hd] at e; have := h.inj _ _ hk (by omega) e; omega)
    rw [hd] at this; omega
  · rw [show i = k by omega] at he hpa; omega

theorem DijkRun.mono (h : DijkRun G p r K v d) (hp : G.IsPot p) {j k : ℕ} (hjk : j ≤ k)
    (hk : k < K) : d j - p (v j) ≤ d k - p (v k) := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact (ih (by omega)).trans (h.mono_succ hp hk)

/-- **The lower bound**: every walk from the root ends at a settled vertex, whose value is at most
the length of the walk. -/
theorem DijkRun.le_walkLen (h : DijkRun G p r K v d) (hp : G.IsPot p) :
    ∀ (m : ℕ) {y : X} {c : ℕ → A}, GWalk G r y m c → ∃ j < K, v j = y ∧ d j ≤ G.walkLen m c := by
  intro m
  induction m with
  | zero =>
    intro y c hw
    rcases hw with ⟨-, rfl⟩ | ⟨h0, -⟩
    · exact ⟨0, h.pos, h.root, by rw [h.root_d]; simp [Digraph.walkLen]⟩
    · omega
  | succ m ih =>
    intro y c hw
    obtain ⟨hw', hy⟩ := hw.snoc
    obtain ⟨i, hi, hvi, hdi⟩ := ih hw'
    obtain ⟨j, hj, hvj⟩ := h.closed i hi (c m) hvi.symm
    refine ⟨j, hj, by rw [← hvj, hy], ?_⟩
    rw [walkLen_succ]
    have hpa := hp (c m)
    rw [← hvi, hvj] at hpa
    rcases Nat.lt_or_ge i j with hij | hij
    · have := h.least j hj i hij (c m) hvi.symm (fun j' hj' e => by
        rw [hvj] at e; have := h.inj _ _ hj (by omega) e; omega)
      rw [hvj] at this; omega
    · have := h.mono hp hij hi
      omega

/-- **The upper bound**: the value of a settled vertex is the length of a walk from the root. -/
theorem DijkRun.walk [Nonempty A] (h : DijkRun G p r K v d) :
    ∀ k < K, ∃ m c, GWalk G r (v k) m c ∧ G.walkLen m c = d k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨0, fun _ => Classical.arbitrary A, Or.inl ⟨rfl, h.root.symm⟩, by
        rw [h.root_d]; simp [Digraph.walkLen]⟩
    · obtain ⟨i, hi, a, hs, hd, he⟩ := h.parent k hk0 hk
      obtain ⟨m, c, hw, hl⟩ := ih i hi (by omega)
      have ha : GWalk G (v i) (v k) 1 (fun _ => a) :=
        Or.inr ⟨by omega, hs, hd, fun t ht => by omega⟩
      refine ⟨m + 1, _, isWalk_append hw ha, ?_⟩
      have e1 : G.walkLen m (fun t => if t < m then c t else a) = G.walkLen m c := by
        unfold Digraph.walkLen
        exact sum_congr rfl fun t ht => by beta_reduce; rw [ite_eq_left (mem_range.1 ht)]
      rw [walkLen_succ, e1, hl, he, ite_eq_right (lt_irrefl m)]

/-- **Correctness of Dijkstra with a price function.** The values of a run are the distances
from the root: `δ y = some (d k)` for the settled vertex `y = v k`, and `δ y = none` (no walk)
for the other vertices. -/
theorem DijkRun.gdist [Nonempty A] (h : DijkRun G p r K v d) (hp : G.IsPot p) :
    GDist G r
      (fun y => if hy : ∃ k < K, v k = y then some (d (Classical.choose hy)) else none) := by
  refine ⟨fun y ℓ hδ => ?_, fun y ℓ hδ m c hw => ?_, fun y hδ m c hw => ?_⟩
  · split_ifs at hδ with hy
    obtain ⟨hk, hvk⟩ := Classical.choose_spec hy
    obtain ⟨m, c, hw, hl⟩ := h.walk _ hk
    rw [hvk] at hw
    exact ⟨m, c, hw, by rw [hl]; exact Option.some_inj.1 hδ⟩
  · split_ifs at hδ with hy
    obtain ⟨hk, hvk⟩ := Classical.choose_spec hy
    obtain ⟨j, hj, hvj, hdj⟩ := h.le_walkLen hp m hw
    have := h.inj _ _ hj hk (hvj.trans hvk.symm)
    rw [← Option.some_inj.1 hδ, ← this]; exact hdj
  · split_ifs at hδ with hy
    obtain ⟨j, hj, hvj, -⟩ := h.le_walkLen hp m hw
    exact hy ⟨j, hj, hvj⟩

end Dijkstra

/-! ### The invariant of the Monge heap -/

section MongeHeap

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- **The targets where a new source beats a set of sources form an interval.** In a totally
monotone matrix `M` (rows: the targets, columns: the sources), if the column `j` is strictly
better than every column of `S` in the rows `t₁ ≤ t₃`, it is so in every row between them. -/
theorem IsTotMono.beats_interval {mR nC : ℕ} {M : ℕ → ℕ → α} (hM : IsTotMono mR nC M)
    {S : ℕ → Prop} {j : ℕ} (hS : ∀ i, S i → i < nC ∧ i ≠ j) (hj : j < nC) {t₁ t₂ t₃ : ℕ}
    (h12 : t₁ ≤ t₂) (h23 : t₂ ≤ t₃) (ht₃ : t₃ < mR) (b₁ : ∀ i, S i → M t₁ j < M t₁ i)
    (b₃ : ∀ i, S i → M t₃ j < M t₃ i) : ∀ i, S i → M t₂ j < M t₂ i := by
  intro i hi
  obtain ⟨hin, hij⟩ := hS i hi
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · -- an earlier source: the rows where `j` wins are upward closed
    rcases Nat.eq_or_lt_of_le h12 with e | h12'
    · rw [← e]; exact b₁ i hi
    · exact (hM t₁ t₂ i j h12' (by omega) hlt hj).1 (b₁ i hi)
  · -- a later source: the rows where `j` wins are downward closed
    rcases Nat.eq_or_lt_of_le h23 with e | h23'
    · rw [e]; exact b₃ i hi
    · by_contra hcon
      rw [not_lt] at hcon
      exact absurd (b₃ i hi) (not_lt.2 ((hM t₂ t₃ j i h23' ht₃ hgt hin).2 hcon))

end MongeHeap

/-! ### The input of FR-Dijkstra -/

section Input

variable {X : Type*}

/-- **One dense distance graph and explicit arcs**: the vertices `β 0, …, β (b - 1)` of a face
(in its cyclic order) with the lengths `D i j` between them, and the explicit arcs `Ex` (source,
target, length). This is the input of FR-Dijkstra in the algorithm of Borradaile, Klein, Mozes,
Nussbaum and Wulff-Nilsen. -/
def ddgPlus (β : ℕ → X) (b : ℕ) (D : ℕ → ℕ → ℤ) (Ex : List (X × X × ℤ)) :
    Digraph X (Arc b ⊕ Fin Ex.length) where
  src
    | .inl a => β a.1.1
    | .inr e => (Ex.get e).1
  dst
    | .inl a => β a.1.2
    | .inr e => (Ex.get e).2.1
  len
    | .inl a => D a.1.1 a.1.2
    | .inr e => (Ex.get e).2.2

/-- **The specification of FR-Dijkstra**: given one dense distance graph and explicit arcs (at
least one arc, so that walks, which are functions `ℕ → A`, exist), a root and a feasible potential
of their union (the price function), the distances from the root in the union. -/
def FRDijkSpec [Fintype X] [DecidableEq X]
    (fr : (ℕ → X) → (b : ℕ) → (ℕ → ℕ → ℤ) → List (X × X × ℤ) → X → (X → ℤ) → X → Option ℤ) :
    Prop :=
  ∀ β b D Ex r p, Nonempty (Arc b ⊕ Fin Ex.length) → (ddgPlus β b D Ex).IsPot p →
    GDist (ddgPlus β b D Ex) r (fr β b D Ex r p)

/-- **Every run of Dijkstra with the price function meets the specification**: an implementation
of FR-Dijkstra only has to settle the vertices in the order of `DijkRun` (the Monge heaps find
the minimum reduced key over the arcs of the dense distance graph). -/
theorem frDijkSpec_of_run [Fintype X] [DecidableEq X]
    (fr : (ℕ → X) → (b : ℕ) → (ℕ → ℕ → ℤ) → List (X × X × ℤ) → X → (X → ℤ) → X → Option ℤ)
    (hrun : ∀ β b D Ex r p, (ddgPlus β b D Ex).IsPot p →
      ∃ K v d, DijkRun (ddgPlus β b D Ex) p r K v d ∧
        fr β b D Ex r p = fun y => if hy : ∃ k < K, v k = y then some (d (Classical.choose hy))
          else none) :
    FRDijkSpec fr := by
  intro β b D Ex r p hE hp
  obtain ⟨K, v, d, hR, hf⟩ := hrun β b D Ex r p hp
  rw [hf]
  exact hR.gdist hp

end Input

end Monge

end PlanarFlow
