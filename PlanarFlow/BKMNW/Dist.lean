module

public import PlanarFlow.ShortestPath.BellmanFord
public import Mathlib.Data.Int.LeastGreatest

/-!
# Walks and shortest-path distances

Walks are lists of arcs, and distances are the least lengths of walks. These are the objects in
which the specifications of the shortest-path subroutines used by the algorithm of Borradaile,
Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J. Comput. 46(4), 2017) are stated: multiple-source
shortest paths, FR-Dijkstra on dense distance graphs, and Dijkstra's algorithm in the dual
(`PlanarFlow/BKMNW/DDG.lean`, `PlanarFlow/BKMNW/Hassin.lean`).

* `IsWalk G x l y`: the list of arcs `l` is a walk from `x` to `y`; `wlen G l` its length.
* `IsDist G r δ`: `δ y = some ℓ` when `ℓ` is the least length of a walk from `r` to `y`, and
  `δ y = none` when there is no walk from `r` to `y`.
* `exists_isDist`: **distances exist** when the lengths admit a feasible potential (for instance
  when they are nonnegative); `IsDist.unique`: they are unique.
* `IsDist.self`, `IsDist.le_arc`, `IsDist.isPot`: the distances from the root vanish at the root,
  satisfy the triangle inequality along every arc, and form a feasible potential when every vertex
  is reachable.
* `isDist_addPot`: changing the lengths by a potential (`len a + p (dst a) - p (src a)`) shifts
  the distances by `p y - p r` (the telescoping identity behind reduced lengths and price
  functions).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset

variable {X A : Type*}

/-! ### Walks -/

/-- `l` is a walk from `x` to `y`: consecutive arcs, the first leaving `x`, the last entering
`y` (the empty walk when `x = y`). -/
def IsWalk (G : Digraph X A) : X → List A → X → Prop
  | x, [], y => x = y
  | x, a :: l, y => G.src a = x ∧ IsWalk G (G.dst a) l y

/-- The length of a list of arcs. -/
def wlen (G : Digraph X A) (l : List A) : ℤ := (l.map G.len).sum

variable {G : Digraph X A}

@[simp] lemma isWalk_nil {x y : X} : IsWalk G x [] y ↔ x = y := Iff.rfl

@[simp] lemma isWalk_cons {x y : X} {a : A} {l : List A} :
    IsWalk G x (a :: l) y ↔ G.src a = x ∧ IsWalk G (G.dst a) l y := Iff.rfl

@[simp] lemma wlen_nil : wlen G [] = 0 := rfl

@[simp] lemma wlen_cons (a : A) (l : List A) : wlen G (a :: l) = G.len a + wlen G l := by
  simp [wlen]

lemma wlen_append (l l' : List A) : wlen G (l ++ l') = wlen G l + wlen G l' := by
  simp [wlen]

lemma isWalk_append_iff {x z : X} {l l' : List A} :
    IsWalk G x (l ++ l') z ↔ ∃ y, IsWalk G x l y ∧ IsWalk G y l' z := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih =>
    simp only [List.cons_append, isWalk_cons, ih]
    constructor
    · rintro ⟨h1, y, h2, h3⟩; exact ⟨y, ⟨h1, h2⟩, h3⟩
    · rintro ⟨y, ⟨h1, h2⟩, h3⟩; exact ⟨h1, y, h2, h3⟩

lemma IsWalk.append {x y z : X} {l l' : List A} (h : IsWalk G x l y) (h' : IsWalk G y l' z) :
    IsWalk G x (l ++ l') z := isWalk_append_iff.2 ⟨y, h, h'⟩

lemma isWalk_singleton {x y : X} {a : A} : IsWalk G x [a] y ↔ G.src a = x ∧ G.dst a = y := by
  simp [eq_comm]

/-- **Telescoping** along a walk. -/
lemma IsWalk.sum_sub (p : X → ℤ) {x y : X} {l : List A} (h : IsWalk G x l y) :
    (l.map fun a => p (G.dst a) - p (G.src a)).sum = p y - p x := by
  induction l generalizing x with
  | nil => simp only [isWalk_nil] at h; subst h; simp
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := h
    simp only [List.map_cons, List.sum_cons, ih h2, h1]; ring

/-- A feasible potential bounds the lengths of walks from below. -/
lemma IsWalk.le_wlen {p : X → ℤ} (hp : G.IsPot p) {x y : X} {l : List A} (h : IsWalk G x l y) :
    p y - p x ≤ wlen G l := by
  rw [← h.sum_sub p, wlen]
  exact List.sum_le_sum fun a _ => by have := hp a; omega

/-- A walk with nonnegative lengths is at least as long as any of its arcs. -/
lemma le_wlen_of_mem (hG : ∀ a, 0 ≤ G.len a) {l : List A} {a : A} (ha : a ∈ l) :
    G.len a ≤ wlen G l := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rw [wlen_cons]
    have h0 : 0 ≤ wlen G l := List.sum_nonneg (by simpa using fun c _ => hG c)
    rcases List.mem_cons.1 ha with rfl | h
    · omega
    · have := ih h; have := hG b; omega

/-! ### Distances -/

/-- **Shortest-path distances** from `r`: `δ y = some ℓ` when `ℓ` is the least length of a walk
from `r` to `y`, `δ y = none` when there is no walk from `r` to `y`. -/
structure IsDist (G : Digraph X A) (r : X) (δ : X → Option ℤ) : Prop where
  some_walk : ∀ y ℓ, δ y = some ℓ → ∃ l, IsWalk G r l y ∧ wlen G l = ℓ
  some_le : ∀ y ℓ, δ y = some ℓ → ∀ l, IsWalk G r l y → ℓ ≤ wlen G l
  none : ∀ y, δ y = none → ∀ l, ¬ IsWalk G r l y

/-- Along a walk, the distance is defined and at most its length. -/
lemma IsDist.exists_le {r y : X} {δ : X → Option ℤ} (h : IsDist G r δ) {l : List A}
    (hl : IsWalk G r l y) : ∃ ℓ, δ y = some ℓ ∧ ℓ ≤ wlen G l := by
  cases hy : δ y with
  | none => exact absurd hl (h.none y hy l)
  | some ℓ => exact ⟨ℓ, rfl, h.some_le y ℓ hy l hl⟩

/-- Distances are unique. -/
theorem IsDist.unique {r : X} {δ δ' : X → Option ℤ} (h : IsDist G r δ) (h' : IsDist G r δ') :
    δ = δ' := by
  funext y
  cases hy : δ y with
  | none =>
    cases hy' : δ' y with
    | none => rfl
    | some ℓ' =>
      obtain ⟨l, hw, -⟩ := h'.some_walk y ℓ' hy'
      exact absurd hw (h.none y hy l)
  | some ℓ =>
    obtain ⟨l, hw, hl⟩ := h.some_walk y ℓ hy
    obtain ⟨ℓ', hy', hle⟩ := h'.exists_le hw
    obtain ⟨l', hw', hl'⟩ := h'.some_walk y ℓ' hy'
    have := h.some_le y ℓ hy l' hw'
    rw [hy']; congr 1; omega

/-- **Distances exist** when the lengths admit a feasible potential: the lengths of the walks
from `r` to `y` are bounded below by `p y - p r`. -/
theorem exists_isDist {p : X → ℤ} (hp : G.IsPot p) (r : X) : ∃ δ, IsDist G r δ := by
  classical
  have key : ∀ y, ∃ o : Option ℤ, (o = none → ∀ l, ¬ IsWalk G r l y) ∧
      ∀ ℓ, o = some ℓ → (∃ l, IsWalk G r l y ∧ wlen G l = ℓ) ∧
        ∀ l, IsWalk G r l y → ℓ ≤ wlen G l := by
    intro y
    by_cases hy : ∃ l, IsWalk G r l y
    · obtain ⟨ℓ, ⟨l, hl, rfl⟩, hmin⟩ := Int.exists_least_of_bdd
        (P := fun ℓ => ∃ l, IsWalk G r l y ∧ wlen G l = ℓ)
        ⟨p y - p r, fun z ⟨l, hl, hz⟩ => hz ▸ hl.le_wlen hp⟩
        (by obtain ⟨l, hl⟩ := hy; exact ⟨_, l, hl, rfl⟩)
      refine ⟨some (wlen G l), by simp, fun ℓ' h' => ?_⟩
      cases h'
      exact ⟨⟨l, hl, rfl⟩, fun l' hl' => hmin _ ⟨l', hl', rfl⟩⟩
    · exact ⟨Option.none, fun _ l hl => hy ⟨l, hl⟩, by simp⟩
  choose δ hδ using key
  exact ⟨δ, ⟨fun y ℓ h => ((hδ y).2 ℓ h).1, fun y ℓ h => ((hδ y).2 ℓ h).2,
    fun y h => (hδ y).1 h⟩⟩

/-- With a feasible potential, the distance from the root to itself is `0`. -/
lemma IsDist.self {p : X → ℤ} (hp : G.IsPot p) {r : X} {δ : X → Option ℤ} (h : IsDist G r δ) :
    δ r = some 0 := by
  obtain ⟨ℓ, hr, hle⟩ := h.exists_le (l := []) rfl
  obtain ⟨l, hl, rfl⟩ := h.some_walk r _ hr
  have := hl.le_wlen hp
  simp only [wlen_nil, sub_self] at hle this
  rw [hr]; congr 1; omega

/-- **The triangle inequality** along an arc. -/
lemma IsDist.le_arc {r : X} {δ : X → Option ℤ} (h : IsDist G r δ) {a : A} {ℓ : ℤ}
    (ha : δ (G.src a) = some ℓ) : ∃ ℓ', δ (G.dst a) = some ℓ' ∧ ℓ' ≤ ℓ + G.len a := by
  obtain ⟨l, hl, rfl⟩ := h.some_walk _ ℓ ha
  obtain ⟨ℓ', h1, h2⟩ := h.exists_le (hl.append (isWalk_singleton.2 ⟨rfl, rfl⟩))
  exact ⟨ℓ', h1, by rw [wlen_append] at h2; simpa [wlen] using h2⟩

/-- **The distances form a feasible potential** when every vertex is reachable from the root. -/
lemma IsDist.isPot {r : X} {δ : X → Option ℤ} (h : IsDist G r δ) (hreach : ∀ y, δ y ≠ Option.none) :
    G.IsPot fun y => (δ y).getD 0 := by
  intro a
  obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 (hreach (G.src a))
  obtain ⟨ℓ', h1, h2⟩ := h.le_arc hℓ
  show (δ (G.dst a)).getD 0 ≤ (δ (G.src a)).getD 0 + G.len a
  rw [h1, hℓ]; exact h2

/-- The value of the distance at a vertex, when it is defined, is the length of a walk and at most
the length of any walk. -/
lemma IsDist.getD_le {r y : X} {δ : X → Option ℤ} (h : IsDist G r δ) {l : List A}
    (hl : IsWalk G r l y) : (δ y).getD 0 ≤ wlen G l := by
  obtain ⟨ℓ, h1, h2⟩ := h.exists_le hl; simpa [h1] using h2

/-! ### Changing the lengths by a potential -/

/-- The lengths changed by a potential `p`: `len a + p (dst a) - p (src a)`. -/
def _root_.PlanarFlow.Digraph.addPot (G : Digraph X A) (p : X → ℤ) : Digraph X A where
  src := G.src
  dst := G.dst
  len a := G.len a + (p (G.dst a) - p (G.src a))

lemma isWalk_addPot {p : X → ℤ} {x y : X} {l : List A} :
    IsWalk (G.addPot p) x l y ↔ IsWalk G x l y := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simp only [isWalk_cons, ih]; rfl

lemma wlen_addPot {p : X → ℤ} {x y : X} {l : List A} (h : IsWalk G x l y) :
    wlen (G.addPot p) l = wlen G l + (p y - p x) := by
  rw [← h.sum_sub p]
  simp only [wlen, Digraph.addPot, ← List.sum_map_add]

/-- **Distances shift under a change of the lengths by a potential.** -/
theorem isDist_addPot {p : X → ℤ} {r : X} {δ : X → Option ℤ} (h : IsDist G r δ) :
    IsDist (G.addPot p) r fun y => (δ y).map (· + (p y - p r)) := by
  refine ⟨fun y ℓ hy => ?_, fun y ℓ hy l hl => ?_, fun y hy l hl => ?_⟩
  · obtain ⟨ℓ₀, h0, rfl⟩ := Option.map_eq_some_iff.1 hy
    obtain ⟨l, hl, rfl⟩ := h.some_walk y ℓ₀ h0
    exact ⟨l, isWalk_addPot.2 hl, wlen_addPot hl⟩
  · obtain ⟨ℓ₀, h0, rfl⟩ := Option.map_eq_some_iff.1 hy
    have hl' := isWalk_addPot.1 hl
    rw [wlen_addPot hl']
    have := h.some_le y ℓ₀ h0 l hl'
    omega
  · rw [Option.map_eq_none_iff] at hy
    exact h.none y hy l (isWalk_addPot.1 hl)

/-! ### Subgraphs -/

/-- The subgraph of the arcs satisfying `q`. -/
def _root_.PlanarFlow.Digraph.restrict (G : Digraph X A) (q : A → Prop) : Digraph X {a // q a} where
  src a := G.src a.1
  dst a := G.dst a.1
  len a := G.len a.1

lemma IsWalk.of_restrict {q : A → Prop} {x y : X} {l : List {a // q a}}
    (h : IsWalk (G.restrict q) x l y) : IsWalk G x (l.map Subtype.val) y := by
  induction l generalizing x with
  | nil => exact h
  | cons a l ih => exact ⟨h.1, ih h.2⟩

lemma wlen_restrict {q : A → Prop} (l : List {a // q a}) :
    wlen (G.restrict q) l = wlen G (l.map Subtype.val) := by
  simp [wlen, Digraph.restrict]

end BKMNW

end PlanarFlow
