module

public import PlanarFlow.Klein.Interval
public import Mathlib.Order.Lex

/-!
# Moving the source: the shortest-path tree changes by pivots

Klein's multiple-source shortest paths in the form of Cabello, Chambers and Erickson (SIAM J.
Comput. 42, 2013, Section 3.1): the source moves from `u` to `v`, the next vertex on the face,
and the shortest-path tree rooted at `u` becomes the one rooted at `v` by pivots. In the
parametric picture the source is a point moving from `u` to `v`; a vertex `x` is *red* while its
shortest path comes from `u` and *blue* once it comes from `v`, and it turns blue when the
parameter passes `dist u x - dist v x`. So the vertices turn blue in decreasing order of the
key `(dist u x - dist v x, - dist v x)` (lexicographic; the second component breaks ties towards
`v`), each turning blue once (Corollary 3.3 of the article).

This file proves this for any digraph with positive lengths in which no arc enters `u` or `v`
and `u`, `v` reach the same other vertices (`MoveHyp`; the article's argument does not use
planarity). For a set `B` of blue vertices closed upwards in the key order (`Closed`), the mixed
parent function (`mix`: the parent towards `v` for blue vertices, towards `u` for red ones)
is a forest rooted at `u` and `v`: every parent link strictly decreases the well-founded measure
`phi` (`mix_descends`). The sweep (`sweep`) turns the vertices blue one at a time, the vertex of
largest key first:

* `sweep_spec`: the blue sets are closed, increase, end with all the vertices, and the sweep is
  a sequence of pivots with monotone colours (`PlanarFlow.Pivot.IsPivotSeq`,
  `PlanarFlow.Pivot.Colours`); so **a dart that pivots in never pivots out** during a move
  (`sweep_stays`, from the pivot lemma), every intermediate parent function is a forest rooted
  at `u` and `v` (`sweep_forest`), and the final one is the shortest-path tree of `v`.
* `next_active_min`: **the next pivot is the active arc of least slack** (the article's
  Lemma 3.1(c) and Corollary 3.2): the arc entering the next vertex to turn blue goes from a blue
  vertex to a red one, and no such arc has a smaller slack `dist v (tail) + len - dist u (head)`.
  (On a plane map these arcs, with the colours read from the forest, are the darts crossing the
  path of the dual cotree between the faces beside the source, the article's Lemma 3.4: see
  `PlanarFlow/Klein/Run.lean` for the pivot loop with these colours and
  `PlanarFlow/Klein/Dual.lean` for the lemma.)
* `realPivots_le`: the pivots that change a parent are at most the darts of the tree of `v`
  that are not in the tree of `u`.
* `tpar_dist`: the distances are read along the tree: `dist r x = dist r (tail a) + len a` for
  the parent arc `a` of `x`.

With `PlanarFlow.Klein.sum_card_sptree_le`, `klein_pivots`: **as the source moves once around
the face, at most `#S` pivots change a parent** (in the setting `PlanarFlow.MSSP.Hyp`, when the
roots reach the same vertices off the face).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset MSSP

section Sweep

variable {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]
variable (G : Digraph X A)

open Classical in
/-- **The parent arc of `x` in the shortest-path tree of `r`** (a tight arc entering `x`). -/
noncomputable def tpar (r x : X) : Option A :=
  if h : ∃ a, Tight G r a ∧ G.dst a = x ∧ x ≠ r then some h.choose else none

variable {G}

lemma tpar_spec {r x : X} {a : A} (h : tpar G r x = some a) :
    Tight G r a ∧ G.dst a = x ∧ x ≠ r := by
  unfold tpar at h
  split_ifs at h with hex
  obtain rfl := Option.some.inj h
  exact hex.choose_spec

lemma tpar_eq (hU : UniqTight G) {r x : X} {a : A} (ha : Tight G r a) (hx : G.dst a = x)
    (hxr : x ≠ r) : tpar G r x = some a := by
  have hex : ∃ a, Tight G r a ∧ G.dst a = x ∧ x ≠ r := ⟨a, ha, hx, hxr⟩
  unfold tpar
  simp only [hex, ↓reduceDIte]
  congr 1
  obtain ⟨h1, h2, -⟩ := hex.choose_spec
  exact hU r _ _ h1 ha (h2.trans hx.symm) (by rw [h2]; exact hxr)

lemma tpar_isSome (hnn : ∀ a, 0 ≤ G.len a) {r x : X} (h : Reach G r x) (hx : x ≠ r) :
    ∃ a, tpar G r x = some a := by
  obtain ⟨a, ha, hd⟩ := exists_tight hnn h hx
  have hex : ∃ a, Tight G r a ∧ G.dst a = x ∧ x ≠ r := ⟨a, ha, hd, hx⟩
  refine ⟨hex.choose, ?_⟩
  unfold tpar
  simp only [hex, ↓reduceDIte]

/-- **The distances are read along the tree.** -/
lemma tpar_dist {r x : X} {a : A} (h : tpar G r x = some a) :
    Reach G r (G.src a) ∧ dist G r x = dist G r (G.src a) + G.len a := by
  obtain ⟨⟨h1, h2⟩, rfl, -⟩ := tpar_spec h
  exact ⟨h1, h2.symm⟩

/-- **The hypotheses of a move** from `u` to `v`: positive lengths, no arc entering `u` or `v`,
and `u`, `v` reach the same other vertices. -/
structure MoveHyp (G : Digraph X A) (u v : X) : Prop where
  pos : ∀ a, 0 < G.len a
  ne : u ≠ v
  noU : ∀ a, G.dst a ≠ u
  noV : ∀ a, G.dst a ≠ v
  reach : ∀ x, x ≠ u → x ≠ v → (Reach G u x ↔ Reach G v x)

variable (G) in
/-- The vertices other than `u`, `v` reached from `u` (and from `v`). -/
noncomputable def moveSet (u v : X) : Finset X :=
  open Classical in univ.filter fun x => x ≠ u ∧ x ≠ v ∧ Reach G u x

variable (G) in
/-- **The key**: the vertices turn blue in decreasing order of the key. -/
noncomputable def key (u v x : X) : ℤ ×ₗ ℤ := toLex (dist G u x - dist G v x, - dist G v x)

variable (G) in
/-- **A set of blue vertices**, closed upwards in the key order. -/
def Closed (u v : X) (B : Finset X) : Prop :=
  B ⊆ moveSet G u v ∧ ∀ x ∈ B, ∀ y ∈ moveSet G u v, key G u v x < key G u v y → y ∈ B

variable (G) in
/-- **The mixed parent function**: towards `v` for blue vertices, towards `u` for red ones. -/
noncomputable def mix (u v : X) (B : Finset X) (x : X) : Option A :=
  if x ∈ B then tpar G v x else tpar G u x

variable (G) in
/-- The measure decreasing along parent links. -/
noncomputable def phi (u v : X) (B : Finset X) (x : X) : ℤ ×ₗ ℤ :=
  if x ∈ B then toLex (0, dist G v x) else toLex (1, dist G u x)

section Move

variable {u v : X} (H : MoveHyp G u v)
include H

lemma MoveHyp.mem_moveSet {x : X} : x ∈ moveSet G u v ↔ x ≠ u ∧ x ≠ v ∧ Reach G u x := by
  classical
  simp [moveSet]

lemma MoveHyp.ne_of_reach {r x : X} (_hr : r = u ∨ r = v) (h : Reach G r x) (hx : x ≠ r) :
    x ≠ u ∧ x ≠ v := by
  obtain ⟨a, -, rfl⟩ := exists_tight (fun a => (H.pos a).le) h hx
  exact ⟨H.noU a, H.noV a⟩

/-- **The mixed parent function is a forest rooted at `u` and `v`**: every parent link of a
vertex of the move leads to `u`, to `v`, or to a vertex of the move of smaller measure. -/
theorem mix_descends {B : Finset X} (hC : Closed G u v B) {x : X} (hx : x ∈ moveSet G u v)
    {a : A} (h : mix G u v B x = some a) :
    G.src a = u ∨ G.src a = v ∨
      (G.src a ∈ moveSet G u v ∧ phi G u v B (G.src a) < phi G u v B x) := by
  have hnn : ∀ a, 0 ≤ G.len a := fun a => (H.pos a).le
  obtain ⟨hxu, hxv, hux⟩ := H.mem_moveSet.1 hx
  have hvx : Reach G v x := (H.reach x hxu hxv).1 hux
  unfold mix at h
  by_cases hB : x ∈ B
  · simp only [hB, ↓reduceIte] at h
    obtain ⟨⟨hz, ht⟩, hd, -⟩ := tpar_spec h
    by_cases hzv : G.src a = v
    · exact Or.inr (Or.inl hzv)
    obtain ⟨hzu, -⟩ := H.ne_of_reach (Or.inr rfl) hz hzv
    have huz : Reach G u (G.src a) := (H.reach _ hzu hzv).2 hz
    have hzW : G.src a ∈ moveSet G u v := H.mem_moveSet.2 ⟨hzu, hzv, huz⟩
    have e1 := dist_arc hnn huz
    have hp := H.pos a
    rw [hd] at e1 ht
    have hkey : key G u v x < key G u v (G.src a) := by
      unfold key
      rw [Prod.Lex.toLex_lt_toLex]
      by_cases heq : dist G u x - dist G v x = dist G u (G.src a) - dist G v (G.src a)
      · right; exact ⟨heq, by simp only; omega⟩
      · left; simp only; omega
    have hzB : G.src a ∈ B := hC.2 x hB _ hzW hkey
    refine Or.inr (Or.inr ⟨hzW, ?_⟩)
    unfold phi
    simp only [hB, hzB, ↓reduceIte]
    rw [Prod.Lex.toLex_lt_toLex]
    right; exact ⟨rfl, by simp only; omega⟩
  · simp only [hB, ↓reduceIte] at h
    obtain ⟨⟨hz, ht⟩, hd, -⟩ := tpar_spec h
    by_cases hzu : G.src a = u
    · exact Or.inl hzu
    obtain ⟨-, hzv⟩ := H.ne_of_reach (Or.inl rfl) hz hzu
    have hzW : G.src a ∈ moveSet G u v := H.mem_moveSet.2 ⟨hzu, hzv, hz⟩
    refine Or.inr (Or.inr ⟨hzW, ?_⟩)
    have hp := H.pos a
    rw [hd] at ht
    unfold phi
    simp only [hB, ↓reduceIte]
    split_ifs with hzB <;> rw [Prod.Lex.toLex_lt_toLex]
    · left; simp
    · right; exact ⟨rfl, by simp only; omega⟩

end Move

/-! ### The sweep -/

variable (G) in
open Classical in
/-- The next vertex to turn blue: a red vertex of the move of largest key. -/
noncomputable def nextBlue (u v : X) (B : Finset X) : X :=
  if h : (moveSet G u v \ B).Nonempty then
    ((moveSet G u v \ B).exists_max_image (key G u v) h).choose
  else u

variable (G) in
/-- The blue sets of the sweep. -/
noncomputable def blue (u v : X) : ℕ → Finset X
  | 0 => ∅
  | i + 1 => insert (nextBlue G u v (blue u v i)) (blue u v i)

variable (G) in
/-- **The sweep**: the vertex turning blue at step `i`. -/
noncomputable def sweep (u v : X) (i : ℕ) : X := nextBlue G u v (blue G u v i)

lemma nextBlue_spec {u v : X} {B : Finset X} (h : (moveSet G u v \ B).Nonempty) :
    nextBlue G u v B ∈ moveSet G u v ∧ nextBlue G u v B ∉ B ∧
      ∀ y ∈ moveSet G u v, y ∉ B → key G u v y ≤ key G u v (nextBlue G u v B) := by
  unfold nextBlue
  simp only [h, ↓reduceDIte]
  obtain ⟨h1, h2⟩ := ((moveSet G u v \ B).exists_max_image (key G u v) h).choose_spec
  rw [mem_sdiff] at h1
  exact ⟨h1.1, h1.2, fun y hy hyB => h2 y (mem_sdiff.2 ⟨hy, hyB⟩)⟩

/-- **The blue sets are closed, and grow by one vertex at each step.** -/
lemma blue_spec {u v : X} : ∀ i ≤ (moveSet G u v).card,
    Closed G u v (blue G u v i) ∧ (blue G u v i).card = i
  | 0, _ => ⟨⟨empty_subset _, fun x hx => absurd hx (notMem_empty x)⟩, rfl⟩
  | i + 1, hi => by
    obtain ⟨⟨hsub, hcl⟩, hcard⟩ := blue_spec (u := u) (v := v) i (by omega)
    have hne : (moveSet G u v \ blue G u v i).Nonempty := by
      rw [nonempty_iff_ne_empty, ne_eq, sdiff_eq_empty_iff_subset]
      intro h
      have := card_le_card h
      omega
    obtain ⟨h1, h2, h3⟩ := nextBlue_spec hne
    refine ⟨⟨insert_subset h1 hsub, fun x hx y hy hxy => ?_⟩, ?_⟩
    · rw [blue, mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · by_contra hyn
        push Not at hyn
        exact absurd (h3 y hy hyn.2) (not_le.2 hxy)
      · exact Or.inr (hcl x hx y hy hxy)
    · rw [blue, card_insert_of_notMem h2, hcard]

/-- **The sweep**: a sequence of pivots with monotone colours, closed blue sets, ending with all
the vertices of the move blue. -/
theorem sweep_spec (u v : X) :
    Pivot.IsPivotSeq (fun i => mix G u v (blue G u v i)) (sweep G u v)
        (fun i => tpar G v (sweep G u v i)) (moveSet G u v).card ∧
      Pivot.Colours (fun i => (blue G u v i : Set X)) (sweep G u v) (moveSet G u v).card ∧
      (∀ i ≤ (moveSet G u v).card, Closed G u v (blue G u v i)) ∧
      blue G u v (moveSet G u v).card = moveSet G u v ∧
      ∀ i < (moveSet G u v).card, sweep G u v i ∈ moveSet G u v := by
  have hne : ∀ i < (moveSet G u v).card, (moveSet G u v \ blue G u v i).Nonempty := by
    intro i hi
    rw [nonempty_iff_ne_empty, ne_eq, sdiff_eq_empty_iff_subset]
    intro h
    have := card_le_card h
    have := (blue_spec i hi.le).2
    omega
  refine ⟨⟨fun i hi => funext fun x => ?_⟩, ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩,
    fun i hi => (blue_spec i hi).1, ?_, fun i hi => (nextBlue_spec (hne i hi)).1⟩
  · simp only [mix, blue, mem_insert, Function.update_apply]
    by_cases hx : x = sweep G u v i
    · subst hx; simp [sweep]
    · have : x ≠ nextBlue G u v (blue G u v i) := hx
      simp [this, hx]
  · intro x hx; simp only [blue, coe_insert, Set.mem_insert_iff]; exact Or.inr hx
  · exact (nextBlue_spec (hne i hi)).2.1
  · simp [blue, sweep]
  · obtain ⟨⟨hsub, -⟩, hcard⟩ := blue_spec (G := G) (u := u) (v := v) _ le_rfl
    exact eq_of_subset_of_card_le hsub (by omega)

/-- **A dart that pivots in never pivots out** during a move (Corollary 3.3 of the article). -/
theorem sweep_stays (u v : X) {i j : ℕ} (hij : i < j) (hj : j ≤ (moveSet G u v).card) :
    mix G u v (blue G u v j) (sweep G u v i) = tpar G v (sweep G u v i) := by
  obtain ⟨hP, hC, -⟩ := sweep_spec (G := G) u v
  exact hP.stays hC hij hj

/-- **Every intermediate parent function is a forest rooted at `u` and `v`.** -/
theorem sweep_forest {u v : X} (H : MoveHyp G u v) {i : ℕ} (hi : i ≤ (moveSet G u v).card)
    {x : X} (hx : x ∈ moveSet G u v) {a : A} (h : mix G u v (blue G u v i) x = some a) :
    G.src a = u ∨ G.src a = v ∨ (G.src a ∈ moveSet G u v ∧
      phi G u v (blue G u v i) (G.src a) < phi G u v (blue G u v i) x) :=
  mix_descends H ((sweep_spec u v).2.2.1 i hi) hx h

/-- **The sweep starts from the tree of `u` and ends with the tree of `v`.** -/
theorem sweep_ends (u v : X) (x : X) :
    mix G u v (blue G u v 0) x = tpar G u x ∧
      (x ∈ moveSet G u v → mix G u v (blue G u v (moveSet G u v).card) x = tpar G v x) := by
  refine ⟨by simp [mix, blue], fun hx => ?_⟩
  rw [(sweep_spec (G := G) u v).2.2.2.1]
  simp [mix, hx]

/-! ### The next pivot -/

variable (G) in
/-- **The slack of an arc** for the move from `u` to `v`: `dist v (tail) + len - dist u (head)`.
Up to a common parametric offset it is the slack of the article (Lemma 3.1: the slacks of the
active darts decrease at the same rate), the value stored on the dual forest. -/
noncomputable def slack (u v : X) (a : A) : ℤ := dist G v (G.src a) + G.len a - dist G u (G.dst a)

variable (G) in
/-- **An active arc** at the blue set `B`: from a blue vertex (or `v`) to a red vertex of the
move (the article's Lemma 3.1(c)). -/
def Active (u v : X) (B : Finset X) (a : A) : Prop :=
  (G.src a ∈ B ∨ G.src a = v) ∧ G.dst a ∈ moveSet G u v ∧ G.dst a ∉ B

/-- **The next pivot is the active arc of least slack** (the article's Corollary 3.2): at a closed
blue set, the parent arc towards `v` of the next vertex to turn blue is active, and no active arc
has a smaller slack. On a plane map the active arcs are the darts crossing the path of the dual
forest between the faces beside the source (the article's Lemma 3.4), so this arc is the answer
of `MINPATH` on the slacks. -/
theorem next_active_min {u v : X} (H : MoveHyp G u v) {B : Finset X} (hC : Closed G u v B)
    (hne : (moveSet G u v \ B).Nonempty) {a : A} (ha : tpar G v (nextBlue G u v B) = some a) :
    Active G u v B a ∧ ∀ b, Active G u v B b → slack G u v a ≤ slack G u v b := by
  have hnn : ∀ a, 0 ≤ G.len a := fun a => (H.pos a).le
  obtain ⟨hxW, hxB, hmax⟩ := nextBlue_spec hne
  generalize nextBlue G u v B = x at hxW hxB hmax ha
  obtain ⟨⟨hz, ht⟩, hd, -⟩ := tpar_spec ha
  obtain ⟨hxu, hxv, hux⟩ := H.mem_moveSet.1 hxW
  refine ⟨⟨?_, hd ▸ hxW, hd ▸ hxB⟩, fun b ⟨hb1, hb2, hb3⟩ => ?_⟩
  · by_cases hzv : G.src a = v
    · exact Or.inr hzv
    left
    obtain ⟨hzu, -⟩ := H.ne_of_reach (Or.inr rfl) hz hzv
    have huz : Reach G u (G.src a) := (H.reach _ hzu hzv).2 hz
    have hzW : G.src a ∈ moveSet G u v := H.mem_moveSet.2 ⟨hzu, hzv, huz⟩
    by_contra hzB
    have e1 := dist_arc hnn huz
    have hp := H.pos a
    rw [hd] at e1 ht
    have h1 := hmax _ hzW hzB
    unfold key at h1
    rw [Prod.Lex.toLex_le_toLex] at h1
    simp only at h1
    omega
  · -- the slack of `b` is at least `dist v y - dist u y` for its red head `y`
    have hvb : Reach G v (G.src b) := by
      rcases hb1 with h | h
      · obtain ⟨h1, h2, h3⟩ := H.mem_moveSet.1 (hC.1 h)
        exact (H.reach _ h1 h2).1 h3
      · rw [h]; exact Reach.refl _
    have e1 := dist_arc hnn hvb
    have h1 := hmax _ hb2 hb3
    unfold key at h1
    rw [Prod.Lex.toLex_le_toLex] at h1
    simp only at h1
    unfold slack
    rw [hd] at ht ⊢
    omega

variable (G) in
open Classical in
/-- The pivots of the sweep that change a parent. -/
noncomputable def realPivots (u v : X) : ℕ :=
  ((range (moveSet G u v).card).filter fun i =>
    tpar G u (sweep G u v i) ≠ tpar G v (sweep G u v i)).card

open Classical in
/-- **The pivots that change a parent are at most the darts of the tree of `v` not in the tree
of `u`.** -/
theorem realPivots_le {u v : X} (H : MoveHyp G u v) (hU : UniqTight G) :
    realPivots G u v ≤
      ((univ.filter fun a => Tight G v a) \ univ.filter fun a => Tight G u a).card := by
  have hnn : ∀ a, 0 ≤ G.len a := fun a => (H.pos a).le
  obtain ⟨-, hC, -, -, hW⟩ := sweep_spec (G := G) u v
  have hsome : ∀ i < (moveSet G u v).card, ∃ a, tpar G v (sweep G u v i) = some a := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := H.mem_moveSet.1 (hW i hi)
    exact tpar_isSome hnn ((H.reach _ h1 h2).1 h3) h2
  rcases isEmpty_or_nonempty A with hA | hA
  · have h0 : (moveSet G u v).card = 0 := by
      by_contra h
      obtain ⟨a, -⟩ := hsome 0 (by omega)
      exact isEmptyElim a
    simp [realPivots, h0]
  choose! f hf using hsome
  unfold realPivots
  refine card_le_card_of_injOn f (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hi
    obtain ⟨hv, -, -⟩ := tpar_spec (hf i hi.1)
    simp only [coe_sdiff, coe_filter, mem_univ, true_and, Set.mem_sdiff, Set.mem_ofPred_eq]
    refine ⟨hv, fun hu => hi.2 ?_⟩
    obtain ⟨-, hd, -⟩ := tpar_spec (hf i hi.1)
    rw [hf i hi.1, tpar_eq hU hu hd (H.mem_moveSet.1 (hd ▸ hW i hi.1)).1]
  · simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hi hj
    obtain ⟨-, hdi, -⟩ := tpar_spec (hf i hi.1)
    obtain ⟨-, hdj, -⟩ := tpar_spec (hf j hj.1)
    have : sweep G u v i = sweep G u v j := by rw [← hdi, ← hdj, hij]
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hC.y_ne h hj.1 this.symm
    · exact hC.y_ne h hi.1 this

end Sweep

/-! ### Around the face -/

section Face

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

/-- **A move between two roots meets the hypotheses of a move.** -/
lemma moveHyp_of_hyp (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) {i j : ℕ} (hi : i < k)
    (hj : j < k) (hij : i ≠ j) :
    MoveHyp (pieceGraph M S ℓ) (M.tail (g i)) (M.tail (g j)) where
  pos := H.pos'
  ne h := hij (H.face.inj i hi j hj h)
  noU a h := H.noIn a.1 a.2 ⟨i, hi, h.symm⟩
  noV a h := H.noIn a.1 a.2 ⟨j, hj, h.symm⟩
  reach x hxu hxv := by
    by_cases hx : IsRoot M k g x
    · constructor
      · intro h; exact absurd (H.eq_of_reach_root h hx) hxu
      · intro h; exact absurd (H.eq_of_reach_root h hx) hxv
    · exact ⟨hR i hi j hj x hx, hR j hj i hi x hx⟩

/-- **As the source moves once around the face, at most `#S` pivots change a parent.** -/
theorem klein_pivots (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) :
    ∑ j ∈ range k, realPivots (pieceGraph M S ℓ) (M.tail (g j)) (M.tail (g ((j + 1) % k)))
      ≤ S.card := by
  classical
  have hk : 2 ≤ k := H.face.two_le
  refine le_trans (sum_le_sum fun j hj => ?_) (sum_card_sptree_le H hR)
  have hj' : j < k := mem_range.1 hj
  have hne : j ≠ (j + 1) % k := by
    rcases Nat.lt_or_ge (j + 1) k with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [show j + 1 = k by omega, Nat.mod_self]; omega
  have := realPivots_le (moveHyp_of_hyp H hR hj' (Nat.mod_lt _ (by omega)) hne) H.uniq
  convert this using 2; ext a; simp [sptree]

/-- **The hypotheses of a move can be met** (the map of a single edge; a witness of
satisfiability only, from `edge_hyp`). -/
theorem edge_moveHyp (ℓ : (⊤ : SimpleGraph (Fin 2)).Dart → ℤ) :
    MoveHyp (pieceGraph (CombMap.ofRotation kEdgeRot) ∅ ℓ)
      ((CombMap.ofRotation kEdgeRot).tail (edgeG 0))
      ((CombMap.ofRotation kEdgeRot).tail (edgeG 1)) :=
  moveHyp_of_hyp (edge_hyp ℓ).1 (edge_hyp ℓ).2 (by norm_num) (by norm_num) (by norm_num)

end Face

end Klein

end PlanarFlow
