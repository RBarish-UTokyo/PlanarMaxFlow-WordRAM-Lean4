module

public import PlanarSeparator.CycleSeparator
public import PlanarSeparator.Machine.Cotree

/-!
# The strict insides of fundamental cycles: an exact recursion

Let `δ` be a dart off a spanning tree `T` of a plane triangulation, with triangle `x z y`
(`x = vert δ`, `z = vert (α δ)`, `y = vert (φ² δ)`), and `a₁ = α (φ δ)`, `a₂ = α (φ² δ)` the
reversals of the two other darts of the triangle. The descent of Miller's separator
(`PlanarSeparator.Map.SpTree.exists_simple_balanced_of_lt`) uses only the inclusion
`inC δ ⊆ inC a₁ ∪ inC a₂ ∪ bset δ` (`inC_subset_union`). To compute the weights of the strict
insides of all darts at once (bottom-up along the dual tree, as a program must), the recursion has
to be exact. This file proves:

* (from `PlanarSeparator/Machine/Cotree.lean`) the insides of `a₁` and `a₂` are disjoint
  (`disjoint_inside`) and with the face of `δ` make up the inside of `δ` (`inside_eq`);
* `inC_child_subset`: a vertex strictly inside `a₁` (or `a₂`) is strictly inside `δ`;
* `bset_eq`: `bset δ` is the set of the vertices of the cycles of `a₁` and `a₂`, and the apex `y`,
  that are off the cycle of `δ` (all of them lie strictly inside `δ`);
* **`inC_eq_union`, `sum_inC`**: `inC δ` is the disjoint union of `inC a₁`, `inC a₂` and
  `bset δ`, so `W (inC δ) = W (inC a₁) + W (inC a₂) + W (bset δ)` for any weights.

* `anc_inter_anc`, `cycV_eq_anc`, **`sum_cycV`**: the common ancestors of the ends `x`, `z` of `δ`
  are the ancestors of their lowest common ancestor `l`, the cycle is the two root paths without
  the strict ancestors of `l`, and `W (cycV δ) = rs x + rs z - 2 rs l + w l` with the root sums
  `rs v = W (anc v)` (computable with root sums and lowest-common-ancestor queries).

* `tripod`: of the three lowest common ancestors `p`, `q`, `r` of the corners `x z`, `x y`, `y z`,
  two coincide and are ancestors of the third; `cycE`, `cycE_eq`: for every dart (tree dart or
  not) the two root paths without the strict ancestors of the lowest common ancestor are the
  cycle with the two ends;
* **`sum_bset`**: `W (bset δ)` is `rs y - rs c` for the center `c ∈ {q, r}`, or
  `rs y - rs q + (rs p - w p) - (rs q - w q)` when the center is `p`.

With `sum_inC`, `sum_cycV` and `inC_α` (the strict inside of `α δ` is the strict outside of `δ`),
the weights of the strict insides of all darts off the tree are computed bottom-up along the dual
tree from root sums and lowest-common-ancestor queries.

Along a descent `δ → a₁` or `δ → a₂` the sets `bset` are pairwise disjoint (each lies on the cycle
of the next dart, `bset_subset₁`, `bset_subset₂`, and later strict insides avoid it), which is what
makes an incremental computation of the weights linear in total.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

open Finset

namespace Map

namespace SpTree

variable {D P : Type*} {M : Map D P} {T : SpTree M} [DecidableEq D] [DecidableEq P] [Fintype D]
  [Fintype P]

section Triangle

variable {δ : D}

variable (hM : M.IsPlane) (hδ : M.IsTriangle δ) (hnt : ¬ T.IsTree δ)
include hM hδ hnt

lemma inside_a₁_subset : T.inside (M.α (M.φ δ)) ⊆ (T.inside δ).erase (M.face δ) :=
  inside_α_subset hM hnt (M.face_φ δ) hδ.edge_ne₁

lemma inside_a₂_subset : T.inside (M.α (M.φ (M.φ δ))) ⊆ (T.inside δ).erase (M.face δ) :=
  inside_α_subset hM hnt ((M.face_φ _).trans (M.face_φ δ)) hδ.edge_ne₂

omit hδ hnt in
/-- A vertex of the cycle of `δ` has a face outside `δ`. -/
lemma exists_face_notMem_inside_of_mem_cycV {v : P} (hv : v ∈ T.cycV δ) :
    ∃ d, M.vert d = v ∧ M.face d ∉ T.inside δ := by
  obtain ⟨d, hd, hf⟩ := (T.mem_cycV).1 hv
  have h := (inside_iff hM δ d).not.2 hf
  by_cases h1 : M.face d ∈ T.inside δ
  · have h2 : M.face (M.α d) ∉ T.inside δ := fun h2 => h ⟨fun _ => h2, fun _ => h1⟩
    refine ⟨M.φ (M.α d), ?_, by rwa [M.face_φ]⟩
    rw [M.vert_φ, M.α_α, hd]
  · exact ⟨d, hd, h1⟩

/-- A vertex strictly inside a child `a` (`a₁` or `a₂`, whose inside lies in the inside of `δ`) is
strictly inside `δ`. -/
lemma inC_child_subset {a : D} (ha : T.inside a ⊆ T.inside δ) : T.inC a ⊆ T.inC δ := by
  intro v hv
  have hva := notMem_cycV_of_mem_inC hv
  have hvδ : v ∉ T.cycV δ := by
    intro hc
    obtain ⟨d, hd, hf⟩ := exists_face_notMem_inside_of_mem_cycV hM hc
    exact hf (ha ((mem_inC_iff hM hva hd).1 hv))
  obtain ⟨d, hd⟩ := hM.exists_dart v
  exact (mem_inC_iff hM hvδ hd).2 (ha ((mem_inC_iff hM hva hd).1 hv))

omit hδ hnt in
/-- A vertex of the cycle of `δ` has a face inside `δ`. -/
lemma exists_face_mem_inside_of_mem_cycV {v : P} (hv : v ∈ T.cycV δ) :
    ∃ d, M.vert d = v ∧ M.face d ∈ T.inside δ := by
  obtain ⟨d, hd, hf⟩ := (T.mem_cycV).1 hv
  have h := (inside_iff hM δ d).not.2 hf
  by_cases h1 : M.face d ∈ T.inside δ
  · exact ⟨d, hd, h1⟩
  · have h2 : M.face (M.α d) ∈ T.inside δ := by
      by_contra h2; exact h ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩
    refine ⟨M.φ (M.α d), ?_, by rwa [M.face_φ]⟩
    rw [M.vert_φ, M.α_α, hd]

/-- **`bset δ` without the strict inside**: every vertex of the cycles of `a₁` and `a₂`, and the
apex `y`, that is off the cycle of `δ` lies strictly inside `δ`; so `bset δ` is the set of these
vertices off the cycle of `δ`. -/
theorem bset_eq :
    bset δ (T := T) = insert (M.vert (M.φ (M.φ δ)))
      (T.cycV (M.α (M.φ δ)) ∪ T.cycV (M.α (M.φ (M.φ δ)))) \ T.cycV δ := by
  ext v
  simp only [bset, mem_inter, mem_sdiff]
  constructor
  · rintro ⟨hi, hv⟩
    exact ⟨hv, notMem_cycV_of_mem_inC hi⟩
  · rintro ⟨hv, hc⟩
    refine ⟨?_, hv⟩
    -- a face at `v` inside a child, or the face of `δ` at the apex
    have hface : ∃ d, M.vert d = v ∧ M.face d ∈ T.inside δ := by
      rcases mem_insert.1 hv with rfl | hv
      · exact ⟨M.φ (M.φ δ), rfl, by rw [M.face_φ, M.face_φ]; exact face_mem_inside hM hnt⟩
      rcases mem_union.1 hv with hv | hv
      · obtain ⟨d, hd, hf⟩ := exists_face_mem_inside_of_mem_cycV hM hv
        exact ⟨d, hd, mem_of_mem_erase (inside_a₁_subset hM hδ hnt hf)⟩
      · obtain ⟨d, hd, hf⟩ := exists_face_mem_inside_of_mem_cycV hM hv
        exact ⟨d, hd, mem_of_mem_erase (inside_a₂_subset hM hδ hnt hf)⟩
    obtain ⟨d, hd, hf⟩ := hface
    exact (mem_inC_iff hM hc hd).2 hf

/-- **The exact recursion of the strict insides**: `inC δ` is the union of `inC a₁`, `inC a₂`
and `bset δ`, and the three are pairwise disjoint. -/
theorem inC_eq_union :
    T.inC δ = T.inC (M.α (M.φ δ)) ∪ T.inC (M.α (M.φ (M.φ δ))) ∪ bset δ (T := T) ∧
      Disjoint (T.inC (M.α (M.φ δ))) (T.inC (M.α (M.φ (M.φ δ)))) ∧
      Disjoint (T.inC (M.α (M.φ δ)) ∪ T.inC (M.α (M.φ (M.φ δ)))) (bset δ (T := T)) := by
  have s₁ : T.inC (M.α (M.φ δ)) ⊆ T.inC δ :=
    inC_child_subset hM hδ hnt fun _ h => mem_of_mem_erase (inside_a₁_subset hM hδ hnt h)
  have s₂ : T.inC (M.α (M.φ (M.φ δ))) ⊆ T.inC δ :=
    inC_child_subset hM hδ hnt fun _ h => mem_of_mem_erase (inside_a₂_subset hM hδ hnt h)
  have sB : bset δ (T := T) ⊆ T.inC δ := inter_subset_left
  -- a vertex strictly inside a child is off the child's cycle, which holds `bset`
  have dB : ∀ a : D, (¬ T.IsTree a → bset δ (T := T) ⊆ T.cycV a) →
      Disjoint (T.inC a) (bset δ (T := T)) := by
    intro a hsub
    by_cases ht : T.IsTree a
    · rw [inC_eq_empty hM ht]; exact disjoint_empty_left _
    · rw [disjoint_left]
      intro v hv hB
      exact notMem_cycV_of_mem_inC hv (hsub ht hB)
  refine ⟨(inC_subset_union hδ hnt hM).antisymm
    (union_subset (union_subset s₁ s₂) sB), ?_, ?_⟩
  · rw [disjoint_left]
    intro v h1 h2
    obtain ⟨d, hd⟩ := hM.exists_dart v
    exact disjoint_left.1 (disjoint_inside hM hδ hnt)
      ((mem_inC_iff hM (notMem_cycV_of_mem_inC h1) hd).1 h1)
      ((mem_inC_iff hM (notMem_cycV_of_mem_inC h2) hd).1 h2)
  · exact disjoint_union_left.2 ⟨dB _ (bset_subset₁ hδ hnt), dB _ (bset_subset₂ hδ hnt)⟩

/-- **The weight of the strict inside of `δ`** is the sum of the weights of the strict insides
of `a₁` and `a₂` and of `bset δ`, for any weights. -/
theorem sum_inC {β : Type*} [AddCommMonoid β] (w : P → β) :
    ∑ v ∈ T.inC δ, w v = ∑ v ∈ T.inC (M.α (M.φ δ)), w v + ∑ v ∈ T.inC (M.α (M.φ (M.φ δ))), w v +
      ∑ v ∈ bset δ (T := T), w v := by
  obtain ⟨he, h12, h3⟩ := inC_eq_union hM hδ hnt
  rw [he, sum_union h3, sum_union h12]

end Triangle

/-! ### Root paths and the weight of a fundamental cycle -/

section Paths

omit [Fintype D] [Fintype P] in
/-- The ancestors of a vertex form a chain. -/
lemma anc_chain {u u' v : P} (hu : u ∈ T.anc v) (hu' : u' ∈ T.anc v) :
    u ∈ T.anc u' ∨ u' ∈ T.anc u := by
  obtain ⟨i, rfl⟩ := (T.mem_anc_iff).1 hu
  obtain ⟨j, rfl⟩ := (T.mem_anc_iff).1 hu'
  rcases le_total i j with h | h
  · right
    rw [← Nat.sub_add_cancel h, Function.iterate_add_apply]
    exact T.iterate_parent_mem_anc _ _
  · left
    rw [← Nat.sub_add_cancel h, Function.iterate_add_apply]
    exact T.iterate_parent_mem_anc _ _

omit [Fintype D] [Fintype P] in
/-- **The common ancestors of the two ends of `δ` are the ancestors of their lowest common
ancestor.** -/
lemma anc_inter_anc (δ : D) :
    T.anc (M.vert δ) ∩ T.anc (M.vert (M.α δ)) = T.anc (lca T δ) := by
  ext u
  simp only [mem_inter]
  constructor
  · rintro ⟨hx, hz⟩
    obtain ⟨i, rfl⟩ := (T.mem_anc_iff).1 hz
    rcases Nat.lt_or_ge i (cs T δ) with hi | hi
    · exact absurd hx (iterate_notMem_of_lt_cs hi)
    · show T.parent^[i] (M.vert (M.α δ)) ∈ T.anc (T.parent^[cs T δ] (M.vert (M.α δ)))
      rw [← Nat.sub_add_cancel hi, Function.iterate_add_apply]
      exact T.iterate_parent_mem_anc _ _
  · intro h
    exact ⟨T.anc_subset_anc (lca_mem_anc δ) h, T.anc_subset_anc (lca_mem_anc' δ) h⟩

omit [Fintype D] [Fintype P] in
/-- Membership in the root path of a lowest common ancestor. -/
lemma mem_anc_lca_iff (δ : D) {u : P} :
    u ∈ T.anc (lca T δ) ↔ u ∈ T.anc (M.vert δ) ∧ u ∈ T.anc (M.vert (M.α δ)) := by
  rw [← anc_inter_anc, mem_inter]

omit [Fintype D] [Fintype P] in
/-- **Three vertices and their pairwise lowest common ancestors** (given as those of three darts
with ends `x z`, `x y`, `y z`): two of the three coincide and are ancestors of the third. -/
lemma tripod {δ a b : D} {x y z : P} (h1 : M.vert δ = x) (h2 : M.vert (M.α δ) = z)
    (h3 : M.vert a = x) (h4 : M.vert (M.α a) = y) (h5 : M.vert b = y) (h6 : M.vert (M.α b) = z) :
    (lca T a = lca T b ∧ lca T a ∈ T.anc (lca T δ)) ∨
      (lca T δ = lca T b ∧ lca T δ ∈ T.anc (lca T a)) ∨
      (lca T δ = lca T a ∧ lca T δ ∈ T.anc (lca T b)) := by
  set p := lca T δ
  set q := lca T a
  set r := lca T b
  have hp : ∀ u, u ∈ T.anc p ↔ u ∈ T.anc x ∧ u ∈ T.anc z := fun u => by
    rw [mem_anc_lca_iff, h1, h2]
  have hq : ∀ u, u ∈ T.anc q ↔ u ∈ T.anc x ∧ u ∈ T.anc y := fun u => by
    rw [mem_anc_lca_iff, h3, h4]
  have hr : ∀ u, u ∈ T.anc r ↔ u ∈ T.anc y ∧ u ∈ T.anc z := fun u => by
    rw [mem_anc_lca_iff, h5, h6]
  have pp := (hp p).1 (T.mem_anc_self p)
  have qq := (hq q).1 (T.mem_anc_self q)
  have rr := (hr r).1 (T.mem_anc_self r)
  -- `anc` is transitive
  have tr : ∀ {u v w : P}, u ∈ T.anc v → v ∈ T.anc w → u ∈ T.anc w :=
    fun huv hvw => T.anc_subset_anc hvw huv
  have antisymm : ∀ {u v : P}, u ∈ T.anc v → v ∈ T.anc u → u = v :=
    fun h h' => T.eq_of_mem_anc_of_mem_anc h h'
  rcases anc_chain pp.1 qq.1 with hpq | hqp
  · -- `p` above `q`
    rcases anc_chain pp.2 rr.2 with hpr | hrp
    · -- `p` above `r` too: `p` is a common ancestor of `y`
      have hpy : p ∈ T.anc y := tr hpq qq.2
      have hpq' : p ∈ T.anc q := (hq p).2 ⟨pp.1, hpy⟩
      have hpr' : p ∈ T.anc r := (hr p).2 ⟨hpy, pp.2⟩
      -- `q` and `r` both lie on the root path of `y`
      rcases anc_chain qq.2 rr.1 with hqr | hrq
      · -- `q` above `r`: `q` is an ancestor of `z`, so of `p`
        have hqz : q ∈ T.anc z := tr hqr rr.2
        have hqp : q ∈ T.anc p := (hp q).2 ⟨qq.1, hqz⟩
        have e : p = q := antisymm hpq' hqp
        exact Or.inr (Or.inr ⟨e, by rw [e]; exact hqr⟩)
      · have hrx : r ∈ T.anc x := tr hrq qq.1
        have hrp : r ∈ T.anc p := (hp r).2 ⟨hrx, rr.2⟩
        have e : p = r := antisymm hpr' hrp
        exact Or.inr (Or.inl ⟨e, by rw [e]; exact hrq⟩)
    · -- `r` above `p`, `p` above `q`
      have hrx : r ∈ T.anc x := tr hrp pp.1
      have hrq : r ∈ T.anc q := (hq r).2 ⟨hrx, rr.1⟩
      have hry : q ∈ T.anc y := qq.2
      rcases anc_chain qq.2 rr.1 with hqr | hrq'
      · have e : q = r := antisymm hqr hrq
        have hqz : q ∈ T.anc z := tr hqr rr.2
        exact Or.inl ⟨e, (hp q).2 ⟨qq.1, hqz⟩⟩
      · -- `r` above `q`: then `p` is an ancestor of `y`
        have hpy : p ∈ T.anc y := tr hpq qq.2
        have hpr : p ∈ T.anc r := (hr p).2 ⟨hpy, pp.2⟩
        have e : p = r := antisymm hpr hrp
        exact Or.inr (Or.inl ⟨e, by rw [e]; exact hrq'⟩)
  · -- `q` above `p`
    have hqz : q ∈ T.anc z := tr hqp pp.2
    have hqr : q ∈ T.anc r := (hr q).2 ⟨qq.2, hqz⟩
    rcases anc_chain qq.2 rr.1 with hqr' | hrq
    · rcases anc_chain pp.2 rr.2 with hpr | hrp
      · have hpy : p ∈ T.anc y := tr hpr rr.1
        have hpq : p ∈ T.anc q := (hq p).2 ⟨pp.1, hpy⟩
        have e : p = q := antisymm hpq hqp
        exact Or.inr (Or.inr ⟨e, by rw [e]; exact hqr⟩)
      · have hrx : r ∈ T.anc x := tr hrp pp.1
        have hrq : r ∈ T.anc q := (hq r).2 ⟨hrx, rr.1⟩
        have e : q = r := antisymm hqr hrq
        exact Or.inl ⟨e, hqp⟩
    · have e : q = r := antisymm hqr hrq
      exact Or.inl ⟨e, hqp⟩

omit [Fintype D] in
/-- **The vertices of a fundamental cycle**: the two root paths of the ends of `δ` without the
strict ancestors of their lowest common ancestor. -/
lemma cycV_eq_anc {δ : D} (hnt : ¬ T.IsTree δ) :
    T.cycV δ = (T.anc (M.vert δ) ∪ T.anc (M.vert (M.α δ))) \ (T.anc (lca T δ)).erase (lca T δ) := by
  ext v
  rw [mem_cycV_iff hnt, mem_sdiff, mem_union, mem_erase]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · refine ⟨Or.inl (T.iterate_parent_mem_anc _ _), fun ⟨hne, hl⟩ => hne ?_⟩
      refine T.eq_of_mem_anc_of_mem_anc hl ?_
      rw [← iterate_ct δ, ← Nat.sub_add_cancel hj, Function.iterate_add_apply]
      exact T.iterate_parent_mem_anc _ _
    · refine ⟨Or.inr (T.iterate_parent_mem_anc _ _), fun ⟨hne, hl⟩ => ?_⟩
      have hl' : lca T δ ∈ T.anc (T.parent^[j] (M.vert (M.α δ))) := by
        show T.parent^[cs T δ] (M.vert (M.α δ)) ∈ _
        rw [← Nat.sub_add_cancel hj.le, Function.iterate_add_apply]
        exact T.iterate_parent_mem_anc _ _
      have := T.eq_of_mem_anc_of_mem_anc hl hl'
      exact iterate_notMem_of_lt_cs hj (this ▸ lca_mem_anc δ)
  · rintro ⟨hv | hv, hnl⟩
    · obtain ⟨j, rfl⟩ := (T.mem_anc_iff).1 hv
      rcases le_or_gt j (ct T δ) with hj | hj
      · exact Or.inl ⟨j, hj, rfl⟩
      · have hl : T.parent^[j] (M.vert δ) ∈ T.anc (lca T δ) := by
          rw [← iterate_ct δ, ← Nat.sub_add_cancel hj.le, Function.iterate_add_apply]
          exact T.iterate_parent_mem_anc _ _
        have he : T.parent^[j] (M.vert δ) = lca T δ := by
          by_contra hne; exact hnl ⟨hne, hl⟩
        exact Or.inl ⟨ct T δ, le_rfl, by rw [he, iterate_ct]⟩
    · obtain ⟨j, rfl⟩ := (T.mem_anc_iff).1 hv
      rcases Nat.lt_or_ge j (cs T δ) with hj | hj
      · exact Or.inr ⟨j, hj, rfl⟩
      · have hl : T.parent^[j] (M.vert (M.α δ)) ∈ T.anc (lca T δ) := by
          show _ ∈ T.anc (T.parent^[cs T δ] (M.vert (M.α δ)))
          rw [← Nat.sub_add_cancel hj, Function.iterate_add_apply]
          exact T.iterate_parent_mem_anc _ _
        have he : T.parent^[j] (M.vert (M.α δ)) = lca T δ := by
          by_contra hne; exact hnl ⟨hne, hl⟩
        exact Or.inl ⟨ct T δ, le_rfl, by rw [he, iterate_ct]⟩

/-- The two root paths of the ends of a dart without the strict ancestors of their lowest common
ancestor: the vertices of the fundamental cycle, together with the two ends. -/
noncomputable def cycE (δ : D) : Finset P :=
  (T.anc (M.vert δ) ∪ T.anc (M.vert (M.α δ))) \ (T.anc (lca T δ)).erase (lca T δ)

omit [Fintype D] [Fintype P] in
lemma notMem_anc_parent {v : P} (hv : v ≠ T.root) : v ∉ T.anc (T.parent v) := fun h =>
  absurd (T.height_le_of_mem_anc h) (not_le.2 (T.height_parent_lt hv))

omit [Fintype D] [Fintype P] in
/-- The lowest common ancestor of the ends of a tree dart is the parent end. -/
lemma lca_par (v : P) (hv : v ≠ T.root) : lca T (T.par v hv) = T.parent v ∧
    lca T (M.α (T.par v hv)) = T.parent v := by
  classical
  have hpv : M.vert (M.α (T.par v hv)) = T.parent v := (T.parent_of_ne hv).symm
  have hvv : M.vert (T.par v hv) = v := T.vert_par v hv
  constructor
  · have h0 : cs T (T.par v hv) = 0 := by
      unfold cs
      rw [Nat.find_eq_zero]
      simp only [Function.iterate_zero, id_eq, hpv, hvv]
      exact T.parent_mem_anc (T.mem_anc_self v)
    show T.parent^[cs T (T.par v hv)] (M.vert (M.α (T.par v hv))) = _
    rw [h0, hpv]; rfl
  · have h1 : cs T (M.α (T.par v hv)) = 1 := by
      unfold cs
      rw [Nat.find_eq_iff]
      simp only [M.α_α, hvv, hpv, Function.iterate_one, Nat.lt_one_iff, forall_eq,
        Function.iterate_zero, id_eq]
      exact ⟨T.mem_anc_self _, notMem_anc_parent hv⟩
    show T.parent^[cs T (M.α (T.par v hv))] (M.vert (M.α (M.α (T.par v hv)))) = _
    rw [h1, M.α_α, hvv]; rfl

/-- **For every dart**, `cycE` is the cycle of the dart with its two ends (for a tree dart the
cycle is empty and `cycE` is the edge). -/
lemma cycE_eq (δ : D) :
    cycE (T := T) δ = insert (M.vert δ) (insert (M.vert (M.α δ)) (T.cycV δ)) := by
  by_cases hnt : T.IsTree δ
  · rw [cycV_eq_empty hnt, insert_empty]
    obtain ⟨v, hv, rfl | rfl⟩ := hnt
    · have hpv : M.vert (M.α (T.par v hv)) = T.parent v := (T.parent_of_ne hv).symm
      have hvv : M.vert (T.par v hv) = v := T.vert_par v hv
      unfold cycE
      rw [(lca_par v hv).1, hvv, hpv, T.anc_of_ne hv]
      ext u
      simp only [mem_sdiff, mem_union, mem_insert, mem_erase, mem_singleton]
      constructor
      · rintro ⟨h, h'⟩
        by_contra hne; push Not at hne
        rcases h with (rfl | h) | h
        · exact hne.1 rfl
        · exact h' ⟨hne.2, h⟩
        · exact h' ⟨hne.2, h⟩
      · rintro (rfl | rfl)
        · exact ⟨Or.inl (Or.inl rfl), fun ⟨_, h⟩ => notMem_anc_parent hv h⟩
        · exact ⟨Or.inr (T.mem_anc_self _), fun ⟨h, _⟩ => h rfl⟩
    · have hpv : M.vert (M.α (T.par v hv)) = T.parent v := (T.parent_of_ne hv).symm
      have hvv : M.vert (M.α (M.α (T.par v hv))) = v := by rw [M.α_α, T.vert_par]
      unfold cycE
      rw [(lca_par v hv).2, hvv, hpv, T.anc_of_ne hv]
      ext u
      simp only [mem_sdiff, mem_union, mem_insert, mem_erase, mem_singleton]
      constructor
      · rintro ⟨h, h'⟩
        by_contra hne; push Not at hne
        rcases h with h | (rfl | h)
        · exact h' ⟨hne.1, h⟩
        · exact hne.2 rfl
        · exact h' ⟨hne.1, h⟩
      · rintro (rfl | rfl)
        · exact ⟨Or.inl (T.mem_anc_self _), fun ⟨h, _⟩ => h rfl⟩
        · exact ⟨Or.inr (Or.inl rfl), fun ⟨_, h⟩ => notMem_anc_parent hv h⟩
  · unfold cycE
    rw [← cycV_eq_anc hnt, insert_eq_of_mem (vert_α_mem_cycV hnt),
      insert_eq_of_mem (vert_mem_cycV hnt)]

omit [Fintype D] in
/-- **The weight of a fundamental cycle from root sums**: with `rs v = ∑ u ∈ anc v, w u`,
`W (cycV δ) = rs x + rs z - 2 rs l + w l`, `l` the lowest common ancestor of the ends `x`, `z`. -/
theorem sum_cycV {β : Type*} [AddCommGroup β] (w : P → β) {δ : D} (hnt : ¬ T.IsTree δ) :
    ∑ v ∈ T.cycV δ, w v = ∑ v ∈ T.anc (M.vert δ), w v + ∑ v ∈ T.anc (M.vert (M.α δ)), w v -
      2 • ∑ v ∈ T.anc (lca T δ), w v + w (lca T δ) := by
  rw [cycV_eq_anc hnt]
  have hsub : (T.anc (lca T δ)).erase (lca T δ) ⊆ T.anc (M.vert δ) ∪ T.anc (M.vert (M.α δ)) :=
    (erase_subset _ _).trans (fun u hu => mem_union_left _ (T.anc_subset_anc (lca_mem_anc δ) hu))
  have h1 := sum_sdiff hsub (f := w)
  have h2 := sum_union_inter (s₁ := T.anc (M.vert δ)) (s₂ := T.anc (M.vert (M.α δ))) (f := w)
  rw [anc_inter_anc] at h2
  have h3 := sum_erase_add _ w (T.mem_anc_self (lca T δ))
  rw [two_nsmul]
  have e : ∑ x ∈ (T.anc (M.vert δ) ∪ T.anc (M.vert (M.α δ))) \
      (T.anc (lca T δ)).erase (lca T δ), w x =
      ∑ x ∈ T.anc (M.vert δ) ∪ T.anc (M.vert (M.α δ)), w x -
        ∑ x ∈ (T.anc (lca T δ)).erase (lca T δ), w x := eq_sub_of_add_eq h1
  rw [e, eq_sub_of_add_eq h2, ← h3]
  abel

end Paths

/-! ### The weight of `bset` -/

section BsetWeight

variable {δ : D}

omit [Fintype D] [Fintype P] in
lemma mem_cycE {d : D} {v : P} : v ∈ cycE (T := T) d ↔
    (v ∈ T.anc (M.vert d) ∨ v ∈ T.anc (M.vert (M.α d))) ∧
      ¬ (v ∈ T.anc (lca T d) ∧ v ≠ lca T d) := by
  simp only [cycE, mem_sdiff, mem_union, mem_erase]
  tauto

omit [DecidableEq D] [DecidableEq P] [Fintype D] [Fintype P] in
lemma vert_a₂ (hδ : M.IsTriangle δ) : M.vert (M.α (M.φ (M.φ δ))) = M.vert δ := by
  rw [← M.vert_φ, hδ.φ_three]

variable (hM : M.IsPlane) (hδ : M.IsTriangle δ) (hnt : ¬ T.IsTree δ)
include hM hδ hnt

/-- `bset δ` through the sets `cycE` of the three darts: no case on tree darts. -/
lemma mem_bset_iff {v : P} : v ∈ bset δ (T := T) ↔
    (v = M.vert (M.φ (M.φ δ)) ∨ v ∈ cycE (T := T) (M.α (M.φ δ)) ∨
        v ∈ cycE (T := T) (M.α (M.φ (M.φ δ)))) ∧ v ∉ cycE (T := T) δ := by
  have hx := vert_mem_cycV (T := T) hnt
  have hz := vert_α_mem_cycV (T := T) hnt
  have ey : M.vert (M.α (M.φ δ)) = M.vert (M.φ (M.φ δ)) := (M.vert_φ _).symm
  have ez : M.vert (M.α (M.α (M.φ δ))) = M.vert (M.α δ) := by rw [M.α_α, M.vert_φ]
  have ex : M.vert (M.α (M.φ (M.φ δ))) = M.vert δ := vert_a₂ hδ
  have ey' : M.vert (M.α (M.α (M.φ (M.φ δ)))) = M.vert (M.φ (M.φ δ)) := by rw [M.α_α]
  rw [bset_eq hM hδ hnt, cycE_eq, cycE_eq, cycE_eq, ey, ez, ex, ey',
    insert_eq_of_mem hz, insert_eq_of_mem hx]
  simp only [mem_sdiff, mem_insert, mem_union]
  constructor
  · rintro ⟨h, h'⟩
    refine ⟨?_, h'⟩
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rintro ⟨h, h'⟩
    refine ⟨?_, h'⟩
    rcases h with h | (h | h | h) | (h | h | h)
    · exact Or.inl h
    · exact Or.inl h
    · exact absurd (h ▸ hz) h'
    · exact Or.inr (Or.inl h)
    · exact absurd (h ▸ hx) h'
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- **The weight of `bset δ` from root sums.** Let `p`, `q`, `r` be the lowest common ancestors
of the corners `x z`, `x y`, `y z` of the triangle of `δ` (those of `δ`, `a₂`, `a₁`), and `rs v`
the weight of the root path of `v`. By `tripod`, two of `p`, `q`, `r` coincide and are ancestors
of the third, the *center*; then `bset δ` is the path from `y` up to the center (excluded) when
the center is `q` or `r`, and that path with the segment strictly above `p` up to `q = r` when
the center is `p`. -/
theorem sum_bset {β : Type*} [AddCommGroup β] (w : P → β) :
    let rs : P → β := fun v => ∑ u ∈ T.anc v, w u
    let p := lca T δ
    let q := lca T (M.α (M.φ (M.φ δ)))
    let r := lca T (M.α (M.φ δ))
    let y := M.vert (M.φ (M.φ δ))
    (q = r ∧ q ∈ T.anc p ∧
        ∑ v ∈ bset δ (T := T), w v = rs y - rs q + ((rs p - w p) - (rs q - w q))) ∨
      (p = r ∧ p ∈ T.anc q ∧ ∑ v ∈ bset δ (T := T), w v = rs y - rs q) ∨
      (p = q ∧ p ∈ T.anc r ∧ ∑ v ∈ bset δ (T := T), w v = rs y - rs r) := by
  intro rs p q r y
  set x := M.vert δ
  set z := M.vert (M.α δ)
  have ex : M.vert (M.α (M.φ (M.φ δ))) = x := vert_a₂ hδ
  have ey : M.vert (M.α (M.α (M.φ (M.φ δ)))) = y := by rw [M.α_α]
  have ey' : M.vert (M.α (M.φ δ)) = y := (M.vert_φ _).symm
  have ez : M.vert (M.α (M.α (M.φ δ))) = z := by rw [M.α_α, M.vert_φ]
  have hP : ∀ u, u ∈ T.anc p ↔ u ∈ T.anc x ∧ u ∈ T.anc z := fun u => mem_anc_lca_iff δ
  have hQ : ∀ u, u ∈ T.anc q ↔ u ∈ T.anc x ∧ u ∈ T.anc y := fun u => by
    rw [mem_anc_lca_iff, ex, ey]
  have hR : ∀ u, u ∈ T.anc r ↔ u ∈ T.anc y ∧ u ∈ T.anc z := fun u => by
    rw [mem_anc_lca_iff, ey', ez]
  have mem : ∀ v, v ∈ bset δ (T := T) ↔
      (v = y ∨ ((v ∈ T.anc y ∨ v ∈ T.anc z) ∧ ¬ (v ∈ T.anc r ∧ v ≠ r)) ∨
        ((v ∈ T.anc x ∨ v ∈ T.anc y) ∧ ¬ (v ∈ T.anc q ∧ v ≠ q))) ∧
      ¬ ((v ∈ T.anc x ∨ v ∈ T.anc z) ∧ ¬ (v ∈ T.anc p ∧ v ≠ p)) := fun v => by
    rw [mem_bset_iff hM hδ hnt, mem_cycE, mem_cycE, mem_cycE, ex, ey, ey', ez]
  have antisymm : ∀ {u v : P}, u ∈ T.anc v → v ∈ T.anc u → u = v :=
    fun h h' => T.eq_of_mem_anc_of_mem_anc h h'
  have tr : ∀ {u v w : P}, u ∈ T.anc v → v ∈ T.anc w → u ∈ T.anc w :=
    fun huv hvw => T.anc_subset_anc hvw huv
  have yy : y ∈ T.anc y := T.mem_anc_self y
  have qy : q ∈ T.anc y := ((hQ q).1 (T.mem_anc_self q)).2
  have ry : r ∈ T.anc y := ((hR r).1 (T.mem_anc_self r)).1
  -- the weight of the path from `y` up to an ancestor `c` excluded
  have path : ∀ c, c ∈ T.anc y → ∑ v ∈ (T.anc y).filter (fun v => v ∉ T.anc c), w v =
      rs y - rs c := fun c hc => by
    have hsub : T.anc c ⊆ T.anc y := T.anc_subset_anc hc
    have e : (T.anc y).filter (fun v => v ∉ T.anc c) = T.anc y \ T.anc c := by
      ext v; simp [mem_sdiff]
    rw [e]
    exact eq_sub_of_add_eq (sum_sdiff hsub)
  have rsdef : ∀ v, rs v = ∑ u ∈ T.anc v, w u := fun _ => rfl
  have trip : (q = r ∧ q ∈ T.anc p) ∨ (p = r ∧ p ∈ T.anc q) ∨ (p = q ∧ p ∈ T.anc r) :=
    tripod (T := T) (rfl : M.vert δ = x) (rfl : M.vert (M.α δ) = z) ex ey ey' ez
  clear_value rs p q r
  rcases trip with
    ⟨hqr, hqp⟩ | ⟨hpr, hpq⟩ | ⟨hpq, hpr⟩
  · -- center `p`, top `q = r`
    left
    refine ⟨hqr, hqp, ?_⟩
    subst hqr
    have hqp' : T.anc q ⊆ T.anc p := T.anc_subset_anc hqp
    have hb : bset δ (T := T) = (T.anc y).filter (fun v => v ∉ T.anc q) ∪
        ((T.anc p).erase p \ (T.anc q).erase q) := by
      ext v
      rw [mem (v := v), mem_union, mem_filter, mem_sdiff, mem_erase, mem_erase]
      constructor
      · rintro ⟨h, h'⟩
        by_cases hY : v ∈ T.anc y
        · by_cases hq : v ∈ T.anc q
          · right
            -- `v` above `q`, so on the root paths of `x` and `z`; off the cycle of `δ`
            have hvx := ((hQ v).1 hq).1
            have hvp : v ∈ T.anc p ∧ v ≠ p := by
              by_contra hc; exact h' ⟨Or.inl hvx, hc⟩
            refine ⟨⟨hvp.2, hvp.1⟩, fun ⟨hne, _⟩ => ?_⟩
            rcases h with rfl | ⟨_, h⟩ | ⟨_, h⟩
            · exact hne (antisymm hq qy)
            · exact h ⟨hq, hne⟩
            · exact h ⟨hq, hne⟩
          · exact Or.inl ⟨hY, hq⟩
        · -- off the root path of `y`: on that of `x` or `z`, hence strictly above `p`
          have hxz : v ∈ T.anc x ∨ v ∈ T.anc z := by
            rcases h with rfl | ⟨h, _⟩ | ⟨h, _⟩
            · exact absurd yy hY
            · exact Or.inr (h.resolve_left hY)
            · exact Or.inl (h.resolve_right hY)
          have hvp : v ∈ T.anc p ∧ v ≠ p := by
            by_contra hc; exact h' ⟨hxz, hc⟩
          right
          refine ⟨⟨hvp.2, hvp.1⟩, fun ⟨_, hq⟩ => hY (tr hq qy)⟩
      · rintro (⟨hY, hq⟩ | ⟨⟨hne, hp⟩, hq⟩)
        · refine ⟨Or.inr (Or.inl ⟨Or.inl hY, fun ⟨hr, _⟩ => hq hr⟩), fun ⟨hxz, hc⟩ => ?_⟩
          rcases hxz with hX | hZ
          · exact hq ((hQ v).2 ⟨hX, hY⟩)
          · exact hq ((hR v).2 ⟨hY, hZ⟩)
        · have hvx := ((hP v).1 hp).1
          refine ⟨Or.inr (Or.inr ⟨Or.inl hvx, fun ⟨h1, h2⟩ => hq ⟨h2, h1⟩⟩),
            fun ⟨_, hc⟩ => hc ⟨hp, hne⟩⟩
    -- the two parts are disjoint
    have hd : Disjoint ((T.anc y).filter (fun v => v ∉ T.anc q))
        ((T.anc p).erase p \ (T.anc q).erase q) := by
      rw [disjoint_left]
      intro v h1 h2
      rw [mem_filter] at h1
      rw [mem_sdiff, mem_erase] at h2
      exact h1.2 ((hQ v).2 ⟨((hP v).1 h2.1.2).1, h1.1⟩)
    have hsub : (T.anc q).erase q ⊆ (T.anc p).erase p := by
      intro u hu
      rw [mem_erase] at hu ⊢
      refine ⟨fun e => hu.1 ?_, hqp' hu.2⟩
      subst e; exact antisymm hu.2 hqp
    have hseg : ∑ v ∈ (T.anc p).erase p \ (T.anc q).erase q, w v =
        (rs p - w p) - (rs q - w q) := by
      rw [eq_sub_of_add_eq (sum_sdiff hsub (f := w))]
      have e1 := sum_erase_add _ w (T.mem_anc_self p)
      have e2 := sum_erase_add _ w (T.mem_anc_self q)
      rw [rsdef, rsdef, ← e1, ← e2]
      abel
    rw [hb, sum_union hd, path q qy, hseg]
  · -- center `q`
    right; left
    refine ⟨hpr, hpq, ?_⟩
    have hb : bset δ (T := T) = (T.anc y).filter (fun v => v ∉ T.anc q) := by
      ext v
      rw [mem (v := v), mem_filter]
      have hPQ : v ∈ T.anc p → v ∈ T.anc q := fun h => tr h hpq
      have hRP : v ∈ T.anc r ↔ v ∈ T.anc p := by rw [hpr]
      constructor
      · rintro ⟨h, h'⟩
        have hY : v ∈ T.anc y := by
          rcases h with rfl | ⟨h, hn⟩ | ⟨h, hn⟩
          · exact yy
          · rcases h with h | hZ
            · exact h
            · have hvp : v ∈ T.anc p ∧ v ≠ p := by
                by_contra hc; exact h' ⟨Or.inr hZ, hc⟩
              exact absurd ⟨hRP.2 hvp.1, by rw [← hpr]; exact hvp.2⟩ hn
          · rcases h with hX | h
            · have hvp : v ∈ T.anc p ∧ v ≠ p := by
                by_contra hc; exact h' ⟨Or.inl hX, hc⟩
              have hvq : v = q := by by_contra hc; exact hn ⟨hPQ hvp.1, hc⟩
              exact absurd (antisymm hpq (show q ∈ T.anc p by rw [← hvq]; exact hvp.1))
                (fun e => hvp.2 (hvq.trans e.symm))
            · exact h
        refine ⟨hY, fun hq => ?_⟩
        have hvx := ((hQ v).1 hq).1
        have hvp : v ∈ T.anc p ∧ v ≠ p := by
          by_contra hc; exact h' ⟨Or.inl hvx, hc⟩
        have hvq : v ≠ q := fun e => hvp.2 (antisymm hvp.1 (by rw [e]; exact hpq))
        rcases h with rfl | ⟨_, hn⟩ | ⟨_, hn⟩
        · exact hvq (antisymm hq qy)
        · exact hn ⟨hRP.2 hvp.1, by rw [← hpr]; exact hvp.2⟩
        · exact hn ⟨hq, hvq⟩
      · rintro ⟨hY, hq⟩
        have hnp : v ∉ T.anc p := fun h => hq (hPQ h)
        refine ⟨Or.inr (Or.inl ⟨Or.inl hY, fun ⟨h, _⟩ => hnp (hRP.1 h)⟩), fun ⟨hxz, _⟩ => ?_⟩
        rcases hxz with hX | hZ
        · exact hq ((hQ v).2 ⟨hX, hY⟩)
        · exact hnp (hRP.1 ((hR v).2 ⟨hY, hZ⟩))
    rw [hb, path q qy]
  · -- center `r`
    right; right
    refine ⟨hpq, hpr, ?_⟩
    have hb : bset δ (T := T) = (T.anc y).filter (fun v => v ∉ T.anc r) := by
      ext v
      rw [mem (v := v), mem_filter]
      have hPR : v ∈ T.anc p → v ∈ T.anc r := fun h => tr h hpr
      have hQP : v ∈ T.anc q ↔ v ∈ T.anc p := by rw [hpq]
      constructor
      · rintro ⟨h, h'⟩
        have hY : v ∈ T.anc y := by
          rcases h with rfl | ⟨h, hn⟩ | ⟨h, hn⟩
          · exact yy
          · rcases h with h | hZ
            · exact h
            · have hvp : v ∈ T.anc p ∧ v ≠ p := by
                by_contra hc; exact h' ⟨Or.inr hZ, hc⟩
              have hvr : v = r := by by_contra hc; exact hn ⟨hPR hvp.1, hc⟩
              exact absurd (antisymm hpr (show r ∈ T.anc p by rw [← hvr]; exact hvp.1))
                (fun e => hvp.2 (hvr.trans e.symm))
          · rcases h with hX | h
            · have hvp : v ∈ T.anc p ∧ v ≠ p := by
                by_contra hc; exact h' ⟨Or.inl hX, hc⟩
              exact absurd ⟨hQP.2 hvp.1, by rw [← hpq]; exact hvp.2⟩ hn
            · exact h
        refine ⟨hY, fun hr => ?_⟩
        have hvz := ((hR v).1 hr).2
        have hvp : v ∈ T.anc p ∧ v ≠ p := by
          by_contra hc; exact h' ⟨Or.inr hvz, hc⟩
        have hvr : v ≠ r := fun e => hvp.2 (antisymm hvp.1 (by rw [e]; exact hpr))
        rcases h with rfl | ⟨_, hn⟩ | ⟨_, hn⟩
        · exact hvr (antisymm hr ry)
        · exact hn ⟨hr, hvr⟩
        · exact hn ⟨hQP.2 hvp.1, by rw [← hpq]; exact hvp.2⟩
      · rintro ⟨hY, hr⟩
        have hnp : v ∉ T.anc p := fun h => hr (hPR h)
        refine ⟨Or.inr (Or.inl ⟨Or.inl hY, fun ⟨h, _⟩ => hr h⟩), fun ⟨hxz, _⟩ => ?_⟩
        rcases hxz with hX | hZ
        · exact hnp (hQP.1 ((hQ v).2 ⟨hX, hY⟩))
        · exact hr ((hR v).2 ⟨hY, hZ⟩)
    rw [hb, path r ry]

end BsetWeight

end SpTree

end Map

end PlanarSeparator
