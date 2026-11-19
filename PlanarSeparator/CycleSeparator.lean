module

public import PlanarSeparator.SimpleCycle

/-!
# Simple cycle separators of triangulations

Let `M` be a plane map all of whose faces are triangles, `T` a spanning tree of `M` and `w`
nonnegative weights on the vertices of total at most `1`. Then some dart `δ` off the tree has a
fundamental cycle — a **simple cycle** (`PlanarSeparator.Map.SpTree.fcycle`) — such that the
vertices *strictly* inside the cycle and the vertices *strictly* outside the cycle weigh at most
`2/3` each, and no edge joins a vertex strictly inside to one strictly outside
(`PlanarSeparator.Map.SpTree.exists_simple_cycle_separator`). The cycle has at most
`#anc x + #anc z - 1` darts, where `x`, `z` are the ends of `δ`; for a breadth-first search tree
of radius `h` this is at most `2 h + 1`.

This is the first step of Miller's simple cycle separator theorem (G. L. Miller, *Finding small
simple cycle separators for 2-connected planar graphs*, J. Comput. Syst. Sci. 32 (1986), 265–279,
§2): a balanced fundamental cycle of a triangulation. Unlike the cycle separator lemma of
Lipton and Tarjan (`PlanarSeparator.Map.SpTree.exists_balanced`), whose separator consists of the
two whole root paths of `δ`, the separator here is the cycle itself: the part of the root paths
above the lowest common ancestor of `x` and `z` lies strictly on one side and is counted there.

## The proof

The vertices of the cycle are the vertices met by the fundamental cochain (`cycV δ`). A vertex off
the cycle has all its faces on one side, which defines the vertices strictly inside (`inC δ`) and
strictly outside (`outC δ`). As in the lemma of Lipton and Tarjan we start from a dart whose
inside is too heavy and pass to one of the reversals `a₁ = α (φ δ)`, `a₂ = α (φ² δ)` of the other
two darts of its triangle `x z y`. Their fundamental cochains add up to that of `δ` and the three
edges of the triangle; hence a vertex other than `x, y, z` and off the cycle of `δ` lies on the
cycle of `a₁` if and only if it lies on the cycle of `a₂`. The vertices strictly inside `δ` are
strictly inside `a₁` or `a₂`, or lie on both cycles (or are `y`), and passing to the heavier of
`a₁, a₂` either keeps the inside too heavy, with fewer faces, or gives a balanced cycle.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

open Finset

namespace Map

namespace SpTree

variable {D P : Type*} {M : Map D P} (T : SpTree M) [DecidableEq D] [DecidableEq P] [Fintype D]
  [Fintype P]

/-! ### The two strict sides of a fundamental cycle -/

/-- The vertices strictly inside the fundamental cycle of `δ`. -/
noncomputable def inC (δ : D) : Finset P :=
  {v | v ∉ T.cycV δ ∧ ∃ d, M.vert d = v ∧ M.face d ∈ T.inside δ}

/-- The vertices strictly outside the fundamental cycle of `δ`. -/
noncomputable def outC (δ : D) : Finset P := {v | v ∉ T.cycV δ ∧ v ∉ T.inC δ}

variable {T}

lemma notMem_cycV_of_mem_inC {δ : D} {v : P} (h : v ∈ T.inC δ) : v ∉ T.cycV δ :=
  (mem_filter.1 h).2.1

lemma fund_eq_zero_of_notMem_cycV {δ d : D} (h : M.vert d ∉ T.cycV δ) : T.fund δ d = 0 := by
  by_contra h'
  exact h ((T.mem_cycV).2 ⟨d, rfl, h'⟩)

/-- Around a vertex off the cycle all faces lie on the same side. -/
lemma face_iff_of_notMem_cycV (hM : M.IsPlane) {δ : D} {v : P} (hv : v ∉ T.cycV δ) {d d' : D}
    (hd : M.vert d = v) (hd' : M.vert d' = v) :
    M.face d ∈ T.inside δ ↔ M.face d' ∈ T.inside δ := by
  obtain ⟨n, rfl⟩ := M.exists_σ_pow_eq (hd.trans hd'.symm)
  clear hd'
  induction n with
  | zero => rfl
  | succ n ih =>
    have hx : T.fund δ ((M.σ ^ n) d) = 0 :=
      fund_eq_zero_of_notMem_cycV (by rwa [M.vert_σ_pow, hd])
    rw [pow_succ', Equiv.Perm.mul_apply, face_σ, ← (inside_iff hM δ _).2 hx]
    exact ih

lemma mem_inC_iff (hM : M.IsPlane) {δ d : D} {v : P} (hv : v ∉ T.cycV δ) (hd : M.vert d = v) :
    v ∈ T.inC δ ↔ M.face d ∈ T.inside δ := by
  simp only [inC, mem_filter, mem_univ, true_and, hv, not_false_eq_true]
  constructor
  · rintro ⟨d', hd', h⟩
    exact (face_iff_of_notMem_cycV hM hv hd' hd).1 h
  · exact fun h => ⟨d, hd, h⟩

/-- **Separation.** No edge joins a vertex strictly inside the cycle of `δ` to a vertex strictly
outside. -/
theorem vert_α_notMem_outC (hM : M.IsPlane) {δ d : D} (hd : M.vert d ∈ T.inC δ) :
    M.vert (M.α d) ∉ T.outC δ := by
  intro hv
  have hus := notMem_cycV_of_mem_inC hd
  obtain ⟨hvs, hvi⟩ := (mem_filter.1 hv).2
  have h1 := (mem_inC_iff hM hus rfl).1 hd
  exact hvi ((mem_inC_iff hM hvs rfl).2
    (((inside_iff hM δ d).2 (fund_eq_zero_of_notMem_cycV hus)).1 h1))

variable (T) in
lemma outC_eq (δ : D) : T.outC δ = (T.cycV δ)ᶜ \ T.inC δ := by
  ext v
  simp [outC]

variable (T) in
lemma inC_subset (δ : D) : T.inC δ ⊆ (T.cycV δ)ᶜ := fun _ h =>
  mem_compl.2 (notMem_cycV_of_mem_inC h)

variable (T) in
/-- The cycle and its two strict sides partition the vertices. -/
lemma sum_inC_add_sum_outC (w : P → ℝ) (δ : D) :
    ∑ v ∈ T.inC δ, w v + ∑ v ∈ T.outC δ, w v + ∑ v ∈ T.cycV δ, w v = ∑ v, w v := by
  rw [T.outC_eq, add_comm (∑ v ∈ T.inC δ, w v), sum_sdiff (T.inC_subset δ), add_comm,
    sum_add_sum_compl]

lemma inC_α (hM : M.IsPlane) {δ : D} (h : ¬ T.IsTree δ) : T.inC (M.α δ) = T.outC δ := by
  ext v
  by_cases hv : v ∈ T.cycV δ
  · simp [inC, outC, T.cycV_α, hv]
  · obtain ⟨d, hd⟩ := hM.exists_dart v
    have hv' : v ∉ T.cycV (M.α δ) := by rwa [T.cycV_α]
    rw [mem_inC_iff hM hv' hd, inside_α hM h, mem_compl]
    simp only [outC, mem_filter, mem_univ, true_and, hv, not_false_eq_true,
      mem_inC_iff hM hv hd]

lemma inC_eq_empty (hM : M.IsPlane) {δ : D} (h : T.IsTree δ) : T.inC δ = ∅ := by
  ext v
  simp [inC, inside_eq_empty hM h]

lemma cycV_eq_empty {δ : D} (h : T.IsTree δ) : T.cycV δ = ∅ := by
  ext v
  simp [mem_cycV, T.fund_of_isTree h]

lemma vert_mem_cycV {δ : D} (h : ¬ T.IsTree δ) : M.vert δ ∈ T.cycV δ :=
  (T.mem_cycV).2 ⟨δ, rfl, by rw [T.fund_self h]; exact one_ne_zero⟩

lemma vert_α_mem_cycV {δ : D} (h : ¬ T.IsTree δ) : M.vert (M.α δ) ∈ T.cycV δ :=
  (T.mem_cycV).2 ⟨M.α δ, rfl, by rw [T.fund_α_apply, T.fund_self h]; exact one_ne_zero⟩

/-! ### Triangles -/

section Triangle

variable {δ : D} (hδ : M.IsTriangle δ) (hnt : ¬ T.IsTree δ)

/-- The fundamental cochains of a dart and of the reversals of the two other darts of its
triangle add up to the three edges of the triangle. -/
lemma fund_add_fund_add_fund (hδ : M.IsTriangle δ) (d : D) :
    T.fund δ d + T.fund (M.α (M.φ δ)) d + T.fund (M.α (M.φ (M.φ δ))) d =
      M.edgeInd δ d + M.edgeInd (M.φ δ) d + M.edgeInd (M.φ (M.φ δ)) d := by
  have hz : M.vert (M.φ δ) = M.vert (M.α δ) := M.vert_φ δ
  have hy : M.vert (M.α (M.φ δ)) = M.vert (M.φ (M.φ δ)) := (M.vert_φ _).symm
  have hx : M.vert (M.α (M.φ (M.φ δ))) = M.vert δ := by rw [← M.vert_φ, hδ.φ_three]
  simp only [fund_apply, edgeInd_of_α, M.α_α, hz, hy, hx]
  generalize M.edgeInd δ d = a
  generalize M.edgeInd (M.φ δ) d = b
  generalize M.edgeInd (M.φ (M.φ δ)) d = c
  generalize T.pathC (M.vert δ) d = p
  generalize T.pathC (M.vert (M.α δ)) d = q
  generalize T.pathC (M.vert (M.φ (M.φ δ))) d = r
  revert a b c p q r
  decide

include hδ in
/-- Off the three corners and off the cycle of `δ`, the cycles of `a₁` and `a₂` meet the same
vertices. -/
lemma mem_cycV_a₁_iff {v : P} (hv : v ∉ T.cycV δ) (hx : v ≠ M.vert δ) (hz : v ≠ M.vert (M.α δ))
    (hy : v ≠ M.vert (M.φ (M.φ δ))) :
    v ∈ T.cycV (M.α (M.φ δ)) ↔ v ∈ T.cycV (M.α (M.φ (M.φ δ))) := by
  have key : ∀ d, M.vert d = v → T.fund (M.α (M.φ δ)) d = T.fund (M.α (M.φ (M.φ δ))) d := by
    intro d hd
    have h := T.fund_add_fund_add_fund hδ d
    have h0 : T.fund δ d = 0 := fund_eq_zero_of_notMem_cycV (hd ▸ hv)
    have e : ∀ c, M.vert c ≠ v → M.vert (M.α c) ≠ v → M.edgeInd c d = 0 := fun c h1 h2 =>
      edgeInd_eq_zero (fun h => h1 (h ▸ hd)) (fun h => h2 (h ▸ hd))
    rw [h0, e δ (Ne.symm hx) (Ne.symm hz),
      e (M.φ δ) (by rw [M.vert_φ]; exact Ne.symm hz) (by rw [← M.vert_φ]; exact Ne.symm hy),
      e (M.φ (M.φ δ)) (Ne.symm hy) (by rw [← M.vert_φ, hδ.φ_three]; exact Ne.symm hx)] at h
    revert h
    generalize T.fund (M.α (M.φ δ)) d = a
    generalize T.fund (M.α (M.φ (M.φ δ))) d = b
    revert a b
    decide
  simp only [mem_cycV]
  constructor
  · rintro ⟨d, hd, h⟩
    exact ⟨d, hd, by rwa [← key d hd]⟩
  · rintro ⟨d, hd, h⟩
    exact ⟨d, hd, by rwa [key d hd]⟩

lemma y_mem_cycV_a₁ (h : ¬ T.IsTree (M.α (M.φ δ))) :
    M.vert (M.φ (M.φ δ)) ∈ T.cycV (M.α (M.φ δ)) := by
  have := vert_mem_cycV (T := T) h
  rwa [← M.vert_φ] at this

include hδ in
lemma y_mem_cycV_a₂ (h : ¬ T.IsTree (M.α (M.φ (M.φ δ)))) :
    M.vert (M.φ (M.φ δ)) ∈ T.cycV (M.α (M.φ (M.φ δ))) := by
  have := vert_α_mem_cycV (T := T) h
  rwa [M.α_α] at this

/-- The vertices strictly inside `δ` which lie on the cycle of `a₁` or `a₂`, or are `y`. -/
noncomputable def bset (δ : D) : Finset P :=
  T.inC δ ∩ insert (M.vert (M.φ (M.φ δ))) (T.cycV (M.α (M.φ δ)) ∪ T.cycV (M.α (M.φ (M.φ δ))))

include hδ hnt in
lemma bset_subset₁ (h : ¬ T.IsTree (M.α (M.φ δ))) : bset δ (T := T) ⊆ T.cycV (M.α (M.φ δ)) := by
  intro v hv
  obtain ⟨hvi, hv⟩ := mem_inter.1 hv
  have hvc := notMem_cycV_of_mem_inC hvi
  rcases mem_insert.1 hv with rfl | hv
  · exact y_mem_cycV_a₁ h
  · by_cases hy : v = M.vert (M.φ (M.φ δ))
    · subst hy; exact y_mem_cycV_a₁ h
    have hx : v ≠ M.vert δ := fun e => hvc (e ▸ vert_mem_cycV hnt)
    have hz : v ≠ M.vert (M.α δ) := fun e => hvc (e ▸ vert_α_mem_cycV hnt)
    rcases mem_union.1 hv with hv | hv
    · exact hv
    · exact (mem_cycV_a₁_iff hδ hvc hx hz hy).2 hv

include hδ hnt in
lemma bset_subset₂ (h : ¬ T.IsTree (M.α (M.φ (M.φ δ)))) :
    bset δ (T := T) ⊆ T.cycV (M.α (M.φ (M.φ δ))) := by
  intro v hv
  obtain ⟨hvi, hv⟩ := mem_inter.1 hv
  have hvc := notMem_cycV_of_mem_inC hvi
  rcases mem_insert.1 hv with rfl | hv
  · exact y_mem_cycV_a₂ hδ h
  · by_cases hy : v = M.vert (M.φ (M.φ δ))
    · subst hy; exact y_mem_cycV_a₂ hδ h
    have hx : v ≠ M.vert δ := fun e => hvc (e ▸ vert_mem_cycV hnt)
    have hz : v ≠ M.vert (M.α δ) := fun e => hvc (e ▸ vert_α_mem_cycV hnt)
    rcases mem_union.1 hv with hv | hv
    · exact (mem_cycV_a₁_iff hδ hvc hx hz hy).1 hv
    · exact hv

include hδ hnt in
/-- The vertices strictly inside `δ` are strictly inside `a₁` or `a₂`, or lie in `bset δ`. -/
lemma inC_subset_union (hM : M.IsPlane) :
    T.inC δ ⊆ T.inC (M.α (M.φ δ)) ∪ T.inC (M.α (M.φ (M.φ δ))) ∪ bset δ (T := T) := by
  intro v hv
  by_cases hB : v ∈ bset δ (T := T)
  · exact mem_union_right _ hB
  apply mem_union_left
  have hvc := notMem_cycV_of_mem_inC hv
  have hB' : v ≠ M.vert (M.φ (M.φ δ)) ∧ v ∉ T.cycV (M.α (M.φ δ)) ∧
      v ∉ T.cycV (M.α (M.φ (M.φ δ))) := by
    simpa [bset, hv] using hB
  obtain ⟨d, hd, hdX⟩ := (mem_filter.1 hv).2.2
  have hf : M.face d ≠ M.face δ := fun hfd => by
    rcases M.eq_of_face_eq_of_φ_three hδ.φ_three hfd with rfl | rfl | rfl
    · exact hvc (hd ▸ vert_mem_cycV hnt)
    · exact hvc (by rw [← hd, M.vert_φ]; exact vert_α_mem_cycV hnt)
    · exact hB'.1 hd.symm
  have := inside_subset hM hδ hnt hdX
  rw [mem_insert, mem_union] at this
  rcases this with h | h | h
  · exact absurd h hf
  · exact mem_union_left _ ((mem_inC_iff hM hB'.2.1 hd).2 h)
  · exact mem_union_right _ ((mem_inC_iff hM hB'.2.2 hd).2 h)

include hδ hnt in
/-- If both other darts of the triangle are tree darts, `bset δ` is empty. -/
lemma bset_eq_empty (h₁ : T.IsTree (M.α (M.φ δ))) (h₂ : T.IsTree (M.α (M.φ (M.φ δ)))) :
    bset δ (T := T) = ∅ := by
  ext v
  simp only [bset, notMem_empty, iff_false, mem_inter, mem_insert, mem_union,
    cycV_eq_empty h₁, cycV_eq_empty h₂, notMem_empty, or_false, not_and]
  rintro hv rfl
  apply notMem_cycV_of_mem_inC hv
  refine (T.mem_cycV).2 ⟨M.φ (M.φ δ), rfl, ?_⟩
  have h := T.fund_add_fund_add_fund hδ (M.φ (M.φ δ))
  rw [T.fund_of_isTree h₁, T.fund_of_isTree h₂, Pi.zero_apply, add_zero, add_zero, edgeInd_self,
    edgeInd_eq_zero (ne_of_edge_ne hδ.edge_ne₂.symm).1 (ne_of_edge_ne hδ.edge_ne₂.symm).2.1,
    edgeInd_eq_zero (ne_of_edge_ne hδ.edge_ne₃.symm).1 (ne_of_edge_ne hδ.edge_ne₃.symm).2.1,
    zero_add, zero_add] at h
  rw [h]
  exact one_ne_zero

end Triangle

/-! ### The balanced simple cycle -/

/-- The recursive step: from a dart whose strict inside is too heavy one reaches a balanced dart
off the tree. -/
theorem exists_simple_balanced_of_lt (hM : M.IsPlane) (hT : ∀ δ, M.IsTriangle δ) {w : P → ℝ}
    (hw : ∀ v, 0 ≤ w v) (h1 : ∑ v, w v ≤ 1) :
    ∀ n, ∀ δ, #(T.inside δ) = n → 2 / 3 < ∑ v ∈ T.inC δ, w v →
      ∃ δ', ¬ T.IsTree δ' ∧ ∑ v ∈ T.inC δ', w v ≤ 2 / 3 ∧ ∑ v ∈ T.outC δ', w v ≤ 2 / 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro δ hn hI
  have hnt : ¬ T.IsTree δ := by
    intro h
    rw [inC_eq_empty hM h, sum_empty] at hI
    norm_num at hI
  have hδ := hT δ
  set W : Finset P → ℝ := fun s => ∑ v ∈ s, w v with hW
  have hWmono : ∀ s t, s ⊆ t → W s ≤ W t := fun s t hst =>
    sum_le_sum_of_subset_of_nonneg hst fun v _ _ => hw v
  have hW0 : ∀ s, 0 ≤ W s := fun s => sum_nonneg fun v _ => hw v
  have hcover : W (T.inC δ) ≤ W (T.inC (M.α (M.φ δ))) + W (T.inC (M.α (M.φ (M.φ δ)))) +
      W (bset δ (T := T)) :=
    (hWmono _ _ (inC_subset_union hδ hnt hM)).trans ((sum_union_le hw).trans
      (add_le_add_left (sum_union_le hw) _))
  have hX := face_mem_inside (T := T) hM hnt
  have hlt₁ : #(T.inside (M.α (M.φ δ))) < n := hn ▸ (card_le_card (inside_α_subset hM hnt
    (M.face_φ δ) hδ.edge_ne₁)).trans_lt (card_erase_lt_of_mem hX)
  have hlt₂ : #(T.inside (M.α (M.φ (M.φ δ)))) < n := hn ▸ (card_le_card (inside_α_subset hM hnt
    ((M.face_φ _).trans (M.face_φ δ)) hδ.edge_ne₂)).trans_lt (card_erase_lt_of_mem hX)
  -- passing to a heaviest dart `a` off the tree among `a₁`, `a₂` whose cycle contains `bset δ`
  have step : ∀ a, ¬ T.IsTree a → #(T.inside a) < n → bset δ (T := T) ⊆ T.cycV a →
      W (T.inC (M.α (M.φ δ))) ≤ W (T.inC a) → W (T.inC (M.α (M.φ (M.φ δ)))) ≤ W (T.inC a) →
      ∃ δ', ¬ T.IsTree δ' ∧ ∑ v ∈ T.inC δ', w v ≤ 2 / 3 ∧ ∑ v ∈ T.outC δ', w v ≤ 2 / 3 := by
    intro a ha hlt hB hle₁ hle₂
    by_cases hh : 2 / 3 < W (T.inC a)
    · exact ih _ hlt a rfl hh
    · refine ⟨a, ha, not_lt.1 hh, ?_⟩
      have hsum := T.sum_inC_add_sum_outC w a
      have := hWmono _ _ hB
      have := hW0 (bset δ (T := T))
      change W (T.inC a) + W (T.outC a) + W (T.cycV a) = W univ at hsum
      change W (T.outC a) ≤ 2 / 3
      change 2 / 3 < W (T.inC δ) at hI
      have : W univ ≤ 1 := h1
      linarith
  by_cases ht₁ : T.IsTree (M.α (M.φ δ))
  · by_cases ht₂ : T.IsTree (M.α (M.φ (M.φ δ)))
    · exfalso
      rw [bset_eq_empty hδ hnt ht₁ ht₂, inC_eq_empty hM ht₁, inC_eq_empty hM ht₂] at hcover
      change 2 / 3 < W (T.inC δ) at hI
      simp only [W, sum_empty] at hcover
      linarith
    · refine step _ ht₂ hlt₂ (bset_subset₂ hδ hnt ht₂) ?_ le_rfl
      rw [inC_eq_empty hM ht₁]
      exact hW0 _
  · by_cases ht₂ : T.IsTree (M.α (M.φ (M.φ δ)))
    · refine step _ ht₁ hlt₁ (bset_subset₁ hδ hnt ht₁) le_rfl ?_
      rw [inC_eq_empty hM ht₂]
      exact hW0 _
    · rcases le_total (W (T.inC (M.α (M.φ (M.φ δ))))) (W (T.inC (M.α (M.φ δ)))) with h | h
      · exact step _ ht₁ hlt₁ (bset_subset₁ hδ hnt ht₁) le_rfl h
      · exact step _ ht₂ hlt₂ (bset_subset₂ hδ hnt ht₂) h le_rfl

/-- **Balanced fundamental cycles of triangulations.** Let `T` be a spanning tree of a plane
map all of whose faces are triangles, and `w` nonnegative weights on the vertices of total at
most `1`. Then some dart `δ` off the tree has a fundamental cycle whose strict inside and strict
outside weigh at most `2/3` each. -/
theorem exists_simple_balanced (hM : M.IsPlane) (hT : ∀ δ, M.IsTriangle δ) {w : P → ℝ}
    (hw : ∀ v, 0 ≤ w v) (h1 : ∑ v, w v ≤ 1) (d₀ : D) :
    ∃ δ, ¬ T.IsTree δ ∧ ∑ v ∈ T.inC δ, w v ≤ 2 / 3 ∧ ∑ v ∈ T.outC δ, w v ≤ 2 / 3 := by
  obtain ⟨δ, hδ⟩ : ∃ δ, ¬ T.IsTree δ := by
    rcases T.not_isTree_of_isTriangle (hT d₀) with h | h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  by_cases hin : 2 / 3 < ∑ v ∈ T.inC δ, w v
  · exact T.exists_simple_balanced_of_lt hM hT hw h1 _ δ rfl hin
  by_cases hout : ∑ v ∈ T.outC δ, w v ≤ 2 / 3
  · exact ⟨δ, hδ, not_lt.1 hin, hout⟩
  rw [not_le, ← inC_α hM hδ] at hout
  exact T.exists_simple_balanced_of_lt hM hT hw h1 _ _ rfl hout

/-- **The simple cycle separator of a triangulation.** Let `T` be a spanning tree of a plane map
`M` all of whose faces are triangles, in which every vertex has at most `h + 1` ancestors (a
breadth-first search tree of radius `h`), and let `w` be nonnegative weights on the vertices of
total at most `1`. Then there are a simple cycle `C` of at most `2 h + 1` darts and a set `Z` of
faces whose boundary is `C` (an edge has exactly one side in `Z` if and only if it is an edge of
`C`) such that the vertices off `C` split into `A` (those with their faces in `Z`) and `B` (those
with their faces off `Z`), no edge joins `A` and `B`, and `A` and `B` weigh at most `2/3` each.
The cycle is the fundamental cycle of a dart off the tree, and `Z` is its inside. -/
theorem exists_simple_cycle_separator (hM : M.IsPlane) (hT : ∀ δ, M.IsTriangle δ) {h : ℕ}
    (hh : ∀ v, #(T.anc v) ≤ h + 1) {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) (h1 : ∑ v, w v ≤ 1)
    (d₀ : D) :
    ∃ (C : M.SCycle) (Z : Finset M.Face) (A B : Finset P),
      C.k ≤ 2 * h + 1 ∧
      (∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ∀ i < C.k, d ≠ C.d i ∧ d ≠ M.α (C.d i)) ∧
      C.verts ∪ A ∪ B = univ ∧ Disjoint C.verts A ∧ Disjoint C.verts B ∧
      Disjoint A B ∧ (∀ d, M.vert d ∈ A → M.face d ∈ Z) ∧ (∀ d, M.vert d ∈ B → M.face d ∉ Z) ∧
      (∀ d, M.vert d ∈ A → M.vert (M.α d) ∉ B) ∧
      ∑ v ∈ A, w v ≤ 2 / 3 ∧ ∑ v ∈ B, w v ≤ 2 / 3 := by
  obtain ⟨δ, hδ, hA, hB⟩ := T.exists_simple_balanced hM hT hw h1 d₀
  have hk := T.fcycle_k_le δ
  have hx := hh (M.vert δ)
  have hz := hh (M.vert (M.α δ))
  refine ⟨T.fcycle δ, T.inside δ, T.inC δ, T.outC δ, by omega, fun d => ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, fun d hd => vert_α_notMem_outC hM hd, hA, hB⟩
  · rw [inside_iff hM, ← not_ne_iff, fund_ne_zero_iff hδ]
    push Not
    rfl
  all_goals try rw [fcycle_verts hδ]
  · ext v
    by_cases h1 : v ∈ T.cycV δ <;> by_cases h2 : v ∈ T.inC δ <;> simp [outC, h1, h2]
  · exact disjoint_left.2 fun v h1 h2 => notMem_cycV_of_mem_inC h2 h1
  · exact disjoint_left.2 fun v h1 h2 => (mem_filter.1 h2).2.1 h1
  · exact disjoint_left.2 fun v h1 h2 => (mem_filter.1 h2).2.2 h1
  · exact fun d hd => (mem_inC_iff hM (notMem_cycV_of_mem_inC hd) rfl).1 hd
  · intro d hd
    obtain ⟨h1, h2⟩ := (mem_filter.1 hd).2
    exact fun h => h2 ((mem_inC_iff hM h1 rfl).2 h)

end SpTree

end Map

end PlanarSeparator
