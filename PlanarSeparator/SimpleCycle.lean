module

public import PlanarSeparator.Fundamental

/-!
# Fundamental cycles are simple cycles

Let `T` be a spanning tree of a map `M` and `δ` a dart off the tree, from `x` to `z`. The
fundamental cochain of `δ` (`PlanarSeparator.Map.SpTree.fund`) is the edge of `δ` together with
the tree paths from `x` and `z` to the root; the parts of the two paths above their lowest common
ancestor `a` cancel. What remains is the closed walk

`x → z → parent z → ⋯ → a → ⋯ → parent x → x`

which visits every vertex at most once: a **simple cycle** (`PlanarSeparator.Map.SCycle`). This
file constructs it (`PlanarSeparator.Map.SpTree.fcycle`) and proves that its vertices are exactly
the vertices met by the fundamental cochain (`PlanarSeparator.Map.SpTree.cycV`), and that it has
at most `#anc x + #anc z - 1` darts, so at most `2 h + 1` darts for a tree of depth `h`.

## Main definitions

* `PlanarSeparator.Map.SCycle`: a simple closed walk of darts.
* `PlanarSeparator.Map.SpTree.cycV δ`: the vertices met by the fundamental cochain of `δ`.
* `PlanarSeparator.Map.SpTree.fcycle`: the fundamental cycle of a dart off the tree.

## Main results

* `PlanarSeparator.Map.SpTree.fcycle_verts`: the vertices of the fundamental cycle are `cycV δ`.
* `PlanarSeparator.Map.SpTree.fcycle_k_le`: its length is at most `#anc x + #anc z - 1`.
-/

@[expose] public section

namespace PlanarSeparator

open Finset

namespace Map

variable {D P : Type*}

/-- A **simple cycle** of a map: a closed walk of `k ≥ 1` darts `d 0, …, d (k - 1)` (the head of
`d i` is the tail of `d (i + 1)`, and the head of `d (k - 1)` is the tail of `d 0`) whose tails
are pairwise distinct. -/
structure SCycle (M : Map D P) where
  /-- The number of darts. -/
  k : ℕ
  /-- The darts. -/
  d : ℕ → D
  pos : 0 < k
  vert_α : ∀ i < k, M.vert (M.α (d i)) = M.vert (d ((i + 1) % k))
  inj : ∀ i < k, ∀ j < k, M.vert (d i) = M.vert (d j) → i = j

namespace SCycle

variable {M : Map D P} (C : M.SCycle)

/-- The vertices of a simple cycle. -/
def verts [DecidableEq P] : Finset P := (range C.k).image fun i => M.vert (C.d i)

lemma mem_verts [DecidableEq P] {v : P} : v ∈ C.verts ↔ ∃ i < C.k, M.vert (C.d i) = v := by
  simp [verts]

/-- A simple cycle of `k` darts has `k` vertices. -/
lemma card_verts [DecidableEq P] : #C.verts = C.k := by
  rw [verts, card_image_of_injOn, card_range]
  intro i hi j hj h
  exact C.inj i (by simpa using hi) j (by simpa using hj) h

end SCycle

namespace SpTree

variable {M : Map D P} (T : SpTree M) [DecidableEq P]

/-! ### Iterated parents -/

lemma parent_root : T.parent T.root = T.root := by simp [parent]

lemma iterate_parent_root (n : ℕ) : T.parent^[n] T.root = T.root := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, T.parent_root, ih]

lemma iterate_parent_mem_anc (n : ℕ) (v : P) : T.parent^[n] v ∈ T.anc v := by
  induction n with
  | zero => exact T.mem_anc_self v
  | succ n ih => rw [Function.iterate_succ_apply']; exact T.parent_mem_anc ih

/-- The ancestors of `v` are its iterated parents. -/
lemma mem_anc_iff {u v : P} : u ∈ T.anc v ↔ ∃ n, T.parent^[n] v = u := by
  refine ⟨fun hu => ?_, fun ⟨n, hn⟩ => hn ▸ T.iterate_parent_mem_anc n v⟩
  induction v using T.induction with
  | hroot =>
    rw [anc_root, mem_singleton] at hu
    exact ⟨0, hu.symm⟩
  | hstep v hv ih =>
    rw [T.anc_of_ne hv] at hu
    rcases mem_insert.1 hu with rfl | hu
    · exact ⟨0, rfl⟩
    · obtain ⟨n, hn⟩ := ih hu
      exact ⟨n + 1, by rw [Function.iterate_succ_apply, hn]⟩

lemma anc_subset_anc {u v : P} (h : u ∈ T.anc v) : T.anc u ⊆ T.anc v := by
  intro w hw
  obtain ⟨n, rfl⟩ := (T.mem_anc_iff).1 h
  obtain ⟨m, rfl⟩ := (T.mem_anc_iff).1 hw
  rw [← Function.iterate_add_apply]
  exact T.iterate_parent_mem_anc _ v

lemma height_iterate_le (n : ℕ) (v : P) : T.height (T.parent^[n] v) ≤ T.height v :=
  T.height_le_of_mem_anc (T.iterate_parent_mem_anc n v)

lemma height_iterate_lt {v : P} (hv : v ≠ T.root) {n : ℕ} (hn : 0 < n) :
    T.height (T.parent^[n] v) < T.height v := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Function.iterate_succ_apply]
  exact (T.height_iterate_le m _).trans_lt (T.height_parent_lt hv)

/-- Iterated parents are distinct until the root is reached. -/
lemma iterate_inj {v : P} {i j : ℕ} (h : T.parent^[i] v = T.parent^[j] v)
    (hr : T.parent^[min i j] v ≠ T.root) : i = j := by
  by_contra hij
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · rw [min_eq_left hlt.le] at hr
    have := T.height_iterate_lt hr (n := j - i) (by omega)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le, ← h] at this
    exact lt_irrefl _ this
  · rw [min_eq_right hlt.le] at hr
    have := T.height_iterate_lt hr (n := i - j) (by omega)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le, h] at this
    exact lt_irrefl _ this

/-- Two vertices which are ancestors of each other are equal. -/
lemma eq_of_mem_anc_of_mem_anc {u v : P} (h1 : u ∈ T.anc v) (h2 : v ∈ T.anc u) : u = v := by
  obtain ⟨n, rfl⟩ := (T.mem_anc_iff).1 h1
  by_contra hne
  have hv : v ≠ T.root := by
    intro hv
    subst hv
    exact hne (T.iterate_parent_root n)
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => hne (by simp [h])
  have := T.height_iterate_lt hv hn
  have := T.height_le_of_mem_anc h2
  omega

lemma exists_iterate_eq_root (v : P) : ∃ n, T.parent^[n] v = T.root :=
  (T.mem_anc_iff).1 (T.root_mem_anc v)

/-- The number of iterated parents before a given ancestor is less than the number of
ancestors. -/
lemma lt_card_anc {v : P} {n : ℕ} (hn : ∀ i < n, T.parent^[i] v ≠ T.root) :
    n ≤ #(T.anc v) := by
  have : (range n).image (fun i => T.parent^[i] v) ⊆ T.anc v := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.1 hu
    exact T.iterate_parent_mem_anc i v
  refine le_trans (le_of_eq ?_) (card_le_card this)
  rw [card_image_of_injOn, card_range]
  intro i hi j hj h
  simp only [coe_range, Set.mem_Iio] at hi hj
  exact T.iterate_inj h (hn _ (lt_of_le_of_lt (min_le_left _ _) hi))

/-! ### The fundamental cycle -/

section Fcycle

variable {T}

open Classical in
/-- The number of steps from the head `z` of `δ` up to the lowest common ancestor. -/
noncomputable def cs (T : SpTree M) (δ : D) : ℕ :=
  Nat.find (p := fun i => T.parent^[i] (M.vert (M.α δ)) ∈ T.anc (M.vert δ))
    (by
      obtain ⟨n, hn⟩ := T.exists_iterate_eq_root (M.vert (M.α δ))
      exact ⟨n, hn ▸ T.root_mem_anc _⟩)

/-- The lowest common ancestor of the two ends of `δ`. -/
noncomputable def lca (T : SpTree M) (δ : D) : P := T.parent^[cs T δ] (M.vert (M.α δ))

lemma lca_mem_anc (δ : D) : lca T δ ∈ T.anc (M.vert δ) := by
  classical
  exact Nat.find_spec (p := fun i => T.parent^[i] (M.vert (M.α δ)) ∈ T.anc (M.vert δ)) _

lemma lca_mem_anc' (δ : D) : lca T δ ∈ T.anc (M.vert (M.α δ)) :=
  T.iterate_parent_mem_anc _ _

lemma iterate_notMem_of_lt_cs {δ : D} {i : ℕ} (hi : i < cs T δ) :
    T.parent^[i] (M.vert (M.α δ)) ∉ T.anc (M.vert δ) := by
  classical
  exact Nat.find_min (p := fun i => T.parent^[i] (M.vert (M.α δ)) ∈ T.anc (M.vert δ)) _ hi

open Classical in
/-- The number of steps from the tail `x` of `δ` up to the lowest common ancestor. -/
noncomputable def ct (T : SpTree M) (δ : D) : ℕ :=
  Nat.find (p := fun j => T.parent^[j] (M.vert δ) = lca T δ) ((T.mem_anc_iff).1 (lca_mem_anc δ))

lemma iterate_ct (δ : D) : T.parent^[ct T δ] (M.vert δ) = lca T δ := by
  classical
  exact Nat.find_spec (p := fun j => T.parent^[j] (M.vert δ) = lca T δ) _

lemma iterate_ne_of_lt_ct {δ : D} {j : ℕ} (hj : j < ct T δ) :
    T.parent^[j] (M.vert δ) ≠ lca T δ := by
  classical
  exact Nat.find_min (p := fun j => T.parent^[j] (M.vert δ) = lca T δ) _ hj

lemma iterate_ne_root_of_lt_cs {δ : D} {i : ℕ} (hi : i < cs T δ) :
    T.parent^[i] (M.vert (M.α δ)) ≠ T.root := fun h =>
  iterate_notMem_of_lt_cs hi (h ▸ T.root_mem_anc _)

lemma iterate_ne_root_of_lt_ct {δ : D} {j : ℕ} (hj : j < ct T δ) :
    T.parent^[j] (M.vert δ) ≠ T.root := fun h => by
  apply iterate_ne_of_lt_ct hj
  rw [← iterate_ct δ, h, ← Nat.sub_add_cancel hj.le, Function.iterate_add_apply, h,
    T.iterate_parent_root]

/-- An ancestor of the tail strictly below the lowest common ancestor is not an ancestor of the
head. -/
lemma iterate_notMem_of_lt_ct {δ : D} {j : ℕ} (hj : j < ct T δ) :
    T.parent^[j] (M.vert δ) ∉ T.anc (M.vert (M.α δ)) := by
  intro h
  obtain ⟨i, hi⟩ := (T.mem_anc_iff).1 h
  rcases Nat.lt_or_ge i (cs T δ) with hi' | hi'
  · exact iterate_notMem_of_lt_cs hi' (hi ▸ T.iterate_parent_mem_anc _ _)
  · -- `parent^[j] x` is an ancestor of the lca, and conversely
    have h1 : T.parent^[j] (M.vert δ) ∈ T.anc (lca T δ) := by
      rw [← hi, ← Nat.sub_add_cancel hi', Function.iterate_add_apply]
      exact T.iterate_parent_mem_anc _ _
    have h2 : lca T δ ∈ T.anc (T.parent^[j] (M.vert δ)) := by
      rw [← iterate_ct δ, ← Nat.sub_add_cancel hj.le, Function.iterate_add_apply]
      exact T.iterate_parent_mem_anc _ _
    exact iterate_ne_of_lt_ct hj (T.eq_of_mem_anc_of_mem_anc h1 h2)

/-- The number of darts of the fundamental cycle. -/
noncomputable def ck (T : SpTree M) (δ : D) : ℕ := 1 + cs T δ + ct T δ

/-- The parent dart of a vertex, with `δ` at the root. -/
noncomputable def pdt (T : SpTree M) (δ : D) (v : P) : D := if h : v = T.root then δ else T.par v h

lemma pdt_of_ne {δ : D} {v : P} (h : v ≠ T.root) : pdt T δ v = T.par v h := by simp [pdt, h]

/-- The darts of the fundamental cycle of `δ`: `δ`, the parent darts from `z` up to the lowest
common ancestor, and the reversed parent darts from the lowest common ancestor down to `x`. -/
noncomputable def fd (T : SpTree M) (δ : D) (i : ℕ) : D :=
  if i = 0 then δ
  else if i ≤ cs T δ then pdt T δ (T.parent^[i - 1] (M.vert (M.α δ)))
  else M.α (pdt T δ (T.parent^[ck T δ - 1 - i] (M.vert δ)))

/-- The vertices of the fundamental cycle of `δ`. -/
noncomputable def fv (T : SpTree M) (δ : D) (i : ℕ) : P :=
  if i = 0 then M.vert δ
  else if i ≤ cs T δ then T.parent^[i - 1] (M.vert (M.α δ))
  else T.parent^[ck T δ - i] (M.vert δ)

lemma vert_fd {δ : D} {i : ℕ} (hi : i < ck T δ) : M.vert (fd T δ i) = fv T δ i := by
  unfold fd fv
  split_ifs with h0 h1
  · rfl
  · rw [pdt_of_ne (iterate_ne_root_of_lt_cs (by omega)), T.vert_par]
  · have hj : ck T δ - 1 - i < ct T δ := by unfold ck at *; omega
    rw [pdt_of_ne (iterate_ne_root_of_lt_ct hj), ← T.parent_of_ne, ← Function.iterate_succ_apply' T.parent]
    congr 1
    omega

lemma fv_ck (δ : D) : fv T δ (ck T δ) = M.vert δ := by
  unfold fv ck
  split_ifs with h0 h1
  · rfl
  · omega
  · simp

lemma vert_α_fd {δ : D} {i : ℕ} (hi : i < ck T δ) :
    M.vert (M.α (fd T δ i)) = fv T δ (i + 1) := by
  have hlca := iterate_ct (T := T) δ
  unfold fd fv
  by_cases h0 : i = 0
  · subst h0
    simp only [↓reduceIte, one_ne_zero, zero_add, Nat.sub_self,
      Function.iterate_zero, id_eq]
    split_ifs with h1
    · rfl
    · have hcs : cs T δ = 0 := by omega
      have : ck T δ - 1 = ct T δ := by unfold ck; omega
      rw [this, hlca, lca, hcs]
      rfl
  rw [ite_eq_right h0, ite_eq_right (by omega : i + 1 ≠ 0)]
  by_cases h1 : i ≤ cs T δ
  · rw [ite_eq_left h1, pdt_of_ne (iterate_ne_root_of_lt_cs (by omega)), ← T.parent_of_ne,
      ← Function.iterate_succ_apply' T.parent]
    split_ifs with h2
    · congr 1; omega
    · have : ck T δ - (i + 1) = ct T δ := by unfold ck; omega
      rw [this, hlca, lca]
      congr 1; omega
  · have hj : ck T δ - 1 - i < ct T δ := by unfold ck at *; omega
    rw [ite_eq_right h1, ite_eq_right (by omega), pdt_of_ne (iterate_ne_root_of_lt_ct hj), M.α_α, T.vert_par]
    congr 1
    omega

/-- The vertices of the fundamental cycle, by the two tree paths. -/
lemma fv_cases {δ : D} {i : ℕ} (hi : i < ck T δ) :
    (∃ j ≤ ct T δ, fv T δ i = T.parent^[j] (M.vert δ)) ∨
      (∃ j < cs T δ, fv T δ i = T.parent^[j] (M.vert (M.α δ))) := by
  unfold fv
  split_ifs with h0 h1
  · exact Or.inl ⟨0, Nat.zero_le _, rfl⟩
  · exact Or.inr ⟨i - 1, by omega, rfl⟩
  · exact Or.inl ⟨ck T δ - i, by unfold ck at *; omega, rfl⟩

lemma fv_injective {δ : D} {i j : ℕ} (hi : i < ck T δ) (hj : j < ck T δ)
    (h : fv T δ i = fv T δ j) : i = j := by
  -- the tail path is injective up to the lca, the head path below it
  have hx : ∀ a ≤ ct T δ, ∀ b ≤ ct T δ, T.parent^[a] (M.vert δ) = T.parent^[b] (M.vert δ) →
      a = b := by
    intro a ha b hb hab
    by_cases hm : min a b < ct T δ
    · exact T.iterate_inj hab (iterate_ne_root_of_lt_ct hm)
    · omega
  have hz : ∀ a < cs T δ, ∀ b < cs T δ,
      T.parent^[a] (M.vert (M.α δ)) = T.parent^[b] (M.vert (M.α δ)) → a = b := by
    intro a ha b hb hab
    exact T.iterate_inj hab (iterate_ne_root_of_lt_cs (lt_of_le_of_lt (min_le_left _ _) ha))
  have hxz : ∀ a, ∀ b < cs T δ, T.parent^[a] (M.vert δ) ≠ T.parent^[b] (M.vert (M.α δ)) :=
    fun a b hb hab => iterate_notMem_of_lt_cs hb (hab ▸ T.iterate_parent_mem_anc _ _)
  have e0 : M.vert δ = T.parent^[0] (M.vert δ) := rfl
  unfold fv at h
  unfold ck at hi hj
  by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
  · omega
  · simp only [hi0, hj0, ↓reduceIte] at h
    rw [e0] at h
    split_ifs at h with hj1
    · exact absurd h (hxz _ _ (by omega))
    · have := hx 0 (Nat.zero_le _) _ (by unfold ck; omega) h
      unfold ck at this; omega
  · simp only [hi0, hj0, ↓reduceIte] at h
    rw [e0] at h
    split_ifs at h with hi1
    · exact absurd h.symm (hxz _ _ (by omega))
    · have := hx _ (by unfold ck; omega) 0 (Nat.zero_le _) h
      unfold ck at this; omega
  · simp only [hi0, hj0, ↓reduceIte] at h
    split_ifs at h with hi1 hj1 hj1
    · have := hz _ (by omega) _ (by omega) h; omega
    · exact absurd h.symm (hxz _ _ (by omega))
    · exact absurd h (hxz _ _ (by omega))
    · have := hx _ (by unfold ck; omega) _ (by unfold ck; omega) h
      unfold ck at this; omega

/-- **The fundamental cycle** of a dart off the tree, as a simple cycle. -/
noncomputable def fcycle (T : SpTree M) (δ : D) : M.SCycle where
  k := ck T δ
  d := fd T δ
  pos := by unfold ck; omega
  vert_α i hi := by
    rw [vert_α_fd hi, vert_fd (Nat.mod_lt _ (by unfold ck; omega))]
    by_cases h : i + 1 < ck T δ
    · rw [Nat.mod_eq_of_lt h]
    · rw [show i + 1 = ck T δ by omega, Nat.mod_self, fv_ck]
      unfold fv
      simp
  inj i hi j hj h := by
    rw [vert_fd hi, vert_fd hj] at h
    exact fv_injective hi hj h

@[simp] lemma fcycle_k (δ : D) : (fcycle T δ).k = ck T δ := rfl

@[simp] lemma fcycle_d (δ : D) : (fcycle T δ).d = fd T δ := rfl

lemma fcycle_d_zero (δ : D) : (fcycle T δ).d 0 = δ := by simp [fd]

/-- **The length of the fundamental cycle**: at most `#anc x + #anc z - 1` darts. -/
theorem fcycle_k_le (δ : D) :
    (fcycle T δ).k + 1 ≤ #(T.anc (M.vert δ)) + #(T.anc (M.vert (M.α δ))) := by
  rw [fcycle_k, ck]
  have h1 : cs T δ + 1 ≤ #(T.anc (M.vert (M.α δ))) := by
    -- the head path below the lca, and the lca itself
    have hs : (range (cs T δ + 1)).image (fun i => T.parent^[i] (M.vert (M.α δ))) ⊆
        T.anc (M.vert (M.α δ)) := by
      intro u hu
      obtain ⟨i, -, rfl⟩ := mem_image.1 hu
      exact T.iterate_parent_mem_anc i _
    refine le_trans (le_of_eq ?_) (card_le_card hs)
    rw [card_image_of_injOn, card_range]
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    by_cases hm : min a b < cs T δ
    · exact T.iterate_inj hab (iterate_ne_root_of_lt_cs hm)
    · omega
  have h2 : ct T δ ≤ #(T.anc (M.vert δ)) := T.lt_card_anc fun i hi => iterate_ne_root_of_lt_ct hi
  have h3 : ct T δ < #(T.anc (M.vert δ)) := by
    -- the lca is an ancestor of `x` which is not among the first `ct` iterated parents
    have hs : insert (lca T δ) ((range (ct T δ)).image (fun i => T.parent^[i] (M.vert δ))) ⊆
        T.anc (M.vert δ) := by
      intro u hu
      rcases mem_insert.1 hu with rfl | hu
      · exact lca_mem_anc δ
      · obtain ⟨i, -, rfl⟩ := mem_image.1 hu
        exact T.iterate_parent_mem_anc i _
    refine lt_of_lt_of_le ?_ (card_le_card hs)
    rw [card_insert_of_notMem, card_image_of_injOn, card_range]
    · omega
    · intro a ha b hb hab
      simp only [coe_range, Set.mem_Iio] at ha hb
      exact T.iterate_inj hab (iterate_ne_root_of_lt_ct (lt_of_le_of_lt (min_le_left _ _) ha))
    · intro h
      obtain ⟨i, hi, he⟩ := mem_image.1 h
      exact iterate_ne_of_lt_ct (by simpa using hi) he
  omega

end Fcycle

/-! ### The vertices of the fundamental cycle -/

section Verts

variable [DecidableEq D]

/-- The vertices met by the fundamental cochain of `δ`. -/
noncomputable def cycV [Fintype P] (δ : D) : Finset P :=
  by classical exact univ.filter fun v => ∃ d, M.vert d = v ∧ T.fund δ d ≠ 0

lemma mem_cycV [Fintype P] {δ : D} {v : P} : v ∈ T.cycV δ ↔ ∃ d, M.vert d = v ∧ T.fund δ d ≠ 0 := by
  classical
  simp [cycV]

lemma cycV_α [Fintype P] (δ : D) : T.cycV (M.α δ) = T.cycV δ := by
  ext v
  simp only [mem_cycV, fund_α]

lemma cycV_subset_sep [Fintype P] (δ : D) : T.cycV δ ⊆ T.sep δ := by
  intro v hv
  obtain ⟨d, rfl, hd⟩ := (T.mem_cycV).1 hv
  exact T.vert_mem_sep_of_fund_ne_zero hd

/-- The fundamental cochain on a parent dart. -/
lemma fund_par {δ : D} (hδ : ¬ T.IsTree δ) (u : P) (hu : u ≠ T.root) :
    T.fund δ (T.par u hu) =
      (if u ∈ T.anc (M.vert δ) then 1 else 0) + (if u ∈ T.anc (M.vert (M.α δ)) then 1 else 0) := by
  have h0 : M.edgeInd δ (T.par u hu) = 0 := by
    refine edgeInd_eq_zero (fun h => hδ ?_) (fun h => hδ ?_)
    · rw [← h]; exact T.isTree_par u hu
    · rw [← M.α_α δ, ← h, T.isTree_α]; exact T.isTree_par u hu
  rw [fund_apply, h0, zero_add, T.pathC_par, T.pathC_par]


variable {T} [Fintype P]


lemma mem_cycV_iff {δ : D} (hδ : ¬ T.IsTree δ) {v : P} :
    v ∈ T.cycV δ ↔ (∃ j ≤ ct T δ, v = T.parent^[j] (M.vert δ)) ∨
      (∃ j < cs T δ, v = T.parent^[j] (M.vert (M.α δ))) := by
  -- the ancestors of `x` off the head path, and conversely
  have hAx : ∀ u, u ∈ T.anc (M.vert δ) → u ∉ T.anc (M.vert (M.α δ)) →
      ∃ j < ct T δ, u = T.parent^[j] (M.vert δ) := by
    intro u hu hu'
    obtain ⟨j, rfl⟩ := (T.mem_anc_iff).1 hu
    refine ⟨j, ?_, rfl⟩
    by_contra hj
    apply hu'
    refine T.anc_subset_anc (lca_mem_anc' δ) ?_
    have : T.parent^[j] (M.vert δ) = T.parent^[j - ct T δ] (T.parent^[ct T δ] (M.vert δ)) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel (not_lt.1 hj)]
    rw [this, iterate_ct δ]
    exact T.iterate_parent_mem_anc _ _
  have hAz : ∀ u, u ∈ T.anc (M.vert (M.α δ)) → u ∉ T.anc (M.vert δ) →
      ∃ j < cs T δ, u = T.parent^[j] (M.vert (M.α δ)) := by
    intro u hu hu'
    obtain ⟨j, rfl⟩ := (T.mem_anc_iff).1 hu
    refine ⟨j, ?_, rfl⟩
    by_contra hj
    apply hu'
    refine T.anc_subset_anc (lca_mem_anc δ) ?_
    have : T.parent^[j] (M.vert (M.α δ)) =
        T.parent^[j - cs T δ] (T.parent^[cs T δ] (M.vert (M.α δ))) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel (not_lt.1 hj)]
    rw [this]
    exact T.iterate_parent_mem_anc _ _
  have hlca : T.parent^[ct T δ] (M.vert δ) = T.parent^[cs T δ] (M.vert (M.α δ)) := iterate_ct δ
  rw [mem_cycV]
  constructor
  · rintro ⟨d, rfl, hd⟩
    rcases T.fund_ne_zero hd with ⟨u, hu, rfl | rfl⟩ | rfl | rfl
    · rw [T.vert_par]
      rw [fund_par T hδ] at hd
      by_cases h1 : u ∈ T.anc (M.vert δ) <;> by_cases h2 : u ∈ T.anc (M.vert (M.α δ)) <;>
        simp only [h1, h2, ↓reduceIte] at hd
      · exact absurd (by decide : (1 : ZMod 2) + 1 = 0) hd
      · obtain ⟨j, hj, rfl⟩ := hAx u h1 h2
        exact Or.inl ⟨j, hj.le, rfl⟩
      · obtain ⟨j, hj, rfl⟩ := hAz u h2 h1
        exact Or.inr ⟨j, hj, rfl⟩
      · exact absurd rfl hd
    · rw [fund_α_apply, fund_par T hδ] at hd
      rw [← T.parent_of_ne hu]
      by_cases h1 : u ∈ T.anc (M.vert δ) <;> by_cases h2 : u ∈ T.anc (M.vert (M.α δ)) <;>
        simp only [h1, h2, ↓reduceIte] at hd
      · exact absurd (by decide : (1 : ZMod 2) + 1 = 0) hd
      · obtain ⟨j, hj, rfl⟩ := hAx u h1 h2
        exact Or.inl ⟨j + 1, hj, by rw [Function.iterate_succ_apply']⟩
      · obtain ⟨j, hj, rfl⟩ := hAz u h2 h1
        rw [← Function.iterate_succ_apply' T.parent]
        by_cases hj' : j + 1 < cs T δ
        · exact Or.inr ⟨j + 1, hj', rfl⟩
        · rw [Nat.succ_eq_add_one, show j + 1 = cs T δ by omega, ← hlca]
          exact Or.inl ⟨ct T δ, le_rfl, rfl⟩
      · exact absurd rfl hd
    · exact Or.inl ⟨0, Nat.zero_le _, rfl⟩
    · by_cases h : 0 < cs T δ
      · exact Or.inr ⟨0, h, rfl⟩
      · refine Or.inl ⟨ct T δ, le_rfl, ?_⟩
        rw [hlca, show cs T δ = 0 by omega]
        rfl
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact ⟨δ, rfl, by rw [T.fund_self hδ]; exact one_ne_zero⟩
      · -- the end of the reversed parent dart of `parent^[j - 1] x`
        have hj1 : j - 1 < ct T δ := by omega
        have hr := iterate_ne_root_of_lt_ct hj1
        refine ⟨M.α (T.par _ hr), ?_, ?_⟩
        · rw [← T.parent_of_ne, ← Function.iterate_succ_apply' T.parent, Nat.succ_eq_add_one,
            Nat.sub_add_cancel hj0]
        · rw [fund_α_apply, fund_par T hδ, ite_eq_left (T.iterate_parent_mem_anc _ _),
            ite_eq_right (iterate_notMem_of_lt_ct hj1), add_zero]
          exact one_ne_zero
    · have hr := iterate_ne_root_of_lt_cs hj
      refine ⟨T.par _ hr, T.vert_par _ _, ?_⟩
      rw [fund_par T hδ, ite_eq_right (iterate_notMem_of_lt_cs hj),
        ite_eq_left (T.iterate_parent_mem_anc _ _), zero_add]
      exact one_ne_zero

/-- **The vertices of the fundamental cycle** are the vertices met by the fundamental cochain. -/
theorem fcycle_verts {δ : D} (hδ : ¬ T.IsTree δ) : (fcycle T δ).verts = T.cycV δ := by
  ext v
  rw [SCycle.mem_verts, mem_cycV_iff hδ]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [fcycle_d, vert_fd hi]
    rcases fv_cases hi with ⟨j, hj, h⟩ | ⟨j, hj, h⟩
    · exact Or.inl ⟨j, hj, h⟩
    · exact Or.inr ⟨j, hj, h⟩
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact ⟨0, (fcycle T δ).pos, by simp [fd]⟩
      · refine ⟨ck T δ - j, by rw [fcycle_k]; unfold ck; omega, ?_⟩
        rw [fcycle_d, vert_fd (by unfold ck; omega)]
        unfold fv
        rw [ite_eq_right (by unfold ck; omega), ite_eq_right (by unfold ck; omega)]
        congr 1
        unfold ck
        omega
    · refine ⟨j + 1, by rw [fcycle_k]; unfold ck; omega, ?_⟩
      rw [fcycle_d, vert_fd (by unfold ck; omega)]
      unfold fv
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      rfl

/-- The fundamental cycle has `#cycV δ` darts. -/
theorem card_cycV {δ : D} (hδ : ¬ T.IsTree δ) : #(T.cycV δ) = (fcycle T δ).k := by
  rw [← fcycle_verts hδ, SCycle.card_verts]

omit [Fintype P] in
/-- **The edges of the fundamental cycle** are the edges of the fundamental cochain. -/
theorem fund_ne_zero_iff {δ : D} (hδ : ¬ T.IsTree δ) {d : D} :
    T.fund δ d ≠ 0 ↔ ∃ i < (fcycle T δ).k, d = (fcycle T δ).d i ∨ d = M.α ((fcycle T δ).d i) := by
  simp only [fcycle_k, fcycle_d]
  -- the parent darts of the two tree paths below the lca
  have hz : ∀ j < cs T δ, ∃ h, fd T δ (j + 1) = T.par (T.parent^[j] (M.vert (M.α δ))) h := by
    intro j hj
    refine ⟨iterate_ne_root_of_lt_cs hj, ?_⟩
    unfold fd
    rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel,
      pdt_of_ne (iterate_ne_root_of_lt_cs hj)]
  have hx : ∀ j < ct T δ, ∃ h, fd T δ (ck T δ - 1 - j) = M.α (T.par (T.parent^[j] (M.vert δ)) h) := by
    intro j hj
    refine ⟨iterate_ne_root_of_lt_ct hj, ?_⟩
    unfold fd
    rw [ite_eq_right (by unfold ck; omega), ite_eq_right (by unfold ck; omega),
      show ck T δ - 1 - (ck T δ - 1 - j) = j by unfold ck; omega,
      pdt_of_ne (iterate_ne_root_of_lt_ct hj)]
  have hfz : ∀ j < cs T δ, ∀ h, T.fund δ (T.par (T.parent^[j] (M.vert (M.α δ))) h) ≠ 0 := by
    intro j hj h
    rw [fund_par T hδ, ite_eq_right (iterate_notMem_of_lt_cs hj),
      ite_eq_left (T.iterate_parent_mem_anc _ _), zero_add]
    exact one_ne_zero
  have hfx : ∀ j < ct T δ, ∀ h, T.fund δ (T.par (T.parent^[j] (M.vert δ)) h) ≠ 0 := by
    intro j hj h
    rw [fund_par T hδ, ite_eq_left (T.iterate_parent_mem_anc _ _),
      ite_eq_right (iterate_notMem_of_lt_ct hj), add_zero]
    exact one_ne_zero
  -- a parent dart in the support is one of these
  have hpar : ∀ u (hu : u ≠ T.root), T.fund δ (T.par u hu) ≠ 0 →
      ∃ i < ck T δ, T.par u hu = fd T δ i ∨ T.par u hu = M.α (fd T δ i) := by
    intro u hu hd
    rw [fund_par T hδ] at hd
    by_cases h1 : u ∈ T.anc (M.vert δ) <;> by_cases h2 : u ∈ T.anc (M.vert (M.α δ)) <;>
      simp only [h1, h2, ↓reduceIte] at hd
    · exact absurd (by decide : (1 : ZMod 2) + 1 = 0) hd
    · obtain ⟨j, rfl⟩ := (T.mem_anc_iff).1 h1
      have hj : j < ct T δ := by
        by_contra hj
        apply h2
        refine T.anc_subset_anc (lca_mem_anc' δ) ?_
        have : T.parent^[j] (M.vert δ) = T.parent^[j - ct T δ] (T.parent^[ct T δ] (M.vert δ)) := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel (not_lt.1 hj)]
        rw [this, iterate_ct δ]
        exact T.iterate_parent_mem_anc _ _
      obtain ⟨h, e⟩ := hx j hj
      refine ⟨ck T δ - 1 - j, by unfold ck; omega, Or.inr ?_⟩
      rw [e, M.α_α]
    · obtain ⟨j, rfl⟩ := (T.mem_anc_iff).1 h2
      have hj : j < cs T δ := by
        by_contra hj
        apply h1
        refine T.anc_subset_anc (lca_mem_anc δ) ?_
        have : T.parent^[j] (M.vert (M.α δ)) =
            T.parent^[j - cs T δ] (T.parent^[cs T δ] (M.vert (M.α δ))) := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel (not_lt.1 hj)]
        rw [this]
        exact T.iterate_parent_mem_anc _ _
      obtain ⟨h, e⟩ := hz j hj
      exact ⟨j + 1, by unfold ck; omega, Or.inl e.symm⟩
    · exact absurd rfl hd
  constructor
  · intro hd
    rcases T.fund_ne_zero hd with ⟨u, hu, rfl | rfl⟩ | rfl | rfl
    · exact hpar u hu hd
    · rw [fund_α_apply] at hd
      obtain ⟨i, hi, e | e⟩ := hpar u hu hd
      · exact ⟨i, hi, Or.inr (by rw [e])⟩
      · exact ⟨i, hi, Or.inl (by rw [e, M.α_α])⟩
    · exact ⟨0, by unfold ck; omega, Or.inl (by simp [fd])⟩
    · exact ⟨0, by unfold ck; omega, Or.inr (by simp [fd])⟩
  · rintro ⟨i, hi, e⟩
    suffices h : T.fund δ (fd T δ i) ≠ 0 by
      rcases e with rfl | rfl
      · exact h
      · rwa [fund_α_apply]
    unfold fd
    split_ifs with h0 h1
    · rw [T.fund_self hδ]; exact one_ne_zero
    · rw [pdt_of_ne (iterate_ne_root_of_lt_cs (by omega))]
      exact hfz _ (by omega) _
    · have hj : ck T δ - 1 - i < ct T δ := by unfold ck at *; omega
      rw [pdt_of_ne (iterate_ne_root_of_lt_ct hj), fund_α_apply]
      exact hfx _ hj _

end Verts

end SpTree

end Map

end PlanarSeparator
