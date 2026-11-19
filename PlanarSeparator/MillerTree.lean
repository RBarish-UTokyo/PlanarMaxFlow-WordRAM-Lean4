module

public import PlanarSeparator.MillerBoundary
public import PlanarSeparator.CycleSeparator

/-!
# Spanning trees redirected along cycles

Tools for Miller's simple cycle separator theorem.

* Along the root path of a vertex the heights are distinct, and the root paths of two vertices
  `u` and `c`, with `c` an ancestor of `u`, add up to the tree path between them
  (`PlanarSeparator.Map.SpTree.pathC_add_ne_zero`).
* A closed cochain supported on the tree edges and one dart `e` off the tree, taking the value
  `1` at `e`, is the fundamental cochain of `e` (`PlanarSeparator.Map.SpTree.eq_fund`): a tree
  carries no closed cochain.
* A spanning tree can be *redirected*: some vertices get a new parent of the same height, with a
  secondary potential decreasing along the new parents (`PlanarSeparator.Map.SpTree.redirect`).
  Redirecting along an arc of a simple cycle makes the arc a tree path
  (`PlanarSeparator.Map.SpTree.arcTree`), whose root path cochains are the cochains of the arcs
  (`PlanarSeparator.Map.SpTree.pathC_arcTree`).
* A simple cycle bounding a set of faces separates the vertices off the cycle into two sides with
  no edge between them (`PlanarSeparator.Map.isCycleSep_of_bd`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

open Finset

namespace Map

variable {D P : Type*} {M : Map D P}

namespace SpTree

variable (T : M.SpTree) [DecidableEq P]

/-! ### Root paths -/

/-- The heights along a root path are distinct. -/
lemma height_injOn_anc (v : P) : Set.InjOn T.height (T.anc v) := by
  induction v using T.induction with
  | hroot =>
    intro a ha b hb _
    simp only [anc_root, coe_singleton, Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  | hstep v hv ih =>
    rw [T.anc_of_ne hv]
    intro a ha b hb hab
    simp only [coe_insert, Set.mem_insert_iff, mem_coe] at ha hb
    have hlt : ∀ c ∈ T.anc (T.parent v), T.height c < T.height v := fun c hc =>
      (T.height_le_of_mem_anc hc).trans_lt (T.height_parent_lt hv)
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd hab (hlt b hb).ne'
    · exact absurd hab (hlt a ha).ne
    · exact ih ha hb hab

/-- The ancestors of a vertex are totally ordered. -/
lemma anc_total {u a b : P} (ha : a ∈ T.anc u) (hb : b ∈ T.anc u) :
    a ∈ T.anc b ∨ b ∈ T.anc a := by
  obtain ⟨i, rfl⟩ := T.mem_anc_iff.1 ha
  obtain ⟨j, rfl⟩ := T.mem_anc_iff.1 hb
  rcases le_total i j with h | h
  · right
    rw [← Nat.sub_add_cancel h, Function.iterate_add_apply]
    exact T.iterate_parent_mem_anc _ _
  · left
    rw [← Nat.sub_add_cancel h, Function.iterate_add_apply]
    exact T.iterate_parent_mem_anc _ _

/-- An ancestor of `u` which is not an ancestor of the ancestor `c` has `c` as an ancestor of
its parent. -/
lemma mem_anc_parent_of_notMem {u c v : P} (hc : c ∈ T.anc u) (hv : v ∈ T.anc u)
    (hvc : v ∉ T.anc c) (hvr : v ≠ T.root) : c ∈ T.anc (T.parent v) := by
  rcases T.anc_total hv hc with h | h
  · exact absurd h hvc
  · rw [T.anc_of_ne hvr] at h
    rcases mem_insert.1 h with rfl | h
    · exact absurd (T.mem_anc_self _) hvc
    · exact h

variable [DecidableEq D]

/-- **The tree path between a vertex and one of its ancestors.** The sum of the root path
cochains of `u` and of an ancestor `c` is supported on the parent darts of the ancestors of `u`
which are not ancestors of `c`. -/
lemma pathC_add_ne_zero {u c : P} (hc : c ∈ T.anc u) {d : D}
    (h : T.pathC u d + T.pathC c d ≠ 0) :
    ∃ v ∈ T.anc u, v ∉ T.anc c ∧ ∃ hv : v ≠ T.root, d = T.par v hv ∨ d = M.α (T.par v hv) := by
  induction u using T.induction with
  | hroot =>
    rw [anc_root, mem_singleton] at hc
    subst hc
    exact absurd (Kasteleyn.ZMod.two_add_self _) h
  | hstep u hu ih =>
    by_cases huc : u = c
    · subst huc
      exact absurd (Kasteleyn.ZMod.two_add_self _) h
    have hc' : c ∈ T.anc (T.parent u) := by
      rw [T.anc_of_ne hu] at hc
      exact (mem_insert.1 hc).resolve_left (Ne.symm huc)
    rw [T.pathC_of_ne hu, Pi.add_apply, add_assoc] at h
    by_cases h1 : M.edgeInd (T.par u hu) d = 0
    · rw [h1, zero_add] at h
      obtain ⟨v, hv, hvc, rest⟩ := ih hc' h
      exact ⟨v, by rw [T.anc_of_ne hu]; exact mem_insert_of_mem hv, hvc, rest⟩
    · exact ⟨u, T.mem_anc_self u, fun hu' => huc (T.eq_of_mem_anc_of_mem_anc hu' hc), hu,
        edgeInd_ne_zero h1⟩

/-- The vertices met by the tree path between `u` and its ancestor `c`. -/
lemma vert_of_pathC_add_ne_zero {u c : P} (hc : c ∈ T.anc u) {d : D}
    (h : T.pathC u d + T.pathC c d ≠ 0) :
    M.vert d = c ∨ (M.vert d ∈ T.anc u ∧ M.vert d ∉ T.anc c) := by
  obtain ⟨v, hv, hvc, hvr, rfl | rfl⟩ := T.pathC_add_ne_zero hc h
  · exact Or.inr ⟨by rw [T.vert_par]; exact hv, by rw [T.vert_par]; exact hvc⟩
  · rw [← T.parent_of_ne hvr]
    by_cases hp : T.parent v ∈ T.anc c
    · left
      exact T.eq_of_mem_anc_of_mem_anc hp (T.mem_anc_parent_of_notMem hc hv hvc hvr)
    · exact Or.inr ⟨T.parent_mem_anc hv, hp⟩

variable [Fintype D] [Fintype P]

/-- **Uniqueness of fundamental cochains.** A closed cochain supported on the tree darts and on
a dart `e` off the tree, with value `1` at `e`, is the fundamental cochain of `e`. -/
theorem eq_fund (c : D → ZMod 2) (hcα : ∀ d, c (M.α d) = c d)
    (hc : ∀ v, ∑ d with M.vert d = v, c d = 0) {e : D} (he : ¬ T.IsTree e) (hce : c e = 1)
    (hsupp : ∀ d, c d ≠ 0 → T.IsTree d ∨ d = e ∨ d = M.α e) : c = T.fund e := by
  have hfe := T.fund_self he
  have hsupp' : ∀ d, c d + T.fund e d ≠ 0 → T.IsTree d := by
    intro d hd
    by_contra ht
    by_cases hde : d = e ∨ d = M.α e
    · rcases hde with rfl | rfl
      · exact hd (by rw [hce, hfe]; decide)
      · exact hd (by rw [hcα, hce, T.fund_α_apply, hfe]; decide)
    · push Not at hde
      have h1 : c d = 0 := by
        by_contra h1
        rcases hsupp d h1 with h2 | h2 | h2
        · exact ht h2
        · exact hde.1 h2
        · exact hde.2 h2
      have h2 : T.fund e d = 0 := by
        by_contra h2
        rcases T.fund_ne_zero h2 with h3 | h3 | h3
        · exact ht h3
        · exact hde.1 h3
        · exact hde.2 h3
      exact hd (by rw [h1, h2, add_zero])
  have h0 := T.eq_zero (fun d => c d + T.fund e d) (fun d => by rw [hcα, T.fund_α_apply])
    (fun v => by rw [sum_add_distrib, hc, T.sum_fund, add_zero]) hsupp'
  funext d
  exact Kasteleyn.ZMod.two_eq_of_add_eq_zero (h0 d)

end SpTree

/-! ### Redirected trees -/

namespace SpTree

variable [DecidableEq P]

/-- **A redirected spanning tree.** The vertices of `R` take the dart `nxt v` to a new parent of
the same height, and a potential `pos` (at most `N`) decreases along these darts; the new height
is `height * (N + 1) + pos`. -/
noncomputable def redirect (T : M.SpTree) (R : Finset P) (nxt : P → D) (pos : P → ℕ) (N : ℕ)
    (_hroot : T.root ∉ R) (hvert : ∀ v ∈ R, M.vert (nxt v) = v)
    (hh : ∀ v ∈ R, T.height (M.vert (M.α (nxt v))) = T.height v)
    (hpos : ∀ v ∈ R, pos (M.vert (M.α (nxt v))) < pos v) (hN : ∀ v, pos v ≤ N) : M.SpTree where
  root := T.root
  par v h := if v ∈ R then nxt v else T.par v h
  height v := T.height v * (N + 1) + pos v
  vert_par v h := by
    split_ifs with hv
    · exact hvert v hv
    · exact T.vert_par v h
  height_lt v h := by
    split_ifs with hv
    · rw [hh v hv]
      have := hpos v hv
      omega
    · have h1 := T.height_lt v h
      have h2 := hN (M.vert (M.α (T.par v h)))
      have h3 := Nat.mul_le_mul_right (N + 1) (Nat.succ_le_of_lt h1)
      nlinarith

section Redirect

variable (T : M.SpTree) {R : Finset P} {nxt : P → D} {pos : P → ℕ} {N : ℕ}
  {hroot : T.root ∉ R} {hvert : ∀ v ∈ R, M.vert (nxt v) = v}
  {hh : ∀ v ∈ R, T.height (M.vert (M.α (nxt v))) = T.height v}
  {hpos : ∀ v ∈ R, pos (M.vert (M.α (nxt v))) < pos v} {hN : ∀ v, pos v ≤ N}

@[simp] lemma redirect_root : (T.redirect R nxt pos N hroot hvert hh hpos hN).root = T.root := rfl

lemma redirect_height (v : P) :
    (T.redirect R nxt pos N hroot hvert hh hpos hN).height v = T.height v * (N + 1) + pos v :=
  rfl

lemma redirect_par_of_mem {v : P} (h : v ≠ T.root) (hv : v ∈ R) :
    (T.redirect R nxt pos N hroot hvert hh hpos hN).par v h = nxt v := by
  simp [redirect, hv]

lemma redirect_par_of_notMem {v : P} (h : v ≠ T.root) (hv : v ∉ R) :
    (T.redirect R nxt pos N hroot hvert hh hpos hN).par v h = T.par v h := by
  simp [redirect, hv]

lemma redirect_parent_of_notMem {v : P} (hv : v ∉ R) :
    (T.redirect R nxt pos N hroot hvert hh hpos hN).parent v = T.parent v := by
  by_cases h : v = T.root
  · subst h
    simp [parent]
  · rw [SpTree.parent_of_ne _ (by exact h), T.parent_of_ne h, redirect_par_of_notMem T h hv]

lemma redirect_parent_of_mem {v : P} (hv : v ∈ R) :
    (T.redirect R nxt pos N hroot hvert hh hpos hN).parent v = M.vert (M.α (nxt v)) := by
  have h : v ≠ T.root := fun h => hroot (h ▸ hv)
  rw [SpTree.parent_of_ne _ (by exact h), redirect_par_of_mem T h hv]

/-- Root paths avoiding the redirected vertices are unchanged. -/
lemma redirect_anc {v : P} (hv : ∀ u ∈ T.anc v, u ∉ R) :
    (T.redirect R nxt pos N hroot hvert hh hpos hN).anc v = T.anc v := by
  induction v using T.induction with
  | hroot =>
    rw [T.anc_root]
    exact (T.redirect R nxt pos N hroot hvert hh hpos hN).anc_root
  | hstep v hv' ih =>
    have hvR := hv v (T.mem_anc_self v)
    rw [SpTree.anc_of_ne _ (by exact hv'), T.anc_of_ne hv', redirect_parent_of_notMem T hvR,
      ih fun u hu => hv u (by rw [T.anc_of_ne hv']; exact mem_insert_of_mem hu)]

variable [DecidableEq D] in
/-- Root path cochains avoiding the redirected vertices are unchanged. -/
lemma redirect_pathC {v : P} (hv : ∀ u ∈ T.anc v, u ∉ R) :
    (T.redirect R nxt pos N hroot hvert hh hpos hN).pathC v = T.pathC v := by
  induction v using T.induction with
  | hroot =>
    rw [T.pathC_root]
    exact (T.redirect R nxt pos N hroot hvert hh hpos hN).pathC_root
  | hstep v hv' ih =>
    have hvR := hv v (T.mem_anc_self v)
    rw [SpTree.pathC_of_ne _ (by exact hv'), T.pathC_of_ne hv', redirect_parent_of_notMem T hvR,
      redirect_par_of_notMem T hv' hvR,
      ih fun u hu => hv u (by rw [T.anc_of_ne hv']; exact mem_insert_of_mem hu)]

/-- The tree darts of a redirected tree. -/
lemma redirect_isTree {d : D} :
    (T.redirect R nxt pos N hroot hvert hh hpos hN).IsTree d ↔
      ∃ v, ∃ h : v ≠ T.root, (v ∈ R ∧ (d = nxt v ∨ d = M.α (nxt v))) ∨
        (v ∉ R ∧ (d = T.par v h ∨ d = M.α (T.par v h))) := by
  constructor
  · rintro ⟨v, h, hd⟩
    by_cases hv : v ∈ R
    · rw [redirect_par_of_mem T h hv] at hd
      exact ⟨v, h, Or.inl ⟨hv, hd⟩⟩
    · rw [redirect_par_of_notMem T h hv] at hd
      exact ⟨v, h, Or.inr ⟨hv, hd⟩⟩
  · rintro ⟨v, h, ⟨hv, hd⟩ | ⟨hv, hd⟩⟩
    · exact ⟨v, h, by rw [redirect_par_of_mem T h hv]; exact hd⟩
    · exact ⟨v, h, by rw [redirect_par_of_notMem T h hv]; exact hd⟩

end Redirect

end SpTree

/-! ### Indices along a simple cycle -/

namespace SCycle

variable (C : M.SCycle)

/-- The index following `j` along the cycle. -/
def suc (j : ℕ) : ℕ := if j + 1 < C.k then j + 1 else 0

/-- The index preceding `j` along the cycle. -/
def pre (j : ℕ) : ℕ := if j = 0 then C.k - 1 else j - 1

/-- The index `m` steps after `s` along the cycle. -/
def idxAt (s m : ℕ) : ℕ := if s + m < C.k then s + m else s + m - C.k

/-- The number of steps from `s` to `j` along the cycle. -/
def off (s j : ℕ) : ℕ := if s ≤ j then j - s else j + C.k - s

lemma vert_α_d_suc {j : ℕ} (hj : j < C.k) : M.vert (M.α (C.d j)) = M.vert (C.d (C.suc j)) :=
  C.vert_α_d hj

lemma suc_lt {j : ℕ} (hj : j < C.k) : C.suc j < C.k := by
  unfold suc; split_ifs <;> omega

lemma pre_lt {j : ℕ} (hj : j < C.k) : C.pre j < C.k := by
  unfold pre; split_ifs <;> omega

lemma suc_pre {j : ℕ} (hj : j < C.k) : C.suc (C.pre j) = j := by
  unfold suc pre; split_ifs <;> omega

lemma idxAt_lt {s m : ℕ} (hs : s < C.k) (hm : m < C.k) : C.idxAt s m < C.k := by
  unfold idxAt; split_ifs <;> omega

lemma off_lt {s j : ℕ} (hs : s < C.k) (hj : j < C.k) : C.off s j < C.k := by
  unfold off; split_ifs <;> omega

lemma off_idxAt {s m : ℕ} (hs : s < C.k) (hm : m < C.k) : C.off s (C.idxAt s m) = m := by
  unfold off idxAt; split_ifs <;> omega

lemma idxAt_off {s j : ℕ} (hs : s < C.k) (hj : j < C.k) : C.idxAt s (C.off s j) = j := by
  unfold off idxAt; split_ifs <;> omega

lemma pre_idxAt {s m : ℕ} (hs : s < C.k) (hm : m + 1 < C.k) :
    C.pre (C.idxAt s (m + 1)) = C.idxAt s m := by
  unfold pre idxAt; split_ifs <;> first | contradiction | omega

lemma off_pre {s j : ℕ} (hs : s < C.k) (hj : j < C.k) (h : 1 ≤ C.off s j) :
    C.off s (C.pre j) = C.off s j - 1 := by
  unfold off pre at *; split_ifs at * <;> omega

lemma idxAt_idxAt {s L j : ℕ} (hs : s < C.k) (hL : L + j < C.k) :
    C.idxAt (C.idxAt s L) j = C.idxAt s (L + j) := by
  unfold idxAt; split_ifs <;> omega

/-- In a proper simple cycle, distinct indices carry darts of distinct edges. -/
lemma ne_of_proper (hC : C.Proper) {i j : ℕ} (hi : i < C.k) (hj : j < C.k) (hij : i ≠ j) :
    C.d j ≠ C.d i ∧ C.d j ≠ M.α (C.d i) := by
  refine ⟨fun h => hij (C.inj i hi j hj (by rw [h])), fun h => ?_⟩
  have h1 : M.vert (C.d j) = M.vert (C.d (C.suc i)) := by rw [h, C.vert_α_d_suc hi]
  have h2 : M.vert (C.d (C.suc j)) = M.vert (C.d i) := by
    rw [← C.vert_α_d_suc hj, h, M.α_α]
  have e1 := C.inj _ hj _ (C.suc_lt hi) h1
  have e2 := C.inj _ (C.suc_lt hj) _ hi h2
  unfold suc at e1 e2
  by_cases hk2 : C.k = 2
  · apply hC hk2
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [show j = 1 by omega] at h
      rw [h, M.α_α]
    · rw [show j = 0 by omega] at h
      exact h
  · split_ifs at e1 e2 <;> omega

variable [DecidableEq P]

open Classical in
/-- The index of a vertex of the cycle. -/
noncomputable def idx (v : P) : ℕ :=
  if h : ∃ j, j < C.k ∧ M.vert (C.d j) = v then Nat.find h else 0

lemma idx_spec {v : P} (hv : v ∈ C.verts) : C.idx v < C.k ∧ M.vert (C.d (C.idx v)) = v := by
  classical
  have h : ∃ j, j < C.k ∧ M.vert (C.d j) = v := by
    obtain ⟨j, hj, e⟩ := C.mem_verts.1 hv
    exact ⟨j, hj, e⟩
  rw [idx, dite_eq_left h]
  exact Nat.find_spec h

lemma idx_vert {j : ℕ} (hj : j < C.k) : C.idx (M.vert (C.d j)) = j := by
  have := C.idx_spec (C.mem_verts.2 ⟨j, hj, rfl⟩)
  exact C.inj _ this.1 _ hj this.2

/-! ### Arcs -/

variable [DecidableEq D]

/-- The cochain of the arc of `m` darts of the cycle from index `s`. -/
noncomputable def arcS (s m : ℕ) : D → ZMod 2 := ∑ j ∈ range m, M.edgeInd (C.d (C.idxAt s j))

lemma arcS_succ (s m : ℕ) : C.arcS s (m + 1) = C.arcS s m + M.edgeInd (C.d (C.idxAt s m)) := by
  simp [arcS, sum_range_succ]

/-- The edges of a proper simple cycle, as a sum over its darts. -/
lemma sum_edgeInd (hC : C.Proper) : ∑ j ∈ range C.k, M.edgeInd (C.d j) = C.cochain := by
  classical
  funext d
  rw [Finset.sum_apply]
  by_cases hd : C.Mem d
  · obtain ⟨i, hi, hdi⟩ := hd
    rw [sum_eq_single_of_mem i (mem_range.2 hi) fun j hj hji => ?_]
    · rcases hdi with rfl | rfl
      · simp [cochain, C.mem_d hi]
      · rw [edgeInd_α]; simp [cochain, (C.mem_α_iff).2 (C.mem_d hi)]
    · obtain ⟨h1, h2⟩ := C.ne_of_proper hC hi (mem_range.1 hj) (Ne.symm hji)
      rcases hdi with rfl | rfl
      · exact edgeInd_eq_zero (Ne.symm h1) (fun h => h2 (by rw [h, M.α_α]))
      · exact edgeInd_eq_zero (fun h => h2 h.symm) (fun h => h1 (M.α_injective h).symm)
  · have : C.cochain d = 0 := by simp [cochain, hd]
    rw [this]
    refine sum_eq_zero fun j hj => edgeInd_eq_zero (fun h => hd ⟨j, mem_range.1 hj, Or.inl h⟩)
      (fun h => hd ⟨j, mem_range.1 hj, Or.inr h⟩)

/-- **The two arcs between two indices make up the cycle.** -/
lemma arcS_add_arcS (hC : C.Proper) {s L : ℕ} (hs : s < C.k) (hL : L ≤ C.k) :
    C.arcS s L + C.arcS (C.idxAt s L) (C.k - L) = C.cochain := by
  rw [← C.sum_edgeInd hC]
  have h1 : C.arcS s L + C.arcS (C.idxAt s L) (C.k - L) =
      ∑ j ∈ range C.k, M.edgeInd (C.d (C.idxAt s j)) := by
    have e := sum_range_add (fun j => M.edgeInd (C.d (C.idxAt s j))) L (C.k - L)
    rw [show L + (C.k - L) = C.k by omega] at e
    rw [e, arcS, arcS]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [C.idxAt_idxAt hs (by rw [mem_range] at hj; omega)]
  rw [h1]
  refine sum_nbij' (C.idxAt s) (C.off s) (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
    (fun j hj => ?_) (fun _ _ => rfl)
  · exact mem_range.2 (C.idxAt_lt hs (mem_range.1 hj))
  · exact mem_range.2 (C.off_lt hs (mem_range.1 hj))
  · exact C.off_idxAt hs (mem_range.1 hj)
  · exact C.idxAt_off hs (mem_range.1 hj)

end SCycle

/-! ### Redirecting a tree along an arc -/

namespace SCycle

variable (C : M.SCycle) [DecidableEq P]

/-- The vertices `1, …, ℓ` steps after the index `s`. -/
noncomputable def arcR (s ℓ : ℕ) : Finset P :=
  C.verts.filter fun v => 1 ≤ C.off s (C.idx v) ∧ C.off s (C.idx v) ≤ ℓ

/-- The dart from a vertex of the cycle back to the previous one. -/
noncomputable def arcNxt (v : P) : D := M.α (C.d (C.pre (C.idx v)))

/-- The number of steps from `s`, on the redirected vertices. -/
noncomputable def arcPos (s ℓ : ℕ) (v : P) : ℕ :=
  if v ∈ C.arcR s ℓ then C.off s (C.idx v) else 0

lemma mem_arcR {s ℓ : ℕ} {v : P} :
    v ∈ C.arcR s ℓ ↔ v ∈ C.verts ∧ 1 ≤ C.off s (C.idx v) ∧ C.off s (C.idx v) ≤ ℓ := by
  simp [arcR]

lemma vert_arcNxt {s ℓ : ℕ} {v : P} (hv : v ∈ C.arcR s ℓ) : M.vert (C.arcNxt v) = v := by
  obtain ⟨hi, he⟩ := C.idx_spec (C.mem_arcR.1 hv).1
  rw [arcNxt, C.vert_α_d_suc (C.pre_lt hi), C.suc_pre hi, he]

lemma vert_α_arcNxt (v : P) : M.vert (M.α (C.arcNxt v)) = M.vert (C.d (C.pre (C.idx v))) := by
  rw [arcNxt, M.α_α]

end SCycle

namespace SpTree

variable (T : M.SpTree) [DecidableEq P] (C : M.SCycle)

/-- **The tree redirected along an arc** of `ℓ` steps of a simple cycle from the index `s`:
the vertices `1, …, ℓ` steps after `s` take the previous vertex of the cycle as their parent.
The vertices of the cycle must have the same height and the root must be off the cycle. -/
noncomputable def arcTree (s ℓ : ℕ) (hs : s < C.k) (hr : T.root ∉ C.verts)
    (hC : ∀ i < C.k, T.height (M.vert (C.d i)) = T.height (M.vert (C.d s))) : M.SpTree :=
  T.redirect (C.arcR s ℓ) C.arcNxt (C.arcPos s ℓ) C.k
    (fun h => hr (C.mem_arcR.1 h).1) (fun v hv => C.vert_arcNxt hv)
    (fun v hv => by
      obtain ⟨hi, he⟩ := C.idx_spec (C.mem_arcR.1 hv).1
      rw [C.vert_α_arcNxt, hC _ (C.pre_lt hi), ← he, hC _ hi])
    (fun v hv => by
      obtain ⟨hv1, h1, h2⟩ := C.mem_arcR.1 hv
      obtain ⟨hi, he⟩ := C.idx_spec hv1
      have hp := C.off_pre hs hi h1
      rw [C.vert_α_arcNxt, SCycle.arcPos, SCycle.arcPos, ite_eq_left hv, C.idx_vert (C.pre_lt hi)]
      split_ifs <;> omega)
    (fun v => by
      unfold SCycle.arcPos
      split_ifs with h
      · exact (C.off_lt hs (C.idx_spec (C.mem_arcR.1 h).1).1).le
      · exact Nat.zero_le _)

section ArcTree

variable {s ℓ : ℕ} {hs : s < C.k} {hr : T.root ∉ C.verts}
  {hC : ∀ i < C.k, T.height (M.vert (C.d i)) = T.height (M.vert (C.d s))}

lemma height_lt_of_mem_anc {u v : P} (hu : u ∈ T.anc v) (huv : u ≠ v) :
    T.height u < T.height v := by
  by_cases hv : v = T.root
  · subst hv
    rw [T.anc_root, mem_singleton] at hu
    exact absurd hu huv
  · rw [T.anc_of_ne hv] at hu
    rcases mem_insert.1 hu with rfl | hu
    · exact absurd rfl huv
    · exact (T.height_le_of_mem_anc hu).trans_lt (T.height_parent_lt hv)

/-- Root paths of vertices not redirected and not higher than the cycle are unchanged. -/
lemma arcTree_pathC [DecidableEq D] {v : P} (hv : v ∉ C.arcR s ℓ)
    (hhv : T.height v ≤ T.height (M.vert (C.d s))) :
    (T.arcTree C s ℓ hs hr hC).pathC v = T.pathC v := by
  refine T.redirect_pathC fun u hu hu' => ?_
  by_cases huv : u = v
  · exact hv (huv ▸ hu')
  · have h1 := T.height_lt_of_mem_anc hu huv
    obtain ⟨hi, he⟩ := C.idx_spec (C.mem_arcR.1 hu').1
    have := hC _ hi
    rw [he] at this
    omega

/-- **Root paths along the arc.** -/
lemma pathC_arcTree [DecidableEq D] (hℓ : ℓ < C.k) {m : ℕ} (hm : m ≤ ℓ) :
    (T.arcTree C s ℓ hs hr hC).pathC (M.vert (C.d (C.idxAt s m))) =
      C.arcS s m + (T.arcTree C s ℓ hs hr hC).pathC (M.vert (C.d s)) := by
  induction m with
  | zero =>
    simp [SCycle.arcS, SCycle.idxAt, hs]
  | succ m ih =>
    have hlt : C.idxAt s (m + 1) < C.k := C.idxAt_lt hs (by omega)
    have hmem : M.vert (C.d (C.idxAt s (m + 1))) ∈ C.arcR s ℓ := by
      rw [C.mem_arcR, C.idx_vert hlt, C.off_idxAt hs (by omega)]
      exact ⟨C.mem_verts.2 ⟨_, hlt, rfl⟩, by omega, hm⟩
    have hne : M.vert (C.d (C.idxAt s (m + 1))) ≠ T.root := fun h => hr (h ▸ C.mem_verts.2
      ⟨_, hlt, rfl⟩)
    rw [SpTree.pathC_of_ne _ (by exact hne)]
    have e1 : (T.arcTree C s ℓ hs hr hC).par _ (by exact hne) =
        M.α (C.d (C.idxAt s m)) := by
      unfold arcTree
      rw [redirect_par_of_mem T hne hmem, SCycle.arcNxt, C.idx_vert hlt,
        C.pre_idxAt hs (by omega)]
    have e2 : (T.arcTree C s ℓ hs hr hC).parent (M.vert (C.d (C.idxAt s (m + 1)))) =
        M.vert (C.d (C.idxAt s m)) := by
      unfold arcTree
      rw [redirect_parent_of_mem T hmem, C.vert_α_arcNxt, C.idx_vert hlt,
        C.pre_idxAt hs (by omega)]
    rw [e1, e2, ih (by omega), C.arcS_succ]
    funext d
    simp only [Pi.add_apply, edgeInd_of_α]
    ring

/-- The tree darts of the redirected tree are tree darts of `T` or darts of the arc. -/
lemma isTree_arcTree {d : D} (h : (T.arcTree C s ℓ hs hr hC).IsTree d) :
    T.IsTree d ∨ ∃ m < ℓ, d = C.d (C.idxAt s m) ∨ d = M.α (C.d (C.idxAt s m)) := by
  unfold arcTree at h
  rw [redirect_isTree] at h
  obtain ⟨v, hv, ⟨hR, hd⟩ | ⟨_, hd⟩⟩ := h
  · right
    obtain ⟨hv1, h1, h2⟩ := C.mem_arcR.1 hR
    obtain ⟨hi, -⟩ := C.idx_spec hv1
    refine ⟨C.off s (C.idx v) - 1, by omega, ?_⟩
    have : C.pre (C.idx v) = C.idxAt s (C.off s (C.idx v) - 1) := by
      rw [← C.off_pre hs hi h1, C.idxAt_off hs (C.pre_lt hi)]
    rw [SCycle.arcNxt, this] at hd
    rcases hd with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (M.α_α _)
  · exact Or.inl ⟨v, hv, hd⟩

/-- **The fundamental cochain of the last dart of an arc** in the tree redirected along the
arc: the arc, closed up by the root paths of its two ends. -/
lemma fund_arcTree [DecidableEq D] [Fintype D] {L : ℕ} (hL : 1 ≤ L)
    (hLk : L < C.k) :
    (T.arcTree C s (L - 1) hs hr hC).fund (C.d (C.idxAt s (L - 1))) =
      C.arcS s L + T.pathC (M.vert (C.d s)) + T.pathC (M.vert (C.d (C.idxAt s L))) := by
  have hlt : C.idxAt s (L - 1) < C.k := C.idxAt_lt hs (by omega)
  have hlt' : C.idxAt s L < C.k := C.idxAt_lt hs hLk
  have hsR : M.vert (C.d s) ∉ C.arcR s (L - 1) := by
    rw [C.mem_arcR, C.idx_vert hs]
    unfold SCycle.off
    simp
  have haR : M.vert (C.d (C.idxAt s L)) ∉ C.arcR s (L - 1) := by
    rw [C.mem_arcR, C.idx_vert hlt', C.off_idxAt hs hLk]
    omega
  have hhd : C.suc (C.idxAt s (L - 1)) = C.idxAt s L := by
    unfold SCycle.suc SCycle.idxAt
    split_ifs <;> first | contradiction | omega
  funext d
  rw [fund_apply, C.vert_α_d_suc hlt, hhd,
    T.pathC_arcTree C (by omega) (le_refl _),
    T.arcTree_pathC C hsR le_rfl, T.arcTree_pathC C haR (le_of_eq (hC _ hlt'))]
  have : C.arcS s L = C.arcS s (L - 1) + M.edgeInd (C.d (C.idxAt s (L - 1))) := by
    rw [← C.arcS_succ, Nat.sub_add_cancel hL]
  rw [this]
  simp only [Pi.add_apply]
  ring

end ArcTree

/-- The last dart of an arc is off the redirected tree, if no dart of the cycle is a tree dart
of `T`. -/
lemma not_isTree_arcTree [DecidableEq D] {s : ℕ} {hs : s < C.k} {hr : T.root ∉ C.verts}
    {hC : ∀ i < C.k, T.height (M.vert (C.d i)) = T.height (M.vert (C.d s))} (hCp : C.Proper)
    (hnt : ∀ i < C.k, ¬ T.IsTree (C.d i)) {L : ℕ} (hL : 1 ≤ L) (hLk : L < C.k) :
    ¬ (T.arcTree C s (L - 1) hs hr hC).IsTree (C.d (C.idxAt s (L - 1))) := by
  intro h
  rcases T.isTree_arcTree C h with h | ⟨m, hm, h⟩
  · exact hnt _ (C.idxAt_lt hs (by omega)) h
  · have hne : C.idxAt s m ≠ C.idxAt s (L - 1) := by
      intro e
      have := congrArg (C.off s) e
      rw [C.off_idxAt hs (by omega), C.off_idxAt hs (by omega)] at this
      omega
    obtain ⟨h1, h2⟩ := C.ne_of_proper hCp (C.idxAt_lt hs (by omega)) (C.idxAt_lt hs (by omega))
      hne
    rcases h with h | h
    · exact h1 h
    · exact h2 h

end SpTree

/-! ### Separation by a simple cycle -/

/-- **Separation by a simple cycle.** The simple cycle `C` is the boundary of the set of faces
`Z` (an edge has exactly one side in `Z` if and only if it lies on `C`); the vertices off `C`
are split into `A`, whose faces lie in `Z`, and `B`, whose faces lie off `Z`; no edge joins `A`
and `B`. -/
structure IsCycleSep (C : M.SCycle) (Z : Finset M.Face) (A B : Finset P) [DecidableEq P]
    [Fintype P] : Prop where
  bd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d
  cover : C.verts ∪ A ∪ B = univ
  disjA : Disjoint C.verts A
  disjB : Disjoint C.verts B
  disjAB : Disjoint A B
  inA : ∀ d, M.vert d ∈ A → M.face d ∈ Z
  inB : ∀ d, M.vert d ∈ B → M.face d ∉ Z
  noEdge : ∀ d, M.vert d ∈ A → M.vert (M.α d) ∉ B

section Sides

variable [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]

/-- The vertices off `C` with a face in `Z`. -/
noncomputable def sideIn (C : M.SCycle) (Z : Finset M.Face) : Finset P :=
  by classical exact {v | v ∉ C.verts ∧ ∃ d, M.vert d = v ∧ M.face d ∈ Z}

/-- The vertices off `C` with no face in `Z`. -/
noncomputable def sideOut (C : M.SCycle) (Z : Finset M.Face) : Finset P :=
  {v | v ∉ C.verts ∧ v ∉ sideIn C Z}

lemma mem_sideIn {C : M.SCycle} {Z : Finset M.Face} {v : P} :
    v ∈ sideIn C Z ↔ v ∉ C.verts ∧ ∃ d, M.vert d = v ∧ M.face d ∈ Z := by
  classical
  simp [sideIn]

lemma mem_sideOut {C : M.SCycle} {Z : Finset M.Face} {v : P} :
    v ∈ sideOut C Z ↔ v ∉ C.verts ∧ v ∉ sideIn C Z := by
  simp [sideOut]

/-- Around a vertex off the boundary cycle, all faces lie on the same side. -/
lemma face_iff_of_notMem_verts {C : M.SCycle} {Z : Finset M.Face}
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) {v : P} (hv : v ∉ C.verts)
    {d d' : D} (hd : M.vert d = v) (hd' : M.vert d' = v) : M.face d ∈ Z ↔ M.face d' ∈ Z := by
  obtain ⟨n, rfl⟩ := M.exists_σ_pow_eq (hd.trans hd'.symm)
  clear hd'
  induction n with
  | zero => rfl
  | succ n ih =>
    have hx : ¬ C.Mem ((M.σ ^ n) d) := fun h =>
      hv (by rw [← hd, ← M.vert_σ_pow n d]; exact C.mem_verts_of_mem h)
    rw [pow_succ', Equiv.Perm.mul_apply, face_σ, ← (hbd _).2 hx]
    exact ih

/-- **A simple cycle bounding a set of faces separates.** -/
theorem isCycleSep_of_bd {C : M.SCycle} {Z : Finset M.Face}
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) :
    IsCycleSep C Z (sideIn C Z) (sideOut C Z) := by
  have hinA : ∀ d, M.vert d ∈ sideIn C Z → M.face d ∈ Z := by
    intro d hd
    obtain ⟨hv, d', hd', hZ⟩ := mem_sideIn.1 hd
    exact (face_iff_of_notMem_verts hbd hv hd' rfl).1 hZ
  have hinB : ∀ d, M.vert d ∈ sideOut C Z → M.face d ∉ Z := by
    intro d hd hZ
    obtain ⟨hv, hn⟩ := mem_sideOut.1 hd
    exact hn (mem_sideIn.2 ⟨hv, d, rfl, hZ⟩)
  refine ⟨hbd, ?_, ?_, ?_, ?_, hinA, hinB, fun d hA hB => ?_⟩
  · ext v
    simp only [mem_union, mem_univ, iff_true]
    by_cases h1 : v ∈ C.verts
    · exact Or.inl (Or.inl h1)
    by_cases h2 : v ∈ sideIn C Z
    · exact Or.inl (Or.inr h2)
    · exact Or.inr (mem_sideOut.2 ⟨h1, h2⟩)
  · exact disjoint_left.2 fun v h1 h2 => (mem_sideIn.1 h2).1 h1
  · exact disjoint_left.2 fun v h1 h2 => (mem_sideOut.1 h2).1 h1
  · exact disjoint_left.2 fun v h1 h2 => (mem_sideOut.1 h2).2 h1
  · have h1 := hinA d hA
    have h2 := hinB (M.α d) hB
    have : C.Mem d := by
      by_contra hm
      exact h2 (((hbd d).2 hm).1 h1)
    exact (mem_sideIn.1 hA).1 (C.mem_verts_of_mem this)

lemma bd_compl {C : M.SCycle} {Z : Finset M.Face}
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) :
    ∀ d, (M.face d ∈ Zᶜ ↔ M.face (M.α d) ∈ Zᶜ) ↔ ¬ C.Mem d := by
  intro d
  rw [mem_compl, mem_compl, ← hbd d]
  tauto

/-- The boundary relation for a fundamental cycle and its inside. -/
lemma SpTree.bd_inside (hM : M.IsPlane) (T : M.SpTree) {δ : D} (hδ : ¬ T.IsTree δ) :
    ∀ d, (M.face d ∈ T.inside δ ↔ M.face (M.α d) ∈ T.inside δ) ↔ ¬ (T.fcycle δ).Mem d := by
  intro d
  rw [SpTree.inside_iff hM, ← not_ne_iff, SpTree.fund_ne_zero_iff hδ]
  rfl

lemma SpTree.sideIn_inside (T : M.SpTree) {δ : D} (hδ : ¬ T.IsTree δ) :
    sideIn (T.fcycle δ) (T.inside δ) = T.inC δ := by
  ext v
  rw [mem_sideIn, SpTree.fcycle_verts hδ]
  simp [SpTree.inC]

end Sides

end Map

end PlanarSeparator
