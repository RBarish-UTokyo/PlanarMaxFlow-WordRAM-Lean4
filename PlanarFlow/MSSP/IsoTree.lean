module

public import PlanarFlow.MSSP.Isolate
public import PlanarFlow.STFlow.Tree

/-!
# Isolating weights from a spanning tree of the dual graph

`PlanarFlow/MSSP/Isolate.lean` proves that an isolating weight exists (`exists_isoW`: the sum,
over the faces `y`, of the unit flows of dual paths from `y` to the exceptional face). Here the
paths are those of a **rooted spanning tree `C` of the dual graph** (`STFlow.DTree`, as the
initial cotree of Klein's program), so that the weight has a closed form computable in linear
time:

* `tsz C y`: the number of faces of the subtree of `y` (the faces `x` with `y` an ancestor);
* `treeW C d`: `tsz y` on the dart `rev (par y)` (from `y` to its parent, `y ≠ root`),
  `- tsz y` on `par y`, and `0` on the darts off the tree (`treeW_rev_par`, `treeW_par`,
  `treeW_off`);
* `treeW_isoW`, `abs_treeW_le`: **`treeW C` is an isolating weight with the exceptional face
  `C.root`, at most `#F` in absolute value** (`sum_dflow_tpath`: it is the sum of the unit flows
  of the tree paths `tpath C x` from every face to the root; `isoW_of_walks`).
* `szFold C l`: the sizes computed by the pass over a list `l` of faces **from its end**, adding
  the value of `y` to that of its parent; `szFold_eq_tsz`: over the non-root faces in an order of
  nondecreasing depth (`Klein.Orders`, the order of the cotree in Klein's input), the pass leaves
  `tsz C y` at every face `y ≠ root` (`szFold_eq`: the invariant, counting the faces reaching `y`
  through the faces already passed).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace MSSP

open Finset CombMap STFlow

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-! ### Isolating weights from dual walks -/

/-- **The sum of the unit flows of simple dual walks from every face to `f₀` is an isolating
weight**, at most `#F` in absolute value (the proof of `exists_isoW`, for given walks). -/
theorem isoW_of_walks {f₀ : F} (L : F → List D) (hL : ∀ y, LWalk (dualGraph M) y f₀ (L y))
    (hLn : ∀ y, ((L y).map M.face).Nodup) :
    IsoW M f₀ (fun d => ∑ y, dflow M (L y) d) ∧
      ∀ d, |∑ y, dflow M (L y) d| ≤ Fintype.card F := by
  refine ⟨⟨fun d => ?_, fun f hf => ?_⟩, fun d => ?_⟩
  · simp only [dflow_antisymm _ d, Finset.sum_neg_distrib]
  · have : curl M (fun d => ∑ y, dflow M (L y) d) f = ∑ y, curl M (dflow M (L y)) f := by
      simp only [curl]; rw [Finset.sum_comm]
    rw [this]
    simp only [curl_dflow (hL _), Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    have : ¬ f₀ = f := fun h => hf h.symm
    simp [this]
  · calc |∑ y, dflow M (L y) d| ≤ ∑ y, |dflow M (L y) d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _y : F, (1 : ℤ) := Finset.sum_le_sum fun y _ => abs_dflow_le (hLn y) d
      _ = Fintype.card F := by simp

/-! ### Depths along the paths to the root -/

section Tree

variable (C : DTree M)

lemma depth_iter (x : F) (i : ℕ) : C.depth (C.up^[i] x) = C.depth x - i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    by_cases h : C.up^[i] x = C.root
    · rw [h, C.up_root, C.depth_root]
      have : C.depth x ≤ i := by
        by_contra h'
        exact C.iterate_ne_root (show i < C.depth x by omega) h
      omega
    · rw [C.depth_up h] at ih; omega

lemma depth_pos {a : F} (ha : a ≠ C.root) : 0 < C.depth a := by
  rw [C.depth_up ha]; omega

lemma iter_ne_self {a : F} (ha : a ≠ C.root) {k : ℕ} (hk : 0 < k) : C.up^[k] a ≠ a := by
  intro h
  have h1 := depth_iter C a k
  rw [h] at h1
  have := depth_pos C ha
  omega

lemma up_ne_self {a : F} (ha : a ≠ C.root) : C.up a ≠ a := iter_ne_self C ha (k := 1) one_pos

/-- Two parent darts are never reverse to each other. -/
lemma par_ne_rev_par {y u : F} (hy : y ≠ C.root) (hu : u ≠ C.root) :
    C.par u ≠ M.rev (C.par y) := by
  intro h
  have h1 : C.up u = y := by rw [C.up_of_ne hu, h, C.head_par y hy]
  have h2 : C.up y = u := by
    rw [C.up_of_ne hy, ← M.rev_rev (C.par y), ← h, C.head_par u hu]
  have e1 := C.depth_up hu
  have e2 := C.depth_up hy
  rw [h1] at e1; rw [h2] at e2
  omega

/-! ### The tree paths -/

/-- The path of the tree from `x` to the root: the darts `rev (par z)` from `z = x` up. -/
def tpath (x : F) : List D :=
  (List.range (C.depth x)).map fun i => M.rev (C.par (C.up^[i] x))

lemma tpath_cons {x : F} (hx : x ≠ C.root) :
    tpath C x = M.rev (C.par x) :: tpath C (C.up x) := by
  unfold tpath
  rw [C.depth_up hx, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Function.iterate_zero, id_eq, List.cons.injEq, true_and]
  exact List.map_congr_left fun i _ => by simp [Function.comp, Function.iterate_succ_apply]

lemma tpath_walk : ∀ (n : ℕ) (x : F), C.depth x = n → LWalk (dualGraph M) x C.root (tpath C x)
  | 0, x, h => by
    have hx : x = C.root := by have := C.iterate_depth x; rw [h] at this; exact this
    subst hx
    have : tpath C C.root = [] := by simp [tpath, C.depth_root]
    rw [this]; exact LWalk.nil _
  | n + 1, x, h => by
    have hx : x ≠ C.root := fun hx => by rw [hx, C.depth_root] at h; omega
    rw [tpath_cons C hx]
    have ih := tpath_walk n (C.up x) (by rw [C.depth_up hx] at h; omega)
    have e1 : (dualGraph M).dst (M.rev (C.par x)) = C.up x := by
      simp [dualGraph, M.rev_rev, C.up_of_ne hx]
    have e2 : (dualGraph M).src (M.rev (C.par x)) = x := C.head_par x hx
    have ih' : LWalk (dualGraph M) ((dualGraph M).dst (M.rev (C.par x))) C.root
        (tpath C (C.up x)) := by rw [e1]; exact ih
    have := LWalk.cons (G := dualGraph M) (a := M.rev (C.par x)) ih'
    rwa [e2] at this

lemma tpath_nodup (x : F) : ((tpath C x).map M.face).Nodup := by
  have e : (tpath C x).map M.face = (List.range (C.depth x)).map fun i => C.up^[i] x := by
    unfold tpath
    rw [List.map_map]
    refine List.map_congr_left fun i hi => ?_
    exact C.head_par _ (C.iterate_ne_root (List.mem_range.1 hi))
  rw [e]
  refine List.Nodup.map_on (fun i hi j hj hij => ?_) List.nodup_range
  have hi' := List.mem_range.1 hi
  have hj' := List.mem_range.1 hj
  have h1 := depth_iter C x i
  have h2 := depth_iter C x j
  rw [hij] at h1
  omega

lemma mem_tpath {x : F} {d : D} :
    d ∈ tpath C x ↔ M.face d ≠ C.root ∧ d = M.rev (C.par (M.face d)) ∧ C.Anc (M.face d) x := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
    have hi' := List.mem_range.1 hi
    have hne := C.iterate_ne_root hi'
    rw [C.head_par _ hne]
    exact ⟨hne, rfl, i, rfl⟩
  · rintro ⟨h1, h2, n, hn⟩
    have hn' : n < C.depth x := by
      by_contra h'
      rw [C.iterate_of_le (by omega)] at hn
      exact h1 hn.symm
    refine List.mem_map.2 ⟨n, List.mem_range.2 hn', ?_⟩
    rw [hn, ← h2]

/-! ### The weight of the tree -/

open Classical in
/-- The number of faces of the subtree of `y`. -/
noncomputable def tsz (y : F) : ℕ := #{x | C.Anc y x}

open Classical in
/-- **The isolating weight of the tree**: `tsz y` on `rev (par y)`, `- tsz y` on `par y`. -/
noncomputable def treeW (d : D) : ℤ :=
  (if M.face d ≠ C.root ∧ d = M.rev (C.par (M.face d)) then (tsz C (M.face d) : ℤ) else 0) -
    (if M.face (M.rev d) ≠ C.root ∧ d = C.par (M.face (M.rev d)) then
      (tsz C (M.face (M.rev d)) : ℤ) else 0)

lemma sum_mem_tpath (d : D) :
    (∑ x, if d ∈ tpath C x then (1 : ℤ) else 0) =
      if M.face d ≠ C.root ∧ d = M.rev (C.par (M.face d)) then (tsz C (M.face d) : ℤ) else 0 := by
  classical
  by_cases h : M.face d ≠ C.root ∧ d = M.rev (C.par (M.face d))
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
    have e : ∀ x, (d ∈ tpath C x ↔ C.Anc (M.face d) x) := fun x => by
      rw [mem_tpath]; exact ⟨fun h' => h'.2.2, fun h' => ⟨h.1, h.2, h'⟩⟩
    simp_rw [e]
    rw [Finset.sum_boole]
    unfold tsz
    congr
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [ite_eq_right_of_eq_false _ _ (eq_false ?_)]
    rw [mem_tpath]
    exact fun h' => h ⟨h'.1, h'.2.1⟩

/-- **The weight of the tree is the sum of the unit flows of the tree paths.** -/
theorem sum_dflow_tpath (d : D) : ∑ x, dflow M (tpath C x) d = treeW C d := by
  simp only [dflow_eq_of_nodup (tpath_nodup C _), Finset.sum_sub_distrib]
  unfold treeW
  rw [sum_mem_tpath, sum_mem_tpath]
  congr 2
  exact propext (and_congr_right fun _ => M.rev_injective.eq_iff)

/-- **The weight of the tree is an isolating weight**, with the exceptional face the root. -/
theorem treeW_isoW : IsoW M C.root (treeW C) := by
  have h := (isoW_of_walks (tpath C) (fun y => tpath_walk C _ y rfl) (tpath_nodup C)).1
  have e : (fun d => ∑ y, dflow M (tpath C y) d) = treeW C := funext (sum_dflow_tpath C)
  rwa [e] at h

theorem abs_treeW_le (d : D) : |treeW C d| ≤ Fintype.card F := by
  rw [← sum_dflow_tpath]
  exact (isoW_of_walks (tpath C) (fun y => tpath_walk C _ y rfl) (tpath_nodup C)).2 d

lemma tsz_le (y : F) : tsz C y ≤ Fintype.card F := by
  classical
  unfold tsz
  exact card_le_univ _

lemma tsz_lt {y : F} (hy : y ≠ C.root) : tsz C y < Fintype.card F := by
  classical
  unfold tsz
  refine Finset.card_lt_univ_of_notMem (x := C.root) ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun h => hy (C.anc_root_iff.1 h)

lemma treeW_rev_par {y : F} (hy : y ≠ C.root) : treeW C (M.rev (C.par y)) = tsz C y := by
  unfold treeW
  rw [C.head_par y hy, ite_eq_left_of_eq_true _ _ (eq_true ⟨hy, rfl⟩), M.rev_rev,
    ite_eq_right_of_eq_false _ _ (eq_false ?_), sub_zero]
  rintro ⟨h1, h2⟩
  exact par_ne_rev_par C hy h1 h2.symm

lemma treeW_par {y : F} (hy : y ≠ C.root) : treeW C (C.par y) = - (tsz C y : ℤ) := by
  unfold treeW
  rw [C.head_par y hy, ite_eq_right_of_eq_false _ _ (eq_false ?_),
    ite_eq_left_of_eq_true _ _ (eq_true ⟨hy, rfl⟩), zero_sub]
  rintro ⟨h1, h2⟩
  exact par_ne_rev_par C h1 hy h2

lemma treeW_off {d : D} (h1 : ∀ y, y ≠ C.root → d ≠ C.par y)
    (h2 : ∀ y, y ≠ C.root → d ≠ M.rev (C.par y)) : treeW C d = 0 := by
  unfold treeW
  rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => h2 _ h.1 h.2)), ite_eq_right_of_eq_false _ _ (eq_false (fun h => h1 _ h.1 h.2)), sub_zero]

/-! ### The pass computing the sizes -/

/-- One step of the pass: the value of `y` added to that of its parent. -/
def szStep (y : F) (s : F → ℕ) : F → ℕ := Function.update s (C.up y) (s (C.up y) + s y)

/-- **The pass from the end of `l`**, from the value `1` everywhere. -/
def szFold (l : List F) : F → ℕ := l.foldr (szStep C) fun _ => 1

lemma szFold_cons (a : F) (l : List F) : szFold C (a :: l) = szStep C a (szFold C l) := rfl

/-- `x` reaches `y` through faces of `T` (the faces before `y`). -/
def RT (T : Finset F) (x y : F) : Prop := ∃ j, C.up^[j] x = y ∧ ∀ i < j, C.up^[i] x ∈ T

lemma rt_empty (x y : F) : RT C ∅ x y ↔ x = y := by
  constructor
  · rintro ⟨j, hj, hT⟩
    rcases j with _ | j
    · exact hj
    · exact absurd (hT 0 (by omega)) (Finset.notMem_empty _)
  · rintro rfl; exact ⟨0, rfl, fun i hi => absurd hi (by omega)⟩

section Insert

variable {C} {T : Finset F} {a : F} (ha : a ≠ C.root) (haT : a ∉ T)
  (hd : ∀ b ∈ T, C.depth a ≤ C.depth b)
include ha haT hd

lemma up_notMem : C.up a ∉ insert a T := by
  rw [Finset.mem_insert, not_or]
  refine ⟨up_ne_self C ha, fun h => ?_⟩
  have h1 := hd _ h
  have h2 := C.depth_up ha
  omega

lemma rt_insert_cases {x v : F} (h : RT C (insert a T) x v) :
    RT C T x v ∨ (v = C.up a ∧ RT C T x a) := by
  obtain ⟨j, hj, hT⟩ := h
  by_cases hit : ∃ i < j, C.up^[i] x = a
  · right
    obtain ⟨i, hi, hia⟩ := hit
    have hij : i + 1 = j := by
      by_contra hne
      have := hT (i + 1) (by omega)
      rw [Function.iterate_succ_apply', hia] at this
      exact up_notMem ha haT hd this
    refine ⟨by rw [← hj, ← hij, Function.iterate_succ_apply', hia], i, hia, fun i' hi' => ?_⟩
    have hm := hT i' (by omega)
    rcases Finset.mem_insert.1 hm with h' | h'
    · exfalso
      have : C.up^[i - i'] a = a := by
        conv_lhs => rw [← h']
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hi'.le, hia]
      exact iter_ne_self C ha (by omega) this
    · exact h'
  · left
    push Not at hit
    refine ⟨j, hj, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 (hT i hi) with h' | h'
    · exact absurd h' (hit i hi)
    · exact h'

lemma rt_mono {x v : F} (h : RT C T x v) : RT C (insert a T) x v := by
  obtain ⟨j, hj, hT⟩ := h
  exact ⟨j, hj, fun i hi => Finset.mem_insert_of_mem (hT i hi)⟩

lemma rt_up {x : F} (h : RT C T x a) : RT C (insert a T) x (C.up a) := by
  obtain ⟨j, hj, hT⟩ := h
  refine ⟨j + 1, by rw [Function.iterate_succ_apply', hj], fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | rfl
  · exact Finset.mem_insert_of_mem (hT i h')
  · rw [hj]; exact Finset.mem_insert_self _ _

lemma rt_disj {x : F} (h₁ : RT C T x (C.up a)) (h₂ : RT C T x a) : False := by
  obtain ⟨j₁, hj₁, hT₁⟩ := h₁
  obtain ⟨j₂, hj₂, -⟩ := h₂
  by_cases hlt : j₂ < j₁
  · exact haT (hj₂ ▸ hT₁ j₂ hlt)
  · have : C.up^[j₂ - j₁ + 1] a = a := by
      rw [Function.iterate_succ_apply, ← hj₁, ← Function.iterate_add_apply,
        Nat.sub_add_cancel (by omega), hj₂]
    exact iter_ne_self C ha (by omega) this

end Insert

open Classical in
/-- **The invariant of the pass**: from the end of a list of non-root faces without repetition
in an order of nondecreasing depth, the value at `y` is the number of faces reaching `y` through
the faces of the list. -/
theorem szFold_eq : ∀ (l : List F), l.Nodup → (∀ y ∈ l, y ≠ C.root) →
    l.Pairwise (fun a b => C.depth a ≤ C.depth b) → ∀ y, szFold C l y = #{x | RT C l.toFinset x y}
  | [], _, _, _, y => by
    have : (univ.filter fun x => RT C [].toFinset x y) = {y} := by
      ext x; simp [rt_empty]
    rw [this, card_singleton]; rfl
  | a :: l, hnd, hr, hpw, y => by
    rw [List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hpw
    have ha : a ≠ C.root := hr a (List.mem_cons_self ..)
    have haT : a ∉ l.toFinset := fun h => hnd.1 (List.mem_toFinset.1 h)
    have hd : ∀ b ∈ l.toFinset, C.depth a ≤ C.depth b := fun b hb => hpw.1 b (List.mem_toFinset.1 hb)
    have ih := szFold_eq l hnd.2 (fun y hy => hr y (List.mem_cons_of_mem _ hy)) hpw.2
    rw [szFold_cons, List.toFinset_cons]
    unfold szStep
    by_cases hy : y = C.up a
    · subst hy
      rw [Function.update_self, ih, ih, Finset.card_filter, Finset.card_filter, Finset.card_filter,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases h1 : RT C l.toFinset x (C.up a)
      · have h2 : ¬ RT C l.toFinset x a := fun h2 => rt_disj ha haT hd h1 h2
        rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_left_of_eq_true _ _ (eq_true (rt_mono ha haT hd h1))]
      · by_cases h2 : RT C l.toFinset x a
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true (rt_up ha haT hd h2))]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false ?_)]
          intro h
          rcases rt_insert_cases ha haT hd h with h' | h'
          · exact h1 h'
          · exact h2 h'.2
    · rw [Function.update_of_ne hy, ih]
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨rt_mono ha haT hd, fun h => ?_⟩
      rcases rt_insert_cases ha haT hd h with h' | h'
      · exact h'
      · exact absurd h'.1 hy

lemma szFold_le (l : List F) (hnd : l.Nodup) (hr : ∀ y ∈ l, y ≠ C.root)
    (hpw : l.Pairwise (fun a b => C.depth a ≤ C.depth b)) (y : F) :
    szFold C l y ≤ Fintype.card F := by
  classical
  rw [szFold_eq C l hnd hr hpw y]
  exact card_le_univ _

/-- **The pass over all the non-root faces leaves the sizes of the subtrees.** -/
theorem szFold_eq_tsz (l : List F) (hnd : l.Nodup) (hmem : ∀ y, y ∈ l ↔ y ≠ C.root)
    (hpw : l.Pairwise (fun a b => C.depth a ≤ C.depth b)) {y : F} (hy : y ≠ C.root) :
    szFold C l y = tsz C y := by
  classical
  rw [szFold_eq C l hnd (fun y hy => (hmem y).1 hy) hpw y]
  unfold tsz
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, -⟩; exact ⟨j, hj⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, hn, fun i hi => List.mem_toFinset.2 ((hmem _).2 fun h => hy ?_)⟩
    rw [← hn]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hi
    rw [show i + k + 1 = (k + 1) + i by ring, Function.iterate_add_apply, h, C.iterate_root]

end Tree

end MSSP

end PlanarFlow
