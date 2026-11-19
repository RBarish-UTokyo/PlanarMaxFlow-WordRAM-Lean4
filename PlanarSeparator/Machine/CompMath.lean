module

public import PlanarSeparator.Machine.PieceCall

/-!
# The separator of the components: the lists behind the program

Facts used by the program computing `PlanarSeparator.compSep` on the machine
(`PlanarSeparator/Machine/CompProg.lean`, `PlanarSeparator/Machine/CompSepProg.lean`): a vertex
set `U` of a graph on `Fin N` is given by the sorted list `ul U` of its vertices.

* `heavyC_eq`: the heavy component is the first vertex of `ul U` whose component is heavy
  (`List.find?`).
* `pU U i`: the union of the components of the first `i` vertices of `ul U`; `lightA_zero`,
  `lightA_eq`: the first part `lightA` when no component is heavy, from the first `i` at which
  `pU U (i + 1)` weighs at least a third of `U`.
* `sum_range_eq`: a sum over an injective enumeration of a vertex set.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]

/-- `if` with a true condition. -/
theorem iteT {α : Sort*} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

/-- `if` with a false condition. -/
theorem iteF {α : Sort*} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]

/-! ### The sorted list of a vertex set -/

/-- The vertices of `U` in increasing order. -/
abbrev ul (U : Finset (Fin N)) : List (Fin N) := clist (ord N) U

theorem ul_length (U : Finset (Fin N)) : (ul U).length = #U := length_clist_ord U

theorem lv_ul (U : Finset (Fin N)) {l : ℕ} (hl : l < (ul U).length) : lv U l = ((ul U)[l] : ℕ) := by
  unfold lv
  rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map]

theorem ul_lt_iff (U : Finset (Fin N)) {i j : ℕ} (hi : i < (ul U).length) (hj : j < (ul U).length) :
    (ul U)[i] < (ul U)[j] ↔ i < j := by
  have hmono : StrictMono (ul U).get := (clist_sorted U).strictMono_get
  exact hmono.lt_iff_lt (a := ⟨i, hi⟩) (b := ⟨j, hj⟩)

theorem ul_le_iff (U : Finset (Fin N)) {i j : ℕ} (hi : i < (ul U).length) (hj : j < (ul U).length) :
    (ul U)[i] ≤ (ul U)[j] ↔ i ≤ j := by
  rw [← not_lt, ← not_lt, ul_lt_iff U hj hi]

theorem ul_inj (U : Finset (Fin N)) {i j : ℕ} (hi : i < (ul U).length) (hj : j < (ul U).length)
    (h : (ul U)[i] = (ul U)[j]) : i = j := by
  have h1 := (ul_le_iff U hi hj).1 h.le
  have h2 := (ul_le_iff U hj hi).1 h.ge
  omega

theorem mem_ul (U : Finset (Fin N)) {v : Fin N} : v ∈ ul U ↔ v ∈ U := mem_clist mem_ord

theorem ul_mem (U : Finset (Fin N)) {l : ℕ} (hl : l < (ul U).length) : (ul U)[l] ∈ U :=
  (mem_ul U).1 (List.getElem_mem hl)

theorem exists_ul (U : Finset (Fin N)) {v : Fin N} (hv : v ∈ U) :
    ∃ l, ∃ hl : l < (ul U).length, (ul U)[l] = v := List.getElem_of_mem ((mem_ul U).2 hv)

theorem mem_take_ul (U : Finset (Fin N)) {i : ℕ} {v : Fin N} :
    v ∈ (ul U).take i ↔ ∃ l, ∃ hl : l < (ul U).length, l < i ∧ (ul U)[l] = v := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, by omega, by omega, rfl⟩
  · rintro ⟨l, hl, hli, rfl⟩
    exact ⟨l, by omega, rfl⟩

/-! ### Components -/

omit [DecidableRel G.Adj] in
theorem comp_symm {U : Finset (Fin N)} {x y : Fin N} (hx : x ∈ U) (hy : y ∈ comp G U x) :
    x ∈ comp G U y :=
  mem_comp.2 ⟨hx, rtg_symm (mem_comp.1 hy).2⟩

omit [DecidableRel G.Adj] in
theorem mem_comp_iff_eq {U : Finset (Fin N)} {x y : Fin N} :
    y ∈ comp G U x ↔ y ∈ U ∧ comp G U y = comp G U x := by
  constructor
  · intro h
    exact ⟨(mem_comp.1 h).1, comp_eq_comp h⟩
  · rintro ⟨hy, h⟩
    rw [← h]
    exact mem_comp_self hy

/-! ### The heavy component -/

theorem heavyC_eq (U : Finset (Fin N)) (w : Fin N → ℕ) :
    heavyC G (ord N) U w =
      (ul U).find? (fun v => decide (2 * ∑ u ∈ U, w u < 3 * ∑ u ∈ comp G U v, w u)) := by
  unfold heavyC
  rw [show ul U = (ord N).filter (· ∈ U) from clist_eq U, List.head?_filter, List.find?_filter]
  congr 1

/-! ### The prefixes of components -/

variable (G) in
/-- The union of the components of the first `i` vertices of `ul U`. -/
noncomputable def pU (U : Finset (Fin N)) (i : ℕ) : Finset (Fin N) :=
  ((ul U).take i).toFinset.biUnion (comp G U)

theorem pU_zero (U : Finset (Fin N)) : pU G U 0 = ∅ := by simp [pU]

theorem mem_pU {U : Finset (Fin N)} {i : ℕ} {x : Fin N} :
    x ∈ pU G U i ↔ ∃ l, ∃ hl : l < (ul U).length, l < i ∧ x ∈ comp G U (ul U)[l] := by
  simp only [pU, mem_biUnion, List.mem_toFinset, mem_take_ul]
  constructor
  · rintro ⟨_, ⟨l, hl, hli, rfl⟩, hx⟩
    exact ⟨l, hl, hli, hx⟩
  · rintro ⟨l, hl, hli, hx⟩
    exact ⟨_, ⟨l, hl, hli, rfl⟩, hx⟩

theorem pU_subset (U : Finset (Fin N)) (i : ℕ) : pU G U i ⊆ U := fun x hx => by
  obtain ⟨l, hl, -, hx⟩ := mem_pU.1 hx
  exact comp_subset _ _ hx

theorem pU_mono (U : Finset (Fin N)) {i j : ℕ} (h : i ≤ j) : pU G U i ⊆ pU G U j := fun x hx => by
  obtain ⟨l, hl, hli, hx⟩ := mem_pU.1 hx
  exact mem_pU.2 ⟨l, hl, by omega, hx⟩

theorem pU_succ (U : Finset (Fin N)) {i : ℕ} (hi : i < (ul U).length) :
    pU G U (i + 1) = pU G U i ∪ comp G U (ul U)[i] := by
  ext x
  simp only [mem_union, mem_pU]
  constructor
  · rintro ⟨l, hl, hli, hx⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hli with h | rfl
    · exact Or.inl ⟨l, hl, h, hx⟩
    · exact Or.inr hx
  · rintro (⟨l, hl, hli, hx⟩ | hx)
    · exact ⟨l, hl, by omega, hx⟩
    · exact ⟨i, hi, by omega, hx⟩

/-- A component meeting `pU U i` lies in it. -/
theorem comp_subset_pU {U : Finset (Fin N)} {i : ℕ} {x y : Fin N} (hy : y ∈ pU G U i)
    (hyx : y ∈ comp G U x) : comp G U x ⊆ pU G U i := fun z hz => by
  obtain ⟨l, hl, hli, hyl⟩ := mem_pU.1 hy
  refine mem_pU.2 ⟨l, hl, hli, ?_⟩
  rw [← comp_eq_comp hyl, comp_eq_comp hyx]
  exact hz

theorem mem_pU_iff_comp {U : Finset (Fin N)} {i : ℕ} {x : Fin N} (hx : x ∈ U) :
    x ∈ pU G U i ↔ ∃ y ∈ pU G U i, y ∈ comp G U x :=
  ⟨fun h => ⟨x, h, mem_comp_self hx⟩, fun ⟨_, hy, hyx⟩ => comp_subset_pU hy hyx (mem_comp_self hx)⟩

/-! ### The first part when no component is heavy -/

theorem mem_take_ord {k : ℕ} {v : Fin N} : v ∈ (ord N).take k ↔ (v : ℕ) < k := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.getElem_finRange, Fin.cast_mk]
    omega
  · intro h
    exact ⟨v, by simp; omega, by simp⟩

theorem mem_pre {U : Finset (Fin N)} {k : ℕ} {x : Fin N} :
    x ∈ pre G (ord N) U k ↔ ∃ v ∈ U, (v : ℕ) < k ∧ x ∈ comp G U v := by
  simp only [pre, mem_biUnion, mem_filter, List.mem_toFinset, mem_take_ord]
  constructor
  · rintro ⟨v, ⟨h1, h2⟩, h3⟩
    exact ⟨v, h2, h1, h3⟩
  · rintro ⟨v, h2, h1, h3⟩
    exact ⟨v, ⟨h1, h2⟩, h3⟩

theorem pre_eq_pU (U : Finset (Fin N)) {i : ℕ} (hi : i < (ul U).length) :
    pre G (ord N) U ((ul U)[i] + 1) = pU G U (i + 1) := by
  ext x
  rw [mem_pre, mem_pU]
  constructor
  · rintro ⟨v, hv, hlt, hx⟩
    obtain ⟨l, hl, rfl⟩ := exists_ul U hv
    have : (ul U)[l] ≤ (ul U)[i] := by rw [Fin.le_def]; omega
    exact ⟨l, hl, by have := (ul_le_iff U hl hi).1 this; omega, hx⟩
  · rintro ⟨l, hl, hli, hx⟩
    have : (ul U)[l] ≤ (ul U)[i] := (ul_le_iff U hl hi).2 (by omega)
    exact ⟨_, ul_mem U hl, by rw [Fin.le_def] at this; omega, hx⟩

theorem pre_subset_pU (U : Finset (Fin N)) {i k : ℕ} (hi : i < (ul U).length)
    (hk : k ≤ (ul U)[i]) : pre G (ord N) U k ⊆ pU G U i := fun x hx => by
  obtain ⟨v, hv, hlt, hx⟩ := mem_pre.1 hx
  obtain ⟨l, hl, rfl⟩ := exists_ul U hv
  have : (ul U)[l] < (ul U)[i] := by rw [Fin.lt_def]; omega
  exact mem_pU.2 ⟨l, hl, (ul_lt_iff U hl hi).1 this, hx⟩

theorem lightA_zero (U : Finset (Fin N)) (w : Fin N → ℕ) (hw : ∑ u ∈ U, w u = 0) :
    lightA G (ord N) U w = ∅ := by
  have hk : kstar G (ord N) U w = 0 := by
    unfold kstar
    rw [Nat.find_eq_zero]
    left
    rw [hw]
    exact Nat.zero_le _
  unfold lightA
  rw [hk]
  have h0 : pre G (ord N) U 0 = ∅ := by simp [pre]
  split
  · simp [h0]
  · exact h0

theorem lightA_eq (U : Finset (Fin N)) (w : Fin N → ℕ) {i : ℕ} (hi : i < (ul U).length)
    (hpos : 0 < ∑ u ∈ U, w u)
    (hcross : ∑ u ∈ U, w u ≤ 3 * ∑ u ∈ pU G U (i + 1), w u)
    (hmin : ∀ l < i, 3 * ∑ u ∈ pU G U (l + 1), w u < ∑ u ∈ U, w u) :
    lightA G (ord N) U w =
      if ∑ u ∈ U, w u ≤ 3 * ∑ u ∈ comp G U (ul U)[i], w u then comp G U (ul U)[i]
      else pU G U (i + 1) := by
  have hk : kstar G (ord N) U w = (ul U)[i] + 1 := by
    unfold kstar
    rw [Nat.find_eq_iff]
    refine ⟨Or.inl (by rw [pre_eq_pU (G := G) U hi]; exact hcross), fun k hk => ?_⟩
    rintro (h | h)
    · have hsub := pre_subset_pU (G := G) U hi (k := k) (by omega)
      have hle : ∑ u ∈ pre G (ord N) U k, w u ≤ ∑ u ∈ pU G U i, w u :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [pU_zero, sum_empty] at hle
        omega
      · have := hmin (i - 1) (by omega)
        rw [show i - 1 + 1 = i by omega] at this
        omega
    · have : ((ul U)[i] : ℕ) < N := (ul U)[i].2
      simp only [List.length_finRange] at h
      omega
  unfold lightA
  rw [hk, Nat.add_sub_cancel]
  have hget : (ord N)[((ul U)[i] : ℕ)]? = some (ul U)[i] := by
    simp
  rw [hget]
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, true_and,
    ul_mem U hi, pre_eq_pU U hi]

/-! ### Sums over enumerations -/

omit [DecidableRel G.Adj] in
/-- A sum over an injective enumeration `Q 0, …, Q (t - 1)` of a vertex set `S`. -/
theorem sum_range_eq {t : ℕ} (Q : ℕ → ℕ) (S : Finset (Fin N)) (hQ : ∀ j < t, Q j < N)
    (hin : ∀ j (hj : j < t), (⟨Q j, hQ j hj⟩ : Fin N) ∈ S)
    (hinj : ∀ i < t, ∀ j < t, Q i = Q j → i = j)
    (hsurj : ∀ x ∈ S, ∃ j < t, Q j = x) (f : ℕ → ℕ) :
    ∑ j ∈ range t, f (Q j) = ∑ x ∈ S, f x := by
  rw [← sum_image (fun i hi j hj h => hinj i (mem_range.1 hi) j (mem_range.1 hj) h)]
  have himg : (range t).image Q = S.map Fin.valEmbedding := by
    ext a
    simp only [mem_image, mem_range, mem_map, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨_, hin j hj, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hsurj x hx
  rw [himg, sum_map]
  rfl

end Piece

end PlanarSeparator
