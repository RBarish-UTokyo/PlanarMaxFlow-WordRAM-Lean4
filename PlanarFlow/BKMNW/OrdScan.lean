module

public import PlanarFlow.BKMNW.ChoiceE
public import PlanarFlow.BKMNW.IteR23

/-!
# The listing `ordE` of a disjoint family is the order of a scan

`pcChoiceE` lists a set of sets by `ordE e n` (sorted by the codes `Σ 2^i` of the indices). A
program lists a family of sets by one scan of the indices, emitting each set at its largest
index. Here the two orders are shown equal:

* `sum_two_pow_lt` (`Σ_{i ∈ A} 2^i < 2^(m+1)` for `A ⊆ [0, m]`), `codeE_lt` (a set whose indices
  are `≤ m` has a smaller code than a set with an index `> m`);
* **`ordE_eq`**: a nodup list `L` with `L.toFinset = X` and strictly increasing codes is
  `ordE e n X`; **`ordE_eq_of_max`**: the same with strictly increasing largest indices;
* **`ordE_pairs`**: for a set `F` of darts closed under an involution `r` without fixed points
  (indices `rv`), the pairs `{d, r d}` are listed by `ordE` as the scan "`i` with `e i ∈ F` and
  `rv i < i`, emit `{e (rv i), e i}`" (the order of `pcEs` in `pcLs`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset

variable {D : Type*} [DecidableEq D] {e : ℕ → D} {n : ℕ}

lemma sum_two_pow_range (m : ℕ) : ∑ i ∈ range m, 2 ^ i + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, pow_succ]; omega

lemma sum_two_pow_lt {A : Finset ℕ} {m : ℕ} (h : ∀ i ∈ A, i ≤ m) : ∑ i ∈ A, 2 ^ i < 2 ^ (m + 1) := by
  have hs : A ⊆ range (m + 1) := fun i hi => mem_range.2 (Nat.lt_succ_of_le (h i hi))
  have := sum_le_sum_of_subset_of_nonneg (f := fun i => 2 ^ i) hs (fun _ _ _ => Nat.zero_le _)
  have := sum_two_pow_range (m + 1)
  omega

/-- A set with indices `≤ m` has a smaller code than a set with an index `> m`. -/
lemma codeE_lt {E E' : Finset D} {m : ℕ} (hE : ∀ i ∈ idxE e n E, i ≤ m)
    (hE' : ∃ i ∈ idxE e n E', m < i) : codeE e n E < codeE e n E' := by
  obtain ⟨i, hi, hmi⟩ := hE'
  have h1 := sum_two_pow_lt hE
  have h2 : 2 ^ (m + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hmi
  have h3 : 2 ^ i ≤ ∑ i ∈ idxE e n E', 2 ^ i :=
    single_le_sum (f := fun i => 2 ^ i) (fun _ _ => Nat.zero_le _) hi
  unfold codeE
  omega

/-- **A list with strictly increasing codes is the listing `ordE`.** -/
theorem ordE_eq (hsurj : ∀ d, ∃ i < n, e i = d) {X : Finset (Finset D)} {L : List (Finset D)}
    (hX : L.toFinset = X) (hcode : L.Pairwise fun E E' => codeE e n E < codeE e n E') :
    ordE e n X = L := by
  have hmap : (X.image (codeE e n)).sort (· ≤ ·) = L.map (codeE e n) := by
    refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (pairwise_sort _ _) ?_ ?_
    · rw [List.pairwise_map]; exact hcode.imp le_of_lt
    · refine List.perm_of_nodup_nodup_toFinset_eq (sort_nodup _ _) ?_ ?_
      · rw [List.nodup_iff_pairwise_ne, List.pairwise_map]; exact hcode.imp ne_of_lt
      · rw [sort_toFinset, ← hX]
        ext x; simp
  unfold ordE
  rw [hmap, List.map_map]
  conv_rhs => rw [← List.map_id L]
  exact List.map_congr_left fun E _ => decodeE_codeE hsurj E

/-- **A list with strictly increasing largest indices is the listing `ordE`.** -/
theorem ordE_eq_of_max (hsurj : ∀ d, ∃ i < n, e i = d) {X : Finset (Finset D)}
    {L : List (Finset D)} (mx : Finset D → ℕ)
    (hmx : ∀ E ∈ L, mx E ∈ idxE e n E ∧ ∀ i ∈ idxE e n E, i ≤ mx E)
    (hX : L.toFinset = X) (hinc : L.Pairwise fun E E' => mx E < mx E') :
    ordE e n X = L := by
  refine ordE_eq hsurj hX ?_
  have := List.Pairwise.and_mem.1 hinc
  refine (List.Pairwise.and_mem.1 hinc).imp fun {E E'} ⟨hE, hE', h⟩ => ?_
  exact codeE_lt (hmx E hE).2 ⟨mx E', (hmx E' hE').1, h⟩

/-- The scan of the pairs: the indices `i` with `e i ∈ F` and `rv i < i`, emitting
`{e (rv i), e i}`. -/
def pairScan (e : ℕ → D) (n : ℕ) (rv : ℕ → ℕ) (F : Finset D) : List (Finset D) :=
  ((List.range n).filter fun i => decide (e i ∈ F ∧ rv i < i)).map fun i => {e (rv i), e i}

/-- **The pairs of a set closed under an involution are listed by `ordE` in scan order.** With
`e` bijective from `[0, n)`, `r` an involution without fixed points on `F` (`r` maps `F` into
`F`) and `rv i < n` the index of `r (e i)`: `ordE e n (F.image fun d => {r d, d}) =
pairScan e n rv F`. -/
theorem ordE_pairs (hsurj : ∀ d, ∃ i < n, e i = d) (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    {r : D → D} (hr : ∀ d, r (r d) = d) (hr1 : ∀ d, r d ≠ d) {F : Finset D}
    (hF : ∀ d ∈ F, r d ∈ F) {rv : ℕ → ℕ} (hrv : ∀ i < n, rv i < n ∧ e (rv i) = r (e i)) :
    ordE e n (F.image fun d => ({r d, d} : Finset D)) = pairScan e n rv F := by
  -- the indices of a pair
  have hidx : ∀ i < n, idxE e n ({e (rv i), e i} : Finset D) = {rv i, i} := by
    intro i hi
    ext j
    simp only [idxE, mem_filter, mem_range, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hj, h | h⟩
      · exact Or.inl (hinj j hj (rv i) (hrv i hi).1 h)
      · exact Or.inr (hinj j hj i hi h)
    · rintro (rfl | rfl)
      · exact ⟨(hrv i hi).1, Or.inl rfl⟩
      · exact ⟨hi, Or.inr rfl⟩
  refine ordE_eq_of_max hsurj (fun E => (idxE e n E).sup id) ?_ ?_ ?_
  · intro E hE
    simp only [pairScan, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hE
    obtain ⟨i, ⟨hi, -, hlt⟩, rfl⟩ := hE
    rw [hidx i hi]
    have hs : ({rv i, i} : Finset ℕ).sup id = i := by
      rw [sup_insert, sup_singleton]; simp only [id]; omega
    rw [hs]
    refine ⟨by simp, fun j hj => ?_⟩
    simp only [mem_insert, mem_singleton] at hj
    omega
  · ext E
    simp only [pairScan, List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq, mem_image]
    constructor
    · rintro ⟨i, ⟨hi, hF', hlt⟩, rfl⟩
      refine ⟨e (rv i), ?_, ?_⟩
      · rw [(hrv i hi).2]; exact hF _ hF'
      · rw [(hrv i hi).2, hr, pair_comm]
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨i, hi, rfl⟩ := hsurj d
      obtain ⟨hrvi, hrve⟩ := hrv i hi
      have hne : rv i ≠ i := fun h => hr1 (e i) (by rw [← hrve, h])
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · refine ⟨i, ⟨hi, hd, hlt⟩, ?_⟩
        rw [hrve]
      · obtain ⟨hrr, hrre⟩ := hrv (rv i) hrvi
        have hback : rv (rv i) = i := hinj _ hrr _ hi (by rw [hrre, hrve, hr])
        refine ⟨rv i, ⟨hrvi, by rw [hrve]; exact hF _ hd, by omega⟩, ?_⟩
        rw [hback, hrve, pair_comm]
  · unfold pairScan
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ ((List.pairwise_lt_range (n := n)).filter _)
    intro i j hi hj hij
    rw [List.mem_filter, List.mem_range] at hi hj
    rw [hidx i hi.1, hidx j hj.1]
    simp only [decide_eq_true_eq] at hi hj
    have hs : ∀ k, rv k < k → ({rv k, k} : Finset ℕ).sup id = k := fun k hk => by
      rw [sup_insert, sup_singleton]; simp only [id]; omega
    rw [hs i hi.2.2, hs j hj.2.2]
    exact hij

section Pc

variable {V F : Type*} [Fintype D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  {M : CombMap D V F}

/-- **The attached pairs `pcEs` in the order of `pcChoiceE` are the scan of the pairs**: with
`F = pcNf \ pdarts (core)` closed under `rev` and `rv i` the index of `rev (e i)`. -/
theorem ordE_pcEs (hsurj : ∀ d, ∃ i < n, e i = d) (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    {Q : Finset V} {P : Finset D} {Hs : List (Finset V)}
    (hF : ∀ d ∈ pcNf M Q P Hs \ pdarts M (core M Q P) Hs,
      M.rev d ∈ pcNf M Q P Hs \ pdarts M (core M Q P) Hs)
    {rv : ℕ → ℕ} (hrv : ∀ i < n, rv i < n ∧ e (rv i) = M.rev (e i)) :
    ordE e n (pcEs M Q P Hs) = pairScan e n rv (pcNf M Q P Hs \ pdarts M (core M Q P) Hs) := by
  have h : pcEs M Q P Hs = (pcNf M Q P Hs \ pdarts M (core M Q P) Hs).image
      fun d => ({M.rev d, d} : Finset D) := by
    unfold pcEs
    exact image_congr fun d _ => pair_comm _ _
  rw [h]
  exact ordE_pairs hsurj hinj M.rev_rev M.rev_ne hF hrv

/-- **The attached sets of `pcertD` with the choices `pcChoiceE`, in scan order.** -/
theorem pcLs_pcChoiceE (hsurj : ∀ d, ∃ i < n, e i = d)
    (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) (d₀ : D)
    {Q : Finset V} {P : Finset D} {Hs : List (Finset V)}
    (hF : ∀ d ∈ pcNf M Q P Hs \ pdarts M (core M Q P) Hs,
      M.rev d ∈ pcNf M Q P Hs \ pdarts M (core M Q P) Hs)
    {rv : ℕ → ℕ} (hrv : ∀ i < n, rv i < n ∧ e (rv i) = M.rev (e i)) :
    pcLs M (pcChoiceE M Q e n d₀) Q P Hs =
      (pairScan e n rv (pcNf M Q P Hs \ pdarts M (core M Q P) Hs)).map fun E =>
        (E, cls Hs (avQ M Q ((pcChoiceE M Q e n d₀).rep E)),
          (pcChoiceE M Q e n d₀).ancD P Hs ((pcChoiceE M Q e n d₀).rep E)) := by
  unfold pcLs
  rw [show (pcChoiceE M Q e n d₀).ord = ordE e n from rfl, ordE_pcEs hsurj hinj hF hrv]

end Pc

end BKMNW

end PlanarFlow
