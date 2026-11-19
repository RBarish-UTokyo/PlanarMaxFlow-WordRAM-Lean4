module

public import PlanarFlow.BKMNW.Cost

/-!
# The mathematics of the hole flags of `c2sP`: a bottom-up merge sort and a distinct-value scan

The hole `i < #pholes` of a piece map is the image of the `i`-th hole `Hs[J]` with a vertex in
the piece; its darts are those of hole label `J + 1`, the `i`-th smallest distinct positive
label of the frame (`HL`). The labels are at most `#Hs`, which the size of the piece does not
bound, so the program sorts the `m` labels (`O(m lg m)`, a bottom-up merge sort) and scans the
sorted array for the distinct positive values.

* **`mpass w L`**: one pass of the merge sort with blocks of width `w` (`List.merge` of the
  blocks `2k`, `2k + 1`); `mpass_blk`, `perm_mpass`, `length_mpass`;
  `BSorted w L` (every block of width `w` sorted), **`bsorted_mpass`**
  (`BSorted w L → BSorted (2w) (mpass w L)`);
* **`msortW m w L`**: the passes `w, 2w, 4w, …` while `w < m`; **`msortW_sorted`**,
  `perm_msortW`; `npass m w` (the number of passes), **`npass_one_le`** (`npass m 1 ≤ lg m`);
* the scan **`dscan i`** (`prev`, `cnt`, `v`: on a new value `x > prev`, `v := x` if `cnt = i`,
  `cnt := cnt + 1`); **`dscan_sorted`**: on a sorted list from `(0, 0, 0)`, the final `v` is
  the element of the set of the positive values with exactly `i` smaller ones, when there are
  more than `i` of them (**`dscan_spec`**, through a permutation).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open List

/-! ### One pass -/

/-- **One pass of the bottom-up merge sort** with blocks of width `w`. -/
def mpass (w : ℕ) (L : List ℕ) : List ℕ :=
  if h : L.length ≤ w ∨ w = 0 then L
  else merge (L.take w) ((L.drop w).take w) ++ mpass w (L.drop (2 * w))
termination_by L.length
decreasing_by simp only [List.length_drop]; omega

lemma mpass_nil (w : ℕ) : mpass w [] = [] := by
  rw [mpass]; simp

lemma mpass_short {w : ℕ} {L : List ℕ} (h : L.length ≤ w) : mpass w L = L := by
  rw [mpass]; simp [h]

/-- **The pass block by block.** -/
lemma mpass_blk {w : ℕ} (hw : 0 < w) {X : List ℕ} (hX : X ≠ []) :
    mpass w X = merge (X.take w) ((X.drop w).take w) ++ mpass w (X.drop (2 * w)) := by
  by_cases h : X.length ≤ w
  · rw [mpass_short h, List.take_of_length_le h, List.drop_eq_nil_of_le h,
      List.drop_eq_nil_of_le (by omega : X.length ≤ 2 * w)]
    simp [mpass_nil]
  · rw [mpass]; simp only [h, show w ≠ 0 by omega, or_self, ↓reduceDIte]

lemma perm_mpass_aux {w : ℕ} : ∀ (n : ℕ) (L : List ℕ), L.length ≤ n → mpass w L ~ L
  | 0, L, hn => by
    obtain rfl : L = [] := List.length_eq_zero_iff.1 (by omega)
    rw [mpass_nil]
  | n + 1, L, hn => by
    by_cases h : L.length ≤ w ∨ w = 0
    · rw [mpass]; simp only [h, ↓reduceDIte]; exact Perm.refl _
    · rw [mpass]
      simp only [h, ↓reduceDIte]
      have ih := perm_mpass_aux (w := w) n (L.drop (2 * w))
        (by simp only [List.length_drop]; omega)
      have e : L = L.take w ++ ((L.drop w).take w ++ L.drop (2 * w)) := by
        conv_lhs => rw [← List.take_append_drop w L]
        congr 1
        conv_lhs => rw [← List.take_append_drop w (L.drop w)]
        rw [List.drop_drop]; congr 2; omega
      calc merge (L.take w) ((L.drop w).take w) ++ mpass w (L.drop (2 * w))
          ~ (L.take w ++ (L.drop w).take w) ++ L.drop (2 * w) :=
            (merge_perm_append _).append ih
        _ = L := by rw [List.append_assoc]; exact e.symm

lemma perm_mpass {w : ℕ} (L : List ℕ) : mpass w L ~ L := perm_mpass_aux L.length L le_rfl

lemma length_mpass (w : ℕ) (L : List ℕ) : (mpass w L).length = L.length :=
  (perm_mpass L).length_eq

/-- Every block of width `w` is sorted. -/
def BSorted (w : ℕ) (L : List ℕ) : Prop :=
  ∀ k, ((L.drop (w * k)).take w).Pairwise (· ≤ ·)

lemma bsorted_one (L : List ℕ) : BSorted 1 L := fun k => by
  generalize L.drop (1 * k) = X
  rcases X with _ | ⟨a, t⟩ <;> simp

lemma BSorted.drop {w : ℕ} {L : List ℕ} (h : BSorted w L) (j : ℕ) : BSorted w (L.drop (w * j)) :=
  fun k => by rw [List.drop_drop, ← Nat.mul_add, Nat.add_comm]; exact h (k + j)

lemma pairwise_merge_le {l₁ l₂ : List ℕ} (h₁ : l₁.Pairwise (· ≤ ·)) (h₂ : l₂.Pairwise (· ≤ ·)) :
    (merge l₁ l₂).Pairwise (· ≤ ·) := by
  have := pairwise_merge (le := fun a b : ℕ => decide (a ≤ b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l₁ l₂
    (by simpa using h₁) (by simpa using h₂)
  simpa using this

lemma length_merge_take {w : ℕ} (X : List ℕ) :
    (merge (X.take w) ((X.drop w).take w)).length = min (2 * w) X.length := by
  simp only [length_merge, List.length_take, List.length_drop]; omega

/-- **One pass doubles the width of the sorted blocks.** -/
theorem bsorted_mpass_aux {w : ℕ} (hw : 0 < w) : ∀ (n : ℕ) (L : List ℕ), L.length ≤ n →
    BSorted w L → BSorted (2 * w) (mpass w L)
  | 0, L, hn, h => by
    obtain rfl : L = [] := List.length_eq_zero_iff.1 (by omega)
    intro k; simp [mpass_nil]
  | n + 1, L, hn, h => by
    rcases eq_or_ne L [] with rfl | hL
    · intro k; simp [mpass_nil]
    rw [mpass_blk hw hL]
    set A := merge (L.take w) ((L.drop w).take w) with hA
    have hAl : A.length = min (2 * w) L.length := length_merge_take L
    have hsA : A.Pairwise (· ≤ ·) := by
      have h0 := h 0
      have h1 := h 1
      simp only [Nat.mul_zero, List.drop_zero, Nat.mul_one] at h0 h1
      exact pairwise_merge_le h0 h1
    have hLp : 0 < L.length := List.length_pos_iff.2 hL
    have ih := bsorted_mpass_aux hw n (L.drop (2 * w)) (by simp only [List.length_drop]; omega)
      (by have := h.drop 2; rwa [Nat.mul_comm] at this)
    intro k
    by_cases hl : A.length = 2 * w
    · rcases k with _ | k
      · simp only [Nat.mul_zero, List.drop_zero]
        rw [List.take_append_of_le_length (by omega), ← hl, List.take_length]; exact hsA
      · rw [show 2 * w * (k + 1) = A.length + 2 * w * k by rw [hl]; ring,
          ← List.drop_drop, List.drop_left]
        exact ih k
    · have e : L.drop (2 * w) = [] := List.drop_eq_nil_of_le (by omega)
      rw [e, mpass_nil, List.append_nil]
      rcases k with _ | k
      · simp only [Nat.mul_zero, List.drop_zero]
        rw [List.take_of_length_le (by omega)]; exact hsA
      · have : 2 * w ≤ 2 * w * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
        rw [List.drop_eq_nil_of_le (by omega)]
        simp

theorem bsorted_mpass {w : ℕ} (hw : 0 < w) (L : List ℕ) (h : BSorted w L) :
    BSorted (2 * w) (mpass w L) := bsorted_mpass_aux hw L.length L le_rfl h

lemma BSorted.pairwise {w : ℕ} {L : List ℕ} (h : BSorted w L) (hl : L.length ≤ w) :
    L.Pairwise (· ≤ ·) := by
  have := h 0
  simp only [Nat.mul_zero, List.drop_zero] at this
  rwa [List.take_of_length_le hl] at this

/-! ### The passes -/

/-- **The passes of the merge sort** of widths `w, 2w, 4w, …` while `w < m`. -/
def msortW (m w : ℕ) (L : List ℕ) : List ℕ :=
  if h : m ≤ w ∨ w = 0 then L else msortW m (2 * w) (mpass w L)
termination_by m - w

/-- The number of passes. -/
def npass (m w : ℕ) : ℕ :=
  if h : m ≤ w ∨ w = 0 then 0 else npass m (2 * w) + 1
termination_by m - w

lemma msortW_stop {m w : ℕ} {L : List ℕ} (h : m ≤ w ∨ w = 0) : msortW m w L = L := by
  rw [msortW]; simp [h]

lemma msortW_step {m w : ℕ} {L : List ℕ} (h : ¬ (m ≤ w ∨ w = 0)) :
    msortW m w L = msortW m (2 * w) (mpass w L) := by
  rw [msortW]; simp [h]

lemma npass_stop {m w : ℕ} (h : m ≤ w ∨ w = 0) : npass m w = 0 := by
  rw [npass]; simp [h]

lemma npass_step {m w : ℕ} (h : ¬ (m ≤ w ∨ w = 0)) : npass m w = npass m (2 * w) + 1 := by
  rw [npass]; simp [h]

lemma perm_msortW (m : ℕ) : ∀ (w : ℕ) (L : List ℕ), msortW m w L ~ L
  | w, L => by
    by_cases h : m ≤ w ∨ w = 0
    · rw [msortW_stop h]
    · rw [msortW_step h]
      exact (perm_msortW m (2 * w) (mpass w L)).trans (perm_mpass L)
termination_by w => m - w
decreasing_by omega

/-- **The passes sort.** -/
theorem msortW_sorted (m : ℕ) : ∀ (w : ℕ) (L : List ℕ), 0 < w → L.length = m → BSorted w L →
    (msortW m w L).Pairwise (· ≤ ·)
  | w, L, hw, hl, h => by
    by_cases hs : m ≤ w ∨ w = 0
    · rw [msortW_stop hs]; exact h.pairwise (by omega)
    · rw [msortW_step hs]
      exact msortW_sorted m (2 * w) (mpass w L) (by omega) (by rw [length_mpass, hl])
        (bsorted_mpass hw L h)
termination_by w => m - w
decreasing_by omega

lemma npass_bound (m : ℕ) : ∀ w, 0 < w → npass m w = 0 ∨ w * 2 ^ npass m w < 2 * m
  | w, hw => by
    by_cases hs : m ≤ w ∨ w = 0
    · exact Or.inl (npass_stop hs)
    · right
      rw [npass_step hs]
      rcases npass_bound m (2 * w) (by omega) with h | h
      · rw [h]; simp; omega
      · rw [pow_succ]; nlinarith
termination_by w => m - w
decreasing_by omega

/-- **At most `lg m` passes** from the width `1`. -/
theorem npass_one_le (m : ℕ) : npass m 1 ≤ lg m := by
  rcases npass_bound m 1 one_pos with h | h
  · rw [h]; exact Nat.zero_le _
  · rw [one_mul] at h
    unfold lg
    rcases Nat.eq_zero_or_pos (npass m 1) with h0 | h0
    · omega
    · have h2 : 2 ^ (npass m 1 - 1) ≤ m := by
        have : 2 ^ npass m 1 = 2 * 2 ^ (npass m 1 - 1) := by
          rw [← pow_succ']; congr 1; omega
        omega
      have := Nat.le_log_of_pow_le (by norm_num) h2
      omega

/-! ### The scan of the distinct positive values -/

/-- One step of the scan: state `(prev, cnt, v)`. -/
def dstep (i : ℕ) (s : ℕ × ℕ × ℕ) (x : ℕ) : ℕ × ℕ × ℕ :=
  if s.1 < x then (x, s.2.1 + 1, if s.2.1 = i then x else s.2.2) else s

/-- **The scan** of a list. -/
def dscan (i : ℕ) (L : List ℕ) : ℕ × ℕ × ℕ := L.foldl (dstep i) (0, 0, 0)

/-- The set of the positive values of a list. -/
def posVals (L : List ℕ) : Finset ℕ := (L.filter (fun x => 0 < x)).toFinset

lemma mem_posVals {L : List ℕ} {x : ℕ} : x ∈ posVals L ↔ x ∈ L ∧ 0 < x := by
  simp [posVals]

lemma posVals_append (L : List ℕ) (x : ℕ) (hx : 0 < x) :
    posVals (L ++ [x]) = insert x (posVals L) := by
  ext y; simp only [mem_posVals, List.mem_append, List.mem_singleton, Finset.mem_insert]
  constructor
  · rintro ⟨h | rfl, hy⟩
    · exact Or.inr ⟨h, hy⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨h, hy⟩)
    · exact ⟨Or.inr rfl, hx⟩
    · exact ⟨Or.inl h, hy⟩

/-- The invariant of the scan on the prefix `L` of a sorted list. -/
def DInv (i : ℕ) (L : List ℕ) (s : ℕ × ℕ × ℕ) : Prop :=
  (∀ y ∈ L, y ≤ s.1) ∧ (s.1 = 0 ∨ s.1 ∈ L) ∧ s.2.1 = (posVals L).card ∧
    (i < s.2.1 → s.2.2 ∈ posVals L ∧ ((posVals L).filter (· < s.2.2)).card = i)

lemma dinv_nil (i : ℕ) : DInv i [] (0, 0, 0) := by
  refine ⟨fun y hy => by simp at hy, Or.inl rfl, by simp [posVals], fun h => by simp at h⟩

lemma dinv_step {i : ℕ} {L : List ℕ} {s : ℕ × ℕ × ℕ} {x : ℕ} (h : DInv i L s)
    (hx : ∀ y ∈ L, y ≤ x) : DInv i (L ++ [x]) (dstep i s x) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold dstep
  by_cases hlt : s.1 < x
  · simp only [hlt, ↓reduceIte, DInv]
    have hx0 : 0 < x := by omega
    have hnew : x ∉ posVals L := fun hm => by
      have := h1 x (mem_posVals.1 hm).1; omega
    rw [posVals_append L x hx0]
    refine ⟨fun y hy => ?_, Or.inr (by simp), ?_, fun hi => ?_⟩
    · rcases List.mem_append.1 hy with hy | hy
      · exact hx y hy
      · simp at hy; omega
    · rw [Finset.card_insert_of_notMem hnew, h3]
    · have hall : ∀ y ∈ posVals L, y < x := fun y hy => by
        have := h1 y (mem_posVals.1 hy).1; omega
      by_cases he : s.2.1 = i
      · simp only [he, ↓reduceIte, Finset.mem_insert, true_or, true_and]
        rw [Finset.filter_insert]
        simp only [lt_irrefl, ↓reduceIte]
        rw [Finset.filter_true_of_mem hall, ← h3, he]
      · simp only [he, ↓reduceIte]
        obtain ⟨hv, hc⟩ := h4 (by omega)
        refine ⟨Finset.mem_insert_of_mem hv, ?_⟩
        rw [Finset.filter_insert]
        have : ¬ x < s.2.2 := by have := hall _ hv; omega
        simp only [this, ↓reduceIte, hc]
  · simp only [hlt, ↓reduceIte, DInv]
    have hxe : x = s.1 := by
      rcases h2 with h2 | h2
      · omega
      · have := hx _ h2; omega
    have hpv : posVals (L ++ [x]) = posVals L := by
      ext y; simp only [mem_posVals, List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨h | rfl, hy⟩
        · exact ⟨h, hy⟩
        · rcases h2 with h2 | h2
          · omega
          · rw [hxe]; exact ⟨h2, by omega⟩
      · rintro ⟨h, hy⟩; exact ⟨Or.inl h, hy⟩
    rw [hpv]
    refine ⟨fun y hy => ?_, Or.inr ?_, h3, h4⟩
    · rcases List.mem_append.1 hy with hy | hy
      · exact h1 y hy
      · simp at hy; omega
    · rw [← hxe]; simp

lemma dinv_foldl {i : ℕ} : ∀ (R L : List ℕ) (s : ℕ × ℕ × ℕ), DInv i L s →
    (L ++ R).Pairwise (· ≤ ·) → DInv i (L ++ R) (R.foldl (dstep i) s)
  | [], L, s, h, _ => by simpa using h
  | x :: R, L, s, h, hp => by
    simp only [List.foldl_cons]
    have hx : ∀ y ∈ L, y ≤ x := fun y hy =>
      (List.pairwise_append.1 hp).2.2 y hy x (by simp)
    have := dinv_foldl R (L ++ [x]) (dstep i s x) (dinv_step h hx) (by simpa using hp)
    simpa using this

/-- **The scan of a sorted list.** -/
theorem dscan_sorted {i : ℕ} {L : List ℕ} (hL : L.Pairwise (· ≤ ·))
    (hi : i < (posVals L).card) :
    (dscan i L).2.2 ∈ posVals L ∧ ((posVals L).filter (· < (dscan i L).2.2)).card = i := by
  have := dinv_foldl L [] (0, 0, 0) (dinv_nil i) (by simpa using hL)
  simp only [List.nil_append] at this
  obtain ⟨-, -, h3, h4⟩ := this
  exact h4 (by rw [h3]; exact hi)

lemma posVals_perm {L L' : List ℕ} (h : L ~ L') : posVals L = posVals L' := by
  ext x; simp only [mem_posVals, h.mem_iff]

/-- **The scan after the sort** (through a permutation). -/
theorem dscan_spec {i m : ℕ} {L : List ℕ} (hl : L.length = m)
    (hi : i < (posVals L).card) :
    (dscan i (msortW m 1 L)).2.2 ∈ posVals L ∧
      ((posVals L).filter (· < (dscan i (msortW m 1 L)).2.2)).card = i := by
  have hp := perm_msortW m 1 L
  rw [← posVals_perm hp] at hi ⊢
  exact dscan_sorted (msortW_sorted m 1 L one_pos hl (bsorted_one L)) hi

end NcStep

end BKMNW

end PlanarFlow
