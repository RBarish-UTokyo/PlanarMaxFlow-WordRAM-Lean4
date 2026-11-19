module

public import PlanarSeparator.Machine.DivProg

/-!
# The balanced split on the machine

**`PlanarSeparator.Piece.bsProg`** computes the balanced split `bsplit x y p q l` of
`PlanarSeparator/SepTreeExplicit.lean` for a list `l` of numbers below `N` stored in memory, the
measures `x`, `y` given as arrays: the members of the result are flagged `1` in a flag array.

* `mwalk`: the walk `bwalk` on positions in the two lists (`bwalk_eq_mwalk`);
* `gpre_drop`: the prefix `gpre` read along the list.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The walk on positions -/

/-- The walk on positions: `i` in the first list `F`, `j` in the second list `D`; `sx`, `sy` the
measures of the current family `F.drop i ++ (D.take j).reverse`. Returns the final positions. -/
def mwalk (x y : ℕ → ℕ) (X p q : ℕ) (F D : List ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, i, j, _, _ => (i, j)
  | k + 1, i, j, sx, sy =>
    if j < D.length ∧ 2 * sx < X then
      mwalk x y X p q F D k i (j + 1) (sx + x (D.getD j 0)) (sy + y (D.getD j 0))
    else if i < F.length then
      if p * (sy - y (F.getD i 0)) ≤ q then (i + 1, j)
      else mwalk x y X p q F D k (i + 1) j (sx - x (F.getD i 0)) (sy - y (F.getD i 0))
    else (i, j)

theorem bwalk_eq_mwalk (x y : ℕ → ℕ) (X p q : ℕ) (F D : List ℕ) :
    ∀ (k i j sx sy : ℕ), i ≤ F.length → j ≤ D.length → (F.length - i) + (D.length - j) ≤ k →
      sx = lsum x (F.drop i ++ (D.take j).reverse) →
      sy = lsum y (F.drop i ++ (D.take j).reverse) →
      bwalk x y X p q k (F.drop i) (D.drop j) (D.take j).reverse =
        F.drop (mwalk x y X p q F D k i j sx sy).1 ++
          (D.take (mwalk x y X p q F D k i j sx sy).2).reverse := by
  intro k
  induction k with
  | zero =>
    intro i j sx sy hi hj hk _ _
    obtain rfl : i = F.length := by omega
    obtain rfl : j = D.length := by omega
    simp [bwalk, mwalk]
  | succ k ih =>
  intro i j sx sy hi hj hk hsx hsy
  have hstepD : ∀ (hjD : j < D.length), 2 * sx < X →
      bwalk x y X p q k (F.drop i) (D.drop (j + 1)) (D[j] :: (D.take j).reverse) =
        F.drop (mwalk x y X p q F D k i (j + 1) (sx + x (D.getD j 0)) (sy + y (D.getD j 0))).1 ++
          (D.take (mwalk x y X p q F D k i (j + 1) (sx + x (D.getD j 0))
            (sy + y (D.getD j 0))).2).reverse := fun hjD _ => by
    have hgj : D.getD j 0 = D[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjD]; rfl
    have e : D[j] :: (D.take j).reverse = (D.take (j + 1)).reverse := by
      rw [List.take_succ_eq_append_getElem hjD, List.reverse_append]; rfl
    rw [e, hgj]
    refine ih i (j + 1) _ _ hi (by omega) (by omega) ?_ ?_
    · rw [hsx, List.take_succ_eq_append_getElem hjD]
      simp only [lsum_append, lsum_reverse, lsum_cons, lsum_nil]; ring
    · rw [hsy, List.take_succ_eq_append_getElem hjD]
      simp only [lsum_append, lsum_reverse, lsum_cons, lsum_nil]; ring
  have hstepF : ∀ (hiF : i < F.length) (a : List ℕ), a = D.drop j →
      bwalk x y X p q k (F.drop (i + 1)) a (D.take j).reverse =
        F.drop (mwalk x y X p q F D k (i + 1) j (sx - x (F.getD i 0)) (sy - y (F.getD i 0))).1 ++
          (D.take (mwalk x y X p q F D k (i + 1) j (sx - x (F.getD i 0))
            (sy - y (F.getD i 0))).2).reverse := fun hiF a ha => by
    have hgi : F.getD i 0 = F[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiF]; rfl
    rw [ha, hgi]
    refine ih (i + 1) j _ _ (by omega) hj (by omega) ?_ ?_
    · rw [hsx, List.drop_eq_getElem_cons hiF, List.cons_append, lsum_cons]; omega
    · rw [hsy, List.drop_eq_getElem_cons hiF, List.cons_append, lsum_cons]; omega
  have hsy' : ∀ (hiF : i < F.length), sy - y (F.getD i 0) =
      lsum y (F.drop (i + 1) ++ (D.take j).reverse) := fun hiF => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiF, Option.getD_some, hsy,
      List.drop_eq_getElem_cons hiF, List.cons_append, lsum_cons]; omega
  by_cases hjD : j < D.length <;> by_cases hiF : i < F.length
  · conv_lhs => rw [List.drop_eq_getElem_cons hjD, List.drop_eq_getElem_cons hiF]
    simp only [bwalk]
    rw [← List.drop_eq_getElem_cons hiF, ← hsx]
    by_cases hX : 2 * sx < X
    · rw [iteT hX]
      simp only [mwalk, hjD, hX, and_self, ite_true]
      exact hstepD hjD hX
    · rw [iteF hX, ← hsy' hiF]
      simp only [mwalk, hjD, hX, and_false, ite_false, hiF, ite_true]
      split_ifs
      · rfl
      · exact hstepF hiF _ (List.drop_eq_getElem_cons hjD).symm
  · conv_lhs => rw [List.drop_eq_getElem_cons hjD, List.drop_of_length_le (show F.length ≤ i by
      omega)]
    simp only [bwalk, List.nil_append]
    have e0 : F.drop i = [] := List.drop_of_length_le (by omega)
    by_cases hX : 2 * sx < X
    · rw [show lsum x (D.take j).reverse = sx by rw [hsx, e0, List.nil_append], iteT hX]
      simp only [mwalk, hjD, hX, and_self, ite_true]
      rw [← e0]
      exact hstepD hjD hX
    · rw [show lsum x (D.take j).reverse = sx by rw [hsx, e0, List.nil_append], iteF hX]
      simp only [mwalk, hjD, hX, and_false, ite_false, hiF]
      rw [e0, List.nil_append]
  · conv_lhs => rw [List.drop_of_length_le (show D.length ≤ j by omega),
      List.drop_eq_getElem_cons hiF]
    simp only [bwalk]
    rw [← hsy' hiF]
    simp only [mwalk, hjD, false_and, ite_false, hiF, ite_true]
    split_ifs
    · rfl
    · exact hstepF hiF _ (List.drop_of_length_le (by omega)).symm
  · conv_lhs => rw [List.drop_of_length_le (show D.length ≤ j by omega),
      List.drop_of_length_le (show F.length ≤ i by omega)]
    simp only [bwalk, mwalk, hjD, false_and, ite_false, hiF]
    rw [List.drop_of_length_le (show F.length ≤ i by omega), List.nil_append]

/-- The prefix `gpre` along the list. -/
theorem gpre_drop (x : ℕ → ℕ) (X : ℕ) (l : List ℕ) {t s : ℕ} (ht : t < l.length) :
    gpre x X s (l.drop t) = if 2 * (s + x (l.getD t 0)) ≤ X then
      l.getD t 0 :: gpre x X (s + x (l.getD t 0)) (l.drop (t + 1)) else [] := by
  rw [List.drop_eq_getElem_cons ht, gpre, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  rfl

/-! ### Segments of the list -/

theorem lsum_seg (f : ℕ → ℕ) (l : List ℕ) {a b : ℕ} (hb : b ≤ l.length) :
    lsum f ((l.drop a).take (b - a)) = ∑ t ∈ Ico a b, f (l.getD t 0) := by
  induction b with
  | zero => simp
  | succ b ih =>
    by_cases hab : b + 1 ≤ a
    · rw [Nat.sub_eq_zero_of_le hab, Ico_eq_empty_of_le hab]; simp
    · rw [sum_Ico_succ_top (by omega), ← ih (by omega), show b + 1 - a = (b - a) + 1 by omega,
        List.take_succ_eq_append_getElem (by simp; omega), lsum_append]
      simp only [lsum_cons, lsum_nil, Nat.add_zero, List.getElem_drop]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      congr 3
      omega

theorem mem_seg (l : List ℕ) {a b e : ℕ} (hb : b ≤ l.length) :
    e ∈ (l.drop a).take (b - a) ↔ ∃ t, a ≤ t ∧ t < b ∧ l.getD t 0 = e := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp only [List.length_take, List.length_drop] at ht
    refine ⟨a + t, by omega, by omega, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp
  · rintro ⟨t, h1, h2, rfl⟩
    refine ⟨t - a, by simp; omega, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp only [List.getElem_take, List.getElem_drop, Option.getD_some]
    congr 1; omega

variable {N W : ℕ} {P : Input}

variable (N W) in
/-- The list `l` at `l0` (`1350`, length `1351`). -/
structure LLay (l : List ℕ) (d : Config) : Prop where
  wb : WordsBounded W d
  one : d.nreg 1001 = 1
  len : d.nreg 1351 = l.length
  mem : ∀ t < l.length, d.nmem (d.nreg 1350 + t) = l.getD t 0
  lt : ∀ t < l.length, l.getD t 0 < N
  lW : d.nreg 1350 + l.length ≤ W

/-- The sum of the array at `1362` along the positions `[1360, 1361)` of the list. -/
def segSumBody : Stmt := block [.addN 1364 1350 1367, .loadN 1365 1364, .addN 1364 1362 1365,
  .loadN 1366 1364, .addN 1363 1363 1366, .addN 1367 1367 1001]

def segSum : Stmt := .seq (block [.constN 1363 0, .copyN 1367 1360]) (.whileLtN 1367 1361 segSumBody)

theorem segSum_exec {l : List ℕ} {d : Config} (hL : LLay N W l d) {lo hi af : ℕ} (f : ℕ → ℕ)
    (h60 : d.nreg 1360 = lo) (h61 : d.nreg 1361 = hi) (h62 : d.nreg 1362 = af)
    (hlh : lo ≤ hi) (hhl : hi ≤ l.length) (hf : ∀ i < N, d.nmem (af + i) = f i)
    (haf : af + N ≤ W) (hS : ∑ t ∈ Ico lo hi, f (l.getD t 0) ≤ W) :
    ∃ d' k, Exec P W segSum d d' k ∧ WordsBounded W d' ∧
      d'.nreg 1363 = ∑ t ∈ Ico lo hi, f (l.getD t 0) ∧ d'.nmem = d.nmem ∧
      (∀ r, r ≠ 1363 → r ≠ 1364 → r ≠ 1365 → r ≠ 1366 → r ≠ 1367 → d'.nreg r = d.nreg r) ∧
      k ≤ 8 * (hi - lo) + 4 := by
  have hw := hL.wb
  let I : ℕ → Config → Prop := fun j d' => WordsBounded W d' ∧ d'.nreg 1367 = j ∧
    d'.nreg 1361 = hi ∧ d'.nreg 1363 = ∑ t ∈ Ico lo j, f (l.getD t 0) ∧ d'.nmem = d.nmem ∧
    (∀ r, r ≠ 1363 → r ≠ 1364 → r ≠ 1365 → r ≠ 1366 → r ≠ 1367 → d'.nreg r = d.nreg r) ∧
    lo ≤ j
  obtain ⟨d₀, k₀, e₀, h₀, hk₀⟩ : ∃ d₀ k₀, Exec P W (block [.constN 1363 0, .copyN 1367 1360])
      d d₀ k₀ ∧ I lo d₀ ∧ k₀ = 2 := by
    exec_block
    · omega
    · refine ⟨⟨‹WordsBounded _ _›, by config_simp; exact h60, by config_simp; exact h61,
        by config_simp; simp, rfl, fun r h1 _ _ _ h5 => by simp [h1, h5], le_rfl⟩, rfl⟩
  have hmono : ∀ j, j ≤ hi → ∑ t ∈ Ico lo j, f (l.getD t 0) ≤ ∑ t ∈ Ico lo hi, f (l.getD t 0) :=
    fun j hj => sum_le_sum_of_subset (Ico_subset_Ico_right hj)
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1367) (rN := 1361)
    (N := hi) (lo := lo) (B := 6) (body := segSumBody) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi' => by
      obtain ⟨hw', h67, h61', h63, hm, hq, hlo⟩ := h
      have hxl := hL.lt i (by omega)
      have r50 : d'.nreg 1350 = d.nreg 1350 := hq 1350 (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have r62 : d'.nreg 1362 = af := by rw [hq 1362 (by omega) (by omega) (by omega)
        (by omega) (by omega), h62]
      have r1 : d'.nreg 1001 = 1 := by rw [hq 1001 (by omega) (by omega) (by omega) (by omega)
        (by omega), hL.one]
      have ml : d'.nmem (d.nreg 1350 + i) = l.getD i 0 := by rw [hm]; exact hL.mem i (by omega)
      have mf : d'.nmem (af + l.getD i 0) = f (l.getD i 0) := by rw [hm]; exact hf _ hxl
      have hs1 := hmono (i + 1) (by omega)
      rw [sum_Ico_succ_top hlo] at hs1
      unfold segSumBody
      exec_block
      · rw [r50, h67]; have := hL.lW; omega
      · config_simp; rw [r62, r50, h67, ml]; omega
      · config_simp; rw [r62, r50, h67, ml, mf, h63]; omega
      · config_simp; rw [h67]; have := hL.lW; omega
      · refine ⟨⟨‹WordsBounded _ _›, by config_simp; rw [h67, r1], by config_simp; exact h61',
          by config_simp; rw [r62, r50, h67, ml, mf, h63, sum_Ico_succ_top hlo], hm,
          fun r a b c' e f' => ?_, by omega⟩, by omega⟩
        simp only [upd_apply, a, b, c', e, f', ite_false]; exact hq r a b c' e f')
    hlh h₀
  obtain ⟨hw₁, -, -, h63₁, hm₁, hq₁, -⟩ := h₁
  exact ⟨d₁, k₀ + k₁, .seq e₀ e₁, hw₁, h63₁, hm₁, hq₁, by omega⟩

/-- The flags `1` at `1354` on the members of the positions `[1360, 1361)` of the list. -/
def segMarkBody : Stmt := block [.addN 1364 1350 1367, .loadN 1365 1364, .addN 1364 1354 1365,
  .storeN 1364 1001, .addN 1367 1367 1001]

def segMark : Stmt := .seq (block [.copyN 1367 1360]) (.whileLtN 1367 1361 segMarkBody)

theorem segMark_exec {l : List ℕ} {d : Config} (hL : LLay N W l d) {lo hi aj : ℕ}
    (h60 : d.nreg 1360 = lo) (h61 : d.nreg 1361 = hi) (h54 : d.nreg 1354 = aj)
    (hlh : lo ≤ hi) (hhl : hi ≤ l.length) (haj : aj + N ≤ W)
    (hd : d.nreg 1350 + l.length ≤ aj ∨ aj + N ≤ d.nreg 1350) :
    ∃ d' k, Exec P W segMark d d' k ∧ WordsBounded W d' ∧
      (∀ i < N, d'.nmem (aj + i) =
        if ∃ t ∈ Ico lo hi, l.getD t 0 = i then 1 else d.nmem (aj + i)) ∧
      (∀ a, (a < aj ∨ aj + N ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, r ≠ 1364 → r ≠ 1365 → r ≠ 1367 → d'.nreg r = d.nreg r) ∧
      k ≤ 7 * (hi - lo) + 3 := by
  have hw := hL.wb
  let I : ℕ → Config → Prop := fun j d' => WordsBounded W d' ∧ d'.nreg 1367 = j ∧
    d'.nreg 1361 = hi ∧
    (∀ i < N, d'.nmem (aj + i) =
      if ∃ t ∈ Ico lo j, l.getD t 0 = i then 1 else d.nmem (aj + i)) ∧
    (∀ a, (a < aj ∨ aj + N ≤ a) → d'.nmem a = d.nmem a) ∧
    (∀ r, r ≠ 1364 → r ≠ 1365 → r ≠ 1367 → d'.nreg r = d.nreg r) ∧ lo ≤ j
  obtain ⟨d₀, k₀, e₀, h₀, hk₀⟩ : ∃ d₀ k₀, Exec P W (block [.copyN 1367 1360])
      d d₀ k₀ ∧ I lo d₀ ∧ k₀ = 1 := by
    exec_block
    refine ⟨⟨‹WordsBounded _ _›, by config_simp; exact h60, by config_simp; exact h61,
      fun i _ => by
        rw [iteF (by rintro ⟨t, ht, -⟩; simp only [mem_Ico] at ht; omega)], fun _ _ => rfl,
      fun r _ _ h3 => by simp [h3], le_rfl⟩, rfl⟩
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1367) (rN := 1361)
    (N := hi) (lo := lo) (B := 5) (body := segMarkBody) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi' => by
      obtain ⟨hw', h67, h61', hF, hfr, hq, hlo⟩ := h
      have hxl := hL.lt i (by omega)
      have r50 : d'.nreg 1350 = d.nreg 1350 := hq 1350 (by omega) (by omega) (by omega)
      have r54 : d'.nreg 1354 = aj := by rw [hq 1354 (by omega) (by omega) (by omega), h54]
      have r1 : d'.nreg 1001 = 1 := by rw [hq 1001 (by omega) (by omega) (by omega), hL.one]
      have ml : d'.nmem (d.nreg 1350 + i) = l.getD i 0 := by
        rw [hfr _ (by have := hL.lW; omega)]; exact hL.mem i (by omega)
      unfold segMarkBody
      exec_block
      · rw [r50, h67]; have := hL.lW; omega
      · config_simp; rw [r54, r50, h67, ml]; omega
      · config_simp; rw [h67]; have := hL.lW; omega
      · refine ⟨⟨‹WordsBounded _ _›, by config_simp; rw [h67, r1], by config_simp; exact h61',
          fun y hy => ?_, fun a ha => ?_, fun r a b c' => ?_, by omega⟩, by omega⟩
        · simp only [Config.nmem_mk]
          rw [r54, r50, h67, ml, r1]
          simp only [upd_apply]
          by_cases hyx : aj + y = aj + l.getD i 0
          · rw [iteT hyx, iteT ⟨i, by
              exact mem_Ico.2 ⟨hlo, by omega⟩, by omega⟩]
          · rw [iteF hyx, hF y hy]
            congr 1
            simp only [eq_iff_iff]
            constructor
            · rintro ⟨t, ht, h3⟩; rw [mem_Ico] at ht; exact ⟨t, mem_Ico.2 ⟨ht.1, by omega⟩, h3⟩
            · rintro ⟨t, ht, h3⟩
              rw [mem_Ico] at ht
              refine ⟨t, mem_Ico.2 ⟨ht.1, ?_⟩, h3⟩
              rcases Nat.lt_succ_iff_lt_or_eq.1 ht.2 with h2 | rfl
              · exact h2
              · exact absurd (by rw [h3]) hyx
        · simp only [Config.nmem_mk]
          rw [r54, r50, h67, ml, upd_other _ _ _ (by omega)]; exact hfr a ha
        · simp only [upd_apply, a, b, c', ite_false]; exact hq r a b c')
    hlh h₀
  obtain ⟨hw₁, -, -, hF₁, hfr₁, hq₁, -⟩ := h₁
  exact ⟨d₁, k₀ + k₁, .seq e₀ e₁, hw₁, hF₁, hfr₁, hq₁, by omega⟩

theorem lsum_take_add_drop (f : ℕ → ℕ) (l : List ℕ) (t : ℕ) :
    lsum f (l.take t) + lsum f (l.drop t) = lsum f l := by
  rw [← lsum_append, List.take_append_drop]

theorem lsum_take_succ (f : ℕ → ℕ) (l : List ℕ) {t : ℕ} (ht : t < l.length) :
    lsum f (l.take (t + 1)) = lsum f (l.take t) + f (l.getD t 0) := by
  rw [List.take_succ_eq_append_getElem ht, lsum_append, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem ht]
  simp

/-! ### The prefix -/

/-- A round of the prefix: the next member of the list joins while the measure stays at most
half of `X` (`1373`). -/
def gpBody : Stmt := .ifLtN 1370 1351
  (.seq (block [.addN 1364 1350 1370, .loadN 1365 1364, .addN 1364 1352 1365, .loadN 1366 1364,
      .addN 1374 1371 1366, .addN 1366 1374 1374])
    (.ifLtN 1373 1366 (.instr (.constN 1372 1)) (block [.copyN 1371 1374, .addN 1370 1370 1001])))
  (.instr (.constN 1372 1))

def gpLoop : Stmt := .whileLtN 1372 1001 gpBody

theorem gpLoop_exec {l : List ℕ} {d : Config} (hL : LLay N W l d) {ax X : ℕ} (x : ℕ → ℕ)
    (h52 : d.nreg 1352 = ax) (hx : ∀ i < N, d.nmem (ax + i) = x i) (hax : ax + N ≤ W)
    (h70 : d.nreg 1370 = 0) (h71 : d.nreg 1371 = 0) (h72 : d.nreg 1372 = 0)
    (h73 : d.nreg 1373 = X) (hX : X = lsum x l) (hXW : 2 * X ≤ W) (hW1 : 1 ≤ W) :
    ∃ d' k, Exec P W gpLoop d d' k ∧ WordsBounded W d' ∧
      gpre x X 0 l = l.take (d'.nreg 1370) ∧ d'.nreg 1370 ≤ l.length ∧
      d'.nreg 1371 = lsum x (l.take (d'.nreg 1370)) ∧ d'.nmem = d.nmem ∧
      (∀ r, r ≠ 1364 → r ≠ 1365 → r ≠ 1366 → r ≠ 1370 → r ≠ 1371 → r ≠ 1372 → r ≠ 1374 →
        d'.nreg r = d.nreg r) ∧ k ≤ 13 * l.length + 15 := by
  have hW := hL.lW
  have hle : ∀ t, lsum x (l.take t) ≤ X := fun t => by
    have := lsum_take_add_drop x l t; omega
  let I : ℕ × ℕ → Config → Prop := fun st c => WordsBounded W c ∧ c.nreg 1370 = st.1 ∧
    c.nreg 1371 = lsum x (l.take st.1) ∧ c.nreg 1372 = st.2 ∧ st.2 ≤ 1 ∧ st.1 ≤ l.length ∧
    gpre x X 0 l = l.take st.1 ++
      (if st.2 = 0 then gpre x X (lsum x (l.take st.1)) (l.drop st.1) else []) ∧
    c.nmem = d.nmem ∧ (∀ r, r ≠ 1364 → r ≠ 1365 → r ≠ 1366 → r ≠ 1370 → r ≠ 1371 → r ≠ 1372 →
      r ≠ 1374 → c.nreg r = d.nreg r)
  obtain ⟨st, c', k, e, ⟨hw', h70', h71', h72', hgo, htl, hg, hm, hq⟩, hn, hk⟩ :=
    whileLtN_abs (P := P) (W := W) (a := 1372) (b := 1001) (body := gpBody) I
    (fun st => 13 * (l.length - st.1) + 13 * (1 - st.2)) (fun _ _ h => h.1)
    (fun st c ⟨hw', h70', h71', h72', hgo, htl, hg, hm, hq⟩ ht => by
      have r1 : c.nreg 1001 = 1 := by rw [hq 1001 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega), hL.one]
      rw [h72', r1] at ht
      have hgo0 : st.2 = 0 := by omega
      have r51 : c.nreg 1351 = l.length := by rw [hq 1351 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega), hL.len]
      have r50 : c.nreg 1350 = d.nreg 1350 := hq 1350 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
      have r52 : c.nreg 1352 = ax := by rw [hq 1352 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega), h52]
      have r73 : c.nreg 1373 = X := by rw [hq 1373 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega), h73]
      rw [hgo0, iteT rfl] at hg
      unfold gpBody
      by_cases htn : st.1 < l.length
      · have hxl := hL.lt st.1 htn
        have ml : c.nmem (d.nreg 1350 + st.1) = l.getD st.1 0 := by
          rw [hm]; exact hL.mem _ htn
        have mx : c.nmem (ax + l.getD st.1 0) = x (l.getD st.1 0) := by rw [hm]; exact hx _ hxl
        have hs1 := lsum_take_succ x l htn
        have hs2 := hle (st.1 + 1)
        rw [gpre_drop x X l htn] at hg
        by_cases hc : 2 * (lsum x (l.take st.1) + x (l.getD st.1 0)) ≤ X
        · rw [iteT hc] at hg
          refine ⟨(st.1 + 1, 0), ?_⟩
          refine spec_ifLtN_true (by omega) ?_
          refine spec_seq ?_
          exec_block
          · rw [r50, h70']; omega
          · config_simp; rw [r52, r50, h70', ml]; omega
          · config_simp; rw [r52, r50, h70', ml, mx, h71']; omega
          · config_simp; rw [r52, r50, h70', ml, mx, h71']; omega
          · refine spec_ifLtN_false (by config_simp; rw [r52, r50, h70', ml, mx, h71', r73]; omega) ?_
            exec_block
            · config_simp; rw [h70', r1]; omega
            · refine ⟨⟨‹_›, by config_simp; rw [h70', r1], ?_, by
                config_simp; rw [h72', hgo0], by simp, by simp only; omega, ?_, hm,
                fun r a b c'' e f g h' => ?_⟩,
                by simp only; omega⟩
              · config_simp; rw [r52, r50, h70', ml, mx, h71', hs1]
              · simp only [iteT]
                rw [hg, hs1, List.take_succ_eq_append_getElem htn, List.append_assoc]
                congr 1
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htn]; rfl
              · simp only [upd_apply, a, b, c'', e, f, g, h', ite_false]
                exact hq r a b c'' e f g h'
        · rw [iteF hc] at hg
          refine ⟨(st.1, 1), ?_⟩
          refine spec_ifLtN_true (by omega) ?_
          refine spec_seq ?_
          exec_block
          · rw [r50, h70']; omega
          · config_simp; rw [r52, r50, h70', ml]; omega
          · config_simp; rw [r52, r50, h70', ml, mx, h71']; omega
          · config_simp; rw [r52, r50, h70', ml, mx, h71']; omega
          · refine spec_ifLtN_true (by config_simp; rw [r52, r50, h70', ml, mx, h71', r73]; omega) ?_
            refine spec_instr (Exec.constN ‹_› _ _ (by omega)) fun hw₂ => ?_
            refine ⟨⟨hw₂, by config_simp; exact h70', by config_simp; exact h71',
              by config_simp, le_rfl, htl, by simp only [one_ne_zero, ite_false]; simpa using hg, hm,
              fun r a b c'' e f g h' => ?_⟩, by simp only; omega⟩
            simp only [upd_apply, a, b, c'', e, f, g, h', ite_false]
            exact hq r a b c'' e f g h'
      · refine ⟨(st.1, 1), ?_⟩
        refine spec_ifLtN_false (by omega) ?_
        refine spec_instr (Exec.constN ‹_› _ _ (by omega)) fun hw₂ => ?_
        refine ⟨⟨hw₂, by config_simp; exact h70', by config_simp; exact h71',
          by config_simp, le_rfl, htl, ?_, hm, fun r a b c'' e f g h' => ?_⟩, by simp only; omega⟩
        · simp only [one_ne_zero, ite_false]
          rw [hg, List.drop_of_length_le (by omega)]
          simp [gpre]
        · simp only [upd_apply, a, b, c'', e, f, g, h', ite_false]
          exact hq r a b c'' e f g h')
    (s := (0, 0)) ⟨hL.wb, h70, by rw [h71]; simp, h72, by omega, by omega, by simp, rfl,
      fun _ _ _ _ _ _ _ _ => rfl⟩
  have r1 : c'.nreg 1001 = 1 := by rw [hq 1001 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega), hL.one]
  rw [h72', r1] at hn
  have h1 : st.2 = 1 := by omega
  rw [h1] at hg
  simp only [one_ne_zero, ite_false, List.append_nil] at hg
  refine ⟨c', k, e, hw', by rw [h70']; exact hg, by rw [h70']; exact htl, by rw [h70', h71'],
    hm, hq, by simp only at hk; omega⟩

/-! ### The walk -/

theorem getD_seg (l : List ℕ) {a b t : ℕ} (ht : t < b) :
    ((l.drop a).take b).getD t 0 = l.getD (a + t) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, ht]

theorem length_seg (l : List ℕ) {a b : ℕ} (h : a + b ≤ l.length) :
    ((l.drop a).take b).length = b := by
  simp; omega

theorem lsum_fam_le (f : ℕ → ℕ) (F D : List ℕ) (i j : ℕ) :
    lsum f (F.drop i ++ (D.take j).reverse) ≤ lsum f F + lsum f D := by
  rw [lsum_append, lsum_reverse]
  have h1 := lsum_take_add_drop f F i
  have h2 := lsum_take_add_drop f D j
  omega

/-- The walk: a member of the second list joins while the measure is below half of `X`;
otherwise the first member of the first list leaves, and the walk stops when the `y`-measure is
small enough or the first list is empty. -/
def bwStepD : Stmt := block [.addN 1377 1377 1366, .addN 1364 1353 1365, .loadN 1366 1364,
  .addN 1378 1378 1366, .addN 1376 1376 1001]

def bwRem : Stmt := .ifLtN 1375 1381
  (.seq (block [.addN 1364 1380 1375, .addN 1364 1350 1364, .loadN 1365 1364, .addN 1364 1353 1365,
      .loadN 1366 1364, .subN 1378 1378 1366, .mulN 1374 1355 1378, .addN 1375 1375 1001])
    (.ifLtN 1356 1374 (block [.addN 1364 1352 1365, .loadN 1366 1364, .subN 1377 1377 1366])
      (.instr (.constN 1372 1))))
  (.instr (.constN 1372 1))

def bwBody : Stmt := .ifLtN 1376 1383
  (.seq (block [.addN 1364 1382 1376, .addN 1364 1350 1364, .loadN 1365 1364, .addN 1364 1352 1365,
      .loadN 1366 1364, .addN 1374 1377 1377])
    (.ifLtN 1374 1373 bwStepD bwRem))
  bwRem

def bwLoop : Stmt := .whileLtN 1372 1001 bwBody

theorem bwLoop_exec {l : List ℕ} {d : Config} (hL : LLay N W l d) {ax ay X p q f0 fl s0 dl : ℕ}
    (x y : ℕ → ℕ) (h52 : d.nreg 1352 = ax) (h53 : d.nreg 1353 = ay)
    (hx : ∀ i < N, d.nmem (ax + i) = x i) (hy : ∀ i < N, d.nmem (ay + i) = y i)
    (hax : ax + N ≤ W) (hay : ay + N ≤ W) (h55 : d.nreg 1355 = p) (h56 : d.nreg 1356 = q)
    (h73 : d.nreg 1373 = X) (h80 : d.nreg 1380 = f0) (h81 : d.nreg 1381 = fl)
    (h82 : d.nreg 1382 = s0) (h83 : d.nreg 1383 = dl) (hf : f0 + fl ≤ l.length)
    (hd : s0 + dl ≤ l.length) {Y : ℕ}
    (hXF : lsum x ((l.drop f0).take fl) + lsum x ((l.drop s0).take dl) ≤ X)
    (hYF : lsum y ((l.drop f0).take fl) + lsum y ((l.drop s0).take dl) ≤ Y)
    (hXW : 2 * X ≤ W) (hYW : p * Y + Y ≤ W) (hW1 : 1 ≤ W)
    (h75 : d.nreg 1375 = 0) (h76 : d.nreg 1376 = 0) (h72 : d.nreg 1372 = 0)
    (h77 : d.nreg 1377 = lsum x ((l.drop f0).take fl))
    (h78 : d.nreg 1378 = lsum y ((l.drop f0).take fl)) :
    let F := (l.drop f0).take fl
    let D := (l.drop s0).take dl
    let fin := mwalk x y X p q F D (fl + dl) 0 0 (lsum x F) (lsum y F)
    ∃ d' k, Exec P W bwLoop d d' k ∧ WordsBounded W d' ∧ d'.nreg 1375 = fin.1 ∧
      d'.nreg 1376 = fin.2 ∧ fin.1 ≤ fl ∧ fin.2 ≤ dl ∧ d'.nmem = d.nmem ∧
      (∀ r, r ≠ 1364 → r ≠ 1365 → r ≠ 1366 → r ≠ 1372 → r ≠ 1374 → r ≠ 1375 → r ≠ 1376 →
        r ≠ 1377 → r ≠ 1378 → d'.nreg r = d.nreg r) ∧ k ≤ 30 * (fl + dl + 1) + 2 := by
  intro F D fin
  have hXF' : lsum x F + lsum x D ≤ X := hXF
  have hYF' : lsum y F + lsum y D ≤ Y := hYF
  have hW := hL.lW
  have hFl : F.length = fl := length_seg l hf
  have hDl : D.length = dl := length_seg l hd
  let I : ℕ × ℕ × ℕ × ℕ × ℕ → Config → Prop := fun st c => WordsBounded W c ∧
    c.nreg 1375 = st.1 ∧ c.nreg 1376 = st.2.1 ∧ c.nreg 1377 = st.2.2.1 ∧
    c.nreg 1378 = st.2.2.2.1 ∧ c.nreg 1372 = st.2.2.2.2 ∧ st.2.2.2.2 ≤ 1 ∧ st.1 ≤ fl ∧
    st.2.1 ≤ dl ∧
    (st.2.2.2.2 = 0 → st.2.2.1 = lsum x (F.drop st.1 ++ (D.take st.2.1).reverse) ∧
      st.2.2.2.1 = lsum y (F.drop st.1 ++ (D.take st.2.1).reverse) ∧
      mwalk x y X p q F D ((fl - st.1) + (dl - st.2.1)) st.1 st.2.1 st.2.2.1 st.2.2.2.1 = fin) ∧
    (st.2.2.2.2 = 1 → (st.1, st.2.1) = fin) ∧ c.nmem = d.nmem ∧
    (∀ r, r ≠ 1364 → r ≠ 1365 → r ≠ 1366 → r ≠ 1372 → r ≠ 1374 → r ≠ 1375 → r ≠ 1376 →
      r ≠ 1377 → r ≠ 1378 → c.nreg r = d.nreg r)
  have Φdef : ∀ st : ℕ × ℕ × ℕ × ℕ × ℕ, 30 * (1 - st.2.2.2.2) * ((fl - st.1) + (dl - st.2.1) + 1) =
      30 * (1 - st.2.2.2.2) * ((fl - st.1) + (dl - st.2.1) + 1) := fun _ => rfl
  have hstep : ∀ (st : ℕ × ℕ × ℕ × ℕ × ℕ) (c : Config), I st c → c.nreg 1372 < c.nreg 1001 →
      ∃ c' k, Exec P W bwBody c c' k ∧ ∃ st', I st' c' ∧
        30 * (1 - st'.2.2.2.2) * ((fl - st'.1) + (dl - st'.2.1) + 1) + k + 2 ≤
          30 * (1 - st.2.2.2.2) * ((fl - st.1) + (dl - st.2.1) + 1) := by
    intro st c ⟨hw', h75', h76', h77', h78', h72', hgo, hi, hj, h0, _, hm, hq⟩ ht
    have r1 : c.nreg 1001 = 1 := by rw [hq 1001 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega), hL.one]
    rw [h72', r1] at ht
    have hgo0 : st.2.2.2.2 = 0 := by omega
    obtain ⟨hsx, hsy, hmw⟩ := h0 hgo0
    obtain ⟨i, j, sx, sy, go⟩ := st
    simp only at hgo0 hsx hsy hmw h75' h76' h77' h78' hi hj
    subst hgo0
    simp only [Nat.sub_zero]
    -- the registers of any state with the same frame
    have regs : ∀ c₁ : Config, (∀ r, r ≠ 1364 → r ≠ 1365 → r ≠ 1366 → r ≠ 1372 → r ≠ 1374 →
        r ≠ 1375 → r ≠ 1376 → r ≠ 1377 → r ≠ 1378 → c₁.nreg r = d.nreg r) →
        c₁.nreg 1350 = d.nreg 1350 ∧ c₁.nreg 1001 = 1 ∧ c₁.nreg 1352 = ax ∧ c₁.nreg 1353 = ay ∧
        c₁.nreg 1355 = p ∧ c₁.nreg 1356 = q ∧ c₁.nreg 1373 = X ∧ c₁.nreg 1380 = f0 ∧
        c₁.nreg 1381 = fl ∧ c₁.nreg 1382 = s0 ∧ c₁.nreg 1383 = dl := fun c₁ hq₁ => by
      have K : ∀ r, 1379 ≤ r → c₁.nreg r = d.nreg r := fun r hr =>
        hq₁ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
      refine ⟨hq₁ 1350 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hq₁ 1001 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega), hL.one]
      · rw [hq₁ 1352 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega), h52]
      · rw [hq₁ 1353 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega), h53]
      · rw [hq₁ 1355 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega), h55]
      · rw [hq₁ 1356 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega), h56]
      · rw [hq₁ 1373 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega), h73]
      · rw [K 1380 (by omega), h80]
      · rw [K 1381 (by omega), h81]
      · rw [K 1382 (by omega), h82]
      · rw [K 1383 (by omega), h83]
    obtain ⟨r50, _, r52, r53, r55, r56, r73, r80, r81, r82, r83⟩ := regs c hq
    have hsxl := lsum_fam_le x F D i j
    have hsyl := lsum_fam_le y F D i j
    -- removing the first member of the first list
    have hrem : ∀ c₁ : Config, WordsBounded W c₁ → c₁.nmem = d.nmem →
        (∀ r, r ≠ 1364 → r ≠ 1365 → r ≠ 1366 → r ≠ 1372 → r ≠ 1374 → r ≠ 1375 → r ≠ 1376 →
          r ≠ 1377 → r ≠ 1378 → c₁.nreg r = d.nreg r) →
        c₁.nreg 1375 = i → c₁.nreg 1376 = j → c₁.nreg 1377 = sx → c₁.nreg 1378 = sy →
        c₁.nreg 1372 = 0 → ¬ (j < D.length ∧ 2 * sx < X) →
        ∃ c' k, Exec P W bwRem c₁ c' k ∧ k ≤ 13 ∧ ∃ st', I st' c' ∧
          30 * (1 - st'.2.2.2.2) * ((fl - st'.1) + (dl - st'.2.1) + 1) + 24 ≤
            30 * ((fl - i) + (dl - j) + 1) := by
      intro c₁ hw₁ hm₁ hq₁ g75 g76 g77 g78 g72 hn
      obtain ⟨s50, s1, s52, s53, s55, s56, s73, s80, s81, s82, s83⟩ := regs c₁ hq₁
      unfold bwRem
      by_cases hiF : i < fl
      · have hgi : F.getD i 0 = l.getD (f0 + i) 0 := getD_seg l hiF
        have hli := hL.lt (f0 + i) (by omega)
        have ml : c₁.nmem (d.nreg 1350 + (f0 + i)) = l.getD (f0 + i) 0 := by
          rw [hm₁]; exact hL.mem _ (by omega)
        have mx : c₁.nmem (ax + l.getD (f0 + i) 0) = x (l.getD (f0 + i) 0) := by
          rw [hm₁]; exact hx _ hli
        have my : c₁.nmem (ay + l.getD (f0 + i) 0) = y (l.getD (f0 + i) 0) := by
          rw [hm₁]; exact hy _ hli
        have hsy' : sy - y (F.getD i 0) = lsum y (F.drop (i + 1) ++ (D.take j).reverse) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
            hsy, List.drop_eq_getElem_cons (by omega), List.cons_append, lsum_cons]; omega
        have hsx' : sx - x (F.getD i 0) = lsum x (F.drop (i + 1) ++ (D.take j).reverse) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
            hsx, List.drop_eq_getElem_cons (by omega), List.cons_append, lsum_cons]; omega
        have hmw' : mwalk x y X p q F D ((fl - i) + (dl - j)) i j sx sy =
            if p * (sy - y (F.getD i 0)) ≤ q then (i + 1, j)
            else mwalk x y X p q F D ((fl - (i + 1)) + (dl - j)) (i + 1) j
              (sx - x (F.getD i 0)) (sy - y (F.getD i 0)) := by
          rw [show (fl - i) + (dl - j) = ((fl - (i + 1)) + (dl - j)) + 1 by omega]
          simp only [mwalk, hn, ite_false, hFl, hiF, ite_true]
        have hpy : p * (sy - y (l.getD (f0 + i) 0)) ≤ p * Y := Nat.mul_le_mul_left _ (by omega)
        rw [hgi] at hsy' hsx' hmw'
        refine spec_ifLtN_true (by rw [g75, s81]; exact hiF) ?_
        refine spec_seq ?_
        exec_block
        · rw [s80, g75]; omega
        · config_simp; rw [s50, s80, g75]; omega
        · config_simp; rw [s53, s50, s80, g75, ml]; omega
        · config_simp; rw [s55, g78, s53, s50, s80, g75, ml, my]; omega
        · config_simp; rw [g75, s1]; omega
        · by_cases hq' : p * (sy - y (l.getD (f0 + i) 0)) ≤ q
          · rw [iteT hq'] at hmw'
            refine spec_ifLtN_false ?_ ?_
            · config_simp; rw [s56, s55, g78, s53, s50, s80, g75, ml, my]; omega
            refine spec_instr (Exec.constN ‹_› _ _ (by omega)) fun hw₂ => ?_
            refine ⟨by omega, (i + 1, j, sx, sy - y (l.getD (f0 + i) 0), 1), ⟨hw₂, ?_, ?_, ?_, ?_,
              by config_simp, le_rfl, by simp only; omega, hj, fun h => by simp at h,
              fun _ => by rw [← hmw, hmw'], by config_simp; exact hm₁,
              fun r a b c'' e f g h' i' j' => ?_⟩, by simp only; omega⟩
            · config_simp; rw [g75, s1]
            · config_simp; exact g76
            · config_simp; exact g77
            · config_simp; rw [g78, s53, s50, s80, g75, ml, my]
            · simp only [Config.nreg_mk, upd_apply, a, b, c'', e, f, g, h', i', j', ite_false]
              exact hq₁ r a b c'' e f g h' i' j'
          · rw [iteF hq'] at hmw'
            refine spec_ifLtN_true ?_ ?_
            · config_simp; rw [s56, s55, g78, s53, s50, s80, g75, ml, my]; omega
            exec_block
            · config_simp; rw [s52, s50, s80, g75, ml]; omega
            · refine ⟨by omega, (i + 1, j, sx - x (l.getD (f0 + i) 0), sy - y (l.getD (f0 + i) 0), 0),
                ⟨‹_›, ?_, ?_, ?_, ?_, by config_simp; exact g72, by simp, by simp only; omega, hj,
                fun _ => ⟨hsx', hsy', by rw [← hmw, hmw']⟩, fun h => by simp at h,
                by config_simp; exact hm₁, fun r a b c'' e f g h' i' j' => ?_⟩, by simp only; omega⟩
              · config_simp; rw [g75, s1]
              · config_simp; exact g76
              · config_simp; rw [s52, s50, s80, g75, ml, mx, g77]
              · config_simp; rw [g78, s53, s50, s80, g75, ml, my]
              · simp only [Config.nreg_mk, upd_apply, a, b, c'', e, f, g, h', i', j', ite_false]
                exact hq₁ r a b c'' e f g h' i' j'
      · refine spec_ifLtN_false ?_ ?_
        · rw [g75, s81]; exact hiF
        refine spec_instr (Exec.constN hw₁ _ _ (by omega)) fun hw₂ => ?_
        have hfin : (i, j) = fin := by
          rw [← hmw]
          rcases Nat.eq_zero_or_pos (dl - j) with h0 | h0
          · rw [show (fl - i) + (dl - j) = 0 by omega]; rfl
          · rw [show (fl - i) + (dl - j) = (dl - j - 1) + 1 by omega]
            simp only [mwalk, hn, ite_false, hFl, hiF]
        refine ⟨by omega, (i, j, sx, sy, 1), ⟨hw₂, by config_simp; exact g75,
          by config_simp; exact g76, by config_simp; exact g77, by config_simp; exact g78,
          by config_simp, le_rfl, hi, hj, fun h => by simp at h, fun _ => hfin,
          by config_simp; exact hm₁, fun r a b c'' e f g h' i' j' => ?_⟩, by simp only; omega⟩
        simp only [Config.nreg_mk, upd_apply, a, b, c'', e, f, g, h', i', j', ite_false]
        exact hq₁ r a b c'' e f g h' i' j'
    unfold bwBody
    by_cases hjD : j < dl
    · have hgj : D.getD j 0 = l.getD (s0 + j) 0 := getD_seg l hjD
      have hlj := hL.lt (s0 + j) (by omega)
      have ml : c.nmem (d.nreg 1350 + (s0 + j)) = l.getD (s0 + j) 0 := by
        rw [hm]; exact hL.mem _ (by omega)
      have mx : c.nmem (ax + l.getD (s0 + j) 0) = x (l.getD (s0 + j) 0) := by
        rw [hm]; exact hx _ hlj
      have my : c.nmem (ay + l.getD (s0 + j) 0) = y (l.getD (s0 + j) 0) := by
        rw [hm]; exact hy _ hlj
      refine spec_ifLtN_true ?_ ?_
      · rw [h76', r83]; exact hjD
      refine spec_seq ?_
      exec_block
      · rw [r82, h76']; omega
      · config_simp; rw [r50, r82, h76']; omega
      · config_simp; rw [r52, r50, r82, h76', ml]; omega
      · config_simp; rw [h77']; omega
      · by_cases hX : 2 * sx < X
        · have hmw' : mwalk x y X p q F D ((fl - i) + (dl - j)) i j sx sy =
              mwalk x y X p q F D ((fl - i) + (dl - (j + 1))) i (j + 1) (sx + x (D.getD j 0))
                (sy + y (D.getD j 0)) := by
            rw [show (fl - i) + (dl - j) = ((fl - i) + (dl - (j + 1))) + 1 by omega]
            simp only [mwalk, hDl, hjD, hX, and_self, ite_true]
          have hsx' : sx + x (D.getD j 0) = lsum x (F.drop i ++ (D.take (j + 1)).reverse) := by
            rw [hsx, List.take_succ_eq_append_getElem (by omega), List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (by omega)]
            simp only [lsum_append, lsum_reverse, lsum_cons, lsum_nil, Option.getD_some]; ring
          have hsy' : sy + y (D.getD j 0) = lsum y (F.drop i ++ (D.take (j + 1)).reverse) := by
            rw [hsy, List.take_succ_eq_append_getElem (by omega), List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (by omega)]
            simp only [lsum_append, lsum_reverse, lsum_cons, lsum_nil, Option.getD_some]; ring
          have hb1 := lsum_fam_le x F D i (j + 1)
          have hb2 := lsum_fam_le y F D i (j + 1)
          rw [hgj] at hmw' hsx' hsy'
          refine spec_ifLtN_true ?_ ?_
          · config_simp; rw [h77', r73]; omega
          exec_block
          · config_simp; rw [r52, r50, r82, h76', ml, mx, h77']; omega
          · config_simp; rw [r53, r50, r82, h76', ml]; omega
          · config_simp; rw [r53, r50, r82, h76', ml, my, h78']; omega
          · config_simp; rw [h76', r1]; omega
          · refine ⟨(i, j + 1, sx + x (l.getD (s0 + j) 0), sy + y (l.getD (s0 + j) 0), 0),
              ⟨‹_›, ?_, ?_, ?_, ?_, by config_simp; exact h72', by simp, hi, by simp only; omega,
              fun _ => ⟨hsx', hsy', by rw [← hmw, hmw']⟩, fun h => by simp at h,
              by config_simp; exact hm, fun r a b c'' e f g h' i' j' => ?_⟩, by simp only; omega⟩
            · config_simp; exact h75'
            · config_simp; rw [h76', r1]
            · config_simp; rw [r52, r50, r82, h76', ml, mx, h77']
            · config_simp; rw [r53, r50, r82, h76', ml, my, h78']
            · simp only [Config.nreg_mk, upd_apply, a, b, c'', e, f, g, h', i', j', ite_false]
              exact hq r a b c'' e f g h' i' j'
        · refine spec_ifLtN_false ?_ ?_
          · config_simp; rw [h77', r73]; omega
          obtain ⟨c', k', e', hk', st', hI', hΦ⟩ := hrem _ ‹_› (by config_simp; exact hm)
            (fun r a b c'' e f g h' i' j' => by
              simp only [Config.nreg_mk, upd_apply, a, b, c'', e, f, g, h', i', j', ite_false]
              exact hq r a b c'' e f g h' i' j')
            (by config_simp; exact h75') (by config_simp; exact h76')
            (by config_simp; exact h77') (by config_simp; exact h78') (by config_simp; exact h72')
            (fun h => hX h.2)
          exact ⟨c', k', e', st', hI', by omega⟩
    · refine spec_ifLtN_false ?_ ?_
      · rw [h76', r83]; exact hjD
      obtain ⟨c', k', e', hk', st', hI', hΦ⟩ := hrem c hw' hm hq h75' h76' h77' h78' h72'
        (fun h => hjD (by rw [hDl] at h; exact h.1))
      exact ⟨c', k', e', st', hI', by omega⟩
  obtain ⟨st, c', k, e, ⟨hw', h75', h76', -, -, h72', hgo, hi, hj, -, hfin, hm, hq⟩, hn, hk⟩ :=
    whileLtN_abs (P := P) (W := W) (a := 1372) (b := 1001) (body := bwBody) I
    (fun st => 30 * (1 - st.2.2.2.2) * ((fl - st.1) + (dl - st.2.1) + 1)) (fun _ _ h => h.1)
    (fun st c h ht => by
      obtain ⟨c', k, e, st', h', hk⟩ := hstep st c h ht
      exact ⟨st', c', k, e, h', hk⟩)
    (s := (0, 0, lsum x F, lsum y F, 0))
    ⟨hL.wb, h75, h76, h77, h78, h72, by simp, by simp, by simp,
      fun _ => ⟨by simp, by simp, by simp only [Nat.sub_zero]; rfl⟩, fun h => by simp at h, rfl,
      fun _ _ _ _ _ _ _ _ _ _ => rfl⟩
  have r1 : c'.nreg 1001 = 1 := by rw [hq 1001 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega), hL.one]
  rw [h72', r1] at hn
  have h1 : st.2.2.2.2 = 1 := by omega
  have hf := hfin h1
  refine ⟨c', k, e, hw', by rw [h75', ← hf], by rw [h76', ← hf], by rw [← hf]; exact hi,
    by rw [← hf]; exact hj, hm, hq, by simp only at hk; omega⟩

/-! ### The balanced split -/

theorem LLay.congr {l : List ℕ} {d c : Config} (h : LLay N W l d) (hw : WordsBounded W c)
    (hr : ∀ r, r < 1360 → c.nreg r = d.nreg r)
    (hm : ∀ t < l.length, c.nmem (d.nreg 1350 + t) = d.nmem (d.nreg 1350 + t)) :
    LLay N W l c :=
  ⟨hw, by rw [hr 1001 (by omega)]; exact h.one, by rw [hr 1351 (by omega)]; exact h.len,
    fun t ht => by rw [hr 1350 (by omega), hm t ht]; exact h.mem t ht, h.lt,
    by rw [hr 1350 (by omega)]; exact h.lW⟩

/-- The flags of the result of the walk: the rest of the first list and the taken part of the
second. -/
def bsMarks : Stmt := .seq (block [.addN 1360 1380 1375, .addN 1361 1380 1381])
  (.seq segMark (.seq (block [.copyN 1360 1382, .addN 1361 1382 1376]) segMark))

def bsCase1 : Stmt := .seq (block [.constN 1380 0, .copyN 1381 1370, .copyN 1382 1370,
  .subN 1383 1351 1370, .constN 1375 0, .constN 1376 0, .copyN 1377 1371, .copyN 1378 1384,
  .constN 1372 0]) (.seq bwLoop bsMarks)

def bsCase2 : Stmt := .seq (block [.copyN 1380 1370, .subN 1381 1351 1370, .constN 1382 0,
  .copyN 1383 1370, .constN 1375 0, .constN 1376 0, .subN 1377 1373 1371, .copyN 1378 1385,
  .constN 1372 0]) (.seq bwLoop bsMarks)

def bsCase3 : Stmt := .seq (block [.constN 1360 0, .copyN 1361 1370]) segMark

/-- **The balanced split on the machine**: the list at `1350` (length `1351`), the measures at
`1352`, `1353`, the flags at `1354`, the constants `p`, `q` in `1355`, `1356`. -/
def bsProg : Stmt :=
  .seq (block [.constN 1360 0, .copyN 1361 1351, .copyN 1362 1352])
  (.seq segSum
  (.seq (block [.copyN 1373 1363, .constN 1370 0, .constN 1371 0, .constN 1372 0])
  (.seq gpLoop
  (.seq (block [.constN 1360 0, .copyN 1361 1370, .copyN 1362 1353])
  (.seq segSum
  (.seq (block [.copyN 1384 1363, .copyN 1360 1370, .copyN 1361 1351])
  (.seq segSum
  (.seq (block [.copyN 1385 1363, .mulN 1386 1355 1384, .mulN 1387 1355 1385])
    (.ifLtN 1356 1386 bsCase1 (.ifLtN 1356 1387 bsCase2 bsCase3))))))))))

theorem mem_drop_seg (l : List ℕ) {a b i e : ℕ} (h : a + b ≤ l.length) (hi : i ≤ b) :
    e ∈ ((l.drop a).take b).drop i ↔ ∃ t ∈ Ico (a + i) (a + b), l.getD t 0 = e := by
  rw [List.drop_take, List.drop_drop, show b - i = (a + b) - (a + i) by omega, mem_seg l h]
  simp only [mem_Ico]
  constructor
  · rintro ⟨t, h1, h2, h3⟩; exact ⟨t, ⟨by omega, h2⟩, h3⟩
  · rintro ⟨t, ⟨h1, h2⟩, h3⟩; exact ⟨t, by omega, h2, h3⟩

theorem mem_take_seg (l : List ℕ) {a b j e : ℕ} (h : a + b ≤ l.length) (hj : j ≤ b) :
    e ∈ ((l.drop a).take b).take j ↔ ∃ t ∈ Ico a (a + j), l.getD t 0 = e := by
  rw [List.take_take, min_eq_left hj, show j = (a + j) - a by omega, mem_seg l (by omega)]
  simp only [mem_Ico]
  constructor
  · rintro ⟨t, h1, h2, h3⟩; exact ⟨t, ⟨h1, by omega⟩, h3⟩
  · rintro ⟨t, ⟨h1, h2⟩, h3⟩; exact ⟨t, h1, by omega, h3⟩

set_option maxHeartbeats 1000000 in
theorem bsMarks_exec {l : List ℕ} {d : Config} (hL : LLay N W l d) {aj f0 fl s0 dl i' j' : ℕ}
    (h54 : d.nreg 1354 = aj) (h80 : d.nreg 1380 = f0) (h81 : d.nreg 1381 = fl)
    (h82 : d.nreg 1382 = s0) (h75 : d.nreg 1375 = i') (h76 : d.nreg 1376 = j')
    (hf : f0 + fl ≤ l.length) (hs : s0 + dl ≤ l.length) (hi : i' ≤ fl) (hj : j' ≤ dl)
    (hfd : fl + dl ≤ l.length)
    (haj : aj + N ≤ W) (hd : d.nreg 1350 + l.length ≤ aj ∨ aj + N ≤ d.nreg 1350) :
    ∃ d' k, Exec P W bsMarks d d' k ∧ WordsBounded W d' ∧
      (∀ i < N, d'.nmem (aj + i) =
        if i ∈ ((l.drop f0).take fl).drop i' ++ (((l.drop s0).take dl).take j').reverse then 1
        else d.nmem (aj + i)) ∧
      (∀ a, (a < aj ∨ aj + N ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, r < 1360 ∨ 1388 ≤ r → d'.nreg r = d.nreg r) ∧ k ≤ 7 * l.length + 12 := by
  have hW := hL.lW
  have hw := hL.wb
  obtain ⟨c₁, k₁, e₁, hk₁, hw₁, g60, g61, gm₁, gq₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 1360 1380 1375, .addN 1361 1380 1381]) d c₁ k₁ ∧ k₁ = 2 ∧
      WordsBounded W c₁ ∧ c₁.nreg 1360 = f0 + i' ∧ c₁.nreg 1361 = f0 + fl ∧ c₁.nmem = d.nmem ∧
      ∀ r, r ≠ 1360 → r ≠ 1361 → c₁.nreg r = d.nreg r := by
    exec_block
    · rw [h80, h75]; omega
    · config_simp; rw [h80, h81]; omega
    · exact ⟨rfl, ‹_›, by config_simp; rw [h80, h75], by config_simp; rw [h80, h81], rfl,
        fun r h1 h2 => by simp [h1, h2]⟩
  have hL1 : LLay N W l c₁ := hL.congr hw₁ (fun r hr => gq₁ r (by omega) (by omega))
    (fun t _ => by rw [gm₁])
  obtain ⟨c₂, k₂, e₂, hw₂, hF₂, hfr₂, hq₂, hk₂⟩ := segMark_exec (P := P) hL1 g60 g61
    (by rw [gq₁ 1354 (by omega) (by omega)]; exact h54) (by omega) hf haj
    (by rw [gq₁ 1350 (by omega) (by omega)]; exact hd)
  obtain ⟨c₃, k₃, e₃, hk₃, hw₃, g60', g61', gm₃, gq₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN 1360 1382, .addN 1361 1382 1376]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
      WordsBounded W c₃ ∧ c₃.nreg 1360 = s0 ∧ c₃.nreg 1361 = s0 + j' ∧ c₃.nmem = c₂.nmem ∧
      ∀ r, r ≠ 1360 → r ≠ 1361 → c₃.nreg r = c₂.nreg r := by
    have r82 : c₂.nreg 1382 = s0 := by
      rw [hq₂ 1382 (by omega) (by omega) (by omega), gq₁ 1382 (by omega) (by omega), h82]
    have r76 : c₂.nreg 1376 = j' := by
      rw [hq₂ 1376 (by omega) (by omega) (by omega), gq₁ 1376 (by omega) (by omega), h76]
    exec_block
    · config_simp; rw [r82, r76]; omega
    · exact ⟨rfl, ‹_›, by config_simp; rw [r82], by config_simp; rw [r82, r76], rfl,
        fun r h1 h2 => by simp [h1, h2]⟩
  have hR3 : ∀ r, r < 1360 ∨ 1368 ≤ r → c₃.nreg r = d.nreg r := fun r hr => by
    rw [gq₃ r (by omega) (by omega), hq₂ r (by omega) (by omega) (by omega),
      gq₁ r (by omega) (by omega)]
  have hL3 : LLay N W l c₃ := hL.congr hw₃ (fun r hr => hR3 r (Or.inl hr))
    (fun t ht => by rw [gm₃, hfr₂ _ (by omega), gm₁])
  obtain ⟨c₄, k₄, e₄, hw₄, hF₄, hfr₄, hq₄, hk₄⟩ := segMark_exec (P := P) hL3 g60' g61'
    (by rw [hR3 1354 (by omega)]; exact h54) (by omega) (by omega) haj
    (by rw [hR3 1350 (by omega)]; exact hd)
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), hw₄, fun e he => ?_,
    fun a ha => by rw [hfr₄ a ha, gm₃, hfr₂ a ha, gm₁], fun r hr => by
      rw [hq₄ r (by omega) (by omega) (by omega), hR3 r (by omega)], by omega⟩
  rw [hF₄ e he, gm₃, hF₂ e he, gm₁]
  have e1 := mem_drop_seg l (e := e) hf hi
  have e2 := mem_take_seg l (e := e) hs hj
  simp only [List.mem_append, List.mem_reverse]
  by_cases h1 : ∃ t ∈ Ico s0 (s0 + j'), l.getD t 0 = e
  · rw [iteT h1, iteT (Or.inr (e2.2 h1))]
  · rw [iteF h1]
    by_cases h2 : ∃ t ∈ Ico (f0 + i') (f0 + fl), l.getD t 0 = e
    · rw [iteT h2, iteT (Or.inl (e1.2 h2))]
    · rw [iteF h2, iteF (fun h => h.elim (fun h => h2 (e1.1 h)) (fun h => h1 (e2.1 h)))]

theorem bsplit_cases (x y : ℕ → ℕ) (p q : ℕ) (l : List ℕ) {g : ℕ}
    (hg : gpre x (lsum x l) 0 l = l.take g) (hgl : g ≤ l.length) :
    bsplit x y p q l =
      if q < p * lsum y (l.take g) then
        bwalk x y (lsum x l) p q (g + (l.length - g)) (l.take g) (l.drop g) []
      else if q < p * lsum y (l.drop g) then
        bwalk x y (lsum x l) p q (g + (l.length - g)) (l.drop g) (l.take g) []
      else l.take g := by
  have hlen : (l.take g).length = g := by simp; omega
  simp only [bsplit, hg, hlen, List.length_drop]

theorem walkMark_exec {l : List ℕ} {d : Config} (hL : LLay N W l d)
    {ax ay aj X p q f0 fl s0 dl : ℕ}
    (x y : ℕ → ℕ) (h52 : d.nreg 1352 = ax) (h53 : d.nreg 1353 = ay) (h54 : d.nreg 1354 = aj)
    (hx : ∀ i < N, d.nmem (ax + i) = x i) (hy : ∀ i < N, d.nmem (ay + i) = y i)
    (hax : ax + N ≤ W) (hay : ay + N ≤ W) (haj : aj + N ≤ W)
    (hd : d.nreg 1350 + l.length ≤ aj ∨ aj + N ≤ d.nreg 1350)
    (h55 : d.nreg 1355 = p) (h56 : d.nreg 1356 = q)
    (h73 : d.nreg 1373 = X) (h80 : d.nreg 1380 = f0) (h81 : d.nreg 1381 = fl)
    (h82 : d.nreg 1382 = s0) (h83 : d.nreg 1383 = dl) (hf : f0 + fl ≤ l.length)
    (hs : s0 + dl ≤ l.length) (hfd : fl + dl ≤ l.length) {Y : ℕ}
    (hXF : lsum x ((l.drop f0).take fl) + lsum x ((l.drop s0).take dl) ≤ X)
    (hYF : lsum y ((l.drop f0).take fl) + lsum y ((l.drop s0).take dl) ≤ Y)
    (hXW : 2 * X ≤ W) (hYW : p * Y + Y ≤ W) (hW1 : 1 ≤ W)
    (h75 : d.nreg 1375 = 0) (h76 : d.nreg 1376 = 0) (h72 : d.nreg 1372 = 0)
    (h77 : d.nreg 1377 = lsum x ((l.drop f0).take fl))
    (h78 : d.nreg 1378 = lsum y ((l.drop f0).take fl)) :
    ∃ d' k, Exec P W (.seq bwLoop bsMarks) d d' k ∧ WordsBounded W d' ∧
      (∀ i < N, d'.nmem (aj + i) =
        if i ∈ bwalk x y X p q (fl + dl) ((l.drop f0).take fl) ((l.drop s0).take dl) [] then 1
        else d.nmem (aj + i)) ∧
      (∀ a, (a < aj ∨ aj + N ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, r < 1360 ∨ 1388 ≤ r → d'.nreg r = d.nreg r) ∧ k ≤ 37 * l.length + 44 := by
  have hW := hL.lW
  obtain ⟨c₁, k₁, e₁, hw₁, g75, g76, hi, hj, gm₁, gq₁, hk₁⟩ := bwLoop_exec (P := P) hL x y h52 h53
    hx hy hax hay h55 h56 h73 h80 h81 h82 h83 hf hs hXF hYF hXW hYW hW1 h75 h76 h72 h77 h78
  have hL₁ : LLay N W l c₁ := hL.congr hw₁ (fun r hr => gq₁ r (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) (fun t _ => by rw [gm₁])
  have K : ∀ r, 1379 ≤ r → c₁.nreg r = d.nreg r := fun r hr => gq₁ r (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hw₂, hF₂, hfr₂, hq₂, hk₂⟩ := bsMarks_exec (P := P) hL₁
    (by rw [gq₁ 1354 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]; exact h54)
    (by rw [K 1380 (by omega)]; exact h80) (by rw [K 1381 (by omega)]; exact h81)
    (by rw [K 1382 (by omega)]; exact h82) g75 g76 hf hs hi hj hfd haj
    (by rw [gq₁ 1350 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]; exact hd)
  have hb := bwalk_eq_mwalk x y X p q ((l.drop f0).take fl) ((l.drop s0).take dl) (fl + dl) 0 0
    (lsum x ((l.drop f0).take fl)) (lsum y ((l.drop f0).take fl)) (Nat.zero_le _) (Nat.zero_le _) (by rw [length_seg l hf, length_seg l hs]; omega)
    (by simp) (by simp)
  simp only [List.drop_zero, List.take_zero, List.reverse_nil] at hb
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, hw₂, fun i hi' => ?_, fun a ha => by rw [hfr₂ a ha, gm₁],
    fun r hr => by rw [hq₂ r hr, gq₁ r (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)], by omega⟩
  rw [hF₂ i hi', hb, gm₁]

set_option maxHeartbeats 2000000 in
theorem bsProg_exec {l : List ℕ} {d : Config} (hL : LLay N W l d) {ax ay aj p q : ℕ}
    (x y : ℕ → ℕ) (h52 : d.nreg 1352 = ax) (h53 : d.nreg 1353 = ay) (h54 : d.nreg 1354 = aj)
    (h55 : d.nreg 1355 = p) (h56 : d.nreg 1356 = q)
    (hx : ∀ i < N, d.nmem (ax + i) = x i) (hy : ∀ i < N, d.nmem (ay + i) = y i)
    (hax : ax + N ≤ W) (hay : ay + N ≤ W) (haj : aj + N ≤ W)
    (hd : d.nreg 1350 + l.length ≤ aj ∨ aj + N ≤ d.nreg 1350)
    (hXW : 2 * lsum x l ≤ W) (hYW : p * lsum y l + lsum y l ≤ W) (hW1 : 1 ≤ W) :
    ∃ d' k, Exec P W bsProg d d' k ∧ WordsBounded W d' ∧
      (∀ i < N, d'.nmem (aj + i) = if i ∈ bsplit x y p q l then 1 else d.nmem (aj + i)) ∧
      (∀ a, (a < aj ∨ aj + N ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, r < 1360 ∨ 1388 ≤ r → d'.nreg r = d.nreg r) ∧ k ≤ 90 * l.length + 150 := by
  have hW := hL.lW
  have hw := hL.wb
  set n := l.length with hn
  have hX : lsum x l = ∑ t ∈ Ico 0 n, x (l.getD t 0) := by
    rw [← lsum_seg x l (a := 0) le_rfl]; simp
  have hYsum : ∀ a b, b ≤ n → ∑ t ∈ Ico a b, y (l.getD t 0) ≤ lsum y l := fun a b hb => by
    rw [← lsum_seg y l hb]
    have h1 := lsum_take_add_drop y (l.drop a) (b - a)
    have h2 := lsum_take_add_drop y l a
    omega
  -- the total
  obtain ⟨c₁, k₁, e₁, hk₁, hw₁, g60, g61, g62, gm₁, gq₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.constN 1360 0, .copyN 1361 1351, .copyN 1362 1352]) d c₁ k₁ ∧ k₁ = 3 ∧
      WordsBounded W c₁ ∧ c₁.nreg 1360 = 0 ∧ c₁.nreg 1361 = n ∧ c₁.nreg 1362 = ax ∧
      c₁.nmem = d.nmem ∧ ∀ r, r < 1360 ∨ 1363 ≤ r → c₁.nreg r = d.nreg r := by
    exec_block
    · omega
    · exact ⟨rfl, ‹_›, by config_simp, by config_simp; exact hL.len, by config_simp; exact h52,
        rfl, fun r hr => by simp [show r ≠ 1360 by omega, show r ≠ 1361 by omega,
          show r ≠ 1362 by omega]⟩
  have hL₁ : LLay N W l c₁ := hL.congr hw₁ (fun r hr => gq₁ r (Or.inl hr)) (fun t _ => by rw [gm₁])
  obtain ⟨c₂, k₂, e₂, hw₂, g63, gm₂, gq₂, hk₂⟩ := segSum_exec (P := P) hL₁ x g60 g61 g62
    (Nat.zero_le _) le_rfl (fun i hi => by rw [gm₁]; exact hx i hi) hax (by rw [← hX]; omega)
  rw [← hX] at g63
  obtain ⟨c₃, k₃, e₃, hk₃, hw₃, g73, g70, g71, g72, gm₃, gq₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN 1373 1363, .constN 1370 0, .constN 1371 0, .constN 1372 0]) c₂ c₃ k₃ ∧
      k₃ = 4 ∧ WordsBounded W c₃ ∧ c₃.nreg 1373 = lsum x l ∧ c₃.nreg 1370 = 0 ∧
      c₃.nreg 1371 = 0 ∧ c₃.nreg 1372 = 0 ∧ c₃.nmem = c₂.nmem ∧
      ∀ r, r ≠ 1370 → r ≠ 1371 → r ≠ 1372 → r ≠ 1373 → c₃.nreg r = c₂.nreg r := by
    exec_block
    · omega
    · omega
    · omega
    · exact ⟨rfl, ‹_›, by config_simp; exact g63, by config_simp, by config_simp, by config_simp,
        rfl, fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4]⟩
  have R3 : ∀ r, r < 1360 ∨ 1374 ≤ r → c₃.nreg r = d.nreg r := fun r hr => by
    rw [gq₃ r (by omega) (by omega) (by omega) (by omega),
      gq₂ r (by omega) (by omega) (by omega) (by omega) (by omega), gq₁ r (by omega)]
  have hL₃ : LLay N W l c₃ := hL.congr hw₃ (fun r hr => R3 r (Or.inl hr))
    (fun t _ => by rw [gm₃, gm₂, gm₁])
  -- the prefix
  obtain ⟨c₄, k₄, e₄, hw₄, hg, hgl, g71', gm₄, gq₄, hk₄⟩ := gpLoop_exec (P := P) hL₃ x
    (by rw [R3 1352 (by omega)]; exact h52) (fun i hi => by rw [gm₃, gm₂, gm₁]; exact hx i hi)
    hax g70 g71 g72 g73 rfl hXW hW1
  set g := c₄.nreg 1370 with hgdef
  have R4 : ∀ r, r < 1360 ∨ 1375 ≤ r → c₄.nreg r = d.nreg r := fun r hr => by
    rw [gq₄ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      R3 r (by omega)]
  -- the `y`-measures of the two parts
  obtain ⟨c₅, k₅, e₅, hk₅, hw₅, g60₅, g61₅, g62₅, gm₅, gq₅⟩ : ∃ c₅ k₅, Exec P W
      (block [.constN 1360 0, .copyN 1361 1370, .copyN 1362 1353]) c₄ c₅ k₅ ∧ k₅ = 3 ∧
      WordsBounded W c₅ ∧ c₅.nreg 1360 = 0 ∧ c₅.nreg 1361 = g ∧ c₅.nreg 1362 = ay ∧
      c₅.nmem = c₄.nmem ∧ ∀ r, r ≠ 1360 → r ≠ 1361 → r ≠ 1362 → c₅.nreg r = c₄.nreg r := by
    exec_block
    · omega
    · exact ⟨rfl, ‹_›, by config_simp, by config_simp; exact hgdef.symm,
        by config_simp; rw [R4 1353 (by omega), h53], rfl, fun r h1 h2 h3 => by simp [h1, h2, h3]⟩
  have hL₅ : LLay N W l c₅ := hL.congr hw₅ (fun r hr => by
      rw [gq₅ r (by omega) (by omega) (by omega), R4 r (Or.inl hr)])
    (fun t _ => by rw [gm₅, gm₄, gm₃, gm₂, gm₁])
  have hy5 : ∀ i < N, c₅.nmem (ay + i) = y i := fun i hi => by
    rw [gm₅, gm₄, gm₃, gm₂, gm₁]; exact hy i hi
  obtain ⟨c₆, k₆, e₆, hw₆, g63₆, gm₆, gq₆, hk₆⟩ := segSum_exec (P := P) hL₅ y g60₅ g61₅ g62₅
    (Nat.zero_le _) hgl hy5 hay (by have := hYsum 0 g hgl; omega)
  obtain ⟨c₇, k₇, e₇, hk₇, hw₇, g84, g60₇, g61₇, gm₇, gq₇⟩ : ∃ c₇ k₇, Exec P W
      (block [.copyN 1384 1363, .copyN 1360 1370, .copyN 1361 1351]) c₆ c₇ k₇ ∧ k₇ = 3 ∧
      WordsBounded W c₇ ∧ c₇.nreg 1384 = ∑ t ∈ Ico 0 g, y (l.getD t 0) ∧ c₇.nreg 1360 = g ∧
      c₇.nreg 1361 = n ∧ c₇.nmem = c₆.nmem ∧
      ∀ r, r ≠ 1360 → r ≠ 1361 → r ≠ 1384 → c₇.nreg r = c₆.nreg r := by
    exec_block
    exact ⟨rfl, ‹_›, by config_simp; exact g63₆,
      by config_simp; rw [gq₆ 1370 (by omega) (by omega) (by omega) (by omega) (by omega),
        gq₅ 1370 (by omega) (by omega) (by omega)],
      by config_simp; rw [gq₆ 1351 (by omega) (by omega) (by omega) (by omega) (by omega),
        gq₅ 1351 (by omega) (by omega) (by omega), R4 1351 (by omega)]; exact hL.len, rfl,
      fun r h1 h2 h3 => by simp [h1, h2, h3]⟩
  have R7 : ∀ r, r < 1360 ∨ 1385 ≤ r → c₇.nreg r = d.nreg r := fun r hr => by
    rw [gq₇ r (by omega) (by omega) (by omega),
      gq₆ r (by omega) (by omega) (by omega) (by omega) (by omega),
      gq₅ r (by omega) (by omega) (by omega), R4 r (by omega)]
  have hL₇ : LLay N W l c₇ := hL.congr hw₇ (fun r hr => R7 r (Or.inl hr))
    (fun t _ => by rw [gm₇, gm₆, gm₅, gm₄, gm₃, gm₂, gm₁])
  obtain ⟨c₈, k₈, e₈, hw₈, g63₈, gm₈, gq₈, hk₈⟩ := segSum_exec (P := P) hL₇ y g60₇ g61₇
    (by rw [gq₇ 1362 (by omega) (by omega) (by omega),
      gq₆ 1362 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact g62₅)
    hgl le_rfl (fun i hi => by rw [gm₇, gm₆]; exact hy5 i hi) hay
    (by have := hYsum g n le_rfl; omega)
  have hly1 : ∑ t ∈ Ico 0 g, y (l.getD t 0) = lsum y (l.take g) := by
    rw [← lsum_seg y l hgl]; simp
  have hly2 : ∑ t ∈ Ico g n, y (l.getD t 0) = lsum y (l.drop g) := by
    rw [← lsum_seg y l le_rfl, List.take_of_length_le (by simp)]
  rw [hly1] at g84
  rw [hly2] at g63₈
  have hYl := lsum_take_add_drop y l g
  have hXl := lsum_take_add_drop x l g
  have hp1 : p * lsum y (l.take g) ≤ p * lsum y l := Nat.mul_le_mul_left _ (by omega)
  have hp2 : p * lsum y (l.drop g) ≤ p * lsum y l := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨c₉, k₉, e₉, hk₉, hw₉, g85, g86, g87, gm₉, gq₉⟩ : ∃ c₉ k₉, Exec P W
      (block [.copyN 1385 1363, .mulN 1386 1355 1384, .mulN 1387 1355 1385]) c₈ c₉ k₉ ∧
      k₉ = 3 ∧ WordsBounded W c₉ ∧ c₉.nreg 1385 = lsum y (l.drop g) ∧
      c₉.nreg 1386 = p * lsum y (l.take g) ∧ c₉.nreg 1387 = p * lsum y (l.drop g) ∧
      c₉.nmem = c₈.nmem ∧ ∀ r, r ≠ 1385 → r ≠ 1386 → r ≠ 1387 → c₉.nreg r = c₈.nreg r := by
    have r55 : c₈.nreg 1355 = p := by
      rw [gq₈ 1355 (by omega) (by omega) (by omega) (by omega) (by omega), R7 1355 (by omega),
        h55]
    have r84 : c₈.nreg 1384 = lsum y (l.take g) := by
      rw [gq₈ 1384 (by omega) (by omega) (by omega) (by omega) (by omega), g84]
    exec_block
    · config_simp; rw [r55, r84]; omega
    · config_simp; rw [r55, g63₈]; omega
    · exact ⟨rfl, ‹_›, by config_simp; exact g63₈, by config_simp; rw [r55, r84],
        by config_simp; rw [r55, g63₈], rfl, fun r h1 h2 h3 => by simp [h1, h2, h3]⟩
  have R9 : ∀ r, r < 1360 ∨ 1388 ≤ r → c₉.nreg r = d.nreg r := fun r hr => by
    rw [gq₉ r (by omega) (by omega) (by omega),
      gq₈ r (by omega) (by omega) (by omega) (by omega) (by omega), R7 r (by omega)]
  have hm9 : c₉.nmem = d.nmem := by rw [gm₉, gm₈, gm₇, gm₆, gm₅, gm₄, gm₃, gm₂, gm₁]
  have hL₉ : LLay N W l c₉ := hL.congr hw₉ (fun r hr => R9 r (Or.inl hr))
    (fun t _ => by rw [hm9])
  have r56 : c₉.nreg 1356 = q := by rw [R9 1356 (by omega), h56]
  have hcases := bsplit_cases x y p q l hg hgl
  have r71 : c₉.nreg 1371 = lsum x (l.take g) := by
    rw [gq₉ 1371 (by omega) (by omega) (by omega),
      gq₈ 1371 (by omega) (by omega) (by omega) (by omega) (by omega),
      gq₇ 1371 (by omega) (by omega) (by omega),
      gq₆ 1371 (by omega) (by omega) (by omega) (by omega) (by omega),
      gq₅ 1371 (by omega) (by omega) (by omega), g71']
  have r70 : c₉.nreg 1370 = g := by
    rw [gq₉ 1370 (by omega) (by omega) (by omega),
      gq₈ 1370 (by omega) (by omega) (by omega) (by omega) (by omega),
      gq₇ 1370 (by omega) (by omega) (by omega),
      gq₆ 1370 (by omega) (by omega) (by omega) (by omega) (by omega),
      gq₅ 1370 (by omega) (by omega) (by omega)]
  have r73 : c₉.nreg 1373 = lsum x l := by
    rw [gq₉ 1373 (by omega) (by omega) (by omega),
      gq₈ 1373 (by omega) (by omega) (by omega) (by omega) (by omega),
      gq₇ 1373 (by omega) (by omega) (by omega),
      gq₆ 1373 (by omega) (by omega) (by omega) (by omega) (by omega),
      gq₅ 1373 (by omega) (by omega) (by omega),
      gq₄ 1373 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g73]
  have r84 : c₉.nreg 1384 = lsum y (l.take g) := by
    rw [gq₉ 1384 (by omega) (by omega) (by omega),
      gq₈ 1384 (by omega) (by omega) (by omega) (by omega) (by omega), g84]
  have hT : (l.drop 0).take g = l.take g := by rw [List.drop_zero]
  have hD : (l.drop g).take (n - g) = l.drop g := List.take_of_length_le (by simp; omega)
  have hDx : ∀ (f : ℕ → ℕ), lsum f (l.take g) + lsum f (l.drop g) = lsum f l :=
    fun f => lsum_take_add_drop f l g
  have hx9 : ∀ i < N, c₉.nmem (ax + i) = x i := fun i hi => by rw [hm9]; exact hx i hi
  have hy9 : ∀ i < N, c₉.nmem (ay + i) = y i := fun i hi => by rw [hm9]; exact hy i hi
  have hpre : ∀ k₀ : ℕ, k₀ ≤ 66 * n + 66 → ∀ (s : Stmt) (c' : Config) (k' : ℕ),
      Exec P W s c₉ c' k' →
      Exec P W (.seq (block [.constN 1360 0, .copyN 1361 1351, .copyN 1362 1352])
        (.seq segSum (.seq (block [.copyN 1373 1363, .constN 1370 0, .constN 1371 0,
          .constN 1372 0]) (.seq gpLoop (.seq (block [.constN 1360 0, .copyN 1361 1370,
          .copyN 1362 1353]) (.seq segSum (.seq (block [.copyN 1384 1363, .copyN 1360 1370,
          .copyN 1361 1351]) (.seq segSum (.seq (block [.copyN 1385 1363, .mulN 1386 1355 1384,
          .mulN 1387 1355 1385]) s)))))))))
        d c' (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + (k₈ + (k₉ + k'))))))))) :=
    fun _ _ s c' k' e => .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇
      (.seq e₈ (.seq e₉ e))))))))
  have hk9 : k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + (k₈ + k₉))))))) ≤ 37 * n + 50 := by
    omega
  by_cases h1 : q < p * lsum y (l.take g)
  · obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, hw₁₀, q₁₀⟩ : ∃ c₁₀ k₁₀, Exec P W (block [.constN 1380 0,
        .copyN 1381 1370, .copyN 1382 1370, .subN 1383 1351 1370, .constN 1375 0,
        .constN 1376 0, .copyN 1377 1371, .copyN 1378 1384, .constN 1372 0]) c₉ c₁₀ k₁₀ ∧
        k₁₀ = 9 ∧ WordsBounded W c₁₀ ∧
        (c₁₀.nreg 1380 = 0 ∧ c₁₀.nreg 1381 = g ∧ c₁₀.nreg 1382 = g ∧ c₁₀.nreg 1383 = n - g ∧
        c₁₀.nreg 1375 = 0 ∧ c₁₀.nreg 1376 = 0 ∧ c₁₀.nreg 1377 = lsum x (l.take g) ∧
        c₁₀.nreg 1378 = lsum y (l.take g) ∧ c₁₀.nreg 1372 = 0 ∧ c₁₀.nmem = c₉.nmem ∧
        ∀ r, r < 1372 ∨ r = 1373 ∨ r = 1374 ∨ (1379 ≤ r ∧ r ≠ 1380 ∧ r ≠ 1381 ∧ r ≠ 1382 ∧
          r ≠ 1383) → c₁₀.nreg r = c₉.nreg r) := by
      exec_block
      · omega
      · omega
      · omega
      · omega
      · refine ⟨rfl, ‹_›, by config_simp, by config_simp; exact r70, by config_simp; exact r70,
          by config_simp; rw [R9 1351 (by omega), hL.len, r70], by config_simp, by config_simp,
          by config_simp; exact r71, by config_simp; exact r84, by config_simp, rfl,
          fun r hr => ?_⟩
        simp only [Config.nreg_mk, upd_apply]
        split_ifs <;> first | rfl | omega
    obtain ⟨h80, h81, h82, h83, h75, h76, h77, h78, h72, hm10, hq10⟩ := q₁₀
    have hL₁₀ : LLay N W l c₁₀ := hL.congr hw₁₀ (fun r hr => by rw [hq10 r (by omega),
      R9 r (Or.inl hr)]) (fun t _ => by rw [hm10, hm9])
    obtain ⟨c', k', e', hw', hF', hfr', hq', hk'⟩ := walkMark_exec (P := P) (X := lsum x l)
      (p := p) (q := q) hL₁₀ x y
      (by rw [hq10 1352 (by omega), R9 1352 (by omega)]; exact h52)
      (by rw [hq10 1353 (by omega), R9 1353 (by omega)]; exact h53)
      (by rw [hq10 1354 (by omega), R9 1354 (by omega)]; exact h54)
      (fun i hi => by rw [hm10]; exact hx9 i hi) (fun i hi => by rw [hm10]; exact hy9 i hi)
      hax hay haj (by rw [hq10 1350 (by omega), R9 1350 (by omega)]; exact hd)
      (by rw [hq10 1355 (by omega), R9 1355 (by omega)]; exact h55)
      (by rw [hq10 1356 (by omega)]; exact r56) (by rw [hq10 1373 (by omega)]; exact r73)
      h80 h81 h82 h83 (by omega) (by omega) (by omega) (Y := lsum y l)
      (by rw [hT, hD, hDx]) (by rw [hT, hD, hDx]) hXW hYW hW1 h75 h76 h72
      (by rw [hT]; exact h77) (by rw [hT]; exact h78)
    refine ⟨c', _, hpre _ le_rfl _ c' _ (.ifLtN_true (by rw [r56, g86]; exact h1)
      (.seq e₁₀ e')), hw', fun i hi => ?_, fun a ha => by rw [hfr' a ha, hm10, hm9],
      fun r hr => by rw [hq' r hr, hq10 r (by omega), R9 r hr], by omega⟩
    rw [hF' i hi, hcases, iteT h1, hT, hD, show g + (n - g) = g + (n - g) from rfl, hm10, hm9]
  by_cases h2 : q < p * lsum y (l.drop g)
  · obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, hw₁₀, q₁₀⟩ : ∃ c₁₀ k₁₀, Exec P W (block [.copyN 1380 1370,
        .subN 1381 1351 1370, .constN 1382 0, .copyN 1383 1370, .constN 1375 0, .constN 1376 0,
        .subN 1377 1373 1371, .copyN 1378 1385, .constN 1372 0]) c₉ c₁₀ k₁₀ ∧
        k₁₀ = 9 ∧ WordsBounded W c₁₀ ∧
        (c₁₀.nreg 1380 = g ∧ c₁₀.nreg 1381 = n - g ∧ c₁₀.nreg 1382 = 0 ∧ c₁₀.nreg 1383 = g ∧
        c₁₀.nreg 1375 = 0 ∧ c₁₀.nreg 1376 = 0 ∧ c₁₀.nreg 1377 = lsum x l - lsum x (l.take g) ∧
        c₁₀.nreg 1378 = lsum y (l.drop g) ∧ c₁₀.nreg 1372 = 0 ∧ c₁₀.nmem = c₉.nmem ∧
        ∀ r, r < 1372 ∨ r = 1373 ∨ r = 1374 ∨ (1379 ≤ r ∧ r ≠ 1380 ∧ r ≠ 1381 ∧ r ≠ 1382 ∧
          r ≠ 1383) → c₁₀.nreg r = c₉.nreg r) := by
      exec_block
      · omega
      · omega
      · omega
      · omega
      · refine ⟨rfl, ‹_›, by config_simp; exact r70,
          by config_simp; rw [R9 1351 (by omega), hL.len, r70], by config_simp,
          by config_simp; exact r70, by config_simp, by config_simp,
          by config_simp; rw [r73, r71], by config_simp; exact g85, by config_simp, rfl,
          fun r hr => ?_⟩
        simp only [Config.nreg_mk, upd_apply]
        split_ifs <;> first | rfl | omega
    obtain ⟨h80, h81, h82, h83, h75, h76, h77, h78, h72, hm10, hq10⟩ := q₁₀
    have hL₁₀ : LLay N W l c₁₀ := hL.congr hw₁₀ (fun r hr => by rw [hq10 r (by omega),
      R9 r (Or.inl hr)]) (fun t _ => by rw [hm10, hm9])
    have hsx : lsum x l - lsum x (l.take g) = lsum x (l.drop g) := by
      have := hDx x; omega
    obtain ⟨c', k', e', hw', hF', hfr', hq', hk'⟩ := walkMark_exec (P := P) (X := lsum x l)
      (p := p) (q := q) hL₁₀ x y
      (by rw [hq10 1352 (by omega), R9 1352 (by omega)]; exact h52)
      (by rw [hq10 1353 (by omega), R9 1353 (by omega)]; exact h53)
      (by rw [hq10 1354 (by omega), R9 1354 (by omega)]; exact h54)
      (fun i hi => by rw [hm10]; exact hx9 i hi) (fun i hi => by rw [hm10]; exact hy9 i hi)
      hax hay haj (by rw [hq10 1350 (by omega), R9 1350 (by omega)]; exact hd)
      (by rw [hq10 1355 (by omega), R9 1355 (by omega)]; exact h55)
      (by rw [hq10 1356 (by omega)]; exact r56) (by rw [hq10 1373 (by omega)]; exact r73)
      h80 h81 h82 h83 (by omega) (by omega) (by omega) (Y := lsum y l)
      (by rw [hT, hD, Nat.add_comm, hDx]) (by rw [hT, hD, Nat.add_comm, hDx]) hXW hYW hW1
      h75 h76 h72 (by rw [hD, ← hsx]; exact h77) (by rw [hD]; exact h78)
    refine ⟨c', _, hpre _ le_rfl _ c' _ (.ifLtN_false (by rw [r56, g86]; exact h1)
      (.ifLtN_true (by rw [r56, g87]; exact h2) (.seq e₁₀ e'))), hw', fun i hi => ?_,
      fun a ha => by rw [hfr' a ha, hm10, hm9],
      fun r hr => by rw [hq' r hr, hq10 r (by omega), R9 r hr], by omega⟩
    rw [hF' i hi, hcases, iteF h1, iteT h2, hT, hD, Nat.add_comm (n - g) g, hm10, hm9]
  · obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, hw₁₀, g60', g61', hm10, hq10⟩ : ∃ c₁₀ k₁₀, Exec P W
        (block [.constN 1360 0, .copyN 1361 1370]) c₉ c₁₀ k₁₀ ∧ k₁₀ = 2 ∧ WordsBounded W c₁₀ ∧
        c₁₀.nreg 1360 = 0 ∧ c₁₀.nreg 1361 = g ∧ c₁₀.nmem = c₉.nmem ∧
        ∀ r, r ≠ 1360 → r ≠ 1361 → c₁₀.nreg r = c₉.nreg r := by
      exec_block
      · omega
      · exact ⟨rfl, ‹_›, by config_simp, by config_simp; exact r70, rfl,
          fun r h1 h2 => by simp [h1, h2]⟩
    have hL₁₀ : LLay N W l c₁₀ := hL.congr hw₁₀ (fun r hr => by rw [hq10 r (by omega) (by omega),
      R9 r (Or.inl hr)]) (fun t _ => by rw [hm10, hm9])
    obtain ⟨c', k', e', hw', hF', hfr', hq', hk'⟩ := segMark_exec (P := P) hL₁₀ g60' g61'
      (by rw [hq10 1354 (by omega) (by omega), R9 1354 (by omega)]; exact h54) (Nat.zero_le _)
      hgl haj (by rw [hq10 1350 (by omega) (by omega), R9 1350 (by omega)]; exact hd)
    refine ⟨c', _, hpre _ le_rfl _ c' _ (.ifLtN_false (by rw [r56, g86]; exact h1)
      (.ifLtN_false (by rw [r56, g87]; exact h2) (.seq e₁₀ e'))), hw', fun i hi => ?_,
      fun a ha => by rw [hfr' a ha, hm10, hm9],
      fun r hr => by rw [hq' r (by omega) (by omega) (by omega), hq10 r (by omega) (by omega),
        R9 r hr], by omega⟩
    rw [hF' i hi, hcases, iteF h1, iteF h2, hm10, hm9]
    congr 1
    have := mem_seg l (a := 0) (b := g) (e := i) hgl
    simp only [List.drop_zero, Nat.sub_zero] at this
    rw [this]
    simp only [mem_Ico, eq_iff_iff]
    constructor
    · rintro ⟨t, ht, h⟩; exact ⟨t, Nat.zero_le _, ht.2, h⟩
    · rintro ⟨t, -, ht, h⟩; exact ⟨t, ⟨Nat.zero_le _, ht⟩, h⟩

end Piece

end PlanarSeparator
