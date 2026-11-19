module

public import PlanarFlow.BKMNW.NcHf

/-!
# The merge sort of `hfP` on the machine

* `segL mem b n` (the words `mem (b + t)`, `t < n`, as a list) and its lemmas;
* **`mergeLoop_exec`**: the loop of `mstep` writes `List.merge` of the two blocks
  (`16 (hi - lo) + 2` steps);
* **`hfBlk_exec`**: one block of a pass; **`hfPass_exec`**: one pass writes `mpass w` of the
  source into the target (`30 m + 4` steps);
* **`hfSort_exec`**: the merge sort leaves `msortW m 1 L` in the buffer `r9760`
  (`(30 m + 10) lg m + 3` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### Arrays as lists -/

/-- The words `mem (b + t)`, `t < n`. -/
def segL (mem : ℕ → ℕ) (b n : ℕ) : List ℕ := (List.range n).map fun t => mem (b + t)

lemma segL_length (mem : ℕ → ℕ) (b n : ℕ) : (segL mem b n).length = n := by simp [segL]

lemma segL_zero (mem : ℕ → ℕ) (b : ℕ) : segL mem b 0 = [] := by simp [segL]

lemma segL_succ_right (mem : ℕ → ℕ) (b n : ℕ) :
    segL mem b (n + 1) = segL mem b n ++ [mem (b + n)] := by
  simp [segL, List.range_succ]

lemma segL_succ_left (mem : ℕ → ℕ) (b n : ℕ) :
    segL mem b (n + 1) = mem b :: segL mem (b + 1) n := by
  simp only [segL, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro t _; simp only [Function.comp_apply]; congr 1; omega

lemma segL_add (mem : ℕ → ℕ) (b n₁ : ℕ) : ∀ n₂,
    segL mem b (n₁ + n₂) = segL mem b n₁ ++ segL mem (b + n₁) n₂
  | 0 => by simp [segL_zero]
  | n₂ + 1 => by
    rw [← Nat.add_assoc, segL_succ_right, segL_add mem b n₁ n₂, segL_succ_right,
      List.append_assoc]
    simp only [Nat.add_assoc]

lemma segL_congr {mem mem' : ℕ → ℕ} {b n : ℕ} (h : ∀ t < n, mem (b + t) = mem' (b + t)) :
    segL mem b n = segL mem' b n := by
  unfold segL
  apply List.map_congr_left
  intro t ht; exact h t (List.mem_range.1 ht)

lemma segL_drop (mem : ℕ → ℕ) (b n k : ℕ) : (segL mem b n).drop k = segL mem (b + k) (n - k) := by
  rcases le_or_gt k n with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [segL_add, List.drop_left' (segL_length _ _ _)]
    congr 1; omega
  · rw [List.drop_eq_nil_of_le (by rw [segL_length]; omega), show n - k = 0 by omega, segL_zero]

lemma segL_take (mem : ℕ → ℕ) (b n k : ℕ) : (segL mem b n).take k = segL mem b (min k n) := by
  rcases le_or_gt k n with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [segL_add, List.take_left' (segL_length _ _ _)]
    congr 1; omega
  · rw [List.take_of_length_le (by rw [segL_length]; omega)]
    congr 1; omega

/-! ### The merge loop -/

/-- The invariant of the merge loop. -/
def HfMInv (c₀ : Config) (S T lo mid hi : ℕ) (c : Config) : Prop :=
  ∃ p q, c.nreg 9770 = p ∧ c.nreg 9771 = q ∧ lo ≤ p ∧ p ≤ mid ∧ mid ≤ q ∧ q ≤ hi ∧
    c.nreg 9772 = p + q - mid ∧
    (∀ r, r ≠ 9770 → r ≠ 9771 → r ≠ 9772 → r ≠ 9773 → r ≠ 9774 → r ≠ 9775 →
      c.nreg r = c₀.nreg r) ∧
    (∀ a, (a < T + lo ∨ T + (p + q - mid) ≤ a) → c.nmem a = c₀.nmem a) ∧
    segL c.nmem (T + lo) (p + q - mid - lo) ++
        List.merge (segL c₀.nmem (S + p) (mid - p)) (segL c₀.nmem (S + q) (hi - q)) =
      List.merge (segL c₀.nmem (S + lo) (mid - lo)) (segL c₀.nmem (S + mid) (hi - mid)) ∧
    c.rreg = c₀.rreg ∧ c.rmem = c₀.rmem ∧ c.output = c₀.output ∧ WordsBounded W c

/-- **The merge loop.** -/
theorem mergeLoop_exec (c₀ : Config) (hc : WordsBounded W c₀) {S T lo mid hi : ℕ}
    (r60 : c₀.nreg 9760 = S) (r61 : c₀.nreg 9761 = T) (r64 : c₀.nreg 9764 = 1)
    (r68 : c₀.nreg 9768 = mid) (r69 : c₀.nreg 9769 = hi)
    (r70 : c₀.nreg 9770 = lo) (r71 : c₀.nreg 9771 = mid) (r72 : c₀.nreg 9772 = lo)
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) (hdj : S + hi ≤ T + lo ∨ T + hi ≤ S + lo)
    (w1 : S + hi ≤ W) (w2 : T + hi ≤ W) (w3 : hi + 1 ≤ W) :
    ∃ c' k, Exec P W (.whileLtN 9772 9769 mstep) c₀ c' k ∧ k ≤ 16 * (hi - lo) + 2 ∧
      segL c'.nmem (T + lo) (hi - lo) =
        List.merge (segL c₀.nmem (S + lo) (mid - lo)) (segL c₀.nmem (S + mid) (hi - mid)) ∧
      (∀ a, (a < T + lo ∨ T + hi ≤ a) → c'.nmem a = c₀.nmem a) ∧
      (∀ r, r ≠ 9770 → r ≠ 9771 → r ≠ 9772 → r ≠ 9773 → r ≠ 9774 → r ≠ 9775 →
        c'.nreg r = c₀.nreg r) ∧
      c'.rreg = c₀.rreg ∧ c'.rmem = c₀.rmem ∧ c'.output = c₀.output := by
  have hI0 : HfMInv (W := W) c₀ S T lo mid hi c₀ :=
    ⟨lo, mid, r70, r71, le_rfl, h1, le_rfl, h2, by rw [r72]; omega, fun _ _ _ _ _ _ _ => rfl,
      fun _ _ => rfl, by rw [show lo + mid - mid - lo = 0 by omega, segL_zero, List.nil_append],
      rfl, rfl, rfl, hc⟩
  obtain ⟨c', k, ex, hI, hn, hk⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 9772)
    (b := 9769) (body := mstep) (HfMInv (W := W) c₀ S T lo mid hi)
    (fun c => 16 * (hi - c.nreg 9772)) (fun c h => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hw⟩ := h; exact hw)
    (fun c ⟨p, q, e70, e71, hlp, hpm, hmq, hqh, e72, hreg, hmem, hseg, er, erm, eo, hw⟩ hlt => by
      have q60 : c.nreg 9760 = S := by rw [hreg _ (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), r60]
      have q61 : c.nreg 9761 = T := by rw [hreg _ (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), r61]
      have q64 : c.nreg 9764 = 1 := by rw [hreg _ (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), r64]
      have q68 : c.nreg 9768 = mid := by rw [hreg _ (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), r68]
      have q69 : c.nreg 9769 = hi := by rw [hreg _ (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), r69]
      rw [e72, q69] at hlt
      have hpq : p < mid ∨ q < hi := by omega
      -- the source is not written
      have hS : ∀ x, lo ≤ x → x < hi → c.nmem (S + x) = c₀.nmem (S + x) := fun x hx1 hx2 =>
        hmem _ (by omega)
      obtain ⟨c₁, k₁, e₁, hk₁, o₁, g₁, rr₁, rm₁, ou₁, tP, tQ⟩ := mstep_exec (P := P) c hw q60 q61
        q64 q68 q69 e70 e71 e72 hpq (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)
      have hpot : ∀ o', o' = p + q - mid + 1 →
          16 * (hi - o') + k₁ + 2 ≤ 16 * (hi - (p + q - mid)) := by
        intro o' ho'; subst ho'; omega
      by_cases ht : mTakesP c.nmem S p q mid hi
      · obtain ⟨m₁, a₁, b₁⟩ := tP ht
        have hpm' : p < mid := ht.1
        have hpS := hS p hlp (by omega)
        refine ⟨c₁, k₁, e₁, ⟨p + 1, q, a₁, b₁, by omega, by omega, hmq, hqh, by rw [o₁]; omega,
          fun r h1 h2 h3 h4 h5 h6 => by rw [g₁ r h1 h2 h3 h4 h5 h6, hreg r h1 h2 h3 h4 h5 h6],
          fun a ha => ?_, ?_, by rw [rr₁, er], by rw [rm₁, erm], by rw [ou₁, eo], e₁.wb_right⟩,
          by rw [o₁, e72]; exact hpot _ rfl⟩
        · rw [m₁, upd_apply, iteF (by omega)]; exact hmem a (by omega)
        · rw [← hseg, show p + 1 + q - mid - lo = (p + q - mid - lo) + 1 by omega,
            segL_succ_right, m₁, upd_apply, iteT (by omega), hpS,
            segL_congr (mem' := c.nmem) (fun t ht => by rw [upd_apply, iteF (by omega)]),
            List.append_assoc]
          congr 1
          rw [show mid - p = (mid - (p + 1)) + 1 by omega, segL_succ_left,
            show S + p + 1 = S + (p + 1) by omega]
          rcases Nat.lt_or_ge q hi with hq | hq
          · rw [show hi - q = (hi - (q + 1)) + 1 by omega, segL_succ_left (b := S + q)]
            have hle : c₀.nmem (S + p) ≤ c₀.nmem (S + q) := by
              unfold mTakesP at ht; rw [hS q (by omega) hq] at ht; omega
            rw [List.cons_merge_cons_pos _ _ _ (by simpa using hle)]
            rfl
          · rw [show hi - q = 0 by omega, segL_zero, List.merge_right, List.merge_right]
            rfl
      · obtain ⟨m₁, a₁, b₁⟩ := tQ ht
        have hqh' : q < hi := by unfold mTakesP at ht; omega
        have hqS := hS q (by omega) hqh'
        refine ⟨c₁, k₁, e₁, ⟨p, q + 1, a₁, b₁, hlp, hpm, by omega, by omega, by rw [o₁]; omega,
          fun r h1 h2 h3 h4 h5 h6 => by rw [g₁ r h1 h2 h3 h4 h5 h6, hreg r h1 h2 h3 h4 h5 h6],
          fun a ha => ?_, ?_, by rw [rr₁, er], by rw [rm₁, erm], by rw [ou₁, eo], e₁.wb_right⟩,
          by rw [o₁, e72]; exact hpot _ rfl⟩
        · rw [m₁, upd_apply, iteF (by omega)]; exact hmem a (by omega)
        · rw [← hseg, show p + (q + 1) - mid - lo = (p + q - mid - lo) + 1 by omega,
            segL_succ_right, m₁, upd_apply, iteT (by omega), hqS,
            segL_congr (mem' := c.nmem) (fun t ht => by rw [upd_apply, iteF (by omega)]),
            List.append_assoc]
          congr 1
          rw [show hi - q = (hi - (q + 1)) + 1 by omega, segL_succ_left (b := S + q),
            show S + q + 1 = S + (q + 1) by omega]
          rcases Nat.lt_or_ge p mid with hp | hp
          · rw [show mid - p = (mid - (p + 1)) + 1 by omega, segL_succ_left (b := S + p)]
            have hlt' : c₀.nmem (S + q) < c₀.nmem (S + p) := by
              unfold mTakesP at ht; rw [hS q (by omega) hqh', hS p hlp (by omega)] at ht; omega
            rw [List.cons_merge_cons_neg _ _ _ (by simpa using hlt')]
            rfl
          · rw [show mid - p = 0 by omega, segL_zero, List.nil_merge, List.nil_merge]
            rfl)
    hI0
  obtain ⟨p, q, e70, e71, hlp, hpm, hmq, hqh, e72, hreg, hmem, hseg, er, erm, eo, hw⟩ := hI
  have q69 : c'.nreg 9769 = hi := by
    rw [hreg _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r69]
  rw [e72, q69] at hn
  have hp : p = mid := by omega
  have hq : q = hi := by omega
  subst hp hq
  rw [show p + q - p - lo = q - lo by omega, Nat.sub_self, Nat.sub_self, segL_zero, segL_zero,
    List.merge_right, List.append_nil] at hseg
  refine ⟨c', k, ex, by rw [r72] at hk; exact hk, hseg, fun a ha => hmem a (by omega), hreg,
    er, erm, eo⟩

end NcStep

end BKMNW

end PlanarFlow
