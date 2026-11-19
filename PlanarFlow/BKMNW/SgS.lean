module

public import PlanarFlow.BKMNW.S7C
public import PlanarFlow.BKMNW.RunsProg

/-!
# The parts of the separator (`SegsOut` of `sepL`), pure part

The parts `segsF ρ Hs = ρ.runsF hρ 0` are given by the index pairs `runIdx H k 0` (`rnProg`,
`RunsProg.lean`; `H j` the flag "the `j`-th vertex of the path is in a hole"). The darts of the
parts, listed one part after the other, are exactly the darts `t < k` of the path with both ends
off the holes (`rfN H k t = 1`), in increasing order:

* `rfN` (that flag), **`runIdx_cnt`**: for the `j`-th pair `(a, e)` of `runIdx H k s`, the count of
  the flagged darts before `a` is the count before `s` plus the lengths `e' - a'` of the earlier
  pairs, and the darts `a, …, e - 1` are flagged;
* `runIdx_len_le` (the lengths add up to at most the count of flagged darts).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset

/-- The flag of a dart of a run: both ends off the holes, before the end of the path. -/
def rfN (H : ℕ → Bool) (k t : ℕ) : ℕ := if t < k ∧ H t = false ∧ H (t + 1) = false then 1 else 0

/-- **The darts of the runs are the flagged darts, run after run.** -/
theorem runIdx_cnt (H : ℕ → Bool) (k : ℕ) : ∀ s, ∀ j (hj : j < (runIdx H k s).length),
    cnt (rfN H k) ((runIdx H k s)[j]).1 =
      cnt (rfN H k) s + (((runIdx H k s).take j).map fun p => p.2 - p.1).sum ∧
    ∀ l < ((runIdx H k s)[j]).2 - ((runIdx H k s)[j]).1, 0 < rfN H k (((runIdx H k s)[j]).1 + l)
    := by
  intro s
  induction hn : k + 1 - s using Nat.strong_induction_on generalizing s with
  | _ N ih =>
    intro j hj
    by_cases hks : k < s
    · rw [runIdx_of_lt H hks] at hj; simp at hj
    by_cases hHs : H s = true
    · have e := runIdx_of_mem H (k := k) (s := s) (by omega) hHs
      have hj' : j < (runIdx H k (s + 1)).length := by rw [← e]; exact hj
      have hc : cnt (rfN H k) (s + 1) = cnt (rfN H k) s := by
        rw [cnt_succ]; simp [rfN, hHs]
      obtain ⟨h1, h2⟩ := ih (k + 1 - (s + 1)) (by omega) (s + 1) rfl j hj'
      simp only [e]
      exact ⟨by rw [h1, hc], h2⟩
    · have hHs' : H s = false := by simpa using hHs
      have e := runIdx_of_not_mem H (k := k) (s := s) (by omega) hHs'
      set b := runEndF H k s with hb
      have hsb : s ≤ b := runEndF_ge H k s
      have hbk : b ≤ k := runEndF_le_k H (by omega)
      have hoff := runEndF_off H k hHs'
      simp only [e]
      rcases j with _ | j
      · refine ⟨by simp, fun l hl => ?_⟩
        simp only [List.getElem_cons_zero] at hl ⊢
        unfold rfN
        rw [iteT ⟨by omega, hoff _ (by omega) (by omega), hoff _ (by omega) (by omega)⟩]
        omega
      · have hj' : j < (runIdx H k (b + 2)).length := by
          rw [e] at hj; simpa using hj
        -- the flagged darts from `s` to `b + 2`
        have hflag : ∀ t, s ≤ t → t < b → rfN H k t = 1 := fun t h1 h2 => by
          unfold rfN
          rw [iteT ⟨by omega, hoff _ (by omega) (by omega), hoff _ (by omega) (by omega)⟩]
        have hb0 : rfN H k b = 0 := by
          unfold rfN
          rw [iteF]
          rintro ⟨h1, -, h3⟩
          rcases runEndF_spec H k s with h | h
          · omega
          · rw [← hb] at h; rw [h] at h3; exact Bool.noConfusion h3
        have hb1 : rfN H k (b + 1) = 0 := by
          unfold rfN
          rw [iteF]
          rintro ⟨h1, h2, -⟩
          rcases runEndF_spec H k s with h | h
          · omega
          · rw [← hb] at h; rw [h] at h2; exact Bool.noConfusion h2
        have hcs : ∀ t, s ≤ t → t ≤ b → cnt (rfN H k) t = cnt (rfN H k) s + (t - s) := by
          intro t h1 h2
          induction t with
          | zero => obtain rfl : s = 0 := by omega
                    simp
          | succ t iht =>
            rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
            · simp
            · rw [cnt_succ, iht (by omega) (by omega), hflag t (by omega) (by omega)]
              simp; omega
        have hc2 : cnt (rfN H k) (b + 2) = cnt (rfN H k) s + (b - s) := by
          rw [cnt_succ, cnt_succ, hcs b hsb le_rfl, hb0, hb1]; simp
        obtain ⟨h1, h2⟩ := ih (k + 1 - (b + 2)) (by omega) (b + 2) rfl j hj'
        refine ⟨?_, fun l hl => ?_⟩
        · simp only [List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
          rw [h1, hc2]; ring
        · simp only [List.getElem_cons_succ] at hl ⊢
          exact h2 l hl

end BKMNW

end PlanarFlow
