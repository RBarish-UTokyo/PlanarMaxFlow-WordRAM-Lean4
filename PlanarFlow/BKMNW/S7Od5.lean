module

public import PlanarFlow.BKMNW.S7Od4

/-!
# Stage 7 of `sepL` (III), the meaning of the machine's weights and flags

* `card_filter_getD` (indices of a list with a property ↔ `List.filter`);
* **`od_wt_sem`**: the machine's weight of position `q` (`#{i | P1[i] = q + 1}` plus the
  scatter-add of `K (1 - HT)` over the holes owned by `q`) is `hw M K Hs C (odL g n lst q)`;
* **`od_hsum`**: the weights of the holes add up to at most `K · nTouch M P Hs`;
* **`od_left_sem`**: with the machine's first group (`twoGroupsL` of the weights), a dart is in the
  first group `l` of `twoGroupsL (hw …) A (ordE eG N (P.image X))` iff its position satisfies the
  test of `odC`, and in the rest otherwise.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset MfDrv

lemma card_filter_getD {α : Type*} (l : List α) (d : α) (p : α → Bool) :
    ((range l.length).filter fun j => p (l.getD j d) = true).card = (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.range_add_one', filter_insert, filter_map]
    simp only [List.getD_cons_zero, List.filter_cons]
    have e : ((range t.length).filter ((fun j => p ((a :: t).getD j d) = true) ∘
        ⇑(Function.Embedding.mk Nat.succ Nat.succ_injective))) =
        (range t.length).filter fun j => p (t.getD j d) = true := by
      apply filter_congr; intro j _; simp
    by_cases ha : p a = true
    · simp only [ha, ↓reduceIte, List.length_cons]
      rw [card_insert_of_notMem (by simp), card_map, e, ih]
    · simp only [ha, ↓reduceIte, Bool.false_eq_true]
      rw [card_map, e, ih]

section Sem

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}
variable {P : Finset D} {X : D → Finset D} {g : ℕ → D} {n : ℕ} {cid lst : ℕ → ℕ}

/-- The owner of a hole, from `svF_spec`. -/
lemma own_spec (hp p1 : ℕ → ℕ) (n h : ℕ) :
    (svF hp p1 n h 0 = 0 ∧ ∀ i < n, hp i ≠ h) ∨ (∃ i < n, hp i = h ∧ svF hp p1 n h 0 = p1 i) := by
  rcases svF_spec hp p1 n h 0 with ⟨hn, e⟩ | ⟨j, hj, h1, h2, -⟩
  · exact Or.inl ⟨e, fun i hi hi' => hn ⟨i, hi, hi'⟩⟩
  · exact Or.inr ⟨j, hj, h1, h2⟩

/-- **The machine's weight of a position is `hw` of its class.** -/
theorem od_wt_sem (h : OdIn P X g n cid lst) {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint)
    {C : Finset V} {K : ℕ}
    (htH : K ≠ 0 → ∀ d ∈ P, ∀ d' ∈ P, X d ≠ X d' →
      Disjoint (tH M Hs C (X d)) (tH M Hs C (X d')))
    {hp ht : ℕ → ℕ} (hhp : ∀ i < n, hp i = hlab Hs (M.tail (g i)))
    (hht : ∀ j < Hs.length, (ht (j + 1) = 0 ↔ Disjoint (Hs.getD j ∅) C)) (q : ℕ) :
    ((range n).filter fun i => odPos lst i + 1 = q + 1).card +
      saF (fun j => svF hp (fun i => odPos lst i + 1) n (j + 1) 0)
        (fun j => vhV K (ht (j + 1)) (svF hp (fun i => odPos lst i + 1) n (j + 1) 0))
        Hs.length (q + 1) = hw M K Hs C (odL g n lst q) := by
  set own : ℕ → ℕ := fun h => svF hp (fun i => odPos lst i + 1) n h 0 with hown
  rw [hw_eq, h.odL_card]
  have e1 : ((range n).filter fun i => odPos lst i + 1 = q + 1) =
      (range n).filter fun i => odPos lst i = q := filter_congr fun i _ => by omega
  rw [e1]
  congr 1
  -- the scatter-add of the holes
  have e2 : saF (fun j => own (j + 1)) (fun j => vhV K (ht (j + 1)) (own (j + 1))) Hs.length
      (q + 1) = K * ((range Hs.length).filter fun j => ht (j + 1) = 0 ∧ own (j + 1) = q + 1).card
      := by
    unfold saF
    have hv : ∀ j ∈ (range Hs.length).filter (fun j => own (j + 1) = q + 1),
        vhV K (ht (j + 1)) (own (j + 1)) = if ht (j + 1) = 0 then K else 0 := by
      intro j hj
      rw [(mem_filter.1 hj).2]
      unfold vhV
      rw [Nat.div_self (by omega)]
      by_cases h0 : ht (j + 1) = 0
      · simp [h0]
      · simp [h0, show 1 - ht (j + 1) = 0 by omega]
    rw [sum_congr rfl hv, sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul,
      filter_filter, mul_comm]
    congr 2
    ext j
    simp only [mem_filter]
    tauto
  rw [e2]
  by_cases hK : K = 0
  · simp [hK]
  · congr 1
    rw [h.odL_tH_card hd (htH hK) hhp hht (fun j hj => ?_) q]
    rcases own_spec hp (fun i => odPos lst i + 1) n (j + 1) with ⟨a, b⟩ | ⟨i, hi, a, b⟩
    · exact Or.inl ⟨a, b⟩
    · exact Or.inr ⟨i, hi, a, b⟩

/-- **The weights of the holes add up to at most `K · nTouch`.** -/
theorem od_hsum {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {K : ℕ} {hp p1 ht : ℕ → ℕ}
    (hgP : ∀ i < n, g i ∈ P) (hhp : ∀ i < n, hp i = hlab Hs (M.tail (g i))) :
    ∑ j ∈ range Hs.length, vhV K (ht (j + 1)) (svF hp p1 n (j + 1) 0) ≤
      K * nTouch M P Hs := by
  classical
  have hle : ∀ j ∈ range Hs.length, vhV K (ht (j + 1)) (svF hp p1 n (j + 1) 0) ≤
      if decide (∃ v ∈ Hs.getD j ∅, Touch M P v) = true then K else 0 := by
    intro j hj
    rw [mem_range] at hj
    unfold vhV
    rcases own_spec hp p1 n (j + 1) with ⟨a, -⟩ | ⟨i, hi, a, -⟩
    · rw [a]; simp
    · have hv : M.tail (g i) ∈ Hs.getD j ∅ := by
        rw [← hlab_eq_succ_iff hd hj, ← hhp i hi, a]
      have ht' : decide (∃ v ∈ Hs.getD j ∅, Touch M P v) = true :=
        decide_eq_true ⟨_, hv, g i, hgP i hi, rfl⟩
      rw [iteT ht']
      have h1 := dself_le (svF hp p1 n (j + 1) 0)
      have h2 : (svF hp p1 n (j + 1) 0 / svF hp p1 n (j + 1) 0) * (1 - ht (j + 1)) ≤ 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with e | e <;> rw [e] <;> omega
      calc _ ≤ 1 * K := Nat.mul_le_mul_right K h2
        _ = K := one_mul K
  refine (sum_le_sum hle).trans ?_
  rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_comm]
  apply Nat.mul_le_mul_left
  rw [card_filter_getD Hs ∅ (fun H => decide (∃ v ∈ H, Touch M P v))]
  unfold nTouch
  apply le_of_eq
  congr 1

/-- **The flags of the left piece mean the first group.** -/
theorem od_left_sem (h : OdIn P X g n cid lst) {gid : D → ℕ}
    (hmono : ∀ i j, i < j → j < n → gid (g i) < gid (g j)) {eG : ℕ → D} {N : ℕ}
    (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d) {ω : Finset D → ℕ}
    {A : ℕ} {wt : ℕ → ℕ} (hwt : ∀ q < odM lst n, wt q = ω (odL g n lst q)) {r6 r7 r11 : ℕ}
    (htg : twoGroupsL wt A (List.range (odM lst n)) =
      if r6 = 1 then [r7] else List.range (min r11 (odM lst n))) {i : ℕ} (hi : i < n) :
    (g i ∈ (twoGroupsL ω A (ordE eG N (P.image X))).toFinset.biUnion _root_.id ↔
      if r6 = 1 then odPos lst i = r7 else odPos lst i < min r11 (odM lst n)) ∧
    (g i ∈ (P.image X \ (twoGroupsL ω A (ordE eG N (P.image X))).toFinset).biUnion _root_.id ↔
      ¬ (if r6 = 1 then odPos lst i = r7 else odPos lst i < min r11 (odM lst n))) := by
  have e : twoGroupsL ω A (ordE eG N (P.image X)) =
      (if r6 = 1 then [r7] else List.range (min r11 (odM lst n))).map (odL g n lst) := by
    rw [h.odL_ordE hmono he hesurj, twoGroupsL_map, ← htg]
    congr 1
    exact twoGroupsL_congr A fun q hq => (hwt q (List.mem_range.1 hq)).symm
  rw [e, h.odL_left _ hi, h.odL_right _ hi]
  split_ifs with h6 <;> simp

end Sem

end BKMNW

end PlanarFlow
