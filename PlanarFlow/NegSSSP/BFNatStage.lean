module

public import PlanarFlow.NegSSSP.NodeRunE
public import PlanarFlow.NegSSSP.BFNat

/-!
# The start of Bellman–Ford in the node run: integer reals, bounded memory

`bfStage` (`PlanarFlow/NegSSSP/NodeRunE.lean`) prepares the configuration of `bfFull` by the
prefix `bfPre` (registers, clearing, the three copies) and then runs `bfFull`
(`bfStage_split`). `bfPre_start`: from a configuration as in `bfStage_exec` whose real registers
`< 85` and real memory `≤ bfWP b` are integers bounded by `B` (the memory), with the lengths of
both matrices bounded by `B`, the prefix ends in a configuration satisfying all the hypotheses of
`bfFull_exec_emb` and moreover `MemB (bfWP b) B` and the integrality of its real registers `< 85`
and real memory `≤ bfWP b`, i.e. the hypotheses of `bfFull_exec_emb_nat` (with `B = bfB b L`)
and of `ModNat.sim_natOf`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge CmpAbs

variable {I : Input}

/-- The preparation of `bfFull` in `bfStage`. -/
def bfPre : Stmt :=
  .seq (zeroRegs (List.range 85)) <| .seq bfSet <| .seq clrProg <|
  .seq (cpS 1 9 970 974 4) <| .seq cpyProg <| .seq (cpS 50 42 971 41 971) <| .seq cpyProg <|
  .seq (cpS 50 81 972 80 972) cpyProg

theorem exec_seq_inv {W' : ℕ} {s t : Stmt} {c d : Config} {k : ℕ}
    (e : Exec I W' (.seq s t) c d k) : ∃ c₁ k₁ k₂, Exec I W' s c c₁ k₁ ∧ Exec I W' t c₁ d k₂ := by
  cases e with
  | seq e₁ e₂ => exact ⟨_, _, _, e₁, e₂⟩

/-- **A run of `bfStage` is the preparation `bfPre`, then `bfFull` and the outputs.** -/
theorem bfStage_split {W' : ℕ} {c c' : Config} {k : ℕ} (e : Exec I W' bfStage c c' k) :
    ∃ c₉ k₁ k₂, Exec I W' bfPre c c₉ k₁ ∧
      Exec I W' (.seq bfFull (.seq bfOut (.seq (cpS 802 809 973 810 86) cpyProg))) c₉ c' k₂ := by
  unfold bfStage at e
  obtain ⟨_, _, _, e₁, e⟩ := exec_seq_inv e
  obtain ⟨_, _, _, e₂, e⟩ := exec_seq_inv e
  obtain ⟨_, _, _, e₃, e⟩ := exec_seq_inv e
  obtain ⟨_, _, _, e₄, e⟩ := exec_seq_inv e
  obtain ⟨_, _, _, e₅, e⟩ := exec_seq_inv e
  obtain ⟨_, _, _, e₆, e⟩ := exec_seq_inv e
  obtain ⟨_, _, _, e₇, e⟩ := exec_seq_inv e
  obtain ⟨_, _, _, e₈, e⟩ := exec_seq_inv e
  obtain ⟨_, _, _, e₉, e⟩ := exec_seq_inv e
  exact ⟨_, _, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉))))))),
    e⟩

set_option maxHeartbeats 4000000 in
/-- **The start of Bellman–Ford in the node run** (see the module docstring). -/
theorem bfPre_start {b B : ℕ} {X₁ X₂ : ℕ → ℕ → Prop} {D₁ D₂ : ℕ → ℕ → ℤ} {π : ℕ → ℕ}
    (hπ : IsPermB b π)
    {πb F0 F1 Ob R Z6 Z7 W' : ℕ} (hL : BLay b πb F0 F1 Ob R Z6 Z7 W') (c : Config)
    (hc : WordsBounded W' c) (h802 : c.nreg 802 = b) (h970 : c.nreg 970 = πb)
    (h971 : c.nreg 971 = F0) (h972 : c.nreg 972 = F1) (h974 : c.nreg 974 = R)
    (hπm : ∀ i < b, c.nmem (πb + i) = π i)
    (hF0 : ∀ s < b, ∀ t < b, c.nmem (F0 + (s * b + t)) = finB X₁ s t ∧
      c.rmem (F0 + (s * b + t)) = (D₁ s t : ℝ))
    (hF1 : ∀ s < b, ∀ t < b, c.nmem (F1 + (s * b + t)) = finB X₂ s t ∧
      c.rmem (F1 + (s * b + t)) = (D₂ s t : ℝ))
    (hB₁ : ∀ s < b, ∀ t < b, |(D₁ s t : ℝ)| ≤ B) (hB₂ : ∀ s < b, ∀ t < b, |(D₂ s t : ℝ)| ≤ B)
    (hri : ∀ r < 85, ∃ z : ℤ, c.rreg r = z) (hmi : ∀ a ≤ bfWP b, ∃ z : ℤ, c.rmem a = z)
    (hmB : MemB (bfWP b) B c) :
    ∃ c₉ k, Exec I W' bfPre c c₉ k ∧ BFRegs b c₉ ∧ BFMem b X₁ D₁ X₂ D₂ π c₉ ∧
      (∀ r < 85, c₉.nreg r ≤ bfWP b) ∧ (∀ a ≤ bfWP b, c₉.nmem a ≤ bfWP b) ∧
      MemB (bfWP b) B c₉ ∧ (∀ r < 85, ∃ z : ℤ, c₉.rreg r = z) ∧
      (∀ a ≤ bfWP b, ∃ z : ℤ, c₉.rmem a = z) ∧ (∀ a, bfWP b < a → c₉.nmem a = c.nmem a) ∧
      (∀ a, bfWP b < a → (a < R ∨ R + b ≤ a) → c₉.rmem a = c.rmem a) ∧
      (∀ r, 85 ≤ r → r ≠ 86 → r ≠ 900 → (r < 901 ∨ 918 < r) → c₉.nreg r = c.nreg r) ∧
      c₉.output = c.output := by
  obtain ⟨wp, pi, piW, f0, f0W, f1, f1W, ob, obW, r, rW, rF0, rF1, z6, z6W, z6O, z7, z7W⟩ := hL
  have hWb : bfWP b = 8 * (b * b) + 14 * b + 12 := rfl
  -- 0., 1. the registers
  obtain ⟨c₁, k₁, e₁, hk₁, hz₁, hrr₁, hnm₁, hrm₁, ho₁⟩ :=
    zeroRegs_exec (P := I) (List.range 85) c hc
  have hn₁ : ∀ r, 85 ≤ r → c₁.nreg r = c.nreg r := fun r hr => by
    rw [hz₁ r, ite_eq_right_of_eq_false _ _ (eq_false (by simp; omega))]
  obtain ⟨c₂, k₂, e₂, hk₂, hR₂, r50, r86, r900, hb₂, hn₂, hrr₂, hnm₂, hrm₂, ho₂⟩ :=
    bfSet_exec (I := I) (b := b) c₁ e₁.wb_right (by rw [hn₁ 802 (by omega), h802])
      (by omega) (fun r hr => by
        rw [hz₁ r, ite_eq_left_of_eq_true _ _ (eq_true (by simp; omega))]; exact Nat.zero_le _)
  have hn₂' : ∀ r, 85 ≤ r → r ≠ 86 → r ≠ 900 → c₂.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [hn₂ r h1 h2 h3, hn₁ r h1]
  -- 2. the clearing
  obtain ⟨c₃, k₃, e₃, hk₃, z₃, hm₃, hn₃, hrr₃, hrm₃, ho₃⟩ :=
    clrProg_exec (P := I) (L := bfWP b + 1) (by omega) c₂ e₂.wb_right r900
  -- 3., 4. `π`
  obtain ⟨c₄, k₄, e₄, hk₄, p910, p911, p912, p913, p914, hn₄, hrr₄, hnm₄, hrm₄, ho₄⟩ :=
    cpS_exec (I := I) (rn := 1) (rDn := 9) (rSn := 970) (rDr := 974) (rSr := 4) (by omega) c₃
      e₃.wb_right
  have g : ∀ r, r < 85 → c₄.nreg r = c₂.nreg r := fun r hr => by
    rw [hn₄ r (by omega), hn₃ r (by omega)]
  have hL₄ : CpyLay b (5 * b + 2) πb R 0 W' :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨c₅, k₅, e₅, hk₅, hcp₅, hm₅, hr₅, hn₅, hrr₅, ho₅⟩ := cpyProg_exec (P := I) hL₄ c₄
    e₄.wb_right (by rw [p910, hn₃ 1 (by omega), hR₂.r1])
    (by rw [p911, hn₃ 9 (by omega), hR₂.r9])
    (by rw [p912, hn₃ 970 (by omega), hn₂' 970 (by omega) (by omega) (by omega), h970])
    (by rw [p913, hn₃ 974 (by omega), hn₂' 974 (by omega) (by omega) (by omega), h974])
    (by rw [p914, hn₃ 4 (by omega), hR₂.r4])
  -- 5., 6. the first matrix
  obtain ⟨c₆, k₆, e₆, hk₆, q910, q911, q912, q913, q914, hn₆, hrr₆, hnm₆, hrm₆, ho₆⟩ :=
    cpS_exec (I := I) (rn := 50) (rDn := 42) (rSn := 971) (rDr := 41) (rSr := 971) (by omega) c₅
      e₅.wb_right
  have hL₆ : CpyLay (b * b) (7 * b + 2) F0 (10 * b + 2 + 2 * (b * b)) F0 W' :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have g₅ : ∀ r, r < 85 ∨ (900 ≤ r ∧ r < 910) ∨ 970 ≤ r → c₅.nreg r = c₃.nreg r := fun r hr => by
    rw [hn₅ r (by omega), hn₄ r (by omega)]
  have g₃ : ∀ r, 970 ≤ r → c₃.nreg r = c.nreg r := fun r hr => by
    rw [hn₃ r (by omega), hn₂' r (by omega) (by omega) (by omega)]
  obtain ⟨c₇, k₇, e₇, hk₇, hcp₇, hm₇, hr₇, hn₇, hrr₇, ho₇⟩ := cpyProg_exec (P := I) hL₆ c₆
    e₆.wb_right (by rw [q910, g₅ 50 (by omega), hn₃ 50 (by omega), r50])
    (by rw [q911, g₅ 42 (by omega), hn₃ 42 (by omega), hR₂.r42])
    (by rw [q912, g₅ 971 (by omega), g₃ 971 (by omega), h971])
    (by rw [q913, g₅ 41 (by omega), hn₃ 41 (by omega), hR₂.r41])
    (by rw [q914, g₅ 971 (by omega), g₃ 971 (by omega), h971])
  -- 7., 8. the second matrix
  obtain ⟨c₈, k₈, e₈, hk₈, u910, u911, u912, u913, u914, hn₈, hrr₈, hnm₈, hrm₈, ho₈⟩ :=
    cpS_exec (I := I) (rn := 50) (rDn := 81) (rSn := 972) (rDr := 80) (rSr := 972) (by omega) c₇
      e₇.wb_right
  have hL₈ : CpyLay (b * b) (7 * b + 2 + b * b) F1 (10 * b + 2 + 3 * (b * b)) F1 W' :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have g₇ : ∀ r, r < 85 ∨ (900 ≤ r ∧ r < 910) ∨ 970 ≤ r → c₇.nreg r = c₃.nreg r := fun r hr => by
    rw [hn₇ r (by omega), hn₆ r (by omega), g₅ r hr]
  obtain ⟨c₉, k₉, e₉, hk₉, hcp₉, hm₉, hr₉, hn₉, hrr₉, ho₉⟩ := cpyProg_exec (P := I) hL₈ c₈
    e₈.wb_right (by rw [u910, g₇ 50 (by omega), hn₃ 50 (by omega), r50])
    (by rw [u911, g₇ 81 (by omega), hn₃ 81 (by omega), hR₂.r81])
    (by rw [u912, g₇ 972 (by omega), g₃ 972 (by omega), h972])
    (by rw [u913, g₇ 80 (by omega), hn₃ 80 (by omega), hR₂.r80])
    (by rw [u914, g₇ 972 (by omega), g₃ 972 (by omega), h972])
  have g₉ : ∀ r, r < 85 ∨ (900 ≤ r ∧ r < 910) ∨ 970 ≤ r → c₉.nreg r = c₃.nreg r := fun r hr => by
    rw [hn₉ r (by omega), hn₈ r (by omega), g₇ r hr]
  -- the memory before Bellman–Ford
  have hmc : ∀ a, bfWP b < a → c₉.nmem a = c.nmem a := fun a ha => by
    rw [hm₉ a (Or.inr (by omega)), hnm₈, hm₇ a (Or.inr (by omega)), hnm₆,
      hm₅ a (Or.inr (by omega)), hnm₄, hm₃ a (by omega), hnm₂, hnm₁]
  have hrc : ∀ a, bfWP b < a → (a < R ∨ R + b ≤ a) → c₉.rmem a = c.rmem a := fun a ha ha' => by
    rw [hr₉ a (Or.inr (by omega)), hrm₈, hr₇ a (Or.inr (by omega)), hrm₆, hr₅ a ha', hrm₄,
      hrm₃, hrm₂, hrm₁]
  have hF0' : ∀ e < b * b, c₉.nmem (7 * b + 2 + e) = c.nmem (F0 + e) ∧
      c₉.rmem (10 * b + 2 + 2 * (b * b) + e) = c.rmem (F0 + e) := fun e he => by
    refine ⟨?_, ?_⟩
    · rw [hm₉ _ (Or.inl (by omega)), hnm₈, (hcp₇ e he).1, hnm₆, ← hmc _ (by omega),
        hm₉ _ (Or.inr (by omega)), hnm₈, hm₇ _ (Or.inr (by omega)), hnm₆]
    · rw [hr₉ _ (Or.inl (by omega)), hrm₈, (hcp₇ e he).2, hrm₆,
        ← hrc _ (by omega) (by omega), hr₉ _ (Or.inr (by omega)), hrm₈,
        hr₇ _ (Or.inr (by omega)), hrm₆]
  have hF1' : ∀ e < b * b, c₉.nmem (7 * b + 2 + b * b + e) = c.nmem (F1 + e) ∧
      c₉.rmem (10 * b + 2 + 3 * (b * b) + e) = c.rmem (F1 + e) := fun e he => by
    refine ⟨?_, ?_⟩
    · rw [(hcp₉ e he).1, hnm₈, ← hmc _ (by omega), hm₉ _ (Or.inr (by omega)), hnm₈]
    · rw [(hcp₉ e he).2, hrm₈, ← hrc _ (by omega) (by omega), hr₉ _ (Or.inr (by omega)), hrm₈]
  have hπ' : ∀ i < b, c₉.nmem (5 * b + 2 + i) = π i := fun i hi => by
    rw [hm₉ _ (Or.inl (by omega)), hnm₈, hm₇ _ (Or.inl (by omega)), hnm₆, (hcp₅ i hi).1, hnm₄,
      hm₃ _ (by omega), hnm₂, hnm₁, hπm i hi]
  have hBM : BFMem b X₁ D₁ X₂ D₂ π c₉ := by
    refine ⟨hπ', fun s t hs ht => ?_, fun s t hs ht => ?_, fun s t hs ht => ?_,
      fun s t hs ht => ?_⟩
    · have := (hF0' _ (rmLt hs ht)).1
      rw [← Nat.add_assoc] at this; rw [this]; exact (hF0 s hs t ht).1
    · have := (hF1' _ (rmLt hs ht)).1
      rw [← Nat.add_assoc] at this; rw [this]; exact (hF1 s hs t ht).1
    · have := (hF0' _ (rmLt hs ht)).2
      rw [← Nat.add_assoc] at this; rw [this]; exact (hF0 s hs t ht).2
    · have := (hF1' _ (rmLt hs ht)).2
      rw [← Nat.add_assoc] at this; rw [this]; exact (hF1 s hs t ht).2
  have hBR : BFRegs b c₉ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [g₉ _ (by omega), hn₃ _ (by omega)]
    exacts [hR₂.r1, hR₂.r2, hR₂.r3, hR₂.r4, hR₂.r7, hR₂.r8, hR₂.r9, hR₂.r10, hR₂.r40, hR₂.r41,
      hR₂.r42, hR₂.r43, hR₂.r80, hR₂.r81]
  have hmb : ∀ a ≤ bfWP b, c₉.nmem a ≤ bfWP b := by
    intro a ha
    by_cases h1 : 7 * b + 2 + b * b ≤ a ∧ a < 7 * b + 2 + b * b + b * b
    · obtain ⟨e, rfl⟩ : ∃ e, a = 7 * b + 2 + b * b + e := ⟨a - (7 * b + 2 + b * b), by omega⟩
      obtain ⟨s, hs, t, ht, rfl⟩ := rowmaj (show e < b * b by omega)
      rw [(hF1' _ (by omega)).1, (hF1 s hs t ht).1]
      have := finB_le (X := X₂) s t; omega
    by_cases h2 : 7 * b + 2 ≤ a ∧ a < 7 * b + 2 + b * b
    · obtain ⟨e, rfl⟩ : ∃ e, a = 7 * b + 2 + e := ⟨a - (7 * b + 2), by omega⟩
      obtain ⟨s, hs, t, ht, rfl⟩ := rowmaj (show e < b * b by omega)
      rw [(hF0' _ (by omega)).1, (hF0 s hs t ht).1]
      have := finB_le (X := X₁) s t; omega
    rw [hm₉ a (by omega), hnm₈, hm₇ a (by omega), hnm₆]
    by_cases h3 : 5 * b + 2 ≤ a ∧ a < 5 * b + 2 + b
    · obtain ⟨i, rfl⟩ : ∃ i, a = 5 * b + 2 + i := ⟨a - (5 * b + 2), by omega⟩
      rw [(hcp₅ i (by omega)).1, hnm₄, hm₃ _ (by omega), hnm₂, hnm₁, hπm i (by omega)]
      have := hπ.lt i (by omega); omega
    rw [hm₅ a (by omega), hnm₄, z₃ a (by omega)]; exact Nat.zero_le _
  -- the real registers and the real memory below `bfWP b`
  have hrr : ∀ r < 85, c₉.rreg r = c.rreg r := fun r hr => by
    rw [hrr₉ r (by omega), hrr₈, hrr₇ r (by omega), hrr₆, hrr₅ r (by omega), hrr₄, hrr₃, hrr₂,
      hrr₁]
  have hrm : ∀ a ≤ bfWP b, c₉.rmem a = c.rmem a ∨
      (∃ s < b, ∃ t < b, c₉.rmem a = D₁ s t) ∨ (∃ s < b, ∃ t < b, c₉.rmem a = D₂ s t) := by
    intro a ha
    by_cases h1 : 10 * b + 2 + 3 * (b * b) ≤ a ∧ a < 10 * b + 2 + 3 * (b * b) + b * b
    · obtain ⟨e, rfl⟩ : ∃ e, a = 10 * b + 2 + 3 * (b * b) + e :=
        ⟨a - (10 * b + 2 + 3 * (b * b)), by omega⟩
      obtain ⟨s, hs, t, ht, rfl⟩ := rowmaj (show e < b * b by omega)
      right; right; refine ⟨s, hs, t, ht, ?_⟩
      rw [(hF1' _ (by omega)).2, (hF1 s hs t ht).2]
    by_cases h2 : 10 * b + 2 + 2 * (b * b) ≤ a ∧ a < 10 * b + 2 + 2 * (b * b) + b * b
    · obtain ⟨e, rfl⟩ : ∃ e, a = 10 * b + 2 + 2 * (b * b) + e :=
        ⟨a - (10 * b + 2 + 2 * (b * b)), by omega⟩
      obtain ⟨s, hs, t, ht, rfl⟩ := rowmaj (show e < b * b by omega)
      right; left; refine ⟨s, hs, t, ht, ?_⟩
      rw [(hF0' _ (by omega)).2, (hF0 s hs t ht).2]
    left
    rw [hr₉ a (by omega), hrm₈, hr₇ a (by omega), hrm₆, hr₅ a (Or.inl (by omega)), hrm₄, hrm₃,
      hrm₂, hrm₁]
  refine ⟨c₉, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉))))))),
    hBR, hBM, fun r hr => by rw [g₉ r (by omega), hn₃ r (by omega)]; exact hb₂ r hr, hmb,
    fun a ha => ?_, fun r hr => ?_, fun a ha => ?_, hmc, hrc, fun r h1 h2 h3 h4 => ?_, ?_⟩
  · rcases hrm a ha with h | ⟨s, hs, t, ht, h⟩ | ⟨s, hs, t, ht, h⟩ <;> rw [h]
    exacts [hmB a ha, hB₁ s hs t ht, hB₂ s hs t ht]
  · rw [hrr r hr]; exact hri r hr
  · rcases hrm a ha with h | ⟨s, hs, t, ht, h⟩ | ⟨s, hs, t, ht, h⟩ <;> rw [h]
    exacts [hmi a ha, ⟨_, rfl⟩, ⟨_, rfl⟩]
  · rw [hn₉ r (by omega), hn₈ r (by omega), hn₇ r (by omega), hn₆ r (by omega),
      hn₅ r (by omega), hn₄ r (by omega), hn₃ r (by omega), hn₂' r h1 h2 h3]
  · rw [ho₉, ho₈, ho₇, ho₆, ho₅, ho₄, ho₃, ho₂, ho₁]

end NegSSSP

end PlanarFlow
