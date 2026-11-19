module

public import PlanarFlow.BKMNW.NrOs

/-!
# One pass of the cancellation on the machine: `nrPass`

From the flow array `G` (`m` words, `G[i] = Z + g(ed i)`), the face keys `KY[i] < n` of the darts
and the keys `NH[i]` of their reverses, `nrPass` (registers `9000 … 9024`, inputs
`9000 m`, `9001 n`, `9002 G`, `9003 KY`, `9004 NH`, `9005 Z`, `9006 S` (scratch base),
`9007 s` (root key), `9008 Inf`):

1. loop A: `LN[i] := Z - G[i]` (the length `canLen g`), `ONE[i] := 1`;
2. `osProg`: the out-lists of the keys (counting sort, `nrOs_exec`);
3. `dkProg`: Dijkstra from the key `s`;
4. loop D: `G[i] := G[i] + D[NH[i]] - D[KY[i]]`.

Scratch `[S, S + 3m + 8n + 1)`: `LN`, `ONE`, the counting sort `[S + 2m, S + 2m + 2n + 1)`, `OB`,
`OE`, `OL`, the distances `D` at `S + 3m + 4n + 1`, Dijkstra's heap after them.

**`nrPass_exec`**: within `nrPassCost m n` steps, the arcs of Dijkstra (a `DkP` with the out-lists
of the keys, heads `NH`, lengths `LN`) and its distances `Dv`, and `G[i] = G[i] + Dv NH[i] - Dv KY[i]`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP Monge.FR

/-! ### The program -/

/-- The bases. -/
def nrPA : Stmt :=
  block [.constN 9010 1, .addN 9011 9006 9000, .addN 9012 9011 9000, .addN 9013 9012 9001,
    .addN 9013 9013 9010, .addN 9014 9013 9001, .addN 9015 9014 9001, .addN 9016 9015 9001,
    .addN 9017 9016 9000, .addN 9018 9017 9001]

/-- `i := 0`. -/
def nrI0 : Stmt := block [.constN 9019 0]

/-- `LN[i] := Z - G[i]`, `ONE[i] := 1`, `i := i + 1`. -/
def nrLA : Stmt :=
  block [.addN 9020 9002 9019, .loadN 9021 9020, .subN 9022 9005 9021, .addN 9020 9006 9019,
    .storeN 9020 9022, .addN 9020 9011 9019, .storeN 9020 9010, .addN 9019 9019 9010]

/-- The registers of `osProg`. -/
def nrPB : Stmt :=
  block [.copyN 1500 9000, .copyN 1501 9001, .copyN 1502 9003, .copyN 1504 9011,
    .copyN 1505 9012, .copyN 1506 9013, .copyN 1507 9014, .copyN 1508 9015, .copyN 1509 9016]

/-- The registers of `dkProg`. -/
def nrPC : Stmt :=
  block [.copyN 2500 9001, .copyN 2501 9017, .copyN 2502 9018, .copyN 2504 9014,
    .copyN 2505 9015, .copyN 2506 9016, .copyN 2507 9004, .copyN 2508 9006, .copyN 2509 9008,
    .copyN 2510 9007]

/-- `a := G[i] + D[NH[i]]`. -/
def nrLD1 : Stmt :=
  block [.addN 9020 9002 9019, .loadN 9021 9020, .addN 9023 9004 9019, .loadN 9023 9023,
    .addN 9023 9017 9023, .loadN 9023 9023, .addN 9021 9021 9023]

/-- `G[i] := a - D[KY[i]]`, `i := i + 1`. -/
def nrLD2 : Stmt :=
  block [.addN 9024 9003 9019, .loadN 9024 9024, .addN 9024 9017 9024, .loadN 9024 9024,
    .subN 9021 9021 9024, .storeN 9020 9021, .addN 9019 9019 9010]

/-- **One pass of the cancellation.** -/
def nrPass : Stmt :=
  .seq nrPA (.seq nrI0 (.seq (.whileLtN 9019 9000 nrLA) (.seq nrPB (.seq osProg (.seq nrPC
    (.seq dkProg (.seq nrI0 (.whileLtN 9019 9000 (.seq nrLD1 nrLD2)))))))))

theorem nrPass_natOnly : Klein.natOnly nrPass = true := by kernel_rfl

/-- The step bound of `nrPass`. -/
def nrPassCost (m n : ℕ) : ℕ :=
  10 + 1 + (10 * m + 2) + 9 + osCost m n + 10 +
    (17 * n + 13 * Heap.lg (2 * n) + 22 + n * (23 * Heap.lg (2 * n) + 21) +
      (13 * Heap.lg (2 * n) + 20) * m) +
    1 + (16 * m + 2)

/-! ### The blocks -/

section Blocks

variable {P : Input} {W : ℕ}

theorem nrPA_exec (c : Config) (hc : WordsBounded W c) {m n S : ℕ} (r0 : c.nreg 9000 = m)
    (r1 : c.nreg 9001 = n) (r6 : c.nreg 9006 = S) (w : S + 3 * m + 8 * n + 1 ≤ W) :
    ∃ c' t, Exec P W nrPA c c' t ∧ t = 10 ∧ c'.nreg 9010 = 1 ∧ c'.nreg 9011 = S + m ∧
      c'.nreg 9012 = S + 2 * m ∧ c'.nreg 9013 = S + 2 * m + n + 1 ∧
      c'.nreg 9014 = S + 2 * m + 2 * n + 1 ∧ c'.nreg 9015 = S + 2 * m + 3 * n + 1 ∧
      c'.nreg 9016 = S + 2 * m + 4 * n + 1 ∧ c'.nreg 9017 = S + 3 * m + 4 * n + 1 ∧
      c'.nreg 9018 = S + 3 * m + 5 * n + 1 ∧
      (∀ x, (x < 9010 ∨ 9018 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nrPA
  exec_block
  all_goals try (clear * - r0 r1 r6 w; config_simp; (try simp only [r0, r1, r6]); omega)
  all_goals try (clear * - w; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r0, r1, r6]
  all_goals try omega
  simp only [upd_apply]; split_ifs <;> omega

theorem nrI0_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W nrI0 c c' t ∧ t = 1 ∧ c'.nreg 9019 = 0 ∧
      (∀ x, x ≠ 9019 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nrI0
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem nrLA_exec (c : Config) (hc : WordsBounded W c) {G Z S m i : ℕ}
    (r2 : c.nreg 9002 = G) (r5 : c.nreg 9005 = Z) (r6 : c.nreg 9006 = S)
    (r10 : c.nreg 9010 = 1) (r11 : c.nreg 9011 = S + m) (r19 : c.nreg 9019 = i)
    (w1 : G + i ≤ W) (w2 : S + m + i ≤ W) (w3 : i + 1 ≤ W) (hne : 0 < m) :
    ∃ c' t, Exec P W nrLA c c' t ∧ t = 8 ∧ c'.nreg 9019 = i + 1 ∧
      c'.nmem = upd (upd c.nmem (S + i) (Z - c.nmem (G + i))) (S + m + i) 1 ∧
      (∀ x, (x < 9019 ∨ 9022 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nrLA
  exec_block
  all_goals try (config_simp; simp only [r2, r5, r6, r10, r11, r19]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r10, r19]
  · config_simp; simp only [r2, r5, r6, r10, r11, r19]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem nrPB_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W nrPB c c' t ∧ t = 9 ∧ c'.nreg 1500 = c.nreg 9000 ∧
      c'.nreg 1501 = c.nreg 9001 ∧ c'.nreg 1502 = c.nreg 9003 ∧ c'.nreg 1504 = c.nreg 9011 ∧
      c'.nreg 1505 = c.nreg 9012 ∧ c'.nreg 1506 = c.nreg 9013 ∧ c'.nreg 1507 = c.nreg 9014 ∧
      c'.nreg 1508 = c.nreg 9015 ∧ c'.nreg 1509 = c.nreg 9016 ∧
      (∀ x, (x < 1500 ∨ 1509 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nrPB
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try rfl
  simp only [upd_apply]; split_ifs <;> omega

theorem nrPC_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W nrPC c c' t ∧ t = 10 ∧ c'.nreg 2500 = c.nreg 9001 ∧
      c'.nreg 2501 = c.nreg 9017 ∧ c'.nreg 2502 = c.nreg 9018 ∧ c'.nreg 2504 = c.nreg 9014 ∧
      c'.nreg 2505 = c.nreg 9015 ∧ c'.nreg 2506 = c.nreg 9016 ∧ c'.nreg 2507 = c.nreg 9004 ∧
      c'.nreg 2508 = c.nreg 9006 ∧ c'.nreg 2509 = c.nreg 9008 ∧ c'.nreg 2510 = c.nreg 9007 ∧
      (∀ x, (x < 2500 ∨ 2510 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nrPC
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try rfl
  simp only [upd_apply]; split_ifs <;> omega

theorem nrLD1_exec (c : Config) (hc : WordsBounded W c) {G NH Db i : ℕ}
    (r2 : c.nreg 9002 = G) (r4 : c.nreg 9004 = NH) (r17 : c.nreg 9017 = Db)
    (r19 : c.nreg 9019 = i) (w1 : G + i ≤ W) (w2 : NH + i ≤ W)
    (w3 : Db + c.nmem (NH + i) ≤ W)
    (w4 : c.nmem (G + i) + c.nmem (Db + c.nmem (NH + i)) ≤ W) :
    ∃ c' t, Exec P W nrLD1 c c' t ∧ t = 7 ∧ c'.nreg 9020 = G + i ∧
      c'.nreg 9021 = c.nmem (G + i) + c.nmem (Db + c.nmem (NH + i)) ∧
      (∀ x, (x < 9020 ∨ 9023 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nrLD1
  exec_block
  all_goals try (config_simp; simp only [r2, r4, r17, r19]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r2, r19]
  · config_simp; simp only [r2, r4, r17, r19]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem nrLD2_exec (c : Config) (hc : WordsBounded W c) {KY Db i a v : ℕ}
    (r3 : c.nreg 9003 = KY) (r17 : c.nreg 9017 = Db) (r10 : c.nreg 9010 = 1)
    (r19 : c.nreg 9019 = i) (r20 : c.nreg 9020 = a) (r21 : c.nreg 9021 = v)
    (w1 : KY + i ≤ W) (w2 : Db + c.nmem (KY + i) ≤ W) (w3 : a ≤ W) (w4 : i + 1 ≤ W) :
    ∃ c' t, Exec P W nrLD2 c c' t ∧ t = 7 ∧ c'.nreg 9019 = i + 1 ∧
      c'.nmem = upd c.nmem a (v - c.nmem (Db + c.nmem (KY + i))) ∧
      (∀ x, (x < 9019 ∨ 9024 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hv : v ≤ W := by rw [← r21]; exact hc.1 _
  unfold nrLD2
  exec_block
  all_goals try (config_simp; simp only [r3, r17, r10, r19, r20, r21]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r10, r19]
  · config_simp; simp only [r3, r17, r10, r19, r20, r21]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

end Blocks

/-! ### The loops -/

section Loops

variable {P : Input} {W : ℕ}

/-- **Loop A**: `LN[i] = Z - G[i]`, `ONE[i] = 1`. -/
theorem nrLAL_exec (c : Config) (hc : WordsBounded W c) {G Z S m : ℕ}
    (r0 : c.nreg 9000 = m) (r2 : c.nreg 9002 = G) (r5 : c.nreg 9005 = Z)
    (r6 : c.nreg 9006 = S) (r10 : c.nreg 9010 = 1) (r11 : c.nreg 9011 = S + m)
    (r19 : c.nreg 9019 = 0) (hG : G + m ≤ S ∨ S + 2 * m ≤ G) (w1 : G + m ≤ W)
    (w2 : S + 2 * m ≤ W) (w3 : m + 1 ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 9019 9000 nrLA) c c' t ∧ t ≤ 10 * m + 2 ∧
      (∀ i < m, c'.nmem (S + i) = Z - c.nmem (G + i) ∧ c'.nmem (S + m + i) = 1) ∧
      (∀ a, (a < S ∨ S + 2 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 9019 ∨ 9022 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    obtain ⟨c', t, ex, ht, -, -, j1⟩ := lnRange (P := P) (a := 9019) (b := 9000) (body := nrLA)
      (fun _ c' => c' = c) (B := 8) c hc r19 r0 le_rfl rfl
      (fun i c₁ _ hi => absurd hi (Nat.not_lt_zero _))
    subst j1
    exact ⟨_, t, ex, by omega, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 9019 ∨ 9022 < x) → c'.nreg x = c.nreg x) ∧
    (∀ j < i, c'.nmem (S + j) = Z - c.nmem (G + j) ∧ c'.nmem (S + m + j) = 1) ∧
    (∀ a, (a < S ∨ S + 2 * m ≤ a) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', t, ex, ht, -, -, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 9019)
    (b := 9000) (body := nrLA) J (B := 8) c hc r19 r0 (Nat.zero_le _)
    ⟨fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c₁ _ hi hw h19 h0 ⟨f₁, s₁, o₁, q1, q2, q3⟩ => by
      obtain ⟨c₂, t₂, e₂, ht₂, g19, gm, gn, gr, grm, go⟩ := nrLA_exec (P := P) c₁ hw
        (by rw [f₁ _ (by omega), r2]) (by rw [f₁ _ (by omega), r5])
        (by rw [f₁ _ (by omega), r6]) (by rw [f₁ _ (by omega), r10])
        (by rw [f₁ _ (by omega), r11]) h19 (by omega) (by omega) (by omega) hm
      have hGi : c₁.nmem (G + i) = c.nmem (G + i) := o₁ _ (by omega)
      refine ⟨c₂, t₂, e₂, ht₂.le, g19, by rw [gn _ (by omega)]; exact h0,
        fun x hx => by rw [gn x hx, f₁ x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [gr, q1], by rw [grm, q2], by rw [go, q3]⟩
      · rw [gm, hGi]
        by_cases e : j = i
        · subst e
          refine ⟨?_, by rw [upd_same]⟩
          rw [upd_other _ _ _ (by omega), upd_same]
        · obtain ⟨a1, a2⟩ := s₁ j (by omega)
          exact ⟨by rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact a1,
            by rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact a2⟩
      · rw [gm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact o₁ a ha)
  exact ⟨c', t, ex, by omega, j2, j3, j1, j4, j5, j6⟩

/-- **Loop D**: `G[i] := G[i] + D[NH[i]] - D[KY[i]]`. -/
theorem nrLDL_exec (c : Config) (hc : WordsBounded W c) {G KY NH Db m : ℕ}
    (r0 : c.nreg 9000 = m) (r2 : c.nreg 9002 = G) (r3 : c.nreg 9003 = KY)
    (r4 : c.nreg 9004 = NH) (r10 : c.nreg 9010 = 1) (r17 : c.nreg 9017 = Db)
    (r19 : c.nreg 9019 = 0) (n : ℕ)
    (hK : ∀ i < m, c.nmem (KY + i) < n ∧ c.nmem (NH + i) < n)
    (d1 : G + m ≤ KY ∨ KY + m ≤ G) (d2 : G + m ≤ NH ∨ NH + m ≤ G)
    (d3 : G + m ≤ Db ∨ Db + n ≤ G) (w1 : G + m ≤ W) (w2 : KY + m ≤ W) (w3 : NH + m ≤ W)
    (w4 : Db + n ≤ W) (w5 : ∀ i < m, c.nmem (G + i) + c.nmem (Db + c.nmem (NH + i)) ≤ W)
    (w6 : m + 1 ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 9019 9000 (.seq nrLD1 nrLD2)) c c' t ∧ t ≤ 16 * m + 2 ∧
      (∀ i < m, c'.nmem (G + i) = c.nmem (G + i) + c.nmem (Db + c.nmem (NH + i)) -
        c.nmem (Db + c.nmem (KY + i))) ∧
      (∀ a, (a < G ∨ G + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 9019 ∨ 9024 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 9019 ∨ 9024 < x) → c'.nreg x = c.nreg x) ∧
    (∀ j < i, c'.nmem (G + j) = c.nmem (G + j) + c.nmem (Db + c.nmem (NH + j)) -
        c.nmem (Db + c.nmem (KY + j))) ∧
    (∀ a, (a < G ∨ G + i ≤ a) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', t, ex, ht, -, -, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 9019)
    (b := 9000) (body := .seq nrLD1 nrLD2) J (B := 14) c hc r19 r0 (Nat.zero_le _)
    ⟨fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c₁ _ hi hw h19 h0 ⟨f₁, s₁, o₁, q1, q2, q3⟩ => by
      obtain ⟨k1, k2⟩ := hK i hi
      have eK : c₁.nmem (KY + i) = c.nmem (KY + i) := o₁ _ (by omega)
      have eN : c₁.nmem (NH + i) = c.nmem (NH + i) := o₁ _ (by omega)
      have eG : c₁.nmem (G + i) = c.nmem (G + i) := o₁ _ (by omega)
      have eD1 : c₁.nmem (Db + c.nmem (NH + i)) = c.nmem (Db + c.nmem (NH + i)) :=
        o₁ _ (by omega)
      have eD2 : c₁.nmem (Db + c.nmem (KY + i)) = c.nmem (Db + c.nmem (KY + i)) :=
        o₁ _ (by omega)
      obtain ⟨c₂, t₂, e₂, ht₂, g20, g21, gn, gm, gr, grm, go⟩ := nrLD1_exec (P := P) c₁ hw
        (by rw [f₁ _ (by omega), r2]) (by rw [f₁ _ (by omega), r4])
        (by rw [f₁ _ (by omega), r17]) h19 (by omega) (by omega) (by rw [eN]; omega)
        (by rw [eN, eG, eD1]; exact w5 i hi)
      obtain ⟨c₃, t₃, e₃, ht₃, h19', hm, hn, hr, hrm, ho⟩ := nrLD2_exec (P := P) c₂ e₂.wb_right
        (by rw [gn _ (by omega), f₁ _ (by omega), r3])
        (by rw [gn _ (by omega), f₁ _ (by omega), r17])
        (by rw [gn _ (by omega), f₁ _ (by omega), r10]) (by rw [gn _ (by omega), h19])
        g20 g21 (by omega) (by rw [gm, eK]; omega) (by omega) (by omega)
      refine ⟨c₃, t₂ + t₃, .seq e₂ e₃, by omega, h19', by rw [hn _ (by omega), gn _ (by omega)]; exact h0,
        fun x hx => by rw [hn x (by omega), gn x (by omega), f₁ x hx], fun j hj => ?_,
        fun a ha => ?_, by rw [hr, gr, q1], by rw [hrm, grm, q2], by rw [ho, go, q3]⟩
      · rw [hm, gm, eK, eN, eG, eD1, eD2]
        by_cases e : j = i
        · subst e; rw [upd_same]
        · rw [upd_other _ _ _ (by omega)]; exact s₁ j (by omega)
      · rw [hm, gm, upd_other _ _ _ (by omega)]; exact o₁ a (by omega))
  exact ⟨c', t, ex, by omega, j2, fun a ha => j3 a (by omega), j1, j4, j5, j6⟩

end Loops

end BKMNW

end PlanarFlow
