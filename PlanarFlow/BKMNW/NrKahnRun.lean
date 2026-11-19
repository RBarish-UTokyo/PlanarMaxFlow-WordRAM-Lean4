module

public import PlanarFlow.BKMNW.NrKahn
public import PlanarFlow.BKMNW.NrPassRun

/-!
# Kahn's algorithm on the machine: the loops before the main loop

With the arrays `VL`, `RV`, `G` of the memory `mem₀` (`kvl`, `khd`, `kps`):

* `kZL_exec` (`IND := 0`), `kPL_exec` (`POS[j] = kps j`, `IND[w]` = the positive darts entering
  `w`), `kSL_exec` (the scan: the queue lists the vertices without entering positive dart).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

/-- The vertex label of `v`. -/
def kvl (mem : ℕ → ℕ) (VL v : ℕ) : ℕ := mem (VL + v)

/-- The head label of the dart `j`. -/
def khd (mem : ℕ → ℕ) (VL RV j : ℕ) : ℕ := mem (VL + mem (RV + j))

/-- The positivity flag of the dart `j`. -/
def kps (mem : ℕ → ℕ) (G Z j : ℕ) : ℕ := if Z < mem (G + j) then 1 else 0

variable {P : Input} {W : ℕ}

/-- **The zero loop** `IND[i] := 0`. -/
theorem kZL_exec (c : Config) (hc : WordsBounded W c) {A m : ℕ} (r0 : c.nreg 9100 = m)
    (r8 : c.nreg 9108 = A) (r15 : c.nreg 9115 = 0) (r6 : c.nreg 9106 = 1)
    (r7 : c.nreg 9107 = 0) (w : A + m + 1 ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 9115 9100 kahnZ) c c' t ∧ t ≤ 5 * m + 2 ∧
      (∀ i < m, c'.nmem (A + i) = 0) ∧ (∀ a, (a < A ∨ A + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 9115 → x ≠ 9116 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, x ≠ 9115 → x ≠ 9116 → c'.nreg x = c.nreg x) ∧ (∀ j < i, c'.nmem (A + j) = 0) ∧
    (∀ a, (a < A ∨ A + i ≤ a) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', t, ex, ht, -, -, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 9115)
    (b := 9100) (body := kahnZ) J (B := 3) c hc r15 r0 (Nat.zero_le _)
    ⟨fun _ _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c₁ _ hi hw h15 h0 ⟨f₁, z₁, o₁, q1, q2, q3⟩ => by
      obtain ⟨c₂, t₂, e₂, ht₂, g15, gm, gn, gr, grm, go⟩ := kahnZ_exec (P := P) c₁ hw
        (by rw [f₁ _ (by omega) (by omega), r8]) h15 (by rw [f₁ _ (by omega) (by omega), r6])
        (by rw [f₁ _ (by omega) (by omega), r7]) (by omega)
      refine ⟨c₂, t₂, e₂, ht₂.le, g15, by rw [gn _ (by omega) (by omega)]; exact h0,
        fun x h1 h2 => by rw [gn x h1 h2, f₁ x h1 h2], fun j hj => ?_, fun a ha => ?_,
        by rw [gr, q1], by rw [grm, q2], by rw [go, q3]⟩
      · rw [gm]
        by_cases e : j = i
        · subst e; rw [upd_same]
        · rw [upd_other _ _ _ (by omega)]; exact z₁ j (by omega)
      · rw [gm, upd_other _ _ _ (by omega)]; exact o₁ a (by omega))
  exact ⟨c', t, ex, by omega, j2, fun a ha => j3 a (by omega), j1, j4, j5, j6⟩

/-- The number of positive darts among the first `i` entering `w`. -/
def kCnt (mem : ℕ → ℕ) (VL RV G Z : ℕ) (i w : ℕ) : ℕ :=
  ((range i).filter fun j => kps mem G Z j ≠ 0 ∧ khd mem VL RV j = w).card

lemma kCnt_succ (mem : ℕ → ℕ) (VL RV G Z i w : ℕ) :
    kCnt mem VL RV G Z (i + 1) w = kCnt mem VL RV G Z i w +
      (if kps mem G Z i ≠ 0 ∧ khd mem VL RV i = w then 1 else 0) := by
  unfold kCnt
  rw [Finset.range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

lemma kCnt_le (mem : ℕ → ℕ) (VL RV G Z i w : ℕ) : kCnt mem VL RV G Z i w ≤ i :=
  (card_filter_le _ _).trans (by simp)

/-- **Loop P**: `POS[j] = kps j`, `IND[w] = kCnt m w`. -/
theorem kPL_exec (c : Config) (hc : WordsBounded W c) {m VL RV G Z S : ℕ}
    (r0 : c.nreg 9100 = m) (r1 : c.nreg 9101 = VL) (r2 : c.nreg 9102 = RV)
    (r3 : c.nreg 9103 = G) (r4 : c.nreg 9104 = Z) (r5 : c.nreg 9105 = S)
    (r6 : c.nreg 9106 = 1) (r7 : c.nreg 9107 = 0) (r8 : c.nreg 9108 = S + m)
    (r15 : c.nreg 9115 = 0) (hz : ∀ w < m, c.nmem (S + m + w) = 0)
    (hRV : ∀ j < m, c.nmem (RV + j) < m) (hVL : ∀ j < m, c.nmem (VL + j) < m)
    (dV : NrSep VL m S (2 * m)) (dR : NrSep RV m S (2 * m)) (dG : NrSep G m S (2 * m))
    (wS : S + 2 * m + 1 ≤ W) (wV : VL + m ≤ W) (wR : RV + m ≤ W) (wG : G + m ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 9115 9100 kP) c c' t ∧ t ≤ 17 * m + 2 ∧
      (∀ j < m, c'.nmem (S + j) = kps c.nmem G Z j) ∧
      (∀ w < m, c'.nmem (S + m + w) = kCnt c.nmem VL RV G Z m w) ∧
      (∀ a, (a < S ∨ S + 2 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 9115 ∨ 9119 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 9115 ∨ 9119 < x) → c'.nreg x = c.nreg x) ∧
    (∀ j < i, c'.nmem (S + j) = kps c.nmem G Z j) ∧
    (∀ w < m, c'.nmem (S + m + w) = kCnt c.nmem VL RV G Z i w) ∧
    (∀ a, (a < S ∨ S + 2 * m ≤ a) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', t, ex, ht, -, -, j1, j2, j3, j4, j5, j6, j7⟩ := lnRange (P := P) (a := 9115)
    (b := 9100) (body := kP) J (B := 15) c hc r15 r0 (Nat.zero_le _)
    ⟨fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun w hw => by rw [hz w hw]; simp [kCnt], fun _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c₁ _ hi hw h15 h0 ⟨f₁, p₁, s₁, o₁, q1, q2, q3⟩ => by
      have eR : c₁.nmem (RV + i) = c.nmem (RV + i) := o₁ _ (by rcases dR with h | h <;> omega)
      have hr := hRV i hi
      have eV : c₁.nmem (VL + c.nmem (RV + i)) = c.nmem (VL + c.nmem (RV + i)) :=
        o₁ _ (by rcases dV with h | h <;> omega)
      have hv := hVL _ hr
      have eG : c₁.nmem (G + i) = c.nmem (G + i) := o₁ _ (by rcases dG with h | h <;> omega)
      have hcnt := s₁ _ hv
      have hcl := kCnt_le c.nmem VL RV G Z i (c.nmem (VL + c.nmem (RV + i)))
      obtain ⟨c₂, t₂, e₂, ht₂, g15, gm, gn, gr, grm, go⟩ := kP_exec (P := P) c₁ hw
        (VL := VL) (RV := RV) (G := G) (Z := Z) (S := S) (A := S + m) (i := i)
        (by rw [f₁ _ (by omega), r1]) (by rw [f₁ _ (by omega), r2])
        (by rw [f₁ _ (by omega), r3]) (by rw [f₁ _ (by omega), r4])
        (by rw [f₁ _ (by omega), r5]) (by rw [f₁ _ (by omega), r6])
        (by rw [f₁ _ (by omega), r7]) (by rw [f₁ _ (by omega), r8]) h15 (by omega) (by omega)
        (by omega) (by rw [eR]; omega) (by rw [eR, eV]; omega) (by rw [eR, eV, hcnt]; omega)
        (by omega) (by rw [eR, eV]; omega)
      rw [eR, eV, eG] at gm
      refine ⟨c₂, t₂, e₂, ht₂, g15, by rw [gn _ (by omega)]; exact h0,
        fun x hx => by rw [gn x hx, f₁ x hx], fun j hj => ?_, fun w hw' => ?_, fun a ha => ?_,
        by rw [gr, q1], by rw [grm, q2], by rw [go, q3]⟩
      · rw [gm]
        by_cases e : j = i
        · subst e; split_ifs with hz' <;> simp [upd_same, kps, hz']
        · split_ifs
          · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact p₁ j (by omega)
          · rw [upd_other _ _ _ (by omega)]; exact p₁ j (by omega)
      · rw [kCnt_succ]
        have e1 : khd c.nmem VL RV i = c.nmem (VL + c.nmem (RV + i)) := rfl
        by_cases hz' : Z < c.nmem (G + i)
        · rw [if_pos hz'] at gm
          rw [gm, upd_other _ _ _ (by omega)]
          by_cases e : w = c.nmem (VL + c.nmem (RV + i))
          · subst e
            rw [upd_same, hcnt, if_pos ⟨by simp [kps, hz'], e1⟩]
          · have : ¬ (kps c.nmem G Z i ≠ 0 ∧ khd c.nmem VL RV i = w) := fun h' =>
              e (h'.2.symm.trans e1)
            rw [upd_other _ _ _ (fun h' => e (by omega)), s₁ w hw', if_neg this, Nat.add_zero]
        · rw [if_neg hz'] at gm
          have : ¬ (kps c.nmem G Z i ≠ 0 ∧ khd c.nmem VL RV i = w) := fun h' =>
            h'.1 (by simp [kps, hz'])
          rw [gm, upd_other _ _ _ (by omega), s₁ w hw', if_neg this, Nat.add_zero]
      · rw [gm]
        split_ifs
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact o₁ a ha
        · rw [upd_other _ _ _ (by omega)]; exact o₁ a ha)
  exact ⟨c', t, ex, by omega, j2, j3, j4, j1, j5, j6, j7⟩

/-- The queue after the scan of the labels below `i`. -/
def kScanL (vl ind : ℕ → ℕ) (i : ℕ) : List ℕ :=
  (List.range i).filter fun v => decide (vl v = v ∧ ind v = 0)

/-- **The scan**: the queue lists the labels `v < m` with `VL[v] = v` and `IND[v] = 0`. -/
theorem kSL_exec (c : Config) (hc : WordsBounded W c) {m VL A Qb : ℕ}
    (r0 : c.nreg 9100 = m) (r1 : c.nreg 9101 = VL) (r6 : c.nreg 9106 = 1)
    (r7 : c.nreg 9107 = 0) (r8 : c.nreg 9108 = A) (r9 : c.nreg 9109 = Qb)
    (r15 : c.nreg 9115 = 0) (r20 : c.nreg 9120 = 0)
    (hVL : ∀ v < m, c.nmem (VL + v) ≤ v) (dV : NrSep VL m Qb m) (dA : NrSep A m Qb m)
    (wV : VL + m ≤ W) (wA : A + m ≤ W) (wQ : Qb + m + 1 ≤ W) :
    ∃ c' t', Exec P W (.whileLtN 9115 9100 kS) c c' t' ∧ t' ≤ 16 * m + 2 ∧
      ∃ t, c'.nreg 9120 = t ∧ t ≤ m ∧
        kQ (fun k => c'.nmem (Qb + k)) t =
          kScanL (fun v => c.nmem (VL + v)) (fun v => c.nmem (A + v)) m ∧
        (∀ a, (a < Qb ∨ Qb + m ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ x, (x < 9115 ∨ 9120 < x) → c'.nreg x = c.nreg x) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 9115 ∨ 9120 < x) → c'.nreg x = c.nreg x) ∧
    (∃ t, c'.nreg 9120 = t ∧ t ≤ i ∧ kQ (fun k => c'.nmem (Qb + k)) t =
      kScanL (fun v => c.nmem (VL + v)) (fun v => c.nmem (A + v)) i) ∧
    (∀ a, (a < Qb ∨ Qb + i ≤ a) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', t', ex, ht, -, -, j1, ⟨t, j2, j3, j4⟩, j5, j6, j7, j8⟩ := lnRange (P := P)
    (a := 9115) (b := 9100) (body := kS) J (B := 14) c hc r15 r0 (Nat.zero_le _)
    ⟨fun _ _ => rfl, ⟨0, r20, le_rfl, by simp [kQ, kScanL]⟩, fun _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c₁ _ hi hw h15 h0 ⟨f₁, ⟨t, ht1, ht2, hq⟩, o₁, q1, q2, q3⟩ => by
      have eV : c₁.nmem (VL + i) = c.nmem (VL + i) := o₁ _ (by rcases dV with h | h <;> omega)
      have eA : c₁.nmem (A + i) = c.nmem (A + i) := o₁ _ (by rcases dA with h | h <;> omega)
      obtain ⟨c₂, t₂, e₂, ht₂, g15, gif, gn, gr, grm, go⟩ := kS_exec (P := P) c₁ hw
        (VL := VL) (A := A) (Qb := Qb) (i := i) (t := t)
        (by rw [f₁ _ (by omega), r1]) (by rw [f₁ _ (by omega), r6])
        (by rw [f₁ _ (by omega), r7]) (by rw [f₁ _ (by omega), r8])
        (by rw [f₁ _ (by omega), r9]) h15 ht1 (by omega) (by omega) (by omega) (by omega)
      rw [eV, eA] at gif
      have hsucc : kScanL (fun v => c.nmem (VL + v)) (fun v => c.nmem (A + v)) (i + 1) =
          kScanL (fun v => c.nmem (VL + v)) (fun v => c.nmem (A + v)) i ++
            (if c.nmem (VL + i) = i ∧ c.nmem (A + i) = 0 then [i] else []) := by
        simp only [kScanL, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
        split_ifs <;> simp_all
      have hle := hVL i hi
      refine ⟨c₂, t₂, e₂, ht₂, g15, by rw [gn _ (by omega)]; exact h0,
        fun x hx => by rw [gn x hx, f₁ x hx], ?_, ?_, by rw [gr, q1], by rw [grm, q2],
        by rw [go, q3]⟩
      · split_ifs at gif with hcond
        · obtain ⟨g20, gm⟩ := gif
          refine ⟨t, g20, by omega, ?_⟩
          rw [hsucc, if_neg (by omega), List.append_nil, ← hq]
          simp only [kQ, gm]
        · obtain ⟨g20, gm⟩ := gif
          refine ⟨t + 1, g20, by omega, ?_⟩
          rw [hsucc, if_pos (by omega), kQ_succ, ← hq]
          simp only [kQ, gm, upd_same]
          congr 1
          exact List.map_congr_left fun k hk => by
            rw [upd_other _ _ _ (by have := List.mem_range.1 hk; omega)]
      · intro a ha
        split_ifs at gif with hcond
        · rw [gif.2]; exact o₁ a (by omega)
        · rw [gif.2, upd_other _ _ _ (by omega)]; exact o₁ a (by omega))
  exact ⟨c', t', ex, by omega, t, j2, by omega, j4, fun a ha => j5 a (by omega), j1, j6, j7, j8⟩

end BKMNW

end PlanarFlow
