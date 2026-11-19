module

public import PlanarFlow.BKMNW.Nf7cF

/-!
# The final step of `fixP`: the program and its machine phases

**`finP = finA ; finB ; finC`** (after the stage loop; for `k = 0` without it):

* `finA = fnL ; lnA ; lnB`: the layout of the final step from `T = r9469` (`LN = T`, `POT = T + m`,
  the root frame of the negative call `A' = T + 2m + 1`, its copy `Ob' = A' + 10 m + 6`, its log
  `p' = Ob' + 10 m + 6`) and the lengths `LN` (**`finA_exec`**: the three cases of a frame index:
  `PD l`, `RV PD l`, or off the path; `lnBM_at`);
* `finB = fnN ; negStep` (the registers of `negStep` and the call);
* `finC = fnH ; fnZ ; potP ; flP` (**`finC_exec`**): the header of the root frame and the outcome
  region (`m' = mem[A' + 1]`, `k' = mem[A' + 2]`, `R0 = Ob' + 4 + 5 k' + m'`, `w = mem[R0 + 1]`),
  `POT` zeroed, the potentials scattered by face identifier, the flow `FL`;
* `clrP`: clear the resident image and its shadow (four `mzFill`), before `finP` when `k > 0`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The programs -/

/-- The layout of the final step. -/
def fnL : Stmt := block [.copyN 9477 9469, .addN 9479 9477 9400, .addN 9480 9479 9400,
  .addN 9480 9480 9436, .constN 9498 10, .mulN 9497 9400 9498, .constN 9498 6,
  .addN 9497 9497 9498, .addN 9481 9480 9497, .addN 9482 9481 9497]

/-- The registers of `negStep`. -/
def fnN : Stmt := block [.copyN 7500 9400, .copyN 7501 9430, .copyN 7502 9431, .copyN 7503 9477,
  .copyN 7504 9310, .constN 7505 0, .copyN 7506 9480, .copyN 7322 9481, .copyN 7324 9482]

/-- The header of the root frame and the outcome region. -/
def fnH : Stmt := block [.addN 9497 9480 9436, .loadN 9485 9497, .addN 9497 9497 9436,
  .loadN 9486 9497, .constN 9498 5, .mulN 9487 9486 9498, .addN 9487 9487 9485,
  .constN 9498 4, .addN 9487 9487 9498, .addN 9487 9487 9481, .addN 9497 9487 9436,
  .loadN 9488 9497, .addN 9489 9497 9436, .addN 9490 9489 9485, .addN 9490 9490 9485]

/-- Zero the `m + 1` cells of `POT`. -/
def fnZ : Stmt := .seq (block [.copyN 5031 9479, .addN 5030 9400 9436]) mzFill

/-- Phase A: layout and lengths. -/
def finA : Stmt := .seq fnL (.seq lnA lnB)

/-- Phase B: the negative-length call. -/
def finB : Stmt := .seq fnN NsStep.negStep

/-- Phase C: the potentials and the flow. -/
def finC : Stmt := .seq fnH (.seq fnZ (.seq potP flP))

/-- **The final step of `fixP`.** -/
def finP : Stmt := .seq (.seq finA finB) finC

/-- Zero `sb = r7607` cells from `r[rb]`. -/
def clrK (rb : ℕ) : Stmt := .seq (block [.copyN 5030 7607, .copyN 5031 rb]) mzFill

/-- **Clear the resident image and its shadow.** -/
def clrP : Stmt := .seq (clrK 9475) (.seq (clrK 9471) (.seq (clrK 7612) (clrK 9474)))

/-! ### The final memory of `lnB` -/

/-- **The three cases of `lnBM`**, for distinct indices. -/
lemma lnBM_at (nm : ℕ → ℕ) {PDb RVb CWb CRb FWb LNb K : ℕ} :
    ∀ k : ℕ, (∀ l < k, ∀ l' < k, nm (PDb + l) ≠ nm (RVb + nm (PDb + l')) ∧
      (nm (PDb + l) = nm (PDb + l') → l = l') ∧
      (nm (RVb + nm (PDb + l)) = nm (RVb + nm (PDb + l')) → l = l')) →
    (∀ l < k, lnBM nm PDb RVb CWb CRb FWb LNb K k (LNb + nm (PDb + l)) =
      nm (CWb + l) + K + K - nm (FWb + l)) ∧
    (∀ l < k, lnBM nm PDb RVb CWb CRb FWb LNb K k (LNb + nm (RVb + nm (PDb + l))) =
      nm (CRb + l) + nm (FWb + l)) ∧
    (∀ i, (∀ l < k, nm (PDb + l) ≠ i ∧ nm (RVb + nm (PDb + l)) ≠ i) →
      lnBM nm PDb RVb CWb CRb FWb LNb K k (LNb + i) = nm (LNb + i))
  | 0, _ => ⟨fun l hl => absurd hl (by omega), fun l hl => absurd hl (by omega), fun i _ => rfl⟩
  | k + 1, hd => by
    obtain ⟨i1, i2, i3⟩ := lnBM_at nm k fun l hl l' hl' => hd l (by omega) l' (by omega)
    have dk := hd k (by omega) k (by omega)
    refine ⟨fun l hl => ?_, fun l hl => ?_, fun i hi => ?_⟩
    · simp only [lnBM]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | rfl
      · have d1 := hd l (by omega) k (by omega)
        have d2 := hd k (by omega) l (by omega)
        have n1 : nm (PDb + l) ≠ nm (RVb + nm (PDb + k)) := d1.1
        have n2 : nm (PDb + l) ≠ nm (PDb + k) := fun e => by have := d2.2.1 e.symm; omega
        rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        exact i1 l h
      · rw [upd_other _ _ _ (by have := dk.1; omega), upd_same]
    · simp only [lnBM]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | rfl
      · have d1 := hd l (by omega) k (by omega)
        have d2 := hd k (by omega) l (by omega)
        have n1 : nm (RVb + nm (PDb + l)) ≠ nm (RVb + nm (PDb + k)) := fun e => by
          have := d1.2.2 e; omega
        have n2 : nm (RVb + nm (PDb + l)) ≠ nm (PDb + k) := fun e => d2.1 e.symm
        rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        exact i2 l h
      · rw [upd_same]
    · simp only [lnBM]
      have h1 := hi k (by omega)
      rw [upd_other _ _ _ (by have := h1.2; omega), upd_other _ _ _ (by have := h1.1; omega)]
      exact i3 i fun l hl => hi l (by omega)

variable {P : Input} {W : ℕ}

/-! ### The blocks -/

set_option maxHeartbeats 1000000 in
theorem fnL_exec (c : Config) (hc : WordsBounded W c) {T m : ℕ} (r69 : c.nreg 9469 = T)
    (r00 : c.nreg 9400 = m) (r36 : c.nreg 9436 = 1) (hW : T + 22 * m + 13 ≤ W) :
    ∃ c' t, Exec P W fnL c c' t ∧ t = 10 ∧ c'.nreg 9477 = T ∧ c'.nreg 9479 = T + m ∧
      c'.nreg 9480 = T + m + m + 1 ∧ c'.nreg 9481 = T + m + m + 1 + (10 * m + 6) ∧
      c'.nreg 9482 = T + m + m + 1 + (10 * m + 6) + (10 * m + 6) ∧
      (∀ r, r ≠ 9477 → (r < 9479 ∨ 9482 < r) → r ≠ 9497 → r ≠ 9498 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fnL
  exec_block
  all_goals try ((try config_simp) <;> (try simp only [r69, r00, r36]) <;> omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r69, r00, r36])
  all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

theorem fnN_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W fnN c c' t ∧ t = 9 ∧ c'.nreg 7500 = c.nreg 9400 ∧
      c'.nreg 7501 = c.nreg 9430 ∧ c'.nreg 7502 = c.nreg 9431 ∧ c'.nreg 7503 = c.nreg 9477 ∧
      c'.nreg 7504 = c.nreg 9310 ∧ c'.nreg 7505 = 0 ∧ c'.nreg 7506 = c.nreg 9480 ∧
      c'.nreg 7322 = c.nreg 9481 ∧ c'.nreg 7324 = c.nreg 9482 ∧
      (∀ r, (r < 7500 ∨ 7506 < r) → r ≠ 7322 → r ≠ 7324 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fnN
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

set_option maxHeartbeats 1000000 in
theorem fnH_exec (c : Config) (hc : WordsBounded W c) {A Ob m' k' : ℕ}
    (r80 : c.nreg 9480 = A) (r81 : c.nreg 9481 = Ob) (r36 : c.nreg 9436 = 1)
    (hm' : c.nmem (A + 1) = m') (hk' : c.nmem (A + 1 + 1) = k')
    (hW : Ob + 4 + 5 * k' + m' + 2 + m' + m' + A + 2 ≤ W) :
    ∃ c' t, Exec P W fnH c c' t ∧ t = 15 ∧ c'.nreg 9485 = m' ∧
      c'.nreg 9488 = c.nmem (Ob + (4 + 5 * k' + m') + 1) ∧
      c'.nreg 9489 = Ob + (4 + 5 * k' + m') + 2 ∧
      c'.nreg 9490 = Ob + (4 + 5 * k' + m') + 2 + m' + m' ∧
      (∀ r, (r < 9485 ∨ 9490 < r) → r ≠ 9497 → r ≠ 9498 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hc' := hc
  unfold fnH
  exec_block
  all_goals try ((try config_simp) <;> (try simp only [r80, r81, r36, hm', hk']) <;>
    first | omega | exact hc.2.1 _)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r80, r81, r36, hm', hk'])
  all_goals first | omega | rfl | (congr 1; omega) | (repeat rw [upd_other _ _ _ (by omega)])

/-! ### Phase A -/

/-- **Phase A of the final step: the lengths `LN`.** -/
theorem finA_exec (c : Config) (hc : WordsBounded W c)
    {T m k CPb FLb Z K PDb RVb CWb CRb FWb : ℕ} (r69 : c.nreg 9469 = T)
    (r00 : c.nreg 9400 = m) (r36 : c.nreg 9436 = 1) (r34 : c.nreg 9434 = CPb)
    (r35 : c.nreg 9435 = FLb) (r21 : c.nreg 9421 = Z) (r10 : c.nreg 9310 = K)
    (r01 : c.nreg 9401 = k) (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = RVb)
    (r74 : c.nreg 9374 = CWb) (r75 : c.nreg 9375 = CRb) (r76 : c.nreg 9376 = FWb)
    (hPD : ∀ l < k, c.nmem (PDb + l) < m) (hRV : ∀ i < m, c.nmem (RVb + i) < m)
    (hdist : ∀ l < k, ∀ l' < k, c.nmem (PDb + l) ≠ c.nmem (RVb + c.nmem (PDb + l')) ∧
      (c.nmem (PDb + l) = c.nmem (PDb + l') → l = l') ∧
      (c.nmem (RVb + c.nmem (PDb + l)) = c.nmem (RVb + c.nmem (PDb + l')) → l = l'))
    (hlo : CPb + m ≤ T ∧ FLb + m ≤ T ∧ PDb + k ≤ T ∧ RVb + m ≤ T ∧ CWb + k ≤ T ∧ CRb + k ≤ T ∧
      FWb + k ≤ T)
    (hW : T + 22 * m + 13 + CPb + FLb + PDb + RVb + CWb + CRb + FWb + k ≤ W)
    (hv : ∀ i < m, c.nmem (CPb + i) + Z + K ≤ W) (hx : ∀ l < k, c.nmem (CWb + l) + K + K ≤ W)
    (hy : ∀ l < k, c.nmem (CRb + l) + c.nmem (FWb + l) ≤ W) :
    ∃ c' t, Exec P W finA c c' t ∧ t ≤ 12 * m + 21 * k + 16 ∧
      c'.nreg 9477 = T ∧ c'.nreg 9479 = T + m ∧ c'.nreg 9480 = T + m + m + 1 ∧
      c'.nreg 9481 = T + m + m + 1 + (10 * m + 6) ∧
      c'.nreg 9482 = T + m + m + 1 + (10 * m + 6) + (10 * m + 6) ∧
      (∀ l < k, c'.nmem (T + c.nmem (PDb + l)) = c.nmem (CWb + l) + K + K - c.nmem (FWb + l)) ∧
      (∀ l < k, c'.nmem (T + c.nmem (RVb + c.nmem (PDb + l))) =
        c.nmem (CRb + l) + c.nmem (FWb + l)) ∧
      (∀ i < m, (∀ l < k, c.nmem (PDb + l) ≠ i ∧ c.nmem (RVb + c.nmem (PDb + l)) ≠ i) →
        c'.nmem (T + i) = c.nmem (CPb + i) + Z + K - c.nmem (FLb + i)) ∧
      (∀ a, (a < T ∨ T + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 9477 → (r < 9479 ∨ 9490 < r) → (r < 9497 ∨ 9498 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hlo
  obtain ⟨c₁, t₁, e₁, ht₁, a77, a79, a80, a81, a82, ak, am, ar, arm, ao⟩ :=
    fnL_exec (P := P) c hc r69 r00 r36 (by omega)
  have k1 : ∀ r, (r < 9477 ∨ 9498 < r) → c₁.nreg r = c.nreg r := fun r hr =>
    ak r (by omega) (by omega) (by omega) (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, bLN, bK, bn, br, brm, bo⟩ :=
    lnA_exec (P := P) c₁ e₁.wb_right (m := m) (CPb := CPb) (FLWb := FLb) (Z := Z) (K := K)
      (LNb := T) (by rw [k1 _ (by omega), r00]) (by rw [k1 _ (by omega), r34])
      (by rw [k1 _ (by omega), r35]) (by rw [k1 _ (by omega), r21]) (by rw [k1 _ (by omega), r10])
      a77 (by rw [k1 _ (by omega), r36]) ⟨h1, h2⟩ (by omega) (fun i hi => by rw [am]; exact hv i hi)
  have m2 : ∀ a, (a < T ∨ T + m ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by rw [bK a ha, am]
  have k2 : ∀ r, (r < 9484 ∨ 9486 < r) → c₂.nreg r = c₁.nreg r := bn
  obtain ⟨c₃, t₃, e₃, ht₃, cm, cn, cr, crm, co⟩ :=
    lnB_exec (P := P) c₂ e₂.wb_right (m := m) (PDb := PDb) (RVb := RVb) (CWb := CWb) (CRb := CRb)
      (FWb := FWb) (LNb := T) (K := K)
      (by rw [k2 _ (by omega), k1 _ (by omega), r01]) (by rw [k2 _ (by omega), k1 _ (by omega), r02])
      (by rw [k2 _ (by omega), k1 _ (by omega), r30]) (by rw [k2 _ (by omega), k1 _ (by omega), r74])
      (by rw [k2 _ (by omega), k1 _ (by omega), r75]) (by rw [k2 _ (by omega), k1 _ (by omega), r76])
      (by rw [k2 _ (by omega), a77]) (by rw [k2 _ (by omega), k1 _ (by omega), r10])
      (by rw [k2 _ (by omega), k1 _ (by omega), r36])
      (fun l hl => by rw [m2 _ (Or.inl (by omega))]; exact hPD l hl)
      (fun i hi => by rw [m2 _ (Or.inl (by omega))]; exact hRV i hi) ⟨h3, h4, h5, h6, h7⟩
      (by omega) (fun l hl => by rw [m2 _ (Or.inl (by omega))]; exact hx l hl)
      (fun l hl => by rw [m2 _ (Or.inl (by omega)), m2 _ (Or.inl (by omega))]; exact hy l hl)
  -- the values read by `lnB` are those of `c`
  have ePD : ∀ l < k, c₂.nmem (PDb + l) = c.nmem (PDb + l) := fun l hl => m2 _ (Or.inl (by omega))
  have eRV : ∀ i < m, c₂.nmem (RVb + i) = c.nmem (RVb + i) := fun i hi => m2 _ (Or.inl (by omega))
  have hd2 : ∀ l < k, ∀ l' < k, c₂.nmem (PDb + l) ≠ c₂.nmem (RVb + c₂.nmem (PDb + l')) ∧
      (c₂.nmem (PDb + l) = c₂.nmem (PDb + l') → l = l') ∧
      (c₂.nmem (RVb + c₂.nmem (PDb + l)) = c₂.nmem (RVb + c₂.nmem (PDb + l')) → l = l') :=
    fun l hl l' hl' => by
      rw [ePD l hl, ePD l' hl', eRV _ (hPD l hl), eRV _ (hPD l' hl')]; exact hdist l hl l' hl'
  obtain ⟨j1, j2, j3⟩ := lnBM_at c₂.nmem (CWb := CWb) (CRb := CRb) (FWb := FWb) (LNb := T)
    (K := K) k hd2
  refine ⟨c₃, _, e₁.seq (e₂.seq e₃), by omega, ?_, ?_, ?_, ?_, ?_, fun l hl => ?_, fun l hl => ?_,
    fun i hi hn => ?_, fun a ha => ?_, fun r g1 g2 g3 => ?_, by rw [cr, br, ar],
    by rw [crm, brm, arm], by rw [co, bo, ao]⟩
  · rw [cn _ (by omega), k2 _ (by omega), a77]
  · rw [cn _ (by omega), k2 _ (by omega), a79]
  · rw [cn _ (by omega), k2 _ (by omega), a80]
  · rw [cn _ (by omega), k2 _ (by omega), a81]
  · rw [cn _ (by omega), k2 _ (by omega), a82]
  · have := j1 l hl
    rw [ePD l hl, m2 _ (Or.inl (by omega)), m2 _ (Or.inl (by omega))] at this
    rw [cm, this]
  · have := j2 l hl
    rw [ePD l hl, eRV _ (hPD l hl), m2 _ (Or.inl (by omega)), m2 _ (Or.inl (by omega))] at this
    rw [cm, this]
  · rw [cm, j3 i (fun l hl => by rw [ePD l hl, eRV _ (hPD l hl)]; exact hn l hl), bLN i hi, am]
  · rw [cm, lnBM_out _ (m := m) (fun l hl => by rw [ePD l hl]; exact hPD l hl)
      (fun i hi => by rw [eRV i hi]; exact hRV i hi) ha, m2 a ha]
  · rw [cn r (by omega), k2 r (by omega), ak r g1 (by omega) (by omega) (by omega)]

end BKMNW

end PlanarFlow
