module

public import PlanarFlow.BKMNW.Nf7cH
public import PlanarFlow.BKMNW.Nf7eWD

/-!
# Per-address word bounds for the final-step phases A and C

Copies of `fnH_exec`, `finA_exec` (`T + 22m + 13 ≤ W`, the top of the final step's layout below
the log), `finC_exec` (`Ob + 5k' + 5m' + 6 ≤ W`, the top of the outcome region) with suffix `W`;
all other addresses are below these by the layout hypotheses. Same programs and conclusions.
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

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1000000 in
theorem fnH_execW (c : Config) (hc : WordsBounded W c) {A Ob m' k' : ℕ}
    (r80 : c.nreg 9480 = A) (r81 : c.nreg 9481 = Ob) (r36 : c.nreg 9436 = 1)
    (hm' : c.nmem (A + 1) = m') (hk' : c.nmem (A + 1 + 1) = k')
    (hW : Ob + 4 + 5 * k' + m' + 2 + m' + m' ≤ W ∧ A + 2 ≤ W) :
    ∃ c' t, Exec P W fnH c c' t ∧ t = 15 ∧ c'.nreg 9485 = m' ∧
      c'.nreg 9488 = c.nmem (Ob + (4 + 5 * k' + m') + 1) ∧
      c'.nreg 9489 = Ob + (4 + 5 * k' + m') + 2 ∧
      c'.nreg 9490 = Ob + (4 + 5 * k' + m') + 2 + m' + m' ∧
      (∀ r, (r < 9485 ∨ 9490 < r) → r ≠ 9497 → r ≠ 9498 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hWa, hWb⟩ := hW
  have hc' := hc
  unfold fnH
  exec_block
  all_goals try ((try config_simp) <;> (try simp only [r80, r81, r36, hm', hk']) <;>
    first | omega | exact hc.2.1 _)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r80, r81, r36, hm', hk'])
  all_goals first | omega | rfl | (congr 1; omega) | (repeat rw [upd_other _ _ _ (by omega)])

/-- **Phase A of the final step: the lengths `LN`.** -/
theorem finA_execW (c : Config) (hc : WordsBounded W c)
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
    (hW : T + 22 * m + 13 ≤ W)
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
    lnA_execW (P := P) c₁ e₁.wb_right (m := m) (CPb := CPb) (FLWb := FLb) (Z := Z) (K := K)
      (LNb := T) (by rw [k1 _ (by omega), r00]) (by rw [k1 _ (by omega), r34])
      (by rw [k1 _ (by omega), r35]) (by rw [k1 _ (by omega), r21]) (by rw [k1 _ (by omega), r10])
      a77 (by rw [k1 _ (by omega), r36]) ⟨h1, h2⟩ (by omega) (fun i hi => by rw [am]; exact hv i hi)
  have m2 : ∀ a, (a < T ∨ T + m ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by rw [bK a ha, am]
  have k2 : ∀ r, (r < 9484 ∨ 9486 < r) → c₂.nreg r = c₁.nreg r := bn
  obtain ⟨c₃, t₃, e₃, ht₃, cm, cn, cr, crm, co⟩ :=
    lnB_execW (P := P) c₂ e₂.wb_right (m := m) (PDb := PDb) (RVb := RVb) (CWb := CWb) (CRb := CRb)
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

set_option maxHeartbeats 1000000 in
/-- **Phase C of the final step: the potentials and the flow.** -/
theorem finC_execW (c : Config) (hc : WordsBounded W c)
    {T m A Ob m' k' w CPb RVb LABb FLb Z K B : ℕ}
    (r77 : c.nreg 9477 = T) (r79 : c.nreg 9479 = T + m) (r80 : c.nreg 9480 = A)
    (r81 : c.nreg 9481 = Ob) (r00 : c.nreg 9400 = m) (r36 : c.nreg 9436 = 1)
    (r34 : c.nreg 9434 = CPb) (r30 : c.nreg 9430 = RVb) (r05 : c.nreg 9405 = LABb)
    (r35 : c.nreg 9435 = FLb) (r21 : c.nreg 9421 = Z) (r10 : c.nreg 9310 = K)
    (hm' : c.nmem (A + 1) = m') (hk' : c.nmem (A + 1 + 1) = k')
    (hw : c.nmem (Ob + (4 + 5 * k' + m') + 1) = w) (hwm : w ≤ 2 * m')
    (hid : ∀ v < w, c.nmem (Ob + (4 + 5 * k' + m') + 2 + v) < m)
    (hRV : ∀ i < m, c.nmem (RVb + i) < m) (hLAB : ∀ i < m, c.nmem (LABb + i) ≤ m)
    (hlay : T + m + (m + 1) ≤ A ∧ A + 3 ≤ Ob ∧ RVb + m ≤ CPb ∧ CPb + m ≤ FLb ∧
      FLb + m ≤ LABb ∧ LABb + m ≤ T)
    (hW : Ob + 5 * k' + 5 * m' + 6 ≤ W)
    (hVL : ∀ v < w, c.nmem (Ob + (4 + 5 * k' + m') + 2 + m' + m' + v) ≤ B)
    (h4 : ∀ i < m, c.nmem (CPb + i) + Z + K + K + B ≤ W) (h5 : B + K ≤ W) :
    ∃ c' t, Exec P W finC c c' t ∧ t ≤ 10 * w + 31 * m + 35 ∧
      (∀ i < m, c'.nmem (FLb + i) = flV (potM (potZ c.nmem (T + m) m)
        (Ob + (4 + 5 * k' + m') + 2) (Ob + (4 + 5 * k' + m') + 2 + m' + m') (T + m) w)
        CPb RVb LABb (T + m) T Z K i) ∧
      (∀ a, (a < T + m ∨ T + m + (m + 1) ≤ a) → (a < FLb ∨ FLb + m ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 5030 ∨ 5035 < r) → (r < 9485 ∨ 9498 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hlay
  set R0 := Ob + (4 + 5 * k' + m') with hR0
  obtain ⟨c₁, t₁, e₁, ht₁, a85, a88, a89, a90, ak, am, ar, arm, ao⟩ :=
    fnH_execW (P := P) c hc r80 r81 r36 hm' hk' (by omega)
  have k1 : ∀ r, (r < 9485 ∨ 9498 < r) → c₁.nreg r = c.nreg r := fun r hr =>
    ak r (by omega) (by omega) (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, bm, bn, br, brm, bo⟩ :=
    fnZ_exec (P := P) c₁ e₁.wb_right (POTb := T + m) (m := m) (by rw [k1 _ (by omega), r79])
      (by rw [k1 _ (by omega), r00]) (by rw [k1 _ (by omega), r36]) (by omega)
  rw [am] at bm
  have k2 : ∀ r, (r < 5030 ∨ 5035 < r) → (r < 9485 ∨ 9498 < r) → c₂.nreg r = c.nreg r :=
    fun r h1 h2 => by rw [bn r h1, k1 r h2]
  have m2 : ∀ a, (a < T + m ∨ T + m + (m + 1) ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [bm]; unfold potZ; split_ifs with h
    · omega
    · rfl
  obtain ⟨c₃, t₃, e₃, ht₃, cm, cn, cr, crm, co⟩ :=
    potP_execW (P := P) c₂ e₂.wb_right (w := w) (G := m) (IDb := R0 + 2) (VLb := R0 + 2 + m' + m')
      (POTb := T + m) (by rw [bn _ (by omega), a88, hw]) (by rw [bn _ (by omega), a89])
      (by rw [bn _ (by omega), a90]) (by rw [k2 _ (by omega) (by omega), r79])
      (by rw [k2 _ (by omega) (by omega), r36])
      (fun v hv => by rw [m2 _ (Or.inr (by omega))]; exact hid v hv)
      ⟨Or.inr (by omega), Or.inr (by omega)⟩ (by omega)
  have k3 : ∀ r, (r < 5030 ∨ 5035 < r) → (r < 9485 ∨ 9498 < r) → c₃.nreg r = c.nreg r :=
    fun r h1 h2 => by rw [cn r (by omega), k2 r h1 h2]
  have eM : c₃.nmem = potM (potZ c.nmem (T + m) m) (R0 + 2) (R0 + 2 + m' + m') (T + m) w := by
    rw [cm, bm]
  have m3 : ∀ a, (a < T + m ∨ T + m + (m + 1) ≤ a) → c₃.nmem a = c.nmem a := fun a ha => by
    rw [cm, potM_out _ (G := m) (fun v hv => by rw [m2 _ (Or.inr (by omega))]; exact hid v hv)
      (by omega), m2 a ha]
  have hPOT : ∀ x ≤ m, c₃.nmem (T + m + x) ≤ B := fun x hx => by
    rw [eM]
    refine potM_le _ ?_ fun v hv => ?_
    · unfold potZ; split_ifs with h
      · omega
      · omega
    · unfold potZ; split_ifs with h
      · omega
      · exact hVL v hv
  obtain ⟨c₄, t₄, e₄, ht₄, d1, dk, dn, dr, drm, dO⟩ :=
    flP_execW (P := P) c₃ e₃.wb_right (m := m) (CPb := CPb) (RVb := RVb) (LABb := LABb)
      (POTb := T + m) (LNb := T) (FLb := FLb) (Z := Z) (K := K) (G := m)
      (by rw [k3 _ (by omega) (by omega), r00]) (by rw [k3 _ (by omega) (by omega), r34])
      (by rw [k3 _ (by omega) (by omega), r30]) (by rw [k3 _ (by omega) (by omega), r05])
      (by rw [k3 _ (by omega) (by omega), r79]) (by rw [k3 _ (by omega) (by omega), r77])
      (by rw [k3 _ (by omega) (by omega), r35]) (by rw [k3 _ (by omega) (by omega), r21])
      (by rw [k3 _ (by omega) (by omega), r10]) (by rw [k3 _ (by omega) (by omega), r36])
      (fun i hi => by rw [m3 _ (Or.inl (by omega))]; exact hRV i hi)
      (fun i hi => by rw [m3 _ (Or.inl (by omega))]; exact hLAB i hi)
      (fun a h1 h2 => ⟨by omega, by omega, by omega, by omega, by omega⟩) (by omega)
      (fun i hi => by
        have hr := hRV i hi
        have hl := hLAB _ hr
        have eR : c₃.nmem (RVb + i) = c.nmem (RVb + i) := m3 _ (Or.inl (by omega))
        have eL : c₃.nmem (LABb + c.nmem (RVb + i)) = c.nmem (LABb + c.nmem (RVb + i)) :=
          m3 _ (Or.inl (by omega))
        have eC : c₃.nmem (CPb + i) = c.nmem (CPb + i) := m3 _ (Or.inl (by omega))
        have hp := hPOT _ hl
        rw [eC, eR, eL]
        have := h4 i hi
        omega)
      (fun i hi => by
        have eL : c₃.nmem (LABb + i) = c.nmem (LABb + i) := m3 _ (Or.inl (by omega))
        have hp := hPOT _ (hLAB i hi)
        rw [eL]
        omega)
  refine ⟨c₄, _, e₁.seq (e₂.seq (e₃.seq e₄)), by omega, fun i hi => ?_, fun a h1 h2 => ?_,
    fun r h1 h2 => ?_, by rw [dr, cr, br, ar], by rw [drm, crm, brm, arm],
    by rw [dO, co, bo, ao]⟩
  · rw [d1 i hi, eM]
  · rw [dk a h2, m3 a h1]
  · rw [dn r (by omega), k3 r h1 h2]

end BKMNW

end PlanarFlow
