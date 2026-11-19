module

public import PlanarFlow.BKMNW.NcScan
public import PlanarFlow.BKMNW.IteR23

/-!
# The run of the scan `scP`

**`scP_exec`**: see `NcScan.lean`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

variable {P : Input} {W : ℕ}

theorem scInit_exec (c : Config) (hc : WordsBounded W c) (h1 : 1 ≤ W) :
    ∃ c' k, Exec P W (block [.constN 9730 0, .constN 9731 1]) c c' k ∧ k = 2 ∧
      c'.nreg 9730 = 0 ∧ c'.nreg 9731 = 1 ∧ (∀ r, r ≠ 9730 → r ≠ 9731 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

/-- **The capacity and excess scan.** -/
theorem scP_exec (c : Config) (hc : WordsBounded W c) {m CFb MKb RVb CPb FLb LABb DVb DGb CAPb
    BTb Z : ℕ}
    (r32 : c.nreg 9732 = CFb) (r33 : c.nreg 9733 = MKb) (r34 : c.nreg 9734 = RVb)
    (r35 : c.nreg 9735 = CPb) (r36 : c.nreg 9736 = FLb) (r37 : c.nreg 9737 = LABb)
    (r38 : c.nreg 9738 = DVb) (r39 : c.nreg 9739 = DGb) (r40 : c.nreg 9740 = CAPb)
    (r41 : c.nreg 9741 = BTb) (r42 : c.nreg 9742 = Z) (r43 : c.nreg 9743 = m)
    (hcf : ∀ i < m, c.nmem (CFb + i) ≤ 1) (hmk : ∀ i < m, c.nmem (MKb + i) ≤ 1)
    (hrv : ∀ i < m, c.nmem (RVb + i) < m) (hlab : ∀ i < m, 1 ≤ c.nmem (LABb + i) ∧
      c.nmem (LABb + i) ≤ m)
    (hcp : ∀ i < m, c.nmem (CPb + i) + Z ≤ W) (hdg : ∀ l < m, c.nmem (DGb + l) * Z ≤ W)
    (o1 : CFb + m ≤ CAPb) (o2 : MKb + m ≤ CAPb) (o3 : RVb + m ≤ CAPb) (o4 : CPb + m ≤ CAPb)
    (o5 : FLb + m ≤ CAPb) (o6 : LABb + m ≤ CAPb) (o7 : DVb + m ≤ CAPb) (o8 : DGb + m ≤ CAPb)
    (o9 : CAPb + m ≤ BTb) (w1 : BTb + m ≤ W) (h1 : 1 ≤ W) :
    ∃ c' k, Exec P W scP c c' k ∧ k ≤ 40 * m + 4 ∧
      (∀ i < m, c'.nmem (CAPb + i) = scCap c.nmem CFb MKb RVb CPb FLb Z i) ∧
      (∀ i < m, c'.nmem (BTb + i) = scBt c.nmem CFb MKb LABb DVb DGb Z i) ∧
      (∀ a, (a < CAPb ∨ BTb + m ≤ a ∨ (CAPb + m ≤ a ∧ a < BTb)) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ ScScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a30, a31, f₁, m₁, rr₁, rm₁, o₁⟩ := scInit_exec (P := P) c hc h1
  have g₁ : ∀ r, 9732 ≤ r → r ≤ 9743 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    f₁ r (by omega) (by omega)
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (CAPb + e) = scCap c.nmem CFb MKb RVb CPb FLb Z e) ∧
      (∀ e < i, c'.nmem (BTb + e) = scBt c.nmem CFb MKb LABb DVb DGb Z e) ∧
      (∀ a, (a < CAPb ∨ BTb + i ≤ a ∨ (CAPb + i ≤ a ∧ a < BTb)) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ ScScr r → c'.nreg r = c.nreg r) ∧ c'.nreg 9731 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have hJ0 : J 0 c₁ := ⟨fun e he => absurd he (by omega), fun e he => absurd he (by omega),
    fun a _ => by rw [m₁], fun r hr => f₁ r (fun h => hr (Or.inl (Or.inl h)))
      (fun h => hr (Or.inl (Or.inr h))), a31, rr₁, rm₁, o₁⟩
  obtain ⟨c₂, k₂, e₂, hk₂, -, j1, j2, j3, j4, -, jr, jrm, jo⟩ := forLoop_exec (P := P)
    (a := 9730) (bR := 9743) (body := scB) J (K := 38) (n := m) c₁ e₁.wb_right a30
    (by rw [g₁ _ (by omega) (by omega), r43]) hJ0
    (fun i c' hi hw ha hb ⟨j1, j2, j3, j4, j31, jr, jrm, jo⟩ => by
      have q : ∀ r, 9732 ≤ r → r ≤ 9743 → c'.nreg r = c.nreg r := fun r h1 h2 =>
        j4 r (by unfold ScScr; omega)
      have rd : ∀ a, a < CAPb → c'.nmem a = c.nmem a := fun a h => j3 a (Or.inl h)
      have hRV := hrv i hi
      have hL := hlab i hi
      obtain ⟨c'', k, ex, hk, hm, h30, hn, hr, hrm, ho⟩ := scB_exec (P := P) c' hw
        (CFb := CFb) (MKb := MKb) (RVb := RVb) (CPb := CPb) (FLb := FLb) (LABb := LABb)
        (DVb := DVb) (DGb := DGb) (CAPb := CAPb) (BTb := BTb) (Z := Z) ha j31
        (by rw [q _ (by omega) (by omega), r32]) (by rw [q _ (by omega) (by omega), r33])
        (by rw [q _ (by omega) (by omega), r34]) (by rw [q _ (by omega) (by omega), r35])
        (by rw [q _ (by omega) (by omega), r36]) (by rw [q _ (by omega) (by omega), r37])
        (by rw [q _ (by omega) (by omega), r38]) (by rw [q _ (by omega) (by omega), r39])
        (by rw [q _ (by omega) (by omega), r40]) (by rw [q _ (by omega) (by omega), r41])
        (by rw [q _ (by omega) (by omega), r42])
        (by rw [rd _ (by omega)]; exact hcf i hi) (by rw [rd _ (by omega)]; exact hmk i hi)
        (by rw [rd (RVb + i) (by omega), rd _ (by omega)]; exact hcf _ hRV)
        (by rw [rd (RVb + i) (by omega), rd _ (by omega)]; exact hmk _ hRV)
        (by omega) (by omega) (by omega) (by rw [rd (RVb + i) (by omega)]; omega)
        (by rw [rd (RVb + i) (by omega)]; omega) (by omega) (by omega) (by omega) (by omega)
        (by rw [rd (LABb + i) (by omega)]; omega) (by rw [rd (LABb + i) (by omega)]; omega)
        (by omega) (by omega) (by rw [rd _ (by omega)]; exact hcp i hi)
        (by rw [rd (LABb + i) (by omega), rd _ (by omega)]; exact hdg _ (by omega))
        (by omega) (by rw [rd (LABb + i) (by omega)]; omega)
        (by rw [rd (LABb + i) (by omega)]; omega)
      -- the values read by the body are those of the start
      have eCap : scCap c'.nmem CFb MKb RVb CPb FLb Z i = scCap c.nmem CFb MKb RVb CPb FLb Z i := by
        unfold scCap scDF
        rw [rd (RVb + i) (by omega), rd (CFb + i) (by omega), rd (MKb + i) (by omega),
          rd (CFb + c.nmem (RVb + i)) (by omega), rd (MKb + c.nmem (RVb + i)) (by omega),
          rd (CPb + i) (by omega), rd (FLb + i) (by omega)]
      have eBt : scBt c'.nmem CFb MKb LABb DVb DGb Z i = scBt c.nmem CFb MKb LABb DVb DGb Z i := by
        unfold scBt
        rw [rd (LABb + i) (by omega), rd (CFb + i) (by omega), rd (MKb + i) (by omega),
          rd (DGb + (c.nmem (LABb + i) - 1)) (by omega),
          rd (DVb + (c.nmem (LABb + i) - 1)) (by omega)]
      rw [eCap, eBt] at hm
      refine ⟨c'', k, ex, by omega, h30, by rw [hn _ (by omega) (by omega)]; exact hb,
        fun e he => ?_, fun e he => ?_, fun a h => ?_,
        fun r hr' => by
          unfold ScScr at hr'
          rw [hn r (by omega) (by omega), j4 r (by unfold ScScr; omega)],
        by rw [hn _ (by omega) (by omega)]; exact j31, by rw [hr, jr], by rw [hrm, jrm],
        by rw [ho, jo]⟩
      · rw [hm, upd_apply, iteF (by omega), upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [iteF (by omega)]; exact j1 e he
        · rw [iteT rfl]
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [iteF (by omega), upd_apply, iteF (by omega)]; exact j2 e he
        · rw [iteT rfl]
      · rw [hm, upd_apply, iteF (by omega), upd_apply, iteF (by omega)]
        exact j3 a (by omega))
  exact ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j1, j2, j3, j4, jr, jrm, jo⟩

end NcStep

end BKMNW

end PlanarFlow
