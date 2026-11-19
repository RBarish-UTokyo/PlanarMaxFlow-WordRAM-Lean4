module

public import PlanarFlow.BKMNW.Nf7cG

/-!
# The final step of `fixP`: phase C on the machine

**`finC_exec`**: `fnH ; fnZ ; potP ; flP` from the header of the root frame (`m' = mem[A + 1]`,
`k' = mem[A + 2]`) and the outcome region at `R0 = Ob + 4 + 5 k' + m'` (`w = mem[R0 + 1]`, the
identifiers at `R0 + 2 + v`, the values at `R0 + 2 + 2 m' + v`): `POT` (the `m + 1` cells at
`T + m`) zeroed then `potM`, and `FL[i] = flV …` for `i < m`.
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

/-- The memory after `fnZ`: `POT` zeroed. -/
def potZ (nm : ℕ → ℕ) (POTb m : ℕ) (a : ℕ) : ℕ :=
  if POTb ≤ a ∧ a < POTb + (m + 1) then 0 else nm a

lemma potM_le (nm : ℕ → ℕ) {IDb VLb POTb B v : ℕ} {a : ℕ} (ha : nm a ≤ B)
    (hv : ∀ v' < v, nm (VLb + v') ≤ B) : potM nm IDb VLb POTb v a ≤ B := by
  induction v with
  | zero => exact ha
  | succ v ih =>
    simp only [potM, upd_apply]
    split_ifs
    · exact hv v (by omega)
    · exact ih fun v' hv' => hv v' (by omega)

theorem fnZ_exec (c : Config) (hc : WordsBounded W c) {POTb m : ℕ} (r79 : c.nreg 9479 = POTb)
    (r00 : c.nreg 9400 = m) (r36 : c.nreg 9436 = 1) (hW : POTb + (m + 1) + 1 ≤ W) :
    ∃ c' t, Exec P W fnZ c c' t ∧ t ≤ 5 * m + 12 ∧ c'.nmem = potZ c.nmem POTb m ∧
      (∀ r, (r < 5030 ∨ 5035 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a31, a30, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.copyN 5031 9479, .addN 5030 9400 9436]) c c₁ t₁ ∧ t₁ = 2 ∧
        c₁.nreg 5031 = POTb ∧ c₁.nreg 5030 = m + 1 ∧
        (∀ r, r ≠ 5030 → r ≠ 5031 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp) <;> (try simp only [r79, r00, r36]) <;> omega)
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r79, r00, r36])
    all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl
  obtain ⟨c₂, t₂, e₂, ht₂, z1, zk, zn, zr, zrm, zo⟩ :=
    mzFill_exec (P := P) c₁ e₁.wb_right a30 a31 (by omega) (by omega)
  refine ⟨c₂, _, e₁.seq e₂, by omega, funext fun a => ?_, fun r hr => ?_, by rw [zr, ar],
    by rw [zrm, arm], by rw [zo, ao]⟩
  · unfold potZ
    split_ifs with h
    · obtain ⟨i, rfl⟩ : ∃ i, a = POTb + i := ⟨a - POTb, by omega⟩
      exact z1 i (by omega)
    · rw [zk a (by omega), am]
  · rw [zn r (by omega), ak r (by omega) (by omega)]

set_option maxHeartbeats 1000000 in
/-- **Phase C of the final step: the potentials and the flow.** -/
theorem finC_exec (c : Config) (hc : WordsBounded W c)
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
    (hW : 2 * (Ob + 4 + 5 * k' + m' + 2 + m' + m') + A + 2 + 2 * T + 4 * m + 2 + CPb + RVb +
      LABb + FLb ≤ W)
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
    fnH_exec (P := P) c hc r80 r81 r36 hm' hk' (by omega)
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
    potP_exec (P := P) c₂ e₂.wb_right (w := w) (G := m) (IDb := R0 + 2) (VLb := R0 + 2 + m' + m')
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
    flP_exec (P := P) c₃ e₃.wb_right (m := m) (CPb := CPb) (RVb := RVb) (LABb := LABb)
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
