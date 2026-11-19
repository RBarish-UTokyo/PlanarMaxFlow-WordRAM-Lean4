module

public import PlanarFlow.BKMNW.SgE

/-!
# The parts of the separator on the machine: `sgProg` composed

* pure: `cnt_congr_pos`, `cnt_run`, `sgOff_mono`, `sgOff_length`;
* **`sgProg_exec`**: with `PD` (`PD[j] ∈ [1, n']` for `j ≤ k`, `0` after; `k < n'`), `IX`
  (values `< n`), `HP`, `FX` (injective, values `< n`) below `Gb`, the runs
  `R = runIdx H k 0` of the flags `H j = [0 < HP[IX[PD[j] - 1]]]`: within `110 n' + 7 m + 100`
  steps, `Gb := #R`, the offsets `sgOff R j` and lengths `sgLen R j`, the frame index `f` of the
  `l`-th dart of the run `j` (any `f < m` with `FX[f] = IX[PD[a_j + l] - 1]`) at
  `Gb + 1 + 2 #R + sgOff R j + l`, and that of its start (`FX[f] = IX[PD[a_j] - 1]`) at
  `Gb + 1 + 2 #R + sgOff R #R + j`; `r6502 = Gb`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

lemma cnt_congr_pos {F G : ℕ → ℕ} {n : ℕ} (h : ∀ j < n, (0 < F j ↔ 0 < G j)) :
    cnt F n = cnt G n := by
  unfold cnt; congr 1
  apply Finset.filter_congr; intro j hj; rw [Finset.mem_range] at hj; exact h j hj

lemma cnt_run (F : ℕ → ℕ) (a : ℕ) : ∀ l, (∀ i < l, 0 < F (a + i)) → cnt F (a + l) = cnt F a + l
  | 0, _ => by simp
  | l + 1, h => by
    rw [← Nat.add_assoc, cnt_succ, cnt_run F a l fun i hi => h i (by omega), iteT (h l (by omega))]
    omega

lemma sgOff_mono (R : List (ℕ × ℕ)) {j j' : ℕ} (h : j ≤ j') : sgOff R j ≤ sgOff R j' := by
  have e : sgOff R j = sgOff (R.take j') j := by
    unfold sgOff; rw [List.take_take, Nat.min_eq_left h]
  rw [e]
  have := sgOff_le (R.take j') j
  unfold sgOff at this ⊢
  exact this

lemma sgOff_length (R : List (ℕ × ℕ)) : sgOff R R.length = (R.map fun p => p.2 - p.1).sum := by
  unfold sgOff; rw [List.take_length]

section Exec

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The parts of the separator on the machine** (see the module docstring). -/
theorem sgProg_exec (c : Config) (hc : WordsBounded W c) {n' PDb IXb HPb m FXb Z Gb n k : ℕ}
    (r00 : c.nreg 7200 = n') (r01 : c.nreg 7201 = PDb) (r02 : c.nreg 7202 = IXb)
    (r03 : c.nreg 7203 = HPb) (r04 : c.nreg 7204 = m) (r05 : c.nreg 7205 = FXb)
    (r06 : c.nreg 7206 = Z) (r07 : c.nreg 7207 = Gb) (r08 : c.nreg 7208 = n)
    (r21 : c.nreg 6521 = 1)
    (hk : k < n') (hpd : ∀ j ≤ k, 1 ≤ c.nmem (PDb + j) ∧ c.nmem (PDb + j) ≤ n')
    (hpd0 : ∀ j < n', k < j → c.nmem (PDb + j) = 0)
    (hix : ∀ q < n', c.nmem (IXb + q) < n) (hfx : ∀ f < m, c.nmem (FXb + f) < n)
    (hinj : ∀ i < m, ∀ j < m, c.nmem (FXb + i) = c.nmem (FXb + j) → i = j)
    (lay : PDb + n' ≤ Gb ∧ IXb + n' ≤ Gb ∧ HPb + n ≤ Gb ∧ FXb + m ≤ Gb ∧ Gb + 2 * n' + 3 ≤ Z ∧
      Z + 8 * n' + n + 2 ≤ W) (hm : m + 1 ≤ W) (R : List (ℕ × ℕ))
    (hRd : R = runIdx (fun j => decide (0 < c.nmem (HPb + c.nmem (IXb + (c.nmem (PDb + j) - 1)))))
      k 0) :
    ∃ c' t, Exec P W sgProg c c' t ∧ t ≤ 110 * n' + 7 * m + 100 ∧
      c'.nmem Gb = R.length ∧
      (∀ j < R.length, c'.nmem (Gb + 1 + j) = sgOff R j ∧
        c'.nmem (Gb + 1 + R.length + j) = sgLen R j) ∧
      (∀ j < R.length, ∀ l < sgLen R j, ∀ f < m,
        c.nmem (FXb + f) = c.nmem (IXb + (c.nmem (PDb + ((R.getD j (0, 0)).1 + l)) - 1)) →
        c'.nmem (Gb + 1 + 2 * R.length + sgOff R j + l) = f) ∧
      (∀ j < R.length, ∀ f < m,
        c.nmem (FXb + f) = c.nmem (IXb + (c.nmem (PDb + (R.getD j (0, 0)).1) - 1)) →
        c'.nmem (Gb + 1 + 2 * R.length + sgOff R R.length + j) = f) ∧
      sgOff R R.length + 2 * R.length ≤ k + 2 ∧ c'.nreg 6502 = Gb ∧
      (∀ a, ¬ (Gb ≤ a ∧ a < Gb + 2 * n' + 3) → ¬ (Z ≤ a ∧ a < Z + 8 * n' + n + 1) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4100 ∨ (4113 < x ∧ x < 4600) ∨ (4605 < x ∧ x < 6300) ∨
        (6309 < x ∧ x < 6502) ∨ (6502 < x ∧ x < 6520) ∨ x = 6521 ∨ (6529 < x ∧ x < 7210) ∨
        7229 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lay
  have hn : 1 ≤ n := by have := hix 0 (by omega); omega
  set hf : ℕ → ℕ := fun j => c.nmem (HPb + c.nmem (IXb + (c.nmem (PDb + j) - 1))) with hhf
  set H : ℕ → Bool := fun j => decide (0 < hf j) with hH
  have hsl := runIdx_sum_len H k 0
  rw [← hRd] at hsl
  unfold sgProg
  obtain ⟨c₁, t₁, e₁, ht₁, R1, s19, hHF, hFXI, m1, n1, rr1, rm1, o1⟩ := sgP1_exec (P := P) c hc
    r00 r01 r02 r03 r04 r05 r06 r07 r08 r21 hk hpd hpd0 hix hfx hinj
    ⟨by omega, by omega, by omega, by omega, by omega⟩ hm
  have hR1 : R = runIdx (fun j => decide (0 < c₁.nmem (Z + 2 * n' + j))) k 0 := by
    rw [hRd]; exact runIdx_congr (fun j hj => by rw [hHF j (by omega)]) 0
  obtain ⟨c₂, t₂, e₂, ht₂, R2, s19', s20, s24, s22, g0, gOL, gRn, m2, n2, rr2, rm2, o2⟩ :=
    sgP2_exec (P := P) c₁ e₁.wb_right R1 s19 hk hn ⟨by omega, by omega⟩ R hR1
  have hL : sgOff R R.length + 2 * R.length ≤ k + 2 := by rw [sgOff_length]; exact hsl
  have hm2 : ∀ a, a < Gb → c₂.nmem a = c.nmem a := fun a ha => by
    rw [m2 a (by omega) (by omega), m1 a (by omega)]
  have ha : ∀ j < R.length, c₂.nmem (Z + 3 * n' + n + 2 * j) = (R.getD j (0, 0)).1 :=
    fun j hj => (gRn j hj).1
  have haK : ∀ j < R.length, (R.getD j (0, 0)).1 ≤ (R.getD j (0, 0)).2 ∧
      (R.getD j (0, 0)).2 ≤ k := fun j hj => by
    rw [hRd] at hj ⊢; exact runIdx_getD_le _ k hj
  obtain ⟨c₃, t₃, e₃, ht₃, dD, dV, d02, m3, n3, rr3, rm3, o3⟩ := sgP3_exec (P := P) c₂
    e₂.wb_right R2 s19' s20 s22 s24 hk hL
    (fun j hj => by rw [hm2 _ (by omega)]; exact hpd j hj)
    (fun q hq => by rw [hm2 _ (by omega)]; exact hix q hq)
    (fun j hj => by rw [ha j hj]; exact (haK j hj).1.trans (haK j hj).2)
    ⟨by omega, by omega, by omega, by omega⟩
  -- the FXI cells and the HF cells at stage 3
  have hFX3 : ∀ f < m, c₂.nmem (Z + 3 * n' + c.nmem (FXb + f)) = f := fun f hf' => by
    rw [m2 _ (by omega) (by have := hfx f hf'; omega)]; exact hFXI f hf'
  have hHF2 : ∀ j < n', c₂.nmem (Z + 2 * n' + j) = hf j := fun j hj => by
    rw [m2 _ (by omega) (by omega)]; exact hHF j hj
  -- the flags of the darts are `rfN`
  have hpos : ∀ t < k, (0 < rfV (c₂.nmem (Z + 2 * n' + t)) (c₂.nmem (Z + 2 * n' + t + 1)) ↔
      0 < rfN H k t) := fun t ht => by
    rw [hHF2 t (by omega), Nat.add_assoc, hHF2 (t + 1) (by omega), rfV_pos]
    unfold rfN
    simp only [hH, decide_eq_false_iff_not, not_lt, Nat.le_zero]
    constructor
    · rintro ⟨h1, h2⟩; rw [iteT ⟨ht, h1, h2⟩]; omega
    · intro h; by_contra hc
      rw [iteF (fun hh => hc ⟨hh.2.1, hh.2.2⟩)] at h; omega
  have hcnt : ∀ i ≤ k, cnt (fun j => rfV (c₂.nmem (Z + 2 * n' + j)) (c₂.nmem (Z + 2 * n' + j + 1)))
      i = cnt (rfN H k) i := fun i hi => cnt_congr_pos fun j hj => hpos j (by omega)
  have hRH : R = runIdx H k 0 := hRd
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), ?_, ?_, fun j hj => ?_, fun j hj l hl f hf' hfe => ?_,
    fun j hj f hf' hfe => ?_, hL, d02, fun a h1 h2 => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · clear * - ht₁ ht₂ ht₃; omega
  · rw [m3 _ (by omega) (by omega)]; exact g0
  · rw [m3 _ (by omega) (by omega), m3 _ (by omega) (by omega)]; exact gOL j hj
  · -- a dart of a run
    have hj' : j < (runIdx H k 0).length := by rw [← hRH]; exact hj
    obtain ⟨hc1, hc2⟩ := runIdx_cnt H k 0 j hj'
    have e1 : (runIdx H k 0)[j] = R.getD j (0, 0) := by
      rw [List.getD_eq_getElem _ _ hj]; simp only [hRH]
    have e2 : (((runIdx H k 0).take j).map fun p => p.2 - p.1).sum = sgOff R j := by
      rw [← hRH]; rfl
    rw [e1, e2] at hc1
    rw [e1] at hc2
    have hz : cnt (rfN H k) 0 = 0 := by simp [cnt]
    have hl' : l < (R.getD j (0, 0)).2 - (R.getD j (0, 0)).1 := hl
    have hk2 := haK j hj
    have hrun := cnt_run (rfN H k) (R.getD j (0, 0)).1 l fun i hi => hc2 i (by omega)
    have hflag := hc2 l hl'
    have ht : (R.getD j (0, 0)).1 + l < k := by omega
    have hct : cnt (fun j => rfV (c₂.nmem (Z + 2 * n' + j)) (c₂.nmem (Z + 2 * n' + j + 1)))
        ((R.getD j (0, 0)).1 + l) = sgOff R j + l := by
      rw [hcnt _ ht.le, hrun, hc1, hz]; omega
    have hlt : sgOff R j + l < sgOff R R.length := by
      have := sgOff_mono R (show j + 1 ≤ R.length by omega)
      rw [sgOff_succ hj] at this; unfold sgLen at this; omega
    have := dD _ ht ((hpos _ ht).2 hflag) (by rw [hct]; exact hlt)
    have hp := hpd _ ht.le
    rw [hct, hm2 (PDb + ((R.getD j (0, 0)).1 + l)) (by omega),
      hm2 (IXb + (c.nmem (PDb + ((R.getD j (0, 0)).1 + l)) - 1)) (by omega), ← hfe,
      hFX3 f hf'] at this
    rw [show Gb + 1 + 2 * R.length + sgOff R j + l = Gb + 1 + 2 * R.length + (sgOff R j + l) by
      omega]
    exact this
  · -- the start of a run
    have := dV j hj
    have hk2 := haK j hj
    have hp := hpd _ (hk2.1.trans hk2.2)
    rw [ha j hj, hm2 (PDb + (R.getD j (0, 0)).1) (by omega),
      hm2 (IXb + (c.nmem (PDb + (R.getD j (0, 0)).1) - 1)) (by omega), ← hfe,
      hFX3 f hf'] at this
    rw [← s22] at this ⊢
    exact this
  · rw [m3 a (by omega) (by omega), m2 a (by omega) (by omega), m1 a (by omega)]
  · rw [n3 x (by omega), n2 x (by omega), n1 x (by omega)]
  · rw [rr3, rr2, rr1]
  · rw [rm3, rm2, rm1]
  · rw [o3, o2, o1]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
