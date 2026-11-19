module

public import PlanarFlow.BKMNW.Nf7aP2

/-!
# The prologue of `fixP`, part 3: lengths, offsets and the stage arrays

**`proP3`** `= clProg ; kBlk ; fsaProg ; fsbProg ; fscProg` (**`proP3_exec`**,
`≤ 12 m + 84 k + 40` steps): `CL[i] = CP i + Z − FLW i`, `r9420 = AS`, `r9373 = 4 AS + 1`,
`r9422 = 8 fpB`, `r9310 = K`, and the stage arrays `CW`, `CR`, `FW`, `F0`, `DV`, `ET`, `EH`, `PW`,
`PR`, `EL` (values in `FpIn`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv

variable {P : Input} {W : ℕ}

lemma dvS_le_sum (lab fl : ℕ → ℕ) (i v : ℕ) : dvS lab fl i v ≤ ∑ j ∈ range i, fl j :=
  sum_le_sum_of_subset (filter_subset _ _)

lemma dvC_le (lab : ℕ → ℕ) (i v : ℕ) : dvC lab i v ≤ i := by
  unfold dvC; exact (card_filter_le _ _).trans (by simp)

/-- The lengths and the offsets. -/
def proP3a : Stmt := .seq clProg kBlk

set_option maxHeartbeats 1600000 in
theorem proP3a_exec (p : FpIn) (c : Config) (hc : WordsBounded W c) {A0 : ℕ}
    (hR : RegP1 p A0 c) (hlo : ∀ a < A0, c.nmem a = p.mem a) (hfr : p.d + 4 + 7 * p.m ≤ A0)
    (hW1 : A0 + 9 * p.m + 2 ≤ W)
    (hW2 : p.AS + 16 * fpB p.AS p.m p.k + p.Z + p.k + 16 ≤ W) :
    ∃ c' t, Exec P W proP3a c c' t ∧ t ≤ 12 * p.m + 22 ∧
      c'.nreg 9420 = p.AS ∧ c'.nreg 9373 = 4 * p.AS + 1 ∧ c'.nreg 9422 = 8 * fpB p.AS p.m p.k ∧
      c'.nreg 9310 = p.K ∧
      (∀ i < p.m, c'.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + i) =
        p.CP i + p.Z - p.FLW i) ∧
      (∀ a, ¬ (A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m ≤ a ∧
        a < A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 9420 → r ≠ 9373 → r ≠ 9422 → r ≠ 9310 → (r < 9456 ∨ 9497 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨g00, -, g36, g21, g01, -, -, -, -, g34, g35, -, -, -, -, -, g09, -⟩ := hR
  have hCPm : ∀ i < p.m, c.nmem (p.d + 4 + p.m + p.m + p.m + i) = p.CP i := fun i hi =>
    hlo _ (by omega)
  have hFWm : ∀ i < p.m, c.nmem (p.d + 4 + p.m + p.m + p.m + p.m + p.m + p.m + i) = p.FLW i :=
    fun i hi => hlo _ (by omega)
  have hsumCP : ∑ i ∈ range p.m, c.nmem (p.d + 4 + p.m + p.m + p.m + i) = p.AS :=
    sum_congr rfl fun i hi => hCPm i (mem_range.1 hi)
  obtain ⟨c₁, t₁, e₁, ht₁, aCL, a20, ak, an, ar, arm, ao⟩ :=
    clProg_exec (P := P) c hc (m := p.m) (CPb := p.d + 4 + p.m + p.m + p.m)
      (FLWb := p.d + 4 + p.m + p.m + p.m + p.m + p.m + p.m)
      (CLb := A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m) (Z := p.Z) g00 g34 g35 g09 g21 g36
      ⟨by omega, by omega⟩ (by rw [hsumCP]; omega) (by omega)
  rw [hsumCP] at a20
  have n1 : ∀ r, r ≠ 9420 → (r < 9456 ∨ 9460 < r) → c₁.nreg r = c.nreg r := an
  obtain ⟨c₂, t₂, e₂, ht₂, b73, b22, b10, bk, bm, br, brm, bo⟩ :=
    kBlk_exec (P := P) c₁ e₁.wb_right a20 (by rw [n1 _ (by omega) (by omega), g00])
      (by rw [n1 _ (by omega) (by omega), g01]) (by rw [n1 _ (by omega) (by omega), g36])
      (by omega)
  refine ⟨c₂, _, e₁.seq e₂, by omega, by rw [bk _ (by omega) (by omega) (by omega) (by omega), a20],
    b73, b22, b10, fun i hi => ?_, fun a ha => by rw [bm]; exact ak a ha,
    fun r h1 h2 h3 h4 h5 => by rw [bk r h2 h3 h4 (by omega), n1 r h1 (by omega)],
    by rw [br, ar], by rw [brm, arm], by rw [bo, ao]⟩
  rw [bm, aCL i hi, hCPm i hi, hFWm i hi]

/-- The words of the darts of the path. -/
def proP3b : Stmt := fsaProg

set_option maxHeartbeats 1600000 in
theorem proP3b_exec (p : FpIn) (c : Config) (hc : WordsBounded W c) {A0 : ℕ}
    (hR : RegP1 p A0 c) (r10 : c.nreg 9310 = p.K)
    (hlo : ∀ a < A0, c.nmem a = p.mem a)
    (hLAB : ∀ i < p.m, c.nmem (A0 + p.m + p.m + p.m + p.m + 1 + i) = p.vl i + 1)
    (hDV : ∀ v < p.m, c.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + v) = dvS p.vl p.FLW p.m v ∧
        c.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + v) = dvC p.vl p.m v)
    (hRV : ∀ i < p.m, p.RV i < p.m) (hSG : PermOn (sgF p.d p.m p.mem) p.m)
    (hPD : ∀ l < p.k, p.PD l < p.m)
    (hfr : p.d + 4 + 7 * p.m ≤ A0) (hsg : p.PDb + p.k ≤ A0)
    (hW1 : 16 * (p.Qb A0 + 15 * p.k + 2) ≤ W)
    (hW2 : ∑ i ∈ range p.m, p.FLW i + p.K + p.m * p.Z ≤ W) :
    ∃ c' t, Exec P W proP3b c c' t ∧ t ≤ 38 * p.k + 3 ∧
      (∀ l < p.k, c'.nmem (p.Qb A0 + l) = p.CP (p.PD l) ∧
        c'.nmem (p.Qb A0 + p.k + l) = p.CP (p.RV (p.PD l)) ∧
        c'.nmem (p.Qb A0 + p.k + p.k + l) = p.FLW (p.PD l) + p.K - p.Z ∧
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + l) = p.FLW (p.PD l) + p.K - p.Z ∧
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + l) = p.DVw l) ∧
      (∀ a, ¬ (p.Qb A0 ≤ a ∧ a < p.Qb A0 + p.k + p.k + p.k) →
        ¬ (p.Qb A0 + p.k + p.k + p.k + p.k + p.k ≤ a ∧
          a < p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9461 ∨ 9470 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨g00, -, g36, g21, g01, -, g02, g30, -, g34, g35, -, -, -, -, g08, -, -, -, g74, g75,
    g76, -, g12, g13, -⟩ := hR
  have hPDm : ∀ l < p.k, c.nmem (p.PDb + l) = p.PD l := fun l hl => hlo _ (by omega)
  have hRVm : ∀ i < p.m, c.nmem (p.d + 4 + p.m + i) = p.RV i := fun i hi => hlo _ (by omega)
  have hCPm : ∀ i < p.m, c.nmem (p.d + 4 + p.m + p.m + p.m + i) = p.CP i := fun i hi =>
    hlo _ (by omega)
  have hFWm : ∀ i < p.m, c.nmem (p.d + 4 + p.m + p.m + p.m + p.m + p.m + p.m + i) = p.FLW i :=
    fun i hi => hlo _ (by omega)
  have hFLle : ∀ i < p.m, p.FLW i ≤ ∑ j ∈ range p.m, p.FLW j := fun i hi =>
    single_le_sum (fun j _ => Nat.zero_le _) (mem_range.2 hi)
  have hvl : ∀ i < p.m, p.vl i < p.m := fun i hi => olab_lt hSG hi
  have hQ : p.Qb A0 = A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m + p.m := rfl
  obtain ⟨c₃, t₃, e₃, ht₃, sA, sk, sn, sr, srm, so⟩ :=
    fsaProg_exec (P := P) c hc (k := p.k) (m := p.m) (K := p.K) (Z := p.Z)
      (PDb := p.PDb) (RVb := p.d + 4 + p.m) (CPb := p.d + 4 + p.m + p.m + p.m)
      (FLWb := p.d + 4 + p.m + p.m + p.m + p.m + p.m + p.m)
      (DVA := A0 + p.m + p.m + p.m + p.m + 1) (CWb := p.Qb A0) (CRb := p.Qb A0 + p.k)
      (FWb := p.Qb A0 + p.k + p.k) (F0b := p.Qb A0 + p.k + p.k + p.k + p.k + p.k)
      (DVb := p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k)
      g01 g00 g02 g30 g34 g35 g08 r10 g21 g36 g74 g75 g76 g12 g13
      (fun l hl => by rw [hPDm l hl]; exact hPD l hl)
      (fun i hi => by rw [hRVm i hi]; exact hRV i hi)
      (fun i hi => by rw [hLAB i hi]; have := hvl i hi; omega)
      (fun i hi => by rw [hFWm i hi]; have := hFLle i hi; omega)
      (fun v hv => by
        rw [(hDV v hv).1]
        have := dvS_le_sum p.vl p.FLW p.m v; omega)
      (fun v hv => by
        rw [(hDV v hv).2]
        have := dvC_le p.vl p.m v
        have := Nat.mul_le_mul_right p.Z this; omega)
      ⟨by omega, by omega, by omega, by omega, by omega⟩
      ⟨by omega, by omega, by omega, by omega⟩ (by omega)
  refine ⟨c₃, _, e₃, by omega, fun l hl => ?_, fun a h1 h2 => ?_, sn, sr,
    srm, so⟩
  · obtain ⟨s1, s2, s3, s4, s5⟩ := sA l hl
    have := hPD l hl
    have hv := hvl _ this
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [s1, hPDm l hl, hCPm _ this]
    · rw [s2, hPDm l hl, hRVm _ this, hCPm _ (hRV _ this)]
    · rw [s3]; simp only [fsaFW]; rw [hPDm l hl, hFWm _ this]
    · rw [s4]; simp only [fsaFW]; rw [hPDm l hl, hFWm _ this]
    · rw [s5]; simp only [fsaDV]
      rw [hPDm l hl, hLAB _ this, Nat.add_sub_cancel, (hDV _ hv).1, (hDV _ hv).2]
      rfl
  · exact sk a (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The arcs and the start of the prices and lengths. -/
def proP3c : Stmt := .seq fsbProg fscProg

set_option maxHeartbeats 1600000 in
theorem proP3c_exec (p : FpIn) (c : Config) (hc : WordsBounded W c) {A0 : ℕ}
    (hR : RegP1 p A0 c) (r10 : c.nreg 9310 = p.K)
    (hlo : ∀ a < A0, c.nmem a = p.mem a)
    (hFLm : ∀ i < p.m, c.nmem (A0 + p.m + i) = p.lab i)
    (hMKm : ∀ a ≤ p.m, c.nmem (A0 + p.m + p.m + p.m + a) = p.cw.mks a)
    (hRV : ∀ i < p.m, p.RV i < p.m) (hNX : PermOn (nxF p.d p.m p.mem) p.m)
    (hPD : ∀ l < p.k, p.PD l < p.m)
    (hfr : p.d + 4 + 7 * p.m ≤ A0) (hsg : p.PDb + p.k ≤ A0)
    (hW1 : 16 * (p.Qb A0 + 15 * p.k + 2) ≤ W) :
    ∃ c' t, Exec P W proP3c c c' t ∧ t ≤ 46 * p.k + 8 ∧
      (∀ l < p.k,
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + 2 * l) = p.ix (p.PD l) ∧
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + 2 * l + 1) =
          p.ix (p.RV (p.PD l)) ∧
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + 2 * l) =
          p.ix (p.RV (p.PD l)) ∧
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + 2 * l + 1) =
          p.ix (p.PD l)) ∧
      (∀ x < 2 * p.k,
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + x) =
          0 ∧
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k +
          p.k + x) = p.K ∧
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + x) = p.K) ∧
      (∀ a, ¬ (p.Qb A0 + p.k + p.k + p.k ≤ a ∧ a < p.Qb A0 + p.k + p.k + p.k + p.k + p.k) →
        ¬ (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k ≤ a ∧ a < p.Qb A0 + 15 * p.k) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9471 ∨ 9477 < r) → (r < 9480 ∨ 9483 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨g00, -, g36, -, g01, -, g02, g30, -, -, -, -, g05, -, g07, -, -, -, -, -, -, -, g77,
    -, -, g14, g15, g16, g17, -⟩ := hR
  have hPDm : ∀ l < p.k, c.nmem (p.PDb + l) = p.PD l := fun l hl => hlo _ (by omega)
  have hRVm : ∀ i < p.m, c.nmem (p.d + 4 + p.m + i) = p.RV i := fun i hi => hlo _ (by omega)
  have hQ : p.Qb A0 = A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m + p.m := rfl
  obtain ⟨c₄, t₄, e₄, ht₄, bA, bk4, bn, br4, brm4, bo4⟩ :=
    fsbProg_exec (P := P) c hc (k := p.k) (m := p.m) (PDb := p.PDb)
      (RVb := p.d + 4 + p.m) (FLb := A0 + p.m) (MKb := A0 + p.m + p.m + p.m)
      (ETb := p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k)
      (EHb := p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k)
      g01 g02 g30 g05 g07 g14 g15 g36
      (fun l hl => by rw [hPDm l hl]; exact hPD l hl)
      (fun i hi => by rw [hRVm i hi]; exact hRV i hi)
      (fun i hi => by rw [hFLm i hi]; have := olab_lt hNX hi; simp only [FpIn.lab]; omega)
      ⟨by omega, by omega, by omega, by omega⟩ (by omega) (by omega)
  have hI : ∀ x < p.m, fsbI c.nmem (A0 + p.m) (A0 + p.m + p.m + p.m) x = p.ix x := fun x hx => by
    have := olab_lt hNX hx
    simp only [fsbI]
    rw [hFLm x hx, hMKm _ (by simp only [FpIn.lab]; omega)]
    rfl
  have n4 : ∀ r, (r < 9471 ∨ 9477 < r) → c₄.nreg r = c.nreg r := bn
  obtain ⟨c₅, t₅, e₅, ht₅, cA, ck, cn, cr, crm, co⟩ :=
    fscProg_exec (P := P) c₄ e₄.wb_right (k := p.k)
      (PWb := p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k)
      (PRb := p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k)
      (ELb := p.Qb A0 + p.k + p.k + p.k) (K := p.K)
      (by rw [n4 _ (by omega), g01]) (by rw [n4 _ (by omega), g16])
      (by rw [n4 _ (by omega), g17]) (by rw [n4 _ (by omega), g77]) (by rw [n4 _ (by omega), r10])
      (by rw [n4 _ (by omega), g36])
      ⟨Or.inl (by omega), Or.inr (by omega), Or.inr (by omega)⟩ (by omega)
  refine ⟨c₅, _, e₄.seq e₅, by omega, fun l hl => ?_, cA, fun a h1 h2 => ?_,
    fun r h1 h2 => by rw [cn r h2, n4 r h1], by rw [cr, br4], by rw [crm, brm4], by rw [co, bo4]⟩
  · obtain ⟨s1, s2, s3, s4⟩ := bA l hl
    have := hPD l hl
    have hr := hRV _ this
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ck _ (by omega) (by omega) (by omega), s1, hPDm l hl, hI _ this]
    · rw [ck _ (by omega) (by omega) (by omega), s2, hPDm l hl, hRVm _ this, hI _ hr]
    · rw [ck _ (by omega) (by omega) (by omega), s3, hPDm l hl, hRVm _ this, hI _ hr]
    · rw [ck _ (by omega) (by omega) (by omega), s4, hPDm l hl, hI _ this]
  · rw [ck _ (by omega) (by omega) (by omega), bk4 _ (by omega) (by omega)]

end BKMNW

end PlanarFlow
