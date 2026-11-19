module

public import PlanarFlow.BKMNW.Nf7aP3

/-!
# The prologue of `fixP` on the machine

**`fpPro`** `= proP1a ; proP1b ; proP2 ; proP3a ; proP3b ; proP3c` and **`fpPro_exec`**
(`≤ 200 m + 200 k + 300` steps): from the frame of the call and the parts of the separator
(natural data `FpIn`), the layout registers and all the arrays of the prologue (**`ProOut`**).
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

/-- **The state after the prologue** (layout of `Nf7aP1.lean`): the registers, the
memory below `A0` unchanged, the face labels `FL`, the corners `BT` (`b = r9419` of them), the
lengths `CL`, the stage arrays `CW`, `CR`, `FW`, `F0`, `DV`, `ET`, `EH`, `PW`, `PR`, `EL`. -/
def ProOut (p : FpIn) (A0 : ℕ) (c : Config) : Prop :=
  RegP1 p A0 c ∧ c.nreg 9419 = p.cw.cnt ∧ c.nreg 9420 = p.AS ∧ c.nreg 9373 = 4 * p.AS + 1 ∧
    c.nreg 9422 = 8 * fpB p.AS p.m p.k ∧ c.nreg 9310 = p.K ∧
    (∀ a < A0, c.nmem a = p.mem a) ∧
    (∀ i < p.m, c.nmem (A0 + p.m + i) = p.lab i) ∧
    (∀ x < p.cw.cnt, c.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m + x) =
      p.cw.bt x) ∧
    (∀ i < p.m, c.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + i) =
      p.CP i + p.Z - p.FLW i) ∧
    (∀ l < p.k, c.nmem (p.Qb A0 + l) = p.CP (p.PD l) ∧
      c.nmem (p.Qb A0 + p.k + l) = p.CP (p.RV (p.PD l)) ∧
      c.nmem (p.Qb A0 + p.k + p.k + l) = p.FLW (p.PD l) + p.K - p.Z ∧
      c.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + l) = p.FLW (p.PD l) + p.K - p.Z ∧
      c.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + l) = p.DVw l) ∧
    (∀ l < p.k,
      c.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + 2 * l) = p.ix (p.PD l) ∧
      c.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + 2 * l + 1) =
        p.ix (p.RV (p.PD l)) ∧
      c.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + 2 * l) =
        p.ix (p.RV (p.PD l)) ∧
      c.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + 2 * l + 1) =
        p.ix (p.PD l)) ∧
    (∀ x < 2 * p.k,
      c.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + x) = 0 ∧
      c.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k +
        p.k + x) = p.K ∧
      c.nmem (p.Qb A0 + p.k + p.k + p.k + x) = p.K)

/-- The scratch registers of the prologue. -/
def proScr (r : ℕ) : Prop :=
  scr1 r ∨ r = 9310 ∨ r = 9373 ∨ (9439 ≤ r ∧ r ≤ 9497)

/-- Parts 1 and 2. -/
def fpProA : Stmt := .seq proP1a (.seq proP1b proP2)

theorem fpProA_exec (p : FpIn) (c : Config) (hc : WordsBounded W c) {A0 j : ℕ}
    (r04 : c.nreg 3004 = p.d) (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = p.Gb)
    (r00 : c.nreg 6800 = j) (hmem : ∀ a < A0, c.nmem a = p.mem a)
    (hm : p.mem p.d = p.m) (hZ : p.mem (p.d + 3) = p.Z) (hns : p.mem p.Gb = p.ns)
    (hoff : p.mem (p.Gb + 1 + j) = p.off) (hk : p.mem (p.Gb + 1 + j + p.ns) = p.k)
    (hj : p.Gb + 1 + j + p.ns < A0)
    (hRV : ∀ i < p.m, p.RV i < p.m) (hSG : PermOn (sgF p.d p.m p.mem) p.m)
    (hNX : PermOn (nxF p.d p.m p.mem) p.m) (hPD : ∀ l < p.k, p.PD l < p.m) (hk0 : 0 < p.k)
    (hfr : p.d + 4 + 7 * p.m ≤ A0) (hsg : p.PDb + p.k ≤ A0)
    (hW1 : 16 * (p.Qb A0 + 15 * p.k + 2) ≤ W) (hW2 : ∑ i ∈ range p.m, p.FLW i + 6 ≤ W) :
    ∃ c' t, Exec P W fpProA c c' t ∧ t ≤ 150 * p.m + 19 * p.k + 140 ∧
      RegP1 p A0 c' ∧ c'.nreg 9419 = p.cw.cnt ∧ (∀ a < A0, c'.nmem a = p.mem a) ∧
      (∀ i < p.m, c'.nmem (A0 + p.m + i) = p.lab i) ∧
      (∀ a ≤ p.m, c'.nmem (A0 + p.m + p.m + p.m + a) = p.cw.mks a) ∧
      (∀ x < p.cw.cnt, c'.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m + x) =
        p.cw.bt x) ∧
      (∀ i < p.m, c'.nmem (A0 + p.m + p.m + p.m + p.m + 1 + i) = p.vl i + 1) ∧
      (∀ v < p.m, c'.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + v) = dvS p.vl p.FLW p.m v ∧
        c'.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + v) = dvC p.vl p.m v) ∧
      (∀ r, ¬ proScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hQ : p.Qb A0 = A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m + p.m := rfl
  have hPDb : p.PDb = p.Gb + 1 + p.ns + p.ns + p.off := rfl
  obtain ⟨c₁, t₁, e₁, ht₁, R1, a5030, a5031, a4470, a4471, a4472, a4473, a7350, a7351, a7352,
      a8430, ak, am, ar, arm, ao⟩ :=
    proP1a_exec (P := P) p c hc r04 r06 r07 r00 (by rw [hmem _ (by omega)]; exact hm)
      (by rw [hmem _ (by omega)]; exact hZ) (by rw [hmem _ (by omega)]; exact hns)
      (by rw [hmem _ (by omega)]; exact hoff) (by rw [hmem _ (by omega)]; exact hk) (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, blo, bNX, bFL, bON, bMK, bLAB, bDV, -, bk, br, brm, bo⟩ :=
    proP1b_exec (P := P) p c₁ e₁.wb_right (A0 := A0)
      (by rw [ak _ (by simp [scr1]), r04]) a5030 a5031 a4470 a4471 a4472 a4473 a7350 a7351
      a7352 a8430 (fun a ha => by rw [am]; exact hmem a ha) hm hRV hSG hNX hfr (by omega) hW2
  have R2 : RegP1 p A0 c₂ := R1.congr fun r hr _ _ _ => bk r (by omega) (by omega) (by omega)
    (by omega) (by omega)
  obtain ⟨c₃, t₃, e₃, ht₃, cON, cMK, cBT, c19, ck, cn, cr, crm, co⟩ :=
    proP2_exec (P := P) p c₂ e₂.wb_right R2 blo bNX bFL bON bMK hRV hSG hNX hPD hk0 hfr hsg
      (by omega)
  refine ⟨c₃, _, e₁.seq (e₂.seq e₃), by omega,
    R2.congr fun r hr h19 _ _ => cn r (by omega) (by omega) h19, c19,
    fun a ha => by rw [ck a (by omega) (by omega) (by omega)]; exact blo a ha,
    fun i hi => by rw [ck _ (by omega) (by omega) (by omega)]; exact bFL i hi, cMK, cBT,
    fun i hi => by rw [ck _ (by omega) (by omega) (by omega)]; exact bLAB i hi,
    fun v hv => by
      rw [ck _ (by omega) (by omega) (by omega), ck _ (by omega) (by omega) (by omega)]
      exact bDV v hv,
    fun r hr => ?_, by rw [cr, br, ar], by rw [crm, brm, arm], by rw [co, bo, ao]⟩
  have hr' := hr
  simp only [proScr, scr1, not_or] at hr'
  rw [cn r (by omega) (by omega) (by omega), bk r (by omega) (by omega) (by omega) (by omega)
    (by omega), ak r (fun h => hr (Or.inl h))]

/-- Part 3. -/
def fpProB : Stmt := .seq proP3a (.seq proP3b proP3c)

theorem fpProB_exec (p : FpIn) (c : Config) (hc : WordsBounded W c) {A0 : ℕ}
    (hR : RegP1 p A0 c) (h19 : c.nreg 9419 = p.cw.cnt) (hlo : ∀ a < A0, c.nmem a = p.mem a)
    (hFLm : ∀ i < p.m, c.nmem (A0 + p.m + i) = p.lab i)
    (hMKm : ∀ a ≤ p.m, c.nmem (A0 + p.m + p.m + p.m + a) = p.cw.mks a)
    (hBT : ∀ x < p.cw.cnt, c.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m + x) =
        p.cw.bt x)
    (hLAB : ∀ i < p.m, c.nmem (A0 + p.m + p.m + p.m + p.m + 1 + i) = p.vl i + 1)
    (hDV : ∀ v < p.m, c.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + v) = dvS p.vl p.FLW p.m v ∧
        c.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + v) = dvC p.vl p.m v)
    (hRV : ∀ i < p.m, p.RV i < p.m) (hSG : PermOn (sgF p.d p.m p.mem) p.m)
    (hNX : PermOn (nxF p.d p.m p.mem) p.m) (hPD : ∀ l < p.k, p.PD l < p.m)
    (hfr : p.d + 4 + 7 * p.m ≤ A0) (hsg : p.PDb + p.k ≤ A0) (hcnt : p.cw.cnt ≤ p.m)
    (hW1 : 16 * (p.Qb A0 + 15 * p.k + 2) ≤ W)
    (hW2 : ∑ i ∈ range p.m, p.FLW i + p.AS + 16 * fpB p.AS p.m p.k + p.m * p.Z + p.Z + p.k + 16
      ≤ W) :
    ∃ c' t, Exec P W fpProB c c' t ∧ t ≤ 12 * p.m + 84 * p.k + 40 ∧ ProOut p A0 c' ∧
      (∀ r, (r < 9456 ∨ 9497 < r) → r ≠ 9420 → r ≠ 9373 → r ≠ 9422 → r ≠ 9310 →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hQ : p.Qb A0 = A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m + p.m := rfl
  obtain ⟨c₁, t₁, e₁, ht₁, a20, a73, a22, a10, aCL, am, an, ar, arm, ao⟩ :=
    proP3a_exec (P := P) p c hc hR hlo hfr (by omega) (by omega)
  have R1 : RegP1 p A0 c₁ := hR.congr fun r hr _ h2 h3 => an r h2 (by omega) h3 (by omega)
    (by omega)
  have m1 : ∀ a, a < A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m → c₁.nmem a = c.nmem a :=
    fun a ha => am a (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, bS, bk, bn, br, brm, bo⟩ :=
    proP3b_exec (P := P) p c₁ e₁.wb_right R1 a10 (fun a ha => by rw [m1 a (by omega)]; exact hlo a ha)
      (fun i hi => by rw [m1 _ (by omega)]; exact hLAB i hi)
      (fun v hv => by rw [m1 _ (by omega), m1 _ (by omega)]; exact hDV v hv) hRV hSG hPD hfr hsg
      hW1 (by
        have : p.K ≤ 16 * fpB p.AS p.m p.k := le_rfl
        omega)
  have R2 : RegP1 p A0 c₂ := R1.congr fun r hr _ _ _ => bn r (by omega)
  obtain ⟨c₃, t₃, e₃, ht₃, cE, cP, ck, cn, cr, crm, co⟩ :=
    proP3c_exec (P := P) p c₂ e₂.wb_right R2 (by rw [bn _ (by omega), a10])
      (fun a ha => by rw [bk a (by omega) (by omega), m1 a (by omega)]; exact hlo a ha)
      (fun i hi => by rw [bk _ (by omega) (by omega), m1 _ (by omega)]; exact hFLm i hi)
      (fun a ha => by rw [bk _ (by omega) (by omega), m1 _ (by omega)]; exact hMKm a ha)
      hRV hNX hPD hfr hsg hW1
  have n3 : ∀ r, (r < 9456 ∨ 9497 < r) → c₃.nreg r = c₂.nreg r := fun r hr =>
    cn r (by omega) (by omega)
  refine ⟨c₃, _, e₁.seq (e₂.seq e₃), by omega,
    ⟨R2.congr fun r hr _ _ _ => cn r (by omega) (by omega),
      by rw [n3 _ (by omega), bn _ (by omega), an _ (by omega) (by omega) (by omega) (by omega)
        (by omega), h19],
      by rw [n3 _ (by omega), bn _ (by omega), a20], by rw [n3 _ (by omega), bn _ (by omega), a73],
      by rw [n3 _ (by omega), bn _ (by omega), a22], by rw [n3 _ (by omega), bn _ (by omega), a10],
      fun a ha => by
        rw [ck a (by omega) (by omega), bk a (by omega) (by omega), m1 a (by omega)]
        exact hlo a ha,
      fun i hi => by
        rw [ck _ (by omega) (by omega), bk _ (by omega) (by omega), m1 _ (by omega)]
        exact hFLm i hi,
      fun x hx => by
        rw [ck _ (by omega) (by omega), bk _ (by omega) (by omega),
          am _ (by omega)]
        exact hBT x hx,
      fun i hi => by rw [ck _ (by omega) (by omega), bk _ (by omega) (by omega)]; exact aCL i hi,
      fun l hl => by
        obtain ⟨s1, s2, s3, s4, s5⟩ := bS l hl
        exact ⟨by rw [ck _ (by omega) (by omega)]; exact s1,
          by rw [ck _ (by omega) (by omega)]; exact s2,
          by rw [ck _ (by omega) (by omega)]; exact s3,
          by rw [ck _ (by omega) (by omega)]; exact s4,
          by rw [ck _ (by omega) (by omega)]; exact s5⟩,
      cE, cP⟩,
    fun r h1 h2 h3 h4 h5 => by
      rw [n3 r h1, bn r (by omega), an r h2 h3 h4 h5 (by omega)],
    by rw [cr, br, ar], by rw [crm, brm, arm], by rw [co, bo, ao]⟩

/-- **The prologue of `fixP`.** -/
def fpPro : Stmt := .seq fpProA fpProB

/-- **The prologue of `fixP` on the machine**: from the frame and the parts of the separator
(natural data `p : FpIn`, memory below `A0 = r3006` equal to `p.mem`), within
`162 m + 103 k + 180` steps, the state `ProOut` (registers and arrays of the layout); the
registers outside `proScr`, reals and output kept. -/
theorem fpPro_exec (p : FpIn) (c : Config) (hc : WordsBounded W c) {A0 j : ℕ}
    (r04 : c.nreg 3004 = p.d) (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = p.Gb)
    (r00 : c.nreg 6800 = j) (hmem : ∀ a < A0, c.nmem a = p.mem a)
    (hm : p.mem p.d = p.m) (hZ : p.mem (p.d + 3) = p.Z) (hns : p.mem p.Gb = p.ns)
    (hoff : p.mem (p.Gb + 1 + j) = p.off) (hk : p.mem (p.Gb + 1 + j + p.ns) = p.k)
    (hj : p.Gb + 1 + j + p.ns < A0)
    (hRV : ∀ i < p.m, p.RV i < p.m) (hSG : PermOn (sgF p.d p.m p.mem) p.m)
    (hNX : PermOn (nxF p.d p.m p.mem) p.m) (hPD : ∀ l < p.k, p.PD l < p.m) (hk0 : 0 < p.k)
    (hfr : p.d + 4 + 7 * p.m ≤ A0) (hsg : p.PDb + p.k ≤ A0)
    (hW1 : 16 * (p.Qb A0 + 15 * p.k + 2) ≤ W)
    (hW2 : ∑ i ∈ range p.m, p.FLW i + p.AS + 16 * fpB p.AS p.m p.k + p.m * p.Z + p.Z + p.k + 16
      ≤ W) :
    ∃ c' t, Exec P W fpPro c c' t ∧ t ≤ 162 * p.m + 103 * p.k + 180 ∧ ProOut p A0 c' ∧
      (∀ r, ¬ proScr r → r ≠ 9419 → r ≠ 9420 → r ≠ 9422 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, R1, a19, alo, aFL, aMK, aBT, aLAB, aDV, ak, ar, arm, ao⟩ :=
    fpProA_exec (P := P) p c hc r04 r06 r07 r00 hmem hm hZ hns hoff hk hj hRV hSG hNX hPD hk0
      hfr hsg hW1 (by omega)
  have hcnt : p.cw.cnt ≤ p.m :=
    (cwRun_inv _ _ _ (fun a => by simp only [FpIn.MK0]; split_ifs <;> first | exact fmk2_le_one |
      omega) p.m).cnt_le
  obtain ⟨c₂, t₂, e₂, ht₂, O, bk, br, brm, bo⟩ :=
    fpProB_exec (P := P) p c₁ e₁.wb_right R1 a19 alo aFL aMK aBT aLAB aDV hRV hSG hNX hPD hfr hsg
      hcnt hW1 hW2
  refine ⟨c₂, _, e₁.seq e₂, by omega, O, fun r h1 h2 h3 h4 => ?_, by rw [br, ar],
    by rw [brm, arm], by rw [bo, ao]⟩
  have h1' := h1
  simp only [proScr, scr1, not_or] at h1'
  rw [bk r (by omega) h3 (by omega) h4 (by omega), ak r h1]

end BKMNW

end PlanarFlow
