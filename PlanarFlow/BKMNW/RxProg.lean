module

public import PlanarFlow.BKMNW.MfDrvX

/-!
# The root's decomposition record on the machine

After `rfProg` (the root frame at `d = Hb + 5`, `N` darts, ending at `e₀ = d + 4 + 7 N`),
**`rxProg`** writes the root's record at `R = e₀ + 1` and the pointer `mem e₀ := R`: header
`N | 0 | 1` (phase `0`: the root call `decS … univ [] st true`), then `GP` (copy of the frame's
`GID`), `RP` (copy of `RV`), `HP` (copy of `HL`, zeros), `KP` (copy of `KR`), `VP` (copy of an
input array `VT`), `SP` (copy of an input array `RT`: the state of `decS`), `FX` (copy of `GID`,
the identity); the bases of `VT` and `RT` are read from `mem (Hb - 1)`, `mem (Hb - 2)`; the frame
end `eF = R + 3 + 7 N` is stored at `Hb + 2` and in `r3003`.

* `rxA`, `rxB`, `rxCp` (a copy with the registers of `cpArr` set), **`rxProg_exec`**
  (`49 N + 120` steps). Registers `5700 … 5724`, `4910 … 4916`.
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

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

/-- The pointer, the header, the bases of the record. -/
def rxA : Stmt := block [.copyN 5700 3002, .constN 5701 5, .addN 5702 5700 5701,
  .loadN 5703 5702, .constN 5701 7, .mulN 5704 5701 5703, .addN 5705 5702 5704, .constN 5701 4,
  .addN 5705 5705 5701, .constN 5701 1, .addN 5706 5705 5701, .storeN 5705 5706,
  .storeN 5706 5703, .addN 5707 5706 5701, .constN 5708 0, .storeN 5707 5708,
  .addN 5707 5707 5701, .storeN 5707 5701, .addN 5709 5707 5701, .addN 5710 5709 5703,
  .addN 5711 5710 5703, .addN 5712 5711 5703, .addN 5713 5712 5703, .addN 5714 5713 5703,
  .addN 5715 5714 5703, .addN 5716 5715 5703]

/-- The frame's arrays, the input arrays, the new frame end. -/
def rxB : Stmt := block [.constN 5701 9, .addN 5717 5700 5701, .addN 5718 5717 5703,
  .addN 5719 5718 5703, .addN 5719 5719 5703, .addN 5719 5719 5703, .addN 5720 5719 5703,
  .constN 5701 1, .subN 5721 5700 5701, .loadN 5722 5721, .subN 5721 5721 5701,
  .loadN 5723 5721, .constN 5701 2, .addN 5724 5700 5701, .storeN 5724 5716, .copyN 3003 5716]

/-- A copy of `N = r5703` cells from `r src` to `r dst`. -/
def rxCp (src dst : ℕ) : Stmt := .seq (block [.copyN 4910 5703, .copyN 4911 src, .copyN 4912 dst])
  cpArr

/-- **The root's record.** -/
def rxProg : Stmt := .seq rxA (.seq rxB (.seq (rxCp 5717 5709) (.seq (rxCp 5718 5710)
  (.seq (rxCp 5720 5711) (.seq (rxCp 5719 5712) (.seq (rxCp 5722 5713) (.seq (rxCp 5723 5714)
    (rxCp 5717 5715))))))))

section Exec

variable {I : Input} {W : ℕ}

theorem rxA_exec (c : Config) (hc : WordsBounded W c) {Hb N : ℕ}
    (r2 : c.nreg 3002 = Hb) (hN : c.nmem (Hb + 5) = N) (w : Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N ≤ W) :
    ∃ c' t, Exec I W rxA c c' t ∧ t = 26 ∧ c'.nreg 5700 = Hb ∧ c'.nreg 5703 = N ∧
      c'.nreg 5709 = Hb + 5 + 4 + 7 * N + 1 + 3 ∧ c'.nreg 5710 = Hb + 5 + 4 + 7 * N + 1 + 3 + N ∧
      c'.nreg 5711 = Hb + 5 + 4 + 7 * N + 1 + 3 + 2 * N ∧
      c'.nreg 5712 = Hb + 5 + 4 + 7 * N + 1 + 3 + 3 * N ∧
      c'.nreg 5713 = Hb + 5 + 4 + 7 * N + 1 + 3 + 4 * N ∧
      c'.nreg 5714 = Hb + 5 + 4 + 7 * N + 1 + 3 + 5 * N ∧
      c'.nreg 5715 = Hb + 5 + 4 + 7 * N + 1 + 3 + 6 * N ∧
      c'.nreg 5716 = Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N ∧
      c'.nmem = upd (upd (upd (upd c.nmem (Hb + 5 + 4 + 7 * N) (Hb + 5 + 4 + 7 * N + 1))
        (Hb + 5 + 4 + 7 * N + 1) N) (Hb + 5 + 4 + 7 * N + 1 + 1) 0)
        (Hb + 5 + 4 + 7 * N + 1 + 1 + 1) 1 ∧
      (∀ x, x < 5700 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rxA
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r2, hN]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r2, hN])
    try omega
  all_goals rw [show Hb + 5 + 7 * N + 4 = Hb + 5 + 4 + 7 * N by omega]

theorem rxB_exec (c : Config) (hc : WordsBounded W c) {Hb N eF VTb RTb : ℕ}
    (r00 : c.nreg 5700 = Hb) (r03 : c.nreg 5703 = N) (r16 : c.nreg 5716 = eF) (hHb : 2 ≤ Hb)
    (hv : c.nmem (Hb - 1) = VTb) (hr : c.nmem (Hb - 1 - 1) = RTb) (w : Hb + 9 + 5 * N ≤ W) :
    ∃ c' t, Exec I W rxB c c' t ∧ t = 16 ∧ c'.nreg 5717 = Hb + 9 ∧
      c'.nreg 5718 = Hb + 9 + N ∧ c'.nreg 5719 = Hb + 9 + 4 * N ∧ c'.nreg 5720 = Hb + 9 + 5 * N ∧
      c'.nreg 5722 = VTb ∧ c'.nreg 5723 = RTb ∧ c'.nreg 3003 = eF ∧
      c'.nmem = upd c.nmem (Hb + 2) eF ∧
      (∀ x, (x < 3003 ∨ (3003 < x ∧ x < 5701) ∨ (5701 < x ∧ x < 5717) ∨ 5724 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hc.1 5716
  unfold rxB
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r00, r03, r16]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r00, r03, r16, hv, hr])
    try omega

theorem rxCp_exec (c : Config) (hc : WordsBounded W c) {src dst N Sa Da : ℕ}
    (hs : 4916 < src) (hd : 4916 < dst) (r03 : c.nreg 5703 = N) (rs : c.nreg src = Sa)
    (rd : c.nreg dst = Da) (lay : Sa + N ≤ Da ∨ Da + N ≤ Sa) (w1 : Sa + N ≤ W) (w2 : Da + N ≤ W)
    (w3 : N + 1 ≤ W) :
    ∃ c' t, Exec I W (rxCp src dst) c c' t ∧ t ≤ 7 * N + 7 ∧
      (∀ i < N, c'.nmem (Da + i) = c.nmem (Sa + i)) ∧
      (∀ a, (a < Da ∨ Da + N ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4910 ∨ 4916 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, v10, v11, v12, n1, m1, rr1, rm1, o1⟩ : ∃ c₁ t₁,
      Exec I W (block [.copyN 4910 5703, .copyN 4911 src, .copyN 4912 dst]) c c₁ t₁ ∧ t₁ = 3 ∧
      c₁.nreg 4910 = N ∧ c₁.nreg 4911 = Sa ∧ c₁.nreg 4912 = Da ∧
      (∀ x, (x < 4910 ∨ 4912 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧
      c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    have := hc.1 5703; have := hc.1 src; have := hc.1 dst
    exec_block
    all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same, r03, rs, rd])
      try omega
  obtain ⟨c₂, t₂, e₂, ht₂, cp, mm, nn, rr2, rm2, o2⟩ := cpArr_exec (P := I) c₁ e₁.wb_right v10 v11
    v12 ⟨lay, w1, w2, w3⟩
  refine ⟨c₂, _, .seq e₁ e₂, by clear * - ht₁ ht₂; omega, fun i hi => by rw [cp i hi, m1],
    fun a ha => by rw [mm a ha, m1], fun x hx => by rw [nn x (by omega), n1 x (by omega)],
    by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩

end Exec

end MfDrv

end BKMNW

end PlanarFlow
