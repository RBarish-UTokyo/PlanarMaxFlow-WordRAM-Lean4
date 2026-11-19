module

public import PlanarFlow.BKMNW.MsCutB

/-!
# The cut map of the path on the machine, part C: the five value blocks

For the dart index `i = r8205` of `M`, each block computes the selection flag, the position and
the two words (reverse, next) of one kind of dart of the cut (`MsCutA`), from the arrays
`LF` (path flags, `r8220`), `TF` (root flags, `r8221`), `RE` (ranks of the copies, `r8222`),
`RK` (ranks of the roots, `r8223`), `TA` (the tour, `r8224`), `TI` (its inverse, `r8225`),
`RV`, `RT` (`r8226`, `r8227`) and the offsets `nE` (`r8228`), `nE + nT`, `nE + 2 nT`,
`nE + 3 nT` (`r8230 … r8232`):

* `valE` (copies, selected when `LF[i] = 0`): position `RE[i]`, words `RE[RV[i]]` and
  `TF[i] ≠ 0 ? nE + nT + RK[TA[i]] : RE[RT[i]]`;
* `val1` (pendant darts, selected when `TF[i] ≠ 0`): position `nE + RK[i]`, words
  `nE + nT + RK[i]` and `LF[i] ≠ 0 ? nE + nT + RK[TA[i]] : RE[i]`;
* `val2` (reverse pendant darts): `nE + nT + RK[i]`; `nE + RK[i]`, `nE + 3nT + RK[TI[i]]`;
* `val3` (ring darts): `nE + 2nT + RK[i]`; `nE + 3nT + RK[i]`, `nE + 2nT + RK[TA[i]]`;
* `val4` (reverse ring darts): `nE + 3nT + RK[i]`; `nE + 2nT + RK[i]`, `nE + RK[i]`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The parameter registers of the value blocks. -/
structure VRegs (c : Config) (LFb TFb REb RKb TAb TIb RVb RTb nE nT : ℕ) : Prop where
  r20 : c.nreg 8220 = LFb
  r21 : c.nreg 8221 = TFb
  r22 : c.nreg 8222 = REb
  r23 : c.nreg 8223 = RKb
  r24 : c.nreg 8224 = TAb
  r25 : c.nreg 8225 = TIb
  r26 : c.nreg 8226 = RVb
  r27 : c.nreg 8227 = RTb
  r28 : c.nreg 8228 = nE
  r30 : c.nreg 8230 = nE + nT
  r31 : c.nreg 8231 = nE + 2 * nT
  r32 : c.nreg 8232 = nE + 3 * nT

lemma VRegs.of {c d : Config} {LFb TFb REb RKb TAb TIb RVb RTb nE nT : ℕ}
    (h : VRegs c LFb TFb REb RKb TAb TIb RVb RTb nE nT)
    (hr : ∀ r, 8220 ≤ r → r ≤ 8232 → d.nreg r = c.nreg r) :
    VRegs d LFb TFb REb RKb TAb TIb RVb RTb nE nT :=
  ⟨by rw [hr _ (by omega) (by omega), h.r20], by rw [hr _ (by omega) (by omega), h.r21],
    by rw [hr _ (by omega) (by omega), h.r22], by rw [hr _ (by omega) (by omega), h.r23],
    by rw [hr _ (by omega) (by omega), h.r24], by rw [hr _ (by omega) (by omega), h.r25],
    by rw [hr _ (by omega) (by omega), h.r26], by rw [hr _ (by omega) (by omega), h.r27],
    by rw [hr _ (by omega) (by omega), h.r28], by rw [hr _ (by omega) (by omega), h.r30],
    by rw [hr _ (by omega) (by omega), h.r31], by rw [hr _ (by omega) (by omega), h.r32]⟩

/-! ### The copies -/

def vE1 : Stmt :=
  block [.addN 8211 8220 8205, .loadN 8211 8211, .subN 8206 8203 8211, .addN 8211 8222 8205,
    .loadN 8207 8211, .addN 8211 8226 8205, .loadN 8211 8211, .addN 8211 8222 8211,
    .loadN 8208 8211, .addN 8211 8221 8205, .loadN 8212 8211]

def vEt : Stmt :=
  block [.addN 8211 8224 8205, .loadN 8211 8211, .addN 8211 8223 8211, .loadN 8211 8211,
    .addN 8209 8230 8211]

def vEe : Stmt := block [.addN 8211 8227 8205, .loadN 8211 8211, .addN 8211 8222 8211,
  .loadN 8209 8211]

/-- **The value block of the copies.** -/
def valE : Stmt := .seq vE1 (.ifLtN 8204 8212 vEt vEe)

/-- The common hypotheses of the value blocks at the index `i`. -/
structure VHyp (c : Config) (i LFb TFb REb RKb TAb TIb RVb RTb nE nT m W : ℕ) : Prop where
  i_lt : i < m
  lf : c.nmem (LFb + i) ≤ 1
  rv : c.nmem (RVb + i) < m
  rt : c.nmem (RTb + i) < m
  ta : c.nmem (TAb + i) < m
  ti : c.nmem (TIb + i) < m
  rk : ∀ j < m, c.nmem (RKb + j) ≤ m
  re : ∀ j < m, c.nmem (REb + j) ≤ m
  wLF : LFb + m ≤ W
  wTF : TFb + m ≤ W
  wRE : REb + m ≤ W
  wRK : RKb + m ≤ W
  wTA : TAb + m ≤ W
  wTI : TIb + m ≤ W
  wRV : RVb + m ≤ W
  wRT : RTb + m ≤ W
  wN : nE + 3 * nT + m ≤ W

theorem valE_exec (c : Config) (hc : WordsBounded W c)
    {i LFb TFb REb RKb TAb TIb RVb RTb nE nT m : ℕ}
    (hR : VRegs c LFb TFb REb RKb TAb TIb RVb RTb nE nT) (r05 : c.nreg 8205 = i)
    (r03 : c.nreg 8203 = 1) (r04 : c.nreg 8204 = 0)
    (hH : VHyp c i LFb TFb REb RKb TAb TIb RVb RTb nE nT m W) :
    ∃ c' k, Exec P W valE c c' k ∧ k ≤ 17 ∧ c'.nreg 8206 = 1 - c.nmem (LFb + i) ∧
      c'.nreg 8207 = c.nmem (REb + i) ∧ c'.nreg 8208 = c.nmem (REb + c.nmem (RVb + i)) ∧
      c'.nreg 8209 = (if 0 < c.nmem (TFb + i) then nE + nT + c.nmem (RKb + c.nmem (TAb + i))
        else c.nmem (REb + c.nmem (RTb + i))) ∧
      (∀ r, (r < 8206 ∨ 8219 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hi, hlf, hrv, hrt, hta, hti, hrk, hre, w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hH
  obtain ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28, h30, h31, h32⟩ := hR
  obtain ⟨c₁, k₁, e₁, hk₁, a06, a07, a08, a12, aR, am, ar, arm, ao⟩ : ∃ c₁ k₁,
      Exec P W vE1 c c₁ k₁ ∧ k₁ = 11 ∧ c₁.nreg 8206 = 1 - c.nmem (LFb + i) ∧
      c₁.nreg 8207 = c.nmem (REb + i) ∧ c₁.nreg 8208 = c.nmem (REb + c.nmem (RVb + i)) ∧
      c₁.nreg 8212 = c.nmem (TFb + i) ∧
      (∀ r, r ≠ 8206 → r ≠ 8207 → r ≠ 8208 → r ≠ 8211 → r ≠ 8212 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold vE1
    exec_block
    all_goals try ((try config_simp); (try simp only [h20, h21, h22, h26, r05, r03]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun r a b d e f => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals first
      | (simp only [h20, h21, h22, h26, r05, r03]; done)
      | (simp only [upd_apply]; split_ifs <;> omega)
  have q : ∀ r, 8212 < r → c₁.nreg r = c.nreg r := fun r hr => aR r (by omega) (by omega)
    (by omega) (by omega) (by omega)
  by_cases ht : 0 < c.nmem (TFb + i)
  · obtain ⟨c₂, k₂, e₂, hk₂, b09, bR, bm, br, brm, bo⟩ : ∃ c₂ k₂,
        Exec P W vEt c₁ c₂ k₂ ∧ k₂ = 5 ∧
        c₂.nreg 8209 = nE + nT + c.nmem (RKb + c.nmem (TAb + i)) ∧
        (∀ r, r ≠ 8209 → r ≠ 8211 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
      have s24 : c₁.nreg 8224 = TAb := by rw [q _ (by omega), h24]
      have s23 : c₁.nreg 8223 = RKb := by rw [q _ (by omega), h23]
      have s30 : c₁.nreg 8230 = nE + nT := by rw [q _ (by omega), h30]
      have s05 : c₁.nreg 8205 = i := by rw [aR _ (by omega) (by omega) (by omega) (by omega)
        (by omega), r05]
      have hk := hrk _ hta
      have hw₁ := e₁.wb_right
      unfold vEt
      exec_block
      all_goals try ((try config_simp); (try simp only [s24, s23, s30, s05, am]); omega)
      refine ⟨rfl, ?_, fun r a b => ?_, rfl, rfl, rfl, rfl⟩
      all_goals config_simp
      all_goals first
        | (simp only [s24, s23, s30, s05, am]; done)
        | (simp only [upd_apply]; split_ifs <;> omega)
    have t : c₁.nreg 8204 < c₁.nreg 8212 := by
      rw [aR _ (by omega) (by omega) (by omega) (by omega) (by omega), r04, a12]; exact ht
    refine ⟨c₂, k₁ + (k₂ + 1), .seq e₁ (.ifLtN_true t e₂), by omega,
      by rw [bR _ (by omega) (by omega), a06], by rw [bR _ (by omega) (by omega), a07],
      by rw [bR _ (by omega) (by omega), a08], by rw [b09, iteT ht], fun r hr => ?_,
      by rw [bm, am], by rw [br, ar], by rw [brm, arm], by rw [bo, ao]⟩
    rw [bR r (by omega) (by omega), aR r (by omega) (by omega) (by omega) (by omega) (by omega)]
  · obtain ⟨c₂, k₂, e₂, hk₂, b09, bR, bm, br, brm, bo⟩ : ∃ c₂ k₂,
        Exec P W vEe c₁ c₂ k₂ ∧ k₂ = 4 ∧ c₂.nreg 8209 = c.nmem (REb + c.nmem (RTb + i)) ∧
        (∀ r, r ≠ 8209 → r ≠ 8211 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
      have s27 : c₁.nreg 8227 = RTb := by rw [q _ (by omega), h27]
      have s22 : c₁.nreg 8222 = REb := by rw [q _ (by omega), h22]
      have s05 : c₁.nreg 8205 = i := by rw [aR _ (by omega) (by omega) (by omega) (by omega)
        (by omega), r05]
      have hw₁ := e₁.wb_right
      unfold vEe
      exec_block
      all_goals try ((try config_simp); (try simp only [s27, s22, s05, am]); omega)
      refine ⟨rfl, ?_, fun r a b => ?_, rfl, rfl, rfl, rfl⟩
      all_goals config_simp
      all_goals first
        | (simp only [s27, s22, s05, am]; done)
        | (simp only [upd_apply]; split_ifs <;> omega)
    have t : ¬ c₁.nreg 8204 < c₁.nreg 8212 := by
      rw [aR _ (by omega) (by omega) (by omega) (by omega) (by omega), r04, a12]; exact ht
    refine ⟨c₂, k₁ + (k₂ + 2), .seq e₁ (.ifLtN_false t e₂), by omega,
      by rw [bR _ (by omega) (by omega), a06], by rw [bR _ (by omega) (by omega), a07],
      by rw [bR _ (by omega) (by omega), a08], by rw [b09, iteF ht], fun r hr => ?_,
      by rw [bm, am], by rw [br, ar], by rw [brm, arm], by rw [bo, ao]⟩
    rw [bR r (by omega) (by omega), aR r (by omega) (by omega) (by omega) (by omega) (by omega)]

/-! ### The pendant darts -/

def v11 : Stmt :=
  block [.addN 8211 8221 8205, .loadN 8206 8211, .addN 8211 8223 8205, .loadN 8213 8211,
    .addN 8207 8228 8213, .addN 8208 8230 8213, .addN 8211 8220 8205, .loadN 8212 8211]

def v1t : Stmt := vEt

def v1e : Stmt := block [.addN 8211 8222 8205, .loadN 8209 8211]

/-- **The value block of the pendant darts.** -/
def val1 : Stmt := .seq v11 (.ifLtN 8204 8212 v1t v1e)

theorem val1_exec (c : Config) (hc : WordsBounded W c)
    {i LFb TFb REb RKb TAb TIb RVb RTb nE nT m : ℕ}
    (hR : VRegs c LFb TFb REb RKb TAb TIb RVb RTb nE nT) (r05 : c.nreg 8205 = i)
    (r04 : c.nreg 8204 = 0) (hH : VHyp c i LFb TFb REb RKb TAb TIb RVb RTb nE nT m W) :
    ∃ c' k, Exec P W val1 c c' k ∧ k ≤ 14 ∧ c'.nreg 8206 = c.nmem (TFb + i) ∧
      c'.nreg 8207 = nE + c.nmem (RKb + i) ∧ c'.nreg 8208 = nE + nT + c.nmem (RKb + i) ∧
      c'.nreg 8209 = (if 0 < c.nmem (LFb + i) then nE + nT + c.nmem (RKb + c.nmem (TAb + i))
        else c.nmem (REb + i)) ∧
      (∀ r, (r < 8206 ∨ 8219 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hi, hlf, hrv, hrt, hta, hti, hrk, hre, w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hH
  obtain ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28, h30, h31, h32⟩ := hR
  have hk0 := hrk i hi
  obtain ⟨c₁, k₁, e₁, hk₁, a06, a07, a08, a12, aR, am, ar, arm, ao⟩ : ∃ c₁ k₁,
      Exec P W v11 c c₁ k₁ ∧ k₁ = 8 ∧ c₁.nreg 8206 = c.nmem (TFb + i) ∧
      c₁.nreg 8207 = nE + c.nmem (RKb + i) ∧ c₁.nreg 8208 = nE + nT + c.nmem (RKb + i) ∧
      c₁.nreg 8212 = c.nmem (LFb + i) ∧
      (∀ r, r ≠ 8206 → r ≠ 8207 → r ≠ 8208 → r ≠ 8211 → r ≠ 8212 → r ≠ 8213 →
        c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold v11
    exec_block
    all_goals try ((try config_simp); (try simp only [h20, h21, h23, h28, h30, r05]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun r a b d e f g => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals first
      | (simp only [h20, h21, h23, h28, h30, r05]; done)
      | (simp only [upd_apply]; split_ifs <;> omega)
  have q : ∀ r, 8213 < r → c₁.nreg r = c.nreg r := fun r hr => aR r (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  have s05 : c₁.nreg 8205 = i := by
    rw [aR _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r05]
  by_cases ht : 0 < c.nmem (LFb + i)
  · obtain ⟨c₂, k₂, e₂, hk₂, b09, bR, bm, br, brm, bo⟩ : ∃ c₂ k₂,
        Exec P W v1t c₁ c₂ k₂ ∧ k₂ = 5 ∧
        c₂.nreg 8209 = nE + nT + c.nmem (RKb + c.nmem (TAb + i)) ∧
        (∀ r, r ≠ 8209 → r ≠ 8211 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
      have s24 : c₁.nreg 8224 = TAb := by rw [q _ (by omega), h24]
      have s23 : c₁.nreg 8223 = RKb := by rw [q _ (by omega), h23]
      have s30 : c₁.nreg 8230 = nE + nT := by rw [q _ (by omega), h30]
      have hk := hrk _ hta
      have hw₁ := e₁.wb_right
      unfold v1t vEt
      exec_block
      all_goals try ((try config_simp); (try simp only [s24, s23, s30, s05, am]); omega)
      refine ⟨rfl, ?_, fun r a b => ?_, rfl, rfl, rfl, rfl⟩
      all_goals config_simp
      all_goals first
        | (simp only [s24, s23, s30, s05, am]; done)
        | (simp only [upd_apply]; split_ifs <;> omega)
    have t : c₁.nreg 8204 < c₁.nreg 8212 := by
      rw [aR _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r04, a12]
      exact ht
    refine ⟨c₂, k₁ + (k₂ + 1), .seq e₁ (.ifLtN_true t e₂), by omega,
      by rw [bR _ (by omega) (by omega), a06], by rw [bR _ (by omega) (by omega), a07],
      by rw [bR _ (by omega) (by omega), a08], by rw [b09, iteT ht], fun r hr => ?_,
      by rw [bm, am], by rw [br, ar], by rw [brm, arm], by rw [bo, ao]⟩
    rw [bR r (by omega) (by omega), aR r (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]
  · obtain ⟨c₂, k₂, e₂, hk₂, b09, bR, bm, br, brm, bo⟩ : ∃ c₂ k₂,
        Exec P W v1e c₁ c₂ k₂ ∧ k₂ = 2 ∧ c₂.nreg 8209 = c.nmem (REb + i) ∧
        (∀ r, r ≠ 8209 → r ≠ 8211 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
      have s22 : c₁.nreg 8222 = REb := by rw [q _ (by omega), h22]
      have hw₁ := e₁.wb_right
      unfold v1e
      exec_block
      all_goals try ((try config_simp); (try simp only [s22, s05, am]); omega)
      refine ⟨rfl, ?_, fun r a b => ?_, rfl, rfl, rfl, rfl⟩
      all_goals config_simp
      all_goals first
        | (simp only [s22, s05, am]; done)
        | (simp only [upd_apply]; split_ifs <;> omega)
    have t : ¬ c₁.nreg 8204 < c₁.nreg 8212 := by
      rw [aR _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r04, a12]
      exact ht
    refine ⟨c₂, k₁ + (k₂ + 2), .seq e₁ (.ifLtN_false t e₂), by omega,
      by rw [bR _ (by omega) (by omega), a06], by rw [bR _ (by omega) (by omega), a07],
      by rw [bR _ (by omega) (by omega), a08], by rw [b09, iteF ht], fun r hr => ?_,
      by rw [bm, am], by rw [br, ar], by rw [brm, arm], by rw [bo, ao]⟩
    rw [bR r (by omega) (by omega), aR r (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]

/-! ### The reverse pendant darts, the ring and its reverse -/

/-- **The value block of the reverse pendant darts.** -/
def val2 : Stmt :=
  block [.addN 8211 8221 8205, .loadN 8206 8211, .addN 8211 8223 8205, .loadN 8213 8211,
    .addN 8207 8230 8213, .addN 8208 8228 8213, .addN 8211 8225 8205, .loadN 8211 8211,
    .addN 8211 8223 8211, .loadN 8211 8211, .addN 8209 8232 8211]

/-- **The value block of the ring darts.** -/
def val3 : Stmt :=
  block [.addN 8211 8221 8205, .loadN 8206 8211, .addN 8211 8223 8205, .loadN 8213 8211,
    .addN 8207 8231 8213, .addN 8208 8232 8213, .addN 8211 8224 8205, .loadN 8211 8211,
    .addN 8211 8223 8211, .loadN 8211 8211, .addN 8209 8231 8211]

/-- **The value block of the reverse ring darts.** -/
def val4 : Stmt :=
  block [.addN 8211 8221 8205, .loadN 8206 8211, .addN 8211 8223 8205, .loadN 8213 8211,
    .addN 8207 8232 8213, .addN 8208 8231 8213, .addN 8209 8228 8213]

set_option maxHeartbeats 1000000 in
theorem val2_exec (c : Config) (hc : WordsBounded W c)
    {i LFb TFb REb RKb TAb TIb RVb RTb nE nT m : ℕ}
    (hR : VRegs c LFb TFb REb RKb TAb TIb RVb RTb nE nT) (r05 : c.nreg 8205 = i)
    (hH : VHyp c i LFb TFb REb RKb TAb TIb RVb RTb nE nT m W) :
    ∃ c' k, Exec P W val2 c c' k ∧ k ≤ 11 ∧ c'.nreg 8206 = c.nmem (TFb + i) ∧
      c'.nreg 8207 = nE + nT + c.nmem (RKb + i) ∧ c'.nreg 8208 = nE + c.nmem (RKb + i) ∧
      c'.nreg 8209 = nE + 3 * nT + c.nmem (RKb + c.nmem (TIb + i)) ∧
      (∀ r, (r < 8206 ∨ 8219 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hi, hlf, hrv, hrt, hta, hti, hrk, hre, w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hH
  obtain ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28, h30, h31, h32⟩ := hR
  have hk0 := hrk i hi
  have hk1 := hrk _ hti
  unfold val2
  exec_block
  all_goals try ((try config_simp); (try simp only [h21, h23, h25, h28, h30, h32, r05]); omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [h21, h23, h25, h28, h30, h32, r05]; done)
    | (simp only [upd_apply]; split_ifs <;> omega)

set_option maxHeartbeats 1000000 in
theorem val3_exec (c : Config) (hc : WordsBounded W c)
    {i LFb TFb REb RKb TAb TIb RVb RTb nE nT m : ℕ}
    (hR : VRegs c LFb TFb REb RKb TAb TIb RVb RTb nE nT) (r05 : c.nreg 8205 = i)
    (hH : VHyp c i LFb TFb REb RKb TAb TIb RVb RTb nE nT m W) :
    ∃ c' k, Exec P W val3 c c' k ∧ k ≤ 11 ∧ c'.nreg 8206 = c.nmem (TFb + i) ∧
      c'.nreg 8207 = nE + 2 * nT + c.nmem (RKb + i) ∧
      c'.nreg 8208 = nE + 3 * nT + c.nmem (RKb + i) ∧
      c'.nreg 8209 = nE + 2 * nT + c.nmem (RKb + c.nmem (TAb + i)) ∧
      (∀ r, (r < 8206 ∨ 8219 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hi, hlf, hrv, hrt, hta, hti, hrk, hre, w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hH
  obtain ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28, h30, h31, h32⟩ := hR
  have hk0 := hrk i hi
  have hk1 := hrk _ hta
  unfold val3
  exec_block
  all_goals try ((try config_simp); (try simp only [h21, h23, h24, h31, h32, r05]); omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [h21, h23, h24, h31, h32, r05]; done)
    | (simp only [upd_apply]; split_ifs <;> omega)

theorem val4_exec (c : Config) (hc : WordsBounded W c)
    {i LFb TFb REb RKb TAb TIb RVb RTb nE nT m : ℕ}
    (hR : VRegs c LFb TFb REb RKb TAb TIb RVb RTb nE nT) (r05 : c.nreg 8205 = i)
    (hH : VHyp c i LFb TFb REb RKb TAb TIb RVb RTb nE nT m W) :
    ∃ c' k, Exec P W val4 c c' k ∧ k ≤ 7 ∧ c'.nreg 8206 = c.nmem (TFb + i) ∧
      c'.nreg 8207 = nE + 3 * nT + c.nmem (RKb + i) ∧
      c'.nreg 8208 = nE + 2 * nT + c.nmem (RKb + i) ∧
      c'.nreg 8209 = nE + c.nmem (RKb + i) ∧
      (∀ r, (r < 8206 ∨ 8219 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hi, hlf, hrv, hrt, hta, hti, hrk, hre, w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hH
  obtain ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28, h30, h31, h32⟩ := hR
  have hk0 := hrk i hi
  unfold val4
  exec_block
  all_goals try ((try config_simp); (try simp only [h21, h23, h28, h31, h32, r05]); omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [h21, h23, h28, h31, h32, r05]; done)
    | (simp only [upd_apply]; split_ifs <;> omega)

end MsEnc

end BKMNW

end PlanarFlow
