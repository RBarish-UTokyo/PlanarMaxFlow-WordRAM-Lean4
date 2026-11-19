module

public import PlanarFlow.NegSSSP.Enc.SdWalkF

/-!
# The registers of the walk of a side (`StR` after the separator run)

`sdWalk_exec` reads the layout registers `10`, `800 … 810` (of `faceWalk`), `301 … 318`
(`StR`, of `stPhase`: the separator run overwrites them) and `2550 … 2561` (of `sdSide`). They
are layout values: polynomials of the sizes of the piece map (`r960 = m'`, `r961 = nV`,
`r962 = nF`, `r801 = Y` the base of its plain encoding, as `bigProg_spec''` leaves them) and of
seven caller values in `r2790 … r2796` (the walk's area `T₀`, the marks `bz` and the side value
`sv`, the flags `bK`, the lengths `bL`, a bound `Ck` of the length of the cycle, the base `I0` of
the arrays).

`swSet` (a straight block, `41` steps): `bA = T₀ + 3 (nV + nF) + 6 m' + Ck`, `bV = bA + 3 m'`,
`S = bV + 3 m'`. **`swSet_exec`**: all the register hypotheses of `sdWalk_exec` (`StR` included);
registers outside `10`, `300 … 318`, `800 … 810`, `2550 … 2561`, `2797`, `2798` kept; memory,
reals, output kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs PlanarSeparator.MillerProg

variable {P : Input} {W : ℕ}

/-- The registers of `faceWalk`. -/
def swA1 : Stmt := block [.constN 10 1,
  .copyN 800 960, .addN 802 801 960, .addN 803 802 960, .addN 804 803 960, .addN 805 804 960,
  .copyN 806 2791, .copyN 807 961, .copyN 808 962, .copyN 809 2792, .copyN 810 2790]

/-- The layout: `r305 = bA`, `r317 = bV`, `r2560 = S`, `r2555 = nV + nF`. -/
def swA2 : Stmt := block [.addN 2555 961 962,
  .constN 2797 3, .mulN 2798 2797 2555, .addN 305 2790 2798, .constN 2797 6,
  .mulN 2798 2797 960, .addN 305 305 2798, .addN 305 305 2795,
  .constN 2797 3, .mulN 2798 2797 960, .addN 317 305 2798, .addN 2560 317 2798]

/-- The rest of `StR`. -/
def swA3 : Stmt := block [.copyN 301 960, .copyN 302 801, .copyN 303 802, .copyN 304 803,
  .constN 306 3, .constN 307 1, .constN 308 2, .copyN 315 804, .copyN 316 805, .copyN 318 961]

/-- The registers of `sdSide`. -/
def swA4 : Stmt := block [.copyN 2550 960, .copyN 2551 2791, .copyN 2552 2792,
  .copyN 2553 305, .copyN 2554 317, .copyN 2556 2793, .copyN 2557 2794, .copyN 2561 2796]

/-- **The registers of the walk of a side** (see the module docstring). -/
def swSet : Stmt := .seq swA1 (.seq swA2 (.seq swA3 swA4))

theorem swSet_natOnly : Klein.natOnly swSet = true := by kernel_rfl

/-- The base of the reversals of the stellar subdivision. -/
def swA (T₀ m nV nF Ck : ℕ) : ℕ := T₀ + 3 * (nV + nF) + 6 * m + Ck

theorem swA1_exec (c : Config) (hc : WordsBounded W c) {m Y T₀ bz sv : ℕ}
    (r960 : c.nreg 960 = m) (r801 : c.nreg 801 = Y) (r90 : c.nreg 2790 = T₀)
    (r91 : c.nreg 2791 = bz) (r92 : c.nreg 2792 = sv) (hY : Y + 4 * m ≤ W) (h1 : 1 ≤ W) :
    ∃ c' t, Exec P W swA1 c c' t ∧ t = 11 ∧
      c'.nreg 10 = 1 ∧ c'.nreg 800 = m ∧ c'.nreg 801 = Y ∧ c'.nreg 802 = Y + m ∧
      c'.nreg 803 = Y + 2 * m ∧ c'.nreg 804 = Y + 3 * m ∧ c'.nreg 805 = Y + 4 * m ∧
      c'.nreg 806 = bz ∧ c'.nreg 807 = c.nreg 961 ∧ c'.nreg 808 = c.nreg 962 ∧
      c'.nreg 809 = sv ∧ c'.nreg 810 = T₀ ∧
      (∀ r, r ≠ 10 → (r < 800 ∨ 810 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold swA1
  exec_block
  all_goals try ((try config_simp); (try simp only [r960, r801, r90, r91, r92]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl,
    rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r960, r801, r90, r91, r92])
  all_goals try omega
  simp only [upd_apply]; split_ifs <;> omega

theorem swA2_exec (c : Config) (hc : WordsBounded W c) {m nV nF T₀ Ck : ℕ}
    (r960 : c.nreg 960 = m) (r961 : c.nreg 961 = nV) (r962 : c.nreg 962 = nF)
    (r90 : c.nreg 2790 = T₀) (r95 : c.nreg 2795 = Ck)
    (hW : swA T₀ m nV nF Ck + 6 * m ≤ W) (h6 : 6 ≤ W) :
    ∃ c' t, Exec P W swA2 c c' t ∧ t = 12 ∧
      c'.nreg 2555 = nV + nF ∧ c'.nreg 305 = swA T₀ m nV nF Ck ∧
      c'.nreg 317 = swA T₀ m nV nF Ck + 3 * m ∧ c'.nreg 2560 = swA T₀ m nV nF Ck + 6 * m ∧
      (∀ r, r ≠ 2555 → r ≠ 305 → r ≠ 317 → r ≠ 2560 → r ≠ 2797 → r ≠ 2798 →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold swA2
  unfold swA at hW
  exec_block
  all_goals try ((try config_simp); (try simp only [r960, r961, r962, r90, r95]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r960, r961, r962, r90, r95, swA])
  all_goals try omega
  simp only [upd_apply]; split_ifs <;> omega

theorem swA3_exec (c : Config) (hc : WordsBounded W c) (h3 : 3 ≤ W) :
    ∃ c' t, Exec P W swA3 c c' t ∧ t = 10 ∧
      c'.nreg 301 = c.nreg 960 ∧ c'.nreg 302 = c.nreg 801 ∧ c'.nreg 303 = c.nreg 802 ∧
      c'.nreg 304 = c.nreg 803 ∧ c'.nreg 306 = 3 ∧ c'.nreg 307 = 1 ∧ c'.nreg 308 = 2 ∧
      c'.nreg 315 = c.nreg 804 ∧ c'.nreg 316 = c.nreg 805 ∧ c'.nreg 318 = c.nreg 961 ∧
      (∀ r, (r < 301 ∨ 318 < r ∨ r = 305 ∨ r = 309 ∨ r = 310 ∨ r = 311 ∨ r = 312 ∨ r = 313 ∨
        r = 314 ∨ r = 317) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold swA3
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

theorem swA4_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W swA4 c c' t ∧ t = 8 ∧
      c'.nreg 2550 = c.nreg 960 ∧ c'.nreg 2551 = c.nreg 2791 ∧ c'.nreg 2552 = c.nreg 2792 ∧
      c'.nreg 2553 = c.nreg 305 ∧ c'.nreg 2554 = c.nreg 317 ∧ c'.nreg 2556 = c.nreg 2793 ∧
      c'.nreg 2557 = c.nreg 2794 ∧ c'.nreg 2561 = c.nreg 2796 ∧
      (∀ r, (r < 2550 ∨ 2561 < r ∨ r = 2555 ∨ r = 2558 ∨ r = 2559 ∨ r = 2560) →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold swA4
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

/-- **The registers of the walk of a side on the machine** (see the module docstring). -/
theorem swSet_exec (c : Config) (hc : WordsBounded W c) {m nV nF Y T₀ bz sv bK bL Ck I0 : ℕ}
    (r960 : c.nreg 960 = m) (r961 : c.nreg 961 = nV) (r962 : c.nreg 962 = nF)
    (r801 : c.nreg 801 = Y) (r90 : c.nreg 2790 = T₀) (r91 : c.nreg 2791 = bz)
    (r92 : c.nreg 2792 = sv) (r93 : c.nreg 2793 = bK) (r94 : c.nreg 2794 = bL)
    (r95 : c.nreg 2795 = Ck) (r96 : c.nreg 2796 = I0)
    (hW : swA T₀ m nV nF Ck + 6 * m ≤ W) (hY : Y + 4 * m ≤ W) (h6 : 6 ≤ W) :
    ∃ c' t, Exec P W swSet c c' t ∧ t = 41 ∧
      c'.nreg 10 = 1 ∧ c'.nreg 800 = m ∧ c'.nreg 801 = Y ∧ c'.nreg 802 = Y + m ∧
      c'.nreg 803 = Y + 2 * m ∧ c'.nreg 804 = Y + 3 * m ∧ c'.nreg 805 = Y + 4 * m ∧
      c'.nreg 806 = bz ∧ c'.nreg 807 = nV ∧ c'.nreg 808 = nF ∧ c'.nreg 809 = sv ∧
      c'.nreg 810 = T₀ ∧
      StR m Y (Y + m) (Y + 2 * m) (swA T₀ m nV nF Ck) (Y + 3 * m) (Y + 4 * m)
        (swA T₀ m nV nF Ck + 3 * m) nV c' ∧
      c'.nreg 2550 = m ∧ c'.nreg 2551 = bz ∧ c'.nreg 2552 = sv ∧
      c'.nreg 2553 = swA T₀ m nV nF Ck ∧ c'.nreg 2554 = swA T₀ m nV nF Ck + 3 * m ∧
      c'.nreg 2555 = nV + nF ∧ c'.nreg 2556 = bK ∧ c'.nreg 2557 = bL ∧
      c'.nreg 2560 = swA T₀ m nV nF Ck + 6 * m ∧ c'.nreg 2561 = I0 ∧
      (∀ r, r ≠ 10 → (r < 300 ∨ 318 < r) → (r < 800 ∨ 810 < r) → (r < 2550 ∨ 2561 < r) →
        r ≠ 2797 → r ≠ 2798 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a10, a800, a801, a802, a803, a804, a805, a806, a807, a808, a809,
    a810, af, am, ar, arm, ao⟩ := swA1_exec (P := P) c hc r960 r801 r90 r91 r92 hY (by omega)
  have A : ∀ r, r ≠ 10 → (r < 800 ∨ 810 < r) → c₁.nreg r = c.nreg r := af
  obtain ⟨c₂, t₂, e₂, ht₂, b55, b305, b317, b60, bf, bm, br, brm, bo⟩ := swA2_exec (P := P) c₁
    e₁.wb_right (m := m) (nV := nV) (nF := nF) (T₀ := T₀) (Ck := Ck)
    ((A 960 (by omega) (by omega)).trans r960) ((A 961 (by omega) (by omega)).trans r961)
    ((A 962 (by omega) (by omega)).trans r962) ((A 2790 (by omega) (by omega)).trans r90)
    ((A 2795 (by omega) (by omega)).trans r95) hW h6
  obtain ⟨c₃, t₃, e₃, ht₃, d301, d302, d303, d304, d306, d307, d308, d315, d316, d318, df, dm,
    dr, drm, dO⟩ := swA3_exec (P := P) c₂ e₂.wb_right (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, g50, g51, g52, g53, g54, g56, g57, g61, gf, gm, gr, grm, go⟩ :=
    swA4_exec (P := P) c₃ e₃.wb_right
  have B : ∀ r, (r < 300 ∨ 318 < r) → r ≠ 2555 → r ≠ 2560 → r ≠ 2797 → r ≠ 2798 →
      c₃.nreg r = c₁.nreg r := fun r h1 h2 h3 h4 h5 =>
    (df r (by omega)).trans (bf r h2 (by omega) (by omega) h3 h4 h5)
  have G : ∀ r, (r < 2550 ∨ 2561 < r) → c₄.nreg r = c₃.nreg r := fun r h => gf r (by omega)
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => ?_, by rw [gm, dm, bm, am],
    by rw [gr, dr, br, ar], by rw [grm, drm, brm, arm], by rw [go, dO, bo, ao]⟩
  · rw [G 10 (by omega), B 10 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact a10
  · rw [G 800 (by omega), B 800 (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact a800
  · rw [G 801 (by omega), B 801 (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact a801
  · rw [G 802 (by omega), B 802 (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact a802
  · rw [G 803 (by omega), B 803 (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact a803
  · rw [G 804 (by omega), B 804 (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact a804
  · rw [G 805 (by omega), B 805 (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact a805
  · rw [G 806 (by omega), B 806 (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact a806
  · rw [G 807 (by omega), B 807 (by omega) (by omega) (by omega) (by omega) (by omega), a807,
      r961]
  · rw [G 808 (by omega), B 808 (by omega) (by omega) (by omega) (by omega) (by omega), a808,
      r962]
  · rw [G 809 (by omega), B 809 (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact a809
  · rw [G 810 (by omega), B 810 (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact a810
  · rw [G 301 (by omega), d301, bf 960 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; exact (A 960 (by omega) (by omega)).trans r960
  · rw [G 302 (by omega), d302, bf 801 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; exact a801
  · rw [G 303 (by omega), d303, bf 802 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; exact a802
  · rw [G 304 (by omega), d304, bf 803 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; exact a803
  · rw [G 305 (by omega), df 305 (by omega)]; exact b305
  · rw [G 306 (by omega)]; exact d306
  · rw [G 307 (by omega)]; exact d307
  · rw [G 308 (by omega)]; exact d308
  · rw [G 315 (by omega), d315, bf 804 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; exact a804
  · rw [G 316 (by omega), d316, bf 805 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; exact a805
  · rw [G 317 (by omega), df 317 (by omega)]; exact b317
  · rw [G 318 (by omega), d318, bf 961 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), A 961 (by omega) (by omega)]; exact r961
  · rw [g50, df 960 (by omega), bf 960 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), A 960 (by omega) (by omega)]; exact r960
  · rw [g51, B 2791 (by omega) (by omega) (by omega) (by omega) (by omega),
      A 2791 (by omega) (by omega)]; exact r91
  · rw [g52, B 2792 (by omega) (by omega) (by omega) (by omega) (by omega),
      A 2792 (by omega) (by omega)]; exact r92
  · rw [g53, df 305 (by omega)]; exact b305
  · rw [g54, df 317 (by omega)]; exact b317
  · rw [gf 2555 (by omega), df 2555 (by omega)]; exact b55
  · rw [g56, B 2793 (by omega) (by omega) (by omega) (by omega) (by omega),
      A 2793 (by omega) (by omega)]; exact r93
  · rw [g57, B 2794 (by omega) (by omega) (by omega) (by omega) (by omega),
      A 2794 (by omega) (by omega)]; exact r94
  · rw [gf 2560 (by omega), df 2560 (by omega)]; exact b60
  · rw [g61, B 2796 (by omega) (by omega) (by omega) (by omega) (by omega),
      A 2796 (by omega) (by omega)]; exact r96
  · rw [G r h4, B r h2 (by omega) (by omega) h5 h6, A r h1 h3]

end NegSSSP

end PlanarFlow
