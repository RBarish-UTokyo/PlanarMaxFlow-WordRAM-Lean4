module

public import PlanarFlow.NegSSSP.NodeRunF
public import WordRAM.Machine.RealsToNat

/-!
# The glue programs of a node keep bounded integers in their reals

The programs of `PlanarFlow.NegSSSP.nodeProg` other than Klein's part (`kPart`: Klein's MSSP,
its encoding constants `kpR` and the reading `rdProg`), Bellman–Ford over the dense distance
graphs (`bfFull`) and FR-Dijkstra (`frProg`):

* **No real arithmetic** (`WordRAM.Machine.Stmt.ArithFree 0`, checked by `decide`): `bdSet`,
  `bdryProg`, `partSet`, `kpC`, `cornerProg`, `kpK`, `cpyProg`, `zeroRegs`, `restSet`,
  `permProg`, `bfIn`, `bfSet`, `clrProg`, `cpS`, `bfOut`, `glueP`, `cSet`, `cStore`, `sideSet`,
  `mSet`, `minProg`, `clrSet`, `pSet`, `aSet`, `aProg`, `csSet`, `csProg`, `cpSet`, `inpBlk`,
  `nSet`, `nrmProg`. By `WordRAM.Machine.Exec.toExecI_arithFree`, every run of one of them keeps
  any bound of its reals, with no hypothesis (`arithFree_execI`).
* **The lowering `C`** (`cProg`, `C = Σ |E i - δ₀ (n i)| + |E i - δ₁ (n i)|`):
  `cProg_execI_of_exec`, from reals bounded by `X`: `256 (4 b + 2) X` along the run,
  `(4 b + 2) X` at the end.
* **The initial lengths and the prices** (`pProg`, storing `E i - C`):
  `pProg_execI_of_exec`, `32 (2 b + 3) (b + 1) X` along the run, `(2 b + 3) (b + 1) X` at the
  end.

All these bounds hold for **every** run (no hypothesis on the start besides the bound `X`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

theorem instrs_block (l : List Instr) : (block l).instrs = l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [block, Stmt.instrs, ih]

/-! ### The programs without real arithmetic -/

theorem bdSet_arithFree : bdSet.ArithFree 0 := by decide +kernel
theorem bdryProg_arithFree : bdryProg.ArithFree 0 := by decide +kernel
theorem cornerProg_arithFree : cornerProg.ArithFree 0 := by decide +kernel
theorem cpyProg_arithFree : cpyProg.ArithFree 0 := by decide +kernel
theorem restSet_arithFree : restSet.ArithFree 0 := by decide +kernel
theorem permProg_arithFree : permProg.ArithFree 0 := by decide +kernel
theorem bfIn_arithFree : bfIn.ArithFree 0 := by decide +kernel
theorem bfSet_arithFree : bfSet.ArithFree 0 := by decide +kernel
theorem clrProg_arithFree : clrProg.ArithFree 0 := by decide +kernel
theorem bfOut_arithFree : bfOut.ArithFree 0 := by decide +kernel
theorem glueP_arithFree : glueP.ArithFree 0 := by decide +kernel
theorem cSet_arithFree : cSet.ArithFree 0 := by decide +kernel
theorem cStore_arithFree : cStore.ArithFree 0 := by decide +kernel
theorem mSet_arithFree : mSet.ArithFree 0 := by decide +kernel
theorem minProg_arithFree : minProg.ArithFree 0 := by decide +kernel
theorem clrSet_arithFree : clrSet.ArithFree 0 := by decide +kernel
theorem pSet_arithFree : pSet.ArithFree 0 := by decide +kernel
theorem aSet_arithFree : aSet.ArithFree 0 := by decide +kernel
theorem aProg_arithFree : aProg.ArithFree 0 := by decide +kernel
theorem csSet_arithFree : csSet.ArithFree 0 := by decide +kernel
theorem csProg_arithFree : csProg.ArithFree 0 := by decide +kernel
theorem cpSet_arithFree : cpSet.ArithFree 0 := by decide +kernel
theorem inpBlk_arithFree : inpBlk.ArithFree 0 := by decide +kernel
theorem nSet_arithFree : nSet.ArithFree 0 := by decide +kernel
theorem nrmProg_arithFree : nrmProg.ArithFree 0 := by decide +kernel

theorem zeroRegs_arithFree (l : List ℕ) : (zeroRegs l).ArithFree 0 := by
  intro i hi
  rw [zeroRegs, instrs_block, List.mem_map] at hi
  obtain ⟨r, -, rfl⟩ := hi
  exact ⟨trivial, rfl⟩

theorem partSet_arithFree (z δr : ℕ) : (partSet z δr).ArithFree 0 := by
  intro i hi; rw [partSet, instrs_block] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨trivial, rfl⟩

theorem kpC_arithFree (k Pb : ℕ) : (kpC k Pb).ArithFree 0 := by
  intro i hi; rw [kpC, instrs_block] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨trivial, rfl⟩

theorem kpK_arithFree (nD Rk : ℕ) : (kpK nD Rk).ArithFree 0 := by
  intro i hi; rw [kpK, instrs_block] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact ⟨trivial, rfl⟩

theorem cpS_arithFree (rn rDn rSn rDr rSr : ℕ) : (cpS rn rDn rSn rDr rSr).ArithFree 0 := by
  intro i hi; rw [cpS, instrs_block] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact ⟨trivial, rfl⟩

theorem sideSet_arithFree (s δr Fr Vr : ℕ) : (sideSet s δr Fr Vr).ArithFree 0 := by
  intro i hi; rw [sideSet, instrs_block] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> exact ⟨trivial, rfl⟩

/-- **Every run of a program without real arithmetic keeps the bound of its reals.** -/
theorem arithFree_execI {s : Stmt} (hs : s.ArithFree 0) {X : ℕ} {c c' : Config} {k : ℕ}
    (hc : RealsIntBounded X c) (e : Exec P W s c c' k) :
    ExecI P (fun c => WordsBounded W c ∧ RealsIntBounded X c) s c c' k ∧ RealsIntBounded X c' :=
  e.toExecI_arithFree hs (Nat.zero_le X) hc

/-! ### Small facts on bounded values -/

/-- A value that is an integer of absolute value at most `X`. -/
def IB (X : ℕ) (x : ℝ) : Prop := ∃ z : ℤ, x = z ∧ |z| ≤ (X : ℤ)

theorem IB.mono {X Y : ℕ} {x : ℝ} (h : IB X x) (hXY : X ≤ Y) : IB Y x := intB_mono h hXY

theorem IB.abs {X : ℕ} {x : ℝ} (h : IB X x) : IB X |x| :=
  let ⟨z, hz, hb⟩ := h; ⟨|z|, by rw [hz, Int.cast_abs], by rwa [abs_abs]⟩

theorem IB.zero (X : ℕ) : IB X 0 := ⟨0, by simp, by simp⟩

/-- An update away from the register `j`. -/
theorem ib_upd_ne {X j : ℕ} {f : ℕ → ℝ} (hf : ∀ r, r ≠ j → IB X (f r)) (i : ℕ) {x : ℝ}
    (hx : IB X x) : ∀ r, r ≠ j → IB X (upd f i x r) := fun r hr => by
  by_cases h : r = i
  · subst h; simpa using hx
  · rw [upd_other _ _ _ h]; exact hf r hr

/-! ### `acc += |x|` -/

theorem absAdd_fx {acc x t z : ℕ} (h1 : acc ≠ x) (h2 : acc ≠ t) (h4 : x ≠ t)
    {c c' : Config} {k : ℕ} (e : Exec P W (absAdd acc x t z) c c' k) (hz : c.rreg z = 0) :
    c'.rmem = c.rmem ∧ c'.nreg = c.nreg ∧ c'.nmem = c.nmem ∧ c'.output = c.output ∧
      c'.rreg acc = c.rreg acc + |c.rreg x| ∧ (c'.rreg t = c.rreg t ∨ c'.rreg t = -c.rreg x) ∧
      ∀ r, r ≠ acc → r ≠ t → c'.rreg r = c.rreg r := by
  unfold absAdd at e
  cases e with
  | ifLtR_true hx e =>
    obtain ⟨he, -⟩ := e.block_effs
    simp only [blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at he
    subst he
    rw [hz] at hx
    refine ⟨rfl, rfl, rfl, rfl, ?_, Or.inr ?_, fun r hr ht => ?_⟩
    · simp only [upd_same, upd_other _ _ _ h2, upd_other _ _ _ h4.symm, hz, abs_of_neg hx]; ring
    · simp only [upd_same, upd_other _ _ _ h2.symm, hz, zero_sub]
    · simp only [upd_other _ _ _ hr, upd_other _ _ _ ht]
  | ifLtR_false hx e =>
    obtain ⟨he, -⟩ := e.block_effs
    simp only [blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at he
    subst he
    rw [hz] at hx
    refine ⟨rfl, rfl, rfl, rfl, ?_, Or.inl ?_, fun r hr ht => ?_⟩
    · simp only [upd_same, abs_of_nonneg (not_lt.1 hx)]
    · simp only [upd_other _ _ _ h2.symm]
    · simp only [upd_other _ _ _ hr]

/-- The bound after `acc += |x|`: the scratch `t` is `t` or `-x`. -/
theorem absAdd_ib {acc x t z : ℕ} (h1 : acc ≠ x) (h2 : acc ≠ t) (h4 : x ≠ t) (h5 : acc ≠ z)
    (h6 : t ≠ z) {X A : ℕ} {c c' : Config} {k : ℕ} (e : Exec P W (absAdd acc x t z) c c' k)
    (hz : c.rreg z = 0) (hr : ∀ r, r ≠ acc → IB X (c.rreg r)) (ha : IB A (c.rreg acc)) :
    c'.rmem = c.rmem ∧ c'.nreg = c.nreg ∧ c'.nmem = c.nmem ∧ c'.output = c.output ∧
      c'.rreg z = 0 ∧ (∀ r, r ≠ acc → IB X (c'.rreg r)) ∧ IB (A + X) (c'.rreg acc) ∧
      ∀ r, r ≠ acc → r ≠ t → c'.rreg r = c.rreg r := by
  obtain ⟨m, n, nm, o, hacc, ht, hother⟩ := absAdd_fx h1 h2 h4 e hz
  refine ⟨m, n, nm, o, by rw [hother z (Ne.symm h5) (Ne.symm h6), hz], fun r hra => ?_, ?_,
    hother⟩
  · by_cases hrt : r = t
    · subst hrt
      rcases ht with ht | ht
      · rw [ht]; exact hr _ hra
      · rw [ht]; exact intB_neg (hr x (Ne.symm h1))
    · rw [hother r hra hrt]; exact hr r hra
  · rw [hacc]; exact intB_add ha (hr x (Ne.symm h1)).abs

/-! ### The lowering `C` -/

/-- The state of the loop of `cProg` after `i = r511` pairs. -/
structure CI (W b X : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  r500 : c.nreg 500 = b
  r510 : c.nreg 510 = 1
  r511 : c.nreg 511 ≤ b
  z : c.rreg 501 = 0
  mem : ∀ a, IB X (c.rmem a)
  regs : ∀ r, r ≠ 500 → IB (2 * X) (c.rreg r)
  acc : IB (4 * c.nreg 511 * X) (c.rreg 500)

theorem CI.rib {W b X : ℕ} {c : Config} (h : CI W b X c) : RealsIntBounded ((4 * b + 2) * X) c :=
  ⟨fun r => by
    by_cases hr : r = 500
    · subst hr; refine h.acc.mono ?_
      have := Nat.mul_le_mul_right X (Nat.mul_le_mul_left 4 h.r511); nlinarith
    · exact (h.regs r hr).mono (by nlinarith),
    fun a => (h.mem a).mono (by nlinarith)⟩

theorem cBody_ci {b X : ℕ} {c c' : Config} {k : ℕ} (hI : CI W b X c) (hlt : c.nreg 511 < b)
    (e : Exec P W cBody c c' k) : CI W b X c' := by
  unfold cBody at e
  cases e with | @seq _ _ _ c1 _ _ _ er e =>
  cases e with | @seq _ _ _ c2 _ _ _ ea1 e =>
  cases e with | @seq _ _ _ c3 _ _ _ ea2 ei =>
  obtain ⟨he, -⟩ := er.block_effs
  simp only [cRead, blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at he
  have hm := hI.mem
  have f1m : c1.rmem = c.rmem := by rw [← he]
  have f1n : ∀ r, r ≠ 512 → r ≠ 513 → c1.nreg r = c.nreg r := fun r h1 h2 => by
    rw [← he]; simp only [upd_other _ _ _ h1, upd_other _ _ _ h2]
  have f1z : c1.rreg 501 = 0 := by rw [← he]; simp only [upd_other _ _ _ (by omega : (501 : ℕ) ≠ 506),
    upd_other _ _ _ (by omega : (501 : ℕ) ≠ 505), upd_other _ _ _ (by omega : (501 : ℕ) ≠ 502),
    upd_other _ _ _ (by omega : (501 : ℕ) ≠ 504)]; exact hI.z
  have f1a : c1.rreg 500 = c.rreg 500 := by rw [← he]; simp only [upd_other _ _ _ (by omega : (500 : ℕ) ≠ 506),
    upd_other _ _ _ (by omega : (500 : ℕ) ≠ 505), upd_other _ _ _ (by omega : (500 : ℕ) ≠ 502),
    upd_other _ _ _ (by omega : (500 : ℕ) ≠ 504)]
  have f1r : ∀ r, r ≠ 500 → IB (2 * X) (c1.rreg r) := by
    rw [← he]
    refine ib_upd_ne (ib_upd_ne (ib_upd_ne (ib_upd_ne (ib_upd_ne hI.regs 504
      ((hm _).mono (by omega))) 505 ((hm _).mono (by omega))) 502 ?_) 505
      ((hm _).mono (by omega))) 506 ?_
    · simp only [upd_same, upd_other _ _ _ (show (504 : ℕ) ≠ 505 by omega)]
      exact intB_mono (intB_sub (hm _) (hm _)) (by omega)
    · simp only [upd_same, upd_other _ _ _ (show (504 : ℕ) ≠ 505 by omega),
        upd_other _ _ _ (show (504 : ℕ) ≠ 502 by omega)]
      exact intB_mono (intB_sub (hm _) (hm _)) (by omega)
  obtain ⟨m2, n2, -, -, z2, r2, a2, -⟩ := absAdd_ib (by omega) (by omega) (by omega) (by omega)
    (by omega) ea1 f1z f1r (by rw [f1a]; exact hI.acc)
  obtain ⟨m3, n3, -, -, z3, r3, a3, -⟩ := absAdd_ib (by omega) (by omega) (by omega) (by omega)
    (by omega) ea2 z2 r2 a2
  obtain ⟨hei, -⟩ := ei.block_effs
  simp only [blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at hei
  have fn : ∀ r, r ≠ 511 → r ≠ 512 → r ≠ 513 → c'.nreg r = c.nreg r := fun r h0 h1 h2 => by
    rw [← hei]; simp only [upd_other _ _ _ h0]; rw [n3, n2, f1n r h1 h2]
  have f511 : c'.nreg 511 = c.nreg 511 + 1 := by
    rw [← hei]; simp only [upd_same]; rw [n3, n2, f1n _ (by omega) (by omega),
      f1n _ (by omega) (by omega), hI.r510]
  have fr : c'.rreg = c3.rreg := by rw [← hei]
  refine ⟨ei.wb_right, (fn 500 (by omega) (by omega) (by omega)).trans hI.r500,
    (fn 510 (by omega) (by omega) (by omega)).trans hI.r510, by omega, by rw [fr]; exact z3,
    fun a => by rw [← hei]; simp only; rw [m3, m2, f1m]; exact hm a,
    fun r hr => by rw [fr]; exact r3 r hr, ?_⟩
  rw [fr, f511]
  exact a3.mono (by nlinarith)

/-- **`cProg` keeps bounded integers**: from reals bounded by `X`, the reals stay bounded by
`256 (4 b + 2) X` along the run and by `(4 b + 2) X` at the end (`b = r500`, no other
hypothesis: the terms `|E i - δ|` are at most `2 X`). -/
theorem cProg_execI_of_exec {X : ℕ} {c₀ c' : Config} {k : ℕ} (hB : RealsIntBounded X c₀)
    (e : Exec P W cProg c₀ c' k) :
    ExecI P (fun c => WordsBounded W c ∧
        RealsIntBounded (256 * ((4 * c₀.nreg 500 + 2) * X)) c) cProg c₀ c' k ∧
      RealsIntBounded ((4 * c₀.nreg 500 + 2) * X) c' := by
  have hX1 : X ≤ (4 * c₀.nreg 500 + 2) * X := by nlinarith
  have hX2 : (4 * c₀.nreg 500 + 2) * X ≤ 256 * ((4 * c₀.nreg 500 + 2) * X) := by omega
  unfold cProg at e ⊢
  cases e with | @seq _ _ _ c1 _ _ _ e1 e2 =>
  obtain ⟨E1, -⟩ := e1.toExecI_arithFree (Bc := 0) (by decide) (Nat.zero_le _) hB
  obtain ⟨he, -⟩ := e1.block_effs
  simp only [blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at he
  have hI1 : CI W (c₀.nreg 500) X c1 := by
    refine ⟨e1.wb_right, by rw [← he]; simp [upd_apply], by rw [← he]; simp [upd_apply],
      by rw [← he]; simp [upd_apply], by rw [← he]; simp [upd_apply],
      fun a => by rw [← he]; exact hB.2 a, fun r hr => ?_, ?_⟩
    · rw [← he]; simp only
      exact intB_mono (intB_upd (intB_upd hB.1 500 ⟨0, by simp, by simp⟩) 501
        ⟨0, by simp, by simp⟩ r) (by omega)
    · rw [← he]; simp only [upd_same, upd_other _ _ _ (show (500 : ℕ) ≠ 501 by omega)]
      exact ⟨0, by simp, by simp⟩
  obtain ⟨E2, hI2, -⟩ := Exec.toExecI_whileLtN
    (Q := fun c => WordsBounded W c ∧ RealsIntBounded (256 * ((4 * c₀.nreg 500 + 2) * X)) c)
    (I := CI W (c₀.nreg 500) X) e2
    (fun c c₂ k hI hlt eb => by
      have hlt' : c.nreg 511 < c₀.nreg 500 := hI.r500 ▸ hlt
      obtain ⟨Eb, -⟩ := eb.toExecI_linLoopFree (Bc := 0)
        (by simp [cBody, cRead, absAdd, block, Stmt.LinLoopFree, Instr.LinR]) _ (Nat.zero_le _)
        hI.rib
      simp only [cBody, cRead, absAdd, block, Stmt.addCount, Instr.addCount] at Eb
      exact ⟨Eb, cBody_ci hI hlt' eb⟩)
    (fun c hI => ⟨hI.wb, hI.rib.mono hX2⟩) hI1
  exact ⟨.seq (E1.mono_rib (hX1.trans hX2)) E2, hI2.rib⟩

/-! ### The initial lengths and the prices of a part -/

/-- The state of the loop `pBody` of `pProg` after `i = r511` boundary vertices. -/
structure PI (W b X : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  r500 : c.nreg 500 = b
  r510 : c.nreg 510 = 1
  r511 : c.nreg 511 ≤ b
  z : c.rreg 501 = 0
  C : IB X (c.rreg 500)
  mem : ∀ a, IB ((c.nreg 511 + 1) * X) (c.rmem a)
  regs : ∀ r, r ≠ 507 → IB ((2 * c.nreg 511 + 3) * X) (c.rreg r)
  acc : IB (c.nreg 511 * ((2 * b + 2) * X)) (c.rreg 507)

theorem PI.rib {W b X : ℕ} {c : Config} (h : PI W b X c) :
    RealsIntBounded ((2 * b + 3) * ((b + 1) * X)) c := by
  have hi := h.r511
  have e1 : (2 * c.nreg 511 + 3) * X ≤ (2 * b + 3) * ((b + 1) * X) := by
    have := Nat.mul_le_mul_right X (show 2 * c.nreg 511 + 3 ≤ 2 * b + 3 by omega)
    have h2 : (2 * b + 3) * X ≤ (2 * b + 3) * ((b + 1) * X) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left X (by omega))
    omega
  refine ⟨fun r => ?_, fun a => (h.mem a).mono (by
    have := Nat.mul_le_mul_right X (show c.nreg 511 + 1 ≤ b + 1 by omega); nlinarith)⟩
  by_cases hr : r = 507
  · subst hr; refine h.acc.mono ?_
    have := Nat.mul_le_mul_right ((2 * b + 2) * X) hi; nlinarith
  · exact (h.regs r hr).mono e1

theorem pBody_pi {b X : ℕ} {c c' : Config} {k : ℕ} (hI : PI W b X c) (hlt : c.nreg 511 < b)
    (e : Exec P W pBody c c' k) : PI W b X c' := by
  unfold pBody at e
  cases e with | @seq _ _ _ c1 _ _ _ er e =>
  cases e with | @seq _ _ _ c2 _ _ _ ea ei =>
  obtain ⟨he, -⟩ := er.block_effs
  simp only [pRead, blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at he
  have hm := hI.mem
  have hle : ∀ {u v : ℕ}, u ≤ v → u * X ≤ v * X := fun h => Nat.mul_le_mul_right X h
  -- the value stored: `E i - C`
  have hv : ∀ a, IB ((c.nreg 511 + 2) * X) (c.rmem a - c.rreg 500) := fun a => by
    have := intB_sub (hm a) hI.C
    rwa [show (c.nreg 511 + 1) * X + X = (c.nreg 511 + 2) * X by ring] at this
  have hm' : ∀ A A' a, IB ((c.nreg 511 + 2) * X) (upd c.rmem A (c.rmem A' - c.rreg 500) a) :=
    fun A A' => intB_upd (fun a => (hm a).mono (hle (by omega))) A (hv A')
  have f1n : ∀ r, r ≠ 512 → r ≠ 513 → c1.nreg r = c.nreg r := fun r h1 h2 => by
    rw [← he]; simp only [upd_other _ _ _ h1, upd_other _ _ _ h2]
  have hne : ∀ r, r ≠ 502 → r ≠ 504 → r ≠ 505 → c1.rreg r = c.rreg r := fun r h1 h2 h3 => by
    rw [← he]; simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3]
  have f1m : ∀ a, IB ((c.nreg 511 + 2) * X) (c1.rmem a) := by
    rw [← he]; simp only [upd_same, upd_other _ _ _ (show (504 : ℕ) ≠ 500 by omega)]
    exact hm' _ _
  have f1r : ∀ r, r ≠ 507 → IB ((2 * c.nreg 511 + 4) * X) (c1.rreg r) := by
    rw [← he]
    refine ib_upd_ne (ib_upd_ne (ib_upd_ne (ib_upd_ne
      (fun r hr => (hI.regs r hr).mono (hle (by omega))) 504 ((hm _).mono (hle (by omega))))
      504 ?_) 505 ?_) 502 ?_
    · simp only [upd_same, upd_other _ _ _ (show (500 : ℕ) ≠ 504 by omega)]
      exact (hv _).mono (hle (by omega))
    · simp only [upd_same, upd_other _ _ _ (show (504 : ℕ) ≠ 500 by omega)]
      exact (hm' _ _ _).mono (hle (by omega))
    · simp only [upd_same, upd_other _ _ _ (show (505 : ℕ) ≠ 504 by omega),
        upd_other _ _ _ (show (504 : ℕ) ≠ 500 by omega)]
      exact intB_mono (intB_sub (hm' _ _ _) (hv _)) (by rw [← add_mul]; exact hle (by omega))
  obtain ⟨m2, n2, -, -, z2, r2, a2, q2⟩ := absAdd_ib (by omega) (by omega) (by omega) (by omega)
    (by omega) ea (by rw [hne 501 (by omega) (by omega) (by omega)]; exact hI.z) f1r
    (by rw [hne 507 (by omega) (by omega) (by omega)]; exact hI.acc)
  obtain ⟨hei, -⟩ := ei.block_effs
  simp only [blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at hei
  have fn : ∀ r, r ≠ 511 → r ≠ 512 → r ≠ 513 → c'.nreg r = c.nreg r := fun r h0 h1 h2 => by
    rw [← hei]; simp only [upd_other _ _ _ h0]; rw [n2, f1n r h1 h2]
  have f511 : c'.nreg 511 = c.nreg 511 + 1 := by
    rw [← hei]; simp only [upd_same]; rw [n2, f1n _ (by omega) (by omega),
      f1n _ (by omega) (by omega), hI.r510]
  have fr : c'.rreg = c2.rreg := by rw [← hei]
  have fm : c'.rmem = c2.rmem := by rw [← hei]
  refine ⟨ei.wb_right, (fn 500 (by omega) (by omega) (by omega)).trans hI.r500,
    (fn 510 (by omega) (by omega) (by omega)).trans hI.r510, by omega, by rw [fr]; exact z2,
    ?_, fun a => ?_, fun r hr => ?_, ?_⟩
  · rw [fr, q2 500 (by omega) (by omega), hne 500 (by omega) (by omega) (by omega)]
    exact hI.C
  · rw [fm, m2, f511]; exact f1m a
  · rw [fr, f511]; exact (r2 r hr).mono (hle (by omega))
  · rw [fr, f511]
    refine a2.mono ?_
    have := Nat.mul_le_mul_right X (show 2 * c.nreg 511 + 4 ≤ 2 * b + 2 by omega)
    nlinarith

/-- What the copy loop of `pProg` keeps. -/
def PR (X b : ℕ) (c : Config) : Prop :=
  RealsIntBounded X c ∧ c.nreg 500 = b ∧ c.nreg 510 = 1 ∧ c.rreg 501 = 0

theorem pCopy_pr {X b : ℕ} : ∀ i ∈ pCopy.instrs, ∀ c c', PR X b c → i.effect P c = some c' →
    PR X b c' := by
  have hR : ∀ i ∈ pCopy.instrs, i.NoArith 0 := by decide
  intro i hi c c' hc he
  have hb := Instr.rib_effect (hR i hi).1 (Nat.zero_le X) he hc.1
  rw [(hR i hi).2, pow_zero, one_mul] at hb
  refine ⟨hb, ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := hc
  simp only [pCopy, block, Stmt.instrs, List.mem_append, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, List.nil_append, List.append_nil] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Instr.effect, Option.some.injEq] at he <;> subst he <;>
    simp [upd_apply, h1, h2, h3]

/-- **`pProg` keeps bounded integers**: from reals bounded by `X` (`C` among them), the reals
stay bounded by `32 (2 b + 3) (b + 1) X` along the run and by `(2 b + 3) (b + 1) X` at the end
(`b = r500`; the stored `E i - C` grow by at most `X` per vertex). -/
theorem pProg_execI_of_exec {X : ℕ} {c₀ c' : Config} {k : ℕ} (hB : RealsIntBounded X c₀)
    (e : Exec P W pProg c₀ c' k) :
    ExecI P (fun c => WordsBounded W c ∧
        RealsIntBounded (32 * ((2 * c₀.nreg 500 + 3) * ((c₀.nreg 500 + 1) * X))) c) pProg c₀ c' k ∧
      RealsIntBounded ((2 * c₀.nreg 500 + 3) * ((c₀.nreg 500 + 1) * X)) c' := by
  set b := c₀.nreg 500 with hb
  have hX1 : X ≤ (2 * b + 3) * ((b + 1) * X) :=
    (Nat.le_mul_of_pos_left X (by omega : 0 < b + 1)).trans (Nat.le_mul_of_pos_left _ (by omega))
  have hX2 : (2 * b + 3) * ((b + 1) * X) ≤ 32 * ((2 * b + 3) * ((b + 1) * X)) := by omega
  unfold pProg at e ⊢
  cases e with | @seq _ _ _ c1 _ _ _ e1 e =>
  cases e with | @seq _ _ _ c2 _ _ _ e2 e =>
  cases e with | @seq _ _ _ c3 _ _ _ e3 e =>
  cases e with | @seq _ _ _ c4 _ _ _ e4 e5 =>
  obtain ⟨E1, b1⟩ := e1.toExecI_arithFree (Bc := 0) (by decide) (Nat.zero_le _) hB
  obtain ⟨he1, -⟩ := e1.block_effs
  simp only [blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at he1
  have p1 : PR X b c1 := ⟨b1, by rw [← he1]; simp [upd_apply, hb],
    by rw [← he1]; simp [upd_apply], by rw [← he1]; simp [upd_apply]⟩
  obtain ⟨E2, ⟨b2, g500, g510, g501⟩⟩ := e2.toExecI_stepInv pCopy_pr p1
  have E2' : ExecI P (fun c => WordsBounded W c ∧ RealsIntBounded X c) _ c1 c2 _ :=
    E2.mono fun _ h => ⟨h.1, h.2.1⟩
  obtain ⟨E3, -⟩ := e3.toExecI_arithFree (Bc := 0) (by decide) (Nat.zero_le _) b2
  obtain ⟨he3, -⟩ := e3.block_effs
  simp only [blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at he3
  have hI3 : PI W b X c3 := by
    refine ⟨e3.wb_right, by rw [← he3]; simp [upd_apply, g500], by rw [← he3]; simp [upd_apply, g510],
      by rw [← he3]; simp, by rw [← he3]; simp [upd_apply, g501],
      by rw [← he3]; simp only [upd_other _ _ _ (by omega : (500 : ℕ) ≠ 507)]; exact b2.1 500,
      fun a => ?_, fun r hr => ?_, ?_⟩
    · rw [← he3]; simp only [upd_same, zero_add, one_mul]; exact b2.2 a
    · rw [← he3]; simp only [upd_same, upd_other _ _ _ hr]
      exact intB_mono (b2.1 r) (by nlinarith)
    · rw [← he3]; simp only [upd_same, zero_mul]; exact ⟨0, by simp, by simp⟩
  obtain ⟨E4, hI4, -⟩ := Exec.toExecI_whileLtN
    (Q := fun c => WordsBounded W c ∧ RealsIntBounded (32 * ((2 * b + 3) * ((b + 1) * X))) c)
    (I := PI W b X) e4
    (fun c c₂ k hI hlt eb => by
      have hlt' : c.nreg 511 < b := hI.r500 ▸ hlt
      obtain ⟨Eb, -⟩ := eb.toExecI_linLoopFree (Bc := 0)
        (by simp [pBody, pRead, absAdd, block, Stmt.LinLoopFree, Instr.LinR]) _ (Nat.zero_le _)
        hI.rib
      simp only [pBody, pRead, absAdd, block, Stmt.addCount, Instr.addCount] at Eb
      exact ⟨Eb, pBody_pi hI hlt' eb⟩)
    (fun c hI => ⟨hI.wb, hI.rib.mono hX2⟩) hI3
  obtain ⟨E5, b5⟩ := e5.toExecI_arithFree (Bc := 0) (by decide) (Nat.zero_le _) hI4.rib
  exact ⟨.seq (E1.mono_rib (hX1.trans hX2)) (.seq (E2'.mono_rib (hX1.trans hX2))
    (.seq (E3.mono_rib (hX1.trans hX2)) (.seq E4 (E5.mono_rib hX2)))), b5⟩

end NegSSSP

end PlanarFlow
