module

public import PlanarFlow.BKMNW.LrA

/-!
# The children's records of the large split: the value maps

Registers of these programs (`8500 …`): inputs `8500 = LFb` (the flags of the left piece over the
parent record), `8501 = CVb` (tail on the path), `8502 = HMb` (holes meeting the path),
`8503 = PFb` (dart on the path), `8504 = CCb` (dart of the core's piece map), `8505 = hb`
(`[holeStep]`); computed `8506 = Y` (the area of `crProg`), `8507 = Xb` (the records),
`8508 = t` (`0`: left child, `1`: right child), `8509` (the base of the current child's record),
`8510` (its size), `8511` (the size of the left record), `8513 = R + 3 + 5 n` (the parent's state
array `SP`), `8514 = Y + n`, `8515 = Y + 2 n`, `8516 = Y + 3 n`, `8517 = Y + 6 n`.

* `vbLP`, **`lrLP = mapRunS vbLP 5504 5507`**: `LP[i] = (t - LF[i]) + (LF[i] - t)` at `A + n`
  (the flags of the child `t`);
* `vbBc`, **`lrBc = mapRunS vbBc 5504 8516`**: `Bc[i] = CF[i] · CC[i]` at `Y + 3 n` (the flags of
  the child's core piece map);
* `vbXSG`, **`lrSG = mapRunS vbXSG 5504 8506`**: `SG[i] = CC[i] · SP[i] + (1 - CC[i]) · i` at `Y` (the
  parent's state extended by the identity, in the record's numbering).
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

/-- `r6523 := (t - LF[i]) + (LF[i] - t)`. -/
def vbLP : Stmt := block [.addN 6524 8500 6520, .loadN 6525 6524, .subN 6526 8508 6525,
  .subN 6527 6525 8508, .addN 6523 6526 6527]

/-- The flags of the child `t` at `A + n`. -/
def lrLP : Stmt := mapRunS vbLP 5504 5507

/-- `r6523 := CF[i] · CC[i]`. -/
def vbBc : Stmt := block [.addN 6524 5510 6520, .loadN 6525 6524, .addN 6524 8504 6520,
  .loadN 6526 6524, .mulN 6523 6525 6526]

/-- The flags of the child's core piece map at `Y + 3 n`. -/
def lrBc : Stmt := mapRunS vbBc 5504 8516

/-- `r6523 := CC[i] · SP[i] + (1 - CC[i]) · i`. -/
def vbXSG : Stmt := block [.addN 6524 8504 6520, .loadN 6525 6524, .addN 6524 8513 6520,
  .loadN 6526 6524, .mulN 6527 6525 6526, .subN 6528 6521 6525, .mulN 6529 6528 6520,
  .addN 6523 6527 6529]

/-- The extended state at `Y`. -/
def lrSG : Stmt := mapRunS vbXSG 5504 8506

/-- The flip value: `t` and `x` bits. -/
lemma flipV_eq (t x : ℕ) : (t - x) + (x - t) = if t = x then 0 else (max t x - min t x) := by
  split_ifs with h <;> omega

lemma sgV_eq {cf sp i : ℕ} (h : cf ≤ 1) : cf * sp + (1 - cf) * i = if cf = 0 then i else sp := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with rfl | rfl <;> simp

section Exec

variable {I : Input} {W : ℕ}

theorem vbLP_exec (c : Config) (hc : WordsBounded W c) {i LFb t : ℕ}
    (r20 : c.nreg 6520 = i) (r00 : c.nreg 8500 = LFb) (r08 : c.nreg 8508 = t)
    (w1 : LFb + i ≤ W) :
    ∃ c' k, Exec I W vbLP c c' k ∧ k ≤ 5 ∧
      c'.nreg 6523 = (t - c.nmem (LFb + i)) + (c.nmem (LFb + i) - t) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ha := hc.2 (LFb + i)
  have ht := hc.1 8508
  unfold vbLP
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r20, r00, r08]; omega)
  refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
    simp (disch := omega) only [upd_other, upd_same, r20, r00, r08]
  · unfold vscr at hx
    config_simp; simp (disch := omega) only [upd_other, upd_same]

theorem vbBc_exec (c : Config) (hc : WordsBounded W c) {i CFb CCb : ℕ}
    (r20 : c.nreg 6520 = i) (r10 : c.nreg 5510 = CFb) (r04 : c.nreg 8504 = CCb)
    (w1 : CFb + i ≤ W) (w2 : CCb + i ≤ W) (hb : c.nmem (CFb + i) ≤ 1) :
    ∃ c' k, Exec I W vbBc c c' k ∧ k ≤ 5 ∧
      c'.nreg 6523 = c.nmem (CFb + i) * c.nmem (CCb + i) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ha := hc.2 (CFb + i)
  have hb' := hc.2 (CCb + i)
  have hm : c.nmem (CFb + i) * c.nmem (CCb + i) ≤ W := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h | h <;> rw [h] <;> omega
  unfold vbBc
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r20, r10, r04]; omega)
  refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
    simp (disch := omega) only [upd_other, upd_same, r20, r10, r04]
  · unfold vscr at hx
    config_simp; simp (disch := omega) only [upd_other, upd_same]

theorem vbXSG_exec (c : Config) (hc : WordsBounded W c) {i CCb SPb : ℕ}
    (r20 : c.nreg 6520 = i) (r21 : c.nreg 6521 = 1) (r04 : c.nreg 8504 = CCb)
    (r13 : c.nreg 8513 = SPb) (w1 : CCb + i ≤ W) (w2 : SPb + i ≤ W)
    (hb : c.nmem (CCb + i) ≤ 1) :
    ∃ c' k, Exec I W vbXSG c c' k ∧ k ≤ 8 ∧
      c'.nreg 6523 = (if c.nmem (CCb + i) = 0 then i else c.nmem (SPb + i)) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ha := hc.2 (CCb + i)
  have hb' := hc.2 (SPb + i)
  have hi := hc.1 6520
  rw [r20] at hi
  have hm1 : c.nmem (CCb + i) * c.nmem (SPb + i) ≤ W := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h | h <;> rw [h] <;> omega
  have hm2 : (1 - c.nmem (CCb + i)) * i ≤ W := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h | h <;> rw [h] <;> omega
  have hm3 : c.nmem (CCb + i) * c.nmem (SPb + i) + (1 - c.nmem (CCb + i)) * i ≤ W := by
    rw [sgV_eq hb]; split_ifs <;> omega
  unfold vbXSG
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r20, r21, r04, r13]; omega)
  refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
    simp (disch := omega) only [upd_other, upd_same, r20, r21, r04, r13]
    exact sgV_eq hb
  · unfold vscr at hx
    config_simp; simp (disch := omega) only [upd_other, upd_same]

/-- **The flags of the child `t`** at `A + n`. -/
theorem lrLP_exec (c : Config) (hc : WordsBounded W c) {n LFb t Ob : ℕ}
    (r04 : c.nreg 5504 = n) (r21 : c.nreg 6521 = 1) (r07 : c.nreg 5507 = Ob)
    (r00 : c.nreg 8500 = LFb) (r08 : c.nreg 8508 = t)
    (o1 : LFb + n ≤ Ob ∨ Ob + n ≤ LFb) (w : Ob + n ≤ W) (w' : LFb + n ≤ W) (w0 : n + 1 ≤ W) :
    ∃ c' k, Exec I W lrLP c c' k ∧ k ≤ 10 * n + 3 ∧
      (∀ i < n, c'.nmem (Ob + i) = (t - c.nmem (LFb + i)) + (c.nmem (LFb + i) - t)) ∧
      (∀ a, ¬ (Ob ≤ a ∧ a < Ob + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t', e, ht, h1, h2, h3, h4, h5, h6⟩ := mapRun_exec (P := I) c hc (vb := vbLP)
    (bnd := 5504) (ob := 5507) (m := n) (Ob := Ob) (B := 5)
    (fun i => (t - c.nmem (LFb + i)) + (c.nmem (LFb + i) - t))
    r04 r21 r07 w w0 (by unfold vscr; decide) (by unfold vscr; decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi c' hw h20 hr hm => by
      have R : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x := hr
      have e1 : c'.nmem (LFb + i) = c.nmem (LFb + i) := hm _ (by clear * - hi o1; omega)
      obtain ⟨c'', k, ex, hk, v, nn, mm, rr, rm, oo⟩ := vbLP_exec (I := I) c' hw h20
        ((R 8500 (by unfold vscr; decide) (by decide) (by decide)).trans r00)
        ((R 8508 (by unfold vscr; decide) (by decide) (by decide)).trans r08)
        (by clear * - hi w'; omega)
      refine ⟨c'', k, ex, hk, ?_, nn, mm, rr, rm, oo⟩
      rw [v, e1])
  exact ⟨c', t', e, by clear * - ht; omega, h1, h2, h3, h4, h5, h6⟩

/-- **The flags of the child's core piece map** at `Y + 3 n`. -/
theorem lrBc_exec (c : Config) (hc : WordsBounded W c) {n CFb CCb Ob : ℕ}
    (r04 : c.nreg 5504 = n) (r21 : c.nreg 6521 = 1) (r10 : c.nreg 5510 = CFb)
    (r84 : c.nreg 8504 = CCb) (r16 : c.nreg 8516 = Ob)
    (o1 : CFb + n ≤ Ob ∨ Ob + n ≤ CFb) (o2 : CCb + n ≤ Ob ∨ Ob + n ≤ CCb)
    (w : Ob + n ≤ W) (w1 : CFb + n ≤ W) (w2 : CCb + n ≤ W) (w0 : n + 1 ≤ W)
    (hb : ∀ i < n, c.nmem (CFb + i) ≤ 1) :
    ∃ c' k, Exec I W lrBc c c' k ∧ k ≤ 10 * n + 3 ∧
      (∀ i < n, c'.nmem (Ob + i) = c.nmem (CFb + i) * c.nmem (CCb + i)) ∧
      (∀ a, ¬ (Ob ≤ a ∧ a < Ob + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t', e, ht, h1, h2, h3, h4, h5, h6⟩ := mapRun_exec (P := I) c hc (vb := vbBc)
    (bnd := 5504) (ob := 8516) (m := n) (Ob := Ob) (B := 5)
    (fun i => c.nmem (CFb + i) * c.nmem (CCb + i))
    r04 r21 r16 w w0 (by unfold vscr; decide) (by unfold vscr; decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi c' hw h20 hr hm => by
      have R : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x := hr
      have e1 : c'.nmem (CFb + i) = c.nmem (CFb + i) := hm _ (by clear * - hi o1; omega)
      have e2 : c'.nmem (CCb + i) = c.nmem (CCb + i) := hm _ (by clear * - hi o2; omega)
      obtain ⟨c'', k, ex, hk, v, nn, mm, rr, rm, oo⟩ := vbBc_exec (I := I) c' hw h20
        ((R 5510 (by unfold vscr; decide) (by decide) (by decide)).trans r10)
        ((R 8504 (by unfold vscr; decide) (by decide) (by decide)).trans r84)
        (by clear * - hi w1; omega) (by clear * - hi w2; omega) (by rw [e1]; exact hb i hi)
      refine ⟨c'', k, ex, hk, ?_, nn, mm, rr, rm, oo⟩
      rw [v, e1, e2])
  exact ⟨c', t', e, by clear * - ht; omega, h1, h2, h3, h4, h5, h6⟩

/-- **The extended state** at `Y`. -/
theorem lrSG_exec (c : Config) (hc : WordsBounded W c) {n CCb SPb Ob : ℕ}
    (r04 : c.nreg 5504 = n) (r21 : c.nreg 6521 = 1) (r84 : c.nreg 8504 = CCb)
    (r13 : c.nreg 8513 = SPb) (r06 : c.nreg 8506 = Ob)
    (o1 : CCb + n ≤ Ob ∨ Ob + n ≤ CCb) (o2 : SPb + n ≤ Ob ∨ Ob + n ≤ SPb)
    (w : Ob + n ≤ W) (w1 : CCb + n ≤ W) (w2 : SPb + n ≤ W) (w0 : n + 1 ≤ W)
    (hb : ∀ i < n, c.nmem (CCb + i) ≤ 1) :
    ∃ c' k, Exec I W lrSG c c' k ∧ k ≤ 13 * n + 3 ∧
      (∀ i < n, c'.nmem (Ob + i) = if c.nmem (CCb + i) = 0 then i else c.nmem (SPb + i)) ∧
      (∀ a, ¬ (Ob ≤ a ∧ a < Ob + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t', e, ht, h1, h2, h3, h4, h5, h6⟩ := mapRun_exec (P := I) c hc (vb := vbXSG)
    (bnd := 5504) (ob := 8506) (m := n) (Ob := Ob) (B := 8)
    (fun i => if c.nmem (CCb + i) = 0 then i else c.nmem (SPb + i))
    r04 r21 r06 w w0 (by unfold vscr; decide) (by unfold vscr; decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi c' hw h20 hr hm => by
      have R : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x := hr
      have e1 : c'.nmem (CCb + i) = c.nmem (CCb + i) := hm _ (by clear * - hi o1; omega)
      have e2 : c'.nmem (SPb + i) = c.nmem (SPb + i) := hm _ (by clear * - hi o2; omega)
      obtain ⟨c'', k, ex, hk, v, nn, mm, rr, rm, oo⟩ := vbXSG_exec (I := I) c' hw h20
        ((R 6521 (by unfold vscr; decide) (by decide) (by decide)).trans r21)
        ((R 8504 (by unfold vscr; decide) (by decide) (by decide)).trans r84)
        ((R 8513 (by unfold vscr; decide) (by decide) (by decide)).trans r13)
        (by clear * - hi w1; omega) (by clear * - hi w2; omega) (by rw [e1]; exact hb i hi)
      refine ⟨c'', k, ex, hk, ?_, nn, mm, rr, rm, oo⟩
      rw [v, e1, e2])
  exact ⟨c', t', e, by clear * - ht; omega, h1, h2, h3, h4, h5, h6⟩

end Exec

end MfDrv

end BKMNW

end PlanarFlow
