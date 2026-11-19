module

public import PlanarFlow.BKMNW.S7Od3

/-!
# Stage 7 of `sepL` (III), machine part (IV): `twoGroupsL` and the flags of the left piece

* `odC = (tgProg on WT, A) ; odSL ; LF` with `hv = pdEq r4006 1`, `Mx = min r4011 mC`,
  **`odC_exec`**: `twoGroupsL WT A (range mC) = if r4006 = 1 then [r4007] else range (min r4011 mC)`
  and `LF[i] = [if r4006 = 1 then P1[i] - 1 = r4007 else P1[i] - 1 < min r4011 mC]` at
  `LFb = WTb + n`;
* the meaning (pure): **`od_wt_sem`** (`WT[q] = hw K Hs C (odL q)`: the count of the positions and
  the owned holes off `C`), **`od_hsum`** (the weights of the holes add up to at most
  `K · nTouch`), **`od_left_sem`** (`LF[i] = bf (g i ∈ l)` for the first group `l` of
  `twoGroupsL (hw …) A (ordE eG N (P.image X))`, and the rest).

Registers `4000 … 4013` (`tgProg`), `7153 = A`, `7181 … 7192`.
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

/-- The registers of `tgProg`. -/
def odTg : Stmt := block [.copyN 4000 6306, .copyN 4001 7186, .copyN 4002 7153]

/-- The values of the flags of the left piece. -/
def odSL : Stmt :=
  block [.subN 7190 4006 6521, .subN 7191 6521 4006, .addN 7190 7190 7191, .divN 7191 7190 7190,
    .subN 7181 6521 7191, .copyN 7182 4007, .subN 7192 4011 6306, .subN 7183 4011 7192,
    .addN 7187 7186 7100]

/-- **The first group and the flags of the left piece.** -/
def odC : Stmt := .seq (.seq odTg tgProg) (.seq odSL (mapRunS vbLF 7100 7187))

section Exec

variable {P : Input} {W : ℕ}

theorem odTg_exec (c : Config) (hc : WordsBounded W c) {mC WTb A : ℕ}
    (r06 : c.nreg 6306 = mC) (r86 : c.nreg 7186 = WTb) (r53 : c.nreg 7153 = A) :
    ∃ c' t, Exec P W odTg c c' t ∧ t = 3 ∧ c'.nreg 4000 = mC ∧ c'.nreg 4001 = WTb ∧
      c'.nreg 4002 = A ∧ c'.nmem = c.nmem ∧
      (∀ x, (x < 4000 ∨ 4002 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold odTg
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp (disch := omega) only [upd_other, upd_same, r06, r86, r53]

theorem odSL_exec (c : Config) (hc : WordsBounded W c) {n mC WTb a b f : ℕ}
    (r00 : c.nreg 7100 = n) (r06 : c.nreg 6306 = mC) (r86 : c.nreg 7186 = WTb)
    (r21 : c.nreg 6521 = 1) (q6 : c.nreg 4006 = a) (q7 : c.nreg 4007 = b)
    (q11 : c.nreg 4011 = f) (w : WTb + n ≤ W) :
    ∃ c' t, Exec P W odSL c c' t ∧ t = 9 ∧ c'.nreg 7181 = pdEq a 1 ∧ c'.nreg 7182 = b ∧
      c'.nreg 7183 = f - (f - mC) ∧ c'.nreg 7187 = WTb + n ∧ c'.nmem = c.nmem ∧
      (∀ x, (x < 7181 ∨ 7183 < x) → x ≠ 7187 → (x < 7190 ∨ 7192 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ba : a ≤ W := q6 ▸ hc.1 _
  have b1 : 1 ≤ W := by have := hc.1 6521; rw [r21] at this; exact this
  unfold odSL
  exec_block
  all_goals try (config_simp; (try simp only [r00, r06, r86, r21, q6, q7, q11]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, fun x h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r00, r06, r86, r21, q6, q7, q11, pdEq]); done)
  all_goals try (config_simp; (try simp only [r00, r06, r86, r21, q6, q7, q11]); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other])

set_option maxHeartbeats 4000000 in
/-- **The first group and the flags of the left piece** (see the module docstring). -/
theorem odC_exec (c : Config) (hc : WordsBounded W c) {n mC WTb A P1b : ℕ} {wt p1 : ℕ → ℕ}
    (r00 : c.nreg 7100 = n) (r06 : c.nreg 6306 = mC) (r86 : c.nreg 7186 = WTb)
    (r53 : c.nreg 7153 = A) (r80 : c.nreg 7180 = P1b) (r21 : c.nreg 6521 = 1)
    (hwt : ∀ q < mC, c.nmem (WTb + q) = wt q) (hp1 : ∀ i < n, c.nmem (P1b + i) = p1 i)
    (hwA : ∀ q < mC, A + 2 * wt q ≤ W) (hmC : mC ≤ n)
    (lay : P1b + n ≤ WTb ∧ WTb + 2 * n ≤ W) :
    ∃ c' t, Exec P W odC c c' t ∧ t ≤ 50 * n + 40 ∧
      twoGroupsL wt A (List.range mC) =
        (if c'.nreg 4006 = 1 then [c'.nreg 4007] else List.range (min (c'.nreg 4011) mC)) ∧
      (∀ i < n, c'.nmem (WTb + n + i) =
        if (if c'.nreg 4006 = 1 then p1 i - 1 = c'.nreg 4007 else p1 i - 1 < min (c'.nreg 4011) mC)
          then 1 else 0) ∧
      (∀ a, ¬ (WTb + n ≤ a ∧ a < WTb + 2 * n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4000 ∨ (4013 < x ∧ x < 6520) ∨ x = 6521 ∨ (6529 < x ∧ x < 7181) ∨
        (7183 < x ∧ x < 7187) ∨ (7187 < x ∧ x < 7190) ∨ 7192 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2⟩ := lay
  have bW : 1 ≤ W := by have := hc.1 6521; rw [r21] at this; exact this
  unfold odC
  obtain ⟨c₁, t₁, e₁, ht₁, a0, a1, a2, m1, n1, rr1, rm1, o1⟩ := odTg_exec (P := P) c hc r06 r86 r53
  obtain ⟨c₂, t₂, e₂, ht₂, tg, n2, m2, rr2, rm2, o2⟩ := tgProg_exec (P := P) c₁ e₁.wb_right a0 a1 a2
    (by omega) (fun j hj => by rw [m1, hwt j hj]; exact hwA j hj) (by omega)
  have tg' : twoGroupsL wt A (List.range mC) =
      (if c₂.nreg 4006 = 1 then [c₂.nreg 4007] else List.range (min (c₂.nreg 4011) mC)) := by
    rw [← tg]
    exact twoGroupsL_congr A fun q hq => by rw [m1, hwt q (List.mem_range.1 hq)]
  have k : ∀ x, (x < 4000 ∨ 4013 < x) → c₂.nreg x = c.nreg x := fun x hx => by
    rw [n2 x (by omega), n1 x (by omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, b1, b2, b3, b4, m3, n3, rr3, rm3, o3⟩ := odSL_exec (P := P) c₂
    e₂.wb_right (n := n) (mC := mC) (WTb := WTb) ((k 7100 (by omega)).trans r00)
    ((k 6306 (by omega)).trans r06) ((k 7186 (by omega)).trans r86)
    ((k 6521 (by omega)).trans r21) rfl rfl rfl (by omega)
  have hv1 : pdEq (c₂.nreg 4006) 1 ≤ 1 := by rw [pdEq_eq]; split_ifs <;> omega
  obtain ⟨c₄, t₄, e₄, ht₄, f4, fm4, fn4, fr4, frm4, fo4⟩ := mapRun_exec (P := P) c₃ e₃.wb_right
    (vb := vbLF) (bnd := 7100) (ob := 7187) (m := n) (Ob := WTb + n) (B := 14)
    (fun i => lfV (pdEq (c₂.nreg 4006) 1) (c₂.nreg 4007) (c₂.nreg 4011 - (c₂.nreg 4011 - mC))
      (p1 i))
    (by rw [n3 _ (by omega) (by omega) (by omega), k _ (by omega), r00])
    (by rw [n3 _ (by omega) (by omega) (by omega), k _ (by omega), r21]) b4
    (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega)
    (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      have g : ∀ x, (x < 6520 ∨ x = 6521 ∨ 6529 < x) → c'.nreg x = c₃.nreg x := fun x hx =>
        hr x (by unfold vscr; omega) (by omega) (by omega)
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbLF_exec (P := P) c' hw
        (P1b := P1b) (hv := pdEq (c₂.nreg 4006) 1) (r7 := c₂.nreg 4007)
        (mx := c₂.nreg 4011 - (c₂.nreg 4011 - mC)) (p := p1 i) h20
        (by rw [g _ (by omega), n3 _ (by omega) (by omega) (by omega), k _ (by omega), r80])
        (by rw [g _ (by omega)]; exact b1) (by rw [g _ (by omega)]; exact b2)
        (by rw [g _ (by omega)]; exact b3)
        (by rw [g _ (by omega), n3 _ (by omega) (by omega) (by omega), k _ (by omega), r21])
        (by rw [hm _ (by omega), m3, m2, m1]; exact hp1 i hi) hv1 (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  have q2 : ∀ x, (4003 ≤ x ∧ x ≤ 4013) → c₄.nreg x = c₂.nreg x := fun x hx => by
    rw [fn4 x (by unfold vscr; omega) (by omega) (by omega),
      n3 x (by omega) (by omega) (by omega)]
  have hmin : c₂.nreg 4011 - (c₂.nreg 4011 - mC) = min (c₂.nreg 4011) mC := by omega
  refine ⟨c₄, _, .seq (.seq e₁ e₂) (.seq e₃ e₄), by omega, ?_, fun i hi => ?_, fun a ha => ?_,
    fun x hx => ?_, by rw [fr4, rr3, rr2, rr1], by rw [frm4, rm3, rm2, rm1],
    by rw [fo4, o3, o2, o1]⟩
  · rw [q2 4006 (by omega), q2 4007 (by omega), q2 4011 (by omega)]; exact tg'
  · rw [f4 i hi, lfV_eq hv1, q2 4006 (by omega), q2 4007 (by omega), q2 4011 (by omega), hmin,
      pdEq_eq]
    by_cases h : c₂.nreg 4006 = 1 <;> simp [h]
  · rw [fm4 a (by omega), m3, m2, m1]
  · rw [fn4 x (by unfold vscr; omega) (by omega) (by omega),
      n3 x (by omega) (by omega) (by omega), k x (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
