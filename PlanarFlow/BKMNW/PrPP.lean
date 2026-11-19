module

public import PlanarFlow.BKMNW.PrPd2
public import PlanarFlow.BKMNW.PqPP

/-!
# The preprocessing of a map with loops

* **`ppALB = S0B ; pd1 ; pdL ; r8820 := B + 10 n ; pd2G ; sl`**, **`ppAL_execB`**: the
  conclusions of `ppA_execB` (`PqPP.lean`) for any encoded map (loops allowed): the slot arrays
  `SL wf B`, `N = ∑ fl (ValidS s)`, the total capacity of the non-loop darts `bigN` in `r8708`;
* **`ppBL_execB`**: `ppB_execB` (the same program `ppBB`) without the hypothesis of no loops, and
  with the position of an invalid slot (e.g. the slot `3 x` of a loop `x`) in `[N, 7 n)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv Feas

variable {P : Input} {W : ℕ}

/-- The first half at the base `r8730`, loops allowed. -/
def ppALB : Stmt := .seq S0B (.seq pd1 (.seq pdL (.seq (setB 8820 10) (.seq pd2G sl))))

set_option maxHeartbeats 2000000 in
theorem ppAL_execB {d : List ℕ} (hP : P.data = d) (wf : Wf d) (hrot : (map wf).RotTrans)
    (hwd : ∀ i, word d i ≤ W) (c : Config) (hc : WordsBounded W c) {B : ℕ} (r30 : c.nreg 8730 = B)
    (hbig : ∑ x ∈ range (nd d), fl (tl d (rv d x) ≠ tl d x) * cp d x ≤ W)
    (hW : 10 * B + 200 * nd d + 4 * nv d + (2 * (nv d + nd d) + 1) * (7 * nd d) + 200 ≤ W) :
    ∃ c' t, Exec P W ppALB c c' t ∧ t ≤ 1600 * nd d + 400 ∧ SL wf B c'.nmem ∧
      (∀ a < B, c'.nmem a = c.nmem a) ∧
      c'.nreg 8700 = nd d ∧ c'.nreg 8703 = 7 * nd d ∧ c'.nreg 8704 = 1 ∧ c'.nreg 8705 = 2 ∧
      c'.nreg 8706 = 3 ∧ c'.nreg 8708 = bigN (map wf) (fun i => cp d i) ∧
      c'.nreg 8709 = 2 * (nv d + nd d) ∧
      c'.nreg 8730 = B ∧ c'.nreg 8731 = ∑ s ∈ range (7 * nd d), fl (ValidS (map wf) s) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set n := nd d with hn
  have hcp : ∀ x < nd d, cp d x ≤ W := fun x _ => hwd _
  obtain ⟨c₀, t₀, e₀, ht₀, s00, s01, s02, s03, s04, s05, s06, s07, s30, sm, srr, srm, so⟩ :=
    S0B_exec hP c hc hwd (by nlinarith)
  obtain ⟨c₁, t₁, e₁, ht₁, h1, m1, r41, f1, rr1, rm1, o1⟩ := pd1_exec hP wf hwd c₀ e₀.wb_right
    (B := B) s00 s04 (s30.trans r30) (by nlinarith)
  have k1 : ∀ x, 8700 ≤ x → x ≤ 8730 → c₁.nreg x = c₀.nreg x := fun x a b =>
    f1 x (by unfold wscr pscr; omega) (by omega)
  have S1 : SR n B n c₁ := ⟨by rw [k1 _ (by omega) (by omega)]; exact s00,
    by rw [k1 _ (by omega) (by omega)]; exact s04,
    by rw [k1 _ (by omega) (by omega)]; exact s30.trans r30, r41⟩
  -- the rotation and the faces without loops
  obtain ⟨c₂, t₂, e₂, ht₂, g1, g2, m2, f2, rr2, rm2, o2⟩ := pdL_exec (P := P) wf c₁ e₁.wb_right
    S1 h1 (by nlinarith)
  have k2 : ∀ x, 8700 ≤ x → x ≤ 8710 → c₂.nreg x = c₁.nreg x := fun x a b =>
    f2 x (by unfold wscrL wscr wR pscr; omega)
  have S2 : SR n B n c₂ := ⟨by rw [f2 _ (by unfold wscrL wscr wR pscr; omega)]; exact S1.1,
    by rw [f2 _ (by unfold wscrL wscr wR pscr; omega)]; exact S1.2.1,
    by rw [f2 _ (by unfold wscrL wscr wR pscr; omega)]; exact S1.2.2.1,
    by rw [f2 _ (by unfold wscrL wscr wR pscr; omega)]; exact S1.2.2.2⟩
  obtain ⟨c₃, t₃, e₃, ht₃, v3, f3, m3, rr3, rm3, o3⟩ := setB_exec (P := P) (r := 8820) (k := 10)
    (n := n) (B := B) c₂ e₂.wb_right (by omega) S2.1 S2.2.2.1 (by nlinarith)
  have S3 : SR n B n c₃ := ⟨by rw [f3 _ (by omega) (by omega)]; exact S2.1,
    by rw [f3 _ (by omega) (by omega)]; exact S2.2.1,
    by rw [f3 _ (by omega) (by omega)]; exact S2.2.2.1,
    by rw [f3 _ (by omega) (by omega)]; exact S2.2.2.2⟩
  -- memory after `pdL` and `setB`: the read arrays
  have M3 : ∀ a, ¬ (B + 1 * n ≤ a ∧ a < B + 2 * n) → ¬ (B + 11 * n ≤ a ∧ a < B + 13 * n) →
      c₃.nmem a = c₁.nmem a := fun a h h' => by rw [m3, m2 a h h']
  have hG1 : PD1G d B c₃.nmem (sgI (map wf)) (phI (map wf)) :=
    ⟨fun x hx => by rw [m3]; exact g1 x hx, fun x hx => by rw [m3]; exact g2 x hx,
      fun x hx => by rw [M3 _ (by omega) (by omega)]; exact h1.fcp x hx,
      fun x hx => by rw [M3 _ (by omega) (by omega)]; exact h1.fnl x hx⟩
  obtain ⟨c₄, t₄, e₄, ht₄, h2, b2, m4, F4, rr4, rm4, o4⟩ := pd2G_exec (P := P)
    (sgI_permOn (map wf)) (phI_permOn (map wf)) c₃ e₃.wb_right S3 hG1 v3 hbig hcp
    (by nlinarith)
  have k4 : ∀ x, 8700 ≤ x → x ≤ 8707 → c₄.nreg x = c₀.nreg x := fun x a b => by
    rw [F4 x (by unfold wscr2 wscr pscr; omega), f3 x (by omega) (by omega),
      k2 x a (by omega), k1 x a (by omega)]
  have M4 : ∀ a, ¬ (B + 2 * n ≤ a ∧ a < B + 6 * n) → ¬ (B + 12 * n ≤ a ∧ a < B + 14 * n) →
      c₄.nmem a = c₃.nmem a := m4
  -- the index-level arrays
  have hA : LowA wf B c₄.nmem :=
    { frv := fun x hx => by
        rw [M4 _ (by omega) (by omega), M3 _ (by omega) (by omega), rvI_eq wf hx]
        exact h1.frv x hx
      fsg := fun x hx => by rw [M4 _ (by omega) (by omega)]; exact hG1.fsg x hx
      fpi := fun x hx => by
        have hp := piI_lt_gen (map wf) hx
        have e := h2.fpi _ hp
        rwa [phI_piI _ hx] at e
      fcv := fun x hx => by rw [h2.fcv x hx]; exact cv_eq wf hrot hx
      fcf := fun x hx => by rw [h2.fcf x hx]; exact cf_eq wf hx
      ffl := fun x hx => by rw [h2.ffl x hx]; rfl
      fcp := fun x hx => by
        rw [M4 _ (by omega) (by omega), M3 _ (by omega) (by omega)]; exact h1.fcp x hx
      fts := fun x hx => by
        rw [M4 _ (by omega) (by omega), M3 _ (by omega) (by omega), h1.fts x hx]
        exact fl_congr (tlIn_src wf hx).symm
      ftt := fun x hx => by
        rw [M4 _ (by omega) (by omega), M3 _ (by omega) (by omega), h1.ftt x hx]
        exact fl_congr (tlIn_snk wf hx).symm
      fvt := fun x hx => by
        rw [M4 _ (by omega) (by omega), M3 _ (by omega) (by omega)]; exact h1.fvt x hx
      fnl := fun x hx => by
        rw [M4 _ (by omega) (by omega), M3 _ (by omega) (by omega), h1.fnl x hx]
        exact nl_eq wf hx }
  have hbN := bigN_eq_sumL wf
  obtain ⟨c₅, t₅, e₅, ht₅, h5, n5, m5, B5, r415, f5, rr5, rm5, o5⟩ := slG_exec (P := P) wf
    c₄ e₄.wb_right (B := B)
    ⟨by rw [k4 _ (by omega) (by omega)]; exact s00, by rw [k4 _ (by omega) (by omega)]; exact s01,
      by rw [k4 _ (by omega) (by omega)]; exact s02, by rw [k4 _ (by omega) (by omega)]; exact s03,
      by rw [k4 _ (by omega) (by omega)]; exact s04, by rw [k4 _ (by omega) (by omega)]; exact s05,
      by rw [k4 _ (by omega) (by omega)]; exact s06, by rw [k4 _ (by omega) (by omega)]; exact s07,
      by rw [b2, hbN]⟩
    (by rw [F4 _ (by unfold wscr2 wscr pscr; omega)]; exact S3.2.2.1) hA (by nlinarith)
  have k5 : ∀ x, 8700 ≤ x → x ≤ 8708 → c₅.nreg x = c₄.nreg x := fun x a b =>
    f5 x (by unfold wscr pscr; omega) (by unfold slW; omega) (by omega)
  refine ⟨c₅, t₀ + (t₁ + (t₂ + (t₃ + (t₄ + t₅)))),
    by unfold ppALB; exact .seq e₀ (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))),
    by omega, h5, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_, B5.b09, ?_, n5, ?_, ?_, ?_⟩
  · rw [m5 a (by omega), M4 a (by omega) (by omega), M3 a (by omega) (by omega),
      m1 a (by omega), sm]
  · rw [k5 _ (by omega) (by omega), k4 _ (by omega) (by omega)]; exact s00
  · rw [k5 _ (by omega) (by omega), k4 _ (by omega) (by omega)]; exact s03
  · rw [k5 _ (by omega) (by omega), k4 _ (by omega) (by omega)]; exact s04
  · rw [k5 _ (by omega) (by omega), k4 _ (by omega) (by omega)]; exact s05
  · rw [k5 _ (by omega) (by omega), k4 _ (by omega) (by omega)]; exact s06
  · rw [k5 _ (by omega) (by omega), b2, hbN]
  · rw [f5 _ (by unfold wscr pscr; omega) (by unfold slW; omega) (by omega),
      F4 _ (by unfold wscr2 wscr pscr; omega)]; exact S3.2.2.1
  · rw [rr5, rr4, rr3, rr2, rr1, srr]
  · rw [rm5, rm4, rm3, rm2, rm1, srm]
  · rw [o5, o4, o3, o2, o1, so]

set_option maxHeartbeats 2000000 in
theorem ppBL_execB {d : List ℕ} (hP : P.data = d) (hwd : ∀ i, word d i ≤ W) (wf : Wf d)
    (hrot : (map wf).RotTrans) (hn : 0 < nd d) (c : Config) (hc : WordsBounded W c) {B : ℕ}
    (hS : SL wf B c.nmem) (r00 : c.nreg 8700 = nd d) (r03 : c.nreg 8703 = 7 * nd d)
    (r04 : c.nreg 8704 = 1) (r05 : c.nreg 8705 = 2) (r06 : c.nreg 8706 = 3)
    (r08 : c.nreg 8708 = bigN (map wf) (fun i => cp d i))
    (r09 : c.nreg 8709 = 2 * (nv d + nd d)) (r30 : c.nreg 8730 = B)
    (r31 : c.nreg 8731 = ∑ s ∈ range (7 * nd d), fl (ValidS (map wf) s))
    (hW : B + 300 * nd d + 4 * nv d + (2 * (nv d + nd d) + 1) * (7 * nd d) + 300 ≤ W) :
    ∃ c' t, Exec P W ppBB c c' t ∧ t ≤ 800 * nd d + 50 * nv d + 300 ∧
      let n := nd d
      let KM := 2 * (nv d + nd d)
      let N := ∑ s ∈ range (7 * nd d), fl (ValidS (map wf) s)
      let F₀ := B + 84 * n + KM + 1
      ∃ pos : ℕ → ℕ, Sorted (map wf) (fun v => v.val) (nv d) N (srtD wf) pos ∧
      (∀ s < 7 * n, ¬ ValidS (map wf) s → N ≤ pos s ∧ pos s < 7 * n) ∧
      (∀ i < N, c'.nmem (F₀ + i) = pos (revS (map wf) (srtD wf i))) ∧
      (∀ i < N, c'.nmem (F₀ + 7 * n + i) = pos (rotS (map wf) (srtD wf i))) ∧
      (∀ i < N, c'.nmem (F₀ + 14 * n + i) =
        capS (map wf) (fun i => cp d i) (srcF d) (snkF d) (srtD wf i)) ∧
      (∀ i < N, c'.nmem (F₀ + 21 * n + i) = krS (map wf) (srcF d) (snkF d) (srtD wf i)) ∧
      (∀ i < N, c'.nmem (F₀ + 28 * n + i) = keyS (map wf) (fun v => v.val) (nv d) (srtD wf i)) ∧
      (∀ i < N, c'.nmem (F₀ + 35 * n + i) = pos (rtS (map wf) (srtD wf i))) ∧
      c'.nreg 6700 = N ∧ c'.nreg 6701 = F₀ ∧ c'.nreg 6702 = F₀ + 7 * n ∧
      c'.nreg 6703 = F₀ + 14 * n ∧ c'.nreg 6704 = F₀ + 21 * n ∧ c'.nreg 6705 = 1 ∧
      c'.nreg 6706 = bigN (map wf) (fun i => cp d i) ∧ c'.nreg 6707 = F₀ + 42 * n + 2 ∧
      c'.nmem (F₀ + 42 * n + 2 - 1) = F₀ + 28 * n ∧
      c'.nmem (F₀ + 42 * n + 2 - 1 - 1) = F₀ + 35 * n ∧
      c'.output = c.output ++ (List.range n).map (fun x => pos (3 * x)) ∧
      (∀ a < B, c'.nmem a = c.nmem a) ∧ N ≤ 7 * n := by
  have hG : 0 < 7 * nd d := by omega
  have hkey : ∀ s < 7 * nd d, keyS (map wf) (fun v => v.val) (nv d) s < 2 * (nv d + nd d) :=
    fun s hs => keyS_lt (map wf) _ (nv d) (fun x hx => by rw [xt_tl wf hx]; exact wf.tl_lt x hx)
      (fun x hx => flI_lt_gen _ hx) hs
  have hkap : ∀ s < 7 * nd d, kapD wf s ≤ 2 * (nv d + nd d) := fun s hs => by
    unfold kapD kapS; split_ifs
    · exact (hkey s hs).le
    · exact le_rfl
  have hV : ∀ s < 7 * nd d, ValidS (map wf) s ↔ kapD wf s < 2 * (nv d + nd d) := fun s hs => by
    unfold kapD kapS; split_ifs with h
    · exact ⟨fun _ => hkey s hs, fun _ => h⟩
    · exact ⟨fun h' => absurd h' h, fun h' => absurd h' (lt_irrefl _)⟩
  have hNV : ∑ s ∈ range (7 * nd d), fl (ValidS (map wf) s) =
      nV (7 * nd d) (2 * (nv d + nd d)) (kapD wf) :=
    (nV_eq hG hkap (ValidS (map wf)) hV).symm
  have hNle : ∑ s ∈ range (7 * nd d), fl (ValidS (map wf) s) ≤ 7 * nd d := by
    rw [hNV]; exact nV_le hG hkap
  have hmul : (2 * (nv d + nd d) + 1) * (7 * nd d) ≥ 7 * nd d := Nat.le_mul_of_pos_left _ (by omega)
  -- the sort
  obtain ⟨c₁, t₁, e₁, ht₁, a1, a2, m1, f1, rr1, rm1, o1⟩ := so_exec (P := P) c hc (n := nd d)
    (B := B) (KM := 2 * (nv d + nd d)) (kap := kapD wf) hn hkap r00 r03 r04 r09 r30
    (fun s hs => hS.it s hs) (by omega)
  have q : ∀ x, 8700 ≤ x → x ≤ 8731 → x ≠ 8728 → c₁.nreg x = c.nreg x := fun x a b h =>
    f1 x (by unfold wso wscr pscr; omega)
  -- the slot arrays after the sort
  have M1 : ∀ a, (a < B + 28 * nd d ∨ B + 49 * nd d ≤ a) → a < B + 84 * nd d →
      c₁.nmem a = c.nmem a := fun a h1 h2 => m1 a (by omega) (by omega)
  have hrv : ∀ x < nd d, rvI (map wf) x < nd d := fun x hx => rvI_lt_gen _ hx
  have hsg : ∀ x < nd d, sgI (map wf) x < nd d := fun x hx => sgI_lt_gen _ hx
  have hpi : ∀ x < nd d, piI (map wf) x < nd d := fun x hx => piI_lt_gen _ hx
  obtain ⟨c₂, t₂, e₂, ht₂, b1, b2, b3, b4, b5, b6, w00, w01, w02, w03, w04, w05, w06, w07, wm1,
    wm2, m2, rr2, rm2, o2⟩ := fin_exec (P := P) c₁ e₁.wb_right (n := nd d) (B := B)
    (KM := 2 * (nv d + nd d)) (N := ∑ s ∈ range (7 * nd d), fl (ValidS (map wf) s))
    (Z := bigN (map wf) (fun i => cp d i)) (srt := srtD wf)
    (revS (map wf)) (rotS (map wf)) (rtS (map wf))
    (capS (map wf) (fun i => cp d i) (srcF d) (snkF d)) (krS (map wf) (srcF d) (snkF d))
    (keyS (map wf) (fun v => v.val) (nv d))
    (by rw [q _ (by omega) (by omega) (by omega)]; exact r00) (by rw [q _ (by omega) (by omega) (by omega)]; exact r04)
    (by rw [q _ (by omega) (by omega) (by omega)]; exact r05) (by rw [q _ (by omega) (by omega) (by omega)]; exact r08)
    (by rw [q _ (by omega) (by omega) (by omega)]; exact r09) (by rw [q _ (by omega) (by omega) (by omega)]; exact r30)
    (by rw [q _ (by omega) (by omega) (by omega)]; exact r31) hNle
    (fun i hi => a1 i (by omega)) (fun i hi => srtF_lt hG hkap i)
    (fun s hs => ⟨by rw [M1 _ (by omega) (by omega)]; exact hS.rvs s hs,
      (slot_bounds _ hrv hsg hpi hs).1⟩)
    (fun s hs => ⟨by rw [M1 _ (by omega) (by omega)]; exact hS.ros s hs,
      (slot_bounds _ hrv hsg hpi hs).2.1⟩)
    (fun s hs => ⟨by rw [M1 _ (by omega) (by omega)]; exact hS.rts s hs,
      (slot_bounds _ hrv hsg hpi hs).2.2⟩)
    (fun s hs => by rw [M1 _ (by omega) (by omega)]; exact hS.cps s hs)
    (fun s hs => by rw [M1 _ (by omega) (by omega)]; exact hS.krs s hs)
    (fun s hs => by rw [M1 _ (by omega) (by omega)]; exact hS.ky s hs) (by omega)
  -- the print
  have e2 : d.getD 2 0 = nd d := rfl
  have e0 : d.getD 0 0 = nv d := rfl
  have w01' : c₂.nreg 6701 = B + 84 * nd d + 2 * (nv d + nd d) + 1 := w01
  obtain ⟨c₃, t₃, e₃, ht₃, v41, v75, v76, v04, f3, m3, rr3, rm3, o3⟩ : ∃ c₃ t₃,
      Exec P W prAB0 c₂ c₃ t₃ ∧ t₃ = 14 ∧ c₃.nreg 8741 = nd d ∧
      c₃.nreg 8775 = B + 42 * nd d ∧ c₃.nreg 8776 = 3 ∧ c₃.nreg 8704 = 1 ∧
      (∀ x, x < 8700 → c₃.nreg x = c₂.nreg x) ∧
      c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have hw₂ := e₂.wb_right
    unfold prAB0
    exec_block
    all_goals try omega
    all_goals try (config_simp; rw [hP]; first | exact hwd 2 | exact hwd 0)
    all_goals try (config_simp; rw [hP, e2]; omega)
    all_goals try (config_simp; rw [hP, e0]; omega)
    all_goals try (config_simp; rw [hP, e2, e0]; omega)
    all_goals try (config_simp; rw [hP, e2, e0, w01']; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (rw [hP]; rfl)
    all_goals try (simp only [hP, e2, e0, w01']; omega)
    all_goals try simp (disch := omega) only [upd_other]
  obtain ⟨c₄, t₄, e₄, ht₄, o4, m4, f4, rr4, rm4⟩ := prL_exec (P := P) c₃ e₃.wb_right v41 v04 v75
    v76 (by omega)
  have hpr : (List.range (nd d)).map (fun i => c₃.nmem (B + 42 * nd d + 3 * i)) =
      (List.range (nd d)).map (fun x => c₁.nmem (B + 42 * nd d + 3 * x)) := by
    refine List.map_congr_left fun x hx => ?_
    rw [List.mem_range] at hx
    rw [m3, m2 _ (by omega)]
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), by unfold ppBB prAB; exact .seq e₁ (.seq e₂ (.seq e₃ e₄)),
    by omega, fun s => c₁.nmem (B + 42 * nd d + s), ⟨fun i hi => ?_, fun s hs => ?_,
      fun i hi => ?_, fun i j hij hj => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, hNle⟩
  · rw [hNV] at hi; exact srtF_valid hG hkap _ hV hi
  · have h7 : s < 7 * nd d := by
      rcases hs with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
    obtain ⟨p, hp, e⟩ := srtF_all hG hkap _ hV h7 hs
    exact ⟨p, by rw [hNV]; exact hp, e⟩
  · exact a2 i (by omega)
  · have v1 : ValidS (map wf) (srtD wf i) :=
      srtF_valid hG hkap _ hV (show i < _ by rw [← hNV]; omega)
    have v2 : ValidS (map wf) (srtD wf j) :=
      srtF_valid hG hkap _ hV (show j < _ by rw [← hNV]; exact hj)
    have h3 : kapD wf (srtD wf i) ≤ kapD wf (srtD wf j) :=
      srtF_sorted hG hkap _ hV hij (show j < 7 * nd d by omega)
    have k1 : kapD wf (srtD wf i) = keyS (map wf) (fun v => v.val) (nv d) (srtD wf i) := by
      unfold kapD kapS; rw [ppIteT v1]
    have k2 : kapD wf (srtD wf j) = keyS (map wf) (fun v => v.val) (nv d) (srtD wf j) := by
      unfold kapD kapS; rw [ppIteT v2]
    rw [k1, k2] at h3; exact h3
  · intro s hs hv
    have himg : (range (7 * nd d)).image (srtF (7 * nd d) (2 * (nv d + nd d)) (kapD wf)) =
        range (7 * nd d) := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        simp only [Finset.mem_image, mem_range] at hy ⊢
        obtain ⟨i, hi, rfl⟩ := hy
        exact srtF_lt hG hkap i
      · rw [Finset.card_image_of_injOn (fun p hp q hq e => srtF_inj hG hkap
          (by simpa using hp) (by simpa using hq) e)]
    have hm : s ∈ (range (7 * nd d)).image (srtF (7 * nd d) (2 * (nv d + nd d)) (kapD wf)) := by
      rw [himg]; exact mem_range.2 hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hm
    rw [mem_range] at hi
    have e := a2 i hi
    simp only [e]
    refine ⟨?_, hi⟩
    by_contra hlt
    exact hv (srtF_valid hG hkap _ hV (show i < _ by rw [← hNV]; omega))
  · intro i hi; have := b1 i hi; rw [m4, m3]; exact this
  · intro i hi; have := b2 i hi; rw [m4, m3]; exact this
  · intro i hi; have := b3 i hi; rw [m4, m3]; exact this
  · intro i hi; have := b4 i hi; rw [m4, m3]; exact this
  · intro i hi; have := b5 i hi; rw [m4, m3]; exact this
  · intro i hi; have := b6 i hi; rw [m4, m3]; exact this
  · rw [f4 _ (by omega) (by omega) (by omega), f3 _ (by omega)]; exact w00
  · rw [f4 _ (by omega) (by omega) (by omega), f3 _ (by omega)]; exact w01
  · rw [f4 _ (by omega) (by omega) (by omega), f3 _ (by omega)]; exact w02
  · rw [f4 _ (by omega) (by omega) (by omega), f3 _ (by omega)]; exact w03
  · rw [f4 _ (by omega) (by omega) (by omega), f3 _ (by omega)]; exact w04
  · rw [f4 _ (by omega) (by omega) (by omega), f3 _ (by omega)]; exact w05
  · rw [f4 _ (by omega) (by omega) (by omega), f3 _ (by omega)]; exact w06
  · rw [f4 _ (by omega) (by omega) (by omega), f3 _ (by omega)]; exact w07
  · rw [m4, m3]; exact wm1
  · rw [m4, m3]; exact wm2
  · rw [o4, o3, o2, o1, hpr]
  · intro a ha; rw [m4, m3, m2 a (by omega), m1 a (by omega) (by omega)]

end Pp

end BKMNW

end PlanarFlow
