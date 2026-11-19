module

public import PlanarFlow.BKMNW.PqZ

/-!
# The preprocessing at any base `B`

`ppA_exec`, `ppB_exec` (`PpPP.lean`) run the preprocessing at the base `B = 0`. Here the same
stages run at the base `B` held in `r8730` (computed by `zP`, `PqZ.lean`), so that the memory
below `B` is left untouched (the zero area of the in-place subroutine calls):

* `S0B` (`S0` without `B := 0`), **`ppAB = S0B ; pd1 ; pd2 ; sl`**, **`ppA_execB`**;
* `prAB` (the print of `POS[3x]` at `B + 42 n + 3x`, the address from `r6701 = F₀`),
  **`ppBB = so ; fin ; prAB`**, **`ppB_execB`**;
* both leave the memory below `B` unchanged.
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

/-- **The setup at a given base**: `n`, `K`, the constants; `r8730` (the base) kept. -/
def S0B : Stmt :=
  block [.constN 8778 2, .readIn 8700 8778, .constN 8778 0, .readIn 8707 8778, .constN 8704 1,
    .constN 8705 2, .constN 8706 3, .mulN 8701 8700 8706, .constN 8778 5, .mulN 8702 8700 8778,
    .constN 8778 7, .mulN 8703 8700 8778]

theorem S0B_exec {d : List ℕ} (hP : P.data = d) (c : Config) (hc : WordsBounded W c)
    (hwd : ∀ i, word d i ≤ W) (hW : 7 * nd d + 7 ≤ W) :
    ∃ c' t, Exec P W S0B c c' t ∧ t = 12 ∧ c'.nreg 8700 = nd d ∧ c'.nreg 8701 = 3 * nd d ∧
      c'.nreg 8702 = 5 * nd d ∧ c'.nreg 8703 = 7 * nd d ∧ c'.nreg 8704 = 1 ∧
      c'.nreg 8705 = 2 ∧ c'.nreg 8706 = 3 ∧ c'.nreg 8707 = nv d ∧ c'.nreg 8730 = c.nreg 8730 ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have e2 : d.getD 2 0 = nd d := rfl
  have e0 : d.getD 0 0 = nv d := rfl
  unfold S0B
  exec_block
  all_goals try omega
  all_goals try (config_simp; rw [hP, e2]; omega)
  all_goals try (config_simp; rw [hP, e0]; exact hwd 0)
  all_goals try (config_simp; rw [hP]; exact hwd 2)
  all_goals try (config_simp; simp (disch := omega) only [upd_other])

/-- The first half at the base `r8730`. -/
def ppAB : Stmt := .seq S0B (.seq pd1 (.seq pd2 sl))

set_option maxHeartbeats 1000000 in
theorem ppA_execB {d : List ℕ} (hP : P.data = d) (wf : Wf d)
    (hl : ∀ i < nd d, tl d (rv d i) ≠ tl d i) (hrot : (map wf).RotTrans)
    (hwd : ∀ i, word d i ≤ W) (c : Config) (hc : WordsBounded W c) {B : ℕ} (r30 : c.nreg 8730 = B)
    (hbig : ∑ x ∈ range (nd d), fl (tl d (rv d x) ≠ tl d x) * cp d x ≤ W)
    (hW : 10 * B + 200 * nd d + 4 * nv d + (2 * (nv d + nd d) + 1) * (7 * nd d) + 200 ≤ W) :
    ∃ c' t, Exec P W ppAB c c' t ∧ t ≤ 1600 * nd d + 300 ∧ SL wf B c'.nmem ∧
      (∀ a < B, c'.nmem a = c.nmem a) ∧
      c'.nreg 8700 = nd d ∧ c'.nreg 8703 = 7 * nd d ∧ c'.nreg 8704 = 1 ∧ c'.nreg 8705 = 2 ∧
      c'.nreg 8706 = 3 ∧ c'.nreg 8708 = bigN (map wf) (fun i => cp d i) ∧ c'.nreg 8709 = 2 * (nv d + nd d) ∧
      c'.nreg 8730 = B ∧ c'.nreg 8731 = ∑ s ∈ range (7 * nd d), fl (ValidS (map wf) s) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hcp : ∀ x < nd d, cp d x ≤ W := fun x _ => hwd _
  obtain ⟨c₀, t₀, e₀, ht₀, s00, s01, s02, s03, s04, s05, s06, s07, s30, sm, srr, srm, so⟩ :=
    S0B_exec hP c hc hwd (by nlinarith)
  obtain ⟨c₁, t₁, e₁, ht₁, h1, m1, r41, f1, rr1, rm1, o1⟩ := pd1_exec hP wf hwd c₀ e₀.wb_right
    (B := B) s00 s04 (s30.trans r30) (by nlinarith)
  have k1 : ∀ x, 8700 ≤ x → x ≤ 8730 → c₁.nreg x = c₀.nreg x := fun x a b =>
    f1 x (by unfold wscr pscr; omega) (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, h2, b2, m2, F2, rr2, rm2, o2⟩ := pd2_exec (P := P) wf c₁ e₁.wb_right
    (B := B) ⟨by rw [k1 _ (by omega) (by omega)]; exact s00, by rw [k1 _ (by omega) (by omega)]; exact s04,
      by rw [k1 _ (by omega) (by omega)]; exact s30.trans r30, r41⟩ h1 hbig hcp (by nlinarith)
  have k2 : ∀ x, 8700 ≤ x → x ≤ 8707 → c₂.nreg x = c₀.nreg x := fun x a b => by
    rw [F2 x (by unfold wscr2 wscr pscr; omega), k1 x a (by omega)]
  have mm : ∀ a, ¬ (B + 2 * nd d ≤ a ∧ a < B + 6 * nd d) → ¬ (B + 12 * nd d ≤ a ∧
      a < B + 14 * nd d) → c₂.nmem a = c₁.nmem a := m2
  have h1' : PD1 d B c₂.nmem :=
    ⟨fun x hx => by rw [mm _ (by omega) (by omega)]; exact h1.frv x hx,
      fun x hx => by rw [mm _ (by omega) (by omega)]; exact h1.fsg x hx,
      fun x hx => by rw [mm _ (by omega) (by omega)]; exact h1.fnx x hx,
      fun x hx => by rw [mm _ (by omega) (by omega)]; exact h1.fcp x hx,
      fun x hx => by rw [mm _ (by omega) (by omega)]; exact h1.fvt x hx,
      fun x hx => by rw [mm _ (by omega) (by omega)]; exact h1.fnl x hx,
      fun x hx => by rw [mm _ (by omega) (by omega)]; exact h1.fts x hx,
      fun x hx => by rw [mm _ (by omega) (by omega)]; exact h1.ftt x hx⟩
  obtain ⟨c₃, t₃, e₃, ht₃, h3, n3, m3, B3, r413, f3, rr3, rm3, o3⟩ := sl_exec (P := P) wf hl hrot
    c₂ e₂.wb_right (B := B)
    ⟨by rw [k2 _ (by omega) (by omega)]; exact s00, by rw [k2 _ (by omega) (by omega)]; exact s01,
      by rw [k2 _ (by omega) (by omega)]; exact s02, by rw [k2 _ (by omega) (by omega)]; exact s03,
      by rw [k2 _ (by omega) (by omega)]; exact s04, by rw [k2 _ (by omega) (by omega)]; exact s05,
      by rw [k2 _ (by omega) (by omega)]; exact s06, by rw [k2 _ (by omega) (by omega)]; exact s07,
      b2⟩
    (by rw [F2 _ (by unfold wscr2 wscr pscr; omega), k1 _ (by omega) (by omega)]; exact s30.trans r30)
    h1' h2 (by nlinarith)
  have k3 : ∀ x, 8700 ≤ x → x ≤ 8708 → c₃.nreg x = c₂.nreg x := fun x a b =>
    f3 x (by unfold wscr pscr; omega) (by unfold slW; omega) (by omega)
  refine ⟨c₃, t₀ + (t₁ + (t₂ + t₃)), by unfold ppAB; exact .seq e₀ (.seq e₁ (.seq e₂ e₃)),
    by omega, h3, fun a ha => by rw [m3 a (by omega), mm a (by omega) (by omega), m1 a (by omega), sm], by rw [k3 _ (by omega) (by omega), k2 _ (by omega) (by omega)]; exact s00,
    by rw [k3 _ (by omega) (by omega), k2 _ (by omega) (by omega)]; exact s03,
    by rw [k3 _ (by omega) (by omega), k2 _ (by omega) (by omega)]; exact s04,
    by rw [k3 _ (by omega) (by omega), k2 _ (by omega) (by omega)]; exact s05,
    by rw [k3 _ (by omega) (by omega), k2 _ (by omega) (by omega)]; exact s06,
    by rw [k3 _ (by omega) (by omega), b2, bigN_map wf hl], B3.b09,
    by rw [f3 _ (by unfold wscr pscr; omega) (by unfold slW; omega) (by omega),
      F2 _ (by unfold wscr2 wscr pscr; omega), k1 _ (by omega) (by omega)]; exact s30.trans r30, n3,
    by rw [rr3, rr2, rr1, srr], by rw [rm3, rm2, rm1, srm], by rw [o3, o2, o1, so]⟩

/-- The setup of the print of `POS[3x]` at the base: `8775 = r6701 - (44 n + 2 K + 1)`
(`= B + 42 n` after `fin`), stride `3`. -/
def prAB0 : Stmt := block [.constN 8778 2, .readIn 8741 8778, .constN 8778 0, .readIn 8803 8778,
  .constN 8778 44, .mulN 8804 8741 8778, .constN 8778 2, .mulN 8805 8803 8778,
  .addN 8804 8804 8805, .constN 8778 1, .addN 8804 8804 8778, .subN 8775 6701 8804,
  .constN 8776 3, .constN 8704 1]

/-- Print `POS[3 x]` for every dart `x`, at the base. -/
def prAB : Stmt := .seq prAB0 prL

/-- The second half at the base `r8730`. -/
def ppBB : Stmt := .seq so (.seq fin prAB)

set_option maxHeartbeats 2000000 in
theorem ppB_execB {d : List ℕ} (hP : P.data = d) (hwd : ∀ i, word d i ≤ W) (wf : Wf d) (hl : ∀ i < nd d, tl d (rv d i) ≠ tl d i)
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
      (fun x hx => by rw [flI_map wf hl hx]; exact OrbLab.olab_lt (nx_permOn wf) hx) hs
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
  have hrv : ∀ x < nd d, rvI (map wf) x < nd d := fun x hx => by
    rw [rvI_map wf hl hx]; exact wf.rv_lt x hx
  have hsg : ∀ x < nd d, sgI (map wf) x < nd d := fun x hx => by
    rw [sgI_map wf hl hx]; exact wf.nx_lt _ (wf.rv_lt x hx)
  have hpi : ∀ x < nd d, piI (map wf) x < nd d := fun x hx => piI_lt_map wf hl hx
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
      fun i hi => ?_, fun i j hij hj => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
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
