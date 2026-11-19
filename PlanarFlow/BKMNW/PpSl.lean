module

public import PlanarFlow.BKMNW.PpConv

/-!
# The slot stage of the preprocessing

From the per-dart arrays (`PD1`, `PD2`), `sl` computes, for every slot `s < 7 n`, at `B + k n`:
the keys `KY = keyS` (`k = 14`), the sort items `IT = itS` (`21`), the slot functions
`RVS = revS` (`49`), `ROS = rotS` (`56`), `RTS = rtS` (`63`), `CPS = capS` (`70`), `KRS = krS`
(`77`), and the number `N` of valid slots in `r8731`. **`sl_exec`**.
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

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv Feas OrbLab

variable {P : Input} {W : ℕ}

lemma PD1.congr {d : List ℕ} {B : ℕ} {mem mem' : ℕ → ℕ} (h : PD1 d B mem)
    (hm : ∀ a, a < B + 12 * nd d → mem' a = mem a) : PD1 d B mem' where
  frv x hx := by rw [hm _ (by omega)]; exact h.frv x hx
  fsg x hx := by rw [hm _ (by omega)]; exact h.fsg x hx
  fnx x hx := by rw [hm _ (by omega)]; exact h.fnx x hx
  fcp x hx := by rw [hm _ (by omega)]; exact h.fcp x hx
  fvt x hx := by rw [hm _ (by omega)]; exact h.fvt x hx
  fnl x hx := by rw [hm _ (by omega)]; exact h.fnl x hx
  fts x hx := by rw [hm _ (by omega)]; exact h.fts x hx
  ftt x hx := by rw [hm _ (by omega)]; exact h.ftt x hx

lemma PD2.congr {d : List ℕ} (wf : Wf d) {B : ℕ} {mem mem' : ℕ → ℕ} (h : PD2 d B mem)
    (hm : ∀ a, a < B + 12 * nd d → mem' a = mem a) : PD2 d B mem' where
  fpi y hy := by have := wf.nx_lt y hy; rw [hm _ (by omega)]; exact h.fpi y hy
  fcv x hx := by rw [hm _ (by omega)]; exact h.fcv x hx
  fcf x hx := by rw [hm _ (by omega)]; exact h.fcf x hx
  ffl x hx := by rw [hm _ (by omega)]; exact h.ffl x hx

/-- The keys are below `2 (K + n)`. -/
lemma keyS_lt {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (M : CombMap (Fin n) V F) (vn : V → ℕ) (K : ℕ) (hvn : ∀ x < n, xt (fun e => vn (M.tail e)) x < K)
    (hfl : ∀ x < n, flI M x < n) {s : ℕ} (hs : s < 7 * n) : keyS M vn K s < 2 * (K + n) := by
  unfold keyS
  split_ifs with h1 h2 h3
  · have := hfl (s / 3) (by omega); omega
  · have := hvn (s / 3) (by omega); omega
  · have := hvn ((s - 3 * n) / 2) (by omega); have := Nat.mod_lt (s - 3 * n) (by norm_num : 0 < 2)
    omega
  · have := Nat.mod_lt (s - 5 * n) (by norm_num : 0 < 2); omega

/-- The base registers of the slot stage. -/
def slRegs : Stmt :=
  block [.constN 8778 0, .mulN 8778 8700 8778, .addN 8710 8778 8730, .constN 8778 1,
    .mulN 8778 8700 8778, .addN 8711 8778 8730, .constN 8778 2, .mulN 8778 8700 8778,
    .addN 8712 8778 8730, .constN 8778 3, .mulN 8778 8700 8778, .addN 8713 8778 8730,
    .constN 8778 4, .mulN 8778 8700 8778, .addN 8714 8778 8730, .constN 8778 5,
    .mulN 8778 8700 8778, .addN 8715 8778 8730, .constN 8778 6, .mulN 8778 8700 8778,
    .addN 8716 8778 8730, .constN 8778 7, .mulN 8778 8700 8778, .addN 8717 8778 8730,
    .constN 8778 8, .mulN 8778 8700 8778, .addN 8718 8778 8730, .constN 8778 9,
    .mulN 8778 8700 8778, .addN 8719 8778 8730, .constN 8778 10, .mulN 8778 8700 8778,
    .addN 8720 8778 8730, .constN 8778 14, .mulN 8778 8700 8778, .addN 8721 8778 8730,
    .copyN 8741 8703, .addN 8709 8707 8700, .addN 8709 8709 8709]

/-- The base registers after `slRegs`. -/
structure BRegs (B n K : ℕ) (c : Config) : Prop where
  b10 : c.nreg 8710 = B + 0 * n
  b11 : c.nreg 8711 = B + 1 * n
  b12 : c.nreg 8712 = B + 2 * n
  b13 : c.nreg 8713 = B + 3 * n
  b14 : c.nreg 8714 = B + 4 * n
  b15 : c.nreg 8715 = B + 5 * n
  b16 : c.nreg 8716 = B + 6 * n
  b17 : c.nreg 8717 = B + 7 * n
  b18 : c.nreg 8718 = B + 8 * n
  b19 : c.nreg 8719 = B + 9 * n
  b20 : c.nreg 8720 = B + 10 * n
  b21 : c.nreg 8721 = B + 14 * n
  b09 : c.nreg 8709 = 2 * (K + n)

/-- The registers `slRegs` writes. -/
def slW (x : ℕ) : Prop := (8709 ≤ x ∧ x ≤ 8721) ∨ x = 8741 ∨ x = 8778

lemma BRegs.keep {B n K : ℕ} {c c' : Config} (h : BRegs B n K c)
    (f : ∀ x, x ≤ 8721 → c'.nreg x = c.nreg x) : BRegs B n K c' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨by rw [f _ (by omega)]; exact h0, by rw [f _ (by omega)]; exact h1,
    by rw [f _ (by omega)]; exact h2, by rw [f _ (by omega)]; exact h3,
    by rw [f _ (by omega)]; exact h4, by rw [f _ (by omega)]; exact h5,
    by rw [f _ (by omega)]; exact h6, by rw [f _ (by omega)]; exact h7,
    by rw [f _ (by omega)]; exact h8, by rw [f _ (by omega)]; exact h9,
    by rw [f _ (by omega)]; exact h10, by rw [f _ (by omega)]; exact h11,
    by rw [f _ (by omega)]; exact h12⟩

theorem slRegs_exec (c : Config) (hc : WordsBounded W c) {n K B : ℕ} (r00 : c.nreg 8700 = n)
    (r03 : c.nreg 8703 = 7 * n) (r07 : c.nreg 8707 = K) (r30 : c.nreg 8730 = B)
    (hW : B + 14 * n + 2 * K + 20 ≤ W) :
    ∃ c' t, Exec P W slRegs c c' t ∧ t = 39 ∧ BRegs B n K c' ∧ c'.nreg 8741 = 7 * n ∧
      (∀ x, ¬ slW x → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold slRegs
  exec_block
  all_goals try omega
  all_goals try (config_simp; rw [r00]; omega)
  all_goals try (config_simp; rw [r00, r30]; omega)
  all_goals try (config_simp; rw [r00, r07]; omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun x hx => ?_,
    rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; rw [r00, r30]; ring)
  · config_simp; rw [r00, r07]; ring
  · config_simp; rw [r03]
  · unfold slW at hx; config_simp; simp (disch := omega) only [upd_other]

/-- **The slot stage.** -/
def sl : Stmt := .seq slRegs (.seq (stageM 14 vbKey) (.seq (stageM 21 vbItem)
  (.seq (.seq (sumL vbVal) (block [.copyN 8731 8738])) (.seq (stageM 49 vbRev)
  (.seq (stageM 56 vbRot) (.seq (stageM 63 vbRt) (.seq (stageM 70 vbCap) (stageM 77 vbKr))))))))

section SL

variable {d : List ℕ} (wf : Wf d)

/-- The contents of the slot arrays. -/
structure SL (B : ℕ) (mem : ℕ → ℕ) : Prop where
  ky : ∀ s < 7 * nd d, mem (B + 14 * nd d + s) = keyS (map wf) (fun v => v.val) (nv d) s
  it : ∀ s < 7 * nd d, mem (B + 21 * nd d + s) =
    itS (map wf) (fun v => v.val) (nv d) (2 * (nv d + nd d)) s
  rvs : ∀ s < 7 * nd d, mem (B + 49 * nd d + s) = revS (map wf) s
  ros : ∀ s < 7 * nd d, mem (B + 56 * nd d + s) = rotS (map wf) s
  rts : ∀ s < 7 * nd d, mem (B + 63 * nd d + s) = rtS (map wf) s
  cps : ∀ s < 7 * nd d, mem (B + 70 * nd d + s) =
    capS (map wf) (fun i => cp d i) (srcF d) (snkF d) s
  krs : ∀ s < 7 * nd d, mem (B + 77 * nd d + s) = krS (map wf) (srcF d) (snkF d) s

lemma KRegs.keep {n K BIG : ℕ} {c c' : Config} (h : KRegs n K BIG c)
    (f : ∀ x, x ≤ 8708 → c'.nreg x = c.nreg x) : KRegs n K BIG c' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨by rw [f _ (by omega)]; exact h0, by rw [f _ (by omega)]; exact h1,
    by rw [f _ (by omega)]; exact h2, by rw [f _ (by omega)]; exact h3,
    by rw [f _ (by omega)]; exact h4, by rw [f _ (by omega)]; exact h5,
    by rw [f _ (by omega)]; exact h6, by rw [f _ (by omega)]; exact h7,
    by rw [f _ (by omega)]; exact h8⟩

lemma low_of_wscr {c c' : Config} (f : ∀ x, ¬ wscr x → c'.nreg x = c.nreg x) :
    ∀ x, x < 8738 → c'.nreg x = c.nreg x := fun x hx => f x (by unfold wscr pscr; omega)

variable (hl : ∀ i < nd d, tl d (rv d i) ≠ tl d i) (hrot : (map wf).RotTrans)

include hl hrot in
set_option maxHeartbeats 1000000 in
theorem sl_exec (c : Config) (hc : WordsBounded W c) {B : ℕ}
    (hK : KRegs (nd d) (nv d) (∑ x ∈ range (nd d), fl (tl d (rv d x) ≠ tl d x) * cp d x) c)
    (r30 : c.nreg 8730 = B) (h1 : PD1 d B c.nmem) (h2 : PD2 d B c.nmem)
    (hW : 10 * B + 200 * nd d + 4 * nv d + (2 * (nv d + nd d) + 1) * (7 * nd d) + 200 ≤ W) :
    ∃ c' t, Exec P W sl c c' t ∧ t ≤ 1300 * nd d + 100 ∧ SL wf B c'.nmem ∧
      c'.nreg 8731 = ∑ s ∈ range (7 * nd d), fl (ValidS (map wf) s) ∧
      (∀ a, ¬ (B + 14 * nd d ≤ a ∧ a < B + 84 * nd d) → c'.nmem a = c.nmem a) ∧
      BRegs B (nd d) (nv d) c' ∧ c'.nreg 8741 = 7 * nd d ∧
      (∀ x, ¬ wscr x → ¬ slW x → x ≠ 8731 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set n := nd d with hn
  set K := nv d with hKd
  set M := map wf with hM
  have hbig := bigN_map wf hl
  rw [← hbig] at hK
  have h7 : 7 * n ≤ (2 * (K + n) + 1) * (7 * n) := Nat.le_mul_of_pos_left _ (by omega)
  have hprod : (2 * (K + n) + 1) * (7 * nd d) = (2 * (K + n) + 1) * (7 * n) := rfl
  -- the registers
  obtain ⟨c₁, t₁, e₁, ht₁, B₁, r41, f1, m1, rr1, rm1, o1⟩ := slRegs_exec (P := P) c hc
    hK.rn hK.r7 hK.rk r30 (by omega)
  have hK₁ : KRegs n K (bigN M (fun i => cp d i)) c₁ :=
    hK.keep (fun x hx => f1 x (by unfold slW; omega))
  have r30₁ : c₁.nreg 8730 = B := by rw [f1 _ (by unfold slW; omega)]; exact r30
  -- arrays of a configuration whose low memory is that of `c`
  have arrs : ∀ c' : Config, (∀ a, a < B + 12 * n → c'.nmem a = c.nmem a) →
      (∀ x, x ≤ 8730 → c'.nreg x = c₁.nreg x) →
      KRegs n K (bigN M (fun i => cp d i)) c' ∧ BRegs B n K c' ∧
      RotArrs M c' (B + 1 * n) (B + 2 * n) (B + 3 * n) (B + 4 * n) ∧
      CapArrs M (fun i => cp d i) (srcF d) (snkF d) c' (B + 6 * n) (B + 7 * n) (B + 8 * n) ∧
      KeyArrs M (fun v => v.val) K c' (B + 5 * n) (B + 9 * n) ∧
      (∀ x < n, c'.nmem (B + 10 * n + x) = fl (IsNl M x)) ∧
      (∀ x < n, c'.nmem (B + 0 * n + x) = rvI M x) := by
    intro c' hm hr
    have p1 := h1.congr hm
    have p2 := h2.congr wf hm
    have hB' := B₁.keep (fun x hx => hr x (by omega))
    exact ⟨hK₁.keep (fun x hx => hr x (by omega)), hB', rotArrs_of wf hl hrot p1 p2 hB'.b11 hB'.b12 hB'.b13 hB'.b14,
      capArrs_of wf hl p1 hB'.b16 hB'.b17 hB'.b18,
      keyArrs_of wf hl p1 p2 hB'.b15 hB'.b19, fun x hx => nl_of wf hl p1 hx,
      fun x hx => by rw [p1.frv x hx, rvI_map wf hl hx]⟩
  have hkeyb : ∀ s < 7 * n, keyS M (fun v => v.val) K s < 2 * (K + n) := fun s hs =>
    keyS_lt M _ K (fun x hx => by rw [xt_tl wf hx]; exact wf.tl_lt x hx)
      (fun x hx => by rw [flI_map wf hl hx]; exact olab_lt (nx_permOn wf) hx) hs
  -- KY
  obtain ⟨c₂, t₂, e₂, ht₂, a2, m2, f2, rr2, rm2, o2⟩ := stageM_exec (P := P) c₁ e₁.wb_right
    (n := n) (k := 14) (m := 7 * n) (B := B) (B' := 14) (vb := vbKey)
    (fun s => keyS M (fun v => v.val) K s) hK₁.rn r30₁ r41 hK₁.one (by omega) (by omega)
    (fun i hi c' hw h40 hfr hm => by
      obtain ⟨q1, q2, -, -, q5, -, -⟩ := arrs c' (fun a ha => by rw [hm _ (by omega), m1])
        (fun x hx => low_of_wscr hfr x (by omega))
      exact vbKey_exec (P := P) M _ c' hw q1 h40 hi q5 (by omega))
  have L2 := low_of_wscr f2
  -- IT
  obtain ⟨c₃, t₃, e₃, ht₃, a3, m3, f3, rr3, rm3, o3⟩ := stageM_exec (P := P) c₂ e₂.wb_right
    (n := n) (k := 21) (m := 7 * n) (B := B) (B' := 20) (vb := vbItem)
    (fun s => itS M (fun v => v.val) K (2 * (K + n)) s)
    (by rw [L2 _ (by omega)]; exact hK₁.rn) (by rw [L2 _ (by omega)]; exact r30₁)
    (by rw [f2 _ (by unfold wscr pscr; omega)]; exact r41)
    (by rw [L2 _ (by omega)]; exact hK₁.one) (by omega) (by omega)
    (fun i hi c' hw h40 hfr hm => by
      have hr' : ∀ x, x ≤ 8730 → c'.nreg x = c₁.nreg x := fun x hx => by
        rw [low_of_wscr hfr x (by omega), L2 x (by omega)]
      obtain ⟨q1, q2, q3, -, -, q6, -⟩ := arrs c'
        (fun a ha => by rw [hm _ (by omega), m2 _ (by omega), m1]) hr'
      have IA : ItArrs M (fun v => v.val) K c' (B + 14 * n) (B + 10 * n) (B + 3 * n) (B + 4 * n)
          (2 * (K + n)) :=
        ⟨q2.b21, q2.b20, q2.b13, q2.b14, q2.b09, fun s hs => by
          rw [hm _ (by omega), a2 s hs], q6, q3.cv, q3.cf⟩
      exact vbItem_exec (P := P) M _ c' hw q1 h40 hi IA (hkeyb i hi).le (by omega))
  have L3 := low_of_wscr f3
  have L13 : ∀ x, x ≤ 8730 → c₃.nreg x = c₁.nreg x := fun x hx => by
    rw [L3 x (by omega), L2 x (by omega)]
  have M3 : ∀ a, a < B + 14 * n → c₃.nmem a = c₁.nmem a := fun a ha => by
    rw [m3 _ (by omega), m2 _ (by omega)]
  have r41₃ : c₃.nreg 8741 = 7 * n := by
    rw [f3 _ (by unfold wscr pscr; omega), f2 _ (by unfold wscr pscr; omega)]; exact r41
  -- N
  have hsumv : ∑ j ∈ range (7 * n), fl (ValidS M j) ≤ 7 * n := by
    calc ∑ j ∈ range (7 * n), fl (ValidS M j) ≤ ∑ j ∈ range (7 * n), 1 :=
          Finset.sum_le_sum fun j _ => fl_le_one _
      _ = 7 * n := by simp
  obtain ⟨c₄, t₄, e₄, ht₄, s4, m4, f4, rr4, rm4, o4⟩ := sumL_exec (P := P) c₃ e₃.wb_right
    (vb := vbVal) (m := 7 * n) (B := 14) (fun s => fl (ValidS M s)) r41₃
    (by rw [L13 _ (by omega)]; exact hK₁.one) (by omega) (by omega)
    (fun i hi c' hw h40 hfr hm => by
      have hr' : ∀ x, x ≤ 8730 → c'.nreg x = c₁.nreg x := fun x hx => by
        rw [hfr x (by unfold pscr; omega) (by omega) (by omega), L13 x hx]
      obtain ⟨q1, q2, q3, -, -, q6, -⟩ := arrs c'
        (fun a ha => by rw [hm, M3 _ (by omega), m1]) hr'
      have IA : ItArrs M (fun v => v.val) K c' (B + 14 * n) (B + 10 * n) (B + 3 * n) (B + 4 * n)
          (2 * (K + n)) :=
        ⟨q2.b21, q2.b20, q2.b13, q2.b14, q2.b09, fun s hs => by
          rw [hm, m3 _ (by omega), a2 s hs], q6, q3.cv, q3.cf⟩
      exact vbVal_exec (P := P) M _ c' hw q1 h40 hi IA (by omega))
  obtain ⟨c₅, t₅, e₅, ht₅, v5, f5, m5, rr5, rm5, o5⟩ := cpy_exec (P := P) (r := 8731) (a := 8738)
    c₄ e₄.wb_right
  have L15 : ∀ x, x ≤ 8730 → c₅.nreg x = c₁.nreg x := fun x hx => by
    rw [f5 x (by omega), f4 x (by unfold pscr; omega) (by omega) (by omega), L13 x hx]
  have r41₅ : c₅.nreg 8741 = 7 * n := by
    rw [f5 _ (by omega), f4 _ (by unfold pscr; omega) (by omega) (by omega)]; exact r41₃
  have M5 : ∀ a, a < B + 14 * n → c₅.nmem a = c₁.nmem a := fun a ha => by
    rw [m5, m4, M3 a ha]
  -- the slot functions: a generic stage
  have stg : ∀ (c₀ : Config) (k B' : ℕ) (vb : Stmt) (g : ℕ → ℕ), WordsBounded W c₀ →
      (∀ x, x ≤ 8730 → c₀.nreg x = c₁.nreg x) → c₀.nreg 8741 = 7 * n →
      (∀ a, a < B + 12 * n → c₀.nmem a = c₁.nmem a) → 49 ≤ k → k ≤ 77 →
      (∀ i < 7 * n, ∀ c' : Config, WordsBounded W c' → c'.nreg 8740 = i →
        (∀ x, x ≤ 8730 → c'.nreg x = c₁.nreg x) →
        (∀ a, a < B + 12 * n → c'.nmem a = c.nmem a) →
        ∃ c'' t, Exec P W vb c' c'' t ∧ VBPost c' (g i) B' c'' t) →
      ∃ c' t, Exec P W (stageM k vb) c₀ c' t ∧ t ≤ (B' + 5) * (7 * n) + 6 ∧
        (∀ j < 7 * n, c'.nmem (B + k * n + j) = g j) ∧
        (∀ a, ¬ (B + k * n ≤ a ∧ a < B + k * n + 7 * n) → c'.nmem a = c₀.nmem a) ∧
        (∀ x, ¬ wscr x → c'.nreg x = c₀.nreg x) ∧
        c'.rreg = c₀.rreg ∧ c'.rmem = c₀.rmem ∧ c'.output = c₀.output := by
    intro c₀ k B' vb g hw₀ hr₀ h41 hm₀ hk1 hk2 hvb
    have hk3 : k * n ≤ 77 * n := Nat.mul_le_mul_right _ hk2
    have hk4 : 49 * n ≤ k * n := Nat.mul_le_mul_right _ hk1
    exact stageM_exec (P := P) c₀ hw₀ (n := n) (k := k) (m := 7 * n) (B := B) (B' := B') g
      (by rw [hr₀ _ (by omega)]; exact hK₁.rn) (by rw [hr₀ _ (by omega)]; exact r30₁) h41
      (by rw [hr₀ _ (by omega)]; exact hK₁.one) (by omega) (by omega)
      (fun i hi c' hw h40 hfr hm => hvb i hi c' hw h40
        (fun x hx => by rw [hfr x (by unfold wscr pscr; omega), hr₀ x hx])
        (fun a ha => by rw [hm _ (by omega), hm₀ a ha, m1]))
  -- RVS
  obtain ⟨c₆, t₆, e₆, ht₆, a6, m6, f6, rr6, rm6, o6⟩ := stg c₅ 49 13 vbRev (fun s => revS M s)
    e₅.wb_right L15 r41₅ (fun a ha => M5 a (by omega)) (by norm_num) (by norm_num)
    (fun i hi c' hw h40 hr hm => by
      obtain ⟨q1, q2, -, -, -, -, q7⟩ := arrs c' hm hr
      exact vbRev_exec (P := P) M c' hw q1 h40 hi q2.b10 q7
        (fun x hx => by rw [rvI_map wf hl hx]; exact wf.rv_lt x hx) (by omega))
  have L16 : ∀ x, x ≤ 8730 → c₆.nreg x = c₁.nreg x := fun x hx => by
    rw [f6 x (by unfold wscr pscr; omega), L15 x hx]
  have r41₆ : c₆.nreg 8741 = 7 * n := by rw [f6 _ (by unfold wscr pscr; omega)]; exact r41₅
  have M6 : ∀ a, a < B + 14 * n → c₆.nmem a = c₁.nmem a := fun a ha => by
    rw [m6 _ (by omega), M5 a ha]
  -- ROS
  obtain ⟨c₇, t₇, e₇, ht₇, a7, m7, f7, rr7, rm7, o7⟩ := stg c₆ 56 20 vbRot (fun s => rotS M s)
    e₆.wb_right L16 r41₆ (fun a ha => M6 a (by omega)) (by norm_num) (by norm_num)
    (fun i hi c' hw h40 hr hm => by
      obtain ⟨q1, q2, q3, -, -, -, -⟩ := arrs c' hm hr
      exact vbRot_exec (P := P) M c' hw q1 h40 hi q3 (by omega))
  have L17 : ∀ x, x ≤ 8730 → c₇.nreg x = c₁.nreg x := fun x hx => by
    rw [f7 x (by unfold wscr pscr; omega), L16 x hx]
  have r41₇ : c₇.nreg 8741 = 7 * n := by rw [f7 _ (by unfold wscr pscr; omega)]; exact r41₆
  have M7 : ∀ a, a < B + 14 * n → c₇.nmem a = c₁.nmem a := fun a ha => by
    rw [m7 _ (by omega), M6 a ha]
  -- RTS
  obtain ⟨c₈, t₈, e₈, ht₈, a8, m8, f8, rr8, rm8, o8⟩ := stg c₇ 63 16 vbRt (fun s => rtS M s)
    e₇.wb_right L17 r41₇ (fun a ha => M7 a (by omega)) (by norm_num) (by norm_num)
    (fun i hi c' hw h40 hr hm => by
      obtain ⟨q1, q2, q3, -, -, -, -⟩ := arrs c' hm hr
      exact vbRt_exec (P := P) M c' hw q1 h40 hi q3 (by omega))
  have L18 : ∀ x, x ≤ 8730 → c₈.nreg x = c₁.nreg x := fun x hx => by
    rw [f8 x (by unfold wscr pscr; omega), L17 x hx]
  have r41₈ : c₈.nreg 8741 = 7 * n := by rw [f8 _ (by unfold wscr pscr; omega)]; exact r41₇
  have M8 : ∀ a, a < B + 14 * n → c₈.nmem a = c₁.nmem a := fun a ha => by
    rw [m8 _ (by omega), M7 a ha]
  -- CPS
  obtain ⟨c₉, t₉, e₉, ht₉, a9, m9, f9, rr9, rm9, o9⟩ := stg c₈ 70 18 vbCap
    (fun s => capS M (fun i => cp d i) (srcF d) (snkF d) s)
    e₈.wb_right L18 r41₈ (fun a ha => M8 a (by omega)) (by norm_num) (by norm_num)
    (fun i hi c' hw h40 hr hm => by
      obtain ⟨q1, q2, -, q4, -, -, -⟩ := arrs c' hm hr
      exact vbCap_exec (P := P) M _ _ _ c' hw q1 h40 hi q4 (by omega))
  have L19 : ∀ x, x ≤ 8730 → c₉.nreg x = c₁.nreg x := fun x hx => by
    rw [f9 x (by unfold wscr pscr; omega), L18 x hx]
  have r41₉ : c₉.nreg 8741 = 7 * n := by rw [f9 _ (by unfold wscr pscr; omega)]; exact r41₈
  have M9 : ∀ a, a < B + 14 * n → c₉.nmem a = c₁.nmem a := fun a ha => by
    rw [m9 _ (by omega), M8 a ha]
  -- KRS
  obtain ⟨c₁₀, t₁₀, e₁₀, ht₁₀, a10, m10, f10, rr10, rm10, o10⟩ := stg c₉ 77 20 vbKr
    (fun s => krS M (srcF d) (snkF d) s)
    e₉.wb_right L19 r41₉ (fun a ha => M9 a (by omega)) (by norm_num) (by norm_num)
    (fun i hi c' hw h40 hr hm => by
      obtain ⟨q1, q2, -, q4, -, -, -⟩ := arrs c' hm hr
      exact vbKr_exec (P := P) M (fun i => cp d i) _ _ c' hw q1 h40 hi q4 (by omega))
  have L110 : ∀ x, x ≤ 8730 → c₁₀.nreg x = c₁.nreg x := fun x hx => by
    rw [f10 x (by unfold wscr pscr; omega), L19 x hx]
  -- assembling
  refine ⟨c₁₀, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq (.seq e₄ e₅) (.seq e₆ (.seq e₇ (.seq e₈
    (.seq e₉ e₁₀))))))), by omega, ⟨fun s hs => ?_, fun s hs => ?_, fun s hs => ?_,
    fun s hs => ?_, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩, ?_, fun a ha => ?_,
    B₁.keep (fun x hx => L110 x (by omega)), ?_, fun x h1 h2 h3 => ?_,
    by rw [rr10, rr9, rr8, rr7, rr6, rr5, rr4, rr3, rr2, rr1],
    by rw [rm10, rm9, rm8, rm7, rm6, rm5, rm4, rm3, rm2, rm1],
    by rw [o10, o9, o8, o7, o6, o5, o4, o3, o2, o1]⟩
  · rw [m10 _ (by omega), m9 _ (by omega), m8 _ (by omega), m7 _ (by omega), m6 _ (by omega),
      m5, m4, m3 _ (by omega), a2 s hs]
  · rw [m10 _ (by omega), m9 _ (by omega), m8 _ (by omega), m7 _ (by omega), m6 _ (by omega),
      m5, m4, a3 s hs]
  · rw [m10 _ (by omega), m9 _ (by omega), m8 _ (by omega), m7 _ (by omega), a6 s hs]
  · rw [m10 _ (by omega), m9 _ (by omega), m8 _ (by omega), a7 s hs]
  · rw [m10 _ (by omega), m9 _ (by omega), a8 s hs]
  · rw [m10 _ (by omega), a9 s hs]
  · rw [a10 s hs]
  · rw [f10 _ (by unfold wscr pscr; omega), f9 _ (by unfold wscr pscr; omega),
      f8 _ (by unfold wscr pscr; omega), f7 _ (by unfold wscr pscr; omega),
      f6 _ (by unfold wscr pscr; omega), v5, s4]
  · rw [m10 _ (by omega), m9 _ (by omega), m8 _ (by omega), m7 _ (by omega), m6 _ (by omega),
      m5, m4, m3 _ (by omega), m2 _ (by omega), m1]
  · rw [f10 _ (by unfold wscr pscr; omega), f9 _ (by unfold wscr pscr; omega),
      f8 _ (by unfold wscr pscr; omega), f7 _ (by unfold wscr pscr; omega),
      f6 _ (by unfold wscr pscr; omega)]
    exact r41₅
  · unfold wscr at h1
    rw [f10 x h1, f9 x h1, f8 x h1, f7 x h1, f6 x h1, f5 x h3,
      f4 x (fun h => h1 (Or.inl h)) (by omega) (by omega), f3 x h1, f2 x h1,
      f1 x h2]

end SL

end Pp

end BKMNW

end PlanarFlow
