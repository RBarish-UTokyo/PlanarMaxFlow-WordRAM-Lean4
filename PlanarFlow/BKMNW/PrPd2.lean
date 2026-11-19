module

public import PlanarFlow.BKMNW.PrVB

/-!
# The computed per-dart arrays for general rotation and face arrays

`pd2G` is `pd2` (`PpPD.lean`) for any permutations `sg` (at `B + n`) and `ph` (at `B + 11 n`) of
`[0, n)` (after `pdL`: the rotation and the face permutation of the map without loops), with the
flags `CV`, `CF` multiplied by `NL` (`vbEqM`, `NL` at `r8820 = B + 10 n`), so that a loop is never
a chosen dart. **`pd2G_exec`**: `PI[ph y] = y`, `CV`, `CF`, `FL = olab ph`, `BIG` in `r8708`.
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

/-- The arrays `pd2G` reads. -/
structure PD1G (d : List ℕ) (B : ℕ) (mem : ℕ → ℕ) (sg ph : ℕ → ℕ) : Prop where
  fsg : ∀ x < nd d, mem (B + 1 * nd d + x) = sg x
  fnx : ∀ x < nd d, mem (B + 11 * nd d + x) = ph x
  fcp : ∀ x < nd d, mem (B + 6 * nd d + x) = Feas.cp d x
  fnl : ∀ x < nd d, mem (B + 10 * nd d + x) = fl (Feas.tl d (Feas.rv d x) ≠ Feas.tl d x)

/-- **The per-dart arrays computed from those read, general permutations** (`pd2` with the flags `CV`, `CF` masked by `NL` at `r8820`): `PI` (the inverse of `NX`, `k = 2`), the
orbit labels `LV` of the rotation (`12`) and `LF` of `nx` (`13`), the flags `CV` (`3`) and `CF`
(`4`) of the chosen darts, the face labels `FL` (`5`), and the total capacity `BIG` (`r8708`). -/
def pd2G : Stmt :=
  .seq (.seq (setB 8748 11) (.seq (setB 8742 2) scatL))
  (.seq (stageM 12 vbZero) (.seq (stageM 13 vbZero)
  (.seq (.seq (setB 7350 1) (.seq (setB 7351 12) (.seq (block [.copyN 7352 8700]) olProg)))
  (.seq (.seq (setB 7350 11) (.seq (setB 7351 13) olProg))
  (.seq (.seq (setB 8727 12) (stageM 3 vbEqM))
  (.seq (.seq (setB 8727 13) (stageM 4 vbEqM))
  (.seq (stageM 5 vbPred)
  (.seq (setB 8727 10) (.seq (setB 8729 6) (.seq (sumL vbMul) (block [.copyN 8708 8738])))))))))))

/-- The contents of the computed per-dart arrays, general permutations. -/
structure PD2G (d : List ℕ) (B : ℕ) (mem : ℕ → ℕ) (sg ph : ℕ → ℕ) : Prop where
  fpi : ∀ y < nd d, mem (B + 2 * nd d + ph y) = y
  fcv : ∀ x < nd d, mem (B + 3 * nd d + x) =
    fl (olab sg x + 1 = x + 1) * fl (tl d (rv d x) ≠ tl d x)
  fcf : ∀ x < nd d, mem (B + 4 * nd d + x) =
    fl (olab ph x + 1 = x + 1) * fl (tl d (rv d x) ≠ tl d x)
  ffl : ∀ x < nd d, mem (B + 5 * nd d + x) = olab ph x

set_option maxHeartbeats 1000000 in
theorem pd2G_exec {d : List ℕ} {sg ph : ℕ → ℕ} (hsgP : PermOn sg (nd d)) (hphP : PermOn ph (nd d))
    (c : Config) (hc : WordsBounded W c) {B : ℕ}
    (hS : SR (nd d) B (nd d) c) (h1 : PD1G d B c.nmem sg ph) (r20 : c.nreg 8820 = B + 10 * nd d)
    (hbig : ∑ x ∈ range (nd d), fl (tl d (rv d x) ≠ tl d x) * cp d x ≤ W)
    (hcpW : ∀ x < nd d, cp d x ≤ W)
    (hW : B + 20 * nd d + 20 ≤ W) :
    ∃ c' t, Exec P W pd2G c c' t ∧ t ≤ 130 * nd d + 100 ∧ PD2G d B c'.nmem sg ph ∧
      c'.nreg 8708 = ∑ x ∈ range (nd d), fl (tl d (rv d x) ≠ tl d x) * cp d x ∧
      (∀ a, ¬ (B + 2 * nd d ≤ a ∧ a < B + 6 * nd d) → ¬ (B + 12 * nd d ≤ a ∧ a < B + 14 * nd d) →
        c'.nmem a = c.nmem a) ∧
      FR2 c c' ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set n := nd d with hn
  have hnx : ∀ y < n, ph y < n := fun y hy => hphP.lt y hy
  have hrw : ∀ x < n, sg x < n := fun x hx => hsgP.lt x hx
  -- PI
  obtain ⟨c₁, t₁, e₁, ht₁, v1, f1, m1, rr1, rm1, o1⟩ := setB_exec (P := P) (r := 8748) (k := 11)
    c hc (by omega) hS.1 hS.2.2.1 (by omega)
  have K1 := hS.keep2 (FR2.of_two (by unfold wscr2; omega) w2_8778 f1)
  obtain ⟨c₂, t₂, e₂, ht₂, v2, f2, m2, rr2, rm2, o2⟩ := setB_exec (P := P) (r := 8742) (k := 2)
    c₁ e₁.wb_right (by omega) K1.1 K1.2.2.1 (by omega)
  have F2 := FR2.of_two (w2 _ (by unfold wscr; omega)) w2_8778 f2
  have K2 := K1.keep2 F2
  obtain ⟨c₃, t₃, e₃, ht₃, a3, m3, f3, rr3, rm3, o3⟩ := scatL_exec (P := P) c₂ e₂.wb_right
    (m := n) (Ab := B + 11 * n) (Ob := B + 2 * n) ph K2.2.2.2 K2.2.1 v2
    (by rw [f2 8748 (by decide) (by decide)]; exact v1)
    (fun i hi => by rw [m2, m1]; exact h1.fnx i hi) hnx (fun i hi j hj e => hphP.inj i hi j hj e)
    (by omega) (by omega) (by omega)
  have F3 := FR2.of_three (w2 _ (by unfold wscr; omega)) (w2 _ (by unfold wscr; omega))
    (w2 _ (by unfold wscr pscr; omega)) f3
  have K3 := K2.keep2 F3
  -- the zero labels
  obtain ⟨c₄, t₄, e₄, ht₄, a4, m4, f4, rr4, rm4, o4⟩ := stageM_exec (P := P) c₃ e₃.wb_right
    (k := 12) (m := n) (B := B) (B' := 1) (vb := vbZero) (fun _ => 0) K3.1 K3.2.2.1 K3.2.2.2
    K3.2.1 (by omega) (by omega) (fun i hi c' hw _ _ _ => vbZero_exec c' hw)
  have K4 := K3.keep2 (FR2.of_wscr f4)
  obtain ⟨c₅, t₅, e₅, ht₅, a5, m5, f5, rr5, rm5, o5⟩ := stageM_exec (P := P) c₄ e₄.wb_right
    (k := 13) (m := n) (B := B) (B' := 1) (vb := vbZero) (fun _ => 0) K4.1 K4.2.2.1 K4.2.2.2
    K4.2.1 (by omega) (by omega) (fun i hi c' hw _ _ _ => vbZero_exec c' hw)
  have K5 := K4.keep2 (FR2.of_wscr f5)
  -- the labels of the rotation
  obtain ⟨c₆, t₆, e₆, ht₆, v6, f6, m6, rr6, rm6, o6⟩ := setB_exec (P := P) (r := 7350) (k := 1)
    c₅ e₅.wb_right (by omega) K5.1 K5.2.2.1 (by omega)
  have F6 := FR2.of_two (by unfold wscr2; omega) w2_8778 f6
  have K6 := K5.keep2 F6
  obtain ⟨c₇, t₇, e₇, ht₇, v7, f7, m7, rr7, rm7, o7⟩ := setB_exec (P := P) (r := 7351) (k := 12)
    c₆ e₆.wb_right (by omega) K6.1 K6.2.2.1 (by omega)
  have F7 := FR2.of_two (by unfold wscr2; omega) w2_8778 f7
  have K7 := K6.keep2 F7
  obtain ⟨c₈, t₈, e₈, ht₈, v8, f8, m8, rr8, rm8, o8⟩ := cpy_exec (P := P) (r := 7352) (a := 8700)
    c₇ e₇.wb_right
  have F8 := FR2.of_one (r := 7352) (by unfold wscr2; omega) f8
  have K8 := K7.keep2 F8
  obtain ⟨c₉, t₉, e₉, ht₉, a9, m9, f9, rr9, rm9, o9⟩ := olProg_exec (P := P)
    hsgP (Pb := B + 1 * n) (Lb := B + 12 * n) (by omega) (by omega) (by omega)
    c₈ e₈.wb_right (by rw [f8 _ (by omega), f7 _ (by omega) (by omega)]; exact v6)
    (by rw [f8 _ (by omega)]; exact v7) (by rw [v8, K7.1])
    (fun x hx => by
      rw [m8, m7, m6, m5 _ (by omega), m4 _ (by omega), m3 _ (by omega), m2, m1]
      exact h1.fsg x hx)
    (fun x hx => by rw [m8, m7, m6, m5 _ (by omega), a4 x hx])
  have F9 := FR2.of_ol f9
  have K9 := K8.keep2 F9
  -- the labels of `nx`
  obtain ⟨c₁₀, t₁₀, e₁₀, ht₁₀, v10, f10, m10, rr10, rm10, o10⟩ := setB_exec (P := P) (r := 7350)
    (k := 11) c₉ e₉.wb_right (by omega) K9.1 K9.2.2.1 (by omega)
  have F10 := FR2.of_two (by unfold wscr2; omega) w2_8778 f10
  have K10 := K9.keep2 F10
  obtain ⟨c₁₁, t₁₁, e₁₁, ht₁₁, v11, f11, m11, rr11, rm11, o11⟩ := setB_exec (P := P) (r := 7351)
    (k := 13) c₁₀ e₁₀.wb_right (by omega) K10.1 K10.2.2.1 (by omega)
  have F11 := FR2.of_two (by unfold wscr2; omega) w2_8778 f11
  have K11 := K10.keep2 F11
  obtain ⟨c₁₂, t₁₂, e₁₂, ht₁₂, a12, m12, f12, rr12, rm12, o12⟩ := olProg_exec (P := P)
    hphP (Pb := B + 11 * n) (Lb := B + 13 * n) (by omega) (by omega) (by omega)
    c₁₁ e₁₁.wb_right (by rw [f11 _ (by omega) (by omega)]; exact v10) v11
    (by rw [f11 _ (by omega) (by omega), f10 _ (by omega) (by omega), f9 _ (by omega), v8]
        exact K7.1)
    (fun x hx => by
      rw [m11, m10, m9 _ (by omega), m8, m7, m6, m5 _ (by omega), m4 _ (by omega),
        m3 _ (by omega), m2, m1]
      exact h1.fnx x hx)
    (fun x hx => by rw [m11, m10, m9 _ (by omega), m8, m7, m6, a5 x hx])
  have F12 := FR2.of_ol f12
  have K12 := K11.keep2 F12
  -- memory of the read arrays after `c₁₂`
  have M12 : ∀ a, ¬ (B + 2 * n ≤ a ∧ a < B + 3 * n) → ¬ (B + 12 * n ≤ a ∧ a < B + 14 * n) →
      c₁₂.nmem a = c.nmem a := fun a ha hb => by
    rw [m12 _ (by omega), m11, m10, m9 _ (by omega), m8, m7, m6, m5 _ (by omega),
      m4 _ (by omega), m3 _ (by omega), m2, m1]
  have LV : ∀ x < n, c₁₂.nmem (B + 12 * n + x) = olab sg x + 1 := fun x hx => by
    rw [m12 _ (by omega), m11, m10, a9 x hx]
  have LF : ∀ x < n, c₁₂.nmem (B + 13 * n + x) = olab ph x + 1 := a12
  -- CV
  obtain ⟨c₁₃, t₁₃, e₁₃, ht₁₃, v13, f13, m13, rr13, rm13, o13⟩ := setB_exec (P := P) (r := 8727)
    (k := 12) c₁₂ e₁₂.wb_right (by omega) K12.1 K12.2.2.1 (by omega)
  have F13 := FR2.of_two (by unfold wscr2; omega) w2_8778 f13
  have K13 := K12.keep2 F13
  have FA : FR2 c c₁₃ := ((((((((((((FR2.of_two (by unfold wscr2; omega) w2_8778 f1).trans F2).trans
      F3).trans (FR2.of_wscr f4)).trans (FR2.of_wscr f5)).trans F6).trans F7).trans F8).trans
      F9).trans F10).trans F11).trans F12).trans F13
  have R13 : c₁₃.nreg 8820 = B + 10 * n := (FA 8820 (by unfold wscr2 wscr pscr; omega)).trans r20
  obtain ⟨c₁₄, t₁₄, e₁₄, ht₁₄, a14, m14, f14, rr14, rm14, o14⟩ := stageM_exec (P := P) c₁₃
    e₁₃.wb_right (k := 3) (m := n) (B := B) (B' := 10) (vb := vbEqM)
    (fun x => fl (olab sg x + 1 = x + 1) * fl (tl d (rv d x) ≠ tl d x)) K13.1 K13.2.2.1
    K13.2.2.2 K13.2.1 (by omega)
    (by omega) (fun i hi c' hw h40 hfr hm => by
      obtain ⟨c'', t, e, post⟩ := vbEqM_exec (P := P) (Ab := B + 12 * n) (Nb := B + 10 * n) c' hw
        h40 (by rw [hfr _ (by unfold wscr pscr; omega)]; exact K13.2.1)
        (by rw [hfr _ (by unfold wscr pscr; omega)]; exact v13)
        (by rw [hfr _ (by unfold wscr pscr; omega)]; exact R13) (by omega) (by omega)
      rw [hm _ (by omega), m13, LV i hi, hm _ (by omega), m13, M12 _ (by omega) (by omega),
        h1.fnl i hi] at post
      exact ⟨c'', t, e, post⟩)
  have F14 := FR2.of_wscr f14
  have K14 := K13.keep2 F14
  -- CF
  obtain ⟨c₁₅, t₁₅, e₁₅, ht₁₅, v15, f15, m15, rr15, rm15, o15⟩ := setB_exec (P := P) (r := 8727)
    (k := 13) c₁₄ e₁₄.wb_right (by omega) K14.1 K14.2.2.1 (by omega)
  have F15 := FR2.of_two (by unfold wscr2; omega) w2_8778 f15
  have K15 := K14.keep2 F15
  have R15 : c₁₅.nreg 8820 = B + 10 * n :=
    ((F14.trans F15) 8820 (by unfold wscr2 wscr pscr; omega)).trans R13
  have LF15 : ∀ x < n, c₁₅.nmem (B + 13 * n + x) = olab ph x + 1 := fun x hx => by
    rw [m15, m14 _ (by omega), m13, LF x hx]
  obtain ⟨c₁₆, t₁₆, e₁₆, ht₁₆, a16, m16, f16, rr16, rm16, o16⟩ := stageM_exec (P := P) c₁₅
    e₁₅.wb_right (k := 4) (m := n) (B := B) (B' := 10) (vb := vbEqM)
    (fun x => fl (olab ph x + 1 = x + 1) * fl (tl d (rv d x) ≠ tl d x)) K15.1 K15.2.2.1
    K15.2.2.2 K15.2.1 (by omega)
    (by omega) (fun i hi c' hw h40 hfr hm => by
      obtain ⟨c'', t, e, post⟩ := vbEqM_exec (P := P) (Ab := B + 13 * n) (Nb := B + 10 * n) c' hw
        h40 (by rw [hfr _ (by unfold wscr pscr; omega)]; exact K15.2.1)
        (by rw [hfr _ (by unfold wscr pscr; omega)]; exact v15)
        (by rw [hfr _ (by unfold wscr pscr; omega)]; exact R15) (by omega) (by omega)
      rw [hm _ (by omega), LF15 i hi, hm _ (by omega), m15, m14 _ (by omega), m13,
        M12 _ (by omega) (by omega), h1.fnl i hi] at post
      exact ⟨c'', t, e, post⟩)
  have F16 := FR2.of_wscr f16
  have K16 := K15.keep2 F16
  -- FL
  have v16 : c₁₆.nreg 8727 = B + 13 * n := by
    rw [f16 _ (by unfold wscr pscr; omega)]; exact v15
  obtain ⟨c₁₇, t₁₇, e₁₇, ht₁₇, a17, m17, f17, rr17, rm17, o17⟩ := stageM_exec (P := P) c₁₆
    e₁₆.wb_right (k := 5) (m := n) (B := B) (B' := 3) (vb := vbPred)
    (fun x => olab ph x) K16.1 K16.2.2.1 K16.2.2.2 K16.2.1 (by omega)
    (by omega) (fun i hi c' hw h40 hfr hm => by
      obtain ⟨c'', t, e, post⟩ := vbPred_exec (P := P) (Ab := B + 13 * n) c' hw h40
        (by rw [hfr _ (by unfold wscr pscr; omega)]; exact K16.2.1)
        (by rw [hfr _ (by unfold wscr pscr; omega)]; exact v16) (by omega)
      rw [hm _ (by omega), m16 _ (by omega), LF15 i hi, Nat.add_sub_cancel] at post
      exact ⟨c'', t, e, post⟩)
  have F17 := FR2.of_wscr f17
  have K17 := K16.keep2 F17
  -- BIG
  obtain ⟨c₁₈, t₁₈, e₁₈, ht₁₈, v18, f18, m18, rr18, rm18, o18⟩ := setB_exec (P := P) (r := 8727)
    (k := 10) c₁₇ e₁₇.wb_right (by omega) K17.1 K17.2.2.1 (by omega)
  have F18 := FR2.of_two (by unfold wscr2; omega) w2_8778 f18
  have K18 := K17.keep2 F18
  obtain ⟨c₁₉, t₁₉, e₁₉, ht₁₉, v19, f19, m19, rr19, rm19, o19⟩ := setB_exec (P := P) (r := 8729)
    (k := 6) c₁₈ e₁₈.wb_right (by omega) K18.1 K18.2.2.1 (by omega)
  have F19 := FR2.of_two (by unfold wscr2; omega) w2_8778 f19
  have K19 := K18.keep2 F19
  have M19 : ∀ a, ¬ (B + 2 * n ≤ a ∧ a < B + 6 * n) → c₁₉.nmem a = c₁₂.nmem a := fun a ha => by
    rw [m19, m18, m17 _ (by omega), m16 _ (by omega), m15, m14 _ (by omega), m13]
  have v19' : c₁₉.nreg 8727 = B + 10 * n := by rw [f19 8727 (by decide) (by decide)]; exact v18
  obtain ⟨c₂₀, t₂₀, e₂₀, ht₂₀, s20, m20, f20, rr20, rm20, o20⟩ := sumL_exec (P := P) c₁₉
    e₁₉.wb_right (vb := vbMul) (m := n) (B := 5) (fun x => fl (tl d (rv d x) ≠ tl d x) * cp d x)
    K19.2.2.2 K19.2.1 hbig (by omega) (fun i hi c' hw h40 hfr hm => by
      have e1 : c'.nmem (B + 10 * n + i) = fl (tl d (rv d i) ≠ tl d i) := by
        rw [hm, M19 _ (by omega), M12 _ (by omega) (by omega)]; exact h1.fnl i hi
      have e2 : c'.nmem (B + 6 * n + i) = cp d i := by
        rw [hm, M19 _ (by omega), M12 _ (by omega) (by omega)]; exact h1.fcp i hi
      obtain ⟨c'', t, e, post⟩ := vbMul_exec (P := P) (Ab := B + 10 * n) (Bb := B + 6 * n) c' hw
        h40
        (by rw [hfr _ (by unfold pscr; omega) (by omega) (by omega)]; exact v19')
        (by rw [hfr _ (by unfold pscr; omega) (by omega) (by omega)]; exact v19) (by omega)
        (by omega) (by rw [e1, e2]; have := fl_le_one (tl d (rv d i) ≠ tl d i)
                       have := hcpW i hi
                       calc _ ≤ 1 * cp d i := Nat.mul_le_mul_right _ ‹_›
                         _ ≤ W := by omega)
      rw [e1, e2] at post
      exact ⟨c'', t, e, post⟩)
  have F20 : FR2 c₁₉ c₂₀ := fun x hx => f20 x (fun h => hx (Or.inl (Or.inl h)))
    (by unfold wscr2 wscr at hx; omega) (by unfold wscr2 wscr at hx; omega)
  obtain ⟨c₂₁, t₂₁, e₂₁, ht₂₁, v21, f21, m21, rr21, rm21, o21⟩ := cpy_exec (P := P) (r := 8708)
    (a := 8738) c₂₀ e₂₀.wb_right
  have F21 := FR2.of_one (r := 8708) (by unfold wscr2; omega) f21
  -- assembling
  refine ⟨c₂₁, _, .seq (.seq e₁ (.seq e₂ e₃)) (.seq e₄ (.seq e₅ (.seq (.seq e₆ (.seq e₇
    (.seq e₈ e₉))) (.seq (.seq e₁₀ (.seq e₁₁ e₁₂)) (.seq (.seq e₁₃ e₁₄) (.seq (.seq e₁₅ e₁₆)
    (.seq e₁₇ (.seq e₁₈ (.seq e₁₉ (.seq e₂₀ e₂₁)))))))))), ?_, ⟨fun y hy => ?_, fun x hx => ?_,
    fun x hx => ?_, fun x hx => ?_⟩, by rw [v21, s20], fun a ha hb => ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · have := hnx y hy
    rw [m21, m20, m19, m18, m17 _ (by omega), m16 _ (by omega), m15, m14 _ (by omega), m13,
      m12 _ (by omega), m11, m10, m9 _ (by omega), m8, m7, m6,
      m5 _ (by omega), m4 _ (by omega), a3 y hy]
  · rw [m21, m20, m19, m18, m17 _ (by omega), m16 _ (by omega), m15, a14 x hx]
  · rw [m21, m20, m19, m18, m17 _ (by omega), a16 x hx]
  · rw [m21, m20, m19, m18, a17 x hx]
  · rw [m21, m20, M19 _ ha, M12 _ (by omega) hb]
  · exact ((((((((((((((((((((FR2.of_two (by unfold wscr2; omega) w2_8778 f1).trans F2).trans
      F3).trans (FR2.of_wscr f4)).trans (FR2.of_wscr f5)).trans F6).trans F7).trans F8).trans
      F9).trans F10).trans F11).trans F12).trans F13).trans F14).trans F15).trans F16).trans
      F17).trans F18).trans F19).trans F20).trans F21
  · rw [rr21, rr20, rr19, rr18, rr17, rr16, rr15, rr14, rr13, rr12, rr11, rr10, rr9, rr8, rr7,
      rr6, rr5, rr4, rr3, rr2, rr1]
  · rw [rm21, rm20, rm19, rm18, rm17, rm16, rm15, rm14, rm13, rm12, rm11, rm10, rm9, rm8, rm7,
      rm6, rm5, rm4, rm3, rm2, rm1]
  · rw [o21, o20, o19, o18, o17, o16, o15, o14, o13, o12, o11, o10, o9, o8, o7, o6, o5, o4,
      o3, o2, o1]

end Pp

end BKMNW

end PlanarFlow
