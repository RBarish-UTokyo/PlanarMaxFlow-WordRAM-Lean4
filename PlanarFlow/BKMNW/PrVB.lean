module

public import PlanarFlow.BKMNW.PrConv

/-!
# The rotation and face arrays of a map with loops on the machine

`pdL = pdW ; NX' ; SG'` runs after `pd1` (`PpPD.lean`) and overwrites

* `NX` (`B + 11 n`) by `NX'[x] = SG'[RV[x]]` if `x` is not a loop, `x` otherwise (`vbPh`);
* `SG` (`B + n`) by `SG' = T` (`vbCp`), `T` the walk of `pdW` at `B + 12 n`,

so that (**`pdL_exec`**) `SG = sgI (map wf)` and `NX = phI (map wf)` (the rotation and the face
permutation of the map without loops, identity on the loops), for any encoded map.
Also the masked flag block `vbEqM` (`fl (A[x] = x + 1) · NL[x]`, `NL` at `r8820`) for `pd2G`.
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

/-- `A[x]`, `A` at `r8727`. -/
def vbCp : Stmt := block [.addN 8755 8727 8740, .loadN 8744 8755]

theorem vbCp_exec (c : Config) (hc : WordsBounded W c) {x Ab : ℕ}
    (hx : c.nreg 8740 = x) (h27 : c.nreg 8727 = Ab) (hw : Ab + x ≤ W) :
    ∃ c' t, Exec P W vbCp c c' t ∧ VBPost c (c.nmem (Ab + x)) 2 c' t := by
  unfold vbCp
  exec_block
  · config_simp; rw [hx, h27]; omega
  refine ⟨by omega, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [hx, h27]
  · vbframe

/-- `x` if `NL[x] = 0`, else `T[RV[x]]` (`NL` at `r8727`, `RV` at `r8729`, `T` at `r8725`). -/
def vbPh : Stmt := .seq (block [.addN 8755 8727 8740, .loadN 8757 8755])
  (.ifLtN 8757 8704 (block [.copyN 8744 8740])
    (block [.addN 8755 8729 8740, .loadN 8758 8755, .addN 8755 8725 8758, .loadN 8744 8755]))

theorem vbPh_exec (c : Config) (hc : WordsBounded W c) {x Ab Rb Tb : ℕ}
    (hx : c.nreg 8740 = x) (h04 : c.nreg 8704 = 1) (h27 : c.nreg 8727 = Ab)
    (h29 : c.nreg 8729 = Rb) (h25 : c.nreg 8725 = Tb) (hw : Ab + x ≤ W) (hw' : Rb + x ≤ W)
    (hw'' : Tb + c.nmem (Rb + x) ≤ W) :
    ∃ c' t, Exec P W vbPh c c' t ∧
      VBPost c (if c.nmem (Ab + x) < 1 then x else c.nmem (Tb + c.nmem (Rb + x))) 8 c' t := by
  obtain ⟨c₁, t₁, e₁, ht₁, v57, f1, m1, rr1, rm1, o1⟩ : ∃ c₁ t₁,
      Exec P W (block [.addN 8755 8727 8740, .loadN 8757 8755]) c c₁ t₁ ∧ t₁ = 2 ∧
      c₁.nreg 8757 = c.nmem (Ab + x) ∧ (∀ y, y ≠ 8755 → y ≠ 8757 → c₁.nreg y = c.nreg y) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · config_simp; rw [hx, h27]; omega
    refine ⟨rfl, ?_, fun y h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [hx, h27]
    · config_simp; simp (disch := omega) only [upd_other]
  have q04 : c₁.nreg 8704 = 1 := by rw [f1 _ (by omega) (by omega)]; exact h04
  have q40 : c₁.nreg 8740 = x := by rw [f1 _ (by omega) (by omega)]; exact hx
  have q29 : c₁.nreg 8729 = Rb := by rw [f1 _ (by omega) (by omega)]; exact h29
  have q25 : c₁.nreg 8725 = Tb := by rw [f1 _ (by omega) (by omega)]; exact h25
  have hw₁ := e₁.wb_right
  by_cases h : c.nmem (Ab + x) < 1
  · obtain ⟨c₂, t₂, e₂, ht₂, v44, f2, m2, rr2, rm2, o2⟩ : ∃ c₂ t₂,
        Exec P W (block [.copyN 8744 8740]) c₁ c₂ t₂ ∧ t₂ = 1 ∧ c₂.nreg 8744 = x ∧
        (∀ y, y ≠ 8744 → c₂.nreg y = c₁.nreg y) ∧
        c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
      exec_block
      refine ⟨rfl, ?_, fun y h1 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [q40]
      · config_simp; simp (disch := omega) only [upd_other]
    refine ⟨c₂, t₁ + (t₂ + 1), .seq e₁ (.ifLtN_true (by rw [v57, q04]; exact h) e₂),
      ⟨by omega, by rw [v44, ppIteT h], fun y hy => ?_, by rw [m2, m1], by rw [rr2, rr1],
        by rw [rm2, rm1], by rw [o2, o1]⟩⟩
    unfold pscr at hy
    rw [f2 _ (by omega), f1 _ (by omega) (by omega)]
  · obtain ⟨c₂, t₂, e₂, ht₂, v44, f2, m2, rr2, rm2, o2⟩ : ∃ c₂ t₂,
        Exec P W (block [.addN 8755 8729 8740, .loadN 8758 8755, .addN 8755 8725 8758,
          .loadN 8744 8755]) c₁ c₂ t₂ ∧ t₂ = 4 ∧ c₂.nreg 8744 = c.nmem (Tb + c.nmem (Rb + x)) ∧
        (∀ y, y ≠ 8744 → y ≠ 8755 → y ≠ 8758 → c₂.nreg y = c₁.nreg y) ∧
        c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
      exec_block
      · config_simp; rw [q40, q29]; omega
      · config_simp; rw [q40, q29, q25, m1]; omega
      refine ⟨rfl, ?_, fun y h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [q40, q29, q25, m1]
      · config_simp; simp (disch := omega) only [upd_other]
    refine ⟨c₂, t₁ + (t₂ + 2), .seq e₁ (.ifLtN_false (by rw [v57, q04]; exact h) e₂),
      ⟨by omega, by rw [v44, ppIteF h], fun y hy => ?_, by rw [m2, m1], by rw [rr2, rr1],
        by rw [rm2, rm1], by rw [o2, o1]⟩⟩
    unfold pscr at hy
    rw [f2 _ (by omega) (by omega) (by omega), f1 _ (by omega) (by omega)]

/-- The flag of `A[x] = x + 1` times `NL[x]` (`A` at `r8727`, `NL` at `r8820`). -/
def vbEqM : Stmt :=
  block [.addN 8755 8727 8740, .loadN 8757 8755, .addN 8758 8740 8704, .subN 8755 8757 8758,
    .subN 8756 8758 8757, .addN 8755 8755 8756, .subN 8744 8704 8755, .addN 8755 8820 8740,
    .loadN 8757 8755, .mulN 8744 8744 8757]

theorem vbEqM_exec (c : Config) (hc : WordsBounded W c) {x Ab Nb : ℕ}
    (hx : c.nreg 8740 = x) (h04 : c.nreg 8704 = 1) (h27 : c.nreg 8727 = Ab)
    (h20 : c.nreg 8820 = Nb) (hw : Ab + x + 1 ≤ W) (hw' : Nb + x ≤ W) :
    ∃ c' t, Exec P W vbEqM c c' t ∧
      VBPost c (fl (c.nmem (Ab + x) = x + 1) * c.nmem (Nb + x)) 10 c' t := by
  have hm := hc.2 (Ab + x)
  have hm' := hc.2 (Nb + x)
  have hfl := fl_le_one (c.nmem (Ab + x) = x + 1)
  have hmul : fl (c.nmem (Ab + x) = x + 1) * c.nmem (Nb + x) ≤ W :=
    (Nat.mul_le_mul_right _ hfl).trans (by rw [one_mul]; exact hm')
  unfold vbEqM
  exec_block
  all_goals try (config_simp; rw [hx, h27]; omega)
  all_goals try (config_simp; rw [hx, h04]; omega)
  all_goals try (config_simp; rw [hx, h04, h27]; omega)
  all_goals try (config_simp; rw [hx, h20]; omega)
  all_goals try (config_simp; rw [hx, h04, h27, h20, eqf_eq]; exact hmul)
  refine ⟨by omega, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [hx, h04, h27, h20, eqf_eq]
  · vbframe

/-- **The rotation and face arrays without loops.** -/
def pdL : Stmt := .seq pdW (.seq (setB 8725 12) (.seq (setB 8727 10) (.seq (setB 8729 0)
  (.seq (stageM 11 vbPh) (.seq (setB 8727 12) (stageM 1 vbCp))))))

/-- The registers `pdL` may write. -/
def wscrL (x : ℕ) : Prop :=
  wscr x ∨ wR x ∨ x = 8778 ∨ x = 8811 ∨ x = 8812 ∨ x = 8813 ∨ x = 8725 ∨ x = 8727 ∨ x = 8729

set_option maxHeartbeats 1000000 in
theorem pdL_exec {d : List ℕ} (wf : Wf d) (c : Config) (hc : WordsBounded W c) {B : ℕ}
    (hS : SR (nd d) B (nd d) c) (h1 : PD1 d B c.nmem) (hW : B + 20 * nd d + 20 ≤ W) :
    ∃ c' t, Exec P W pdL c c' t ∧ t ≤ 44 * nd d + 80 ∧
      (∀ x < nd d, c'.nmem (B + 1 * nd d + x) = sgI (map wf) x) ∧
      (∀ x < nd d, c'.nmem (B + 11 * nd d + x) = phI (map wf) x) ∧
      (∀ a, ¬ (B + 1 * nd d ≤ a ∧ a < B + 2 * nd d) → ¬ (B + 11 * nd d ≤ a ∧
        a < B + 13 * nd d) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ wscrL x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set n := nd d with hn
  obtain ⟨r00, r04, r30, r41⟩ := hS
  have hP := rotW_permOn wf
  -- the walk
  obtain ⟨c₁, t₁, e₁, ht₁, a1, m1, f1, rr1, rm1, o1⟩ := pdW_exec (P := P) (f := rotW d)
    (Q := NlP d) (n := n) (B := B) hP c hc r00 r04 r30
    ⟨fun x hx => h1.fsg x hx, fun x hx => h1.fnl x hx⟩ (by omega)
  have F1 : ∀ x, ¬ wscrL x → c₁.nreg x = c.nreg x := fun x hx => by
    unfold wscrL at hx
    exact f1 x (fun h => hx (Or.inr (Or.inl h))) (by omega) (by omega) (by omega) (by omega)
  have k1 : ∀ x, ¬ wscrL x → c₁.nreg x = c.nreg x := F1
  have T1 : ∀ x < n, c₁.nmem (B + 12 * n + x) = sgI (map wf) x := fun x hx => by
    rw [a1 x hx, wv_eq_sgI wf hx]
  have nW : ∀ x, x = 8700 ∨ x = 8704 ∨ x = 8730 ∨ x = 8741 → ¬ wscrL x := by
    intro x hx; unfold wscrL wscr wR pscr; omega
  -- the bases
  obtain ⟨c₂, t₂, e₂, ht₂, v2, f2, m2, rr2, rm2, o2⟩ := setB_exec (P := P) (r := 8725) (k := 12)
    (n := n) (B := B) c₁ e₁.wb_right (by omega) (by rw [k1 _ (nW _ (by omega))]; exact r00)
    (by rw [k1 _ (nW _ (by omega))]; exact r30) (by omega)
  have k2 : ∀ x, ¬ wscrL x → c₂.nreg x = c.nreg x := fun x hx => by
    rw [f2 x (by unfold wscrL at hx; omega) (by unfold wscrL at hx; omega), k1 x hx]
  obtain ⟨c₃, t₃, e₃, ht₃, v3, f3, m3, rr3, rm3, o3⟩ := setB_exec (P := P) (r := 8727) (k := 10)
    (n := n) (B := B) c₂ e₂.wb_right (by omega) (by rw [k2 _ (nW _ (by omega))]; exact r00)
    (by rw [k2 _ (nW _ (by omega))]; exact r30) (by omega)
  have k3 : ∀ x, ¬ wscrL x → c₃.nreg x = c.nreg x := fun x hx => by
    rw [f3 x (by unfold wscrL at hx; omega) (by unfold wscrL at hx; omega), k2 x hx]
  obtain ⟨c₄, t₄, e₄, ht₄, v4, f4, m4, rr4, rm4, o4⟩ := setB_exec (P := P) (r := 8729) (k := 0)
    (n := n) (B := B) c₃ e₃.wb_right (by omega) (by rw [k3 _ (nW _ (by omega))]; exact r00)
    (by rw [k3 _ (nW _ (by omega))]; exact r30) (by omega)
  have k4 : ∀ x, ¬ wscrL x → c₄.nreg x = c.nreg x := fun x hx => by
    rw [f4 x (by unfold wscrL at hx; omega) (by unfold wscrL at hx; omega), k3 x hx]
  have v25 : c₄.nreg 8725 = B + 12 * n := by
    rw [f4 _ (by omega) (by omega), f3 _ (by omega) (by omega)]; exact v2
  have v27 : c₄.nreg 8727 = B + 10 * n := by rw [f4 _ (by omega) (by omega)]; exact v3
  have M4 : c₄.nmem = c₁.nmem := by rw [m4, m3, m2]
  -- NX'
  obtain ⟨c₅, t₅, e₅, ht₅, a5, m5, f5, rr5, rm5, o5⟩ := stageM_exec (P := P) c₄ e₄.wb_right
    (n := n) (k := 11) (m := n) (B := B) (B' := 8) (vb := vbPh)
    (fun x => phI (map wf) x) (by rw [k4 _ (nW _ (by omega))]; exact r00)
    (by rw [k4 _ (nW _ (by omega))]; exact r30) (by rw [k4 _ (nW _ (by omega))]; exact r41)
    (by rw [k4 _ (nW _ (by omega))]; exact r04) (by omega) (by omega)
    (fun i hi c' hw h40 hfr hm => by
      have hrv : rv d i < n := wf.rv_lt i hi
      have e1 : c'.nmem (B + 10 * n + i) = fl (NlP d i) := by
        rw [hm _ (by omega), M4, m1 _ (by omega)]; exact h1.fnl i hi
      have e2 : c'.nmem (B + 0 * n + i) = rv d i := by
        rw [hm _ (by omega), M4, m1 _ (by omega)]; exact h1.frv i hi
      have e3 : c'.nmem (B + 12 * n + rv d i) = sgI (map wf) (rv d i) := by
        rw [hm _ (by omega), M4]; exact T1 _ hrv
      obtain ⟨c'', t, e, post⟩ := vbPh_exec (P := P) (Ab := B + 10 * n) (Rb := B + 0 * n)
        (Tb := B + 12 * n) c' hw h40
        (by rw [hfr _ (by unfold wscr pscr; omega), k4 _ (nW _ (by omega))]; exact r04)
        (by rw [hfr _ (by unfold wscr pscr; omega)]; exact v27)
        (by rw [hfr _ (by unfold wscr pscr; omega)]; exact v4)
        (by rw [hfr _ (by unfold wscr pscr; omega)]; exact v25) (by omega) (by omega)
        (by rw [e2]; omega)
      rw [e1, e2, e3] at post
      have hv : (if fl (NlP d i) < 1 then i else sgI (map wf) (rv d i)) = phI (map wf) i := by
        rw [← phv_eq_phI wf hi]
        unfold fl
        by_cases hq : NlP d i
        · simp [hq]
        · simp [hq]
      rw [hv] at post
      exact ⟨c'', t, e, post⟩)
  have k5 : ∀ x, ¬ wscrL x → c₅.nreg x = c.nreg x := fun x hx => by
    rw [f5 x (fun h => hx (Or.inl h)), k4 x hx]
  -- SG'
  obtain ⟨c₆, t₆, e₆, ht₆, v6, f6, m6, rr6, rm6, o6⟩ := setB_exec (P := P) (r := 8727) (k := 12)
    (n := n) (B := B) c₅ e₅.wb_right (by omega) (by rw [k5 _ (nW _ (by omega))]; exact r00)
    (by rw [k5 _ (nW _ (by omega))]; exact r30) (by omega)
  have k6 : ∀ x, ¬ wscrL x → c₆.nreg x = c.nreg x := fun x hx => by
    rw [f6 x (by unfold wscrL at hx; omega) (by unfold wscrL at hx; omega), k5 x hx]
  obtain ⟨c₇, t₇, e₇, ht₇, a7, m7, f7, rr7, rm7, o7⟩ := stageM_exec (P := P) c₆ e₆.wb_right
    (n := n) (k := 1) (m := n) (B := B) (B' := 2) (vb := vbCp)
    (fun x => sgI (map wf) x) (by rw [k6 _ (nW _ (by omega))]; exact r00)
    (by rw [k6 _ (nW _ (by omega))]; exact r30) (by rw [k6 _ (nW _ (by omega))]; exact r41)
    (by rw [k6 _ (nW _ (by omega))]; exact r04) (by omega) (by omega)
    (fun i hi c' hw h40 hfr hm => by
      obtain ⟨c'', t, e, post⟩ := vbCp_exec (P := P) (Ab := B + 12 * n) c' hw h40
        (by rw [hfr _ (by unfold wscr pscr; omega)]; exact v6) (by omega)
      rw [hm _ (by omega), m6, m5 _ (by omega), M4, T1 i hi] at post
      exact ⟨c'', t, e, post⟩)
  refine ⟨c₇, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), by omega, a7,
    fun x hx => ?_, fun a h1 h2 => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · rw [m7 _ (by omega), m6, a5 x hx]
  · rw [m7 _ (by omega), m6, m5 _ (by omega), M4, m1 _ (by omega)]
  · rw [f7 x (fun h => hx (Or.inl h)), k6 x hx]
  · rw [rr7, rr6, rr5, rr4, rr3, rr2, rr1]
  · rw [rm7, rm6, rm5, rm4, rm3, rm2, rm1]
  · rw [o7, o6, o5, o4, o3, o2, o1]

end Pp

end BKMNW

end PlanarFlow
