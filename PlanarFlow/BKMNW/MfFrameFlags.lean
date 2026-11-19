module

public import PlanarFlow.BKMNW.LinMap
public import PlanarFlow.BKMNW.LinCmp

/-!
# The per-dart data of the child frames on the machine

From the parent's frame and the separator data (per dart: `LP` the dart in the left piece, `CV`
the tail on the separator; per hole: `HM` the hole meets the separator), the value blocks of
`mapProg` loops computing, dart by dart:

* `NH[i] = nhF CV[i] HL[i] HM[HL[i] - 1]` (the tail in the new hole), `vbNH`;
* `HF[j] = hfF HM[j]` (the hole kept), `vbHF`;
* `FLl[i]`, `FLr[i]` (`flF`: the dart in the left / right piece and not both ends in the new
  hole), `vbFLl`, `vbFLr`;
* `KC[i] = kcF NH[i] KR[i]` (the child's rank), `vbKC`;
* `HC[i] = hcF NH[i] HL[i] HCI[HL[i] - 1] (nd + 1)` (the child's hole label, `HCI` the
  compaction of the kept holes, `nd` their number), `vbHC`;
* `ID[i] = i`, `vbID`.

Registers: counter `6520`, `6521 = 1`, store address `6522`, value `6523`, scratch
`6524 … 6529`, `6539 = 0`, bases `6540 … 6548`.
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

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The value functions -/

/-- The tail in the new hole: on the separator, or in a hole meeting it. -/
def nhF (cv hl hmv : ℕ) : ℕ := if 0 < cv then 1 else if 0 < hl then hmv else 0

/-- The hole kept (disjoint from the separator). -/
def hfF (hm : ℕ) : ℕ := if 0 < hm then 0 else 1

/-- Both ends in the new hole. -/
def inF (nhi nhj : ℕ) : ℕ := if 0 < nhi then nhj else 0

/-- A dart of the left child. -/
def flL (lp nhi nhj : ℕ) : ℕ := if 0 < lp then (if inF nhi nhj < 1 then 1 else 0) else 0

/-- A dart of the right child. -/
def flR (lp nhi nhj : ℕ) : ℕ := if 0 < lp then 0 else (if inF nhi nhj < 1 then 1 else 0)

/-- The child's rank. -/
def kcF (nh kr : ℕ) : ℕ := if 0 < nh then 1 else kr

/-- The child's hole label. -/
def hcF (nh hl hci nd1 : ℕ) : ℕ := if 0 < nh then nd1 else if 0 < hl then hci + 1 else 0

/-! ### The value blocks -/

/-- `r6523 := nhF CV[i] HL[i] HM[HL[i] - 1]` (bases `6540`, `6541`, `6542`). -/
def vbNH : Stmt :=
  .seq (block [.addN 6524 6540 6520, .loadN 6525 6524])
    (.ifLtN 6539 6525 (block [.constN 6523 1])
      (.seq (block [.addN 6524 6541 6520, .loadN 6526 6524])
        (.ifLtN 6539 6526 (block [.subN 6526 6526 6521, .addN 6524 6542 6526, .loadN 6523 6524])
          (block [.constN 6523 0]))))

/-- `r6523 := hfF HM[i]` (base `6542`). -/
def vbHF : Stmt :=
  .seq (block [.addN 6524 6542 6520, .loadN 6525 6524])
    (.ifLtN 6539 6525 (block [.constN 6523 0]) (block [.constN 6523 1]))

/-- The loads of the flags: `r6525 = NH[i]`, `r6527 = NH[RV[i]]`, `r6528 = LP[i]`,
`r6529 = inF` (bases `6544 = NH`, `6545 = RV`, `6543 = LP`). -/
def vbLd : Stmt :=
  .seq (block [.addN 6524 6544 6520, .loadN 6525 6524])
    (.seq (block [.addN 6524 6545 6520, .loadN 6526 6524])
      (.seq (block [.addN 6524 6544 6526, .loadN 6527 6524])
        (.seq (block [.addN 6524 6543 6520, .loadN 6528 6524])
          (.ifLtN 6539 6525 (block [.copyN 6529 6527]) (block [.constN 6529 0])))))

/-- `r6523 := flL LP[i] NH[i] NH[RV[i]]`. -/
def vbFLl : Stmt :=
  .seq vbLd (.ifLtN 6539 6528 (.ifLtN 6529 6521 (block [.constN 6523 1]) (block [.constN 6523 0]))
    (block [.constN 6523 0]))

/-- `r6523 := flR LP[i] NH[i] NH[RV[i]]`. -/
def vbFLr : Stmt :=
  .seq vbLd (.ifLtN 6539 6528 (block [.constN 6523 0])
    (.ifLtN 6529 6521 (block [.constN 6523 1]) (block [.constN 6523 0])))

/-- `r6523 := kcF NH[i] KR[i]` (bases `6544 = NH`, `6546 = KR`). -/
def vbKC : Stmt :=
  .seq (block [.addN 6524 6544 6520, .loadN 6525 6524])
    (.seq (block [.addN 6524 6546 6520, .loadN 6526 6524])
      (.ifLtN 6539 6525 (block [.constN 6523 1]) (block [.copyN 6523 6526])))

/-- `r6523 := hcF NH[i] HL[i] HCI[HL[i] - 1] (nd + 1)` (bases `6544 = NH`, `6541 = HL`,
`6547 = HCI`, `6548 = nd + 1`). -/
def vbHC : Stmt :=
  .seq (block [.addN 6524 6544 6520, .loadN 6525 6524])
    (.ifLtN 6539 6525 (block [.copyN 6523 6548])
      (.seq (block [.addN 6524 6541 6520, .loadN 6526 6524])
        (.ifLtN 6539 6526 (block [.subN 6526 6526 6521, .addN 6524 6547 6526, .loadN 6527 6524,
          .addN 6523 6527 6521]) (block [.constN 6523 0]))))

/-- `r6523 := i`. -/
def vbID : Stmt := block [.copyN 6523 6520]

/-- The scratch registers of the value blocks. -/
def vscr (x : ℕ) : Prop := 6523 ≤ x ∧ x ≤ 6529

section Exec

variable {P : Input} {W : ℕ}

/-- A two-instruction load `r := mem (base + i)`. -/
theorem ld2_exec (c : Config) (hc : WordsBounded W c) {t r b ctr i B : ℕ}
    (rb : c.nreg b = B) (rc : c.nreg ctr = i) (w : B + i ≤ W) (h1 : t ≠ b) (h2 : t ≠ ctr) :
    ∃ c' k, Exec P W (block [.addN t b ctr, .loadN r t]) c c' k ∧ k = 2 ∧
      c'.nreg r = c.nmem (B + i) ∧ (∀ x, x ≠ t → x ≠ r → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, rb, rc]; omega)
  refine ⟨rfl, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, rb, rc])
    try omega

/-- A one-instruction constant. -/
theorem cst_exec (c : Config) (hc : WordsBounded W c) {r v : ℕ} (hv : v ≤ W) :
    ∃ c' k, Exec P W (block [.constN r v]) c c' k ∧ k = 1 ∧ c'.nreg r = v ∧
      (∀ x, x ≠ r → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])

/-- A one-instruction copy. -/
theorem cpy_exec (c : Config) (hc : WordsBounded W c) {r a : ℕ} :
    ∃ c' k, Exec P W (block [.copyN r a]) c c' k ∧ k = 1 ∧ c'.nreg r = c.nreg a ∧
      (∀ x, x ≠ r → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try (have := hc.1 a; omega)
  refine ⟨rfl, ?_, fun x h => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])

/-- The tail of `vbNH`: `r6523 := HM[hl - 1]`. -/
theorem vbHM_exec (c : Config) (hc : WordsBounded W c) {HMb hl : ℕ} (r21 : c.nreg 6521 = 1)
    (r26 : c.nreg 6526 = hl) (r42 : c.nreg 6542 = HMb) (hl1 : 0 < hl) (w : HMb + (hl - 1) ≤ W) :
    ∃ c' k, Exec P W (block [.subN 6526 6526 6521, .addN 6524 6542 6526, .loadN 6523 6524]) c c'
      k ∧ k = 3 ∧ c'.nreg 6523 = c.nmem (HMb + (hl - 1)) ∧ (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hc.1 6526
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r21, r26, r42]; omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp (disch := omega) only [upd_other, upd_same, r21, r26, r42]
  · unfold vscr at hx
    config_simp; simp (disch := omega) only [upd_other, upd_same]

/-- **The value block `vbNH`.** -/
theorem vbNH_exec (c : Config) (hc : WordsBounded W c) {i CVb HLb HMb : ℕ}
    (r20 : c.nreg 6520 = i) (r21 : c.nreg 6521 = 1) (r39 : c.nreg 6539 = 0)
    (r40 : c.nreg 6540 = CVb) (r41 : c.nreg 6541 = HLb) (r42 : c.nreg 6542 = HMb)
    (w1 : CVb + i ≤ W) (w2 : HLb + i ≤ W)
    (w3 : 0 < c.nmem (HLb + i) → HMb + (c.nmem (HLb + i) - 1) ≤ W) :
    ∃ c' k, Exec P W vbNH c c' k ∧ k ≤ 10 ∧
      c'.nreg 6523 = nhF (c.nmem (CVb + i)) (c.nmem (HLb + i))
        (c.nmem (HMb + (c.nmem (HLb + i) - 1))) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hW1 : 1 ≤ W := r21 ▸ hc.1 6521
  obtain ⟨c₁, k₁, e₁, hk₁, v1, n1, m1, rr1, rm1, o1⟩ := ld2_exec (P := P) (t := 6524) (r := 6525)
    (b := 6540) (ctr := 6520) c hc r40 r20 w1 (by omega) (by omega)
  have q1 : ∀ x, ¬ vscr x → c₁.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; exact n1 x (by omega) (by omega)
  have z1 : c₁.nreg 6539 = 0 := by rw [q1 _ (by unfold vscr; omega), r39]
  unfold vbNH
  by_cases h1 : 0 < c.nmem (CVb + i)
  · obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := cst_exec (P := P) (r := 6523) (v := 1)
      c₁ e₁.wb_right hW1
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true (by rw [z1, v1]; exact h1) e₂), by omega,
      by rw [v2]; simp [nhF, h1], fun x hx => ?_, by rw [m2, m1], by rw [rr2, rr1],
      by rw [rm2, rm1], by rw [o2, o1]⟩
    rw [n2 x (by unfold vscr at hx; omega), q1 x hx]
  · have q1' : c₁.nreg 6520 = i := by rw [q1 _ (by unfold vscr; omega), r20]
    obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := ld2_exec (P := P) (t := 6524)
      (r := 6526) (b := 6541) (ctr := 6520) c₁ e₁.wb_right (by rw [q1 _ (by unfold vscr; omega), r41]) q1' w2 (by omega)
      (by omega)
    have q2 : ∀ x, ¬ vscr x → c₂.nreg x = c.nreg x := fun x hx => by
      unfold vscr at hx; rw [n2 x (by omega) (by omega), q1 x (by unfold vscr; omega)]
    have z2 : c₂.nreg 6539 = 0 := by rw [q2 _ (by unfold vscr; omega), r39]
    rw [m1] at v2
    by_cases h2 : 0 < c.nmem (HLb + i)
    · obtain ⟨c₃, k₃, e₃, hk₃, v3, n3, m3, rr3, rm3, o3⟩ := vbHM_exec (P := P) c₂ e₂.wb_right
        (by rw [q2 _ (by unfold vscr; omega), r21]) v2 (by rw [q2 _ (by unfold vscr; omega), r42])
        h2 (w3 h2)
      refine ⟨c₃, _, .seq e₁ (.ifLtN_false (by rw [z1, v1]; exact h1)
        (.seq e₂ (.ifLtN_true (by rw [z2, v2]; exact h2) e₃))), by omega, ?_, fun x hx => ?_,
        by rw [m3, m2, m1], by rw [rr3, rr2, rr1], by rw [rm3, rm2, rm1], by rw [o3, o2, o1]⟩
      · rw [v3, m2, m1]; simp [nhF, h1, h2]
      · rw [n3 x hx, q2 x hx]
    · obtain ⟨c₃, k₃, e₃, hk₃, v3, n3, m3, rr3, rm3, o3⟩ := cst_exec (P := P) (r := 6523) (v := 0)
        c₂ e₂.wb_right (Nat.zero_le _)
      refine ⟨c₃, _, .seq e₁ (.ifLtN_false (by rw [z1, v1]; exact h1)
        (.seq e₂ (.ifLtN_false (by rw [z2, v2]; exact h2) e₃))), by omega, ?_, fun x hx => ?_,
        by rw [m3, m2, m1], by rw [rr3, rr2, rr1], by rw [rm3, rm2, rm1], by rw [o3, o2, o1]⟩
      · rw [v3]; simp [nhF, h1, h2]
      · rw [n3 x (by unfold vscr at hx; omega), q2 x hx]

/-- **The value block `vbHF`.** -/
theorem vbHF_exec (c : Config) (hc : WordsBounded W c) {i HMb : ℕ}
    (r20 : c.nreg 6520 = i) (r21 : c.nreg 6521 = 1) (r39 : c.nreg 6539 = 0) (r42 : c.nreg 6542 = HMb)
    (w : HMb + i ≤ W) :
    ∃ c' k, Exec P W vbHF c c' k ∧ k ≤ 5 ∧ c'.nreg 6523 = hfF (c.nmem (HMb + i)) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v1, n1, m1, rr1, rm1, o1⟩ := ld2_exec (P := P) (t := 6524) (r := 6525)
    (b := 6542) (ctr := 6520) c hc r42 r20 w (by omega) (by omega)
  have q1 : ∀ x, ¬ vscr x → c₁.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; exact n1 x (by omega) (by omega)
  have z1 : c₁.nreg 6539 = 0 := by rw [q1 _ (by unfold vscr; omega), r39]
  unfold vbHF
  by_cases h1 : 0 < c.nmem (HMb + i)
  · obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := cst_exec (P := P) (r := 6523) (v := 0)
      c₁ e₁.wb_right (Nat.zero_le _)
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true (by rw [z1, v1]; exact h1) e₂), by omega,
      by rw [v2]; simp [hfF, h1], fun x hx => ?_, by rw [m2, m1], by rw [rr2, rr1],
      by rw [rm2, rm1], by rw [o2, o1]⟩
    rw [n2 x (by unfold vscr at hx; omega), q1 x hx]
  · obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := cst_exec (P := P) (r := 6523) (v := 1)
      c₁ e₁.wb_right (r21 ▸ hc.1 6521)
    refine ⟨c₂, _, .seq e₁ (.ifLtN_false (by rw [z1, v1]; exact h1) e₂), by omega,
      by rw [v2]; simp [hfF, h1], fun x hx => ?_, by rw [m2, m1], by rw [rr2, rr1],
      by rw [rm2, rm1], by rw [o2, o1]⟩
    rw [n2 x (by unfold vscr at hx; omega), q1 x hx]

/-- **The loads of the flags.** -/
theorem vbLd_exec (c : Config) (hc : WordsBounded W c) {i LPb NHb RVb : ℕ}
    (r20 : c.nreg 6520 = i) (r39 : c.nreg 6539 = 0) (r43 : c.nreg 6543 = LPb)
    (r44 : c.nreg 6544 = NHb) (r45 : c.nreg 6545 = RVb) (w1 : NHb + i ≤ W) (w2 : RVb + i ≤ W)
    (w3 : NHb + c.nmem (RVb + i) ≤ W) (w4 : LPb + i ≤ W) :
    ∃ c' k, Exec P W vbLd c c' k ∧ k ≤ 11 ∧ c'.nreg 6528 = c.nmem (LPb + i) ∧
      c'.nreg 6529 = inF (c.nmem (NHb + i)) (c.nmem (NHb + c.nmem (RVb + i))) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v1, n1, m1, rr1, rm1, o1⟩ := ld2_exec (P := P) (t := 6524) (r := 6525)
    (b := 6544) (ctr := 6520) c hc r44 r20 w1 (by omega) (by omega)
  have q1 : ∀ x, ¬ vscr x → c₁.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; exact n1 x (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := ld2_exec (P := P) (t := 6524) (r := 6526)
    (b := 6545) (ctr := 6520) c₁ e₁.wb_right (by rw [q1 _ (by unfold vscr; omega), r45])
    (by rw [q1 _ (by unfold vscr; omega), r20]) w2 (by omega) (by omega)
  have q2 : ∀ x, ¬ vscr x → c₂.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; rw [n2 x (by omega) (by omega), q1 x (by unfold vscr; omega)]
  rw [m1] at v2
  obtain ⟨c₃, k₃, e₃, hk₃, v3, n3, m3, rr3, rm3, o3⟩ := ld2_exec (P := P) (t := 6524) (r := 6527)
    (b := 6544) (ctr := 6526) c₂ e₂.wb_right (by rw [q2 _ (by unfold vscr; omega), r44]) v2 w3
    (by omega) (by omega)
  have q3 : ∀ x, ¬ vscr x → c₃.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; rw [n3 x (by omega) (by omega), q2 x (by unfold vscr; omega)]
  have v1' : c₃.nreg 6525 = c.nmem (NHb + i) := by rw [n3 _ (by omega) (by omega),
    n2 _ (by omega) (by omega), v1]
  rw [m2, m1] at v3
  obtain ⟨c₄, k₄, e₄, hk₄, v4, n4, m4, rr4, rm4, o4⟩ := ld2_exec (P := P) (t := 6524) (r := 6528)
    (b := 6543) (ctr := 6520) c₃ e₃.wb_right (by rw [q3 _ (by unfold vscr; omega), r43])
    (by rw [q3 _ (by unfold vscr; omega), r20]) w4 (by omega) (by omega)
  have q4 : ∀ x, ¬ vscr x → c₄.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; rw [n4 x (by omega) (by omega), q3 x (by unfold vscr; omega)]
  rw [m3, m2, m1] at v4
  have v1'' : c₄.nreg 6525 = c.nmem (NHb + i) := by rw [n4 _ (by omega) (by omega), v1']
  have v3' : c₄.nreg 6527 = c.nmem (NHb + c.nmem (RVb + i)) := by
    rw [n4 _ (by omega) (by omega), v3]
  have z4 : c₄.nreg 6539 = 0 := by rw [q4 _ (by unfold vscr; omega), r39]
  unfold vbLd
  by_cases h1 : 0 < c.nmem (NHb + i)
  · obtain ⟨c₅, k₅, e₅, hk₅, v5, n5, m5, rr5, rm5, o5⟩ := cpy_exec (P := P) (r := 6529)
      (a := 6527) c₄ e₄.wb_right
    refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.ifLtN_true (by rw [z4, v1'']; exact h1)
      e₅)))), by omega, by rw [n5 _ (by omega), v4], by rw [v5, v3']; simp [inF, h1],
      fun x hx => ?_, by rw [m5, m4, m3, m2, m1], by rw [rr5, rr4, rr3, rr2, rr1],
      by rw [rm5, rm4, rm3, rm2, rm1], by rw [o5, o4, o3, o2, o1]⟩
    rw [n5 x (by unfold vscr at hx; omega), q4 x hx]
  · obtain ⟨c₅, k₅, e₅, hk₅, v5, n5, m5, rr5, rm5, o5⟩ := cst_exec (P := P) (r := 6529)
      (v := 0) c₄ e₄.wb_right (Nat.zero_le _)
    refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.ifLtN_false (by rw [z4, v1'']; exact h1)
      e₅)))), by omega, by rw [n5 _ (by omega), v4], by rw [v5]; simp [inF, h1],
      fun x hx => ?_, by rw [m5, m4, m3, m2, m1], by rw [rr5, rr4, rr3, rr2, rr1],
      by rw [rm5, rm4, rm3, rm2, rm1], by rw [o5, o4, o3, o2, o1]⟩
    rw [n5 x (by unfold vscr at hx; omega), q4 x hx]

/-- **The value block `vbFLl`.** -/
theorem vbFLl_exec (c : Config) (hc : WordsBounded W c) {i LPb NHb RVb : ℕ}
    (r20 : c.nreg 6520 = i) (r21 : c.nreg 6521 = 1) (r39 : c.nreg 6539 = 0)
    (r43 : c.nreg 6543 = LPb) (r44 : c.nreg 6544 = NHb) (r45 : c.nreg 6545 = RVb)
    (w1 : NHb + i ≤ W) (w2 : RVb + i ≤ W) (w3 : NHb + c.nmem (RVb + i) ≤ W) (w4 : LPb + i ≤ W) :
    ∃ c' k, Exec P W vbFLl c c' k ∧ k ≤ 16 ∧
      c'.nreg 6523 = flL (c.nmem (LPb + i)) (c.nmem (NHb + i)) (c.nmem (NHb + c.nmem (RVb + i))) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hW1 : 1 ≤ W := r21 ▸ hc.1 6521
  obtain ⟨c₁, k₁, e₁, hk₁, v8, v9, n1, m1, rr1, rm1, o1⟩ := vbLd_exec (P := P) c hc r20 r39 r43
    r44 r45 w1 w2 w3 w4
  have z1 : c₁.nreg 6539 = 0 := by rw [n1 _ (by unfold vscr; omega), r39]
  have u1 : c₁.nreg 6521 = 1 := by rw [n1 _ (by unfold vscr; omega), r21]
  unfold vbFLl
  by_cases h1 : 0 < c.nmem (LPb + i)
  · by_cases h2 : inF (c.nmem (NHb + i)) (c.nmem (NHb + c.nmem (RVb + i))) < 1
    · obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := cst_exec (P := P) (r := 6523)
        (v := 1) c₁ e₁.wb_right hW1
      refine ⟨c₂, _, .seq e₁ (.ifLtN_true (by rw [z1, v8]; exact h1)
        (.ifLtN_true (by rw [u1, v9]; exact h2) e₂)), by omega, by rw [v2]; simp [flL, h1, h2],
        fun x hx => ?_, by rw [m2, m1], by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
      rw [n2 x (by unfold vscr at hx; omega), n1 x hx]
    · obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := cst_exec (P := P) (r := 6523)
        (v := 0) c₁ e₁.wb_right (Nat.zero_le _)
      refine ⟨c₂, _, .seq e₁ (.ifLtN_true (by rw [z1, v8]; exact h1)
        (.ifLtN_false (by rw [u1, v9]; exact h2) e₂)), by omega, by rw [v2]; simp [flL, h1, h2],
        fun x hx => ?_, by rw [m2, m1], by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
      rw [n2 x (by unfold vscr at hx; omega), n1 x hx]
  · obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := cst_exec (P := P) (r := 6523)
      (v := 0) c₁ e₁.wb_right (Nat.zero_le _)
    refine ⟨c₂, _, .seq e₁ (.ifLtN_false (by rw [z1, v8]; exact h1) e₂), by omega,
      by rw [v2]; simp [flL, h1], fun x hx => ?_, by rw [m2, m1], by rw [rr2, rr1],
      by rw [rm2, rm1], by rw [o2, o1]⟩
    rw [n2 x (by unfold vscr at hx; omega), n1 x hx]

/-- **The value block `vbFLr`.** -/
theorem vbFLr_exec (c : Config) (hc : WordsBounded W c) {i LPb NHb RVb : ℕ}
    (r20 : c.nreg 6520 = i) (r21 : c.nreg 6521 = 1) (r39 : c.nreg 6539 = 0)
    (r43 : c.nreg 6543 = LPb) (r44 : c.nreg 6544 = NHb) (r45 : c.nreg 6545 = RVb)
    (w1 : NHb + i ≤ W) (w2 : RVb + i ≤ W) (w3 : NHb + c.nmem (RVb + i) ≤ W) (w4 : LPb + i ≤ W) :
    ∃ c' k, Exec P W vbFLr c c' k ∧ k ≤ 16 ∧
      c'.nreg 6523 = flR (c.nmem (LPb + i)) (c.nmem (NHb + i)) (c.nmem (NHb + c.nmem (RVb + i))) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hW1 : 1 ≤ W := r21 ▸ hc.1 6521
  obtain ⟨c₁, k₁, e₁, hk₁, v8, v9, n1, m1, rr1, rm1, o1⟩ := vbLd_exec (P := P) c hc r20 r39 r43
    r44 r45 w1 w2 w3 w4
  have z1 : c₁.nreg 6539 = 0 := by rw [n1 _ (by unfold vscr; omega), r39]
  have u1 : c₁.nreg 6521 = 1 := by rw [n1 _ (by unfold vscr; omega), r21]
  unfold vbFLr
  by_cases h1 : 0 < c.nmem (LPb + i)
  · obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := cst_exec (P := P) (r := 6523)
      (v := 0) c₁ e₁.wb_right (Nat.zero_le _)
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true (by rw [z1, v8]; exact h1) e₂), by omega,
      by rw [v2]; simp [flR, h1], fun x hx => ?_, by rw [m2, m1], by rw [rr2, rr1],
      by rw [rm2, rm1], by rw [o2, o1]⟩
    rw [n2 x (by unfold vscr at hx; omega), n1 x hx]
  · by_cases h2 : inF (c.nmem (NHb + i)) (c.nmem (NHb + c.nmem (RVb + i))) < 1
    · obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := cst_exec (P := P) (r := 6523)
        (v := 1) c₁ e₁.wb_right hW1
      refine ⟨c₂, _, .seq e₁ (.ifLtN_false (by rw [z1, v8]; exact h1)
        (.ifLtN_true (by rw [u1, v9]; exact h2) e₂)), by omega, by rw [v2]; simp [flR, h1, h2],
        fun x hx => ?_, by rw [m2, m1], by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
      rw [n2 x (by unfold vscr at hx; omega), n1 x hx]
    · obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := cst_exec (P := P) (r := 6523)
        (v := 0) c₁ e₁.wb_right (Nat.zero_le _)
      refine ⟨c₂, _, .seq e₁ (.ifLtN_false (by rw [z1, v8]; exact h1)
        (.ifLtN_false (by rw [u1, v9]; exact h2) e₂)), by omega, by rw [v2]; simp [flR, h1, h2],
        fun x hx => ?_, by rw [m2, m1], by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
      rw [n2 x (by unfold vscr at hx; omega), n1 x hx]

/-- **The value block `vbKC`.** -/
theorem vbKC_exec (c : Config) (hc : WordsBounded W c) {i NHb KRb : ℕ}
    (r20 : c.nreg 6520 = i) (r21 : c.nreg 6521 = 1) (r39 : c.nreg 6539 = 0)
    (r44 : c.nreg 6544 = NHb) (r46 : c.nreg 6546 = KRb) (w1 : NHb + i ≤ W) (w2 : KRb + i ≤ W) :
    ∃ c' k, Exec P W vbKC c c' k ∧ k ≤ 7 ∧
      c'.nreg 6523 = kcF (c.nmem (NHb + i)) (c.nmem (KRb + i)) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hW1 : 1 ≤ W := r21 ▸ hc.1 6521
  obtain ⟨c₁, k₁, e₁, hk₁, v1, n1, m1, rr1, rm1, o1⟩ := ld2_exec (P := P) (t := 6524) (r := 6525)
    (b := 6544) (ctr := 6520) c hc r44 r20 w1 (by omega) (by omega)
  have q1 : ∀ x, ¬ vscr x → c₁.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; exact n1 x (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := ld2_exec (P := P) (t := 6524) (r := 6526)
    (b := 6546) (ctr := 6520) c₁ e₁.wb_right (by rw [q1 _ (by unfold vscr; omega), r46])
    (by rw [q1 _ (by unfold vscr; omega), r20]) w2 (by omega) (by omega)
  have q2 : ∀ x, ¬ vscr x → c₂.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; rw [n2 x (by omega) (by omega), q1 x (by unfold vscr; omega)]
  rw [m1] at v2
  have v1' : c₂.nreg 6525 = c.nmem (NHb + i) := by rw [n2 _ (by omega) (by omega), v1]
  have z2 : c₂.nreg 6539 = 0 := by rw [q2 _ (by unfold vscr; omega), r39]
  unfold vbKC
  by_cases h1 : 0 < c.nmem (NHb + i)
  · obtain ⟨c₃, k₃, e₃, hk₃, v3, n3, m3, rr3, rm3, o3⟩ := cst_exec (P := P) (r := 6523) (v := 1)
      c₂ e₂.wb_right hW1
    refine ⟨c₃, _, .seq e₁ (.seq e₂ (.ifLtN_true (by rw [z2, v1']; exact h1) e₃)), by omega,
      by rw [v3]; simp [kcF, h1], fun x hx => ?_, by rw [m3, m2, m1], by rw [rr3, rr2, rr1],
      by rw [rm3, rm2, rm1], by rw [o3, o2, o1]⟩
    rw [n3 x (by unfold vscr at hx; omega), q2 x hx]
  · obtain ⟨c₃, k₃, e₃, hk₃, v3, n3, m3, rr3, rm3, o3⟩ := cpy_exec (P := P) (r := 6523)
      (a := 6526) c₂ e₂.wb_right
    refine ⟨c₃, _, .seq e₁ (.seq e₂ (.ifLtN_false (by rw [z2, v1']; exact h1) e₃)), by omega,
      by rw [v3, v2]; simp [kcF, h1], fun x hx => ?_, by rw [m3, m2, m1], by rw [rr3, rr2, rr1],
      by rw [rm3, rm2, rm1], by rw [o3, o2, o1]⟩
    rw [n3 x (by unfold vscr at hx; omega), q2 x hx]

/-- The tail of `vbHC`: `r6523 := HCI[hl - 1] + 1`. -/
theorem vbHCI_exec (c : Config) (hc : WordsBounded W c) {HCIb hl : ℕ} (r21 : c.nreg 6521 = 1)
    (r26 : c.nreg 6526 = hl) (r47 : c.nreg 6547 = HCIb) (hl1 : 0 < hl)
    (w : HCIb + (hl - 1) ≤ W) (w' : c.nmem (HCIb + (hl - 1)) + 1 ≤ W) :
    ∃ c' k, Exec P W (block [.subN 6526 6526 6521, .addN 6524 6547 6526, .loadN 6527 6524,
      .addN 6523 6527 6521]) c c' k ∧ k = 4 ∧ c'.nreg 6523 = c.nmem (HCIb + (hl - 1)) + 1 ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hc.1 6526
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r21, r26, r47]; omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp (disch := omega) only [upd_other, upd_same, r21, r26, r47]
  · unfold vscr at hx
    config_simp; simp (disch := omega) only [upd_other, upd_same]

/-- **The value block `vbHC`.** -/
theorem vbHC_exec (c : Config) (hc : WordsBounded W c) {i NHb HLb HCIb : ℕ}
    (r20 : c.nreg 6520 = i) (r21 : c.nreg 6521 = 1) (r39 : c.nreg 6539 = 0)
    (r44 : c.nreg 6544 = NHb) (r41 : c.nreg 6541 = HLb) (r47 : c.nreg 6547 = HCIb)
    (w1 : NHb + i ≤ W) (w2 : HLb + i ≤ W)
    (w3 : ¬ 0 < c.nmem (NHb + i) → 0 < c.nmem (HLb + i) → HCIb + (c.nmem (HLb + i) - 1) ≤ W ∧
      c.nmem (HCIb + (c.nmem (HLb + i) - 1)) + 1 ≤ W) :
    ∃ c' k, Exec P W vbHC c c' k ∧ k ≤ 11 ∧
      c'.nreg 6523 = hcF (c.nmem (NHb + i)) (c.nmem (HLb + i))
        (c.nmem (HCIb + (c.nmem (HLb + i) - 1))) (c.nreg 6548) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v1, n1, m1, rr1, rm1, o1⟩ := ld2_exec (P := P) (t := 6524) (r := 6525)
    (b := 6544) (ctr := 6520) c hc r44 r20 w1 (by omega) (by omega)
  have q1 : ∀ x, ¬ vscr x → c₁.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; exact n1 x (by omega) (by omega)
  have z1 : c₁.nreg 6539 = 0 := by rw [q1 _ (by unfold vscr; omega), r39]
  unfold vbHC
  by_cases h1 : 0 < c.nmem (NHb + i)
  · obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := cpy_exec (P := P) (r := 6523)
      (a := 6548) c₁ e₁.wb_right
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true (by rw [z1, v1]; exact h1) e₂), by omega,
      by rw [v2, q1 _ (by unfold vscr; omega)]; simp [hcF, h1], fun x hx => ?_, by rw [m2, m1],
      by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
    rw [n2 x (by unfold vscr at hx; omega), q1 x hx]
  · obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := ld2_exec (P := P) (t := 6524)
      (r := 6526) (b := 6541) (ctr := 6520) c₁ e₁.wb_right
      (by rw [q1 _ (by unfold vscr; omega), r41]) (by rw [q1 _ (by unfold vscr; omega), r20]) w2
      (by omega) (by omega)
    have q2 : ∀ x, ¬ vscr x → c₂.nreg x = c.nreg x := fun x hx => by
      unfold vscr at hx; rw [n2 x (by omega) (by omega), q1 x (by unfold vscr; omega)]
    have z2 : c₂.nreg 6539 = 0 := by rw [q2 _ (by unfold vscr; omega), r39]
    rw [m1] at v2
    by_cases h2 : 0 < c.nmem (HLb + i)
    · obtain ⟨w3a, w3b⟩ := w3 h1 h2
      obtain ⟨c₃, k₃, e₃, hk₃, v3, n3, m3, rr3, rm3, o3⟩ := vbHCI_exec (P := P) c₂ e₂.wb_right
        (by rw [q2 _ (by unfold vscr; omega), r21]) v2
        (by rw [q2 _ (by unfold vscr; omega), r47]) h2 w3a (by rw [m2, m1]; exact w3b)
      refine ⟨c₃, _, .seq e₁ (.ifLtN_false (by rw [z1, v1]; exact h1)
        (.seq e₂ (.ifLtN_true (by rw [z2, v2]; exact h2) e₃))), by omega, ?_, fun x hx => ?_,
        by rw [m3, m2, m1], by rw [rr3, rr2, rr1], by rw [rm3, rm2, rm1], by rw [o3, o2, o1]⟩
      · rw [v3, m2, m1]; simp [hcF, h1, h2]
      · rw [n3 x hx, q2 x hx]
    · obtain ⟨c₃, k₃, e₃, hk₃, v3, n3, m3, rr3, rm3, o3⟩ := cst_exec (P := P) (r := 6523) (v := 0)
        c₂ e₂.wb_right (Nat.zero_le _)
      refine ⟨c₃, _, .seq e₁ (.ifLtN_false (by rw [z1, v1]; exact h1)
        (.seq e₂ (.ifLtN_false (by rw [z2, v2]; exact h2) e₃))), by omega, ?_, fun x hx => ?_,
        by rw [m3, m2, m1], by rw [rr3, rr2, rr1], by rw [rm3, rm2, rm1], by rw [o3, o2, o1]⟩
      · rw [v3]; simp [hcF, h1, h2]
      · rw [n3 x (by unfold vscr at hx; omega), q2 x hx]

/-- **The value block `vbID`.** -/
theorem vbID_exec (c : Config) (hc : WordsBounded W c) {i : ℕ} (r20 : c.nreg 6520 = i) :
    ∃ c' k, Exec P W vbID c c' k ∧ k ≤ 1 ∧ c'.nreg 6523 = i ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v1, n1, m1, rr1, rm1, o1⟩ := cpy_exec (P := P) (r := 6523) (a := 6520)
    c hc
  exact ⟨c₁, k₁, e₁, by omega, by rw [v1, r20], fun x hx => n1 x (by unfold vscr at hx; omega),
    m1, rr1, rm1, o1⟩

lemma cnt_ext {F G : ℕ → ℕ} {n : ℕ} (h : ∀ j < n, F j = G j) : cnt F n = cnt G n := by
  unfold cnt; congr 1
  apply Finset.filter_congr; intro j hj; rw [Finset.mem_range] at hj; rw [h j hj]

/-- A map loop with its counter reset first. -/
def mapRunS (vb : Stmt) (bnd ob : ℕ) : Stmt :=
  .seq (block [.constN 6520 0]) (mapProg vb 6520 bnd 6521 ob 6522 6523)

/-- **A map loop of the value blocks** (counter `6520`, `6521 = 1`, store `6522`, value
`6523`, scratch `vscr`), its counter reset first: `(B + 5) m + 3` steps. -/
theorem mapRun_exec (c : Config) (hc : WordsBounded W c) {vb : Stmt} {bnd ob m Ob B : ℕ}
    (g : ℕ → ℕ) (r1 : c.nreg bnd = m) (r2 : c.nreg 6521 = 1) (r3 : c.nreg ob = Ob)
    (w1 : Ob + m ≤ W) (w2 : m + 1 ≤ W) (s2 : ¬ vscr bnd) (s4 : ¬ vscr ob) (h6 : 6522 ≠ bnd)
    (h7 : 6520 ≠ bnd) (h8 : ob ≠ 6520) (h3 : 6522 ≠ ob)
    (hvb : ∀ i < m, ∀ c' : Config, WordsBounded W c' → c'.nreg 6520 = i →
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) →
      (∀ a, ¬ (Ob ≤ a ∧ a < Ob + m) → c'.nmem a = c.nmem a) →
      ∃ c'' k, Exec P W vb c' c'' k ∧ k ≤ B ∧ c''.nreg 6523 = g i ∧
        (∀ x, ¬ vscr x → c''.nreg x = c'.nreg x) ∧ c''.nmem = c'.nmem ∧
        c''.rreg = c'.rreg ∧ c''.rmem = c'.rmem ∧ c''.output = c'.output) :
    ∃ c' t, Exec P W (mapRunS vb bnd ob) c c' t ∧ t ≤ (B + 5) * m + 3 ∧
      (∀ j < m, c'.nmem (Ob + j) = g j) ∧
      (∀ a, ¬ (Ob ≤ a ∧ a < Ob + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v1, n1, m1, rr1, rm1, o1⟩ := cst_exec (P := P) (r := 6520) (v := 0)
    c hc (Nat.zero_le _)
  obtain ⟨c₂, k₂, e₂, hk₂, h20, j1, j2, j3, j4, j5, j6⟩ := mapProg_exec (P := P) c₁ e₁.wb_right
    (vb := vb) (ctr := 6520) (bnd := bnd) (one := 6521) (ob := ob) (t := 6522) (v := 6523)
    (m := m) (Ob := Ob) (B := B) vscr g v1 (by rw [n1 _ (Ne.symm h7)]; exact r1)
    (by rw [n1 _ (by omega)]; exact r2)
    (by rw [n1 _ h8]; exact r3) w1 w2 (by unfold vscr; omega) s2 (by unfold vscr; omega) s4
    (by omega) (by omega) h3 (by omega) (by omega) h6 h7 h8
    (fun i hi c' hw h20 hr hm => hvb i hi c' hw h20 (fun x hx h1 h2 => by
      rw [hr x hx h1 h2, n1 x h2]) (fun a ha => by rw [hm a ha, m1]))
  refine ⟨c₂, _, .seq e₁ e₂, by omega, j1, fun a ha => by rw [j2 a ha, m1],
    fun x hx h1 h2 => by rw [j3 x hx h1 h2, n1 x h2], by rw [j4, rr1], by rw [j5, rm1],
    by rw [j6, o1]⟩

/-- The first half of the flags: `NH`, `HF`, the compaction of the kept holes, `r6548 = nd + 1`. -/
def sfFlagsA : Stmt :=
  .seq (mapRunS vbNH 6510 6544) (.seq (mapRunS vbHF 6511 6536)
    (.seq (block [.copyN 6300 6511, .copyN 6301 6536, .copyN 6302 6547, .copyN 6303 6537])
      (.seq lkProg (block [.addN 6548 6306 6521]))))

/-- The second half: `HC`, `FLl`, `FLr`, `KC`, `ID`. -/
def sfFlagsB : Stmt :=
  .seq (mapRunS vbHC 6510 6534) (.seq (mapRunS vbFLl 6510 6531) (.seq (mapRunS vbFLr 6510 6532)
    (.seq (mapRunS vbKC 6510 6533) (mapRunS vbID 6510 6535))))

set_option maxHeartbeats 1000000 in
/-- **The first half of the flags.** -/
theorem sfFlagsA_exec (c : Config) (hc : WordsBounded W c) {m k Wb CVb HLb HMb : ℕ}
    (r10 : c.nreg 6510 = m) (r11 : c.nreg 6511 = k) (r21 : c.nreg 6521 = 1)
    (r39 : c.nreg 6539 = 0) (r40 : c.nreg 6540 = CVb) (r41 : c.nreg 6541 = HLb)
    (r42 : c.nreg 6542 = HMb) (r44 : c.nreg 6544 = Wb) (r36 : c.nreg 6536 = Wb + 7 * m)
    (r47 : c.nreg 6547 = Wb + 7 * m + k) (r37 : c.nreg 6537 = Wb + 7 * m + 2 * k)
    (o1 : CVb + m ≤ Wb) (o2 : HLb + m ≤ Wb) (o3 : HMb + k ≤ Wb) (w : Wb + 7 * m + 3 * k ≤ W)
    (w' : m + k + 2 ≤ W) (hHL : ∀ i < m, c.nmem (HLb + i) ≤ k) :
    ∃ c' t, Exec P W sfFlagsA c c' t ∧ t ≤ 15 * m + 21 * k + 17 ∧
      (∀ i < m, c'.nmem (Wb + i) = nhF (c.nmem (CVb + i)) (c.nmem (HLb + i))
        (c.nmem (HMb + (c.nmem (HLb + i) - 1)))) ∧
      (∀ j < k, c'.nmem (Wb + 7 * m + j) = hfF (c.nmem (HMb + j))) ∧
      c'.nreg 6548 = cnt (fun j => hfF (c.nmem (HMb + j))) k + 1 ∧
      (∀ j < k, 0 < hfF (c.nmem (HMb + j)) →
        c'.nmem (Wb + 7 * m + k + j) = cnt (fun j => hfF (c.nmem (HMb + j))) j) ∧
      (∀ a, (a < Wb ∨ (Wb + m ≤ a ∧ a < Wb + 7 * m) ∨ Wb + 7 * m + 3 * k ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6300 ∨ (6309 < x ∧ x < 6520) ∨ x = 6521 ∨ (6529 < x ∧ x ≠ 6548)) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- NH
  obtain ⟨c₁, k₁, e₁, hk₁, a1, m1, n1, rr1, rm1, o1'⟩ := mapRun_exec (P := P) c hc (vb := vbNH)
    (bnd := 6510) (ob := 6544) (m := m) (Ob := Wb) (B := 10)
    (fun i => nhF (c.nmem (CVb + i)) (c.nmem (HLb + i)) (c.nmem (HMb + (c.nmem (HLb + i) - 1))))
    r10 r21 r44 (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega)
    (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      have e1 : c'.nmem (CVb + i) = c.nmem (CVb + i) := hm _ (by omega)
      have e2 : c'.nmem (HLb + i) = c.nmem (HLb + i) := hm _ (by omega)
      have hl := hHL i hi
      obtain ⟨c'', t, ex, ht, v, n, mm, rr, rm, oo⟩ := vbNH_exec (P := P) c' hw h20
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega), r21])
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega), r39])
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega), r40])
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega), r41])
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega), r42]) (by omega) (by omega)
        (fun _ => by rw [e2]; omega)
      refine ⟨c'', t, ex, ht, ?_, n, mm, rr, rm, oo⟩
      rw [v, e1, e2]
      by_cases h : 0 < c.nmem (HLb + i)
      · rw [hm _ (by omega)]
      · have : c.nmem (HLb + i) = 0 := by omega
        simp [nhF, this])
  have q1 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₁.nreg x = c.nreg x := n1
  -- HF
  obtain ⟨c₂, k₂, e₂, hk₂, a2, m2, n2, rr2, rm2, o2'⟩ := mapRun_exec (P := P) c₁ e₁.wb_right
    (vb := vbHF) (bnd := 6511) (ob := 6536) (m := k) (Ob := Wb + 7 * m) (B := 5)
    (fun j => hfF (c.nmem (HMb + j)))
    (by rw [q1 _ (by unfold vscr; omega) (by omega) (by omega), r11])
    (by rw [q1 _ (by unfold vscr; omega) (by omega) (by omega), r21])
    (by rw [q1 _ (by unfold vscr; omega) (by omega) (by omega), r36]) (by omega) (by omega)
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun j hj c' hw h20 hr hm => by
      have e1 : c'.nmem (HMb + j) = c.nmem (HMb + j) := by
        rw [hm _ (by omega), m1 _ (by omega)]
      obtain ⟨c'', t, ex, ht, v, n, mm, rr, rm, oo⟩ := vbHF_exec (P := P) c' hw h20
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega),
          q1 _ (by unfold vscr; omega) (by omega) (by omega), r21])
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega),
          q1 _ (by unfold vscr; omega) (by omega) (by omega), r39])
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega),
          q1 _ (by unfold vscr; omega) (by omega) (by omega), r42]) (by omega)
      exact ⟨c'', t, ex, ht, by rw [v, e1], n, mm, rr, rm, oo⟩)
  have q2 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₂.nreg x = c.nreg x := fun x h1 h2 h3 => by
    rw [n2 x h1 h2 h3, q1 x h1 h2 h3]
  -- the compaction
  obtain ⟨c₃, k₃, e₃, hk₃, s0, s1, s2, s3, n3, m3, rr3, rm3, o3'⟩ : ∃ c₃ k₃,
      Exec P W (block [.copyN 6300 6511, .copyN 6301 6536, .copyN 6302 6547, .copyN 6303 6537])
        c₂ c₃ k₃ ∧ k₃ = 4 ∧ c₃.nreg 6300 = k ∧ c₃.nreg 6301 = Wb + 7 * m ∧
      c₃.nreg 6302 = Wb + 7 * m + k ∧ c₃.nreg 6303 = Wb + 7 * m + 2 * k ∧
      (∀ x, (x < 6300 ∨ 6303 < x) → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have t1 : c₂.nreg 6511 = k := by rw [q2 _ (by unfold vscr; omega) (by omega) (by omega), r11]
    have t2 : c₂.nreg 6536 = Wb + 7 * m := by
      rw [q2 _ (by unfold vscr; omega) (by omega) (by omega), r36]
    have t3 : c₂.nreg 6547 = Wb + 7 * m + k := by
      rw [q2 _ (by unfold vscr; omega) (by omega) (by omega), r47]
    have t4 : c₂.nreg 6537 = Wb + 7 * m + 2 * k := by
      rw [q2 _ (by unfold vscr; omega) (by omega) (by omega), r37]
    have hw := e₂.wb_right
    exec_block
    all_goals try omega
    all_goals
      try (config_simp; simp (disch := omega) only [upd_other, upd_same, t1, t2, t3, t4]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same, t1, t2, t3, t4])
      try omega
  rw [← m3] at a2
  obtain ⟨c₄, k₄, e₄, hk₄, l6, l1, l2, n4, rr4, rm4, o4'⟩ := lkProg_exec (P := P) c₃ e₃.wb_right
    s0 s1 s2 s3 (by omega) (by omega) (by omega) (by omega)
  have hcF : ∀ i ≤ k, cnt (fun j => c₃.nmem (Wb + 7 * m + j)) i =
      cnt (fun j => hfF (c.nmem (HMb + j))) i := fun i hi => cnt_ext fun j hj => a2 j (by omega)
  have q4 : ∀ x, (x < 6304 ∨ 6309 < x) → c₄.nreg x = c₃.nreg x := n4
  -- `r6548 := nd + 1`
  obtain ⟨c₅, k₅, e₅, hk₅, v48, n5, m5, rr5, rm5, o5'⟩ : ∃ c₅ k₅,
      Exec P W (block [.addN 6548 6306 6521]) c₄ c₅ k₅ ∧ k₅ = 1 ∧
      c₅.nreg 6548 = c₄.nreg 6306 + 1 ∧ (∀ x, x ≠ 6548 → c₅.nreg x = c₄.nreg x) ∧
      c₅.nmem = c₄.nmem ∧ c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    have t1 : c₄.nreg 6521 = 1 := by
      rw [q4 _ (by omega), n3 _ (by omega), q2 _ (by unfold vscr; omega) (by omega) (by omega),
        r21]
    have t6 : c₄.nreg 6306 ≤ k := by
      rw [l6]; exact (cnt_le _ _)
    have hw := e₄.wb_right
    exec_block
    all_goals try omega
    all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, t1]; omega)
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same, t1])
      try omega
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega, fun i hi => ?_,
    fun j hj => ?_, by rw [v48, l6, hcF k le_rfl], fun j hj hf => ?_, fun a ha => ?_,
    fun x hx => ?_, by rw [rr5, rr4, rr3, rr2, rr1], by rw [rm5, rm4, rm3, rm2, rm1],
    by rw [o5', o4', o3', o2', o1']⟩
  · rw [m5, l2 _ (by omega), m3, m2 _ (by omega)]; exact a1 i hi
  · rw [m5, l2 _ (by omega)]; exact a2 j hj
  · rw [m5, ← hcF j hj.le]
    exact (l1 j hj (by rw [a2 j hj]; exact hf)).1
  · rw [m5, l2 _ (by omega), m3, m2 _ (by omega), m1 _ (by omega)]
  · rw [n5 x (by omega), q4 x (by omega), n3 x (by omega),
      q2 x (by unfold vscr; omega) (by omega) (by omega)]

set_option maxHeartbeats 1000000 in
/-- **The second half of the flags.** -/
theorem sfFlagsB_exec (c : Config) (hc : WordsBounded W c) {m k Wb HLb LPb RVb KRb nd1 : ℕ}
    (r10 : c.nreg 6510 = m) (r21 : c.nreg 6521 = 1) (r39 : c.nreg 6539 = 0)
    (r41 : c.nreg 6541 = HLb) (r43 : c.nreg 6543 = LPb) (r44 : c.nreg 6544 = Wb)
    (r45 : c.nreg 6545 = RVb) (r46 : c.nreg 6546 = KRb) (r47 : c.nreg 6547 = Wb + 7 * m + k)
    (r48 : c.nreg 6548 = nd1) (r31 : c.nreg 6531 = Wb + m) (r32 : c.nreg 6532 = Wb + 2 * m)
    (r33 : c.nreg 6533 = Wb + 3 * m) (r34 : c.nreg 6534 = Wb + 4 * m)
    (r35 : c.nreg 6535 = Wb + 5 * m)
    (o1 : HLb + m ≤ Wb) (o2 : LPb + m ≤ Wb) (o3 : RVb + m ≤ Wb) (o4 : KRb + m ≤ Wb)
    (w : Wb + 7 * m + 3 * k ≤ W) (w' : m + 2 ≤ W)
    (hrv : ∀ i < m, c.nmem (RVb + i) < m) (hHL : ∀ i < m, c.nmem (HLb + i) ≤ k)
    (hci : ∀ i < m, ¬ 0 < c.nmem (Wb + i) → 0 < c.nmem (HLb + i) →
      c.nmem (Wb + 7 * m + k + (c.nmem (HLb + i) - 1)) + 1 ≤ W) :
    ∃ c' t, Exec P W sfFlagsB c c' t ∧ t ≤ 76 * m + 15 ∧
      (∀ i < m, c'.nmem (Wb + 4 * m + i) = hcF (c.nmem (Wb + i)) (c.nmem (HLb + i))
        (c.nmem (Wb + 7 * m + k + (c.nmem (HLb + i) - 1))) nd1) ∧
      (∀ i < m, c'.nmem (Wb + m + i) = flL (c.nmem (LPb + i)) (c.nmem (Wb + i))
        (c.nmem (Wb + c.nmem (RVb + i)))) ∧
      (∀ i < m, c'.nmem (Wb + 2 * m + i) = flR (c.nmem (LPb + i)) (c.nmem (Wb + i))
        (c.nmem (Wb + c.nmem (RVb + i)))) ∧
      (∀ i < m, c'.nmem (Wb + 3 * m + i) = kcF (c.nmem (Wb + i)) (c.nmem (KRb + i))) ∧
      (∀ i < m, c'.nmem (Wb + 5 * m + i) = i) ∧
      (∀ a, ¬ (Wb + m ≤ a ∧ a < Wb + 6 * m) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have R : ∀ (c' : Config) (x : ℕ), (∀ y, ¬ vscr y → y ≠ 6522 → y ≠ 6520 → c'.nreg y = c.nreg y) →
      (x < 6520 ∨ x = 6521 ∨ 6529 < x) → c'.nreg x = c.nreg x := fun c' x h hx =>
    h x (by unfold vscr; omega) (by omega) (by omega)
  -- HC
  obtain ⟨c₁, k₁, e₁, hk₁, a1, m1, n1, rr1, rm1, o1'⟩ := mapRun_exec (P := P) c hc (vb := vbHC)
    (bnd := 6510) (ob := 6534) (m := m) (Ob := Wb + 4 * m) (B := 11)
    (fun i => hcF (c.nmem (Wb + i)) (c.nmem (HLb + i))
        (c.nmem (Wb + 7 * m + k + (c.nmem (HLb + i) - 1))) nd1)
    r10 r21 r34 (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega)
    (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      have e1 : c'.nmem (Wb + i) = c.nmem (Wb + i) := hm _ (by omega)
      have e2 : c'.nmem (HLb + i) = c.nmem (HLb + i) := hm _ (by omega)
      have hl := hHL i hi
      obtain ⟨c'', t, ex, ht, v, n, mm, rr, rm, oo⟩ := vbHC_exec (P := P) c' hw h20
        (by rw [R c' 6521 hr (by omega), r21]) (by rw [R c' 6539 hr (by omega), r39])
        (by rw [R c' 6544 hr (by omega), r44]) (by rw [R c' 6541 hr (by omega), r41])
        (by rw [R c' 6547 hr (by omega), r47]) (by omega) (by omega)
        (fun h1 h2 => by
          rw [e1] at h1; rw [e2] at h2 ⊢
          refine ⟨by omega, ?_⟩
          rw [hm _ (by omega)]; exact hci i hi h1 h2)
      refine ⟨c'', t, ex, ht, ?_, n, mm, rr, rm, oo⟩
      rw [v, e1, e2, R c' 6548 hr (by omega), r48]
      by_cases h : 0 < c.nmem (HLb + i)
      · rw [hm _ (by omega)]
      · have : c.nmem (HLb + i) = 0 := by omega
        simp [hcF, this])
  -- FLl
  obtain ⟨c₂, k₂, e₂, hk₂, a2, m2, n2, rr2, rm2, o2'⟩ := mapRun_exec (P := P) c₁ e₁.wb_right
    (vb := vbFLl) (bnd := 6510) (ob := 6531) (m := m) (Ob := Wb + m) (B := 16)
    (fun i => flL (c.nmem (LPb + i)) (c.nmem (Wb + i)) (c.nmem (Wb + c.nmem (RVb + i))))
    (by rw [R c₁ 6510 n1 (by omega), r10]) (by rw [R c₁ 6521 n1 (by omega), r21])
    (by rw [R c₁ 6531 n1 (by omega), r31]) (by omega) (by omega) (by unfold vscr; omega)
    (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      have hr' := hrv i hi
      have e1 : c'.nmem (LPb + i) = c.nmem (LPb + i) := by rw [hm _ (by omega), m1 _ (by omega)]
      have e2 : c'.nmem (Wb + i) = c.nmem (Wb + i) := by rw [hm _ (by omega), m1 _ (by omega)]
      have e3 : c'.nmem (RVb + i) = c.nmem (RVb + i) := by rw [hm _ (by omega), m1 _ (by omega)]
      have e4 : c'.nmem (Wb + c.nmem (RVb + i)) = c.nmem (Wb + c.nmem (RVb + i)) := by
        rw [hm _ (by omega), m1 _ (by omega)]
      have Q : ∀ x, (x < 6520 ∨ x = 6521 ∨ 6529 < x) → c'.nreg x = c.nreg x := fun x hx => by
        rw [R c' x (fun y h1 h2 h3 => by rw [hr y h1 h2 h3, n1 y h1 h2 h3]) hx]
      obtain ⟨c'', t, ex, ht, v, n, mm, rr, rm, oo⟩ := vbFLl_exec (P := P) c' hw h20
        (by rw [Q 6521 (by omega), r21]) (by rw [Q 6539 (by omega), r39]) (by rw [Q 6543 (by omega), r43])
        (by rw [Q 6544 (by omega), r44]) (by rw [Q 6545 (by omega), r45]) (by omega) (by omega)
        (by rw [e3]; omega) (by omega)
      exact ⟨c'', t, ex, ht, by rw [v, e3, e1, e2, e4], n, mm, rr, rm, oo⟩)
  have Q2 : ∀ x, (x < 6520 ∨ x = 6521 ∨ 6529 < x) → c₂.nreg x = c.nreg x := fun x hx => by
    rw [R c₂ x (fun y h1 h2 h3 => by rw [n2 y h1 h2 h3, n1 y h1 h2 h3]) hx]
  have M2 : ∀ a, ¬ (Wb + m ≤ a ∧ a < Wb + 2 * m) → ¬ (Wb + 4 * m ≤ a ∧ a < Wb + 5 * m) →
      c₂.nmem a = c.nmem a := fun a h1 h2 => by rw [m2 a (by omega), m1 a (by omega)]
  -- FLr
  obtain ⟨c₃, k₃, e₃, hk₃, a3, m3, n3, rr3, rm3, o3'⟩ := mapRun_exec (P := P) c₂ e₂.wb_right
    (vb := vbFLr) (bnd := 6510) (ob := 6532) (m := m) (Ob := Wb + 2 * m) (B := 16)
    (fun i => flR (c.nmem (LPb + i)) (c.nmem (Wb + i)) (c.nmem (Wb + c.nmem (RVb + i))))
    (by rw [Q2 6510 (by omega), r10]) (by rw [Q2 6521 (by omega), r21])
    (by rw [Q2 6532 (by omega), r32]) (by omega) (by omega) (by unfold vscr; omega)
    (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      have hr' := hrv i hi
      have e1 : c'.nmem (LPb + i) = c.nmem (LPb + i) := by
        rw [hm _ (by omega), M2 _ (by omega) (by omega)]
      have e2 : c'.nmem (Wb + i) = c.nmem (Wb + i) := by
        rw [hm _ (by omega), M2 _ (by omega) (by omega)]
      have e3 : c'.nmem (RVb + i) = c.nmem (RVb + i) := by
        rw [hm _ (by omega), M2 _ (by omega) (by omega)]
      have e4 : c'.nmem (Wb + c.nmem (RVb + i)) = c.nmem (Wb + c.nmem (RVb + i)) := by
        rw [hm _ (by omega), M2 _ (by omega) (by omega)]
      have Q : ∀ x, (x < 6520 ∨ x = 6521 ∨ 6529 < x) → c'.nreg x = c.nreg x := fun x hx => by
        rw [R c' x (fun y h1 h2 h3 => by rw [hr y h1 h2 h3, n2 y h1 h2 h3, n1 y h1 h2 h3]) hx]
      obtain ⟨c'', t, ex, ht, v, n, mm, rr, rm, oo⟩ := vbFLr_exec (P := P) c' hw h20
        (by rw [Q 6521 (by omega), r21]) (by rw [Q 6539 (by omega), r39]) (by rw [Q 6543 (by omega), r43])
        (by rw [Q 6544 (by omega), r44]) (by rw [Q 6545 (by omega), r45]) (by omega) (by omega)
        (by rw [e3]; omega) (by omega)
      exact ⟨c'', t, ex, ht, by rw [v, e3, e1, e2, e4], n, mm, rr, rm, oo⟩)
  have Q3 : ∀ x, (x < 6520 ∨ x = 6521 ∨ 6529 < x) → c₃.nreg x = c.nreg x := fun x hx => by
    rw [R c₃ x (fun y h1 h2 h3 => by rw [n3 y h1 h2 h3, n2 y h1 h2 h3, n1 y h1 h2 h3]) hx]
  have M3 : ∀ a, ¬ (Wb + m ≤ a ∧ a < Wb + 3 * m) → ¬ (Wb + 4 * m ≤ a ∧ a < Wb + 5 * m) →
      c₃.nmem a = c.nmem a := fun a h1 h2 => by rw [m3 a (by omega), M2 a (by omega) h2]
  -- KC
  obtain ⟨c₄, k₄, e₄, hk₄, a4, m4, n4, rr4, rm4, o4'⟩ := mapRun_exec (P := P) c₃ e₃.wb_right
    (vb := vbKC) (bnd := 6510) (ob := 6533) (m := m) (Ob := Wb + 3 * m) (B := 7)
    (fun i => kcF (c.nmem (Wb + i)) (c.nmem (KRb + i)))
    (by rw [Q3 6510 (by omega), r10]) (by rw [Q3 6521 (by omega), r21])
    (by rw [Q3 6533 (by omega), r33]) (by omega) (by omega) (by unfold vscr; omega)
    (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      have e2 : c'.nmem (Wb + i) = c.nmem (Wb + i) := by
        rw [hm _ (by omega), M3 _ (by omega) (by omega)]
      have e5 : c'.nmem (KRb + i) = c.nmem (KRb + i) := by
        rw [hm _ (by omega), M3 _ (by omega) (by omega)]
      have Q : ∀ x, (x < 6520 ∨ x = 6521 ∨ 6529 < x) → c'.nreg x = c.nreg x := fun x hx => by
        rw [R c' x (fun y h1 h2 h3 => by
          rw [hr y h1 h2 h3, n3 y h1 h2 h3, n2 y h1 h2 h3, n1 y h1 h2 h3]) hx]
      obtain ⟨c'', t, ex, ht, v, n, mm, rr, rm, oo⟩ := vbKC_exec (P := P) c' hw h20
        (by rw [Q 6521 (by omega), r21]) (by rw [Q 6539 (by omega), r39]) (by rw [Q 6544 (by omega), r44])
        (by rw [Q 6546 (by omega), r46]) (by omega) (by omega)
      exact ⟨c'', t, ex, ht, by rw [v, e2, e5], n, mm, rr, rm, oo⟩)
  have Q4 : ∀ x, (x < 6520 ∨ x = 6521 ∨ 6529 < x) → c₄.nreg x = c.nreg x := fun x hx => by
    rw [R c₄ x (fun y h1 h2 h3 => by
      rw [n4 y h1 h2 h3, n3 y h1 h2 h3, n2 y h1 h2 h3, n1 y h1 h2 h3]) hx]
  -- ID
  obtain ⟨c₅, k₅, e₅, hk₅, a5, m5, n5, rr5, rm5, o5'⟩ := mapRun_exec (P := P) c₄ e₄.wb_right
    (vb := vbID) (bnd := 6510) (ob := 6535) (m := m) (Ob := Wb + 5 * m) (B := 1) (fun i => i)
    (by rw [Q4 6510 (by omega), r10]) (by rw [Q4 6521 (by omega), r21])
    (by rw [Q4 6535 (by omega), r35]) (by omega) (by omega) (by unfold vscr; omega)
    (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => vbID_exec (P := P) c' hw h20)
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, a5, fun a ha => ?_,
    fun x h1 h2 h3 => ?_, by rw [rr5, rr4, rr3, rr2, rr1], by rw [rm5, rm4, rm3, rm2, rm1],
    by rw [o5', o4', o3', o2', o1']⟩
  · rw [m5 _ (by omega), m4 _ (by omega), m3 _ (by omega), m2 _ (by omega)]; exact a1 i hi
  · rw [m5 _ (by omega), m4 _ (by omega), m3 _ (by omega)]; exact a2 i hi
  · rw [m5 _ (by omega), m4 _ (by omega)]; exact a3 i hi
  · rw [m5 _ (by omega)]; exact a4 i hi
  · rw [m5 _ (by omega), m4 _ (by omega), M3 _ (by omega) (by omega)]
  · rw [n5 x h1 h2 h3, n4 x h1 h2 h3, n3 x h1 h2 h3, n2 x h1 h2 h3, n1 x h1 h2 h3]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
