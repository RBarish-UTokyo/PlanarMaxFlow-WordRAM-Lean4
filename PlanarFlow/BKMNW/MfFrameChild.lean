module

public import PlanarFlow.BKMNW.LinCmp2
public import PlanarFlow.BKMNW.LinGather
public import PlanarFlow.BKMNW.MfFrame

/-!
# Writing the frame of a child call

`sfChild` writes the frame of one child call at `dc` from the parent's frame at `d` (`m` darts
numbered by `en`) and four per-dart arrays of the parent: the identity `ID`, the flags `PF` of
the separator's darts, the flags `Fx` of the child's darts `Bc`, the child's ranks `KC` and hole
labels `HC`:

* copies `SG | RV | PF | Fx` to the area `A` of `chRotProg` (four gathers by `ID`), runs
  `chRotProg` (the child's rotation in the child's own numbering, with the compaction maps
  `CI`, `IX` and the count `mc`, `chRotProg_exec'`);
* writes the header `mc | kc | tg | Z` and, by seven gathers through `IX`, the arrays
  `GID[IX]`, `RV_c = CI[RV[IX]]` (through a temporary `T`), `SG_c = OUT`, `CP[IX]`, `KC[IX]`,
  `HC[IX]`.

Registers: inputs `6560 = m`, `6561 = d`, `6562 = A`, `6563 = IDb`, `6564 = PFb`, `6565 = Fxb`,
`6566 = Tb`, `6567 = KCb`, `6568 = HCb`, `6569 = dc`, `6570 = kc`, `6571 = tg`, `6572 = Z`;
written `6580 … 6599` and those of `chRotProg` (`6200 … 6328`); `r6597 = dc + 4 + 7 mc` at the end.

* **`sfChild_exec`**: within `135 m + 120` steps, the child's darts listed as `en (ix k)`
  (`k < mc`, `ix` strictly increasing, onto `Bc`), the header, `GID`, `RV`, `SG` (the child's
  rotation `childRot M σ B L Bc`), and `CP`, `KR`, `HL` read through `ix`.
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

/-- The addresses in the parent's frame and in the area `A`. -/
def sfA0 : Stmt := block [.constN 6598 4, .addN 6580 6561 6598, .addN 6581 6580 6560,
  .addN 6582 6581 6560, .addN 6583 6582 6560, .addN 6585 6562 6560, .addN 6586 6585 6560,
  .addN 6587 6586 6560, .addN 6599 6587 6560, .addN 6599 6599 6560, .addN 6599 6599 6560,
  .addN 6599 6599 6560, .addN 6588 6599 6560, .addN 6589 6588 6560, .addN 6590 6589 6560]

/-- The input arrays of `chRotProg`: `SG | RV | PF | Fx` at `A`. -/
def sfPrep : Stmt := .seq (ggProg 6560 6563 6582 6562) (.seq (ggProg 6560 6563 6581 6585)
  (.seq (ggProg 6560 6563 6564 6586) (ggProg 6560 6563 6565 6587)))

/-- `chRotProg` on `m` darts at `A`. -/
def sfChr : Stmt := .seq (block [.copyN 6200 6560, .copyN 6201 6562]) chRotProg

/-- The addresses of the child's arrays, and its header. -/
def sfA1 : Stmt := block [.addN 6591 6569 6598, .addN 6592 6591 6306, .addN 6593 6592 6306,
  .addN 6594 6593 6306, .addN 6595 6594 6306, .addN 6596 6595 6306, .addN 6599 6596 6306,
  .addN 6597 6599 6306, .storeN 6569 6306, .constN 6599 1, .addN 6599 6569 6599,
  .storeN 6599 6570, .constN 6599 2, .addN 6599 6569 6599, .storeN 6599 6571, .constN 6599 3,
  .addN 6599 6569 6599, .storeN 6599 6572]

/-- The child's arrays, by gathers through `IX`. -/
def sfGath : Stmt := .seq (ggProg 6306 6589 6580 6591) (.seq (ggProg 6306 6589 6581 6566)
  (.seq (ggProg 6306 6566 6588 6592) (.seq (ggProg 6306 6563 6590 6593)
  (.seq (ggProg 6306 6589 6583 6594) (.seq (ggProg 6306 6589 6567 6595)
  (ggProg 6306 6589 6568 6596))))))

/-- **The frame of a child call.** -/
def sfChild : Stmt := .seq (.seq sfA0 (.seq sfPrep sfChr)) (.seq sfA1 sfGath)

section Exec

variable {P : Input} {W : ℕ}

theorem sfA0_exec (c : Config) (hc : WordsBounded W c) {m d A : ℕ} (r0 : c.nreg 6560 = m)
    (r1 : c.nreg 6561 = d) (r2 : c.nreg 6562 = A) (w1 : d + 4 + 4 * m ≤ W)
    (w2 : A + 11 * m ≤ W) :
    ∃ c' k, Exec P W sfA0 c c' k ∧ k = 15 ∧ c'.nreg 6598 = 4 ∧ c'.nreg 6580 = d + 4 ∧
      c'.nreg 6581 = d + 4 + m ∧ c'.nreg 6582 = d + 4 + 2 * m ∧ c'.nreg 6583 = d + 4 + 3 * m ∧
      c'.nreg 6585 = A + m ∧ c'.nreg 6586 = A + 2 * m ∧ c'.nreg 6587 = A + 3 * m ∧
      c'.nreg 6588 = A + 8 * m ∧ c'.nreg 6589 = A + 9 * m ∧ c'.nreg 6590 = A + 10 * m ∧
      (∀ x, (x < 6580 ∨ 6599 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sfA0
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r0, r1, r2]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r0, r1, r2])
    try omega

/-- One copy by the identity: `OUT[j] := A[j]`. -/
theorem ggId_exec (c : Config) (hc : WordsBounded W c) {a b cc dd m IDb Ab OUTb : ℕ}
    (ha : a < 6210 ∨ 6217 < a) (hb : b < 6210 ∨ 6217 < b) (hcc : cc < 6210 ∨ 6217 < cc)
    (hdd : dd < 6210 ∨ 6217 < dd)
    (r0 : c.nreg a = m) (r1 : c.nreg b = IDb) (r2 : c.nreg cc = Ab) (r3 : c.nreg dd = OUTb)
    (hid : ∀ j < m, c.nmem (IDb + j) = j) (w1 : IDb + m ≤ W) (w2 : Ab + m ≤ W)
    (w3 : OUTb + m ≤ W) (w4 : m + 1 ≤ W) (o1 : IDb + m ≤ OUTb ∨ OUTb + m ≤ IDb)
    (o2 : Ab + m ≤ OUTb ∨ OUTb + m ≤ Ab) :
    ∃ c' k, Exec P W (ggProg a b cc dd) c c' k ∧ k ≤ 9 * m + 8 ∧
      (∀ j < m, c'.nmem (OUTb + j) = c.nmem (Ab + j)) ∧
      (∀ x, ¬ (OUTb ≤ x ∧ x < OUTb + m) → c'.nmem x = c.nmem x) ∧
      (∀ x, (x < 6210 ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, ex, hk, h1, h2, h3, h4, h5, h6⟩ := ggProg_exec (P := P) c hc ha hb hcc hdd r0 r1
    r2 r3 (by omega) w3 w4 (fun j hj => by rw [hid j hj]; omega)
    (fun j hj => by omega) (fun j hj => by rw [hid j hj]; omega)
  exact ⟨c', k, ex, hk, fun j hj => by rw [h1 j hj, hid j hj], h2, h3, h4, h5, h6⟩

theorem sfPrep_exec (c : Config) (hc : WordsBounded W c) {m d A IDb PFb Fxb : ℕ}
    (r0 : c.nreg 6560 = m) (r3 : c.nreg 6563 = IDb) (r4 : c.nreg 6564 = PFb)
    (r5 : c.nreg 6565 = Fxb) (r62 : c.nreg 6562 = A) (r81 : c.nreg 6581 = d + 4 + m)
    (r82 : c.nreg 6582 = d + 4 + 2 * m) (r85 : c.nreg 6585 = A + m)
    (r86 : c.nreg 6586 = A + 2 * m) (r87 : c.nreg 6587 = A + 3 * m)
    (hid : ∀ j < m, c.nmem (IDb + j) = j) (o1 : d + 4 + 3 * m ≤ A) (o2 : IDb + m ≤ A)
    (o3 : PFb + m ≤ A) (o4 : Fxb + m ≤ A) (w : A + 4 * m ≤ W) (w' : m + 1 ≤ W) :
    ∃ c' k, Exec P W sfPrep c c' k ∧ k ≤ 36 * m + 32 ∧
      (∀ j < m, c'.nmem (A + j) = c.nmem (d + 4 + 2 * m + j)) ∧
      (∀ j < m, c'.nmem (A + m + j) = c.nmem (d + 4 + m + j)) ∧
      (∀ j < m, c'.nmem (A + 2 * m + j) = c.nmem (PFb + j)) ∧
      (∀ j < m, c'.nmem (A + 3 * m + j) = c.nmem (Fxb + j)) ∧
      (∀ x, ¬ (A ≤ x ∧ x < A + 4 * m) → c'.nmem x = c.nmem x) ∧
      (∀ x, (x < 6210 ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a1, m1, n1, rr1, rm1, ro1⟩ := ggId_exec (P := P) c hc (by omega)
    (by omega) (by omega) (by omega) r0 r3 r82 r62 hid (by omega) (by omega) (by omega)
    w' (by omega) (by omega)
  have q : ∀ x, (x < 6210 ∨ 6217 < x) → c₁.nreg x = c.nreg x := n1
  have hid1 : ∀ j < m, c₁.nmem (IDb + j) = j := fun j hj => by rw [m1 _ (by omega), hid j hj]
  obtain ⟨c₂, k₂, e₂, hk₂, a2, m2, n2, rr2, rm2, ro2⟩ := ggId_exec (P := P) (a := 6560) (b := 6563) (cc := 6581) (dd := 6585) c₁ e₁.wb_right
    (by omega) (by omega) (by omega) (by omega) (by rw [q _ (by omega), r0])
    (by rw [q _ (by omega), r3]) (by rw [q _ (by omega), r81]) (by rw [q _ (by omega), r85])
    hid1 (by omega) (by omega) (by omega) w' (by omega) (by omega)
  have q2 : ∀ x, (x < 6210 ∨ 6217 < x) → c₂.nreg x = c.nreg x := fun x hx => by
    rw [n2 x hx, q x hx]
  have hid2 : ∀ j < m, c₂.nmem (IDb + j) = j := fun j hj => by rw [m2 _ (by omega), hid1 j hj]
  obtain ⟨c₃, k₃, e₃, hk₃, a3, m3, n3, rr3, rm3, ro3⟩ := ggId_exec (P := P) (a := 6560) (b := 6563) (cc := 6564) (dd := 6586) c₂ e₂.wb_right
    (by omega) (by omega) (by omega) (by omega) (by rw [q2 _ (by omega), r0])
    (by rw [q2 _ (by omega), r3]) (by rw [q2 _ (by omega), r4]) (by rw [q2 _ (by omega), r86])
    hid2 (by omega) (by omega) (by omega) w' (by omega) (by omega)
  have q3 : ∀ x, (x < 6210 ∨ 6217 < x) → c₃.nreg x = c.nreg x := fun x hx => by
    rw [n3 x hx, q2 x hx]
  have hid3 : ∀ j < m, c₃.nmem (IDb + j) = j := fun j hj => by rw [m3 _ (by omega), hid2 j hj]
  obtain ⟨c₄, k₄, e₄, hk₄, a4, m4, n4, rr4, rm4, ro4⟩ := ggId_exec (P := P) (a := 6560) (b := 6563) (cc := 6565) (dd := 6587) c₃ e₃.wb_right
    (by omega) (by omega) (by omega) (by omega) (by rw [q3 _ (by omega), r0])
    (by rw [q3 _ (by omega), r3]) (by rw [q3 _ (by omega), r5]) (by rw [q3 _ (by omega), r87])
    hid3 (by omega) (by omega) (by omega) w' (by omega) (by omega)
  have M : ∀ x, ¬ (A ≤ x ∧ x < A + 4 * m) → c₄.nmem x = c.nmem x := fun x hx => by
    rw [m4 _ (by omega), m3 _ (by omega), m2 _ (by omega), m1 _ (by omega)]
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, fun j hj => ?_,
    fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, M, fun x hx => by rw [n4 x hx, q3 x hx],
    by rw [rr4, rr3, rr2, rr1], by rw [rm4, rm3, rm2, rm1], by rw [ro4, ro3, ro2, ro1]⟩
  · rw [m4 _ (by omega), m3 _ (by omega), m2 _ (by omega), a1 j hj]
  · rw [m4 _ (by omega), m3 _ (by omega), a2 j hj, m1 _ (by omega)]
  · rw [m4 _ (by omega), a3 j hj, m2 _ (by omega), m1 _ (by omega)]
  · rw [a4 j hj, m3 _ (by omega), m2 _ (by omega), m1 _ (by omega)]

theorem sfA1_exec (c : Config) (hc : WordsBounded W c) {dc mc kc tg Z : ℕ}
    (r69 : c.nreg 6569 = dc) (r98 : c.nreg 6598 = 4) (r06 : c.nreg 6306 = mc)
    (r70 : c.nreg 6570 = kc) (r71 : c.nreg 6571 = tg) (r72 : c.nreg 6572 = Z)
    (w : dc + 4 + 7 * mc ≤ W) :
    ∃ c' k, Exec P W sfA1 c c' k ∧ k = 18 ∧ c'.nreg 6591 = dc + 4 ∧
      c'.nreg 6592 = dc + 4 + mc ∧ c'.nreg 6593 = dc + 4 + 2 * mc ∧
      c'.nreg 6594 = dc + 4 + 3 * mc ∧ c'.nreg 6595 = dc + 4 + 4 * mc ∧
      c'.nreg 6596 = dc + 4 + 5 * mc ∧ c'.nreg 6597 = dc + 4 + 7 * mc ∧
      c'.nmem dc = mc ∧ c'.nmem (dc + 1) = kc ∧ c'.nmem (dc + 2) = tg ∧ c'.nmem (dc + 3) = Z ∧
      (∀ a, (a < dc ∨ dc + 3 < a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6591 ∨ 6599 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sfA1
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r69, r98, r06]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun x hx => ?_, rfl,
    rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r69, r98, r06, r70, r71, r72])
    try omega

set_option maxHeartbeats 2000000 in
theorem sfGath_exec (c : Config) (hc : WordsBounded W c) {m mc d A IDb Tb KCb HCb dc : ℕ}
    (r06 : c.nreg 6306 = mc) (r89 : c.nreg 6589 = A + 9 * m) (r80 : c.nreg 6580 = d + 4)
    (r91 : c.nreg 6591 = dc + 4) (r81 : c.nreg 6581 = d + 4 + m) (r66 : c.nreg 6566 = Tb)
    (r88 : c.nreg 6588 = A + 8 * m) (r92 : c.nreg 6592 = dc + 4 + mc)
    (r63 : c.nreg 6563 = IDb) (r90 : c.nreg 6590 = A + 10 * m)
    (r93 : c.nreg 6593 = dc + 4 + 2 * mc) (r83 : c.nreg 6583 = d + 4 + 3 * m)
    (r94 : c.nreg 6594 = dc + 4 + 3 * mc) (r67 : c.nreg 6567 = KCb)
    (r95 : c.nreg 6595 = dc + 4 + 4 * mc) (r68 : c.nreg 6568 = HCb)
    (r96 : c.nreg 6596 = dc + 4 + 5 * mc) (hmc : mc ≤ m)
    (hix : ∀ k < mc, c.nmem (A + 9 * m + k) < m)
    (hrv : ∀ i < m, c.nmem (d + 4 + m + i) < m) (hid : ∀ j < m, c.nmem (IDb + j) = j)
    (o1 : d + 4 + 6 * m ≤ dc) (o2 : dc + 4 + 7 * m ≤ IDb) (o3 : dc + 4 + 7 * m ≤ KCb)
    (o4 : dc + 4 + 7 * m ≤ HCb) (o5 : IDb + m ≤ Tb) (o6 : KCb + m ≤ Tb) (o7 : HCb + m ≤ Tb)
    (o8 : Tb + m ≤ A) (w : A + 11 * m ≤ W) (w' : m + 1 ≤ W) :
    ∃ c' k, Exec P W sfGath c c' k ∧ k ≤ 63 * m + 56 ∧
      (∀ k < mc, c'.nmem (dc + 4 + k) = c.nmem (d + 4 + c.nmem (A + 9 * m + k))) ∧
      (∀ k < mc, c'.nmem (dc + 4 + mc + k) =
        c.nmem (A + 8 * m + c.nmem (d + 4 + m + c.nmem (A + 9 * m + k)))) ∧
      (∀ k < mc, c'.nmem (dc + 4 + 2 * mc + k) = c.nmem (A + 10 * m + k)) ∧
      (∀ k < mc, c'.nmem (dc + 4 + 3 * mc + k) = c.nmem (d + 4 + 3 * m + c.nmem (A + 9 * m + k))) ∧
      (∀ k < mc, c'.nmem (dc + 4 + 4 * mc + k) = c.nmem (KCb + c.nmem (A + 9 * m + k))) ∧
      (∀ k < mc, c'.nmem (dc + 4 + 5 * mc + k) = c.nmem (HCb + c.nmem (A + 9 * m + k))) ∧
      (∀ a, ¬ (dc + 4 ≤ a ∧ a < dc + 4 + 6 * mc) → ¬ (Tb ≤ a ∧ a < Tb + mc) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6210 ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- GID
  obtain ⟨c₁, k₁, e₁, hk₁, a1, m1, n1, rr1, rm1, ro1⟩ := ggProg_exec (P := P) c hc
    (a := 6306) (b := 6589) (cc := 6580) (dd := 6591) (by omega) (by omega) (by omega)
    (by omega) r06 r89 r80 r91 (by omega) (by omega) (by omega)
    (fun j hj => by have := hix j hj; omega) (fun j hj => by omega)
    (fun j hj => by have := hix j hj; omega)
  have q1 : ∀ x, (x < 6210 ∨ 6217 < x) → c₁.nreg x = c.nreg x := n1
  have f1 : ∀ a, ¬ (dc + 4 ≤ a ∧ a < dc + 4 + mc) → c₁.nmem a = c.nmem a := m1
  -- T := RV[IX]
  obtain ⟨c₂, k₂, e₂, hk₂, a2, m2, n2, rr2, rm2, ro2⟩ := ggProg_exec (P := P) c₁ e₁.wb_right
    (a := 6306) (b := 6589) (cc := 6581) (dd := 6566) (by omega) (by omega) (by omega)
    (by omega) (by rw [q1 _ (by omega), r06]) (by rw [q1 _ (by omega), r89])
    (by rw [q1 _ (by omega), r81]) (by rw [q1 _ (by omega), r66]) (by omega) (by omega)
    (by omega) (fun j hj => by rw [f1 _ (by omega)]; have := hix j (by omega); omega)
    (fun j hj => by omega) (fun j hj => by rw [f1 _ (by omega)]; have := hix j hj; omega)
  have q2 : ∀ x, (x < 6210 ∨ 6217 < x) → c₂.nreg x = c.nreg x := fun x hx => by
    rw [n2 x hx, q1 x hx]
  have f2 : ∀ a, ¬ (dc + 4 ≤ a ∧ a < dc + 4 + mc) → ¬ (Tb ≤ a ∧ a < Tb + mc) →
      c₂.nmem a = c.nmem a := fun a h1 h2 => by rw [m2 a h2, f1 a h1]
  have hT : ∀ k < mc, c₂.nmem (Tb + k) = c.nmem (d + 4 + m + c.nmem (A + 9 * m + k)) :=
    fun k hk => by
      have := hix k hk
      rw [a2 k hk, f1 (A + 9 * m + k) (by omega), f1 _ (by omega)]
  have hT' : ∀ k < mc, c₂.nmem (Tb + k) < m := fun k hk => by
    rw [hT k hk]; exact hrv _ (hix k hk)
  -- RV_c := CI[T]
  obtain ⟨c₃, k₃, e₃, hk₃, a3, m3, n3, rr3, rm3, ro3⟩ := ggProg_exec (P := P) c₂ e₂.wb_right
    (a := 6306) (b := 6566) (cc := 6588) (dd := 6592) (by omega) (by omega) (by omega)
    (by omega) (by rw [q2 _ (by omega), r06]) (by rw [q2 _ (by omega), r66])
    (by rw [q2 _ (by omega), r88]) (by rw [q2 _ (by omega), r92]) (by omega) (by omega)
    (by omega) (fun j hj => by have := hT' j hj; omega)
    (fun j hj => by omega) (fun j hj => by have := hT' j hj; omega)
  have q3 : ∀ x, (x < 6210 ∨ 6217 < x) → c₃.nreg x = c.nreg x := fun x hx => by
    rw [n3 x hx, q2 x hx]
  have f3 : ∀ a, ¬ (dc + 4 ≤ a ∧ a < dc + 4 + 2 * mc) → ¬ (Tb ≤ a ∧ a < Tb + mc) →
      c₃.nmem a = c.nmem a := fun a h1 h2 => by
    rw [m3 a (by omega), f2 a (by omega) h2]
  -- SG_c := OUT[ID]
  obtain ⟨c₄, k₄, e₄, hk₄, a4, m4, n4, rr4, rm4, ro4⟩ := ggProg_exec (P := P) c₃ e₃.wb_right
    (a := 6306) (b := 6563) (cc := 6590) (dd := 6593) (by omega) (by omega) (by omega)
    (by omega) (by rw [q3 _ (by omega), r06]) (by rw [q3 _ (by omega), r63])
    (by rw [q3 _ (by omega), r90]) (by rw [q3 _ (by omega), r93]) (by omega) (by omega)
    (by omega) (fun j hj => by rw [f3 _ (by omega) (by omega), hid j (by omega)]; omega)
    (fun j hj => by omega)
    (fun j hj => by rw [f3 _ (by omega) (by omega), hid j (by omega)]; omega)
  have q4 : ∀ x, (x < 6210 ∨ 6217 < x) → c₄.nreg x = c.nreg x := fun x hx => by
    rw [n4 x hx, q3 x hx]
  have f4 : ∀ a, ¬ (dc + 4 ≤ a ∧ a < dc + 4 + 3 * mc) → ¬ (Tb ≤ a ∧ a < Tb + mc) →
      c₄.nmem a = c.nmem a := fun a h1 h2 => by
    rw [m4 a (by omega), f3 a (by omega) h2]
  -- CP
  obtain ⟨c₅, k₅, e₅, hk₅, a5, m5, n5, rr5, rm5, ro5⟩ := ggProg_exec (P := P) c₄ e₄.wb_right
    (a := 6306) (b := 6589) (cc := 6583) (dd := 6594) (by omega) (by omega) (by omega)
    (by omega) (by rw [q4 _ (by omega), r06]) (by rw [q4 _ (by omega), r89])
    (by rw [q4 _ (by omega), r83]) (by rw [q4 _ (by omega), r94]) (by omega) (by omega)
    (by omega) (fun j hj => by rw [f4 _ (by omega) (by omega)]; have := hix j hj; omega)
    (fun j hj => by omega)
    (fun j hj => by rw [f4 _ (by omega) (by omega)]; have := hix j hj; omega)
  have q5 : ∀ x, (x < 6210 ∨ 6217 < x) → c₅.nreg x = c.nreg x := fun x hx => by
    rw [n5 x hx, q4 x hx]
  have f5 : ∀ a, ¬ (dc + 4 ≤ a ∧ a < dc + 4 + 4 * mc) → ¬ (Tb ≤ a ∧ a < Tb + mc) →
      c₅.nmem a = c.nmem a := fun a h1 h2 => by
    rw [m5 a (by omega), f4 a (by omega) h2]
  -- KR
  obtain ⟨c₆, k₆, e₆, hk₆, a6, m6, n6, rr6, rm6, ro6⟩ := ggProg_exec (P := P) c₅ e₅.wb_right
    (a := 6306) (b := 6589) (cc := 6567) (dd := 6595) (by omega) (by omega) (by omega)
    (by omega) (by rw [q5 _ (by omega), r06]) (by rw [q5 _ (by omega), r89])
    (by rw [q5 _ (by omega), r67]) (by rw [q5 _ (by omega), r95]) (by omega) (by omega)
    (by omega) (fun j hj => by rw [f5 _ (by omega) (by omega)]; have := hix j hj; omega)
    (fun j hj => by omega)
    (fun j hj => by rw [f5 _ (by omega) (by omega)]; have := hix j hj; omega)
  have q6 : ∀ x, (x < 6210 ∨ 6217 < x) → c₆.nreg x = c.nreg x := fun x hx => by
    rw [n6 x hx, q5 x hx]
  have f6 : ∀ a, ¬ (dc + 4 ≤ a ∧ a < dc + 4 + 5 * mc) → ¬ (Tb ≤ a ∧ a < Tb + mc) →
      c₆.nmem a = c.nmem a := fun a h1 h2 => by
    rw [m6 a (by omega), f5 a (by omega) h2]
  -- HL
  obtain ⟨c₇, k₇, e₇, hk₇, a7, m7, n7, rr7, rm7, ro7⟩ := ggProg_exec (P := P) c₆ e₆.wb_right
    (a := 6306) (b := 6589) (cc := 6568) (dd := 6596) (by omega) (by omega) (by omega)
    (by omega) (by rw [q6 _ (by omega), r06]) (by rw [q6 _ (by omega), r89])
    (by rw [q6 _ (by omega), r68]) (by rw [q6 _ (by omega), r96]) (by omega) (by omega)
    (by omega) (fun j hj => by rw [f6 _ (by omega) (by omega)]; have := hix j hj; omega)
    (fun j hj => by omega)
    (fun j hj => by rw [f6 _ (by omega) (by omega)]; have := hix j hj; omega)
  have f7 : ∀ a, ¬ (dc + 4 ≤ a ∧ a < dc + 4 + 6 * mc) → ¬ (Tb ≤ a ∧ a < Tb + mc) →
      c₇.nmem a = c.nmem a := fun a h1 h2 => by
    rw [m7 a (by omega), f6 a (by omega) h2]
  refine ⟨c₇, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + k₇))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), by omega, ?_, ?_, ?_, ?_, ?_,
    ?_, f7, fun x hx => by rw [n7 x hx, q6 x hx], by rw [rr7, rr6, rr5, rr4, rr3, rr2, rr1],
    by rw [rm7, rm6, rm5, rm4, rm3, rm2, rm1], by rw [ro7, ro6, ro5, ro4, ro3, ro2, ro1]⟩
  · intro k hk
    rw [m7 _ (by omega), m6 _ (by omega), m5 _ (by omega), m4 _ (by omega), m3 _ (by omega),
      m2 _ (by omega), a1 k hk]
  · intro k hk
    have := hT' k hk
    rw [m7 _ (by omega), m6 _ (by omega), m5 _ (by omega), m4 _ (by omega), a3 k hk, hT k hk,
      f2 _ (by omega) (by omega)]
  · intro k hk
    rw [m7 _ (by omega), m6 _ (by omega), m5 _ (by omega), a4 k hk,
      f3 (IDb + k) (by omega) (by omega), hid k (by omega), f3 _ (by omega) (by omega)]
  · intro k hk
    have := hix k hk
    rw [m7 _ (by omega), m6 _ (by omega), a5 k hk, f4 (A + 9 * m + k) (by omega) (by omega),
      f4 _ (by omega) (by omega)]
  · intro k hk
    have := hix k hk
    rw [m7 _ (by omega), a6 k hk, f5 (A + 9 * m + k) (by omega) (by omega),
      f5 _ (by omega) (by omega)]
  · intro k hk
    have := hix k hk
    rw [a7 k hk, f6 (A + 9 * m + k) (by omega) (by omega), f6 _ (by omega) (by omega)]


lemma cnt_congr {F G : ℕ → ℕ} {n : ℕ} (h : ∀ j < n, F j = G j) : cnt F n = cnt G n := by
  unfold cnt; congr 1
  apply filter_congr; intro j hj; rw [mem_range] at hj; rw [h j hj]

set_option maxHeartbeats 1000000 in
/-- The front of `sfChild`: the addresses, the copies, `chRotProg`. -/
theorem sfFront_exec {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] (M : CombMap D V F) (σ : Perm D) (B : Finset D) (L : List D)
    (Bc : Finset D) (c : Config) (hc : WordsBounded W c) {m d A IDb PFb Fxb : ℕ}
    (r60 : c.nreg 6560 = m) (r61 : c.nreg 6561 = d) (r62 : c.nreg 6562 = A)
    (r63 : c.nreg 6563 = IDb) (r64 : c.nreg 6564 = PFb) (r65 : c.nreg 6565 = Fxb)
    {en : ℕ → D} (he : ∀ i < m, ∀ j < m, en i = en j → i = j) (heB : ∀ i < m, en i ∈ B)
    (hBe : ∀ x ∈ B, ∃ i < m, en i = x) (hσ : Stable σ B) (hrB : ∀ x ∈ B, M.rev x ∈ B)
    (hrL : ∀ x ∈ L, M.rev x ∈ L) (hBc : Bc ⊆ B \ L.toFinset)
    (hSG : ∀ i < m, c.nmem (d + 4 + 2 * m + i) < m ∧ en (c.nmem (d + 4 + 2 * m + i)) = σ (en i))
    (hRV : ∀ i < m, c.nmem (d + 4 + m + i) < m ∧ en (c.nmem (d + 4 + m + i)) = M.rev (en i))
    (hPF : ∀ i < m, c.nmem (PFb + i) = if en i ∈ L.toFinset then 1 else 0)
    (hFx : ∀ i < m, c.nmem (Fxb + i) = if en i ∈ Bc then 1 else 0)
    (hid : ∀ j < m, c.nmem (IDb + j) = j)
    (o1 : d + 4 + 3 * m ≤ A) (o2 : IDb + m ≤ A) (o3 : PFb + m ≤ A) (o4 : Fxb + m ≤ A)
    (w : A + 11 * m ≤ W) (w' : m + 2 ≤ W) :
    ∃ c' t, Exec P W (.seq sfA0 (.seq sfPrep sfChr)) c c' t ∧ t ≤ 140 * m + 149 ∧
      c'.nreg 6306 ≤ m ∧ c'.nreg 6306 = cnt (fun j => c.nmem (Fxb + j)) m ∧
      (∀ k < c'.nreg 6306, c'.nmem (A + 9 * m + k) < m ∧ en (c'.nmem (A + 9 * m + k)) ∈ Bc) ∧
      (∀ y ∈ Bc, ∃ k < c'.nreg 6306, en (c'.nmem (A + 9 * m + k)) = y) ∧
      (∀ k < c'.nreg 6306, c'.nmem (A + 10 * m + k) < c'.nreg 6306 ∧
        en (c'.nmem (A + 9 * m + c'.nmem (A + 10 * m + k))) =
          childRot M σ B L Bc (en (c'.nmem (A + 9 * m + k)))) ∧
      (∀ i < m, en i ∈ Bc → c'.nmem (A + 8 * m + i) = cnt (fun j => c.nmem (Fxb + j)) i ∧
        c'.nmem (A + 9 * m + cnt (fun j => c.nmem (Fxb + j)) i) = i) ∧
      (∀ x, ¬ (A ≤ x ∧ x < A + 11 * m) → c'.nmem x = c.nmem x) ∧
      c'.nreg 6598 = 4 ∧ c'.nreg 6580 = d + 4 ∧ c'.nreg 6581 = d + 4 + m ∧
      c'.nreg 6583 = d + 4 + 3 * m ∧ c'.nreg 6588 = A + 8 * m ∧ c'.nreg 6589 = A + 9 * m ∧
      c'.nreg 6590 = A + 10 * m ∧
      (∀ x, (x < 6200 ∨ (6328 < x ∧ x < 6580) ∨ 6599 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a98, a80, a81, a82, a83, a85, a86, a87, a88, a89, a90, n1, m1, rr1,
    rm1, ro1⟩ := sfA0_exec (P := P) c hc r60 r61 r62 (by omega) w
  have q1 : ∀ x, (x < 6580 ∨ 6599 < x) → c₁.nreg x = c.nreg x := n1
  obtain ⟨c₂, k₂, e₂, hk₂, p1, p2, p3, p4, m2, n2, rr2, rm2, ro2⟩ := sfPrep_exec (P := P) c₁
    e₁.wb_right (by rw [q1 _ (by omega), r60]) (by rw [q1 _ (by omega), r63])
    (by rw [q1 _ (by omega), r64]) (by rw [q1 _ (by omega), r65]) (by rw [q1 _ (by omega), r62])
    a81 a82 a85 a86 a87 (fun j hj => by rw [m1, hid j hj]) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  rw [m1] at p1 p2 p3 p4 m2
  have q2 : ∀ x, (x < 6210 ∨ 6217 < x) → c₂.nreg x = c₁.nreg x := n2
  obtain ⟨c₃, k₃, e₃, hk₃, b0, b1, n3, m3, rr3, rm3, ro3⟩ : ∃ c₃ k₃,
      Exec P W (block [.copyN 6200 6560, .copyN 6201 6562]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
      c₃.nreg 6200 = m ∧ c₃.nreg 6201 = A ∧
      (∀ x, x ≠ 6200 → x ≠ 6201 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have s0 : c₂.nreg 6560 = m := by rw [q2 _ (by omega), q1 _ (by omega), r60]
    have s2 : c₂.nreg 6562 = A := by rw [q2 _ (by omega), q1 _ (by omega), r62]
    have hw₂ := e₂.wb_right
    exec_block
    all_goals try omega
    all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, s0, s2]; omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same, s0, s2])
      try omega
  rw [← m3] at p1 p2 p3 p4
  obtain ⟨c₄, k₄, e₄, hk₄, hmc, hIX, hIXs, hIXi, hOUT, m4, n4, rr4, rm4, ro4, h06, hCI⟩ :=
    chRotProg_exec' (P := P) M σ B L Bc c₃ e₃.wb_right b0 b1 w (by omega) he heB hBe hσ hrB
      hrL hBc
      (fun i hi => by rw [p1 i hi]; exact hSG i hi) (fun i hi => by rw [p2 i hi]; exact hRV i hi)
      (fun i hi => by rw [p3 i hi]; exact hPF i hi) (fun i hi => by rw [p4 i hi]; exact hFx i hi)
  have hcF : ∀ i ≤ m, cnt (fun j => c₃.nmem (A + 3 * m + j)) i =
      cnt (fun j => c.nmem (Fxb + j)) i := fun i hi => cnt_congr fun j hj => p4 j (by omega)
  have q4 : ∀ x, (x < 6200 ∨ 6328 < x) → c₄.nreg x = c₃.nreg x := n4
  have q3 : ∀ x, (x < 6200 ∨ (6328 < x ∧ x < 6580) ∨ 6599 < x) → c₃.nreg x = c.nreg x :=
    fun x hx => by rw [n3 x (by omega) (by omega), q2 x (by omega), q1 x (by omega)]
  have reg4 : ∀ x, 6580 ≤ x → x ≤ 6599 → c₄.nreg x = c₁.nreg x := fun x h1 h2 => by
    rw [q4 x (by omega), n3 x (by omega) (by omega), q2 x (by omega)]
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, hmc,
    by rw [h06, hcF m le_rfl], hIX, hIXs, hOUT, fun i hi hx => ?_, fun x hx => ?_,
    by rw [reg4 _ (by omega) (by omega), a98], by rw [reg4 _ (by omega) (by omega), a80],
    by rw [reg4 _ (by omega) (by omega), a81], by rw [reg4 _ (by omega) (by omega), a83],
    by rw [reg4 _ (by omega) (by omega), a88], by rw [reg4 _ (by omega) (by omega), a89],
    by rw [reg4 _ (by omega) (by omega), a90], fun x hx => by rw [q4 x (by omega), q3 x hx],
    by rw [rr4, rr3, rr2, rr1], by rw [rm4, rm3, rm2, rm1], by rw [ro4, ro3, ro2, ro1]⟩
  · rw [← hcF i hi.le]; exact hCI i hi hx
  · rw [m4 x (by omega), m3, m2 x (by omega)]

/-- The back of `sfChild`: the header and the gathers. -/
theorem sfBack_exec (c : Config) (hc : WordsBounded W c)
    {m mc d A IDb Tb KCb HCb dc kc tg Z : ℕ}
    (r69 : c.nreg 6569 = dc) (r98 : c.nreg 6598 = 4) (r06 : c.nreg 6306 = mc)
    (r70 : c.nreg 6570 = kc) (r71 : c.nreg 6571 = tg) (r72 : c.nreg 6572 = Z)
    (r89 : c.nreg 6589 = A + 9 * m) (r80 : c.nreg 6580 = d + 4) (r81 : c.nreg 6581 = d + 4 + m)
    (r66 : c.nreg 6566 = Tb) (r88 : c.nreg 6588 = A + 8 * m) (r63 : c.nreg 6563 = IDb)
    (r90 : c.nreg 6590 = A + 10 * m) (r83 : c.nreg 6583 = d + 4 + 3 * m)
    (r67 : c.nreg 6567 = KCb) (r68 : c.nreg 6568 = HCb) (hmc : mc ≤ m)
    (hix : ∀ k < mc, c.nmem (A + 9 * m + k) < m)
    (hrv : ∀ i < m, c.nmem (d + 4 + m + i) < m) (hid : ∀ j < m, c.nmem (IDb + j) = j)
    (o1 : d + 4 + 6 * m ≤ dc) (o2 : dc + 4 + 7 * m ≤ IDb) (o3 : dc + 4 + 7 * m ≤ KCb)
    (o4 : dc + 4 + 7 * m ≤ HCb) (o5 : IDb + m ≤ Tb) (o6 : KCb + m ≤ Tb) (o7 : HCb + m ≤ Tb)
    (o8 : Tb + m ≤ A) (w : A + 11 * m ≤ W) (w' : m + 1 ≤ W) :
    ∃ c' k, Exec P W (.seq sfA1 sfGath) c c' k ∧ k ≤ 63 * m + 74 ∧
      c'.nreg 6597 = dc + 4 + 7 * mc ∧
      c'.nmem dc = mc ∧ c'.nmem (dc + 1) = kc ∧ c'.nmem (dc + 2) = tg ∧ c'.nmem (dc + 3) = Z ∧
      (∀ k < mc, c'.nmem (dc + 4 + k) = c.nmem (d + 4 + c.nmem (A + 9 * m + k))) ∧
      (∀ k < mc, c'.nmem (dc + 4 + mc + k) =
        c.nmem (A + 8 * m + c.nmem (d + 4 + m + c.nmem (A + 9 * m + k)))) ∧
      (∀ k < mc, c'.nmem (dc + 4 + 2 * mc + k) = c.nmem (A + 10 * m + k)) ∧
      (∀ k < mc, c'.nmem (dc + 4 + 3 * mc + k) = c.nmem (d + 4 + 3 * m + c.nmem (A + 9 * m + k))) ∧
      (∀ k < mc, c'.nmem (dc + 4 + 4 * mc + k) = c.nmem (KCb + c.nmem (A + 9 * m + k))) ∧
      (∀ k < mc, c'.nmem (dc + 4 + 5 * mc + k) = c.nmem (HCb + c.nmem (A + 9 * m + k))) ∧
      (∀ a, ¬ (dc ≤ a ∧ a < dc + 4 + 6 * mc) → ¬ (Tb ≤ a ∧ a < Tb + mc) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6210 ∨ (6217 < x ∧ x < 6591) ∨ 6599 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, d91, d92, d93, d94, d95, d96, d97, h0, h1, h2, h3, m1, n1, rr1, rm1,
    ro1⟩ := sfA1_exec (P := P) c hc r69 r98 r06 r70 r71 r72 (by omega)
  have q : ∀ x, (x < 6591 ∨ 6599 < x) → c₁.nreg x = c.nreg x := n1
  have mm : ∀ x, (x < dc ∨ dc + 3 < x) → c₁.nmem x = c.nmem x := m1
  obtain ⟨c₂, k₂, e₂, hk₂, g1, g2, g3, g4, g5, g6, m2, n2, rr2, rm2, ro2⟩ := sfGath_exec (P := P)
    c₁ e₁.wb_right (m := m) (mc := mc) (d := d) (A := A) (IDb := IDb) (Tb := Tb) (KCb := KCb)
    (HCb := HCb) (dc := dc)
    (by rw [q _ (by omega), r06]) (by rw [q _ (by omega), r89]) (by rw [q _ (by omega), r80])
    d91 (by rw [q _ (by omega), r81]) (by rw [q _ (by omega), r66])
    (by rw [q _ (by omega), r88]) d92 (by rw [q _ (by omega), r63])
    (by rw [q _ (by omega), r90]) d93 (by rw [q _ (by omega), r83])
    d94 (by rw [q _ (by omega), r67]) d95 (by rw [q _ (by omega), r68]) d96 hmc
    (fun k hk => by rw [mm _ (by omega)]; exact hix k hk)
    (fun i hi => by rw [mm _ (by omega)]; exact hrv i hi)
    (fun j hj => by rw [mm _ (by omega)]; exact hid j hj)
    o1 o2 o3 o4 o5 o6 o7 o8 w w'
  have ix : ∀ k < mc, c₁.nmem (A + 9 * m + k) = c.nmem (A + 9 * m + k) := fun k hk =>
    mm _ (by omega)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, by rw [n2 _ (by omega)]; exact d97,
    by rw [m2 _ (by omega) (by omega)]; exact h0, by rw [m2 _ (by omega) (by omega)]; exact h1,
    by rw [m2 _ (by omega) (by omega)]; exact h2, by rw [m2 _ (by omega) (by omega)]; exact h3,
    fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_,
    fun k hk => ?_, fun a h1 h2 => ?_, fun x hx => ?_, by rw [rr2, rr1], by rw [rm2, rm1],
    by rw [ro2, ro1]⟩
  · have := hix k hk
    rw [g1 k hk, ix k hk, mm _ (by omega)]
  · have := hix k hk
    have := hrv _ this
    rw [g2 k hk, ix k hk, mm (d + 4 + m + c.nmem (A + 9 * m + k)) (by omega), mm _ (by omega)]
  · rw [g3 k hk, mm _ (by omega)]
  · have := hix k hk
    rw [g4 k hk, ix k hk, mm _ (by omega)]
  · have := hix k hk
    rw [g5 k hk, ix k hk, mm _ (by omega)]
  · have := hix k hk
    rw [g6 k hk, ix k hk, mm _ (by omega)]
  · rw [m2 a (by omega) h2, mm a (by omega)]
  · rw [n2 x (by omega), q x (by omega)]

set_option maxHeartbeats 1000000 in
/-- **The frame of a child call** (see the module docstring). -/
theorem sfChild_exec {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] (M : CombMap D V F) (σ : Perm D) (B : Finset D) (L : List D)
    (Bc : Finset D) (c : Config) (hc : WordsBounded W c)
    {m d A IDb PFb Fxb Tb KCb HCb dc kc tg Z : ℕ}
    (r60 : c.nreg 6560 = m) (r61 : c.nreg 6561 = d) (r62 : c.nreg 6562 = A)
    (r63 : c.nreg 6563 = IDb) (r64 : c.nreg 6564 = PFb) (r65 : c.nreg 6565 = Fxb)
    (r66 : c.nreg 6566 = Tb) (r67 : c.nreg 6567 = KCb) (r68 : c.nreg 6568 = HCb)
    (r69 : c.nreg 6569 = dc) (r70 : c.nreg 6570 = kc) (r71 : c.nreg 6571 = tg)
    (r72 : c.nreg 6572 = Z)
    {en : ℕ → D} (he : ∀ i < m, ∀ j < m, en i = en j → i = j) (heB : ∀ i < m, en i ∈ B)
    (hBe : ∀ x ∈ B, ∃ i < m, en i = x) (hσ : Stable σ B) (hrB : ∀ x ∈ B, M.rev x ∈ B)
    (hrL : ∀ x ∈ L, M.rev x ∈ L) (hBc : Bc ⊆ B \ L.toFinset) (hBcr : ∀ y ∈ Bc, M.rev y ∈ Bc)
    (hSG : ∀ i < m, c.nmem (d + 4 + 2 * m + i) < m ∧ en (c.nmem (d + 4 + 2 * m + i)) = σ (en i))
    (hRV : ∀ i < m, c.nmem (d + 4 + m + i) < m ∧ en (c.nmem (d + 4 + m + i)) = M.rev (en i))
    (hPF : ∀ i < m, c.nmem (PFb + i) = if en i ∈ L.toFinset then 1 else 0)
    (hFx : ∀ i < m, c.nmem (Fxb + i) = if en i ∈ Bc then 1 else 0)
    (hid : ∀ j < m, c.nmem (IDb + j) = j)
    (o0 : d + 4 + 6 * m ≤ dc) (o1 : dc + 4 + 7 * m ≤ IDb) (o2 : dc + 4 + 7 * m ≤ PFb)
    (o3 : dc + 4 + 7 * m ≤ Fxb) (o4 : dc + 4 + 7 * m ≤ KCb) (o5 : dc + 4 + 7 * m ≤ HCb)
    (o6 : IDb + m ≤ Tb) (o7 : PFb + m ≤ Tb) (o8 : Fxb + m ≤ Tb) (o9 : KCb + m ≤ Tb)
    (o10 : HCb + m ≤ Tb) (o11 : Tb + m ≤ A) (w : A + 11 * m ≤ W) (w' : m + 2 ≤ W) :
    ∃ c' t, Exec P W sfChild c c' t ∧ t ≤ 203 * m + 223 ∧ ∃ mc : ℕ, ∃ ix : ℕ → ℕ, mc ≤ m ∧
      c'.nreg 6597 = dc + 4 + 7 * mc ∧
      (∀ k < mc, ix k < m ∧ en (ix k) ∈ Bc) ∧ (∀ y ∈ Bc, ∃ k < mc, en (ix k) = y) ∧
      (∀ k k', k < k' → k' < mc → ix k < ix k') ∧
      c'.nmem dc = mc ∧ c'.nmem (dc + 1) = kc ∧ c'.nmem (dc + 2) = tg ∧ c'.nmem (dc + 3) = Z ∧
      (∀ k < mc, c'.nmem (dc + 4 + k) = c.nmem (d + 4 + ix k)) ∧
      (∀ k < mc, c'.nmem (dc + 4 + mc + k) < mc ∧
        en (ix (c'.nmem (dc + 4 + mc + k))) = M.rev (en (ix k))) ∧
      (∀ k < mc, c'.nmem (dc + 4 + 2 * mc + k) < mc ∧
        en (ix (c'.nmem (dc + 4 + 2 * mc + k))) = childRot M σ B L Bc (en (ix k))) ∧
      (∀ k < mc, c'.nmem (dc + 4 + 3 * mc + k) = c.nmem (d + 4 + 3 * m + ix k)) ∧
      (∀ k < mc, c'.nmem (dc + 4 + 4 * mc + k) = c.nmem (KCb + ix k)) ∧
      (∀ k < mc, c'.nmem (dc + 4 + 5 * mc + k) = c.nmem (HCb + ix k)) ∧
      (∀ a, (a < dc ∨ (dc + 4 + 7 * m ≤ a ∧ a < Tb) ∨ A + 11 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6200 ∨ (6328 < x ∧ x < 6580) ∨ 6599 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, hmc, h06, hIX, hIXs, hOUT, hCI, m1, a98, a80, a81, a83, a88, a89, a90,
    n1, rr1, rm1, ro1⟩ := sfFront_exec (P := P) M σ B L Bc c hc r60 r61 r62 r63 r64 r65 he heB
    hBe hσ hrB hrL hBc hSG hRV hPF hFx hid (by omega) (by omega) (by omega) (by omega) w
    (by omega)
  have q : ∀ x, (x < 6200 ∨ (6328 < x ∧ x < 6580) ∨ 6599 < x) → c₁.nreg x = c.nreg x := n1
  have mA : ∀ x, ¬ (A ≤ x ∧ x < A + 11 * m) → c₁.nmem x = c.nmem x := m1
  obtain ⟨c₂, k₂, e₂, hk₂, d97, h0, h1, h2, h3, g1, g2, g3, g4, g5, g6, m2, n2, rr2, rm2, ro2⟩ :=
    sfBack_exec (P := P) c₁ e₁.wb_right (m := m) (mc := c₁.nreg 6306) (d := d) (A := A)
      (IDb := IDb) (Tb := Tb) (KCb := KCb) (HCb := HCb) (dc := dc) (kc := kc) (tg := tg) (Z := Z)
      (by rw [q _ (by omega), r69]) a98 rfl (by rw [q _ (by omega), r70])
      (by rw [q _ (by omega), r71]) (by rw [q _ (by omega), r72]) a89 a80 a81
      (by rw [q _ (by omega), r66]) a88 (by rw [q _ (by omega), r63]) a90 a83
      (by rw [q _ (by omega), r67]) (by rw [q _ (by omega), r68]) hmc
      (fun k hk => (hIX k hk).1) (fun i hi => by rw [mA _ (by omega)]; exact (hRV i hi).1)
      (fun j hj => by rw [mA _ (by omega)]; exact hid j hj)
      o0 o1 o4 o5 o6 o9 o10 o11 w (by omega)
  have hFl' : ∀ i < m, (0 < c.nmem (Fxb + i) ↔ en i ∈ Bc) := fun i hi => by
    rw [hFx i hi]; split_ifs with h <;> simp [h]
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, c₁.nreg 6306, fun k => c₁.nmem (A + 9 * m + k),
    hmc, d97, hIX, hIXs, ?_, h0, h1, h2, h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [rr2, rr1],
    by rw [rm2, rm1], by rw [ro2, ro1]⟩
  · intro k k' hk hk'
    have hk'' : k' < cnt (fun j => c.nmem (Fxb + j)) m := by rw [← h06]; exact hk'
    obtain ⟨i, hi, hFi, rfl⟩ := cnt_surj (fun j => c.nmem (Fxb + j)) m k (by omega)
    obtain ⟨i', hi', hFi', rfl⟩ := cnt_surj (fun j => c.nmem (Fxb + j)) m _ hk''
    show c₁.nmem (A + 9 * m + _) < c₁.nmem (A + 9 * m + _)
    rw [(hCI i hi ((hFl' i hi).1 hFi)).2, (hCI i' hi' ((hFl' i' hi').1 hFi')).2]
    by_contra hle
    have := cnt_mono (fun j => c.nmem (Fxb + j)) (show i' ≤ i by omega)
    omega
  · intro k hk
    have := (hIX k hk).1
    rw [g1 k hk, mA _ (by omega)]
  · intro k hk
    obtain ⟨hk1, hkB⟩ := hIX k hk
    obtain ⟨hp, ep⟩ := hRV _ hk1
    have hpB : en (c.nmem (d + 4 + m + c₁.nmem (A + 9 * m + k))) ∈ Bc := by
      rw [ep]; exact hBcr _ hkB
    obtain ⟨c1, c2⟩ := hCI _ hp hpB
    rw [g2 k hk, mA (d + 4 + m + c₁.nmem (A + 9 * m + k)) (by omega), c1]
    refine ⟨?_, ?_⟩
    · rw [h06]; exact cnt_lt_of _ hp ((hFl' _ hp).2 hpB)
    · show en (c₁.nmem (A + 9 * m + _)) = _
      rw [c2, ep]
  · intro k hk
    rw [g3 k hk]; exact hOUT k hk
  · intro k hk
    have := (hIX k hk).1
    rw [g4 k hk, mA _ (by omega)]
  · intro k hk
    have := (hIX k hk).1
    rw [g5 k hk, mA _ (by omega)]
  · intro k hk
    have := (hIX k hk).1
    rw [g6 k hk, mA _ (by omega)]
  · intro a ha
    rw [m2 a (by omega) (by omega), mA a (by omega)]
  · intro x hx
    rw [n2 x (by omega), q x hx]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
