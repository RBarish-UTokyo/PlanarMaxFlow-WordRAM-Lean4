module

public import PlanarFlow.BKMNW.NcHfX
public import PlanarFlow.BKMNW.NcWz
public import PlanarFlow.BKMNW.NcS2c
public import PlanarFlow.BKMNW.NcScanRun
public import PlanarFlow.BKMNW.NcRb
public import PlanarFlow.BKMNW.NcTfRun
public import PlanarFlow.BKMNW.NpDiv

/-!
# The heads of `c2sP` and `s2cP`: the glue blocks

The head reads the frame at `d` (`r3004`): `m = mem[d]`, `Z = mem[d + 3]`, and `b = r3006 − 5`,
and lays out its arrays above `b` (in words, from `b`):

`CPg (m) | LAB DV DG (3m) | VM (m+1) | CF (m) | rbP scratch (10m+8, MK at +8m+4) | CAP | BT | DF |
hfA | hfB (m each) | VM2 (m+1) | HF (m) | O (m) | p (stRm m) | F1 FF G PB (4m) | Sb`

with **`stRm m = 4·10⁹ m² + 9`** (a bound of the scratch of `stCallZ`). The registers of the head
are `9830 … 9879` (`HdScr`): `9830` capacities base (`CPb`), `9831` `d`, `9832` `m`, `9833` `Z`,
`9834` `b`, `9835 … 9855` the bases, `9874 … 9878` the frame's `RV`, `SG`, `FL`, `HL`, `CP`.

Blocks (each with its exec lemma): `hdA` (`d`, `m`, `Z`, `b`, `2Z`), `hdQ0`, `sqB`, `hdQ1`
(`ib = wzQ m Z + 339 m + 128` in `r9813`: `q = m + Z + 100` squared five times), `hdB1 … hdB4`
(the bases), `hdCc`/`hdCs` (the capacity base for `c2s`/`s2c`), `tfGl` (the arguments of `tfP` for
the part whose index is in a register, read from `SegsOut'`), `rbGl`, `scGl`, `dfGl`, `hfGl`,
`jjGl` (the part `j + 1 + (i − #pholes)`), `tlGl` (the registers of the tail), `gaGl` (the
gather of `U ∘ rev` for `s2c`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The scratch registers of the head. -/
def HdScr (r : ℕ) : Prop := 9830 ≤ r ∧ r ≤ 9879

/-- The room of the scratch of `stCallZ`: `4·10⁹ m² + 9`. -/
def stRm (m : ℕ) : ℕ := 4000000000 * (m * m) + 9

/-! ### The blocks -/

/-- `d`, `m`, `Z`, `b`, and the tail's `m`, `d`, `2Z`. -/
def hdA : Stmt :=
  block [.copyN 9831 3004, .loadN 9832 9831, .constN 9860 3, .addN 9861 9831 9860,
    .loadN 9833 9861, .constN 9860 5, .subN 9834 3006 9860, .copyN 9818 9832, .copyN 9819 9831,
    .addN 9816 9833 9833]

/-- `q = m + Z + 100`. -/
def hdQ0 : Stmt := block [.constN 9860 100, .addN 9862 9832 9833, .addN 9862 9862 9860]

/-- `t := t · t`. -/
def sqB : Stmt := block [.mulN 9862 9862 9862]

/-- `ib = t + 339 m + 128`. -/
def hdQ1 : Stmt :=
  block [.constN 9860 339, .mulN 9863 9832 9860, .addN 9863 9863 9862, .constN 9860 128,
    .addN 9813 9863 9860]

/-- **`ib = wzQ m Z + 339 m + 128`.** -/
def hdQ : Stmt := .seq hdQ0 (.seq sqB (.seq sqB (.seq sqB (.seq sqB (.seq sqB hdQ1)))))

/-- The frame's arrays: `RV`, `SG`, `CP`, `HL`, `FL`. -/
def hdB1 : Stmt :=
  block [.constN 9860 4, .addN 9874 9831 9860, .addN 9874 9874 9832, .addN 9875 9874 9832,
    .addN 9878 9875 9832, .addN 9877 9878 9832, .addN 9877 9877 9832, .addN 9876 9877 9832]

/-- The bases `LAB … CAP`. -/
def hdB2 : Stmt :=
  block [.constN 9860 1, .addN 9835 9834 9832, .addN 9836 9835 9832, .addN 9837 9836 9832,
    .addN 9838 9837 9832, .addN 9839 9838 9832, .addN 9839 9839 9860, .addN 9840 9839 9832,
    .constN 9860 8, .mulN 9864 9832 9860, .addN 9841 9840 9864, .constN 9860 4,
    .addN 9841 9841 9860, .addN 9842 9841 9832, .addN 9842 9842 9832, .addN 9842 9842 9860]

/-- The bases `BT … p`. -/
def hdB3 : Stmt :=
  block [.constN 9860 1, .addN 9843 9842 9832, .addN 9844 9843 9832, .addN 9845 9844 9832,
    .addN 9846 9845 9832, .addN 9847 9846 9832, .addN 9848 9847 9832, .addN 9848 9848 9860,
    .addN 9849 9848 9832, .addN 9850 9849 9832]

/-- The bases `F1 … Sb`. -/
def hdB4 : Stmt :=
  block [.mulN 9864 9832 9832, .constN 9860 4000000000, .mulN 9864 9864 9860, .constN 9860 9,
    .addN 9864 9864 9860, .addN 9851 9850 9864, .addN 9852 9851 9832, .addN 9853 9852 9832,
    .addN 9854 9853 9832, .addN 9855 9854 9832]

/-- **The frame and the bases.** -/
def hdF : Stmt := .seq hdA (.seq hdQ (.seq hdB1 (.seq hdB2 (.seq hdB3 hdB4))))

/-- The capacities of `c2s`: the frame's. -/
def hdCc : Stmt := block [.copyN 9830 9878]

/-- The capacities of `s2c`: the gathered array at `b`. -/
def hdCs : Stmt := block [.copyN 9830 9834]

/-- The arguments of `tfP` for the part whose index is in `rj` (from `SegsOut'` at `r6807`), with
the scratch `Vr` and the output `Fr`. -/
def tfGl (rj Vr Fr : ℕ) : Stmt :=
  block [.copyN 9856 6807, .loadN 9857 9856, .addN 9865 9856 9857, .loadN 9866 9865,
    .addN 9865 9865 9857, .loadN 9867 9865, .addN 9858 9866 9867,
    .constN 9860 1, .addN 9868 9856 9860, .addN 9868 9868 9857, .addN 9868 9868 9857,
    .addN 9869 9856 9860, .addN 9869 9869 rj, .loadN 9870 9869, .addN 9702 9868 9870,
    .addN 9869 9869 9857, .loadN 9703 9869,
    .addN 9871 9868 9858, .addN 9871 9871 rj, .loadN 9714 9871,
    .copyN 9700 9832, .copyN 9701 9835, .copyN 9704 Vr, .copyN 9705 Fr, .copyN 9713 9874]

/-- The arguments of `rbP`. -/
def rbGl : Stmt :=
  block [.copyN 9600 9832, .copyN 9601 9876, .copyN 9602 9830, .copyN 9603 9833,
    .copyN 9604 9839, .copyN 9605 9835, .copyN 9606 9836, .copyN 9607 9837, .copyN 9608 9875,
    .copyN 9609 9874, .copyN 9610 9840, .constN 9860 2, .addN 9879 9832 9860,
    .addN 9611 9840 9879, .addN 9612 9611 9879, .addN 9613 9612 9832, .addN 9613 9613 9832,
    .addN 9613 9613 9832, .addN 9614 9613 9832, .addN 9614 9614 9832, .addN 9614 9614 9832,
    .addN 9615 9614 9879]

/-- The arguments of `scP`. -/
def scGl : Stmt :=
  block [.copyN 9732 9839, .copyN 9733 9841, .copyN 9734 9874, .copyN 9735 9830,
    .copyN 9736 9876, .copyN 9737 9835, .copyN 9738 9836, .copyN 9739 9837, .copyN 9740 9842,
    .copyN 9741 9843, .copyN 9742 9833, .copyN 9743 9832]

/-- The arguments of `dfL` (`DF = CF ∸ CF · MK`). -/
def dfGl : Stmt :=
  block [.copyN 9792 9839, .copyN 9793 9841, .copyN 9794 9844, .constN 9795 0, .copyN 9796 9832]

/-- The arguments of `hfP`. -/
def hfGl : Stmt :=
  block [.copyN 9757 9832, .copyN 9758 9877, .copyN 9759 6802, .copyN 9760 9845,
    .copyN 9761 9846, .copyN 9762 9848]

/-- The part `j + 1 + (i − #pholes)`. -/
def jjGl : Stmt := block [.constN 9860 1, .addN 9872 6800 9860, .subN 9873 6802 9780,
  .addN 9872 9872 9873]

/-- The registers of the tail. -/
def tlGl : Stmt :=
  block [.copyN 9800 9851, .copyN 9801 9844, .copyN 9802 9830, .copyN 9803 9852,
    .copyN 9804 9855, .copyN 9805 9843, .copyN 9806 9853, .copyN 9807 9854, .copyN 9808 9855,
    .copyN 9810 9842, .copyN 9811 9839, .copyN 9812 9848, .copyN 9814 9849, .copyN 9815 9850]

/-- The arguments of the gather `CPg[i] = CP[RV i]` (`lgProg`). -/
def gaGl : Stmt := block [.copyN 6210 9832, .copyN 6211 9874, .copyN 6212 9878, .copyN 6213 9834]

/-! ### The exec lemmas of the blocks -/

variable {P : Input} {W : ℕ}

theorem hdA_exec (c : Config) (hc : WordsBounded W c) {d b m Z : ℕ}
    (r04 : c.nreg 3004 = d) (r06 : c.nreg 3006 = b + 5) (hm : c.nmem d = m)
    (hZ : c.nmem (d + 3) = Z) (w1 : d + 3 ≤ W) (w2 : 2 * Z ≤ W) (w3 : 5 ≤ W) :
    ∃ c' k, Exec P W hdA c c' k ∧ k = 10 ∧ c'.nreg 9831 = d ∧ c'.nreg 9832 = m ∧
      c'.nreg 9833 = Z ∧ c'.nreg 9834 = b ∧ c'.nreg 9818 = m ∧ c'.nreg 9819 = d ∧
      c'.nreg 9816 = 2 * Z ∧
      (∀ r, ¬ (9831 ≤ r ∧ r ≤ 9834) → r ≠ 9860 → r ≠ 9861 → r ≠ 9816 → r ≠ 9818 → r ≠ 9819 →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hdA
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, r06, hm, hZ]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r04, r06, hm, hZ])
  all_goals (try unfold HdScr at h1)
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

theorem hdQ0_exec (c : Config) (hc : WordsBounded W c) {m Z : ℕ}
    (r32 : c.nreg 9832 = m) (r33 : c.nreg 9833 = Z) (w : wzq m Z ≤ W) :
    ∃ c' k, Exec P W hdQ0 c c' k ∧ k = 3 ∧ c'.nreg 9862 = wzq m Z ∧
      (∀ r, r ≠ 9860 → r ≠ 9862 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hdQ0
  exec_block
  all_goals try ((try config_simp); (try simp only [r32, r33]); unfold wzq at w; omega)
  refine ⟨rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r32, r33])
  all_goals (try unfold HdScr at h1)
  all_goals (try unfold wzq)
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

theorem sqB_exec (c : Config) (hc : WordsBounded W c) {t : ℕ}
    (r62 : c.nreg 9862 = t) (w : t * t ≤ W) :
    ∃ c' k, Exec P W sqB c c' k ∧ k = 1 ∧ c'.nreg 9862 = t * t ∧
      (∀ r, r ≠ 9862 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sqB
  exec_block
  all_goals try ((try config_simp); (try simp only [r62]); exact w)
  refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r62])
  all_goals (try unfold HdScr at h1)
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

theorem hdQ1_exec (c : Config) (hc : WordsBounded W c) {m t : ℕ}
    (r32 : c.nreg 9832 = m) (r62 : c.nreg 9862 = t) (w : t + 339 * m + 128 ≤ W) (w3 : 339 ≤ W) :
    ∃ c' k, Exec P W hdQ1 c c' k ∧ k = 5 ∧ c'.nreg 9813 = t + 339 * m + 128 ∧
      (∀ r, r ≠ 9860 → r ≠ 9863 → r ≠ 9813 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hdQ1
  exec_block
  all_goals try ((try config_simp); (try simp only [r32, r62]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r32, r62])
  all_goals (try unfold HdScr at h1)
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

/-- **`ib = wzQ m Z + 339 m + 128`** in `r9813`. -/
theorem hdQ_exec (c : Config) (hc : WordsBounded W c) {m Z : ℕ}
    (r32 : c.nreg 9832 = m) (r33 : c.nreg 9833 = Z) (w : wzQ m Z + 339 * m + 128 ≤ W)
    (w3 : 339 ≤ W) :
    ∃ c' k, Exec P W hdQ c c' k ∧ k = 13 ∧ c'.nreg 9813 = wzQ m Z + 339 * m + 128 ∧
      (∀ r, r ≠ 9860 → r ≠ 9862 → r ≠ 9863 → r ≠ 9813 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set q := wzq m Z with hq
  have hq1 : 1 ≤ q := by rw [hq]; unfold wzq; omega
  have hQ : wzQ m Z = q ^ 32 := rfl
  have pw : ∀ k, k ≤ 32 → q ^ k ≤ W := fun k hk =>
    le_trans (Nat.pow_le_pow_right hq1 hk) (by rw [← hQ]; omega)
  obtain ⟨c₀, k₀, e₀, hk₀, t₀, g₀, m₀, rr₀, rm₀, o₀⟩ := hdQ0_exec (P := P) c hc r32 r33
    (by have := pw 1 (by omega); rw [pow_one] at this; exact this)
  obtain ⟨c₁, k₁, e₁, hk₁, t₁, g₁, m₁, rr₁, rm₁, o₁⟩ := sqB_exec (P := P) c₀ e₀.wb_right t₀
    (by have := pw 2 (by omega); rw [pow_two] at this; exact this)
  obtain ⟨c₂, k₂, e₂, hk₂, t₂, g₂, m₂, rr₂, rm₂, o₂⟩ := sqB_exec (P := P) c₁ e₁.wb_right t₁
    (by have := pw 4 (by omega); rw [show q ^ 4 = q * q * (q * q) by ring] at this; exact this)
  obtain ⟨c₃, k₃, e₃, hk₃, t₃, g₃, m₃, rr₃, rm₃, o₃⟩ := sqB_exec (P := P) c₂ e₂.wb_right t₂
    (by have := pw 8 (by omega)
        rw [show q ^ 8 = q * q * (q * q) * (q * q * (q * q)) by ring] at this; exact this)
  obtain ⟨c₄, k₄, e₄, hk₄, t₄, g₄, m₄, rr₄, rm₄, o₄⟩ := sqB_exec (P := P) c₃ e₃.wb_right t₃
    (by have := pw 16 (by omega)
        rw [show q ^ 16 = q * q * (q * q) * (q * q * (q * q)) *
          (q * q * (q * q) * (q * q * (q * q))) by ring] at this; exact this)
  obtain ⟨c₅, k₅, e₅, hk₅, t₅, g₅, m₅, rr₅, rm₅, o₅⟩ := sqB_exec (P := P) c₄ e₄.wb_right t₄
    (by have := pw 32 (by omega)
        rw [show q ^ 32 = q * q * (q * q) * (q * q * (q * q)) *
          (q * q * (q * q) * (q * q * (q * q))) *
          (q * q * (q * q) * (q * q * (q * q)) *
          (q * q * (q * q) * (q * q * (q * q)))) by ring] at this; exact this)
  have hs : ∀ r, r ≠ 9860 → r ≠ 9862 → c₅.nreg r = c.nreg r := fun r h h' => by
    rw [g₅ r h', g₄ r h', g₃ r h', g₂ r h', g₁ r h', g₀ r h h']
  have e32 : q * q * (q * q) * (q * q * (q * q)) * (q * q * (q * q) * (q * q * (q * q))) *
      (q * q * (q * q) * (q * q * (q * q)) * (q * q * (q * q) * (q * q * (q * q)))) =
      wzQ m Z := by rw [hQ]; ring
  rw [e32] at t₅
  obtain ⟨c₆, k₆, e₆, hk₆, t₆, g₆, m₆, rr₆, rm₆, o₆⟩ := hdQ1_exec (P := P) c₅ e₅.wb_right
    (by rw [hs _ (by omega) (by omega), r32]) t₅ w w3
  refine ⟨c₆, k₀ + (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆))))),
    e₀.seq (e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq e₆))))), by omega, t₆,
    fun r h1 h2 h3 h4 => by rw [g₆ r h1 h3 h4, hs r h1 h2], ?_, ?_, ?_, ?_⟩
  · rw [m₆, m₅, m₄, m₃, m₂, m₁, m₀]
  · rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁, rr₀]
  · rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁, rm₀]
  · rw [o₆, o₅, o₄, o₃, o₂, o₁, o₀]

theorem hdB1_exec (c : Config) (hc : WordsBounded W c) {d m : ℕ}
    (r31 : c.nreg 9831 = d) (r32 : c.nreg 9832 = m) (w : d + 4 + 6 * m ≤ W) :
    ∃ c' k, Exec P W hdB1 c c' k ∧ k = 8 ∧ c'.nreg 9874 = d + 4 + m ∧
      c'.nreg 9875 = d + 4 + 2 * m ∧ c'.nreg 9878 = d + 4 + 3 * m ∧
      c'.nreg 9877 = d + 4 + 5 * m ∧ c'.nreg 9876 = d + 4 + 6 * m ∧
      (∀ r, r ≠ 9860 → r ≠ 9874 → r ≠ 9875 → r ≠ 9876 → r ≠ 9877 → r ≠ 9878 →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hdB1
  exec_block
  all_goals try ((try config_simp); (try simp only [r31, r32]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r31, r32])
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

theorem hdB2_exec (c : Config) (hc : WordsBounded W c) {b m : ℕ}
    (r32 : c.nreg 9832 = m) (r34 : c.nreg 9834 = b) (w : b + 16 * m + 9 ≤ W) (w8 : 8 ≤ W) :
    ∃ c' k, Exec P W hdB2 c c' k ∧ k = 16 ∧ c'.nreg 9835 = b + m ∧
      c'.nreg 9836 = b + 2 * m ∧ c'.nreg 9837 = b + 3 * m ∧ c'.nreg 9838 = b + 4 * m ∧
      c'.nreg 9839 = b + 5 * m + 1 ∧ c'.nreg 9840 = b + 6 * m + 1 ∧
      c'.nreg 9841 = b + 14 * m + 5 ∧ c'.nreg 9842 = b + 16 * m + 9 ∧
      (∀ r, ¬ (9835 ≤ r ∧ r ≤ 9842) → r ≠ 9860 → r ≠ 9864 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hdB2
  exec_block
  all_goals try ((try config_simp); (try simp only [r32, r34]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r32, r34])
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

theorem hdB3_exec (c : Config) (hc : WordsBounded W c) {b m : ℕ}
    (r32 : c.nreg 9832 = m) (r42 : c.nreg 9842 = b + 16 * m + 9) (w : b + 24 * m + 10 ≤ W) :
    ∃ c' k, Exec P W hdB3 c c' k ∧ k = 10 ∧ c'.nreg 9843 = b + 17 * m + 9 ∧
      c'.nreg 9844 = b + 18 * m + 9 ∧ c'.nreg 9845 = b + 19 * m + 9 ∧
      c'.nreg 9846 = b + 20 * m + 9 ∧ c'.nreg 9847 = b + 21 * m + 9 ∧
      c'.nreg 9848 = b + 22 * m + 10 ∧ c'.nreg 9849 = b + 23 * m + 10 ∧
      c'.nreg 9850 = b + 24 * m + 10 ∧
      (∀ r, ¬ (9843 ≤ r ∧ r ≤ 9850) → r ≠ 9860 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hdB3
  exec_block
  all_goals try ((try config_simp); (try simp only [r32, r42]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r32, r42])
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

theorem hdB4_exec (c : Config) (hc : WordsBounded W c) {p m : ℕ}
    (r32 : c.nreg 9832 = m) (r50 : c.nreg 9850 = p) (w : p + stRm m + 4 * m ≤ W)
    (w3 : 4000000000 ≤ W) :
    ∃ c' k, Exec P W hdB4 c c' k ∧ k = 10 ∧ c'.nreg 9851 = p + stRm m ∧
      c'.nreg 9852 = p + stRm m + m ∧ c'.nreg 9853 = p + stRm m + 2 * m ∧
      c'.nreg 9854 = p + stRm m + 3 * m ∧ c'.nreg 9855 = p + stRm m + 4 * m ∧
      (∀ r, ¬ (9851 ≤ r ∧ r ≤ 9855) → r ≠ 9860 → r ≠ 9864 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hp : 4000000000 * (m * m) + 9 = stRm m := rfl
  have e1 : m * m * 4000000000 = 4000000000 * (m * m) := by ring
  unfold hdB4
  exec_block
  all_goals try ((try config_simp); (try simp only [r32, r50]); (try rw [e1]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r32, r50])
  all_goals (try rw [e1])
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

theorem hdCc_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W hdCc c c' k ∧ k = 1 ∧ c'.nreg 9830 = c.nreg 9878 ∧
      (∀ r, r ≠ 9830 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hdCc
  exec_block
  refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

theorem hdCs_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W hdCs c c' k ∧ k = 1 ∧ c'.nreg 9830 = c.nreg 9834 ∧
      (∀ r, r ≠ 9830 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hdCs
  exec_block
  refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

/-- The registers written by `tfGl` outside the head's scratch. -/
def TfGo (r : ℕ) : Prop := (9700 ≤ r ∧ r ≤ 9705) ∨ r = 9713 ∨ r = 9714

theorem tfGl_exec (c : Config) (hc : WordsBounded W c) {rj Vr Fr Gb s jj m LAB RV V F : ℕ}
    (hrj : 9830 ≤ rj ∨ rj < 9700) (hrj' : rj ≠ 9856 ∧ rj ≠ 9857 ∧ rj ≠ 9858 ∧ rj ≠ 9860 ∧
      rj ≠ 9865 ∧ rj ≠ 9866 ∧ rj ≠ 9867 ∧ rj ≠ 9868 ∧ rj ≠ 9869 ∧ rj ≠ 9870 ∧ rj ≠ 9871)
    (hV : 9830 ≤ Vr ∧ Vr < 9856) (hF : 9830 ≤ Fr ∧ Fr < 9856)
    (r07 : c.nreg 6807 = Gb) (hs : c.nmem Gb = s) (rjj : c.nreg rj = jj)
    (r32 : c.nreg 9832 = m) (r35 : c.nreg 9835 = LAB) (r74 : c.nreg 9874 = RV)
    (rV : c.nreg Vr = V) (rF : c.nreg Fr = F)
    (w1 : Gb + 1 + s + s + (c.nmem (Gb + s) + c.nmem (Gb + s + s)) + jj ≤ W)
    (w2 : Gb + 1 + s + s + c.nmem (Gb + 1 + jj) ≤ W) (w3 : Gb + 1 + jj + s ≤ W) :
    ∃ c' k, Exec P W (tfGl rj Vr Fr) c c' k ∧ k = 25 ∧ c'.nreg 9700 = m ∧
      c'.nreg 9701 = LAB ∧ c'.nreg 9702 = Gb + 1 + s + s + c.nmem (Gb + 1 + jj) ∧
      c'.nreg 9703 = c.nmem (Gb + 1 + jj + s) ∧ c'.nreg 9704 = V ∧ c'.nreg 9705 = F ∧
      c'.nreg 9713 = RV ∧
      c'.nreg 9714 = c.nmem (Gb + 1 + s + s + (c.nmem (Gb + s) + c.nmem (Gb + s + s)) + jj) ∧
      (∀ r, ¬ TfGo r → ¬ (9856 ≤ r ∧ r ≤ 9871) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hrj'
  unfold tfGl
  exec_block
  all_goals try ((try config_simp); (try simp (disch := omega) only [upd_other, upd_same]); (try simp only [r07, hs, rjj, r32, r35, r74, rV, rF]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp (disch := omega) only [upd_other, upd_same])
  all_goals (try simp only [r07, hs, rjj, r32, r35, r74, rV, rF])
  all_goals (try unfold TfGo at h1)
  all_goals (try omega)
  all_goals (try (congr 1; omega))
  all_goals (simp (disch := omega) only [upd_other])

/-- The registers written by `rbGl` outside the head's scratch. -/
def RbGo (r : ℕ) : Prop := 9600 ≤ r ∧ r ≤ 9615

theorem rbGl_exec (c : Config) (hc : WordsBounded W c) {m S : ℕ}
    (r32 : c.nreg 9832 = m) (r40 : c.nreg 9840 = S) (w : S + 3 * (m + 2) + 6 * m ≤ W) :
    ∃ c' k, Exec P W rbGl c c' k ∧ k = 22 ∧ c'.nreg 9600 = m ∧
      c'.nreg 9601 = c.nreg 9876 ∧ c'.nreg 9602 = c.nreg 9830 ∧ c'.nreg 9603 = c.nreg 9833 ∧
      c'.nreg 9604 = c.nreg 9839 ∧ c'.nreg 9605 = c.nreg 9835 ∧ c'.nreg 9606 = c.nreg 9836 ∧
      c'.nreg 9607 = c.nreg 9837 ∧ c'.nreg 9608 = c.nreg 9875 ∧ c'.nreg 9609 = c.nreg 9874 ∧
      c'.nreg 9610 = S ∧ c'.nreg 9611 = S + (m + 2) ∧ c'.nreg 9612 = S + 2 * (m + 2) ∧
      c'.nreg 9613 = S + 2 * (m + 2) + 3 * m ∧ c'.nreg 9614 = S + 2 * (m + 2) + 6 * m ∧
      c'.nreg 9615 = S + 3 * (m + 2) + 6 * m ∧
      (∀ r, ¬ RbGo r → r ≠ 9860 → r ≠ 9879 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rbGl
  exec_block
  all_goals try ((try config_simp); (try simp only [r32, r40]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r32, r40])
  all_goals (try unfold RbGo at h1)
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

theorem scGl_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W scGl c c' k ∧ k = 12 ∧ c'.nreg 9732 = c.nreg 9839 ∧
      c'.nreg 9733 = c.nreg 9841 ∧ c'.nreg 9734 = c.nreg 9874 ∧ c'.nreg 9735 = c.nreg 9830 ∧
      c'.nreg 9736 = c.nreg 9876 ∧ c'.nreg 9737 = c.nreg 9835 ∧ c'.nreg 9738 = c.nreg 9836 ∧
      c'.nreg 9739 = c.nreg 9837 ∧ c'.nreg 9740 = c.nreg 9842 ∧ c'.nreg 9741 = c.nreg 9843 ∧
      c'.nreg 9742 = c.nreg 9833 ∧ c'.nreg 9743 = c.nreg 9832 ∧
      (∀ r, ¬ (9732 ≤ r ∧ r ≤ 9743) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold scGl
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

theorem dfGl_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W dfGl c c' k ∧ k = 5 ∧ c'.nreg 9792 = c.nreg 9839 ∧
      c'.nreg 9793 = c.nreg 9841 ∧ c'.nreg 9794 = c.nreg 9844 ∧ c'.nreg 9795 = 0 ∧
      c'.nreg 9796 = c.nreg 9832 ∧
      (∀ r, ¬ (9792 ≤ r ∧ r ≤ 9796) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dfGl
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

theorem hfGl_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W hfGl c c' k ∧ k = 6 ∧ c'.nreg 9757 = c.nreg 9832 ∧
      c'.nreg 9758 = c.nreg 9877 ∧ c'.nreg 9759 = c.nreg 6802 ∧ c'.nreg 9760 = c.nreg 9845 ∧
      c'.nreg 9761 = c.nreg 9846 ∧ c'.nreg 9762 = c.nreg 9848 ∧
      (∀ r, ¬ (9757 ≤ r ∧ r ≤ 9762) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hfGl
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

theorem jjGl_exec (c : Config) (hc : WordsBounded W c) {j i n : ℕ}
    (r00 : c.nreg 6800 = j) (r02 : c.nreg 6802 = i) (r80 : c.nreg 9780 = n)
    (w : j + 1 + (i - n) ≤ W) :
    ∃ c' k, Exec P W jjGl c c' k ∧ k = 4 ∧ c'.nreg 9872 = j + 1 + (i - n) ∧
      (∀ r, r ≠ 9860 → r ≠ 9872 → r ≠ 9873 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold jjGl
  exec_block
  all_goals try ((try config_simp); (try simp only [r00, r02, r80]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r00, r02, r80])
  all_goals (try unfold HdScr at h1)
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

theorem tlGl_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W tlGl c c' k ∧ k = 14 ∧ c'.nreg 9800 = c.nreg 9851 ∧
      c'.nreg 9801 = c.nreg 9844 ∧ c'.nreg 9802 = c.nreg 9830 ∧ c'.nreg 9803 = c.nreg 9852 ∧
      c'.nreg 9804 = c.nreg 9855 ∧ c'.nreg 9805 = c.nreg 9843 ∧ c'.nreg 9806 = c.nreg 9853 ∧
      c'.nreg 9807 = c.nreg 9854 ∧ c'.nreg 9808 = c.nreg 9855 ∧ c'.nreg 9810 = c.nreg 9842 ∧
      c'.nreg 9811 = c.nreg 9839 ∧ c'.nreg 9812 = c.nreg 9848 ∧ c'.nreg 9814 = c.nreg 9849 ∧
      c'.nreg 9815 = c.nreg 9850 ∧
      (∀ r, ¬ (9800 ≤ r ∧ r ≤ 9815) → c'.nreg r = c.nreg r) ∧
      (∀ r, r = 9813 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tlGl
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 => ?_,
    fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

theorem gaGl_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W gaGl c c' k ∧ k = 4 ∧ c'.nreg 6210 = c.nreg 9832 ∧
      c'.nreg 6211 = c.nreg 9874 ∧ c'.nreg 6212 = c.nreg 9878 ∧ c'.nreg 6213 = c.nreg 9834 ∧
      (∀ r, ¬ (6210 ≤ r ∧ r ≤ 6213) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold gaGl
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try omega)
  all_goals (simp (disch := omega) only [upd_other])

end NcStep

end BKMNW

end PlanarFlow
