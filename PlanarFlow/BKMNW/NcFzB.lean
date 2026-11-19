module

public import PlanarFlow.BKMNW.NcFzA
public import PlanarFlow.BKMNW.NpDiv
public import PlanarFlow.BKMNW.LinCmp

/-!
# The pendant frame writer `pfP`: the program and its glue blocks

From the frame of a call at `d` (`r3004`; `m = mem[d]`, `Z = mem[d + 3]`, `RV = d + 4 + m`,
`SG = d + 4 + 2m`) and the arrays `F1 = Z + f₁` (`r9800`), `DF = [tail ∈ Del]` (`r9801`),
`CP = U` (`r9802`), with the scratch base `S = r9804`, `pfP` writes the frame of the map with a
pendant edge at every vertex at `d' = S + 12 + 16m` (`m' = m + 2n` darts, `n` the number of
vertices; the darts of the map first, then `(v, true)` at `m + t`, then `(v, false)` at
`m + n + t` for the vertex `v` of number `t`), with offset `Z' = m Z`.

**Scratch layout** (`S = r9804`, all arrays of length `m` unless said):
`S … S + 7` saved values (`d`, the heap top `r3006`, `m`, `Z`, `Z'`, the base of `Q`, the base of
`FL'`); `d0 = S + 8` a fake frame for `dvP` (`mem[d0] = m`, `SG` copied at
`d0 + 4 + 2m`, `X0 = d0 + 4 + 6m` its flow array); `A = d0 + 4 + 7m`: `LAB = A`, `DV = A + m`,
`DG = A + 2m` (`dvP`), `RF = A + 3m` (representative flags), `CI = A + 4m`, `IX = A + 5m`
(`lkProg`), `Q = A + 6m` (`[dart touches Del]`), `DVr = A + 7m`, `ZG = A + 8m` (per vertex),
`d' = A + 9m` (the pendant frame).

**Layout registers**: `9930 m`, `9931 n`, `9950 d`, `9951 Z`, `9952 Z'`, `9953 RV`, `9954 SG`,
`9955 CP`, `9956 F1`, `9957 DF`, `9958 S`, `9959 d0`, `9960 SG0`, `9961 X0`, `9962 A`, `9963 DV`,
`9964 DG`, `9965 RF`, `9966 CI`, `9967 IX`, `9968 Q`, `9969 DVr`, `9970 ZG`, `9971 d'`, `9972 0`,
`9973 m'`, `9974 RV'`, `9975 SG'`, `9976 CP'`, `9977 FL'`, `9978 m + n`, `9979 d' + 4 + 7m'`,
`9980 … 9987` the bases of the pendant blocks (`RV' + m`, `RV' + m + n`, `SG' + m`, …),
`9988 1`.

The program: `pfS1` (registers, saved values, `SG0 := SG`, `Q`, `X0 := Q ? F1 : Z`), `pfS2`
(`dvP` on the fake frame, `RF := LAB ∸ i`, `lkProg`, the registers of the pendant frame and its
header), `pfS3` (`DVr`, `ZG`, `RV'`, `SG'`), `pfS4` (`CP'`, `FL'`); **`pfP = pfS1 ; pfS2 ; pfS3 ;
pfS4`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcFz

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### The blocks -/

/-- The layout registers, part 1. -/
def pfA1 : Stmt :=
  block [.copyN 9950 3004, .loadN 9930 9950, .constN 9940 3, .addN 9941 9950 9940,
    .loadN 9951 9941, .mulN 9952 9930 9951, .constN 9940 4, .addN 9953 9950 9940,
    .addN 9953 9953 9930, .addN 9954 9953 9930, .copyN 9955 9802, .copyN 9956 9800,
    .copyN 9957 9801, .copyN 9958 9804, .constN 9972 0, .constN 9988 1]

/-- The layout registers, part 2: the bases of the scratch arrays. -/
def pfA2 : Stmt :=
  block [.constN 9940 8, .addN 9959 9958 9940, .constN 9940 4, .addN 9960 9959 9940,
    .addN 9960 9960 9930, .addN 9960 9960 9930, .addN 9961 9960 9930, .addN 9961 9961 9930,
    .addN 9961 9961 9930, .addN 9961 9961 9930, .addN 9962 9961 9930, .addN 9963 9962 9930,
    .addN 9964 9963 9930, .addN 9965 9964 9930, .addN 9966 9965 9930, .addN 9967 9966 9930,
    .addN 9968 9967 9930, .addN 9969 9968 9930, .addN 9970 9969 9930, .addN 9971 9970 9930]

/-- The header of the fake frame and the saved values. -/
def pfA3 : Stmt :=
  block [.storeN 9959 9930, .storeN 9958 9950, .constN 9940 1, .addN 9941 9958 9940,
    .storeN 9941 3006, .addN 9941 9941 9940, .storeN 9941 9930, .addN 9941 9941 9940,
    .storeN 9941 9951, .addN 9941 9941 9940, .storeN 9941 9952, .addN 9941 9941 9940,
    .storeN 9941 9968]

/-- The arguments of `dvP` (the fake frame). -/
def dvG : Stmt := block [.copyN 3004 9959, .copyN 8430 9962]

/-- `r3004` back to the frame. -/
def dvR : Stmt := block [.copyN 3004 9950]

/-- The arguments of `lkProg`. -/
def lkG : Stmt := block [.copyN 6300 9930, .copyN 6301 9965, .copyN 6302 9966, .copyN 6303 9967]

/-- The registers of the pendant frame. -/
def pfB1 : Stmt :=
  block [.copyN 9931 6306, .addN 9978 9930 9931, .addN 9973 9978 9931, .constN 9940 4,
    .addN 9974 9971 9940, .addN 9974 9974 9973, .addN 9975 9974 9973, .addN 9976 9975 9973,
    .addN 9977 9976 9973, .addN 9977 9977 9973, .addN 9977 9977 9973, .addN 9979 9977 9973,
    .addN 9980 9974 9930, .addN 9981 9974 9978, .addN 9982 9975 9930, .addN 9983 9975 9978,
    .addN 9984 9976 9930, .addN 9985 9976 9978, .addN 9986 9977 9930, .addN 9987 9977 9978]

/-- The header of the pendant frame and the saved base of `FL'`. -/
def pfB2 : Stmt :=
  block [.storeN 9971 9973, .constN 9940 3, .addN 9941 9971 9940, .storeN 9941 9952,
    .constN 9940 6, .addN 9941 9958 9940, .storeN 9941 9977]

/-- The arguments of a store loop. -/
def ini (xr yr or kr k2r rr : ℕ) : Stmt :=
  block [.copyN 9923 xr, .copyN 9924 yr, .copyN 9925 or, .copyN 9926 kr, .copyN 9927 k2r,
    .copyN 9929 rr]

/-- **A store loop with its arguments.** -/
def lp (xr yr or kr k2r rr bnd : ℕ) (body : Stmt) : Stmt :=
  .seq (ini xr yr or kr k2r rr) (pfW bnd body)

/-! ### The program -/

/-- Stage 1: the registers, the saved values, `SG0 := SG`, `Q`, `X0`. -/
def pfS1 : Stmt :=
  .seq (.seq pfA1 (.seq pfA2 pfA3))
    (.seq (lp 9954 9972 9960 9972 9972 9972 9930 bAk)
      (.seq (lp 9957 9953 9968 9972 9972 9972 9930 bQ)
        (lp 9956 9968 9961 9951 9972 9972 9930 bXm)))

/-- Stage 2: `dvP` on the fake frame, `RF`, `lkProg`, the pendant registers and header. -/
def pfS2 : Stmt :=
  .seq (.seq dvG (.seq MfDrv.dvP dvR))
    (.seq (lp 9962 9972 9965 9972 9972 9972 9930 bRf)
      (.seq (.seq lkG lkProg) (.seq pfB1 pfB2)))

/-- Stage 3: `DVr`, `ZG`, `RV'`, `SG'`. -/
def pfS3 : Stmt :=
  .seq (.seq (lp 9963 9967 9969 9988 9972 9972 9931 bG) (lp 9964 9967 9970 9951 9972 9972 9931 bG))
    (.seq (.seq (lp 9953 9972 9974 9972 9972 9972 9930 bAk)
        (.seq (lp 9972 9972 9980 9978 9972 9972 9931 bId) (lp 9972 9972 9981 9930 9972 9972 9931 bId)))
      (.seq (lp 9962 9954 9975 9930 9972 9966 9930 bSg)
        (.seq (lp 9967 9972 9982 9972 9972 9972 9931 bAk) (lp 9972 9972 9983 9978 9972 9972 9931 bId))))

/-- Stage 4: `CP'`, `FL'`. -/
def pfS4 : Stmt :=
  .seq (.seq (lp 9955 9968 9976 9972 9972 9972 9930 bDf)
      (.seq (lp 9969 9970 9984 9972 9972 9972 9931 bSx) (lp 9970 9969 9985 9972 9972 9972 9931 bSx)))
    (.seq (lp 9956 9961 9977 9952 9972 9972 9930 bSx)
      (.seq (lp 9969 9970 9986 9952 9972 9972 9931 bSx) (lp 9970 9969 9987 9952 9972 9972 9931 bSx)))

/-- **The pendant frame writer.** -/
def pfP : Stmt := .seq pfS1 (.seq pfS2 (.seq pfS3 pfS4))

/-! ### The runs of the blocks -/

set_option maxHeartbeats 1600000 in
theorem pfA1_exec (c : Config) (hc : WordsBounded W c) {d m Z : ℕ} (r04 : c.nreg 3004 = d)
    (hm : c.nmem d = m) (hz : c.nmem (d + 3) = Z) (w1 : d + 4 + m + m ≤ W) (w2 : m * Z ≤ W) :
    ∃ c' k, Exec P W pfA1 c c' k ∧ k = 16 ∧ c'.nreg 9950 = d ∧ c'.nreg 9930 = m ∧
      c'.nreg 9951 = Z ∧ c'.nreg 9952 = m * Z ∧ c'.nreg 9953 = d + 4 + m ∧
      c'.nreg 9954 = d + 4 + m + m ∧ c'.nreg 9955 = c.nreg 9802 ∧ c'.nreg 9956 = c.nreg 9800 ∧
      c'.nreg 9957 = c.nreg 9801 ∧ c'.nreg 9958 = c.nreg 9804 ∧ c'.nreg 9972 = 0 ∧
      c'.nreg 9988 = 1 ∧
      (∀ r, r ≠ 9930 → ¬ (9940 ≤ r ∧ r ≤ 9958) → r ≠ 9972 → r ≠ 9988 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pfA1
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, hm, hz]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl,
    rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r04, hm, hz])
  all_goals (try (simp (disch := omega) only [upd_other]))
  all_goals (try omega)

set_option maxHeartbeats 1600000 in
theorem pfA2_exec (c : Config) (hc : WordsBounded W c) {m S : ℕ} (r30 : c.nreg 9930 = m)
    (r58 : c.nreg 9958 = S) (w : S + 12 + 16 * m ≤ W) :
    ∃ c' k, Exec P W pfA2 c c' k ∧ k = 20 ∧ c'.nreg 9959 = S + 8 ∧
      c'.nreg 9960 = S + 12 + 2 * m ∧ c'.nreg 9961 = S + 12 + 6 * m ∧
      c'.nreg 9962 = S + 12 + 7 * m ∧ c'.nreg 9963 = S + 12 + 8 * m ∧
      c'.nreg 9964 = S + 12 + 9 * m ∧ c'.nreg 9965 = S + 12 + 10 * m ∧
      c'.nreg 9966 = S + 12 + 11 * m ∧ c'.nreg 9967 = S + 12 + 12 * m ∧
      c'.nreg 9968 = S + 12 + 13 * m ∧ c'.nreg 9969 = S + 12 + 14 * m ∧
      c'.nreg 9970 = S + 12 + 15 * m ∧ c'.nreg 9971 = S + 12 + 16 * m ∧
      (∀ r, r ≠ 9940 → ¬ (9959 ≤ r ∧ r ≤ 9971) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pfA2
  exec_block
  all_goals try ((try config_simp); (try simp only [r30, r58]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl,
    rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r30, r58])
  all_goals (try (simp (disch := omega) only [upd_other]))
  all_goals (try omega)

theorem pfA3_exec (c : Config) (hc : WordsBounded W c) {m S d Z Z' Qb : ℕ}
    (r30 : c.nreg 9930 = m) (r50 : c.nreg 9950 = d) (r51 : c.nreg 9951 = Z)
    (r52 : c.nreg 9952 = Z') (r58 : c.nreg 9958 = S) (r59 : c.nreg 9959 = S + 8)
    (r68 : c.nreg 9968 = Qb) (w : S + 8 ≤ W) :
    ∃ c' k, Exec P W pfA3 c c' k ∧ k = 13 ∧
      c'.nmem (S + 8) = m ∧ c'.nmem S = d ∧ c'.nmem (S + 1) = c.nreg 3006 ∧
      c'.nmem (S + 2) = m ∧ c'.nmem (S + 3) = Z ∧ c'.nmem (S + 4) = Z' ∧ c'.nmem (S + 5) = Qb ∧
      (∀ a, (a < S ∨ S + 5 < a) → a ≠ S + 8 → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 9940 → r ≠ 9941 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pfA3
  exec_block
  all_goals try ((try config_simp); (try simp only [r30, r50, r51, r52, r58, r59, r68]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a h1 h2 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r30, r50, r51, r52, r58, r59, r68, upd_apply]) <;> (try split_ifs) <;>
    omega

theorem dvG_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W dvG c c' k ∧ k = 2 ∧ c'.nreg 3004 = c.nreg 9959 ∧
      c'.nreg 8430 = c.nreg 9962 ∧ (∀ r, r ≠ 3004 → r ≠ 8430 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dvG
  exec_block
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [upd_apply]) <;> (try split_ifs) <;> omega

theorem dvR_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W dvR c c' k ∧ k = 1 ∧ c'.nreg 3004 = c.nreg 9950 ∧
      (∀ r, r ≠ 3004 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dvR
  exec_block
  refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [upd_apply]) <;> (try split_ifs) <;> omega

theorem lkG_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W lkG c c' k ∧ k = 4 ∧ c'.nreg 6300 = c.nreg 9930 ∧
      c'.nreg 6301 = c.nreg 9965 ∧ c'.nreg 6302 = c.nreg 9966 ∧ c'.nreg 6303 = c.nreg 9967 ∧
      (∀ r, ¬ (6300 ≤ r ∧ r ≤ 6303) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lkG
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [upd_apply]) <;> (try split_ifs) <;> omega

set_option maxHeartbeats 1600000 in
theorem pfB1_exec (c : Config) (hc : WordsBounded W c) {m n d' : ℕ}
    (r30 : c.nreg 9930 = m) (r06 : c.nreg 6306 = n) (r71 : c.nreg 9971 = d')
    (w : d' + 4 + 7 * (m + 2 * n) ≤ W) :
    ∃ c' k, Exec P W pfB1 c c' k ∧ k = 20 ∧ c'.nreg 9931 = n ∧ c'.nreg 9978 = m + n ∧
      c'.nreg 9973 = m + 2 * n ∧ c'.nreg 9974 = d' + 4 + (m + 2 * n) ∧
      c'.nreg 9975 = d' + 4 + 2 * (m + 2 * n) ∧ c'.nreg 9976 = d' + 4 + 3 * (m + 2 * n) ∧
      c'.nreg 9977 = d' + 4 + 6 * (m + 2 * n) ∧ c'.nreg 9979 = d' + 4 + 7 * (m + 2 * n) ∧
      c'.nreg 9980 = d' + 4 + (m + 2 * n) + m ∧
      c'.nreg 9981 = d' + 4 + (m + 2 * n) + (m + n) ∧
      c'.nreg 9982 = d' + 4 + 2 * (m + 2 * n) + m ∧
      c'.nreg 9983 = d' + 4 + 2 * (m + 2 * n) + (m + n) ∧
      c'.nreg 9984 = d' + 4 + 3 * (m + 2 * n) + m ∧
      c'.nreg 9985 = d' + 4 + 3 * (m + 2 * n) + (m + n) ∧
      c'.nreg 9986 = d' + 4 + 6 * (m + 2 * n) + m ∧
      c'.nreg 9987 = d' + 4 + 6 * (m + 2 * n) + (m + n) ∧
      (∀ r, r ≠ 9931 → r ≠ 9940 → ¬ (9973 ≤ r ∧ r ≤ 9987) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pfB1
  exec_block
  all_goals try ((try config_simp); (try simp only [r30, r06, r71]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r30, r06, r71])
  all_goals (try (simp (disch := omega) only [upd_other]))
  all_goals (try omega)

theorem pfB2_exec (c : Config) (hc : WordsBounded W c) {d' m' Z' S F : ℕ}
    (r71 : c.nreg 9971 = d') (r73 : c.nreg 9973 = m') (r52 : c.nreg 9952 = Z')
    (r58 : c.nreg 9958 = S) (r77 : c.nreg 9977 = F) (w1 : d' + 3 ≤ W) (w2 : S + 6 ≤ W) :
    ∃ c' k, Exec P W pfB2 c c' k ∧ k = 7 ∧
      c'.nmem = upd (upd (upd c.nmem d' m') (d' + 3) Z') (S + 6) F ∧
      (∀ r, r ≠ 9940 → r ≠ 9941 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pfB2
  exec_block
  all_goals try ((try config_simp); (try simp only [r71, r73, r52, r58, r77]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r71, r73, r52, r58, r77, upd_apply]) <;> (try split_ifs) <;> omega

/-- The registers written by a store loop with its arguments. -/
def LpScr (r : ℕ) : Prop := r = 9920 ∨ r = 9921 ∨ (9923 ≤ r ∧ r ≤ 9929) ∨ (9940 ≤ r ∧ r ≤ 9945)

set_option maxHeartbeats 1600000 in
theorem ini_exec (c : Config) (hc : WordsBounded W c) {xr yr or kr k2r rr : ℕ}
    (h1 : ¬ (9923 ≤ xr ∧ xr ≤ 9929)) (h2 : ¬ (9923 ≤ yr ∧ yr ≤ 9929))
    (h3 : ¬ (9923 ≤ or ∧ or ≤ 9929)) (h4 : ¬ (9923 ≤ kr ∧ kr ≤ 9929))
    (h5 : ¬ (9923 ≤ k2r ∧ k2r ≤ 9929)) (h6 : ¬ (9923 ≤ rr ∧ rr ≤ 9929)) :
    ∃ c' k, Exec P W (ini xr yr or kr k2r rr) c c' k ∧ k = 6 ∧
      c'.nreg 9923 = c.nreg xr ∧ c'.nreg 9924 = c.nreg yr ∧ c'.nreg 9925 = c.nreg or ∧
      c'.nreg 9926 = c.nreg kr ∧ c'.nreg 9927 = c.nreg k2r ∧ c'.nreg 9929 = c.nreg rr ∧
      (∀ r, ¬ (9923 ≤ r ∧ r ≤ 9929) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ini
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [upd_apply]) <;> (try split_ifs) <;> omega

/-- **The result of a store loop with its arguments.** -/
structure LpOut (c c' : Config) (O n : ℕ) (val : ℕ → ℕ) : Prop where
  val : ∀ t < n, c'.nmem (O + t) = val t
  mem : ∀ a, (a < O ∨ O + n ≤ a) → c'.nmem a = c.nmem a
  reg : ∀ r, ¬ LpScr r → c'.nreg r = c.nreg r
  rr : c'.rreg = c.rreg
  rm : c'.rmem = c.rmem
  out : c'.output = c.output

/-- **A store loop with its arguments**, from the loop lemma run after `ini`. -/
theorem lp_exec {xr yr or kr k2r rr bnd : ℕ} {body : Stmt} {O n B : ℕ} {val : ℕ → ℕ}
    (c : Config) (hc : WordsBounded W c)
    (h1 : ¬ (9923 ≤ xr ∧ xr ≤ 9929)) (h2 : ¬ (9923 ≤ yr ∧ yr ≤ 9929))
    (h3 : ¬ (9923 ≤ or ∧ or ≤ 9929)) (h4 : ¬ (9923 ≤ kr ∧ kr ≤ 9929))
    (h5 : ¬ (9923 ≤ k2r ∧ k2r ≤ 9929)) (h6 : ¬ (9923 ≤ rr ∧ rr ≤ 9929))
    (hL : ∀ c₁ : Config, WordsBounded W c₁ → c₁.nmem = c.nmem →
      c₁.nreg 9923 = c.nreg xr → c₁.nreg 9924 = c.nreg yr → c₁.nreg 9925 = c.nreg or →
      c₁.nreg 9926 = c.nreg kr → c₁.nreg 9927 = c.nreg k2r → c₁.nreg 9929 = c.nreg rr →
      (∀ r, ¬ (9923 ≤ r ∧ r ≤ 9929) → c₁.nreg r = c.nreg r) →
      ∃ c' k, Exec P W (pfW bnd body) c₁ c' k ∧ k ≤ B ∧ PfOut c₁ c' O n val) :
    ∃ c' k, Exec P W (lp xr yr or kr k2r rr bnd body) c c' k ∧ k ≤ B + 6 ∧
      LpOut c c' O n val := by
  obtain ⟨c₁, k₁, e₁, hk₁, a23, a24, a25, a26, a27, a29, g₁, m₁, rr₁, rm₁, o₁⟩ :=
    ini_exec (P := P) (W := W) c hc h1 h2 h3 h4 h5 h6
  obtain ⟨c', k, e, hk, hP⟩ := hL c₁ e₁.wb_right m₁ a23 a24 a25 a26 a27 a29 g₁
  refine ⟨c', k₁ + k, e₁.seq e, by omega, ⟨hP.val, fun a ha => by rw [hP.mem a ha, m₁],
    fun r hr => ?_, by rw [hP.rr, rr₁], by rw [hP.rm, rm₁], by rw [hP.out, o₁]⟩⟩
  unfold LpScr at hr
  rw [hP.reg r (by unfold PfScr; omega), g₁ r (by omega)]

end NcFz

end BKMNW

end PlanarFlow
