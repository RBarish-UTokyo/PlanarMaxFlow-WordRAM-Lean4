module

public import PlanarFlow.BKMNW.NcFzB
public import PlanarFlow.BKMNW.Nf7aP1

/-!
# The pendant frame writer `pfP`: stage 1

`pfS1 = pfA1 ; pfA2 ; pfA3 ; SG0 := SG ; Q ; X0` (**`pfS1_exec`**, `36 m + 79` steps):

* the layout registers (`Rg1`), the saved values `mem[S … S + 5]`, the fake frame header
  `mem[S + 8] = m`;
* `SG0[t] = SG[t]` at `S + 12 + 2m`;
* `Q[t] = qF` (`1` iff the dart `t` or its reverse has its tail flagged in `DF`) at `S + 12 + 13m`;
* `X0[t] = F1[t]·Q[t] + Z ∸ Z·Q[t]` at `S + 12 + 6m` (`F1` on the darts touching `Del`, `Z`
  elsewhere: the flow array of the fake frame, whose net outflows are the frozen outflows).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcFz

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The flag `[the dart or its reverse has its tail flagged]` from `DF` and `RV`. -/
def qF (mem : ℕ → ℕ) (DFb RVb i : ℕ) : ℕ :=
  (mem (DFb + i) + mem (DFb + mem (RVb + i))) - ((mem (DFb + i) + mem (DFb + mem (RVb + i))) - 1)

lemma qF_le_one (mem : ℕ → ℕ) (DFb RVb i : ℕ) : qF mem DFb RVb i ≤ 1 := by unfold qF; omega

lemma mul_le_of_le_one' {a b : ℕ} (h : b ≤ 1) : a * b ≤ a := by
  interval_cases b <;> simp

lemma mul_le_of_le_one'' {a b : ℕ} (h : b ≤ 1) : b * a ≤ a := by
  interval_cases b <;> simp

/-- **The layout registers of stage 1.** -/
structure Rg1 (c : Config) (d m Z S F1b DFb CPb : ℕ) : Prop where
  r30 : c.nreg 9930 = m
  r50 : c.nreg 9950 = d
  r51 : c.nreg 9951 = Z
  r52 : c.nreg 9952 = m * Z
  r53 : c.nreg 9953 = d + 4 + m
  r54 : c.nreg 9954 = d + 4 + m + m
  r55 : c.nreg 9955 = CPb
  r56 : c.nreg 9956 = F1b
  r57 : c.nreg 9957 = DFb
  r58 : c.nreg 9958 = S
  r59 : c.nreg 9959 = S + 8
  r60 : c.nreg 9960 = S + 12 + 2 * m
  r61 : c.nreg 9961 = S + 12 + 6 * m
  r62 : c.nreg 9962 = S + 12 + 7 * m
  r63 : c.nreg 9963 = S + 12 + 8 * m
  r64 : c.nreg 9964 = S + 12 + 9 * m
  r65 : c.nreg 9965 = S + 12 + 10 * m
  r66 : c.nreg 9966 = S + 12 + 11 * m
  r67 : c.nreg 9967 = S + 12 + 12 * m
  r68 : c.nreg 9968 = S + 12 + 13 * m
  r69 : c.nreg 9969 = S + 12 + 14 * m
  r70 : c.nreg 9970 = S + 12 + 15 * m
  r71 : c.nreg 9971 = S + 12 + 16 * m
  r72 : c.nreg 9972 = 0
  r88 : c.nreg 9988 = 1

/-- The registers of `Rg1`. -/
def InRg1 (r : ℕ) : Prop := r = 9930 ∨ (9950 ≤ r ∧ r ≤ 9972) ∨ r = 9988

lemma Rg1.keep {c c' : Config} {d m Z S F1b DFb CPb : ℕ} (h : Rg1 c d m Z S F1b DFb CPb)
    (hk : ∀ r, InRg1 r → c'.nreg r = c.nreg r) : Rg1 c' d m Z S F1b DFb CPb := by
  obtain ⟨a30, a50, a51, a52, a53, a54, a55, a56, a57, a58, a59, a60, a61, a62, a63, a64, a65,
    a66, a67, a68, a69, a70, a71, a72, a88⟩ := h
  unfold InRg1 at hk
  exact ⟨by rw [hk _ (by omega), a30], by rw [hk _ (by omega), a50], by rw [hk _ (by omega), a51],
    by rw [hk _ (by omega), a52], by rw [hk _ (by omega), a53], by rw [hk _ (by omega), a54],
    by rw [hk _ (by omega), a55], by rw [hk _ (by omega), a56], by rw [hk _ (by omega), a57],
    by rw [hk _ (by omega), a58], by rw [hk _ (by omega), a59], by rw [hk _ (by omega), a60],
    by rw [hk _ (by omega), a61], by rw [hk _ (by omega), a62], by rw [hk _ (by omega), a63],
    by rw [hk _ (by omega), a64], by rw [hk _ (by omega), a65], by rw [hk _ (by omega), a66],
    by rw [hk _ (by omega), a67], by rw [hk _ (by omega), a68], by rw [hk _ (by omega), a69],
    by rw [hk _ (by omega), a70], by rw [hk _ (by omega), a71], by rw [hk _ (by omega), a72],
    by rw [hk _ (by omega), a88]⟩

lemma Rg1.keepLp {c c' : Config} {d m Z S F1b DFb CPb : ℕ} (h : Rg1 c d m Z S F1b DFb CPb)
    (hk : ∀ r, ¬ LpScr r → c'.nreg r = c.nreg r) : Rg1 c' d m Z S F1b DFb CPb :=
  h.keep fun r hr => hk r (by unfold InRg1 at hr; unfold LpScr; omega)

/-- **The hypotheses of `pfP`** on the start configuration. -/
structure PfIn (c : Config) (W d m Z S F1b DFb CPb : ℕ) : Prop where
  hm : c.nmem d = m
  hz : c.nmem (d + 3) = Z
  m0 : 0 < m
  r04 : c.nreg 3004 = d
  r00 : c.nreg 9800 = F1b
  r01 : c.nreg 9801 = DFb
  r02 : c.nreg 9802 = CPb
  r04' : c.nreg 9804 = S
  lF : F1b + m ≤ S
  lD : DFb + m ≤ S
  lC : CPb + m ≤ S
  lfr : d + 4 + 7 * m ≤ S
  wS : S + 40 * m + 20 ≤ W
  wZ : 4 * (m * Z) + 4 * Z + 4 ≤ W
  rv : ∀ i < m, c.nmem (d + 4 + m + i) < m
  sg : ∀ i < m, c.nmem (d + 4 + m + m + i) < m
  df : ∀ i < m, c.nmem (DFb + i) ≤ 1
  f1 : ∀ i < m, c.nmem (F1b + i) ≤ 2 * Z
  cp : ∀ i < m, c.nmem (CPb + i) ≤ Z
  sgp : OrbLab.PermOn (MfDrv.sgF d m c.nmem) m

/-- **The result of stage 1.** -/
structure St1 (c c' : Config) (d m Z S F1b DFb CPb : ℕ) : Prop where
  rg : Rg1 c' d m Z S F1b DFb CPb
  r04 : c'.nreg 3004 = d
  reg : ∀ r, ¬ (9920 ≤ r ∧ r ≤ 9999) → c'.nreg r = c.nreg r
  low : ∀ a, a < S → c'.nmem a = c.nmem a
  sv0 : c'.nmem S = d
  sv1 : c'.nmem (S + 1) = c.nreg 3006
  sv2 : c'.nmem (S + 2) = m
  sv3 : c'.nmem (S + 3) = Z
  sv4 : c'.nmem (S + 4) = m * Z
  sv5 : c'.nmem (S + 5) = S + 12 + 13 * m
  h0 : c'.nmem (S + 8) = m
  sg0 : ∀ t < m, c'.nmem (S + 12 + 2 * m + t) = c.nmem (d + 4 + m + m + t)
  q : ∀ t < m, c'.nmem (S + 12 + 13 * m + t) = qF c.nmem DFb (d + 4 + m) t
  x0 : ∀ t < m, c'.nmem (S + 12 + 6 * m + t) =
    c.nmem (F1b + t) * qF c.nmem DFb (d + 4 + m) t + Z - Z * qF c.nmem DFb (d + 4 + m) t
  rr : c'.rreg = c.rreg
  rm : c'.rmem = c.rmem
  out : c'.output = c.output

/-- The saved values and the fake frame header after the first blocks. -/
structure A3Out (c c' : Config) (d m Z S : ℕ) : Prop where
  h0 : c'.nmem (S + 8) = m
  sv0 : c'.nmem S = d
  sv1 : c'.nmem (S + 1) = c.nreg 3006
  sv2 : c'.nmem (S + 2) = m
  sv3 : c'.nmem (S + 3) = Z
  sv4 : c'.nmem (S + 4) = m * Z
  sv5 : c'.nmem (S + 5) = S + 12 + 13 * m
  mem : ∀ a, (a < S ∨ S + 8 < a) → c'.nmem a = c.nmem a
  reg : ∀ r, ¬ (9920 ≤ r ∧ r ≤ 9999) → c'.nreg r = c.nreg r
  rr : c'.rreg = c.rreg
  rm : c'.rmem = c.rmem
  out : c'.output = c.output

lemma Rg1.keepA3 {c c' : Config} {d m Z S F1b DFb CPb : ℕ} (h : Rg1 c d m Z S F1b DFb CPb)
    (hk : ∀ r, r ≠ 9940 → r ≠ 9941 → c'.nreg r = c.nreg r) : Rg1 c' d m Z S F1b DFb CPb :=
  h.keep fun r hr => hk r (by unfold InRg1 at hr; omega) (by unfold InRg1 at hr; omega)

lemma Rg1.ofA2 {c₁ c₂ : Config} {d m Z S F1b DFb CPb : ℕ}
    (q : ∀ r, r ≠ 9940 → ¬ (9959 ≤ r ∧ r ≤ 9971) → c₂.nreg r = c₁.nreg r)
    (a30 : c₁.nreg 9930 = m) (a50 : c₁.nreg 9950 = d) (a51 : c₁.nreg 9951 = Z)
    (a52 : c₁.nreg 9952 = m * Z) (a53 : c₁.nreg 9953 = d + 4 + m)
    (a54 : c₁.nreg 9954 = d + 4 + m + m) (a55 : c₁.nreg 9955 = CPb) (a56 : c₁.nreg 9956 = F1b)
    (a57 : c₁.nreg 9957 = DFb) (a58 : c₁.nreg 9958 = S) (a72 : c₁.nreg 9972 = 0)
    (a88 : c₁.nreg 9988 = 1)
    (b59 : c₂.nreg 9959 = S + 8) (b60 : c₂.nreg 9960 = S + 12 + 2 * m)
    (b61 : c₂.nreg 9961 = S + 12 + 6 * m) (b62 : c₂.nreg 9962 = S + 12 + 7 * m)
    (b63 : c₂.nreg 9963 = S + 12 + 8 * m) (b64 : c₂.nreg 9964 = S + 12 + 9 * m)
    (b65 : c₂.nreg 9965 = S + 12 + 10 * m) (b66 : c₂.nreg 9966 = S + 12 + 11 * m)
    (b67 : c₂.nreg 9967 = S + 12 + 12 * m) (b68 : c₂.nreg 9968 = S + 12 + 13 * m)
    (b69 : c₂.nreg 9969 = S + 12 + 14 * m) (b70 : c₂.nreg 9970 = S + 12 + 15 * m)
    (b71 : c₂.nreg 9971 = S + 12 + 16 * m) : Rg1 c₂ d m Z S F1b DFb CPb :=
  ⟨by rw [q _ (by omega) (by omega), a30], by rw [q _ (by omega) (by omega), a50],
    by rw [q _ (by omega) (by omega), a51], by rw [q _ (by omega) (by omega), a52],
    by rw [q _ (by omega) (by omega), a53], by rw [q _ (by omega) (by omega), a54],
    by rw [q _ (by omega) (by omega), a55], by rw [q _ (by omega) (by omega), a56],
    by rw [q _ (by omega) (by omega), a57], by rw [q _ (by omega) (by omega), a58],
    b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71,
    by rw [q _ (by omega) (by omega), a72], by rw [q _ (by omega) (by omega), a88]⟩

lemma a3_mem_aux {S a : ℕ} (ha : a < S ∨ S + 8 < a) : (a < S ∨ S + 5 < a) ∧ a ≠ S + 8 := by
  omega

set_option maxHeartbeats 1600000 in
/-- The three register/store blocks of stage 1. -/
theorem pfA_exec (c : Config) (hc : WordsBounded W c) {d m Z S F1b DFb CPb : ℕ}
    (hm : c.nmem d = m) (hz : c.nmem (d + 3) = Z) (r04 : c.nreg 3004 = d)
    (r00 : c.nreg 9800 = F1b) (r01 : c.nreg 9801 = DFb) (r02 : c.nreg 9802 = CPb)
    (r04' : c.nreg 9804 = S) (lfr : d + 4 + 7 * m ≤ S) (wS : S + 40 * m + 20 ≤ W)
    (hmZ : m * Z ≤ W) :
    ∃ c' k, Exec P W (.seq pfA1 (.seq pfA2 pfA3)) c c' k ∧ k = 49 ∧
      Rg1 c' d m Z S F1b DFb CPb ∧ A3Out c c' d m Z S := by
  have w1 : d + 4 + m + m ≤ W := by omega
  have w2 : S + 12 + 16 * m ≤ W := by omega
  have w3 : S + 8 ≤ W := by omega
  clear lfr wS
  obtain ⟨c₁, k₁, e₁, hk₁, a50, a30, a51, a52, a53, a54, a55, a56, a57, a58, a72, a88, g₁, m₁, rr₁,
    rm₁, o₁⟩ := pfA1_exec (P := P) c hc r04 hm hz w1 hmZ
  rw [r02] at a55; rw [r00] at a56; rw [r01] at a57; rw [r04'] at a58
  obtain ⟨c₂, k₂, e₂, hk₂, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, g₂, m₂,
    rr₂, rm₂, o₂⟩ := pfA2_exec (P := P) c₁ e₁.wb_right a30 a58 w2
  have R2 : Rg1 c₂ d m Z S F1b DFb CPb := Rg1.ofA2 g₂ a30 a50 a51 a52 a53 a54 a55 a56 a57 a58 a72
    a88 b59 b60 b61 b62 b63 b64 b65 b66 b67 b68 b69 b70 b71
  clear a30 a50 a51 a52 a53 a54 a55 a56 a57 a58 a72 a88 b59 b60 b61 b62 b63 b64 b65 b66 b67 b68
    b69 b70 b71
  obtain ⟨c₃, k₃, e₃, hk₃, s8, s0, s1, s2, s3, s4, s5, f₃, g₃, rr₃, rm₃, o₃⟩ :=
    pfA3_exec (P := P) c₂ e₂.wb_right R2.r30 R2.r50 R2.r51 R2.r52 R2.r58 R2.r59 R2.r68 w3
  have R3 : Rg1 c₃ d m Z S F1b DFb CPb := R2.keepA3 g₃
  have hr3006 : c₂.nreg 3006 = c.nreg 3006 := by
    rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)]
  refine ⟨c₃, k₁ + (k₂ + k₃), e₁.seq (e₂.seq e₃), by rw [hk₁, hk₂, hk₃], R3,
    ⟨s8, s0, by rw [s1, hr3006], s2, s3, s4, s5,
    fun a ha => by
      obtain ⟨h1, h2⟩ := a3_mem_aux ha
      rw [f₃ a h1 h2, m₂, m₁],
    fun r hr => ?_, by rw [rr₃, rr₂, rr₁], by rw [rm₃, rm₂, rm₁], by rw [o₃, o₂, o₁]⟩⟩
  have h1 : r ≠ 9940 ∧ r ≠ 9941 ∧ ¬ (9959 ≤ r ∧ r ≤ 9971) ∧ r ≠ 9930 ∧
      ¬ (9940 ≤ r ∧ r ≤ 9958) ∧ r ≠ 9972 ∧ r ≠ 9988 := by clear * - hr; omega
  rw [g₃ _ h1.1 h1.2.1, g₂ _ h1.1 h1.2.2.1, g₁ _ h1.2.2.2.1 h1.2.2.2.2.1 h1.2.2.2.2.2.1
    h1.2.2.2.2.2.2]

/-- `SG0 := SG`. -/
theorem pfSG_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) {d m Z S F1b DFb CPb : ℕ}
    (R : Rg1 c d m Z S F1b DFb CPb) (lfr : d + 4 + 7 * m ≤ S) (wS : S + 40 * m + 20 ≤ W) :
    ∃ c' k, Exec P W (lp 9954 9972 9960 9972 9972 9972 9930 bAk) c c' k ∧ k ≤ 9 * m + 10 ∧
      LpOut c c' (S + 12 + 2 * m) m (fun t => c.nmem (d + 4 + m + m + t) + 0 - 0) :=
  lp_exec (P := P) c hc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      obtain ⟨c'', k, ex, hk, hP⟩ := lAk_exec (P := P) c' hw hW (bnd := 9930) (n := m)
        (X := d + 4 + m + m) (O := S + 12 + 2 * m) (K := 0) (K₂ := 0)
        (by rw [g _ (by omega), R.r30]) (by unfold PfScr; omega) (by rw [a23, R.r54])
        (by rw [a25, R.r60]) (by rw [a26, R.r72]) (by rw [a27, R.r72]) (by omega) (by omega)
        (by omega) (fun t ht => by have := hw.2 (d + 4 + m + m + t); omega)
        (fun t ht j hj => by omega)
      rw [hm'] at hP
      exact ⟨c'', k, ex, hk, hP⟩)

/-- `Q[t] := qF`. -/
theorem pfQ_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) {d m Z S F1b DFb CPb : ℕ}
    (R : Rg1 c d m Z S F1b DFb CPb) (lD : DFb + m ≤ S) (lfr : d + 4 + 7 * m ≤ S)
    (wS : S + 40 * m + 20 ≤ W) (hrv : ∀ t < m, c.nmem (d + 4 + m + t) < m)
    (hdf : ∀ t < m, c.nmem (DFb + t) ≤ 1) :
    ∃ c' k, Exec P W (lp 9957 9953 9968 9972 9972 9972 9930 bQ) c c' k ∧ k ≤ 14 * m + 10 ∧
      LpOut c c' (S + 12 + 13 * m) m (fun t => qF c.nmem DFb (d + 4 + m) t) :=
  lp_exec (P := P) c hc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      have hrv' : ∀ t < m, c'.nmem (d + 4 + m + t) < m := fun t ht => by
        rw [hm']; exact hrv t ht
      obtain ⟨c'', k, ex, hk, hP⟩ := lQ_exec (P := P) c' hw hW (bnd := 9930) (n := m)
        (X := DFb) (Y := d + 4 + m) (O := S + 12 + 13 * m)
        (by rw [g _ (by omega), R.r30]) (by unfold PfScr; omega) (by rw [a23, R.r57])
        (by rw [a24, R.r53]) (by rw [a25, R.r68]) (by omega) (by omega) (by omega) (by omega)
        (fun t ht => by have := hrv' t ht; omega)
        (fun t ht => by
          have h1 := hdf t ht; have h2 := hdf _ (hrv' t ht); rw [← hm'] at h1 h2; omega)
        (fun t ht j hj => by omega) (fun t ht j hj => by omega)
        (fun t ht j hj => by have := hrv' t ht; omega)
      rw [hm'] at hP
      exact ⟨c'', k, ex, hk, hP⟩)

/-- `X0[t] := F1[t]·Q[t] + Z ∸ Z·Q[t]`. -/
theorem pfX0_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) {d m Z S F1b DFb CPb : ℕ}
    (R : Rg1 c d m Z S F1b DFb CPb) (lF : F1b + m ≤ S)
    (wS : S + 40 * m + 20 ≤ W) (wZ : 4 * (m * Z) + 4 * Z + 4 ≤ W)
    (hq : ∀ t < m, c.nmem (S + 12 + 13 * m + t) ≤ 1) (hf : ∀ t < m, c.nmem (F1b + t) ≤ 2 * Z) :
    ∃ c' k, Exec P W (lp 9956 9968 9961 9951 9972 9972 9930 bXm) c c' k ∧ k ≤ 13 * m + 10 ∧
      LpOut c c' (S + 12 + 6 * m) m (fun t => c.nmem (F1b + t) * c.nmem (S + 12 + 13 * m + t) +
        Z - Z * c.nmem (S + 12 + 13 * m + t)) :=
  lp_exec (P := P) c hc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      have hq' : ∀ t < m, c'.nmem (S + 12 + 13 * m + t) ≤ 1 := fun t ht => by
        rw [hm']; exact hq t ht
      have hf' : ∀ t < m, c'.nmem (F1b + t) ≤ 2 * Z := fun t ht => by rw [hm']; exact hf t ht
      obtain ⟨c'', k, ex, hk, hP⟩ := lXm_exec (P := P) c' hw hW (bnd := 9930) (n := m)
        (X := F1b) (Y := S + 12 + 13 * m) (O := S + 12 + 6 * m) (K := Z)
        (by rw [g _ (by omega), R.r30]) (by unfold PfScr; omega) (by rw [a23, R.r56])
        (by rw [a24, R.r68]) (by rw [a25, R.r61]) (by rw [a26, R.r51]) (by omega) (by omega)
        (by omega) (by omega)
        (fun t ht => by
          have := mul_le_of_le_one' (a := c'.nmem (F1b + t)) (hq' t ht); have := hf' t ht; omega)
        (fun t ht => by have := mul_le_of_le_one' (a := Z) (hq' t ht); omega)
        (fun t ht j hj => by omega) (fun t ht j hj => by omega)
      rw [hm'] at hP
      exact ⟨c'', k, ex, hk, hP⟩)

set_option maxHeartbeats 1600000 in
/-- **Stage 1 of `pfP`.** -/
theorem pfS1_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) {d m Z S F1b DFb CPb : ℕ}
    (hI : PfIn c W d m Z S F1b DFb CPb) :
    ∃ c' k, Exec P W pfS1 c c' k ∧ k ≤ 36 * m + 79 ∧ St1 c c' d m Z S F1b DFb CPb := by
  have hmZ : m * Z ≤ W := by have := hI.wZ; omega
  obtain ⟨c₃, k₃, e₃, hk₃, R3, A3⟩ :=
    pfA_exec (P := P) c hc hI.hm hI.hz hI.r04 hI.r00 hI.r01 hI.r02 hI.r04' hI.lfr hI.wS hmZ
  have M3 := A3.mem
  have g₃ := A3.reg
  have lF := hI.lF; have lD := hI.lD; have lfr := hI.lfr; have wS := hI.wS
  obtain ⟨c₄, k₄, e₄, hk₄, L₄⟩ := pfSG_exec (P := P) c₃ e₃.wb_right hW R3 lfr wS
  obtain ⟨c₅, k₅, e₅, hk₅, L₅⟩ := pfQ_exec (P := P) c₄ e₄.wb_right hW (R3.keepLp L₄.reg) lD lfr
    wS (fun t ht => by
      rw [L₄.mem _ (Or.inl (by omega)), M3 _ (Or.inl (by omega))]; exact hI.rv t ht)
    (fun t ht => by
      rw [L₄.mem _ (Or.inl (by omega)), M3 _ (Or.inl (by omega))]; exact hI.df t ht)
  have M4 : ∀ a, (a < S ∨ S + 8 < a) → (a < S + 12 + 2 * m ∨ S + 12 + 2 * m + m ≤ a) →
      c₄.nmem a = c.nmem a := fun a h1 h2 => by rw [L₄.mem a h2, M3 a h1]
  have Qv : ∀ t < m, c₅.nmem (S + 12 + 13 * m + t) = qF c.nmem DFb (d + 4 + m) t := by
    intro t ht
    rw [L₅.val t ht]
    unfold qF
    have hr := hI.rv t ht
    rw [M4 (DFb + t) (by omega) (by omega), M4 (d + 4 + m + t) (by omega) (by omega),
      M4 (DFb + c.nmem (d + 4 + m + t)) (by omega) (by omega)]
  obtain ⟨c₆, k₆, e₆, hk₆, L₆⟩ := pfX0_exec (P := P) c₅ e₅.wb_right hW
    ((R3.keepLp L₄.reg).keepLp L₅.reg) lF wS hI.wZ
    (fun t ht => by rw [Qv t ht]; exact qF_le_one _ _ _ _)
    (fun t ht => by
      rw [L₅.mem _ (Or.inl (by omega)), M4 _ (by omega) (by omega)]; exact hI.f1 t ht)
  have R6 : Rg1 c₆ d m Z S F1b DFb CPb := ((R3.keepLp L₄.reg).keepLp L₅.reg).keepLp L₆.reg
  have K : ∀ a, a ≤ S + 8 → c₆.nmem a = c₃.nmem a := fun a ha => by
    rw [L₆.mem _ (Or.inl (by omega)), L₅.mem _ (Or.inl (by omega)), L₄.mem _ (Or.inl (by omega))]
  refine ⟨c₆, 49 + (k₄ + (k₅ + k₆)), by rw [← hk₃]; exact e₃.seq (e₄.seq (e₅.seq e₆)),
    by omega, ⟨R6, ?_, fun r hr => ?_, fun a ha => ?_, by rw [K _ (by omega), A3.sv0],
    by rw [K _ (by omega), A3.sv1], by rw [K _ (by omega), A3.sv2], by rw [K _ (by omega), A3.sv3],
    by rw [K _ (by omega), A3.sv4], by rw [K _ (by omega), A3.sv5], by rw [K _ (by omega), A3.h0],
    fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, ?_, ?_, ?_⟩⟩
  · rw [L₆.reg _ (by unfold LpScr; omega), L₅.reg _ (by unfold LpScr; omega),
      L₄.reg _ (by unfold LpScr; omega), g₃ _ (by omega)]
    exact hI.r04
  · rw [L₆.reg _ (by unfold LpScr; omega), L₅.reg _ (by unfold LpScr; omega),
      L₄.reg _ (by unfold LpScr; omega), g₃ _ hr]
  · rw [K _ (by omega), M3 a (Or.inl ha)]
  · rw [L₆.mem _ (Or.inl (by omega)), L₅.mem _ (Or.inl (by omega)), L₄.val t ht,
      M3 _ (Or.inl (by omega))]
    simp
  · rw [L₆.mem _ (Or.inr (by omega)), Qv t ht]
  · rw [L₆.val t ht, Qv t ht, L₅.mem _ (Or.inl (by omega)), M4 _ (by omega) (by omega)]
  · rw [L₆.rr, L₅.rr, L₄.rr, A3.rr]
  · rw [L₆.rm, L₅.rm, L₄.rm, A3.rm]
  · rw [L₆.out, L₅.out, L₄.out, A3.out]

end NcFz

end BKMNW

end PlanarFlow
