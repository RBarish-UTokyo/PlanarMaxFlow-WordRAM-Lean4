module

public import PlanarFlow.BKMNW.NrKahnM

/-!
# Kahn's algorithm on the machine: the program and its blocks

Inputs (registers `9100 … 9105`): `m`, the vertex labels `VL` (`VL[j]` the label of the tail of
dart `j`), the reverse darts `RV`, the flow array `G` (positive dart: `Z < G[j]`), `Z`, the
scratch base `S`. Scratch `[S, S + 8m + 1)`: `POS`, `IND`, the queue `Q`, the counting sort
(`osProg`, `[S + 3m, S + 5m + 1)`), `OB`, `OE`, `OL`. Registers `9106 … 9127`.

1. `IND := 0`; loop P: `POS[j] := [Z < G[j]]`, `IND[VL[RV[j]]] += POS[j]`;
2. `osProg`: the positive darts by tail label;
3. scan: push every label `v = VL[v]` with `IND[v] = 0`;
4. main loop: pop `u`, for every positive dart `j` of `u`: `IND[w] -= 1` (`w = VL[RV[j]]`), push
   `w` when it reaches zero.

The run is in `NrKahnRun.lean`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

/-! ### The program -/

/-- The constants and the bases. -/
def kA : Stmt :=
  block [.constN 9106 1, .constN 9107 0, .addN 9108 9105 9100, .addN 9109 9108 9100,
    .addN 9110 9109 9100, .addN 9111 9110 9100, .addN 9111 9111 9106, .addN 9112 9111 9100,
    .addN 9113 9112 9100, .addN 9114 9113 9100]

/-- `i := 0`. -/
def kI0 : Stmt := block [.constN 9115 0]

/-- `IND[i] := 0`. -/
def kahnZ : Stmt := block [.addN 9116 9108 9115, .storeN 9116 9107, .addN 9115 9115 9106]

/-- `g := G[i]`, the address of `POS[i]`. -/
def kP1 : Stmt := block [.addN 9116 9103 9115, .loadN 9117 9116, .addN 9118 9105 9115]

/-- A positive dart: `POS[i] := 1`, `IND[VL[RV[i]]] += 1`. -/
def kPT : Stmt :=
  block [.addN 9116 9102 9115, .loadN 9116 9116, .addN 9116 9101 9116,
    .loadN 9116 9116, .addN 9116 9108 9116, .loadN 9119 9116, .addN 9119 9119 9106,
    .storeN 9116 9119, .storeN 9118 9106]

/-- `POS[i] := 0`. -/
def kPF : Stmt := block [.storeN 9118 9107]

/-- `i := i + 1`. -/
def kP2 : Stmt := block [.addN 9115 9115 9106]

/-- One dart of loop P. -/
def kP : Stmt := .seq kP1 (.seq (.ifLtN 9104 9117 kPT kPF) kP2)

/-- The registers of `osProg`. -/
def kOs : Stmt :=
  block [.copyN 1500 9100, .copyN 1501 9100, .copyN 1502 9101, .copyN 1504 9105,
    .copyN 1505 9110, .copyN 1506 9111, .copyN 1507 9112, .copyN 1508 9113, .copyN 1509 9114]

/-- `i := 0`, `t := 0`. -/
def kI1 : Stmt := block [.constN 9115 0, .constN 9120 0]

/-- Push the label in `r`: `Q[t] := r`, `t := t + 1`. -/
def kPush (r : ℕ) : Stmt := block [.addN 9118 9109 9120, .storeN 9118 r, .addN 9120 9120 9106]

/-- `x := VL[i]`. -/
def kS1 : Stmt := block [.addN 9116 9101 9115, .loadN 9116 9116]

/-- `y := IND[i]`. -/
def kS2 : Stmt := block [.addN 9117 9108 9115, .loadN 9117 9117]

/-- One label of the scan: push it if it is a vertex (`¬ VL[i] < i`) without entering positive
dart. -/
def kS : Stmt :=
  .seq kS1 (.seq (.ifLtN 9116 9115 .skip (.seq kS2 (.ifLtN 9107 9117 .skip (kPush 9115)))) kP2)

/-- Pop `u := Q[h]`, `h := h + 1`, its interval `[OB[u], OE[u])`. -/
def kM1 : Stmt :=
  block [.addN 9116 9109 9121, .loadN 9122 9116, .addN 9121 9121 9106, .addN 9116 9112 9122,
    .loadN 9123 9116, .addN 9116 9113 9122, .loadN 9124 9116]

/-- `w := VL[RV[OL[k]]]`, `IND[w] -= 1`. -/
def kahnN1 : Stmt :=
  block [.addN 9116 9114 9123, .loadN 9116 9116, .addN 9116 9102 9116, .loadN 9116 9116,
    .addN 9116 9101 9116, .loadN 9125 9116, .addN 9126 9108 9125, .loadN 9127 9126,
    .subN 9127 9127 9106, .storeN 9126 9127]

/-- `k := k + 1`. -/
def kN2 : Stmt := block [.addN 9123 9123 9106]

/-- One positive dart of the popped vertex. -/
def kN : Stmt := .seq kahnN1 (.seq (.ifLtN 9107 9127 .skip (kPush 9125)) kN2)

/-- One pop. -/
def kM : Stmt := .seq kM1 (.whileLtN 9123 9124 kN)

/-- **Kahn's algorithm.** -/
def kahnP : Stmt :=
  .seq kA (.seq kI0 (.seq (.whileLtN 9115 9100 kahnZ) (.seq kI0 (.seq (.whileLtN 9115 9100 kP)
    (.seq kOs (.seq osProg (.seq kI1 (.seq (.whileLtN 9115 9100 kS)
      (.seq (block [.constN 9121 0]) (.whileLtN 9121 9120 kM))))))))))

theorem kahnP_natOnly : Klein.natOnly kahnP = true := by kernel_rfl

/-! ### The blocks -/

section Blocks

variable {P : Input} {W : ℕ}

theorem kA_exec (c : Config) (hc : WordsBounded W c) {m S : ℕ} (r0 : c.nreg 9100 = m)
    (r5 : c.nreg 9105 = S) (w : S + 8 * m + 1 ≤ W) :
    ∃ c' t, Exec P W kA c c' t ∧ t = 10 ∧ c'.nreg 9106 = 1 ∧ c'.nreg 9107 = 0 ∧
      c'.nreg 9108 = S + m ∧ c'.nreg 9109 = S + 2 * m ∧ c'.nreg 9110 = S + 3 * m ∧
      c'.nreg 9111 = S + 4 * m + 1 ∧ c'.nreg 9112 = S + 5 * m + 1 ∧
      c'.nreg 9113 = S + 6 * m + 1 ∧ c'.nreg 9114 = S + 7 * m + 1 ∧
      (∀ x, (x < 9106 ∨ 9114 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kA
  exec_block
  all_goals try (clear * - r0 r5 w; config_simp; (try simp only [r0, r5]); omega)
  all_goals try (clear * - w; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r0, r5]
  all_goals try omega
  simp only [upd_apply]; split_ifs <;> omega

theorem kI0_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W kI0 c c' t ∧ t = 1 ∧ c'.nreg 9115 = 0 ∧
      (∀ x, x ≠ 9115 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kI0
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem kI1_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W kI1 c c' t ∧ t = 2 ∧ c'.nreg 9115 = 0 ∧ c'.nreg 9120 = 0 ∧
      (∀ x, x ≠ 9115 → x ≠ 9120 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kI1
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

theorem kH0_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (block [.constN 9121 0]) c c' t ∧ t = 1 ∧ c'.nreg 9121 = 0 ∧
      (∀ x, x ≠ 9121 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem kahnZ_exec (c : Config) (hc : WordsBounded W c) {A i : ℕ} (r8 : c.nreg 9108 = A)
    (r15 : c.nreg 9115 = i) (r6 : c.nreg 9106 = 1) (r7 : c.nreg 9107 = 0) (w : A + i + 1 ≤ W) :
    ∃ c' t, Exec P W kahnZ c c' t ∧ t = 3 ∧ c'.nreg 9115 = i + 1 ∧
      c'.nmem = upd c.nmem (A + i) 0 ∧ (∀ x, x ≠ 9115 → x ≠ 9116 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kahnZ
  exec_block
  all_goals try (config_simp; simp only [r8, r15, r6, r7]; omega)
  refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r6, r15]
  · config_simp; simp only [r8, r15, r7]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem kP2_exec (c : Config) (hc : WordsBounded W c) {i : ℕ} (r15 : c.nreg 9115 = i)
    (r6 : c.nreg 9106 = 1) (w : i + 1 ≤ W) :
    ∃ c' t, Exec P W kP2 c c' t ∧ t = 1 ∧ c'.nreg 9115 = i + 1 ∧
      (∀ x, x ≠ 9115 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kP2
  exec_block
  all_goals try (config_simp; simp only [r15, r6]; omega)
  refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r15, r6]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem kPT_exec (c : Config) (hc : WordsBounded W c) {VL RV A i Pa : ℕ}
    (r1 : c.nreg 9101 = VL) (r2 : c.nreg 9102 = RV) (r6 : c.nreg 9106 = 1)
    (r8 : c.nreg 9108 = A) (r15 : c.nreg 9115 = i) (r18 : c.nreg 9118 = Pa)
    (w3 : RV + i ≤ W) (w4 : VL + c.nmem (RV + i) ≤ W)
    (w5 : A + c.nmem (VL + c.nmem (RV + i)) ≤ W)
    (w6 : c.nmem (A + c.nmem (VL + c.nmem (RV + i))) + 1 ≤ W) (w7 : Pa ≤ W) :
    ∃ c' t, Exec P W kPT c c' t ∧ t = 9 ∧
      c'.nmem = upd (upd c.nmem (A + c.nmem (VL + c.nmem (RV + i)))
        (c.nmem (A + c.nmem (VL + c.nmem (RV + i))) + 1)) Pa 1 ∧
      (∀ x, (x < 9116 ∨ 9119 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kPT
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r6, r8, r15, r18]; omega)
  refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r1, r2, r6, r8, r15, r18]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem kPF_exec (c : Config) (hc : WordsBounded W c) {Pa : ℕ} (r18 : c.nreg 9118 = Pa)
    (r7 : c.nreg 9107 = 0) (w : Pa ≤ W) :
    ∃ c' t, Exec P W kPF c c' t ∧ t = 1 ∧ c'.nmem = upd c.nmem Pa 0 ∧
      (∀ x, c'.nreg x = c.nreg x) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold kPF
  exec_block
  all_goals try (config_simp; simp only [r18, r7]; omega)
  refine ⟨rfl, ?_, fun x => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r18, r7]
  · config_simp

theorem kS2_exec (c : Config) (hc : WordsBounded W c) {A i : ℕ} (r8 : c.nreg 9108 = A)
    (r15 : c.nreg 9115 = i) (w : A + i ≤ W) :
    ∃ c' t, Exec P W kS2 c c' t ∧ t = 2 ∧ c'.nreg 9117 = c.nmem (A + i) ∧
      (∀ x, x ≠ 9117 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kS2
  exec_block
  all_goals try (config_simp; simp only [r8, r15]; omega)
  refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r8, r15]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- One dart of loop P. -/
theorem kP_exec (c : Config) (hc : WordsBounded W c) {VL RV G Z S A i : ℕ}
    (r1 : c.nreg 9101 = VL) (r2 : c.nreg 9102 = RV) (r3 : c.nreg 9103 = G)
    (r4 : c.nreg 9104 = Z) (r5 : c.nreg 9105 = S) (r6 : c.nreg 9106 = 1) (r7 : c.nreg 9107 = 0)
    (r8 : c.nreg 9108 = A) (r15 : c.nreg 9115 = i) (w1 : G + i ≤ W) (w2 : S + i ≤ W)
    (w3 : RV + i ≤ W) (w4 : VL + c.nmem (RV + i) ≤ W)
    (w5 : A + c.nmem (VL + c.nmem (RV + i)) ≤ W)
    (w6 : c.nmem (A + c.nmem (VL + c.nmem (RV + i))) + 1 ≤ W) (w7 : i + 1 ≤ W)
    (hne : S + i ≠ A + c.nmem (VL + c.nmem (RV + i))) :
    ∃ c' t, Exec P W kP c c' t ∧ t ≤ 15 ∧ c'.nreg 9115 = i + 1 ∧
      c'.nmem = (if Z < c.nmem (G + i) then
          upd (upd c.nmem (A + c.nmem (VL + c.nmem (RV + i)))
            (c.nmem (A + c.nmem (VL + c.nmem (RV + i))) + 1)) (S + i) 1
        else upd c.nmem (S + i) 0) ∧
      (∀ x, (x < 9115 ∨ 9119 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g17, g18, f₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ t₁, Exec P W kP1 c c₁ t₁ ∧
      t₁ = 3 ∧ c₁.nreg 9117 = c.nmem (G + i) ∧ c₁.nreg 9118 = S + i ∧
      (∀ x, x ≠ 9116 → x ≠ 9117 → x ≠ 9118 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold kP1
    exec_block
    all_goals try (config_simp; simp only [r3, r5, r15]; omega)
    refine ⟨rfl, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r3, r15]
    · config_simp; simp only [r5, r15]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have q : ∀ x, 9115 ≤ x → x ≤ 9115 ∨ x < 9116 → c₁.nreg x = c.nreg x := fun x h1 h2 =>
    f₁ x (by omega) (by omega) (by omega)
  have k1 : ∀ x, x < 9116 → c₁.nreg x = c.nreg x := fun x h => f₁ x (by omega) (by omega) (by omega)
  by_cases hz : Z < c.nmem (G + i)
  · obtain ⟨c₂, t₂, e₂, ht₂, m₂, f₂, rr₂, rm₂, o₂⟩ := kPT_exec (P := P) c₁ e₁.wb_right
      (VL := VL) (RV := RV) (A := A) (i := i) (Pa := S + i)
      (by rw [k1 _ (by omega), r1]) (by rw [k1 _ (by omega), r2]) (by rw [k1 _ (by omega), r6])
      (by rw [k1 _ (by omega), r8]) (by rw [k1 _ (by omega), r15]) g18
      w3 (by rw [m₁]; exact w4) (by rw [m₁]; exact w5) (by rw [m₁]; exact w6)
      w2
    have hlt : c₁.nreg 9104 < c₁.nreg 9117 := by rw [k1 _ (by omega), r4, g17]; exact hz
    obtain ⟨c₃, t₃, e₃, ht₃, g15, f₃, m₃, rr₃, rm₃, o₃⟩ := kP2_exec (P := P) c₂ e₂.wb_right
      (i := i) (by rw [f₂ _ (by omega), k1 _ (by omega), r15])
      (by rw [f₂ _ (by omega), k1 _ (by omega), r6]) w7
    refine ⟨c₃, t₁ + (t₂ + 1 + t₃), .seq e₁ (.seq (.ifLtN_true hlt e₂) e₃), by omega, g15,
      by rw [m₃, m₂, if_pos hz, m₁], fun x hx => ?_, by rw [rr₃, rr₂, rr₁], by rw [rm₃, rm₂, rm₁],
      by rw [o₃, o₂, o₁]⟩
    rw [f₃ x (by omega), f₂ x (by omega), f₁ x (by omega) (by omega) (by omega)]
  · obtain ⟨c₂, t₂, e₂, ht₂, m₂, f₂, rr₂, rm₂, o₂⟩ := kPF_exec (P := P) c₁ e₁.wb_right
      (Pa := S + i) g18 (by rw [k1 _ (by omega), r7]) w2
    have hlt : ¬ c₁.nreg 9104 < c₁.nreg 9117 := by rw [k1 _ (by omega), r4, g17]; exact hz
    obtain ⟨c₃, t₃, e₃, ht₃, g15, f₃, m₃, rr₃, rm₃, o₃⟩ := kP2_exec (P := P) c₂ e₂.wb_right
      (i := i) (by rw [f₂, k1 _ (by omega), r15]) (by rw [f₂, k1 _ (by omega), r6]) w7
    refine ⟨c₃, t₁ + (t₂ + 2 + t₃), .seq e₁ (.seq (.ifLtN_false hlt e₂) e₃), by omega, g15,
      by rw [m₃, m₂, if_neg hz, m₁], fun x hx => ?_, by rw [rr₃, rr₂, rr₁], by rw [rm₃, rm₂, rm₁],
      by rw [o₃, o₂, o₁]⟩
    rw [f₃ x (by omega), f₂ x, f₁ x (by omega) (by omega) (by omega)]

theorem kOs_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W kOs c c' t ∧ t = 9 ∧ c'.nreg 1500 = c.nreg 9100 ∧
      c'.nreg 1501 = c.nreg 9100 ∧ c'.nreg 1502 = c.nreg 9101 ∧ c'.nreg 1504 = c.nreg 9105 ∧
      c'.nreg 1505 = c.nreg 9110 ∧ c'.nreg 1506 = c.nreg 9111 ∧ c'.nreg 1507 = c.nreg 9112 ∧
      c'.nreg 1508 = c.nreg 9113 ∧ c'.nreg 1509 = c.nreg 9114 ∧
      (∀ x, (x < 1500 ∨ 1509 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kOs
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try rfl
  simp only [upd_apply]; split_ifs <;> omega

theorem kPush_exec (c : Config) (hc : WordsBounded W c) {r Qb t : ℕ} (hr : r ≠ 9118)
    (hr' : r ≠ 9120) (r9 : c.nreg 9109 = Qb) (r20 : c.nreg 9120 = t) (r6 : c.nreg 9106 = 1)
    (w : Qb + t + 1 ≤ W) :
    ∃ c' k, Exec P W (kPush r) c c' k ∧ k = 3 ∧ c'.nreg 9120 = t + 1 ∧
      c'.nmem = upd c.nmem (Qb + t) (c.nreg r) ∧
      (∀ x, x ≠ 9118 → x ≠ 9120 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kPush
  exec_block
  all_goals try (config_simp; simp only [r9, r20, r6]; omega)
  refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r6]
  · config_simp; simp only [r9, r20, upd_apply]; split_ifs <;> first | omega | rfl
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- One label of the scan. -/
theorem kS_exec (c : Config) (hc : WordsBounded W c) {VL A Qb i t : ℕ}
    (r1 : c.nreg 9101 = VL) (r6 : c.nreg 9106 = 1) (r7 : c.nreg 9107 = 0)
    (r8 : c.nreg 9108 = A) (r9 : c.nreg 9109 = Qb) (r15 : c.nreg 9115 = i)
    (r20 : c.nreg 9120 = t) (w1 : VL + i ≤ W) (w2 : A + i ≤ W) (w3 : Qb + t + 1 ≤ W)
    (w4 : i + 1 ≤ W) :
    ∃ c' k, Exec P W kS c c' k ∧ k ≤ 14 ∧ c'.nreg 9115 = i + 1 ∧
      (if c.nmem (VL + i) < i ∨ 0 < c.nmem (A + i) then
        c'.nreg 9120 = t ∧ c'.nmem = c.nmem
      else c'.nreg 9120 = t + 1 ∧ c'.nmem = upd c.nmem (Qb + t) i) ∧
      (∀ x, (x < 9115 ∨ 9120 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g16, f₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ t₁, Exec P W kS1 c c₁ t₁ ∧
      t₁ = 2 ∧ c₁.nreg 9116 = c.nmem (VL + i) ∧ (∀ x, x ≠ 9116 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold kS1
    exec_block
    all_goals try (config_simp; simp only [r1, r15]; omega)
    refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r1, r15]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  -- the tail: `i := i + 1`
  have tail : ∀ c₂ t₂, Exec P W (.ifLtN 9116 9115 .skip
        (.seq kS2 (.ifLtN 9107 9117 .skip (kPush 9115)))) c₁ c₂ t₂ → t₂ ≤ 11 →
      c₂.nreg 9115 = i → c₂.nreg 9106 = 1 →
      (∀ x, (x < 9115 ∨ 9120 < x) → c₂.nreg x = c.nreg x) →
      c₂.rreg = c.rreg → c₂.rmem = c.rmem → c₂.output = c.output →
      ∃ c' k, Exec P W kS c c' k ∧ k ≤ 14 ∧ c'.nreg 9115 = i + 1 ∧ c'.nreg 9120 = c₂.nreg 9120 ∧
        c'.nmem = c₂.nmem ∧ (∀ x, (x < 9115 ∨ 9120 < x) → c'.nreg x = c.nreg x) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    intro c₂ t₂ e₂ ht₂ h15 h6 f₂ rr₂ rm₂ o₂
    obtain ⟨c₃, t₃, e₃, ht₃, g15, f₃, m₃, rr₃, rm₃, o₃⟩ := kP2_exec (P := P) c₂ e₂.wb_right
      (i := i) h15 h6 w4
    exact ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, g15, f₃ _ (by omega), m₃,
      fun x hx => by rw [f₃ x (by omega), f₂ x hx], by rw [rr₃, rr₂], by rw [rm₃, rm₂],
      by rw [o₃, o₂]⟩
  by_cases h1 : c.nmem (VL + i) < i
  · have hlt : c₁.nreg 9116 < c₁.nreg 9115 := by rw [g16, f₁ _ (by omega), r15]; exact h1
    obtain ⟨c', k, e', hk, g15, g20, gm, gf, gr, grm, go⟩ := tail c₁ _ (.ifLtN_true hlt
      (.skip e₁.wb_right)) (by omega) (by rw [f₁ _ (by omega), r15])
      (by rw [f₁ _ (by omega), r6]) (fun x hx => f₁ x (by omega)) rr₁ rm₁ o₁
    refine ⟨c', k, e', hk, g15, ?_, gf, gr, grm, go⟩
    rw [if_pos (Or.inl h1)]
    exact ⟨by rw [g20, f₁ _ (by omega), r20], by rw [gm, m₁]⟩
  have hnlt : ¬ c₁.nreg 9116 < c₁.nreg 9115 := by rw [g16, f₁ _ (by omega), r15]; exact h1
  obtain ⟨c₂, t₂, e₂, ht₂, g17, f₂, m₂, rr₂, rm₂, o₂⟩ := kS2_exec (P := P) c₁ e₁.wb_right
    (A := A) (i := i) (by rw [f₁ _ (by omega), r8]) (by rw [f₁ _ (by omega), r15]) w2
  rw [m₁] at g17
  have k2 : ∀ x, x ≠ 9116 → x ≠ 9117 → c₂.nreg x = c.nreg x := fun x h1 h2 => by
    rw [f₂ x h2, f₁ x h1]
  by_cases h2 : 0 < c.nmem (A + i)
  · have hlt : c₂.nreg 9107 < c₂.nreg 9117 := by rw [k2 _ (by omega) (by omega), r7, g17]; exact h2
    obtain ⟨c', k, e', hk, g15, g20, gm, gf, gr, grm, go⟩ := tail c₂ _
      (.ifLtN_false hnlt (.seq e₂ (.ifLtN_true hlt (.skip e₂.wb_right)))) (by omega)
      (by rw [k2 _ (by omega) (by omega), r15]) (by rw [k2 _ (by omega) (by omega), r6])
      (fun x hx => k2 x (by omega) (by omega)) (by rw [rr₂, rr₁]) (by rw [rm₂, rm₁])
      (by rw [o₂, o₁])
    refine ⟨c', k, e', hk, g15, ?_, gf, gr, grm, go⟩
    rw [if_pos (Or.inr h2)]
    exact ⟨by rw [g20, k2 _ (by omega) (by omega), r20], by rw [gm, m₂, m₁]⟩
  · have hlt : ¬ c₂.nreg 9107 < c₂.nreg 9117 := by
      rw [k2 _ (by omega) (by omega), r7, g17]; exact h2
    obtain ⟨c₃, t₃, e₃, ht₃, g20, m₃, f₃, rr₃, rm₃, o₃⟩ := kPush_exec (P := P) c₂ e₂.wb_right
      (r := 9115) (by omega) (by omega) (by rw [k2 _ (by omega) (by omega), r9])
      (by rw [k2 _ (by omega) (by omega), r20]) (by rw [k2 _ (by omega) (by omega), r6]) w3
    obtain ⟨c', k, e', hk, g15, g20', gm, gf, gr, grm, go⟩ := tail c₃ _
      (.ifLtN_false hnlt (.seq e₂ (.ifLtN_false hlt e₃))) (by omega)
      (by rw [f₃ _ (by omega) (by omega), k2 _ (by omega) (by omega), r15])
      (by rw [f₃ _ (by omega) (by omega), k2 _ (by omega) (by omega), r6])
      (fun x hx => by rw [f₃ x (by omega) (by omega), k2 x (by omega) (by omega)])
      (by rw [rr₃, rr₂, rr₁]) (by rw [rm₃, rm₂, rm₁]) (by rw [o₃, o₂, o₁])
    refine ⟨c', k, e', hk, g15, ?_, gf, gr, grm, go⟩
    rw [if_neg (by push Not at h1 h2 ⊢; exact ⟨h1, h2⟩)]
    exact ⟨by rw [g20', g20], by rw [gm, m₃, m₂, m₁, k2 _ (by omega) (by omega), r15]⟩

theorem kM1_exec (c : Config) (hc : WordsBounded W c) {Qb OBb OEb h : ℕ}
    (r9 : c.nreg 9109 = Qb) (r12 : c.nreg 9112 = OBb) (r13 : c.nreg 9113 = OEb)
    (r21 : c.nreg 9121 = h) (r6 : c.nreg 9106 = 1) (w1 : Qb + h ≤ W)
    (w2 : OBb + c.nmem (Qb + h) ≤ W) (w3 : OEb + c.nmem (Qb + h) ≤ W) (w4 : h + 1 ≤ W) :
    ∃ c' t, Exec P W kM1 c c' t ∧ t = 7 ∧ c'.nreg 9122 = c.nmem (Qb + h) ∧
      c'.nreg 9121 = h + 1 ∧ c'.nreg 9123 = c.nmem (OBb + c.nmem (Qb + h)) ∧
      c'.nreg 9124 = c.nmem (OEb + c.nmem (Qb + h)) ∧
      (∀ x, x ≠ 9116 → (x < 9121 ∨ 9124 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kM1
  exec_block
  all_goals try (config_simp; simp only [r9, r12, r13, r21, r6]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r9, r12, r13, r21, r6]
  simp only [upd_apply]; split_ifs <;> omega

theorem kahnN1_exec (c : Config) (hc : WordsBounded W c) {OLb RV VL A k : ℕ}
    (r14 : c.nreg 9114 = OLb) (r23 : c.nreg 9123 = k) (r2 : c.nreg 9102 = RV)
    (r1 : c.nreg 9101 = VL) (r8 : c.nreg 9108 = A) (r6 : c.nreg 9106 = 1) (w1 : OLb + k ≤ W)
    (w2 : RV + c.nmem (OLb + k) ≤ W) (w3 : VL + c.nmem (RV + c.nmem (OLb + k)) ≤ W)
    (w4 : A + c.nmem (VL + c.nmem (RV + c.nmem (OLb + k))) ≤ W) :
    ∃ c' t, Exec P W kahnN1 c c' t ∧ t = 10 ∧
      c'.nreg 9125 = c.nmem (VL + c.nmem (RV + c.nmem (OLb + k))) ∧
      c'.nreg 9126 = A + c.nmem (VL + c.nmem (RV + c.nmem (OLb + k))) ∧
      c'.nreg 9127 = c.nmem (A + c.nmem (VL + c.nmem (RV + c.nmem (OLb + k)))) - 1 ∧
      c'.nmem = upd c.nmem (A + c.nmem (VL + c.nmem (RV + c.nmem (OLb + k))))
        (c.nmem (A + c.nmem (VL + c.nmem (RV + c.nmem (OLb + k)))) - 1) ∧
      (∀ x, x ≠ 9116 → (x < 9125 ∨ 9127 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kahnN1
  exec_block
  all_goals try (config_simp; simp only [r14, r23, r2, r1, r8, r6]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r14, r23, r2, r1, r8, r6]
  simp only [upd_apply]; split_ifs <;> omega

theorem kN2_exec (c : Config) (hc : WordsBounded W c) {k : ℕ} (r23 : c.nreg 9123 = k)
    (r6 : c.nreg 9106 = 1) (w : k + 1 ≤ W) :
    ∃ c' t, Exec P W kN2 c c' t ∧ t = 1 ∧ c'.nreg 9123 = k + 1 ∧
      (∀ x, x ≠ 9123 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kN2
  exec_block
  all_goals try (config_simp; simp only [r23, r6]; omega)
  refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r23, r6]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- One positive dart of the popped vertex. -/
theorem kN_exec (c : Config) (hc : WordsBounded W c) {OLb RV VL A Qb k t : ℕ}
    (r14 : c.nreg 9114 = OLb) (r23 : c.nreg 9123 = k) (r2 : c.nreg 9102 = RV)
    (r1 : c.nreg 9101 = VL) (r8 : c.nreg 9108 = A) (r6 : c.nreg 9106 = 1)
    (r7 : c.nreg 9107 = 0) (r9 : c.nreg 9109 = Qb) (r20 : c.nreg 9120 = t) (w1 : OLb + k ≤ W)
    (w2 : RV + c.nmem (OLb + k) ≤ W) (w3 : VL + c.nmem (RV + c.nmem (OLb + k)) ≤ W)
    (w4 : A + c.nmem (VL + c.nmem (RV + c.nmem (OLb + k))) ≤ W) (w5 : Qb + t + 1 ≤ W)
    (w6 : k + 1 ≤ W) :
    ∃ c' t', Exec P W kN c c' t' ∧ t' ≤ 16 ∧ c'.nreg 9123 = k + 1 ∧
      (if 0 < c.nmem (A + c.nmem (VL + c.nmem (RV + c.nmem (OLb + k)))) - 1 then
        c'.nreg 9120 = t ∧ c'.nmem = upd c.nmem (A + c.nmem (VL + c.nmem (RV + c.nmem (OLb + k))))
          (c.nmem (A + c.nmem (VL + c.nmem (RV + c.nmem (OLb + k)))) - 1)
      else c'.nreg 9120 = t + 1 ∧
        c'.nmem = upd (upd c.nmem (A + c.nmem (VL + c.nmem (RV + c.nmem (OLb + k))))
          (c.nmem (A + c.nmem (VL + c.nmem (RV + c.nmem (OLb + k)))) - 1)) (Qb + t)
          (c.nmem (VL + c.nmem (RV + c.nmem (OLb + k))))) ∧
      (∀ x, x ≠ 9116 → x ≠ 9118 → x ≠ 9120 → x ≠ 9123 → (x < 9125 ∨ 9127 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g25, g26, g27, m₁, f₁, rr₁, rm₁, o₁⟩ := kahnN1_exec (P := P) c hc
    r14 r23 r2 r1 r8 r6 w1 w2 w3 w4
  have k1 : ∀ x, (x < 9116 ∨ 9127 < x) → c₁.nreg x = c.nreg x := fun x hx =>
    f₁ x (by omega) (by omega)
  have tail : ∀ c₂ t₂, Exec P W (.ifLtN 9107 9127 .skip (kPush 9125)) c₁ c₂ t₂ → t₂ ≤ 5 →
      c₂.nreg 9123 = k → c₂.nreg 9106 = 1 →
      (∀ x, x ≠ 9116 → x ≠ 9118 → x ≠ 9120 → (x < 9125 ∨ 9127 < x) → c₂.nreg x = c.nreg x) →
      c₂.rreg = c.rreg → c₂.rmem = c.rmem → c₂.output = c.output →
      ∃ c' t', Exec P W kN c c' t' ∧ t' ≤ 16 ∧ c'.nreg 9123 = k + 1 ∧
        c'.nreg 9120 = c₂.nreg 9120 ∧ c'.nmem = c₂.nmem ∧
        (∀ x, x ≠ 9116 → x ≠ 9118 → x ≠ 9120 → x ≠ 9123 → (x < 9125 ∨ 9127 < x) →
        c'.nreg x = c.nreg x) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    intro c₂ t₂ e₂ ht₂ h23 h6 f₂ rr₂ rm₂ o₂
    obtain ⟨c₃, t₃, e₃, ht₃, g23, f₃, m₃, rr₃, rm₃, o₃⟩ := kN2_exec (P := P) c₂ e₂.wb_right
      h23 h6 w6
    exact ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, g23, f₃ _ (by omega), m₃,
      fun x h1 h2 h3 h4 h5 => by rw [f₃ x h4, f₂ x h1 h2 h3 h5], by rw [rr₃, rr₂], by rw [rm₃, rm₂],
      by rw [o₃, o₂]⟩
  by_cases hx : 0 < c.nmem (A + c.nmem (VL + c.nmem (RV + c.nmem (OLb + k)))) - 1
  · have hlt : c₁.nreg 9107 < c₁.nreg 9127 := by rw [k1 _ (by omega), r7, g27]; exact hx
    obtain ⟨c', k', e', hk, g23, g20, gm, gf, gr, grm, go⟩ := tail c₁ _
      (.ifLtN_true hlt (.skip e₁.wb_right)) (by omega) (by rw [f₁ _ (by omega) (by omega), r23])
      (by rw [k1 _ (by omega), r6]) (fun x h1 h2 h3 h4 => f₁ x h1 h4) rr₁ rm₁ o₁
    refine ⟨c', k', e', hk, g23, ?_, gf, gr, grm, go⟩
    rw [if_pos hx]
    exact ⟨by rw [g20, f₁ _ (by omega) (by omega), r20], by rw [gm, m₁]⟩
  · have hlt : ¬ c₁.nreg 9107 < c₁.nreg 9127 := by rw [k1 _ (by omega), r7, g27]; exact hx
    obtain ⟨c₂, t₂, e₂, ht₂, g20, m₂, f₂, rr₂, rm₂, o₂⟩ := kPush_exec (P := P) c₁ e₁.wb_right
      (r := 9125) (by omega) (by omega) (by rw [k1 _ (by omega), r9])
      (by rw [f₁ _ (by omega) (by omega), r20]) (by rw [k1 _ (by omega), r6]) w5
    obtain ⟨c', k', e', hk, g23, g20', gm, gf, gr, grm, go⟩ := tail c₂ _
      (.ifLtN_false hlt e₂) (by omega) (by rw [f₂ _ (by omega) (by omega), f₁ _ (by omega) (by omega), r23])
      (by rw [f₂ _ (by omega) (by omega), k1 _ (by omega), r6])
      (fun x h1 h2 h3 h4 => by rw [f₂ x h2 h3, f₁ x h1 h4])
      (by rw [rr₂, rr₁]) (by rw [rm₂, rm₁]) (by rw [o₂, o₁])
    refine ⟨c', k', e', hk, g23, ?_, gf, gr, grm, go⟩
    rw [if_neg hx]
    exact ⟨by rw [g20', g20], by rw [gm, m₂, m₁, g25]⟩

end Blocks

end BKMNW

end PlanarFlow
