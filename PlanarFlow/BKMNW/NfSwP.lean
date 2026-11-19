module

public import PlanarFlow.BKMNW.NfStage
public import WordRAM

/-!
# The words of a stage on the machine: `swP`

The arithmetic of one stage of FixConservationOnPath (`SW`, `NfStage.lean`) as a machine program on
natural words, signed values stored with an offset `K` (`z ↦ z + K`). Inputs (registers):
`9310 = K`, `9311 = Fw i + K`, `9312 = Pw (ia i)`, `9313 = Pw (ib i)`, `9314 = cw i`,
`9315 = cr i`, `9316 = f0w i + K`, `9317 = dv + K`, `9318 = d1 + K` (the change on
`d (i − 1)`, `0` for `i = 0`), `9319 = ia i`, `9320 = ib i`. Outputs: `9330 = cob + K`,
`9331 = f1 + K`, `9332 = bv + K`, `9333 = [bv < 0]`, `9334 = |bv|`, `9335 = res`, `9336 = val0`,
`9337 = f2 + K`, `9338 = [skip]`, `9339 = root`, `9340 = ef`, `9341 = |bv| − val0`. Scratch
`9350 … 9358`.

* `swpA1`, `swpA2`, `swB` (blocks), `swN`/`swQ` (the two branches on `bv < 0`), `swC`;
  **`swP`** `= (swpA1 ; swpA2) ; swB ; (if 9332 < 9310 then swN else swQ) ; swC`;
* the natural values `nCOB` … `nF2` and **`swP_exec`** (`≤ 48` steps);
* **`swP_link`**: with the inputs of `SW` and `|·| ≤ B`, `8 B ≤ K`, the outputs are the words of
  `SW` (`cob`, `f1`, `bv`, `res`, `val0`, `f2`, `skip`, `root`, `ef`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The program -/

/-- `one`, `cob + K`, `f1 + K` (first half). -/
def swpA1 : Stmt :=
  block [.constN 9350 1, .addN 9351 9313 9310, .subN 9330 9351 9312, .addN 9351 9311 9330,
    .subN 9351 9351 9310, .addN 9352 9314 9310, .subN 9353 9351 9352]

/-- `f1 + K` (second half). -/
def swpA2 : Stmt :=
  block [.subN 9353 9351 9353, .subN 9354 9310 9315, .subN 9355 9354 9353,
    .addN 9353 9353 9355, .addN 9353 9353 9310, .subN 9331 9353 9330]

/-- `bv + K`, `|bv|`. -/
def swB : Stmt :=
  block [.addN 9356 9317 9331, .addN 9356 9356 9310, .subN 9356 9356 9316,
    .subN 9332 9356 9318, .subN 9357 9310 9332, .subN 9358 9332 9310, .addN 9334 9358 9357]

/-- The branch `bv < 0` (`e = d i`). -/
def swN : Stmt :=
  block [.addN 9356 9314 9310, .addN 9356 9356 9310, .subN 9356 9356 9331,
    .subN 9335 9356 9330, .subN 9356 9335 9334, .subN 9336 9335 9356, .addN 9337 9331 9336,
    .constN 9333 1, .copyN 9339 9320, .copyN 9340 9319]

/-- The branch `bv ≥ 0` (`e = rev (d i)`). -/
def swQ : Stmt :=
  block [.addN 9356 9315 9331, .addN 9356 9356 9330, .subN 9356 9356 9310,
    .subN 9335 9356 9310, .subN 9356 9335 9334, .subN 9336 9335 9356, .subN 9337 9331 9336,
    .constN 9333 0, .copyN 9339 9319, .copyN 9340 9320]

/-- `|bv| − val0`, `[skip]`. -/
def swC : Stmt := block [.subN 9341 9334 9336, .subN 9338 9350 9341]

/-- **The words of a stage.** -/
def swP : Stmt := .seq (.seq swpA1 swpA2) (.seq swB (.seq (.ifLtN 9332 9310 swN swQ) swC))

/-! ### The natural values -/

/-- `cob + K`. -/
def nCOB (K PA PB : ℕ) : ℕ := PB + K - PA

/-- `f1 + K`. -/
def nF1 (K F PA PB CW CR : ℕ) : ℕ :=
  (F + nCOB K PA PB - K - (F + nCOB K PA PB - K - (CW + K)) +
    (K - CR - (F + nCOB K PA PB - K - (F + nCOB K PA PB - K - (CW + K)))) + K) - nCOB K PA PB

/-- `bv + K`. -/
def nBV (K F PA PB CW CR F0 DV D1 : ℕ) : ℕ := DV + nF1 K F PA PB CW CR + K - F0 - D1

/-- `|bv|`. -/
def nAB (K BV : ℕ) : ℕ := BV - K + (K - BV)

/-- `res`. -/
def nRES (K BV F1 COB CW CR : ℕ) : ℕ :=
  if BV < K then CW + K + K - F1 - COB else CR + F1 + COB - K - K

/-- `val0`. -/
def nV0 (RES AB : ℕ) : ℕ := RES - (RES - AB)

/-- `f2 + K`. -/
def nF2 (K BV F1 V0 : ℕ) : ℕ := if BV < K then F1 + V0 else F1 - V0

/-! ### The run -/

variable {P : Input} {W : ℕ}

/-- The registers written by `swP`. -/
def swScr (r : ℕ) : Prop := (9330 ≤ r ∧ r ≤ 9341) ∨ (9350 ≤ r ∧ r ≤ 9358)

theorem swA_exec (c : Config) (hc : WordsBounded W c) {K F PA PB CW CR : ℕ}
    (r10 : c.nreg 9310 = K) (r11 : c.nreg 9311 = F) (r12 : c.nreg 9312 = PA)
    (r13 : c.nreg 9313 = PB) (r14 : c.nreg 9314 = CW) (r15 : c.nreg 9315 = CR)
    (hF : F ≤ 2 * K) (hPB : PB ≤ 2 * K) (hCW : CW ≤ 2 * K) (hW : 16 * K + 1 ≤ W) :
    ∃ c' t, Exec P W (.seq swpA1 swpA2) c c' t ∧ t = 13 ∧ c'.nreg 9350 = 1 ∧
      c'.nreg 9330 = nCOB K PA PB ∧ c'.nreg 9331 = nF1 K F PA PB CW CR ∧
      (∀ r, ¬ swScr r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a50, a30, a51, a52, a53, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W swpA1 c c₁ t₁ ∧ t₁ = 7 ∧ c₁.nreg 9350 = 1 ∧ c₁.nreg 9330 = nCOB K PA PB ∧
      c₁.nreg 9351 = F + nCOB K PA PB - K ∧ c₁.nreg 9352 = CW + K ∧
      c₁.nreg 9353 = F + nCOB K PA PB - K - (CW + K) ∧
      (∀ r, ¬ swScr r → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold swpA1 nCOB
    exec_block
    all_goals try ((try config_simp); (try simp only [r10, r11, r12, r13, r14, r15]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r10, r11, r12, r13, r14, r15])
    all_goals try omega
    unfold swScr at hr
    simp only [upd_apply]; split_ifs <;> omega
  have hw1 := e₁.wb_right
  have hcob : nCOB K PA PB ≤ 3 * K := by unfold nCOB; omega
  obtain ⟨c₂, t₂, e₂, ht₂, b31, bk, bm, br, brm, bo⟩ : ∃ c₂ t₂,
      Exec P W swpA2 c₁ c₂ t₂ ∧ t₂ = 6 ∧ c₂.nreg 9331 = nF1 K F PA PB CW CR ∧
      (∀ r, r ≠ 9353 → r ≠ 9354 → r ≠ 9355 → r ≠ 9331 → c₂.nreg r = c₁.nreg r) ∧
      c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have q10 : c₁.nreg 9310 = K := by rw [ak _ (by unfold swScr; omega), r10]
    have q15 : c₁.nreg 9315 = CR := by rw [ak _ (by unfold swScr; omega), r15]
    unfold swpA2 nF1
    exec_block
    all_goals try ((try config_simp); (try simp only [q10, q15, a30, a51, a52, a53]); omega)
    refine ⟨rfl, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [q10, q15, a30, a51, a52, a53])
    all_goals try omega
    simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₂, _, .seq e₁ e₂, by omega, ?_, ?_, b31, fun r hr => ?_,
    by rw [bm, am], by rw [br, ar], by rw [brm, arm], by rw [bo, ao]⟩
  · rw [bk _ (by omega) (by omega) (by omega) (by omega), a50]
  · rw [bk _ (by omega) (by omega) (by omega) (by omega), a30]
  · unfold swScr at hr
    rw [bk r (by omega) (by omega) (by omega) (by omega), ak r (by unfold swScr; omega)]

theorem swB_exec (c : Config) (hc : WordsBounded W c) {K F1 F0 DV D1 : ℕ}
    (r10 : c.nreg 9310 = K) (r31 : c.nreg 9331 = F1) (r16 : c.nreg 9316 = F0)
    (r17 : c.nreg 9317 = DV) (r18 : c.nreg 9318 = D1)
    (hF1 : F1 ≤ 6 * K) (hDV : DV ≤ 2 * K) (hW : 16 * K + 1 ≤ W) :
    ∃ c' t, Exec P W swB c c' t ∧ t = 7 ∧ c'.nreg 9332 = DV + F1 + K - F0 - D1 ∧
      c'.nreg 9334 = nAB K (DV + F1 + K - F0 - D1) ∧
      (∀ r, r ≠ 9332 → r ≠ 9334 → r ≠ 9356 → r ≠ 9357 → r ≠ 9358 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold swB nAB
  exec_block
  all_goals try ((try config_simp); (try simp only [r10, r31, r16, r17, r18]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r10, r31, r16, r17, r18])
  all_goals try omega
  simp only [upd_apply]; split_ifs <;> omega

/-- The registers written by a branch. -/
def swBr (r : ℕ) : Prop := r = 9356 ∨ r = 9335 ∨ r = 9336 ∨ r = 9337 ∨ r = 9333 ∨ r = 9339 ∨ r = 9340

theorem swN_exec (c : Config) (hc : WordsBounded W c) {K F1 COB CW AB IA IB : ℕ}
    (r10 : c.nreg 9310 = K) (r31 : c.nreg 9331 = F1) (r30 : c.nreg 9330 = COB)
    (r14 : c.nreg 9314 = CW) (r34 : c.nreg 9334 = AB) (r19 : c.nreg 9319 = IA)
    (r20 : c.nreg 9320 = IB) (hF1 : F1 ≤ 6 * K) (hCW : CW ≤ 2 * K) (hAB : AB ≤ 10 * K)
    (hW : 16 * K + 1 ≤ W) :
    ∃ c' t, Exec P W swN c c' t ∧ t = 10 ∧ c'.nreg 9335 = CW + K + K - F1 - COB ∧
      c'.nreg 9336 = nV0 (CW + K + K - F1 - COB) AB ∧
      c'.nreg 9337 = F1 + nV0 (CW + K + K - F1 - COB) AB ∧ c'.nreg 9333 = 1 ∧
      c'.nreg 9339 = IB ∧ c'.nreg 9340 = IA ∧
      (∀ r, ¬ swBr r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold swN nV0
  exec_block
  all_goals try ((try config_simp); (try simp only [r10, r31, r30, r14, r34, r19, r20]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r10, r31, r30, r14, r34, r19, r20])
  all_goals try omega
  unfold swBr at hr
  simp only [upd_apply]; split_ifs <;> omega

theorem swQ_exec (c : Config) (hc : WordsBounded W c) {K F1 COB CR AB IA IB : ℕ}
    (r10 : c.nreg 9310 = K) (r31 : c.nreg 9331 = F1) (r30 : c.nreg 9330 = COB)
    (r15 : c.nreg 9315 = CR) (r34 : c.nreg 9334 = AB) (r19 : c.nreg 9319 = IA)
    (r20 : c.nreg 9320 = IB) (hF1 : F1 ≤ 6 * K) (hCR : CR ≤ 2 * K) (hCOB : COB ≤ 3 * K)
    (hW : 16 * K + 1 ≤ W) :
    ∃ c' t, Exec P W swQ c c' t ∧ t = 10 ∧ c'.nreg 9335 = CR + F1 + COB - K - K ∧
      c'.nreg 9336 = nV0 (CR + F1 + COB - K - K) AB ∧
      c'.nreg 9337 = F1 - nV0 (CR + F1 + COB - K - K) AB ∧ c'.nreg 9333 = 0 ∧
      c'.nreg 9339 = IA ∧ c'.nreg 9340 = IB ∧
      (∀ r, ¬ swBr r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold swQ nV0
  exec_block
  all_goals try ((try config_simp); (try simp only [r10, r31, r30, r15, r34, r19, r20]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r10, r31, r30, r15, r34, r19, r20])
  all_goals try omega
  unfold swBr at hr
  simp only [upd_apply]; split_ifs <;> omega

theorem swC_exec (c : Config) (hc : WordsBounded W c) {AB V0 : ℕ}
    (r50 : c.nreg 9350 = 1) (r34 : c.nreg 9334 = AB) (r36 : c.nreg 9336 = V0) :
    ∃ c' t, Exec P W swC c c' t ∧ t = 2 ∧ c'.nreg 9341 = AB - V0 ∧
      c'.nreg 9338 = 1 - (AB - V0) ∧
      (∀ r, r ≠ 9341 → r ≠ 9338 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold swC
  exec_block
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r50, r34, r36])
  simp only [upd_apply]; split_ifs <;> omega

lemma nF1_le {K F PA PB CW CR : ℕ} (hF : F ≤ 2 * K) (hPB : PB ≤ 2 * K) :
    nF1 K F PA PB CW CR ≤ 6 * K := by
  unfold nF1 nCOB; omega

lemma nCOB_le {K PA PB : ℕ} (hPB : PB ≤ 2 * K) : nCOB K PA PB ≤ 3 * K := by unfold nCOB; omega

/-- **The words of a stage on the machine.** -/
theorem swP_exec (c : Config) (hc : WordsBounded W c) {K F PA PB CW CR F0 DV D1 IA IB : ℕ}
    (r10 : c.nreg 9310 = K) (r11 : c.nreg 9311 = F) (r12 : c.nreg 9312 = PA)
    (r13 : c.nreg 9313 = PB) (r14 : c.nreg 9314 = CW) (r15 : c.nreg 9315 = CR)
    (r16 : c.nreg 9316 = F0) (r17 : c.nreg 9317 = DV) (r18 : c.nreg 9318 = D1)
    (r19 : c.nreg 9319 = IA) (r20 : c.nreg 9320 = IB)
    (hF : F ≤ 2 * K) (hPB : PB ≤ 2 * K) (hCW : CW ≤ 2 * K) (hCR : CR ≤ 2 * K)
    (hDV : DV ≤ 2 * K) (hW : 16 * K + 1 ≤ W) :
    ∃ c' t, Exec P W swP c c' t ∧ t ≤ 40 ∧
      c'.nreg 9330 = nCOB K PA PB ∧ c'.nreg 9331 = nF1 K F PA PB CW CR ∧
      c'.nreg 9332 = nBV K F PA PB CW CR F0 DV D1 ∧
      c'.nreg 9333 = (if nBV K F PA PB CW CR F0 DV D1 < K then 1 else 0) ∧
      c'.nreg 9334 = nAB K (nBV K F PA PB CW CR F0 DV D1) ∧
      c'.nreg 9335 = nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR) (nCOB K PA PB)
        CW CR ∧
      c'.nreg 9336 = nV0 (nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR)
        (nCOB K PA PB) CW CR) (nAB K (nBV K F PA PB CW CR F0 DV D1)) ∧
      c'.nreg 9337 = nF2 K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR)
        (nV0 (nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR) (nCOB K PA PB) CW CR)
          (nAB K (nBV K F PA PB CW CR F0 DV D1))) ∧
      c'.nreg 9341 = nAB K (nBV K F PA PB CW CR F0 DV D1) -
        nV0 (nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR) (nCOB K PA PB) CW CR)
          (nAB K (nBV K F PA PB CW CR F0 DV D1)) ∧
      c'.nreg 9338 = 1 - (nAB K (nBV K F PA PB CW CR F0 DV D1) -
        nV0 (nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR) (nCOB K PA PB) CW CR)
          (nAB K (nBV K F PA PB CW CR F0 DV D1))) ∧
      c'.nreg 9339 = (if nBV K F PA PB CW CR F0 DV D1 < K then IB else IA) ∧
      c'.nreg 9340 = (if nBV K F PA PB CW CR F0 DV D1 < K then IA else IB) ∧
      (∀ r, ¬ swScr r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hF1 := nF1_le (PA := PA) (CW := CW) (CR := CR) hF hPB
  have hCOB := nCOB_le (PA := PA) hPB
  obtain ⟨c₁, t₁, e₁, ht₁, a50, a30, a31, ak, am, ar, arm, ao⟩ :=
    swA_exec (P := P) c hc r10 r11 r12 r13 r14 r15 hF hPB hCW hW
  have k1 : ∀ r, ¬ swScr r → c₁.nreg r = c.nreg r := ak
  have q : ∀ r, 9310 ≤ r → r ≤ 9320 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    ak r (by unfold swScr; omega)
  obtain ⟨c₂, t₂, e₂, ht₂, b32, b34, bk, bm, br, brm, bo⟩ :=
    swB_exec (P := P) c₁ e₁.wb_right (K := K) (F1 := nF1 K F PA PB CW CR) (F0 := F0) (DV := DV)
      (D1 := D1) (by rw [q _ (by omega) (by omega), r10]) a31
      (by rw [q _ (by omega) (by omega), r16]) (by rw [q _ (by omega) (by omega), r17])
      (by rw [q _ (by omega) (by omega), r18]) hF1 hDV hW
  have hBV : nBV K F PA PB CW CR F0 DV D1 = DV + nF1 K F PA PB CW CR + K - F0 - D1 := rfl
  rw [← hBV] at b32 b34
  have hAB : nAB K (nBV K F PA PB CW CR F0 DV D1) ≤ 10 * K := by
    unfold nAB; rw [hBV]; omega
  have q2 : ∀ r, 9310 ≤ r → r ≤ 9331 → r ≠ 9332 → c₂.nreg r = c₁.nreg r := fun r h1 h2 h3 =>
    bk r h3 (by omega) (by omega) (by omega) (by omega)
  -- the branch
  obtain ⟨c₃, t₃, e₃, ht₃, d35, d36, d37, d33, d39, d40, dk, dm, dr, drm, do'⟩ : ∃ c₃ t₃,
      Exec P W (.ifLtN 9332 9310 swN swQ) c₂ c₃ t₃ ∧ t₃ ≤ 12 ∧
      c₃.nreg 9335 = nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR)
        (nCOB K PA PB) CW CR ∧
      c₃.nreg 9336 = nV0 (nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR)
        (nCOB K PA PB) CW CR) (nAB K (nBV K F PA PB CW CR F0 DV D1)) ∧
      c₃.nreg 9337 = nF2 K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR)
        (nV0 (nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR) (nCOB K PA PB) CW CR)
          (nAB K (nBV K F PA PB CW CR F0 DV D1))) ∧
      c₃.nreg 9333 = (if nBV K F PA PB CW CR F0 DV D1 < K then 1 else 0) ∧
      c₃.nreg 9339 = (if nBV K F PA PB CW CR F0 DV D1 < K then IB else IA) ∧
      c₃.nreg 9340 = (if nBV K F PA PB CW CR F0 DV D1 < K then IA else IB) ∧
      (∀ r, ¬ swBr r → c₃.nreg r = c₂.nreg r) ∧
      c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have s10 : c₂.nreg 9310 = K := by rw [q2 _ (by omega) (by omega) (by omega), q _ (by omega)
      (by omega), r10]
    have s31 : c₂.nreg 9331 = nF1 K F PA PB CW CR := by
      rw [q2 _ (by omega) (by omega) (by omega), a31]
    have s30 : c₂.nreg 9330 = nCOB K PA PB := by
      rw [q2 _ (by omega) (by omega) (by omega), a30]
    have s14 : c₂.nreg 9314 = CW := by
      rw [q2 _ (by omega) (by omega) (by omega), q _ (by omega) (by omega), r14]
    have s15 : c₂.nreg 9315 = CR := by
      rw [q2 _ (by omega) (by omega) (by omega), q _ (by omega) (by omega), r15]
    have s19 : c₂.nreg 9319 = IA := by
      rw [q2 _ (by omega) (by omega) (by omega), q _ (by omega) (by omega), r19]
    have s20 : c₂.nreg 9320 = IB := by
      rw [q2 _ (by omega) (by omega) (by omega), q _ (by omega) (by omega), r20]
    by_cases hlt : nBV K F PA PB CW CR F0 DV D1 < K
    · obtain ⟨c₃, t₃, e₃, ht₃, h35, h36, h37, h33, h39, h40, hk, hm, hr, hrm, ho⟩ :=
        swN_exec (P := P) c₂ e₂.wb_right s10 s31 s30 s14 b34 s19 s20 hF1 hCW hAB hW
      refine ⟨c₃, _, .ifLtN_true (by rw [b32, s10]; exact hlt) e₃, by omega, ?_, ?_, ?_, ?_,
        ?_, ?_, hk, hm, hr, hrm, ho⟩
      · rw [h35]; simp only [nRES, hlt, ↓reduceIte]
      · rw [h36]; simp only [nRES, hlt, ↓reduceIte]
      · rw [h37]; simp only [nRES, nF2, hlt, ↓reduceIte]
      · rw [h33]; simp only [hlt, ↓reduceIte]
      · rw [h39]; simp only [hlt, ↓reduceIte]
      · rw [h40]; simp only [hlt, ↓reduceIte]
    · obtain ⟨c₃, t₃, e₃, ht₃, h35, h36, h37, h33, h39, h40, hk, hm, hr, hrm, ho⟩ :=
        swQ_exec (P := P) c₂ e₂.wb_right s10 s31 s30 s15 b34 s19 s20 hF1 hCR hCOB hW
      refine ⟨c₃, _, .ifLtN_false (by rw [b32, s10]; exact hlt) e₃, by omega, ?_, ?_, ?_, ?_,
        ?_, ?_, hk, hm, hr, hrm, ho⟩
      · rw [h35]; simp only [nRES, hlt, ↓reduceIte]
      · rw [h36]; simp only [nRES, hlt, ↓reduceIte]
      · rw [h37]; simp only [nRES, nF2, hlt, ↓reduceIte]
      · rw [h33]; simp only [hlt, ↓reduceIte]
      · rw [h39]; simp only [hlt, ↓reduceIte]
      · rw [h40]; simp only [hlt, ↓reduceIte]
  have t50 : c₃.nreg 9350 = 1 := by
    rw [dk _ (by unfold swBr; omega), bk _ (by omega) (by omega) (by omega) (by omega)
      (by omega), a50]
  have t34 : c₃.nreg 9334 = nAB K (nBV K F PA PB CW CR F0 DV D1) := by
    rw [dk _ (by unfold swBr; omega), b34]
  obtain ⟨c₄, t₄, e₄, ht₄, f41, f38, fk, fm, fr, frm, fo⟩ :=
    swC_exec (P := P) c₃ e₃.wb_right t50 t34 d36
  have keep3 : ∀ r, r ≠ 9341 → r ≠ 9338 → ¬ swBr r → r ≠ 9332 → r ≠ 9334 → r ≠ 9356 →
      r ≠ 9357 → r ≠ 9358 → c₄.nreg r = c₁.nreg r := fun r h1 h2 h3 h4 h5 h6 h7 h8 => by
    rw [fk r h1 h2, dk r h3, bk r h4 h5 h6 h7 h8]
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, f41,
    f38, ?_, ?_, fun r hr => ?_, by rw [fm, dm, bm, am], by rw [fr, dr, br, ar],
    by rw [frm, drm, brm, arm], by rw [fo, do', bo, ao]⟩
  · rw [keep3 _ (by omega) (by omega) (by unfold swBr; omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), a30]
  · rw [keep3 _ (by omega) (by omega) (by unfold swBr; omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), a31]
  · rw [fk _ (by omega) (by omega), dk _ (by unfold swBr; omega), b32]
  · rw [fk _ (by omega) (by omega), d33]
  · rw [fk _ (by omega) (by omega), t34]
  · rw [fk _ (by omega) (by omega), d35]
  · rw [fk _ (by omega) (by omega), d36]
  · rw [fk _ (by omega) (by omega), d37]
  · rw [fk _ (by omega) (by omega), d39]
  · rw [fk _ (by omega) (by omega), d40]
  · unfold swScr at hr
    rw [keep3 r (by omega) (by omega) (by unfold swBr; omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), ak r (by unfold swScr; omega)]

/-! ### The natural values are the words of `SW` -/

/-- **The outputs of `swP` are the words of the stage** (signed values with the offset `K`),
when the inputs hold the words of `SW` and every input is at most `B` in absolute value,
`8 B ≤ K`. -/
theorem swP_link (w : SW) {K F PA PB CW CR F0 DV D1 : ℕ} {B : ℤ}
    (hF : (F : ℤ) = w.Fw w.i + K) (hPA : (PA : ℤ) = w.Pw (w.ia w.i))
    (hPB : (PB : ℤ) = w.Pw (w.ib w.i)) (hCW : (CW : ℤ) = w.cw w.i) (hCR : (CR : ℤ) = w.cr w.i)
    (hF0 : (F0 : ℤ) = w.f0w w.i + K) (hDV : (DV : ℤ) = w.dv + K)
    (hD1 : (D1 : ℤ) = (if 0 < w.i then w.Fw (w.i - 1) - w.f0w (w.i - 1) else 0) + K)
    (bF : |w.Fw w.i| ≤ B) (bPA : (PA : ℤ) ≤ B) (bPB : (PB : ℤ) ≤ B) (bCW : (CW : ℤ) ≤ B)
    (bCR : (CR : ℤ) ≤ B) (bF0 : |w.f0w w.i| ≤ B) (bDV : |w.dv| ≤ B)
    (bD1 : |(if 0 < w.i then w.Fw (w.i - 1) - w.f0w (w.i - 1) else 0)| ≤ B)
    (hBK : 8 * B ≤ K) :
    (nCOB K PA PB : ℤ) = w.cob + K ∧ (nF1 K F PA PB CW CR : ℤ) = w.f1 + K ∧
    (nBV K F PA PB CW CR F0 DV D1 : ℤ) = w.bv + K ∧
    (nBV K F PA PB CW CR F0 DV D1 < K ↔ w.bv < 0) ∧
    (nAB K (nBV K F PA PB CW CR F0 DV D1) : ℤ) = |w.bv| ∧
    (nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR) (nCOB K PA PB) CW CR : ℤ) =
      w.res ∧
    (nV0 (nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR) (nCOB K PA PB) CW CR)
      (nAB K (nBV K F PA PB CW CR F0 DV D1)) : ℤ) = w.val0 ∧
    (nF2 K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR)
      (nV0 (nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR) (nCOB K PA PB) CW CR)
        (nAB K (nBV K F PA PB CW CR F0 DV D1))) : ℤ) = w.f2 + K ∧
    ((nAB K (nBV K F PA PB CW CR F0 DV D1) -
      nV0 (nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR) (nCOB K PA PB) CW CR)
        (nAB K (nBV K F PA PB CW CR F0 DV D1)) : ℕ) : ℤ) = |w.bv| - w.val0 ∧
    (1 - (nAB K (nBV K F PA PB CW CR F0 DV D1) -
      nV0 (nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR) (nCOB K PA PB) CW CR)
        (nAB K (nBV K F PA PB CW CR F0 DV D1))) = 1 ↔ w.skip) := by
  generalize hd1 : (if 0 < w.i then w.Fw (w.i - 1) - w.f0w (w.i - 1) else 0) = d1 at hD1 bD1
  have ebv : w.bv = w.dv + (w.f1 - w.f0w w.i) - d1 := by unfold SW.bv; rw [hd1]
  rw [abs_le] at bF bF0 bDV bD1
  -- `cob`
  have h1 : (nCOB K PA PB : ℤ) = w.cob + K := by
    unfold nCOB SW.cob; omega
  -- `f1`
  have h2 : (nF1 K F PA PB CW CR : ℤ) = w.f1 + K := by
    have := h1
    unfold nF1 SW.f1
    rw [← hCW, ← hCR, show w.Fw w.i = F - (K : ℤ) by omega, show w.cob = nCOB K PA PB - (K : ℤ) by
      omega]
    unfold nCOB at this ⊢
    omega
  have bf1 : -(CR : ℤ) - B ≤ w.f1 ∧ w.f1 ≤ (CW : ℤ) + B := by
    unfold SW.f1 SW.cob; rw [← hCW, ← hCR, ← hPA, ← hPB]; omega
  -- `bv`
  have h3 : (nBV K F PA PB CW CR F0 DV D1 : ℤ) = w.bv + K := by
    have := h2
    unfold nBV
    rw [ebv]
    omega
  have h4 : nBV K F PA PB CW CR F0 DV D1 < K ↔ w.bv < 0 := by omega
  have h5 : (nAB K (nBV K F PA PB CW CR F0 DV D1) : ℤ) = |w.bv| := by
    unfold nAB; rw [abs_eq_max_neg]; omega
  -- `res`
  have h6 : (nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR) (nCOB K PA PB) CW CR :
      ℤ) = w.res := by
    have hc1 : w.f1 + w.cob ≤ CW ∧ -(CR : ℤ) ≤ w.f1 + w.cob := by
      unfold SW.f1; rw [← hCW, ← hCR]; omega
    unfold nRES SW.res
    by_cases hb : nBV K F PA PB CW CR F0 DV D1 < K
    · simp only [hb, ↓reduceIte, h4.1 hb]; rw [← hCW]; omega
    · simp only [hb, ↓reduceIte, show ¬ w.bv < 0 from fun h => hb (h4.2 h)]; rw [← hCR]; omega
  have hres0 : 0 ≤ w.res := by rw [← h6]; omega
  -- `val0`
  have h7 : (nV0 (nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR) (nCOB K PA PB) CW
      CR) (nAB K (nBV K F PA PB CW CR F0 DV D1)) : ℤ) = w.val0 := by
    unfold nV0 SW.val0
    omega
  have hv0 : w.val0 ≤ |w.bv| := min_le_right _ _
  have hv00 : 0 ≤ w.val0 := le_min hres0 (abs_nonneg _)
  -- `f2`
  have h8 : (nF2 K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR)
      (nV0 (nRES K (nBV K F PA PB CW CR F0 DV D1) (nF1 K F PA PB CW CR) (nCOB K PA PB) CW CR)
        (nAB K (nBV K F PA PB CW CR F0 DV D1))) : ℤ) = w.f2 + K := by
    have hab := h5
    rw [abs_eq_max_neg] at hab hv0
    have hcob : w.cob = (PB : ℤ) - PA := by unfold SW.cob; rw [hPA, hPB]
    unfold nF2 SW.f2
    by_cases hb : nBV K F PA PB CW CR F0 DV D1 < K
    · simp only [hb, ↓reduceIte, h4.1 hb]; omega
    · simp only [hb, ↓reduceIte, show ¬ w.bv < 0 from fun h => hb (h4.2 h)]
      have : w.val0 ≤ w.res := min_le_left _ _
      unfold SW.res at this
      simp only [show ¬ w.bv < 0 from fun h => hb (h4.2 h), ↓reduceIte] at this
      omega
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, by omega, ?_⟩
  unfold SW.skip
  omega

end BKMNW

end PlanarFlow
