module

public import PlanarFlow.BKMNW.Nf7bA

/-!
# The stage loop of `fixP`, part B: the small machine pieces of a stage

Registers of the stage loop: `9500 = i` (the stage), `9501 = PWb` (prices `PW[x] = Pw x`, `x < b`),
`9502 = F0b` (`F0[l] = f₀ (d l) + K`), `9503 = DVb` (`DV[l] = div f₀ (p l) + K`),
`9504 = ETb` (`ET[a] = idx (face (dartAt a))`, `a < 2k`, so `ia l = ET[2l]`, `ib l = ET[2l+1]`);
scratch `9505 … 9511`, `9520 … 9524`, `9530`, `9531`.

* **`ldP`** — load the words of stage `i` into the inputs `9311 … 9320` of `swP` (and `9372 = i`
  for `elP`): `FW[i]`, `PW[ia]`, `PW[ib]`, `CW[i]`, `CR[i]`, `F0[i]`, `DV[i]`,
  `d1 = FW[i−1] + K − F0[i−1]` (`K` at `i = 0`), `ia`, `ib`;
* **`prP`** — `PR[x] := PW[x] + K` (`x < b`, the prices as `FrImgIn`/`imU` read them);
* **`rtP`** — `r7606 := root`;
* **`rdP`** — the new prices from the FR answers: `PW[x] := rdV flag res PWroot` (`PWroot + res`
  or `PWroot + res − M` when reached, `PWroot` otherwise);
* **`fwP`** — `FW[i] := F2 + PW'[ia] − PA` (`bv < 0`) or `F2 + PB − PW'[ib]`; **`skP`** — `FW[i] := F2`;
* `incP` — `i := i + 1`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The programs -/

/-- Load the words of the stage (all but `d1`). -/
def ldA1 : Stmt :=
  block [.constN 9510 1, .constN 9511 0, .copyN 9372 9500,
    .addN 9505 9376 9500, .loadN 9311 9505,
    .addN 9505 9504 9500, .addN 9505 9505 9500, .loadN 9319 9505,
    .addN 9505 9505 9510, .loadN 9320 9505]

/-- Load the words of the stage (second half). -/
def ldA2 : Stmt :=
  block [.addN 9505 9501 9319, .loadN 9312 9505,
    .addN 9505 9501 9320, .loadN 9313 9505,
    .addN 9505 9374 9500, .loadN 9314 9505,
    .addN 9505 9375 9500, .loadN 9315 9505,
    .addN 9505 9502 9500, .loadN 9316 9505,
    .addN 9505 9503 9500, .loadN 9317 9505, .copyN 9318 9310]

/-- Load the words of the stage (all but `d1`). -/
def ldA : Stmt := .seq ldA1 ldA2

/-- `d1 + K = FW[i−1] + K − F0[i−1]` (for `i > 0`). -/
def ldD : Stmt :=
  block [.subN 9506 9500 9510, .addN 9505 9376 9506, .loadN 9507 9505,
    .addN 9505 9502 9506, .loadN 9508 9505, .addN 9507 9507 9310, .subN 9318 9507 9508]

/-- **Load the words of stage `i`.** -/
def ldP : Stmt := .seq ldA (.ifLtN 9511 9500 ldD .skip)

/-- The body of `prP`. -/
def prBody : Stmt :=
  block [.addN 9521 9501 9520, .loadN 9522 9521, .addN 9522 9522 9310, .addN 9521 8102 9520,
    .storeN 9521 9522, .addN 9520 9520 9510]

/-- **`PR[x] := PW[x] + K`** for `x < b` (`b = r8100`). -/
def prP : Stmt := .seq (block [.constN 9520 0]) (.whileLtN 9520 8100 prBody)

/-- **`r7606 := root`.** -/
def rtP : Stmt := block [.copyN 7606 9339]

/-- The value of a new price: `PWroot` if not reached, else `PWroot + frDec res`. -/
def rdV (fl rs pr H Mo : ℕ) : ℕ := if fl = 1 then (if H < rs then pr + rs - Mo else rs + pr) else pr

/-- The reads of the body of `rdP`. -/
def rdA : Stmt := block [.addN 9521 7614 9520, .loadN 9522 9521, .addN 9521 9521 7600,
  .loadN 9523 9521]

/-- The value of the body of `rdP`. -/
def rdB : Stmt := .ifLtN 9522 9510 (block [.copyN 9524 9530])
  (.ifLtN 9510 9522 (block [.copyN 9524 9530])
    (.ifLtN 7611 9523 (block [.addN 9524 9530 9523, .subN 9524 9524 7610])
      (block [.addN 9524 9523 9530])))

/-- The store of the body of `rdP`. -/
def rdC : Stmt := block [.addN 9521 9501 9520, .storeN 9521 9524, .addN 9520 9520 9510]

/-- The body of `rdP`. -/
def rdBody : Stmt := .seq rdA (.seq rdB rdC)

/-- **The new prices** `PW[x] := rdV (mem[Ob + x]) (mem[Ob + b + x]) PW[root] H M` for `x < b`
(`Ob = r7614`, `b = r7600`, `H = r7611`, `M = r7610`). -/
def rdP : Stmt :=
  .seq (block [.addN 9531 9501 9339, .loadN 9530 9531, .constN 9520 0]) (.whileLtN 9520 7600 rdBody)

/-- The reads of `fwP`: the new prices at `ia`, `ib`. -/
def fwA : Stmt := block [.addN 9505 9501 9319, .loadN 9506 9505, .addN 9505 9501 9320,
  .loadN 9507 9505]

/-- **`FW[i] := f3 + K`.** -/
def fwP : Stmt :=
  .seq fwA (.seq (.ifLtN 9333 9510 (block [.addN 9508 9337 9313, .subN 9508 9508 9507])
    (block [.addN 9508 9337 9506, .subN 9508 9508 9312]))
    (block [.addN 9505 9376 9500, .storeN 9505 9508]))

/-- **`FW[i] := f2 + K`** (a skipped stage). -/
def skP : Stmt := block [.addN 9505 9376 9500, .storeN 9505 9337]

/-- `i := i + 1`. -/
def incP : Stmt := block [.addN 9500 9500 9510]

/-! ### The runs -/

variable {P : Input} {W : ℕ}

theorem ldA1_exec (c : Config) (hc : WordsBounded W c) {i FWb ETb : ℕ}
    (r00 : c.nreg 9500 = i) (r76 : c.nreg 9376 = FWb) (r04 : c.nreg 9504 = ETb)
    (hA : FWb + i ≤ W ∧ ETb + i + i + 1 ≤ W) :
    ∃ c' t, Exec P W ldA1 c c' t ∧ t = 10 ∧ c'.nreg 9510 = 1 ∧ c'.nreg 9511 = 0 ∧
      c'.nreg 9372 = i ∧ c'.nreg 9311 = c.nmem (FWb + i) ∧
      c'.nreg 9319 = c.nmem (ETb + i + i) ∧ c'.nreg 9320 = c.nmem (ETb + i + i + 1) ∧
      (∀ r, r ≠ 9510 → r ≠ 9511 → r ≠ 9372 → r ≠ 9505 → r ≠ 9311 → r ≠ 9319 → r ≠ 9320 →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h1, h2⟩ := hA
  unfold ldA1
  exec_block
  all_goals try ((try config_simp); (try simp only [r00, r76, r04]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r q1 q2 q3 q4 q5 q6 q7 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r00, r76, r04])
  all_goals try rfl
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem ldA2_exec (c : Config) (hc : WordsBounded W c) {i K PWb CWb CRb F0b DVb IA IB : ℕ}
    (r00 : c.nreg 9500 = i) (r10 : c.nreg 9310 = K) (r01 : c.nreg 9501 = PWb)
    (r74 : c.nreg 9374 = CWb) (r75 : c.nreg 9375 = CRb) (r02 : c.nreg 9502 = F0b)
    (r03 : c.nreg 9503 = DVb) (r19 : c.nreg 9319 = IA) (r20 : c.nreg 9320 = IB)
    (hA : PWb + IA ≤ W ∧ PWb + IB ≤ W ∧ CWb + i ≤ W ∧ CRb + i ≤ W ∧ F0b + i ≤ W ∧
      DVb + i ≤ W) :
    ∃ c' t, Exec P W ldA2 c c' t ∧ t = 13 ∧
      c'.nreg 9312 = c.nmem (PWb + IA) ∧ c'.nreg 9313 = c.nmem (PWb + IB) ∧
      c'.nreg 9314 = c.nmem (CWb + i) ∧ c'.nreg 9315 = c.nmem (CRb + i) ∧
      c'.nreg 9316 = c.nmem (F0b + i) ∧ c'.nreg 9317 = c.nmem (DVb + i) ∧ c'.nreg 9318 = K ∧
      (∀ r, r ≠ 9505 → (r < 9312 ∨ 9318 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hA
  unfold ldA2
  exec_block
  all_goals try ((try config_simp); (try simp only [r00, r10, r01, r74, r75, r02, r03, r19, r20]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r q1 q2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r00, r10, r01, r74, r75, r02, r03, r19, r20])
  all_goals try rfl
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem ldD_exec (c : Config) (hc : WordsBounded W c) {i K FWb F0b : ℕ}
    (r00 : c.nreg 9500 = i) (r10 : c.nreg 9310 = K) (r76 : c.nreg 9376 = FWb)
    (r02 : c.nreg 9502 = F0b) (r510 : c.nreg 9510 = 1) (hi : 0 < i)
    (hA : FWb + i ≤ W ∧ F0b + i ≤ W ∧ c.nmem (FWb + (i - 1)) + K ≤ W) :
    ∃ c' t, Exec P W ldD c c' t ∧ t = 7 ∧
      c'.nreg 9318 = c.nmem (FWb + (i - 1)) + K - c.nmem (F0b + (i - 1)) ∧
      (∀ r, r ≠ 9318 → (r < 9505 ∨ 9508 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h1, h2, h3⟩ := hA
  unfold ldD
  exec_block
  all_goals try ((try config_simp); (try simp only [r00, r10, r76, r02, r510]); omega)
  refine ⟨rfl, ?_, fun r q1 q2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r00, r10, r76, r02, r510])
  all_goals try rfl
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

/-- **The loads of a stage.** -/
theorem ldP_exec (c : Config) (hc : WordsBounded W c) {i K FWb ETb PWb CWb CRb F0b DVb : ℕ}
    (r00 : c.nreg 9500 = i) (r10 : c.nreg 9310 = K) (r76 : c.nreg 9376 = FWb)
    (r04 : c.nreg 9504 = ETb) (r01 : c.nreg 9501 = PWb) (r74 : c.nreg 9374 = CWb)
    (r75 : c.nreg 9375 = CRb) (r02 : c.nreg 9502 = F0b) (r03 : c.nreg 9503 = DVb)
    (hA : FWb + i ≤ W ∧ ETb + i + i + 1 ≤ W ∧ PWb + c.nmem (ETb + i + i) ≤ W ∧
      PWb + c.nmem (ETb + i + i + 1) ≤ W ∧ CWb + i ≤ W ∧ CRb + i ≤ W ∧ F0b + i ≤ W ∧
      DVb + i ≤ W ∧ c.nmem (FWb + (i - 1)) + K ≤ W) :
    ∃ c' t, Exec P W ldP c c' t ∧ t ≤ 33 ∧ c'.nreg 9510 = 1 ∧ c'.nreg 9511 = 0 ∧
      c'.nreg 9372 = i ∧ c'.nreg 9311 = c.nmem (FWb + i) ∧
      c'.nreg 9319 = c.nmem (ETb + i + i) ∧ c'.nreg 9320 = c.nmem (ETb + i + i + 1) ∧
      c'.nreg 9312 = c.nmem (PWb + c.nmem (ETb + i + i)) ∧
      c'.nreg 9313 = c.nmem (PWb + c.nmem (ETb + i + i + 1)) ∧
      c'.nreg 9314 = c.nmem (CWb + i) ∧ c'.nreg 9315 = c.nmem (CRb + i) ∧
      c'.nreg 9316 = c.nmem (F0b + i) ∧ c'.nreg 9317 = c.nmem (DVb + i) ∧
      c'.nreg 9318 = (if 0 < i then c.nmem (FWb + (i - 1)) + K - c.nmem (F0b + (i - 1)) else K) ∧
      (∀ r, r ≠ 9510 → r ≠ 9511 → r ≠ 9372 → (r < 9505 ∨ 9508 < r) → (r < 9311 ∨ 9320 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hA
  obtain ⟨c₁, t₁, e₁, ht₁, a10, a11, a72, a11', a19, a20, ak, am, ar, arm, ao⟩ :=
    ldA1_exec (P := P) c hc r00 r76 r04 ⟨h1, h2⟩
  have q : ∀ r, r ≠ 9510 → r ≠ 9511 → r ≠ 9372 → r ≠ 9505 → r ≠ 9311 → r ≠ 9319 → r ≠ 9320 →
      c₁.nreg r = c.nreg r := ak
  obtain ⟨c₂, t₂, e₂, ht₂, b12, b13, b14, b15, b16, b17, b18, bk, bm, br, brm, bo⟩ :=
    ldA2_exec (P := P) c₁ e₁.wb_right (i := i) (K := K) (PWb := PWb) (CWb := CWb) (CRb := CRb)
      (F0b := F0b) (DVb := DVb)
      (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r00])
      (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r10])
      (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r01])
      (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r74])
      (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r75])
      (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r02])
      (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r03])
      a19 a20 ⟨h3, h4, h5, h6, h7, h8⟩
  have q2 : ∀ r, r ≠ 9510 → r ≠ 9511 → r ≠ 9372 → r ≠ 9505 → (r < 9311 ∨ 9320 < r) →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 => by
    rw [bk r h4 (by omega), q r h1 h2 h3 h4 (by omega) (by omega) (by omega)]
  have s00 : c₂.nreg 9500 = i := by rw [q2 _ (by omega) (by omega) (by omega) (by omega) (by omega), r00]
  have s11 : c₂.nreg 9511 = 0 := by rw [bk _ (by omega) (by omega), a11]
  have s10 : c₂.nreg 9510 = 1 := by rw [bk _ (by omega) (by omega), a10]
  have hw2 := e₂.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, d18, dk, dm, dr, drm, do'⟩ : ∃ c₃ t₃,
      Exec P W (.ifLtN 9511 9500 ldD .skip) c₂ c₃ t₃ ∧ t₃ ≤ 9 ∧
      c₃.nreg 9318 = (if 0 < i then c.nmem (FWb + (i - 1)) + K - c.nmem (F0b + (i - 1)) else K) ∧
      (∀ r, r ≠ 9318 → (r < 9505 ∨ 9508 < r) → c₃.nreg r = c₂.nreg r) ∧
      c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    by_cases hi : 0 < i
    · obtain ⟨c₃, t₃, e₃, ht₃, d18, dk, dm, dr, drm, do'⟩ :=
        ldD_exec (P := P) c₂ hw2 (i := i) (K := K) (FWb := FWb) (F0b := F0b) s00
          (by rw [q2 _ (by omega) (by omega) (by omega) (by omega) (by omega), r10])
          (by rw [q2 _ (by omega) (by omega) (by omega) (by omega) (by omega), r76])
          (by rw [q2 _ (by omega) (by omega) (by omega) (by omega) (by omega), r02]) s10 hi
          ⟨h1, h7, by rw [bm, am]; exact h9⟩
      refine ⟨c₃, _, .ifLtN_true (by rw [s11, s00]; exact hi) e₃, by omega, ?_, dk, dm, dr, drm,
        do'⟩
      rw [d18, bm, am]; simp only [hi, ↓reduceIte]
    · refine ⟨c₂, _, .ifLtN_false (by rw [s11, s00]; exact hi) (.skip hw2), by omega, ?_,
        fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
      rw [b18]; simp only [hi, ↓reduceIte]
  refine ⟨c₃, _, .seq (.seq e₁ e₂) e₃, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    d18, fun r h1 h2 h3 h4 h5 => ?_, by rw [dm, bm, am], by rw [dr, br, ar], by rw [drm, brm, arm],
    by rw [do', bo, ao]⟩
  · rw [dk _ (by omega) (by omega), s10]
  · rw [dk _ (by omega) (by omega), s11]
  · rw [dk _ (by omega) (by omega), bk _ (by omega) (by omega), a72]
  · rw [dk _ (by omega) (by omega), bk _ (by omega) (by omega), a11']
  · rw [dk _ (by omega) (by omega), bk _ (by omega) (by omega), a19]
  · rw [dk _ (by omega) (by omega), bk _ (by omega) (by omega), a20]
  · rw [dk _ (by omega) (by omega), b12, am]
  · rw [dk _ (by omega) (by omega), b13, am]
  · rw [dk _ (by omega) (by omega), b14, am]
  · rw [dk _ (by omega) (by omega), b15, am]
  · rw [dk _ (by omega) (by omega), b16, am]
  · rw [dk _ (by omega) (by omega), b17, am]
  · rw [dk r (by omega) h4, q2 r h1 h2 h3 (by omega) h5]

theorem prBody_exec (c : Config) (hc : WordsBounded W c) {x K PWb PRb : ℕ}
    (r20 : c.nreg 9520 = x) (r01 : c.nreg 9501 = PWb) (r02 : c.nreg 8102 = PRb)
    (r10 : c.nreg 9310 = K) (r510 : c.nreg 9510 = 1)
    (hA : PWb + x ≤ W ∧ c.nmem (PWb + x) + K ≤ W ∧ PRb + x ≤ W ∧ x + 1 ≤ W) :
    ∃ c' t, Exec P W prBody c c' t ∧ t = 6 ∧ c'.nreg 9520 = x + 1 ∧
      (∀ a, c'.nmem a = if a = PRb + x then c.nmem (PWb + x) + K else c.nmem a) ∧
      (∀ r, r ≠ 9520 → r ≠ 9521 → r ≠ 9522 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h1, h2, h3, h4⟩ := hA
  unfold prBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r01, r02, r10, r510]); omega)
  refine ⟨rfl, ?_, fun a => ?_, fun r q1 q2 q3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r20, r01, r02, r10, r510])
  all_goals try rfl
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

/-- **`PR[x] := PW[x] + K`.** -/
theorem prP_exec (c : Config) (hc : WordsBounded W c) {b K PWb PRb : ℕ}
    (r00 : c.nreg 8100 = b) (r01 : c.nreg 9501 = PWb) (r02 : c.nreg 8102 = PRb)
    (r10 : c.nreg 9310 = K) (r510 : c.nreg 9510 = 1) (hd : PWb + b ≤ PRb)
    (hA : PRb + b ≤ W ∧ ∀ x < b, c.nmem (PWb + x) + K ≤ W) :
    ∃ c' t, Exec P W prP c c' t ∧ t ≤ 8 * b + 3 ∧
      (∀ x < b, c'.nmem (PRb + x) = c.nmem (PWb + x) + K) ∧
      (∀ a, ¬ (PRb ≤ a ∧ a < PRb + b) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 9520 → r ≠ 9521 → r ≠ 9522 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h1, h2⟩ := hA
  obtain ⟨c₁, t₁, e₁, ht₁, a20, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.constN 9520 0]) c c₁ t₁ ∧ t₁ = 1 ∧ c₁.nreg 9520 = 0 ∧
      (∀ r, r ≠ 9520 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun x c' =>
    (∀ y < x, c'.nmem (PRb + y) = c.nmem (PWb + y) + K) ∧
    (∀ a, ¬ (PRb ≤ a ∧ a < PRb + x) → c'.nmem a = c.nmem a) ∧
    (∀ r, r ≠ 9520 → r ≠ 9521 → r ≠ 9522 → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, hJ⟩ := NegSSSP.forLoop_exec (P := P) (a := 9520) (bR := 8100)
    (body := prBody) J (K := 6) (n := b) c₁ e₁.wb_right a20 (by rw [ak _ (by omega), r00])
    ⟨fun y hy => absurd hy (by omega), fun a _ => by rw [am], fun r h _ _ => ak r h, ar, arm, ao⟩
    (fun x c' hx hw ha hb hJ => by
      obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
      have mPW : c'.nmem (PWb + x) = c.nmem (PWb + x) := j2 _ (by omega)
      obtain ⟨c'', t, ex, ht, h20, hm, hk, hr, hrm, ho⟩ :=
        prBody_exec (P := P) c' hw (x := x) (K := K) (PWb := PWb) (PRb := PRb) ha
          (by rw [jn _ (by omega) (by omega) (by omega), r01])
          (by rw [jn _ (by omega) (by omega) (by omega), r02])
          (by rw [jn _ (by omega) (by omega) (by omega), r10])
          (by rw [jn _ (by omega) (by omega) (by omega), r510])
          ⟨by omega, by rw [mPW]; exact h2 x hx, by omega, by omega⟩
      refine ⟨c'', t, ex, ht.le, h20, by rw [hk _ (by omega) (by omega) (by omega)]; exact hb,
        fun y hy => ?_, fun a ha' => ?_, fun r q1 q2 q3 => (hk r q1 q2 q3).trans (jn r q1 q2 q3),
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hy with h | rfl
        · simp only [show PRb + y ≠ PRb + x by omega, ↓reduceIte]; exact j1 y h
        · simp only [↓reduceIte, mPW]
      · rw [hm]
        simp only [show a ≠ PRb + x by omega, ↓reduceIte]
        exact j2 a (by omega))
  obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
  refine ⟨c₂, _, .seq e₁ e₂, by omega, j1, j2, jn, jr, jrm, jo⟩

theorem rtP_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W rtP c c' t ∧ t = 1 ∧ c'.nreg 7606 = c.nreg 9339 ∧
      (∀ r, r ≠ 7606 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rtP
  exec_block
  refine ⟨rfl, ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

theorem incP_exec (c : Config) (hc : WordsBounded W c) {i : ℕ} (r00 : c.nreg 9500 = i)
    (r510 : c.nreg 9510 = 1) (hi : i + 1 ≤ W) :
    ∃ c' t, Exec P W incP c c' t ∧ t = 1 ∧ c'.nreg 9500 = i + 1 ∧
      (∀ r, r ≠ 9500 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold incP
  exec_block
  all_goals try (simp only [r00, r510]; omega)
  refine ⟨rfl, ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r00, r510]
  · simp only [upd_apply]; split_ifs <;> omega

theorem skP_exec (c : Config) (hc : WordsBounded W c) {i FWb : ℕ} (r00 : c.nreg 9500 = i)
    (r76 : c.nreg 9376 = FWb) (hA : FWb + i ≤ W) :
    ∃ c' t, Exec P W skP c c' t ∧ t = 2 ∧
      (∀ a, c'.nmem a = if a = FWb + i then c.nreg 9337 else c.nmem a) ∧
      (∀ r, r ≠ 9505 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold skP
  exec_block
  all_goals try (simp only [r00, r76]; omega)
  refine ⟨rfl, fun a => ?_, fun r h => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r00, r76])
  all_goals try rfl
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem rdA_exec (c : Config) (hc : WordsBounded W c) {x b Ob : ℕ}
    (r20 : c.nreg 9520 = x) (r14 : c.nreg 7614 = Ob) (r7600 : c.nreg 7600 = b)
    (hA : Ob + b + x ≤ W) :
    ∃ c' t, Exec P W rdA c c' t ∧ t = 4 ∧ c'.nreg 9522 = c.nmem (Ob + x) ∧
      c'.nreg 9523 = c.nmem (Ob + x + b) ∧
      (∀ r, r ≠ 9521 → r ≠ 9522 → r ≠ 9523 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rdA
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r14, r7600]); omega)
  refine ⟨rfl, ?_, ?_, fun r q1 q2 q3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r20, r14, r7600])
  all_goals try rfl
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem rdB_exec (c : Config) (hc : WordsBounded W c) {fl rs pr H Mo : ℕ}
    (r22 : c.nreg 9522 = fl) (r23 : c.nreg 9523 = rs) (r30 : c.nreg 9530 = pr)
    (r510 : c.nreg 9510 = 1) (r11 : c.nreg 7611 = H) (r10 : c.nreg 7610 = Mo)
    (hA' : fl = 1 → pr + rs ≤ W) :
    ∃ c' t, Exec P W rdB c c' t ∧ t ≤ 7 ∧ c'.nreg 9524 = rdV fl rs pr H Mo ∧
      (∀ r, r ≠ 9524 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rdB
  obtain ⟨cz, tz, ez, htz, z24, zk, zm, zr, zrm, zo⟩ : ∃ c' t,
      Exec P W (block [.copyN 9524 9530]) c c' t ∧ t = 1 ∧ c'.nreg 9524 = pr ∧
      (∀ r, r ≠ 9524 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    refine ⟨rfl, ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    · exact r30
    · simp only [upd_apply]; split_ifs <;> omega
  by_cases h1 : fl < 1
  · refine ⟨cz, _, .ifLtN_true (by rw [r22, r510]; exact h1) ez, by omega, ?_, zk, zm, zr, zrm,
      zo⟩
    rw [z24]; unfold rdV; simp only [show fl ≠ 1 by omega, ↓reduceIte]
  by_cases h1' : 1 < fl
  · refine ⟨cz, _, .ifLtN_false (by rw [r22, r510]; exact h1)
      (.ifLtN_true (by rw [r22, r510]; exact h1') ez), by omega, ?_, zk, zm, zr, zrm, zo⟩
    rw [z24]; unfold rdV; simp only [show fl ≠ 1 by omega, ↓reduceIte]
  have hf : fl = 1 := by omega
  have hA := hA' hf
  · by_cases h2 : H < rs
    · obtain ⟨c', t, e, ht, h24, hk, hm, hr, hrm, ho⟩ : ∃ c' t,
          Exec P W (block [.addN 9524 9530 9523, .subN 9524 9524 7610]) c c' t ∧ t = 2 ∧
          c'.nreg 9524 = pr + rs - Mo ∧
          (∀ r, r ≠ 9524 → c'.nreg r = c.nreg r) ∧
          c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
        exec_block
        all_goals try ((try config_simp); (try simp only [r30, r23]); omega)
        refine ⟨rfl, ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
        all_goals config_simp
        all_goals try (simp only [r30, r23, r10])
        all_goals try rfl
        all_goals try (simp only [upd_apply]; split_ifs <;> omega)
      refine ⟨c', _, .ifLtN_false (by rw [r22, r510]; exact h1)
        (.ifLtN_false (by rw [r22, r510]; exact h1') (.ifLtN_true (by rw [r11, r23]; exact h2) e)),
        by omega, ?_, hk, hm, hr, hrm, ho⟩
      rw [h24]; unfold rdV; simp only [hf, h2, ↓reduceIte]
    · obtain ⟨c', t, e, ht, h24, hk, hm, hr, hrm, ho⟩ : ∃ c' t,
          Exec P W (block [.addN 9524 9523 9530]) c c' t ∧ t = 1 ∧
          c'.nreg 9524 = rs + pr ∧
          (∀ r, r ≠ 9524 → c'.nreg r = c.nreg r) ∧
          c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
        exec_block
        all_goals try ((try config_simp); (try simp only [r30, r23]); omega)
        refine ⟨rfl, ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
        all_goals config_simp
        all_goals try (simp only [r30, r23])
        all_goals try rfl
        all_goals try (simp only [upd_apply]; split_ifs <;> omega)
      refine ⟨c', _, .ifLtN_false (by rw [r22, r510]; exact h1)
        (.ifLtN_false (by rw [r22, r510]; exact h1') (.ifLtN_false (by rw [r11, r23]; exact h2) e)),
        by omega, ?_, hk, hm, hr, hrm, ho⟩
      rw [h24]; unfold rdV; simp only [hf, h2, ↓reduceIte]

theorem rdC_exec (c : Config) (hc : WordsBounded W c) {x PWb : ℕ}
    (r20 : c.nreg 9520 = x) (r01 : c.nreg 9501 = PWb) (r510 : c.nreg 9510 = 1)
    (hA : PWb + x ≤ W ∧ x + 1 ≤ W) :
    ∃ c' t, Exec P W rdC c c' t ∧ t = 3 ∧ c'.nreg 9520 = x + 1 ∧
      (∀ a, c'.nmem a = if a = PWb + x then c.nreg 9524 else c.nmem a) ∧
      (∀ r, r ≠ 9520 → r ≠ 9521 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h1, h2⟩ := hA
  unfold rdC
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r01, r510]); omega)
  refine ⟨rfl, ?_, fun a => ?_, fun r q1 q2 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r20, r01, r510])
  all_goals try rfl
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem rdBody_exec (c : Config) (hc : WordsBounded W c) {x b Ob PWb pr H Mo : ℕ}
    (r20 : c.nreg 9520 = x) (r14 : c.nreg 7614 = Ob) (r7600 : c.nreg 7600 = b)
    (r01 : c.nreg 9501 = PWb) (r30 : c.nreg 9530 = pr) (r510 : c.nreg 9510 = 1)
    (r11 : c.nreg 7611 = H) (r10 : c.nreg 7610 = Mo)
    (hA : Ob + b + x ≤ W ∧ (c.nmem (Ob + x) = 1 → pr + c.nmem (Ob + x + b) ≤ W) ∧
      PWb + x ≤ W ∧ x + 1 ≤ W) :
    ∃ c' t, Exec P W rdBody c c' t ∧ t ≤ 14 ∧ c'.nreg 9520 = x + 1 ∧
      (∀ a, c'.nmem a = if a = PWb + x then
        rdV (c.nmem (Ob + x)) (c.nmem (Ob + x + b)) pr H Mo else c.nmem a) ∧
      (∀ r, r ≠ 9520 → r ≠ 9521 → r ≠ 9522 → r ≠ 9523 → r ≠ 9524 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h1, h2, h3, h4⟩ := hA
  obtain ⟨c₁, t₁, e₁, ht₁, a22, a23, ak, am, ar, arm, ao⟩ :=
    rdA_exec (P := P) c hc r20 r14 r7600 h1
  obtain ⟨c₂, t₂, e₂, ht₂, b24, bk, bm, br, brm, bo⟩ :=
    rdB_exec (P := P) c₁ e₁.wb_right a22 a23 (by rw [ak _ (by omega) (by omega) (by omega), r30])
      (by rw [ak _ (by omega) (by omega) (by omega), r510])
      (by rw [ak _ (by omega) (by omega) (by omega), r11])
      (by rw [ak _ (by omega) (by omega) (by omega), r10]) h2
  have q : ∀ r, r ≠ 9521 → r ≠ 9522 → r ≠ 9523 → r ≠ 9524 → c₂.nreg r = c.nreg r :=
    fun r q1 q2 q3 q4 => by rw [bk r q4, ak r q1 q2 q3]
  obtain ⟨c₃, t₃, e₃, ht₃, d20, dm, dk, dr, drm, do'⟩ :=
    rdC_exec (P := P) c₂ e₂.wb_right (x := x) (PWb := PWb)
      (by rw [q _ (by omega) (by omega) (by omega) (by omega), r20])
      (by rw [q _ (by omega) (by omega) (by omega) (by omega), r01])
      (by rw [q _ (by omega) (by omega) (by omega) (by omega), r510]) ⟨h3, h4⟩
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, d20, fun a => ?_,
    fun r q1 q2 q3 q4 q5 => ?_, by rw [dr, br, ar], by rw [drm, brm, arm], by rw [do', bo, ao]⟩
  · rw [dm a, b24, bm, am]
  · rw [dk r q1 q2, q r q2 q3 q4 q5]

/-- **The new prices from the FR answers.** -/
theorem rdP_exec (c : Config) (hc : WordsBounded W c) {b Ob PWb root H Mo : ℕ}
    (r14 : c.nreg 7614 = Ob) (r7600 : c.nreg 7600 = b) (r01 : c.nreg 9501 = PWb)
    (r39 : c.nreg 9339 = root) (r510 : c.nreg 9510 = 1) (r11 : c.nreg 7611 = H)
    (r10 : c.nreg 7610 = Mo) (hd : PWb + b ≤ Ob) (hA : Ob + b + b ≤ W) (hr : root < b)
    (hB : ∀ x < b, c.nmem (Ob + x) = 1 → c.nmem (PWb + root) + c.nmem (Ob + x + b) ≤ W) :
    ∃ c' t, Exec P W rdP c c' t ∧ t ≤ 16 * b + 5 ∧
      (∀ x < b, c'.nmem (PWb + x) =
        rdV (c.nmem (Ob + x)) (c.nmem (Ob + x + b)) (c.nmem (PWb + root)) H Mo) ∧
      (∀ a, ¬ (PWb ≤ a ∧ a < PWb + b) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9520 ∨ 9524 < r) → r ≠ 9530 → r ≠ 9531 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hPW : PWb + root ≤ W := by have := hc.1 9339; have := hc.1 9501; omega
  obtain ⟨c₁, t₁, e₁, ht₁, a30, a20, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.addN 9531 9501 9339, .loadN 9530 9531, .constN 9520 0]) c c₁ t₁ ∧
      t₁ = 3 ∧ c₁.nreg 9530 = c.nmem (PWb + root) ∧ c₁.nreg 9520 = 0 ∧
      (∀ r, r ≠ 9520 → r ≠ 9530 → r ≠ 9531 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r01, r39]); omega)
    refine ⟨rfl, ?_, ?_, fun r q1 q2 q3 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r01, r39])
    all_goals try rfl
    all_goals try (simp only [upd_apply]; split_ifs <;> omega)
  have q : ∀ r, (r < 9520 ∨ 9524 < r) → r ≠ 9530 → r ≠ 9531 → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => ak r (by omega) h2 h3
  let J : ℕ → Config → Prop := fun x c' =>
    (∀ y < x, c'.nmem (PWb + y) =
      rdV (c.nmem (Ob + y)) (c.nmem (Ob + y + b)) (c.nmem (PWb + root)) H Mo) ∧
    (∀ a, ¬ (PWb ≤ a ∧ a < PWb + x) → c'.nmem a = c.nmem a) ∧
    (∀ r, (r < 9520 ∨ 9524 < r) → c'.nreg r = c₁.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, hJ⟩ := NegSSSP.forLoop_exec (P := P) (a := 9520) (bR := 7600)
    (body := rdBody) J (K := 14) (n := b) c₁ e₁.wb_right a20
    (by rw [q _ (by omega) (by omega) (by omega), r7600])
    ⟨fun y hy => absurd hy (by omega), fun a _ => by rw [am], fun _ _ => rfl, ar, arm, ao⟩
    (fun x c' hx hw ha hb hJ => by
      obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
      have s : ∀ r, (r < 9520 ∨ 9524 < r) → r ≠ 9530 → r ≠ 9531 → c'.nreg r = c.nreg r :=
        fun r h1 h2 h3 => by rw [jn r h1, q r h1 h2 h3]
      have mF : c'.nmem (Ob + x) = c.nmem (Ob + x) := j2 _ (by omega)
      have mR : c'.nmem (Ob + x + b) = c.nmem (Ob + x + b) := j2 _ (by omega)
      obtain ⟨c'', t, ex, ht, h20, hm, hk, hr, hrm, ho⟩ :=
        rdBody_exec (P := P) c' hw (x := x) (b := b) (Ob := Ob) (PWb := PWb)
          (pr := c.nmem (PWb + root)) (H := H) (Mo := Mo) ha
          (by rw [s _ (by omega) (by omega) (by omega), r14])
          (by rw [s _ (by omega) (by omega) (by omega), r7600])
          (by rw [s _ (by omega) (by omega) (by omega), r01])
          (by rw [jn _ (by omega), a30])
          (by rw [s _ (by omega) (by omega) (by omega), r510])
          (by rw [s _ (by omega) (by omega) (by omega), r11])
          (by rw [s _ (by omega) (by omega) (by omega), r10])
          ⟨by omega, by rw [mR, mF]; exact hB x hx, by omega, by omega⟩
      have hb' : c''.nreg 7600 = b := by
        rw [hk _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hb
      refine ⟨c'', t, ex, ht, h20, hb', fun y hy => ?_, fun a ha' => ?_,
        fun r h1 => (hk r (by omega) (by omega) (by omega) (by omega) (by omega)).trans (jn r h1),
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hy with h | rfl
        · simp only [show PWb + y ≠ PWb + x by omega, ↓reduceIte]; exact j1 y h
        · simp only [↓reduceIte, mF, mR]
      · rw [hm]
        simp only [show a ≠ PWb + x by omega, ↓reduceIte]
        exact j2 a (by omega))
  obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
  refine ⟨c₂, _, .seq e₁ e₂, by omega, j1, j2, fun r h1 h2 h3 => by rw [jn r h1, q r h1 h2 h3],
    jr, jrm, jo⟩

theorem fwA_exec (c : Config) (hc : WordsBounded W c) {PWb IA IB : ℕ}
    (r01 : c.nreg 9501 = PWb) (r19 : c.nreg 9319 = IA) (r20 : c.nreg 9320 = IB)
    (hA : PWb + IA ≤ W ∧ PWb + IB ≤ W) :
    ∃ c' t, Exec P W fwA c c' t ∧ t = 4 ∧ c'.nreg 9506 = c.nmem (PWb + IA) ∧
      c'.nreg 9507 = c.nmem (PWb + IB) ∧
      (∀ r, r ≠ 9505 → r ≠ 9506 → r ≠ 9507 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h1, h2⟩ := hA
  unfold fwA
  exec_block
  all_goals try ((try config_simp); (try simp only [r01, r19, r20]); omega)
  refine ⟨rfl, ?_, ?_, fun r q1 q2 q3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r01, r19, r20])
  all_goals try rfl
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

/-- The value written by `fwP`. -/
def fwV (NG F2 PA PB NA NB : ℕ) : ℕ := if NG < 1 then F2 + PB - NB else F2 + NA - PA

/-- **`FW[i] := f3 + K`.** -/
theorem fwP_exec (c : Config) (hc : WordsBounded W c) {i FWb PWb IA IB NG F2 PA PB : ℕ}
    (r00 : c.nreg 9500 = i) (r76 : c.nreg 9376 = FWb) (r01 : c.nreg 9501 = PWb)
    (r19 : c.nreg 9319 = IA) (r20 : c.nreg 9320 = IB) (r33 : c.nreg 9333 = NG)
    (r510 : c.nreg 9510 = 1) (r37 : c.nreg 9337 = F2) (r12 : c.nreg 9312 = PA)
    (r13 : c.nreg 9313 = PB)
    (hA : PWb + IA ≤ W ∧ PWb + IB ≤ W ∧ FWb + i ≤ W ∧ F2 + PB ≤ W ∧ F2 + c.nmem (PWb + IA) ≤ W) :
    ∃ c' t, Exec P W fwP c c' t ∧ t ≤ 11 ∧
      (∀ a, c'.nmem a = if a = FWb + i then
        fwV NG F2 PA PB (c.nmem (PWb + IA)) (c.nmem (PWb + IB)) else c.nmem a) ∧
      (∀ r, (r < 9505 ∨ 9508 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hA
  obtain ⟨c₁, t₁, e₁, ht₁, a06, a07, ak, am, ar, arm, ao⟩ :=
    fwA_exec (P := P) c hc r01 r19 r20 ⟨h1, h2⟩
  have q : ∀ r, (r < 9505 ∨ 9508 < r) → c₁.nreg r = c.nreg r := fun r h =>
    ak r (by omega) (by omega) (by omega)
  have hw1 := e₁.wb_right
  obtain ⟨c₂, t₂, e₂, ht₂, b08, bk, bm, br, brm, bo⟩ : ∃ c₂ t₂,
      Exec P W (.ifLtN 9333 9510 (block [.addN 9508 9337 9313, .subN 9508 9508 9507])
        (block [.addN 9508 9337 9506, .subN 9508 9508 9312])) c₁ c₂ t₂ ∧ t₂ ≤ 4 ∧
      c₂.nreg 9508 = fwV NG F2 PA PB (c.nmem (PWb + IA)) (c.nmem (PWb + IB)) ∧
      (∀ r, r ≠ 9508 → c₂.nreg r = c₁.nreg r) ∧
      c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have s33 : c₁.nreg 9333 = NG := by rw [q _ (by omega), r33]
    have s510 : c₁.nreg 9510 = 1 := by rw [q _ (by omega), r510]
    have s37 : c₁.nreg 9337 = F2 := by rw [q _ (by omega), r37]
    have s12 : c₁.nreg 9312 = PA := by rw [q _ (by omega), r12]
    have s13 : c₁.nreg 9313 = PB := by rw [q _ (by omega), r13]
    by_cases hng : NG < 1
    · obtain ⟨c₂, t₂, e₂, ht₂, b08, bk, bm, br, brm, bo⟩ : ∃ c₂ t₂,
          Exec P W (block [.addN 9508 9337 9313, .subN 9508 9508 9507]) c₁ c₂ t₂ ∧ t₂ = 2 ∧
          c₂.nreg 9508 = F2 + PB - c.nmem (PWb + IB) ∧
          (∀ r, r ≠ 9508 → c₂.nreg r = c₁.nreg r) ∧
          c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
        exec_block
        all_goals try ((try config_simp); (try simp only [s37, s13]); omega)
        refine ⟨rfl, ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
        all_goals config_simp
        all_goals try (simp only [s37, s13, a07])
        all_goals try rfl
        all_goals try (simp only [upd_apply]; split_ifs <;> omega)
      refine ⟨c₂, _, .ifLtN_true (by rw [s33, s510]; exact hng) e₂, by omega, ?_, bk, bm, br,
        brm, bo⟩
      rw [b08]; unfold fwV; simp only [hng, ↓reduceIte]
    · obtain ⟨c₂, t₂, e₂, ht₂, b08, bk, bm, br, brm, bo⟩ : ∃ c₂ t₂,
          Exec P W (block [.addN 9508 9337 9506, .subN 9508 9508 9312]) c₁ c₂ t₂ ∧ t₂ = 2 ∧
          c₂.nreg 9508 = F2 + c.nmem (PWb + IA) - PA ∧
          (∀ r, r ≠ 9508 → c₂.nreg r = c₁.nreg r) ∧
          c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
        exec_block
        all_goals try ((try config_simp); (try simp only [s37, a06]); omega)
        refine ⟨rfl, ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
        all_goals config_simp
        all_goals try (simp only [s37, s12, a06])
        all_goals try rfl
        all_goals try (simp only [upd_apply]; split_ifs <;> omega)
      refine ⟨c₂, _, .ifLtN_false (by rw [s33, s510]; exact hng) e₂, by omega, ?_, bk, bm, br,
        brm, bo⟩
      rw [b08]; unfold fwV; simp only [hng, ↓reduceIte]
  have hw2 := e₂.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, dm, dk, dr, drm, do'⟩ : ∃ c₃ t₃,
      Exec P W (block [.addN 9505 9376 9500, .storeN 9505 9508]) c₂ c₃ t₃ ∧ t₃ = 2 ∧
      (∀ a, c₃.nmem a = if a = FWb + i then c₂.nreg 9508 else c₂.nmem a) ∧
      (∀ r, r ≠ 9505 → c₃.nreg r = c₂.nreg r) ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have s00 : c₂.nreg 9500 = i := by rw [bk _ (by omega), q _ (by omega), r00]
    have s76 : c₂.nreg 9376 = FWb := by rw [bk _ (by omega), q _ (by omega), r76]
    exec_block
    all_goals try ((try config_simp); (try simp only [s00, s76]); omega)
    refine ⟨rfl, fun a => ?_, fun r h => ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [s00, s76])
    all_goals try rfl
    all_goals try (simp only [upd_apply]; split_ifs <;> omega)
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, fun a => ?_, fun r h => ?_, by rw [dr, br, ar],
    by rw [drm, brm, arm], by rw [do', bo, ao]⟩
  · rw [dm a, b08, bm, am]
  · rw [dk r (by omega), bk r (by omega), q r h]

end BKMNW

end PlanarFlow
