module

public import PlanarFlow.BKMNW.MsValA

/-!
# Loops of the MSSP encoder, part B: the value blocks of the weight, tree and trip stages

Value blocks for `wrLoop` with their `ValSpec` (`Off RVo RTo N a`: the address `a` is off the two
output arrays):

* **`vLN`**: `IS[j] := [j < nP]`, `LN[j] := [j < nP] (CL[j] N₁ + WM[j] N₃ + N₂ + j)` (the isolating
  lengths of the piece; `r7326 = nP`, `r7327 = CLb`, `r7328 = N₁`, `r7329 = WMb`, `r7330 = N₃`,
  `r7331 = N₂`);
* **`vLD`**: Dijkstra's lengths `LD[j] := IS[j] = 1 ? LN[j] : (j = G₀ ? H : 2H)` (`r7332 = ISb`,
  `r7333 = LNb`, `r7334 = G₀`, `r7335 = H`);
* **`vXT`**: the targets `XN[r] := NH[nE + RK[TR[CS[r]]]]`, `XR[r] := [DI[XN[r]] < H]`
  (`r7336 = CSb`, `r7337 = TRb`, `r7338 = RKb`, `r7339 = nE`, `r7346 = NHb`, `r7347 = DIb`,
  `r7348 = H`);
* **`vMK`**: the flags `MK[CS[r]] := 1` (`r7336 = CSb`);
* **`vSL`**: the slots `SL[i] := CN[FL[Q[i]]]` (`r8270 = Qb`, `r8271 = FLb`, `r8272 = CNb`);
* **`vTW`**: the trip weights `WT[j] := [IS[j] = 1 ∧ D1[NT[j]] < H] ? LN[j] : L`,
  `PH[j] := IS[j] · LN[j]` (`r8273 = ISb`, `r8274 = LNb`, `r8275 = NTb`, `r8276 = D1b`,
  `r8277 = H`, `r8278 = L`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The address `a` is off the two output arrays of a write loop. -/
def Off (RVo RTo N a : ℕ) : Prop := (a < RVo ∨ RVo + N ≤ a) ∧ (a < RTo ∨ RTo + N ≤ a)

/-! ### The isolating lengths of the piece -/

def vLN : Stmt :=
  block [.subN 8211 7326 8205, .subN 8211 8203 8211, .subN 8208 8203 8211, .addN 8212 7327 8205,
    .loadN 8212 8212, .mulN 8212 8212 7328, .addN 8213 7329 8205, .loadN 8213 8213,
    .mulN 8213 8213 7330, .addN 8212 8212 8213, .addN 8212 8212 7331, .addN 8212 8212 8205,
    .mulN 8209 8212 8208, .constN 8206 1, .copyN 8207 8205]

theorem vLN_spec (c : Config) {nD nP CLb N1 WMb N3 N2 RVo RTo N : ℕ} (r26 : c.nreg 7326 = nP)
    (r27 : c.nreg 7327 = CLb) (r28 : c.nreg 7328 = N1) (r29 : c.nreg 7329 = WMb)
    (r30 : c.nreg 7330 = N3) (r31 : c.nreg 7331 = N2)
    (hA : ∀ j < nD, Off RVo RTo N (CLb + j) ∧ Off RVo RTo N (WMb + j))
    (hw : ∀ j < nD, CLb + j ≤ W ∧ WMb + j ≤ W ∧
      c.nmem (CLb + j) * N1 + c.nmem (WMb + j) * N3 + N2 + j ≤ W) (h1 : 1 ≤ W) :
    ValSpec (P := P) (W := W) vLN 15 c nD RVo RTo N (fun _ => true) (fun j => j)
      (fun j => if j < nP then 1 else 0)
      (fun j => if j < nP then c.nmem (CLb + j) * N1 + c.nmem (WMb + j) * N3 + N2 + j else 0) := by
  intro d i hd hi h05 h03 h04 hR hM
  have d26 : d.nreg 7326 = nP := by rw [hR _ (by omega), r26]
  have d27 : d.nreg 7327 = CLb := by rw [hR _ (by omega), r27]
  have d28 : d.nreg 7328 = N1 := by rw [hR _ (by omega), r28]
  have d29 : d.nreg 7329 = WMb := by rw [hR _ (by omega), r29]
  have d30 : d.nreg 7330 = N3 := by rw [hR _ (by omega), r30]
  have d31 : d.nreg 7331 = N2 := by rw [hR _ (by omega), r31]
  have m1 : d.nmem (CLb + i) = c.nmem (CLb + i) := hM _ (hA i hi).1.1 (hA i hi).1.2
  have m2 : d.nmem (WMb + i) = c.nmem (WMb + i) := hM _ (hA i hi).2.1 (hA i hi).2.2
  obtain ⟨w1, w2, w3⟩ := hw i hi
  have p1 : c.nmem (CLb + i) * N1 ≤ W := by
    have := Nat.zero_le (c.nmem (WMb + i) * N3); omega
  have p2 : c.nmem (WMb + i) * N3 ≤ W := by
    have := Nat.zero_le (c.nmem (CLb + i) * N1); omega
  have p3 : (c.nmem (CLb + i) * N1 + c.nmem (WMb + i) * N3 + N2 + i) * (1 - (1 - (nP - i))) ≤ W :=
    by
    rcases Nat.lt_or_ge i nP with h | h
    · rw [show 1 - (1 - (nP - i)) = 1 by omega, Nat.mul_one]; exact w3
    · rw [show 1 - (1 - (nP - i)) = 0 by omega, Nat.mul_zero]; omega
  have hfl : 1 - (1 - (nP - i)) = if i < nP then 1 else 0 := by split_ifs <;> omega
  unfold vLN
  exec_block
  all_goals try ((try config_simp); (try simp only [d26, d27, d28, d29, d30, d31, h05, h03, m1, m2]); omega)
  refine ⟨by omega, ?_, fun _ => ⟨?_, ?_, ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [d26, d27, d28, d29, d30, d31, h05, h03, m1, m2])
  all_goals first
    | rfl
    | (simp; done)
    | exact hfl
    | (rw [hfl]; split_ifs <;> simp <;> done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-! ### Dijkstra's lengths -/

def vLD : Stmt :=
  block [.addN 8211 7332 8205, .loadN 8211 8211, .addN 8212 7333 8205, .loadN 8212 8212,
    .mulN 8212 8212 8211, .subN 8213 8205 7334, .subN 8214 7334 8205, .addN 8213 8213 8214,
    .subN 8213 8203 8213, .mulN 8213 8213 7335, .addN 8214 7335 7335, .subN 8214 8214 8213,
    .subN 8215 8203 8211, .mulN 8214 8214 8215, .addN 8208 8212 8214, .constN 8206 1,
    .copyN 8207 8205, .constN 8209 0]

theorem vLD_spec (c : Config) {nD ISb LNb G0 H RVo RTo N : ℕ} (r32 : c.nreg 7332 = ISb)
    (r33 : c.nreg 7333 = LNb) (r34 : c.nreg 7334 = G0) (r35 : c.nreg 7335 = H)
    (hA : ∀ j < nD, Off RVo RTo N (ISb + j) ∧ Off RVo RTo N (LNb + j))
    (his : ∀ j < nD, c.nmem (ISb + j) ≤ 1)
    (hw : ∀ j < nD, ISb + j ≤ W ∧ LNb + j ≤ W ∧ c.nmem (LNb + j) ≤ W) (hH : 2 * H ≤ W)
    (hG : G0 ≤ W) (hn : nD ≤ W) (h1 : 1 ≤ W) :
    ValSpec (P := P) (W := W) vLD 18 c nD RVo RTo N (fun _ => true) (fun j => j)
      (fun j => if c.nmem (ISb + j) = 1 then c.nmem (LNb + j) else if j = G0 then H else 2 * H)
      (fun _ => 0) := by
  intro d i hd hi h05 h03 h04 hR hM
  have d32 : d.nreg 7332 = ISb := by rw [hR _ (by omega), r32]
  have d33 : d.nreg 7333 = LNb := by rw [hR _ (by omega), r33]
  have d34 : d.nreg 7334 = G0 := by rw [hR _ (by omega), r34]
  have d35 : d.nreg 7335 = H := by rw [hR _ (by omega), r35]
  have m1 : d.nmem (ISb + i) = c.nmem (ISb + i) := hM _ (hA i hi).1.1 (hA i hi).1.2
  have m2 : d.nmem (LNb + i) = c.nmem (LNb + i) := hM _ (hA i hi).2.1 (hA i hi).2.2
  obtain ⟨w1, w2, w3⟩ := hw i hi
  have hf := his i hi
  set f := c.nmem (ISb + i) with hfd
  set ln := c.nmem (LNb + i) with hlnd
  have e1 : ln * f ≤ W := by
    rcases (show f = 0 ∨ f = 1 by omega) with h | h <;> rw [h] <;> simp <;> omega
  have e2 : (1 - (i - G0 + (G0 - i))) * H ≤ W := by
    by_cases h : i = G0
    · rw [show 1 - (i - G0 + (G0 - i)) = 1 by omega]; omega
    · rw [show 1 - (i - G0 + (G0 - i)) = 0 by omega]; omega
  have e3 : (H + H - (1 - (i - G0 + (G0 - i))) * H) * (1 - f) ≤ W := by
    rcases (show f = 0 ∨ f = 1 by omega) with h | h <;> rw [h] <;> simp <;> omega
  have e4 : ln * f + (H + H - (1 - (i - G0 + (G0 - i))) * H) * (1 - f) ≤ W := by
    rcases (show f = 0 ∨ f = 1 by omega) with h | h <;> rw [h] <;> simp <;> omega
  have hval : ln * f + (H + H - (1 - (i - G0 + (G0 - i))) * H) * (1 - f) =
      if f = 1 then ln else if i = G0 then H else 2 * H := by
    have he : 1 - (i - G0 + (G0 - i)) = if i = G0 then 1 else 0 := by split_ifs <;> omega
    rw [he]
    rcases (show f = 0 ∨ f = 1 by omega) with h | h <;> rw [h] <;> by_cases h' : i = G0
    · simp only [h', ↓reduceIte, one_mul, Nat.sub_zero, Nat.mul_one, Nat.mul_zero, Nat.zero_add,
        zero_ne_one]
      omega
    · simp only [h', ↓reduceIte, zero_mul, Nat.sub_zero, Nat.mul_one, Nat.mul_zero, Nat.zero_add,
        zero_ne_one]
      omega
    · simp [h']
    · simp [h']
  unfold vLD
  exec_block
  all_goals try ((try config_simp); (try simp only [d32, d33, d34, d35, h05, h03, m1, m2]); omega)
  refine ⟨by omega, ?_, fun _ => ⟨?_, ?_, ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [d32, d33, d34, d35, h05, h03, m1, m2])
  all_goals first
    | rfl
    | (simp; done)
    | exact hval
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-! ### The targets -/

def vXT : Stmt :=
  block [.addN 8211 7336 8205, .loadN 8211 8211, .addN 8211 7337 8211, .loadN 8211 8211,
    .addN 8211 7338 8211, .loadN 8211 8211, .addN 8211 7339 8211, .addN 8211 7346 8211,
    .loadN 8208 8211, .addN 8212 7347 8208, .loadN 8212 8212, .subN 8212 7348 8212,
    .subN 8212 8203 8212, .subN 8209 8203 8212, .constN 8206 1, .copyN 8207 8205]

/-- The node of the head of the pendant dart of the corner `r` (`NH[nE + RK[TR[CS[r]]]]`). -/
def xtN (mem : ℕ → ℕ) (CSb TRb RKb nE NHb r : ℕ) : ℕ :=
  mem (NHb + (nE + mem (RKb + mem (TRb + mem (CSb + r)))))

theorem vXT_spec (c : Config) {t CSb TRb RKb nE NHb DIb H RVo RTo N : ℕ}
    (r36 : c.nreg 7336 = CSb) (r37 : c.nreg 7337 = TRb) (r38 : c.nreg 7338 = RKb)
    (r39 : c.nreg 7339 = nE) (r46 : c.nreg 7346 = NHb) (r47 : c.nreg 7347 = DIb)
    (r48 : c.nreg 7348 = H)
    (hA : ∀ r < t, Off RVo RTo N (CSb + r) ∧
      Off RVo RTo N (TRb + c.nmem (CSb + r)) ∧
      Off RVo RTo N (RKb + c.nmem (TRb + c.nmem (CSb + r))) ∧
      Off RVo RTo N (NHb + (nE + c.nmem (RKb + c.nmem (TRb + c.nmem (CSb + r))))) ∧
      Off RVo RTo N (DIb + xtN c.nmem CSb TRb RKb nE NHb r))
    (hw : ∀ r < t, CSb + r ≤ W ∧ TRb + c.nmem (CSb + r) ≤ W ∧
      RKb + c.nmem (TRb + c.nmem (CSb + r)) ≤ W ∧
      NHb + (nE + c.nmem (RKb + c.nmem (TRb + c.nmem (CSb + r)))) ≤ W ∧
      DIb + xtN c.nmem CSb TRb RKb nE NHb r ≤ W) (h1 : 1 ≤ W) :
    ValSpec (P := P) (W := W) vXT 16 c t RVo RTo N (fun _ => true) (fun r => r)
      (fun r => xtN c.nmem CSb TRb RKb nE NHb r)
      (fun r => if c.nmem (DIb + xtN c.nmem CSb TRb RKb nE NHb r) < H then 1 else 0) := by
  intro d i hd hi h05 h03 h04 hR hM
  have d36 : d.nreg 7336 = CSb := by rw [hR _ (by omega), r36]
  have d37 : d.nreg 7337 = TRb := by rw [hR _ (by omega), r37]
  have d38 : d.nreg 7338 = RKb := by rw [hR _ (by omega), r38]
  have d39 : d.nreg 7339 = nE := by rw [hR _ (by omega), r39]
  have d46 : d.nreg 7346 = NHb := by rw [hR _ (by omega), r46]
  have d47 : d.nreg 7347 = DIb := by rw [hR _ (by omega), r47]
  have d48 : d.nreg 7348 = H := by rw [hR _ (by omega), r48]
  obtain ⟨a1, a2, a3, a4, a5⟩ := hA i hi
  have m1 := hM _ a1.1 a1.2
  have m2 := hM _ a2.1 a2.2
  have m3 := hM _ a3.1 a3.2
  have m4 := hM _ a4.1 a4.2
  have m5 := hM _ a5.1 a5.2
  unfold xtN at m5 ⊢
  obtain ⟨w1, w2, w3, w4, w5⟩ := hw i hi
  unfold xtN at w5
  have hxr : 1 - (1 - (H - c.nmem (DIb + c.nmem (NHb + (nE + c.nmem (RKb + c.nmem (TRb +
      c.nmem (CSb + i)))))))) = if c.nmem (DIb + c.nmem (NHb + (nE + c.nmem (RKb + c.nmem (TRb +
      c.nmem (CSb + i)))))) < H then 1 else 0 := by split_ifs <;> omega
  unfold vXT
  exec_block
  all_goals try ((try config_simp); (try simp only [d36, d37, d38, d39, d46, d47, d48, h05, h03, m1, m2, m3, m4, m5]); omega)
  refine ⟨by omega, ?_, fun _ => ⟨?_, ?_, ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [d36, d37, d38, d39, d46, d47, d48, h05, h03, m1, m2, m3, m4, m5])
  all_goals first
    | rfl
    | (simp; done)
    | exact hxr
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-! ### The flags -/

def vMK : Stmt :=
  block [.addN 8211 7336 8205, .loadN 8207 8211, .constN 8208 1, .constN 8209 1, .constN 8206 1]

theorem vMK_spec (c : Config) {t CSb RVo RTo N : ℕ} (r36 : c.nreg 7336 = CSb)
    (hA : ∀ r < t, Off RVo RTo N (CSb + r)) (hw : CSb + t ≤ W) (h1 : 1 ≤ W) :
    ValSpec (P := P) (W := W) vMK 5 c t RVo RTo N (fun _ => true) (fun r => c.nmem (CSb + r))
      (fun _ => 1) (fun _ => 1) := by
  intro d i hd hi h05 h03 h04 hR hM
  have d36 : d.nreg 7336 = CSb := by rw [hR _ (by omega), r36]
  have m1 := hM _ (hA i hi).1 (hA i hi).2
  unfold vMK
  exec_block
  all_goals try ((try config_simp); (try simp only [d36, h05, m1]); omega)
  refine ⟨by omega, ?_, fun _ => ⟨?_, ?_, ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [d36, h05, m1])
  all_goals first
    | rfl
    | (simp; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-! ### The slots of the query darts -/

def vSL : Stmt :=
  block [.addN 8211 8270 8205, .loadN 8211 8211, .addN 8211 8271 8211, .loadN 8211 8211,
    .addN 8211 8272 8211, .loadN 8208 8211, .copyN 8209 8208, .constN 8206 1, .copyN 8207 8205]

/-- The slot of the query `i`: `CN[FL[Q[i]]]`. -/
def slV (mem : ℕ → ℕ) (Qb FLb CNb i : ℕ) : ℕ := mem (CNb + mem (FLb + mem (Qb + i)))

theorem vSL_spec (c : Config) {q Qb FLb CNb RVo RTo N : ℕ} (r70 : c.nreg 8270 = Qb)
    (r71 : c.nreg 8271 = FLb) (r72 : c.nreg 8272 = CNb)
    (hA : ∀ i < q, Off RVo RTo N (Qb + i) ∧ Off RVo RTo N (FLb + c.nmem (Qb + i)) ∧
      Off RVo RTo N (CNb + c.nmem (FLb + c.nmem (Qb + i))))
    (hw : ∀ i < q, Qb + i ≤ W ∧ FLb + c.nmem (Qb + i) ≤ W ∧
      CNb + c.nmem (FLb + c.nmem (Qb + i)) ≤ W) (h1 : 1 ≤ W) :
    ValSpec (P := P) (W := W) vSL 9 c q RVo RTo N (fun _ => true) (fun i => i)
      (fun i => slV c.nmem Qb FLb CNb i) (fun i => slV c.nmem Qb FLb CNb i) := by
  intro d i hd hi h05 h03 h04 hR hM
  have d70 : d.nreg 8270 = Qb := by rw [hR _ (by omega), r70]
  have d71 : d.nreg 8271 = FLb := by rw [hR _ (by omega), r71]
  have d72 : d.nreg 8272 = CNb := by rw [hR _ (by omega), r72]
  obtain ⟨a1, a2, a3⟩ := hA i hi
  have m1 := hM _ a1.1 a1.2
  have m2 := hM _ a2.1 a2.2
  have m3 := hM _ a3.1 a3.2
  obtain ⟨w1, w2, w3⟩ := hw i hi
  unfold slV
  unfold vSL
  exec_block
  all_goals try ((try config_simp); (try simp only [d70, d71, d72, h05, m1, m2, m3]); omega)
  refine ⟨by omega, ?_, fun _ => ⟨?_, ?_, ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [d70, d71, d72, h05, m1, m2, m3])
  all_goals first
    | rfl
    | (simp; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-! ### The weights of the trip -/

def vTW : Stmt :=
  block [.addN 8211 8273 8205, .loadN 8211 8211, .addN 8212 8274 8205, .loadN 8212 8212,
    .mulN 8209 8212 8211, .addN 8213 8275 8205, .loadN 8213 8213, .addN 8213 8276 8213,
    .loadN 8213 8213, .subN 8213 8277 8213, .subN 8213 8203 8213, .subN 8213 8203 8213,
    .mulN 8213 8213 8211, .mulN 8214 8212 8213, .subN 8215 8203 8213, .mulN 8215 8215 8278,
    .addN 8208 8214 8215, .constN 8206 1, .copyN 8207 8205]

theorem vTW_spec (c : Config) {nD ISb LNb NTb D1b H L RVo RTo N : ℕ} (r73 : c.nreg 8273 = ISb)
    (r74 : c.nreg 8274 = LNb) (r75 : c.nreg 8275 = NTb) (r76 : c.nreg 8276 = D1b)
    (r77 : c.nreg 8277 = H) (r78 : c.nreg 8278 = L)
    (hA : ∀ j < nD, Off RVo RTo N (ISb + j) ∧ Off RVo RTo N (LNb + j) ∧
      Off RVo RTo N (NTb + j) ∧ Off RVo RTo N (D1b + c.nmem (NTb + j)))
    (his : ∀ j < nD, c.nmem (ISb + j) ≤ 1)
    (hw : ∀ j < nD, ISb + j ≤ W ∧ LNb + j ≤ W ∧ NTb + j ≤ W ∧ D1b + c.nmem (NTb + j) ≤ W ∧
      c.nmem (LNb + j) ≤ W) (hL : L ≤ W) (h1 : 1 ≤ W) :
    ValSpec (P := P) (W := W) vTW 19 c nD RVo RTo N (fun _ => true) (fun j => j)
      (fun j => if c.nmem (ISb + j) = 1 ∧ c.nmem (D1b + c.nmem (NTb + j)) < H then
        c.nmem (LNb + j) else L)
      (fun j => if c.nmem (ISb + j) = 1 then c.nmem (LNb + j) else 0) := by
  intro d i hd hi h05 h03 h04 hR hM
  have d73 : d.nreg 8273 = ISb := by rw [hR _ (by omega), r73]
  have d74 : d.nreg 8274 = LNb := by rw [hR _ (by omega), r74]
  have d75 : d.nreg 8275 = NTb := by rw [hR _ (by omega), r75]
  have d76 : d.nreg 8276 = D1b := by rw [hR _ (by omega), r76]
  have d77 : d.nreg 8277 = H := by rw [hR _ (by omega), r77]
  have d78 : d.nreg 8278 = L := by rw [hR _ (by omega), r78]
  obtain ⟨a1, a2, a3, a4⟩ := hA i hi
  have m1 := hM _ a1.1 a1.2
  have m2 := hM _ a2.1 a2.2
  have m3 := hM _ a3.1 a3.2
  have m4 := hM _ a4.1 a4.2
  obtain ⟨w1, w2, w3, w4, w5⟩ := hw i hi
  have hf := his i hi
  set f := c.nmem (ISb + i) with hfd
  set ln := c.nmem (LNb + i) with hlnd
  set dv := c.nmem (D1b + c.nmem (NTb + i)) with hdv
  have hr : 1 - (1 - (H - dv)) ≤ 1 := by omega
  have e1 : ln * f ≤ W := by
    rcases (show f = 0 ∨ f = 1 by omega) with h | h <;> rw [h] <;> simp <;> omega
  have e2 : (1 - (1 - (H - dv))) * f ≤ 1 := by
    rcases (show f = 0 ∨ f = 1 by omega) with h | h <;> rw [h] <;> simp <;> omega
  have e3 : ln * ((1 - (1 - (H - dv))) * f) ≤ W := by
    rcases (show (1 - (1 - (H - dv))) * f = 0 ∨ (1 - (1 - (H - dv))) * f = 1 by omega)
      with h | h <;> rw [h] <;> simp <;> omega
  have e4 : (1 - (1 - (1 - (H - dv))) * f) * L ≤ W := by
    rcases (show (1 - (1 - (H - dv))) * f = 0 ∨ (1 - (1 - (H - dv))) * f = 1 by omega)
      with h | h <;> rw [h] <;> simp <;> omega
  have e5 : ln * ((1 - (1 - (H - dv))) * f) + (1 - (1 - (1 - (H - dv))) * f) * L ≤ W := by
    rcases (show (1 - (1 - (H - dv))) * f = 0 ∨ (1 - (1 - (H - dv))) * f = 1 by omega)
      with h | h <;> rw [h] <;> simp <;> omega
  have hv1 : ln * ((1 - (1 - (H - dv))) * f) + (1 - (1 - (1 - (H - dv))) * f) * L =
      if f = 1 ∧ dv < H then ln else L := by
    rcases (show f = 0 ∨ f = 1 by omega) with h | h
    · simp [h]
    · by_cases hd : dv < H
      · simp [h, hd, show 1 - (1 - (H - dv)) = 1 by omega]
      · simp [h, hd, show 1 - (1 - (H - dv)) = 0 by omega]
  have hv2 : ln * f = if f = 1 then ln else 0 := by
    rcases (show f = 0 ∨ f = 1 by omega) with h | h <;> simp [h]
  unfold vTW
  exec_block
  all_goals try ((try config_simp); (try simp only [d73, d74, d75, d76, d77, d78, h05, h03, m1, m2, m3, m4]); omega)
  refine ⟨by omega, ?_, fun _ => ⟨?_, ?_, ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [d73, d74, d75, d76, d77, d78, h05, h03, m1, m2, m3, m4])
  all_goals first
    | rfl
    | (simp; done)
    | exact hv1
    | exact hv2
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

end MsEnc

end BKMNW

end PlanarFlow
