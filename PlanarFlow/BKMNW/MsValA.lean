module

public import PlanarFlow.BKMNW.MsCutB
public import PlanarFlow.BKMNW.LinLoops

/-!
# Loops of the MSSP encoder, part A: a sum loop and the value blocks of the map stage

* **`smLoop`** (`r7342 := ∑_{j < r7340} M[r7341 + j]`, registers `7340 … 7345`), `smLoop_exec`;
* value blocks for the generic write loop `wrLoop` (`MsCutB.lean`), with their `ValSpec`:
  - **`vG`**: the boundary darts `G[i] := nE + 2 nT + RK[TR[i]]` (parameters `r7320 = TRb`,
    `r7321 = RKb`, `r7322 = nE + 2 nT`);
  - **`vCL`**: the lengths of the copies `CL[RE[i]] := LEN[i]` for the darts off the path
    (`r7323 = LFb`, `r7324 = REb`, `r7325 = Lb`).
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

/-! ### The sum loop -/

/-- One step of the sum. -/
def smBody : Stmt :=
  block [.addN 7345 7341 7343, .loadN 7345 7345, .addN 7342 7342 7345, .addN 7343 7343 7344]

/-- **The sum loop** `r7342 := ∑_{j < r7340} M[r7341 + j]`. -/
def smLoop : Stmt :=
  .seq (block [.constN 7342 0, .constN 7343 0, .constN 7344 1]) (.whileLtN 7343 7340 smBody)

theorem smLoop_exec (c : Config) (hc : WordsBounded W c) {len base : ℕ}
    (r40 : c.nreg 7340 = len) (r41 : c.nreg 7341 = base) (hw : base + len ≤ W)
    (hs : ∑ j ∈ range len, c.nmem (base + j) ≤ W) (hl : len + 1 ≤ W) :
    ∃ c' t, Exec P W smLoop c c' t ∧ t ≤ 6 * len + 5 ∧
      c'.nreg 7342 = ∑ j ∈ range len, c.nmem (base + j) ∧
      (∀ r, (r < 7342 ∨ 7345 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smLoop
  obtain ⟨c₁, k₁, e₁, hk₁, g2, g3, g4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 7342 0, .constN 7343 0, .constN 7344 1]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 7342 = 0 ∧ c₁.nreg 7343 = 0 ∧ c₁.nreg 7344 = 1 ∧
      (∀ x, (x < 7342 ∨ 7344 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun i d =>
    d.nreg 7344 = 1 ∧ d.nreg 7342 = ∑ j ∈ range i, c.nmem (base + j) ∧
    (∀ r, (r < 7342 ∨ 7345 < r) → d.nreg r = c.nreg r) ∧ d.nmem = c.nmem ∧
    d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h43, j1, j2, j3, j4, j5, j6, j7⟩ := lnRange (P := P)
    (a := 7343) (b := 7340) (body := smBody) J (B := 4) c₁ e₁.wb_right g3
    (by rw [gn₁ _ (by omega), r40]) (Nat.zero_le len)
    ⟨g4, by simp [g2], fun r hr => gn₁ r (by omega), gm₁, gr₁, grm₁, go₁⟩
    (fun i d hlo hhi hwd h43 h40 ⟨j1, j2, j3, j4, j5, j6, j7⟩ => by
      have d41 : d.nreg 7341 = base := by rw [j3 _ (by omega), r41]
      have hsi : ∑ j ∈ range (i + 1), c.nmem (base + j) ≤ W :=
        (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))).trans hs
      rw [Finset.sum_range_succ] at hsi
      unfold smBody
      exec_block
      all_goals try ((try config_simp); (try simp only [d41, h43, j1, j2, j4]); omega)
      refine ⟨by omega, ?_, ?_, ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩⟩
      all_goals config_simp
      · simp only [h43, j1]
      · simp only [upd_other _ _ _ (show (7340 : ℕ) ≠ 7343 by omega),
          upd_other _ _ _ (show (7340 : ℕ) ≠ 7342 by omega),
          upd_other _ _ _ (show (7340 : ℕ) ≠ 7345 by omega), h40]
      · simp only [upd_other _ _ _ (show (7344 : ℕ) ≠ 7343 by omega),
          upd_other _ _ _ (show (7344 : ℕ) ≠ 7342 by omega),
          upd_other _ _ _ (show (7344 : ℕ) ≠ 7345 by omega), j1]
      · simp only [d41, h43, j2, j4, Finset.sum_range_succ]
        try (simp only [upd_apply]; split_ifs <;> first | omega | rfl)
      · simp only [upd_apply]; split_ifs <;> first | omega | exact j3 r hr
      · exact j4
      · exact j5
      · exact j6
      · exact j7)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by
    have : k₂ ≤ (4 + 2) * len + 2 := by simpa using hk₂
    omega, by rw [j2], j3, j4, j5, j6, j7⟩

/-! ### The boundary darts -/

/-- **The value block of the boundary darts**: `G[i] := nE + 2 nT + RK[TR[i]]`. -/
def vG : Stmt :=
  block [.constN 8206 1, .copyN 8207 8205, .addN 8211 7320 8205, .loadN 8211 8211,
    .addN 8211 7321 8211, .loadN 8211 8211, .addN 8208 7322 8211, .constN 8209 0]

theorem vG_spec (c : Config) {k TRb RKb nE2 RVo RTo N : ℕ} (r20 : c.nreg 7320 = TRb)
    (r21 : c.nreg 7321 = RKb) (r22 : c.nreg 7322 = nE2)
    (hTR : ∀ i < k, (TRb + i < RVo ∨ RVo + N ≤ TRb + i) ∧ (TRb + i < RTo ∨ RTo + N ≤ TRb + i))
    (hRK : ∀ i < k, (RKb + c.nmem (TRb + i) < RVo ∨ RVo + N ≤ RKb + c.nmem (TRb + i)) ∧
      (RKb + c.nmem (TRb + i) < RTo ∨ RTo + N ≤ RKb + c.nmem (TRb + i)))
    (hw : ∀ i < k, TRb + i ≤ W ∧ RKb + c.nmem (TRb + i) ≤ W ∧
      nE2 + c.nmem (RKb + c.nmem (TRb + i)) ≤ W) (hk : k ≤ W) (h1 : 1 ≤ W) :
    ValSpec (P := P) (W := W) vG 8 c k RVo RTo N (fun _ => true) (fun i => i)
      (fun i => nE2 + c.nmem (RKb + c.nmem (TRb + i))) (fun _ => 0) := by
  intro d i hd hi h05 h03 h04 hR hM
  have d20 : d.nreg 7320 = TRb := by rw [hR _ (by omega), r20]
  have d21 : d.nreg 7321 = RKb := by rw [hR _ (by omega), r21]
  have d22 : d.nreg 7322 = nE2 := by rw [hR _ (by omega), r22]
  have m1 : d.nmem (TRb + i) = c.nmem (TRb + i) := hM _ (hTR i hi).1 (hTR i hi).2
  have m2 : d.nmem (RKb + c.nmem (TRb + i)) = c.nmem (RKb + c.nmem (TRb + i)) :=
    hM _ (hRK i hi).1 (hRK i hi).2
  obtain ⟨w1, w2, w3⟩ := hw i hi
  unfold vG
  exec_block
  all_goals try ((try config_simp); (try simp only [d20, d21, d22, h05, m1, m2]); omega)
  refine ⟨by omega, ?_, fun _ => ⟨?_, ?_, ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [d20, d21, d22, h05, m1, m2])
  all_goals (try (simp only [upd_apply]; split_ifs <;> first | omega | rfl))
  all_goals (try simp)

/-! ### The lengths of the copies -/

/-- **The value block of the copy lengths**: selected when `LF[i] = 0`, `CL[RE[i]] := LEN[i]`. -/
def vCL : Stmt :=
  block [.addN 8211 7323 8205, .loadN 8211 8211, .subN 8206 8203 8211, .addN 8211 7324 8205,
    .loadN 8207 8211, .addN 8211 7325 8205, .loadN 8208 8211, .constN 8209 0]

theorem vCL_spec (c : Config) {m LFb REb Lb RVo RTo N : ℕ} (r23 : c.nreg 7323 = LFb)
    (r24 : c.nreg 7324 = REb) (r25 : c.nreg 7325 = Lb)
    (hA : ∀ i < m, ∀ X, X = LFb ∨ X = REb ∨ X = Lb →
      (X + i < RVo ∨ RVo + N ≤ X + i) ∧ (X + i < RTo ∨ RTo + N ≤ X + i))
    (hlf : ∀ i < m, c.nmem (LFb + i) ≤ 1)
    (hw : LFb + m ≤ W ∧ REb + m ≤ W ∧ Lb + m ≤ W) (h1 : 1 ≤ W) :
    ValSpec (P := P) (W := W) vCL 8 c m RVo RTo N (fun i => decide (c.nmem (LFb + i) = 0))
      (fun i => c.nmem (REb + i)) (fun i => c.nmem (Lb + i)) (fun _ => 0) := by
  intro d i hd hi h05 h03 h04 hR hM
  have d23 : d.nreg 7323 = LFb := by rw [hR _ (by omega), r23]
  have d24 : d.nreg 7324 = REb := by rw [hR _ (by omega), r24]
  have d25 : d.nreg 7325 = Lb := by rw [hR _ (by omega), r25]
  have m1 : d.nmem (LFb + i) = c.nmem (LFb + i) := hM _ (hA i hi _ (Or.inl rfl)).1
    (hA i hi _ (Or.inl rfl)).2
  have m2 : d.nmem (REb + i) = c.nmem (REb + i) := hM _ (hA i hi _ (Or.inr (Or.inl rfl))).1
    (hA i hi _ (Or.inr (Or.inl rfl))).2
  have m3 : d.nmem (Lb + i) = c.nmem (Lb + i) := hM _ (hA i hi _ (Or.inr (Or.inr rfl))).1
    (hA i hi _ (Or.inr (Or.inr rfl))).2
  have hl := hlf i hi
  obtain ⟨w1, w2, w3⟩ := hw
  unfold vCL
  exec_block
  all_goals try ((try config_simp); (try simp only [d23, d24, d25, h05, h03, m1, m2, m3]); omega)
  refine ⟨by omega, ?_, fun _ => ⟨?_, ?_, ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [d23, h05, h03, m1]
    by_cases h0 : c.nmem (LFb + i) = 0 <;> simp [h0] <;> omega
  all_goals first
    | (simp only [d23, d24, d25, h05, m1, m2, m3]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

end MsEnc

end BKMNW

end PlanarFlow
