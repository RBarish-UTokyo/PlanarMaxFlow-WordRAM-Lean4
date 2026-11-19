module

public import PlanarFlow.BKMNW.MsCutF

/-!
# The cut map of the path on the machine, part G: the five write loops

**`cutWr`** `= wrLoop valE ; wrLoop val1 ; wrLoop val2 ; wrLoop val3 ; wrLoop val4` writes the
reverse (`RV'`, at `RVo`) and next (`RT'`, at `RTo`) words of the five kinds of darts of the cut
at their numbers. **`cutWr_exec`** (on arrays, from the registers `VRegs` and the arrays `LF`,
`TF`, `RE`, `RK`, `TA`, `TI`, `RV`, `RT` outside the outputs).
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

/-- **The five write loops.** -/
def cutWr : Stmt :=
  .seq (wrLoop valE) (.seq (wrLoop val1) (.seq (wrLoop val2) (.seq (wrLoop val3) (wrLoop val4))))

/-- The arrays of the write loops, read at the start `c`. -/
structure WrArr (c : Config) (LFb TFb REb RKb TAb TIb RVb RTb nE nT m W : ℕ)
    (lf tf re rk ta ti rv rt : ℕ → ℕ) : Prop where
  lf : ∀ i < m, c.nmem (LFb + i) = lf i ∧ lf i ≤ 1
  tf : ∀ i < m, c.nmem (TFb + i) = tf i ∧ tf i ≤ 1
  re : ∀ i < m, c.nmem (REb + i) = re i ∧ re i ≤ m
  rk : ∀ i < m, c.nmem (RKb + i) = rk i ∧ rk i ≤ m
  ta : ∀ i < m, c.nmem (TAb + i) = ta i ∧ ta i < m
  ti : ∀ i < m, c.nmem (TIb + i) = ti i ∧ ti i < m
  rv : ∀ i < m, c.nmem (RVb + i) = rv i ∧ rv i < m
  rt : ∀ i < m, c.nmem (RTb + i) = rt i ∧ rt i < m
  wLF : LFb + m ≤ W
  wTF : TFb + m ≤ W
  wRE : REb + m ≤ W
  wRK : RKb + m ≤ W
  wTA : TAb + m ≤ W
  wTI : TIb + m ≤ W
  wRV : RVb + m ≤ W
  wRT : RTb + m ≤ W
  wN : nE + 3 * nT + m ≤ W

/-- The input arrays lie outside the two output blocks. -/
def WrOut (LFb TFb REb RKb TAb TIb RVb RTb m RVo RTo N : ℕ) : Prop :=
  ∀ b ∈ [LFb, TFb, REb, RKb, TAb, TIb, RVb, RTb],
    (b + m ≤ RVo ∨ RVo + N ≤ b) ∧ (b + m ≤ RTo ∨ RTo + N ≤ b)

lemma wrOut_of {LFb TFb REb RKb TAb TIb RVb RTb m RVo RTo N : ℕ}
    (h : WrOut LFb TFb REb RKb TAb TIb RVb RTb m RVo RTo N) :
    ((LFb + m ≤ RVo ∨ RVo + N ≤ LFb) ∧ (LFb + m ≤ RTo ∨ RTo + N ≤ LFb)) ∧
    ((TFb + m ≤ RVo ∨ RVo + N ≤ TFb) ∧ (TFb + m ≤ RTo ∨ RTo + N ≤ TFb)) ∧
    ((REb + m ≤ RVo ∨ RVo + N ≤ REb) ∧ (REb + m ≤ RTo ∨ RTo + N ≤ REb)) ∧
    ((RKb + m ≤ RVo ∨ RVo + N ≤ RKb) ∧ (RKb + m ≤ RTo ∨ RTo + N ≤ RKb)) ∧
    ((TAb + m ≤ RVo ∨ RVo + N ≤ TAb) ∧ (TAb + m ≤ RTo ∨ RTo + N ≤ TAb)) ∧
    ((TIb + m ≤ RVo ∨ RVo + N ≤ TIb) ∧ (TIb + m ≤ RTo ∨ RTo + N ≤ TIb)) ∧
    ((RVb + m ≤ RVo ∨ RVo + N ≤ RVb) ∧ (RVb + m ≤ RTo ∨ RTo + N ≤ RVb)) ∧
    ((RTb + m ≤ RVo ∨ RVo + N ≤ RTb) ∧ (RTb + m ≤ RTo ∨ RTo + N ≤ RTb)) :=
  ⟨h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp),
    h _ (by simp), h _ (by simp)⟩

lemma wr_tr1 {c d : Config} {b m RVo RTo N : ℕ}
    (hb : (b + m ≤ RVo ∨ RVo + N ≤ b) ∧ (b + m ≤ RTo ∨ RTo + N ≤ b))
    (hm : ∀ a, (a < RVo ∨ RVo + N ≤ a) → (a < RTo ∨ RTo + N ≤ a) → d.nmem a = c.nmem a) :
    ∀ i < m, d.nmem (b + i) = c.nmem (b + i) := fun i hi =>
  hm _ (by rcases hb.1 with h | h <;> omega) (by rcases hb.2 with h | h <;> omega)

/-- The arrays are read the same from a configuration agreeing off the outputs. -/
lemma WrArr.transfer {c d : Config} {LFb TFb REb RKb TAb TIb RVb RTb nE nT m W : ℕ}
    {lf tf re rk ta ti rv rt : ℕ → ℕ} {RVo RTo N : ℕ}
    (h : WrArr c LFb TFb REb RKb TAb TIb RVb RTb nE nT m W lf tf re rk ta ti rv rt)
    (hO : WrOut LFb TFb REb RKb TAb TIb RVb RTb m RVo RTo N)
    (hm : ∀ a, (a < RVo ∨ RVo + N ≤ a) → (a < RTo ∨ RTo + N ≤ a) → d.nmem a = c.nmem a) :
    WrArr d LFb TFb REb RKb TAb TIb RVb RTb nE nT m W lf tf re rk ta ti rv rt := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := wrOut_of hO
  exact ⟨fun i hi => by rw [wr_tr1 o1 hm i hi]; exact h.lf i hi,
    fun i hi => by rw [wr_tr1 o2 hm i hi]; exact h.tf i hi,
    fun i hi => by rw [wr_tr1 o3 hm i hi]; exact h.re i hi,
    fun i hi => by rw [wr_tr1 o4 hm i hi]; exact h.rk i hi,
    fun i hi => by rw [wr_tr1 o5 hm i hi]; exact h.ta i hi,
    fun i hi => by rw [wr_tr1 o6 hm i hi]; exact h.ti i hi,
    fun i hi => by rw [wr_tr1 o7 hm i hi]; exact h.rv i hi,
    fun i hi => by rw [wr_tr1 o8 hm i hi]; exact h.rt i hi,
    h.wLF, h.wTF, h.wRE, h.wRK, h.wTA, h.wTI, h.wRV, h.wRT, h.wN⟩

lemma WrArr.vhyp {c : Config} {LFb TFb REb RKb TAb TIb RVb RTb nE nT m W : ℕ}
    {lf tf re rk ta ti rv rt : ℕ → ℕ}
    (h : WrArr c LFb TFb REb RKb TAb TIb RVb RTb nE nT m W lf tf re rk ta ti rv rt) {i : ℕ}
    (hi : i < m) : VHyp c i LFb TFb REb RKb TAb TIb RVb RTb nE nT m W :=
  ⟨hi, by rw [(h.lf i hi).1]; exact (h.lf i hi).2, by rw [(h.rv i hi).1]; exact (h.rv i hi).2,
    by rw [(h.rt i hi).1]; exact (h.rt i hi).2, by rw [(h.ta i hi).1]; exact (h.ta i hi).2,
    by rw [(h.ti i hi).1]; exact (h.ti i hi).2, fun j hj => by rw [(h.rk j hj).1]; exact (h.rk j hj).2,
    fun j hj => by rw [(h.re j hj).1]; exact (h.re j hj).2, h.wLF, h.wTF, h.wRE, h.wRK, h.wTA,
    h.wTI, h.wRV, h.wRT, h.wN⟩

/-! ### The specifications of the value blocks -/

section Specs

variable {c : Config} {LFb TFb REb RKb TAb TIb RVb RTb nE nT m RVo RTo N : ℕ}
  {lf tf re rk ta ti rv rt : ℕ → ℕ}

theorem valE_spec (hR : VRegs c LFb TFb REb RKb TAb TIb RVb RTb nE nT)
    (hA : WrArr c LFb TFb REb RKb TAb TIb RVb RTb nE nT m W lf tf re rk ta ti rv rt)
    (hO : WrOut LFb TFb REb RKb TAb TIb RVb RTb m RVo RTo N) :
    ValSpec (W := W) (P := P) valE 17 c m RVo RTo N (fun i => lf i == 0) re
      (fun i => re (rv i)) (fun i => if 0 < tf i then nE + nT + rk (ta i) else re (rt i)) := by
  intro d i hd hi h05 h03 h04 hreg hmem
  have hA' := hA.transfer hO hmem
  have hR' := hR.of fun r h1 h2 => hreg r (by omega)
  obtain ⟨d', k, ex, hk, v6, v7, v8, v9, vR, vm, vr, vrm, vo⟩ :=
    valE_exec (P := P) d hd hR' h05 h03 h04 (hA'.vhyp hi)
  obtain ⟨l1, l2⟩ := hA'.lf i hi
  refine ⟨d', k, ex, hk, ?_, fun _ => ⟨?_, ?_, ?_⟩, vR, vm, vr, vrm, vo⟩
  · rw [v6, l1]; by_cases h0 : lf i = 0 <;> simp [h0]; omega
  · rw [v7, (hA'.re i hi).1]
  · rw [v8, (hA'.rv i hi).1, (hA'.re _ (hA'.rv i hi).2).1]
  · beta_reduce
    rw [v9, (hA'.tf i hi).1]
    split_ifs
    · rw [(hA'.ta i hi).1, (hA'.rk _ (hA'.ta i hi).2).1]
    · rw [(hA'.rt i hi).1, (hA'.re _ (hA'.rt i hi).2).1]

theorem val1_spec (hR : VRegs c LFb TFb REb RKb TAb TIb RVb RTb nE nT)
    (hA : WrArr c LFb TFb REb RKb TAb TIb RVb RTb nE nT m W lf tf re rk ta ti rv rt)
    (hO : WrOut LFb TFb REb RKb TAb TIb RVb RTb m RVo RTo N) :
    ValSpec (W := W) (P := P) val1 14 c m RVo RTo N (fun i => decide (0 < tf i))
      (fun i => nE + rk i) (fun i => nE + nT + rk i)
      (fun i => if 0 < lf i then nE + nT + rk (ta i) else re i) := by
  intro d i hd hi h05 h03 h04 hreg hmem
  have hA' := hA.transfer hO hmem
  have hR' := hR.of fun r h1 h2 => hreg r (by omega)
  obtain ⟨d', k, ex, hk, v6, v7, v8, v9, vR, vm, vr, vrm, vo⟩ :=
    val1_exec (P := P) d hd hR' h05 h04 (hA'.vhyp hi)
  obtain ⟨t1, t2⟩ := hA'.tf i hi
  refine ⟨d', k, ex, hk, ?_, fun _ => ⟨?_, ?_, ?_⟩, vR, vm, vr, vrm, vo⟩
  · rw [v6, t1]; by_cases h0 : 0 < tf i <;> simp [h0] <;> omega
  · rw [v7, (hA'.rk i hi).1]
  · rw [v8, (hA'.rk i hi).1]
  · beta_reduce
    rw [v9, (hA'.lf i hi).1]
    split_ifs
    · rw [(hA'.ta i hi).1, (hA'.rk _ (hA'.ta i hi).2).1]
    · rw [(hA'.re i hi).1]

theorem val2_spec (hR : VRegs c LFb TFb REb RKb TAb TIb RVb RTb nE nT)
    (hA : WrArr c LFb TFb REb RKb TAb TIb RVb RTb nE nT m W lf tf re rk ta ti rv rt)
    (hO : WrOut LFb TFb REb RKb TAb TIb RVb RTb m RVo RTo N) :
    ValSpec (W := W) (P := P) val2 11 c m RVo RTo N (fun i => decide (0 < tf i))
      (fun i => nE + nT + rk i) (fun i => nE + rk i) (fun i => nE + 3 * nT + rk (ti i)) := by
  intro d i hd hi h05 h03 h04 hreg hmem
  have hA' := hA.transfer hO hmem
  have hR' := hR.of fun r h1 h2 => hreg r (by omega)
  obtain ⟨d', k, ex, hk, v6, v7, v8, v9, vR, vm, vr, vrm, vo⟩ :=
    val2_exec (P := P) d hd hR' h05 (hA'.vhyp hi)
  obtain ⟨t1, t2⟩ := hA'.tf i hi
  refine ⟨d', k, ex, hk, ?_, fun _ => ⟨?_, ?_, ?_⟩, vR, vm, vr, vrm, vo⟩
  · rw [v6, t1]; by_cases h0 : 0 < tf i <;> simp [h0] <;> omega
  · rw [v7, (hA'.rk i hi).1]
  · rw [v8, (hA'.rk i hi).1]
  · rw [v9, (hA'.ti i hi).1, (hA'.rk _ (hA'.ti i hi).2).1]

theorem val3_spec (hR : VRegs c LFb TFb REb RKb TAb TIb RVb RTb nE nT)
    (hA : WrArr c LFb TFb REb RKb TAb TIb RVb RTb nE nT m W lf tf re rk ta ti rv rt)
    (hO : WrOut LFb TFb REb RKb TAb TIb RVb RTb m RVo RTo N) :
    ValSpec (W := W) (P := P) val3 11 c m RVo RTo N (fun i => decide (0 < tf i))
      (fun i => nE + 2 * nT + rk i) (fun i => nE + 3 * nT + rk i)
      (fun i => nE + 2 * nT + rk (ta i)) := by
  intro d i hd hi h05 h03 h04 hreg hmem
  have hA' := hA.transfer hO hmem
  have hR' := hR.of fun r h1 h2 => hreg r (by omega)
  obtain ⟨d', k, ex, hk, v6, v7, v8, v9, vR, vm, vr, vrm, vo⟩ :=
    val3_exec (P := P) d hd hR' h05 (hA'.vhyp hi)
  obtain ⟨t1, t2⟩ := hA'.tf i hi
  refine ⟨d', k, ex, hk, ?_, fun _ => ⟨?_, ?_, ?_⟩, vR, vm, vr, vrm, vo⟩
  · rw [v6, t1]; by_cases h0 : 0 < tf i <;> simp [h0] <;> omega
  · rw [v7, (hA'.rk i hi).1]
  · rw [v8, (hA'.rk i hi).1]
  · rw [v9, (hA'.ta i hi).1, (hA'.rk _ (hA'.ta i hi).2).1]

theorem val4_spec (hR : VRegs c LFb TFb REb RKb TAb TIb RVb RTb nE nT)
    (hA : WrArr c LFb TFb REb RKb TAb TIb RVb RTb nE nT m W lf tf re rk ta ti rv rt)
    (hO : WrOut LFb TFb REb RKb TAb TIb RVb RTb m RVo RTo N) :
    ValSpec (W := W) (P := P) val4 7 c m RVo RTo N (fun i => decide (0 < tf i))
      (fun i => nE + 3 * nT + rk i) (fun i => nE + 2 * nT + rk i) (fun i => nE + rk i) := by
  intro d i hd hi h05 h03 h04 hreg hmem
  have hA' := hA.transfer hO hmem
  have hR' := hR.of fun r h1 h2 => hreg r (by omega)
  obtain ⟨d', k, ex, hk, v6, v7, v8, v9, vR, vm, vr, vrm, vo⟩ :=
    val4_exec (P := P) d hd hR' h05 (hA'.vhyp hi)
  obtain ⟨t1, t2⟩ := hA'.tf i hi
  refine ⟨d', k, ex, hk, ?_, fun _ => ⟨?_, ?_, ?_⟩, vR, vm, vr, vrm, vo⟩
  · rw [v6, t1]; by_cases h0 : 0 < tf i <;> simp [h0] <;> omega
  · rw [v7, (hA'.rk i hi).1]
  · rw [v8, (hA'.rk i hi).1]
  · rw [v9, (hA'.rk i hi).1]

end Specs

/-! ### The five loops -/

/-- The words of the cut written by the five loops (on arrays). -/
structure CutWords (mem : ℕ → ℕ) (RVo RTo nE nT m : ℕ) (lf tf re rk ta ti rv rt : ℕ → ℕ) :
    Prop where
  e : ∀ i < m, lf i = 0 → mem (RVo + re i) = re (rv i) ∧
    mem (RTo + re i) = if 0 < tf i then nE + nT + rk (ta i) else re (rt i)
  t1 : ∀ i < m, 0 < tf i → mem (RVo + (nE + rk i)) = nE + nT + rk i ∧
    mem (RTo + (nE + rk i)) = if 0 < lf i then nE + nT + rk (ta i) else re i
  t2 : ∀ i < m, 0 < tf i → mem (RVo + (nE + nT + rk i)) = nE + rk i ∧
    mem (RTo + (nE + nT + rk i)) = nE + 3 * nT + rk (ti i)
  t3 : ∀ i < m, 0 < tf i → mem (RVo + (nE + 2 * nT + rk i)) = nE + 3 * nT + rk i ∧
    mem (RTo + (nE + 2 * nT + rk i)) = nE + 2 * nT + rk (ta i)
  t4 : ∀ i < m, 0 < tf i → mem (RVo + (nE + 3 * nT + rk i)) = nE + 2 * nT + rk i ∧
    mem (RTo + (nE + 3 * nT + rk i)) = nE + rk i

set_option maxHeartbeats 2000000 in
/-- **The five write loops** (on arrays): with the positions of the copies (`re`, below `nE`)
and of the roots (`rk`, below `nT`) injective on the selected darts, within `100 m + 25` steps
the words `CutWords` are written; the memory outside the two output blocks of `nE + 4 nT`
words, the registers outside `8203 … 8219`, reals and output kept. -/
theorem cutWr_exec (c : Config) (hc : WordsBounded W c)
    {LFb TFb REb RKb TAb TIb RVb RTb nE nT m RVo RTo : ℕ} {lf tf re rk ta ti rv rt : ℕ → ℕ}
    (hR : VRegs c LFb TFb REb RKb TAb TIb RVb RTb nE nT) (r00 : c.nreg 8200 = m)
    (r01 : c.nreg 8201 = RVo) (r02 : c.nreg 8202 = RTo)
    (hA : WrArr c LFb TFb REb RKb TAb TIb RVb RTb nE nT m W lf tf re rk ta ti rv rt)
    (hO : WrOut LFb TFb REb RKb TAb TIb RVb RTb m RVo RTo (nE + 4 * nT))
    (hE : ∀ i < m, lf i = 0 → re i < nE)
    (hEi : ∀ i < m, ∀ j < m, lf i = 0 → lf j = 0 → re i = re j → i = j)
    (hT : ∀ i < m, 0 < tf i → rk i < nT)
    (hTi : ∀ i < m, ∀ j < m, 0 < tf i → 0 < tf j → rk i = rk j → i = j)
    (hd : RVo + (nE + 4 * nT) ≤ RTo ∨ RTo + (nE + 4 * nT) ≤ RVo)
    (w1 : RVo + (nE + 4 * nT) ≤ W) (w2 : RTo + (nE + 4 * nT) ≤ W) (w3 : m + 1 ≤ W) :
    ∃ c' t, Exec P W cutWr c c' t ∧ t ≤ 100 * m + 25 ∧
      CutWords c'.nmem RVo RTo nE nT m lf tf re rk ta ti rv rt ∧
      (∀ a, (a < RVo ∨ RVo + (nE + 4 * nT) ≤ a) → (a < RTo ∨ RTo + (nE + 4 * nT) ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 8203 ∨ 8219 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set N := nE + 4 * nT with hN
  -- loop E
  obtain ⟨c₁, k₁, e₁, hk₁, wE, fE, pE, rE, xr₁, xm₁, xo₁⟩ := wrLoop_exec (P := P) c hc r00 r01 r02
    (valE_spec (P := P) (N := N) hR hA hO)
    (fun i hi hs => by have := hE i hi (by simpa using hs); omega)
    (fun i hi j hj hsi hsj e => hEi i hi j hj (by simpa using hsi) (by simpa using hsj) e)
    hd w1 w2 w3
  have g₁ : ∀ r, (r < 8203 ∨ 8219 < r) → c₁.nreg r = c.nreg r := rE
  have hR₁ := hR.of fun r h1 h2 => g₁ r (by omega)
  have hA₁ := hA.transfer hO fE
  -- loop 1
  obtain ⟨c₂, k₂, e₂, hk₂, w1', f1, p1, r1, xr₂, xm₂, xo₂⟩ := wrLoop_exec (P := P) c₁
    e₁.wb_right (by rw [g₁ _ (by omega), r00]) (by rw [g₁ _ (by omega), r01])
    (by rw [g₁ _ (by omega), r02]) (val1_spec (P := P) (N := N) hR₁ hA₁ hO)
    (fun i hi hs => by have := hT i hi (by simpa using hs); omega)
    (fun i hi j hj hsi hsj e => hTi i hi j hj (by simpa using hsi) (by simpa using hsj)
      (by omega)) hd w1 w2 w3
  have g₂ : ∀ r, (r < 8203 ∨ 8219 < r) → c₂.nreg r = c.nreg r := fun r hr => by
    rw [r1 r hr, g₁ r hr]
  have hR₂ := hR.of fun r h1 h2 => g₂ r (by omega)
  have hA₂ := hA₁.transfer hO f1
  -- loop 2
  obtain ⟨c₃, k₃, e₃, hk₃, w2', f2, p2, r2, xr₃, xm₃, xo₃⟩ := wrLoop_exec (P := P) c₂
    e₂.wb_right (by rw [g₂ _ (by omega), r00]) (by rw [g₂ _ (by omega), r01])
    (by rw [g₂ _ (by omega), r02]) (val2_spec (P := P) (N := N) hR₂ hA₂ hO)
    (fun i hi hs => by have := hT i hi (by simpa using hs); omega)
    (fun i hi j hj hsi hsj e => hTi i hi j hj (by simpa using hsi) (by simpa using hsj)
      (by omega)) hd w1 w2 w3
  have g₃ : ∀ r, (r < 8203 ∨ 8219 < r) → c₃.nreg r = c.nreg r := fun r hr => by
    rw [r2 r hr, g₂ r hr]
  have hR₃ := hR.of fun r h1 h2 => g₃ r (by omega)
  have hA₃ := hA₂.transfer hO f2
  -- loop 3
  obtain ⟨c₄, k₄, e₄, hk₄, w3', f3, p3, r3, xr₄, xm₄, xo₄⟩ := wrLoop_exec (P := P) c₃
    e₃.wb_right (by rw [g₃ _ (by omega), r00]) (by rw [g₃ _ (by omega), r01])
    (by rw [g₃ _ (by omega), r02]) (val3_spec (P := P) (N := N) hR₃ hA₃ hO)
    (fun i hi hs => by have := hT i hi (by simpa using hs); omega)
    (fun i hi j hj hsi hsj e => hTi i hi j hj (by simpa using hsi) (by simpa using hsj)
      (by omega)) hd w1 w2 w3
  have g₄ : ∀ r, (r < 8203 ∨ 8219 < r) → c₄.nreg r = c.nreg r := fun r hr => by
    rw [r3 r hr, g₃ r hr]
  have hR₄ := hR.of fun r h1 h2 => g₄ r (by omega)
  have hA₄ := hA₃.transfer hO f3
  -- loop 4
  obtain ⟨c₅, k₅, e₅, hk₅, w4', f4, p4, r4, xr₅, xm₅, xo₅⟩ := wrLoop_exec (P := P) c₄
    e₄.wb_right (by rw [g₄ _ (by omega), r00]) (by rw [g₄ _ (by omega), r01])
    (by rw [g₄ _ (by omega), r02]) (val4_spec (P := P) (N := N) hR₄ hA₄ hO)
    (fun i hi hs => by have := hT i hi (by simpa using hs); omega)
    (fun i hi j hj hsi hsj e => hTi i hi j hj (by simpa using hsi) (by simpa using hsj)
      (by omega)) hd w1 w2 w3
  -- the cells of a block survive the later loops
  have k4 : ∀ a, (∀ i < m, 0 < tf i → a ≠ RVo + (nE + 3 * nT + rk i) ∧
      a ≠ RTo + (nE + 3 * nT + rk i)) → c₅.nmem a = c₄.nmem a := fun a ha =>
    p4 a fun i hi hs => ha i hi (by simpa using hs)
  have k3 : ∀ a, (∀ i < m, 0 < tf i → a ≠ RVo + (nE + 2 * nT + rk i) ∧
      a ≠ RTo + (nE + 2 * nT + rk i)) → c₄.nmem a = c₃.nmem a := fun a ha =>
    p3 a fun i hi hs => ha i hi (by simpa using hs)
  have k2 : ∀ a, (∀ i < m, 0 < tf i → a ≠ RVo + (nE + nT + rk i) ∧
      a ≠ RTo + (nE + nT + rk i)) → c₃.nmem a = c₂.nmem a := fun a ha =>
    p2 a fun i hi hs => ha i hi (by simpa using hs)
  have k1 : ∀ a, (∀ i < m, 0 < tf i → a ≠ RVo + (nE + rk i) ∧
      a ≠ RTo + (nE + rk i)) → c₂.nmem a = c₁.nmem a := fun a ha =>
    p1 a fun i hi hs => ha i hi (by simpa using hs)
  -- the positions of a block lie in its range
  have pT : ∀ i < m, 0 < tf i → rk i < nT := hT
  refine ⟨c₅, k₁ + (k₂ + (k₃ + (k₄ + k₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega,
    ⟨fun i hi h0 => ?_, fun i hi ht => ?_, fun i hi ht => ?_, fun i hi ht => ?_,
      fun i hi ht => ?_⟩, fun a h1 h2 => by rw [f4 a h1 h2, f3 a h1 h2, f2 a h1 h2, f1 a h1 h2,
        fE a h1 h2], fun r hr => by rw [r4 r hr, g₄ r hr], by rw [xr₅, xr₄, xr₃, xr₂, xr₁],
    by rw [xm₅, xm₄, xm₃, xm₂, xm₁], by rw [xo₅, xo₄, xo₃, xo₂, xo₁]⟩
  · have hp := hE i hi h0
    obtain ⟨v1, v2⟩ := wE i hi (by simpa using h0)
    have q : ∀ a, (a = RVo + re i ∨ a = RTo + re i) → c₅.nmem a = c₁.nmem a := fun a ha => by
      rw [k4 a fun j hj hs => (by have := pT j hj hs; constructor <;> omega),
        k3 a fun j hj hs => (by have := pT j hj hs; constructor <;> omega),
        k2 a fun j hj hs => (by have := pT j hj hs; constructor <;> omega),
        k1 a fun j hj hs => (by have := pT j hj hs; constructor <;> omega)]
    exact ⟨by rw [q _ (Or.inl rfl)]; exact v1, by rw [q _ (Or.inr rfl)]; exact v2⟩
  · have hp := pT i hi ht
    obtain ⟨v1, v2⟩ := w1' i hi (by simpa using ht)
    have q : ∀ a, (a = RVo + (nE + rk i) ∨ a = RTo + (nE + rk i)) → c₅.nmem a = c₂.nmem a :=
      fun a ha => by
        rw [k4 a fun j hj hs => (by have := pT j hj hs; constructor <;> omega),
          k3 a fun j hj hs => (by have := pT j hj hs; constructor <;> omega),
          k2 a fun j hj hs => (by have := pT j hj hs; constructor <;> omega)]
    exact ⟨by rw [q _ (Or.inl rfl)]; exact v1, by rw [q _ (Or.inr rfl)]; exact v2⟩
  · have hp := pT i hi ht
    obtain ⟨v1, v2⟩ := w2' i hi (by simpa using ht)
    have q : ∀ a, (a = RVo + (nE + nT + rk i) ∨ a = RTo + (nE + nT + rk i)) →
        c₅.nmem a = c₃.nmem a := fun a ha => by
      rw [k4 a fun j hj hs => (by have := pT j hj hs; constructor <;> omega),
        k3 a fun j hj hs => (by have := pT j hj hs; constructor <;> omega)]
    exact ⟨by rw [q _ (Or.inl rfl)]; exact v1, by rw [q _ (Or.inr rfl)]; exact v2⟩
  · have hp := pT i hi ht
    obtain ⟨v1, v2⟩ := w3' i hi (by simpa using ht)
    have q : ∀ a, (a = RVo + (nE + 2 * nT + rk i) ∨ a = RTo + (nE + 2 * nT + rk i)) →
        c₅.nmem a = c₄.nmem a := fun a ha => by
      rw [k4 a fun j hj hs => (by have := pT j hj hs; constructor <;> omega)]
    exact ⟨by rw [q _ (Or.inl rfl)]; exact v1, by rw [q _ (Or.inr rfl)]; exact v2⟩
  · exact w4' i hi (by simpa using ht)

end MsEnc

end BKMNW

end PlanarFlow
