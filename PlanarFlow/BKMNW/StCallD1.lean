module

public import PlanarFlow.BKMNW.StCallSC

/-!
# The run stage of the s-t flow call, part 1: the image at `ib` and the parameters

* `zres_lt`, `pstWN_mono`, `StEnc.KInM.clamp` (Klein's map words survive a clamped copy when
  they are at most the clamp), `StFix.sPrm_sum_le`, `StFix.sVM_le` (the parameters of `sNFM` are
  at most `7n + 9nD + B + pstM H + H + β + ib + len + 16`);
* **`stD1_exec`**: `stD1` copies the image `[IMb, IMb + len)` clamped to `W₀` to `ib`, zeroes the
  registers `< 1000`, writes the 45 parameters `sVM len m n H β₀ ib len` of `sNFM` into
  `r1000 …` and the log registers `r9150 = p`, `r9151 = 1`, within `11 len + 1018 + hpCost sPrmL`
  steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

variable {D' X Y : Type*} [Fintype D'] [DecidableEq D'] [Fintype X] [DecidableEq X]

/-- **Klein's map words survive a clamped copy** when every field value is at most the clamp. -/
theorem KInM.clamp {Q : CombMap D' X Y} {nD : ℕ} {σ : D' ≃ Fin nD} {ιv : X → ℕ}
    {ιg : D' → ℕ} {ιf : Y → ℕ} {ιe : D' → ℕ} {mem mem' : ℕ → ℕ} {β β' E cap : ℕ}
    (h : KInM Q σ ιv ιg ιf ιe mem β) (hE : ∀ d, ιe d < E) (hn : nD ≤ cap)
    (hv : ∀ x, ιv x ≤ cap) (hg : ∀ d, ιg d ≤ cap) (hf : ∀ y, ιf y ≤ cap) (he : ∀ d, ιe d ≤ cap)
    (hm : ∀ i < 8 * nD + E, mem' (β' + i) = min (mem (β + i)) cap) :
    KInM Q σ ιv ιg ιf ιe mem' β' where
  rv d := by
    have := (σ d).2; have := (σ (Q.rev d)).2
    rw [add_assoc, hm _ (by unfold Klein.iRV; omega), ← add_assoc, h.rv d]; omega
  nf d := by
    have := (σ d).2; have := hf (Q.face d)
    rw [add_assoc, hm _ (by unfold Klein.iNF; omega), ← add_assoc, h.nf d]; omega
  ne d := by
    have := (σ d).2; have := he d
    rw [add_assoc, hm _ (by unfold Klein.iNE; omega), ← add_assoc, h.ne d]; omega
  ng d := by
    have := (σ d).2; have := hg d
    rw [add_assoc, hm _ (by unfold Klein.iNG; omega), ← add_assoc, h.ng d]; omega
  nt d := by
    have := (σ d).2; have := hv (Q.tail d)
    rw [add_assoc, hm _ (by unfold Klein.iNT; omega), ← add_assoc, h.nt d]; omega
  nh d := by
    have := (σ d).2; have := hv (Q.head d)
    rw [add_assoc, hm _ (by unfold Klein.iNH; omega), ← add_assoc, h.nh d]; omega
  is d := by
    have := (σ d).2
    rw [add_assoc, hm _ (by unfold Klein.iIS; omega), ← add_assoc, h.is d]; omega
  ed d := by
    have := hE d
    rw [add_assoc, hm _ (by unfold Klein.iED; omega), ← add_assoc]
    have := (σ d).2; have := (σ (Q.rev d)).2
    rcases h.ed d with e | e
    · left; rw [e]; omega
    · right; rw [e]; omega

end StEnc

namespace StFix

open NegSSSP

/-- Every parameter sum of `sPrmL` is at most the bound of `sPrm_exec`. -/
theorem sPrm_sum_le {f : ℕ → ℕ} {B nD n H β ib len : ℕ} (hP : SPrim f B nD n H β ib len) :
    ∀ e ∈ sPrmL, hpSum f e.1 ≤
      7 * n + 9 * nD + B + STFlow.pstM H + H + β + ib + len + 16 := by
  intro e he
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hP
  simp only [sPrmL, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h <;> subst h <;>
    simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r0, r1,
      r2, r3, r4, r5, r6, r7] <;> omega

/-- **The parameters of `sNFM` are bounded.** -/
theorem sVM_le {B nD n H β ib len : ℕ} {j : ℕ} (hj : j < 45) :
    sVM B nD n H β ib len j ≤ 7 * n + 9 * nD + B + STFlow.pstM H + H + β + ib + len + 16 := by
  let f : ℕ → ℕ := fun r => if r = 8000 then n else if r = 8001 then nD else if r = 8002 then B
    else if r = 8003 then STFlow.pstM H else if r = 8004 then H else if r = 8005 then β
    else if r = 8006 then ib else len
  have hP : SPrim f B nD n H β ib len := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [← sPrm_val hP hj]
  have hm : sPrmL.getD j ([], 0) ∈ sPrmL := by
    rw [List.getD_eq_getElem _ _ (by rw [sPrmL_length]; exact hj)]; exact List.getElem_mem _
  have := sPrm_sum_le hP _ hm
  omega

end StFix

namespace StCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP StEnc
  NsStep STFlow CombMap

lemma zres_lt {Mo : ℕ} (hMo : 0 < Mo) (z : ℤ) : zres Mo z < Mo := by
  unfold zres
  have h1 := Int.emod_nonneg z (show (Mo : ℤ) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos z (show (0 : ℤ) < Mo by omega)
  omega

lemma pstWN_mono {W₀ H H' : ℕ} (h : H ≤ H') : pstWN W₀ H ≤ pstWN W₀ H' := by
  unfold pstWN pstM
  have := Nat.mul_le_mul (show 2 * H + 1 ≤ 2 * H' + 1 by omega)
    (show 2 * H + 1 ≤ 2 * H' + 1 by omega)
  omega

variable {P : Input} {W : ℕ}

/-- The cost of `stD1`. -/
def costD1 (m : ℕ) : ℕ := 11 * (37 * m + 13) + 1018 + hpCost StFix.sPrmL

set_option maxHeartbeats 800000 in
/-- **The image at `ib` and the parameters** (see the module docstring). -/
theorem stD1_exec (c : Config) (hc : WordsBounded W c) {m Sb ib p H : ℕ}
    (hL : StL c.nreg m Sb) (r00 : c.nreg 9100 = m) (r07 : c.nreg 9107 = ib)
    (r10 : c.nreg 9110 = p) (r45 : c.nreg 9145 = H) (r46 : c.nreg 9146 = pstM H)
    (lI : ib + (37 * m + 13) ≤ Sb + 3 * m ∨ Sb + 3 * m + (37 * m + 13) ≤ ib)
    (hW : Sb + stSz m ≤ W)
    (hWs : 7 * (4 * m + 1) + 9 * m + (37 * m + 13) + pstM H + H + (101 * m + 46) + ib +
      (37 * m + 13) + 16 ≤ W) :
    ∃ c' t, Exec P W stD1 c c' t ∧ t ≤ costD1 m ∧
      (∀ r < 1000, c'.nreg r = 0) ∧
      (∀ j < 45, c'.nreg (1000 + j) =
        StFix.sVM (37 * m + 13) m (4 * m + 1) H (101 * m + 46) ib (37 * m + 13) j) ∧
      c'.nreg 9150 = p ∧ c'.nreg 9151 = 1 ∧
      (∀ i < 37 * m + 13, c'.nmem (ib + i) = min (c.nmem (Sb + 3 * m + i)) (101 * m + 45)) ∧
      (∀ a, (a < ib ∨ ib + (37 * m + 13) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, 1045 ≤ r → (r < 8000 ∨ 8011 < r) → (r < 9120 ∨ 9128 < r) → r ≠ 9150 → r ≠ 9151 →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hSz : stSz m = 132 * m + 36 := rfl
  rw [hSz] at hW
  -- 1. the registers of the clamped copy
  obtain ⟨c₁, e₁, v₁, f₁, m₁, r₁, rm₁, o₁⟩ := cpL_exec (P := P) stSD1 (by decide) (by decide) c hc
  -- 2. the clamped copy
  obtain ⟨c₂, t₂, e₂, ht₂, CP₂, K₂, R₂, rr₂, rm₂, o₂⟩ := clpProg_exec (P := P) c₁ e₁.wb_right
    (n := 37 * m + 13) (Sb := Sb + 3 * m) (Db := ib) (cap := 101 * m + 45)
    (by rw [v₁ (9120, 9161) (by simp [stSD1]), hL.len])
    (by rw [v₁ (9121, 9164) (by simp [stSD1]), hL.im])
    (by rw [v₁ (9122, 9107) (by simp [stSD1]), r07])
    (by rw [v₁ (9123, 9162) (by simp [stSD1]), hL.w0]) lI.symm (by omega) (by omega)
    (by omega)
  have k₂ : ∀ r, (r < 9120 ∨ 9128 < r) → c₂.nreg r = c.nreg r := fun r hr => by
    rw [R₂ r (by omega), f₁ r (by simp only [stSD1, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false]; omega)]
  -- 3. the registers `< 1000` zeroed
  obtain ⟨c₃, e₃, Z₃, K₃, m₃, rr₃, rm₃, o₃⟩ := mbZeroRegs_exec' (P := P) (List.range 1000) c₂
    e₂.wb_right
  have k₃ : ∀ r, 1000 ≤ r → (r < 9120 ∨ 9128 < r) → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    rw [K₃ r (by simp; omega), k₂ r h2]
  -- 4. the primary registers of `sPrm`
  obtain ⟨c₄, e₄, v₄, f₄, m₄, r₄, rm₄, o₄⟩ := cpL_exec (P := P) stSD2 (by decide) (by decide) c₃
    e₃.wb_right
  have b : ∀ x y, (x, y) ∈ stSD2 → ∀ v, c.nreg y = v → c₄.nreg x = v := fun x y hxy v hv => by
    rw [v₄ (x, y) hxy, k₃ y (by simp [stSD2] at hxy; omega) (by simp [stSD2] at hxy; omega), hv]
  have hP : StFix.SPrim c₄.nreg (37 * m + 13) m (4 * m + 1) H (101 * m + 46) ib (37 * m + 13) :=
    ⟨b _ _ (by simp [stSD2]) _ hL.n, b _ _ (by simp [stSD2]) _ r00,
      b _ _ (by simp [stSD2]) _ hL.len, b _ _ (by simp [stSD2]) _ r46,
      b _ _ (by simp [stSD2]) _ r45, b _ _ (by simp [stSD2]) _ hL.b0,
      b _ _ (by simp [stSD2]) _ r07, b _ _ (by simp [stSD2]) _ hL.len⟩
  -- 5. `sPrm`
  obtain ⟨c₅, e₅, V₅, F₅, m₅, rr₅, rm₅, o₅⟩ := StFix.sPrm_exec (I := P) c₄ e₄.wb_right hP hWs
  -- 6. the log registers
  obtain ⟨c₆, e₆, v₆, f₆, m₆, r₆, rm₆, o₆⟩ := cpL_exec (P := P) stSD3 (by decide) (by decide) c₅
    e₅.wb_right
  have k₅ : ∀ r, 1045 ≤ r → (r < 8000 ∨ 8011 < r) → (r < 9120 ∨ 9128 < r) →
      c₅.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [F₅ r (Or.inr h1) (by omega) (by omega), f₄ r (by simp only [stSD2, List.map_cons,
      List.map_nil, List.mem_cons, List.not_mem_nil, or_false]; omega), k₃ r (by omega) h3]
  refine ⟨c₆, _, e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq e₆)))), ?_, fun r hr => ?_,
    fun j hj => ?_, ?_, ?_, fun i hi => ?_, fun a ha => ?_, fun r h1 h2 h3 h4 h5 => ?_,
    by rw [r₆, rr₅, r₄, rr₃, rr₂, r₁], by rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · simp only [stSD1, stSD2, stSD3, List.length_cons, List.length_nil, List.length_range,
      costD1]
    omega
  · rw [f₆ r (by simp [stSD3]; omega), F₅ r (Or.inl hr) (by omega) (by omega),
      f₄ r (by simp only [stSD2, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false]; omega), Z₃ r (by simp; omega)]
  · rw [f₆ _ (by simp [stSD3]; omega), V₅ j hj]
  · rw [v₆ (9150, 9110) (by simp [stSD3]), k₅ _ (by omega) (by omega) (by omega), r10]
  · rw [v₆ (9151, 9182) (by simp [stSD3]), k₅ _ (by omega) (by omega) (by omega), hL.one]
  · rw [m₆, m₅, m₄, m₃, CP₂ i hi, m₁]
  · rw [m₆, m₅, m₄, m₃, K₂ a ha, m₁]
  · rw [f₆ r (by simp [stSD3]; omega), k₅ r h1 h2 h3]

end StCall

end BKMNW

end PlanarFlow
