module

public import PlanarFlow.BKMNW.NpCntM
public import PlanarFlow.BKMNW.LinLoops

/-!
# `cntP`: the counts of the step on the machine

The program **`cntP`** of the step `stepPO` (registers `8300 … 8314`, plus the outputs `6801`,
`6806`):

* `cnA`: `d = r3004`, `m = mem d`, `k = mem (d + 1)`, `HLb = d + 4 + 5 m`, the scratch base
  `b = r3006 - 5` (the heap top), `Gb = r6807` and **`r6801 := mem Gb`** (the number
  of parts of the separator, `SegsAt`);
* `cnZ` loop: `MK[j] := 0` for `j ≤ k` (`MK = b`, above everything the step keeps);
* `cnM` loop: `MK[HL[i]] := 1` for `i < m`;
* `cnS` loop: `cnt := Σ_{1 ≤ j ≤ k} MK[j]`;
* `cnD`: **`r6806 := cnt + r6801`**.

**`cntP_spec`**: `cntP` meets **`CntPSpecS`** with the steps `cnT x = 7 m + 11 k + 40`
(`m = #pdarts`, `k = #Hs`) and any room `rO` with `k + 1 ≤ rO x`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

universe w

/-! ### The program -/

/-- Set-up, part 1: `d`, `m`, `1`, `k`, `HLb`, `5`. -/
def cnA1 : Stmt :=
  block [.copyN 8300 3004, .loadN 8301 8300, .constN 8302 1, .addN 8305 8300 8302,
    .loadN 8303 8305, .constN 8313 5, .mulN 8305 8301 8313, .addN 8304 8300 8305,
    .constN 8305 4, .addN 8304 8304 8305]

/-- Set-up, part 2: `Gb`, `r6801`, `b`, `k + 1`, `0`, `j := 0`. -/
def cnA2 : Stmt :=
  block [.copyN 8307 6807, .loadN 6801 8307, .subN 8306 3006 8313,
    .addN 8309 8303 8302, .constN 8314 0, .constN 8308 0]

/-- Set-up. -/
def cnA : Stmt := .seq cnA1 cnA2

/-- `MK[j] := 0`; `j := j + 1`. -/
def cnZ : Stmt := block [.addN 8311 8306 8308, .storeN 8311 8314, .addN 8308 8308 8302]

/-- `j := 0`. -/
def cnB : Stmt := block [.constN 8308 0]

/-- `MK[HL[i]] := 1`; `i := i + 1`. -/
def cnM : Stmt :=
  block [.addN 8311 8304 8308, .loadN 8311 8311, .addN 8311 8306 8311, .storeN 8311 8302,
    .addN 8308 8308 8302]

/-- `j := 1`, `cnt := 0`. -/
def cnC : Stmt := block [.constN 8308 1, .constN 8310 0]

/-- `cnt := cnt + MK[j]`; `j := j + 1`. -/
def cnS : Stmt :=
  block [.addN 8311 8306 8308, .loadN 8311 8311, .addN 8310 8310 8311, .addN 8308 8308 8302]

/-- `r6806 := cnt + r6801`. -/
def cnD : Stmt := block [.addN 6806 8310 6801]

/-- **The counts of the step.** -/
def cntP : Stmt :=
  .seq cnA (.seq (.whileLtN 8308 8309 cnZ) (.seq cnB (.seq (.whileLtN 8308 8301 cnM)
    (.seq cnC (.seq (.whileLtN 8308 8309 cnS) cnD)))))

/-! ### The blocks -/

section Blocks

variable {P : Input} {W : ℕ}

theorem cnA1_exec (c : Config) (hc : WordsBounded W c) {d m k : ℕ}
    (r4 : c.nreg 3004 = d) (hm : c.nmem d = m) (hk : c.nmem (d + 1) = k)
    (w1 : d + 5 * m + 4 ≤ W) (w3 : 5 ≤ W) :
    ∃ c' t, Exec P W cnA1 c c' t ∧ t = 10 ∧ c'.nreg 8300 = d ∧ c'.nreg 8301 = m ∧
      c'.nreg 8302 = 1 ∧ c'.nreg 8303 = k ∧ c'.nreg 8304 = d + 5 * m + 4 ∧ c'.nreg 8313 = 5 ∧
      (∀ x, (x < 8300 ∨ 8314 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cnA1
  exec_block
  all_goals try (clear * - r4 hm hk w1 w3; config_simp; simp only [r4, hm, hk]; omega)
  all_goals try (clear * - w1 w3; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r4, hm, hk]
  all_goals try omega
  simp only [upd_apply]; split_ifs <;> omega

theorem cnA2_exec (c : Config) (hc : WordsBounded W c) {e b k : ℕ}
    (r5 : c.nreg 6807 = e) (r6 : c.nreg 3006 = b + 5) (r2 : c.nreg 8302 = 1)
    (r3 : c.nreg 8303 = k) (r13 : c.nreg 8313 = 5) (w2 : k + 1 ≤ W) :
    ∃ c' t, Exec P W cnA2 c c' t ∧ t = 6 ∧ c'.nreg 8306 = b ∧
      c'.nreg 8308 = 0 ∧ c'.nreg 8309 = k + 1 ∧ c'.nreg 8314 = 0 ∧
      c'.nreg 6801 = c.nmem e ∧
      (∀ x, x ≠ 8306 → x ≠ 8307 → x ≠ 8308 → x ≠ 8309 → x ≠ 8314 → x ≠ 6801 →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cnA2
  exec_block
  all_goals try (clear * - r2 r3 w2; config_simp; simp only [r2, r3]; omega)
  all_goals try (clear * - w2; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 h3 h4 h5 h6 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r5, r6, r2, r3, r13]
  all_goals try omega
  simp only [upd_apply]; split_ifs <;> omega

theorem cnA_exec (c : Config) (hc : WordsBounded W c) {d e m k b : ℕ}
    (r4 : c.nreg 3004 = d) (r5 : c.nreg 6807 = e) (r6 : c.nreg 3006 = b + 5)
    (hm : c.nmem d = m) (hk : c.nmem (d + 1) = k) (w1 : d + 5 * m + 4 ≤ W) (w2 : k + 1 ≤ W)
    (w3 : 5 ≤ W) :
    ∃ c' t, Exec P W cnA c c' t ∧ t = 16 ∧ c'.nreg 8300 = d ∧ c'.nreg 8301 = m ∧
      c'.nreg 8302 = 1 ∧ c'.nreg 8303 = k ∧ c'.nreg 8304 = d + 5 * m + 4 ∧ c'.nreg 8306 = b ∧
      c'.nreg 8308 = 0 ∧ c'.nreg 8309 = k + 1 ∧ c'.nreg 8314 = 0 ∧
      c'.nreg 6801 = c.nmem e ∧
      (∀ x, (x < 8300 ∨ 8314 < x) → x ≠ 6801 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a0, a1, a2, a3, a4, a13, f₁, m₁, r₁, rm₁, o₁⟩ :=
    cnA1_exec (P := P) c hc r4 hm hk w1 w3
  obtain ⟨c₂, t₂, e₂, ht₂, b6, b8, b9, b14, b61, f₂, m₂, r₂, rm₂, o₂⟩ :=
    cnA2_exec (P := P) c₁ e₁.wb_right (by rw [f₁ _ (by omega), r5])
      (by rw [f₁ _ (by omega), r6]) a2 a3 a13 w2
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, ?_, ?_, ?_, ?_, ?_, b6, b8, b9, b14, ?_,
    fun x h1 h2 => ?_, by rw [m₂, m₁], by rw [r₂, r₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
  · rw [f₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a0]
  · rw [f₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a1]
  · rw [f₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a2]
  · rw [f₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a3]
  · rw [f₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a4]
  · rw [b61, m₁]
  · rw [f₂ x (by omega) (by omega) (by omega) (by omega) (by omega) h2, f₁ x h1]

theorem cnZ_exec (c : Config) (hc : WordsBounded W c) {b j : ℕ}
    (r6 : c.nreg 8306 = b) (r8 : c.nreg 8308 = j) (r2 : c.nreg 8302 = 1) (r14 : c.nreg 8314 = 0)
    (w1 : b + j ≤ W) (w2 : j + 1 ≤ W) :
    ∃ c' t, Exec P W cnZ c c' t ∧ t = 3 ∧ c'.nreg 8308 = j + 1 ∧
      c'.nmem = upd c.nmem (b + j) 0 ∧
      (∀ x, x ≠ 8308 → x ≠ 8311 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cnZ
  exec_block
  all_goals try (config_simp; simp only [r6, r8, r2, r14]; omega)
  refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r8, r2]
  · config_simp; simp only [r6, r8, r14]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem cnB_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W cnB c c' t ∧ t = 1 ∧ c'.nreg 8308 = 0 ∧
      (∀ x, x ≠ 8308 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cnB
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem cnM_exec (c : Config) (hc : WordsBounded W c) {b HLb i : ℕ}
    (r4 : c.nreg 8304 = HLb) (r6 : c.nreg 8306 = b) (r8 : c.nreg 8308 = i) (r2 : c.nreg 8302 = 1)
    (w1 : HLb + i ≤ W) (w2 : b + c.nmem (HLb + i) ≤ W) (w3 : i + 1 ≤ W) :
    ∃ c' t, Exec P W cnM c c' t ∧ t = 5 ∧ c'.nreg 8308 = i + 1 ∧
      c'.nmem = upd c.nmem (b + c.nmem (HLb + i)) 1 ∧
      (∀ x, x ≠ 8308 → x ≠ 8311 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cnM
  exec_block
  all_goals try (config_simp; simp only [r4, r6, r8, r2]; omega)
  refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r8, r2]
  · config_simp; simp only [r4, r6, r8, r2]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem cnC_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' t, Exec P W cnC c c' t ∧ t = 2 ∧ c'.nreg 8308 = 1 ∧ c'.nreg 8310 = 0 ∧
      (∀ x, x ≠ 8308 → x ≠ 8310 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cnC
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · config_simp
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem cnS_exec (c : Config) (hc : WordsBounded W c) {b j s : ℕ}
    (r6 : c.nreg 8306 = b) (r8 : c.nreg 8308 = j) (r2 : c.nreg 8302 = 1) (r10 : c.nreg 8310 = s)
    (w1 : b + j ≤ W) (w2 : s + c.nmem (b + j) ≤ W) (w3 : j + 1 ≤ W) :
    ∃ c' t, Exec P W cnS c c' t ∧ t = 4 ∧ c'.nreg 8308 = j + 1 ∧
      c'.nreg 8310 = s + c.nmem (b + j) ∧
      (∀ x, x ≠ 8308 → x ≠ 8310 → x ≠ 8311 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cnS
  exec_block
  all_goals try (config_simp; simp only [r6, r8, r2, r10]; omega)
  refine ⟨rfl, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r8, r2]
  · config_simp; simp only [r6, r8, r10]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem cnD_exec (c : Config) (hc : WordsBounded W c) {s n : ℕ}
    (r10 : c.nreg 8310 = n) (r1 : c.nreg 6801 = s) (w : n + s ≤ W) :
    ∃ c' t, Exec P W cnD c c' t ∧ t = 1 ∧ c'.nreg 6806 = n + s ∧
      (∀ x, x ≠ 6806 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cnD
  exec_block
  all_goals try (config_simp; simp only [r10, r1]; omega)
  refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r10, r1]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

end Blocks

/-! ### The loops -/

section Loops

variable {P : Input} {W : ℕ}

/-- **The zeroing loop** `MK[j] := 0`, `j ≤ k`. -/
theorem cnZL_exec (c : Config) (hc : WordsBounded W c) {b k : ℕ}
    (r6 : c.nreg 8306 = b) (r8 : c.nreg 8308 = 0) (r9 : c.nreg 8309 = k + 1)
    (r2 : c.nreg 8302 = 1) (r14 : c.nreg 8314 = 0) (w : b + k + 1 ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 8308 8309 cnZ) c c' t ∧ t ≤ 5 * (k + 1) + 2 ∧
      (∀ j ≤ k, c'.nmem (b + j) = 0) ∧
      (∀ a, ¬ (b ≤ a ∧ a ≤ b + k) → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 8308 → x ≠ 8311 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, x ≠ 8308 → x ≠ 8311 → c'.nreg x = c.nreg x) ∧
    (∀ j < i, c'.nmem (b + j) = 0) ∧
    (∀ a, ¬ (b ≤ a ∧ a < b + i) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', t, ex, ht, -, -, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 8308) (b := 8309)
    (body := cnZ) J (B := 3) c hc r8 r9 (Nat.zero_le _)
    ⟨fun _ _ _ => rfl, fun j hj => absurd hj (by omega), fun _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c₁ _ hi hw h8 h9 ⟨f, z, o, q1, q2, q3⟩ => by
      obtain ⟨c₂, t₂, e₂, ht₂, g8, gm, gn, gr, grm, go⟩ := cnZ_exec (P := P) c₁ hw
        (by rw [f _ (by omega) (by omega), r6]) h8 (by rw [f _ (by omega) (by omega), r2])
        (by rw [f _ (by omega) (by omega), r14]) (by omega) (by omega)
      refine ⟨c₂, t₂, e₂, ht₂.le, g8, by rw [gn _ (by omega) (by omega)]; exact h9,
        fun x h1 h2 => by rw [gn x h1 h2, f x h1 h2], fun j hj => ?_, fun a ha => ?_,
        by rw [gr, q1], by rw [grm, q2], by rw [go, q3]⟩
      · rw [gm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact z j hj
        · rw [upd_same]
      · rw [gm, upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
        exact o a (fun h => ha ⟨h.1, by omega⟩))
  exact ⟨c', t, ex, by omega, fun j hj => j2 j (by omega),
    fun a ha => j3 a (fun h => ha ⟨h.1, by omega⟩), j1, j4, j5, j6⟩

/-- **The marking loop** `MK[HL[i]] := 1`, `i < m`. -/
theorem cnML_exec (c : Config) (hc : WordsBounded W c) {b k m HLb : ℕ}
    (r4 : c.nreg 8304 = HLb) (r6 : c.nreg 8306 = b) (r8 : c.nreg 8308 = 0)
    (r1 : c.nreg 8301 = m) (r2 : c.nreg 8302 = 1) (w : b + k + 1 ≤ W) (w1 : HLb + m ≤ W)
    (hlo : HLb + m ≤ b) (hHL : ∀ i < m, c.nmem (HLb + i) ≤ k)
    (hz : ∀ j ≤ k, c.nmem (b + j) = 0) :
    ∃ c' t, Exec P W (.whileLtN 8308 8301 cnM) c c' t ∧ t ≤ 7 * m + 2 ∧
      (∀ j ≤ k, c'.nmem (b + j) = if ∃ i < m, c.nmem (HLb + i) = j then 1 else 0) ∧
      (∀ a, ¬ (b ≤ a ∧ a ≤ b + k) → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 8308 → x ≠ 8311 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, x ≠ 8308 → x ≠ 8311 → c'.nreg x = c.nreg x) ∧
    (∀ j ≤ k, c'.nmem (b + j) = if ∃ i' < i, c.nmem (HLb + i') = j then 1 else 0) ∧
    (∀ a, ¬ (b ≤ a ∧ a ≤ b + k) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', t, ex, ht, -, -, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 8308) (b := 8301)
    (body := cnM) J (B := 5) c hc r8 r1 (Nat.zero_le _)
    ⟨fun _ _ _ => rfl, fun j hj => by
      rw [hz j hj]; split_ifs with h
      · exact absurd h (fun ⟨i', hi', _⟩ => by omega)
      · rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c₁ _ hi hw h8 h1 ⟨f, z, o, q1, q2, q3⟩ => by
      have eHL : c₁.nmem (HLb + i) = c.nmem (HLb + i) := o _ (fun h => by omega)
      have hHLi := hHL i hi
      obtain ⟨c₂, t₂, e₂, ht₂, g8, gm, gn, gr, grm, go⟩ := cnM_exec (P := P) c₁ hw
        (by rw [f _ (by omega) (by omega), r4]) (by rw [f _ (by omega) (by omega), r6]) h8
        (by rw [f _ (by omega) (by omega), r2]) (by omega) (by rw [eHL]; omega) (by omega)
      rw [eHL] at gm
      refine ⟨c₂, t₂, e₂, ht₂.le, g8, by rw [gn _ (by omega) (by omega)]; exact h1,
        fun x h1 h2 => by rw [gn x h1 h2, f x h1 h2], fun j hj => ?_, fun a ha => ?_,
        by rw [gr, q1], by rw [grm, q2], by rw [go, q3]⟩
      · rw [gm]
        by_cases hji : c.nmem (HLb + i) = j
        · rw [← hji, upd_same]; split_ifs with h
          · rfl
          · exact absurd ⟨i, by omega, rfl⟩ h
        · rw [upd_other _ _ _ (fun h => hji (by omega)), z j hj]
          congr 1
          refine propext ⟨fun ⟨i', h1, h2⟩ => ⟨i', by omega, h2⟩, fun ⟨i', h1, h2⟩ => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | rfl
          · exact ⟨i', h1, h2⟩
          · exact absurd h2 hji
      · rw [gm, upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
        exact o a ha)
  exact ⟨c', t, ex, by omega, j2, j3, j1, j4, j5, j6⟩

/-- **The summing loop** `cnt := Σ_{1 ≤ j ≤ k} MK[j]`. -/
theorem cnSL_exec (c : Config) (hc : WordsBounded W c) {b k : ℕ}
    (r6 : c.nreg 8306 = b) (r8 : c.nreg 8308 = 1) (r9 : c.nreg 8309 = k + 1)
    (r2 : c.nreg 8302 = 1) (r10 : c.nreg 8310 = 0) (w : b + k + 1 ≤ W)
    (hb : ∀ j ≤ k, c.nmem (b + j) ≤ 1) :
    ∃ c' t, Exec P W (.whileLtN 8308 8309 cnS) c c' t ∧ t ≤ 6 * k + 2 ∧
      c'.nreg 8310 = ∑ j ∈ Ico 1 (k + 1), c.nmem (b + j) ∧
      (∀ x, x ≠ 8308 → x ≠ 8310 → x ≠ 8311 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, x ≠ 8308 → x ≠ 8310 → x ≠ 8311 → c'.nreg x = c.nreg x) ∧
    c'.nreg 8310 = ∑ j ∈ Ico 1 i, c.nmem (b + j) ∧
    c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have hsum : ∀ i ≤ k + 1, ∑ j ∈ Ico 1 i, c.nmem (b + j) ≤ i := fun i _ => by
    calc ∑ j ∈ Ico 1 i, c.nmem (b + j) ≤ ∑ j ∈ Ico 1 i, 1 :=
          sum_le_sum fun j hj => hb j (by simp at hj; omega)
      _ ≤ i := by simp
  obtain ⟨c', t, ex, ht, -, -, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 8308) (b := 8309)
    (body := cnS) J (B := 4) c hc r8 r9 (by omega)
    ⟨fun _ _ _ _ => rfl, by rw [r10]; simp, rfl, rfl, rfl, rfl⟩
    (fun i c₁ hlo hi hw h8 h9 ⟨f, s, m₁, q1, q2, q3⟩ => by
      have hs := hsum i (by omega)
      have hbi := hb i (by omega)
      obtain ⟨c₂, t₂, e₂, ht₂, g8, g10, gn, gm, gr, grm, go⟩ := cnS_exec (P := P) c₁ hw
        (by rw [f _ (by omega) (by omega) (by omega), r6]) h8
        (by rw [f _ (by omega) (by omega) (by omega), r2]) s (by omega)
        (by rw [m₁]; omega) (by omega)
      refine ⟨c₂, t₂, e₂, ht₂.le, g8, by rw [gn _ (by omega) (by omega) (by omega)]; exact h9,
        fun x h1 h2 h3 => by rw [gn x h1 h2 h3, f x h1 h2 h3], ?_, by rw [gm, m₁],
        by rw [gr, q1], by rw [grm, q2], by rw [go, q3]⟩
      rw [g10, m₁, sum_Ico_succ_top (by omega)])
  exact ⟨c', t, ex, by omega, j2, j1, j3, j4, j5, j6⟩

end Loops

/-! ### The whole program -/

section Main

variable {P : Input} {W : ℕ}

/-- The sum computed by the summing loop is the number of present labels. -/
lemma cnt_sum_eq {mem : ℕ → ℕ} {HL : ℕ → ℕ} {b k m : ℕ}
    (h : ∀ j ≤ k, mem (b + j) = if ∃ i < m, HL i = j then 1 else 0) :
    ∑ j ∈ Ico 1 (k + 1), mem (b + j) =
      ∑ j ∈ range k, (if ∃ i < m, HL i = j + 1 then 1 else 0) := by
  rw [sum_Ico_eq_sum_range, show k + 1 - 1 = k by omega]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [h (1 + j) (by omega), show 1 + j = j + 1 by omega]

/-- **The run of `cntP`** from the frame of a call. -/
theorem cntP_exec (c : Config) (hc : WordsBounded W c) {d e b m k : ℕ}
    (r4 : c.nreg 3004 = d) (r5 : c.nreg 6807 = e) (r6 : c.nreg 3006 = b + 5)
    (hm : c.nmem d = m) (hk : c.nmem (d + 1) = k) (hde : d + 4 + 7 * m ≤ b)
    (w : b + k + 1 ≤ W) (hHL : ∀ i < m, c.nmem (d + 4 + 5 * m + i) ≤ k)
    (hs : c.nmem e ≤ b) :
    ∃ c' t, Exec P W cntP c c' t ∧ t ≤ 7 * m + 11 * k + 40 ∧
      c'.nreg 6801 = c.nmem e ∧
      c'.nreg 6806 = (∑ j ∈ range k,
        (if ∃ i < m, c.nmem (d + 4 + 5 * m + i) = j + 1 then 1 else 0)) + c.nmem e ∧
      (∀ x, (x < 8300 ∨ 8314 < x) → x ≠ 6801 → x ≠ 6806 → c'.nreg x = c.nreg x) ∧
      (∀ a, a < b → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cntP
  obtain ⟨c₁, t₁, e₁, ht₁, a0, a1, a2, a3, a4, a6, a8, a9, a14, a61, fa, ma, ra, rma, oa⟩ :=
    cnA_exec (P := P) c hc r4 r5 r6 hm hk (by omega) (by omega) (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, z1, z2, fz, rz, rmz, oz⟩ := cnZL_exec (P := P) c₁ e₁.wb_right a6 a8 a9
    a2 a14 w
  obtain ⟨c₃, t₃, e₃, ht₃, b8, fb, mb, rb, rmb, ob⟩ := cnB_exec (P := P) c₂ e₂.wb_right
  have hHL₃ : ∀ i < m, c₃.nmem (d + 5 * m + 4 + i) = c.nmem (d + 4 + 5 * m + i) := fun i hi => by
    rw [mb, z2 _ (fun h => by omega), ma, show d + 5 * m + 4 + i = d + 4 + 5 * m + i by omega]
  obtain ⟨c₄, t₄, e₄, ht₄, m1, m2, fm, rm, rmm, om⟩ := cnML_exec (P := P) c₃ e₃.wb_right (k := k)
    (by rw [fb _ (by omega), fz _ (by omega) (by omega), a4])
    (by rw [fb _ (by omega), fz _ (by omega) (by omega), a6]) b8
    (by rw [fb _ (by omega), fz _ (by omega) (by omega), a1])
    (by rw [fb _ (by omega), fz _ (by omega) (by omega), a2]) w (by omega) (by omega)
    (fun i hi => by rw [hHL₃ i hi]; exact hHL i hi) (fun j hj => by rw [mb]; exact z1 j hj)
  obtain ⟨c₅, t₅, e₅, ht₅, c8, c10, fc, mc, rc, rmc, oc⟩ := cnC_exec (P := P) c₄ e₄.wb_right
    (by omega)
  have hmk : ∀ j ≤ k, c₅.nmem (b + j) = if ∃ i < m, c.nmem (d + 4 + 5 * m + i) = j then 1 else 0 :=
    fun j hj => by
      rw [mc, m1 j hj]
      congr 1
      exact propext ⟨fun ⟨i, h1, h2⟩ => ⟨i, h1, by rw [← hHL₃ i h1]; exact h2⟩,
        fun ⟨i, h1, h2⟩ => ⟨i, h1, by rw [hHL₃ i h1]; exact h2⟩⟩
  have r5' : ∀ x, x ≠ 8308 → x ≠ 8310 → x ≠ 8311 → c₅.nreg x = c₁.nreg x := fun x h1 h2 h3 => by
    rw [fc x h1 h2, fm x h1 h3, fb x h1, fz x h1 h3]
  obtain ⟨c₆, t₆, e₆, ht₆, s10, fs, ms, rs, rms, os⟩ := cnSL_exec (P := P) c₅ e₅.wb_right (k := k)
    (by rw [r5' _ (by omega) (by omega) (by omega), a6]) c8
    (by rw [r5' _ (by omega) (by omega) (by omega), a9])
    (by rw [r5' _ (by omega) (by omega) (by omega), a2]) c10 w
    (fun j hj => by rw [hmk j hj]; split_ifs <;> omega)
  rw [cnt_sum_eq hmk] at s10
  have hcnt : ∑ j ∈ range k, (if ∃ i < m, c.nmem (d + 4 + 5 * m + i) = j + 1 then 1 else 0) ≤ k :=
    calc _ ≤ ∑ j ∈ range k, 1 := sum_le_sum fun j _ => by split_ifs <;> omega
      _ = k := by simp
  obtain ⟨c₇, t₇, e₇, ht₇, d6, fd, md, rd, rmd, od⟩ := cnD_exec (P := P) c₆ e₆.wb_right s10
    (by rw [fs _ (by omega) (by omega) (by omega), r5' _ (by omega) (by omega) (by omega), a61])
    (by omega)
  refine ⟨c₇, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), by omega,
    ?_, d6, fun x h1 h2 h3 => ?_, fun a ha => ?_, ?_, ?_, ?_⟩
  · rw [fd _ (by omega), fs _ (by omega) (by omega) (by omega),
      r5' _ (by omega) (by omega) (by omega), a61]
  · rw [fd x h3, fs x (by omega) (by omega) (by omega), r5' x (by omega) (by omega) (by omega),
      fa x h1 h2]
  · rw [md, ms, mc, m2 a (fun h => by omega), mb, z2 a (fun h => by omega), ma]
  · rw [rd, rs, rc, rm, rb, rz, ra]
  · rw [rmd, rms, rmc, rmm, rmb, rmz, rma]
  · rw [od, os, oc, om, ob, oz, oa]

end Main

section Spec

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- The steps of `cntP` at a call: `7 m + 11 k + 40`. -/
noncomputable def cntT (x : MCall M) : ℕ :=
  7 * (pdarts M x.1.piece x.2.1).card + 11 * x.2.1.length + 40
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {I : Input} {W : ℕ}

/-- **`cntP` meets `CntPSpecS`**: within `7 m + 11 k + 40` steps (`m = #pdarts`, `k = #Hs`),
for any room `rO` with `k + 1 ≤ rO x`. -/
theorem cntP_spec (Reach : MCall M → Prop) (rO : MCall M → ℕ)
    (hrO : ∀ x : MCall M, x.2.1.length + 1 ≤ rO x) :
    CntPSpecS M Reach gid u S T Z I W cntP (cntT M) rO := by
  intro l r π Hs σ d e b m en c hR hok hL hSg hde heb hroom hc r4 r5 r6
  have hk := hL.hk
  have hm := hL.hm
  have hcard : m = (pdarts M (l.piece ∪ r.piece) Hs).card := hL.card
  have hro := hrO (.node l r π, Hs, σ)
  simp only at hk hro
  unfold fsz at hde
  have hSg' := hSg
  obtain ⟨g1, g2, g3, -⟩ := hSg'
  have hs : c.nmem (c.nreg 6807) ≤ b := by omega
  obtain ⟨c', t, ex, ht, s1, s6, fr, fm, rr, rm, ro⟩ := cntP_exec (P := I) c hc r4 rfl r6 hm hk
    (by omega) (by omega)
    (fun i hi => by rw [(hL.hl i hi)]; exact hlab_le _ _) hs
  have hd : Hs.Pairwise Disjoint := hok.2.2.2.2.2.2
  have eph := pholes_length_eq hL hd
  simp only at eph
  refine ⟨c', t, ex, ?_, fun x h1 h2 => fr x (by omega) (by omega) (by omega), fun a ha =>
    ⟨fm a ha, by rw [rm]⟩, ro, fun x h1 h2 => fr x (by omega) (by omega) (by omega), by rw [s1, g2], ?_⟩
  · unfold cntT
    show t ≤ 7 * (pdarts M (l.piece ∪ r.piece) Hs).card + 11 * Hs.length + 40
    rw [← hcard]
    omega
  · rw [s6, g2]
    congr 1
    exact eph.symm

end Spec

end MfDrv

end BKMNW

end PlanarFlow
