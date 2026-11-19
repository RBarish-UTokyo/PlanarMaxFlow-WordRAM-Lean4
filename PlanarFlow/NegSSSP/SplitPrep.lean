module

public import PlanarFlow.NegSSSP.SplitStage
public import PlanarFlow.NegSSSP.LinGlue

/-!
# The canonical configuration of the split, prepared on the machine from the frame

`spPrep` (registers `< 972` zeroed, scratch `2966 … 2980`, the frame's address in `r3004`):
from the frame of a piece `P` (`InP`) it zeroes the registers `< 972`, reads `m`, `k` from the
frame, computes `L = log₂ (3k)` (`prepLog`, by halving), `spB0 k` and `spWs k`, zeroes the memory
`[0, spWs k]`, copies the reversal `cα` and the rotation `cσ` of the frame to `[0, k)`,
`[k, 2k)`, and sets `r10 r860 r861 r863 r865 r950`. **`spPrep_agree`**: the configuration reached
agrees with the canonical one `spCfgP P` on the registers `< 972` and the memory `[0, spWs k]`
(`Agree spU (spWs k)`), within `prepCost k = O(k log k)` steps; so the split run after it
writes the sides of `msplit P` (`msplit_run`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Driver

variable {P : Input} {W : ℕ}

/-! ### Zeroing a list of registers -/

/-- `r := 0` for every `r` of the list. -/
def spZeroRegs : List ℕ → Stmt
  | [] => .skip
  | r :: l => .seq (.instr (.constN r 0)) (spZeroRegs l)

theorem spZeroRegs_exec (l : List ℕ) (c : Config) (hc : WordsBounded W c) :
    ∃ c', Exec P W (spZeroRegs l) c c' l.length ∧ (∀ r ∈ l, c'.nreg r = 0) ∧
      (∀ r, r ∉ l → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  induction l generalizing c with
  | nil => exact ⟨c, .skip hc, by simp, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | cons r l ih =>
    have e₁ := Exec.constN (P := P) hc r 0 (Nat.zero_le _)
    obtain ⟨c', e₂, h1, h2, h3, h4, h5, h6⟩ := ih _ e₁.wb_right
    refine ⟨c', ?_, fun r' hr' => ?_, fun r' hr' => ?_, h3, h4, h5, h6⟩
    · have := Exec.seq e₁ e₂
      rw [List.length_cons, Nat.add_comm]; exact this
    · by_cases hl : r' ∈ l
      · exact h1 r' hl
      · rw [h2 r' hl]
        rcases List.mem_cons.1 hr' with rfl | h
        · simp [upd]
        · exact absurd h hl
    · simp only [List.mem_cons, not_or] at hr'
      rw [h2 r' hr'.2]
      simp only [upd_apply, hr'.1, ite_false]

/-! ### The program -/

/-- Constants, `m`, `k`, `3k`. -/
def prepB : Stmt := block [.constN 2966 1, .constN 2967 2, .constN 2977 0, .addN 2975 3004 2966,
  .loadN 2968 2975, .addN 2975 2975 2966, .loadN 2969 2975, .addN 2970 2969 2969,
  .addN 2970 2970 2969, .constN 2971 0]

/-- One halving. -/
def prepLogBody : Stmt := block [.divN 2970 2970 2967, .addN 2971 2971 2966]

/-- `r2971 := log₂ (3k)`. -/
def prepLog : Stmt := .whileLtN 2966 2970 prepLogBody

/-- `r2972 := spB0 k`, `r2973 := spWs k`, `r2978 := spWs k + 1`, `r2974 := 0`. -/
def prepB0 : Stmt := block [.addN 2975 2971 2967, .addN 2976 2969 2969, .addN 2976 2976 2969,
  .mulN 2975 2975 2976, .constN 2972 204, .mulN 2972 2972 2969, .addN 2972 2972 2975,
  .constN 2976 7, .addN 2972 2972 2976, .constN 2973 66, .mulN 2973 2973 2969,
  .addN 2973 2973 2972, .constN 2976 35, .addN 2973 2973 2976, .constN 2974 0,
  .addN 2978 2973 2966]

/-- One zero. -/
def prepZeroBody : Stmt := block [.storeN 2974 2977, .addN 2974 2974 2966]

/-- The bases of the copies. -/
def prepCpSet : Stmt := block [.constN 2974 0, .constN 2975 4, .addN 2979 3004 2975,
  .addN 2979 2979 2969, .addN 2980 2979 2969]

/-- One copy: `mem[h] := mem[d + 4 + k + h]`, `mem[k + h] := mem[d + 4 + 2k + h]`. -/
def prepCpBody : Stmt := block [.addN 2975 2979 2974, .loadN 2976 2975, .storeN 2974 2976,
  .addN 2975 2980 2974, .loadN 2976 2975, .addN 2975 2969 2974, .storeN 2975 2976,
  .addN 2974 2974 2966]

/-- The registers of the split. -/
def prepG : Stmt := block [.copyN 10 2966, .copyN 860 2968, .copyN 861 2969, .copyN 863 2969,
  .addN 865 2969 2969, .copyN 950 2972]

/-- **The preparation of the split** from the frame at `r3004`. -/
def spPrep : Stmt :=
  .seq (spZeroRegs (List.range 972)) <| .seq prepB <| .seq prepLog <| .seq prepB0 <|
  .seq (.whileLtN 2974 2978 prepZeroBody) <| .seq prepCpSet <|
  .seq (.whileLtN 2974 2969 prepCpBody) prepG

theorem spB0_eq (k : ℕ) : spB0 k = 204 * k + (Nat.log 2 (3 * k) + 2) * (3 * k) + 7 := by
  unfold spB0 PlanarSeparator.MillerProg.aEnd10 PlanarSeparator.MillerProg.aEnd
  ring

/-! ### The phases -/

theorem prepB_exec (c : Config) (hc : WordsBounded W c) {d m k : ℕ} (r04 : c.nreg 3004 = d)
    (hm : c.nmem (d + 1) = m) (hk : c.nmem (d + 2) = k) (w1 : d + 2 ≤ W) (w2 : 3 * k + 2 ≤ W) :
    ∃ c' t, Exec P W prepB c c' t ∧ t = 10 ∧ c'.nreg 2966 = 1 ∧ c'.nreg 2967 = 2 ∧
      c'.nreg 2977 = 0 ∧ c'.nreg 2968 = m ∧ c'.nreg 2969 = k ∧ c'.nreg 2970 = k + k + k ∧
      c'.nreg 2971 = 0 ∧ (∀ r, r < 2966 ∨ 2977 < r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold prepB
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, hm, hk]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r04, hm, hk])
  simp only [upd_apply]; split_ifs <;> omega

theorem prepLogBody_exec (c : Config) (hc : WordsBounded W c) {x L : ℕ}
    (r66 : c.nreg 2966 = 1) (r67 : c.nreg 2967 = 2) (r70 : c.nreg 2970 = x)
    (r71 : c.nreg 2971 = L) (w : L + 1 ≤ W) :
    ∃ c' t, Exec P W prepLogBody c c' t ∧ t = 2 ∧ c'.nreg 2970 = x / 2 ∧
      c'.nreg 2971 = L + 1 ∧ (∀ r, r ≠ 2970 → r ≠ 2971 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold prepLogBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r66, r67, r70, r71]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r66, r67, r70, r71])
  simp only [upd_apply]; split_ifs <;> omega

/-- **`log₂` by halving.** -/
theorem prepLog_exec (c : Config) (hc : WordsBounded W c) {n : ℕ}
    (r66 : c.nreg 2966 = 1) (r67 : c.nreg 2967 = 2) (r70 : c.nreg 2970 = n)
    (r71 : c.nreg 2971 = 0) (hW : n + 1 ≤ W) :
    ∃ c' t, Exec P W prepLog c c' t ∧ t ≤ 4 * n + 2 ∧ c'.nreg 2971 = Nat.log 2 n ∧
      (∀ r, r ≠ 2970 → r ≠ 2971 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let I : Config → Prop := fun c' => WordsBounded W c' ∧ c'.nreg 2966 = 1 ∧
    c'.nreg 2967 = 2 ∧ c'.nreg 2971 + Nat.log 2 (c'.nreg 2970) = Nat.log 2 n ∧
    (∀ r, r ≠ 2970 → r ≠ 2971 → c'.nreg r = c.nreg r) ∧
    c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have hlogn : Nat.log 2 n ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact (Nat.log_lt_self 2 h.ne').le
  obtain ⟨c', t, ex, ⟨-, g66, -, hL, hn, hm, hr, hrm, ho⟩, hexit, ht⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 2966) (b := 2970) (body := prepLogBody) I
      (fun c' => 4 * c'.nreg 2970) (fun c' h => h.1)
      (fun c₁ ⟨hw, h66, h67, hL, hn, hm, hr, hrm, ho⟩ hlt => by
        rw [h66] at hlt
        have hx : 1 ≤ Nat.log 2 (c₁.nreg 2970) := Nat.le_log_of_pow_le (by norm_num) (by omega)
        obtain ⟨c₂, t₂, e₂, ht₂, g70, g71, gn, gm, gr, grm, go⟩ :=
          prepLogBody_exec (P := P) c₁ hw h66 h67 rfl rfl (by omega)
        refine ⟨c₂, t₂, e₂, ⟨e₂.wb_right, by rw [gn _ (by omega) (by omega)]; exact h66,
          by rw [gn _ (by omega) (by omega)]; exact h67, ?_, fun r h1 h2 => ?_,
          by rw [gm, hm], by rw [gr, hr], by rw [grm, hrm], by rw [go, ho]⟩, ?_⟩
        · rw [g70, g71, Nat.log_div_base]; omega
        · rw [gn r h1 h2, hn r h1 h2]
        · rw [g70]; omega)
      ⟨hc, r66, r67, by rw [r71, r70, Nat.zero_add], fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have hx : Nat.log 2 (c'.nreg 2970) = 0 := Nat.log_of_lt (by rw [g66] at hexit; omega)
  refine ⟨c', t, ex, by rw [r70] at ht; omega, by omega, hn, hm, hr, hrm, ho⟩

theorem prepB0_exec (c : Config) (hc : WordsBounded W c) {k : ℕ}
    (r66 : c.nreg 2966 = 1) (r67 : c.nreg 2967 = 2) (r69 : c.nreg 2969 = k)
    (r71 : c.nreg 2971 = Nat.log 2 (3 * k)) (hW : spWs k + 205 ≤ W) :
    ∃ c' t, Exec P W prepB0 c c' t ∧ t = 16 ∧ c'.nreg 2972 = spB0 k ∧
      c'.nreg 2973 = spWs k ∧ c'.nreg 2974 = 0 ∧ c'.nreg 2978 = spWs k + 1 ∧
      (∀ r, r < 2972 ∨ (2976 < r ∧ r ≠ 2978) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hB := spB0_eq k
  have hp : (Nat.log 2 (3 * k) + 2) * (k + k + k) = (Nat.log 2 (3 * k) + 2) * (3 * k) := by
    ring_nf
  have hWs : spWs k = spB0 k + 66 * k + 35 := rfl
  have hlog : Nat.log 2 (3 * k) ≤ 3 * k := by
    rcases Nat.eq_zero_or_pos (3 * k) with h | h
    · simp [h]
    · exact (Nat.log_lt_self 2 h.ne').le
  unfold prepB0
  exec_block
  all_goals try ((try config_simp); (try simp only [r66, r67, r69, r71]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r66, r67, r69, r71])
  all_goals try omega
  simp only [upd_apply]; split_ifs <;> omega

theorem prepZero_exec (c : Config) (hc : WordsBounded W c) {n : ℕ}
    (r66 : c.nreg 2966 = 1) (r74 : c.nreg 2974 = 0) (r77 : c.nreg 2977 = 0)
    (r78 : c.nreg 2978 = n) (hW : n + 1 ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 2974 2978 prepZeroBody) c c' t ∧ t ≤ 4 * n + 2 ∧
      (∀ a < n, c'.nmem a = 0) ∧ (∀ a, n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2974 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ a < i, c'.nmem a = 0) ∧ (∀ a, i ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2974 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2974) (bR := 2978)
    (body := prepZeroBody) J (K := 2) (n := n) c hc r74 r78
    ⟨fun a ha => absurd ha (by omega), fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
      have q66 : c'.nreg 2966 = 1 := (jn _ (by omega)).trans r66
      have q77 : c'.nreg 2977 = 0 := (jn _ (by omega)).trans r77
      obtain ⟨c'', t, ex, ht, hm, h74, hn, hr, hrm, ho⟩ : ∃ c'' t,
          Exec P W prepZeroBody c' c'' t ∧ t = 2 ∧ c''.nmem = upd c'.nmem i 0 ∧
          c''.nreg 2974 = i + 1 ∧ (∀ r, r ≠ 2974 → c''.nreg r = c'.nreg r) ∧
          c''.rreg = c'.rreg ∧ c''.rmem = c'.rmem ∧ c''.output = c'.output := by
        unfold prepZeroBody
        exec_block
        all_goals try ((try config_simp); (try simp only [q66, q77, ha]); omega)
        refine ⟨rfl, ?_, ?_, fun r h1 => ?_, rfl, rfl, rfl⟩
        all_goals config_simp
        all_goals try (simp only [q66, q77, ha])
        simp only [upd_apply]; split_ifs <;> omega
      refine ⟨c'', t, ex, by omega, h74, (hn _ (by omega)).trans hb, fun a ha' => ?_,
        fun a ha' => ?_, fun r hr' => (hn r hr').trans (jn r hr'), by rw [hr, jr],
        by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        split_ifs with h
        · rfl
        · exact j1 a (by omega)
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega))
  obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₂, e₂, by omega, j1, j2, jn, jr, jrm, jo⟩

theorem prepCpSet_exec (c : Config) (hc : WordsBounded W c) {d k : ℕ}
    (r04 : c.nreg 3004 = d) (r69 : c.nreg 2969 = k) (hW : d + 4 + k + k ≤ W) :
    ∃ c' t, Exec P W prepCpSet c c' t ∧ t = 5 ∧ c'.nreg 2974 = 0 ∧
      c'.nreg 2979 = d + 4 + k ∧ c'.nreg 2980 = d + 4 + k + k ∧
      (∀ r, r ≠ 2974 → r ≠ 2975 → r ≠ 2979 → r ≠ 2980 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold prepCpSet
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, r69]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r04, r69])
  simp only [upd_apply]; split_ifs <;> omega

theorem prepCp_exec (c : Config) (hc : WordsBounded W c) {d k : ℕ}
    (r66 : c.nreg 2966 = 1) (r69 : c.nreg 2969 = k) (r74 : c.nreg 2974 = 0)
    (r79 : c.nreg 2979 = d + 4 + k) (r80 : c.nreg 2980 = d + 4 + k + k)
    (hW : d + 4 + k + k + k ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 2974 2969 prepCpBody) c c' t ∧ t ≤ 10 * k + 2 ∧
      (∀ h < k, c'.nmem h = c.nmem (d + 4 + k + h) ∧
        c'.nmem (k + h) = c.nmem (d + 4 + k + k + h)) ∧
      (∀ a, k + k ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2974 → r ≠ 2975 → r ≠ 2976 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ h < i, c'.nmem h = c.nmem (d + 4 + k + h) ∧
        c'.nmem (k + h) = c.nmem (d + 4 + k + k + h)) ∧
      (∀ a, i ≤ a → (a < k ∨ k + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2974 → r ≠ 2975 → r ≠ 2976 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2974) (bR := 2969)
    (body := prepCpBody) J (K := 8) (n := k) c hc r74 r69
    ⟨fun a ha => absurd ha (by omega), fun _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
      have q66 : c'.nreg 2966 = 1 := (jn _ (by omega) (by omega) (by omega)).trans r66
      have q79 : c'.nreg 2979 = d + 4 + k := (jn _ (by omega) (by omega) (by omega)).trans r79
      have q80 : c'.nreg 2980 = d + 4 + k + k :=
        (jn _ (by omega) (by omega) (by omega)).trans r80
      have eA : c'.nmem (d + 4 + k + i) = c.nmem (d + 4 + k + i) := j2 _ (by omega) (by omega)
      have eS : c'.nmem (d + 4 + k + k + i) = c.nmem (d + 4 + k + k + i) :=
        j2 _ (by omega) (by omega)
      obtain ⟨c'', t, ex, ht, hm, h74, hn, hr, hrm, ho⟩ : ∃ c'' t,
          Exec P W prepCpBody c' c'' t ∧ t = 8 ∧
          c''.nmem = upd (upd c'.nmem i (c.nmem (d + 4 + k + i))) (k + i)
            (c.nmem (d + 4 + k + k + i)) ∧
          c''.nreg 2974 = i + 1 ∧ (∀ r, r ≠ 2974 → r ≠ 2975 → r ≠ 2976 → c''.nreg r = c'.nreg r) ∧
          c''.rreg = c'.rreg ∧ c''.rmem = c'.rmem ∧ c''.output = c'.output := by
        unfold prepCpBody
        exec_block
        all_goals try ((try config_simp); (try simp only [q66, q79, q80, ha, hb]); omega)
        refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
        all_goals config_simp
        all_goals try (simp only [q66, q79, q80, ha, hb])
        · simp only [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false
            (show ¬ (d + 4 + k + k + i = i) by omega))]
          rw [eA, eS]
        · simp only [upd_apply]; split_ifs <;> omega
      refine ⟨c'', t, ex, by omega, h74, (hn _ (by omega) (by omega) (by omega)).trans hb,
        fun h hh => ?_, fun a h1 h2 => ?_,
        fun r h1 h2 h3 => (hn r h1 h2 h3).trans (jn r h1 h2 h3), by rw [hr, jr],
        by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hh with hh | rfl
        · obtain ⟨t1, t2⟩ := j1 h hh
          simp only [upd_apply]
          constructor <;> split_ifs <;> omega
        · simp only [upd_apply]
          constructor <;> split_ifs <;> omega
      · rw [hm]
        simp only [upd_apply]
        split_ifs <;> first | omega | exact j2 a (by omega) (by omega))
  obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₂, e₂, by omega, j1, fun a ha => j2 a (by omega) (by omega), jn, jr, jrm, jo⟩

theorem prepG_exec (c : Config) (hc : WordsBounded W c) {m k B : ℕ}
    (r66 : c.nreg 2966 = 1) (r68 : c.nreg 2968 = m) (r69 : c.nreg 2969 = k)
    (r72 : c.nreg 2972 = B) (hW : k + k ≤ W) :
    ∃ c' t, Exec P W prepG c c' t ∧ t = 6 ∧ c'.nreg 10 = 1 ∧ c'.nreg 860 = m ∧
      c'.nreg 861 = k ∧ c'.nreg 863 = k ∧ c'.nreg 865 = 2 * k ∧ c'.nreg 950 = B ∧
      (∀ r, r ≠ 10 → r ≠ 860 → r ≠ 861 → r ≠ 863 → r ≠ 865 → r ≠ 950 →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold prepG
  exec_block
  all_goals try ((try config_simp); (try simp only [r66, r68, r69, r72]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r66, r68, r69, r72])
  all_goals try omega
  simp only [upd_apply]; split_ifs <;> omega

/-- The cost of `spPrep`. -/
def prepCost (k : ℕ) : ℕ :=
  972 + 10 + (4 * (k + k + k) + 2) + 16 + (4 * (spWs k + 1) + 2) + 5 + (10 * k + 2) + 6

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

set_option maxHeartbeats 1600000 in
/-- **The preparation reaches the canonical configuration of the split** (on the registers
`< 972` and the memory up to `spWs k`), from the frame of the piece at `r3004`, the reals of the
work area zero, the frame above the work area. -/
theorem spPrep_agree {ℓ : D → ℤ} {L n : ℕ} {Q : Finset D} {d e : ℕ} (c : Config)
    (hc : WordsBounded W c) (hin : InP g N ℓ L n Q d e c) (r04 : c.nreg 3004 = d)
    (hd : spWs (ck N Q) < d) (hrr : ∀ r < 972, c.rreg r = 0)
    (hrm : ∀ a ≤ spWs (ck N Q), c.rmem a = 0) (hW : d + 4 + 3 * ck N Q + 1 ≤ W)
    (hW2 : spWs (ck N Q) + 205 ≤ W) :
    ∃ c' t, Exec P W spPrep c c' t ∧ t ≤ prepCost (ck N Q) ∧
      Agree spU (spWs (ck N Q)) (spCfgP g N Q) c' ∧
      (∀ a, spWs (ck N Q) < a → c'.nmem a = c.nmem a) ∧
      (∀ r, 972 ≤ r → (r < 2966 ∨ 2980 < r) → c'.nreg r = c.nreg r) ∧
      c'.nreg 2966 = 1 ∧ c'.nreg 2969 = ck N Q ∧ c'.nreg 2972 = spB0 (ck N Q) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set k := ck N Q with hk
  have hmk : Q.card ≤ k := ck_ge Q
  have hWs : spWs k = spB0 k + 66 * k + 35 := rfl
  have hB3 : 3 * k ≤ spB0 k := by unfold spB0; omega
  -- zero the registers
  obtain ⟨c₁, e₁, z₁, n₁, m₁, r₁, rm₁, o₁⟩ := spZeroRegs_exec (P := P) (List.range 972) c hc
  have N₁ : ∀ r, 972 ≤ r → c₁.nreg r = c.nreg r := fun r hr => n₁ r (by simp; omega)
  -- constants, `m`, `k`
  obtain ⟨c₂, t₂, e₂, ht₂, g66, g67, g77, g68, g69, g70, g71, n₂, m₂, r₂, rm₂, o₂⟩ :=
    prepB_exec (P := P) (d := d) (m := Q.card) (k := k) c₁ e₁.wb_right
      (by rw [N₁ _ (by omega)]; exact r04) (by rw [m₁]; exact hin.rm) (by rw [m₁]; exact hin.rk)
      (by omega) (by omega)
  -- `log₂ (3k)`
  obtain ⟨c₃, t₃, e₃, ht₃, h71, n₃, m₃, r₃, rm₃, o₃⟩ :=
    prepLog_exec (P := P) c₂ e₂.wb_right g66 g67 g70 g71 (by omega)
  have q₃ : ∀ r, r ≠ 2970 → r ≠ 2971 → r < 2966 ∨ 2977 < r → c₃.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => by rw [n₃ r h1 h2, n₂ r h3]
  -- `spB0`, `spWs`
  obtain ⟨c₄, t₄, e₄, ht₄, h72, h73, h74, h78, n₄, m₄, r₄, rm₄, o₄⟩ :=
    prepB0_exec (P := P) (k := k) c₃ e₃.wb_right (by rw [n₃ _ (by omega) (by omega)]; exact g66)
      (by rw [n₃ _ (by omega) (by omega)]; exact g67)
      (by rw [n₃ _ (by omega) (by omega)]; exact g69)
      (by rw [h71, show k + k + k = 3 * k by omega]) hW2
  -- zero the work area
  obtain ⟨c₅, t₅, e₅, ht₅, z₅, f₅, n₅, r₅, rm₅, o₅⟩ :=
    prepZero_exec (P := P) c₄ e₄.wb_right
      (by rw [n₄ _ (by omega), n₃ _ (by omega) (by omega)]; exact g66) h74
      (by rw [n₄ _ (by omega), n₃ _ (by omega) (by omega)]; exact g77) h78 (by omega)
  -- copy the reversal and the rotation
  obtain ⟨c₆, t₆, e₆, ht₆, h74', h79, h80, n₆, m₆, r₆, rm₆, o₆⟩ :=
    prepCpSet_exec (P := P) (d := d) (k := k) c₅ e₅.wb_right
      (by rw [n₅ _ (by omega), n₄ _ (by omega), n₃ _ (by omega) (by omega), n₂ _ (by omega),
        N₁ _ (by omega)]; exact r04)
      (by rw [n₅ _ (by omega), n₄ _ (by omega), n₃ _ (by omega) (by omega)]; exact g69)
      (by omega)
  obtain ⟨c₇, t₇, e₇, ht₇, cp₇, f₇, n₇, r₇, rm₇, o₇⟩ :=
    prepCp_exec (P := P) (d := d) (k := k) c₆ e₆.wb_right
      (by rw [n₆ _ (by omega) (by omega) (by omega) (by omega), n₅ _ (by omega),
        n₄ _ (by omega), n₃ _ (by omega) (by omega)]; exact g66)
      (by rw [n₆ _ (by omega) (by omega) (by omega) (by omega), n₅ _ (by omega),
        n₄ _ (by omega), n₃ _ (by omega) (by omega)]; exact g69)
      h74' h79 h80 (by omega)
  -- the registers of the split
  have q₇ : ∀ r, r ≠ 2970 → r ≠ 2971 → (r < 2966 ∨ 2980 < r ∨ r = 2966 ∨ r = 2968 ∨
      r = 2969) → c₇.nreg r = c₃.nreg r := fun r h1 h2 h3 => by
    rw [n₇ r (by omega) (by omega) (by omega), n₆ r (by omega) (by omega) (by omega) (by omega),
      n₅ r (by omega), n₄ r (by omega)]
  obtain ⟨c₈, t₈, e₈, ht₈, s10, s860, s861, s863, s865, s950, n₈, m₈, r₈, rm₈, o₈⟩ :=
    prepG_exec (P := P) (m := Q.card) (k := k) (B := spB0 k) c₇ e₇.wb_right
      (by rw [q₇ _ (by omega) (by omega) (by omega), n₃ _ (by omega) (by omega)]; exact g66)
      (by rw [q₇ _ (by omega) (by omega) (by omega), n₃ _ (by omega) (by omega)]; exact g68)
      (by rw [q₇ _ (by omega) (by omega) (by omega), n₃ _ (by omega) (by omega)]; exact g69)
      (by rw [n₇ _ (by omega) (by omega) (by omega), n₆ _ (by omega) (by omega) (by omega)
          (by omega), n₅ _ (by omega)]; exact h72)
      (by omega)
  -- the memory
  have M₆ : ∀ a, spWs k < a → c₆.nmem a = c.nmem a := fun a ha => by
    rw [m₆, f₅ a (by omega), m₄, m₃, m₂, m₁]
  have hal : ∀ h < k, c₈.nmem h = cα g N Q h := fun h hh => by
    rw [m₈, (cp₇ h hh).1, M₆ _ (by omega)]; exact hin.α h hh
  have hsg : ∀ h < k, c₈.nmem (k + h) = cσ g N Q h := fun h hh => by
    rw [m₈, (cp₇ h hh).2, M₆ _ (by omega), show d + 4 + k + k + h = d + 4 + 2 * k + h by omega]
    exact hin.σ h hh
  refine ⟨c₈, 0 + 972 + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + t₈)))))), ?_, ?_,
    ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_⟩, fun a ha => ?_,
    fun r h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e₁' : Exec P W (spZeroRegs (List.range 972)) c c₁ 972 := by simpa using e₁
    exact .seq e₁' (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈))))))
  · unfold prepCost; omega
  · have hr : r < 972 := by simpa [spU] using hr
    simp only [spCfgP, spCfg, spRegs]
    by_cases r10 : r = 10
    · subst r10; simp [s10]
    by_cases r60 : r = 860
    · subst r60; simp [s860]
    by_cases r61 : r = 861
    · subst r61; simp [s861, hk]
    by_cases r63 : r = 863
    · subst r63; simp [s863, hk]
    by_cases r65 : r = 865
    · subst r65; simp [s865, hk]
    by_cases r50 : r = 950
    · subst r50; simp [s950, hk]
    simp only [r10, r60, r61, r63, r65, r50, ite_false]
    rw [n₈ r r10 r60 r61 r63 r65 r50, q₇ r (by omega) (by omega) (by omega),
      n₃ r (by omega) (by omega), n₂ r (by omega)]
    exact z₁ r (List.mem_range.2 hr)
  · have hr : r < 972 := by simpa [spU] using hr
    rw [r₈, r₇, r₆, r₅, r₄, r₃, r₂, r₁, hrr r hr]; rfl
  · simp only [spCfgP, spCfg, spMem]
    split_ifs with h1 h2
    · exact hal a h1
    · rw [show a = k + (a - k) by omega]; rw [hsg _ (by omega)]
      congr 1; omega
    · rw [m₈, f₇ a (by omega), m₆, z₅ a (by omega)]
  · rw [rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁, hrm a ha]; rfl
  · rw [m₈, f₇ a (by omega), M₆ a ha]
  · rw [n₈ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      q₇ r (by omega) (by omega) (by omega), n₃ r (by omega) (by omega), n₂ r (by omega),
      N₁ r h1]
  · rw [n₈ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      q₇ _ (by omega) (by omega) (by omega), n₃ _ (by omega) (by omega)]; exact g66
  · rw [n₈ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      q₇ _ (by omega) (by omega) (by omega), n₃ _ (by omega) (by omega)]; exact g69
  · rw [n₈ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      n₇ _ (by omega) (by omega) (by omega), n₆ _ (by omega) (by omega) (by omega) (by omega),
      n₅ _ (by omega)]; exact h72
  · rw [r₈, r₇, r₆, r₅, r₄, r₃, r₂, r₁]
  · rw [rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁]
  · rw [o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]

/-! ### No output -/

/-- An instruction other than `outN`. -/
def instrNoOut : Instr → Bool
  | .outN _ => false
  | _ => true

/-- No `outN` in the statement. -/
def stmtNoOut : Stmt → Bool
  | .skip => true
  | .instr i => instrNoOut i
  | .seq s t => stmtNoOut s && stmtNoOut t
  | .ifLtN _ _ t e => stmtNoOut t && stmtNoOut e
  | .ifLtR _ _ t e => stmtNoOut t && stmtNoOut e
  | .whileLtN _ _ body => stmtNoOut body
  | .whileLtR _ _ body => stmtNoOut body

theorem effect_output {i : Instr} (hi : instrNoOut i = true) {c c' : Config}
    (h : i.effect P c = some c') : c'.output = c.output := by
  cases i with
  | divR r a b =>
    simp only [Instr.effect] at h
    split_ifs at h with h0
    cases h
    rfl
  | outN a => simp [instrNoOut] at hi
  | halt => cases h
  | jump _ => cases h
  | brLtN _ _ _ => cases h
  | brLtR _ _ _ => cases h
  | _ => simp only [Instr.effect, Option.some.injEq] at h; rw [← h]

/-- **A statement without `outN` keeps the output.** -/
theorem exec_output {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k)
    (hs : stmtNoOut s = true) : c'.output = c.output := by
  induction h with
  | skip _ => rfl
  | instr _ he _ _ => exact effect_output hs he
  | seq _ _ ih₁ ih₂ =>
    simp only [stmtNoOut, Bool.and_eq_true] at hs
    rw [ih₂ hs.2, ih₁ hs.1]
  | ifLtN_true _ _ ih => simp only [stmtNoOut, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtN_false _ _ ih => simp only [stmtNoOut, Bool.and_eq_true] at hs; exact ih hs.2
  | ifLtR_true _ _ ih => simp only [stmtNoOut, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtR_false _ _ ih => simp only [stmtNoOut, Bool.and_eq_true] at hs; exact ih hs.2
  | whileLtN_false _ _ => rfl
  | whileLtN_true _ _ _ ih₁ ih₂ => rw [ih₂ hs, ih₁ hs]
  | whileLtR_false _ _ => rfl
  | whileLtR_true _ _ _ ih₁ ih₂ => rw [ih₂ hs, ih₁ hs]

theorem splitProg_noOut : stmtNoOut splitProg = true := by decide +kernel

/-! ### The split stage -/

/-- **The split stage**: the preparation, then the split. -/
def spStage : Stmt := .seq spPrep splitProg

/-- **The split stage on the machine.** From the frame of a piece `Q ⊆ reps N` (plane map) at
`r3004`, the frame above the work area `[0, spWs k]` whose reals are zero: within
`prepCost k + splitT k = O(k log k)` steps, the side of the dart `cδ x` (`x < #Q`) at
`spB0 k + 41 k + 4 + x` is `0` exactly on the first part of `msplit Q`; the memory above
`spWs k`, the registers `≥ 972` but `2966 … 2980`, the reals and the output are kept. -/
theorem spStage_exec (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {ℓ : D → ℤ} {L n : ℕ} {Q : Finset D} (hQ : Q ⊆ reps N) {d e : ℕ} (c : Config)
    (hc : WordsBounded W c) (hin : InP g N ℓ L n Q d e c) (r04 : c.nreg 3004 = d)
    (hd : spWs (ck N Q) < d) (hrr : ∀ r < 972, c.rreg r = 0)
    (hrm : ∀ a ≤ spWs (ck N Q), c.rmem a = 0) (hW : d + 4 + 3 * ck N Q + 1 ≤ W)
    (hW2 : spWs (ck N Q) + 205 ≤ W) :
    ∃ c' t, Exec P W spStage c c' t ∧ t ≤ prepCost (ck N Q) + splitT (ck N Q) ∧
      (∀ x < Q.card, (c'.nmem (spB0 (ck N Q) + 41 * ck N Q + 4 + x) = 0 ↔
        cδ g N Q x ∈ (msplit g N Q).1) ∧
        (c'.nmem (spB0 (ck N Q) + 41 * ck N Q + 4 + x) ≠ 0 ↔ cδ g N Q x ∈ (msplit g N Q).2) ∧
        c'.nmem (spB0 (ck N Q) + 41 * ck N Q + 4 + x) ≤ 1) ∧
      c'.nreg 2966 = 1 ∧ c'.nreg 2969 = ck N Q ∧ c'.nreg 2972 = spB0 (ck N Q) ∧
      (∀ a, spWs (ck N Q) < a → c'.nmem a = c.nmem a) ∧
      (∀ r, 972 ≤ r → (r < 2966 ∨ 2980 < r) → c'.nreg r = c.nreg r) ∧
      (∀ r, 972 ≤ r → c'.rreg r = c.rreg r) ∧
      (∀ a, spWs (ck N Q) < a → c'.rmem a = c.rmem a) ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, hA, m₁, n₁, p66, p69, p72, r₁, rm₁, o₁⟩ :=
    spPrep_agree (P := P) c hc hin r04 hd hrr hrm hW hW2
  obtain ⟨⟨t₀, ex₀, ht₀⟩, -, -⟩ := spFin_run (g := g) hM hrot hface hQ
  obtain ⟨c₂, e₂, hA₂, hK₂, -⟩ := Exec.lift (P' := P) ex₀ splitProg_ok.1 splitProg_ok.2.1
    splitProg_ok.2.2 (show spWs (ck N Q) ≤ W by omega) hA e₁.wb_right
  have hside := msplit_run (g := g) hM hrot hface hQ hA e₂ (by omega)
  have hU : ∀ r, 972 ≤ r → spU r = false := fun r hr => by simp [spU]; omega
  refine ⟨c₂, t₁ + t₀, .seq e₁ e₂, by omega, hside, by rw [hK₂.nreg _ (hU _ (by omega))]; exact p66,
    by rw [hK₂.nreg _ (hU _ (by omega))]; exact p69,
    by rw [hK₂.nreg _ (hU _ (by omega))]; exact p72, fun a ha => ?_, fun r h1 h2 => ?_,
    fun r hr => ?_, fun a ha => ?_, ?_⟩
  · rw [hK₂.nmem a ha, m₁ a ha]
  · rw [hK₂.nreg r (hU r h1), n₁ r h1 h2]
  · rw [hK₂.rreg r (hU r hr), r₁]
  · rw [hK₂.rmem a ha, rm₁]
  · rw [exec_output e₂ splitProg_noOut, o₁]

end Frame

end NegSSSP

end PlanarFlow
