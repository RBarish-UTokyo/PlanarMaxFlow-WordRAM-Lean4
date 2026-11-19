module

public import PlanarFlow.BKMNW.NcHfPs
public import PlanarFlow.BKMNW.NcLoop

/-!
# The run of the hole-flag program `hfP`

`hfCopy_exec`, `hfScan_exec` (the scan `dscan i` of the sorted buffer), `hfFlag_exec`, and
**`hfP_exec`**: within `hfCost m = (30 m + 10) lg m + 32 m + 16` steps,
`F[t] = [HL[t] = hfV]` with **`hfV mem HLb m i = (dscan i (msortW m 1 HL)).2.2`**, the `i`-th
smallest distinct positive label when there are more than `i` of them (**`hfV_spec`**); the memory
changed only in `[A, Fb + m)` (the two buffers and the flags).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The label selected by `hfP`. -/
def hfV (mem : ℕ → ℕ) (HLb m i : ℕ) : ℕ := (dscan i (msortW m 1 (segL mem HLb m))).2.2

/-- **The selected label**: the element of the positive labels with exactly `i` smaller ones. -/
theorem hfV_spec {mem : ℕ → ℕ} {HLb m i : ℕ} (hi : i < (posVals (segL mem HLb m)).card) :
    hfV mem HLb m i ∈ posVals (segL mem HLb m) ∧
      ((posVals (segL mem HLb m)).filter (· < hfV mem HLb m i)).card = i :=
  dscan_spec (segL_length _ _ _) hi

/-- The step bound of `hfP`. -/
def hfCost (m : ℕ) : ℕ := (30 * m + 10) * lg m + 32 * m + 16

/-! ### The copy -/

theorem hfCopy_exec (c : Config) (hc : WordsBounded W c) {m HLb A : ℕ}
    (r57 : c.nreg 9757 = m) (r58 : c.nreg 9758 = HLb) (r60 : c.nreg 9760 = A)
    (h1 : HLb + m ≤ A) (w1 : A + m ≤ W) (w2 : m + 1 ≤ W) :
    ∃ c' k, Exec P W hfCopy c c' k ∧ k ≤ 7 * m + 4 ∧ c'.nreg 9764 = 1 ∧
      (∀ t < m, c'.nmem (A + t) = c.nmem (HLb + t)) ∧
      (∀ a, (a < A ∨ A + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 9764 → r ≠ 9775 → r ≠ 9778 → r ≠ 9781 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₀, k₀, e₀, hk₀, a64, a78, g₀, m₀, rr₀, rm₀, o₀⟩ :=
    hfCopyI_exec (P := P) c hc (by omega)
  have q : ∀ r, r ≠ 9764 → r ≠ 9778 → c₀.nreg r = c.nreg r := g₀
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁, g₁, a₁, rr₁, rm₁, o₁⟩ := lnStore (P := P) (a := 9778)
    (b := 9757) (body := hfCopyB) (Ob := A) (s := 1) (o := 0) (n := m) (B := 5) one_pos
    (fun t => c.nmem (HLb + t)) (fun r => r ≠ 9775 ∧ r ≠ 9778 ∧ r ≠ 9781) c₀ e₀.wb_right a78
    (by rw [q _ (by omega) (by omega), r57]) (by omega)
    (fun t c' ht hw e78 hk hm => by
      obtain ⟨c'', k, ex, hk', m', b78, g', rr', rm', o'⟩ := hfCopyB_exec (P := P) c' hw
        (HLb := HLb) (S := A) (t := t)
        (by rw [hk _ (by omega), q _ (by omega) (by omega), r58])
        (by rw [hk _ (by omega), q _ (by omega) (by omega), r60])
        (by rw [hk _ (by omega), a64]) e78 (by omega) (by omega) (by omega)
      refine ⟨c'', k, ex, by omega, b78, fun x hx => g' x hx.1 hx.2.1 hx.2.2, ?_, rr', rm', o'⟩
      rw [m', hm _ (fun j hj => by omega), m₀]
      simp only [one_mul, add_zero])
  refine ⟨c₁, k₀ + k₁, e₀.seq e₁, by omega, by rw [g₁ _ ⟨by omega, by omega, by omega⟩, a64],
    fun t ht => ?_, fun a ha => ?_, fun r h1 h2 h3 h4 => ?_, by rw [rr₁, rr₀],
    by rw [rm₁, rm₀], by rw [o₁, o₀]⟩
  · have := v₁ t ht; simp only [one_mul, add_zero] at this; exact this
  · rw [f₁ a (fun j hj => by omega), m₀]
  · rw [g₁ r ⟨h2, h3, h4⟩, q r h1 (by omega)]

/-! ### The scan -/

theorem hfScU_exec (c : Config) (hc : WordsBounded W c) {cnt i x v : ℕ}
    (r80 : c.nreg 9780 = cnt) (r59 : c.nreg 9759 = i) (r81 : c.nreg 9781 = x)
    (r63 : c.nreg 9763 = v) (r64 : c.nreg 9764 = 1) (w1 : cnt + 1 ≤ W) :
    ∃ c' k, Exec P W hfScU c c' k ∧ k ≤ 7 ∧ c'.nreg 9780 = cnt + 1 ∧ c'.nreg 9779 = x ∧
      c'.nreg 9763 = (if cnt = i then x else v) ∧
      (∀ r, r ≠ 9763 → r ≠ 9779 → r ≠ 9780 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- the inner test
  obtain ⟨c₁, k₁, e₁, hk₁, a63, g₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
      (.ifLtN 9780 9759 .skip (.ifLtN 9759 9780 .skip (block [.copyN 9763 9781]))) c c₁ k₁ ∧
      k₁ ≤ 5 ∧ c₁.nreg 9763 = (if cnt = i then x else v) ∧
      (∀ r, r ≠ 9763 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    by_cases h1 : cnt < i
    · refine ⟨c, 0 + 1, .ifLtN_true (by rw [r80, r59]; exact h1) (.skip hc), by omega,
        by rw [r63, iteF (by omega)], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    · by_cases h2 : i < cnt
      · refine ⟨c, 0 + 1 + 2, .ifLtN_false (by rw [r80, r59]; exact h1)
          (.ifLtN_true (by rw [r80, r59]; exact h2) (.skip hc)), by omega,
          by rw [r63, iteF (by omega)], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
      · obtain ⟨c₁, k₁, e₁, hk₁, h63, g₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
            (block [.copyN 9763 9781]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 9763 = x ∧
            (∀ r, r ≠ 9763 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
            c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
          exec_block
          refine ⟨rfl, ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
          all_goals config_simp
          · simp only [r81]
          · simp only [upd_apply]; split_ifs <;> omega
        refine ⟨c₁, k₁ + 2 + 2, .ifLtN_false (by rw [r80, r59]; exact h1)
          (.ifLtN_false (by rw [r80, r59]; exact h2) e₁), by omega,
          by rw [h63, iteT (by omega)], g₁, m₁, rr₁, rm₁, o₁⟩
  obtain ⟨c₂, k₂, e₂, hk₂, b80, b79, g₂, m₂, rr₂, rm₂, o₂⟩ : ∃ c₂ k₂, Exec P W
      (block [.addN 9780 9780 9764, .copyN 9779 9781]) c₁ c₂ k₂ ∧ k₂ = 2 ∧
      c₂.nreg 9780 = cnt + 1 ∧ c₂.nreg 9779 = x ∧
      (∀ r, r ≠ 9779 → r ≠ 9780 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have q80 : c₁.nreg 9780 = cnt := by rw [g₁ _ (by omega), r80]
    have q81 : c₁.nreg 9781 = x := by rw [g₁ _ (by omega), r81]
    have q64 : c₁.nreg 9764 = 1 := by rw [g₁ _ (by omega), r64]
    have hw₁ := e₁.wb_right
    exec_block
    all_goals try ((try config_simp); (try simp only [q80, q81, q64]); omega)
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [q80, q81, q64])
    simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₂, k₁ + k₂, e₁.seq e₂, by omega, b80, b79, by rw [g₂ _ (by omega) (by omega), a63],
    fun r h1 h2 h3 => by rw [g₂ r h2 h3, g₁ r h1], by rw [m₂, m₁], by rw [rr₂, rr₁],
    by rw [rm₂, rm₁], by rw [o₂, o₁]⟩

/-- **One step of the scan** is `dstep`. -/
theorem hfScB_exec (c : Config) (hc : WordsBounded W c) {Sb t i prev cnt v : ℕ}
    (r60 : c.nreg 9760 = Sb) (r64 : c.nreg 9764 = 1) (r78 : c.nreg 9778 = t)
    (r59 : c.nreg 9759 = i) (r79 : c.nreg 9779 = prev) (r80 : c.nreg 9780 = cnt)
    (r63 : c.nreg 9763 = v) (w1 : Sb + t ≤ W) (w2 : t + 1 ≤ W) (w3 : cnt + 1 ≤ W) :
    ∃ c' k, Exec P W hfScB c c' k ∧ k ≤ 12 ∧
      (c'.nreg 9779, c'.nreg 9780, c'.nreg 9763) =
        dstep i (prev, cnt, v) (c.nmem (Sb + t)) ∧ c'.nreg 9778 = t + 1 ∧
      (∀ r, r ≠ 9763 → r ≠ 9775 → r ≠ 9778 → r ≠ 9779 → r ≠ 9780 → r ≠ 9781 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a81, g₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W hfScL c c₁ k₁ ∧
      k₁ = 2 ∧ c₁.nreg 9781 = c.nmem (Sb + t) ∧
      (∀ r, r ≠ 9775 → r ≠ 9781 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold hfScL
    exec_block
    all_goals try ((try config_simp); (try simp only [r60, r78]); omega)
    refine ⟨rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    · simp only [r60, r78]
    · simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ r, r ≠ 9775 → r ≠ 9781 → c₁.nreg r = c.nreg r := g₁
  -- the test
  obtain ⟨c₂, k₂, e₂, hk₂, d₂, g₂, m₂, rr₂, rm₂, o₂⟩ : ∃ c₂ k₂, Exec P W
      (.ifLtN 9779 9781 hfScU .skip) c₁ c₂ k₂ ∧ k₂ ≤ 9 ∧
      (c₂.nreg 9779, c₂.nreg 9780, c₂.nreg 9763) = dstep i (prev, cnt, v) (c.nmem (Sb + t)) ∧
      (∀ r, r ≠ 9763 → r ≠ 9779 → r ≠ 9780 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have q79 : c₁.nreg 9779 = prev := by rw [q _ (by omega) (by omega), r79]
    by_cases hlt : prev < c.nmem (Sb + t)
    · obtain ⟨c₂, k₂, e₂, hk₂, b80, b79, b63, g₂, m₂, rr₂, rm₂, o₂⟩ := hfScU_exec (P := P) c₁ hw₁
        (cnt := cnt) (i := i) (x := c.nmem (Sb + t)) (v := v)
        (by rw [q _ (by omega) (by omega), r80]) (by rw [q _ (by omega) (by omega), r59]) a81
        (by rw [q _ (by omega) (by omega), r63]) (by rw [q _ (by omega) (by omega), r64]) w3
      refine ⟨c₂, k₂ + 1, .ifLtN_true (by rw [q79, a81]; exact hlt) e₂, by omega, ?_, g₂, m₂,
        rr₂, rm₂, o₂⟩
      rw [b80, b79, b63]; unfold dstep; simp only [hlt, ↓reduceIte]
    · refine ⟨c₁, 0 + 2, .ifLtN_false (by rw [q79, a81]; exact hlt) (.skip hw₁), by omega, ?_,
        fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
      rw [q79, q _ (by omega) (by omega), q _ (by omega) (by omega), r80, r63]
      unfold dstep; simp only [hlt, ↓reduceIte]
  have hw₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, b78, g₃, m₃, rr₃, rm₃, o₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.addN 9778 9778 9764]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 9778 = t + 1 ∧
      (∀ r, r ≠ 9778 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have q78 : c₂.nreg 9778 = t := by rw [g₂ _ (by omega) (by omega) (by omega),
      q _ (by omega) (by omega), r78]
    have q64 : c₂.nreg 9764 = 1 := by rw [g₂ _ (by omega) (by omega) (by omega),
      q _ (by omega) (by omega), r64]
    exec_block
    all_goals try ((try config_simp); (try simp only [q78, q64]); omega)
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    · simp only [q78, q64]
    · simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, k₁ + (k₂ + k₃), e₁.seq (e₂.seq e₃), by omega, ?_, b78,
    fun r h1 h2 h3 h4 h5 h6 => by rw [g₃ r h3, g₂ r h1 h4 h5, q r h2 h6], by rw [m₃, m₂, m₁],
    by rw [rr₃, rr₂, rr₁], by rw [rm₃, rm₂, rm₁], by rw [o₃, o₂, o₁]⟩
  rw [g₃ _ (by omega), g₃ _ (by omega), g₃ _ (by omega)]; exact d₂

lemma dstep_cnt_le (i : ℕ) (s : ℕ × ℕ × ℕ) (x : ℕ) : (dstep i s x).2.1 ≤ s.2.1 + 1 := by
  unfold dstep; split_ifs <;> simp

lemma foldl_dstep_cnt_le (i : ℕ) : ∀ (L : List ℕ) (s : ℕ × ℕ × ℕ),
    (L.foldl (dstep i) s).2.1 ≤ s.2.1 + L.length
  | [], s => by simp
  | x :: L, s => by
    simp only [List.foldl_cons, List.length_cons]
    have := foldl_dstep_cnt_le i L (dstep i s x)
    have := dstep_cnt_le i s x
    omega

theorem hfScI_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W hfScI c c' k ∧ k = 4 ∧ c'.nreg 9778 = 0 ∧ c'.nreg 9779 = 0 ∧
      c'.nreg 9780 = 0 ∧ c'.nreg 9763 = 0 ∧
      (∀ r, r ≠ 9763 → r ≠ 9778 → r ≠ 9779 → r ≠ 9780 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hfScI
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

/-- **The scan.** -/
theorem hfScan_exec (c : Config) (hc : WordsBounded W c) {m Sb i : ℕ}
    (r57 : c.nreg 9757 = m) (r60 : c.nreg 9760 = Sb) (r64 : c.nreg 9764 = 1)
    (r59 : c.nreg 9759 = i) (w1 : Sb + m ≤ W) (w2 : m + 1 ≤ W) :
    ∃ c' k, Exec P W hfScan c c' k ∧ k ≤ 14 * m + 6 ∧
      c'.nreg 9763 = (dscan i (segL c.nmem Sb m)).2.2 ∧
      (∀ r, r ≠ 9763 → r ≠ 9775 → r ≠ 9778 → r ≠ 9779 → r ≠ 9780 → r ≠ 9781 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₀, k₀, e₀, hk₀, a78, a79, a80, a63, g₀, m₀, rr₀, rm₀, o₀⟩ := hfScI_exec (P := P) c hc
  have q : ∀ r, r ≠ 9763 → r ≠ 9778 → r ≠ 9779 → r ≠ 9780 → c₀.nreg r = c.nreg r := g₀
  let J : ℕ → Config → Prop := fun t c' =>
    (c'.nreg 9779, c'.nreg 9780, c'.nreg 9763) = (segL c.nmem Sb t).foldl (dstep i) (0, 0, 0) ∧
    (∀ r, r ≠ 9763 → r ≠ 9775 → r ≠ 9778 → r ≠ 9779 → r ≠ 9780 → r ≠ 9781 →
      c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hk₁, -, a₁, ⟨j1, j2, j3, j4, j5, j6⟩⟩ := lnRange (P := P) (a := 9778)
    (b := 9757) (body := hfScB) J (lo := 0) (hi := m) (B := 12) c₀ e₀.wb_right a78
    (by rw [q _ (by omega) (by omega) (by omega) (by omega), r57]) (Nat.zero_le m)
    ⟨by rw [a79, a80, a63, segL_zero]; rfl,
      fun r h1 h2 h3 h4 h5 h6 => q r h1 h3 h4 h5, m₀, rr₀, rm₀, o₀⟩
    (fun t c' _ ht hw e78 e57 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have hcnt : c'.nreg 9780 ≤ t := by
        have h := congrArg (fun s => s.2.1) j1
        simp only at h
        have := foldl_dstep_cnt_le i (segL c.nmem Sb t) (0, 0, 0)
        rw [segL_length] at this; simp only at this; omega
      obtain ⟨c'', k, ex, hk, d, b78, g, mm, rr, rm, oo⟩ := hfScB_exec (P := P) c' hw
        (Sb := Sb) (t := t) (i := i) (prev := c'.nreg 9779) (cnt := c'.nreg 9780)
        (v := c'.nreg 9763)
        (by rw [j2 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r60])
        (by rw [j2 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r64])
        e78 (by rw [j2 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r59])
        rfl rfl rfl (by omega) (by omega) (by omega)
      refine ⟨c'', k, ex, hk, b78, by
        rw [g _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact e57,
        ⟨?_, fun r h1 h2 h3 h4 h5 h6 => by rw [g r h1 h2 h3 h4 h5 h6, j2 r h1 h2 h3 h4 h5 h6],
          by rw [mm, j3], by rw [rr, j4], by rw [rm, j5], by rw [oo, j6]⟩⟩
      rw [d, segL_succ_right, List.foldl_append, ← j1, j3]
      rfl)
  refine ⟨c₁, k₀ + k₁, e₀.seq e₁, by omega, ?_, j2, j3, j4, j5, j6⟩
  have := congrArg (fun s => s.2.2) j1
  simp only at this
  rw [this]; rfl

/-! ### The flags -/

theorem hfFlag_exec (c : Config) (hc : WordsBounded W c) {m HLb Fb v : ℕ}
    (r57 : c.nreg 9757 = m) (r58 : c.nreg 9758 = HLb) (r62 : c.nreg 9762 = Fb)
    (r63 : c.nreg 9763 = v) (r64 : c.nreg 9764 = 1) (h1 : HLb + m ≤ Fb) (w1 : Fb + m ≤ W)
    (w2 : m + 1 ≤ W) :
    ∃ c' k, Exec P W hfFlag c c' k ∧ k ≤ 11 * m + 3 ∧
      (∀ t < m, c'.nmem (Fb + t) = if c.nmem (HLb + t) = v then 1 else 0) ∧
      (∀ a, (a < Fb ∨ Fb + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 9775 → r ≠ 9776 → r ≠ 9778 → r ≠ 9781 → r ≠ 9782 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₀, k₀, e₀, hk₀, a78, g₀, m₀, rr₀, rm₀, o₀⟩ : ∃ c₀ k₀, Exec P W
      (block [.constN 9778 0]) c c₀ k₀ ∧ k₀ = 1 ∧ c₀.nreg 9778 = 0 ∧
      (∀ r, r ≠ 9778 → c₀.nreg r = c.nreg r) ∧ c₀.nmem = c.nmem ∧
      c₀.rreg = c.rreg ∧ c₀.rmem = c.rmem ∧ c₀.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁, g₁, a₁, rr₁, rm₁, o₁⟩ := lnStore (P := P) (a := 9778)
    (b := 9757) (body := hfFlB) (Ob := Fb) (s := 1) (o := 0) (n := m) (B := 9) one_pos
    (fun t => hfFlagW (c.nmem (HLb + t)) v)
    (fun r => r ≠ 9775 ∧ r ≠ 9776 ∧ r ≠ 9778 ∧ r ≠ 9781 ∧ r ≠ 9782) c₀ e₀.wb_right a78
    (by rw [g₀ _ (by omega), r57]) (by omega)
    (fun t c' ht hw e78 hk hm => by
      obtain ⟨c'', k, ex, hk', m', b78, g', rr', rm', o'⟩ := hfFlB_exec (P := P) c' hw
        (HLb := HLb) (Fb := Fb) (v := v) (t := t)
        (by rw [hk _ (by omega), g₀ _ (by omega), r58])
        (by rw [hk _ (by omega), g₀ _ (by omega), r62])
        (by rw [hk _ (by omega), g₀ _ (by omega), r63])
        (by rw [hk _ (by omega), g₀ _ (by omega), r64]) e78 (by omega) (by omega) (by omega)
      refine ⟨c'', k, ex, by omega, b78, fun x hx => g' x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1
        hx.2.2.2.2, ?_, rr', rm', o'⟩
      rw [m', hm _ (fun j hj => by omega), m₀]
      simp only [one_mul, add_zero])
  refine ⟨c₁, k₀ + k₁, e₀.seq e₁, by omega, fun t ht => ?_, fun a ha => ?_,
    fun r h1 h2 h3 h4 h5 => ?_, by rw [rr₁, rr₀], by rw [rm₁, rm₀], by rw [o₁, o₀]⟩
  · have := v₁ t ht; simp only [one_mul, add_zero] at this; rw [this, hfFlagW_eq]
  · rw [f₁ a (fun j hj => by omega), m₀]
  · rw [g₁ r ⟨h1, h2, h3, h4, h5⟩, g₀ r h3]

/-! ### The program -/

/-- **The hole-flag program**: `F[t] = [HL[t] = hfV]` within `hfCost m` steps. -/
theorem hfP_exec (c : Config) (hc : WordsBounded W c) {m HLb i A B Fb : ℕ}
    (r57 : c.nreg 9757 = m) (r58 : c.nreg 9758 = HLb) (r59 : c.nreg 9759 = i)
    (r60 : c.nreg 9760 = A) (r61 : c.nreg 9761 = B) (r62 : c.nreg 9762 = Fb)
    (h1 : HLb + m ≤ A) (h2 : A + m ≤ B) (h3 : B + m ≤ Fb) (w1 : Fb + m ≤ W)
    (w2 : 3 * m + 1 ≤ W) :
    ∃ c' k, Exec P W hfP c c' k ∧ k ≤ hfCost m ∧ c'.nreg 9763 = hfV c.nmem HLb m i ∧
      (∀ t < m, c'.nmem (Fb + t) = if c.nmem (HLb + t) = hfV c.nmem HLb m i then 1 else 0) ∧
      (∀ a, (a < A ∨ Fb + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ HfScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a64, v₁, f₁, g₁, rr₁, rm₁, o₁⟩ :=
    hfCopy_exec (P := P) c hc r57 r58 r60 h1 (by omega) (by omega)
  have hseg₁ : segL c₁.nmem A m = segL c.nmem HLb m := by
    unfold segL; apply List.map_congr_left; intro t ht; exact v₁ t (List.mem_range.1 ht)
  obtain ⟨c₂, k₂, e₂, hk₂, s₂, b₂, f₂, g₂, rr₂, rm₂, o₂⟩ := hfSort_exec (P := P) c₁ e₁.wb_right
    (by rw [g₁ _ (by omega) (by omega) (by omega) (by omega), r57])
    (by rw [g₁ _ (by omega) (by omega) (by omega) (by omega), r60])
    (by rw [g₁ _ (by omega) (by omega) (by omega) (by omega), r61]) a64 h2 (by omega) w2
  obtain ⟨c₃, k₃, e₃, hk₃, a63, g₃, m₃, rr₃, rm₃, o₃⟩ := hfScan_exec (P := P) c₂ e₂.wb_right
    (m := m) (Sb := c₂.nreg 9760) (i := i)
    (by rw [g₂ _ (by omega), g₁ _ (by omega) (by omega) (by omega) (by omega), r57]) rfl
    (by rw [g₂ _ (by omega), a64])
    (by rw [g₂ _ (by omega), g₁ _ (by omega) (by omega) (by omega) (by omega), r59])
    (by omega) (by omega)
  have hv : c₃.nreg 9763 = hfV c.nmem HLb m i := by
    rw [a63, s₂, hseg₁]; rfl
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄, g₄, rr₄, rm₄, o₄⟩ := hfFlag_exec (P := P) c₃ e₃.wb_right
    (m := m) (HLb := HLb) (Fb := Fb) (v := hfV c.nmem HLb m i)
    (by rw [g₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      g₂ _ (by omega), g₁ _ (by omega) (by omega) (by omega) (by omega), r57])
    (by rw [g₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      g₂ _ (by omega), g₁ _ (by omega) (by omega) (by omega) (by omega), r58])
    (by rw [g₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      g₂ _ (by omega), g₁ _ (by omega) (by omega) (by omega) (by omega), r62]) hv
    (by rw [g₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      g₂ _ (by omega), a64]) (by omega) w1 (by omega)
  have hHL : ∀ t < m, c₃.nmem (HLb + t) = c.nmem (HLb + t) := fun t ht => by
    rw [m₃, f₂ _ (Or.inl (by omega)), f₁ _ (Or.inl (by omega))]
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), e₁.seq (e₂.seq (e₃.seq e₄)), ?_, ?_, fun t ht => ?_,
    fun a ha => ?_, fun r hr => ?_, by rw [rr₄, rr₃, rr₂, rr₁], by rw [rm₄, rm₃, rm₂, rm₁],
    by rw [o₄, o₃, o₂, o₁]⟩
  · unfold hfCost; omega
  · rw [g₄ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hv
  · rw [v₄ t ht, hHL t ht]
  · rw [f₄ a (by omega), m₃, f₂ a (by omega), f₁ a (by omega)]
  · unfold HfScr at hr
    rw [g₄ r (by omega) (by omega) (by omega) (by omega) (by omega),
      g₃ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      g₂ r (by omega), g₁ r (by omega) (by omega) (by omega) (by omega)]

end NcStep

end BKMNW

end PlanarFlow
