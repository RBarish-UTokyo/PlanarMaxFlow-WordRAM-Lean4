module

public import WordRAM.Programs.Tactics
public import PlanarFlow.BKMNW.IteR23

/-!
# Linear array loops for the bookkeeping of the max-flow recursion (`lin`)

Small natural-word loops over arrays of length `m`, used by the bookkeeping programs of the
max-flow recursion (`PlanarFlow/BKMNW/LinRet.lean`, `PlanarFlow/BKMNW/LinFlow.lean`). Each has its
own registers in the band `6210 … 6239`, so that they compose without clashes.

* `lnRange`: a `whileLtN` over `[lo, hi)` with a per-index invariant.
* **`lgProg`** (gather, `OUT[i] := A[IX[i]]`; registers `6210 = m`, `6211 = IXb`, `6212 = Ab`,
  `6213 = OUTb`; scratch `6214 … 6217`), `lgProg_exec` (`9 m + 4` steps).
* **`lsProg`** (conditional scatter, `OUT[IX[i]] := i` when `FL[i] < thr`; registers
  `6220 = m`, `6221 = IXb`, `6222 = FLb`, `6223 = thr`, `6224 = OUTb`; scratch `6225 … 6228`),
  `lsProg_exec` (`11 m + 4` steps; `IX` injective on the selected indices).
* **`lmProg`** (flag map, `OUT[i] := (1 - X[i]) - Y[i]`; registers `6230 = m`, `6231 = Xb`,
  `6232 = Yb`, `6233 = OUTb`; scratch `6234 … 6238`), `lmProg_exec` (`11 m + 4` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Exec

variable {P : Input} {W : ℕ}

/-- **A loop over `[lo, hi)`** with a per-index invariant. -/
theorem lnRange {a b : ℕ} {body : Stmt} (J : ℕ → Config → Prop) {lo hi B : ℕ} (c : Config)
    (hc : WordsBounded W c) (ha : c.nreg a = lo) (hb : c.nreg b = hi) (hle : lo ≤ hi)
    (hJ : J lo c)
    (hbody : ∀ i c, lo ≤ i → i < hi → WordsBounded W c → c.nreg a = i → c.nreg b = hi →
      J i c → ∃ c' k, Exec P W body c c' k ∧ k ≤ B ∧ c'.nreg a = i + 1 ∧ c'.nreg b = hi ∧
        J (i + 1) c') :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ k ≤ (B + 2) * (hi - lo) + 2 ∧
      WordsBounded W c' ∧ c'.nreg a = hi ∧ J hi c' := by
  obtain ⟨c', k, e, ⟨hw, h1, h2, h3, hJ'⟩, hn, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := a) (b := b) (body := body)
    (fun c => WordsBounded W c ∧ lo ≤ c.nreg a ∧ c.nreg a ≤ hi ∧ c.nreg b = hi ∧ J (c.nreg a) c)
    (fun c => (B + 2) * (hi - c.nreg a)) (fun c h => h.1)
    (fun c ⟨hw, h1, h2, h3, hJ⟩ hlt => by
      rw [h3] at hlt
      obtain ⟨c', k, e, hk, ha', hb', hJ'⟩ := hbody _ c h1 hlt hw rfl h3 hJ
      refine ⟨c', k, e, ⟨e.wb_right, by omega, by omega, hb', by rw [ha']; exact hJ'⟩, ?_⟩
      rw [ha']
      have : (B + 2) * (hi - (c.nreg a + 1)) + (B + 2) ≤ (B + 2) * (hi - c.nreg a) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      omega) ⟨hc, by omega, by omega, hb, by rw [ha]; exact hJ⟩
  have e' : c'.nreg a = hi := by omega
  refine ⟨c', k, e, by rw [ha] at hk; exact hk, hw, e', by rw [e'] at hJ'; exact hJ'⟩

/-! ### The gather -/

/-- `OUT[i] := A[IX[i]]`. -/
def lgBody : Stmt :=
  block [.addN 6216 6211 6215, .loadN 6216 6216, .addN 6216 6212 6216, .loadN 6216 6216,
    .addN 6217 6213 6215, .storeN 6217 6216, .addN 6215 6215 6214]

/-- **The gather** `OUT[i] := A[IX[i]]`, `i < m`. -/
def lgProg : Stmt :=
  .seq (block [.constN 6214 1, .constN 6215 0]) (.whileLtN 6215 6210 lgBody)

theorem lgBody_exec (c : Config) (hc : WordsBounded W c) {IXb Ab OUTb j : ℕ}
    (r1 : c.nreg 6211 = IXb) (r2 : c.nreg 6212 = Ab) (r3 : c.nreg 6213 = OUTb)
    (r4 : c.nreg 6214 = 1) (r5 : c.nreg 6215 = j) (w1 : IXb + j ≤ W)
    (w2 : Ab + c.nmem (IXb + j) ≤ W) (w3 : OUTb + j ≤ W) (w4 : j + 1 ≤ W) :
    ∃ c' k, Exec P W lgBody c c' k ∧ k = 7 ∧ c'.nreg 6215 = j + 1 ∧
      c'.nmem = upd c.nmem (OUTb + j) (c.nmem (Ab + c.nmem (IXb + j))) ∧
      (∀ x, (x < 6215 ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lgBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r4, r5]
  · config_simp; simp only [r1, r2, r3, r4, r5]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The gather**: within `9 m + 4` steps `OUT[i] = A[IX[i]]` for `i < m`; memory outside
`[OUTb, OUTb + m)`, registers outside `6214 … 6217`, reals and output kept. -/
theorem lgProg_exec (c : Config) (hc : WordsBounded W c) {m IXb Ab OUTb : ℕ}
    (r0 : c.nreg 6210 = m) (r1 : c.nreg 6211 = IXb) (r2 : c.nreg 6212 = Ab)
    (r3 : c.nreg 6213 = OUTb) (w1 : IXb + m ≤ W) (w3 : OUTb + m ≤ W) (w4 : m + 1 ≤ W)
    (hIX : ∀ j < m, Ab + c.nmem (IXb + j) ≤ W)
    (d1 : ∀ j < m, ¬ (OUTb ≤ IXb + j ∧ IXb + j < OUTb + m))
    (d2 : ∀ j < m, ¬ (OUTb ≤ Ab + c.nmem (IXb + j) ∧ Ab + c.nmem (IXb + j) < OUTb + m)) :
    ∃ c' k, Exec P W lgProg c c' k ∧ k ≤ 9 * m + 4 ∧
      (∀ j < m, c'.nmem (OUTb + j) = c.nmem (Ab + c.nmem (IXb + j))) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6214 ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lgProg
  obtain ⟨c₁, k₁, e₁, hk₁, g4, g5, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 6214 1, .constN 6215 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 6214 = 1 ∧ c₁.nreg 6215 = 0 ∧
      (∀ x, x ≠ 6214 → x ≠ 6215 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 6214 → x ≠ 6215 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 6215 ∨ 6217 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (OUTb + j) = m₀ (Ab + m₀ (IXb + j))) ∧
    (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h75, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 6215)
    (b := 6210) (body := lgBody) J (B := 7) c₁ hw₁ g5 (by rw [q _ (by omega) (by omega), r0])
    (Nat.zero_le m) ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h75 h70 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 6215 ∨ 6217 < x) → c'.nreg x = c₁.nreg x := j1
      have e1 : c'.nmem (IXb + i) = m₀ (IXb + i) :=
        j3 _ (fun h => d1 i hhi ⟨h.1, by omega⟩)
      have e2 : c'.nmem (Ab + m₀ (IXb + i)) = m₀ (Ab + m₀ (IXb + i)) :=
        j3 _ (fun h => d2 i hhi ⟨h.1, by omega⟩)
      obtain ⟨c'', t, ex, ht, h75', hm', hn', hr', hrm', ho'⟩ := lgBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r3])
        (by rw [f _ (by omega), g4]) h75 (by omega) (by rw [e1]; exact hIX i hhi) (by omega)
        (by omega)
      rw [e1, e2] at hm'
      refine ⟨c'', t, ex, ht.le, h75', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
        exact j3 a (fun h => ha ⟨h.1, by omega⟩))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, fun x hx => ?_, by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega)]

/-! ### The conditional scatter -/

/-- `if FL[i] < thr then OUT[IX[i]] := i`; then `i := i + 1`. -/
def lsBody : Stmt :=
  .seq (block [.addN 6227 6222 6226, .loadN 6228 6227])
    (.seq (.ifLtN 6228 6223
      (block [.addN 6227 6221 6226, .loadN 6227 6227, .addN 6227 6224 6227, .storeN 6227 6226])
      .skip)
      (block [.addN 6226 6226 6225]))

/-- **The conditional scatter** `OUT[IX[i]] := i` for the `i < m` with `FL[i] < thr`. -/
def lsProg : Stmt :=
  .seq (block [.constN 6225 1, .constN 6226 0]) (.whileLtN 6226 6220 lsBody)

theorem lsBody_exec (c : Config) (hc : WordsBounded W c) {IXb FLb thr OUTb j : ℕ}
    (r1 : c.nreg 6221 = IXb) (r2 : c.nreg 6222 = FLb) (r3 : c.nreg 6223 = thr)
    (r4 : c.nreg 6224 = OUTb) (r5 : c.nreg 6225 = 1) (r6 : c.nreg 6226 = j)
    (w1 : IXb + j ≤ W) (w2 : FLb + j ≤ W)
    (w3 : c.nmem (FLb + j) < thr → OUTb + c.nmem (IXb + j) ≤ W) (w4 : j + 1 ≤ W) :
    ∃ c' k, Exec P W lsBody c c' k ∧ k ≤ 9 ∧ c'.nreg 6226 = j + 1 ∧
      c'.nmem = (if c.nmem (FLb + j) < thr then upd c.nmem (OUTb + c.nmem (IXb + j)) j
        else c.nmem) ∧
      (∀ x, (x < 6226 ∨ 6228 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lsBody
  obtain ⟨c₁, k₁, e₁, hk₁, g8, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 6227 6222 6226, .loadN 6228 6227]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 6228 = c.nmem (FLb + j) ∧
      (∀ x, x ≠ 6227 → x ≠ 6228 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; simp only [r2, r6]; omega)
    refine ⟨rfl, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r2, r6]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q1 : ∀ x, x ≠ 6227 → x ≠ 6228 → c₁.nreg x = c.nreg x := gn₁
  -- the increment, from any configuration with the registers of `c₁`
  have inc : ∀ d : Config, WordsBounded W d → d.nreg 6226 = j → d.nreg 6225 = 1 →
      ∃ d' k, Exec P W (block [.addN 6226 6226 6225]) d d' k ∧ k = 1 ∧ d'.nreg 6226 = j + 1 ∧
        (∀ x, x ≠ 6226 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem ∧ d'.rreg = d.rreg ∧
        d'.rmem = d.rmem ∧ d'.output = d.output := fun d hd s6 s5 => by
    exec_block
    all_goals try (config_simp; simp only [s5, s6]; omega)
    refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [s5, s6]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  by_cases hs : c.nmem (FLb + j) < thr
  · obtain ⟨c₂, k₂, e₂, hk₂, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
        Exec P W (block [.addN 6227 6221 6226, .loadN 6227 6227, .addN 6227 6224 6227,
          .storeN 6227 6226]) c₁ c₂ k₂ ∧ k₂ = 4 ∧
        (∀ x, x ≠ 6227 → c₂.nreg x = c₁.nreg x) ∧
        c₂.nmem = upd c.nmem (OUTb + c.nmem (IXb + j)) j ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
      have s1 : c₁.nreg 6221 = IXb := by rw [q1 _ (by omega) (by omega), r1]
      have s4 : c₁.nreg 6224 = OUTb := by rw [q1 _ (by omega) (by omega), r4]
      have s6 : c₁.nreg 6226 = j := by rw [q1 _ (by omega) (by omega), r6]
      have w3' := w3 hs
      exec_block
      all_goals try (config_simp; simp only [s1, s4, s6, gm₁]; omega)
      refine ⟨rfl, fun x a => ?_, ?_, rfl, rfl, rfl⟩
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
      · config_simp; simp only [s1, s4, s6, gm₁]
    obtain ⟨c₃, k₃, e₃, hk₃, h6, gn₃, gm₃, gr₃, grm₃, go₃⟩ := inc c₂ e₂.wb_right
      (by rw [gn₂ _ (by omega), q1 _ (by omega) (by omega), r6])
      (by rw [gn₂ _ (by omega), q1 _ (by omega) (by omega), r5])
    have t3 : c₁.nreg 6228 < c₁.nreg 6223 := by
      rw [g8, q1 _ (by omega) (by omega), r3]; exact hs
    refine ⟨c₃, k₁ + (k₂ + 1 + k₃), .seq e₁ (.seq (.ifLtN_true t3 e₂) e₃), by omega, h6,
      by rw [gm₃, gm₂, iteT hs],
      fun x hx => ?_, by rw [gr₃, gr₂, gr₁], by rw [grm₃, grm₂, grm₁], by rw [go₃, go₂, go₁]⟩
    rw [gn₃ x (by omega), gn₂ x (by omega), q1 x (by omega) (by omega)]
  · obtain ⟨c₃, k₃, e₃, hk₃, h6, gn₃, gm₃, gr₃, grm₃, go₃⟩ := inc c₁ hw₁
      (by rw [q1 _ (by omega) (by omega), r6]) (by rw [q1 _ (by omega) (by omega), r5])
    have t3 : ¬ c₁.nreg 6228 < c₁.nreg 6223 := by
      rw [g8, q1 _ (by omega) (by omega), r3]; exact hs
    refine ⟨c₃, k₁ + (0 + 2 + k₃), .seq e₁ (.seq (.ifLtN_false t3 (.skip hw₁)) e₃), by omega,
      h6, by rw [gm₃, gm₁, iteF hs],
      fun x hx => ?_, by rw [gr₃, gr₁], by rw [grm₃, grm₁], by rw [go₃, go₁]⟩
    rw [gn₃ x (by omega), q1 x (by omega) (by omega)]

/-- **The conditional scatter**: with `IX` injective on the selected indices (`FL[i] < thr`) and
the output disjoint from `IX` and `FL`, within `11 m + 4` steps `OUT[IX[i]] = i` for every
selected `i < m`; the memory off the selected cells, registers outside `6225 … 6228`, reals and
output kept. -/
theorem lsProg_exec (c : Config) (hc : WordsBounded W c) {m IXb FLb thr OUTb : ℕ}
    (r0 : c.nreg 6220 = m) (r1 : c.nreg 6221 = IXb) (r2 : c.nreg 6222 = FLb)
    (r3 : c.nreg 6223 = thr) (r4 : c.nreg 6224 = OUTb)
    (w1 : IXb + m ≤ W) (w2 : FLb + m ≤ W) (w4 : m + 1 ≤ W)
    (hIX : ∀ j < m, c.nmem (FLb + j) < thr → OUTb + c.nmem (IXb + j) ≤ W)
    (hinj : ∀ i < m, ∀ j < m, c.nmem (FLb + i) < thr → c.nmem (FLb + j) < thr →
      c.nmem (IXb + i) = c.nmem (IXb + j) → i = j)
    (d1 : ∀ i < m, c.nmem (FLb + i) < thr → ∀ j < m, OUTb + c.nmem (IXb + i) ≠ IXb + j)
    (d2 : ∀ i < m, c.nmem (FLb + i) < thr → ∀ j < m, OUTb + c.nmem (IXb + i) ≠ FLb + j) :
    ∃ c' k, Exec P W lsProg c c' k ∧ k ≤ 11 * m + 4 ∧
      (∀ i < m, c.nmem (FLb + i) < thr → c'.nmem (OUTb + c.nmem (IXb + i)) = i) ∧
      (∀ a, (∀ i < m, c.nmem (FLb + i) < thr → a ≠ OUTb + c.nmem (IXb + i)) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6225 ∨ 6228 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lsProg
  obtain ⟨c₁, k₁, e₁, hk₁, g5, g6, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 6225 1, .constN 6226 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 6225 = 1 ∧ c₁.nreg 6226 = 0 ∧
      (∀ x, x ≠ 6225 → x ≠ 6226 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 6225 → x ≠ 6226 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 6226 ∨ 6228 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, m₀ (FLb + j) < thr → c'.nmem (OUTb + m₀ (IXb + j)) = j) ∧
    (∀ a, (∀ j < i, m₀ (FLb + j) < thr → a ≠ OUTb + m₀ (IXb + j)) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h76, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 6226)
    (b := 6220) (body := lsBody) J (B := 9) c₁ hw₁ g6 (by rw [q _ (by omega) (by omega), r0])
    (Nat.zero_le m) ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h76 h70 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 6226 ∨ 6228 < x) → c'.nreg x = c₁.nreg x := j1
      have e1 : c'.nmem (IXb + i) = m₀ (IXb + i) :=
        j3 _ (fun j hj hs h => d1 j (by omega) hs i hhi h.symm)
      have e2 : c'.nmem (FLb + i) = m₀ (FLb + i) :=
        j3 _ (fun j hj hs h => d2 j (by omega) hs i hhi h.symm)
      obtain ⟨c'', t, ex, ht, h76', hm', hn', hr', hrm', ho'⟩ := lsBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r3])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r4])
        (by rw [f _ (by omega), g5]) h76 (by omega) (by omega)
        (fun hs => by rw [e1]; rw [e2] at hs; exact hIX i hhi hs)
        (by omega)
      rw [e1, e2] at hm'
      refine ⟨c'', t, ex, ht, h76', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj hs => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · split_ifs with hsi
          · rw [upd_other _ _ _ (fun h => by
              have := hinj j (by omega) i hhi hs hsi (by omega); omega)]
            exact j2 j hj hs
          · exact j2 j hj hs
        · rw [iteT hs, upd_same]
      · rw [hm']
        have ha' : ∀ j < i, m₀ (FLb + j) < thr → a ≠ OUTb + m₀ (IXb + j) := fun j hj hs =>
          ha j (by omega) hs
        split_ifs with hsi
        · rw [upd_other _ _ _ (ha i (by omega) hsi)]; exact j3 a ha'
        · exact j3 a ha')
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fun i hi hs => j2 i hi hs, j3,
    fun x hx => ?_, by rw [j4, gr₁], by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega)]

/-! ### The flag map -/

/-- `OUT[i] := (1 - X[i]) - Y[i]` (truncated subtractions). -/
def lmBody : Stmt :=
  block [.addN 6236 6231 6235, .loadN 6236 6236, .subN 6237 6234 6236,
    .addN 6236 6232 6235, .loadN 6236 6236, .subN 6237 6237 6236,
    .addN 6238 6233 6235, .storeN 6238 6237, .addN 6235 6235 6234]

/-- **The flag map** `OUT[i] := (1 - X[i]) - Y[i]`, `i < m`. -/
def lmProg : Stmt :=
  .seq (block [.constN 6234 1, .constN 6235 0]) (.whileLtN 6235 6230 lmBody)

theorem lmBody_exec (c : Config) (hc : WordsBounded W c) {Xb Yb OUTb j : ℕ}
    (r1 : c.nreg 6231 = Xb) (r2 : c.nreg 6232 = Yb) (r3 : c.nreg 6233 = OUTb)
    (r4 : c.nreg 6234 = 1) (r5 : c.nreg 6235 = j) (w1 : Xb + j ≤ W) (w2 : Yb + j ≤ W)
    (w3 : OUTb + j ≤ W) (w4 : j + 1 ≤ W) :
    ∃ c' k, Exec P W lmBody c c' k ∧ k = 9 ∧ c'.nreg 6235 = j + 1 ∧
      c'.nmem = upd c.nmem (OUTb + j) (1 - c.nmem (Xb + j) - c.nmem (Yb + j)) ∧
      (∀ x, (x < 6235 ∨ 6238 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lmBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r4, r5]
  · config_simp; simp only [r1, r2, r3, r4, r5]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The flag map**: within `11 m + 4` steps `OUT[i] = (1 - X[i]) - Y[i]` for `i < m`; memory
outside `[OUTb, OUTb + m)`, registers outside `6234 … 6238`, reals and output kept. -/
theorem lmProg_exec (c : Config) (hc : WordsBounded W c) {m Xb Yb OUTb : ℕ}
    (r0 : c.nreg 6230 = m) (r1 : c.nreg 6231 = Xb) (r2 : c.nreg 6232 = Yb)
    (r3 : c.nreg 6233 = OUTb) (w1 : Xb + m ≤ W) (w2 : Yb + m ≤ W) (w3 : OUTb + m ≤ W)
    (w4 : m + 1 ≤ W)
    (d1 : ∀ j < m, ¬ (OUTb ≤ Xb + j ∧ Xb + j < OUTb + m))
    (d2 : ∀ j < m, ¬ (OUTb ≤ Yb + j ∧ Yb + j < OUTb + m)) :
    ∃ c' k, Exec P W lmProg c c' k ∧ k ≤ 11 * m + 4 ∧
      (∀ j < m, c'.nmem (OUTb + j) = 1 - c.nmem (Xb + j) - c.nmem (Yb + j)) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6234 ∨ 6238 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lmProg
  obtain ⟨c₁, k₁, e₁, hk₁, g4, g5, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 6234 1, .constN 6235 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 6234 = 1 ∧ c₁.nreg 6235 = 0 ∧
      (∀ x, x ≠ 6234 → x ≠ 6235 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 6234 → x ≠ 6235 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 6235 ∨ 6238 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (OUTb + j) = 1 - m₀ (Xb + j) - m₀ (Yb + j)) ∧
    (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h75, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 6235)
    (b := 6230) (body := lmBody) J (B := 9) c₁ hw₁ g5 (by rw [q _ (by omega) (by omega), r0])
    (Nat.zero_le m) ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h75 h70 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 6235 ∨ 6238 < x) → c'.nreg x = c₁.nreg x := j1
      have e1 : c'.nmem (Xb + i) = m₀ (Xb + i) := j3 _ (fun h => d1 i hhi ⟨h.1, by omega⟩)
      have e2 : c'.nmem (Yb + i) = m₀ (Yb + i) := j3 _ (fun h => d2 i hhi ⟨h.1, by omega⟩)
      obtain ⟨c'', t, ex, ht, h75', hm', hn', hr', hrm', ho'⟩ := lmBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r3])
        (by rw [f _ (by omega), g4]) h75 (by omega) (by omega) (by omega) (by omega)
      rw [e1, e2] at hm'
      refine ⟨c'', t, ex, ht.le, h75', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
        exact j3 a (fun h => ha ⟨h.1, by omega⟩))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, fun x hx => ?_, by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega)]

end Exec

end BKMNW

end PlanarFlow
