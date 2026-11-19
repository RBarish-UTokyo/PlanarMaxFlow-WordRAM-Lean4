module

public import PlanarFlow.BKMNW.MbRun

/-!
# Miller's base, step 3: copying the separator out, and the keys of the compacted darts

After `mbIn` (`MbRun.lean`) the separator found by `msep` is in the memory `[0, Wr]` read with
the memory above `Wr` as `0` (`mbCut Wr`): the `k = r641` dart codes from `r640`, the face marks
from `r642`. That area is restored afterwards (it holds the level data), so the separator is first
copied to the high area:

* `gcpLd`, `gcpBody`, **`gcp`** (`mem[Db + i] := mem[Sb + i]` if `Sb + i ≤ Wr`, else `0`, for
  `i < len`; the address is formed only when it is at most `Wr`), `gcpBody_exec`, **`gcp_exec`**
  (`8 len + 6` steps; registers `5100 = len`, `5101 = Sb`, `5102 = Db`, `5109 = Wr`, written
  `5103 … 5108`);
* `tksPut`, `tksBody`, **`tks`** (the scatter `D[K[i]] := S[i]` for the flagged `i < n`), used
  for the class keys of the compacted darts `TKc[RK[i]] := TK[i]`), `tksBody_exec`,
  **`tks_exec`** (`12 n + 5` steps; registers `5110 = n`, `5111 = NFb`, `5112 = Kb`,
  `5113 = Sb`, `5114 = Db`, written `5115 … 5120`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The guarded copy -/

/-- The load of the guarded copy: `v := mem[Sb + i]` if `i < lim = Wr + 1 - Sb`, else `0`. -/
def gcpLd : Stmt :=
  .ifLtN 5105 5103 (block [.addN 5106 5101 5105, .loadN 5107 5106]) (block [.constN 5107 0])

/-- One index of the guarded copy. -/
def gcpBody : Stmt :=
  .seq gcpLd (block [.addN 5106 5102 5105, .storeN 5106 5107, .addN 5105 5105 5104])

/-- **The guarded copy**: `mem[Db + i] := (mbCut Wr c).nmem (Sb + i)` for `i < len`. -/
def gcp : Stmt :=
  .seq (block [.constN 5104 1, .constN 5105 0, .addN 5108 5109 5104, .subN 5103 5108 5101])
    (.whileLtN 5105 5100 gcpBody)

section Gcp

variable {P : Input} {W : ℕ}

theorem gcpBody_exec (c : Config) (hc : WordsBounded W c) {Sb Db Wr i : ℕ}
    (r1 : c.nreg 5101 = Sb) (r2 : c.nreg 5102 = Db) (r3 : c.nreg 5103 = Wr + 1 - Sb)
    (r4 : c.nreg 5104 = 1) (r5 : c.nreg 5105 = i)
    (w1 : Wr + 1 ≤ W) (w2 : Db + i ≤ W) (w3 : i + 1 ≤ W) :
    ∃ c' t, Exec P W gcpBody c c' t ∧ t ≤ 6 ∧ c'.nreg 5105 = i + 1 ∧
      c'.nmem = upd c.nmem (Db + i) (if Sb + i ≤ Wr then c.nmem (Sb + i) else 0) ∧
      (∀ x, (x < 5105 ∨ 5107 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a7, an₁, am₁, ar₁, arm₁, ao₁⟩ : ∃ c₁ t₁, Exec P W gcpLd c c₁ t₁ ∧
      t₁ ≤ 3 ∧ c₁.nreg 5107 = (if Sb + i ≤ Wr then c.nmem (Sb + i) else 0) ∧
      (∀ x, (x < 5106 ∨ 5107 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    by_cases h : Sb + i ≤ Wr
    · have hlt : c.nreg 5105 < c.nreg 5103 := by rw [r5, r3]; omega
      obtain ⟨c₁, t₁, e₁, ht₁, b7, bn, bm, br, brm, bo⟩ : ∃ c₁ t₁,
          Exec P W (block [.addN 5106 5101 5105, .loadN 5107 5106]) c c₁ t₁ ∧ t₁ = 2 ∧
          c₁.nreg 5107 = c.nmem (Sb + i) ∧
          (∀ x, (x < 5106 ∨ 5107 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
          c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
        exec_block
        all_goals try (config_simp; simp only [r1, r5]; omega)
        refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; simp only [r1, r5]
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      exact ⟨c₁, t₁ + 1, .ifLtN_true hlt e₁, by omega, by rw [b7, iteT h], bn, bm, br, brm, bo⟩
    · have hlt : ¬ c.nreg 5105 < c.nreg 5103 := by rw [r5, r3]; omega
      obtain ⟨c₁, t₁, e₁, ht₁, b7, bn, bm, br, brm, bo⟩ : ∃ c₁ t₁,
          Exec P W (block [.constN 5107 0]) c c₁ t₁ ∧ t₁ = 1 ∧ c₁.nreg 5107 = 0 ∧
          (∀ x, (x < 5106 ∨ 5107 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
          c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
        exec_block
        all_goals try (config_simp; omega)
        refine ⟨rfl, by config_simp, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      exact ⟨c₁, t₁ + 2, .ifLtN_false hlt e₁, by omega, by rw [b7, iteF h], bn, bm, br, brm, bo⟩
  have hw₁ := e₁.wb_right
  have k2 : c₁.nreg 5102 = Db := by rw [an₁ _ (by omega), r2]
  have k4 : c₁.nreg 5104 = 1 := by rw [an₁ _ (by omega), r4]
  have k5 : c₁.nreg 5105 = i := by rw [an₁ _ (by omega), r5]
  obtain ⟨c₂, t₂, e₂, ht₂, d5, dm, dn, dr, drm, do'⟩ : ∃ c₂ t₂,
      Exec P W (block [.addN 5106 5102 5105, .storeN 5106 5107, .addN 5105 5105 5104]) c₁ c₂ t₂ ∧
      t₂ = 3 ∧ c₂.nreg 5105 = i + 1 ∧ c₂.nmem = upd c₁.nmem (Db + i) (c₁.nreg 5107) ∧
      (∀ x, (x < 5105 ∨ 5106 < x) → c₂.nreg x = c₁.nreg x) ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    exec_block
    all_goals try (config_simp; simp only [k2, k4, k5]; omega)
    refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [k4, k5]
    · config_simp; simp only [k2, k5]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, d5, by rw [dm, am₁, a7], fun x hx => ?_,
    by rw [dr, ar₁], by rw [drm, arm₁], by rw [do', ao₁]⟩
  rw [dn x (by omega), an₁ x (by omega)]

/-- **The guarded copy**: with `Wr < Db`, within `8 len + 6` steps
`mem[Db + i] = mem[Sb + i]` if `Sb + i ≤ Wr` and `0` otherwise (`i < len`); memory outside
`[Db, Db + len)`, registers outside `5103 … 5108`, reals and output kept. -/
theorem gcp_exec (c : Config) (hc : WordsBounded W c) {len Sb Db Wr : ℕ}
    (r0 : c.nreg 5100 = len) (r1 : c.nreg 5101 = Sb) (r2 : c.nreg 5102 = Db)
    (r9 : c.nreg 5109 = Wr) (hD : Wr < Db) (w1 : Db + len ≤ W) (w2 : Wr + 1 ≤ W)
    (w3 : len + 1 ≤ W) :
    ∃ c' t, Exec P W gcp c c' t ∧ t ≤ 8 * len + 6 ∧
      (∀ i < len, c'.nmem (Db + i) = if Sb + i ≤ Wr then c.nmem (Sb + i) else 0) ∧
      (∀ a, (a < Db ∨ Db + len ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5103 ∨ 5108 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold gcp
  obtain ⟨c₁, k₁, e₁, hk₁, g3, g4, g5, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 5104 1, .constN 5105 0, .addN 5108 5109 5104,
        .subN 5103 5108 5101]) c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg 5103 = Wr + 1 - Sb ∧ c₁.nreg 5104 = 1 ∧ c₁.nreg 5105 = 0 ∧
      (∀ x, (x < 5103 ∨ 5108 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; (try simp only [r1, r9]); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; (try simp only [r1, r9]); done)
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 5103 ∨ 5108 < x) → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 5105 ∨ 5107 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (Db + j) = if Sb + j ≤ Wr then m₀ (Sb + j) else 0) ∧
    (∀ a, (a < Db ∨ Db + len ≤ a) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h05, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 5105) (b := 5100) (body := gcpBody) J (B := 6) c₁ hw₁ g5
    (by rw [q _ (by omega), r0]) (Nat.zero_le len)
    ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega), fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h05 h00 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 5105 ∨ 5107 < x) → c'.nreg x = c₁.nreg x := j1
      obtain ⟨c'', t, ex, ht, h05', hm', hn', hr', hrm', ho'⟩ :=
        gcpBody_exec (P := P) c' hw (Sb := Sb) (Db := Db) (Wr := Wr)
          (by rw [f _ (by omega), q _ (by omega), r1]) (by rw [f _ (by omega), q _ (by omega), r2])
          (by rw [f _ (by omega), g3]) (by rw [f _ (by omega), g4]) h05 w2 (by omega) (by omega)
      refine ⟨c'', t, ex, ht, h05', by rw [hn' _ (by omega)]; exact h00,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same]
          split_ifs with h
          · exact j3 _ (Or.inl (by omega))
          · rfl
      · rw [hm', upd_other _ _ _ (by omega)]; exact j3 a ha)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3,
    fun x hx => by rw [j1 x (by omega), q x (by omega)], by rw [j4, gr₁], by rw [j5, grm₁],
    by rw [j6, go₁]⟩

end Gcp

/-! ### The scatter of the flagged indices -/

/-- The write of a flagged index: `D[K[i]] := S[i]`. -/
def tksPut : Stmt :=
  block [.addN 5119 5112 5116, .loadN 5119 5119, .addN 5120 5113 5116, .loadN 5120 5120,
    .addN 5119 5114 5119, .storeN 5119 5120]

/-- One index of the scatter (`5115 = 1`, `5116 = i`, `5117 = 0`). -/
def tksBody : Stmt :=
  .seq (block [.addN 5118 5111 5116, .loadN 5118 5118])
    (.seq (.ifLtN 5117 5118 tksPut .skip) (block [.addN 5116 5116 5115]))

/-- **The scatter**: `D[K[i]] := S[i]` for the `i < n` with `F[i] ≠ 0`. -/
def tks : Stmt :=
  .seq (block [.constN 5115 1, .constN 5116 0, .constN 5117 0]) (.whileLtN 5116 5110 tksBody)

section Tks

variable {P : Input} {W : ℕ}

theorem tksBody_exec (c : Config) (hc : WordsBounded W c) {NFb Kb Sb Db i : ℕ}
    (r1 : c.nreg 5111 = NFb) (r2 : c.nreg 5112 = Kb) (r3 : c.nreg 5113 = Sb)
    (r4 : c.nreg 5114 = Db) (r5 : c.nreg 5115 = 1) (r6 : c.nreg 5116 = i) (r7 : c.nreg 5117 = 0)
    (w1 : NFb + i ≤ W) (w2 : Kb + i ≤ W) (w3 : Sb + i ≤ W)
    (w4 : c.nmem (NFb + i) ≠ 0 → Db + c.nmem (Kb + i) ≤ W) (w5 : i + 1 ≤ W) :
    ∃ c' t, Exec P W tksBody c c' t ∧ t ≤ 10 ∧ c'.nreg 5116 = i + 1 ∧
      c'.nmem = (if c.nmem (NFb + i) ≠ 0 then
        upd c.nmem (Db + c.nmem (Kb + i)) (c.nmem (Sb + i)) else c.nmem) ∧
      (∀ x, (x < 5116 ∨ x = 5117 ∨ 5120 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a8, an₁, am₁, ar₁, arm₁, ao₁⟩ : ∃ c₁ t₁,
      Exec P W (block [.addN 5118 5111 5116, .loadN 5118 5118]) c c₁ t₁ ∧ t₁ = 2 ∧
      c₁.nreg 5118 = c.nmem (NFb + i) ∧
      (∀ x, x ≠ 5118 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; simp only [r1, r6]; omega)
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r1, r6]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have k : ∀ x, x ≠ 5118 → c₁.nreg x = c.nreg x := an₁
  obtain ⟨c₂, t₂, e₂, ht₂, bm₂, bn₂, br₂, brm₂, bo₂⟩ : ∃ c₂ t₂,
      Exec P W (.ifLtN 5117 5118 tksPut .skip) c₁ c₂ t₂ ∧ t₂ ≤ 7 ∧
      (c₂.nmem = if c.nmem (NFb + i) ≠ 0 then
        upd c.nmem (Db + c.nmem (Kb + i)) (c.nmem (Sb + i)) else c.nmem) ∧
      (∀ x, (x < 5119 ∨ 5120 < x) → c₂.nreg x = c₁.nreg x) ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    by_cases h : c.nmem (NFb + i) ≠ 0
    · have hlt : c₁.nreg 5117 < c₁.nreg 5118 := by rw [k _ (by omega), r7, a8]; omega
      have k2 : c₁.nreg 5112 = Kb := by rw [k _ (by omega), r2]
      have k3 : c₁.nreg 5113 = Sb := by rw [k _ (by omega), r3]
      have k4 : c₁.nreg 5114 = Db := by rw [k _ (by omega), r4]
      have k6 : c₁.nreg 5116 = i := by rw [k _ (by omega), r6]
      have w4' := w4 h
      obtain ⟨c₂, t₂, e₂, ht₂, pm, pn, pr, prm, po⟩ : ∃ c₂ t₂, Exec P W tksPut c₁ c₂ t₂ ∧
          t₂ = 6 ∧ c₂.nmem = upd c.nmem (Db + c.nmem (Kb + i)) (c.nmem (Sb + i)) ∧
          (∀ x, (x < 5119 ∨ 5120 < x) → c₂.nreg x = c₁.nreg x) ∧
          c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
        unfold tksPut
        exec_block
        all_goals try (config_simp; simp only [k2, k3, k4, k6, am₁]; omega)
        refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
        · config_simp; simp only [k2, k3, k4, k6, am₁]
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      exact ⟨c₂, t₂ + 1, .ifLtN_true hlt e₂, by omega, by rw [pm, iteT h], pn, pr, prm, po⟩
    · have hlt : ¬ c₁.nreg 5117 < c₁.nreg 5118 := by rw [k _ (by omega), r7, a8]; omega
      exact ⟨c₁, 0 + 2, .ifLtN_false hlt (.skip hw₁), by omega, by rw [am₁, iteF h],
        fun _ _ => rfl, rfl, rfl, rfl⟩
  have hw₂ := e₂.wb_right
  have h16 : c₂.nreg 5116 = i := by rw [bn₂ _ (by omega), k _ (by omega), r6]
  have h15 : c₂.nreg 5115 = 1 := by rw [bn₂ _ (by omega), k _ (by omega), r5]
  obtain ⟨c₃, t₃, e₃, ht₃, d16, dn₃, dm₃, dr₃, drm₃, do₃⟩ : ∃ c₃ t₃,
      Exec P W (block [.addN 5116 5116 5115]) c₂ c₃ t₃ ∧ t₃ = 1 ∧ c₃.nreg 5116 = i + 1 ∧
      (∀ x, x ≠ 5116 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try (config_simp; simp only [h16, h15]; omega)
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [h16, h15]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, d16, by rw [dm₃, bm₂],
    fun x hx => ?_, by rw [dr₃, br₂, ar₁], by rw [drm₃, brm₂, arm₁], by rw [do₃, bo₂, ao₁]⟩
  rw [dn₃ _ (by omega), bn₂ _ (by omega), k _ (by omega)]

/-- **The scatter**: with the arrays `F`, `K`, `S` below `Db`, `K` injective on the flagged
indices with values `< m`, within `12 n + 5` steps `D[K[i]] = S[i]` for every flagged `i < n`;
memory outside `[Db, Db + m)`, registers outside `5115 … 5120`, reals and output kept. -/
theorem tks_exec (c : Config) (hc : WordsBounded W c) {n m NFb Kb Sb Db : ℕ}
    (r0 : c.nreg 5110 = n) (r1 : c.nreg 5111 = NFb) (r2 : c.nreg 5112 = Kb)
    (r3 : c.nreg 5113 = Sb) (r4 : c.nreg 5114 = Db)
    (lay : NFb + n ≤ Db ∧ Kb + n ≤ Db ∧ Sb + n ≤ Db ∧ Db + m ≤ W ∧ n + 1 ≤ W)
    (hK : ∀ i < n, c.nmem (NFb + i) ≠ 0 → c.nmem (Kb + i) < m)
    (hinj : ∀ i < n, ∀ j < n, c.nmem (NFb + i) ≠ 0 → c.nmem (NFb + j) ≠ 0 →
      c.nmem (Kb + i) = c.nmem (Kb + j) → i = j) :
    ∃ c' t, Exec P W tks c c' t ∧ t ≤ 12 * n + 5 ∧
      (∀ i < n, c.nmem (NFb + i) ≠ 0 → c'.nmem (Db + c.nmem (Kb + i)) = c.nmem (Sb + i)) ∧
      (∀ a, (a < Db ∨ Db + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5115 ∨ 5120 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := lay
  unfold tks
  obtain ⟨c₁, k₁, e₁, hk₁, g5, g6, g7, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 5115 1, .constN 5116 0, .constN 5117 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 5115 = 1 ∧ c₁.nreg 5116 = 0 ∧ c₁.nreg 5117 = 0 ∧
      (∀ x, (x < 5115 ∨ 5117 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    obtain ⟨a1, a2, a3⟩ : x ≠ 5115 ∧ x ≠ 5116 ∧ x ≠ 5117 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3]
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 5115 ∨ 5117 < x) → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 5116 ∨ x = 5117 ∨ 5120 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, m₀ (NFb + j) ≠ 0 → c'.nmem (Db + m₀ (Kb + j)) = m₀ (Sb + j)) ∧
    (∀ a, (a < Db ∨ Db + m ≤ a) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h16, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 5116) (b := 5110) (body := tksBody) J (B := 10) c₁ hw₁ g6
    (by rw [q _ (by omega), r0]) (Nat.zero_le n)
    ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega), fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h16 h10 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 5116 ∨ x = 5117 ∨ 5120 < x) → c'.nreg x = c₁.nreg x := j1
      have eF : c'.nmem (NFb + i) = m₀ (NFb + i) := j3 _ (Or.inl (by omega))
      have eK : c'.nmem (Kb + i) = m₀ (Kb + i) := j3 _ (Or.inl (by omega))
      have eS : c'.nmem (Sb + i) = m₀ (Sb + i) := j3 _ (Or.inl (by omega))
      obtain ⟨c'', t, ex, ht, h16', hm', hn', hr', hrm', ho'⟩ :=
        tksBody_exec (P := P) c' hw (NFb := NFb) (Kb := Kb) (Sb := Sb) (Db := Db)
          (by rw [f _ (by omega), q _ (by omega), r1]) (by rw [f _ (by omega), q _ (by omega), r2])
          (by rw [f _ (by omega), q _ (by omega), r3]) (by rw [f _ (by omega), q _ (by omega), r4])
          (by rw [f _ (by omega), g5]) h16 (by rw [f _ (by omega), g7]) (by omega) (by omega)
          (by omega) (fun h => by
            have h' : m₀ (NFb + i) ≠ 0 := by rw [← eF]; exact h
            have h2 : m₀ (Kb + i) < m := hK i hhi h'
            rw [eK]; omega)
          (by omega)
      refine ⟨c'', t, ex, ht, h16', by rw [hn' _ (by omega)]; exact h10,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj hjF => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm', eF, eK, eS]
        split_ifs with hF
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · have hne : m₀ (Kb + j) ≠ m₀ (Kb + i) := fun h =>
              absurd (hinj j (by omega) i hhi hjF hF h) (by omega)
            rw [upd_other _ _ _ (by omega)]; exact j2 j hj hjF
          · rw [upd_same]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact j2 j hj hjF
          · exact absurd hjF hF
      · rw [hm', eF, eK]
        split_ifs with hF
        · have := hK i hhi hF
          rw [upd_other _ _ _ (by omega)]; exact j3 a ha
        · exact j3 a ha)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3,
    fun x hx => by rw [j1 x (by omega), q x (by omega)], by rw [j4, gr₁], by rw [j5, grm₁],
    by rw [j6, go₁]⟩

end Tks

end BKMNW

end PlanarFlow
