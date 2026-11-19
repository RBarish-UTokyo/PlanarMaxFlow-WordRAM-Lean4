module

public import PlanarFlow.BKMNW.NpNode

/-!
# `segP`: the parts of the separator at the node, by rerunning the separator

The node step needs the parts of the separator (`SegPSpec`, `NpNode.lean`). The node field of
the driver receives the extended frame (`FInLX`), so the separator program can be run again at
the node: **`segP sepX = sgA ; sepX ; sgB ; while (sum the lengths) ; sgC ; while (copy) ; sgD`**
(registers `8400 … 8413`):

* `sgA`: `b = r3006 - 5` (the node's heap top), `mem b := r3003` (saved), `r3003 := b`,
  `r6500 := b + 1` (the separator's output base `Sb = b + 1`);
* `sepX`: any program meeting **`SepPSpecXS`** (the separator with the parts `SegsOut` from
  `Gb = r6502`, `SepSegs.lean`);
* `sgB` + loop: `s = mem Gb`, `Σ k_j` (the lengths at `Gb + 1 + s + j`); `sgC`: the size
  `z = 1 + 2 s + Σ k_j`; loop: the block `[Gb, Gb + z)` copied down to `[b, b + z)` (forward:
  `b < Gb`); `sgD`: `r6807 := b`, `r6808 := b + 5`, `r3006 := b + z + 5`, `r3003` restored.

* `SegsOut.shift` (the parts' layout is translation invariant), **`segP_spec`**: `SepPSpecXS sepX
  sT sR` ⇒ `SegPSpec (segP sepX)` with steps **`sT n k + 13 sR n m k + 30`** and room
  **`1 + sR n m k`** (`n = #piece`, `m = #pdarts`, `k = #Hs`).
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

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs NegSSSP.Driver

universe w

/-! ### The program -/

/-- `b := r3006 - 5`, `mem b := r3003`, `r3003 := b`, `r6500 := b + 1`. -/
def sgA : Stmt :=
  block [.constN 8401 5, .subN 8400 3006 8401, .storeN 8400 3003, .copyN 3003 8400,
    .constN 8402 1, .addN 6500 8400 8402]

/-- `b`, the saved `h₀`, `Gb`, `s`, the base of the lengths, `sum := 0`, `j := 0`. -/
def sgB : Stmt :=
  block [.constN 8401 5, .subN 8400 3006 8401, .loadN 8403 8400, .copyN 8404 6502,
    .loadN 8405 8404, .constN 8402 1, .addN 8406 8404 8402, .addN 8406 8406 8405,
    .constN 8407 0, .constN 8408 0]

/-- `sum := sum + mem (KB + j)`; `j := j + 1`. -/
def npSgK : Stmt := block [.addN 8409 8406 8408, .loadN 8409 8409, .addN 8407 8407 8409,
  .addN 8408 8408 8402]

/-- `z := 2 s + sum + 1`, `j := 0`. -/
def sgC : Stmt := block [.addN 8410 8405 8405, .addN 8410 8410 8407, .addN 8410 8410 8402,
  .constN 8408 0]

/-- `mem (b + j) := mem (Gb + j)`; `j := j + 1`. -/
def sgM : Stmt := block [.addN 8411 8404 8408, .loadN 8411 8411, .addN 8412 8400 8408,
  .storeN 8412 8411, .addN 8408 8408 8402]

/-- `r6807 := b`, `r6808 := r3006`, `r3006 := b + z + 5`, `r3003 := h₀`. -/
def sgD : Stmt := block [.copyN 6807 8400, .copyN 6808 3006, .addN 8413 8400 8410,
  .addN 3006 8413 8401, .copyN 3003 8403]

/-- **The parts of the separator at the node.** -/
def segP (sepX : Stmt) : Stmt :=
  .seq sgA (.seq sepX (.seq sgB (.seq (.whileLtN 8408 8405 npSgK) (.seq sgC
    (.seq (.whileLtN 8408 8410 sgM) sgD)))))

/-! ### The blocks -/

section Blocks

variable {P : Input} {W : ℕ}

theorem sgA_exec (c : Config) (hc : WordsBounded W c) {b : ℕ} (r6 : c.nreg 3006 = b + 5)
    (w : b + 1 ≤ W) :
    ∃ c' t, Exec P W sgA c c' t ∧ t = 6 ∧ c'.nreg 3003 = b ∧ c'.nreg 6500 = b + 1 ∧
      c'.nmem = upd c.nmem b (c.nreg 3003) ∧
      (∀ x, x ≠ 3003 → x ≠ 6500 → (x < 8400 ∨ 8413 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h5 : b + 5 ≤ W := by rw [← r6]; exact WordsBounded.nreg hc 3006
  unfold sgA
  exec_block
  all_goals try (clear * - r6 w h5; config_simp; (try simp only [r6]); omega)
  all_goals try (clear * - w h5; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r6]
  all_goals try omega
  · simp only [r6, show b + 5 - 5 = b by omega]
  · simp only [upd_apply]; split_ifs <;> omega

theorem sgB_exec (c : Config) (hc : WordsBounded W c) {b : ℕ} (r6 : c.nreg 3006 = b + 5)
    (w1 : c.nreg 6502 + 1 + c.nmem (c.nreg 6502) ≤ W) :
    ∃ c' t, Exec P W sgB c c' t ∧ t = 10 ∧ c'.nreg 8400 = b ∧ c'.nreg 8401 = 5 ∧
      c'.nreg 8402 = 1 ∧ c'.nreg 8403 = c.nmem b ∧ c'.nreg 8404 = c.nreg 6502 ∧
      c'.nreg 8405 = c.nmem (c.nreg 6502) ∧
      c'.nreg 8406 = c.nreg 6502 + 1 + c.nmem (c.nreg 6502) ∧ c'.nreg 8407 = 0 ∧
      c'.nreg 8408 = 0 ∧ (∀ x, (x < 8400 ∨ 8413 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h5 : b + 5 ≤ W := by rw [← r6]; exact WordsBounded.nreg hc 3006
  unfold sgB
  exec_block
  all_goals try (clear * - r6 w1 h5; config_simp; (try simp only [r6]); omega)
  all_goals try (clear * - w1 h5; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r6, show b + 5 - 5 = b by omega]
  all_goals try omega
  · simp only [upd_apply]; split_ifs <;> omega

theorem sgK_exec (c : Config) (hc : WordsBounded W c) {KB j s : ℕ}
    (r6 : c.nreg 8406 = KB) (r8 : c.nreg 8408 = j) (r2 : c.nreg 8402 = 1)
    (r7 : c.nreg 8407 = s) (w1 : KB + j ≤ W) (w2 : s + c.nmem (KB + j) ≤ W) (w3 : j + 1 ≤ W) :
    ∃ c' t, Exec P W npSgK c c' t ∧ t = 4 ∧ c'.nreg 8408 = j + 1 ∧
      c'.nreg 8407 = s + c.nmem (KB + j) ∧
      (∀ x, x ≠ 8407 → x ≠ 8408 → x ≠ 8409 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold npSgK
  exec_block
  all_goals try (config_simp; simp only [r6, r8, r2, r7]; omega)
  refine ⟨rfl, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r8, r2]
  · config_simp; simp only [r6, r8, r7]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem sgC_exec (c : Config) (hc : WordsBounded W c) {s sum : ℕ}
    (r5 : c.nreg 8405 = s) (r7 : c.nreg 8407 = sum) (r2 : c.nreg 8402 = 1)
    (w : 2 * s + sum + 1 ≤ W) :
    ∃ c' t, Exec P W sgC c c' t ∧ t = 4 ∧ c'.nreg 8410 = 2 * s + sum + 1 ∧ c'.nreg 8408 = 0 ∧
      (∀ x, x ≠ 8408 → x ≠ 8410 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sgC
  exec_block
  all_goals try (config_simp; simp only [r5, r7, r2]; omega)
  all_goals try omega
  refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r5, r7, r2]; omega
  · config_simp
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem sgM_exec (c : Config) (hc : WordsBounded W c) {b Gb j : ℕ}
    (r0 : c.nreg 8400 = b) (r4 : c.nreg 8404 = Gb) (r8 : c.nreg 8408 = j)
    (r2 : c.nreg 8402 = 1) (w1 : Gb + j ≤ W) (w2 : b + j ≤ W) (w3 : j + 1 ≤ W) :
    ∃ c' t, Exec P W sgM c c' t ∧ t = 5 ∧ c'.nreg 8408 = j + 1 ∧
      c'.nmem = upd c.nmem (b + j) (c.nmem (Gb + j)) ∧
      (∀ x, x ≠ 8408 → x ≠ 8411 → x ≠ 8412 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sgM
  exec_block
  all_goals try (config_simp; simp only [r0, r4, r8, r2]; omega)
  refine ⟨rfl, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r8, r2]
  · config_simp; simp only [r0, r4, r8]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem sgD_exec (c : Config) (hc : WordsBounded W c) {b z h₀ : ℕ}
    (r0 : c.nreg 8400 = b) (r10 : c.nreg 8410 = z) (r1 : c.nreg 8401 = 5)
    (r3 : c.nreg 8403 = h₀) (w : b + z + 5 ≤ W) :
    ∃ c' t, Exec P W sgD c c' t ∧ t = 5 ∧ c'.nreg 6807 = b ∧ c'.nreg 6808 = c.nreg 3006 ∧
      c'.nreg 3006 = b + z + 5 ∧ c'.nreg 3003 = h₀ ∧
      (∀ x, x ≠ 6807 → x ≠ 6808 → x ≠ 3006 → x ≠ 3003 → x ≠ 8413 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sgD
  exec_block
  all_goals try (config_simp; simp only [r0, r10, r1, r3]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r0, r10, r1, r3]
  · simp only [upd_apply]; split_ifs <;> omega

end Blocks

/-! ### The loops -/

section Loops

variable {P : Input} {W : ℕ}

/-- **The sum of the lengths** `Σ_{j < s} mem (KB + j)`. -/
theorem sgKL_exec (c : Config) (hc : WordsBounded W c) {KB s : ℕ} (f : ℕ → ℕ)
    (r6 : c.nreg 8406 = KB) (r8 : c.nreg 8408 = 0) (r5 : c.nreg 8405 = s) (r2 : c.nreg 8402 = 1)
    (r7 : c.nreg 8407 = 0) (w1 : KB + s ≤ W) (hf : ∀ j < s, c.nmem (KB + j) = f j)
    (w2 : ∑ j ∈ range s, f j ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 8408 8405 npSgK) c c' t ∧ t ≤ 6 * s + 2 ∧
      c'.nreg 8407 = ∑ j ∈ range s, f j ∧
      (∀ x, x ≠ 8407 → x ≠ 8408 → x ≠ 8409 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hmono : ∀ i ≤ s, ∑ j ∈ range i, f j ≤ ∑ j ∈ range s, f j := fun i hi =>
    sum_le_sum_of_subset (range_subset_range.2 hi)
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, x ≠ 8407 → x ≠ 8408 → x ≠ 8409 → c'.nreg x = c.nreg x) ∧
    c'.nreg 8407 = ∑ j ∈ range i, f j ∧
    c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', t, ex, ht, -, -, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 8408) (b := 8405)
    (body := npSgK) J (B := 4) c hc r8 r5 (Nat.zero_le _)
    ⟨fun _ _ _ _ => rfl, by rw [r7]; simp, rfl, rfl, rfl, rfl⟩
    (fun i c₁ _ hi hw h8 h5 ⟨f₁, s₁, m₁, q1, q2, q3⟩ => by
      have hs := hmono (i + 1) hi
      rw [sum_range_succ] at hs
      obtain ⟨c₂, t₂, e₂, ht₂, g8, g7, gn, gm, gr, grm, go⟩ := sgK_exec (P := P) c₁ hw
        (by rw [f₁ _ (by omega) (by omega) (by omega), r6]) h8
        (by rw [f₁ _ (by omega) (by omega) (by omega), r2]) s₁ (by omega)
        (by rw [m₁, hf i hi]; omega) (by omega)
      refine ⟨c₂, t₂, e₂, ht₂.le, g8, by rw [gn _ (by omega) (by omega) (by omega)]; exact h5,
        fun x h1 h2 h3 => by rw [gn x h1 h2 h3, f₁ x h1 h2 h3], ?_, by rw [gm, m₁],
        by rw [gr, q1], by rw [grm, q2], by rw [go, q3]⟩
      rw [g7, m₁, hf i hi, sum_range_succ])
  exact ⟨c', t, ex, by omega, j2, j1, j3, j4, j5, j6⟩

/-- **The copy** `[Gb, Gb + z) → [b, b + z)`, `b < Gb` (forward). -/
theorem sgML_exec (c : Config) (hc : WordsBounded W c) {b Gb z : ℕ}
    (r0 : c.nreg 8400 = b) (r4 : c.nreg 8404 = Gb) (r8 : c.nreg 8408 = 0)
    (r10 : c.nreg 8410 = z) (r2 : c.nreg 8402 = 1) (hbG : b < Gb) (w1 : Gb + z ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 8408 8410 sgM) c c' t ∧ t ≤ 7 * z + 2 ∧
      (∀ a < z, c'.nmem (b + a) = c.nmem (Gb + a)) ∧
      (∀ a, ¬ (b ≤ a ∧ a < b + z) → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 8408 → x ≠ 8411 → x ≠ 8412 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, x ≠ 8408 → x ≠ 8411 → x ≠ 8412 → c'.nreg x = c.nreg x) ∧
    (∀ a < i, c'.nmem (b + a) = c.nmem (Gb + a)) ∧
    (∀ a, ¬ (b ≤ a ∧ a < b + i) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', t, ex, ht, -, -, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 8408) (b := 8410)
    (body := sgM) J (B := 5) c hc r8 r10 (Nat.zero_le _)
    ⟨fun _ _ _ _ => rfl, fun a ha => absurd ha (by omega), fun _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c₁ _ hi hw h8 h10 ⟨f₁, z₁, o₁, q1, q2, q3⟩ => by
      have e1 : c₁.nmem (Gb + i) = c.nmem (Gb + i) := o₁ _ (fun h => by omega)
      obtain ⟨c₂, t₂, e₂, ht₂, g8, gm, gn, gr, grm, go⟩ := sgM_exec (P := P) c₁ hw
        (by rw [f₁ _ (by omega) (by omega) (by omega), r0])
        (by rw [f₁ _ (by omega) (by omega) (by omega), r4]) h8
        (by rw [f₁ _ (by omega) (by omega) (by omega), r2]) (by omega) (by omega) (by omega)
      rw [e1] at gm
      refine ⟨c₂, t₂, e₂, ht₂.le, g8, by rw [gn _ (by omega) (by omega) (by omega)]; exact h10,
        fun x h1 h2 h3 => by rw [gn x h1 h2 h3, f₁ x h1 h2 h3], fun a ha => ?_, fun a ha => ?_,
        by rw [gr, q1], by rw [grm, q2], by rw [go, q3]⟩
      · rw [gm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
        · rw [upd_other _ _ _ (by omega)]; exact z₁ a ha
        · rw [upd_same]
      · rw [gm, upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
        exact o₁ a (fun h => ha ⟨h.1, by omega⟩))
  exact ⟨c', t, ex, by omega, j2, j3, j1, j4, j5, j6⟩

end Loops

/-! ### The layout of the parts is translation invariant -/

section Shift

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

lemma sum_take_add_getElem (L : List (SPath M)) {j : ℕ} (hj : j < L.length) :
    ((L.take j).map SPath.k).sum + (L[j]).k ≤ (L.map SPath.k).sum := by
  have e : L.take (j + 1) = L.take j ++ [L[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  have := sum_take_le_sum (L.map SPath.k) (j + 1)
  rw [← List.map_take, e, List.map_append, List.sum_append] at this
  simpa using this

lemma sum_take_succ (L : List (SPath M)) {j : ℕ} (hj : j < L.length) :
    ((L.take (j + 1)).map SPath.k).sum = ((L.take j).map SPath.k).sum + (L[j]).k := by
  have e : L.take (j + 1) = L.take j ++ [L[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  rw [e, List.map_append, List.sum_append]; simp

/-- **The layout of the parts is translation invariant.** -/
lemma SegsOut.shift {en : ℕ → D} {m : ℕ} {π : HSep M} {lo hi Gb lo' hi' b : ℕ}
    {mem mem' : ℕ → ℕ} (h : SegsOut M en m π lo hi Gb mem)
    (hz : ∀ a < 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum, mem' (b + a) = mem (Gb + a))
    (hlo : lo' ≤ b) (hhi : b + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum ≤ hi') :
    SegsOut M en m π lo' hi' b mem' := by
  obtain ⟨-, h2, -, h4⟩ := h
  refine ⟨hlo, ?_, hhi, fun j hj => ?_⟩
  · have := hz 0 (by omega)
    rw [Nat.add_zero, Nat.add_zero] at this
    rw [this]; exact h2
  obtain ⟨g1, g2, g3⟩ := h4 j hj
  have hk := sum_take_add_getElem π.segs hj
  refine ⟨?_, ?_, fun l hl => ?_⟩
  · rw [show b + 1 + j = b + (1 + j) by omega, hz _ (by omega),
      show Gb + (1 + j) = Gb + 1 + j by omega]
    exact g1
  · rw [show b + 1 + π.segs.length + j = b + (1 + π.segs.length + j) by omega,
      hz _ (by omega), show Gb + (1 + π.segs.length + j) = Gb + 1 + π.segs.length + j by omega]
    exact g2
  · have e : mem' (b + 1 + 2 * π.segs.length + ((π.segs.take j).map SPath.k).sum + l) =
        mem (Gb + 1 + 2 * π.segs.length + ((π.segs.take j).map SPath.k).sum + l) := by
      rw [show b + 1 + 2 * π.segs.length + ((π.segs.take j).map SPath.k).sum + l =
        b + (1 + 2 * π.segs.length + ((π.segs.take j).map SPath.k).sum + l) by omega,
        hz _ (by omega)]
      congr 1; omega
    rw [e]
    exact g3 l hl

end Shift

/-! ### The specification -/

section Spec

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {ds : DSys M} {Reach : MCall M → Prop} {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ}
  {S T : Finset V} {Z : ℕ} {I : Input} {W : ℕ} {sepX : Stmt} {sT : ℕ → ℕ → ℕ}
  {sR : ℕ → ℕ → ℕ → ℕ}

variable (M) in
/-- The steps of `segP` at a call: the separator's, plus `13 sR + 30` (the copy). -/
noncomputable def segT (sT : ℕ → ℕ → ℕ) (sR : ℕ → ℕ → ℕ → ℕ) (x : MCall M) : ℕ :=
  sT x.1.piece.card x.2.1.length +
    13 * sR x.1.piece.card (pdarts M x.1.piece x.2.1).card x.2.1.length + 30

variable (M) in
/-- The room of `segP` at a call: `1 + sR`. -/
noncomputable def segR (sR : ℕ → ℕ → ℕ → ℕ) (x : MCall M) : ℕ :=
  1 + sR x.1.piece.card (pdarts M x.1.piece x.2.1).card x.2.1.length

/-- **`segP` meets `SegPSpec`**, from the separator's specification with the parts. -/
lemma sum_range_getD (L : List ℕ) : ∑ j ∈ range L.length, L.getD j 0 = L.sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.sum_cons]
    omega

theorem segP_spec (hsep : SepPSpecXS M ds Reach gid ν u S T Z I W sepX sT sR) :
    SegPSpec M ds Reach gid ν u S T Z I W (segP sepX) (segT M sT sR) (segR M sR) := by
  intro l r π Hs σ d e b m en c hin hL hde heb hroom hc r4 r5 r6
  have hcard : m = (pdarts M (l.piece ∪ r.piece) Hs).card := hL.card
  have hroom' : b + 1 + sR (l.piece ∪ r.piece).card m Hs.length ≤ W := by
    have : segR M sR (.node l r π, Hs, σ) = 1 + sR (l.piece ∪ r.piece).card m Hs.length := by
      unfold segR; simp only [ADec.piece]; rw [← hcard]
    rw [this] at hroom; omega
  unfold fsz at hde
  -- the set-up
  obtain ⟨c₁, t₁, e₁, ht₁, a3, a65, m₁, f₁, rr₁, rm₁, o₁⟩ :=
    sgA_exec (P := I) c hc r6 (by omega)
  have hmem₁ : ∀ a, a ≠ b → c₁.nmem a = c.nmem a := fun a ha => by
    rw [m₁, upd_other _ _ _ ha]
  have hin₁ : FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c₁ :=
    hin.stab fun a h1 h2 => ⟨hmem₁ a (by omega), by rw [rm₁]⟩
  have hL₁ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₁.nmem :=
    hL.congr fun a h1 h2 => hmem₁ a (by omega)
  -- the separator
  obtain ⟨c₂, t₂, e₂, ht₂, dk₂, m₂, o₂, -, -, -, -, -, -, hrec, hseg⟩ :=
    hsep l r π Hs σ d e b (b + 1) m en c₁ hin₁ hL₁ e₁.wb_right
      (by rw [f₁ _ (by omega) (by omega) (by omega), r4])
      (by rw [f₁ _ (by omega) (by omega) (by omega), r5]) a3 a65 heb (by omega) hroom'
  obtain ⟨g1, g2, g3, g4⟩ := hseg
  obtain ⟨x1, -⟩ := hrec
  have hGb' : b + 1 ≤ c₂.nreg 6502 := by omega
  have hsz : c₂.nreg 6502 + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum ≤
      b + 1 + sR (l.piece ∪ r.piece).card m Hs.length := g3
  have r6₂ : c₂.nreg 3006 = b + 5 := by
    rw [dk₂ _ (by omega) (by omega), f₁ _ (by omega) (by omega) (by omega), r6]
  have hb₂ : c₂.nmem b = c.nreg 3003 := by
    rw [(m₂ b (by omega)).1, m₁, upd_same]
  -- the reading
  obtain ⟨c₃, t₃, e₃, ht₃, b0, b1, b2, b3, b4, b5, b6, b7, b8, fb, mb, rb, rmb, ob⟩ :=
    sgB_exec (P := I) c₂ e₂.wb_right r6₂ (by rw [g2]; omega)
  rw [g2] at b5 b6
  -- the sum of the lengths
  have hfK : ∀ j < π.segs.length, c₃.nmem (c₂.nreg 6502 + 1 + π.segs.length + j) =
      (π.segs.map SPath.k).getD j 0 := fun j hj => by
    rw [mb, (g4 j hj).2.1, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have hsumK : ∑ j ∈ range π.segs.length, (π.segs.map SPath.k).getD j 0 =
      (π.segs.map SPath.k).sum := by
    have := sum_range_getD (π.segs.map SPath.k)
    rw [List.length_map] at this
    exact this
  obtain ⟨c₄, t₄, e₄, ht₄, k7, fk, mk, rk, rmk, ok⟩ := sgKL_exec (P := I) c₃ e₃.wb_right
    (fun j => (π.segs.map SPath.k).getD j 0) b6 b8 b5 b2 b7 (by omega) hfK (by rw [hsumK]; omega)
  rw [hsumK] at k7
  -- the size
  obtain ⟨c₅, t₅, e₅, ht₅, z10, z8, fz, mz, rz, rmz, oz⟩ := sgC_exec (P := I) c₄ e₄.wb_right
    (by rw [fk _ (by omega) (by omega) (by omega), b5]) k7
    (by rw [fk _ (by omega) (by omega) (by omega), b2]) (by omega)
  -- the copy
  obtain ⟨c₆, t₆, e₆, ht₆, cp, co, fc, rc, rmc, oc⟩ := sgML_exec (P := I) c₅ e₅.wb_right
    (b := b) (Gb := c₂.nreg 6502)
    (by rw [fz _ (by omega) (by omega), fk _ (by omega) (by omega) (by omega), b0])
    (by rw [fz _ (by omega) (by omega), fk _ (by omega) (by omega) (by omega), b4]) z8 z10
    (by rw [fz _ (by omega) (by omega), fk _ (by omega) (by omega) (by omega), b2])
    (by omega) (by omega)
  -- the registers
  have r₆ : ∀ x, x ≠ 8408 → x ≠ 8410 → x ≠ 8411 → x ≠ 8412 → x ≠ 8407 → x ≠ 8409 →
      c₆.nreg x = c₃.nreg x := fun x h1 h2 h3 h4 h5 h6 => by
    rw [fc x h1 h3 h4, fz x h1 h2, fk x h5 h1 h6]
  obtain ⟨c₇, t₇, e₇, ht₇, d07, d08, d06, d03, fd, md, rd, rmd, od⟩ := sgD_exec (P := I) c₆
    e₆.wb_right (b := b) (z := 2 * π.segs.length + (π.segs.map SPath.k).sum + 1)
    (h₀ := c.nreg 3003)
    (by rw [r₆ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b0])
    (by rw [fc _ (by omega) (by omega) (by omega)]; exact z10)
    (by rw [r₆ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b1])
    (by rw [r₆ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b3, hb₂])
    (by omega)
  have hmem₂ : ∀ a, a < b → c₇.nmem a = c.nmem a := fun a ha => by
    rw [md, co a (by omega), mz, mk, mb, (m₂ a (by omega)).1, hmem₁ a (by omega)]
  refine ⟨c₇, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))),
    b + (2 * π.segs.length + (π.segs.map SPath.k).sum + 1),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), ?_, by omega, ?_,
    fun x h1 h2 h3 => ?_, d06, ?_, fun a ha => ⟨hmem₂ a ha, ?_⟩, ?_, ?_⟩
  · have ht₂' : t₂ ≤ sT (l.piece ∪ r.piece).card Hs.length := ht₂
    show _ ≤ segT M sT sR (.node l r π, Hs, σ)
    unfold segT; simp only [ADec.piece]; rw [← hcard]
    omega
  · unfold segR; simp only [ADec.piece]; rw [← hcard]; omega
  · by_cases hx : x = 3003
    · subst hx; rw [d03]
    · rw [fd x (by omega) (by omega) h3 hx (by omega),
        r₆ x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        fb x (by omega), dk₂ x h1 h2, f₁ x hx (by omega) (by omega)]
  · rw [d08, r₆ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      fb _ (by omega), r6₂]
  · rw [rmd, rmc, rmz, rmk, rmb, (m₂ a (by omega)).2, rm₁]
  · rw [od, oc, oz, ok, ob, o₂, o₁]
  · show SegsOut M en m π e (b + (2 * π.segs.length + (π.segs.map SPath.k).sum + 1))
      (c₇.nreg 6807) c₇.nmem
    rw [d07]
    refine SegsOut.shift ⟨g1, g2, g3, g4⟩ (fun a ha => ?_) heb (by omega)
    rw [md, cp a (by omega), mz, mk, mb]

end Spec

end MfDrv

end BKMNW

end PlanarFlow
