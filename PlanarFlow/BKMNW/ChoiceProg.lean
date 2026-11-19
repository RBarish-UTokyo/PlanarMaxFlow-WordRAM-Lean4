module

public import PlanarFlow.BKMNW.CutProg
public import PlanarFlow.BKMNW.EncScan

/-!
# The heavy-component and anchor choices of `scChoiceE` on the machine

After the components off a cut-vertex hole `g` are labelled (`ccProg`, `LAB[i] = LAB[j] ↔
e j ∈ comp N g (e i)` for `e i ∈ N`), `scChoiceE.heavy N g ex` is the first index `z` with
`e z ∈ N` and `W₀ < A + Σ_{comp (e z)} (1 + ex)`, and `scChoiceE.anchor (comp N g (e z)) g` the
first index `a` with `LAB[a] = LAB[z]` and tail in `g`. Both are first-index scans
(branch-free: state `(f, z)`, `z += (1 - f) · p · i`, `f += (1 - f) · p`); the weights of the
components are one scatter-add (`saProg`) of `VAL[i] = [e i ∈ N] (1 + ex (e i))` by label.

* pure: `ffStep`, `ffS`, **`ffS_spec`**, **`find?_ffS`** (the scan is `List.find?`),
  `sum_range_filter_reindex`;
* `hvBody` (17 instrs), **`hvScan`** (registers `4780 = n`, `4781 = NFb`, `4782 = LABb`,
  `4783 = SUMb`, `4784 = A`, `4785 = W₀`; written `4786 … 4793`), **`hvScan_exec`**
  (`19 n + 6` steps);
* `acBody` (17 instrs), **`acScan`** (registers `4800 = n`, `4801 = TGb`, `4802 = LABb`,
  `4803 = LZ`; written `4804 … 4811`), **`acScan_exec`** (`19 n + 6` steps);
* **`hvScan_heavy`**, **`acScan_anchor`**: the scans compute `(scChoiceE …).heavy N g ex` and
  `(scChoiceE …).anchor (comp M N Hs g z) g`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The first-index scan, purely -/

/-- One index of the first-index scan with the test value `p ∈ {0, 1}`. -/
def ffStep (p i : ℕ) (st : ℕ × ℕ) : ℕ × ℕ :=
  (st.1 + (1 - st.1) * p, st.2 + (1 - st.1) * p * i)

/-- The state of the first-index scan after the indices `< i`. -/
def ffS (p : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | i + 1 => ffStep (p i) i (ffS p i)

/-- **The state of the first-index scan**: nothing found and all tests zero, or found (`f = 1`)
at the first index `z < i` with test `1`. -/
theorem ffS_spec {p : ℕ → ℕ} (hp : ∀ i, p i ≤ 1) (i : ℕ) :
    ((ffS p i).1 = 0 ∧ (ffS p i).2 = 0 ∧ ∀ j < i, p j = 0) ∨
      ((ffS p i).1 = 1 ∧ (ffS p i).2 < i ∧ p (ffS p i).2 = 1 ∧ ∀ j < (ffS p i).2, p j = 0) := by
  induction i with
  | zero => left; simp [ffS]
  | succ i ih =>
    simp only [ffS, ffStep]
    rcases ih with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
    · rw [h1, h2]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hp i) with h | h
      · left
        refine ⟨by simp [h], by simp [h], fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact h3 j hj
        · exact h
      · right
        simp only [h]
        refine ⟨by simp, by simp, by simp [h], fun j hj => h3 j (by simp at hj; omega)⟩
    · rw [h1]
      right
      have e0 : (1 - 1) * p i = 0 := by simp
      rw [e0, zero_mul, add_zero, add_zero]
      exact ⟨rfl, by omega, h3, h4⟩

/-- **The first-index scan is `List.find?`** for a predicate `q` equivalent to `p i = 1` on
`[0, n)`. -/
theorem find?_ffS {p : ℕ → ℕ} (hp : ∀ i, p i ≤ 1) {n : ℕ} (q : ℕ → Prop) [DecidablePred q]
    (hq : ∀ i < n, (q i ↔ p i = 1)) :
    (List.range n).find? (fun i => decide (q i)) =
      if (ffS p n).1 = 0 then none else some (ffS p n).2 := by
  suffices h : ∀ m ≤ n, (List.range m).find? (fun i => decide (q i)) =
      if (ffS p m).1 = 0 then none else some (ffS p m).2 from h n le_rfl
  intro m hm
  induction m with
  | zero => simp [ffS]
  | succ m ih =>
    rw [List.range_succ, List.find?_append, ih (by omega)]
    have hs := ffS_spec hp m
    simp only [ffS, ffStep]
    rcases hs with ⟨h1, h2, -⟩ | ⟨h1, -, -, -⟩
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hp m) with h | h
      · have : ¬ q m := fun hh => by have := (hq m (by omega)).1 hh; omega
        simp [h1, h2, this, h]
      · have : q m := (hq m (by omega)).2 h
        simp [h1, h2, this, h]
    · simp [h1]

lemma ffS_le {p : ℕ → ℕ} (hp : ∀ i, p i ≤ 1) (i : ℕ) : (ffS p i).1 ≤ 1 ∧ (ffS p i).2 ≤ i := by
  rcases ffS_spec hp i with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;> omega

lemma ffS_congr {p p' : ℕ → ℕ} {i : ℕ} (h : ∀ j < i, p j = p' j) : ffS p i = ffS p' i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [ffS, ih fun j hj => h j (by omega), h i (by omega)]

/-- The sum over the indices of a set of darts. -/
lemma sum_range_filter_reindex {D : Type*} [DecidableEq D] {e : ℕ → D} {n : ℕ}
    (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) {S : Finset D} (hS : ∀ d ∈ S, ∃ i < n, e i = d)
    (f : D → ℕ) : ∑ j ∈ (range n).filter (fun j => e j ∈ S), f (e j) = ∑ d ∈ S, f d := by
  rw [← sum_image (f := f) (g := e) (s := (range n).filter (fun j => e j ∈ S))]
  · congr 1
    ext d
    simp only [mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨j, ⟨-, h⟩, rfl⟩; exact h
    · intro hd
      obtain ⟨i, hi, rfl⟩ := hS d hd
      exact ⟨i, ⟨hi, hd⟩, rfl⟩
  · intro i hi j hj h
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hi hj
    exact hinj i hi.1 j hj.1 h

/-! ### The programs -/

/-- One index of the heavy scan (`4786 = 1`, `4787 = i`, `4788 = f`, `4789 = z`, scratch
`4790 … 4793`): the test `[NF[i] ≠ 0] · [W₀ < A + SUM[LAB[i]]]`. -/
def hvBody : Stmt :=
  block [.addN 4790 4781 4787, .loadN 4790 4790, .divN 4790 4790 4790,
    .addN 4791 4782 4787, .loadN 4791 4791, .addN 4791 4783 4791, .loadN 4791 4791,
    .addN 4791 4784 4791, .subN 4791 4791 4785, .divN 4791 4791 4791,
    .mulN 4790 4790 4791,
    .subN 4792 4786 4788, .mulN 4792 4792 4790, .mulN 4793 4792 4787, .addN 4789 4789 4793,
    .addN 4788 4788 4792, .addN 4787 4787 4786]

/-- **The heavy scan.** -/
def hvScan : Stmt :=
  .seq (block [.constN 4786 1, .constN 4787 0, .constN 4788 0, .constN 4789 0])
    (.whileLtN 4787 4780 hvBody)

/-- One index of the anchor scan (`4804 = 1`, `4805 = i`, `4806 = f`, `4807 = z`, scratch
`4808 … 4811`): the test `[TG[i] ≠ 0] · [LAB[i] = LZ]`. -/
def acBody : Stmt :=
  block [.addN 4808 4801 4805, .loadN 4808 4808, .divN 4808 4808 4808,
    .addN 4809 4802 4805, .loadN 4809 4809,
    .subN 4810 4809 4803, .subN 4811 4803 4809, .addN 4810 4810 4811, .divN 4810 4810 4810,
    .subN 4810 4804 4810, .mulN 4808 4808 4810,
    .subN 4810 4804 4806, .mulN 4810 4810 4808, .mulN 4811 4810 4805, .addN 4807 4807 4811,
    .addN 4806 4806 4810, .addN 4805 4805 4804]

/-- **The anchor scan.** -/
def acScan : Stmt :=
  .seq (block [.constN 4804 1, .constN 4805 0, .constN 4806 0, .constN 4807 0])
    (.whileLtN 4805 4800 acBody)

/-- The test of the heavy scan. -/
def hvP (nf s A W₀ : ℕ) : ℕ := nf / nf * ((A + s - W₀) / (A + s - W₀))

/-- The test of the anchor scan. -/
def acP (tg l LZ : ℕ) : ℕ := tg / tg * (1 - (l - LZ + (LZ - l)) / (l - LZ + (LZ - l)))

lemma hvP_eq (nf s A W₀ : ℕ) : hvP nf s A W₀ = if nf ≠ 0 ∧ W₀ < A + s then 1 else 0 := by
  unfold hvP; rw [sgn_eq, sgn_eq]; split_ifs <;> omega

lemma acP_eq (tg l LZ : ℕ) : acP tg l LZ = if tg ≠ 0 ∧ l = LZ then 1 else 0 := by
  unfold acP; rw [sgn_eq, ne_sgn]; split_ifs <;> omega

lemma hvP_le (nf s A W₀ : ℕ) : hvP nf s A W₀ ≤ 1 := by rw [hvP_eq]; split_ifs <;> omega

lemma acP_le (tg l LZ : ℕ) : acP tg l LZ ≤ 1 := by rw [acP_eq]; split_ifs <;> omega

section Exec

variable {P : Input} {W : ℕ}

theorem hvBody_exec (c : Config) (hc : WordsBounded W c) {NFb LABb SUMb A W₀ i nf l s : ℕ}
    (r1 : c.nreg 4781 = NFb) (r2 : c.nreg 4782 = LABb) (r3 : c.nreg 4783 = SUMb)
    (r4 : c.nreg 4784 = A) (r5 : c.nreg 4785 = W₀) (r6 : c.nreg 4786 = 1)
    (r7 : c.nreg 4787 = i) (hnf : c.nmem (NFb + i) = nf) (hl : c.nmem (LABb + i) = l)
    (hs : c.nmem (SUMb + l) = s) (hf : c.nreg 4788 ≤ 1) (hz : c.nreg 4789 ≤ i)
    (w1 : NFb + i ≤ W) (w2 : LABb + i ≤ W) (w3 : SUMb + l ≤ W) (w4 : A + s ≤ W)
    (w5 : 2 * i + 2 ≤ W) :
    ∃ c' t, Exec P W hvBody c c' t ∧ t = 17 ∧ c'.nreg 4787 = i + 1 ∧
      (c'.nreg 4788, c'.nreg 4789) = ffStep (hvP nf s A W₀) i (c.nreg 4788, c.nreg 4789) ∧
      (∀ x, (x < 4787 ∨ 4793 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set f := c.nreg 4788 with hf'
  set z := c.nreg 4789 with hz'
  have hp := hvP_le nf s A W₀
  have hpv : nf / nf * ((A + s - W₀) / (A + s - W₀)) = hvP nf s A W₀ := rfl
  have m1 : (1 - f) * hvP nf s A W₀ ≤ 1 :=
    (Nat.mul_le_mul (by omega : 1 - f ≤ 1) hp).trans (by norm_num)
  have m2 : (1 - f) * hvP nf s A W₀ * i ≤ i := (Nat.mul_le_mul_right i m1).trans (by simp)
  have hq1 : (A + s - W₀) / (A + s - W₀) ≤ 1 := by rw [sgn_eq]; split_ifs <;> omega
  have hq2 : nf / nf ≤ 1 := by rw [sgn_eq]; split_ifs <;> omega
  have m0 : nf / nf * ((A + s - W₀) / (A + s - W₀)) ≤ 1 :=
    (Nat.mul_le_mul hq2 hq1).trans (by norm_num)
  unfold hvBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5, r6, r7, hnf, hl, hs, ← hf', ← hz', hpv]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r6, r7]
  · config_simp
    simp only [r1, r2, r3, r4, r5, r6, r7, hnf, hl, hs, ← hf', ← hz', hpv, ffStep]
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ : x ≠ 4787 ∧ x ≠ 4788 ∧ x ≠ 4789 ∧ x ≠ 4790 ∧
        x ≠ 4791 ∧ x ≠ 4792 ∧ x ≠ 4793 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4, upd_other _ _ _ a5, upd_other _ _ _ a6, upd_other _ _ _ a7]

theorem acBody_exec (c : Config) (hc : WordsBounded W c) {TGb LABb LZ i tg l : ℕ}
    (r1 : c.nreg 4801 = TGb) (r2 : c.nreg 4802 = LABb) (r3 : c.nreg 4803 = LZ)
    (r4 : c.nreg 4804 = 1) (r5 : c.nreg 4805 = i) (htg : c.nmem (TGb + i) = tg)
    (hl : c.nmem (LABb + i) = l) (hf : c.nreg 4806 ≤ 1) (hz : c.nreg 4807 ≤ i)
    (w1 : TGb + i ≤ W) (w2 : LABb + i ≤ W) (w3 : l + LZ ≤ W) (w5 : 2 * i + 2 ≤ W) :
    ∃ c' t, Exec P W acBody c c' t ∧ t = 17 ∧ c'.nreg 4805 = i + 1 ∧
      (c'.nreg 4806, c'.nreg 4807) = ffStep (acP tg l LZ) i (c.nreg 4806, c.nreg 4807) ∧
      (∀ x, (x < 4805 ∨ 4811 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set f := c.nreg 4806 with hf'
  set z := c.nreg 4807 with hz'
  have hp := acP_le tg l LZ
  have hpv : tg / tg * (1 - (l - LZ + (LZ - l)) / (l - LZ + (LZ - l))) = acP tg l LZ := rfl
  have m1 : (1 - f) * acP tg l LZ ≤ 1 :=
    (Nat.mul_le_mul (by omega : 1 - f ≤ 1) hp).trans (by norm_num)
  have m2 : (1 - f) * acP tg l LZ * i ≤ i := (Nat.mul_le_mul_right i m1).trans (by simp)
  have hq2 : tg / tg ≤ 1 := by rw [sgn_eq]; split_ifs <;> omega
  have m0 : tg / tg * (1 - (l - LZ + (LZ - l)) / (l - LZ + (LZ - l))) ≤ 1 :=
    (Nat.mul_le_mul hq2 (Nat.sub_le 1 _)).trans (by norm_num)
  unfold acBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5, htg, hl, ← hf', ← hz', hpv]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r4, r5]
  · config_simp
    simp only [r1, r2, r3, r4, r5, htg, hl, ← hf', ← hz', hpv, ffStep]
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ : x ≠ 4805 ∧ x ≠ 4806 ∧ x ≠ 4807 ∧ x ≠ 4808 ∧
        x ≠ 4809 ∧ x ≠ 4810 ∧ x ≠ 4811 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4, upd_other _ _ _ a5, upd_other _ _ _ a6, upd_other _ _ _ a7]

/-- **The heavy scan on the machine**: with the flags `NF`, the labels `LAB[i] < nl` and the
weights `SUM` (`nl` words, `A + SUM[k] ≤ W`), within `19 n + 6` steps
`(r4788, r4789) = ffS (hvP NF[i] SUM[LAB[i]] A W₀) n`; memory, registers outside `4786 … 4793`,
reals and output kept. -/
theorem hvScan_exec (c : Config) (hc : WordsBounded W c) {n NFb LABb SUMb A W₀ nl : ℕ}
    (r0 : c.nreg 4780 = n) (r1 : c.nreg 4781 = NFb) (r2 : c.nreg 4782 = LABb)
    (r3 : c.nreg 4783 = SUMb) (r4 : c.nreg 4784 = A) (r5 : c.nreg 4785 = W₀)
    (hlab : ∀ j < n, c.nmem (LABb + j) < nl) (hsum : ∀ k < nl, A + c.nmem (SUMb + k) ≤ W)
    (w1 : NFb + n ≤ W) (w2 : LABb + n ≤ W) (w3 : SUMb + nl ≤ W) (w4 : 2 * n + 2 ≤ W) :
    ∃ c' t, Exec P W hvScan c c' t ∧ t ≤ 19 * n + 6 ∧
      (c'.nreg 4788, c'.nreg 4789) = ffS (fun i => hvP (c.nmem (NFb + i))
        (c.nmem (SUMb + c.nmem (LABb + i))) A W₀) n ∧
      (∀ x, (x < 4786 ∨ 4793 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hvScan
  obtain ⟨c₁, k₁, e₁, hk₁, g6, g7, g8, g9, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4786 1, .constN 4787 0, .constN 4788 0, .constN 4789 0]) c c₁ k₁ ∧
      k₁ = 4 ∧ c₁.nreg 4786 = 1 ∧ c₁.nreg 4787 = 0 ∧ c₁.nreg 4788 = 0 ∧ c₁.nreg 4789 = 0 ∧
      (∀ x, (x < 4786 ∨ 4789 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    obtain ⟨a1, a2, a3, a4⟩ : x ≠ 4786 ∧ x ≠ 4787 ∧ x ≠ 4788 ∧ x ≠ 4789 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4]
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 4786 ∨ 4789 < x) → c₁.nreg x = c.nreg x := gn₁
  set pp : ℕ → ℕ := fun i => hvP (c.nmem (NFb + i)) (c.nmem (SUMb + c.nmem (LABb + i))) A W₀
    with hpp
  have hp : ∀ i, pp i ≤ 1 := fun i => hvP_le _ _ _ _
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4787 ∨ 4793 < x) → c'.nreg x = c₁.nreg x) ∧
    (c'.nreg 4788, c'.nreg 4789) = ffS pp i ∧
    c'.nmem = c.nmem ∧ c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h87, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P) (a := 4787)
    (b := 4780) (body := hvBody) J (B := 17) c₁ hw₁ g7 (by rw [q _ (by omega), r0])
    (Nat.zero_le n) ⟨fun _ _ => rfl, by rw [g8, g9]; rfl, gm₁, rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h87 h80 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 4787 ∨ 4793 < x) → c'.nreg x = c₁.nreg x := j1
      have hle := ffS_le hp i
      have e8 : c'.nreg 4788 = (ffS pp i).1 := congrArg Prod.fst j2
      have e9 : c'.nreg 4789 = (ffS pp i).2 := congrArg Prod.snd j2
      have hli := hlab i hhi
      obtain ⟨c'', t, ex, ht, h87', hst, hn', hm', hr', hrm', ho'⟩ :=
        hvBody_exec (P := P) c' hw (by rw [f _ (by omega), q _ (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega), r2]) (by rw [f _ (by omega), q _ (by omega), r3])
        (by rw [f _ (by omega), q _ (by omega), r4]) (by rw [f _ (by omega), q _ (by omega), r5])
        (by rw [f _ (by omega), g6]) h87 (by rw [j3]) (by rw [j3]) (by rw [j3])
        (by rw [e8]; exact hle.1) (by rw [e9]; exact hle.2) (by omega) (by omega) (by omega)
        (hsum _ hli) (by omega)
      refine ⟨c'', t, ex, ht.le, h87', by rw [hn' _ (by omega)]; exact h80,
        fun x hx => by rw [hn' x hx, f x hx], ?_, by rw [hm', j3],
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      rw [hst, e8, e9]
      rfl)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, fun x hx => ?_, j3,
    by rw [j4, gr₁], by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega)]

/-- **The anchor scan on the machine**: with the flags `TG` and the labels `LAB`
(`LAB[i] + LZ ≤ W`), within `19 n + 6` steps `(r4806, r4807) = ffS (acP TG[i] LAB[i] LZ) n`;
memory, registers outside `4804 … 4811`, reals and output kept. -/
theorem acScan_exec (c : Config) (hc : WordsBounded W c) {n TGb LABb LZ : ℕ}
    (r0 : c.nreg 4800 = n) (r1 : c.nreg 4801 = TGb) (r2 : c.nreg 4802 = LABb)
    (r3 : c.nreg 4803 = LZ) (hlab : ∀ j < n, c.nmem (LABb + j) + LZ ≤ W)
    (w1 : TGb + n ≤ W) (w2 : LABb + n ≤ W) (w4 : 2 * n + 2 ≤ W) :
    ∃ c' t, Exec P W acScan c c' t ∧ t ≤ 19 * n + 6 ∧
      (c'.nreg 4806, c'.nreg 4807) = ffS (fun i => acP (c.nmem (TGb + i))
        (c.nmem (LABb + i)) LZ) n ∧
      (∀ x, (x < 4804 ∨ 4811 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold acScan
  obtain ⟨c₁, k₁, e₁, hk₁, g4, g5, g6, g7, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4804 1, .constN 4805 0, .constN 4806 0, .constN 4807 0]) c c₁ k₁ ∧
      k₁ = 4 ∧ c₁.nreg 4804 = 1 ∧ c₁.nreg 4805 = 0 ∧ c₁.nreg 4806 = 0 ∧ c₁.nreg 4807 = 0 ∧
      (∀ x, (x < 4804 ∨ 4807 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    obtain ⟨a1, a2, a3, a4⟩ : x ≠ 4804 ∧ x ≠ 4805 ∧ x ≠ 4806 ∧ x ≠ 4807 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4]
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 4804 ∨ 4807 < x) → c₁.nreg x = c.nreg x := gn₁
  set pp : ℕ → ℕ := fun i => acP (c.nmem (TGb + i)) (c.nmem (LABb + i)) LZ with hpp
  have hp : ∀ i, pp i ≤ 1 := fun i => acP_le _ _ _
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4805 ∨ 4811 < x) → c'.nreg x = c₁.nreg x) ∧
    (c'.nreg 4806, c'.nreg 4807) = ffS pp i ∧
    c'.nmem = c.nmem ∧ c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h05, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P) (a := 4805)
    (b := 4800) (body := acBody) J (B := 17) c₁ hw₁ g5 (by rw [q _ (by omega), r0])
    (Nat.zero_le n) ⟨fun _ _ => rfl, by rw [g6, g7]; rfl, gm₁, rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h05 h00 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 4805 ∨ 4811 < x) → c'.nreg x = c₁.nreg x := j1
      have hle := ffS_le hp i
      have e6 : c'.nreg 4806 = (ffS pp i).1 := congrArg Prod.fst j2
      have e7 : c'.nreg 4807 = (ffS pp i).2 := congrArg Prod.snd j2
      obtain ⟨c'', t, ex, ht, h05', hst, hn', hm', hr', hrm', ho'⟩ :=
        acBody_exec (P := P) c' hw (by rw [f _ (by omega), q _ (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega), r2]) (by rw [f _ (by omega), q _ (by omega), r3])
        (by rw [f _ (by omega), g4]) h05 (by rw [j3]) (by rw [j3])
        (by rw [e6]; exact hle.1) (by rw [e7]; exact hle.2) (by omega) (by omega)
        (hlab i hhi) (by omega)
      refine ⟨c'', t, ex, ht.le, h05', by rw [hn' _ (by omega)]; exact h00,
        fun x hx => by rw [hn' x hx, f x hx], ?_, by rw [hm', j3],
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      rw [hst, e6, e7]
      rfl)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, fun x hx => ?_, j3,
    by rw [j4, gr₁], by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega)]

end Exec

/-! ### The choices read off the scans -/

section Sem

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

lemma findE_ffS {e : ℕ → D} {n : ℕ} {X : Finset D} {p : ℕ → ℕ} (hp : ∀ i, p i ≤ 1)
    (hX : ∀ i < n, (e i ∈ X ↔ p i = 1)) :
    findE e n X = if (ffS p n).1 = 0 then none else some (e (ffS p n).2) := by
  unfold findE
  rw [find?_ffS hp (fun i => e i ∈ X) hX]
  split_ifs <;> rfl

open Classical in
/-- **The heavy choice of `scChoiceE` read off the heavy scan**: for labels `lab` exact on the
components off `g` (for darts of `N`), the component weights `sum (lab i) = saF lab val n (lab i)`
of `val j = [e j ∈ N] (1 + ex (e j))`, and flags `nf i ≠ 0 ↔ e i ∈ N`,
`(scChoiceE …).heavy N g ex` is the dart of the first-index scan of
`hvP (nf i) (sum (lab i)) A W₀`. -/
theorem hvScan_heavy (sepF : SepFn M) {e : ℕ → D} {n : ℕ}
    (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) {Hs : List (Finset V)} {N : Finset D}
    (hsurjN : ∀ d ∈ N, ∃ i < n, e i = d) {g : Finset V} (ex : D → ℕ) (A W₀ : ℕ)
    {lab sum nf : ℕ → ℕ}
    (hlab : ∀ i < n, ∀ j < n, e i ∈ N → (lab i = lab j ↔ e j ∈ comp M N Hs g (e i)))
    (hsum : ∀ i < n, sum (lab i) =
      saF lab (fun j => if e j ∈ N then 1 + ex (e j) else 0) n (lab i))
    (hnf : ∀ i < n, (nf i ≠ 0 ↔ e i ∈ N)) :
    (scChoiceE M sepF e n Hs A W₀).heavy N g ex =
      if (ffS (fun i => hvP (nf i) (sum (lab i)) A W₀) n).1 = 0 then none
      else some (e (ffS (fun i => hvP (nf i) (sum (lab i)) A W₀) n).2) := by
  show findE e n _ = _
  refine findE_ffS (fun i => hvP_le _ _ _ _) fun i hi => ?_
  rw [hvP_eq, mem_filter]
  by_cases hN : e i ∈ N
  · have hs : sum (lab i) = ∑ d ∈ comp M N Hs g (e i), (1 + ex d) := by
      rw [hsum i hi, saF]
      have hf : (range n).filter (fun j => lab j = lab i) =
          (range n).filter (fun j => e j ∈ comp M N Hs g (e i)) := by
        ext j
        simp only [mem_filter, mem_range]
        exact and_congr_right fun hj => by rw [eq_comm]; exact hlab i hi j hj hN
      rw [hf]
      rw [show (∑ j ∈ (range n).filter (fun j => e j ∈ comp M N Hs g (e i)),
          (if e j ∈ N then 1 + ex (e j) else 0)) =
          ∑ j ∈ (range n).filter (fun j => e j ∈ comp M N Hs g (e i)), (1 + ex (e j)) from
        sum_congr rfl fun j hj => by
          simp only [(mem_comp.1 (mem_filter.1 hj).2).1, ↓reduceIte]]
      exact sum_range_filter_reindex hinj (fun d hd => hsurjN d (mem_comp.1 hd).1)
        (fun d => 1 + ex d)
    rw [hs]
    have := (hnf i hi).2 hN
    split_ifs with h <;> simp_all
  · have : ¬ nf i ≠ 0 := fun h => hN ((hnf i hi).1 h)
    split_ifs with h <;> simp_all

open Classical in
/-- **The anchor choice of `scChoiceE` read off the anchor scan**: for labels exact on the
components off `g`, `e z ∈ N`, and flags `tg i ≠ 0 ↔ tail (e i) ∈ g`,
`(scChoiceE …).anchor (comp M N Hs g (e z)) g` is the dart of the first-index scan of
`acP (tg i) (lab i) (lab z)`. -/
theorem acScan_anchor (sepF : SepFn M) {e : ℕ → D} {n : ℕ} {Hs : List (Finset V)}
    {N : Finset D} {g : Finset V} (A W₀ : ℕ) {lab tg : ℕ → ℕ} {z : ℕ} (hz : z < n)
    (hzN : e z ∈ N)
    (hlab : ∀ i < n, ∀ j < n, e i ∈ N → (lab i = lab j ↔ e j ∈ comp M N Hs g (e i)))
    (htg : ∀ i < n, (tg i ≠ 0 ↔ M.tail (e i) ∈ g)) :
    (scChoiceE M sepF e n Hs A W₀).anchor (comp M N Hs g (e z)) g =
      if (ffS (fun i => acP (tg i) (lab i) (lab z)) n).1 = 0 then none
      else some (e (ffS (fun i => acP (tg i) (lab i) (lab z)) n).2) := by
  show findE e n _ = _
  refine findE_ffS (fun i => acP_le _ _ _) fun i hi => ?_
  have e1 := hlab z hz i hi hzN
  have e2 := htg i hi
  rw [acP_eq, mem_filter]
  split_ifs with h
  · exact ⟨fun _ => rfl, fun _ => ⟨e1.1 h.2.symm, e2.1 h.1⟩⟩
  · refine ⟨fun h' => absurd ⟨e2.2 h'.2, (e1.2 h'.1).symm⟩ h, fun h' => absurd h' (by norm_num)⟩

end Sem

end BKMNW

end PlanarFlow
