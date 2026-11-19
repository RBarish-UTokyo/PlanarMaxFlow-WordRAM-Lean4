module

public import PlanarFlow.BKMNW.ScertDepth
public import PlanarFlow.BKMNW.ClsIdD
public import PlanarFlow.BKMNW.CompGraphProg
public import PlanarFlow.BKMNW.TwoGroupsProg

/-!
# The cut-vertex test of a hole on the machine

The first test of `scertD` (`NoCut`) and the choice `scChoiceE.hole` (the first cut-vertex hole of
the list) need, for a hole `g`, the predicate `CutH M N Hs g`: two darts of `N` off `g` not
connected by steps avoiding `g`. On the machine: label the components off `g` (`ccProg`, for an
enumeration of a superset `B ⊇ N` with the darts outside `N` isolated: `CgEnumSub`), then one
branch-free scan over the flags `GN[i] ≠ 0 ↔ e i ∈ N ∧ tail (e i) ∉ g` compares every flagged
label with the first flagged one.

* `ccProg_comp_sub` (`ccProg_comp` for `CgEnumSub`);
* pure: `cuStep`, `cuS` (the scan state `(f, L, C)`), **`cuS_spec`** (`C ≠ 0` iff two flagged
  indices have different labels);
* programs `cuBody` (18 instrs), **`cuScan`** (registers `4760 = n`, `4761 = GNb`,
  `4762 = LABb`; written `4763 … 4771`, the count `C` in `4767`), `cuBody_exec`,
  **`cuScan_exec`** (`20 n + 7` steps);
* **`cutProg := ccProg ; cuScan`**, **`cutProg_cutH`**: within `124 n + 23` steps
  `r4767 ≠ 0 ↔ CutH M N Hs g`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The scan, purely -/

/-- One index of the scan: `s = [GN[i] ≠ 0]`, `l = LAB[i]`; count a flagged label different from
the first flagged one, record the first flagged label. -/
def cuStep (gn lab : ℕ → ℕ) (i : ℕ) (st : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (st.1 + (1 - st.1) * (gn i / gn i),
    st.2.1 + (1 - st.1) * (gn i / gn i) * lab i,
    st.2.2 + (lab i - st.2.1 + (st.2.1 - lab i)) / (lab i - st.2.1 + (st.2.1 - lab i)) *
      (gn i / gn i) * st.1)

/-- The scan state after the indices `< i`. -/
def cuS (gn lab : ℕ → ℕ) : ℕ → ℕ × ℕ × ℕ
  | 0 => (0, 0, 0)
  | i + 1 => cuStep gn lab i (cuS gn lab i)

lemma sgn_eq (x : ℕ) : x / x = if x = 0 then 0 else 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | h
  · simp
  · rw [Nat.div_self h]; simp [Nat.pos_iff_ne_zero.1 h]

lemma ne_sgn (a b : ℕ) : (a - b + (b - a)) / (a - b + (b - a)) = if a = b then 0 else 1 := by
  rw [sgn_eq]; split_ifs <;> omega

/-- **The scan state**: before the first flagged index all zero; after it, `f = 1`, `L` the
first flagged label, and `C ≠ 0` iff a flagged label differs from it; `C ≤ i`. -/
theorem cuS_spec (gn lab : ℕ → ℕ) (i : ℕ) :
    ((cuS gn lab i).1 = 0 ∧ (cuS gn lab i).2.1 = 0 ∧ (cuS gn lab i).2.2 = 0 ∧
        ∀ j < i, gn j = 0) ∨
      ((cuS gn lab i).1 = 1 ∧ (cuS gn lab i).2.2 ≤ i ∧ ∃ j₀ < i, gn j₀ ≠ 0 ∧
        (cuS gn lab i).2.1 = lab j₀ ∧
        ((cuS gn lab i).2.2 ≠ 0 ↔ ∃ j < i, gn j ≠ 0 ∧ lab j ≠ lab j₀)) := by
  induction i with
  | zero => left; simp [cuS]
  | succ i ih =>
    simp only [cuS, cuStep, sgn_eq (gn i), ne_sgn]
    rcases ih with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, j₀, hj₀, hg₀, hL, hC⟩
    · rw [h1, h2, h3]
      by_cases hg : gn i = 0
      · left; simp only [hg, ↓reduceIte]
        refine ⟨by simp, by simp, by simp, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact h4 j hj
        · exact hg
      · right; simp only [hg, ↓reduceIte]
        refine ⟨by simp, by simp, i, by omega, hg, by simp, ?_⟩
        simp only [mul_zero, add_zero, ne_eq, not_true_eq_false, false_iff, not_exists, not_and]
        intro j hj hgj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact absurd (h4 j hj) hgj
        · exact fun h => h rfl
    · rw [h1, hL]
      right
      refine ⟨by simp, ?_, j₀, by omega, hg₀, by simp, ?_⟩
      · split_ifs <;> simp <;> omega
      · constructor
        · intro h
          by_cases hc : (cuS gn lab i).2.2 = 0
          · rw [hc] at h
            refine ⟨i, by omega, ?_⟩
            by_cases hg : gn i = 0
            · simp [hg] at h
            · refine ⟨hg, fun e => ?_⟩
              simp [hg, e] at h
          · obtain ⟨j, hj, h'⟩ := hC.1 hc
            exact ⟨j, by omega, h'⟩
        · rintro ⟨j, hj, hgj, hlj⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · have := hC.2 ⟨j, hj, hgj, hlj⟩
            omega
          · simp [hgj, hlj]

/-- **The count decides the predicate**: `C ≠ 0` iff two flagged indices `< n` have different
labels. -/
theorem cuS_iff (gn lab : ℕ → ℕ) (n : ℕ) :
    (cuS gn lab n).2.2 ≠ 0 ↔ ∃ i < n, ∃ j < n, gn i ≠ 0 ∧ gn j ≠ 0 ∧ lab i ≠ lab j := by
  rcases cuS_spec gn lab n with ⟨-, -, h3, h4⟩ | ⟨-, -, j₀, hj₀, hg₀, -, hC⟩
  · rw [h3]
    simp only [ne_eq, not_true_eq_false, false_iff, not_exists, not_and]
    intro i hi _ _ hg; exact absurd (h4 i hi) hg
  · rw [hC]
    constructor
    · rintro ⟨j, hj, hg, hl⟩; exact ⟨j, hj, j₀, hj₀, hg, hg₀, hl⟩
    · rintro ⟨i, hi, j, hj, hgi, hgj, hl⟩
      by_cases h : lab i = lab j₀
      · exact ⟨j, hj, hgj, fun e => hl (h.trans e.symm)⟩
      · exact ⟨i, hi, hgi, h⟩

lemma cuS_le (gn lab : ℕ → ℕ) (B : ℕ) (i : ℕ) (hB : ∀ j < i, lab j ≤ B) :
    (cuS gn lab i).1 ≤ 1 ∧ (cuS gn lab i).2.1 ≤ B ∧ (cuS gn lab i).2.2 ≤ i := by
  rcases cuS_spec gn lab i with ⟨h1, h2, h3, -⟩ | ⟨h1, h2, j₀, hj₀, -, hL, -⟩
  · omega
  · exact ⟨by omega, hL ▸ hB j₀ hj₀, h2⟩

/-! ### The program -/

/-- One index of the scan (registers `4763 = 1`, `4764 = i`, `4765 = f`, `4766 = L`,
`4767 = C`, scratch `4768 … 4771`). -/
def cuBody : Stmt :=
  block [.addN 4768 4761 4764, .loadN 4768 4768, .divN 4768 4768 4768,
    .addN 4769 4762 4764, .loadN 4769 4769,
    .subN 4770 4769 4766, .subN 4771 4766 4769, .addN 4770 4770 4771, .divN 4770 4770 4770,
    .mulN 4770 4770 4768, .mulN 4770 4770 4765, .addN 4767 4767 4770,
    .subN 4771 4763 4765, .mulN 4771 4771 4768,
    .mulN 4770 4771 4769, .addN 4766 4766 4770,
    .addN 4765 4765 4771, .addN 4764 4764 4763]

/-- **The scan** (registers `4760 = n`, `4761 = GNb`, `4762 = LABb`; the count in `4767`). -/
def cuScan : Stmt :=
  .seq (block [.constN 4763 1, .constN 4764 0, .constN 4765 0, .constN 4766 0, .constN 4767 0])
    (.whileLtN 4764 4760 cuBody)

section Exec

variable {P : Input} {W : ℕ}

theorem cuBody_exec (c : Config) (hc : WordsBounded W c) {GNb LABb i g l B : ℕ}
    (r1 : c.nreg 4761 = GNb) (r2 : c.nreg 4762 = LABb) (r3 : c.nreg 4763 = 1)
    (r4 : c.nreg 4764 = i) (hg : c.nmem (GNb + i) = g) (hl : c.nmem (LABb + i) = l)
    (hf : c.nreg 4765 ≤ 1) (hL : c.nreg 4766 ≤ B) (hlB : l ≤ B) (hB : 2 * B + 2 ≤ W)
    (hC : c.nreg 4767 ≤ i) (w1 : GNb + i ≤ W) (w2 : LABb + i ≤ W) (w3 : i + 2 ≤ W)
    (hfL : c.nreg 4765 = 0 → c.nreg 4766 = 0) :
    ∃ c' t, Exec P W cuBody c c' t ∧ t = 18 ∧ c'.nreg 4764 = i + 1 ∧
      (c'.nreg 4765, c'.nreg 4766, c'.nreg 4767) =
        cuStep (fun _ => g) (fun _ => l) 0 (c.nreg 4765, c.nreg 4766, c.nreg 4767) ∧
      (∀ x, (x < 4764 ∨ 4771 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set f := c.nreg 4765 with hf'
  set L := c.nreg 4766 with hL'
  set C := c.nreg 4767 with hC'
  have hs : g / g ≤ 1 := by rw [sgn_eq]; split_ifs <;> omega
  have hne : (l - L + (L - l)) / (l - L + (L - l)) ≤ 1 := by rw [ne_sgn]; split_ifs <;> omega
  have hd : l - L + (L - l) ≤ 2 * B := by omega
  have m1 : (l - L + (L - l)) / (l - L + (L - l)) * (g / g) ≤ 1 :=
    (Nat.mul_le_mul hne hs).trans (by norm_num)
  have m2 : (l - L + (L - l)) / (l - L + (L - l)) * (g / g) * f ≤ 1 :=
    (Nat.mul_le_mul m1 hf).trans (by norm_num)
  have m3 : (1 - f) * (g / g) ≤ 1 := (Nat.mul_le_mul (by omega : 1 - f ≤ 1) hs).trans (by norm_num)
  have m4 : (1 - f) * (g / g) * l ≤ l := (Nat.mul_le_mul_right l m3).trans (by simp)
  have m5 : L + (1 - f) * (g / g) * l ≤ B := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [hfL h0]; omega
    · have : 1 - f = 0 := by omega
      rw [this]; simp; omega
  unfold cuBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, hg, hl, ← hf', ← hL', ← hC']; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r3, r4]
  · config_simp
    simp only [r1, r2, r3, r4, hg, hl, ← hf', ← hL', ← hC', cuStep]
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ : x ≠ 4764 ∧ x ≠ 4765 ∧ x ≠ 4766 ∧ x ≠ 4767 ∧
        x ≠ 4768 ∧ x ≠ 4769 ∧ x ≠ 4770 ∧ x ≠ 4771 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4, upd_other _ _ _ a5, upd_other _ _ _ a6, upd_other _ _ _ a7,
      upd_other _ _ _ a8]

lemma cuStep_congr (gn lab : ℕ → ℕ) (i : ℕ) (st : ℕ × ℕ × ℕ) :
    cuStep (fun _ => gn i) (fun _ => lab i) 0 st = cuStep gn lab i st := rfl

/-- **The scan on the machine**: with the flags `GN` and the labels `LAB` (`≤ B`,
`2 B + 2 ≤ W`), within `20 n + 7` steps `(r4765, r4766, r4767) = cuS GN LAB n`; memory,
registers outside `4763 … 4771`, reals and output kept. -/
theorem cuScan_exec (c : Config) (hc : WordsBounded W c) {n GNb LABb B : ℕ}
    (r0 : c.nreg 4760 = n) (r1 : c.nreg 4761 = GNb) (r2 : c.nreg 4762 = LABb)
    (hlab : ∀ j < n, c.nmem (LABb + j) ≤ B) (hB : 2 * B + 2 ≤ W) (w1 : GNb + n ≤ W)
    (w2 : LABb + n ≤ W) (w3 : n + 2 ≤ W) :
    ∃ c' t, Exec P W cuScan c c' t ∧ t ≤ 20 * n + 7 ∧
      (c'.nreg 4765, c'.nreg 4766, c'.nreg 4767) =
        cuS (fun j => c.nmem (GNb + j)) (fun j => c.nmem (LABb + j)) n ∧
      (∀ x, (x < 4763 ∨ 4771 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cuScan
  obtain ⟨c₁, k₁, e₁, hk₁, g3, g4, g5, g6, g7, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4763 1, .constN 4764 0, .constN 4765 0, .constN 4766 0,
        .constN 4767 0]) c c₁ k₁ ∧ k₁ = 5 ∧
      c₁.nreg 4763 = 1 ∧ c₁.nreg 4764 = 0 ∧ c₁.nreg 4765 = 0 ∧ c₁.nreg 4766 = 0 ∧
      c₁.nreg 4767 = 0 ∧
      (∀ x, (x < 4763 ∨ 4767 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    obtain ⟨a1, a2, a3, a4, a5⟩ : x ≠ 4763 ∧ x ≠ 4764 ∧ x ≠ 4765 ∧ x ≠ 4766 ∧ x ≠ 4767 := by
      omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4, upd_other _ _ _ a5]
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 4763 ∨ 4767 < x) → c₁.nreg x = c.nreg x := gn₁
  set gn : ℕ → ℕ := fun j => c.nmem (GNb + j) with hgn
  set lab : ℕ → ℕ := fun j => c.nmem (LABb + j) with hlab'
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4764 ∨ 4771 < x) → c'.nreg x = c₁.nreg x) ∧
    (c'.nreg 4765, c'.nreg 4766, c'.nreg 4767) = cuS gn lab i ∧
    c'.nmem = c.nmem ∧ c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h64, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P) (a := 4764)
    (b := 4760) (body := cuBody) J (B := 18) c₁ hw₁ g4 (by rw [q _ (by omega), r0])
    (Nat.zero_le n) ⟨fun _ _ => rfl, by rw [g5, g6, g7]; rfl, gm₁, rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h64 h60 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 4764 ∨ 4771 < x) → c'.nreg x = c₁.nreg x := j1
      have hle := cuS_le gn lab B i fun j hj => hlab j (by omega)
      have hsp := cuS_spec gn lab i
      have e5 : c'.nreg 4765 = (cuS gn lab i).1 := by
        have := congrArg Prod.fst j2; exact this
      have e6 : c'.nreg 4766 = (cuS gn lab i).2.1 := by
        have := congrArg (fun p => p.2.1) j2; exact this
      have e7 : c'.nreg 4767 = (cuS gn lab i).2.2 := by
        have := congrArg (fun p => p.2.2) j2; exact this
      obtain ⟨c'', t, ex, ht, h64', hst, hn', hm', hr', hrm', ho'⟩ :=
        cuBody_exec (P := P) (B := B) c' hw (by rw [f _ (by omega), q _ (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega), r2]) (by rw [f _ (by omega), g3]) h64
        (by rw [j3]) (by rw [j3]) (by rw [e5]; exact hle.1) (by rw [e6]; exact hle.2.1)
        (hlab i hhi) hB (by rw [e7]; exact hle.2.2) (by omega) (by omega) (by omega)
        (by
          rw [e5, e6]; intro h0
          rcases hsp with ⟨-, h2, -⟩ | ⟨h1, -⟩
          · exact h2
          · omega)
      refine ⟨c'', t, ex, ht.le, h64', by rw [hn' _ (by omega)]; exact h60,
        fun x hx => by rw [hn' x hx, f x hx], ?_, by rw [hm', j3],
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      rw [hst, e5, e6, e7]
      show cuStep (fun _ => gn i) (fun _ => lab i) 0 _ = cuStep gn lab i (cuS gn lab i)
      rfl)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, fun x hx => ?_, j3,
    by rw [j4, gr₁], by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega)]

end Exec

section Cut

variable {P : Input} {W : ℕ}
variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **`ccProg_comp` for an enumeration of a superset** (`CgEnumSub`: the darts outside `N`
isolated). -/
theorem ccProg_comp_sub {B N : Finset D} {Hs : List (Finset V)} {Y : Finset V} {e : ℕ → D}
    (hY : HClosed Hs Y) (c : Config) (hc : WordsBounded W c)
    {n nk RVb TKb YFb LSb OFFb ADJb LABb Qb : ℕ} (hL : CgLay n nk RVb TKb YFb LSb OFFb ADJb)
    (hB : BfLay n (3 * n) OFFb ADJb LABb Qb W) (hTK : ∀ i < n, c.nmem (TKb + i) < nk)
    (hE : CgEnumSub M B N Hs Y n e (fun i => c.nmem (RVb + i)) (cgKey c.nmem TKb)
      (cgYf c.nmem YFb))
    (hLS : ∀ k < nk, c.nmem (LSb + k) = 0) (hLAB : ∀ u < n, c.nmem (LABb + u) = 0)
    (r0 : c.nreg 4420 = n) (r1 : c.nreg 4421 = RVb) (r2 : c.nreg 4422 = TKb)
    (r3 : c.nreg 4423 = YFb) (r4 : c.nreg 4424 = LSb) (r5 : c.nreg 4425 = OFFb)
    (r6 : c.nreg 4426 = ADJb) (s0 : c.nreg 4400 = n) (s1 : c.nreg 4401 = OFFb)
    (s2 : c.nreg 4402 = ADJb) (s3 : c.nreg 4403 = LABb) (s4 : c.nreg 4404 = Qb) :
    ∃ c' k, Exec P W ccProg c c' k ∧ k ≤ 104 * n + 16 ∧
      (∀ i < n, ∀ j < n, e i ∈ N → (c'.nmem (LABb + i) = c'.nmem (LABb + j) ↔
        e j ∈ comp M N Hs Y (e i))) ∧
      (∀ u < n, 0 < c'.nmem (LABb + u) ∧ c'.nmem (LABb + u) ≤ n) ∧
      (∀ a, ¬ (LSb ≤ a ∧ a < LSb + nk) → ¬ (OFFb ≤ a ∧ a < ADJb + 3 * n) →
        ¬ (LABb ≤ a ∧ a < Qb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4405 ∨ 4436 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, ex, hk, H1, H2, H3, H4, H5, H6, H7⟩ := ccProg_exec (P := P) c hc hL hB hTK
    hE.rvOK hLS hLAB r0 r1 r2 r3 r4 r5 r6 s0 s1 s2 s3 s4
  exact ⟨c', k, ex, hk, fun i hi j hj hiN => by
    rw [H1 i hi j hj, mem_comp_iff_cgAdj_sub hY hE hi hj hiN], H2, H3, H4, H5, H6, H7⟩

/-- **The cut-vertex test of a hole**: the components off `g` (`ccProg`), then the scan. -/
def cutProg : Stmt := .seq ccProg cuScan

/-- **The cut-vertex test of a hole on the machine**: for an enumeration `e` of a superset
`B ⊇ N` (`CgEnumSub` with `Y = g`, `g ∈ Hs`, holes pairwise disjoint) and the flags
`GN[i] ≠ 0 ↔ e i ∈ N ∧ tail (e i) ∉ g` (below the arrays of `ccProg`), within `124 n + 23` steps
`r4767 ≠ 0 ↔ CutH M N Hs g`. -/
theorem cutProg_cutH {B N : Finset D} {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint)
    {g : Finset V} (hg : g ∈ Hs) {e : ℕ → D} (c : Config) (hc : WordsBounded W c)
    {n nk GNb RVb TKb YFb LSb OFFb ADJb LABb Qb : ℕ} (hL : CgLay n nk RVb TKb YFb LSb OFFb ADJb)
    (hB : BfLay n (3 * n) OFFb ADJb LABb Qb W) (hGN : GNb + n ≤ RVb) (hW : 2 * n + 2 ≤ W)
    (hTK : ∀ i < n, c.nmem (TKb + i) < nk)
    (hE : CgEnumSub M B N Hs g n e (fun i => c.nmem (RVb + i)) (cgKey c.nmem TKb)
      (cgYf c.nmem YFb))
    (hGNf : ∀ i < n, (c.nmem (GNb + i) ≠ 0 ↔ e i ∈ N ∧ M.tail (e i) ∉ g))
    (hLS : ∀ k < nk, c.nmem (LSb + k) = 0) (hLAB : ∀ u < n, c.nmem (LABb + u) = 0)
    (r0 : c.nreg 4420 = n) (r1 : c.nreg 4421 = RVb) (r2 : c.nreg 4422 = TKb)
    (r3 : c.nreg 4423 = YFb) (r4 : c.nreg 4424 = LSb) (r5 : c.nreg 4425 = OFFb)
    (r6 : c.nreg 4426 = ADJb) (s0 : c.nreg 4400 = n) (s1 : c.nreg 4401 = OFFb)
    (s2 : c.nreg 4402 = ADJb) (s3 : c.nreg 4403 = LABb) (s4 : c.nreg 4404 = Qb)
    (u0 : c.nreg 4760 = n) (u1 : c.nreg 4761 = GNb) (u2 : c.nreg 4762 = LABb) :
    ∃ c' k, Exec P W cutProg c c' k ∧ k ≤ 124 * n + 23 ∧
      (c'.nreg 4767 ≠ 0 ↔ CutH M N Hs g) ∧
      (∀ a, ¬ (LSb ≤ a ∧ a < LSb + nk) → ¬ (OFFb ≤ a ∧ a < ADJb + 3 * n) →
        ¬ (LABb ≤ a ∧ a < Qb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4405 ∨ (4436 < x ∧ x < 4763) ∨ 4771 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hY := hClosed_of_mem hd hg
  obtain ⟨c₁, k₁, e₁, hk₁, H1, H2, H3, H4, H5, H6, H7⟩ := ccProg_comp_sub (P := P) hY c hc hL hB
    hTK hE hLS hLAB r0 r1 r2 r3 r4 r5 r6 s0 s1 s2 s3 s4
  have hw₁ := e₁.wb_right
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  obtain ⟨b1, b2, b3, b4⟩ := hB
  have hGN₁ : ∀ i < n, c₁.nmem (GNb + i) = c.nmem (GNb + i) := fun i hi =>
    H3 _ (by omega) (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, hst, hn₂, hm₂, hr₂, hrm₂, ho₂⟩ := cuScan_exec (P := P) (B := n) c₁ hw₁
    (by rw [H4 _ (by omega), u0]) (by rw [H4 _ (by omega), u1]) (by rw [H4 _ (by omega), u2])
    (fun j hj => (H2 j hj).2) hW (by omega) (by omega) (by omega)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, ?_, fun a ha hb hc' => by rw [hm₂, H3 a ha hb hc'],
    fun x hx => by rw [hn₂ x (by omega), H4 x (by omega)], by rw [hr₂, H5],
    by rw [hrm₂, H6], by rw [ho₂, H7]⟩
  have h67 : c₂.nreg 4767 = (cuS (fun j => c₁.nmem (GNb + j)) (fun j => c₁.nmem (LABb + j)) n).2.2 :=
    congrArg (fun p => p.2.2) hst
  rw [h67, cuS_iff]
  constructor
  · rintro ⟨i, hi, j, hj, hgi, hgj, hl⟩
    rw [hGN₁ i hi, hGNf i hi] at hgi
    rw [hGN₁ j hj, hGNf j hj] at hgj
    refine ⟨e i, hgi.1, e j, hgj.1, hgi.2, hgj.2, fun h => hl ?_⟩
    exact (H1 i hi j hj hgi.1).2 (mem_comp.2 ⟨hgj.1, h⟩)
  · rintro ⟨x, hx, y, hy, hxg, hyg, hn⟩
    obtain ⟨i, hi, rfl⟩ := hE.surj x (hE.sub hx)
    obtain ⟨j, hj, rfl⟩ := hE.surj y (hE.sub hy)
    refine ⟨i, hi, j, hj, by rw [hGN₁ i hi, hGNf i hi]; exact ⟨hx, hxg⟩,
      by rw [hGN₁ j hj, hGNf j hj]; exact ⟨hy, hyg⟩, fun h => hn ?_⟩
    exact (mem_comp.1 ((H1 i hi j hj hx).1 h)).2

end Cut

end BKMNW

end PlanarFlow
