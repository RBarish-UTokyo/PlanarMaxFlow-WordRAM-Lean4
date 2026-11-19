module

public import PlanarFlow.BKMNW.TwoGroupsProg
public import PlanarFlow.BKMNW.IteR23

/-!
# Three scans of the encoding of a piece map: inverse, rank, scatter-add

The plain encoding of the piece map `psep` (the input of Miller's program `msep`) is built from
the index arrays of the piece by gathers (`gaProg`), orbit labellings (`bfProg`) and the three
scans of this file.

* **`invProg`** (`OUT[P[j]] := j`, the inverse of an injective index array), `invBody_exec`
  (5 steps), **`invProg_exec`** (`7 m + 4` steps). Registers `4600 = m`, `4601 = Pb`,
  `4602 = OUTb`; written `4603 = 1`, `4604` (index), `4605`.
* **`rkProg`** (contiguous renumbering of labels by first occurrence): pure `rkT`, `rkC`
  (table and counter after `i` indices) with `rkT_ne_zero_iff`, `rkT_le`, `rkT_inj`,
  `rkT_stable`, `rkT_surj`; `rkBody_exec` (14 steps), **`rkProg_exec`** (`16 m + 5` steps,
  `OUT[j] = rkT (j+1) (LAB j) - 1`, counter `r4616 = rkC m`), **`rk_final`** (`OUT[i] = OUT[j] ↔
  LAB i = LAB j`, `OUT[j] < rkC m`, every number `< rkC m` is some `OUT[j]`). Registers
  `4610 = m`, `4611 = LABb`, `4612 = Tb`, `4613 = OUTb`; written `4614 = 1`, `4615` (index),
  `4616` (counter), `4617 … 4621`.
* **`saProg`** (scatter-add: `WT[KEY[j]] += VAL[j]` with `VAL[j] = mem (VALb + st · j)`; `st = 0`
  adds one constant cell), `saF` (the sums), `saBody_exec` (10 steps), **`saProg_exec`**
  (`12 m + 4` steps). Registers `4630 = m`, `4631 = KEYb`, `4632 = VALb`, `4633 = st`,
  `4634 = Wb`; written `4635 = 1`, `4636` (index), `4637 … 4639`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The inverse of an index array -/

/-- `OUT[P[j]] := j`. -/
def invBody : Stmt :=
  block [.addN 4605 4601 4604, .loadN 4605 4605, .addN 4605 4602 4605, .storeN 4605 4604,
    .addN 4604 4604 4603]

/-- **The inverse of an index array on the machine.** -/
def invProg : Stmt :=
  .seq (block [.constN 4603 1, .constN 4604 0]) (.whileLtN 4604 4600 invBody)

section Inv

variable {P : Input} {W : ℕ}

theorem invBody_exec (c : Config) (hc : WordsBounded W c) {Pb OUTb j : ℕ}
    (r1 : c.nreg 4601 = Pb) (r2 : c.nreg 4602 = OUTb) (r3 : c.nreg 4603 = 1)
    (r4 : c.nreg 4604 = j) (w1 : Pb + j ≤ W) (w2 : OUTb + c.nmem (Pb + j) ≤ W)
    (w4 : j + 1 ≤ W) :
    ∃ c' k, Exec P W invBody c c' k ∧ k = 5 ∧ c'.nreg 4604 = j + 1 ∧
      c'.nmem = upd c.nmem (OUTb + c.nmem (Pb + j)) j ∧
      (∀ x, (x < 4604 ∨ 4605 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold invBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r3, r4]
  · config_simp; simp only [r1, r2, r4]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The inverse of an index array**: with `P[j] = nmem (Pb + j)` injective on `[0, m)` and the
output `OUT` disjoint from `P`, within `7 m + 4` steps `OUT[P[j]] = j` for `j < m`; memory
outside the cells `OUTb + P[j]` and registers outside `4603 … 4605` kept. -/
theorem invProg_exec (c : Config) (hc : WordsBounded W c) {m Pb OUTb : ℕ}
    (r0 : c.nreg 4600 = m) (r1 : c.nreg 4601 = Pb) (r2 : c.nreg 4602 = OUTb)
    (w1 : Pb + m ≤ W) (w4 : m + 1 ≤ W) (hP : ∀ j < m, OUTb + c.nmem (Pb + j) ≤ W)
    (hinj : ∀ i < m, ∀ j < m, c.nmem (Pb + i) = c.nmem (Pb + j) → i = j)
    (d1 : ∀ i < m, ∀ j < m, Pb + i ≠ OUTb + c.nmem (Pb + j)) :
    ∃ c' k, Exec P W invProg c c' k ∧ k ≤ 7 * m + 4 ∧
      (∀ j < m, c'.nmem (OUTb + c.nmem (Pb + j)) = j) ∧
      (∀ a, (∀ j < m, a ≠ OUTb + c.nmem (Pb + j)) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4603 ∨ 4605 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold invProg
  obtain ⟨c₁, k₁, e₁, hk₁, g3, g4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4603 1, .constN 4604 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 4603 = 1 ∧ c₁.nreg 4604 = 0 ∧
      (∀ x, x ≠ 4603 → x ≠ 4604 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 4603 → x ≠ 4604 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4604 ∨ 4605 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (OUTb + m₀ (Pb + j)) = j) ∧
    (∀ a, (∀ j < i, a ≠ OUTb + m₀ (Pb + j)) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h75, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P) (a := 4604)
    (b := 4600) (body := invBody) J (B := 5) c₁ hw₁ g4 (by rw [q _ (by omega) (by omega), r0])
    (Nat.zero_le m) ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h75 h70 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 4604 ∨ 4605 < x) → c'.nreg x = c₁.nreg x := j1
      have e1 : c'.nmem (Pb + i) = m₀ (Pb + i) :=
        j3 _ (fun j hj => d1 i hhi j (by omega))
      obtain ⟨c'', t, ex, ht, h75', hm', hn', hr', hrm', ho'⟩ := invBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
        (by rw [f _ (by omega), g3]) h75 (by omega) (by rw [e1]; exact hP i hhi) (by omega)
      rw [e1] at hm'
      refine ⟨c'', t, ex, ht.le, h75', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · have hne : OUTb + m₀ (Pb + j) ≠ OUTb + m₀ (Pb + i) := by
            intro h; have := hinj j (by omega) i hhi (by omega); omega
          rw [upd_other _ _ _ hne]; exact j2 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (ha i (by omega))]
        exact j3 a (fun j hj => ha j (by omega)))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, fun x hx => ?_, by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega)]

end Inv

/-! ### The rank of labels by first occurrence -/

/-- The table and the counter after the first `i` labels: a label met for the first time gets
the next number (from `1`). -/
def rkS (lab : ℕ → ℕ) : ℕ → (ℕ → ℕ) × ℕ
  | 0 => (fun _ => 0, 0)
  | i + 1 =>
    if (rkS lab i).1 (lab i) = 0 then
      (Function.update (rkS lab i).1 (lab i) ((rkS lab i).2 + 1), (rkS lab i).2 + 1)
    else rkS lab i

/-- The table after the first `i` labels. -/
def rkT (lab : ℕ → ℕ) (i : ℕ) : ℕ → ℕ := (rkS lab i).1

/-- The number of distinct labels among the first `i`. -/
def rkC (lab : ℕ → ℕ) (i : ℕ) : ℕ := (rkS lab i).2

/-- The output of the rank: the number (from `0`) of the label of `j`. -/
def rkO (lab : ℕ → ℕ) (j : ℕ) : ℕ := rkT lab (j + 1) (lab j) - 1

section RankPure

variable {lab : ℕ → ℕ}

@[simp] lemma rkT_zero (k : ℕ) : rkT lab 0 k = 0 := rfl

@[simp] lemma rkC_zero : rkC lab 0 = 0 := rfl

lemma rkC_succ (i : ℕ) :
    rkC lab (i + 1) = if rkT lab i (lab i) = 0 then rkC lab i + 1 else rkC lab i := by
  unfold rkC rkT
  rw [rkS]
  split_ifs <;> rfl

lemma rkT_succ (i k : ℕ) :
    rkT lab (i + 1) k =
      if rkT lab i (lab i) = 0 ∧ k = lab i then rkC lab i + 1 else rkT lab i k := by
  unfold rkC rkT
  rw [rkS]
  by_cases h : (rkS lab i).1 (lab i) = 0
  · simp only [h, ↓reduceIte, true_and, Function.update_apply]
  · simp only [h, ↓reduceIte, false_and]

lemma rkC_le (i : ℕ) : rkC lab i ≤ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [rkC_succ]; split_ifs <;> omega

lemma rkT_le (i k : ℕ) : rkT lab i k ≤ rkC lab i := by
  induction i generalizing k with
  | zero => simp
  | succ i ih =>
    rw [rkT_succ, rkC_succ]
    have := ih (lab i)
    split_ifs with h1 h2 <;> first | omega | (have := ih k; omega)

lemma rkT_ne_zero_iff (i k : ℕ) : rkT lab i k ≠ 0 ↔ ∃ j < i, lab j = k := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [rkT_succ]
    constructor
    · intro h
      split_ifs at h with h1
      · exact ⟨i, by omega, h1.2.symm⟩
      · obtain ⟨j, hj, e⟩ := ih.1 h; exact ⟨j, by omega, e⟩
    · rintro ⟨j, hj, e⟩
      split_ifs with h1
      · omega
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact ih.2 ⟨j, hj, e⟩
        · intro h0
          apply h1
          subst e
          exact ⟨h0, rfl⟩

lemma rkT_succ_of_ne {i k : ℕ} (h : rkT lab i k ≠ 0) : rkT lab (i + 1) k = rkT lab i k := by
  rw [rkT_succ]
  split_ifs with h1
  · exact absurd (h1.2 ▸ h1.1) h
  · rfl

lemma rkT_stable {i k : ℕ} (h : rkT lab i k ≠ 0) : ∀ i', i ≤ i' → rkT lab i' k = rkT lab i k := by
  intro i' hi'
  induction i' with
  | zero => rw [show i = 0 by omega]
  | succ i' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hi') with h' | h'
    · have e := ih (by omega)
      rw [rkT_succ_of_ne (by rw [e]; exact h), e]
    · rw [h']

lemma rkT_inj (i : ℕ) {k k' : ℕ} (h : rkT lab i k ≠ 0) (e : rkT lab i k = rkT lab i k') :
    k = k' := by
  induction i generalizing k k' with
  | zero => simp at h
  | succ i ih =>
    rw [rkT_succ, rkT_succ] at e
    rw [rkT_succ] at h
    have b1 := rkT_le (lab := lab) i k
    have b2 := rkT_le (lab := lab) i k'
    split_ifs at e h with h1 h2 h2 <;> first | omega | exact h1.2.trans h2.2.symm | exact ih h e

lemma rkT_surj (i : ℕ) : ∀ r, 0 < r → r ≤ rkC lab i → ∃ j < i, rkT lab i (lab j) = r := by
  induction i with
  | zero => intro r h1 h2; simp at h2; omega
  | succ i ih =>
    intro r h1 h2
    rw [rkC_succ] at h2
    by_cases h0 : rkT lab i (lab i) = 0
    · rw [iteT h0] at h2
      rcases Nat.lt_or_ge r (rkC lab i + 1) with h2 | h2'
      · obtain ⟨j, hj, e⟩ := ih r h1 (by omega)
        exact ⟨j, by omega, by rw [rkT_succ_of_ne (by omega), e]⟩
      · refine ⟨i, by omega, ?_⟩
        rw [rkT_succ, iteT ⟨h0, rfl⟩]; omega
    · rw [iteF h0] at h2
      obtain ⟨j, hj, e⟩ := ih r h1 h2
      exact ⟨j, by omega, by rw [rkT_succ_of_ne (by omega), e]⟩

lemma rkO_eq {m j : ℕ} (hj : j < m) : rkO lab j = rkT lab m (lab j) - 1 := by
  unfold rkO
  have h : rkT lab (j + 1) (lab j) ≠ 0 := (rkT_ne_zero_iff _ _).2 ⟨j, by omega, rfl⟩
  rw [rkT_stable h m (by omega)]

lemma rkT_pos {m j : ℕ} (hj : j < m) : 0 < rkT lab m (lab j) :=
  Nat.pos_of_ne_zero ((rkT_ne_zero_iff _ _).2 ⟨j, hj, rfl⟩)

/-- **The rank is a contiguous renumbering**: `rkO i = rkO j ↔ lab i = lab j`, the numbers are
`< rkC m`, and every number `< rkC m` is used. -/
theorem rk_final (m : ℕ) :
    (∀ i < m, ∀ j < m, (rkO lab i = rkO lab j ↔ lab i = lab j)) ∧
      (∀ j < m, rkO lab j < rkC lab m) ∧ (∀ r < rkC lab m, ∃ j < m, rkO lab j = r) := by
  refine ⟨fun i hi j hj => ?_, fun j hj => ?_, fun r hr => ?_⟩
  · rw [rkO_eq hi, rkO_eq hj]
    have a := rkT_pos (lab := lab) hi
    have b := rkT_pos (lab := lab) hj
    constructor
    · intro e; exact rkT_inj (lab := lab) (k := lab i) (k' := lab j) m (by omega) (by omega)
    · intro e; rw [e]
  · rw [rkO_eq hj]
    have := rkT_le (lab := lab) m (lab j)
    have := rkT_pos (lab := lab) hj
    omega
  · obtain ⟨j, hj, e⟩ := rkT_surj (lab := lab) m (r + 1) (by omega) (by omega)
    exact ⟨j, hj, by rw [rkO_eq hj, e]; omega⟩

end RankPure

/-- One index of the rank: `x := LAB[i]`, `y := T[x]`; a new label (`y = 0`) gets the next
number; `T[x] := y'`, `OUT[i] := y' - 1`. Branch-free: `1 - y / y` is the test `y = 0`. -/
def rkBody : Stmt :=
  block [.addN 4617 4611 4615, .loadN 4617 4617, .addN 4618 4612 4617, .loadN 4619 4618,
    .divN 4620 4619 4619, .subN 4620 4614 4620, .addN 4616 4616 4620, .mulN 4621 4620 4616,
    .addN 4619 4619 4621, .storeN 4618 4619, .subN 4619 4619 4614, .addN 4621 4613 4615,
    .storeN 4621 4619, .addN 4615 4615 4614]

/-- **The rank of labels on the machine.** -/
def rkProg : Stmt :=
  .seq (block [.constN 4614 1, .constN 4615 0, .constN 4616 0]) (.whileLtN 4615 4610 rkBody)

section RankExec

variable {P : Input} {W : ℕ}

theorem rkBody_exec (c : Config) (hc : WordsBounded W c) {LABb Tb OUTb i cnt x y : ℕ}
    (r1 : c.nreg 4611 = LABb) (r2 : c.nreg 4612 = Tb) (r3 : c.nreg 4613 = OUTb)
    (r4 : c.nreg 4614 = 1) (r5 : c.nreg 4615 = i) (r6 : c.nreg 4616 = cnt)
    (hx : c.nmem (LABb + i) = x) (hy : c.nmem (Tb + x) = y)
    (w1 : LABb + i ≤ W) (w2 : Tb + x ≤ W) (w3 : OUTb + i ≤ W) (w4 : i + 1 ≤ W)
    (w5 : cnt + 1 ≤ W) :
    ∃ c' k, Exec P W rkBody c c' k ∧ k = 14 ∧ c'.nreg 4615 = i + 1 ∧
      c'.nreg 4616 = (if y = 0 then cnt + 1 else cnt) ∧
      c'.nmem = upd (upd c.nmem (Tb + x) (if y = 0 then cnt + 1 else y)) (OUTb + i)
        ((if y = 0 then cnt + 1 else y) - 1) ∧
      (∀ x, (x < 4615 ∨ 4621 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hyW : y ≤ W := hy ▸ hc.2 _
  unfold rkBody
  by_cases h0 : y = 0
  · subst h0
    exec_block
    all_goals try (config_simp; simp only [r1, r2, r3, r4, r5, r6, hx, hy, Nat.zero_div,
      Nat.sub_zero, one_mul, Nat.zero_add]; omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [r4, r5]
    · config_simp; simp only [r1, r2, r4, r5, r6, hx, hy, Nat.zero_div, Nat.sub_zero, ↓reduceIte]
    · config_simp
      simp only [r1, r2, r3, r4, r5, r6, hx, hy, Nat.zero_div, Nat.sub_zero, one_mul,
        Nat.zero_add, ↓reduceIte]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  · have hd : y / y = 1 := Nat.div_self (Nat.pos_of_ne_zero h0)
    exec_block
    all_goals try (config_simp; simp only [r1, r2, r3, r4, r5, r6, hx, hy, hd, Nat.sub_self,
      zero_mul, Nat.add_zero]; omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [r4, r5]
    · config_simp; simp only [r1, r2, r4, r5, r6, hx, hy, hd, Nat.sub_self, Nat.add_zero, h0,
        ↓reduceIte]
    · config_simp
      simp only [r1, r2, r3, r4, r5, r6, hx, hy, hd, Nat.sub_self, zero_mul, Nat.add_zero, h0,
        ↓reduceIte]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The rank on the machine**: with labels `LAB[j] < nk` (`j < m`), the table `T` zero on
`[0, nk)` and the three arrays disjoint, within `16 m + 5` steps `OUT[j] = rkO LAB j` for
`j < m`, the counter `r4616 = rkC LAB m` (the number of distinct labels), `T[k] = rkT LAB m k`;
memory outside `T` and `OUT` and registers outside `4614 … 4621` kept. -/
theorem rkProg_exec (c : Config) (hc : WordsBounded W c) {m nk LABb Tb OUTb : ℕ}
    (r0 : c.nreg 4610 = m) (r1 : c.nreg 4611 = LABb) (r2 : c.nreg 4612 = Tb)
    (r3 : c.nreg 4613 = OUTb) (hlab : ∀ j < m, c.nmem (LABb + j) < nk)
    (hT : ∀ k < nk, c.nmem (Tb + k) = 0)
    (lay : (LABb + m ≤ Tb ∨ Tb + nk ≤ LABb) ∧ (LABb + m ≤ OUTb ∨ OUTb + m ≤ LABb) ∧
      (Tb + nk ≤ OUTb ∨ OUTb + m ≤ Tb) ∧ LABb + m ≤ W ∧ Tb + nk ≤ W ∧ OUTb + m ≤ W ∧
      m + 1 ≤ W) :
    ∃ c' k, Exec P W rkProg c c' k ∧ k ≤ 16 * m + 5 ∧
      (∀ j < m, c'.nmem (OUTb + j) = rkO (fun j => c.nmem (LABb + j)) j) ∧
      c'.nreg 4616 = rkC (fun j => c.nmem (LABb + j)) m ∧
      (∀ k < nk, c'.nmem (Tb + k) = rkT (fun j => c.nmem (LABb + j)) m k) ∧
      (∀ a, ¬ (Tb ≤ a ∧ a < Tb + nk) → ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4614 ∨ 4621 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := lay
  unfold rkProg
  obtain ⟨c₁, k₁, e₁, hk₁, g4, g5, g6, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4614 1, .constN 4615 0, .constN 4616 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 4614 = 1 ∧ c₁.nreg 4615 = 0 ∧ c₁.nreg 4616 = 0 ∧
      (∀ x, x ≠ 4614 → x ≠ 4615 → x ≠ 4616 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 4614 → x ≠ 4615 → x ≠ 4616 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  set lab : ℕ → ℕ := fun j => m₀ (LABb + j) with hlabd
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4615 ∨ 4621 < x) → c'.nreg x = c₁.nreg x) ∧ c'.nreg 4616 = rkC lab i ∧
    (∀ k < nk, c'.nmem (Tb + k) = rkT lab i k) ∧
    (∀ j < i, c'.nmem (OUTb + j) = rkO lab j) ∧
    (∀ a, ¬ (Tb ≤ a ∧ a < Tb + nk) → ¬ (OUTb ≤ a ∧ a < OUTb + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h75, j1, j0, jT, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 4615) (b := 4610) (body := rkBody) J (B := 14) c₁ hw₁ g5
    (by rw [q _ (by omega) (by omega) (by omega), r0])
    (Nat.zero_le m) ⟨fun _ _ => rfl, by rw [g6]; rfl, fun k hk => by rw [gm₁, hT k hk]; rfl,
      fun j hj => absurd hj (by omega), fun a _ _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h75 h70 ⟨j1, j0, jT, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 4615 ∨ 4621 < x) → c'.nreg x = c₁.nreg x := j1
      have hli : lab i < nk := hlab i hhi
      have e1 : c'.nmem (LABb + i) = lab i :=
        j3 _ (fun h => by omega) (fun h => by omega)
      have e2 : c'.nmem (Tb + lab i) = rkT lab i (lab i) := jT _ hli
      have hcnt := rkC_le (lab := lab) i
      obtain ⟨c'', t, ex, ht, h75', h76', hm', hn', hr', hrm', ho'⟩ := rkBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega) (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega) (by omega) (by omega), r3])
        (by rw [f _ (by omega), g4]) h75 j0 e1 e2 (by omega) (by omega) (by omega) (by omega)
        (by omega)
      have hv : (if rkT lab i (lab i) = 0 then rkC lab i + 1 else rkT lab i (lab i)) =
          rkT lab (i + 1) (lab i) := by
        rw [rkT_succ]; split_ifs with h1 h2 <;> simp_all
      rw [hv] at hm'
      refine ⟨c'', t, ex, ht.le, h75', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], by rw [h76', rkC_succ], fun k hk => ?_,
        fun j hj => ?_, fun a ha hb => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm', upd_other _ _ _ (by omega)]
        by_cases hk' : k = lab i
        · subst hk'; rw [upd_same]
        · rw [upd_other _ _ _ (by omega), jT k hk, rkT_succ]
          split_ifs with h1
          · exact absurd h1.2 hk'
          · rfl
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same]; rfl
      · rw [hm', upd_other _ _ _ (fun h => hb ⟨by omega, by omega⟩),
          upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
        exact j3 a ha (fun h => hb ⟨h.1, by omega⟩))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j0, jT, j3, fun x hx => ?_, by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega) (by omega)]

end RankExec

/-! ### Scatter-add -/

/-- The sums after the first `i` indices: `Σ_{j < i, key j = k} val j`. -/
def saF (key val : ℕ → ℕ) (i k : ℕ) : ℕ := ∑ j ∈ (range i).filter (fun j => key j = k), val j

lemma saF_zero (key val : ℕ → ℕ) (k : ℕ) : saF key val 0 k = 0 := by simp [saF]

lemma saF_succ (key val : ℕ → ℕ) (i k : ℕ) :
    saF key val (i + 1) k = saF key val i k + if key i = k then val i else 0 := by
  unfold saF
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [sum_insert (by simp), add_comm]
  · rw [Nat.add_zero]

lemma saF_le (key val : ℕ → ℕ) (i k : ℕ) : saF key val i k ≤ ∑ j ∈ range i, val j :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

/-- `WT[KEY[i]] += VAL[i]` with `VAL[i] = mem (VALb + st · i)`. -/
def saBody : Stmt :=
  block [.addN 4637 4631 4636, .loadN 4637 4637, .addN 4637 4634 4637, .mulN 4638 4633 4636,
    .addN 4638 4632 4638, .loadN 4638 4638, .loadN 4639 4637, .addN 4639 4639 4638,
    .storeN 4637 4639, .addN 4636 4636 4635]

/-- **The scatter-add on the machine.** -/
def saProg : Stmt :=
  .seq (block [.constN 4635 1, .constN 4636 0]) (.whileLtN 4636 4630 saBody)

section SaExec

variable {P : Input} {W : ℕ}

theorem saBody_exec (c : Config) (hc : WordsBounded W c) {KEYb VALb st Wb i : ℕ}
    (r1 : c.nreg 4631 = KEYb) (r2 : c.nreg 4632 = VALb) (r3 : c.nreg 4633 = st)
    (r4 : c.nreg 4634 = Wb) (r5 : c.nreg 4635 = 1) (r6 : c.nreg 4636 = i)
    (w1 : KEYb + i ≤ W) (w2 : Wb + c.nmem (KEYb + i) ≤ W) (w3 : VALb + st * i ≤ W)
    (w4 : i + 1 ≤ W)
    (w5 : c.nmem (Wb + c.nmem (KEYb + i)) + c.nmem (VALb + st * i) ≤ W) :
    ∃ c' k, Exec P W saBody c c' k ∧ k = 10 ∧ c'.nreg 4636 = i + 1 ∧
      c'.nmem = upd c.nmem (Wb + c.nmem (KEYb + i))
        (c.nmem (Wb + c.nmem (KEYb + i)) + c.nmem (VALb + st * i)) ∧
      (∀ x, (x < 4636 ∨ 4639 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold saBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5, r6]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r5, r6]
  · config_simp; simp only [r1, r2, r3, r4, r6]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The scatter-add**: with keys `KEY[j] < nk` and values `VAL[j] = mem (VALb + st · j)`
(`j < m`) outside the table `WT = [Wb, Wb + nk)`, zero at the start, and `Σ_{j<m} VAL[j] ≤ W`:
within `12 m + 4` steps `WT[k] = saF KEY VAL m k` for `k < nk`; memory outside `WT` and
registers outside `4635 … 4639` kept. -/
theorem saProg_exec (c : Config) (hc : WordsBounded W c) {m nk KEYb VALb st Wb : ℕ}
    (r0 : c.nreg 4630 = m) (r1 : c.nreg 4631 = KEYb) (r2 : c.nreg 4632 = VALb)
    (r3 : c.nreg 4633 = st) (r4 : c.nreg 4634 = Wb)
    (hkey : ∀ j < m, c.nmem (KEYb + j) < nk) (hW0 : ∀ k < nk, c.nmem (Wb + k) = 0)
    (d1 : ∀ j < m, ¬ (Wb ≤ KEYb + j ∧ KEYb + j < Wb + nk))
    (d2 : ∀ j < m, ¬ (Wb ≤ VALb + st * j ∧ VALb + st * j < Wb + nk))
    (w1 : KEYb + m ≤ W) (w2 : Wb + nk ≤ W) (w3 : ∀ j < m, VALb + st * j ≤ W) (w4 : m + 1 ≤ W)
    (hsum : ∑ j ∈ range m, c.nmem (VALb + st * j) ≤ W) :
    ∃ c' k, Exec P W saProg c c' k ∧ k ≤ 12 * m + 4 ∧
      (∀ k < nk, c'.nmem (Wb + k) =
        saF (fun j => c.nmem (KEYb + j)) (fun j => c.nmem (VALb + st * j)) m k) ∧
      (∀ a, ¬ (Wb ≤ a ∧ a < Wb + nk) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4635 ∨ 4639 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold saProg
  obtain ⟨c₁, k₁, e₁, hk₁, g5, g6, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4635 1, .constN 4636 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 4635 = 1 ∧ c₁.nreg 4636 = 0 ∧
      (∀ x, x ≠ 4635 → x ≠ 4636 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 4635 → x ≠ 4636 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  set key : ℕ → ℕ := fun j => m₀ (KEYb + j) with hkeyd
  set val : ℕ → ℕ := fun j => m₀ (VALb + st * j) with hvald
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4636 ∨ 4639 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ k < nk, c'.nmem (Wb + k) = saF key val i k) ∧
    (∀ a, ¬ (Wb ≤ a ∧ a < Wb + nk) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h75, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P) (a := 4636)
    (b := 4630) (body := saBody) J (B := 10) c₁ hw₁ g6 (by rw [q _ (by omega) (by omega), r0])
    (Nat.zero_le m) ⟨fun _ _ => rfl, fun k hk => by rw [gm₁, hW0 k hk, saF_zero],
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h75 h70 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 4636 ∨ 4639 < x) → c'.nreg x = c₁.nreg x := j1
      have e1 : c'.nmem (KEYb + i) = key i := j3 _ (d1 i hhi)
      have e2 : c'.nmem (VALb + st * i) = val i := j3 _ (d2 i hhi)
      have hk : key i < nk := hkey i hhi
      have e3 : c'.nmem (Wb + key i) = saF key val i (key i) := j2 _ hk
      have hb : saF key val i (key i) + val i ≤ W := by
        have h1 := saF_le key val (i + 1) (key i)
        rw [saF_succ, iteT rfl] at h1
        have h2 : ∑ j ∈ range (i + 1), val j ≤ ∑ j ∈ range m, val j :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
            (fun _ _ _ => Nat.zero_le _)
        have h3 : ∑ j ∈ range m, val j ≤ W := hsum
        omega
      obtain ⟨c'', t, ex, ht, h75', hm', hn', hr', hrm', ho'⟩ := saBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r3])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r4])
        (by rw [f _ (by omega), g5]) h75 (by omega) (by rw [e1]; omega) (w3 i hhi) (by omega)
        (by rw [e1, e2, e3]; exact hb)
      rw [e1, e2, e3] at hm'
      refine ⟨c'', t, ex, ht.le, h75', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], fun k hk' => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm', saF_succ]
        by_cases hkk : key i = k
        · subst hkk; rw [upd_same, iteT rfl]
        · rw [upd_other _ _ _ (by omega), j2 k hk', iteF hkk, Nat.add_zero]
      · rw [hm', upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
        exact j3 a ha)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, fun x hx => ?_, by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega)]

end SaExec

end BKMNW

end PlanarFlow
