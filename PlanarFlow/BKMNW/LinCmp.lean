module

public import PlanarFlow.BKMNW.LinRot

/-!
# The child's rotation in the child's own numbering

`crProg_childRot` gives the rotation of a child piece map in the indices of the parent
(`CN[i]`, `i` an index of the parent). The child's frame numbers its own darts `0, …, mc - 1`:

* **`lkProg`** (compaction; registers `6300 = m`, `6301 = Fb`, `6302 = CIb`, `6303 = IXb`;
  written `6304 … 6309`, the count `mc` in `6306`): for the flagged indices `i < m`
  (`F[i] > 0`) in increasing order, `CI[i] := k`, `IX[k] := i`, `k := k + 1`;
  `lkProg_exec` (`11 m + 5` steps): `CI[i] = cnt F i`, `IX[cnt F i] = i`, `mc = cnt F m`.
* **`lrProg`** (remap; registers `6310 = m`, `6311 = Fb`, `6312 = CIb`, `6313 = Ab`,
  `6314 = OUTb`; written `6315 … 6319`): `OUT[CI[i]] := CI[A[i]]` for the flagged `i`;
  `lrProg_exec` (`12 m + 5` steps).
* `cnt`, `cnt_lt_of`, `cnt_surj` (every `k < cnt F m` is `cnt F i` of a flagged `i`).
* **`chRotProg`** = `crProg; lkProg; lrProg` (layout of eleven arrays of length `m` from `A`:
  `SG | RV | LF | CF | NX | PR | CN | DF | CI | IX | OUT`), **`chRotProg_exec`**: within
  `104 m + 100` steps, with `mc = r6306` and the child's enumeration `e' k = e (IX[k])` (`k < mc`,
  without repetition, onto `Bc`): `OUT[k] < mc` and **`e' (OUT[k]) = childRot M σ B L Bc (e' k)`**
  — the rotation array of the child's frame.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The number of flagged indices below `i`. -/
def cnt (F : ℕ → ℕ) (i : ℕ) : ℕ := ((range i).filter fun j => 0 < F j).card

lemma cnt_succ (F : ℕ → ℕ) (i : ℕ) : cnt F (i + 1) = cnt F i + if 0 < F i then 1 else 0 := by
  unfold cnt
  rw [Finset.range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

lemma cnt_mono (F : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) : cnt F i ≤ cnt F j :=
  card_le_card (filter_subset_filter _ (range_subset_range.2 h))

lemma cnt_lt_of (F : ℕ → ℕ) {i j : ℕ} (h : i < j) (hi : 0 < F i) : cnt F i < cnt F j := by
  have := cnt_mono F (show i + 1 ≤ j by omega)
  rw [cnt_succ, iteT hi] at this
  omega

lemma cnt_inj (F : ℕ → ℕ) {i j : ℕ} (hi : 0 < F i) (hj : 0 < F j) (h : cnt F i = cnt F j) :
    i = j := by
  rcases lt_trichotomy i j with hl | rfl | hl
  · have := cnt_lt_of F hl hi; omega
  · rfl
  · have := cnt_lt_of F hl hj; omega

lemma cnt_surj (F : ℕ → ℕ) : ∀ m k, k < cnt F m → ∃ i < m, 0 < F i ∧ cnt F i = k
  | 0, k, h => by simp [cnt] at h
  | m + 1, k, h => by
    rw [cnt_succ] at h
    by_cases hk : k < cnt F m
    · obtain ⟨i, hi, h1, h2⟩ := cnt_surj F m k hk
      exact ⟨i, by omega, h1, h2⟩
    · split_ifs at h with hF
      · exact ⟨m, by omega, hF, by omega⟩
      · omega

section Exec

variable {P : Input} {W : ℕ}

/-! ### The compaction -/

/-- `if F[i] > 0 then (CI[i] := k; IX[k] := i; k := k + 1)`; `i := i + 1`. -/
def lkBody : Stmt :=
  .seq (block [.addN 6307 6301 6305, .loadN 6307 6307])
    (.seq (.ifLtN 6309 6307
      (block [.addN 6308 6302 6305, .storeN 6308 6306, .addN 6308 6303 6306, .storeN 6308 6305,
        .addN 6306 6306 6304])
      .skip)
      (block [.addN 6305 6305 6304]))

/-- **The compaction** of the flagged indices. -/
def lkProg : Stmt :=
  .seq (block [.constN 6304 1, .constN 6305 0, .constN 6306 0, .constN 6309 0])
    (.whileLtN 6305 6300 lkBody)

theorem lkBody_exec (c : Config) (hc : WordsBounded W c) {Fb CIb IXb i k : ℕ}
    (r1 : c.nreg 6301 = Fb) (r2 : c.nreg 6302 = CIb) (r3 : c.nreg 6303 = IXb)
    (r4 : c.nreg 6304 = 1) (r5 : c.nreg 6305 = i) (r6 : c.nreg 6306 = k) (r9 : c.nreg 6309 = 0)
    (w1 : Fb + i ≤ W) (w2 : CIb + i ≤ W) (w3 : IXb + k ≤ W) (w4 : i + 1 ≤ W) (w5 : k + 1 ≤ W) :
    ∃ c' t, Exec P W lkBody c c' t ∧ t ≤ 9 ∧ c'.nreg 6305 = i + 1 ∧
      c'.nreg 6306 = k + (if 0 < c.nmem (Fb + i) then 1 else 0) ∧
      c'.nmem = (if 0 < c.nmem (Fb + i) then upd (upd c.nmem (CIb + i) k) (IXb + k) i
        else c.nmem) ∧
      (∀ x, (x < 6305 ∨ 6308 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lkBody
  obtain ⟨c₁, k₁, e₁, hk₁, g7, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 6307 6301 6305, .loadN 6307 6307]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 6307 = c.nmem (Fb + i) ∧ (∀ x, x ≠ 6307 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; simp only [r1, r5]; omega)
    refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r1, r5]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q1 : ∀ x, x ≠ 6307 → c₁.nreg x = c.nreg x := gn₁
  have inc : ∀ d : Config, WordsBounded W d → d.nreg 6305 = i → d.nreg 6304 = 1 →
      ∃ d' t, Exec P W (block [.addN 6305 6305 6304]) d d' t ∧ t = 1 ∧ d'.nreg 6305 = i + 1 ∧
        (∀ x, x ≠ 6305 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem ∧ d'.rreg = d.rreg ∧
        d'.rmem = d.rmem ∧ d'.output = d.output := fun d hd s5 s4 => by
    exec_block
    all_goals try (config_simp; simp only [s4, s5]; omega)
    refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [s4, s5]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  by_cases hs : 0 < c.nmem (Fb + i)
  · obtain ⟨c₂, k₂, e₂, hk₂, h6, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
        Exec P W (block [.addN 6308 6302 6305, .storeN 6308 6306, .addN 6308 6303 6306,
          .storeN 6308 6305, .addN 6306 6306 6304]) c₁ c₂ k₂ ∧ k₂ = 5 ∧ c₂.nreg 6306 = k + 1 ∧
        (∀ x, x ≠ 6306 → x ≠ 6308 → c₂.nreg x = c₁.nreg x) ∧
        c₂.nmem = upd (upd c.nmem (CIb + i) k) (IXb + k) i ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
      have s2 : c₁.nreg 6302 = CIb := by rw [q1 _ (by omega), r2]
      have s3 : c₁.nreg 6303 = IXb := by rw [q1 _ (by omega), r3]
      have s4 : c₁.nreg 6304 = 1 := by rw [q1 _ (by omega), r4]
      have s5 : c₁.nreg 6305 = i := by rw [q1 _ (by omega), r5]
      have s6 : c₁.nreg 6306 = k := by rw [q1 _ (by omega), r6]
      exec_block
      all_goals try (config_simp; simp only [s2, s3, s4, s5, s6, gm₁]; omega)
      refine ⟨rfl, ?_, fun x a b => ?_, ?_, rfl, rfl, rfl⟩
      · config_simp; simp only [s4, s6]
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
      · config_simp; simp only [s2, s3, s5, s6, gm₁]
    obtain ⟨c₃, k₃, e₃, hk₃, h5, gn₃, gm₃, gr₃, grm₃, go₃⟩ := inc c₂ e₂.wb_right
      (by rw [gn₂ _ (by omega) (by omega), q1 _ (by omega), r5])
      (by rw [gn₂ _ (by omega) (by omega), q1 _ (by omega), r4])
    have t : c₁.nreg 6309 < c₁.nreg 6307 := by rw [g7, q1 _ (by omega), r9]; exact hs
    refine ⟨c₃, k₁ + (k₂ + 1 + k₃), .seq e₁ (.seq (.ifLtN_true t e₂) e₃), by omega, h5,
      by rw [gn₃ _ (by omega), h6, iteT hs], by rw [gm₃, gm₂, iteT hs], fun x hx => ?_,
      by rw [gr₃, gr₂, gr₁], by rw [grm₃, grm₂, grm₁], by rw [go₃, go₂, go₁]⟩
    rw [gn₃ x (by omega), gn₂ x (by omega) (by omega), q1 x (by omega)]
  · obtain ⟨c₃, k₃, e₃, hk₃, h5, gn₃, gm₃, gr₃, grm₃, go₃⟩ := inc c₁ hw₁
      (by rw [q1 _ (by omega), r5]) (by rw [q1 _ (by omega), r4])
    have t : ¬ c₁.nreg 6309 < c₁.nreg 6307 := by rw [g7, q1 _ (by omega), r9]; exact hs
    refine ⟨c₃, k₁ + (0 + 2 + k₃), .seq e₁ (.seq (.ifLtN_false t (.skip hw₁)) e₃), by omega,
      h5, by rw [gn₃ _ (by omega), q1 _ (by omega), r6, iteF hs]; omega, by rw [gm₃, gm₁, iteF hs],
      fun x hx => ?_, by rw [gr₃, gr₁], by rw [grm₃, grm₁], by rw [go₃, go₁]⟩
    rw [gn₃ x (by omega), q1 x (by omega)]

/-- **The compaction**: with the flags `F`, the arrays `CI`, `IX` in three disjoint regions
(`Fb + m ≤ CIb`, `CIb + m ≤ IXb`), within `11 m + 6` steps `r6306 = cnt F m`, and for every
flagged `i < m`: `CI[i] = cnt F i`, `IX[cnt F i] = i`; memory outside `[CIb, IXb + m)`,
registers outside `6304 … 6309`, reals and output kept. -/
theorem lkProg_exec (c : Config) (hc : WordsBounded W c) {m Fb CIb IXb : ℕ}
    (r0 : c.nreg 6300 = m) (r1 : c.nreg 6301 = Fb) (r2 : c.nreg 6302 = CIb)
    (r3 : c.nreg 6303 = IXb) (l1 : Fb + m ≤ CIb) (l2 : CIb + m ≤ IXb) (l3 : IXb + m ≤ W)
    (w4 : m + 1 ≤ W) :
    ∃ c' t, Exec P W lkProg c c' t ∧ t ≤ 11 * m + 6 ∧
      c'.nreg 6306 = cnt (fun j => c.nmem (Fb + j)) m ∧
      (∀ i < m, 0 < c.nmem (Fb + i) →
        c'.nmem (CIb + i) = cnt (fun j => c.nmem (Fb + j)) i ∧
        c'.nmem (IXb + cnt (fun j => c.nmem (Fb + j)) i) = i) ∧
      (∀ a, ¬ (CIb ≤ a ∧ a < IXb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6304 ∨ 6309 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lkProg
  obtain ⟨c₁, k₁, e₁, hk₁, g4, g5, g6, g9, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 6304 1, .constN 6305 0, .constN 6306 0, .constN 6309 0])
        c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg 6304 = 1 ∧ c₁.nreg 6305 = 0 ∧ c₁.nreg 6306 = 0 ∧ c₁.nreg 6309 = 0 ∧
      (∀ x, x ≠ 6304 → x ≠ 6305 → x ≠ 6306 → x ≠ 6309 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x a b d f => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 6304 ∨ 6309 < x) → c₁.nreg x = c.nreg x := fun x hx =>
    gn₁ x (by omega) (by omega) (by omega) (by omega)
  set m₀ := c.nmem with hm₀
  set F : ℕ → ℕ := fun j => m₀ (Fb + j) with hF
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 6305 ∨ 6308 < x) → x ≠ 6306 → c'.nreg x = c₁.nreg x) ∧
    c'.nreg 6306 = cnt F i ∧
    (∀ j < i, 0 < F j → c'.nmem (CIb + j) = cnt F j ∧ c'.nmem (IXb + cnt F j) = j) ∧
    (∀ a, ¬ (CIb ≤ a ∧ a < IXb + m) → c'.nmem a = m₀ a) ∧
    (∀ a, CIb + i ≤ a → a < CIb + m → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h75, j1, j2, j3, j4, j5, j6, j7, j8⟩ := lnRange (P := P)
    (a := 6305) (b := 6300) (body := lkBody) J (B := 9) c₁ hw₁ g5 (by rw [q _ (by omega), r0])
    (Nat.zero_le m) ⟨fun _ _ _ => rfl, by rw [g6]; rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], fun a _ _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h75 h70 ⟨j1, j2, j3, j4, j5, j6, j7, j8⟩ => by
      have f : ∀ x, (x < 6305 ∨ 6308 < x) → x ≠ 6306 → c'.nreg x = c₁.nreg x := j1
      have eF : c'.nmem (Fb + i) = F i := j4 _ (fun h => by omega)
      have hc : cnt F i ≤ i := by
        unfold cnt
        exact (card_filter_le _ _).trans (by simp)
      obtain ⟨c'', t, ex, ht, h75', h76', hm', hn', hr', hrm', ho'⟩ := lkBody_exec (P := P) c' hw
        (by rw [f _ (by omega) (by omega), q _ (by omega), r1])
        (by rw [f _ (by omega) (by omega), q _ (by omega), r2])
        (by rw [f _ (by omega) (by omega), q _ (by omega), r3])
        (by rw [f _ (by omega) (by omega), g4]) h75 j2
        (by rw [f _ (by omega) (by omega), g9]) (by omega) (by omega) (by omega) (by omega)
        (by omega)
      rw [eF] at hm' h76'
      refine ⟨c'', t, ex, ht, h75', by rw [hn' _ (by omega)]; exact h70,
        fun x hx hx6 => by rw [hn' x hx, f x hx hx6], by rw [h76', cnt_succ], ?_, ?_, ?_,
        by rw [hr', j6], by rw [hrm', j7], by rw [ho', j8]⟩
      · intro j hj hFj
        rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · obtain ⟨a1, a2⟩ := j3 j hj hFj
          have hlt := cnt_lt_of F hj hFj
          split_ifs with hFi
          · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
              upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
            exact ⟨a1, a2⟩
          · exact ⟨a1, a2⟩
        · rw [iteT hFj, upd_other _ _ _ (by omega), upd_same, upd_same]; exact ⟨rfl, rfl⟩
      · intro a ha
        rw [hm']
        split_ifs
        · rw [upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩),
            upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
          exact j4 a ha
        · exact j4 a ha
      · intro a h1 h2
        rw [hm']
        split_ifs
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
          exact j5 a (by omega) h2
        · exact j5 a (by omega) h2)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, j4, fun x hx => ?_, by rw [j6, gr₁],
    by rw [j7, grm₁], by rw [j8, go₁]⟩
  rw [j1 x (by omega) (by omega), q x (by omega)]

/-! ### The remap -/

/-- `if F[i] > 0 then OUT[CI[i]] := CI[A[i]]`; `i := i + 1`. -/
def lrBody : Stmt :=
  .seq (block [.addN 6317 6311 6316, .loadN 6317 6317])
    (.seq (.ifLtN 6319 6317
      (block [.addN 6317 6313 6316, .loadN 6317 6317, .addN 6317 6312 6317, .loadN 6317 6317,
        .addN 6318 6312 6316, .loadN 6318 6318, .addN 6318 6314 6318, .storeN 6318 6317])
      .skip)
      (block [.addN 6316 6316 6315]))

/-- **The remap** `OUT[CI[i]] := CI[A[i]]` for the flagged `i < m`. -/
def lrProg : Stmt :=
  .seq (block [.constN 6315 1, .constN 6316 0, .constN 6319 0]) (.whileLtN 6316 6310 lrBody)

theorem lrBody_exec (c : Config) (hc : WordsBounded W c) {Fb CIb Ab OUTb i : ℕ}
    (r1 : c.nreg 6311 = Fb) (r2 : c.nreg 6312 = CIb) (r3 : c.nreg 6313 = Ab)
    (r4 : c.nreg 6314 = OUTb) (r5 : c.nreg 6315 = 1) (r6 : c.nreg 6316 = i)
    (r9 : c.nreg 6319 = 0) (w1 : Fb + i ≤ W) (w4 : i + 1 ≤ W)
    (w2 : 0 < c.nmem (Fb + i) → Ab + i ≤ W ∧ CIb + c.nmem (Ab + i) ≤ W ∧ CIb + i ≤ W ∧
      OUTb + c.nmem (CIb + i) ≤ W) :
    ∃ c' t, Exec P W lrBody c c' t ∧ t ≤ 12 ∧ c'.nreg 6316 = i + 1 ∧
      c'.nmem = (if 0 < c.nmem (Fb + i) then
        upd c.nmem (OUTb + c.nmem (CIb + i)) (c.nmem (CIb + c.nmem (Ab + i))) else c.nmem) ∧
      (∀ x, (x < 6316 ∨ 6318 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lrBody
  obtain ⟨c₁, k₁, e₁, hk₁, g7, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 6317 6311 6316, .loadN 6317 6317]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 6317 = c.nmem (Fb + i) ∧ (∀ x, x ≠ 6317 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; simp only [r1, r6]; omega)
    refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r1, r6]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q1 : ∀ x, x ≠ 6317 → c₁.nreg x = c.nreg x := gn₁
  have inc : ∀ d : Config, WordsBounded W d → d.nreg 6316 = i → d.nreg 6315 = 1 →
      ∃ d' t, Exec P W (block [.addN 6316 6316 6315]) d d' t ∧ t = 1 ∧ d'.nreg 6316 = i + 1 ∧
        (∀ x, x ≠ 6316 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem ∧ d'.rreg = d.rreg ∧
        d'.rmem = d.rmem ∧ d'.output = d.output := fun d hd s6 s5 => by
    exec_block
    all_goals try (config_simp; simp only [s5, s6]; omega)
    refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [s5, s6]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  by_cases hs : 0 < c.nmem (Fb + i)
  · obtain ⟨a1, a2, a3, a4⟩ := w2 hs
    obtain ⟨c₂, k₂, e₂, hk₂, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
        Exec P W (block [.addN 6317 6313 6316, .loadN 6317 6317, .addN 6317 6312 6317,
          .loadN 6317 6317, .addN 6318 6312 6316, .loadN 6318 6318, .addN 6318 6314 6318,
          .storeN 6318 6317]) c₁ c₂ k₂ ∧ k₂ = 8 ∧
        (∀ x, x ≠ 6317 → x ≠ 6318 → c₂.nreg x = c₁.nreg x) ∧
        c₂.nmem = upd c.nmem (OUTb + c.nmem (CIb + i)) (c.nmem (CIb + c.nmem (Ab + i))) ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
      have s2 : c₁.nreg 6312 = CIb := by rw [q1 _ (by omega), r2]
      have s3 : c₁.nreg 6313 = Ab := by rw [q1 _ (by omega), r3]
      have s4 : c₁.nreg 6314 = OUTb := by rw [q1 _ (by omega), r4]
      have s6 : c₁.nreg 6316 = i := by rw [q1 _ (by omega), r6]
      exec_block
      all_goals try (config_simp; simp only [s2, s3, s4, s6, gm₁]; omega)
      refine ⟨rfl, fun x a b => ?_, ?_, rfl, rfl, rfl⟩
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
      · config_simp; simp only [s2, s3, s4, s6, gm₁]
    obtain ⟨c₃, k₃, e₃, hk₃, h6, gn₃, gm₃, gr₃, grm₃, go₃⟩ := inc c₂ e₂.wb_right
      (by rw [gn₂ _ (by omega) (by omega), q1 _ (by omega), r6])
      (by rw [gn₂ _ (by omega) (by omega), q1 _ (by omega), r5])
    have t : c₁.nreg 6319 < c₁.nreg 6317 := by rw [g7, q1 _ (by omega), r9]; exact hs
    refine ⟨c₃, k₁ + (k₂ + 1 + k₃), .seq e₁ (.seq (.ifLtN_true t e₂) e₃), by omega, h6,
      by rw [gm₃, gm₂, iteT hs], fun x hx => ?_, by rw [gr₃, gr₂, gr₁],
      by rw [grm₃, grm₂, grm₁], by rw [go₃, go₂, go₁]⟩
    rw [gn₃ x (by omega), gn₂ x (by omega) (by omega), q1 x (by omega)]
  · obtain ⟨c₃, k₃, e₃, hk₃, h6, gn₃, gm₃, gr₃, grm₃, go₃⟩ := inc c₁ hw₁
      (by rw [q1 _ (by omega), r6]) (by rw [q1 _ (by omega), r5])
    have t : ¬ c₁.nreg 6319 < c₁.nreg 6317 := by rw [g7, q1 _ (by omega), r9]; exact hs
    refine ⟨c₃, k₁ + (0 + 2 + k₃), .seq e₁ (.seq (.ifLtN_false t (.skip hw₁)) e₃), by omega,
      h6, by rw [gm₃, gm₁, iteF hs], fun x hx => ?_, by rw [gr₃, gr₁], by rw [grm₃, grm₁],
      by rw [go₃, go₁]⟩
    rw [gn₃ x (by omega), q1 x (by omega)]

/-- **The remap**: with `CI` injective on the flagged indices and below `mc ≤ m`, `OUT` of
length `m` after the other arrays, every `A[i]` of a flagged `i` below `m`: within
`14 m + 5` steps `OUT[CI[i]] = CI[A[i]]` for every flagged `i < m`; memory outside
`[OUTb, OUTb + m)`, registers outside `6315 … 6319`, reals and output kept. -/
theorem lrProg_exec (c : Config) (hc : WordsBounded W c) {m Fb CIb Ab OUTb : ℕ}
    (r0 : c.nreg 6310 = m) (r1 : c.nreg 6311 = Fb) (r2 : c.nreg 6312 = CIb)
    (r3 : c.nreg 6313 = Ab) (r4 : c.nreg 6314 = OUTb)
    (l1 : Fb + m ≤ OUTb) (l2 : CIb + m ≤ OUTb) (l3 : Ab + m ≤ OUTb) (l4 : OUTb + m ≤ W)
    (w4 : m + 1 ≤ W)
    (hA : ∀ i < m, 0 < c.nmem (Fb + i) → c.nmem (Ab + i) < m)
    (hCI : ∀ i < m, 0 < c.nmem (Fb + i) → c.nmem (CIb + i) < m)
    (hinj : ∀ i < m, ∀ j < m, 0 < c.nmem (Fb + i) → 0 < c.nmem (Fb + j) →
      c.nmem (CIb + i) = c.nmem (CIb + j) → i = j) :
    ∃ c' t, Exec P W lrProg c c' t ∧ t ≤ 14 * m + 5 ∧
      (∀ i < m, 0 < c.nmem (Fb + i) →
        c'.nmem (OUTb + c.nmem (CIb + i)) = c.nmem (CIb + c.nmem (Ab + i))) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6315 ∨ 6319 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lrProg
  obtain ⟨c₁, k₁, e₁, hk₁, g5, g6, g9, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 6315 1, .constN 6316 0, .constN 6319 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 6315 = 1 ∧ c₁.nreg 6316 = 0 ∧ c₁.nreg 6319 = 0 ∧
      (∀ x, x ≠ 6315 → x ≠ 6316 → x ≠ 6319 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 6315 ∨ 6319 < x) → c₁.nreg x = c.nreg x := fun x hx =>
    gn₁ x (by omega) (by omega) (by omega)
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 6316 ∨ 6318 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, 0 < m₀ (Fb + j) → c'.nmem (OUTb + m₀ (CIb + j)) = m₀ (CIb + m₀ (Ab + j))) ∧
    (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = m₀ a) ∧
    (∀ a, (∀ j < i, 0 < m₀ (Fb + j) → a ≠ OUTb + m₀ (CIb + j)) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h76, j1, j2, j3, j9, j4, j5, j6⟩ := lnRange (P := P) (a := 6316)
    (b := 6310) (body := lrBody) J (B := 12) c₁ hw₁ g6 (by rw [q _ (by omega), r0])
    (Nat.zero_le m) ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h76 h70 ⟨j1, j2, j3, j9, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 6316 ∨ 6318 < x) → c'.nreg x = c₁.nreg x := j1
      have eF : c'.nmem (Fb + i) = m₀ (Fb + i) := j3 _ (fun h => by omega)
      have eA : c'.nmem (Ab + i) = m₀ (Ab + i) := j3 _ (fun h => by omega)
      have eC : c'.nmem (CIb + i) = m₀ (CIb + i) := j3 _ (fun h => by omega)
      have eCA : 0 < m₀ (Fb + i) → c'.nmem (CIb + m₀ (Ab + i)) = m₀ (CIb + m₀ (Ab + i)) :=
        fun hs => j3 _ (fun h => by have := hA i hhi hs; omega)
      obtain ⟨c'', t, ex, ht, h76', hm', hn', hr', hrm', ho'⟩ := lrBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega), r3])
        (by rw [f _ (by omega), q _ (by omega), r4])
        (by rw [f _ (by omega), g5]) h76 (by rw [f _ (by omega), g9]) (by omega) (by omega)
        (fun hs => by
          rw [eF] at hs; rw [eA, eC]
          have := hA i hhi hs; have := hCI i hhi hs
          exact ⟨by omega, by omega, by omega, by omega⟩)
      rw [eF] at hm'
      refine ⟨c'', t, ex, ht, h76', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj hs => ?_, fun a ha => ?_,
        fun a ha => ?_, by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · split_ifs with hsi
          · rw [eC, upd_other _ _ _ (fun h => by
              have := hinj j (by omega) i hhi hs hsi (by omega); omega)]
            exact j2 j hj hs
          · exact j2 j hj hs
        · rw [iteT hs, eC, upd_same, eA, eCA hs]
      · rw [hm']
        split_ifs with hsi
        · rw [upd_other _ _ _ (fun h => ha ⟨by omega, by
            rw [eC] at h; have := hCI i hhi hsi; omega⟩)]
          exact j3 a ha
        · exact j3 a ha
      · rw [hm']
        split_ifs with hsi
        · rw [upd_other _ _ _ (by rw [eC]; exact ha i (by omega) hsi)]
          exact j9 a (fun j hj hs => ha j (by omega) hs)
        · exact j9 a (fun j hj hs => ha j (by omega) hs))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, fun x hx => ?_, by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega)]

end Exec

lemma cnt_le (F : ℕ → ℕ) (i : ℕ) : cnt F i ≤ i := by
  unfold cnt; exact (card_filter_le _ _).trans (by simp)

/-! ### The child's rotation array -/

/-- The bases `A + 8 m` (`CI`), `A + 9 m` (`IX`), `A + 10 m` (`OUT`), `A + 3 m` (`CF`),
`A + 6 m` (`CN`), and the registers of the compaction. -/
def chS1 : Stmt := block [.addN 6324 6200 6200, .addN 6325 6324 6324, .addN 6326 6325 6325,
  .addN 6320 6201 6326, .addN 6321 6320 6200, .addN 6322 6321 6200, .addN 6327 6201 6324,
  .addN 6327 6327 6200, .addN 6328 6201 6325, .addN 6328 6328 6324, .copyN 6300 6200,
  .copyN 6301 6327, .copyN 6302 6320, .copyN 6303 6321]

/-- The registers of the remap `OUT[CI[i]] := CI[CN[i]]`. -/
def chS2 : Stmt :=
  block [.copyN 6310 6200, .copyN 6311 6327, .copyN 6312 6320, .copyN 6313 6328, .copyN 6314 6322]

/-- **The rotation array of a child's frame**: `crProg`, then the compaction of the child's
darts (flags `CF`) and the remap of `CN` into the child's numbering. -/
def chRotProg : Stmt := .seq crProg (.seq chS1 (.seq lkProg (.seq chS2 lrProg)))

section Exec

variable {P : Input} {W : ℕ}


theorem chS1_exec (c : Config) (hc : WordsBounded W c) {m A : ℕ} (s0 : c.nreg 6200 = m)
    (s1 : c.nreg 6201 = A) (hW : A + 11 * m ≤ W) :
    ∃ c2 k2, Exec P W chS1 c c2 k2 ∧ k2 = 14 ∧ c2.nreg 6300 = m ∧
      c2.nreg 6301 = A + 3 * m ∧ c2.nreg 6302 = A + 8 * m ∧ c2.nreg 6303 = A + 9 * m ∧
      c2.nreg 6320 = A + 8 * m ∧ c2.nreg 6321 = A + 9 * m ∧ c2.nreg 6322 = A + 10 * m ∧
      c2.nreg 6327 = A + 3 * m ∧ c2.nreg 6328 = A + 6 * m ∧
      (∀ x, (x < 6300 ∨ 6328 < x) → c2.nreg x = c.nreg x) ∧ c2.nmem = c.nmem ∧
      c2.rreg = c.rreg ∧ c2.rmem = c.rmem ∧ c2.output = c.output := by
  unfold chS1
  exec_block
  all_goals try (config_simp; simp only [s0, s1]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [s0, s1])
  all_goals (try omega)
  all_goals try (simp (disch := omega) only [upd_other])

theorem chS2_exec (c : Config) (hc : WordsBounded W c) {m A : ℕ} (s0 : c.nreg 6200 = m)
    (s7 : c.nreg 6327 = A + 3 * m) (s20 : c.nreg 6320 = A + 8 * m)
    (s8 : c.nreg 6328 = A + 6 * m) (s22 : c.nreg 6322 = A + 10 * m) :
    ∃ c4 k4, Exec P W chS2 c c4 k4 ∧ k4 = 5 ∧ c4.nreg 6310 = m ∧
      c4.nreg 6311 = A + 3 * m ∧ c4.nreg 6312 = A + 8 * m ∧ c4.nreg 6313 = A + 6 * m ∧
      c4.nreg 6314 = A + 10 * m ∧
      (∀ x, (x < 6310 ∨ 6314 < x) → c4.nreg x = c.nreg x) ∧ c4.nmem = c.nmem ∧
      c4.rreg = c.rreg ∧ c4.rmem = c.rmem ∧ c4.output = c.output := by
  unfold chS2
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [s0, s7, s20, s8, s22])
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

set_option maxHeartbeats 1000000 in
/-- **The rotation of a child piece map in the child's numbering** (see the module docstring):
with the hypotheses of `crProg_childRot` and room for eleven arrays (`A + 11 m ≤ W`), within
`104 m + 100` steps, `mc = r6306 ≤ m`, the child's enumeration `e' k = e (IX[k])` (`k < mc`) lists
the darts of `Bc` once each, and `OUT[k] < mc`, `e' (OUT[k]) = childRot M σ B L Bc (e' k)`. -/
theorem chRotProg_exec {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] (M : CombMap D V F)
    (σ : Perm D) (B : Finset D) (L : List D) (Bc : Finset D)
    (c : Config) (hc : WordsBounded W c) {m A : ℕ} (r0 : c.nreg 6200 = m)
    (r1 : c.nreg 6201 = A) (hW : A + 11 * m ≤ W) (hm : m + 2 ≤ W)
    {e : ℕ → D} (he : ∀ i < m, ∀ j < m, e i = e j → i = j) (heB : ∀ i < m, e i ∈ B)
    (hBe : ∀ x ∈ B, ∃ i < m, e i = x)
    (hσ : Stable σ B) (hrB : ∀ x ∈ B, M.rev x ∈ B) (hrL : ∀ x ∈ L, M.rev x ∈ L)
    (hBc : Bc ⊆ B \ L.toFinset)
    (hSG : ∀ i < m, c.nmem (A + i) < m ∧ e (c.nmem (A + i)) = σ (e i))
    (hRV : ∀ i < m, c.nmem (A + m + i) < m ∧ e (c.nmem (A + m + i)) = M.rev (e i))
    (hLF : ∀ i < m, c.nmem (A + 2 * m + i) = if e i ∈ L.toFinset then 1 else 0)
    (hCF : ∀ i < m, c.nmem (A + 3 * m + i) = if e i ∈ Bc then 1 else 0) :
    ∃ c' k, Exec P W chRotProg c c' k ∧ k ≤ 104 * m + 100 ∧ c'.nreg 6306 ≤ m ∧
      (∀ k < c'.nreg 6306, c'.nmem (A + 9 * m + k) < m ∧ e (c'.nmem (A + 9 * m + k)) ∈ Bc) ∧
      (∀ x ∈ Bc, ∃ k < c'.nreg 6306, e (c'.nmem (A + 9 * m + k)) = x) ∧
      (∀ k < c'.nreg 6306, ∀ k' < c'.nreg 6306,
        e (c'.nmem (A + 9 * m + k)) = e (c'.nmem (A + 9 * m + k')) → k = k') ∧
      (∀ k < c'.nreg 6306, c'.nmem (A + 10 * m + k) < c'.nreg 6306 ∧
        e (c'.nmem (A + 9 * m + c'.nmem (A + 10 * m + k))) =
          childRot M σ B L Bc (e (c'.nmem (A + 9 * m + k)))) ∧
      (∀ a, ¬ (A + 4 * m ≤ a ∧ a < A + 11 * m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6200 ∨ 6328 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c1, k1, x1, hk1, cn1, mk1, rk1, rr1, rm1, ro1⟩ := crProg_childRot (P := P) M σ B L Bc c hc
    r0 r1 (by omega) hm he heB hBe hσ hrB hrL hBc hSG hRV hLF hCF
  have s0 : c1.nreg 6200 = m := by rw [rk1 _ (by omega), r0]
  have s1 : c1.nreg 6201 = A := by rw [rk1 _ (by omega), r1]
  have hw1 := x1.wb_right
  obtain ⟨c2, k2, x2, hk2, t0, t1, t2, t3, t20, t21, t22, t27, t28, gn2, gm2, gr2, grm2, go2⟩ :=
    chS1_exec (P := P) c1 hw1 s0 s1 (by omega)
  obtain ⟨F, hFd⟩ : ∃ F : ℕ → ℕ, F = fun j => c.nmem (A + 3 * m + j) := ⟨_, rfl⟩
  have hF1 : ∀ i < m, c1.nmem (A + 3 * m + i) = F i := fun i hi => by
    rw [hFd]; exact mk1 _ (fun h => by omega)
  have hFiff : ∀ i < m, 0 < F i ↔ e i ∈ Bc := fun i hi => by
    rw [hFd]; show 0 < c.nmem (A + 3 * m + i) ↔ _
    rw [hCF i hi]; split_ifs with h <;> simp [h]
  obtain ⟨c3, k3, x3, hk3, u6, ul, uk, urk, urr, urm, uro⟩ := lkProg_exec (P := P) c2 x2.wb_right
    t0 t1 t2 t3 (by omega) (by omega) (by omega) (by omega)
  have cntEq : ∀ i ≤ m, cnt (fun j => c2.nmem (A + 3 * m + j)) i = cnt F i := fun i hi => by
    unfold cnt; congr 1
    apply filter_congr; intro j hj; rw [mem_range] at hj
    show 0 < c2.nmem (A + 3 * m + j) ↔ 0 < F j
    rw [gm2, hF1 j (by omega)]
  rw [cntEq m le_rfl] at u6
  have ul' : ∀ i < m, 0 < F i → c3.nmem (A + 8 * m + i) = cnt F i ∧
      c3.nmem (A + 9 * m + cnt F i) = i := fun i hi hFi => by
    have := ul i hi (by rw [gm2, hF1 i hi]; exact hFi)
    rw [cntEq i hi.le] at this; exact this
  have hw3 := x3.wb_right
  have v : ∀ x, (x < 6300 ∨ 6328 < x) → c3.nreg x = c2.nreg x := fun x hx => urk x (by omega)
  obtain ⟨c4, k4, x4, hk4, w0, w1, w2, w3, w4, gn4, gm4, gr4, grm4, go4⟩ :=
    chS2_exec (P := P) c3 hw3 (by rw [urk 6200 (by omega), gn2 6200 (by omega), s0])
      (by rw [urk 6327 (by omega), t27]) (by rw [urk 6320 (by omega), t20])
      (by rw [urk 6328 (by omega), t28]) (by rw [urk 6322 (by omega), t22])
  -- the memory of `c3` on the arrays read by the remap
  have m3F : ∀ i < m, c3.nmem (A + 3 * m + i) = F i := fun i hi => by
    rw [uk _ (fun h => by omega), gm2, hF1 i hi]
  have m3C : ∀ i < m, c3.nmem (A + 6 * m + i) = c1.nmem (A + 6 * m + i) := fun i hi => by
    rw [uk _ (fun h => by omega), gm2]
  have cnB : ∀ i < m, 0 < F i → c1.nmem (A + 6 * m + i) < m ∧
      e (c1.nmem (A + 6 * m + i)) = childRot M σ B L Bc (e i) := fun i hi hFi =>
    cn1 i hi ((hFiff i hi).1 hFi)
  have cnF : ∀ i < m, 0 < F i → 0 < F (c1.nmem (A + 6 * m + i)) := fun i hi hFi => by
    obtain ⟨a1, a2⟩ := cnB i hi hFi
    rw [hFiff _ a1, a2]
    unfold childRot
    exact ret_mem ((hFiff i hi).1 hFi)
  obtain ⟨c5, k5, x5, hk5, o1, o2, o3, o4, o5, o6⟩ := lrProg_exec (P := P) c4 x4.wb_right w0 w1 w2
    w3 w4 (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi hs => by
      rw [gm4, m3F i hi] at hs; rw [gm4, m3C i hi]; exact (cnB i hi hs).1)
    (fun i hi hs => by
      rw [gm4, m3F i hi] at hs; rw [gm4, (ul' i hi hs).1]
      have := cnt_le F i; omega)
    (fun i hi j hj hsi hsj h => by
      rw [gm4, m3F i hi] at hsi; rw [gm4, m3F j hj] at hsj
      rw [gm4, (ul' i hi hsi).1, (ul' j hj hsj).1] at h
      exact cnt_inj F hsi hsj h)
  rw [gm4] at o1 o2
  have m5 : ∀ a, ¬ (A + 10 * m ≤ a ∧ a < A + 10 * m + m) → c5.nmem a = c3.nmem a := o2
  have r6 : c5.nreg 6306 = cnt F m := by
    rw [o3 _ (by omega), gn4 _ (by omega), u6]
  have IXv : ∀ i < m, 0 < F i → c5.nmem (A + 9 * m + cnt F i) = i := fun i hi hFi => by
    rw [m5 _ (fun h => by have := cnt_le F i; omega)]; exact (ul' i hi hFi).2
  have hmc : cnt F m ≤ m := cnt_le F m
  refine ⟨c5, k1 + (k2 + (k3 + (k4 + k5))), .seq x1 (.seq x2 (.seq x3 (.seq x4 x5))), by omega,
    by rw [r6]; exact hmc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [r6] at hk
    obtain ⟨i, hi, hFi, rfl⟩ := cnt_surj F m k hk
    rw [IXv i hi hFi]
    exact ⟨hi, (hFiff i hi).1 hFi⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := hBe x (mem_sdiff.1 (hBc hx)).1
    have hFi := (hFiff i hi).2 hx
    exact ⟨cnt F i, by rw [r6]; exact cnt_lt_of F hi hFi, by rw [IXv i hi hFi]⟩
  · intro k hk k' hk' h
    rw [r6] at hk hk'
    obtain ⟨i, hi, hFi, rfl⟩ := cnt_surj F m k hk
    obtain ⟨i', hi', hFi', rfl⟩ := cnt_surj F m k' hk'
    rw [IXv i hi hFi, IXv i' hi' hFi'] at h
    rw [he i hi i' hi' h]
  · intro k hk
    rw [r6] at hk ⊢
    obtain ⟨i, hi, hFi, rfl⟩ := cnt_surj F m k hk
    have h1 := o1 i hi (by rw [m3F i hi]; exact hFi)
    rw [(ul' i hi hFi).1, m3C i hi] at h1
    obtain ⟨a1, a2⟩ := cnB i hi hFi
    have hF' := cnF i hi hFi
    rw [(ul' _ a1 hF').1] at h1
    rw [h1, IXv _ a1 hF', IXv i hi hFi, a2]
    exact ⟨cnt_lt_of F a1 hF', rfl⟩
  · intro a ha
    have g1 : ¬ (A + 10 * m ≤ a ∧ a < A + 10 * m + m) := by
      rintro ⟨h1, h2⟩; exact ha ⟨by omega, by omega⟩
    have g2 : ¬ (A + 8 * m ≤ a ∧ a < A + 9 * m + m) := by
      rintro ⟨h1, h2⟩; exact ha ⟨by omega, by omega⟩
    have g3 : ¬ (A + 4 * m ≤ a ∧ a < A + 8 * m) := by
      rintro ⟨h1, h2⟩; exact ha ⟨by omega, by omega⟩
    have e1 := m5 a g1
    have e2 := uk a g2
    have e3 := mk1 a g3
    rw [e1, e2, gm2, e3]
  · intro x hx
    rw [o3 x (by omega), gn4 x (by omega), urk x (by omega), gn2 x (by omega), rk1 x (by omega)]
  · rw [o4, gr4, urr, gr2, rr1]
  · rw [o5, grm4, urm, grm2, rm1]
  · rw [o6, go4, uro, go2, ro1]

end Exec

end BKMNW

end PlanarFlow
