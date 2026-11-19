module

public import PlanarFlow.BKMNW.LgKey
public import PlanarFlow.BKMNW.ScTouch

/-!
# The pre-filter of the holes: relabel the hole labels by the touching holes, in `O(n + k)`

`scProg` costs `|Hs| · (160 n + 36)` per level (the hole loop `hlProg` tests every hole). By
`scertD_tHs` (`ScTouch.lean`) the recursion may run on the list `tHs B Hs` of the holes touching
the enumerated darts `B` (at most `nTouch ≤ 6` on the pieces of the decomposition). **`tfProg`**
rewrites the hole labels `TH` (`TH[i] = j + 1` iff the tail of `e i` lies in `Hs[j]`, `0` off the
holes) into the labels of `tHs B Hs`, and the hole count `r4874` into `|tHs B Hs|`:

1. `WT[0 … k] := 0`; scatter-add `WT[TH[i]] += 1` (`saProg`): `F[j] = WT[j + 1] > 0` iff the hole
   `j` touches `B`;
2. the compaction `lkProg` of the flags `F`: `CI[j] = cnt F j` for the touching `j`, `mc = cnt F k`;
3. `TH2[i] := (TH[i] > 0 ? CI[TH[i] - 1] + 1 : 0)`, `TH[i] := TH2[i]`, `r4874 := mc`.

* pure: `cnt_shift`, **`filter_getD_cnt`**, **`length_filter_cnt`** (the `j`-th element of a filtered
  list is the element of index `v` with `cnt F v = j`), `saF_one_pos`;
* `nlF`, `vbNL`, `vbCP`, `tf0 … tf6`, **`tfProg`**; `vbNL_exec`, `vbCP_exec`, `tf0_exec`, …;
* **`tfProg_exec`** (within `32 n + 17 k + 60` steps): for some flags `F` with
  `0 < F j ↔ ∃ i < n, TH[i] = j + 1` (`j < k`), `r4874 = cnt F k` and
  `TH'[i] = (TH[i] > 0 ? cnt F (TH[i] - 1) + 1 : 0)`; memory outside `TH` and the scratch
  `[Zb, Zb + 3 k + n + 2)` kept; registers outside `tfW` kept (`4630 … 4634` restored);
* **`tf_th`**: the new labels are those of `tHs B Hs` (`LvIn.th` for the touching holes).

Registers: inputs `4840 = n`, `4842 = Tb` (the labels), `4874 = k`, `5830 = Zb`; written `4874`,
`5831 … 5844`, `4635 … 4639`, `6300 … 6309`, `6520 … 6529`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver Relation

/-! ### The `j`-th element of a filtered list -/

lemma cnt_shift (F : ℕ → ℕ) (j : ℕ) :
    cnt F (j + 1) = cnt (fun i => F (i + 1)) j + if 0 < F 0 then 1 else 0 := by
  induction j with
  | zero => rw [cnt_succ]; simp [cnt]
  | succ j ih => rw [cnt_succ, ih, cnt_succ]; omega

/-- **The length of a filtered list** is the number of flagged indices. -/
lemma length_filter_cnt {α : Type*} (p : α → Bool) (d : α) :
    ∀ (l : List α) (F : ℕ → ℕ), (∀ j < l.length, (0 < F j ↔ p (l.getD j d) = true)) →
      (l.filter p).length = cnt F l.length
  | [], F, _ => by simp [cnt]
  | a :: l, F, hF => by
    have ih := length_filter_cnt p d l (fun i => F (i + 1)) (fun j hj => by
      simpa using hF (j + 1) (by simp; omega))
    have h0 := hF 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    rw [List.length_cons, cnt_shift, ← ih, List.filter_cons]
    by_cases hp : p a = true
    · rw [iteT hp, iteT (h0.2 hp)]; simp
    · have : ¬ 0 < F 0 := fun h => hp (h0.1 h)
      rw [iteF hp, iteF this]; rfl

/-- **The element of the filtered list at the count of a flagged index** is the element at that
index. -/
lemma filter_getD_cnt {α : Type*} (p : α → Bool) (d : α) :
    ∀ (l : List α) (F : ℕ → ℕ), (∀ j < l.length, (0 < F j ↔ p (l.getD j d) = true)) →
      ∀ v < l.length, p (l.getD v d) = true → (l.filter p).getD (cnt F v) d = l.getD v d
  | [], F, _, v, hv, _ => absurd hv (by simp)
  | a :: l, F, hF, v, hv, hpv => by
    have hF' : ∀ j < l.length, (0 < F (j + 1) ↔ p (l.getD j d) = true) := fun j hj => by
      simpa using hF (j + 1) (by simp; omega)
    have h0 := hF 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    rw [List.filter_cons]
    rcases v with _ | v
    · simp only [List.getD_cons_zero] at hpv ⊢
      rw [iteT hpv]
      simp [cnt]
    · simp only [List.getD_cons_succ] at hpv ⊢
      have ih := filter_getD_cnt p d l (fun i => F (i + 1)) hF' v (by simp at hv; omega) hpv
      rw [cnt_shift]
      by_cases hp : p a = true
      · rw [iteT hp, iteT (h0.2 hp)]
        simpa using ih
      · have : ¬ 0 < F 0 := fun h => hp (h0.1 h)
        rw [iteF hp, iteF this]
        simpa using ih

lemma saF_one_pos (key : ℕ → ℕ) (n k : ℕ) :
    0 < saF key (fun _ => 1) n k ↔ ∃ i < n, key i = k := by
  unfold saF
  rw [sum_const, smul_eq_mul, mul_one, card_pos]
  constructor
  · rintro ⟨i, hi⟩
    rw [mem_filter, mem_range] at hi
    exact ⟨i, hi.1, hi.2⟩
  · rintro ⟨i, hi, hk⟩
    exact ⟨i, mem_filter.2 ⟨mem_range.2 hi, hk⟩⟩

/-- **The relabelled hole labels are those of the touching holes**: if `TH[i] = j + 1 ↔ tail (e i) ∈
Hs[j]` (`TH[i] ≤ |Hs|`), `e` maps `[0, n)` onto `B`, and the flags `F` mark the labels that occur,
then the labels `TH[i] > 0 ? cnt F (TH[i] - 1) + 1 : 0` are those of `tHs B Hs`, and
`cnt F |Hs| = |tHs B Hs|`. -/
theorem tf_th {D V F' : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F'] [DecidableEq F'] {M : CombMap D V F'} {B : Finset D} {Hs : List (Finset V)}
    {e : ℕ → D} {n : ℕ} (hmem : ∀ i < n, e i ∈ B) (hsurj : ∀ d ∈ B, ∃ i < n, e i = d)
    {TH F : ℕ → ℕ} (hle : ∀ i < n, TH i ≤ Hs.length)
    (hth : ∀ i < n, ∀ j < Hs.length, (TH i = j + 1 ↔ M.tail (e i) ∈ Hs.getD j ∅))
    (hF : ∀ j < Hs.length, (0 < F j ↔ ∃ i < n, TH i = j + 1)) :
    cnt F Hs.length = (tHs M B Hs).length ∧
      ∀ i < n, ∀ j, ((if 0 < TH i then cnt F (TH i - 1) + 1 else 0) = j + 1 ↔
        M.tail (e i) ∈ (tHs M B Hs).getD j ∅) := by
  classical
  set p : Finset V → Bool := fun g => decide (∃ d ∈ B, M.tail d ∈ g) with hp
  have hFp : ∀ j < Hs.length, (0 < F j ↔ p (Hs.getD j ∅) = true) := fun j hj => by
    rw [hF j hj, hp, decide_eq_true_iff]
    constructor
    · rintro ⟨i, hi, h⟩
      exact ⟨e i, hmem i hi, (hth i hi j hj).1 h⟩
    · rintro ⟨d, hd, h⟩
      obtain ⟨i, hi, rfl⟩ := hsurj d hd
      exact ⟨i, hi, (hth i hi j hj).2 h⟩
  have htHs : tHs M B Hs = Hs.filter p := rfl
  have hlen : (tHs M B Hs).length = cnt F Hs.length := by
    rw [htHs]; exact length_filter_cnt p ∅ Hs F hFp
  refine ⟨hlen.symm, fun i hi j => ?_⟩
  constructor
  · intro h
    have h0 : 0 < TH i := by by_contra h0; rw [iteF h0] at h; omega
    rw [iteT h0] at h
    have hv : TH i - 1 < Hs.length := by have := hle i hi; omega
    have hmemv : M.tail (e i) ∈ Hs.getD (TH i - 1) ∅ := (hth i hi _ hv).1 (by omega)
    have hpv : p (Hs.getD (TH i - 1) ∅) = true :=
      (hFp _ hv).1 ((hF _ hv).2 ⟨i, hi, by omega⟩)
    have := filter_getD_cnt p ∅ Hs F hFp _ hv hpv
    rw [← htHs, show cnt F (TH i - 1) = j by omega] at this
    rw [this]; exact hmemv
  · intro h
    have hj : j < (tHs M B Hs).length := by
      by_contra hj
      rw [List.getD_eq_default _ _ (by omega)] at h
      simp at h
    rw [hlen] at hj
    obtain ⟨v, hv, hFv, hcv⟩ := cnt_surj F Hs.length j hj
    have := filter_getD_cnt p ∅ Hs F hFp v hv ((hFp v hv).1 hFv)
    rw [← htHs, hcv] at this
    rw [this] at h
    have hT := (hth i hi v hv).2 h
    rw [hT, iteT (by omega)]
    simp only [Nat.add_sub_cancel, hcv]

/-! ### The programs -/

/-- `nlF t v = (t > 0 ? v + 1 : 0)`. -/
def nlF (t v : ℕ) : ℕ := if 0 < t then v + 1 else 0

/-- `r6523 := nlF TH[i] CI[TH[i] - 1]` (bases `4842 = TH`, `5832 = CI`, `5837 = 0`). -/
def vbNL : Stmt :=
  .seq (block [.addN 6524 4842 6520, .loadN 6525 6524])
    (.ifLtN 5837 6525
      (block [.subN 6525 6525 6521, .addN 6524 5832 6525, .loadN 6527 6524, .addN 6523 6527 6521])
      (block [.constN 6523 0]))

/-- `r6523 := TH2[i]` (base `5834`). -/
def vbCP : Stmt := block [.addN 6524 5834 6520, .loadN 6523 6524]

/-- The bases and the saved registers. -/
def tf0 : Stmt := block [.constN 6521 1, .constN 5837 0, .addN 5831 4874 6521,
  .addN 5836 5830 6521, .addN 5832 5836 4874, .addN 5833 5832 4874, .addN 5834 5833 4874,
  .addN 5835 5834 4840, .storeN 5835 6521, .copyN 5840 4630, .copyN 5841 4631, .copyN 5842 4632,
  .copyN 5843 4633, .copyN 5844 4634]

/-- `WT[0 … k] := 0`. -/
def tf1 : Stmt := mapRunS (block [.constN 6523 0]) 5831 5830

/-- The scatter-add of ones at the labels. -/
def tf2 : Stmt := .seq (block [.copyN 4630 4840, .copyN 4631 4842, .copyN 4632 5835,
  .constN 4633 0, .copyN 4634 5830]) saProg

/-- The compaction of the flags `WT[1 … k]`. -/
def tf3 : Stmt := .seq (block [.copyN 6300 4874, .copyN 6301 5836, .copyN 6302 5832,
  .copyN 6303 5833]) lkProg

/-- The new labels into `TH2`. -/
def tf4 : Stmt := mapRunS vbNL 4840 5834

/-- `TH := TH2`. -/
def tf5 : Stmt := mapRunS vbCP 4840 4842

/-- The new count; the saved registers back. -/
def tf6 : Stmt := block [.copyN 4874 6306, .copyN 4630 5840, .copyN 4631 5841, .copyN 4632 5842,
  .copyN 4633 5843, .copyN 4634 5844]

/-- **The pre-filter of the holes.** -/
def tfProg : Stmt := .seq (.seq tf0 (.seq tf1 tf2)) (.seq tf3 (.seq tf4 (.seq tf5 tf6)))

/-- The registers written by `tfProg`. -/
def tfW (x : ℕ) : Prop :=
  x = 4874 ∨ (5831 ≤ x ∧ x ≤ 5844) ∨ (4635 ≤ x ∧ x ≤ 4639) ∨ (6300 ≤ x ∧ x ≤ 6309) ∨
    (6520 ≤ x ∧ x ≤ 6529)

section Exec

variable {P : Input} {W : ℕ}

theorem vbNLb_exec (c : Config) (hc : WordsBounded W c) {t CIb : ℕ}
    (r25 : c.nreg 6525 = t) (r21 : c.nreg 6521 = 1) (r32 : c.nreg 5832 = CIb)
    (w1 : CIb + (t - 1) ≤ W) (w2 : c.nmem (CIb + (t - 1)) + 1 ≤ W) :
    ∃ c' k, Exec P W (block [.subN 6525 6525 6521, .addN 6524 5832 6525, .loadN 6527 6524,
        .addN 6523 6527 6521]) c c' k ∧ k = 4 ∧
      c'.nreg 6523 = c.nmem (CIb + (t - 1)) + 1 ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r25, r21, r32]; omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp (disch := omega) only [upd_other, upd_same, r25, r21, r32]
  · unfold vscr at hx; config_simp; simp (disch := omega) only [upd_other]

theorem vbNL_exec (c : Config) (hc : WordsBounded W c) {i Tb CIb : ℕ}
    (r20 : c.nreg 6520 = i) (r21 : c.nreg 6521 = 1) (r37 : c.nreg 5837 = 0)
    (r42 : c.nreg 4842 = Tb) (r32 : c.nreg 5832 = CIb) (w1 : Tb + i ≤ W)
    (w2 : 0 < c.nmem (Tb + i) → CIb + (c.nmem (Tb + i) - 1) ≤ W ∧
      c.nmem (CIb + (c.nmem (Tb + i) - 1)) + 1 ≤ W) :
    ∃ c' k, Exec P W vbNL c c' k ∧ k ≤ 8 ∧
      c'.nreg 6523 = nlF (c.nmem (Tb + i)) (c.nmem (CIb + (c.nmem (Tb + i) - 1))) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v1, n1, m1, rr1, rm1, o1⟩ := ld2_exec (P := P) (t := 6524) (r := 6525)
    (b := 4842) (ctr := 6520) c hc r42 r20 w1 (by omega) (by omega)
  have q1 : ∀ x, ¬ vscr x → c₁.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; exact n1 x (by omega) (by omega)
  have z1 : c₁.nreg 5837 = 0 := by rw [q1 _ (by unfold vscr; omega), r37]
  unfold vbNL
  by_cases h1 : 0 < c.nmem (Tb + i)
  · obtain ⟨w2a, w2b⟩ := w2 h1
    have s21 : c₁.nreg 6521 = 1 := by rw [q1 _ (by unfold vscr; omega), r21]
    have s32 : c₁.nreg 5832 = CIb := by rw [q1 _ (by unfold vscr; omega), r32]
    obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := vbNLb_exec (P := P) c₁ e₁.wb_right
      v1 s21 s32 w2a (by rw [m1]; exact w2b)
    rw [m1] at v2
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true (by rw [z1, v1]; exact h1) e₂), by omega, ?_,
      fun x hx => ?_, by rw [m2, m1], by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
    · rw [v2]; simp [nlF, h1]
    · rw [n2 x hx, q1 x hx]
  · obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := cst_exec (P := P) (r := 6523) (v := 0)
      c₁ e₁.wb_right (Nat.zero_le _)
    refine ⟨c₂, _, .seq e₁ (.ifLtN_false (by rw [z1, v1]; exact h1) e₂), by omega, ?_,
      fun x hx => ?_, by rw [m2, m1], by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
    · rw [v2]; simp [nlF, h1]
    · rw [n2 x (by unfold vscr at hx; omega), q1 x hx]

theorem vbCP_exec (c : Config) (hc : WordsBounded W c) {i T2b : ℕ}
    (r20 : c.nreg 6520 = i) (r34 : c.nreg 5834 = T2b) (w1 : T2b + i ≤ W) :
    ∃ c' k, Exec P W vbCP c c' k ∧ k ≤ 2 ∧ c'.nreg 6523 = c.nmem (T2b + i) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v1, n1, m1, rr1, rm1, o1⟩ := ld2_exec (P := P) (t := 6524) (r := 6523)
    (b := 5834) (ctr := 6520) c hc r34 r20 w1 (by omega) (by omega)
  exact ⟨c₁, k₁, e₁, by omega, v1, fun x hx => n1 x (by unfold vscr at hx; omega)
    (by unfold vscr at hx; omega), m1, rr1, rm1, o1⟩

theorem tf0_exec (c : Config) (hc : WordsBounded W c) {n k Zb : ℕ}
    (r40 : c.nreg 4840 = n) (r74 : c.nreg 4874 = k) (r30 : c.nreg 5830 = Zb)
    (w : Zb + 3 * k + n + 2 ≤ W) :
    ∃ c' t, Exec P W tf0 c c' t ∧ t = 14 ∧ c'.nreg 6521 = 1 ∧ c'.nreg 5837 = 0 ∧
      c'.nreg 5831 = k + 1 ∧ c'.nreg 5836 = Zb + 1 ∧ c'.nreg 5832 = Zb + k + 1 ∧
      c'.nreg 5833 = Zb + 2 * k + 1 ∧ c'.nreg 5834 = Zb + 3 * k + 1 ∧
      c'.nreg 5835 = Zb + 3 * k + n + 1 ∧
      c'.nreg 5840 = c.nreg 4630 ∧ c'.nreg 5841 = c.nreg 4631 ∧ c'.nreg 5842 = c.nreg 4632 ∧
      c'.nreg 5843 = c.nreg 4633 ∧ c'.nreg 5844 = c.nreg 4634 ∧
      (∀ x, x ≠ 6521 → (x < 5831 ∨ 5844 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (Zb + 3 * k + n + 1) 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tf0
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r40, r74, r30]; omega)
  all_goals try (have := hc.1 4630; omega)
  all_goals try (have := hc.1 4631; omega)
  all_goals try (have := hc.1 4632; omega)
  all_goals try (have := hc.1 4633; omega)
  all_goals try (have := hc.1 4634; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 => ?_, ?_,
    rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r40, r74, r30])
    try omega
  rw [show Zb + 1 + k + k + k + n = Zb + 3 * k + n + 1 by omega]

theorem tf2a_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (block [.copyN 4630 4840, .copyN 4631 4842, .copyN 4632 5835,
      .constN 4633 0, .copyN 4634 5830]) c c' t ∧ t = 5 ∧ c'.nreg 4630 = c.nreg 4840 ∧
      c'.nreg 4631 = c.nreg 4842 ∧ c'.nreg 4632 = c.nreg 5835 ∧ c'.nreg 4633 = 0 ∧
      c'.nreg 4634 = c.nreg 5830 ∧ (∀ x, (x < 4630 ∨ 4634 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try omega
  all_goals try (have := hc.1 4840; omega)
  all_goals try (have := hc.1 4842; omega)
  all_goals try (have := hc.1 5835; omega)
  all_goals try (have := hc.1 5830; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])
    try omega

theorem tf3a_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (block [.copyN 6300 4874, .copyN 6301 5836, .copyN 6302 5832,
      .copyN 6303 5833]) c c' t ∧ t = 4 ∧ c'.nreg 6300 = c.nreg 4874 ∧
      c'.nreg 6301 = c.nreg 5836 ∧ c'.nreg 6302 = c.nreg 5832 ∧ c'.nreg 6303 = c.nreg 5833 ∧
      (∀ x, (x < 6300 ∨ 6303 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try (have := hc.1 4874; omega)
  all_goals try (have := hc.1 5836; omega)
  all_goals try (have := hc.1 5832; omega)
  all_goals try (have := hc.1 5833; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])
    try omega

theorem tf6_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W tf6 c c' t ∧ t = 6 ∧ c'.nreg 4874 = c.nreg 6306 ∧
      c'.nreg 4630 = c.nreg 5840 ∧ c'.nreg 4631 = c.nreg 5841 ∧ c'.nreg 4632 = c.nreg 5842 ∧
      c'.nreg 4633 = c.nreg 5843 ∧ c'.nreg 4634 = c.nreg 5844 ∧
      (∀ x, x ≠ 4874 → (x < 4630 ∨ 4634 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tf6
  exec_block
  all_goals try (have := hc.1 6306; omega)
  all_goals try (have := hc.1 5840; omega)
  all_goals try (have := hc.1 5841; omega)
  all_goals try (have := hc.1 5842; omega)
  all_goals try (have := hc.1 5843; omega)
  all_goals try (have := hc.1 5844; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])
    try omega

lemma saF_congrT {key key' val val' : ℕ → ℕ} {n : ℕ} (hk : ∀ i < n, key i = key' i)
    (hv : ∀ i < n, val i = val' i) (j : ℕ) : saF key val n j = saF key' val' n j := by
  unfold saF
  rw [filter_congr fun i hi => by rw [hk i (mem_range.1 hi)]]
  exact sum_congr rfl fun i hi => hv i (mem_range.1 (mem_filter.1 hi).1)

set_option maxHeartbeats 2000000 in
/-- The first part of the pre-filter: the bases, `WT := 0`, the scatter-add. -/
theorem tfA_exec (c : Config) (hc : WordsBounded W c) {n k Tb Zb : ℕ}
    (r40 : c.nreg 4840 = n) (r42 : c.nreg 4842 = Tb) (r74 : c.nreg 4874 = k)
    (r30 : c.nreg 5830 = Zb) (hTH : ∀ i < n, c.nmem (Tb + i) ≤ k) (l1 : Tb + n ≤ Zb)
    (w : Zb + 3 * k + n + 2 ≤ W) (wk : n + k + 2 ≤ W) :
    ∃ c' t, Exec P W (.seq tf0 (.seq tf1 tf2)) c c' t ∧ t ≤ 12 * n + 6 * k + 40 ∧
      c'.nreg 6521 = 1 ∧ c'.nreg 5837 = 0 ∧ c'.nreg 5832 = Zb + k + 1 ∧
      c'.nreg 5833 = Zb + 2 * k + 1 ∧ c'.nreg 5834 = Zb + 3 * k + 1 ∧ c'.nreg 5836 = Zb + 1 ∧
      (∀ x, 4630 ≤ x → x ≤ 4634 → c'.nreg (x + 1210) = c.nreg x) ∧
      (∀ x, (x < 4630 ∨ (4639 < x ∧ x < 5831) ∨ (5844 < x ∧ x < 6520) ∨ 6529 < x) →
        c'.nreg x = c.nreg x) ∧
      (∀ j < k, c'.nmem (Zb + 1 + j) = saF (fun i => c.nmem (Tb + i)) (fun _ => 1) n (j + 1)) ∧
      (∀ a, ¬ (Zb ≤ a ∧ a < Zb + 3 * k + n + 2) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₀, t₀, e₀, ht₀, a21, a37, a31, a36, a32, a33, a34, a35, s40, s41, s42, s43, s44, n0,
    m0, rr0, rm0, o0⟩ := tf0_exec (P := P) c hc r40 r74 r30 w
  have q0 : ∀ x, x ≠ 6521 → (x < 5831 ∨ 5844 < x) → c₀.nreg x = c.nreg x := n0
  obtain ⟨c₁, t₁, e₁, ht₁, f1, m1, n1, rr1, rm1, o1⟩ := mapRun_exec (P := P) c₀ e₀.wb_right
    (vb := block [.constN 6523 0]) (bnd := 5831) (ob := 5830) (m := k + 1) (Ob := Zb) (B := 1)
    (fun _ => 0) a31 a21 (by rw [q0 _ (by omega) (by omega), r30]) (by omega) (by omega)
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      obtain ⟨c'', k', e', hk'', v, nn, mm, rr, rm, oo⟩ := cst_exec (P := P) (r := 6523) (v := 0)
        c' hw (Nat.zero_le _)
      exact ⟨c'', k', e', by omega, v, fun x hx => nn x (by unfold vscr at hx; omega), mm, rr,
        rm, oo⟩)
  have q1 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₁.nreg x = c₀.nreg x := n1
  have M1 : ∀ a, ¬ (Zb ≤ a ∧ a < Zb + (k + 1)) →
      c₁.nmem a = upd c.nmem (Zb + 3 * k + n + 1) 1 a := fun a ha => by rw [m1 a ha, m0]
  have one1 : c₁.nmem (Zb + 3 * k + n + 1) = 1 := by rw [M1 _ (by omega), upd_same]
  have TH1 : ∀ i < n, c₁.nmem (Tb + i) = c.nmem (Tb + i) := fun i hi => by
    rw [M1 _ (by omega), upd_other _ _ _ (by omega)]
  obtain ⟨c₂, t₂, e₂, ht₂, b0, b1, b2, b3, b4, n2, m2, rr2, rm2, o2⟩ := tf2a_exec (P := P) c₁
    e₁.wb_right
  have g40 : c₁.nreg 4840 = n := by
    rw [q1 _ (by unfold vscr; omega) (by omega) (by omega), q0 _ (by omega) (by omega), r40]
  have g42 : c₁.nreg 4842 = Tb := by
    rw [q1 _ (by unfold vscr; omega) (by omega) (by omega), q0 _ (by omega) (by omega), r42]
  have g35 : c₁.nreg 5835 = Zb + 3 * k + n + 1 := by
    rw [q1 _ (by unfold vscr; omega) (by omega) (by omega), a35]
  have g30 : c₁.nreg 5830 = Zb := by
    rw [q1 _ (by unfold vscr; omega) (by omega) (by omega), q0 _ (by omega) (by omega), r30]
  rw [g40] at b0; rw [g42] at b1; rw [g35] at b2; rw [g30] at b4
  rw [← m2] at one1 TH1
  have hsum : ∑ j ∈ range n, c₂.nmem (Zb + 3 * k + n + 1 + 0 * j) ≤ W := by
    simp only [Nat.zero_mul, Nat.add_zero, one1, sum_const, card_range, smul_eq_mul, Nat.mul_one]
    omega
  have hW0 : ∀ j < k + 1, c₂.nmem (Zb + j) = 0 := fun j hj => by rw [m2]; exact f1 j hj
  obtain ⟨c₃, t₃, e₃, ht₃, h3, m3, n3, rr3, rm3, o3⟩ := saProg_exec (P := P) c₂ e₂.wb_right
    (m := n) (nk := k + 1) (KEYb := Tb) (VALb := Zb + 3 * k + n + 1) (st := 0) (Wb := Zb)
    b0 b1 b2 b3 b4 (fun j hj => by rw [TH1 j hj]; have := hTH j hj; omega) hW0
    (fun j hj => by omega) (fun j hj => by omega) (by omega) (by omega) (fun j hj => by omega)
    (by omega) hsum
  refine ⟨c₃, t₀ + (t₁ + (t₂ + t₃)), .seq e₀ (.seq e₁ (.seq e₂ e₃)), by omega, ?_, ?_, ?_, ?_,
    ?_, ?_, fun x h1 h2 => ?_, fun x h1 => ?_, fun j hj => ?_, fun a ha => ?_,
    by rw [rr3, rr2, rr1, rr0], by rw [rm3, rm2, rm1, rm0], by rw [o3, o2, o1, o0]⟩
  · rw [n3 _ (by omega), n2 _ (by omega), q1 _ (by unfold vscr; omega) (by omega) (by omega)]
    exact a21
  · rw [n3 _ (by omega), n2 _ (by omega), q1 _ (by unfold vscr; omega) (by omega) (by omega)]
    exact a37
  · rw [n3 _ (by omega), n2 _ (by omega), q1 _ (by unfold vscr; omega) (by omega) (by omega)]
    exact a32
  · rw [n3 _ (by omega), n2 _ (by omega), q1 _ (by unfold vscr; omega) (by omega) (by omega)]
    exact a33
  · rw [n3 _ (by omega), n2 _ (by omega), q1 _ (by unfold vscr; omega) (by omega) (by omega)]
    exact a34
  · rw [n3 _ (by omega), n2 _ (by omega), q1 _ (by unfold vscr; omega) (by omega) (by omega)]
    exact a36
  · rw [n3 _ (by omega), n2 _ (by omega), q1 _ (by unfold vscr; omega) (by omega) (by omega)]
    rcases (show x = 4630 ∨ x = 4631 ∨ x = 4632 ∨ x = 4633 ∨ x = 4634 by omega) with
      rfl | rfl | rfl | rfl | rfl
    · exact s40
    · exact s41
    · exact s42
    · exact s43
    · exact s44
  · rw [n3 _ (by omega), n2 _ (by omega), q1 _ (by unfold vscr; omega) (by omega) (by omega),
      q0 _ (by omega) (by omega)]
  · rw [show Zb + 1 + j = Zb + (j + 1) by omega, h3 _ (by omega)]
    exact saF_congrT (fun i hi => TH1 i hi) (fun i hi => by simp only [Nat.zero_mul,
      Nat.add_zero, one1]) _
  · rw [m3 a (by omega), m2, M1 a (by omega), upd_other _ _ _ (by omega)]

/-- The compaction of the flags. -/
theorem tfB_exec (c : Config) (hc : WordsBounded W c) {k Zb : ℕ} {F : ℕ → ℕ}
    (r74 : c.nreg 4874 = k) (r36 : c.nreg 5836 = Zb + 1) (r32 : c.nreg 5832 = Zb + k + 1)
    (r33 : c.nreg 5833 = Zb + 2 * k + 1) (w : Zb + 3 * k + 1 ≤ W) (wk : k + 1 ≤ W)
    (hF : ∀ j < k, c.nmem (Zb + 1 + j) = F j) :
    ∃ c' t, Exec P W tf3 c c' t ∧ t ≤ 11 * k + 10 ∧ c'.nreg 6306 = cnt F k ∧
      (∀ j < k, 0 < F j → c'.nmem (Zb + k + 1 + j) = cnt F j) ∧
      (∀ a, ¬ (Zb + k + 1 ≤ a ∧ a < Zb + 3 * k + 1) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6300 ∨ 6309 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₄, t₄, e₄, ht₄, d0, d1, d2, d3, n4, m4, rr4, rm4, o4⟩ := tf3a_exec (P := P) c hc
  rw [r74] at d0; rw [r36] at d1; rw [r32] at d2; rw [r33] at d3
  obtain ⟨c₅, t₅, e₅, ht₅, l6, lCI, m5, n5, rr5, rm5, o5⟩ := lkProg_exec (P := P) c₄ e₄.wb_right
    d0 d1 d2 d3 (by omega) (by omega) (by omega) (by omega)
  have FL : ∀ j < k, c₄.nmem (Zb + 1 + j) = F j := fun j hj => by rw [m4]; exact hF j hj
  have hcF : ∀ j ≤ k, cnt (fun j => c₄.nmem (Zb + 1 + j)) j = cnt F j := fun j hj =>
    cnt_ext fun i hi => FL i (by omega)
  refine ⟨c₅, t₄ + t₅, .seq e₄ e₅, by omega, by rw [l6, hcF k le_rfl], fun j hj hFj => ?_,
    fun a ha => by rw [m5 a (by omega), m4], fun x hx => by rw [n5 x (by omega), n4 x (by omega)],
    by rw [rr5, rr4], by rw [rm5, rm4], by rw [o5, o4]⟩
  rw [(lCI j hj (by rw [FL j hj]; exact hFj)).1, hcF j (by omega)]

set_option maxHeartbeats 2000000 in
/-- The new labels, `TH := TH2`, the count and the saved registers. -/
theorem tfC_exec (c : Config) (hc : WordsBounded W c) {n k Tb Zb : ℕ} {F : ℕ → ℕ}
    (r40 : c.nreg 4840 = n) (r42 : c.nreg 4842 = Tb) (r21 : c.nreg 6521 = 1)
    (r37 : c.nreg 5837 = 0) (r32 : c.nreg 5832 = Zb + k + 1) (r34 : c.nreg 5834 = Zb + 3 * k + 1)
    (hTH : ∀ i < n, c.nmem (Tb + i) ≤ k)
    (hpos : ∀ i < n, 0 < c.nmem (Tb + i) → 0 < F (c.nmem (Tb + i) - 1))
    (hCI : ∀ j < k, 0 < F j → c.nmem (Zb + k + 1 + j) = cnt F j) (l1 : Tb + n ≤ Zb)
    (w : Zb + 3 * k + n + 2 ≤ W) (wk : n + k + 2 ≤ W) :
    ∃ c' t, Exec P W (.seq tf4 (.seq tf5 tf6)) c c' t ∧ t ≤ 20 * n + 12 ∧
      c'.nreg 4874 = c.nreg 6306 ∧
      (∀ i < n, c'.nmem (Tb + i) = nlF (c.nmem (Tb + i)) (cnt F (c.nmem (Tb + i) - 1))) ∧
      (∀ x, 4630 ≤ x → x ≤ 4634 → c'.nreg x = c.nreg (x + 1210)) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → x ≠ 4874 → ¬ (4630 ≤ x ∧ x ≤ 4634) →
        c'.nreg x = c.nreg x) ∧
      (∀ a, ¬ (Tb ≤ a ∧ a < Tb + n) → ¬ (Zb + 3 * k + 1 ≤ a ∧ a < Zb + 3 * k + n + 1) →
        c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set g4 : ℕ → ℕ := fun i => nlF (c.nmem (Tb + i)) (cnt F (c.nmem (Tb + i) - 1)) with hg4
  obtain ⟨c₆, t₆, e₆, ht₆, f6, m6, n6, rr6, rm6, o6⟩ := mapRun_exec (P := P) c hc
    (vb := vbNL) (bnd := 4840) (ob := 5834) (m := n) (Ob := Zb + 3 * k + 1) (B := 8) g4 r40 r21
    r34 (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega)
    (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      have tq : c'.nmem (Tb + i) = c.nmem (Tb + i) := hm _ (by omega)
      have hv : 0 < c.nmem (Tb + i) → c.nmem (Tb + i) - 1 < k := fun hp => by
        have := hTH i hi; omega
      have cq : 0 < c.nmem (Tb + i) → c'.nmem (Zb + k + 1 + (c.nmem (Tb + i) - 1)) =
          cnt F (c.nmem (Tb + i) - 1) := fun hp => by
        rw [hm _ (by have := hv hp; omega)]; exact hCI _ (hv hp) (hpos i hi hp)
      obtain ⟨c'', k', e', hk'', v, nn, mm, rr, rm, oo⟩ := vbNL_exec (P := P) (Tb := Tb)
        (CIb := Zb + k + 1) c' hw h20
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega)]; exact r21)
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega)]; exact r37)
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega)]; exact r42)
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega)]; exact r32) (by omega)
        (fun hp => by
          rw [tq] at hp ⊢
          refine ⟨by have := hv hp; omega, ?_⟩
          rw [cq hp]
          have := cnt_le F (c.nmem (Tb + i) - 1)
          have := hv hp
          omega)
      refine ⟨c'', k', e', hk'', ?_, nn, mm, rr, rm, oo⟩
      rw [v, tq, hg4]
      show nlF _ _ = nlF _ _
      unfold nlF
      by_cases hp : 0 < c.nmem (Tb + i)
      · rw [iteT hp, iteT hp, cq hp]
      · rw [iteF hp, iteF hp])
  have q6 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₆.nreg x = c.nreg x := n6
  obtain ⟨c₇, t₇, e₇, ht₇, f7, m7, n7, rr7, rm7, o7⟩ := mapRun_exec (P := P) c₆ e₆.wb_right
    (vb := vbCP) (bnd := 4840) (ob := 4842) (m := n) (Ob := Tb) (B := 2) g4
    (by rw [q6 _ (by unfold vscr; omega) (by omega) (by omega)]; exact r40)
    (by rw [q6 _ (by unfold vscr; omega) (by omega) (by omega)]; exact r21)
    (by rw [q6 _ (by unfold vscr; omega) (by omega) (by omega)]; exact r42) (by omega) (by omega)
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      obtain ⟨c'', k', e', hk'', v, nn, mm, rr, rm, oo⟩ := vbCP_exec (P := P)
        (T2b := Zb + 3 * k + 1) c' hw h20 (by rw [hr _ (by unfold vscr; omega) (by omega)
          (by omega), q6 _ (by unfold vscr; omega) (by omega) (by omega)]; exact r34) (by omega)
      refine ⟨c'', k', e', hk'', ?_, nn, mm, rr, rm, oo⟩
      rw [v, hm _ (by omega)]; exact f6 i hi)
  have q7 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₇.nreg x = c.nreg x := fun x h1 h2 h3 => by
    rw [n7 x h1 h2 h3, q6 x h1 h2 h3]
  obtain ⟨c₈, t₈, e₈, ht₈, k8, x0, x1, x2, x3, x4, n8, m8, rr8, rm8, o8⟩ := tf6_exec (P := P) c₇
    e₇.wb_right
  refine ⟨c₈, t₆ + (t₇ + t₈), .seq e₆ (.seq e₇ e₈), by omega,
    by rw [k8, q7 _ (by unfold vscr; omega) (by omega) (by omega)], fun i hi => by
      rw [m8, f7 i hi], fun x h1 h2 => ?_, fun x h1 h2 h3 h4 h5 => ?_, fun a h1 h2 => ?_,
    by rw [rr8, rr7, rr6], by rw [rm8, rm7, rm6], by rw [o8, o7, o6]⟩
  · rcases (show x = 4630 ∨ x = 4631 ∨ x = 4632 ∨ x = 4633 ∨ x = 4634 by omega) with
      rfl | rfl | rfl | rfl | rfl
    · rw [x0, q7 _ (by unfold vscr; omega) (by omega) (by omega)]
    · rw [x1, q7 _ (by unfold vscr; omega) (by omega) (by omega)]
    · rw [x2, q7 _ (by unfold vscr; omega) (by omega) (by omega)]
    · rw [x3, q7 _ (by unfold vscr; omega) (by omega) (by omega)]
    · rw [x4, q7 _ (by unfold vscr; omega) (by omega) (by omega)]
  · rw [n8 x h4 (by omega), q7 x h1 h2 h3]
  · rw [m8, m7 a h1, m6 a (by omega)]

/-- **The pre-filter of the holes** (see the module docstring): within `32 n + 17 k + 60` steps,
for flags `F` marking the labels `j + 1` that occur in `TH` (`j < k`), `r4874 = cnt F k` and
`TH'[i] = nlF TH[i] (cnt F (TH[i] - 1))`; memory outside `TH` and `[Zb, Zb + 3 k + n + 2)` and
registers outside `tfW` kept. -/
theorem tfProg_exec (c : Config) (hc : WordsBounded W c) {n k Tb Zb : ℕ}
    (r40 : c.nreg 4840 = n) (r42 : c.nreg 4842 = Tb) (r74 : c.nreg 4874 = k)
    (r30 : c.nreg 5830 = Zb) (hTH : ∀ i < n, c.nmem (Tb + i) ≤ k) (l1 : Tb + n ≤ Zb)
    (w : Zb + 3 * k + n + 2 ≤ W) (wk : n + k + 2 ≤ W) :
    ∃ c' t, Exec P W tfProg c c' t ∧ t ≤ 32 * n + 17 * k + 62 ∧
      ∃ F : ℕ → ℕ, (∀ j, (0 < F j ↔ ∃ i < n, c.nmem (Tb + i) = j + 1)) ∧
      c'.nreg 4874 = cnt F k ∧
      (∀ i < n, c'.nmem (Tb + i) = nlF (c.nmem (Tb + i)) (cnt F (c.nmem (Tb + i) - 1))) ∧
      (∀ a, ¬ (Tb ≤ a ∧ a < Tb + n) → ¬ (Zb ≤ a ∧ a < Zb + 3 * k + n + 2) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ tfW x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set F : ℕ → ℕ := fun j => saF (fun i => c.nmem (Tb + i)) (fun _ => 1) n (j + 1) with hFd
  have hF : ∀ j, (0 < F j ↔ ∃ i < n, c.nmem (Tb + i) = j + 1) := fun j =>
    saF_one_pos _ n (j + 1)
  obtain ⟨c₁, t₁, e₁, ht₁, a21, a37, a32, a33, a34, a36, sv1, q1, WT1, M1, rr1, rm1, o1⟩ :=
    tfA_exec (P := P) c hc r40 r42 r74 r30 hTH l1 w wk
  have g74 : c₁.nreg 4874 = k := by rw [q1 _ (by omega), r74]
  obtain ⟨c₂, t₂, e₂, ht₂, l6, CI2, M2, q2, rr2, rm2, o2⟩ := tfB_exec (P := P) (F := F) c₁
    e₁.wb_right g74 a36 a32 a33 (by omega) (by omega) WT1
  have TH2 : ∀ i < n, c₂.nmem (Tb + i) = c.nmem (Tb + i) := fun i hi => by
    rw [M2 _ (by omega), M1 _ (by omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, k3, TH3, sv3, q3, M3, rr3, rm3, o3⟩ := tfC_exec (P := P) (F := F) c₂
    e₂.wb_right (n := n) (k := k) (Tb := Tb) (Zb := Zb)
    (by rw [q2 _ (by omega), q1 _ (by omega), r40])
    (by rw [q2 _ (by omega), q1 _ (by omega), r42])
    (by rw [q2 _ (by omega)]; exact a21) (by rw [q2 _ (by omega)]; exact a37)
    (by rw [q2 _ (by omega)]; exact a32) (by rw [q2 _ (by omega)]; exact a34)
    (fun i hi => by rw [TH2 i hi]; exact hTH i hi)
    (fun i hi hp => by rw [TH2 i hi] at hp ⊢; exact (hF _).2 ⟨i, hi, by omega⟩)
    CI2 l1 w wk
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, F, hF, by rw [k3, l6],
    fun i hi => by rw [TH3 i hi, TH2 i hi], fun a h1 h2 => ?_, fun x hx => ?_,
    by rw [rr3, rr2, rr1], by rw [rm3, rm2, rm1], by rw [o3, o2, o1]⟩
  · rw [M3 a h1 (by omega), M2 a (by omega), M1 a h2]
  · unfold tfW at hx
    by_cases hx1 : 4630 ≤ x ∧ x ≤ 4634
    · rw [sv3 x hx1.1 hx1.2, q2 _ (by omega)]; exact sv1 x hx1.1 hx1.2
    · rw [q3 x (by unfold vscr; omega) (by omega) (by omega) (by omega) hx1, q2 x (by omega),
        q1 x (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
