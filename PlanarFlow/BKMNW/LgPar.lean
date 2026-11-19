module

public import PlanarFlow.BKMNW.LgWtF
public import PlanarFlow.BKMNW.TfProg

/-!
# The large-piece separator, stage 5 (part): the parameters of the split on the machine

The split of a large piece is `spSR` (by size: `K = 0`, `A = aS P`) or, if
`holeStep P Hs b` (`b ∧ nTouch = 6`), `spHR` (by holes: `K = kH P`, `A = aH P`); both use the
weight bound `W₀ = #P + K · nTouch` of the heavy test and the base `Bz = encB' W₀` of Miller's
program. With `lS P = 6 √(2 #P) + 4`, `kH P = #P + 3 lS P + 2`, `aS P = (2 #P + 2 + 9 lS P)/3 + 1`,
`aH P = (2 (#P + 6 kH P) + 2 + 9 lS P)/3 + 1`.

* **`nTouch_cnt`**: on the record (`g` onto `P`, hole labels `hp`), `nTouch M P Hs` is the number
  of labels `j + 1 ≤ |Hs|` carried by some dart (`cnt` of the scatter-add of ones);
* `sqInit`, `sqBody`, **`sqLoop`** (`r = #{1 ≤ i ≤ x | i ≤ x / i}`), `card_sqrt`,
  **`sqLoop_exec`**: `r5902 = Nat.sqrt x` within `8 x + 13` steps;
* `pa0`, `paSA`, `paLK`, `paSQ`, `parBlk`, **`lgPar`**, **`lgPar_exec`**: from `n = #P`, the hole
  labels `HP`, `kk = |Hs|` and the flag `bfl ≤ 1`, the registers
  `5913 = bf (bfl = 1 ∧ nt = 6)`, `5910 = K`, `5911 = A`, `5912 = W₀`, `5914 = nt`
  (`nt = cnt …`, the number of touched holes), within `30 n + 30 kk + 100` steps;
  **`lgPar_sem`**: on a record, these are `holeStep`, `K`, `A`, `#P + K · nTouch` of the split.
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

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The number of touched holes from the record's hole labels.** -/
theorem nTouch_cnt {P : Finset D} {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {g : ℕ → D}
    {n : ℕ} (hg_mem : ∀ i < n, g i ∈ P) (hg_surj : ∀ y ∈ P, ∃ i < n, g i = y) {hp : ℕ → ℕ}
    (hhp : ∀ i < n, hp i = hlab Hs (M.tail (g i))) :
    nTouch M P Hs = cnt (fun j => saF hp (fun _ => 1) n (j + 1)) Hs.length := by
  classical
  unfold nTouch
  refine length_filter_cnt _ ∅ Hs _ fun j hj => ?_
  rw [saF_one_pos, decide_eq_true_iff]
  constructor
  · rintro ⟨i, hi, hk⟩
    rw [hhp i hi, hlab_eq_succ_iff hd hj] at hk
    exact ⟨_, hk, g i, hg_mem i hi, rfl⟩
  · rintro ⟨v, hv, d, hdP, rfl⟩
    obtain ⟨i, hi, rfl⟩ := hg_surj d hdP
    exact ⟨i, hi, by rw [hhp i hi, hlab_eq_succ_iff hd hj]; exact hv⟩

/-! ### The integer square root -/

lemma card_sqrt (x : ℕ) : ((Ico 1 (x + 1)).filter fun j => j ≤ x / j).card = Nat.sqrt x := by
  have : (Ico 1 (x + 1)).filter (fun j => j ≤ x / j) = Icc 1 (Nat.sqrt x) := by
    ext j
    simp only [mem_filter, mem_Ico, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, Nat.le_sqrt.2 ?_⟩
      exact (Nat.le_div_iff_mul_le (by omega)).1 h3
    · rintro ⟨h1, h2⟩
      have h3 : j * j ≤ x := Nat.le_sqrt.1 h2
      refine ⟨⟨h1, ?_⟩, (Nat.le_div_iff_mul_le (by omega)).2 h3⟩
      have := Nat.sqrt_le_self x
      omega
  rw [this, Nat.card_Icc]
  omega

/-- `i := 1`, `r := 0`, `5903 := x + 1`. -/
def sqInit : Stmt := block [.constN 5901 1, .constN 5902 0, .addN 5903 5900 5806]

/-- `r := r + [i ≤ x / i]`, `i := i + 1`. -/
def sqBody : Stmt :=
  block [.divN 5904 5900 5901, .subN 5904 5901 5904, .divN 5904 5904 5904, .subN 5904 5806 5904,
    .addN 5902 5902 5904, .addN 5901 5901 5806]

/-- **The integer square root** of `r5900` into `r5902`. -/
def sqLoop : Stmt := .seq sqInit (.whileLtN 5901 5903 sqBody)

/-- The arithmetic of the sizes from `n = r5800` and `s = r5902`: `5923 = lS = 6 s + 4`,
`5924 = kH = 3 lS + n + 2`, `5925 = aS`, `5905 = aH`. -/
def pb1 : Stmt :=
  block [.constN 5922 6, .mulN 5923 5922 5902, .constN 5922 4, .addN 5923 5923 5922,
    .constN 5922 3, .mulN 5924 5922 5923, .addN 5924 5924 5800, .constN 5922 2,
    .addN 5924 5924 5922, .addN 5925 5800 5800, .addN 5925 5925 5922, .constN 5922 9,
    .mulN 5904 5922 5923, .addN 5925 5925 5904, .constN 5922 3, .divN 5925 5925 5922,
    .addN 5925 5925 5806, .constN 5922 6, .mulN 5905 5922 5924, .addN 5905 5905 5800,
    .addN 5905 5905 5905, .constN 5922 2, .addN 5905 5905 5922, .addN 5905 5905 5904,
    .constN 5922 3, .divN 5905 5905 5922, .addN 5905 5905 5806]

/-- The flag of the split by holes: `5913 = bfl · [nt = 6]` (`bfl = r5915`, `nt = r5914`). -/
def pb2 : Stmt :=
  block [.constN 5922 6, .subN 5906 5914 5922, .subN 5904 5922 5914, .addN 5906 5906 5904,
    .divN 5906 5906 5906, .subN 5906 5806 5906, .mulN 5913 5915 5906]

/-- `5910 = K = hs · kH`, `5911 = A = (1 - hs) aS + hs aH`, `5912 = W₀ = n + K · nt`. -/
def pb3 : Stmt :=
  block [.mulN 5910 5913 5924, .subN 5906 5806 5913, .mulN 5906 5906 5925, .mulN 5904 5913 5905,
    .addN 5911 5906 5904, .mulN 5904 5910 5914, .addN 5912 5800 5904]

/-- The bases of the count of touched holes from `Zb = r5916`: `5917 = kk + 1`,
`5918 = Zb + kk + 1`, `5919 = Zb + 2 kk + 1`, `5920 = Zb + 3 kk + 1` (holding `1`),
`5921 = Zb + 1`. -/
def pa0 : Stmt :=
  block [.addN 5917 5870 5806, .addN 5918 5916 5917, .addN 5919 5918 5870, .addN 5920 5919 5870,
    .storeN 5920 5806, .addN 5921 5916 5806]

/-- The registers of the scatter-add of ones at the hole labels. -/
def paSA : Stmt :=
  block [.copyN 4630 5800, .copyN 4631 5802, .copyN 4632 5920, .constN 4633 0, .copyN 4634 5916]

/-- The registers of the count of the labels carried. -/
def paLK : Stmt := block [.copyN 6300 5870, .copyN 6301 5921, .copyN 6302 5918, .copyN 6303 5919]

/-- `nt := r6306`, `x := 2 n`. -/
def paSQ : Stmt := block [.copyN 5914 6306, .addN 5900 5800 5800]

/-- **The parameters of the split** (see the module docstring). -/
def lgPar : Stmt :=
  .seq pa0 (.seq (zfill 5917 5916) (.seq (.seq paSA saProg) (.seq (.seq paLK lkProg)
    (.seq (.seq paSQ sqLoop) (.seq pb1 (.seq pb2 pb3))))))

/-- The registers written by `lgPar`. -/
def lgParW (x : ℕ) : Prop :=
  (5900 ≤ x ∧ x ≤ 5914) ∨ (5917 ≤ x ∧ x ≤ 5925) ∨ (4630 ≤ x ∧ x ≤ 4639) ∨
    (6300 ≤ x ∧ x ≤ 6309) ∨ x = 6520 ∨ (6522 ≤ x ∧ x ≤ 6529)

section Exec

variable {P : Input} {W : ℕ}

theorem sqBody_exec (c : Config) (hc : WordsBounded W c) {x i r : ℕ}
    (r00 : c.nreg 5900 = x) (r01 : c.nreg 5901 = i) (r02 : c.nreg 5902 = r)
    (r06 : c.nreg 5806 = 1) (hi : 1 ≤ i) (w : r + i + 1 ≤ W) :
    ∃ c' t, Exec P W sqBody c c' t ∧ t = 6 ∧ c'.nreg 5901 = i + 1 ∧
      c'.nreg 5902 = r + (if i ≤ x / i then 1 else 0) ∧
      (∀ y, y ≠ 5901 → y ≠ 5902 → y ≠ 5904 → c'.nreg y = c.nreg y) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hd := dself_le (i - x / i)
  have hq : x / i ≤ x := Nat.div_le_self _ _
  have bx : x ≤ W := r00 ▸ hc.1 _
  have bi : i ≤ W := r01 ▸ hc.1 _
  have b1 : x / i ≤ W := le_trans hq bx
  have b2 : i - x / i ≤ W := le_trans (Nat.sub_le _ _) bi
  have b3 : (i - x / i) / (i - x / i) ≤ W := le_trans hd (by omega)
  have b4 : 1 - (i - x / i) / (i - x / i) ≤ W := le_trans (Nat.sub_le 1 _) (by omega)
  have hf : 1 - (i - x / i) / (i - x / i) = if i ≤ x / i then 1 else 0 := by
    rw [div_self_flag]; split_ifs <;> omega
  unfold sqBody
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r00, r01, r02, r06]; omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r00, r01, r02, r06]; first | exact b1 | exact b2 | exact b3 | exact b4)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r00, r01, r02, r06]; exact le_trans (Nat.add_le_add_left (Nat.sub_le 1 _) r) (by omega))
  refine ⟨rfl, ?_, ?_, fun y h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r00, r01, r02, r06, hf])

/-- **The square root loop**: `r5902 = Nat.sqrt x` for `x = r5900`, within `8 x + 13` steps;
registers outside `5901 … 5904` kept. -/
theorem sqLoop_exec (c : Config) (hc : WordsBounded W c) {x : ℕ} (r00 : c.nreg 5900 = x)
    (r06 : c.nreg 5806 = 1) (w : 2 * x + 3 ≤ W) :
    ∃ c' t, Exec P W sqLoop c c' t ∧ t ≤ 8 * x + 13 ∧ c'.nreg 5902 = Nat.sqrt x ∧
      (∀ y, (y < 5901 ∨ 5904 < y) → c'.nreg y = c.nreg y) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, g1, g2, g3, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W sqInit c c₁ k₁ ∧ k₁ = 3 ∧ c₁.nreg 5901 = 1 ∧ c₁.nreg 5902 = 0 ∧
      c₁.nreg 5903 = x + 1 ∧ (∀ y, (y < 5901 ∨ 5904 < y) → c₁.nreg y = c.nreg y) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold sqInit
    exec_block
    all_goals try ((try config_simp); omega)
    all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r00, r06]; omega)
    refine ⟨rfl, ?_, ?_, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same, r00, r06])
  let J : ℕ → Config → Prop := fun i c' =>
    c'.nreg 5902 = ((Ico 1 i).filter fun j => j ≤ x / j).card ∧
    (∀ y, (y < 5901 ∨ 5904 < y) → c'.nreg y = c.nreg y) ∧
    c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h01, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P) (a := 5901)
    (b := 5903) (body := sqBody) J (B := 6) c₁ e₁.wb_right g1 g3 (by omega)
    ⟨by rw [g2]; simp, gn₁, gm₁, gr₁, grm₁, go₁⟩
    (fun i c' hlo hhi hw h01 h03 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have hcard : ((Ico 1 i).filter fun j => j ≤ x / j).card ≤ i := by
        have := card_le_card (filter_subset (fun j => j ≤ x / j) (Ico 1 i))
        rw [Nat.card_Ico] at this
        omega
      obtain ⟨c'', t, ex, ht, h01', h02', hn', hm', hr', hrm', ho'⟩ := sqBody_exec (P := P) c' hw
        (by rw [j2 _ (by omega), r00]) h01 j1 (by rw [j2 _ (by omega), r06]) hlo (by omega)
      refine ⟨c'', t, ex, ht.le, h01', by rw [hn' _ (by omega) (by omega) (by omega)]; exact h03, ?_,
        fun y hy => by rw [hn' y (by omega) (by omega) (by omega), j2 y hy], by rw [hm', j3], by rw [hr', j4],
        by rw [hrm', j5], by rw [ho', j6]⟩
      rw [h02', Nat.Ico_succ_right_eq_insert_Ico hlo, filter_insert]
      split_ifs with h
      · rw [card_insert_of_notMem (by simp)]
      · rfl)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, by rw [j1, card_sqrt], j2, j3, j4, j5, j6⟩

theorem pb1_exec (c : Config) (hc : WordsBounded W c) {n s : ℕ} (r00 : c.nreg 5800 = n)
    (r02 : c.nreg 5902 = s) (r06 : c.nreg 5806 = 1) (hs : s ≤ 2 * n) (w : 600 * n + 300 ≤ W) :
    ∃ c' t, Exec P W pb1 c c' t ∧ t = 27 ∧ c'.nreg 5923 = 6 * s + 4 ∧
      c'.nreg 5924 = n + 3 * (6 * s + 4) + 2 ∧
      c'.nreg 5925 = (2 * n + 2 + 9 * (6 * s + 4)) / 3 + 1 ∧
      c'.nreg 5905 = (2 * (n + 6 * (n + 3 * (6 * s + 4) + 2)) + 2 + 9 * (6 * s + 4)) / 3 + 1 ∧
      (∀ y, (y < 5904 ∨ (5905 < y ∧ y < 5922) ∨ 5925 < y) → c'.nreg y = c.nreg y) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pb1
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r00, r02, r06]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r00, r02, r06])
    try omega

lemma hsM_eq {bfl nt : ℕ} (hb : bfl ≤ 1) :
    bfl * (1 - ((nt - 6) + (6 - nt)) / ((nt - 6) + (6 - nt))) = bf (bfl = 1 ∧ nt = 6) := by
  rw [div_self_flag]
  unfold bf
  by_cases h : nt = 6
  · subst h; interval_cases bfl <;> simp
  · have : (nt - 6) + (6 - nt) ≠ 0 := by omega
    simp only [this, ↓reduceIte, h, and_false]
    simp

theorem pb2_exec (c : Config) (hc : WordsBounded W c) {nt bfl : ℕ} (r14 : c.nreg 5914 = nt)
    (r15 : c.nreg 5915 = bfl) (r06 : c.nreg 5806 = 1) (hb : bfl ≤ 1) (w : 6 ≤ W) :
    ∃ c' t, Exec P W pb2 c c' t ∧ t = 7 ∧ c'.nreg 5913 = bf (bfl = 1 ∧ nt = 6) ∧
      (∀ y, (y < 5904 ∨ y = 5905 ∨ (5906 < y ∧ y ≠ 5913 ∧ y ≠ 5922)) → c'.nreg y = c.nreg y) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have bn : nt ≤ W := r14 ▸ hc.1 _
  have hd := dself_le ((nt - 6) + (6 - nt))
  have h1 : bfl * (1 - ((nt - 6) + (6 - nt)) / ((nt - 6) + (6 - nt))) ≤ 1 :=
    mul_le_one'' hb (Nat.sub_le _ _)
  have e := hsM_eq (nt := nt) hb
  unfold pb2
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r14, r15, r06]; omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r14, r15, r06]; exact le_trans (Nat.sub_le 1 _) (by omega))
  refine ⟨rfl, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r14, r15, r06, e])

theorem pb3_exec (c : Config) (hc : WordsBounded W c) {n nt h kH aS aH : ℕ}
    (r00 : c.nreg 5800 = n) (r14 : c.nreg 5914 = nt) (r13 : c.nreg 5913 = h)
    (r24 : c.nreg 5924 = kH) (r25 : c.nreg 5925 = aS) (r05 : c.nreg 5905 = aH)
    (r06 : c.nreg 5806 = 1) (hh : h ≤ 1) (hnt : h = 1 → nt = 6)
    (w : n + 6 * kH + aS + aH ≤ W) :
    ∃ c' t, Exec P W pb3 c c' t ∧ t = 7 ∧ c'.nreg 5910 = (if h = 1 then kH else 0) ∧
      c'.nreg 5911 = (if h = 1 then aH else aS) ∧
      c'.nreg 5912 = n + (if h = 1 then kH else 0) * nt ∧
      (∀ y, (y < 5904 ∨ (5906 < y ∧ y < 5910) ∨ 5912 < y) → c'.nreg y = c.nreg y) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  interval_cases h
  · unfold pb3
    exec_block
    all_goals try ((try config_simp); omega)
    all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r00, r14, r13,
      r24, r25, r05, r06]; omega)
    refine ⟨rfl, ?_, ?_, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same, r00, r14, r13, r24, r25, r05, r06])
      try omega
      try simp
  · have h6 := hnt rfl
    subst h6
    unfold pb3
    exec_block
    all_goals try ((try config_simp); omega)
    all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r00, r14, r13,
      r24, r25, r05, r06]; omega)
    refine ⟨rfl, ?_, ?_, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same, r00, r14, r13, r24, r25, r05, r06])
      try omega
      try simp

theorem pa0_exec (c : Config) (hc : WordsBounded W c) {kk Zb : ℕ} (r70 : c.nreg 5870 = kk)
    (r16 : c.nreg 5916 = Zb) (r06 : c.nreg 5806 = 1) (w : Zb + 3 * kk + 2 ≤ W) :
    ∃ c' t, Exec P W pa0 c c' t ∧ t = 6 ∧ c'.nreg 5917 = kk + 1 ∧
      c'.nreg 5918 = Zb + kk + 1 ∧ c'.nreg 5919 = Zb + 2 * kk + 1 ∧
      c'.nreg 5920 = Zb + 3 * kk + 1 ∧ c'.nreg 5921 = Zb + 1 ∧
      c'.nmem = upd c.nmem (Zb + 3 * kk + 1) 1 ∧
      (∀ y, (y < 5917 ∨ 5921 < y) → c'.nreg y = c.nreg y) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pa0
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r70, r16, r06]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r70, r16, r06])
    try omega
    try (congr 1; omega)

theorem paSA_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W paSA c c' t ∧ t = 5 ∧ c'.nreg 4630 = c.nreg 5800 ∧
      c'.nreg 4631 = c.nreg 5802 ∧ c'.nreg 4632 = c.nreg 5920 ∧ c'.nreg 4633 = 0 ∧
      c'.nreg 4634 = c.nreg 5916 ∧ (∀ y, (y < 4630 ∨ 4634 < y) → c'.nreg y = c.nreg y) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold paSA
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])

theorem paLK_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W paLK c c' t ∧ t = 4 ∧ c'.nreg 6300 = c.nreg 5870 ∧
      c'.nreg 6301 = c.nreg 5921 ∧ c'.nreg 6302 = c.nreg 5918 ∧ c'.nreg 6303 = c.nreg 5919 ∧
      (∀ y, (y < 6300 ∨ 6303 < y) → c'.nreg y = c.nreg y) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold paLK
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])

theorem paSQ_exec (c : Config) (hc : WordsBounded W c) {n : ℕ} (r00 : c.nreg 5800 = n)
    (w : 2 * n ≤ W) :
    ∃ c' t, Exec P W paSQ c c' t ∧ t = 2 ∧ c'.nreg 5914 = c.nreg 6306 ∧ c'.nreg 5900 = n + n ∧
      (∀ y, y ≠ 5914 → y ≠ 5900 → c'.nreg y = c.nreg y) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b := hc.1 6306
  unfold paSQ
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r00]; omega)
  refine ⟨rfl, ?_, ?_, fun y h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r00])

/-- **The parameters of the split on the machine.** From `n = r5800`, the hole labels
`HP[i] ≤ kk` (`i < n`), `kk = r5870`, the flag `bfl = r5915 ≤ 1` and a scratch `Zb = r5916`
(`3 kk + 2` words): `r5914 = nt` (the number of labels `1 … kk` carried by a dart),
`r5913 = bf (bfl = 1 ∧ nt = 6)`, and, `s = √(2n)`, `l = 6 s + 4`, `kH = n + 3 l + 2`:
`r5910 = K`, `r5911 = A`, `r5912 = W₀ = n + K · nt` (`K = kH`, `A = aH` if the flag holds, else
`K = 0`, `A = aS`); within `30 n + 30 kk + 100` steps; memory outside the scratch, registers
outside `lgParW` kept. -/
theorem lgPar_exec (c : Config) (hc : WordsBounded W c) {n HPb kk bfl Zb : ℕ}
    (r00 : c.nreg 5800 = n) (r02 : c.nreg 5802 = HPb) (r06 : c.nreg 5806 = 1)
    (r70 : c.nreg 5870 = kk) (r15 : c.nreg 5915 = bfl) (r16 : c.nreg 5916 = Zb)
    (r21 : c.nreg 6521 = 1) (hb : bfl ≤ 1) (hhp : ∀ i < n, c.nmem (HPb + i) ≤ kk)
    (l : HPb + n ≤ Zb) (w : Zb + 3 * kk + 2 ≤ W) (w' : 600 * n + 300 ≤ W) :
    ∃ c' t, Exec P W lgPar c c' t ∧ t ≤ 30 * n + 30 * kk + 100 ∧
      c'.nreg 5914 = cnt (fun j => saF (fun i => c.nmem (HPb + i)) (fun _ => 1) n (j + 1)) kk ∧
      c'.nreg 5913 = bf (bfl = 1 ∧
        cnt (fun j => saF (fun i => c.nmem (HPb + i)) (fun _ => 1) n (j + 1)) kk = 6) ∧
      c'.nreg 5910 = (if bfl = 1 ∧
          cnt (fun j => saF (fun i => c.nmem (HPb + i)) (fun _ => 1) n (j + 1)) kk = 6
        then n + 3 * (6 * Nat.sqrt (n + n) + 4) + 2 else 0) ∧
      c'.nreg 5911 = (if bfl = 1 ∧
          cnt (fun j => saF (fun i => c.nmem (HPb + i)) (fun _ => 1) n (j + 1)) kk = 6
        then (2 * (n + 6 * (n + 3 * (6 * Nat.sqrt (n + n) + 4) + 2)) + 2 +
          9 * (6 * Nat.sqrt (n + n) + 4)) / 3 + 1
        else (2 * n + 2 + 9 * (6 * Nat.sqrt (n + n) + 4)) / 3 + 1) ∧
      c'.nreg 5912 = n + (if bfl = 1 ∧
          cnt (fun j => saF (fun i => c.nmem (HPb + i)) (fun _ => 1) n (j + 1)) kk = 6
        then n + 3 * (6 * Nat.sqrt (n + n) + 4) + 2 else 0) *
          cnt (fun j => saF (fun i => c.nmem (HPb + i)) (fun _ => 1) n (j + 1)) kk ∧
      (∀ a, ¬ (Zb ≤ a ∧ a < Zb + 3 * kk + 2) → c'.nmem a = c.nmem a) ∧
      (∀ y, ¬ lgParW y → c'.nreg y = c.nreg y) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set nt := cnt (fun j => saF (fun i => c.nmem (HPb + i)) (fun _ => 1) n (j + 1)) kk with hnt
  -- the bases
  obtain ⟨c₀, t₀, e₀, ht₀, s17, s18, s19, s20, s21, m0, n0, rr0, rm0, o0⟩ := pa0_exec (P := P) c hc
    r70 r16 r06 w
  have q0 : ∀ y, ¬ lgParW y → c₀.nreg y = c.nreg y := fun y hy => n0 y (by unfold lgParW at hy; omega)
  -- the zero table
  obtain ⟨c₁, t₁, e₁, ht₁, f1, m1, n1, rr1, rm1, o1⟩ := zfill_exec (P := P) c₀ e₀.wb_right
    (bnd := 5917) (ob := 5916) s17 (by rw [q0 _ (by unfold lgParW; omega), r21])
    (by rw [q0 _ (by unfold lgParW; omega), r16]) (by omega) (by omega) (by unfold vscr; omega)
    (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
  have q1 : ∀ y, ¬ lgParW y → c₁.nreg y = c.nreg y := fun y hy => by
    rw [n1 y (by unfold vscr; unfold lgParW at hy; omega) (by unfold lgParW at hy; omega)
      (by unfold lgParW at hy; omega), q0 y hy]
  have s20' : c₁.nreg 5920 = Zb + 3 * kk + 1 := by
    rw [n1 _ (by unfold vscr; omega) (by omega) (by omega), s20]
  have s21' : c₁.nreg 5921 = Zb + 1 := by rw [n1 _ (by unfold vscr; omega) (by omega) (by omega), s21]
  have s18' : c₁.nreg 5918 = Zb + kk + 1 := by
    rw [n1 _ (by unfold vscr; omega) (by omega) (by omega), s18]
  have s19' : c₁.nreg 5919 = Zb + 2 * kk + 1 := by
    rw [n1 _ (by unfold vscr; omega) (by omega) (by omega), s19]
  have M1 : ∀ a, ¬ (Zb ≤ a ∧ a < Zb + 3 * kk + 2) → c₁.nmem a = c.nmem a := fun a ha => by
    rw [m1 a (by omega), m0, upd_other _ _ _ (by omega)]
  have ONE : c₁.nmem (Zb + 3 * kk + 1) = 1 := by rw [m1 _ (by omega), m0, upd_same]
  -- the scatter-add of ones
  obtain ⟨c₂, t₂, e₂, ht₂, a0, a1, a2, a3, a4, n2, m2, rr2, rm2, o2⟩ := paSA_exec (P := P) c₁
    e₁.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, f3, m3, n3, rr3, rm3, o3⟩ := saProg_exec (P := P) c₂ e₂.wb_right
    (m := n) (nk := kk + 1) (KEYb := HPb) (VALb := Zb + 3 * kk + 1) (st := 0) (Wb := Zb)
    (by rw [a0, q1 _ (by unfold lgParW; omega), r00]) (by rw [a1, q1 _ (by unfold lgParW; omega), r02])
    (by rw [a2, s20']) a3 (by rw [a4, q1 _ (by unfold lgParW; omega), r16])
    (fun j hj => by rw [m2, M1 _ (by omega)]; have := hhp j hj; omega)
    (fun k hk => by rw [m2]; exact f1 k hk) (fun j hj => by omega) (fun j hj => by omega)
    (by omega) (by omega) (fun j hj => by omega) (by omega)
    (by
      rw [sum_congr rfl fun j hj => by rw [Nat.zero_mul, Nat.add_zero, m2, ONE], sum_const,
        card_range, smul_eq_mul]
      omega)
  have q3 : ∀ y, ¬ lgParW y → c₃.nreg y = c.nreg y := fun y hy => by
    rw [n3 y (by unfold lgParW at hy; omega), n2 y (by unfold lgParW at hy; omega), q1 y hy]
  have S3 : ∀ k < kk + 1, c₃.nmem (Zb + k) =
      saF (fun i => c.nmem (HPb + i)) (fun _ => 1) n k := fun k hk => by
    rw [f3 k hk]
    exact saF_congr (fun j hj => by rw [m2, M1 _ (by omega)])
      (fun j hj => by rw [Nat.zero_mul, Nat.add_zero, m2, ONE]) k
  -- the count
  obtain ⟨c₄, t₄, e₄, ht₄, k0, k1, k2, k3, n4, m4, rr4, rm4, o4⟩ := paLK_exec (P := P) c₃
    e₃.wb_right
  obtain ⟨c₅, t₅, e₅, ht₅, f5, -, m5, n5, rr5, rm5, o5⟩ := lkProg_exec (P := P) c₄ e₄.wb_right
    (m := kk) (Fb := Zb + 1) (CIb := Zb + kk + 1) (IXb := Zb + 2 * kk + 1)
    (by rw [k0, n3 _ (by omega), n2 _ (by omega), q1 _ (by unfold lgParW; omega), r70])
    (by rw [k1, n3 _ (by omega), n2 _ (by omega), s21'])
    (by rw [k2, n3 _ (by omega), n2 _ (by omega), s18'])
    (by rw [k3, n3 _ (by omega), n2 _ (by omega), s19']) (by omega) (by omega) (by omega)
    (by omega)
  have NT : c₅.nreg 6306 = nt := by
    rw [f5, hnt]
    unfold cnt
    congr 1
    refine filter_congr fun j hj => ?_
    have := mem_range.1 hj
    show 0 < c₄.nmem (Zb + 1 + j) ↔ 0 < saF (fun i => c.nmem (HPb + i)) (fun _ => 1) n (j + 1)
    rw [m4, show Zb + 1 + j = Zb + (j + 1) by omega, S3 _ (by omega)]
  have q5 : ∀ y, ¬ lgParW y → c₅.nreg y = c.nreg y := fun y hy => by
    rw [n5 y (by unfold lgParW at hy; omega), n4 y (by unfold lgParW at hy; omega), q3 y hy]
  -- the square root
  obtain ⟨c₆, t₆, e₆, ht₆, v14, v00, n6, m6, rr6, rm6, o6⟩ := paSQ_exec (P := P) c₅ e₅.wb_right
    (n := n) (by rw [q5 _ (by unfold lgParW; omega), r00]) (by omega)
  obtain ⟨c₇, t₇, e₇, ht₇, v02, n7, m7, rr7, rm7, o7⟩ := sqLoop_exec (P := P) c₆ e₆.wb_right v00
    (by rw [n6 _ (by omega) (by omega), q5 _ (by unfold lgParW; omega), r06]) (by omega)
  have q7 : ∀ y, ¬ lgParW y → c₇.nreg y = c.nreg y := fun y hy => by
    rw [n7 y (by unfold lgParW at hy; omega), n6 y (by unfold lgParW at hy; omega)
      (by unfold lgParW at hy; omega), q5 y hy]
  have hsq : Nat.sqrt (n + n) ≤ 2 * n := by
    have := Nat.sqrt_le_self (n + n); omega
  -- the sizes
  obtain ⟨c₈, t₈, e₈, ht₈, v23, v24, v25, v05, n8, m8, rr8, rm8, o8⟩ := pb1_exec (P := P) c₇
    e₇.wb_right (n := n) (s := Nat.sqrt (n + n)) (by rw [q7 _ (by unfold lgParW; omega), r00]) v02
    (by rw [q7 _ (by unfold lgParW; omega), r06]) hsq w'
  have N8 : c₈.nreg 5914 = nt := by
    rw [n8 _ (by omega), n7 _ (by omega), v14, NT]
  -- the flag
  obtain ⟨c₉, t₉, e₉, ht₉, v13, n9, m9, rr9, rm9, o9⟩ := pb2_exec (P := P) c₈ e₈.wb_right
    (nt := nt) (bfl := bfl) N8
    (by rw [n8 _ (by omega), q7 _ (by unfold lgParW; omega), r15])
    (by rw [n8 _ (by omega), q7 _ (by unfold lgParW; omega), r06]) hb (by omega)
  -- the parameters
  have hb3 : ∀ s, s ≤ 2 * n → n + 6 * (n + 3 * (6 * s + 4) + 2) +
      ((2 * n + 2 + 9 * (6 * s + 4)) / 3 + 1) +
      ((2 * (n + 6 * (n + 3 * (6 * s + 4) + 2)) + 2 + 9 * (6 * s + 4)) / 3 + 1) ≤
      600 * n + 300 := by
    intro s hs; omega
  have hbf : bf (bfl = 1 ∧ nt = 6) ≤ 1 := by unfold bf; split_ifs <;> omega
  obtain ⟨c₁₀, t₁₀, e₁₀, ht₁₀, v10, v11, v12, n10, m10, rr10, rm10, o10⟩ := pb3_exec (P := P) c₉
    e₉.wb_right (n := n) (nt := nt)
    (by rw [n9 _ (by omega), n8 _ (by omega), q7 _ (by unfold lgParW; omega), r00])
    (by rw [n9 _ (by omega), N8]) v13 (by rw [n9 _ (by omega), v24])
    (by rw [n9 _ (by omega), v25]) (by rw [n9 _ (by omega), v05])
    (by rw [n9 _ (by omega), n8 _ (by omega), q7 _ (by unfold lgParW; omega), r06]) hbf
    (fun h => by unfold bf at h; split_ifs at h with h'; exact h'.2)
    (le_trans (hb3 _ hsq) w')
  have hbf1 : bf (bfl = 1 ∧ nt = 6) = 1 ↔ (bfl = 1 ∧ nt = 6) := by
    unfold bf; split_ifs with h' <;> simp [h']
  simp only [hbf1] at v10 v11 v12
  refine ⟨c₁₀, t₀ + (t₁ + ((t₂ + t₃) + ((t₄ + t₅) + ((t₆ + t₇) + (t₈ + (t₉ + t₁₀)))))),
    .seq e₀ (.seq e₁ (.seq (.seq e₂ e₃) (.seq (.seq e₄ e₅) (.seq (.seq e₆ e₇)
      (.seq e₈ (.seq e₉ e₁₀)))))), ?_, ?_, ?_, v10, v11, v12, fun a ha => ?_, fun y hy => ?_,
    by rw [rr10, rr9, rr8, rr7, rr6, rr5, rr4, rr3, rr2, rr1, rr0],
    by rw [rm10, rm9, rm8, rm7, rm6, rm5, rm4, rm3, rm2, rm1, rm0],
    by rw [o10, o9, o8, o7, o6, o5, o4, o3, o2, o1, o0]⟩
  · have := Nat.sqrt_le_self (n + n)
    omega
  · rw [n10 _ (by omega), n9 _ (by omega), N8]
  · rw [n10 _ (by omega), v13]
  · rw [m10, m9, m8, m7, m6, m5 a (by omega), m4, m3 a (by omega), m2, M1 a ha]
  · rw [n10 y (by unfold lgParW at hy; omega), n9 y (by unfold lgParW at hy; omega),
      n8 y (by unfold lgParW at hy; omega), q7 y hy]

end Exec

/-! ### The parameters on a record -/

lemma lS_eq' (P : Finset D) : lS P = 6 * Nat.sqrt (P.card + P.card) + 4 := by
  unfold lS; rw [two_mul]

lemma kH_eq' (P : Finset D) : kH P = P.card + 3 * (6 * Nat.sqrt (P.card + P.card) + 4) + 2 := by
  unfold kH; rw [lS_eq']

lemma aS_eq' (P : Finset D) :
    aS P = (2 * P.card + 2 + 9 * (6 * Nat.sqrt (P.card + P.card) + 4)) / 3 + 1 := by
  unfold aS; rw [lS_eq']

lemma aH_eq' (P : Finset D) :
    aH P = (2 * (P.card + 6 * (P.card + 3 * (6 * Nat.sqrt (P.card + P.card) + 4) + 2)) + 2 +
      9 * (6 * Nat.sqrt (P.card + P.card) + 4)) / 3 + 1 := by
  unfold aH; rw [kH_eq', lS_eq']

lemma holeStep_iff {P : Finset D} {Hs : List (Finset V)} {b : Bool} :
    holeStep M P Hs b = true ↔ (b = true ∧ nTouch M P Hs = 6) := by
  unfold holeStep; simp

section Exec

variable {P : Input} {W : ℕ}

/-- **The parameters of the split of a recorded piece**: from the record's hole labels and the
flag `bfl` of the call (`bfl = 1 ↔ b`), `r5914 = nTouch`, `r5913 = bf (holeStep P Hs b)`,
`r5910 = K`, `r5911 = A`, `r5912 = #P + K · nTouch` with `K = kH P`, `A = aH P` for the split by
holes and `K = 0`, `A = aS P` for the split by size. -/
theorem lgPar_rec {gid : D → ℕ} {ν : V → ℕ} {S T : Finset V} {x : MCall M} {m n R : ℕ}
    {g : ℕ → D} (c : Config) (hc : WordsBounded W c) (hA : RArr M gid ν S T x m n R g c.nmem)
    (hd : x.2.1.Pairwise Disjoint) {bfl Zb : ℕ} {b : Bool} (hbfl : bfl = 1 ↔ b = true)
    (r00 : c.nreg 5800 = n) (r02 : c.nreg 5802 = R + 3 + 2 * n) (r06 : c.nreg 5806 = 1)
    (r70 : c.nreg 5870 = x.2.1.length) (r15 : c.nreg 5915 = bfl) (r16 : c.nreg 5916 = Zb)
    (r21 : c.nreg 6521 = 1) (hb : bfl ≤ 1) (l : R + 3 + 3 * n ≤ Zb)
    (w : Zb + 3 * x.2.1.length + 2 ≤ W) (w' : 600 * n + 300 ≤ W) :
    ∃ c' t, Exec P W lgPar c c' t ∧ t ≤ 30 * n + 30 * x.2.1.length + 100 ∧
      c'.nreg 5914 = nTouch M x.1.piece x.2.1 ∧
      c'.nreg 5913 = bf (holeStep M x.1.piece x.2.1 b = true) ∧
      c'.nreg 5910 = (if holeStep M x.1.piece x.2.1 b = true then kH x.1.piece else 0) ∧
      c'.nreg 5911 = (if holeStep M x.1.piece x.2.1 b = true then aH x.1.piece
        else aS x.1.piece) ∧
      c'.nreg 5912 = x.1.piece.card +
        (if holeStep M x.1.piece x.2.1 b = true then kH x.1.piece else 0) *
          nTouch M x.1.piece x.2.1 ∧
      (∀ a, ¬ (Zb ≤ a ∧ a < Zb + 3 * x.2.1.length + 2) → c'.nmem a = c.nmem a) ∧
      (∀ y, ¬ lgParW y → c'.nreg y = c.nreg y) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, v14, v13, v10, v11, v12, hm, hr, rr, rm, oo⟩ := lgPar_exec (P := P) c hc
    r00 r02 r06 r70 r15 r16 r21 hb (fun i hi => by rw [hA.hp i hi]; exact hlab_le _ _)
    (by omega) w w'
  have hnt : cnt (fun j => saF (fun i => c.nmem (R + 3 + 2 * n + i)) (fun _ => 1) n (j + 1))
      x.2.1.length = nTouch M x.1.piece x.2.1 :=
    (nTouch_cnt hd hA.g_mem hA.g_surj hA.hp).symm
  have hcard : x.1.piece.card = n := hA.card.symm
  have hiff : (bfl = 1 ∧ nTouch M x.1.piece x.2.1 = 6) ↔ holeStep M x.1.piece x.2.1 b = true := by
    rw [holeStep_iff, hbfl]
  rw [hnt] at v14 v13 v10 v11 v12
  refine ⟨c', t, ex, ht, v14, ?_, ?_, ?_, ?_, hm, hr, rr, rm, oo⟩
  · rw [v13]; unfold bf; simp only [hiff]
  · rw [v10, kH_eq', hcard]; simp only [hiff]
  · rw [v11, aH_eq', aS_eq', hcard]; simp only [hiff]
  · rw [v12, kH_eq', hcard]; simp only [hiff]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
