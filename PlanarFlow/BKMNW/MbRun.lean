module

public import PlanarFlow.BKMNW.MbArr
public import PlanarFlow.BKMNW.LevelProg

/-!
# Miller's base, step 2: the frame image in place, and the run of `encProg ; msep`

After `mcProg` (`MbArr.lean`) the index arrays of the piece map `psep M hσ hB`, numbered by
`cNe e n N`, are at `CRb`, `CSb`, `CEb` (above the work area). This file reproduces the canonical
frame image `encInZ … Bz` of `sepC` (`MbSep.lean`) **in place** on the memory `[0, Wr]`
(`Wr = encWZ Bz #N (Σ ex + #N)`) and on the registers `mbU` named by `encProg ; msep`, after
saving `[0, Wr]` to `SVb`, and runs `encProg ; msep`: by `sepC_insitu` the run decodes to
`sepC M e n Bz N σ hσ hB ex`.

* `mbZeroRegs L` (one `constN r 0` per register of `L`), **`mbZeroRegs_exec`** (any list, by
  induction); `mbUL` (the registers `mbU` as a list), `mem_mbUL`;
* `mzBody`, **`mzFill`** (`mem[Zb + j] := 0`, `j < len`; registers `5030 … 5035`),
  `mzFill_exec`;
* **`encInZ_nmem_of`** (memory zero on `[0, Wr]` outside the three arrays, arrays `EncArr` at
  `B₀`, `B₀ + 7m`, `B₀ + 8m` ⟹ it is the frame image's on `[0, Wr]`);
* `mbW` (the word bound `Wr` into `5040`), `mbSv`, `mbZ`, `mbCp`, `mbRg`, **`mbIn`**,
  **`mbIn_exec`**.
Registers: inputs `5012 = #N`, `5021 = Σ_N ex`, `5041 = Bz`, `5046 = SVb`, `5009 = CRb`,
`5018 = CSb`, `5019 = CEb`; written `5030 … 5049`, `4910 … 4916` (`cpArr`), the registers `mbU`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### Zeroing registers -/

/-- One `constN r 0` per register of `L`. -/
def mbZeroRegs (L : List ℕ) : Stmt := block (L.map fun r => .constN r 0)

section Zero

variable {P : Input} {W : ℕ}

/-- **Zeroing a list of registers**: `|L|` steps, the registers of `L` are `0`, nothing else
changes. -/
theorem mbZeroRegs_exec (L : List ℕ) (c : Config) (hc : WordsBounded W c) :
    Exec P W (mbZeroRegs L) c { c with nreg := fun r => if r ∈ L then 0 else c.nreg r } L.length := by
  induction L generalizing c with
  | nil =>
    have : ({ c with nreg := fun r => if r ∈ ([] : List ℕ) then 0 else c.nreg r } : Config) = c := by
      cases c; simp
    rw [this]; exact .skip hc
  | cons r L ih =>
    set c₁ : Config := { c with nreg := upd c.nreg r 0 } with hc₁
    have hw₁ : WordsBounded W c₁ := ⟨fun x => by
      simp only [hc₁, upd_apply]; split_ifs
      · exact Nat.zero_le _
      · exact hc.1 x, hc.2⟩
    have e₁ : Exec P W (.instr (.constN r 0)) c c₁ 1 := .instr (by simp) rfl hc hw₁
    have e₂ := ih c₁ hw₁
    have heq : ({ c₁ with nreg := fun x => if x ∈ L then 0 else c₁.nreg x } : Config) =
        { c with nreg := fun x => if x ∈ r :: L then 0 else c.nreg x } := by
      simp only [hc₁, List.mem_cons]
      congr 1
      funext x
      by_cases h1 : x = r
      · subst h1; simp
      · by_cases h2 : x ∈ L
        · simp [h2]
        · simp [h1, h2, upd_apply]
    rw [heq] at e₂
    have := Exec.seq e₁ e₂
    rw [show 1 + L.length = (r :: L).length by simp; omega] at this
    exact this

/-- `mbZeroRegs_exec` with the final configuration described by its properties. -/
theorem mbZeroRegs_exec' (L : List ℕ) (c : Config) (hc : WordsBounded W c) :
    ∃ c', Exec P W (mbZeroRegs L) c c' L.length ∧ (∀ r ∈ L, c'.nreg r = 0) ∧
      (∀ r, r ∉ L → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output :=
  ⟨_, mbZeroRegs_exec L c hc, fun r hr => by simp [hr], fun r hr => by simp [hr], rfl, rfl, rfl,
    rfl⟩

end Zero

/-- The registers `mbU` as a list. -/
def mbUL : List ℕ := List.range 700 ++ List.range' 4400 300

lemma mem_mbUL (r : ℕ) : r ∈ mbUL ↔ mbU r = true := by
  simp only [mbUL, List.mem_append, List.mem_range, List.mem_range', mbU, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨i, hi, rfl⟩) <;> omega
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r - 4400, by omega, by omega⟩

lemma mbUL_length : mbUL.length = 1000 := by simp [mbUL]

/-! ### Zeroing memory -/

/-- `mem[Zb + j] := 0` (`5031 = Zb`, `5032 = 0`, `5033 = 1`, `5034 = j`). -/
def mzBody : Stmt := block [.addN 5035 5031 5034, .storeN 5035 5032, .addN 5034 5034 5033]

/-- **Zero `len = r5030` cells from `Zb = r5031`.** -/
def mzFill : Stmt :=
  .seq (block [.constN 5032 0, .constN 5033 1, .constN 5034 0]) (.whileLtN 5034 5030 mzBody)

section Fill

variable {P : Input} {W : ℕ}

theorem mzBody_exec (c : Config) (hc : WordsBounded W c) {Zb j : ℕ}
    (r1 : c.nreg 5031 = Zb) (r2 : c.nreg 5032 = 0) (r3 : c.nreg 5033 = 1) (r4 : c.nreg 5034 = j)
    (w1 : Zb + j ≤ W) (w2 : j + 1 ≤ W) :
    ∃ c' t, Exec P W mzBody c c' t ∧ t = 3 ∧ c'.nreg 5034 = j + 1 ∧
      c'.nmem = upd c.nmem (Zb + j) 0 ∧
      (∀ x, (x < 5034 ∨ 5035 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mzBody
  exec_block
  all_goals try (config_simp; first | done | omega | (simp only [r1, r2, r3, r4]; omega) | (simp only [r1, r2, r3, r4]; done))
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r3, r4]
  · config_simp; simp only [r1, r2, r4]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **Zeroing**: within `5 len + 5` steps `[Zb, Zb + len)` is zero; other memory, registers
outside `5032 … 5035`, reals and output kept. -/
theorem mzFill_exec (c : Config) (hc : WordsBounded W c) {len Zb : ℕ}
    (r0 : c.nreg 5030 = len) (r1 : c.nreg 5031 = Zb) (w : Zb + len ≤ W) (w' : len + 1 ≤ W) :
    ∃ c' t, Exec P W mzFill c c' t ∧ t ≤ 5 * len + 5 ∧
      (∀ i < len, c'.nmem (Zb + i) = 0) ∧
      (∀ a, (a < Zb ∨ Zb + len ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5032 ∨ 5035 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mzFill
  obtain ⟨c₁, k₁, e₁, hk₁, g2, g3, g4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 5032 0, .constN 5033 1, .constN 5034 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 5032 = 0 ∧ c₁.nreg 5033 = 1 ∧ c₁.nreg 5034 = 0 ∧
      (∀ x, (x < 5032 ∨ 5034 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    obtain ⟨a1, a2, a3⟩ : x ≠ 5032 ∧ x ≠ 5033 ∧ x ≠ 5034 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3]
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 5032 ∨ 5034 < x) → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 5034 ∨ 5035 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (Zb + j) = 0) ∧
    (∀ a, (a < Zb ∨ Zb + len ≤ a) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h34, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 5034) (b := 5030) (body := mzBody) J (B := 3) c₁ hw₁ g4
    (by rw [q _ (by omega), r0]) (Nat.zero_le len)
    ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega), fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h34 h30 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 5034 ∨ 5035 < x) → c'.nreg x = c₁.nreg x := j1
      obtain ⟨c'', t, ex, ht, h34', hm', hn', hr', hrm', ho'⟩ :=
        mzBody_exec (P := P) c' hw (by rw [f _ (by omega), q _ (by omega), r1])
          (by rw [f _ (by omega), g2]) (by rw [f _ (by omega), g3]) h34 (by omega) (by omega)
      refine ⟨c'', t, ex, ht.le, h34', by rw [hn' _ (by omega)]; exact h30,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (by omega)]; exact j3 a ha)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3,
    fun x hx => by rw [j1 x (by omega), q x (by omega)], by rw [j4, gr₁], by rw [j5, grm₁],
    by rw [j6, go₁]⟩

end Fill

/-! ### The frame image from the arrays -/

section Img

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]

/-- **The frame image on `[0, Wr]`**: zero outside the three arrays, the arrays `EncArr` at
`B₀`, `B₀ + 7m`, `B₀ + 8m`. -/
theorem encInZ_nmem_of (M : PlanarSeparator.Map D Q) {m : ℕ} (c : D ≃ Fin m) (ex : D → ℕ)
    {B₀ Wr : ℕ} {mem : ℕ → ℕ} (hA : EncArr M c ex mem B₀ (B₀ + 7 * m) (B₀ + 8 * m))
    (hz : ∀ a ≤ Wr, ¬ (B₀ ≤ a ∧ a < B₀ + m) → ¬ (B₀ + 7 * m ≤ a ∧ a < B₀ + 8 * m) →
      ¬ (B₀ + 8 * m ≤ a ∧ a < B₀ + 9 * m) → mem a = 0) :
    ∀ a ≤ Wr, mem a = (encInZ M c ex B₀).nmem a := by
  intro a ha
  simp only [encInZ]
  split_ifs with h1 h2 h3
  · obtain ⟨d, hd⟩ : ∃ d, (c d : ℕ) = a - B₀ := ⟨c.symm ⟨a - B₀, by omega⟩, by simp⟩
    have := hA.rev d
    rw [hd, show B₀ + (a - B₀) = a by omega] at this
    rw [this, ← hd, darr_c]
  · obtain ⟨d, hd⟩ : ∃ d, (c d : ℕ) = a - (B₀ + 7 * m) :=
      ⟨c.symm ⟨a - (B₀ + 7 * m), by omega⟩, by simp⟩
    have := hA.sig d
    rw [hd, show B₀ + 7 * m + (a - (B₀ + 7 * m)) = a by omega] at this
    rw [this, ← hd, darr_c]
  · obtain ⟨d, hd⟩ : ∃ d, (c d : ℕ) = a - (B₀ + 8 * m) :=
      ⟨c.symm ⟨a - (B₀ + 8 * m), by omega⟩, by simp⟩
    have := hA.ex d
    rw [hd, show B₀ + 8 * m + (a - (B₀ + 8 * m)) = a by omega] at this
    rw [this, ← hd, darr_c]
  · exact hz a ha h1 h2 h3

end Img

/-! ### The preparation in place and the run -/

/-- The word bound `Wr = Bz + 25 m + 3 S + 14` (`5040`), `Wr + 1` (`5045`), `Bz + 7m`, `Bz + 8m`,
`Bz + 9m` (`5047 … 5049`), from `m = r5012`, `S = r5021`, `Bz = r5041`. -/
def mbW : Stmt :=
  block [.constN 5042 25, .mulN 5043 5012 5042, .constN 5042 3, .mulN 5044 5021 5042,
    .addN 5040 5041 5043, .addN 5040 5040 5044, .constN 5042 14, .addN 5040 5040 5042,
    .constN 5042 1, .addN 5045 5040 5042, .constN 5042 7, .mulN 5043 5012 5042,
    .addN 5047 5041 5043, .addN 5048 5047 5012, .addN 5049 5048 5012]

/-- Save `[0, Wr]` to `SVb = r5046`. -/
def mbSv : Stmt := .seq (block [.copyN 4910 5045, .constN 4911 0, .copyN 4912 5046]) cpArr

/-- Zero `[0, Wr]`. -/
def mbZ : Stmt := .seq (block [.copyN 5030 5045, .constN 5031 0]) mzFill

/-- Copy the three arrays to `Bz`, `Bz + 7m`, `Bz + 8m`. -/
def mbCp : Stmt :=
  .seq (.seq (block [.copyN 4910 5012, .copyN 4911 5009, .copyN 4912 5041]) cpArr)
    (.seq (.seq (block [.copyN 4911 5018, .copyN 4912 5047]) cpArr)
      (.seq (block [.copyN 4911 5019, .copyN 4912 5048]) cpArr))

/-- Zero the registers `mbU`, then the registers `4660 … 4664` of `encProg`. -/
def mbRg : Stmt :=
  .seq (mbZeroRegs mbUL)
    (block [.copyN 4660 5012, .copyN 4661 5041, .copyN 4662 5047, .copyN 4663 5048,
      .copyN 4664 5049])

/-- The preparation. -/
def mbPre : Stmt := .seq mbW (.seq mbSv (.seq mbZ (.seq mbCp mbRg)))

/-- **The frame image in place, and the run of `encProg ; msep`.** -/
def mbIn : Stmt := .seq mbPre (.seq encProg msep)

section Pre

variable {P : Input} {W : ℕ}

theorem mbW_exec (c : Config) (hc : WordsBounded W c) {m S Bz : ℕ}
    (r12 : c.nreg 5012 = m) (r21 : c.nreg 5021 = S) (r41 : c.nreg 5041 = Bz)
    (hW : Bz + 25 * m + 3 * S + 15 ≤ W) (hW25 : 25 ≤ W) :
    ∃ c' t, Exec P W mbW c c' t ∧ t = 15 ∧
      c'.nreg 5040 = Bz + 25 * m + 3 * S + 14 ∧ c'.nreg 5045 = Bz + 25 * m + 3 * S + 15 ∧
      c'.nreg 5047 = Bz + 7 * m ∧ c'.nreg 5048 = Bz + 8 * m ∧ c'.nreg 5049 = Bz + 9 * m ∧
      (∀ x, (x < 5040 ∨ x = 5041 ∨ x = 5046 ∨ 5049 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mbW
  exec_block
  all_goals try (config_simp; first | done | omega | (simp only [r12, r21, r41]; omega) | (simp only [r12, r21, r41]; done))
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; first | done | omega | (simp only [r12, r21, r41]; omega) | (simp only [r12, r21, r41]; done))
  config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem mbRg_exec (c : Config) (hc : WordsBounded W c) {m Bz : ℕ}
    (r12 : c.nreg 5012 = m) (r41 : c.nreg 5041 = Bz) (r47 : c.nreg 5047 = Bz + 7 * m)
    (r48 : c.nreg 5048 = Bz + 8 * m) (r49 : c.nreg 5049 = Bz + 9 * m) :
    ∃ c' t, Exec P W mbRg c c' t ∧ t = 1005 ∧
      (∀ r, mbU r = true → c'.nreg r = if r = 4660 then m else if r = 4661 then Bz else
        if r = 4662 then Bz + 7 * m else if r = 4663 then Bz + 8 * m else
        if r = 4664 then Bz + 9 * m else 0) ∧
      (∀ x, mbU x = false → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁₂, e₁₂, z₁₂, n₁₂', m₁₂, r₁₂, rm₁₂, o₁₂⟩ := mbZeroRegs_exec' (P := P) mbUL c hc
  have hw₁₂ := e₁₂.wb_right
  have n₁₂ : ∀ x, mbU x = false → c₁₂.nreg x = c.nreg x := fun x hx =>
    n₁₂' x (fun h => by rw [mem_mbUL] at h; rw [h] at hx; exact absurd hx (by simp))
  have t12 : c₁₂.nreg 5012 = m := by rw [n₁₂ _ (by simp [mbU]), r12]
  have t41 : c₁₂.nreg 5041 = Bz := by rw [n₁₂ _ (by simp [mbU]), r41]
  have t47 : c₁₂.nreg 5047 = Bz + 7 * m := by rw [n₁₂ _ (by simp [mbU]), r47]
  have t48 : c₁₂.nreg 5048 = Bz + 8 * m := by rw [n₁₂ _ (by simp [mbU]), r48]
  have t49 : c₁₂.nreg 5049 = Bz + 9 * m := by rw [n₁₂ _ (by simp [mbU]), r49]
  have e' : Exec P W (mbZeroRegs mbUL) c c₁₂ 1000 := by rw [← mbUL_length]; exact e₁₂
  clear e₁₂ n₁₂'
  obtain ⟨c₁₃, k₁₃, e₁₃, hk₁₃, v60, v61, v62, v63, v64, vn₁₃, vm₁₃, vr₁₃, vrm₁₃, vo₁₃⟩ : ∃ c₁₃ k₁₃,
      Exec P W (block [.copyN 4660 5012, .copyN 4661 5041, .copyN 4662 5047, .copyN 4663 5048,
        .copyN 4664 5049]) c₁₂ c₁₃ k₁₃ ∧ k₁₃ = 5 ∧
      c₁₃.nreg 4660 = m ∧ c₁₃.nreg 4661 = Bz ∧ c₁₃.nreg 4662 = Bz + 7 * m ∧
      c₁₃.nreg 4663 = Bz + 8 * m ∧ c₁₃.nreg 4664 = Bz + 9 * m ∧
      (∀ x, (x < 4660 ∨ 4664 < x) → c₁₃.nreg x = c₁₂.nreg x) ∧ c₁₃.nmem = c₁₂.nmem ∧
      c₁₃.rreg = c₁₂.rreg ∧ c₁₃.rmem = c₁₂.rmem ∧ c₁₃.output = c₁₂.output := by
    exec_block
    all_goals try (config_simp; first | done | omega | (simp only [t12, t41, t47, t48, t49]; omega))
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; (try simp only [t12, t41, t47, t48, t49]); done)
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₁₃, 1000 + k₁₃, .seq e' e₁₃, by omega, fun r hr => ?_, fun x hx => ?_,
    by rw [vm₁₃, m₁₂], by rw [vr₁₃, r₁₂], by rw [vrm₁₃, rm₁₂], by rw [vo₁₃, o₁₂]⟩
  · have hr' : r ∈ mbUL := (mem_mbUL r).2 hr
    by_cases h60 : r = 4660
    · subst h60; rw [v60]; rfl
    by_cases h61 : r = 4661
    · subst h61; rw [v61]; rfl
    by_cases h62 : r = 4662
    · subst h62; rw [v62]; rfl
    by_cases h63 : r = 4663
    · subst h63; rw [v63]; rfl
    by_cases h64 : r = 4664
    · subst h64; rw [v64]; rfl
    rw [iteF h60, iteF h61, iteF h62, iteF h63, iteF h64, vn₁₃ _ (by omega)]
    exact z₁₂ r hr'
  · have h1 : ¬ (4660 ≤ x ∧ x ≤ 4664) := fun h => by
      have : mbU x = true := by simp [mbU]; omega
      rw [this] at hx; exact absurd hx (by simp)
    rw [vn₁₃ _ (by omega), n₁₂ x hx]

set_option maxHeartbeats 1600000 in
/-- **The preparation**: save `[0, Wr]` to `SVb`, zero it, write the three arrays at `Bz`,
`Bz + 7m`, `Bz + 8m`, zero the registers `mbU`, set `4660 … 4664`. Afterwards the memory on
`[0, Wr]` and the registers `mbU` are those of the frame image (`encInZ_nmem_of`). -/
theorem mbPre_exec (c : Config) (hc : WordsBounded W c) {m S Bz SVb CRb CSb CEb : ℕ}
    (r12 : c.nreg 5012 = m) (r21 : c.nreg 5021 = S) (r41 : c.nreg 5041 = Bz)
    (r46 : c.nreg 5046 = SVb) (r09 : c.nreg 5009 = CRb) (r18 : c.nreg 5018 = CSb)
    (r19 : c.nreg 5019 = CEb)
    (lay : Bz + 25 * m + 3 * S + 14 < CRb ∧ CRb + m ≤ SVb ∧
      Bz + 25 * m + 3 * S + 14 < CSb ∧ CSb + m ≤ SVb ∧
      Bz + 25 * m + 3 * S + 14 < CEb ∧ CEb + m ≤ SVb ∧
      SVb + (Bz + 25 * m + 3 * S + 15) + 1 ≤ W ∧ 25 ≤ W) :
    ∃ c' t, Exec P W mbPre c c' t ∧ t ≤ 12 * (Bz + 25 * m + 3 * S + 15) + 21 * m + 1060 ∧
      (∀ i < m, c'.nmem (Bz + i) = c.nmem (CRb + i)) ∧
      (∀ i < m, c'.nmem (Bz + 7 * m + i) = c.nmem (CSb + i)) ∧
      (∀ i < m, c'.nmem (Bz + 8 * m + i) = c.nmem (CEb + i)) ∧
      (∀ a ≤ Bz + 25 * m + 3 * S + 14, ¬ (Bz ≤ a ∧ a < Bz + m) →
        ¬ (Bz + 7 * m ≤ a ∧ a < Bz + 8 * m) → ¬ (Bz + 8 * m ≤ a ∧ a < Bz + 9 * m) →
        c'.nmem a = 0) ∧
      (∀ a ≤ Bz + 25 * m + 3 * S + 14, c'.nmem (SVb + a) = c.nmem a) ∧
      (∀ a, Bz + 25 * m + 3 * S + 14 < a → ¬ (SVb ≤ a ∧ a < SVb + (Bz + 25 * m + 3 * S + 15)) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, mbU r = true → c'.nreg r = if r = 4660 then m else if r = 4661 then Bz else
        if r = 4662 then Bz + 7 * m else if r = 4663 then Bz + 8 * m else
        if r = 4664 then Bz + 9 * m else 0) ∧
      c'.nreg 5040 = Bz + 25 * m + 3 * S + 14 ∧ c'.nreg 5045 = Bz + 25 * m + 3 * S + 15 ∧
      (∀ x, mbU x = false → (x < 4910 ∨ (4916 < x ∧ x < 5030) ∨ x = 5041 ∨ x = 5046 ∨
        5049 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := lay
  set Wr := Bz + 25 * m + 3 * S + 14 with hWr
  set L := Bz + 25 * m + 3 * S + 15 with hL
  unfold mbPre
  -- the word bound
  obtain ⟨c₁, k₁, e₁, hk₁, a40, a45, a47, a48, a49, an₁, am₁, ar₁, arm₁, ao₁⟩ :=
    mbW_exec (P := P) c hc r12 r21 r41 (by omega) l8
  have hw₁ := e₁.wb_right
  -- save
  obtain ⟨c₂, k₂, e₂, hk₂, b10, b11, b12, bn₂, bm₂, br₂, brm₂, bo₂⟩ : ∃ c₂ k₂,
      Exec P W (block [.copyN 4910 5045, .constN 4911 0, .copyN 4912 5046]) c₁ c₂ k₂ ∧ k₂ = 3 ∧
      c₂.nreg 4910 = L ∧ c₂.nreg 4911 = 0 ∧ c₂.nreg 4912 = SVb ∧
      (∀ x, (x < 4910 ∨ 4912 < x) → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have t46 : c₁.nreg 5046 = SVb := by rw [an₁ _ (by omega), r46]
    exec_block
    all_goals try (config_simp; first | done | omega | (simp only [a45, t46]; omega) | (simp only [a45, t46]; done))
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => by
      obtain ⟨b1, b2, b3⟩ : x ≠ 4910 ∧ x ≠ 4911 ∧ x ≠ 4912 := by omega
      simp only [Config.nreg_mk, upd_other _ _ _ b1, upd_other _ _ _ b2, upd_other _ _ _ b3],
      rfl, rfl, rfl, rfl⟩
    all_goals (config_simp; first | done | omega | (simp only [a45, t46]; omega) |
      (simp only [a45, t46]; done))
  have hw₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, sv₃, sm₃, sn₃, sr₃, srm₃, so₃⟩ :=
    cpArr_exec (P := P) c₂ hw₂ b10 b11 b12 ⟨by omega, by omega, by omega, by omega⟩
  have hw₃ := e₃.wb_right
  -- zero
  obtain ⟨c₄, k₄, e₄, hk₄, z30, z31, zn₄, zm₄, zr₄, zrm₄, zo₄⟩ : ∃ c₄ k₄,
      Exec P W (block [.copyN 5030 5045, .constN 5031 0]) c₃ c₄ k₄ ∧ k₄ = 2 ∧
      c₄.nreg 5030 = L ∧ c₄.nreg 5031 = 0 ∧
      (∀ x, (x < 5030 ∨ 5031 < x) → c₄.nreg x = c₃.nreg x) ∧ c₄.nmem = c₃.nmem ∧
      c₄.rreg = c₃.rreg ∧ c₄.rmem = c₃.rmem ∧ c₄.output = c₃.output := by
    have t45 : c₃.nreg 5045 = L := by rw [sn₃ _ (by omega), bn₂ _ (by omega), a45]
    exec_block
    all_goals try (config_simp; first | done | omega | (simp only [t45]; omega) | (simp only [t45]; done))
    refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; (try simp only [t45]); done)
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₄ := e₄.wb_right
  obtain ⟨c₅, k₅, e₅, hk₅, zz₅, zm₅, zn₅, zr₅, zrm₅, zo₅⟩ :=
    mzFill_exec (P := P) c₄ hw₄ z30 z31 (by omega) (by omega)
  have hw₅ := e₅.wb_right
  -- the registers of `c` seen at `c₅`
  have g5 : ∀ x, (x < 4910 ∨ (4916 < x ∧ x < 5030) ∨ (5035 < x ∧ x < 5040) ∨ x = 5041 ∨
      x = 5046 ∨ 5049 < x) → c₅.nreg x = c.nreg x := fun x hx => by
    rw [zn₅ _ (by omega), zn₄ _ (by omega), sn₃ _ (by omega), bn₂ _ (by omega),
      an₁ _ (by omega)]
  have g5' : ∀ x, 5040 ≤ x → x ≤ 5049 → 5035 < x → c₅.nreg x = c₁.nreg x := fun x h1 h2 h3 => by
    rw [zn₅ _ (by omega), zn₄ _ (by omega), sn₃ _ (by omega), bn₂ _ (by omega)]
  -- memory of `c` above `Wr`, off the save area, seen at `c₅`
  have mem₅ : ∀ a, Wr < a → ¬ (SVb ≤ a ∧ a < SVb + L) → c₅.nmem a = c.nmem a := fun a h1 h2 => by
    rw [zm₅ a (by omega), zm₄, sm₃ a (by omega), bm₂, am₁]
  have sv₅ : ∀ a ≤ Wr, c₅.nmem (SVb + a) = c.nmem a := fun a ha => by
    rw [zm₅ (SVb + a) (by omega), zm₄, sv₃ a (by omega), bm₂, am₁]; simp
  -- copies
  obtain ⟨c₆, k₆, e₆, hk₆, p10, p11, p12, pn₆, pm₆, pr₆, prm₆, po₆⟩ : ∃ c₆ k₆,
      Exec P W (block [.copyN 4910 5012, .copyN 4911 5009, .copyN 4912 5041]) c₅ c₆ k₆ ∧ k₆ = 3 ∧
      c₆.nreg 4910 = m ∧ c₆.nreg 4911 = CRb ∧ c₆.nreg 4912 = Bz ∧
      (∀ x, (x < 4910 ∨ 4912 < x) → c₆.nreg x = c₅.nreg x) ∧ c₆.nmem = c₅.nmem ∧
      c₆.rreg = c₅.rreg ∧ c₆.rmem = c₅.rmem ∧ c₆.output = c₅.output := by
    have t1 : c₅.nreg 5012 = m := by rw [g5 _ (by omega), r12]
    have t2 : c₅.nreg 5009 = CRb := by rw [g5 _ (by omega), r09]
    have t3 : c₅.nreg 5041 = Bz := by rw [g5 _ (by omega), r41]
    exec_block
    all_goals try (config_simp; first | done | omega | (simp only [t1, t2, t3]; omega) | (simp only [t1, t2, t3]; done))
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; (try simp only [t1, t2, t3]); done)
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₆ := e₆.wb_right
  obtain ⟨c₇, k₇, e₇, hk₇, cp₇, cm₇, cn₇, cr₇, crm₇, co₇⟩ :=
    cpArr_exec (P := P) c₆ hw₆ p10 p11 p12 ⟨by omega, by omega, by omega, by omega⟩
  have hw₇ := e₇.wb_right
  obtain ⟨c₈, k₈, e₈, hk₈, q11, q12, qn₈, qm₈, qr₈, qrm₈, qo₈⟩ : ∃ c₈ k₈,
      Exec P W (block [.copyN 4911 5018, .copyN 4912 5047]) c₇ c₈ k₈ ∧ k₈ = 2 ∧
      c₈.nreg 4911 = CSb ∧ c₈.nreg 4912 = Bz + 7 * m ∧
      (∀ x, (x < 4911 ∨ 4912 < x) → c₈.nreg x = c₇.nreg x) ∧ c₈.nmem = c₇.nmem ∧
      c₈.rreg = c₇.rreg ∧ c₈.rmem = c₇.rmem ∧ c₈.output = c₇.output := by
    have t1 : c₇.nreg 5018 = CSb := by
      rw [cn₇ _ (by omega), pn₆ _ (by omega), g5 _ (by omega), r18]
    have t2 : c₇.nreg 5047 = Bz + 7 * m := by
      rw [cn₇ _ (by omega), pn₆ _ (by omega), g5' _ (by omega) (by omega) (by omega), a47]
    exec_block
    all_goals try (config_simp; first | done | omega | (simp only [t1, t2]; omega) | (simp only [t1, t2]; done))
    refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; (try simp only [t1, t2]); done)
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₈ := e₈.wb_right
  obtain ⟨c₉, k₉, e₉, hk₉, cp₉, cm₉, cn₉, cr₉, crm₉, co₉⟩ :=
    cpArr_exec (P := P) c₈ hw₈ (by rw [qn₈ _ (by omega), cn₇ _ (by omega), p10]) q11 q12
      ⟨by omega, by omega, by omega, by omega⟩
  have hw₉ := e₉.wb_right
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, u11, u12, un₁₀, um₁₀, ur₁₀, urm₁₀, uo₁₀⟩ : ∃ c₁₀ k₁₀,
      Exec P W (block [.copyN 4911 5019, .copyN 4912 5048]) c₉ c₁₀ k₁₀ ∧ k₁₀ = 2 ∧
      c₁₀.nreg 4911 = CEb ∧ c₁₀.nreg 4912 = Bz + 8 * m ∧
      (∀ x, (x < 4911 ∨ 4912 < x) → c₁₀.nreg x = c₉.nreg x) ∧ c₁₀.nmem = c₉.nmem ∧
      c₁₀.rreg = c₉.rreg ∧ c₁₀.rmem = c₉.rmem ∧ c₁₀.output = c₉.output := by
    have t1 : c₉.nreg 5019 = CEb := by
      rw [cn₉ _ (by omega), qn₈ _ (by omega), cn₇ _ (by omega), pn₆ _ (by omega),
        g5 _ (by omega), r19]
    have t2 : c₉.nreg 5048 = Bz + 8 * m := by
      rw [cn₉ _ (by omega), qn₈ _ (by omega), cn₇ _ (by omega), pn₆ _ (by omega),
        g5' _ (by omega) (by omega) (by omega), a48]
    exec_block
    all_goals try (config_simp; first | done | omega | (simp only [t1, t2]; omega) | (simp only [t1, t2]; done))
    refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; (try simp only [t1, t2]); done)
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁₀ := e₁₀.wb_right
  obtain ⟨c₁₁, k₁₁, e₁₁, hk₁₁, cp₁₁, cm₁₁, cn₁₁, cr₁₁, crm₁₁, co₁₁⟩ :=
    cpArr_exec (P := P) c₁₀ hw₁₀ (by rw [un₁₀ _ (by omega), cn₉ _ (by omega), qn₈ _ (by omega),
      cn₇ _ (by omega), p10]) u11 u12 ⟨by omega, by omega, by omega, by omega⟩
  have hw₁₁ := e₁₁.wb_right
  have hCR : ∀ i < m, c₁₁.nmem (Bz + i) = c.nmem (CRb + i) := fun i hi => by
    rw [cm₁₁ (Bz + i) (by omega), um₁₀, cm₉ (Bz + i) (by omega), qm₈, cp₇ i hi, pm₆,
      mem₅ (CRb + i) (by omega) (by omega)]
  have hCS : ∀ i < m, c₁₁.nmem (Bz + 7 * m + i) = c.nmem (CSb + i) := fun i hi => by
    rw [cm₁₁ (Bz + 7 * m + i) (by omega), um₁₀, cp₉ i hi, qm₈, cm₇ (CSb + i) (by omega), pm₆,
      mem₅ (CSb + i) (by omega) (by omega)]
  have hCE : ∀ i < m, c₁₁.nmem (Bz + 8 * m + i) = c.nmem (CEb + i) := fun i hi => by
    rw [cp₁₁ i hi, um₁₀, cm₉ (CEb + i) (by omega), qm₈, cm₇ (CEb + i) (by omega), pm₆,
      mem₅ (CEb + i) (by omega) (by omega)]
  have hoff : ∀ a, ¬ (Bz ≤ a ∧ a < Bz + m) → ¬ (Bz + 7 * m ≤ a ∧ a < Bz + 8 * m) →
      ¬ (Bz + 8 * m ≤ a ∧ a < Bz + 9 * m) → c₁₁.nmem a = c₅.nmem a := fun a h1 h2 h3 => by
    rw [cm₁₁ a (by omega), um₁₀, cm₉ a (by omega), qm₈, cm₇ a (by omega), pm₆]
  -- the registers of `c₅` seen at `c₁₁`
  have g11 : ∀ x, (x < 4910 ∨ 4916 < x) → c₁₁.nreg x = c₅.nreg x := fun x hx => by
    rw [cn₁₁ _ (by omega), un₁₀ _ (by omega), cn₉ _ (by omega), qn₈ _ (by omega),
      cn₇ _ (by omega), pn₆ _ (by omega)]
  -- registers
  obtain ⟨c₁₃, k₁₃, e₁₃, hk₁₃, vU, vN, vm₁₃, vr₁₃, vrm₁₃, vo₁₃⟩ :=
    mbRg_exec (P := P) c₁₁ hw₁₁ (m := m) (Bz := Bz)
      (by rw [g11 _ (by omega), g5 _ (by omega), r12]) (by rw [g11 _ (by omega), g5 _ (by omega), r41])
      (by rw [g11 _ (by omega), g5' _ (by omega) (by omega) (by omega), a47])
      (by rw [g11 _ (by omega), g5' _ (by omega) (by omega) (by omega), a48])
      (by rw [g11 _ (by omega), g5' _ (by omega) (by omega) (by omega), a49])
  have hm₁₃ : c₁₃.nmem = c₁₁.nmem := vm₁₃
  refine ⟨c₁₃, k₁ + (k₂ + k₃ + (k₄ + k₅ + ((k₆ + k₇) + ((k₈ + k₉) + (k₁₀ + k₁₁)) + k₁₃))),
    .seq e₁ (.seq (.seq e₂ e₃) (.seq (.seq e₄ e₅) (.seq (.seq (.seq e₆ e₇)
      (.seq (.seq e₈ e₉) (.seq e₁₀ e₁₁))) e₁₃))), by omega,
    fun i hi => by rw [hm₁₃, hCR i hi], fun i hi => by rw [hm₁₃, hCS i hi],
    fun i hi => by rw [hm₁₃, hCE i hi], fun a ha h1 h2 h3 => ?_, fun a ha => ?_,
    fun a h1 h2 => ?_, vU, ?_, ?_, fun x hx1 hx2 => ?_, ?_, ?_, ?_⟩
  · rw [hm₁₃, hoff a h1 h2 h3, show a = 0 + a by omega, zz₅ a (by omega)]
  · rw [hm₁₃, hoff (SVb + a) (by omega) (by omega) (by omega), sv₅ a ha]
  · rw [hm₁₃, hoff a (by omega) (by omega) (by omega), mem₅ a h1 h2]
  · rw [vN _ (by simp [mbU]), g11 _ (by omega), g5' _ (by omega) (by omega) (by omega), a40]
  · rw [vN _ (by simp [mbU]), g11 _ (by omega), g5' _ (by omega) (by omega) (by omega), a45]
  · rw [vN x hx1, g11 _ (by omega), g5 _ (by omega)]
  · rw [vr₁₃, cr₁₁, ur₁₀, cr₉, qr₈, cr₇, pr₆, zr₅, zr₄, sr₃, br₂, ar₁]
  · rw [vrm₁₃, crm₁₁, urm₁₀, crm₉, qrm₈, crm₇, prm₆, zrm₅, zrm₄, srm₃, brm₂, arm₁]
  · rw [vo₁₃, co₁₁, uo₁₀, co₉, qo₈, co₇, po₆, zo₅, zo₄, so₃, bo₂, ao₁]

end Pre

section In

open Function Equiv Orbit CombMap PlanarSeparator PlanarSeparator.Map PlanarSeparator.MillerProg

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F} {P : Input} {W : ℕ}

open Classical in
set_option maxHeartbeats 1600000 in
/-- **Miller's separator in place**: from the compacted index arrays of the piece map
`psep M hσ hB` (numbering `cNe e n N`) at `CRb`, `CSb`, `CEb` above the work area
`[0, Wr]` (`Wr = Bz + 25 #N + 3 Σ_N ex + 14`, `encB' #N ≤ Bz`), `mbIn` saves `[0, Wr]` at `SVb`,
writes the frame image of `sepC` in place and runs `encProg ; msep`, within
`12 (Wr + 1) + 21 #N + 1060 + encT #N + msT #N (#Q + #Face)` steps. The output, read with the
memory above `Wr` as `0` (`mbCut Wr`), is `sepC M e n Bz N σ hσ hB ex = some R` in the output
form, `R` meets `SepOK`; the saved copy of `[0, Wr]` is at `SVb`, the memory above `Wr` off the
save area is kept, `r5040 = Wr`, `r5045 = Wr + 1`, the registers outside `mbU`, `4910 … 4916`,
`5030 … 5049` (but `5041`, `5046`), reals kept; output extended. -/
theorem mbIn_exec (e : ℕ → D) (n Bz : ℕ) {N : Finset D} {σ : Perm D}
    (hσ : Stable σ N) (hB : Stable (revPerm M) N) (ex : D → ℕ)
    (hP : (psep M hσ hB).IsPlane)
    (hl : ∀ d, (psep M hσ hB).vert ((psep M hσ hB).α d) ≠ (psep M hσ hB).vert d)
    (hm2 : 2 ≤ #N) (c : Config) (hc : WordsBounded W c) {SVb CRb CSb CEb : ℕ}
    (r12 : c.nreg 5012 = #N) (r21 : c.nreg 5021 = ∑ d ∈ N, ex d) (r41 : c.nreg 5041 = Bz)
    (r46 : c.nreg 5046 = SVb) (r09 : c.nreg 5009 = CRb) (r18 : c.nreg 5018 = CSb)
    (r19 : c.nreg 5019 = CEb)
    (hA : EncArr (psep M hσ hB) (cNe e n N) (fun x => ex x.1) c.nmem CRb CSb CEb)
    (hBz : encB' #N ≤ Bz)
    (lay : Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 14 < CRb ∧ CRb + #N ≤ SVb ∧
      Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 14 < CSb ∧ CSb + #N ≤ SVb ∧
      Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 14 < CEb ∧ CEb + #N ≤ SVb ∧
      SVb + (Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 15) + 1 ≤ W ∧ 25 ≤ W) :
    ∃ d' t, Exec P W mbIn c d' t ∧
      t ≤ 12 * (Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 15) + 21 * #N + 1060 + encT #N +
        msT #N (Fintype.card (SVert σ N) + Fintype.card (psep M hσ hB).Face) ∧
      ∃ R, sepC M e n Bz N σ hσ hB ex = some R ∧
        d'.nreg 641 = R.1.k ∧
        (∀ i < R.1.k, (mbCut (Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 14) d').nmem
          (d'.nreg 640 + i) = (psep M hσ hB).stCode (cNe e n N) (R.1.d i)) ∧
        (∀ G, G ∈ R.2 ↔ ((mbCut (Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 14) d').nmem
          (d'.nreg 642 + (psep M hσ hB).stFn (cNe e n N) G) ≠ d'.nreg 643 ↔ d'.nreg 644 = 1)) ∧
        SepOK (wR (encWt (psep M hσ hB) (fun x => ex x.1)))
          (6 * Nat.sqrt (Fintype.card (SVert σ N) + Fintype.card (psep M hσ hB).Face) + 4) R ∧
      (∀ a ≤ Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 14, d'.nmem (SVb + a) = c.nmem a) ∧
      (∀ a, Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 14 < a →
        ¬ (SVb ≤ a ∧ a < SVb + (Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 15)) →
        d'.nmem a = c.nmem a) ∧
      d'.nreg 5040 = Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 14 ∧
      d'.nreg 5045 = Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 15 ∧
      (∀ x, mbU x = false → (x < 4910 ∨ (4916 < x ∧ x < 5030) ∨ x = 5041 ∨ x = 5046 ∨
        5049 < x) → d'.nreg x = c.nreg x) ∧
      d'.rreg = c.rreg ∧ d'.rmem = c.rmem ∧ ∃ L, d'.output = c.output ++ L := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := lay
  set S := ∑ d ∈ N, ex d with hS
  set Wr := Bz + 25 * #N + 3 * S + 14 with hWr
  obtain ⟨c₁, t₁, e₁, ht₁, pCR, pCS, pCE, pz, psv, pmem, pU, p40, p45, pN, pr, prm, po⟩ :=
    mbPre_exec (P := P) c hc r12 r21 r41 r46 r09 r18 r19
      ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩
  have hw₁ := e₁.wb_right
  have hBz' : mbBz Bz #N = Bz := mbBz_eq hBz
  have hsum : ∑ x : SDart N, ex x.1 = S := by rw [hS]; exact Finset.sum_coe_sort N ex
  have hWreq : encWZ (mbBz Bz #N) #N (∑ x : SDart N, ex x.1 + #N) = Wr := by
    rw [hBz', hsum]; unfold encWZ; omega
  have hcd : ∀ d : SDart N, ((cNe e n N) d : ℕ) < #N := fun d => (cNe e n N d).2
  have hA₁ : EncArr (psep M hσ hB) (cNe e n N) (fun x => ex x.1) c₁.nmem Bz (Bz + 7 * #N)
      (Bz + 8 * #N) :=
    ⟨fun d => by rw [pCR _ (hcd d)]; exact hA.rev d, fun d => by rw [pCS _ (hcd d)]; exact hA.sig d,
      fun d => by rw [pCE _ (hcd d)]; exact hA.ex d⟩
  have hmem : ∀ a ≤ encWZ (mbBz Bz #N) #N (∑ x : SDart N, ex x.1 + #N),
      c₁.nmem a = (encInZ (psep M hσ hB) (cNe e n N) (fun x => ex x.1) (mbBz Bz #N)).nmem a := by
    rw [hWreq, hBz']
    exact encInZ_nmem_of (psep M hσ hB) (cNe e n N) (fun x => ex x.1) hA₁ pz
  have hreg : ∀ r, mbU r = true → c₁.nreg r =
      (encInZ (psep M hσ hB) (cNe e n N) (fun x => ex x.1) (mbBz Bz #N)).nreg r := fun r hr => by
    rw [pU r hr, hBz']; rfl
  obtain ⟨d', t₂, e₂, ht₂, R, hsep, -, h641, h640, hZ, hok, hN₂, hM₂, hr₂, hrm₂, L, ho₂⟩ :=
    sepC_insitu (M := M) (P := P) (W := W) e n Bz hσ hB ex hP hl hm2 c₁ hw₁
      (by rw [hWreq]; omega) hreg hmem
  rw [hWreq] at h640 hZ hM₂
  refine ⟨d', t₁ + t₂, .seq e₁ e₂, by omega, R, hsep, h641, h640, hZ, hok, fun a ha => ?_,
    fun a h1 h2 => ?_, ?_, ?_, fun x hx1 hx2 => ?_, by rw [hr₂, pr], by rw [hrm₂, prm],
    L, by rw [ho₂, po]⟩
  · rw [hM₂ _ (by omega), psv a ha]
  · rw [hM₂ a h1, pmem a h1 h2]
  · rw [hN₂ _ (by simp [mbU]), p40]
  · rw [hN₂ _ (by simp [mbU]), p45]
  · rw [hN₂ x hx1, pN x hx1 hx2]

end In

end BKMNW

end PlanarFlow
