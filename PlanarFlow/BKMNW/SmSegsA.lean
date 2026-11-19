module

public import PlanarFlow.BKMNW.SepSegs
public import PlanarFlow.BKMNW.NoEmit
public import PlanarFlow.BKMNW.SmSegsP

/-!
# `SegsOut` for the small separator: the program `smSegs`

After `sepSm` (the outputs of `SepPSpecX` at `Sb`, the children's records from `Xb = r6501`),
`smSegs` writes the parts of the separator from `Gb = Xb + 2 + zl + zr` (`r6502 := Gb`):
two compactions `lkProg` count the path's dart flags `F[i] = mem (Sb + m + i)` (`cP`, with the
least flagged index at `IX[0]`) and the hole flags `mem (Sb + 3m + j)` (`cH`); then
`mem Gb = s = [¬ (cP = 0 ∧ 0 < cH)]`, `mem (Gb + 1) = 0`, `mem (Gb + 2) = [0 < cP ∧ cH = 0]`,
`mem (Gb + 3) = IX[0]` (`smD_node_segs`: these are the parts of a node of `smD`).
Inputs: `3004 = d` (`m = mem d`, `k = mem (d + 1)`), `3120 = Sb` (saved before `sepSm`),
`6501 = Xb`; scratch `[Gb + 4, Gb + 4 + 2m + 2k)`; registers written `5970 … 5990`,
`6300 … 6309`, `6502`.

* `sgS`, `sgK` (branch-free, no products) and their values; `sg0`, `sg1`, `sg2`, **`smSegs`**,
  the block lemmas, **`smSegs_exec`** (`11 m + 11 k + 70` steps);
* `sepSmS := (3120 := r6500) ; sepSm ; smSegs`, **`wrOK_sepSm`** (`sepSm` writes registers only in
  `[4000, 7000)`, `decide +kernel`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.rwaSuggestion false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

/-- The number of parts: `0` iff no dart flagged and a hole met. -/
def sgS (cP cH : ℕ) : ℕ := 1 - (1 - (2 - ((1 - cP) + (1 - (1 - cH)))))

/-- The darts of the part: `1` iff a dart flagged and no hole met. -/
def sgK (cP cH : ℕ) : ℕ := 1 - (2 - ((1 - (1 - cP)) + (1 - cH)))

lemma sgS_eq (cP cH : ℕ) : sgS cP cH = if cP = 0 ∧ 0 < cH then 0 else 1 := by
  unfold sgS; split_ifs <;> omega

lemma sgK_eq (cP cH : ℕ) : sgK cP cH = if 0 < cP ∧ cH = 0 then 1 else 0 := by
  unfold sgK; split_ifs <;> omega

/-- The bases. -/
def sg0 : Stmt := block [.copyN 5970 6501, .loadN 5971 5970, .constN 5972 1,
  .addN 5973 5970 5972, .loadN 5974 5973, .addN 5975 5970 5971, .addN 5975 5975 5974,
  .constN 5972 2, .addN 5975 5975 5972, .copyN 6502 5975, .loadN 5976 3004, .constN 5972 1,
  .addN 5977 3004 5972, .loadN 5978 5977, .addN 5979 3120 5976, .addN 5980 5979 5976,
  .addN 5980 5980 5976, .constN 5972 4, .addN 5981 5975 5972, .addN 5982 5981 5976,
  .addN 5983 5982 5976, .addN 5984 5983 5978, .copyN 6300 5976, .copyN 6301 5979,
  .copyN 6302 5981, .copyN 6303 5982]

/-- Keep `cP` and `IX[0]`; the registers of the second compaction. -/
def sg1 : Stmt := block [.copyN 5985 6306, .loadN 5986 5982, .copyN 6300 5978,
  .copyN 6301 5980, .copyN 6302 5983, .copyN 6303 5984]

/-- The four words of `SegsOut`. -/
def sg2 : Stmt := block [.constN 5972 1, .constN 5990 2, .subN 5987 5972 5985,
  .subN 5988 5972 6306, .subN 5989 5972 5988, .addN 5989 5987 5989, .subN 5989 5990 5989,
  .subN 5989 5972 5989, .subN 5989 5972 5989, .storeN 5975 5989, .constN 5987 0,
  .addN 5973 5975 5972, .storeN 5973 5987, .subN 5987 5972 5985, .subN 5987 5972 5987,
  .addN 5987 5987 5988, .subN 5987 5990 5987, .subN 5987 5972 5987, .addN 5973 5973 5972,
  .storeN 5973 5987, .addN 5973 5973 5972, .storeN 5973 5986]

/-- **The parts of the small separator.** -/
def smSegs : Stmt := .seq sg0 (.seq lkProg (.seq sg1 (.seq lkProg sg2)))

/-- **The small separator with its parts.** -/
def sepSmS : Stmt := .seq (block [.copyN 3120 6500]) (.seq sepSm smSegs)

/-- The room of `sepSmS`. -/
def smRS (n m k : ℕ) : ℕ := smR n m k + 2 * m + 2 * k + 16

/-- `sepSm` writes natural registers only in `[4000, 7000)`, no reals. -/
theorem wrOK_sepSm : Stmt.wrOK (fun x => decide (4000 ≤ x ∧ x < 7000)) sepSm = true := by
  decide +kernel

lemma upd4_other {mem : ℕ → ℕ} {G a : ℕ} (x0 x1 x2 x3 : ℕ) (h : a < G ∨ G + 3 < a) :
    upd (upd (upd (upd mem G x0) (G + 1) x1) (G + 2) x2) (G + 3) x3 a = mem a := by
  simp (disch := omega) only [upd_other]

lemma upd4_0 (mem : ℕ → ℕ) (G x0 x1 x2 x3 : ℕ) :
    upd (upd (upd (upd mem G x0) (G + 1) x1) (G + 2) x2) (G + 3) x3 G = x0 := by
  simp (disch := omega) only [upd_other, upd_same]

lemma upd4_1 (mem : ℕ → ℕ) (G x0 x1 x2 x3 : ℕ) :
    upd (upd (upd (upd mem G x0) (G + 1) x1) (G + 2) x2) (G + 3) x3 (G + 1) = x1 := by
  simp (disch := omega) only [upd_other, upd_same]

lemma upd4_2 (mem : ℕ → ℕ) (G x0 x1 x2 x3 : ℕ) :
    upd (upd (upd (upd mem G x0) (G + 1) x1) (G + 2) x2) (G + 3) x3 (G + 2) = x2 := by
  simp (disch := omega) only [upd_other, upd_same]

lemma upd4_3 (mem : ℕ → ℕ) (G x0 x1 x2 x3 : ℕ) :
    upd (upd (upd (upd mem G x0) (G + 1) x1) (G + 2) x2) (G + 3) x3 (G + 3) = x3 := by
  simp only [upd_same]

section Exec

variable {I : Input} {W : ℕ}

theorem sg0_exec (c : Config) (hc : WordsBounded W c) {Xb d Sb zl zr m k : ℕ}
    (r1 : c.nreg 6501 = Xb) (r2 : c.nreg 3004 = d) (r3 : c.nreg 3120 = Sb)
    (h1 : c.nmem Xb = zl) (h2 : c.nmem (Xb + 1) = zr) (h3 : c.nmem d = m)
    (h4 : c.nmem (d + 1) = k) (w : Xb + 2 + zl + zr + 4 + 2 * m + k ≤ W) (w' : d + 1 ≤ W)
    (w'' : Sb + 3 * m ≤ W) (w2 : 4 ≤ W) :
    ∃ c' t, Exec I W sg0 c c' t ∧ t = 26 ∧ c'.nreg 6502 = Xb + 2 + zl + zr ∧
      c'.nreg 5975 = Xb + 2 + zl + zr ∧ c'.nreg 5976 = m ∧ c'.nreg 5978 = k ∧
      c'.nreg 5979 = Sb + m ∧ c'.nreg 5980 = Sb + m + m + m ∧
      c'.nreg 5981 = Xb + 2 + zl + zr + 4 ∧ c'.nreg 5982 = Xb + 2 + zl + zr + 4 + m ∧
      c'.nreg 5983 = Xb + 2 + zl + zr + 4 + m + m ∧
      c'.nreg 5984 = Xb + 2 + zl + zr + 4 + m + m + k ∧
      c'.nreg 6300 = m ∧ c'.nreg 6301 = Sb + m ∧ c'.nreg 6302 = Xb + 2 + zl + zr + 4 ∧
      c'.nreg 6303 = Xb + 2 + zl + zr + 4 + m ∧
      (∀ x, (x < 5970 ∨ 5990 < x) → (x < 6300 ∨ 6309 < x) → x ≠ 6502 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sg0
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r1, r2, r3, h1, h2, h3, h4, show Xb + 1 = 1 + Xb by omega, show d + 1 = 1 + d by omega] at h2 h4 ⊢; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x a1 a2 a3 => ?_, rfl,
    rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r1, r2, r3, h1, h3,
      show Xb + 1 = 1 + Xb by omega, show d + 1 = 1 + d by omega] at h2 h4 ⊢)
    try (simp only [h2, h4])
    try omega

theorem sg1_exec (c : Config) (hc : WordsBounded W c) {IXb k Hb CI2 IX2 : ℕ}
    (r82 : c.nreg 5982 = IXb) (r78 : c.nreg 5978 = k) (r80 : c.nreg 5980 = Hb)
    (r83 : c.nreg 5983 = CI2) (r84 : c.nreg 5984 = IX2) :
    ∃ c' t, Exec I W sg1 c c' t ∧ t = 6 ∧ c'.nreg 5985 = c.nreg 6306 ∧
      c'.nreg 5986 = c.nmem IXb ∧ c'.nreg 6300 = k ∧ c'.nreg 6301 = Hb ∧ c'.nreg 6302 = CI2 ∧
      c'.nreg 6303 = IX2 ∧
      (∀ x, x ≠ 5985 → x ≠ 5986 → (x < 6300 ∨ 6303 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sg1
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x a1 a2 a3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r82, r78, r80, r83, r84])
    try omega

theorem sg2_exec (c : Config) (hc : WordsBounded W c) {Gb cP cH ix : ℕ}
    (r75 : c.nreg 5975 = Gb) (r85 : c.nreg 5985 = cP) (r06 : c.nreg 6306 = cH)
    (r86 : c.nreg 5986 = ix) (w : Gb + 3 ≤ W) (w2 : 2 ≤ W) :
    ∃ c' t, Exec I W sg2 c c' t ∧ t = 22 ∧
      c'.nmem = upd (upd (upd (upd c.nmem Gb (sgS cP cH)) (Gb + 1) 0) (Gb + 2) (sgK cP cH))
        (Gb + 3) ix ∧
      (∀ x, (x < 5972 ∨ 5990 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have bP : cP ≤ W := r85 ▸ hc.1 5985
  have bH : cH ≤ W := r06 ▸ hc.1 6306
  unfold sg2
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r75, r85, r06, r86]; omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp
    simp (disch := omega) only [upd_other, upd_same, r75, r85, r06, r86]
    unfold sgS sgK
    congr 1
  · config_simp
    simp (disch := omega) only [upd_other, upd_same]

set_option maxHeartbeats 1000000 in
/-- **The parts of the small separator on the machine** (see the module docstring). -/
theorem smSegs_exec (c : Config) (hc : WordsBounded W c) {Xb d Sb zl zr m k : ℕ}
    (r1 : c.nreg 6501 = Xb) (r2 : c.nreg 3004 = d) (r3 : c.nreg 3120 = Sb)
    (h1 : c.nmem Xb = zl) (h2 : c.nmem (Xb + 1) = zr) (h3 : c.nmem d = m)
    (h4 : c.nmem (d + 1) = k) (lay : Sb + 3 * m + k ≤ Xb + 2 + zl + zr) (hd : d + 1 ≤ Sb)
    (w : Xb + 2 + zl + zr + 4 + 2 * m + 2 * k + 10 ≤ W) :
    ∃ c' t, Exec I W smSegs c c' t ∧ t ≤ 11 * m + 11 * k + 70 ∧
      c'.nreg 6502 = Xb + 2 + zl + zr ∧
      c'.nmem (Xb + 2 + zl + zr) = sgS (cnt (fun j => c.nmem (Sb + m + j)) m)
        (cnt (fun j => c.nmem (Sb + 3 * m + j)) k) ∧
      c'.nmem (Xb + 2 + zl + zr + 1) = 0 ∧
      c'.nmem (Xb + 2 + zl + zr + 2) = sgK (cnt (fun j => c.nmem (Sb + m + j)) m)
        (cnt (fun j => c.nmem (Sb + 3 * m + j)) k) ∧
      (∀ i < m, 0 < c.nmem (Sb + m + i) → cnt (fun j => c.nmem (Sb + m + j)) i = 0 →
        c'.nmem (Xb + 2 + zl + zr + 3) = i) ∧
      (∀ a, ¬ (Xb + 2 + zl + zr ≤ a ∧ a < Xb + 2 + zl + zr + 4 + 2 * m + 2 * k) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5970 ∨ 5990 < x) → (x < 6300 ∨ 6309 < x) → x ≠ 6502 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a502, a75, a76, a78, a79, a80, a81, a82, a83, a84, a300, a301, a302,
    a303, f₁, m₁, rr₁, rm₁, o₁⟩ := sg0_exec (I := I) c hc r1 r2 r3 h1 h2 h3 h4
      (by clear * - w; omega) (by clear * - w lay hd; omega) (by clear * - w lay; omega)
      (by clear * - w; omega)
  obtain ⟨c₂, t₂, e₂, ht₂, cP2, ix2, m₂, f₂, rr₂, rm₂, o₂⟩ := lkProg_exec (P := I) c₁ e₁.wb_right
    a300 a301 a302 a303 (by clear * - lay; omega) (by clear * - lay; omega)
    (by clear * - w; omega) (by clear * - w; omega)
  have q2 : ∀ x, (x < 6304 ∨ 6309 < x) → c₂.nreg x = c₁.nreg x := f₂
  obtain ⟨c₃, t₃, e₃, ht₃, b85, b86, b300, b301, b302, b303, f₃, m₃, rr₃, rm₃, o₃⟩ :=
    sg1_exec (I := I) c₂ e₂.wb_right ((q2 5982 (by decide)).trans a82)
      ((q2 5978 (by decide)).trans a78) ((q2 5980 (by decide)).trans a80)
      ((q2 5983 (by decide)).trans a83) ((q2 5984 (by decide)).trans a84)
  obtain ⟨c₄, t₄, e₄, ht₄, cH4, -, m₄, f₄, rr₄, rm₄, o₄⟩ := lkProg_exec (P := I) c₃ e₃.wb_right
    b300 b301 b302 b303 (by clear * - lay; omega) (by clear * - lay; omega)
    (by clear * - w; omega) (by clear * - w; omega)
  have g75 : c₄.nreg 5975 = Xb + 2 + zl + zr := by
    rw [f₄ 5975 (by decide), f₃ 5975 (by decide) (by decide) (by decide), q2 5975 (by decide)]
    exact a75
  have g85 : c₄.nreg 5985 = c₂.nreg 6306 := by rw [f₄ 5985 (by decide)]; exact b85
  have g86 : c₄.nreg 5986 = c₂.nmem (Xb + 2 + zl + zr + 4 + m) := by
    rw [f₄ 5986 (by decide)]; exact b86
  obtain ⟨c₅, t₅, e₅, ht₅, m₅, f₅, rr₅, rm₅, o₅⟩ := sg2_exec (I := I) c₄ e₄.wb_right g75 g85 cH4
    g86 (by clear * - w; omega) (by clear * - w; omega)
  -- the memory
  have mc1 : c₁.nmem = c.nmem := m₁
  have mlow : ∀ a, a < Xb + 2 + zl + zr → c₃.nmem a = c.nmem a := fun a ha => by
    rw [m₃, m₂ a (by clear * - ha; omega), mc1]
  have hcP : cnt (fun j => c₁.nmem (Sb + m + j)) m = cnt (fun j => c.nmem (Sb + m + j)) m := by
    rw [mc1]
  have hcH : cnt (fun j => c₃.nmem (Sb + m + m + m + j)) k =
      cnt (fun j => c.nmem (Sb + 3 * m + j)) k :=
    cnt_congr fun j hj => by
      rw [show Sb + m + m + m + j = Sb + 3 * m + j by omega, mlow _ (by clear * - hj lay; omega)]
  have m54 : ∀ a, (a < Xb + 2 + zl + zr ∨ Xb + 2 + zl + zr + 3 < a) →
      c₅.nmem a = c₄.nmem a := fun a ha => by
    rw [m₅]; exact upd4_other _ _ _ _ ha
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_, ?_, ?_, ?_, ?_, fun i hi hp h0 => ?_,
    fun a ha => ?_, fun x a1 a2 a3 => ?_, ?_, ?_, ?_⟩
  · clear * - ht₁ ht₂ ht₃ ht₄ ht₅
    omega
  · rw [f₅ 6502 (by decide), f₄ 6502 (by decide), f₃ 6502 (by decide) (by decide) (by decide),
      q2 6502 (by decide)]
    exact a502
  · rw [m₅, upd4_0, cP2, hcP, hcH]
  · rw [m₅, upd4_1]
  · rw [m₅, upd4_2, cP2, hcP, hcH]
  · have hp1 : 0 < c₁.nmem (Sb + m + i) := by rw [mc1]; exact hp
    have := (ix2 i hi hp1).2
    rw [show cnt (fun j => c₁.nmem (Sb + m + j)) i = 0 by rw [mc1]; exact h0] at this
    rw [m₅, upd4_3]
    rw [show Xb + 2 + zl + zr + 4 + m + 0 = Xb + 2 + zl + zr + 4 + m by omega] at this
    exact this
  · rw [m54 a (by clear * - ha; omega), m₄ a (by clear * - ha; omega), m₃,
      m₂ a (by clear * - ha; omega), mc1]
  · rw [f₅ x (by clear * - a1; omega), f₄ x (by clear * - a2; omega),
      f₃ x (by clear * - a1; omega) (by clear * - a1; omega) (by clear * - a2; omega),
      q2 x (by clear * - a2; omega), f₁ x a1 a2 a3]
  · rw [rr₅, rr₄, rr₃, rr₂, rr₁]
  · rw [rm₅, rm₄, rm₃, rm₂, rm₁]
  · rw [o₅, o₄, o₃, o₂, o₁]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
