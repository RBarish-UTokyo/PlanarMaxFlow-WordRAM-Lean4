module

public import PlanarFlow.BKMNW.NegInPlace

/-!
# One in-place call of the machine's negative-length shortest paths

**`negCall`** `= ncPre ; lgS 7330 7331 negFix ; ncPost` runs `negFix` inside the memory of a
larger computation (the max-flow driver) whose memory up to a bound `Wz ≥ rtW` holds the root
image of the call (`rootMemP`, the root frame of `negFix` at `rtHb + 5`, zero elsewhere) and whose
data lives above `Wz`:

* `ncPre`: save the driver registers `3000 … 3012` to `7300 … 7312` (`cpRegs ncSvL`), zero the
  registers `< 3200` (`mbZeroRegs`), set `r3001 = 1`, `r3002 = Hb = r7320`, `r3003 = h = r7321`
  (the root registers of `negFix`), the log pointer `r7330 = p = r7324` and `r7331 = 1`;
* the logged run `lgS 7330 7331 negFix` (`negFix_lgRun`);
* `ncPost`: copy the root frame `[Hb + 5, h)` to `[Ob, Ob + F)` (`Ob = r7322`, `cpArr`), clear the
  logged cells (`lgClr`), zero the root image `[Hb + 2, h)` (`mzFill`), restore `3000 … 3012`.

**`negCall_exec`**: within **`9 · negT C C₀ n + 12 · F + 3270`** steps (`F = fsz m k` the root
frame's size, `≤ 10 n + 6`), the memory up to `Wz` is **zero again**, the copy at `Ob` holds the
outcome `negMach g M I ℓ` (`Res … Ob (Ob + F)`), the memory above `Wz` outside the copy and the
log area `[p, p + negT)` is kept, the registers `3000 … 3012` and every register outside the
scratch `ncScr` (`< 3200`, `4910 … 4916`, `5030 … 5036`, `7300 … 7340`) are kept, reals and output
kept.

So a subroutine whose precondition is "memory up to `Wz` zero but the root image" can be called
repeatedly from data laid out above `Wz` (the max-flow frames) at a cost `O(negsssp-cost)`.
Writing the root image from a max-flow frame is not done here.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP
  NegSSSP.Driver NegSSSP.Frame CombMap

/-! ### The programs -/

/-- Save the driver registers `3000 … 3012` to `7300 … 7312`. -/
def ncSvL : List (ℕ × ℕ) := (List.range 13).map fun i => (7300 + i, 3000 + i)

/-- Restore the driver registers. -/
def ncRsL : List (ℕ × ℕ) := (List.range 13).map fun i => (3000 + i, 7300 + i)

/-- The root registers of `negFix` and the log registers. -/
def ncSet : Stmt :=
  block [.constN 3001 1, .copyN 3002 7320, .copyN 3003 7321, .copyN 7330 7324, .constN 7331 1]

/-- **Before the run**: save, zero the registers `< 3200`, set. -/
def ncPre : Stmt := .seq (cpRegs ncSvL) (.seq (mbZeroRegs (List.range nfR)) ncSet)

/-- The arguments of the copy of the root frame: `4910 = h - (Hb + 5)`, `4911 = Hb + 5`,
`4912 = Ob`. -/
def ncCpSet : Stmt :=
  block [.constN 7340 5, .addN 4911 7320 7340, .subN 4910 7321 4911, .copyN 4912 7322]

/-- The arguments of the clearing of the log: `2924 = p`, `2925 = LP`, `2926 = 1`. -/
def ncClSet : Stmt := block [.copyN 2924 7324, .copyN 2925 7330, .constN 2926 1]

/-- The arguments of the zeroing of the root image: `5031 = Hb + 2`, `5030 = h - (Hb + 2)`. -/
def ncZSet : Stmt := block [.constN 7340 2, .addN 5031 7320 7340, .subN 5030 7321 5031]

/-- **After the run**: copy the frame out, clear the log, zero the root image, restore. -/
def ncPost : Stmt :=
  .seq (.seq ncCpSet cpArr) (.seq (.seq ncClSet lgClr) (.seq (.seq ncZSet mzFill) (cpRegs ncRsL)))

/-- **One in-place call of `negFix`.** -/
def negCall : Stmt := .seq ncPre (.seq (lgS 7330 7331 negFix) ncPost)

/-- The scratch registers of `negCall`. -/
def ncScr (r : ℕ) : Prop :=
  r < 3200 ∨ (4910 ≤ r ∧ r ≤ 4916) ∨ (5030 ≤ r ∧ r ≤ 5036) ∨ (7300 ≤ r ∧ r ≤ 7340)

theorem ncSvL_ok : cpOK ncSvL = true ∧ cpSrc ncSvL = true := by decide
theorem ncRsL_ok : cpOK ncRsL = true ∧ cpSrc ncRsL = true := by decide

theorem mem_ncSvL {q : ℕ × ℕ} : q ∈ ncSvL ↔ ∃ i < 13, q = (7300 + i, 3000 + i) := by
  simp only [ncSvL, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem mem_ncRsL {q : ℕ × ℕ} : q ∈ ncRsL ↔ ∃ i < 13, q = (3000 + i, 7300 + i) := by
  simp only [ncRsL, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem ncSvL_tgt {r : ℕ} : r ∈ ncSvL.map (·.1) ↔ 7300 ≤ r ∧ r < 7313 := by
  simp only [List.mem_map, mem_ncSvL]
  constructor
  · rintro ⟨q, ⟨i, hi, rfl⟩, rfl⟩; simp only; omega
  · rintro ⟨h1, h2⟩; exact ⟨(r, r - 4300), ⟨r - 7300, by omega, by ext <;> simp <;> omega⟩, rfl⟩

theorem ncRsL_tgt {r : ℕ} : r ∈ ncRsL.map (·.1) ↔ 3000 ≤ r ∧ r < 3013 := by
  simp only [List.mem_map, mem_ncRsL]
  constructor
  · rintro ⟨q, ⟨i, hi, rfl⟩, rfl⟩; simp only; omega
  · rintro ⟨h1, h2⟩; exact ⟨(r, r + 4300), ⟨r - 3000, by omega, by ext <;> simp <;> omega⟩, rfl⟩

/-! ### The blocks -/

section Blocks

variable {P : Input} {W : ℕ}

theorem ncSet_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' t, Exec P W ncSet c c' t ∧ t = 5 ∧ c'.nreg 3001 = 1 ∧ c'.nreg 3002 = c.nreg 7320 ∧
      c'.nreg 3003 = c.nreg 7321 ∧ c'.nreg 7330 = c.nreg 7324 ∧ c'.nreg 7331 = 1 ∧
      (∀ r, r ≠ 3001 → r ≠ 3002 → r ≠ 3003 → r ≠ 7330 → r ≠ 7331 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ncSet
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

theorem ncCpSet_exec (c : Config) (hc : WordsBounded W c) {Hb h : ℕ} (r20 : c.nreg 7320 = Hb)
    (r21 : c.nreg 7321 = h) (hW : Hb + 5 ≤ W) :
    ∃ c' t, Exec P W ncCpSet c c' t ∧ t = 4 ∧ c'.nreg 4911 = Hb + 5 ∧ c'.nreg 4910 = h - (Hb + 5) ∧
      c'.nreg 4912 = c.nreg 7322 ∧
      (∀ r, r ≠ 7340 → r ≠ 4910 → r ≠ 4911 → r ≠ 4912 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ncCpSet
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r21]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r20, r21])
  simp only [upd_apply]; split_ifs <;> omega

theorem ncClSet_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' t, Exec P W ncClSet c c' t ∧ t = 3 ∧ c'.nreg 2924 = c.nreg 7324 ∧
      c'.nreg 2925 = c.nreg 7330 ∧ c'.nreg 2926 = 1 ∧
      (∀ r, r ≠ 2924 → r ≠ 2925 → r ≠ 2926 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ncClSet
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

theorem ncZSet_exec (c : Config) (hc : WordsBounded W c) {Hb h : ℕ} (r20 : c.nreg 7320 = Hb)
    (r21 : c.nreg 7321 = h) (hW : Hb + 2 ≤ W) :
    ∃ c' t, Exec P W ncZSet c c' t ∧ t = 3 ∧ c'.nreg 5031 = Hb + 2 ∧ c'.nreg 5030 = h - (Hb + 2) ∧
      (∀ r, r ≠ 7340 → r ≠ 5030 → r ≠ 5031 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ncZSet
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r21]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r20, r21])
  simp only [upd_apply]; split_ifs <;> omega

/-- **After the run** (see the module docstring): copy the frame `[Hb + 5, h)` to `Ob`, clear the
`j` logged cells, zero `[Hb + 2, h)`, restore `3000 … 3012` from `7300 … 7312`. -/
theorem ncPost_exec (c : Config) (hc : WordsBounded W c) {Hb h Ob p j Ws : ℕ}
    (r20 : c.nreg 7320 = Hb) (r21 : c.nreg 7321 = h) (r22 : c.nreg 7322 = Ob)
    (r24 : c.nreg 7324 = p) (r30 : c.nreg 7330 = p + j) (hHh : Hb + 5 ≤ h) (hhW : h ≤ Ws)
    (hWO : Ws < Ob) (hOp : Ob + (h - (Hb + 5)) ≤ p) (hlog : ∀ i < j, c.nmem (p + i) ≤ Ws) :
    ∃ c' t, Exec P W ncPost c c' t ∧ t ≤ 12 * (h - (Hb + 5)) + 6 * j + 52 ∧
      (∀ a ≤ Ws, ¬ (Hb + 2 ≤ a ∧ a < h) → (∀ i < j, c.nmem (p + i) ≠ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ a, (∃ i < j, c.nmem (p + i) = a) ∨ (Hb + 2 ≤ a ∧ a < h) → c'.nmem a = 0) ∧
      (∀ i < h - (Hb + 5), c'.nmem (Ob + i) = c.nmem (Hb + 5 + i)) ∧
      (∀ a, Ws < a → (a < Ob ∨ Ob + (h - (Hb + 5)) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ i < 13, c'.nreg (3000 + i) = c.nreg (7300 + i)) ∧
      (∀ r, ¬ ncScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hpW : p + j ≤ W := r30 ▸ WordsBounded.nreg hc 7330
  obtain ⟨c₁, t₁, e₁, ht₁, a11, a10, a12, ak, am, ar, arm, ao⟩ :=
    ncCpSet_exec (P := P) c hc r20 r21 (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, bcp, bkeep, bregs, br, brm, bo⟩ :=
    cpArr_exec (P := P) c₁ e₁.wb_right a10 a11 (a12.trans r22)
      ⟨Or.inl (by omega), by omega, by omega, by omega⟩
  have k12 : ∀ r, r ≠ 7340 → (r < 4910 ∨ 4916 < r) → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [bregs r (by omega), ak r h1 (by omega) (by omega) (by omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, c24, c25, c26, ck3, cm, cr, crm, co⟩ :=
    ncClSet_exec (P := P) c₂ e₂.wb_right (by omega)
  have hl3 : ∀ i < j, c₃.nmem (p + i) = c.nmem (p + i) := fun i hi => by
    rw [cm, bkeep _ (Or.inr (by omega)), am]
  obtain ⟨c₄, t₄, e₄, ht₄, dzero, dkeep, dregs, dr, drm, do'⟩ :=
    lgClr_exec (P := P) c₃ e₃.wb_right (p := p) (j := j) (Ws := Ws)
      (by rw [c24, k12 _ (by omega) (by omega), r24])
      (by rw [c25, k12 _ (by omega) (by omega), r30]) c26
      (fun i hi => by rw [hl3 i hi]; exact hlog i hi) (by omega)
  have k14 : ∀ r, 3200 ≤ r → r ≠ 7340 → (r < 4910 ∨ 4916 < r) → c₄.nreg r = c.nreg r :=
    fun r h0 h1 h2 => by
      rw [dregs r (by omega) (by omega), ck3 r (by omega) (by omega) (by omega), k12 r h1 h2]
  obtain ⟨c₅, t₅, e₅, ht₅, e31, e30, ek, em, er, erm, eo⟩ :=
    ncZSet_exec (P := P) c₄ e₄.wb_right (by rw [k14 _ (by omega) (by omega) (by omega), r20])
      (by rw [k14 _ (by omega) (by omega) (by omega), r21]) (by omega)
  obtain ⟨c₆, t₆, e₆, ht₆, fzero, fkeep, fregs, fr, frm, fo⟩ :=
    mzFill_exec (P := P) c₅ e₅.wb_right e30 e31 (by omega) (by omega)
  obtain ⟨c₇, e₇, gcp, gkeep, gm, gr, grm, go⟩ :=
    cpRegs_exec (P := P) ncRsL ncRsL_ok.1 ncRsL_ok.2 c₆ e₆.wb_right
  have k16 : ∀ r, 3200 ≤ r → r ≠ 7340 → (r < 4910 ∨ 4916 < r) → (r < 5030 ∨ 5035 < r) →
      c₆.nreg r = c.nreg r := fun r h0 h1 h2 h3 => by
    rw [fregs r (by omega), ek r h1 (by omega) (by omega), k14 r h0 h1 h2]
  -- the memory
  have m64 : ∀ a, ¬ (Hb + 2 ≤ a ∧ a < h) → c₆.nmem a = c₄.nmem a := fun a ha => by
    rw [fkeep a (by omega), em]
  have m42 : ∀ a, (∀ i < j, c.nmem (p + i) ≠ a) → c₄.nmem a = c₂.nmem a := fun a ha => by
    rw [dkeep a (fun i hi => by rw [hl3 i hi]; exact ha i hi), cm]
  have notlog : ∀ a, Ws < a → ∀ i < j, c.nmem (p + i) ≠ a := fun a ha i hi e => by
    have := hlog i hi; omega
  have ln : t₄ ≤ 6 * j + 5 := ht₄
  refine ⟨c₇, _, (e₁.seq e₂).seq ((e₃.seq e₄).seq ((e₅.seq e₆).seq e₇)), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ncRsL, List.length_map, List.length_range]
    have : h - (Hb + 2) = h - (Hb + 5) + 3 := by omega
    omega
  · intro a ha hn hl
    rw [gm, m64 a hn, m42 a hl, bkeep a (Or.inl (by omega)), am]
  · intro a ha
    rw [gm]
    by_cases hr : Hb + 2 ≤ a ∧ a < h
    · have := fzero (a - (Hb + 2)) (by omega)
      rwa [show Hb + 2 + (a - (Hb + 2)) = a by omega] at this
    · rw [m64 a hr]
      rcases ha with ⟨i, hi, hia⟩ | hr'
      · exact dzero a ⟨i, hi, by rw [hl3 i hi]; exact hia⟩
      · exact absurd hr' hr
  · intro i hi
    rw [gm, m64 _ (by omega), m42 _ (notlog _ (by omega)), bcp i hi, am]
  · intro a ha hn
    rw [gm, m64 _ (by omega), m42 _ (notlog _ ha), bkeep a hn, am]
  · intro i hi
    rw [gcp (3000 + i, 7300 + i) (mem_ncRsL.2 ⟨i, hi, rfl⟩)]
    exact k16 _ (by omega) (by omega) (by omega) (by omega)
  · intro r hr
    unfold ncScr at hr
    rw [gkeep r (fun h' => by rw [ncRsL_tgt] at h'; omega)]
    exact k16 r (by omega) (by omega) (by omega) (by omega)
  · rw [gr, fr, er, dr, cr, br, ar]
  · rw [grm, frm, erm, drm, crm, brm, arm]
  · rw [go, fo, eo, do', co, bo, ao]

end Blocks

section Call

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **One in-place call of the machine's negative-length shortest paths** (see the module
docstring). -/
theorem negCall_exec (C C₀ : ℕ) (hC : 200000 ≤ C) (g : GIds D F) {M : CombMap D V F}
    {ℓ : D → ℤ} (hpre : NegPre M ℓ) (I P' : Input) {W Wz Ob p : ℕ} (d : Config)
    (hd : WordsBounded W d)
    (r20 : d.nreg 7320 = rtHb (Fintype.card D) (rtL M ℓ) g.G)
    (r21 : d.nreg 7321 = rtH (Fintype.card D) (rtL M ℓ) g.G (repsN M.dual g.gd).card
      (ck M.dual (repsN M.dual g.gd)))
    (r22 : d.nreg 7322 = Ob) (r24 : d.nreg 7324 = p)
    (hm : ∀ a ≤ Wz, d.nmem a = rootMemP g M ℓ (repsN M.dual g.gd) a)
    (hWz : rtW (Fintype.card D) (rtL M ℓ) g.G ≤ Wz) (hOb : Wz < Ob)
    (hOp : Ob + Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) ≤ p)
    (hpW : p + negT C C₀ (Fintype.card D) ≤ W) :
    ∃ d' t, Exec P' W negCall d d' t ∧
      t ≤ 9 * negT C C₀ (Fintype.card D) +
        12 * Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) + 3270 ∧
      (∀ a ≤ Wz, d'.nmem a = 0) ∧
      Res g M.dual (rtL M ℓ) (repsN M.dual g.gd) (negMach g M I ℓ) Ob
        (Ob + Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd))) d' ∧
      (∀ a, Wz < a →
        (a < Ob ∨ Ob + Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) ≤ a) →
        (a < p ∨ p + negT C C₀ (Fintype.card D) ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, 3000 ≤ r → r ≤ 3012 → d'.nreg r = d.nreg r) ∧
      (∀ r, ¬ ncScr r → d'.nreg r = d.nreg r) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  have hhF : rtH (Fintype.card D) (rtL M ℓ) g.G (repsN M.dual g.gd).card
      (ck M.dual (repsN M.dual g.gd)) = rtHb (Fintype.card D) (rtL M ℓ) g.G + 5 +
      Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) := rfl
  have hhW : rtH (Fintype.card D) (rtL M ℓ) g.G (repsN M.dual g.gd).card
      (ck M.dual (repsN M.dual g.gd)) ≤ rtW (Fintype.card D) (rtL M ℓ) g.G :=
    rtH_le_rtW (card_le_n _) (ck_le_n M.dual _)
  have hT : 4610 ≤ negT C C₀ (Fintype.card D) := by unfold negT; omega
  -- before the run
  obtain ⟨c₁, e₁, acp, akeep, am, ar, arm, ao⟩ :=
    cpRegs_exec (P := P') ncSvL ncSvL_ok.1 ncSvL_ok.2 d hd
  have e₂ := mbZeroRegs_exec (P := P') (List.range nfR) c₁ e₁.wb_right
  set c₂ : Config := { c₁ with nreg := fun r => if r ∈ List.range nfR then 0 else c₁.nreg r }
    with hc₂
  have k2 : ∀ r, nfR ≤ r → c₂.nreg r = c₁.nreg r := fun r hr => by
    simp only [hc₂, List.mem_range]; exact ite_eq_right_iff.2 fun h' => by omega
  have k1 : ∀ r, (r < 7300 ∨ 7313 ≤ r) → c₁.nreg r = d.nreg r := fun r hr =>
    akeep r (fun h' => by rw [ncSvL_tgt] at h'; omega)
  obtain ⟨c₃, t₃, e₃, ht₃, s01, s02, s03, s30, s31, skeep, sm, sr, srm, so⟩ :=
    ncSet_exec (P := P') c₂ e₂.wb_right (by omega)
  have k3 : ∀ r, nfR ≤ r → r ≠ 7330 → r ≠ 7331 → (r < 7300 ∨ 7313 ≤ r) →
      c₃.nreg r = d.nreg r := fun r h0 h1 h2 h3 => by
    rw [skeep r (by simp only [nfR] at h0; omega) (by simp only [nfR] at h0; omega)
      (by simp only [nfR] at h0; omega) h1 h2, k2 r h0, k1 r h3]
  have q30 : c₃.nreg 7330 = p := by
    rw [s30, k2 _ (by simp [nfR]), k1 _ (by omega), r24]
  have hA : ∀ r, r < nfR → c₃.nreg r = (rootCfgP g M ℓ (repsN M.dual g.gd)).nreg r := by
    intro r hr
    rcases (show r = 3001 ∨ r = 3002 ∨ r = 3003 ∨ (r ≠ 3001 ∧ r ≠ 3002 ∧ r ≠ 3003) by omega)
      with rfl | rfl | rfl | ⟨h1, h2, h3⟩
    · rw [s01]; simp [rootCfgP]
    · rw [s02, k2 _ (by simp [nfR]), k1 _ (by omega), r20]; simp [rootCfgP]
    · rw [s03, k2 _ (by simp [nfR]), k1 _ (by omega), r21]; simp [rootCfgP]
    · rw [skeep r h1 h2 h3 (by simp only [nfR] at hr; omega) (by simp only [nfR] at hr; omega)]
      simp only [hc₂, List.mem_range, hr, ite_true]
      simp [rootCfgP, h1, h2, h3]
  have hm3 : ∀ a ≤ rtW (Fintype.card D) (rtL M ℓ) g.G,
      c₃.nmem a = rootMemP g M ℓ (repsN M.dual g.gd) a := fun a ha => by
    rw [sm, show c₂.nmem = c₁.nmem from rfl, am]; exact hm a (by omega)
  -- the run
  obtain ⟨c₄, k, j, ex, hk, hj, henc, hK, hr4, hrm4, ho4⟩ :=
    negFix_lgRun C C₀ hC g hpre I P' c₃ e₃.wb_right hA hm3 s31 (by rw [q30]; omega)
      (by rw [q30]; exact hpW) (by omega)
  rw [q30] at hK
  have k4 : ∀ r, nfR ≤ r → r ≠ 7330 → c₄.nreg r = c₃.nreg r := fun r h0 h1 =>
    hK.nreg r (by simp only [nfU, decide_eq_false_iff_not]; omega) h1
  -- after the run
  obtain ⟨c₅, t₅, e₅, ht₅, pkeep, pzero, pcopy, pabove, prest, pregs, pr, prm, po⟩ :=
    ncPost_exec (P := P') (Ws := rtW (Fintype.card D) (rtL M ℓ) g.G) c₄ ex.wb_right
      (by rw [k4 _ (by simp [nfR]) (by omega), k3 _ (by simp [nfR]) (by omega) (by omega)
        (by omega), r20])
      (by rw [k4 _ (by simp [nfR]) (by omega), k3 _ (by simp [nfR]) (by omega) (by omega)
        (by omega), r21])
      (by rw [k4 _ (by simp [nfR]) (by omega), k3 _ (by simp [nfR]) (by omega) (by omega)
        (by omega), r22])
      (by rw [k4 _ (by simp [nfR]) (by omega), k3 _ (by simp [nfR]) (by omega) (by omega)
        (by omega), r24])
      hK.lp (by omega) hhW (by omega) (by omega) hK.logle
  -- the memory of the run outside the image and the log
  have m43 : ∀ a, (∀ i < j, c₄.nmem (p + i) ≠ a) → a < p → c₄.nmem a = c₃.nmem a := by
    intro a hl hap
    by_cases ha : a ≤ rtW (Fintype.card D) (rtL M ℓ) g.G
    · exact hK.dirty a ha hl
    · exact hK.nmem a (by omega) (Or.inl hap)
  have m54 : ∀ a, ¬ (rtHb (Fintype.card D) (rtL M ℓ) g.G + 2 ≤ a ∧
      a < rtH (Fintype.card D) (rtL M ℓ) g.G (repsN M.dual g.gd).card
        (ck M.dual (repsN M.dual g.gd))) → (∀ i < j, c₄.nmem (p + i) ≠ a) →
      (a < Ob ∨ Ob + Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) ≤ a) →
      c₅.nmem a = c₄.nmem a := by
    intro a hr hl ho
    by_cases ha : a ≤ rtW (Fintype.card D) (rtL M ℓ) g.G
    · exact pkeep a ha hr hl
    · exact pabove a (by omega) (by omega)
  refine ⟨c₅, _, (e₁.seq (e₂.seq e₃)).seq (ex.seq e₅), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ncSvL, List.length_map, List.length_range, nfR]
    omega
  · intro a ha
    by_cases hr : rtHb (Fintype.card D) (rtL M ℓ) g.G + 2 ≤ a ∧
        a < rtH (Fintype.card D) (rtL M ℓ) g.G (repsN M.dual g.gd).card
          (ck M.dual (repsN M.dual g.gd))
    · exact pzero a (Or.inr hr)
    by_cases hl : ∃ i < j, c₄.nmem (p + i) = a
    · exact pzero a (Or.inl hl)
    simp only [not_exists, not_and] at hl
    rw [m54 a hr hl (Or.inl (by omega)), m43 a hl (by omega), sm,
      show c₂.nmem = c₁.nmem from rfl, am, hm a ha]
    exact rootMemP_out g M ℓ _ (by omega)
  · exact res_shift g M.dual henc (fun i hi => pcopy i (by omega))
  · intro a ha ho hp
    have hl : ∀ i < j, c₄.nmem (p + i) ≠ a := fun i hi e => by
      have := hK.logle i hi; omega
    rw [m54 a (by omega) hl ho, hK.nmem a (by omega) (by omega), sm,
      show c₂.nmem = c₁.nmem from rfl, am]
  · intro r h1 h2
    obtain ⟨i, hi, rfl⟩ : ∃ i < 13, r = 3000 + i := ⟨r - 3000, by omega, by omega⟩
    rw [prest i hi, k4 _ (by simp only [nfR]; omega) (by omega),
      skeep _ (by omega) (by omega) (by omega) (by omega) (by omega),
      k2 _ (by simp only [nfR]; omega),
      acp (7300 + i, 3000 + i) (mem_ncSvL.2 ⟨i, hi, rfl⟩)]
  · intro r hr
    have hr' := hr
    unfold ncScr at hr'
    rw [pregs r hr, k4 r (by simp only [nfR]; omega) (by omega),
      k3 r (by simp only [nfR]; omega) (by omega) (by omega) (by omega)]
  · rw [pr, hr4, sr]; exact ar
  · rw [prm, hrm4, srm]; exact arm
  · rw [po, ho4, so]; exact ao

end Call

end MfDrv

end BKMNW

end PlanarFlow
