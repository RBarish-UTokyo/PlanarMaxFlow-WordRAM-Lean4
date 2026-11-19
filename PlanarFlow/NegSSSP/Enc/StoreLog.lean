module

public import WordRAM
public import PlanarFlow.NegSSSP.LinGlue
public import PlanarFlow.Klein.ExecNat

/-!
# Logging the natural stores of a run, and clearing them afterwards

The node of the driver runs the fixed node program (`nodeFullR`) from a configuration whose
natural memory below its word bound `WN` must be **zero** except for the node's data (the
residues of the real memory of the simulation live at `W' + 1 + a` for every `a ≤ W'`, and
`W'` is a word bound — polynomial in the lengths — not a size). Zeroing `[0, WN]` before every
node costs `Θ(WN)` steps, which is not `O(m log m)`. Instead the driver keeps the memory below
the heap zero (an invariant) and every node **clears the cells it wrote**. For a program whose
footprint is not known, the cells written are logged:

* `lgS LP ONE s`: every `storeN a r` of `s` becomes `storeN a r ; storeN LP a ; LP := LP + ONE`
  (the address is appended to a log at `nreg LP`).
* **`lg_lift`**: a run of `s` with word bound `Ws` (naming only registers in `U`, no input, no
  randomness) from `c` to `c'` in `k` steps gives, from any `d` agreeing with `c` (registers in
  `U`, memory `≤ Ws`) with `LP ∉ U`, `ONE ∉ U`, `nreg ONE = 1`, `Ws < nreg LP = p`,
  `p + k ≤ W`, a run of `lgS LP ONE s` with word bound `W` in at most `3k` steps to a `d'`
  agreeing with `c'`, with `j ≤ k` log entries `≤ Ws` at `[p, p + j)`, every cell `≤ Ws` not in
  the log unchanged, the registers outside `U` but `LP` and the memory above `Ws` outside the log
  kept (`LgKeep`).
* `lgClr` (registers `2923 … 2929`: `p = r2924`, `LP = r2925`, `ONE = r2926`) and
  **`lgClr_exec`**: zero every logged cell within `6j + 5` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The transformation -/

/-- One instruction logged. -/
def lgI (LP ONE : ℕ) : Instr → Stmt
  | .storeN a r => .seq (.instr (.storeN a r)) (.seq (.instr (.storeN LP a))
      (.instr (.addN LP LP ONE)))
  | i => .instr i

/-- **The statement with its natural stores logged.** -/
def lgS (LP ONE : ℕ) : Stmt → Stmt
  | .skip => .skip
  | .instr i => lgI LP ONE i
  | .seq s t => .seq (lgS LP ONE s) (lgS LP ONE t)
  | .ifLtN a b t e => .ifLtN a b (lgS LP ONE t) (lgS LP ONE e)
  | .ifLtR a b t e => .ifLtR a b (lgS LP ONE t) (lgS LP ONE e)
  | .whileLtN a b body => .whileLtN a b (lgS LP ONE body)
  | .whileLtR a b body => .whileLtR a b (lgS LP ONE body)

/-- The frame of a logged run: `LP` advanced by the `j` entries of the log at `[p, p + j)`, the
entries `≤ Ws`, every cell `≤ Ws` outside the log unchanged, the registers outside `U` but `LP`
and the memory above `Ws` outside the log kept. -/
structure LgKeep (U : ℕ → Bool) (Ws LP p j : ℕ) (d d' : Config) : Prop where
  lp : d'.nreg LP = p + j
  nreg : ∀ r, U r = false → r ≠ LP → d'.nreg r = d.nreg r
  rreg : ∀ r, U r = false → d'.rreg r = d.rreg r
  nmem : ∀ a, Ws < a → (a < p ∨ p + j ≤ a) → d'.nmem a = d.nmem a
  rmem : ∀ a, Ws < a → d'.rmem a = d.rmem a
  logle : ∀ i < j, d'.nmem (p + i) ≤ Ws
  dirty : ∀ a ≤ Ws, (∀ i < j, d'.nmem (p + i) ≠ a) → d'.nmem a = d.nmem a

theorem LgKeep.trans {U : ℕ → Bool} {Ws LP p j₁ j₂ : ℕ} {d d₁ d₂ : Config} (hp : Ws < p)
    (h₁ : LgKeep U Ws LP p j₁ d d₁) (h₂ : LgKeep U Ws LP (p + j₁) j₂ d₁ d₂) :
    LgKeep U Ws LP p (j₁ + j₂) d d₂ where
  lp := by rw [h₂.lp]; omega
  nreg r hr hl := by rw [h₂.nreg r hr hl, h₁.nreg r hr hl]
  rreg r hr := by rw [h₂.rreg r hr, h₁.rreg r hr]
  nmem a ha h := by rw [h₂.nmem a ha (by omega), h₁.nmem a ha (by omega)]
  rmem a ha := by rw [h₂.rmem a ha, h₁.rmem a ha]
  logle i hi := by
    by_cases h : i < j₁
    · rw [h₂.nmem _ (by omega) (Or.inl (by omega))]; exact h₁.logle i h
    · have := h₂.logle (i - j₁) (by omega)
      rwa [show p + j₁ + (i - j₁) = p + i by omega] at this
  dirty a ha hn := by
    have e2 : d₂.nmem a = d₁.nmem a := h₂.dirty a ha fun i hi => by
      have := hn (j₁ + i) (by omega)
      rwa [show p + (j₁ + i) = p + j₁ + i by omega] at this
    rw [e2]
    refine h₁.dirty a ha fun i hi => ?_
    have := hn i (by omega)
    rwa [h₂.nmem _ (by omega) (Or.inl (by omega))] at this

theorem LgKeep.refl (U : ℕ → Bool) (Ws LP : ℕ) (d : Config) :
    LgKeep U Ws LP (d.nreg LP) 0 d d :=
  ⟨by omega, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ h => absurd h (by omega), fun _ _ _ => rfl⟩

/-- A non-store instruction keeps the natural memory. -/
theorem effect_nmem_keep {P : Input} {ins : Instr} {c c' : Config}
    (hst : ∀ a r, ins ≠ .storeN a r) (he : ins.effect P c = some c') : c'.nmem = c.nmem := by
  cases ins with
  | storeN a r => exact absurd rfl (hst a r)
  | divR r a b =>
    by_cases h0 : c.rreg b = 0
    · rw [Instr.effect_divR_zero _ _ _ h0] at he; cases he
    · rw [Instr.effect_divR _ _ _ h0, Option.some.injEq] at he; subst he; rfl
  | _ => simp only [Instr.effect, Option.some.injEq, reduceCtorEq] at he <;> (subst he; rfl)

/-! ### The simulation -/

section Lift

variable {P P' : Input} {Ws W : ℕ}

private lemma or_and' {x y : Bool} (h : (x && y) = true) : x = true ∧ y = true := by
  simpa using h

/-- One instruction, logged. -/
theorem lgI_exec {ins : Instr} {c c' : Config} {U : ℕ → Bool} {LP ONE : ℕ}
    (hst : ins.IsStraight) (he : ins.effect P c = some c') (hc : WordsBounded Ws c)
    (hc' : WordsBounded Ws c') (hok : ins.regsOK U = true) (hnr : ins.notInp = true)
    (hrd : ins.noRand = true) (hLP : U LP = false) (_hONE : U ONE = false) (_hne : LP ≠ ONE)
    (hWs : Ws ≤ W)
    {d : Config} (hA : Agree U Ws c d) (hd : WordsBounded W d) (h1 : d.nreg ONE = 1)
    (hp : Ws < d.nreg LP) (hpW : d.nreg LP + 1 ≤ W) :
    ∃ d' k' j, Exec P' W (lgI LP ONE ins) d d' k' ∧ k' ≤ 3 * 1 ∧ j ≤ 1 ∧ Agree U Ws c' d' ∧
      LgKeep U Ws LP (d.nreg LP) j d d' ∧
      ∃ L, c'.output = c.output ++ L ∧ d'.output = d.output ++ L := by
  by_cases hs : ∃ a r, ins = .storeN a r
  · obtain ⟨a, r, rfl⟩ := hs
    have hl : ∀ x ∈ (Instr.storeN a r).regs, U x = true := fun x hx =>
      List.all_eq_true.1 hok x hx
    have ha : U a = true := hl a (by simp [Instr.regs])
    have hr' : U r = true := hl r (by simp [Instr.regs])
    have haLP : a ≠ LP := fun e => by rw [e, hLP] at ha; exact absurd ha (by simp)
    simp only [Instr.effect, Option.some.injEq] at he
    subst he
    set p := d.nreg LP with hpdef
    have hAa : d.nreg a = c.nreg a := hA.nreg a ha
    have hAr : d.nreg r = c.nreg r := hA.nreg r hr'
    have haW : c.nreg a ≤ Ws := WordsBounded.nreg hc a
    let d₁ : Config := { d with nmem := upd d.nmem (d.nreg a) (d.nreg r) }
    let d₂ : Config := { d₁ with nmem := upd d₁.nmem (d₁.nreg LP) (d₁.nreg a) }
    let d₃ : Config := { d₂ with nreg := upd d₂.nreg LP (d₂.nreg LP + d₂.nreg ONE) }
    have hd₁ : WordsBounded W d₁ := by
      refine ⟨fun x => WordsBounded.nreg hd x, fun x => ?_⟩
      show upd d.nmem (d.nreg a) (d.nreg r) x ≤ W
      simp only [upd_apply]; split
      · exact WordsBounded.nreg hd r
      · exact WordsBounded.nmem hd x
    have hd₂ : WordsBounded W d₂ := by
      refine ⟨fun x => WordsBounded.nreg hd₁ x, fun x => ?_⟩
      show upd d₁.nmem (d₁.nreg LP) (d₁.nreg a) x ≤ W
      simp only [upd_apply]; split
      · exact WordsBounded.nreg hd₁ a
      · exact WordsBounded.nmem hd₁ x
    have q2 : d₂.nreg ONE = 1 := h1
    have hd₃ : WordsBounded W d₃ := by
      refine ⟨fun x => ?_, fun x => WordsBounded.nmem hd₂ x⟩
      show upd d₂.nreg LP (d₂.nreg LP + d₂.nreg ONE) x ≤ W
      simp only [upd_apply]; split
      · rw [q2]; exact hpW
      · exact WordsBounded.nreg hd₂ x
    have m3 : ∀ x, d₃.nmem x = upd (upd d.nmem (d.nreg a) (d.nreg r)) p (d.nreg a) x :=
      fun x => rfl
    refine ⟨d₃, 3, 1, .seq (.instr (by simp [Instr.IsStraight, Instr.isControl]) rfl hd hd₁)
      (.seq (.instr (by simp [Instr.IsStraight, Instr.isControl]) rfl hd₁ hd₂)
        (.instr (by simp [Instr.IsStraight, Instr.isControl]) rfl hd₂ hd₃)), le_refl _,
      le_refl _, ⟨fun x hx => ?_, fun x hx => hA.rreg x hx, fun x hx => ?_,
        fun x hx => hA.rmem x hx⟩, ⟨?_, fun x hx hxl => ?_, fun _ _ => rfl, fun x hx h => ?_,
        fun _ _ => rfl, fun i hi => ?_, fun x hx hn => ?_⟩, [], by simp, by simp [d₃, d₂, d₁]⟩
    · show upd d₂.nreg LP _ x = _
      rw [upd_other _ _ _ (fun e => by rw [e, hLP] at hx; exact absurd hx (by simp))]
      exact hA.nreg x hx
    · rw [m3, upd_other _ _ _ (by omega), hAa, hAr]
      show _ = upd c.nmem (c.nreg a) (c.nreg r) x
      simp only [upd_apply]; split
      · rfl
      · exact hA.nmem x hx
    · show upd d₂.nreg LP (d₂.nreg LP + d₂.nreg ONE) LP = p + 1
      rw [upd_same, q2]
    · show upd d₂.nreg LP _ x = _
      rw [upd_other _ _ _ hxl]
    · rw [m3, upd_other _ _ _ (by omega), upd_other _ _ _ (by rw [hAa]; omega)]
    · have : i = 0 := by omega
      subst this
      rw [m3, Nat.add_zero, upd_same, hAa]; exact haW
    · have hxa : x ≠ c.nreg a := fun e => hn 0 (by omega) (by
        rw [m3, Nat.add_zero, upd_same, hAa, e])
      rw [m3, upd_other _ _ _ (by omega), upd_other _ _ _ (by rw [hAa]; exact hxa)]
  · push Not at hs
    obtain ⟨d₁, ed, hA₁, hK₁, L, o₁, o₂⟩ :=
      effect_embed (P' := P') hok hnr (Or.inl hrd) he hc hA
    have hlg : lgI LP ONE ins = .instr ins := by
      cases ins <;> first | rfl | exact absurd rfl (hs _ _)
    rw [hlg]
    have hd₁ : WordsBounded W d₁ :=
      wordsBounded_of_agree hA₁ hc' hWs (fun r hr => by rw [hK₁.nreg r hr]; exact hd.1 r)
        (fun a ha => by rw [hK₁.nmem a ha]; exact hd.2 a)
    have hm : d₁.nmem = d.nmem := effect_nmem_keep hs ed
    refine ⟨d₁, 1, 0, .instr hst ed hd hd₁, by omega, by omega, hA₁,
      ⟨by rw [hK₁.nreg LP hLP]; omega, fun r hr _ => hK₁.nreg r hr, hK₁.rreg,
        fun a ha _ => hK₁.nmem a ha, hK₁.rmem, fun i hi => absurd hi (by omega),
        fun a _ _ => by rw [hm]⟩, L, o₁, o₂⟩

/-- **The logged run.** -/
theorem lg_lift {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P Ws s c c' k) {U : ℕ → Bool}
    {LP ONE : ℕ} (hs : s.regsOK U = true) (hn : s.noInp = true) (hr : s.noRand = true)
    (hLP : U LP = false) (hONE : U ONE = false) (hne : LP ≠ ONE) (hWs : Ws ≤ W) :
    ∀ d, Agree U Ws c d → WordsBounded W d → d.nreg ONE = 1 → Ws < d.nreg LP →
      d.nreg LP + k ≤ W →
      ∃ d' k' j, Exec P' W (lgS LP ONE s) d d' k' ∧ k' ≤ 3 * k ∧ j ≤ k ∧ Agree U Ws c' d' ∧
        LgKeep U Ws LP (d.nreg LP) j d d' ∧
        ∃ L, c'.output = c.output ++ L ∧ d'.output = d.output ++ L := by
  induction h with
  | skip hw =>
    intro d hA hd _ _ _
    exact ⟨d, 0, 0, .skip hd, le_refl _, le_refl _, hA, LgKeep.refl U Ws LP d, [], by simp,
      by simp⟩
  | instr hst he hw hw' =>
    intro d hA hd h1 hp hpW
    exact lgI_exec hst he hw hw' hs hn hr hLP hONE hne hWs hA hd h1 hp hpW
  | @seq s t c c₁ c₂ k₁ k₂ _ _ ih₁ ih₂ =>
    intro d hA hd h1 hp hpW
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true] at hs hn hr
    obtain ⟨d₁, k₁', j₁, e₁, a₁, b₁, hA₁, hK₁, L₁, o₁, o₁'⟩ :=
      ih₁ hs.1 hn.1 hr.1 d hA hd h1 hp (by omega)
    have g1 : d₁.nreg ONE = 1 := by
      rw [hK₁.nreg ONE hONE (Ne.symm hne)]
      exact h1
    obtain ⟨d₂, k₂', j₂, e₂, a₂, b₂, hA₂, hK₂, L₂, o₂, o₂'⟩ :=
      ih₂ hs.2 hn.2 hr.2 d₁ hA₁ e₁.wb_right g1 (by rw [hK₁.lp]; omega)
        (by rw [hK₁.lp]; omega)
    rw [hK₁.lp] at hK₂
    exact ⟨d₂, k₁' + k₂', j₁ + j₂, .seq e₁ e₂, by omega, by omega, hA₂, hK₁.trans hp hK₂,
      L₁ ++ L₂, by rw [o₂, o₁, List.append_assoc], by rw [o₂', o₁', List.append_assoc]⟩
  | @ifLtN_true a b t e c c' k ht _ ih =>
    intro d hA hd h1 hp hpW
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true] at hs hn hr
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, -⟩ := hs
    obtain ⟨d', k', j, e', a', b', hA', hK', L, o⟩ :=
      ih hst hn.1 hr.1 d hA hd h1 hp (by omega)
    exact ⟨d', k' + 1, j, .ifLtN_true (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) e',
      by omega, by omega, hA', hK', L, o⟩
  | @ifLtN_false a b t e c c' k ht _ ih =>
    intro d hA hd h1 hp hpW
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true] at hs hn hr
    obtain ⟨⟨⟨ha, hb⟩, -⟩, hse⟩ := hs
    obtain ⟨d', k', j, e', a', b', hA', hK', L, o⟩ :=
      ih hse hn.2 hr.2 d hA hd h1 hp (by omega)
    exact ⟨d', k' + 2, j, .ifLtN_false (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) e',
      by omega, by omega, hA', hK', L, o⟩
  | @ifLtR_true a b t e c c' k ht _ ih =>
    intro d hA hd h1 hp hpW
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true] at hs hn hr
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, -⟩ := hs
    obtain ⟨d', k', j, e', a', b', hA', hK', L, o⟩ :=
      ih hst hn.1 hr.1 d hA hd h1 hp (by omega)
    exact ⟨d', k' + 1, j, .ifLtR_true (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) e',
      by omega, by omega, hA', hK', L, o⟩
  | @ifLtR_false a b t e c c' k ht _ ih =>
    intro d hA hd h1 hp hpW
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true] at hs hn hr
    obtain ⟨⟨⟨ha, hb⟩, -⟩, hse⟩ := hs
    obtain ⟨d', k', j, e', a', b', hA', hK', L, o⟩ :=
      ih hse hn.2 hr.2 d hA hd h1 hp (by omega)
    exact ⟨d', k' + 2, j, .ifLtR_false (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) e',
      by omega, by omega, hA', hK', L, o⟩
  | @whileLtN_false a b body c ht hw =>
    intro d hA hd _ _ _
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨ha, hb⟩, _⟩ := hs
    exact ⟨d, 2, 0, .whileLtN_false (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) hd,
      by omega, by omega, hA, LgKeep.refl U Ws LP d, [], by simp, by simp⟩
  | @whileLtN_true a b body c c₁ c' k₁ k₂ ht _ _ ih₁ ih₂ =>
    intro d hA hd h1 hp hpW
    have hs' := hs
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs'
    obtain ⟨⟨ha, hb⟩, hsb⟩ := hs'
    obtain ⟨d₁, k₁', j₁, e₁, a₁, b₁, hA₁, hK₁, L₁, o₁, o₁'⟩ :=
      ih₁ hsb hn hr d hA hd h1 hp (by omega)
    have g1 : d₁.nreg ONE = 1 := by
      rw [hK₁.nreg ONE hONE (Ne.symm hne)]
      exact h1
    obtain ⟨d₂, k₂', j₂, e₂, a₂, b₂, hA₂, hK₂, L₂, o₂, o₂'⟩ :=
      ih₂ hs hn hr d₁ hA₁ e₁.wb_right g1 (by rw [hK₁.lp]; omega) (by rw [hK₁.lp]; omega)
    rw [hK₁.lp] at hK₂
    exact ⟨d₂, k₁' + 2 + k₂', j₁ + j₂,
      .whileLtN_true (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) e₁ e₂, by omega, by omega,
      hA₂, hK₁.trans hp hK₂, L₁ ++ L₂, by rw [o₂, o₁, List.append_assoc],
      by rw [o₂', o₁', List.append_assoc]⟩
  | @whileLtR_false a b body c ht hw =>
    intro d hA hd _ _ _
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨ha, hb⟩, _⟩ := hs
    exact ⟨d, 2, 0, .whileLtR_false (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) hd,
      by omega, by omega, hA, LgKeep.refl U Ws LP d, [], by simp, by simp⟩
  | @whileLtR_true a b body c c₁ c' k₁ k₂ ht _ _ ih₁ ih₂ =>
    intro d hA hd h1 hp hpW
    have hs' := hs
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs'
    obtain ⟨⟨ha, hb⟩, hsb⟩ := hs'
    obtain ⟨d₁, k₁', j₁, e₁, a₁, b₁, hA₁, hK₁, L₁, o₁, o₁'⟩ :=
      ih₁ hsb hn hr d hA hd h1 hp (by omega)
    have g1 : d₁.nreg ONE = 1 := by
      rw [hK₁.nreg ONE hONE (Ne.symm hne)]
      exact h1
    obtain ⟨d₂, k₂', j₂, e₂, a₂, b₂, hA₂, hK₂, L₂, o₂, o₂'⟩ :=
      ih₂ hs hn hr d₁ hA₁ e₁.wb_right g1 (by rw [hK₁.lp]; omega) (by rw [hK₁.lp]; omega)
    rw [hK₁.lp] at hK₂
    exact ⟨d₂, k₁' + 2 + k₂', j₁ + j₂,
      .whileLtR_true (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) e₁ e₂, by omega, by omega,
      hA₂, hK₁.trans hp hK₂, L₁ ++ L₂, by rw [o₂, o₁, List.append_assoc],
      by rw [o₂', o₁', List.append_assoc]⟩

end Lift


/-! ### Syntactic properties of the logged statement -/

theorem lgI_regsOK {U V : ℕ → Bool} {LP ONE : ℕ} {i : Instr} (h : i.regsOK U = true)
    (hUV : ∀ r, U r = true → V r = true) (hLP : V LP = true) (hONE : V ONE = true) :
    (lgI LP ONE i).regsOK V = true := by
  have hV : i.regsOK V = true := List.all_eq_true.2 fun r hr => hUV r (List.all_eq_true.1 h r hr)
  cases i with
  | storeN a r =>
    have ha : U a = true := List.all_eq_true.1 h a (by simp [Instr.regs])
    have hr : U r = true := List.all_eq_true.1 h r (by simp [Instr.regs])
    simp only [lgI, Stmt.regsOK, Instr.regsOK, Instr.regs, List.all_cons, List.all_nil,
      Bool.and_true, Bool.and_eq_true]
    simp [hLP, hONE, hUV a ha, hUV r hr]
  | _ => exact hV

theorem lgS_regsOK {U V : ℕ → Bool} {LP ONE : ℕ} (hUV : ∀ r, U r = true → V r = true)
    (hLP : V LP = true) (hONE : V ONE = true) :
    ∀ s : Stmt, s.regsOK U = true → (lgS LP ONE s).regsOK V = true
  | .skip, _ => rfl
  | .instr i, h => lgI_regsOK h hUV hLP hONE
  | .seq s t, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true, lgS] at h ⊢
    exact ⟨lgS_regsOK hUV hLP hONE s h.1, lgS_regsOK hUV hLP hONE t h.2⟩
  | .ifLtN a b t e, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true, lgS] at h ⊢
    exact ⟨⟨⟨hUV a h.1.1.1, hUV b h.1.1.2⟩, lgS_regsOK hUV hLP hONE t h.1.2⟩,
      lgS_regsOK hUV hLP hONE e h.2⟩
  | .ifLtR a b t e, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true, lgS] at h ⊢
    exact ⟨⟨⟨hUV a h.1.1.1, hUV b h.1.1.2⟩, lgS_regsOK hUV hLP hONE t h.1.2⟩,
      lgS_regsOK hUV hLP hONE e h.2⟩
  | .whileLtN a b body, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true, lgS] at h ⊢
    exact ⟨⟨hUV a h.1.1, hUV b h.1.2⟩, lgS_regsOK hUV hLP hONE body h.2⟩
  | .whileLtR a b body, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true, lgS] at h ⊢
    exact ⟨⟨hUV a h.1.1, hUV b h.1.2⟩, lgS_regsOK hUV hLP hONE body h.2⟩

theorem lgS_noInp {LP ONE : ℕ} : ∀ s : Stmt, s.noInp = true → (lgS LP ONE s).noInp = true
  | .skip, _ => rfl
  | .instr i, h => by cases i <;> exact h
  | .seq s t, h => by
    simp only [Stmt.noInp, Bool.and_eq_true, lgS] at h ⊢
    exact ⟨lgS_noInp s h.1, lgS_noInp t h.2⟩
  | .ifLtN a b t e, h => by
    simp only [Stmt.noInp, Bool.and_eq_true, lgS] at h ⊢
    exact ⟨lgS_noInp t h.1, lgS_noInp e h.2⟩
  | .ifLtR a b t e, h => by
    simp only [Stmt.noInp, Bool.and_eq_true, lgS] at h ⊢
    exact ⟨lgS_noInp t h.1, lgS_noInp e h.2⟩
  | .whileLtN a b body, h => by
    simp only [Stmt.noInp, lgS] at h ⊢; exact lgS_noInp body h
  | .whileLtR a b body, h => by
    simp only [Stmt.noInp, lgS] at h ⊢; exact lgS_noInp body h

theorem lgS_noRand {LP ONE : ℕ} : ∀ s : Stmt, s.noRand = true → (lgS LP ONE s).noRand = true
  | .skip, _ => rfl
  | .instr i, h => by cases i <;> exact h
  | .seq s t, h => by
    simp only [Stmt.noRand, Bool.and_eq_true, lgS] at h ⊢
    exact ⟨lgS_noRand s h.1, lgS_noRand t h.2⟩
  | .ifLtN a b t e, h => by
    simp only [Stmt.noRand, Bool.and_eq_true, lgS] at h ⊢
    exact ⟨lgS_noRand t h.1, lgS_noRand e h.2⟩
  | .ifLtR a b t e, h => by
    simp only [Stmt.noRand, Bool.and_eq_true, lgS] at h ⊢
    exact ⟨lgS_noRand t h.1, lgS_noRand e h.2⟩
  | .whileLtN a b body, h => by
    simp only [Stmt.noRand, lgS] at h ⊢; exact lgS_noRand body h
  | .whileLtR a b body, h => by
    simp only [Stmt.noRand, lgS] at h ⊢; exact lgS_noRand body h

theorem lgS_natOnly {LP ONE : ℕ} :
    ∀ s : Stmt, Klein.natOnly s = true → Klein.natOnly (lgS LP ONE s) = true
  | .skip, _ => rfl
  | .instr i, h => by cases i <;> exact h
  | .seq s t, h => by
    simp only [Klein.natOnly, Bool.and_eq_true, lgS] at h ⊢
    exact ⟨lgS_natOnly s h.1, lgS_natOnly t h.2⟩
  | .ifLtN a b t e, h => by
    simp only [Klein.natOnly, Bool.and_eq_true, lgS] at h ⊢
    exact ⟨lgS_natOnly t h.1, lgS_natOnly e h.2⟩
  | .ifLtR a b t e, h => by simp [Klein.natOnly] at h
  | .whileLtN a b body, h => by
    simp only [Klein.natOnly, lgS] at h ⊢; exact lgS_natOnly body h
  | .whileLtR a b body, h => by simp [Klein.natOnly] at h

/-! ### Clearing the logged cells -/

/-- The body of the clearing loop: `nmem[nmem[p + i]] := 0`, `i := i + 1`. -/
def lgClrBody : Stmt :=
  block [.addN 2928 2924 2927, .loadN 2928 2928, .storeN 2928 2929, .addN 2927 2927 2926]

/-- **Clear the logged cells** (`p = r2924`, `LP = r2925`, `ONE = r2926`; scratch
`2923`, `2927 … 2929`). -/
def lgClr : Stmt :=
  .seq (block [.constN 2929 0, .constN 2927 0, .subN 2923 2925 2924])
    (.whileLtN 2927 2923 lgClrBody)

theorem lgClr_natOnly : Klein.natOnly lgClr = true := by decide

variable {P : Input} {W : ℕ}

/-- **The clearing loop**: every cell named in the log `[p, p + j)` (entries `≤ Ws < p`) is
zero, every other cell is kept, within `6 j + 5` steps. -/
theorem lgClr_exec (c : Config) (hc : WordsBounded W c) {p j Ws : ℕ}
    (r24 : c.nreg 2924 = p) (r25 : c.nreg 2925 = p + j) (r26 : c.nreg 2926 = 1)
    (hlog : ∀ i < j, c.nmem (p + i) ≤ Ws) (hp : Ws < p) :
    ∃ c' t, Exec P W lgClr c c' t ∧ t ≤ 6 * j + 5 ∧
      (∀ a, (∃ i < j, c.nmem (p + i) = a) → c'.nmem a = 0) ∧
      (∀ a, (∀ i < j, c.nmem (p + i) ≠ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2923 → (r < 2927 ∨ 2929 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hpW : p + j ≤ W := r25 ▸ WordsBounded.nreg hc 2925
  obtain ⟨c₁, k₁, e₁, hk₁, g29, g27, g23, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2929 0, .constN 2927 0, .subN 2923 2925 2924]) c c₁ k₁ ∧
      k₁ = 3 ∧ c₁.nreg 2929 = 0 ∧ c₁.nreg 2927 = 0 ∧ c₁.nreg 2923 = j ∧
      (∀ r, r ≠ 2923 → r ≠ 2927 → r ≠ 2929 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r24, r25]; omega)
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ a, (∃ i' < i, c.nmem (p + i') = a) → c'.nmem a = 0) ∧
      (∀ a, (∀ i' < i, c.nmem (p + i') ≠ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2927 → r ≠ 2928 → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2927) (bR := 2923)
    (body := lgClrBody) J (K := 4) (n := j) c₁ e₁.wb_right g27 g23
    ⟨fun a ⟨i, hi, _⟩ => absurd hi (by omega), fun a _ => by rw [gm₁], fun _ _ _ => rfl,
      gr₁, grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
      have q24 : c'.nreg 2924 = p := by
        rw [jn _ (by omega) (by omega), gn₁ _ (by omega) (by omega) (by omega)]; exact r24
      have q26 : c'.nreg 2926 = 1 := by
        rw [jn _ (by omega) (by omega), gn₁ _ (by omega) (by omega) (by omega)]; exact r26
      have q29 : c'.nreg 2929 = 0 := by rw [jn _ (by omega) (by omega)]; exact g29
      have hlogi : c'.nmem (p + i) = c.nmem (p + i) := j2 _ fun i' hi' e => by
        have := hlog i' (by omega); omega
      obtain ⟨c'', t, ex, ht, hm, h27, hn, hr, hrm, ho⟩ : ∃ c'' t,
          Exec P W lgClrBody c' c'' t ∧ t = 4 ∧
          c''.nmem = upd c'.nmem (c.nmem (p + i)) 0 ∧
          c''.nreg 2927 = i + 1 ∧ (∀ r, r ≠ 2927 → r ≠ 2928 → c''.nreg r = c'.nreg r) ∧
          c''.rreg = c'.rreg ∧ c''.rmem = c'.rmem ∧ c''.output = c'.output := by
        unfold lgClrBody
        exec_block
        all_goals try ((try config_simp); (try simp only [q24, q26, q29, ha]); omega)
        refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
        all_goals config_simp
        all_goals try (simp only [q24, q26, q29, ha, hlogi])
        all_goals try omega
        simp only [upd_apply]; split_ifs <;> omega
      refine ⟨c'', t, ex, by omega, h27, (hn _ (by omega) (by omega)).trans hb, fun a ha' => ?_,
        fun a ha' => ?_, fun r h1 h2 => (hn r h1 h2).trans (jn r h1 h2), by rw [hr, jr],
        by rw [hrm, jrm], by rw [ho, jo]⟩
      · obtain ⟨i', hi', rfl⟩ := ha'
        rw [hm, upd_apply]
        split_ifs with h
        · rfl
        · exact j1 _ ⟨i', by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h' | h'
            · exact h'
            · subst h'; exact absurd rfl h, rfl⟩
      · rw [hm, upd_other _ _ _ (fun e => ha' i (by omega) e.symm)]
        exact j2 a fun i' hi' => ha' i' (by omega))
  obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j1, j2, fun r h1 h2 => ?_, jr, jrm, jo⟩
  rw [jn r (by omega) (by omega), gn₁ r h1 (by omega) (by omega)]

end NegSSSP

end PlanarFlow
