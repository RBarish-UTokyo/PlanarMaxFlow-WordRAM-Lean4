module

public import PlanarSeparator.Machine.SepCall

/-!
# Subroutine calls with the input base and length in registers

`WordRAM.Machine.Stmt.toMem tmp β len` (`WordRAM/Machine/WordMono.lean`) reads the input of a
subroutine from memory at the **constant** base `β`, with the **constant** length `len`; a fixed
program calling the separator program on inputs of varying sizes needs both in registers.

* `Stmt.toMemR tmp rβ rlen`: `readIn r a` becomes `tmp := rβ; tmp := tmp + a; r := nmem tmp`,
  and `inputSize r` becomes `r := rlen`.
* **`WordRAM.Machine.Exec.embedR`**: the embedding theorem `Exec.embed` for `toMemR`, with the
  base and the length held in the registers `rβ`, `rlen` outside `U` (other than `tmp`).
* **`WordRAM.Machine.Exec.subcallR`**: `Exec.subcall` for `toMemR`.
* `Stmt.noReal`, **`WordRAM.Machine.Exec.real_of_noReal`**: a statement without real
  instructions keeps the real registers and the real memory.
* `zeroRegs n`, `Exec.zeroRegs`: the registers `< n` set to zero in `n` steps.
* **`PlanarSeparator.ltSubR`**, **`PlanarSeparator.ltSubR_exec`**: the separator program as a
  subroutine with the input base and length in registers (`ltSub_exec` for `toMemR`), keeping
  the real registers and the real memory.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace WordRAM

namespace Machine

open Instr

namespace Stmt

/-- One instruction with the input read from memory at the base held in the register `rβ`:
`readIn r a` becomes `tmp := rβ; tmp := tmp + a; r := nmem tmp`, and `inputSize r` becomes
`r := rlen`. -/
def instrToMemR (tmp rβ rlen : ℕ) : Instr → Stmt
  | .readIn r a =>
    .seq (.instr (.copyN tmp rβ)) (.seq (.instr (.addN tmp tmp a)) (.instr (.loadN r tmp)))
  | .inputSize r => .instr (.copyN r rlen)
  | i => .instr i

/-- The statement with the input read from memory at the base in the register `rβ` and the
input size in the register `rlen` (`instrToMemR`). -/
def toMemR (tmp rβ rlen : ℕ) : Stmt → Stmt
  | .skip => .skip
  | .instr i => instrToMemR tmp rβ rlen i
  | .seq s t => .seq (toMemR tmp rβ rlen s) (toMemR tmp rβ rlen t)
  | .ifLtN a b t e => .ifLtN a b (toMemR tmp rβ rlen t) (toMemR tmp rβ rlen e)
  | .ifLtR a b t e => .ifLtR a b (toMemR tmp rβ rlen t) (toMemR tmp rβ rlen e)
  | .whileLtN a b body => .whileLtN a b (toMemR tmp rβ rlen body)
  | .whileLtR a b body => .whileLtR a b (toMemR tmp rβ rlen body)

theorem instrToMemR_of_notInp {tmp rβ rlen : ℕ} {i : Instr} (h : i.notInp = true) :
    instrToMemR tmp rβ rlen i = .instr i := by
  cases i <;> first | rfl | simp [Instr.notInp] at h

end Stmt

open Stmt

/-- The input words at `β` (`InData`) with the base `β` in the register `rβ` and the length
`len` in the register `rlen`, these registers and `tmp` outside `U`. -/
abbrev InDR (P : Input) (W β len W' : ℕ) (U : ℕ → Bool) (tmp rβ rlen : ℕ) (d : Config) : Prop :=
  (InData P W β len W' d ∧ U tmp = false) ∧
    (d.nreg rβ = β ∧ d.nreg rlen = len ∧ U rβ = false ∧ U rlen = false ∧ rβ ≠ tmp ∧ rlen ≠ tmp)

namespace Exec

variable {P P' : Input} {W : ℕ}

private lemma or_andR {x y : Bool} {Q : Prop} (h : (x && y) = true ∨ Q) :
    (x = true ∨ Q) ∧ (y = true ∨ Q) := by
  rcases h with h | h
  · simp only [Bool.and_eq_true] at h; exact ⟨Or.inl h.1, Or.inl h.2⟩
  · exact ⟨Or.inr h, Or.inr h⟩

/-- **Embedding of a structured run.** Let `s` name only registers satisfying `U` and run from
`c` to `c'` in `k` steps with word bound `W` on input `P`. From any configuration `d` bounded by
`W' ≥ W`, agreeing with `c` on the registers in `U` and on the memory at addresses `≤ W`, and
holding the input words of `P` at `β` (`InData`, with `len` the number of words) unless `s` has
neither `readIn` nor `inputSize`, the statement `s.toMemR tmp rβ rlen` (`tmp` a register outside
`U`) runs on any input `P'` with the random tape of `P` (any input at all if `s` has no `rand`)
in `k'` steps, `k ≤ k' ≤ 3k` (`k' = k` without `readIn` and `inputSize`), to a configuration
agreeing with `c'`, keeping the registers outside `U` but `tmp` (and `tmp` too without
`readIn`, `inputSize`) and the memory above `W`, and appending to the output what `s`
appends. -/
theorem embedR {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k) {U : ℕ → Bool}
    {W' tmp β len rβ rlen : ℕ} (hs : s.regsOK U = true) (hW : W ≤ W')
    (hrd : s.noRand = true ∨ P'.tape = P.tape) :
    ∀ d, Agree U W c d → WordsBounded W' d →
      (s.noInp = true ∨ (InDR P W β len W' U tmp rβ rlen d)) →
      ∃ d' k', Exec P' W' (s.toMemR tmp rβ rlen) d d' k' ∧ k ≤ k' ∧ k' ≤ 3 * k ∧
        (s.noInp = true → k' = k) ∧ Agree U W c' d' ∧ KeepT U W tmp s.noInp d d' ∧
        ∃ L, c'.output = c.output ++ L ∧ d'.output = d.output ++ L := by
  -- the data region survives a frame
  have hID : ∀ {ro : Bool} {d d' : Config}, KeepT U W tmp ro d d' →
      InDR P W β len W' U tmp rβ rlen d → InDR P W β len W' U tmp rβ rlen d' :=
    fun hK ⟨⟨hI, ht⟩, h1, h2, h3, h4, h5, h6⟩ => ⟨⟨⟨hI.lt, hI.le, hI.len, fun i hi => by
      rw [hK.nmem _ (by have := hI.lt; omega)]; exact hI.mem i hi⟩, ht⟩,
      by rw [hK.nreg _ h3 (fun e => absurd e h5)]; exact h1,
      by rw [hK.nreg _ h4 (fun e => absurd e h6)]; exact h2, h3, h4, h5, h6⟩
  induction h with
  | skip hw =>
    intro d hA hd _
    exact ⟨d, 0, .skip hd, le_rfl, by omega, fun _ => rfl, hA, (Keep.refl _ _ _).toT _ _, [],
      by simp, by simp⟩
  | @instr ins c c' hst he hw hw' =>
    intro d hA hd hD
    have hl : ∀ r ∈ ins.regs, U r = true := fun r hr => List.all_eq_true.1 hs r hr
    by_cases hri : ins.notInp = true
    · obtain ⟨d', hed, hA', hK, L, hL⟩ := effect_embed (P' := P') hs hri hrd he hw hA
      have hd' : WordsBounded W' d' := wordsBounded_of_agree hA' hw' hW
        (fun r hr => by rw [hK.nreg r hr]; exact WordsBounded.nreg hd r)
        (fun a ha => by rw [hK.nmem a ha]; exact WordsBounded.nmem hd a)
      refine ⟨d', 1, ?_, le_rfl, by omega, fun _ => rfl, hA', hK.toT _ _, L, hL⟩
      rw [show (Stmt.instr ins).toMemR tmp rβ rlen = .instr ins from instrToMemR_of_notInp hri]
      exact .instr hst hed hd hd'
    · have hnr : (Stmt.instr ins).noInp = false := by
        simp only [Bool.not_eq_true] at hri; exact hri
      obtain ⟨⟨hI, htmp⟩, hRβ, hRlen, -, -, -, -⟩ : InDR P W β len W' U tmp rβ rlen d := by
        rcases hD with hD | hI
        · rw [hnr] at hD; cases hD
        · exact hI
      have hβ := hI.lt; have hβ' := hI.le
      cases ins with
      | readIn r a =>
        have hr := hl r (by simp [Instr.regs])
        have ha := hl a (by simp [Instr.regs])
        have hrt : r ≠ tmp := fun e => by rw [e, htmp] at hr; cases hr
        have hat : a ≠ tmp := fun e => by rw [e, htmp] at ha; cases ha
        simp only [Instr.effect, Option.some.injEq] at he; subst he
        have hca := WordsBounded.nreg hw a
        set d₁ : Config := { d with nreg := upd d.nreg tmp β } with hd₁
        have hw₁ : WordsBounded W' d₁ := ⟨upd_le hd.1 (by omega), hd.2⟩
        have e₁a : d₁.nreg a = c.nreg a := by
          rw [hd₁]; simp only [upd_other _ _ _ hat]; exact hA.nreg a ha
        set d₂ : Config := { d₁ with nreg := upd d₁.nreg tmp (d₁.nreg tmp + d₁.nreg a) }
          with hd₂
        have e₂ : d₂.nreg tmp = β + c.nreg a := by
          rw [hd₂]; simp only [upd_apply, ite_true]; rw [e₁a, hd₁]; simp
        have hw₂ : WordsBounded W' d₂ := ⟨upd_le hw₁.1 (by
          rw [e₁a, hd₁]; simp only [upd_apply, ite_true]; omega), hw₁.2⟩
        set d₃ : Config := { d₂ with nreg := upd d₂.nreg r (d₂.nmem (d₂.nreg tmp)) } with hd₃
        have hval : d₂.nmem (d₂.nreg tmp) = P.data.getD (c.nreg a) 0 := by
          rw [e₂]; exact hI.mem _ hca
        have hA₃ : Agree U W { c with nreg := upd c.nreg r (P.data.getD (c.nreg a) 0) } d₃ := by
          refine ⟨fun x hx => ?_, hA.rreg, hA.nmem, hA.rmem⟩
          have hxt : x ≠ tmp := fun e => by rw [e, htmp] at hx; cases hx
          rw [hd₃]; simp only [hval, upd_apply]
          split
          · rfl
          · rw [hd₂]; simp only [upd_apply, hxt, ite_false]
            rw [hd₁]; simp only [upd_apply, hxt, ite_false]; exact hA.nreg x hx
        have hK₃ : KeepT U W tmp false d d₃ := by
          refine ⟨fun x hx ht => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
          have hxt : x ≠ tmp := fun e => by simpa using ht e
          have hxr : x ≠ r := fun e => by rw [e, hr] at hx; cases hx
          rw [hd₃]; simp only [upd_other _ _ _ hxr]
          rw [hd₂]; simp only [upd_other _ _ _ hxt]
          rw [hd₁]; simp only [upd_other _ _ _ hxt]
        have hw₃ : WordsBounded W' d₃ := ⟨upd_le hw₂.1 (by
          rw [hval]; have := WordsBounded.nreg hw' r; simp only [upd_apply, ite_true] at this
          omega), hw₂.2⟩
        refine ⟨d₃, 1 + (1 + 1), ?_, by omega, by omega, (fun h => by rw [hnr] at h; cases h),
          hA₃, (by rw [hnr]; exact hK₃), [], by simp, by simp [hd₃, hd₂, hd₁]⟩
        exact .seq (.instr rfl (by rw [hd₁, ← hRβ]; rfl) hd hw₁) (.seq (.instr rfl rfl hw₁ hw₂) (.instr rfl rfl hw₂ hw₃))
      | inputSize r =>
        have hr := hl r (by simp [Instr.regs])
        simp only [Instr.effect, Option.some.injEq] at he; subst he
        have hlen : len ≤ W' := by
          have := WordsBounded.nreg hw' r; simp only [upd_apply, ite_true] at this
          rw [hI.len]; omega
        have hw₁ : WordsBounded W' { d with nreg := upd d.nreg r len } :=
          ⟨upd_le hd.1 hlen, hd.2⟩
        refine ⟨_, 1, .instr rfl (by rw [← hRlen]; rfl) hd hw₁, le_rfl, by omega, (fun _ => rfl), ⟨fun x hx => ?_, hA.rreg, hA.nmem, hA.rmem⟩,
          ⟨fun x hx _ => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, [],
          (List.append_nil _).symm, (List.append_nil _).symm⟩
        · simp only [upd_apply, hI.len]; split
          · rfl
          · exact hA.nreg x hx
        · exact upd_other _ _ _ (fun e => by rw [e, hr] at hx; cases hx)
      | _ => simp [Instr.notInp] at hri
  | @seq s t c c₁ c₂ k₁ k₂ _ _ ih₁ ih₂ =>
    intro d hA hd hD
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨hrd₁, hrd₂⟩ := or_andR hrd
    obtain ⟨hD₁, hD₂'⟩ := or_andR hD
    obtain ⟨d₁, k₁', e₁, a₁, b₁, c₁', hA₁, hK₁, L₁, o₁, o₁'⟩ := ih₁ hs.1 hrd₁ d hA hd hD₁
    have hD₂ : t.noInp = true ∨ (InDR P W β len W' U tmp rβ rlen d₁) := by
      rcases hD₂' with h | h
      · exact Or.inl h
      · exact Or.inr (hID hK₁ h)
    obtain ⟨d₂, k₂', e₂, a₂, b₂, c₂', hA₂, hK₂, L₂, o₂, o₂'⟩ :=
      ih₂ hs.2 hrd₂ d₁ hA₁ e₁.wb_right hD₂
    refine ⟨d₂, k₁' + k₂', .seq e₁ e₂, by omega, by omega, fun h => ?_, hA₂, hK₁.trans hK₂,
      L₁ ++ L₂, by rw [o₂, o₁, List.append_assoc], by rw [o₂', o₁', List.append_assoc]⟩
    simp only [Stmt.noInp, Bool.and_eq_true] at h; rw [c₁' h.1, c₂' h.2]
  | @ifLtN_true a b t e c c' k ht _ ih =>
    intro d hA hd hD
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', a', b', c'', hA', hK', L, o⟩ :=
      ih hst (or_andR hrd).1 d hA hd (or_andR hD).1
    refine ⟨d', k' + 1, .ifLtN_true (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) e',
      by omega, by omega, fun h => ?_, hA', hK'.weaken fun h' => ?_, L, o⟩
    · simp only [Stmt.noInp, Bool.and_eq_true] at h; rw [c'' h.1]
    · simp only [Stmt.noInp, Bool.and_eq_true] at h'; exact h'.1
  | @ifLtN_false a b t e c c' k ht _ ih =>
    intro d hA hd hD
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', a', b', c'', hA', hK', L, o⟩ :=
      ih hse (or_andR hrd).2 d hA hd (or_andR hD).2
    refine ⟨d', k' + 2, .ifLtN_false (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) e',
      by omega, by omega, fun h => ?_, hA', hK'.weaken fun h' => ?_, L, o⟩
    · simp only [Stmt.noInp, Bool.and_eq_true] at h; rw [c'' h.2]
    · simp only [Stmt.noInp, Bool.and_eq_true] at h'; exact h'.2
  | @ifLtR_true a b t e c c' k ht _ ih =>
    intro d hA hd hD
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', a', b', c'', hA', hK', L, o⟩ :=
      ih hst (or_andR hrd).1 d hA hd (or_andR hD).1
    refine ⟨d', k' + 1, .ifLtR_true (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) e',
      by omega, by omega, fun h => ?_, hA', hK'.weaken fun h' => ?_, L, o⟩
    · simp only [Stmt.noInp, Bool.and_eq_true] at h; rw [c'' h.1]
    · simp only [Stmt.noInp, Bool.and_eq_true] at h'; exact h'.1
  | @ifLtR_false a b t e c c' k ht _ ih =>
    intro d hA hd hD
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', a', b', c'', hA', hK', L, o⟩ :=
      ih hse (or_andR hrd).2 d hA hd (or_andR hD).2
    refine ⟨d', k' + 2, .ifLtR_false (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) e',
      by omega, by omega, fun h => ?_, hA', hK'.weaken fun h' => ?_, L, o⟩
    · simp only [Stmt.noInp, Bool.and_eq_true] at h; rw [c'' h.2]
    · simp only [Stmt.noInp, Bool.and_eq_true] at h'; exact h'.2
  | @whileLtN_false a b body c ht hw =>
    intro d hA hd _
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨ha, hb⟩, _⟩ := hs
    exact ⟨d, 2, .whileLtN_false (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) hd, le_rfl,
      by omega, fun _ => rfl, hA, (Keep.refl _ _ _).toT _ _, [], by simp, by simp⟩
  | @whileLtN_true a b body c c₁ c' k₁ k₂ ht _ _ ih₁ ih₂ =>
    intro d hA hd hD
    have hs' := hs
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs'
    obtain ⟨⟨ha, hb⟩, hsb⟩ := hs'
    obtain ⟨d₁, k₁', e₁, a₁, b₁, c₁', hA₁, hK₁, L₁, o₁, o₁'⟩ := ih₁ hsb hrd d hA hd hD
    have hD₂ : (Stmt.whileLtN a b body).noInp = true ∨ (InDR P W β len W' U tmp rβ rlen d₁) := by
      rcases hD with h | h
      · exact Or.inl h
      · exact Or.inr (hID hK₁ h)
    obtain ⟨d₂, k₂', e₂, a₂, b₂, c₂', hA₂, hK₂, L₂, o₂, o₂'⟩ := ih₂ hs hrd d₁ hA₁ e₁.wb_right hD₂
    refine ⟨d₂, k₁' + 2 + k₂',
      .whileLtN_true (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) e₁ e₂, by omega, by omega,
      fun h => ?_, hA₂, (hK₁.trans hK₂).weaken fun h => ?_, L₁ ++ L₂,
      by rw [o₂, o₁, List.append_assoc], by rw [o₂', o₁', List.append_assoc]⟩
    · have h' : body.noInp = true := h
      rw [c₁' h', c₂' h]
    · simp only [Bool.and_eq_true]; exact ⟨h, h⟩
  | @whileLtR_false a b body c ht hw =>
    intro d hA hd _
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨ha, hb⟩, _⟩ := hs
    exact ⟨d, 2, .whileLtR_false (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) hd, le_rfl,
      by omega, fun _ => rfl, hA, (Keep.refl _ _ _).toT _ _, [], by simp, by simp⟩
  | @whileLtR_true a b body c c₁ c' k₁ k₂ ht _ _ ih₁ ih₂ =>
    intro d hA hd hD
    have hs' := hs
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs'
    obtain ⟨⟨ha, hb⟩, hsb⟩ := hs'
    obtain ⟨d₁, k₁', e₁, a₁, b₁, c₁', hA₁, hK₁, L₁, o₁, o₁'⟩ := ih₁ hsb hrd d hA hd hD
    have hD₂ : (Stmt.whileLtR a b body).noInp = true ∨ (InDR P W β len W' U tmp rβ rlen d₁) := by
      rcases hD with h | h
      · exact Or.inl h
      · exact Or.inr (hID hK₁ h)
    obtain ⟨d₂, k₂', e₂, a₂, b₂, c₂', hA₂, hK₂, L₂, o₂, o₂'⟩ := ih₂ hs hrd d₁ hA₁ e₁.wb_right hD₂
    refine ⟨d₂, k₁' + 2 + k₂',
      .whileLtR_true (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) e₁ e₂, by omega, by omega,
      fun h => ?_, hA₂, (hK₁.trans hK₂).weaken fun h => ?_, L₁ ++ L₂,
      by rw [o₂, o₁, List.append_assoc], by rw [o₂', o₁', List.append_assoc]⟩
    · have h' : body.noInp = true := h
      rw [c₁' h', c₂' h]
    · simp only [Bool.and_eq_true]; exact ⟨h, h⟩

/-- **A printing program as a subroutine, base and length in registers** (`Exec.subcall` for
`toMemR`): the input words at the base held in the register `rβ`, their number in `rlen`. -/
theorem subcallR {P P' : Input} {W : ℕ} {s : Stmt} {c' : Config} {k : ℕ}
    (h : Exec P W s initConfig c' k) {R₀ rp ro tmp rβ rlen W' : ℕ}
    (hs : s.regsOK (fun r => decide (r < R₀)) = true) (hrd : s.noRand = true)
    (hrp : R₀ ≤ rp) (hro : R₀ ≤ ro) (htmp : R₀ ≤ tmp) (hpo : rp ≠ ro) (hpt : rp ≠ tmp)
    (hot : ro ≠ tmp) (hβ : R₀ ≤ rβ) (hl : R₀ ≤ rlen) (hβp : rβ ≠ rp) (hβo : rβ ≠ ro)
    (hβt : rβ ≠ tmp) (hlp : rlen ≠ rp) (hlo : rlen ≠ ro) (hlt : rlen ≠ tmp) {d : Config} (hd : WordsBounded W' d)
    (hz : ∀ r < R₀, d.nreg r = 0) (hzr : ∀ r, r < R₀ ∨ r = rp ∨ r = ro → d.rreg r = 0)
    (hm : ∀ a ≤ d.nreg rp + k, d.nmem a = 0) (hmr : ∀ a ≤ d.nreg rp + k, d.rmem a = 0)
    (h1 : d.nreg ro = 1) (hpW : W < d.nreg rp)
    (hI : InData P (d.nreg rp + k) (d.nreg rβ) (d.nreg rlen) W' d) :
    ∃ d' k', Exec P' W' ((s.outMem rp ro).toMemR tmp rβ rlen) d d' k' ∧ k' ≤ 6 * k ∧
      d'.nreg rp = d.nreg rp + c'.output.length ∧
      (∀ i (hi : i < c'.output.length), d'.nmem (d.nreg rp + i) = c'.output[i]) ∧
      (∀ r, R₀ ≤ r → r ≠ rp → r ≠ tmp → d'.nreg r = d.nreg r) ∧
      (∀ a, d.nreg rp + k < a → d'.nmem a = d.nmem a) ∧ d'.output = d.output := by
  set U : ℕ → Bool := fun r => decide (r < R₀) with hU
  set U' : ℕ → Bool := fun r => decide (r < R₀ ∨ r = rp ∨ r = ro) with hU'
  set W₂ := d.nreg rp + k with hW₂
  have hUp : U rp = false := by simp [hU]; omega
  have hUo : U ro = false := by simp [hU]; omega
  have hU't : U' tmp = false := by simp [hU']; omega
  have hWW : W ≤ W₂ := by omega
  -- the intermediate configuration: `d` cut to `U'` and the memory up to `W₂`
  set d₀ := trunc U' W₂ d with hd₀
  have hA₀ : Agree U W initConfig d₀ := by
    refine ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_⟩
    · have hr' : r < R₀ := by simpa [hU] using hr
      show (if U' r = true then d.nreg r else 0) = 0
      split <;> [exact hz r hr'; rfl]
    · have hr' : r < R₀ := by simpa [hU] using hr
      show (if U' r = true then d.rreg r else 0) = 0
      split <;> [exact hzr r (Or.inl hr'); rfl]
    · show (if a ≤ W₂ then d.nmem a else 0) = 0
      split <;> [exact hm a (by omega); rfl]
    · show (if a ≤ W₂ then d.rmem a else 0) = 0
      split <;> [exact hmr a (by omega); rfl]
  have hU'p : U' rp = true := by simp [hU']
  have hU'o : U' ro = true := by simp [hU']
  have hd₀p : d₀.nreg rp = d.nreg rp := by
    show (if U' rp = true then d.nreg rp else 0) = _; simp only [hU'p, ↓reduceIte]
  have hd₀o : d₀.nreg ro = 1 := by
    show (if U' ro = true then d.nreg ro else 0) = _; simp only [hU'o, ↓reduceIte, h1]
  have hwb₀ : WordsBounded W₂ d₀ := by
    refine ⟨fun r => ?_, fun a => ?_⟩
    · show (if U' r = true then d.nreg r else 0) ≤ W₂
      split
      · rename_i hr
        simp only [hU', decide_eq_true_eq] at hr
        rcases hr with hr | rfl | rfl
        · rw [hz r hr]; omega
        · omega
        · rw [h1]; omega
      · omega
    · show (if a ≤ W₂ then d.nmem a else 0) ≤ W₂
      split
      · rw [hm a (by omega)]; omega
      · omega
  obtain ⟨d₀', k₁, e₁, hk₁, hA₁, L, oL, hL, hK⟩ :=
    outMem_embed h hs hUp hUo hpo hWW d₀ hA₀ hwb₀ hd₀o (by rw [hd₀p]; exact hpW)
      (by rw [hd₀p])
  have hL' : L = c'.output := by simpa [initConfig] using oL.symm
  subst hL'
  -- the input in memory
  have hs' : (s.outMem rp ro).regsOK U' = true := by
    refine Stmt.regsOK_outMem hU'p hU'o ?_
    have hsub : ∀ r, U r = true → U' r = true := fun r hr => by
      simp only [hU, decide_eq_true_eq] at hr; simp [hU', hr]
    exact Stmt.regsOK_mono hsub hs
  have hle : W₂ ≤ W' := by have := hI.le; omega
  obtain ⟨d', k₂, e₂, -, hk₂, -, hA₂, hK₂, L₂, o₂, o₂'⟩ :=
    embedR (P' := P') (tmp := tmp) (rβ := rβ) (rlen := rlen) e₁ hs' hle
      (Or.inl (Stmt.noRand_outMem hrd)) d (agree_trunc U' W₂ d) hd
      (Or.inr ⟨⟨hI, hU't⟩, rfl, rfl, by simp [hU']; omega, by simp [hU']; omega, hβt, hlt⟩)
  have hL₂ : L₂ = [] := by
    have := hK.out; rw [o₂] at this; simpa using this
  subst hL₂
  refine ⟨d', k₂, e₂, by omega, ?_, fun i hi => ?_, fun r hr hrp' hrt => ?_, fun a ha => ?_,
    by simpa using o₂'⟩
  · rw [hA₂.nreg rp hU'p, hK.ptr, hd₀p]
  · rw [hA₂.nmem _ (by omega), ← hd₀p, hK.mem i hi]
  · by_cases hro' : r = ro
    · subst hro'
      rw [hA₂.nreg _ hU'o, hK.nreg _ hUo hrp'.symm.symm, hd₀o, h1]
    · have hr' : U' r = false := by simp [hU']; omega
      exact hK₂.nreg r hr' (fun e => absurd e hrt)
  · exact hK₂.nmem a ha

end Exec

/-! ### Statements without real instructions -/

/-- The instruction touches no real register and no real memory. -/
def _root_.WordRAM.Instr.noReal : Instr → Bool
  | .constR _ _ | .copyR _ _ | .addR _ _ _ | .subR _ _ _ | .mulR _ _ _ | .divR _ _ _
  | .loadR _ _ | .storeR _ _ | .brLtR _ _ _ => false
  | _ => true

namespace Stmt

/-- No real instruction and no real test in the statement. -/
def noReal : Stmt → Bool
  | .skip => true
  | .instr i => i.noReal
  | .seq s t => noReal s && noReal t
  | .ifLtN _ _ t e => noReal t && noReal e
  | .ifLtR _ _ _ _ => false
  | .whileLtN _ _ body => noReal body
  | .whileLtR _ _ _ => false

theorem noReal_outMem {p one : ℕ} : ∀ {s : Stmt}, s.noReal = true → (s.outMem p one).noReal = true
  | .skip, _ => rfl
  | .instr i, h => by cases i <;> first | rfl | exact h
  | .seq s t, h => by
    simp only [noReal, Bool.and_eq_true] at h
    simp only [outMem, noReal, noReal_outMem h.1, noReal_outMem h.2, Bool.and_self]
  | .ifLtN a b t e, h => by
    simp only [noReal, Bool.and_eq_true] at h
    simp only [outMem, noReal, noReal_outMem h.1, noReal_outMem h.2, Bool.and_self]
  | .ifLtR _ _ _ _, h => by simp [noReal] at h
  | .whileLtN a b body, h => by
    simp only [noReal] at h
    simp only [outMem, noReal, noReal_outMem h]
  | .whileLtR _ _ _, h => by simp [noReal] at h

theorem noReal_toMemR {tmp rβ rlen : ℕ} :
    ∀ {s : Stmt}, s.noReal = true → (s.toMemR tmp rβ rlen).noReal = true
  | .skip, _ => rfl
  | .instr i, h => by cases i <;> first | rfl | exact h
  | .seq s t, h => by
    simp only [noReal, Bool.and_eq_true] at h
    simp only [toMemR, noReal, noReal_toMemR h.1, noReal_toMemR h.2, Bool.and_self]
  | .ifLtN a b t e, h => by
    simp only [noReal, Bool.and_eq_true] at h
    simp only [toMemR, noReal, noReal_toMemR h.1, noReal_toMemR h.2, Bool.and_self]
  | .ifLtR _ _ _ _, h => by simp [noReal] at h
  | .whileLtN a b body, h => by
    simp only [noReal] at h
    simp only [toMemR, noReal, noReal_toMemR h]
  | .whileLtR _ _ _, h => by simp [noReal] at h

end Stmt

namespace Exec

variable {P : Input} {W : ℕ}

/-- **A statement without real instructions keeps the real registers and the real memory.** -/
theorem real_of_noReal {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k)
    (hs : s.noReal = true) : c'.rreg = c.rreg ∧ c'.rmem = c.rmem := by
  induction h with
  | skip _ => exact ⟨rfl, rfl⟩
  | @instr ins c c' _ he _ _ =>
    cases ins <;> simp only [Stmt.noReal, Instr.noReal, Bool.false_eq_true] at hs <;>
      simp only [Instr.effect, Option.some.injEq, reduceCtorEq] at he <;> subst he <;>
      exact ⟨rfl, rfl⟩
  | seq _ _ ih₁ ih₂ =>
    simp only [Stmt.noReal, Bool.and_eq_true] at hs
    obtain ⟨a, b⟩ := ih₁ hs.1; obtain ⟨a', b'⟩ := ih₂ hs.2
    exact ⟨a'.trans a, b'.trans b⟩
  | ifLtN_true _ _ ih =>
    simp only [Stmt.noReal, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtN_false _ _ ih =>
    simp only [Stmt.noReal, Bool.and_eq_true] at hs; exact ih hs.2
  | ifLtR_true _ _ _ => simp [Stmt.noReal] at hs
  | ifLtR_false _ _ _ => simp [Stmt.noReal] at hs
  | whileLtN_false _ _ => exact ⟨rfl, rfl⟩
  | whileLtN_true _ _ _ ih₁ ih₂ =>
    have hb : _ = true := hs
    obtain ⟨a, b⟩ := ih₁ hb; obtain ⟨a', b'⟩ := ih₂ hs
    exact ⟨a'.trans a, b'.trans b⟩
  | whileLtR_false _ _ => simp [Stmt.noReal] at hs
  | whileLtR_true _ _ _ _ _ => simp [Stmt.noReal] at hs

end Exec

/-! ### Zeroing registers -/

/-- The registers `< n` set to zero. -/
def zeroRegs (n : ℕ) : Stmt := block ((List.range n).map fun r => .constN r 0)

namespace Exec

variable {P : Input} {W : ℕ}

theorem zeroList (l : List ℕ) {d : Config} (hd : WordsBounded W d) :
    Exec P W (block (l.map fun r => .constN r 0)) d
      { d with nreg := fun r => if r ∈ l then 0 else d.nreg r } l.length := by
  induction l generalizing d with
  | nil => simpa using Exec.block_nil hd
  | cons a l ih =>
    have e₁ := Exec.constN (P := P) hd a 0 (Nat.zero_le _)
    have e₂ := ih e₁.wb_right
    have hc : ({ { d with nreg := upd d.nreg a 0 } with
        nreg := fun r => if r ∈ l then 0 else (upd d.nreg a 0) r } : Config) =
        { d with nreg := fun r => if r ∈ a :: l then 0 else d.nreg r } := by
      show Config.mk _ _ _ _ _ _ = Config.mk _ _ _ _ _ _
      congr 1; funext r
      simp only [upd_apply, List.mem_cons]
      by_cases h1 : r = a <;> by_cases h2 : r ∈ l <;> simp [h1, h2]
    rw [hc] at e₂
    have := Exec.block_cons e₁ e₂
    simpa [Nat.add_comm] using this

/-- **Zeroing the registers `< n`**, in `n` steps. -/
theorem zeroRegs (n : ℕ) {d : Config} (hd : WordsBounded W d) :
    Exec P W (Machine.zeroRegs n) d
      { d with nreg := fun r => if r < n then 0 else d.nreg r } n := by
  have := zeroList (P := P) (List.range n) hd
  simp only [List.mem_range, List.length_range] at this
  exact this

end Exec

end Machine

end WordRAM

namespace PlanarSeparator

open Finset WordRAM WordRAM.Machine

/-- The separator program draws no real word. -/
theorem sepProg_noReal : SepProg.sepProg.noReal = true := by
  decide +kernel

/-- **The separator program as a subroutine, base and length in registers.** -/
def ltSubR (rp ro tmp rβ rlen : ℕ) : Stmt := (SepProg.sepProg.outMem rp ro).toMemR tmp rβ rlen

theorem ltSubR_noReal (rp ro tmp rβ rlen : ℕ) : (ltSubR rp ro tmp rβ rlen).noReal = true :=
  Stmt.noReal_toMemR (Stmt.noReal_outMem sepProg_noReal)

/-- **The separator program run as a subroutine on `sepInput R w di` held in memory**, the base
in the register `rβ` and the number of words in `rlen` (`ltSub_exec` for `toMemR`); the real
registers and the real memory are kept. -/
theorem ltSubR_exec {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G) (hR : R.IsPlane) (w : Fin n → ℕ) (di : G.Dart ≃ Fin m)
    (hdi : ∀ d d' : G.Dart, d.fst < d'.fst → di d < di d') {P' : Input}
    {rp ro tmp rβ rlen W' : ℕ}
    (hrp : 1000 ≤ rp) (hro : 1000 ≤ ro) (htmp : 1000 ≤ tmp) (hpo : rp ≠ ro) (hpt : rp ≠ tmp)
    (hot : ro ≠ tmp) (hβ : 1000 ≤ rβ) (hl : 1000 ≤ rlen) (hβp : rβ ≠ rp) (hβo : rβ ≠ ro)
    (hβt : rβ ≠ tmp) (hlp : rlen ≠ rp) (hlo : rlen ≠ ro) (hlt : rlen ≠ tmp)
    {d : Config} (hd : WordsBounded W' d)
    (hz : ∀ r < 1000, d.nreg r = 0) (hzr : ∀ r, r < 1000 ∨ r = rp ∨ r = ro → d.rreg r = 0)
    (hm : ∀ a ≤ d.nreg rp + (320 * m + 191 * n + 403), d.nmem a = 0)
    (hmr : ∀ a ≤ d.nreg rp + (320 * m + 191 * n + 403), d.rmem a = 0)
    (h1 : d.nreg ro = 1) (hpW : 16 * m + 12 * n + 3 * ∑ v, w v + 22 < d.nreg rp)
    (hI : InData (sepInput R w di) (d.nreg rp + (320 * m + 191 * n + 403)) (d.nreg rβ)
      (d.nreg rlen) W' d) :
    ∃ d' k', Exec P' W' (ltSubR rp ro tmp rβ rlen) d d' k' ∧
      k' ≤ 6 * (320 * m + 191 * n + 403) ∧
      d'.nreg rp = d.nreg rp + (ltOut (sepInput R w di)).length ∧
      (∀ i (hi : i < (ltOut (sepInput R w di)).length),
        d'.nmem (d.nreg rp + i) = (ltOut (sepInput R w di))[i]) ∧
      (∀ r, 1000 ≤ r → r ≠ rp → r ≠ tmp → d'.nreg r = d.nreg r) ∧
      (∀ a, d.nreg rp + (320 * m + 191 * n + 403) < a → d'.nmem a = d.nmem a) ∧
      d'.output = d.output ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem := by
  obtain ⟨c', k, e, hk, hout⟩ := ltProg_exec G R hR w di hdi _ le_rfl
  have hI' : InData (sepInput R w di) (d.nreg rp + k) (d.nreg rβ) (d.nreg rlen) W' d :=
    ⟨by have := hI.lt; omega, by have := hI.le; omega, hI.len,
      fun i hi => hI.mem i (by omega)⟩
  obtain ⟨d', k', e', hk', hp', hmem, hreg, hkeep, ho⟩ := Exec.subcallR (P' := P') e
    sepProg_regsOK sepProg_noRand hrp hro htmp hpo hpt hot hβ hl hβp hβo hβt hlp hlo hlt hd hz
    hzr (fun a ha => hm a (by omega)) (fun a ha => hmr a (by omega)) h1 hpW hI'
  rw [hout] at hp' hmem
  obtain ⟨hr1, hr2⟩ := Exec.real_of_noReal e' (ltSubR_noReal rp ro tmp rβ rlen)
  exact ⟨d', k', e', by omega, hp', hmem, hreg, fun a ha => hkeep a (by omega), ho, hr1, hr2⟩

end PlanarSeparator
