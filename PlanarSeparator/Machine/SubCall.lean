module

public import PlanarSeparator.Machine.SepInduced
public import WordRAM.Machine.WordMono

/-!
# Running a printing program as a subroutine: the output into memory

A program that prints its result (`outN`) cannot be called as a subroutine by another program:
the output tape is write-only. `Stmt.outMem p one` replaces every `outN a` by
`nmem[p] := a; p := p + one`: the words are written to memory from the address in the register
`p` on.

* **`WordRAM.Machine.Exec.outMem_embed`**: if `s` (registers in `U`, `p` and `one` outside `U`)
  runs `Exec P W s c c' k` and prints `L`, then from any `d` agreeing with `c` on the registers in
  `U` and on the memory up to `W`, with `one = 1` and `W < p`, `p + k ≤ W'`, the statement
  `s.outMem p one` runs on the same input within `2 k` steps to a `d'` agreeing with `c'`, with
  `L` written at `p, p + 1, …`, `p` advanced by the length of `L`, and everything else above `W`
  and outside `U` kept, nothing printed (`OutK`).

Combined with `WordRAM.Machine.Exec.embed` (the input read from memory, `Stmt.toMem`), this runs
the separator program `ltProg` on an input held in memory and leaves its output in memory.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace WordRAM

namespace Machine

open Instr

namespace Stmt

/-- One instruction with the output written to memory: `outN a` becomes
`nmem[p] := a; p := p + one`. -/
def instrOutMem (p one : ℕ) : Instr → Stmt
  | .outN a => .seq (.instr (.storeN p a)) (.instr (.addN p p one))
  | i => .instr i

/-- The statement with its output written to memory at the pointer `p` (`instrOutMem`). -/
def outMem (p one : ℕ) : Stmt → Stmt
  | .skip => .skip
  | .instr i => instrOutMem p one i
  | .seq s t => .seq (outMem p one s) (outMem p one t)
  | .ifLtN a b t e => .ifLtN a b (outMem p one t) (outMem p one e)
  | .ifLtR a b t e => .ifLtR a b (outMem p one t) (outMem p one e)
  | .whileLtN a b body => .whileLtN a b (outMem p one body)
  | .whileLtR a b body => .whileLtR a b (outMem p one body)

end Stmt

/-- The frame of a run with the output written to memory: the words `L` at `p, p + 1, …` (the
initial value of `p`), `p` advanced by the length of `L`, the other memory cells above `W`, the
registers outside `U` but `p` and the output kept. -/
structure OutK (U : ℕ → Bool) (W p : ℕ) (d d' : Config) (L : List ℕ) : Prop where
  ptr : d'.nreg p = d.nreg p + L.length
  mem : ∀ i (hi : i < L.length), d'.nmem (d.nreg p + i) = L[i]
  keep : ∀ a, W < a → (a < d.nreg p ∨ d.nreg p + L.length ≤ a) → d'.nmem a = d.nmem a
  nreg : ∀ r, U r = false → r ≠ p → d'.nreg r = d.nreg r
  rreg : ∀ r, U r = false → d'.rreg r = d.rreg r
  rmem : ∀ a, W < a → d'.rmem a = d.rmem a
  out : d'.output = d.output

theorem OutK.refl (U : ℕ → Bool) (W p : ℕ) (d : Config) : OutK U W p d d [] :=
  ⟨by simp, fun i hi => by simp at hi, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, rfl⟩

theorem OutK.trans {U : ℕ → Bool} {W p : ℕ} {d d₁ d₂ : Config} {L₁ L₂ : List ℕ}
    (hW : W < d.nreg p) (h₁ : OutK U W p d d₁ L₁) (h₂ : OutK U W p d₁ d₂ L₂) :
    OutK U W p d d₂ (L₁ ++ L₂) where
  ptr := by rw [h₂.ptr, h₁.ptr, List.length_append, Nat.add_assoc]
  mem i hi := by
    rw [List.length_append] at hi
    by_cases hi₁ : i < L₁.length
    · rw [h₂.keep _ (by omega) (Or.inl (by rw [h₁.ptr]; omega)), h₁.mem i hi₁,
        List.getElem_append_left hi₁]
    · have e : d.nreg p + i = d₁.nreg p + (i - L₁.length) := by rw [h₁.ptr]; omega
      rw [e, h₂.mem _ (by omega), List.getElem_append_right (by omega)]
  keep a ha h := by
    rw [List.length_append] at h
    rw [h₂.keep a ha (by rw [h₁.ptr]; omega), h₁.keep a ha (by omega)]
  nreg r hr hrp := by rw [h₂.nreg r hr hrp, h₁.nreg r hr hrp]
  rreg r hr := by rw [h₂.rreg r hr, h₁.rreg r hr]
  rmem a ha := by rw [h₂.rmem a ha, h₁.rmem a ha]
  out := by rw [h₂.out, h₁.out]

/-- An instruction other than `outN` prints nothing. -/
theorem effect_output {P : Input} {ins : Instr} (hno : ∀ a, ins ≠ .outN a) {c c' : Config}
    (he : ins.effect P c = some c') : c'.output = c.output := by
  cases ins <;> simp only [Instr.effect, Option.some.injEq] at he
  all_goals first
    | (subst he; rfl)
    | (cases he; done)
    | exact absurd rfl (hno _)
    | (split at he
       · cases he
       · simp only [Option.some.injEq] at he; subst he; rfl)

namespace Exec

variable {P : Input} {W : ℕ}

/-- **A printing statement with its output written to memory.** -/
theorem outMem_embed {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k)
    {U : ℕ → Bool} {W' p one : ℕ} (hs : s.regsOK U = true) (hp : U p = false)
    (hone : U one = false) (hpo : p ≠ one) (hW : W ≤ W') :
    ∀ d, Agree U W c d → WordsBounded W' d → d.nreg one = 1 → W < d.nreg p →
      d.nreg p + k ≤ W' →
      ∃ d' k', Exec P W' (s.outMem p one) d d' k' ∧ k' ≤ 2 * k ∧ Agree U W c' d' ∧
        ∃ L, c'.output = c.output ++ L ∧ L.length ≤ k ∧ OutK U W p d d' L := by
  induction h with
  | skip hw =>
    intro d hA hd _ _ _
    exact ⟨d, 0, .skip hd, le_rfl, hA, [], by simp, le_rfl, OutK.refl _ _ _ _⟩
  | @instr ins c c' hst he hw hw' =>
    intro d hA hd h1 hpW hk
    have hl : ∀ r ∈ ins.regs, U r = true := fun r hr => List.all_eq_true.1 hs r hr
    by_cases hout : ∃ a, ins = .outN a
    · obtain ⟨a, rfl⟩ := hout
      have ha := hl a (by simp [Instr.regs])
      have hap : a ≠ p := fun e => by rw [e, hp] at ha; cases ha
      simp only [Instr.effect, Option.some.injEq] at he; subst he
      set d₁ : Config := { d with nmem := upd d.nmem (d.nreg p) (d.nreg a) } with hd₁
      have hw₁ : WordsBounded W' d₁ := ⟨hd.1, upd_le hd.2 (WordsBounded.nreg hd a)⟩
      set d₂ : Config := { d₁ with nreg := upd d₁.nreg p (d₁.nreg p + d₁.nreg one) } with hd₂
      have hp₂ : d₂.nreg p = d.nreg p + 1 := by
        rw [hd₂]; simp only [upd_apply, ite_true]; rw [hd₁]; simp only; rw [h1]
      have hw₂ : WordsBounded W' d₂ := ⟨upd_le hw₁.1 (by
        rw [hd₁]; simp only; rw [h1]; omega), hw₁.2⟩
      have e₁ : Exec P W' (.instr (.storeN p a)) d d₁ 1 := .instr (by simp) rfl hd hw₁
      have e₂ : Exec P W' (.instr (.addN p p one)) d₁ d₂ 1 := .instr (by simp) rfl hw₁ hw₂
      refine ⟨d₂, 2, .seq e₁ e₂, by omega, ⟨fun r hr => ?_, hA.rreg, fun x hx => ?_, hA.rmem⟩,
        [c.nreg a], rfl, by simp, ⟨?_, fun i hi => ?_, fun x hx hx' => ?_, fun r hr hrp => ?_,
        fun _ _ => rfl, fun _ _ => rfl, rfl⟩⟩
      · have hrp : r ≠ p := fun e => by rw [e, hp] at hr; cases hr
        rw [hd₂]; simp only [upd_apply, hrp, ite_false]; rw [hd₁]; exact hA.nreg r hr
      · rw [hd₂, hd₁]; simp only [upd_apply, show x ≠ d.nreg p by omega, ite_false]
        exact hA.nmem x hx
      · rw [hp₂]; rfl
      · have hi0 : i = 0 := by simp at hi; omega
        subst hi0
        rw [hd₂, hd₁]; simp only [upd_apply, Nat.add_zero, ite_true, List.getElem_singleton]
        exact hA.nreg a ha
      · simp only [List.length_singleton] at hx'
        rw [hd₂, hd₁]; simp only [upd_apply, show x ≠ d.nreg p by omega, ite_false]
      · rw [hd₂]; simp only [upd_apply, hrp, ite_false]; rfl
    · push Not at hout
      have hso : (Stmt.instr ins).outMem p one = .instr ins := by
        cases ins <;> first | rfl | exact absurd rfl (hout _)
      rw [hso]
      have hco := effect_output hout he
      by_cases hri : ins.notInp = true
      · obtain ⟨d', hed, hA', hK, L, hL, hL'⟩ := effect_embed (P' := P) hs hri (Or.inr rfl) he hw hA
        have hL0 : L = [] := by rw [hco] at hL; simpa using hL
        subst hL0
        have hd' : WordsBounded W' d' := wordsBounded_of_agree hA' hw' hW
          (fun r hr => by rw [hK.nreg r hr]; exact WordsBounded.nreg hd r)
          (fun a ha => by rw [hK.nmem a ha]; exact WordsBounded.nmem hd a)
        refine ⟨d', 1, .instr hst hed hd hd', by omega, hA', [], by simp [hco], by simp,
          ⟨by rw [hK.nreg p hp]; simp, fun i hi => by simp at hi, fun a ha _ => hK.nmem a ha,
            fun r hr _ => hK.nreg r hr, hK.rreg, hK.rmem, by simpa using hL'⟩⟩
      · -- `readIn` and `inputSize`, on the same input
        have kN : ∀ (f : ℕ → ℕ) (i : ℕ) (v : ℕ), U i = true → ∀ r, U r = false →
            upd f i v r = f r :=
          fun f i v hi r hr => upd_other _ _ _ (fun e => by rw [e, hi] at hr; cases hr)
        have aN : ∀ (i : ℕ) (v : ℕ), ∀ r, U r = true → upd d.nreg i v r = upd c.nreg i v r :=
          fun i v r hr => by simp only [upd_apply]; split <;> [rfl; exact hA.nreg r hr]
        cases ins with
        | readIn r a =>
          have hr := hl r (by simp [Instr.regs])
          have ha := hl a (by simp [Instr.regs])
          simp only [Instr.effect, Option.some.injEq] at he; subst he
          set d' : Config := { d with nreg := upd d.nreg r (P.data.getD (d.nreg a) 0) }
          have hA' : Agree U W { c with nreg := upd c.nreg r (P.data.getD (c.nreg a) 0) } d' :=
            ⟨fun x hx => by
              show upd d.nreg r _ x = upd c.nreg r _ x
              rw [hA.nreg a ha]; exact aN r _ x hx, hA.rreg, hA.nmem, hA.rmem⟩
          have hd' : WordsBounded W' d' := wordsBounded_of_agree hA' hw' hW
            (fun x hx => by
              show upd d.nreg r _ x ≤ W'
              rw [kN _ _ _ hr x hx]; exact WordsBounded.nreg hd x)
            (fun x _ => WordsBounded.nmem hd x)
          refine ⟨d', 1, .instr hst rfl hd hd', by omega, hA', [], by simp, by simp,
            ⟨?_, fun i hi => by simp at hi, fun _ _ _ => rfl, fun x hx _ => kN _ _ _ hr x hx,
              fun _ _ => rfl, fun _ _ => rfl, rfl⟩⟩
          show upd d.nreg r _ p = _
          rw [kN _ _ _ hr p hp]; simp
        | inputSize r =>
          have hr := hl r (by simp [Instr.regs])
          simp only [Instr.effect, Option.some.injEq] at he; subst he
          set d' : Config := { d with nreg := upd d.nreg r P.data.length }
          have hA' : Agree U W { c with nreg := upd c.nreg r P.data.length } d' :=
            ⟨fun x hx => aN r _ x hx, hA.rreg, hA.nmem, hA.rmem⟩
          have hd' : WordsBounded W' d' := wordsBounded_of_agree hA' hw' hW
            (fun x hx => by
              show upd d.nreg r _ x ≤ W'
              rw [kN _ _ _ hr x hx]; exact WordsBounded.nreg hd x)
            (fun x _ => WordsBounded.nmem hd x)
          refine ⟨d', 1, .instr hst rfl hd hd', by omega, hA', [], by simp, by simp,
            ⟨?_, fun i hi => by simp at hi, fun _ _ _ => rfl, fun x hx _ => kN _ _ _ hr x hx,
              fun _ _ => rfl, fun _ _ => rfl, rfl⟩⟩
          show upd d.nreg r _ p = _
          rw [kN _ _ _ hr p hp]; simp
        | _ => simp [Instr.notInp] at hri
  | @seq s t c c₁ c₂ k₁ k₂ e₁ e₂ ih₁ ih₂ =>
    intro d hA hd h1 hpW hk
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨d₁, k₁', f₁, hk₁, hA₁, L₁, o₁, hL₁, hK₁⟩ := ih₁ hs.1 d hA hd h1 hpW (by omega)
    have h1' : d₁.nreg one = 1 := by rw [hK₁.nreg one hone (Ne.symm hpo)]; exact h1
    obtain ⟨d₂, k₂', f₂, hk₂, hA₂, L₂, o₂, hL₂, hK₂⟩ := ih₂ hs.2 d₁ hA₁ f₁.wb_right h1'
      (by rw [hK₁.ptr]; omega) (by rw [hK₁.ptr]; omega)
    exact ⟨d₂, k₁' + k₂', .seq f₁ f₂, by omega, hA₂, L₁ ++ L₂,
      by rw [o₂, o₁, List.append_assoc], by simp; omega, hK₁.trans hpW hK₂⟩
  | @ifLtN_true a b t e c c' k ht _ ih =>
    intro d hA hd h1 hpW hk
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', hk', hA', L, o, hL, hK⟩ := ih hst d hA hd h1 hpW (by omega)
    exact ⟨d', k' + 1, .ifLtN_true (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) e',
      by omega, hA', L, o, by omega, hK⟩
  | @ifLtN_false a b t e c c' k ht _ ih =>
    intro d hA hd h1 hpW hk
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', hk', hA', L, o, hL, hK⟩ := ih hse d hA hd h1 hpW (by omega)
    exact ⟨d', k' + 2, .ifLtN_false (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) e',
      by omega, hA', L, o, by omega, hK⟩
  | @ifLtR_true a b t e c c' k ht _ ih =>
    intro d hA hd h1 hpW hk
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', hk', hA', L, o, hL, hK⟩ := ih hst d hA hd h1 hpW (by omega)
    exact ⟨d', k' + 1, .ifLtR_true (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) e',
      by omega, hA', L, o, by omega, hK⟩
  | @ifLtR_false a b t e c c' k ht _ ih =>
    intro d hA hd h1 hpW hk
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', hk', hA', L, o, hL, hK⟩ := ih hse d hA hd h1 hpW (by omega)
    exact ⟨d', k' + 2, .ifLtR_false (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) e',
      by omega, hA', L, o, by omega, hK⟩
  | @whileLtN_false a b body c ht hw =>
    intro d hA hd _ _ _
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨ha, hb⟩, _⟩ := hs
    exact ⟨d, 2, .whileLtN_false (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) hd, by omega,
      hA, [], by simp, by simp, OutK.refl _ _ _ _⟩
  | @whileLtN_true a b body c c₁ c' k₁ k₂ ht _ _ ih₁ ih₂ =>
    intro d hA hd h1 hpW hk
    have hs' := hs
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs'
    obtain ⟨⟨ha, hb⟩, hsb⟩ := hs'
    obtain ⟨d₁, k₁', f₁, hk₁, hA₁, L₁, o₁, hL₁, hK₁⟩ := ih₁ hsb d hA hd h1 hpW (by omega)
    have h1' : d₁.nreg one = 1 := by rw [hK₁.nreg one hone (Ne.symm hpo)]; exact h1
    obtain ⟨d₂, k₂', f₂, hk₂, hA₂, L₂, o₂, hL₂, hK₂⟩ := ih₂ hs d₁ hA₁ f₁.wb_right h1'
      (by rw [hK₁.ptr]; omega) (by rw [hK₁.ptr]; omega)
    exact ⟨d₂, k₁' + 2 + k₂',
      .whileLtN_true (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) f₁ f₂, by omega, hA₂,
      L₁ ++ L₂, by rw [o₂, o₁, List.append_assoc], by simp; omega, hK₁.trans hpW hK₂⟩
  | @whileLtR_false a b body c ht hw =>
    intro d hA hd _ _ _
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨ha, hb⟩, _⟩ := hs
    exact ⟨d, 2, .whileLtR_false (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) hd, by omega,
      hA, [], by simp, by simp, OutK.refl _ _ _ _⟩
  | @whileLtR_true a b body c c₁ c' k₁ k₂ ht _ _ ih₁ ih₂ =>
    intro d hA hd h1 hpW hk
    have hs' := hs
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs'
    obtain ⟨⟨ha, hb⟩, hsb⟩ := hs'
    obtain ⟨d₁, k₁', f₁, hk₁, hA₁, L₁, o₁, hL₁, hK₁⟩ := ih₁ hsb d hA hd h1 hpW (by omega)
    have h1' : d₁.nreg one = 1 := by rw [hK₁.nreg one hone (Ne.symm hpo)]; exact h1
    obtain ⟨d₂, k₂', f₂, hk₂, hA₂, L₂, o₂, hL₂, hK₂⟩ := ih₂ hs d₁ hA₁ f₁.wb_right h1'
      (by rw [hK₁.ptr]; omega) (by rw [hK₁.ptr]; omega)
    exact ⟨d₂, k₁' + 2 + k₂',
      .whileLtR_true (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) f₁ f₂, by omega, hA₂,
      L₁ ++ L₂, by rw [o₂, o₁, List.append_assoc], by simp; omega, hK₁.trans hpW hK₂⟩

end Exec

namespace Stmt

theorem regsOK_mono {U U' : ℕ → Bool} (hsub : ∀ r, U r = true → U' r = true) :
    ∀ {s : Stmt}, s.regsOK U = true → s.regsOK U' = true
  | .skip, _ => rfl
  | .instr i, h => by
    simp only [regsOK, Instr.regsOK, List.all_eq_true] at h ⊢
    exact fun r hr => hsub r (h r hr)
  | .seq s t, h => by
    simp only [regsOK, Bool.and_eq_true] at h ⊢
    exact ⟨regsOK_mono hsub h.1, regsOK_mono hsub h.2⟩
  | .ifLtN a b t e, h => by
    simp only [regsOK, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨hsub _ h.1.1.1, hsub _ h.1.1.2⟩, regsOK_mono hsub h.1.2⟩, regsOK_mono hsub h.2⟩
  | .ifLtR a b t e, h => by
    simp only [regsOK, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨hsub _ h.1.1.1, hsub _ h.1.1.2⟩, regsOK_mono hsub h.1.2⟩, regsOK_mono hsub h.2⟩
  | .whileLtN a b body, h => by
    simp only [regsOK, Bool.and_eq_true] at h ⊢
    exact ⟨⟨hsub _ h.1.1, hsub _ h.1.2⟩, regsOK_mono hsub h.2⟩
  | .whileLtR a b body, h => by
    simp only [regsOK, Bool.and_eq_true] at h ⊢
    exact ⟨⟨hsub _ h.1.1, hsub _ h.1.2⟩, regsOK_mono hsub h.2⟩

theorem regsOK_outMem {U : ℕ → Bool} {p one : ℕ} (hp : U p = true) (hone : U one = true) :
    ∀ {s : Stmt}, s.regsOK U = true → (s.outMem p one).regsOK U = true
  | .skip, _ => rfl
  | .instr i, h => by
    cases i <;> first
      | exact h
      | (simp only [outMem, instrOutMem, regsOK, Instr.regsOK, Instr.regs, List.all_cons,
           List.all_nil, Bool.and_true, Bool.and_eq_true] at h ⊢
         exact ⟨⟨hp, h⟩, hp, hp, hone⟩)
  | .seq s t, h => by
    simp only [regsOK, Bool.and_eq_true, outMem] at h ⊢
    exact ⟨regsOK_outMem hp hone h.1, regsOK_outMem hp hone h.2⟩
  | .ifLtN a b t e, h => by
    simp only [regsOK, Bool.and_eq_true, outMem] at h ⊢
    exact ⟨⟨h.1.1, regsOK_outMem hp hone h.1.2⟩, regsOK_outMem hp hone h.2⟩
  | .ifLtR a b t e, h => by
    simp only [regsOK, Bool.and_eq_true, outMem] at h ⊢
    exact ⟨⟨h.1.1, regsOK_outMem hp hone h.1.2⟩, regsOK_outMem hp hone h.2⟩
  | .whileLtN a b body, h => by
    simp only [regsOK, Bool.and_eq_true, outMem] at h ⊢
    exact ⟨h.1, regsOK_outMem hp hone h.2⟩
  | .whileLtR a b body, h => by
    simp only [regsOK, Bool.and_eq_true, outMem] at h ⊢
    exact ⟨h.1, regsOK_outMem hp hone h.2⟩

theorem noRand_outMem {p one : ℕ} : ∀ {s : Stmt}, s.noRand = true → (s.outMem p one).noRand = true
  | .skip, _ => rfl
  | .instr i, h => by cases i <;> exact h
  | .seq s t, h => by
    simp only [noRand, Bool.and_eq_true, outMem] at h ⊢
    exact ⟨noRand_outMem h.1, noRand_outMem h.2⟩
  | .ifLtN a b t e, h => by
    simp only [noRand, Bool.and_eq_true, outMem] at h ⊢
    exact ⟨noRand_outMem h.1, noRand_outMem h.2⟩
  | .ifLtR a b t e, h => by
    simp only [noRand, Bool.and_eq_true, outMem] at h ⊢
    exact ⟨noRand_outMem h.1, noRand_outMem h.2⟩
  | .whileLtN a b body, h => by
    simp only [noRand, outMem] at h ⊢; exact noRand_outMem h
  | .whileLtR a b body, h => by
    simp only [noRand, outMem] at h ⊢; exact noRand_outMem h

end Stmt

namespace Exec

/-- **A printing statement run as a subroutine on an input held in memory.** Let `s` (registers
`< R₀`, no `rand`) run from the initial configuration on the input `P` with word bound `W` in
`k` steps and print `L`. Let the outer configuration `d` have its registers `< R₀` and its memory
up to `W₂ = p + k` zero (`p` the value of the register `rp > W`), `1` in the register `ro`, and
the words of `P` at `β + i`, `i ≤ W₂` (`W₂ < β`, `β + W₂ ≤ W'`). Then
`(s.outMem rp ro).toMem tmp β len` runs on any input within `6 k` steps, writes `L` at
`p, p + 1, …`, advances `rp` by the length of `L`, keeps the registers `≥ R₀` but `rp`, `tmp`
and the memory above `W₂`, and prints nothing. -/
theorem subcall {P P' : Input} {W : ℕ} {s : Stmt} {c' : Config} {k : ℕ}
    (h : Exec P W s initConfig c' k) {R₀ rp ro tmp β len W' : ℕ}
    (hs : s.regsOK (fun r => decide (r < R₀)) = true) (hrd : s.noRand = true)
    (hrp : R₀ ≤ rp) (hro : R₀ ≤ ro) (htmp : R₀ ≤ tmp) (hpo : rp ≠ ro) (hpt : rp ≠ tmp)
    (hot : ro ≠ tmp) {d : Config} (hd : WordsBounded W' d)
    (hz : ∀ r < R₀, d.nreg r = 0) (hzr : ∀ r, r < R₀ ∨ r = rp ∨ r = ro → d.rreg r = 0)
    (hm : ∀ a ≤ d.nreg rp + k, d.nmem a = 0) (hmr : ∀ a ≤ d.nreg rp + k, d.rmem a = 0)
    (h1 : d.nreg ro = 1) (hpW : W < d.nreg rp)
    (hI : InData P (d.nreg rp + k) β len W' d) :
    ∃ d' k', Exec P' W' ((s.outMem rp ro).toMem tmp β len) d d' k' ∧ k' ≤ 6 * k ∧
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
    embed (P' := P') (tmp := tmp) (β := β) (len := len) e₁ hs' hle
      (Or.inl (Stmt.noRand_outMem hrd)) d (agree_trunc U' W₂ d) hd (Or.inr ⟨hI, hU't⟩)
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

end Machine

end WordRAM
