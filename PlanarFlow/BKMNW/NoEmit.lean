module

public import PlanarFlow.BKMNW.MbSep

/-!
# Statements without output instructions keep the output

`sepC_insitu` (and `mbA_exec`, `mbBase_spec`) only say that the run of `encProg ; msep` *extends*
the output (`∃ L, d'.output = d.output ++ L`). A separator program must keep the output
(`SepPSpecX`). Here: `Stmt.noEmit` (no `outN` in the statement), **`Exec.output_eq`** (a run of
such a statement keeps the output), and **`noEmit_encMsep`**: `encProg ; msep` has no `outN`
(by `decide +kernel`), so its runs keep the output.
-/

@[expose] public section

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine PlanarSeparator.MillerProg

/-- No `outN` in the statement. -/
def Stmt.noEmit : Stmt → Bool
  | .skip => true
  | .instr i => !i.isEmit
  | .seq s t => Stmt.noEmit s && Stmt.noEmit t
  | .ifLtN _ _ t e => Stmt.noEmit t && Stmt.noEmit e
  | .ifLtR _ _ t e => Stmt.noEmit t && Stmt.noEmit e
  | .whileLtN _ _ b => Stmt.noEmit b
  | .whileLtR _ _ b => Stmt.noEmit b

lemma effect_output_eq {P : Input} {ins : Instr} {c c' : Config} (he : ins.effect P c = some c')
    (hs : ins.isEmit = false) : c'.output = c.output := by
  cases ins <;> simp only [Instr.effect, Option.some.injEq, Instr.isEmit] at he hs <;>
    first
    | (subst he; rfl)
    | (split at he
       · cases he
       · cases he; rfl)
    | (cases he; done)
    | (cases hs)

/-- **A run of a statement without `outN` keeps the output.** -/
theorem Exec.output_eq {P : Input} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : Stmt.noEmit s = true) : c'.output = c.output := by
  induction h with
  | skip _ => rfl
  | instr _ he _ _ =>
    simp only [Stmt.noEmit, Bool.not_eq_eq_eq_not, Bool.not_true] at hs
    exact effect_output_eq he hs
  | seq _ _ ih1 ih2 =>
    simp only [Stmt.noEmit, Bool.and_eq_true] at hs
    rw [ih2 hs.2, ih1 hs.1]
  | ifLtN_true _ _ ih => simp only [Stmt.noEmit, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtN_false _ _ ih => simp only [Stmt.noEmit, Bool.and_eq_true] at hs; exact ih hs.2
  | ifLtR_true _ _ ih => simp only [Stmt.noEmit, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtR_false _ _ ih => simp only [Stmt.noEmit, Bool.and_eq_true] at hs; exact ih hs.2
  | whileLtN_false _ _ => rfl
  | whileLtN_true _ _ _ ih1 ih2 => rw [ih2 hs, ih1 hs]
  | whileLtR_false _ _ => rfl
  | whileLtR_true _ _ _ ih1 ih2 => rw [ih2 hs, ih1 hs]


/-- The natural register written by an instruction. -/
def insDst : Instr → Option ℕ
  | .inputSize r | .constN r _ | .copyN r _ | .addN r _ _ | .subN r _ _ | .mulN r _ _
  | .divN r _ _ | .modN r _ _ | .loadN r _ | .readIn r _ | .rand r _ => some r
  | _ => none

/-- Does the instruction write real registers or real memory? -/
def insWrR : Instr → Bool
  | .constR .. | .copyR .. | .addR .. | .subR .. | .mulR .. | .divR .. | .loadR .. | .storeR .. =>
    true
  | _ => false

/-- Every natural register written by the statement satisfies `U`; no real register or real
memory is written. -/
def Stmt.wrOK (U : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => !insWrR i && (match insDst i with | some r => U r | none => true)
  | .seq s t => Stmt.wrOK U s && Stmt.wrOK U t
  | .ifLtN _ _ t e => Stmt.wrOK U t && Stmt.wrOK U e
  | .ifLtR _ _ t e => Stmt.wrOK U t && Stmt.wrOK U e
  | .whileLtN _ _ b => Stmt.wrOK U b
  | .whileLtR _ _ b => Stmt.wrOK U b

lemma effect_frame {P : Input} {ins : Instr} {c c' : Config} (he : ins.effect P c = some c')
    (hr : insWrR ins = false) :
    (∀ x, insDst ins ≠ some x → c'.nreg x = c.nreg x) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem := by
  cases ins <;> simp only [Instr.effect, Option.some.injEq, insWrR, insDst] at he hr ⊢ <;>
    first
    | (subst he; refine ⟨fun x hx => ?_, rfl, rfl⟩; simp only [upd_apply]; split_ifs <;> simp_all)
    | (subst he; exact ⟨fun x _ => rfl, rfl, rfl⟩)
    | (cases he; done)
    | (cases hr)

/-- **A run of a statement meeting `wrOK U` keeps the registers outside `U` and the reals.** -/
theorem Exec.wr_frame {P : Input} {W : ℕ} {U : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : Stmt.wrOK U s = true) :
    (∀ x, U x = false → c'.nreg x = c.nreg x) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem := by
  induction h with
  | skip _ => exact ⟨fun _ _ => rfl, rfl, rfl⟩
  | instr _ he _ _ =>
    rename_i ins c₀ c₁
    simp only [Stmt.wrOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hs
    obtain ⟨f1, f2, f3⟩ := effect_frame he hs.1
    refine ⟨fun x hx => f1 x fun hd => ?_, f2, f3⟩
    have := hs.2
    rw [hd] at this
    simp only at this
    rw [this] at hx; cases hx
  | seq _ _ ih1 ih2 =>
    simp only [Stmt.wrOK, Bool.and_eq_true] at hs
    obtain ⟨a1, a2, a3⟩ := ih1 hs.1
    obtain ⟨b1, b2, b3⟩ := ih2 hs.2
    exact ⟨fun x hx => by rw [b1 x hx, a1 x hx], by rw [b2, a2], by rw [b3, a3]⟩
  | ifLtN_true _ _ ih => simp only [Stmt.wrOK, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtN_false _ _ ih => simp only [Stmt.wrOK, Bool.and_eq_true] at hs; exact ih hs.2
  | ifLtR_true _ _ ih => simp only [Stmt.wrOK, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtR_false _ _ ih => simp only [Stmt.wrOK, Bool.and_eq_true] at hs; exact ih hs.2
  | whileLtN_false _ _ => exact ⟨fun _ _ => rfl, rfl, rfl⟩
  | whileLtN_true _ _ _ ih1 ih2 =>
    obtain ⟨a1, a2, a3⟩ := ih1 hs
    obtain ⟨b1, b2, b3⟩ := ih2 hs
    exact ⟨fun x hx => by rw [b1 x hx, a1 x hx], by rw [b2, a2], by rw [b3, a3]⟩
  | whileLtR_false _ _ => exact ⟨fun _ _ => rfl, rfl, rfl⟩
  | whileLtR_true _ _ _ ih1 ih2 =>
    obtain ⟨a1, a2, a3⟩ := ih1 hs
    obtain ⟨b1, b2, b3⟩ := ih2 hs
    exact ⟨fun x hx => by rw [b1 x hx, a1 x hx], by rw [b2, a2], by rw [b3, a3]⟩

/-- **`encProg ; msep` has no output instruction.** -/
theorem noEmit_encMsep : Stmt.noEmit (.seq encProg msep) = true := by decide +kernel

end BKMNW

end PlanarFlow
