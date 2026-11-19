module

public import WordRAM

/-!
# Registers a structured program never writes are kept

`Exec.nreg_frame` (`NcLoop.lean`) keeps the registers a statement does not *name*; here the
registers it does not *write* (no instruction with that natural destination `Instr.nDest`):

* `Stmt.nWrites j` (some instruction writes `r j`);
* **`Exec.nreg_keepW`**: a run of a statement with `s.nWrites j = false` keeps `r j`.
-/

@[expose] public section

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-- Does some instruction of the statement write the natural register `j`? -/
def Stmt.nWrites (j : ℕ) : Stmt → Bool
  | .skip => false
  | .instr i => decide (i.nDest = some j)
  | .seq s t => Stmt.nWrites j s || Stmt.nWrites j t
  | .ifLtN _ _ t e => Stmt.nWrites j t || Stmt.nWrites j e
  | .ifLtR _ _ t e => Stmt.nWrites j t || Stmt.nWrites j e
  | .whileLtN _ _ b => Stmt.nWrites j b
  | .whileLtR _ _ b => Stmt.nWrites j b

/-- The natural registers written by the statement. -/
def Stmt.nDests : Stmt → List ℕ
  | .skip => []
  | .instr i => i.nDest.toList
  | .seq s t => Stmt.nDests s ++ Stmt.nDests t
  | .ifLtN _ _ t e => Stmt.nDests t ++ Stmt.nDests e
  | .ifLtR _ _ t e => Stmt.nDests t ++ Stmt.nDests e
  | .whileLtN _ _ b => Stmt.nDests b
  | .whileLtR _ _ b => Stmt.nDests b

lemma nWrites_eq_false_of {j : ℕ} (s : Stmt) (h : j ∉ Stmt.nDests s) :
    Stmt.nWrites j s = false := by
  induction s with
  | skip => rfl
  | instr i =>
    simp only [Stmt.nDests] at h
    simp only [Stmt.nWrites, decide_eq_false_iff_not]
    intro e; rw [e] at h; simp at h
  | seq s t ihs iht =>
    simp only [Stmt.nDests, List.mem_append, not_or] at h
    simp only [Stmt.nWrites, ihs h.1, iht h.2, Bool.or_false]
  | ifLtN _ _ t e iht ihe =>
    simp only [Stmt.nDests, List.mem_append, not_or] at h
    simp only [Stmt.nWrites, iht h.1, ihe h.2, Bool.or_false]
  | ifLtR _ _ t e iht ihe =>
    simp only [Stmt.nDests, List.mem_append, not_or] at h
    simp only [Stmt.nWrites, iht h.1, ihe h.2, Bool.or_false]
  | whileLtN _ _ b ih => simp only [Stmt.nDests] at h; exact ih h
  | whileLtR _ _ b ih => simp only [Stmt.nDests] at h; exact ih h

lemma effect_nreg_keep {P : Input} {ins : Instr} {c c' : Config} (h : ins.effect P c = some c')
    {j : ℕ} (hj : ins.nDest ≠ some j) : c'.nreg j = c.nreg j := by
  cases ins <;> simp only [Instr.effect, Option.some.injEq] at h <;>
    (try split at h) <;> (try (cases h; simp_all [Instr.nDest, upd, Ne.symm])) <;>
    (try exact absurd h (by simp))

/-- **A run keeps every natural register its statement never writes.** -/
theorem Exec.nreg_keepW {P : Input} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) {j : ℕ} (hs : Stmt.nWrites j s = false) : c'.nreg j = c.nreg j := by
  induction h with
  | skip => rfl
  | instr _ he _ _ =>
    exact effect_nreg_keep he (by simp only [Stmt.nWrites, decide_eq_false_iff_not] at hs; exact hs)
  | seq _ _ ih₁ ih₂ =>
    simp only [Stmt.nWrites, Bool.or_eq_false_iff] at hs
    rw [ih₂ hs.2, ih₁ hs.1]
  | ifLtN_true _ _ ih =>
    simp only [Stmt.nWrites, Bool.or_eq_false_iff] at hs; exact ih hs.1
  | ifLtN_false _ _ ih =>
    simp only [Stmt.nWrites, Bool.or_eq_false_iff] at hs; exact ih hs.2
  | ifLtR_true _ _ ih =>
    simp only [Stmt.nWrites, Bool.or_eq_false_iff] at hs; exact ih hs.1
  | ifLtR_false _ _ ih =>
    simp only [Stmt.nWrites, Bool.or_eq_false_iff] at hs; exact ih hs.2
  | whileLtN_false _ _ => rfl
  | whileLtN_true _ _ _ ih₁ ih₂ =>
    rw [ih₂ hs, ih₁ hs]
  | whileLtR_false _ _ => rfl
  | whileLtR_true _ _ _ ih₁ ih₂ =>
    rw [ih₂ hs, ih₁ hs]

/-- **The registers of the driver and of the step are never written** if no destination of the
statement lies in `3000 … 3012` or `6800 … 6819`. -/
theorem sreg_keepW {P : Input} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k)
    (hs : (Stmt.nDests s).all (fun x => decide (x < 3000 ∨ (3012 < x ∧ x < 6800) ∨ 6819 < x)) =
      true) :
    ∀ r, (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) → c'.nreg r = c.nreg r := by
  intro r hr
  refine Exec.nreg_keepW h (nWrites_eq_false_of _ fun hm => ?_)
  have := List.all_eq_true.1 hs r hm
  simp only [decide_eq_true_eq] at this
  omega


end BKMNW

end PlanarFlow
