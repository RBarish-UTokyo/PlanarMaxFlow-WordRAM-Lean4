module

public import WordRAM

/-!
# Renaming the natural registers of a program

For a permutation `π` of `ℕ`, `rnS π s` is the statement `s` with every natural register `r` it
names replaced by `π r` (destinations, operands, address registers of the real loads and stores,
tests); the real registers are unchanged. `rnC π c` is the configuration `c` with its natural
register file permuted (`(rnC π c).nreg (π r) = c.nreg r`).

* **`rn_exec`**: a run of `s` from `c` to `c'` in `k` steps is a run of `rnS π s` from `rnC π c`
  to `rnC π c'` in `k` steps (same word bound; the memory, the reals and the output are the same).

This lets a program whose registers clash with others (e.g. the encoders of the one-face
instances, registers `1400 … 2547`, against the residues of the real registers kept in
`1000 … 1999` by `ModNat.Sim`) run on other registers, with all its theorems.
-/

@[expose] public section

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-- An instruction with its natural registers renamed. -/
def rnI (π : Equiv.Perm ℕ) : Instr → Instr
  | .inputSize r => .inputSize (π r)
  | .constN r k => .constN (π r) k
  | .copyN r a => .copyN (π r) (π a)
  | .addN r a b => .addN (π r) (π a) (π b)
  | .subN r a b => .subN (π r) (π a) (π b)
  | .mulN r a b => .mulN (π r) (π a) (π b)
  | .divN r a b => .divN (π r) (π a) (π b)
  | .modN r a b => .modN (π r) (π a) (π b)
  | .loadN r a => .loadN (π r) (π a)
  | .storeN a r => .storeN (π a) (π r)
  | .loadR r a => .loadR r (π a)
  | .storeR a r => .storeR (π a) r
  | .readIn r a => .readIn (π r) (π a)
  | .rand r a => .rand (π r) (π a)
  | .outN a => .outN (π a)
  | .brLtN a b l => .brLtN (π a) (π b) l
  | .constR r z => .constR r z
  | .copyR r a => .copyR r a
  | .addR r a b => .addR r a b
  | .subR r a b => .subR r a b
  | .mulR r a b => .mulR r a b
  | .divR r a b => .divR r a b
  | .halt => .halt
  | .jump l => .jump l
  | .brLtR a b l => .brLtR a b l

/-- A statement with its natural registers renamed. -/
def rnS (π : Equiv.Perm ℕ) : Stmt → Stmt
  | .skip => .skip
  | .instr i => .instr (rnI π i)
  | .seq s t => .seq (rnS π s) (rnS π t)
  | .ifLtN a b t e => .ifLtN (π a) (π b) (rnS π t) (rnS π e)
  | .ifLtR a b t e => .ifLtR a b (rnS π t) (rnS π e)
  | .whileLtN a b body => .whileLtN (π a) (π b) (rnS π body)
  | .whileLtR a b body => .whileLtR a b (rnS π body)

/-- A configuration with its natural register file permuted. -/
def rnC (π : Equiv.Perm ℕ) (c : Config) : Config :=
  { c with nreg := fun r => c.nreg (π.symm r) }

@[simp] theorem rnC_nreg (π : Equiv.Perm ℕ) (c : Config) (r : ℕ) :
    (rnC π c).nreg (π r) = c.nreg r := by
  simp [rnC]

@[simp] theorem rnC_nmem (π : Equiv.Perm ℕ) (c : Config) : (rnC π c).nmem = c.nmem := rfl
@[simp] theorem rnC_rreg (π : Equiv.Perm ℕ) (c : Config) : (rnC π c).rreg = c.rreg := rfl
@[simp] theorem rnC_rmem (π : Equiv.Perm ℕ) (c : Config) : (rnC π c).rmem = c.rmem := rfl
@[simp] theorem rnC_output (π : Equiv.Perm ℕ) (c : Config) : (rnC π c).output = c.output := rfl

theorem rnC_nreg' (π : Equiv.Perm ℕ) (c : Config) (r : ℕ) :
    (rnC π c).nreg r = c.nreg (π.symm r) := rfl

theorem rn_upd (π : Equiv.Perm ℕ) (f : ℕ → ℕ) (r v : ℕ) :
    upd (fun x => f (π.symm x)) (π r) v = fun x => upd f r v (π.symm x) := by
  funext x
  simp only [upd]
  by_cases h : x = π r
  · subst h; simp
  · have : π.symm x ≠ r := fun e => h (by rw [← e]; simp)
    simp [h, this]

theorem rn_wb {π : Equiv.Perm ℕ} {W : ℕ} {c : Config} (h : WordsBounded W c) :
    WordsBounded W (rnC π c) :=
  ⟨fun _ => h.1 _, fun a => h.2 a⟩

theorem rn_straight (π : Equiv.Perm ℕ) {i : Instr} (h : i.IsStraight) : (rnI π i).IsStraight := by
  cases i <;> simp [rnI, Instr.IsStraight, Instr.isControl] at h ⊢

theorem rn_effect (π : Equiv.Perm ℕ) (P : Input) (i : Instr) (c : Config) :
    (rnI π i).effect P (rnC π c) = (i.effect P c).map (rnC π) := by
  cases i <;> simp only [rnI, Instr.effect, Option.map_some, Option.map_none, rnC,
    rn_upd] <;> (try split_ifs) <;> simp_all [rnC]

/-- **A run with the natural registers renamed.** -/
theorem rn_exec {P : Input} {W : ℕ} (π : Equiv.Perm ℕ) {s : Stmt} {c c' : Config} {k : ℕ}
    (e : Exec P W s c c' k) : Exec P W (rnS π s) (rnC π c) (rnC π c') k := by
  induction e with
  | skip hw => exact .skip (rn_wb hw)
  | instr hs he hw hw' =>
    refine .instr (rn_straight π hs) ?_ (rn_wb hw) (rn_wb hw')
    rw [rn_effect, he]; rfl
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifLtN_true h _ ih => exact .ifLtN_true (by simpa using h) ih
  | ifLtN_false h _ ih => exact .ifLtN_false (by simpa using h) ih
  | ifLtR_true h _ ih => exact .ifLtR_true h ih
  | ifLtR_false h _ ih => exact .ifLtR_false h ih
  | whileLtN_false h hw => exact .whileLtN_false (by simpa using h) (rn_wb hw)
  | whileLtN_true h _ _ ih₁ ih₂ => exact .whileLtN_true (by simpa using h) ih₁ ih₂
  | whileLtR_false h hw => exact .whileLtR_false h (rn_wb hw)
  | whileLtR_true h _ _ ih₁ ih₂ => exact .whileLtR_true h ih₁ ih₂

/-- Renaming back. -/
theorem rnC_symm (π : Equiv.Perm ℕ) (c : Config) : rnC π.symm (rnC π c) = c := by
  cases c; simp [rnC]

end NegSSSP

end PlanarFlow
