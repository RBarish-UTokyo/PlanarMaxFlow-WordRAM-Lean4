module

public import WordRAM.Machine.RealsModNat

/-!
# Bounded comparisons and stores, by an abstract interpretation

`WordRAM.Machine.ModNat.ExecCmp.toNat` simulates the exact integer reals modulo `M` and needs
only a bound `|x - y| ≤ H` at every executed real comparison. This file gives a tool to obtain
it for statements whose compared reals are computed, inside the statement, from a few loads:

* `MemB W B c`: every real memory cell at an address `≤ W` has absolute value at most `B`.
* `ExecG P W B H s c c' k`: `Exec` with, at every executed real test, the bound `≤ H` on the
  difference (as in `ExecCmp`), and at every executed `storeR`, the bound `≤ B` on the stored
  real. Such a run keeps `MemB W B` (`ExecG.mem`), and gives `ExecCmp` (`ExecG.toCmp`).
* `Good P W B H s c`: every execution of `s` from `c`, started with `MemB W B`, is such a run.
  The rules `Good.seq`, `Good.ifLtN`, `Good.ifLtR`, `Good.whileLtN`, `Good.whileLtR` and their
  variants compose it along the existing realization lemmas (with `Exec.det`).
* **The abstract interpretation** `absS m n s A`: the abstract state `A` (a list of pairs) bounds
  some real registers `r` by `j B` (`RegA`); a load gives `1`, a sum or difference adds, a copy
  copies, a constant `0` gives `0`; a store needs `≤ 1`, a test `ifLtR a b` needs the sum of the
  two bounds `≤ m`; loops are handled by a fixed point (joins, at most `n` rounds). If
  `absS m n s A = some A'`, then `s` is `Good` with `H = m B` from every configuration bounded by
  `A` (`good_abs`), and every run ends bounded by `A'` (`absS_sound`). The check is decidable and
  run by the kernel on concrete statements.
-/

@[expose] public section

namespace PlanarFlow

namespace Monge

namespace CmpAbs

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Machine.ModNat

/-! ### Bounded memory, bounded stores -/

/-- Every real memory cell at an address `≤ W` is bounded by `B`. -/
def MemB (W B : ℕ) (c : Config) : Prop := ∀ a ≤ W, |c.rmem a| ≤ (B : ℝ)

/-- The bound of a stored real. -/
def StOK (B : ℕ) : Instr → Config → Prop
  | .storeR _ r, c => |c.rreg r| ≤ (B : ℝ)
  | _, _ => True

/-- `Exec` with bounded real tests (by `H`) and bounded stored reals (by `B`). -/
inductive ExecG (P : Input) (W B H : ℕ) : Stmt → Config → Config → ℕ → Prop
  | skip {c : Config} : WordsBounded W c → ExecG P W B H .skip c c 0
  | instr {ins : Instr} {c c' : Config} : ins.IsStraight → ins.effect P c = some c' →
      WordsBounded W c → WordsBounded W c' → StOK B ins c → ExecG P W B H (.instr ins) c c' 1
  | seq {s t : Stmt} {c c₁ c₂ : Config} {k₁ k₂ : ℕ} :
      ExecG P W B H s c c₁ k₁ → ExecG P W B H t c₁ c₂ k₂ → ExecG P W B H (.seq s t) c c₂ (k₁ + k₂)
  | ifLtN_true {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : c.nreg a < c.nreg b →
      ExecG P W B H t c c' k → ExecG P W B H (.ifLtN a b t e) c c' (k + 1)
  | ifLtN_false {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : ¬ c.nreg a < c.nreg b →
      ExecG P W B H e c c' k → ExecG P W B H (.ifLtN a b t e) c c' (k + 2)
  | ifLtR_true {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} :
      |c.rreg a - c.rreg b| ≤ H → c.rreg a < c.rreg b →
      ExecG P W B H t c c' k → ExecG P W B H (.ifLtR a b t e) c c' (k + 1)
  | ifLtR_false {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} :
      |c.rreg a - c.rreg b| ≤ H → ¬ c.rreg a < c.rreg b →
      ExecG P W B H e c c' k → ExecG P W B H (.ifLtR a b t e) c c' (k + 2)
  | whileLtN_false {a b : ℕ} {body : Stmt} {c : Config} : ¬ c.nreg a < c.nreg b →
      WordsBounded W c → ExecG P W B H (.whileLtN a b body) c c 2
  | whileLtN_true {a b : ℕ} {body : Stmt} {c c₁ c' : Config} {k₁ k₂ : ℕ} : c.nreg a < c.nreg b →
      ExecG P W B H body c c₁ k₁ → ExecG P W B H (.whileLtN a b body) c₁ c' k₂ →
      ExecG P W B H (.whileLtN a b body) c c' (k₁ + 2 + k₂)
  | whileLtR_false {a b : ℕ} {body : Stmt} {c : Config} :
      |c.rreg a - c.rreg b| ≤ H → ¬ c.rreg a < c.rreg b →
      WordsBounded W c → ExecG P W B H (.whileLtR a b body) c c 2
  | whileLtR_true {a b : ℕ} {body : Stmt} {c c₁ c' : Config} {k₁ k₂ : ℕ} :
      |c.rreg a - c.rreg b| ≤ H → c.rreg a < c.rreg b →
      ExecG P W B H body c c₁ k₁ → ExecG P W B H (.whileLtR a b body) c₁ c' k₂ →
      ExecG P W B H (.whileLtR a b body) c c' (k₁ + 2 + k₂)

variable {P : Input} {W B H : ℕ}

/-- Forget the store bounds. -/
theorem ExecG.toCmp {s : Stmt} {c c' : Config} {k : ℕ} (h : ExecG P W B H s c c' k) :
    ExecCmp P W H s c c' k := by
  induction h with
  | skip hw => exact .skip hw
  | instr hs he hw hw' _ => exact .instr hs he hw hw'
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifLtN_true ht _ ih => exact .ifLtN_true ht ih
  | ifLtN_false ht _ ih => exact .ifLtN_false ht ih
  | ifLtR_true hb ht _ ih => exact .ifLtR_true hb ht ih
  | ifLtR_false hb ht _ ih => exact .ifLtR_false hb ht ih
  | whileLtN_false ht hw => exact .whileLtN_false ht hw
  | whileLtN_true ht _ _ ih₁ ih₂ => exact .whileLtN_true ht ih₁ ih₂
  | whileLtR_false hb ht hw => exact .whileLtR_false hb ht hw
  | whileLtR_true hb ht _ _ ih₁ ih₂ => exact .whileLtR_true hb ht ih₁ ih₂

/-- One instruction with a bounded store keeps the bound of the memory. -/
theorem instr_mem {ins : Instr} {c c' : Config} (hs : ins.IsStraight)
    (he : ins.effect P c = some c') (_hw : WordsBounded W c) (hst : StOK B ins c)
    (hM : MemB W B c) : MemB W B c' := by
  cases ins
  all_goals first
    | (simp at hs; done)
    | (simp only [Instr.effect, Option.some.injEq] at he; subst he; exact hM)
    | skip
  case storeR a r =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    intro x hx
    simp only [upd_apply]
    split_ifs
    · exact hst
    · exact hM x hx
  case divR r a b =>
    simp only [Instr.effect] at he
    split_ifs at he
    simp only [Option.some.injEq] at he; subst he; exact hM

/-- A run with bounded stores keeps the bound of the memory. -/
theorem ExecG.mem {s : Stmt} {c c' : Config} {k : ℕ} (h : ExecG P W B H s c c' k)
    (hM : MemB W B c) : MemB W B c' := by
  induction h with
  | skip => exact hM
  | instr hs he hw _ hst => exact instr_mem hs he hw hst hM
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hM)
  | ifLtN_true _ _ ih => exact ih hM
  | ifLtN_false _ _ ih => exact ih hM
  | ifLtR_true _ _ _ ih => exact ih hM
  | ifLtR_false _ _ _ ih => exact ih hM
  | whileLtN_false => exact hM
  | whileLtN_true _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hM)
  | whileLtR_false => exact hM
  | whileLtR_true _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hM)

theorem ExecG.toExec {s : Stmt} {c c' : Config} {k : ℕ} (h : ExecG P W B H s c c' k) :
    Exec P W s c c' k := h.toCmp.toExec

/-! ### Good statements -/

/-- Every execution of `s` from `c`, started with the memory bounded by `B`, has bounded tests
and bounded stores. -/
def Good (P : Input) (W B H : ℕ) (s : Stmt) (c : Config) : Prop :=
  ∀ c' k, Exec P W s c c' k → MemB W B c → ExecG P W B H s c c' k

theorem Good.toCmp {s : Stmt} {c : Config} (h : Good P W B H s c) (hM : MemB W B c) :
    CmpOK P W H s c := fun c' k e => (h c' k e hM).toCmp

theorem Good.mem {s : Stmt} {c c' : Config} {k : ℕ} (h : Good P W B H s c)
    (e : Exec P W s c c' k) (hM : MemB W B c) : MemB W B c' := (h c' k e hM).mem hM

theorem Good.seq {s t : Stmt} {c : Config} (hs : Good P W B H s c)
    (ht : ∀ c₁ k₁, Exec P W s c c₁ k₁ → Good P W B H t c₁) : Good P W B H (.seq s t) c := by
  intro c' k e hM
  cases e with
  | seq e₁ e₂ =>
    have g₁ := hs _ _ e₁ hM
    exact .seq g₁ (ht _ _ e₁ _ _ e₂ (g₁.mem hM))

theorem Good.ifLtN {a b : ℕ} {t e : Stmt} {c : Config}
    (ht : c.nreg a < c.nreg b → Good P W B H t c) (he : ¬ c.nreg a < c.nreg b → Good P W B H e c) :
    Good P W B H (.ifLtN a b t e) c := by
  intro c' k ex hM
  cases ex with
  | ifLtN_true h e₁ => exact .ifLtN_true h (ht h _ _ e₁ hM)
  | ifLtN_false h e₁ => exact .ifLtN_false h (he h _ _ e₁ hM)

theorem Good.ifLtR {a b : ℕ} {t e : Stmt} {c : Config}
    (hb : MemB W B c → |c.rreg a - c.rreg b| ≤ H)
    (ht : c.rreg a < c.rreg b → Good P W B H t c) (he : ¬ c.rreg a < c.rreg b → Good P W B H e c) :
    Good P W B H (.ifLtR a b t e) c := by
  intro c' k ex hM
  cases ex with
  | ifLtR_true h e₁ => exact .ifLtR_true (hb hM) h (ht h _ _ e₁ hM)
  | ifLtR_false h e₁ => exact .ifLtR_false (hb hM) h (he h _ _ e₁ hM)

theorem Good.whileLtN {a b : ℕ} {body : Stmt} (I : Config → Prop)
    (hI : ∀ c, I c → c.nreg a < c.nreg b →
      Good P W B H body c ∧ ∀ c₁ k, Exec P W body c c₁ k → I c₁)
    {c : Config} (hc : I c) : Good P W B H (.whileLtN a b body) c := by
  intro c' k ex hM
  generalize hs : Stmt.whileLtN a b body = s at ex
  induction ex with
  | whileLtN_false h hw =>
    cases hs; exact .whileLtN_false h hw
  | whileLtN_true h e₁ _ _ ih₂ =>
    cases hs
    obtain ⟨hb, hp⟩ := hI _ hc h
    have g₁ := hb _ _ e₁ hM
    exact .whileLtN_true h g₁ (ih₂ (hp _ _ e₁) (g₁.mem hM) rfl)
  | _ => cases hs

theorem Good.whileLtR {a b : ℕ} {body : Stmt} (I : Config → Prop)
    (hB : ∀ c, I c → MemB W B c → |c.rreg a - c.rreg b| ≤ H)
    (hI : ∀ c, I c → c.rreg a < c.rreg b →
      Good P W B H body c ∧ ∀ c₁ k, Exec P W body c c₁ k → I c₁)
    {c : Config} (hc : I c) : Good P W B H (.whileLtR a b body) c := by
  intro c' k ex hM
  generalize hs : Stmt.whileLtR a b body = s at ex
  induction ex with
  | whileLtR_false h hw =>
    cases hs; exact .whileLtR_false (hB _ hc hM) h hw
  | whileLtR_true h e₁ _ _ ih₂ =>
    cases hs
    obtain ⟨hb, hp⟩ := hI _ hc h
    have g₁ := hb _ _ e₁ hM
    exact .whileLtR_true (hB _ hc hM) h g₁ (ih₂ (hp _ _ e₁) (g₁.mem hM) rfl)
  | _ => cases hs

/-- A single instruction. -/
theorem Good.instr {i : Instr} {c : Config} (h : MemB W B c → StOK B i c) :
    Good P W B H (.instr i) c := by
  intro c' k ex hM
  cases ex with
  | instr hs he hw hw' => exact .instr hs he hw hw' (h hM)

/-- `skip`. -/
theorem Good.skip {c : Config} : Good P W B H .skip c := by
  intro c' k ex _
  cases ex with
  | skip hw => exact .skip hw

/-- Sequencing with a realization lemma for the first statement (the pattern of `spec_use`). -/
theorem good_seq_use {s t : Stmt} {c : Config} {K : ℕ} {post : Config → Prop}
    (h : ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ post c') (hs : Good P W B H s c)
    (ht : ∀ c' k, k ≤ K → WordsBounded W c' → post c' → Good P W B H t c') :
    Good P W B H (.seq s t) c := by
  refine hs.seq fun c₁ k₁ e₁ => ?_
  obtain ⟨c', k, e, hk, hp⟩ := h
  obtain ⟨rfl, rfl⟩ := Exec.det e e₁
  exact ht _ _ hk e.wb_right hp

/-- Sequencing with a realization lemma for the first statement, any postcondition. -/
theorem good_seq_post {s t : Stmt} {c : Config} {post : Config → ℕ → Prop}
    (h : ∃ c' k, Exec P W s c c' k ∧ post c' k) (hs : Good P W B H s c)
    (ht : ∀ c' k, Exec P W s c c' k → post c' k → Good P W B H t c') :
    Good P W B H (.seq s t) c := by
  refine hs.seq fun c₁ k₁ e₁ => ?_
  obtain ⟨c', k, e, hp⟩ := h
  obtain ⟨rfl, rfl⟩ := Exec.det e e₁
  exact ht _ _ e hp

/-- Sequencing with an explicit run of the first statement (the pattern of `exec_block`). -/
theorem good_seq_ex {s t : Stmt} {c : Config} (hs : Good P W B H s c)
    (h : ∃ c₁ k₁, Exec P W s c c₁ k₁ ∧ Good P W B H t c₁) : Good P W B H (.seq s t) c := by
  refine hs.seq fun c₁ k₁ e₁ => ?_
  obtain ⟨c₂, k₂, e₂, hg⟩ := h
  obtain ⟨rfl, rfl⟩ := Exec.det e₂ e₁
  exact hg

/-- Sequencing with one instruction first (the pattern of `spec_instr`). -/
theorem good_seq_instr {i : Instr} {t : Stmt} {c c₁ : Config} (h₁ : Exec P W (.instr i) c c₁ 1)
    (hst : MemB W B c → StOK B i c) (h : WordsBounded W c₁ → Good P W B H t c₁) :
    Good P W B H (.seq (.instr i) t) c :=
  good_seq_ex (Good.instr hst) ⟨c₁, 1, h₁, h h₁.wb_right⟩

/-- A block: its first instruction, without a bounded store to check, then the rest from the
explicit next configuration. -/
theorem good_cons {i : Instr} {l : List Instr} {c : Config} (hi : MemB W B c → StOK B i c)
    (h : ∀ c₁, i.effect P c = some c₁ → Good P W B H (block l) c₁) :
    Good P W B H (block (i :: l)) c :=
  Good.seq (Good.instr hi) fun c₁ _ e₁ => by
    cases e₁ with
    | instr _ he _ _ => exact h c₁ he

theorem good_ifLtN_true {a b : ℕ} {t e : Stmt} {c : Config} (h : c.nreg a < c.nreg b)
    (ht : Good P W B H t c) : Good P W B H (.ifLtN a b t e) c :=
  Good.ifLtN (fun _ => ht) (fun h' => absurd h h')

theorem good_ifLtN_false {a b : ℕ} {t e : Stmt} {c : Config} (h : ¬ c.nreg a < c.nreg b)
    (he : Good P W B H e c) : Good P W B H (.ifLtN a b t e) c :=
  Good.ifLtN (fun h' => absurd h' h) (fun _ => he)

/-- The loop rule with a ghost invariant, from the realization lemma of the body. -/
theorem good_whileLtN_ghost {α : Type} {a b : ℕ} {body : Stmt} (I : α → Config → Prop)
    (hbody : ∀ g c, I g c → c.nreg a < c.nreg b →
      Good P W B H body c ∧ ∃ c' k, Exec P W body c c' k ∧ ∃ g', I g' c')
    {g : α} {c : Config} (hc : I g c) : Good P W B H (.whileLtN a b body) c := by
  refine Good.whileLtN (fun c => ∃ g, I g c) (fun c ⟨g, hg⟩ ht => ⟨(hbody g c hg ht).1,
    fun c₁ k e => ?_⟩) ⟨g, hc⟩
  obtain ⟨c', k', e', hg'⟩ := (hbody g c hg ht).2
  obtain ⟨rfl, rfl⟩ := Exec.det e' e
  exact hg'

/-- Monotonicity in the comparison bound. -/
theorem ExecG.mono_H {s : Stmt} {c c' : Config} {k H' : ℕ} (h : ExecG P W B H s c c' k)
    (hH : H ≤ H') : ExecG P W B H' s c c' k := by
  have hH' : (H : ℝ) ≤ H' := by exact_mod_cast hH
  induction h with
  | skip hw => exact .skip hw
  | instr hs he hw hw' hst => exact .instr hs he hw hw' hst
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifLtN_true ht _ ih => exact .ifLtN_true ht ih
  | ifLtN_false ht _ ih => exact .ifLtN_false ht ih
  | ifLtR_true hb ht _ ih => exact .ifLtR_true (hb.trans hH') ht ih
  | ifLtR_false hb ht _ ih => exact .ifLtR_false (hb.trans hH') ht ih
  | whileLtN_false ht hw => exact .whileLtN_false ht hw
  | whileLtN_true ht _ _ ih₁ ih₂ => exact .whileLtN_true ht ih₁ ih₂
  | whileLtR_false hb ht hw => exact .whileLtR_false (hb.trans hH') ht hw
  | whileLtR_true hb ht _ _ ih₁ ih₂ => exact .whileLtR_true (hb.trans hH') ht ih₁ ih₂

/-! ### The abstract states -/

/-- An abstract state: the pairs `(r, j)` bound the real register `r` by `j B` (the first pair
of `r` counts; a register without a pair is not bounded). -/
abbrev AS : Type := List (ℕ × ℕ)

/-- The bound of a register. -/
def get : AS → ℕ → Option ℕ
  | [], _ => none
  | (a, j) :: A, r => if a = r then some j else get A r

/-- Forget a register. -/
def del : AS → ℕ → AS
  | [], _ => []
  | (a, j) :: A, r => if a = r then del A r else (a, j) :: del A r

/-- Set the bound of a register. -/
def put (A : AS) (r : ℕ) : Option ℕ → AS
  | some j => (r, j) :: del A r
  | none => del A r

/-- The registers bounded in both states, by the larger bound. -/
def join : AS → AS → AS
  | [], _ => []
  | (a, j) :: A, B => match get B a with
    | some j' => (a, max j j') :: join A B
    | none => join A B

/-- `A` refines `B`: every register bounded in `B` is bounded in `A`, at most as much. -/
def le (A B : AS) : Bool :=
  B.all fun p => match get A p.1 with
    | some j => decide (j ≤ p.2)
    | none => false

/-- The sum of two bounds, forgotten above `m`. -/
def add2 (m : ℕ) : Option ℕ → Option ℕ → Option ℕ
  | some a, some b => if a + b ≤ m then some (a + b) else none
  | _, _ => none

/-- One instruction. -/
def absI (m : ℕ) : Instr → AS → Option AS
  | .constR r z, A => some (put A r (if z = 0 then some 0 else none))
  | .copyR r a, A => some (put A r (get A a))
  | .addR r a b, A => some (put A r (add2 m (get A a) (get A b)))
  | .subR r a b, A => some (put A r (add2 m (get A a) (get A b)))
  | .mulR r _ _, A => some (put A r none)
  | .divR r _ _, A => some (put A r none)
  | .loadR r _, A => some (put A r (some 1))
  | .storeR _ r, A => match get A r with
    | some j => if j ≤ 1 then some A else none
    | none => none
  | _, A => some A

/-- A real test is bounded. -/
def cmpB (m : ℕ) (A : AS) (a b : ℕ) : Bool :=
  match get A a, get A b with
  | some x, some y => decide (x + y ≤ m)
  | _, _ => false

/-- The fixed point of a loop body `f`, at most `n` rounds, the test `ok` at every candidate. -/
def fix (f : AS → Option AS) (ok : AS → Bool) : ℕ → AS → Option AS
  | 0, _ => none
  | n + 1, A =>
    if ok A then
      match f A with
      | some A' => if le A' A then some A else fix f ok n (join A A')
      | none => none
    else none

/-- **The abstract interpretation of a statement**: `none` if a check fails. -/
def absS (m n : ℕ) : Stmt → AS → Option AS
  | .skip, A => some A
  | .instr i, A => absI m i A
  | .seq s t, A => match absS m n s A with
    | some A₁ => absS m n t A₁
    | none => none
  | .ifLtN _ _ t e, A => match absS m n t A, absS m n e A with
    | some A₁, some A₂ => some (join A₁ A₂)
    | _, _ => none
  | .ifLtR a b t e, A =>
    if cmpB m A a b then
      match absS m n t A, absS m n e A with
      | some A₁, some A₂ => some (join A₁ A₂)
      | _, _ => none
    else none
  | .whileLtN _ _ body, A => fix (absS m n body) (fun _ => true) n A
  | .whileLtR a b body, A => fix (absS m n body) (fun X => cmpB m X a b) n A

/-! ### Soundness -/

/-- The registers of `c` within the bounds of `A`. -/
def RegA (B : ℕ) (A : AS) (c : Config) : Prop :=
  ∀ r j, get A r = some j → |c.rreg r| ≤ ((j * B : ℕ) : ℝ)

/-- `A` refines `B` (semantically). -/
def Ref (A B' : AS) : Prop := ∀ r j, get B' r = some j → ∃ j' ≤ j, get A r = some j'

theorem Ref.refl (A : AS) : Ref A A := fun _ j h => ⟨j, le_rfl, h⟩

theorem Ref.trans {A₁ A₂ A₃ : AS} (h₁ : Ref A₁ A₂) (h₂ : Ref A₂ A₃) : Ref A₁ A₃ := by
  intro r j h
  obtain ⟨j₂, hj₂, h₂'⟩ := h₂ r j h
  obtain ⟨j₁, hj₁, h₁'⟩ := h₁ r j₂ h₂'
  exact ⟨j₁, hj₁.trans hj₂, h₁'⟩

theorem RegA.of_ref {A A' : AS} {c : Config} (h : RegA B A c) (hr : Ref A A') : RegA B A' c := by
  intro r j hj
  obtain ⟨j', hj', h'⟩ := hr r j hj
  refine (h r j' h').trans ?_
  exact_mod_cast Nat.mul_le_mul_right B hj'

theorem get_del (A : AS) (r r' : ℕ) : get (del A r) r' = if r' = r then none else get A r' := by
  induction A with
  | nil => simp [del, get]
  | cons p A ih =>
    obtain ⟨a, j⟩ := p
    by_cases h : a = r
    · subst h; simp only [del, ↓reduceIte, ih, get]
      by_cases h' : r' = a
      · simp [h']
      · simp [h', Ne.symm h']
    · simp only [del, h, ↓reduceIte, get, ih]
      by_cases h' : r' = r
      · subst h'; simp [h]
      · simp [h']

theorem get_put (A : AS) (r r' : ℕ) (o : Option ℕ) :
    get (put A r o) r' = if r' = r then o else get A r' := by
  cases o with
  | none => simp only [put, get_del]
  | some j =>
    simp only [put, get, get_del]
    by_cases h : r' = r
    · simp [h]
    · simp [h, Ne.symm h]

theorem get_join (A A' : AS) (r : ℕ) :
    get (join A A') r = match get A r, get A' r with
      | some x, some y => some (max x y)
      | _, _ => none := by
  induction A with
  | nil => simp [join, get]
  | cons p A ih =>
    obtain ⟨a, j⟩ := p
    simp only [join]
    by_cases h : a = r
    · subst h
      cases h' : get A' a with
      | none => simp only [ih, h', get, ↓reduceIte]; split <;> simp_all
      | some j' => simp [get]
    · cases h' : get A' a with
      | none => simp only [ih, get, h, ↓reduceIte]
      | some j' => simp only [get, h, ↓reduceIte, ih]

theorem ref_join_left (A A' : AS) : Ref A (join A A') := by
  intro r j h
  rw [get_join] at h
  split at h
  · rename_i x y hx _
    simp only [Option.some.injEq] at h
    exact ⟨x, by omega, hx⟩
  · simp at h

theorem ref_join_right (A A' : AS) : Ref A' (join A A') := by
  intro r j h
  rw [get_join] at h
  split at h
  · rename_i x y _ hy
    simp only [Option.some.injEq] at h
    exact ⟨y, by omega, hy⟩
  · simp at h

theorem le_sound {A A' : AS} (h : le A A' = true) : Ref A A' := by
  intro r j hj
  have hmem : (r, j) ∈ A' := by
    clear h
    induction A' with
    | nil => simp [get] at hj
    | cons p A' ih =>
      obtain ⟨a, j'⟩ := p
      simp only [get] at hj
      split_ifs at hj with ha
      · simp only [Option.some.injEq] at hj; subst ha hj; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hj)
  have := List.all_eq_true.1 h _ hmem
  simp only at this
  split at this
  · rename_i j' hj'
    exact ⟨j', by simpa using this, hj'⟩
  · simp at this

theorem fix_sound {f : AS → Option AS} {ok : AS → Bool} :
    ∀ (n : ℕ) (A X : AS), fix f ok n A = some X →
      Ref A X ∧ ok X = true ∧ ∃ Y, f X = some Y ∧ Ref Y X := by
  intro n
  induction n with
  | zero => intro A X h; simp [fix] at h
  | succ n ih =>
    intro A X h
    simp only [fix] at h
    split_ifs at h with hok
    split at h
    · rename_i A' hA'
      split_ifs at h with hle
      · simp only [Option.some.injEq] at h; subst h
        exact ⟨Ref.refl _, hok, A', hA', le_sound hle⟩
      · obtain ⟨h1, h2, h3⟩ := ih _ _ h
        exact ⟨(ref_join_left A A').trans h1, h2, h3⟩
    · simp at h

theorem RegA.put {A : AS} {c : Config} (hA : RegA B A c) (r : ℕ) (o : Option ℕ) (x : ℝ)
    (hx : ∀ j, o = some j → |x| ≤ ((j * B : ℕ) : ℝ)) :
    RegA B (put A r o) { c with rreg := upd c.rreg r x } := by
  intro r' j h
  rw [get_put] at h
  simp only [upd_apply]
  split_ifs at h ⊢ with h'
  · exact hx j h
  · exact hA r' j h

theorem add2_sound {m : ℕ} {x y : ℝ} {ja jb : Option ℕ}
    (hx : ∀ j, ja = some j → |x| ≤ ((j * B : ℕ) : ℝ))
    (hy : ∀ j, jb = some j → |y| ≤ ((j * B : ℕ) : ℝ)) (z : ℝ) (hz : |z| ≤ |x| + |y|) :
    ∀ j, add2 m ja jb = some j → |z| ≤ ((j * B : ℕ) : ℝ) := by
  intro j h
  cases ja with
  | none => simp [add2] at h
  | some u =>
    cases jb with
    | none => simp [add2] at h
    | some v =>
      simp only [add2] at h
      split_ifs at h
      simp only [Option.some.injEq] at h; subst h
      have h1 := hx u rfl
      have h2 := hy v rfl
      push_cast at h1 h2 ⊢
      rw [add_mul]
      exact hz.trans (add_le_add h1 h2)

/-- **One instruction**: its store is bounded, and the registers stay within the new bounds. -/
theorem absI_sound {m : ℕ} {ins : Instr} {A A' : AS} {c c' : Config} (h : absI m ins A = some A')
    (hs : ins.IsStraight) (he : ins.effect P c = some c') (hw : WordsBounded W c)
    (hM : MemB W B c) (hA : RegA B A c) : StOK B ins c ∧ RegA B A' c' := by
  cases ins
  all_goals first
    | (simp at hs; done)
    | (simp only [absI, Option.some.injEq] at h; subst h
       simp only [Instr.effect, Option.some.injEq] at he; subst he
       exact ⟨trivial, hA⟩)
    | skip
  case constR r z =>
    simp only [absI, Option.some.injEq] at h; subst h
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    refine ⟨trivial, hA.put r _ _ fun j hj => ?_⟩
    split_ifs at hj with hz
    · simp only [Option.some.injEq] at hj; subst hj hz; simp
  case copyR r a =>
    simp only [absI, Option.some.injEq] at h; subst h
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    exact ⟨trivial, hA.put r _ _ fun j hj => hA a j hj⟩
  case addR r a b =>
    simp only [absI, Option.some.injEq] at h; subst h
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    exact ⟨trivial, hA.put r _ _ (add2_sound (hA a) (hA b) _ (abs_add_le _ _))⟩
  case subR r a b =>
    simp only [absI, Option.some.injEq] at h; subst h
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    exact ⟨trivial, hA.put r _ _ (add2_sound (hA a) (hA b) _ (abs_sub _ _))⟩
  case mulR r a b =>
    simp only [absI, Option.some.injEq] at h; subst h
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    exact ⟨trivial, hA.put r _ _ fun j hj => by simp at hj⟩
  case divR r a b =>
    simp only [absI, Option.some.injEq] at h; subst h
    simp only [Instr.effect] at he
    split_ifs at he
    simp only [Option.some.injEq] at he; subst he
    exact ⟨trivial, hA.put r _ _ fun j hj => by simp at hj⟩
  case loadR r a =>
    simp only [absI, Option.some.injEq] at h; subst h
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    refine ⟨trivial, hA.put r _ _ fun j hj => ?_⟩
    simp only [Option.some.injEq] at hj; subst hj
    simpa using hM _ (hw.1 a)
  case storeR a r =>
    simp only [absI] at h
    split at h
    · rename_i j hj
      split_ifs at h with hj1
      simp only [Option.some.injEq] at h; subst h
      simp only [Instr.effect, Option.some.injEq] at he; subst he
      refine ⟨?_, fun r' j' h' => hA r' j' h'⟩
      have := hA r j hj
      have h2 : ((j * B : ℕ) : ℝ) ≤ B := by
        have := Nat.mul_le_mul_right B hj1
        rw [Nat.one_mul] at this
        exact_mod_cast this
      exact this.trans h2
    · simp at h

theorem cmpB_sound {m : ℕ} {A : AS} {a b : ℕ} {c : Config} (h : cmpB m A a b = true)
    (hA : RegA B A c) : |c.rreg a - c.rreg b| ≤ ((m * B : ℕ) : ℝ) := by
  simp only [cmpB] at h
  split at h
  · rename_i x y hx hy
    have h1 := hA a x hx
    have h2 := hA b y hy
    have h3 : x + y ≤ m := by simpa using h
    have h4 : (((x + y) * B : ℕ) : ℝ) ≤ ((m * B : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right B h3
    push_cast at h1 h2 h4 ⊢
    rw [add_mul] at h4
    calc |c.rreg a - c.rreg b| ≤ |c.rreg a| + |c.rreg b| := abs_sub _ _
      _ ≤ _ := (add_le_add h1 h2).trans h4
  · simp at h

theorem RegA.join_left {A₁ : AS} {c : Config} (h : RegA B A₁ c) (A₂ : AS) :
    RegA B (join A₁ A₂) c := h.of_ref (ref_join_left _ _)

theorem RegA.join_right {A₂ : AS} {c : Config} (h : RegA B A₂ c) (A₁ : AS) :
    RegA B (join A₁ A₂) c := h.of_ref (ref_join_right _ _)

/-- **Soundness of the abstract interpretation.** -/
theorem absS_sound (m n : ℕ) : ∀ (s : Stmt) (A A' : AS), absS m n s A = some A' →
    ∀ c c' k, Exec P W s c c' k → MemB W B c → RegA B A c →
      ExecG P W B (m * B) s c c' k ∧ RegA B A' c' := by
  intro s
  induction s with
  | skip =>
    intro A A' h c c' k e _ hA
    simp only [absS, Option.some.injEq] at h; subst h
    cases e with
    | skip hw => exact ⟨.skip hw, hA⟩
  | instr i =>
    intro A A' h c c' k e hM hA
    cases e with
    | instr hs he hw hw' =>
      obtain ⟨hst, hA'⟩ := absI_sound h hs he hw hM hA
      exact ⟨.instr hs he hw hw' hst, hA'⟩
  | seq s t ihs iht =>
    intro A A' h c c' k e hM hA
    simp only [absS] at h
    split at h
    · rename_i A₁ h₁
      cases e with
      | seq e₁ e₂ =>
        obtain ⟨g₁, r₁⟩ := ihs A A₁ h₁ _ _ _ e₁ hM hA
        obtain ⟨g₂, r₂⟩ := iht A₁ A' h _ _ _ e₂ (g₁.mem hM) r₁
        exact ⟨.seq g₁ g₂, r₂⟩
    · simp at h
  | ifLtN a b t e iht ihe =>
    intro A A' h c c' k ex hM hA
    simp only [absS] at h
    split at h
    · rename_i A₁ A₂ h₁ h₂
      simp only [Option.some.injEq] at h; subst h
      cases ex with
      | ifLtN_true ht e₁ =>
        obtain ⟨g, r⟩ := iht A A₁ h₁ _ _ _ e₁ hM hA
        exact ⟨.ifLtN_true ht g, r.join_left _⟩
      | ifLtN_false ht e₁ =>
        obtain ⟨g, r⟩ := ihe A A₂ h₂ _ _ _ e₁ hM hA
        exact ⟨.ifLtN_false ht g, r.join_right _⟩
    · simp at h
  | ifLtR a b t e iht ihe =>
    intro A A' h c c' k ex hM hA
    simp only [absS] at h
    split_ifs at h with hc
    have hb := cmpB_sound hc hA
    split at h
    · rename_i A₁ A₂ h₁ h₂
      simp only [Option.some.injEq] at h; subst h
      cases ex with
      | ifLtR_true ht e₁ =>
        obtain ⟨g, r⟩ := iht A A₁ h₁ _ _ _ e₁ hM hA
        exact ⟨.ifLtR_true (by exact_mod_cast hb) ht g, r.join_left _⟩
      | ifLtR_false ht e₁ =>
        obtain ⟨g, r⟩ := ihe A A₂ h₂ _ _ _ e₁ hM hA
        exact ⟨.ifLtR_false (by exact_mod_cast hb) ht g, r.join_right _⟩
    · simp at h
  | whileLtN a b body ih =>
    intro A A' h c c' k ex hM hA
    simp only [absS] at h
    obtain ⟨hAX, -, Y, hY, hYX⟩ := fix_sound n A A' h
    have hA' : RegA B A' c := hA.of_ref hAX
    clear h hA hAX
    generalize hs : Stmt.whileLtN a b body = s at ex
    induction ex with
    | whileLtN_false ht hw => cases hs; exact ⟨.whileLtN_false ht hw, hA'⟩
    | whileLtN_true ht e₁ _ _ ih₂ =>
      cases hs
      obtain ⟨g₁, r₁⟩ := ih A' Y hY _ _ _ e₁ hM hA'
      obtain ⟨g₂, r₂⟩ := ih₂ (g₁.mem hM) (r₁.of_ref hYX) rfl
      exact ⟨.whileLtN_true ht g₁ g₂, r₂⟩
    | _ => cases hs
  | whileLtR a b body ih =>
    intro A A' h c c' k ex hM hA
    simp only [absS] at h
    obtain ⟨hAX, hok, Y, hY, hYX⟩ := fix_sound n A A' h
    have hA' : RegA B A' c := hA.of_ref hAX
    clear h hA hAX
    generalize hs : Stmt.whileLtR a b body = s at ex
    induction ex with
    | whileLtR_false ht hw =>
      cases hs
      exact ⟨.whileLtR_false (by exact_mod_cast cmpB_sound hok hA') ht hw, hA'⟩
    | whileLtR_true ht e₁ _ _ ih₂ =>
      cases hs
      obtain ⟨g₁, r₁⟩ := ih A' Y hY _ _ _ e₁ hM hA'
      obtain ⟨g₂, r₂⟩ := ih₂ (g₁.mem hM) (r₁.of_ref hYX) rfl
      exact ⟨.whileLtR_true (by exact_mod_cast cmpB_sound hok hA') ht g₁ g₂, r₂⟩
    | _ => cases hs

/-- **A statement passing the abstract interpretation is good** (with `H = m B`). -/
theorem good_abs {m n : ℕ} {s : Stmt} {A A' : AS} (h : absS m n s A = some A') {c : Config}
    (hA : MemB W B c → RegA B A c) : Good P W B (m * B) s c :=
  fun _ _ e hM => (absS_sound m n s A A' h _ _ _ e hM (hA hM)).1

/-- The same, with the result of the interpretation left implicit. -/
theorem good_abs' {m n : ℕ} {s : Stmt} {A : AS} (h : (absS m n s A).isSome = true) {c : Config}
    (hA : MemB W B c → RegA B A c) : Good P W B (m * B) s c := by
  obtain ⟨A', hA'⟩ := Option.isSome_iff_exists.1 h
  exact good_abs hA' hA

/-- The empty abstract state bounds every configuration. -/
theorem regA_nil (c : Config) : RegA B [] c := fun _ _ h => by simp [get] at h

end CmpAbs

end Monge

end PlanarFlow
