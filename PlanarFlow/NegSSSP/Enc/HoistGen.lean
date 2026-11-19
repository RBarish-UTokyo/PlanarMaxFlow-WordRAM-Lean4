module

public import WordRAM
public import WordRAM.Machine.RealsModNat

/-!
# Constant hoisting: one fixed program for a family of programs

A family of statements `s p` that differ only in the constants of their `constN` instructions
(the instance's sizes, layout bases, …) is turned into **one** statement `T` reading those
constants from *parameter registers* `PB + j`:

* `hsHoist PB tbl s` (the transformation): every `constN r k` whose constant `k` is listed in
  the table `tbl` (`(k, j)`) becomes `copyN r (PB + j)`; everything else is unchanged.
  Applied to the family at a *marker* instance (constants chosen so that the instance-dependent
  ones are distinct from every fixed constant), it gives a fixed statement `T`.
* `hsUn PB v T` (the converse, used in the proofs): every `copyN r a` with `a ≥ PB` becomes
  `constN r (v (a - PB))`. For a concrete family the equation `hsUn PB (v p) T = s p` for
  **all** `p` (`v p` the list of the instance's constants) is checked by the kernel
  (`kernel_rfl`, see `HoistFe.lean`, `HoistNode.lean`); it fails if a constant of `T` were
  not the marker image of the corresponding constant of `s p`.
* `hsOK PB np T`: `T` names only registers `< PB`, except that `copyN r a` may read a parameter
  register `PB ≤ a < PB + np` (decidable, checked by the kernel).

**`hs_exec`** (the simulation theorem): if `hsOK PB np T`, a run of `hsUn PB v T` from `c` to `c'`
in `k` steps, from a configuration holding the parameters (`c.nreg (PB + j) = v j`, `j < np`), is a
run of `T` from `c` to `c'` in the **same** `k` steps (same configurations, same word bound), and
it keeps every register `≥ PB`.

Also `hsAt` (the constant at a path of a statement), `hsCR` (every real constant `z` of a
statement has `0 ≤ z < m`) and **`hs_toNat`**: `ModNat.toNat R M s = ModNat.toNat R M' s` when
`hsCR m s` and `m ≤ M`, `m ≤ M'` (the only place where the modulus is a program constant are the
residues `z mod M` of the real constants, which do not depend on `M` when `0 ≤ z < M`).
-/

@[expose] public section

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-! ### The transformation and its converse -/

/-- One instruction hoisted: `constN r k` with `(k, j)` in the table reads `PB + j`. -/
def hsHoistI (PB : ℕ) (tbl : List (ℕ × ℕ)) : Instr → Instr
  | .constN r k => match tbl.lookup k with
    | some j => .copyN r (PB + j)
    | none => .constN r k
  | i => i

/-- **Constant hoisting** of a statement (see the module docstring). -/
def hsHoist (PB : ℕ) (tbl : List (ℕ × ℕ)) : Stmt → Stmt
  | .skip => .skip
  | .instr i => .instr (hsHoistI PB tbl i)
  | .seq s t => .seq (hsHoist PB tbl s) (hsHoist PB tbl t)
  | .ifLtN a b s t => .ifLtN a b (hsHoist PB tbl s) (hsHoist PB tbl t)
  | .ifLtR a b s t => .ifLtR a b (hsHoist PB tbl s) (hsHoist PB tbl t)
  | .whileLtN a b s => .whileLtN a b (hsHoist PB tbl s)
  | .whileLtR a b s => .whileLtR a b (hsHoist PB tbl s)

/-- One instruction with the parameters put back: `copyN r a` with `a ≥ PB` is
`constN r (v (a - PB))`. -/
def hsUnI (PB : ℕ) (v : ℕ → ℕ) : Instr → Instr
  | .copyN r a => if PB ≤ a then .constN r (v (a - PB)) else .copyN r a
  | i => i

/-- **The parameters put back** into a hoisted statement. -/
def hsUn (PB : ℕ) (v : ℕ → ℕ) : Stmt → Stmt
  | .skip => .skip
  | .instr i => .instr (hsUnI PB v i)
  | .seq s t => .seq (hsUn PB v s) (hsUn PB v t)
  | .ifLtN a b s t => .ifLtN a b (hsUn PB v s) (hsUn PB v t)
  | .ifLtR a b s t => .ifLtR a b (hsUn PB v s) (hsUn PB v t)
  | .whileLtN a b s => .whileLtN a b (hsUn PB v s)
  | .whileLtR a b s => .whileLtR a b (hsUn PB v s)

/-- The constant of the `constN` instruction at a path (`false`: first child, `true`: second
child; a loop has one child); `0` if there is none. -/
def hsAt : Stmt → List Bool → ℕ
  | .instr (.constN _ k), [] => k
  | .seq s _, false :: l => hsAt s l
  | .seq _ t, true :: l => hsAt t l
  | .ifLtN _ _ s _, false :: l => hsAt s l
  | .ifLtN _ _ _ t, true :: l => hsAt t l
  | .ifLtR _ _ s _, false :: l => hsAt s l
  | .ifLtR _ _ _ t, true :: l => hsAt t l
  | .whileLtN _ _ b, _ :: l => hsAt b l
  | .whileLtR _ _ b, _ :: l => hsAt b l
  | _, _ => 0

/-- The register condition of a hoisted instruction: registers `< PB`, except the parameters
`[PB, PB + np)` read by `copyN`. -/
def hsOKI (PB np : ℕ) : Instr → Bool
  | .copyN r a => decide (r < PB) && (decide (a < PB) || decide (PB ≤ a ∧ a < PB + np))
  | i => i.regs.all (fun r => decide (r < PB))

/-- **The register condition of a hoisted statement** (instructions and natural tests). -/
def hsOK (PB np : ℕ) : Stmt → Bool
  | .skip => true
  | .instr i => hsOKI PB np i
  | .seq s t => hsOK PB np s && hsOK PB np t
  | .ifLtN a b s t => decide (a < PB) && decide (b < PB) && hsOK PB np s && hsOK PB np t
  | .ifLtR _ _ s t => hsOK PB np s && hsOK PB np t
  | .whileLtN a b s => decide (a < PB) && decide (b < PB) && hsOK PB np s
  | .whileLtR _ _ s => hsOK PB np s

/-! ### The simulation theorem -/

/-- An instruction naming only registers `< PB` keeps the registers `≥ PB`. -/
theorem hs_keepI {P : Input} {i : Instr} {c c' : Config} {PB : ℕ}
    (hi : i.regs.all (fun r => decide (r < PB)) = true) (he : i.effect P c = some c') :
    ∀ a, PB ≤ a → c'.nreg a = c.nreg a := by
  intro a ha
  cases i <;>
    simp only [Instr.regs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hi <;>
    simp only [Instr.effect, reduceCtorEq] at he <;>
    (try split_ifs at he) <;>
    (try (obtain rfl := Option.some.inj he)) <;>
    (try simp only [upd]) <;> (try split_ifs) <;> omega

theorem hsUnI_of_not {PB : ℕ} {v : ℕ → ℕ} {i : Instr}
    (h : ∀ r a, i = .copyN r a → a < PB) : hsUnI PB v i = i := by
  cases i <;> simp only [hsUnI]
  rename_i r a
  have := h r a rfl
  simp only [show ¬ PB ≤ a by omega, ↓reduceIte]

theorem hsOKI_regs {PB np : ℕ} {i : Instr} (hi : hsOKI PB np i = true)
    (h : ∀ r a, i = .copyN r a → a < PB) : i.regs.all (fun r => decide (r < PB)) = true := by
  cases i <;> simp only [hsOKI] at hi <;> try exact hi
  rename_i r a
  have := h r a rfl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
  simp [Instr.regs, hi.1, this]

/-- **The simulation theorem of constant hoisting** (see the module docstring). -/
theorem hs_exec {P : Input} {W PB np : ℕ} {v : ℕ → ℕ} {T : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W (hsUn PB v T) c c' k) (hT : hsOK PB np T = true)
    (hv : ∀ j < np, c.nreg (PB + j) = v j) :
    Exec P W T c c' k ∧ ∀ a, PB ≤ a → c'.nreg a = c.nreg a := by
  generalize hs : hsUn PB v T = s at h
  induction h generalizing T with
  | skip hw =>
    cases T <;> simp only [hsUn, reduceCtorEq] at hs
    exact ⟨.skip hw, fun _ _ => rfl⟩
  | @instr ins c₀ c₁ hst he hw hw' =>
    cases T <;> simp only [hsUn, reduceCtorEq, Stmt.instr.injEq] at hs
    rename_i i
    subst hs
    simp only [hsOK] at hT
    by_cases hcp : ∃ r a, i = .copyN r a ∧ PB ≤ a
    · obtain ⟨r, a, rfl, ha⟩ := hcp
      simp only [hsUnI, ha, ↓reduceIte, Instr.effect, Option.some.injEq] at he
      simp only [hsOKI, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hT
      have hva : c₀.nreg a = v (a - PB) := by
        have := hv (a - PB) (by omega)
        rwa [Nat.add_sub_cancel' ha] at this
      subst he
      refine ⟨.instr (by simp [Instr.IsStraight, Instr.isControl]) ?_ hw hw', fun a' ha' => ?_⟩
      · simp only [Instr.effect, hva]
      · exact upd_other _ _ _ (by omega)
    · have hn : ∀ r a, i = .copyN r a → a < PB := fun r a he' => by
        by_contra hc; exact hcp ⟨r, a, he', by omega⟩
      rw [hsUnI_of_not hn] at hst he
      exact ⟨.instr hst he hw hw', hs_keepI (hsOKI_regs hT hn) he⟩
  | seq _ _ ih₁ ih₂ =>
    cases T <;> simp only [hsUn, reduceCtorEq, Stmt.seq.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    simp only [hsOK, Bool.and_eq_true] at hT
    obtain ⟨e₁, k₁⟩ := ih₁ hT.1 hv rfl
    obtain ⟨e₂, k₂⟩ := ih₂ hT.2 (fun j hj => by rw [k₁ _ (by omega)]; exact hv j hj) rfl
    exact ⟨.seq e₁ e₂, fun a ha => (k₂ a ha).trans (k₁ a ha)⟩
  | ifLtN_true hlt _ ih =>
    cases T <;> simp only [hsUn, reduceCtorEq, Stmt.ifLtN.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    simp only [hsOK, Bool.and_eq_true] at hT
    obtain ⟨e, k⟩ := ih hT.1.2 hv rfl
    exact ⟨.ifLtN_true hlt e, k⟩
  | ifLtN_false hlt _ ih =>
    cases T <;> simp only [hsUn, reduceCtorEq, Stmt.ifLtN.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    simp only [hsOK, Bool.and_eq_true] at hT
    obtain ⟨e, k⟩ := ih hT.2 hv rfl
    exact ⟨.ifLtN_false hlt e, k⟩
  | ifLtR_true hlt _ ih =>
    cases T <;> simp only [hsUn, reduceCtorEq, Stmt.ifLtR.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    simp only [hsOK, Bool.and_eq_true] at hT
    obtain ⟨e, k⟩ := ih hT.1 hv rfl
    exact ⟨.ifLtR_true hlt e, k⟩
  | ifLtR_false hlt _ ih =>
    cases T <;> simp only [hsUn, reduceCtorEq, Stmt.ifLtR.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    simp only [hsOK, Bool.and_eq_true] at hT
    obtain ⟨e, k⟩ := ih hT.2 hv rfl
    exact ⟨.ifLtR_false hlt e, k⟩
  | whileLtN_false hlt hw =>
    cases T <;> simp only [hsUn, reduceCtorEq, Stmt.whileLtN.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    exact ⟨.whileLtN_false hlt hw, fun _ _ => rfl⟩
  | whileLtN_true hlt _ _ ih₁ ih₂ =>
    cases T <;> simp only [hsUn, reduceCtorEq, Stmt.whileLtN.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    have hT' := hT
    simp only [hsOK, Bool.and_eq_true] at hT
    obtain ⟨e₁, k₁⟩ := ih₁ hT.2 hv rfl
    obtain ⟨e₂, k₂⟩ := ih₂ hT' (fun j hj => by rw [k₁ _ (by omega)]; exact hv j hj)
      (by simp only [hsUn])
    exact ⟨.whileLtN_true hlt e₁ e₂, fun a ha => (k₂ a ha).trans (k₁ a ha)⟩
  | whileLtR_false hlt hw =>
    cases T <;> simp only [hsUn, reduceCtorEq, Stmt.whileLtR.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    exact ⟨.whileLtR_false hlt hw, fun _ _ => rfl⟩
  | whileLtR_true hlt _ _ ih₁ ih₂ =>
    cases T <;> simp only [hsUn, reduceCtorEq, Stmt.whileLtR.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    have hT' := hT
    simp only [hsOK] at hT
    obtain ⟨e₁, k₁⟩ := ih₁ hT hv rfl
    obtain ⟨e₂, k₂⟩ := ih₂ hT' (fun j hj => by rw [k₁ _ (by omega)]; exact hv j hj)
      (by simp only [hsUn])
    exact ⟨.whileLtR_true hlt e₁ e₂, fun a ha => (k₂ a ha).trans (k₁ a ha)⟩

/-- `hs_exec` for a family given by an equation `hsUn PB v T = s` (as the kernel checks it). -/
theorem hs_exec' {P : Input} {W PB np : ℕ} {v : ℕ → ℕ} {T s : Stmt} {c c' : Config} {k : ℕ}
    (hsT : hsUn PB v T = s) (h : Exec P W s c c' k) (hT : hsOK PB np T = true)
    (hv : ∀ j < np, c.nreg (PB + j) = v j) :
    Exec P W T c c' k ∧ ∀ a, PB ≤ a → c'.nreg a = c.nreg a :=
  hs_exec (hsT ▸ h) hT hv

/-! ### The modulus of the natural simulation of reals -/

/-- Every real constant `z` of the statement has `0 ≤ z < m`. -/
def hsCR (m : ℕ) : Stmt → Bool
  | .skip => true
  | .instr (.constR _ z) => decide (0 ≤ z ∧ z < (m : ℤ))
  | .instr _ => true
  | .seq s t => hsCR m s && hsCR m t
  | .ifLtN _ _ s t => hsCR m s && hsCR m t
  | .ifLtR _ _ s t => hsCR m s && hsCR m t
  | .whileLtN _ _ s => hsCR m s
  | .whileLtR _ _ s => hsCR m s

theorem hs_trI {R M M' m : ℕ} (i : Instr) (hi : hsCR m (.instr i) = true) (hM : m ≤ M)
    (hM' : m ≤ M') : ModNat.trI R M i = ModNat.trI R M' i := by
  cases i <;> simp only [ModNat.trI]
  rename_i r z
  simp only [hsCR, decide_eq_true_eq] at hi
  have h1 : z % (M : ℤ) = z := Int.emod_eq_of_lt hi.1 (by omega)
  have h2 : z % (M' : ℤ) = z := Int.emod_eq_of_lt hi.1 (by omega)
  rw [h1, h2]

/-- **The residues of the real constants do not depend on the modulus** (`0 ≤ z < m ≤ M, M'`). -/
theorem hs_toNat {R M M' m : ℕ} (s : Stmt) (hs : hsCR m s = true) (hM : m ≤ M) (hM' : m ≤ M') :
    ModNat.toNat R M s = ModNat.toNat R M' s := by
  induction s with
  | skip => rfl
  | instr i => exact hs_trI i hs hM hM'
  | seq s t ihs iht =>
    simp only [hsCR, Bool.and_eq_true] at hs
    simp only [ModNat.toNat, ihs hs.1, iht hs.2]
  | ifLtN a b s t ihs iht =>
    simp only [hsCR, Bool.and_eq_true] at hs
    simp only [ModNat.toNat, ihs hs.1, iht hs.2]
  | ifLtR a b s t ihs iht =>
    simp only [hsCR, Bool.and_eq_true] at hs
    simp only [ModNat.toNat, ihs hs.1, iht hs.2]
  | whileLtN a b s ih =>
    simp only [hsCR] at hs
    simp only [ModNat.toNat, ih hs]
  | whileLtR a b s ih =>
    simp only [hsCR] at hs
    simp only [ModNat.toNat, ih hs]

end NegSSSP

end PlanarFlow
