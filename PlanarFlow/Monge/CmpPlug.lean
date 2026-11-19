module

public import PlanarFlow.Monge.CmpAbs

/-!
# Bounded comparisons around a plugged statement, and syntactic frames

Two generic tools for `PlanarFlow.Monge.CmpAbs.Good`:

* **A statement with a hole** (`Plug mk e e' sM s s'`): `s` and `s'` are the same statement `sM`
  with every occurrence of the *marker* `mk` (at the positions chosen by the derivation) replaced
  by `e`, resp. `e'`. `plug_sound`: if `sM` passes the abstract interpretation `absS` and the hole
  is sound (`HoleOK`: every run of `e` from a configuration from which `e'` runs is bounded, ends
  within the abstract effect of the marker, and `e'` ends at the same configuration), then every
  run of `s` from a configuration from which `s'` runs is bounded. Used with a *checked* copy
  `e'` of an oracle `e` (which stops when the entry it computes is out of bounds): the existence
  of a run of the checked statement `s'` (from a realization lemma generic in the oracle) shows
  that every executed oracle call of `s` computes a bounded entry.
* **Syntactic frames** (`Stmt.allI`, `Exec.of_steps`): a reflexive, transitive relation kept by
  every instruction of a statement holds between the ends of every run; `Exec.nreg_keep`,
  `Exec.rreg_keep`: a register that no instruction of the statement writes is kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace CmpAbs

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Machine.ModNat

/-! ### Statements with a hole -/

/-- `s` and `s'` are `sM` with (some) occurrences of the marker `mk` replaced by `e`, `e'`. -/
inductive Plug (mk e e' : Stmt) : Stmt → Stmt → Stmt → Prop
  | hole : Plug mk e e' mk e e'
  | refl (s : Stmt) : Plug mk e e' s s s
  | seq {s₁ s₂ s₃ t₁ t₂ t₃ : Stmt} : Plug mk e e' s₁ s₂ s₃ → Plug mk e e' t₁ t₂ t₃ →
      Plug mk e e' (.seq s₁ t₁) (.seq s₂ t₂) (.seq s₃ t₃)
  | ifLtN (a b : ℕ) {t₁ t₂ t₃ e₁ e₂ e₃ : Stmt} : Plug mk e e' t₁ t₂ t₃ →
      Plug mk e e' e₁ e₂ e₃ → Plug mk e e' (.ifLtN a b t₁ e₁) (.ifLtN a b t₂ e₂) (.ifLtN a b t₃ e₃)
  | ifLtR (a b : ℕ) {t₁ t₂ t₃ e₁ e₂ e₃ : Stmt} : Plug mk e e' t₁ t₂ t₃ →
      Plug mk e e' e₁ e₂ e₃ → Plug mk e e' (.ifLtR a b t₁ e₁) (.ifLtR a b t₂ e₂) (.ifLtR a b t₃ e₃)
  | whileLtN (a b : ℕ) {s₁ s₂ s₃ : Stmt} : Plug mk e e' s₁ s₂ s₃ →
      Plug mk e e' (.whileLtN a b s₁) (.whileLtN a b s₂) (.whileLtN a b s₃)
  | whileLtR (a b : ℕ) {s₁ s₂ s₃ : Stmt} : Plug mk e e' s₁ s₂ s₃ →
      Plug mk e e' (.whileLtR a b s₁) (.whileLtR a b s₂) (.whileLtR a b s₃)

variable {P : Input} {W B : ℕ}

/-- The hole is sound: from a configuration bounded by `A` from which the checked statement `e'`
runs, every run of `e` is bounded, ends bounded by the abstract effect of the marker, and `e'`
ends at the same configuration. -/
def HoleOK (P : Input) (W B m n : ℕ) (mk e e' : Stmt) : Prop :=
  ∀ A A₁, absS m n mk A = some A₁ → ∀ c d k, Exec P W e c d k → MemB W B c → RegA B A c →
    (∃ d' k', Exec P W e' c d' k') →
      ExecG P W B (m * B) e c d k ∧ RegA B A₁ d ∧ ∃ k', Exec P W e' c d k'

/-- **Soundness of the abstract interpretation around a hole.** -/
theorem plug_sound {m n : ℕ} {mk o o' : Stmt} (hO : HoleOK P W B m n mk o o') {sM s s' : Stmt}
    (hp : Plug mk o o' sM s s') : ∀ A A', absS m n sM A = some A' → ∀ c d k, Exec P W s c d k →
      MemB W B c → RegA B A c → (∃ d' k', Exec P W s' c d' k') →
      ExecG P W B (m * B) s c d k ∧ RegA B A' d ∧ ∃ k', Exec P W s' c d k' := by
  induction hp with
  | hole => exact hO
  | refl s =>
    intro A A' h c d k ex hM hA _
    obtain ⟨g, r⟩ := absS_sound m n s A A' h c d k ex hM hA
    exact ⟨g, r, k, ex⟩
  | seq _ _ ih₁ ih₂ =>
    intro A A' h c d k ex hM hA hex'
    obtain ⟨d', k', ex'⟩ := hex'
    simp only [absS] at h
    split at h
    · rename_i A₁ h₁
      cases ex with
      | seq e₁ e₂ =>
        cases ex' with
        | seq e₁' e₂' =>
          obtain ⟨g₁, r₁, k₁', f₁⟩ := ih₁ A A₁ h₁ _ _ _ e₁ hM hA ⟨_, _, e₁'⟩
          obtain ⟨rfl, rfl⟩ := Exec.det f₁ e₁'
          obtain ⟨g₂, r₂, k₂', f₂⟩ := ih₂ A₁ A' h _ _ _ e₂ (g₁.mem hM) r₁ ⟨_, _, e₂'⟩
          exact ⟨.seq g₁ g₂, r₂, _, .seq f₁ f₂⟩
    · simp at h
  | ifLtN a b _ _ iht ihe =>
    intro A A' h c d k ex hM hA hex'
    obtain ⟨d', k', ex'⟩ := hex'
    simp only [absS] at h
    split at h
    · rename_i A₁ A₂ h₁ h₂
      simp only [Option.some.injEq] at h; subst h
      cases ex with
      | ifLtN_true ht e₁ =>
        cases ex' with
        | ifLtN_true _ e₁' =>
          obtain ⟨g, r, k₁, f⟩ := iht A A₁ h₁ _ _ _ e₁ hM hA ⟨_, _, e₁'⟩
          exact ⟨.ifLtN_true ht g, r.join_left _, _, .ifLtN_true ht f⟩
        | ifLtN_false hf _ => exact absurd ht hf
      | ifLtN_false ht e₁ =>
        cases ex' with
        | ifLtN_true hf _ => exact absurd hf ht
        | ifLtN_false _ e₁' =>
          obtain ⟨g, r, k₁, f⟩ := ihe A A₂ h₂ _ _ _ e₁ hM hA ⟨_, _, e₁'⟩
          exact ⟨.ifLtN_false ht g, r.join_right _, _, .ifLtN_false ht f⟩
    · simp at h
  | ifLtR a b _ _ iht ihe =>
    intro A A' h c d k ex hM hA hex'
    obtain ⟨d', k', ex'⟩ := hex'
    simp only [absS] at h
    split_ifs at h with hc
    have hb := cmpB_sound hc hA
    split at h
    · rename_i A₁ A₂ h₁ h₂
      simp only [Option.some.injEq] at h; subst h
      cases ex with
      | ifLtR_true ht e₁ =>
        cases ex' with
        | ifLtR_true _ e₁' =>
          obtain ⟨g, r, k₁, f⟩ := iht A A₁ h₁ _ _ _ e₁ hM hA ⟨_, _, e₁'⟩
          exact ⟨.ifLtR_true (by exact_mod_cast hb) ht g, r.join_left _, _, .ifLtR_true ht f⟩
        | ifLtR_false hf _ => exact absurd ht hf
      | ifLtR_false ht e₁ =>
        cases ex' with
        | ifLtR_true hf _ => exact absurd hf ht
        | ifLtR_false _ e₁' =>
          obtain ⟨g, r, k₁, f⟩ := ihe A A₂ h₂ _ _ _ e₁ hM hA ⟨_, _, e₁'⟩
          exact ⟨.ifLtR_false (by exact_mod_cast hb) ht g, r.join_right _, _, .ifLtR_false ht f⟩
    · simp at h
  | whileLtN a b _ ih =>
    intro A A' h c d k ex hM hA hex'
    simp only [absS] at h
    obtain ⟨hAX, -, Y, hY, hYX⟩ := fix_sound n A A' h
    have hA' : RegA B A' c := hA.of_ref hAX
    clear h hA hAX
    generalize hs : Stmt.whileLtN a b _ = s at ex
    induction ex with
    | whileLtN_false ht hw =>
      cases hs; exact ⟨.whileLtN_false ht hw, hA', _, .whileLtN_false ht hw⟩
    | whileLtN_true ht e₁ _ _ ih₂ =>
      cases hs
      obtain ⟨d', k', ex'⟩ := hex'
      cases ex' with
      | whileLtN_false hf _ => exact absurd ht hf
      | whileLtN_true _ e₁' e₂' =>
        obtain ⟨g₁, r₁, k₁', f₁⟩ := ih A' Y hY _ _ _ e₁ hM hA' ⟨_, _, e₁'⟩
        obtain ⟨rfl, rfl⟩ := Exec.det f₁ e₁'
        obtain ⟨g₂, r₂, k₂', f₂⟩ := ih₂ (g₁.mem hM) ⟨_, _, e₂'⟩ (r₁.of_ref hYX) rfl
        exact ⟨.whileLtN_true ht g₁ g₂, r₂, _, .whileLtN_true ht f₁ f₂⟩
    | _ => cases hs
  | whileLtR a b _ ih =>
    intro A A' h c d k ex hM hA hex'
    simp only [absS] at h
    obtain ⟨hAX, hok, Y, hY, hYX⟩ := fix_sound n A A' h
    have hA' : RegA B A' c := hA.of_ref hAX
    clear h hA hAX
    generalize hs : Stmt.whileLtR a b _ = s at ex
    induction ex with
    | whileLtR_false ht hw =>
      cases hs
      exact ⟨.whileLtR_false (by exact_mod_cast cmpB_sound hok hA') ht hw, hA', _,
        .whileLtR_false ht hw⟩
    | whileLtR_true ht e₁ _ _ ih₂ =>
      cases hs
      obtain ⟨d', k', ex'⟩ := hex'
      cases ex' with
      | whileLtR_false hf _ => exact absurd ht hf
      | whileLtR_true _ e₁' e₂' =>
        obtain ⟨g₁, r₁, k₁', f₁⟩ := ih A' Y hY _ _ _ e₁ hM hA' ⟨_, _, e₁'⟩
        obtain ⟨rfl, rfl⟩ := Exec.det f₁ e₁'
        obtain ⟨g₂, r₂, k₂', f₂⟩ := ih₂ (g₁.mem hM) ⟨_, _, e₂'⟩ (r₁.of_ref hYX) rfl
        exact ⟨.whileLtR_true (by exact_mod_cast cmpB_sound hok hA') ht g₁ g₂, r₂, _,
          .whileLtR_true ht f₁ f₂⟩
    | _ => cases hs

/-- **A plugged statement is good** from a configuration from which its checked copy runs. -/
theorem good_plug {m n : ℕ} {mk o o' sM s s' : Stmt} (hO : HoleOK P W B m n mk o o')
    (hp : Plug mk o o' sM s s') {A A' : AS} (h : absS m n sM A = some A') {c : Config}
    (hA : MemB W B c → RegA B A c) (hex : ∃ d' k', Exec P W s' c d' k') :
    Good P W B (m * B) s c :=
  fun _ _ e hM => (plug_sound hO hp A A' h _ _ _ e hM (hA hM) hex).1

/-! ### Runs without real tests and real stores -/

/-- No real test and no real store. -/
def noRS : Stmt → Bool
  | .skip => true
  | .instr (.storeR _ _) => false
  | .instr _ => true
  | .seq s t => noRS s && noRS t
  | .ifLtN _ _ t e => noRS t && noRS e
  | .ifLtR _ _ _ _ => false
  | .whileLtN _ _ body => noRS body
  | .whileLtR _ _ _ => false

/-- A run without real tests and stores is bounded. -/
theorem ExecG.of_noRS {H : ℕ} {s : Stmt} {c d : Config} {k : ℕ} (e : Exec P W s c d k)
    (h : noRS s = true) : ExecG P W B H s c d k := by
  induction e with
  | skip hw => exact .skip hw
  | instr hs he hw hw' =>
    rename_i ins _ _
    refine .instr hs he hw hw' ?_
    cases ins <;> simp_all [noRS, StOK]
  | seq _ _ ih₁ ih₂ =>
    simp only [noRS, Bool.and_eq_true] at h; exact .seq (ih₁ h.1) (ih₂ h.2)
  | ifLtN_true ht _ ih =>
    simp only [noRS, Bool.and_eq_true] at h; exact .ifLtN_true ht (ih h.1)
  | ifLtN_false ht _ ih =>
    simp only [noRS, Bool.and_eq_true] at h; exact .ifLtN_false ht (ih h.2)
  | ifLtR_true => simp [noRS] at h
  | ifLtR_false => simp [noRS] at h
  | whileLtN_false ht hw => exact .whileLtN_false ht hw
  | whileLtN_true ht _ _ ih₁ ih₂ => exact .whileLtN_true ht (ih₁ h) (ih₂ h)
  | whileLtR_false => simp [noRS] at h
  | whileLtR_true => simp [noRS] at h

/-- A statement without real tests and stores is good from everywhere. -/
theorem good_noRS {H : ℕ} {s : Stmt} (h : noRS s = true) (c : Config) : Good P W B H s c :=
  fun _ _ e _ => ExecG.of_noRS e h

/-! ### Syntactic frames -/

/-- Every instruction of the statement satisfies `f`. -/
def _root_.WordRAM.Machine.Stmt.allI (f : Instr → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => f i
  | .seq s t => s.allI f && t.allI f
  | .ifLtN _ _ t e => t.allI f && e.allI f
  | .ifLtR _ _ t e => t.allI f && e.allI f
  | .whileLtN _ _ body => body.allI f
  | .whileLtR _ _ body => body.allI f

/-- **A relation kept by the instructions is kept by the runs.** -/
theorem _root_.WordRAM.Machine.Exec.of_steps {f : Instr → Bool} {R : Config → Config → Prop}
    (hrefl : ∀ c, R c c) (htrans : ∀ c₁ c₂ c₃, R c₁ c₂ → R c₂ c₃ → R c₁ c₃)
    (hstep : ∀ (i : Instr) c c', i.IsStraight → f i = true → i.effect P c = some c' → R c c')
    {s : Stmt} {c d : Config} {k : ℕ} (e : Exec P W s c d k) (h : s.allI f = true) : R c d := by
  induction e with
  | skip => exact hrefl _
  | instr hs he => exact hstep _ _ _ hs h he
  | seq _ _ ih₁ ih₂ =>
    simp only [Stmt.allI, Bool.and_eq_true] at h; exact htrans _ _ _ (ih₁ h.1) (ih₂ h.2)
  | ifLtN_true _ _ ih => simp only [Stmt.allI, Bool.and_eq_true] at h; exact ih h.1
  | ifLtN_false _ _ ih => simp only [Stmt.allI, Bool.and_eq_true] at h; exact ih h.2
  | ifLtR_true _ _ ih => simp only [Stmt.allI, Bool.and_eq_true] at h; exact ih h.1
  | ifLtR_false _ _ ih => simp only [Stmt.allI, Bool.and_eq_true] at h; exact ih h.2
  | whileLtN_false => exact hrefl _
  | whileLtN_true _ _ _ ih₁ ih₂ => exact htrans _ _ _ (ih₁ h) (ih₂ h)
  | whileLtR_false => exact hrefl _
  | whileLtR_true _ _ _ ih₁ ih₂ => exact htrans _ _ _ (ih₁ h) (ih₂ h)

/-- The natural register written by an instruction. -/
def _root_.WordRAM.Instr.wN : Instr → Option ℕ
  | .inputSize r | .constN r _ | .copyN r _ | .addN r _ _ | .subN r _ _ | .mulN r _ _
  | .divN r _ _ | .modN r _ _ | .loadN r _ | .readIn r _ | .rand r _ => some r
  | _ => none

/-- The real register written by an instruction. -/
def _root_.WordRAM.Instr.wR : Instr → Option ℕ
  | .constR r _ | .copyR r _ | .addR r _ _ | .subR r _ _ | .mulR r _ _ | .divR r _ _
  | .loadR r _ => some r
  | _ => none

/-- No instruction writes the natural register `r`. -/
def keepsN (r : ℕ) (s : Stmt) : Bool := s.allI fun i => decide (i.wN ≠ some r)

/-- No instruction writes the real register `r`. -/
def keepsR (r : ℕ) (s : Stmt) : Bool := s.allI fun i => decide (i.wR ≠ some r)

/-- A natural register no instruction writes is kept. -/
theorem _root_.WordRAM.Machine.Exec.nreg_keep {r : ℕ} {s : Stmt} {c d : Config} {k : ℕ}
    (e : Exec P W s c d k) (h : keepsN r s = true) : d.nreg r = c.nreg r := by
  refine Exec.of_steps (R := fun c d => d.nreg r = c.nreg r) (fun _ => rfl)
    (fun _ _ _ h₁ h₂ => h₂.trans h₁) (fun i c c' _ hi he => ?_) e h
  simp only [decide_eq_true_eq] at hi
  cases i <;> simp only [Instr.effect, Option.some.injEq, Instr.wN] at he hi <;>
    (try split_ifs at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;>
    subst he <;> (try simp only [upd_apply]) <;> (try split_ifs with hh) <;>
    first | rfl | exact absurd (congrArg some hh.symm) hi

/-- A real register no instruction writes is kept. -/
theorem _root_.WordRAM.Machine.Exec.rreg_keep {r : ℕ} {s : Stmt} {c d : Config} {k : ℕ}
    (e : Exec P W s c d k) (h : keepsR r s = true) : d.rreg r = c.rreg r := by
  refine Exec.of_steps (R := fun c d => d.rreg r = c.rreg r) (fun _ => rfl)
    (fun _ _ _ h₁ h₂ => h₂.trans h₁) (fun i c c' _ hi he => ?_) e h
  simp only [decide_eq_true_eq] at hi
  cases i <;> simp only [Instr.effect, Option.some.injEq, Instr.wR] at he hi <;>
    (try split_ifs at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;>
    subst he <;> (try simp only [upd_apply]) <;> (try split_ifs with hh) <;>
    first | rfl | exact absurd (congrArg some hh.symm) hi

end CmpAbs

end Monge

end PlanarFlow
