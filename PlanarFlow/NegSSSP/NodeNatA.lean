module

public import PlanarFlow.NegSSSP.BFNatStage
public import PlanarFlow.NegSSSP.GlueInt

/-!
# The node run on natural words: the generic tools

The node program `nodeProg` (`PlanarFlow/NegSSSP/NodeRunF.lean`) is put on natural words by
**one** modulus `M` for the whole node: `ModNat.toNat R M nodeProg` with `R` above every register
of the node. `ExecCmp.toNat_consts` (`WordRAM/Machine/RealsModNat.lean`) needs one run of the
whole node with every real test bounded by one `H` (`ExecCmp`); `ExecCmp` is compositional
(`ExecCmp.seq`), so the pieces of the node are bounded one by one, each with its own bound, and
raised to the common `H` by `ExecCmp.mono_H`. The tools:

* `IntAll`, `Exec.intAll`: the reals stay integers along every run without `divR`.
* `ExecCmp.lift`, `ExecCmp.lift_det`: a compare-bounded run of a piece on a truncated
  configuration (registers `U`, memory `≤ W`), as used by FR-Dijkstra and Bellman–Ford, gives a
  compare-bounded run of the same piece inside the node (any word bound `W' ≥ W`).
* `ExecI.toCmp`: a run whose reals are bounded integers (`RealsIntBounded X` along the run) has
  its tests bounded by `2 X`.
* `NInv W B c`: the invariant between the pieces, the real memory `≤ W` bounded by `B` and the
  real registers `500 … 519` (those of `cProg`, `pProg`) bounded by `B`.
* `glueOK`, `glue_cmp`: a piece passing the abstract interpretation `CmpAbs.absS` from the
  registers `500 … 519` bounded by `B` (`A500`) and ending with them bounded by `B` (decidable)
  compares within `m B` and keeps `NInv W B`: the copies of reals of the node, the tests of
  `minProg`, and all the arithmetic-free blocks of the node (`*_glueOK`, by `decide`).
* `cProg_cmp`, `pProg_cmp`: the two pieces with real arithmetic of the Dijkstra half, from
  `cProg_execI_of_exec`, `pProg_execI_of_exec` on the truncation to the registers `500 … 519`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge CmpAbs ModNat

/-! ### Integers -/

/-- Every real register and memory cell is an integer. -/
def IntAll (c : Config) : Prop := (∀ r, ∃ z : ℤ, c.rreg r = z) ∧ ∀ a, ∃ z : ℤ, c.rmem a = z

theorem allI_noDivR (s : Stmt) : s.allI Instr.noDivR = s.noDivR := by
  induction s <;> simp_all [Stmt.allI, Stmt.noDivR]

theorem intAll_step {P : Input} {i : Instr} {c c' : Config} (hi : i.noDivR = true)
    (he : i.effect P c = some c') (hc : IntAll c) : IntAll c' := by
  obtain ⟨hr, hm⟩ := hc
  have up : ∀ (f : ℕ → ℝ) (j : ℕ) (x : ℝ), (∀ r, ∃ z : ℤ, f r = z) → (∃ z : ℤ, x = z) →
      ∀ r, ∃ z : ℤ, upd f j x r = z := fun f j x hf hx r => by
    rw [upd_apply]; split
    · exact hx
    · exact hf r
  cases i <;> simp only [Instr.effect, Instr.noDivR, Option.some.injEq, reduceCtorEq] at he hi <;>
    (try subst he) <;> (try exact ⟨hr, hm⟩)
  case constR r z => exact ⟨up _ _ _ hr ⟨z, rfl⟩, hm⟩
  case copyR r a => exact ⟨up _ _ _ hr (hr a), hm⟩
  case addR r a b =>
    obtain ⟨x, hx⟩ := hr a; obtain ⟨y, hy⟩ := hr b
    exact ⟨up _ _ _ hr ⟨x + y, by rw [hx, hy]; push_cast; ring⟩, hm⟩
  case subR r a b =>
    obtain ⟨x, hx⟩ := hr a; obtain ⟨y, hy⟩ := hr b
    exact ⟨up _ _ _ hr ⟨x - y, by rw [hx, hy]; push_cast; ring⟩, hm⟩
  case mulR r a b =>
    obtain ⟨x, hx⟩ := hr a; obtain ⟨y, hy⟩ := hr b
    exact ⟨up _ _ _ hr ⟨x * y, by rw [hx, hy]; push_cast; ring⟩, hm⟩
  case loadR r a => exact ⟨up _ _ _ hr (hm _), hm⟩
  case storeR a r => exact ⟨hr, up _ _ _ hm (hr r)⟩

/-- **The reals stay integers** along every run without real division. -/
theorem Exec.intAll {P : Input} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (e : Exec P W s c c' k) (hD : s.noDivR = true) (hc : IntAll c) : IntAll c' :=
  Exec.of_steps (f := Instr.noDivR) (R := fun c d => IntAll c → IntAll d) (fun _ h => h)
    (fun _ _ _ h₁ h₂ h => h₂ (h₁ h)) (fun _ _ _ _ hi he h => intAll_step hi he h) e
    (by rw [allI_noDivR]; exact hD) hc

/-! ### Lifting compare-bounded runs -/

/-- **A compare-bounded run lifts** (as `Exec.lift`): from any `d` agreeing with `c` on the
registers `U` and the memory `≤ W`, the lifted run is compare-bounded with the same `H`. -/
theorem _root_.WordRAM.Machine.ModNat.ExecCmp.lift {P P' : Input} {W H W' : ℕ} {U : ℕ → Bool} {s : Stmt} {c c' : Config}
    {k : ℕ} (h : ExecCmp P W H s c c' k) (hs : s.regsOK U = true) (hn : s.noInp = true)
    (hr : s.noRand = true) (hW : W ≤ W') {d : Config} (hA : Agree U W c d)
    (hd : WordsBounded W' d) :
    ∃ d', ExecCmp P' W' H s d d' k ∧ Agree U W c' d' ∧ Keep U W d d' := by
  induction h generalizing d with
  | skip hw => exact ⟨d, .skip hd, hA, Keep.refl _ _ _⟩
  | instr hst he hw hw' =>
    obtain ⟨d', e, hA', hK, -⟩ := Exec.lift (P' := P') (Exec.instr hst he hw hw') hs hn hr hW hA hd
    cases e with | instr hst' he' _ hd' => exact ⟨d', .instr hst' he' hd hd', hA', hK⟩
  | seq _ _ ih₁ ih₂ =>
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true] at hs hn hr
    obtain ⟨d₁, e₁, hA₁, hK₁⟩ := ih₁ hs.1 hn.1 hr.1 hA hd
    obtain ⟨d₂, e₂, hA₂, hK₂⟩ := ih₂ hs.2 hn.2 hr.2 hA₁ e₁.toExec.wb_right
    exact ⟨d₂, .seq e₁ e₂, hA₂, hK₁.trans hK₂⟩
  | ifLtN_true ht _ ih =>
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true] at hs hn hr
    obtain ⟨d', e', hA', hK⟩ := ih hs.1.2 hn.1 hr.1 hA hd
    refine ⟨d', .ifLtN_true ?_ e', hA', hK⟩
    rw [hA.nreg _ hs.1.1.1, hA.nreg _ hs.1.1.2]; exact ht
  | ifLtN_false ht _ ih =>
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true] at hs hn hr
    obtain ⟨d', e', hA', hK⟩ := ih hs.2 hn.2 hr.2 hA hd
    refine ⟨d', .ifLtN_false ?_ e', hA', hK⟩
    rw [hA.nreg _ hs.1.1.1, hA.nreg _ hs.1.1.2]; exact ht
  | ifLtR_true hb ht _ ih =>
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true] at hs hn hr
    obtain ⟨d', e', hA', hK⟩ := ih hs.1.2 hn.1 hr.1 hA hd
    refine ⟨d', .ifLtR_true ?_ ?_ e', hA', hK⟩ <;>
      rw [hA.rreg _ hs.1.1.1, hA.rreg _ hs.1.1.2] <;> assumption
  | ifLtR_false hb ht _ ih =>
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true] at hs hn hr
    obtain ⟨d', e', hA', hK⟩ := ih hs.2 hn.2 hr.2 hA hd
    refine ⟨d', .ifLtR_false ?_ ?_ e', hA', hK⟩ <;>
      rw [hA.rreg _ hs.1.1.1, hA.rreg _ hs.1.1.2] <;> assumption
  | whileLtN_false ht _ =>
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    refine ⟨d, .whileLtN_false ?_ hd, hA, Keep.refl _ _ _⟩
    rw [hA.nreg _ hs.1.1, hA.nreg _ hs.1.2]; exact ht
  | whileLtN_true ht _ _ ih₁ ih₂ =>
    have hs' := hs; have hn' := hn; have hr' := hr
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true] at hs hn hr
    obtain ⟨d₁, e₁, hA₁, hK₁⟩ := ih₁ hs.2 hn hr hA hd
    obtain ⟨d₂, e₂, hA₂, hK₂⟩ := ih₂ hs' hn' hr' hA₁ e₁.toExec.wb_right
    refine ⟨d₂, .whileLtN_true ?_ e₁ e₂, hA₂, hK₁.trans hK₂⟩
    rw [hA.nreg _ hs.1.1, hA.nreg _ hs.1.2]; exact ht
  | whileLtR_false hb ht _ =>
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    refine ⟨d, .whileLtR_false ?_ ?_ hd, hA, Keep.refl _ _ _⟩ <;>
      rw [hA.rreg _ hs.1.1, hA.rreg _ hs.1.2] <;> assumption
  | whileLtR_true hb ht _ _ ih₁ ih₂ =>
    have hs' := hs; have hn' := hn; have hr' := hr
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true] at hs hn hr
    obtain ⟨d₁, e₁, hA₁, hK₁⟩ := ih₁ hs.2 hn hr hA hd
    obtain ⟨d₂, e₂, hA₂, hK₂⟩ := ih₂ hs' hn' hr' hA₁ e₁.toExec.wb_right
    refine ⟨d₂, .whileLtR_true ?_ ?_ e₁ e₂, hA₂, hK₁.trans hK₂⟩ <;>
      rw [hA.rreg _ hs.1.1, hA.rreg _ hs.1.2] <;> assumption

/-- **The run inside the node is compare-bounded** when the run of the same piece on the
truncation is: with the run `e` of `s` from `d` (word bound `W'`), the compare-bounded run from
`trunc U W d` gives `e` itself compare-bounded (by `Exec.det`), agreeing with the truncated run
and keeping the registers outside `U` and the memory above `W`. -/
theorem _root_.WordRAM.Machine.ModNat.ExecCmp.lift_det {P P' : Input} {W H W' : ℕ} {U : ℕ → Bool} {s : Stmt} {c' d d' : Config}
    {k k' : ℕ} (h : ExecCmp P W H s (trunc U W d) c' k) (hs : s.regsOK U = true)
    (hn : s.noInp = true) (hr : s.noRand = true) (hW : W ≤ W') (hd : WordsBounded W' d)
    (e : Exec P' W' s d d' k') :
    ExecCmp P' W' H s d d' k' ∧ Agree U W c' d' ∧ Keep U W d d' := by
  obtain ⟨d'', e'', hA, hK⟩ := h.lift (P' := P') hs hn hr hW (agree_trunc U W d) hd
  obtain ⟨rfl, rfl⟩ := Exec.det e''.toExec e
  exact ⟨e'', hA, hK⟩

/-- A run whose reals are integers bounded by `X` compares within `2 X`. -/
theorem _root_.WordRAM.Machine.ExecI.toCmp {P : Input} {W X : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : ExecI P (fun c => WordsBounded W c ∧ RealsIntBounded X c) s c c' k) :
    ExecCmp P W (2 * X) s c c' k := by
  have hb : ∀ d : Config, RealsIntBounded X d → ∀ a b, |d.rreg a - d.rreg b| ≤ ((2 * X : ℕ) : ℝ) := by
    intro d hd a b
    obtain ⟨x, hx, hxb⟩ := hd.1 a
    obtain ⟨y, hy, hyb⟩ := hd.1 b
    rw [hx, hy]
    have : |x - y| ≤ 2 * (X : ℤ) := (abs_sub _ _).trans (by linarith)
    have : ((|x - y| : ℤ) : ℝ) ≤ ((2 * (X : ℤ) : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at this ⊢; exact this
  induction h with
  | skip hq => exact .skip hq.1
  | instr hs he hq hq' => exact .instr hs he hq.1 hq'.1
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifLtN_true ht _ ih => exact .ifLtN_true ht ih
  | ifLtN_false ht _ ih => exact .ifLtN_false ht ih
  | ifLtR_true ht e ih => exact .ifLtR_true (hb _ e.q_left.2 _ _) ht ih
  | ifLtR_false ht e ih => exact .ifLtR_false (hb _ e.q_left.2 _ _) ht ih
  | whileLtN_false ht hq => exact .whileLtN_false ht hq.1
  | whileLtN_true ht _ _ ih₁ ih₂ => exact .whileLtN_true ht ih₁ ih₂
  | whileLtR_false ht hq => exact .whileLtR_false (hb _ hq.2 _ _) ht hq.1
  | whileLtR_true ht e _ ih₁ ih₂ => exact .whileLtR_true (hb _ e.q_left.2 _ _) ht ih₁ ih₂

/-! ### The invariant between the pieces of the node -/

/-- The real memory `≤ W` and the real registers `500 … 519` bounded by `B`. -/
def NInv (W B : ℕ) (c : Config) : Prop :=
  MemB W B c ∧ ∀ r, 500 ≤ r → r < 520 → |c.rreg r| ≤ (B : ℝ)

theorem NInv.mono {W B B' : ℕ} {c : Config} (h : NInv W B c) (hB : B ≤ B') : NInv W B' c := by
  have hB' : (B : ℝ) ≤ B' := by exact_mod_cast hB
  exact ⟨fun a ha => (h.1 a ha).trans hB', fun r h1 h2 => (h.2 r h1 h2).trans hB'⟩

/-- The registers `500 … 519` bounded by one unit. -/
def A500 : AS := (List.range 20).map fun j => (500 + j, 1)

theorem get_map_one (l : List ℕ) (f : ℕ → ℕ) {r j : ℕ}
    (h : CmpAbs.get (l.map fun i => (f i, 1)) r = some j) : j = 1 ∧ ∃ i ∈ l, f i = r := by
  induction l with
  | nil => simp [CmpAbs.get] at h
  | cons x l ih =>
    simp only [List.map_cons, CmpAbs.get] at h
    split_ifs at h with hx
    · simp only [Option.some.injEq] at h; exact ⟨h.symm, x, by simp, hx⟩
    · obtain ⟨h1, i, hi, he⟩ := ih h; exact ⟨h1, i, by simp [hi], he⟩

theorem regA_A500 {W B : ℕ} {c : Config} (h : NInv W B c) : RegA B A500 c := by
  intro r j hj
  obtain ⟨rfl, i, hi, rfl⟩ := get_map_one _ _ hj
  simp only [List.mem_range] at hi
  simpa using h.2 (500 + i) (by omega) (by omega)

/-- The abstract states bounding the registers `500 … 519` by one unit. -/
def okA (A : AS) : Bool :=
  (List.range 20).all fun j => match CmpAbs.get A (500 + j) with
    | some i => decide (i ≤ 1)
    | none => false

/-- A piece passing `absS` from `A500` and ending in a state bounding the registers
`500 … 519` by one unit. -/
def glueOK (m n : ℕ) (s : Stmt) : Bool :=
  match absS m n s A500 with
  | some A => okA A
  | none => false

theorem okA_sound {B : ℕ} {A : AS} {c : Config} (h : okA A = true) (hA : RegA B A c) :
    ∀ r, 500 ≤ r → r < 520 → |c.rreg r| ≤ (B : ℝ) := by
  intro r h1 h2
  have := List.all_eq_true.1 h (r - 500) (by simp; omega)
  rw [show 500 + (r - 500) = r by omega] at this
  split at this
  next i hi =>
    have hi' : (i : ℝ) ≤ 1 := by exact_mod_cast (of_decide_eq_true this)
    have := hA r i hi
    push_cast at this
    have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    nlinarith
  next => simp at this

/-- **A glue piece compares within `m B` and keeps the invariant.** -/
theorem glue_cmp {P : Input} {W B m n : ℕ} {s : Stmt} (h : glueOK m n s = true) {c c' : Config}
    {k : ℕ} (e : Exec P W s c c' k) (hI : NInv W B c) :
    ExecCmp P W (m * B) s c c' k ∧ NInv W B c' := by
  unfold glueOK at h
  split at h
  next A hA =>
    obtain ⟨hG, hR⟩ := absS_sound m n s A500 A hA c c' k e hI.1 (regA_A500 hI)
    exact ⟨hG.toCmp, hG.mem hI.1, okA_sound h hR⟩
  next => simp at h

/-- No real test, no real store, no write of the real registers `500 … 519`. -/
def natOnly (s : Stmt) : Bool :=
  noRS s && (List.range 20).all fun j => keepsR (500 + j) s

/-- **A piece without real tests and stores** compares within any `H` and keeps the
invariant. -/
theorem nat_cmp {P : Input} {W B H : ℕ} {s : Stmt} (h : natOnly s = true) {c c' : Config}
    {k : ℕ} (e : Exec P W s c c' k) (hI : NInv W B c) :
    ExecCmp P W H s c c' k ∧ NInv W B c' := by
  simp only [natOnly, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have hG : ExecG P W B H s c c' k := ExecG.of_noRS e h.1
  refine ⟨hG.toCmp, hG.mem hI.1, fun r h1 h2 => ?_⟩
  have := h.2 (r - 500) (by omega)
  rw [show 500 + (r - 500) = r by omega] at this
  rw [e.rreg_keep this]; exact hI.2 r h1 h2

/-! ### The glue of the node -/

theorem bdSet_glueOK : glueOK 2 10 bdSet = true := by decide +kernel
theorem bdryProg_glueOK : glueOK 2 10 bdryProg = true := by decide +kernel
theorem cornerProg_glueOK : glueOK 2 10 cornerProg = true := by decide +kernel
theorem cpyProg_glueOK : glueOK 2 10 cpyProg = true := by decide +kernel
theorem restSet_glueOK : glueOK 2 10 restSet = true := by decide +kernel
theorem permProg_glueOK : glueOK 2 10 permProg = true := by decide +kernel
theorem bfIn_glueOK : glueOK 2 10 bfIn = true := by decide +kernel
theorem bfPre_glueOK : glueOK 2 10 bfPre = true := by decide +kernel
theorem bfTail_glueOK :
    glueOK 2 10 (.seq bfOut (.seq (cpS 802 809 973 810 86) cpyProg)) = true := by decide +kernel
theorem cSet_glueOK : glueOK 2 10 cSet = true := by decide +kernel
theorem cStore_glueOK : glueOK 2 10 cStore = true := by decide +kernel
theorem clrSet_glueOK : glueOK 2 10 clrSet = true := by decide +kernel
theorem clrProg_glueOK : glueOK 2 10 clrProg = true := by decide +kernel
theorem pSet_glueOK : glueOK 2 10 pSet = true := by decide +kernel
theorem aSet_glueOK : glueOK 2 10 aSet = true := by decide +kernel
theorem aProg_glueOK : glueOK 2 10 aProg = true := by decide +kernel
theorem csSet_glueOK : glueOK 2 10 csSet = true := by decide +kernel
theorem csProg_glueOK : glueOK 2 10 csProg = true := by decide +kernel
theorem cpSet_glueOK : glueOK 2 10 cpSet = true := by decide +kernel
theorem lowRegs_glueOK : glueOK 2 10 (zeroRegs lowRegs) = true := by decide +kernel
theorem inpBlk_glueOK : glueOK 2 10 inpBlk = true := by decide +kernel
theorem nSet_glueOK : glueOK 2 10 nSet = true := by decide +kernel
theorem nrmProg_glueOK : glueOK 2 10 nrmProg = true := by decide +kernel
theorem mSet_glueOK : glueOK 2 10 mSet = true := by decide +kernel
theorem minProg_glueOK : glueOK 2 10 minProg = true := by decide +kernel

theorem natOnly_block {l : List Instr}
    (h : ∀ i ∈ l, (match i with | .storeR _ _ => false | _ => true) = true ∧ i.wR = none) :
    natOnly (block l) = true := by
  induction l with
  | nil => simp [natOnly, block, noRS, keepsR, Stmt.allI]
  | cons i l ih =>
    have hi := h i (by simp)
    have ih' := ih fun j hj => h j (by simp [hj])
    simp only [natOnly, Bool.and_eq_true, List.all_eq_true, List.mem_range] at ih' ⊢
    simp only [block, noRS, keepsR, Stmt.allI, Bool.and_eq_true] at ih' ⊢
    refine ⟨⟨?_, ih'.1⟩, fun j hj => ⟨?_, ih'.2 j hj⟩⟩
    · cases i <;> first | rfl | (simp at hi)
    · simp [hi.2]

theorem partSet_natOnly (z δr : ℕ) : natOnly (partSet z δr) = true :=
  natOnly_block (by simp [Instr.wR])
theorem kpC_natOnly (k Pb : ℕ) : natOnly (kpC k Pb) = true := natOnly_block (by simp [Instr.wR])
theorem kpK_natOnly (nD Rk : ℕ) : natOnly (kpK nD Rk) = true := natOnly_block (by simp [Instr.wR])
theorem sideSet_natOnly (s δr Fr Vr : ℕ) : natOnly (sideSet s δr Fr Vr) = true :=
  natOnly_block (by simp [Instr.wR])
theorem cpS_natOnly (rn rDn rSn rDr rSr : ℕ) : natOnly (cpS rn rDn rSn rDr rSr) = true :=
  natOnly_block (by simp [Instr.wR])
theorem zeroRegs_natOnly (l : List ℕ) : natOnly (zeroRegs l) = true :=
  natOnly_block (by simp [Instr.wR])

/-! ### `cProg` and `pProg` -/

/-- The registers of `cProg` and `pProg`. -/
def U500 : ℕ → Bool := fun r => decide (500 ≤ r ∧ r < 520)

theorem cProg_regs500 : cProg.regsOK U500 = true := by decide +kernel
theorem pProg_regs500 : pProg.regsOK U500 = true := by decide +kernel

theorem agree_trunc' (U : ℕ → Bool) (W : ℕ) (d : Config) : Agree U W d (trunc U W d) :=
  ⟨fun r hr => by simp [trunc, hr], fun r hr => by simp [trunc, hr],
    fun a ha => by simp [trunc, ha], fun a ha => by simp [trunc, ha]⟩

theorem abs_le_of_rib {X : ℕ} {x : ℝ} (h : ∃ z : ℤ, x = z ∧ |z| ≤ (X : ℤ)) : |x| ≤ (X : ℝ) := by
  obtain ⟨z, rfl, hz⟩ := h
  have : ((|z| : ℤ) : ℝ) ≤ ((X : ℤ) : ℝ) := by exact_mod_cast hz
  simpa using this

theorem rib_trunc {W B : ℕ} {c : Config} (hI : NInv W B c) (hZ : IntAll c) :
    RealsIntBounded B (trunc U500 W c) := by
  refine ⟨fun r => ?_, fun a => ?_⟩
  · simp only [trunc]
    split
    · next h =>
      simp only [U500, decide_eq_true_eq] at h
      obtain ⟨z, hz⟩ := hZ.1 r
      have := hI.2 r h.1 h.2
      rw [hz] at this ⊢
      exact ⟨z, rfl, by exact_mod_cast this⟩
    · exact ⟨0, by simp, by simp⟩
  · simp only [trunc]
    split
    · next h =>
      obtain ⟨z, hz⟩ := hZ.2 a
      have := hI.1 a h
      rw [hz] at this ⊢
      exact ⟨z, rfl, by exact_mod_cast this⟩
    · exact ⟨0, by simp, by simp⟩

/-- **`cProg` in the node**: compares within `2 · 256 (4 b + 2) B`, ends with the invariant for
`(4 b + 2) B` (`b = r500`). -/
theorem cProg_cmp {P : Input} {W B : ℕ} {c c' : Config} {k : ℕ} (e : Exec P W cProg c c' k)
    (hI : NInv W B c) (hZ : IntAll c) :
    ExecCmp P W (2 * (256 * ((4 * c.nreg 500 + 2) * B))) cProg c c' k ∧
      NInv W ((4 * c.nreg 500 + 2) * B) c' := by
  have hw : WordsBounded W c := e.wb_left
  have hwt : WordsBounded W (trunc U500 W c) :=
    wordsBounded_trunc (fun r _ => hw.1 r) (fun a _ => hw.2 a)
  obtain ⟨t', et, -, -, -⟩ := Exec.lift (P' := P) e cProg_regs500 (by decide +kernel)
    (by decide +kernel) le_rfl (agree_trunc' U500 W c) hwt
  obtain ⟨E, hE⟩ := cProg_execI_of_exec (rib_trunc hI hZ) et
  have h500 : (trunc U500 W c).nreg 500 = c.nreg 500 := by simp [trunc, U500]
  rw [h500] at E hE
  obtain ⟨hC, hA, -⟩ := E.toCmp.lift_det cProg_regs500 (by decide +kernel) (by decide +kernel)
    le_rfl hw e
  refine ⟨hC, fun a ha => ?_, fun r h1 h2 => ?_⟩
  · rw [hA.rmem a ha]; exact abs_le_of_rib (hE.2 a)
  · rw [hA.rreg r (by simp [U500]; omega)]; exact abs_le_of_rib (hE.1 r)

/-- **`pProg` in the node**: compares within `2 · 32 (2 b + 3)(b + 1) B`, ends with the invariant
for `(2 b + 3)(b + 1) B` (`b = r500`). -/
theorem pProg_cmp {P : Input} {W B : ℕ} {c c' : Config} {k : ℕ} (e : Exec P W pProg c c' k)
    (hI : NInv W B c) (hZ : IntAll c) :
    ExecCmp P W (2 * (32 * ((2 * c.nreg 500 + 3) * ((c.nreg 500 + 1) * B)))) pProg c c' k ∧
      NInv W ((2 * c.nreg 500 + 3) * ((c.nreg 500 + 1) * B)) c' := by
  have hw : WordsBounded W c := e.wb_left
  have hwt : WordsBounded W (trunc U500 W c) :=
    wordsBounded_trunc (fun r _ => hw.1 r) (fun a _ => hw.2 a)
  obtain ⟨t', et, -, -, -⟩ := Exec.lift (P' := P) e pProg_regs500 (by decide +kernel)
    (by decide +kernel) le_rfl (agree_trunc' U500 W c) hwt
  obtain ⟨E, hE⟩ := pProg_execI_of_exec (rib_trunc hI hZ) et
  have h500 : (trunc U500 W c).nreg 500 = c.nreg 500 := by simp [trunc, U500]
  rw [h500] at E hE
  obtain ⟨hC, hA, -⟩ := E.toCmp.lift_det pProg_regs500 (by decide +kernel) (by decide +kernel)
    le_rfl hw e
  refine ⟨hC, fun a ha => ?_, fun r h1 h2 => ?_⟩
  · rw [hA.rmem a ha]; exact abs_le_of_rib (hE.2 a)
  · rw [hA.rreg r (by simp [U500]; omega)]; exact abs_le_of_rib (hE.1 r)

end NegSSSP

end PlanarFlow
