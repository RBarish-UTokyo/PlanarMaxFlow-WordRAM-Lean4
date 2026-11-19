module

public import PlanarFlow.DynTree.Init

/-!
# Dynamic trees: a run of operations on the machine

`IOp` is an operation with an integer increment for `add` (the machine has integer literals but no
conversion of input words to reals). `opStmt B o` loads the operands of `o` into `r193`, `r194`,
the real `r200`, runs the block of the operation and prints its answer; `runS B n os`
initialises the structure for `n` nodes and runs the operations `os`.

**`lct_run`.** For valid operations, `runS B n os` prints `(runOps n (Forest.init n) os).2` within
`140 (n + 1) + 30 + |os| (311600 ⌊log₂ n⌋ + 42220)` steps: the amortised costs telescope against
the rank potential `16400 · potL`, which starts at `0`. **`lct_runsWithin`**: the program
`compile (runS B n os) 0 ++ [halt]` runs within `400000 (n + |os| + 1) (⌊log₂ n⌋ + 1)` steps with
words at most `B + 8 (n + 1)`.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs VT

/-- An operation with an integer increment. -/
inductive IOp
  | link (v w : ℕ)
  | cut (v : ℕ)
  | root (v : ℕ)
  | parent (v : ℕ)
  | add (v : ℕ) (z : ℤ)
  | min (v : ℕ)

/-- The operation of the forest. -/
def IOp.toOp : IOp → Op
  | .link v w => .link v w
  | .cut v => .cut v
  | .root v => .root v
  | .parent v => .parent v
  | .add v z => .add v (z : ℝ)
  | .min v => .min v

/-- The machine block of an operation. -/
def opStmt (B : ℕ) : IOp → Stmt
  | .link v w => .seq (block [.constN 193 v, .constN 194 w]) (opLinkS B)
  | .cut v => .seq (block [.constN 193 v]) (opCutS B)
  | .root v => .seq (block [.constN 193 v]) (.seq (opQueryS B) (.instr (.outN 195)))
  | .parent v => .seq (block [.constN 193 v]) (.seq (opParentS B) (.instr (.outN 195)))
  | .add v z => .seq (block [.constN 193 v, .constR 200 z]) (opAddS B)
  | .min v => .seq (block [.constN 193 v]) (.seq (opQueryS B) (.instr (.outN 196)))

/-- Run a list of operations. -/
def opsStmt (B : ℕ) : List IOp → Stmt
  | [] => .skip
  | o :: os => .seq (opStmt B o) (opsStmt B os)

/-- Initialise the structure for `n` nodes and run the operations. -/
def runS (B n : ℕ) (os : List IOp) : Stmt :=
  .seq (.instr (.constN 151 n)) (.seq (initS B) (opsStmt B os))

section
variable {P : Input} {W : ℕ}

lemma LCT.lift {B n : ℕ} {F : Forest} {G : List VT} {c c' : Config} (hS : LCT B n F G c)
    (hm : mem c' = mem c) (h151 : c'.nreg 151 = c.nreg 151) : LCT B n F G c' :=
  ⟨hm ▸ hS.inv, hm ▸ hS.rep, hm ▸ hS.bnd, h151.trans hS.hn⟩

/-- **One operation**, with its amortised cost. -/
theorem opStmt_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCT B n F G c) (o : IOp) (hv : o.toOp.Valid n F) :
    ∃ c' k, Exec P W (opStmt B o) c c' k ∧ ∃ G', LCT B n (o.toOp.apply n F) G' c' ∧
      c'.output = c.output ++ o.toOp.answer n F ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 311600 * Nat.log 2 n + 42220 := by
  cases o with
  | link v w =>
    obtain ⟨hvn, hwn, hp, hr⟩ := hv
    refine spec_seq ?_
    exec_block
    any_goals omega
    refine spec_gen fun c1 hc1 => ?_
    have hw1 : WordsBounded W c1 := by rw [hc1]; assumption
    have hm1 : mem c1 = mem c := by rw [hc1]; rfl
    have h151 : c1.nreg 151 = c.nreg 151 := by rw [hc1]; simp
    have h193 : c1.nreg 193 = v := by rw [hc1]; simp
    have ho1 : c1.output = c.output := by rw [hc1]
    obtain ⟨c', k, G', e, hS', -, hfr, -, -, hk⟩ := opLink_exec (P := P) B n hw1 hW
      (hS.lift hm1 h151) h193 (by rw [hc1]; simp) hvn hwn hp hr
    exact ⟨c', k, e, G', hS', by rw [hfr.2.2, ho1]; simp [IOp.toOp, Op.answer], by omega⟩
  | cut v =>
    obtain ⟨hvn, hp⟩ := hv
    refine spec_seq ?_
    exec_block
    any_goals omega
    refine spec_gen fun c1 hc1 => ?_
    have hw1 : WordsBounded W c1 := by rw [hc1]; assumption
    have hm1 : mem c1 = mem c := by rw [hc1]; rfl
    have h151 : c1.nreg 151 = c.nreg 151 := by rw [hc1]; simp
    have h193 : c1.nreg 193 = v := by rw [hc1]; simp
    have ho1 : c1.output = c.output := by rw [hc1]
    obtain ⟨c', k, G', e, hS', -, hfr, -, -, hk⟩ := opCut_exec (P := P) B n hw1 hW
      (hS.lift hm1 h151) h193 hvn hp
    exact ⟨c', k, e, G', hS', by rw [hfr.2.2, ho1]; simp [IOp.toOp, Op.answer], by omega⟩
  | root v =>
    have hvn : v < n := hv
    refine spec_seq ?_
    exec_block
    any_goals omega
    refine spec_gen fun c1 hc1 => ?_
    have hw1 : WordsBounded W c1 := by rw [hc1]; assumption
    have hm1 : mem c1 = mem c := by rw [hc1]; rfl
    have h151 : c1.nreg 151 = c.nreg 151 := by rw [hc1]; simp
    have h193 : c1.nreg 193 = v := by rw [hc1]; simp
    have ho1 : c1.output = c.output := by rw [hc1]
    obtain ⟨c', k, G', e, hS', h195, -, -, -, -, hfr, -, -, hk⟩ := opQuery_exec (P := P) B n
      hw1 hW (hS.lift hm1 h151) h193 hv
    refine spec_seq_known e (fun hw => spec_instr (Exec.outN hw 195) (fun _ =>
      ⟨G', hS'.lift rfl rfl, ?_, by omega⟩))
    simp only [IOp.toOp, Op.answer]; rw [h195, hfr.2.2, ho1]
  | parent v =>
    have hvn : v < n := hv
    refine spec_seq ?_
    exec_block
    any_goals omega
    refine spec_gen fun c1 hc1 => ?_
    have hw1 : WordsBounded W c1 := by rw [hc1]; assumption
    have hm1 : mem c1 = mem c := by rw [hc1]; rfl
    have h151 : c1.nreg 151 = c.nreg 151 := by rw [hc1]; simp
    have h193 : c1.nreg 193 = v := by rw [hc1]; simp
    have ho1 : c1.output = c.output := by rw [hc1]
    obtain ⟨c', k, e, hk, hS', h195, -, hfr, -, -⟩ := opParent_exec (P := P) B n
      hw1 hW (hS.lift hm1 h151) h193 hv
    refine spec_seq_known e (fun hw => spec_instr (Exec.outN hw 195) (fun _ =>
      ⟨G, hS'.lift rfl rfl, ?_, by omega⟩))
    simp only [IOp.toOp, Op.answer]; rw [h195, hfr.2.2, ho1]
  | add v z =>
    have hvn : v < n := hv
    refine spec_seq ?_
    exec_block
    any_goals omega
    refine spec_gen fun c1 hc1 => ?_
    have hw1 : WordsBounded W c1 := by rw [hc1]; assumption
    have hm1 : mem c1 = mem c := by rw [hc1]; rfl
    have h151 : c1.nreg 151 = c.nreg 151 := by rw [hc1]; simp
    have h193 : c1.nreg 193 = v := by rw [hc1]; simp
    have ho1 : c1.output = c.output := by rw [hc1]
    obtain ⟨c', k, G', e, hS', -, hfr, -, -, hk⟩ := opAdd_exec (P := P) B n hw1 hW
      (hS.lift hm1 h151) h193 hvn
    refine ⟨c', k, e, G', ?_, by rw [hfr.2.2, ho1]; simp [IOp.toOp, Op.answer], by omega⟩
    simp only [IOp.toOp, Op.apply]
    have h200 : c1.rreg 200 = (z : ℝ) := by rw [hc1]; simp
    rw [h200] at hS'
    exact hS'
  | min v =>
    have hvn : v < n := hv
    refine spec_seq ?_
    exec_block
    any_goals omega
    refine spec_gen fun c1 hc1 => ?_
    have hw1 : WordsBounded W c1 := by rw [hc1]; assumption
    have hm1 : mem c1 = mem c := by rw [hc1]; rfl
    have h151 : c1.nreg 151 = c.nreg 151 := by rw [hc1]; simp
    have h193 : c1.nreg 193 = v := by rw [hc1]; simp
    have ho1 : c1.output = c.output := by rw [hc1]
    obtain ⟨c', k, G', e, hS', -, h196, -, -, -, hfr, -, -, hk⟩ := opQuery_exec (P := P) B n
      hw1 hW (hS.lift hm1 h151) h193 hv
    refine spec_seq_known e (fun hw => spec_instr (Exec.outN hw 196) (fun _ =>
      ⟨G', hS'.lift rfl rfl, ?_, by omega⟩))
    simp only [IOp.toOp, Op.answer]; rw [h196, hfr.2.2, ho1]


/-- **A list of operations**: the amortised costs telescope. -/
theorem opsStmt_exec (B n : ℕ) (hW : B + 16 * (n + 1) ≤ W) (os : List IOp) :
    ∀ {c : Config} {F : Forest} {G : List VT}, WordsBounded W c → LCT B n F G c →
    ValidOps n F (os.map IOp.toOp) →
    ∃ c' k, Exec P W (opsStmt B os) c c' k ∧ ∃ G', LCT B n (runOps n F (os.map IOp.toOp)).1 G' c' ∧
      c'.output = c.output ++ (runOps n F (os.map IOp.toOp)).2 ∧
      k + 16400 * potL G' ≤ 16400 * potL G + os.length * (311600 * Nat.log 2 n + 42220) := by
  induction os with
  | nil =>
    intro c F G hc hS _
    exact ⟨c, 0, .skip hc, G, hS, by simp [runOps], by simp⟩
  | cons o os ih =>
    intro c F G hc hS hv
    obtain ⟨c1, k1, e1, G1, hS1, ho1, hk1⟩ := opStmt_exec (P := P) B n hc hW hS o hv.1
    obtain ⟨c2, k2, e2, G2, hS2, ho2, hk2⟩ := ih e1.wb_right hS1 hv.2
    refine ⟨c2, k1 + k2, .seq e1 e2, G2, hS2, by rw [ho2, ho1]; simp [runOps], ?_⟩
    simp only [List.length_cons]
    nlinarith

/-- **A run of the link-cut tree**: initialisation and `os`. -/
theorem lct_run (B n : ℕ) (hW : B + 16 * (n + 1) ≤ W) (os : List IOp)
    (hv : ValidOps n (Forest.init n) (os.map IOp.toOp)) :
    ∃ c' k, Exec P W (runS B n os) initConfig c' k ∧
      c'.output = (runOps n (Forest.init n) (os.map IOp.toOp)).2 ∧
      k ≤ 140 * (n + 1) + 21 + os.length * (311600 * Nat.log 2 n + 42220) := by
  have hc := wordsBounded_initConfig W
  have e1 := Exec.constN (P := P) hc 151 n (by omega)
  obtain ⟨c2, k2, e2, hk2, hS2, hpot, -, hfr2⟩ := init_exec (P := P) B n e1.wb_right hW
    (by simp)
  obtain ⟨c3, k3, e3, G3, -, ho3, hk3⟩ := opsStmt_exec (P := P) B n hW os e2.wb_right hS2 hv
  refine ⟨c3, 1 + (k2 + k3), .seq e1 (.seq e2 e3), ?_, ?_⟩
  · rw [ho3, hfr2.2.2]; rfl
  · rw [hpot] at hk3; omega

/-- **The link-cut tree on the machine.** For valid operations on `n` nodes, the program
`compile (runS B n os) 0 ++ [halt]` prints the answers of the operations within
`400000 (n + |os| + 1) (⌊log₂ n⌋ + 1)` steps, with words at most `B + 16 (n + 1)`. -/
theorem lct_runsWithin (B n : ℕ) (os : List IOp)
    (hv : ValidOps n (Forest.init n) (os.map IOp.toOp)) (P : Input) :
    RunsWithin (compile (runS B n os) 0 ++ [Instr.halt]) P (B + 16 * (n + 1))
      (400000 * (n + os.length + 1) * (Nat.log 2 n + 1))
      (runOps n (Forest.init n) (os.map IOp.toOp)).2 := by
  obtain ⟨c', k, e, ho, hk⟩ := lct_run (P := P) (W := B + 16 * (n + 1)) B n le_rfl os hv
  refine RunsWithin.mono_steps (runsWithin_of_exec_output e ho) ?_
  nlinarith

end

end DynTree

end PlanarFlow
