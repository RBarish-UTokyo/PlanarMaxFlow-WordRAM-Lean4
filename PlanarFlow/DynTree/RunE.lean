module

public import PlanarFlow.DynTree.Run

/-!
# Dynamic trees with evert: a run of operations on the machine

The operations of the evertable link-cut tree (`LCTE`, without the field `fpar`), with integer
operands: `link`, `cut`, `add` and `add2` (to the first and the second values of a root path),
`evert`, `min v z` (prints the node of least value on the root path of `v`, closest to the root,
then `1` if that value is below `z` and `0` otherwise: the comparison is made on the machine,
with the real registers), `min2 v z` (the same on the second values), `sum v` (the path sum of
`v`, left in the real register `r196`; nothing is printed) and `parent v` (prints the parent of
`v`, read from the access).

**`lctE_run`.** For valid operations, `runSE B n os` prints `(runOpsE n (Forest.init n) os).2`
within `140 (n + 1) + 21 + |os| (311600 ⌊log₂ n⌋ + 42220)` steps (the amortised costs of
`PlanarFlow/DynTree/OpsCode.lean` telescope against the rank potential, which starts at `0`).
**`lctE_runsWithin`**: the compiled program runs within `400000 (n + |os| + 1) (⌊log₂ n⌋ + 1)`
steps with words at most `B + 16 (n + 1)`.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs VT

/-- An operation of the evertable structure, with integer operands. -/
inductive EOp
  | link (v w : ℕ)
  | cut (v : ℕ)
  | add (v : ℕ) (z : ℤ)
  | add2 (v : ℕ) (z : ℤ)
  | evert (v : ℕ)
  | min (v : ℕ) (z : ℤ)
  | min2 (v : ℕ) (z : ℤ)
  | sum (v : ℕ)
  | parent (v : ℕ)

namespace EOp

/-- The precondition of an operation. -/
def Valid (n : ℕ) (F : Forest) : EOp → Prop
  | .link v w => v < n ∧ w < n ∧ F.par v = n ∧ findRoot F n w ≠ v
  | .cut v => v < n ∧ F.par v < n
  | .add v _ => v < n
  | .add2 v _ => v < n
  | .evert v => v < n
  | .min v _ => v < n
  | .min2 v _ => v < n
  | .sum v => v < n
  | .parent v => v < n

/-- The effect of an operation on the forest. -/
def apply (n : ℕ) (F : Forest) : EOp → Forest
  | .link v w => DynTree.link F v w
  | .cut v => DynTree.cut F n v
  | .add v z => addPath F n v z
  | .add2 v z => addPath2 F n v z
  | .evert v => DynTree.evert F n v
  | _ => F

open Classical in
/-- The words an operation prints. -/
def answer (n : ℕ) (F : Forest) : EOp → List ℕ
  | .min v z => [(pathMin F n v).2, if (pathMin F n v).1 < (z : ℝ) then 1 else 0]
  | .min2 v z => [(pathMin2 F n v).2, if (pathMin2 F n v).1 < (z : ℝ) then 1 else 0]
  | .parent v => [F.par v]
  | _ => []

/-- The machine block of an operation. -/
def stmt (B : ℕ) : EOp → Stmt
  | .link v w => .seq (block [.constN 193 v, .constN 194 w]) (opLinkS B)
  | .cut v => .seq (block [.constN 193 v]) (opCutS B)
  | .add v z => .seq (block [.constN 193 v, .constR 200 z]) (opAddS B)
  | .add2 v z => .seq (block [.constN 193 v, .constR 200 z]) (opAdd2S B)
  | .evert v => .seq (block [.constN 193 v]) (opEvertS B)
  | .min v z => .seq (block [.constN 193 v, .constR 200 z]) <| .seq (opQueryS B) <|
      .seq (.instr (.outN 196))
        (.ifLtR 195 200 (block [.constN 198 1, .outN 198]) (block [.constN 198 0, .outN 198]))
  | .min2 v z => .seq (block [.constN 193 v, .constR 200 z]) <| .seq (opQuery2S B) <|
      .seq (.instr (.outN 196))
        (.ifLtR 195 200 (block [.constN 198 1, .outN 198]) (block [.constN 198 0, .outN 198]))
  | .sum v => .seq (block [.constN 193 v]) (opQueryS B)
  | .parent v => .seq (block [.constN 193 v]) (.seq (opParentAccS B) (.instr (.outN 195)))

end EOp

/-- Run a list of operations: the final forest and the printed words. -/
def runOpsE (n : ℕ) : Forest → List EOp → Forest × List ℕ
  | F, [] => (F, [])
  | F, o :: os =>
    let r := runOpsE n (o.apply n F) os
    (r.1, o.answer n F ++ r.2)

/-- Every operation of the list is valid on the forest it is applied to. -/
def ValidOpsE (n : ℕ) : Forest → List EOp → Prop
  | _, [] => True
  | F, o :: os => o.Valid n F ∧ ValidOpsE n (o.apply n F) os

/-- Run a list of operations. -/
def opsStmtE (B : ℕ) : List EOp → Stmt
  | [] => .skip
  | o :: os => .seq (o.stmt B) (opsStmtE B os)

/-- Initialise the structure for `n` nodes and run the operations. -/
def runSE (B n : ℕ) (os : List EOp) : Stmt :=
  .seq (.instr (.constN 151 n)) (.seq (initS B) (opsStmtE B os))

section
variable {P : Input} {W : ℕ}

lemma LCTE.lift {B n : ℕ} {F : Forest} {G : List VT} {c c' : Config} (hS : LCTE B n F G c)
    (hm : mem c' = mem c) (h151 : c'.nreg 151 = c.nreg 151) : LCTE B n F G c' :=
  ⟨hm ▸ hS.inv, hm ▸ hS.rep, hm ▸ hS.bnd, h151.trans hS.hn⟩

/-- **One operation**, with its amortised cost. -/
theorem eopStmt_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) (o : EOp) (hv : o.Valid n F) :
    ∃ c' k, Exec P W (o.stmt B) c c' k ∧ ∃ G', LCTE B n (o.apply n F) G' c' ∧
      c'.output = c.output ++ o.answer n F ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 311600 * Nat.log 2 n + 42220 := by
  cases o with
  | link v w =>
    obtain ⟨hvn, hwn, hp, hr⟩ := hv
    refine spec_seq ?_
    exec_block
    any_goals omega
    refine spec_gen fun c1 hc1 => ?_
    have hw1 : WordsBounded W c1 := by rwa [hc1]
    have hm1 : mem c1 = mem c := by rw [hc1]; rfl
    have h151 : c1.nreg 151 = c.nreg 151 := by rw [hc1]; simp
    have h193 : c1.nreg 193 = v := by rw [hc1]; simp
    have ho1 : c1.output = c.output := by rw [hc1]
    obtain ⟨c', k, G', e, hS', -, hfr, -, -, hk, -⟩ := opLink_execE (P := P) B n hw1 hW
      (hS.lift hm1 h151) h193 (by rw [hc1]; simp) hvn hwn hp hr
    exact ⟨c', k, e, G', hS', by rw [hfr.2.2, ho1]; simp [EOp.answer], by omega⟩
  | cut v =>
    obtain ⟨hvn, hp⟩ := hv
    refine spec_seq ?_
    exec_block
    any_goals omega
    refine spec_gen fun c1 hc1 => ?_
    have hw1 : WordsBounded W c1 := by rwa [hc1]
    have hm1 : mem c1 = mem c := by rw [hc1]; rfl
    have h151 : c1.nreg 151 = c.nreg 151 := by rw [hc1]; simp
    have h193 : c1.nreg 193 = v := by rw [hc1]; simp
    have ho1 : c1.output = c.output := by rw [hc1]
    obtain ⟨c', k, G', e, hS', -, hfr, -, -, hk, -⟩ := opCut_execE (P := P) B n hw1 hW
      (hS.lift hm1 h151) h193 hvn hp
    exact ⟨c', k, e, G', hS', by rw [hfr.2.2, ho1]; simp [EOp.answer], by omega⟩
  | add v z =>
    have hvn : v < n := hv
    refine spec_seq ?_
    exec_block
    any_goals omega
    refine spec_gen fun c1 hc1 => ?_
    have hw1 : WordsBounded W c1 := by rwa [hc1]
    have hm1 : mem c1 = mem c := by rw [hc1]; rfl
    have h151 : c1.nreg 151 = c.nreg 151 := by rw [hc1]; simp
    have h193 : c1.nreg 193 = v := by rw [hc1]; simp
    have ho1 : c1.output = c.output := by rw [hc1]
    obtain ⟨c', k, G', e, hS', -, hfr, -, -, hk, -⟩ := opAddC_execE (P := P) B n false hw1 hW
      (hS.lift hm1 h151) h193 hvn
    refine ⟨c', k, e, G', ?_, by rw [hfr.2.2, ho1]; simp [EOp.answer], by omega⟩
    have h200 : c1.rreg 200 = (z : ℝ) := by rw [hc1]; simp
    rw [h200] at hS'
    exact hS'
  | add2 v z =>
    have hvn : v < n := hv
    refine spec_seq ?_
    exec_block
    any_goals omega
    refine spec_gen fun c1 hc1 => ?_
    have hw1 : WordsBounded W c1 := by rwa [hc1]
    have hm1 : mem c1 = mem c := by rw [hc1]; rfl
    have h151 : c1.nreg 151 = c.nreg 151 := by rw [hc1]; simp
    have h193 : c1.nreg 193 = v := by rw [hc1]; simp
    have ho1 : c1.output = c.output := by rw [hc1]
    obtain ⟨c', k, G', e, hS', -, hfr, -, -, hk⟩ := opAdd2_execE (P := P) B n hw1 hW
      (hS.lift hm1 h151) h193 hvn
    refine ⟨c', k, e, G', ?_, by rw [hfr.2.2, ho1]; simp [EOp.answer], by omega⟩
    have h200 : c1.rreg 200 = (z : ℝ) := by rw [hc1]; simp
    rw [h200] at hS'
    exact hS'
  | evert v =>
    have hvn : v < n := hv
    refine spec_seq ?_
    exec_block
    any_goals omega
    refine spec_gen fun c1 hc1 => ?_
    have hw1 : WordsBounded W c1 := by rwa [hc1]
    have hm1 : mem c1 = mem c := by rw [hc1]; rfl
    have h151 : c1.nreg 151 = c.nreg 151 := by rw [hc1]; simp
    have h193 : c1.nreg 193 = v := by rw [hc1]; simp
    have ho1 : c1.output = c.output := by rw [hc1]
    obtain ⟨c', k, G', e, hS', -, hfr, -, -, hk⟩ := opEvert_exec (P := P) B n hw1 hW
      (hS.lift hm1 h151) h193 hvn
    exact ⟨c', k, e, G', hS', by rw [hfr.2.2, ho1]; simp [EOp.answer], by omega⟩
  | sum v =>
    have hvn : v < n := hv
    refine spec_seq ?_
    exec_block
    any_goals omega
    refine spec_gen fun c1 hc1 => ?_
    have hw1 : WordsBounded W c1 := by rwa [hc1]
    have hm1 : mem c1 = mem c := by rw [hc1]; rfl
    have h151 : c1.nreg 151 = c.nreg 151 := by rw [hc1]; simp
    have h193 : c1.nreg 193 = v := by rw [hc1]; simp
    have ho1 : c1.output = c.output := by rw [hc1]
    obtain ⟨c', k, G', e, hS', -, -, -, -, -, hfr, -, -, hk, -⟩ := opQuery_execE (P := P) B n
      hw1 hW (hS.lift hm1 h151) h193 hvn
    exact ⟨c', k, e, G', hS', by rw [hfr.2.2, ho1]; simp [EOp.answer], by omega⟩
  | parent v =>
    have hvn : v < n := hv
    refine spec_seq ?_
    exec_block
    any_goals omega
    refine spec_gen fun c1 hc1 => ?_
    have hw1 : WordsBounded W c1 := by rwa [hc1]
    have hm1 : mem c1 = mem c := by rw [hc1]; rfl
    have h151 : c1.nreg 151 = c.nreg 151 := by rw [hc1]; simp
    have h193 : c1.nreg 193 = v := by rw [hc1]; simp
    have ho1 : c1.output = c.output := by rw [hc1]
    obtain ⟨c', k, G', e, hS', h195, -, hfr, -, -, hk⟩ := opParentAcc_exec (P := P) B n
      hw1 hW (hS.lift hm1 h151) h193 hvn
    refine spec_seq_known e (fun hw => spec_instr (Exec.outN hw 195) (fun _ =>
      ⟨G', hS'.lift rfl rfl, ?_, by omega⟩))
    simp only [EOp.answer]; rw [h195, hfr.2.2, ho1]
  | min v z =>
    have hvn : v < n := hv
    refine spec_seq ?_
    exec_block
    any_goals omega
    refine spec_gen fun c1 hc1 => ?_
    have hw1 : WordsBounded W c1 := by rwa [hc1]
    have hm1 : mem c1 = mem c := by rw [hc1]; rfl
    have h151 : c1.nreg 151 = c.nreg 151 := by rw [hc1]; simp
    have h193 : c1.nreg 193 = v := by rw [hc1]; simp
    have ho1 : c1.output = c.output := by rw [hc1]
    have h200 : c1.rreg 200 = (z : ℝ) := by rw [hc1]; simp
    obtain ⟨c2, k2, G2, e2, hS2, -, h196, h195, -, -, hfr, -, -, hk2, -⟩ :=
      opQuery_execE (P := P) B n hw1 hW (hS.lift hm1 h151) h193 hvn
    have h200' : c2.rreg 200 = (z : ℝ) := by rw [(hfr.1 200 (by omega)).2, h200]
    have hW1 : 1 ≤ W := by omega
    refine spec_seq_known e2 (fun hw2 => spec_seq_known (Exec.outN hw2 196) (fun hw3 => ?_))
    by_cases hlt : (pathMin F n v).1 < (z : ℝ)
    · have x1 := Exec.constN (P := P) hw3 198 1 hW1
      have x2 := Exec.outN (P := P) x1.wb_right 198
      have e4 := Exec.block_cons x1 (Exec.block_cons x2 (Exec.block_nil x2.wb_right))
      refine ⟨_, _, Exec.ifLtR_true (by simp only; rw [h195, h200']; exact hlt) e4, G2,
        hS2.lift rfl (by simp), ?_, by omega⟩
      simp [EOp.answer, hlt, h196, hfr.2.2, ho1]
    · have x1 := Exec.constN (P := P) hw3 198 0 (Nat.zero_le _)
      have x2 := Exec.outN (P := P) x1.wb_right 198
      have e4 := Exec.block_cons x1 (Exec.block_cons x2 (Exec.block_nil x2.wb_right))
      refine ⟨_, _, Exec.ifLtR_false (by simp only; rw [h195, h200']; exact hlt) e4, G2,
        hS2.lift rfl (by simp), ?_, by omega⟩
      simp [EOp.answer, hlt, h196, hfr.2.2, ho1]
  | min2 v z =>
    have hvn : v < n := hv
    refine spec_seq ?_
    exec_block
    any_goals omega
    refine spec_gen fun c1 hc1 => ?_
    have hw1 : WordsBounded W c1 := by rwa [hc1]
    have hm1 : mem c1 = mem c := by rw [hc1]; rfl
    have h151 : c1.nreg 151 = c.nreg 151 := by rw [hc1]; simp
    have h193 : c1.nreg 193 = v := by rw [hc1]; simp
    have ho1 : c1.output = c.output := by rw [hc1]
    have h200 : c1.rreg 200 = (z : ℝ) := by rw [hc1]; simp
    obtain ⟨c2, k2, G2, e2, hS2, h196, h195, -, -, hfr, -, -, hk2⟩ :=
      opQuery2_exec (P := P) B n hw1 hW (hS.lift hm1 h151) h193 hvn
    have h200' : c2.rreg 200 = (z : ℝ) := by rw [(hfr.1 200 (by omega)).2, h200]
    have hW1 : 1 ≤ W := by omega
    refine spec_seq_known e2 (fun hw2 => spec_seq_known (Exec.outN hw2 196) (fun hw3 => ?_))
    by_cases hlt : (pathMin2 F n v).1 < (z : ℝ)
    · have x1 := Exec.constN (P := P) hw3 198 1 hW1
      have x2 := Exec.outN (P := P) x1.wb_right 198
      have e4 := Exec.block_cons x1 (Exec.block_cons x2 (Exec.block_nil x2.wb_right))
      refine ⟨_, _, Exec.ifLtR_true (by simp only; rw [h195, h200']; exact hlt) e4, G2,
        hS2.lift rfl (by simp), ?_, by omega⟩
      simp [EOp.answer, hlt, h196, hfr.2.2, ho1]
    · have x1 := Exec.constN (P := P) hw3 198 0 (Nat.zero_le _)
      have x2 := Exec.outN (P := P) x1.wb_right 198
      have e4 := Exec.block_cons x1 (Exec.block_cons x2 (Exec.block_nil x2.wb_right))
      refine ⟨_, _, Exec.ifLtR_false (by simp only; rw [h195, h200']; exact hlt) e4, G2,
        hS2.lift rfl (by simp), ?_, by omega⟩
      simp [EOp.answer, hlt, h196, hfr.2.2, ho1]

/-- **A list of operations**: the amortised costs telescope. -/
theorem opsStmtE_exec (B n : ℕ) (hW : B + 16 * (n + 1) ≤ W) (os : List EOp) :
    ∀ {c : Config} {F : Forest} {G : List VT}, WordsBounded W c → LCTE B n F G c →
    ValidOpsE n F os →
    ∃ c' k, Exec P W (opsStmtE B os) c c' k ∧ ∃ G', LCTE B n (runOpsE n F os).1 G' c' ∧
      c'.output = c.output ++ (runOpsE n F os).2 ∧
      k + 16400 * potL G' ≤ 16400 * potL G + os.length * (311600 * Nat.log 2 n + 42220) := by
  induction os with
  | nil =>
    intro c F G hc hS _
    exact ⟨c, 0, .skip hc, G, hS, by simp [runOpsE], by simp⟩
  | cons o os ih =>
    intro c F G hc hS hv
    obtain ⟨c1, k1, e1, G1, hS1, ho1, hk1⟩ := eopStmt_exec (P := P) B n hc hW hS o hv.1
    obtain ⟨c2, k2, e2, G2, hS2, ho2, hk2⟩ := ih e1.wb_right hS1 hv.2
    refine ⟨c2, k1 + k2, .seq e1 e2, G2, hS2, by rw [ho2, ho1]; simp [runOpsE], ?_⟩
    simp only [List.length_cons]
    nlinarith

/-- **A run of the evertable link-cut tree**: initialisation and `os`. -/
theorem lctE_run (B n : ℕ) (hW : B + 16 * (n + 1) ≤ W) (os : List EOp)
    (hv : ValidOpsE n (Forest.init n) os) :
    ∃ c' k, Exec P W (runSE B n os) initConfig c' k ∧
      c'.output = (runOpsE n (Forest.init n) os).2 ∧
      k ≤ 140 * (n + 1) + 21 + os.length * (311600 * Nat.log 2 n + 42220) := by
  have hc := wordsBounded_initConfig W
  have e1 := Exec.constN (P := P) hc 151 n (by omega)
  obtain ⟨c2, k2, e2, hk2, hS2, hpot, -, hfr2⟩ := init_exec (P := P) B n e1.wb_right hW
    (by simp)
  obtain ⟨c3, k3, e3, G3, -, ho3, hk3⟩ := opsStmtE_exec (P := P) B n hW os e2.wb_right
    hS2.toE hv
  refine ⟨c3, 1 + (k2 + k3), .seq e1 (.seq e2 e3), ?_, ?_⟩
  · rw [ho3, hfr2.2.2]; rfl
  · rw [hpot] at hk3; omega

/-- **The evertable link-cut tree on the machine.** For valid operations on `n` nodes, the
program `compile (runSE B n os) 0 ++ [halt]` prints the answers of the operations within
`400000 (n + |os| + 1) (⌊log₂ n⌋ + 1)` steps, with words at most `B + 16 (n + 1)`. -/
theorem lctE_runsWithin (B n : ℕ) (os : List EOp) (hv : ValidOpsE n (Forest.init n) os)
    (P : Input) :
    RunsWithin (compile (runSE B n os) 0 ++ [Instr.halt]) P (B + 16 * (n + 1))
      (400000 * (n + os.length + 1) * (Nat.log 2 n + 1))
      (runOpsE n (Forest.init n) os).2 := by
  obtain ⟨c', k, e, ho, hk⟩ := lctE_run (P := P) (W := B + 16 * (n + 1)) B n le_rfl os hv
  refine RunsWithin.mono_steps (runsWithin_of_exec_output e ho) ?_
  nlinarith

end

end DynTree

end PlanarFlow
