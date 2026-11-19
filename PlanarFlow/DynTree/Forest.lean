module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Dynamic trees: the abstract forest and the operations

A forest on the nodes `0, …, n-1` is given by a parent function `par` (with `par v = n` for a
root; the word `n` plays the role of "none") and two real values `val v` and `val2 v` at every
node.

**Value semantics.** The value of a node `v` is best read as the length of the edge from `v` to
its parent (the value of a root is then unused). The path aggregates are taken over the path
from `v` to the root of its tree, `v` included:

* `pathSum F n v`: the sum of the values; with edge lengths as values and `0` at the roots it is
  the distance from `v` to its root;
* `pathMin F n v`: the least value and the node attaining it closest to the root (the leftmost
  minimum on the path listed from the root down to `v`);
* `addPath F n v δ`: add `δ` to every value on the path.

The structural operations are `link F v w` (make `w` the parent of the root `v`), `cut F n v`
(remove the edge from `v` to its parent) and `evert F n v` (make `v` the root of its tree: the
path from `v` to its root is reversed); the queries are `findRoot F n v` and the parent
`F.par v`.

**Two values: darts.** The second value `val2` has the same aggregates (`pathMin2`, `pathSum2`,
`addPath2`). `evert` swaps `val` and `val2` on the reversed path. With a tree of the dual graph
subdivided by one node per edge, and `val e` (`val2 e`) the value of the dart of `e` towards
(away from) the root, this is the dart semantics of the dynamic trees of A. V. Goldberg,
M. D. Grigoriadis and R. E. Tarjan, *Use of dynamic trees in a network simplex algorithm for the
maximum flow problem*, Math. Programming 50 (1991), 277–290: everting reverses the darts of the
path, and the values travel with the darts.

The operations are those of the dynamic trees of D. D. Sleator and R. E. Tarjan, *A data
structure for dynamic trees*, J. Comput. Syst. Sci. 26 (1983), 362–391.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

/-- A forest on `0, …, n-1`: parents (`n` for a root) and values. -/
structure Forest where
  /-- The parent of a node, `n` for a root. -/
  par : ℕ → ℕ
  /-- The value of a node. -/
  val : ℕ → ℝ
  /-- The second value of a node. -/
  val2 : ℕ → ℝ

/-- The forest of `n` isolated nodes with value `0`. -/
def Forest.init (n : ℕ) : Forest := ⟨fun _ => n, fun _ => 0, fun _ => 0⟩

/-- The path from `v` towards the root, `v` first, following at most `fuel` parent links. -/
def upPath (F : Forest) (n : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, v => if v < n then v :: upPath F n fuel (F.par v) else []

/-- The path from `v` to the root of its tree, `v` first and the root last. -/
def rootPath (F : Forest) (n v : ℕ) : List ℕ := upPath F n n v

/-- The root of the tree containing `v`. -/
def findRoot (F : Forest) (n v : ℕ) : ℕ := (rootPath F n v).getLastD n

/-- The least value of a nonempty list of `(node, value)` pairs, with the first node attaining
it. -/
def lmin : List (ℕ × ℝ) → ℝ × ℕ
  | [] => (0, 0)
  | [p] => (p.2, p.1)
  | p :: q :: ps => if (lmin (q :: ps)).1 < p.2 then lmin (q :: ps) else (p.2, p.1)

/-- The path from the root down to `v` with the values. -/
def downVals (F : Forest) (n v : ℕ) : List (ℕ × ℝ) :=
  (rootPath F n v).reverse.map fun u => (u, F.val u)

/-- The least value on the path from `v` to its root, and the node attaining it that is closest
to the root. -/
def pathMin (F : Forest) (n v : ℕ) : ℝ × ℕ := lmin (downVals F n v)

/-- The sum of the values on the path from `v` to its root. -/
def pathSum (F : Forest) (n v : ℕ) : ℝ := ((rootPath F n v).map F.val).sum

/-- Make `w` the parent of `v`. -/
def link (F : Forest) (v w : ℕ) : Forest :=
  ⟨fun u => if u = v then w else F.par u, F.val, F.val2⟩

/-- Remove the edge from `v` to its parent. -/
def cut (F : Forest) (n v : ℕ) : Forest :=
  ⟨fun u => if u = v then n else F.par u, F.val, F.val2⟩

/-- Add `δ` to the values on the path from `v` to its root. -/
def addPath (F : Forest) (n v : ℕ) (δ : ℝ) : Forest :=
  ⟨F.par, fun u => if u ∈ rootPath F n v then F.val u + δ else F.val u, F.val2⟩

/-- The path from the root down to `v` with the second values. -/
def downVals2 (F : Forest) (n v : ℕ) : List (ℕ × ℝ) :=
  (rootPath F n v).reverse.map fun u => (u, F.val2 u)

/-- The least second value on the path from `v` to its root, and the node attaining it that is
closest to the root. -/
def pathMin2 (F : Forest) (n v : ℕ) : ℝ × ℕ := lmin (downVals2 F n v)

/-- The sum of the second values on the path from `v` to its root. -/
def pathSum2 (F : Forest) (n v : ℕ) : ℝ := ((rootPath F n v).map F.val2).sum

/-- Add `δ` to the second values on the path from `v` to its root. -/
def addPath2 (F : Forest) (n v : ℕ) (δ : ℝ) : Forest :=
  ⟨F.par, F.val, fun u => if u ∈ rootPath F n v then F.val2 u + δ else F.val2 u⟩

/-- The new parent of `u` when the path `p :: xs` is reversed (`p` the new parent of the first
node of `xs`); `none` if `u` is not on `xs`. -/
def revPar (p : ℕ) : List ℕ → ℕ → Option ℕ
  | [], _ => none
  | x :: xs, u => if u = x then some p else revPar x xs u

/-- **Evert**: make `v` the root of its tree. The path from `v` to its root is reversed, and the
two values of its nodes are swapped. -/
def evert (F : Forest) (n v : ℕ) : Forest :=
  ⟨fun u => (revPar n (rootPath F n v) u).getD (F.par u),
    fun u => if u ∈ rootPath F n v then F.val2 u else F.val u,
    fun u => if u ∈ rootPath F n v then F.val u else F.val2 u⟩

/-- The operations of a run. -/
inductive Op
  /-- `link v w`: `v` is a root, `w` is not in the tree of `v`; make `w` the parent of `v`. -/
  | link (v w : ℕ)
  /-- `cut v`: `v` is not a root; remove the edge to its parent. -/
  | cut (v : ℕ)
  /-- `findRoot v`; prints the root. -/
  | root (v : ℕ)
  /-- `parent v`; prints the parent (`n` for a root). -/
  | parent (v : ℕ)
  /-- `addPath v δ`. -/
  | add (v : ℕ) (δ : ℝ)
  /-- `minPath v`; prints the node of least value on the path (closest to the root). -/
  | min (v : ℕ)

/-- The precondition of an operation. -/
def Op.Valid (n : ℕ) (F : Forest) : Op → Prop
  | .link v w => v < n ∧ w < n ∧ F.par v = n ∧ findRoot F n w ≠ v
  | .cut v => v < n ∧ F.par v < n
  | .root v => v < n
  | .parent v => v < n
  | .add v _ => v < n
  | .min v => v < n

/-- The effect of an operation on the forest. -/
def Op.apply (n : ℕ) (F : Forest) : Op → Forest
  | .link v w => DynTree.link F v w
  | .cut v => DynTree.cut F n v
  | .add v δ => addPath F n v δ
  | _ => F

/-- The words an operation prints. -/
def Op.answer (n : ℕ) (F : Forest) : Op → List ℕ
  | .root v => [findRoot F n v]
  | .parent v => [F.par v]
  | .min v => [(pathMin F n v).2]
  | _ => []

/-- Run a list of operations: the final forest and the printed words. -/
def runOps (n : ℕ) : Forest → List Op → Forest × List ℕ
  | F, [] => (F, [])
  | F, o :: os =>
    let r := runOps n (o.apply n F) os
    (r.1, o.answer n F ++ r.2)

/-- Every operation of the list is valid on the forest it is applied to. -/
def ValidOps (n : ℕ) : Forest → List Op → Prop
  | _, [] => True
  | F, o :: os => o.Valid n F ∧ ValidOps n (o.apply n F) os

/-! ### Basic facts -/

lemma lmin_cons {p q : ℕ × ℝ} {ps : List (ℕ × ℝ)} :
    lmin (p :: q :: ps) = if (lmin (q :: ps)).1 < p.2 then lmin (q :: ps) else (p.2, p.1) := rfl

/-- The leftmost minimum of a concatenation of two nonempty lists. -/
lemma lmin_append {A C : List (ℕ × ℝ)} (hA : A ≠ []) (hC : C ≠ []) :
    lmin (A ++ C) = if (lmin C).1 < (lmin A).1 then lmin C else lmin A := by
  induction A with
  | nil => exact absurd rfl hA
  | cons p A ih =>
    rcases A with _ | ⟨q, A⟩
    · obtain ⟨r, C, rfl⟩ := List.exists_cons_of_ne_nil hC
      rfl
    · have ih' := ih (by simp)
      rw [List.cons_append, List.cons_append, lmin_cons, ← List.cons_append, ih', lmin_cons]
      split_ifs <;> first | rfl | (exfalso; simp_all; linarith)

end DynTree

end PlanarFlow
