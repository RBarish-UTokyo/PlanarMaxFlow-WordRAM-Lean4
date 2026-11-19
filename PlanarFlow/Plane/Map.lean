module

public import PlanarFlow.Spec
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Combinatorial maps and flows on darts

Planar flow algorithms work with *darts*: every edge of the graph is a pair of opposite darts
`d` and `rev d`. A flow is an antisymmetric function on darts (`f (rev d) = - f d`), and a
capacity is a function on darts, `f d ≤ u d` bounding the flow along `d` (so `-u (rev d) ≤ f d`
is the lower bound). Directed graphs are included: an arc `a → b` of capacity `c` is a dart of
capacity `c` whose reverse has capacity `0`.

A *combinatorial map* (`PlanarFlow.CombMap`) on the darts `D` records the reversal of darts, the
vertex `tail d` at which a dart starts, the face `face d` whose boundary walk traverses `d`, and
the successor `next d` of `d` along that boundary walk: `next d` starts where `d` ends and has
the same face. Maps may have loops and parallel edges. The rotation at the vertices is
`rot d = next (rev d)`: it permutes the darts leaving each vertex, and `face (rot d) =
face (rev d)`. This is the usual description of a graph embedded in an oriented surface by its
face boundary walks (Edmonds; Mohar–Thomassen, §3.2).

A map is *plane* (`PlanarFlow.CombMap.IsPlane`) if the graph and its dual are connected and
Euler's formula `V + F = E + 2` holds, where `E` is half the number of darts.

## Main definitions

* `PlanarFlow.CombMap`, `PlanarFlow.CombMap.head`, `PlanarFlow.CombMap.rot`.
* `PlanarFlow.CombMap.div f v`: the net flow of `f` out of `v`.
* `PlanarFlow.CombMap.IsCirc f`: `f` is antisymmetric with zero divergence.
* `PlanarFlow.CombMap.cob φ`: the coboundary of a function on the faces,
  `cob φ d = φ (face (rev d)) - φ (face d)`.
* `PlanarFlow.CombMap.IsPlane`.

## Main results

* `PlanarFlow.CombMap.isCirc_cob`: the coboundary of a function on the faces is a circulation
  (for any map).
* `PlanarFlow.CombMap.sum_div`: the total divergence of an antisymmetric function vanishes.

## References

* J. Edmonds, *A combinatorial representation for polyhedral surfaces*, Notices Amer. Math. Soc.
  7 (1960), 646.
* B. Mohar, C. Thomassen, *Graphs on Surfaces*, Johns Hopkins University Press (2001), §3.2.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

open Finset

namespace CombMap

variable {D V F : Type*} (M : CombMap D V F)

@[simp] lemma head_rev (d : D) : M.head (M.rev d) = M.tail d := by simp [head, M.rev_rev]

@[simp] lemma tail_rev (d : D) : M.tail (M.rev d) = M.head d := rfl

lemma rev_injective : Function.Injective M.rev := fun a b h => by
  rw [← M.rev_rev a, h, M.rev_rev]

/-- The rotation at the vertices: the next dart leaving the same vertex. -/
def rot (d : D) : D := M.next (M.rev d)

lemma tail_rot (d : D) : M.tail (M.rot d) = M.tail d := by simp [rot, M.tail_next, M.rev_rev]

lemma face_rot (d : D) : M.face (M.rot d) = M.face (M.rev d) := by simp [rot, M.face_next]

lemma rot_injective : Function.Injective M.rot := fun _ _ h =>
  M.rev_injective (M.next_injective h)

variable [Fintype D] [DecidableEq V]

/-- A circulation: an antisymmetric function with zero net flow out of every vertex. -/
structure IsCirc (f : D → ℤ) : Prop where
  antisymm : M.IsAntisymm f
  div_eq : ∀ v, M.div f v = 0

lemma cob_antisymm {R : Type*} [AddCommGroup R] (φ : F → R) : M.IsAntisymm (M.cob φ) := by
  intro d; simp [cob, M.rev_rev]

/-- A sum over the darts leaving a vertex is invariant under the rotation. -/
lemma sum_tail_rot {β : Type*} [AddCommMonoid β] (v : V) (g : D → β) :
    ∑ d with M.tail d = v, g (M.rot d) = ∑ d with M.tail d = v, g d := by
  have hbij : Function.Bijective M.rot := M.rot_injective.bijective_of_finite
  let e : D ≃ D := Equiv.ofBijective _ hbij
  exact sum_equiv e (fun d => by simp [e, M.tail_rot]) (fun _ _ => rfl)

/-- **Coboundaries are circulations**, for any map. -/
theorem div_cob {R : Type*} [AddCommGroup R] (φ : F → R) (v : V) :
    ∑ d with M.tail d = v, M.cob φ d = 0 := by
  simp only [cob, sum_sub_distrib]
  rw [← sum_congr rfl fun d _ => congrArg φ (M.face_rot d), M.sum_tail_rot v (fun d => φ (M.face d)),
    sub_self]

theorem isCirc_cob (φ : F → ℤ) : M.IsCirc (M.cob φ) :=
  ⟨M.cob_antisymm φ, M.div_cob φ⟩

/-- The total net flow of an antisymmetric function is zero. -/
theorem sum_div [Fintype V] {f : D → ℤ} (hf : M.IsAntisymm f) : ∑ v, M.div f v = 0 := by
  have h1 : ∑ v, M.div f v = ∑ d, f d := by
    simp only [div]
    exact sum_fiberwise univ M.tail f
  have h2 : ∑ d, f d = ∑ d, f (M.rev d) := by
    have hbij : Function.Bijective M.rev := M.rev_injective.bijective_of_finite
    exact (sum_equiv (Equiv.ofBijective _ hbij) (by simp) (fun _ _ => rfl)).symm
  rw [h1]
  have : ∑ d, f (M.rev d) = - ∑ d, f d := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun d _ => hf d
  linarith

end CombMap

end PlanarFlow
