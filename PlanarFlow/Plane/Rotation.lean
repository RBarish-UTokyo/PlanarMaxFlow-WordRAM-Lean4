module

public import PlanarFlow.Plane.Feasible
public import Kasteleyn.Plane.Map

/-!
# Plane rotation systems are plane maps

A rotation system `M` of a simple graph `G` (`Kasteleyn.RotationSystem`) gives a combinatorial
map on the darts of `G`: the reverse of a dart is `Dart.symm`, its tail is `Dart.fst`, its face
is `M.face` and the next dart along the boundary walk of its face is `M.faceNext`
(`PlanarFlow.CombMap.ofRotation`). If `M` is plane (connected and Euler's formula), so is the map
(`PlanarFlow.CombMap.ofRotation_isPlane`); hence the flow theorems for plane maps apply to plane
rotation systems, for instance Hassin's theorem (`PlanarFlow.CombMap.ofRotation_circ_iff`).
-/

@[expose] public section

namespace PlanarFlow

namespace CombMap

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The combinatorial map of a rotation system. -/
def ofRotation (M : Kasteleyn.RotationSystem G) : CombMap G.Dart V M.Face where
  rev d := d.symm
  rev_rev d := Dart.symm_symm d
  rev_ne d := Dart.symm_ne d
  tail d := d.fst
  face := M.face
  next := M.faceNext
  next_injective := M.faceNext.injective
  face_next := M.face_faceNext
  tail_next d := by simp [M.fst_rot]

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- **Plane rotation systems give plane maps.** -/
theorem ofRotation_isPlane {M : Kasteleyn.RotationSystem G} (hM : M.IsPlane) :
    (ofRotation M).IsPlane := by
  have hG := hM.connected
  refine ⟨hG.nonempty, fun a b => ?_, fun x y => ?_, ?_⟩
  · exact Relation.ReflTransGen.mono (fun a b hab => ⟨⟨(a, b), hab⟩, rfl, rfl⟩) _ _
      ((reachable_iff_reflTransGen _ _).1 (hG.preconnected a b))
  · -- the dual is connected: induction over the darts
    have key : ∀ x₀ : M.Face, ∀ d : G.Dart,
        Relation.ReflTransGen (ofRotation M).DualAdj x₀ (M.face d) := by
      intro x₀ d
      obtain ⟨d₀, rfl⟩ := M.face_surjective x₀
      refine M.dart_induction hG (P := fun d => Relation.ReflTransGen (ofRotation M).DualAdj
        (M.face d₀) (M.face d)) (fun d hd => ?_) (fun d hd => hd.tail ⟨d, rfl, rfl⟩) .refl d
      rw [Kasteleyn.RotationSystem.face_rot]
      exact hd.tail ⟨d, rfl, rfl⟩
    obtain ⟨d, rfl⟩ := M.face_surjective y
    exact key x d
  · have h1 := hM.euler
    have h2 := G.dart_card_eq_twice_card_edges
    rw [h2, Nat.mul_div_cancel_left _ (by omega)]
    exact h1

/-- **Hassin's theorem for plane rotation systems.** A circulation in a plane graph respecting
capacities `u` on the darts exists if and only if the dual graph has a feasible potential. -/
theorem ofRotation_circ_iff {M : Kasteleyn.RotationSystem G} (hM : M.IsPlane)
    (u : G.Dart → ℤ) :
    (∃ f, (ofRotation M).IsCirc f ∧ ∀ d, f d ≤ u d) ↔
      ∃ φ : M.Face → ℤ, ∀ d, φ (M.face d.symm) - φ (M.face d) ≤ u d :=
  circ_iff_potential (ofRotation_isPlane hM) u

end CombMap

end PlanarFlow
