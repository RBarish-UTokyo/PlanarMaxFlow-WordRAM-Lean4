module

public import PlanarFlow.Plane.Map
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod

/-!
# Pendant edges

Attaching a pendant edge at every vertex of a plane map keeps it plane. The vertex `v` gets a new
neighbour `v'` (`Sum.inr v`); the new edge has the darts `inr (v, true)` from `v` to `v'` and
`inr (v, false)` from `v'` to `v`. It is drawn in the corner of `v` just before a chosen dart
`e v` leaving `v`: along the boundary walk of the face of `e v`, the dart `a` entering `v` with
`next a = e v` is now followed by `v → v'`, then `v' → v`, then `e v`. The faces do not change,
and Euler's formula is preserved: one more vertex and one more edge for each vertex.

This is how vertex capacities enter a planar flow problem without losing planarity; it is used
for bipartite matching (`PlanarFlow/BKMNW/Matching.lean`).

* `PlanarFlow.CombMap.pendant`: the map with the pendant edges.
* `PlanarFlow.CombMap.pendant_isPlane`: it is plane when the map is.
* `PlanarFlow.CombMap.pendant_rotTrans`, `PlanarFlow.CombMap.pendant_faceTrans`
  (`PlanarFlow/BKMNW/Matching.lean`): it has transitive rotations and faces when the map has.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace CombMap

open Finset

variable {D V F : Type*} [DecidableEq D] (M : CombMap D V F) (e : V → D)

/-- The reversal of the darts of the map with pendant edges. -/
def pRev : D ⊕ (V × Bool) → D ⊕ (V × Bool)
  | .inl d => .inl (M.rev d)
  | .inr (v, b) => .inr (v, !b)

/-- The tails of the darts of the map with pendant edges. -/
def pTail : D ⊕ (V × Bool) → V ⊕ V
  | .inl d => .inl (M.tail d)
  | .inr (v, true) => .inl v
  | .inr (v, false) => .inr v

/-- The faces of the darts of the map with pendant edges. -/
def pFace : D ⊕ (V × Bool) → F
  | .inl d => M.face d
  | .inr (v, _) => M.face (e v)

/-- The boundary walks of the map with pendant edges. -/
def pNext : D ⊕ (V × Bool) → D ⊕ (V × Bool)
  | .inl d => if M.next d = e (M.head d) then .inr (M.head d, true) else .inl (M.next d)
  | .inr (v, true) => .inr (v, false)
  | .inr (v, false) => .inl (e v)

variable {M e}

lemma pNext_injective (he : ∀ v, M.tail (e v) = v) : Function.Injective (pNext M e) := by
  have hhead : ∀ d, M.tail (M.next d) = M.head d := fun d => M.tail_next d
  intro x y h
  match x, y with
  | .inl d, .inl d' =>
    by_cases h1 : M.next d = e (M.head d) <;> by_cases h2 : M.next d' = e (M.head d') <;>
      simp only [pNext, h1, h2, ite_true, ite_false, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq,
        Prod.mk.injEq, and_true] at h
    all_goals first
      | exact congrArg Sum.inl (M.next_injective (by rw [h1, h2, h]))
      | exact congrArg Sum.inl (M.next_injective h)
  | .inl d, .inr (v', true) =>
    by_cases h1 : M.next d = e (M.head d) <;>
      simp only [pNext, h1, ite_true, ite_false, reduceCtorEq, Sum.inr.injEq, Prod.mk.injEq,
        Bool.true_eq_false, and_false] at h
  | .inl d, .inr (v', false) =>
    by_cases h1 : M.next d = e (M.head d) <;>
      simp only [pNext, h1, ite_true, ite_false, reduceCtorEq, Sum.inl.injEq] at h
    exfalso; apply h1
    rw [h, show M.head d = v' by rw [← hhead d, h, he]]
  | .inr (v, true), .inl d' =>
    by_cases h1 : M.next d' = e (M.head d') <;>
      simp only [pNext, h1, ite_true, ite_false, reduceCtorEq, Sum.inr.injEq, Prod.mk.injEq,
        Bool.false_eq_true, and_false] at h
  | .inr (v, true), .inr (v', true) =>
    simp only [pNext] at h
    rw [(Prod.mk.inj (Sum.inr.inj h)).1]
  | .inr (v, true), .inr (v', false) => simp [pNext] at h
  | .inr (v, false), .inl d' =>
    by_cases h1 : M.next d' = e (M.head d') <;>
      simp only [pNext, h1, ite_true, ite_false, reduceCtorEq, Sum.inl.injEq] at h
    exfalso; apply h1
    rw [← h, show M.head d' = v by rw [← hhead d', ← h, he]]
  | .inr (v, false), .inr (v', true) => simp [pNext] at h
  | .inr (v, false), .inr (v', false) =>
    simp only [pNext] at h
    have h2 := Sum.inl.inj h
    rw [show v = v' by rw [← he v, h2, he]]

variable (M e) in
/-- **The map with a pendant edge at every vertex**, each drawn just before the dart `e v`. -/
def pendant (he : ∀ v, M.tail (e v) = v) : CombMap (D ⊕ (V × Bool)) (V ⊕ V) F where
  rev := pRev M
  rev_rev x := by rcases x with d | ⟨v, b⟩ <;> simp [pRev, M.rev_rev]
  rev_ne x := by rcases x with d | ⟨v, _ | _⟩ <;> simp [pRev, M.rev_ne]
  tail := pTail M
  face := pFace M e
  next := pNext M e
  next_injective := pNext_injective he
  face_next x := by
    rcases x with d | ⟨v, _ | _⟩
    · show pFace M e (pNext M e (.inl d)) = M.face d
      simp only [pNext]
      split_ifs with h
      · show M.face (e (M.head d)) = M.face d
        rw [← h, M.face_next]
      · show M.face (M.next d) = M.face d
        exact M.face_next d
    · rfl
    · rfl
  tail_next x := by
    rcases x with d | ⟨v, _ | _⟩
    · show pTail M (pNext M e (.inl d)) = .inl (M.tail (M.rev d))
      simp only [pNext]
      split_ifs with h
      · rfl
      · show Sum.inl (M.tail (M.next d)) = _
        rw [M.tail_next]
    · show Sum.inl (M.tail (e v)) = Sum.inl v
      rw [he]
    · rfl

variable (he : ∀ v, M.tail (e v) = v)

@[simp] lemma pendant_tail_inl (d : D) : (M.pendant e he).tail (.inl d) = .inl (M.tail d) := rfl
@[simp] lemma pendant_rev_inl (d : D) : (M.pendant e he).rev (.inl d) = .inl (M.rev d) := rfl
@[simp] lemma pendant_rev_inr (v : V) (b : Bool) :
    (M.pendant e he).rev (.inr (v, b)) = .inr (v, !b) := rfl
@[simp] lemma pendant_tail_true (v : V) : (M.pendant e he).tail (.inr (v, true)) = .inl v := rfl
@[simp] lemma pendant_tail_false (v : V) : (M.pendant e he).tail (.inr (v, false)) = .inr v :=
  rfl
@[simp] lemma pendant_head_inl (d : D) : (M.pendant e he).head (.inl d) = .inl (M.head d) := rfl

/-- **Pendant edges keep a map plane.** -/
theorem pendant_isPlane [Fintype D] [Fintype V] [DecidableEq V] [Fintype F] (hM : M.IsPlane) :
    (M.pendant e he).IsPlane := by
  classical
  have hadj : ∀ a b, Relation.ReflTransGen (M.pendant e he).Adj (.inl a) (.inl b) := by
    intro a b
    refine Relation.ReflTransGen.lift Sum.inl (fun x y hxy => ?_) _ _ (hM.conn a b)
    obtain ⟨d, rfl, rfl⟩ := hxy
    exact ⟨.inl d, rfl, rfl⟩
  have hin : ∀ v, (M.pendant e he).Adj (.inl v) (.inr v) := fun v => ⟨.inr (v, true), rfl, rfl⟩
  have hout : ∀ v, (M.pendant e he).Adj (.inr v) (.inl v) := fun v => ⟨.inr (v, false), rfl, rfl⟩
  have hbase : ∀ x : V ⊕ V, ∃ v, Relation.ReflTransGen (M.pendant e he).Adj x (.inl v) ∧
      Relation.ReflTransGen (M.pendant e he).Adj (.inl v) x := by
    rintro (v | v)
    · exact ⟨v, .refl, .refl⟩
    · exact ⟨v, .single (hout v), .single (hin v)⟩
  refine ⟨?_, fun x y => ?_, fun x y => ?_, ?_⟩
  · obtain ⟨v⟩ := hM.nonempty; exact ⟨.inl v⟩
  · obtain ⟨a, hxa, -⟩ := hbase x
    obtain ⟨b, -, hby⟩ := hbase y
    exact hxa.trans ((hadj a b).trans hby)
  · refine Relation.ReflTransGen.mono (fun x y hxy => ?_) _ _ (hM.dualConn x y)
    obtain ⟨d, rfl, rfl⟩ := hxy
    exact ⟨.inl d, rfl, rfl⟩
  · have h1 : Fintype.card (V ⊕ V) = 2 * Fintype.card V := by
      rw [Fintype.card_sum]; ring
    have h2 : Fintype.card (D ⊕ (V × Bool)) / 2 = Fintype.card D / 2 + Fintype.card V := by
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
      exact Nat.add_mul_div_right _ _ (by norm_num)
    rw [h1, h2]
    have := hM.euler
    omega

end CombMap

end PlanarFlow
