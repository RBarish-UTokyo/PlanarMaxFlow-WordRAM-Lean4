module

public import PlanarFlow.Plane.Potential

/-!
# Feasible flows in plane graphs via the dual

Let `M` be a plane map with capacities `u` on the darts. A *circulation* respecting the
capacities is an antisymmetric integer function `f` on the darts with zero net flow out of every
vertex and `f d ≤ u d` for every dart (so `-u (rev d) ≤ f d`: lower bounds are capacities of
reverse darts).

**Hassin's theorem** (`PlanarFlow.CombMap.circ_iff_potential`): such a circulation exists if and
only if there is a function `φ` on the faces with `φ (face (rev d)) ≤ φ (face d) + u d` for every
dart `d`, that is, a *feasible potential* for the dual graph whose arcs go from `face d` to
`face (rev d)` with length `u d`; and then `f = cob φ` is such a circulation. A feasible potential
exists if and only if the dual has no cycle of negative length, and then the distances from any
face (or the distances in the dual with a virtual source joined to every face at length `0`) are
one (`PlanarFlow/ShortestPath/BellmanFord.lean`).

**Supplies and demands** (Miller–Naor, `PlanarFlow.CombMap.bflow_iff_potential`). Given an
integer `b v` for every vertex (positive for a supply, negative for a demand), a *`b`-flow* is an
antisymmetric `f ≤ u` with net flow `b v` out of every vertex `v`. If `g` is any antisymmetric
function with net flow `b` (not necessarily respecting the capacities), then `f ↦ f - g` is a
bijection between `b`-flows and circulations respecting the capacities `u - g`; so a `b`-flow
exists if and only if the dual with lengths `u - g` has a feasible potential. On a connected
graph such a `g` exists as soon as the supplies and demands balance
(`PlanarFlow.CombMap.exists_base`), for instance along a spanning tree; and they must balance
for a `b`-flow to exist (`PlanarFlow.CombMap.sum_eq_zero_of_bflow`).

Every flow obtained in this way is integral: the face potentials are integers.

## References

* R. Hassin, *Maximum flow in (s,t) planar networks*, Inform. Process. Lett. 13 (1981), 107.
* G. L. Miller, J. Naor, *Flow in planar graphs with multiple sources and sinks*, SIAM J. Comput.
  24 (1995), 1002–1017.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

open Finset

namespace CombMap

variable {D V F : Type*} {M : CombMap D V F}
variable [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]

/-- **Hassin's theorem.** On a plane map, a circulation respecting the capacities `u` exists if
and only if the dual graph with lengths `u` has a feasible potential. -/
theorem circ_iff_potential (hM : M.IsPlane) (u : D → ℤ) :
    (∃ f, M.IsCirc f ∧ ∀ d, f d ≤ u d) ↔ ∃ φ, M.IsPotential u φ := by
  constructor
  · rintro ⟨f, hf, hu⟩
    obtain ⟨φ, hφ⟩ := exists_int_potential hM hf
    exact ⟨φ, fun d => hφ d ▸ hu d⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨M.cob φ, M.isCirc_cob φ, hφ⟩

lemma div_add (f g : D → ℤ) (v : V) : M.div (f + g) v = M.div f v + M.div g v := by
  simp [div, sum_add_distrib]

lemma div_sub (f g : D → ℤ) (v : V) : M.div (f - g) v = M.div f v - M.div g v := by
  simp [div, sum_sub_distrib]

/-- **Supplies and demands (Miller–Naor).** If `g` is antisymmetric with net flow `b`, a
`b`-flow respecting the capacities `u` exists if and only if the dual graph with lengths
`u - g` has a feasible potential `φ`; then `cob φ + g` is a `b`-flow. -/
theorem bflow_iff_potential (hM : M.IsPlane) {b : V → ℤ} (u : D → ℤ) {g : D → ℤ}
    (hg : M.IsAntisymm g) (hgb : ∀ v, M.div g v = b v) :
    (∃ f, M.IsBFlow b u f) ↔ ∃ φ, M.IsPotential (u - g) φ := by
  rw [← circ_iff_potential hM]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f - g, ⟨fun d => ?_, fun v => ?_⟩, fun d => ?_⟩
    · simp [hf.antisymm d, hg d]; ring
    · rw [div_sub, hf.div_eq, hgb, sub_self]
    · simp only [Pi.sub_apply]; linarith [hf.le_cap d]
  · rintro ⟨h, hh, hu⟩
    refine ⟨h + g, fun d => ?_, fun v => ?_, fun d => ?_⟩
    · simp [hh.antisymm d, hg d]; ring
    · rw [div_add, hh.div_eq, hgb, zero_add]
    · have := hu d; simp only [Pi.sub_apply] at this; simp only [Pi.add_apply]; linarith

/-- The supplies and demands of a `b`-flow balance. -/
theorem sum_eq_zero_of_bflow {b : V → ℤ} {u f : D → ℤ} (hf : M.IsBFlow b u f) :
    ∑ v, b v = 0 := by
  rw [← M.sum_div hf.antisymm]
  exact sum_congr rfl fun v _ => (hf.div_eq v).symm

/-- The antisymmetric function of a single dart. -/
lemma div_dart (d : D) (v : V) :
    M.div (Pi.single d 1 - Pi.single (M.rev d) 1) v =
      (if M.tail d = v then 1 else 0) - (if M.head d = v then 1 else 0) := by
  rw [div_sub]
  simp only [div, sum_filter, Pi.single_apply]
  have key : ∀ e : D, (∑ a, if M.tail a = v then (if a = e then (1 : ℤ) else 0) else 0) =
      if M.tail e = v then 1 else 0 := by
    intro e
    rw [Finset.sum_eq_single e]
    · simp
    · intro a _ ha; simp [ha]
    · simp
  rw [key, key]
  rfl

lemma isAntisymm_dart (d : D) : M.IsAntisymm (Pi.single d 1 - Pi.single (M.rev d) 1) := by
  intro x
  simp only [Pi.sub_apply, Pi.single_apply]
  by_cases h1 : M.rev x = d
  · subst h1
    simp [M.rev_rev, M.rev_ne x, (M.rev_ne x).symm]
  · by_cases h2 : x = d
    · subst h2; simp [M.rev_ne x, (M.rev_ne x).symm]
    · have h3 : M.rev x ≠ M.rev d := fun h => h2 (M.rev_injective h)
      have h4 : x ≠ M.rev d := fun h => h1 (by rw [h, M.rev_rev])
      simp [h1, h2, h3, h4]

/-- **A base flow.** On a connected map, if the supplies and demands balance, there is an
antisymmetric integer function with net flow `b`. -/
theorem exists_base (hc : ∀ a c, Relation.ReflTransGen M.Adj a c) {b : V → ℤ}
    (hb : ∑ v, b v = 0) : ∃ g, M.IsAntisymm g ∧ ∀ v, M.div g v = b v := by
  by_cases hV : Nonempty V
  · obtain ⟨v₀⟩ := hV
    have hpair : ∀ y, ∃ g, M.IsAntisymm g ∧ ∀ v, M.div g v =
        (if v₀ = v then 1 else 0) - (if y = v then 1 else 0) := by
      intro y
      induction hc v₀ y with
      | refl => exact ⟨0, fun d => by simp, fun v => by simp [div]⟩
      | @tail a c _ hac ih =>
        obtain ⟨g, hg, hgd⟩ := ih
        obtain ⟨d, rfl, rfl⟩ := hac
        refine ⟨g + (Pi.single d 1 - Pi.single (M.rev d) 1), fun x => ?_, fun v => ?_⟩
        · have := M.isAntisymm_dart d x
          simp only [Pi.add_apply] at this ⊢
          rw [hg x, this]; ring
        · rw [div_add, hgd, div_dart]; ring
    choose g hg hgd using hpair
    refine ⟨-∑ y, b y • g y, fun x => ?_, fun v => ?_⟩
    · simp only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hg _ x, mul_neg,
        sum_neg_distrib, neg_neg]
    · have hlin : ∀ (s : Finset V) (h : V → D → ℤ), M.div (∑ y ∈ s, h y) v =
          ∑ y ∈ s, M.div (h y) v := by
        intro s h
        simp only [div, Finset.sum_apply]
        exact sum_comm
      have hneg : ∀ h : D → ℤ, M.div (-h) v = - M.div h v := by
        intro h; simp [div, sum_neg_distrib]
      have hsmul : ∀ (c : ℤ) (h : D → ℤ), M.div (c • h) v = c * M.div h v := by
        intro c h; simp [div, mul_sum]
      rw [hneg, hlin]
      simp only [hsmul, hgd, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib]
      have : ∑ y, (if v₀ = v then b y else 0) = 0 := by
        split_ifs
        · exact hb
        · simp
      simp only [sum_ite_eq', mem_univ, ite_true, this]; ring
  · exact ⟨0, fun d => by simp, fun v => (hV ⟨v⟩).elim⟩

/-- **Feasibility of supplies and demands.** On a plane map, a `b`-flow respecting the capacities
`u` exists if and only if the supplies and demands balance and, for one (equivalently every)
antisymmetric `g` with net flow `b`, the dual graph with lengths `u - g` has a feasible
potential. -/
theorem bflow_iff (hM : M.IsPlane) (b : V → ℤ) (u : D → ℤ) :
    (∃ f, M.IsBFlow b u f) ↔ ∑ v, b v = 0 ∧
      ∀ g, M.IsAntisymm g → (∀ v, M.div g v = b v) → ∃ φ, M.IsPotential (u - g) φ := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨sum_eq_zero_of_bflow hf, fun g hg hgb => (bflow_iff_potential hM u hg hgb).1 ⟨f, hf⟩⟩
  · rintro ⟨hb, h⟩
    obtain ⟨g, hg, hgb⟩ := exists_base hM.conn hb
    exact (bflow_iff_potential hM u hg hgb).2 (h g hg hgb)

end CombMap

end PlanarFlow
