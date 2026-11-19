module

public import PlanarSeparator.Machine.CompSepProg

/-!
# The separator of the square: facts behind the program

* `ltComp_congr`, `compSep_congr`: the separation of the components of `U` depends on the
  weights only through their values on `U` (so the program may leave other weights in its
  weight array).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

open Finset

section congr

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]


theorem ltComp_congr (R : Kasteleyn.RotationSystem G) (ord : List V) (hord : ∀ v, v ∈ ord)
    {C : Finset V} {w₁ w₂ : V → ℕ} (h : ∀ v ∈ C, w₁ v = w₂ v) :
    ltComp R ord C w₁ = ltComp R ord C w₂ := by
  have hin : ltIn R ord C w₁ = ltIn R ord C w₂ := by
    unfold ltIn
    congr 1
    funext i
    exact h _ ((mem_clist hord).1 (List.get_mem _ _))
  unfold ltComp
  rw [hin]


theorem ltComp_subset (R : Kasteleyn.RotationSystem G) (ord : List V) (hord : ∀ v, v ∈ ord)
    (C : Finset V) (w : V → ℕ) :
    (ltComp R ord C w).1 ⊆ C ∧ (ltComp R ord C w).2.1 ⊆ C ∧ (ltComp R ord C w).2.2 ⊆ C := by
  have hm : ∀ (p : Fin (clist ord C).length → Prop) [DecidablePred p],
      (univ.filter p).map (cemb ord C) ⊆ C := fun p _ x hx => by
    obtain ⟨i, -, rfl⟩ := mem_map.1 hx
    exact (mem_clist hord).1 (List.get_mem _ _)
  unfold ltComp
  split_ifs
  · exact ⟨subset_rfl, empty_subset _, empty_subset _⟩
  · exact ⟨hm _, hm _, hm _⟩

theorem sum_congr_sub {U S : Finset V} (hS : S ⊆ U) {w₁ w₂ : V → ℕ} (h : ∀ v ∈ U, w₁ v = w₂ v) :
    ∑ v ∈ S, w₁ v = ∑ v ∈ S, w₂ v := sum_congr rfl fun v hv => h v (hS hv)

theorem heavyC_congr (ord : List V) {U : Finset V} {w₁ w₂ : V → ℕ}
    (h : ∀ v ∈ U, w₁ v = w₂ v) : heavyC G ord U w₁ = heavyC G ord U w₂ := by
  unfold heavyC
  congr 2
  funext v
  rw [sum_congr_sub subset_rfl h, sum_congr_sub (comp_subset U v) h]

theorem kstar_congr (ord : List V) {U : Finset V} {w₁ w₂ : V → ℕ}
    (h : ∀ v ∈ U, w₁ v = w₂ v) : kstar G ord U w₁ = kstar G ord U w₂ := by
  unfold kstar
  simp only [sum_congr_sub subset_rfl h, sum_congr_sub (pre_subset ord U _) h]

theorem lightA_congr (ord : List V) {U : Finset V} {w₁ w₂ : V → ℕ}
    (h : ∀ v ∈ U, w₁ v = w₂ v) : lightA G ord U w₁ = lightA G ord U w₂ := by
  unfold lightA
  rw [kstar_congr ord h]
  split
  · rename_i v _
    rw [sum_congr_sub subset_rfl h, sum_congr_sub (comp_subset U v) h]
  · rfl

/-- **The separation of the components depends only on the weights on `U`.** -/
theorem compSep_congr (R : Kasteleyn.RotationSystem G) (ord : List V) (hord : ∀ v, v ∈ ord)
    {U : Finset V} {w₁ w₂ : V → ℕ} (h : ∀ v ∈ U, w₁ v = w₂ v) :
    compSep G (ltComp R ord) ord U w₁ = compSep G (ltComp R ord) ord U w₂ := by
  unfold compSep
  rw [heavyC_congr ord h, lightA_congr ord h]
  split
  · rename_i v _
    have hC : ∀ x ∈ comp G U v, w₁ x = w₂ x := fun x hx => h x (comp_subset U v hx)
    rw [ltComp_congr R ord hord hC]
    have hA := sum_congr_sub (U := comp G U v)
      (S := (ltComp R ord (comp G U v) w₂).2.1) ?_ hC
    have hB := sum_congr_sub (U := comp G U v)
      (S := (ltComp R ord (comp G U v) w₂).2.2) ?_ hC
    · rw [hA, hB]
    · exact (ltComp_subset R ord hord _ _).2.2
    · exact (ltComp_subset R ord hord _ _).2.1
  · rfl

end congr

end PlanarSeparator
