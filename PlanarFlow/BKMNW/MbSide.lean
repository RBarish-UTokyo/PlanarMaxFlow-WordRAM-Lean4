module

public import PlanarFlow.BKMNW.MbRun

/-!
# Miller's base: the two items of a separator are disjoint

The base case of `scertD` returns the items `sideItem (coreI C Z)` and `sideItem (coreO C Z)`
(the darts with an end strictly inside, resp. outside, the separator). A label array represents
items only when they are disjoint (`ItemRep`); for a cycle separator (`IsCycleSep`, as `SepFnOK`
provides it) no dart joins the two sides (`noEdge`), so the items are disjoint.

* **`sideItem_core_disj`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap PlanarSeparator PlanarSeparator.Map

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

open Classical in
/-- **The two items of a cycle separator are disjoint.** -/
theorem sideItem_core_disj {τ : Perm D} {N : Finset D} (hσ : Stable τ N)
    (hB : Stable (revPerm M) N) {C : (psep M hσ hB).stellar.SCycle}
    {Z : Finset (psep M hσ hB).stellar.Face}
    (hsep : IsCycleSep C Z (sideIn C Z) (sideOut C Z)) :
    Disjoint (sideItem hσ hB (coreI hσ hB C Z)) (sideItem hσ hB (coreO hσ hB C Z)) := by
  rw [Finset.disjoint_left]
  intro d h1 h2
  obtain ⟨h, a1⟩ := (mem_sideItem hσ hB).1 h1
  obtain ⟨h', a2⟩ := (mem_sideItem hσ hB).1 h2
  set x : SDart N := ⟨d, h⟩ with hx
  have hI : ∀ y : SDart N, Quotient.mk _ y ∈ coreI hσ hB C Z ↔
      (Sum.inl ((psep M hσ hB).vert y) : SVert τ N ⊕ (psep M hσ hB).Face) ∈ sideIn C Z :=
    fun y => by simp [coreI, psep_vert]
  have hO : ∀ y : SDart N, Quotient.mk _ y ∈ coreO hσ hB C Z ↔
      (Sum.inl ((psep M hσ hB).vert y) : SVert τ N ⊕ (psep M hσ hB).Face) ∈ sideOut C Z :=
    fun y => by simp [coreO, psep_vert]
  have hdis : ∀ v, v ∈ sideIn C Z → v ∉ sideOut C Z := fun v hv ho =>
    (mem_sideOut.1 ho).2 hv
  have hne : ∀ y : SDart N, (Sum.inl ((psep M hσ hB).vert y) : SVert τ N ⊕ _) ∈ sideIn C Z →
      (Sum.inl ((psep M hσ hB).vert ((psep M hσ hB).α y)) : SVert τ N ⊕ _) ∉ sideOut C Z :=
    fun y hy => by
      have := hsep.noEdge (StDart.old y) (by simpa using hy)
      simpa using this
  have hαα : (psep M hσ hB).α ((psep M hσ hB).α x) = x := (psep M hσ hB).α_α x
  rcases a1 with a1 | a1 <;> rcases a2 with a2 | a2
  · exact hdis _ ((hI x).1 a1) ((hO x).1 a2)
  · exact hne x ((hI x).1 a1) ((hO _).1 a2)
  · have := hne ((psep M hσ hB).α x) ((hI _).1 a1)
    rw [hαα] at this
    exact this ((hO x).1 a2)
  · exact hdis _ ((hI _).1 a1) ((hO _).1 a2)

end BKMNW

end PlanarFlow
