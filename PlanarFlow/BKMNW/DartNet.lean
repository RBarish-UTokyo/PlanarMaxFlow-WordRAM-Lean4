module

public import PlanarFlow.BKMNW.Model
public import PlanarFlow.Flow.Network

/-!
# Flows on darts and flows on arcs

Flows on darts (antisymmetric functions, `PlanarFlow/BKMNW/Model.lean`) are related to flows on
the arcs of `PlanarFlow.Network` by `ofNet x d = x d - x (rev d)`: the net outflows agree
(`div_ofNet`), and a flow within the capacities `r` of the network on the darts gives an
antisymmetric flow within `r` (`ofNet_le`). Used for bipartite matching
(`PlanarFlow/BKMNW/Matching.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable {M : CombMap D V F}

/-! ### Flows on darts and flows on arcs -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable {M : CombMap D V F}

variable (M) in
/-- The network on the darts of `M` with capacities `r`. -/
def dartNet (r : D → ℤ) : Network V D := ⟨M.tail, M.head, r⟩

variable (M) in
/-- The antisymmetric flow of a flow on the darts. -/
def ofNet (x : D → ℤ) (d : D) : ℤ := x d - x (M.rev d)

lemma ofNet_antisymm (x : D → ℤ) : M.IsAntisymm (ofNet M x) := fun d => by
  simp [ofNet, M.rev_rev]

lemma ofNet_le {r x : D → ℤ} {S T : Finset V} (hx : (dartNet M r).IsFlow S T x) (d : D) :
    ofNet M x d ≤ r d := by
  have := hx.nonneg (M.rev d); have := hx.le_cap d
  simp only [ofNet, dartNet] at *; linarith

/-- The net outflows of a flow on the darts and of its antisymmetric flow agree. -/
lemma div_ofNet (r x : D → ℤ) (v : V) : M.div (ofNet M x) v = (dartNet M r).netOut x v := by
  unfold CombMap.div Network.netOut ofNet
  rw [sum_sub_distrib]
  congr 1
  refine sum_nbij' M.rev M.rev ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    show M.tail (M.rev (M.rev a)) = v
    rw [M.rev_rev]; exact ha
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    exact ha
  · intro a _; exact M.rev_rev a
  · intro a _; exact M.rev_rev a
  · intro a _; rfl

lemma sum_div_ofNet (r x : D → ℤ) (X : Finset V) :
    ∑ v ∈ X, M.div (ofNet M x) v = (dartNet M r).flowAcross x X := by
  simp only [div_ofNet r x]; exact (dartNet M r).sum_netOut x X

end BKMNW

end PlanarFlow
