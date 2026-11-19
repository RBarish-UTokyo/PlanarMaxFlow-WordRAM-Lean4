module

public import PlanarFlow.BKMNW.SmXC

/-!
# The small separator program: the meaning of the children's data over the record

**`smSem_vals`**: from the record's arrays and the outputs of stage A (the flags of `l.piece`, of
the path's vertices `C` and of the holes meeting `C`), the machine's values of stage B over the
record's darts are the children's data: `smHC = hlab (childHoles Hs C) ∘ tail`,
`smKC = lrk S T (hunion (childHoles Hs C)) ∘ tail`, `smCF = bf (· ∈ pdarts l.piece (childHoles
Hs C))`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {ν : V → ℕ} {S T : Finset V}

set_option maxHeartbeats 1000000 in
/-- **The machine's values of stage B are the children's data** (see the module docstring). -/
theorem smSem_vals {x : MCall M} {m n R A : ℕ} {g : ℕ → D} {mem : ℕ → ℕ} {L : Finset D}
    {C : Finset V} (hA : RArr M gid ν S T x m n R g mem) (hd : x.2.1.Pairwise Disjoint)
    (hSC : Disjoint S C) (hTC : Disjoint T C) (hSA : Disjoint S (hunion x.2.1))
    (hLP : ∀ i < n, mem (A + n + i) = bf (g i ∈ L))
    (hCV : ∀ i < n, mem (A + 3 * n + i) = bf (M.tail (g i) ∈ C))
    (hHM : ∀ j < x.2.1.length, mem (A + 4 * n + j) = bf (¬ Disjoint (x.2.1.getD j ∅) C)) :
    (∀ i < n, smHC mem A R n x.2.1.length i = hlab (childHoles x.2.1 C) (M.tail (g i))) ∧
    (∀ i < n, smKC mem A R n i = lrk S T (hunion (childHoles x.2.1 C)) (M.tail (g i))) ∧
    (∀ i < n, smCF mem A R n x.2.1.length i = bf (g i ∈ pdarts M L (childHoles x.2.1 C))) := by
  -- the new hole
  have NH : ∀ i < n, smNH mem A R n i = bf (M.tail (g i) ∈ newHole x.2.1 C) := fun i hi => by
    rw [← nhF_eq hd]
    unfold smNH nhR
    rw [hCV i hi, hA.hp i hi]
    by_cases h2 : 0 < hlab x.2.1 (M.tail (g i))
    · have hl := hlab_le x.2.1 (M.tail (g i))
      rw [hHM _ (by clear * - h2 hl; omega)]
    · have h0 : hlab x.2.1 (M.tail (g i)) = 0 := by omega
      rw [h0]; unfold nhF; simp
  -- the count of the kept holes
  have CNT : ∀ j ≤ x.2.1.length, cnt (hfR mem (A + 4 * n)) j = hcnt x.2.1 C j := fun j hj => by
    rw [← cnt_hfF x.2.1 C hj]
    exact cnt_congr fun i hi => by unfold hfR; rw [hHM i (by clear * - hi hj; omega)]
  have HC : ∀ i < n, smHC mem A R n x.2.1.length i = hlab (childHoles x.2.1 C) (M.tail (g i)) :=
    fun i hi => by
      have hl := hlab_le x.2.1 (M.tail (g i))
      unfold smHC
      rw [NH i hi, hA.hp i hi, CNT _ le_rfl, CNT _ (by clear * - hl; omega)]
      exact hcF_eq hd _ (fun _ _ => rfl)
  refine ⟨HC, fun i hi => ?_, fun i hi => ?_⟩
  · unfold smKC
    rw [NH i hi, hA.kp i hi]
    exact kcF_eq hSC hTC hSA _
  · obtain ⟨r1, r2⟩ := hA.rp i hi
    unfold smCF
    rw [hLP i hi, HC i hi, HC _ r1, r2, CombMap.tail_rev, cfV_bf]
    refine bf_congr ?_
    rw [mem_pdarts, inner_iff_hlab (pairwise_childHoles hd)]

end MfDrv

end BKMNW

end PlanarFlow
