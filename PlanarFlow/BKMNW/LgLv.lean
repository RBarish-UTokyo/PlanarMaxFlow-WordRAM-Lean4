module

public import PlanarFlow.BKMNW.LgPar
public import PlanarFlow.BKMNW.ScLoc
public import PlanarFlow.BKMNW.ScFrame

/-!
# The large-piece separator, stage 5 (part): the input of the levels from stages 2–4

**`lvIn_of_stages`**: the arrays written by stage 2 (`lgPrep`: flags `NF = 1`, hole labels `TH`,
reverse indices `RV0`), stage 3 (`lgKey`: class keys `TK`, orbits of the rotation) and stage 4
(`lgWt`: the weights `EX`) on the enumeration `e'` of the piece map of the core `B` (rotation `τ`
with `PMap M B Hs τ`) are the input `LvIn M mem n' b e' B B Hs ex` of `scProgT_execK` (`N = B`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The input of the levels** from the arrays of stages 2–4. -/
theorem lvIn_of_stages {B : Finset D} {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint)
    {τ : Perm D} (hPM : PMap M B Hs τ) {e' : ℕ → D} {n' b : ℕ} {mem : ℕ → ℕ} {ex : D → ℕ}
    (he_mem : ∀ j < n', e' j ∈ B) (he_surj : ∀ y ∈ B, ∃ j < n', e' j = y)
    (he_inj : ∀ i < n', ∀ j < n', e' i = e' j → i = j)
    (hnf : ∀ j < n', mem (b + j) = 1)
    (hth : ∀ j < n', mem (b + n' + j) = hlab Hs (M.tail (e' j)))
    (hrv : ∀ j < n', mem (b + 2 * n' + j) < n' ∧ e' (mem (b + 2 * n' + j)) = M.rev (e' j))
    (htk : ∀ i < n', mem (b + 6 * n' + i) < n')
    (hkey : ∀ i < n', ∀ j < n', (mem (b + 6 * n' + i) = mem (b + 6 * n' + j) ↔
      τ.SameCycle (e' i) (e' j)))
    (hex : ∀ j < n', mem (b + 3 * n' + j) = ex (e' j)) :
    LvIn M mem n' b e' B B Hs ex where
  mem := he_mem
  surj := he_surj
  inj := he_inj
  sub := subset_refl _
  rv0 := hrv
  nf i hi := by rw [hnf i hi]; exact ⟨fun _ => he_mem i hi, fun _ => one_ne_zero⟩
  th i hi j hj := by rw [hth i hi]; exact hlab_eq_succ_iff hd hj
  tk := htk
  key := lgKey_hrel hPM he_mem hkey
  ex := hex

end MfDrv

end BKMNW

end PlanarFlow
