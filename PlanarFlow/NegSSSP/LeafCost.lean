module

public import PlanarFlow.NegSSSP.LeafExec
public import PlanarFlow.BKMNW.MachCost

/-!
# The cost of the leaf: `O(m²)`

`lfCost_le`: `11 + lfCost m k w ≤ 2000 m² + 400` for `k, w ≤ 2m` (the test, `nmProg`, the
`w` rounds of Bellman–Ford over `m` arcs, the renormalization `O((m + w) log w)`), hence
**`leaf_cost_le`**: the leaf meets the hypothesis `hl` of the driver (`drive_msplit_node`) with
the machine costs `cNegMach C` (`leaf m = 96 m²`) for any `A ≥ 21`, `B ≥ 400`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset BKMNW

theorem heapLg_le (j : ℕ) : Heap.lg j ≤ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rw [Heap.lg]
    split_ifs with h
    · omega
    · have := ih (j / 2) (by omega); omega

theorem lfCost_le {m k w : ℕ} (hk : k ≤ 2 * m) (hw : w ≤ 2 * m) :
    11 + lfCost m k w ≤ 2000 * (m * m) + 400 := by
  unfold lfCost lbCost rnCost osCost dkC
  have hx := heapLg_le (2 * (w + 1))
  have e1 : w * (19 * m + 8) ≤ 2 * m * (19 * m + 8) := Nat.mul_le_mul_right _ hw
  have e2 : (w + 1) * (23 * Heap.lg (2 * (w + 1)) + 21) ≤
      (2 * m + 1) * (23 * (4 * m + 2) + 21) := Nat.mul_le_mul (by omega) (by omega)
  have e3 : (13 * Heap.lg (2 * (w + 1)) + 20) * (m + w) ≤ (13 * (4 * m + 2) + 20) * (3 * m) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith [e1, e2, e3, Nat.le_mul_self m]

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {N : CombMap D V F}

/-- **The leaf costs `O(m²)`**: the hypothesis `hl` of the driver with `cNegMach C`. -/
theorem leaf_cost_le (C : ℕ) {A B : ℕ} (hA : 21 ≤ A) (hB : 400 ≤ B) (P : Finset D) :
    11 + lfCost P.card (ck N P) (verts N P).card ≤ A * (cNegMach C).leaf P.card + B := by
  have h1 := lfCost_le (m := P.card) (k := ck N P) (w := (verts N P).card) (card_rcl_le P)
    (NTree.card_verts_le P)
  show _ ≤ A * (96 * P.card ^ 2) + B
  have : 2000 * (P.card * P.card) ≤ A * (96 * P.card ^ 2) := by
    rw [sq]
    have : 2000 * (P.card * P.card) ≤ 21 * (96 * (P.card * P.card)) := by omega
    exact this.trans (Nat.mul_le_mul_right _ hA)
  omega

end Frame

end NegSSSP

end PlanarFlow
