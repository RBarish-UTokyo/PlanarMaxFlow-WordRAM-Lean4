module

public import PlanarFlow.BKMNW.StChoiceM
public import PlanarFlow.BKMNW.CsScale

/-!
# The step bound of the s-t flow call inside `c2sP` against the budget of `cMachS`

`stCallZ_lay` (`NcChs.lean`) runs the s-t flow call at a frame within
`stCostZ m (4 · pcoreB V F m (4 m + 1) + 3)` steps (`V`, `F` the vertices and faces of the piece
map, `m` its darts). Here:

* `stdCost_le`, `stCostZ_le` (`stCostZ m K ≤ 27 K + 4000 · m lg m + 30000`),
  `pcoreB_le` (`pcoreB V F m (4m+1) ≤ 2.3 · 10⁸ · m lg m` when `#V + #F ≤ m + 2`);
* **`stCostZ_pcore_le`**: `stCostZ m (4 · pcoreB V F m (4m+1) + 3) ≤ 3 · 10¹⁰ · m lg m` for
  `1 ≤ m`, `#V + #F ≤ m + 2` (Euler: `#V + #F = m / 2 + 2` on a plane map);
* **`stCostZ_le_stflow`**: hence at most `(cMachS C C₀).stflow m = 10¹⁵ · 504000000 · m lg m`
  (and, with room to spare, at most `10⁻⁵` of it: `10⁵ · stCostZ … ≤ stflow m`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open StCall NegSSSP STFlow

lemma hpCost_sPrmL : hpCost StFix.sPrmL = 475 := by decide +kernel
lemma hpCost_stClrL : hpCost stClrL = 22 := by decide +kernel
lemma hpCost_stInL : hpCost stInL = 66 := by decide +kernel
lemma hpCost_stLayL : hpCost stLayL = 285 := by decide +kernel

/-- `Nat.log 2 (16 m) = Nat.log 2 m + 4` for `1 ≤ m`. -/
lemma log_mul_sixteen {m : ℕ} (hm : 1 ≤ m) : Nat.log 2 (m * 2 * 2 * 2 * 2) = Nat.log 2 m + 4 := by
  rw [Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega),
    Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega)]

/-- `Heap.lg (2 (4 m + 1)) ≤ lg m + 4` for `1 ≤ m`. -/
lemma lg_eight_le {m : ℕ} (hm : 1 ≤ m) : Heap.lg (2 * (4 * m + 1)) ≤ lg m + 4 := by
  rw [Heap.lg_eq_log (by omega)]
  have h1 : 2 * (4 * m + 1) ≤ m * 2 * 2 * 2 * 2 := by omega
  have h2 : Nat.log 2 (2 * (4 * m + 1)) ≤ Nat.log 2 (m * 2 * 2 * 2 * 2) := Nat.log_mono_right h1
  rw [log_mul_sixteen hm] at h2
  unfold lg; omega

/-- `Nat.log 2 (4 m + 1) ≤ lg m + 3` for `1 ≤ m`. -/
lemma log_four_le {m : ℕ} (hm : 1 ≤ m) : Nat.log 2 (4 * m + 1) ≤ lg m + 3 := by
  have h1 : 4 * m + 1 ≤ m * 2 * 2 * 2 * 2 := by omega
  have h2 : Nat.log 2 (4 * m + 1) ≤ Nat.log 2 (m * 2 * 2 * 2 * 2) := Nat.log_mono_right h1
  rw [log_mul_sixteen hm] at h2
  unfold lg; omega

/-- The step bound of the Dijkstra stage of the s-t flow call. -/
lemma stdCost_le {m : ℕ} (hm : 1 ≤ m) :
    stdCost (4 * m + 1) m ≤ 1000 * (m * lg m) + 1000 := by
  have hL := lg_eight_le hm
  have hl1 := one_le_lg m
  unfold stdCost osCost
  generalize Heap.lg (2 * (4 * m + 1)) = L at hL ⊢
  have e1 : m * L ≤ m * (lg m + 4) := Nat.mul_le_mul_left m hL
  have e2 : m * (lg m + 4) ≤ 5 * (m * lg m) := by nlinarith
  have e3 : m ≤ m * lg m := Nat.le_mul_of_pos_right m (by omega)
  have e4 : lg m ≤ m * lg m := Nat.le_mul_of_pos_left _ (by omega)
  have e5 : (4 * m + 1) * (23 * L + 21) = 92 * (m * L) + 84 * m + 23 * L + 21 := by ring
  have e6 : (13 * L + 20) * m = 13 * (m * L) + 20 * m := by ring
  rw [e5, e6]
  omega

/-- **The step bound of the s-t flow call** without its core: linear plus `m lg m`. -/
lemma stCostZ_le {m : ℕ} (hm : 1 ≤ m) (K : ℕ) :
    stCostZ m K ≤ 27 * K + 4000 * (m * lg m) + 30000 := by
  have h1 := stdCost_le hm
  have e3 : m ≤ m * lg m := Nat.le_mul_of_pos_right m (one_le_lg m)
  unfold stCostZ costIn costE costD1 costA costB costC
  rw [hpCost_sPrmL, hpCost_stClrL, hpCost_stInL, hpCost_stLayL]
  omega

/-- **The core of the s-t flow call** (`pcoreB` with `4 m + 1` nodes) is `O(m lg m)` when the map
has at most `m + 2` vertices and faces. -/
lemma pcoreB_le (V F : Type*) [Fintype V] [Fintype F] {m : ℕ} (hm : 1 ≤ m)
    (hVF : Fintype.card V + Fintype.card F ≤ m + 2) :
    pcoreB V F m (4 * m + 1) ≤ 230000000 * (m * lg m) := by
  have hl1 := one_le_lg m
  have e3 : m ≤ m * lg m := Nat.le_mul_of_pos_right m (by omega)
  have hops : STFlow.pstOps (Fintype.card V) (Fintype.card F) m ≤ 176 * m := by
    unfold STFlow.pstOps; omega
  have hext : STFlow.pstExt (Fintype.card V) (Fintype.card F) m ≤ 500 * m := by
    unfold STFlow.pstExt; omega
  have hlog := log_four_le hm
  have hcost : DynTree.opCostE (4 * m + 1) ≤ 1300000 * lg m := by
    unfold DynTree.opCostE; omega
  have hprod : STFlow.pstOps (Fintype.card V) (Fintype.card F) m * DynTree.opCostE (4 * m + 1) ≤
      176 * m * (1300000 * lg m) := Nat.mul_le_mul hops hcost
  have e4 : 176 * m * (1300000 * lg m) = 228800000 * (m * lg m) := by ring
  unfold pcoreB
  omega

/-- **The s-t flow call of `c2sP` is within `3 · 10¹⁰ · m lg m` steps.** -/
theorem stCostZ_pcore_le (V F : Type*) [Fintype V] [Fintype F] {m : ℕ} (hm : 1 ≤ m)
    (hVF : Fintype.card V + Fintype.card F ≤ m + 2) :
    stCostZ m (4 * pcoreB V F m (4 * m + 1) + 3) ≤ 30000000000 * (m * lg m) := by
  have h1 := stCostZ_le hm (4 * pcoreB V F m (4 * m + 1) + 3)
  have h2 := pcoreB_le V F hm hVF
  have e3 : m ≤ m * lg m := Nat.le_mul_of_pos_right m (one_le_lg m)
  omega

/-- **The s-t flow call of `c2sP` fits the s-t flow budget of `cMachS`**, with a factor `10⁵` to
spare. -/
theorem stCostZ_le_stflow (V F : Type*) [Fintype V] [Fintype F] {m : ℕ} (hm : 1 ≤ m)
    (hVF : Fintype.card V + Fintype.card F ≤ m + 2) (C C₀ : ℕ) :
    100000 * stCostZ m (4 * pcoreB V F m (4 * m + 1) + 3) ≤ (cMachS C C₀).stflow m := by
  have h := stCostZ_pcore_le V F hm hVF
  show _ ≤ csK * (504000000 * (m * lg m))
  unfold csK
  omega

end NcStep

end BKMNW

end PlanarFlow
