module

public import PlanarFlow.DynTree.VBndOps

/-!
# Dynamic trees: a potential bounding the values of the forest

The compare-bounded runs (`ORunC`, `PlanarFlow/DynTree/CmpRun.lean`) need the values of the
forest bounded (`VBnd V n F`) before every operation. This file bounds them by the **potential**
`pot n F = Σ_{u < n} (|val u| + |val2 u|)`:

* `vbnd_pot`: `VBnd (pot n F) n F`;
* `pot_apply_le`: an operation raises the potential by at most `n |z|` (`z` its amount, `0` for
  the operations without amount); `evert`, `link`, `cut` keep it;
* `pot_add_root`, `pot_add2_root`: an addition at a root (a node whose root path is the node
  alone) raises it by at most the absolute value of the **new** value of the node: an addition
  `t - v` at a root of value `v` sets the value `t`, whatever `v` is;
* `AllV.append`, `AllV.final`, `allV_of_pot` (`AllV.mono`, `AllV.left`, `AllV.right` are in
  `VBndOps.lean`): the bound before every operation of a list.
-/

@[expose] public section

namespace PlanarFlow

namespace DynTree

open Finset

/-- **The potential** of a forest: the sum of the absolute values of the two values of the
nodes `< n`. -/
noncomputable def pot (n : ℕ) (F : Forest) : ℝ := ∑ u ∈ range n, (|F.val u| + |F.val2 u|)

/-- The amount of an operation (`0` for the operations without amount). -/
def EOp.amt : EOp → ℤ
  | .add _ z => |z|
  | .add2 _ z => |z|
  | _ => 0

/-- The total amount of a list of operations. -/
def amtSum (os : List EOp) : ℤ := (os.map EOp.amt).sum

lemma amt_nonneg (o : EOp) : 0 ≤ o.amt := by cases o <;> simp [EOp.amt]

lemma amtSum_nonneg (os : List EOp) : 0 ≤ amtSum os := by
  induction os with
  | nil => simp [amtSum]
  | cons o os ih =>
    simp only [amtSum, List.map_cons, List.sum_cons] at ih ⊢
    have := amt_nonneg o; omega

@[simp] lemma amtSum_nil : amtSum [] = 0 := rfl

@[simp] lemma amtSum_cons (o : EOp) (os : List EOp) : amtSum (o :: os) = o.amt + amtSum os := by
  simp [amtSum]

@[simp] lemma amtSum_append (os₁ os₂ : List EOp) :
    amtSum (os₁ ++ os₂) = amtSum os₁ + amtSum os₂ := by
  simp [amtSum]

lemma pot_nonneg (n : ℕ) (F : Forest) : 0 ≤ pot n F :=
  sum_nonneg fun u _ => by positivity

theorem vbnd_pot (n : ℕ) (F : Forest) : VBnd (pot n F) n F := by
  intro u hu
  have h := single_le_sum (f := fun u => |F.val u| + |F.val2 u|) (fun u _ => by positivity)
    (mem_range.2 hu)
  exact ⟨by have := abs_nonneg (F.val2 u); unfold pot; linarith,
    by have := abs_nonneg (F.val u); unfold pot; linarith⟩

lemma vbnd_of_pot {V : ℝ} {n : ℕ} {F : Forest} (h : pot n F ≤ V) : VBnd V n F :=
  (vbnd_pot n F).mono h

/-! ### The potential along the operations -/

lemma pot_congr {n : ℕ} {F F' : Forest}
    (h : ∀ u < n, |F'.val u| + |F'.val2 u| = |F.val u| + |F.val2 u|) : pot n F' = pot n F :=
  sum_congr rfl fun u hu => h u (mem_range.1 hu)

lemma pot_le_of {n : ℕ} {F F' : Forest} (δ : ℕ → ℝ)
    (h : ∀ u < n, |F'.val u| + |F'.val2 u| ≤ |F.val u| + |F.val2 u| + δ u) :
    pot n F' ≤ pot n F + ∑ u ∈ range n, δ u := by
  unfold pot
  rw [← sum_add_distrib]
  exact sum_le_sum fun u hu => h u (mem_range.1 hu)

lemma pot_addPath_le (F : Forest) (n v : ℕ) (δ : ℝ) :
    pot n (addPath F n v δ) ≤ pot n F + n * |δ| := by
  have h := pot_le_of (n := n) (F := F) (F' := addPath F n v δ) (fun _ => |δ|) fun u _ => by
    simp only [addPath]
    split_ifs
    · have := abs_add_le (F.val u) δ; linarith
    · have := abs_nonneg δ; linarith
  simpa using h

lemma pot_addPath2_le (F : Forest) (n v : ℕ) (δ : ℝ) :
    pot n (addPath2 F n v δ) ≤ pot n F + n * |δ| := by
  have h := pot_le_of (n := n) (F := F) (F' := addPath2 F n v δ) (fun _ => |δ|) fun u _ => by
    simp only [addPath2]
    split_ifs
    · have := abs_add_le (F.val2 u) δ; linarith
    · have := abs_nonneg δ; linarith
  simpa using h

lemma pot_evert (F : Forest) (n v : ℕ) : pot n (evert F n v) = pot n F :=
  pot_congr fun u _ => by
    simp only [evert]
    split_ifs
    · ring
    · rfl

/-- **An operation raises the potential by at most `n` times its amount.** -/
theorem pot_apply_le (n : ℕ) (F : Forest) (o : EOp) :
    pot n (o.apply n F) ≤ pot n F + n * (o.amt : ℝ) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  cases o with
  | link v w => simp [EOp.apply, EOp.amt, DynTree.link, pot]
  | cut v => simp [EOp.apply, EOp.amt, DynTree.cut, pot]
  | add v z =>
    have := pot_addPath_le F n v (z : ℝ)
    simp only [EOp.apply, EOp.amt, Int.cast_abs]; exact this
  | add2 v z =>
    have := pot_addPath2_le F n v (z : ℝ)
    simp only [EOp.apply, EOp.amt, Int.cast_abs]; exact this
  | evert v => simp [EOp.apply, EOp.amt, pot_evert]
  | min v z => simp [EOp.apply, EOp.amt]
  | min2 v z => simp [EOp.apply, EOp.amt]
  | sum v => simp [EOp.apply, EOp.amt]
  | parent v => simp [EOp.apply, EOp.amt]

theorem pot_runOpsE_le (n : ℕ) :
    ∀ (os : List EOp) (F : Forest), pot n (runOpsE n F os).1 ≤ pot n F + n * (amtSum os : ℝ)
  | [], F => by simp [runOpsE]
  | o :: os, F => by
    have h1 := pot_apply_le n F o
    have h2 := pot_runOpsE_le n os (o.apply n F)
    simp only [runOpsE, amtSum_cons, Int.cast_add]
    linarith

/-- The root path of a root is the root alone. -/
lemma rootPath_of_root {F : Forest} {n v : ℕ} (hv : v < n) (hp : F.par v = n) :
    rootPath F n v = [v] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [rootPath, upPath, hv, ↓reduceIte, hp]
  cases m with
  | zero => rfl
  | succ m => simp [upPath]

/-- **An addition at a root** changes the value of the root only. -/
theorem pot_add_root {F : Forest} {n v : ℕ} (hv : v < n) (hp : F.par v = n) (δ : ℝ) :
    pot n (addPath F n v δ) ≤ pot n F + |F.val v + δ| := by
  have h := pot_le_of (n := n) (F := F) (F' := addPath F n v δ)
    (fun u => if u = v then |F.val v + δ| else 0) fun u _ => by
      simp only [addPath, rootPath_of_root hv hp, List.mem_singleton]
      split_ifs with h
      · subst h; have := abs_nonneg (F.val u); linarith
      · simp
  rw [sum_ite_eq' (range n) v] at h
  simpa only [mem_range.2 hv, ↓reduceIte] using h

theorem pot_add2_root {F : Forest} {n v : ℕ} (hv : v < n) (hp : F.par v = n) (δ : ℝ) :
    pot n (addPath2 F n v δ) ≤ pot n F + |F.val2 v + δ| := by
  have h := pot_le_of (n := n) (F := F) (F' := addPath2 F n v δ)
    (fun u => if u = v then |F.val2 v + δ| else 0) fun u _ => by
      simp only [addPath2, rootPath_of_root hv hp, List.mem_singleton]
      split_ifs with h
      · subst h; have := abs_nonneg (F.val2 u); linarith
      · simp
  rw [sum_ite_eq' (range n) v] at h
  simpa only [mem_range.2 hv, ↓reduceIte] using h

/-! ### The bound before every operation of a list -/

theorem AllV.append {V : ℝ} {n : ℕ} : ∀ {F : Forest} {os₁ os₂ : List EOp},
    AllV V n F os₁ → AllV V n (runOpsE n F os₁).1 os₂ → AllV V n F (os₁ ++ os₂)
  | _, [], _, _, h₂ => h₂
  | _, _ :: _, _, h₁, h₂ => ⟨h₁.1, AllV.append h₁.2 h₂⟩

/-- The final forest of a list of bounded operations is bounded. -/
theorem AllV.final {V : ℝ} {n : ℕ} : ∀ {F : Forest} {os : List EOp},
    AllV V n F os → VBnd V n (runOpsE n F os).1
  | _, [], h => h
  | F, o :: os, h => AllV.final (F := o.apply n F) (os := os) h.2

/-- **The crude bound**: the forests along a list of operations of total amount `A` from a
forest of potential `p` have potential at most `p + n A`. -/
theorem allV_of_pot {V : ℝ} {n : ℕ} : ∀ {F : Forest} {os : List EOp},
    pot n F + n * (amtSum os : ℝ) ≤ V → AllV V n F os
  | F, [], h => vbnd_of_pot (by simpa using h)
  | F, o :: os, h => by
    have h1 := pot_apply_le n F o
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have ho : (0 : ℝ) ≤ o.amt := by exact_mod_cast amt_nonneg o
    have hs : (0 : ℝ) ≤ amtSum os := by exact_mod_cast amtSum_nonneg os
    simp only [amtSum_cons, Int.cast_add] at h
    refine ⟨vbnd_of_pot (by nlinarith), allV_of_pot (by nlinarith)⟩

end DynTree

end PlanarFlow
