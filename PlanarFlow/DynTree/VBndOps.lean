module

public import PlanarFlow.DynTree.CmpRun

/-!
# Dynamic trees: bounds of the values along a list of operations

`VBnd V n F` (`PlanarFlow/DynTree/CmpZip.lean`): the two values of every node `< n` are at most
`V` in absolute value. The operations change the values only by the additions on a root path:

* `VBnd.mono`, `vbnd_link`, `vbnd_cut`, `vbnd_evert` (the values are swapped on the path),
  `vbnd_addPath`, `vbnd_addPath2` (`V + |z|`), `vbnd_set`, `vbnd_set2` (an addition at a root
  changes only the root: the bound of its new value);
* `EOp.zabs`: `|z|` for an addition, `0` otherwise; `vbnd_apply`: `V + zabs o` after `o`;
  `vbnd_runOps`, `allV_of_vbnd`: along a list, `V + Σ zabs` (`zsum`) bounds every forest
  (`AllV`, the condition of `ropsS_orunC`);
* `allV_append`, `AllV.mono`, `AllV.left`, `AllV.right`: the condition along a concatenation.
-/

@[expose] public section

namespace PlanarFlow

namespace DynTree

section
variable {V V' : ℝ} {n : ℕ} {F : Forest}

lemma VBnd.mono (h : VBnd V n F) (hV : V ≤ V') : VBnd V' n F := fun u hu =>
  ⟨(h u hu).1.trans hV, (h u hu).2.trans hV⟩

lemma VBnd.nonneg (h : VBnd V n F) (hn : 0 < n) : 0 ≤ V := (abs_nonneg _).trans (h 0 hn).1

lemma vbnd_link (h : VBnd V n F) (v w : ℕ) : VBnd V n (link F v w) := h

lemma vbnd_cut (h : VBnd V n F) (v : ℕ) : VBnd V n (cut F n v) := h

lemma vbnd_evert (h : VBnd V n F) (v : ℕ) : VBnd V n (evert F n v) := fun u hu => by
  simp only [evert]
  split_ifs
  · exact ⟨(h u hu).2, (h u hu).1⟩
  · exact h u hu

lemma vbnd_addPath (h : VBnd V n F) (v : ℕ) (z : ℝ) : VBnd (V + |z|) n (addPath F n v z) :=
  fun u hu => by
  simp only [addPath]
  refine ⟨?_, (h u hu).2.trans (le_add_of_nonneg_right (abs_nonneg _))⟩
  split_ifs
  · exact (abs_add_le _ _).trans (add_le_add_left (h u hu).1 _ |>.trans_eq' rfl |>.trans
      (by linarith [(h u hu).1]))
  · exact (h u hu).1.trans (le_add_of_nonneg_right (abs_nonneg _))

lemma vbnd_addPath2 (h : VBnd V n F) (v : ℕ) (z : ℝ) : VBnd (V + |z|) n (addPath2 F n v z) :=
  fun u hu => by
  simp only [addPath2]
  refine ⟨(h u hu).1.trans (le_add_of_nonneg_right (abs_nonneg _)), ?_⟩
  split_ifs
  · exact (abs_add_le _ _).trans (by linarith [(h u hu).2])
  · exact (h u hu).2.trans (le_add_of_nonneg_right (abs_nonneg _))

/-- An addition of `z'` to the first values on a path and of `z` to the second values on a path,
`|z'| ≤ |z|`. -/
lemma vbnd_addBoth (h : VBnd V n F) (v : ℕ) {z z' : ℝ} (hz : |z'| ≤ |z|) (w : ℕ) :
    VBnd (V + |z|) n (addPath2 (addPath F n v z') n w z) := fun u hu => by
  have h1 := (vbnd_addPath h v z' u hu).1
  have h2 : |F.val2 u| ≤ V := (h u hu).2
  refine ⟨h1.trans (by linarith), ?_⟩
  show |(if _ then F.val2 u + z else F.val2 u)| ≤ V + |z|
  split_ifs
  · exact (abs_add_le _ _).trans (by linarith)
  · exact h2.trans (le_add_of_nonneg_right (abs_nonneg _))

/-- An addition at a root sets the first value of the root only. -/
lemma vbnd_set (h : VBnd V n F) {v : ℕ} (hvn : v < n) (hp : F.par v = n) {z : ℝ}
    (hz : |F.val v + z| ≤ V) : VBnd V n (addPath F n v z) := fun u hu => by
  simp only [addPath, rootPath_root hvn hp, List.mem_singleton]
  refine ⟨?_, (h u hu).2⟩
  split_ifs with hu'
  · subst hu'; exact hz
  · exact (h u hu).1

/-- An addition at a root sets the second value of the root only. -/
lemma vbnd_set2 (h : VBnd V n F) {v : ℕ} (hvn : v < n) (hp : F.par v = n) {z : ℝ}
    (hz : |F.val2 v + z| ≤ V) : VBnd V n (addPath2 F n v z) := fun u hu => by
  simp only [addPath2, rootPath_root hvn hp, List.mem_singleton]
  refine ⟨(h u hu).1, ?_⟩
  split_ifs with hu'
  · subst hu'; exact hz
  · exact (h u hu).2

end

namespace EOp

/-- The size of the change of the values by an operation. -/
def zabs : EOp → ℝ
  | .add _ z => |(z : ℝ)|
  | .add2 _ z => |(z : ℝ)|
  | _ => 0

lemma zabs_nonneg (o : EOp) : 0 ≤ o.zabs := by
  cases o <;> simp [zabs]

end EOp

/-- The total size of the changes of the values along a list. -/
def zsum : List EOp → ℝ
  | [] => 0
  | o :: os => o.zabs + zsum os

lemma zsum_nonneg : ∀ os : List EOp, 0 ≤ zsum os
  | [] => le_rfl
  | o :: os => add_nonneg o.zabs_nonneg (zsum_nonneg os)

lemma zsum_append : ∀ os₁ os₂ : List EOp, zsum (os₁ ++ os₂) = zsum os₁ + zsum os₂
  | [], _ => by simp [zsum]
  | o :: os, os₂ => by simp [zsum, zsum_append os os₂]; ring

section
variable {V V' : ℝ} {n : ℕ}

lemma vbnd_apply {F : Forest} (h : VBnd V n F) (o : EOp) :
    VBnd (V + o.zabs) n (o.apply n F) := by
  cases o with
  | link v w => simpa [EOp.zabs, EOp.apply] using vbnd_link h v w
  | cut v => simpa [EOp.zabs, EOp.apply] using vbnd_cut h v
  | add v z => simpa [EOp.zabs, EOp.apply] using vbnd_addPath h v z
  | add2 v z => simpa [EOp.zabs, EOp.apply] using vbnd_addPath2 h v z
  | evert v => simpa [EOp.zabs, EOp.apply] using vbnd_evert h v
  | min v z => simpa [EOp.zabs, EOp.apply] using h
  | min2 v z => simpa [EOp.zabs, EOp.apply] using h
  | sum v => simpa [EOp.zabs, EOp.apply] using h
  | parent v => simpa [EOp.zabs, EOp.apply] using h

lemma vbnd_evertOp {F : Forest} (h : VBnd V n F) (v : ℕ) :
    VBnd V n (runOpsE n F [.evert v]).1 := vbnd_evert h v

lemma vbnd_runOps : ∀ (os : List EOp) {F : Forest} {V : ℝ}, VBnd V n F →
    VBnd (V + zsum os) n (runOpsE n F os).1
  | [], F, V, h => by simpa [zsum, runOpsE] using h
  | o :: os, F, V, h => by
    have := vbnd_runOps os (vbnd_apply h o)
    simp only [runOpsE, zsum]
    exact this.mono (by linarith)

lemma AllV.mono {F : Forest} : ∀ {os : List EOp}, AllV V n F os → V ≤ V' → AllV V' n F os
  | [], h, hV => VBnd.mono h hV
  | _ :: _, h, hV => ⟨h.1.mono hV, AllV.mono h.2 hV⟩

/-- **Along a list of operations, `V + Σ |z|` bounds every forest.** -/
lemma allV_of_vbnd : ∀ (os : List EOp) {F : Forest} {V : ℝ}, VBnd V n F →
    AllV (V + zsum os) n F os
  | [], F, V, h => by simpa [zsum, AllV] using h
  | o :: os, F, V, h => by
    refine ⟨h.mono (by linarith [zsum_nonneg (o :: os)]), ?_⟩
    have := allV_of_vbnd os (vbnd_apply h o)
    exact this.mono (by simp only [zsum]; linarith)

lemma allV_append : ∀ {F : Forest} (os₁ os₂ : List EOp), AllV V n F os₁ →
    AllV V n (runOpsE n F os₁).1 os₂ → AllV V n F (os₁ ++ os₂)
  | F, [], os₂, _, h₂ => by simpa [runOpsE] using h₂
  | F, o :: os, os₂, h₁, h₂ => ⟨h₁.1, allV_append os os₂ h₁.2 (by simpa [runOpsE] using h₂)⟩

lemma AllV.left : ∀ {F : Forest} {os₁ os₂ : List EOp}, AllV V n F (os₁ ++ os₂) → AllV V n F os₁
  | F, [], [], h => h
  | F, [], _ :: _, h => h.1
  | F, _ :: _, _, h => ⟨h.1, AllV.left h.2⟩

lemma AllV.right : ∀ {F : Forest} {os₁ os₂ : List EOp}, AllV V n F (os₁ ++ os₂) →
    AllV V n (runOpsE n F os₁).1 os₂
  | F, [], _, h => by simpa [runOpsE] using h
  | F, _ :: _, _, h => by simpa [runOpsE] using AllV.right h.2

/-- The forest after the operations is bounded when every forest along them is and the last
one is. -/
lemma AllV.last : ∀ {F : Forest} {os : List EOp}, AllV V n F os →
    (∀ o ∈ os.getLast?, VBnd V n (o.apply n (runOpsE n F os.dropLast).1)) →
    VBnd V n (runOpsE n F os).1
  | F, [], h, _ => h
  | F, [o], h, hl => by simpa [runOpsE] using hl o rfl
  | F, o :: o' :: os, h, hl => by
    have := AllV.last (F := o.apply n F) (os := o' :: os) h.2 (fun o₁ ho₁ => by
      have := hl o₁ (by simpa using ho₁)
      simpa [runOpsE, List.dropLast] using this)
    simpa [runOpsE] using this

end

end DynTree

end PlanarFlow
