module

public import Mathlib.Order.Basic

/-!
# Undeprecated forms of `if_pos`, `if_neg`, `dif_pos` (as `itePos`/`iteNeg` of
`MuchaSankowski/MachineElimSpec.lean`, without its imports)
-/

@[expose] public section

namespace PlanarFlow

namespace BKMNW

theorem iteT {α : Sort*} {q : Prop} [Decidable q] (h : q) {a b : α} :
    (if q then a else b) = a := by simp [h]

theorem iteF {α : Sort*} {q : Prop} [Decidable q] (h : ¬ q) {a b : α} :
    (if q then a else b) = b := by simp [h]

theorem diteT {α : Sort*} {q : Prop} [Decidable q] (h : q) {a : q → α} {b : ¬ q → α} :
    (if h : q then a h else b h) = a h := by simp [h]

end BKMNW

end PlanarFlow
