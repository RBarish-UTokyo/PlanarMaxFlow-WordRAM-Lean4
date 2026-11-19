module

public import PlanarFlow.DynTree.Adaptive

/-!
# Dynamic trees with evert: lists of register-operand operations

A straight list of the forest-changing register-operand blocks of
`PlanarFlow/DynTree/RegOps.lean`, each reading its operands from registers below `r160` (which
no block writes), runs as one `ORun`: the operations performed are those named by the registers
at the start.

* `ROp`: an operation with register operands (`link ra rb`, `cut ra`, `add ra rz`, `add2 ra rz`,
  `evert ra`; `rz` a real register holding an integer amount `zr rz`); `ROp.eop c zr`: the
  operation it performs from the configuration `c`.
* `ropsS_orun`: **a list of register-operand operations** whose operations are valid in turn is
  an `ORun` performing them, counted one operation each, with no further steps; it keeps the
  registers outside the scratch registers (`RegFr`) and the memory outside the structure.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs VT

/-- An operation of the structure with its operands in registers. -/
inductive ROp
  | link (ra rb : ℕ)
  | cut (ra : ℕ)
  | add (ra rz : ℕ)
  | add2 (ra rz : ℕ)
  | evert (ra : ℕ)

namespace ROp

/-- The block of a register-operand operation. -/
def stmt (B : ℕ) : ROp → Stmt
  | .link ra rb => regLinkS B ra rb
  | .cut ra => regCutS B ra
  | .add ra rz => regAddS B ra rz
  | .add2 ra rz => regAdd2S B ra rz
  | .evert ra => regEvertS B ra

/-- The operation performed from the configuration `c`, the real registers holding the integer
amounts `zr`. -/
def eop (c : Config) (zr : ℕ → ℤ) : ROp → EOp
  | .link ra rb => .link (c.nreg ra) (c.nreg rb)
  | .cut ra => .cut (c.nreg ra)
  | .add ra rz => .add (c.nreg ra) (zr rz)
  | .add2 ra rz => .add2 (c.nreg ra) (zr rz)
  | .evert ra => .evert (c.nreg ra)

/-- The operands are registers below `r160`, and the real ones hold their integer amounts. -/
def Ok (c : Config) (zr : ℕ → ℤ) : ROp → Prop
  | .link ra rb => ra < 160 ∧ rb < 160
  | .cut ra => ra < 160
  | .add ra rz => ra < 160 ∧ rz < 160 ∧ c.rreg rz = (zr rz : ℝ)
  | .add2 ra rz => ra < 160 ∧ rz < 160 ∧ c.rreg rz = (zr rz : ℝ)
  | .evert ra => ra < 160

lemma eop_congr {c c' : Config} (h : RegFr c c') (zr : ℕ → ℤ) {o : ROp} (ho : o.Ok c zr) :
    o.eop c' zr = o.eop c zr := by
  cases o with
  | link ra rb => simp only [eop, h.1 ra (by simp [Ok] at ho; omega), h.1 rb (by
      simp [Ok] at ho; omega)]
  | cut ra => simp only [eop, h.1 ra (by simp [Ok] at ho; omega)]
  | add ra rz => simp only [eop, h.1 ra (by simp [Ok] at ho; omega)]
  | add2 ra rz => simp only [eop, h.1 ra (by simp [Ok] at ho; omega)]
  | evert ra => simp only [eop, h.1 ra (by simp [Ok] at ho; omega)]

lemma ok_congr {c c' : Config} (h : RegFr c c') (zr : ℕ → ℤ) {o : ROp} (ho : o.Ok c zr) :
    o.Ok c' zr := by
  cases o with
  | link ra rb => exact ho
  | cut ra => exact ho
  | add ra rz => exact ⟨ho.1, ho.2.1, (h.2.1 rz (Or.inl ho.2.1)).trans ho.2.2⟩
  | add2 ra rz => exact ⟨ho.1, ho.2.1, (h.2.1 rz (Or.inl ho.2.1)).trans ho.2.2⟩
  | evert ra => exact ho

end ROp

/-- The blocks of a list of register-operand operations, one after the other. -/
def ropsS (B : ℕ) : List ROp → Stmt
  | [] => .skip
  | o :: os => .seq (o.stmt B) (ropsS B os)

section
variable {P : Input} {W B n : ℕ}

lemma LRun.lcte {s : Stmt} {c c' : Config} {G G' : List VT} {F' : Forest} {m g : ℕ}
    (h : LRun P W B n s c G c' F' G' m g) : LCTE B n F' G' c' := h.choose_spec.2.1

lemma LRun.wb {s : Stmt} {c c' : Config} {G G' : List VT} {F' : Forest} {m g : ℕ}
    (h : LRun P W B n s c G c' F' G' m g) : WordsBounded W c' := h.choose_spec.1.wb_right

/-- One register-operand operation. -/
theorem rop_orun (hW : B + 16 * (n + 1) ≤ W) {c : Config} (hc : WordsBounded W c) {F : Forest}
    {G : List VT} (hS : LCTE B n F G c) (zr : ℕ → ℤ) (o : ROp) (hok : o.Ok c zr)
    (hv : (o.eop c zr).Valid n F) :
    ∃ c' G', ORun P W B n (o.stmt B) c F G c' [o.eop c zr] G' 1 0 ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  cases o with
  | link ra rb =>
    exact regLink_orun hW hc hS (by simp [ROp.Ok] at hok; omega) rfl rfl hv.1 hv.2.1 hv.2.2.1
      hv.2.2.2
  | cut ra => exact regCut_orun hW hc hS rfl hv.1 hv.2
  | add ra rz => exact regAdd_orun hW hc hS rfl hok.2.2 hv
  | add2 ra rz => exact regAdd2_orun hW hc hS rfl hok.2.2 hv
  | evert ra => exact regEvert_orun hW hc hS rfl hv

/-- **A list of register-operand operations** is an `ORun` performing the operations named by
the registers at the start, counted one operation each. -/
theorem ropsS_orun (hW : B + 16 * (n + 1) ≤ W) (zr : ℕ → ℤ) :
    ∀ (os : List ROp) {c : Config}, WordsBounded W c → ∀ {F : Forest} {G : List VT},
      LCTE B n F G c → (∀ o ∈ os, o.Ok c zr) → ValidOpsE n F (os.map (ROp.eop c zr)) →
      ∃ c' G', ORun P W B n (ropsS B os) c F G c' (os.map (ROp.eop c zr)) G' os.length 0 ∧
        MemFrame B n (mem c) (mem c') ∧ RegFr c c'
  | [], c, hc, F, G, hS, _, _ =>
    ⟨c, G, ⟨trivial, LRun.skip hc hS⟩, MemFrame.refl B n _, RegFr.refl c⟩
  | o :: os, c, hc, F, G, hS, hok, hv => by
    obtain ⟨c₁, G₁, h₁, hm₁, hf₁⟩ := rop_orun (P := P) hW hc hS zr o (hok o (by simp)) hv.1
    have hok₁ : ∀ o' ∈ os, o'.Ok c₁ zr := fun o' ho' =>
      ROp.ok_congr hf₁ zr (hok o' (by simp [ho']))
    have hmap : os.map (ROp.eop c₁ zr) = os.map (ROp.eop c zr) :=
      List.map_congr_left fun o' ho' => ROp.eop_congr hf₁ zr (hok o' (by simp [ho']))
    have hv₁ : ValidOpsE n ((o.eop c zr).apply n F) (os.map (ROp.eop c₁ zr)) := by
      rw [hmap]; exact hv.2
    obtain ⟨c₂, G₂, h₂, hm₂, hf₂⟩ := ropsS_orun hW zr os h₁.2.wb h₁.2.lcte hok₁ hv₁
    refine ⟨c₂, G₂, ?_, MemFrame.trans B n hm₁ hm₂, hf₁.trans hf₂⟩
    have h := ORun.seq h₁ (by rw [hmap] at h₂; exact h₂)
    simpa [ropsS, Nat.add_comm] using h

end

end DynTree

end PlanarFlow
