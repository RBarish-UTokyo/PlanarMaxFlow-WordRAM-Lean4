module

public import PlanarFlow.BKMNW.MfStepProg

/-!
# The step program `stepPO` meets `StepPSpec`

* `segBodyP_exec`: one part `j` of the separator (FixConservationOnPath, the hole loop, the two
  push-backs, `j := j + 1`) takes the flow `C.seg j` in `FL` to `C.seg (j + 1)` within
  `sgCost … j nH` steps (`nH` the holes of the part `j`).
* **`stepPO_spec`**: for subroutine programs meeting `CntPSpec`, `FixPSpec`, `C2SPSpec`,
  `S2CPSpec`, `RetPSpec`, `FrmPSpec` (the six calls of lines 9–13 of Algorithm 1, on the frame),
  `stepPO cntP fixP c2sP s2cP retP frmP` meets `StepPSpec` with the steps `stTO` and the room `rO`:
  from the joined flow of the children in `FL` it writes `cflow x`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs NegSSSP.Driver

universe w

section Run

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {I : Input} {W : ℕ}
  {O : PlaneOracles.{w}} {Reach : MCall M → Prop}
  {cntP fixP c2sP s2cP retP frmP : Stmt} {cnT rO : MCall M → ℕ}
  {fT rtT fmT : MCall M → ℕ → ℕ} {cT sT : MCall M → ℕ → ℕ → ℕ}

/-- **One part of the separator.** -/
theorem segBodyP_exec (hfx : FixPSpec M O Reach gid u S T Z I W fixP fT rO)
    (hc2 : C2SPSpec M O Reach gid u S T Z I W c2sP cT rO)
    (hs2 : S2CPSpec M O Reach gid u S T Z I W s2cP sT rO)
    (hrt : RetPSpec M O Reach gid u S T Z I W retP rtT rO)
    (hfm : FrmPSpec M O Reach gid u S T Z I W frmP fmT rO)
    {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D} (h : SCond M l r π Hs σ)
    {d e b m : ℕ} {en : ℕ → D} {j : ℕ}
    (hR : Reach (.node l r π, Hs, σ)) (hok : CallOk M S T (.node l r π, Hs, σ))
    (hde : d + fsz m ≤ e) (heb : e ≤ b) (hroom : b + rO (.node l r π, Hs, σ) ≤ W)
    (hj : j < (xCtx M O u S T l r π Hs σ h).L.length) {c₀ : Config}
    (hL₀ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₀.nmem)
    (r4 : c₀.nreg 3004 = d) (r5 : c₀.nreg 3005 = e) (r6 : c₀.nreg 3006 = b + 5) (c : Config)
    (hc : WordsBounded W c) (hS : StInv c₀ c d m b) (q0 : c.nreg 6800 = j)
    (q5 : c.nreg 6805 = 1)
    (q6 : c.nreg 6806 = (xCtx M O u S T l r π Hs σ h).Hs.length +
      (xCtx M O u S T l r π Hs σ h).L.length)
    (hfl : FLHas Z m d en c.nmem ((xCtx M O u S T l r π Hs σ h).seg j)) :
    ∃ c' t, Exec I W (segBodyP fixP c2sP s2cP retP frmP) c c' t ∧
      t ≤ sgCost fT cT sT rtT fmT (.node l r π, Hs, σ) j
        ((xCtx M O u S T l r π Hs σ h).Hs.length +
          ((xCtx M O u S T l r π Hs σ h).L.length - (j + 1))) ∧
      StInv c₀ c' d m b ∧ c'.nreg 6800 = j + 1 ∧
      (∀ x, 6800 ≤ x → x ≤ 6819 → x ≠ 6800 → x ≠ 6802 → x ≠ 6803 → c'.nreg x = c.nreg x) ∧
      FLHas Z m d en c'.nmem ((xCtx M O u S T l r π Hs σ h).seg (j + 1)) := by
  set C := xCtx M O u S T l r π Hs σ h with hC
  set πj := C.L[j] with hπj
  have hj' : C.L[j]? = some πj := List.getElem?_eq_getElem hj
  have hlen : (C.holes j).length = C.Hs.length + (C.L.length - (j + 1)) :=
    length_sHoles C.Hs C.L j
  -- FixConservationOnPath
  obtain ⟨c₁, t₁, e₁, ht₁, S₁, K₁, F₁⟩ := flow_step
    (hfx l r π Hs σ h d e b m en j πj hR hok hde heb hroom hj') hL₀ hde heb r4 r5 r6 c hc hS q0
    hfl
  -- the bound of the hole loop
  obtain ⟨c₂, t₂, e₂, ht₂, p2, p3, K₂, m₂, rr₂, rm₂, o₂⟩ := stH_exec (P := I) c₁ e₁.wb_right
    (N := C.Hs.length + C.L.length) (j := j)
    (by rw [K₁ _ (by omega) (by omega), q6]) (by rw [K₁ _ (by omega) (by omega), q0])
    (by rw [K₁ _ (by omega) (by omega), q5])
  have S₂ := S₁.of_block (fun x h1 h2 => K₂ x (by omega) (by omega)) m₂ rm₂ o₂
  have p3' : c₂.nreg 6803 = (C.holes j).length := by rw [p3, hlen]; omega
  have k2 : ∀ x, 6800 ≤ x → x ≤ 6819 → x ≠ 6802 → x ≠ 6803 → c₂.nreg x = c.nreg x :=
    fun x h1 h2 h3 h4 => by rw [K₂ x h3 h4, K₁ x h1 h2]
  -- the hole loop
  obtain ⟨c₃, t₃, e₃, ht₃, S₃, K₃, F₃⟩ := holeLoopP_exec hc2 hs2 h hR hok hde heb hroom hj' hL₀
    r4 r5 r6 c₂ e₂.wb_right S₂ (by rw [k2 _ (by omega) (by omega) (by omega) (by omega), q0])
    p2 p3' (by rw [k2 _ (by omega) (by omega) (by omega) (by omega), q5])
    (by rw [m₂]; exact F₁)
  have k3 : ∀ x, 6800 ≤ x → x ≤ 6819 → x ≠ 6802 → x ≠ 6803 → c₃.nreg x = c.nreg x :=
    fun x h1 h2 h3 h4 => by rw [K₃ x h1 h2 h3, k2 x h1 h2 h3 h4]
  -- the two push-backs
  obtain ⟨c₄, t₄, e₄, ht₄, S₄, K₄, F₄⟩ := flow_step
    (hrt l r π Hs σ h d e b m en j πj hR hok hde heb hroom hj') hL₀ hde heb r4 r5 r6 c₃
    e₃.wb_right S₃ (by rw [k3 _ (by omega) (by omega) (by omega) (by omega), q0]) F₃
  obtain ⟨c₅, t₅, e₅, ht₅, S₅, K₅, F₅⟩ := flow_step
    (hfm l r π Hs σ h d e b m en j πj hR hok hde heb hroom hj') hL₀ hde heb r4 r5 r6 c₄
    e₄.wb_right S₄ (by rw [K₄ _ (by omega) (by omega), k3 _ (by omega) (by omega) (by omega)
      (by omega), q0]) F₄
  have k5 : ∀ x, 6800 ≤ x → x ≤ 6819 → x ≠ 6802 → x ≠ 6803 → c₅.nreg x = c.nreg x :=
    fun x h1 h2 h3 h4 => by rw [K₅ x h1 h2, K₄ x h1 h2, k3 x h1 h2 h3 h4]
  have hjW : j + 1 ≤ W := by
    have := WordsBounded.nreg hc 6806
    rw [q6] at this; omega
  -- `j := j + 1`
  obtain ⟨c₆, t₆, e₆, ht₆, p0, K₆, m₆, rr₆, rm₆, o₆⟩ := stJ_exec (P := I) c₅ e₅.wb_right
    (by rw [k5 _ (by omega) (by omega) (by omega) (by omega), q0])
    (by rw [k5 _ (by omega) (by omega) (by omega) (by omega), q5]) hjW
  refine ⟨c₆, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ?_,
    S₅.of_block (fun x h1 h2 => K₆ x (by omega)) m₆ rm₆ o₆, p0,
    fun x h1 h2 h3 h4 h5 => by rw [K₆ x h3, k5 x h1 h2 h4 h5], ?_⟩
  · unfold sgCost
    rw [← hlen]
    rw [← hC] at ht₃
    omega
  · rw [m₆, C.seg_succ hj' (xCtx_touch O u S T h j)]
    exact F₅

/-- **The step program meets `StepPSpec`** (see the module docstring). -/
theorem stepPO_spec (hcn : CntPSpec M Reach gid u S T Z I W cntP cnT rO)
    (hfx : FixPSpec M O Reach gid u S T Z I W fixP fT rO)
    (hc2 : C2SPSpec M O Reach gid u S T Z I W c2sP cT rO)
    (hs2 : S2CPSpec M O Reach gid u S T Z I W s2cP sT rO)
    (hrt : RetPSpec M O Reach gid u S T Z I W retP rtT rO)
    (hfm : FrmPSpec M O Reach gid u S T Z I W frmP fmT rO) :
    StepPSpec M O Reach gid u S T Z I W (stepPO cntP fixP c2sP s2cP retP frmP)
      (stTO M cnT fT cT sT rtT fmT) rO := by
  intro l r π Hs σ d e b m en c hR hok hL hde hfl hc r4 r5 r6 heb hroom
  have h : SCond M l r π Hs σ := callOk_cond hok
  set C := xCtx M O u S T l r π Hs σ h with hC
  have hLs : C.L.length = π.segs.length := length_segsP h.1 π.segs h.2
  unfold fsz at hde
  -- the counts
  obtain ⟨c₁, t₁, e₁, ht₁, K₁, m₁, o₁, q1, q6⟩ := hcn l r π Hs σ d e b m en c hR hok hL
    (by unfold fsz; omega) heb hroom hc r4 r5 r6
  have S₁ : StInv c c₁ d m b :=
    ⟨fun x h1 h2 => K₁ x h1 h2, fun a h1 _ => m₁ a h1, o₁⟩
  have hfl₁ : FLHas Z m d en c₁.nmem (C.seg 0) := fun i hi => by
    rw [(m₁ _ (by omega)).1]; exact hfl i hi
  -- the initialization
  obtain ⟨c₂, t₂, e₂, ht₂, p5, p0, K₂, m₂, rr₂, rm₂, o₂⟩ := stA_exec (P := I) c₁ e₁.wb_right
    (by have := WordsBounded.nreg hc 3006; omega)
  have S₂ := S₁.of_block (fun x h1 h2 => K₂ x (by omega) (by omega)) m₂ rm₂ o₂
  -- the loop over the parts
  let J : ℕ → Config → Prop := fun j c' =>
    StInv c c' d m b ∧ c'.nreg 6805 = 1 ∧ c'.nreg 6806 = C.Hs.length + C.L.length ∧
      FLHas Z m d en c'.nmem (C.seg j)
  obtain ⟨c₃, t₃, e₃, ht₃, -, -, S₃, -, -, F₃⟩ := lnRangeV (P := I) (W := W) (a := 6800)
    (b := 6801) (body := segBodyP fixP c2sP s2cP retP frmP) J (lo := 0) (hi := C.L.length)
    (fun j => sgCost fT cT sT rtT fmT (.node l r π, Hs, σ) j
      (C.Hs.length + (C.L.length - (j + 1)))) c₂ e₂.wb_right p0
    (by rw [K₂ _ (by omega) (by omega), q1, hLs]) (Nat.zero_le _)
    ⟨S₂, p5, by rw [K₂ _ (by omega) (by omega), q6, hLs]; rfl, by rw [m₂]; exact hfl₁⟩
    (fun j c' _ hj hw a1 a2 ⟨Sj, s5, s6, Fj⟩ => by
      obtain ⟨c'', t, ex, ht, S', p0', K', F'⟩ := segBodyP_exec hfx hc2 hs2 hrt hfm h hR hok
        (by unfold fsz; omega) heb hroom hj hL r4 r5 r6 c' hw Sj a1 s5 s6 Fj
      exact ⟨c'', t, ex, ht, p0', by rw [K' _ (by omega) (by omega) (by omega) (by omega)
        (by omega), a2], S', by rw [K' _ (by omega) (by omega) (by omega) (by omega)
        (by omega), s5], by rw [K' _ (by omega) (by omega) (by omega) (by omega) (by omega),
        s6], F'⟩)
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), ?_, fun x h1 h2 => S₃.1 x h1 h2,
    fun a h1 h2 => S₃.2.1 a h1 h2, S₃.2.2, ?_⟩
  · show _ ≤ stCost cnT fT cT sT rtT fmT (.node l r π, Hs, σ) π.segs.length
      (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length
    unfold stCost
    rw [← hLs, range_eq_Ico]
    have : C.Hs = pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs := rfl
    rw [← this]
    omega
  · intro i hi
    rw [cflow_node_eq O u S T h, ← hLs]
    exact F₃ i hi

end Run

end MfDrv

end BKMNW

end PlanarFlow
