module

public import PlanarFlow.BKMNW.MfSplitChild

/-!
# The split meets its field of `MfSpecR`

* `rSp sR x` (the room of the split at a call of `m` darts and `k` holes:
  `18 + 14 m + sR m k + 21 m + 4 k + 2`), `scp sT x` (its steps: `sT m + 500 m + 21 k + 600`).
* **`mfSplit_spec`**: for a separator program `sepP` meeting `SepPSpec` (the only parameter) and
  `Reach` closed under the child calls, the program `splitS sepP` meets the field `split` of
  `MfSpecR` for the frame predicates `FInL Reach`, with `G = True`, the room `rSp sR` and the
  steps `scp sT`: it ends with the frames of the two child calls `chL`, `chR` (their holes
  `childHoles`, their rotations `childRot`) at `h + 5` and `el + 5`.
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

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

variable (M) in
/-- The room of the split at a call. -/
noncomputable def rSp (sR : ℕ → ℕ → ℕ) (x : MCall M) : ℕ :=
  18 + 14 * (pdarts M x.1.piece x.2.1).card + sR (pdarts M x.1.piece x.2.1).card x.2.1.length +
    21 * (pdarts M x.1.piece x.2.1).card + 4 * x.2.1.length + 2

variable (M) in
/-- The steps of the split at a call. -/
noncomputable def scp (sT : ℕ → ℕ) (x : MCall M) : ℕ :=
  sT (pdarts M x.1.piece x.2.1).card + 500 * (pdarts M x.1.piece x.2.1).card +
    21 * x.2.1.length + 600

section Exec

variable {I : Input} {W : ℕ}

theorem spFin_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' s, Exec I W spFin c c' s ∧ s = 2 ∧ c'.nreg 2998 = c.nreg 6553 ∧
      c'.nreg 2999 = c.nreg 6597 ∧ (∀ x, x ≠ 2998 → x ≠ 2999 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold spFin
  exec_block
  all_goals try (have := hc.1 6553; have := hc.1 6597; omega)
  refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])

set_option maxHeartbeats 2000000 in
/-- **The split meets the field `split` of `MfSpecR`** (see the module docstring). -/
theorem mfSplit_spec {Reach : MCall M → Prop} {sepP : Stmt} {sT : ℕ → ℕ} {sR : ℕ → ℕ → ℕ}
    (hsep : SepPSpec M Reach gid u S T Z I W sepP sT sR)
    (hReach : ∀ l r π Hs σ, Reach ((.node l r π, Hs, σ) : MCall M) →
      Reach (chL M l r π Hs σ) ∧ Reach (chR M l r π Hs σ)) {Hb : ℕ} :
    ∀ l r π Hs σ d e h c, True → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → h + rSp M sR (.node l r π, Hs, σ) ≤ W →
    FInL M Reach gid u S T Z (.node l r π, Hs, σ) d e c →
    ∃ c' t el er, Exec I W (splitS sepP) c c' t ∧ t ≤ scp M sT (.node l r π, Hs, σ) ∧ True ∧
      DRegKeep c c' ∧ HeapKeep Hb h h h c c' ∧ c'.output = c.output ∧ c'.nreg 2998 = el ∧
      c'.nreg 2999 = er ∧ h + 5 ≤ el ∧ el + 5 ≤ er ∧ er ≤ h + rSp M sR (.node l r π, Hs, σ) ∧
      FInL M Reach gid u S T Z (chL M l r π Hs σ) (h + 5) el c' ∧
      FInL M Reach gid u S T Z (chR M l r π Hs σ) (el + 5) er c' := by
  intro l r π Hs σ d e h c _ hc r4 r5 r3 hd1 hde heh hroom hin
  have hin0 := hin
  obtain ⟨hR, hok, m, en, hL, hfs⟩ := hin0
  have hm : m = (pdarts M (l.piece ∪ r.piece) Hs).card := hL.card
  have hroom' : h + 18 + 14 * m + sR m Hs.length + 21 * m + 4 * Hs.length + 2 ≤ W := by
    dsimp only [rSp, ADec.piece] at hroom; rw [← hm] at hroom; omega
  have hfs' := hfs
  unfold fsz at hfs'
  obtain ⟨hRl, hRr⟩ := hReach l r π Hs σ hR
  obtain ⟨-, ⟨gl, gr, -⟩, -⟩ := hok
  -- the front
  obtain ⟨c₁, t₁, e₁, ht₁, hF1, dk1, mk1, o1⟩ := spFront_exec hsep c hc r4 r5 r3 heh hin hL hfs
    hroom'
  set Sb := h + 18 + 14 * m with hSb
  set Wb := h + 18 + 14 * m + 3 * m + Hs.length + 2 with hWb
  have hzL : c₁.nmem (d + 3) = Z := hF1.lay.hz
  -- the left child
  obtain ⟨c₂, s₂, e₂, hs₂, a60, a61, a63, a65, a67, a68, a69, a70, a71, a72, n2, m2, rr2, rm2,
    o2⟩ := spGlL_exec (I := I) c₁ e₁.wb_right hF1.r04 hF1.r03 hF1.regs.r10 hF1.regs.r35
    hF1.regs.r31 hF1.regs.r33 hF1.regs.r34 hF1.r48 hF1.regs.r54 hzL (by omega) (by omega)
  have hF2 : SpFront M gid u S T Z c₂ l r π Hs σ m en d h Sb Wb :=
    hF1.congr (fun x hx => n2 x (by unfold spReg at hx; omega)) (fun a _ => by rw [m2])
  rw [hF1.tl] at a71
  obtain ⟨c₃, t₃, e₃, ht₃, mcl, ixl, hmcl, h97l, hLl, mml, nnl, rrl, rml, ool⟩ :=
    spChild_core (I := I) c₂ e₂.wb_right hF2 hin.2.1 l subset_union_left gl.revClosed
    hF2.fl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) a60 a61 a63 a65
    a67 a68 a69 a70 a71 a72
  have hF3 : SpFront M gid u S T Z c₃ l r π Hs σ m en d h Sb Wb :=
    hF2.congr (fun x hx => nnl x (by rcases hx with hx | hx | hx | hx <;>
      (try unfold spReg at hx) <;> omega)) (fun a ha => mml a (by omega))
  -- the right child
  obtain ⟨c₄, s₄, e₄, hs₄, b53, b65, b69, b71, n4, m4, rr4, rm4, o4⟩ := spGlR_exec (I := I) c₃
    e₃.wb_right h97l hF3.regs.r32 hF3.regs.r54 (by omega) (by omega)
  have hF4 : SpFront M gid u S T Z c₄ l r π Hs σ m en d h Sb Wb :=
    hF3.congr (fun x hx => n4 x (by rcases hx with hx | hx | hx | hx <;>
      (try unfold spReg at hx) <;> omega)) (fun a _ => by rw [m4])
  rw [hF3.tr] at b71
  have R4 : ∀ x, (x = 6560 ∨ x = 6561 ∨ x = 6563 ∨ x = 6567 ∨ x = 6568 ∨ x = 6570 ∨
      x = 6572) → c₄.nreg x = c₂.nreg x := fun x hx => by
    rw [n4 x (by omega), nnl x (by omega)]
  obtain ⟨c₅, t₅, e₅, ht₅, mcr, ixr, hmcr, h97r, hLr, mmr, nnr, rrr, rmr, oor⟩ :=
    spChild_core (I := I) c₄ e₄.wb_right hF4 hin.2.1 r subset_union_right gr.revClosed
    hF4.fr (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [R4 _ (by omega)]; exact a60) (by rw [R4 _ (by omega)]; exact a61)
    (by rw [R4 _ (by omega)]; exact a63) b65 (by rw [R4 _ (by omega)]; exact a67)
    (by rw [R4 _ (by omega)]; exact a68) b69 (by rw [R4 _ (by omega)]; exact a70) b71
    (by rw [R4 _ (by omega)]; exact a72)
  obtain ⟨c₆, s₆, e₆, hs₆, f98, f99, n6, m6, rr6, rm6, o6⟩ := spFin_exec (I := I) c₅ e₅.wb_right
  have el_def : c₅.nreg 6553 = h + 5 + 4 + 7 * mcl := by rw [nnr _ (by omega), b53]
  refine ⟨c₆, _, h + 5 + 4 + 7 * mcl, h + 5 + 4 + 7 * mcl + 5 + 4 + 7 * mcr,
    .seq e₁ (.seq (.seq e₂ e₃) (.seq e₄ (.seq e₅ e₆))), ?_, trivial, fun x h1 h2 => ?_,
    fun a h1 h2 _ => ?_, by rw [o6, oor, o4, ool, o2, o1], by rw [f98, el_def], ?_, by omega,
    by omega, ?_, ⟨hRl, hin.2.1.chL, mcl, fun k => en (ixl k), ?_, by unfold fsz; omega⟩,
    ⟨hRr, hin.2.1.chR, mcr, fun k => en (ixr k), ?_, by unfold fsz; omega⟩⟩
  · dsimp only [scp, ADec.piece]; rw [← hm]; omega
  · rw [n6 x (by omega) (by omega), nnr x (by omega), n4 x (by omega), nnl x (by omega),
      n2 x (by omega)]
    exact dk1 x h1 h2
  · have k1 := mk1 a (by omega)
    refine ⟨?_, ?_⟩
    · rw [m6, mmr a (by omega), m4, mml a (by omega), m2, k1.1]
    · rw [rm6, rmr, rm4, rml, rm2, k1.2]
  · rw [f99, h97r]
  · dsimp only [rSp, ADec.piece]; rw [← hm]; omega
  · exact hLl.congr fun a h1 h2 => by rw [m6, mmr a (by omega), m4]
  · exact hLr.congr fun a h1 h2 => by rw [m6]
end Exec

end MfDrv

end BKMNW

end PlanarFlow
