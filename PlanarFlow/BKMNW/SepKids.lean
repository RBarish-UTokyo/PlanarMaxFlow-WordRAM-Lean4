module

public import PlanarFlow.BKMNW.SepRec

/-!
# The front and the two child frames of the extended split

**`spKids_execX`**: `spFront sepP ; spChL ; spGlR ; sfChild` on the extended frame (the separator
program meeting `SepPSpecX`): the left child's frame at `h + 5`, the right child's at `el + 5`
(`el = r6553`), and the children's records written by the separator program from `Xb = r6501`
(`RecsOut`), within `sT n k + 497 m + 21 k + 540` steps.
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

variable {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {ds : DSys M}

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The front and the left child's frame of the extended split** (`spFront sepP ; spChL`). -/
theorem spKidL_execX {Reach : MCall M → Prop} {sepP : Stmt} {sT : ℕ → ℕ → ℕ}
    {sR : ℕ → ℕ → ℕ → ℕ}
    (hsep : SepPSpecX M ds Reach gid ν u S T Z I W sepP sT sR)
    {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D} {d e h m : ℕ} {en : ℕ → D}
    (c : Config) (hc : WordsBounded W c) (r4 : c.nreg 3004 = d) (r5 : c.nreg 3005 = e)
    (r3 : c.nreg 3003 = h) (heh : e ≤ h)
    (hin : FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c)
    (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem) (hfs : d + fsz m ≤ e)
    (hroom : h + 18 + 14 * m + sR (l.piece ∪ r.piece).card m Hs.length + 21 * m +
      4 * Hs.length + 2 ≤ W) :
    ∃ c₁ c₃ t₁ t₃, Exec I W (spFront sepP) c c₁ t₁ ∧ Exec I W spChL c₁ c₃ t₃ ∧
      t₁ + t₃ ≤ sT (l.piece ∪ r.piece).card Hs.length + 294 * m + 21 * Hs.length + 308 ∧
      SpFront M gid u S T Z c₃ l r π Hs σ m en d h (h + 18 + 14 * m)
        (h + 18 + 14 * m + 3 * m + Hs.length + 2) ∧
      c₃.nreg 6560 = m ∧ c₃.nreg 6561 = d ∧
      c₃.nreg 6563 = h + 18 + 14 * m + 3 * m + Hs.length + 2 + 5 * m ∧
      c₃.nreg 6567 = h + 18 + 14 * m + 3 * m + Hs.length + 2 + 3 * m ∧
      c₃.nreg 6568 = h + 18 + 14 * m + 3 * m + Hs.length + 2 + 4 * m ∧
      c₃.nreg 6570 = (childHoles Hs π.path.mverts).length ∧ c₃.nreg 6572 = Z ∧
      ∃ mcl : ℕ, ∃ ixl : ℕ → ℕ, mcl ≤ m ∧ c₃.nreg 6597 = h + 5 + 4 + 7 * mcl ∧
      Lay M gid u S T Z (chL M l r π Hs σ) mcl (fun k => en (ixl k)) (h + 5) c₃.nmem ∧
      RecsOut M ds gid ν S T l r π Hs σ (h + 18 + 14 * m + 21 * m + 4 * Hs.length + 2)
        (h + 18 + 14 * m + sR (l.piece ∪ r.piece).card m Hs.length) (c₃.nreg 6501) c₃.nmem ∧
      DRegKeep c c₃ ∧ (∀ a < h, c₃.nmem a = c.nmem a ∧ c₃.rmem a = c.rmem a) ∧
      c₃.output = c.output := by
  have hm : m = (pdarts M (l.piece ∪ r.piece) Hs).card := hL.card
  have hfs' := hfs
  unfold fsz at hfs'
  have hok := hin.2.1
  obtain ⟨-, ⟨gl, -, -⟩, -⟩ := hok
  -- the front
  obtain ⟨c₁, t₁, e₁, ht₁, hF1, dk1, mk1, o1, hRO⟩ := spFront_execX hsep c hc r4 r5 r3 heh hin
    hL hfs hroom
  set Sb := h + 18 + 14 * m with hSb
  set Wb := h + 18 + 14 * m + 3 * m + Hs.length + 2 with hWb
  have hX1 := hRO.1
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
  have x01 : c₃.nreg 6501 = c₁.nreg 6501 := by rw [nnl _ (by omega), n2 _ (by omega)]
  refine ⟨c₁, c₃, t₁, s₂ + t₃, e₁, .seq e₂ e₃, by omega, hF3, by rw [nnl _ (by omega)]; exact a60,
    by rw [nnl _ (by omega)]; exact a61, by rw [nnl _ (by omega)]; exact a63,
    by rw [nnl _ (by omega)]; exact a67, by rw [nnl _ (by omega)]; exact a68,
    by rw [nnl _ (by omega)]; exact a70, by rw [nnl _ (by omega)]; exact a72,
    mcl, ixl, hmcl, h97l, hLl, ?_, fun x h1 h2 => ?_, fun a ha => ?_, by rw [ool, o2, o1]⟩
  · rw [x01]
    exact hRO.congr fun a h1 h2 => by rw [mml a (by omega), m2]
  · rw [nnl x (by omega), n2 x (by omega)]
    exact dk1 x h1 h2
  · have k1 := mk1 a (by omega)
    refine ⟨?_, ?_⟩
    · rw [mml a (by omega), m2, k1.1]
    · rw [rml, rm2, k1.2]

set_option maxHeartbeats 4000000 in
/-- **The right child's frame of the extended split** (`spGlR ; sfChild`), from the state after
`spKidL_execX`. -/
theorem spKidR_execX {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    {d h m mcl : ℕ} {en : ℕ → D} {lo hi : ℕ} (c₃ : Config) (hc : WordsBounded W c₃)
    (hF3 : SpFront M gid u S T Z c₃ l r π Hs σ m en d h (h + 18 + 14 * m)
        (h + 18 + 14 * m + 3 * m + Hs.length + 2))
    (hok : CallOk M S T (.node l r π, Hs, σ))
    (a60 : c₃.nreg 6560 = m) (a61 : c₃.nreg 6561 = d)
    (a63 : c₃.nreg 6563 = h + 18 + 14 * m + 3 * m + Hs.length + 2 + 5 * m)
    (a67 : c₃.nreg 6567 = h + 18 + 14 * m + 3 * m + Hs.length + 2 + 3 * m)
    (a68 : c₃.nreg 6568 = h + 18 + 14 * m + 3 * m + Hs.length + 2 + 4 * m)
    (a70 : c₃.nreg 6570 = (childHoles Hs π.path.mverts).length) (a72 : c₃.nreg 6572 = Z)
    (hmcl : mcl ≤ m) (h97l : c₃.nreg 6597 = h + 5 + 4 + 7 * mcl)
    (hRO : RecsOut M ds gid ν S T l r π Hs σ lo hi (c₃.nreg 6501) c₃.nmem)
    (hlo : h + 18 + 14 * m + 21 * m + 4 * Hs.length + 2 ≤ lo)
    (hw : h + 18 + 14 * m + 21 * m + 4 * Hs.length + 2 ≤ W) (hdh : d + 4 + 7 * m ≤ h) :
    ∃ c₄ c₅ t₄ t₅, Exec I W spGlR c₃ c₄ t₄ ∧ Exec I W sfChild c₄ c₅ t₅ ∧
      t₄ + t₅ ≤ 203 * m + 230 ∧ ∃ mcr : ℕ, ∃ ixr : ℕ → ℕ, mcr ≤ m ∧
      c₅.nreg 6553 = h + 5 + 4 + 7 * mcl ∧
      Lay M gid u S T Z (chR M l r π Hs σ) mcr (fun k => en (ixr k)) (h + 5 + 4 + 7 * mcl + 5)
        c₅.nmem ∧
      (∀ a, a < h + 5 + 4 + 7 * mcl + 5 → c₅.nmem a = c₃.nmem a) ∧
      RecsOut M ds gid ν S T l r π Hs σ lo hi (c₅.nreg 6501) c₅.nmem ∧
      DRegKeep c₃ c₅ ∧ c₅.rmem = c₃.rmem ∧ c₅.output = c₃.output := by
  have hX1 := hRO.1
  obtain ⟨-, ⟨-, gr, -⟩, -⟩ := id hok
  obtain ⟨c₄, s₄, e₄, hs₄, b53, b65, b69, b71, n4, m4, rr4, rm4, o4⟩ := spGlR_exec (I := I) c₃
    hc h97l hF3.regs.r32 hF3.regs.r54 (by omega) (by omega)
  have hF4 : SpFront M gid u S T Z c₄ l r π Hs σ m en d h (h + 18 + 14 * m)
      (h + 18 + 14 * m + 3 * m + Hs.length + 2) :=
    hF3.congr (fun x hx => n4 x (by rcases hx with hx | hx | hx | hx <;>
      (try unfold spReg at hx) <;> omega)) (fun a _ => by rw [m4])
  rw [hF3.tr] at b71
  have R4 : ∀ x, (x = 6560 ∨ x = 6561 ∨ x = 6563 ∨ x = 6567 ∨ x = 6568 ∨ x = 6570 ∨
      x = 6572) → c₄.nreg x = c₃.nreg x := fun x hx => n4 x (by omega)
  obtain ⟨c₅, t₅, e₅, ht₅, mcr, ixr, hmcr, h97r, hLr, mmr, nnr, rrr, rmr, oor⟩ :=
    spChild_core (I := I) c₄ e₄.wb_right hF4 hok r subset_union_right gr.revClosed
    hF4.fr (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [R4 _ (by omega)]; exact a60) (by rw [R4 _ (by omega)]; exact a61)
    (by rw [R4 _ (by omega)]; exact a63) b65 (by rw [R4 _ (by omega)]; exact a67)
    (by rw [R4 _ (by omega)]; exact a68) b69 (by rw [R4 _ (by omega)]; exact a70) b71
    (by rw [R4 _ (by omega)]; exact a72)
  have el_def : c₅.nreg 6553 = h + 5 + 4 + 7 * mcl := by rw [nnr _ (by omega), b53]
  have x01 : c₅.nreg 6501 = c₃.nreg 6501 := by rw [nnr _ (by omega), n4 _ (by omega)]
  refine ⟨c₄, c₅, s₄, t₅, e₄, e₅, by omega, mcr, ixr, hmcr, el_def, hLr,
    fun a ha => by rw [mmr a (by omega), m4], ?_, fun x h1 h2 => ?_, by rw [rmr, rm4],
    by rw [oor, o4]⟩
  · rw [x01]
    exact hRO.congr fun a h1 h2 => by rw [mmr a (by omega), m4]
  · rw [nnr x (by omega), n4 x (by omega)]

/-- **The front and the two child frames of the extended split**: `spFront sepP`, `spChL`,
`spGlR`, `sfChild`; at the end the left child's frame at `h + 5` (ending at `el = r6553`), the right
child's at `el + 5`, and the children's records from `Xb = r6501`. -/
theorem spKids_execX {Reach : MCall M → Prop} {sepP : Stmt} {sT : ℕ → ℕ → ℕ}
    {sR : ℕ → ℕ → ℕ → ℕ}
    (hsep : SepPSpecX M ds Reach gid ν u S T Z I W sepP sT sR)
    {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D} {d e h m : ℕ} {en : ℕ → D}
    (c : Config) (hc : WordsBounded W c) (r4 : c.nreg 3004 = d) (r5 : c.nreg 3005 = e)
    (r3 : c.nreg 3003 = h) (heh : e ≤ h)
    (hin : FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c)
    (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem) (hfs : d + fsz m ≤ e)
    (hroom : h + 18 + 14 * m + sR (l.piece ∪ r.piece).card m Hs.length + 21 * m +
      4 * Hs.length + 2 ≤ W) :
    ∃ c₁ c₃ c₄ c₅ t₁ t₃ t₄ t₅, Exec I W (spFront sepP) c c₁ t₁ ∧ Exec I W spChL c₁ c₃ t₃ ∧
      Exec I W spGlR c₃ c₄ t₄ ∧ Exec I W sfChild c₄ c₅ t₅ ∧
      t₁ + t₃ + t₄ + t₅ ≤ sT (l.piece ∪ r.piece).card Hs.length + 497 * m + 21 * Hs.length + 540 ∧
      ∃ mcl mcr : ℕ, ∃ ixl ixr : ℕ → ℕ, mcl ≤ m ∧ mcr ≤ m ∧
      c₅.nreg 6553 = h + 5 + 4 + 7 * mcl ∧
      Lay M gid u S T Z (chL M l r π Hs σ) mcl (fun k => en (ixl k)) (h + 5) c₅.nmem ∧
      Lay M gid u S T Z (chR M l r π Hs σ) mcr (fun k => en (ixr k)) (h + 5 + 4 + 7 * mcl + 5)
        c₅.nmem ∧
      RecsOut M ds gid ν S T l r π Hs σ (h + 18 + 14 * m + 21 * m + 4 * Hs.length + 2)
        (h + 18 + 14 * m + sR (l.piece ∪ r.piece).card m Hs.length) (c₅.nreg 6501) c₅.nmem ∧
      DRegKeep c c₅ ∧ (∀ a < h, c₅.nmem a = c.nmem a ∧ c₅.rmem a = c.rmem a) ∧
      c₅.output = c.output := by
  obtain ⟨c₁, c₃, t₁, t₃, e₁, e₃, ht, hF3, a60, a61, a63, a67, a68, a70, a72, mcl, ixl, hmcl,
    h97l, hLl, hRO, dk3, mk3, o3⟩ := spKidL_execX hsep c hc r4 r5 r3 heh hin hL hfs hroom
  obtain ⟨c₄, c₅, t₄, t₅, e₄, e₅, ht', mcr, ixr, hmcr, el_def, hLr, mm5, hRO5, dk5, rm5, o5⟩ :=
    spKidR_execX (I := I) c₃ e₃.wb_right hF3 hin.2.1 a60 a61 a63 a67 a68 a70 a72 hmcl h97l hRO
      le_rfl (by omega) (by unfold fsz at hfs; omega)
  refine ⟨c₁, c₃, c₄, c₅, t₁, t₃, t₄, t₅, e₁, e₃, e₄, e₅, by omega, mcl, mcr, ixl, ixr, hmcl,
    hmcr, el_def, hLl.congr fun a h1 h2 => mm5 a (by omega), hLr, hRO5,
    fun x h1 h2 => by rw [dk5 x h1 h2]; exact dk3 x h1 h2, fun a ha => ?_, by rw [o5, o3]⟩
  rw [mm5 a (by omega), rm5]; exact mk3 a ha

end Exec

end MfDrv

end BKMNW

end PlanarFlow
