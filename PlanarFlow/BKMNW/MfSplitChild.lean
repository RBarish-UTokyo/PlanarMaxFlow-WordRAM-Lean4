module

public import PlanarFlow.BKMNW.MfSplit

/-!
# The two child frames of the split

From the state `SpFront` after the front of the split:

* **`spChild_core`**: `sfChild` (with its registers set) writes at `dc` the frame of the child
  call `(τc, childHoles Hs C, childRot M σ B π.path.darts Bc)`, `Bc = pdarts M τc.piece
  (childHoles Hs C)`, as `Lay` with the numbering `en ∘ ix` (`203 m + 223` steps).
* `spGlL_exec`, `spGlR_exec` (the registers of `sfChild` for the left and the right child).
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

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The frame of one child call** (see the module docstring). -/
theorem spChild_core {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    {m : ℕ} {en : ℕ → D} {d h Sb Wb : ℕ} (c : Config) (hc : WordsBounded W c)
    (hF : SpFront M gid u S T Z c l r π Hs σ m en d h Sb Wb)
    (hok : CallOk M S T (.node l r π, Hs, σ)) (τc : ADec M) (hτc : τc.piece ⊆ l.piece ∪ r.piece)
    (hτr : RevClosed M τc.piece) {Fxb dc : ℕ}
    (hFx : ∀ i < m, c.nmem (Fxb + i) = bf (en i ∈ pdarts M τc.piece (childHoles Hs π.path.mverts)))
    (oF1 : Wb ≤ Fxb) (oF2 : Fxb + m ≤ Wb + 6 * m) (od1 : d + 4 + 6 * m ≤ dc)
    (od2 : dc + 4 + 7 * m ≤ Sb) (w : Wb + 18 * m + 3 * Hs.length ≤ W) (w' : m + 2 ≤ W)
    (r60 : c.nreg 6560 = m) (r61 : c.nreg 6561 = d) (r63 : c.nreg 6563 = Wb + 5 * m)
    (r65 : c.nreg 6565 = Fxb) (r67 : c.nreg 6567 = Wb + 3 * m) (r68 : c.nreg 6568 = Wb + 4 * m)
    (r69 : c.nreg 6569 = dc) (r70 : c.nreg 6570 = (childHoles Hs π.path.mverts).length)
    (r71 : c.nreg 6571 = ntag τc) (r72 : c.nreg 6572 = Z) :
    ∃ c' t, Exec I W sfChild c c' t ∧ t ≤ 203 * m + 223 ∧ ∃ mc : ℕ, ∃ ix : ℕ → ℕ, mc ≤ m ∧
      c'.nreg 6597 = dc + 4 + 7 * mc ∧
      Lay M gid u S T Z (τc, childHoles Hs π.path.mverts,
        childRot M σ (pdarts M (l.piece ∪ r.piece) Hs) π.path.darts
          (pdarts M τc.piece (childHoles Hs π.path.mverts))) mc (fun k => en (ix k)) dc c'.nmem ∧
      (∀ a, (a < dc ∨ (dc + 4 + 7 * m ≤ a ∧ a < Wb + 6 * m) ∨ Wb + 18 * m + 3 * Hs.length ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6200 ∨ (6328 < x ∧ x < 6580) ∨ 6599 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hL := hF.lay
  have hSb := hF.hSb
  have hWb := hF.hWb
  obtain ⟨hPI, -, -⟩ := hok.1
  have emL : ∀ i < m, en i ∈ pdarts M (l.piece ∪ r.piece) Hs := hL.en_mem
  have esL : ∀ y ∈ pdarts M (l.piece ∪ r.piece) Hs, ∃ i < m, en i = y := hL.en_surj
  have sgL : ∀ i < m, c.nmem (d + 4 + 2 * m + i) < m ∧
      en (c.nmem (d + 4 + 2 * m + i)) = σ (en i) := hL.sg
  have rvL : ∀ i < m, c.nmem (d + 4 + m + i) < m ∧
      en (c.nmem (d + 4 + m + i)) = M.rev (en i) := hL.rv
  have cpL : ∀ i < m, (c.nmem (d + 4 + 3 * m + i) : ℤ) = u (en i) ∧
      c.nmem (d + 4 + 3 * m + i) ≤ Z := hL.cp
  have gdL : ∀ i < m, c.nmem (d + 4 + i) = gid (en i) := hL.gd
  obtain ⟨c', t, ex, ht, mc, ix, hmc, h97, hix, hsurj, hmono, h0, h1, h2, h3, hg, hr, hs, hcp,
    hkr, hhl, mm, nn, rr, rm, oo⟩ := sfChild_exec (P := I) M σ (pdarts M (l.piece ∪ r.piece) Hs)
    π.path.darts (pdarts M τc.piece (childHoles Hs π.path.mverts)) c hc
    (m := m) (d := d) (A := Wb + 7 * m + 3 * Hs.length) (IDb := Wb + 5 * m) (PFb := Sb + m)
    (Fxb := Fxb) (Tb := Wb + 6 * m) (KCb := Wb + 3 * m) (HCb := Wb + 4 * m) (dc := dc)
    (kc := (childHoles Hs π.path.mverts).length) (tg := ntag τc) (Z := Z)
    r60 r61 hF.regs.r62 r63 hF.regs.r64 r65 hF.regs.r66 r67 r68 r69 r70 r71 r72
    (fun i hi j hj e => hL.en_inj hi hj e) emL esL hPI.stable
    (fun y hy => stable_pdarts hPI.rev Hs y hy) (hpath_rev π.path)
    (pdarts_child_sub π.path hτc) (pdarts_child_rev hτr _) sgL rvL hF.pf hFx hF.id
    od1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) oF2
    (by omega) (by omega) (by omega) (by omega) w'
  refine ⟨c', t, ex, ht, mc, ix, hmc, h97, ?_, fun a ha => mm a (by omega), nn, rr, rm, oo⟩
  exact lay_child hL τc _ _ hix hsurj hmono h0 h1 h2 h3 hg hr hs hcp
    (fun k hk => by rw [hkr k hk]; exact hF.kc _ (hix k hk).1)
    (fun k hk => by rw [hhl k hk]; exact hF.hc _ (hix k hk).1)

theorem spGlL_exec (c : Config) (hc : WordsBounded W c) {d h m k Wb t Z : ℕ}
    (r4 : c.nreg 3004 = d) (r3 : c.nreg 3003 = h) (r10 : c.nreg 6510 = m)
    (r35 : c.nreg 6535 = Wb + 5 * m) (r31 : c.nreg 6531 = Wb + m) (r33 : c.nreg 6533 = Wb + 3 * m)
    (r34 : c.nreg 6534 = Wb + 4 * m) (r48 : c.nreg 6548 = k) (r54 : c.nreg 6554 = t)
    (hz : c.nmem (d + 3) = Z) (w : h + 5 ≤ W) (wd : d + 3 ≤ W) :
    ∃ c' s, Exec I W spGlL c c' s ∧ s = 13 ∧ c'.nreg 6560 = m ∧ c'.nreg 6561 = d ∧
      c'.nreg 6563 = Wb + 5 * m ∧ c'.nreg 6565 = Wb + m ∧ c'.nreg 6567 = Wb + 3 * m ∧
      c'.nreg 6568 = Wb + 4 * m ∧ c'.nreg 6569 = h + 5 ∧ c'.nreg 6570 = k ∧
      c'.nreg 6571 = c.nmem t ∧ c'.nreg 6572 = Z ∧
      (∀ x, (x < 6550 ∨ x = 6551 ∨ (6552 < x ∧ x < 6560) ∨ x = 6562 ∨ x = 6564 ∨ x = 6566 ∨
        6572 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold spGlL
  exec_block
  all_goals try omega
  all_goals try (have := hc.2 t; omega)
  all_goals try (have := hc.1 6510; have := hc.1 6548; omega)
  all_goals
    try (config_simp; simp (disch := omega) only [upd_other, upd_same, r4, r3, r10, r54]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r4, r3, r10, r35, r31, r33, r34, r48,
      r54, hz])
    try omega

theorem spGlR_exec (c : Config) (hc : WordsBounded W c) {el t : ℕ} {Fr : ℕ}
    (r97 : c.nreg 6597 = el) (r32 : c.nreg 6532 = Fr) (r54 : c.nreg 6554 = t) (w : el + 5 ≤ W)
    (wt : t + 1 ≤ W) :
    ∃ c' s, Exec I W spGlR c c' s ∧ s = 7 ∧ c'.nreg 6553 = el ∧ c'.nreg 6565 = Fr ∧
      c'.nreg 6569 = el + 5 ∧ c'.nreg 6571 = c.nmem (t + 1) ∧
      (∀ x, (x < 6550 ∨ x = 6551 ∨ (6553 < x ∧ x < 6565) ∨ (6565 < x ∧ x < 6569) ∨ x = 6570 ∨
        6571 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold spGlR
  exec_block
  all_goals try omega
  all_goals try (have := hc.1 6532; have := hc.2 (t + 1); omega)
  all_goals
    try (config_simp; simp (disch := omega) only [upd_other, upd_same, r97, r32, r54]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r97, r32, r54])
    try omega

end Exec

end MfDrv

end BKMNW

end PlanarFlow
