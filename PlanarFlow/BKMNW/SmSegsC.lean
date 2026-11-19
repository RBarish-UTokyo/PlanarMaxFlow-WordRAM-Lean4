module

public import PlanarFlow.BKMNW.SmSegsB
public import PlanarFlow.BKMNW.SmXF

/-!
# The small separator with its parts: `sepSmS_exec`

**`sepSmS_exec`**: `sepSmS = (3120 := r6500) ; sepSm ; smSegs` at a node of `smD` meets the
conclusion of `sepSm_exec` (the outputs of `SepPSpecX`, the children's records, with the room
`smRS n m k = smR n m k + 2 m + 2 k + 16`) **and `SegsOut`** (the parts of the separator, from
`r6502`, after the records), within `560 n + 38 m + 61 k + 591` steps — the small-piece half of
`SepPSpecXS`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
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

set_option maxHeartbeats 1000000 in
/-- **The small separator with its parts** (see the module docstring). -/
theorem sepSmS_exec {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    {m n d R Sb : ℕ} {en g : ℕ → D} (c : Config) (hc : WordsBounded W c)
    (hok : CallOk M S T ((.node l r π, Hs, σ) : MCall M))
    (hL : Lay M gid u S T Z ((.node l r π, Hs, σ) : MCall M) m en d c.nmem)
    (hpR : c.nmem (d + fsz m) = R) (o2 : d + fsz m < R)
    (hA : RArr M gid ν S T ((.node l r π, Hs, σ) : MCall M) m n R g c.nmem) (hn : c.nmem R = n)
    (hsm : smD M ds.pk S T (l.piece ∪ r.piece) Hs = .node l r π)
    (hpk : PkMin gid ds.pk) (hν : Injective ν) (hloop : ∀ y, M.head y ≠ M.tail y)
    (r4 : c.nreg 3004 = d) (r50 : c.nreg 6500 = Sb) (o1 : R + 3 + 6 * n + m ≤ Sb)
    (w : Sb + smRS n m Hs.length ≤ W) (hW : 21 ≤ W) :
    ∃ c' t, Exec I W sepSmS c c' t ∧ t ≤ 560 * n + 38 * m + 61 * Hs.length + 591 ∧
      DRegKeep c c' ∧ (∀ a < Sb, c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      c'.output = c.output ∧
      (∀ i < m, c'.nmem (Sb + i) = bf (en i ∈ l.piece)) ∧
      (∀ i < m, c'.nmem (Sb + m + i) = bf (en i ∈ π.path.darts.toFinset)) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = bf (M.tail (en i) ∈ π.path.mverts)) ∧
      (∀ j < Hs.length, c'.nmem (Sb + 3 * m + j) =
        bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
      c'.nmem (Sb + 3 * m + Hs.length) = ntag l ∧ c'.nmem (Sb + 3 * m + Hs.length + 1) = ntag r ∧
      RecsOut M ds gid ν S T l r π Hs σ (Sb + 21 * m + 4 * Hs.length + 2)
        (Sb + smRS n m Hs.length) (c'.nreg 6501) c'.nmem ∧
      SegsOut M en m π (c'.nreg 6501 + 2 + c'.nmem (c'.nreg 6501) +
        c'.nmem (c'.nreg 6501 + 1)) (Sb + smRS n m Hs.length) (c'.nreg 6502) c'.nmem := by
  have hR : smRS n m Hs.length = smR n m Hs.length + 2 * m + 2 * Hs.length + 16 := rfl
  have hR' : smR n m Hs.length = 22 * m + 24 * n + 8 * Hs.length + 30 := rfl
  -- the save of `Sb`
  obtain ⟨c₀, t₀, e₀, ht₀, s0, f₀, m₀, rr₀, rm₀, o₀⟩ : ∃ c₀ t₀,
      Exec I W (block [.copyN 3120 6500]) c c₀ t₀ ∧ t₀ = 1 ∧ c₀.nreg 3120 = Sb ∧
      (∀ x, x ≠ 3120 → c₀.nreg x = c.nreg x) ∧ c₀.nmem = c.nmem ∧ c₀.rreg = c.rreg ∧
      c₀.rmem = c.rmem ∧ c₀.output = c.output := by
    exec_block
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same, r50])
  rw [← m₀] at hL hpR hA hn
  -- `sepSm`
  obtain ⟨c₁, t₁, e₁, ht₁, dk1, low1, out1, o1a, o1b, o1c, o1d, o1e, o1f, hRec⟩ :=
    sepSm_exec (I := I) (ds := ds) c₀ e₀.wb_right hok hL hpR o2 hA hn hsm hpk hν hloop
      ((f₀ 3004 (by decide)).trans r4) ((f₀ 6500 (by decide)).trans r50) o1
      (by clear * - w hR; omega) hW
  obtain ⟨hlo, hhi, hrl, hrr⟩ := hRec
  have q1 := (Exec.wr_frame e₁ wrOK_sepSm).1
  have s1 : c₁.nreg 3120 = Sb := by rw [q1 3120 (by decide)]; exact s0
  have hdS : d + 1 ≤ Sb := by unfold fsz at o2; clear * - o2 o1; omega
  have hm1 : c₁.nmem d = m := by rw [(low1 d (by omega)).1]; exact hL.hm
  have hk1 : c₁.nmem (d + 1) = Hs.length := by rw [(low1 (d + 1) (by omega)).1]; exact hL.hk
  -- `smSegs`
  have d1 : c₁.nreg 3004 = d := by
    rw [dk1 3004 (by omega) (by omega), f₀ 3004 (by decide)]; exact r4
  obtain ⟨c₂, t₂, e₂, ht₂, g502, w0, w1, w2, w3, mfr, rfr, rr₂, rm₂, o₂⟩ :=
    smSegs_exec (I := I) c₁ e₁.wb_right rfl d1 s1 rfl rfl hm1 hk1 (by clear * - hlo; omega) hdS
      (by clear * - hhi w hR; omega)
  set Xb := c₁.nreg 6501 with hXb
  set Gb := Xb + 2 + c₁.nmem Xb + c₁.nmem (Xb + 1) with hGb
  have k6501 : c₂.nreg 6501 = Xb := rfr 6501 (by decide) (by decide) (by decide)
  have keep : ∀ a, a < Gb → c₂.nmem a = c₁.nmem a := fun a ha =>
    mfr a (by clear * - ha; omega)
  have kX0 : c₂.nmem Xb = c₁.nmem Xb := keep _ (by clear * - hGb; omega)
  have kX1 : c₂.nmem (Xb + 1) = c₁.nmem (Xb + 1) := keep _ (by clear * - hGb; omega)
  have hSeg : Sb + 3 * m + Hs.length + 2 ≤ Xb := by clear * - hlo; omega
  refine ⟨c₂, _, .seq e₀ (.seq e₁ e₂), ?_, fun x a1 a2 => ?_, fun a ha => ?_, ?_,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · clear * - ht₀ ht₁ ht₂
    omega
  · rw [rfr x (by omega) (by omega) (by omega), dk1 x a1 a2, f₀ x (by omega)]
  · refine ⟨?_, ?_⟩
    · rw [keep a (by clear * - ha hSeg; omega), (low1 a ha).1, m₀]
    · rw [rm₂, (low1 a ha).2, rm₀]
  · rw [o₂, out1, o₀]
  · rw [keep _ (by clear * - hi hSeg; omega)]; exact o1a i hi
  · rw [keep _ (by clear * - hi hSeg; omega)]; exact o1b i hi
  · rw [keep _ (by clear * - hi hSeg; omega)]; exact o1c i hi
  · rw [keep _ (by clear * - hj hSeg; omega)]; exact o1d j hj
  · rw [keep _ (by clear * - hSeg; omega)]; exact o1e
  · rw [keep _ (by clear * - hSeg; omega)]; exact o1f
  · rw [k6501]
    have h0 : RecsOut M ds gid ν S T l r π Hs σ (Sb + 21 * m + 4 * Hs.length + 2) Gb Xb
        c₁.nmem := ⟨hlo, le_refl _, hrl, hrr⟩
    exact (h0.congr fun a a1 a2 => keep a a2).mono (by clear * - hhi w hR; omega)
  · rw [k6501, kX0, kX1, g502]
    refine segsOut_sm hpk (hok.pieceInv.rev) hsm hL.en_mem hL.en_surj hL.en_mono
      (PF := fun i => c₁.nmem (Sb + m + i)) (HF := fun j => c₁.nmem (Sb + 3 * m + j))
      (fun i hi => o1b i hi) (fun j hj => o1d j hj) (le_refl _)
      (by clear * - hhi w hR; omega) w0 w1 w2 w3

end Exec

end MfDrv

end BKMNW

end PlanarFlow
