module

public import PlanarFlow.BKMNW.SmXA2

/-!
# The small separator program, stage A: the meaning

**`smXA_exec`**: at a node `smD pk S T P Hs = .node l r π` of the small decomposition (`pk` the
dart of least `gid`, `PkMin`), from the frame (`Lay`, `m` darts) and the record (`RArr`, `n` darts
of the piece), `smXA` runs within `300 n + 27 m + 26 k + 300` steps and ends with `SmRegs`, the six
outputs of `SepPSpec` at `Sb`, and — over **all** the record's darts — the flags of `l.piece` at
`Ob = A + n` and of the path's vertices at `A + 3 n`, the flags of the holes meeting the path at
`A + 4 n` (`A = Sb + 21 m + 4 k + 2`); the memory below `Sb` and from `A + 4 n + k + 2` on kept.
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

variable {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

lemma smReg_st {x : ℕ} (h : smReg x) : x < 5308 ∨ 5440 < x := by unfold smReg at h; omega

lemma smReg_gg {x : ℕ} (h : smReg x) : (x < 4910 ∨ (4916 < x ∧ x < 6210) ∨ 6217 < x) := by
  unfold smReg at h; omega

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **Stage A of the small separator program** (see the module docstring). -/
theorem smXA_exec {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    {m n d R Sb : ℕ} {en g : ℕ → D} {pk : Finset D → D} (c : Config) (hc : WordsBounded W c)
    (hpw : Hs.Pairwise Disjoint) (hrc : RevClosed M (l.piece ∪ r.piece))
    (hL : Lay M gid u S T Z ((.node l r π, Hs, σ) : MCall M) m en d c.nmem)
    (hpR : c.nmem (d + fsz m) = R)
    (hA : RArr M gid ν S T ((.node l r π, Hs, σ) : MCall M) m n R g c.nmem) (hn : c.nmem R = n)
    (hsm : smD M pk S T (l.piece ∪ r.piece) Hs = .node l r π)
    (hpk : PkMin gid pk) (hν : Injective ν) (hloop : ∀ y, M.head y ≠ M.tail y)
    (r4 : c.nreg 3004 = d) (r50 : c.nreg 6500 = Sb)
    (o1 : R + 3 + 6 * n + m ≤ Sb) (o2 : d + fsz m < R)
    (w : Sb + 22 * m + 22 * n + 8 * Hs.length + 20 ≤ W) (hW : 21 ≤ W) :
    ∃ c' t, Exec I W smXA c c' t ∧ t ≤ 300 * n + 27 * m + 26 * Hs.length + 300 ∧
      SmRegs c' d m Hs.length R n Sb (Sb + 21 * m + 4 * Hs.length + 2) ∧ c'.nreg 6521 = 1 ∧
      (∀ i < m, c'.nmem (Sb + i) = bf (en i ∈ l.piece)) ∧
      (∀ i < m, c'.nmem (Sb + m + i) = bf (en i ∈ π.path.darts.toFinset)) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = bf (M.tail (en i) ∈ π.path.mverts)) ∧
      (∀ j < Hs.length, c'.nmem (Sb + 3 * m + j) =
        bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
      c'.nmem (Sb + 3 * m + Hs.length) = ntag l ∧
      c'.nmem (Sb + 3 * m + Hs.length + 1) = ntag r ∧
      (∀ i < n, c'.nmem (Sb + 21 * m + 4 * Hs.length + 2 + n + i) = bf (g i ∈ l.piece)) ∧
      (∀ i < n, c'.nmem (Sb + 21 * m + 4 * Hs.length + 2 + 3 * n + i) =
        bf (M.tail (g i) ∈ π.path.mverts)) ∧
      (∀ j < Hs.length, c'.nmem (Sb + 21 * m + 4 * Hs.length + 2 + 4 * n + j) =
        bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
      (∀ a < Sb, c'.nmem a = c.nmem a) ∧
      (∀ a, Sb + 21 * m + 4 * Hs.length + 2 + 4 * n + Hs.length + 2 ≤ a →
        c'.nmem a = c.nmem a) ∧
      DRegKeep c c' ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hm : c.nmem d = m := hL.hm
  have hk : c.nmem (d + 1) = Hs.length := hL.hk
  have hf : fsz m = 4 + 7 * m := rfl
  have hR' : c.nmem (d + 7 * m + 4) = R := by
    rw [show d + 7 * m + 4 = d + fsz m by omega]; exact hpR
  have o2' : d + 7 * m + 4 < R := by omega
  -- the set-up and the ones
  obtain ⟨c₄, t₄, e₄, ht₄, hR4, o21, s0, s1, s2, s3, s4, s5, s6, s7, f4, mm4, dk4, rr4, rm4,
    o4⟩ := smXA0_exec (I := I) c hc r4 r50 hm hk hR' hn o1 o2' w hW
  have M4 : ∀ a, a < Sb + 21 * m + 4 * Hs.length + 2 → c₄.nmem a = c.nmem a := fun a ha =>
    mm4 a (Or.inl ha)
  have hA4 : RArr M gid ν S T ((.node l r π, Hs, σ) : MCall M) m n R g c₄.nmem :=
    hA.congr fun a h1 h2 => M4 a (by clear * - h2 o1; omega)
  have hSA : SmArr M c₄.nmem n (Sb + 21 * m + 4 * Hs.length + 2) (R + 3 + n) (R + 3 + 2 * n)
      (R + 3 + 3 * n) (R + 3 + 4 * n) g (l.piece ∪ r.piece) Hs S T ν :=
    smArr_of_rArr (x := ((.node l r π, Hs, σ) : MCall M)) hA4 f4 hν hpw
  -- bounds for `smStep`
  have b1 : R + 3 + n + n ≤ Sb + 21 * m + 4 * Hs.length + 2 + n := by clear * - o1; omega
  have b2 : R + 3 + 2 * n + n ≤ Sb + 21 * m + 4 * Hs.length + 2 + n := by clear * - o1; omega
  have b3 : R + 3 + 3 * n + n ≤ Sb + 21 * m + 4 * Hs.length + 2 + n := by clear * - o1; omega
  have b4 : R + 3 + 4 * n + n ≤ Sb + 21 * m + 4 * Hs.length + 2 + n := by clear * - o1; omega
  have b6 : Sb + 21 * m + 4 * Hs.length + 2 + n + 3 * n + Hs.length + 2 ≤ W := by
    clear * - w; omega
  have b7 : n + 1 ≤ W := by clear * - w; omega
  -- one step of `smD`
  obtain ⟨c₅, t₅, e₅, ht₅, hnd, hout, mm5, nn5, rr5, rm5, o5⟩ := smStep_smD (I := I) c₄
    e₄.wb_right hSA hrc (pk_first (x := ((.node l r π, Hs, σ) : MCall M)) hA4 hpk)
    (fun X hX => (hpk X hX).1) hloop s0 s1 s2 s3 s4 s5 s6 s7 (by clear * - hW; omega) le_rfl
    b1 b2 b3 b4 b6 b7
  obtain ⟨oLP, oPD, oCV, oHM, oTl, oTr⟩ := hout l r π hsm
  have hR5 : SmRegs c₅ d m Hs.length R n Sb (Sb + 21 * m + 4 * Hs.length + 2) :=
    hR4.congr fun x hx => nn5 x (smReg_st hx)
  have M5 : ∀ a, (a < Sb + 21 * m + 4 * Hs.length + 2 + n ∨
      Sb + 21 * m + 4 * Hs.length + 2 + n + 3 * n + Hs.length + 2 ≤ a) →
      c₅.nmem a = c₄.nmem a := mm5
  have K54 : ∀ a < Sb, c₅.nmem a = c.nmem a := fun a ha => by
    rw [M5 a (Or.inl (by clear * - ha; omega)), M4 a (by clear * - ha; omega)]
  have hfx5 : ∀ i < m, c₅.nmem (R + 3 + 6 * n + i) < n := fun i hi => by
    rw [K54 _ (by clear * - hi o1; omega)]; exact hA.fx i hi
  have FXe : ∀ i < m, g (c₅.nmem (R + 3 + 6 * n + i)) = en i := fun i hi => by
    rw [K54 _ (by clear * - hi o1; omega)]; exact hA.fx_en hL i hi
  -- the outputs of `SepPSpec`
  obtain ⟨c₆, t₆, e₆, ht₆, g1, g2, g3, g4, mm6, nn6, rr6, rm6, o6⟩ := smAG_exec (I := I) c₅
    e₅.wb_right hR5 hfx5 o1 (by clear * - w; omega)
  have M6 : ∀ a, (a < Sb ∨ Sb + 3 * m + Hs.length + 2 ≤ a) → c₆.nmem a = c₅.nmem a := mm6
  have ht : t₄ + (t₅ + t₆) ≤ 300 * n + 27 * m + 26 * Hs.length + 300 := by
    clear * - ht₄ ht₅ ht₆; omega
  refine ⟨c₆, _, by unfold smXA; exact .seq e₄ (.seq e₅ e₆), ht,
    hR5.congr fun x hx => nn6 x (smReg_gg hx),
    by rw [nn6 6521 (by decide), nn5 6521 (by decide)]; exact o21,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, ?_, ?_, fun i hi => ?_,
    fun i hi => ?_, fun j hj => ?_, fun a ha => ?_, fun a ha => ?_, fun x h1 h2 => ?_,
    by rw [rr6, rr5, rr4], by rw [rm6, rm5, rm4], by rw [o6, o5, o4]⟩
  · rw [g1 i hi, oLP _ (hfx5 i hi), FXe i hi]
  · rw [g2 i hi, show Sb + 21 * m + 4 * Hs.length + 2 + 2 * n + c₅.nmem (R + 3 + 6 * n + i) =
      Sb + 21 * m + 4 * Hs.length + 2 + n + n + c₅.nmem (R + 3 + 6 * n + i) by
        clear * -; omega, oPD _ (hfx5 i hi), FXe i hi]
  · rw [g3 i hi, show Sb + 21 * m + 4 * Hs.length + 2 + 3 * n + c₅.nmem (R + 3 + 6 * n + i) =
      Sb + 21 * m + 4 * Hs.length + 2 + n + 2 * n + c₅.nmem (R + 3 + 6 * n + i) by
        clear * -; omega, oCV _ (hfx5 i hi), FXe i hi]
  · rw [g4 j (by clear * - hj; omega), show Sb + 21 * m + 4 * Hs.length + 2 + 4 * n + j =
      Sb + 21 * m + 4 * Hs.length + 2 + n + 3 * n + j by clear * -; omega, oHM j hj]
  · rw [g4 Hs.length (by clear * -; omega), show Sb + 21 * m + 4 * Hs.length + 2 + 4 * n +
      Hs.length = Sb + 21 * m + 4 * Hs.length + 2 + n + 3 * n + Hs.length by clear * -; omega, oTl]
  · rw [show Sb + 3 * m + Hs.length + 1 = Sb + 3 * m + (Hs.length + 1) by clear * -; omega,
      g4 (Hs.length + 1) (by clear * -; omega), show Sb + 21 * m + 4 * Hs.length + 2 + 4 * n +
      (Hs.length + 1) = Sb + 21 * m + 4 * Hs.length + 2 + n + 3 * n + Hs.length + 1 by
        clear * -; omega, oTr]
  · rw [M6 _ (Or.inr (by clear * - hi; omega)), oLP i hi]
  · rw [M6 _ (Or.inr (by clear * - hi; omega)), show Sb + 21 * m + 4 * Hs.length + 2 + 3 * n + i =
      Sb + 21 * m + 4 * Hs.length + 2 + n + 2 * n + i by clear * -; omega, oCV i hi]
  · rw [M6 _ (Or.inr (by clear * - hj; omega)), show Sb + 21 * m + 4 * Hs.length + 2 + 4 * n + j =
      Sb + 21 * m + 4 * Hs.length + 2 + n + 3 * n + j by clear * -; omega, oHM j hj]
  · rw [M6 _ (Or.inl ha), K54 a ha]
  · rw [M6 _ (Or.inr (by clear * - ha; omega)), M5 _ (Or.inr (by clear * - ha; omega)),
      mm4 a (Or.inr (by clear * - ha; omega))]
  · rw [nn6 x (by clear * - h1 h2; omega), nn5 x (by clear * - h1 h2; omega)]
    exact dk4 x (by clear * - h2; omega)

end Exec

end MfDrv

end BKMNW

end PlanarFlow
