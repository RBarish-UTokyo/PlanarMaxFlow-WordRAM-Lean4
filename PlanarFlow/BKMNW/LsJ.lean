module

public import PlanarFlow.BKMNW.LsI

/-!
# `sepL`: the parts of the separator (`lsG ; lsSg`)

**`ls10_exec`** (`110 n + 7 m + 140` steps): from the path written by `lsB` (`PathPD` of `g ∘ IX'`
at `E + n`), `SegsOut' M en m π lo hi Gb` at `Gb = E + 2 n` and `r6502 = Gb`: by `sgProg_segsOut`
when `0 < m`; when `m = 0` (no piece-map dart) the parts are empty and `lsS0` writes `0`.
Memory outside `[Gb, Gb + 2 n + 3)` and `sgProg`'s scratch `[Z', Z' + 9 n + 2)` kept.
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

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The parts of `sepL`. -/
def ls10 : Stmt := .seq lsG lsSg

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **The parts of the separator** (see the module docstring). -/
theorem ls10_exec (c : Config) (hc : WordsBounded W c) {g en : ℕ → D} {m k R n Sb U n' : ℕ}
    (hR : LsR c m k R n Sb) (hL : LsL c n k U)
    (hU : U = Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3)
    (r57 : c.nreg 8557 = n') (r71 : c.nreg 8571 = Sb + 21 * m + 38 * n + 8 * k + 24 + n)
    (hn' : n' ≤ n) (hn'1 : 1 ≤ n')
    (hIX : ∀ q < n', c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q) < n)
    (hcov : 0 < m → ∀ q < n', ∃ f < m, en f = g (c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q)))
    {ρ : HPath M} {Hs : List (Finset V)} {π : HSep M}
    (hPD : PathPD M (fun q => g (c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q))) n'
      (Sb + 21 * m + 38 * n + 8 * k + 24 + n) c ρ)
    (hρ : ρ.Simple Hs) (hπ : π.segs = segsF ρ Hs) (hm0 : m = 0 → π.segs = [])
    (hHP : ∀ i < n, c.nmem (R + 3 + 2 * n + i) = hlab Hs (M.tail (g i)))
    (hFX : ∀ f < m, c.nmem (R + 3 + 6 * n + f) < n ∧ g (c.nmem (R + 3 + 6 * n + f)) = en f)
    (hginj : ∀ i < n, ∀ j < n, g i = g j → i = j)
    (heninj : ∀ i < m, ∀ j < m, en i = en j → i = j)
    {lo hi : ℕ} (hlo : lo ≤ Sb + 21 * m + 38 * n + 8 * k + 24 + 2 * n)
    (hhi : Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 ≤ hi)
    (lR : R + 3 + 6 * n + m ≤ Sb) (w : U + 55 * n + 9 * k + 17 ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W ls10 c c' t ∧ t ≤ 110 * n + 7 * m + 140 ∧
      SegsOut' M en m π lo hi (Sb + 21 * m + 38 * n + 8 * k + 24 + 2 * n) c'.nmem ∧
      c'.nreg 6502 = Sb + 21 * m + 38 * n + 8 * k + 24 + 2 * n ∧
      (∀ a, ¬ (Sb + 21 * m + 38 * n + 8 * k + 24 + 2 * n ≤ a ∧
          a < Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3) →
        ¬ (U + 46 * n + 9 * k + 15 ≤ a ∧ a < U + 55 * n + 9 * k + 17) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4100 ∨ x = 6501) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ls10 lsSg
  obtain ⟨c₁, t₁, e₁, ht₁, g00, g01, g02, g03, g04, g05, g06, g07, g08, g21, n1, m1, rr1, rm1,
    o1⟩ := lsG_exec (I := I) c hc hR hL r71 (by omega) (by omega) w2
  rw [r57] at g00
  have hR1 : LsR c₁ m k R n Sb := hR.congr fun x hx => n1 x (by omega)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- no piece-map dart: no parts
    have hf : ¬ c₁.nreg 8568 < c₁.nreg 8550 := by rw [hR1.r68, hR1.r50, hm]; omega
    obtain ⟨c₂, t₂, e₂, ht₂, m2, v02, n2, rr2, rm2, o2⟩ := lsS0_exec (I := I) c₁ e₁.wb_right g07
      (by omega) w2
    have hs := hm0 hm
    refine ⟨c₂, t₁ + (t₂ + 2), .seq e₁ (.ifLtN_false hf e₂), by omega, ?_, v02,
      fun a h1 h2 => ?_, fun x hx => ?_, by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
    · refine ⟨⟨hlo, ?_, ?_, fun j hj => ?_⟩, ?_, fun j hj => ?_⟩
      · rw [m2, upd_same, hs]; rfl
      · rw [hs]; simp; omega
      · rw [hs] at hj; simp at hj
      · rw [hs]; simp; omega
      · rw [hs] at hj; simp at hj
    · rw [m2, upd_other _ _ _ (by omega), m1]
    · rw [n2 x (by omega) (by omega), n1 x (by omega)]
  · have ht : c₁.nreg 8568 < c₁.nreg 8550 := by rw [hR1.r68, hR1.r50]; exact hm
    have hPD1 : PathPD M (fun q => g (c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q))) n'
        (Sb + 21 * m + 38 * n + 8 * k + 24 + n) c₁ ρ :=
      pathPD_congr hPD (fun j hj => by rw [m1]) (fun i hi => rfl)
    obtain ⟨c₂, t₂, e₂, ht₂, hSO, v02, m2, n2, rr2, rm2, o2⟩ := sgProg_segsOut (P := I) c₁
      e₁.wb_right (n' := n') (PDb := Sb + 21 * m + 38 * n + 8 * k + 24 + n)
      (IXb := Sb + 21 * m + 38 * n + 8 * k + 24) (HPb := R + 3 + 2 * n) (m := m)
      (FXb := R + 3 + 6 * n) (Z := U + 46 * n + 9 * k + 15)
      (Gb := Sb + 21 * m + 38 * n + 8 * k + 24 + 2 * n) (n := n) (lo := lo) (hi := hi) g00 g01 g02 g03 g04 g05 g06 g07 g08 g21 hρ hπ (g := g) (en := en)
      hPD1
      (fun i hi => by rw [m1]; exact ⟨hIX i hi, rfl⟩) (fun i hi => by rw [m1]; exact hHP i hi)
      (fun f hf => by rw [m1]; exact hFX f hf) hginj heninj
      (fun i hi => hcov hm i hi)
      ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ (by omega) hlo
      (by clear * - hhi hn' g00 g07; omega)
    refine ⟨c₂, t₁ + (t₂ + 1), .seq e₁ (.ifLtN_true ht e₂), by omega, hSO, v02,
      fun a h1 h2 => ?_, fun x hx => ?_, by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
    · rw [m2 a (by omega) (by omega), m1]
    · rw [n2 x (by omega), n1 x (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
