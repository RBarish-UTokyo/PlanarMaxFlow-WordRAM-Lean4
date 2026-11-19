module

public import PlanarFlow.BKMNW.SgSem

/-!
# `sgProg` writes `SegsOut'` (the parts of `sepL`'s separator)

**`sgProg_segsOut`**: from the path's darts in memory (`PathPD M e' n' PDb c ρ`, as `lgS5D_exec`
gives them in Miller's case), the core's enumeration through the record (`g (IX[i]) = e' i`), the
record's hole labels (`HP[i] = hlab Hs (tail (g i))`), the frame through the record
(`g (FX[f]) = en f`, `en` injective on the frame), every core dart a frame dart, a simple path
`ρ` and `π.segs = segsF ρ Hs`: within `110 n' + 7 m + 100` steps `SegsOut' M en m π lo hi Gb`
from `Gb = r6502` (`lo ≤ Gb`, `Gb + 2 n' + 3 ≤ hi`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset WordRAM WordRAM.Machine

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

section Exec

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **`sgProg` writes `SegsOut'`** (see the module docstring). -/
theorem sgProg_segsOut (c : Config) (hc : WordsBounded W c) {n' PDb IXb HPb m FXb Z Gb n lo hi : ℕ}
    (r00 : c.nreg 7200 = n') (r01 : c.nreg 7201 = PDb) (r02 : c.nreg 7202 = IXb)
    (r03 : c.nreg 7203 = HPb) (r04 : c.nreg 7204 = m) (r05 : c.nreg 7205 = FXb)
    (r06 : c.nreg 7206 = Z) (r07 : c.nreg 7207 = Gb) (r08 : c.nreg 7208 = n)
    (r21 : c.nreg 6521 = 1)
    {ρ : HPath M} {Hs : List (Finset V)} (hρ : ρ.Simple Hs) {π : HSep M}
    (hπ : π.segs = segsF ρ Hs) {g en e' : ℕ → D}
    (hPD : PathPD M e' n' PDb c ρ)
    (hIX : ∀ i < n', c.nmem (IXb + i) < n ∧ g (c.nmem (IXb + i)) = e' i)
    (hHP : ∀ i < n, c.nmem (HPb + i) = hlab Hs (M.tail (g i)))
    (hFX : ∀ f < m, c.nmem (FXb + f) < n ∧ g (c.nmem (FXb + f)) = en f)
    (hginj : ∀ i < n, ∀ j < n, g i = g j → i = j)
    (heninj : ∀ i < m, ∀ j < m, en i = en j → i = j)
    (hcov : ∀ i < n', ∃ f < m, en f = e' i)
    (lay : PDb + n' ≤ Gb ∧ IXb + n' ≤ Gb ∧ HPb + n ≤ Gb ∧ FXb + m ≤ Gb ∧ Gb + 2 * n' + 3 ≤ Z ∧
      Z + 8 * n' + n + 2 ≤ W) (hm : m + 1 ≤ W) (hlo : lo ≤ Gb) (hhi : Gb + 2 * n' + 3 ≤ hi) :
    ∃ c' t, Exec P W sgProg c c' t ∧ t ≤ 110 * n' + 7 * m + 100 ∧
      SegsOut' M en m π lo hi Gb c'.nmem ∧ c'.nreg 6502 = Gb ∧
      (∀ a, ¬ (Gb ≤ a ∧ a < Gb + 2 * n' + 3) → ¬ (Z ≤ a ∧ a < Z + 8 * n' + n + 1) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4100 ∨ (4113 < x ∧ x < 4600) ∨ (4605 < x ∧ x < 6300) ∨
        (6309 < x ∧ x < 6502) ∨ (6502 < x ∧ x < 6520) ∨ x = 6521 ∨ (6529 < x ∧ x < 7210) ∨
        7229 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hk, hPD1, hPD0⟩ := hPD
  have hpd : ∀ j ≤ ρ.k, 1 ≤ c.nmem (PDb + j) ∧ c.nmem (PDb + j) ≤ n' := fun j hj => by
    obtain ⟨i, hi, h1, -⟩ := hPD1 j hj; omega
  obtain ⟨c', t, e, ht, g0, gOL, gD, gV, hL, g502, gm, gn, grr, grm, go⟩ :=
    sgProg_exec (P := P) c hc r00 r01 r02 r03 r04 r05 r06 r07 r08 r21 hk hpd hPD0
      (fun q hq => (hIX q hq).1) (fun f hf => (hFX f hf).1)
      (fun i hi j hj h => heninj i hi j hj (by rw [← (hFX i hi).2, ← (hFX j hj).2, h]))
      lay hm _ rfl
  refine ⟨c', t, e, ht, ?_, g502, gm, gn, grr, grm, go⟩
  exact segsOut'_sg hρ hπ (g := g) (en := en) (e' := e') (n := n) (n' := n') (m := m)
    (pd := fun j => c.nmem (PDb + j)) (ix := fun i => c.nmem (IXb + i))
    (hp := fun i => c.nmem (HPb + i)) (fx := fun f => c.nmem (FXb + f)) c'.nmem hk hPD1 hIX hHP
    hFX hginj hcov _ rfl g0 gOL gD gV hL hlo hhi

end Exec

end MfDrv

end BKMNW

end PlanarFlow
