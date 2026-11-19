module

public import PlanarFlow.BKMNW.LsF

/-!
# `sepL`: the children's records and tags (`lsF ; lrecT 100000`)

**`ls8_exec`**: `lrecT_rec` with its inputs taken from the scratch of stages 6–7 (`LF` at
`U + 44 n + 9 k + 14`, `CV = VF` at `U + 5 n + k + 3`, the hole flags at `U + 11 n + k + 4`,
`PF = DF` at `U + 4 n + k + 2`, `CC` at `U + 45 n + 9 k + 15`, `hb = r8559`): within
`1600 n + 100 k + 1330` steps the tags at `Sb + 3 m + k`, `+ 1` and `RecsOut … (Sb + 21 m + 4 k + 2)
E (r6501)`; memory below `Sb` and from `E` kept.
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

variable {gid : D → ℕ} {ν : V → ℕ} {S T : Finset V} {ds : DSys M}

/-- The records and tags of `sepL`. -/
def ls8 : Stmt := .seq lsF (lrecT 100000)

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The children's records and tags** (see the module docstring). -/
theorem ls8_exec (c : Config) (hc : WordsBounded W c) {l r : ADec M} {π : HSep M}
    {Hs : List (Finset V)} {σ st : Perm D} {g : ℕ → D} {d m k R n Sb U : ℕ}
    (hR : LsR c m k R n Sb) (hL : LsL c n k U) (hU : U = Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3)
    (r4 : c.nreg 3004 = d) (hm : c.nmem d = m)
    (hk : c.nmem (d + 1) = k) (hRm : c.nmem (d + 7 * m + 4) = R) (hn : c.nmem R = n)
    (o1 : R + 3 + 6 * n + m ≤ Sb) (o2 : d + 7 * m + 4 < R)
    (w : U + 46 * n + 9 * k + 15 ≤ W) (w2 : 50 ≤ W)
    (arr : RArr M gid ν S T (.node l r π, Hs, σ) m n R g c.nmem)
    (hk' : Hs.length = k) (pw : Hs.Pairwise Disjoint)
    (hSC : Disjoint S π.path.mverts) (hTC : Disjoint T π.path.mverts)
    (hSA : Disjoint S (hunion Hs))
    (stab : Stable st (pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs))
    (sp : ∀ i < n, g i ∈ pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs →
      c.nmem (R + 3 + 5 * n + i) < n ∧ g (c.nmem (R + 3 + 5 * n + i)) = st (g i))
    (hLF : ∀ i < n, c.nmem (U + 44 * n + 9 * k + 14 + i) = bf (g i ∈ l.piece))
    (hCV : ∀ i < n, c.nmem (U + 5 * n + k + 3 + i) = bf (M.tail (g i) ∈ π.path.mverts))
    (hHM : ∀ j < Hs.length, c.nmem (U + 11 * n + k + 4 + j) =
      bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts))
    (hPF : ∀ i < n, c.nmem (U + 4 * n + k + 2 + i) = bf (g i ∈ π.path.darts.toFinset))
    (hCC : ∀ i < n, c.nmem (U + 45 * n + 9 * k + 15 + i) =
      bf (g i ∈ pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs))
    (hlr : ∀ i < n, g i ∈ r.piece ↔ g i ∉ l.piece)
    (hlrev : ∀ d ∈ l.piece, M.rev d ∈ l.piece) (hrrev : ∀ d ∈ r.piece, M.rev d ∈ r.piece)
    (hl : l = ds.dec S T l.piece (childHoles Hs π.path.mverts)
      (childRot M st (pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs) π.path.darts
        (pdarts M (core M ds.Q l.piece) (childHoles Hs π.path.mverts)))
        (decide (1 - c.nreg 8559 = 1)))
    (hr : r = ds.dec S T r.piece (childHoles Hs π.path.mverts)
      (childRot M st (pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs) π.path.darts
        (pdarts M (core M ds.Q r.piece) (childHoles Hs π.path.mverts)))
        (decide (1 - c.nreg 8559 = 1)))
    (hν : Injective ν) (hpk : PkMin gid ds.pk) (hloop : ∀ d, M.head d ≠ M.tail d)
    (hs : ds.s = 100000) (hsW : 100000 ≤ W) (hlargeL : ds.s < l.piece.card → ntag l = 1)
    (hlargeR : ds.s < r.piece.card → ntag r = 1) :
    ∃ c' t, Exec I W ls8 c c' t ∧ t ≤ 1600 * n + 100 * k + 1330 ∧
      c'.nmem (Sb + 3 * m + k) = ntag l ∧ c'.nmem (Sb + 3 * m + k + 1) = ntag r ∧
      RecsOut M ds gid ν S T l r π Hs σ (Sb + 21 * m + 4 * k + 2)
        (Sb + 21 * m + 38 * n + 8 * k + 24) (c'.nreg 6501) c'.nmem ∧
      (∀ a, (a < Sb ∨ Sb + 21 * m + 38 * n + 8 * k + 24 ≤ a) → c'.nmem a = c.nmem a) ∧
      LsR c' m k R n Sb ∧ LsL c' n k U ∧
      (∀ x, (x < 3013 ∨ (8550 ≤ x ∧ x < 8564) ∨ (8564 < x ∧ x < 8588) ∨ 8588 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ls8
  obtain ⟨c₁, t₁, e₁, ht₁, f00, f01, f02, f03, f04, f05, f6500, n1, m1, rr1, rm1, o1'⟩ :=
    lsF_exec (I := I) c hc hR hL w w2
  have q1 : ∀ x, (x < 3013 ∨ (8505 < x ∧ x < 8564) ∨ (8564 < x ∧ x < 8588) ∨ 8588 < x) →
      c₁.nreg x = c.nreg x := fun x hx => n1 x (by omega)
  have hR1 : LsR c₁ m k R n Sb := hR.congr fun x hx => q1 x (by omega)
  have hL1 : LsL c₁ n k U := hL.congr fun x hx => q1 x (by omega)
  rw [← m1] at hm hk hRm hn arr sp hLF hCV hHM hPF hCC
  obtain ⟨c₂, t₂, e₂, ht₂, tl, tr, hRO, m2, n2, rr2, rm2, o2⟩ := lrecT_rec (I := I) (ds := ds)
    (s := 100000) c₁ e₁.wb_right (st := st) (g := g) (hb := c.nreg 8559)
    ((q1 _ (by omega)).trans r4) f6500 hm hk hRm hn o1 o2 f00 f01 f02 f03 f04 f05
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) arr hk' pw hSC hTC hSA stab sp
    hLF
    hCV hHM hPF hCC hlr hlrev hrrev hl hr hν hpk hloop hs hsW hlargeL hlargeR
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, tl, tr, hRO, fun a ha => by rw [m2 a ha, m1],
    hR1.congr fun x hx => n2 x (by omega), hL1.congr fun x hx => n2 x (by omega),
    fun x hx => ?_, by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1']⟩
  rw [n2 x (by omega), q1 x (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
