module

public import PlanarFlow.BKMNW.LsH

/-!
# `sepL`: the outputs 1–4 again after the records (`lsH ; s7O1 ; s7G`)

`lrecT` keeps only the memory below `Sb` and from `E`, so the outputs 1–4 of stage 7 at
`[Sb, Sb + 3 m + k)` are written again from the flags in the scratch (kept by `lrecT`).

**`ls9_exec`** (`30 m + 7 k + 80` steps): `Sb + i = [en i ∈ X]`, `Sb + m + i = [en i ∈ Y]`,
`Sb + 2 m + i = [tail (en i) ∈ C]` (`i < m`), `Sb + 3 m + j = HT[j]` (`j < k`), from the flags of
`X` (`LF`), `Y` (`DF`), `C` (`VF`) on the record and the hole flags; memory outside
`[Sb, Sb + 3 m + k)` kept.
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

/-- The outputs 1–4 written again. -/
def ls9 : Stmt := .seq lsH (.seq s7O1 s7G)

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **The outputs 1–4** (see the module docstring). -/
theorem ls9_exec (c : Config) (hc : WordsBounded W c) {g en : ℕ → D} {m k R n Sb U : ℕ}
    (hR : LsR c m k R n Sb) (hL : LsL c n k U)
    (hU : U = Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3)
    (hFX : ∀ i < m, c.nmem (R + 3 + 6 * n + i) < n ∧ g (c.nmem (R + 3 + 6 * n + i)) = en i)
    {X Y : Finset D} {C : Finset V} {hf : ℕ → ℕ}
    (hLF : ∀ i < n, c.nmem (U + 44 * n + 9 * k + 14 + i) = bf (g i ∈ X))
    (hDF : ∀ i < n, c.nmem (U + 4 * n + k + 2 + i) = bf (g i ∈ Y))
    (hVF : ∀ i < n, c.nmem (U + 5 * n + k + 3 + i) = bf (M.tail (g i) ∈ C))
    (hHT : ∀ j < k, c.nmem (U + 11 * n + k + 4 + j) = hf j)
    (lR : R + 3 + 6 * n + m ≤ Sb) (w : U + 46 * n + 9 * k + 15 ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W ls9 c c' t ∧ t ≤ 30 * m + 7 * k + 80 ∧
      (∀ i < m, c'.nmem (Sb + i) = bf (en i ∈ X)) ∧
      (∀ i < m, c'.nmem (Sb + m + i) = bf (en i ∈ Y)) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = bf (M.tail (en i) ∈ C)) ∧
      (∀ j < k, c'.nmem (Sb + 3 * m + j) = hf j) ∧
      (∀ a, ¬ (Sb ≤ a ∧ a < Sb + 3 * m + k) → c'.nmem a = c.nmem a) ∧
      LsR c' m k R n Sb ∧ LsL c' n k U ∧
      (∀ x, (x < 4910 ∨ (4916 < x ∧ x < 6210) ∨ (6217 < x ∧ x < 7100) ∨ (7199 < x ∧ x < 8564) ∨
        (8564 < x ∧ x < 8587) ∨ 8588 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ls9
  obtain ⟨c₁, t₁, e₁, ht₁, h30, h31, h86, h00, h93, h32, h02, h33, h34, h35, h36, h37, n1, m1,
    rr1, rm1, o1⟩ := lsH_exec (I := I) c hc hR hL hU.symm (by omega) w w2
  have F1 : ∀ i < m, c₁.nmem (R + 3 + 6 * n + i) < n := fun i hi => by rw [m1]; exact (hFX i hi).1
  obtain ⟨c₂, t₂, e₂, ht₂, O1, m2, n2, rr2, rm2, o2⟩ := s7O1_exec (P := I) c₁ e₁.wb_right
    h30 h31 h86 h00 h93 F1 ⟨by omega, by omega, by omega⟩ (by omega)
  have q2 : ∀ x, (x < 6210 ∨ 6217 < x) → x ≠ 7198 → c₂.nreg x = c₁.nreg x := n2
  obtain ⟨c₃, t₃, e₃, ht₃, G1, G2, G3, m3, n3, rr3, rm3, o3⟩ := s7G_exec' (P := I) c₂ e₂.wb_right
    (n := n) (HTb := U + 11 * n + k + 3)
    ((q2 _ (by omega) (by omega)).trans h30) ((q2 _ (by omega) (by omega)).trans h31)
    ((q2 _ (by omega) (by omega)).trans h32) ((q2 _ (by omega) (by omega)).trans h02)
    ((q2 _ (by omega) (by omega)).trans h33) ((q2 _ (by omega) (by omega)).trans h34)
    ((q2 _ (by omega) (by omega)).trans h35)
    ((q2 _ (by omega) (by omega)).trans (by rw [h36]))
    ((q2 _ (by omega) (by omega)).trans h37)
    (fun i hi => by rw [m2 _ (by omega)]; exact F1 i hi)
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩ (by omega)
  have M2 : ∀ a, (a < Sb ∨ Sb + m ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [m2 a (by omega), m1]
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, fun j hj => ?_, fun a ha => ?_, hR.congr fun x hx => ?_,
    hL.congr fun x hx => ?_, fun x hx => ?_, by rw [rr3, rr2, rr1], by rw [rm3, rm2, rm1],
    by rw [o3, o2, o1]⟩
  · rw [m3 _ (by omega), O1 i hi, m1]
    have h1 := hFX i hi
    rw [show U + 43 * n + 9 * k + 14 + n + c.nmem (R + 3 + 6 * n + i) =
      U + 44 * n + 9 * k + 14 + c.nmem (R + 3 + 6 * n + i) by omega, hLF _ h1.1, h1.2]
  · have h1 := hFX i hi
    rw [G1 i hi, M2 _ (Or.inr (by omega)), M2 _ (Or.inl (by omega)), hDF _ h1.1, h1.2]
  · have h1 := hFX i hi
    rw [G2 i hi, M2 _ (Or.inr (by omega)), M2 _ (Or.inl (by omega)), hVF _ h1.1, h1.2]
  · rw [G3 j hj, M2 _ (Or.inr (by omega)),
      show U + 11 * n + k + 3 + 1 + j = U + 11 * n + k + 4 + j by omega, hHT j hj]
  · rw [m3 a (by omega), m2 a (by omega), m1]
  all_goals rw [n3 x (by omega), q2 x (by omega) (by omega), n1 x (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
