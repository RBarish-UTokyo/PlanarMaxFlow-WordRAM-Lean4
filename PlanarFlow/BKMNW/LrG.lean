module

public import PlanarFlow.BKMNW.LrF

/-!
# The children's records of the large split: one child composed

* **`LrIn`**: the state before a child's run (the registers of stage B, `SmRegs`, the parent's
  record `RArr` at `R` with its state array on the core's piece map `B = pdarts (core Q P) Hs`,
  the flags `CV`, `HM` at `A + 3 n`, `A + 4 n`, the extended state `SG` at `Y`, the reverses at
  `Y + n`, the path flags at `Y + 2 n`, the core flags `CC` at `CCb`, the layout);
  `LrIn.congr` (it reads the memory outside `[A + n, A + 2 n)`, `[A + 4 n + k + 2, Y)`,
  `[Y + 3 n, Y + 8 n)` and the records' area `[Y + 8 n, Y + 22 n + 20)`);
* **`lrOne = lrOneA ; lrCr ; lrOneB`**, **`lrOne_rec`**: for a child `X ⊆ P` (flags
  `|t - LF[i]| = bf (g i ∈ X)`), a call `y` with `y.1 = ds.dec S T X (childHoles Hs C) st' b'`,
  `st' = childRot st B ρ.darts (pdarts (core Q X) (childHoles Hs C))` (= `chRot`), within
  `400 n + 21 k + 310` steps the record **`RecAt y (XX + 2) z`** (`z = r8510 ≤ 7 n + 3`), `LrIn`
  again, memory outside the scratch and `[XX + 2, XX + 7 n + 6)` kept.
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

variable (M ds gid ν S T) in
/-- **The state before a child's run** (see the module docstring). -/
structure LrIn (c : Config) (x : MCall M) (P : Finset D) (Hs : List (Finset V)) (ρ : HPath M)
    (st : Perm D) (g : ℕ → D) (d m k R n Sb A Y LFb CCb W : ℕ) : Prop where
  regs : SmRegs c d m k R n Sb A
  r21 : c.nreg 6521 = 1
  r00 : c.nreg 8500 = LFb
  r84 : c.nreg 8504 = CCb
  r06 : c.nreg 8506 = Y
  r16 : c.nreg 8516 = Y + 3 * n
  r17 : c.nreg 8517 = Y + 6 * n
  hY : Y = A + 16 * n + 4 * k + 2
  oR : R + 3 + 6 * n + m ≤ Sb
  oL : Y + 22 * n + 20 ≤ LFb
  oC : Y + 22 * n + 20 ≤ CCb
  wA : A + 22 * n + m + 4 * k + 20 ≤ W
  wL : LFb + n ≤ W
  wC : CCb + n ≤ W
  hW : 21 ≤ W
  arr : RArr M gid ν S T x m n R g c.nmem
  hP : x.1.piece = P
  hHs : x.2.1 = Hs
  hk : Hs.length = k
  pw : Hs.Pairwise Disjoint
  hSC : Disjoint S ρ.mverts
  hTC : Disjoint T ρ.mverts
  hSA : Disjoint S (hunion Hs)
  stab : Stable st (pdarts M (core M ds.Q P) Hs)
  sp : ∀ i < n, g i ∈ pdarts M (core M ds.Q P) Hs →
    c.nmem (R + 3 + 5 * n + i) < n ∧ g (c.nmem (R + 3 + 5 * n + i)) = st (g i)
  cv : ∀ i < n, c.nmem (A + 3 * n + i) = bf (M.tail (g i) ∈ ρ.mverts)
  hm : ∀ j < Hs.length, c.nmem (A + 4 * n + j) = bf (¬ Disjoint (Hs.getD j ∅) ρ.mverts)
  sg : ∀ i < n, c.nmem (Y + i) =
    if c.nmem (CCb + i) = 0 then i else c.nmem (R + 3 + 5 * n + i)
  rv : ∀ i < n, c.nmem (Y + n + i) = c.nmem (R + 3 + n + i)
  pf : ∀ i < n, c.nmem (Y + 2 * n + i) = bf (g i ∈ ρ.darts.toFinset)
  cc : ∀ i < n, c.nmem (CCb + i) = bf (g i ∈ pdarts M (core M ds.Q P) Hs)

/-- `LrIn` survives a run that keeps the registers it reads and the memory outside the scratch. -/
lemma LrIn.congr {c c' : Config} {x : MCall M} {P : Finset D} {Hs : List (Finset V)}
    {ρ : HPath M} {st : Perm D} {g : ℕ → D} {d m k R n Sb A Y LFb CCb W : ℕ}
    (h : LrIn M gid ν S T ds c x P Hs ρ st g d m k R n Sb A Y LFb CCb W)
    (hR' : SmRegs c' d m k R n Sb A) (h21 : c'.nreg 6521 = 1)
    (h8 : ∀ x, (x = 8500 ∨ x = 8504 ∨ x = 8506 ∨ x = 8516 ∨ x = 8517) → c'.nreg x = c.nreg x)
    (hm : ∀ a, (a < Sb ∨ (A + 3 * n ≤ a ∧ a < A + 4 * n + k) ∨ (Y ≤ a ∧ a < Y + 3 * n) ∨
      Y + 22 * n + 20 ≤ a) → c'.nmem a = c.nmem a) :
    LrIn M gid ν S T ds c' x P Hs ρ st g d m k R n Sb A Y LFb CCb W := by
  have hA := h.regs.hA
  have hY := h.hY
  have oR := h.oR
  have oL := h.oL
  have oC := h.oC
  refine ⟨hR', h21,
    (h8 _ (by norm_num)).trans h.r00, (h8 _ (by norm_num)).trans h.r84,
    (h8 _ (by norm_num)).trans h.r06,
    (h8 _ (by norm_num)).trans h.r16, (h8 _ (by norm_num)).trans h.r17, hY, oR, oL, oC, h.wA, h.wL,
    h.wC, h.hW, h.arr.congr fun a a1 a2 => hm a (Or.inl (by clear * - a2 oR; omega)),
    h.hP, h.hHs, h.hk, h.pw, h.hSC, h.hTC, h.hSA, h.stab, fun i hi => ?_, fun i hi => ?_,
    fun j hj => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hm _ (Or.inl (by clear * - hi oR; omega))]
    exact h.sp i hi
  · rw [hm _ (Or.inr (Or.inl (by clear * - hi; omega)))]; exact h.cv i hi
  · rw [hm _ (Or.inr (Or.inl (by rw [h.hk] at hj; clear * - hj; omega)))]; exact h.hm j hj
  · rw [hm _ (Or.inr (Or.inr (Or.inl (by clear * - hi; omega)))),
      hm _ (Or.inr (Or.inr (Or.inr (by clear * - hi oC; omega)))),
      hm _ (Or.inl (by clear * - hi oR; omega))]
    exact h.sg i hi
  · rw [hm _ (Or.inr (Or.inr (Or.inl (by clear * - hi; omega)))),
      hm _ (Or.inl (by clear * - hi oR; omega))]
    exact h.rv i hi
  · rw [hm _ (Or.inr (Or.inr (Or.inl (by clear * - hi; omega))))]; exact h.pf i hi
  · rw [hm _ (Or.inr (Or.inr (Or.inr (by clear * - hi oC; omega))))]; exact h.cc i hi

/-- **One child's record.** -/
def lrOne : Stmt := .seq lrOneA (.seq lrCr lrOneB)

end MfDrv

end BKMNW

end PlanarFlow
