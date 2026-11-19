module

public import PlanarFlow.BKMNW.StChoiceM

/-!
# The machine's s-t flow choices at the calls of the max-flow recursion

* **`stChs I enF mF fb`**: the choices of the s-t flow at every call `x` (and piece invariant
  `h`), as a function of the call: `stChoiceOf (EnumOK of enF x h) I` where the numbering
  `enF x h` of the darts of the piece map (the frame order of the call, by increasing `gid`) is
  `EnumOK` and a dual tree exists, `fb x h` otherwise;
* **`machMOS_stflow`**: the s-t flow of `machMOS gid I (stChs …)` at such a call **is**
  `(stChoiceOf … I).flow`;
* **`stChs_OK`**: the choices are valid at every call whose piece map is plane, with `EnumOK` for
  the map and its dual (the hypothesis `hok` of `NsStep.oSpecOn_machMOS`);
* **`stCallZ_machMOS`**: at such a call, `stCallZ` (`stCallZ_exec`) writes
  `max 0 (Z + (machMOS gid I (stChs …) x h).stflow c X Y (enF x h i))` at `Ob + i`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace StCall

open Finset WordRAM WordRAM.Machine STFlow NsStep MfDrv Orbit

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **Natural words only.** -/
theorem stCallZ_natOnly : Klein.natOnly stCallZ = true := by decide +kernel

theorem stCall_natOnly : Klein.natOnly stCall = true := by decide +kernel

/-- **The machine's s-t flow choices at the calls** (see the module docstring). -/
noncomputable def stChs (I : Input)
    (enF : (x : MCall M) → PieceInv M x.1.piece x.2.1 x.2.2 → ℕ → SDart (pdarts M x.1.piece x.2.1))
    (mF : MCall M → ℕ)
    (fb : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → StChoice (pmap h)) :
    (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → StChoice (pmap h) := by
  classical
  exact fun x h =>
    if hE : EnumOK (pmap h) (enF x h) (mF x) ∧ Nonempty (DTree (pmap h)) then
      @stChoiceOf _ _ _ _ _ _ _ _ _ (pmap h) (enF x h) (mF x) hE.1 I hE.2
    else fb x h

/-- **The s-t flow of `machMOS` with the machine's choices** at a call. -/
theorem machMOS_stflow (gid : D → ℕ) (I : Input)
    (enF : (x : MCall M) → PieceInv M x.1.piece x.2.1 x.2.2 → ℕ → SDart (pdarts M x.1.piece x.2.1))
    (mF : MCall M → ℕ)
    (fb : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → StChoice (pmap h))
    (x : MCall M) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    (hE : EnumOK (pmap h) (enF x h) (mF x)) [hT : Nonempty (DTree (pmap h))] :
    (machMOS gid I (stChs I enF mF fb) x h).stflow = (stChoiceOf hE I).flow := by
  classical
  show (stChs I enF mF fb x h).flow = _
  simp only [stChs, dif_pos (And.intro hE hT)]

/-- **The machine's choices are valid** at a call whose piece map is plane with `EnumOK` for
the map and its dual. -/
theorem stChs_OK (I : Input)
    (enF : (x : MCall M) → PieceInv M x.1.piece x.2.1 x.2.2 → ℕ → SDart (pdarts M x.1.piece x.2.1))
    (mF : MCall M → ℕ)
    (fb : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → StChoice (pmap h))
    (x : MCall M) (h : PieceInv M x.1.piece x.2.1 x.2.2) (hM : (pmap h).IsPlane)
    (hE : EnumOK (pmap h) (enF x h) (mF x)) (hE' : EnumOK (pmap h).dual (enF x h) (mF x))
    (hm : 0 < mF x) [hT : Nonempty (DTree (pmap h))] : (stChs I enF mF fb x h).OK := by
  classical
  simp only [stChs, dif_pos (And.intro hE hT)]
  exact stChoiceOf_OK hM hE hE' hm I

set_option maxHeartbeats 1000000 in
/-- **`stCallZ` at a call computes the s-t flow of `machMOS` with the machine's choices.** -/
theorem stCallZ_machMOS (gid : D → ℕ)
    (enF : (x : MCall M) → PieceInv M x.1.piece x.2.1 x.2.2 → ℕ → SDart (pdarts M x.1.piece x.2.1))
    (mF : MCall M → ℕ)
    (fb : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → StChoice (pmap h))
    (x : MCall M) (h : PieceInv M x.1.piece x.2.1 x.2.2) (hM : (pmap h).IsPlane)
    (hrot : (pmap h).RotTrans) (hE : EnumOK (pmap h) (enF x h) (mF x))
    (hE' : EnumOK (pmap h).dual (enF x h) (mF x)) (hm : 0 < mF x) [hT : Nonempty (DTree (pmap h))]
    {P : Input} {W : ℕ} {cp : SDart (pdarts M x.1.piece x.2.1) → ℤ} (hcp : ∀ d, 0 ≤ cp d)
    {X Y : Finset (SVert x.2.2 (pdarts M x.1.piece x.2.1))} (hXY : Disjoint X Y)
    (hXn : ∃ d, (pmap h).tail d ∈ X) (hYn : ∃ d, (pmap h).tail d ∈ Y) (c : Config)
    (hc : WordsBounded W c) {RVb RTb Cb Xb Yb ib Ob Z p Wz : ℕ}
    (r00 : c.nreg 9100 = mF x) (r01 : c.nreg 9101 = RVb) (r02 : c.nreg 9102 = RTb)
    (r03 : c.nreg 9103 = Cb) (r04 : c.nreg 9104 = Xb) (r05 : c.nreg 9105 = Yb)
    (r07 : c.nreg 9107 = ib) (r08 : c.nreg 9108 = Ob) (r09 : c.nreg 9109 = Z)
    (r10 : c.nreg 9110 = p)
    (hRV : ∀ i < mF x, c.nmem (RVb + i) = rvI (pmap h) (enF x h) (mF x) i)
    (hRT : ∀ i < mF x, c.nmem (RTb + i) = ixOf (enF x h) (mF x) ((pmap h).rot (enF x h i)))
    (hC : ∀ i < mF x, c.nmem (Cb + i) = (cp (enF x h i)).toNat)
    (hX : ∀ i < mF x, c.nmem (Xb + i) = flagX (pmap h) (enF x h) X i)
    (hY : ∀ i < mF x, c.nmem (Yb + i) = flagX (pmap h) (enF x h) Y i)
    (hz : MemZ Wz c)
    (oR : Wz < RVb) (oT : Wz < RTb) (oC : Wz < Cb) (oX : Wz < Xb) (oY : Wz < Yb)
    (wR : RVb + mF x ≤ W) (wT : RTb + mF x ≤ W) (wC : Cb + mF x ≤ W) (wX : Xb + mF x ≤ W)
    (wY : Yb + mF x ≤ W)
    (hWc : stWc (pmap h) cp X Y (mF x) ≤ Wz)
    (hib : pstWN (101 * mF x + 45) (stHb (pmap h) cp X Y (mF x)) < ib)
    (hib0 : 339 * mF x + 128 ≤ ib)
    (hibz : ib + pstWN (101 * mF x + 45) (stHb (pmap h) cp X Y (mF x)) ≤ Wz)
    (hO : Wz < Ob) (hOp : Ob + mF x ≤ p)
    (hpW : p + 3 * (4 * pcoreB (SVert x.2.2 (pdarts M x.1.piece x.2.1))
      (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) (mF x) (4 * mF x + 1) + 3) ≤ W)
    (hZW : Z + Wz ≤ W) :
    ∃ c' t, Exec P W stCallZ c c' t ∧
      t ≤ stCostZ (mF x) (4 * pcoreB (SVert x.2.2 (pdarts M x.1.piece x.2.1))
        (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) (mF x) (4 * mF x + 1) + 3) ∧
      MemZ Wz c' ∧
      (∀ i < mF x, (c'.nmem (Ob + i) : ℤ) =
        max 0 ((Z : ℤ) + (machMOS gid P (stChs P enF mF fb) x h).stflow cp X Y (enF x h i))) ∧
      (∀ a, Wz < a → (a < Ob ∨ Ob + mF x ≤ a) →
        (a < p ∨ p + 3 * (4 * pcoreB (SVert x.2.2 (pdarts M x.1.piece x.2.1))
          (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) (mF x) (4 * mF x + 1) + 3) ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ StScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  rw [machMOS_stflow gid P enF mF fb x h hE]
  exact stCallZ_exec hM hrot hE hE' hm hcp hXY hXn hYn c hc r00 r01 r02 r03 r04 r05 r07 r08 r09
    r10 hRV hRT hC hX hY hz oR oT oC oX oY wR wT wC wX wY hWc hib hib0 hibz hO hOp hpW hZW

end StCall

end BKMNW

end PlanarFlow
