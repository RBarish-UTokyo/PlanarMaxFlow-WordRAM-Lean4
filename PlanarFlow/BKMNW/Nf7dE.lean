module

public import PlanarFlow.BKMNW.Nf7dD

/-!
# `fixP` on a part with `0 < k`: the stage loop and the final step

* `SLx.wr_ge` (the cells the stage loop writes lie above `CW`), `SLx.fix_congr` (the fixed
  arrays survive a run that keeps the memory above the shadow outside `Wr`);
* **`fin7d_exec`**: from the state after step 2 (`X.Good`, `X.Regs`, `X.Fix`, `X.Stt (X.st 0)`,
  `X.Img`, the frame and the registers of the final step), `loopP ; clrP ; finP` runs within
  `loopT b k + 20 (lb + 2k) + 32 + finT C C₀ m k` steps and writes
  `fixPath (pmap hP) X.c X.f₀ X.P X.mssp X.fr (negLay gid I x hP)` into `FL`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap OrbLab NegSSSP NegSSSP.Frame MfDrv NsStep SPath
  WordRAM WordRAM.Machine WordRAM.Programs

section Gen

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- The cells written by the stage loop lie at or above `CW`. -/
lemma SLx.wr_ge {X : SLx M} {W : ℕ} (hG : X.Good W) {a : ℕ} (h : X.Wr a) : X.CWb ≤ a := by
  have := hG.l3; have := hG.l4; have := hG.l5; have := hG.l6; have := hG.l7; have := hG.l8
  have := hG.l9; have := hG.l10; have := hG.l11; have := hG.l12; have := hG.l13
  unfold SLx.Wr at h; omega

/-- The fixed arrays survive a run keeping the memory above the shadow outside `Wr`. -/
lemma SLx.fix_congr {X : SLx M} {W : ℕ} (hG : X.Good W) {nm nm' : ℕ → ℕ} (h : X.Fix nm)
    (hk : ∀ a, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → ¬ X.Wr a → nm' a = nm a) :
    X.Fix nm' := by
  have := hG.l1; have := hG.l2; have := hG.l3; have := hG.l4; have := hG.l5; have := hG.l6
  have := hG.l7; have := hG.l8; have := hG.l9; have := hG.l10; have := hG.l11; have := hG.l12
  have := hG.l13
  have K : ∀ a, X.CWb ≤ a → a < X.FWb ∨ (X.ELb + 2 * X.P.k ≤ a ∧ a < X.PWb) ∨
      (X.PRb + X.b ≤ a ∧ a < X.Ob) → nm' a = nm a := fun a h1 h2 =>
    hk a (by omega) (by omega) (fun hw => by unfold SLx.Wr at hw; omega)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun a ha => ?_,
    fun e he => ?_⟩
  · rw [K _ (by omega) (by omega)]; exact h1 l hl
  · rw [K _ (by omega) (by omega)]; exact h2 l hl
  · rw [K _ (by omega) (by omega)]; exact h3 l hl
  · rw [K _ (by omega) (by omega)]; exact h4 l hl
  · rw [K _ (by omega) (by omega)]; exact h5 a ha
  · rw [K _ (by omega) (by omega)]; exact h6 e he

end Gen

section Call

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The stage loop and the final step** (see the module docstring). -/
theorem fin7d_exec (C C₀ : ℕ) (hC : 200000 ≤ C) (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (X : SLx (pmap hP)) {W : ℕ} (hG : X.Good W) (hrot : (pmap hP).RotTrans)
    (hface : (pmap hP).FaceTrans) (hU : X.c = fun y => u y.1)
    (I P' : Input) (c : Config) (hc : WordsBounded W c) (hl : Lay M gid u S T Z x m en d c.nmem)
    (hm : 0 < m) (hFL0 : FLHas Z m d en c.nmem X.f₀) {LABb Wz : ℕ}
    (hPDm : ∀ l < X.P.k, c.nmem (c.nreg 9402 + l) < m ∧
      en (c.nmem (c.nreg 9402 + l)) = (X.P.d l).1)
    (hR : X.Regs c) (hFix : X.Fix c.nmem) (hS0 : X.Stt (X.st 0) c.nmem) (hImg : X.Img c.nmem)
    (r69 : c.nreg 9469 = X.p) (r00 : c.nreg 9400 = m) (r36 : c.nreg 9436 = 1)
    (r34 : c.nreg 9434 = d + 4 + 3 * m) (r35 : c.nreg 9435 = d + 4 + 6 * m)
    (r21 : c.nreg 9421 = Z) (r01 : c.nreg 9401 = X.P.k) (r30 : c.nreg 9430 = d + 4 + m) (r31 : c.nreg 9431 = d + 4 + 2 * m)
    (r05 : c.nreg 9405 = LABb) (r9475 : c.nreg 9475 = 0) (r71 : c.nreg 9471 = X.SH)
    (r9474 : c.nreg 9474 = X.SH + (X.Wf + 1))
    (hLAB : ∀ i < m, c.nmem (LABb + i) = olab (nxF d m c.nmem) i + 1)
    (hz : ∀ a ≤ Wz, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → c.nmem a = 0)
    (hSHz : X.SH + X.WN ≤ Wz) (hPDz : Wz < c.nreg 9402) (hS : 9 * m + 1 + tsz m ≤ Wz + 1)
    (hWzd : Wz < d)
    (hlo : d + 4 + 7 * m ≤ LABb ∧ LABb + m ≤ X.CWb ∧ c.nreg 9402 + X.P.k ≤ X.CWb)
    (hWz : rtW m (rtL (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y)) m ≤ Wz)
    (hW : 5 * X.p + LABb + 3 * d + 60 * m + 60 + c.nreg 9402 + X.CWb + X.CRb + X.FWb + X.P.k +
      negT C C₀ m ≤ W)
    (wL : 2 * X.K + rtL (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y) ≤ W)
    (hw2 : spWs m + 205 ≤ W)
    (hw3 : fxWB m (rtL (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y)) ≤ W)
    (hv : ∀ i < m, c.nmem (d + 4 + 3 * m + i) + Z + X.K + X.K +
      2 * rtL (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y) ≤ W) :
    ∃ c' t, Exec P' W (.seq loopP (.seq clrP finP)) c c' t ∧
      t ≤ loopT X.b X.P.k + (20 * (X.lb + 2 * X.P.k) + 32 + finT C C₀ m X.P.k) ∧
      FLHas Z m d en c'.nmem (fixPath (pmap hP) X.c X.f₀ X.P X.mssp X.fr (negLay gid I x hP)) ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      (∀ a, Wz < a → a < X.CWb → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, KeepR r → (r < 9477 ∨ 9498 < r) → ¬ SLx.scr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have l1 := hG.l1; have l2 := hG.l2
  obtain ⟨c₄, t₄, e₄, ht₄, S4, I4, M4, R4, rr4, rm4, o4⟩ :=
    SLx.loopP_exec' (I := P') hG c hc hR hFix hS0 hImg
  -- what the loop keeps below `CW`
  have m4 : ∀ a, X.SH + X.WN < a → a < X.CWb → c₄.nmem a = c.nmem a := fun a h1 h2 =>
    M4 a (by omega) (by omega) (fun hw => by have := SLx.wr_ge hG hw; omega)
  have hscr : ∀ r, ¬ SLx.scr r → c₄.nreg r = c.nreg r := R4
  have ns : ∀ r, (r = 9469 ∨ r = 9400 ∨ r = 9436 ∨ r = 9434 ∨ r = 9435 ∨ r = 9421 ∨ r = 9310 ∨
      r = 9401 ∨ r = 9402 ∨ r = 9430 ∨ r = 9431 ∨ r = 9374 ∨ r = 9375 ∨ r = 9376 ∨ r = 9405 ∨
      r = 7607 ∨ r = 9475 ∨ r = 9471 ∨ r = 7612 ∨ r = 9474) → c₄.nreg r = c.nreg r :=
    fun r hr => hscr r (by
      unfold SLx.scr swScr FrFix.frScr; omega)
  obtain ⟨⟨g10, g71, -, g74, g75, g76, -, -, -, -, -⟩, -, ⟨-, -, -, -, -, -, g07, -, -, -, -, g12,
    -, -, -⟩⟩ := hR
  have hl4 : Lay M gid u S T Z x m en d c₄.nmem := hl.congr fun a h1 h2 => m4 a (by omega)
    (by have := hlo.1; have := hlo.2.1; omega)
  have hFL4 : FLHas Z m d en c₄.nmem X.f₀ := fun i hi => by
    rw [m4 _ (by omega) (by have := hlo.1; have := hlo.2.1; omega)]; exact hFL0 i hi
  have hNX : ∀ i < m, nxF d m c₄.nmem i = nxF d m c.nmem i := fun i hi => by
    unfold nxF
    have := hlo.1; have := hlo.2.1
    have h1 := (hl.rv i hi).1
    rw [m4 (d + 4 + m + i) (by omega) (by omega), m4 _ (by omega) (by omega)]
  have hLAB4 : ∀ i < m, c₄.nmem (LABb + i) = olab (nxF d m c₄.nmem) i + 1 := fun i hi => by
    have := hlo.1; have := hlo.2.1
    rw [m4 _ (by omega) (by omega), hLAB i hi,
      olab_congr (f := nxF d m c₄.nmem) (g := nxF d m c.nmem) hNX hl4.permOn_nx hi]
  have hPDm4 : ∀ l < X.P.k, c₄.nmem (c.nreg 9402 + l) < m ∧
      en (c₄.nmem (c.nreg 9402 + l)) = (X.P.d l).1 := fun l hl' => by
    have := hlo.2.2
    rw [m4 _ (by omega) (by omega)]; exact hPDm l hl'
  have hz4 : ∀ a ≤ Wz, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → c₄.nmem a = 0 :=
    fun a h1 h2 h3 => by
      rw [M4 a h2 h3 (fun hw => by have := SLx.wr_ge hG hw; omega)]; exact hz a h1 h2 h3
  have hv4 : ∀ i < m, c₄.nmem (d + 4 + 3 * m + i) + Z + X.K + X.K +
      2 * rtL (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y) ≤ W := fun i hi => by
    have := hlo.1; have := hlo.2.1
    rw [m4 _ (by omega) (by omega)]; exact hv i hi
  have hTb : LABb + m ≤ X.p ∧ c.nreg 9402 + X.P.k ≤ X.p ∧ X.CWb + X.P.k ≤ X.p ∧
      X.CRb + X.P.k ≤ X.p ∧ X.FWb + X.P.k ≤ X.p := by
    have := hG.l13; have := hG.l12; have := hG.l11; have := hG.l10; have := hG.l9
    have := hG.l8; have := hG.l7; have := hG.l6; have := hG.l5; have := hG.l4; have := hG.l3
    omega
  obtain ⟨c₅, t₅, e₅, ht₅, F5, z5, k5, r5, rr5, rm5, o5⟩ :=
    fixFin_exec C C₀ hC hP X hG hrot hface hU I P' c₄ e₄.wb_right hl4 hm hFL4 (Tb := X.p)
      (PDb := c.nreg 9402) (LABb := LABb) (Wz := Wz) hPDm4
      (by rw [ns _ (by omega), r69]) (by rw [ns _ (by omega), r00]) (by rw [ns _ (by omega), r36])
      (by rw [ns _ (by omega), r34]) (by rw [ns _ (by omega), r35]) (by rw [ns _ (by omega), r21])
      (by rw [ns _ (by omega), g10]) (by rw [ns _ (by omega), r01])
      (by rw [ns _ (by omega)]) (by rw [ns _ (by omega), r30]) (by rw [ns _ (by omega), r31])
      (by rw [ns _ (by omega), g74]) (by rw [ns _ (by omega), g75]) (by rw [ns _ (by omega), g76])
      (by rw [ns _ (by omega), r05]) (by rw [ns _ (by omega), g07]) (by rw [ns _ (by omega), r9475])
      (by rw [ns _ (by omega), r71]) (by rw [ns _ (by omega), g12])
      (by rw [ns _ (by omega), r9474]) hLAB4 S4 (SLx.fix_congr hG hFix M4) I4 hz4 hSHz hPDz
      (by omega) hS hWzd
      ⟨hlo.1, hTb⟩
      hWz hW wL hw2 hw3 hv4
  refine ⟨c₅, _, e₄.seq e₅, by omega, F5, z5, fun a h1 h2 h3 => ?_, fun r hr h1 h2 => ?_,
    by rw [rr5, rr4], by rw [rm5, rm4], by rw [o5, o4]⟩
  · have := hG.l13; have := hG.l12; have := hG.l11; have := hG.l10; have := hG.l9
    have := hG.l8; have := hG.l7; have := hG.l6; have := hG.l5; have := hG.l4; have := hG.l3
    rw [k5 a h1 (by omega) h3, m4 a (by omega) h2]
  · rw [r5 r hr h1, hscr r h2]

end Call

end BKMNW

end PlanarFlow
