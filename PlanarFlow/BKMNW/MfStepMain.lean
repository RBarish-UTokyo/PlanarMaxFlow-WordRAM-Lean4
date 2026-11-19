module

public import PlanarFlow.BKMNW.MfStepCost

/-!
# The whole max-flow program with the step around its subroutine programs

* **`mfMain_cMachX`**: `mfMain_cMach` (`PlanarFlow/BKMNW/MfRoot.lean`) with the step allowed
  `runsCharge + cs m + 100 m + 100 k + 106` steps at a node call (`sT m + cs m ≤ C m lg m`,
  `C ≥ 100`), by `mfDriveFrame_cMachX`.
* **`mfMain_cMachO`**: the fixed program
  `rfProg ; driver mtProg mlProg (splitS sepP) (nodeSF (stepPO cntP fixP c2sP s2cP retP frmP))`;
  the hypotheses are `SepPSpec sepP` and the six specifications of the subroutine programs of the
  step (`CntPSpec`, `FixPSpec`, `C2SPSpec`, `S2CPSpec`, `RetPSpec`, `FrmPSpec`), with the costs of
  FixConservationOnPath, of `c2s`/`s2c` and of the push-backs in the fields `fixRun`, `c2sRun`,
  `pushRun + lin` of `cMach C C₀` at the sizes of the piece map and of the part, and the counts
  within `cs m + 100 m + 100 k + 100`. Same conclusion and bound as `mfMain_cMach`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver

universe w

section Head

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **`mfMain_cMach` with room for the counts of the step** (see the module docstring). -/
theorem mfMain_cMachX (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) {C C₀ : ℕ} (hC : 100 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Z : ℕ} {gid : _ → ℕ} {sepP stepP : Stmt} {sT cs : ℕ → ℕ}
    {sR : ℕ → ℕ → ℕ} {stT rT : MCall (lpreMap M) → ℕ} {RS RT : ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepM (lpreMap M)) e n Hs A W
    let τ := decS (lpreMap M) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMap M) τ [] (rotPerm (lpreMap M))
    let N := τ.piece.card
    SepPSpec (lpreMap M) Reach gid u' S' T' Z I W sepP sT sR →
    StepPSpec (lpreMap M) (planeOracles fun X => frRef X) Reach gid u' S' T' Z I W stepP stT rT →
    (∀ m, sT m + cs m ≤ C * m * lg m) →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      stT (.node l r π, Hs, σ) ≤ runsCharge (lpreMap M) (cMach C C₀) l r π Hs σ +
        cs (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card +
        100 * (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card + 100 * Hs.length + 106) →
    (∀ m k, m ≤ N → k ≤ N → sR m k ≤ RS) → (∀ x, Reach x → rT x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 0 < Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    c₀.nreg 6700 = N → c₀.nreg 6701 = REVb → c₀.nreg 6702 = SIGb → c₀.nreg 6703 = CAPb →
    c₀.nreg 6704 = KRb → c₀.nreg 6705 = ntag τ → c₀.nreg 6706 = Z → c₀.nreg 6707 = Hb →
    (∀ i < N, c₀.nmem (REVb + i) < N ∧ en (c₀.nmem (REVb + i)) = (lpreMap M).rev (en i)) →
    (∀ i < N, c₀.nmem (SIGb + i) < N ∧
      en (c₀.nmem (SIGb + i)) = rotPerm (lpreMap M) (en i)) →
    (∀ i < N, (c₀.nmem (CAPb + i) : ℤ) = u' (en i) ∧ c₀.nmem (CAPb + i) ≤ Z) →
    (∀ i < N, c₀.nmem (KRb + i) = lrk S' T' (hunion []) ((lpreMap M).tail (en i))) →
    REVb + N ≤ Hb → SIGb + N ≤ Hb → CAPb + N ≤ Hb → KRb + N ≤ Hb →
    Hb + 9 + 7 * N + (2 * N + 1) * (39 * N + 20 + RS + RT) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq rfProg (driver mtProg mlProg (splitS sepP) (nodeSF stepP))) c₀ c' t ∧
      t ≤ 46 * N + 80 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        1000 * (2 * N + 1) + 2) ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunL (lpreMap M) (planeOracles fun X => frRef X) u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) (Hb + 9 + 7 * N) c' ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) := by
  intro pc sc τ u' S' T' Reach N hsep hstep hsT hstT hsR hrT REVb SIGb CAPb KRb en hen hgid hHb
    c₀ hc₀ r0 r1 r2 r3 r4 r5 r6 r7 hrev hsig hcap hkr i1 i2 i3 i4 hW
  obtain ⟨hbal, -, -⟩ := maxflow_plane_cost_decM hM hrot hface hu hST e hsurj d₀
    (cMach_bounds C C₀)
  have hok := callOk_root hM hrot hface hx₀ hbal
  have hW' : Hb + 9 + 7 * N ≤ W := le_trans (Nat.le_add_right _ _) hW
  obtain ⟨c₁, t₁, e₁, ht₁, hw₁, b0, b1, b2, b3, m0, m1, m2, hin, ho₁⟩ :=
    rfProg_root (I := I) (W := W) (Reach := Reach) (gid := gid) (u := u') (S := S') (T := T')
      (Z := Z) τ (rotPerm (lpreMap M)) hbal.1 (calls_self _ _ _) hok hen hgid c₀ hc₀ r0 r1 r2 r3
      r4 r5 r6 r7 hrev hsig hcap hkr i1 i2 i3 i4 hW'
  obtain ⟨hpc, c', t, ex, ht, hout, hmax⟩ := mfDriveFrame_cMachX hM hrot hface hu hST e hsurj d₀
    hC hC₀ hZ hsep hstep hsT hstT hsR hrT hHb c₁ hw₁ b0 b1 b2 b3 m0 m1 m2 (by omega) le_rfl hW
    hin
  have ht' : t ≤ (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        1000 * (2 * N + 1) + 2 := ht
  exact ⟨hpc, c', t₁ + t, .seq e₁ ex, by omega, hout, hmax⟩

/-- **The whole program with the step around its subroutine programs** (see the module
docstring). -/
theorem mfMain_cMachO (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) {C C₀ : ℕ} (hC : 100 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Z : ℕ} {gid : _ → ℕ}
    {sepP cntP fixP c2sP s2cP retP frmP : Stmt} {sT cs : ℕ → ℕ} {sR : ℕ → ℕ → ℕ}
    {cnT rO : MCall (lpreMap M) → ℕ} {fT rtT fmT : MCall (lpreMap M) → ℕ → ℕ}
    {cT s2T : MCall (lpreMap M) → ℕ → ℕ → ℕ} {RS RT : ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepM (lpreMap M)) e n Hs A W
    let τ := decS (lpreMap M) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMap M) τ [] (rotPerm (lpreMap M))
    let N := τ.piece.card
    let O := planeOracles fun X => frRef X
    let c := cMach C C₀
    SepPSpec (lpreMap M) Reach gid u' S' T' Z I W sepP sT sR →
    CntPSpec (lpreMap M) Reach gid u' S' T' Z I W cntP cnT rO →
    FixPSpec (lpreMap M) O Reach gid u' S' T' Z I W fixP fT rO →
    C2SPSpec (lpreMap M) O Reach gid u' S' T' Z I W c2sP cT rO →
    S2CPSpec (lpreMap M) O Reach gid u' S' T' Z I W s2cP s2T rO →
    RetPSpec (lpreMap M) O Reach gid u' S' T' Z I W retP rtT rO →
    FrmPSpec (lpreMap M) O Reach gid u' S' T' Z I W frmP fmT rO →
    (∀ m, sT m + cs m ≤ C * m * lg m) →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      cnT (.node l r π, Hs, σ) ≤ cs (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card +
        100 * (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card + 100 * Hs.length + 100) →
    (∀ l r π Hs σ (h : SCond (lpreMap M) l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtx (lpreMap M) O u' S' T' l r π Hs σ h).L[j]? = some πj →
      fT (.node l r π, Hs, σ) j ≤ c.fixRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
        πj.faces.card πj.k (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) ∧
      (∀ i, cT (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      (∀ i, s2T (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      rtT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) ∧
      fmT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))) →
    (∀ m k, m ≤ N → k ≤ N → sR m k ≤ RS) → (∀ x, Reach x → rO x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 0 < Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    c₀.nreg 6700 = N → c₀.nreg 6701 = REVb → c₀.nreg 6702 = SIGb → c₀.nreg 6703 = CAPb →
    c₀.nreg 6704 = KRb → c₀.nreg 6705 = ntag τ → c₀.nreg 6706 = Z → c₀.nreg 6707 = Hb →
    (∀ i < N, c₀.nmem (REVb + i) < N ∧ en (c₀.nmem (REVb + i)) = (lpreMap M).rev (en i)) →
    (∀ i < N, c₀.nmem (SIGb + i) < N ∧
      en (c₀.nmem (SIGb + i)) = rotPerm (lpreMap M) (en i)) →
    (∀ i < N, (c₀.nmem (CAPb + i) : ℤ) = u' (en i) ∧ c₀.nmem (CAPb + i) ≤ Z) →
    (∀ i < N, c₀.nmem (KRb + i) = lrk S' T' (hunion []) ((lpreMap M).tail (en i))) →
    REVb + N ≤ Hb → SIGb + N ≤ Hb → CAPb + N ≤ Hb → KRb + N ≤ Hb →
    Hb + 9 + 7 * N + (2 * N + 1) * (39 * N + 20 + RS + RT) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq rfProg (driver mtProg mlProg (splitS sepP)
        (nodeSF (stepPO cntP fixP c2sP s2cP retP frmP)))) c₀ c' t ∧
      t ≤ 46 * N + 80 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        1000 * (2 * N + 1) + 2) ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunL (lpreMap M) O u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) (Hb + 9 + 7 * N) c' ∧
      IsMax M u S T (nlRun M u S T τ O) := by
  intro pc sc τ u' S' T' Reach N O c hsep hcn hfx hc2 hs2 hrt hfm hsT hcnT hcost hsR hrO
    REVb SIGb CAPb KRb en hen hgid hHb c₀ hc₀ r0 r1 r2 r3 r4 r5 r6 r7 hrev hsig hcap hkr i1 i2 i3
    i4 hW
  have hstep := stepPO_spec hcn hfx hc2 hs2 hrt hfm
  obtain ⟨hbal, -, -⟩ := maxflow_plane_cost_decM hM hrot hface hu hST e hsurj d₀
    (cMach_bounds C C₀)
  have hok := callOk_root hM hrot hface hx₀ hbal
  refine mfMain_cMachX hM hrot hface hu hST e hsurj d₀ hx₀ hC hC₀ hZ hsep hstep hsT
    (fun l r π Hs σ hx => ?_) hsR hrO hen hgid hHb c₀ hc₀ r0 r1 r2 r3 r4 r5 r6 r7 hrev hsig hcap
    hkr i1 i2 i3 i4 hW
  have hcond : SCond (lpreMap M) l r π Hs σ := callOk_cond (callOk_calls τ [] _ _ hok hx)
  have hle := stTO_le (O := O) (u := u') (S := S') (T := T') (cnT := cnT) (fT := fT) (cT := cT)
    (sT := s2T) (rtT := rtT) (fmT := fmT) (cMach C C₀) hcond
    (fun hn => by
      have h1 : (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card ≤
          psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs) := by
        unfold psize; omega
      have h2 : 100 * 1 ≤ C * psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs) :=
        Nat.mul_le_mul hC (by omega)
      show 8 ≤ C * _
      omega)
    (fun j πj hj => (hcost l r π Hs σ hcond j πj hx hj).1)
    (fun j πj i hj => (hcost l r π Hs σ hcond j πj hx hj).2.1 i)
    (fun j πj i hj => (hcost l r π Hs σ hcond j πj hx hj).2.2.1 i)
    (fun j πj hj => (hcost l r π Hs σ hcond j πj hx hj).2.2.2.1)
    (fun j πj hj => (hcost l r π Hs σ hcond j πj hx hj).2.2.2.2)
  have := hcnT l r π Hs σ hx
  omega

end Head

end MfDrv

end BKMNW

end PlanarFlow
