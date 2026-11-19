module

public import PlanarFlow.BKMNW.MfStepO

/-!
# The whole max-flow program with subroutines depending on the call

`mfDriveFrame_cMachX`, `mfMain_cMachX`, `mfMain_cMachO` restated relative to `arunLO`
(`PlanarFlow/BKMNW/LocalO.lean`): the planar subroutines `NO x h` may depend on the call, as the
outputs of machine runs do.

* **`mfDriveFrame_cMachXO`**, **`mfMain_cMachXO`**: the fixed program, the step meeting
  `StepPSpecC` for the flows `cflowO` of `arunLO`; the subroutines meet their specifications at the
  calls of the decomposition (`OSpecOn`); the flow in the root frame is that of `arunLO`, and
  `nlRunO` is a maximum flow. Same bound as `mfMain_cMachX`.
* **`mfMain_cMachOC`**: the fixed program
  `rfProg ; driver mtProg mlProg (splitS sepP) (nodeSF (stepPO cntP fixP c2sP s2cP retP frmP))`
  with the hypotheses `SepPSpec`, `OSpecOn NO`, `CntPSpec`, `FixPSpecO`, `C2SPSpecO`, `S2CPSpecO`,
  `RetPSpecO`, `FrmPSpecO` (the subroutine programs compute the outputs of `impl` with the
  subroutines `NO x` of the call) and the costs of `mfMain_cMachO`. Same bound.
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

/-- **`mfDriveFrame_cMachX` with subroutines depending on the call**: the same program and bound;
the step meets `StepPSpecC` for the flows of `arunLO`, the subroutines `NO` meet their
specifications at the calls of the decomposition (`OSpecOn`), and the flow is a maximum flow
(`nlRunO_isMax`, which needs a dart of `M` that is not a loop). -/
theorem mfDriveFrame_cMachXO (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) {NO : MOFam (lpreMap M)} {C C₀ : ℕ} (hC : 100 ≤ C)
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
    OSpecOn (lpreMap M) NO Reach →
    StepPSpecC (lpreMap M) (cflowO (lpreMap M) NO u' S' T') Reach gid u' S' T' Z I W stepP stT rT →
    (∀ m, sT m + cs m ≤ C * m * lg m) →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      stT (.node l r π, Hs, σ) ≤ runsCharge (lpreMap M) (cMach C C₀) l r π Hs σ +
        cs (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card +
        100 * (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card + 100 * Hs.length + 106) →
    (∀ m k, m ≤ N → k ≤ N → sR m k ≤ RS) → (∀ x, Reach x → rT x ≤ RT) →
    0 < Hb → ∀ {eF h : ℕ} (c₀ : Config), WordsBounded W c₀ → c₀.nreg 3000 = 0 →
    c₀.nreg 3001 = 1 → c₀.nreg 3002 = Hb → c₀.nreg 3003 = h → c₀.nmem Hb = 0 →
    c₀.nmem (Hb + 1) = 0 → c₀.nmem (Hb + 2) = eF → Hb + 5 ≤ eF → eF ≤ h →
    h + (2 * N + 1) * (39 * N + 20 + RS + RT) ≤ W →
    FInL (lpreMap M) Reach gid u' S' T' Z (τ, [], rotPerm (lpreMap M)) (Hb + 5) eF c₀ →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (driver mtProg mlProg (splitS sepP) (nodeSF stepP)) c₀ c' t ∧
      t ≤ (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        1000 * (2 * N + 1) + 2 ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunLO (lpreMap M) NO u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) eF c' ∧
      IsMax M u S T (nlRunO M u S T τ NO) := by
  intro pc sc τ u' S' T' Reach N hsep hO hstep hsT hstT hsR hrT hHb eF h c₀ hc₀ r0 r1 r2 r3 m0 m1
    m2 he hh hroom hin
  obtain ⟨hbal, -, hcost⟩ := maxflow_plane_cost_decM hM hrot hface hu hST e hsurj d₀
    (cMach_bounds C C₀)
  have hcore := ADec.BalA.core hbal.2.2.2.2
  have hsz := asize_le hcore
  have hok0 := hin.2.1
  have hsize : ∀ x, Reach x → (pdarts (lpreMap M) x.1.piece x.2.1).card ≤ N ∧
      x.2.1.length ≤ N ∧ x.1.piece.card ≤ N := fun x hx => by
    have h1 := calls_size τ [] _ x hcore hx
    have h2 := card_le_card (pdarts_subset (M := lpreMap M) x.1.piece x.2.1)
    simp only [List.length_nil, zero_add] at h1
    exact ⟨by omega, by omega, by omega⟩
  have hR : ∀ x, Reach x → rSp (lpreMap M) sR x + rT x ≤ 39 * N + 20 + RS + RT := fun x hx => by
    obtain ⟨a1, a2, -⟩ := hsize x hx
    have := hsR _ _ a1 a2
    have := hrT x hx
    unfold rSp; omega
  have hrm := roomC_le_on (M := lpreMap M) (rL := fun _ => 0) (rS := rSp (lpreMap M) sR)
    (rN := rT) Reach (fun _ _ => Nat.zero_le _) hR τ [] (rotPerm (lpreMap M)) (fun x hx => hx)
  have hsz' := Nat.mul_le_mul_right (39 * N + 20 + RS + RT) hsz
  obtain ⟨c', t, ex, ht, hout, -, -⟩ := mfDriveFrameO hsep
    (fun l r π Hs σ hx => calls_child τ [] _ l r π Hs σ hx) hZ (nodeSF_specC (Hb := Hb) hstep)
    hHb τ [] (rotPerm (lpreMap M)) c₀ hc₀ r0 r1 r2 r3 m0 m1 m2 he hh
    ((Nat.add_le_add_left (hrm.trans hsz') h).trans hroom) hin
  have hm := mcost_le_on (M := lpreMap M) (tc := fun _ => 3)
    (lc := fun x => 20 * (pdarts (lpreMap M) x.1.piece x.2.1).card + 17)
    (sc := scp (lpreMap M) sT) (nc := ncF (lpreMap M) stT) (cMach C C₀) (A := 1) (B := 1000)
    Reach (fun Q Hs σ _ => by
      have := Nat.mul_le_mul_right (pdarts (lpreMap M) Q Hs).card hC₀
      simp only [cMach, ADec.piece]; omega)
    (fun l r π Hs σ hx => by
      have hok := callOk_calls τ [] _ _ hok0 hx
      have hcond := callOk_cond hok
      rw [nodeCharge_eq _ hcond]
      obtain ⟨a1, a2, a3⟩ := hsize _ hx
      have hs := hstT l r π Hs σ hx
      simp only [ADec.piece] at a1 a3
      set P := (l.piece ∪ r.piece).card with hP
      set m := (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card with hmdef
      have hmP : m ≤ P := card_le_card (pdarts_subset _ _)
      have e1 : sT m + cs m ≤ C * P * lg P := (hsT m).trans
        (Nat.mul_le_mul (Nat.mul_le_mul_left _ hmP) (lg_mono hmP))
      have e2 : 644 * m + 121 * Hs.length ≤ 8 * (C * (P + Hs.length)) := by
        have h1 : 100 * P ≤ C * P := Nat.mul_le_mul_right P hC
        have h2 : 100 * Hs.length ≤ C * Hs.length := Nat.mul_le_mul_right _ hC
        rw [Nat.mul_add C P Hs.length]
        omega
      have es : (cMach C C₀).sep P = C * P * lg P := rfl
      have el : (cMach C C₀).lin (P + Hs.length) = C * (P + Hs.length) := rfl
      rw [es, el]
      simp only [scp, ncF, ADec.piece]
      rw [← hmdef]
      omega)
    τ [] (rotPerm (lpreMap M)) (fun x hx => hx)
  have ha : arunLCost (lpreMap M) (cMach C C₀) τ [] (rotPerm (lpreMap M)) ≤
      runLCost (lpreMap M) (cMach C C₀) τ := by
    unfold runLCost; omega
  have hB : 1000 * asize τ ≤ 1000 * (2 * N + 1) := Nat.mul_le_mul_left 1000 hsz
  refine ⟨hbal.1, c', t, ex, ?_, hout, nlRunO_isMax hM hrot hface hu hST hx₀ hbal hO⟩
  have := ha.trans hcost
  omega


/-- **`mfMain_cMachX` with subroutines depending on the call.** -/
theorem mfMain_cMachXO (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) {NO : MOFam (lpreMap M)} {C C₀ : ℕ} (hC : 100 ≤ C)
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
    OSpecOn (lpreMap M) NO Reach →
    StepPSpecC (lpreMap M) (cflowO (lpreMap M) NO u' S' T') Reach gid u' S' T' Z I W stepP stT rT →
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
        (arunLO (lpreMap M) NO u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) (Hb + 9 + 7 * N) c' ∧
      IsMax M u S T (nlRunO M u S T τ NO) := by
  intro pc sc τ u' S' T' Reach N hsep hO hstep hsT hstT hsR hrT REVb SIGb CAPb KRb en hen hgid hHb
    c₀ hc₀ r0 r1 r2 r3 r4 r5 r6 r7 hrev hsig hcap hkr i1 i2 i3 i4 hW
  obtain ⟨hbal, -, -⟩ := maxflow_plane_cost_decM hM hrot hface hu hST e hsurj d₀
    (cMach_bounds C C₀)
  have hok := callOk_root hM hrot hface hx₀ hbal
  have hW' : Hb + 9 + 7 * N ≤ W := le_trans (Nat.le_add_right _ _) hW
  obtain ⟨c₁, t₁, e₁, ht₁, hw₁, b0, b1, b2, b3, m0, m1, m2, hin, ho₁⟩ :=
    rfProg_root (I := I) (W := W) (Reach := Reach) (gid := gid) (u := u') (S := S') (T := T')
      (Z := Z) τ (rotPerm (lpreMap M)) hbal.1 (calls_self _ _ _) hok hen hgid c₀ hc₀ r0 r1 r2 r3
      r4 r5 r6 r7 hrev hsig hcap hkr i1 i2 i3 i4 hW'
  obtain ⟨hpc, c', t, ex, ht, hout, hmax⟩ := mfDriveFrame_cMachXO hM hrot hface hu hST e hsurj d₀
    hx₀ hC hC₀ hZ hsep hO hstep hsT hstT hsR hrT hHb c₁ hw₁ b0 b1 b2 b3 m0 m1 m2 (by omega) le_rfl
    hW
    hin
  have ht' : t ≤ (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        1000 * (2 * N + 1) + 2 := ht
  exact ⟨hpc, c', t₁ + t, .seq e₁ ex, by omega, hout, hmax⟩

/-- **The whole program with the step around its subroutine programs, the subroutines depending
on the call** (`mfMain_cMachO` relative to `arunLO`): the hypotheses on the six subroutine
programs are `CntPSpec` and the specifications of `MfStepO.lean` for the subroutines `NO`, which
must meet their specifications at the calls of the decomposition (`OSpecOn`); the conclusion is
the flow of `arunLO` in the root frame and `IsMax` of `nlRunO`. -/
theorem mfMain_cMachOC (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) {NO : MOFam (lpreMap M)} {C C₀ : ℕ} (hC : 100 ≤ C)
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
    let c := cMach C C₀
    SepPSpec (lpreMap M) Reach gid u' S' T' Z I W sepP sT sR →
    OSpecOn (lpreMap M) NO Reach →
    CntPSpec (lpreMap M) Reach gid u' S' T' Z I W cntP cnT rO →
    FixPSpecO (lpreMap M) NO Reach gid u' S' T' Z I W fixP fT rO →
    C2SPSpecO (lpreMap M) NO Reach gid u' S' T' Z I W c2sP cT rO →
    S2CPSpecO (lpreMap M) NO Reach gid u' S' T' Z I W s2cP s2T rO →
    RetPSpecO (lpreMap M) NO Reach gid u' S' T' Z I W retP rtT rO →
    FrmPSpecO (lpreMap M) NO Reach gid u' S' T' Z I W frmP fmT rO →
    (∀ m, sT m + cs m ≤ C * m * lg m) →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      cnT (.node l r π, Hs, σ) ≤ cs (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card +
        100 * (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card + 100 * Hs.length + 100) →
    (∀ l r π Hs σ (h : SCond (lpreMap M) l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxO (lpreMap M) NO u' S' T' l r π Hs σ h).L[j]? = some πj →
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
        (arunLO (lpreMap M) NO u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) (Hb + 9 + 7 * N) c' ∧
      IsMax M u S T (nlRunO M u S T τ NO) := by
  intro pc sc τ u' S' T' Reach N c hsep hO hcn hfx hc2 hs2 hrt hfm hsT hcnT hcost hsR hrO
    REVb SIGb CAPb KRb en hen hgid hHb c₀ hc₀ r0 r1 r2 r3 r4 r5 r6 r7 hrev hsig hcap hkr i1 i2 i3
    i4 hW
  have hstep := stepPO_specO hcn hfx hc2 hs2 hrt hfm
  obtain ⟨hbal, -, -⟩ := maxflow_plane_cost_decM hM hrot hface hu hST e hsurj d₀
    (cMach_bounds C C₀)
  have hok := callOk_root hM hrot hface hx₀ hbal
  refine mfMain_cMachXO hM hrot hface hu hST e hsurj d₀ hx₀ hC hC₀ hZ hsep hO hstep hsT
    (fun l r π Hs σ hx => ?_) hsR hrO hen hgid hHb c₀ hc₀ r0 r1 r2 r3 r4 r5 r6 r7 hrev hsig hcap
    hkr i1 i2 i3 i4 hW
  have hcond : SCond (lpreMap M) l r π Hs σ := callOk_cond (callOk_calls τ [] _ _ hok hx)
  have hle := stTO_le (O := planeOracles fun X => frRef X) (u := u') (S := S') (T := T')
    (cnT := cnT) (fT := fT) (cT := cT)
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
