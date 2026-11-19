module

public import PlanarFlow.BKMNW.MfMainX
public import PlanarFlow.BKMNW.DecGuard

/-!
# The whole max-flow program for the guarded decomposition and any choices

`mfDriveFrameX_cMach` / `mfMain_cMachXX` (`MfMainX.lean`) are stated for the decomposition with
the plain split functions `spSR`, `spHR` and Miller's separator `sepM` (numbered by
`Fintype.equivFin`). Two obstructions to discharging their hypothesis `SepPSpecXL sepL` by a
program:

1. the record of a call gives its state only as `∃ st, x.1 = ds.dec … st b` (`PhOk`), and with the
   plain split functions such an `st` need not be a valid rotation (`CInvS`), which every program
   of the split chain needs (`PMap`);
2. `sepM` numbers the darts by `Fintype.equivFin` (chosen, not computable): a program running
   Miller's machine computes `sepC` (`MbSep.lean`), numbered by the enumeration.

Here the decomposition is the **guarded** one (`DecGuard.lean`: the split functions answer only
where the hypotheses of `SplitFnsS` hold, so any state producing a node is valid) and the choices
`pc`, `sc` are arbitrary under their specifications:

* **`maxflow_plane_cost_decG`**: the headline bound (`BalDecA`, `IsMax`, `runLCost`) for the
  guarded decomposition with any `pc`, `sc` meeting `PcChoice.OK` / `ScChoice.OK`;
* **`mfDriveFrameX_cMachG`**, **`mfMain_cMachXG`**: `mfDriveFrameX_cMach` / `mfMain_cMachXX` for
  the guarded decomposition and any such choices, with the separator's cost allowed a term linear
  in the number of holes (`sTL n k + cs m ≤ C n lg n + C k`: the separator writes one flag per
  hole, so `k` cannot be avoided);
* **`mfMain_cMachXGE`**: the instance with the choices of the enumeration (`pcChoiceE`) and the
  separator `sepC M e n (encB' W)` decoded from the machine's run (base `encB' W`, a function of
  the weight bound `W = #P + K nTouch` of the call, so a program can compute it).
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

/-- **Maximum flow in plane graphs in `O(n log³ n)` with the guarded decomposition**:
`maxflow_plane_cost_decDD'` for the guarded split functions (`splitFnsS_guard`). -/
theorem maxflow_plane_cost_decG (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) (pc : PcChoice _ _)
    (hpc : ∀ P Hs, pc.OK (lpreMap M) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMap M)) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W)
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀) :
    let gS := gSz (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMap M) (pendQ _))
    let gH := gHl (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMap M) (pendQ _))
    let τ := decS (lpreMap M) (guardS (lpreMap M) gS (spSR (lpreMap M) pc sc (pendQ _)))
      (guardS (lpreMap M) gH (spHR (lpreMap M) pc sc (pendQ _)))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) ∧
      runLCost (lpreMap M) c τ ≤
        (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) := by
  intro gS gH τ
  have hτ : BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ :=
    decS_balDecA_lpre hM hrot hface (splitFnsS_guard (splitFnsS_lpreR S T pc hpc sc hsc))
  obtain ⟨h1, h2⟩ := maxflow_cost_of hM hrot hface hu hST
    (planeOracles_spec _ fun X => frRef_spec X) hc hτ
  exact ⟨hτ, h1, h2.trans (cost_bound_le K K₀ _)⟩

set_option maxHeartbeats 4000000 in
/-- **The fixed driver program on the extended frames, guarded decomposition, any choices**:
`mfDriveFrameX_cMach` (see the module docstring). -/
theorem mfDriveFrameX_cMachG (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    (pc : PcChoice _ _) (hpc : ∀ P Hs, pc.OK (lpreMap M) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMap M)) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W) {C C₀ : ℕ} (hC : 200 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ} {sepL stepP : Stmt}
    {sTL : ℕ → ℕ → ℕ} {cs : ℕ → ℕ} {sRL : ℕ → ℕ → ℕ → ℕ} {stT rT : MCall (lpreMap M) → ℕ}
    {RS RT : ℕ} (hZ : 2 * Z ≤ W) :
    let gS := gSz (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMap M) (pendQ _))
    let gH := gHl (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMap M) (pendQ _))
    let ds : DSys (lpreMap M) := ⟨guardS (lpreMap M) gS (spSR (lpreMap M) pc sc (pendQ _)),
      guardS (lpreMap M) gH (spHR (lpreMap M) pc sc (pendQ _)),
      chRot (lpreMap M) (pendQ _), 100000, pendQ _, pc.pick⟩
    let τ := decS (lpreMap M) (guardS (lpreMap M) gS (spSR (lpreMap M) pc sc (pendQ _)))
      (guardS (lpreMap M) gH (spHR (lpreMap M) pc sc (pendQ _)))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMap M) τ [] (rotPerm (lpreMap M))
    let N := τ.piece.card
    SepPSpecXL (lpreMap M) ds Reach gid ν u' S' T' Z I W sepL sTL sRL →
    StepPSpec (lpreMap M) (planeOracles fun X => frRef X) Reach gid u' S' T' Z I W stepP stT rT →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMap M).head y ≠ (lpreMap M).tail y) →
    100000 ≤ W →
    (∀ n m k, m ≤ n → sTL n k + cs m ≤ C * n * lg n + C * k) →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      stT (.node l r π, Hs, σ) ≤ runsCharge (lpreMap M) (cMach C C₀) l r π Hs σ +
        cs (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card +
        100 * (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card + 100 * Hs.length + 106) →
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) → (∀ x, Reach x → rT x ≤ RT) →
    0 < Hb → ∀ {eF h : ℕ} (c₀ : Config), WordsBounded W c₀ → c₀.nreg 3000 = 0 →
    c₀.nreg 3001 = 1 → c₀.nreg 3002 = Hb → c₀.nreg 3003 = h → c₀.nmem Hb = 0 →
    c₀.nmem (Hb + 1) = 0 → c₀.nmem (Hb + 2) = eF → Hb + 5 ≤ eF → eF ≤ h →
    h + (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ W →
    FInLX (lpreMap M) ds Reach gid ν u' S' T' Z (τ, [], rotPerm (lpreMap M)) (Hb + 5) eF c₀ →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (driver mtProg mlProg (splitSX (sepPX 100000 sepL)) (nodeSF stepP)) c₀ c' t ∧
      t ≤ (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2 ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunL (lpreMap M) (planeOracles fun X => frRef X) u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) eF c' ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) := by
  intro gS gH ds τ u' S' T' Reach N hsL hstep hpk hν hloop hsW hsT hstT hsR hrT hHb eF h c₀ hc₀
    r0 r1 r2 r3 m0 m1 m2 he hh hroom hin
  have hsep := sepPX_spec (ds := ds) hsL hpk hν hloop hsW
  obtain ⟨hbal, hmax, hcost⟩ := maxflow_plane_cost_decG hM hrot hface hu hST pc hpc sc hsc
    (cMach_bounds C C₀)
  have hcore := ADec.BalA.core hbal.2.2.2.2
  have hsz := asize_le hcore
  have hsize : ∀ x, Reach x → (pdarts (lpreMap M) x.1.piece x.2.1).card ≤ N ∧
      x.2.1.length ≤ N ∧ x.1.piece.card ≤ N := fun x hx => by
    have h1 := calls_size τ [] _ x hcore hx
    have h2 := card_le_card (pdarts_subset (M := lpreMap M) x.1.piece x.2.1)
    simp only [List.length_nil, zero_add] at h1
    exact ⟨by omega, by omega, by omega⟩
  have hR : ∀ x, Reach x → rSpX (lpreMap M) (fun n m k => sRL n m k + smR n m k) x + rT x ≤
      110 * N + 80 + RS + RT := fun x hx => by
    obtain ⟨a1, a2, a3⟩ := hsize x hx
    have := hrT x hx
    rcases x with ⟨τx, Hs, σ⟩
    cases τx with
    | leaf Q => simp only [rSpX]; omega
    | node l r π =>
      have hr1 : r.piece.card ≤ N :=
        (card_le_card (subset_union_right (s₁ := l.piece) (s₂ := r.piece))).trans a3
      have hr2 := card_le_card (pdarts_subset (M := lpreMap M) r.piece
        (childHoles Hs π.path.mverts))
      have := hsR _ _ _ a3 a1 a2
      simp only [rSpX, rszC, chR, smR, ADec.piece] at *
      omega
  have hrm := roomC_le_on (M := lpreMap M) (rL := fun _ => 0)
    (rS := rSpX (lpreMap M) (fun n m k => sRL n m k + smR n m k))
    (rN := rT) Reach (fun _ _ => Nat.zero_le _) hR τ [] (rotPerm (lpreMap M)) (fun x hx => hx)
  have hsz' := Nat.mul_le_mul_right (110 * N + 80 + RS + RT) hsz
  obtain ⟨c', t, ex, ht, hout, -, -⟩ := mfDriveFrameX hsep
    (fun l r π Hs σ hx => calls_child τ [] _ l r π Hs σ hx) hZ (nodeSF_spec (Hb := Hb) hstep)
    hHb τ [] (rotPerm (lpreMap M)) c₀ hc₀ r0 r1 r2 r3 m0 m1 m2 he hh
    ((Nat.add_le_add_left (hrm.trans hsz') h).trans hroom) hin
  have hm := mcost_le_on (M := lpreMap M) (tc := fun _ => 3)
    (lc := fun x => 20 * (pdarts (lpreMap M) x.1.piece x.2.1).card + 17)
    (sc := scpX (lpreMap M) (fun n k => sTL n k + 600 * n + 50 * k + 600)) (nc := ncF (lpreMap M) stT)
    (cMach C C₀) (A := 1) (B := 2000)
    Reach (fun Q Hs σ _ => by
      have := Nat.mul_le_mul_right (pdarts (lpreMap M) Q Hs).card hC₀
      simp only [cMach, ADec.piece]; omega)
    (fun l r π Hs σ hx => by
      have hok := callOk_calls τ [] _ _ hin.2.1 hx
      have hcond := callOk_cond hok
      rw [nodeCharge_eq _ hcond]
      obtain ⟨a1, a2, a3⟩ := hsize _ hx
      have hs := hstT l r π Hs σ hx
      simp only [ADec.piece] at a1 a3
      set P := (l.piece ∪ r.piece).card with hP
      set m := (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card with hmdef
      have hmP : m ≤ P := card_le_card (pdarts_subset _ _)
      have hr1 : r.piece.card ≤ P := card_le_card (subset_union_right (s₁ := l.piece) (s₂ := r.piece))
      have hr2 := card_le_card (pdarts_subset (M := lpreMap M) r.piece (childHoles Hs π.path.mverts))
      have e1 : sTL P Hs.length + cs m ≤ C * P * lg P + C * Hs.length := hsT P m Hs.length hmP
      have e2 : 1335 * P + 171 * Hs.length + C * Hs.length ≤ 8 * (C * (P + Hs.length)) := by
        have h1 : 200 * P ≤ C * P := Nat.mul_le_mul_right P hC
        have h2 : 200 * Hs.length ≤ C * Hs.length := Nat.mul_le_mul_right _ hC
        rw [Nat.mul_add C P Hs.length]
        omega
      have es : (cMach C C₀).sep P = C * P * lg P := rfl
      have el : (cMach C C₀).lin (P + Hs.length) = C * (P + Hs.length) := rfl
      rw [es, el]
      simp only [scpX, ncF, ADec.piece, rszC, chR]
      rw [← hP, ← hmdef]
      omega)
    τ [] (rotPerm (lpreMap M)) (fun x hx => hx)
  have ha : arunLCost (lpreMap M) (cMach C C₀) τ [] (rotPerm (lpreMap M)) ≤
      runLCost (lpreMap M) (cMach C C₀) τ := by
    unfold runLCost; omega
  have hB : 2000 * asize τ ≤ 2000 * (2 * N + 1) := Nat.mul_le_mul_left 2000 hsz
  refine ⟨hbal.1, c', t, ex, ?_, hout, hmax⟩
  have := ha.trans hcost
  omega

set_option maxHeartbeats 4000000 in
/-- **The whole program on the extended frame, guarded decomposition, any choices**:
`mfMain_cMachXX` (see the module docstring). -/
theorem mfMain_cMachXG (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    (pc : PcChoice _ _) (hpc : ∀ P Hs, pc.OK (lpreMap M) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMap M)) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) {C C₀ : ℕ} (hC : 200 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ} {sepL stepP : Stmt}
    {sTL : ℕ → ℕ → ℕ} {cs : ℕ → ℕ} {sRL : ℕ → ℕ → ℕ → ℕ} {stT rT : MCall (lpreMap M) → ℕ}
    {RS RT : ℕ} (hZ : 2 * Z ≤ W) :
    let gS := gSz (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMap M) (pendQ _))
    let gH := gHl (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMap M) (pendQ _))
    let ds : DSys (lpreMap M) := ⟨guardS (lpreMap M) gS (spSR (lpreMap M) pc sc (pendQ _)),
      guardS (lpreMap M) gH (spHR (lpreMap M) pc sc (pendQ _)),
      chRot (lpreMap M) (pendQ _), 100000, pendQ _, pc.pick⟩
    let τ := decS (lpreMap M) (guardS (lpreMap M) gS (spSR (lpreMap M) pc sc (pendQ _)))
      (guardS (lpreMap M) gH (spHR (lpreMap M) pc sc (pendQ _)))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMap M) τ [] (rotPerm (lpreMap M))
    let N := τ.piece.card
    SepPSpecXL (lpreMap M) ds Reach gid ν u' S' T' Z I W sepL sTL sRL →
    StepPSpec (lpreMap M) (planeOracles fun X => frRef X) Reach gid u' S' T' Z I W stepP stT rT →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMap M).head y ≠ (lpreMap M).tail y) →
    100000 ≤ W →
    (∀ n m k, m ≤ n → sTL n k + cs m ≤ C * n * lg n + C * k) →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      stT (.node l r π, Hs, σ) ≤ runsCharge (lpreMap M) (cMach C C₀) l r π Hs σ +
        cs (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card +
        100 * (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card + 100 * Hs.length + 106) →
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) → (∀ x, Reach x → rT x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb VTb RTb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 2 ≤ Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    c₀.nreg 6700 = N → c₀.nreg 6701 = REVb → c₀.nreg 6702 = SIGb → c₀.nreg 6703 = CAPb →
    c₀.nreg 6704 = KRb → c₀.nreg 6705 = ntag τ → c₀.nreg 6706 = Z → c₀.nreg 6707 = Hb →
    c₀.nmem (Hb - 1) = VTb → c₀.nmem (Hb - 1 - 1) = RTb →
    (∀ i < N, c₀.nmem (REVb + i) < N ∧ en (c₀.nmem (REVb + i)) = (lpreMap M).rev (en i)) →
    (∀ i < N, c₀.nmem (SIGb + i) < N ∧
      en (c₀.nmem (SIGb + i)) = rotPerm (lpreMap M) (en i)) →
    (∀ i < N, (c₀.nmem (CAPb + i) : ℤ) = u' (en i) ∧ c₀.nmem (CAPb + i) ≤ Z) →
    (∀ i < N, c₀.nmem (KRb + i) = lrk S' T' (hunion []) ((lpreMap M).tail (en i))) →
    (∀ i < N, c₀.nmem (VTb + i) = ν ((lpreMap M).tail (en i))) →
    (∀ i < N, en i ∈ pdarts (lpreMap M) (core (lpreMap M) (pendQ _) univ) [] →
      c₀.nmem (RTb + i) < N ∧ en (c₀.nmem (RTb + i)) = rootRot (lpreMap M) (pendQ _) (en i)) →
    REVb + N ≤ Hb → SIGb + N ≤ Hb → CAPb + N ≤ Hb → KRb + N ≤ Hb → VTb + N ≤ Hb - 2 →
    RTb + N ≤ Hb - 2 →
    Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N + (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq (.seq rfProg rxProg)
        (driver mtProg mlProg (splitSX (sepPX 100000 sepL)) (nodeSF stepP))) c₀ c' t ∧
      t ≤ 95 * N + 200 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2) ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunL (lpreMap M) (planeOracles fun X => frRef X) u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) (Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N) c' ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) := by
  intro gS gH ds τ u' S' T' Reach N hsL hstep hpk hν hloop hsW hsT hstT hsR hrT REVb SIGb CAPb
    KRb VTb RTb en hen hgid hHb c₀ hc₀ r0 r1 r2 r3 r4 r5 r6 r7 hv hrt hrev hsig hcap hkr hvt hst
    i1 i2 i3 i4 i5 i6 hW
  obtain ⟨hbal, -, -⟩ := maxflow_plane_cost_decG hM hrot hface hu hST pc hpc sc hsc
    (cMach_bounds C C₀)
  have hok := callOk_root hM hrot hface hx₀ hbal
  obtain ⟨c₁, t₁, e₁, ht₁, hw₁, b0, b1, b2, b3, m0, m1, m2, hin, ho₁⟩ :=
    rfxProg_root (I := I) (W := W) (Reach := Reach) (gid := gid) (ν := ν) (u := u') (S := S')
      (T := T') (Z := Z) (ds := ds) (rootRot (lpreMap M) (pendQ _)) (rotPerm (lpreMap M))
      hbal.1 (calls_self _ _ _) hok hen hgid c₀ hc₀ r0 r1 r2 r3 r4 r5 r6 r7 hrev hsig hcap hkr hv
      hrt hvt hst i1 i2 i3 i4 i5 i6 hHb (by clear * - hW; omega)
  obtain ⟨hpc, c', t, ex, ht, hout, hmax⟩ := mfDriveFrameX_cMachG hM hrot hface hu hST pc hpc sc hsc
    hC hC₀ hZ hsL hstep hpk hν hloop hsW hsT hstT hsR hrT (by clear * - hHb; omega) c₁ hw₁ b0 b1
    b2 b3 m0 m1 m2 (by clear * -; omega) le_rfl (by clear * - hW; omega) hin
  have ht' : t ≤ (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * τ.piece.card + 1) + 2 := ht
  exact ⟨hpc, c', t₁ + t, .seq e₁ ex, by clear * - ht₁ ht'; omega, hout, hmax⟩

/-- **The whole program with the choices of the enumeration and the machine's separator**:
`mfMain_cMachXG` for `pc = pcChoiceE … e n d₀` and
`sc Hs A W = scChoiceE … (sepC … e n (encB' W)) e n Hs A W` (Miller's separator decoded from the
deterministic run of `encProg ; msep` at base `encB' W`, numbered by the enumeration `e`; it meets
`SepFnOK` by `sepC_ok`). The only hypothesis on the separator is `SepPSpecXL` for this guarded
decomposition. -/
theorem mfMain_cMachXGE (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) {C C₀ : ℕ} (hC : 200 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ} {sepL stepP : Stmt}
    {sTL : ℕ → ℕ → ℕ} {cs : ℕ → ℕ} {sRL : ℕ → ℕ → ℕ → ℕ} {stT rT : MCall (lpreMap M) → ℕ}
    {RS RT : ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepC (lpreMap M) e n (encB' W)) e n Hs A W
    let gS := gSz (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMap M) (pendQ _))
    let gH := gHl (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMap M) (pendQ _))
    let ds : DSys (lpreMap M) := ⟨guardS (lpreMap M) gS (spSR (lpreMap M) pc sc (pendQ _)),
      guardS (lpreMap M) gH (spHR (lpreMap M) pc sc (pendQ _)),
      chRot (lpreMap M) (pendQ _), 100000, pendQ _, pc.pick⟩
    let τ := decS (lpreMap M) (guardS (lpreMap M) gS (spSR (lpreMap M) pc sc (pendQ _)))
      (guardS (lpreMap M) gH (spHR (lpreMap M) pc sc (pendQ _)))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMap M) τ [] (rotPerm (lpreMap M))
    let N := τ.piece.card
    SepPSpecXL (lpreMap M) ds Reach gid ν u' S' T' Z I W sepL sTL sRL →
    StepPSpec (lpreMap M) (planeOracles fun X => frRef X) Reach gid u' S' T' Z I W stepP stT rT →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMap M).head y ≠ (lpreMap M).tail y) →
    100000 ≤ W →
    (∀ n m k, m ≤ n → sTL n k + cs m ≤ C * n * lg n + C * k) →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      stT (.node l r π, Hs, σ) ≤ runsCharge (lpreMap M) (cMach C C₀) l r π Hs σ +
        cs (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card +
        100 * (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card + 100 * Hs.length + 106) →
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) → (∀ x, Reach x → rT x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb VTb RTb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 2 ≤ Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    c₀.nreg 6700 = N → c₀.nreg 6701 = REVb → c₀.nreg 6702 = SIGb → c₀.nreg 6703 = CAPb →
    c₀.nreg 6704 = KRb → c₀.nreg 6705 = ntag τ → c₀.nreg 6706 = Z → c₀.nreg 6707 = Hb →
    c₀.nmem (Hb - 1) = VTb → c₀.nmem (Hb - 1 - 1) = RTb →
    (∀ i < N, c₀.nmem (REVb + i) < N ∧ en (c₀.nmem (REVb + i)) = (lpreMap M).rev (en i)) →
    (∀ i < N, c₀.nmem (SIGb + i) < N ∧
      en (c₀.nmem (SIGb + i)) = rotPerm (lpreMap M) (en i)) →
    (∀ i < N, (c₀.nmem (CAPb + i) : ℤ) = u' (en i) ∧ c₀.nmem (CAPb + i) ≤ Z) →
    (∀ i < N, c₀.nmem (KRb + i) = lrk S' T' (hunion []) ((lpreMap M).tail (en i))) →
    (∀ i < N, c₀.nmem (VTb + i) = ν ((lpreMap M).tail (en i))) →
    (∀ i < N, en i ∈ pdarts (lpreMap M) (core (lpreMap M) (pendQ _) univ) [] →
      c₀.nmem (RTb + i) < N ∧ en (c₀.nmem (RTb + i)) = rootRot (lpreMap M) (pendQ _) (en i)) →
    REVb + N ≤ Hb → SIGb + N ≤ Hb → CAPb + N ≤ Hb → KRb + N ≤ Hb → VTb + N ≤ Hb - 2 →
    RTb + N ≤ Hb - 2 →
    Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N + (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq (.seq rfProg rxProg)
        (driver mtProg mlProg (splitSX (sepPX 100000 sepL)) (nodeSF stepP))) c₀ c' t ∧
      t ≤ 95 * N + 200 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2) ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunL (lpreMap M) (planeOracles fun X => frRef X) u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) (Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N) c' ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) := by
  intro pc sc
  exact mfMain_cMachXG hM hrot hface hu hST pc (fun P Hs => pcChoiceE_ok hsurj d₀ _ P Hs) sc
    (fun Hs A W => scChoiceE_ok hsurj
      (sepC_ok (preMap_loopless nlMap_loopless nlE_tail) e n (encB' W) Hs) A W) hx₀ hC hC₀ hZ

end Head

end MfDrv

end BKMNW

end PlanarFlow
