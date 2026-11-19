module

public import PlanarFlow.BKMNW.MfStepMain
public import PlanarFlow.BKMNW.RxRoot

/-!
# The whole max-flow program on the extended frame

`mfDriveFrame_cMachX` / `mfMain_cMachX` (`MfStepCost.lean`, `MfStepMain.lean`) restated with the
extended frame (`FInLX`, the decomposition record), the split `splitSX (sepPX 100000 sepL)` and
the root `rfProg ; rxProg`:

* `hdsys` (the decomposition of the headline theorem as a `DSys`);
* **`mfDriveFrameX_cMach`**: from the root's extended frame, the fixed program
  `driver mtProg mlProg (splitSX (sepPX 100000 sepL)) (nodeSF stepP)` computes `arunL` within
  `headline(cMach) + 2000 (2 N + 1) + 2` steps; the separator is **discharged** at every node
  of the small decomposition (`sepPX_spec`), the hypothesis left is `SepPSpecXL` for `sepL` at
  the large pieces of `decS` (more than `100000` darts), and `C ≥ 200`;
* **`mfMain_cMachXX`**: the whole program `rfProg ; rxProg ; driver …` from the index arrays
  (with `VT`, `RT`), same bound plus `95 N + 200`;
* **`mfMain_cMachXX_small`**: when the map has at most `100000` darts after preprocessing
  (`N ≤ 100000`), `sepL = .skip` and the separator hypothesis disappears.
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

set_option maxHeartbeats 4000000 in
/-- **The fixed driver program on the extended frames, on the decomposition of the headline
theorem** (see the module docstring). -/
theorem mfDriveFrameX_cMach (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {C C₀ : ℕ} (hC : 200 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ} {sepL stepP : Stmt}
    {sTL : ℕ → ℕ → ℕ} {cs : ℕ → ℕ} {sRL : ℕ → ℕ → ℕ → ℕ} {stT rT : MCall (lpreMap M) → ℕ}
    {RS RT : ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepM (lpreMap M)) e n Hs A W
    let ds : DSys (lpreMap M) := ⟨spSR (lpreMap M) pc sc (pendQ _), spHR (lpreMap M) pc sc (pendQ _),
      chRot (lpreMap M) (pendQ _), 100000, pendQ _, pc.pick⟩
    let τ := decS (lpreMap M) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
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
    (∀ n m k, m ≤ n → sTL n k + cs m ≤ C * n * lg n) →
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
  intro pc sc ds τ u' S' T' Reach N hsL hstep hpk hν hloop hsW hsT hstT hsR hrT hHb eF h c₀ hc₀
    r0 r1 r2 r3 m0 m1 m2 he hh hroom hin
  have hsep := sepPX_spec (ds := ds) hsL hpk hν hloop hsW
  obtain ⟨hbal, hmax, hcost⟩ := maxflow_plane_cost_decM hM hrot hface hu hST e hsurj d₀
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
      have e1 : sTL P Hs.length + cs m ≤ C * P * lg P := hsT P m Hs.length hmP
      have e2 : 1335 * P + 171 * Hs.length ≤ 8 * (C * (P + Hs.length)) := by
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
/-- **The whole program on the extended frame**:
`(rfProg ; rxProg) ; driver mtProg mlProg (splitSX (sepPX 100000 sepL)) (nodeSF stepP)` from the
index arrays (`REV SIG CAP KR` as for `mfMain_cMachX`, and `VT`, `RT` with their bases at
`Hb - 1`, `Hb - 2`), within `95 N + 200 + headline(cMach) + 2000 (2 N + 1) + 2` steps; the
hypotheses on the separator are `SepPSpecXL sepL` (the large pieces only). -/
theorem mfMain_cMachXX (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) {C C₀ : ℕ} (hC : 200 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ} {sepL stepP : Stmt}
    {sTL : ℕ → ℕ → ℕ} {cs : ℕ → ℕ} {sRL : ℕ → ℕ → ℕ → ℕ} {stT rT : MCall (lpreMap M) → ℕ}
    {RS RT : ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepM (lpreMap M)) e n Hs A W
    let ds : DSys (lpreMap M) := ⟨spSR (lpreMap M) pc sc (pendQ _), spHR (lpreMap M) pc sc (pendQ _),
      chRot (lpreMap M) (pendQ _), 100000, pendQ _, pc.pick⟩
    let τ := decS (lpreMap M) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
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
    (∀ n m k, m ≤ n → sTL n k + cs m ≤ C * n * lg n) →
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
  intro pc sc ds τ u' S' T' Reach N hsL hstep hpk hν hloop hsW hsT hstT hsR hrT REVb SIGb CAPb
    KRb VTb RTb en hen hgid hHb c₀ hc₀ r0 r1 r2 r3 r4 r5 r6 r7 hv hrt hrev hsig hcap hkr hvt hst
    i1 i2 i3 i4 i5 i6 hW
  obtain ⟨hbal, -, -⟩ := maxflow_plane_cost_decM hM hrot hface hu hST e hsurj d₀
    (cMach_bounds C C₀)
  have hok := callOk_root hM hrot hface hx₀ hbal
  obtain ⟨c₁, t₁, e₁, ht₁, hw₁, b0, b1, b2, b3, m0, m1, m2, hin, ho₁⟩ :=
    rfxProg_root (I := I) (W := W) (Reach := Reach) (gid := gid) (ν := ν) (u := u') (S := S')
      (T := T') (Z := Z) (ds := ds) (rootRot (lpreMap M) (pendQ _)) (rotPerm (lpreMap M))
      hbal.1 (calls_self _ _ _) hok hen hgid c₀ hc₀ r0 r1 r2 r3 r4 r5 r6 r7 hrev hsig hcap hkr hv
      hrt hvt hst i1 i2 i3 i4 i5 i6 hHb (by clear * - hW; omega)
  obtain ⟨hpc, c', t, ex, ht, hout, hmax⟩ := mfDriveFrameX_cMach hM hrot hface hu hST e hsurj d₀
    hC hC₀ hZ hsL hstep hpk hν hloop hsW hsT hstT hsR hrT (by clear * - hHb; omega) c₁ hw₁ b0 b1
    b2 b3 m0 m1 m2 (by clear * -; omega) le_rfl (by clear * - hW; omega) hin
  have ht' : t ≤ (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * τ.piece.card + 1) + 2 := ht
  exact ⟨hpc, c', t₁ + t, .seq e₁ ex, by clear * - ht₁ ht'; omega, hout, hmax⟩

set_option maxHeartbeats 4000000 in
/-- **The whole program on the extended frame, with no separator hypothesis, for small maps**:
when the preprocessed map has at most `100000` darts every call of the decomposition is a call of
`smD` and the separator program `sepPX 100000 .skip` is discharged (`sepPX_spec_small`). -/
theorem mfMain_cMachXX_small (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) {C C₀ : ℕ} (hC : 200 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ} {stepP : Stmt}
    {cs : ℕ → ℕ} {stT rT : MCall (lpreMap M) → ℕ} {RT : ℕ} (hZ : 2 * Z ≤ W) :
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
    N ≤ 100000 →
    StepPSpec (lpreMap M) (planeOracles fun X => frRef X) Reach gid u' S' T' Z I W stepP stT rT →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMap M).head y ≠ (lpreMap M).tail y) →
    100000 ≤ W →
    (∀ n m, m ≤ n → cs m ≤ C * n * lg n) →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      stT (.node l r π, Hs, σ) ≤ runsCharge (lpreMap M) (cMach C C₀) l r π Hs σ +
        cs (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card +
        100 * (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card + 100 * Hs.length + 106) →
    (∀ x, Reach x → rT x ≤ RT) →
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
    Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N + (2 * N + 1) * (110 * N + 80 + 0 + RT) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq (.seq rfProg rxProg)
        (driver mtProg mlProg (splitSX (sepPX 100000 .skip)) (nodeSF stepP))) c₀ c' t ∧
      t ≤ 95 * N + 200 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2) ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunL (lpreMap M) (planeOracles fun X => frRef X) u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) (Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N) c' ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) := by
  intro pc sc τ u' S' T' Reach N hN hstep hpk hν hloop hsW hcs hstT hrT
  obtain ⟨hbal, -, -⟩ := maxflow_plane_cost_decM hM hrot hface hu hST e hsurj d₀
    (cMach_bounds C C₀)
  have hcore := ADec.BalA.core hbal.2.2.2.2
  have hsmall : ∀ x, Reach x → x.1.piece.card ≤ 100000 := fun x hx => by
    have h1 := calls_size τ [] _ x hcore hx
    simp only [List.length_nil, zero_add] at h1
    show x.1.piece.card ≤ 100000
    omega
  intro REVb SIGb CAPb KRb VTb RTb en
  exact mfMain_cMachXX hM hrot hface hu hST e hsurj d₀ hx₀ hC hC₀ (sRL := fun _ _ _ => 0)
    (sTL := fun _ _ => 0) (RS := 0) hZ
    (sepPXL_vacuous (ds := ⟨spSR (lpreMap M) pc sc (pendQ _), spHR (lpreMap M) pc sc (pendQ _),
      chRot (lpreMap M) (pendQ _), 100000, pendQ _, pc.pick⟩) hsmall .skip _ _)
    hstep hpk hν hloop hsW (fun n m k hmn => by simpa using hcs n m hmn) hstT
    (fun _ _ _ _ _ _ => le_rfl) hrT

end Head

end MfDrv

end BKMNW

end PlanarFlow
