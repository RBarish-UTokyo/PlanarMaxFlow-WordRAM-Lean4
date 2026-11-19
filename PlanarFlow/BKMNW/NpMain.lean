module

public import PlanarFlow.BKMNW.NpDrv
public import PlanarFlow.BKMNW.MfMainG

/-!
# The whole max-flow program with the node-step subroutine programs plugged in

`mfMain_cMachXGE` (`MfMainG.lean`) asks for one program `stepP` meeting `StepPSpec` relative to
`arunL … (planeOracles frRef)`, which no machine program can meet (the push-backs' classical
choices, `NpPushG.lean`; the step does not get the parts of the separator, `NpCntM.lean`). Here
the node step is **`stepX segP (stepPO cntP fixP c2sP s2cP retP frmP)`** (the parts, the counts
`cntP` of `NpCnt.lean`, FixConservationOnPath, the hole loop, the two push-backs) and the
subroutines are **any family `NF : NFam`** meeting the specifications of Algorithm 1 at the calls
(`NSpecOn`, e.g. `implG` with the explicit push-back `pushFwdL`):

* `rfxProg_memZ` (the root set-up `rfProg ; rxProg` keeps the memory below `Hb`, so `MemZ Wz`);
* **`mfDriveFrameXN_cMachG`** (the driver, guarded decomposition, any choices);
* **`mfMain_cMachXGN`**, **`mfMain_cMachXGEN`**: the whole program
  `(rfProg ; rxProg) ; driver mtProg mlProg (splitSX (sepPX 100000 sepL))
  (nodeSF (stepX segP (stepPO cntP fixP c2sP s2cP retP frmP)))` within
  **`95 N + 200 + ((100000+11)² · 448 · (27 · 102256 + 25) · machK C · n · lg³ n +
  (100000+11)² · 28 · C₀ · n · lg n + 2000 (2 N + 1) + 2)`** steps (`n = #D`) writes the flow of
  `arunLN NF` and `IsMax M u S T (nlRunN M u S T τ NF)`, keeping `MemZ Wz`. The remaining program
  hypotheses: **`SepPSpecXL sepL`** (separator), **`SegPSpec segP`** (the parts at the node),
  **`FixPSpecN`, `C2SPSpecN`, `S2CPSpecN`, `RetPSpecN`, `FrmPSpecN`** (the five subroutine
  programs, relative to `NF`), with their costs in the fields of `cMach C C₀` and, per node
  call, `sTL n k + sgT x ≤ C n lg n + C k` (the split's separator and the parts' rerun share the
  separator budget).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver

universe w

section Root

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The root set-up keeps the memory below `Hb`**: every run of `rfProg ; rxProg` (from the
configuration of `rfxProg_root`) keeps `MemZ Wz` for `Wz < Hb - 2`. -/
theorem rfxProg_memZ {I : Input} {W : ℕ} {m REVb SIGb CAPb KRb VTb RTb Hb tg Z Wz : ℕ}
    (c : Config) (hc : WordsBounded W c) (hz : MemZ Wz c) (hWz : Wz + 2 < Hb)
    (r0 : c.nreg 6700 = m) (r2 : c.nreg 6702 = SIGb) (r5 : c.nreg 6705 = tg)
    (r6 : c.nreg 6706 = Z) (r7 : c.nreg 6707 = Hb)
    (hv : c.nmem (Hb - 1) = VTb) (hr : c.nmem (Hb - 1 - 1) = RTb)
    (i1 : REVb + m ≤ Hb) (i2 : SIGb + m ≤ Hb) (i3 : CAPb + m ≤ Hb) (i4 : KRb + m ≤ Hb)
    (i5 : VTb + m ≤ Hb - 2) (i6 : RTb + m ≤ Hb - 2) (hHb : 2 ≤ Hb)
    (w : Hb + 5 + 4 + 7 * m + 1 + 3 + 7 * m ≤ W) (hr1 : c.nreg 6701 = REVb)
    (hr3 : c.nreg 6703 = CAPb) (hr4 : c.nreg 6704 = KRb) :
    ∀ c' t, Exec I W (.seq rfProg rxProg) c c' t → MemZ Wz c' := by
  intro c' t ex
  cases ex with
  | seq e1 e2 =>
    obtain ⟨c₀, t₀, e₀, -, -, -, -, -, -, g2, -, hN, -, -, -, -, -, -, -, -, -, kb, -, -⟩ :=
      rfProg_exec (P := I) c hc r0 hr1 r2 hr3 hr4 r5 r6 r7 i1 i2 i3 i4 (by clear * - w; omega)
    have hcc := (Exec.det e₀ e1).1
    subst hcc
    obtain ⟨c₂, t₂, e₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, zk, -, -, -, -⟩ :=
      rxProg_exec (I := I) c₀ e₀.wb_right g2 hN hHb
        (by rw [kb _ (by clear * - hHb; omega)]; exact hv)
        (by rw [kb _ (by clear * - hHb; omega)]; exact hr) i5 i6 w
    have hcc2 := (Exec.det e₂ e2).1
    subst hcc2
    exact hz.of_eq fun a ha => by
      rw [zk a (Or.inl (by clear * - ha hWz; omega)), kb a (by clear * - ha hWz; omega)]

end Root

section Head

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

set_option maxHeartbeats 4000000 in
/-- **The fixed driver with the node-step programs, guarded decomposition, any choices**
(`mfDriveFrameX_cMachG` with `stepX segP (stepPO cntP …)` and a family `NF`). -/
theorem mfDriveFrameXN_cMachG (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    (pc : PcChoice _ _) (hpc : ∀ P Hs, pc.OK (lpreMap M) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMap M)) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W)
    {x₀ : D} (hx₀ : x₀ ∈ nlDarts M) {C C₀ : ℕ} (hC : 200 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Wz Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ}
    {sepL segP fixP c2sP s2cP retP frmP : Stmt} {NF : NFam (lpreMap M)}
    {sTL : ℕ → ℕ → ℕ} {sRL : ℕ → ℕ → ℕ → ℕ} {sgT sgR rO : MCall (lpreMap M) → ℕ}
    {fT rtT fmT : MCall (lpreMap M) → ℕ → ℕ} {cT s2T : MCall (lpreMap M) → ℕ → ℕ → ℕ}
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
    let c := cMach C C₀
    SepPSpecXL (lpreMap M) ds Reach gid ν u' S' T' Z I W sepL sTL sRL →
    SegPSpec (lpreMap M) ds Reach gid ν u' S' T' Z I W segP sgT sgR →
    NSpecOn (lpreMap M) NF Reach →
    FixPSpecN (lpreMap M) NF Reach gid u' S' T' Z I W Wz fixP fT rO →
    C2SPSpecN (lpreMap M) NF Reach gid u' S' T' Z I W Wz c2sP cT rO →
    S2CPSpecN (lpreMap M) NF Reach gid u' S' T' Z I W Wz s2cP s2T rO →
    RetPSpecN (lpreMap M) NF Reach gid u' S' T' Z I W Wz retP rtT rO →
    FrmPSpecN (lpreMap M) NF Reach gid u' S' T' Z I W Wz frmP fmT rO →
    (∀ x : MCall (lpreMap M), x.2.1.length + 1 ≤ rO x) →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMap M).head y ≠ (lpreMap M).tail y) →
    100000 ≤ W →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      sTL (l.piece ∪ r.piece).card Hs.length + sgT (.node l r π, Hs, σ) ≤
        C * (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card + C * Hs.length) →
    (∀ l r π Hs σ (h : SCond (lpreMap M) l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN (lpreMap M) NF u' S' T' l r π Hs σ h).L[j]? = some πj →
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
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) → (∀ x, Reach x → sgR x + rO x ≤ RT) →
    0 < Hb → Wz < Hb → ∀ {eF h : ℕ} (c₀ : Config), WordsBounded W c₀ → MemZ Wz c₀ →
    c₀.nreg 3000 = 0 →
    c₀.nreg 3001 = 1 → c₀.nreg 3002 = Hb → c₀.nreg 3003 = h → c₀.nmem Hb = 0 →
    c₀.nmem (Hb + 1) = 0 → c₀.nmem (Hb + 2) = eF → Hb + 5 ≤ eF → eF ≤ h →
    h + (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ W →
    FInLX (lpreMap M) ds Reach gid ν u' S' T' Z (τ, [], rotPerm (lpreMap M)) (Hb + 5) eF c₀ →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (driver mtProg mlProg (splitSX (sepPX 100000 sepL))
        (nodeSF (stepX segP (stepPO cntP fixP c2sP s2cP retP frmP)))) c₀ c' t ∧
      t ≤ (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2 ∧ MemZ Wz c' ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunLN (lpreMap M) NF u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) eF c' ∧
      IsMax M u S T (nlRunN M u S T τ NF) := by
  intro gS gH ds τ u' S' T' Reach N c hsL hseg hO hfx hc2 hs2 hrt hfm hrO hpk hν hloop hsW hsT
    hcost' hsR hrT hHb hWz eF h c₀ hc₀ hz r0 r1 r2 r3 m0 m1 m2 he hh hroom hin
  have hsep := sepPX_spec (ds := ds) hsL hpk hν hloop hsW
  obtain ⟨hbal, -, hcost⟩ := maxflow_plane_cost_decG hM hrot hface hu hST pc hpc sc hsc
    (cMach_bounds C C₀)
  have hcore := ADec.BalA.core hbal.2.2.2.2
  have hsz := asize_le hcore
  have hsize : ∀ x, Reach x → (pdarts (lpreMap M) x.1.piece x.2.1).card ≤ N ∧
      x.2.1.length ≤ N ∧ x.1.piece.card ≤ N := fun x hx => by
    have h1 := calls_size τ [] _ x hcore hx
    have h2 := card_le_card (pdarts_subset (M := lpreMap M) x.1.piece x.2.1)
    simp only [List.length_nil, zero_add] at h1
    exact ⟨by omega, by omega, by omega⟩
  have hmax : IsMax M u S T (nlRunN M u S T τ NF) := nlRunN_isMax hM hrot hface hu hST hx₀ hbal hO
  have hok₀ := callOk_root hM hrot hface hx₀ hbal
  -- the steps of the node step
  have hstT : ∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      (fun x => sgT x + stTO (lpreMap M) (cntT (lpreMap M)) fT cT s2T rtT fmT x + 1)
        (.node l r π, Hs, σ) ≤ runsCharge (lpreMap M) (cMach C C₀) l r π Hs σ +
        sgT (.node l r π, Hs, σ) +
        100 * (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card + 100 * Hs.length + 106 := by
    intro l r π Hs σ hx
    have hcond : SCond (lpreMap M) l r π Hs σ := callOk_cond (callOk_calls τ [] _ _ hok₀ hx)
    have hle := stTO_le (O := planeOracles fun X => frRef X) (u := u') (S := S') (T := T')
      (cnT := cntT (lpreMap M)) (fT := fT) (cT := cT)
      (sT := s2T) (rtT := rtT) (fmT := fmT) (cMach C C₀) hcond
      (fun hn => by
        have h1 : (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card ≤
            psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs) := by
          unfold psize; omega
        have h2 : 100 * 1 ≤ C * psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs) :=
          Nat.mul_le_mul (by omega) (by omega)
        show 8 ≤ C * _
        omega)
      (fun j πj hj => (hcost' l r π Hs σ hcond j πj hx hj).1)
      (fun j πj i hj => (hcost' l r π Hs σ hcond j πj hx hj).2.1 i)
      (fun j πj i hj => (hcost' l r π Hs σ hcond j πj hx hj).2.2.1 i)
      (fun j πj hj => (hcost' l r π Hs σ hcond j πj hx hj).2.2.2.1)
      (fun j πj hj => (hcost' l r π Hs σ hcond j πj hx hj).2.2.2.2)
    have h2 : cntT (lpreMap M) (.node l r π, Hs, σ) =
        7 * (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card + 11 * Hs.length + 40 := rfl
    simp only
    omega
  have hR : ∀ x, Reach x → rSpX (lpreMap M) (fun n m k => sRL n m k + smR n m k) x +
      (fun x => sgR x + rO x) x ≤
      110 * N + 80 + RS + RT := fun x hx => by
    obtain ⟨a1, a2, a3⟩ := hsize x hx
    have := hrT x hx
    simp only
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
    (rN := fun x => sgR x + rO x) Reach (fun _ _ => Nat.zero_le _) hR τ [] (rotPerm (lpreMap M)) (fun x hx => hx)
  have hsz' := Nat.mul_le_mul_right (110 * N + 80 + RS + RT) hsz
  obtain ⟨c', t, ex, ht, hz', hout, -, -⟩ := mfDriveFrameXN_step hsep
    (fun l r π Hs σ hx => calls_child τ [] _ l r π Hs σ hx) hZ hWz hseg hrO hfx hc2 hs2 hrt hfm
    hHb τ [] (rotPerm (lpreMap M)) c₀ hc₀ hz r0 r1 r2 r3 m0 m1 m2 he hh
    ((Nat.add_le_add_left (hrm.trans hsz') h).trans hroom) hin
  have hm := mcost_le_on (M := lpreMap M) (tc := fun _ => 3)
    (lc := fun x => 20 * (pdarts (lpreMap M) x.1.piece x.2.1).card + 17)
    (sc := scpX (lpreMap M) (fun n k => sTL n k + 600 * n + 50 * k + 600)) (nc := ncF (lpreMap M)
      (fun x => sgT x + stTO (lpreMap M) (cntT (lpreMap M)) fT cT s2T rtT fmT x + 1))
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
      simp only at hs
      simp only [ADec.piece] at a1 a3
      set P := (l.piece ∪ r.piece).card with hP
      set m := (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card with hmdef
      have hmP : m ≤ P := card_le_card (pdarts_subset _ _)
      have hr1 : r.piece.card ≤ P := card_le_card (subset_union_right (s₁ := l.piece) (s₂ := r.piece))
      have hr2 := card_le_card (pdarts_subset (M := lpreMap M) r.piece (childHoles Hs π.path.mverts))
      have e1 : sTL P Hs.length + sgT (.node l r π, Hs, σ) ≤ C * P * lg P + C * Hs.length :=
        hsT l r π Hs σ hx
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
  refine ⟨hbal.1, c', t, ex, ?_, hz', hout, hmax⟩
  have := ha.trans hcost
  omega


set_option maxHeartbeats 4000000 in
/-- **The whole program on the extended frame for any family of node subroutines**
(`mfMain_cMachXG` with the node step `stepX segP (stepPO cntP fixP c2sP s2cP retP frmP)`, the
zero memory below `Wz` and the family `NF` meeting its specifications at the calls). The same
bound `95 N + 200 + headline(cMach C C₀) + 2000 (2 N + 1) + 2`. Program hypotheses: the
separator (`SepPSpecXL`), the parts (`SegPSpec`), the five subroutines (`…PSpecN`); `cntP` is
discharged. -/
theorem mfMain_cMachXGN (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    (pc : PcChoice _ _) (hpc : ∀ P Hs, pc.OK (lpreMap M) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMap M)) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W)
    {x₀ : D} (hx₀ : x₀ ∈ nlDarts M)
    {C C₀ : ℕ} (hC : 200 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Wz Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ}
    {sepL segP fixP c2sP s2cP retP frmP : Stmt} {NF : NFam (lpreMap M)}
    {sTL : ℕ → ℕ → ℕ} {sRL : ℕ → ℕ → ℕ → ℕ} {sgT sgR rO : MCall (lpreMap M) → ℕ}
    {fT rtT fmT : MCall (lpreMap M) → ℕ → ℕ} {cT s2T : MCall (lpreMap M) → ℕ → ℕ → ℕ}
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
    let c := cMach C C₀
    SepPSpecXL (lpreMap M) ds Reach gid ν u' S' T' Z I W sepL sTL sRL →
    SegPSpec (lpreMap M) ds Reach gid ν u' S' T' Z I W segP sgT sgR →
    NSpecOn (lpreMap M) NF Reach →
    FixPSpecN (lpreMap M) NF Reach gid u' S' T' Z I W Wz fixP fT rO →
    C2SPSpecN (lpreMap M) NF Reach gid u' S' T' Z I W Wz c2sP cT rO →
    S2CPSpecN (lpreMap M) NF Reach gid u' S' T' Z I W Wz s2cP s2T rO →
    RetPSpecN (lpreMap M) NF Reach gid u' S' T' Z I W Wz retP rtT rO →
    FrmPSpecN (lpreMap M) NF Reach gid u' S' T' Z I W Wz frmP fmT rO →
    (∀ x : MCall (lpreMap M), x.2.1.length + 1 ≤ rO x) →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMap M).head y ≠ (lpreMap M).tail y) →
    100000 ≤ W →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      sTL (l.piece ∪ r.piece).card Hs.length + sgT (.node l r π, Hs, σ) ≤
        C * (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card + C * Hs.length) →
    (∀ l r π Hs σ (h : SCond (lpreMap M) l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN (lpreMap M) NF u' S' T' l r π Hs σ h).L[j]? = some πj →
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
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) → (∀ x, Reach x → sgR x + rO x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb VTb RTb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 2 ≤ Hb → Wz + 2 < Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    MemZ Wz c₀ →
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
    ∃ c' t, Exec I W (.seq (.seq rfProg rxProg) (driver mtProg mlProg
        (splitSX (sepPX 100000 sepL))
        (nodeSF (stepX segP (stepPO cntP fixP c2sP s2cP retP frmP))))) c₀ c' t ∧
      t ≤ 95 * N + 200 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2) ∧ MemZ Wz c' ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunLN (lpreMap M) NF u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) (Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N) c' ∧
      IsMax M u S T (nlRunN M u S T τ NF) := by
  intro gS gH ds τ u' S' T' Reach N c hsL hseg hO hfx hc2 hs2 hrt hfm hrO hpk hν hloop hsW hsT
    hcost' hsR hrT REVb SIGb CAPb KRb VTb RTb en hen hgid hHb hWz c₀ hc₀ hz r0 r1 r2 r3 r4 r5
    r6 r7 hv hrt' hrev hsig hcap hkr hvt hst i1 i2 i3 i4 i5 i6 hW
  obtain ⟨hbal, -, -⟩ := maxflow_plane_cost_decG hM hrot hface hu hST pc hpc sc hsc
    (cMach_bounds C C₀)
  have hok := callOk_root hM hrot hface hx₀ hbal
  obtain ⟨c₁, t₁, e₁, ht₁, hw₁, b0, b1, b2, b3, m0, m1, m2, hin, ho₁⟩ :=
    rfxProg_root (I := I) (W := W) (Reach := Reach) (gid := gid) (ν := ν) (u := u') (S := S')
      (T := T') (Z := Z) (ds := ds) (rootRot (lpreMap M) (pendQ _)) (rotPerm (lpreMap M))
      hbal.1 (calls_self _ _ _) hok hen hgid c₀ hc₀ r0 r1 r2 r3 r4 r5 r6 r7 hrev hsig hcap hkr hv
      hrt' hvt hst i1 i2 i3 i4 i5 i6 hHb (by clear * - hW; omega)
  have hz₁ : MemZ Wz c₁ := rfxProg_memZ (I := I) (W := W) c₀ hc₀ hz (by clear * - hWz; omega)
    r0 r2 r5 r6 r7 hv hrt' i1 i2 i3 i4 i5 i6 hHb (by clear * - hW; omega) r1 r3 r4 c₁ t₁ e₁
  obtain ⟨hpc, c', t, ex, ht, hz', hout, hmax⟩ := mfDriveFrameXN_cMachG hM hrot hface hu hST pc hpc
    sc hsc hx₀ hC hC₀ hZ hsL hseg hO hfx hc2 hs2 hrt hfm hrO hpk hν hloop hsW hsT hcost' hsR
    hrT (by clear * - hHb; omega) (by clear * - hWz; omega) c₁ hw₁ hz₁ b0 b1 b2 b3 m0 m1 m2
    (by clear * -; omega) le_rfl (by clear * - hW; omega) hin
  have ht' : t ≤ (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * τ.piece.card + 1) + 2 := ht
  exact ⟨hpc, c', t₁ + t, .seq e₁ ex, by clear * - ht₁ ht'; omega, hz', hout, hmax⟩

/-- **The whole program with the choices of the enumeration and the machine's separator, for any
family of node subroutines** (`mfMain_cMachXGE` with the node step
`stepX segP (stepPO cntP fixP c2sP s2cP retP frmP)`): `mfMain_cMachXGN` for
`pc = pcChoiceE … e n d₀` and Miller's separator `sepC … e n (encB' W)`. -/
theorem mfMain_cMachXGEN (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M)
    {C C₀ : ℕ} (hC : 200 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Wz Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ}
    {sepL segP fixP c2sP s2cP retP frmP : Stmt} {NF : NFam (lpreMap M)}
    {sTL : ℕ → ℕ → ℕ} {sRL : ℕ → ℕ → ℕ → ℕ} {sgT sgR rO : MCall (lpreMap M) → ℕ}
    {fT rtT fmT : MCall (lpreMap M) → ℕ → ℕ} {cT s2T : MCall (lpreMap M) → ℕ → ℕ → ℕ}
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
    let c := cMach C C₀
    SepPSpecXL (lpreMap M) ds Reach gid ν u' S' T' Z I W sepL sTL sRL →
    SegPSpec (lpreMap M) ds Reach gid ν u' S' T' Z I W segP sgT sgR →
    NSpecOn (lpreMap M) NF Reach →
    FixPSpecN (lpreMap M) NF Reach gid u' S' T' Z I W Wz fixP fT rO →
    C2SPSpecN (lpreMap M) NF Reach gid u' S' T' Z I W Wz c2sP cT rO →
    S2CPSpecN (lpreMap M) NF Reach gid u' S' T' Z I W Wz s2cP s2T rO →
    RetPSpecN (lpreMap M) NF Reach gid u' S' T' Z I W Wz retP rtT rO →
    FrmPSpecN (lpreMap M) NF Reach gid u' S' T' Z I W Wz frmP fmT rO →
    (∀ x : MCall (lpreMap M), x.2.1.length + 1 ≤ rO x) →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMap M).head y ≠ (lpreMap M).tail y) →
    100000 ≤ W →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      sTL (l.piece ∪ r.piece).card Hs.length + sgT (.node l r π, Hs, σ) ≤
        C * (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card + C * Hs.length) →
    (∀ l r π Hs σ (h : SCond (lpreMap M) l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN (lpreMap M) NF u' S' T' l r π Hs σ h).L[j]? = some πj →
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
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) → (∀ x, Reach x → sgR x + rO x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb VTb RTb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 2 ≤ Hb → Wz + 2 < Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    MemZ Wz c₀ →
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
    ∃ c' t, Exec I W (.seq (.seq rfProg rxProg) (driver mtProg mlProg
        (splitSX (sepPX 100000 sepL))
        (nodeSF (stepX segP (stepPO cntP fixP c2sP s2cP retP frmP))))) c₀ c' t ∧
      t ≤ 95 * N + 200 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2) ∧ MemZ Wz c' ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunLN (lpreMap M) NF u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) (Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N) c' ∧
      IsMax M u S T (nlRunN M u S T τ NF) := by
  intro pc sc
  exact mfMain_cMachXGN hM hrot hface hu hST pc (fun P Hs => pcChoiceE_ok hsurj d₀ _ P Hs) sc
    (fun Hs A W => scChoiceE_ok hsurj
      (sepC_ok (preMap_loopless nlMap_loopless nlE_tail) e n (encB' W) Hs) A W) hx₀ hC hC₀ hZ

end Head

end MfDrv

end BKMNW

end PlanarFlow
