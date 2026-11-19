module

public import PlanarFlow.BKMNW.ThStep
public import PlanarFlow.BKMNW.PqChain

/-!
# The primed chain on the preprocessed map with explicit pendant darts

`PqChain.lean` (the chain for `lpreMapX M ep hep`) restated with the primed node-step
specifications, mechanically, by the same transformation as for `CsGen.lean` followed by the one of
`PqChain.lean`: `SegPSpec'`, `FixPSpecN'`, `C2SPSpecNA`, `S2CPSpecNA`,
`RetPSpecN'`, `FrmPSpecN'`, the hypothesis `(∀ m, m ≤ N → wzc m Z ≤ Wz)` after the `FrmPSpecN'`
one, `SepPSpecXS' sepX` and `segP' sepX` from `mfMain_XGEFGenX''` on. Same bounds.

* **`mfDriveFrameXN_GenX''`**, **`mfMain_XGNGenX''`**, **`mfMain_XGENGenX''`**,
  **`mfMain_XGEFGenX''`**, **`mfMain_XGEPGenX''`**, **`mfMain_cMachSGEPX''`** (within
  `95 N + 200 + ((100000+11)² · 448 · (27 · 102256 + 25) · machKS C · n · lg³ n +
  (100000+11)² · 28 · C₀ · n · lg n + 2000 (2 N + 1) + 2)` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver MfDrv NcStep

universe w

section Head

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

set_option maxHeartbeats 4000000 in
/-- **The fixed driver with the node-step programs, guarded decomposition, any choices, for any
cost family `c` with `c.Bounds K K₀` and the lower bound `hlin`** (`mfDriveFrameXN_cMachG` with
`cMach C C₀` replaced by `c`): within `headline(K, K₀) + 2000 (2 N + 1) + 2` steps. -/
theorem mfDriveFrameXN_GenX'' (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (ep : PVert M → TDart M) (hep : ∀ w, (tnlMap M).tail (ep w) = w)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    (pc : PcChoice _ _) (hpc : ∀ P Hs, pc.OK (lpreMapX M ep hep) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMapX M ep hep)) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W)
    {x₀ : D} (hx₀ : x₀ ∈ nlDarts M) {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    (hlin : ∀ a b, 200 * a + c.lin b ≤ c.lin (a + b)) {I : Input} {W Hb Wz Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ}
    {sepL segP fixP c2sP s2cP retP frmP : Stmt} {NF : NFam (lpreMapX M ep hep)}
    {sTL : ℕ → ℕ → ℕ} {sRL : ℕ → ℕ → ℕ → ℕ} {sgT sgR rO : MCall (lpreMapX M ep hep) → ℕ}
    {fT rtT fmT : MCall (lpreMapX M ep hep) → ℕ → ℕ} {cT s2T : MCall (lpreMapX M ep hep) → ℕ → ℕ → ℕ}
    {RS RT : ℕ} {wzc : ℕ → ℕ → ℕ} (hZ : 2 * Z ≤ W) :
    let gS := gSz (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMapX M ep hep) (pendQ _))
    let gH := gHl (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMapX M ep hep) (pendQ _))
    let ds : DSys (lpreMapX M ep hep) := ⟨guardS (lpreMapX M ep hep) gS (spSR (lpreMapX M ep hep) pc sc (pendQ _)),
      guardS (lpreMapX M ep hep) gH (spHR (lpreMapX M ep hep) pc sc (pendQ _)),
      chRot (lpreMapX M ep hep) (pendQ _), 100000, pendQ _, pc.pick⟩
    let τ := decS (lpreMapX M ep hep) (guardS (lpreMapX M ep hep) gS (spSR (lpreMapX M ep hep) pc sc (pendQ _)))
      (guardS (lpreMapX M ep hep) gH (spHR (lpreMapX M ep hep) pc sc (pendQ _)))
      (smD (lpreMapX M ep hep) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMapX M ep hep) (pendQ _)) 100000 univ [] (rootRot (lpreMapX M ep hep) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMapX M ep hep) τ [] (rotPerm (lpreMapX M ep hep))
    let N := τ.piece.card
    SepPSpecXL (lpreMapX M ep hep) ds Reach gid ν u' S' T' Z I W sepL sTL sRL →
    SegPSpec' (lpreMapX M ep hep) ds Reach gid ν u' S' T' Z I W segP sgT sgR →
    NSpecOn (lpreMapX M ep hep) NF Reach →
    FixPSpecN' (lpreMapX M ep hep) NF Reach gid u' S' T' Z I W Wz wzc fixP fT rO →
    C2SPSpecNA (lpreMapX M ep hep) NF Reach gid u' S' T' Z I W Wz wzc c2sP cT rO →
    S2CPSpecNA (lpreMapX M ep hep) NF Reach gid u' S' T' Z I W Wz wzc s2cP s2T rO →
    RetPSpecN' (lpreMapX M ep hep) NF Reach gid u' S' T' Z I W Wz wzc retP rtT rO →
    FrmPSpecN' (lpreMapX M ep hep) NF Reach gid u' S' T' Z I W Wz wzc frmP fmT rO →
    (∀ m, m ≤ N → wzc m Z ≤ Wz) →
    (∀ x : MCall (lpreMapX M ep hep), x.2.1.length + 1 ≤ rO x) →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMapX M ep hep).head y ≠ (lpreMapX M ep hep).tail y) →
    100000 ≤ W →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      sTL (l.piece ∪ r.piece).card Hs.length + sgT (.node l r π, Hs, σ) ≤
        c.sep (l.piece ∪ r.piece).card + c.lin Hs.length) →
    (∀ l r π Hs σ (h : SCond (lpreMapX M ep hep) l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN (lpreMapX M ep hep) NF u' S' T' l r π Hs σ h).L[j]? = some πj →
      fT (.node l r π, Hs, σ) j ≤ c.fixRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
        πj.faces.card πj.k (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) ∧
      (∀ i, cT (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      (∀ i, s2T (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      rtT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) ∧
      fmT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))) →
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) → (∀ x, Reach x → sgR x + rO x ≤ RT) →
    0 < Hb → Wz < Hb → ∀ {eF h : ℕ} (c₀ : Config), WordsBounded W c₀ → MemZ Wz c₀ →
    c₀.nreg 3000 = 0 →
    c₀.nreg 3001 = 1 → c₀.nreg 3002 = Hb → c₀.nreg 3003 = h → c₀.nmem Hb = 0 →
    c₀.nmem (Hb + 1) = 0 → c₀.nmem (Hb + 2) = eF → Hb + 5 ≤ eF → eF ≤ h →
    h + (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ W →
    FInLX (lpreMapX M ep hep) ds Reach gid ν u' S' T' Z (τ, [], rotPerm (lpreMapX M ep hep)) (Hb + 5) eF c₀ →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (driver mtProg mlProg (splitSX (sepPX 100000 sepL))
        (nodeSF (stepX segP (stepPO cntP fixP c2sP s2cP retP frmP)))) c₀ c' t ∧
      t ≤ (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2 ∧ MemZ Wz c' ∧
      FOutL (lpreMapX M ep hep) gid u' S' T' Z (τ, [], rotPerm (lpreMapX M ep hep))
        (arunLN (lpreMapX M ep hep) NF u' S' T' τ [] (rotPerm (lpreMapX M ep hep)))
        (Hb + 5) eF c' ∧
      IsMax M u S T (nlRunNX M ep hep u S T τ NF) := by
  intro gS gH ds τ u' S' T' Reach N hsL hseg hO hfx hc2 hs2 hrt hfm hwzN hrO hpk hν hloop hsW hsT
    hcost' hsR hrT hHb hWz eF h c₀ hc₀ hz r0 r1 r2 r3 m0 m1 m2 he hh hroom hin
  have hsep := sepPX_spec (ds := ds) hsL hpk hν hloop hsW
  obtain ⟨hbal, -, hcost⟩ := maxflow_plane_cost_decGX hM hrot hface hx₀ ep hep hu hST pc hpc sc hsc
    hc
  have hcore := ADec.BalA.core hbal.2.2.2.2
  have hsz := asize_le hcore
  have hsize : ∀ x, Reach x → (pdarts (lpreMapX M ep hep) x.1.piece x.2.1).card ≤ N ∧
      x.2.1.length ≤ N ∧ x.1.piece.card ≤ N := fun x hx => by
    have h1 := calls_size τ [] _ x hcore hx
    have h2 := card_le_card (pdarts_subset (M := lpreMapX M ep hep) x.1.piece x.2.1)
    simp only [List.length_nil, zero_add] at h1
    exact ⟨by omega, by omega, by omega⟩
  have hmax : IsMax M u S T (nlRunNX M ep hep u S T τ NF) := nlRunNX_isMax hM hrot hface hu hST hx₀ ep hep hbal hO
  have hok₀ := callOk_rootX hM hrot hface hx₀ ep hep hbal
  -- the steps of the node step
  have hstT : ∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      (fun x => sgT x + stTO (lpreMapX M ep hep) (cntT (lpreMapX M ep hep)) fT cT s2T rtT fmT x + 1)
        (.node l r π, Hs, σ) ≤ runsCharge (lpreMapX M ep hep) c l r π Hs σ +
        sgT (.node l r π, Hs, σ) +
        100 * (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card + 100 * Hs.length + 106 := by
    intro l r π Hs σ hx
    have hcond : SCond (lpreMapX M ep hep) l r π Hs σ := callOk_cond (callOk_calls τ [] _ _ hok₀ hx)
    have hle := stTO_le (O := planeOracles fun X => frRef X) (u := u') (S := S') (T := T')
      (cnT := cntT (lpreMapX M ep hep)) (fT := fT) (cT := cT)
      (sT := s2T) (rtT := rtT) (fmT := fmT) c hcond
      (fun hn => by
        have h1 : (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card ≤
            psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs) := by
          unfold psize; omega
        have h2 := lin_ge_of hlin (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
        omega)
      (fun j πj hj => (hcost' l r π Hs σ hcond j πj hx hj).1)
      (fun j πj i hj => (hcost' l r π Hs σ hcond j πj hx hj).2.1 i)
      (fun j πj i hj => (hcost' l r π Hs σ hcond j πj hx hj).2.2.1 i)
      (fun j πj hj => (hcost' l r π Hs σ hcond j πj hx hj).2.2.2.1)
      (fun j πj hj => (hcost' l r π Hs σ hcond j πj hx hj).2.2.2.2)
    have h2 : cntT (lpreMapX M ep hep) (.node l r π, Hs, σ) =
        7 * (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card + 11 * Hs.length + 40 := rfl
    simp only
    omega
  have hR : ∀ x, Reach x → rSpX (lpreMapX M ep hep) (fun n m k => sRL n m k + smR n m k) x +
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
      have hr2 := card_le_card (pdarts_subset (M := lpreMapX M ep hep) r.piece
        (childHoles Hs π.path.mverts))
      have := hsR _ _ _ a3 a1 a2
      simp only [rSpX, rszC, chR, smR, ADec.piece] at *
      omega
  have hrm := roomC_le_on (M := lpreMapX M ep hep) (rL := fun _ => 0)
    (rS := rSpX (lpreMapX M ep hep) (fun n m k => sRL n m k + smR n m k))
    (rN := fun x => sgR x + rO x) Reach (fun _ _ => Nat.zero_le _) hR τ [] (rotPerm (lpreMapX M ep hep)) (fun x hx => hx)
  have hsz' := Nat.mul_le_mul_right (110 * N + 80 + RS + RT) hsz
  obtain ⟨c', t, ex, ht, hz', hout, -, -⟩ := mfDriveFrameXN_step'' hsep
    (fun l r π Hs σ hx => calls_child τ [] _ l r π Hs σ hx) hZ hWz hseg hrO hfx hc2 hs2 hrt hfm
    (fun m hm => hwzN m (by
      have h1 : τ.piece = univ := hbal.1
      simp only [N, h1, card_univ]; exact hm))
    hHb τ [] (rotPerm (lpreMapX M ep hep)) c₀ hc₀ hz r0 r1 r2 r3 m0 m1 m2 he hh
    ((Nat.add_le_add_left (hrm.trans hsz') h).trans hroom) hin
  have hm := mcost_le_on (M := lpreMapX M ep hep) (tc := fun _ => 3)
    (lc := fun x => 20 * (pdarts (lpreMapX M ep hep) x.1.piece x.2.1).card + 17)
    (sc := scpX (lpreMapX M ep hep) (fun n k => sTL n k + 600 * n + 50 * k + 600)) (nc := ncF (lpreMapX M ep hep)
      (fun x => sgT x + stTO (lpreMapX M ep hep) (cntT (lpreMapX M ep hep)) fT cT s2T rtT fmT x + 1))
    c (A := 1) (B := 2000)
    Reach (fun Q Hs σ _ => by
      have h1 := card_le_card (pdarts_subset (M := lpreMapX M ep hep) Q Hs)
      have h2 := lin_ge_of hlin (Q.card + Hs.length)
      simp only [ADec.piece]; omega)
    (fun l r π Hs σ hx => by
      have hok := callOk_calls τ [] _ _ hin.2.1 hx
      have hcond := callOk_cond hok
      rw [nodeCharge_eq _ hcond]
      obtain ⟨a1, a2, a3⟩ := hsize _ hx
      have hs := hstT l r π Hs σ hx
      simp only at hs
      simp only [ADec.piece] at a1 a3
      set P := (l.piece ∪ r.piece).card with hP
      set m := (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card with hmdef
      have hmP : m ≤ P := card_le_card (pdarts_subset _ _)
      have hr1 : r.piece.card ≤ P := card_le_card (subset_union_right (s₁ := l.piece) (s₂ := r.piece))
      have hr2 := card_le_card (pdarts_subset (M := lpreMapX M ep hep) r.piece (childHoles Hs π.path.mverts))
      have e1 : sTL P Hs.length + sgT (.node l r π, Hs, σ) ≤ c.sep P + c.lin Hs.length :=
        hsT l r π Hs σ hx
      have e2 : 1335 * P + 171 * Hs.length + c.lin Hs.length ≤ 8 * c.lin (P + Hs.length) := by
        have h1 := hlin P Hs.length
        have h2 := lin_ge_of hlin (P + Hs.length)
        omega
      simp only [scpX, ncF, ADec.piece, rszC, chR]
      rw [← hP, ← hmdef]
      omega)
    τ [] (rotPerm (lpreMapX M ep hep)) (fun x hx => hx)
  have ha : arunLCost (lpreMapX M ep hep) c τ [] (rotPerm (lpreMapX M ep hep)) ≤
      runLCost (lpreMapX M ep hep) c τ := by
    unfold runLCost; omega
  have hB : 2000 * asize τ ≤ 2000 * (2 * N + 1) := Nat.mul_le_mul_left 2000 hsz
  refine ⟨hbal.1, c', t, ex, ?_, hz', hout, hmax⟩
  have := ha.trans hcost
  omega


set_option maxHeartbeats 4000000 in
/-- **The whole program on the extended frame for any family of node subroutines**
(`mfMain_cMachXG` with the node step `stepX segP (stepPO cntP fixP c2sP s2cP retP frmP)`, the
zero memory below `Wz` and the family `NF` meeting its specifications at the calls). The same
bound `95 N + 200 + headline(K, K₀) + 2000 (2 N + 1) + 2`, for any cost family `c` with
`c.Bounds K K₀` and `hlin` (`mfMain_cMachXGN` with `cMach C C₀` replaced by `c`). Program hypotheses: the
separator (`SepPSpecXL`), the parts (`SegPSpec`), the five subroutines (`…PSpecN`); `cntP` is
discharged. -/
theorem mfMain_XGNGenX'' (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (ep : PVert M → TDart M) (hep : ∀ w, (tnlMap M).tail (ep w) = w)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    (pc : PcChoice _ _) (hpc : ∀ P Hs, pc.OK (lpreMapX M ep hep) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMapX M ep hep)) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W)
    {x₀ : D} (hx₀ : x₀ ∈ nlDarts M)
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    (hlin : ∀ a b, 200 * a + c.lin b ≤ c.lin (a + b)) {I : Input} {W Hb Wz Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ}
    {sepL segP fixP c2sP s2cP retP frmP : Stmt} {NF : NFam (lpreMapX M ep hep)}
    {sTL : ℕ → ℕ → ℕ} {sRL : ℕ → ℕ → ℕ → ℕ} {sgT sgR rO : MCall (lpreMapX M ep hep) → ℕ}
    {fT rtT fmT : MCall (lpreMapX M ep hep) → ℕ → ℕ} {cT s2T : MCall (lpreMapX M ep hep) → ℕ → ℕ → ℕ}
    {RS RT : ℕ} {wzc : ℕ → ℕ → ℕ} (hZ : 2 * Z ≤ W) :
    let gS := gSz (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMapX M ep hep) (pendQ _))
    let gH := gHl (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMapX M ep hep) (pendQ _))
    let ds : DSys (lpreMapX M ep hep) := ⟨guardS (lpreMapX M ep hep) gS (spSR (lpreMapX M ep hep) pc sc (pendQ _)),
      guardS (lpreMapX M ep hep) gH (spHR (lpreMapX M ep hep) pc sc (pendQ _)),
      chRot (lpreMapX M ep hep) (pendQ _), 100000, pendQ _, pc.pick⟩
    let τ := decS (lpreMapX M ep hep) (guardS (lpreMapX M ep hep) gS (spSR (lpreMapX M ep hep) pc sc (pendQ _)))
      (guardS (lpreMapX M ep hep) gH (spHR (lpreMapX M ep hep) pc sc (pendQ _)))
      (smD (lpreMapX M ep hep) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMapX M ep hep) (pendQ _)) 100000 univ [] (rootRot (lpreMapX M ep hep) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMapX M ep hep) τ [] (rotPerm (lpreMapX M ep hep))
    let N := τ.piece.card
    SepPSpecXL (lpreMapX M ep hep) ds Reach gid ν u' S' T' Z I W sepL sTL sRL →
    SegPSpec' (lpreMapX M ep hep) ds Reach gid ν u' S' T' Z I W segP sgT sgR →
    NSpecOn (lpreMapX M ep hep) NF Reach →
    FixPSpecN' (lpreMapX M ep hep) NF Reach gid u' S' T' Z I W Wz wzc fixP fT rO →
    C2SPSpecNA (lpreMapX M ep hep) NF Reach gid u' S' T' Z I W Wz wzc c2sP cT rO →
    S2CPSpecNA (lpreMapX M ep hep) NF Reach gid u' S' T' Z I W Wz wzc s2cP s2T rO →
    RetPSpecN' (lpreMapX M ep hep) NF Reach gid u' S' T' Z I W Wz wzc retP rtT rO →
    FrmPSpecN' (lpreMapX M ep hep) NF Reach gid u' S' T' Z I W Wz wzc frmP fmT rO →
    (∀ m, m ≤ N → wzc m Z ≤ Wz) →
    (∀ x : MCall (lpreMapX M ep hep), x.2.1.length + 1 ≤ rO x) →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMapX M ep hep).head y ≠ (lpreMapX M ep hep).tail y) →
    100000 ≤ W →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      sTL (l.piece ∪ r.piece).card Hs.length + sgT (.node l r π, Hs, σ) ≤
        c.sep (l.piece ∪ r.piece).card + c.lin Hs.length) →
    (∀ l r π Hs σ (h : SCond (lpreMapX M ep hep) l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN (lpreMapX M ep hep) NF u' S' T' l r π Hs σ h).L[j]? = some πj →
      fT (.node l r π, Hs, σ) j ≤ c.fixRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
        πj.faces.card πj.k (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) ∧
      (∀ i, cT (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      (∀ i, s2T (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      rtT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) ∧
      fmT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))) →
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) → (∀ x, Reach x → sgR x + rO x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb VTb RTb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 2 ≤ Hb → Wz + 2 < Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    MemZ Wz c₀ →
    c₀.nreg 6700 = N → c₀.nreg 6701 = REVb → c₀.nreg 6702 = SIGb → c₀.nreg 6703 = CAPb →
    c₀.nreg 6704 = KRb → c₀.nreg 6705 = ntag τ → c₀.nreg 6706 = Z → c₀.nreg 6707 = Hb →
    c₀.nmem (Hb - 1) = VTb → c₀.nmem (Hb - 1 - 1) = RTb →
    (∀ i < N, c₀.nmem (REVb + i) < N ∧ en (c₀.nmem (REVb + i)) = (lpreMapX M ep hep).rev (en i)) →
    (∀ i < N, c₀.nmem (SIGb + i) < N ∧
      en (c₀.nmem (SIGb + i)) = rotPerm (lpreMapX M ep hep) (en i)) →
    (∀ i < N, (c₀.nmem (CAPb + i) : ℤ) = u' (en i) ∧ c₀.nmem (CAPb + i) ≤ Z) →
    (∀ i < N, c₀.nmem (KRb + i) = lrk S' T' (hunion []) ((lpreMapX M ep hep).tail (en i))) →
    (∀ i < N, c₀.nmem (VTb + i) = ν ((lpreMapX M ep hep).tail (en i))) →
    (∀ i < N, en i ∈ pdarts (lpreMapX M ep hep) (core (lpreMapX M ep hep) (pendQ _) univ) [] →
      c₀.nmem (RTb + i) < N ∧ en (c₀.nmem (RTb + i)) = rootRot (lpreMapX M ep hep) (pendQ _) (en i)) →
    REVb + N ≤ Hb → SIGb + N ≤ Hb → CAPb + N ≤ Hb → KRb + N ≤ Hb → VTb + N ≤ Hb - 2 →
    RTb + N ≤ Hb - 2 →
    Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N + (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq (.seq rfProg rxProg) (driver mtProg mlProg
        (splitSX (sepPX 100000 sepL))
        (nodeSF (stepX segP (stepPO cntP fixP c2sP s2cP retP frmP))))) c₀ c' t ∧
      t ≤ 95 * N + 200 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2) ∧ MemZ Wz c' ∧
      FOutL (lpreMapX M ep hep) gid u' S' T' Z (τ, [], rotPerm (lpreMapX M ep hep))
        (arunLN (lpreMapX M ep hep) NF u' S' T' τ [] (rotPerm (lpreMapX M ep hep)))
        (Hb + 5) (Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N) c' ∧
      IsMax M u S T (nlRunNX M ep hep u S T τ NF) := by
  intro gS gH ds τ u' S' T' Reach N hsL hseg hO hfx hc2 hs2 hrt hfm hwzN hrO hpk hν hloop hsW hsT
    hcost' hsR hrT REVb SIGb CAPb KRb VTb RTb en hen hgid hHb hWz c₀ hc₀ hz r0 r1 r2 r3 r4 r5
    r6 r7 hv hrt' hrev hsig hcap hkr hvt hst i1 i2 i3 i4 i5 i6 hW
  obtain ⟨hbal, -, -⟩ := maxflow_plane_cost_decGX hM hrot hface hx₀ ep hep hu hST pc hpc sc hsc
    hc
  have hok := callOk_rootX hM hrot hface hx₀ ep hep hbal
  obtain ⟨c₁, t₁, e₁, ht₁, hw₁, b0, b1, b2, b3, m0, m1, m2, hin, ho₁⟩ :=
    rfxProg_root (I := I) (W := W) (Reach := Reach) (gid := gid) (ν := ν) (u := u') (S := S')
      (T := T') (Z := Z) (ds := ds) (rootRot (lpreMapX M ep hep) (pendQ _)) (rotPerm (lpreMapX M ep hep))
      hbal.1 (calls_self _ _ _) hok hen hgid c₀ hc₀ r0 r1 r2 r3 r4 r5 r6 r7 hrev hsig hcap hkr hv
      hrt' hvt hst i1 i2 i3 i4 i5 i6 hHb (by clear * - hW; omega)
  have hz₁ : MemZ Wz c₁ := rfxProg_memZ (I := I) (W := W) c₀ hc₀ hz (by clear * - hWz; omega)
    r0 r2 r5 r6 r7 hv hrt' i1 i2 i3 i4 i5 i6 hHb (by clear * - hW; omega) r1 r3 r4 c₁ t₁ e₁
  obtain ⟨hpc, c', t, ex, ht, hz', hout, hmax⟩ := mfDriveFrameXN_GenX'' hM hrot hface ep hep hu hST pc hpc
    sc hsc hx₀ hc hlin hZ hsL hseg hO hfx hc2 hs2 hrt hfm hwzN hrO hpk hν hloop hsW hsT hcost' hsR
    hrT (by clear * - hHb; omega) (by clear * - hWz; omega) c₁ hw₁ hz₁ b0 b1 b2 b3 m0 m1 m2
    (by clear * -; omega) le_rfl (by clear * - hW; omega) hin
  have ht' : t ≤ (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * τ.piece.card + 1) + 2 := ht
  exact ⟨hpc, c', t₁ + t, .seq e₁ ex, by clear * - ht₁ ht'; omega, hz', hout, hmax⟩

/-- **The whole program with the choices of the enumeration and the machine's separator, for any
family of node subroutines** (`mfMain_cMachXGE` with the node step
`stepX segP (stepPO cntP fixP c2sP s2cP retP frmP)`), for any cost family `c` with
`c.Bounds K K₀` and `hlin`: `mfMain_XGNGenX''` for `pc = pcChoiceE … e n d₀` and Miller's separator
`sepC … e n (encB' W)` (`mfMain_cMachXGEN` with `cMach C C₀` replaced by `c`). -/
theorem mfMain_XGENGenX'' (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (ep : PVert M → TDart M) (hep : ∀ w, (tnlMap M).tail (ep w) = w)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M)
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    (hlin : ∀ a b, 200 * a + c.lin b ≤ c.lin (a + b)) {I : Input} {W Hb Wz Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ}
    {sepL segP fixP c2sP s2cP retP frmP : Stmt} {NF : NFam (lpreMapX M ep hep)}
    {sTL : ℕ → ℕ → ℕ} {sRL : ℕ → ℕ → ℕ → ℕ} {sgT sgR rO : MCall (lpreMapX M ep hep) → ℕ}
    {fT rtT fmT : MCall (lpreMapX M ep hep) → ℕ → ℕ} {cT s2T : MCall (lpreMapX M ep hep) → ℕ → ℕ → ℕ}
    {RS RT : ℕ} {wzc : ℕ → ℕ → ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMapX M ep hep) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMapX M ep hep) (sepC (lpreMapX M ep hep) e n (encB' W)) e n Hs A W
    let gS := gSz (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMapX M ep hep) (pendQ _))
    let gH := gHl (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMapX M ep hep) (pendQ _))
    let ds : DSys (lpreMapX M ep hep) := ⟨guardS (lpreMapX M ep hep) gS (spSR (lpreMapX M ep hep) pc sc (pendQ _)),
      guardS (lpreMapX M ep hep) gH (spHR (lpreMapX M ep hep) pc sc (pendQ _)),
      chRot (lpreMapX M ep hep) (pendQ _), 100000, pendQ _, pc.pick⟩
    let τ := decS (lpreMapX M ep hep) (guardS (lpreMapX M ep hep) gS (spSR (lpreMapX M ep hep) pc sc (pendQ _)))
      (guardS (lpreMapX M ep hep) gH (spHR (lpreMapX M ep hep) pc sc (pendQ _)))
      (smD (lpreMapX M ep hep) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMapX M ep hep) (pendQ _)) 100000 univ [] (rootRot (lpreMapX M ep hep) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMapX M ep hep) τ [] (rotPerm (lpreMapX M ep hep))
    let N := τ.piece.card
    SepPSpecXL (lpreMapX M ep hep) ds Reach gid ν u' S' T' Z I W sepL sTL sRL →
    SegPSpec' (lpreMapX M ep hep) ds Reach gid ν u' S' T' Z I W segP sgT sgR →
    NSpecOn (lpreMapX M ep hep) NF Reach →
    FixPSpecN' (lpreMapX M ep hep) NF Reach gid u' S' T' Z I W Wz wzc fixP fT rO →
    C2SPSpecNA (lpreMapX M ep hep) NF Reach gid u' S' T' Z I W Wz wzc c2sP cT rO →
    S2CPSpecNA (lpreMapX M ep hep) NF Reach gid u' S' T' Z I W Wz wzc s2cP s2T rO →
    RetPSpecN' (lpreMapX M ep hep) NF Reach gid u' S' T' Z I W Wz wzc retP rtT rO →
    FrmPSpecN' (lpreMapX M ep hep) NF Reach gid u' S' T' Z I W Wz wzc frmP fmT rO →
    (∀ m, m ≤ N → wzc m Z ≤ Wz) →
    (∀ x : MCall (lpreMapX M ep hep), x.2.1.length + 1 ≤ rO x) →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMapX M ep hep).head y ≠ (lpreMapX M ep hep).tail y) →
    100000 ≤ W →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      sTL (l.piece ∪ r.piece).card Hs.length + sgT (.node l r π, Hs, σ) ≤
        c.sep (l.piece ∪ r.piece).card + c.lin Hs.length) →
    (∀ l r π Hs σ (h : SCond (lpreMapX M ep hep) l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN (lpreMapX M ep hep) NF u' S' T' l r π Hs σ h).L[j]? = some πj →
      fT (.node l r π, Hs, σ) j ≤ c.fixRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
        πj.faces.card πj.k (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) ∧
      (∀ i, cT (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      (∀ i, s2T (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      rtT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) ∧
      fmT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))) →
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) → (∀ x, Reach x → sgR x + rO x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb VTb RTb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 2 ≤ Hb → Wz + 2 < Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    MemZ Wz c₀ →
    c₀.nreg 6700 = N → c₀.nreg 6701 = REVb → c₀.nreg 6702 = SIGb → c₀.nreg 6703 = CAPb →
    c₀.nreg 6704 = KRb → c₀.nreg 6705 = ntag τ → c₀.nreg 6706 = Z → c₀.nreg 6707 = Hb →
    c₀.nmem (Hb - 1) = VTb → c₀.nmem (Hb - 1 - 1) = RTb →
    (∀ i < N, c₀.nmem (REVb + i) < N ∧ en (c₀.nmem (REVb + i)) = (lpreMapX M ep hep).rev (en i)) →
    (∀ i < N, c₀.nmem (SIGb + i) < N ∧
      en (c₀.nmem (SIGb + i)) = rotPerm (lpreMapX M ep hep) (en i)) →
    (∀ i < N, (c₀.nmem (CAPb + i) : ℤ) = u' (en i) ∧ c₀.nmem (CAPb + i) ≤ Z) →
    (∀ i < N, c₀.nmem (KRb + i) = lrk S' T' (hunion []) ((lpreMapX M ep hep).tail (en i))) →
    (∀ i < N, c₀.nmem (VTb + i) = ν ((lpreMapX M ep hep).tail (en i))) →
    (∀ i < N, en i ∈ pdarts (lpreMapX M ep hep) (core (lpreMapX M ep hep) (pendQ _) univ) [] →
      c₀.nmem (RTb + i) < N ∧ en (c₀.nmem (RTb + i)) = rootRot (lpreMapX M ep hep) (pendQ _) (en i)) →
    REVb + N ≤ Hb → SIGb + N ≤ Hb → CAPb + N ≤ Hb → KRb + N ≤ Hb → VTb + N ≤ Hb - 2 →
    RTb + N ≤ Hb - 2 →
    Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N + (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq (.seq rfProg rxProg) (driver mtProg mlProg
        (splitSX (sepPX 100000 sepL))
        (nodeSF (stepX segP (stepPO cntP fixP c2sP s2cP retP frmP))))) c₀ c' t ∧
      t ≤ 95 * N + 200 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2) ∧ MemZ Wz c' ∧
      FOutL (lpreMapX M ep hep) gid u' S' T' Z (τ, [], rotPerm (lpreMapX M ep hep))
        (arunLN (lpreMapX M ep hep) NF u' S' T' τ [] (rotPerm (lpreMapX M ep hep)))
        (Hb + 5) (Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N) c' ∧
      IsMax M u S T (nlRunNX M ep hep u S T τ NF) := by
  intro pc sc
  exact mfMain_XGNGenX'' hM hrot hface ep hep hu hST pc (fun P Hs => pcChoiceE_ok hsurj d₀ _ P Hs) sc
    (fun Hs A W => scChoiceE_ok hsurj
      (sepC_ok (preP_loopless nlMap_loopless hep) e n (encB' W) Hs) A W) hx₀ hc hlin hZ


/-- **The whole program with the machine's node subroutines and the parts by `segP`, for any cost
family `c` with `c.Bounds K K₀` and `hlin`** (`mfMain_cMachXGEF` with `cMach C C₀` replaced by
`c`; see the module docstring). -/
theorem mfMain_XGEFGenX'' (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (ep : PVert M → TDart M) (hep : ∀ w, (tnlMap M).tail (ep w) = w)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) (I₀ : Input)
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    (hlin : ∀ a b, 200 * a + c.lin b ≤ c.lin (a + b)) {I : Input} {W Hb Wz Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ}
    {sepL sepX fixP c2sP s2cP retP frmP : Stmt}
    {chs : (x : MCall (lpreMapX M ep hep)) → (h : PieceInv (lpreMapX M ep hep) x.1.piece x.2.1 x.2.2) →
      STFlow.StChoice (pmap h)}
    {pch : (x : MCall (lpreMapX M ep hep)) → (h : PieceInv (lpreMapX M ep hep) x.1.piece x.2.1 x.2.2) →
      PushFn (Orbit.SDart (pdarts (lpreMapX M ep hep) x.1.piece x.2.1))
        (Orbit.SVert x.2.2 (pdarts (lpreMapX M ep hep) x.1.piece x.2.1))}
    {sTL sTX : ℕ → ℕ → ℕ} {sRL sRX : ℕ → ℕ → ℕ → ℕ} {rO : MCall (lpreMapX M ep hep) → ℕ}
    {fT rtT fmT : MCall (lpreMapX M ep hep) → ℕ → ℕ} {cT s2T : MCall (lpreMapX M ep hep) → ℕ → ℕ → ℕ}
    {RS RT : ℕ} {wzc : ℕ → ℕ → ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMapX M ep hep) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMapX M ep hep) (sepC (lpreMapX M ep hep) e n (encB' W)) e n Hs A W
    let gS := gSz (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMapX M ep hep) (pendQ _))
    let gH := gHl (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMapX M ep hep) (pendQ _))
    let ds : DSys (lpreMapX M ep hep) := ⟨guardS (lpreMapX M ep hep) gS (spSR (lpreMapX M ep hep) pc sc (pendQ _)),
      guardS (lpreMapX M ep hep) gH (spHR (lpreMapX M ep hep) pc sc (pendQ _)),
      chRot (lpreMapX M ep hep) (pendQ _), 100000, pendQ _, pc.pick⟩
    let τ := decS (lpreMapX M ep hep) (guardS (lpreMapX M ep hep) gS (spSR (lpreMapX M ep hep) pc sc (pendQ _)))
      (guardS (lpreMapX M ep hep) gH (spHR (lpreMapX M ep hep) pc sc (pendQ _)))
      (smD (lpreMapX M ep hep) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMapX M ep hep) (pendQ _)) 100000 univ [] (rootRot (lpreMapX M ep hep) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMapX M ep hep) τ [] (rotPerm (lpreMapX M ep hep))
    let N := τ.piece.card
    SepPSpecXL (lpreMapX M ep hep) ds Reach gid ν u' S' T' Z I W sepL sTL sRL →
    SepPSpecXS' (lpreMapX M ep hep) ds Reach gid ν u' S' T' Z I W sepX sTX sRX →
    (∀ x, Reach x → ∀ h, (chs x h).OK) →
    (∀ x, Reach x → ∀ h, (pmap h).IsPlane → PushSpec (pmap h) (pch x h)) →
    FixPSpecN' (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs pch)
      Reach gid u' S' T' Z I W Wz wzc fixP fT rO →
    C2SPSpecNA (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs pch)
      Reach gid u' S' T' Z I W Wz wzc c2sP cT rO →
    S2CPSpecNA (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs pch)
      Reach gid u' S' T' Z I W Wz wzc s2cP s2T rO →
    RetPSpecN' (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs pch)
      Reach gid u' S' T' Z I W Wz wzc retP rtT rO →
    FrmPSpecN' (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs pch)
      Reach gid u' S' T' Z I W Wz wzc frmP fmT rO →
    (∀ m, m ≤ N → wzc m Z ≤ Wz) →
    (∀ x : MCall (lpreMapX M ep hep), x.2.1.length + 1 ≤ rO x) →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMapX M ep hep).head y ≠ (lpreMapX M ep hep).tail y) →
    100000 ≤ W →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      sTL (l.piece ∪ r.piece).card Hs.length + segT (lpreMapX M ep hep) sTX sRX (.node l r π, Hs, σ) ≤
        c.sep (l.piece ∪ r.piece).card + c.lin Hs.length) →
    (∀ l r π Hs σ (h : SCond (lpreMapX M ep hep) l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs pch) u' S' T' l r π Hs σ h).L[j]? = some πj →
      fT (.node l r π, Hs, σ) j ≤ c.fixRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
        πj.faces.card πj.k (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) ∧
      (∀ i, cT (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      (∀ i, s2T (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      rtT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) ∧
      fmT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))) →
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) → (∀ x, Reach x → segR (lpreMapX M ep hep) sRX x + rO x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb VTb RTb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 2 ≤ Hb → Wz + 2 < Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    MemZ Wz c₀ →
    c₀.nreg 6700 = N → c₀.nreg 6701 = REVb → c₀.nreg 6702 = SIGb → c₀.nreg 6703 = CAPb →
    c₀.nreg 6704 = KRb → c₀.nreg 6705 = ntag τ → c₀.nreg 6706 = Z → c₀.nreg 6707 = Hb →
    c₀.nmem (Hb - 1) = VTb → c₀.nmem (Hb - 1 - 1) = RTb →
    (∀ i < N, c₀.nmem (REVb + i) < N ∧ en (c₀.nmem (REVb + i)) = (lpreMapX M ep hep).rev (en i)) →
    (∀ i < N, c₀.nmem (SIGb + i) < N ∧
      en (c₀.nmem (SIGb + i)) = rotPerm (lpreMapX M ep hep) (en i)) →
    (∀ i < N, (c₀.nmem (CAPb + i) : ℤ) = u' (en i) ∧ c₀.nmem (CAPb + i) ≤ Z) →
    (∀ i < N, c₀.nmem (KRb + i) = lrk S' T' (hunion []) ((lpreMapX M ep hep).tail (en i))) →
    (∀ i < N, c₀.nmem (VTb + i) = ν ((lpreMapX M ep hep).tail (en i))) →
    (∀ i < N, en i ∈ pdarts (lpreMapX M ep hep) (core (lpreMapX M ep hep) (pendQ _) univ) [] →
      c₀.nmem (RTb + i) < N ∧ en (c₀.nmem (RTb + i)) = rootRot (lpreMapX M ep hep) (pendQ _) (en i)) →
    REVb + N ≤ Hb → SIGb + N ≤ Hb → CAPb + N ≤ Hb → KRb + N ≤ Hb → VTb + N ≤ Hb - 2 →
    RTb + N ≤ Hb - 2 →
    Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N + (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq (.seq rfProg rxProg) (driver mtProg mlProg
        (splitSX (sepPX 100000 sepL))
        (nodeSF (stepX (segP' sepX) (stepPO cntP fixP c2sP s2cP retP frmP))))) c₀ c' t ∧
      t ≤ 95 * N + 200 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2) ∧ MemZ Wz c' ∧
      FOutL (lpreMapX M ep hep) gid u' S' T' Z (τ, [], rotPerm (lpreMapX M ep hep))
        (arunLN (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs pch) u' S' T' τ [] (rotPerm (lpreMapX M ep hep)))
        (Hb + 5) (Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N) c' ∧
      IsMax M u S T (nlRunNX M ep hep u S T τ (NsStep.machNF gid I₀ chs pch)) := by
  intro pc sc gS gH ds τ u' S' T' Reach N hsL hsX hok hpush
  exact mfMain_XGENGenX'' hM hrot hface ep hep hu hST e hsurj d₀ hx₀ hc hlin hZ hsL (segP'_spec hsX)
    (NsStep.nSpecOn_machNF gid I₀ chs pch Reach hok hpush)


/-- **The whole program with the machine's node subroutines, the push-back of `NsStep.pchCall`
and the parts by `segP`** (`mfMain_XGEFGenX''` with `pch = NsStep.pchCall gid`; its `PushSpec`
hypothesis discharged by `NsStep.pushSpec_pchCall`), for any cost family `c` with `c.Bounds K K₀`
and `hlin` (`mfMain_cMachXGEP` with `cMach C C₀` replaced by `c`). -/
theorem mfMain_XGEPGenX'' (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (ep : PVert M → TDart M) (hep : ∀ w, (tnlMap M).tail (ep w) = w)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) (I₀ : Input)
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    (hlin : ∀ a b, 200 * a + c.lin b ≤ c.lin (a + b)) {I : Input} {W Hb Wz Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ}
    {sepL sepX fixP c2sP s2cP retP frmP : Stmt}
    {chs : (x : MCall (lpreMapX M ep hep)) → (h : PieceInv (lpreMapX M ep hep) x.1.piece x.2.1 x.2.2) →
      STFlow.StChoice (pmap h)}
    {sTL sTX : ℕ → ℕ → ℕ} {sRL sRX : ℕ → ℕ → ℕ → ℕ} {rO : MCall (lpreMapX M ep hep) → ℕ}
    {fT rtT fmT : MCall (lpreMapX M ep hep) → ℕ → ℕ} {cT s2T : MCall (lpreMapX M ep hep) → ℕ → ℕ → ℕ}
    {RS RT : ℕ} {wzc : ℕ → ℕ → ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMapX M ep hep) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMapX M ep hep) (sepC (lpreMapX M ep hep) e n (encB' W)) e n Hs A W
    let gS := gSz (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMapX M ep hep) (pendQ _))
    let gH := gHl (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMapX M ep hep) (pendQ _))
    let ds : DSys (lpreMapX M ep hep) := ⟨guardS (lpreMapX M ep hep) gS (spSR (lpreMapX M ep hep) pc sc (pendQ _)),
      guardS (lpreMapX M ep hep) gH (spHR (lpreMapX M ep hep) pc sc (pendQ _)),
      chRot (lpreMapX M ep hep) (pendQ _), 100000, pendQ _, pc.pick⟩
    let τ := decS (lpreMapX M ep hep) (guardS (lpreMapX M ep hep) gS (spSR (lpreMapX M ep hep) pc sc (pendQ _)))
      (guardS (lpreMapX M ep hep) gH (spHR (lpreMapX M ep hep) pc sc (pendQ _)))
      (smD (lpreMapX M ep hep) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMapX M ep hep) (pendQ _)) 100000 univ [] (rootRot (lpreMapX M ep hep) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMapX M ep hep) τ [] (rotPerm (lpreMapX M ep hep))
    let N := τ.piece.card
    SepPSpecXL (lpreMapX M ep hep) ds Reach gid ν u' S' T' Z I W sepL sTL sRL →
    SepPSpecXS' (lpreMapX M ep hep) ds Reach gid ν u' S' T' Z I W sepX sTX sRX →
    (∀ x, Reach x → ∀ h, (chs x h).OK) →
    FixPSpecN' (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz wzc fixP fT rO →
    C2SPSpecNA (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz wzc c2sP cT rO →
    S2CPSpecNA (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz wzc s2cP s2T rO →
    RetPSpecN' (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz wzc retP rtT rO →
    FrmPSpecN' (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz wzc frmP fmT rO →
    (∀ m, m ≤ N → wzc m Z ≤ Wz) →
    (∀ x : MCall (lpreMapX M ep hep), x.2.1.length + 1 ≤ rO x) →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMapX M ep hep).head y ≠ (lpreMapX M ep hep).tail y) →
    100000 ≤ W →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      sTL (l.piece ∪ r.piece).card Hs.length + segT (lpreMapX M ep hep) sTX sRX (.node l r π, Hs, σ) ≤
        c.sep (l.piece ∪ r.piece).card + c.lin Hs.length) →
    (∀ l r π Hs σ (h : SCond (lpreMapX M ep hep) l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid)) u' S' T' l r π Hs σ
        h).L[j]? = some πj →
      fT (.node l r π, Hs, σ) j ≤ c.fixRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
        πj.faces.card πj.k (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) ∧
      (∀ i, cT (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      (∀ i, s2T (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      rtT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) ∧
      fmT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))) →
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) → (∀ x, Reach x → segR (lpreMapX M ep hep) sRX x + rO x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb VTb RTb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 2 ≤ Hb → Wz + 2 < Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    MemZ Wz c₀ →
    c₀.nreg 6700 = N → c₀.nreg 6701 = REVb → c₀.nreg 6702 = SIGb → c₀.nreg 6703 = CAPb →
    c₀.nreg 6704 = KRb → c₀.nreg 6705 = ntag τ → c₀.nreg 6706 = Z → c₀.nreg 6707 = Hb →
    c₀.nmem (Hb - 1) = VTb → c₀.nmem (Hb - 1 - 1) = RTb →
    (∀ i < N, c₀.nmem (REVb + i) < N ∧ en (c₀.nmem (REVb + i)) = (lpreMapX M ep hep).rev (en i)) →
    (∀ i < N, c₀.nmem (SIGb + i) < N ∧
      en (c₀.nmem (SIGb + i)) = rotPerm (lpreMapX M ep hep) (en i)) →
    (∀ i < N, (c₀.nmem (CAPb + i) : ℤ) = u' (en i) ∧ c₀.nmem (CAPb + i) ≤ Z) →
    (∀ i < N, c₀.nmem (KRb + i) = lrk S' T' (hunion []) ((lpreMapX M ep hep).tail (en i))) →
    (∀ i < N, c₀.nmem (VTb + i) = ν ((lpreMapX M ep hep).tail (en i))) →
    (∀ i < N, en i ∈ pdarts (lpreMapX M ep hep) (core (lpreMapX M ep hep) (pendQ _) univ) [] →
      c₀.nmem (RTb + i) < N ∧ en (c₀.nmem (RTb + i)) = rootRot (lpreMapX M ep hep) (pendQ _) (en i)) →
    REVb + N ≤ Hb → SIGb + N ≤ Hb → CAPb + N ≤ Hb → KRb + N ≤ Hb → VTb + N ≤ Hb - 2 →
    RTb + N ≤ Hb - 2 →
    Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N + (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq (.seq rfProg rxProg) (driver mtProg mlProg
        (splitSX (sepPX 100000 sepL))
        (nodeSF (stepX (segP' sepX) (stepPO cntP fixP c2sP s2cP retP frmP))))) c₀ c' t ∧
      t ≤ 95 * N + 200 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2) ∧ MemZ Wz c' ∧
      FOutL (lpreMapX M ep hep) gid u' S' T' Z (τ, [], rotPerm (lpreMapX M ep hep))
        (arunLN (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid)) u' S' T' τ [] (rotPerm (lpreMapX M ep hep)))
        (Hb + 5) (Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N) c' ∧
      IsMax M u S T (nlRunNX M ep hep u S T τ (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))) := by
  intro pc sc gS gH ds τ u' S' T' Reach N hsL hsX hok
  exact mfMain_XGEFGenX'' hM hrot hface ep hep hu hST e hsurj d₀ hx₀ I₀ hc hlin hZ hsL hsX hok
    (fun x _ h hpl => NsStep.pushSpec_pchCall gid x h hpl)


/-- **The whole program with the machine's node subroutines, the push-back of `NsStep.pchCall`
and the parts by `segP`, with the scaled machine costs `cMachS C C₀`** (`mfMain_XGEPGenX''` for
`c = cMachS C C₀`, `K = machKS C = 10¹⁵ · machK C`, `K₀ = C₀`): within
`95 N + 200 + ((100000+11)² · 448 · (27 · 102256 + 25) · machKS C · n · lg³ n +
(100000+11)² · 28 · C₀ · n · lg n + 2000 (2 N + 1) + 2)` steps (`n = #D`). The subroutine costs
are asked in the fields of `cMachS C C₀` (`10¹⁵` times those of `cMach C C₀`: `cMachS_fixRun`,
`cMachS_c2sRun`, `cMachS_pushRun`, `cMachS_lin`); the separator steps in `C n lg n + C h` as in
`mfMain_cMachXGEP`; `1 ≤ C` (no condition on `C₀`). -/
theorem mfMain_cMachSGEPX'' (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (ep : PVert M → TDart M) (hep : ∀ w, (tnlMap M).tail (ep w) = w)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) (I₀ : Input)
    {C C₀ : ℕ} (hC : 1 ≤ C) {I : Input} {W Hb Wz Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ}
    {sepL sepX fixP c2sP s2cP retP frmP : Stmt}
    {chs : (x : MCall (lpreMapX M ep hep)) → (h : PieceInv (lpreMapX M ep hep) x.1.piece x.2.1 x.2.2) →
      STFlow.StChoice (pmap h)}
    {sTL sTX : ℕ → ℕ → ℕ} {sRL sRX : ℕ → ℕ → ℕ → ℕ} {rO : MCall (lpreMapX M ep hep) → ℕ}
    {fT rtT fmT : MCall (lpreMapX M ep hep) → ℕ → ℕ} {cT s2T : MCall (lpreMapX M ep hep) → ℕ → ℕ → ℕ}
    {RS RT : ℕ} {wzc : ℕ → ℕ → ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMapX M ep hep) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMapX M ep hep) (sepC (lpreMapX M ep hep) e n (encB' W)) e n Hs A W
    let gS := gSz (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMapX M ep hep) (pendQ _))
    let gH := gHl (lpreMapX M ep hep) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMapX M ep hep) (pendQ _))
    let ds : DSys (lpreMapX M ep hep) := ⟨guardS (lpreMapX M ep hep) gS (spSR (lpreMapX M ep hep) pc sc (pendQ _)),
      guardS (lpreMapX M ep hep) gH (spHR (lpreMapX M ep hep) pc sc (pendQ _)),
      chRot (lpreMapX M ep hep) (pendQ _), 100000, pendQ _, pc.pick⟩
    let τ := decS (lpreMapX M ep hep) (guardS (lpreMapX M ep hep) gS (spSR (lpreMapX M ep hep) pc sc (pendQ _)))
      (guardS (lpreMapX M ep hep) gH (spHR (lpreMapX M ep hep) pc sc (pendQ _)))
      (smD (lpreMapX M ep hep) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMapX M ep hep) (pendQ _)) 100000 univ [] (rootRot (lpreMapX M ep hep) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMapX M ep hep) τ [] (rotPerm (lpreMapX M ep hep))
    let N := τ.piece.card
    let c := cMachS C C₀
    SepPSpecXL (lpreMapX M ep hep) ds Reach gid ν u' S' T' Z I W sepL sTL sRL →
    SepPSpecXS' (lpreMapX M ep hep) ds Reach gid ν u' S' T' Z I W sepX sTX sRX →
    (∀ x, Reach x → ∀ h, (chs x h).OK) →
    FixPSpecN' (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz wzc fixP fT rO →
    C2SPSpecNA (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz wzc c2sP cT rO →
    S2CPSpecNA (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz wzc s2cP s2T rO →
    RetPSpecN' (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz wzc retP rtT rO →
    FrmPSpecN' (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz wzc frmP fmT rO →
    (∀ m, m ≤ N → wzc m Z ≤ Wz) →
    (∀ x : MCall (lpreMapX M ep hep), x.2.1.length + 1 ≤ rO x) →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMapX M ep hep).head y ≠ (lpreMapX M ep hep).tail y) →
    100000 ≤ W →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      sTL (l.piece ∪ r.piece).card Hs.length + segT (lpreMapX M ep hep) sTX sRX (.node l r π, Hs, σ) ≤
        C * (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card + C * Hs.length) →
    (∀ l r π Hs σ (h : SCond (lpreMapX M ep hep) l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid)) u' S' T' l r π Hs σ
        h).L[j]? = some πj →
      fT (.node l r π, Hs, σ) j ≤ c.fixRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
        πj.faces.card πj.k (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) ∧
      (∀ i, cT (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      (∀ i, s2T (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      rtT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) ∧
      fmT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMapX M ep hep)) (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))
          (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMapX M ep hep) σ (pdarts (lpreMapX M ep hep) (l.piece ∪ r.piece) Hs))) →
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) → (∀ x, Reach x → segR (lpreMapX M ep hep) sRX x + rO x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb VTb RTb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 2 ≤ Hb → Wz + 2 < Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    MemZ Wz c₀ →
    c₀.nreg 6700 = N → c₀.nreg 6701 = REVb → c₀.nreg 6702 = SIGb → c₀.nreg 6703 = CAPb →
    c₀.nreg 6704 = KRb → c₀.nreg 6705 = ntag τ → c₀.nreg 6706 = Z → c₀.nreg 6707 = Hb →
    c₀.nmem (Hb - 1) = VTb → c₀.nmem (Hb - 1 - 1) = RTb →
    (∀ i < N, c₀.nmem (REVb + i) < N ∧ en (c₀.nmem (REVb + i)) = (lpreMapX M ep hep).rev (en i)) →
    (∀ i < N, c₀.nmem (SIGb + i) < N ∧
      en (c₀.nmem (SIGb + i)) = rotPerm (lpreMapX M ep hep) (en i)) →
    (∀ i < N, (c₀.nmem (CAPb + i) : ℤ) = u' (en i) ∧ c₀.nmem (CAPb + i) ≤ Z) →
    (∀ i < N, c₀.nmem (KRb + i) = lrk S' T' (hunion []) ((lpreMapX M ep hep).tail (en i))) →
    (∀ i < N, c₀.nmem (VTb + i) = ν ((lpreMapX M ep hep).tail (en i))) →
    (∀ i < N, en i ∈ pdarts (lpreMapX M ep hep) (core (lpreMapX M ep hep) (pendQ _) univ) [] →
      c₀.nmem (RTb + i) < N ∧ en (c₀.nmem (RTb + i)) = rootRot (lpreMapX M ep hep) (pendQ _) (en i)) →
    REVb + N ≤ Hb → SIGb + N ≤ Hb → CAPb + N ≤ Hb → KRb + N ≤ Hb → VTb + N ≤ Hb - 2 →
    RTb + N ≤ Hb - 2 →
    Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N + (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq (.seq rfProg rxProg) (driver mtProg mlProg
        (splitSX (sepPX 100000 sepL))
        (nodeSF (stepX (segP' sepX) (stepPO cntP fixP c2sP s2cP retP frmP))))) c₀ c' t ∧
      t ≤ 95 * N + 200 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machKS C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2) ∧ MemZ Wz c' ∧
      FOutL (lpreMapX M ep hep) gid u' S' T' Z (τ, [], rotPerm (lpreMapX M ep hep))
        (arunLN (lpreMapX M ep hep) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid)) u' S' T' τ [] (rotPerm (lpreMapX M ep hep)))
        (Hb + 5) (Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N) c' ∧
      IsMax M u S T (nlRunNX M ep hep u S T τ (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))) := by
  intro pc sc gS gH ds τ u' S' T' Reach N c hsL hsX hok hfx hc2 hs2 hrt hfm hwzN hrO hpk hν hloop
    hsW hsT
  exact mfMain_XGEPGenX'' hM hrot hface ep hep hu hST e hsurj d₀ hx₀ I₀ (cMachS_bounds C C₀)
    (cMachS_linLow hC) hZ hsL hsX hok hfx hc2 hs2 hrt hfm hwzN hrO hpk hν hloop hsW
    (fun l r π Hs σ hx => (hsT l r π Hs σ hx).trans (cMachS_sepLin hC _ _))


end Head

end Pp

end BKMNW

end PlanarFlow
