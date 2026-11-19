module

public import PlanarFlow.BKMNW.ThFinal
public import PlanarFlow.BKMNW.Nf7dA

/-!
# The primed specifications of `fixP`

* **`MfDrv.FixPSpecN''`**: `FixPSpecN'` with the input flow of the part a pseudoflow for `U` in the
  precondition; **`MfDrv.FixPSpecN''.toN'`**: at the reachable
  calls (`u ≥ 0`, `Disjoint S T`, `NSpecOn`, `Reach` closed under calls) it gives `FixPSpecN'`
  (`seg_pseudo`);
* **`Pp.FixHypF'`** (the MSSP premise with a step bound `cost` leaving
  `200 k² + 2000 k + 2000` of `mssp`; plus scratch below `9300`), **`Pp.mfMainSpecS''_final'`**,
  **`Pp.maxFlowMachine_final'`** (the final assembly with `FixHypF'`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NcStep

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **`FixPSpecN'` with the input flow of the part a pseudoflow** for the capacities. -/
def FixPSpecN'' (NF : NFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (wzc : ℕ → ℕ → ℕ) (fixP : Stmt)
    (fT : MCall M → ℕ → ℕ) (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j : ℕ) (πj : SPath (pmap h.1)),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d → wzc m Z ≤ Wz →
    (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj →
    IsPseudo (pmap h.1) (fun x => u x.1) ((xCtxN M NF u S T l r π Hs σ h).seg j) →
    FlowProg M gid u S T Z I W fixP (.node l r π, Hs, σ) m en d e b
      (fun c => (c.nreg 6800 = j ∧ MemZ Wz c) ∧ SegsAt' M en m π e b c)
      ((xCtxN M NF u S T l r π Hs σ h).seg j)
      ((xCtxN M NF u S T l r π Hs σ h).O.fix (xCtxN M NF u S T l r π Hs σ h).U
        ((xCtxN M NF u S T l r π Hs σ h).seg j) πj) (fT (.node l r π, Hs, σ) j)

/-- **`FixPSpecN''` gives `FixPSpecN'` at the reachable calls** (the input flow of every part is a
pseudoflow there, `seg_pseudo`). -/
theorem FixPSpecN''.toN' {NF : NFam M} {Reach : MCall M → Prop} {gid : D → ℕ} {u : D → ℤ}
    {S T : Finset V} {Z : ℕ} {I : Input} {W Wz : ℕ} {wzc : ℕ → ℕ → ℕ} {fixP : Stmt}
    {fT : MCall M → ℕ → ℕ} {rO : MCall M → ℕ} (hu : ∀ d, 0 ≤ u d) (hST : Disjoint S T)
    (hO : NSpecOn M NF Reach) (hR : ∀ x y, Reach x → Calls M x.1 x.2.1 x.2.2 y → Reach y)
    (h : FixPSpecN'' M NF Reach gid u S T Z I W Wz wzc fixP fT rO) :
    FixPSpecN' M NF Reach gid u S T Z I W Wz wzc fixP fT rO :=
  fun l r π Hs σ hs d e b m en j πj hx hok a1 a2 a3 a4 a5 hj =>
    h l r π Hs σ hs d e b m en j πj hx hok a1 a2 a3 a4 a5 hj
      (seg_pseudo hu hST hO hR hx hok hs hj)

end MfDrv

namespace Pp

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver MfDrv
  PlanarSeparator.StDart NcStep

/-- **What `fixP` must meet, with the MSSP cost restated**:
as `FixHypF`, but the MSSP call program meets `MsspCallSpec` with some step bound `cost` that
leaves `200 k² + 2000 k + 2000` of the `mssp` field for `q ≤ 2k` queries, and its scratch
registers lie below `9300` (`st2a_exec` saves the driver's registers around the call and
needs the registers `≥ 9300` kept). -/
def FixHypF' (fixP msP : Stmt) (Scr : ℕ → Prop) (cost Rm : ℕ → ℕ → ℕ → ℕ) (wzm : ℕ → ℕ → ℕ)
    (C C₀ : ℕ) (wzF rF : ℕ → ℕ → ℕ) : Prop :=
    (∀ {D' V' F' : Type} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V'] [Fintype F']
      [DecidableEq F'] (M' : CombMap D' V' F'), MsCall.MsspCallSpec M' msP Scr cost Rm wzm) →
  (∀ m k q, 1 ≤ m → q ≤ 2 * k →
    cost m k q + 200 * k ^ 2 + 2000 * k + 2000 ≤ (cMachS C C₀).mssp m k) →
  (∀ r, Scr r → r < 9300) →
  ∀ {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
    [DecidableEq F] (M : CombMap D V F), M.IsPlane → M.RotTrans → M.FaceTrans →
  ∀ (ep : PVert M → TDart M) (hep : ∀ w, (tnlMap M).tail (ep w) = w) {u : D → ℤ},
    (∀ d, 0 ≤ u d) → ∀ {S T : Finset V}, Disjoint S T → (nlDarts M).Nonempty →
  ∀ {N : ℕ} (en : ℕ → TDart M ⊕ (PVert M × Bool)) (d₀ : TDart M ⊕ (PVert M × Bool))
    {gid : TDart M ⊕ (PVert M × Bool) → ℕ} {ν : PVert M ⊕ PVert M → ℕ},
    Fintype.card (TDart M ⊕ (PVert M × Bool)) = N →
    (∀ y, ∃ i < N, en i = y) → (∀ i < N, gid (en i) = i) → Injective ν →
    QPar (pendQ (PVert M)) ν → TailSorted (lpreMapX M ep hep) gid ν →
  let L := lpreMapX M ep hep
  let pc := pcChoiceE L (pendQ _) en N d₀
  let sc := fun Hs A W => scChoiceE L (sepC L en N (encB' W)) en N Hs A W
  let gS := gSz L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000 (CInvS L (pendQ _))
  let gH := gHl L (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000 (CInvS L (pendQ _))
  let τ := decS L (guardS L gS (spSR L pc sc (pendQ _))) (guardS L gH (spHR L pc sc (pendQ _)))
    (smD L pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
    (chRot L (pendQ _)) 100000 univ [] (rootRot L (pendQ _)) true
  let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
  let S' := preTerm (nlTerm M S)
  let T' := preTerm (nlTerm M T)
  let Reach := Calls L τ [] (rotPerm L)
  let c := cMachS C C₀
  ∀ {I : Input} {W Z Wz : ℕ}, 100000 ≤ W → 2 * Z ≤ W → 3 * ((N + 2) * (Z + 1)) ≤ W →
  ∃ (fT : MCall L → ℕ → ℕ) (rO : MCall L → ℕ),
    FixPSpecN' L (NcStep.machNFT gid I (NsStep.pchCall gid)) Reach gid u' S' T' Z I W Wz wzF fixP fT rO ∧
    (∀ x, Reach x → rO x ≤ rF N Z) ∧
    (∀ l r π Hs σ (h : SCond L l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN L (NcStep.machNFT gid I (NsStep.pchCall gid)) u' S' T' l r π Hs σ h).L[j]? = some πj →
      fT (.node l r π, Hs, σ) j ≤ c.fixRun (pdarts L (l.piece ∪ r.piece) Hs).card πj.faces.card πj.k (psize L σ (pdarts L (l.piece ∪ r.piece) Hs)))


set_option maxHeartbeats 4000000 in
/-- **`mfMainSpecS''_final` with `FixHypF'`** (the MSSP premise of `fixP` with a step bound `cost`
leaving slack in the `mssp` field, scratch below `9300`). As before: (see the module
docstring): the separator is `sepL` (with `sepX = sepPXS' 100000 sepL`), the node-step
programs `fixP`, `c2sP`, `s2cP` meet `FixHypF`, `C2SHypF`, `S2CHypF` for an MSSP call program `msP`
meeting `MsspCallSpec` at `msCostS C C₀` on every map. Room `rowR r q`, zero area
`a (N + Z + 1)^p`. -/
theorem mfMainSpecS''_final' {fixP c2sP s2cP msP : Stmt} {Scr : ℕ → Prop} {cost : ℕ → ℕ → ℕ → ℕ}
    {Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ} {C C₀ : ℕ} (hC : 3200000 ≤ C)
    {wzF wzC wzS rF rC rS : ℕ → ℕ → ℕ} {a p r q : ℕ}
    (hMS : ∀ {D' V' F' : Type} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
      [Fintype F'] [DecidableEq F'] (M' : CombMap D' V' F'),
      MsCall.MsspCallSpec M' msP Scr (MsEnc.msCostS C C₀) Rm wzm)
    (hMSc : ∀ {D' V' F' : Type} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
      [Fintype F'] [DecidableEq F'] (M' : CombMap D' V' F'),
      MsCall.MsspCallSpec M' msP Scr cost Rm wzm)
    (hcost : ∀ m k q, 1 ≤ m → q ≤ 2 * k →
      cost m k q + 200 * k ^ 2 + 2000 * k + 2000 ≤ (cMachS C C₀).mssp m k)
    (hScr : ∀ r, Scr r → r < 9300)
    (hfix : FixHypF' fixP msP Scr cost Rm wzm C C₀ wzF rF)
    (hc2s : C2SHypF c2sP msP Scr Rm wzm C C₀ wzC rC)
    (hs2c : S2CHypF s2cP msP Scr Rm wzm C C₀ wzS rS)
    (hwz : ∀ m Z, wzF m Z + wzC m Z + wzS m Z ≤ a * (m + Z + 1) ^ p)
    (hr : ∀ N Z, rF N Z + rC N Z + rS N Z ≤ r * (N + Z + 1) ^ q) :
    MfMainSpecS'' MfDrv.sepL MfDrv.sepX fixP c2sP s2cP C C₀ (rowR r q)
      (fun N Z => a * (N + Z + 1) ^ p) := by
  intro D V F _ _ _ _ _ _ M hM hrot hface ep hep u hu S T hST hne N en d₀ gid ν hN hsurj hgid hν
    hQ hTS
  unfold SubSpecS''
  intro L pc sc gS gH ds τ u' S' T' Reach c I W Z Wz hW hZ hNZ hWZ
  obtain ⟨fT, rOF, hfx, hrF, hfc⟩ := hfix hMSc hcost hScr M hM hrot hface ep hep hu hST hne en d₀ hN hsurj hgid
    hν hQ hTS (I := I) (W := W) (Z := Z) (Wz := Wz) hW hZ hNZ
  obtain ⟨cT, rOC, hc2, hrC, hcc⟩ := hc2s hMS M hM hrot hface ep hep hu hST hne en d₀ hN hsurj hgid
    hν hQ hTS (I := I) (W := W) (Z := Z) (Wz := Wz) hW hZ hNZ
  obtain ⟨s2T, rOS, hs2, hrS, hsc'⟩ := hs2c hMS M hM hrot hface ep hep hu hST hne en d₀ hN hsurj
    hgid hν hQ hTS (I := I) (W := W) (Z := Z) (Wz := Wz) hW hZ hNZ
  obtain ⟨x₀, hx₀⟩ := hne
  have hginj : Injective gid := by
    intro y₁ y₂ e
    obtain ⟨i₁, hi₁, rfl⟩ := hsurj y₁
    obtain ⟨i₂, hi₂, rfl⟩ := hsurj y₂
    rw [hgid i₁ hi₁, hgid i₂ hi₂] at e
    rw [e]
  have hpc : ∀ P Hs, pc.OK L (pendQ _) P Hs := fun P Hs => pcChoiceE_ok hsurj d₀ _ P Hs
  have hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W := fun Hs A W => scChoiceE_ok hsurj
    (sepC_ok (preP_loopless nlMap_loopless hep) en N (encB' W) Hs) A W
  have hbal := (maxflow_plane_cost_decGX hM hrot hface hx₀ ep hep hu hST pc hpc sc hsc
    (cMachS_bounds C C₀)).1
  have hcore := ADec.BalA.core hbal.2.2.2.2
  have hNc : τ.piece.card = N := by
    have h1 : τ.piece = univ := hbal.1
    rw [h1, card_univ]; exact hN
  have hsize : ∀ x, Reach x → x.2.1.length + x.1.piece.card ≤ N := fun x hx => by
    have := calls_size τ [] (rotPerm L) x hcore hx
    simp only [List.length_nil, zero_add] at this
    omega
  have hloop := preP_loopless nlMap_loopless hep
  obtain ⟨hq1, hq2, hq3⟩ := pendQ_hypsP (hrot := nlMap_rotTrans) hep (nlTerm M S) (nlTerm M T)
  have hpk := pkMin_pcChoiceE (M := L) (Q := pendQ _) hsurj hgid d₀
  have hL := sepL_spec (M := L) (ds := ds) (Reach := Reach) (u := u') (S := S') (T := T') (Z := Z)
    (I := I) (W := W) (gid := gid) (ν := ν) (κ := 9) (eG := en) (N := N) (d₀ := d₀)
    (splitFnsS_lpreRX ep hep S T pc hpc sc hsc)
    (fun P Hs hP => smD_piece (hpc univ []).pick _ P Hs rfl hP) rfl rfl rfl rfl rfl hq1 hloop hq2
    hq3 hTS hQ hν hginj hgid hsurj hW
  have hX := sepPXS'_spec hL hpk hν hloop hW
  refine ⟨I, sTL, sTX, sRL, sRX,
    fun x => x.2.1.length + 1 + (40 * (pdarts L x.1.piece x.2.1).card + 10) + rOF x + rOC x + rOS x,
    fT, cT, s2T, sRL N N N, 1 + sRX N N N + 41 * N + 11 + r * (N + Z + 1) ^ q,
    fun m Z => wzF m Z + wzC m Z + wzS m Z, hL.toXLS.toXL, hX,
    hfx.mono (fun m => by omega) (fun x => by omega),
    hc2.mono (fun m => by omega) (fun x => by omega),
    hs2.mono (fun m => by omega) (fun x => by omega), ?_, fun x => ⟨by beta_reduce; omega, by beta_reduce; omega⟩, ?_,
    fun l r π Hs σ h j πj hx hj => ⟨hfc l r π Hs σ h j πj hx hj, hcc l r π Hs σ h j πj hx hj,
      hsc' l r π Hs σ h j πj hx hj⟩, fun n m k hn hm hk => sRL_mono hn hm hk, ?_, ?_⟩
  · intro m hm
    refine (hwz m Z).trans (le_trans ?_ hWZ)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) p)
  · intro l r π Hs σ hx
    have hpos := calls_node_pos τ [] (rotPerm L) hcore hx
    have hm : (pdarts L (l.piece ∪ r.piece) Hs).card ≤ (l.piece ∪ r.piece).card :=
      card_le_card (pdarts_subset _ _)
    have h1 := sep_cost_le (k := Hs.length) hpos hm
    have h2 : 3200000 * (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card ≤
        C * (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hC)
    have h3 : 3200000 * Hs.length ≤ C * Hs.length := Nat.mul_le_mul_right _ hC
    show sTL (l.piece ∪ r.piece).card Hs.length + (sTX (l.piece ∪ r.piece).card Hs.length +
      13 * sRX (l.piece ∪ r.piece).card (pdarts L (l.piece ∪ r.piece) Hs).card Hs.length + 30) ≤ _
    omega
  · intro x hx
    have hs := hsize x hx
    have hm : (pdarts L x.1.piece x.2.1).card ≤ x.1.piece.card := card_le_card (pdarts_subset _ _)
    have h1 := sRL_mono (show x.1.piece.card ≤ N by omega)
      (show (pdarts L x.1.piece x.2.1).card ≤ N by omega) (show x.2.1.length ≤ N by omega)
    have h2 := hrF x hx
    have h3 := hrC x hx
    have h4 := hrS x hx
    have h5 := hr N Z
    show 1 + sRX x.1.piece.card (pdarts L x.1.piece x.2.1).card x.2.1.length + _ ≤ _
    unfold sRX smRS' smR
    beta_reduce
    omega
  · unfold rowR; omega

/-- **The maximum-flow theorem from one hypothesis per remaining program** (the final assembly):
the MSSP encoder `msEnc` meets `MsEncSpec'` on every map; `fixP`, `c2sP`, `s2cP` meet
`FixHypF`, `C2SHypF`, `S2CHypF` for the MSSP call `msspCall' msEnc`; they print nothing; their
zero-area functions sum to at most `a (m + Z + 1)^p` and their rooms to at most `r (N + Z + 1)^q`;
`3200000 ≤ C`. The separator (`sepL`, `sepX`), `cntP`, the parts `segP'`, the
push-backs `retP`/`frmP` are fixed and proved. ⟹ **`MaxFlowMachine'`** (time
`cMF C C₀ p · (n + K + 1) · (⌊log₂ n⌋ + 1)³`, word size polynomial of degree `p + q + 6`). -/

theorem maxFlowMachine_final' {fixP c2sP s2cP msEnc : Stmt} {C C₀ : ℕ} (hC : 3200000 ≤ C)
    {cost : ℕ → ℕ → ℕ → ℕ}
    {EScr : ℕ → Prop} {Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    {wzF wzC wzS rF rC rS : ℕ → ℕ → ℕ} {a p r q : ℕ}
    (hE : ∀ {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
      [DecidableEq F] (M : CombMap D V F), MsCall.MsEncSpec' M msEnc EScr MsEnc.msEncCost
        (fun m k _ => MsEnc.KCf m k) (fun m _ _ => MsEnc.ZCf m) Rm wzm)
    (hMSc : ∀ {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
      [DecidableEq F] (M : CombMap D V F), MsCall.MsspCallSpec M (MsCall.msspCall' msEnc)
        (fun x => EScr x ∨ MsCall.msScr x) cost Rm wzm)
    (hcost : ∀ m k q, 1 ≤ m → q ≤ 2 * k →
      cost m k q + 200 * k ^ 2 + 2000 * k + 2000 ≤ (cMachS C C₀).mssp m k)
    (hEScr : ∀ r, EScr r → r < 9300)
    (hfix : FixHypF' fixP (MsCall.msspCall' msEnc) (fun x => EScr x ∨ MsCall.msScr x) cost Rm wzm
      C C₀ wzF rF)
    (hc2s : C2SHypF c2sP (MsCall.msspCall' msEnc) (fun x => EScr x ∨ MsCall.msScr x) Rm wzm C C₀
      wzC rC)
    (hs2c : S2CHypF s2cP (MsCall.msspCall' msEnc) (fun x => EScr x ∨ MsCall.msScr x) Rm wzm C C₀
      wzS rS)
    (hE3 : Stmt.noEmit fixP = true) (hE4 : Stmt.noEmit c2sP = true)
    (hE5 : Stmt.noEmit s2cP = true)
    (hwz : ∀ m Z, wzF m Z + wzC m Z + wzS m Z ≤ a * (m + Z + 1) ^ p)
    (hr : ∀ N Z, rF N Z + rC N Z + rS N Z ≤ r * (N + Z + 1) ^ q) :
    MaxFlowMachine' :=
  maxFlowMachine_of_spec''
    (mfMainSpecS''_final' hC (fun M' => MsEnc.msspCall'_cMachS C C₀ (hE M')) hMSc hcost
      (fun r hr => hr.elim (hEScr r) (fun h => by unfold MsCall.msScr at h; omega)) hfix hc2s hs2c
      hwz hr)
    (by omega) sepL_noEmit sepX_noEmit hE3 hE4 hE5 (rowR_mono r q) (rowR_le r q) (fun N Z => le_rfl)


end Pp

end BKMNW

end PlanarFlow
