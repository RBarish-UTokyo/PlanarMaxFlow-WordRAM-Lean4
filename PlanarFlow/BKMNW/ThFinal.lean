module

public import PlanarFlow.BKMNW.ThPipeR
public import PlanarFlow.BKMNW.LsR
public import PlanarFlow.BKMNW.MsCost

/-!
# The final assembly of the maximum-flow theorem: one hypothesis per remaining program

* `MfDrv.calls_node_pos` (a reachable node call of a decomposition meeting `Core` has a nonempty
  piece), `FixPSpecN'.mono`, `C2SPSpecN''.mono`, `S2CPSpecN''.mono` (more room, larger zero-area
  function);
* **`FixHypF`**, **`C2SHypF`**, **`S2CHypF`**: what `fixP`, `c2sP`, `s2cP` must meet — at every
  instance, relative to the machine's family `NcStep.machNFT gid I (NsStep.pchCall gid)`, given that
  the MSSP call program `msP` meets `MsspCallSpec` with the step bound `msCostS C C₀` on every map:
  `FixPSpecN'`/`C2SPSpecN''`/`S2CPSpecN''` with a zero-area function `wzX m Z`, steps within
  `(cMachS C C₀).fixRun`/`c2sRun` at the node calls, a room `≤ rX N Z` at the calls;
* `rowR r q N Z = sRL N N N + 1 + sRX N N N + 41 N + 11 + r (N + Z + 1)^q` (the room per call),
  `rowR_mono`, **`rowR_le`** (`≤ (r + 3000000)(N + Z + 1)^(q + 2)`);
* **`mfMainSpecS''_final`**: the separator part discharged (`sepL`, `sepX = sepPXS' 100000 sepL`:
  `sepL_spec`, `sepPXS'_spec`, `sep_cost_le` with `C ≥ 3200000`; its hypotheses for
  `lpreMapX M ep hep` from `splitFnsS_lpreRX`, `smD_piece`, `pendQ_hypsP`, `preP_loopless` and the
  input conventions), `retP`/`frmP`/`cntP` fixed, the rooms and the zero area assembled:
  `FixHypF`, `C2SHypF`, `S2CHypF`, `wzF + wzC + wzS ≤ a (m + Z + 1)^p`,
  `rF + rC + rS ≤ r (N + Z + 1)^q` ⟹ `MfMainSpecS'' sepL sepX fixP c2sP s2cP C C₀ (rowR r q)
  (a (N + Z + 1)^p)`;
* `sepL_noEmit`, `sepX_noEmit`;
* **`maxFlowMachine_final`**: the MSSP encoder meeting `MsEncSpec'`, `FixHypF fixP`,
  `C2SHypF c2sP`, `S2CHypF s2cP` (MSSP program `msspCall' msEnc`), the three print nothing, the
  two polynomial bounds, `3200000 ≤ C` ⟹ **`MaxFlowMachine'`**.
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

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine

universe w

section Pos

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **A reachable node call has a nonempty piece** (when the decomposition meets `Core`). -/
theorem calls_node_pos {κ η : ℕ} : ∀ (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D)
    {l r : ADec M} {π : HSep M} {Hs' : List (Finset V)} {σ' : Perm D},
    τ.Core M κ η Hs → Calls M τ Hs σ (.node l r π, Hs', σ') → 0 < (l.piece ∪ r.piece).card
  | .leaf Q, Hs, σ, l, r, π, Hs', σ', _, hx => by simp [Calls] at hx
  | .node l₀ r₀ π₀, Hs, σ, l, r, π, Hs', σ', ⟨hl, hr, _, hl0, _, _⟩, hx => by
    rcases hx with hx | hx | hx
    · simp only [Prod.mk.injEq, ADec.node.injEq] at hx
      obtain ⟨⟨rfl, rfl, rfl⟩, -, -⟩ := hx
      exact lt_of_lt_of_le hl0 (card_le_card subset_union_left)
    · exact calls_node_pos l₀ _ _ hl hx
    · exact calls_node_pos r₀ _ _ hr hx

end Pos

section Mono

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {NF : NFam M} {Reach : MCall M → Prop} {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}
  {I : Input} {W Wz : ℕ} {wzc wzc' : ℕ → ℕ → ℕ} {rO rO' : MCall M → ℕ}

/-- More room and a larger zero-area function. -/
theorem FixPSpecN'.mono {fixP : Stmt} {fT : MCall M → ℕ → ℕ}
    (h : FixPSpecN' M NF Reach gid u S T Z I W Wz wzc fixP fT rO)
    (hw : ∀ m, wzc m Z ≤ wzc' m Z) (hr : ∀ x, rO x ≤ rO' x) :
    FixPSpecN' M NF Reach gid u S T Z I W Wz wzc' fixP fT rO' :=
  fun l r π Hs σ hs d e b m en j πj hR hC a1 a2 a3 a4 a5 =>
    h l r π Hs σ hs d e b m en j πj hR hC a1 a2 ((Nat.add_le_add_left (hr _) b).trans a3) a4
      ((hw m).trans a5)

/-- More room and a larger zero-area function. -/
theorem C2SPSpecN''.mono {c2sP : Stmt} {cT : MCall M → ℕ → ℕ → ℕ}
    (h : C2SPSpecN'' M NF Reach gid u S T Z I W Wz wzc c2sP cT rO)
    (hw : ∀ m, wzc m Z ≤ wzc' m Z) (hr : ∀ x, rO x ≤ rO' x) :
    C2SPSpecN'' M NF Reach gid u S T Z I W Wz wzc' c2sP cT rO' :=
  fun l r π Hs σ hs d e b m en j i πj H hR hC a1 a2 a3 a4 a5 =>
    h l r π Hs σ hs d e b m en j i πj H hR hC a1 a2 ((Nat.add_le_add_left (hr _) b).trans a3) a4
      ((hw m).trans a5)

/-- More room and a larger zero-area function. -/
theorem S2CPSpecN''.mono {s2cP : Stmt} {sT : MCall M → ℕ → ℕ → ℕ}
    (h : S2CPSpecN'' M NF Reach gid u S T Z I W Wz wzc s2cP sT rO)
    (hw : ∀ m, wzc m Z ≤ wzc' m Z) (hr : ∀ x, rO x ≤ rO' x) :
    S2CPSpecN'' M NF Reach gid u S T Z I W Wz wzc' s2cP sT rO' :=
  fun l r π Hs σ hs d e b m en j i πj H hR hC a1 a2 a3 a4 a5 =>
    h l r π Hs σ hs d e b m en j i πj H hR hC a1 a2 ((Nat.add_le_add_left (hr _) b).trans a3) a4
      ((hw m).trans a5)

end Mono

/-- The separator program `sepL` prints nothing. -/
theorem sepL_noEmit : Stmt.noEmit sepL = true := by decide +kernel

/-- `sepX = sepPXS' 100000 sepL` prints nothing. -/
theorem sepX_noEmit : Stmt.noEmit sepX = true := by decide +kernel

end MfDrv

namespace Pp

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver MfDrv
  PlanarSeparator.StDart NcStep

/-- **What `fixP` must meet** (one hypothesis of `maxFlowMachine_final`): given that the MSSP call
program `msP` meets `MsspCallSpec` with the step bound `msCostS C C₀` on every map, at every
instance (the input conventions of `MfMainSpecS'`) and every word size `W`, bound `Z`, zero area
`Wz` with `100000 ≤ W`, `2 Z ≤ W`, `3 (N + 2)(Z + 1) ≤ W`: `FixPSpecN'` relative to the machine's
family `machNFT gid I (pchCall gid)` with the zero-area function `wzF`, some step function `fT`
within `(cMachS C C₀).fixRun` at the node calls, and some room `rO ≤ rF N Z` at the calls. -/
def FixHypF (fixP msP : Stmt) (Scr : ℕ → Prop) (Rm : ℕ → ℕ → ℕ → ℕ) (wzm : ℕ → ℕ → ℕ)
    (C C₀ : ℕ) (wzF rF : ℕ → ℕ → ℕ) : Prop :=
    (∀ {D' V' F' : Type} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V'] [Fintype F']
      [DecidableEq F'] (M' : CombMap D' V' F'), MsCall.MsspCallSpec M' msP Scr (MsEnc.msCostS C C₀) Rm wzm) →
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

/-- **What `c2sP` must meet** (one hypothesis of `maxFlowMachine_final`): as `FixHypF`, with
`C2SPSpecN''` and the step bound `(cMachS C C₀).c2sRun` (the MSSP premise kept for its `fixFrozen`). -/
def C2SHypF (c2sP msP : Stmt) (Scr : ℕ → Prop) (Rm : ℕ → ℕ → ℕ → ℕ) (wzm : ℕ → ℕ → ℕ)
    (C C₀ : ℕ) (wzX rX : ℕ → ℕ → ℕ) : Prop :=
    (∀ {D' V' F' : Type} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V'] [Fintype F']
      [DecidableEq F'] (M' : CombMap D' V' F'), MsCall.MsspCallSpec M' msP Scr (MsEnc.msCostS C C₀) Rm wzm) →
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
  ∃ (cT : MCall L → ℕ → ℕ → ℕ) (rO : MCall L → ℕ),
    C2SPSpecN'' L (NcStep.machNFT gid I (NsStep.pchCall gid)) Reach gid u' S' T' Z I W Wz wzX c2sP cT rO ∧
    (∀ x, Reach x → rO x ≤ rX N Z) ∧
    (∀ l r π Hs σ (h : SCond L l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN L (NcStep.machNFT gid I (NsStep.pchCall gid)) u' S' T' l r π Hs σ h).L[j]? = some πj →
      ∀ i, cT (.node l r π, Hs, σ) j i ≤ c.c2sRun (pdarts L (l.piece ∪ r.piece) Hs).card
        (nOrb (σ * revPerm L) (pdarts L (l.piece ∪ r.piece) Hs)) (psize L σ (pdarts L (l.piece ∪ r.piece) Hs)) πj.faces.card πj.k)

/-- **What `s2cP` must meet** (one hypothesis of `maxFlowMachine_final`): as `FixHypF`, with
`S2CPSpecN''` and the step bound `(cMachS C C₀).c2sRun` (the MSSP premise kept for its `fixFrozen`). -/
def S2CHypF (s2cP msP : Stmt) (Scr : ℕ → Prop) (Rm : ℕ → ℕ → ℕ → ℕ) (wzm : ℕ → ℕ → ℕ)
    (C C₀ : ℕ) (wzX rX : ℕ → ℕ → ℕ) : Prop :=
    (∀ {D' V' F' : Type} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V'] [Fintype F']
      [DecidableEq F'] (M' : CombMap D' V' F'), MsCall.MsspCallSpec M' msP Scr (MsEnc.msCostS C C₀) Rm wzm) →
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
  ∃ (cT : MCall L → ℕ → ℕ → ℕ) (rO : MCall L → ℕ),
    S2CPSpecN'' L (NcStep.machNFT gid I (NsStep.pchCall gid)) Reach gid u' S' T' Z I W Wz wzX s2cP cT rO ∧
    (∀ x, Reach x → rO x ≤ rX N Z) ∧
    (∀ l r π Hs σ (h : SCond L l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN L (NcStep.machNFT gid I (NsStep.pchCall gid)) u' S' T' l r π Hs σ h).L[j]? = some πj →
      ∀ i, cT (.node l r π, Hs, σ) j i ≤ c.c2sRun (pdarts L (l.piece ∪ r.piece) Hs).card
        (nOrb (σ * revPerm L) (pdarts L (l.piece ∪ r.piece) Hs)) (psize L σ (pdarts L (l.piece ∪ r.piece) Hs)) πj.faces.card πj.k)

/-- **The room per call of the final assembly**: the separator's `sRL N N N` and `segR`'s
`1 + sRX N N N`, the counts `#holes + 1 ≤ N + 1` and the push-back's `40 N + 10`, and the
programs' rooms `r (N + Z + 1)^q`. -/
def rowR (r q N Z : ℕ) : ℕ := sRL N N N + 1 + sRX N N N + 41 * N + 11 + r * (N + Z + 1) ^ q

theorem rowR_mono (r q : ℕ) : ∀ N N' Z Z', N ≤ N' → Z ≤ Z' → rowR r q N Z ≤ rowR r q N' Z' := by
  intro N N' Z Z' hN hZ
  have h1 := sRL_mono hN hN hN
  have h2 : r * (N + Z + 1) ^ q ≤ r * (N' + Z' + 1) ^ q :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) q)
  unfold rowR sRX smRS' smR; omega

/-- **The room per call is polynomial.** -/
theorem rowR_le (r q N Z : ℕ) : rowR r q N Z ≤ (r + 3000000) * (N + Z + 1) ^ (q + 2) := by
  unfold rowR sRX sRL smRS' smR
  have e := encB'_eq (223 * N + 84)
  obtain ⟨X, hX⟩ : ∃ X, X = N + Z + 1 := ⟨_, rfl⟩
  rw [← hX]
  have hX1 : 1 ≤ X := by omega
  have hl := Nat.log_le_self 2 (2 * (223 * N + 84))
  generalize Nat.log 2 (2 * (223 * N + 84)) = lg2 at e hl
  generalize encB' (223 * N + 84) = E at e
  have h1 : (lg2 + 2) * (2 * (223 * N + 84)) ≤ (614 * X + 2) * (614 * X) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hXX1 : X ≤ X * X := Nat.le_mul_of_pos_left X hX1
  have e2 : (614 * X + 2) * (614 * X) = 376996 * (X * X) + 1228 * X := by ring
  have hXX : X * X ≤ X ^ (q + 2) := by
    rw [← pow_two]; exact Nat.pow_le_pow_right hX1 (by omega)
  have hrq : r * X ^ q ≤ r * X ^ (q + 2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
  have e3 : (r + 3000000) * X ^ (q + 2) = r * X ^ (q + 2) + 3000000 * X ^ (q + 2) := by ring
  omega

set_option maxHeartbeats 4000000 in
/-- **The hypothesis `MfMainSpecS''` from one hypothesis per remaining program** (see the module
docstring): the separator is `sepL` (with `sepX = sepPXS' 100000 sepL`), the node-step
programs `fixP`, `c2sP`, `s2cP` meet `FixHypF`, `C2SHypF`, `S2CHypF` for an MSSP call program `msP`
meeting `MsspCallSpec` at `msCostS C C₀` on every map. Room `rowR r q`, zero area
`a (N + Z + 1)^p`. -/
theorem mfMainSpecS''_final {fixP c2sP s2cP msP : Stmt} {Scr : ℕ → Prop}
    {Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ} {C C₀ : ℕ} (hC : 3200000 ≤ C)
    {wzF wzC wzS rF rC rS : ℕ → ℕ → ℕ} {a p r q : ℕ}
    (hMS : ∀ {D' V' F' : Type} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
      [Fintype F'] [DecidableEq F'] (M' : CombMap D' V' F'),
      MsCall.MsspCallSpec M' msP Scr (MsEnc.msCostS C C₀) Rm wzm)
    (hfix : FixHypF fixP msP Scr Rm wzm C C₀ wzF rF)
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
  obtain ⟨fT, rOF, hfx, hrF, hfc⟩ := hfix hMS M hM hrot hface ep hep hu hST hne en d₀ hN hsurj hgid
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
theorem maxFlowMachine_final {fixP c2sP s2cP msEnc : Stmt} {C C₀ : ℕ} (hC : 3200000 ≤ C)
    {EScr : ℕ → Prop} {Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    {wzF wzC wzS rF rC rS : ℕ → ℕ → ℕ} {a p r q : ℕ}
    (hE : ∀ {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
      [DecidableEq F] (M : CombMap D V F), MsCall.MsEncSpec' M msEnc EScr MsEnc.msEncCost
        (fun m k _ => MsEnc.KCf m k) (fun m _ _ => MsEnc.ZCf m) Rm wzm)
    (hfix : FixHypF fixP (MsCall.msspCall' msEnc) (fun x => EScr x ∨ MsCall.msScr x) Rm wzm C C₀
      wzF rF)
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
    (mfMainSpecS''_final hC (fun M' => MsEnc.msspCall'_cMachS C C₀ (hE M')) hfix hc2s hs2c hwz hr)
    (by omega) sepL_noEmit sepX_noEmit hE3 hE4 hE5 (rowR_mono r q) (rowR_le r q) (fun N Z => le_rfl)

end Pp

end BKMNW

end PlanarFlow
