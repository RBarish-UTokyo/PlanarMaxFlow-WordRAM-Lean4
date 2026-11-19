module

public import PlanarFlow.BKMNW.NcPbTop
public import PlanarFlow.BKMNW.NcPbS
public import PlanarFlow.BKMNW.NcCostX
public import PlanarFlow.BKMNW.ThFinal

/-!
# `C2SHypF` and `S2CHypF` from a `fixFrozen` program

The push-back parameter is now a program (`pbP`, `pbP_spec'`); the `fixFrozen` parameter `fzP` is
not yet written. **`FzHypF fzP msP Scr Rm wzm C C₀ wzz rFz`** states what `fzP` must meet, in the
form of `FixHypF`: given the MSSP call program's specification on every map, at every
instance of the final assembly and every `I W Z Wz` with `100000 ≤ W`, `2 Z ≤ W`,
`3 (N + 2)(Z + 1) ≤ W`: `FzPSpec'` (`NcPb.lean`, zero area `wzz m Z`) with some steps `fzT`
within `(cMachS C C₀).fixRun m xf k (3 · psize)` at the reachable node calls and some room
`fzR m ≤ rFz N Z` (`m ≤ N`).

* **`c2sHypF_of_fz`**: `FzHypF fzP … wzz rFz → 1 ≤ C → Pp.C2SHypF (c2sP fzP pbP) msP Scr Rm wzm C C₀
  (fun m Z => wzc m Z + wzz m Z) (c2sRC rFz)`;
* **`s2cHypF_of_fz`**: the same for `Pp.S2CHypF (s2cP fzP pbP)`;
* **`c2sRC rFz N Z = 28 N + 10 + stRm N + rFz N Z + pbRZ Z N + 6 Z`** (the room per call:
  `c2sRoom` with `pbRZ`), `c2sRC_le` (`≤ (rF₀ + 4·10⁹ + 100)(N + Z + 1)^(q + 2)` when
  `rFz N Z ≤ rF₀ (N + Z + 1)^q`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver MfDrv
  PlanarSeparator.StDart NcStep

/-- **What the `fixFrozen` program `fzP` must meet** (see the module docstring). -/
def FzHypF (fzP msP : Stmt) (Scr : ℕ → Prop) (Rm : ℕ → ℕ → ℕ → ℕ) (wzm : ℕ → ℕ → ℕ)
    (C C₀ : ℕ) (wzz rFz : ℕ → ℕ → ℕ) : Prop :=
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
  ∃ (fzT : MCall L → ℕ → ℕ) (fzR : ℕ → ℕ),
    FzPSpec' L gid u' S' T' Z I W wzz fzP fzT fzR ∧
    (∀ m, m ≤ N → fzR m ≤ rFz N Z) ∧
    (∀ l r π Hs σ (h : SCond L l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN L (NcStep.machNFT gid I (NsStep.pchCall gid)) u' S' T' l r π Hs σ h).L[j]? = some πj →
      fzT (.node l r π, Hs, σ) j ≤ c.fixRun (pdarts L (l.piece ∪ r.piece) Hs).card πj.faces.card
        πj.k (3 * psize L σ (pdarts L (l.piece ∪ r.piece) Hs)))

/-- **The room per call of `c2sP`/`s2cP`** with `pbP` and a `fixFrozen` program of room `rFz`. -/
def c2sRC (rFz : ℕ → ℕ → ℕ) (N Z : ℕ) : ℕ := 28 * N + 10 + stRm N + rFz N Z + pbRZ Z N + 6 * Z

lemma stRm_mono {m N : ℕ} (h : m ≤ N) : stRm m ≤ stRm N := by
  unfold stRm; have := Nat.mul_le_mul h h; omega

lemma pbRZ_mono {Z m N : ℕ} (h : m ≤ N) : pbRZ Z m ≤ pbRZ Z N := by
  unfold pbRZ; have := Nat.mul_le_mul_right Z h; omega

/-- The room of a call with at most `N` darts. -/
lemma c2sRoom_le {fzR : ℕ → ℕ} {rFz : ℕ → ℕ → ℕ} {m N Z : ℕ} (h : m ≤ N)
    (hR : ∀ m, m ≤ N → fzR m ≤ rFz N Z) : c2sRoom fzR (pbRZ Z) m Z ≤ c2sRC rFz N Z := by
  unfold c2sRoom c2sRC
  have := stRm_mono h; have := pbRZ_mono (Z := Z) h; have := hR m h
  omega

/-- **The room per call is polynomial** when `rFz` is. -/
lemma c2sRC_le {rFz : ℕ → ℕ → ℕ} {rF₀ q : ℕ} (hr : ∀ N Z, rFz N Z ≤ rF₀ * (N + Z + 1) ^ q)
    (N Z : ℕ) : c2sRC rFz N Z ≤ (rF₀ + 4000000100) * (N + Z + 1) ^ (q + 2) := by
  unfold c2sRC stRm pbRZ
  set X := N + Z + 1 with hX
  have h1 : 1 ≤ X := by omega
  have hp : X ^ 2 ≤ X ^ (q + 2) := Nat.pow_le_pow_right h1 (by omega)
  have hq : X ^ q ≤ X ^ (q + 2) := Nat.pow_le_pow_right h1 (by omega)
  have hNX : N * N ≤ X ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
  have hNZ : N * Z ≤ X ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
  have hX2 : X ≤ X ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_left _ h1
  have e1 : rFz N Z ≤ rF₀ * X ^ q := hr N Z
  have e2 : rF₀ * X ^ q ≤ rF₀ * X ^ (q + 2) := Nat.mul_le_mul_left _ hq
  have e3 : (rF₀ + 4000000100) * X ^ (q + 2) = rF₀ * X ^ (q + 2) + 4000000100 * X ^ (q + 2) := by
    ring
  rw [e3]
  omega

/-- **`c2sP fzP pbP` meets `C2SHypF`**, given a `fixFrozen` program meeting `FzHypF`. -/
theorem c2sHypF_of_fz {fzP msP : Stmt} {Scr : ℕ → Prop} {Rm : ℕ → ℕ → ℕ → ℕ}
    {wzm : ℕ → ℕ → ℕ} {C C₀ : ℕ} {wzz rFz : ℕ → ℕ → ℕ}
    (hfz : FzHypF fzP msP Scr Rm wzm C C₀ wzz rFz) (hC : 1 ≤ C) :
    C2SHypF (c2sP fzP pbP) msP Scr Rm wzm C C₀ (fun m Z => wzc m Z + wzz m Z) (c2sRC rFz) := by
  intro hMS D V F _ _ _ _ _ _ M hM hrot hft ep hep u hu S T hST hne N en d₀ gid ν hN hsurj hgid
    hν hQ hTS L pc sc gS gH τ u' S' T' Reach c I W Z Wz hW1 hW2 hW3
  obtain ⟨fzT, fzR, hF, hR, hT⟩ := hfz hMS M hM hrot hft ep hep hu hST hne en d₀ hN hsurj hgid
    hν hQ hTS (I := I) (W := W) (Z := Z) (Wz := Wz) hW1 hW2 hW3
  have hginj : Injective gid := by
    intro y₁ y₂ e
    obtain ⟨i₁, hi₁, rfl⟩ := hsurj y₁
    obtain ⟨i₂, hi₂, rfl⟩ := hsurj y₂
    rw [hgid i₁ hi₁, hgid i₂ hi₂] at e
    rw [e]
  have hu₁ : ∀ y : SDart (nlDarts M), 0 ≤ (fun y : SDart (nlDarts M) => u y.1) y :=
    fun y => hu y.1
  have hu' : ∀ d, 0 ≤ u' d :=
    pendCap_nonneg (triCap_nonneg hu₁) _ _ (sum_nonneg fun x _ => triCap_nonneg hu₁ x)
  refine ⟨c2sT fzT pbTN, fun x => c2sRoom fzR (pbRZ Z) (pdarts L x.1.piece x.2.1).card Z,
    c2sP_spec' hF (pbP_spec' gid u' S' T' Z I W) hginj hu' (fun x => le_rfl),
    fun x _ => c2sRoom_le ((card_le_univ _).trans hN.le) hR, ?_⟩
  intro l r π Hs σ h j πj hx hj i
  obtain ⟨y, -⟩ := Quotient.exists_rep (πj.p 0)
  have hm : 1 ≤ (pdarts L (l.piece ∪ r.piece) Hs).card := Finset.card_pos.2 ⟨y.1, y.2⟩
  have hps : (pdarts L (l.piece ∪ r.piece) Hs).card ≤
      psize L σ (pdarts L (l.piece ∪ r.piece) Hs) := by unfold psize; omega
  exact c2sT_le C C₀ _ j i hm (hT l r π Hs σ h j πj hx hj) (pbTN_le C C₀ _ j hC hm hps)

/-- **`s2cP fzP pbP` meets `S2CHypF`**, given a `fixFrozen` program meeting `FzHypF`. -/
theorem s2cHypF_of_fz {fzP msP : Stmt} {Scr : ℕ → Prop} {Rm : ℕ → ℕ → ℕ → ℕ}
    {wzm : ℕ → ℕ → ℕ} {C C₀ : ℕ} {wzz rFz : ℕ → ℕ → ℕ}
    (hfz : FzHypF fzP msP Scr Rm wzm C C₀ wzz rFz) (hC : 1 ≤ C) :
    S2CHypF (s2cP fzP pbP) msP Scr Rm wzm C C₀ (fun m Z => wzc m Z + wzz m Z) (c2sRC rFz) := by
  intro hMS D V F _ _ _ _ _ _ M hM hrot hft ep hep u hu S T hST hne N en d₀ gid ν hN hsurj hgid
    hν hQ hTS L pc sc gS gH τ u' S' T' Reach c I W Z Wz hW1 hW2 hW3
  obtain ⟨fzT, fzR, hF, hR, hT⟩ := hfz hMS M hM hrot hft ep hep hu hST hne en d₀ hN hsurj hgid
    hν hQ hTS (I := I) (W := W) (Z := Z) (Wz := Wz) hW1 hW2 hW3
  have hginj : Injective gid := by
    intro y₁ y₂ e
    obtain ⟨i₁, hi₁, rfl⟩ := hsurj y₁
    obtain ⟨i₂, hi₂, rfl⟩ := hsurj y₂
    rw [hgid i₁ hi₁, hgid i₂ hi₂] at e
    rw [e]
  have hu₁ : ∀ y : SDart (nlDarts M), 0 ≤ (fun y : SDart (nlDarts M) => u y.1) y :=
    fun y => hu y.1
  have hu' : ∀ d, 0 ≤ u' d :=
    pendCap_nonneg (triCap_nonneg hu₁) _ _ (sum_nonneg fun x _ => triCap_nonneg hu₁ x)
  refine ⟨s2cT fzT pbTN, fun x => c2sRoom fzR (pbRZ Z) (pdarts L x.1.piece x.2.1).card Z,
    s2cP_spec' hF (pbP_spec' gid u' S' T' Z I W) hginj hu' (fun x => le_rfl),
    fun x _ => c2sRoom_le ((card_le_univ _).trans hN.le) hR, ?_⟩
  intro l r π Hs σ h j πj hx hj i
  obtain ⟨y, -⟩ := Quotient.exists_rep (πj.p 0)
  have hm : 1 ≤ (pdarts L (l.piece ∪ r.piece) Hs).card := Finset.card_pos.2 ⟨y.1, y.2⟩
  have hps : (pdarts L (l.piece ∪ r.piece) Hs).card ≤
      psize L σ (pdarts L (l.piece ∪ r.piece) Hs) := by unfold psize; omega
  exact s2cT_le C C₀ _ j i hm (hT l r π Hs σ h j πj hx hj) (pbTN_le C C₀ _ j hC hm hps)

end Pp

end BKMNW

end PlanarFlow
