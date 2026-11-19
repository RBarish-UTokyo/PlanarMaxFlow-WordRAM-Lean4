module

public import PlanarFlow.BKMNW.ThChsE
public import PlanarFlow.BKMNW.NrCost

/-!
# `retP`, `frmP` meet their specifications relative to `machNFT`

`frmP_specNV`, `retP_specNV` (`NrSpec.lean`) are stated relative to
`machNF gid I₀ chs (pchCall gid)` for a family `chs` of s-t flow choices, a type with no element
(`NsStep.chs_isEmpty`). The same proofs (copied; they do not use the s-t flow) give them relative
to the family that exists, `NcStep.machNFT gid I₀ (pchCall gid)`:

* **`retP_specNVT`**, **`frmP_specNVT`**: costs `rtNV`, `fmNV`, any room `rO x ≥ 40 m + 10`, word
  bound `3 N Z + 3 Z + 1 ≤ W` with `N` bounding the darts of the calls of `Reach`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv Orbit NegSSSP

namespace MfDrv

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **`frmP` meets `FrmPSpecNV`** for the machine's subroutines `machNFT`. -/
theorem frmP_specNVT {I₀ I : Input} {Reach : MCall M → Prop} {Wz N : ℕ} {rO : MCall M → ℕ} (hST : Disjoint S T)
    (hN : ∀ x, Reach x → (pdarts M x.1.piece x.2.1).card ≤ N)
    (hWZ : 3 * (N * Z) + 3 * Z + 1 ≤ W)
    (hrO : ∀ x, 40 * (pdarts M x.1.piece x.2.1).card + 10 ≤ rO x) :
    FrmPSpecNV M (NcStep.machNFT gid I₀ (NsStep.pchCall gid)) Reach gid u S T Z I W Wz frmP
      fmNV rO := by
  intro l r π Hs σ h d e b m en j πj hR hok hde heb hbW hWz hj hanti c hpre hL hfl
    hc r3004 r3005 r3006
  obtain ⟨⟨r6800, -⟩, hS⟩ := hpre
  obtain ⟨hj', hv⟩ := xCtxN_L_verts _ u S T h hj
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (hS.2.2 j hj').1
  have hpl := (NcStep.lay_plane h.1 hok hL hm).1
  have hcard := hL.card_eq
  have hmN : m ≤ N := by rw [← hcard]; exact hN _ hR
  have hmZ : m * Z ≤ N * Z := Nat.mul_le_mul_right _ hmN
  have hP : Disjoint (π.segs[j]).verts (hunion Hs) := (h.2 _ (List.getElem_mem hj')).2.2
  have hTh : Disjoint T (hunion Hs) := hok.2.2.2.2.2.1
  have hrO' := hrO (.node l r π, Hs, σ)
  rw [hcard] at hrO'
  obtain ⟨c', t, ex, ht, FL, k, sr, rr, rm, o⟩ := frmP_exec (gid := gid) c hc hL h.1 hpl hm hST
    hTh hanti hfl r3004 r3006 hS r6800 hj' hP hde heb (by clear * - hbW hrO'; omega)
    (by clear * - hWZ hmZ; omega)
  refine ⟨c', t, ex, ht.trans ?_, sr, fun a ha hnf => ⟨k a (by clear * - hnf; omega) (Or.inl ha),
    by rw [rm]⟩, o, ?_⟩
  · unfold fmNV nfOf
    rw [hcard, ← card_sFace]
    exact frmCost_mono (hL.rcnt_le_card h.1 hm hL.faceArr_nx)
  · rw [hv]; exact FL

set_option maxHeartbeats 4000000 in
/-- **`retP` meets `RetPSpecNV`** for the machine's subroutines `machNFT`. -/
theorem retP_specNVT {I₀ I : Input} {Reach : MCall M → Prop} {Wz N : ℕ} {rO : MCall M → ℕ}
    (hN : ∀ x, Reach x → (pdarts M x.1.piece x.2.1).card ≤ N)
    (hWZ : 3 * (N * Z) + 3 * Z + 1 ≤ W)
    (hrO : ∀ x, 40 * (pdarts M x.1.piece x.2.1).card + 10 ≤ rO x) :
    RetPSpecNV M (NcStep.machNFT gid I₀ (NsStep.pchCall gid)) Reach gid u S T Z I W Wz retP
      rtNV rO := by
  intro l r π Hs σ h d e b m en j πj hR hok hde heb hbW hWz hj hanti c hpre hL hfl
    hc r3004 r3005 r3006
  obtain ⟨⟨r6800, -⟩, hS⟩ := hpre
  obtain ⟨hj', hv⟩ := xCtxN_L_verts _ u S T h hj
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (hS.2.2 j hj').1
  have hpl := (NcStep.lay_plane h.1 hok hL hm).1
  have hcard := hL.card_eq
  have hmN : m ≤ N := by rw [← hcard]; exact hN _ hR
  have hmZ : m * Z ≤ N * Z := Nat.mul_le_mul_right _ hmN
  have hP : Disjoint (π.segs[j]).verts (hunion Hs) := (h.2 _ (List.getElem_mem hj')).2.2
  have hSh : Disjoint S (hunion Hs) := hok.2.2.2.2.1
  have hrO' := hrO (.node l r π, Hs, σ)
  rw [hcard] at hrO'
  obtain ⟨c', t, ex, ht, FL, k, sr, rr, rm, o⟩ := retP_exec (gid := gid) c hc hL h.1 hpl hm
    hSh hanti hfl r3004 r3006 hS r6800 hj' hP hde heb (by clear * - hbW hrO'; omega)
    (by clear * - hWZ hmZ; omega)
  refine ⟨c', t, ex, ht.trans ?_, sr, fun a ha hnf => ⟨k a (by clear * - hnf; omega) (Or.inl ha),
    by rw [rm]⟩, o, ?_⟩
  · unfold rtNV nfOf
    rw [hcard, ← card_sFace]
    exact retCost_mono (hL.rcnt_le_card h.1 hm hL.faceArr_nx)
  · show FLHas Z m d en c'.nmem (retG (pmap h.1) (NsStep.pchCall gid (.node l r π, Hs, σ) h.1) _
      (posSet (pmap h.1) _ πj.verts) _)
    rw [hv]; exact FL

end MfDrv

end BKMNW

end PlanarFlow
