module

public import PlanarFlow.BKMNW.NrRet
public import PlanarFlow.BKMNW.NcChs

/-!
# `retP`, `frmP` meet the step specifications (with the start-vertex layout)

`RetPSpecN`/`FrmPSpecN` (`NpStep.lean`) give the programs only `SegsAt` (the darts of the parts),
which does not determine a part with no dart; and they do not give the antisymmetry of the input
flow, without which the flow array cannot be read back as words of the push-back. Here:

* **`RetPSpecNV`**, **`FrmPSpecNV`**: `RetPSpecN`/`FrmPSpecN` with `SegsAtV` (the parts with their
  start vertex) in place of `SegsAt`, and the hypothesis that the input flow is antisymmetric;
* `nrPassCost_mono`, `pchCost_mono`, `Lay.card_eq`;
* **`retP_specNV`**, **`frmP_specNV`**: `retP`, `frmP` meet them relative to
  `machNF gid I₀ chs (pchCall gid)` (any `chs`), with costs
  `rtNV x = retCost m nf`, `fmNV x = frmCost m nf` (`m = #darts`, `nf = #faces` of the piece
  map), any room `rO x ≥ 40 m + 10`, and the word bound `3 N Z + 3 Z + 1 ≤ W` for `N` bounding
  the numbers of darts of the calls of `Reach`.
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

lemma osCost_mono {M N N' : ℕ} (h : N ≤ N') : osCost M N ≤ osCost M N' := by
  unfold osCost; omega

lemma nrPassCost_mono {m n n' : ℕ} (h : n ≤ n') : nrPassCost m n ≤ nrPassCost m n' := by
  unfold nrPassCost
  have h1 := Heap.lg_mono (show 2 * n ≤ 2 * n' by omega)
  have h2 := osCost_mono (M := m) h
  have h3 : n * (23 * Heap.lg (2 * n) + 21) ≤ n' * (23 * Heap.lg (2 * n') + 21) :=
    Nat.mul_le_mul h (by omega)
  have h4 : (13 * Heap.lg (2 * n) + 20) * m ≤ (13 * Heap.lg (2 * n') + 20) * m :=
    Nat.mul_le_mul_right _ (by omega)
  omega

lemma frmCost_mono {m n n' : ℕ} (h : n ≤ n') : frmCost m n ≤ frmCost m n' := by
  have := nrPassCost_mono (m := m) h
  unfold frmCost fcCost pchCost; omega

lemma retCost_mono {m n n' : ℕ} (h : n ≤ n') : retCost m n ≤ retCost m n' := by
  have := nrPassCost_mono (m := m) h
  unfold retCost fcCost pchCost; omega

namespace MfDrv

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- The number of darts of the frame is the number of darts of the piece. -/
lemma Lay.card_eq {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) : (pdarts M x.1.piece x.2.1).card = m := by
  classical
  have e : (range m).image en = pdarts M x.1.piece x.2.1 := by
    ext y
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hL.en_mem i hi
    · intro hy; obtain ⟨i, hi, rfl⟩ := hL.en_surj y hy; exact ⟨i, hi, rfl⟩
  rw [← e, card_image_of_injOn (fun i hi j hj h => hL.en_inj (mem_range.1 hi) (mem_range.1 hj) h),
    card_range]

/-- The number of faces of the piece map of a call. -/
noncomputable def nfOf (x : MCall M) : ℕ := nOrb (x.2.2 * revPerm M) (pdarts M x.1.piece x.2.1)

/-- **The costs of the push-backs at a call**: `retCost`/`frmCost` of the darts and faces. -/
noncomputable def rtNV (x : MCall M) (j : ℕ) : ℕ :=
  retCost (pdarts M x.1.piece x.2.1).card (nfOf x)

noncomputable def fmNV (x : MCall M) (j : ℕ) : ℕ :=
  frmCost (pdarts M x.1.piece x.2.1).card (nfOf x)

variable (M) in
/-- **The push-back of the excess to the sources** on the part `j`, with the start vertices of
the parts (`SegsAtV`) and an antisymmetric input. -/
def RetPSpecNV (NF : NFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (retP : Stmt) (rtT : MCall M → ℕ → ℕ)
    (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j : ℕ) (πj : SPath (pmap h.1)),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d →
    (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj →
    (pmap h.1).IsAntisymm ((xCtxN M NF u S T l r π Hs σ h).hole j πj
      ((xCtxN M NF u S T l r π Hs σ h).holes j).length) →
    FlowProg M gid u S T Z I W retP (.node l r π, Hs, σ) m en d e b
      (fun c => (c.nreg 6800 = j ∧ MemZ Wz c) ∧ SegsAtV M en m π e b c)
      ((xCtxN M NF u S T l r π Hs σ h).hole j πj ((xCtxN M NF u S T l r π Hs σ h).holes j).length)
      ((xCtxN M NF u S T l r π Hs σ h).ret j πj) (rtT (.node l r π, Hs, σ) j)

variable (M) in
/-- **The push-back from the sinks** on the part `j`, with the start vertices of the parts
(`SegsAtV`) and an antisymmetric input. -/
def FrmPSpecNV (NF : NFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (frmP : Stmt) (fmT : MCall M → ℕ → ℕ)
    (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j : ℕ) (πj : SPath (pmap h.1)),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d →
    (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj →
    (pmap h.1).IsAntisymm ((xCtxN M NF u S T l r π Hs σ h).ret j πj) →
    FlowProg M gid u S T Z I W frmP (.node l r π, Hs, σ) m en d e b
      (fun c => (c.nreg 6800 = j ∧ MemZ Wz c) ∧ SegsAtV M en m π e b c)
      ((xCtxN M NF u S T l r π Hs σ h).ret j πj)
      ((xCtxN M NF u S T l r π Hs σ h).O.frm (xCtxN M NF u S T l r π Hs σ h).U
        ((xCtxN M NF u S T l r π Hs σ h).ret j πj) (xCtxN M NF u S T l r π Hs σ h).T
        (negSet (pmap h.1) ((xCtxN M NF u S T l r π Hs σ h).ret j πj) πj.verts))
      (fmT (.node l r π, Hs, σ) j)

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **`frmP` meets `FrmPSpecNV`** for the machine's subroutines (any s-t flow choices). -/
theorem frmP_specNV {I₀ I : Input} {chs : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) →
      STFlow.StChoice (pmap h)}
    {Reach : MCall M → Prop} {Wz N : ℕ} {rO : MCall M → ℕ} (hST : Disjoint S T)
    (hN : ∀ x, Reach x → (pdarts M x.1.piece x.2.1).card ≤ N)
    (hWZ : 3 * (N * Z) + 3 * Z + 1 ≤ W)
    (hrO : ∀ x, 40 * (pdarts M x.1.piece x.2.1).card + 10 ≤ rO x) :
    FrmPSpecNV M (NsStep.machNF gid I₀ chs (NsStep.pchCall gid)) Reach gid u S T Z I W Wz frmP
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
/-- **`retP` meets `RetPSpecNV`** for the machine's subroutines (any s-t flow choices). -/
theorem retP_specNV {I₀ I : Input} {chs : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) →
      STFlow.StChoice (pmap h)}
    {Reach : MCall M → Prop} {Wz N : ℕ} {rO : MCall M → ℕ}
    (hN : ∀ x, Reach x → (pdarts M x.1.piece x.2.1).card ≤ N)
    (hWZ : 3 * (N * Z) + 3 * Z + 1 ≤ W)
    (hrO : ∀ x, 40 * (pdarts M x.1.piece x.2.1).card + 10 ≤ rO x) :
    RetPSpecNV M (NsStep.machNF gid I₀ chs (NsStep.pchCall gid)) Reach gid u S T Z I W Wz retP
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
