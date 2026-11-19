module

public import PlanarFlow.BKMNW.Nf7fC

/-!
# `fixP7` meets `FixPSpecN''` at the node calls

* **`fx7fT`**: the steps of `fixP7` at a call and a part: `(cMachS C C₀).fixRun m #πj.faces πj.k
  (psize)` for the part `πj = L[j]` of a node call (`0` elsewhere); `fx7fT_eq`;
* **`fixP7_specN''`**: from `FixPosW`, `FixZeroW` (the per-address statements), an MSSP call program meeting
  `MsspCallSpec` on the piece maps with scratch below `9300` and a step bound `cost` within the
  `mssp` field (`q ≤ 2k`), and `200000 ≤ C`: `fixP7 msP` meets
  `FixPSpecN'' M (machNFT gid I pch) Reach … (wzF7 wzm) (fixP7 msP) fx7fT (rOF7 C C₀ Rm #pdarts Z)`
  for every family `pch` and every `Reach`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap OrbLab NegSSSP NegSSSP.Frame MfDrv NsStep SPath
  WordRAM WordRAM.Machine WordRAM.Programs

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

variable (M : CombMap D V F) in
open Classical in
/-- **The steps of `fixP7` at a node call and a part.** -/
noncomputable def fx7fT (NF : NFam M) (u : D → ℤ) (S T : Finset V) (C C₀ : ℕ) :
    MCall M → ℕ → ℕ
  | (.node l r π, Hs, σ), j =>
    if h : SCond M l r π Hs σ then
      match (xCtxN M NF u S T l r π Hs σ h).L[j]? with
      | some πj => (cMachS C C₀).fixRun (pdarts M (l.piece ∪ r.piece) Hs).card πj.faces.card πj.k
          (psize M σ (pdarts M (l.piece ∪ r.piece) Hs))
      | none => 0
    else 0
  | _, _ => 0

variable {M : CombMap D V F}

lemma fx7fT_eq (NF : NFam M) (u : D → ℤ) (S T : Finset V) (C C₀ : ℕ) {l r : ADec M}
    {π : HSep M} {Hs : List (Finset V)} {σ : Perm D} (h : SCond M l r π Hs σ) {j : ℕ}
    {πj : SPath (pmap h.1)} (hj : (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj) :
    fx7fT M NF u S T C C₀ (.node l r π, Hs, σ) j = (cMachS C C₀).fixRun
      (pdarts M (l.piece ∪ r.piece) Hs).card πj.faces.card πj.k
      (psize M σ (pdarts M (l.piece ∪ r.piece) Hs)) := by
  simp only [fx7fT, h, ↓reduceDIte]
  split
  · next πj' e => rw [hj] at e; cases e; rfl
  · next e => rw [hj] at e; cases e

set_option maxHeartbeats 8000000 in
/-- **`fixP7 msP` meets `FixPSpecN''`** (see the module docstring). -/
theorem fixP7_specN'' (hPW : FixPosW.{w}) (hZW : FixZeroW.{w}) {C C₀ : ℕ} (hC : 200000 ≤ C)
    {msP : Stmt} {Scr : ℕ → Prop} {cost Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    {M : CombMap D V F}
    (hMS : ∀ (x : MCall M) (hP : PieceInv M x.1.piece x.2.1 x.2.2),
      MsCall.MsspCallSpec (pmap hP) msP Scr cost Rm wzm)
    (hScr : ∀ r, Scr r → r < 9300)
    (hcost : ∀ m k q, 1 ≤ m → q ≤ 2 * k →
      cost m k q + 200 * k ^ 2 + 2000 * k + 2000 ≤ (cMachS C C₀).mssp m k)
    {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {I : Input} {W Wz : ℕ}
    (pch : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) →
      PushFn (Orbit.SDart (pdarts M x.1.piece x.2.1)) (Orbit.SVert x.2.2 (pdarts M x.1.piece x.2.1)))
    (Reach : MCall M → Prop) :
    FixPSpecN'' M (NcStep.machNFT gid I pch) Reach gid u S T Z I W Wz (wzF7 wzm) (fixP7 msP)
      (fx7fT M (NcStep.machNFT gid I pch) u S T C C₀)
      (fun x => rOF7 C C₀ Rm (pdarts M x.1.piece x.2.1).card Z) := by
  intro l r π Hs σ h d e b m en j πj hReach hok hde heb hbW hWzd hwz hj hps c ⟨⟨r00, hMZ⟩, hSA⟩
    hl hFL hc r04 r05 r06
  obtain ⟨hpl, hrot, hface, hne, hj', hkk, hdd⟩ := fx7f_call h hok hj
  have hm : 0 < m := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨i, hi, -⟩ := hl.en_surj y hy
    omega
  have hmc : (pdarts M (l.piece ∪ r.piece) Hs).card = m := (hl.card).symm
  beta_reduce at hbW
  rw [← hl.card] at hbW
  have hSO : SegsOut M en m π e b (c.nreg 6807) c.nmem := SegsOut'.toSegsOut hSA
  have hkq : πj.k = (callIn d m (c.nreg 6807) π j Z c.nmem).k := by rw [callIn_k hj']; exact hkk
  obtain ⟨-, -, hns, -, hkn, -⟩ := callIn_pre hl hSO hj' (Z := Z)
  have htop := (callIn_top hSO hj' (d := d) (Z := Z)).2
  have hfsz : MfDrv.fsz m = 4 + 7 * m := rfl
  have hnsl : (callIn d m (c.nreg 6807) π j Z c.nmem).ns = π.segs.length := rfl
  obtain ⟨c', t, s, ex, hs, hQ⟩ := fixP7_branch (I := I) (W := W) msP c hc rfl r00 hns hkn
    (by omega)
    (fun c' t => t + 9 ≤ fx7fT M (NcStep.machNFT gid I pch) u S T C C₀ (.node l r π, Hs, σ) j ∧
      SRegKeep c c' ∧
      (∀ a, a < b → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      FLHas Z m d en c'.nmem ((xCtxN M (NcStep.machNFT gid I pch) u S T l r π Hs σ h).O.fix
        (xCtxN M (NcStep.machNFT gid I pch) u S T l r π Hs σ h).U
        ((xCtxN M (NcStep.machNFT gid I pch) u S T l r π Hs σ h).seg j) πj))
    (fun hk0 c₁ hc₁ hmem hreg hrr hrm hout => by
      have hk0' : 0 < πj.k := by rw [hkq]; exact hk0
      have hl1 : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₁.nmem := by rw [hmem]; exact hl
      have hSO1 : SegsOut M en m π e b (c₁.nreg 6807) c₁.nmem := by
        rw [hmem, hreg 6807 (by omega)]; exact hSO
      have hkq1 : πj.k = (callIn d m (c₁.nreg 6807) π j Z c₁.nmem).k := by
        rw [hmem, hreg 6807 (by omega)]; exact hkq
      have hFL1 : FLHas Z m d en c₁.nmem ((xCtxN M (NcStep.machNFT gid I pch) u S T l r π Hs σ h).seg j) := by
        rw [hmem]; exact hFL
      obtain ⟨c', t, ex, ht, hK, hkeep, ho, -, hF⟩ :=
        fx7f_pos hPW C C₀ hC h.1 (hMS (.node l r π, Hs, σ) h.1) hScr hpl hrot hface I c₁ hc₁ hl1 hm hSO1 hj' hkq1
          hdd hk0' hps hFL1 (by rw [hreg 3004 (by omega)]; exact r04)
          (by rw [hreg 3006 (by omega)]; exact r06) rfl (by rw [hreg 6800 (by omega)]; exact r00)
          (fun a ha => by rw [hmem]; exact hMZ a ha) hWzd (by unfold MfDrv.fsz at hde; omega)
          (Nat.le_add_right b 5) (by unfold MfDrv.fsz at hde; omega) (by omega) hwz
      have hbF : (callIn d m (c₁.nreg 6807) π j Z c₁.nmem).cw.cnt = πj.faces.card :=
        mkX_card h.1 hl1 hm hrot hSO1 hj' hkq1 hdd hk0'
      have hb1 : 1 ≤ (callIn d m (c₁.nreg 6807) π j Z c₁.nmem).cw.cnt := by
        rw [hbF]; exact πj.one_le_faces hk0'
      have hb2 : (callIn d m (c₁.nreg 6807) π j Z c₁.nmem).cw.cnt ≤ 2 * πj.k := by
        rw [hbF]; exact πj.card_faces_le
      have hkm : πj.k ≤ m := (SPath.k_le_card' πj).trans_eq hl.card_sdart
      have hcs := hcost m πj.k _ hm hb2
      have hpf := posT_le_fixRun (C := C) (C₀ := C₀) (cost := cost)
        (L := psize M σ (pdarts M (l.piece ∪ r.piece) Hs)) (by omega) hm hb1 hb2 hkm (by omega)
      refine ⟨c', t, ex, ?_, fun r hr => ?_, fun a ha hn => ?_, by rw [ho, hout], hF⟩
      · rw [fx7fT_eq _ u S T C C₀ h hj, hmc, ← hbF]; omega
      · rw [hK r hr, hreg r (by omega)]
      · obtain ⟨e1, e2⟩ := hkeep a (by omega) hn
        rw [e1, e2, hmem, hrm]; exact ⟨rfl, rfl⟩)
    (fun hk0 c₁ hc₁ hmem hreg hrr hrm hout => by
      have hk0' : πj.k = 0 := by rw [hkq]; exact hk0
      have hl1 : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₁.nmem := by rw [hmem]; exact hl
      have hSO1 : SegsOut M en m π e b (c₁.nreg 6807) c₁.nmem := by
        rw [hmem, hreg 6807 (by omega)]; exact hSO
      have hkq1 : πj.k = (callIn d m (c₁.nreg 6807) π j Z c₁.nmem).k := by
        rw [hmem, hreg 6807 (by omega)]; exact hkq
      have hFL1 : FLHas Z m d en c₁.nmem ((xCtxN M (NcStep.machNFT gid I pch) u S T l r π Hs σ h).seg j) := by
        rw [hmem]; exact hFL
      obtain ⟨c', t, ex, ht, hK, hkeep, ho, -, hF⟩ :=
        fx7f_zero hZW C C₀ hC (Rm := Rm) (wzm := wzm) h.1 hpl hrot hface I c₁ hc₁ hl1 hm hSO1 hj'
          hkq1 hk0' hps hFL1 (by rw [hreg 3004 (by omega)]; exact r04)
          (by rw [hreg 3006 (by omega)]; exact r06) rfl (by rw [hreg 6800 (by omega)]; exact r00)
          (fun a ha => by rw [hmem]; exact hMZ a ha) hWzd (by unfold MfDrv.fsz at hde; omega)
          (Nat.le_add_right b 5) (by unfold MfDrv.fsz at hde; omega) (by omega) hwz
      have hzf := zT_le_fixRun (C := C) (C₀ := C₀) (b := πj.faces.card) (k := πj.k)
        (L := psize M σ (pdarts M (l.piece ∪ r.piece) Hs)) hm
      refine ⟨c', t, ex, ?_, fun r hr => ?_, fun a ha hn => ?_, by rw [ho, hout], hF⟩
      · rw [fx7fT_eq _ u S T C C₀ h hj, hmc]; omega
      · rw [hK r hr, hreg r (by omega)]
      · obtain ⟨e1, e2⟩ := hkeep a (by omega) hn
        rw [e1, e2, hmem, hrm]; exact ⟨rfl, rfl⟩)
  obtain ⟨hT, hK, hkeep, ho, hF⟩ := hQ
  exact ⟨c', s, ex, by omega, hK, hkeep, ho, hF⟩

end BKMNW

end PlanarFlow
