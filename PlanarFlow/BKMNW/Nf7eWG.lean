module

public import PlanarFlow.BKMNW.Nf7dE
public import PlanarFlow.BKMNW.Nf7eWF

/-!
# The stage loop and the final step with a per-address word bound

**`fixFin_execW`** (`clrP ; finP`) and **`fin7d_execW`** (`loopP ; clrP ; finP`): `fixFin_exec`,
`fin7d_exec` with the word hypothesis (a sum of addresses) replaced by
`Tb + 60 m + 60 + negT ≤ W` (resp. `X.p + 60 m + 60 + negT ≤ W`, `Tb = X.p`). Same programs and
conclusions.
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
  WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Call

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ}

set_option maxHeartbeats 4000000 in
/-- **After the stage loop: `clrP ; finP` writes the flow of `fixPath`.** -/
theorem fixFin_execW (C C₀ : ℕ) (hC : 200000 ≤ C) (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (X : SLx (pmap hP)) {W : ℕ} (hG : X.Good W) (hrot : (pmap hP).RotTrans)
    (hface : (pmap hP).FaceTrans) (hU : X.c = fun y => u y.1)
    (I P' : Input) (c : Config) (hc : WordsBounded W c) (hl : Lay M gid u S T Z x m en d c.nmem)
    (hm : 0 < m) (hFL0 : FLHas Z m d en c.nmem X.f₀) {Tb PDb LABb Wz : ℕ}
    (hPDm : ∀ l < X.P.k, c.nmem (PDb + l) < m ∧ en (c.nmem (PDb + l)) = (X.P.d l).1)
    (r69 : c.nreg 9469 = Tb) (r00 : c.nreg 9400 = m) (r36 : c.nreg 9436 = 1)
    (r34 : c.nreg 9434 = d + 4 + 3 * m) (r35 : c.nreg 9435 = d + 4 + 6 * m)
    (r21 : c.nreg 9421 = Z) (r10 : c.nreg 9310 = X.K) (r01 : c.nreg 9401 = X.P.k)
    (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = d + 4 + m) (r31 : c.nreg 9431 = d + 4 + 2 * m)
    (r74 : c.nreg 9374 = X.CWb) (r75 : c.nreg 9375 = X.CRb) (r76 : c.nreg 9376 = X.FWb)
    (r05 : c.nreg 9405 = LABb)
    (r07 : c.nreg 7607 = X.lb + 2 * X.P.k) (r9475 : c.nreg 9475 = 0) (r71 : c.nreg 9471 = X.SH)
    (r12 : c.nreg 7612 = X.Wf + 1) (r9474 : c.nreg 9474 = X.SH + (X.Wf + 1))
    (hLAB : ∀ i < m, c.nmem (LABb + i) = olab (nxF d m c.nmem) i + 1)
    (hStt : X.Stt (X.st X.P.k) c.nmem) (hFix : X.Fix c.nmem) (hImg : X.Img c.nmem)
    (hz : ∀ a ≤ Wz, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → c.nmem a = 0)
    (hSHz : X.SH + X.WN ≤ Wz) (hPDz : Wz < PDb) (hCWz : Wz < X.CWb) (hS : 9 * m + 1 + tsz m ≤ Wz + 1) (hWzd : Wz < d)
    (hlo : d + 4 + 7 * m ≤ LABb ∧ LABb + m ≤ Tb ∧ PDb + X.P.k ≤ Tb ∧ X.CWb + X.P.k ≤ Tb ∧
      X.CRb + X.P.k ≤ Tb ∧ X.FWb + X.P.k ≤ Tb)
    (hWz : rtW m (rtL (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y)) m ≤ Wz)
    (hW : Tb + 60 * m + 60 + negT C C₀ m ≤ W)
    (wL : 2 * X.K + rtL (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y) ≤ W)
    (hw2 : spWs m + 205 ≤ W)
    (hw3 : fxWB m (rtL (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y)) ≤ W)
    (hv : ∀ i < m, c.nmem (d + 4 + 3 * m + i) + Z + X.K + X.K +
      2 * rtL (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y) ≤ W) :
    ∃ c' t, Exec P' W (.seq clrP finP) c c' t ∧
      t ≤ 20 * (X.lb + 2 * X.P.k) + 32 + finT C C₀ m X.P.k ∧
      FLHas Z m d en c'.nmem (fixPath (pmap hP) X.c X.f₀ X.P X.mssp X.fr (negLay gid I x hP)) ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      (∀ a, Wz < a → a < Tb → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, KeepR r → (r < 9477 ∨ 9498 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := hlo
  obtain ⟨E, hE⟩ : ∃ E, E = layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm := ⟨_, rfl⟩
  have eEv : ∀ i < m, (E i).1 = en i := fun i hi => by rw [hE]; exact layEn_val hi
  have hinv : EffInvB (pmap hP) X.c X.f₀ X.P X.P.k (X.st X.P.k) :=
    fixPath_invB hG.plane hG.c_nn hG.pseudo hG.mssp_spec hG.fr_spec X.P.k le_rfl
  -- the bounds
  have hK := hG.hK
  have hbc := hG.bc
  have hbst := hG.bst
  have hAS := absSum_nonneg X.c
  have hBst := Bst_nonneg (D := SDart (pdarts M x.1.piece x.2.1)) X.c
  have hkB : (0 : ℤ) ≤ (X.P.k : ℤ) * Bst (SDart (pdarts M x.1.piece x.2.1)) X.c := by positivity
  have hgK' : ∀ e, |(X.st X.P.k).1 e| ≤ X.K := fun e => by
    have h1 := (hinv.flow_bound hG.c_nn hG.pseudo e).2
    have h2 : ((16 * X.B : ℕ) : ℤ) ≤ X.K := by exact_mod_cast hK
    push_cast at h2
    have h3 : (0 : ℤ) ≤ X.B := by positivity
    linarith
  have hℓK' : ∀ e, |(X.c - (X.st X.P.k).1) e| ≤ X.K := fun e => by
    have h1 := hinv.len_bound hG.c_nn hG.pseudo e
    have h2 : ((16 * X.B : ℕ) : ℤ) ≤ X.K := by exact_mod_cast hK
    push_cast at h2
    linarith
  have hcK : ∀ e, X.c e ≤ X.K := fun e => by
    have := abs_le_absSum X.c e
    have := (abs_le.1 this).2
    have : ((16 * X.B : ℕ) : ℤ) ≤ X.K := by exact_mod_cast hK
    push_cast at this; omega
  obtain ⟨Φ, -, hoff, hanti, -⟩ := hinv.1
  -- the darts of the path in the frame
  have eD : ∀ l < X.P.k, E (c.nmem (PDb + l)) = X.P.d l := fun l hl' =>
    Subtype.ext (by rw [eEv _ (hPDm l hl').1, (hPDm l hl').2])
  have eR : ∀ l < X.P.k, E (c.nmem (d + 4 + m + c.nmem (PDb + l))) =
      (pmap hP).rev (X.P.d l) := fun l hl' => by
    have h1 := hl.rv _ (hPDm l hl').1
    exact Subtype.ext (by rw [eEv _ h1.1, h1.2, pmap_rev, (hPDm l hl').2])
  have Einj : ∀ i < m, ∀ j < m, E i = E j → i = j := fun i hi j hj e => by
    have := congrArg Subtype.val e
    rw [eEv i hi, eEv j hj] at this
    exact hl.en_inj hi hj this
  -- the negative call: `NegPre`, an outcome `χ`, the final flow is a pseudoflow
  have eℓ : X.c - (X.st X.P.k).1 = fun y => u y.1 - (X.st X.P.k).1 y := by
    funext y; rw [hU]; rfl
  have hpre : NegPre (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y) := by
    rw [← eℓ]
    exact fixPath_negPre hG.plane hrot hface hG.c_nn hG.pseudo hG.mssp_spec hG.fr_spec
  obtain ⟨χ, hχ⟩ := neg_some (negLay_spec gid I x hP) (hinv.final)
  rw [eℓ] at hχ
  have hfx : fixPath (pmap hP) X.c X.f₀ X.P X.mssp X.fr (negLay gid I x hP) =
      (X.st X.P.k).1 + (pmap hP).cob χ := by
    rw [fixPath_eq_fpState]
    have h' : negLay gid I x hP (X.c - (fpState (pmap hP) X.c X.f₀ X.P X.mssp X.fr X.P.k).1) =
        some χ := (congrArg (negLay gid I x hP) eℓ).trans hχ
    rw [h']
    rfl
  have hps := (fixPath_spec hG.plane hG.c_nn hG.pseudo X.P hG.mssp_spec hG.fr_spec
    (negLay_spec gid I x hP)).pseudo
  rw [hfx] at hps
  -- clear the image
  have h2sb := X.two_sb_le
  have hWN : 2 * X.Wf + 1 ≤ X.WN := by unfold SLx.WN; omega
  have hSHW : X.SH + X.WN < W := by
    have := hG.l2; have := hG.l3; have := hG.l4; have := hG.l5; have := hG.l6; have := hG.l7
    have := hG.l8; have := hG.l9; have := hG.l10; have := hG.l11; have := hG.l12; have := hG.l13
    have := hG.l14; omega
  obtain ⟨c₁, t₁, e₁, ht₁, z1, k1, n1, r1, rm1, o1⟩ :=
    clrP_exec (P := P') c hc (sb := X.lb + 2 * X.P.k) (SH := X.SH) (w1 := X.Wf + 1) r07 r9475 r71
      r12 r9474 (by omega)
  have hl1 := hG.l1
  have hz1 : ∀ a ≤ Wz, c₁.nmem a = 0 := fun a ha => by
    by_cases q1 : a < X.lb + 2 * X.P.k
    · exact (z1 a q1).1
    by_cases q2 : X.SH ≤ a ∧ a < X.SH + (X.lb + 2 * X.P.k)
    · have := (z1 (a - X.SH) (by omega)).2.1; rwa [show X.SH + (a - X.SH) = a by omega] at this
    by_cases q3 : X.Wf + 1 ≤ a ∧ a < X.Wf + 1 + (X.lb + 2 * X.P.k)
    · have := (z1 (a - (X.Wf + 1)) (by omega)).2.2.1
      rwa [show X.Wf + 1 + (a - (X.Wf + 1)) = a by omega] at this
    by_cases q4 : X.SH + (X.Wf + 1) ≤ a ∧ a < X.SH + (X.Wf + 1) + (X.lb + 2 * X.P.k)
    · have := (z1 (a - (X.SH + (X.Wf + 1))) (by omega)).2.2.2
      rwa [show X.SH + (X.Wf + 1) + (a - (X.SH + (X.Wf + 1))) = a by omega] at this
    rw [k1 a q1 q2 q3 q4]
    by_cases q5 : a ≤ X.WN
    · exact (img_zero hG hImg q5 q1 q3).1
    by_cases q6 : X.SH ≤ a ∧ a ≤ X.SH + X.WN
    · have := (img_zero hG hImg (a := a - X.SH) (by omega) (by omega) (by omega)).2
      rwa [show X.SH + (a - X.SH) = a by omega] at this
    exact hz a ha (by omega) q6
  have k1' : ∀ a, Wz < a → c₁.nmem a = c.nmem a := fun a ha =>
    k1 a (by omega) (by omega) (by omega) (by omega)
  have hl₁ : Lay M gid u S T Z x m en d c₁.nmem := hl.congr fun a h1 h2 => k1' a (by omega)
  have q : ∀ r, (r < 5030 ∨ 5035 < r) → c₁.nreg r = c.nreg r := n1
  have hW1 := hG.w1
  have l3' := hG.l3; have l4' := hG.l4
  -- the reads of `finP` on `c₁`
  have mPD : ∀ l < X.P.k, c₁.nmem (PDb + l) = c.nmem (PDb + l) := fun l hl' => k1' _ (by omega)
  have mRV : ∀ i < m, c₁.nmem (d + 4 + m + i) = c.nmem (d + 4 + m + i) := fun i hi =>
    k1' _ (by omega)
  have mFix := hFix
  obtain ⟨fCW, fCR, -, -, -, -⟩ := hFix
  obtain ⟨sFW, -⟩ := hStt
  have hNX : ∀ i < m, nxF d m c₁.nmem i = nxF d m c.nmem i := fun i hi => by
    unfold nxF
    rw [k1' (d + 4 + m + i) (by omega), k1' _ (by have := (hl.rv i hi).1; omega)]
  have hLAB₁ : ∀ i < m, c₁.nmem (LABb + i) = olab (nxF d m c₁.nmem) i + 1 := fun i hi => by
    rw [k1' _ (by omega), hLAB i hi, olab_congr (f := nxF d m c₁.nmem) (g := nxF d m c.nmem)
      hNX hl₁.permOn_nx hi]
  have hrevE : ∀ i < m, E (c.nmem (d + 4 + m + i)) = (pmap hP).rev (E i) := fun i hi => by
    have h1 := hl.rv i hi
    exact Subtype.ext (by rw [eEv _ h1.1, h1.2, pmap_rev, eEv i hi])
  have eL1 : layEn (pdarts M x.1.piece x.2.1) en m hl₁.en_mem hm = E := hE.symm
  obtain ⟨c₂, t₂, e₂, ht₂, fFL, fz, fK, fR, fr, frm, fo⟩ :=
    finP_execW C C₀ hC hP (X.st X.P.k).1 hpre I P' c₁ e₁.wb_right hl₁ hm (Tb := Tb) (k := X.P.k)
      (PDb := PDb) (CWb := X.CWb) (CRb := X.CRb) (FWb := X.FWb) (K := X.K) (Wz := Wz)
      (LABb := LABb) hχ
      (by rw [q _ (by omega), r69]) (by rw [q _ (by omega), r00]) (by rw [q _ (by omega), r36])
      (by rw [q _ (by omega), r34]) (by rw [q _ (by omega), r35]) (by rw [q _ (by omega), r21])
      (by rw [q _ (by omega), r10]) (by rw [q _ (by omega), r01]) (by rw [q _ (by omega), r02])
      (by rw [q _ (by omega), r30]) (by rw [q _ (by omega), r31]) (by rw [q _ (by omega), r74])
      (by rw [q _ (by omega), r75]) (by rw [q _ (by omega), r76]) (by rw [q _ (by omega), r05])
      hLAB₁ (fun l hl' => by rw [mPD l hl']; exact (hPDm l hl').1)
      (fun l hl' l' hl'' => by
        rw [mPD l hl', mPD l' hl'', mRV _ (hPDm l hl').1, mRV _ (hPDm l' hl'').1]
        refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
        · have := congrArg E e
          rw [eD l hl', eR l' hl''] at this
          exact X.P.d_ne_rev hl' hl'' this
        · have := congrArg E e
          rw [eD l hl', eD l' hl''] at this
          exact X.P.d_inj hl' hl'' this
        · have := congrArg E e
          rw [eR l hl', eR l' hl''] at this
          have := congrArg (pmap hP).rev this
          rw [(pmap hP).rev_rev, (pmap hP).rev_rev] at this
          exact X.P.d_inj hl' hl'' this)
      (fun i hi hn => by
        rw [eL1, k1' _ (by omega)]
        have hfl := hFL0 i hi
        rw [fext_mem _ (hl.en_mem i hi)] at hfl
        have eEi : (⟨en i, hl.en_mem i hi⟩ : SDart (pdarts M x.1.piece x.2.1)) = E i :=
          (Subtype.ext (eEv i hi)).symm
        rw [eEi] at hfl
        rw [hfl, hoff (E i) fun hd => ?_]
        obtain ⟨l, hl', hd'⟩ := X.P.mem_darts.1 hd
        have hn' := hn l hl'
        rw [mPD l hl', mRV _ (hPDm l hl').1] at hn'
        rcases hd' with e | e
        · rw [← eD l hl'] at e
          exact hn'.1 (Einj _ (hPDm l hl').1 i hi e.symm)
        · rw [← eR l hl'] at e
          exact hn'.2 (Einj _ (by have := (hl.rv _ (hPDm l hl').1).1; omega) i hi e.symm))
      (fun l hl' => by
        rw [mPD l hl', k1' _ (by omega), fCW l hl', ← eD l hl', hU]
        exact congrArg u (eEv _ (hPDm l hl').1))
      (fun l hl' => by
        have h1 := (hl.rv _ (hPDm l hl').1)
        rw [mPD l hl', mRV _ (hPDm l hl').1, k1' _ (by omega), fCR l hl', hU]
        show u (M.rev (X.P.d l).1) = _
        rw [h1.2, (hPDm l hl').2])
      (fun l hl' => by rw [eL1, mPD l hl', k1' _ (by omega), sFW l hl', eD l hl'])
      (fun l hl' => by rw [eL1, mPD l hl', mRV _ (hPDm l hl').1, eR l hl', eD l hl', hanti])
      (fun i hi => by rw [eL1]; exact hgK' _)
      (fun i hi => by
        have := hℓK' (E i)
        rw [hU] at this
        rw [eL1, ← eEv i hi]
        exact this)
      (fun i hi => by
        rw [eL1]
        have h1 := hps.le_cap ((pmap hP).rev (E i))
        rw [hps.antisymm (E i)] at h1
        rw [← hrevE i hi, hU] at h1
        have h2 := (hl.cp _ (hl.rv i hi).1)
        have h3 : u (E (c.nmem (d + 4 + m + i))).1 = u (en (c.nmem (d + 4 + m + i))) := by
          rw [eEv _ (hl.rv i hi).1]
        change -((X.st X.P.k).1 + (pmap hP).cob χ) (E i) ≤ u (E (c.nmem (d + 4 + m + i))).1 at h1
        rw [h3] at h1
        have : (c.nmem (d + 4 + 3 * m + c.nmem (d + 4 + m + i)) : ℤ) ≤ Z := by exact_mod_cast h2.2
        linarith [h2.1])
      hz1 hS hWzd ⟨l0, l1, l2, l3, l4, l5⟩ hWz hW wL hw2 hw3
      (fun i hi => by rw [k1' _ (by omega)]; exact hv i hi)
      (fun l hl' => by
        have h1 := fCW l hl'
        have h2 := hcK (X.P.d l)
        have h3 : (c₁.nmem (X.CWb + l) : ℤ) ≤ X.K := by rw [k1' _ (by omega), h1]; exact h2
        have h4 : ((16 * X.K + 1 : ℕ) : ℤ) ≤ W := by exact_mod_cast hW1
        push_cast at h4
        have : ((c₁.nmem (X.CWb + l) + X.K + X.K : ℕ) : ℤ) ≤ W := by push_cast; omega
        exact_mod_cast this)
      (fun l hl' => by
        have h1 := fCR l hl'
        have h2 := hcK ((pmap hP).rev (X.P.d l))
        have h3 := sFW l hl'
        have h5 := hgK' (X.P.d l)
        have h6 := (abs_le.1 h5).2
        rw [← k1' (X.CRb + l) (by omega)] at h1
        rw [← k1' (X.FWb + l) (by omega)] at h3
        have h4 : ((16 * X.K + 1 : ℕ) : ℤ) ≤ W := by exact_mod_cast hW1
        push_cast at h4
        have : ((c₁.nmem (X.CRb + l) + c₁.nmem (X.FWb + l) : ℕ) : ℤ) ≤ W := by push_cast; omega
        exact_mod_cast this)
  refine ⟨c₂, _, e₁.seq e₂, by omega, ?_, fz, fun a h1 h2 h3 => ?_, fun r hr h2 => ?_,
    by rw [fr, r1], by rw [frm, rm1], by rw [fo, o1]⟩
  · rw [hfx]; exact fFL
  · rw [fK a h1 h2 h3, k1' a h1]
  · rw [fR r hr h2]; have hr' := hr; unfold KeepR at hr'; exact q r (by omega)

set_option maxHeartbeats 4000000 in
/-- **The stage loop and the final step** (see the module docstring). -/
theorem fin7d_execW (C C₀ : ℕ) (hC : 200000 ≤ C) (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (X : SLx (pmap hP)) {W : ℕ} (hG : X.Good W) (hrot : (pmap hP).RotTrans)
    (hface : (pmap hP).FaceTrans) (hU : X.c = fun y => u y.1)
    (I P' : Input) (c : Config) (hc : WordsBounded W c) (hl : Lay M gid u S T Z x m en d c.nmem)
    (hm : 0 < m) (hFL0 : FLHas Z m d en c.nmem X.f₀) {LABb Wz : ℕ}
    (hPDm : ∀ l < X.P.k, c.nmem (c.nreg 9402 + l) < m ∧
      en (c.nmem (c.nreg 9402 + l)) = (X.P.d l).1)
    (hR : X.Regs c) (hFix : X.Fix c.nmem) (hS0 : X.Stt (X.st 0) c.nmem) (hImg : X.Img c.nmem)
    (r69 : c.nreg 9469 = X.p) (r00 : c.nreg 9400 = m) (r36 : c.nreg 9436 = 1)
    (r34 : c.nreg 9434 = d + 4 + 3 * m) (r35 : c.nreg 9435 = d + 4 + 6 * m)
    (r21 : c.nreg 9421 = Z) (r01 : c.nreg 9401 = X.P.k) (r30 : c.nreg 9430 = d + 4 + m) (r31 : c.nreg 9431 = d + 4 + 2 * m)
    (r05 : c.nreg 9405 = LABb) (r9475 : c.nreg 9475 = 0) (r71 : c.nreg 9471 = X.SH)
    (r9474 : c.nreg 9474 = X.SH + (X.Wf + 1))
    (hLAB : ∀ i < m, c.nmem (LABb + i) = olab (nxF d m c.nmem) i + 1)
    (hz : ∀ a ≤ Wz, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → c.nmem a = 0)
    (hSHz : X.SH + X.WN ≤ Wz) (hPDz : Wz < c.nreg 9402) (hS : 9 * m + 1 + tsz m ≤ Wz + 1)
    (hWzd : Wz < d)
    (hlo : d + 4 + 7 * m ≤ LABb ∧ LABb + m ≤ X.CWb ∧ c.nreg 9402 + X.P.k ≤ X.CWb)
    (hWz : rtW m (rtL (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y)) m ≤ Wz)
    (hW : X.p + 60 * m + 60 + negT C C₀ m ≤ W)
    (wL : 2 * X.K + rtL (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y) ≤ W)
    (hw2 : spWs m + 205 ≤ W)
    (hw3 : fxWB m (rtL (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y)) ≤ W)
    (hv : ∀ i < m, c.nmem (d + 4 + 3 * m + i) + Z + X.K + X.K +
      2 * rtL (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y) ≤ W) :
    ∃ c' t, Exec P' W (.seq loopP (.seq clrP finP)) c c' t ∧
      t ≤ loopT X.b X.P.k + (20 * (X.lb + 2 * X.P.k) + 32 + finT C C₀ m X.P.k) ∧
      FLHas Z m d en c'.nmem (fixPath (pmap hP) X.c X.f₀ X.P X.mssp X.fr (negLay gid I x hP)) ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      (∀ a, Wz < a → a < X.CWb → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, KeepR r → (r < 9477 ∨ 9498 < r) → ¬ SLx.scr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have l1 := hG.l1; have l2 := hG.l2
  obtain ⟨c₄, t₄, e₄, ht₄, S4, I4, M4, R4, rr4, rm4, o4⟩ :=
    SLx.loopP_exec' (I := P') hG c hc hR hFix hS0 hImg
  -- what the loop keeps below `CW`
  have m4 : ∀ a, X.SH + X.WN < a → a < X.CWb → c₄.nmem a = c.nmem a := fun a h1 h2 =>
    M4 a (by omega) (by omega) (fun hw => by have := SLx.wr_ge hG hw; omega)
  have hscr : ∀ r, ¬ SLx.scr r → c₄.nreg r = c.nreg r := R4
  have ns : ∀ r, (r = 9469 ∨ r = 9400 ∨ r = 9436 ∨ r = 9434 ∨ r = 9435 ∨ r = 9421 ∨ r = 9310 ∨
      r = 9401 ∨ r = 9402 ∨ r = 9430 ∨ r = 9431 ∨ r = 9374 ∨ r = 9375 ∨ r = 9376 ∨ r = 9405 ∨
      r = 7607 ∨ r = 9475 ∨ r = 9471 ∨ r = 7612 ∨ r = 9474) → c₄.nreg r = c.nreg r :=
    fun r hr => hscr r (by
      unfold SLx.scr swScr FrFix.frScr; omega)
  obtain ⟨⟨g10, g71, -, g74, g75, g76, -, -, -, -, -⟩, -, ⟨-, -, -, -, -, -, g07, -, -, -, -, g12,
    -, -, -⟩⟩ := hR
  have hl4 : Lay M gid u S T Z x m en d c₄.nmem := hl.congr fun a h1 h2 => m4 a (by omega)
    (by have := hlo.1; have := hlo.2.1; omega)
  have hFL4 : FLHas Z m d en c₄.nmem X.f₀ := fun i hi => by
    rw [m4 _ (by omega) (by have := hlo.1; have := hlo.2.1; omega)]; exact hFL0 i hi
  have hNX : ∀ i < m, nxF d m c₄.nmem i = nxF d m c.nmem i := fun i hi => by
    unfold nxF
    have := hlo.1; have := hlo.2.1
    have h1 := (hl.rv i hi).1
    rw [m4 (d + 4 + m + i) (by omega) (by omega), m4 _ (by omega) (by omega)]
  have hLAB4 : ∀ i < m, c₄.nmem (LABb + i) = olab (nxF d m c₄.nmem) i + 1 := fun i hi => by
    have := hlo.1; have := hlo.2.1
    rw [m4 _ (by omega) (by omega), hLAB i hi,
      olab_congr (f := nxF d m c₄.nmem) (g := nxF d m c.nmem) hNX hl4.permOn_nx hi]
  have hPDm4 : ∀ l < X.P.k, c₄.nmem (c.nreg 9402 + l) < m ∧
      en (c₄.nmem (c.nreg 9402 + l)) = (X.P.d l).1 := fun l hl' => by
    have := hlo.2.2
    rw [m4 _ (by omega) (by omega)]; exact hPDm l hl'
  have hz4 : ∀ a ≤ Wz, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → c₄.nmem a = 0 :=
    fun a h1 h2 h3 => by
      rw [M4 a h2 h3 (fun hw => by have := SLx.wr_ge hG hw; omega)]; exact hz a h1 h2 h3
  have hv4 : ∀ i < m, c₄.nmem (d + 4 + 3 * m + i) + Z + X.K + X.K +
      2 * rtL (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y) ≤ W := fun i hi => by
    have := hlo.1; have := hlo.2.1
    rw [m4 _ (by omega) (by omega)]; exact hv i hi
  have hTb : LABb + m ≤ X.p ∧ c.nreg 9402 + X.P.k ≤ X.p ∧ X.CWb + X.P.k ≤ X.p ∧
      X.CRb + X.P.k ≤ X.p ∧ X.FWb + X.P.k ≤ X.p := by
    have := hG.l13; have := hG.l12; have := hG.l11; have := hG.l10; have := hG.l9
    have := hG.l8; have := hG.l7; have := hG.l6; have := hG.l5; have := hG.l4; have := hG.l3
    omega
  obtain ⟨c₅, t₅, e₅, ht₅, F5, z5, k5, r5, rr5, rm5, o5⟩ :=
    fixFin_execW C C₀ hC hP X hG hrot hface hU I P' c₄ e₄.wb_right hl4 hm hFL4 (Tb := X.p)
      (PDb := c.nreg 9402) (LABb := LABb) (Wz := Wz) hPDm4
      (by rw [ns _ (by omega), r69]) (by rw [ns _ (by omega), r00]) (by rw [ns _ (by omega), r36])
      (by rw [ns _ (by omega), r34]) (by rw [ns _ (by omega), r35]) (by rw [ns _ (by omega), r21])
      (by rw [ns _ (by omega), g10]) (by rw [ns _ (by omega), r01])
      (by rw [ns _ (by omega)]) (by rw [ns _ (by omega), r30]) (by rw [ns _ (by omega), r31])
      (by rw [ns _ (by omega), g74]) (by rw [ns _ (by omega), g75]) (by rw [ns _ (by omega), g76])
      (by rw [ns _ (by omega), r05]) (by rw [ns _ (by omega), g07]) (by rw [ns _ (by omega), r9475])
      (by rw [ns _ (by omega), r71]) (by rw [ns _ (by omega), g12])
      (by rw [ns _ (by omega), r9474]) hLAB4 S4 (SLx.fix_congr hG hFix M4) I4 hz4 hSHz hPDz
      (by omega) hS hWzd
      ⟨hlo.1, hTb⟩
      hWz hW wL hw2 hw3 hv4
  refine ⟨c₅, _, e₄.seq e₅, by omega, F5, z5, fun a h1 h2 h3 => ?_, fun r hr h1 h2 => ?_,
    by rw [rr5, rr4], by rw [rm5, rm4], by rw [o5, o4]⟩
  · have := hG.l13; have := hG.l12; have := hG.l11; have := hG.l10; have := hG.l9
    have := hG.l8; have := hG.l7; have := hG.l6; have := hG.l5; have := hG.l4; have := hG.l3
    rw [k5 a h1 (by omega) h3, m4 a (by omega) h2]
  · rw [r5 r hr h1, hscr r h2]

end Call

end BKMNW

end PlanarFlow
