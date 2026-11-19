module

public import PlanarFlow.BKMNW.Nf9bH

/-!
# The stage loop and the final step of the frozen fix

* `pcob_inl`, `pcob_inr` (the coboundary on the map with pendant edges vanishes on the pendant
  darts), `PCtx.en_inr` (the pendant indices `≥ m` are pendant darts);
* **`fixFin9_exec`**: after the stage loop of `X = mkP …` (state `X.st k` in `FW`, `PW`),
  `clrP ; finP` with the base frame for the negative-length call (`r9400 = m`, `r9431` the base
  `SG`) writes in the pendant flow array
  `Z' + fixPath (M₀.pendant e he) cap f₀ (πj.lift) (msspP (msspPlaneK M₀)) (frRef F)
    (negP (negMach (nsIds M₀ henum (en 0)) M₀ I))` on all `m'` pendant darts: on the base darts by
  `finP9_exec`, on the pendant darts the flow array is untouched and the value is `f₀`;
* **`fin9_exec`**: `loopP ; clrP ; finP` (the loop + `fixFin9_exec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace F9b

open Finset Function Equiv Orbit CombMap OrbLab NegSSSP NegSSSP.Frame MfDrv NsStep NcFz SPath
  WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M₀ : CombMap D V F} {e : V → D} {he : ∀ v, M₀.tail (e v) = v}
variable {en : ℕ → D} {en' : ℕ → D ⊕ (V × Bool)} {m m' Z' d d' : ℕ}
  {cap f₀ : D ⊕ (V × Bool) → ℤ} {segs : List (SPath M₀)} {lo hi Gb j : ℕ} {mem : ℕ → ℕ}

lemma pcob_inl (χ : F → ℤ) (y : D) : (M₀.pendant e he).cob χ (.inl y) = M₀.cob χ y := rfl

lemma pcob_inr (χ : F → ℤ) (x : V × Bool) : (M₀.pendant e he).cob χ (.inr x) = 0 := by
  obtain ⟨v, b⟩ := x
  show χ (M₀.face (e v)) - χ (M₀.face (e v)) = 0
  exact sub_self _

lemma inr_not_mem_lift (π : SPath M₀) (x : V × Bool) : Sum.inr x ∉ (π.lift e he).darts := by
  rw [SPath.lift_darts]; simp

lemma inl_mem_lift {π : SPath M₀} {y : D} (h : Sum.inl y ∈ (π.lift e he).darts) : y ∈ π.darts := by
  rw [SPath.lift_darts] at h; simpa using h

/-- **The pendant indices `≥ m` are pendant darts.** -/
lemma PCtx.en_inr (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j mem) {i : ℕ}
    (hi : i < m') (hm : m ≤ i) : ∃ x, en' i = .inr x := by
  rcases h : en' i with y | x
  · exfalso
    obtain ⟨i₀, hi₀, rfl⟩ := H.enum.surj y
    have := H.fr.en_inj hi (by have := H.mm; omega) (h.trans (H.hen i₀ hi₀).symm)
    omega
  · exact ⟨x, rfl⟩

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 8000000 in
/-- **After the stage loop: `clrP ; finP` writes the frozen fix on the pendant frame.** -/
theorem fixFin9_exec (C C₀ : ℕ) (hC : 200000 ≤ C) (c : Config)
    (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j c.nmem) (hj : j < segs.length)
    {q : FpIn} {Q : ℕ} {W : ℕ}
    (hG : (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).Good W)
    (I P' : Input) (hc : WordsBounded W c) {Tb PDb LABb Wz : ℕ}
    (hPDm : ∀ l < (segs[j]'hj).k, c.nmem (PDb + l) < m ∧
      en (c.nmem (PDb + l)) = (segs[j]'hj).d l)
    (r69 : c.nreg 9469 = Tb) (r00 : c.nreg 9400 = m) (r36 : c.nreg 9436 = 1)
    (r34 : c.nreg 9434 = d' + 4 + 3 * m') (r35 : c.nreg 9435 = d' + 4 + 6 * m')
    (r21 : c.nreg 9421 = Z') (r10 : c.nreg 9310 = (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).K)
    (r01 : c.nreg 9401 = (segs[j]'hj).k)
    (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = d' + 4 + m') (r31 : c.nreg 9431 = d + 4 + m + m)
    (r74 : c.nreg 9374 = (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).CWb)
    (r75 : c.nreg 9375 = (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).CRb)
    (r76 : c.nreg 9376 = (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).FWb)
    (r05 : c.nreg 9405 = LABb)
    (r07 : c.nreg 7607 = (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).lb +
      2 * (segs[j]'hj).k) (r9475 : c.nreg 9475 = 0)
    (r71 : c.nreg 9471 = (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).SH)
    (r12 : c.nreg 7612 = (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).Wf + 1)
    (r9474 : c.nreg 9474 = (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).SH +
      ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).Wf + 1))
    (hLAB : ∀ i < m, c.nmem (LABb + i) = olab (nxF d' m' c.nmem) i + 1)
    (hStt : (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).Stt
      ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).st (segs[j]'hj).k) c.nmem)
    (hFix : (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).Fix c.nmem)
    (hImg : (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).Img c.nmem)
    (hz : ∀ a ≤ Wz, (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).WN < a →
      ¬ ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).SH ≤ a ∧
        a ≤ (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).SH +
          (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).WN) → c.nmem a = 0)
    (hSHz : (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).SH +
      (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).WN ≤ Wz)
    (hS : 9 * m + 1 + tsz m ≤ Wz + 1) (hWzd : Wz < d) (hWzd' : Wz < d') (hPDz : Wz < PDb)
    (hCWz : Wz < (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).CWb)
    (hlo : d' + 4 + 7 * m' ≤ LABb ∧ LABb + m ≤ Tb ∧ d + 4 + 3 * m ≤ Tb ∧
      PDb + (segs[j]'hj).k ≤ Tb ∧
      (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).CWb + (segs[j]'hj).k ≤ Tb ∧
      (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).CRb + (segs[j]'hj).k ≤ Tb ∧
      (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).FWb + (segs[j]'hj).k ≤ Tb)
    (hWz : rtW m (rtL M₀ (fun y => cap (.inl y) -
      ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).st (segs[j]'hj).k).1 (.inl y))) m ≤ Wz)
    (hW : Tb + 60 * m + 60 + negT C C₀ m ≤ W)
    (wL : 2 * (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).K + rtL M₀ (fun y => cap (.inl y) -
      ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).st (segs[j]'hj).k).1 (.inl y)) ≤ W)
    (hw2 : spWs m + 205 ≤ W)
    (hw3 : fxWB m (rtL M₀ (fun y => cap (.inl y) -
      ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).st (segs[j]'hj).k).1 (.inl y))) ≤ W)
    (hv : ∀ i < m, c.nmem (d' + 4 + 3 * m' + i) + Z' +
      (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).K +
      (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).K + 2 * rtL M₀ (fun y => cap (.inl y) -
      ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).st (segs[j]'hj).k).1 (.inl y)) ≤ W) :
    ∃ c' t, Exec P' W (.seq clrP finP) c c' t ∧
      t ≤ 20 * ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).lb + 2 * (segs[j]'hj).k) + 32 +
        finT C C₀ m (segs[j]'hj).k ∧
      (∀ i < m', (c'.nmem (d' + 4 + 6 * m' + i) : ℤ) = Z' + fixPath (M₀.pendant e he) cap f₀
        ((segs[j]'hj).lift e he) (msspP (Klein.msspPlaneK M₀)) (frRef F)
        (negP (negMach (nsIds M₀ H.enum (en 0)) M₀ I)) (en' i)) ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      (∀ a, Wz < a → a < Tb → (a < d' + 4 + 6 * m' ∨ d' + 4 + 7 * m' ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, KeepR r → (r < 9477 ∨ 9498 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set X := mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q with hX
  set π := segs[j]'hj with hπ
  obtain ⟨l0, l1, lb, l2, l3, l4, l5⟩ := hlo
  have hmm := H.mm
  have hm0 := H.m0
  have hinv : EffInvB (M₀.pendant e he) X.c X.f₀ X.P X.P.k (X.st X.P.k) :=
    fixPath_invB hG.plane hG.c_nn hG.pseudo hG.mssp_spec hG.fr_spec X.P.k le_rfl
  set s1 := (X.st X.P.k).1 with hs1
  have hPk : X.P.k = π.k := rfl
  set u₀ : D → ℤ := fun y => cap (.inl y) with hu₀
  set g₀ : D → ℤ := fun y => s1 (.inl y) with hg₀
  -- the bounds
  have hK := hG.hK
  have hgK' : ∀ y, |s1 y| ≤ X.K := fun y => by
    have h1 := (hinv.flow_bound hG.c_nn hG.pseudo y).2
    have h2 : ((16 * X.B : ℕ) : ℤ) ≤ X.K := by exact_mod_cast hK
    push_cast at h2
    have hbst := hG.bst
    have hkB : (0 : ℤ) ≤ (X.P.k : ℤ) * Bst (D ⊕ (V × Bool)) X.c := by
      have := Bst_nonneg (D := D ⊕ (V × Bool)) X.c; positivity
    have h3 : (0 : ℤ) ≤ X.B := by positivity
    linarith
  have hℓK' : ∀ y, |(X.c - s1) y| ≤ X.K := fun y => by
    have h1 := hinv.len_bound hG.c_nn hG.pseudo y
    have h2 : ((16 * X.B : ℕ) : ℤ) ≤ X.K := by exact_mod_cast hK
    push_cast at h2
    have hbst := hG.bst
    have hbc := hG.bc
    have hA := absSum_nonneg X.c
    have hkB : (0 : ℤ) ≤ (X.P.k : ℤ) * Bst (D ⊕ (V × Bool)) X.c := by
      have := Bst_nonneg (D := D ⊕ (V × Bool)) X.c; positivity
    linarith
  have hcK : ∀ y, X.c y ≤ X.K := fun y => by
    have := abs_le_absSum X.c y
    have := (abs_le.1 this).2
    have h2 := hG.bc
    have : ((16 * X.B : ℕ) : ℤ) ≤ X.K := by exact_mod_cast hK
    push_cast at this
    have hA := absSum_nonneg X.c
    have hb := hG.bst
    have hkB : (0 : ℤ) ≤ (X.P.k : ℤ) * Bst (D ⊕ (V × Bool)) X.c := by
      have := Bst_nonneg (D := D ⊕ (V × Bool)) X.c; positivity
    linarith
  obtain ⟨Φ, -, hoff, hanti, -⟩ := hinv.1
  have hoff' : ∀ y ∉ X.P.darts, s1 y = f₀ y := hoff
  -- the base darts of the path
  have eR : ∀ l < π.k, en (c.nmem (d' + 4 + m' + c.nmem (PDb + l))) = M₀.rev (π.d l) := by
    intro l hl'
    have h1 := (hPDm l hl').1
    rw [H.rvE h1, (H.brv _ h1).2, (hPDm l hl').2]
  have eRl : ∀ l < π.k, c.nmem (d' + 4 + m' + c.nmem (PDb + l)) < m := fun l hl' => by
    rw [H.rvE (hPDm l hl').1]; exact (H.brv _ (hPDm l hl').1).1
  -- the negative call on the base map
  have hpre' := fixPath_negPre hG.plane (pendant_rotTrans he H.rot) (pendant_faceTrans he H.ft)
    hG.c_nn hG.pseudo hG.mssp_spec hG.fr_spec
  have hpre : NegPre M₀ (u₀ - g₀) :=
    ⟨H.pl, H.rot, H.ft, fun y hy => hpre'.2.2.2 (.inl y) hy⟩
  obtain ⟨Φ', hΦ'⟩ := hinv.final
  have hfeas : ∃ Ψ : F → ℤ, IsPseudo M₀ u₀ (g₀ + M₀.cob Ψ) :=
    ⟨Φ', ⟨fun y => hΦ'.antisymm (.inl y), fun y => hΦ'.le_cap (.inl y)⟩⟩
  obtain ⟨χ, hχ⟩ := neg_some (negMach_spec (nsIds M₀ H.enum (en 0)) M₀ I) hfeas
  have hpos : ∀ x : V × Bool, 0 ≤ (cap - s1) (.inr x) := fun x => by
    have h1 := hoff (.inr x) (inr_not_mem_lift π x)
    have h2 := H.pseudo.le_cap (.inr x)
    simp only [Pi.sub_apply]
    show 0 ≤ cap (.inr x) - s1 (.inr x)
    rw [show s1 (.inr x) = f₀ (.inr x) from h1]; linarith
  have hnegP : negP (negMach (nsIds M₀ H.enum (en 0)) M₀ I) (cap - s1) = some χ := by
    unfold negP
    rw [if_pos hpos]
    exact hχ
  have hfx : fixPath (M₀.pendant e he) cap f₀ (π.lift e he) (msspP (Klein.msspPlaneK M₀))
      (frRef F) (negP (negMach (nsIds M₀ H.enum (en 0)) M₀ I)) =
      s1 + (M₀.pendant e he).cob χ := by
    rw [fixPath_eq_fpState]
    have h' : negP (negMach (nsIds M₀ H.enum (en 0)) M₀ I)
        (cap - (fpState (M₀.pendant e he) cap f₀ (π.lift e he) (msspP (Klein.msspPlaneK M₀))
          (frRef F) (π.lift e he).k).1) = some χ := hnegP
    rw [h']
    rfl
  have hps := (fixPath_spec hG.plane hG.c_nn hG.pseudo X.P hG.mssp_spec hG.fr_spec
    (negP_spec (negMach_spec (nsIds M₀ H.enum (en 0)) M₀ I))).pseudo
  have hfx' : fixPath (M₀.pendant e he) X.c X.f₀ X.P X.mssp X.fr
      (negP (negMach (nsIds M₀ H.enum (en 0)) M₀ I)) = s1 + (M₀.pendant e he).cob χ := hfx
  rw [hfx'] at hps
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
  have qr : ∀ r, (r < 5030 ∨ 5035 < r) → c₁.nreg r = c.nreg r := n1
  have hW1 := hG.w1
  have hl3 := hG.l3
  have hl4 := hG.l4
  -- the reads of `finP` on `c₁`
  obtain ⟨fCW, fCR, -, -, -, -⟩ := hFix
  obtain ⟨sFW, -⟩ := hStt
  have hdk : ∀ l < π.k, ∀ l' < π.k, π.d l ≠ M₀.rev (π.d l') ∧ (π.d l = π.d l' → l = l') ∧
      (M₀.rev (π.d l) = M₀.rev (π.d l') → l = l') := fun l hl' l' hl'' =>
    ⟨fun e' => π.d_ne_rev hl' hl'' e', fun e' => π.d_inj hl' hl'' e',
      fun e' => π.d_inj hl' hl'' (M₀.rev_injective e')⟩
  obtain ⟨χ', hχ'⟩ : ∃ χ', negMach (nsIds M₀ H.enum (en 0)) M₀ I (u₀ - g₀) = some χ' := ⟨χ, hχ⟩
  obtain ⟨c₂, t₂, e₂, ht₂, fFL, fz, fK, fR, fr, frm, fo⟩ :=
    finP9_exec C C₀ hC H.enum hm0 u₀ g₀ hpre I P' c₁ e₁.wb_right (Tb := Tb) (k := π.k)
      (PDb := PDb) (CWb := X.CWb) (CRb := X.CRb) (FWb := X.FWb) (K := X.K) (Wz := Wz)
      (RVb := d' + 4 + m') (RTb := d + 4 + m + m) (CPb := d' + 4 + 3 * m')
      (FLb := d' + 4 + 6 * m') (LABb := LABb) (Z := Z') hχ
      (by rw [qr _ (by omega), r69]) (by rw [qr _ (by omega), r00]) (by rw [qr _ (by omega), r36])
      (by rw [qr _ (by omega), r34]) (by rw [qr _ (by omega), r35]) (by rw [qr _ (by omega), r21])
      (by rw [qr _ (by omega), r10]) (by rw [qr _ (by omega), r01]) (by rw [qr _ (by omega), r02])
      (by rw [qr _ (by omega), r30]) (by rw [qr _ (by omega), r31]) (by rw [qr _ (by omega), r74])
      (by rw [qr _ (by omega), r75]) (by rw [qr _ (by omega), r76]) (by rw [qr _ (by omega), r05])
      (fun i hi => by
        rw [k1' (d' + 4 + m' + i) (by omega), H.rvE hi]; exact H.brv i hi)
      (fun i hi => by
        rw [k1' (d + 4 + m + m + i) (by omega), show d + 4 + m + m + i = d + 4 + 2 * m + i by omega]
        exact H.bsg i hi)
      (fun i hi => by
        rw [k1' (d' + 4 + 3 * m' + i) (by omega)]
        have := (H.fr.cp i (by omega)).1
        rw [H.hen i hi] at this; exact this)
      (fun i hi => by rw [k1' (LABb + i) (by omega), hLAB i hi, pq_lab H hi])
      (fun l hl' => by rw [k1' (PDb + l) (by omega)]; exact (hPDm l hl').1)
      (fun l hl' l' hl'' => by
        rw [k1' (PDb + l) (by omega), k1' (PDb + l') (by omega),
          k1' (d' + 4 + m' + c.nmem (PDb + l')) (by omega),
          k1' (d' + 4 + m' + c.nmem (PDb + l)) (by omega)]
        refine ⟨fun e' => ?_, fun e' => ?_, fun e' => ?_⟩
        · have := congrArg en e'
          rw [(hPDm l hl').2, eR l' hl''] at this
          exact (hdk l hl' l' hl'').1 this
        · have := congrArg en e'
          rw [(hPDm l hl').2, (hPDm l' hl'').2] at this
          exact (hdk l hl' l' hl'').2.1 this
        · have := congrArg en e'
          rw [eR l hl', eR l' hl''] at this
          exact (hdk l hl' l' hl'').2.2 this)
      (fun i hi hn => by
        rw [k1' (d' + 4 + 6 * m' + i) (by omega)]
        have hfl := H.fr.fl i (by omega)
        rw [H.hen i hi] at hfl
        rw [hfl]
        show (Z' : ℤ) + f₀ (.inl (en i)) = Z' + s1 (.inl (en i))
        rw [hoff' (.inl (en i)) fun hd => ?_]
        have hd' := inl_mem_lift hd
        obtain ⟨l, hl', hd''⟩ := π.mem_darts.1 hd'
        have hn' := hn l hl'
        rw [k1' (PDb + l) (by omega), k1' (d' + 4 + m' + c.nmem (PDb + l)) (by omega)] at hn'
        rcases hd'' with e' | e'
        · rw [← (hPDm l hl').2] at e'
          exact hn'.1 (H.en_inj (hPDm l hl').1 hi e'.symm)
        · rw [← eR l hl'] at e'
          exact hn'.2 (H.en_inj (eRl l hl') hi e'.symm))
      (fun l hl' => by
        rw [k1' (X.CWb + l) (by omega), k1' (PDb + l) (by omega), fCW l hl']
        show cap (.inl (π.d l)) = cap (.inl (en (c.nmem (PDb + l))))
        rw [(hPDm l hl').2])
      (fun l hl' => by
        rw [k1' (X.CRb + l) (by omega), k1' (PDb + l) (by omega),
          k1' (d' + 4 + m' + c.nmem (PDb + l)) (by omega), fCR l hl']
        show cap (.inl (M₀.rev (π.d l))) = cap (.inl (en (c.nmem (d' + 4 + m' + c.nmem (PDb + l)))))
        rw [eR l hl'])
      (fun l hl' => by
        rw [k1' (X.FWb + l) (by omega), k1' (PDb + l) (by omega), sFW l hl']
        show s1 (.inl (π.d l)) + X.K = s1 (.inl (en (c.nmem (PDb + l)))) + X.K
        rw [(hPDm l hl').2])
      (fun l hl' => by
        rw [k1' (PDb + l) (by omega), k1' (d' + 4 + m' + c.nmem (PDb + l)) (by omega)]
        show s1 (.inl (en (c.nmem (d' + 4 + m' + c.nmem (PDb + l))))) =
          - s1 (.inl (en (c.nmem (PDb + l))))
        rw [eR l hl', (hPDm l hl').2]
        exact hanti (.inl (π.d l)))
      (fun i hi => hgK' _)
      (fun i hi => hℓK' _)
      (fun i hi => by
        have h1 := hps.le_cap ((M₀.pendant e he).rev (.inl (en i)))
        rw [hps.antisymm (.inl (en i))] at h1
        have h2 := H.fr.cp _ (H.fr.rv i (by omega)).1
        have h3 := (H.fr.rv i (by omega)).2
        rw [H.hen i hi] at h3
        rw [← h3] at h1
        have : (c.nmem (d' + 4 + 3 * m' + c.nmem (d' + 4 + m' + i)) : ℤ) ≤ Z' := by
          exact_mod_cast h2.2
        have h1' : -((s1 + (M₀.pendant e he).cob χ) (.inl (en i))) ≤
            cap (en' (c.nmem (d' + 4 + m' + i))) := h1
        have h4 : -((s1 + (M₀.pendant e he).cob χ) (.inl (en i))) ≤ Z' := by linarith [h2.1]
        show 0 ≤ (Z' : ℤ) + (s1 (.inl (en i)) + M₀.cob χ (en i))
        have e5 : (s1 + (M₀.pendant e he).cob χ) (.inl (en i)) = s1 (.inl (en i)) + M₀.cob χ (en i) :=
          rfl
        linarith)
      hz1 hS ⟨by omega, by omega⟩
      ⟨by omega, by omega, (by clear * - l0 hmm; omega), l1, by omega, l2, l3, l4, l5⟩ hWz hW wL hw2 hw3
      (fun i hi => by
        rw [k1' (d' + 4 + 3 * m' + i) (by omega)]
        exact hv i hi)
      (fun l hl' => by
        have h1 := fCW l hl'
        have h2 := hcK (X.P.d l)
        have h3 : (c₁.nmem (X.CWb + l) : ℤ) ≤ X.K := by rw [k1' _ (by omega), h1]; exact h2
        have h4 : ((16 * X.K + 1 : ℕ) : ℤ) ≤ W := by exact_mod_cast hW1
        push_cast at h4
        have : ((c₁.nmem (X.CWb + l) + X.K + X.K : ℕ) : ℤ) ≤ W := by push_cast; omega
        exact_mod_cast this)
      (fun l hl' => by
        have h1 : (c₁.nmem (X.CRb + l) : ℤ) = X.c ((M₀.pendant e he).rev (X.P.d l)) := by
          rw [k1' (X.CRb + l) (by omega)]; exact fCR l hl'
        have h2 := hcK ((M₀.pendant e he).rev (X.P.d l))
        have h3 : (c₁.nmem (X.FWb + l) : ℤ) = s1 (X.P.d l) + X.K := by
          rw [k1' (X.FWb + l) (by omega)]; exact sFW l hl'
        have h6 := (abs_le.1 (hgK' (X.P.d l))).2
        have h4 : ((16 * X.K + 1 : ℕ) : ℤ) ≤ W := by exact_mod_cast hW1
        push_cast at h4
        have : ((c₁.nmem (X.CRb + l) + c₁.nmem (X.FWb + l) : ℕ) : ℤ) ≤ W := by
          push_cast; clear * - h1 h2 h3 h6 h4; omega
        exact_mod_cast this)
  refine ⟨c₂, _, e₁.seq e₂, by omega, fun i hi => ?_, fz, fun a h1 h2 h3 => ?_,
    fun r hr h2 => ?_, by rw [fr, r1], by rw [frm, rm1], by rw [fo, o1]⟩
  · rw [hfx]
    by_cases him : i < m
    · rw [fFL i him, H.hen i him]
      rfl
    · obtain ⟨x, hx⟩ := H.en_inr hi (by omega)
      rw [fK (d' + 4 + 6 * m' + i) (by omega) (by omega) (Or.inr (by omega)),
        k1' (d' + 4 + 6 * m' + i) (by omega), H.fr.fl i hi, hx]
      show (Z' : ℤ) + f₀ (.inr x) = Z' + (s1 (.inr x) + (M₀.pendant e he).cob χ (.inr x))
      rw [pcob_inr, add_zero, show s1 (.inr x) = f₀ (.inr x) from
        hoff (.inr x) (inr_not_mem_lift π x)]
  · rw [fK a h1 h2 (by omega), k1' a h1]
  · rw [fR r hr h2]; have hr' := hr; unfold KeepR at hr'; exact qr r (by omega)

set_option maxHeartbeats 8000000 in
/-- **The stage loop and the final step of the frozen fix.** -/
theorem fin9_exec (C C₀ : ℕ) (hC : 200000 ≤ C) (c : Config)
    (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j c.nmem) (hj : j < segs.length)
    {q : FpIn} {Q : ℕ} {W : ℕ}
    (hG : (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).Good W)
    (I P' : Input) (hc : WordsBounded W c) {LABb Wz : ℕ}
    (hPDm : ∀ l < (segs[j]'hj).k, c.nmem (c.nreg 9402 + l) < m ∧
      en (c.nmem (c.nreg 9402 + l)) = (segs[j]'hj).d l)
    (hR : (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).Regs c)
    (hFix : (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).Fix c.nmem)
    (hS0 : (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).Stt
      ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).st 0) c.nmem)
    (hImg : (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).Img c.nmem)
    (r69 : c.nreg 9469 = (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).p)
    (r00 : c.nreg 9400 = m) (r36 : c.nreg 9436 = 1)
    (r34 : c.nreg 9434 = d' + 4 + 3 * m') (r35 : c.nreg 9435 = d' + 4 + 6 * m')
    (r21 : c.nreg 9421 = Z') (r01 : c.nreg 9401 = (segs[j]'hj).k)
    (r30 : c.nreg 9430 = d' + 4 + m') (r31 : c.nreg 9431 = d + 4 + m + m)
    (r05 : c.nreg 9405 = LABb) (r9475 : c.nreg 9475 = 0)
    (r71 : c.nreg 9471 = (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).SH)
    (r9474 : c.nreg 9474 = (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).SH +
      ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).Wf + 1))
    (hLAB : ∀ i < m, c.nmem (LABb + i) = olab (nxF d' m' c.nmem) i + 1)
    (hz : ∀ a ≤ Wz, (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).WN < a →
      ¬ ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).SH ≤ a ∧
        a ≤ (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).SH +
          (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).WN) → c.nmem a = 0)
    (hSHz : (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).SH +
      (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).WN ≤ Wz)
    (hPDz : Wz < c.nreg 9402) (hS : 9 * m + 1 + tsz m ≤ Wz + 1) (hWzd : Wz < d)
    (hWzd' : Wz < d') (hWlo : Wz < lo)
    (hlo : d' + 4 + 7 * m' ≤ LABb ∧ LABb + m ≤ (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).CWb ∧
      c.nreg 9402 + (segs[j]'hj).k ≤ (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).CWb ∧
      d + 4 + 3 * m ≤ (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).CWb ∧
      hi ≤ (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).CWb)
    (hWz : rtW m (rtL M₀ (fun y => cap (.inl y) -
      ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).st (segs[j]'hj).k).1 (.inl y))) m ≤ Wz)
    (hW : (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).p + 60 * m + 60 + negT C C₀ m ≤ W)
    (wL : 2 * (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).K + rtL M₀ (fun y => cap (.inl y) -
      ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).st (segs[j]'hj).k).1 (.inl y)) ≤ W)
    (hw2 : spWs m + 205 ≤ W)
    (hw3 : fxWB m (rtL M₀ (fun y => cap (.inl y) -
      ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).st (segs[j]'hj).k).1 (.inl y))) ≤ W)
    (hv : ∀ i < m, c.nmem (d' + 4 + 3 * m' + i) + Z' +
      (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).K +
      (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).K + 2 * rtL M₀ (fun y => cap (.inl y) -
      ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).st (segs[j]'hj).k).1 (.inl y)) ≤ W) :
    ∃ c' t, Exec P' W (.seq loopP (.seq clrP finP)) c c' t ∧
      t ≤ loopT (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).b (segs[j]'hj).k +
        (20 * ((mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).lb + 2 * (segs[j]'hj).k) + 32 +
          finT C C₀ m (segs[j]'hj).k) ∧
      (∀ i < m', (c'.nmem (d' + 4 + 6 * m' + i) : ℤ) = Z' + fixPath (M₀.pendant e he) cap f₀
        ((segs[j]'hj).lift e he) (msspP (Klein.msspPlaneK M₀)) (frRef F)
        (negP (negMach (nsIds M₀ H.enum (en 0)) M₀ I)) (en' i)) ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      (∀ a, Wz < a → a < (mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q).CWb →
        (a < d' + 4 + 6 * m' ∨ d' + 4 + 7 * m' ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, KeepR r → (r < 9477 ∨ 9498 < r) → ¬ SLx.scr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set X := mkP M₀ e he en' (segs[j]'hj) cap f₀ q Q with hX
  have hPk : X.P.k = (segs[j]'hj).k := rfl
  have l1 := hG.l1; have l2 := hG.l2
  obtain ⟨hlo1, hlo2, hlo3, hlo4, hlo5⟩ := hlo
  obtain ⟨c₄, t₄, e₄, ht₄, S4, I4, M4, R4, rr4, rm4, o4⟩ :=
    SLx.loopP_exec' (I := P') hG c hc hR hFix hS0 hImg
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
  have H4 : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j c₄.nmem :=
    H.congr (A0 := X.CWb) (Wz := Wz) (by omega) hlo4 hlo5 hWzd hWzd' hWlo
      (fun a h1 h2 => m4 a (by omega) h2)
  have hLAB4 : ∀ i < m, c₄.nmem (LABb + i) = olab (nxF d' m' c₄.nmem) i + 1 := fun i hi => by
    have hmm := H.mm
    rw [m4 _ (by omega) (by omega), hLAB i hi, pq_lab H hi, pq_lab H4 hi]
  have hPDm4 : ∀ l < (segs[j]'hj).k, c₄.nmem (c.nreg 9402 + l) < m ∧
      en (c₄.nmem (c.nreg 9402 + l)) = (segs[j]'hj).d l := fun l hl' => by
    rw [m4 _ (by omega) (by omega)]; exact hPDm l hl'
  have hz4 : ∀ a ≤ Wz, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → c₄.nmem a = 0 :=
    fun a h1 h2 h3 => by
      rw [M4 a h2 h3 (fun hw => by have := SLx.wr_ge hG hw; omega)]; exact hz a h1 h2 h3
  have hv4 : ∀ i < m, c₄.nmem (d' + 4 + 3 * m' + i) + Z' + X.K + X.K +
      2 * rtL M₀ (fun y => cap (.inl y) - (X.st X.P.k).1 (.inl y)) ≤ W := fun i hi => by
    have hmm := H.mm
    rw [m4 _ (by omega) (by omega)]; exact hv i hi
  have hTb : LABb + m ≤ X.p ∧ d + 4 + 3 * m ≤ X.p ∧ c.nreg 9402 + X.P.k ≤ X.p ∧
      X.CWb + X.P.k ≤ X.p ∧ X.CRb + X.P.k ≤ X.p ∧ X.FWb + X.P.k ≤ X.p := by
    have := hG.l13; have := hG.l12; have := hG.l11; have := hG.l10; have := hG.l9
    have := hG.l8; have := hG.l7; have := hG.l6; have := hG.l5; have := hG.l4; have := hG.l3
    omega
  obtain ⟨c₅, t₅, e₅, ht₅, F5, z5, k5, r5, rr5, rm5, o5⟩ :=
    fixFin9_exec C C₀ hC c₄ H4 hj hG I P' e₄.wb_right (Tb := X.p) (PDb := c.nreg 9402)
      (LABb := LABb) (Wz := Wz) hPDm4
      (by rw [ns _ (by omega), r69]) (by rw [ns _ (by omega), r00]) (by rw [ns _ (by omega), r36])
      (by rw [ns _ (by omega), r34]) (by rw [ns _ (by omega), r35]) (by rw [ns _ (by omega), r21])
      (by rw [ns _ (by omega), g10]) (by rw [ns _ (by omega), r01])
      (by rw [ns _ (by omega)]) (by rw [ns _ (by omega), r30]) (by rw [ns _ (by omega), r31])
      (by rw [ns _ (by omega), g74]) (by rw [ns _ (by omega), g75]) (by rw [ns _ (by omega), g76])
      (by rw [ns _ (by omega), r05]) (by rw [ns _ (by omega), g07]; rfl) (by rw [ns _ (by omega), r9475])
      (by rw [ns _ (by omega), r71]) (by rw [ns _ (by omega), g12])
      (by rw [ns _ (by omega), r9474]) hLAB4 S4 (SLx.fix_congr hG hFix M4) I4 hz4 hSHz hS hWzd
      hWzd' hPDz (show Wz < X.CWb by omega)
      ⟨hlo1, hTb.1, hTb.2.1, hTb.2.2.1, hTb.2.2.2.1, hTb.2.2.2.2.1, hTb.2.2.2.2.2⟩
      hWz hW wL hw2 hw3 hv4
  have ht₄' : t₄ ≤ loopT X.b (segs[j]'hj).k := ht₄
  have ht₅' : t₅ ≤ 20 * (X.lb + 2 * (segs[j]'hj).k) + 32 + finT C C₀ m (segs[j]'hj).k := ht₅
  refine ⟨c₅, _, e₄.seq e₅, by clear * - ht₄' ht₅'; omega, F5, z5, fun a h1 h2 h3 => ?_, fun r hr h1 h2 => ?_,
    by rw [rr5, rr4], by rw [rm5, rm4], by rw [o5, o4]⟩
  · have := hG.l13; have := hG.l12; have := hG.l11; have := hG.l10; have := hG.l9
    have := hG.l8; have := hG.l7; have := hG.l6; have := hG.l5; have := hG.l4; have := hG.l3
    rw [k5 a h1 (by omega) h3, m4 a (by omega) h2]
  · rw [r5 r hr h1, hscr r h2]

end F9b

end BKMNW

end PlanarFlow
