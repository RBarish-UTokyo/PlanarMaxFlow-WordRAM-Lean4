module

public import PlanarFlow.BKMNW.Nf7bE

/-!
# The stage loop of `fixP`, part F: the lengths, the prices and the image of a stage

* `MsCall.sIdx_lt` (the sorted indices are arc numbers);
* `SLx.pm₁`, `SLx.Lz₁` (the prices and the lengths of the explicit arcs of stage `i`);
* **`SLx.hsA_exec`**: from the words of a stage that is not skipped, `elP ; prP ; imU` writes the
  lengths `EL`, the offset prices `PR` and turns the resident image and its shadow into the image of
  the stage's FR input `X.prm (pm₁ i) root (Lz₁ i)` (with `FrImgB`), within `68 k + 26 b + 43`
  steps, nothing else above the image written outside `PR`, `EL`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap SPath WordRAM WordRAM.Machine Monge.FR

theorem MsCall.sIdx_lt {ET : ℕ → ℕ} {mE b : ℕ} (h : ∀ a < mE, ET a < b) {e : ℕ} (he : e < mE) :
    MsCall.sIdx ET mE b e < mE := by
  have hlen : (pre (MsCall.fiL ET mE) b).length = mE := by
    have := MsCall.frPrm_m (b := b) (Dm := fun _ _ => 0) (pm := 0) (r := 0) (ET := ET) (EH := id)
      (Lz := 0) (mE := mE) h
    rw [← MsCall.length_pre_fiL ET id 0 mE b]; exact this
  unfold MsCall.sIdx
  rw [List.getD_eq_getElem _ _ (by omega)]
  have he' : e < (pre (MsCall.fiL ET mE) b).length := by omega
  have hm := (mem_pre.1 (List.getElem_mem he')).1
  generalize (pre (MsCall.fiL ET mE) b)[e] = q at hm ⊢
  rw [MsCall.fiL, MsCall.csList_ones, List.mem_map] at hm
  obtain ⟨a, ha, rfl⟩ := hm
  exact List.mem_range.1 ha

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

namespace SLx

variable (X : SLx M)

/-- The prices of stage `i` at the corners. -/
noncomputable def pm₁ (i : ℕ) (x : ℕ) : ℤ := (X.st i).2 (X.β x)

/-- The lengths of the explicit arcs of stage `i`. -/
noncomputable def Lz₁ (i : ℕ) (a : ℕ) : ℤ :=
  (X.w i).lenD X.P X.c (X.st i).1 (X.st i).2 (dartAt X.P a)

variable {X} {W : ℕ}

lemma Mbw_eq : (X.Mbw : ℤ) = 4 * absSum X.c + 1 := by
  unfold Mbw; have := absSum_nonneg X.c; omega

lemma root_lt (hG : X.Good W) {i : ℕ} (hi : i < X.P.k) : (X.w i).root < X.b := by
  have hd := X.P.d_mem i hi
  unfold SW.root; split_ifs
  · exact hG.idx_lt _ (X.P.face_mem (X.P.rev_mem_darts hd))
  · exact hG.idx_lt _ (X.P.face_mem hd)

/-- The lengths of the explicit arcs of stage `i` in words, at `2l` and `2l + 1`. -/
lemma Lz₁_even (hG : X.Good W) {i l : ℕ} (hi : i < X.P.k) (hl : l < X.P.k) :
    X.Lz₁ i (l + l) = (X.w i).elD (4 * absSum X.c + 1) (fun l => X.c (X.P.d l)) l := by
  unfold Lz₁; rw [dartAt_even]
  exact ((X.w i).lenD_words X.c (w_ok hG hi) (w_rep hG hi.le) hl).1

lemma Lz₁_odd (hG : X.Good W) {i l : ℕ} (hi : i < X.P.k) (hl : l < X.P.k) :
    X.Lz₁ i (l + l + 1) = (X.w i).elR (4 * absSum X.c + 1) (fun l => X.c (M.rev (X.P.d l))) l := by
  unfold Lz₁; rw [dartAt_odd]
  exact ((X.w i).lenD_words X.c (w_ok hG hi) (w_rep hG hi.le) hl).2

lemma Lz₁_bnd (hG : X.Good W) {i a : ℕ} (hi : i < X.P.k) (ha : a < 2 * X.P.k) :
    |X.Lz₁ i a| ≤ 7 * (X.B : ℤ) := by
  have hMb : 0 ≤ 4 * absSum X.c + 1 ∧ 4 * absSum X.c + 1 ≤ (X.B : ℤ) :=
    ⟨by have := absSum_nonneg X.c; omega, hG.bc⟩
  obtain ⟨l, rfl | rfl⟩ : ∃ l, a = l + l ∨ a = l + l + 1 := ⟨a / 2, by omega⟩
  · rw [Lz₁_even hG hi (by omega)]
    exact (X.w i).elD_bnd (w_bF hG hi.le) (w_bP hG hi.le) (w_bcw hG i) (w_bcr hG i) (w_bf0 hG i)
      (w_bdv hG i) hMb l (c_le_B hG _)
  · rw [Lz₁_odd hG hi (by omega)]
    exact (X.w i).elR_bnd (w_bF hG hi.le) (w_bP hG hi.le) (w_bcw hG i) (w_bcr hG i) (w_bf0 hG i)
      (w_bdv hG i) hMb l (c_le_B hG _)

/-- The bounds of the stage's FR input. -/
lemma frImgB₁ (hG : X.Good W) {i : ℕ} (hi : i < X.P.k) :
    MsCall.FrImgB X.b X.Dm (X.pm₁ i) (X.w i).root (2 * X.P.k) X.ET X.EH (X.Lz₁ i) X.L where
  b_pos := b_pos hG
  r_lt := root_lt hG hi
  et := fun a ha => ET_lt hG ha
  eh := fun a ha => EH_lt hG ha
  dm := hG.dmL
  pm := fun x hx => by
    have := st_price hG hi.le (X.β x); have := hG.hL
    unfold pm₁; rw [abs_le]; constructor <;> omega
  lz := fun a ha => by
    have h1 := Lz₁_bnd hG hi ha; have := hG.hL
    rw [abs_le] at h1 ⊢; constructor <;> omega

set_option maxHeartbeats 1600000 in
/-- **`elP ; prP ; imU`**: the image of the stage's FR input, live and shadow. -/
theorem hsA_exec {I : Input} (hG : X.Good W) {i : ℕ} (hi : i < X.P.k) (c : Config)
    (hc : WordsBounded W c) (hR : X.Regs c) (hFx : X.Fix c.nmem) (hS : X.Stt (X.st i) c.nmem)
    (hImg : X.Img c.nmem)
    (r33 : c.nreg 9333 = if (X.w i).bv < 0 then 1 else 0)
    (r30 : (c.nreg 9330 : ℤ) = (X.w i).cob + X.K) (r37 : (c.nreg 9337 : ℤ) = (X.w i).f2 + X.K)
    (r41 : (c.nreg 9341 : ℤ) = |(X.w i).bv| - (X.w i).val0) (r72 : c.nreg 9372 = i)
    (r510 : c.nreg 9510 = 1) :
    ∃ c' t, Exec I W (.seq elP (.seq prP MsCall.imU)) c c' t ∧
      t ≤ 68 * X.P.k + 26 * X.b + 43 ∧
      (∀ a ≤ X.WN, c'.nmem a = (FrFix.frCfgN (X.prm (X.pm₁ i) (X.w i).root (X.Lz₁ i)) X.L).nmem a ∧
        c'.nmem (X.SH + a) =
          (FrFix.frCfgN (X.prm (X.pm₁ i) (X.w i).root (X.Lz₁ i)) X.L).nmem a) ∧
      (∀ a, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → ¬ (X.PRb ≤ a ∧ a < X.PRb + X.b) →
        ¬ (X.ELb ≤ a ∧ a < X.ELb + 2 * X.P.k) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 9370 → (r < 9378 ∨ 9387 < r) → r ≠ 9520 → r ≠ 9521 → r ≠ 9522 → r ≠ 8126 →
        (r < 8140 ∨ 8149 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩,
    ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩, -⟩ := hR
  obtain ⟨fCW, fCR, fF0, fDV, fET, fSI⟩ := hFx
  obtain ⟨sFW, sPW⟩ := hS
  obtain ⟨pm₀, r₀, Lz₀, hb₀, himg⟩ := hImg
  have l1 := hG.l1; have l2 := hG.l2; have l3 := hG.l3; have l4 := hG.l4; have l5 := hG.l5
  have l6 := hG.l6; have l7 := hG.l7; have l8 := hG.l8; have l9 := hG.l9; have l10 := hG.l10
  have l11 := hG.l11; have l12 := hG.l12; have l13 := hG.l13; have l14 := hG.l14
  have w1 := hG.w1; have w2 := hG.w2; have hK := hG.hK; have hL := hG.hL
  have hWf := X.lb_le_Wf
  have hWN : 2 * X.Wf + 1 ≤ X.WN := by unfold WN; omega
  have hlb : X.b * X.b + X.b + X.b + 1 + 2 * X.P.k = X.lb := rfl
  have hb1 := b_pos hG
  have hw := w_ok hG hi
  have bF := w_bF hG hi.le
  have bP := w_bP hG hi.le
  obtain ⟨wb1, wb2, wb3, wb4, wb5, wb6, wb7, wb8⟩ :=
    (X.w i).wbnd bF bP (w_bcw hG i) (w_bcr hG i) (w_bf0 hG i) (w_bdv hG i)
  rw [abs_le] at wb1 wb6
  have hMb := Mbw_eq (X := X)
  have hBc := hG.bc
  have hc0 : 0 ≤ absSum X.c := absSum_nonneg X.c
  have hCWv : ∀ l < X.P.k, c.nmem (X.CWb + l) ≤ X.B := fun l hl => by
    have := fCW l hl; have := c_le_B hG (X.P.d l); omega
  have hCRv : ∀ l < X.P.k, c.nmem (X.CRb + l) ≤ X.B := fun l hl => by
    have := fCR l hl; have := c_le_B hG (M.rev (X.P.d l)); omega
  have hFWv : ∀ l < X.P.k, c.nmem (X.FWb + l) ≤ X.B + X.K := fun l hl => by
    have e := sFW l hl; have := bF l; rw [abs_le] at this
    have e' : (c.nmem (X.FWb + l) : ℤ) = (X.w i).Fw l + X.K := e
    omega
  have hNG : c.nreg 9333 ≤ 1 := by rw [r33]; split_ifs <;> omega
  -- `elP`
  obtain ⟨c₁, t₁, e₁, ht₁, E1, Em, Ek, Er, Erm, Eo⟩ :=
    elP_exec (P := I) c hc (K := X.K) (k := X.P.k) (i := i) (Mbw := X.Mbw) (CWb := X.CWb)
      (CRb := X.CRb) (FWb := X.FWb) (ELb := X.ELb) a2 r72 a3 a4 a5 a6 a7 a1 rfl rfl rfl rfl hi
      hNG (fun l hl => by have := hCWv l hl; omega) (fun l hl => by have := hCRv l hl; omega)
      (fun l hl => by have := hFWv l hl; omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) ⟨by omega, by omega, by omega⟩ (by omega)
  -- the lengths as integers
  have hEL : ∀ a < 2 * X.P.k, (c₁.nmem (X.ELb + a) : ℤ) = X.Lz₁ i a + X.K := by
    intro a ha
    obtain ⟨l, rfl | rfl⟩ : ∃ l, a = l + l ∨ a = l + l + 1 := ⟨a / 2, by omega⟩
    · have hl : l < X.P.k := by omega
      obtain ⟨v1, -⟩ := elP_val (X.w i) (K := X.K) (Mbw := X.Mbw) (NG := c.nreg 9333)
        (XV := c.nreg 9341) (COB := c.nreg 9330) (F2 := c.nreg 9337) (Mb := 4 * absSum X.c + 1)
        (cw := fun l => X.c (X.P.d l)) (cr := fun l => X.c (M.rev (X.P.d l)))
        (CW := fun l => c.nmem (X.CWb + l)) (CR := fun l => c.nmem (X.CRb + l))
        (FW := fun l => c.nmem (X.FWb + l)) (l := l) (fCW l hl) (fCR l hl) (sFW l hl)
        (fCW i hi) (fCR i hi) hMb r33 r41 r30 r37
        (by have := bF l; rw [abs_le] at this; have := hG.c_nn (X.P.d l); show (X.w i).Fw l ≤ X.c (X.P.d l) + X.K; omega)
        (by have := hG.c_nn (X.P.d i); show (X.w i).f2 ≤ X.c (X.P.d i) + X.K; omega)
        (by show (X.w i).cob ≤ |(X.w i).bv| - (X.w i).val0 + X.K; omega)
      rw [show X.ELb + (l + l) = X.ELb + 2 * l by ring, (E1 l hl).1, Lz₁_even hG hi hl]
      exact v1
    · have hl : l < X.P.k := by omega
      obtain ⟨-, v2⟩ := elP_val (X.w i) (K := X.K) (Mbw := X.Mbw) (NG := c.nreg 9333)
        (XV := c.nreg 9341) (COB := c.nreg 9330) (F2 := c.nreg 9337) (Mb := 4 * absSum X.c + 1)
        (cw := fun l => X.c (X.P.d l)) (cr := fun l => X.c (M.rev (X.P.d l)))
        (CW := fun l => c.nmem (X.CWb + l)) (CR := fun l => c.nmem (X.CRb + l))
        (FW := fun l => c.nmem (X.FWb + l)) (l := l) (fCW l hl) (fCR l hl) (sFW l hl)
        (fCW i hi) (fCR i hi) hMb r33 r41 r30 r37
        (by have := bF l; rw [abs_le] at this; have := hG.c_nn (X.P.d l); show (X.w i).Fw l ≤ X.c (X.P.d l) + X.K; omega)
        (by have := hG.c_nn (X.P.d i); show (X.w i).f2 ≤ X.c (X.P.d i) + X.K; omega)
        (by show (X.w i).cob ≤ |(X.w i).bv| - (X.w i).val0 + X.K; omega)
      rw [show X.ELb + (l + l + 1) = X.ELb + 2 * l + 1 by ring, (E1 l hl).2, Lz₁_odd hG hi hl]
      exact v2
  have hELv : ∀ a < 2 * X.P.k, c₁.nmem (X.ELb + a) ≤ 2 * X.K := fun a ha => by
    have e := hEL a ha; have := Lz₁_bnd hG hi ha; rw [abs_le] at this; omega
  have q1 : ∀ r, r ≠ 9370 → (r < 9378 ∨ 9387 < r) → c₁.nreg r = c.nreg r := Ek
  -- `prP`
  obtain ⟨c₂, t₂, e₂, ht₂, P1, Pm, Pk, Pr, Prm, Po⟩ :=
    prP_exec (P := I) c₁ e₁.wb_right (b := X.b) (K := X.K) (PWb := X.PWb) (PRb := X.PRb)
      (by rw [q1 _ (by omega) (by omega), b1]) (by rw [q1 _ (by omega) (by omega), a8])
      (by rw [q1 _ (by omega) (by omega), b5]) (by rw [q1 _ (by omega) (by omega), a1])
      (by rw [q1 _ (by omega) (by omega), r510]) l10
      ⟨by omega, fun x hx => by
        rw [Em _ (by omega)]
        have e := sPW x hx; have := st_price hG hi.le (X.β x); omega⟩
  have q2 : ∀ r, r ≠ 9370 → (r < 9378 ∨ 9387 < r) → r ≠ 9520 → r ≠ 9521 → r ≠ 9522 →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 => by rw [Pk r h3 h4 h5, q1 r h1 h2]
  have m2 : ∀ a, ¬ (X.PRb ≤ a ∧ a < X.PRb + X.b) → ¬ (X.ELb ≤ a ∧ a < X.ELb + 2 * X.P.k) →
      c₂.nmem a = c.nmem a := fun a h1 h2 => by rw [Pm a h1, Em a h2]
  have hPRv : ∀ x < X.b, (c₂.nmem (X.PRb + x) : ℤ) = X.pm₁ i x + X.K := fun x hx => by
    rw [P1 x hx, Em _ (by omega)]; push_cast; rw [sPW x hx]; rfl
  -- `imU`
  have hSIv : ∀ e < 2 * X.P.k, c₂.nmem (X.SIb + e) = MsCall.sIdx X.ET (2 * X.P.k) X.b e :=
    fun e he => by rw [m2 _ (by omega) (by omega)]; exact fSI e he
  have hSIl : ∀ e < 2 * X.P.k, MsCall.sIdx X.ET (2 * X.P.k) X.b e < 2 * X.P.k := fun e he =>
    MsCall.sIdx_lt (fun a ha => ET_lt hG ha) he
  have hKp : X.Mo - X.K % X.Mo ≤ X.Mo := Nat.sub_le _ _
  have hc2 : ∀ a < 2 * X.P.k, c₂.nmem (X.ELb + a) = c₁.nmem (X.ELb + a) := fun a ha =>
    Pm _ (by omega)
  have s2 : ∀ r, ¬ (r = 9370 ∨ (9378 ≤ r ∧ r ≤ 9387) ∨ (9520 ≤ r ∧ r ≤ 9522)) →
      c₂.nreg r = c.nreg r := fun r h => q2 r (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨c₃, t₃, e₃, ht₃, U1, U2, Um, Uk, Ur, Urm, Uo⟩ :=
    MsCall.imU_exec (P := I) c₂ e₂.wb_right (b := X.b) (mE := 2 * X.P.k) (Bl := X.Wf + 1)
      (Bs := X.SH + (X.Wf + 1)) (pb := X.b * X.b) (lb := X.lb) (PRb := X.PRb) (SIb := X.SIb)
      (ELb := X.ELb) (Kp := X.Mo - X.K % X.Mo) (Mo := X.Mo)
      (by rw [s2 _ (by omega), b1]) (by rw [s2 _ (by omega), b2]) (by rw [s2 _ (by omega), b3])
      (by rw [s2 _ (by omega), b4]) (by rw [s2 _ (by omega), b5]) (by rw [s2 _ (by omega), b6])
      (by rw [s2 _ (by omega), b7]) (by rw [s2 _ (by omega), b8]) (by rw [s2 _ (by omega), b9])
      (by rw [s2 _ (by omega), b10]) (by rw [s2 _ (by omega), b11]) (by rw [s2 _ (by omega), b12])
      (by unfold SLx.lb; omega) (by omega) (by omega) (by omega)
      (fun e he => by
        rw [hSIv e he]
        have := hSIl e he
        refine ⟨by omega, by omega, ?_⟩
        rw [hc2 _ this]; have := hELv _ this; omega)
      (fun x hx => by have e := hPRv x hx; have := st_price hG hi.le (X.β x); unfold pm₁ at e; omega)
      (by omega) (by omega) (by omega)
  have hM0 : 0 < X.Mo := by unfold Mo; omega
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, ?_, fun a h1 h2 h3 h4 => ?_,
    fun r h1 h2 h3 h4 h5 h6 h7 => ?_, by rw [Ur, Pr, Er], by rw [Urm, Prm, Erm], by rw [Uo, Po, Eo]⟩
  · refine img_upd hG hb₀ (frImgB₁ hG hi) (nm := c.nmem) (nm' := c₃.nmem) himg
      (fun x hx => ?_) (fun e he => ?_) (fun a ha h1 h2 h3 h4 => ?_)
    · obtain ⟨u1, u2⟩ := U1 x hx
      rw [u1, u2, and_self]
      exact MsCall.res_off hM0 _ (hPRv x hx)
    · obtain ⟨u1, u2⟩ := U2 e he
      have hs := hSIl e he
      rw [u1, u2, and_self, hSIv e he, hc2 _ hs]
      exact MsCall.res_off hM0 _ (hEL _ hs)
    · rw [Um a h1 h2 h3 h4]
      exact m2 a (by omega) (by omega)
  · rw [Um a (by omega) (by omega) (by omega) (by omega)]; exact m2 a h3 h4
  · rw [Uk r (by omega) h6, q2 r h1 h2 h3 h4 h5]

end SLx

end BKMNW

end PlanarFlow
