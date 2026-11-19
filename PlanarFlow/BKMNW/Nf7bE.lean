module

public import PlanarFlow.BKMNW.Nf7bD

/-!
# The stage loop of `fixP`, part E: the words of stage `i` and their loads

* `SLx.w X i` (the words `SW` of stage `i` of the state `X.st i`), **`SLx.w_ok`**, `SLx.invB`,
  **`SLx.w_rep`** (`SRep`), the bounds `SLx.w_bF`, `w_bP`, `w_bcw`, `w_bcr`, `w_bf0`, `w_bdv`;
* **`SLx.ldsw_exec`**: from the invariant, `ldP ; swP` leaves the words of the stage in the
  registers `9330 … 9341` (as integers with the offset `K`), within `73` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap SPath WordRAM WordRAM.Machine Monge.FR

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

namespace SLx

variable (X : SLx M)

/-- **The words of stage `i`.** -/
noncomputable def w (i : ℕ) : SW where
  i := i
  Fw := fun l => (X.st i).1 (X.P.d l)
  Pw := fun x => (X.st i).2 (X.β x)
  cw := fun l => X.c (X.P.d l)
  cr := fun l => X.c (M.rev (X.P.d l))
  f0w := fun l => X.f₀ (X.P.d l)
  ia := fun l => X.idx (M.face (X.P.d l))
  ib := fun l => X.idx (M.face (M.rev (X.P.d l)))
  dv := M.div X.f₀ (X.P.p i)

variable {X} {W : ℕ}

lemma w_ok (hG : X.Good W) {i : ℕ} (hi : i < X.P.k) :
    (X.w i).OK X.P X.c X.f₀ X.b X.β X.idx :=
  { hi := hi, cw := rfl, cr := rfl, f0 := fun _ _ => rfl, ia := rfl, ib := rfl, dv := rfl,
    anti0 := hG.pseudo.antisymm, β_mem := hG.β_mem, idx_lt := hG.idx_lt, β_idx := hG.β_idx }

lemma invB (hG : X.Good W) {i : ℕ} (hi : i ≤ X.P.k) : EffInvB M X.c X.f₀ X.P i (X.st i) :=
  fixPath_invB hG.plane hG.c_nn hG.pseudo hG.mssp_spec hG.fr_spec i hi

lemma w_rep (hG : X.Good W) {i : ℕ} (hi : i ≤ X.P.k) :
    SRep X.P X.f₀ X.b X.β (X.st i) (X.w i).Fw (X.w i).Pw := by
  obtain ⟨⟨Φ, hφ, hoff, hanti, -⟩, -, -⟩ := invB hG hi
  exact ⟨fun l _ => rfl, hanti, hoff, fun x _ => rfl⟩

lemma absSum_le_B (hG : X.Good W) : absSum X.c ≤ (X.B : ℤ) := by
  have := hG.bc; have := absSum_nonneg X.c; omega

lemma st_flow (hG : X.Good W) {i : ℕ} (hi : i ≤ X.P.k) (e : D) : |(X.st i).1 e| ≤ (X.B : ℤ) := by
  have h := ((invB hG hi).flow_bound hG.c_nn hG.pseudo e).2
  have hB := Bst_nonneg (D := D) X.c
  have : (i : ℤ) * Bst D X.c ≤ X.P.k * Bst D X.c :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hB
  have := hG.bst
  linarith

lemma st_price (hG : X.Good W) {i : ℕ} (hi : i ≤ X.P.k) (y : F) :
    0 ≤ (X.st i).2 y ∧ (X.st i).2 y ≤ (X.B : ℤ) := by
  obtain ⟨h1, h2⟩ := (invB hG hi).2.2 y
  have hB := Bst_nonneg (D := D) X.c
  have : (i : ℤ) * Bst D X.c ≤ X.P.k * Bst D X.c :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hB
  have := hG.bst; have := absSum_nonneg X.c
  constructor <;> linarith

lemma c_le_B (hG : X.Good W) (e : D) : 0 ≤ X.c e ∧ X.c e ≤ (X.B : ℤ) :=
  ⟨hG.c_nn e, (le_abs_self _).trans ((abs_le_absSum X.c e).trans (absSum_le_B hG))⟩

lemma w_bF (hG : X.Good W) {i : ℕ} (hi : i ≤ X.P.k) (l : ℕ) : |(X.w i).Fw l| ≤ (X.B : ℤ) :=
  st_flow hG hi _

lemma w_bP (hG : X.Good W) {i : ℕ} (hi : i ≤ X.P.k) (x : ℕ) :
    0 ≤ (X.w i).Pw x ∧ (X.w i).Pw x ≤ (X.B : ℤ) := st_price hG hi _

lemma w_bcw (hG : X.Good W) (i : ℕ) : 0 ≤ (X.w i).cw i ∧ (X.w i).cw i ≤ (X.B : ℤ) := c_le_B hG _

lemma w_bcr (hG : X.Good W) (i : ℕ) : 0 ≤ (X.w i).cr i ∧ (X.w i).cr i ≤ (X.B : ℤ) := c_le_B hG _

lemma w_bf0 (hG : X.Good W) (i l : ℕ) : |(X.w i).f0w l| ≤ (X.B : ℤ) := hG.bf0 _

lemma w_bdv (hG : X.Good W) (i : ℕ) : |(X.w i).dv| ≤ (X.B : ℤ) := hG.bdv _

lemma st_succ (i : ℕ) : X.st (i + 1) = fpStep M X.c X.P X.Dst X.fr i (X.st i) :=
  fpState_succ M X.c X.f₀ X.P X.mssp X.fr i

lemma dartAt_even (l : ℕ) : dartAt X.P (l + l) = X.P.d l := by
  simp only [dartAt, show (l + l) % 2 = 0 by omega, ↓reduceIte, show (l + l) / 2 = l by omega]

lemma dartAt_odd (l : ℕ) : dartAt X.P (l + l + 1) = M.rev (X.P.d l) := by
  simp only [dartAt, show (l + l + 1) % 2 = 1 by omega, one_ne_zero, ↓reduceIte,
    show (l + l + 1) / 2 = l by omega]

lemma ET_even (l : ℕ) : X.ET (l + l) = (X.w 0).ia l := by unfold ET; rw [dartAt_even]; rfl

lemma ET_odd (l : ℕ) : X.ET (l + l + 1) = (X.w 0).ib l := by unfold ET; rw [dartAt_odd]; rfl

/-! ### The registers and the fixed arrays under the invariant -/

lemma J_regs {c₀ c : Config} {i : ℕ} (hR : X.Regs c₀) (hJ : X.J c₀ i c) : X.Regs c := by
  have hk := hJ.2.1
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩,
    ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩,
    ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15⟩⟩ := hR
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
  (rwa [hk _ (by unfold scr swScr FrFix.frScr; omega)])

lemma J_fix (hG : X.Good W) {c₀ c : Config} {i : ℕ} (hFx : X.Fix c₀.nmem) (hJ : X.J c₀ i c) :
    X.Fix c.nmem := by
  have hk := hJ.2.2.2.2.1
  have l2 := hG.l2; have l3 := hG.l3; have l4 := hG.l4; have l5 := hG.l5; have l6 := hG.l6
  have l7 := hG.l7; have l8 := hG.l8; have l9 := hG.l9; have l10 := hG.l10; have l11 := hG.l11
  have l12 := hG.l12; have l13 := hG.l13
  have key : ∀ a, X.SH + X.WN < a →
      a < X.FWb ∨ (X.ELb + 2 * X.P.k ≤ a ∧ a < X.PWb) ∨ (X.PRb + X.b ≤ a ∧ a < X.Ob) →
      c.nmem a = c₀.nmem a := fun a h1 h2 =>
    hk a (by omega) (by omega) (by unfold Wr; omega)
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hFx
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun a ha => ?_,
    fun e he => ?_⟩
  · rw [key _ (by omega) (by omega)]; exact f1 l hl
  · rw [key _ (by omega) (by omega)]; exact f2 l hl
  · rw [key _ (by omega) (by omega)]; exact f3 l hl
  · rw [key _ (by omega) (by omega)]; exact f4 l hl
  · rw [key _ (by omega) (by omega)]; exact f5 a ha
  · rw [key _ (by omega) (by omega)]; exact f6 e he

/-! ### Loading the words and `swP` -/

set_option maxHeartbeats 1000000 in
/-- **`ldP ; swP` from the invariant**: the words of stage `i` in the registers. -/
theorem ldsw_exec {I : Input} (hG : X.Good W) {c₀ : Config} (hR : X.Regs c₀)
    (hFx : X.Fix c₀.nmem) {i : ℕ} (hi : i < X.P.k) (c : Config) (hc : WordsBounded W c)
    (hJ : X.J c₀ i c) :
    ∃ c' t, Exec I W (.seq ldP swP) c c' t ∧ t ≤ 73 ∧
      (c'.nreg 9330 : ℤ) = (X.w i).cob + X.K ∧
      c'.nreg 9333 = (if (X.w i).bv < 0 then 1 else 0) ∧
      (c'.nreg 9337 : ℤ) = (X.w i).f2 + X.K ∧
      (c'.nreg 9341 : ℤ) = |(X.w i).bv| - (X.w i).val0 ∧
      (c'.nreg 9338 = 1 ↔ (X.w i).skip) ∧ c'.nreg 9338 ≤ 1 ∧
      c'.nreg 9339 = (X.w i).root ∧
      (c'.nreg 9312 : ℤ) = (X.w i).Pw ((X.w i).ia i) ∧
      (c'.nreg 9313 : ℤ) = (X.w i).Pw ((X.w i).ib i) ∧
      c'.nreg 9319 = (X.w i).ia i ∧ c'.nreg 9320 = (X.w i).ib i ∧
      c'.nreg 9372 = i ∧ c'.nreg 9510 = 1 ∧
      (∀ r, ¬ (swScr r ∨ (9311 ≤ r ∧ r ≤ 9320) ∨ r = 9372 ∨ (9505 ≤ r ∧ r ≤ 9511)) →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩, -, -⟩ := J_regs hR hJ
  obtain ⟨fCW, fCR, fF0, fDV, fET, -⟩ := J_fix hG hFx hJ
  obtain ⟨j00, -, ⟨sFW, sPW⟩, -⟩ := hJ
  have l2 := hG.l2; have l3 := hG.l3; have l4 := hG.l4; have l5 := hG.l5; have l6 := hG.l6
  have l7 := hG.l7; have l8 := hG.l8; have l9 := hG.l9; have l10 := hG.l10; have l11 := hG.l11
  have l12 := hG.l12; have l13 := hG.l13; have l14 := hG.l14; have w1 := hG.w1
  have hK := hG.hK
  have hia : X.ET (i + i) = (X.w i).ia i := ET_even i
  have hib : X.ET (i + i + 1) = (X.w i).ib i := ET_odd i
  have hia_lt : (X.w i).ia i < X.b := by rw [← hia]; exact ET_lt hG (by omega)
  have hib_lt : (X.w i).ib i < X.b := by rw [← hib]; exact ET_lt hG (by omega)
  have eia : c.nmem (X.ETb + i + i) = (X.w i).ia i := by
    rw [show X.ETb + i + i = X.ETb + (i + i) by ring, fET _ (by omega), hia]
  have eib : c.nmem (X.ETb + i + i + 1) = (X.w i).ib i := by
    rw [show X.ETb + i + i + 1 = X.ETb + (i + i + 1) by ring, fET _ (by omega), hib]
  have bF := w_bF hG hi.le
  have bP := w_bP hG hi.le
  have hFi : (c.nmem (X.FWb + i) : ℤ) = (X.w i).Fw i + X.K := sFW i hi
  have hFi1 : 0 < i → (c.nmem (X.FWb + (i - 1)) : ℤ) = (X.w i).Fw (i - 1) + X.K :=
    fun h => sFW (i - 1) (by omega)
  have hPA : (c.nmem (X.PWb + (X.w i).ia i) : ℤ) = (X.w i).Pw ((X.w i).ia i) := sPW _ hia_lt
  have hPB : (c.nmem (X.PWb + (X.w i).ib i) : ℤ) = (X.w i).Pw ((X.w i).ib i) := sPW _ hib_lt
  have hCW : (c.nmem (X.CWb + i) : ℤ) = (X.w i).cw i := fCW i hi
  have hCR : (c.nmem (X.CRb + i) : ℤ) = (X.w i).cr i := fCR i hi
  have hF0 : ∀ l < X.P.k, (c.nmem (X.F0b + l) : ℤ) = (X.w i).f0w l + X.K := fun l hl => fF0 l hl
  have hDV : (c.nmem (X.DVb + i) : ℤ) = (X.w i).dv + X.K := fDV i hi
  have bFi := bF i; have bFi1 := bF (i - 1); have bPA := bP ((X.w i).ia i)
  have bPB := bP ((X.w i).ib i); have bcw := w_bcw hG i; have bcr := w_bcr hG i
  have bf0 := w_bf0 hG i i; have bf01 := w_bf0 hG i (i - 1); have bdv := w_bdv hG i
  rw [abs_le] at bFi bFi1 bf0 bf01 bdv
  have nF1 : 0 < i → c.nmem (X.FWb + (i - 1)) + X.K ≤ W := fun h => by
    have := hFi1 h; omega
  obtain ⟨c₁, t₁, e₁, ht₁, b510, b511, b72, b11, b19, b20, b12, b13, b14, b15, b16, b17, b18,
      bk, bm, br, brm, bo⟩ :=
    ldP_exec (P := I) c hc j00 a1 a6 a11 a8 a4 a5 a9 a10
      ⟨by omega, by omega, by rw [eia]; omega, by rw [eib]; omega, by omega, by omega, by omega,
        by omega, by
          have e : (c.nmem (X.FWb + (i - 1)) : ℤ) = (X.w i).Fw (i - 1) + X.K := sFW (i - 1) (by omega)
          omega⟩
  rw [eia] at b19 b12; rw [eib] at b20 b13
  -- the natural inputs of `swP`
  set F := c.nmem (X.FWb + i) with hF
  set PA := c.nmem (X.PWb + (X.w i).ia i) with hPAd
  set PB := c.nmem (X.PWb + (X.w i).ib i) with hPBd
  set CW := c.nmem (X.CWb + i) with hCWd
  set CR := c.nmem (X.CRb + i) with hCRd
  set F0 := c.nmem (X.F0b + i) with hF0d
  set DV := c.nmem (X.DVb + i) with hDVd
  set D1 := (if 0 < i then c.nmem (X.FWb + (i - 1)) + X.K - c.nmem (X.F0b + (i - 1)) else X.K)
    with hD1d
  have hD1 : (D1 : ℤ) = (if 0 < i then (X.w i).Fw (i - 1) - (X.w i).f0w (i - 1) else 0) + X.K := by
    rw [hD1d]
    by_cases h : 0 < i
    · have e1 := hFi1 h; have e2 := hF0 (i - 1) (by omega)
      simp only [h, ↓reduceIte]
      push_cast [Nat.cast_sub (show c.nmem (X.F0b + (i - 1)) ≤ c.nmem (X.FWb + (i - 1)) + X.K by
        omega)]
      omega
    · simp only [h, ↓reduceIte]; ring
  have q1 : ∀ r, ¬ ((9311 ≤ r ∧ r ≤ 9320) ∨ r = 9372 ∨ (9505 ≤ r ∧ r ≤ 9511)) →
      c₁.nreg r = c.nreg r := fun r h => bk r (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, g30, g31, g32, g33, g34, g35, g36, g37, g41, g38, g39, g40, gk, gm, gr,
      grm, go⟩ :=
    swP_exec (P := I) c₁ e₁.wb_right (K := X.K) (F := F) (PA := PA) (PB := PB) (CW := CW)
      (CR := CR) (F0 := F0) (DV := DV) (D1 := D1) (IA := (X.w i).ia i) (IB := (X.w i).ib i)
      (by rw [q1 _ (by omega), a1]) b11 b12 b13 b14 b15 b16 b17 b18 b19 b20
      (by omega) (by omega) (by omega) (by omega) (by omega) w1
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩ := swP_link (X.w i) (K := X.K) (F := F)
    (PA := PA) (PB := PB) (CW := CW) (CR := CR) (F0 := F0) (DV := DV) (D1 := D1)
    (B := 2 * (X.B : ℤ)) hFi hPA hPB hCW hCR (hF0 i hi) hDV hD1
    (by rw [show (X.w i).i = i from rfl, abs_le]; constructor <;> linarith)
    (by omega) (by omega) (by omega) (by omega)
    (by rw [show (X.w i).i = i from rfl, abs_le]; constructor <;> linarith)
    (by rw [abs_le]; constructor <;> linarith)
    (by
      rw [show (X.w i).i = i from rfl]
      split_ifs
      · rw [abs_le]; constructor <;> linarith
      · simp only [abs_zero]; positivity)
    (by omega)
  refine ⟨c₂, _, .seq e₁ e₂, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr => ?_, by rw [gm, bm], by rw [gr, br], by rw [grm, brm], by rw [go, bo]⟩
  · rw [g30]; exact k1
  · rw [g33]; by_cases h : (X.w i).bv < 0
    · simp only [h, ↓reduceIte, k4.2 h]
    · simp only [h, ↓reduceIte, show ¬ (nBV X.K F PA PB CW CR F0 DV D1 < X.K) from
        fun h' => h (k4.1 h')]
  · rw [g37]; exact k8
  · rw [g41]; exact k9
  · rw [g38]; exact k10
  · rw [g38]; omega
  · rw [g39]; unfold SW.root
    by_cases h : (X.w i).bv < 0
    · simp only [h, ↓reduceIte, k4.2 h]; rfl
    · simp only [h, ↓reduceIte, show ¬ (nBV X.K F PA PB CW CR F0 DV D1 < X.K) from
        fun h' => h (k4.1 h')]; rfl
  · rw [gk _ (by unfold swScr; omega), b12]; exact hPA
  · rw [gk _ (by unfold swScr; omega), b13]; exact hPB
  · rw [gk _ (by unfold swScr; omega), b19]
  · rw [gk _ (by unfold swScr; omega), b20]
  · rw [gk _ (by unfold swScr; omega), b72]
  · rw [gk _ (by unfold swScr; omega), b510]
  · rw [gk r (fun h => hr (Or.inl h)), q1 r (fun h => hr (Or.inr h))]

end SLx

end BKMNW

end PlanarFlow
