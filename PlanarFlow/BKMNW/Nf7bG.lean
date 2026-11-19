module

public import PlanarFlow.BKMNW.Nf7bF
public import PlanarFlow.BKMNW.CsScale

/-!
# The stage loop of `fixP`, part G: the FR run of a stage and the new state

* the fields of the stage inputs (`SLx.prm_lb`, …), `SLx.frCost_prm`
  (`frCost ≤ 6300 (b lg² b + 2k lg b)`);
* **`SLx.hsB_exec`**: from the image of the stage input (live and shadow) and the words of a
  stage that is not skipped, `rtP ; frRun ; rdP ; fwP` runs FR-Dijkstra on the resident image
  (`frRun_exec`, feasibility `SW.feas`, bounds `frPrm_xb`), reads the answers (`SW.dw_eq`) into
  the new prices `PW` and writes `FW[i]`: the arrays hold the state `X.st (i + 1)` (`SRep.step`,
  `fpState_succ`), the image and its shadow are kept, within
  `108 · 6300 (b lg² b + 2k lg b) + 30 b + 1020` steps.
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

variable {X : SLx M} {W : ℕ}

lemma prm_lb (hG : X.Good W) (pm : ℕ → ℤ) (r : ℕ) (Lz : ℕ → ℤ) : (X.prm pm r Lz).lb = X.lb := by
  rw [prm, MsCall.frPrm_lb (fun a ha => ET_lt hG ha)]; rfl

lemma prm_sb (hG : X.Good W) (pm : ℕ → ℤ) (r : ℕ) (Lz : ℕ → ℤ) :
    (X.prm pm r Lz).sb = X.lb + 2 * X.P.k := by
  rw [prm, MsCall.frPrm_sb (fun a ha => ET_lt hG ha)]; rfl

lemma prm_db (hG : X.Good W) (pm : ℕ → ℤ) (r : ℕ) (Lz : ℕ → ℤ) :
    (X.prm pm r Lz).db = X.lb + 2 * X.P.k + X.b := by
  rw [prm, MsCall.frPrm_db (fun a ha => ET_lt hG ha)]; rfl

lemma prm_wb (hG : X.Good W) (pm : ℕ → ℤ) (r : ℕ) (Lz : ℕ → ℤ) :
    (X.prm pm r Lz).wb = X.lb + 2 * X.P.k + X.b + X.b := by
  rw [prm, MsCall.frPrm_wb (fun a ha => ET_lt hG ha)]; rfl

lemma prm_m (hG : X.Good W) (pm : ℕ → ℤ) (r : ℕ) (Lz : ℕ → ℤ) :
    (X.prm pm r Lz).m = 2 * X.P.k := MsCall.frPrm_m (fun a ha => ET_lt hG ha)

lemma frCost_prm (hG : X.Good W) {pm : ℕ → ℤ} {r : ℕ} {Lz : ℕ → ℤ}
    (hb : MsCall.FrImgB X.b X.Dm pm r (2 * X.P.k) X.ET X.EH Lz X.L) :
    frCost (X.prm pm r Lz) ≤ 6300 * (X.b * lg X.b ^ 2 + 2 * X.P.k * lg X.b) := by
  have h := frCost_le_fr (MsCall.frPrm_lay hb)
  have e1 : (MsCall.frPrm X.b X.Dm pm r X.ET X.EH Lz (2 * X.P.k)).N = X.b := rfl
  have e2 : (MsCall.frPrm X.b X.Dm pm r X.ET X.EH Lz (2 * X.P.k)).m = 2 * X.P.k :=
    prm_m hG pm r Lz
  rw [e1, e2] at h
  have := heap_lg_le X.b
  refine h.trans ?_
  gcongr

/-- The next state after a stage that is not skipped, at the corners and on the path. -/
lemma st_next (hG : X.Good W) {i : ℕ} (hi : i < X.P.k) (hsk : ¬ (X.w i).skip) :
    (∀ l < X.P.k, (X.st (i + 1)).1 (X.P.d l) =
      if l = i then (X.w i).f3 ((X.w i).dw X.P X.c X.Dst X.fr X.β (X.st i)) else (X.w i).Fw l) ∧
    ∀ x < X.b, (X.st (i + 1)).2 (X.β x) =
      (X.w i).dw X.P X.c X.Dst X.fr X.β (X.st i) x + (X.w i).Pw (X.w i).root := by
  have h := SRep.step X.Dst X.fr (X.w i) (w_ok hG hi) (w_rep hG hi.le)
  have e : X.st (i + 1) = fpStep M X.c X.P X.Dst X.fr (X.w i).i (X.st i) := st_succ i
  rw [← e] at h
  obtain ⟨h1, -, -, h4⟩ := h
  refine ⟨fun l hl => ?_, fun x hx => ?_⟩
  · rw [h1 l hl]; simp only [hsk, ↓reduceIte]; rfl
  · rw [h4 x hx]; simp only [hsk, ↓reduceIte, SW.ph]; ring

/-- The next state after a skipped stage. -/
lemma st_next_skip (hG : X.Good W) {i : ℕ} (hi : i < X.P.k) (hsk : (X.w i).skip) :
    (∀ l < X.P.k, (X.st (i + 1)).1 (X.P.d l) = if l = i then (X.w i).f2 else (X.w i).Fw l) ∧
    ∀ x < X.b, (X.st (i + 1)).2 (X.β x) = (X.w i).Pw x := by
  have h := SRep.step X.Dst X.fr (X.w i) (w_ok hG hi) (w_rep hG hi.le)
  have e : X.st (i + 1) = fpStep M X.c X.P X.Dst X.fr (X.w i).i (X.st i) := st_succ i
  rw [← e] at h
  obtain ⟨h1, -, -, h4⟩ := h
  refine ⟨fun l hl => ?_, fun x hx => ?_⟩
  · rw [h1 l hl]; simp only [hsk, ↓reduceIte]; rfl
  · rw [h4 x hx]; simp only [hsk, ↓reduceIte]

set_option maxHeartbeats 2000000 in
/-- **`rtP ; frRun ; rdP ; fwP`**: the FR run of a stage that is not skipped and the new state. -/
theorem hsB_exec {I : Input} (hG : X.Good W) {i : ℕ} (hi : i < X.P.k) (c : Config)
    (hc : WordsBounded W c) (hR : X.Regs c) (hS : X.Stt (X.st i) c.nmem)
    (himg : ∀ a ≤ X.WN,
      c.nmem a = (FrFix.frCfgN (X.prm (X.pm₁ i) (X.w i).root (X.Lz₁ i)) X.L).nmem a ∧
      c.nmem (X.SH + a) = (FrFix.frCfgN (X.prm (X.pm₁ i) (X.w i).root (X.Lz₁ i)) X.L).nmem a)
    (r39 : c.nreg 9339 = (X.w i).root) (r33 : c.nreg 9333 = if (X.w i).bv < 0 then 1 else 0)
    (r37 : (c.nreg 9337 : ℤ) = (X.w i).f2 + X.K)
    (r12 : (c.nreg 9312 : ℤ) = (X.w i).Pw ((X.w i).ia i))
    (r13 : (c.nreg 9313 : ℤ) = (X.w i).Pw ((X.w i).ib i))
    (r19 : c.nreg 9319 = (X.w i).ia i) (r20 : c.nreg 9320 = (X.w i).ib i)
    (r00 : c.nreg 9500 = i) (r510 : c.nreg 9510 = 1) (hsk : ¬ (X.w i).skip) :
    ∃ c' t, Exec I W (.seq rtP (.seq FrFix.frRun (.seq rdP fwP))) c c' t ∧
      t ≤ 108 * (6300 * (X.b * lg X.b ^ 2 + 2 * X.P.k * lg X.b)) + 30 * X.b + 1020 ∧
      X.Stt (X.st (i + 1)) c'.nmem ∧
      (∀ a ≤ X.WN, c'.nmem a = c.nmem a ∧ c'.nmem (X.SH + a) = c.nmem (X.SH + a)) ∧
      (∀ a, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → ¬ X.Wr a → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ (FrFix.frScr r ∨ r = 7606 ∨ (9505 ≤ r ∧ r ≤ 9508) ∨ (9520 ≤ r ∧ r ≤ 9531)) →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩, -,
    ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15⟩⟩ := hR
  obtain ⟨sFW, sPW⟩ := hS
  have l1 := hG.l1; have l2 := hG.l2; have l3 := hG.l3; have l4 := hG.l4; have l5 := hG.l5
  have l6 := hG.l6; have l7 := hG.l7; have l8 := hG.l8; have l9 := hG.l9; have l10 := hG.l10
  have l11 := hG.l11; have l12 := hG.l12; have l13 := hG.l13; have l14 := hG.l14
  have w1 := hG.w1; have w2 := hG.w2; have hK := hG.hK; have hL := hG.hL
  have hWf := X.lb_le_Wf
  have hWN : 2 * X.Wf + 1 ≤ X.WN := by unfold WN; omega
  have hb1 := b_pos hG
  have hroot := root_lt hG hi
  have hb₁ := frImgB₁ hG hi
  set P₁ := X.prm (X.pm₁ i) (X.w i).root (X.Lz₁ i) with hP₁
  have hL₁ : Lay P₁ := MsCall.frPrm_lay hb₁
  have hfc := frCost_prm hG hb₁
  rw [← hP₁] at hfc
  have eLG : X.LG = 4 * (6300 * (X.b * lg X.b ^ 2 + 2 * X.P.k * lg X.b)) + 3 := rfl
  -- `rtP`
  obtain ⟨c₁, t₁, e₁, ht₁, h06, k1, m1, rr1, rm1, o1⟩ := rtP_exec (P := I) c hc
  -- `frRun`
  have hWN₁ : frWN P₁ X.L = X.WN := prm_WN hG _ _ _
  have hfeas : Feas P₁ :=
    (X.w i).feas hG.c_nn hG.pseudo hG.mssp_spec (w_ok hG hi) (w_rep hG hi.le) (invB hG hi.le).1
      hsk hG.inj hG.dsome hG.dm (pm := X.pm₁ i) (fun x hx => rfl)
  obtain ⟨c₂, t₂, e₂, ht₂, F1, ⟨K', v, dd, hres⟩, F3, F4, rr2, rm2, o2⟩ :=
    FrFix.frRun_exec (P' := I) (W := W) hL₁ (MsCall.frPrm_xb hb₁) hG.cross hfeas (Ob := X.Ob)
      (p := X.p) (SH := X.SH) c₁ e₁.wb_right
      (by rw [k1 _ (by omega), d1]; rfl) (by rw [k1 _ (by omega), d2]; rfl)
      (by rw [k1 _ (by omega), d3]; rfl) (by rw [k1 _ (by omega), d4]; rfl)
      (by rw [k1 _ (by omega), d5]; rfl) (by rw [k1 _ (by omega), d6, prm_lb hG])
      (by rw [h06, r39]; rfl) (by rw [k1 _ (by omega), d7, prm_sb hG])
      (by rw [k1 _ (by omega), d8, prm_db hG]) (by rw [k1 _ (by omega), d9, prm_wb hG])
      (by rw [k1 _ (by omega), d10]; rfl) (by rw [k1 _ (by omega), d11]; rfl)
      (by rw [k1 _ (by omega), d12, prm_W hG]) (by rw [k1 _ (by omega), d13])
      (by rw [k1 _ (by omega), d14]) (by rw [k1 _ (by omega), d15])
      (fun a ha => by rw [m1]; rw [hWN₁] at ha; exact (himg a ha).1)
      (fun a ha => by rw [m1]; rw [hWN₁] at ha; exact (himg a ha).2)
      (by rw [hWN₁]; exact l1) (by rw [hWN₁]; omega) (by show X.Ob + X.b + X.b ≤ X.p; omega)
      (by omega)
  rw [hWN₁] at F1 F3
  have eN : P₁.N = X.b := rfl
  rw [eN] at ht₂
  have q2 : ∀ r, ¬ FrFix.frScr r → r ≠ 7606 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [F4 r h1, k1 r h2]
  have up2 : ∀ a, X.WN < a → (a < X.Ob ∨ X.Ob + X.b + X.b ≤ a) → a < X.p →
      c₂.nmem a = c.nmem a := fun a h1 h2 h3 => by
    rw [F3 a h1 h2 (Or.inl h3), m1]
  -- the FR answers
  have hres' : FrFix.FResN (MsCall.frPrm X.b X.Dm (X.pm₁ i) (X.w i).root
      (fun a => X.idx (M.face (dartAt X.P a))) (fun a => X.idx (M.face (M.rev (dartAt X.P a))))
      (fun a => (X.w i).lenD X.P X.c (X.st i).1 (X.st i).2 (dartAt X.P a)) (2 * X.P.k))
      X.L K' v dd c₂.nmem X.Ob (X.Ob + X.b) := hres
  have hdw := (X.w i).dw_eq hG.c_nn hG.pseudo hG.k_pos hG.mssp_spec hG.fr_spec (w_ok hG hi)
    (w_rep hG hi.le) (invB hG hi.le).1 hsk hG.inj hG.dsome hG.dm (pm := X.pm₁ i)
    (fun x hx => rfl) hG.cross hres'
  have hdw' : ∀ x < X.b, (X.w i).dw X.P X.c X.Dst X.fr X.β (X.st i) x =
      if c₂.nmem (X.Ob + x) = 1 then frDec (MsCall.frPrm X.b X.Dm (X.pm₁ i) (X.w i).root
        (fun a => X.idx (M.face (dartAt X.P a))) (fun a => X.idx (M.face (M.rev (dartAt X.P a))))
        (fun a => (X.w i).lenD X.P X.c (X.st i).1 (X.st i).2 (dartAt X.P a)) (2 * X.P.k)) X.L
        (c₂.nmem (X.Ob + X.b + x)) else 0 := hdw
  obtain ⟨nF, nP⟩ := st_next hG hi hsk
  have eH : frH (MsCall.frPrm X.b X.Dm (X.pm₁ i) (X.w i).root
      (fun a => X.idx (M.face (dartAt X.P a))) (fun a => X.idx (M.face (M.rev (dartAt X.P a))))
      (fun a => (X.w i).lenD X.P X.c (X.st i).1 (X.st i).2 (dartAt X.P a)) (2 * X.P.k)) X.L =
      X.H := rfl
  have eM : frM (MsCall.frPrm X.b X.Dm (X.pm₁ i) (X.w i).root
      (fun a => X.idx (M.face (dartAt X.P a))) (fun a => X.idx (M.face (M.rev (dartAt X.P a))))
      (fun a => (X.w i).lenD X.P X.c (X.st i).1 (X.st i).2 (dartAt X.P a)) (2 * X.P.k)) X.L =
      X.Mo := rfl
  have hPr : (c.nmem (X.PWb + (X.w i).root) : ℤ) = (X.w i).Pw (X.w i).root := sPW _ hroot
  have hPr2 : c₂.nmem (X.PWb + (X.w i).root) = c.nmem (X.PWb + (X.w i).root) :=
    up2 _ (by omega) (Or.inl (by omega)) (by omega)
  -- the new prices as values of `rdV`
  have hval : ∀ x < X.b, c₂.nmem (X.Ob + x) = 1 →
      c.nmem (X.PWb + (X.w i).root) + c₂.nmem (X.Ob + x + X.b) ≤ 2 * X.B + X.Mo ∧
      ((rdV (c₂.nmem (X.Ob + x)) (c₂.nmem (X.Ob + x + X.b)) (c.nmem (X.PWb + (X.w i).root))
        X.H X.Mo : ℕ) : ℤ) = (X.st (i + 1)).2 (X.β x) := by
    intro x hx hf
    have e := hdw' x hx
    rw [nP x hx, e]
    have hb := st_price hG (show i + 1 ≤ X.P.k by omega) (X.β x)
    rw [nP x hx, e] at hb
    have hPrB := st_price hG hi.le (X.β (X.w i).root)
    have hPr' : (c.nmem (X.PWb + (X.w i).root) : ℤ) = (X.st i).2 (X.β (X.w i).root) := hPr
    simp only [hf, ↓reduceIte, frDec, eH, eM] at hb ⊢
    rw [show X.Ob + X.b + x = X.Ob + x + X.b by ring] at hb ⊢
    unfold rdV; simp only [↓reduceIte]
    have ePw : (X.w i).Pw (X.w i).root = (X.st i).2 (X.β (X.w i).root) := rfl
    rw [ePw] at hb ⊢
    by_cases h2 : X.H < c₂.nmem (X.Ob + x + X.b)
    · simp only [h2, ↓reduceIte, show ¬ (c₂.nmem (X.Ob + x + X.b) ≤ X.H) by omega] at hb ⊢
      constructor
      · omega
      · push_cast [Nat.cast_sub (show X.Mo ≤ c.nmem (X.PWb + (X.w i).root) +
          c₂.nmem (X.Ob + x + X.b) by omega)]
        omega
    · simp only [h2, ↓reduceIte, show c₂.nmem (X.Ob + x + X.b) ≤ X.H by omega] at hb ⊢
      constructor
      · omega
      · push_cast; omega
  have hval0 : ∀ x < X.b, c₂.nmem (X.Ob + x) ≠ 1 →
      ((rdV (c₂.nmem (X.Ob + x)) (c₂.nmem (X.Ob + x + X.b)) (c.nmem (X.PWb + (X.w i).root))
        X.H X.Mo : ℕ) : ℤ) = (X.st (i + 1)).2 (X.β x) := by
    intro x hx hf
    rw [nP x hx, hdw' x hx]
    unfold rdV
    simp only [hf, ↓reduceIte, zero_add]
    exact hPr
  -- `rdP`
  obtain ⟨c₃, t₃, e₃, ht₃, R1, R2, R3, rr3, rm3, o3⟩ :=
    rdP_exec (P := I) c₂ e₂.wb_right (b := X.b) (Ob := X.Ob) (PWb := X.PWb) (root := (X.w i).root)
      (H := X.H) (Mo := X.Mo)
      (by rw [q2 _ (by unfold FrFix.frScr; omega) (by omega), d13])
      (by rw [q2 _ (by unfold FrFix.frScr; omega) (by omega), d1])
      (by rw [q2 _ (by unfold FrFix.frScr; omega) (by omega), a8])
      (by rw [q2 _ (by unfold FrFix.frScr; omega) (by omega), r39])
      (by rw [q2 _ (by unfold FrFix.frScr; omega) (by omega), r510])
      (by rw [q2 _ (by unfold FrFix.frScr; omega) (by omega), d11])
      (by rw [q2 _ (by unfold FrFix.frScr; omega) (by omega), d10]) (by omega) (by omega) hroot
      (fun x hx hf => by rw [hPr2]; have := (hval x hx hf).1; omega)
  rw [hPr2] at R1
  have hnewP : ∀ x < X.b, (c₃.nmem (X.PWb + x) : ℤ) = (X.st (i + 1)).2 (X.β x) := fun x hx => by
    rw [R1 x hx]
    by_cases hf : c₂.nmem (X.Ob + x) = 1
    · exact (hval x hx hf).2
    · exact hval0 x hx hf
  have q3 : ∀ r, ¬ (FrFix.frScr r ∨ r = 7606 ∨ (9520 ≤ r ∧ r ≤ 9531)) → c₃.nreg r = c.nreg r :=
    fun r h => by
      have h3 : ¬ (9520 ≤ r ∧ r ≤ 9531) := fun h' => h (Or.inr (Or.inr h'))
      rw [R3 r (by omega) (by omega) (by omega), q2 r (fun h' => h (Or.inl h'))
        (fun h' => h (Or.inr (Or.inl h')))]
  -- `fwP`
  have hia := (X.w i).ia i; have hia_lt : (X.w i).ia i < X.b := by
    have := ET_lt hG (a := i + i) (by omega); rw [ET_even] at this; exact this
  have hib_lt : (X.w i).ib i < X.b := by
    have := ET_lt hG (a := i + i + 1) (by omega); rw [ET_odd] at this; exact this
  have bF2 : (c.nreg 9337 : ℤ) ≤ 4 * X.B + X.K := by
    obtain ⟨-, -, -, -, -, h6, -⟩ :=
      (X.w i).wbnd (w_bF hG hi.le) (w_bP hG hi.le) (w_bcw hG i) (w_bcr hG i) (w_bf0 hG i)
        (w_bdv hG i)
    rw [abs_le] at h6; omega
  have bNA := hnewP _ hia_lt; have bNB := hnewP _ hib_lt
  have pNA := st_price hG (show i + 1 ≤ X.P.k by omega) (X.β ((X.w i).ia i))
  have pNB := st_price hG (show i + 1 ≤ X.P.k by omega) (X.β ((X.w i).ib i))
  have pA := st_price hG hi.le (X.β ((X.w i).ia i))
  have pB := st_price hG hi.le (X.β ((X.w i).ib i))
  have r12' : (c.nreg 9312 : ℤ) = (X.st i).2 (X.β ((X.w i).ia i)) := r12
  have r13' : (c.nreg 9313 : ℤ) = (X.st i).2 (X.β ((X.w i).ib i)) := r13
  obtain ⟨c₄, t₄, e₄, ht₄, W1, W2, rr4, rm4, o4⟩ :=
    fwP_exec (P := I) c₃ e₃.wb_right (i := i) (FWb := X.FWb) (PWb := X.PWb) (IA := (X.w i).ia i)
      (IB := (X.w i).ib i) (NG := c.nreg 9333) (F2 := c.nreg 9337) (PA := c.nreg 9312)
      (PB := c.nreg 9313)
      (by rw [q3 _ (by unfold FrFix.frScr; omega)]; exact r00)
      (by rw [q3 _ (by unfold FrFix.frScr; omega)]; exact a6)
      (by rw [q3 _ (by unfold FrFix.frScr; omega)]; exact a8)
      (by rw [q3 _ (by unfold FrFix.frScr; omega)]; exact r19)
      (by rw [q3 _ (by unfold FrFix.frScr; omega)]; exact r20)
      (by rw [q3 _ (by unfold FrFix.frScr; omega)])
      (by rw [q3 _ (by unfold FrFix.frScr; omega)]; exact r510)
      (by rw [q3 _ (by unfold FrFix.frScr; omega)])
      (by rw [q3 _ (by unfold FrFix.frScr; omega)])
      (by rw [q3 _ (by unfold FrFix.frScr; omega)])
      ⟨by omega, by omega, by omega, by omega, by omega⟩
  -- the new flow on `d i`
  have hf3 : (fwV (c.nreg 9333) (c.nreg 9337) (c.nreg 9312) (c.nreg 9313)
      (c₃.nmem (X.PWb + (X.w i).ia i)) (c₃.nmem (X.PWb + (X.w i).ib i)) : ℤ) =
      (X.st (i + 1)).1 (X.P.d i) + X.K := by
    have hfl := st_flow hG (show i + 1 ≤ X.P.k by omega) (X.P.d i)
    rw [abs_le] at hfl
    have e3 := nF i hi
    simp only [↓reduceIte] at e3
    rw [e3] at hfl ⊢
    have eA := nP _ hia_lt; have eB := nP _ hib_lt
    unfold SW.f3 SW.ph at hfl ⊢
    rw [← bNA, ← bNB] at *
    have eA' : (c₃.nmem (X.PWb + (X.w i).ia i) : ℤ) =
        (X.w i).dw X.P X.c X.Dst X.fr X.β (X.st i) ((X.w i).ia i) + (X.w i).Pw (X.w i).root := by
      rw [bNA]; exact eA
    have eB' : (c₃.nmem (X.PWb + (X.w i).ib i) : ℤ) =
        (X.w i).dw X.P X.c X.Dst X.fr X.β (X.st i) ((X.w i).ib i) + (X.w i).Pw (X.w i).root := by
      rw [bNB]; exact eB
    have ePA : (X.w i).Pw ((X.w i).ia i) = (c.nreg 9312 : ℤ) := r12.symm
    have ePB : (X.w i).Pw ((X.w i).ib i) = (c.nreg 9313 : ℤ) := r13.symm
    have ei : (X.w i).i = i := rfl
    rw [ei, ePA, ePB] at hfl ⊢
    unfold fwV
    by_cases hng : (X.w i).bv < 0
    · simp only [hng, ↓reduceIte] at hfl ⊢
      rw [r33]; simp only [hng, ↓reduceIte, show ¬ (1 < 1) by omega]
      push_cast [Nat.cast_sub (show c.nreg 9312 ≤ c.nreg 9337 + c₃.nmem (X.PWb + (X.w i).ia i) by
        omega)]
      omega
    · simp only [hng, ↓reduceIte] at hfl ⊢
      rw [r33]; simp only [hng, ↓reduceIte, show (0 < 1) by omega]
      push_cast [Nat.cast_sub (show c₃.nmem (X.PWb + (X.w i).ib i) ≤ c.nreg 9337 + c.nreg 9313 by
        omega)]
      omega
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, ⟨fun l hl => ?_, fun x hx => ?_⟩,
    fun a ha => ?_, fun a h1 h2 h3 => ?_, fun r hr => ?_, by rw [rr4, rr3, rr2, rr1],
    by rw [rm4, rm3, rm2, rm1], by rw [o4, o3, o2, o1]⟩
  · rw [W1]
    by_cases hli : l = i
    · subst hli; simp only [↓reduceIte]; exact hf3
    · simp only [show X.FWb + l ≠ X.FWb + i by omega, ↓reduceIte]
      rw [R2 _ (by omega), up2 _ (by omega) (Or.inl (by omega)) (by omega), sFW l hl, nF l hl]
      simp only [hli, ↓reduceIte]; rfl
  · rw [W1]; simp only [show X.PWb + x ≠ X.FWb + i by omega, ↓reduceIte]; exact hnewP x hx
  · rw [W1, W1]
    simp only [show a ≠ X.FWb + i by omega, show X.SH + a ≠ X.FWb + i by omega, ↓reduceIte]
    rw [R2 _ (by omega), R2 _ (by omega), F1 a ha, m1,
      up2 _ (by omega) (Or.inl (by omega)) (by omega)]
    exact ⟨rfl, rfl⟩
  · unfold Wr at h3
    rw [W1]; simp only [show a ≠ X.FWb + i by omega, ↓reduceIte]
    rw [R2 _ (by omega), F3 a h1 (by omega) (by omega), m1]
  · have h5 : ¬ (9505 ≤ r ∧ r ≤ 9508) := fun h' => hr (Or.inr (Or.inr (Or.inl h')))
    rw [W2 r (by omega), q3 r (fun h => hr (h.elim Or.inl
      (fun h => Or.inr (h.elim Or.inl (fun h => Or.inr (Or.inr h))))))]

end SLx

end BKMNW

end PlanarFlow
