module

public import PlanarFlow.BKMNW.Nf7bG

/-!
# The stage loop of `fixP`, part H: one stage and the loop

* programs **`hsP`** `= (elP ; prP ; imU) ; (rtP ; frRun ; rdP ; fwP)` (a stage with a Hassin
  step), **`fxStB`** `= (ldP ; swP) ; (if [skip] < 1 then hsP else skP) ; incP` (one stage),
  **`loopP`** `= r9500 := 0 ; while r9500 < r9371 do fxStB` (the `k` stages);
* `SLx.Regs_of`; **`SLx.fxStB_exec`** (the stage lemma: `J c₀ i c → J c₀ (i+1) c'` within `X.T`
  steps); **`SLx.loopP_exec`** (from the state `X.st 0` — `FW[l] = f₀ (d l) + K`, `PW = 0` — and an
  image of the stage family, within `(X.T + 2) k + 3` steps: the arrays hold `X.st k =
  fpState … k`, the image and its shadow are an image of the family, the memory above the
  shadow outside `Wr` and the registers outside `scr` are kept).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap SPath WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge.FR

/-- **A stage with a Hassin step.** -/
def hsP : Stmt := .seq (.seq elP (.seq prP MsCall.imU)) (.seq rtP (.seq FrFix.frRun (.seq rdP fwP)))

/-- **One stage of `fixPath`.** -/
def fxStB : Stmt := .seq (.seq ldP swP) (.seq (.ifLtN 9338 9510 hsP skP) incP)

/-- **The `k` stages of `fixPath`.** -/
def loopP : Stmt := .seq (block [.constN 9500 0]) (.whileLtN 9500 9371 fxStB)

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

namespace SLx

variable {X : SLx M} {W : ℕ}

lemma Regs_of {c c' : Config} (hR : X.Regs c) (hk : ∀ r, ¬ scr r → c'.nreg r = c.nreg r) :
    X.Regs c' := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩,
    ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩,
    ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15⟩⟩ := hR
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
  (rwa [hk _ (by unfold scr swScr FrFix.frScr; omega)])

set_option maxHeartbeats 2000000 in
/-- **One stage**: the invariant before stage `i` gives the invariant before stage `i + 1`. -/
theorem fxStB_exec {I : Input} (hG : X.Good W) {c₀ : Config} (hR : X.Regs c₀)
    (hFx : X.Fix c₀.nmem) {i : ℕ} (hi : i < X.P.k) (c : Config) (hc : WordsBounded W c)
    (hJ : X.J c₀ i c) :
    ∃ c' t, Exec I W fxStB c c' t ∧ t ≤ X.T ∧ X.J c₀ (i + 1) c' := by
  have hRc := J_regs hR hJ
  have hFc := J_fix hG hFx hJ
  obtain ⟨j00, jreg, jS, jI, jK, jr, jrm, jo⟩ := hJ
  have l1 := hG.l1; have l2 := hG.l2; have l3 := hG.l3; have l4 := hG.l4; have l5 := hG.l5
  have l6 := hG.l6; have l7 := hG.l7; have l8 := hG.l8; have l9 := hG.l9; have l10 := hG.l10
  have l11 := hG.l11; have l12 := hG.l12; have l13 := hG.l13; have l14 := hG.l14
  have w1 := hG.w1
  obtain ⟨c₂, t₂, e₂, ht₂, g30, g33, g37, g41, g38, g38', g39, g12, g13, g19, g20, g72, g510, gk,
      gm, gr, grm, go⟩ := ldsw_exec (I := I) hG hR hFx hi c hc ⟨j00, jreg, jS, jI, jK, jr, jrm, jo⟩
  have k2 : ∀ r, ¬ scr r → c₂.nreg r = c.nreg r := fun r hr =>
    gk r (by unfold scr swScr FrFix.frScr at *; omega)
  have hR2 : X.Regs c₂ := Regs_of hRc k2
  have g00 : c₂.nreg 9500 = i := by rw [gk _ (by unfold swScr; omega), j00]
  have hw2 := e₂.wb_right
  -- the incrementation
  have hinc : ∀ c₄ : Config, WordsBounded W c₄ → c₄.nreg 9500 = i → c₄.nreg 9510 = 1 →
      ∃ c₅ t₅, Exec I W incP c₄ c₅ t₅ ∧ t₅ = 1 ∧ c₅.nreg 9500 = i + 1 ∧
        (∀ r, r ≠ 9500 → c₅.nreg r = c₄.nreg r) ∧ c₅.nmem = c₄.nmem ∧ c₅.rreg = c₄.rreg ∧
        c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := fun c₄ hw h1 h2 =>
    incP_exec (P := I) c₄ hw h1 h2 (by omega)
  by_cases hsk : c₂.nreg 9338 < 1
  · -- a Hassin step
    have hsk' : ¬ (X.w i).skip := fun h => by have := g38.2 h; omega
    obtain ⟨c₃, t₃, e₃, ht₃, A1, A2, A3, Ar, Arm, Ao⟩ :=
      hsA_exec (I := I) hG hi c₂ hw2 hR2 (by rw [gm]; exact hFc) (by rw [gm]; exact jS)
        (by rw [gm]; exact jI) g33 g30 g37 g41 g72 g510
    have k3 : ∀ r, ¬ (r = 9370 ∨ (9378 ≤ r ∧ r ≤ 9387) ∨ (9520 ≤ r ∧ r ≤ 9522) ∨ r = 8126 ∨
        (8140 ≤ r ∧ r ≤ 8149)) → c₃.nreg r = c₂.nreg r := fun r h =>
      A3 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hR3 : X.Regs c₃ := Regs_of hR2 fun r hr => k3 r (by unfold scr at hr; omega)
    have m3 : ∀ a, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → ¬ X.Wr a →
        c₃.nmem a = c.nmem a := fun a h1 h2 h3 => by
      unfold Wr at h3; rw [A2 a h1 h2 (by omega) (by omega), gm]
    have hS3 : X.Stt (X.st i) c₃.nmem := by
      obtain ⟨s1, s2⟩ := jS
      refine ⟨fun l hl => ?_, fun x hx => ?_⟩
      · rw [A2 _ (by omega) (by omega) (by omega) (by omega), gm]; exact s1 l hl
      · rw [A2 _ (by omega) (by omega) (by omega) (by omega), gm]; exact s2 x hx
    obtain ⟨c₄, t₄, e₄, ht₄, B1, B2, B3, B4, Br, Brm, Bo⟩ :=
      hsB_exec (I := I) hG hi c₃ e₃.wb_right hR3 hS3 A1
        (by rw [k3 _ (by omega)]; exact g39) (by rw [k3 _ (by omega)]; exact g33)
        (by rw [k3 _ (by omega)]; exact g37) (by rw [k3 _ (by omega)]; exact g12)
        (by rw [k3 _ (by omega)]; exact g13) (by rw [k3 _ (by omega)]; exact g19)
        (by rw [k3 _ (by omega)]; exact g20) (by rw [k3 _ (by omega)]; exact g00)
        (by rw [k3 _ (by omega)]; exact g510) hsk'
    have k4 : ∀ r, ¬ scr r → c₄.nreg r = c₃.nreg r := fun r hr =>
      B4 r (by unfold scr FrFix.frScr at *; omega)
    obtain ⟨c₅, t₅, e₅, ht₅, i00, ik, im, ir, irm, io⟩ :=
      hinc c₄ e₄.wb_right (by rw [B4 _ (by unfold FrFix.frScr; omega), k3 _ (by omega)]; exact g00)
        (by rw [B4 _ (by unfold FrFix.frScr; omega), k3 _ (by omega)]; exact g510)
    refine ⟨c₅, _, .seq e₂ (.seq (.ifLtN_true (by rw [g510]; exact hsk) (.seq e₃ e₄)) e₅),
      ?_, i00, fun r hr => ?_, by rw [im]; exact B1,
      ⟨X.pm₁ i, (X.w i).root, X.Lz₁ i, frImgB₁ hG hi, fun a ha => ?_⟩, fun a h1 h2 h3 => ?_,
      by rw [ir, Br, Ar, gr, jr], by rw [irm, Brm, Arm, grm, jrm], by rw [io, Bo, Ao, go, jo]⟩
    · unfold T; omega
    · rw [ik r (by unfold scr at hr; omega), k4 r hr, k3 r (by unfold scr at hr; omega), k2 r hr,
        jreg r hr]
    · rw [im, (B2 a ha).1, (B2 a ha).2]; exact A1 a ha
    · rw [im, B3 a h1 h2 h3, m3 a h1 h2 h3]; exact jK a h1 h2 h3
  · -- a skipped stage
    have hsk' : (X.w i).skip := g38.1 (by omega)
    obtain ⟨⟨-, -, -, -, -, a6, -⟩, -, -⟩ := hR2
    obtain ⟨c₃, t₃, e₃, ht₃, S1, Sk, Sr, Srm, So⟩ :=
      skP_exec (P := I) c₂ hw2 g00 a6 (by omega)
    obtain ⟨c₅, t₅, e₅, ht₅, i00, ik, im, ir, irm, io⟩ :=
      hinc c₃ e₃.wb_right (by rw [Sk _ (by omega)]; exact g00)
        (by rw [Sk _ (by omega)]; exact g510)
    obtain ⟨nF, nP⟩ := st_next_skip hG hi hsk'
    obtain ⟨s1, s2⟩ := jS
    obtain ⟨pm, r, Lz, hb, himg⟩ := jI
    refine ⟨c₅, _, .seq e₂ (.seq (.ifLtN_false (by rw [g510]; exact hsk) e₃) e₅),
      ?_, i00, fun r hr => ?_, ⟨fun l hl => ?_, fun x hx => ?_⟩,
      ⟨pm, r, Lz, hb, fun a ha => ?_⟩, fun a h1 h2 h3 => ?_,
      by rw [ir, Sr, gr, jr], by rw [irm, Srm, grm, jrm], by rw [io, So, go, jo]⟩
    · unfold T; omega
    · rw [ik r (by unfold scr at hr; omega), Sk r (by unfold scr at hr; omega), k2 r hr,
        jreg r hr]
    · rw [im, S1, nF l hl, gm]
      by_cases hli : l = i
      · subst hli; simp only [↓reduceIte]; exact g37
      · simp only [show X.FWb + l ≠ X.FWb + i by omega, hli, ↓reduceIte]; exact s1 l hl
    · rw [im, S1, nP x hx, gm]
      simp only [show X.PWb + x ≠ X.FWb + i by omega, ↓reduceIte]; exact s2 x hx
    · rw [im, S1, S1, gm]
      simp only [show a ≠ X.FWb + i by omega, show X.SH + a ≠ X.FWb + i by omega, ↓reduceIte]
      exact himg a ha
    · unfold Wr at h3
      rw [im, S1, gm]
      simp only [show a ≠ X.FWb + i by omega, ↓reduceIte]
      exact jK a h1 h2 (by unfold Wr; omega)

/-- **The `k` stages of `fixPath` on the machine.** From the state `X.st 0` in the arrays and
an image of the stage family (live and shadow), `loopP` leaves the state `X.st k` (that of
`fixPath` before its final call, `fixPath_eq_fpState`) within `(X.T + 2) k + 3` steps. -/
theorem loopP_exec {I : Input} (hG : X.Good W) (c : Config) (hc : WordsBounded W c)
    (hR : X.Regs c) (hFx : X.Fix c.nmem) (hS : X.Stt (X.st 0) c.nmem) (hImg : X.Img c.nmem) :
    ∃ c' t, Exec I W loopP c c' t ∧ t ≤ (X.T + 2) * X.P.k + 3 ∧
      X.Stt (X.st X.P.k) c'.nmem ∧ X.Img c'.nmem ∧
      (∀ a, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → ¬ X.Wr a → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ scr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a00, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec I W (block [.constN 9500 0]) c c₁ t₁ ∧ t₁ = 1 ∧ c₁.nreg 9500 = 0 ∧
      (∀ r, r ≠ 9500 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  have k1 : ∀ r, ¬ scr r → c₁.nreg r = c.nreg r := fun r hr =>
    ak r (by unfold scr at hr; omega)
  have hR1 : X.Regs c₁ := Regs_of hR k1
  have hF1 : X.Fix c₁.nmem := by rw [am]; exact hFx
  have h71 : c₁.nreg 9371 = X.P.k := hR1.1.2.1
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, hJ⟩ := NegSSSP.forLoop_exec (P := I) (a := 9500) (bR := 9371)
    (body := fxStB) (fun i c' => X.J c₁ i c') (K := X.T) (n := X.P.k) c₁ e₁.wb_right a00 h71
    ⟨a00, fun _ _ => rfl, by rw [am]; exact hS, by rw [am]; exact hImg, fun _ _ _ _ => rfl, rfl,
      rfl, rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨c'', t, ex, ht, hJ'⟩ := fxStB_exec (I := I) hG hR1 hF1 hi c' hw hJ
      exact ⟨c'', t, ex, ht, hJ'.1,
        by rw [hJ'.2.1 _ (by unfold scr swScr FrFix.frScr; omega), h71], hJ'⟩)
  obtain ⟨j00, jreg, jS, jI, jK, jr, jrm, jo⟩ := hJ
  refine ⟨c₂, _, .seq e₁ e₂, by omega, jS, jI, fun a h1 h2 h3 => by rw [jK a h1 h2 h3, am],
    fun r hr => by rw [jreg r hr, k1 r hr], by rw [jr, ar], by rw [jrm, arm], by rw [jo, ao]⟩

/-- The start of the loop: `X.st 0 = (f₀, 0)`, so `FW[l] = f₀ (d l) + K`, `PW[x] = 0`. -/
theorem stt_zero (nm : ℕ → ℕ) (h1 : ∀ l < X.P.k, (nm (X.FWb + l) : ℤ) = X.f₀ (X.P.d l) + X.K)
    (h2 : ∀ x < X.b, nm (X.PWb + x) = 0) : X.Stt (X.st 0) nm :=
  ⟨h1, fun x hx => by rw [h2 x hx]; rfl⟩

/-- The end of the loop: the state of `fixPath` before its final call. -/
theorem st_k_eq : X.st X.P.k = fpState M X.c X.f₀ X.P X.mssp X.fr X.P.k := rfl

end SLx

end BKMNW

end PlanarFlow
