module

public import PlanarFlow.BKMNW.PpFin

/-!
# The final arrays: the composed stage

**`fin_exec`**: `fin0`, the six gathers (`gat1_exec` through `POS`, `gat2_exec` plain), `finR`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv

variable {P : Input} {W : ℕ}

/-- The fixed registers and the low memory along the gathers. -/
def GR (n B F₀ N Z : ℕ) (mem₀ : ℕ → ℕ) (d : Config) : Prop :=
  d.nreg 8700 = n ∧ d.nreg 8704 = 1 ∧ d.nreg 8730 = B ∧
    d.nreg 8732 = F₀ ∧ d.nreg 8741 = N ∧ d.nreg 8725 = B + 35 * n ∧ d.nreg 8726 = B + 42 * n ∧
    d.nreg 8705 = 2 ∧ d.nreg 8708 = Z ∧ d.nreg 8731 = N ∧ (∀ a, a < F₀ → d.nmem a = mem₀ a)

lemma GR.keep {n B F₀ N Z : ℕ} {mem₀ : ℕ → ℕ} {d d' : Config} (h : GR n B F₀ N Z mem₀ d)
    (hf : ∀ x, ¬ wscr x → x ≠ 8727 → x ≠ 8778 → d'.nreg x = d.nreg x)
    (hm : ∀ a, a < F₀ → d'.nmem a = d.nmem a) : GR n B F₀ N Z mem₀ d' := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := h
  have hf' : ∀ x, 8700 ≤ x → x ≤ 8737 → x ≠ 8727 → d'.nreg x = d.nreg x := fun x h1 h2 h3 =>
    hf x (by unfold wscr pscr; omega) h3 (by omega)
  exact ⟨by rw [hf' _ (by omega) (by omega) (by omega)]; exact g1,
    by rw [hf' _ (by omega) (by omega) (by omega)]; exact g2,
    by rw [hf' _ (by omega) (by omega) (by omega)]; exact g3,
    by rw [hf' _ (by omega) (by omega) (by omega)]; exact g4,
    by rw [hf _ (by unfold wscr pscr; omega) (by omega) (by omega)]; exact g5,
    by rw [hf' _ (by omega) (by omega) (by omega)]; exact g6,
    by rw [hf' _ (by omega) (by omega) (by omega)]; exact g7,
    by rw [hf' _ (by omega) (by omega) (by omega)]; exact g8,
    by rw [hf' _ (by omega) (by omega) (by omega)]; exact g9,
    by rw [hf' _ (by omega) (by omega) (by omega)]; exact g10,
    fun a ha => by rw [hm a ha, g11 a ha]⟩

/-- **A gather through `POS`.** -/
theorem gat1_exec (d : Config) (hd : WordsBounded W d) {n B KM N Z : ℕ} {mem₀ : ℕ → ℕ}
    {srt : ℕ → ℕ} (a j : ℕ) (f : ℕ → ℕ) (hG : GR n B (B + 84 * n + KM + 1) N Z mem₀ d)
    (hj : j ≤ 5) (ha : a ≤ 77) (hN : N ≤ 7 * n)
    (hsrt : ∀ i < N, mem₀ (B + 35 * n + i) = srt i) (hslt : ∀ i < N, srt i < 7 * n)
    (hf : ∀ s < 7 * n, mem₀ (B + a * n + s) = f s ∧ f s ≤ 7 * n)
    (hW : B + 200 * n + KM + 200 ≤ W) :
    ∃ d' t, Exec P W (gat a j vbG1) d d' t ∧ t ≤ 11 * N + 9 ∧
      (∀ i < N, d'.nmem (B + 84 * n + KM + 1 + 7 * j * n + i) = mem₀ (B + 42 * n + f (srt i))) ∧
      (∀ a', ¬ (B + 84 * n + KM + 1 + 7 * j * n ≤ a' ∧ a' < B + 84 * n + KM + 1 + 7 * j * n + N) →
        d'.nmem a' = d.nmem a') ∧
      (∀ x, ¬ wscr x → x ≠ 8727 → x ≠ 8778 → d'.nreg x = d.nreg x) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, _, _, _, g11⟩ := hG
  have h1 : 7 * j * n ≤ 35 * n := Nat.mul_le_mul_right _ (by omega)
  have h2 : a * n ≤ 77 * n := Nat.mul_le_mul_right _ ha
  exact gat_exec (P := P) d hd (n := n) (B := B) (F₀ := B + 84 * n + KM + 1) (a := a) (j := j)
    (m := N) (B' := 6) (fun i => mem₀ (B + 42 * n + f (srt i))) g1 g3 g4 g5 g2 hN (by omega)
    (by omega) (by omega) (fun i hi c' hw h40 h27 hfr hm => by
      have q25 : c'.nreg 8725 = B + 35 * n := by
        rw [hfr _ (by unfold wscr pscr; omega) (by omega) (by omega)]; exact g6
      have q26 : c'.nreg 8726 = B + 42 * n := by
        rw [hfr _ (by unfold wscr pscr; omega) (by omega) (by omega)]; exact g7
      have hlow : ∀ a', a' < B + 84 * n + KM + 1 → c'.nmem a' = mem₀ a' := fun a' h' => by
        rw [hm a' (by omega), g11 a' h']
      have hs := hslt i hi
      have e1 : c'.nmem (B + 35 * n + i) = srt i := by rw [hlow _ (by omega), hsrt i hi]
      have e2 : c'.nmem (B + a * n + srt i) = f (srt i) := by
        rw [hlow _ (by omega)]; exact (hf _ hs).1
      have hfl := (hf _ hs).2
      obtain ⟨c'', t, e, post⟩ := vbG1_exec (P := P) (Ab := B + a * n) (Sb := B + 35 * n)
        (Pb := B + 42 * n) c' hw h40 q25 h27 q26 (by omega) (by rw [e1]; omega)
        (by rw [e1, e2]; omega)
      rw [e1, e2, hlow _ (by omega)] at post
      exact ⟨c'', t, e, post⟩)

/-- **A plain gather.** -/
theorem gat2_exec (d : Config) (hd : WordsBounded W d) {n B KM N Z : ℕ} {mem₀ : ℕ → ℕ}
    {srt : ℕ → ℕ} (a j : ℕ) (f : ℕ → ℕ) (hG : GR n B (B + 84 * n + KM + 1) N Z mem₀ d)
    (hj : j ≤ 5) (ha : a ≤ 77) (hN : N ≤ 7 * n)
    (hsrt : ∀ i < N, mem₀ (B + 35 * n + i) = srt i) (hslt : ∀ i < N, srt i < 7 * n)
    (hf : ∀ s < 7 * n, mem₀ (B + a * n + s) = f s)
    (hW : B + 200 * n + KM + 200 ≤ W) :
    ∃ d' t, Exec P W (gat a j vbG2) d d' t ∧ t ≤ 9 * N + 9 ∧
      (∀ i < N, d'.nmem (B + 84 * n + KM + 1 + 7 * j * n + i) = f (srt i)) ∧
      (∀ a', ¬ (B + 84 * n + KM + 1 + 7 * j * n ≤ a' ∧ a' < B + 84 * n + KM + 1 + 7 * j * n + N) →
        d'.nmem a' = d.nmem a') ∧
      (∀ x, ¬ wscr x → x ≠ 8727 → x ≠ 8778 → d'.nreg x = d.nreg x) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, _, _, _, g11⟩ := hG
  have h1 : 7 * j * n ≤ 35 * n := Nat.mul_le_mul_right _ (by omega)
  have h2 : a * n ≤ 77 * n := Nat.mul_le_mul_right _ ha
  exact gat_exec (P := P) d hd (n := n) (B := B) (F₀ := B + 84 * n + KM + 1) (a := a) (j := j)
    (m := N) (B' := 4) (fun i => f (srt i)) g1 g3 g4 g5 g2 hN (by omega) (by omega)
    (by omega) (fun i hi c' hw h40 h27 hfr hm => by
      have q25 : c'.nreg 8725 = B + 35 * n := by
        rw [hfr _ (by unfold wscr pscr; omega) (by omega) (by omega)]; exact g6
      have hlow : ∀ a', a' < B + 84 * n + KM + 1 → c'.nmem a' = mem₀ a' := fun a' h' => by
        rw [hm a' (by omega), g11 a' h']
      have hs := hslt i hi
      have e1 : c'.nmem (B + 35 * n + i) = srt i := by rw [hlow _ (by omega), hsrt i hi]
      have e2 : c'.nmem (B + a * n + srt i) = f (srt i) := by
        rw [hlow _ (by omega)]; exact hf _ hs
      obtain ⟨c'', t, e, post⟩ := vbG2_exec (P := P) (Ab := B + a * n) (Sb := B + 35 * n)
        c' hw h40 q25 h27 (by omega) (by rw [e1]; omega)
      rw [e1, e2] at post
      exact ⟨c'', t, e, post⟩)

set_option maxHeartbeats 1000000 in
theorem fin_exec (c : Config) (hc : WordsBounded W c) {n B KM N Z : ℕ} {srt : ℕ → ℕ}
    (fR fO fT fC fK fY : ℕ → ℕ)
    (r00 : c.nreg 8700 = n) (r04 : c.nreg 8704 = 1) (r05 : c.nreg 8705 = 2)
    (r08 : c.nreg 8708 = Z) (r09 : c.nreg 8709 = KM) (r30 : c.nreg 8730 = B)
    (r31 : c.nreg 8731 = N) (hN : N ≤ 7 * n)
    (hsrt : ∀ i < N, c.nmem (B + 35 * n + i) = srt i) (hslt : ∀ i < N, srt i < 7 * n)
    (hR : ∀ s < 7 * n, c.nmem (B + 49 * n + s) = fR s ∧ fR s ≤ 7 * n)
    (hO : ∀ s < 7 * n, c.nmem (B + 56 * n + s) = fO s ∧ fO s ≤ 7 * n)
    (hT : ∀ s < 7 * n, c.nmem (B + 63 * n + s) = fT s ∧ fT s ≤ 7 * n)
    (hC : ∀ s < 7 * n, c.nmem (B + 70 * n + s) = fC s)
    (hK : ∀ s < 7 * n, c.nmem (B + 77 * n + s) = fK s)
    (hY : ∀ s < 7 * n, c.nmem (B + 14 * n + s) = fY s)
    (hW : B + 200 * n + KM + 200 ≤ W) :
    ∃ c' t, Exec P W fin c c' t ∧ t ≤ 60 * N + 100 ∧
      (∀ i < N, c'.nmem (B + 84 * n + KM + 1 + i) = c.nmem (B + 42 * n + fR (srt i))) ∧
      (∀ i < N, c'.nmem (B + 84 * n + KM + 1 + 7 * n + i) = c.nmem (B + 42 * n + fO (srt i))) ∧
      (∀ i < N, c'.nmem (B + 84 * n + KM + 1 + 14 * n + i) = fC (srt i)) ∧
      (∀ i < N, c'.nmem (B + 84 * n + KM + 1 + 21 * n + i) = fK (srt i)) ∧
      (∀ i < N, c'.nmem (B + 84 * n + KM + 1 + 28 * n + i) = fY (srt i)) ∧
      (∀ i < N, c'.nmem (B + 84 * n + KM + 1 + 35 * n + i) = c.nmem (B + 42 * n + fT (srt i))) ∧
      c'.nreg 6700 = N ∧ c'.nreg 6701 = B + 84 * n + KM + 1 ∧
      c'.nreg 6702 = B + 84 * n + KM + 1 + 7 * n ∧ c'.nreg 6703 = B + 84 * n + KM + 1 + 14 * n ∧
      c'.nreg 6704 = B + 84 * n + KM + 1 + 21 * n ∧ c'.nreg 6705 = 1 ∧ c'.nreg 6706 = Z ∧
      c'.nreg 6707 = B + 84 * n + KM + 1 + 42 * n + 2 ∧
      c'.nmem (B + 84 * n + KM + 1 + 42 * n + 2 - 1) = B + 84 * n + KM + 1 + 28 * n ∧
      c'.nmem (B + 84 * n + KM + 1 + 42 * n + 2 - 1 - 1) = B + 84 * n + KM + 1 + 35 * n ∧
      (∀ a, a < B + 84 * n + KM + 1 → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set F₀ := B + 84 * n + KM + 1 with hF₀
  obtain ⟨c₀, t₀, e₀, ht₀, v32, v41, v25, v26, f0, m0, rr0, rm0, o0⟩ := fin0_exec (P := P) c hc
    r00 r04 r09 r30 r31 (by omega)
  have G0 : GR n B F₀ N Z c.nmem c₀ :=
    ⟨by rw [f0 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r00,
    by rw [f0 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r04,
    by rw [f0 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r30, v32, v41, v25,
    v26, by rw [f0 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r05,
    by rw [f0 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r08,
    by rw [f0 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r31,
    fun a _ => by rw [m0]⟩
  have hN7 : ∀ j ≤ 5, F₀ + 7 * j * n + N ≤ F₀ + 7 * j * n + 7 * n := fun j _ => by omega
  obtain ⟨c₁, t₁, e₁, ht₁, a1, m1, f1, rr1, rm1, o1⟩ := gat1_exec (P := P) c₀ e₀.wb_right 49 0 fR G0
    (by norm_num) (by norm_num) hN hsrt hslt hR hW
  have G1 := G0.keep f1 (fun a ha => m1 a (by omega))
  obtain ⟨c₂, t₂, e₂, ht₂, a2, m2, f2, rr2, rm2, o2⟩ := gat1_exec (P := P) c₁ e₁.wb_right 56 1 fO G1
    (by norm_num) (by norm_num) hN hsrt hslt hO hW
  have G2 := G1.keep f2 (fun a ha => m2 a (by omega))
  obtain ⟨c₃, t₃, e₃, ht₃, a3, m3, f3, rr3, rm3, o3⟩ := gat2_exec (P := P) c₂ e₂.wb_right 70 2 fC G2
    (by norm_num) (by norm_num) hN hsrt hslt hC hW
  have G3 := G2.keep f3 (fun a ha => m3 a (by omega))
  obtain ⟨c₄, t₄, e₄, ht₄, a4, m4, f4, rr4, rm4, o4⟩ := gat2_exec (P := P) c₃ e₃.wb_right 77 3 fK G3
    (by norm_num) (by norm_num) hN hsrt hslt hK hW
  have G4 := G3.keep f4 (fun a ha => m4 a (by omega))
  obtain ⟨c₅, t₅, e₅, ht₅, a5, m5, f5, rr5, rm5, o5⟩ := gat2_exec (P := P) c₄ e₄.wb_right 14 4 fY G4
    (by norm_num) (by norm_num) hN hsrt hslt hY hW
  have G5 := G4.keep f5 (fun a ha => m5 a (by omega))
  obtain ⟨c₆, t₆, e₆, ht₆, a6, m6, f6, rr6, rm6, o6⟩ := gat1_exec (P := P) c₅ e₅.wb_right 63 5 fT G5
    (by norm_num) (by norm_num) hN hsrt hslt hT hW
  have G6 := G5.keep f6 (fun a ha => m6 a (by omega))
  obtain ⟨h00, h04, h30, h32, h41, h25, h26, h05, h08, h31, h11⟩ := G6
  obtain ⟨c₇, t₇, e₇, ht₇, w00, w01, w02, w03, w04, w05, w06, w07, wm1, wm2, m7, f7, rr7, rm7,
    o7⟩ := finR_exec (P := P) c₆ e₆.wb_right h00 h04 h05 h31 h32 h08 (by omega)
  have ex : Exec P W fin c c₇ (t₀ + (t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))))) := by
    unfold fin
    exact .seq e₀ (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))))
  have z0 : ∀ i, F₀ + 7 * 0 * n + i = F₀ + i := fun i => by ring
  have z1 : ∀ i, F₀ + 7 * 1 * n + i = F₀ + 7 * n + i := fun i => by ring
  have z2 : ∀ i, F₀ + 7 * 2 * n + i = F₀ + 14 * n + i := fun i => by ring
  have z3 : ∀ i, F₀ + 7 * 3 * n + i = F₀ + 21 * n + i := fun i => by ring
  have z4 : ∀ i, F₀ + 7 * 4 * n + i = F₀ + 28 * n + i := fun i => by ring
  have z5 : ∀ i, F₀ + 7 * 5 * n + i = F₀ + 35 * n + i := fun i => by ring
  refine ⟨c₇, _, ex, by omega, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, w00, w01, by rw [w02], by rw [w03], by rw [w04], w05, w06,
    by rw [w07], by rw [wm1], by rw [wm2], fun a ha => ?_,
    by rw [rr7, rr6, rr5, rr4, rr3, rr2, rr1, rr0], by rw [rm7, rm6, rm5, rm4, rm3, rm2, rm1, rm0],
    by rw [o7, o6, o5, o4, o3, o2, o1, o0]⟩
  · rw [m7 _ (by omega), m6 _ (by omega), m5 _ (by omega), m4 _ (by omega), m3 _ (by omega),
      m2 _ (by omega), ← z0, a1 i hi]
  · rw [m7 _ (by omega), m6 _ (by omega), m5 _ (by omega), m4 _ (by omega), m3 _ (by omega),
      ← z1, a2 i hi]
  · rw [m7 _ (by omega), m6 _ (by omega), m5 _ (by omega), m4 _ (by omega), ← z2, a3 i hi]
  · rw [m7 _ (by omega), m6 _ (by omega), m5 _ (by omega), ← z3, a4 i hi]
  · rw [m7 _ (by omega), m6 _ (by omega), ← z4, a5 i hi]
  · rw [m7 _ (by omega), ← z5, a6 i hi]
  · rw [m7 _ (by omega), h11 a ha]

end Pp

end BKMNW

end PlanarFlow
