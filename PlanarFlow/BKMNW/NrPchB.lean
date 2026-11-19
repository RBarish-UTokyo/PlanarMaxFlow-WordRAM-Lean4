module

public import PlanarFlow.BKMNW.NrPchA

/-!
# `pchP`, phase B: the compact face keys

**`pchB = pG3 ; lgProg ; pG4 ; cstL ; pG5 ; olProg ; pG6 ; decL ; pG7 ; cntL ; pG8 ; lgProg ;
pG9 ; lgProg`**: `NX[i] = SG[RV[i]]` (`A + 5m`), its orbit labels (`FLB = olab + 1` at `A + 6m`,
`F0 = olab` at `A + 7m`), the prefix counts of the labels (`CR` at `A + 8m`, their number
`nf = rcnt (olab NX) m` in `r9226`), the keys `KY[i] = rkey NX i` (`A + 9m`) and the keys of the
reverse darts `NH[i] = KY[RV[i]]` (`A + 10m`).

**`pchB_exec`**: within `70 m + 60` steps; memory changed only in `[A + 5m, A + 11m)`.
`olab_congr`, `rcnt_congr`: labels and counts depend only on the values on `[0, m)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv

lemma nr_iter_congr {f g : ℕ → ℕ} {m : ℕ} (hp : PermOn f m) (h : ∀ x < m, f x = g x) {i : ℕ}
    (hi : i < m) : ∀ t, f^[t] i = g^[t] i
  | 0 => rfl
  | t + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← nr_iter_congr hp h hi t]
    exact h _ (OrbLab.iter_lt hp hi t)

/-- **The orbit labels depend only on the values on `[0, m)`.** -/
lemma nr_olab_congr {f g : ℕ → ℕ} {m : ℕ} (hp : PermOn f m) (h : ∀ x < m, f x = g x) {i : ℕ}
    (hi : i < m) : olab f i = olab g i := by
  classical
  unfold olab
  congr 1
  funext j
  simp only [nr_iter_congr hp h hi]

lemma nr_rcnt_congr {X Y : ℕ → ℕ} : ∀ {k : ℕ}, (∀ j < k, X j = Y j) → rcnt X k = rcnt Y k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [rcnt]
    rw [nr_rcnt_congr fun j hj => h j (by omega), h k (by omega)]

/-- **Phase B of `pchP`**: the compact face keys. -/
def pchB : Stmt :=
  .seq pG3 (.seq lgProg (.seq pG4 (.seq cstL (.seq pG5 (.seq OrbLab.olProg (.seq pG6 (.seq decL
    (.seq pG7 (.seq cntL (.seq pG8 (.seq lgProg (.seq pG9 lgProg))))))))))))

section Exec

variable {P : Input} {W : ℕ}

/-- **Phase B of `pchP`** (see the module docstring). -/
theorem pchB_exec (c : Config) (hc : WordsBounded W c) {d A BT FR Kd m Z : ℕ}
    (R : PchR c d A BT FR Kd m Z) (hrv : ∀ i < m, c.nmem (d + 4 + m + i) < m)
    (hp : PermOn (nxFP d m c.nmem) m) (hA : d + 4 + 7 * m ≤ A)
    (w : A + 30 * m + 10 ≤ W) :
    ∃ c' t, Exec P W pchB c c' t ∧ t ≤ 70 * m + 60 ∧ PchR c' d A BT FR Kd m Z ∧
      c'.nreg 9226 = rcnt (olab (nxFP d m c.nmem)) m ∧
      (∀ i < m, c'.nmem (A + 9 * m + i) = rkey (nxFP d m c.nmem) i) ∧
      (∀ i < m, c'.nmem (A + 10 * m + i) = rkey (nxFP d m c.nmem) (c.nmem (d + 4 + m + i))) ∧
      (∀ a, (a < A + 5 * m ∨ A + 11 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set f := nxFP d m c.nmem with hf
  -- `pG3 ; lgProg`: `NX[i] = SG[RV[i]]`
  obtain ⟨c₁, t₁, e₁, ht₁, a10, a11, a12, a13, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    pG3_exec (P := P) c hc
  have R₁ := R.congr (fun x h1 h2 => f₁ x (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)) (f₁ _ (by decide) (by decide) (by decide)
    (by decide))
  rw [R.r04] at a10; rw [R.r06] at a11; rw [R.r07] at a12; rw [R.r12] at a13
  obtain ⟨c₂, t₂, e₂, ht₂, v₂, k₂, f₂, rr₂, rm₂, o₂⟩ := lgProg_exec (P := P) c₁ e₁.wb_right
    a10 a11 a12 a13 (by clear * - w hA; omega) (by clear * - w hA; omega) (by clear * - w hA; omega)
    (fun j hj => by rw [m₁]; have := hrv j hj; clear * - this w hA; omega)
    (fun j hj => by clear * - hj hA; omega)
    (fun j hj => by rw [m₁]; have := hrv j hj; clear * - this hA; omega)
  have R₂ := R₁.congr (fun x h1 h2 => f₂ x (by clear * - h1 h2; omega)) (f₂ _ (by decide))
  have nx₂ : ∀ i < m, c₂.nmem (A + 5 * m + i) = f i := fun i hi => by
    rw [v₂ i hi, m₁]; rfl
  have mem₂ : ∀ a, (a < A + 5 * m ∨ A + 6 * m ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [k₂ a (by clear * - ha; omega), m₁]
  clear v₂ k₂ a10 a11 a12 a13
  -- `pG4 ; cstL`: `FLB := 0`
  obtain ⟨c₃, t₃, e₃, ht₃, b51, b52, b53, f₃, m₃, rr₃, rm₃, o₃⟩ := pG4_exec (P := P) c₂ e₂.wb_right
  have R₃ := R₂.congr (fun x h1 h2 => f₃ x (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega)) (f₃ _ (by decide) (by decide) (by decide))
  rw [R₂.r04] at b51; rw [R₂.r13] at b52
  obtain ⟨c₄, t₄, e₄, ht₄, v₄, k₄, f₄, rr₄, rm₄, o₄⟩ := cstL_exec (P := P) c₃ e₃.wb_right
    b51 b52 b53 (by clear * - w hA; omega) (by clear * - w hA; omega)
  have R₄ := R₃.congr (fun x h1 h2 => f₄ x (by clear * - h1 h2; omega)) (f₄ _ (by decide))
  have mem₄ : ∀ a, (a < A + 6 * m ∨ A + 7 * m ≤ a) → c₄.nmem a = c₂.nmem a := fun a ha => by
    rw [k₄ a (by clear * - ha; omega), m₃]
  clear k₄ b51 b52 b53
  -- `pG5 ; olProg`: `FLB[i] = olab NX i + 1`
  obtain ⟨c₅, t₅, e₅, ht₅, g50, g51, g52, f₅, m₅, rr₅, rm₅, o₅⟩ := pG5_exec (P := P) c₄ e₄.wb_right
  have R₅ := R₄.congr (fun x h1 h2 => f₅ x (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega)) (f₅ _ (by decide) (by decide) (by decide))
  rw [R₄.r12] at g50; rw [R₄.r13] at g51; rw [R₄.r04] at g52
  obtain ⟨c₆, t₆, e₆, ht₆, l₆, k₆, f₆, rr₆, rm₆, o₆⟩ := olProg_exec (P := P) (W := W) (f := f)
    hp (Pb := A + 5 * m) (Lb := A + 6 * m) (by clear * -; omega) (by clear * - w hA; omega)
    (by clear * - w hA; omega) c₅ e₅.wb_right g50 g51 g52
    (fun x hx => by rw [m₅, mem₄ _ (by clear * - hx; omega)]; exact nx₂ x hx)
    (fun x hx => by rw [m₅]; exact v₄ x hx)
  have R₆ := R₅.congr (fun x h1 h2 => f₆ x (by clear * - h1 h2; omega)) (f₆ _ (by decide))
  have mem₆ : ∀ a, (a < A + 6 * m ∨ A + 7 * m ≤ a) → c₆.nmem a = c₂.nmem a := fun a ha => by
    rw [k₆ a (by clear * - ha; omega), m₅, mem₄ a ha]
  clear k₆ g50 g51 g52 v₄
  -- `pG6 ; decL`: `F0[i] = olab NX i`
  obtain ⟨c₇, t₇, e₇, ht₇, h41, h42, h43, f₇, m₇, rr₇, rm₇, o₇⟩ := pG6_exec (P := P) c₆ e₆.wb_right
  have R₇ := R₆.congr (fun x h1 h2 => f₇ x (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega)) (f₇ _ (by decide) (by decide) (by decide))
  rw [R₆.r04] at h41; rw [R₆.r13] at h42; rw [R₆.r14] at h43
  obtain ⟨c₈, t₈, e₈, ht₈, v₈, k₈, f₈, rr₈, rm₈, o₈⟩ := decL_exec (P := P) c₇ e₇.wb_right
    h41 h42 h43 (by clear * -; omega) (by clear * - w hA; omega) (by clear * - w hA; omega)
    (by clear * - w hA; omega)
  have R₈ := R₇.congr (fun x h1 h2 => f₈ x (by clear * - h1 h2; omega)) (f₈ _ (by decide))
  have f0₈ : ∀ i < m, c₈.nmem (A + 7 * m + i) = olab f i := fun i hi => by
    rw [v₈ i hi, m₇, l₆ i hi]; clear * -; omega
  have mem₈ : ∀ a, (a < A + 7 * m ∨ A + 8 * m ≤ a) → c₈.nmem a = c₆.nmem a := fun a ha => by
    rw [k₈ a (by clear * - ha; omega), m₇]
  clear v₈ k₈ h41 h42 h43
  -- `pG7 ; cntL`: `CR[k] = rcnt (olab NX) k`
  obtain ⟨c₉, t₉, e₉, ht₉, i72, i73, i74, f₉, m₉, rr₉, rm₉, o₉⟩ := pG7_exec (P := P) c₈ e₈.wb_right
  have R₉ := R₈.congr (fun x h1 h2 => f₉ x (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega)) (f₉ _ (by decide) (by decide) (by decide))
  rw [R₈.r04] at i72; rw [R₈.r14] at i73; rw [R₈.r15] at i74
  obtain ⟨c₁₀, t₁₀, e₁₀, ht₁₀, v₁₀, n₁₀, k₁₀, f₁₀, rr₁₀, rm₁₀, o₁₀⟩ :=
    cntL_exec (P := P) c₉ e₉.wb_right i72 i73 i74 (by clear * -; omega) (by clear * - w hA; omega)
      (by clear * - w hA; omega) (by clear * - w hA; omega)
  have R₁₀ := R₉.congr (fun x h1 h2 => f₁₀ x (by clear * - h1 h2; omega)) (f₁₀ _ (by decide))
  have hX : ∀ {k}, k ≤ m → rcnt (fun j => c₉.nmem (A + 7 * m + j)) k = rcnt (olab f) k :=
    fun hk => nr_rcnt_congr fun j hj => by rw [m₉]; exact f0₈ j (by omega)
  have cr₁₀ : ∀ i < m, c₁₀.nmem (A + 8 * m + i) = rcnt (olab f) i := fun i hi => by
    rw [v₁₀ i hi, hX hi.le]
  have nf₁₀ : c₁₀.nreg 9275 = rcnt (olab f) m := by rw [n₁₀, hX le_rfl]
  have mem₁₀ : ∀ a, (a < A + 8 * m ∨ A + 9 * m ≤ a) → c₁₀.nmem a = c₈.nmem a := fun a ha => by
    rw [k₁₀ a (by clear * - ha; omega), m₉]
  clear v₁₀ n₁₀ k₁₀ i72 i73 i74 hX
  -- `pG8 ; lgProg`: `KY[i] = CR[F0[i]]`
  obtain ⟨c₁₁, t₁₁, e₁₁, ht₁₁, j10, j11, j12, j13, j26, f₁₁, m₁₁, rr₁₁, rm₁₁, o₁₁⟩ :=
    pG8_exec (P := P) c₁₀ e₁₀.wb_right
  have R₁₁ := R₁₀.congr (fun x h1 h2 => f₁₁ x (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega) (by clear * - h1 h2; omega) (by clear * - h1 h2; omega))
    (f₁₁ _ (by decide) (by decide) (by decide) (by decide) (by decide))
  rw [nf₁₀] at j26; rw [R₁₀.r04] at j10; rw [R₁₀.r14] at j11; rw [R₁₀.r15] at j12
  rw [R₁₀.r16] at j13
  have f0₁₁ : ∀ i < m, c₁₁.nmem (A + 7 * m + i) = olab f i := fun i hi => by
    rw [m₁₁, mem₁₀ _ (by clear * - hi; omega)]; exact f0₈ i hi
  have hlt : ∀ i < m, olab f i < m := fun i hi => olab_lt hp hi
  obtain ⟨c₁₂, t₁₂, e₁₂, ht₁₂, v₁₂, k₁₂, f₁₂, rr₁₂, rm₁₂, o₁₂⟩ := lgProg_exec (P := P) c₁₁
    e₁₁.wb_right j10 j11 j12 j13 (by clear * - w hA; omega) (by clear * - w hA; omega)
    (by clear * - w hA; omega)
    (fun j hj => by rw [f0₁₁ j hj]; have := hlt j hj; clear * - this w hA; omega)
    (fun j hj => by clear * - hj; omega)
    (fun j hj => by rw [f0₁₁ j hj]; have := hlt j hj; clear * - this; omega)
  have R₁₂ := R₁₁.congr (fun x h1 h2 => f₁₂ x (by clear * - h1 h2; omega)) (f₁₂ _ (by decide))
  have ky₁₂ : ∀ i < m, c₁₂.nmem (A + 9 * m + i) = rkey f i := fun i hi => by
    rw [v₁₂ i hi, f0₁₁ i hi, m₁₁, cr₁₀ _ (hlt i hi)]; rfl
  have mem₁₂ : ∀ a, (a < A + 9 * m ∨ A + 10 * m ≤ a) → c₁₂.nmem a = c₁₀.nmem a := fun a ha => by
    rw [k₁₂ a (by clear * - ha; omega), m₁₁]
  have n26 : c₁₂.nreg 9226 = rcnt (olab f) m := by
    rw [f₁₂ _ (by decide)]; exact j26
  clear v₁₂ k₁₂ j10 j11 j12 j13
  -- `pG9 ; lgProg`: `NH[i] = KY[RV[i]]`
  obtain ⟨c₁₃, t₁₃, e₁₃, ht₁₃, l10, l11, l12, l13, f₁₃, m₁₃, rr₁₃, rm₁₃, o₁₃⟩ :=
    pG9_exec (P := P) c₁₂ e₁₂.wb_right
  have R₁₃ := R₁₂.congr (fun x h1 h2 => f₁₃ x (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega) (by clear * - h1 h2; omega))
    (f₁₃ _ (by decide) (by decide) (by decide) (by decide))
  rw [R₁₂.r04] at l10; rw [R₁₂.r06] at l11; rw [R₁₂.r16] at l12; rw [R₁₂.r17] at l13
  have rv₁₃ : ∀ i < m, c₁₃.nmem (d + 4 + m + i) = c.nmem (d + 4 + m + i) := fun i hi => by
    rw [m₁₃, mem₁₂ _ (by clear * - hA hi; omega), mem₁₀ _ (by clear * - hA hi; omega),
      mem₈ _ (by clear * - hA hi; omega), mem₆ _ (by clear * - hA hi; omega),
      mem₂ _ (by clear * - hA hi; omega)]
  obtain ⟨c₁₄, t₁₄, e₁₄, ht₁₄, v₁₄, k₁₄, f₁₄, rr₁₄, rm₁₄, o₁₄⟩ := lgProg_exec (P := P) c₁₃
    e₁₃.wb_right l10 l11 l12 l13 (by clear * - w hA; omega) (by clear * - w hA; omega)
    (by clear * - w hA; omega)
    (fun j hj => by rw [rv₁₃ j hj]; have := hrv j hj; clear * - this w hA; omega)
    (fun j hj => by clear * - hj hA; omega)
    (fun j hj => by rw [rv₁₃ j hj]; have := hrv j hj; clear * - this; omega)
  have R₁₄ := R₁₃.congr (fun x h1 h2 => f₁₄ x (by clear * - h1 h2; omega)) (f₁₄ _ (by decide))
  refine ⟨c₁₄, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + (t₈ + (t₉ + (t₁₀ + (t₁₁ + (t₁₂ +
    (t₁₃ + t₁₄)))))))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉ (.seq e₁₀
      (.seq e₁₁ (.seq e₁₂ (.seq e₁₃ e₁₄)))))))))))),
    by clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ ht₇ ht₈ ht₉ ht₁₀ ht₁₁ ht₁₂ ht₁₃ ht₁₄; omega, R₁₄,
    by rw [f₁₄ _ (by decide), f₁₃ _ (by decide) (by decide) (by decide) (by decide)]; exact n26,
    fun i hi => ?_, fun i hi => ?_, fun a ha => ?_,
    by rw [rr₁₄, rr₁₃, rr₁₂, rr₁₁, rr₁₀, rr₉, rr₈, rr₇, rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₁₄, rm₁₃, rm₁₂, rm₁₁, rm₁₀, rm₉, rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₁₄, o₁₃, o₁₂, o₁₁, o₁₀, o₉, o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · rw [k₁₄ _ (by clear * - hi; omega), m₁₃]; exact ky₁₂ i hi
  · rw [v₁₄ i hi, rv₁₃ i hi, m₁₃]; exact ky₁₂ _ (hrv i hi)
  · rw [k₁₄ _ (by clear * - ha; omega), m₁₃, mem₁₂ _ (by clear * - ha; omega),
      mem₁₀ _ (by clear * - ha; omega), mem₈ _ (by clear * - ha; omega),
      mem₆ _ (by clear * - ha; omega), mem₂ _ (by clear * - ha; omega)]

end Exec

end BKMNW

end PlanarFlow
