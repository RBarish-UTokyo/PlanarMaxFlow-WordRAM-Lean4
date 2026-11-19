module

public import PlanarFlow.BKMNW.NrPchB

/-!
# `pchP`, phase C: the out-lists by vertex label and the number of vertices

**`pchC = pG10 ; cstL ; pG11 ; osProg ; pG12 ; cntL`**: `ONE[i] := 1` (`A + 11m`), the out-lists
of all darts by vertex label (`osProg` with keys `VL`, flags `ONE`: `OB`, `OE`, `OL` at
`A + 12m`, `A + 13m`, `A + 14m`, scratch at `A + 15m`), the prefix counts of the labels (`CRV` at
`A + 18m`) and their number (`r9275 = rcnt VL m`, the number of vertices).

**`pchC_exec`**: within `15 m + osCost m m + 40` steps; memory changed only in
`[A + 11m, A + 19m)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv NegSSSP

/-- **Phase C of `pchP`**: the out-lists by vertex label, the number of vertices. -/
def pchC : Stmt := .seq pG10 (.seq cstL (.seq pG11 (.seq osProg (.seq pG12 cntL))))

section Exec

variable {P : Input} {W : ℕ}

/-- **Phase C of `pchP`** (see the module docstring). -/
theorem pchC_exec (c : Config) (hc : WordsBounded W c) {d A BT FR Kd m Z : ℕ}
    (R : PchR c d A BT FR Kd m Z) (hvl : ∀ i < m, c.nmem (A + 3 * m + i) < m) (hm : 0 < m)
    (w : A + 30 * m + 10 ≤ W) :
    ∃ c' t, Exec P W pchC c c' t ∧ t ≤ 15 * m + osCost m m + 40 ∧ PchR c' d A BT FR Kd m Z ∧
      c'.nreg 9275 = rcnt (fun j => c.nmem (A + 3 * m + j)) m ∧
      (∀ y < m, c'.nmem (A + 13 * m + y) = c'.nmem (A + 12 * m + y) +
          (nrF (fun i => c.nmem (A + 3 * m + i)) (fun _ => 1) m y).length ∧
        c'.nmem (A + 13 * m + y) ≤ m ∧
        ∀ t (ht : t < (nrF (fun i => c.nmem (A + 3 * m + i)) (fun _ => 1) m y).length),
          c'.nmem (A + 14 * m + (c'.nmem (A + 12 * m + y) + t)) =
            (nrF (fun i => c.nmem (A + 3 * m + i)) (fun _ => 1) m y)[t]) ∧
      (∀ a, (a < A + 11 * m ∨ A + 19 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- `pG10 ; cstL`: `ONE := 1`
  obtain ⟨c₁, t₁, e₁, ht₁, a51, a52, a53, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    pG10_exec (P := P) c hc (by clear * - w; omega)
  have R₁ := R.congr (fun x h1 h2 => f₁ x (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega)) (f₁ _ (by decide) (by decide) (by decide))
  rw [R.r04] at a51; rw [R.r18] at a52
  obtain ⟨c₂, t₂, e₂, ht₂, v₂, k₂, f₂, rr₂, rm₂, o₂⟩ := cstL_exec (P := P) c₁ e₁.wb_right
    a51 a52 a53 (by clear * - w; omega) (by clear * - w; omega)
  have R₂ := R₁.congr (fun x h1 h2 => f₂ x (by clear * - h1 h2; omega)) (f₂ _ (by decide))
  have mem₂ : ∀ a, (a < A + 11 * m ∨ A + 12 * m ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [k₂ a (by clear * - ha; omega), m₁]
  clear a51 a52 a53 k₂
  -- `pG11 ; osProg`: the out-lists
  obtain ⟨c₃, t₃, e₃, ht₃, b00, b01, b02, b04, b05, b06, b07, b08, b09, f₃, m₃, rr₃, rm₃, o₃⟩ :=
    pG11_exec (P := P) c₂ e₂.wb_right
  have R₃ := R₂.congr (fun x h1 h2 => f₃ x (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega) (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega) (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega) (by clear * - h1 h2; omega))
    (f₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
  rw [R₂.r04] at b00 b01; rw [R₂.r10] at b02; rw [R₂.r18] at b04; rw [R₂.r22] at b05
  rw [R₂.r23] at b06; rw [R₂.r19] at b07; rw [R₂.r20] at b08; rw [R₂.r21] at b09
  have hLay : OsLay m m (A + 3 * m) (A + 11 * m) (A + 15 * m) (A + 16 * m + 1) (A + 12 * m)
      (A + 13 * m) (A + 14 * m) W (fun i => c.nmem (A + 3 * m + i)) (fun _ => 1) :=
    ⟨fun i hi _ => hvl i hi, by clear * -; omega, by clear * -; omega, by clear * -; omega,
      by clear * -; omega, by clear * -; omega, by clear * -; omega, by clear * -; omega,
      by clear * -; omega, by clear * - w; omega, by clear * - w; omega, by clear * - w; omega,
      by clear * - w; omega, by clear * - w; omega, by clear * - w; omega⟩
  have hIn : OsIn m m (A + 3 * m) (A + 11 * m) (A + 15 * m) (A + 16 * m + 1) (A + 12 * m)
      (A + 13 * m) (A + 14 * m) (fun i => c.nmem (A + 3 * m + i)) (fun _ => 1) c₃ :=
    ⟨b00, b01, b02, b04, b05, b06, b07, b08, b09,
      fun i hi => by rw [m₃, mem₂ _ (by clear * - hi; omega)],
      fun i hi => by rw [m₃]; exact v₂ i hi⟩
  obtain ⟨c₄, t₄, e₄, ht₄, os₄, -, k₄, f₄, rr₄, rm₄, o₄⟩ :=
    nrOs_exec (P := P) hLay c₃ e₃.wb_right hIn
  have R₄ := R₃.congr (fun x h1 h2 => f₄ x (by clear * - h1 h2; omega)) (f₄ _ (by decide))
  have mem₄ : ∀ a, (a < A + 11 * m ∨ A + 19 * m ≤ a) → c₄.nmem a = c.nmem a := fun a ha => by
    rw [k₄ a (by clear * - ha hm; omega) (by clear * - ha; omega), m₃, mem₂ a (by clear * - ha; omega)]
  clear b00 b01 b02 b04 b05 b06 b07 b08 b09 hIn hLay
  -- `pG12 ; cntL`: the number of vertex labels
  obtain ⟨c₅, t₅, e₅, ht₅, g72, g73, g74, f₅, m₅, rr₅, rm₅, o₅⟩ :=
    pG12_exec (P := P) c₄ e₄.wb_right
  have R₅ := R₄.congr (fun x h1 h2 => f₅ x (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega)) (f₅ _ (by decide) (by decide) (by decide))
  rw [R₄.r04] at g72; rw [R₄.r10] at g73; rw [R₄.r24] at g74
  obtain ⟨c₆, t₆, e₆, ht₆, v₆, n₆, k₆, f₆, rr₆, rm₆, o₆⟩ :=
    cntL_exec (P := P) c₅ e₅.wb_right g72 g73 g74 (by clear * -; omega) (by clear * - w; omega)
      (by clear * - w; omega) (by clear * - w; omega)
  have R₆ := R₅.congr (fun x h1 h2 => f₆ x (by clear * - h1 h2; omega)) (f₆ _ (by decide))
  have k6 : ∀ a, (a < A + 18 * m ∨ A + 19 * m ≤ a) → c₆.nmem a = c₄.nmem a := fun a ha => by
    rw [k₆ a (by clear * - ha; omega), m₅]
  refine ⟨c₆, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))),
    by clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆; omega, R₆, ?_, fun y hy => ?_, fun a ha => ?_,
    by rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁], by rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · rw [n₆]
    exact nr_rcnt_congr fun j hj => by rw [m₅, mem₄ _ (by clear * - hj; omega)]
  · obtain ⟨u1, u2, u3⟩ := os₄ y hy
    refine ⟨by rw [k6 _ (by clear * - hy; omega), k6 _ (by clear * - hy; omega)]; exact u1,
      by rw [k6 _ (by clear * - hy; omega)]; exact u2, fun t ht => ?_⟩
    have hle : c₄.nmem (A + 12 * m + y) + t < m := by
      have := u2; rw [u1] at this; clear * - this ht; omega
    rw [k6 (A + 12 * m + y) (by clear * - hy; omega), k6 _ (by clear * - hle; omega)]
    exact u3 t ht
  · rw [k6 a (by clear * - ha; omega)]; exact mem₄ a ha

end Exec

end BKMNW

end PlanarFlow
