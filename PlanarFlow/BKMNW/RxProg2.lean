module

public import PlanarFlow.BKMNW.RxProg

/-!
# The root's record on the machine: the whole writer

**`rxProg_exec`** (see `RxProg.lean`): from `r3002 = Hb`, `mem (Hb + 5) = N`, the bases
`VTb = mem (Hb - 1)`, `RTb = mem (Hb - 2)` (arrays below `Hb - 2`): the pointer, the header, the
seven arrays of the record, the frame end `eF` at `Hb + 2` and in `r3003`; within `49 N + 120`
steps; the memory below `Hb + 2` and in `(Hb + 2, e₀)` kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The root's record on the machine** (see the module docstring). -/
theorem rxProg_exec (c : Config) (hc : WordsBounded W c) {Hb N VTb RTb : ℕ}
    (r2 : c.nreg 3002 = Hb) (hN : c.nmem (Hb + 5) = N) (hHb : 2 ≤ Hb)
    (hv : c.nmem (Hb - 1) = VTb) (hr : c.nmem (Hb - 1 - 1) = RTb)
    (iv : VTb + N ≤ Hb - 2) (ir : RTb + N ≤ Hb - 2)
    (w : Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N ≤ W) :
    ∃ c' t, Exec I W rxProg c c' t ∧ t ≤ 49 * N + 120 ∧
      c'.nreg 3003 = Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N ∧
      c'.nmem (Hb + 2) = Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N ∧
      c'.nmem (Hb + 5 + 4 + 7 * N) = Hb + 5 + 4 + 7 * N + 1 ∧
      c'.nmem (Hb + 5 + 4 + 7 * N + 1) = N ∧ c'.nmem (Hb + 5 + 4 + 7 * N + 1 + 1) = 0 ∧
      c'.nmem (Hb + 5 + 4 + 7 * N + 1 + 2) = 1 ∧
      (∀ j < N, c'.nmem (Hb + 5 + 4 + 7 * N + 1 + 3 + j) = c.nmem (Hb + 9 + j)) ∧
      (∀ j < N, c'.nmem (Hb + 5 + 4 + 7 * N + 1 + 3 + N + j) = c.nmem (Hb + 9 + N + j)) ∧
      (∀ j < N, c'.nmem (Hb + 5 + 4 + 7 * N + 1 + 3 + 2 * N + j) = c.nmem (Hb + 9 + 5 * N + j)) ∧
      (∀ j < N, c'.nmem (Hb + 5 + 4 + 7 * N + 1 + 3 + 3 * N + j) = c.nmem (Hb + 9 + 4 * N + j)) ∧
      (∀ j < N, c'.nmem (Hb + 5 + 4 + 7 * N + 1 + 3 + 4 * N + j) = c.nmem (VTb + j)) ∧
      (∀ j < N, c'.nmem (Hb + 5 + 4 + 7 * N + 1 + 3 + 5 * N + j) = c.nmem (RTb + j)) ∧
      (∀ j < N, c'.nmem (Hb + 5 + 4 + 7 * N + 1 + 3 + 6 * N + j) = c.nmem (Hb + 9 + j)) ∧
      (∀ a, (a < Hb + 2 ∨ (Hb + 2 < a ∧ a < Hb + 5 + 4 + 7 * N)) → c'.nmem a = c.nmem a) ∧
      (∀ x, x < 3003 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a00, a03, a09, a10, a11, a12, a13, a14, a15, a16, m1, n1, rr1, rm1,
    o1⟩ := rxA_exec (I := I) c hc r2 hN w
  -- the memory after the header: the input below `e₀`
  have M1 : ∀ a, a < Hb + 5 + 4 + 7 * N → c₁.nmem a = c.nmem a := fun a ha => by
    rw [m1, upd_other _ _ _ (by clear * - ha; omega), upd_other _ _ _ (by clear * - ha; omega),
      upd_other _ _ _ (by clear * - ha; omega), upd_other _ _ _ (by clear * - ha; omega)]
  obtain ⟨c₂, t₂, e₂, ht₂, b17, b18, b19, b20, b22, b23, b03, m2, n2, rr2, rm2, o2⟩ :=
    rxB_exec (I := I) c₁ e₁.wb_right a00 a03 a16 hHb
      ((M1 _ (by clear * - hHb; omega)).trans hv)
      ((M1 _ (by clear * - hHb; omega)).trans hr) (by clear * - w; omega)
  have q2 : ∀ x, (5701 < x ∧ x < 5717) → c₂.nreg x = c₁.nreg x := fun x hx =>
    n2 x (Or.inr (Or.inr (Or.inl hx)))
  have M2 : ∀ a, a ≠ Hb + 2 → c₂.nmem a = c₁.nmem a := fun a ha => by
    rw [m2, upd_other _ _ _ ha]
  -- the seven copies
  have hW1 : N + 1 ≤ W := by clear * - w; omega
  obtain ⟨c₃, t₃, e₃, ht₃, k3, mm3, nn3, rr3, rm3, o3⟩ := rxCp_exec (I := I) c₂ e₂.wb_right
    (src := 5717) (dst := 5709) (by decide) (by decide) ((q2 5703 (by decide)).trans a03) b17
    ((q2 5709 (by decide)).trans a09) (Or.inl (by clear * -; omega)) (by clear * - w; omega)
    (by clear * - w; omega) hW1
  obtain ⟨c₄, t₄, e₄, ht₄, k4, mm4, nn4, rr4, rm4, o4⟩ := rxCp_exec (I := I) c₃ e₃.wb_right
    (src := 5718) (dst := 5710) (by decide) (by decide)
    ((nn3 5703 (by decide)).trans ((q2 5703 (by decide)).trans a03))
    ((nn3 5718 (by decide)).trans b18)
    ((nn3 5710 (by decide)).trans ((q2 5710 (by decide)).trans a10))
    (Or.inl (by clear * -; omega)) (by clear * - w; omega) (by clear * - w; omega) hW1
  obtain ⟨c₅, t₅, e₅, ht₅, k5, mm5, nn5, rr5, rm5, o5⟩ := rxCp_exec (I := I) c₄ e₄.wb_right
    (src := 5720) (dst := 5711) (by decide) (by decide)
    ((nn4 5703 (by decide)).trans ((nn3 5703 (by decide)).trans ((q2 5703 (by decide)).trans a03)))
    ((nn4 5720 (by decide)).trans ((nn3 5720 (by decide)).trans b20))
    ((nn4 5711 (by decide)).trans ((nn3 5711 (by decide)).trans ((q2 5711 (by decide)).trans a11)))
    (Or.inl (by clear * -; omega)) (by clear * - w; omega) (by clear * - w; omega) hW1
  have R5 : ∀ x, (x < 4910 ∨ 4916 < x) → c₅.nreg x = c₂.nreg x := fun x hx => by
    rw [nn5 x hx, nn4 x hx, nn3 x hx]
  obtain ⟨c₆, t₆, e₆, ht₆, k6, mm6, nn6, rr6, rm6, o6⟩ := rxCp_exec (I := I) c₅ e₅.wb_right
    (src := 5719) (dst := 5712) (by decide) (by decide)
    ((R5 5703 (by decide)).trans ((q2 5703 (by decide)).trans a03))
    ((R5 5719 (by decide)).trans b19)
    ((R5 5712 (by decide)).trans ((q2 5712 (by decide)).trans a12))
    (Or.inl (by clear * -; omega)) (by clear * - w; omega) (by clear * - w; omega) hW1
  obtain ⟨c₇, t₇, e₇, ht₇, k7, mm7, nn7, rr7, rm7, o7⟩ := rxCp_exec (I := I) c₆ e₆.wb_right
    (src := 5722) (dst := 5713) (by decide) (by decide)
    ((nn6 5703 (by decide)).trans ((R5 5703 (by decide)).trans ((q2 5703 (by decide)).trans a03)))
    ((nn6 5722 (by decide)).trans ((R5 5722 (by decide)).trans b22))
    ((nn6 5713 (by decide)).trans ((R5 5713 (by decide)).trans ((q2 5713 (by decide)).trans a13)))
    (Or.inl (by clear * - iv; omega)) (by clear * - iv w; omega) (by clear * - w; omega) hW1
  have R7 : ∀ x, (x < 4910 ∨ 4916 < x) → c₇.nreg x = c₂.nreg x := fun x hx => by
    rw [nn7 x hx, nn6 x hx, R5 x hx]
  obtain ⟨c₈, t₈, e₈, ht₈, k8, mm8, nn8, rr8, rm8, o8⟩ := rxCp_exec (I := I) c₇ e₇.wb_right
    (src := 5723) (dst := 5714) (by decide) (by decide)
    ((R7 5703 (by decide)).trans ((q2 5703 (by decide)).trans a03))
    ((R7 5723 (by decide)).trans b23)
    ((R7 5714 (by decide)).trans ((q2 5714 (by decide)).trans a14))
    (Or.inl (by clear * - ir; omega)) (by clear * - ir w; omega) (by clear * - w; omega) hW1
  obtain ⟨c₉, t₉, e₉, ht₉, k9, mm9, nn9, rr9, rm9, o9⟩ := rxCp_exec (I := I) c₈ e₈.wb_right
    (src := 5717) (dst := 5715) (by decide) (by decide)
    ((nn8 5703 (by decide)).trans ((R7 5703 (by decide)).trans ((q2 5703 (by decide)).trans a03)))
    ((nn8 5717 (by decide)).trans ((R7 5717 (by decide)).trans b17))
    ((nn8 5715 (by decide)).trans ((R7 5715 (by decide)).trans ((q2 5715 (by decide)).trans a15)))
    (Or.inl (by clear * -; omega)) (by clear * - w; omega) (by clear * - w; omega) hW1
  -- the memory: below `R + 3` every copy keeps the memory
  have L : ∀ a, a < Hb + 5 + 4 + 7 * N + 1 + 3 → c₉.nmem a = c₂.nmem a := fun a ha => by
    rw [mm9 a (Or.inl (by clear * - ha; omega)), mm8 a (Or.inl (by clear * - ha; omega)),
      mm7 a (Or.inl (by clear * - ha; omega)), mm6 a (Or.inl (by clear * - ha; omega)),
      mm5 a (Or.inl (by clear * - ha; omega)), mm4 a (Or.inl (by clear * - ha; omega)),
      mm3 a (Or.inl (by clear * - ha; omega))]
  -- the sources: the input
  have SRC : ∀ a, a < Hb + 5 + 4 + 7 * N → a ≠ Hb + 2 → c₂.nmem a = c.nmem a := fun a h1 h2 => by
    rw [M2 a h2, M1 a h1]
  have ht : t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + (t₈ + t₉))))))) ≤ 49 * N + 120 := by
    clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ ht₇ ht₈ ht₉; omega
  refine ⟨c₉, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉))))))),
    ht, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
    fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun a ha => ?_, fun x hx => ?_,
    by rw [rr9, rr8, rr7, rr6, rr5, rr4, rr3, rr2, rr1],
    by rw [rm9, rm8, rm7, rm6, rm5, rm4, rm3, rm2, rm1],
    by rw [o9, o8, o7, o6, o5, o4, o3, o2, o1]⟩
  · rw [nn9 3003 (by decide), nn8 3003 (by decide), R7 3003 (by decide)]; exact b03
  · rw [L _ (by clear * -; omega), m2, upd_same]
  · rw [L _ (by clear * -; omega), M2 _ (by clear * - hHb; omega), m1,
      upd_other _ _ _ (by clear * -; omega), upd_other _ _ _ (by clear * -; omega),
      upd_other _ _ _ (by clear * -; omega), upd_same]
  · rw [L _ (by clear * -; omega), M2 _ (by clear * - hHb; omega), m1,
      upd_other _ _ _ (by clear * -; omega), upd_other _ _ _ (by clear * -; omega), upd_same]
  · rw [L _ (by clear * -; omega), M2 _ (by clear * - hHb; omega), m1,
      upd_other _ _ _ (by clear * -; omega), upd_same]
  · rw [L _ (by clear * -; omega), M2 _ (by clear * - hHb; omega), m1, upd_same]
  · rw [mm9 _ (Or.inl (by clear * - hj; omega)), mm8 _ (Or.inl (by clear * - hj; omega)), mm7 _ (Or.inl (by clear * - hj; omega)), mm6 _ (Or.inl (by clear * - hj; omega)), mm5 _ (Or.inl (by clear * - hj; omega)), mm4 _ (Or.inl (by clear * - hj; omega)), k3 j hj, SRC _ (by clear * - hj; omega) (by clear * - hj; omega)]
  · rw [mm9 _ (Or.inl (by clear * - hj; omega)), mm8 _ (Or.inl (by clear * - hj; omega)), mm7 _ (Or.inl (by clear * - hj; omega)), mm6 _ (Or.inl (by clear * - hj; omega)), mm5 _ (Or.inl (by clear * - hj; omega)), k4 j hj, mm3 _ (Or.inl (by clear * - hj; omega)), SRC _ (by clear * - hj; omega) (by clear * - hj; omega)]
  · rw [mm9 _ (Or.inl (by clear * - hj; omega)), mm8 _ (Or.inl (by clear * - hj; omega)), mm7 _ (Or.inl (by clear * - hj; omega)), mm6 _ (Or.inl (by clear * - hj; omega)), k5 j hj, mm4 _ (Or.inl (by clear * - hj; omega)), mm3 _ (Or.inl (by clear * - hj; omega)), SRC _ (by clear * - hj; omega) (by clear * - hj; omega)]
  · rw [mm9 _ (Or.inl (by clear * - hj; omega)), mm8 _ (Or.inl (by clear * - hj; omega)), mm7 _ (Or.inl (by clear * - hj; omega)), k6 j hj, mm5 _ (Or.inl (by clear * - hj; omega)), mm4 _ (Or.inl (by clear * - hj; omega)), mm3 _ (Or.inl (by clear * - hj; omega)), SRC _ (by clear * - hj; omega) (by clear * - hj; omega)]
  · rw [mm9 _ (Or.inl (by clear * - hj; omega)), mm8 _ (Or.inl (by clear * - hj; omega)), k7 j hj, mm6 _ (Or.inl (by clear * - hj iv; omega)), mm5 _ (Or.inl (by clear * - hj iv; omega)), mm4 _ (Or.inl (by clear * - hj iv; omega)), mm3 _ (Or.inl (by clear * - hj iv; omega)), SRC _ (by clear * - hj iv; omega) (by clear * - hj iv; omega)]
  · rw [mm9 _ (Or.inl (by clear * - hj; omega)), k8 j hj, mm7 _ (Or.inl (by clear * - hj ir; omega)), mm6 _ (Or.inl (by clear * - hj ir; omega)), mm5 _ (Or.inl (by clear * - hj ir; omega)), mm4 _ (Or.inl (by clear * - hj ir; omega)), mm3 _ (Or.inl (by clear * - hj ir; omega)), SRC _ (by clear * - hj ir; omega) (by clear * - hj ir; omega)]
  · rw [k9 j hj, mm8 _ (Or.inl (by clear * - hj; omega)), mm7 _ (Or.inl (by clear * - hj; omega)), mm6 _ (Or.inl (by clear * - hj; omega)), mm5 _ (Or.inl (by clear * - hj; omega)), mm4 _ (Or.inl (by clear * - hj; omega)), mm3 _ (Or.inl (by clear * - hj; omega)), SRC _ (by clear * - hj; omega) (by clear * - hj; omega)]
  · rw [L a (by clear * - ha; omega), SRC a (by clear * - ha; omega) (by clear * - ha; omega)]
  · rw [nn9 x (by clear * - hx; omega), nn8 x (by clear * - hx; omega),
      R7 x (by clear * - hx; omega), n2 x (Or.inl hx), n1 x (by clear * - hx; omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
