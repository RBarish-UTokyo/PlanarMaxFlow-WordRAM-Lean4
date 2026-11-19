module

public import PlanarFlow.BKMNW.NrKahnAll

/-!
# The visits of the push-back on the machine: the program and its blocks

Inputs (registers `9151 … 9162`): the flow array `G` (`G[i] = Z + g(ed i)`), `RV`, `VL`, `Z`,
`DV` (`Kd + div g` at every vertex label), `BT` (`Kd + β`), `FR` (free flags), the order `Q`
of the vertex labels and its length `nv`, the out-lists `OB`, `OE`, `OL` of all darts by tail
label (increasing index). Registers `9163 … 9179`.

For `t < nv`: `v := Q[t]`; if `FR[v] = 0` and `BT[v] < DV[v]`: `rem := DV[v] - BT[v]` and for
every dart `i` of `v` in order, if `Z < G[i]` and `0 < rem`: `a := min rem (G[i] - Z)`,
`G[i] -= a`, `G[RV[i]] += a`, `rem -= a`, `DV[v] -= a`, `DV[VL[RV[i]]] += a` (the reduction
`redStep`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

/-- Constants, `t := 0`. -/
def pA : Stmt := block [.constN 9163 1, .constN 9164 0, .constN 9165 0]

/-- `v := Q[t]`, `t := t + 1`, `fr := FR[v]`, `bt := BT[v]`, `dv := DV[v]`. -/
def pO1 : Stmt :=
  block [.addN 9170 9158 9165, .loadN 9166 9170, .addN 9165 9165 9163, .addN 9170 9157 9166,
    .loadN 9171 9170, .addN 9170 9156 9166, .loadN 9172 9170, .addN 9170 9155 9166,
    .loadN 9173 9170]

/-- `rem := dv - bt`, `k := OB[v]`, `e := OE[v]`. -/
def pI1 : Stmt :=
  block [.subN 9167 9173 9172, .addN 9170 9160 9166, .loadN 9168 9170, .addN 9170 9161 9166,
    .loadN 9169 9170]

/-- `i := OL[k]`, `gi := G[i]`, `k := k + 1`. -/
def pR1 : Stmt :=
  block [.addN 9170 9162 9168, .loadN 9174 9170, .addN 9175 9151 9174, .loadN 9176 9175,
    .addN 9168 9168 9163]

/-- `x := gi - Z`. -/
def pR2 : Stmt := block [.subN 9177 9176 9154]

/-- `G[i] -= a`, `rem -= a`, `r := RV[i]`, `G[r] += a`. -/
def pU1 : Stmt :=
  block [.subN 9176 9176 9178, .storeN 9175 9176, .subN 9167 9167 9178, .addN 9170 9152 9174,
    .loadN 9170 9170, .addN 9179 9151 9170, .loadN 9177 9179, .addN 9177 9177 9178,
    .storeN 9179 9177]

/-- `DV[v] -= a`, `DV[VL[r]] += a`. -/
def pU2 : Stmt :=
  block [.addN 9179 9155 9166, .loadN 9177 9179, .subN 9177 9177 9178, .storeN 9179 9177,
    .addN 9179 9153 9170, .loadN 9179 9179, .addN 9179 9155 9179, .loadN 9177 9179,
    .addN 9177 9177 9178, .storeN 9179 9177]

/-- The reduction of a positive dart with `rem > 0`. -/
def pRed : Stmt :=
  .seq pR2 (.seq (.ifLtN 9167 9177 (block [.copyN 9178 9167]) (block [.copyN 9178 9177]))
    (.seq pU1 pU2))

/-- One dart of the visited vertex. -/
def pR : Stmt := .seq pR1 (.ifLtN 9154 9176 (.ifLtN 9164 9167 pRed .skip) .skip)

/-- One vertex of the order. -/
def pO : Stmt :=
  .seq pO1 (.ifLtN 9164 9171 .skip (.ifLtN 9172 9173 (.seq pI1 (.whileLtN 9168 9169 pR)) .skip))

/-- **The visits.** -/
def pushP : Stmt := .seq pA (.whileLtN 9165 9159 pO)

theorem pushP_natOnly : Klein.natOnly pushP = true := by kernel_rfl

section Blocks

variable {P : Input} {W : ℕ}

theorem pR1_exec (c : Config) (hc : WordsBounded W c) {G OL k : ℕ} (r1 : c.nreg 9151 = G)
    (r62 : c.nreg 9162 = OL) (r63 : c.nreg 9163 = 1) (r68 : c.nreg 9168 = k)
    (w1 : OL + k ≤ W) (w2 : G + c.nmem (OL + k) ≤ W) (w3 : k + 1 ≤ W) :
    ∃ c' t, Exec P W pR1 c c' t ∧ t = 5 ∧ c'.nreg 9174 = c.nmem (OL + k) ∧
      c'.nreg 9175 = G + c.nmem (OL + k) ∧ c'.nreg 9176 = c.nmem (G + c.nmem (OL + k)) ∧
      c'.nreg 9168 = k + 1 ∧
      (∀ x, x ≠ 9168 → x ≠ 9170 → (x < 9174 ∨ 9176 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pR1
  exec_block
  all_goals try (config_simp; simp only [r1, r62, r63, r68]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r1, r62, r63, r68]
  simp only [upd_apply]; split_ifs <;> omega

theorem pU1_exec (c : Config) (hc : WordsBounded W c) {G RV gi a rem i : ℕ}
    (r1 : c.nreg 9151 = G) (r2 : c.nreg 9152 = RV) (r67 : c.nreg 9167 = rem)
    (r74 : c.nreg 9174 = i) (r75 : c.nreg 9175 = G + i) (r76 : c.nreg 9176 = gi)
    (r78 : c.nreg 9178 = a) (hne : G + i ≠ G + c.nmem (RV + i)) (hGR : G + i ≠ RV + i)
    (w1 : RV + i ≤ W)
    (w2 : G + c.nmem (RV + i) ≤ W) (w3 : c.nmem (G + c.nmem (RV + i)) + a ≤ W) (w4 : G + i ≤ W) :
    ∃ c' t, Exec P W pU1 c c' t ∧ t = 9 ∧ c'.nreg 9167 = rem - a ∧
      c'.nreg 9170 = c.nmem (RV + i) ∧
      c'.nmem = upd (upd c.nmem (G + i) (gi - a)) (G + c.nmem (RV + i))
        (c.nmem (G + c.nmem (RV + i)) + a) ∧
      (∀ x, x ≠ 9167 → x ≠ 9170 → x ≠ 9176 → x ≠ 9177 → x ≠ 9179 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hRVi : c.nmem (RV + i) ≤ W := hc.2 _
  unfold pU1
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r67, r74, r75, r76, r78,
    upd_other _ _ _ (Ne.symm hGR), upd_other _ _ _ (Ne.symm hne)]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r67, r78]
  · config_simp; simp only [r2, r74, r75, upd_other _ _ _ (Ne.symm hGR)]
  · config_simp
    simp only [r1, r2, r74, r75, r76, r78, upd_other _ _ _ (Ne.symm hGR),
      upd_other _ _ _ (Ne.symm hne)]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem pU2_exec (c : Config) (hc : WordsBounded W c) {VL DV v a r : ℕ}
    (r3 : c.nreg 9153 = VL) (r5 : c.nreg 9155 = DV) (r66 : c.nreg 9166 = v)
    (r70 : c.nreg 9170 = r) (r78 : c.nreg 9178 = a) (hne : DV + v ≠ VL + r) (w1 : DV + v ≤ W)
    (w2 : VL + r ≤ W) (w3 : DV + c.nmem (VL + r) ≤ W)
    (w4 : (upd c.nmem (DV + v) (c.nmem (DV + v) - a)) (DV + c.nmem (VL + r)) + a ≤ W) :
    ∃ c' t, Exec P W pU2 c c' t ∧ t = 10 ∧
      c'.nmem = upd (upd c.nmem (DV + v) (c.nmem (DV + v) - a)) (DV + c.nmem (VL + r))
        ((upd c.nmem (DV + v) (c.nmem (DV + v) - a)) (DV + c.nmem (VL + r)) + a) ∧
      (∀ x, x ≠ 9177 → x ≠ 9179 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pU2
  exec_block
  all_goals try (config_simp; simp only [r3, r5, r66, r70, r78, upd_other _ _ _ (Ne.symm hne)]; omega)
  refine ⟨rfl, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r3, r5, r66, r70, r78, upd_other _ _ _ (Ne.symm hne)]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The reduction of a positive dart.** -/
theorem pRed_exec (c : Config) (hc : WordsBounded W c) {G RV VL Z DV v rem i : ℕ}
    (r1 : c.nreg 9151 = G) (r2 : c.nreg 9152 = RV) (r3 : c.nreg 9153 = VL)
    (r4 : c.nreg 9154 = Z) (r5 : c.nreg 9155 = DV) (r66 : c.nreg 9166 = v)
    (r67 : c.nreg 9167 = rem) (r74 : c.nreg 9174 = i) (r75 : c.nreg 9175 = G + i)
    (r76 : c.nreg 9176 = c.nmem (G + i))
    (n1 : G + i ≠ G + c.nmem (RV + i)) (n2 : G + i ≠ RV + i)
    (n3 : DV + v ≠ VL + c.nmem (RV + i)) (n4 : G + i ≠ VL + c.nmem (RV + i))
    (n5 : G + c.nmem (RV + i) ≠ VL + c.nmem (RV + i)) (n6 : G + i ≠ DV + v)
    (n7 : G + c.nmem (RV + i) ≠ DV + v) (n8 : G + i ≠ DV + c.nmem (VL + c.nmem (RV + i)))
    (n9 : G + c.nmem (RV + i) ≠ DV + c.nmem (VL + c.nmem (RV + i)))
    (w1 : RV + i ≤ W) (w2 : G + c.nmem (RV + i) ≤ W) (w4 : G + i ≤ W)
    (w3 : c.nmem (G + c.nmem (RV + i)) + min rem (c.nmem (G + i) - Z) ≤ W)
    (w5 : DV + v ≤ W) (w6 : VL + c.nmem (RV + i) ≤ W)
    (w7 : DV + c.nmem (VL + c.nmem (RV + i)) ≤ W)
    (w8 : (upd c.nmem (DV + v) (c.nmem (DV + v) - min rem (c.nmem (G + i) - Z)))
      (DV + c.nmem (VL + c.nmem (RV + i))) + min rem (c.nmem (G + i) - Z) ≤ W) :
    ∃ c' t, Exec P W pRed c c' t ∧ t ≤ 23 ∧ c'.nreg 9167 = rem - min rem (c.nmem (G + i) - Z) ∧
      c'.nmem = upd (upd (upd (upd c.nmem (G + i) (c.nmem (G + i) - min rem (c.nmem (G + i) - Z)))
        (G + c.nmem (RV + i)) (c.nmem (G + c.nmem (RV + i)) + min rem (c.nmem (G + i) - Z)))
        (DV + v) (c.nmem (DV + v) - min rem (c.nmem (G + i) - Z)))
        (DV + c.nmem (VL + c.nmem (RV + i)))
        ((upd c.nmem (DV + v) (c.nmem (DV + v) - min rem (c.nmem (G + i) - Z)))
          (DV + c.nmem (VL + c.nmem (RV + i))) + min rem (c.nmem (G + i) - Z)) ∧
      (∀ x, x ≠ 9167 → x ≠ 9170 → (x < 9176 ∨ 9179 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set a := min rem (c.nmem (G + i) - Z) with ha
  obtain ⟨c₁, t₁, e₁, ht₁, g77, f₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ t₁, Exec P W pR2 c c₁ t₁ ∧ t₁ = 1 ∧
      c₁.nreg 9177 = c.nmem (G + i) - Z ∧ (∀ x, x ≠ 9177 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold pR2
    exec_block
    all_goals try (config_simp; simp only [r4, r76]; omega)
    refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r4, r76]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  -- `a := min rem x`
  obtain ⟨c₂, t₂, e₂, ht₂, g78, f₂, m₂, rr₂, rm₂, o₂⟩ : ∃ c₂ t₂,
      Exec P W (.ifLtN 9167 9177 (block [.copyN 9178 9167]) (block [.copyN 9178 9177])) c₁ c₂ t₂ ∧
      t₂ ≤ 3 ∧ c₂.nreg 9178 = a ∧ (∀ x, x ≠ 9178 → c₂.nreg x = c₁.nreg x) ∧
      c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have h67 : c₁.nreg 9167 = rem := by rw [f₁ _ (by omega), r67]
    by_cases hlt : c₁.nreg 9167 < c₁.nreg 9177
    · have hc₁ := e₁.wb_right
      obtain ⟨c₂, t₂, e₂, ht₂, g78, f₂, m₂, rr₂, rm₂, o₂⟩ : ∃ c₂ t₂,
          Exec P W (block [.copyN 9178 9167]) c₁ c₂ t₂ ∧ t₂ = 1 ∧ c₂.nreg 9178 = c₁.nreg 9167 ∧
          (∀ x, x ≠ 9178 → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧
          c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
        clear hc
        exec_block
        all_goals try omega
        refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      refine ⟨c₂, t₂ + 1, .ifLtN_true hlt e₂, by omega, ?_, f₂, m₂, rr₂, rm₂, o₂⟩
      rw [g78, h67, ha]; rw [h67, g77] at hlt; exact (min_eq_left hlt.le).symm
    · have hc₁ := e₁.wb_right
      obtain ⟨c₂, t₂, e₂, ht₂, g78, f₂, m₂, rr₂, rm₂, o₂⟩ : ∃ c₂ t₂,
          Exec P W (block [.copyN 9178 9177]) c₁ c₂ t₂ ∧ t₂ = 1 ∧ c₂.nreg 9178 = c₁.nreg 9177 ∧
          (∀ x, x ≠ 9178 → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧
          c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
        clear hc
        exec_block
        all_goals try omega
        refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      refine ⟨c₂, t₂ + 2, .ifLtN_false hlt e₂, by omega, ?_, f₂, m₂, rr₂, rm₂, o₂⟩
      rw [g78, g77, ha]; rw [h67, g77] at hlt; exact (min_eq_right (not_lt.1 hlt)).symm
  have k2 : ∀ x, x ≠ 9177 → x ≠ 9178 → c₂.nreg x = c.nreg x := fun x h1 h2 => by
    rw [f₂ x h2, f₁ x h1]
  obtain ⟨c₃, t₃, e₃, ht₃, g67, g70, m₃, f₃, rr₃, rm₃, o₃⟩ := pU1_exec (P := P) c₂ e₂.wb_right
    (G := G) (RV := RV) (gi := c.nmem (G + i)) (a := a) (rem := rem) (i := i)
    (by rw [k2 _ (by omega) (by omega), r1]) (by rw [k2 _ (by omega) (by omega), r2])
    (by rw [k2 _ (by omega) (by omega), r67]) (by rw [k2 _ (by omega) (by omega), r74])
    (by rw [k2 _ (by omega) (by omega), r75]) (by rw [k2 _ (by omega) (by omega), r76]) g78
    (by rw [m₂, m₁]; exact n1) n2 w1 (by rw [m₂, m₁]; exact w2) (by rw [m₂, m₁]; exact w3) w4
  rw [m₂, m₁] at g70 m₃
  have k3 : ∀ x, x ≠ 9167 → x ≠ 9170 → x ≠ 9176 → x ≠ 9177 → x ≠ 9178 → x ≠ 9179 →
      c₃.nreg x = c.nreg x := fun x h1 h2 h3 h4 h5 h6 => by rw [f₃ x h1 h2 h3 h4 h6, k2 x h4 h5]
  have eVL : c₃.nmem (VL + c.nmem (RV + i)) = c.nmem (VL + c.nmem (RV + i)) := by
    rw [m₃, upd_other _ _ _ (Ne.symm n5), upd_other _ _ _ (Ne.symm n4)]
  have eDV : c₃.nmem (DV + v) = c.nmem (DV + v) := by
    rw [m₃, upd_other _ _ _ (Ne.symm n7), upd_other _ _ _ (Ne.symm n6)]
  have e : (upd c₃.nmem (DV + v) (c.nmem (DV + v) - a)) (DV + c.nmem (VL + c.nmem (RV + i))) =
      (upd c.nmem (DV + v) (c.nmem (DV + v) - a)) (DV + c.nmem (VL + c.nmem (RV + i))) := by
    by_cases e : DV + c.nmem (VL + c.nmem (RV + i)) = DV + v
    · rw [e, upd_same, upd_same]
    · rw [upd_other _ _ _ e, upd_other _ _ _ e, m₃, upd_other _ _ _ (Ne.symm n9),
        upd_other _ _ _ (Ne.symm n8)]
  obtain ⟨c₄, t₄, e₄, ht₄, m₄, f₄, rr₄, rm₄, o₄⟩ := pU2_exec (P := P) c₃ e₃.wb_right
    (VL := VL) (DV := DV) (v := v) (a := a) (r := c.nmem (RV + i))
    (by rw [k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r3])
    (by rw [k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r5])
    (by rw [k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r66])
    g70 (by rw [f₃ _ (by omega) (by omega) (by omega) (by omega) (by omega), g78]) n3 w5 w6
    (by rw [eVL]; exact w7) (by rw [eVL, eDV, e]; exact w8)
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega,
    by rw [f₄ _ (by omega) (by omega), g67], by rw [m₄, eVL, eDV, e, m₃],
    fun x h1 h2 h3 => by rw [f₄ x (by omega) (by omega),
      k3 x h1 h2 (by omega) (by omega) (by omega) (by omega)],
    by rw [rr₄, rr₃, rr₂, rr₁], by rw [rm₄, rm₃, rm₂, rm₁], by rw [o₄, o₃, o₂, o₁]⟩

/-- **One dart of the visited vertex.** -/
theorem pR_exec (c : Config) (hc : WordsBounded W c) {G RV VL Z DV OL v rem k : ℕ}
    (r1 : c.nreg 9151 = G) (r2 : c.nreg 9152 = RV) (r3 : c.nreg 9153 = VL)
    (r4 : c.nreg 9154 = Z) (r5 : c.nreg 9155 = DV) (r62 : c.nreg 9162 = OL)
    (r63 : c.nreg 9163 = 1) (r64 : c.nreg 9164 = 0) (r66 : c.nreg 9166 = v)
    (r67 : c.nreg 9167 = rem) (r68 : c.nreg 9168 = k) (wk : OL + k ≤ W) (wk1 : k + 1 ≤ W)
    (n1 : G + c.nmem (OL + k) ≠ G + c.nmem (RV + c.nmem (OL + k)))
    (n2 : G + c.nmem (OL + k) ≠ RV + c.nmem (OL + k))
    (n3 : DV + v ≠ VL + c.nmem (RV + c.nmem (OL + k)))
    (n4 : G + c.nmem (OL + k) ≠ VL + c.nmem (RV + c.nmem (OL + k)))
    (n5 : G + c.nmem (RV + c.nmem (OL + k)) ≠ VL + c.nmem (RV + c.nmem (OL + k)))
    (n6 : G + c.nmem (OL + k) ≠ DV + v) (n7 : G + c.nmem (RV + c.nmem (OL + k)) ≠ DV + v)
    (n8 : G + c.nmem (OL + k) ≠ DV + c.nmem (VL + c.nmem (RV + c.nmem (OL + k))))
    (n9 : G + c.nmem (RV + c.nmem (OL + k)) ≠ DV + c.nmem (VL + c.nmem (RV + c.nmem (OL + k))))
    (w1 : RV + c.nmem (OL + k) ≤ W) (w2 : G + c.nmem (RV + c.nmem (OL + k)) ≤ W)
    (w4 : G + c.nmem (OL + k) ≤ W)
    (w3 : c.nmem (G + c.nmem (RV + c.nmem (OL + k))) +
      min rem (c.nmem (G + c.nmem (OL + k)) - Z) ≤ W)
    (w5 : DV + v ≤ W) (w6 : VL + c.nmem (RV + c.nmem (OL + k)) ≤ W)
    (w7 : DV + c.nmem (VL + c.nmem (RV + c.nmem (OL + k))) ≤ W)
    (w8 : (upd c.nmem (DV + v) (c.nmem (DV + v) - min rem (c.nmem (G + c.nmem (OL + k)) - Z)))
      (DV + c.nmem (VL + c.nmem (RV + c.nmem (OL + k)))) +
        min rem (c.nmem (G + c.nmem (OL + k)) - Z) ≤ W) :
    ∃ c' t, Exec P W pR c c' t ∧ t ≤ 32 ∧ c'.nreg 9168 = k + 1 ∧
      (if Z < c.nmem (G + c.nmem (OL + k)) ∧ 0 < rem then
        c'.nreg 9167 = rem - min rem (c.nmem (G + c.nmem (OL + k)) - Z) ∧
        c'.nmem = upd (upd (upd (upd c.nmem (G + c.nmem (OL + k))
          (c.nmem (G + c.nmem (OL + k)) - min rem (c.nmem (G + c.nmem (OL + k)) - Z)))
          (G + c.nmem (RV + c.nmem (OL + k)))
          (c.nmem (G + c.nmem (RV + c.nmem (OL + k))) +
            min rem (c.nmem (G + c.nmem (OL + k)) - Z)))
          (DV + v) (c.nmem (DV + v) - min rem (c.nmem (G + c.nmem (OL + k)) - Z)))
          (DV + c.nmem (VL + c.nmem (RV + c.nmem (OL + k))))
          ((upd c.nmem (DV + v) (c.nmem (DV + v) - min rem (c.nmem (G + c.nmem (OL + k)) - Z)))
            (DV + c.nmem (VL + c.nmem (RV + c.nmem (OL + k)))) +
              min rem (c.nmem (G + c.nmem (OL + k)) - Z))
      else c'.nreg 9167 = rem ∧ c'.nmem = c.nmem) ∧
      (∀ x, x ≠ 9167 → x ≠ 9168 → x ≠ 9170 → (x < 9174 ∨ 9179 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g74, g75, g76, g68, f₁, m₁, rr₁, rm₁, o₁⟩ := pR1_exec (P := P) c hc
    r1 r62 r63 r68 wk w4 wk1
  have k1 : ∀ x, x ≠ 9168 → x ≠ 9170 → (x < 9174 ∨ 9176 < x) → c₁.nreg x = c.nreg x := f₁
  by_cases h1 : Z < c.nmem (G + c.nmem (OL + k))
  · have hlt1 : c₁.nreg 9154 < c₁.nreg 9176 := by
      rw [k1 _ (by omega) (by omega) (by omega), r4, g76]; exact h1
    by_cases h2 : 0 < rem
    · have hlt2 : c₁.nreg 9164 < c₁.nreg 9167 := by
        rw [k1 _ (by omega) (by omega) (by omega), k1 _ (by omega) (by omega) (by omega), r64, r67]
        exact h2
      obtain ⟨c₂, t₂, e₂, ht₂, g67, m₂, f₂, rr₂, rm₂, o₂⟩ := pRed_exec (P := P) c₁ e₁.wb_right
        (G := G) (RV := RV) (VL := VL) (Z := Z) (DV := DV) (v := v) (rem := rem)
        (i := c.nmem (OL + k))
        (by rw [k1 _ (by omega) (by omega) (by omega), r1])
        (by rw [k1 _ (by omega) (by omega) (by omega), r2])
        (by rw [k1 _ (by omega) (by omega) (by omega), r3])
        (by rw [k1 _ (by omega) (by omega) (by omega), r4])
        (by rw [k1 _ (by omega) (by omega) (by omega), r5])
        (by rw [k1 _ (by omega) (by omega) (by omega), r66])
        (by rw [k1 _ (by omega) (by omega) (by omega), r67]) g74 g75 (by rw [g76, m₁])
        (by rw [m₁]; exact n1) n2 (by rw [m₁]; exact n3) (by rw [m₁]; exact n4)
        (by rw [m₁]; exact n5) n6 (by rw [m₁]; exact n7) (by rw [m₁]; exact n8)
        (by rw [m₁]; exact n9) w1 (by rw [m₁]; exact w2) w4 (by rw [m₁]; exact w3) w5
        (by rw [m₁]; exact w6) (by rw [m₁]; exact w7) (by rw [m₁]; exact w8)
      refine ⟨c₂, t₁ + (t₂ + 1 + 1), .seq e₁ (.ifLtN_true hlt1 (.ifLtN_true hlt2 e₂)), by omega,
        by rw [f₂ _ (by omega) (by omega) (by omega), g68], ?_,
        fun x h1 h2 h3 h4 => by rw [f₂ x h1 h3 (by omega), k1 x h2 h3 (by omega)],
        by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
      rw [if_pos ⟨h1, h2⟩, m₁] at *
      exact ⟨g67, m₂⟩
    · have hlt2 : ¬ c₁.nreg 9164 < c₁.nreg 9167 := by
        rw [k1 _ (by omega) (by omega) (by omega), k1 _ (by omega) (by omega) (by omega), r64, r67]
        exact h2
      refine ⟨c₁, t₁ + (0 + 2 + 1), .seq e₁ (.ifLtN_true hlt1 (.ifLtN_false hlt2
        (.skip e₁.wb_right))), by omega, g68, ?_, fun x h1 h2 h3 h4 => k1 x h2 h3 (by omega),
        rr₁, rm₁, o₁⟩
      rw [if_neg (by tauto)]
      exact ⟨by rw [k1 _ (by omega) (by omega) (by omega), r67], m₁⟩
  · have hlt1 : ¬ c₁.nreg 9154 < c₁.nreg 9176 := by
      rw [k1 _ (by omega) (by omega) (by omega), r4, g76]; exact h1
    refine ⟨c₁, t₁ + (0 + 2), .seq e₁ (.ifLtN_false hlt1 (.skip e₁.wb_right)), by omega, g68, ?_,
      fun x h1 h2 h3 h4 => k1 x h2 h3 (by omega), rr₁, rm₁, o₁⟩
    rw [if_neg (by tauto)]
    exact ⟨by rw [k1 _ (by omega) (by omega) (by omega), r67], m₁⟩

theorem pO1_exec (c : Config) (hc : WordsBounded W c) {Q FR BT DV t : ℕ}
    (r58 : c.nreg 9158 = Q) (r57 : c.nreg 9157 = FR) (r56 : c.nreg 9156 = BT)
    (r55 : c.nreg 9155 = DV) (r63 : c.nreg 9163 = 1) (r65 : c.nreg 9165 = t)
    (w1 : Q + t ≤ W) (w2 : FR + c.nmem (Q + t) ≤ W) (w3 : BT + c.nmem (Q + t) ≤ W)
    (w4 : DV + c.nmem (Q + t) ≤ W) (w5 : t + 1 ≤ W) :
    ∃ c' k, Exec P W pO1 c c' k ∧ k = 9 ∧ c'.nreg 9166 = c.nmem (Q + t) ∧
      c'.nreg 9165 = t + 1 ∧ c'.nreg 9171 = c.nmem (FR + c.nmem (Q + t)) ∧
      c'.nreg 9172 = c.nmem (BT + c.nmem (Q + t)) ∧ c'.nreg 9173 = c.nmem (DV + c.nmem (Q + t)) ∧
      (∀ x, x ≠ 9165 → x ≠ 9166 → (x < 9170 ∨ 9173 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pO1
  exec_block
  all_goals try (config_simp; simp only [r58, r57, r56, r55, r63, r65]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r58, r57, r56, r55, r63, r65]
  simp only [upd_apply]; split_ifs <;> omega

theorem pI1_exec (c : Config) (hc : WordsBounded W c) {OB OE v : ℕ}
    (r60 : c.nreg 9160 = OB) (r61 : c.nreg 9161 = OE) (r66 : c.nreg 9166 = v)
    (w1 : OB + v ≤ W) (w2 : OE + v ≤ W) :
    ∃ c' k, Exec P W pI1 c c' k ∧ k = 5 ∧ c'.nreg 9167 = c.nreg 9173 - c.nreg 9172 ∧
      c'.nreg 9168 = c.nmem (OB + v) ∧ c'.nreg 9169 = c.nmem (OE + v) ∧
      (∀ x, (x < 9167 ∨ 9170 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pI1
  exec_block
  all_goals try (config_simp; simp only [r60, r61, r66]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r60, r61, r66]
  simp only [upd_apply]; split_ifs <;> omega

theorem pA_exec (c : Config) (hc : WordsBounded W c) (w : 1 ≤ W) :
    ∃ c' k, Exec P W pA c c' k ∧ k = 3 ∧ c'.nreg 9163 = 1 ∧ c'.nreg 9164 = 0 ∧
      c'.nreg 9165 = 0 ∧ (∀ x, (x < 9163 ∨ 9165 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pA
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

end Blocks

end BKMNW

end PlanarFlow
