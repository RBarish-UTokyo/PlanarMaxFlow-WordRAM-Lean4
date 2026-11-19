module

public import PlanarFlow.BKMNW.NcFzF

/-!
# The pendant frame writer `pfP`: the whole run

**`pfP_exec`**: from `PfIn` (the frame of the call at `d`, the arrays `F1`, `DF`, `CP` below the
scratch base `S`, the word room), `pfP` runs within **`pfT m = 245 m + 300`** steps and leaves
**`PfRes`**: the facts of stage 2 (`St2`: the saved values, the vertex labels, the frozen
outflows `DV − Z·DG`, the vertex numbering `CI`/`IX`, the header of the pendant frame at
`d' = S + 12 + 16 m`, the registers), and the arrays of the pendant frame (`m' = m + 2n`):
`RV'`, `SG'`, `CP'`, `FL'` on the three blocks `[0, m)`, `[m, m + n)`, `[m + n, m + 2n)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcFz

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv

variable {P : Input} {W : ℕ}

/-- The steps of `pfP`. -/
def pfT (m : ℕ) : ℕ := 245 * m + 300

/-- **The result of `pfP`** (see the module docstring). -/
structure PfRes (c c' : Config) (d m Z S F1b DFb CPb n : ℕ) : Prop where
  st : St2 c c' d m Z S F1b DFb CPb n
  nm : n ≤ m
  dvr : ∀ t < n, c'.nmem (S + 12 + 14 * m + t) =
    c'.nmem (S + 12 + 8 * m + c'.nmem (S + 12 + 12 * m + t))
  zg : ∀ t < n, c'.nmem (S + 12 + 15 * m + t) =
    c'.nmem (S + 12 + 9 * m + c'.nmem (S + 12 + 12 * m + t)) * Z
  rv0 : ∀ t < m, c'.nmem (S + 12 + 16 * m + 4 + (m + 2 * n) + t) = c.nmem (d + 4 + m + t)
  rv1 : ∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + (m + 2 * n) + m + t) = t + (m + n)
  rv2 : ∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + (m + 2 * n) + (m + n) + t) = t + m
  sg0 : ∀ t < m, c'.nmem (S + 12 + 16 * m + 4 + 2 * (m + 2 * n) + t) =
    sgV (c'.nmem (S + 12 + 7 * m + t)) (c.nmem (d + 4 + m + m + t)) m
      (c'.nmem (S + 12 + 11 * m + (c'.nmem (S + 12 + 7 * m + t) - 1)))
  sg1 : ∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + 2 * (m + 2 * n) + m + t) =
    c'.nmem (S + 12 + 12 * m + t)
  sg2 : ∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + 2 * (m + 2 * n) + (m + n) + t) = t + (m + n)
  cp0 : ∀ t < m, c'.nmem (S + 12 + 16 * m + 4 + 3 * (m + 2 * n) + t) =
    c.nmem (CPb + t) - c.nmem (CPb + t) * c'.nmem (S + 12 + 13 * m + t)
  cp1 : ∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + 3 * (m + 2 * n) + m + t) =
    c'.nmem (S + 12 + 14 * m + t) + 0 - c'.nmem (S + 12 + 15 * m + t)
  cp2 : ∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + 3 * (m + 2 * n) + (m + n) + t) =
    c'.nmem (S + 12 + 15 * m + t) + 0 - c'.nmem (S + 12 + 14 * m + t)
  fl0 : ∀ t < m, c'.nmem (S + 12 + 16 * m + 4 + 6 * (m + 2 * n) + t) =
    c.nmem (F1b + t) + m * Z - c'.nmem (S + 12 + 6 * m + t)
  fl1 : ∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + 6 * (m + 2 * n) + m + t) =
    c'.nmem (S + 12 + 14 * m + t) + m * Z - c'.nmem (S + 12 + 15 * m + t)
  fl2 : ∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + 6 * (m + 2 * n) + (m + n) + t) =
    c'.nmem (S + 12 + 15 * m + t) + m * Z - c'.nmem (S + 12 + 14 * m + t)

section Facts

variable {c c₂ : Config} {d m Z S F1b DFb CPb n : ℕ}

/-- `St2` passes to a later configuration which agrees below `S + 12 + 14 m` and on the header
of the pendant frame. -/
lemma St2.mono {c' : Config} (h : St2 c c₂ d m Z S F1b DFb CPb n)
    (hm : ∀ a, (a < S + 12 + 14 * m ∨ (S + 12 + 16 * m ≤ a ∧ a < S + 12 + 16 * m + 4)) →
      c'.nmem a = c₂.nmem a)
    (hr : ∀ r, ¬ LpScr r → c'.nreg r = c₂.nreg r) (hrr : c'.rreg = c₂.rreg)
    (hrm : c'.rmem = c₂.rmem) (ho : c'.output = c₂.output) : St2 c c' d m Z S F1b DFb CPb n where
  rg := h.rg.keepLp hr
  rg2 := h.rg2.keepLp hr
  r04 := by rw [hr _ (by unfold LpScr; omega)]; exact h.r04
  reg r h' := by
    unfold ExtScr at h'
    rw [hr _ (by unfold LpScr; omega)]; exact h.reg r (by unfold ExtScr; omega)
  low a ha := by rw [hm a (Or.inl (by omega))]; exact h.low a ha
  sv0 := by rw [hm _ (Or.inl (by omega))]; exact h.sv0
  sv1 := by rw [hm _ (Or.inl (by omega))]; exact h.sv1
  sv2 := by rw [hm _ (Or.inl (by omega))]; exact h.sv2
  sv3 := by rw [hm _ (Or.inl (by omega))]; exact h.sv3
  sv4 := by rw [hm _ (Or.inl (by omega))]; exact h.sv4
  sv5 := by rw [hm _ (Or.inl (by omega))]; exact h.sv5
  sv6 := by rw [hm _ (Or.inl (by omega))]; exact h.sv6
  hd0 := by rw [hm _ (Or.inr (by omega))]; exact h.hd0
  hd3 := by rw [hm _ (Or.inr (by omega))]; exact h.hd3
  q t ht := by rw [hm _ (Or.inl (by omega))]; exact h.q t ht
  x0 t ht := by rw [hm _ (Or.inl (by omega))]; exact h.x0 t ht
  lab i hi := by rw [hm _ (Or.inl (by omega))]; exact h.lab i hi
  dv v hv := by rw [hm _ (Or.inl (by omega))]; exact h.dv v hv
  dg v hv := by rw [hm _ (Or.inl (by omega))]; exact h.dg v hv
  nv := h.nv
  ci i hi hr' := by
    obtain ⟨u1, u2⟩ := h.ci i hi hr'
    have := cnt_le (rfF (sgF d m c.nmem)) i
    exact ⟨by rw [hm _ (Or.inl (by omega))]; exact u1, by rw [hm _ (Or.inl (by omega))]; exact u2⟩
  rr := by rw [hrr]; exact h.rr
  rm := by rw [hrm]; exact h.rm
  out := by rw [ho]; exact h.out

/-- **The vertex numbering**: every `t < n` is the number `cnt rf i` of a representative `i < m`,
and `IX[t] = i`. -/
lemma St2.ix (h : St2 c c₂ d m Z S F1b DFb CPb n) {t : ℕ} (ht : t < n) :
    ∃ i < m, 0 < rfF (sgF d m c.nmem) i ∧ cnt (rfF (sgF d m c.nmem)) i = t ∧
      c₂.nmem (S + 12 + 12 * m + t) = i := by
  rw [h.nv] at ht
  obtain ⟨i, hi, h1, h2⟩ := cnt_surj _ m t ht
  refine ⟨i, hi, h1, h2, ?_⟩
  have := (h.ci i hi h1).2
  rw [h2] at this; exact this

lemma St2.ix_lt (h : St2 c c₂ d m Z S F1b DFb CPb n) {t : ℕ} (ht : t < n) :
    c₂.nmem (S + 12 + 12 * m + t) < m := by
  obtain ⟨i, hi, -, -, e⟩ := h.ix ht
  rw [e]; exact hi

/-- The representative of the vertex of `i` is flagged. -/
lemma rfF_olab {sg : ℕ → ℕ} {m : ℕ} (hp : PermOn sg m) {i : ℕ} (hi : i < m) :
    rfF sg (olab sg i) = 1 := by
  unfold rfF; rw [olab_olab hp hi]; omega

lemma St2.lab_bd (h : St2 c c₂ d m Z S F1b DFb CPb n) (hp : PermOn (sgF d m c.nmem) m)
    {t : ℕ} (ht : t < m) :
    1 ≤ c₂.nmem (S + 12 + 7 * m + t) ∧ c₂.nmem (S + 12 + 7 * m + t) ≤ m := by
  rw [h.lab t ht]; have := olab_lt hp ht; omega

lemma St2.ci_lab (h : St2 c c₂ d m Z S F1b DFb CPb n) (hp : PermOn (sgF d m c.nmem) m)
    {t : ℕ} (ht : t < m) :
    c₂.nmem (S + 12 + 11 * m + (c₂.nmem (S + 12 + 7 * m + t) - 1)) =
      cnt (rfF (sgF d m c.nmem)) (olab (sgF d m c.nmem) t) := by
  rw [h.lab t ht, Nat.add_sub_cancel]
  exact (h.ci _ (olab_lt hp ht) (by rw [rfF_olab hp ht]; omega)).1

lemma St2.dg_bd (h : St2 c c₂ d m Z S F1b DFb CPb n) {v : ℕ} (hv : v < m) :
    c₂.nmem (S + 12 + 9 * m + v) ≤ m := by
  rw [h.dg v hv]; exact dvC_le _ _ _

lemma St2.dv_bd (h : St2 c c₂ d m Z S F1b DFb CPb n) (hf1 : ∀ i < m, c.nmem (F1b + i) ≤ 2 * Z)
    {v : ℕ} (hv : v < m) : c₂.nmem (S + 12 + 8 * m + v) ≤ 2 * (m * Z) := by
  rw [h.dv v hv]
  refine (dvS_le _ _ _ _).trans ?_
  have : ∑ j ∈ range m, x0F c.nmem F1b DFb (d + 4 + m) Z j ≤ ∑ j ∈ range m, 2 * Z :=
    sum_le_sum fun j hj => x0F_le (hf1 j (mem_range.1 hj))
  simp only [sum_const, card_range, smul_eq_mul] at this
  have e : m * (2 * Z) = 2 * (m * Z) := by ring
  omega

end Facts

lemma pf_le_aux {m n k₁ k₂ a b c' d' e : ℕ} (hnm : n ≤ m) (h1 : k₁ ≤ 36 * m + 79)
    (h2 : k₂ ≤ 67 * m + 80) (ha : a ≤ 20 * n + 20) (hb : b ≤ 9 * m + 12 * n + 30)
    (hc : c' ≤ 20 * m + 15 * n + 30) (hd : d' ≤ 11 * m + 22 * n + 30)
    (he : e ≤ 11 * m + 22 * n + 30) : k₁ + (k₂ + (a + (b + c') + (d' + e))) ≤ pfT m := by
  unfold pfT; omega

set_option maxHeartbeats 1600000 in
/-- **The pendant frame writer.** -/
theorem pfP_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) {d m Z S F1b DFb CPb : ℕ}
    (hI : PfIn c W d m Z S F1b DFb CPb) :
    ∃ c' k n, Exec P W pfP c c' k ∧ k ≤ pfT m ∧ PfRes c c' d m Z S F1b DFb CPb n := by
  obtain ⟨c₁, k₁, e₁, hk₁, S1⟩ := pfS1_exec (P := P) c hc hW hI
  obtain ⟨c₂, k₂, n, e₂, hk₂, hnm, S2⟩ := pfS2_exec (P := P) c c₁ hW hI S1 e₁.wb_right
  clear S1
  have hp := hI.sgp
  have lfr := hI.lfr; have lF := hI.lF; have lC := hI.lC; have wS := hI.wS; have wZ := hI.wZ
  -- 3a
  obtain ⟨c₃, k₃, e₃, hk₃, v3, z3, B3⟩ := pf3a_exec (P := P) c₂ e₂.wb_right hW S2.rg S2.rg2 hnm
    wS wZ (fun t ht => S2.ix_lt ht) (fun t ht => S2.dg_bd (S2.ix_lt ht))
  have S3 : St2 c c₃ d m Z S F1b DFb CPb n := S2.mono (fun a ha => B3.mem a (by omega)) B3.reg
    B3.rr B3.rm B3.out
  -- 3b
  obtain ⟨c₄, k₄, e₄, hk₄, rv0, rv1, rv2, B4⟩ := pf3b_exec (P := P) c₃ e₃.wb_right hW S3.rg S3.rg2
    hnm lfr wS
  have S4 : St2 c c₄ d m Z S F1b DFb CPb n := S3.mono (fun a ha => B4.mem a (by omega)) B4.reg
    B4.rr B4.rm B4.out
  -- 3c
  obtain ⟨c₅, k₅, e₅, hk₅, sg0, sg1, sg2, B5⟩ := pf3c_exec (P := P) c₄ e₄.wb_right hW S4.rg
    S4.rg2 hnm lfr wS (fun t ht => S4.lab_bd hp ht)
    (fun t ht => by rw [S4.low _ (by omega)]; exact hI.sg t ht)
    (fun t ht => by rw [S4.ci_lab hp ht]; exact (cnt_le _ _).trans (olab_lt hp ht).le)
    (fun t ht => S4.ix_lt ht)
  have S5 : St2 c c₅ d m Z S F1b DFb CPb n := S4.mono (fun a ha => B5.mem a (by omega)) B5.reg
    B5.rr B5.rm B5.out
  -- 4a
  obtain ⟨c₆, k₆, e₆, hk₆, cp0, cp1, cp2, B6⟩ := pf4a_exec (P := P) c₅ e₅.wb_right hW S5.rg
    S5.rg2 hnm lC wS (fun t ht => by rw [S5.q t ht]; exact qF_le_one _ _ _ _)
  have S6 : St2 c c₆ d m Z S F1b DFb CPb n := S5.mono (fun a ha => B6.mem a (by omega)) B6.reg
    B6.rr B6.rm B6.out
  -- the per-vertex arrays survive 3b … 4a
  have K36 : ∀ a, S + 12 + 14 * m ≤ a → a < S + 12 + 16 * m → c₆.nmem a = c₃.nmem a :=
    fun a h1 h2 => by rw [B6.mem a (by omega), B5.mem a (by omega), B4.mem a (by omega)]
  -- 4b
  obtain ⟨c₇, k₇, e₇, hk₇, fl0, fl1, fl2, B7⟩ := pf4b_exec (P := P) c₆ e₆.wb_right hW S6.rg
    S6.rg2 hnm lF wS wZ (fun t ht => by rw [S6.low _ (by omega)]; exact hI.f1 t ht)
    (fun t ht => by
      rw [K36 _ (by omega) (by omega), v3 t ht, Nat.mul_one]
      have hl := S2.ix_lt ht
      have := S2.dv_bd hI.f1 hl
      exact this)
    (fun t ht => by
      rw [K36 _ (by omega) (by omega), z3 t ht]
      exact Nat.mul_le_mul_right Z (S2.dg_bd (S2.ix_lt ht)))
  have S7 : St2 c c₇ d m Z S F1b DFb CPb n := S6.mono (fun a ha => B7.mem a (by omega)) B7.reg
    B7.rr B7.rm B7.out
  have K37 : ∀ a, S + 12 + 14 * m ≤ a → a < S + 12 + 16 * m → c₇.nmem a = c₃.nmem a :=
    fun a h1 h2 => by rw [B7.mem a (by omega), K36 a h1 h2]
  have K27 : ∀ a, a < S + 12 + 14 * m → c₇.nmem a = c₂.nmem a := fun a ha => by
    rw [B7.mem a (by omega), B6.mem a (by omega), B5.mem a (by omega), B4.mem a (by omega),
      B3.mem a (by omega)]
  have K47 : ∀ a, a < S + 12 + 14 * m → c₄.nmem a = c₂.nmem a := fun a ha => by
    rw [B4.mem a (by omega), B3.mem a (by omega)]
  have K57 : ∀ a, a < S + 12 + 16 * m → c₅.nmem a = c₄.nmem a := fun a ha => B5.mem a (by omega)
  have K67 : ∀ a, a < S + 12 + 16 * m → c₆.nmem a = c₅.nmem a := fun a ha => B6.mem a (by omega)
  refine ⟨c₇, k₁ + (k₂ + (k₃ + (k₄ + k₅) + (k₆ + k₇))), n,
    e₁.seq (e₂.seq ((e₃.seq (e₄.seq e₅)).seq (e₆.seq e₇))),
    pf_le_aux hnm hk₁ hk₂ hk₃ hk₄ hk₅ hk₆ hk₇,
    ⟨S7, hnm, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
    fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
    fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩⟩
  · have hl := S2.ix_lt ht
    rw [K37 _ (by omega) (by omega), v3 t ht, Nat.mul_one, K27 (S + 12 + 12 * m + t) (by omega),
      K27 (S + 12 + 8 * m + c₂.nmem (S + 12 + 12 * m + t)) (by omega)]
  · have hl := S2.ix_lt ht
    rw [K37 _ (by omega) (by omega), z3 t ht, K27 (S + 12 + 12 * m + t) (by omega),
      K27 (S + 12 + 9 * m + c₂.nmem (S + 12 + 12 * m + t)) (by omega)]
  · rw [B7.mem _ (by omega), B6.mem _ (by omega), B5.mem _ (by omega), rv0 t ht,
      S3.low _ (by omega)]
  · rw [B7.mem _ (by omega), B6.mem _ (by omega), B5.mem _ (by omega), rv1 t ht]
  · rw [B7.mem _ (by omega), B6.mem _ (by omega), B5.mem _ (by omega), rv2 t ht]
  · have hl := S2.lab_bd hp ht
    rw [B7.mem _ (by omega), B6.mem _ (by omega), sg0 t ht, S4.low (d + 4 + m + m + t) (by omega),
      K27 (S + 12 + 7 * m + t) (by omega), K47 (S + 12 + 7 * m + t) (by omega),
      K27 (S + 12 + 11 * m + (c₂.nmem (S + 12 + 7 * m + t) - 1)) (by omega),
      K47 (S + 12 + 11 * m + (c₂.nmem (S + 12 + 7 * m + t) - 1)) (by omega)]
  · rw [B7.mem _ (by omega), B6.mem _ (by omega), sg1 t ht, K27 (S + 12 + 12 * m + t) (by omega),
      K47 (S + 12 + 12 * m + t) (by omega)]
  · rw [B7.mem _ (by omega), B6.mem _ (by omega), sg2 t ht]
  · rw [B7.mem _ (by omega), cp0 t ht, S5.low (CPb + t) (by omega),
      K27 (S + 12 + 13 * m + t) (by omega), K57 (S + 12 + 13 * m + t) (by omega),
      K47 (S + 12 + 13 * m + t) (by omega)]
  · rw [B7.mem _ (by omega), cp1 t ht, B7.mem (S + 12 + 14 * m + t) (by omega),
      B7.mem (S + 12 + 15 * m + t) (by omega), B6.mem (S + 12 + 14 * m + t) (by omega),
      B6.mem (S + 12 + 15 * m + t) (by omega)]
  · rw [B7.mem _ (by omega), cp2 t ht, B7.mem (S + 12 + 14 * m + t) (by omega),
      B7.mem (S + 12 + 15 * m + t) (by omega), B6.mem (S + 12 + 14 * m + t) (by omega),
      B6.mem (S + 12 + 15 * m + t) (by omega)]
  · rw [fl0 t ht, S6.low (F1b + t) (by omega), B7.mem (S + 12 + 6 * m + t) (by omega)]
  · rw [fl1 t ht, B7.mem (S + 12 + 14 * m + t) (by omega), B7.mem (S + 12 + 15 * m + t) (by omega)]
  · rw [fl2 t ht, B7.mem (S + 12 + 14 * m + t) (by omega), B7.mem (S + 12 + 15 * m + t) (by omega)]

end NcFz

end BKMNW

end PlanarFlow
