module

public import PlanarSeparator.Machine.CompHeavy

/-!
# The separator of the components on the machine: the marks around the heavy component

After the program of a piece on the heavy component `C` (`PlanarSeparator.Piece.pieceCall`):

* `wPass`, **`wPass_exec`**: the weights of the vertices of `C` marked `1` and `2` (in `1128`,
  `1129`), along the list of `C`.
* `selPass`: the mark of the rest of `U` (`1126`): `1` if the first part is the lighter.
* `rPass`, **`rPass_exec`**: the mark `1126` on the vertices of `U` off the label `1121`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {U : Finset (Fin N)}
  {w : Fin N → ℕ} {W : ℕ} {P : Input}

/-- The body of the weight pass: the mark and the weight of `L[j]`. -/
def wBody : Stmt :=
  .seq (block [.addN 1118 1015 1110, .loadN 1114 1118, .addN 1118 1019 1114, .loadN 1119 1118,
    .addN 1118 1014 1114, .loadN 1117 1118])
    (.seq (.ifLtN 1119 1130 (.ifLtN 0 1119 (.instr (.addN 1128 1128 1117)) .skip)
      (.ifLtN 1119 1131 (.instr (.addN 1129 1129 1117)) .skip)) (.instr (.addN 1110 1110 1001)))

/-- **The weights of the two parts of the heavy component.** -/
def wPass : Stmt :=
  .seq (block [.constN 1110 0, .constN 1128 0, .constN 1129 0, .constN 1131 3])
    (.whileLtN 1110 1016 wBody)

/-- The weight of the vertices of the list marked `b`. -/
noncomputable def wMk (C : Finset (Fin N)) (w : Fin N → ℕ) (mk : ℕ → ℕ) (b k : ℕ) : ℕ :=
  ∑ j ∈ range k, if mk (lv C j) = b then SepProg.wI w (lv C j) else 0

theorem wMk_le (C : Finset (Fin N)) (w : Fin N → ℕ) (mk : ℕ → ℕ) (b : ℕ) {k : ℕ} (hk : k ≤ #C) :
    wMk C w mk b k ≤ ∑ v ∈ C, w v := by
  unfold wMk
  calc _ ≤ ∑ j ∈ range k, SepProg.wI w (lv C j) := sum_le_sum fun j _ => by split_ifs <;> omega
    _ ≤ ∑ x ∈ UN C, SepProg.wI w x := sum_lv_le C _ hk
    _ = _ := sum_UN C w

theorem wPass_exec {d : Config} (hw : WordsBounded W d) {C : Finset (Fin N)} {aL aM aW : ℕ}
    (h01 : d.nreg 1001 = 1) (h00 : d.nreg 0 = 0) (h16 : d.nreg 1016 = #C) (h15 : d.nreg 1015 = aL)
    (h19 : d.nreg 1019 = aM) (h14 : d.nreg 1014 = aW) (h30 : d.nreg 1130 = 2)
    (hL : ∀ j < #C, d.nmem (aL + j) = lv C j) (hwt : ∀ v < N, d.nmem (aW + v) = SepProg.wI w v)
    (hWL : aL + N ≤ W) (hWM : aM + N ≤ W) (hWW : aW + N ≤ W) (hsw : 2 * ∑ v ∈ C, w v ≤ W)
    (hNW : N + 3 ≤ W) :
    ∃ d' k, Exec P W wPass d d' k ∧ WordsBounded W d' ∧
      d'.nreg 1128 = wMk C w (fun x => d.nmem (aM + x)) 1 #C ∧
      d'.nreg 1129 = wMk C w (fun x => d.nmem (aM + x)) 2 #C ∧
      (∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1117 → r ≠ 1118 → r ≠ 1119 → r ≠ 1128 → r ≠ 1129 →
        r ≠ 1131 → d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem ∧ k ≤ 13 * #C + 6 := by
  have hC := card_le_N C
  set mk := fun x => d.nmem (aM + x)
  obtain ⟨d₀, k₀, e₀, hw₀, a10, a28, a29, a31, q₀, m₀, hk₀⟩ : ∃ d₀ k₀, Exec P W
      (block [.constN 1110 0, .constN 1128 0, .constN 1129 0, .constN 1131 3]) d d₀ k₀ ∧
      WordsBounded W d₀ ∧ d₀.nreg 1110 = 0 ∧ d₀.nreg 1128 = 0 ∧ d₀.nreg 1129 = 0 ∧
      d₀.nreg 1131 = 3 ∧
      (∀ r, r ≠ 1110 → r ≠ 1128 → r ≠ 1129 → r ≠ 1131 → d₀.nreg r = d.nreg r) ∧
      d₀.nmem = d.nmem ∧ k₀ = 4 := by
    exec_block
    · omega
    · omega
    · omega
    · omega
    · exact ⟨‹WordsBounded _ _›, by simp, by simp, by simp, by simp,
        fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4], rfl, rfl⟩
  let I : ℕ → Config → Prop := fun j d' => WordsBounded W d' ∧ d'.nreg 1110 = j ∧
    d'.nreg 1016 = #C ∧ d'.nreg 1128 = wMk C w mk 1 j ∧ d'.nreg 1129 = wMk C w mk 2 j ∧
    d'.nreg 1131 = 3 ∧
    (∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1117 → r ≠ 1118 → r ≠ 1119 → r ≠ 1128 → r ≠ 1129 →
      r ≠ 1131 → d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem
  have hI₀ : I 0 d₀ := ⟨hw₀, a10, by rw [q₀ 1016 (by omega) (by omega) (by omega) (by omega), h16],
    by rw [a28]; simp [wMk], by rw [a29]; simp [wMk], a31,
    fun r a b c' e g h k l => q₀ r a h k l, m₀⟩
  obtain ⟨d₁, k₁, e₁, hI₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1110) (rN := 1016)
    (N := #C) (lo := 0) (B := 11) (body := wBody) I (fun j d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j d' h hj => by
      obtain ⟨hw', h10, h16', h28, h29, h31, hq, hm⟩ := h
      have g : ∀ r, 1110 > r → d'.nreg r = d.nreg r := fun r hr => hq r (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hx := lv_ltN C hj
      have mL : d'.nmem (aL + j) = lv C j := by rw [hm]; exact hL j hj
      have mW : d'.nmem (aW + lv C j) = SepProg.wI w (lv C j) := by rw [hm]; exact hwt _ hx
      have hA := wMk_le C w mk 1 (k := j) (by omega)
      have hB := wMk_le C w mk 2 (k := j) (by omega)
      have hwj : SepProg.wI w (lv C j) ≤ ∑ v ∈ C, w v := by
        rw [← sum_UN]
        exact single_le_sum (f := SepProg.wI w) (fun _ _ => Nat.zero_le _) (lv_mem_UN C hj)
      obtain ⟨d₂, k₂, e₂, hw₂, b19, b17, q₂, m₂, hk₂⟩ : ∃ d₂ k₂, Exec P W
          (block [.addN 1118 1015 1110, .loadN 1114 1118, .addN 1118 1019 1114, .loadN 1119 1118,
            .addN 1118 1014 1114, .loadN 1117 1118]) d' d₂ k₂ ∧ WordsBounded W d₂ ∧
          d₂.nreg 1119 = mk (lv C j) ∧ d₂.nreg 1117 = SepProg.wI w (lv C j) ∧
          (∀ r, r ≠ 1118 → r ≠ 1114 → r ≠ 1119 → r ≠ 1117 → d₂.nreg r = d'.nreg r) ∧
          d₂.nmem = d'.nmem ∧ k₂ = 6 := by
        exec_block
        · rw [g 1015 (by omega), h15, h10]; omega
        · config_simp; rw [g 1015 (by omega), h15, h10, mL, g 1019 (by omega), h19]; omega
        · config_simp; rw [g 1015 (by omega), h15, h10, mL, g 1014 (by omega), h14]; omega
        · refine ⟨‹WordsBounded _ _›, ?_, ?_, fun r h1 h2 h3 h4 => by
            simp [h1, h2, h3, h4], rfl, rfl⟩
          · simp only [upd_apply, Nat.reduceEqDiff, ↓reduceIte]
            rw [g 1015 (by omega), h15, h10, mL, g 1019 (by omega), h19, hm]
          · simp only [upd_apply, ↓reduceIte]
            rw [g 1015 (by omega), h15, h10, mL, g 1014 (by omega), h14, mW]
      have c00 : d₂.nreg 0 = 0 := by
        rw [q₂ 0 (by omega) (by omega) (by omega) (by omega), g 0 (by omega), h00]
      have c30 : d₂.nreg 1130 = 2 := by
        rw [q₂ 1130 (by omega) (by omega) (by omega) (by omega), hq 1130 (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h30]
      have c31 : d₂.nreg 1131 = 3 := by
        rw [q₂ 1131 (by omega) (by omega) (by omega) (by omega), h31]
      have c28 : d₂.nreg 1128 = wMk C w mk 1 j := by
        rw [q₂ 1128 (by omega) (by omega) (by omega) (by omega), h28]
      have c29 : d₂.nreg 1129 = wMk C w mk 2 j := by
        rw [q₂ 1129 (by omega) (by omega) (by omega) (by omega), h29]
      have hfin : ∀ d₃ : Config, WordsBounded W d₃ → d₃.nmem = d.nmem →
          d₃.nreg 1128 = wMk C w mk 1 (j + 1) → d₃.nreg 1129 = wMk C w mk 2 (j + 1) →
          (∀ r, r ≠ 1128 → r ≠ 1129 → d₃.nreg r = d₂.nreg r) →
          ∃ d₄, Exec P W (.instr (.addN 1110 1110 1001)) d₃ d₄ 1 ∧ I (j + 1) d₄ := by
        intro d₃ hw₃ hm₃ h28' h29' hq₃
        have g10 : d₃.nreg 1110 = j := by
          rw [hq₃ 1110 (by omega) (by omega), q₂ 1110 (by omega) (by omega) (by omega) (by omega),
            h10]
        have g01 : d₃.nreg 1001 = 1 := by
          rw [hq₃ 1001 (by omega) (by omega), q₂ 1001 (by omega) (by omega) (by omega) (by omega),
            g 1001 (by omega), h01]
        have e := Exec.addN (P := P) hw₃ 1110 1110 1001 (by rw [g10, g01]; omega)
        refine ⟨_, e, e.wb_right, by simp [g10, g01], ?_, ?_, ?_, ?_,
          fun r a b c' e' f' h k l => ?_, hm₃⟩
        · simp only [upd_apply, Nat.reduceEqDiff, ↓reduceIte]
          rw [hq₃ 1016 (by omega) (by omega), q₂ 1016 (by omega) (by omega) (by omega)
            (by omega)]; exact h16'
        · simp only [upd_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h28'
        · simp only [upd_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h29'
        · simp only [upd_apply, Nat.reduceEqDiff, ↓reduceIte]
          rw [hq₃ 1131 (by omega) (by omega)]; exact c31
        · simp only [upd_apply, a, ↓reduceIte]
          rw [hq₃ r h k, q₂ r e' b f' c']
          exact hq r a b c' e' f' h k l
      have s1 : wMk C w mk 1 (j + 1) = wMk C w mk 1 j +
          if mk (lv C j) = 1 then SepProg.wI w (lv C j) else 0 := by unfold wMk; rw [sum_range_succ]
      have s2 : wMk C w mk 2 (j + 1) = wMk C w mk 2 j +
          if mk (lv C j) = 2 then SepProg.wI w (lv C j) else 0 := by unfold wMk; rw [sum_range_succ]
      by_cases hm2 : mk (lv C j) < 2
      · have t1 : d₂.nreg 1119 < d₂.nreg 1130 := by rw [b19, c30]; exact hm2
        by_cases hm0 : mk (lv C j) = 0
        · obtain ⟨d₄, e₄, hI₄⟩ := hfin d₂ hw₂ (by rw [m₂, hm])
            (by rw [c28, s1, iteF (by omega)]; rfl) (by rw [c29, s2, iteF (by omega)]; rfl)
            (fun _ _ _ => rfl)
          exact ⟨d₄, _, .seq e₂ (.seq (.ifLtN_true t1 (.ifLtN_false (by rw [b19, c00, hm0]; omega)
            (.skip hw₂))) e₄), hI₄, by omega⟩
        · have hm1 : mk (lv C j) = 1 := by omega
          have e3 := Exec.addN (P := P) hw₂ 1128 1128 1117 (by rw [c28, b17]; omega)
          have v28 : (upd d₂.nreg 1128 (d₂.nreg 1128 + d₂.nreg 1117)) 1128 =
              wMk C w mk 1 (j + 1) := by rw [upd_same, c28, b17, s1, iteT hm1]
          have v29 : (upd d₂.nreg 1128 (d₂.nreg 1128 + d₂.nreg 1117)) 1129 =
              wMk C w mk 2 (j + 1) := by
            rw [upd_other _ _ _ (by omega), c29, s2, iteF (by omega)]; rfl
          obtain ⟨d₄, e₄, hI₄⟩ := hfin _ e3.wb_right (show d₂.nmem = d.nmem by rw [m₂, hm]) v28 v29
            (fun r h1 h2 => upd_other _ _ _ h1)
          exact ⟨d₄, _, .seq e₂ (.seq (.ifLtN_true t1 (.ifLtN_true (by rw [b19, c00, hm1]; omega)
            e3)) e₄), hI₄, by omega⟩
      · have t1 : ¬ d₂.nreg 1119 < d₂.nreg 1130 := by rw [b19, c30]; exact hm2
        by_cases hm3 : mk (lv C j) = 2
        · have e3 := Exec.addN (P := P) hw₂ 1129 1129 1117 (by rw [c29, b17]; omega)
          have v29 : (upd d₂.nreg 1129 (d₂.nreg 1129 + d₂.nreg 1117)) 1129 =
              wMk C w mk 2 (j + 1) := by rw [upd_same, c29, b17, s2, iteT hm3]
          have v28 : (upd d₂.nreg 1129 (d₂.nreg 1129 + d₂.nreg 1117)) 1128 =
              wMk C w mk 1 (j + 1) := by
            rw [upd_other _ _ _ (by omega), c28, s1, iteF (by omega)]; rfl
          obtain ⟨d₄, e₄, hI₄⟩ := hfin _ e3.wb_right (show d₂.nmem = d.nmem by rw [m₂, hm]) v28 v29
            (fun r h1 h2 => upd_other _ _ _ h2)
          exact ⟨d₄, _, .seq e₂ (.seq (.ifLtN_false t1 (.ifLtN_true (by rw [b19, c31, hm3]; omega)
            e3)) e₄), hI₄, by omega⟩
        · obtain ⟨d₄, e₄, hI₄⟩ := hfin d₂ hw₂ (by rw [m₂, hm])
            (by rw [c28, s1, iteF (by omega)]; rfl) (by rw [c29, s2, iteF hm3]; rfl)
            (fun _ _ _ => rfl)
          exact ⟨d₄, _, .seq e₂ (.seq (.ifLtN_false t1 (.ifLtN_false (by rw [b19, c31]; omega)
            (.skip hw₂))) e₄), hI₄, by omega⟩)
    (Nat.zero_le _) hI₀
  obtain ⟨hw₁, -, -, h28₁, h29₁, -, hq₁, hm₁⟩ := hI₁
  exact ⟨d₁, k₀ + k₁, .seq e₀ e₁, hw₁, h28₁, h29₁, hq₁, hm₁, by omega⟩

/-- The mark of the rest of `U`: `1` if the first part is the lighter, else `2`. -/
def selPass : Stmt :=
  .seq (.instr (.copyN 1126 1001)) (.ifLtN 1129 1128 (.instr (.addN 1126 1001 1001)) .skip)

theorem selPass_exec {d : Config} (hw : WordsBounded W d) (h01 : d.nreg 1001 = 1)
    (hNW : 2 ≤ W) :
    ∃ d' k, Exec P W selPass d d' k ∧ WordsBounded W d' ∧
      d'.nreg 1126 = (if d.nreg 1128 ≤ d.nreg 1129 then 1 else 2) ∧
      (∀ r, r ≠ 1126 → d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem ∧ k ≤ 3 := by
  have e1 := Exec.copyN (P := P) hw 1126 1001
  set d₁ := { d with nreg := upd d.nreg 1126 (d.nreg 1001) }
  have hw₁ : WordsBounded W d₁ := e1.wb_right
  have b01 : d₁.nreg 1001 = 1 := by simp [d₁, h01]
  have b28 : d₁.nreg 1128 = d.nreg 1128 := by simp [d₁]
  have b29 : d₁.nreg 1129 = d.nreg 1129 := by simp [d₁]
  by_cases h : d₁.nreg 1129 < d₁.nreg 1128
  · have e2 := Exec.addN (P := P) hw₁ 1126 1001 1001 (by rw [b01]; omega)
    refine ⟨_, _, .seq e1 (.ifLtN_true h e2), e2.wb_right, ?_, fun r hr => ?_, rfl, by omega⟩
    · rw [b28, b29] at h; simp [b01, iteF (show ¬ d.nreg 1128 ≤ d.nreg 1129 by omega)]
    · simp [d₁, hr]
  · refine ⟨_, _, .seq e1 (.ifLtN_false h (.skip hw₁)), hw₁, ?_, fun r hr => ?_, rfl, by omega⟩
    · rw [b28, b29] at h; simp [d₁, h01, iteT (show d.nreg 1128 ≤ d.nreg 1129 by omega)]
    · simp [d₁, hr]

/-- The body of the pass marking the rest of `U`. -/
def rBody : Stmt :=
  .seq (block pfx) (.seq (.instr (.addN 1118 1019 1114)) (.seq (.ifLtN 1119 1121
    (.instr (.storeN 1118 1126)) (.ifLtN 1121 1119 (.instr (.storeN 1118 1126)) .skip))
    (.instr (.addN 1110 1110 1001))))

/-- **The marks of the rest of `U`**: the mark `1126` on the vertices of `U` whose label is not
`1121`. -/
def rPass : Stmt := .seq (.instr (.constN 1110 0)) (.whileLtN 1110 1101 rBody)

theorem rPass_exec {d : Config} (hw : WordsBounded W d) {aU aC aM hb sel : ℕ}
    (h01 : d.nreg 1001 = 1) (h00 : d.nreg 1100 = aU) (h02 : d.nreg 1102 = aC)
    (h19 : d.nreg 1019 = aM) (h1101 : d.nreg 1101 = #U) (h21 : d.nreg 1121 = hb)
    (h26 : d.nreg 1126 = sel) (hU : ∀ l < #U, d.nmem (aU + l) = lv U l)
    (l1 : aU + N ≤ aC) (l2 : aC + N ≤ aM) (l3 : aM + N ≤ W) :
    ∃ d' k, Exec P W rPass d d' k ∧ WordsBounded W d' ∧
      (∀ x < N, d'.nmem (aM + x) =
        if x ∈ UN U ∧ d.nmem (aC + x) ≠ hb then sel else d.nmem (aM + x)) ∧
      (∀ a, a < aM ∨ aM + N ≤ a → d'.nmem a = d.nmem a) ∧
      (∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1118 → r ≠ 1119 → d'.nreg r = d.nreg r) ∧
      k ≤ 12 * #U + 3 := by
  have hUN := card_le_N U
  have e0 := Exec.constN (P := P) hw 1110 0 (Nat.zero_le _)
  let I : ℕ → Config → Prop := fun i d' => WordsBounded W d' ∧ d'.nreg 1110 = i ∧
    d'.nreg 1101 = #U ∧
    (∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1118 → r ≠ 1119 → d'.nreg r = d.nreg r) ∧
    (∀ x < N, d'.nmem (aM + x) =
      if (∃ l < i, lv U l = x) ∧ d.nmem (aC + x) ≠ hb then sel else d.nmem (aM + x)) ∧
    (∀ a, a < aM ∨ aM + N ≤ a → d'.nmem a = d.nmem a)
  have hI₀ : I 0 _ := ⟨e0.wb_right, by simp, by simp [h1101],
    fun r hr _ _ _ => by simp [hr], fun x hx => by simp, fun a _ => rfl⟩
  obtain ⟨d₁, k₁, e₁, hI₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1110) (rN := 1101)
    (N := #U) (lo := 0) (B := 10) (body := rBody) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw', h10, h01', hq, hmk, hfr⟩ := h
      have hx := lv_ltN U hi
      have mU : d'.nmem (aU + i) = lv U i := by rw [hfr _ (Or.inl (by omega))]; exact hU i hi
      have mC : d'.nmem (aC + lv U i) = d.nmem (aC + lv U i) := hfr _ (Or.inl (by omega))
      obtain ⟨d₂, e₂, hw₂, b14, b18, b19, q₂, m₂⟩ := pfx_exec (P := P) hw'
        (by rw [hq 1100 (by omega) (by omega) (by omega) (by omega), h00])
        (by rw [hq 1102 (by omega) (by omega) (by omega) (by omega), h02]) h10 mU
        (by omega) (by omega)
      rw [mC] at b19
      have q2 : ∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1118 → r ≠ 1119 → d₂.nreg r = d.nreg r :=
        fun r a b c' e => by rw [q₂ r c' b e, hq r a b c' e]
      have e3 := Exec.addN (P := P) hw₂ 1118 1019 1114
        (by rw [q2 1019 (by omega) (by omega) (by omega) (by omega), h19, b14]; omega)
      set d₃ := { d₂ with nreg := upd d₂.nreg 1118 (d₂.nreg 1019 + d₂.nreg 1114) }
      have hw₃ : WordsBounded W d₃ := e3.wb_right
      have c18 : d₃.nreg 1118 = aM + lv U i := by
        simp [d₃, q2 1019 (by omega) (by omega) (by omega) (by omega), h19, b14]
      have q3 : ∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1118 → r ≠ 1119 → d₃.nreg r = d.nreg r :=
        fun r a b c' e => by simp [d₃, c']; exact q2 r a b c' e
      have c19 : d₃.nreg 1119 = d.nmem (aC + lv U i) := by simp [d₃]; exact b19
      have c21 : d₃.nreg 1121 = hb := by rw [q3 1121 (by omega) (by omega) (by omega) (by omega), h21]
      have c26 : d₃.nreg 1126 = sel := by rw [q3 1126 (by omega) (by omega) (by omega) (by omega), h26]
      have c10 : d₃.nreg 1110 = i := by simp [d₃]; rw [q₂ 1110 (by omega) (by omega) (by omega), h10]
      have c01 : d₃.nreg 1001 = 1 := by
        rw [q3 1001 (by omega) (by omega) (by omega) (by omega), h01]
      have hm₃ : d₃.nmem = d'.nmem := by simp [d₃]; exact m₂
      -- the end of the body from a state `d₄`
      have hfin : ∀ d₄ : Config, WordsBounded W d₄ → (∀ r, d₄.nreg r = d₃.nreg r) →
          d₄.nmem = (if d.nmem (aC + lv U i) ≠ hb then upd d'.nmem (aM + lv U i) sel
            else d'.nmem) →
          ∃ d₅, Exec P W (.instr (.addN 1110 1110 1001)) d₄ d₅ 1 ∧ I (i + 1) d₅ := by
        intro d₄ hw₄ hr₄ hm₄
        have e := Exec.addN (P := P) hw₄ 1110 1110 1001 (by rw [hr₄, hr₄, c10, c01]; omega)
        refine ⟨_, e, e.wb_right, by simp [hr₄, c10, c01], by simp [hr₄]; rw [q3 1101 (by omega)
          (by omega) (by omega) (by omega), h1101], fun r a b c' e' => by
            simp [a]; rw [hr₄, q3 r a b c' e'], fun x hxN => ?_, fun a ha => ?_⟩
        · simp only
          rw [hm₄]
          by_cases hne : d.nmem (aC + lv U i) ≠ hb
          · rw [iteT hne]
            by_cases hxi : x = lv U i
            · subst hxi
              rw [upd_same, iteT ⟨⟨i, Nat.lt_succ_self _, rfl⟩, hne⟩]
            · rw [upd_other _ _ _ (by omega), hmk x hxN]
              congr 1
              apply propext
              constructor
              · rintro ⟨⟨l, hl, e⟩, h⟩; exact ⟨⟨l, by omega, e⟩, h⟩
              · rintro ⟨⟨l, hl, e⟩, h⟩
                refine ⟨⟨l, ?_, e⟩, h⟩
                rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
                · exact hl
                · exact absurd e.symm hxi
          · rw [iteF hne, hmk x hxN]
            congr 1
            apply propext
            constructor
            · rintro ⟨⟨l, hl, e⟩, h⟩; exact ⟨⟨l, by omega, e⟩, h⟩
            · rintro ⟨⟨l, hl, e⟩, h⟩
              refine ⟨⟨l, ?_, e⟩, h⟩
              rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
              · exact hl
              · subst e; exact absurd h hne
        · simp only
          rw [hm₄]
          split_ifs
          · rw [upd_other _ _ _ (by omega)]; exact hfr a ha
          · exact hfr a ha
      by_cases hlt : d₃.nreg 1119 < d₃.nreg 1121
      · have e4 := Exec.storeN (P := P) hw₃ 1118 1126
        have hne : d.nmem (aC + lv U i) ≠ hb := by rw [c19, c21] at hlt; omega
        obtain ⟨d₅, e₅, hI₅⟩ := hfin _ e4.wb_right (fun r => rfl)
          (by simp only; rw [iteT hne, c18, c26, hm₃])
        exact ⟨d₅, _, .seq e₂ (.seq e3 (.seq (.ifLtN_true hlt e4) e₅)), hI₅, by omega⟩
      · by_cases hgt : d₃.nreg 1121 < d₃.nreg 1119
        · have e4 := Exec.storeN (P := P) hw₃ 1118 1126
          have hne : d.nmem (aC + lv U i) ≠ hb := by rw [c19, c21] at hgt; omega
          obtain ⟨d₅, e₅, hI₅⟩ := hfin _ e4.wb_right (fun r => rfl)
            (by simp only; rw [iteT hne, c18, c26, hm₃])
          exact ⟨d₅, _, .seq e₂ (.seq e3 (.seq (.ifLtN_false hlt (.ifLtN_true hgt e4)) e₅)),
            hI₅, by omega⟩
        · have heq : ¬ d.nmem (aC + lv U i) ≠ hb := by rw [c19, c21] at hlt hgt; omega
          obtain ⟨d₅, e₅, hI₅⟩ := hfin d₃ hw₃ (fun r => rfl) (by rw [iteF heq, hm₃])
          exact ⟨d₅, _, .seq e₂ (.seq e3 (.seq (.ifLtN_false hlt (.ifLtN_false hgt
            (.skip hw₃))) e₅)), hI₅, by omega⟩)
    (Nat.zero_le _) hI₀
  obtain ⟨hw₁, -, -, hq₁, hmk₁, hfr₁⟩ := hI₁
  refine ⟨d₁, 1 + k₁, .seq e0 e₁, hw₁, fun x hx => ?_, hfr₁, hq₁, by omega⟩
  rw [hmk₁ x hx]
  congr 1
  apply propext
  rw [lv_mem_iff U]

end Piece

end PlanarSeparator
