module

public import PlanarFlow.BKMNW.MbMark

/-!
# Miller's base, step 5: the new-hole flags and the labels of the two items

One scan over the indices `i < n`: `NH[i] := KM[TK[i]]` (the class of the tail of `e i` meets
the separator cycle), and for a dart of the piece (`NF[i] ≠ 0`) the label of its item: with
`a = [KM[TK[i]] = 0]` (the vertex of `e i` is off the cycle), `zi` the face mark of the triangle
of `e i` (`ZF[RK[i]]`, normalised by `z = r643`, `one = [r644 = 1]`), and `b`, `zj` the same for
the reverse `j = RV[i]`: label `1` if `(a ∧ zi) ∨ (b ∧ zj)`, else `2` if `(a ∧ ¬ zi) ∨ (b ∧ ¬ zj)`,
else `0`. All arithmetic is by truncated subtraction (`sgn x = x - (x - 1)`, products of bits
`x - (1 - y)`).

* `lbSg`, `lbZ`, `lbV` (the arithmetic), **`lbZ_eq`**, **`lbV_eq`** (its meaning);
* `lbA`, `lbB1`, `lbB2`, `lbB3`, `lbBody`, **`lbl`**, the block lemmas, `lbBody_exec`,
  **`lbl_exec`** (`70 n + 5` steps); registers `5150 = n`, `5151 = NFb`, `5152 = TKb`,
  `5153 = KMb`, `5154 = RKb`, `5155 = ZFb`, `5156 = RVb`, `5157 = NHb`, `5158 = ITb`,
  `5159 = z`, `5160 = one`; written `5161 … 5182`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The arithmetic -/

/-- The sign by truncated subtraction. -/
abbrev lbSg (x : ℕ) : ℕ := x - (x - 1)

/-- The normalised face mark: `1` iff `(v ≠ z) ↔ one = 1` (for `one ≤ 1`). -/
abbrev lbZ (v z one : ℕ) : ℕ :=
  1 - ((lbSg ((v - z) + (z - v)) - one) + (one - lbSg ((v - z) + (z - v))))

/-- **The label of a dart** from the marks of its two ends and the face marks of its triangle and
of its reverse's. -/
abbrev lbV (kmi vi kmj vj z one : ℕ) : ℕ :=
  lbSg (((1 - kmi) - (1 - lbZ vi z one)) + ((1 - kmj) - (1 - lbZ vj z one))) +
    ((lbSg (((1 - kmi) - lbZ vi z one) + ((1 - kmj) - lbZ vj z one)) -
      lbSg (((1 - kmi) - (1 - lbZ vi z one)) + ((1 - kmj) - (1 - lbZ vj z one)))) +
     (lbSg (((1 - kmi) - lbZ vi z one) + ((1 - kmj) - lbZ vj z one)) -
      lbSg (((1 - kmi) - (1 - lbZ vi z one)) + ((1 - kmj) - (1 - lbZ vj z one)))))

lemma lbZ_eq {v z one : ℕ} (h : one ≤ 1) :
    lbZ v z one = if ((v ≠ z) ↔ one = 1) then 1 else 0 := by
  unfold lbZ lbSg
  by_cases hv : v = z
  · subst hv; split_ifs with h' <;> simp_all <;> omega
  · split_ifs with h' <;> simp_all <;> omega

lemma lbZ_le (v z one : ℕ) : lbZ v z one ≤ 1 := by unfold lbZ; omega

/-- **The meaning of the label.** -/
lemma lbV_eq (kmi vi kmj vj z one : ℕ) :
    lbV kmi vi kmj vj z one =
      if (kmi = 0 ∧ lbZ vi z one = 1) ∨ (kmj = 0 ∧ lbZ vj z one = 1) then 1
      else if (kmi = 0 ∧ lbZ vi z one ≠ 1) ∨ (kmj = 0 ∧ lbZ vj z one ≠ 1) then 2 else 0 := by
  have h1 := lbZ_le vi z one
  have h2 := lbZ_le vj z one
  unfold lbV lbSg
  generalize lbZ vi z one = zi at h1 ⊢
  generalize lbZ vj z one = zj at h2 ⊢
  split_ifs with a b <;> omega

/-! ### The program -/

/-- `NH[i] := KM[TK[i]]` (`5165 = KM[TK[i]]`), `5167 = NF[i]`. -/
def lbA : Stmt :=
  block [.addN 5167 5151 5163, .loadN 5167 5167, .addN 5164 5152 5163, .loadN 5164 5164,
    .addN 5164 5153 5164, .loadN 5165 5164, .addN 5166 5157 5163, .storeN 5166 5165]

/-- The face mark of the triangle of `e i` (`5170`). -/
def lbB1 : Stmt :=
  block [.addN 5168 5154 5163, .loadN 5168 5168, .addN 5168 5155 5168, .loadN 5168 5168,
    .subN 5169 5168 5159, .subN 5170 5159 5168, .addN 5169 5169 5170,
    .subN 5170 5169 5161, .subN 5169 5169 5170,
    .subN 5170 5169 5160, .subN 5171 5160 5169, .addN 5170 5170 5171, .subN 5170 5161 5170]

/-- The reverse `j = RV[i]`: `5173 = KM[TK[j]]`, the face mark of its triangle (`5176`). -/
def lbB2 : Stmt :=
  block [.addN 5172 5156 5163, .loadN 5172 5172,
    .addN 5173 5152 5172, .loadN 5173 5173, .addN 5173 5153 5173, .loadN 5173 5173,
    .addN 5174 5154 5172, .loadN 5174 5174, .addN 5174 5155 5174, .loadN 5174 5174,
    .subN 5175 5174 5159, .subN 5176 5159 5174, .addN 5175 5175 5176,
    .subN 5176 5175 5161, .subN 5175 5175 5176,
    .subN 5176 5175 5160, .subN 5177 5160 5175, .addN 5176 5176 5177, .subN 5176 5161 5176]

/-- The label and its store at `ITb + i`. -/
def lbB3 : Stmt :=
  block [.subN 5178 5161 5165, .subN 5179 5161 5173,
    .subN 5180 5161 5170, .subN 5180 5178 5180, .subN 5181 5161 5176, .subN 5181 5179 5181,
    .addN 5180 5180 5181, .subN 5181 5180 5161, .subN 5180 5180 5181,
    .subN 5181 5178 5170, .subN 5182 5179 5176, .addN 5181 5181 5182,
    .subN 5182 5181 5161, .subN 5181 5181 5182,
    .subN 5182 5181 5180, .addN 5182 5182 5182, .addN 5182 5180 5182,
    .addN 5166 5158 5163, .storeN 5166 5182]

/-- One index (`5161 = 1`, `5162 = 0`, `5163 = i`). -/
def lbBody : Stmt :=
  .seq lbA (.seq (.ifLtN 5162 5167 (.seq lbB1 (.seq lbB2 lbB3))
    (block [.addN 5166 5158 5163, .storeN 5166 5162])) (block [.addN 5163 5163 5161]))

/-- **The new-hole flags and the labels.** -/
def lbl : Stmt :=
  .seq (block [.constN 5161 1, .constN 5162 0, .constN 5163 0]) (.whileLtN 5163 5150 lbBody)

section Lb

variable {P : Input} {W : ℕ}

theorem lbA_exec (c : Config) (hc : WordsBounded W c) {NFb TKb KMb NHb i : ℕ}
    (r1 : c.nreg 5151 = NFb) (r2 : c.nreg 5152 = TKb) (r3 : c.nreg 5153 = KMb)
    (r7 : c.nreg 5157 = NHb) (r63 : c.nreg 5163 = i)
    (w1 : TKb + i ≤ W) (w2 : KMb + c.nmem (TKb + i) ≤ W) (w3 : NHb + i ≤ W) (w4 : NFb + i ≤ W) :
    ∃ c' t, Exec P W lbA c c' t ∧ t = 8 ∧ c'.nreg 5165 = c.nmem (KMb + c.nmem (TKb + i)) ∧
      c'.nreg 5167 = c.nmem (NFb + i) ∧
      c'.nmem = upd c.nmem (NHb + i) (c.nmem (KMb + c.nmem (TKb + i))) ∧
      (∀ x, (x < 5164 ∨ 5167 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lbA
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r7, r63]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r1, r2, r3, r7, r63]
  · config_simp; simp only [r1, r2, r3, r7, r63]
  · config_simp; simp only [r1, r2, r3, r7, r63]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem lbB1_exec (c : Config) (hc : WordsBounded W c) {RKb ZFb z one i : ℕ}
    (r4 : c.nreg 5154 = RKb) (r5 : c.nreg 5155 = ZFb) (r9 : c.nreg 5159 = z)
    (r60 : c.nreg 5160 = one) (r61 : c.nreg 5161 = 1) (r63 : c.nreg 5163 = i)
    (w1 : RKb + i ≤ W) (w2 : ZFb + c.nmem (RKb + i) ≤ W) :
    ∃ c' t, Exec P W lbB1 c c' t ∧ t = 13 ∧
      c'.nreg 5170 = lbZ (c.nmem (ZFb + c.nmem (RKb + i))) z one ∧ c'.nmem = c.nmem ∧
      (∀ x, (x < 5168 ∨ 5171 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hz : z ≤ W := by rw [← r9]; exact hc.1 _
  have ho : one ≤ W := by rw [← r60]; exact hc.1 _
  have hv : c.nmem (ZFb + c.nmem (RKb + i)) ≤ W := hc.2 _
  unfold lbB1
  exec_block
  all_goals try (config_simp; simp only [r4, r5, r9, r60, r61, r63]; omega)
  refine ⟨rfl, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r4, r5, r9, r60, r61, r63]
    try (unfold lbZ lbSg; omega)
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem lbB2_exec (c : Config) (hc : WordsBounded W c) {TKb KMb RKb ZFb RVb z one i : ℕ}
    (r2 : c.nreg 5152 = TKb) (r3 : c.nreg 5153 = KMb) (r4 : c.nreg 5154 = RKb)
    (r5 : c.nreg 5155 = ZFb) (r6 : c.nreg 5156 = RVb) (r9 : c.nreg 5159 = z)
    (r60 : c.nreg 5160 = one) (r61 : c.nreg 5161 = 1) (r63 : c.nreg 5163 = i)
    (w1 : RVb + i ≤ W) (w2 : TKb + c.nmem (RVb + i) ≤ W)
    (w3 : KMb + c.nmem (TKb + c.nmem (RVb + i)) ≤ W) (w4 : RKb + c.nmem (RVb + i) ≤ W)
    (w5 : ZFb + c.nmem (RKb + c.nmem (RVb + i)) ≤ W) :
    ∃ c' t, Exec P W lbB2 c c' t ∧ t = 19 ∧
      c'.nreg 5173 = c.nmem (KMb + c.nmem (TKb + c.nmem (RVb + i))) ∧
      c'.nreg 5176 = lbZ (c.nmem (ZFb + c.nmem (RKb + c.nmem (RVb + i)))) z one ∧
      c'.nmem = c.nmem ∧
      (∀ x, (x < 5172 ∨ 5177 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hz : z ≤ W := by rw [← r9]; exact hc.1 _
  have ho : one ≤ W := by rw [← r60]; exact hc.1 _
  have hv : c.nmem (ZFb + c.nmem (RKb + c.nmem (RVb + i))) ≤ W := hc.2 _
  unfold lbB2
  exec_block
  all_goals try (config_simp; simp only [r2, r3, r4, r5, r6, r9, r60, r61, r63]; omega)
  refine ⟨rfl, ?_, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r2, r3, r4, r5, r6, r9, r60, r61, r63]
  · config_simp; simp only [r2, r3, r4, r5, r6, r9, r60, r61, r63]
    try (unfold lbZ lbSg; omega)
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem lbB3_exec (c : Config) (hc : WordsBounded W c) {ITb i kmi zi kmj zj : ℕ}
    (r8 : c.nreg 5158 = ITb) (r61 : c.nreg 5161 = 1) (r63 : c.nreg 5163 = i)
    (r65 : c.nreg 5165 = kmi) (r70 : c.nreg 5170 = zi) (r73 : c.nreg 5173 = kmj)
    (r76 : c.nreg 5176 = zj) (w1 : ITb + i ≤ W) (w0 : 3 ≤ W) :
    ∃ c' t, Exec P W lbB3 c c' t ∧ t = 19 ∧
      c'.nmem = upd c.nmem (ITb + i)
        (lbSg (((1 - kmi) - (1 - zi)) + ((1 - kmj) - (1 - zj))) +
          ((lbSg (((1 - kmi) - zi) + ((1 - kmj) - zj)) -
            lbSg (((1 - kmi) - (1 - zi)) + ((1 - kmj) - (1 - zj)))) +
           (lbSg (((1 - kmi) - zi) + ((1 - kmj) - zj)) -
            lbSg (((1 - kmi) - (1 - zi)) + ((1 - kmj) - (1 - zj)))))) ∧
      (∀ x, (x < 5166 ∨ (5166 < x ∧ x < 5178) ∨ 5182 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lbB3
  exec_block
  all_goals try (config_simp; simp only [r8, r61, r63, r65, r70, r73, r76]; omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r8, r61, r63, r65, r70, r73, r76]
    try (congr 1; unfold lbSg; omega)
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

set_option maxHeartbeats 800000 in
theorem lbBody_exec (c : Config) (hc : WordsBounded W c)
    {NFb TKb KMb RKb ZFb RVb NHb ITb z one i : ℕ}
    (r1 : c.nreg 5151 = NFb) (r2 : c.nreg 5152 = TKb) (r3 : c.nreg 5153 = KMb)
    (r4 : c.nreg 5154 = RKb) (r5 : c.nreg 5155 = ZFb) (r6 : c.nreg 5156 = RVb)
    (r7 : c.nreg 5157 = NHb) (r8 : c.nreg 5158 = ITb) (r9 : c.nreg 5159 = z)
    (r60 : c.nreg 5160 = one) (r61 : c.nreg 5161 = 1) (r62 : c.nreg 5162 = 0)
    (r63 : c.nreg 5163 = i)
    (w1 : TKb + i ≤ W) (w2 : KMb + c.nmem (TKb + i) ≤ W) (w3 : NHb + i ≤ W) (w4 : NFb + i ≤ W)
    (w5 : ITb + i ≤ W) (w6 : i + 1 ≤ W) (w0 : 3 ≤ W)
    (hfl : c.nmem (NFb + i) ≠ 0 →
      RKb + i ≤ W ∧ ZFb + c.nmem (RKb + i) ≤ W ∧ RVb + i ≤ W ∧ TKb + c.nmem (RVb + i) ≤ W ∧
      KMb + c.nmem (TKb + c.nmem (RVb + i)) ≤ W ∧ RKb + c.nmem (RVb + i) ≤ W ∧
      ZFb + c.nmem (RKb + c.nmem (RVb + i)) ≤ W)
    (hNHr : ∀ a, (a = TKb + i ∨ a = KMb + c.nmem (TKb + i) ∨ a = NFb + i ∨ a = RKb + i ∨
      a = ZFb + c.nmem (RKb + i) ∨ a = RVb + i ∨ a = TKb + c.nmem (RVb + i) ∨
      a = KMb + c.nmem (TKb + c.nmem (RVb + i)) ∨ a = RKb + c.nmem (RVb + i) ∨
      a = ZFb + c.nmem (RKb + c.nmem (RVb + i))) → a ≠ NHb + i) :
    ∃ c' t, Exec P W lbBody c c' t ∧ t ≤ 64 ∧ c'.nreg 5163 = i + 1 ∧
      c'.nmem = upd (upd c.nmem (NHb + i) (c.nmem (KMb + c.nmem (TKb + i)))) (ITb + i)
        (if c.nmem (NFb + i) ≠ 0 then
          lbV (c.nmem (KMb + c.nmem (TKb + i))) (c.nmem (ZFb + c.nmem (RKb + i)))
            (c.nmem (KMb + c.nmem (TKb + c.nmem (RVb + i))))
            (c.nmem (ZFb + c.nmem (RKb + c.nmem (RVb + i)))) z one
        else 0) ∧
      (∀ x, (x < 5163 ∨ 5182 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a65, a67, am₁, an₁, ar₁, arm₁, ao₁⟩ :=
    lbA_exec (P := P) c hc r1 r2 r3 r7 r63 w1 w2 w3 w4
  have hw₁ := e₁.wb_right
  have k : ∀ x, (x < 5164 ∨ 5167 < x) → c₁.nreg x = c.nreg x := an₁
  have hm₁c : ∀ a, a ≠ NHb + i → c₁.nmem a = c.nmem a := fun a ha => by
    rw [am₁, upd_other _ _ _ ha]
  have n1 : TKb + i ≠ NHb + i := hNHr _ (Or.inl rfl)
  have n2 : KMb + c.nmem (TKb + i) ≠ NHb + i := hNHr _ (Or.inr (Or.inl rfl))
  have n4 : RKb + i ≠ NHb + i := hNHr _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have n5 : ZFb + c.nmem (RKb + i) ≠ NHb + i :=
    hNHr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have n6 : RVb + i ≠ NHb + i := hNHr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have n7 : TKb + c.nmem (RVb + i) ≠ NHb + i :=
    hNHr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have n8 : KMb + c.nmem (TKb + c.nmem (RVb + i)) ≠ NHb + i :=
    hNHr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have n9 : RKb + c.nmem (RVb + i) ≠ NHb + i :=
    hNHr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have n10 : ZFb + c.nmem (RKb + c.nmem (RVb + i)) ≠ NHb + i :=
    hNHr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))
  obtain ⟨c₂, t₂, e₂, ht₂, bm₂, bn₂, br₂, brm₂, bo₂⟩ : ∃ c₂ t₂,
      Exec P W (.ifLtN 5162 5167 (.seq lbB1 (.seq lbB2 lbB3))
        (block [.addN 5166 5158 5163, .storeN 5166 5162])) c₁ c₂ t₂ ∧ t₂ ≤ 53 ∧
      c₂.nmem = upd c₁.nmem (ITb + i)
        (if c.nmem (NFb + i) ≠ 0 then
          lbV (c.nmem (KMb + c.nmem (TKb + i))) (c.nmem (ZFb + c.nmem (RKb + i)))
            (c.nmem (KMb + c.nmem (TKb + c.nmem (RVb + i))))
            (c.nmem (ZFb + c.nmem (RKb + c.nmem (RVb + i)))) z one
        else 0) ∧
      (∀ x, (x < 5166 ∨ (5166 < x ∧ x < 5168) ∨ 5182 < x) → c₂.nreg x = c₁.nreg x) ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    by_cases hF : c.nmem (NFb + i) ≠ 0
    · have hlt : c₁.nreg 5162 < c₁.nreg 5167 := by rw [k _ (by omega), r62, a67]; omega
      obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfl hF
      -- the three blocks
      obtain ⟨d₁, s₁, x₁, hs₁, p70, pm₁, pn₁, pr₁, prm₁, po₁⟩ :=
        lbB1_exec (P := P) c₁ hw₁ (RKb := RKb) (ZFb := ZFb) (z := z) (one := one) (i := i)
          (by rw [k _ (by omega), r4]) (by rw [k _ (by omega), r5]) (by rw [k _ (by omega), r9])
          (by rw [k _ (by omega), r60]) (by rw [k _ (by omega), r61])
          (by rw [k _ (by omega), r63]) f1 (by rw [hm₁c _ n4]; exact f2)
      have hwd₁ := x₁.wb_right
      have kk : ∀ x, (x < 5164 ∨ 5171 < x) → d₁.nreg x = c.nreg x := fun x hx => by
        rw [pn₁ x (by omega), k x (by omega)]
      obtain ⟨d₂, s₂, x₂, hs₂, q73, q76, qm₂, qn₂, qr₂, qrm₂, qo₂⟩ :=
        lbB2_exec (P := P) d₁ hwd₁ (TKb := TKb) (KMb := KMb) (RKb := RKb) (ZFb := ZFb)
          (RVb := RVb) (z := z) (one := one) (i := i)
          (by rw [kk _ (by omega), r2]) (by rw [kk _ (by omega), r3]) (by rw [kk _ (by omega), r4])
          (by rw [kk _ (by omega), r5]) (by rw [kk _ (by omega), r6]) (by rw [kk _ (by omega), r9])
          (by rw [kk _ (by omega), r60]) (by rw [kk _ (by omega), r61])
          (by rw [kk _ (by omega), r63]) f3
          (by rw [pm₁, hm₁c _ n6]; exact f4)
          (by rw [pm₁, hm₁c _ n6, hm₁c _ n7]; exact f5)
          (by rw [pm₁, hm₁c _ n6]; exact f6)
          (by rw [pm₁, hm₁c _ n6, hm₁c _ n9]; exact f7)
      have hwd₂ := x₂.wb_right
      have e1 : c₁.nmem (KMb + c₁.nmem (TKb + i)) = c.nmem (KMb + c.nmem (TKb + i)) := by
        rw [hm₁c _ n1, hm₁c _ n2]
      have e2 : c₁.nmem (ZFb + c₁.nmem (RKb + i)) = c.nmem (ZFb + c.nmem (RKb + i)) := by
        rw [hm₁c _ n4, hm₁c _ n5]
      have e3 : c₁.nmem (KMb + c₁.nmem (TKb + c₁.nmem (RVb + i))) =
          c.nmem (KMb + c.nmem (TKb + c.nmem (RVb + i))) := by
        rw [hm₁c _ n6, hm₁c _ n7, hm₁c _ n8]
      have e4 : c₁.nmem (ZFb + c₁.nmem (RKb + c₁.nmem (RVb + i))) =
          c.nmem (ZFb + c.nmem (RKb + c.nmem (RVb + i))) := by
        rw [hm₁c _ n6, hm₁c _ n9, hm₁c _ n10]
      obtain ⟨d₃, s₃, x₃, hs₃, um₃, un₃, ur₃, urm₃, uo₃⟩ :=
        lbB3_exec (P := P) d₂ hwd₂ (ITb := ITb) (i := i)
          (kmi := c.nmem (KMb + c.nmem (TKb + i)))
          (zi := lbZ (c.nmem (ZFb + c.nmem (RKb + i))) z one)
          (kmj := c.nmem (KMb + c.nmem (TKb + c.nmem (RVb + i))))
          (zj := lbZ (c.nmem (ZFb + c.nmem (RKb + c.nmem (RVb + i)))) z one)
          (by rw [qn₂ _ (by omega), kk _ (by omega), r8]) (by rw [qn₂ _ (by omega), kk _ (by omega), r61])
          (by rw [qn₂ _ (by omega), kk _ (by omega), r63])
          (by rw [qn₂ _ (by omega), pn₁ _ (by omega), a65])
          (by rw [qn₂ _ (by omega), p70, e2]) (by rw [q73, pm₁, e3]) (by rw [q76, pm₁, e4]) w5 w0
      refine ⟨d₃, s₁ + (s₂ + s₃) + 1, .ifLtN_true hlt (.seq x₁ (.seq x₂ x₃)), by omega, ?_,
        fun x hx => ?_, by rw [ur₃, qr₂, pr₁], by rw [urm₃, qrm₂, prm₁], by rw [uo₃, qo₂, po₁]⟩
      · rw [um₃, qm₂, pm₁, iteT hF]
      · rw [un₃ x (by omega), qn₂ x (by omega), pn₁ x (by omega)]
    · have hnlt : ¬ c₁.nreg 5162 < c₁.nreg 5167 := by rw [k _ (by omega), r62, a67]; omega
      obtain ⟨d₁, s₁, x₁, hs₁, um, un, ur, urm, uo⟩ : ∃ d₁ s₁,
          Exec P W (block [.addN 5166 5158 5163, .storeN 5166 5162]) c₁ d₁ s₁ ∧ s₁ = 2 ∧
          d₁.nmem = upd c₁.nmem (ITb + i) 0 ∧ (∀ x, x ≠ 5166 → d₁.nreg x = c₁.nreg x) ∧
          d₁.rreg = c₁.rreg ∧ d₁.rmem = c₁.rmem ∧ d₁.output = c₁.output := by
        have k8 : c₁.nreg 5158 = ITb := by rw [k _ (by omega), r8]
        have k63 : c₁.nreg 5163 = i := by rw [k _ (by omega), r63]
        have k62 : c₁.nreg 5162 = 0 := by rw [k _ (by omega), r62]
        exec_block
        all_goals try (config_simp; simp only [k8, k63, k62]; omega)
        refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
        · config_simp; simp only [k8, k63, k62]
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      refine ⟨d₁, s₁ + 2, .ifLtN_false hnlt x₁, by omega, by rw [um, iteF hF], fun x hx => un x
        (by omega), ur, urm, uo⟩
  have hw₂ := e₂.wb_right
  have h63 : c₂.nreg 5163 = i := by rw [bn₂ _ (by omega), k _ (by omega), r63]
  have h61 : c₂.nreg 5161 = 1 := by rw [bn₂ _ (by omega), k _ (by omega), r61]
  obtain ⟨c₃, t₃, e₃, ht₃, d63, dn₃, dm₃, dr₃, drm₃, do₃⟩ : ∃ c₃ t₃,
      Exec P W (block [.addN 5163 5163 5161]) c₂ c₃ t₃ ∧ t₃ = 1 ∧ c₃.nreg 5163 = i + 1 ∧
      (∀ x, x ≠ 5163 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try (config_simp; simp only [h63, h61]; omega)
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [h63, h61]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, d63, by rw [dm₃, bm₂, am₁],
    fun x hx => ?_, by rw [dr₃, br₂, ar₁], by rw [drm₃, brm₂, arm₁], by rw [do₃, bo₂, ao₁]⟩
  rw [dn₃ _ (by omega), bn₂ _ (by omega), k _ (by omega)]

/-- **The new-hole flags and the labels**: with the read arrays `NF`, `TK`, `RV` below `ITb`,
`ITb + n ≤ NHb`, the arrays `KM`, `RK`, `ZF` above `NHb + n`, the keys and reverses `< n`, the
ranks `< m` on the flagged indices, within `66 n + 5` steps: `NH[i] = KM[TK[i]]` and
`IT[i] = lbV …` (flagged) or `0`; memory off the two output ranges, registers outside
`5161 … 5182`, reals and output kept. -/
theorem lbl_exec (c : Config) (hc : WordsBounded W c)
    {n m NFb TKb KMb RKb ZFb RVb NHb ITb z one : ℕ}
    (r0 : c.nreg 5150 = n) (r1 : c.nreg 5151 = NFb) (r2 : c.nreg 5152 = TKb)
    (r3 : c.nreg 5153 = KMb) (r4 : c.nreg 5154 = RKb) (r5 : c.nreg 5155 = ZFb)
    (r6 : c.nreg 5156 = RVb) (r7 : c.nreg 5157 = NHb) (r8 : c.nreg 5158 = ITb)
    (r9 : c.nreg 5159 = z) (r60 : c.nreg 5160 = one)
    (lay : NFb + n ≤ ITb ∧ TKb + n ≤ ITb ∧ RVb + n ≤ ITb ∧ ITb + n ≤ NHb ∧ NHb + n ≤ KMb ∧
      NHb + n ≤ RKb ∧ NHb + n ≤ ZFb ∧ KMb + n ≤ W ∧ RKb + n ≤ W ∧ ZFb + m ≤ W ∧ n + 3 ≤ W)
    (htk : ∀ i < n, c.nmem (TKb + i) < n) (hrv : ∀ i < n, c.nmem (RVb + i) < n)
    (hrk : ∀ i < n, c.nmem (NFb + i) ≠ 0 →
      c.nmem (RKb + i) < m ∧ c.nmem (RKb + c.nmem (RVb + i)) < m) :
    ∃ c' t, Exec P W lbl c c' t ∧ t ≤ 66 * n + 5 ∧
      (∀ i < n, c'.nmem (NHb + i) = c.nmem (KMb + c.nmem (TKb + i))) ∧
      (∀ i < n, c'.nmem (ITb + i) = if c.nmem (NFb + i) ≠ 0 then
          lbV (c.nmem (KMb + c.nmem (TKb + i))) (c.nmem (ZFb + c.nmem (RKb + i)))
            (c.nmem (KMb + c.nmem (TKb + c.nmem (RVb + i))))
            (c.nmem (ZFb + c.nmem (RKb + c.nmem (RVb + i)))) z one
        else 0) ∧
      (∀ a, ¬ (ITb ≤ a ∧ a < ITb + n) → ¬ (NHb ≤ a ∧ a < NHb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5161 ∨ 5182 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := lay
  unfold lbl
  obtain ⟨c₁, k₁, e₁, hk₁, g1, g2, g3, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 5161 1, .constN 5162 0, .constN 5163 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 5161 = 1 ∧ c₁.nreg 5162 = 0 ∧ c₁.nreg 5163 = 0 ∧
      (∀ x, (x < 5161 ∨ 5163 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 5161 ∨ 5163 < x) → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 5163 ∨ 5182 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (NHb + j) = m₀ (KMb + m₀ (TKb + j))) ∧
    (∀ j < i, c'.nmem (ITb + j) = if m₀ (NFb + j) ≠ 0 then
          lbV (m₀ (KMb + m₀ (TKb + j))) (m₀ (ZFb + m₀ (RKb + j)))
            (m₀ (KMb + m₀ (TKb + m₀ (RVb + j))))
            (m₀ (ZFb + m₀ (RKb + m₀ (RVb + j)))) z one
        else 0) ∧
    (∀ a, ¬ (ITb ≤ a ∧ a < ITb + n) → ¬ (NHb ≤ a ∧ a < NHb + n) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h63, j1, j2, j3, j4, j5, j6, j7⟩ := tgRange (P := P)
    (a := 5163) (b := 5150) (body := lbBody) J (B := 64) c₁ hw₁ g3
    (by rw [q _ (by omega), r0]) (Nat.zero_le n)
    ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun a _ _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h63 h50 ⟨j1, j2, j3, j4, j5, j6, j7⟩ => by
      have f : ∀ x, (x < 5163 ∨ 5182 < x) → c'.nreg x = c₁.nreg x := j1
      have g : ∀ a, (a < ITb ∨ NHb + n ≤ a) → c'.nmem a = m₀ a := fun a ha =>
        j4 a (by omega) (by omega)
      have ht := htk i hhi
      have hr := hrv i hhi
      have ht' := htk _ hr
      have eT : c'.nmem (TKb + i) = m₀ (TKb + i) := g _ (by omega)
      have eK : c'.nmem (KMb + m₀ (TKb + i)) = m₀ (KMb + m₀ (TKb + i)) := g _ (by omega)
      have eF : c'.nmem (NFb + i) = m₀ (NFb + i) := g _ (by omega)
      have eR : c'.nmem (RVb + i) = m₀ (RVb + i) := g _ (by omega)
      have eT2 : c'.nmem (TKb + m₀ (RVb + i)) = m₀ (TKb + m₀ (RVb + i)) := g _ (by omega)
      have eK2 : c'.nmem (KMb + m₀ (TKb + m₀ (RVb + i))) = m₀ (KMb + m₀ (TKb + m₀ (RVb + i))) :=
        g _ (by omega)
      have eRK : c'.nmem (RKb + i) = m₀ (RKb + i) := g _ (by omega)
      have eRK2 : c'.nmem (RKb + m₀ (RVb + i)) = m₀ (RKb + m₀ (RVb + i)) := g _ (by omega)
      obtain ⟨c'', t, ex, ht'', h63', hm', hn', hr', hrm', ho'⟩ :=
        lbBody_exec (P := P) c' hw (NFb := NFb) (TKb := TKb) (KMb := KMb) (RKb := RKb)
          (ZFb := ZFb) (RVb := RVb) (NHb := NHb) (ITb := ITb) (z := z) (one := one) (i := i)
          (by rw [f _ (by omega), q _ (by omega), r1]) (by rw [f _ (by omega), q _ (by omega), r2])
          (by rw [f _ (by omega), q _ (by omega), r3]) (by rw [f _ (by omega), q _ (by omega), r4])
          (by rw [f _ (by omega), q _ (by omega), r5]) (by rw [f _ (by omega), q _ (by omega), r6])
          (by rw [f _ (by omega), q _ (by omega), r7]) (by rw [f _ (by omega), q _ (by omega), r8])
          (by rw [f _ (by omega), q _ (by omega), r9]) (by rw [f _ (by omega), q _ (by omega), r60])
          (by rw [f _ (by omega), g1]) (by rw [f _ (by omega), g2]) h63
          (by omega) (by rw [eT]; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (fun hF => by
            rw [eF] at hF
            obtain ⟨k1, k2⟩ := hrk i hhi hF
            simp only [eRK, eR, eT2, eK2, eRK2]
            exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
          (fun a ha => by
            rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      have hNHv : c'.nmem (KMb + c'.nmem (TKb + i)) = m₀ (KMb + m₀ (TKb + i)) := by rw [eT, eK]
      have hITv : (if c'.nmem (NFb + i) ≠ 0 then
          lbV (c'.nmem (KMb + c'.nmem (TKb + i))) (c'.nmem (ZFb + c'.nmem (RKb + i)))
            (c'.nmem (KMb + c'.nmem (TKb + c'.nmem (RVb + i))))
            (c'.nmem (ZFb + c'.nmem (RKb + c'.nmem (RVb + i)))) z one else 0) =
          (if m₀ (NFb + i) ≠ 0 then
          lbV (m₀ (KMb + m₀ (TKb + i))) (m₀ (ZFb + m₀ (RKb + i)))
            (m₀ (KMb + m₀ (TKb + m₀ (RVb + i))))
            (m₀ (ZFb + m₀ (RKb + m₀ (RVb + i)))) z one else 0) := by
        rw [eF]
        split_ifs with hF
        · have eZ : c'.nmem (ZFb + m₀ (RKb + i)) = m₀ (ZFb + m₀ (RKb + i)) := g _ (by omega)
          have eZ2 : c'.nmem (ZFb + m₀ (RKb + m₀ (RVb + i))) = m₀ (ZFb + m₀ (RKb + m₀ (RVb + i))) :=
            g _ (by omega)
          simp only [eT, eK, eRK, eZ, eR, eT2, eK2, eRK2, eZ2]
        · rfl
      rw [hITv, hNHv] at hm'
      refine ⟨c'', t, ex, ht'', h63', by rw [hn' _ (by omega)]; exact h50,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun j hj => ?_, fun a ha ha' => ?_,
        by rw [hr', j5], by rw [hrm', j6], by rw [ho', j7]⟩
      · rw [hm', upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same]
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact j3 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact j4 a ha ha')
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, j4,
    fun x hx => by rw [j1 x (by omega), q x (by omega)], by rw [j5, gr₁], by rw [j6, grm₁],
    by rw [j7, go₁]⟩

end Lb

end BKMNW

end PlanarFlow
