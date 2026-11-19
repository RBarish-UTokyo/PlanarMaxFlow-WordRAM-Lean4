module

public import PlanarFlow.BKMNW.StCall

/-!
# The s-t flow call with its encoders at fixed low addresses

The encoders of `stCall` work at the caller's addresses, so two calls with the same capacities and
terminals but different addresses need not make the same choices (trees). **`stCallZ`** makes
the encoder run a function of the input words alone:

* `stIn`: the five frame arrays are copied to the fixed low addresses `A₀ + j m`
  (`A₀ = 202 m + 92`, in the zero memory), the address registers `9101 … 9106` are set to these
  addresses and to the scratch base `S₀ = 207 m + 92`, and every other register of `uE` (the
  registers the encoders may read or write, `stE_regsOK`) is zeroed;
* `stE = stPro ; stA ; stB ; stC` (the encoders, unchanged) then starts from a configuration that
  agrees with the **canonical configuration** `stCan m arr` (the arrays `arr` at `A₀`, zero
  elsewhere) on `uE` and on the memory `≤ Wz` (`stIn_exec`);
* `stClr` zeroes `[A₀, A₀ + 137 m + 36)` (arrays and scratch) after the image is copied to `ib`;
* `stCallZ = stIn ; stE ; stD1 ; stClr ; stD2 ; stD3`.

`stE_regsOK`, `stE_noRand`, `stE_natOnly` (by `decide +kernel`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace StCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP StEnc

variable {P : Input} {W : ℕ}

/-- **The registers of the encoders**: `StScr` without the inputs `9107 … 9110` (`ib`, `Ob`, `Z`,
`p`), which the encoders never read. -/
def uE (r : ℕ) : Bool :=
  decide (r < 2600) || decide (2900 ≤ r ∧ r < 2930) || decide (4900 ≤ r ∧ r < 4920) ||
  decide (5030 ≤ r ∧ r < 5036) || decide (6210 ≤ r ∧ r < 6218) || decide (7350 ≤ r ∧ r < 7410) ||
  decide (7700 ≤ r ∧ r < 8012) || decide (9100 ≤ r ∧ r < 9107) || decide (9111 ≤ r ∧ r < 9200)

lemma uE_iff (r : ℕ) : uE r = true ↔ (r < 2600 ∨ (2900 ≤ r ∧ r < 2930) ∨ (4900 ≤ r ∧ r < 4920) ∨
    (5030 ≤ r ∧ r < 5036) ∨ (6210 ≤ r ∧ r < 6218) ∨ (7350 ≤ r ∧ r < 7410) ∨
    (7700 ≤ r ∧ r < 8012) ∨ (9100 ≤ r ∧ r < 9107) ∨ (9111 ≤ r ∧ r < 9200)) := by
  simp only [uE, Bool.or_eq_true, decide_eq_true_eq, or_assoc]

/-- **The encoders.** -/
def stE : Stmt := .seq stPro (.seq stA (.seq stB stC))

set_option maxRecDepth 100000 in
theorem stE_regsOK : stE.regsOK uE = true := by decide +kernel

theorem stE_noRand : stE.noRand = true := by decide +kernel

theorem stE_natOnly : Klein.natOnly stE = true := by decide +kernel

/-- The canonical configuration of the encoders: `m`, the array bases `A₀ + j m`, the scratch base
`S₀ = 207 m + 92`, the arrays `arr` at `A₀ = 202 m + 92`, zero elsewhere. -/
def stCan (m : ℕ) (arr : ℕ → ℕ) : Config where
  pc := 0
  nreg := fun r => if r = 9100 then m else if r = 9101 then 202 * m + 92
    else if r = 9102 then 203 * m + 92 else if r = 9103 then 204 * m + 92
    else if r = 9104 then 205 * m + 92 else if r = 9105 then 206 * m + 92
    else if r = 9106 then 207 * m + 92 else 0
  rreg := fun _ => 0
  nmem := fun a => if 202 * m + 92 ≤ a ∧ a < 207 * m + 92 then arr (a - (202 * m + 92)) else 0
  rmem := fun _ => 0
  output := []

/-- The array bases. -/
def stInL : List (List (ℕ × hpM) × ℕ) :=
  [([(202, hpM.v 9100), (92, hpM.one)], 0), ([(203, hpM.v 9100), (92, hpM.one)], 0),
    ([(204, hpM.v 9100), (92, hpM.one)], 0), ([(205, hpM.v 9100), (92, hpM.one)], 0),
    ([(206, hpM.v 9100), (92, hpM.one)], 0), ([(207, hpM.v 9100), (92, hpM.one)], 0)]

theorem stInL_shape : hpShape 9100 9101 207 0 stInL = true := by decide

/-- The registers zeroed by `stIn`: `uE` without `9100 … 9106`. -/
def zl : List ℕ :=
  List.range 2600 ++ List.range' 2900 30 ++ List.range' 4900 20 ++ List.range' 5030 6 ++
    List.range' 6210 8 ++ List.range' 7350 60 ++ List.range' 7700 312 ++ List.range' 9111 89

lemma mem_zl (r : ℕ) : r ∈ zl ↔ (uE r = true ∧ (r < 9100 ∨ 9106 < r)) := by
  rw [uE_iff]
  simp only [zl, List.mem_append, List.mem_range, List.mem_range'_1]
  omega

lemma zl_length : zl.length = 3125 := by simp [zl]

/-- One array copy: `D := A₀ + j m` from the caller's base in `r(9101 + j)`. -/
def stCp (j : ℕ) : Stmt := .seq (cpL [(4910, 9100), (4911, 9101 + j), (4912, 9192 + j)]) cpArr

/-- **The arrays at the fixed low addresses, the encoders' registers canonical.** -/
def stIn : Stmt :=
  .seq (hpProg 9192 9198 stInL) <| .seq (stCp 0) <| .seq (stCp 1) <| .seq (stCp 2) <|
  .seq (stCp 3) <| .seq (stCp 4) <|
  .seq (cpL [(9101, 9192), (9102, 9193), (9103, 9194), (9104, 9195), (9105, 9196),
    (9106, 9197)]) (mbZeroRegs zl)

/-- The clearing of the arrays and the scratch. -/
def stClrL : List (List (ℕ × hpM) × ℕ) :=
  [([(137, hpM.v 9100), (36, hpM.one)], 0), ([(202, hpM.v 9100), (92, hpM.one)], 0)]

theorem stClrL_shape : hpShape 9100 9101 202 0 stClrL = true := by decide

/-- **Zero `[A₀, A₀ + 137 m + 36)`.** -/
def stClr : Stmt := .seq (hpProg 5030 9198 stClrL) mzFill

/-- **One in-place call of the s-t flow program with its encoders at fixed low addresses.** -/
def stCallZ : Stmt :=
  .seq stIn (.seq stE (.seq stD1 (.seq stClr (.seq stD2 stD3))))

/-- The cost of `stIn`. -/
def costIn (m : ℕ) : ℕ := hpCost stInL + 5 * (7 * m + 7) + 6 + 3125

/-- One array copy. -/
theorem stCp_exec (j : ℕ) (hj : j < 5) (c : Config) (hc : WordsBounded W c) {m S D : ℕ}
    (h0 : c.nreg 9100 = m) (hS : c.nreg (9101 + j) = S) (hD : c.nreg (9192 + j) = D)
    (lay : (S + m ≤ D ∨ D + m ≤ S) ∧ S + m ≤ W ∧ D + m ≤ W ∧ m + 1 ≤ W) :
    ∃ c' t, Exec P W (stCp j) c c' t ∧ t ≤ 7 * m + 7 ∧
      (∀ i < m, c'.nmem (D + i) = c.nmem (S + i)) ∧
      (∀ a, (a < D ∨ D + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4910 ∨ 4916 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, e₁, v₁, f₁, m₁, r₁, rm₁, o₁⟩ := cpL_exec (P := P)
    [(4910, 9100), (4911, 9101 + j), (4912, 9192 + j)] (by simp; omega) (by simp) c hc
  obtain ⟨c₂, t₂, e₂, ht₂, cp, kp, rg, rr, rm, o⟩ := cpArr_exec (P := P) c₁ e₁.wb_right
    (n := m) (Sb := S) (Db := D) (by rw [v₁ (4910, 9100) (by simp), h0])
    (by rw [v₁ (4911, 9101 + j) (by simp), hS]) (by rw [v₁ (4912, 9192 + j) (by simp), hD]) lay
  refine ⟨c₂, _, e₁.seq e₂, by simp only [List.length_cons, List.length_nil]; omega,
    fun i hi => by rw [cp i hi, m₁],
    fun a ha => by rw [kp a ha, m₁], fun x hx => ?_, by rw [rr, r₁], by rw [rm, rm₁],
    by rw [o, o₁]⟩
  rw [rg x (by omega), f₁ x (by simp; omega)]

set_option maxHeartbeats 1600000 in
/-- **The arrays at the fixed low addresses** (see the module docstring): after `stIn` the
registers of `uE` and the memory `≤ Wz` are those of `stCan m arr`; other registers and the memory
above `Wz` kept. -/
theorem stIn_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb Cb Xb Yb Wz : ℕ}
    {arr : ℕ → ℕ} (r00 : c.nreg 9100 = m) (r01 : c.nreg 9101 = RVb) (r02 : c.nreg 9102 = RTb)
    (r03 : c.nreg 9103 = Cb) (r04 : c.nreg 9104 = Xb) (r05 : c.nreg 9105 = Yb)
    (a0 : ∀ i < m, c.nmem (RVb + i) = arr i) (a1 : ∀ i < m, c.nmem (RTb + i) = arr (m + i))
    (a2 : ∀ i < m, c.nmem (Cb + i) = arr (2 * m + i))
    (a3 : ∀ i < m, c.nmem (Xb + i) = arr (3 * m + i))
    (a4 : ∀ i < m, c.nmem (Yb + i) = arr (4 * m + i))
    (hz : ∀ a ≤ Wz, c.nmem a = 0) (oR : Wz < RVb) (oT : Wz < RTb) (oC : Wz < Cb) (oX : Wz < Xb)
    (oY : Wz < Yb) (wR : RVb + m ≤ W) (wT : RTb + m ≤ W) (wC : Cb + m ≤ W) (wX : Xb + m ≤ W)
    (wY : Yb + m ≤ W) (hA : 207 * m + 92 ≤ Wz) (hWz : Wz ≤ W) (hm : 0 < m) :
    ∃ c' t, Exec P W stIn c c' t ∧ t ≤ costIn m ∧
      (∀ r, uE r = true → c'.nreg r = (stCan m arr).nreg r) ∧
      (∀ a ≤ Wz, c'.nmem a = (stCan m arr).nmem a) ∧
      (∀ r, uE r = false → c'.nreg r = c.nreg r) ∧
      (∀ a, Wz < a → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 9192 9198 stInL :=
    hpShape_ok stInL_shape (by omega) (by omega) (by simp [stInL]) (by omega) (by simp [stInL])
  obtain ⟨c₁, e₁, v₁, f₁, m₁, r₁, rm₁, o₁⟩ := hpProg_exec (I := P) stInL 9192 hok c hc
    (fun e he => by
      simp only [stInL, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with h | h | h | h | h | h <;> subst h <;>
        simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          r00] <;> omega)
  have b : ∀ j < 6, c₁.nreg (9192 + j) = (202 + j) * m + 92 := fun j hj => by
    rw [v₁ j (by simp [stInL]; omega)]
    interval_cases j <;> simp only [stInL, hpSum, hpM.ev, List.getD_cons_succ,
      List.getD_cons_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r00] <;> omega
  have k₁ : ∀ r, (r < 9192 ∨ 9199 < r) → c₁.nreg r = c.nreg r := fun r hr =>
    f₁ r (by simp [stInL]; omega) (by omega) (by omega)
  -- the five copies
  obtain ⟨c₂, t₂, e₂, ht₂, P₂, K₂, R₂, rr₂, rm₂, o₂⟩ := stCp_exec (P := P) 0 (by omega) c₁
    e₁.wb_right (S := RVb) (D := 202 * m + 92) (by rw [k₁ _ (by omega), r00])
    (by rw [k₁ _ (by omega), r01]) (by rw [b 0 (by omega)])
    ⟨Or.inr (by omega), wR, by omega, by omega⟩
  have k₂ : ∀ r, (r < 4910 ∨ 4916 < r) → (r < 9192 ∨ 9199 < r) → c₂.nreg r = c.nreg r :=
    fun r h1 h2 => by rw [R₂ r h1, k₁ r h2]
  obtain ⟨c₃, t₃, e₃, ht₃, P₃, K₃, R₃, rr₃, rm₃, o₃⟩ := stCp_exec (P := P) 1 (by omega) c₂
    e₂.wb_right (S := RTb) (D := 203 * m + 92) (by rw [k₂ _ (by omega) (by omega), r00])
    (by rw [k₂ _ (by omega) (by omega), r02]) (by rw [R₂ _ (by omega), b 1 (by omega)])
    ⟨Or.inr (by omega), wT, by omega, by omega⟩
  have k₃ : ∀ r, (r < 4910 ∨ 4916 < r) → (r < 9192 ∨ 9199 < r) → c₃.nreg r = c.nreg r :=
    fun r h1 h2 => by rw [R₃ r h1, k₂ r h1 h2]
  obtain ⟨c₄, t₄, e₄, ht₄, P₄, K₄, R₄, rr₄, rm₄, o₄⟩ := stCp_exec (P := P) 2 (by omega) c₃
    e₃.wb_right (S := Cb) (D := 204 * m + 92) (by rw [k₃ _ (by omega) (by omega), r00])
    (by rw [k₃ _ (by omega) (by omega), r03])
    (by rw [R₃ _ (by omega), R₂ _ (by omega), b 2 (by omega)])
    ⟨Or.inr (by omega), wC, by omega, by omega⟩
  have k₄ : ∀ r, (r < 4910 ∨ 4916 < r) → (r < 9192 ∨ 9199 < r) → c₄.nreg r = c.nreg r :=
    fun r h1 h2 => by rw [R₄ r h1, k₃ r h1 h2]
  obtain ⟨c₅, t₅, e₅, ht₅, P₅, K₅, R₅, rr₅, rm₅, o₅⟩ := stCp_exec (P := P) 3 (by omega) c₄
    e₄.wb_right (S := Xb) (D := 205 * m + 92) (by rw [k₄ _ (by omega) (by omega), r00])
    (by rw [k₄ _ (by omega) (by omega), r04])
    (by rw [R₄ _ (by omega), R₃ _ (by omega), R₂ _ (by omega), b 3 (by omega)])
    ⟨Or.inr (by omega), wX, by omega, by omega⟩
  have k₅ : ∀ r, (r < 4910 ∨ 4916 < r) → (r < 9192 ∨ 9199 < r) → c₅.nreg r = c.nreg r :=
    fun r h1 h2 => by rw [R₅ r h1, k₄ r h1 h2]
  obtain ⟨c₆, t₆, e₆, ht₆, P₆, K₆, R₆, rr₆, rm₆, o₆⟩ := stCp_exec (P := P) 4 (by omega) c₅
    e₅.wb_right (S := Yb) (D := 206 * m + 92) (by rw [k₅ _ (by omega) (by omega), r00])
    (by rw [k₅ _ (by omega) (by omega), r05])
    (by
      rw [R₅ _ (by omega), R₄ _ (by omega), R₃ _ (by omega), R₂ _ (by omega), b 4 (by omega)])
    ⟨Or.inr (by omega), wY, by omega, by omega⟩
  have k₆ : ∀ r, (r < 4910 ∨ 4916 < r) → c₆.nreg r = c₁.nreg r := fun r h1 => by
    rw [R₆ r h1, R₅ r h1, R₄ r h1, R₃ r h1, R₂ r h1]
  -- the address registers
  obtain ⟨c₇, e₇, v₇, f₇, m₇, r₇, rm₇, o₇⟩ := cpL_exec (P := P)
    [(9101, 9192), (9102, 9193), (9103, 9194), (9104, 9195), (9105, 9196), (9106, 9197)]
    (by decide) (by decide) c₆ e₆.wb_right
  -- the zeroing
  obtain ⟨c₈, e₈, Z₈, K₈, m₈, rr₈, rm₈, o₈⟩ := mbZeroRegs_exec' (P := P) zl c₇ e₇.wb_right
  -- the memory after the copies
  have hmem : ∀ a, c₆.nmem a = if 202 * m + 92 ≤ a ∧ a < 207 * m + 92 then
      arr (a - (202 * m + 92)) else c.nmem a := fun a => by
    split_ifs with ha
    · by_cases j0 : a < 203 * m + 92
      · rw [K₆ a (Or.inl (by omega)), K₅ a (Or.inl (by omega)), K₄ a (Or.inl (by omega)),
          K₃ a (Or.inl (by omega))]
        have := P₂ (a - (202 * m + 92)) (by omega)
        rw [show 202 * m + 92 + (a - (202 * m + 92)) = a by omega] at this
        rw [this, m₁, a0 _ (by omega)]
      by_cases j1 : a < 204 * m + 92
      · rw [K₆ a (Or.inl (by omega)), K₅ a (Or.inl (by omega)), K₄ a (Or.inl (by omega))]
        have := P₃ (a - (203 * m + 92)) (by omega)
        rw [show 203 * m + 92 + (a - (203 * m + 92)) = a by omega] at this
        rw [this, K₂ _ (Or.inr (by omega)), m₁, a1 _ (by omega)]
        congr 1; omega
      by_cases j2 : a < 205 * m + 92
      · rw [K₆ a (Or.inl (by omega)), K₅ a (Or.inl (by omega))]
        have := P₄ (a - (204 * m + 92)) (by omega)
        rw [show 204 * m + 92 + (a - (204 * m + 92)) = a by omega] at this
        rw [this, K₃ _ (Or.inr (by omega)), K₂ _ (Or.inr (by omega)), m₁, a2 _ (by omega)]
        congr 1; omega
      by_cases j3 : a < 206 * m + 92
      · rw [K₆ a (Or.inl (by omega))]
        have := P₅ (a - (205 * m + 92)) (by omega)
        rw [show 205 * m + 92 + (a - (205 * m + 92)) = a by omega] at this
        rw [this, K₄ _ (Or.inr (by omega)), K₃ _ (Or.inr (by omega)), K₂ _ (Or.inr (by omega)), m₁,
          a3 _ (by omega)]
        congr 1; omega
      · have := P₆ (a - (206 * m + 92)) (by omega)
        rw [show 206 * m + 92 + (a - (206 * m + 92)) = a by omega] at this
        rw [this, K₅ _ (Or.inr (by omega)), K₄ _ (Or.inr (by omega)), K₃ _ (Or.inr (by omega)),
          K₂ _ (Or.inr (by omega)), m₁, a4 _ (by omega)]
        congr 1; omega
    · rw [K₆ a (by omega), K₅ a (by omega), K₄ a (by omega), K₃ a (by omega), K₂ a (by omega), m₁]
  refine ⟨c₈, _, e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq (e₆.seq (e₇.seq e₈)))))), ?_,
    fun r hr => ?_, fun a ha => ?_, fun r hr => ?_, fun a ha => ?_,
    by rw [rr₈, r₇, rr₆, rr₅, rr₄, rr₃, rr₂, r₁], by rw [rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · simp only [costIn, zl_length, List.length_cons, List.length_nil]
    omega
  · by_cases hz' : r ∈ zl
    · rw [Z₈ r hz']
      rw [mem_zl] at hz'
      simp only [stCan]
      split_ifs <;> omega
    · have hr' : 9100 ≤ r ∧ r ≤ 9106 := by
        rw [mem_zl] at hz'; push Not at hz'; have := hz' hr; omega
      rw [K₈ r hz']
      simp only [stCan]
      rcases (show r = 9100 ∨ r = 9101 ∨ r = 9102 ∨ r = 9103 ∨ r = 9104 ∨ r = 9105 ∨ r = 9106 by
        omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [f₇ _ (by simp), k₆ _ (by omega), k₁ _ (by omega), r00]; simp
      · rw [v₇ (9101, 9192) (by simp), k₆ _ (by omega), b 0 (by omega)]; simp
      · rw [v₇ (9102, 9193) (by simp), k₆ _ (by omega), b 1 (by omega)]; simp
      · rw [v₇ (9103, 9194) (by simp), k₆ _ (by omega), b 2 (by omega)]; simp
      · rw [v₇ (9104, 9195) (by simp), k₆ _ (by omega), b 3 (by omega)]; simp
      · rw [v₇ (9105, 9196) (by simp), k₆ _ (by omega), b 4 (by omega)]; simp
      · rw [v₇ (9106, 9197) (by simp), k₆ _ (by omega), b 5 (by omega)]; simp
  · rw [m₈, m₇, hmem a]
    simp only [stCan]
    split_ifs with h1
    · rfl
    · exact hz a ha
  · have hz' : r ∉ zl := by rw [mem_zl]; simp [hr]
    have h1 : ¬ uE r = true := by simp [hr]
    rw [uE_iff] at h1
    rw [K₈ r hz', f₇ r (by simp; omega), k₆ r (by omega), k₁ r (by omega)]
  · rw [m₈, m₇, hmem a]
    split_ifs with h1
    · omega
    · rfl

/-- **Zeroing the arrays and the scratch.** -/
theorem stClr_exec (c : Config) (hc : WordsBounded W c) {m : ℕ} (h0 : c.nreg 9100 = m)
    (hW : 339 * m + 128 ≤ W) (hm : 0 < m) :
    ∃ c' t, Exec P W stClr c c' t ∧ t ≤ hpCost stClrL + 5 * (137 * m + 36) + 5 ∧
      (∀ i < 137 * m + 36, c'.nmem (202 * m + 92 + i) = 0) ∧
      (∀ a, (a < 202 * m + 92 ∨ 339 * m + 128 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 5030 ∨ 5035 < r) → r ≠ 9198 → r ≠ 9199 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 5030 9198 stClrL :=
    hpShape_ok stClrL_shape (by omega) (by omega) (by simp [stClrL]) (by omega) (by simp [stClrL])
  obtain ⟨c₁, e₁, v₁, f₁, m₁, r₁, rm₁, o₁⟩ := hpProg_exec (I := P) stClrL 5030 hok c hc
    (fun e he => by
      simp only [stClrL, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with h | h <;> subst h <;>
        simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          h0] <;> omega)
  have b0 : c₁.nreg 5030 = 137 * m + 36 := by
    rw [show (5030 : ℕ) = 5030 + 0 from rfl, v₁ 0 (by simp [stClrL])]
    simp only [stClrL, hpSum, hpM.ev, List.getD_cons_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, h0]; omega
  have b1 : c₁.nreg 5031 = 202 * m + 92 := by
    rw [show (5031 : ℕ) = 5030 + 1 from rfl, v₁ 1 (by simp [stClrL])]
    simp only [stClrL, hpSum, hpM.ev, List.getD_cons_succ, List.getD_cons_zero, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, h0]; omega
  obtain ⟨c₂, t₂, e₂, ht₂, Z₂, K₂, R₂, rr₂, rm₂, o₂⟩ := mzFill_exec (P := P) c₁ e₁.wb_right b0 b1
    (by omega) (by omega)
  refine ⟨c₂, _, e₁.seq e₂, by omega, Z₂, fun a ha => by rw [K₂ a (by omega), m₁],
    fun r h1 h2 h3 => ?_, by rw [rr₂, r₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
  rw [R₂ r (by omega), f₁ r (by simp [stClrL]; omega) h2 h3]

end StCall

end BKMNW

end PlanarFlow
