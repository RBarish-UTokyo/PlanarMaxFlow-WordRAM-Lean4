module

public import PlanarFlow.BKMNW.NrPch

/-!
# Small loops of the push-back steps `retP`, `frmP`

Registers `9287 … 9297`:

* **`frL`** (`OUT[i] := [X[i] = k]`, branch-free `1 - ((X[i] - k) + (k - X[i]))`; `9288 = n`,
  `9289 = Xb`, `9290 = OUTb`, `9291 = k`), `frL_exec` (`11 n + 4`);
* **`btL`** (`OUT[i] := A[i] - P[i] · (A[i] - Kd)`, i.e. `Kd` where the flag `P[i] = 1` and
  `A[i] > Kd`, else `A[i]`; `9288 = n`, `9289 = Ab`, `9290 = Pb`, `9291 = OUTb`, `9293 = Kd`),
  `btL_exec` (`12 n + 4`);
* **`mkL`** (the marks `MK[VL[RV[D[l]]]] := 1` for `l < k`; `9288 = k`, `9289 = Db`, `9290 = RVb`,
  `9291 = VLb`, `9292 = MKb`), `mkL_exec` (`11 k + 4`): from `MK = [v = v₀]` on `[0, m)`,
  `MK[v] = mkv v₀ val k v` (`1` iff `v = v₀` or `v = val l` for some `l < k`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### `frL` -/

/-- The body of `frL`. -/
def frB : Stmt :=
  block [.addN 9293 9289 9287, .loadN 9294 9293, .subN 9295 9294 9291, .subN 9294 9291 9294,
    .addN 9294 9294 9295, .subN 9294 9292 9294, .addN 9293 9290 9287, .storeN 9293 9294,
    .addN 9287 9287 9292]

/-- **`OUT[i] := [X[i] = k]`** for `i < n`. -/
def frL : Stmt := .seq (block [.constN 9292 1, .constN 9287 0]) (.whileLtN 9287 9288 frB)

/-- The flag `[x = k]`. -/
lemma eqBit (x k : ℕ) : 1 - ((k - x) + (x - k)) = if x = k then 1 else 0 := by
  split_ifs <;> omega

theorem frB_exec (c : Config) (hc : WordsBounded W c) {Xb OUTb k i : ℕ}
    (r9 : c.nreg 9289 = Xb) (r0 : c.nreg 9290 = OUTb) (r1 : c.nreg 9291 = k)
    (r2 : c.nreg 9292 = 1) (r7 : c.nreg 9287 = i) (w1 : Xb + i ≤ W) (w2 : OUTb + i ≤ W)
    (w3 : i + 1 ≤ W) :
    ∃ c' t, Exec P W frB c c' t ∧ t = 9 ∧ c'.nreg 9287 = i + 1 ∧
      (∀ x, x ≠ 9287 → x ≠ 9293 → x ≠ 9294 → x ≠ 9295 → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (OUTb + i) (1 - ((k - c.nmem (Xb + i)) + (c.nmem (Xb + i) - k))) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hk : k ≤ W := by rw [← r1]; exact hc.1 _
  have hx : c.nmem (Xb + i) ≤ W := hc.2 _
  unfold frB
  exec_block
  all_goals try (clear * - r9 r0 r1 r2 r7 w1 w2 w3 hk hx; config_simp; (try simp only [r9, r0, r1, r2, r7]); omega)
  refine ⟨rfl, ?_, fun x h1 h2 h3 h4 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r9, r0, r1, r2, r7]
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

/-- **`frL`**: within `11 n + 4` steps `OUT[i] = [X[i] = k]` for `i < n`. -/
theorem frL_exec (c : Config) (hc : WordsBounded W c) {n Xb OUTb k : ℕ}
    (r8 : c.nreg 9288 = n) (r9 : c.nreg 9289 = Xb) (r0 : c.nreg 9290 = OUTb)
    (r1 : c.nreg 9291 = k) (hd : Xb + n ≤ OUTb ∨ OUTb + n ≤ Xb) (w1 : Xb + n ≤ W)
    (w2 : OUTb + n ≤ W) (w3 : n + 1 ≤ W) :
    ∃ c' t, Exec P W frL c c' t ∧ t ≤ 11 * n + 4 ∧
      (∀ i < n, c'.nmem (OUTb + i) = if c.nmem (Xb + i) = k then 1 else 0) ∧
      (∀ a, (a < OUTb ∨ OUTb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 9287 ∨ 9297 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g2, g7, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    nrInit2_exec (P := P) (r := 9292) (s := 9287) (k := 1) (l := 0) c hc (by omega) (by omega)
      (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, v₂, o₂, f₂, n₂, rr₂, rm₂, oo₂⟩ := nrStore (P := P) (W := W)
    (a := 9287) (b := 9288) (body := frB) (Ob := OUTb) (n := n) (B := 9)
    (fun i => 1 - ((k - c.nmem (Xb + i)) + (c.nmem (Xb + i) - k)))
    (fun x => x ≠ 9287 ∧ x ≠ 9293 ∧ x ≠ 9294 ∧ x ≠ 9295) c₁ e₁.wb_right g7
    (by rw [f₁ _ (by omega) (by omega), r8]) (by omega)
    (fun i c' hi hw h0 hk hm => by
      have e : c'.nmem (Xb + i) = c.nmem (Xb + i) := by
        rw [hm _ (fun j hj => by omega), m₁]
      obtain ⟨c'', k', ex, hk', g0', gk, gm, gr, grm, go⟩ := frB_exec (P := P) c' hw
        (Xb := Xb) (OUTb := OUTb) (k := k)
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r9])
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r0])
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r1])
        (by rw [hk _ (by omega), g2]) h0 (by omega) (by omega) (by omega)
      refine ⟨c'', k', ex, hk'.le, g0', fun x hx => gk x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2, ?_, gr,
        grm, go⟩
      rw [gm, e])
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, fun i hi => by rw [v₂ i hi, eqBit],
    fun a ha => ?_, fun x hx => ?_, by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [oo₂, o₁]⟩
  · rw [o₂ a (fun j hj => by omega), m₁]
  · rw [f₂ x ⟨by omega, by omega, by omega, by omega⟩, f₁ x (by omega) (by omega)]

/-! ### `btL` -/

/-- The body of `btL`. -/
def btB : Stmt :=
  block [.addN 9294 9289 9287, .loadN 9295 9294, .addN 9294 9290 9287, .loadN 9296 9294,
    .subN 9297 9295 9293, .mulN 9297 9296 9297, .subN 9295 9295 9297, .addN 9294 9291 9287,
    .storeN 9294 9295, .addN 9287 9287 9292]

/-- **`OUT[i] := A[i] - P[i] · (A[i] - Kd)`** for `i < n`. -/
def btL : Stmt := .seq (block [.constN 9292 1, .constN 9287 0]) (.whileLtN 9287 9288 btB)

theorem btB_exec (c : Config) (hc : WordsBounded W c) {Ab Pb OUTb Kd i : ℕ}
    (r9 : c.nreg 9289 = Ab) (r0 : c.nreg 9290 = Pb) (r1 : c.nreg 9291 = OUTb)
    (r2 : c.nreg 9292 = 1) (r3 : c.nreg 9293 = Kd) (r7 : c.nreg 9287 = i) (w1 : Ab + i ≤ W)
    (w2 : Pb + i ≤ W) (w3 : OUTb + i ≤ W) (w4 : i + 1 ≤ W) (hp : c.nmem (Pb + i) ≤ 1) :
    ∃ c' t, Exec P W btB c c' t ∧ t = 10 ∧ c'.nreg 9287 = i + 1 ∧
      (∀ x, x ≠ 9287 → x ≠ 9294 → x ≠ 9295 → x ≠ 9296 → x ≠ 9297 → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (OUTb + i)
        (c.nmem (Ab + i) - c.nmem (Pb + i) * (c.nmem (Ab + i) - Kd)) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ha : c.nmem (Ab + i) ≤ W := hc.2 _
  have hmul : c.nmem (Pb + i) * (c.nmem (Ab + i) - Kd) ≤ c.nmem (Ab + i) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hp with h | h <;> rw [h] <;> omega
  unfold btB
  exec_block
  all_goals try (clear * - r9 r0 r1 r2 r3 r7 w1 w2 w3 w4 ha hmul; config_simp; (try simp only [r9, r0, r1, r2, r3, r7]); omega)
  refine ⟨rfl, ?_, fun x h1 h2 h3 h4 h5 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r9, r0, r1, r2, r3, r7]
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

/-- **`btL`**: within `12 n + 4` steps `OUT[i] = A[i] - P[i] · (A[i] - Kd)` for `i < n`
(flags `P[i] ≤ 1`). -/
theorem btL_exec (c : Config) (hc : WordsBounded W c) {n Ab Pb OUTb Kd : ℕ}
    (r8 : c.nreg 9288 = n) (r9 : c.nreg 9289 = Ab) (r0 : c.nreg 9290 = Pb)
    (r1 : c.nreg 9291 = OUTb) (r3 : c.nreg 9293 = Kd)
    (dA : Ab + n ≤ OUTb ∨ OUTb + n ≤ Ab) (dP : Pb + n ≤ OUTb ∨ OUTb + n ≤ Pb)
    (w1 : Ab + n ≤ W) (w2 : Pb + n ≤ W) (w3 : OUTb + n ≤ W) (w4 : n + 1 ≤ W)
    (hp : ∀ i < n, c.nmem (Pb + i) ≤ 1) :
    ∃ c' t, Exec P W btL c c' t ∧ t ≤ 12 * n + 4 ∧
      (∀ i < n, c'.nmem (OUTb + i) =
        c.nmem (Ab + i) - c.nmem (Pb + i) * (c.nmem (Ab + i) - Kd)) ∧
      (∀ a, (a < OUTb ∨ OUTb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 9287 ∨ 9297 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g2, g7, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    nrInit2_exec (P := P) (r := 9292) (s := 9287) (k := 1) (l := 0) c hc (by omega) (by omega)
      (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, v₂, o₂, f₂, n₂, rr₂, rm₂, oo₂⟩ := nrStore (P := P) (W := W)
    (a := 9287) (b := 9288) (body := btB) (Ob := OUTb) (n := n) (B := 10)
    (fun i => c.nmem (Ab + i) - c.nmem (Pb + i) * (c.nmem (Ab + i) - Kd))
    (fun x => x ≠ 9287 ∧ x ≠ 9294 ∧ x ≠ 9295 ∧ x ≠ 9296 ∧ x ≠ 9297) c₁ e₁.wb_right g7
    (by rw [f₁ _ (by omega) (by omega), r8]) (by omega)
    (fun i c' hi hw h0 hk hm => by
      have eA : c'.nmem (Ab + i) = c.nmem (Ab + i) := by
        rw [hm _ (fun j hj => by omega), m₁]
      have eP : c'.nmem (Pb + i) = c.nmem (Pb + i) := by
        rw [hm _ (fun j hj => by omega), m₁]
      obtain ⟨c'', k', ex, hk', g0', gk, gm, gr, grm, go⟩ := btB_exec (P := P) c' hw
        (Ab := Ab) (Pb := Pb) (OUTb := OUTb) (Kd := Kd)
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r9])
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r0])
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r1])
        (by rw [hk _ (by omega), g2])
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r3]) h0 (by omega) (by omega)
        (by omega) (by omega) (by rw [eP]; exact hp i hi)
      refine ⟨c'', k', ex, hk'.le, g0', fun x hx => gk x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1
        hx.2.2.2.2, ?_, gr, grm, go⟩
      rw [gm, eA, eP])
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, v₂, fun a ha => ?_, fun x hx => ?_,
    by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [oo₂, o₁]⟩
  · rw [o₂ a (fun j hj => by omega), m₁]
  · rw [f₂ x ⟨by omega, by omega, by omega, by omega, by omega⟩, f₁ x (by omega) (by omega)]

/-! ### `mkL`: the marks -/

/-- The marks after `l` steps: `1` at `v₀` and at `val l'` for `l' < l`. -/
def mkv (v₀ : ℕ) (val : ℕ → ℕ) (l v : ℕ) : ℕ :=
  if v = v₀ ∨ ∃ l' < l, val l' = v then 1 else 0

lemma mkv_succ (v₀ : ℕ) (val : ℕ → ℕ) (l v : ℕ) :
    mkv v₀ val (l + 1) v = if v = val l then 1 else mkv v₀ val l v := by
  unfold mkv
  by_cases h : v = val l
  · subst h; rw [iteT rfl, iteT (Or.inr ⟨l, by omega, rfl⟩)]
  · rw [iteF h]
    congr 1
    apply propext
    constructor
    · rintro (h1 | ⟨l', hl', e⟩)
      · exact Or.inl h1
      · refine Or.inr ⟨l', ?_, e⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with h2 | rfl
        · exact h2
        · exact absurd e.symm h
    · rintro (h1 | ⟨l', hl', e⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨l', by omega, e⟩

/-- The body of `mkL`. -/
def mkB : Stmt :=
  block [.addN 9294 9289 9287, .loadN 9294 9294, .addN 9294 9290 9294, .loadN 9294 9294,
    .addN 9294 9291 9294, .loadN 9294 9294, .addN 9294 9292 9294, .storeN 9294 9293,
    .addN 9287 9287 9293]

/-- **The marks** `MK[VL[RV[D[l]]]] := 1` for `l < k`. -/
def mkL : Stmt := .seq (block [.constN 9293 1, .constN 9287 0]) (.whileLtN 9287 9288 mkB)

theorem mkB_exec (c : Config) (hc : WordsBounded W c) {Db RVb VLb MKb l : ℕ}
    (r9 : c.nreg 9289 = Db) (r0 : c.nreg 9290 = RVb) (r1 : c.nreg 9291 = VLb)
    (r2 : c.nreg 9292 = MKb) (r3 : c.nreg 9293 = 1) (r7 : c.nreg 9287 = l) (w1 : Db + l ≤ W)
    (w2 : RVb + c.nmem (Db + l) ≤ W) (w3 : VLb + c.nmem (RVb + c.nmem (Db + l)) ≤ W)
    (w4 : MKb + c.nmem (VLb + c.nmem (RVb + c.nmem (Db + l))) ≤ W) (w5 : l + 1 ≤ W) :
    ∃ c' t, Exec P W mkB c c' t ∧ t = 9 ∧ c'.nreg 9287 = l + 1 ∧
      (∀ x, x ≠ 9287 → x ≠ 9294 → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (MKb + c.nmem (VLb + c.nmem (RVb + c.nmem (Db + l)))) 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mkB
  exec_block
  all_goals try (clear * - r9 r0 r1 r2 r3 r7 w1 w2 w3 w4 w5; config_simp; (try simp only [r9, r0, r1, r2, r3, r7]); omega)
  refine ⟨rfl, ?_, fun x h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r9, r0, r1, r2, r3, r7]
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

/-- **`mkL`**: within `11 k + 4` steps, from `MK[v] = [v = v₀]` (`v < m`), the marks
`MK[v] = mkv v₀ val k v` for `v < m`, `val l = VL[RV[D[l]]] < m`; memory outside
`[MKb, MKb + m)` kept. -/
theorem mkL_exec (c : Config) (hc : WordsBounded W c) {k m Db RVb VLb MKb v₀ : ℕ}
    (r8 : c.nreg 9288 = k) (r9 : c.nreg 9289 = Db) (r0 : c.nreg 9290 = RVb)
    (r1 : c.nreg 9291 = VLb) (r2 : c.nreg 9292 = MKb)
    (hval : ∀ l < k, c.nmem (VLb + c.nmem (RVb + c.nmem (Db + l))) < m)
    (hD : ∀ l < k, Db + l < MKb ∨ MKb + m ≤ Db + l)
    (hR : ∀ l < k, RVb + c.nmem (Db + l) < MKb ∨ MKb + m ≤ RVb + c.nmem (Db + l))
    (hV : ∀ l < k, VLb + c.nmem (RVb + c.nmem (Db + l)) < MKb ∨
      MKb + m ≤ VLb + c.nmem (RVb + c.nmem (Db + l)))
    (h0 : ∀ v < m, c.nmem (MKb + v) = if v = v₀ then 1 else 0)
    (w1 : Db + k ≤ W) (w2 : ∀ l < k, RVb + c.nmem (Db + l) ≤ W)
    (w3 : ∀ l < k, VLb + c.nmem (RVb + c.nmem (Db + l)) ≤ W) (w4 : MKb + m ≤ W)
    (w5 : k + 1 ≤ W) :
    ∃ c' t, Exec P W mkL c c' t ∧ t ≤ 11 * k + 4 ∧
      (∀ v < m, c'.nmem (MKb + v) =
        mkv v₀ (fun l => c.nmem (VLb + c.nmem (RVb + c.nmem (Db + l)))) k v) ∧
      (∀ a, (a < MKb ∨ MKb + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 9287 ∨ 9297 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨val, hval'⟩ : ∃ val : ℕ → ℕ,
      val = fun l => c.nmem (VLb + c.nmem (RVb + c.nmem (Db + l))) := ⟨_, rfl⟩
  have hvl : ∀ l < k, val l < m := fun l hl => by rw [hval']; exact hval l hl
  obtain ⟨c₁, t₁, e₁, ht₁, g3, g7, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    nrInit2_exec (P := P) (r := 9293) (s := 9287) (k := 1) (l := 0) c hc (by omega) (by omega)
      (by omega)
  have q : ∀ x, x ≠ 9293 → x ≠ 9287 → c₁.nreg x = c.nreg x := f₁
  let J : ℕ → Config → Prop := fun l c' =>
    (∀ x, x ≠ 9287 → x ≠ 9294 → c'.nreg x = c₁.nreg x) ∧
    (∀ v < m, c'.nmem (MKb + v) = mkv v₀ val l v) ∧
    (∀ a, (a < MKb ∨ MKb + m ≤ a) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h87, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 9287)
    (b := 9288) (body := mkB) J (B := 9) c₁ e₁.wb_right g7
    (by rw [q _ (by omega) (by omega), r8]) (Nat.zero_le k)
    ⟨fun _ _ _ => rfl, fun v hv => by
        rw [m₁, h0 v hv]; unfold mkv
        congr 1; apply propext
        constructor
        · intro h; exact Or.inl h
        · rintro (h | ⟨l', hl', -⟩)
          · exact h
          · omega,
      fun a _ => by rw [m₁], rfl, rfl, rfl⟩
    (fun l c' hlo hhi hw h87 h88 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, x ≠ 9287 → x ≠ 9294 → c'.nreg x = c₁.nreg x := j1
      have eD : c'.nmem (Db + l) = c.nmem (Db + l) := j3 _ (hD l hhi)
      have eR : c'.nmem (RVb + c.nmem (Db + l)) = c.nmem (RVb + c.nmem (Db + l)) :=
        j3 _ (hR l hhi)
      have eV : c'.nmem (VLb + c.nmem (RVb + c.nmem (Db + l))) = val l := by
        rw [j3 _ (hV l hhi), hval']
      obtain ⟨c'', t, ex, ht, h87', hn', hm', hr', hrm', ho'⟩ := mkB_exec (P := P) c' hw
        (Db := Db) (RVb := RVb) (VLb := VLb) (MKb := MKb)
        (by rw [f _ (by omega) (by omega), q _ (by omega) (by omega), r9])
        (by rw [f _ (by omega) (by omega), q _ (by omega) (by omega), r0])
        (by rw [f _ (by omega) (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega) (by omega), q _ (by omega) (by omega), r2])
        (by rw [f _ (by omega) (by omega), g3]) h87 (by omega)
        (by rw [eD]; exact w2 l hhi) (by rw [eD, eR]; exact w3 l hhi)
        (by rw [eD, eR, eV]; have := hvl l hhi; clear * - this w4; omega) (by omega)
      rw [eD, eR, eV] at hm'
      refine ⟨c'', t, ex, ht.le, h87', by rw [hn' _ (by omega) (by omega)]; exact h88,
        ⟨fun x a b => by rw [hn' x a b, f x a b], fun v hv => ?_, fun a ha => ?_,
          by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩⟩
      · rw [hm', mkv_succ]
        by_cases e : v = val l
        · rw [e, upd_same, iteT rfl]
        · rw [upd_other _ _ _ (by omega), iteF e]; exact j2 v hv
      · rw [hm', upd_other _ _ _ (by have := hvl l hhi; clear * - this ha; omega)]; exact j3 a ha)
  rw [hval'] at j2
  refine ⟨c₂, t₁ + k₂, .seq e₁ e₂, by omega, j2, j3, fun x hx => ?_, by rw [j4, rr₁],
    by rw [j5, rm₁], by rw [j6, o₁]⟩
  rw [j1 x (by omega) (by omega), q x (by omega) (by omega)]

end BKMNW

end PlanarFlow
