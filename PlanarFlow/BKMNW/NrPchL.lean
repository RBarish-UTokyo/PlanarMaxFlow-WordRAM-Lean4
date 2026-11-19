module

public import PlanarFlow.BKMNW.NcLoop

/-!
# Small array loops of the push-back program `pchP`

Five `whileLtN` loops over `i < n` with their own registers (`9240 … 9286`), used by `pchP`
(`NrPchA.lean` …):

* **`decL`** (`OUT[i] := X[i] - 1`; registers `9241 = n`, `9242 = Xb`, `9243 = OUTb`; scratch
  `9240`, `9244 … 9246`), `decL_exec` (`8 n + 4` steps);
* **`cstL`** (`OUT[i] := v`; `9251 = n`, `9252 = OUTb`, `9253 = v`; scratch `9250`, `9254`,
  `9255`), `cstL_exec` (`5 n + 4`);
* **`dvL`** (`OUT[i] := Kd + S[i] - Z · G[i]`; `9261 = n`, `9262 = Sb`, `9263 = Gb`,
  `9264 = OUTb`, `9265 = Kd`, `9266 = Z`; scratch `9260`, `9267 … 9270`), `dvL_exec`
  (`12 n + 4`);
* **`cntL`** (the prefix counts of the fixed points `X[j] = j`: `CR[i] := #{j < i | X j = j}`,
  `cnt := #{j < n | X j = j}` in `r9275`, for `X j ≤ j`; `9272 = n`, `9273 = Xb`, `9274 = CRb`;
  scratch `9271`, `9275 … 9278`), `cntL_exec` (`10 n + 5`);
* **`negL`** (in place, `FL[i] := tw - FL[i]`; `9281 = n`, `9282 = FLb`, `9283 = tw`; scratch
  `9280`, `9284 … 9286`), `negL_exec` (`7 n + 4`).

`nrStore` is `NcStep.lnStore` (stride `1`) with the stronger frame hypothesis on the body (only
the cells already written differ from the start), so that in-place updates can be described.
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

/-- **The store loop, stride `1`**, the body seeing every cell not yet written as at the start. -/
theorem nrStore {a b : ℕ} {body : Stmt} {Ob n B : ℕ} (val : ℕ → ℕ)
    (keep : ℕ → Prop) (c : Config) (hc : WordsBounded W c) (ha : c.nreg a = 0)
    (hb : c.nreg b = n) (hkb : keep b)
    (hbody : ∀ i (c' : Config), i < n → WordsBounded W c' → c'.nreg a = i →
      (∀ x, keep x → c'.nreg x = c.nreg x) →
      (∀ addr, (∀ j < i, addr ≠ Ob + j) → c'.nmem addr = c.nmem addr) →
      ∃ c'' k, Exec P W body c' c'' k ∧ k ≤ B ∧ c''.nreg a = i + 1 ∧
        (∀ x, keep x → c''.nreg x = c'.nreg x) ∧
        c''.nmem = upd c'.nmem (Ob + i) (val i) ∧ c''.rreg = c'.rreg ∧
        c''.rmem = c'.rmem ∧ c''.output = c'.output) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ k ≤ (B + 2) * n + 2 ∧
      (∀ i < n, c'.nmem (Ob + i) = val i) ∧
      (∀ addr, (∀ j < n, addr ≠ Ob + j) → c'.nmem addr = c.nmem addr) ∧
      (∀ x, keep x → c'.nreg x = c.nreg x) ∧ c'.nreg a = n ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, keep x → c'.nreg x = c.nreg x) ∧ (∀ j < i, c'.nmem (Ob + j) = val j) ∧
    (∀ addr, (∀ j < i, addr ≠ Ob + j) → c'.nmem addr = c.nmem addr) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', k, ex, hk, -, ha', j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := a) (b := b)
    (body := body) J (B := B) c hc ha hb (Nat.zero_le n)
    ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega), fun _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c₁ hlo hi hw h1 h2 ⟨f₁, v₁, o₁, q1, q2, q3⟩ => by
      obtain ⟨c₂, k₂, e₂, hk₂, g1, f₂, m₂, r₂, rm₂, o₂⟩ := hbody i c₁ hi hw h1 f₁ o₁
      refine ⟨c₂, k₂, e₂, hk₂, g1, by rw [f₂ b hkb, f₁ b hkb, hb],
        ⟨fun x hx => by rw [f₂ x hx, f₁ x hx], fun j hj => ?_, fun addr ha' => ?_,
          by rw [r₂, q1], by rw [rm₂, q2], by rw [o₂, q3]⟩⟩
      · rw [m₂]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact v₁ j hj
        · rw [upd_same]
      · rw [m₂, upd_other _ _ _ (ha' i (by omega))]
        exact o₁ addr fun j hj => ha' j (by omega))
  exact ⟨c', k, ex, hk, j2, j3, j1, ha', j4, j5, j6⟩

/-! ### `decL`: `OUT[i] := X[i] - 1` -/

/-- The body of `decL`. -/
def decB : Stmt :=
  block [.addN 9245 9242 9240, .loadN 9246 9245, .subN 9246 9246 9244,
    .addN 9245 9243 9240, .storeN 9245 9246, .addN 9240 9240 9244]

/-- **`OUT[i] := X[i] - 1`** for `i < n`. -/
def decL : Stmt := .seq (block [.constN 9244 1, .constN 9240 0]) (.whileLtN 9240 9241 decB)

theorem decB_exec (c : Config) (hc : WordsBounded W c) {Xb OUTb i : ℕ}
    (r2 : c.nreg 9242 = Xb) (r3 : c.nreg 9243 = OUTb) (r4 : c.nreg 9244 = 1)
    (r0 : c.nreg 9240 = i) (w1 : Xb + i ≤ W) (w2 : OUTb + i ≤ W) (w3 : i + 1 ≤ W) :
    ∃ c' t, Exec P W decB c c' t ∧ t = 6 ∧ c'.nreg 9240 = i + 1 ∧
      (∀ x, x ≠ 9240 → x ≠ 9245 → x ≠ 9246 → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (OUTb + i) (c.nmem (Xb + i) - 1) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold decB
  exec_block
  all_goals try (clear * - r2 r3 r4 r0 w1 w2 w3; config_simp; (try simp only [r2, r3, r4, r0]); omega)
  refine ⟨rfl, ?_, fun x h1 h2 h3 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r2, r3, r4, r0]
  · simp only [upd_apply]; split_ifs <;> omega

/-- The setup of a loop: two constants. -/
theorem nrInit2_exec (c : Config) (hc : WordsBounded W c) {r s k l : ℕ} (hrs : r ≠ s)
    (hk : k ≤ W) (hl : l ≤ W) :
    ∃ c' t, Exec P W (block [.constN r k, .constN s l]) c c' t ∧ t = 2 ∧ c'.nreg r = k ∧
      c'.nreg s = l ∧ (∀ x, x ≠ r → x ≠ s → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [upd_apply]; split_ifs <;> omega
  · config_simp
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **`decL`**: within `8 n + 4` steps `OUT[i] = X[i] - 1` for `i < n`; memory outside
`[OUTb, OUTb + n)`, registers outside `9240 … 9246`, reals and output kept. -/
theorem decL_exec (c : Config) (hc : WordsBounded W c) {n Xb OUTb : ℕ}
    (r1 : c.nreg 9241 = n) (r2 : c.nreg 9242 = Xb) (r3 : c.nreg 9243 = OUTb)
    (hd : Xb + n ≤ OUTb ∨ OUTb + n ≤ Xb) (w1 : Xb + n ≤ W) (w2 : OUTb + n ≤ W)
    (w3 : n + 1 ≤ W) :
    ∃ c' t, Exec P W decL c c' t ∧ t ≤ 8 * n + 4 ∧
      (∀ i < n, c'.nmem (OUTb + i) = c.nmem (Xb + i) - 1) ∧
      (∀ a, (a < OUTb ∨ OUTb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 9240 ∨ 9246 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g4, g0, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    nrInit2_exec (P := P) (r := 9244) (s := 9240) (k := 1) (l := 0) c hc (by omega) (by omega)
      (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, v₂, o₂, f₂, n₂, rr₂, rm₂, oo₂⟩ := nrStore (P := P) (W := W)
    (a := 9240) (b := 9241) (body := decB) (Ob := OUTb) (n := n) (B := 6)
    (fun i => c.nmem (Xb + i) - 1) (fun x => x ≠ 9240 ∧ x ≠ 9245 ∧ x ≠ 9246) c₁ e₁.wb_right g0
    (by rw [f₁ _ (by omega) (by omega), r1]) (by omega)
    (fun i c' hi hw h0 hk hm => by
      obtain ⟨c'', k, ex, hk', g0', gk, gm, gr, grm, go⟩ := decB_exec (P := P) c' hw
        (Xb := Xb) (OUTb := OUTb)
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r2])
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r3])
        (by rw [hk _ (by omega), g4]) h0 (by omega) (by omega) (by omega)
      have e : c'.nmem (Xb + i) = c.nmem (Xb + i) := by
        rw [hm _ (fun j hj => by omega), m₁]
      refine ⟨c'', k, ex, hk'.le, g0', fun x hx => gk x hx.1 hx.2.1 hx.2.2, ?_, gr, grm, go⟩
      rw [gm, e])
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, v₂, fun a ha => ?_, fun x hx => ?_,
    by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [oo₂, o₁]⟩
  · rw [o₂ a (fun j hj => by omega), m₁]
  · rw [f₂ x ⟨by omega, by omega, by omega⟩, f₁ x (by omega) (by omega)]

/-! ### `cstL`: `OUT[i] := v` -/

/-- The body of `cstL`. -/
def cstB : Stmt := block [.addN 9255 9252 9250, .storeN 9255 9253, .addN 9250 9250 9254]

/-- **`OUT[i] := v`** for `i < n`. -/
def cstL : Stmt := .seq (block [.constN 9254 1, .constN 9250 0]) (.whileLtN 9250 9251 cstB)

theorem cstB_exec (c : Config) (hc : WordsBounded W c) {OUTb v i : ℕ}
    (r2 : c.nreg 9252 = OUTb) (r3 : c.nreg 9253 = v) (r4 : c.nreg 9254 = 1)
    (r0 : c.nreg 9250 = i) (w2 : OUTb + i ≤ W) (w3 : i + 1 ≤ W) :
    ∃ c' t, Exec P W cstB c c' t ∧ t = 3 ∧ c'.nreg 9250 = i + 1 ∧
      (∀ x, x ≠ 9250 → x ≠ 9255 → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (OUTb + i) v ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cstB
  exec_block
  all_goals try (clear * - r2 r3 r4 r0 w2 w3; config_simp; (try simp only [r2, r3, r4, r0]); omega)
  refine ⟨rfl, ?_, fun x h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r2, r3, r4, r0]
  · simp only [upd_apply]; split_ifs <;> omega

/-- **`cstL`**: within `5 n + 4` steps `OUT[i] = v` for `i < n`. -/
theorem cstL_exec (c : Config) (hc : WordsBounded W c) {n OUTb v : ℕ}
    (r1 : c.nreg 9251 = n) (r2 : c.nreg 9252 = OUTb) (r3 : c.nreg 9253 = v)
    (w2 : OUTb + n ≤ W) (w3 : n + 1 ≤ W) :
    ∃ c' t, Exec P W cstL c c' t ∧ t ≤ 5 * n + 4 ∧
      (∀ i < n, c'.nmem (OUTb + i) = v) ∧
      (∀ a, (a < OUTb ∨ OUTb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 9250 ∨ 9255 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g4, g0, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    nrInit2_exec (P := P) (r := 9254) (s := 9250) (k := 1) (l := 0) c hc (by omega) (by omega)
      (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, v₂, o₂, f₂, n₂, rr₂, rm₂, oo₂⟩ := nrStore (P := P) (W := W)
    (a := 9250) (b := 9251) (body := cstB) (Ob := OUTb) (n := n) (B := 3)
    (fun _ => v) (fun x => x ≠ 9250 ∧ x ≠ 9255) c₁ e₁.wb_right g0
    (by rw [f₁ _ (by omega) (by omega), r1]) (by omega)
    (fun i c' hi hw h0 hk hm => by
      obtain ⟨c'', k, ex, hk', g0', gk, gm, gr, grm, go⟩ := cstB_exec (P := P) c' hw
        (OUTb := OUTb) (v := v)
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r2])
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r3])
        (by rw [hk _ (by omega), g4]) h0 (by omega) (by omega)
      exact ⟨c'', k, ex, hk'.le, g0', fun x hx => gk x hx.1 hx.2, gm, gr, grm, go⟩)
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, v₂, fun a ha => ?_, fun x hx => ?_,
    by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [oo₂, o₁]⟩
  · rw [o₂ a (fun j hj => by omega), m₁]
  · rw [f₂ x ⟨by omega, by omega⟩, f₁ x (by omega) (by omega)]

/-! ### `dvL`: `OUT[i] := Kd + S[i] - Z · G[i]` -/

/-- The body of `dvL`. -/
def dvLB : Stmt :=
  block [.addN 9268 9262 9260, .loadN 9269 9268, .addN 9269 9265 9269, .addN 9268 9263 9260,
    .loadN 9270 9268, .mulN 9270 9266 9270, .subN 9269 9269 9270, .addN 9268 9264 9260,
    .storeN 9268 9269, .addN 9260 9260 9267]

/-- **`OUT[i] := Kd + S[i] - Z · G[i]`** for `i < n`. -/
def dvL : Stmt := .seq (block [.constN 9267 1, .constN 9260 0]) (.whileLtN 9260 9261 dvLB)

theorem dvLB_exec (c : Config) (hc : WordsBounded W c) {Sb Gb OUTb Kd Z i : ℕ}
    (r2 : c.nreg 9262 = Sb) (r3 : c.nreg 9263 = Gb) (r4 : c.nreg 9264 = OUTb)
    (r5 : c.nreg 9265 = Kd) (r6 : c.nreg 9266 = Z) (r7 : c.nreg 9267 = 1)
    (r0 : c.nreg 9260 = i) (w1 : Sb + i ≤ W) (w2 : Gb + i ≤ W) (w3 : OUTb + i ≤ W)
    (w4 : Kd + c.nmem (Sb + i) ≤ W) (w5 : Z * c.nmem (Gb + i) ≤ W) (w6 : i + 1 ≤ W) :
    ∃ c' t, Exec P W dvLB c c' t ∧ t = 10 ∧ c'.nreg 9260 = i + 1 ∧
      (∀ x, x ≠ 9260 → x ≠ 9268 → x ≠ 9269 → x ≠ 9270 → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (OUTb + i) (Kd + c.nmem (Sb + i) - Z * c.nmem (Gb + i)) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dvLB
  exec_block
  all_goals try (clear * - r2 r3 r4 r5 r6 r7 r0 w1 w2 w3 w4 w5 w6; config_simp; (try simp only [r2, r3, r4, r5, r6, r7, r0]); omega)
  refine ⟨rfl, ?_, fun x h1 h2 h3 h4 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r2, r3, r4, r5, r6, r7, r0]
  · simp only [upd_apply]; split_ifs <;> omega

/-- **`dvL`**: within `12 n + 4` steps `OUT[i] = Kd + S[i] - Z · G[i]` for `i < n`. -/
theorem dvL_exec (c : Config) (hc : WordsBounded W c) {n Sb Gb OUTb Kd Z : ℕ}
    (r1 : c.nreg 9261 = n) (r2 : c.nreg 9262 = Sb) (r3 : c.nreg 9263 = Gb)
    (r4 : c.nreg 9264 = OUTb) (r5 : c.nreg 9265 = Kd) (r6 : c.nreg 9266 = Z)
    (dS : Sb + n ≤ OUTb ∨ OUTb + n ≤ Sb) (dG : Gb + n ≤ OUTb ∨ OUTb + n ≤ Gb)
    (w1 : Sb + n ≤ W) (w2 : Gb + n ≤ W) (w3 : OUTb + n ≤ W) (w6 : n + 1 ≤ W)
    (w4 : ∀ i < n, Kd + c.nmem (Sb + i) ≤ W) (w5 : ∀ i < n, Z * c.nmem (Gb + i) ≤ W) :
    ∃ c' t, Exec P W dvL c c' t ∧ t ≤ 12 * n + 4 ∧
      (∀ i < n, c'.nmem (OUTb + i) = Kd + c.nmem (Sb + i) - Z * c.nmem (Gb + i)) ∧
      (∀ a, (a < OUTb ∨ OUTb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 9260 ∨ 9270 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g7, g0, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    nrInit2_exec (P := P) (r := 9267) (s := 9260) (k := 1) (l := 0) c hc (by omega) (by omega)
      (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, v₂, o₂, f₂, n₂, rr₂, rm₂, oo₂⟩ := nrStore (P := P) (W := W)
    (a := 9260) (b := 9261) (body := dvLB) (Ob := OUTb) (n := n) (B := 10)
    (fun i => Kd + c.nmem (Sb + i) - Z * c.nmem (Gb + i))
    (fun x => x ≠ 9260 ∧ x ≠ 9268 ∧ x ≠ 9269 ∧ x ≠ 9270) c₁ e₁.wb_right g0
    (by rw [f₁ _ (by omega) (by omega), r1]) (by omega)
    (fun i c' hi hw h0 hk hm => by
      have eS : c'.nmem (Sb + i) = c.nmem (Sb + i) := by
        rw [hm _ (fun j hj => by omega), m₁]
      have eG : c'.nmem (Gb + i) = c.nmem (Gb + i) := by
        rw [hm _ (fun j hj => by omega), m₁]
      obtain ⟨c'', k, ex, hk', g0', gk, gm, gr, grm, go⟩ := dvLB_exec (P := P) c' hw
        (Sb := Sb) (Gb := Gb) (OUTb := OUTb) (Kd := Kd) (Z := Z)
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r2])
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r3])
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r4])
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r5])
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r6])
        (by rw [hk _ (by omega), g7]) h0 (by omega) (by omega) (by omega)
        (by rw [eS]; exact w4 i hi) (by rw [eG]; exact w5 i hi) (by omega)
      refine ⟨c'', k, ex, hk'.le, g0', fun x hx => gk x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2, ?_, gr,
        grm, go⟩
      rw [gm, eS, eG])
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, v₂, fun a ha => ?_, fun x hx => ?_,
    by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [oo₂, o₁]⟩
  · rw [o₂ a (fun j hj => by omega), m₁]
  · rw [f₂ x ⟨by omega, by omega, by omega, by omega⟩, f₁ x (by omega) (by omega)]

/-! ### `negL`: `FL[i] := tw - FL[i]` (in place) -/

/-- The body of `negL`. -/
def negB : Stmt :=
  block [.addN 9285 9282 9280, .loadN 9286 9285, .subN 9286 9283 9286, .storeN 9285 9286,
    .addN 9280 9280 9284]

/-- **`FL[i] := tw - FL[i]`** for `i < n`. -/
def negL : Stmt := .seq (block [.constN 9284 1, .constN 9280 0]) (.whileLtN 9280 9281 negB)

theorem negB_exec (c : Config) (hc : WordsBounded W c) {FLb tw i : ℕ}
    (r2 : c.nreg 9282 = FLb) (r3 : c.nreg 9283 = tw) (r4 : c.nreg 9284 = 1)
    (r0 : c.nreg 9280 = i) (w2 : FLb + i ≤ W) (w3 : i + 1 ≤ W) :
    ∃ c' t, Exec P W negB c c' t ∧ t = 5 ∧ c'.nreg 9280 = i + 1 ∧
      (∀ x, x ≠ 9280 → x ≠ 9285 → x ≠ 9286 → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (FLb + i) (tw - c.nmem (FLb + i)) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have htw : tw ≤ W := by rw [← r3]; exact hc.1 _
  unfold negB
  exec_block
  all_goals try (clear * - r2 r3 r4 r0 w2 w3 htw; config_simp; (try simp only [r2, r3, r4, r0]); omega)
  refine ⟨rfl, ?_, fun x h1 h2 h3 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r2, r3, r4, r0]
  · simp only [upd_apply]; split_ifs <;> omega

/-- **`negL`**: within `7 n + 4` steps `FL[i] := tw - FL[i]` for `i < n`. -/
theorem negL_exec (c : Config) (hc : WordsBounded W c) {n FLb tw : ℕ}
    (r1 : c.nreg 9281 = n) (r2 : c.nreg 9282 = FLb) (r3 : c.nreg 9283 = tw)
    (w2 : FLb + n ≤ W) (w3 : n + 1 ≤ W) :
    ∃ c' t, Exec P W negL c c' t ∧ t ≤ 7 * n + 4 ∧
      (∀ i < n, c'.nmem (FLb + i) = tw - c.nmem (FLb + i)) ∧
      (∀ a, (a < FLb ∨ FLb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 9280 ∨ 9286 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g4, g0, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    nrInit2_exec (P := P) (r := 9284) (s := 9280) (k := 1) (l := 0) c hc (by omega) (by omega)
      (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, v₂, o₂, f₂, n₂, rr₂, rm₂, oo₂⟩ := nrStore (P := P) (W := W)
    (a := 9280) (b := 9281) (body := negB) (Ob := FLb) (n := n) (B := 5)
    (fun i => tw - c.nmem (FLb + i)) (fun x => x ≠ 9280 ∧ x ≠ 9285 ∧ x ≠ 9286) c₁ e₁.wb_right g0
    (by rw [f₁ _ (by omega) (by omega), r1]) (by omega)
    (fun i c' hi hw h0 hk hm => by
      have e : c'.nmem (FLb + i) = c.nmem (FLb + i) := by
        rw [hm _ (fun j hj => by omega), m₁]
      obtain ⟨c'', k, ex, hk', g0', gk, gm, gr, grm, go⟩ := negB_exec (P := P) c' hw
        (FLb := FLb) (tw := tw)
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r2])
        (by rw [hk _ (by omega), f₁ _ (by omega) (by omega), r3])
        (by rw [hk _ (by omega), g4]) h0 (by omega) (by omega)
      refine ⟨c'', k, ex, hk'.le, g0', fun x hx => gk x hx.1 hx.2.1 hx.2.2, ?_, gr, grm, go⟩
      rw [gm, e])
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, v₂, fun a ha => ?_, fun x hx => ?_,
    by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [oo₂, o₁]⟩
  · rw [o₂ a (fun j hj => by omega), m₁]
  · rw [f₂ x ⟨by omega, by omega, by omega⟩, f₁ x (by omega) (by omega)]

/-! ### `cntL`: prefix counts of the fixed points -/

/-- The number of fixed points `X j = j` (`j < i`), counted by `1 - (j - X j)`. -/
def rcnt (X : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => rcnt X i + (1 - (i - X i))

/-- The body of `cntL`. -/
def cntB : Stmt :=
  block [.addN 9277 9273 9271, .loadN 9278 9277, .addN 9277 9274 9271, .storeN 9277 9275,
    .subN 9278 9271 9278, .subN 9278 9276 9278, .addN 9275 9275 9278, .addN 9271 9271 9276]

/-- **The prefix counts** `CR[i] := rcnt X i`, `cnt := rcnt X n`. -/
def cntL : Stmt :=
  .seq (block [.constN 9276 1, .constN 9271 0, .constN 9275 0]) (.whileLtN 9271 9272 cntB)

lemma rcnt_le (X : ℕ → ℕ) : ∀ i, rcnt X i ≤ i
  | 0 => le_rfl
  | i + 1 => by have := rcnt_le X i; simp only [rcnt]; omega

theorem cntB_exec (c : Config) (hc : WordsBounded W c) {Xb CRb i k : ℕ}
    (r3 : c.nreg 9273 = Xb) (r4 : c.nreg 9274 = CRb) (r5 : c.nreg 9275 = k)
    (r6 : c.nreg 9276 = 1) (r1 : c.nreg 9271 = i) (w1 : Xb + i ≤ W) (w2 : CRb + i ≤ W)
    (w3 : i + 1 ≤ W) (w4 : k + 1 ≤ W) :
    ∃ c' t, Exec P W cntB c c' t ∧ t = 8 ∧ c'.nreg 9271 = i + 1 ∧
      c'.nreg 9275 = k + (1 - (i - c.nmem (Xb + i))) ∧
      (∀ x, x ≠ 9271 → x ≠ 9275 → x ≠ 9277 → x ≠ 9278 → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (CRb + i) k ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cntB
  exec_block
  all_goals try (clear * - r3 r4 r5 r6 r1 w1 w2 w3 w4; config_simp; (try simp only [r3, r4, r5, r6, r1]); omega)
  refine ⟨rfl, ?_, ?_, fun x h1 h2 h3 h4 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r3, r4, r5, r6, r1]
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

/-- **`cntL`**: within `10 n + 5` steps `CR[i] = rcnt X i` for `i < n` and `r9275 = rcnt X n`. -/
theorem cntL_exec (c : Config) (hc : WordsBounded W c) {n Xb CRb : ℕ}
    (r2 : c.nreg 9272 = n) (r3 : c.nreg 9273 = Xb) (r4 : c.nreg 9274 = CRb)
    (hd : Xb + n ≤ CRb ∨ CRb + n ≤ Xb) (w1 : Xb + n ≤ W) (w2 : CRb + n ≤ W)
    (w3 : n + 1 ≤ W) :
    ∃ c' t, Exec P W cntL c c' t ∧ t ≤ 10 * n + 5 ∧
      (∀ i < n, c'.nmem (CRb + i) = rcnt (fun j => c.nmem (Xb + j)) i) ∧
      c'.nreg 9275 = rcnt (fun j => c.nmem (Xb + j)) n ∧
      (∀ a, (a < CRb ∨ CRb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 9271 ∨ 9278 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set X : ℕ → ℕ := fun j => c.nmem (Xb + j) with hX
  obtain ⟨c₁, t₁, e₁, ht₁, g6, g1, g5, f₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ t₁,
      Exec P W (block [.constN 9276 1, .constN 9271 0, .constN 9275 0]) c c₁ t₁ ∧ t₁ = 3 ∧
      c₁.nreg 9276 = 1 ∧ c₁.nreg 9271 = 0 ∧ c₁.nreg 9275 = 0 ∧
      (∀ x, x ≠ 9276 → x ≠ 9271 → x ≠ 9275 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals simp only [upd_apply]; split_ifs <;> omega
  have q : ∀ x, x ≠ 9276 → x ≠ 9271 → x ≠ 9275 → c₁.nreg x = c.nreg x := f₁
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, x ≠ 9271 → x ≠ 9275 → x ≠ 9277 → x ≠ 9278 → c'.nreg x = c₁.nreg x) ∧
    c'.nreg 9275 = rcnt X i ∧
    (∀ j < i, c'.nmem (CRb + j) = rcnt X j) ∧
    (∀ a, (a < CRb ∨ CRb + i ≤ a) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h71, j1, j2, j3, j4, j5, j6, j7⟩ := lnRange (P := P) (a := 9271)
    (b := 9272) (body := cntB) J (B := 8) c₁ e₁.wb_right g1
    (by rw [q _ (by omega) (by omega) (by omega), r2]) (Nat.zero_le n)
    ⟨fun _ _ _ _ _ => rfl, by rw [g5]; rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [m₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h71 h72 ⟨j1, j2, j3, j4, j5, j6, j7⟩ => by
      have f : ∀ x, x ≠ 9271 → x ≠ 9275 → x ≠ 9277 → x ≠ 9278 → c'.nreg x = c₁.nreg x := j1
      have e : c'.nmem (Xb + i) = X i := by
        rw [j4 _ (by omega)]
      have hr := rcnt_le X i
      obtain ⟨c'', t, ex, ht, h71', h75', hn', hm', hr', hrm', ho'⟩ := cntB_exec (P := P) c' hw
        (Xb := Xb) (CRb := CRb) (k := rcnt X i)
        (by rw [f _ (by omega) (by omega) (by omega) (by omega), q _ (by omega) (by omega)
          (by omega), r3])
        (by rw [f _ (by omega) (by omega) (by omega) (by omega), q _ (by omega) (by omega)
          (by omega), r4])
        j2 (by rw [f _ (by omega) (by omega) (by omega) (by omega), g6]) h71 (by omega)
        (by omega) (by omega) (by omega)
      refine ⟨c'', t, ex, ht.le, h71', (by rw [hn' _ (by omega) (by omega) (by omega) (by omega)]; exact h72),
        fun x a b d g => by rw [hn' x a b d g, f x a b d g], by rw [h75', e]; rfl,
        fun j hj => ?_, fun a ha => ?_, by rw [hr', j5], by rw [hrm', j6], by rw [ho', j7]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j3 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (by omega)]
        exact j4 a (by omega))
  refine ⟨c₂, t₁ + k₂, .seq e₁ e₂, by omega, j3, j2, j4, fun x hx => ?_,
    by rw [j5, rr₁], by rw [j6, rm₁], by rw [j7, o₁]⟩
  rw [j1 x (by omega) (by omega) (by omega) (by omega), q x (by omega) (by omega) (by omega)]

end BKMNW

end PlanarFlow
