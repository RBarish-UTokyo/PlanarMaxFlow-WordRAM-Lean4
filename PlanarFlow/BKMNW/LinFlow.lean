module

public import PlanarFlow.BKMNW.Local
public import PlanarFlow.BKMNW.LinLoops

/-!
# Flows on the machine: the sum of the children's flows (`joinFlow`) and `f + cob χ`

Integer flows are held on natural words with an offset `Z` (`(g + Z).toNat`, `|g| ≤ Zb`,
`2 Zb ≤ Z`).

* `lzProg` (fill `OUT[i] := v`; registers `6260 = m`, `6261 = OUTb`, `6262 = v`; scratch
  `6263`, `6264`, `6265`), `lzProg_exec` (`5 m + 4` steps).
* `laProg` (add-scatter `OUT[IX[j]] := OUT[IX[j]] + V[j] - Z`; registers `6270 = mc`,
  `6271 = IXb`, `6272 = Vb`, `6273 = Z`, `6274 = OUTb`; scratch `6275 … 6279`), `laProg_exec`
  (`12 mc + 4` steps; `IX` injective).
* **`jfProg`** (registers `6290 = m`, `6291 = ml`, `6292 = mr`, `6293 = ILb`, `6294 = VLb`,
  `6295 = IRb`, `6296 = VRb`, `6297 = Z`, `6298 = OUTb`): the parent's array `OUT` of the sum of
  the two children's flows, from the children's arrays `VL`, `VR` and their index maps `IL`, `IR`
  into the parent's enumeration. **`jfProg_joinFlow`**: within `5 m + 12 (ml + mr) + 25` steps,
  `(OUT[i] : ℤ) = Z + joinFlow fl fr (e i)` (the function `joinFlow` of
  `PlanarFlow/BKMNW/Local.lean`, on the darts of the parent piece map).
* **`cbProg`** (registers `6280 = m`, `6281 = Fb`, `6282 = FRb`, `6283 = FCb`, `6284 = PHb`,
  `6285 = OUTb`; scratch `6286 … 6289`): `OUT[i] := F[i] + PH[FR[i]] - PH[FC[i]]`;
  **`cbProg_cob`**: within `17 m + 4` steps, `(OUT[i] : ℤ) = Z + f (e i) + M.cob χ (e i)`, the last
  line of FixConservationOnPath (`fixPath`: `s.1 + M.cob χ`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Exec

variable {P : Input} {W : ℕ}

/-! ### The fill -/

/-- `OUT[i] := v`. -/
def lzBody : Stmt := block [.addN 6264 6261 6265, .storeN 6264 6262, .addN 6265 6265 6263]

/-- **The fill** `OUT[i] := v`, `i < m`. -/
def lzProg : Stmt :=
  .seq (block [.constN 6263 1, .constN 6265 0]) (.whileLtN 6265 6260 lzBody)

theorem lzBody_exec (c : Config) (hc : WordsBounded W c) {OUTb v j : ℕ}
    (r1 : c.nreg 6261 = OUTb) (r2 : c.nreg 6262 = v) (r3 : c.nreg 6263 = 1)
    (r5 : c.nreg 6265 = j) (w1 : OUTb + j ≤ W) (w4 : j + 1 ≤ W) :
    ∃ c' k, Exec P W lzBody c c' k ∧ k = 3 ∧ c'.nreg 6265 = j + 1 ∧
      c'.nmem = upd c.nmem (OUTb + j) v ∧
      (∀ x, (x < 6264 ∨ 6265 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lzBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r5]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r3, r5]
  · config_simp; simp only [r1, r2, r5]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The fill**: within `5 m + 4` steps `OUT[i] = v` for `i < m`; memory outside
`[OUTb, OUTb + m)`, registers outside `6263 … 6265`, reals and output kept. -/
theorem lzProg_exec (c : Config) (hc : WordsBounded W c) {m OUTb v : ℕ}
    (r0 : c.nreg 6260 = m) (r1 : c.nreg 6261 = OUTb) (r2 : c.nreg 6262 = v)
    (w1 : OUTb + m ≤ W) (w4 : m + 1 ≤ W) :
    ∃ c' k, Exec P W lzProg c c' k ∧ k ≤ 5 * m + 4 ∧
      (∀ j < m, c'.nmem (OUTb + j) = v) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6263 ∨ 6265 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lzProg
  obtain ⟨c₁, k₁, e₁, hk₁, g3, g5, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 6263 1, .constN 6265 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 6263 = 1 ∧ c₁.nreg 6265 = 0 ∧
      (∀ x, x ≠ 6263 → x ≠ 6265 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 6263 → x ≠ 6265 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 6264 ∨ 6265 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (OUTb + j) = v) ∧
    (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h75, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 6265)
    (b := 6260) (body := lzBody) J (B := 3) c₁ hw₁ g5 (by rw [q _ (by omega) (by omega), r0])
    (Nat.zero_le m) ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h75 h70 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 6264 ∨ 6265 < x) → c'.nreg x = c₁.nreg x := j1
      obtain ⟨c'', t, ex, ht, h75', hm', hn', hr', hrm', ho'⟩ := lzBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
        (by rw [f _ (by omega), g3]) h75 (by omega) (by omega)
      refine ⟨c'', t, ex, ht.le, h75', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
        exact j3 a (fun h => ha ⟨h.1, by omega⟩))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, fun x hx => ?_, by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega)]

/-! ### The add-scatter -/

/-- `OUT[IX[j]] := OUT[IX[j]] + V[j] - Z`. -/
def laBody : Stmt :=
  block [.addN 6277 6271 6276, .loadN 6277 6277, .addN 6277 6274 6277, .loadN 6278 6277,
    .addN 6279 6272 6276, .loadN 6279 6279, .addN 6278 6278 6279, .subN 6278 6278 6273,
    .storeN 6277 6278, .addN 6276 6276 6275]

/-- **The add-scatter** `OUT[IX[j]] := OUT[IX[j]] + V[j] - Z`, `j < mc`. -/
def laProg : Stmt :=
  .seq (block [.constN 6275 1, .constN 6276 0]) (.whileLtN 6276 6270 laBody)

theorem laBody_exec (c : Config) (hc : WordsBounded W c) {IXb Vb Z OUTb j : ℕ}
    (r1 : c.nreg 6271 = IXb) (r2 : c.nreg 6272 = Vb) (r3 : c.nreg 6273 = Z)
    (r4 : c.nreg 6274 = OUTb) (r5 : c.nreg 6275 = 1) (r6 : c.nreg 6276 = j)
    (w1 : IXb + j ≤ W) (w2 : Vb + j ≤ W) (w3 : OUTb + c.nmem (IXb + j) ≤ W)
    (w5 : c.nmem (OUTb + c.nmem (IXb + j)) + c.nmem (Vb + j) ≤ W) (w4 : j + 1 ≤ W) :
    ∃ c' k, Exec P W laBody c c' k ∧ k = 10 ∧ c'.nreg 6276 = j + 1 ∧
      c'.nmem = upd c.nmem (OUTb + c.nmem (IXb + j))
        (c.nmem (OUTb + c.nmem (IXb + j)) + c.nmem (Vb + j) - Z) ∧
      (∀ x, (x < 6276 ∨ 6279 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold laBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5, r6]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r5, r6]
  · config_simp; simp only [r1, r2, r3, r4, r6]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The add-scatter**: with `IX` injective, pointing below `m` into `OUT`, and `OUT` disjoint
from `IX` and `V`, within `12 mc + 4` steps `OUT[IX[j]] = OUT₀[IX[j]] + V[j] - Z` for `j < mc`;
the other memory, registers outside `6275 … 6279`, reals and output kept. -/
theorem laProg_exec (c : Config) (hc : WordsBounded W c) {mc IXb Vb Z OUTb : ℕ}
    (r0 : c.nreg 6270 = mc) (r1 : c.nreg 6271 = IXb) (r2 : c.nreg 6272 = Vb)
    (r3 : c.nreg 6273 = Z) (r4 : c.nreg 6274 = OUTb)
    (w1 : IXb + mc ≤ W) (w2 : Vb + mc ≤ W) (w4 : mc + 1 ≤ W)
    (hIX : ∀ j < mc, OUTb + c.nmem (IXb + j) ≤ W)
    (hsum : ∀ j < mc, c.nmem (OUTb + c.nmem (IXb + j)) + c.nmem (Vb + j) ≤ W)
    (hinj : ∀ i < mc, ∀ j < mc, c.nmem (IXb + i) = c.nmem (IXb + j) → i = j)
    (d1 : ∀ i < mc, ∀ j < mc, OUTb + c.nmem (IXb + i) ≠ IXb + j)
    (d2 : ∀ i < mc, ∀ j < mc, OUTb + c.nmem (IXb + i) ≠ Vb + j) :
    ∃ c' k, Exec P W laProg c c' k ∧ k ≤ 12 * mc + 4 ∧
      (∀ j < mc, c'.nmem (OUTb + c.nmem (IXb + j)) =
        c.nmem (OUTb + c.nmem (IXb + j)) + c.nmem (Vb + j) - Z) ∧
      (∀ a, (∀ j < mc, a ≠ OUTb + c.nmem (IXb + j)) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6275 ∨ 6279 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold laProg
  obtain ⟨c₁, k₁, e₁, hk₁, g5, g6, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 6275 1, .constN 6276 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 6275 = 1 ∧ c₁.nreg 6276 = 0 ∧
      (∀ x, x ≠ 6275 → x ≠ 6276 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 6275 → x ≠ 6276 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 6276 ∨ 6279 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (OUTb + m₀ (IXb + j)) = m₀ (OUTb + m₀ (IXb + j)) + m₀ (Vb + j) - Z) ∧
    (∀ a, (∀ j < i, a ≠ OUTb + m₀ (IXb + j)) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h76, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 6276)
    (b := 6270) (body := laBody) J (B := 10) c₁ hw₁ g6 (by rw [q _ (by omega) (by omega), r0])
    (Nat.zero_le mc) ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h76 h70 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 6276 ∨ 6279 < x) → c'.nreg x = c₁.nreg x := j1
      have e1 : c'.nmem (IXb + i) = m₀ (IXb + i) :=
        j3 _ (fun j hj h => d1 j (by omega) i hhi h.symm)
      have e2 : c'.nmem (Vb + i) = m₀ (Vb + i) :=
        j3 _ (fun j hj h => d2 j (by omega) i hhi h.symm)
      have e3 : c'.nmem (OUTb + m₀ (IXb + i)) = m₀ (OUTb + m₀ (IXb + i)) :=
        j3 _ (fun j hj h => by have := hinj j (by omega) i hhi (by omega); omega)
      obtain ⟨c'', t, ex, ht, h76', hm', hn', hr', hrm', ho'⟩ := laBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r3])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r4])
        (by rw [f _ (by omega), g5]) h76 (by omega) (by omega) (by rw [e1]; exact hIX i hhi)
        (by rw [e1, e3, e2]; exact hsum i hhi) (by omega)
      rw [e1, e3, e2] at hm'
      refine ⟨c'', t, ex, ht.le, h76', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (fun h => by have := hinj j (by omega) i hhi (by omega); omega)]
          exact j2 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (ha i (by omega))]
        exact j3 a (fun j hj => ha j (by omega)))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, fun x hx => ?_, by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega)]

/-! ### The cobound map -/

/-- `OUT[i] := F[i] + PH[FR[i]] - PH[FC[i]]`. -/
def cbBody : Stmt :=
  block [.addN 6288 6281 6287, .loadN 6289 6288,
    .addN 6288 6282 6287, .loadN 6288 6288, .addN 6288 6284 6288, .loadN 6288 6288,
    .addN 6289 6289 6288,
    .addN 6288 6283 6287, .loadN 6288 6288, .addN 6288 6284 6288, .loadN 6288 6288,
    .subN 6289 6289 6288,
    .addN 6288 6285 6287, .storeN 6288 6289, .addN 6287 6287 6286]

/-- **The cobound map** `OUT[i] := F[i] + PH[FR[i]] - PH[FC[i]]`, `i < m`. -/
def cbLoop : Stmt :=
  .seq (block [.constN 6286 1, .constN 6287 0]) (.whileLtN 6287 6280 cbBody)

theorem cbBody_exec (c : Config) (hc : WordsBounded W c) {Fb FRb FCb PHb OUTb j : ℕ}
    (r1 : c.nreg 6281 = Fb) (r2 : c.nreg 6282 = FRb) (r3 : c.nreg 6283 = FCb)
    (r4 : c.nreg 6284 = PHb) (r5 : c.nreg 6285 = OUTb) (r6 : c.nreg 6286 = 1)
    (r7 : c.nreg 6287 = j) (w1 : Fb + j ≤ W) (w2 : FRb + j ≤ W) (w3 : FCb + j ≤ W)
    (w4 : PHb + c.nmem (FRb + j) ≤ W) (w5 : PHb + c.nmem (FCb + j) ≤ W)
    (w6 : c.nmem (Fb + j) + c.nmem (PHb + c.nmem (FRb + j)) ≤ W) (w7 : OUTb + j ≤ W)
    (w8 : j + 1 ≤ W) :
    ∃ c' k, Exec P W cbBody c c' k ∧ k = 15 ∧ c'.nreg 6287 = j + 1 ∧
      c'.nmem = upd c.nmem (OUTb + j) (c.nmem (Fb + j) + c.nmem (PHb + c.nmem (FRb + j)) -
        c.nmem (PHb + c.nmem (FCb + j))) ∧
      (∀ x, (x < 6287 ∨ 6289 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cbBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5, r6, r7]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r6, r7]
  · config_simp; simp only [r1, r2, r3, r4, r5, r7]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The cobound map**: with `OUT` disjoint from the four input arrays, within `17 m + 4`
steps `OUT[i] = F[i] + PH[FR[i]] - PH[FC[i]]`; memory outside `[OUTb, OUTb + m)`, registers
outside `6286 … 6289`, reals and output kept. -/
theorem cbLoop_exec (c : Config) (hc : WordsBounded W c) {m Fb FRb FCb PHb OUTb : ℕ}
    (r0 : c.nreg 6280 = m) (r1 : c.nreg 6281 = Fb) (r2 : c.nreg 6282 = FRb)
    (r3 : c.nreg 6283 = FCb) (r4 : c.nreg 6284 = PHb) (r5 : c.nreg 6285 = OUTb)
    (w1 : Fb + m ≤ W) (w2 : FRb + m ≤ W) (w3 : FCb + m ≤ W) (w7 : OUTb + m ≤ W)
    (w8 : m + 1 ≤ W)
    (hR : ∀ j < m, PHb + c.nmem (FRb + j) ≤ W) (hC : ∀ j < m, PHb + c.nmem (FCb + j) ≤ W)
    (hs : ∀ j < m, c.nmem (Fb + j) + c.nmem (PHb + c.nmem (FRb + j)) ≤ W)
    (d1 : ∀ j < m, ¬ (OUTb ≤ Fb + j ∧ Fb + j < OUTb + m))
    (d2 : ∀ j < m, ¬ (OUTb ≤ FRb + j ∧ FRb + j < OUTb + m))
    (d3 : ∀ j < m, ¬ (OUTb ≤ FCb + j ∧ FCb + j < OUTb + m))
    (d4 : ∀ j < m, ¬ (OUTb ≤ PHb + c.nmem (FRb + j) ∧ PHb + c.nmem (FRb + j) < OUTb + m))
    (d5 : ∀ j < m, ¬ (OUTb ≤ PHb + c.nmem (FCb + j) ∧ PHb + c.nmem (FCb + j) < OUTb + m)) :
    ∃ c' k, Exec P W cbLoop c c' k ∧ k ≤ 17 * m + 4 ∧
      (∀ j < m, c'.nmem (OUTb + j) = c.nmem (Fb + j) + c.nmem (PHb + c.nmem (FRb + j)) -
        c.nmem (PHb + c.nmem (FCb + j))) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6286 ∨ 6289 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cbLoop
  obtain ⟨c₁, k₁, e₁, hk₁, g6, g7, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 6286 1, .constN 6287 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 6286 = 1 ∧ c₁.nreg 6287 = 0 ∧
      (∀ x, x ≠ 6286 → x ≠ 6287 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 6286 → x ≠ 6287 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 6287 ∨ 6289 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (OUTb + j) = m₀ (Fb + j) + m₀ (PHb + m₀ (FRb + j)) -
      m₀ (PHb + m₀ (FCb + j))) ∧
    (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h77, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 6287)
    (b := 6280) (body := cbBody) J (B := 15) c₁ hw₁ g7 (by rw [q _ (by omega) (by omega), r0])
    (Nat.zero_le m) ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h77 h70 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 6287 ∨ 6289 < x) → c'.nreg x = c₁.nreg x := j1
      have e1 : c'.nmem (Fb + i) = m₀ (Fb + i) := j3 _ (fun h => d1 i hhi ⟨h.1, by omega⟩)
      have e2 : c'.nmem (FRb + i) = m₀ (FRb + i) := j3 _ (fun h => d2 i hhi ⟨h.1, by omega⟩)
      have e3 : c'.nmem (FCb + i) = m₀ (FCb + i) := j3 _ (fun h => d3 i hhi ⟨h.1, by omega⟩)
      have e4 : c'.nmem (PHb + m₀ (FRb + i)) = m₀ (PHb + m₀ (FRb + i)) :=
        j3 _ (fun h => d4 i hhi ⟨h.1, by omega⟩)
      have e5 : c'.nmem (PHb + m₀ (FCb + i)) = m₀ (PHb + m₀ (FCb + i)) :=
        j3 _ (fun h => d5 i hhi ⟨h.1, by omega⟩)
      obtain ⟨c'', t, ex, ht, h77', hm', hn', hr', hrm', ho'⟩ := cbBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r3])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r4])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r5])
        (by rw [f _ (by omega), g6]) h77 (by omega) (by omega) (by omega)
        (by rw [e2]; exact hR i hhi) (by rw [e3]; exact hC i hhi)
        (by rw [e1, e2, e4]; exact hs i hhi) (by omega) (by omega)
      rw [e1, e2, e3, e4, e5] at hm'
      refine ⟨c'', t, ex, ht.le, h77', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
        exact j3 a (fun h => ha ⟨h.1, by omega⟩))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, fun x hx => ?_, by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega)]

/-! ### The sum of the children's flows -/

/-- Fill `OUT` with `Z`. -/
def jfS1 : Stmt := block [.copyN 6260 6290, .copyN 6261 6298, .copyN 6262 6297]

/-- Add the left child's flow. -/
def jfS2 : Stmt :=
  block [.copyN 6270 6291, .copyN 6271 6293, .copyN 6272 6294, .copyN 6273 6297, .copyN 6274 6298]

/-- Add the right child's flow. -/
def jfS3 : Stmt :=
  block [.copyN 6270 6292, .copyN 6271 6295, .copyN 6272 6296, .copyN 6273 6297, .copyN 6274 6298]

/-- **The sum of the children's flows on the parent's darts.** -/
def jfProg : Stmt := .seq jfS1 (.seq lzProg (.seq jfS2 (.seq laProg (.seq jfS3 laProg))))

/-- The sum of two flows given on two sets of darts (`joinFlow` on functions of `D`). -/
def jfun {D : Type*} [DecidableEq D] (Bl Br : Finset D) (gl gr : D → ℤ) (x : D) : ℤ :=
  (if x ∈ Bl then gl x else 0) + (if x ∈ Br then gr x else 0)

/-- `joinFlow` is `jfun` of the extensions by zero. -/
lemma joinFlow_eq_jfun {D : Type*} [DecidableEq D] {B Bl Br : Finset D}
    (fl : Orbit.SDart Bl → ℤ) (fr : Orbit.SDart Br → ℤ) (x : Orbit.SDart B) :
    joinFlow fl fr x = jfun Bl Br (fun d => if h : d ∈ Bl then fl ⟨d, h⟩ else 0)
      (fun d => if h : d ∈ Br then fr ⟨d, h⟩ else 0) x.1 := by
  unfold joinFlow jfun
  by_cases h1 : x.1 ∈ Bl <;> by_cases h2 : x.1 ∈ Br <;> simp [h1, h2]

lemma toNat_cast_of {a : ℤ} (h : 0 ≤ a) : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h

/-- **The sum of the children's flows on the machine.** The parent's darts `e i` (`i < m`), the
children's darts `el j` (`j < ml`) and `er j` (`j < mr`), each without repetition, the index
maps `IL[j]`, `IR[j]` of the children's darts among the parent's, the children's flows `gl`, `gr`
with offset `Z` (`|g| ≤ Zb`, `2 Zb ≤ Z`, `3 Z ≤ W`) in `VL`, `VR`; layout
`OUT | IL | VL | IR | VR` (`OUT` of length `m`). Within `5 m + 12 (ml + mr) + 25` steps,
`(OUT[i] : ℤ) = Z + jfun Bl Br gl gr (e i)` for every `i < m` (with `joinFlow_eq_jfun`, the
function `joinFlow` of the recursion); memory outside `OUT`, registers outside `6260 … 6279`,
reals and output kept. -/
theorem jfProg_joinFlow {D : Type*} [DecidableEq D] (c : Config) (hc : WordsBounded W c)
    {m ml mr ILb VLb IRb VRb Z OUTb Zb : ℕ}
    (r0 : c.nreg 6290 = m) (r1 : c.nreg 6291 = ml) (r2 : c.nreg 6292 = mr)
    (r3 : c.nreg 6293 = ILb) (r4 : c.nreg 6294 = VLb) (r5 : c.nreg 6295 = IRb)
    (r6 : c.nreg 6296 = VRb) (r7 : c.nreg 6297 = Z) (r8 : c.nreg 6298 = OUTb)
    (l1 : OUTb + m ≤ ILb) (l2 : ILb + ml ≤ VLb) (l3 : VLb + ml ≤ IRb) (l4 : IRb + mr ≤ VRb)
    (l5 : VRb + mr ≤ W) (hmW : m + ml + mr + 1 ≤ W) (hZ : 2 * Zb ≤ Z) (hZW : 3 * Z ≤ W)
    {e el er : ℕ → D} {Bl Br : Finset D} {gl gr : D → ℤ}
    (he : ∀ i < m, ∀ j < m, e i = e j → i = j)
    (hIL : ∀ j < ml, c.nmem (ILb + j) < m ∧ e (c.nmem (ILb + j)) = el j)
    (hIR : ∀ j < mr, c.nmem (IRb + j) < m ∧ e (c.nmem (IRb + j)) = er j)
    (hel : ∀ i < ml, ∀ j < ml, el i = el j → i = j) (her : ∀ i < mr, ∀ j < mr, er i = er j → i = j)
    (hBl : ∀ i < m, e i ∈ Bl → ∃ j < ml, el j = e i) (hBl' : ∀ j < ml, el j ∈ Bl)
    (hBr : ∀ i < m, e i ∈ Br → ∃ j < mr, er j = e i) (hBr' : ∀ j < mr, er j ∈ Br)
    (hgl : ∀ x, -(Zb : ℤ) ≤ gl x ∧ gl x ≤ Zb) (hgr : ∀ x, -(Zb : ℤ) ≤ gr x ∧ gr x ≤ Zb)
    (hVL : ∀ j < ml, c.nmem (VLb + j) = (gl (el j) + Z).toNat)
    (hVR : ∀ j < mr, c.nmem (VRb + j) = (gr (er j) + Z).toNat) :
    ∃ c' k, Exec P W jfProg c c' k ∧ k ≤ 5 * m + 12 * (ml + mr) + 25 ∧
      (∀ i < m, (c'.nmem (OUTb + i) : ℤ) = Z + jfun Bl Br gl gr (e i)) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6260 ∨ 6279 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- stage 1: the fill
  obtain ⟨c₁, k₁, e₁, hk₁, s0, s1, s2, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W jfS1 c c₁ k₁ ∧ k₁ = 3 ∧ c₁.nreg 6260 = m ∧ c₁.nreg 6261 = OUTb ∧
      c₁.nreg 6262 = Z ∧ (∀ x, (x < 6260 ∨ 6262 < x) → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold jfS1
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r0, r7, r8])
    simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c₂, k₂, e₂, hk₂, o1, o2, o3, o4, o5, o6⟩ := lzProg_exec (P := P) c₁ e₁.wb_right s0 s1 s2
    (by omega) (by omega)
  have q2 : ∀ x, (x < 6260 ∨ 6279 < x) → c₂.nreg x = c.nreg x := fun x hx => by
    rw [o3 x (by omega), gn₁ x (by omega)]
  have m2 : ∀ a, OUTb + m ≤ a → c₂.nmem a = c.nmem a := fun a ha => by
    rw [o2 a (by omega), gm₁]
  -- stage 2: the left child
  obtain ⟨c₃, k₃, e₃, hk₃, t0, t1, t2, t3, t4, gn₃, gm₃, gr₃, grm₃, go₃⟩ : ∃ c₃ k₃,
      Exec P W jfS2 c₂ c₃ k₃ ∧ k₃ = 5 ∧ c₃.nreg 6270 = ml ∧ c₃.nreg 6271 = ILb ∧
      c₃.nreg 6272 = VLb ∧ c₃.nreg 6273 = Z ∧ c₃.nreg 6274 = OUTb ∧
      (∀ x, (x < 6270 ∨ 6274 < x) → c₃.nreg x = c₂.nreg x) ∧
      c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have hw₂ := e₂.wb_right
    unfold jfS2
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (rw [q2 _ (by omega)]; simp only [r1, r3, r4, r7, r8])
    simp only [upd_apply]; split_ifs <;> omega
  have hvl : ∀ j < ml, ((c.nmem (VLb + j) : ℕ) : ℤ) = gl (el j) + Z := fun j hj => by
    rw [hVL j hj, toNat_cast_of (by have := hgl (el j); omega)]
  have hvr : ∀ j < mr, ((c.nmem (VRb + j) : ℕ) : ℤ) = gr (er j) + Z := fun j hj => by
    rw [hVR j hj, toNat_cast_of (by have := hgr (er j); omega)]
  obtain ⟨c₄, k₄, e₄, hk₄, p1, p2, p3, p4, p5, p6⟩ := laProg_exec (P := P) c₃ e₃.wb_right t0 t1
    t2 t3 t4 (by omega) (by omega) (by omega)
    (fun j hj => by rw [gm₃, m2 _ (by omega)]; have := (hIL j hj).1; omega)
    (fun j hj => by
      rw [gm₃, m2 (ILb + j) (by omega), m2 (VLb + j) (by omega),
        o1 _ (hIL j hj).1]
      have := hvl j hj; have := hgl (el j); omega)
    (fun i hi j hj h => by
      rw [gm₃, m2 _ (by omega), m2 _ (by omega)] at h
      exact hel i hi j hj (by rw [← (hIL i hi).2, ← (hIL j hj).2, h]))
    (fun i hi j hj h => by rw [gm₃, m2 (ILb + i) (by omega)] at h; have := (hIL i hi).1; omega)
    (fun i hi j hj h => by rw [gm₃, m2 (ILb + i) (by omega)] at h; have := (hIL i hi).1; omega)
  rw [gm₃] at p1 p2
  -- the parent cells after the left child
  have ilv : ∀ j < ml, c₂.nmem (ILb + j) = c.nmem (ILb + j) := fun j hj => m2 _ (by omega)
  have left : ∀ i < m, ((c₄.nmem (OUTb + i) : ℕ) : ℤ) =
      Z + (if e i ∈ Bl then gl (e i) else 0) := fun i hi => by
    by_cases hb : e i ∈ Bl
    · obtain ⟨j, hj, hej⟩ := hBl i hi hb
      have hIj : c.nmem (ILb + j) = i := he _ (hIL j hj).1 i hi (by rw [(hIL j hj).2, hej])
      have := p1 j hj
      rw [ilv j hj, hIj, o1 i hi, m2 _ (by omega)] at this
      rw [this, iteT hb]
      have h1 := hvl j hj; rw [hej] at h1
      have := hgl (e i)
      omega
    · rw [iteF hb, p2 _ (fun j hj h => hb (by
        rw [ilv j hj] at h
        have : c.nmem (ILb + j) = i := by omega
        rw [← this, (hIL j hj).2]; exact hBl' j hj)), o1 i hi]
      ring
  have m4 : ∀ a, OUTb + m ≤ a → c₄.nmem a = c.nmem a := fun a ha => by
    rw [p2 a (fun j hj h => by rw [ilv j hj] at h; have := (hIL j hj).1; omega), m2 a ha]
  have q4 : ∀ x, (x < 6260 ∨ 6279 < x) → c₄.nreg x = c.nreg x := fun x hx => by
    rw [p3 x (by omega), gn₃ x (by omega), q2 x hx]
  -- stage 3: the right child
  obtain ⟨c₅, k₅, e₅, hk₅, u0, u1, u2, u3, u4, gn₅, gm₅, gr₅, grm₅, go₅⟩ : ∃ c₅ k₅,
      Exec P W jfS3 c₄ c₅ k₅ ∧ k₅ = 5 ∧ c₅.nreg 6270 = mr ∧ c₅.nreg 6271 = IRb ∧
      c₅.nreg 6272 = VRb ∧ c₅.nreg 6273 = Z ∧ c₅.nreg 6274 = OUTb ∧
      (∀ x, (x < 6270 ∨ 6274 < x) → c₅.nreg x = c₄.nreg x) ∧
      c₅.nmem = c₄.nmem ∧ c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    have hw₄ := e₄.wb_right
    unfold jfS3
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (rw [q4 _ (by omega)]; simp only [r2, r5, r6, r7, r8])
    simp only [upd_apply]; split_ifs <;> omega
  have irv : ∀ j < mr, c₄.nmem (IRb + j) = c.nmem (IRb + j) := fun j hj => m4 _ (by omega)
  obtain ⟨c₆, k₆, e₆, hk₆, v1, v2, v3, v4, v5, v6⟩ := laProg_exec (P := P) c₅ e₅.wb_right u0 u1
    u2 u3 u4 (by omega) (by omega) (by omega)
    (fun j hj => by rw [gm₅, irv j hj]; have := (hIR j hj).1; omega)
    (fun j hj => by
      rw [gm₅, irv j hj, m4 (VRb + j) (by omega)]
      have h1 := left _ (hIR j hj).1
      have h2 := hvr j hj; have := hgr (er j); have := hgl (e (c.nmem (IRb + j)))
      split_ifs at h1 <;> omega)
    (fun i hi j hj h => by
      rw [gm₅, irv i hi, irv j hj] at h
      exact her i hi j hj (by rw [← (hIR i hi).2, ← (hIR j hj).2, h]))
    (fun i hi j hj h => by rw [gm₅, irv i hi] at h; have := (hIR i hi).1; omega)
    (fun i hi j hj h => by rw [gm₅, irv i hi] at h; have := (hIR i hi).1; omega)
  rw [gm₅] at v1 v2
  refine ⟨c₆, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆)))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), by omega, fun i hi => ?_,
    fun a ha => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · unfold jfun
    by_cases hb : e i ∈ Br
    · obtain ⟨j, hj, hej⟩ := hBr i hi hb
      have hIj : c.nmem (IRb + j) = i := he _ (hIR j hj).1 i hi (by rw [(hIR j hj).2, hej])
      have := v1 j hj
      rw [irv j hj, hIj, m4 (VRb + j) (by omega)] at this
      rw [this, iteT hb]
      have h1 := hvr j hj; rw [hej] at h1
      have h2 := left i hi
      have := hgr (e i); have := hgl (e i)
      split_ifs at h2 ⊢ <;> omega
    · rw [iteF hb, v2 _ (fun j hj h => hb (by
        rw [irv j hj] at h
        have : c.nmem (IRb + j) = i := by omega
        rw [← this, (hIR j hj).2]; exact hBr' j hj)), left i hi]
      ring
  · rw [v2 a (fun j hj h => by rw [irv j hj] at h; have := (hIR j hj).1; omega),
      p2 a (fun j hj h => by rw [ilv j hj] at h; have := (hIL j hj).1; omega), o2 a ha, gm₁]
  · rw [v3 x (by omega), gn₅ x (by omega), q4 x hx]
  · rw [v4, gr₅, p4, gr₃, o4, gr₁]
  · rw [v5, grm₅, p5, grm₃, o5, grm₁]
  · rw [v6, go₅, p6, go₃, o6, go₁]

/-- **`f + cob χ` on the machine** (the last line of FixConservationOnPath, `fixPath`): with
`F[i] = (f (e i) + Z).toNat`, the face numbers `FR[i] = fi (face (rev (e i)))`,
`FC[i] = fi (face (e i))` (`fi y < nf`), the potential `PH[fi y] = (χ y + Zc).toNat`, layout
`F | FR | FC | PH | OUT`, within `17 m + 4` steps `(OUT[i] : ℤ) = Z + f (e i) + M.cob χ (e i)`;
memory outside `OUT`, registers outside `6286 … 6289`, reals and output kept. -/
theorem cbLoop_cob {D V F : Type*} (M : CombMap D V F) (c : Config) (hc : WordsBounded W c)
    {m nf Fb FRb FCb PHb OUTb Z Zc : ℕ}
    (r0 : c.nreg 6280 = m) (r1 : c.nreg 6281 = Fb) (r2 : c.nreg 6282 = FRb)
    (r3 : c.nreg 6283 = FCb) (r4 : c.nreg 6284 = PHb) (r5 : c.nreg 6285 = OUTb)
    (l1 : Fb + m ≤ FRb) (l2 : FRb + m ≤ FCb) (l3 : FCb + m ≤ PHb) (l4 : PHb + nf ≤ OUTb)
    (l5 : OUTb + m ≤ W) (hmW : m + 1 ≤ W)
    {e : ℕ → D} {fi : F → ℕ} {f : D → ℤ} {χ : F → ℤ} (hfi : ∀ y, fi y < nf)
    (hF : ∀ i < m, c.nmem (Fb + i) = (f (e i) + Z).toNat)
    (hFR : ∀ i < m, c.nmem (FRb + i) = fi (M.face (M.rev (e i))))
    (hFC : ∀ i < m, c.nmem (FCb + i) = fi (M.face (e i)))
    (hPH : ∀ y, c.nmem (PHb + fi y) = (χ y + Zc).toNat)
    (hb1 : ∀ i < m, -(Z : ℤ) ≤ f (e i)) (hb2 : ∀ y, -(Zc : ℤ) ≤ χ y)
    (hb3 : ∀ i < m, f (e i) + Z + (χ (M.face (M.rev (e i))) + Zc) ≤ W)
    (hb4 : ∀ i < m, 0 ≤ Z + f (e i) + M.cob χ (e i)) :
    ∃ c' k, Exec P W cbLoop c c' k ∧ k ≤ 17 * m + 4 ∧
      (∀ i < m, (c'.nmem (OUTb + i) : ℤ) = Z + f (e i) + M.cob χ (e i)) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6286 ∨ 6289 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have vF : ∀ i < m, ((c.nmem (Fb + i) : ℕ) : ℤ) = f (e i) + Z := fun i hi => by
    rw [hF i hi, toNat_cast_of (by have := hb1 i hi; omega)]
  have vP : ∀ y, ((c.nmem (PHb + fi y) : ℕ) : ℤ) = χ y + Zc := fun y => by
    rw [hPH y, toNat_cast_of (by have := hb2 y; omega)]
  obtain ⟨c', k, ex, hk, o1, o2, o3, o4, o5, o6⟩ := cbLoop_exec (P := P) c hc r0 r1 r2 r3 r4 r5
    (by omega) (by omega) (by omega) l5 hmW
    (fun j hj => by rw [hFR j hj]; have := hfi (M.face (M.rev (e j))); omega)
    (fun j hj => by rw [hFC j hj]; have := hfi (M.face (e j)); omega)
    (fun j hj => by
      rw [hFR j hj]
      have h1 := vF j hj; have h2 := vP (M.face (M.rev (e j))); have := hb3 j hj
      omega)
    (fun j hj h => by omega) (fun j hj h => by omega) (fun j hj h => by omega)
    (fun j hj h => by rw [hFR j hj] at h; have := hfi (M.face (M.rev (e j))); omega)
    (fun j hj h => by rw [hFC j hj] at h; have := hfi (M.face (e j)); omega)
  refine ⟨c', k, ex, hk, fun i hi => ?_, o2, o3, o4, o5, o6⟩
  rw [o1 i hi, hFR i hi, hFC i hi]
  have h1 := vF i hi
  have h2 := vP (M.face (M.rev (e i)))
  have h3 := vP (M.face (e i))
  have h4 := hb4 i hi
  unfold CombMap.cob at h4 ⊢
  omega

end Exec

end BKMNW

end PlanarFlow
