module

public import PlanarFlow.NegSSSP.LinGlue
public import PlanarFlow.NegSSSP.Step

/-!
# More bookkeeping of a node on the machine: the order `π` and the minima

* `permProg`: from two enumerations `β₀`, `β₁` of the same `b` vertex numbers (natural memory),
  the order `π` with `β₀ (π i) = β₁ i`, through an inverse table indexed by the vertex numbers
  (`permProg_exec`, `16 b + 6` steps).
* `minProg`: from two outcomes per vertex (flags and values), `(omin o₀ o₁).getD 0`
  (`minProg_exec`, `21 w + 3` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge

variable {P : Input} {W : ℕ}

/-! ### The order `π` -/

/-- First loop of `permProg`: `Inv[β₀ i] := i` (`r221` the base of `β₀`, `r223` of `Inv`). -/
def pInvBody : Stmt :=
  block [.addN 226 221 225, .loadN 227 226, .addN 226 223 227, .storeN 226 225, .addN 225 225 10]

/-- Second loop: `π[i] := Inv[β₁ i]` (`r222` the base of `β₁`, `r224` of `π`). -/
def pOutBody : Stmt :=
  block [.addN 226 222 225, .loadN 227 226, .addN 226 223 227, .loadN 228 226, .addN 226 224 225,
    .storeN 226 228, .addN 225 225 10]

/-- **The order `π`** (`r220 = b`). -/
def permProg : Stmt :=
  .seq (.instr (.constN 225 0)) <| .seq (.whileLtN 225 220 pInvBody) <|
  .seq (.instr (.constN 225 0)) (.whileLtN 225 220 pOutBody)

/-- The data of `permProg`. -/
structure PermIn (b B0 B1 Ib πb : ℕ) (β₀ β₁ : ℕ → ℕ) (c : Config) : Prop where
  r10 : c.nreg 10 = 1
  r220 : c.nreg 220 = b
  r221 : c.nreg 221 = B0
  r222 : c.nreg 222 = B1
  r223 : c.nreg 223 = Ib
  r224 : c.nreg 224 = πb
  b0 : ∀ i < b, c.nmem (B0 + i) = β₀ i
  b1 : ∀ i < b, c.nmem (B1 + i) = β₁ i

/-- The layout of `permProg`: `β₀`, `β₁` vertex numbers below `w`, `β₀` injective and `β₁`
in its range; the inverse table `[Ib, Ib + w)` and the output `[πb, πb + b)` apart from the
arrays read. -/
structure PermLay (b w B0 B1 Ib πb W : ℕ) (β₀ β₁ : ℕ → ℕ) : Prop where
  lt0 : ∀ i < b, β₀ i < w
  lt1 : ∀ i < b, β₁ i < w
  inj : ∀ i < b, ∀ j < b, β₀ i = β₀ j → i = j
  rng : ∀ i < b, ∃ j < b, β₀ j = β₁ i
  i0 : Ib + w ≤ B0 ∨ B0 + b ≤ Ib
  i1 : Ib + w ≤ B1 ∨ B1 + b ≤ Ib
  o1 : πb + b ≤ B1 ∨ B1 + b ≤ πb
  oi : πb + b ≤ Ib ∨ Ib + w ≤ πb
  w0 : B0 + b ≤ W
  w1 : B1 + b ≤ W
  wI : Ib + w ≤ W
  wO : πb + b ≤ W
  wb : b + 1 ≤ W

/-- The frame of `permProg`. -/
structure PFr (c c' : Config) : Prop where
  nreg : ∀ r, r < 225 ∨ 228 < r → c'.nreg r = c.nreg r
  rreg : c'.rreg = c.rreg
  rmem : c'.rmem = c.rmem
  out : c'.output = c.output

theorem PFr.trans {c c' c'' : Config} (h : PFr c c') (h' : PFr c' c'') : PFr c c'' :=
  ⟨fun r hr => (h'.nreg r hr).trans (h.nreg r hr), h'.rreg.trans h.rreg, h'.rmem.trans h.rmem,
    h'.out.trans h.out⟩

/-- **The order `π` on the machine.** `permProg` writes at `πb + i` (`i < b`) the index
`π i < b` with `β₀ (π i) = β₁ i`, within `16 b + 6` steps. -/
theorem permProg_exec {b w B0 B1 Ib πb : ℕ} {β₀ β₁ : ℕ → ℕ}
    (hL : PermLay b w B0 B1 Ib πb W β₀ β₁) (c : Config) (hc : WordsBounded W c)
    (hI : PermIn b B0 B1 Ib πb β₀ β₁ c) :
    ∃ c' k, Exec P W permProg c c' k ∧ k ≤ 16 * b + 6 ∧
      ((∀ i < b, c'.nmem (πb + i) < b ∧ β₀ (c'.nmem (πb + i)) = β₁ i) ∧
        (∀ a, (a < Ib ∨ Ib + w ≤ a) → (a < πb ∨ πb + b ≤ a) → c'.nmem a = c.nmem a) ∧
        PFr c c') := by
  have := hL.w0; have := hL.w1; have := hL.wI; have := hL.wO; have := hL.wb
  have := hL.i0; have := hL.i1; have := hL.o1; have := hL.oi
  unfold permProg
  refine spec_seq ?_
  refine spec_instr (Exec.constN hc 225 0 (by omega)) fun hw₁ => ?_
  -- the first loop
  let J : ℕ → Config → Prop := fun i c' =>
    PFr c c' ∧ (∀ a, (a < Ib ∨ Ib + w ≤ a) → c'.nmem a = c.nmem a) ∧
    (∀ j < i, c'.nmem (Ib + β₀ j) = j)
  have hJ0 : J 0 { c with nreg := upd c.nreg 225 0 } :=
    ⟨⟨fun r hr => upd_other _ _ _ (by omega), rfl, rfl, rfl⟩, fun _ _ => rfl,
      fun j hj => absurd hj (by omega)⟩
  refine spec_seq ?_
  refine spec_use (forLoop_exec (P := P) (a := 225) (bR := 220) (body := pInvBody) J (K := 5)
    (n := b) _ hw₁ (by config_simp) (by config_simp; exact hI.r220) hJ0
    (fun i c₁ hi hw ha hb ⟨fr, fo, fv⟩ => by
      have g : ∀ r, r < 225 → c₁.nreg r = c.nreg r := fun r hr => fr.nreg r (by omega)
      have e221 := (g 221 (by omega)).trans hI.r221
      have e223 := (g 223 (by omega)).trans hI.r223
      have e10 := (g 10 (by omega)).trans hI.r10
      have x0 : c₁.nmem (B0 + i) = β₀ i := by rw [fo _ (by omega)]; exact hI.b0 i hi
      have l0 := hL.lt0 i hi
      unfold pInvBody
      exec_block
      all_goals try ((try config_simp); (try simp only [e221, e223, e10, ha, x0]); omega)
      dsimp only [J]
      config_simp
      simp only [e221, e223, e10, ha, x0]
      and_intros
      all_goals try trivial
      · exact ⟨fun r hr => by simp only [upd_apply]; split_ifs <;> first | omega |
          exact fr.nreg r hr, fr.rreg, fr.rmem, fr.out⟩
      · intro a h1
        simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fo a h1]
      · intro j hj
        simp only [upd_apply]
        by_cases hji : j = i
        · subst hji; simp
        · have hne : β₀ j ≠ β₀ i := fun h => hji (hL.inj j (by omega) i hi h)
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fv j (by omega)])) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨_, fr₂, fo₂, fv₂⟩
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₂ 225 0 (by omega)) fun hw₃ => ?_
  -- the second loop
  let J' : ℕ → Config → Prop := fun i c' =>
    PFr c c' ∧ (∀ a, (a < πb ∨ πb + b ≤ a) → c'.nmem a = c₂.nmem a) ∧
    (∀ j < i, c'.nmem (πb + j) = c₂.nmem (Ib + β₁ j))
  have hJ0' : J' 0 { c₂ with nreg := upd c₂.nreg 225 0 } :=
    ⟨fr₂.trans ⟨fun r hr => upd_other _ _ _ (by omega), rfl, rfl, rfl⟩, fun _ _ => rfl,
      fun j hj => absurd hj (by omega)⟩
  refine spec_use (forLoop_exec (P := P) (a := 225) (bR := 220) (body := pOutBody) J' (K := 7)
    (n := b) _ hw₃ (by config_simp) (by config_simp; rw [fr₂.nreg 220 (by omega)]; exact hI.r220)
    hJ0' (fun i c₁ hi hw ha hb ⟨fr, fo, fv⟩ => by
      have g : ∀ r, r < 225 → c₁.nreg r = c.nreg r := fun r hr => fr.nreg r (by omega)
      have e222 := (g 222 (by omega)).trans hI.r222
      have e223 := (g 223 (by omega)).trans hI.r223
      have e224 := (g 224 (by omega)).trans hI.r224
      have e10 := (g 10 (by omega)).trans hI.r10
      have x1 : c₁.nmem (B1 + i) = β₁ i := by
        rw [fo _ (by omega), fo₂ _ (by omega)]; exact hI.b1 i hi
      have l1 := hL.lt1 i hi
      have xI : c₁.nmem (Ib + β₁ i) = c₂.nmem (Ib + β₁ i) := fo _ (by omega)
      have hv : c₂.nmem (Ib + β₁ i) ≤ W := by
        obtain ⟨j, hj, hjβ⟩ := hL.rng i hi
        rw [← hjβ, fv₂ j hj]; omega
      unfold pOutBody
      exec_block
      all_goals try ((try config_simp); (try simp only [e222, e223, e224, e10, ha, x1, xI]); omega)
      dsimp only [J']
      config_simp
      simp only [e222, e223, e224, e10, ha, x1, xI]
      and_intros
      all_goals try trivial
      · exact ⟨fun r hr => by simp only [upd_apply]; split_ifs <;> first | omega |
          exact fr.nreg r hr, fr.rreg, fr.rmem, fr.out⟩
      · intro a h1
        simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fo a h1]
      · intro j hj
        simp only [upd_apply]
        by_cases hji : j = i
        · subst hji; simp
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fv j (by omega)])) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨_, fr₄, fo₄, fv₄⟩
  refine ⟨by omega, fun i hi => ?_, fun a h1 h2 => ?_, fr₄⟩
  · obtain ⟨j, hj, hjβ⟩ := hL.rng i hi
    rw [fv₄ i hi, ← hjβ, fv₂ j hj]
    exact ⟨hj, rfl⟩
  · rw [fo₄ a h2]; show c₂.nmem a = _; exact fo₂ a h1

/-! ### The minima of the two runs of Dijkstra -/

/-- The least of two optional values, as in `NegSSSP.step`. -/
def ominR (o₀ o₁ : Option ℤ) : ℝ := ((omin o₀ o₁).getD 0 : ℤ)

/-- The choice: `r232 := (omin o₀ o₁).getD 0` from the flags `r237`, `r238` and the values
`r230`, `r231`. -/
def mSel : Stmt :=
  .ifLtN 237 10 (.ifLtN 238 10 (.instr (.constR 232 0)) (.instr (.copyR 232 231)))
    (.ifLtN 238 10 (.instr (.copyR 232 230))
      (.ifLtR 231 230 (.instr (.copyR 232 231)) (.instr (.copyR 232 230))))

theorem mSel_exec {o₀ o₁ : Option ℤ} (c : Config) (hc : WordsBounded W c) (h10 : c.nreg 10 = 1)
    (hf₀ : c.nreg 237 = if o₀.isSome then 1 else 0) (hf₁ : c.nreg 238 = if o₁.isSome then 1 else 0)
    (hv₀ : ∀ x, o₀ = some x → c.rreg 230 = x) (hv₁ : ∀ x, o₁ = some x → c.rreg 231 = x) :
    ∃ c' k, Exec P W mSel c c' k ∧ k ≤ 7 ∧
      c' = { c with rreg := upd c.rreg 232 (ominR o₀ o₁) } := by
  unfold mSel ominR
  cases o₀ with
  | none =>
    have t0 : c.nreg 237 < c.nreg 10 := by rw [hf₀, h10]; simp
    refine spec_ifLtN_true t0 ?_
    cases o₁ with
    | none =>
      have t1 : c.nreg 238 < c.nreg 10 := by rw [hf₁, h10]; simp
      refine spec_ifLtN_true t1 ?_
      refine spec_instr (Exec.constR hc 232 0) fun _ => ⟨by omega, by simp [omin]⟩
    | some y =>
      have t1 : ¬ c.nreg 238 < c.nreg 10 := by rw [hf₁, h10]; simp
      refine spec_ifLtN_false t1 ?_
      refine spec_instr (Exec.copyR hc 232 231) fun _ => ⟨by omega, by simp [omin, hv₁ y rfl]⟩
  | some x =>
    have t0 : ¬ c.nreg 237 < c.nreg 10 := by rw [hf₀, h10]; simp
    refine spec_ifLtN_false t0 ?_
    cases o₁ with
    | none =>
      have t1 : c.nreg 238 < c.nreg 10 := by rw [hf₁, h10]; simp
      refine spec_ifLtN_true t1 ?_
      refine spec_instr (Exec.copyR hc 232 230) fun _ => ⟨by omega, by simp [omin, hv₀ x rfl]⟩
    | some y =>
      have t1 : ¬ c.nreg 238 < c.nreg 10 := by rw [hf₁, h10]; simp
      refine spec_ifLtN_false t1 ?_
      by_cases hlt : c.rreg 231 < c.rreg 230
      · refine spec_ifLtR_true hlt ?_
        refine spec_instr (Exec.copyR hc 232 231) fun _ => ⟨by omega, ?_⟩
        rw [hv₀ x rfl, hv₁ y rfl] at hlt
        have : y < x := by exact_mod_cast hlt
        simp [omin, min_eq_right this.le, hv₁ y rfl]
      · refine spec_ifLtR_false hlt ?_
        refine spec_instr (Exec.copyR hc 232 230) fun _ => ⟨by omega, ?_⟩
        rw [hv₀ x rfl, hv₁ y rfl] at hlt
        have : x ≤ y := by exact_mod_cast not_lt.1 hlt
        simp [omin, min_eq_left this, hv₀ x rfl]

/-- The reads of `minProg` at the vertex `r236`: the flags, the values, the output address. -/
def mRead : Stmt :=
  block [.addN 239 231 236, .loadN 237 239, .addN 239 233 236, .loadN 238 239, .addN 239 232 236,
    .loadR 230 239, .addN 239 234 236, .loadR 231 239, .addN 239 235 236]

/-- `minProg` at the vertex `r236`. -/
def minBody : Stmt := .seq mRead (.seq mSel (block [.storeR 239 232, .addN 236 236 10]))

/-- **The minima of the two runs** over the vertices `0, …, r230 - 1`. -/
def minProg : Stmt := .seq (.instr (.constN 236 0)) (.whileLtN 236 230 minBody)

/-- The data of `minProg`: two outcomes `o₀`, `o₁` per vertex, as flags (natural memory) and
values (real memory). -/
structure MinIn (w F0 V0 F1 V1 Ob : ℕ) (o₀ o₁ : ℕ → Option ℤ) (c : Config) : Prop where
  r10 : c.nreg 10 = 1
  r230 : c.nreg 230 = w
  r231 : c.nreg 231 = F0
  r232 : c.nreg 232 = V0
  r233 : c.nreg 233 = F1
  r234 : c.nreg 234 = V1
  r235 : c.nreg 235 = Ob
  f0 : ∀ v < w, c.nmem (F0 + v) = if (o₀ v).isSome then 1 else 0
  f1 : ∀ v < w, c.nmem (F1 + v) = if (o₁ v).isSome then 1 else 0
  v0 : ∀ v < w, ∀ x, o₀ v = some x → c.rmem (V0 + v) = x
  v1 : ∀ v < w, ∀ x, o₁ v = some x → c.rmem (V1 + v) = x

/-- The layout of `minProg`: the output `[Ob, Ob + w)` apart from the values. -/
structure MinLay (w F0 V0 F1 V1 Ob W : ℕ) : Prop where
  o0 : Ob + w ≤ V0 ∨ V0 + w ≤ Ob
  o1 : Ob + w ≤ V1 ∨ V1 + w ≤ Ob
  w0 : F0 + w ≤ W
  w1 : F1 + w ≤ W
  wv0 : V0 + w ≤ W
  wv1 : V1 + w ≤ W
  wO : Ob + w ≤ W

theorem mRead_exec {w F0 V0 F1 V1 Ob : ℕ} {o₀ o₁ : ℕ → Option ℤ}
    (hL : MinLay w F0 V0 F1 V1 Ob W) (c : Config) (hc : WordsBounded W c)
    (hI : MinIn w F0 V0 F1 V1 Ob o₀ o₁ c) {v : ℕ} (hv : v < w) (h236 : c.nreg 236 = v) :
    ∃ c' k, Exec P W mRead c c' k ∧ k ≤ 9 ∧
      (c'.nreg 237 = (if (o₀ v).isSome then 1 else 0) ∧
        c'.nreg 238 = (if (o₁ v).isSome then 1 else 0) ∧ c'.nreg 239 = Ob + v ∧
        (∀ x, o₀ v = some x → c'.rreg 230 = x) ∧ (∀ x, o₁ v = some x → c'.rreg 231 = x) ∧
        (∀ r, r < 237 ∨ 239 < r → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 230 → r ≠ 231 → c'.rreg r = c.rreg r) ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧
        c'.output = c.output) := by
  have := hL.w0; have := hL.w1; have := hL.wv0; have := hL.wv1; have := hL.wO
  have x0 := hI.f0 v hv
  have x1 := hI.f1 v hv
  unfold mRead
  exec_block
  all_goals try ((try config_simp); (try simp only [hI.r231, hI.r232, hI.r233, hI.r234, hI.r235,
    h236, x0, x1]); (try split_ifs) <;> omega)
  config_simp
  simp only [hI.r231, hI.r232, hI.r233, hI.r234, hI.r235, h236, x0, x1]
  and_intros
  all_goals try trivial
  · exact fun x hx => hI.v0 v hv x hx
  · exact fun x hx => hI.v1 v hv x hx
  · intro r hr; simp only [upd_apply]; split_ifs <;> omega
  · intro r h1 h2; simp only [upd_apply]; split_ifs; rfl

/-- **The minima on the machine.** `minProg` writes `(omin (o₀ v) (o₁ v)).getD 0` at `Ob + v`
for every `v < w`, within `21 w + 3` steps. -/
theorem minProg_exec {w F0 V0 F1 V1 Ob : ℕ} {o₀ o₁ : ℕ → Option ℤ}
    (hL : MinLay w F0 V0 F1 V1 Ob W) (c : Config) (hc : WordsBounded W c)
    (hI : MinIn w F0 V0 F1 V1 Ob o₀ o₁ c) :
    ∃ c' k, Exec P W minProg c c' k ∧ k ≤ 21 * w + 3 ∧
      ((∀ v < w, c'.rmem (Ob + v) = ((omin (o₀ v) (o₁ v)).getD 0 : ℤ)) ∧
        (∀ a, (a < Ob ∨ Ob + w ≤ a) → c'.rmem a = c.rmem a) ∧ c'.nmem = c.nmem ∧
        (∀ r, r < 236 ∨ 239 < r → c'.nreg r = c.nreg r) ∧ c'.output = c.output) := by
  have := hL.wO; have := hL.o0; have := hL.o1
  unfold minProg
  refine spec_seq ?_
  refine spec_instr (Exec.constN hc 236 0 (by omega)) fun hw₁ => ?_
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ r, r < 236 ∨ 239 < r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
    (∀ a, (a < Ob ∨ Ob + w ≤ a) → c'.rmem a = c.rmem a) ∧
    (∀ v < i, c'.rmem (Ob + v) = ominR (o₀ v) (o₁ v)) ∧ c'.output = c.output
  have hJ0 : J 0 { c with nreg := upd c.nreg 236 0 } :=
    ⟨fun r hr => upd_other _ _ _ (by omega), rfl, fun _ _ => rfl, fun v hv => absurd hv (by omega),
      rfl⟩
  refine spec_use (forLoop_exec (P := P) (a := 236) (bR := 230) (body := minBody) J (K := 19)
    (n := w) _ hw₁ (by config_simp) (by config_simp; exact hI.r230) hJ0
    (fun i c₁ hi hw ha hb ⟨fn, fnm, frm, fv, fo⟩ => by
      have hI₁ : MinIn w F0 V0 F1 V1 Ob o₀ o₁ c₁ :=
        ⟨(fn 10 (by omega)).trans hI.r10, (fn 230 (by omega)).trans hI.r230,
          (fn 231 (by omega)).trans hI.r231, (fn 232 (by omega)).trans hI.r232,
          (fn 233 (by omega)).trans hI.r233, (fn 234 (by omega)).trans hI.r234,
          (fn 235 (by omega)).trans hI.r235, fun v hv => by rw [fnm]; exact hI.f0 v hv,
          fun v hv => by rw [fnm]; exact hI.f1 v hv,
          fun v hv x hx => by rw [frm _ (by omega)]; exact hI.v0 v hv x hx,
          fun v hv x hx => by rw [frm _ (by omega)]; exact hI.v1 v hv x hx⟩
      unfold minBody
      refine spec_seq ?_
      refine spec_use (mRead_exec (P := P) hL c₁ hw hI₁ hi ha) ?_
      intro c₂ k₂ hk₂ hw₂ ⟨g237, g238, g239, gv0, gv1, gn, gr, gnm, grm, go⟩
      refine spec_seq ?_
      refine spec_use (mSel_exec (P := P) c₂ hw₂ (by rw [gn 10 (by omega)]; exact hI₁.r10)
        g237 g238 gv0 gv1) ?_
      intro c₃ k₃ hk₃ hw₃ hc₃
      subst hc₃
      have k236 : c₂.nreg 236 = i := (gn 236 (by omega)).trans ha
      have k10 : c₂.nreg 10 = 1 := (gn 10 (by omega)).trans hI₁.r10
      exec_block
      all_goals try ((try config_simp); (try simp only [k236, k10]); omega)
      dsimp only [J]
      config_simp
      simp only [g239, k236, k10]
      and_intros
      all_goals try trivial
      · omega
      · rw [gn 230 (by omega), hb]
      · intro r hr; simp only [upd_apply]; split_ifs
        · omega
        · rw [gn r (by omega), fn r hr]
      · rw [gnm, fnm]
      · intro a h1
        simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), grm, frm a h1]
      · intro v hv
        simp only [upd_apply]
        by_cases hvi : v = i
        · subst hvi; simp
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), grm, fv v (by omega)]
      · rw [go, fo])) ?_
  intro c₄ k₄ hk₄ _ ⟨_, fn, fnm, frm, fv, fo⟩
  exact ⟨by omega, fun v hv => fv v hv, frm, fnm, fn, fo⟩

end NegSSSP

end PlanarFlow
