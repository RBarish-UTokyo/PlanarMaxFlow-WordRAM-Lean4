module

public import PlanarFlow.NegSSSP.LinGlue

/-!
# The arithmetic before the calls of Dijkstra of a node, on the machine

After Bellman–Ford, a step of the recursion (`NegSSSP.step`) lowers the boundary values by
`C = Σ_B |E - δ₀| + |E - δ₁|` and calls Dijkstra in each part with the initial lengths
`initLen B (E - C) δᵢ` and the prices `price B (E - C) δᵢ` (the root: `Σ_B |δᵢ - (E - C)|`).
On the machine (`E i` the value of the `i`-th boundary vertex, real memory; `n i` its vertex
number; `δᵢ` by vertex number, real memory):

* `absAdd_exec`: `acc += |x|` by a real comparison with `0` (`ifLtR`).
* `cProg_exec`: `C` (within `21 b + 6` steps).
* `pProg_exec`: for one part, the initial lengths by vertex number (`δ v`, overwritten by
  `E i - C` at `n i`), the prices (`p (v + 1) = δ v`) and the price of the root at `p 0`
  (within `10 w + 17 b + 11` steps). The vertex numbers `n i` of the boundary vertices
  are injective; `NegSSSP.arith_node` (`PlanarFlow/BKMNW/FRDijNum.lean`) reads the outputs as
  `C`, `initLen` and `price` of `NegSSSP.step`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- `acc += |x|` (real registers `acc`, `x`, scratch `t`, `z = 0`). -/
def absAdd (acc x t z : ℕ) : Stmt :=
  .ifLtR x z (block [.subR t z x, .addR acc acc t]) (block [.addR acc acc x])

theorem absAdd_exec {acc x t z : ℕ} (h1 : acc ≠ x) (h2 : acc ≠ t) (h3 : acc ≠ z) (h4 : x ≠ t)
    (h5 : t ≠ z) (c : Config) (hc : WordsBounded W c) (hz : c.rreg z = 0) :
    ∃ c' k, Exec P W (absAdd acc x t z) c c' k ∧ k ≤ 4 ∧
      (c'.rreg acc = c.rreg acc + |c.rreg x| ∧
        (∀ r, r ≠ acc → r ≠ t → c'.rreg r = c.rreg r) ∧ c'.nreg = c.nreg ∧ c'.nmem = c.nmem ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold absAdd
  by_cases hx : c.rreg x < c.rreg z
  · refine spec_ifLtR_true hx ?_
    exec_block
    refine ⟨by omega, ?_, fun r hr ht => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [upd_apply, h2, h4.symm, ↓reduceIte]
      rw [hz] at hx ⊢
      rw [abs_of_neg hx]; ring
    · simp only [upd_apply, hr, ht, ↓reduceIte]
  · refine spec_ifLtR_false hx ?_
    exec_block
    refine ⟨by omega, ?_, fun r hr ht => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [upd_apply, ↓reduceIte]
      rw [hz] at hx
      rw [abs_of_nonneg (not_lt.1 hx)]
    · simp only [upd_apply, hr, ↓reduceIte]

/-! ### The lowering `C` -/

/-- The reads of the pair `i = r511` of `C`: `E i - δ₀ (n i)` into the real `502`,
`E i - δ₁ (n i)` into the real `506`. -/
def cRead : Stmt := block [.addN 512 502 511, .loadN 513 512, .addN 512 501 511, .loadR 504 512,
  .addN 512 503 513, .loadR 505 512, .subR 502 504 505, .addN 512 504 513, .loadR 505 512,
  .subR 506 504 505]

/-- The term of the pair `i` of `C`. -/
def cBody : Stmt :=
  .seq cRead <| .seq (absAdd 500 502 503 501) <| .seq (absAdd 500 506 503 501)
    (block [.addN 511 511 510])

/-- **The lowering** `C = Σ_{i < b} |E i - δ₀ (n i)| + |E i - δ₁ (n i)|` into the real
register `500` (`r500 = b`, `r501` the base of `E` (real), `r502` of `n` (natural), `r503`,
`r504` of `δ₀`, `δ₁` (real)). -/
def cProg : Stmt :=
  .seq (block [.constR 500 0, .constR 501 0, .constN 510 1, .constN 511 0])
    (.whileLtN 511 500 cBody)

/-- The data of `cProg`. -/
structure CIn (b w Eb Nb D0 D1 : ℕ) (n : ℕ → ℕ) (Ev d0 d1 : ℕ → ℝ) (c : Config) : Prop where
  r500 : c.nreg 500 = b
  r501 : c.nreg 501 = Eb
  r502 : c.nreg 502 = Nb
  r503 : c.nreg 503 = D0
  r504 : c.nreg 504 = D1
  nb : ∀ i < b, c.nmem (Nb + i) = n i
  ev : ∀ i < b, c.rmem (Eb + i) = Ev i
  δ0 : ∀ v < w, c.rmem (D0 + v) = d0 v
  δ1 : ∀ v < w, c.rmem (D1 + v) = d1 v

/-- The layout of `cProg`. -/
structure CLay (b w Eb Nb D0 D1 W : ℕ) (n : ℕ → ℕ) : Prop where
  lt : ∀ i < b, n i < w
  wE : Eb + b ≤ W
  wN : Nb + b ≤ W
  w0 : D0 + w ≤ W
  w1 : D1 + w ≤ W
  wb : b + 1 ≤ W

theorem cRead_exec {b w Eb Nb D0 D1 : ℕ} {n : ℕ → ℕ} {Ev d0 d1 : ℕ → ℝ}
    (hL : CLay b w Eb Nb D0 D1 W n) (c : Config) (hc : WordsBounded W c)
    (hI : CIn b w Eb Nb D0 D1 n Ev d0 d1 c) {i : ℕ} (hi : i < b) (h511 : c.nreg 511 = i) :
    ∃ c' k, Exec P W cRead c c' k ∧ k ≤ 10 ∧
      (c'.rreg 502 = Ev i - d0 (n i) ∧ c'.rreg 506 = Ev i - d1 (n i) ∧
        (∀ r, r ≠ 502 → r ≠ 504 → r ≠ 505 → r ≠ 506 → c'.rreg r = c.rreg r) ∧
        (∀ r, r ≠ 512 → r ≠ 513 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wE; have := hL.wN; have := hL.w0; have := hL.w1
  have hlt := hL.lt i hi
  have xn := hI.nb i hi
  have a1 := hI.r501; have a2 := hI.r502; have a3 := hI.r503; have a4 := hI.r504
  unfold cRead
  exec_block
  all_goals try ((try config_simp); (try simp only [a1, a2, a3, a4, h511, xn]); omega)
  config_simp
  simp only [hI.r501, hI.r502, hI.r503, hI.r504, h511, xn, hI.ev i hi, hI.δ0 _ hlt,
    hI.δ1 _ hlt]
  and_intros
  all_goals first
    | trivial
    | omega
    | rfl
    | (intro r h1 h2 h3 h4; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
    | (intro r h1 h2; simp only [upd_apply]; split_ifs <;> first | omega | rfl)

theorem cProg_exec {b w Eb Nb D0 D1 : ℕ} {n : ℕ → ℕ} {Ev d0 d1 : ℕ → ℝ}
    (hL : CLay b w Eb Nb D0 D1 W n) (c : Config) (hc : WordsBounded W c)
    (hI : CIn b w Eb Nb D0 D1 n Ev d0 d1 c) :
    ∃ c' k, Exec P W cProg c c' k ∧ k ≤ 21 * b + 6 ∧
      (c'.rreg 500 = ∑ i ∈ Finset.range b, (|Ev i - d0 (n i)| + |Ev i - d1 (n i)|) ∧
        (∀ r, r < 510 ∨ 513 < r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wE; have := hL.wN; have := hL.w0; have := hL.w1; have := hL.wb
  unfold cProg
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    c'.rreg 500 = ∑ j ∈ Finset.range i, (|Ev j - d0 (n j)| + |Ev j - d1 (n j)|) ∧
      c'.rreg 501 = 0 ∧ c'.nreg 510 = 1 ∧ (∀ r, r < 510 ∨ 513 < r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 511) (bR := 500) (body := cBody) J (K := 19)
    (n := b) _ ‹_› (by config_simp) (by config_simp; exact hI.r500) ?_
    (fun i c₁ hi hw ha hb ⟨g500, g501, g510, gn, gnm, grm, go⟩ => by
      have hI₁ : CIn b w Eb Nb D0 D1 n Ev d0 d1 c₁ :=
        ⟨(gn 500 (by omega)).trans hI.r500, (gn 501 (by omega)).trans hI.r501,
          (gn 502 (by omega)).trans hI.r502, (gn 503 (by omega)).trans hI.r503,
          (gn 504 (by omega)).trans hI.r504, fun j hj => by rw [gnm]; exact hI.nb j hj,
          fun j hj => by rw [grm]; exact hI.ev j hj, fun v hv => by rw [grm]; exact hI.δ0 v hv,
          fun v hv => by rw [grm]; exact hI.δ1 v hv⟩
      unfold cBody
      refine spec_seq ?_
      refine spec_use (cRead_exec (P := P) hL c₁ hw hI₁ hi ha) ?_
      intro c₂ k₂ hk₂ hw₂ ⟨a502, a506, ar, an, anm, arm, ao⟩
      refine spec_seq ?_
      refine spec_use (absAdd_exec (P := P) (acc := 500) (x := 502) (t := 503) (z := 501)
        (by decide) (by decide) (by decide) (by decide) (by decide) c₂ hw₂
        (by rw [ar 501 (by decide) (by decide) (by decide) (by decide)]; exact g501)) ?_
      intro c₃ k₃ hk₃ hw₃ ⟨b500, br, bn, bnm, brm, bo⟩
      refine spec_seq ?_
      refine spec_use (absAdd_exec (P := P) (acc := 500) (x := 506) (t := 503) (z := 501)
        (by decide) (by decide) (by decide) (by decide) (by decide) c₃ hw₃
        (by rw [br 501 (by decide) (by decide), ar 501 (by decide) (by decide) (by decide)
          (by decide)]; exact g501)) ?_
      intro c₄ k₄ hk₄ hw₄ ⟨d500, dr, dn, dnm, drm, d_o⟩
      have h511 : c₄.nreg 511 = i := by rw [dn, bn, an 511 (by decide) (by decide)]; exact ha
      have h510 : c₄.nreg 510 = 1 := by rw [dn, bn, an 510 (by decide) (by decide)]; exact g510
      have h500 : c₄.rreg 500 = c₁.rreg 500 + |Ev i - d0 (n i)| + |Ev i - d1 (n i)| := by
        rw [d500, b500, br 506 (by decide) (by decide), a506, a502,
          ar 500 (by decide) (by decide) (by decide) (by decide)]
      have h501 : c₄.rreg 501 = 0 := by
        rw [dr 501 (by decide) (by decide), br 501 (by decide) (by decide),
          ar 501 (by decide) (by decide) (by decide) (by decide), g501]
      exec_block
      all_goals try ((try config_simp); (try simp only [h511, h510]); omega)
      dsimp only [J]
      config_simp
      simp only [h511, h510, h500, h501]
      refine ⟨by omega, trivial, by rw [dn, bn, an 500 (by decide) (by decide)]; exact hb, ?_,
        trivial, trivial, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [Finset.sum_range_succ, g500]; ring
      · simp only [upd_apply]
        split_ifs
        · omega
        · rw [dn, bn, an r (by omega) (by omega), gn r hr]
      · rw [dnm, bnm, anm, gnm]
      · rw [drm, brm, arm, grm]
      · rw [d_o, bo, ao, go])) ?_
  · refine ⟨?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    · simp
    · simp
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, g500, -, -, gn, gnm, grm, go⟩ := hJ₂
  exact ⟨by omega, g500, gn, gnm, grm, go⟩

/-! ### The initial lengths and the prices of a part -/

/-- The copy of `δ v` into the initial lengths `I[v]` and the prices `p[v + 1]`. -/
def pCopy : Stmt := block [.addN 512 506 511, .loadR 502 512, .addN 512 507 511, .storeR 512 502,
  .addN 512 508 511, .addN 512 512 510, .storeR 512 502, .addN 511 511 510]

/-- The boundary vertex `i = r511`: `I[n i] := E i - C`, and `δ (n i) - (E i - C)` into the
real `502`. -/
def pRead : Stmt := block [.addN 512 502 511, .loadN 513 512, .addN 512 501 511, .loadR 504 512,
  .subR 504 504 500, .addN 512 507 513, .storeR 512 504, .addN 512 506 513, .loadR 505 512,
  .subR 502 505 504]

/-- The boundary vertex `i`, with the price of the root. -/
def pBody : Stmt := .seq pRead (.seq (absAdd 507 502 503 501) (block [.addN 511 511 510]))

/-- **The initial lengths and the prices of a part** (`r500 = b`, `r501` the base of `E`,
`r502` of `n`, `r505 = w`, `r506` the base of `δ`, `r507` of the initial lengths, `r508` of the
prices; the real `500` is `C`). -/
def pProg : Stmt :=
  .seq (block [.constR 501 0, .constN 510 1, .constN 511 0]) <|
  .seq (.whileLtN 511 505 pCopy) <|
  .seq (block [.constR 507 0, .constN 511 0]) <|
  .seq (.whileLtN 511 500 pBody) (block [.copyN 512 508, .storeR 512 507])

/-- The data of `pProg`. -/
structure PIn (b w Eb Nb δb Ib Pb : ℕ) (n : ℕ → ℕ) (Ev δ : ℕ → ℝ) (C : ℝ) (c : Config) :
    Prop where
  r500 : c.nreg 500 = b
  r501 : c.nreg 501 = Eb
  r502 : c.nreg 502 = Nb
  r505 : c.nreg 505 = w
  r506 : c.nreg 506 = δb
  r507 : c.nreg 507 = Ib
  r508 : c.nreg 508 = Pb
  rC : c.rreg 500 = C
  nb : ∀ i < b, c.nmem (Nb + i) = n i
  ev : ∀ i < b, c.rmem (Eb + i) = Ev i
  pt : ∀ v < w, c.rmem (δb + v) = δ v

/-- The layout of `pProg`. -/
structure PLay (b w Eb Nb δb Ib Pb W : ℕ) (n : ℕ → ℕ) : Prop where
  lt : ∀ i < b, n i < w
  inj : ∀ i < b, ∀ j < b, n i = n j → i = j
  iD : Ib + w ≤ δb ∨ δb + w ≤ Ib
  iE : Ib + w ≤ Eb ∨ Eb + b ≤ Ib
  pD : Pb + w + 1 ≤ δb ∨ δb + w ≤ Pb
  pE : Pb + w + 1 ≤ Eb ∨ Eb + b ≤ Pb
  ip : Ib + w ≤ Pb ∨ Pb + w + 1 ≤ Ib
  wE : Eb + b ≤ W
  wN : Nb + b ≤ W
  wD : δb + w ≤ W
  wI : Ib + w ≤ W
  wP : Pb + w + 1 ≤ W
  wb : b + 1 ≤ W

theorem pRead_exec {b w Eb Nb δb Ib Pb : ℕ} {n : ℕ → ℕ} {Ev δ : ℕ → ℝ} {C : ℝ}
    (hL : PLay b w Eb Nb δb Ib Pb W n) (c : Config) (hc : WordsBounded W c)
    (hI : PIn b w Eb Nb δb Ib Pb n Ev δ C c) {i : ℕ} (hi : i < b) (h511 : c.nreg 511 = i) :
    ∃ c' k, Exec P W pRead c c' k ∧ k ≤ 10 ∧
      (c'.rreg 502 = δ (n i) - (Ev i - C) ∧ c'.rmem = upd c.rmem (Ib + n i) (Ev i - C) ∧
        (∀ r, r ≠ 502 → r ≠ 504 → r ≠ 505 → c'.rreg r = c.rreg r) ∧
        (∀ r, r ≠ 512 → r ≠ 513 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
        c'.output = c.output) := by
  have := hL.wE; have := hL.wN; have := hL.wD; have := hL.wI; have := hL.iD; have := hL.iE
  have hlt := hL.lt i hi
  have xn := hI.nb i hi
  have a1 := hI.r501; have a2 := hI.r502; have a6 := hI.r506; have a7 := hI.r507
  have xe := hI.ev i hi
  have xd := hI.pt _ hlt
  unfold pRead
  exec_block
  all_goals try ((try config_simp); (try simp only [a1, a2, a6, a7, h511, xn]); omega)
  config_simp
  simp only [a1, a2, a6, a7, h511, xn, xe, hI.rC]
  have hne : δb + n i ≠ Ib + n i := by omega
  rw [upd_other _ _ _ hne, xd]
  and_intros
  all_goals first
    | trivial
    | omega
    | rfl
    | (intro r h1 h2 h3; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
    | (intro r h1 h2; simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-- **The initial lengths and the prices of a part on the machine.** From `PIn` (with `PLay`),
`pProg` writes `I[n i] = E i - C` for the boundary vertices `i < b`, `I[v] = δ v` for the other
`v < w`, the prices `p[v + 1] = δ v` and `p[0] = Σ_{i < b} |δ (n i) - (E i - C)|`, within
`10 w + 17 b + 11` steps. -/
theorem pProg_exec {b w Eb Nb δb Ib Pb : ℕ} {n : ℕ → ℕ} {Ev δ : ℕ → ℝ} {C : ℝ}
    (hL : PLay b w Eb Nb δb Ib Pb W n) (c : Config) (hc : WordsBounded W c)
    (hI : PIn b w Eb Nb δb Ib Pb n Ev δ C c) :
    ∃ c' k, Exec P W pProg c c' k ∧ k ≤ 10 * w + 17 * b + 11 ∧
      ((∀ i < b, c'.rmem (Ib + n i) = Ev i - C) ∧
        (∀ v < w, (∀ i < b, n i ≠ v) → c'.rmem (Ib + v) = δ v) ∧
        (∀ v < w, c'.rmem (Pb + (v + 1)) = δ v) ∧
        c'.rmem Pb = ∑ i ∈ Finset.range b, |δ (n i) - (Ev i - C)| ∧
        (∀ a, (a < Ib ∨ Ib + w ≤ a) → (a < Pb ∨ Pb + w + 1 ≤ a) → c'.rmem a = c.rmem a) ∧
        c'.nmem = c.nmem ∧ (∀ r, r < 510 ∨ 513 < r → c'.nreg r = c.nreg r) ∧
        c'.output = c.output) := by
  have := hL.wE; have := hL.wN; have := hL.wD; have := hL.wI; have := hL.wP; have := hL.wb
  have := hL.iD; have := hL.iE; have := hL.pD; have := hL.pE; have := hL.ip
  have hw1 : w + 1 ≤ W := by omega
  unfold pProg
  refine spec_seq ?_
  exec_block
  all_goals try omega
  refine spec_seq ?_
  -- the copies
  let J : ℕ → Config → Prop := fun v c' =>
    (∀ u < v, c'.rmem (Ib + u) = δ u ∧ c'.rmem (Pb + (u + 1)) = δ u) ∧
      (∀ a, (a < Ib ∨ Ib + w ≤ a) → (a < Pb ∨ Pb + w + 1 ≤ a) → c'.rmem a = c.rmem a) ∧
      c'.rreg 500 = C ∧ c'.rreg 501 = 0 ∧ c'.nreg 510 = 1 ∧
      (∀ r, r < 510 ∨ 513 < r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 511) (bR := 505) (body := pCopy) J (K := 8)
    (n := w) _ ‹_› (by config_simp) (by config_simp; exact hI.r505) ?_
    (fun v c₁ hv hw ha hb ⟨g, gm, g500, g501, g510, gn, gnm, go⟩ => by
      have e506 : c₁.nreg 506 = δb := (gn 506 (by omega)).trans hI.r506
      have e507 : c₁.nreg 507 = Ib := (gn 507 (by omega)).trans hI.r507
      have e508 : c₁.nreg 508 = Pb := (gn 508 (by omega)).trans hI.r508
      have xd : c₁.rmem (δb + v) = δ v := by rw [gm _ (by omega) (by omega)]; exact hI.pt v hv
      unfold pCopy
      exec_block
      all_goals try ((try config_simp); (try simp only [e506, e507, e508, ha, g510]); omega)
      dsimp only [J]
      config_simp
      simp only [e506, e507, e508, ha, g510, xd]
      refine ⟨by omega, trivial, hb, fun u hu => ?_, fun a h1 h2 => ?_, g500, g501, trivial,
        fun r hr => ?_, gnm, go⟩
      · simp only [upd_apply]
        by_cases huv : u = v
        · subst huv
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
            ite_eq_left_of_eq_true _ _ (eq_true rfl),
            ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
          exact ⟨rfl, rfl⟩
        · obtain ⟨g1, g2⟩ := g u (by omega)
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
            ite_eq_right_of_eq_false _ _ (eq_false (by omega)), g1,
            ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
            ite_eq_right_of_eq_false _ _ (eq_false (by omega)), g2]
          exact ⟨rfl, rfl⟩
      · simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gm a h1 h2]
      · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr)) ?_
  · refine ⟨fun u hu => absurd hu (by omega), fun _ _ _ => rfl, ?_, ?_, ?_, fun r hr => ?_, rfl,
      rfl⟩
    all_goals config_simp
    · exact hI.rC
    · simp
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
  intro c₂ k₂ hk₂ hw₂ hJ₂
  obtain ⟨_, g, gm, g500, g501, g510, gn, gnm, go⟩ := hJ₂
  refine spec_seq ?_
  exec_block
  all_goals try omega
  refine spec_seq ?_
  -- the boundary vertices
  let J' : ℕ → Config → Prop := fun i c' =>
    c'.rreg 507 = ∑ j ∈ Finset.range i, |δ (n j) - (Ev j - C)| ∧
      (∀ j < i, c'.rmem (Ib + n j) = Ev j - C) ∧
      (∀ v < w, (∀ j < i, n j ≠ v) → c'.rmem (Ib + v) = δ v) ∧
      (∀ u < w, c'.rmem (Pb + (u + 1)) = δ u) ∧
      (∀ a, (a < Ib ∨ Ib + w ≤ a) → (a < Pb ∨ Pb + w + 1 ≤ a) → c'.rmem a = c.rmem a) ∧
      c'.rreg 500 = C ∧ c'.rreg 501 = 0 ∧ c'.nreg 510 = 1 ∧
      (∀ r, r < 510 ∨ 513 < r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 511) (bR := 500) (body := pBody) J' (K := 15)
    (n := b) _ ‹_› (by config_simp) (by config_simp; rw [gn 500 (by omega)]; exact hI.r500) ?_
    (fun i c₁ hi hw ha hb ⟨f507, fI, fO, fP, fm, f500, f501, f510, fn, fnm, fo⟩ => by
      have hI₁ : PIn b w Eb Nb δb Ib Pb n Ev δ C c₁ :=
        ⟨(fn 500 (by omega)).trans hI.r500, (fn 501 (by omega)).trans hI.r501,
          (fn 502 (by omega)).trans hI.r502, (fn 505 (by omega)).trans hI.r505,
          (fn 506 (by omega)).trans hI.r506, (fn 507 (by omega)).trans hI.r507,
          (fn 508 (by omega)).trans hI.r508, f500, fun j hj => by rw [fnm]; exact hI.nb j hj,
          fun j hj => by rw [fm _ (by omega) (by omega)]; exact hI.ev j hj,
          fun v hv => by rw [fm _ (by omega) (by omega)]; exact hI.pt v hv⟩
      have hlt := hL.lt i hi
      unfold pBody
      refine spec_seq ?_
      refine spec_use (pRead_exec (P := P) hL c₁ hw hI₁ hi ha) ?_
      intro c₂ k₂ hk₂ hw₂ ⟨a502, arm, ar, an, anm, ao⟩
      refine spec_seq ?_
      refine spec_use (absAdd_exec (P := P) (acc := 507) (x := 502) (t := 503) (z := 501)
        (by decide) (by decide) (by decide) (by decide) (by decide) c₂ hw₂
        (by rw [ar 501 (by decide) (by decide) (by decide)]; exact f501)) ?_
      intro c₃ k₃ hk₃ hw₃ ⟨b507, br, bn, bnm, brm, bo⟩
      have h511 : c₃.nreg 511 = i := by rw [bn, an 511 (by decide) (by decide)]; exact ha
      have h510 : c₃.nreg 510 = 1 := by rw [bn, an 510 (by decide) (by decide)]; exact f510
      exec_block
      all_goals try ((try config_simp); (try simp only [h511, h510]); omega)
      dsimp only [J']
      config_simp
      simp only [h511, h510]
      refine ⟨by omega, trivial, by rw [bn, an 500 (by decide) (by decide)]; exact hb, ?_,
        fun j hj => ?_, fun v hv hv' => ?_, fun u hu => ?_, fun a h1 h2 => ?_, ?_, ?_, trivial,
        fun r hr => ?_, ?_, ?_⟩
      · rw [b507, a502, ar 507 (by decide) (by decide) (by decide), f507, Finset.sum_range_succ]
      · rw [brm, arm]
        simp only [upd_apply]
        by_cases hji : j = i
        · subst hji; simp
        · have : n j ≠ n i := fun h => hji (hL.inj j (by omega) i hi h)
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fI j (by omega)]
      · rw [brm, arm]
        simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by have := hv' i (by omega); omega)),
          fO v hv fun j hj => hv' j (by omega)]
      · rw [brm, arm]
        simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fP u hu]
      · rw [brm, arm]
        simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fm a h1 h2]
      · rw [br 500 (by decide) (by decide), ar 500 (by decide) (by decide) (by decide), f500]
      · rw [br 501 (by decide) (by decide), ar 501 (by decide) (by decide) (by decide), f501]
      · simp only [upd_apply]
        split_ifs
        · omega
        · rw [bn, an r (by omega) (by omega), fn r hr]
      · rw [bnm, anm, fnm]
      · rw [bo, ao, fo])) ?_
  · refine ⟨?_, fun j hj => absurd hj (by omega), fun v hv _ => (g v hv).1,
      fun u hu => (g u hu).2, gm, ?_, ?_, ?_, fun r hr => ?_, gnm, go⟩
    all_goals config_simp
    · simp
    · exact g500
    · exact g501
    · exact g510
    · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr
  intro c₄ k₄ hk₄ hw₄ hJ₄
  obtain ⟨_, h507, hIb, hO, hP, hm, -, -, -, hn, hnm, ho⟩ := hJ₄
  have e508 : c₄.nreg 508 = Pb := (hn 508 (by omega)).trans hI.r508
  exec_block
  config_simp
  simp only [e508, h507]
  refine ⟨by omega, fun i hi => ?_, fun v hv hv' => ?_, fun u hu => ?_, by simp, fun a h1 h2 => ?_,
    hnm, fun r hr => ?_, ho⟩
  · simp only [upd_apply]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by have := hL.lt i hi; omega)), hIb i hi]
  · simp only [upd_apply]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hO v hv hv']
  · simp only [upd_apply]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hP u hu]
  · simp only [upd_apply]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hm a h1 h2]
  · simp only [upd_apply]; split_ifs <;> first | omega | exact hn r hr

/-! ### The flags of a run of Dijkstra, normalized -/

/-- The vertex `v = r611`: `F[v] := [S[v] = 1]`, `V[v] := D[v]` (`r601` the base of the settled
flags `S`, `r602` of the distances `D` (real), `r603` of `F`, `r604` of `V` (real)). -/
def nBody : Stmt :=
  .seq (block [.addN 612 601 611, .loadN 613 612, .constN 614 0]) <|
  .seq (.ifLtN 613 610 .skip (.ifLtN 610 613 .skip (.instr (.copyN 614 610)))) <|
  block [.addN 612 603 611, .storeN 612 614, .addN 612 602 611, .loadR 600 612,
    .addN 612 604 611, .storeR 612 600, .addN 611 611 610]

/-- **The normalization of the flags** of a run over the vertices `0, …, r600 - 1`. -/
def nrmProg : Stmt := .seq (block [.constN 610 1, .constN 611 0]) (.whileLtN 611 600 nBody)

/-- The layout of `nrmProg`. -/
structure NrmLay (w Sb Db Fb Vb W : ℕ) : Prop where
  fs : Fb + w ≤ Sb ∨ Sb + w ≤ Fb
  vd : Vb + w ≤ Db ∨ Db + w ≤ Vb
  wS : Sb + w ≤ W
  wD : Db + w ≤ W
  wF : Fb + w ≤ W
  wV : Vb + w ≤ W
  ww : w + 1 ≤ W

/-- **The flags of a run, normalized to `0`/`1`.** With `r600 = w` and the bases in
`r601 … r604`, `nrmProg` writes `[S[v] = 1]` at `Fb + v` and `D[v]` at `Vb + v` for `v < w`, within
`17 w + 4` steps. -/
theorem nrmProg_exec {w Sb Db Fb Vb : ℕ} (hL : NrmLay w Sb Db Fb Vb W) (c : Config)
    (hc : WordsBounded W c) (h600 : c.nreg 600 = w) (h601 : c.nreg 601 = Sb)
    (h602 : c.nreg 602 = Db) (h603 : c.nreg 603 = Fb) (h604 : c.nreg 604 = Vb) :
    ∃ c' k, Exec P W nrmProg c c' k ∧ k ≤ 17 * w + 4 ∧
      ((∀ v < w, c'.nmem (Fb + v) = (if c.nmem (Sb + v) = 1 then 1 else 0) ∧
          c'.rmem (Vb + v) = c.rmem (Db + v)) ∧
        (∀ a, (a < Fb ∨ Fb + w ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ a, (a < Vb ∨ Vb + w ≤ a) → c'.rmem a = c.rmem a) ∧
        (∀ r, r < 610 ∨ 614 < r → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 600 → c'.rreg r = c.rreg r) ∧ c'.output = c.output) := by
  have := hL.fs; have := hL.vd; have := hL.wS; have := hL.wD; have := hL.wF; have := hL.wV
  have := hL.ww
  unfold nrmProg
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ v < i, c'.nmem (Fb + v) = (if c.nmem (Sb + v) = 1 then 1 else 0) ∧
        c'.rmem (Vb + v) = c.rmem (Db + v)) ∧
      (∀ a, (a < Fb ∨ Fb + w ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < Vb ∨ Vb + w ≤ a) → c'.rmem a = c.rmem a) ∧
      (∀ r, r < 610 ∨ 614 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 610 = 1 ∧
      (∀ r, r ≠ 600 → c'.rreg r = c.rreg r) ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 611) (bR := 600) (body := nBody) J (K := 15)
    (n := w) _ ‹_› (by config_simp) (by config_simp; exact h600) ?_
    (fun i c₁ hi hw ha hb ⟨g, gm, grm, gn, g610, gr, go⟩ => by
      have e601 : c₁.nreg 601 = Sb := (gn 601 (by omega)).trans h601
      have e602 : c₁.nreg 602 = Db := (gn 602 (by omega)).trans h602
      have e603 : c₁.nreg 603 = Fb := (gn 603 (by omega)).trans h603
      have e604 : c₁.nreg 604 = Vb := (gn 604 (by omega)).trans h604
      have xs : c₁.nmem (Sb + i) = c.nmem (Sb + i) := gm _ (by omega)
      have xd : c₁.rmem (Db + i) = c.rmem (Db + i) := grm _ (by omega)
      unfold nBody
      refine spec_seq ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e601, ha]); omega)
      refine spec_seq ?_
      -- the normalized flag in `r614`
      have key : ∀ c₂ : Config, WordsBounded W c₂ → c₂.nreg 613 = c.nmem (Sb + i) →
          c₂.nreg 610 = 1 → c₂.nreg 614 = 0 → ∃ c₃ k, Exec P W
            (.ifLtN 613 610 .skip (.ifLtN 610 613 .skip (.instr (.copyN 614 610)))) c₂ c₃ k ∧
            k ≤ 5 ∧ c₃.nreg 614 = (if c.nmem (Sb + i) = 1 then 1 else 0) ∧
            (∀ r, r ≠ 614 → c₃.nreg r = c₂.nreg r) ∧ c₃.rreg = c₂.rreg ∧
            c₃.nmem = c₂.nmem ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
        intro c₂ hw₂ f613 f610 f614
        by_cases h0 : c₂.nreg 613 < c₂.nreg 610
        · refine spec_ifLtN_true h0 (spec_skip hw₂ ⟨by omega, ?_, fun _ _ => rfl, rfl, rfl, rfl,
            rfl⟩)
          rw [f614, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        · refine spec_ifLtN_false h0 ?_
          by_cases h1 : c₂.nreg 610 < c₂.nreg 613
          · refine spec_ifLtN_true h1 (spec_skip hw₂ ⟨by omega, ?_, fun _ _ => rfl, rfl, rfl,
              rfl, rfl⟩)
            rw [f614, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
          · refine spec_ifLtN_false h1 ?_
            refine spec_instr (Exec.copyN hw₂ 614 610) fun _ => ⟨by omega, ?_, fun r hr => ?_,
              rfl, rfl, rfl, rfl⟩
            · config_simp; rw [f610, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
            · simp only [upd_apply, hr, ↓reduceIte]
      refine spec_use (key _ ‹_› (by config_simp; simp only [e601, ha, xs])
        (by config_simp; exact g610) (by config_simp)) ?_
      intro c₃ k₃ hk₃ hw₃ ⟨f614, fn, fr, fnm, frm, fo⟩
      have q611 : c₃.nreg 611 = i := by rw [fn 611 (by omega)]; config_simp; exact ha
      have q610 : c₃.nreg 610 = 1 := by rw [fn 610 (by omega)]; config_simp; exact g610
      have q602 : c₃.nreg 602 = Db := by rw [fn 602 (by omega)]; config_simp; exact e602
      have q603 : c₃.nreg 603 = Fb := by rw [fn 603 (by omega)]; config_simp; exact e603
      have q604 : c₃.nreg 604 = Vb := by rw [fn 604 (by omega)]; config_simp; exact e604
      have qd : c₃.rmem (Db + i) = c.rmem (Db + i) := by rw [frm]; exact xd
      exec_block
      all_goals try ((try config_simp); (try simp only [q611, q610, q602, q603, q604]); omega)
      dsimp only [J]
      config_simp
      simp only [q611, q610, q602, q603, q604, f614, qd]
      refine ⟨by omega, trivial, by rw [fn 600 (by omega)]; config_simp; exact hb,
        fun v hv => ?_, fun a ha' => ?_, fun a ha' => ?_, fun r hr => ?_, trivial,
        fun r hr => ?_, ?_⟩
      · simp only [upd_apply]
        by_cases hvi : v = i
        · subst hvi; simp
        · have h1 : Fb + v ≠ Fb + i := by omega
          have h2 : Vb + v ≠ Vb + i := by omega
          simp only [h1, h2, ↓reduceIte, fnm, frm]
          exact g v (by omega)
      · simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fnm, gm a ha']
      · simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), frm, grm a ha']
      · simp only [upd_apply]
        split_ifs <;> first | omega | (rw [fn r (by omega)]; config_simp; simp only [upd_apply]
                                       split_ifs <;> first | omega | exact gn r hr)
      · simp only [upd_apply, hr, ↓reduceIte]; rw [fr]; config_simp; exact gr r hr
      · rw [fo, go])) ?_
  · refine ⟨fun v hv => absurd hv (by omega), fun _ _ => rfl, fun _ _ => rfl, fun r hr => ?_, ?_,
      fun _ _ => rfl, rfl⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, g, gm, grm, gn, -, gr, go⟩ := hJ₂
  exact ⟨by omega, g, gm, grm, gn, gr, go⟩

/-! ### The candidate arcs of a part -/

/-- The arc from the root to the vertex `v = r721` at `m + v`: tail `0`, head `v + 1`, keep flag
cleared, length `I[v]`. -/
def aVBody : Stmt := block [.addN 726 700 721, .constN 725 0, .addN 722 707 726, .storeN 722 725,
  .addN 723 721 720, .addN 722 708 726, .storeN 722 723, .addN 722 709 726, .storeN 722 725,
  .addN 722 706 721, .loadR 700 722, .addN 722 710 726, .storeR 722 700, .addN 721 721 720]

/-- The dart `d = r721` at `d`: tail `T d + 1`, head `H d + 1`, keep flag
`f = (S d + s + 1) % 2` (`1` iff the dart is of the side `s`), length `ℓ d`; the flag `f` added to
the keep flags of the arcs from the root to its ends. -/
def aDBody : Stmt := block [.addN 722 702 721, .loadN 723 722, .addN 724 723 720,
  .addN 722 707 721, .storeN 722 724, .addN 722 703 721, .loadN 725 722, .addN 724 725 720,
  .addN 722 708 721, .storeN 722 724, .addN 722 704 721, .loadN 724 722, .addN 724 724 711,
  .addN 724 724 720, .modN 724 724 727, .addN 722 709 721, .storeN 722 724, .addN 722 705 721,
  .loadR 700 722, .addN 722 710 721, .storeR 722 700, .addN 726 700 723, .addN 722 709 726,
  .loadN 728 722, .addN 728 728 724, .storeN 722 728, .addN 726 700 725, .addN 722 709 726,
  .loadN 728 722, .addN 728 728 724, .storeN 722 728, .addN 721 721 720]

/-- **The candidate arcs of the side `s = r711`** (`r700 = m`, `r701 = w`, the bases `r702` of
the tails, `r703` of the heads, `r704` of the sides (natural), `r705` of the lengths, `r706` of
the initial lengths (real); the outputs at `r707` (tails), `r708` (heads), `r709` (keep flags),
`r710` (lengths, real)). -/
def aProg : Stmt :=
  .seq (block [.constN 720 1, .constN 727 2, .constN 721 0]) <|
  .seq (.whileLtN 721 701 aVBody) <| .seq (.instr (.constN 721 0)) (.whileLtN 721 700 aDBody)

/-- The data of `aProg`. -/
structure AIn (m w s Tb Hb Sb Lb Ib Tq Hq Kq Lq : ℕ) (T H S : ℕ → ℕ) (L I : ℕ → ℝ) (c : Config) :
    Prop where
  r700 : c.nreg 700 = m
  r701 : c.nreg 701 = w
  r702 : c.nreg 702 = Tb
  r703 : c.nreg 703 = Hb
  r704 : c.nreg 704 = Sb
  r705 : c.nreg 705 = Lb
  r706 : c.nreg 706 = Ib
  r707 : c.nreg 707 = Tq
  r708 : c.nreg 708 = Hq
  r709 : c.nreg 709 = Kq
  r710 : c.nreg 710 = Lq
  r711 : c.nreg 711 = s
  tl : ∀ d < m, c.nmem (Tb + d) = T d
  hd : ∀ d < m, c.nmem (Hb + d) = H d
  sd : ∀ d < m, c.nmem (Sb + d) = S d
  ln : ∀ d < m, c.rmem (Lb + d) = L d
  il : ∀ v < w, c.rmem (Ib + v) = I v

/-- The layout of `aProg`. -/
structure ALay (m w s Tb Hb Sb Lb Ib Tq Hq Kq Lq W : ℕ) (T H S : ℕ → ℕ) : Prop where
  ends : ∀ d < m, T d < w ∧ H d < w ∧ S d ≤ 1
  s1 : s ≤ 1
  tT : Tq + (m + w) ≤ Tb ∨ Tb + m ≤ Tq
  tH : Tq + (m + w) ≤ Hb ∨ Hb + m ≤ Tq
  tS : Tq + (m + w) ≤ Sb ∨ Sb + m ≤ Tq
  hT : Hq + (m + w) ≤ Tb ∨ Tb + m ≤ Hq
  hH : Hq + (m + w) ≤ Hb ∨ Hb + m ≤ Hq
  hS : Hq + (m + w) ≤ Sb ∨ Sb + m ≤ Hq
  kT : Kq + (m + w) ≤ Tb ∨ Tb + m ≤ Kq
  kH : Kq + (m + w) ≤ Hb ∨ Hb + m ≤ Kq
  kS : Kq + (m + w) ≤ Sb ∨ Sb + m ≤ Kq
  th : Tq + (m + w) ≤ Hq ∨ Hq + (m + w) ≤ Tq
  tk : Tq + (m + w) ≤ Kq ∨ Kq + (m + w) ≤ Tq
  hk : Hq + (m + w) ≤ Kq ∨ Kq + (m + w) ≤ Hq
  lL : Lq + (m + w) ≤ Lb ∨ Lb + m ≤ Lq
  lI : Lq + (m + w) ≤ Ib ∨ Ib + w ≤ Lq
  wT : Tb + m ≤ W
  wH : Hb + m ≤ W
  wS : Sb + m ≤ W
  wL : Lb + m ≤ W
  wI : Ib + w ≤ W
  wTq : Tq + (m + w) ≤ W
  wHq : Hq + (m + w) ≤ W
  wKq : Kq + (m + w) ≤ W
  wLq : Lq + (m + w) ≤ W
  wm : 2 * m + w + 3 ≤ W

lemma flag_ne_zero {a s : ℕ} (ha : a ≤ 1) (hs : s ≤ 1) : (a + s + 1) % 2 ≠ 0 ↔ a = s := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hs with rfl | rfl <;> decide

lemma flag_le {a s : ℕ} : (a + s + 1) % 2 ≤ 1 := by have := Nat.mod_lt (a + s + 1) two_pos; omega

/-- The keep flag of a vertex after the dart `d`: the old flag plus `f` for each end equal to
the vertex. -/
lemma kcell (g : ℕ → ℕ) (A B x f : ℕ) :
    upd (upd g A (g A + f)) B (upd g A (g A + f) B + f) x =
      g x + (if A = x then f else 0) + (if B = x then f else 0) := by
  simp only [upd_apply]
  split_ifs <;> subst_vars <;> omega

set_option maxHeartbeats 800000 in
theorem aDBody_exec {m w s Tb Hb Sb Lb Ib Tq Hq Kq Lq : ℕ} {T H S : ℕ → ℕ} {L I : ℕ → ℝ}
    (hL : ALay m w s Tb Hb Sb Lb Ib Tq Hq Kq Lq W T H S) (c₁ : Config) (hw : WordsBounded W c₁)
    {d : ℕ} (hd : d < m) (ha : c₁.nreg 721 = d) (e702 : c₁.nreg 702 = Tb)
    (e703 : c₁.nreg 703 = Hb) (e704 : c₁.nreg 704 = Sb) (e705 : c₁.nreg 705 = Lb)
    (e700 : c₁.nreg 700 = m) (e707 : c₁.nreg 707 = Tq) (e708 : c₁.nreg 708 = Hq)
    (e709 : c₁.nreg 709 = Kq) (e710 : c₁.nreg 710 = Lq) (e711 : c₁.nreg 711 = s)
    (g720 : c₁.nreg 720 = 1) (g727 : c₁.nreg 727 = 2)
    (xt : c₁.nmem (Tb + d) = T d) (xh : c₁.nmem (Hb + d) = H d) (xs : c₁.nmem (Sb + d) = S d)
    (xl : c₁.rmem (Lb + d) = L d) (hk4 : c₁.nmem (Kq + (m + T d)) ≤ 2 * d)
    (hk5 : c₁.nmem (Kq + (m + H d)) ≤ 2 * d) :
    ∃ c' k, Exec P W aDBody c₁ c' k ∧ k ≤ 32 ∧
      (c'.nreg 721 = d + 1 ∧ c'.nmem (Tq + d) = T d + 1 ∧ c'.nmem (Hq + d) = H d + 1 ∧
        c'.nmem (Kq + d) = (S d + s + 1) % 2 ∧
        (∀ x, x ≠ Tq + d → x ≠ Hq + d → x ≠ Kq + d → c'.nmem x = c₁.nmem x +
          (if Kq + (m + T d) = x then (S d + s + 1) % 2 else 0) +
          (if Kq + (m + H d) = x then (S d + s + 1) % 2 else 0)) ∧
        c'.rmem = upd c₁.rmem (Lq + d) (L d) ∧
        (∀ r, (r < 721 ∨ r = 727 ∨ 728 < r) → c'.nreg r = c₁.nreg r) ∧
        (∀ r, r ≠ 700 → c'.rreg r = c₁.rreg r) ∧ c'.output = c₁.output) := by
  have := hL.tT; have := hL.tH; have := hL.tS; have := hL.hT; have := hL.hH; have := hL.hS
  have := hL.kT; have := hL.kH; have := hL.kS; have := hL.th; have := hL.tk; have := hL.hk
  have := hL.wT; have := hL.wH; have := hL.wS; have := hL.wL; have := hL.wTq; have := hL.wHq
  have := hL.wKq; have := hL.wLq; have := hL.wm; have := hL.s1
  obtain ⟨hTd, hHd, hSd⟩ := hL.ends d hd
  have hfl : (S d + s + 1) % 2 ≤ 1 := flag_le
  have n1 : Hb + d ≠ Tq + d := by omega
  have n2 : Sb + d ≠ Tq + d := by omega
  have n3 : Sb + d ≠ Hq + d := by omega
  have n4 : Kq + (m + T d) ≠ Tq + d := by omega
  have n5 : Kq + (m + T d) ≠ Hq + d := by omega
  have n6 : Kq + (m + T d) ≠ Kq + d := by omega
  have n7 : Kq + (m + H d) ≠ Tq + d := by omega
  have n8 : Kq + (m + H d) ≠ Hq + d := by omega
  have n9 : Kq + (m + H d) ≠ Kq + d := by omega
  unfold aDBody
  exec_block
  rotate_right
  · config_simp
    simp only [e700, e702, e703, e704, e705, e707, e708, e709, e710, e711, ha, xt, xl, g720, g727]
    rw [upd_other _ _ _ n1, xh, upd_other _ _ _ n3, upd_other _ _ _ n2, xs]
    and_intros
    all_goals first
      | trivial
      | omega
      | rfl
      | (rw [kcell]; simp only [upd_apply]; split_ifs <;> omega)
      | (intro x h1 h2 h3; rw [kcell]; simp only [upd_apply, h1, h2, h3, ↓reduceIte])
      | (intro r hr; simp only [upd_apply, hr, ↓reduceIte]; done)
      | (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
  all_goals (try config_simp)
  all_goals (try simp only [e700, e702, e703, e704, e705, e707, e708, e709, e710, e711, ha, xt,
    g720, g727])
  all_goals (try simp only [upd_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, ↓reduceIte, xh, xs, xl])
  all_goals (try omega)
  all_goals (try (split_ifs <;> omega))

set_option maxHeartbeats 400000 in
theorem aProg_exec {m w s Tb Hb Sb Lb Ib Tq Hq Kq Lq : ℕ} {T H S : ℕ → ℕ} {L I : ℕ → ℝ}
    (hL : ALay m w s Tb Hb Sb Lb Ib Tq Hq Kq Lq W T H S) (c : Config) (hc : WordsBounded W c)
    (hI : AIn m w s Tb Hb Sb Lb Ib Tq Hq Kq Lq T H S L I c) :
    ∃ c' k, Exec P W aProg c c' k ∧ k ≤ 34 * m + 16 * w + 8 ∧
      ((∀ d < m, c'.nmem (Tq + d) = T d + 1 ∧ c'.nmem (Hq + d) = H d + 1 ∧
          c'.nmem (Kq + d) = (S d + s + 1) % 2 ∧ c'.rmem (Lq + d) = L d) ∧
        (∀ v < w, c'.nmem (Tq + (m + v)) = 0 ∧ c'.nmem (Hq + (m + v)) = v + 1 ∧
          (c'.nmem (Kq + (m + v)) ≠ 0 ↔ InSide T H S m s v) ∧ c'.rmem (Lq + (m + v)) = I v) ∧
        (∀ a, (a < Tq ∨ Tq + (m + w) ≤ a) → (a < Hq ∨ Hq + (m + w) ≤ a) →
          (a < Kq ∨ Kq + (m + w) ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ a, (a < Lq ∨ Lq + (m + w) ≤ a) → c'.rmem a = c.rmem a) ∧
        (∀ r, r < 720 ∨ 728 < r → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 700 → c'.rreg r = c.rreg r) ∧ c'.output = c.output) := by
  have := hL.wT; have := hL.wH; have := hL.wS; have := hL.wL
  have := hL.wI; have := hL.wTq; have := hL.wHq; have := hL.wKq; have := hL.wLq; have := hL.wm
  have := hL.s1
  unfold aProg
  refine spec_seq ?_
  exec_block
  all_goals try omega
  refine spec_seq ?_
  -- the arcs from the root
  let JB : ℕ → Config → Prop := fun v c' =>
    (∀ u < v, c'.nmem (Tq + (m + u)) = 0 ∧ c'.nmem (Hq + (m + u)) = u + 1 ∧
        c'.nmem (Kq + (m + u)) = 0 ∧ c'.rmem (Lq + (m + u)) = I u) ∧
      (∀ a, (a < Tq + m ∨ Tq + (m + w) ≤ a) → (a < Hq + m ∨ Hq + (m + w) ≤ a) →
        (a < Kq + m ∨ Kq + (m + w) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < Lq + m ∨ Lq + (m + w) ≤ a) → c'.rmem a = c.rmem a) ∧
      (∀ r, r < 720 ∨ 728 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 720 = 1 ∧ c'.nreg 727 = 2 ∧
      (∀ r, r ≠ 700 → c'.rreg r = c.rreg r) ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 721) (bR := 701) (body := aVBody) JB (K := 14)
    (n := w) _ ‹_› (by config_simp) (by config_simp; exact hI.r701) ?_
    (fun v c₁ hv hw ha hb ⟨g, gm, grm, gn, g720, g727, gr, go⟩ => by
      have := hL.th; have := hL.tk; have := hL.hk; have := hL.lI
      have e700 : c₁.nreg 700 = m := (gn 700 (by omega)).trans hI.r700
      have e706 : c₁.nreg 706 = Ib := (gn 706 (by omega)).trans hI.r706
      have e707 : c₁.nreg 707 = Tq := (gn 707 (by omega)).trans hI.r707
      have e708 : c₁.nreg 708 = Hq := (gn 708 (by omega)).trans hI.r708
      have e709 : c₁.nreg 709 = Kq := (gn 709 (by omega)).trans hI.r709
      have e710 : c₁.nreg 710 = Lq := (gn 710 (by omega)).trans hI.r710
      have xi : c₁.rmem (Ib + v) = I v := by rw [grm _ (by omega)]; exact hI.il v hv
      unfold aVBody
      exec_block
      all_goals try ((try config_simp); (try simp only [e700, e706, e707, e708, e709, ha]); omega)
      all_goals try ((try config_simp); (try simp only [e700, e710, ha, g720]); omega)
      dsimp only [JB]
      config_simp
      simp only [e700, e706, e707, e708, e709, e710, ha, g720, g727, xi]
      refine ⟨by omega, trivial, hb, fun u hu => ?_, fun a h1 h2 h3 => ?_, fun a h1 => ?_,
        fun r hr => ?_, trivial, trivial, fun r hr => ?_, go⟩
      · simp only [upd_apply]
        by_cases huv : u = v
        · subst huv
          have n1 : Tq + (m + u) ≠ Hq + (m + u) := by omega
          have n2 : Tq + (m + u) ≠ Kq + (m + u) := by omega
          have n3 : Hq + (m + u) ≠ Kq + (m + u) := by omega
          simp only [n1, n2, n3, n1.symm, n2.symm, n3.symm, ↓reduceIte, true_and]
        · obtain ⟨g1, g2, g3, g4⟩ := g u (by omega)
          have n1 : Tq + (m + u) ≠ Tq + (m + v) := by omega
          have n2 : Hq + (m + u) ≠ Hq + (m + v) := by omega
          have n3 : Kq + (m + u) ≠ Kq + (m + v) := by omega
          have n4 : Lq + (m + u) ≠ Lq + (m + v) := by omega
          have n5 : Tq + (m + u) ≠ Hq + (m + v) := by omega
          have n6 : Tq + (m + u) ≠ Kq + (m + v) := by omega
          have n7 : Hq + (m + u) ≠ Kq + (m + v) := by omega
          have n8 : Hq + (m + u) ≠ Tq + (m + v) := by omega
          have n9 : Kq + (m + u) ≠ Tq + (m + v) := by omega
          have n10 : Kq + (m + u) ≠ Hq + (m + v) := by omega
          simp only [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, ↓reduceIte]
          exact ⟨g1, g2, g3, g4⟩
      · simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gm a h1 h2 h3]
      · simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), grm a h1]
      · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr
      · simp only [upd_apply, hr, ↓reduceIte]; exact gr r hr)) ?_
  · refine ⟨fun u hu => absurd hu (by omega), fun _ _ _ _ => rfl, fun _ _ => rfl, fun r hr => ?_,
      ?_, ?_, fun _ _ => rfl, rfl⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
  intro c₂ k₂ hk₂ hw₂ hJ₂
  obtain ⟨_, gB, gmB, grmB, gnB, g720B, g727B, grB, goB⟩ := hJ₂
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₂ 721 0 (by omega)) fun hw₃ => ?_
  -- the darts
  let JA : ℕ → Config → Prop := fun d c' =>
    (∀ d' < d, c'.nmem (Tq + d') = T d' + 1 ∧ c'.nmem (Hq + d') = H d' + 1 ∧
        c'.nmem (Kq + d') = (S d' + s + 1) % 2 ∧ c'.rmem (Lq + d') = L d') ∧
      (∀ v < w, c'.nmem (Tq + (m + v)) = 0 ∧ c'.nmem (Hq + (m + v)) = v + 1 ∧
        (c'.nmem (Kq + (m + v)) ≠ 0 ↔ InSide T H S d s v) ∧ c'.nmem (Kq + (m + v)) ≤ 2 * d ∧
        c'.rmem (Lq + (m + v)) = I v) ∧
      (∀ a, (a < Tq ∨ Tq + (m + w) ≤ a) → (a < Hq ∨ Hq + (m + w) ≤ a) →
        (a < Kq ∨ Kq + (m + w) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < Lq ∨ Lq + (m + w) ≤ a) → c'.rmem a = c.rmem a) ∧
      (∀ r, r < 720 ∨ 728 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 720 = 1 ∧ c'.nreg 727 = 2 ∧
      (∀ r, r ≠ 700 → c'.rreg r = c.rreg r) ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 721) (bR := 700) (body := aDBody) JA (K := 32)
    (n := m) _ hw₃ (by config_simp) (by config_simp; rw [gnB 700 (by omega)]; exact hI.r700) ?_
    (fun d c₁ hd hw ha hb ⟨g, gv, gm, grm, gn, g720, g727, gr, go⟩ => by
      obtain ⟨hTd, hHd, hSd⟩ := hL.ends d hd
      have xt : c₁.nmem (Tb + d) = T d := by
        have := hL.tT; have := hL.hT; have := hL.kT
        exact (gm (Tb + d) (by omega) (by omega) (by omega)).trans (hI.tl d hd)
      have xh : c₁.nmem (Hb + d) = H d := by
        have := hL.tH; have := hL.hH; have := hL.kH
        exact (gm (Hb + d) (by omega) (by omega) (by omega)).trans (hI.hd d hd)
      have xs : c₁.nmem (Sb + d) = S d := by
        have := hL.tS; have := hL.hS; have := hL.kS
        exact (gm (Sb + d) (by omega) (by omega) (by omega)).trans (hI.sd d hd)
      have xl : c₁.rmem (Lb + d) = L d := by
        have := hL.lL; exact (grm (Lb + d) (by omega)).trans (hI.ln d hd)
      have := hL.th; have := hL.tk; have := hL.hk
      obtain ⟨c', k, hex, hk, h721, hT', hH', hK', hx, hrm, hn, hr, ho⟩ :=
        aDBody_exec (P := P) (I := I) hL c₁ hw hd ha ((gn 702 (by omega)).trans hI.r702)
          ((gn 703 (by omega)).trans hI.r703) ((gn 704 (by omega)).trans hI.r704)
          ((gn 705 (by omega)).trans hI.r705) ((gn 700 (by omega)).trans hI.r700)
          ((gn 707 (by omega)).trans hI.r707) ((gn 708 (by omega)).trans hI.r708)
          ((gn 709 (by omega)).trans hI.r709) ((gn 710 (by omega)).trans hI.r710)
          ((gn 711 (by omega)).trans hI.r711) g720 g727
          xt xh xs xl (gv (T d) hTd).2.2.2.1
          (gv (H d) hHd).2.2.2.1
      have hfl : (S d + s + 1) % 2 ≤ 1 := flag_le
      have hfi := flag_ne_zero hSd hL.s1
      refine ⟨c', k, hex, hk, h721, by rw [hn 700 (by omega)]; exact hb, fun d' hd' => ?_,
        fun v hv => ?_, fun a h1 h2 h3 => ?_, fun a h1 => ?_, fun r hr' => ?_,
        by rw [hn 720 (by omega)]; exact g720, by rw [hn 727 (by omega)]; exact g727,
        fun r hr' => by rw [hr r hr', gr r hr'], by rw [ho, go]⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hd' with hd' | rfl
        · obtain ⟨g1, g2, g3, g4⟩ := g d' hd'
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hx (Tq + d') (by omega) (by omega) (by omega), g1]; split_ifs <;> omega
          · rw [hx (Hq + d') (by omega) (by omega) (by omega), g2]; split_ifs <;> omega
          · rw [hx (Kq + d') (by omega) (by omega) (by omega), g3]; split_ifs <;> omega
          · rw [hrm, upd_other _ _ _ (show Lq + d' ≠ Lq + d by omega), g4]
        · exact ⟨hT', hH', hK', by rw [hrm, upd_same]⟩
      · obtain ⟨g1, g2, g3, g4, g5⟩ := gv v hv
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hx (Tq + (m + v)) (by omega) (by omega) (by omega), g1]; split_ifs <;> omega
        · rw [hx (Hq + (m + v)) (by omega) (by omega) (by omega), g2]; split_ifs <;> omega
        · rw [hx (Kq + (m + v)) (by omega) (by omega) (by omega), inSide_succ, ← g3, ← hfi]
          split_ifs <;> omega
        · rw [hx (Kq + (m + v)) (by omega) (by omega) (by omega)]; split_ifs <;> omega
        · rw [hrm, upd_other _ _ _ (show Lq + (m + v) ≠ Lq + d by omega), g5]
      · rw [hx a (by omega) (by omega) (by omega), gm a h1 h2 h3]; split_ifs <;> omega
      · rw [hrm, upd_other _ _ _ (show a ≠ Lq + d by omega), grm a h1]
      · rw [hn r (by omega), gn r hr'])) ?_
  · refine ⟨fun d' hd' => absurd hd' (by omega), fun v hv => ?_, fun a h1 h2 h3 => ?_,
      fun a h1 => ?_, fun r hr => ?_, ?_, ?_, fun r hr => ?_, ?_⟩
    all_goals config_simp
    · obtain ⟨g1, g2, g3, g4⟩ := gB v hv
      refine ⟨g1, g2, ?_, by omega, g4⟩
      rw [g3]; simp [InSide]
    · exact gmB a (by omega) (by omega) (by omega)
    · exact grmB a (by omega)
    · simp only [upd_apply]; split_ifs <;> first | omega | exact gnB r hr
    · exact g720B
    · exact g727B
    · exact grB r hr
    · exact goB
  intro c₄ k₄ hk₄ _ hJ₄
  obtain ⟨_, gd, gv, gm, grm, gn, -, -, gr, go⟩ := hJ₄
  exact ⟨by omega, gd, fun v hv => ⟨(gv v hv).1, (gv v hv).2.1, (gv v hv).2.2.1,
    (gv v hv).2.2.2.2⟩, gm, grm, gn, gr, go⟩

end NegSSSP

end PlanarFlow
