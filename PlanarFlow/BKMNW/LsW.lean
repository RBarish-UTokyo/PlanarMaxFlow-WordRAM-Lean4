module

public import PlanarFlow.BKMNW.LgS5DD
public import PlanarFlow.BKMNW.LgNf

/-!
# Stages 5 and 6 of `sepL` with word bounds free of the record's address

`s5A_exec`, `s5B_exec`, `s5Pre_exec`, `lgS5D_exec`, `nf0_exec`, `nfProg_rec` assume word bounds
of the form `U + R + … ≤ W` (`R` the record's address, `U` the scratch above it). Inside the
separator program only `Sb + sR n m k ≤ W` is known (`R < Sb`), so these bounds are not
available. The variants here (suffix `W`, proofs copied) assume instead `R + 3 + 6 n ≤ U` (which
the record's layout gives) and `U + … ≤ W` **without `R`**:

* `s5A_execW`, `s5B_execW`, `s5Pre_execW`, **`lgS5D_execW`** (stage 5 with the path decoded);
* `nf0_execW`, **`nfProg_recW`** (stage 6).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.rwaSuggestion false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

section Exec

variable {I : Input} {W : ℕ}

theorem s5A_execW (c : Config) (hc : WordsBounded W c) {R U n : ℕ} (r0 : c.nreg 3100 = R)
    (r1 : c.nreg 3101 = U) (hn : c.nmem R = n) (l0 : R + 3 + 6 * n ≤ U)
    (w : U + 5 * n + 3 ≤ W) (w2 : 3 ≤ W) :
    ∃ c' t, Exec I W s5A c c' t ∧ t = 16 ∧ c'.nreg 5800 = n ∧ c'.nreg 5801 = R + 3 + n ∧
      c'.nreg 5802 = R + 3 + 2 * n ∧ c'.nreg 5803 = R + 3 + 4 * n ∧ c'.nreg 5804 = U ∧
      c'.nreg 5805 = R + 3 + 5 * n ∧ c'.nreg 5806 = 1 ∧ c'.nreg 5807 = 2 ∧
      c'.nreg 5808 = U + n ∧ c'.nreg 5809 = U + 2 * n ∧ c'.nreg 5814 = U + 3 * n ∧
      c'.nreg 5810 = U + 4 * n ∧ c'.nreg 6521 = 1 ∧
      (∀ x, (x < 5800 ∨ (5814 < x ∧ x < 5940) ∨ (5942 < x ∧ x < 6521) ∨ 6521 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold s5A
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r0, r1, hn]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl,
    rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r0, r1, hn])
    try omega

theorem s5B_execW (c : Config) (hc : WordsBounded W c) {R n k b bfl : ℕ} (r0 : c.nreg 3100 = R)
    (r2 : c.nreg 3102 = k) (r00 : c.nreg 5800 = n) (r10 : c.nreg 5810 = b)
    (hb : c.nmem (R + 2) = bfl) (l0 : R + 3 ≤ b)
    (w : b + 38 * n + 2 * k + 11 ≤ W) (w2 : 100 ≤ W) :
    ∃ c' t, Exec I W s5B c c' t ∧ t = 12 ∧ c'.nreg 5870 = k ∧ c'.nreg 5915 = bfl ∧
      c'.nreg 5916 = b + 38 * n + 2 * k + 11 ∧ c'.nreg 6521 = 1 ∧
      (∀ x, x ≠ 5870 → x ≠ 5915 → x ≠ 5916 → x ≠ 6521 → (x < 5943 ∨ 5945 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold s5B
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r0, r2, r00, r10]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x a1 a2 a3 a4 a5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r0, r2, r00, r10,
      show R + 2 = 2 + R by omega] at hb ⊢)
    try omega
  all_goals (rw [show R + 2 = 2 + R by omega] at hb; exact hb)

/-- **Stage 5 before the test**: `s5A ; lgPrep ; s5B ; lgPar ; s5Sv` on a record. -/
theorem s5Pre_execW {gid : D → ℕ} {ν : V → ℕ} {S T Q : Finset V} {x : MCall M} {m n R : ℕ}
    {g : ℕ → D} (hQ : QPar Q ν) (hd : x.2.1.Pairwise Disjoint) {st : Perm D}
    (hst : ∀ d ∈ pdarts M (core M Q x.1.piece) x.2.1, st d ∈ pdarts M (core M Q x.1.piece) x.2.1)
    (c : Config) (hc : WordsBounded W c) (hA : RArr M gid ν S T x m n R g c.nmem)
    (hSP : ∀ i < n, g i ∈ pdarts M (core M Q x.1.piece) x.2.1 →
      c.nmem (R + 3 + 5 * n + i) < n ∧ g (c.nmem (R + 3 + 5 * n + i)) = st (g i))
    {U bfl : ℕ} {bb : Bool} (r0 : c.nreg 3100 = R) (r1 : c.nreg 3101 = U)
    (r2 : c.nreg 3102 = x.2.1.length) (hRn : c.nmem R = n) (hRb : c.nmem (R + 2) = bfl)
    (hb : bfl ≤ 1) (hbb : bfl = 1 ↔ bb = true) (l0 : R + 3 + 6 * n + m ≤ U)
    (w : U + 600 * n + 5 * x.2.1.length + 300 ≤ W) :
    ∃ c' t, Exec I W s5Pre c c' t ∧ t ≤ 130 * n + 30 * x.2.1.length + 200 ∧
      c'.nreg 5800 = n ∧ c'.nreg 5801 = R + 3 + n ∧ c'.nreg 5802 = R + 3 + 2 * n ∧
      c'.nreg 5803 = R + 3 + 4 * n ∧ c'.nreg 5806 = 1 ∧ c'.nreg 5807 = 2 ∧
      c'.nreg 5809 = U + 2 * n ∧ c'.nreg 5810 = U + 4 * n ∧ c'.nreg 5814 = U + 3 * n ∧
      c'.nreg 5870 = x.2.1.length ∧
      c'.nreg 5811 = (pdarts M (core M Q x.1.piece) x.2.1).card ∧
      c'.nreg 5910 = s5Kv M x.1.piece x.2.1 bb ∧ c'.nreg 5911 = s5Av M x.1.piece x.2.1 bb ∧
      c'.nreg 5912 = s5Wv M x.1.piece x.2.1 bb ∧ c'.nreg 5947 = 0 ∧
      c'.nreg 3103 = (pdarts M (core M Q x.1.piece) x.2.1).card ∧
      c'.nreg 3104 = nTouch M x.1.piece x.2.1 ∧
      c'.nreg 3105 = bf (holeStep M x.1.piece x.2.1 bb = true) ∧
      c'.nreg 3106 = s5Kv M x.1.piece x.2.1 bb ∧ c'.nreg 3107 = s5Av M x.1.piece x.2.1 bb ∧
      c'.nreg 3108 = s5Wv M x.1.piece x.2.1 bb ∧
      S2Arr M gid c'.nmem U n (pdarts M (core M Q x.1.piece) x.2.1).card g
        (pdarts M (core M Q x.1.piece) x.2.1) x.2.1 st ∧
      (∀ a, a < U → c'.nmem a = c.nmem a) ∧
      (∀ y, s5Fr y → c'.nreg y = c.nreg y) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set B := pdarts M (core M Q x.1.piece) x.2.1 with hB
  set k := x.2.1.length with hk
  have hBP : B ⊆ x.1.piece := fun y hy => (mem_core.1 (mem_pdarts.1 hy).1).1
  have hnB : B.card ≤ n := by rw [hA.card]; exact card_le_card hBP
  -- the registers of `lgPrep`
  obtain ⟨c₁, t₁, e₁, ht₁, a00, a01, a02, a03, a04, a05, a06, a07, a08, a09, a14, a10, a21, f₁,
    m₁, rr₁, rm₁, o₁⟩ := s5A_execW (I := I) c hc r0 r1 hRn (by omega) (by omega) (by omega)
  -- `lgPrep`
  obtain ⟨c₂, t₂, e₂, ht₂, p11, pix, pixs, pixm, pnf, pth, prv, psg, m₂, f₂, rr₂, rm₂, o₂⟩ :=
    lgPrep_exec (P := I) hQ hd hst c₁ e₁.wb_right (by rw [m₁]; exact hA)
      (by rw [m₁]; exact hSP) a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a14 a21 l0
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have g₂ : ∀ y, ¬ lgPw y → c₂.nreg y = c₁.nreg y := f₂
  -- the registers of `lgPar`
  obtain ⟨c₃, t₃, e₃, ht₃, b70, b15, b16, b21, f₃, m₃, rr₃, rm₃, o₃⟩ :=
    s5B_execW (I := I) c₂ e₂.wb_right (bfl := bfl)
      (((g₂ 3100 (by unfold lgPw; omega)).trans (f₁ 3100 (by omega))).trans r0)
      (((g₂ 3102 (by unfold lgPw; omega)).trans (f₁ 3102 (by omega))).trans r2)
      ((g₂ 5800 (by unfold lgPw; omega)).trans a00) ((g₂ 5810 (by unfold lgPw; omega)).trans a10)
      (by rw [m₂ (R + 2) (by omega), m₁]; exact hRb) (by omega) (by omega) (by omega)
  have g₃ : ∀ y, ¬ lgPw y → y ≠ 5870 → y ≠ 5915 → y ≠ 5916 → y ≠ 6521 → (y < 5943 ∨ 5945 < y) →
      c₃.nreg y = c₁.nreg y := fun y h1 h2 h3 h4 h5 h6 => by rw [f₃ y h2 h3 h4 h5 h6, g₂ y h1]
  have hA₃ : RArr M gid ν S T x m n R g c₃.nmem := hA.congr fun a h1 h2 => by
    rw [m₃, m₂ a (by omega), m₁]
  -- `lgPar`
  obtain ⟨c₄, t₄, e₄, ht₄, v14, v13, v10, v11, v12, m₄, f₄, rr₄, rm₄, o₄⟩ :=
    lgPar_rec (P := I) c₃ e₃.wb_right hA₃ hd hbb
      ((g₃ 5800 (by unfold lgPw; omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        a00)
      ((g₃ 5802 (by unfold lgPw; omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        a02)
      ((g₃ 5806 (by unfold lgPw; omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        a06) b70 b15 b16 b21 hb (by omega) (by omega) (by omega)
  -- the save
  obtain ⟨c₅, t₅, e₅, ht₅, s03, s04, s05, s06, s07, s08, s47, f₅, m₅, rr₅, rm₅, o₅⟩ :=
    s5Sv_exec (I := I) c₄ e₄.wb_right (by omega)
  have g₅ : ∀ y, ¬ lgPw y → y ≠ 5870 → y ≠ 5915 → y ≠ 5916 → y ≠ 6521 → (y < 5943 ∨ 5945 < y) →
      ¬ lgParW y → (y < 3103 ∨ 3108 < y) → y ≠ 5947 → c₅.nreg y = c₁.nreg y :=
    fun y h1 h2 h3 h4 h5 h6 h7 h8 h9 => by rw [f₅ y h8 h9, f₄ y h7, g₃ y h1 h2 h3 h4 h5 h6]
  have q : ∀ y, 5800 ≤ y → y ≤ 5814 → y ≠ 5811 → y ≠ 5812 → y ≠ 5813 →
      c₅.nreg y = c₁.nreg y := fun y h1 h2 h3 h4 h5 =>
    g₅ y (by unfold lgPw; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold lgParW; omega) (by omega) (by omega)
  have hn5 : c₅.nreg 5811 = B.card := by
    rw [f₅ 5811 (by omega) (by omega), f₄ 5811 (by unfold lgParW; omega),
      f₃ 5811 (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact p11
  have hmem : ∀ a, ¬ (U + 4 * n + 38 * n + 2 * k + 11 ≤ a ∧
      a < U + 4 * n + 38 * n + 2 * k + 11 + 3 * k + 2) → c₅.nmem a = c₂.nmem a := fun a h => by
    rw [m₅, m₄ a h, m₃]
  have z00 : c₅.nreg 5800 = n := (q 5800 (by omega) (by omega) (by omega) (by omega) (by omega)).trans a00
  have z01 : c₅.nreg 5801 = R + 3 + n := (q 5801 (by omega) (by omega) (by omega) (by omega) (by omega)).trans a01
  have z02 : c₅.nreg 5802 = R + 3 + 2 * n := (q 5802 (by omega) (by omega) (by omega) (by omega) (by omega)).trans a02
  have z03 : c₅.nreg 5803 = R + 3 + 4 * n := (q 5803 (by omega) (by omega) (by omega) (by omega) (by omega)).trans a03
  have z06 : c₅.nreg 5806 = 1 := (q 5806 (by omega) (by omega) (by omega) (by omega) (by omega)).trans a06
  have z07 : c₅.nreg 5807 = 2 := (q 5807 (by omega) (by omega) (by omega) (by omega) (by omega)).trans a07
  have z09 : c₅.nreg 5809 = U + 2 * n := (q 5809 (by omega) (by omega) (by omega) (by omega) (by omega)).trans a09
  have z10 : c₅.nreg 5810 = U + 4 * n := (q 5810 (by omega) (by omega) (by omega) (by omega) (by omega)).trans a10
  have z14 : c₅.nreg 5814 = U + 3 * n := (q 5814 (by omega) (by omega) (by omega) (by omega) (by omega)).trans a14
  have z70 : c₅.nreg 5870 = k := by
    rw [f₅ 5870 (by omega) (by omega), f₄ 5870 (by unfold lgParW; omega)]; exact b70
  have z910 : c₅.nreg 5910 = s5Kv M x.1.piece x.2.1 bb := by
    rw [f₅ 5910 (by omega) (by omega)]; exact v10
  have z911 : c₅.nreg 5911 = s5Av M x.1.piece x.2.1 bb := by
    rw [f₅ 5911 (by omega) (by omega)]; exact v11
  have z912 : c₅.nreg 5912 = s5Wv M x.1.piece x.2.1 bb := by
    rw [f₅ 5912 (by omega) (by omega)]; exact v12
  have z3103 : c₅.nreg 3103 = B.card := by
    rw [s03, f₄ 5811 (by unfold lgParW; omega),
      f₃ 5811 (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact p11
  refine ⟨c₅, _, .seq (.seq e₁ e₂) (.seq (.seq e₃ e₄) e₅), by omega, z00, z01, z02, z03, z06,
    z07, z09, z10, z14, z70, hn5, z910, z911, z912, s47, z3103, by rw [s04]; exact v14,
    by rw [s05]; exact v13, by rw [s06]; exact v10, by rw [s07]; exact v11,
    by rw [s08]; exact v12, ?_, fun a ha => ?_, fun y hy => ?_,
    by rw [rr₅, rr₄, rr₃, rr₂, rr₁], by rw [rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₅, o₄, o₃, o₂, o₁]⟩
  · have hS : S2Arr M gid c₂.nmem U n B.card g B x.2.1 st :=
      { le := hnB, ix := pix, ixs := pixs, ixm := pixm, nf := pnf, th := pth, rv := prv,
        sg := psg }
    refine S2Arr.congr (mem := c₂.nmem) hS ?_
    intro a h1 h2
    have := hS.le
    exact hmem a (by clear * - h1 h2 this; omega)
  · rw [hmem a (by clear * - ha; omega), m₂ a (by clear * - ha; omega), m₁]
  · unfold s5Fr at hy
    rw [g₅ y (by unfold lgPw; clear * - hy; omega) (by clear * - hy; omega)
      (by clear * - hy; omega) (by clear * - hy; omega) (by clear * - hy; omega)
      (by clear * - hy; omega) (by unfold lgParW; clear * - hy; omega) (by clear * - hy; omega)
      (by clear * - hy; omega)]
    exact f₁ y (by clear * - hy; omega)


/-- **Stage 5 of the large-piece separator, composed, with the path decoded**: `lgS5_exec` for
`lgS5D` (Miller's base `mbBaseD`), the path also given by its darts at `Hb + 6 #B` (`PathNHD`,
`Hb = U + 42 n + 5 k + 34 #B + encB' W₀ + 3 W₀ + 47`), cost with `mbTD`. -/
theorem lgS5D_execW (hloopM : ∀ d, M.head d ≠ M.tail d) {gid : D → ℕ} {ν : V → ℕ}
    {S T Q : Finset V} {x : MCall M} {m n R : ℕ} {g : ℕ → D} (c : Config) (hc : WordsBounded W c)
    (hA : RArr M gid ν S T x m n R g c.nmem) (hTS : TailSorted M gid ν) (hQ : QPar Q ν)
    (hν : Injective ν) (hP : PcOK M S T x.1.piece x.2.1)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {st : Perm D}
    (hCI : CInvS M Q x.1.piece x.2.1 st) (hnt : nTouch M x.1.piece x.2.1 ≤ 6)
    (hSP : ∀ i < n, g i ∈ pdarts M (core M Q x.1.piece) x.2.1 →
      c.nmem (R + 3 + 5 * n + i) < n ∧ g (c.nmem (R + 3 + 5 * n + i)) = st (g i))
    {eG : ℕ → D} {N : ℕ} (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d)
    (d₀ : D) {U bfl : ℕ} {bb : Bool} (r0 : c.nreg 3100 = R) (r1 : c.nreg 3101 = U)
    (r2 : c.nreg 3102 = x.2.1.length) (hRn : c.nmem R = n) (hRb : c.nmem (R + 2) = bfl)
    (hb : bfl ≤ 1) (hbb : bfl = 1 ↔ bb = true) (l0 : R + 3 + 6 * n + m ≤ U)
    (w : U + 600 * n + 10 * x.2.1.length + 2 * encB' (s5Wv M x.1.piece x.2.1 bb) +
      20 * s5Wv M x.1.piece x.2.1 bb + s5Kv M x.1.piece x.2.1 bb + s5Av M x.1.piece x.2.1 bb +
      400 ≤ W) :
    ∃ c' t, Exec I W lgS5D c c' t ∧
      t ≤ 9700 * n + 70 * x.2.1.length + 5 * Nat.log 2 (2 * s5Wv M x.1.piece x.2.1 bb) +
        mbTD (pdarts M (core M Q x.1.piece) x.2.1).card (encB' (s5Wv M x.1.piece x.2.1 bb))
          (s5Wv M x.1.piece x.2.1 bb) + 3800 ∧
      (∀ a < U, c'.nmem a = c.nmem a) ∧ (∀ y, s5Keep y → c'.nreg y = c.nreg y) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 3103 = (pdarts M (core M Q x.1.piece) x.2.1).card ∧
      c'.nreg 3104 = nTouch M x.1.piece x.2.1 ∧
      c'.nreg 3105 = bf (holeStep M x.1.piece x.2.1 bb = true) ∧
      c'.nreg 3106 = s5Kv M x.1.piece x.2.1 bb ∧ c'.nreg 3107 = s5Av M x.1.piece x.2.1 bb ∧
      c'.nreg 3108 = s5Wv M x.1.piece x.2.1 bb ∧
      (∀ j < (pdarts M (core M Q x.1.piece) x.2.1).card, c'.nmem (U + 2 * n + j) < n ∧
        g (c'.nmem (U + 2 * n + j)) ∈ pdarts M (core M Q x.1.piece) x.2.1) ∧
      (∀ y ∈ pdarts M (core M Q x.1.piece) x.2.1,
        ∃ j < (pdarts M (core M Q x.1.piece) x.2.1).card, g (c'.nmem (U + 2 * n + j)) = y) ∧
      (∀ i j, i < j → j < (pdarts M (core M Q x.1.piece) x.2.1).card →
        gid (g (c'.nmem (U + 2 * n + i))) < gid (g (c'.nmem (U + 2 * n + j)))) ∧
      (∀ j < (pdarts M (core M Q x.1.piece) x.2.1).card,
        c'.nmem (U + 3 * n + j) < (pdarts M (core M Q x.1.piece) x.2.1).card ∧
        g (c'.nmem (U + 2 * n + c'.nmem (U + 3 * n + j))) = st (g (c'.nmem (U + 2 * n + j)))) ∧
      ((pdarts M (core M Q x.1.piece) x.2.1).card = 0 ∨
       (0 < (pdarts M (core M Q x.1.piece) x.2.1).card ∧
        c'.nreg 3109 = encB' (s5Wv M x.1.piece x.2.1 bb) ∧
        ((c'.nreg 4970 = 0 ∧ scertD (s5sc M eG N x.2.1 (s5Av M x.1.piece x.2.1 bb)
            (s5Wv M x.1.piece x.2.1 bb)) x.2.1 (pdarts M (core M Q x.1.piece) x.2.1) st
            (s5ex M Q eG N d₀ x.1.piece x.2.1 (s5Kv M x.1.piece x.2.1 bb)) = none) ∨
         (c'.nreg 4970 = 1 ∧ ∃ ρ I, scertD (s5sc M eG N x.2.1 (s5Av M x.1.piece x.2.1 bb)
            (s5Wv M x.1.piece x.2.1 bb)) x.2.1 (pdarts M (core M Q x.1.piece) x.2.1) st
            (s5ex M Q eG N d₀ x.1.piece x.2.1 (s5Kv M x.1.piece x.2.1 bb)) = some (ρ, I) ∧
           ∃ e' : ℕ → D, (∀ j < (pdarts M (core M Q x.1.piece) x.2.1).card,
             e' j = g (c'.nmem (U + 2 * n + j))) ∧
           ItemRep e' (pdarts M (core M Q x.1.piece) x.2.1).card I
             (fun i => c'.nmem (U + 42 * n + 5 * x.2.1.length +
               7 * (pdarts M (core M Q x.1.piece) x.2.1).card + 32 + i)) ∧
           ((c'.nreg 4900 = 0 ∧ PathNHD M e' (pdarts M (core M Q x.1.piece) x.2.1).card
               (U + 42 * n + 5 * x.2.1.length + 8 * (pdarts M (core M Q x.1.piece) x.2.1).card +
                 32)
               (U + 42 * n + 5 * x.2.1.length + 34 * (pdarts M (core M Q x.1.piece) x.2.1).card +
                 encB' (s5Wv M x.1.piece x.2.1 bb) + 3 * s5Wv M x.1.piece x.2.1 bb + 47)
               x.2.1 c' ρ) ∨
            (c'.nreg 4900 = 2 ∧ c'.nreg 4902 < (pdarts M (core M Q x.1.piece) x.2.1).card ∧
              ρ = (SPath.point (M' := M) (e' (c'.nreg 4902))
                (M.tail (e' (c'.nreg 4902)))).toH)))))) := by
  obtain ⟨c₁, t₁, e₁, ht₁, z00, z01, z02, z03, z06, z07, z09, z10, z14, z70, z11, z910, z911,
    z912, z47, s03, s04, s05, s06, s07, s08, hS₁, mem₁, q₁, rr₁, rm₁, o₁⟩ :=
    s5Pre_execW (I := I) (bb := bb) hQ hP.disj hCI.pmap.stable c hc hA hSP r0 r1 r2 hRn hRb hb
      hbb l0 (by clear * - w; omega)
  have hA₁ : RArr M gid ν S T x m n R g c₁.nmem := hA.congr fun a h1 h2 =>
    mem₁ a (by clear * - h2 l0; omega)
  rcases Nat.eq_zero_or_pos (pdarts M (core M Q x.1.piece) x.2.1).card with h0 | hpos
  · -- the empty piece map of the core: skip
    refine ⟨c₁, t₁ + 2, .seq e₁ (.ifLtN_false (by rw [z47, z11, h0]; omega) (.skip e₁.wb_right)),
      ?_, mem₁, fun y hy => q₁ y ?_, rr₁, rm₁, o₁, s03, s04, s05, s06, s07, s08, hS₁.ix, hS₁.ixs,
      hS₁.ixm, hS₁.sg, Or.inl h0⟩
    · clear * - ht₁
      omega
    · unfold s5Keep at hy; unfold s5Fr; clear * - hy; omega
  · obtain ⟨c₂, t₂, e₂, ht₂, mem₂, v3109, q₂, rr₂, rm₂, o₂, hout⟩ := s5BodyD_exec (I := I) hloopM
      c₁ e₁.wb_right hA₁ hTS hQ hν hP hQdeg hQ5 hCI hnt he hesurj d₀ rfl rfl hpos hS₁ z00 z01
      z02 z03 z06 z07 z09 z10 z14 z70 ((q₁ 3102 (by unfold s5Fr; decide)).trans r2) z11 z910
      z911 z912 l0 (by clear * - w; omega)
    have hS₂ : ∀ a < U + 4 * n, c₂.nmem a = c₁.nmem a := mem₂
    have hn'n := hS₁.le
    have keep : ∀ y, s5Keep y → c₂.nreg y = c₁.nreg y := fun y hy =>
      q₂ y (by unfold s5Keep at hy; unfold s5BFr; clear * - hy; omega)
    refine ⟨c₂, t₁ + (t₂ + 1), .seq e₁ (.ifLtN_true (by rw [z47, z11]; exact hpos) e₂), ?_,
      fun a ha => ?_, fun y hy => ?_, by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁], ?_, ?_,
      ?_, ?_, ?_, ?_, fun j hj => ?_, fun y hy => ?_, fun i j hij hj => ?_, fun j hj => ?_,
      Or.inr ⟨hpos, v3109, ?_⟩⟩
    · clear * - ht₁ ht₂ hn'n
      omega
    · rw [hS₂ a (by clear * - ha; omega), mem₁ a ha]
    · rw [keep y hy, q₁ y (by unfold s5Keep at hy; unfold s5Fr; clear * - hy; omega)]
    · rw [q₂ 3103 (by unfold s5BFr; decide)]; exact s03
    · rw [q₂ 3104 (by unfold s5BFr; decide)]; exact s04
    · rw [q₂ 3105 (by unfold s5BFr; decide)]; exact s05
    · rw [q₂ 3106 (by unfold s5BFr; decide)]; exact s06
    · rw [q₂ 3107 (by unfold s5BFr; decide)]; exact s07
    · rw [q₂ 3108 (by unfold s5BFr; decide)]; exact s08
    · rw [hS₂ _ (by clear * - hj hn'n; omega)]; exact hS₁.ix j hj
    · obtain ⟨j, hj, hy'⟩ := hS₁.ixs y hy
      exact ⟨j, hj, by rw [hS₂ _ (by clear * - hj hn'n; omega)]; exact hy'⟩
    · rw [hS₂ _ (by clear * - hj hij hn'n; omega), hS₂ _ (by clear * - hj hn'n; omega)]
      exact hS₁.ixm i j hij hj
    · have h1 := hS₁.sg j hj
      rw [hS₂ (U + 3 * n + j) (by clear * - hj hn'n; omega),
        hS₂ (U + 2 * n + c₁.nmem (U + 3 * n + j)) (by clear * - h1 hn'n; omega),
        hS₂ (U + 2 * n + j) (by clear * - hj hn'n; omega)]
      exact h1
    · rcases hout with ⟨h1, h2⟩ | ⟨h1, ρ, I, h2, h3, h4⟩
      · exact Or.inl ⟨h1, h2⟩
      · refine Or.inr ⟨h1, ρ, I, h2, fun j => g (c₁.nmem (U + 2 * n + j)), fun j hj => ?_, h3, h4⟩
        rw [hS₂ _ (by clear * - hj hn'n; omega)]

theorem nf0_execW (c : Config) (hc : WordsBounded W c) {R n k Y : ℕ} (r0 : c.nreg 3100 = R)
    (r2 : c.nreg 3102 = k) (r11 : c.nreg 3111 = Y) (hn : c.nmem R = n)
    (l0 : R + 3 + 6 * n ≤ Y)
    (w : Y + 6 * n + k + 10 ≤ W) :
    ∃ c' t, Exec I W nf0 c c' t ∧ t = 15 ∧ c'.nreg 5800 = n ∧ c'.nreg 5801 = R + 3 + n ∧
      c'.nreg 5802 = R + 3 + 2 * n ∧ c'.nreg 5803 = R + 3 + 4 * n ∧ c'.nreg 5804 = Y ∧
      c'.nreg 5806 = 1 ∧ c'.nreg 5807 = 2 ∧ c'.nreg 6521 = 1 ∧ c'.nreg 5961 = Y + n ∧
      c'.nreg 5962 = Y + n + k + 1 ∧ c'.nreg 5963 = k + 1 ∧
      (∀ x, ¬ nfW x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nf0
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r0, r2, r11, hn]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try (unfold nfW at hx)
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r0, r2, r11, hn])
    try omega

/-- **Stage 6 on a record**: the flags `NF2[i] = bf (g i ∈ pcNf M Q P Hs)` at `Y + n + k + 1`. -/
theorem nfProg_recW {gid : D → ℕ} {ν : V → ℕ} {S T Q : Finset V} {x : MCall M} {m n R : ℕ}
    {g : ℕ → D} (hQ : QPar Q ν) (hd : x.2.1.Pairwise Disjoint) (c : Config)
    (hc : WordsBounded W c) (hA : RArr M gid ν S T x m n R g c.nmem) {Y : ℕ}
    (r0 : c.nreg 3100 = R) (r2 : c.nreg 3102 = x.2.1.length) (r11 : c.nreg 3111 = Y)
    (hRn : c.nmem R = n) (l0 : R + 3 + 6 * n + m ≤ Y)
    (w : Y + 6 * n + 2 * x.2.1.length + 20 ≤ W) :
    ∃ c' t, Exec I W nfProg c c' t ∧ t ≤ 70 * n + 7 * x.2.1.length + 40 ∧
      (∀ i < n, c'.nmem (Y + n + x.2.1.length + 1 + i) = bf (g i ∈ pcNf M Q x.1.piece x.2.1)) ∧
      (∀ a, ¬ (Y ≤ a ∧ a < Y + 2 * n + x.2.1.length + 1) → c'.nmem a = c.nmem a) ∧
      (∀ y, ¬ nfW y → c'.nreg y = c.nreg y) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a00, a01, a02, a03, a04, a06, a07, a21, a61, a62, a63, f₁, m₁, rr₁,
    rm₁, o₁⟩ := nf0_execW (I := I) c hc r0 r2 r11 hRn (by clear * - l0; omega) (by clear * - l0 w; omega)
  have hA₁ : RArr M gid ν S T x m n R g c₁.nmem := by rw [m₁]; exact hA
  -- the core's flags
  obtain ⟨c₂, t₂, e₂, ht₂, cf2, m₂, f₂, rr₂, rm₂, o₂⟩ := cfScan_rec (P := I) hQ hd c₁ hA₁
    e₁.wb_right (OUTb := Y) a00 a01 a02 a03 a04 a06 a07 a21 (by clear * - l0 w; omega)
    (by clear * - l0 w; omega) l0
  have g₂ : ∀ y, ¬ vscr y → y ≠ 6522 → y ≠ 6520 → c₂.nreg y = c₁.nreg y := f₂
  -- the table, zeroed
  obtain ⟨c₃, t₃, e₃, ht₃, z3, m₃, f₃, rr₃, rm₃, o₃⟩ := zfill_exec (P := I) c₂ e₂.wb_right
    (bnd := 5963) (ob := 5961) (m := x.2.1.length + 1) (Ob := Y + n)
    ((g₂ 5963 (by unfold vscr; decide) (by decide) (by decide)).trans a63)
    ((g₂ 6521 (by unfold vscr; decide) (by decide) (by decide)).trans a21)
    ((g₂ 5961 (by unfold vscr; decide) (by decide) (by decide)).trans a61)
    (by clear * - l0 w; omega) (by clear * - l0 w; omega) (by unfold vscr; decide)
    (by unfold vscr; decide) (by decide) (by decide) (by decide) (by decide)
  have g₃ : ∀ y, ¬ vscr y → y ≠ 6522 → y ≠ 6520 → c₃.nreg y = c₁.nreg y := fun y h1 h2 h3 => by
    rw [f₃ y h1 h2 h3, g₂ y h1 h2 h3]
  -- the registers of the scatter-add
  obtain ⟨c₄, t₄, e₄, ht₄, s30, s31, s32, s33, s34, f₄, m₄, rr₄, rm₄, o₄⟩ := nfSA_exec (I := I) c₃
    e₃.wb_right ((g₃ 5800 (by unfold vscr; decide) (by decide) (by decide)).trans a00)
    ((g₃ 5802 (by unfold vscr; decide) (by decide) (by decide)).trans a02)
    ((g₃ 5804 (by unfold vscr; decide) (by decide) (by decide)).trans a04)
    ((g₃ 5961 (by unfold vscr; decide) (by decide) (by decide)).trans a61) (by clear * - l0 w; omega)
  -- memory facts at `c₄`
  have mrec : ∀ a < Y, c₄.nmem a = c.nmem a := fun a ha => by
    rw [m₄, m₃ a (by clear * - ha; omega), m₂ a (by clear * - ha; omega), m₁]
  have mcf : ∀ j < n, c₄.nmem (Y + 1 * j) = bf (g j ∈ pdarts M (core M Q x.1.piece) x.2.1) :=
    fun j hj => by
      rw [one_mul, m₄, m₃ _ (by clear * - hj; omega)]
      exact cf2 j hj
  have hkey : ∀ j < n, c₄.nmem (R + 3 + 2 * n + j) = hlab x.2.1 (M.tail (g j)) := fun j hj => by
    rw [mrec _ (by clear * - hj l0; omega)]; exact hA.hp j hj
  have hsum : ∑ j ∈ range n, c₄.nmem (Y + 1 * j) ≤ n := by
    calc ∑ j ∈ range n, c₄.nmem (Y + 1 * j) ≤ ∑ _j ∈ range n, 1 :=
          sum_le_sum fun j hj => by rw [mcf j (mem_range.1 hj)]; exact bf_le_one _
      _ = n := by simp
  -- the scatter-add
  obtain ⟨c₅, t₅, e₅, ht₅, tt5, m₅, f₅, rr₅, rm₅, o₅⟩ := saProg_exec (P := I) c₄ e₄.wb_right
    (m := n) (nk := x.2.1.length + 1) s30 s31 s32 s33 s34
    (fun j hj => by rw [hkey j hj]; have := hlab_le x.2.1 (M.tail (g j)); omega)
    (fun k hk => by rw [m₄]; exact z3 k hk)
    (fun j hj => by clear * - hj l0; omega) (fun j hj => by clear * - hj; omega)
    (by clear * - l0 w; omega) (by clear * - l0 w; omega) (fun j hj => by clear * - l0 w hj; omega)
    (by clear * - l0 w; omega) (by clear * - l0 w hsum; omega)
  have g₅ : ∀ y, ¬ vscr y → y ≠ 6522 → y ≠ 6520 → (y < 4630 ∨ 4639 < y) →
      c₅.nreg y = c₁.nreg y := fun y h1 h2 h3 h4 => by
    rw [f₅ y (by omega), f₄ y (by omega), g₃ y h1 h2 h3]
  have m5r : ∀ a, a < Y + n → c₅.nmem a = c₄.nmem a := fun a ha =>
    m₅ a (by clear * - ha; omega)
  -- the flags
  obtain ⟨c₆, t₆, e₆, ht₆, nf6, m₆, f₆, rr₆, rm₆, o₆⟩ := mapRun_exec (P := I) c₅ e₅.wb_right
    (vb := vbNF) (bnd := 5800) (ob := 5962) (m := n) (Ob := Y + n + x.2.1.length + 1) (B := 21)
    (fun i => nfv (c₅.nmem (R + 3 + 2 * n + i))
      (c₅.nmem (R + 3 + 2 * n + c₅.nmem (R + 3 + n + i)))
      (c₅.nmem (Y + n + c₅.nmem (R + 3 + 2 * n + i))))
    ((g₅ 5800 (by unfold vscr; decide) (by decide) (by decide) (by decide)).trans a00)
    ((g₅ 6521 (by unfold vscr; decide) (by decide) (by decide) (by decide)).trans a21)
    ((g₅ 5962 (by unfold vscr; decide) (by decide) (by decide) (by decide)).trans a62)
    (by clear * - l0 w; omega) (by clear * - l0 w; omega) (by unfold vscr; decide)
    (by unfold vscr; decide) (by decide) (by decide) (by decide) (by decide)
    (fun i hi c' hw h20 hr hm => by
      have hrp := (hA.rp i hi).1
      have e1 : c'.nmem (R + 3 + n + i) = c₅.nmem (R + 3 + n + i) :=
        hm _ (by clear * - hi l0; omega)
      rw [m5r _ (by clear * - hi l0; omega), mrec _ (by clear * - hi l0; omega)] at e1
      have hkl : c₅.nmem (R + 3 + 2 * n + i) ≤ x.2.1.length := by
        rw [m5r _ (by clear * - hi l0; omega), hkey i hi]; exact hlab_le _ _
      have e2 : c'.nmem (R + 3 + 2 * n + i) = c₅.nmem (R + 3 + 2 * n + i) :=
        hm _ (by clear * - hi l0; omega)
      have e3 : c'.nmem (R + 3 + 2 * n + c₅.nmem (R + 3 + n + i)) =
          c₅.nmem (R + 3 + 2 * n + c₅.nmem (R + 3 + n + i)) := by
        rw [m5r (R + 3 + n + i) (by clear * - hi l0; omega), mrec _ (by clear * - hi l0; omega)]
        exact hm _ (by clear * - hrp l0; omega)
      have e4 : c'.nmem (Y + n + c₅.nmem (R + 3 + 2 * n + i)) =
          c₅.nmem (Y + n + c₅.nmem (R + 3 + 2 * n + i)) := hm _ (by clear * - hkl; omega)
      have e1' : c'.nmem (R + 3 + n + i) = c₅.nmem (R + 3 + n + i) :=
        hm _ (by clear * - hi l0; omega)
      have hr5 : c₅.nmem (R + 3 + n + i) < n := by
        rw [m5r _ (by clear * - hi l0; omega), mrec _ (by clear * - hi l0; omega)]; exact hrp
      obtain ⟨c₂', k, e, hk, v, n2, m2, rr2, rm2, o2⟩ := vbNF_exec (I := I) c' hw h20
        (RPb := R + 3 + n) (HPb := R + 3 + 2 * n) (TTb := Y + n)
        (by rw [hr _ (by unfold vscr; decide) (by decide) (by decide), g₅ 5801
          (by unfold vscr; decide) (by decide) (by decide) (by decide)]; exact a01)
        (by rw [hr _ (by unfold vscr; decide) (by decide) (by decide), g₅ 5802
          (by unfold vscr; decide) (by decide) (by decide) (by decide)]; exact a02)
        (by rw [hr _ (by unfold vscr; decide) (by decide) (by decide), g₅ 5961
          (by unfold vscr; decide) (by decide) (by decide) (by decide)]; exact a61)
        (by rw [hr _ (by unfold vscr; decide) (by decide) (by decide), g₅ 5806
          (by unfold vscr; decide) (by decide) (by decide) (by decide)]; exact a06)
        (by clear * - l0 w hi; omega) (by clear * - l0 w hi; omega)
        (by rw [e1']; clear * - l0 w hr5; omega) (by rw [e2]; clear * - l0 w hkl; omega)
        (by clear * - l0 w; omega)
      rw [e2, e1', e3, e4] at v
      exact ⟨c₂', k, e, hk, v, n2, m2, rr2, rm2, o2⟩)
  refine ⟨c₆, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ?_, fun i hi => ?_,
    fun a ha => ?_, fun y hy => ?_, by rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁], by rw [o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆
    omega
  · rw [nf6 i hi, nfv_eq]
    have hrp := hA.rp i hi
    have hkl : c₄.nmem (R + 3 + 2 * n + i) ≤ x.2.1.length := by
      rw [hkey i hi]; exact hlab_le _ _
    have q1 : c₅.nmem (R + 3 + 2 * n + i) = c₄.nmem (R + 3 + 2 * n + i) :=
      m5r _ (by clear * - hi l0; omega)
    have q2 : c₅.nmem (R + 3 + n + i) = c₄.nmem (R + 3 + n + i) :=
      m5r _ (by clear * - hi l0; omega)
    have q2' : c₄.nmem (R + 3 + n + i) = c.nmem (R + 3 + n + i) :=
      mrec _ (by clear * - hi l0; omega)
    have q3 : c₅.nmem (R + 3 + 2 * n + c₄.nmem (R + 3 + n + i)) =
        c₄.nmem (R + 3 + 2 * n + c₄.nmem (R + 3 + n + i)) := by
      rw [q2']; exact m5r _ (by clear * - hrp l0; omega)
    have q4 : c₅.nmem (Y + n + c₄.nmem (R + 3 + 2 * n + i)) =
        saF (fun j => c₄.nmem (R + 3 + 2 * n + j)) (fun j => c₄.nmem (Y + 1 * j)) n
          (c₄.nmem (R + 3 + 2 * n + i)) := tt5 _ (by clear * - hkl; omega)
    rw [q1, q2, q3, q4]
    have key := mem_pcNf_iff_tt (M := M) (Q := Q) hd (n := n) (g := g) hA.g_mem hA.g_surj
      (rp := fun j => c₄.nmem (R + 3 + n + j)) (hp := fun j => c₄.nmem (R + 3 + 2 * n + j))
      (cf := fun j => c₄.nmem (Y + 1 * j))
      (fun j hj => by
        rw [mrec _ (by clear * - hj l0; omega)]; exact hA.rp j hj) hkey mcf hi
    unfold bf
    by_cases hm : g i ∈ pcNf M Q x.1.piece x.2.1
    · rw [iteT (key.1 hm), iteT hm]
    · rw [iteF (fun h => hm (key.2 h)), iteF hm]
  · rw [m₆ a (by clear * - ha; omega), m₅ a (by clear * - ha; omega), m₄, m₃ a (by clear * - ha; omega),
      m₂ a (by clear * - ha; omega), m₁]
  · unfold nfW at hy
    rw [f₆ y (by unfold vscr; clear * - hy; omega) (by clear * - hy; omega)
      (by clear * - hy; omega), g₅ y (by unfold vscr; clear * - hy; omega)
      (by clear * - hy; omega) (by clear * - hy; omega) (by clear * - hy; omega),
      f₁ y (by unfold nfW; exact hy)]


end Exec

end MfDrv

end BKMNW

end PlanarFlow
