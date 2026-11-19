module

public import PlanarFlow.BKMNW.LgS5A

/-!
# The large-piece separator, stage 5: the part before the test (`s5Pre`)

* `s5Kv`, `s5Av`, `s5Wv`: the parameters `K`, `A`, `W₀ = #P + K nTouch` of the split of a piece
  (`spSR`/`spHR` by `holeStep`);
* `S2Arr` (the arrays of stage 2 at `U`: the core's enumeration `IX`, `NF = 1`, `TH`, `RV0`, the
  rotation `SG`), **`S2Arr.congr`**;
* `s5Fr` (the registers kept by stage 5);
* **`s5Pre_exec`**: `s5A ; lgPrep ; s5B ; lgPar ; s5Sv` from a record: within
  `130 n + 30 k + 200` steps, `S2Arr`, `n' = #B` in `5811` and `3103`, the parameters in
  `5910 … 5914` and `3104 … 3108`, memory below `U` kept.
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

variable (M) in
/-- The weight `K` of a hole in the split of a piece (`kH P` for a split by holes). -/
noncomputable def s5Kv (P : Finset D) (Hs : List (Finset V)) (bb : Bool) : ℕ :=
  if holeStep M P Hs bb = true then kH P else 0

variable (M) in
/-- The weight bound `A` of the split of a piece. -/
noncomputable def s5Av (P : Finset D) (Hs : List (Finset V)) (bb : Bool) : ℕ :=
  if holeStep M P Hs bb = true then aH P else aS P

variable (M) in
/-- The total weight `W₀ = #P + K nTouch` of the split of a piece. -/
noncomputable def s5Wv (P : Finset D) (Hs : List (Finset V)) (bb : Bool) : ℕ :=
  P.card + s5Kv M P Hs bb * nTouch M P Hs

/-- The registers kept by stage 5 (below `3103`, `3110 … 4399`, from `7000`). -/
def s5Fr (x : ℕ) : Prop := x < 3103 ∨ (3109 < x ∧ x < 4400) ∨ 7000 ≤ x

variable (M) in
/-- **The arrays of stage 2** at `U` (`n` darts of the record, `n'` of the core's piece map `B`):
`IX` at `U + 2n` (the enumeration `g ∘ IX` of `B`, increasing in `gid`), `SG` at `U + 3n` (the
rotation `st` on it), `NF = 1`, `TH`, `RV0` at `b = U + 4n`. -/
structure S2Arr (gid : D → ℕ) (mem : ℕ → ℕ) (U n n' : ℕ) (g : ℕ → D) (B : Finset D)
    (Hs : List (Finset V)) (st : Perm D) : Prop where
  le : n' ≤ n
  ix : ∀ j < n', mem (U + 2 * n + j) < n ∧ g (mem (U + 2 * n + j)) ∈ B
  ixs : ∀ y ∈ B, ∃ j < n', g (mem (U + 2 * n + j)) = y
  ixm : ∀ i j, i < j → j < n' → gid (g (mem (U + 2 * n + i))) < gid (g (mem (U + 2 * n + j)))
  nf : ∀ j < n', mem (U + 4 * n + j) = 1
  th : ∀ j < n', mem (U + 4 * n + n' + j) = hlab Hs (M.tail (g (mem (U + 2 * n + j))))
  rv : ∀ j < n', mem (U + 4 * n + 2 * n' + j) < n' ∧
    g (mem (U + 2 * n + mem (U + 4 * n + 2 * n' + j))) = M.rev (g (mem (U + 2 * n + j)))
  sg : ∀ j < n', mem (U + 3 * n + j) < n' ∧
    g (mem (U + 2 * n + mem (U + 3 * n + j))) = st (g (mem (U + 2 * n + j)))

lemma S2Arr.congr {gid : D → ℕ} {mem mem' : ℕ → ℕ} {U n n' : ℕ} {g : ℕ → D} {B : Finset D}
    {Hs : List (Finset V)} {st : Perm D} (h : S2Arr M gid mem U n n' g B Hs st)
    (he : ∀ a, U + 2 * n ≤ a → a < U + 4 * n + 3 * n' → mem' a = mem a) :
    S2Arr M gid mem' U n n' g B Hs st where
  le := h.le
  ix j hj := by rw [he (U + 2 * n + j) (by omega) (by have := h.le; omega)]; exact h.ix j hj
  ixs y hy := by
    obtain ⟨j, hj, e⟩ := h.ixs y hy
    exact ⟨j, hj, by rw [he (U + 2 * n + j) (by omega) (by have := h.le; omega)]; exact e⟩
  ixm i j hij hj := by
    have := h.le
    rw [he (U + 2 * n + i) (by omega) (by omega), he (U + 2 * n + j) (by omega) (by omega)]
    exact h.ixm i j hij hj
  nf j hj := by rw [he (U + 4 * n + j) (by omega) (by omega)]; exact h.nf j hj
  th j hj := by
    have := h.le
    rw [he (U + 4 * n + n' + j) (by omega) (by omega), he (U + 2 * n + j) (by omega) (by omega)]
    exact h.th j hj
  rv j hj := by
    have := h.le
    have h1 := h.rv j hj
    rw [he (U + 4 * n + 2 * n' + j) (by omega) (by omega)]
    rw [he (U + 2 * n + mem (U + 4 * n + 2 * n' + j)) (by omega) (by omega),
      he (U + 2 * n + j) (by omega) (by omega)]
    exact h1
  sg j hj := by
    have := h.le
    have h1 := h.sg j hj
    rw [he (U + 3 * n + j) (by omega) (by omega)]
    rw [he (U + 2 * n + mem (U + 3 * n + j)) (by omega) (by omega),
      he (U + 2 * n + j) (by omega) (by omega)]
    exact h1

section Exec

variable {I : Input} {W : ℕ}

/-- **Stage 5 before the test**: `s5A ; lgPrep ; s5B ; lgPar ; s5Sv` on a record. -/
theorem s5Pre_exec {gid : D → ℕ} {ν : V → ℕ} {S T Q : Finset V} {x : MCall M} {m n R : ℕ}
    {g : ℕ → D} (hQ : QPar Q ν) (hd : x.2.1.Pairwise Disjoint) {st : Perm D}
    (hst : ∀ d ∈ pdarts M (core M Q x.1.piece) x.2.1, st d ∈ pdarts M (core M Q x.1.piece) x.2.1)
    (c : Config) (hc : WordsBounded W c) (hA : RArr M gid ν S T x m n R g c.nmem)
    (hSP : ∀ i < n, g i ∈ pdarts M (core M Q x.1.piece) x.2.1 →
      c.nmem (R + 3 + 5 * n + i) < n ∧ g (c.nmem (R + 3 + 5 * n + i)) = st (g i))
    {U bfl : ℕ} {bb : Bool} (r0 : c.nreg 3100 = R) (r1 : c.nreg 3101 = U)
    (r2 : c.nreg 3102 = x.2.1.length) (hRn : c.nmem R = n) (hRb : c.nmem (R + 2) = bfl)
    (hb : bfl ≤ 1) (hbb : bfl = 1 ↔ bb = true) (l0 : R + 3 + 6 * n + m ≤ U)
    (w : U + R + 600 * n + 5 * x.2.1.length + 300 ≤ W) :
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
    m₁, rr₁, rm₁, o₁⟩ := s5A_exec (I := I) c hc r0 r1 hRn (by omega) (by omega)
  -- `lgPrep`
  obtain ⟨c₂, t₂, e₂, ht₂, p11, pix, pixs, pixm, pnf, pth, prv, psg, m₂, f₂, rr₂, rm₂, o₂⟩ :=
    lgPrep_exec (P := I) hQ hd hst c₁ e₁.wb_right (by rw [m₁]; exact hA)
      (by rw [m₁]; exact hSP) a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a14 a21 l0
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have g₂ : ∀ y, ¬ lgPw y → c₂.nreg y = c₁.nreg y := f₂
  -- the registers of `lgPar`
  obtain ⟨c₃, t₃, e₃, ht₃, b70, b15, b16, b21, f₃, m₃, rr₃, rm₃, o₃⟩ :=
    s5B_exec (I := I) c₂ e₂.wb_right (bfl := bfl)
      (((g₂ 3100 (by unfold lgPw; omega)).trans (f₁ 3100 (by omega))).trans r0)
      (((g₂ 3102 (by unfold lgPw; omega)).trans (f₁ 3102 (by omega))).trans r2)
      ((g₂ 5800 (by unfold lgPw; omega)).trans a00) ((g₂ 5810 (by unfold lgPw; omega)).trans a10)
      (by rw [m₂ (R + 2) (by omega), m₁]; exact hRb) (by omega) (by omega)
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

end Exec

end MfDrv

end BKMNW

end PlanarFlow
