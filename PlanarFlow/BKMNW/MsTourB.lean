module

public import PlanarFlow.BKMNW.MsTourA

/-!
# The corner order on the machine, part B: zeroing, `NX`, the face labels, the walk

* `ftZ` (zero `FL`, `LF`, `FP`, `VIS`), `ftNX` (`NX[i] := RT[RV[i]]`, `lgProg`), `ftFL` (the
  orbit labels of `NX`, `olProg`), with their `_exec` lemmas;
* **`ftW`**: the walk around the path on the tour array `TA` from `x₀ = P[0]`: `VIS[x] := 1`,
  `TR[j] := x`, `x := TA[x]`, `j := j + 1` until `VIS[x] ≠ 0`; then the period into `r8156`.
  **`ftW_exec`**: for `TA` a permutation of `[0, m)` (`OrbLab.PermOn`), within `11 m + 8` steps
  `r8156 = t` with `0 < t`, `f^[t] x₀ = x₀`, `f^[s] x₀ ≠ x₀` for `0 < s < t` (`t` is the period),
  and `TR[s] = f^[s] x₀` for `s < t`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab

variable {P : Input} {W : ℕ}

/-! ### Zeroing, `NX`, the face labels -/

/-- Zero `[S + m, S + 5m)` (`FL`, `LF`, `FP`, `VIS`). -/
def ftZ : Stmt := .seq (block [.copyN 5030 8168, .copyN 5031 8159]) mzFill

/-- `NX[i] := RT[RV[i]]` at `S`. -/
def ftNX : Stmt :=
  .seq (block [.copyN 6210 8150, .copyN 6211 8151, .copyN 6212 8152, .copyN 6213 8155]) lgProg

/-- The orbit labels of `NX` at `S + m`. -/
def ftFL : Stmt := .seq (block [.copyN 7350 8155, .copyN 7351 8159, .copyN 7352 8150]) olProg

theorem ftZ_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb S : ℕ}
    (hR : FtRegs c m RVb RTb k Pb S) (hW : S + 9 * m + 2 ≤ W) :
    ∃ c' t, Exec P W ftZ c c' t ∧ t ≤ 20 * m + 7 ∧
      (∀ i < 4 * m, c'.nmem (S + m + i) = 0) ∧
      (∀ a, (a < S + m ∨ S + 5 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5030 ∨ 5035 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 5030 8168, .copyN 5031 8159]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 5030 = 4 * m ∧ c₁.nreg 5031 = S + m ∧
      (∀ x, x ≠ 5030 → x ≠ 5031 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [hR.r68, hR.r59]); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    · simp only [hR.r68]
    · simp only [hR.r59]
    · simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c₂, k₂, e₂, hk₂, hz, hm, hn, hr, hrm, ho⟩ :=
    mzFill_exec (P := P) c₁ e₁.wb_right g0 g1 (by omega) (by omega)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, hz, fun a ha => by rw [hm a (by omega), gm₁],
    fun x hx => ?_, by rw [hr, gr₁], by rw [hrm, grm₁], by rw [ho, go₁]⟩
  rw [hn x (by omega), gn₁ x (by omega) (by omega)]

theorem ftNX_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb S : ℕ}
    (hR : FtRegs c m RVb RTb k Pb S) (hW : S + 9 * m + 2 ≤ W)
    (hRV : ∀ i < m, c.nmem (RVb + i) < m) (wRV : RVb + m ≤ W) (wRT : RTb + m ≤ W)
    (dRV : RVb + m ≤ S ∨ S + m ≤ RVb) (dRT : RTb + m ≤ S ∨ S + m ≤ RTb) :
    ∃ c' t, Exec P W ftNX c c' t ∧ t ≤ 9 * m + 8 ∧
      (∀ i < m, c'.nmem (S + i) = c.nmem (RTb + c.nmem (RVb + i))) ∧
      (∀ a, (a < S ∨ S + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6210 ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, g3, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 6210 8150, .copyN 6211 8151, .copyN 6212 8152, .copyN 6213 8155])
        c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg 6210 = m ∧ c₁.nreg 6211 = RVb ∧ c₁.nreg 6212 = RTb ∧ c₁.nreg 6213 = S ∧
      (∀ x, (x < 6210 ∨ 6213 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [hR.r50, hR.r51, hR.r52, hR.r55]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals first
      | (simp only [hR.r50, hR.r51, hR.r52, hR.r55]; done)
      | (simp only [upd_apply]; split_ifs <;> omega)
  obtain ⟨c₂, k₂, e₂, hk₂, hv, hm, hn, hr, hrm, ho⟩ :=
    lgProg_exec (P := P) c₁ e₁.wb_right g0 g1 g2 g3 (by omega) (by omega) (by omega)
      (fun j hj => by rw [gm₁]; have := hRV j hj; omega)
      (fun j hj h => by omega) (fun j hj h => by rw [gm₁] at h; have := hRV j hj; omega)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fun i hi => by rw [hv i hi, gm₁],
    fun a ha => by rw [hm a (by omega), gm₁], fun x hx => ?_, by rw [hr, gr₁],
    by rw [hrm, grm₁], by rw [ho, go₁]⟩
  rw [hn x (by omega), gn₁ x (by omega)]

theorem ftFL_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb S : ℕ}
    (hR : FtRegs c m RVb RTb k Pb S) (hW : S + 9 * m + 2 ≤ W) {f : ℕ → ℕ}
    (hp : PermOn f m) (hf : ∀ i < m, c.nmem (S + i) = f i)
    (hz : ∀ i < m, c.nmem (S + m + i) = 0) :
    ∃ c' t, Exec P W ftFL c c' t ∧ t ≤ 20 * m + 7 ∧
      (∀ i < m, c'.nmem (S + m + i) = olab f i + 1) ∧
      (∀ a, (a < S + m ∨ S + 2 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 7350 ∨ 7352 < x) → (x < 7400 ∨ 7405 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 7350 8155, .copyN 7351 8159, .copyN 7352 8150]) c c₁ k₁ ∧
      k₁ = 3 ∧ c₁.nreg 7350 = S ∧ c₁.nreg 7351 = S + m ∧ c₁.nreg 7352 = m ∧
      (∀ x, (x < 7350 ∨ 7352 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [hR.r50, hR.r59, hR.r55]); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals first
      | (simp only [hR.r50, hR.r59, hR.r55]; done)
      | (simp only [upd_apply]; split_ifs <;> omega)
  obtain ⟨c₂, k₂, e₂, hk₂, hv, hm, hn, hr, hrm, ho⟩ :=
    olProg_exec (P := P) hp (Pb := S) (Lb := S + m) (by omega) (by omega) (by omega) c₁
      e₁.wb_right g0 g1 g2 (fun x hx => by rw [gm₁, hf x hx])
      (fun x hx => by rw [gm₁, hz x hx])
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, hv, fun a ha => by rw [hm a (by omega), gm₁],
    fun x h1 h2 => ?_, by rw [hr, gr₁], by rw [hrm, grm₁], by rw [ho, go₁]⟩
  rw [hn x (by omega), gn₁ x h1]

/-! ### The walk -/

/-- `x := P[0]`, `j := 0`, `v := VIS[x]`. -/
def ftW0 : Stmt :=
  block [.loadN 8173 8154, .constN 8172 0, .addN 8174 8162 8173, .loadN 8175 8174]

/-- `VIS[x] := 1`, `TR[j] := x`, `x := TA[x]`, `j := j + 1`, `v := VIS[x]`. -/
def ftWBody : Stmt :=
  block [.addN 8174 8162 8173, .storeN 8174 8158, .addN 8174 8164 8172, .storeN 8174 8173,
    .addN 8174 8163 8173, .loadN 8173 8174, .addN 8172 8172 8158, .addN 8174 8162 8173,
    .loadN 8175 8174]

/-- **The walk around the path** on the tour array; the period into `r8156`. -/
def ftW : Stmt := .seq ftW0 (.seq (.whileLtN 8175 8158 ftWBody) (block [.copyN 8156 8172]))

theorem ftW0_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb S x₀ : ℕ}
    (hR : FtRegs c m RVb RTb k Pb S) (hx : c.nmem Pb = x₀) (hx₀ : x₀ < m)
    (hW : S + 9 * m + 2 ≤ W) :
    ∃ c' t, Exec P W ftW0 c c' t ∧ t = 4 ∧ c'.nreg 8173 = x₀ ∧ c'.nreg 8172 = 0 ∧
      c'.nreg 8175 = c.nmem (S + 4 * m + x₀) ∧
      (∀ x, (x < 8172 ∨ 8175 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hc.2 Pb
  unfold ftW0
  exec_block
  all_goals try ((try config_simp); (try simp only [hR.r54, hR.r62, hx]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [hR.r54, hR.r62, hx]; done)
    | (simp only [upd_apply]; split_ifs <;> omega)

theorem ftWBody_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb S x j y : ℕ}
    (hR : FtRegs c m RVb RTb k Pb S) (r73 : c.nreg 8173 = x) (r72 : c.nreg 8172 = j)
    (hx : x < m) (hj : j < m) (hy : c.nmem (S + 5 * m + x) = y) (hym : y < m)
    (hW : S + 9 * m + 2 ≤ W) :
    ∃ c' t, Exec P W ftWBody c c' t ∧ t = 9 ∧ c'.nreg 8173 = y ∧ c'.nreg 8172 = j + 1 ∧
      c'.nmem = upd (upd c.nmem (S + 4 * m + x) 1) (S + 6 * m + j) x ∧
      c'.nreg 8175 = upd (upd c.nmem (S + 4 * m + x) 1) (S + 6 * m + j) x (S + 4 * m + y) ∧
      (∀ r, (r < 8172 ∨ 8175 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hy' : upd (upd c.nmem (S + 4 * m + x) 1) (S + 6 * m + j) x (S + 5 * m + x) = y := by
    rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), hy]
  unfold ftWBody
  exec_block
  all_goals try ((try config_simp); (try simp only [hR.r58, hR.r62, hR.r63, hR.r64, r73, r72, hy']); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r a => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [hR.r58, hR.r62, hR.r63, hR.r64, r73, r72, hy']; done)
    | (simp only [upd_apply]; split_ifs <;> omega)

/-- The invariant of the walk after `t` steps. -/
def WInv (f : ℕ → ℕ) (m S x₀ : ℕ) (c₀ : Config) (c : Config) : Prop :=
  WordsBounded W c ∧ (∀ r, (r < 8172 ∨ 8175 < r) → c.nreg r = c₀.nreg r) ∧
  ∃ t, c.nreg 8173 = f^[t] x₀ ∧ c.nreg 8172 = t ∧
    c.nreg 8175 = c.nmem (S + 4 * m + f^[t] x₀) ∧
    (∀ y < m, c.nmem (S + 4 * m + y) = if ∃ s < t, f^[s] x₀ = y then 1 else 0) ∧
    (∀ s < t, c.nmem (S + 6 * m + s) = f^[s] x₀) ∧
    (∀ s s', s < s' → s' < t → f^[s] x₀ ≠ f^[s'] x₀) ∧
    zeros c.nmem (S + 4 * m) m + t = m ∧
    (∀ a, (a < S + 4 * m ∨ S + 5 * m ≤ a) → (a < S + 6 * m ∨ S + 7 * m ≤ a) →
      c.nmem a = c₀.nmem a) ∧
    c.rreg = c₀.rreg ∧ c.rmem = c₀.rmem ∧ c.output = c₀.output

lemma one_le_zeros {mem : ℕ → ℕ} {Lb m y : ℕ} (hy : y < m) (h0 : mem (Lb + y) = 0) :
    1 ≤ zeros mem Lb m := by
  have := zeros_upd (mem := mem) (Lb := Lb) (v := 1) hy h0 (by omega)
  omega

/-- **The walk loop.** -/
theorem ftW_loop {m : ℕ} {f : ℕ → ℕ} (hp : PermOn f m) {RVb RTb k Pb S x₀ : ℕ} (hx₀ : x₀ < m)
    (hW : S + 9 * m + 2 ≤ W) {c₀ : Config} (hR : FtRegs c₀ m RVb RTb k Pb S)
    (hf : ∀ i < m, c₀.nmem (S + 5 * m + i) = f i) {c : Config}
    (hc : WInv (W := W) f m S x₀ c₀ c) :
    ∃ c' u, Exec P W (.whileLtN 8175 8158 ftWBody) c c' u ∧ u ≤ 11 * m + 2 ∧
      WInv (W := W) f m S x₀ c₀ c' ∧ ¬ c'.nreg 8175 < c'.nreg 8158 := by
  obtain ⟨c', u, ex, hI, hstop, hu⟩ := whileLtN_potL (P := P) (W := W) (a := 8175) (b := 8158)
    (body := ftWBody) (WInv (W := W) f m S x₀ c₀) (fun c => 11 * zeros c.nmem (S + 4 * m) m)
    (fun c h => h.1)
    (fun c ⟨hw, hR', t, r73, r72, r75, hV, hT, hD, hZ, hM, hrr, hrm, ho⟩ hlt => by
      have hRc : FtRegs c m RVb RTb k Pb S :=
        hR.of fun r h1 h2 _ _ => hR' r (by omega)
      have hxt : f^[t] x₀ < m := OrbLab.iter_lt hp hx₀ t
      have h0 : c.nmem (S + 4 * m + f^[t] x₀) = 0 := by
        rw [r75, hRc.r58] at hlt; omega
      have hnot : ¬ ∃ s < t, f^[s] x₀ = f^[t] x₀ := by
        intro h; have := hV _ hxt; simp only [h, ↓reduceIte] at this; omega
      have hz1 := one_le_zeros hxt h0
      have ht : t < m := by omega
      have hy : c.nmem (S + 5 * m + f^[t] x₀) = f^[t + 1] x₀ := by
        rw [hM _ (by omega) (by omega), hf _ hxt, Function.iterate_succ_apply']
      obtain ⟨c₁, k₁, e₁, hk₁, s73, s72, sm, s75, sR, srr, srm, so⟩ :=
        ftWBody_exec (P := P) c hw hRc r73 r72 hxt ht hy (OrbLab.iter_lt hp hx₀ (t + 1)) hW
      have hz := zeros_upd (mem := c.nmem) (Lb := S + 4 * m) (v := 1) hxt h0 (by omega)
      have hzT : zeros (upd (upd c.nmem (S + 4 * m + f^[t] x₀) 1) (S + 6 * m + t) (f^[t] x₀))
          (S + 4 * m) m = zeros (upd c.nmem (S + 4 * m + f^[t] x₀) 1) (S + 4 * m) m := by
        unfold zeros
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [upd_other _ _ _ (by have := Finset.mem_range.1 hy; omega)]
      refine ⟨c₁, k₁, e₁, ⟨e₁.wb_right, fun r hr => by rw [sR r hr, hR' r hr], t + 1, s73,
        s72, by rw [s75, sm], fun y hy' => ?_, fun s hs => ?_, fun s s' h1 h2 => ?_, ?_,
        fun a ha ha' => ?_, by rw [srr, hrr], by rw [srm, hrm], by rw [so, ho]⟩, ?_⟩
      · rw [sm, upd_other _ _ _ (by omega)]
        have hiff : (∃ s < t + 1, f^[s] x₀ = y) ↔ (∃ s < t, f^[s] x₀ = y) ∨ f^[t] x₀ = y := by
          constructor
          · rintro ⟨s, hs, e⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
            · exact Or.inl ⟨s, hs, e⟩
            · exact Or.inr e
          · rintro (⟨s, hs, e⟩ | e)
            · exact ⟨s, by omega, e⟩
            · exact ⟨t, by omega, e⟩
        by_cases hyt : f^[t] x₀ = y
        · subst hyt; rw [upd_same]; simp only [hiff, or_true, ↓reduceIte]
        · rw [upd_other _ _ _ (by omega), hV y hy']
          simp only [hiff, hyt, or_false]
      · rw [sm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact hT s hs
        · rw [upd_same]
      · rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
        · exact hD s s' h1 h2
        · exact fun e => hnot ⟨s, h1, e⟩
      · rw [sm, hzT]; omega
      · rw [sm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        exact hM a ha (by omega)
      · rw [sm, hzT]; omega)
    hc
  exact ⟨c', u, ex, by
    obtain ⟨-, -, t, -, -, -, -, -, -, hZ, -⟩ := hc
    omega, hI, hstop⟩

/-- **The walk around the path**: for a tour array `TA = f` (a permutation of `[0, m)`), from
`VIS` zero and `x₀ = P[0] < m`, within `11 m + 8` steps `r8156 = t` with `0 < t ≤ m`,
`f^[t] x₀ = x₀`, `f^[s] x₀ ≠ x₀` for `0 < s < t`, and `TR[s] = f^[s] x₀` for `s < t`; memory
outside `VIS` and `TR`, registers outside `8156`, `8172 … 8175`, reals and output kept. -/
theorem ftW_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb S x₀ : ℕ}
    (hR : FtRegs c m RVb RTb k Pb S) {f : ℕ → ℕ} (hp : PermOn f m)
    (hf : ∀ i < m, c.nmem (S + 5 * m + i) = f i) (hx : c.nmem Pb = x₀) (hx₀ : x₀ < m)
    (hz : ∀ i < m, c.nmem (S + 4 * m + i) = 0) (hW : S + 9 * m + 2 ≤ W) :
    ∃ c' u t, Exec P W ftW c c' u ∧ u ≤ 11 * m + 8 ∧ c'.nreg 8156 = t ∧ 0 < t ∧ t ≤ m ∧
      f^[t] x₀ = x₀ ∧ (∀ s, 0 < s → s < t → f^[s] x₀ ≠ x₀) ∧
      (∀ s < t, c'.nmem (S + 6 * m + s) = f^[s] x₀) ∧
      (∀ a, (a < S + 4 * m ∨ S + 5 * m ≤ a) → (a < S + 6 * m ∨ S + 7 * m ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 8172 ∨ 8175 < r) → r ≠ 8156 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a73, a72, a75, aR, am, ar, arm, ao⟩ :=
    ftW0_exec (P := P) c hc hR hx hx₀ hW
  have hI : WInv (W := W) f m S x₀ c c₁ := by
    refine ⟨e₁.wb_right, aR, 0, a73, a72, by rw [a75, am]; rfl, fun y hy => ?_,
      fun s hs => absurd hs (by omega), fun s s' _ h => absurd h (by omega), ?_,
      fun a _ _ => by rw [am], ar, arm, ao⟩
    · rw [am, hz y hy]; simp
    · rw [am, zeros_all hz, Nat.add_zero]
  obtain ⟨c₂, k₂, e₂, hk₂, ⟨hw, hR', t, r73, r72, r75, hV, hT, hD, hZ, hM, hrr, hrm, ho⟩,
    hstop⟩ := ftW_loop (P := P) hp hx₀ hW hR hf hI
  have hRc : FtRegs c₂ m RVb RTb k Pb S := hR.of fun r h1 h2 _ _ => hR' r (by omega)
  -- the stop: `f^[t] x₀` was visited
  have hxt : f^[t] x₀ < m := OrbLab.iter_lt hp hx₀ t
  obtain ⟨s, hs, es⟩ : ∃ s < t, f^[s] x₀ = f^[t] x₀ := by
    by_contra hno
    have := hV _ hxt
    simp only [hno, ↓reduceIte] at this
    rw [r75, hRc.r58, this] at hstop; omega
  have hs0 : s = 0 := by
    by_contra hne
    have e : f (f^[s - 1] x₀) = f (f^[t - 1] x₀) := by
      rw [← Function.iterate_succ_apply' f (s - 1), ← Function.iterate_succ_apply' f (t - 1),
        show (s - 1).succ = s by omega, show (t - 1).succ = t by omega, es]
    exact hD (s - 1) (t - 1) (by omega) (by omega)
      (hp.inj _ (OrbLab.iter_lt hp hx₀ _) _ (OrbLab.iter_lt hp hx₀ _) e)
  subst hs0
  obtain ⟨c₃, k₃, e₃, hk₃, b56, bR, bm, br, brm, bo⟩ : ∃ c₃ k₃,
      Exec P W (block [.copyN 8156 8172]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 8156 = t ∧
      (∀ x, x ≠ 8156 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have := hw.1 8172
    exec_block
    all_goals try ((try config_simp); (try simp only [r72]); omega)
    refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    · simp only [r72]
    · simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, k₁ + (k₂ + k₃), t, .seq e₁ (.seq e₂ e₃), by omega, b56, hs, by omega, es.symm,
    fun s' h1 h2 e => hD 0 s' h1 h2 (by rw [e]; rfl), fun s' hs' => by rw [bm]; exact hT s' hs',
    fun a ha ha' => by rw [bm]; exact hM a ha ha', fun r hr h56 => ?_, by rw [br, hrr],
    by rw [brm, hrm], by rw [bo, ho]⟩
  rw [bR r h56, hR' r hr]

end MsEnc

end BKMNW

end PlanarFlow
