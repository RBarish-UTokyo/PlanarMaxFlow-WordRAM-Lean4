module

public import PlanarFlow.BKMNW.MsCutA

/-!
# The cut map of the path on the machine, part B: a generic write loop

**`wrLoop VAL`**: for `i < m` (`r8200`), run the value block `VAL` (which sets `r8206` to the
selection flag `1`/`0`, and, when selected, `r8207 = pos i`, `r8208 = xv i`, `r8209 = yv i`), and
if selected write `RVo[pos i] := xv i`, `RTo[pos i] := yv i` (`RVo = r8201`, `RTo = r8202`).
**`wrLoop_exec`**: for a value block meeting its specification (`hval`) on every configuration
whose registers and memory (off the outputs) are those of the start, and positions injective on
the selected indices and below `N`, within `(B + 8) m + 5` steps every selected `i` has its two
words written; the other words, the registers outside `8203 … 8219`, reals and output kept.

Registers: `8200 … 8202` (inputs), `8203 = 1`, `8204 = 0`, `8205 = i`, `8206 … 8209` (the values),
`8210` (address), `8211 … 8219` (scratch of the value blocks).
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

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The two stores. -/
def wrStore : Stmt :=
  block [.addN 8210 8201 8207, .storeN 8210 8208, .addN 8210 8202 8207, .storeN 8210 8209]

/-- The body: values, the selected stores, `i := i + 1`. -/
def wrBody (VAL : Stmt) : Stmt :=
  .seq VAL (.seq (.ifLtN 8204 8206 wrStore .skip) (block [.addN 8205 8205 8203]))

/-- **The write loop** with the value block `VAL`. -/
def wrLoop (VAL : Stmt) : Stmt :=
  .seq (block [.constN 8203 1, .constN 8204 0, .constN 8205 0]) (.whileLtN 8205 8200 (wrBody VAL))

theorem wrStore_exec (c : Config) (hc : WordsBounded W c) {RVo RTo p x y : ℕ}
    (r1 : c.nreg 8201 = RVo) (r2 : c.nreg 8202 = RTo) (r7 : c.nreg 8207 = p)
    (r8 : c.nreg 8208 = x) (r9 : c.nreg 8209 = y) (w1 : RVo + p ≤ W) (w2 : RTo + p ≤ W) :
    ∃ c' t, Exec P W wrStore c c' t ∧ t = 4 ∧
      c'.nmem = upd (upd c.nmem (RVo + p) x) (RTo + p) y ∧
      (∀ r, r ≠ 8210 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold wrStore
  exec_block
  all_goals try ((try config_simp); (try simp only [r1, r2, r7, r8, r9]); omega)
  refine ⟨rfl, ?_, fun r a => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r1, r2, r7, r8, r9]; done)
    | (simp only [upd_apply]; split_ifs <;> omega)

/-- The specification of a value block for the loop started at `c`. -/
def ValSpec (VAL : Stmt) (B : ℕ) (c : Config) (m RVo RTo N : ℕ) (sel : ℕ → Bool)
    (pos xv yv : ℕ → ℕ) : Prop :=
  ∀ (d : Config) (i : ℕ), WordsBounded W d → i < m → d.nreg 8205 = i →
    d.nreg 8203 = 1 → d.nreg 8204 = 0 →
    (∀ r, (r < 8203 ∨ 8219 < r) → d.nreg r = c.nreg r) →
    (∀ a, (a < RVo ∨ RVo + N ≤ a) → (a < RTo ∨ RTo + N ≤ a) → d.nmem a = c.nmem a) →
    ∃ d' k, Exec P W VAL d d' k ∧ k ≤ B ∧ d'.nreg 8206 = (if sel i then 1 else 0) ∧
      (sel i = true → d'.nreg 8207 = pos i ∧ d'.nreg 8208 = xv i ∧ d'.nreg 8209 = yv i) ∧
      (∀ r, (r < 8206 ∨ 8219 < r) → d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output

/-- **The write loop.** -/
theorem wrLoop_exec (c : Config) (hc : WordsBounded W c) {VAL : Stmt} {B m RVo RTo N : ℕ}
    {sel : ℕ → Bool} {pos xv yv : ℕ → ℕ}
    (r0 : c.nreg 8200 = m) (r1 : c.nreg 8201 = RVo) (r2 : c.nreg 8202 = RTo)
    (hval : ValSpec (W := W) (P := P) VAL B c m RVo RTo N sel pos xv yv)
    (hpos : ∀ i < m, sel i = true → pos i < N)
    (hinj : ∀ i < m, ∀ i' < m, sel i = true → sel i' = true → pos i = pos i' → i = i')
    (hd : RVo + N ≤ RTo ∨ RTo + N ≤ RVo) (w1 : RVo + N ≤ W) (w2 : RTo + N ≤ W)
    (w3 : m + 1 ≤ W) :
    ∃ c' t, Exec P W (wrLoop VAL) c c' t ∧ t ≤ (B + 8) * m + 5 ∧
      (∀ i < m, sel i = true → c'.nmem (RVo + pos i) = xv i ∧ c'.nmem (RTo + pos i) = yv i) ∧
      (∀ a, (a < RVo ∨ RVo + N ≤ a) → (a < RTo ∨ RTo + N ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (∀ i < m, sel i = true → a ≠ RVo + pos i ∧ a ≠ RTo + pos i) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 8203 ∨ 8219 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold wrLoop
  obtain ⟨c₁, k₁, e₁, hk₁, g3, g4, g5, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 8203 1, .constN 8204 0, .constN 8205 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 8203 = 1 ∧ c₁.nreg 8204 = 0 ∧ c₁.nreg 8205 = 0 ∧
      (∀ x, (x < 8203 ∨ 8205 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun i d =>
    (∀ r, (r < 8203 ∨ 8219 < r) → d.nreg r = c.nreg r) ∧ d.nreg 8203 = 1 ∧ d.nreg 8204 = 0 ∧
    (∀ i' < i, sel i' = true → d.nmem (RVo + pos i') = xv i' ∧ d.nmem (RTo + pos i') = yv i') ∧
    (∀ a, (∀ i' < i, sel i' = true → a ≠ RVo + pos i' ∧ a ≠ RTo + pos i') →
      d.nmem a = c.nmem a) ∧
    d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h05, j1, j2, j3, j4, j5, j6, j7, j8⟩ := lnRange (P := P)
    (a := 8205) (b := 8200) (body := wrBody VAL) J (B := B + 6) c₁ e₁.wb_right g5
    (by rw [gn₁ _ (by omega), r0]) (Nat.zero_le m)
    ⟨fun r hr => gn₁ r (by omega), g3, g4, fun i' hi' => absurd hi' (by omega),
      fun a _ => by rw [gm₁], gr₁, grm₁, go₁⟩
    (fun i d hlo hhi hw h05 h00 ⟨j1, j2, j3, j4, j5, j6, j7, j8⟩ => by
      obtain ⟨d₁, k₁', ex₁, hk₁', v06, v789, vR, vm, vr, vrm, vo⟩ := hval d i hw hhi h05 j2 j3 j1
        (fun a h1 h2 => j5 a fun i' hi' hs => by
          have := hpos i' (by omega) hs; constructor <;> omega)
      have q1 : ∀ r, (r < 8206 ∨ 8219 < r) → d₁.nreg r = d.nreg r := vR
      -- the increment
      have inc : ∀ e : Config, WordsBounded W e → e.nreg 8205 = i → e.nreg 8203 = 1 →
          ∃ e' k, Exec P W (block [.addN 8205 8205 8203]) e e' k ∧ k = 1 ∧
            e'.nreg 8205 = i + 1 ∧ (∀ x, x ≠ 8205 → e'.nreg x = e.nreg x) ∧
            e'.nmem = e.nmem ∧ e'.rreg = e.rreg ∧ e'.rmem = e.rmem ∧
            e'.output = e.output := fun e he s05 s03 => by
        exec_block
        all_goals try ((try config_simp); (try simp only [s05, s03]); omega)
        refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; simp only [s05, s03]
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      have d05 : d₁.nreg 8205 = i := by rw [q1 _ (by omega), h05]
      have d03 : d₁.nreg 8203 = 1 := by rw [q1 _ (by omega), j2]
      have d04 : d₁.nreg 8204 = 0 := by rw [q1 _ (by omega), j3]
      cases hs : sel i
      · -- not selected
        have t : ¬ d₁.nreg 8204 < d₁.nreg 8206 := by rw [v06, d04, hs]; simp
        obtain ⟨d₃, k₃, ex₃, hk₃, s05, sR, sm, sr, srm, so⟩ := inc d₁ ex₁.wb_right d05 d03
        refine ⟨d₃, k₁' + ((0 + 2) + k₃), .seq ex₁ (.seq (.ifLtN_false t (.skip ex₁.wb_right))
          ex₃), by omega, s05, by rw [sR _ (by omega), q1 _ (by omega), h00], fun r hr => ?_,
          by rw [sR _ (by omega), d03], by rw [sR _ (by omega), d04],
          fun i' hi' hs' => ?_, fun a ha => ?_, by rw [sr, vr, j6], by rw [srm, vrm, j7],
          by rw [so, vo, j8]⟩
        · rw [sR r (by omega), q1 r (by omega), j1 r hr]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
          · rw [sm, vm]; exact j4 i' hi' hs'
          · rw [hs] at hs'; exact absurd hs' (by simp)
        · rw [sm, vm]; exact j5 a fun i' hi' hs' => ha i' (by omega) hs'
      · -- selected
        obtain ⟨v7, v8, v9⟩ := v789 hs
        have hp := hpos i hhi hs
        have t : d₁.nreg 8204 < d₁.nreg 8206 := by rw [v06, d04, hs]; simp
        obtain ⟨d₂, k₂', ex₂, hk₂', sm₂, sR₂, sr₂, srm₂, so₂⟩ := wrStore_exec (P := P) d₁
          ex₁.wb_right (by rw [q1 _ (by omega), j1 _ (by omega), r1])
          (by rw [q1 _ (by omega), j1 _ (by omega), r2]) v7 v8 v9 (by omega) (by omega)
        obtain ⟨d₃, k₃, ex₃, hk₃, s05, sR, sm, sr, srm, so⟩ := inc d₂ ex₂.wb_right
          (by rw [sR₂ _ (by omega), d05]) (by rw [sR₂ _ (by omega), d03])
        refine ⟨d₃, k₁' + ((k₂' + 1) + k₃), .seq ex₁ (.seq (.ifLtN_true t ex₂) ex₃), by omega,
          s05, by rw [sR _ (by omega), sR₂ _ (by omega), q1 _ (by omega), h00],
          fun r hr => ?_, by rw [sR _ (by omega), sR₂ _ (by omega), d03],
          by rw [sR _ (by omega), sR₂ _ (by omega), d04], fun i' hi' hs' => ?_, fun a ha => ?_,
          by rw [sr, sr₂, vr, j6], by rw [srm, srm₂, vrm, j7], by rw [so, so₂, vo, j8]⟩
        · rw [sR r (by omega), sR₂ r (by omega), q1 r (by omega), j1 r hr]
        · rw [sm, sm₂, vm]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
          · have hp' := hpos i' (by omega) hs'
            have hne : pos i' ≠ pos i := fun e => by
              have := hinj i' (by omega) i hhi hs' hs e; omega
            rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
              upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
            exact j4 i' hi' hs'
          · rw [upd_other _ _ _ (by omega), upd_same, upd_same]; exact ⟨rfl, rfl⟩
        · obtain ⟨a1, a2⟩ := ha i (by omega) hs
          rw [sm, sm₂, vm, upd_other _ _ _ a2, upd_other _ _ _ a1]
          exact j5 a fun i' hi' hs' => ha i' (by omega) hs')
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, ?_, fun i hi hs => j4 i hi hs, fun a h1 h2 => ?_, j5, j1, j6,
    j7, j8⟩
  · have : k₂ ≤ (B + 6 + 2) * m + 2 := by simpa using hk₂
    have e : (B + 6 + 2) * m = (B + 8) * m := by ring
    omega
  · exact j5 a fun i' hi' hs' => by have := hpos i' hi' hs'; constructor <;> omega

end MsEnc

end BKMNW

end PlanarFlow
