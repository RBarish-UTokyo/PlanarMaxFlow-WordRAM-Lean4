module

public import PlanarFlow.BKMNW.MsStW1

/-!
# Stage lemmas of the MSSP encoder with per-entry word bounds (generated)

Copies of the earlier stage lemmas (`MsStB2 … MsStE`, `MsEncC3`), renamed with the
suffix `W`, whose hypotheses bound every address and value by `W` separately instead of bounding
sums of several addresses (which needs `W ≥ 16 (p + R)`). The `hpProg` set-up lemmas take
`v + C ≤ W` for every value `v` they write. Same programs, same conclusions.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

section MsStD

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

variable {P : Input} {W : ℕ}


theorem dh4_execW (c : Config) (hc : WordsBounded W c) {w k t nD IM A1 P1 L K H0 P4 T2 : ℕ}
    (d20 : c.nreg 8220 = w) (d23 : c.nreg 8223 = k) (d24 : c.nreg 8224 = t) (d25 : c.nreg 8225 = nD) (d26 : c.nreg 8226 = IM) (d27 : c.nreg 8227 = A1) (d33 : c.nreg 8233 = P1) (d34 : c.nreg 8234 = L) (d36 : c.nreg 8236 = K) (d40 : c.nreg 8240 = H0) (d42 : c.nreg 8242 = P4) (d43 : c.nreg 8243 = T2)
    (hW : 2 * P1 + 2 * P4 + 30 * H0 + 38 * L + 38 * w + 120 * P1 + 60 * P4 + 12 * K + 60 * H0 + 76 * L + 76 * w + 240 * P1 + 120 * P4 + 24 * K + 1 + w + 40 * nD + 2 * k + 2 * t + T2 + 20 + w + 104 * nD + 2 * k + 2 * t + T2 + 52 + w + 104 * nD + 2 * k + 2 * t + T2 + 53 + 4 * nD + 1 + 37 * nD + k + 2 * t + 11 + 3 * nD + 3 + 4 * nD + k + 1 + 240 ≤ W ∧ A1 + 21 * nD + 6 + 240 ≤ W ∧ IM + 7 * nD + 240 ≤ W) :
    ∃ c', Exec P W dh4 c c' (hpCost dh4L) ∧
      c'.nreg 8244 = 2 * P1 + 2 * P4 ∧
      c'.nreg 8245 = 30 * H0 + 38 * L + 38 * w + 120 * P1 + 60 * P4 + 12 * K ∧
      c'.nreg 8246 = 60 * H0 + 76 * L + 76 * w + 240 * P1 + 120 * P4 + 24 * K + 1 ∧
      c'.nreg 8247 = w + 40 * nD + 2 * k + 2 * t + T2 + 20 ∧
      c'.nreg 8248 = w + 104 * nD + 2 * k + 2 * t + T2 + 52 ∧
      c'.nreg 8249 = w + 104 * nD + 2 * k + 2 * t + T2 + 53 ∧
      c'.nreg 8250 = 4 * nD + 1 ∧
      c'.nreg 8251 = 37 * nD + k + 2 * t + 11 ∧
      c'.nreg 8252 = 3 * nD + 3 ∧
      c'.nreg 8253 = 4 * nD + k + 1 ∧
      c'.nreg 8254 = A1 + 21 * nD + 6 ∧
      c'.nreg 8255 = IM + 6 * nD ∧
      c'.nreg 8256 = IM + 7 * nD ∧
      c'.nreg 8257 = IM + 4 * nD ∧
      (∀ r, (r < 8244 ∨ 8258 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8244 7370 dh4L :=
    hpShape_ok dh4L_shape (by omega) (by omega) (by simp [dh4L]) (by omega) (by simp [dh4L])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) dh4L 8244 hok c hc (fun e he => by
    simp only [dh4L, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, d20, d23, d24, d25, d26, d27, d33, d34, d36, d40, d42, d43] <;> omega)
  have g : ∀ j < 14, c'.nreg (8244 + j) =
      hpSum c.nreg (dh4L.getD j ([], 0)).1 - (dh4L.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [dh4L]; omega)
  refine ⟨c', e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [dh4L]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [dh4L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d23, d24, d25, d26, d27, d33, d34, d36, d40, d42, d43] <;> first | omega | ring
  · have := g 1 (by omega); simp [dh4L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d23, d24, d25, d26, d27, d33, d34, d36, d40, d42, d43] <;> first | omega | ring
  · have := g 2 (by omega); simp [dh4L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d23, d24, d25, d26, d27, d33, d34, d36, d40, d42, d43] <;> first | omega | ring
  · have := g 3 (by omega); simp [dh4L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d23, d24, d25, d26, d27, d33, d34, d36, d40, d42, d43] <;> first | omega | ring
  · have := g 4 (by omega); simp [dh4L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d23, d24, d25, d26, d27, d33, d34, d36, d40, d42, d43] <;> first | omega | ring
  · have := g 5 (by omega); simp [dh4L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d23, d24, d25, d26, d27, d33, d34, d36, d40, d42, d43] <;> first | omega | ring
  · have := g 6 (by omega); simp [dh4L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d23, d24, d25, d26, d27, d33, d34, d36, d40, d42, d43] <;> first | omega | ring
  · have := g 7 (by omega); simp [dh4L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d23, d24, d25, d26, d27, d33, d34, d36, d40, d42, d43] <;> first | omega | ring
  · have := g 8 (by omega); simp [dh4L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d23, d24, d25, d26, d27, d33, d34, d36, d40, d42, d43] <;> first | omega | ring
  · have := g 9 (by omega); simp [dh4L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d23, d24, d25, d26, d27, d33, d34, d36, d40, d42, d43] <;> first | omega | ring
  · have := g 10 (by omega); simp [dh4L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d23, d24, d25, d26, d27, d33, d34, d36, d40, d42, d43] <;> first | omega | ring
  · have := g 11 (by omega); simp [dh4L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d23, d24, d25, d26, d27, d33, d34, d36, d40, d42, d43] <;> first | omega | ring
  · have := g 12 (by omega); simp [dh4L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d23, d24, d25, d26, d27, d33, d34, d36, d40, d42, d43] <;> first | omega | ring
  · have := g 13 (by omega); simp [dh4L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d23, d24, d25, d26, d27, d33, d34, d36, d40, d42, d43] <;> first | omega | ring


theorem dh5_execW (c : Config) (hc : WordsBounded W c) {nD Mo Wb bt Mo2 : ℕ}
    (d25 : c.nreg 8225 = nD) (d46 : c.nreg 8246 = Mo) (d48 : c.nreg 8248 = Wb) (d49 : c.nreg 8249 = bt) (d58 : c.nreg 8258 = Mo2)
    (hW : 2 * Wb + Mo2 + Mo + 2 + 3 ≤ W ∧ bt + 3 * nD + 3 ≤ W ∧ bt + 3 * nD + 3 + 3 ≤ W) :
    ∃ c', Exec P W dh5 c c' (hpCost dh5L) ∧
      c'.nreg 8259 = 2 * Wb + Mo2 + Mo + 2 ∧
      c'.nreg 8260 = bt + 3 * nD ∧
      c'.nreg 8261 = bt + 3 * nD + 3 ∧
      (∀ r, (r < 8259 ∨ 8262 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8259 7370 dh5L :=
    hpShape_ok dh5L_shape (by omega) (by omega) (by simp [dh5L]) (by omega) (by simp [dh5L])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) dh5L 8259 hok c hc (fun e he => by
    simp only [dh5L, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, d25, d46, d48, d49, d58] <;> omega)
  have g : ∀ j < 3, c'.nreg (8259 + j) =
      hpSum c.nreg (dh5L.getD j ([], 0)).1 - (dh5L.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [dh5L]; omega)
  refine ⟨c', e, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [dh5L]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [dh5L, hpSum, hpM.ev] at this; rw [this]; simp only [d25, d46, d48, d49, d58] <;> first | omega | ring
  · have := g 1 (by omega); simp [dh5L, hpSum, hpM.ev] at this; rw [this]; simp only [d25, d46, d48, d49, d58] <;> first | omega | ring
  · have := g 2 (by omega); simp [dh5L, hpSum, hpM.ev] at this; rw [this]; simp only [d25, d46, d48, d49, d58] <;> first | omega | ring


theorem twS_execW (c : Config) (hc : WordsBounded W c) {H L D1b ISb LNb NTb : ℕ}
    (d28 : c.nreg 8228 = H) (d34 : c.nreg 8234 = L) (d54 : c.nreg 8254 = D1b) (d55 : c.nreg 8255 = ISb) (d56 : c.nreg 8256 = LNb) (d57 : c.nreg 8257 = NTb)
    (hW : ISb + 1 ≤ W ∧ LNb + 1 ≤ W ∧ NTb + 1 ≤ W ∧ D1b + 1 ≤ W ∧ H + 1 ≤ W ∧ L + 1 ≤ W) :
    ∃ c', Exec P W twS c c' (hpCost twSL) ∧
      c'.nreg 8273 = ISb ∧
      c'.nreg 8274 = LNb ∧
      c'.nreg 8275 = NTb ∧
      c'.nreg 8276 = D1b ∧
      c'.nreg 8277 = H ∧
      c'.nreg 8278 = L ∧
      (∀ r, (r < 8273 ∨ 8279 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8273 7370 twSL :=
    hpShape_ok twSL_shape (by omega) (by omega) (by simp [twSL]) (by omega) (by simp [twSL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) twSL 8273 hok c hc (fun e he => by
    simp only [twSL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, d28, d34, d54, d55, d56, d57] <;> omega)
  have g : ∀ j < 6, c'.nreg (8273 + j) =
      hpSum c.nreg (twSL.getD j ([], 0)).1 - (twSL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [twSL]; omega)
  refine ⟨c', e, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [twSL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [twSL, hpSum, hpM.ev] at this; rw [this]; simp only [d28, d34, d54, d55, d56, d57] <;> first | omega | ring
  · have := g 1 (by omega); simp [twSL, hpSum, hpM.ev] at this; rw [this]; simp only [d28, d34, d54, d55, d56, d57] <;> first | omega | ring
  · have := g 2 (by omega); simp [twSL, hpSum, hpM.ev] at this; rw [this]; simp only [d28, d34, d54, d55, d56, d57] <;> first | omega | ring
  · have := g 3 (by omega); simp [twSL, hpSum, hpM.ev] at this; rw [this]; simp only [d28, d34, d54, d55, d56, d57] <;> first | omega | ring
  · have := g 4 (by omega); simp [twSL, hpSum, hpM.ev] at this; rw [this]; simp only [d28, d34, d54, d55, d56, d57] <;> first | omega | ring
  · have := g 5 (by omega); simp [twSL, hpSum, hpM.ev] at this; rw [this]; simp only [d28, d34, d54, d55, d56, d57] <;> first | omega | ring


theorem twW_execW (c : Config) (hc : WordsBounded W c) {nD bt : ℕ}
    (d25 : c.nreg 8225 = nD) (d49 : c.nreg 8249 = bt)
    (hW : nD + 1 ≤ W ∧ bt + 1 ≤ W ∧ bt + nD + 1 ≤ W) :
    ∃ c', Exec P W twW c c' (hpCost twWL) ∧
      c'.nreg 8200 = nD ∧
      c'.nreg 8201 = bt ∧
      c'.nreg 8202 = bt + nD ∧
      (∀ r, (r < 8200 ∨ 8203 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8200 7370 twWL :=
    hpShape_ok twWL_shape (by omega) (by omega) (by simp [twWL]) (by omega) (by simp [twWL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) twWL 8200 hok c hc (fun e he => by
    simp only [twWL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, d25, d49] <;> omega)
  have g : ∀ j < 3, c'.nreg (8200 + j) =
      hpSum c.nreg (twWL.getD j ([], 0)).1 - (twWL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [twWL]; omega)
  refine ⟨c', e, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [twWL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [twWL, hpSum, hpM.ev] at this; rw [this]; simp only [d25, d49] <;> first | omega | ring
  · have := g 1 (by omega); simp [twWL, hpSum, hpM.ev] at this; rw [this]; simp only [d25, d49] <;> first | omega | ring
  · have := g 2 (by omega); simp [twWL, hpSum, hpM.ev] at this; rw [this]; simp only [d25, d49] <;> first | omega | ring


theorem kpS_execW (c : Config) (hc : WordsBounded W c) {k t nD Hc B n len btp : ℕ}
    (d23 : c.nreg 8223 = k) (d24 : c.nreg 8224 = t) (d25 : c.nreg 8225 = nD) (d45 : c.nreg 8245 = Hc) (d47 : c.nreg 8247 = B) (d50 : c.nreg 8250 = n) (d51 : c.nreg 8251 = len) (d59 : c.nreg 8259 = btp)
    (hW : B + 1 ≤ W ∧ nD + 1 ≤ W ∧ n + 1 ≤ W ∧ k + 1 ≤ W ∧ t + 1 ≤ W ∧ Hc + 1 ≤ W ∧ btp + 1 ≤ W ∧ len + 1 ≤ W) :
    ∃ c', Exec P W kpS c c' (hpCost kpSL) ∧
      c'.nreg 7300 = B ∧
      c'.nreg 7301 = nD ∧
      c'.nreg 7302 = n ∧
      c'.nreg 7303 = k ∧
      c'.nreg 7304 = t ∧
      c'.nreg 7305 = Hc ∧
      c'.nreg 7306 = btp ∧
      c'.nreg 7307 = len ∧
      (∀ r, (r < 7300 ∨ 7308 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 7300 7370 kpSL :=
    hpShape_ok kpSL_shape (by omega) (by omega) (by simp [kpSL]) (by omega) (by simp [kpSL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) kpSL 7300 hok c hc (fun e he => by
    simp only [kpSL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, d23, d24, d25, d45, d47, d50, d51, d59] <;> omega)
  have g : ∀ j < 8, c'.nreg (7300 + j) =
      hpSum c.nreg (kpSL.getD j ([], 0)).1 - (kpSL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [kpSL]; omega)
  refine ⟨c', e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [kpSL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [kpSL, hpSum, hpM.ev] at this; rw [this]; simp only [d23, d24, d25, d45, d47, d50, d51, d59] <;> first | omega | ring
  · have := g 1 (by omega); simp [kpSL, hpSum, hpM.ev] at this; rw [this]; simp only [d23, d24, d25, d45, d47, d50, d51, d59] <;> first | omega | ring
  · have := g 2 (by omega); simp [kpSL, hpSum, hpM.ev] at this; rw [this]; simp only [d23, d24, d25, d45, d47, d50, d51, d59] <;> first | omega | ring
  · have := g 3 (by omega); simp [kpSL, hpSum, hpM.ev] at this; rw [this]; simp only [d23, d24, d25, d45, d47, d50, d51, d59] <;> first | omega | ring
  · have := g 4 (by omega); simp [kpSL, hpSum, hpM.ev] at this; rw [this]; simp only [d23, d24, d25, d45, d47, d50, d51, d59] <;> first | omega | ring
  · have := g 5 (by omega); simp [kpSL, hpSum, hpM.ev] at this; rw [this]; simp only [d23, d24, d25, d45, d47, d50, d51, d59] <;> first | omega | ring
  · have := g 6 (by omega); simp [kpSL, hpSum, hpM.ev] at this; rw [this]; simp only [d23, d24, d25, d45, d47, d50, d51, d59] <;> first | omega | ring
  · have := g 7 (by omega); simp [kpSL, hpSum, hpM.ev] at this; rw [this]; simp only [d23, d24, d25, d45, d47, d50, d51, d59] <;> first | omega | ring


theorem fnA_execW (c : Config) (hc : WordsBounded W c) {t N1 SL TI Lg len nk btp ao : ℕ}
    (d24 : c.nreg 8224 = t) (d29 : c.nreg 8229 = N1) (d30 : c.nreg 8230 = SL) (d31 : c.nreg 8231 = TI) (d32 : c.nreg 8232 = Lg) (d51 : c.nreg 8251 = len) (d53 : c.nreg 8253 = nk) (d59 : c.nreg 8259 = btp) (d61 : c.nreg 8261 = ao)
    (hW : t + 1 ≤ W ∧ nk + 1 ≤ W ∧ ao + 1 ≤ W ∧ N1 + 1 ≤ W ∧ SL + 1 ≤ W ∧ TI + 1 ≤ W ∧ nk + 1 ≤ W ∧ btp + 1 ≤ W ∧ len + 1 ≤ W ∧ Lg + 1 ≤ W) :
    ∃ c', Exec P W fnA c c' (hpCost fnAL) ∧
      c'.nreg 8010 = t ∧
      c'.nreg 8011 = nk ∧
      c'.nreg 8012 = ao ∧
      c'.nreg 8013 = N1 ∧
      c'.nreg 8014 = SL ∧
      c'.nreg 8015 = TI ∧
      c'.nreg 8016 = nk ∧
      c'.nreg 8017 = btp ∧
      c'.nreg 8018 = len ∧
      c'.nreg 8019 = Lg ∧
      (∀ r, (r < 8010 ∨ 8020 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8010 7370 fnAL :=
    hpShape_ok fnAL_shape (by omega) (by omega) (by simp [fnAL]) (by omega) (by simp [fnAL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) fnAL 8010 hok c hc (fun e he => by
    simp only [fnAL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, d24, d29, d30, d31, d32, d51, d53, d59, d61] <;> omega)
  have g : ∀ j < 10, c'.nreg (8010 + j) =
      hpSum c.nreg (fnAL.getD j ([], 0)).1 - (fnAL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [fnAL]; omega)
  refine ⟨c', e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [fnAL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [fnAL, hpSum, hpM.ev] at this; rw [this]; simp only [d24, d29, d30, d31, d32, d51, d53, d59, d61] <;> first | omega | ring
  · have := g 1 (by omega); simp [fnAL, hpSum, hpM.ev] at this; rw [this]; simp only [d24, d29, d30, d31, d32, d51, d53, d59, d61] <;> first | omega | ring
  · have := g 2 (by omega); simp [fnAL, hpSum, hpM.ev] at this; rw [this]; simp only [d24, d29, d30, d31, d32, d51, d53, d59, d61] <;> first | omega | ring
  · have := g 3 (by omega); simp [fnAL, hpSum, hpM.ev] at this; rw [this]; simp only [d24, d29, d30, d31, d32, d51, d53, d59, d61] <;> first | omega | ring
  · have := g 4 (by omega); simp [fnAL, hpSum, hpM.ev] at this; rw [this]; simp only [d24, d29, d30, d31, d32, d51, d53, d59, d61] <;> first | omega | ring
  · have := g 5 (by omega); simp [fnAL, hpSum, hpM.ev] at this; rw [this]; simp only [d24, d29, d30, d31, d32, d51, d53, d59, d61] <;> first | omega | ring
  · have := g 6 (by omega); simp [fnAL, hpSum, hpM.ev] at this; rw [this]; simp only [d24, d29, d30, d31, d32, d51, d53, d59, d61] <;> first | omega | ring
  · have := g 7 (by omega); simp [fnAL, hpSum, hpM.ev] at this; rw [this]; simp only [d24, d29, d30, d31, d32, d51, d53, d59, d61] <;> first | omega | ring
  · have := g 8 (by omega); simp [fnAL, hpSum, hpM.ev] at this; rw [this]; simp only [d24, d29, d30, d31, d32, d51, d53, d59, d61] <;> first | omega | ring
  · have := g 9 (by omega); simp [fnAL, hpSum, hpM.ev] at this; rw [this]; simp only [d24, d29, d30, d31, d32, d51, d53, d59, d61] <;> first | omega | ring


theorem fnB_execW (c : Config) (hc : WordsBounded W c) {bt Z2 : ℕ}
    (d49 : c.nreg 8249 = bt) (d52 : c.nreg 8252 = Z2)
    (hW : bt + 1 ≤ W ∧ Z2 + 1 ≤ W) :
    ∃ c', Exec P W fnB c c' (hpCost fnBL) ∧
      c'.nreg 8033 = bt ∧
      c'.nreg 8034 = Z2 ∧
      (∀ r, (r < 8033 ∨ 8035 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8033 7370 fnBL :=
    hpShape_ok fnBL_shape (by omega) (by omega) (by simp [fnBL]) (by omega) (by simp [fnBL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) fnBL 8033 hok c hc (fun e he => by
    simp only [fnBL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, d49, d52] <;> omega)
  have g : ∀ j < 2, c'.nreg (8033 + j) =
      hpSum c.nreg (fnBL.getD j ([], 0)).1 - (fnBL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [fnBL]; omega)
  refine ⟨c', e, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [fnBL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [fnBL, hpSum, hpM.ev] at this; rw [this]; simp only [d49, d52] <;> first | omega | ring
  · have := g 1 (by omega); simp [fnBL, hpSum, hpM.ev] at this; rw [this]; simp only [d49, d52] <;> first | omega | ring


set_option maxHeartbeats 4000000 in
/-- **Stage D1b: `Hc`, `B`, `β`, `β'` and the addresses.** -/
theorem msD1b_execW (c : Config) (hc : WordsBounded W c)
    {w cV cF k t nD IM A1 H N1 SL TI Lg : ℕ} (hA : DRegA c w cV cF k t nD IM A1 H N1 SL TI Lg)
    (hW : 8 * Klein.kleinWN (dB w nD k t) (4 * nD + 1) (MsEnc.msHI w cV cF k) + 300 * nD +
      4 * k + 8 * t + 500 ≤ W ∧ IM + 8 * nD + 500 ≤ W ∧ A1 + 21 * nD + 500 ≤ W) :
    ∃ e u, Exec P W msD1b c e u ∧ u ≤ 3 + hpCost dh4L + hpCost dh5L ∧
      DReg e w cV cF k t nD IM A1 H N1 SL TI Lg ∧
      (∀ r, (r < 8220 ∨ 8262 ≤ r) → r ≠ 7370 → r ≠ 7371 → e.nreg r = c.nreg r) ∧
      e.nmem = c.nmem ∧ e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  have eH := msHI_dec w cV cF k
  have eKW : Klein.kleinWN (dB w nD k t) (4 * nD + 1) (MsEnc.msHI w cV cF k) =
      2 * (dB w nD k t + 16 * (4 * nD + 1 + 1)) + 1 +
      (2 * MsEnc.msHI w cV cF k + 1) * (2 * MsEnc.msHI w cV cF k + 1) +
      (2 * MsEnc.msHI w cV cF k + 1) := rfl
  have eB : dB w nD k t = w + 40 * nD + 2 * k + 2 * t + t * t + 20 := rfl
  have hMo := Nat.le_mul_self (2 * MsEnc.msHI w cV cF k + 1)
  have b1 : cF * (MsEnc.msH0 w cV k + MsEnc.msL w cV + 2 * (cV * w)) ≤ MsEnc.msHI w cV cF k := by
    rw [eH]; omega
  have b2 : MsEnc.msH0 w cV k + MsEnc.msL w cV + MsEnc.msK w cV + cV * w + w ≤
      MsEnc.msHI w cV cF k := by rw [eH]; omega
  have b3 : t * t + w + nD + k + t ≤ dB w nD k t := by rw [eB]; omega
  obtain ⟨c₁, t₁, x₁, ht₁, m42, mR1, mm1, mr1, mrm1, mo1⟩ :=
    mulR_exec (P := P) c hc 8242 8222 8241 (by rw [hA.d22, hA.d41]; omega)
  rw [hA.d22, hA.d41] at m42
  obtain ⟨c₂, t₂, x₂, ht₂, m43, mR2, mm2, mr2, mrm2, mo2⟩ :=
    mulR_exec (P := P) c₁ x₁.wb_right 8243 8224 8224
      (by rw [mR1 _ (by omega), hA.d24]; omega)
  rw [mR1 _ (by omega), hA.d24] at m43
  have hA2 := hA.congr (e' := c₂) (fun r h1 h2 => by rw [mR2 r (by omega), mR1 r (by omega)])
  obtain ⟨c₃, x₃, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, hR3, hm3,
    hr3, hrm3, ho3⟩ :=
    dh4_execW (P := P) c₂ x₂.wb_right (w := w) (k := k) (t := t) (nD := nD) (IM := IM) (A1 := A1)
      (P1 := cV * w) (L := MsEnc.msL w cV) (K := MsEnc.msK w cV) (H0 := MsEnc.msH0 w cV k)
      (P4 := cF * (MsEnc.msH0 w cV k + MsEnc.msL w cV + 2 * (cV * w))) (T2 := t * t) hA2.d20 hA2.d23 hA2.d24 hA2.d25 hA2.d26 hA2.d27 hA2.d33
      hA2.d34 hA2.d36 hA2.d40 (by rw [mR2 _ (by omega)]; exact m42) m43 (by omega)
  have e45 : c₃.nreg 8245 = MsEnc.msHI w cV cF k := by rw [h45, eH]
  have e46 : c₃.nreg 8246 = 2 * MsEnc.msHI w cV cF k + 1 := by rw [h46, eH]; ring
  obtain ⟨c₄, t₄, x₄, ht₄, m58, mR4, mm4, mr4, mrm4, mo4⟩ :=
    mulR_exec (P := P) c₃ x₃.wb_right 8258 8246 8246 (by rw [e46]; omega)
  rw [e46] at m58
  obtain ⟨c₅, x₅, h59, h60, h61, hR5, hm5, hr5, hrm5, ho5⟩ :=
    dh5_execW (P := P) c₄ x₄.wb_right (nD := nD) (Mo := 2 * MsEnc.msHI w cV cF k + 1)
      (Wb := w + 104 * nD + 2 * k + 2 * t + t * t + 52)
      (bt := w + 104 * nD + 2 * k + 2 * t + t * t + 53)
      (Mo2 := (2 * MsEnc.msHI w cV cF k + 1) * (2 * MsEnc.msHI w cV cF k + 1))
      (by rw [mR4 _ (by omega), hR3 _ (by omega) (by omega) (by omega), mR2 _ (by omega),
        mR1 _ (by omega)]; exact hA.d25)
      (by rw [mR4 _ (by omega)]; exact e46) (by rw [mR4 _ (by omega)]; exact h48)
      (by rw [mR4 _ (by omega)]; exact h49) m58 (by omega)
  have q5 : ∀ r, 8244 ≤ r → r < 8258 → c₅.nreg r = c₃.nreg r := fun r h1 h2 => by
    rw [hR5 r (by omega) (by omega) (by omega), mR4 r (by omega)]
  have hA5 := hA2.congr (e' := c₅) (fun r h1 h2 => by
    rw [hR5 r (by omega) (by omega) (by omega), mR4 r (by omega),
      hR3 r (by omega) (by omega) (by omega)])
  refine ⟨c₅, _, .seq x₁ (.seq x₂ (.seq x₃ (.seq x₄ x₅))), by omega,
    ⟨hA5, by rw [q5 8245 (by omega) (by omega)]; exact e45,
      by rw [q5 8246 (by omega) (by omega)]; exact e46, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩, fun r hr h1 h2 => ?_, by rw [hm5, mm4, hm3, mm2, mm1],
    by rw [hr5, mr4, hr3, mr2, mr1], by rw [hrm5, mrm4, hrm3, mrm2, mrm1],
    by rw [ho5, mo4, ho3, mo2, mo1]⟩
  · rw [q5 8247 (by omega) (by omega), h47, eB]; try ring
  · rw [q5 8248 (by omega) (by omega), h48, eB]; try ring
  · rw [q5 8249 (by omega) (by omega), h49, eB]; try ring
  · rw [q5 8250 (by omega) (by omega), h50]
  · rw [q5 8251 (by omega) (by omega), h51]; unfold dLen; try ring
  · rw [q5 8252 (by omega) (by omega), h52]
  · rw [q5 8253 (by omega) (by omega), h53]; try ring
  · rw [q5 8254 (by omega) (by omega), h54]
  · rw [q5 8255 (by omega) (by omega), h55]
  · rw [q5 8256 (by omega) (by omega), h56]
  · rw [q5 8257 (by omega) (by omega), h57]
  · rw [h59, eKW, eB]; try ring
  · rw [h60, eB]; try ring
  · rw [h61, eB]; try ring
  · rw [hR5 r (by omega) h1 h2, mR4 r (by omega), hR3 r (by omega) h1 h2, mR2 r (by omega),
      mR1 r (by omega)]


end MsStD

end MsEnc

end BKMNW

end PlanarFlow
