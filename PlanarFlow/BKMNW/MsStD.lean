module

public import PlanarFlow.BKMNW.MsStC4

/-!
# The MSSP encoder, stage D, part 1: the constants of Klein's start in registers

The values of stage D are computed in the register block `8220 … 8261` (each `hpProg` reads the
block below its targets): the copies `dcA`, `dcB` (`w`, `cV`, `cF`, `k`, `t`, `nD`, `IM`, `A1`, `H`,
`N₁`, `SL`, `TI`, `Lg`), the products `mulR` and the linear forms `dh1 … dh5`: the trip constants
`msL`, `msTh`, `msH0`, **`Hc = msHI w cV cF k`** (`= kleinHI`, `MsKB.kleinHI_eq`), `Mo = 2 Hc + 1`,
**`B = dB w nD k t`**, `Wb = B + 16 (n + 1)`, `β = Wb + 1`, `n = 4 nD + 1`, the length `len` of
Klein's input, **`β' = kleinWN B n Hc + 1`**, and the set-ups `twS`, `twW` (the trip weights),
`cpS` (the copy of the image), `kpS` (the primaries of `kPrm`), `fnA`, `fnB` (the registers of the
call). **`msD1_exec`**.
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

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

variable {P : Input} {W : ℕ}

/-- The register bound `B` of Klein's natural run. -/
def dB (w nD k t : ℕ) : ℕ := w + 40 * nD + 2 * k + 2 * t + t * t + 20

/-- The length of Klein's input. -/
def dLen (nD k t : ℕ) : ℕ := 37 * nD + k + 2 * t + 11

/-- One product. -/
def mulR (a b d : ℕ) : Stmt := block [.mulN a b d]

theorem mulR_exec (c : Config) (hc : WordsBounded W c) (a b d : ℕ)
    (hw : c.nreg b * c.nreg d ≤ W) :
    ∃ c' u, Exec P W (mulR a b d) c c' u ∧ u = 1 ∧ c'.nreg a = c.nreg b * c.nreg d ∧
      (∀ r, r ≠ a → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mulR
  exec_block
  all_goals try exact hw
  refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp [hr]

def dcA : Stmt := block [.copyN 8220 7342, .copyN 8221 8298, .copyN 8222 8299, .copyN 8223 8156,
  .copyN 8224 8157, .copyN 8225 8297, .copyN 8226 8282]

def dcB : Stmt := block [.copyN 8227 8291, .copyN 8228 7335, .copyN 8229 7328, .copyN 8230 8294,
  .copyN 8231 8295, .copyN 8232 8296]

theorem dcA_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W dcA c c' t ∧ t = 7 ∧ c'.nreg 8220 = c.nreg 7342 ∧
      c'.nreg 8221 = c.nreg 8298 ∧ c'.nreg 8222 = c.nreg 8299 ∧ c'.nreg 8223 = c.nreg 8156 ∧
      c'.nreg 8224 = c.nreg 8157 ∧ c'.nreg 8225 = c.nreg 8297 ∧ c'.nreg 8226 = c.nreg 8282 ∧
      (∀ r, (r < 8220 ∨ 8227 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dcA
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | rfl
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

theorem dcB_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W dcB c c' t ∧ t = 6 ∧ c'.nreg 8227 = c.nreg 8291 ∧
      c'.nreg 8228 = c.nreg 7335 ∧ c'.nreg 8229 = c.nreg 7328 ∧ c'.nreg 8230 = c.nreg 8294 ∧
      c'.nreg 8231 = c.nreg 8295 ∧ c'.nreg 8232 = c.nreg 8296 ∧
      (∀ r, (r < 8227 ∨ 8233 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dcB
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | rfl
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

def dh1L : List (List (ℕ × hpM) × ℕ) :=
  [([(4, hpM.v 8233), (1, hpM.v 8220), (1, hpM.one)], 0),
    ([(2, hpM.v 8233), (1, hpM.v 8220), (1, hpM.one)], 0),
    ([(6, hpM.v 8233), (2, hpM.v 8220), (1, hpM.one)], 0)]

theorem dh1L_shape : hpShape 8220 8234 6 1 dh1L = true := by decide

def dh1 : Stmt := hpProg 8234 7370 dh1L

theorem dh1_exec (c : Config) (hc : WordsBounded W c) {w P1 : ℕ}
    (d20 : c.nreg 8220 = w) (d33 : c.nreg 8233 = P1)
    (hW : 4 * P1 + w + 1 + 2 * P1 + w + 1 + 6 * P1 + 2 * w + 1 + 6 ≤ W) :
    ∃ c', Exec P W dh1 c c' (hpCost dh1L) ∧
      c'.nreg 8234 = 4 * P1 + w + 1 ∧
      c'.nreg 8235 = 2 * P1 + w + 1 ∧
      c'.nreg 8236 = 6 * P1 + 2 * w + 1 ∧
      (∀ r, (r < 8234 ∨ 8237 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8234 7370 dh1L :=
    hpShape_ok dh1L_shape (by omega) (by omega) (by simp [dh1L]) (by omega) (by simp [dh1L])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) dh1L 8234 hok c hc (fun e he => by
    simp only [dh1L, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, d20, d33] <;> omega)
  have g : ∀ j < 3, c'.nreg (8234 + j) =
      hpSum c.nreg (dh1L.getD j ([], 0)).1 - (dh1L.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [dh1L]; omega)
  refine ⟨c', e, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [dh1L]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [dh1L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d33] <;> first | omega | ring
  · have := g 1 (by omega); simp [dh1L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d33] <;> first | omega | ring
  · have := g 2 (by omega); simp [dh1L, hpSum, hpM.ev] at this; rw [this]; simp only [d20, d33] <;> first | omega | ring

def dh2L : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8237), (1, hpM.v 8236)], 0)]

theorem dh2L_shape : hpShape 8220 8238 1 1 dh2L = true := by decide

def dh2 : Stmt := hpProg 8238 7370 dh2L

theorem dh2_exec (c : Config) (hc : WordsBounded W c) {K Q1 : ℕ}
    (d36 : c.nreg 8236 = K) (d37 : c.nreg 8237 = Q1)
    (hW : Q1 + K + 1 ≤ W) :
    ∃ c', Exec P W dh2 c c' (hpCost dh2L) ∧
      c'.nreg 8238 = Q1 + K ∧
      (∀ r, (r < 8238 ∨ 8239 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8238 7370 dh2L :=
    hpShape_ok dh2L_shape (by omega) (by omega) (by simp [dh2L]) (by omega) (by simp [dh2L])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) dh2L 8238 hok c hc (fun e he => by
    simp only [dh2L, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, d36, d37] <;> omega)
  have g : ∀ j < 1, c'.nreg (8238 + j) =
      hpSum c.nreg (dh2L.getD j ([], 0)).1 - (dh2L.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [dh2L]; omega)
  refine ⟨c', e, ?_,
    fun x h1 h2 h3 => f x (by simp [dh2L]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [dh2L, hpSum, hpM.ev] at this; rw [this]; simp only [d36, d37] <;> first | omega | ring

def dh3L : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8235), (1, hpM.v 8239), (1, hpM.v 8238)], 0),
    ([(1, hpM.v 8235), (1, hpM.v 8239), (1, hpM.v 8238), (1, hpM.v 8234), (2, hpM.v 8233)], 0)]

theorem dh3L_shape : hpShape 8220 8240 2 1 dh3L = true := by decide

def dh3 : Stmt := hpProg 8240 7370 dh3L

theorem dh3_exec (c : Config) (hc : WordsBounded W c) {P1 L Th P2 Q2 : ℕ}
    (d33 : c.nreg 8233 = P1) (d34 : c.nreg 8234 = L) (d35 : c.nreg 8235 = Th) (d38 : c.nreg 8238 = P2) (d39 : c.nreg 8239 = Q2)
    (hW : Th + Q2 + P2 + Th + Q2 + P2 + L + 2 * P1 + 2 ≤ W) :
    ∃ c', Exec P W dh3 c c' (hpCost dh3L) ∧
      c'.nreg 8240 = Th + Q2 + P2 ∧
      c'.nreg 8241 = Th + Q2 + P2 + L + 2 * P1 ∧
      (∀ r, (r < 8240 ∨ 8242 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8240 7370 dh3L :=
    hpShape_ok dh3L_shape (by omega) (by omega) (by simp [dh3L]) (by omega) (by simp [dh3L])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) dh3L 8240 hok c hc (fun e he => by
    simp only [dh3L, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, d33, d34, d35, d38, d39] <;> omega)
  have g : ∀ j < 2, c'.nreg (8240 + j) =
      hpSum c.nreg (dh3L.getD j ([], 0)).1 - (dh3L.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [dh3L]; omega)
  refine ⟨c', e, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [dh3L]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [dh3L, hpSum, hpM.ev] at this; rw [this]; simp only [d33, d34, d35, d38, d39] <;> first | omega | ring
  · have := g 1 (by omega); simp [dh3L, hpSum, hpM.ev] at this; rw [this]; simp only [d33, d34, d35, d38, d39] <;> first | omega | ring

def dh4L : List (List (ℕ × hpM) × ℕ) :=
  [([(2, hpM.v 8233), (2, hpM.v 8242)], 0),
    ([(30, hpM.v 8240), (38, hpM.v 8234), (38, hpM.v 8220), (120, hpM.v 8233), (60, hpM.v 8242), (12, hpM.v 8236)], 0),
    ([(60, hpM.v 8240), (76, hpM.v 8234), (76, hpM.v 8220), (240, hpM.v 8233), (120, hpM.v 8242), (24, hpM.v 8236), (1, hpM.one)], 0),
    ([(1, hpM.v 8220), (40, hpM.v 8225), (2, hpM.v 8223), (2, hpM.v 8224), (1, hpM.v 8243), (20, hpM.one)], 0),
    ([(1, hpM.v 8220), (104, hpM.v 8225), (2, hpM.v 8223), (2, hpM.v 8224), (1, hpM.v 8243), (52, hpM.one)], 0),
    ([(1, hpM.v 8220), (104, hpM.v 8225), (2, hpM.v 8223), (2, hpM.v 8224), (1, hpM.v 8243), (53, hpM.one)], 0),
    ([(4, hpM.v 8225), (1, hpM.one)], 0),
    ([(37, hpM.v 8225), (1, hpM.v 8223), (2, hpM.v 8224), (11, hpM.one)], 0),
    ([(3, hpM.v 8225), (3, hpM.one)], 0),
    ([(4, hpM.v 8225), (1, hpM.v 8223), (1, hpM.one)], 0),
    ([(1, hpM.v 8227), (21, hpM.v 8225), (6, hpM.one)], 0),
    ([(1, hpM.v 8226), (6, hpM.v 8225)], 0),
    ([(1, hpM.v 8226), (7, hpM.v 8225)], 0),
    ([(1, hpM.v 8226), (4, hpM.v 8225)], 0)]

theorem dh4L_shape : hpShape 8220 8244 240 1 dh4L = true := by decide

def dh4 : Stmt := hpProg 8244 7370 dh4L

theorem dh4_exec (c : Config) (hc : WordsBounded W c) {w k t nD IM A1 P1 L K H0 P4 T2 : ℕ}
    (d20 : c.nreg 8220 = w) (d23 : c.nreg 8223 = k) (d24 : c.nreg 8224 = t) (d25 : c.nreg 8225 = nD) (d26 : c.nreg 8226 = IM) (d27 : c.nreg 8227 = A1) (d33 : c.nreg 8233 = P1) (d34 : c.nreg 8234 = L) (d36 : c.nreg 8236 = K) (d40 : c.nreg 8240 = H0) (d42 : c.nreg 8242 = P4) (d43 : c.nreg 8243 = T2)
    (hW : 2 * P1 + 2 * P4 + 30 * H0 + 38 * L + 38 * w + 120 * P1 + 60 * P4 + 12 * K + 60 * H0 + 76 * L + 76 * w + 240 * P1 + 120 * P4 + 24 * K + 1 + w + 40 * nD + 2 * k + 2 * t + T2 + 20 + w + 104 * nD + 2 * k + 2 * t + T2 + 52 + w + 104 * nD + 2 * k + 2 * t + T2 + 53 + 4 * nD + 1 + 37 * nD + k + 2 * t + 11 + 3 * nD + 3 + 4 * nD + k + 1 + A1 + 21 * nD + 6 + IM + 6 * nD + IM + 7 * nD + IM + 4 * nD + 240 ≤ W) :
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

def dh5L : List (List (ℕ × hpM) × ℕ) :=
  [([(2, hpM.v 8248), (1, hpM.v 8258), (1, hpM.v 8246), (2, hpM.one)], 0),
    ([(1, hpM.v 8249), (3, hpM.v 8225)], 0),
    ([(1, hpM.v 8249), (3, hpM.v 8225), (3, hpM.one)], 0)]

theorem dh5L_shape : hpShape 8220 8259 3 1 dh5L = true := by decide

def dh5 : Stmt := hpProg 8259 7370 dh5L

theorem dh5_exec (c : Config) (hc : WordsBounded W c) {nD Mo Wb bt Mo2 : ℕ}
    (d25 : c.nreg 8225 = nD) (d46 : c.nreg 8246 = Mo) (d48 : c.nreg 8248 = Wb) (d49 : c.nreg 8249 = bt) (d58 : c.nreg 8258 = Mo2)
    (hW : 2 * Wb + Mo2 + Mo + 2 + bt + 3 * nD + bt + 3 * nD + 3 + 3 ≤ W) :
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

def twSL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8255)], 0),
    ([(1, hpM.v 8256)], 0),
    ([(1, hpM.v 8257)], 0),
    ([(1, hpM.v 8254)], 0),
    ([(1, hpM.v 8228)], 0),
    ([(1, hpM.v 8234)], 0)]

theorem twSL_shape : hpShape 8220 8262 1 1 twSL = true := by decide

def twS : Stmt := hpProg 8273 7370 twSL

theorem twS_exec (c : Config) (hc : WordsBounded W c) {H L D1b ISb LNb NTb : ℕ}
    (d28 : c.nreg 8228 = H) (d34 : c.nreg 8234 = L) (d54 : c.nreg 8254 = D1b) (d55 : c.nreg 8255 = ISb) (d56 : c.nreg 8256 = LNb) (d57 : c.nreg 8257 = NTb)
    (hW : ISb + LNb + NTb + D1b + H + L + 1 ≤ W) :
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

def twWL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8225)], 0),
    ([(1, hpM.v 8249)], 0),
    ([(1, hpM.v 8249), (1, hpM.v 8225)], 0)]

theorem twWL_shape : hpShape 8220 8262 1 1 twWL = true := by decide

def twW : Stmt := hpProg 8200 7370 twWL

theorem twW_exec (c : Config) (hc : WordsBounded W c) {nD bt : ℕ}
    (d25 : c.nreg 8225 = nD) (d49 : c.nreg 8249 = bt)
    (hW : nD + bt + bt + nD + 1 ≤ W) :
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

def cpSL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8251)], 0),
    ([(1, hpM.v 8226)], 0),
    ([(1, hpM.v 8259)], 0)]

theorem cpSL_shape : hpShape 8220 8262 1 1 cpSL = true := by decide

def cpS : Stmt := hpProg 4910 7370 cpSL

theorem cpS_exec (c : Config) (hc : WordsBounded W c) {IM len btp : ℕ}
    (d26 : c.nreg 8226 = IM) (d51 : c.nreg 8251 = len) (d59 : c.nreg 8259 = btp)
    (hW : len + IM + btp + 1 ≤ W) :
    ∃ c', Exec P W cpS c c' (hpCost cpSL) ∧
      c'.nreg 4910 = len ∧
      c'.nreg 4911 = IM ∧
      c'.nreg 4912 = btp ∧
      (∀ r, (r < 4910 ∨ 4913 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 4910 7370 cpSL :=
    hpShape_ok cpSL_shape (by omega) (by omega) (by simp [cpSL]) (by omega) (by simp [cpSL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) cpSL 4910 hok c hc (fun e he => by
    simp only [cpSL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, d26, d51, d59] <;> omega)
  have g : ∀ j < 3, c'.nreg (4910 + j) =
      hpSum c.nreg (cpSL.getD j ([], 0)).1 - (cpSL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [cpSL]; omega)
  refine ⟨c', e, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [cpSL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [cpSL, hpSum, hpM.ev] at this; rw [this]; simp only [d26, d51, d59] <;> first | omega | ring
  · have := g 1 (by omega); simp [cpSL, hpSum, hpM.ev] at this; rw [this]; simp only [d26, d51, d59] <;> first | omega | ring
  · have := g 2 (by omega); simp [cpSL, hpSum, hpM.ev] at this; rw [this]; simp only [d26, d51, d59] <;> first | omega | ring

def kpSL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8247)], 0),
    ([(1, hpM.v 8225)], 0),
    ([(1, hpM.v 8250)], 0),
    ([(1, hpM.v 8223)], 0),
    ([(1, hpM.v 8224)], 0),
    ([(1, hpM.v 8245)], 0),
    ([(1, hpM.v 8259)], 0),
    ([(1, hpM.v 8251)], 0)]

theorem kpSL_shape : hpShape 8220 8262 1 1 kpSL = true := by decide

def kpS : Stmt := hpProg 7300 7370 kpSL

theorem kpS_exec (c : Config) (hc : WordsBounded W c) {k t nD Hc B n len btp : ℕ}
    (d23 : c.nreg 8223 = k) (d24 : c.nreg 8224 = t) (d25 : c.nreg 8225 = nD) (d45 : c.nreg 8245 = Hc) (d47 : c.nreg 8247 = B) (d50 : c.nreg 8250 = n) (d51 : c.nreg 8251 = len) (d59 : c.nreg 8259 = btp)
    (hW : B + nD + n + k + t + Hc + btp + len + 1 ≤ W) :
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

def fnAL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8224)], 0),
    ([(1, hpM.v 8253)], 0),
    ([(1, hpM.v 8261)], 0),
    ([(1, hpM.v 8229)], 0),
    ([(1, hpM.v 8230)], 0),
    ([(1, hpM.v 8231)], 0),
    ([(1, hpM.v 8253)], 0),
    ([(1, hpM.v 8259)], 0),
    ([(1, hpM.v 8251)], 0),
    ([(1, hpM.v 8232)], 0)]

theorem fnAL_shape : hpShape 8220 8262 1 1 fnAL = true := by decide

def fnA : Stmt := hpProg 8010 7370 fnAL

theorem fnA_exec (c : Config) (hc : WordsBounded W c) {t N1 SL TI Lg len nk btp ao : ℕ}
    (d24 : c.nreg 8224 = t) (d29 : c.nreg 8229 = N1) (d30 : c.nreg 8230 = SL) (d31 : c.nreg 8231 = TI) (d32 : c.nreg 8232 = Lg) (d51 : c.nreg 8251 = len) (d53 : c.nreg 8253 = nk) (d59 : c.nreg 8259 = btp) (d61 : c.nreg 8261 = ao)
    (hW : t + nk + ao + N1 + SL + TI + nk + btp + len + Lg + 1 ≤ W) :
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

def fnBL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8249)], 0),
    ([(1, hpM.v 8252)], 0)]

theorem fnBL_shape : hpShape 8220 8262 1 1 fnBL = true := by decide

def fnB : Stmt := hpProg 8033 7370 fnBL

theorem fnB_exec (c : Config) (hc : WordsBounded W c) {bt Z2 : ℕ}
    (d49 : c.nreg 8249 = bt) (d52 : c.nreg 8252 = Z2)
    (hW : bt + Z2 + 1 ≤ W) :
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

/-! ### The constants as one run -/

/-- **Stage D1a.** -/
def msD1a : Stmt := .seq dcA (.seq dcB (.seq (mulR 8233 8221 8220) (.seq dh1
  (.seq (mulR 8237 8221 8236) (.seq dh2 (.seq (mulR 8239 8223 8238) dh3))))))

/-- **Stage D1b.** -/
def msD1b : Stmt := .seq (mulR 8242 8222 8241) (.seq (mulR 8243 8224 8224) (.seq dh4
  (.seq (mulR 8258 8246 8246) dh5)))

/-- **Stage D1.** -/
def msD1 : Stmt := .seq msD1a msD1b

lemma msH0_dec (w cV k : ℕ) : MsEnc.msH0 w cV k = MsEnc.msTh w cV +
    k * (cV * MsEnc.msK w cV + MsEnc.msK w cV) + (cV * MsEnc.msK w cV + MsEnc.msK w cV) := by
  unfold MsEnc.msH0; ring

lemma msHI_dec (w cV cF k : ℕ) : MsEnc.msHI w cV cF k = 30 * MsEnc.msH0 w cV k +
    38 * MsEnc.msL w cV + 38 * w + 120 * (cV * w) +
    60 * (cF * (MsEnc.msH0 w cV k + MsEnc.msL w cV + 2 * (cV * w))) + 12 * MsEnc.msK w cV := by
  unfold MsEnc.msHI MsEnc.msZ; ring

lemma msL_dec (w cV : ℕ) : MsEnc.msL w cV = 4 * (cV * w) + w + 1 := by unfold MsEnc.msL; ring
lemma msTh_dec (w cV : ℕ) : MsEnc.msTh w cV = 2 * (cV * w) + w + 1 := by unfold MsEnc.msTh; ring
lemma msK_dec (w cV : ℕ) : MsEnc.msK w cV = 6 * (cV * w) + 2 * w + 1 := by unfold MsEnc.msK; ring

/-- The register facts of stage D1a. -/
structure DRegA (e : Config) (w cV cF k t nD IM A1 H N1 SL TI Lg : ℕ) : Prop where
  d20 : e.nreg 8220 = w
  d21 : e.nreg 8221 = cV
  d22 : e.nreg 8222 = cF
  d23 : e.nreg 8223 = k
  d24 : e.nreg 8224 = t
  d25 : e.nreg 8225 = nD
  d26 : e.nreg 8226 = IM
  d27 : e.nreg 8227 = A1
  d28 : e.nreg 8228 = H
  d29 : e.nreg 8229 = N1
  d30 : e.nreg 8230 = SL
  d31 : e.nreg 8231 = TI
  d32 : e.nreg 8232 = Lg
  d33 : e.nreg 8233 = cV * w
  d34 : e.nreg 8234 = MsEnc.msL w cV
  d35 : e.nreg 8235 = MsEnc.msTh w cV
  d36 : e.nreg 8236 = MsEnc.msK w cV
  d40 : e.nreg 8240 = MsEnc.msH0 w cV k
  d41 : e.nreg 8241 = MsEnc.msH0 w cV k + MsEnc.msL w cV + 2 * (cV * w)

lemma DRegA.congr {e e' : Config} {w cV cF k t nD IM A1 H N1 SL TI Lg : ℕ}
    (h : DRegA e w cV cF k t nD IM A1 H N1 SL TI Lg)
    (hr : ∀ r, 8220 ≤ r → r < 8242 → e'.nreg r = e.nreg r) :
    DRegA e' w cV cF k t nD IM A1 H N1 SL TI Lg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hr _ (by omega) (by omega)]
  exacts [h.d20, h.d21, h.d22, h.d23, h.d24, h.d25, h.d26, h.d27, h.d28, h.d29, h.d30, h.d31,
    h.d32, h.d33, h.d34, h.d35, h.d36, h.d40, h.d41]

set_option maxHeartbeats 4000000 in
/-- **Stage D1a: the trip constants.** -/
theorem msD1a_exec (c : Config) (hc : WordsBounded W c)
    {w cV cF k t nD IM A1 H N1 SL TI Lg : ℕ}
    (r42 : c.nreg 7342 = w) (r98 : c.nreg 8298 = cV) (r99 : c.nreg 8299 = cF)
    (r56 : c.nreg 8156 = k) (r57 : c.nreg 8157 = t) (r97 : c.nreg 8297 = nD)
    (r82 : c.nreg 8282 = IM) (r91 : c.nreg 8291 = A1) (r35 : c.nreg 7335 = H)
    (r28 : c.nreg 7328 = N1) (r94 : c.nreg 8294 = SL) (r95 : c.nreg 8295 = TI)
    (r96 : c.nreg 8296 = Lg) (hW : 8 * MsEnc.msHI w cV cF k + 20 ≤ W) :
    ∃ e u, Exec P W msD1a c e u ∧ u ≤ 13 + 4 + hpCost dh1L + hpCost dh2L + hpCost dh3L ∧
      DRegA e w cV cF k t nD IM A1 H N1 SL TI Lg ∧
      (∀ r, (r < 8220 ∨ 8242 ≤ r) → r ≠ 7370 → r ≠ 7371 → e.nreg r = c.nreg r) ∧
      e.nmem = c.nmem ∧ e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  have eH := msHI_dec w cV cF k
  have e0 := msH0_dec w cV k
  have eL := msL_dec w cV
  have eT := msTh_dec w cV
  have eK := msK_dec w cV
  obtain ⟨c₁, t₁, x₁, ht₁, a20, a21, a22, a23, a24, a25, a26, aR, am, ar, arm, ao⟩ :=
    dcA_exec (P := P) c hc
  obtain ⟨c₂, t₂, x₂, ht₂, b27, b28, b29, b30, b31, b32, bR, bm, br, brm, bo⟩ :=
    dcB_exec (P := P) c₁ x₁.wb_right
  have g : ∀ r, 8220 ≤ r → r < 8227 → c₂.nreg r = c₁.nreg r := fun r h1 h2 => bR r (by omega)
  have s20 : c₂.nreg 8220 = w := by rw [g _ (by omega) (by omega), a20, r42]
  have s21 : c₂.nreg 8221 = cV := by rw [g _ (by omega) (by omega), a21, r98]
  have s22 : c₂.nreg 8222 = cF := by rw [g _ (by omega) (by omega), a22, r99]
  have s23 : c₂.nreg 8223 = k := by rw [g _ (by omega) (by omega), a23, r56]
  -- products and linear forms
  obtain ⟨c₃, t₃, x₃, ht₃, m33, mR3, mm3, mr3, mrm3, mo3⟩ :=
    mulR_exec (P := P) c₂ x₂.wb_right 8233 8221 8220 (by rw [s21, s20]; omega)
  rw [s21, s20] at m33
  obtain ⟨c₄, x₄, h34, h35, h36, hR4, hm4, hr4, hrm4, ho4⟩ :=
    dh1_exec (P := P) c₃ x₃.wb_right (w := w) (P1 := cV * w)
      (by rw [mR3 _ (by omega)]; exact s20) m33 (by omega)
  obtain ⟨c₅, t₅, x₅, ht₅, m37, mR5, mm5, mr5, mrm5, mo5⟩ :=
    mulR_exec (P := P) c₄ x₄.wb_right 8237 8221 8236
      (by rw [hR4 _ (by omega) (by omega) (by omega), mR3 _ (by omega), s21, h36,
        ← eK]; omega)
  rw [hR4 _ (by omega) (by omega) (by omega), mR3 _ (by omega), s21, h36, ← eK] at m37
  obtain ⟨c₆, x₆, h38, hR6, hm6, hr6, hrm6, ho6⟩ :=
    dh2_exec (P := P) c₅ x₅.wb_right (K := MsEnc.msK w cV) (Q1 := cV * MsEnc.msK w cV)
      (by rw [mR5 _ (by omega), h36, ← eK]) m37 (by omega)
  obtain ⟨c₇, t₇, x₇, ht₇, m39, mR7, mm7, mr7, mrm7, mo7⟩ :=
    mulR_exec (P := P) c₆ x₆.wb_right 8239 8223 8238
      (by rw [hR6 _ (by omega) (by omega) (by omega), mR5 _ (by omega),
        hR4 _ (by omega) (by omega) (by omega), mR3 _ (by omega), s23, h38]; omega)
  rw [hR6 _ (by omega) (by omega) (by omega), mR5 _ (by omega),
    hR4 _ (by omega) (by omega) (by omega), mR3 _ (by omega), s23, h38] at m39
  have q7 : ∀ r, 8233 ≤ r → r < 8237 → c₇.nreg r = c₄.nreg r := fun r h1 h2 => by
    rw [mR7 r (by omega), hR6 r (by omega) (by omega) (by omega), mR5 r (by omega)]
  obtain ⟨c₈, x₈, h40, h41, hR8, hm8, hr8, hrm8, ho8⟩ :=
    dh3_exec (P := P) c₇ x₇.wb_right (P1 := cV * w) (L := 4 * (cV * w) + w + 1)
      (Th := 2 * (cV * w) + w + 1) (P2 := cV * MsEnc.msK w cV + MsEnc.msK w cV)
      (Q2 := k * (cV * MsEnc.msK w cV + MsEnc.msK w cV))
      (by rw [q7 8233 (by omega) (by omega), hR4 8233 (by omega) (by omega) (by omega)]; exact m33)
      (by rw [q7 8234 (by omega) (by omega)]; exact h34)
      (by rw [q7 8235 (by omega) (by omega)]; exact h35)
      (by rw [mR7 8238 (by omega)]; exact h38) m39 (by omega)
  have k8 : ∀ r, (r < 8220 ∨ 8242 ≤ r) → r ≠ 7370 → r ≠ 7371 → c₈.nreg r = c₂.nreg r :=
    fun r hr h1 h2 => by
    rw [hR8 r (by omega) (by omega) (by omega), mR7 r (by omega),
      hR6 r (by omega) (by omega) (by omega), mR5 r (by omega),
      hR4 r (by omega) (by omega) (by omega), mR3 r (by omega)]
  have k8' : ∀ r, 8220 ≤ r → r < 8233 → c₈.nreg r = c₂.nreg r := fun r h1 h2 => by
    rw [hR8 r (by omega) (by omega) (by omega), mR7 r (by omega),
      hR6 r (by omega) (by omega) (by omega), mR5 r (by omega),
      hR4 r (by omega) (by omega) (by omega), mR3 r (by omega)]
  have mm : c₈.nmem = c.nmem := by rw [hm8, mm7, hm6, mm5, hm4, mm3, bm, am]
  refine ⟨c₈, _, .seq x₁ (.seq x₂ (.seq x₃ (.seq x₄ (.seq x₅ (.seq x₆ (.seq x₇ x₈)))))),
    by omega, ⟨(k8' 8220 (by omega) (by omega)).trans s20, (k8' 8221 (by omega) (by omega)).trans s21,
      (k8' 8222 (by omega) (by omega)).trans s22, (k8' 8223 (by omega) (by omega)).trans s23, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun r hr h1 h2 => ?_, mm, by rw [hr8, mr7, hr6, mr5, hr4, mr3, br, ar],
    by rw [hrm8, mrm7, hrm6, mrm5, hrm4, mrm3, brm, arm],
    by rw [ho8, mo7, ho6, mo5, ho4, mo3, bo, ao]⟩
  · rw [k8' _ (by omega) (by omega), g _ (by omega) (by omega), a24, r57]
  · rw [k8' _ (by omega) (by omega), g _ (by omega) (by omega), a25, r97]
  · rw [k8' _ (by omega) (by omega), g _ (by omega) (by omega), a26, r82]
  · rw [k8' _ (by omega) (by omega), b27, aR _ (by omega), r91]
  · rw [k8' _ (by omega) (by omega), b28, aR _ (by omega), r35]
  · rw [k8' _ (by omega) (by omega), b29, aR _ (by omega), r28]
  · rw [k8' _ (by omega) (by omega), b30, aR _ (by omega), r94]
  · rw [k8' _ (by omega) (by omega), b31, aR _ (by omega), r95]
  · rw [k8' _ (by omega) (by omega), b32, aR _ (by omega), r96]
  · rw [hR8 _ (by omega) (by omega) (by omega), q7 _ (by omega) (by omega),
      hR4 _ (by omega) (by omega) (by omega)]; exact m33
  · rw [hR8 _ (by omega) (by omega) (by omega), q7 8234 (by omega) (by omega), h34, eL]
  · rw [hR8 _ (by omega) (by omega) (by omega), q7 8235 (by omega) (by omega), h35, eT]
  · rw [hR8 _ (by omega) (by omega) (by omega), q7 8236 (by omega) (by omega), h36, eK]
  · rw [h40, e0, eT]; try ring
  · rw [h41, e0, eT, eL]; try ring
  · rw [k8 r hr h1 h2, bR r (by omega), aR r (by omega)]

/-- **The register facts of stage D1** (`β = Wb + 1`, `Wb = B + 16 (n + 1)`, `n = 4 nD + 1`). -/
structure DReg (e : Config) (w cV cF k t nD IM A1 H N1 SL TI Lg : ℕ) : Prop where
  a : DRegA e w cV cF k t nD IM A1 H N1 SL TI Lg
  d45 : e.nreg 8245 = MsEnc.msHI w cV cF k
  d46 : e.nreg 8246 = 2 * MsEnc.msHI w cV cF k + 1
  d47 : e.nreg 8247 = dB w nD k t
  d48 : e.nreg 8248 = dB w nD k t + 16 * (4 * nD + 1 + 1)
  d49 : e.nreg 8249 = dB w nD k t + 16 * (4 * nD + 1 + 1) + 1
  d50 : e.nreg 8250 = 4 * nD + 1
  d51 : e.nreg 8251 = dLen nD k t
  d52 : e.nreg 8252 = 3 * nD + 3
  d53 : e.nreg 8253 = 4 * nD + 1 + k
  d54 : e.nreg 8254 = A1 + 21 * nD + 6
  d55 : e.nreg 8255 = IM + 6 * nD
  d56 : e.nreg 8256 = IM + 7 * nD
  d57 : e.nreg 8257 = IM + 4 * nD
  d59 : e.nreg 8259 = Klein.kleinWN (dB w nD k t) (4 * nD + 1) (MsEnc.msHI w cV cF k) + 1
  d60 : e.nreg 8260 = dB w nD k t + 16 * (4 * nD + 1 + 1) + 1 + 3 * nD
  d61 : e.nreg 8261 = dB w nD k t + 16 * (4 * nD + 1 + 1) + 1 + 3 * nD + 3

lemma DReg.congr {e e' : Config} {w cV cF k t nD IM A1 H N1 SL TI Lg : ℕ}
    (h : DReg e w cV cF k t nD IM A1 H N1 SL TI Lg)
    (hr : ∀ r, 8220 ≤ r → r < 8262 → e'.nreg r = e.nreg r) :
    DReg e' w cV cF k t nD IM A1 H N1 SL TI Lg := by
  refine ⟨h.a.congr fun r h1 h2 => hr r h1 (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hr _ (by omega) (by omega)]
  exacts [h.d45, h.d46, h.d47, h.d48, h.d49, h.d50, h.d51, h.d52, h.d53, h.d54, h.d55, h.d56,
    h.d57, h.d59, h.d60, h.d61]

set_option maxHeartbeats 4000000 in
/-- **Stage D1b: `Hc`, `B`, `β`, `β'` and the addresses.** -/
theorem msD1b_exec (c : Config) (hc : WordsBounded W c)
    {w cV cF k t nD IM A1 H N1 SL TI Lg : ℕ} (hA : DRegA c w cV cF k t nD IM A1 H N1 SL TI Lg)
    (hW : 8 * Klein.kleinWN (dB w nD k t) (4 * nD + 1) (MsEnc.msHI w cV cF k) + 4 * IM +
      4 * A1 + 300 * nD + 4 * k + 8 * t + 500 ≤ W) :
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
    dh4_exec (P := P) c₂ x₂.wb_right (w := w) (k := k) (t := t) (nD := nD) (IM := IM) (A1 := A1)
      (P1 := cV * w) (L := MsEnc.msL w cV) (K := MsEnc.msK w cV) (H0 := MsEnc.msH0 w cV k)
      (P4 := cF * (MsEnc.msH0 w cV k + MsEnc.msL w cV + 2 * (cV * w))) (T2 := t * t) hA2.d20 hA2.d23 hA2.d24 hA2.d25 hA2.d26 hA2.d27 hA2.d33
      hA2.d34 hA2.d36 hA2.d40 (by rw [mR2 _ (by omega)]; exact m42) m43 (by omega)
  have e45 : c₃.nreg 8245 = MsEnc.msHI w cV cF k := by rw [h45, eH]
  have e46 : c₃.nreg 8246 = 2 * MsEnc.msHI w cV cF k + 1 := by rw [h46, eH]; ring
  obtain ⟨c₄, t₄, x₄, ht₄, m58, mR4, mm4, mr4, mrm4, mo4⟩ :=
    mulR_exec (P := P) c₃ x₃.wb_right 8258 8246 8246 (by rw [e46]; omega)
  rw [e46] at m58
  obtain ⟨c₅, x₅, h59, h60, h61, hR5, hm5, hr5, hrm5, ho5⟩ :=
    dh5_exec (P := P) c₄ x₄.wb_right (nD := nD) (Mo := 2 * MsEnc.msHI w cV cF k + 1)
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

/-- **Stage D1: the constants of Klein's start in registers.** -/
theorem msD1_exec (c : Config) (hc : WordsBounded W c)
    {w cV cF k t nD IM A1 H N1 SL TI Lg : ℕ}
    (r42 : c.nreg 7342 = w) (r98 : c.nreg 8298 = cV) (r99 : c.nreg 8299 = cF)
    (r56 : c.nreg 8156 = k) (r57 : c.nreg 8157 = t) (r97 : c.nreg 8297 = nD)
    (r82 : c.nreg 8282 = IM) (r91 : c.nreg 8291 = A1) (r35 : c.nreg 7335 = H)
    (r28 : c.nreg 7328 = N1) (r94 : c.nreg 8294 = SL) (r95 : c.nreg 8295 = TI)
    (r96 : c.nreg 8296 = Lg)
    (hW : 8 * Klein.kleinWN (dB w nD k t) (4 * nD + 1) (MsEnc.msHI w cV cF k) + 4 * IM +
      4 * A1 + 300 * nD + 4 * k + 8 * t + 500 ≤ W) :
    ∃ e u, Exec P W msD1 c e u ∧
      u ≤ 13 + 4 + hpCost dh1L + hpCost dh2L + hpCost dh3L + (3 + hpCost dh4L + hpCost dh5L) ∧
      DReg e w cV cF k t nD IM A1 H N1 SL TI Lg ∧
      (∀ r, (r < 8220 ∨ 8262 ≤ r) → r ≠ 7370 → r ≠ 7371 → e.nreg r = c.nreg r) ∧
      e.nmem = c.nmem ∧ e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  have hMo := Nat.le_mul_self (2 * MsEnc.msHI w cV cF k + 1)
  have eKW : Klein.kleinWN (dB w nD k t) (4 * nD + 1) (MsEnc.msHI w cV cF k) =
      2 * (dB w nD k t + 16 * (4 * nD + 1 + 1)) + 1 +
      (2 * MsEnc.msHI w cV cF k + 1) * (2 * MsEnc.msHI w cV cF k + 1) +
      (2 * MsEnc.msHI w cV cF k + 1) := rfl
  obtain ⟨c₁, u₁, x₁, hu₁, hA, R1, m1, r1, rm1, o1⟩ := msD1a_exec (P := P) c hc r42 r98 r99 r56
    r57 r97 r82 r91 r35 r28 r94 r95 r96 (by omega)
  obtain ⟨c₂, u₂, x₂, hu₂, hD, R2, m2, r2, rm2, o2⟩ := msD1b_exec (P := P) c₁ x₁.wb_right hA hW
  exact ⟨c₂, _, .seq x₁ x₂, by omega, hD, fun r h1 h2 h3 => by rw [R2 r h1 h2 h3,
    R1 r (by omega) h2 h3], by rw [m2, m1], by rw [r2, r1], by rw [rm2, rm1], by rw [o2, o1]⟩

end MsEnc

end BKMNW

end PlanarFlow
