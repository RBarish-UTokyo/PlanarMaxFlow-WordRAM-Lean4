module

public import PlanarFlow.BKMNW.MsStC3

/-!
# The MSSP encoder, stage C3: the targets, the flags, the slots

* `scA`, `scB`: the scalars of stages C3–E copied into `r8180 … r8193` (`H`, `IM`, `nD`, `A0`,
  `p`, `nE`, `k`, `t`, `m`, `DU`, `Qb`, `q`, `SL`, `TI`), so that the set-ups below are
  `hpProg`s reading one contiguous block (`xtA`, `xtB`, `xtW`, `mkW`, `slA`, `slW`);
* **`msC3a`** `= scA ; scB ; xtA ; xtB ; xtW ; wrLoop vXT`: the targets `XN[r] =
  NH[nE + RK[TR[CS[r]]]]` and their reach bits `[DI[XN[r]] < H]` at `IM + iXT nD n k`;
* **`msC3b`** `= mkW ; wrLoop vMK`: the flags `MK[CS[r]] := 1` at `aMK n = n = 4 nD + 1` (the
  low memory of Klein's start), the second array into the dummy `DU`;
* **`msC3c`** `= slA ; slW ; wrLoop vSL`: the slots `SL[i] = TI[i] = CN[FL[Q[i]]]`.
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

def scA : Stmt := block [.copyN 8180 7335, .copyN 8181 8282, .copyN 8182 8297, .copyN 8183 8290,
  .copyN 8184 8280, .copyN 8185 8228, .copyN 8186 8156]

def scB : Stmt := block [.copyN 8187 8157, .copyN 8188 8000, .copyN 8189 8289, .copyN 8190 8007,
  .copyN 8191 8006, .copyN 8192 8294, .copyN 8193 8295]

theorem scA_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W scA c c' t ∧ t = 7 ∧ c'.nreg 8180 = c.nreg 7335 ∧
      c'.nreg 8181 = c.nreg 8282 ∧ c'.nreg 8182 = c.nreg 8297 ∧ c'.nreg 8183 = c.nreg 8290 ∧
      c'.nreg 8184 = c.nreg 8280 ∧ c'.nreg 8185 = c.nreg 8228 ∧ c'.nreg 8186 = c.nreg 8156 ∧
      (∀ r, (r < 8180 ∨ 8187 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold scA
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | rfl
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

theorem scB_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W scB c c' t ∧ t = 7 ∧ c'.nreg 8187 = c.nreg 8157 ∧
      c'.nreg 8188 = c.nreg 8000 ∧ c'.nreg 8189 = c.nreg 8289 ∧ c'.nreg 8190 = c.nreg 8007 ∧
      c'.nreg 8191 = c.nreg 8006 ∧ c'.nreg 8192 = c.nreg 8294 ∧ c'.nreg 8193 = c.nreg 8295 ∧
      (∀ r, (r < 8187 ∨ 8194 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold scB
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | rfl
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

def xtAL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8184), (8, hpM.v 8188)], 0),
    ([(1, hpM.v 8184), (6, hpM.v 8188)], 0),
    ([(1, hpM.v 8184), (14, hpM.v 8188)], 0),
    ([(1, hpM.v 8185)], 0)]

theorem xtAL_shape : hpShape 8180 8194 37 1 xtAL = true := by decide

def xtA : Stmt := hpProg 7336 7370 xtAL

theorem xtA_exec (c : Config) (hc : WordsBounded W c) {p nE m : ℕ}
    (s84 : c.nreg 8184 = p) (s85 : c.nreg 8185 = nE) (s88 : c.nreg 8188 = m)
    (hW : p + 8 * m + p + 6 * m + p + 14 * m + nE + 37 ≤ W) :
    ∃ c', Exec P W xtA c c' (hpCost xtAL) ∧
      c'.nreg 7336 = p + 8 * m ∧
      c'.nreg 7337 = p + 6 * m ∧
      c'.nreg 7338 = p + 14 * m ∧
      c'.nreg 7339 = nE ∧
      (∀ r, (r < 7336 ∨ 7340 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 7336 7370 xtAL :=
    hpShape_ok xtAL_shape (by omega) (by omega) (by simp [xtAL]) (by omega) (by simp [xtAL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) xtAL 7336 hok c hc (fun e he => by
    simp only [xtAL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, s84, s85, s88] <;> omega)
  have g : ∀ j < 4, c'.nreg (7336 + j) =
      hpSum c.nreg (xtAL.getD j ([], 0)).1 - (xtAL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [xtAL]; omega)
  refine ⟨c', e, ?_, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [xtAL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [xtAL, hpSum, hpM.ev] at this; rw [this]; simp only [s84, s85, s88] <;> first | omega | ring
  · have := g 1 (by omega); simp [xtAL, hpSum, hpM.ev] at this; rw [this]; simp only [s84, s85, s88] <;> first | omega | ring
  · have := g 2 (by omega); simp [xtAL, hpSum, hpM.ev] at this; rw [this]; simp only [s84, s85, s88] <;> first | omega | ring
  · have := g 3 (by omega); simp [xtAL, hpSum, hpM.ev] at this; rw [this]; simp only [s84, s85, s88] <;> first | omega | ring

def xtBL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8181), (5, hpM.v 8182)], 0),
    ([(1, hpM.v 8183), (21, hpM.v 8182), (6, hpM.one)], 0),
    ([(1, hpM.v 8180)], 0)]

theorem xtBL_shape : hpShape 8180 8194 37 1 xtBL = true := by decide

def xtB : Stmt := hpProg 7346 7370 xtBL

theorem xtB_exec (c : Config) (hc : WordsBounded W c) {H IM nD A0 : ℕ}
    (s80 : c.nreg 8180 = H) (s81 : c.nreg 8181 = IM) (s82 : c.nreg 8182 = nD) (s83 : c.nreg 8183 = A0)
    (hW : IM + 5 * nD + A0 + 21 * nD + 6 + H + 37 ≤ W) :
    ∃ c', Exec P W xtB c c' (hpCost xtBL) ∧
      c'.nreg 7346 = IM + 5 * nD ∧
      c'.nreg 7347 = A0 + 21 * nD + 6 ∧
      c'.nreg 7348 = H ∧
      (∀ r, (r < 7346 ∨ 7349 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 7346 7370 xtBL :=
    hpShape_ok xtBL_shape (by omega) (by omega) (by simp [xtBL]) (by omega) (by simp [xtBL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) xtBL 7346 hok c hc (fun e he => by
    simp only [xtBL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, s80, s81, s82, s83] <;> omega)
  have g : ∀ j < 3, c'.nreg (7346 + j) =
      hpSum c.nreg (xtBL.getD j ([], 0)).1 - (xtBL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [xtBL]; omega)
  refine ⟨c', e, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [xtBL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [xtBL, hpSum, hpM.ev] at this; rw [this]; simp only [s80, s81, s82, s83] <;> first | omega | ring
  · have := g 1 (by omega); simp [xtBL, hpSum, hpM.ev] at this; rw [this]; simp only [s80, s81, s82, s83] <;> first | omega | ring
  · have := g 2 (by omega); simp [xtBL, hpSum, hpM.ev] at this; rw [this]; simp only [s80, s81, s82, s83] <;> first | omega | ring

def xtWL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8187)], 0),
    ([(1, hpM.v 8181), (37, hpM.v 8182), (1, hpM.v 8186), (11, hpM.one)], 0),
    ([(1, hpM.v 8181), (37, hpM.v 8182), (1, hpM.v 8186), (11, hpM.one), (1, hpM.v 8187)], 0)]

theorem xtWL_shape : hpShape 8180 8194 37 1 xtWL = true := by decide

def xtW : Stmt := hpProg 8200 7370 xtWL

theorem xtW_exec (c : Config) (hc : WordsBounded W c) {IM nD k t : ℕ}
    (s81 : c.nreg 8181 = IM) (s82 : c.nreg 8182 = nD) (s86 : c.nreg 8186 = k) (s87 : c.nreg 8187 = t)
    (hW : t + IM + 37 * nD + k + 11 + IM + 37 * nD + k + 11 + t + 37 ≤ W) :
    ∃ c', Exec P W xtW c c' (hpCost xtWL) ∧
      c'.nreg 8200 = t ∧
      c'.nreg 8201 = IM + 37 * nD + k + 11 ∧
      c'.nreg 8202 = IM + 37 * nD + k + 11 + t ∧
      (∀ r, (r < 8200 ∨ 8203 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8200 7370 xtWL :=
    hpShape_ok xtWL_shape (by omega) (by omega) (by simp [xtWL]) (by omega) (by simp [xtWL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) xtWL 8200 hok c hc (fun e he => by
    simp only [xtWL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, s81, s82, s86, s87] <;> omega)
  have g : ∀ j < 3, c'.nreg (8200 + j) =
      hpSum c.nreg (xtWL.getD j ([], 0)).1 - (xtWL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [xtWL]; omega)
  refine ⟨c', e, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [xtWL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [xtWL, hpSum, hpM.ev] at this; rw [this]; simp only [s81, s82, s86, s87] <;> first | omega | ring
  · have := g 1 (by omega); simp [xtWL, hpSum, hpM.ev] at this; rw [this]; simp only [s81, s82, s86, s87] <;> first | omega | ring
  · have := g 2 (by omega); simp [xtWL, hpSum, hpM.ev] at this; rw [this]; simp only [s81, s82, s86, s87] <;> first | omega | ring

def mkWL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8187)], 0),
    ([(4, hpM.v 8182), (1, hpM.one)], 0),
    ([(1, hpM.v 8189)], 0)]

theorem mkWL_shape : hpShape 8180 8194 37 1 mkWL = true := by decide

def mkW : Stmt := hpProg 8200 7370 mkWL

theorem mkW_exec (c : Config) (hc : WordsBounded W c) {nD t DU : ℕ}
    (s82 : c.nreg 8182 = nD) (s87 : c.nreg 8187 = t) (s89 : c.nreg 8189 = DU)
    (hW : t + 4 * nD + 1 + DU + 37 ≤ W) :
    ∃ c', Exec P W mkW c c' (hpCost mkWL) ∧
      c'.nreg 8200 = t ∧
      c'.nreg 8201 = 4 * nD + 1 ∧
      c'.nreg 8202 = DU ∧
      (∀ r, (r < 8200 ∨ 8203 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8200 7370 mkWL :=
    hpShape_ok mkWL_shape (by omega) (by omega) (by simp [mkWL]) (by omega) (by simp [mkWL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) mkWL 8200 hok c hc (fun e he => by
    simp only [mkWL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, s82, s87, s89] <;> omega)
  have g : ∀ j < 3, c'.nreg (8200 + j) =
      hpSum c.nreg (mkWL.getD j ([], 0)).1 - (mkWL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [mkWL]; omega)
  refine ⟨c', e, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [mkWL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [mkWL, hpSum, hpM.ev] at this; rw [this]; simp only [s82, s87, s89] <;> first | omega | ring
  · have := g 1 (by omega); simp [mkWL, hpSum, hpM.ev] at this; rw [this]; simp only [s82, s87, s89] <;> first | omega | ring
  · have := g 2 (by omega); simp [mkWL, hpSum, hpM.ev] at this; rw [this]; simp only [s82, s87, s89] <;> first | omega | ring

def slAL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8190)], 0),
    ([(1, hpM.v 8184), (1, hpM.v 8188)], 0),
    ([(1, hpM.v 8184), (9, hpM.v 8188)], 1)]

theorem slAL_shape : hpShape 8180 8194 37 1 slAL = true := by decide

def slA : Stmt := hpProg 8270 7370 slAL

theorem slA_exec (c : Config) (hc : WordsBounded W c) {p m Qb : ℕ}
    (s84 : c.nreg 8184 = p) (s88 : c.nreg 8188 = m) (s90 : c.nreg 8190 = Qb)
    (hW : Qb + p + m + p + 9 * m - 1 + 37 ≤ W) :
    ∃ c', Exec P W slA c c' (hpCost slAL) ∧
      c'.nreg 8270 = Qb ∧
      c'.nreg 8271 = p + m ∧
      c'.nreg 8272 = p + 9 * m - 1 ∧
      (∀ r, (r < 8270 ∨ 8273 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8270 7370 slAL :=
    hpShape_ok slAL_shape (by omega) (by omega) (by simp [slAL]) (by omega) (by simp [slAL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) slAL 8270 hok c hc (fun e he => by
    simp only [slAL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, s84, s88, s90] <;> omega)
  have g : ∀ j < 3, c'.nreg (8270 + j) =
      hpSum c.nreg (slAL.getD j ([], 0)).1 - (slAL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [slAL]; omega)
  refine ⟨c', e, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [slAL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [slAL, hpSum, hpM.ev] at this; rw [this]; simp only [s84, s88, s90] <;> first | omega | ring
  · have := g 1 (by omega); simp [slAL, hpSum, hpM.ev] at this; rw [this]; simp only [s84, s88, s90] <;> first | omega | ring
  · have := g 2 (by omega); simp [slAL, hpSum, hpM.ev] at this; rw [this]; simp only [s84, s88, s90] <;> first | omega | ring

def slWL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8191)], 0),
    ([(1, hpM.v 8192)], 0),
    ([(1, hpM.v 8193)], 0)]

theorem slWL_shape : hpShape 8180 8194 37 1 slWL = true := by decide

def slW : Stmt := hpProg 8200 7370 slWL

theorem slW_exec (c : Config) (hc : WordsBounded W c) {q SL TI : ℕ}
    (s91 : c.nreg 8191 = q) (s92 : c.nreg 8192 = SL) (s93 : c.nreg 8193 = TI)
    (hW : q + SL + TI + 37 ≤ W) :
    ∃ c', Exec P W slW c c' (hpCost slWL) ∧
      c'.nreg 8200 = q ∧
      c'.nreg 8201 = SL ∧
      c'.nreg 8202 = TI ∧
      (∀ r, (r < 8200 ∨ 8203 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8200 7370 slWL :=
    hpShape_ok slWL_shape (by omega) (by omega) (by simp [slWL]) (by omega) (by simp [slWL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) slWL 8200 hok c hc (fun e he => by
    simp only [slWL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, s91, s92, s93] <;> omega)
  have g : ∀ j < 3, c'.nreg (8200 + j) =
      hpSum c.nreg (slWL.getD j ([], 0)).1 - (slWL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [slWL]; omega)
  refine ⟨c', e, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [slWL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [slWL, hpSum, hpM.ev] at this; rw [this]; simp only [s91, s92, s93] <;> first | omega | ring
  · have := g 1 (by omega); simp [slWL, hpSum, hpM.ev] at this; rw [this]; simp only [s91, s92, s93] <;> first | omega | ring
  · have := g 2 (by omega); simp [slWL, hpSum, hpM.ev] at this; rw [this]; simp only [s91, s92, s93] <;> first | omega | ring

/-- **Stage C3a: the targets.** -/
def msC3a : Stmt := .seq (.seq scA scB) (.seq xtA (.seq xtB (.seq xtW (wrLoop vXT))))

/-- **Stage C3b: the flags.** -/
def msC3b : Stmt := .seq mkW (wrLoop vMK)

/-- **Stage C3c: the slots.** -/
def msC3c : Stmt := .seq slA (.seq slW (wrLoop vSL))

/-- **Stage C3.** -/
def msC3 : Stmt := .seq msC3a (.seq msC3b msC3c)

/-- The scalars of stages C3–E. -/
structure Scal (c : Config) (H IM nD A0 p nE k t m DU Qb q SL TI : ℕ) : Prop where
  s80 : c.nreg 8180 = H
  s81 : c.nreg 8181 = IM
  s82 : c.nreg 8182 = nD
  s83 : c.nreg 8183 = A0
  s84 : c.nreg 8184 = p
  s85 : c.nreg 8185 = nE
  s86 : c.nreg 8186 = k
  s87 : c.nreg 8187 = t
  s88 : c.nreg 8188 = m
  s89 : c.nreg 8189 = DU
  s90 : c.nreg 8190 = Qb
  s91 : c.nreg 8191 = q
  s92 : c.nreg 8192 = SL
  s93 : c.nreg 8193 = TI

lemma Scal.congr {c c' : Config} {H IM nD A0 p nE k t m DU Qb q SL TI : ℕ}
    (h : Scal c H IM nD A0 p nE k t m DU Qb q SL TI)
    (hr : ∀ r, 8180 ≤ r → r < 8194 → c'.nreg r = c.nreg r) :
    Scal c' H IM nD A0 p nE k t m DU Qb q SL TI :=
  ⟨by rw [hr _ (by omega) (by omega)]; exact h.s80, by rw [hr _ (by omega) (by omega)]; exact h.s81,
    by rw [hr _ (by omega) (by omega)]; exact h.s82, by rw [hr _ (by omega) (by omega)]; exact h.s83,
    by rw [hr _ (by omega) (by omega)]; exact h.s84, by rw [hr _ (by omega) (by omega)]; exact h.s85,
    by rw [hr _ (by omega) (by omega)]; exact h.s86, by rw [hr _ (by omega) (by omega)]; exact h.s87,
    by rw [hr _ (by omega) (by omega)]; exact h.s88, by rw [hr _ (by omega) (by omega)]; exact h.s89,
    by rw [hr _ (by omega) (by omega)]; exact h.s90, by rw [hr _ (by omega) (by omega)]; exact h.s91,
    by rw [hr _ (by omega) (by omega)]; exact h.s92, by rw [hr _ (by omega) (by omega)]; exact h.s93⟩

/-- The scalars: `scA ; scB`. -/
theorem scAB_exec (c : Config) (hc : WordsBounded W c) {H IM nD A0 p nE k t m DU Qb q SL TI : ℕ}
    (r35 : c.nreg 7335 = H) (r82 : c.nreg 8282 = IM) (r97 : c.nreg 8297 = nD)
    (r90 : c.nreg 8290 = A0) (r80 : c.nreg 8280 = p) (r28 : c.nreg 8228 = nE)
    (r56 : c.nreg 8156 = k) (r57 : c.nreg 8157 = t) (r00 : c.nreg 8000 = m)
    (r89 : c.nreg 8289 = DU) (r07 : c.nreg 8007 = Qb) (r06 : c.nreg 8006 = q)
    (r94 : c.nreg 8294 = SL) (r95 : c.nreg 8295 = TI) :
    ∃ c' t', Exec P W (.seq scA scB) c c' t' ∧ t' = 14 ∧
      Scal c' H IM nD A0 p nE k t m DU Qb q SL TI ∧
      (∀ r, (r < 8180 ∨ 8194 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a80, a81, a82, a83, a84, a85, a86, aR, am, ar, arm, ao⟩ :=
    scA_exec (P := P) c hc
  obtain ⟨c₂, t₂, e₂, ht₂, b87, b88, b89, b90, b91, b92, b93, bR, bm, br, brm, bo⟩ :=
    scB_exec (P := P) c₁ e₁.wb_right
  refine ⟨c₂, _, .seq e₁ e₂, by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun r hr => ?_, by rw [bm, am], by rw [br, ar], by rw [brm, arm], by rw [bo, ao]⟩
  · rw [bR _ (by omega), a80]; exact r35
  · rw [bR _ (by omega), a81]; exact r82
  · rw [bR _ (by omega), a82]; exact r97
  · rw [bR _ (by omega), a83]; exact r90
  · rw [bR _ (by omega), a84]; exact r80
  · rw [bR _ (by omega), a85]; exact r28
  · rw [bR _ (by omega), a86]; exact r56
  · rw [b87, aR _ (by omega)]; exact r57
  · rw [b88, aR _ (by omega)]; exact r00
  · rw [b89, aR _ (by omega)]; exact r89
  · rw [b90, aR _ (by omega)]; exact r07
  · rw [b91, aR _ (by omega)]; exact r06
  · rw [b92, aR _ (by omega)]; exact r94
  · rw [b93, aR _ (by omega)]; exact r95
  · rw [bR r (by omega), aR r (by omega)]

set_option maxHeartbeats 2000000 in
/-- **Stage C3a: the targets and their reach bits.** -/
theorem msC3a_exec (c : Config) (hc : WordsBounded W c) {H IM nD A0 p nE k t m DU Qb q SL TI : ℕ}
    (r35 : c.nreg 7335 = H) (r82 : c.nreg 8282 = IM) (r97 : c.nreg 8297 = nD)
    (r90 : c.nreg 8290 = A0) (r80 : c.nreg 8280 = p) (r28 : c.nreg 8228 = nE)
    (r56 : c.nreg 8156 = k) (r57 : c.nreg 8157 = t) (r00 : c.nreg 8000 = m)
    (r89 : c.nreg 8289 = DU) (r07 : c.nreg 8007 = Qb) (r06 : c.nreg 8006 = q)
    (r94 : c.nreg 8294 = SL) (r95 : c.nreg 8295 = TI)
    (hb : ∀ r < t, c.nmem (p + 8 * m + r) < k ∧
      c.nmem (p + 6 * m + c.nmem (p + 8 * m + r)) < m ∧
      nE + c.nmem (p + 14 * m + c.nmem (p + 6 * m + c.nmem (p + 8 * m + r))) < nD ∧
      xtN c.nmem (p + 8 * m) (p + 6 * m) (p + 14 * m) nE (IM + 5 * nD) r < 4 * nD + 1)
    (ht : t ≤ m) (hk : k ≤ m) (l1 : p + 16 * m ≤ IM) (l2 : IM + 37 * nD + k + 11 + 2 * t ≤ A0)
    (hW : A0 + 25 * nD + 7 + H + 2 * p + 28 * m + nE + IM + 37 * nD + k + 11 + 2 * t + 40 ≤ W) :
    ∃ e t', Exec P W msC3a c e t' ∧ t' ≤ 14 + hpCost xtAL + hpCost xtBL + hpCost xtWL +
        (16 + 8) * t + 5 ∧
      Scal e H IM nD A0 p nE k t m DU Qb q SL TI ∧
      (∀ r < t, e.nmem (IM + 37 * nD + k + 11 + r) =
          xtN c.nmem (p + 8 * m) (p + 6 * m) (p + 14 * m) nE (IM + 5 * nD) r ∧
        e.nmem (IM + 37 * nD + k + 11 + t + r) =
          if c.nmem (A0 + 21 * nD + 6 + xtN c.nmem (p + 8 * m) (p + 6 * m) (p + 14 * m) nE
            (IM + 5 * nD) r) < H then 1 else 0) ∧
      (∀ a, (a < IM + 37 * nD + k + 11 ∨ IM + 37 * nD + k + 11 + 2 * t ≤ a) →
        e.nmem a = c.nmem a) ∧
      (∀ r, (r < 7336 ∨ 7349 ≤ r) → r ≠ 7370 → r ≠ 7371 → (r < 8180 ∨ 8194 ≤ r) →
        (r < 8200 ∨ 8220 ≤ r) → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, hS, aR, am, ar, arm, ao⟩ := scAB_exec (P := P) c hc r35 r82 r97 r90 r80
    r28 r56 r57 r00 r89 r07 r06 r94 r95
  obtain ⟨c₂, e₂, x36, x37, x38, x39, xR, xm, xr, xrm, xo⟩ :=
    xtA_exec (P := P) c₁ e₁.wb_right hS.s84 hS.s85 hS.s88 (by omega)
  have hS2 := hS.congr (c' := c₂) (fun r h1 h2 => xR r (by omega) (by omega) (by omega))
  obtain ⟨c₃, e₃, y46, y47, y48, yR, ym, yr, yrm, yo⟩ :=
    xtB_exec (P := P) c₂ e₂.wb_right hS2.s80 hS2.s81 hS2.s82 hS2.s83 (by omega)
  have hS3 := hS2.congr (c' := c₃) (fun r h1 h2 => yR r (by omega) (by omega) (by omega))
  obtain ⟨c₄, e₄, w00, w01, w02, wR, wm, wr, wrm, wo⟩ :=
    xtW_exec (P := P) c₃ e₃.wb_right hS3.s81 hS3.s82 hS3.s86 hS3.s87 (by omega)
  have hS4 := hS3.congr (c' := c₄) (fun r h1 h2 => wR r (by omega) (by omega) (by omega))
  have m4 : c₄.nmem = c.nmem := by rw [wm, ym, xm, am]
  have q4 : ∀ r, 7336 ≤ r → r < 7340 → c₄.nreg r = c₂.nreg r := fun r h1 h2 => by
    rw [wR r (by omega) (by omega) (by omega), yR r (by omega) (by omega) (by omega)]
  set X := IM + 37 * nD + k + 11 with hX
  obtain ⟨c₅, t₅, e₅, ht₅, w5, wm5, -, wR5, wr5, wrm5, wo5⟩ := wrLoop_exec (P := P) c₄
    e₄.wb_right (VAL := vXT) (B := 16) (m := t) (RVo := X) (RTo := X + t) (N := t)
    w00 w01 w02
    (vXT_spec (P := P) c₄ (t := t) (CSb := p + 8 * m) (TRb := p + 6 * m) (RKb := p + 14 * m)
      (nE := nE) (NHb := IM + 5 * nD) (DIb := A0 + 21 * nD + 6) (H := H) (by rw [q4 _ (by omega) (by omega)]; exact x36)
      (by rw [q4 _ (by omega) (by omega)]; exact x37) (by rw [q4 _ (by omega) (by omega)]; exact x38)
      (by rw [q4 _ (by omega) (by omega)]; exact x39)
      (by rw [wR _ (by omega) (by omega) (by omega)]; exact y46)
      (by rw [wR _ (by omega) (by omega) (by omega)]; exact y47)
      (by rw [wR _ (by omega) (by omega) (by omega)]; exact y48)
      (fun r hr => by
        obtain ⟨b1, b2, b3, b4⟩ := hb r hr
        rw [m4]; unfold Off
        refine ⟨⟨Or.inl (by omega), Or.inl (by omega)⟩, ⟨Or.inl (by omega), Or.inl (by omega)⟩,
          ⟨Or.inl (by omega), Or.inl (by omega)⟩, ⟨Or.inl (by omega), Or.inl (by omega)⟩,
          ⟨Or.inr (by omega), Or.inr (by omega)⟩⟩)
      (fun r hr => by
        obtain ⟨b1, b2, b3, b4⟩ := hb r hr
        rw [m4]
        refine ⟨by omega, by omega, by omega, by omega, by omega⟩) (by omega))
    (fun i hi _ => hi) (fun i hi i' hi' _ _ e => e) (Or.inl le_rfl) (by omega) (by omega)
    (by omega)
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega,
    hS4.congr (fun r h1 h2 => wR5 r (by omega)), fun r hr => ?_, fun a ha => ?_,
    fun r h1 h2 h3 h4 h5 => ?_, by rw [wr5, wr, yr, xr, ar], by rw [wrm5, wrm, yrm, xrm, arm],
    by rw [wo5, wo, yo, xo, ao]⟩
  · obtain ⟨g1, g2⟩ := w5 r hr rfl
    rw [m4] at g1 g2
    exact ⟨g1, by rw [show IM + 37 * nD + k + 11 + t + r = X + t + r by rw [hX]]; exact g2⟩
  · rw [wm5 a (by omega) (by omega), m4]
  · rw [wR5 r (by omega), wR r (by omega) h2 h3, yR r (by omega) h2 h3, xR r (by omega) h2 h3,
      aR r h4]

set_option maxHeartbeats 2000000 in
/-- **Stage C3b: the flags** `MK[CS[r]] := 1` in the low memory at `4 nD + 1`. -/
theorem msC3b_exec (c : Config) (hc : WordsBounded W c) {H IM nD A0 p nE k t m DU Qb q SL TI : ℕ}
    (hS : Scal c H IM nD A0 p nE k t m DU Qb q SL TI) (r36 : c.nreg 7336 = p + 8 * m)
    (hcs : ∀ r < t, c.nmem (p + 8 * m + r) < k)
    (hinj : ∀ r < t, ∀ r' < t, c.nmem (p + 8 * m + r) = c.nmem (p + 8 * m + r') → r = r')
    (l0 : 4 * nD + 1 + k ≤ p) (ht : t ≤ m) (lDU : p + 10 * m ≤ DU)
    (hW : DU + k + 4 * nD + t + 40 ≤ W) :
    ∃ e t', Exec P W msC3b c e t' ∧ t' ≤ hpCost mkWL + (5 + 8) * t + 5 ∧
      Scal e H IM nD A0 p nE k t m DU Qb q SL TI ∧
      (∀ r < t, e.nmem (4 * nD + 1 + c.nmem (p + 8 * m + r)) = 1) ∧
      (∀ a, (∀ r < t, a ≠ 4 * nD + 1 + c.nmem (p + 8 * m + r)) → (a < DU ∨ DU + k ≤ a) →
        e.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 7370 → r ≠ 7371 → (r < 8200 ∨ 8220 ≤ r) → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  obtain ⟨c₁, e₁, w00, w01, w02, wR, wm, wr, wrm, wo⟩ :=
    mkW_exec (P := P) c hc hS.s82 hS.s87 hS.s89 (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, w5, wm5, wk5, wR5, wr5, wrm5, wo5⟩ := wrLoop_exec (P := P) c₁
    e₁.wb_right (VAL := vMK) (B := 5) (m := t) (RVo := 4 * nD + 1) (RTo := DU) (N := k)
    w00 w01 w02
    (vMK_spec (P := P) c₁ (t := t) (CSb := p + 8 * m)
      (by rw [wR _ (by omega) (by omega) (by omega)]; exact r36)
      (fun r hr => ⟨Or.inr (by omega), Or.inl (by omega)⟩) (by omega) (by omega))
    (fun i hi _ => by rw [wm]; exact hcs i hi)
    (fun i hi i' hi' _ _ e => hinj i hi i' hi' (by rw [wm] at e; exact e)) (Or.inl (by omega))
    (by omega) (by omega) (by omega)
  refine ⟨c₂, _, .seq e₁ e₂, by omega,
    hS.congr (fun r h1 h2 => by rw [wR5 r (by omega), wR r (by omega) (by omega) (by omega)]),
    fun r hr => ?_, fun a h1 h2 => ?_, fun r h1 h2 h3 => ?_, by rw [wr5, wr], by rw [wrm5, wrm],
    by rw [wo5, wo]⟩
  · have := (w5 r hr rfl).1; rwa [wm] at this
  · by_cases ha : 4 * nD + 1 ≤ a ∧ a < 4 * nD + 1 + k
    · rw [wk5 a (fun i hi _ => ⟨by rw [wm]; exact h1 i hi, by omega⟩), wm]
    · rw [wm5 a (by omega) h2, wm]
  · rw [wR5 r (by omega), wR r (by omega) h1 h2]

set_option maxHeartbeats 2000000 in
/-- **Stage C3c: the slots** `SL[i] = TI[i] = CN[FL[Q[i]]]`. -/
theorem msC3c_exec (c : Config) (hc : WordsBounded W c) {H IM nD A0 p nE k t m DU Qb q SL TI : ℕ}
    (hS : Scal c H IM nD A0 p nE k t m DU Qb q SL TI)
    (hq : ∀ i < q, c.nmem (Qb + i) < m ∧ c.nmem (p + m + c.nmem (Qb + i)) ≤ m)
    (hm : 1 ≤ m) (lQ : Qb + q ≤ p) (lSL : p + 10 * m ≤ SL) (lTI : SL + q ≤ TI)
    (hW : TI + q + SL + p + 10 * m + Qb + 40 ≤ W) :
    ∃ e t', Exec P W msC3c c e t' ∧ t' ≤ hpCost slAL + hpCost slWL + (9 + 8) * q + 5 ∧
      Scal e H IM nD A0 p nE k t m DU Qb q SL TI ∧
      (∀ i < q, e.nmem (SL + i) = slV c.nmem Qb (p + m) (p + 9 * m - 1) i ∧
        e.nmem (TI + i) = slV c.nmem Qb (p + m) (p + 9 * m - 1) i) ∧
      (∀ a, (a < SL ∨ SL + q ≤ a) → (a < TI ∨ TI + q ≤ a) → e.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 7370 → r ≠ 7371 → (r < 8200 ∨ 8220 ≤ r) → (r < 8270 ∨ 8273 ≤ r) →
        e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  obtain ⟨c₁, e₁, a70, a71, a72, aR, am, ar, arm, ao⟩ :=
    slA_exec (P := P) c hc hS.s84 hS.s88 hS.s90 (by omega)
  have hS1 := hS.congr (c' := c₁) (fun r h1 h2 => aR r (by omega) (by omega) (by omega))
  obtain ⟨c₂, e₂, w00, w01, w02, wR, wm, wr, wrm, wo⟩ :=
    slW_exec (P := P) c₁ e₁.wb_right hS1.s91 hS1.s92 hS1.s93 (by omega)
  have m2 : c₂.nmem = c.nmem := by rw [wm, am]
  obtain ⟨c₃, t₃, e₃, ht₃, w5, wm5, -, wR5, wr5, wrm5, wo5⟩ := wrLoop_exec (P := P) c₂
    e₂.wb_right (VAL := vSL) (B := 9) (m := q) (RVo := SL) (RTo := TI) (N := q)
    w00 w01 w02
    (vSL_spec (P := P) c₂ (q := q) (Qb := Qb) (FLb := p + m) (CNb := p + 9 * m - 1)
      (by rw [wR _ (by omega) (by omega) (by omega)]; exact a70)
      (by rw [wR _ (by omega) (by omega) (by omega)]; exact a71)
      (by rw [wR _ (by omega) (by omega) (by omega)]; exact a72)
      (fun i hi => by
        obtain ⟨b1, b2⟩ := hq i hi
        rw [m2]
        exact ⟨⟨Or.inl (by omega), Or.inl (by omega)⟩, ⟨Or.inl (by omega), Or.inl (by omega)⟩,
          ⟨Or.inl (by omega), Or.inl (by omega)⟩⟩)
      (fun i hi => by
        obtain ⟨b1, b2⟩ := hq i hi
        rw [m2]
        exact ⟨by omega, by omega, by omega⟩) (by omega))
    (fun i hi _ => hi) (fun i hi i' hi' _ _ e => e) (Or.inl lTI) (by omega) (by omega)
    (by omega)
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega,
    hS1.congr (fun r h1 h2 => by rw [wR5 r (by omega), wR r (by omega) (by omega) (by omega)]),
    fun i hi => ?_, fun a h1 h2 => ?_, fun r h1 h2 h3 h4 => ?_, by rw [wr5, wr, ar],
    by rw [wrm5, wrm, arm], by rw [wo5, wo, ao]⟩
  · obtain ⟨g1, g2⟩ := w5 i hi rfl
    rw [m2] at g1 g2
    exact ⟨g1, g2⟩
  · rw [wm5 a h1 h2, m2]
  · rw [wR5 r (by omega), wR r (by omega) h1 h2, aR r (by omega) h1 h2]

end MsEnc

end BKMNW

end PlanarFlow
