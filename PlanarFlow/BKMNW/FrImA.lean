module

public import PlanarFlow.BKMNW.MsSpec

/-!
# The FR image, part A: the parameters of the layout

The FR image program (`FrImC.lean`) lays out the input `frPrm b Dm pm r ET EH Lz mE` of
FR-Dijkstra (`mkPrm b b …`). This file computes its parameters in registers, natural words only:

* `fiA`: `r8112 = 1`, `r8113 = pb = b²`, `r8114 = ob = b² + b`, `r8115 = lb = ob + b + 1 + mE`,
  `r8116 = sb = lb + mE`, `r8117 = db = sb + b`, `r8118 = wb = db + b`, `r8126 = A + sb`;
* `fiL1`, `fiL2` (`log₂` by halving, `Frame.prepLog`): `r8119 = Lv = ⌊log₂ b⌋ + 1`,
  `r8120 = ⌊log₂ (b Lv)⌋ + 1`; `fiP` (doubling): `r8121 = 2 ^ r8120`;
* `fiW`: `r8122 = W` of `mkPrm` (`fW`);
* `fiM`: `r8123 = frH = 6 (b + 2) L`, `r8124 = frM = 2 frH + 1`, `r8125 = M - K mod M`
  (adding it and reducing modulo `M` turns the stored `z + K` into the residue of `z`);
* `fiR`: the registers `r7600 … r7613` that `FrFix.frCall_exec` reads.

The facts on `frPrm`: `frPrm_m` (all the arcs are kept: `m = mE`), the fields
(`frPrm_N`, …, `frPrm_W`), `res_off` (the residue of `w - K` from `w + (M - K mod M)`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Monge.FR NegSSSP

/-! ### The values -/

/-- The levels `⌊log₂ b⌋ + 1`. -/
def fLv (b : ℕ) : ℕ := Nat.log 2 b + 1

/-- The leaves of the heap of the half blocks, `2 ^ (⌊log₂ (b Lv)⌋ + 1)`. -/
def fP2 (b : ℕ) : ℕ := 2 ^ (Nat.log 2 (b * fLv b) + 1)

/-- The word bound of `mkPrm`, written as the program computes it (`wb` the base of the work
space). -/
def fW (b wb : ℕ) : ℕ :=
  wb + (b + b + b) + b * fLv b * 16 + b * 16 + 16 +
    (wb + (b + b + b) + b * fLv b * 16 + b * fLv b * 16 + b * fLv b * 16 + fP2 b * 16) +
    8 * (b * fLv b) * fLv b + 4 * b + 16

/-! ### The fields of `frPrm` -/

section Fields

variable {b : ℕ} {Dm : ℕ → ℕ → ℕ} {pm : ℕ → ℤ} {r mE : ℕ} {ET EH : ℕ → ℕ} {Lz : ℕ → ℤ}

theorem length_pre_eq (Es : List (ℕ × ℕ × ℤ)) (u : ℕ) :
    (pre Es u).length = (Es.filter fun a => a.1 < u).length := by
  induction u with
  | zero => simp [pre]
  | succ u ih =>
    rw [pre_succ, List.length_append, ih, FR.blk, ← List.countP_eq_length_filter,
      ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact countP_split Es u

/-- **All the arcs are kept**: their tails are corners. -/
theorem frPrm_m (h : ∀ a < mE, ET a < b) : (frPrm b Dm pm r ET EH Lz mE).m = mE := by
  show (arcList b (csList ET EH (fun _ => 1) Lz mE)).length = mE
  unfold arcList
  rw [length_pre_eq, csList_ones, List.filter_eq_self.2, List.length_map, List.length_range]
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  simpa using h i (List.mem_range.1 hi)

theorem frPrm_N : (frPrm b Dm pm r ET EH Lz mE).N = b := rfl
theorem frPrm_b : (frPrm b Dm pm r ET EH Lz mE).b = b := rfl
theorem frPrm_Db : (frPrm b Dm pm r ET EH Lz mE).Db = 0 := rfl
theorem frPrm_pb : (frPrm b Dm pm r ET EH Lz mE).pb = b * b := rfl
theorem frPrm_ob : (frPrm b Dm pm r ET EH Lz mE).ob = b * b + b := rfl
theorem frPrm_r : (frPrm b Dm pm r ET EH Lz mE).r = r := rfl

theorem frPrm_lb (h : ∀ a < mE, ET a < b) :
    (frPrm b Dm pm r ET EH Lz mE).lb = b * b + b + b + 1 + mE := by
  have := frPrm_m (Dm := Dm) (pm := pm) (r := r) (EH := EH) (Lz := Lz) h
  show b * b + b + b + 1 + (frPrm b Dm pm r ET EH Lz mE).m = _
  rw [this]

theorem frPrm_sb (h : ∀ a < mE, ET a < b) :
    (frPrm b Dm pm r ET EH Lz mE).sb = b * b + b + b + 1 + mE + mE := by
  have := frPrm_m (Dm := Dm) (pm := pm) (r := r) (EH := EH) (Lz := Lz) h
  show b * b + b + b + 1 + (frPrm b Dm pm r ET EH Lz mE).m + (frPrm b Dm pm r ET EH Lz mE).m = _
  rw [this]

theorem frPrm_db (h : ∀ a < mE, ET a < b) :
    (frPrm b Dm pm r ET EH Lz mE).db = b * b + b + b + 1 + mE + mE + b := by
  have := frPrm_m (Dm := Dm) (pm := pm) (r := r) (EH := EH) (Lz := Lz) h
  show b * b + b + b + 1 + (frPrm b Dm pm r ET EH Lz mE).m + (frPrm b Dm pm r ET EH Lz mE).m +
    b = _
  rw [this]

theorem frPrm_wb (h : ∀ a < mE, ET a < b) :
    (frPrm b Dm pm r ET EH Lz mE).wb = b * b + b + b + 1 + mE + mE + b + b := by
  have := frPrm_m (Dm := Dm) (pm := pm) (r := r) (EH := EH) (Lz := Lz) h
  show b * b + b + b + 1 + (frPrm b Dm pm r ET EH Lz mE).m + (frPrm b Dm pm r ET EH Lz mE).m +
    b + b = _
  rw [this]

theorem frPrm_W (h : ∀ a < mE, ET a < b) :
    (frPrm b Dm pm r ET EH Lz mE).W = fW b (b * b + b + b + 1 + mE + mE + b + b) := by
  have hm := frPrm_m (Dm := Dm) (pm := pm) (r := r) (EH := EH) (Lz := Lz) h
  have e : (frPrm b Dm pm r ET EH Lz mE).W =
      let m := (frPrm b Dm pm r ET EH Lz mE).m
      let wb := b * b + b + b + 1 + m + m + b + b
      wb + 3 * b + 16 * b * lvOf b + 16 * b + 16 +
        (wb + 3 * b + 16 * b * lvOf b + 32 * b * lvOf b +
          16 * 2 ^ (Nat.log 2 (b * lvOf b) + 1)) + 8 * b * lvOf b * lvOf b + 4 * b + 16 := rfl
  rw [e, hm]
  simp only [fW, fP2, fLv, lvOf]
  ring

theorem frM_frPrm (L : ℕ) : frM (frPrm b Dm pm r ET EH Lz mE) L = 2 * (6 * ((b + 2) * L)) + 1 :=
  rfl

theorem frH_frPrm (L : ℕ) : frH (frPrm b Dm pm r ET EH Lz mE) L = 6 * ((b + 2) * L) := rfl

end Fields

/-- **The residue of `w - K` modulo `M`** from `w + (M - K mod M)`. -/
theorem res_off {M w K : ℕ} (hM : 0 < M) (z : ℤ) (hz : (w : ℤ) = z + K) :
    (w + (M - K % M)) % M = (z % (M : ℤ)).toNat := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < M ∧ K = M * q + s :=
    ⟨K / M, K % M, Nat.mod_lt _ hM, (Nat.div_add_mod K M).symm⟩
  have hsm : (M * q + s) % M = s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  rw [hsm]
  have e : (((w + (M - s)) % M : ℕ) : ℤ) = z % M := by
    have h2 : ((w + (M - s) : ℕ) : ℤ) = z + M * (q + 1) := by
      push_cast [Nat.cast_sub hs.le]
      rw [hz]; push_cast; ring
    rw [Int.natCast_mod, h2, Int.add_mul_emod_self_left]
  rw [← e, Int.toNat_natCast]

/-! ### The programs -/

/-- The layout: `pb, ob, lb, sb, db, wb`, `A + sb`. -/
def fiA : Stmt := block [.constN 8112 1, .mulN 8113 8100 8100, .addN 8114 8113 8100,
  .addN 8115 8114 8100, .addN 8115 8115 8112, .addN 8115 8115 8104, .addN 8116 8115 8104,
  .addN 8117 8116 8100, .addN 8118 8117 8100, .addN 8126 8110 8116]

/-- `r8119 := ⌊log₂ b⌋ + 1`. -/
def fiL1 : Stmt := .seq (block [.constN 2966 1, .constN 2967 2, .copyN 2970 8100, .constN 2971 0])
  (.seq Frame.prepLog (block [.addN 8119 2971 2966]))

/-- `r8120 := ⌊log₂ (b Lv)⌋ + 1`. -/
def fiL2 : Stmt := .seq (block [.mulN 2970 8100 8119, .constN 2971 0])
  (.seq Frame.prepLog (block [.addN 8120 2971 2966]))

/-- `r8121 := 2 ^ r8120` by doubling. -/
def fiP : Stmt := .seq (block [.constN 8121 1, .constN 8140 0])
  (.whileLtN 8140 8120 (block [.addN 8121 8121 8121, .addN 8140 8140 8112]))

/-- `r8122 := W`. -/
def fiW : Stmt := block [.addN 8130 8100 8100, .addN 8130 8130 8100, .mulN 8131 8100 8119,
  .constN 8133 16, .mulN 8132 8131 8133, .addN 8134 8118 8130, .addN 8135 8134 8132,
  .addN 8136 8135 8132, .addN 8136 8136 8132, .mulN 8137 8121 8133, .addN 8137 8136 8137,
  .addN 8122 8118 8130, .addN 8122 8122 8132, .mulN 8138 8100 8133, .addN 8122 8122 8138,
  .addN 8122 8122 8133, .addN 8122 8122 8137, .constN 8139 8, .mulN 8139 8139 8131,
  .mulN 8139 8139 8119, .addN 8122 8122 8139, .constN 8138 4, .mulN 8138 8138 8100,
  .addN 8122 8122 8138, .addN 8122 8122 8133]

/-- `r8123 := frH`, `r8124 := frM`, `r8125 := M - K mod M`. -/
def fiM : Stmt := block [.constN 8130 2, .addN 8130 8100 8130, .mulN 8130 8130 8109,
  .constN 8131 6, .mulN 8123 8131 8130, .addN 8124 8123 8123, .addN 8124 8124 8112,
  .modN 8130 8108 8124, .subN 8125 8124 8130]

/-- The registers of `frCall`. -/
def fiR : Stmt := block [.copyN 7600 8100, .copyN 7601 8100, .constN 7602 0, .copyN 7603 8113,
  .copyN 7604 8114, .copyN 7605 8115, .copyN 7606 8103, .copyN 7607 8116, .copyN 7608 8117,
  .copyN 7609 8118, .copyN 7610 8124, .copyN 7611 8123, .addN 7612 8122 8112, .copyN 7613 8110]

/-- **The parameters.** -/
def fiPar : Stmt := .seq fiA (.seq fiL1 (.seq fiL2 (.seq fiP (.seq fiW fiM))))

/-! ### The blocks -/

section Blocks

variable {P : Input} {W : ℕ}

theorem fiA_exec (c : Config) (hc : WordsBounded W c) {b mE A : ℕ} (r00 : c.nreg 8100 = b)
    (r04 : c.nreg 8104 = mE) (r10 : c.nreg 8110 = A)
    (hW : b * b + b + b + 1 + mE + mE + b + b ≤ W) (hA : A + (b * b + b + b + 1 + mE + mE) ≤ W) :
    ∃ c' t, Exec P W fiA c c' t ∧ t = 10 ∧ c'.nreg 8112 = 1 ∧ c'.nreg 8113 = b * b ∧
      c'.nreg 8114 = b * b + b ∧ c'.nreg 8115 = b * b + b + b + 1 + mE ∧
      c'.nreg 8116 = b * b + b + b + 1 + mE + mE ∧
      c'.nreg 8117 = b * b + b + b + 1 + mE + mE + b ∧
      c'.nreg 8118 = b * b + b + b + 1 + mE + mE + b + b ∧
      c'.nreg 8126 = A + (b * b + b + b + 1 + mE + mE) ∧
      (∀ r, (r < 8112 ∨ 8118 < r) → r ≠ 8126 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fiA
  exec_block
  all_goals try ((try config_simp); (try simp only [r00, r04, r10]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r00, r04, r10] <;> omega)
  all_goals (try simp only [upd_apply]); all_goals (try split_ifs); all_goals omega

theorem fiL1_exec (c : Config) (hc : WordsBounded W c) {b : ℕ} (r00 : c.nreg 8100 = b)
    (hW : b + 2 ≤ W) :
    ∃ c' t, Exec P W fiL1 c c' t ∧ t ≤ 4 * b + 8 ∧ c'.nreg 8119 = fLv b ∧
      c'.nreg 2966 = 1 ∧ c'.nreg 2967 = 2 ∧
      (∀ r, (r < 2966 ∨ 2971 < r) → r ≠ 8119 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hlog : Nat.log 2 b ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · simp [h]
    · exact (Nat.log_lt_self 2 h.ne').le
  obtain ⟨c₁, t₁, e₁, ht₁, a66, a67, a70, a71, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.constN 2966 1, .constN 2967 2, .copyN 2970 8100, .constN 2971 0]) c c₁
        t₁ ∧ t₁ = 4 ∧ c₁.nreg 2966 = 1 ∧ c₁.nreg 2967 = 2 ∧ c₁.nreg 2970 = b ∧
        c₁.nreg 2971 = 0 ∧ (∀ r, (r < 2966 ∨ 2971 < r) → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r00])
    simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c₂, t₂, e₂, ht₂, b71, bk, bm, br, brm, bo⟩ :=
    Frame.prepLog_exec (P := P) c₁ e₁.wb_right a66 a67 a70 a71 (by omega)
  have hw₂ := e₂.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, d19, dk, dm, dr, drm, do'⟩ : ∃ c₃ t₃,
      Exec P W (block [.addN 8119 2971 2966]) c₂ c₃ t₃ ∧ t₃ = 1 ∧
        c₃.nreg 8119 = Nat.log 2 b + 1 ∧ (∀ r, r ≠ 8119 → c₃.nreg r = c₂.nreg r) ∧
        c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧
        c₃.output = c₂.output := by
    exec_block
    · config_simp; rw [b71, bk _ (by omega) (by omega), a66]; omega
    refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [b71, bk _ (by omega) (by omega), a66]
    · config_simp; simp only [upd_apply, hr, ↓reduceIte]
  refine ⟨c₃, _, e₁.seq (e₂.seq e₃), by omega, d19, ?_, ?_, fun r h1 h2 => ?_,
    by rw [dm, bm, am], by rw [dr, br, ar], by rw [drm, brm, arm], by rw [do', bo, ao]⟩
  · rw [dk _ (by omega), bk _ (by omega) (by omega), a66]
  · rw [dk _ (by omega), bk _ (by omega) (by omega), a67]
  · rw [dk _ h2, bk _ (by omega) (by omega), ak r h1]

theorem fiL2_exec (c : Config) (hc : WordsBounded W c) {b : ℕ} (r00 : c.nreg 8100 = b)
    (r19 : c.nreg 8119 = fLv b) (r66 : c.nreg 2966 = 1) (r67 : c.nreg 2967 = 2)
    (hW : b * fLv b + 2 ≤ W) :
    ∃ c' t, Exec P W fiL2 c c' t ∧ t ≤ 4 * (b * fLv b) + 6 ∧
      c'.nreg 8120 = Nat.log 2 (b * fLv b) + 1 ∧
      (∀ r, (r < 2966 ∨ 2971 < r) → r ≠ 8120 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hlog : Nat.log 2 (b * fLv b) ≤ b * fLv b := by
    rcases Nat.eq_zero_or_pos (b * fLv b) with h | h
    · simp [h]
    · exact (Nat.log_lt_self 2 h.ne').le
  obtain ⟨c₁, t₁, e₁, ht₁, a70, a71, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.mulN 2970 8100 8119, .constN 2971 0]) c c₁ t₁ ∧ t₁ = 2 ∧
        c₁.nreg 2970 = b * fLv b ∧ c₁.nreg 2971 = 0 ∧
        (∀ r, r ≠ 2970 → r ≠ 2971 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r00, r19]); omega)
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r00, r19])
    simp only [upd_apply, h1, h2, ↓reduceIte]
  obtain ⟨c₂, t₂, e₂, ht₂, b71, bk, bm, br, brm, bo⟩ :=
    Frame.prepLog_exec (P := P) c₁ e₁.wb_right (by rw [ak _ (by omega) (by omega), r66])
      (by rw [ak _ (by omega) (by omega), r67]) a70 a71 (by omega)
  have hw₂ := e₂.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, d20, dk, dm, dr, drm, do'⟩ : ∃ c₃ t₃,
      Exec P W (block [.addN 8120 2971 2966]) c₂ c₃ t₃ ∧ t₃ = 1 ∧
        c₃.nreg 8120 = Nat.log 2 (b * fLv b) + 1 ∧ (∀ r, r ≠ 8120 → c₃.nreg r = c₂.nreg r) ∧
        c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧
        c₃.output = c₂.output := by
    exec_block
    · config_simp; rw [b71, bk _ (by omega) (by omega), ak _ (by omega) (by omega), r66]; omega
    refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [b71, bk _ (by omega) (by omega), ak _ (by omega) (by omega), r66]
    · config_simp; simp only [upd_apply, hr, ↓reduceIte]
  refine ⟨c₃, _, e₁.seq (e₂.seq e₃), by omega, d20, fun r h1 h2 => ?_,
    by rw [dm, bm, am], by rw [dr, br, ar], by rw [drm, brm, arm], by rw [do', bo, ao]⟩
  rw [dk _ h2, bk _ (by omega) (by omega), ak r (by omega) (by omega)]

theorem fiPBody_exec (c₀ c : Config) (hc : WordsBounded W c) {i T : ℕ} (hi : i < T)
    (r12 : c.nreg 8112 = 1) (r40 : c.nreg 8140 = i) (r21 : c.nreg 8121 = 2 ^ i)
    (hW : 2 ^ T ≤ W) (hk : ∀ r, r ≠ 8121 → r ≠ 8140 → c.nreg r = c₀.nreg r) :
    ∃ c' t, Exec P W (block [.addN 8121 8121 8121, .addN 8140 8140 8112]) c c' t ∧ t ≤ 2 ∧
      c'.nreg 8140 = i + 1 ∧ c'.nreg 8121 = 2 ^ (i + 1) ∧
      (∀ r, r ≠ 8121 → r ≠ 8140 → c'.nreg r = c₀.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hp : 2 ^ i + 2 ^ i ≤ W := by
    have : 2 ^ (i + 1) ≤ 2 ^ T := Nat.pow_le_pow_right (by omega) hi
    rw [pow_succ] at this; omega
  have hT : i + 1 ≤ W := by
    have := Nat.lt_two_pow_self (n := T); omega
  exec_block
  all_goals try ((try config_simp); (try simp only [r12, r40, r21]); omega)
  refine ⟨le_rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r12, r40]
  · simp only [r21, pow_succ]; ring
  · simp only [upd_apply, h1, h2, ite_false]; exact hk r h1 h2

theorem fiP_exec (c : Config) (hc : WordsBounded W c) {T : ℕ} (r12 : c.nreg 8112 = 1)
    (r20 : c.nreg 8120 = T) (hW : 2 ^ T ≤ W) :
    ∃ c' t, Exec P W fiP c c' t ∧ t ≤ 4 * T + 4 ∧ c'.nreg 8121 = 2 ^ T ∧
      (∀ r, r ≠ 8121 → r ≠ 8140 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h1 : 1 ≤ 2 ^ T := Nat.one_le_two_pow
  obtain ⟨c₁, t₁, e₁, ht₁, a21, a40, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.constN 8121 1, .constN 8140 0]) c c₁ t₁ ∧ t₁ = 2 ∧
        c₁.nreg 8121 = 1 ∧ c₁.nreg 8140 = 0 ∧
        (∀ r, r ≠ 8121 → r ≠ 8140 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply, h1, h2, ite_false]
  let J : ℕ → Config → Prop := fun i c' =>
    c'.nreg 8121 = 2 ^ i ∧ (∀ r, r ≠ 8121 → r ≠ 8140 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, t₂, e₂, ht₂, -, g21, gk, gm, gr, grm, go⟩ :=
    forLoop_exec (P := P) (a := 8140) (bR := 8120)
      (body := block [.addN 8121 8121 8121, .addN 8140 8140 8112]) J (K := 2) (n := T) c₁
      e₁.wb_right a40 (by rw [ak _ (by omega) (by omega), r20])
      ⟨a21, ak, by rw [am], by rw [ar], by rw [arm], by rw [ao]⟩
      (fun i c' hi hw ha hb hJ => by
        obtain ⟨g21, gk, gm, gr, grm, go⟩ := hJ
        obtain ⟨c'', t, e, ht, b40, b21, bk, bm, br, brm, bo⟩ :=
          fiPBody_exec (P := P) c c' hw hi (by rw [gk _ (by omega) (by omega), r12]) ha g21 hW gk
        exact ⟨c'', t, e, ht, b40, by rw [bk _ (by omega) (by omega), r20],
          ⟨b21, bk, by rw [bm, gm], by rw [br, gr], by rw [brm, grm], by rw [bo, go]⟩⟩)
  exact ⟨c₂, _, e₁.seq e₂, by omega, g21, gk, gm, gr, grm, go⟩

theorem fiW_exec (c : Config) (hc : WordsBounded W c) {b wb : ℕ} (r00 : c.nreg 8100 = b)
    (r18 : c.nreg 8118 = wb) (r19 : c.nreg 8119 = fLv b) (r21 : c.nreg 8121 = fP2 b)
    (hW : fW b wb ≤ W) :
    ∃ c' t, Exec P W fiW c c' t ∧ t = 25 ∧ c'.nreg 8122 = fW b wb ∧
      (∀ r, (r < 8130 ∨ 8139 < r) → r ≠ 8122 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hW' := hW
  unfold fW at hW'
  unfold fiW
  exec_block
  all_goals try ((try config_simp); (try simp only [r00, r18, r19, r21]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r00, r18, r19, r21, fW]
  · repeat rw [upd_other _ _ _ (by omega)]

theorem fiM_exec (c : Config) (hc : WordsBounded W c) {b K L : ℕ} (r00 : c.nreg 8100 = b)
    (r08 : c.nreg 8108 = K) (r09 : c.nreg 8109 = L) (r12 : c.nreg 8112 = 1)
    (hW : 2 * (6 * ((b + 2) * L)) + 1 ≤ W) (hb : b + 6 ≤ W) :
    ∃ c' t, Exec P W fiM c c' t ∧ t = 9 ∧ c'.nreg 8123 = 6 * ((b + 2) * L) ∧
      c'.nreg 8124 = 2 * (6 * ((b + 2) * L)) + 1 ∧
      c'.nreg 8125 = 2 * (6 * ((b + 2) * L)) + 1 - K % (2 * (6 * ((b + 2) * L)) + 1) ∧
      (∀ r, (r < 8123 ∨ 8125 < r) → (r < 8130 ∨ 8131 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fiM
  exec_block
  all_goals try ((try config_simp); (try simp only [r00, r08, r09, r12]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r00, r09]
  · simp only [r00, r09, r12]; omega
  · simp only [r00, r08, r09, r12]
    rw [show 6 * ((b + 2) * L) + 6 * ((b + 2) * L) + 1 = 2 * (6 * ((b + 2) * L)) + 1 by omega]
  · repeat rw [upd_other _ _ _ (by omega)]

theorem fiR_exec (c : Config) (hc : WordsBounded W c) {Wp : ℕ} (r12 : c.nreg 8112 = 1)
    (r22 : c.nreg 8122 = Wp) (hW : Wp + 1 ≤ W) :
    ∃ c' t, Exec P W fiR c c' t ∧ t = 14 ∧
      c'.nreg 7600 = c.nreg 8100 ∧ c'.nreg 7601 = c.nreg 8100 ∧ c'.nreg 7602 = 0 ∧
      c'.nreg 7603 = c.nreg 8113 ∧ c'.nreg 7604 = c.nreg 8114 ∧ c'.nreg 7605 = c.nreg 8115 ∧
      c'.nreg 7606 = c.nreg 8103 ∧ c'.nreg 7607 = c.nreg 8116 ∧ c'.nreg 7608 = c.nreg 8117 ∧
      c'.nreg 7609 = c.nreg 8118 ∧ c'.nreg 7610 = c.nreg 8124 ∧ c'.nreg 7611 = c.nreg 8123 ∧
      c'.nreg 7612 = Wp + 1 ∧ c'.nreg 7613 = c.nreg 8110 ∧
      (∀ r, (r < 7600 ∨ 7613 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fiR
  exec_block
  all_goals try ((try config_simp); (try simp only [r12, r22]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl,
    rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r12, r22])
  repeat rw [upd_other _ _ _ (by omega)]

end Blocks

end MsCall

end BKMNW

end PlanarFlow
