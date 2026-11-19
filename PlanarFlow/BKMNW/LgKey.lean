module

public import PlanarFlow.BKMNW.LgPrep
public import PlanarFlow.BKMNW.EncProg

/-!
# The large-piece separator, stage 3: the class keys of the piece map of the core

The level program of `scProg` reads class keys `TK` (`LvIn.tk`, `LvIn.key`): `TK[i] = TK[j]` iff
the tails of the darts `e i`, `e j` are related by `HRel Hs`. On the piece map of the core with
its rotation `st` (`PMap`), these classes are the orbits of `st` (`PMap.vert`), so the keys are
the orbit labels of the rotation array `SG` (stage 2): **`lgKey`** inverts `SG` (`invProg`), clears
the label and table parts of the scratch of `orbProg` and numbers the orbits (`orbProg`).

* pure: `iter_rep`, **`iter_iff_sameCycle`** (an index array representing `τ` through an
  injective enumeration: iterates ↔ `SameCycle`);
* `lgK0` (the bases), `lgK1` (`invProg`), `lgK2` (two zero fills), `lgK3` (`orbProg`), **`lgKey`**;
* **`lgKey_exec`** (within `100 n' + 80` steps): `TK[i] < n'` and
  `TK[i] = TK[j] ↔ st.SameCycle (e i) (e j)` at `b + 6 n'`; with `PMap` this is `HRel`
  (**`lgKey_hrel`**).

Registers (inputs) `5800 = n`, `5810 = b`, `5811 = n'`, `5814 = SGb`, `6521 = 1`; written
`5815 … 5820` and the loops' own (`4400 … 4416`, `4600 … 4605`, `4610 … 4621`, `4640 … 4656`,
`6520 … 6529`). Scratch: `[b + 20 n + 3, b + 27 n + 6)` (`SGI` then the scratch of `orbProg`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver Relation

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-! ### Iterates of an index array and cycles -/

lemma iter_rep {p : ℕ → ℕ} {n' : ℕ} {e : ℕ → D} {τ : Perm D} (hlt : ∀ u < n', p u < n')
    (hrep : ∀ u < n', e (p u) = τ (e u)) (k : ℕ) {i : ℕ} (hi : i < n') :
    e (p^[k] i) = (τ ^ k) (e i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', hrep _ (iter_lt hlt k hi), ih, pow_succ', Perm.mul_apply]

/-- **The iterates of an index array representing `τ`** through an enumeration injective on
`[0, n')`: `j` is an iterate of `i` iff `e i` and `e j` are in one cycle of `τ`. -/
theorem iter_iff_sameCycle {p : ℕ → ℕ} {n' : ℕ} {e : ℕ → D} {τ : Perm D}
    (hlt : ∀ u < n', p u < n') (hrep : ∀ u < n', e (p u) = τ (e u))
    (hinj : ∀ i < n', ∀ j < n', e i = e j → i = j) {i j : ℕ} (hi : i < n') (hj : j < n') :
    (∃ k, p^[k] i = j) ↔ τ.SameCycle (e i) (e j) := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨(k : ℤ), by rw [zpow_natCast, ← iter_rep hlt hrep k hi]⟩
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    refine ⟨k, hinj _ (iter_lt hlt k hi) _ hj ?_⟩
    rw [iter_rep hlt hrep k hi, hk]


/-- **The keys are the classes of `HRel`** on a piece map with its rotation (`PMap.vert`). -/
theorem lgKey_hrel {B : Finset D} {Hs : List (Finset V)} {τ : Perm D} (hN : PMap M B Hs τ)
    {e : ℕ → D} {n' : ℕ} (he : ∀ j < n', e j ∈ B) {TK : ℕ → ℕ}
    (h : ∀ i < n', ∀ j < n', (TK i = TK j ↔ τ.SameCycle (e i) (e j))) :
    ∀ i < n', ∀ j < n', (TK i = TK j ↔ HRel Hs (M.tail (e i)) (M.tail (e j))) :=
  fun i hi j hj => (h i hi j hj).trans (hN.vert _ (he i hi) _ (he j hj))

/-! ### The programs -/

/-- The bases: `5815 = SGI = b + 20 n + 3`, `5816 = Zb = SGI + n`, `5817 = b + 6 n'`,
`5818 = n' + 1`, `5819 = Zb + 3 n' + 1`, `5820 = Zb + 5 n' + 2`. -/
def lgK0 : Stmt := block [.constN 5821 20, .mulN 5815 5821 5800, .addN 5815 5815 5810,
  .constN 5821 3, .addN 5815 5815 5821, .addN 5816 5815 5800, .constN 5821 6,
  .mulN 5817 5821 5811, .addN 5817 5817 5810, .constN 5821 1, .addN 5818 5811 5821,
  .constN 5821 3, .mulN 5819 5821 5811, .addN 5819 5819 5816, .constN 5821 1,
  .addN 5819 5819 5821, .constN 5821 5, .mulN 5820 5821 5811, .addN 5820 5820 5816,
  .constN 5821 2, .addN 5820 5820 5821]

/-- The inverse of the rotation array. -/
def lgK1 : Stmt := .seq (block [.copyN 4600 5811, .copyN 4601 5814, .copyN 4602 5815]) invProg

/-- The zero label and table parts of the scratch. -/
def lgK2 : Stmt :=
  .seq (mapRunS (block [.constN 6523 0]) 5818 5819) (mapRunS (block [.constN 6523 0]) 5818 5820)

/-- The orbit labels. -/
def lgK3 : Stmt :=
  .seq (block [.copyN 4650 5811, .copyN 4651 5814, .copyN 4652 5815, .copyN 4653 5816,
    .copyN 4654 5817]) orbProg

/-- **Stage 3 of the large-piece separator**: the class keys. -/
def lgKey : Stmt := .seq lgK0 (.seq lgK1 (.seq lgK2 lgK3))

/-- The registers written by `lgKey`. -/
def lgKw (x : ℕ) : Prop :=
  (5815 ≤ x ∧ x ≤ 5821) ∨ (4400 ≤ x ∧ x ≤ 4416) ∨ (4600 ≤ x ∧ x ≤ 4605) ∨
    (4610 ≤ x ∧ x ≤ 4621) ∨ (4640 ≤ x ∧ x ≤ 4656) ∨ (6520 ≤ x ∧ x ≤ 6529)

section Exec

variable {P : Input} {W : ℕ}

theorem lgK0_exec (c : Config) (hc : WordsBounded W c) {n b n' : ℕ}
    (r00 : c.nreg 5800 = n) (r10 : c.nreg 5810 = b) (r11 : c.nreg 5811 = n') (hn : n' ≤ n)
    (w : b + 27 * n + 6 ≤ W) (hW : 21 ≤ W) :
    ∃ c' t, Exec P W lgK0 c c' t ∧ t = 21 ∧ c'.nreg 5815 = b + 20 * n + 3 ∧
      c'.nreg 5816 = b + 21 * n + 3 ∧ c'.nreg 5817 = b + 6 * n' ∧ c'.nreg 5818 = n' + 1 ∧
      c'.nreg 5819 = b + 21 * n + 3 + 3 * n' + 1 ∧ c'.nreg 5820 = b + 21 * n + 3 + 5 * n' + 2 ∧
      (∀ x, (x < 5815 ∨ 5821 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lgK0
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r00, r10, r11]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r00, r10, r11])
    try omega

theorem lgK1_exec (c : Config) (hc : WordsBounded W c) {n' SGb SGIb : ℕ}
    (r11 : c.nreg 5811 = n') (r14 : c.nreg 5814 = SGb) (r15 : c.nreg 5815 = SGIb)
    (w1 : SGb + n' ≤ W) (w4 : n' + 1 ≤ W) (w5 : SGIb + n' ≤ W)
    (hlt : ∀ j < n', c.nmem (SGb + j) < n')
    (hinj : ∀ i < n', ∀ j < n', c.nmem (SGb + i) = c.nmem (SGb + j) → i = j)
    (d1 : SGb + n' ≤ SGIb) :
    ∃ c' t, Exec P W lgK1 c c' t ∧ t ≤ 7 * n' + 7 ∧
      (∀ j < n', c'.nmem (SGIb + c.nmem (SGb + j)) = j) ∧
      (∀ a, ¬ (SGIb ≤ a ∧ a < SGIb + n') → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4600 ∨ 4605 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 4600 5811, .copyN 4601 5814, .copyN 4602 5815]) c c₁ k₁ ∧
      k₁ = 3 ∧ c₁.nreg 4600 = n' ∧ c₁.nreg 4601 = SGb ∧ c₁.nreg 4602 = SGIb ∧
      (∀ x, (x < 4600 ∨ 4602 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same, r11, r14, r15])
      try omega
  rw [← gm₁] at hlt hinj
  obtain ⟨c₂, k₂, e₂, hk₂, h1, h2, hr, rr, rm, oo⟩ := invProg_exec (P := P) c₁ e₁.wb_right g0 g1
    g2 w1 w4 (fun j hj => by have := hlt j hj; omega) hinj
    (fun i hi j hj => by have := hlt j hj; omega)
  rw [gm₁] at h1 h2
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, h1, fun a ha => h2 a (fun j hj h => ha ?_),
    fun x hx => by rw [hr x (by omega), gn₁ x (by omega)], by rw [rr, gr₁], by rw [rm, grm₁],
    by rw [oo, go₁]⟩
  have := hlt j hj
  rw [gm₁] at this
  omega

theorem lgK2_exec (c : Config) (hc : WordsBounded W c) {n' Z1 Z2 : ℕ}
    (r18 : c.nreg 5818 = n' + 1) (r19 : c.nreg 5819 = Z1) (r20 : c.nreg 5820 = Z2)
    (r21 : c.nreg 6521 = 1) (w1 : Z1 + n' + 2 ≤ W) (w2 : Z2 + n' + 2 ≤ W) :
    ∃ c' t, Exec P W lgK2 c c' t ∧ t ≤ 12 * n' + 18 ∧
      (∀ a, Z1 ≤ a → a < Z1 + (n' + 1) → c'.nmem a = 0) ∧
      (∀ a, Z2 ≤ a → a < Z2 + (n' + 1) → c'.nmem a = 0) ∧
      (∀ a, ¬ (Z1 ≤ a ∧ a < Z1 + (n' + 1)) → ¬ (Z2 ≤ a ∧ a < Z2 + (n' + 1)) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have z : ∀ (c₀ : Config), WordsBounded W c₀ → ∀ i < n' + 1, ∀ c' : Config, WordsBounded W c' →
      c'.nreg 6520 = i → (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c₀.nreg x) →
      (∀ a, ¬ (Z1 ≤ a ∧ a < Z1 + (n' + 1)) → c'.nmem a = c₀.nmem a) →
      ∃ c'' k, Exec P W (block [.constN 6523 0]) c' c'' k ∧ k ≤ 1 ∧ c''.nreg 6523 = 0 ∧
        (∀ x, ¬ vscr x → c''.nreg x = c'.nreg x) ∧ c''.nmem = c'.nmem ∧
        c''.rreg = c'.rreg ∧ c''.rmem = c'.rmem ∧ c''.output = c'.output :=
    fun c₀ _ i _ c' hw _ _ _ => by
      obtain ⟨c'', k', e', hk'', v, nn, mm, rr, rm, oo⟩ := cst_exec (P := P) (r := 6523) (v := 0)
        c' hw (Nat.zero_le _)
      exact ⟨c'', k', e', by omega, v, fun x hx => nn x (by unfold vscr at hx; omega), mm, rr,
        rm, oo⟩
  obtain ⟨c₁, t₁, e₁, ht₁, f1, m1, n1, rr1, rm1, o1⟩ := mapRun_exec (P := P) c hc
    (vb := block [.constN 6523 0]) (bnd := 5818) (ob := 5819) (m := n' + 1) (Ob := Z1) (B := 1)
    (fun _ => 0) r18 r21 r19 (by omega) (by omega) (by unfold vscr; omega)
    (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => z c hc i hi c' hw h20 hr hm)
  obtain ⟨c₂, t₂, e₂, ht₂, f2, m2, n2, rr2, rm2, o2⟩ := mapRun_exec (P := P) c₁ e₁.wb_right
    (vb := block [.constN 6523 0]) (bnd := 5818) (ob := 5820) (m := n' + 1) (Ob := Z2) (B := 1)
    (fun _ => 0) (by rw [n1 _ (by unfold vscr; omega) (by omega) (by omega), r18])
    (by rw [n1 _ (by unfold vscr; omega) (by omega) (by omega), r21])
    (by rw [n1 _ (by unfold vscr; omega) (by omega) (by omega), r20]) (by omega) (by omega)
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      obtain ⟨c'', k', e', hk'', v, nn, mm, rr, rm, oo⟩ := cst_exec (P := P) (r := 6523) (v := 0)
        c' hw (Nat.zero_le _)
      exact ⟨c'', k', e', by omega, v, fun x hx => nn x (by unfold vscr at hx; omega), mm, rr,
        rm, oo⟩)
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, fun a h1 h2 => ?_, fun a h1 h2 => ?_,
    fun a h1 h2 => by rw [m2 a h2, m1 a h1], fun x hx a b => by rw [n2 x hx a b, n1 x hx a b],
    by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
  · by_cases h3 : Z2 ≤ a ∧ a < Z2 + (n' + 1)
    · have := f2 (a - Z2) (by omega); rwa [show Z2 + (a - Z2) = a by omega] at this
    · rw [m2 a h3]; have := f1 (a - Z1) (by omega); rwa [show Z1 + (a - Z1) = a by omega] at this
  · have := f2 (a - Z2) (by omega); rwa [show Z2 + (a - Z2) = a by omega] at this


theorem lgK3_exec (c : Config) (hc : WordsBounded W c) {n' SGb SGIb Zb OUTb : ℕ}
    (r11 : c.nreg 5811 = n') (r14 : c.nreg 5814 = SGb) (r15 : c.nreg 5815 = SGIb)
    (r16 : c.nreg 5816 = Zb) (r17 : c.nreg 5817 = OUTb)
    (hP : PermArr (fun u => c.nmem (SGb + u)) (fun u => c.nmem (SGIb + u)) n')
    (dP : ∀ u < n', ¬ (Zb ≤ SGb + u ∧ SGb + u < Zb + 6 * n' + 3))
    (dPI : ∀ u < n', ¬ (Zb ≤ SGIb + u ∧ SGIb + u < Zb + 6 * n' + 3))
    (dO : Zb + 6 * n' + 3 ≤ OUTb ∨ OUTb + n' ≤ Zb)
    (hz : ∀ a, Zb + 3 * n' + 1 ≤ a → a < Zb + 4 * n' + 1 → c.nmem a = 0)
    (hz' : ∀ a, Zb + 5 * n' + 2 ≤ a → a < Zb + 6 * n' + 3 → c.nmem a = 0)
    (w1 : Zb + 6 * n' + 3 ≤ W) (w2 : SGb + n' ≤ W) (w3 : SGIb + n' ≤ W) (w4 : OUTb + n' ≤ W) :
    ∃ c' t, Exec P W lgK3 c c' t ∧ t ≤ 85 * n' + 42 ∧
      (∀ i < n', ∀ j < n', (c'.nmem (OUTb + i) = c'.nmem (OUTb + j) ↔
        ReflTransGen (pAdj (fun u => c.nmem (SGb + u)) (fun u => c.nmem (SGIb + u)) n') i j)) ∧
      (∀ j < n', c'.nmem (OUTb + j) < n') ∧
      (∀ a, ¬ (Zb ≤ a ∧ a < Zb + 6 * n' + 3) → ¬ (OUTb ≤ a ∧ a < OUTb + n') →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4400 ∨ (4416 < x ∧ x < 4610) ∨ (4621 < x ∧ x < 4640) ∨ 4656 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, g3, g4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 4650 5811, .copyN 4651 5814, .copyN 4652 5815, .copyN 4653 5816,
        .copyN 4654 5817]) c c₁ k₁ ∧ k₁ = 5 ∧
      c₁.nreg 4650 = n' ∧ c₁.nreg 4651 = SGb ∧ c₁.nreg 4652 = SGIb ∧ c₁.nreg 4653 = Zb ∧
      c₁.nreg 4654 = OUTb ∧
      (∀ x, (x < 4650 ∨ 4654 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same, r11, r14, r15, r16, r17])
      try omega
  rw [← gm₁] at hP hz hz'
  obtain ⟨c₂, k₂, e₂, hk₂, h1, h2, h3, h4, h5, hr, rr, rm, oo⟩ := orbProg_exec (P := P) c₁
    e₁.wb_right g0 g1 g2 g3 g4 hP dP dPI dO hz hz' w1 w2 w3 w4
  rw [gm₁] at h1 h5
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, h1, fun j hj => by have := h2 j hj; omega, h5,
    fun x hx => by rw [hr x hx, gn₁ x (by omega)], by rw [rr, gr₁], by rw [rm, grm₁],
    by rw [oo, go₁]⟩

set_option maxHeartbeats 4000000 in
/-- **Stage 3 of the large-piece separator**: from a rotation array `SG` at `SGb` representing
`τ` through an enumeration `e` injective on `[0, n')`, within `110 n + 100` steps the class keys
`TK` at `b + 6 n'`: `TK[i] < n'` and `TK[i] = TK[j] ↔ τ.SameCycle (e i) (e j)`; memory outside
`[b + 6 n', b + 7 n')` and the scratch `[b + 20 n + 3, b + 27 n + 6)` kept. -/
theorem lgKey_exec (c : Config) (hc : WordsBounded W c) {n b n' SGb : ℕ} {e : ℕ → D}
    {τ : Perm D} (r00 : c.nreg 5800 = n) (r10 : c.nreg 5810 = b) (r11 : c.nreg 5811 = n')
    (r14 : c.nreg 5814 = SGb) (r21 : c.nreg 6521 = 1) (hn : n' ≤ n) (l : SGb + n ≤ b)
    (w : b + 27 * n + 7 ≤ W) (hW : 21 ≤ W)
    (hlt : ∀ j < n', c.nmem (SGb + j) < n')
    (hrep : ∀ j < n', e (c.nmem (SGb + j)) = τ (e j))
    (hinj : ∀ i < n', ∀ j < n', e i = e j → i = j) :
    ∃ c' t, Exec P W lgKey c c' t ∧ t ≤ 110 * n + 100 ∧
      (∀ i < n', c'.nmem (b + 6 * n' + i) < n') ∧
      (∀ i < n', ∀ j < n', (c'.nmem (b + 6 * n' + i) = c'.nmem (b + 6 * n' + j) ↔
        τ.SameCycle (e i) (e j))) ∧
      (∀ a, ¬ (b + 6 * n' ≤ a ∧ a < b + 7 * n') → ¬ (b + 20 * n + 3 ≤ a ∧ a < b + 27 * n + 6) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ lgKw x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₀, t₀, e₀, ht₀, s15, s16, s17, s18, s19, s20, n0, m0, rr0, rm0, o0⟩ := lgK0_exec
    (P := P) c hc r00 r10 r11 hn (by omega) hW
  have q0 : ∀ x, ¬ lgKw x → c₀.nreg x = c.nreg x := fun x hx => by
    unfold lgKw at hx; exact n0 x (by omega)
  have hinjSG : ∀ i < n', ∀ j < n', c.nmem (SGb + i) = c.nmem (SGb + j) → i = j :=
    fun i hi j hj h => by
      have := congrArg e h
      rw [hrep i hi, hrep j hj] at this
      exact hinj i hi j hj (τ.injective this)
  obtain ⟨c₁, t₁, e₁, ht₁, f1, m1, n1, rr1, rm1, o1⟩ := lgK1_exec (P := P) c₀ e₀.wb_right
    (by rw [q0 _ (by unfold lgKw; omega), r11]) (by rw [q0 _ (by unfold lgKw; omega), r14]) s15
    (by omega) (by omega) (by omega) (by rw [m0]; exact hlt) (by rw [m0]; exact hinjSG)
    (by omega)
  rw [m0] at f1 m1
  have q1 : ∀ x, ¬ lgKw x → c₁.nreg x = c.nreg x := fun x hx => by
    unfold lgKw at hx; rw [n1 x (by omega), q0 x (by unfold lgKw; omega)]
  obtain ⟨c₂, t₂, e₂, ht₂, z1, z2, m2, n2, rr2, rm2, o2⟩ := lgK2_exec (P := P) c₁ e₁.wb_right
    (n' := n') (Z1 := b + 21 * n + 3 + 3 * n' + 1) (Z2 := b + 21 * n + 3 + 5 * n' + 2)
    (by rw [n1 _ (by omega)]; exact s18) (by rw [n1 _ (by omega)]; exact s19)
    (by rw [n1 _ (by omega)]; exact s20)
    (by rw [n1 _ (by omega), n0 _ (by omega), r21]) (by omega) (by omega)
  have q2 : ∀ x, ¬ lgKw x → c₂.nreg x = c.nreg x := fun x hx => by
    unfold lgKw at hx; rw [n2 x (by unfold vscr; omega) (by omega) (by omega),
      q1 x (by unfold lgKw; omega)]
  -- the arrays seen by `orbProg`
  have hSG2 : ∀ j < n', c₂.nmem (SGb + j) = c.nmem (SGb + j) := fun j hj => by
    rw [m2 _ (by omega) (by omega), m1 _ (by omega)]
  have hSGI2 : ∀ j < n', c₂.nmem (b + 20 * n + 3 + j) = c₁.nmem (b + 20 * n + 3 + j) :=
    fun j hj => m2 _ (by omega) (by omega)
  have hP : PermArr (fun u => c₂.nmem (SGb + u)) (fun u => c₂.nmem (b + 20 * n + 3 + u)) n' := by
    refine permArr_of_inv (fun u hu => by rw [hSG2 u hu]; exact hlt u hu)
      (fun i hi j hj h => by rw [hSG2 i hi, hSG2 j hj] at h; exact hinjSG i hi j hj h)
      (fun j hj => ?_)
    show c₂.nmem (b + 20 * n + 3 + c₂.nmem (SGb + j)) = j
    rw [hSG2 j hj, hSGI2 _ (hlt j hj)]; exact f1 j hj
  obtain ⟨c₃, t₃, e₃, ht₃, h1, h2, m3, n3, rr3, rm3, o3⟩ := lgK3_exec (P := P) c₂ e₂.wb_right
    (n' := n') (SGb := SGb) (SGIb := b + 20 * n + 3) (Zb := b + 21 * n + 3) (OUTb := b + 6 * n')
    (by rw [q2 _ (by unfold lgKw; omega), r11]) (by rw [q2 _ (by unfold lgKw; omega), r14])
    (by rw [n2 _ (by unfold vscr; omega) (by omega) (by omega), n1 _ (by omega)]; exact s15)
    (by rw [n2 _ (by unfold vscr; omega) (by omega) (by omega), n1 _ (by omega)]; exact s16)
    (by rw [n2 _ (by unfold vscr; omega) (by omega) (by omega), n1 _ (by omega)]; exact s17) hP
    (fun u hu => by omega) (fun u hu => by omega) (Or.inr (by omega))
    (fun a h1 h2 => z1 a (by omega) (by omega)) (fun a h1 h2 => z2 a (by omega) (by omega))
    (by omega) (by omega) (by omega) (by omega)
  have q3 : ∀ x, ¬ lgKw x → c₃.nreg x = c.nreg x := fun x hx => by
    unfold lgKw at hx; rw [n3 x (by omega), q2 x (by unfold lgKw; omega)]
  refine ⟨c₃, t₀ + (t₁ + (t₂ + t₃)), .seq e₀ (.seq e₁ (.seq e₂ e₃)), by omega, h2,
    fun i hi j hj => ?_, fun a ha hb => ?_, q3, by rw [rr3, rr2, rr1, rr0],
    by rw [rm3, rm2, rm1, rm0], by rw [o3, o2, o1, o0]⟩
  · rw [h1 i hi j hj, rtg_pAdj_iff hP hi,
      ← iter_iff_sameCycle (p := fun u => c.nmem (SGb + u)) hlt hrep hinj hi hj]
    have hf : ∀ u < n', c₂.nmem (SGb + u) < n' := fun u hu => by rw [hSG2 u hu]; exact hlt u hu
    exact exists_congr fun k => by
      rw [iter_congr (f := fun u => c₂.nmem (SGb + u)) hf (fun u hu => hSG2 u hu) k hi]
  · rw [m3 a (by omega) (by omega), m2 a (by omega) (by omega), m1 a (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
