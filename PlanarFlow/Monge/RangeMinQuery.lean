module

public import PlanarFlow.Monge.RangeMinExec

/-!
# Range minima in an anti-Monge matrix on the machine: the query

`rmQuery` answers a query: for the source `σ` (`r312`) and the rows `[j1, j2]` (`r313`, `r314`),
it finds a row `r315` minimising the matrix over `[j1, j2]`, and the minimum in the real
register `r300` (`rmQuery_exec`), within `80 T + 80` steps, on a built structure (`Built`).

It finds the gap of `σ` at the root by a binary search (`rmCnt`), then descends along the paths
to `j1` and `j2` (`qBody`, one level per iteration): the gaps at the children are read in the
cascading arrays, and a child hanging between the two paths offers the row of its gap
(`qCand`). The query writes no memory.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace RM

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs FR Heap

variable {p : RMP} {I : Input}

lemma cell_succ (j f i : ℕ) : cell p (j + 1) f i = cell p j f i + 4 * p.s := by
  unfold cell; ring

lemma cell_eq (j f i : ℕ) : cell p j f i = cell p j 0 0 + f * p.s + i := by
  unfold cell; ring

lemma cell_bound {j : ℕ} (hj : j ≤ p.T) :
    cell p j 0 0 + 4 * p.s ≤ p.B + 4 * (p.T + 1) * p.s := by
  have : j * p.s ≤ p.T * p.s := Nat.mul_le_mul_right _ hj
  unfold cell; nlinarith

lemma W_bound (hL : RMLay p) : p.B + 4 * (p.T + 1) * p.s + 4 * p.s ≤ p.W := by
  have := hL.wB; nlinarith

lemma lg_lt_pow : ∀ {T x : ℕ}, x < 2 ^ T → lg x ≤ T
  | 0, x, h => by
    have : x = 0 := by simp at h; omega
    subst this; rw [lg_zero]
  | T + 1, x, h => by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [lg_zero]; omega
    · rw [lg_pos hx]
      have := lg_lt_pow (T := T) (x := x / 2) (by rw [pow_succ] at h; omega)
      omega

/-- **The structure is built**: every node is correct. -/
def Built (F : ℕ → ℕ → ℝ) (p : RMP) (nm : ℕ → ℕ) : Prop :=
  ∀ j ≤ p.T, ∀ o, 2 ^ j ∣ o → o < p.s → NodeOK F p nm j o

/-- The parameters in the registers `r300 … r307`. -/
structure RPar (p : RMP) (c : Config) : Prop where
  r300 : c.nreg 300 = p.B
  r301 : c.nreg 301 = p.s
  r302 : c.nreg 302 = p.nc
  r303 : c.nreg 303 = p.Ab
  r304 : c.nreg 304 = p.Ls
  r305 : c.nreg 305 = p.Pb
  r306 : c.nreg 306 = p.nr - 1
  r307 : c.nreg 307 = p.T

/-! ### The programs -/

/-- The constants `1`, `2`, `nc + 1`, `4 s`. -/
def rmSetup : Stmt :=
  block [.constN 308 1, .constN 309 2, .addN 310 302 308, .addN 311 301 301, .addN 311 311 311]

/-- The candidate row at the address `r363`: kept in `r315` (its value in the real `r300`) when
strictly better. -/
def qCand : Stmt :=
  .seq (block [.loadN 316 363, .copyN 317 312]) <|
  .seq rmEv (.ifLtR 301 300 (block [.copyN 315 316, .copyR 300 301]) .skip)

/-- The left path goes to the right child. -/
def qRx : Stmt := block [.loadN 355 361, .copyN 353 360]

/-- The left path goes to the left child; the right child is a candidate when the paths are
apart. -/
def qLx : Stmt :=
  .seq (block [.loadN 362 361, .subN 361 361 301, .loadN 355 361, .addN 363 359 360,
    .addN 363 363 362]) (.ifLtN 353 354 qCand .skip)

/-- The right path goes to the right child; the left child is a candidate when the paths are
apart. -/
def qRy : Stmt :=
  .seq (block [.loadN 362 361, .addN 361 361 301, .loadN 356 361, .addN 363 359 354,
    .addN 363 363 362]) (.seq (.ifLtN 353 354 qCand .skip) (.instr (.copyN 354 364)))

/-- The step of the left path. -/
def qX : Stmt := .ifLtN 313 360 qLx qRx

/-- The step of the right path. -/
def qY : Stmt := .ifLtN 314 364 (.instr (.loadN 356 361)) qRy

/-- One level of the query, from the node size `r352`. -/
def qBody : Stmt :=
  .seq (block [.divN 358 352 309, .subN 359 357 301, .addN 360 353 358, .addN 361 357 301,
    .addN 361 361 301, .addN 361 361 353, .addN 361 361 355]) <|
  .seq qX <|
  .seq (block [.addN 364 354 358, .addN 361 357 301, .addN 361 361 354, .addN 361 361 356]) <|
  .seq qY (block [.copyN 352 358, .subN 357 357 311])

/-- **The query**: the source `r312`, the rows `[r313, r314]`; the row `r315`, the value `r300`
(real). -/
def rmQuery : Stmt :=
  .seq rmSetup <|
  .seq (block [.mulN 357 307 311, .addN 357 357 300, .copyN 320 357, .subN 321 301 308,
    .copyN 322 312]) <|
  .seq rmCnt <|
  .seq (block [.copyN 355 323, .copyN 356 323, .constN 353 0, .constN 354 0, .copyN 352 301,
    .copyN 315 313, .copyN 316 313, .copyN 317 312]) <|
  .seq rmEv <|
  .seq (.instr (.copyR 300 301)) <|
  .seq (.whileLtN 308 352 qBody) <|
  .seq (block [.copyN 316 314, .copyN 317 312]) <|
  .seq rmEv (.ifLtR 301 300 (block [.copyN 315 316, .copyR 300 301]) .skip)

/-! ### The constants and the candidates -/

theorem rmSetup_exec (hL : RMLay p) (c : Config) (hc : WordsBounded p.W c) (hP : RPar p c) :
    ∃ c' k, Exec I p.W rmSetup c c' k ∧ k ≤ 5 ∧
      (RCtx p c' ∧ KN 308 312 c c' ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧
        c'.output = c.output) := by
  have hW := W_bound hL; have := hL.wnc; have := hL.s_pos
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := hP
  unfold rmSetup
  exec_block
  · omega
  · omega
  · config_simp; rw [g2]; omega
  · config_simp; rw [g1]; omega
  · config_simp; rw [g1]; omega
  refine ⟨by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_, rfl, rfl,
    rfl, rfl⟩
  all_goals config_simp
  all_goals first | assumption | rfl | (rw [g1]; ring1) | (rw [g2]; omega) | upd_tac

theorem qCand_exec (hL : RMLay p) (c : Config) (hc : WordsBounded p.W c) (hR : RCtx p c)
    (hσ : c.nreg 312 < p.nc) :
    ∃ c' k, Exec I p.W qCand c c' k ∧ k ≤ 15 ∧
      (c'.rreg 300 ≤ c.rreg 300 ∧
        c'.rreg 300 ≤ rmF c.rmem p (c.nmem (c.nreg 363)) (c.nreg 312) ∧
        ((c'.nreg 315 = c.nmem (c.nreg 363) ∧
            c'.rreg 300 = rmF c.rmem p (c.nmem (c.nreg 363)) (c.nreg 312)) ∨
          (c'.nreg 315 = c.nreg 315 ∧ c'.rreg 300 = c.rreg 300)) ∧
        KN 315 320 c c' ∧ KR 300 303 c c' ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧
        c'.output = c.output) := by
  unfold qCand
  refine spec_seq ?_
  exec_block
  refine spec_seq ?_
  refine spec_use (rmEv_exec (I := I) hL _ ‹_› (hR.of fun r h1 h2 => by config_simp; upd_tac)
    (by config_simp; exact hσ)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨e1, hN, hR', hn, hrm, ho⟩
  config_simp at e1; config_simp at hn; config_simp at hrm; config_simp at ho
  have g200 : c₁.rreg 300 = c.rreg 300 := hR' 300 (by omega)
  have g215 : c₁.nreg 315 = c.nreg 315 := (hN 315 (by omega)).trans (by config_simp)
  have g216 : c₁.nreg 316 = c.nmem (c.nreg 363) := (hN 316 (by omega)).trans (by config_simp)
  have hR'' : KR 301 303 c c₁ := fun r hr => hR' r hr
  have hKN : KN 316 320 c c₁ := fun r hr => by rw [hN r (by omega)]; config_simp; upd_tac
  by_cases hb : c₁.rreg 301 < c₁.rreg 300
  · refine spec_ifLtR_true hb ?_
    exec_block
    rw [e1, g200] at hb
    refine ⟨by omega, by config_simp; rw [e1]; exact hb.le, by config_simp; rw [e1],
      Or.inl ⟨by config_simp; rw [g216], by config_simp; rw [e1]⟩, fun r hr => ?_,
      fun r hr => ?_, hn, hrm, ho⟩
    · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hKN r (by omega)
    · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hR'' r (by omega)
  · refine spec_ifLtR_false hb ?_
    rw [e1, g200] at hb
    refine spec_skip hw₁ ⟨by omega, by rw [g200], by rw [g200]; exact not_lt.1 hb,
      Or.inr ⟨g215, g200⟩, fun r hr => ?_, fun r hr => hR'' r (by omega), hn, hrm, ho⟩
    by_cases h215 : r = 315
    · rw [h215, g215]
    · exact hKN r (by omega)

/-! ### The steps of the two paths -/

lemma off_le {d o : ℕ} (hd : d ∣ o) (hs : d ∣ p.s) (ho : o < p.s) : o + d ≤ p.s := by
  obtain ⟨a, rfl⟩ := hd
  obtain ⟨b, hb⟩ := hs
  rw [hb] at ho ⊢
  have : a < b := Nat.lt_of_mul_lt_mul_left ho
  have : d * (a + 1) ≤ d * b := Nat.mul_le_mul_left _ this
  linarith

lemma pow_dvd_s {j : ℕ} (hj : j ≤ p.T) : 2 ^ j ∣ p.s := pow_dvd_pow 2 hj

lemma gapAt_lt (nm : ℕ → ℕ) (j o σ : ℕ) : gapAt nm p j o σ < 2 ^ j := by
  have := cntP_le (f := Arr nm p j 0 o) (σ := σ) (2 ^ j - 1)
  unfold gapAt; have := Nat.one_le_two_pow (n := j); omega

/-- The registers kept by a step of a path. -/
def KX (c c' : Config) : Prop :=
  ∀ r, r ≠ 353 → r ≠ 354 → r ≠ 355 → r ≠ 356 → r ≠ 361 → r ≠ 362 → r ≠ 363 → (r < 315 ∨ 320 ≤ r) →
    c'.nreg r = c.nreg r

/-- The result of a step of a path: the new row `b'` is in `[j1, j2]`, carries its value, and is
not worse than the old one. -/
def StepOK (F : ℕ → ℕ → ℝ) (σ j1 j2 : ℕ) (c c' : Config) : Prop :=
  j1 ≤ c'.nreg 315 ∧ c'.nreg 315 ≤ j2 ∧ c'.rreg 300 = F (c'.nreg 315) σ ∧
    F (c'.nreg 315) σ ≤ F (c.nreg 315) σ

/-- A candidate row of `[lo, hi) ⊆ [j1, j2]` minimising over `[lo, hi)` (`qCand`, through the
address `r363`). -/
theorem qCand_use (hL : RMLay p) (c : Config) (hc : WordsBounded p.W c) (hR : RCtx p c)
    (hσ : c.nreg 312 < p.nc) {lo hi : ℕ}
    (hmin : IsArgmin (rmF c.rmem p) (c.nreg 312) lo hi (c.nmem (c.nreg 363)))
    (hlo : c.nreg 313 ≤ lo) (hhi : hi ≤ c.nreg 314 + 1)
    (hvb : c.rreg 300 = rmF c.rmem p (c.nreg 315) (c.nreg 312))
    (hb1 : c.nreg 313 ≤ c.nreg 315) (hb2 : c.nreg 315 ≤ c.nreg 314) :
    ∃ c' k, Exec I p.W qCand c c' k ∧ k ≤ 15 ∧
      (StepOK (rmF c.rmem p) (c.nreg 312) (c.nreg 313) (c.nreg 314) c c' ∧
        (∀ ρ, lo ≤ ρ → ρ < hi → rmF c.rmem p (c'.nreg 315) (c.nreg 312) ≤
          rmF c.rmem p ρ (c.nreg 312)) ∧
        KN 315 320 c c' ∧ KR 300 303 c c' ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧
        c'.output = c.output) := by
  obtain ⟨c', k, e, hk, q1, q2, q3, hKN, hKR, hn, hrm, ho⟩ := qCand_exec (I := I) hL c hc hR hσ
  obtain ⟨m1, m2, m3⟩ := hmin
  have hv : c'.rreg 300 = rmF c.rmem p (c'.nreg 315) (c.nreg 312) := by
    rcases q3 with ⟨a, b⟩ | ⟨a, b⟩
    · rw [b, a]
    · rw [b, a, hvb]
  refine ⟨c', k, e, hk, ⟨?_, ?_, hv, by rw [← hv, ← hvb]; exact q1⟩, fun ρ h1 h2 => ?_, hKN, hKR,
    hn, hrm, ho⟩
  · rcases q3 with ⟨a, -⟩ | ⟨a, -⟩ <;> rw [a] <;> omega
  · rcases q3 with ⟨a, -⟩ | ⟨a, -⟩ <;> rw [a] <;> omega
  · rw [← hv]; exact q2.trans (m3 ρ h1 h2)

/-- **The step of the left path**, from the node `[ox, ox + 2 h)` (`h = 2 ^ j`): to the child
holding `j1`; the right child, when the path goes left and the paths are apart, is a canonical
node inside `[j1, j2]` and offers its row. -/
theorem qX_exec (hL : RMLay p) (c : Config) (hc : WordsBounded p.W c) (hR : RCtx p c)
    (hσ : c.nreg 312 < p.nc) (hB : Built (rmF c.rmem p) p c.nmem) {j ox oy : ℕ}
    (hj : j + 1 ≤ p.T) (h253 : c.nreg 353 = ox) (h254 : c.nreg 354 = oy)
    (h259 : c.nreg 359 = cell p j 3 0)
    (h260 : c.nreg 360 = ox + 2 ^ j) (h255 : c.nreg 355 = gapAt c.nmem p (j + 1) ox (c.nreg 312))
    (h261 : c.nreg 361 = cell p (j + 1) 2 (ox + c.nreg 355)) (hox : 2 ^ (j + 1) ∣ ox)
    (hoxs : ox < p.s) (hvb : c.rreg 300 = rmF c.rmem p (c.nreg 315) (c.nreg 312))
    (hb1 : c.nreg 313 ≤ c.nreg 315) (hb2 : c.nreg 315 ≤ c.nreg 314)
    (hdis : ox < oy → ox + 2 ^ (j + 1) ≤ oy) (hoy : oy ≤ c.nreg 314) :
    ∃ c' k, Exec I p.W qX c c' k ∧ k ≤ 23 ∧
      (c'.nreg 353 = (if ox + 2 ^ j ≤ c.nreg 313 then ox + 2 ^ j else ox) ∧
        c'.nreg 355 = gapAt c.nmem p j (c'.nreg 353) (c.nreg 312) ∧
        StepOK (rmF c.rmem p) (c.nreg 312) (c.nreg 313) (c.nreg 314) c c' ∧
        (c.nreg 313 < ox + 2 ^ j → ox < oy → ∀ ρ, ox + 2 ^ j ≤ ρ → ρ < ox + 2 * 2 ^ j →
          rmF c.rmem p (c'.nreg 315) (c.nreg 312) ≤ rmF c.rmem p ρ (c.nreg 312)) ∧
        KX c c' ∧ c'.nreg 354 = c.nreg 354 ∧ c'.nreg 356 = c.nreg 356 ∧ KR 300 303 c c' ∧
        c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hW := W_bound hL
  have hcb := cell_bound (p := p) (j := j) (by omega)
  have e3 := cell_eq (p := p) j 3 0
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have hds := off_le hox (pow_dvd_s hj) hoxs
  generalize hσ' : c.nreg 312 = σ at hσ hvb h255 ⊢
  obtain ⟨-, hnode⟩ := hB (j + 1) hj ox hox hoxs
  obtain ⟨-, hcasc⟩ := hnode σ hσ
  obtain ⟨eGL, eGR⟩ := hcasc j rfl
  have hdr : 2 ^ j ∣ ox + 2 ^ j :=
    dvd_add (dvd_trans (pow_dvd_pow 2 (Nat.le_succ j)) hox) dvd_rfl
  obtain ⟨-, hnr⟩ := hB j (by omega) (ox + 2 ^ j) hdr (by omega)
  obtain ⟨hminr, -⟩ := hnr σ hσ
  have ht := gapAt_lt c.nmem (p := p) j (ox + 2 ^ j) σ
  generalize hg : gapAt c.nmem p (j + 1) ox σ = g at h255 eGL eGR
  have hGR : c.nmem (c.nreg 361) = gapAt c.nmem p j (ox + 2 ^ j) σ := by
    rw [h261, h255]; exact eGR
  have hGL : c.nmem (c.nreg 361 - c.nreg 301) = gapAt c.nmem p j ox σ := by
    rw [h261, h255, hR.r301, show cell p (j + 1) 2 (ox + g) - p.s = cell p (j + 1) 1 (ox + g) by
      unfold cell; rw [show 4 * (j + 1) + 2 = (4 * (j + 1) + 1) + 1 by ring, Nat.add_mul,
        Nat.one_mul]; omega]
    exact eGL
  have hrow : ∀ t, t = gapAt c.nmem p j (ox + 2 ^ j) σ →
      c.nmem (cell p j 3 0 + (ox + 2 ^ j) + t) = Arr c.nmem p j 3 (ox + 2 ^ j)
        (gapAt c.nmem p j (ox + 2 ^ j) σ) := by
    intro t ht'; rw [ht']; unfold Arr; congr 1; unfold cell; ring
  unfold qX
  by_cases hleft : c.nreg 313 < ox + 2 ^ j
  · refine spec_ifLtN_true (by rw [h260]; exact hleft) ?_
    unfold qLx
    refine spec_seq ?_
    exec_block
    · config_simp; rw [h259, h260]; omega
    · config_simp; rw [h259, h260, hGR]; omega
    have hnl : ¬ ox + 2 ^ j ≤ c.nreg 313 := by omega
    by_cases hlt : ox < oy
    · refine spec_ifLtN_true (by config_simp; rw [h253, h254]; exact hlt) ?_
      have := hdis hlt
      refine spec_use (qCand_use (I := I) (lo := ox + 2 ^ j) (hi := ox + 2 ^ j + 2 ^ j) hL _ ‹_›
        (hR.of fun r h1 h2 => by config_simp; upd_tac) (by config_simp; rw [hσ']; exact hσ)
        (by config_simp; rw [hσ', h259, h260, hGR, hrow _ rfl]; exact hminr)
        (by config_simp; omega) (by config_simp; omega) (by config_simp; rw [hσ']; exact hvb)
        (by config_simp; exact hb1) (by config_simp; exact hb2)) ?_
      intro c₂ k₂ hk₂ hw₂ ⟨hS, hcov, hKN, hKR, hn, hrm, ho⟩
      config_simp at hS; config_simp at hcov; config_simp at hn; config_simp at hrm
      config_simp at ho; rw [hσ'] at hS hcov
      have k253 : c₂.nreg 353 = ox := (hKN 353 (by omega)).trans (by config_simp; exact h253)
      have k255 : c₂.nreg 355 = gapAt c.nmem p j ox σ := (hKN 355 (by omega)).trans
        (by config_simp; exact hGL)
      refine ⟨by omega, by rw [k253]; simp only [hnl, ↓reduceIte], by rw [k253, k255], hS,
        fun _ _ ρ h1 h2 => hcov ρ h1 (by omega),
        fun r a1 a2 a3 a4 a5 a6 a7 a8 => ?_, ?_, ?_,
        fun r hr => (hKR r hr).trans (by config_simp), hn, hrm, ho⟩
      · rw [hKN r (by omega)]; config_simp; upd_tac
      · rw [hKN 354 (by omega)]; config_simp
      · rw [hKN 356 (by omega)]; config_simp
    · refine spec_ifLtN_false (by config_simp; rw [h253, h254]; exact hlt) ?_
      refine spec_skip ‹_› ⟨by omega, by config_simp; simp only [hnl, ↓reduceIte]; exact h253,
        by config_simp; rw [h253]; exact hGL,
        ⟨by config_simp; exact hb1, by config_simp; exact hb2, by config_simp; exact hvb,
          by config_simp; exact le_rfl⟩, fun _ h => absurd h hlt,
        fun r a1 a2 a3 a4 a5 a6 a7 a8 => ?_,
        by config_simp, by config_simp, fun r hr => by config_simp, rfl, rfl, rfl⟩
      config_simp; upd_tac
  · refine spec_ifLtN_false (by rw [h260]; exact hleft) ?_
    unfold qRx
    have hr' : ox + 2 ^ j ≤ c.nreg 313 := by omega
    exec_block
    refine ⟨by omega, by config_simp; rw [h260]; simp only [hr', ↓reduceIte],
      by config_simp; rw [h260]; exact hGR, ⟨by config_simp; exact hb1,
      by config_simp; exact hb2, by config_simp; exact hvb, by config_simp; exact le_rfl⟩,
      fun h => absurd h hleft, fun r a1 a2 a3 a4 a5 a6 a7 a8 => ?_, by config_simp,
      by config_simp, fun r hr => by config_simp, rfl, rfl, rfl⟩
    config_simp; upd_tac

/-- **The step of the right path**, from the node `[oy, oy + 2 h)` (`h = 2 ^ j`): to the child
holding `j2`; the left child, when the path goes right and the paths are apart (the test is on
the new node of the left path, `r353`), is a canonical node inside `[j1, j2]` and offers its
row. -/
theorem qY_exec (hL : RMLay p) (c : Config) (hc : WordsBounded p.W c) (hR : RCtx p c)
    (hσ : c.nreg 312 < p.nc) (hB : Built (rmF c.rmem p) p c.nmem) {j oy : ℕ}
    (hj : j + 1 ≤ p.T) (h254 : c.nreg 354 = oy) (h259 : c.nreg 359 = cell p j 3 0)
    (h264 : c.nreg 364 = oy + 2 ^ j) (h256 : c.nreg 356 = gapAt c.nmem p (j + 1) oy (c.nreg 312))
    (h261 : c.nreg 361 = cell p (j + 1) 1 (oy + c.nreg 356)) (hoy : 2 ^ (j + 1) ∣ oy)
    (hoys : oy < p.s) (hvb : c.rreg 300 = rmF c.rmem p (c.nreg 315) (c.nreg 312))
    (hb1 : c.nreg 313 ≤ c.nreg 315) (hb2 : c.nreg 315 ≤ c.nreg 314)
    (hin : c.nreg 353 < oy → c.nreg 313 ≤ oy) :
    ∃ c' k, Exec I p.W qY c c' k ∧ k ≤ 25 ∧
      (c'.nreg 354 = (if oy + 2 ^ j ≤ c.nreg 314 then oy + 2 ^ j else oy) ∧
        c'.nreg 356 = gapAt c.nmem p j (c'.nreg 354) (c.nreg 312) ∧
        StepOK (rmF c.rmem p) (c.nreg 312) (c.nreg 313) (c.nreg 314) c c' ∧
        (oy + 2 ^ j ≤ c.nreg 314 → c.nreg 353 < oy → ∀ ρ, oy ≤ ρ → ρ < oy + 2 ^ j →
          rmF c.rmem p (c'.nreg 315) (c.nreg 312) ≤ rmF c.rmem p ρ (c.nreg 312)) ∧
        KX c c' ∧ c'.nreg 353 = c.nreg 353 ∧ c'.nreg 355 = c.nreg 355 ∧ KR 300 303 c c' ∧
        c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hW := W_bound hL
  have hcb := cell_bound (p := p) (j := j) (by omega)
  have e3 := cell_eq (p := p) j 3 0
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have hds := off_le hoy (pow_dvd_s hj) hoys
  generalize hσ' : c.nreg 312 = σ at hσ hvb h256 ⊢
  obtain ⟨-, hnode⟩ := hB (j + 1) hj oy hoy hoys
  obtain ⟨-, hcasc⟩ := hnode σ hσ
  obtain ⟨eGL, eGR⟩ := hcasc j rfl
  have hdl : 2 ^ j ∣ oy := dvd_trans (pow_dvd_pow 2 (Nat.le_succ j)) hoy
  obtain ⟨-, hnl⟩ := hB j (by omega) oy hdl hoys
  obtain ⟨hminl, -⟩ := hnl σ hσ
  have ht := gapAt_lt c.nmem (p := p) j oy σ
  have hgl := gapAt_lt c.nmem (p := p) (j + 1) oy σ
  have hcb1 := cell_bound (p := p) (j := j + 1) hj
  have e1 := cell_eq (p := p) (j + 1) 1 (oy + c.nreg 356)
  have e0 := cell_succ (p := p) j 0 0
  generalize hg : gapAt c.nmem p (j + 1) oy σ = g at h256 eGL eGR hgl
  have hGL : c.nmem (c.nreg 361) = gapAt c.nmem p j oy σ := by
    rw [h261, h256]; exact eGL
  have hGR : c.nmem (c.nreg 361 + c.nreg 301) = gapAt c.nmem p j (oy + 2 ^ j) σ := by
    rw [h261, h256, hR.r301, show cell p (j + 1) 1 (oy + g) + p.s = cell p (j + 1) 2 (oy + g) by
      unfold cell; ring]
    exact eGR
  have hrow : c.nmem (cell p j 3 0 + oy + gapAt c.nmem p j oy σ) = Arr c.nmem p j 3 oy
      (gapAt c.nmem p j oy σ) := by
    unfold Arr; congr 1; unfold cell; ring
  unfold qY
  by_cases hleft : c.nreg 314 < oy + 2 ^ j
  · refine spec_ifLtN_true (by rw [h264]; exact hleft) ?_
    have hnl : ¬ oy + 2 ^ j ≤ c.nreg 314 := by omega
    refine spec_instr (Exec.loadN hc 356 361) fun hw' => ?_
    refine ⟨by omega, by config_simp; rw [h254]; simp only [hnl, ↓reduceIte],
      by config_simp; rw [h254]; exact hGL,
      ⟨by config_simp; exact hb1, by config_simp; exact hb2, by config_simp; exact hvb,
        by config_simp; exact le_rfl⟩, fun h => absurd h hnl,
      fun r a1 a2 a3 a4 a5 a6 a7 a8 => ?_, by config_simp, by config_simp,
      fun r hr => rfl, rfl, rfl, rfl⟩
    config_simp; upd_tac
  · refine spec_ifLtN_false (by rw [h264]; exact hleft) ?_
    have hr' : oy + 2 ^ j ≤ c.nreg 314 := by omega
    unfold qRy
    refine spec_seq ?_
    exec_block
    · config_simp; rw [hR.r301]; omega
    · config_simp; rw [h259, h254]; omega
    · config_simp; rw [h259, h254, hGL]; omega
    refine spec_seq ?_
    have hfin : ∀ c₂ : Config, WordsBounded p.W c₂ →
        (∀ r, r ≠ 356 → r ≠ 361 → r ≠ 362 → r ≠ 363 → (r < 315 ∨ 320 ≤ r) →
          c₂.nreg r = c.nreg r) → c₂.nreg 356 = gapAt c.nmem p j (oy + 2 ^ j) σ →
        KR 300 303 c c₂ → c₂.nmem = c.nmem → c₂.rmem = c.rmem → c₂.output = c.output →
        StepOK (rmF c.rmem p) σ (c.nreg 313) (c.nreg 314) c c₂ →
        (c.nreg 353 < oy → ∀ ρ, oy ≤ ρ → ρ < oy + 2 ^ j →
          rmF c.rmem p (c₂.nreg 315) σ ≤ rmF c.rmem p ρ σ) →
        ∃ c' k', Exec I p.W (.instr (.copyN 354 364)) c₂ c' k' ∧ k' = 1 ∧
          (c'.nreg 354 = (if oy + 2 ^ j ≤ c.nreg 314 then oy + 2 ^ j else oy) ∧
            c'.nreg 356 = gapAt c.nmem p j (c'.nreg 354) σ ∧
            StepOK (rmF c.rmem p) σ (c.nreg 313) (c.nreg 314) c c' ∧
            (oy + 2 ^ j ≤ c.nreg 314 → c.nreg 353 < oy → ∀ ρ, oy ≤ ρ → ρ < oy + 2 ^ j →
              rmF c.rmem p (c'.nreg 315) σ ≤ rmF c.rmem p ρ σ) ∧
            KX c c' ∧ c'.nreg 353 = c.nreg 353 ∧ c'.nreg 355 = c.nreg 355 ∧ KR 300 303 c c' ∧
            c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
      intro c₂ hw₂ hKN h256' hKR hn hrm ho hS hcov
      have k264 : c₂.nreg 364 = oy + 2 ^ j := (hKN 364 (by omega) (by omega) (by omega) (by omega)
        (by omega)).trans h264
      refine ⟨_, 1, Exec.copyN hw₂ 354 364, rfl, by config_simp; rw [k264]; simp only [hr',
        ↓reduceIte], ?_, ?_, fun _ => ?_, fun r a1 a2 a3 a4 a5 a6 a7 a8 => ?_, ?_, ?_,
        fun r hr => by
          config_simp; exact hKR r hr, hn, hrm, ho⟩
      · config_simp; rw [k264, h256']
      · obtain ⟨s1, s2, s3, s4⟩ := hS
        exact ⟨by config_simp; exact s1, by config_simp; exact s2, by config_simp; exact s3,
          by config_simp; exact s4⟩
      · config_simp; exact hcov
      · config_simp; simp only [upd_apply, a2, ↓reduceIte]; exact hKN r a4 a5 a6 a7 a8
      · config_simp; exact hKN 353 (by omega) (by omega) (by omega) (by omega) (by omega)
      · config_simp; exact hKN 355 (by omega) (by omega) (by omega) (by omega) (by omega)
    by_cases hlt : c.nreg 353 < oy
    · refine spec_ifLtN_true (by config_simp; rw [h254]; exact hlt) ?_
      have := hin hlt
      refine spec_use (qCand_use (I := I) (lo := oy) (hi := oy + 2 ^ j) hL _ ‹_›
        (hR.of fun r h1 h2 => by config_simp; upd_tac) (by config_simp; rw [hσ']; exact hσ)
        (by config_simp; rw [hσ', h259, h254, hGL, hrow]; exact hminl)
        (by config_simp; omega) (by config_simp; omega) (by config_simp; rw [hσ']; exact hvb)
        (by config_simp; exact hb1) (by config_simp; exact hb2)) ?_
      intro c₂ k₂ hk₂ hw₂ ⟨hS, hcov, hKN, hKR, hn, hrm, ho⟩
      config_simp at hS; config_simp at hcov; config_simp at hn; config_simp at hrm
      config_simp at ho; rw [hσ'] at hS hcov
      obtain ⟨c', k', e, hk', hpost⟩ := hfin c₂ hw₂
        (fun r a1 a2 a3 a4 a5 => by rw [hKN r a5]; config_simp; upd_tac)
        (by rw [hKN 356 (by omega)]; config_simp; exact hGR)
        (fun r hr => (hKR r hr).trans (by config_simp)) hn hrm ho hS (fun _ => hcov)
      exact ⟨c', k', e, by omega, hpost⟩
    · refine spec_ifLtN_false (by config_simp; rw [h254]; exact hlt) ?_
      refine spec_skip ‹_› ?_
      obtain ⟨c', k', e, hk', hpost⟩ := hfin _ ‹_›
        (fun r a1 a2 a3 a4 a5 => by config_simp; upd_tac) (by config_simp; exact hGR)
        (fun r hr => by config_simp) (by config_simp) (by config_simp) (by config_simp)
        ⟨by config_simp; exact hb1, by config_simp; exact hb2, by config_simp; exact hvb,
          by config_simp; exact le_rfl⟩ (fun h => absurd h hlt)
      exact ⟨c', k', e, by omega, hpost⟩

/-! ### The descent -/

/-- **The state of the descent** at the height `j` (node size `2 ^ j`), from the configuration
`c₀`: the nodes of the paths (`r353`, `r354`), the gaps of the source there (`r355`, `r356`),
the best row `r315` so far with its value (`r300`), the base `r357` of the level. -/
structure IQ (p : RMP) (c₀ c : Config) (j : ℕ) : Prop where
  wb : WordsBounded p.W c
  keep : ∀ r, (r < 315 ∨ 370 ≤ r) → c.nreg r = c₀.nreg r
  rr : KR 300 310 c₀ c
  nm : c.nmem = c₀.nmem
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
  jT : j ≤ p.T
  n : c.nreg 352 = 2 ^ j
  lc : c.nreg 357 = cell p j 0 0
  q : QCov (rmF c₀.rmem p) (c₀.nreg 312) (c₀.nreg 313) (c₀.nreg 314) (2 ^ j) (c.nreg 353)
    (c.nreg 354) (c.nreg 315)
  vb : c.rreg 300 = rmF c₀.rmem p (c.nreg 315) (c₀.nreg 312)
  gx : c.nreg 355 = gapAt c₀.nmem p j (c.nreg 353) (c₀.nreg 312)
  gy : c.nreg 356 = gapAt c₀.nmem p j (c.nreg 354) (c₀.nreg 312)
  dx : 2 ^ j ∣ c.nreg 353
  dy : 2 ^ j ∣ c.nreg 354

set_option maxHeartbeats 1000000 in
theorem qBody_exec (hL : RMLay p) {c₀ : Config} (hR₀ : RCtx p c₀) (hσ : c₀.nreg 312 < p.nc)
    (h2s : c₀.nreg 314 < p.s) (hB : Built (rmF c₀.rmem p) p c₀.nmem) {j : ℕ} (c : Config)
    (hI : IQ p c₀ c j) (hlt : c.nreg 308 < c.nreg 352) :
    ∃ j' c' k, Exec I p.W qBody c c' k ∧ IQ p c₀ c' j' ∧ 63 * j' + k + 2 ≤ 63 * j := by
  have hc := hI.wb
  have hR : RCtx p c := hR₀.of fun r h1 h2 => hI.keep r (by omega)
  have hW := W_bound hL
  have g212 : c.nreg 312 = c₀.nreg 312 := hI.keep 312 (by omega)
  have g213 : c.nreg 313 = c₀.nreg 313 := hI.keep 313 (by omega)
  have g214 : c.nreg 314 = c₀.nreg 314 := hI.keep 314 (by omega)
  have hBc : Built (rmF c.rmem p) p c.nmem := by rw [hI.nm, hI.rm]; exact hB
  have hn := hI.n
  rw [hR.r308, hn] at hlt
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp at hlt
    · omega⟩
  have hjT := hI.jT
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  obtain ⟨x1, x2, y1, y2, dxy, dyx, b1, b2, cov⟩ := hI.q
  generalize hox : c.nreg 353 = ox at x1 x2 dxy dyx
  generalize hoy : c.nreg 354 = oy at y1 y2 dxy dyx
  have hdx : 2 ^ (j + 1) ∣ ox := hox ▸ hI.dx
  have hdy : 2 ^ (j + 1) ∣ oy := hoy ▸ hI.dy
  have hoxs : ox < p.s := by omega
  have hoys : oy < p.s := by omega
  have hdsx := off_le hdx (pow_dvd_s hjT) hoxs
  have hdsy := off_le hdy (pow_dvd_s hjT) hoys
  have hgyc := gapAt_lt c.nmem (p := p) (j + 1) oy (c.nreg 312)
  have hgxc := gapAt_lt c.nmem (p := p) (j + 1) ox (c.nreg 312)
  have hgx := gapAt_lt c₀.nmem (p := p) (j + 1) ox (c₀.nreg 312)
  have hgy := gapAt_lt c₀.nmem (p := p) (j + 1) oy (c₀.nreg 312)
  have hcb := cell_bound (p := p) (j := j + 1) hjT
  have e0 := cell_succ (p := p) j 0 0
  have e3 := cell_eq (p := p) j 3 0
  have e2 := cell_eq (p := p) (j + 1) 2 (ox + c.nreg 355)
  have e1 := cell_eq (p := p) (j + 1) 1 (oy + c.nreg 356)
  have hlc := hI.lc
  have hgx' : c.nreg 355 = gapAt c.nmem p (j + 1) ox (c.nreg 312) := by
    rw [hI.gx, hI.nm, g212, hox]
  have hgy' : c.nreg 356 = gapAt c.nmem p (j + 1) oy (c.nreg 312) := by
    rw [hI.gy, hI.nm, g212, hoy]
  have hvb : c.rreg 300 = rmF c.rmem p (c.nreg 315) (c.nreg 312) := by rw [hI.vb, hI.rm, g212]
  have hpd : c.nreg 352 / 2 = 2 ^ j := by rw [hn, hpow]; omega
  refine ⟨j, ?_⟩
  unfold qBody
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hR.r309, hpd, hox]; omega
  · config_simp; rw [hR.r301, hlc]; omega
  · config_simp; rw [hR.r301, hlc]; omega
  · config_simp; rw [hR.r301, hlc, hox]; omega
  · config_simp; rw [hR.r301, hlc, hox, hgx']; rw [hI.nm, g212] at *; omega
  refine spec_seq ?_
  refine spec_use (qX_exec (I := I) (j := j) (ox := ox) (oy := oy) hL _ ‹_›
    (hR.of fun r h1 h2 => by config_simp; upd_tac) (by config_simp; rw [g212]; exact hσ)
    (by config_simp; exact hBc) (by omega) (by config_simp; exact hox) (by config_simp; exact hoy)
    (by config_simp; rw [hR.r301, hlc]; omega) (by config_simp; rw [hR.r309, hpd, hox])
    (by config_simp; exact hgx') (by config_simp; rw [hR.r301, hlc, hox]; omega) hdx hoxs
    (by config_simp; exact hvb) (by config_simp; rw [g213]; exact b1)
    (by config_simp; rw [g214]; exact b2) dxy (by config_simp; rw [g214]; exact y1)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨X1, X2, XS, Xc, XK, X254, X256, XR, Xn, Xrm, Xo⟩
  config_simp at X1; config_simp at X2; config_simp at XS; config_simp at Xc
  config_simp at X254; config_simp at X256; config_simp at Xn; config_simp at Xrm
  config_simp at Xo
  have k : ∀ r, r ≠ 353 → r ≠ 354 → r ≠ 355 → r ≠ 356 → r ≠ 361 → r ≠ 362 → r ≠ 363 →
      (r < 315 ∨ 320 ≤ r) → r ≠ 358 → r ≠ 359 → r ≠ 360 → c₁.nreg r = c.nreg r := by
    intro r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    rw [XK r a1 a2 a3 a4 a5 a6 a7 a8]; config_simp; upd_tac
  have k258 : c₁.nreg 358 = 2 ^ j := by
    rw [XK 358 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; config_simp; rw [hR.r309, hpd]
  have k259 : c₁.nreg 359 = cell p j 3 0 := by
    rw [XK 359 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; config_simp; rw [hR.r301, hlc]; omega
  have k257 : c₁.nreg 357 = cell p (j + 1) 0 0 := (k 357 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
    hlc
  have k201 : c₁.nreg 301 = p.s := (k 301 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hR.r301
  have kr : ∀ r, (r < 315 ∨ 370 ≤ r) → c₁.nreg r = c.nreg r := fun r hr =>
    k r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hσ1 : c₁.nreg 312 = c.nreg 312 := kr 312 (by omega)
  have hj1 : c₁.nreg 313 = c.nreg 313 := kr 313 (by omega)
  have hj2 : c₁.nreg 314 = c.nreg 314 := kr 314 (by omega)
  have hgy1 : c₁.nreg 356 = c.nreg 356 := X256
  rw [g212] at X2 XS Xc
  refine spec_seq ?_
  exec_block
  · rw [X254, k258, hoy]; omega
  · config_simp; rw [k257, k201]; omega
  · config_simp; rw [k257, k201, X254, hoy]; omega
  · config_simp; rw [k257, k201, X254, hoy, hgy1, hgy']; omega
  refine spec_seq ?_
  have hR1 : RCtx p c₁ := hR.of fun r h1 h2 => kr r (by omega)
  refine spec_use (qY_exec (I := I) (j := j) (oy := oy) hL _ ‹_›
    (hR1.of fun r h1 h2 => by config_simp; upd_tac) (by config_simp; rw [hσ1, g212]; exact hσ)
    (by config_simp; rw [Xn, Xrm]; exact hBc) (by omega) (by config_simp; rw [X254, hoy])
    (by config_simp; exact k259) (by config_simp; rw [X254, k258, hoy])
    (by config_simp; rw [hgy1, hσ1, Xn, hgy'])
    (by config_simp; rw [k257, k201, X254, hoy, hgy1]; omega) hdy hoys
    (by config_simp; rw [Xrm, hσ1, g212]; exact XS.2.2.1)
    (by config_simp; rw [hj1]; exact XS.1) (by config_simp; rw [hj2]; exact XS.2.1)
    (by config_simp; rw [hj1, X1]; intro h; split_ifs at h <;> omega)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨Y1, Y2, YS, Yc, YK, Y253, Y255, YR, Yn, Yrm, Yo⟩
  config_simp at Y1; config_simp at Y2; config_simp at YS; config_simp at Yc
  config_simp at Y253; config_simp at Y255; config_simp at Yn; config_simp at Yrm
  config_simp at Yo
  have hq := hI.q
  rw [hox, hoy, hpow] at hq
  simp only [Xrm, hI.rm, hσ1, g212, hj1, g213, hj2, g214] at YS Yc
  simp only [hj2, g214] at Y1
  simp only [hσ1, g212, Xn, hI.nm] at Y2
  simp only [hI.rm, g213, g214] at XS Xc
  simp only [g213] at X1
  simp only [hI.nm] at X2
  have v258 : c₂.nreg 358 = 2 ^ j := by
    rw [YK 358 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; config_simp; exact k258
  have v257 : c₂.nreg 357 = cell p (j + 1) 0 0 := by
    rw [YK 357 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; config_simp; exact k257
  have v211 : c₂.nreg 311 = 4 * p.s := by
    rw [YK 311 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; config_simp; rw [kr 311 (by omega)]; exact hR.r311
  have vk : ∀ r, (r < 315 ∨ 370 ≤ r) → c₂.nreg r = c₀.nreg r := fun r hr => by
    rw [YK r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; config_simp
    simp only [upd_apply, show r ≠ 364 by omega, show r ≠ 361 by omega, ↓reduceIte]
    rw [kr r hr]; exact hI.keep r hr
  have v253 : c₂.nreg 353 = if ox + 2 ^ j ≤ c₀.nreg 313 then ox + 2 ^ j else ox := by
    rw [Y253]; exact X1
  have hstep := QCov.step (b' := c₂.nreg 315) hq YS.1 YS.2.1 (YS.2.2.2.trans XS.2.2.2)
    (fun h1 h2 ρ r1 r2 => YS.2.2.2.trans (Xc h1 h2 ρ r1 r2))
    (fun h1 h2 ρ r1 r2 => Yc h1 (by rw [X1]; split_ifs <;> omega) ρ r1 r2)
  rw [← v253, ← Y1] at hstep
  exec_block
  refine ⟨⟨by assumption, fun r hr => by config_simp; rw [← vk r hr]; upd_tac,
    fun r hr => ?_, by config_simp; rw [Yn, Xn, hI.nm], by config_simp; rw [Yrm, Xrm, hI.rm],
    by config_simp; rw [Yo, Xo, hI.out], by omega, by config_simp; exact v258,
    by config_simp; rw [v257, v211, e0]; omega, by config_simp; exact hstep,
    by config_simp; rw [YS.2.2.1], ?_, by config_simp; exact Y2, ?_, ?_⟩,
    by omega⟩
  · config_simp
    rw [YR r (by omega)]; config_simp; rw [XR r (by omega)]; exact hI.rr r hr
  · config_simp; rw [Y255, Y253]; exact X2
  · have : 2 ^ j ∣ ox := dvd_trans (pow_dvd_pow 2 (Nat.le_succ j)) hdx
    config_simp; rw [v253]; split_ifs
    · exact dvd_add this dvd_rfl
    · exact this
  · have : 2 ^ j ∣ oy := dvd_trans (pow_dvd_pow 2 (Nat.le_succ j)) hdy
    config_simp; rw [Y1]; split_ifs
    · exact dvd_add this dvd_rfl
    · exact this

/-! ### The query -/

set_option maxHeartbeats 1000000 in
/-- **The query.** On a built structure, for the source `σ = r312 < nc` and the rows
`[j1, j2] = [r313, r314]` (`j1 ≤ j2 < s`), `rmQuery` puts in `r315` a row minimising the matrix
over `[j1, j2]` and in the real `r300` its value, within `80 T + 80` steps. It writes only the
natural registers `r308 … r369` and the real registers `r300 … r309`, and no memory. -/
theorem rmQuery_exec (hL : RMLay p) (c : Config) (hc : WordsBounded p.W c) (hP : RPar p c)
    (hB : Built (rmF c.rmem p) p c.nmem) (hσ : c.nreg 312 < p.nc)
    (h12 : c.nreg 313 ≤ c.nreg 314) (h2 : c.nreg 314 < p.s) :
    ∃ c' k, Exec I p.W rmQuery c c' k ∧ k ≤ 80 * p.T + 80 ∧
      (IsArgmin (rmF c.rmem p) (c.nreg 312) (c.nreg 313) (c.nreg 314 + 1) (c'.nreg 315) ∧
        c'.rreg 300 = rmF c.rmem p (c'.nreg 315) (c.nreg 312) ∧
        (∀ r, (r < 308 ∨ 370 ≤ r) → c'.nreg r = c.nreg r) ∧ KR 300 310 c c' ∧
        c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hW := W_bound hL
  have hcb := cell_bound (p := p) (j := p.T) le_rfl
  have hs1 := hL.s_pos
  have hTs := hL.T_lt
  have hcT : cell p p.T 0 0 = p.T * (4 * p.s) + p.B := by unfold cell; ring
  have hTs' : p.T * (4 * p.s) ≤ cell p p.T 0 0 := by omega
  obtain ⟨-, hroot⟩ := hB p.T le_rfl 0 (dvd_zero _) (by omega)
  have hlok := (hB p.T le_rfl 0 (dvd_zero _) (by omega)).1
  unfold rmQuery
  refine spec_seq ?_
  refine spec_use (rmSetup_exec (I := I) hL c hc hP) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hR1, hK1, hrr1, hn1, hrm1, ho1⟩
  have k1 : ∀ r, (r < 308 ∨ 312 ≤ r) → c₁.nreg r = c.nreg r := hK1
  refine spec_seq ?_
  exec_block
  · rw [hR1.r307, hR1.r311]; omega
  · config_simp; rw [hR1.r307, hR1.r311, hR1.r300]; omega
  refine spec_seq ?_
  have hsd : p.s = 2 ^ p.T := rfl
  have hlg : lg (p.s - 1) ≤ p.T := lg_lt_pow (by rw [← hsd]; omega)
  have hf : ∀ e < p.s - 1, c₁.nmem (p.T * (4 * p.s) + p.B + e) = Arr c.nmem p p.T 0 0 e := by
    intro e he; rw [hn1, ← hcT]; unfold Arr; congr 1; unfold cell; ring
  refine spec_use (rmCnt_exec (I := I) (f := Arr c.nmem p p.T 0 0) (n := p.s - 1) _ ‹_›
    (hR1.of fun r h1 h2 => by config_simp; upd_tac) (hlok.1.mono (n' := p.s - 1) (by omega))
    (fun e he => by config_simp; rw [hR1.r307, hR1.r311, hR1.r300]; exact hf e he)
    (by config_simp; rw [hR1.r301, hR1.r308])
    (by config_simp; rw [hR1.r307, hR1.r311, hR1.r300]; omega)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨e2, hK2, hrr2, hn2, hrm2, ho2⟩
  config_simp at e2; config_simp at hrr2; config_simp at hn2; config_simp at hrm2
  config_simp at ho2
  have k2' : ∀ r, (r < 320 ∨ 327 ≤ r) → r ≠ 357 → c₂.nreg r = c₁.nreg r := fun r h1 h2 => by
    rw [hK2 r (by omega)]; config_simp; upd_tac
  have k2 : ∀ r, (r < 308 ∨ (312 ≤ r ∧ r < 320) ∨ 327 ≤ r) → r ≠ 357 → c₂.nreg r = c.nreg r :=
    fun r h1 h2 => (k2' r (by omega) h2).trans (k1 r (by omega))
  have v257 : c₂.nreg 357 = cell p p.T 0 0 := by
    rw [hK2 357 (by omega)]; config_simp; rw [hR1.r307, hR1.r311, hR1.r300, hcT]
  have hR2 : RCtx p c₂ := hR1.of fun r h1 h2 => k2' r (by omega) (by omega)
  rw [k1 312 (by omega)] at e2
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  refine spec_seq ?_
  refine spec_use (rmEv_exec (I := I) hL _ ‹_› (hR2.of fun r h1 h2 => by config_simp; upd_tac)
    (by config_simp; rw [k2 312 (by omega) (by omega)]; exact hσ)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨e3, hK3, hR3, hn3, hrm3, ho3⟩
  config_simp at e3; config_simp at hn3; config_simp at hrm3; config_simp at ho3
  rw [k2 312 (by omega) (by omega), k2 313 (by omega) (by omega), hrm2, hrm1] at e3
  refine spec_seq ?_
  refine spec_instr (Exec.copyR ‹_› 300 301) fun hw₄ => ?_
  refine spec_seq ?_
  generalize hc4 : ({ c₃ with rreg := upd c₃.rreg 300 (c₃.rreg 301) } : Config) = c₄ at hw₄ ⊢
  have f4n : c₄.nreg = c₃.nreg := by rw [← hc4]
  have f4r : c₄.rreg 300 = c₃.rreg 301 := by rw [← hc4]; config_simp
  have f4r' : ∀ r, r ≠ 300 → c₄.rreg r = c₃.rreg r := fun r hr => by
    rw [← hc4]; config_simp; upd_tac
  have f4m : c₄.nmem = c.nmem := by rw [← hc4]; config_simp; rw [hn3, hn2, hn1]
  have f4rm : c₄.rmem = c.rmem := by rw [← hc4]; config_simp; rw [hrm3, hrm2, hrm1]
  have f4o : c₄.output = c.output := by rw [← hc4]; config_simp; rw [ho3, ho2, ho1]
  have k3 : ∀ r, (r < 315 ∨ (320 ≤ r ∧ r < 352) ∨ 358 ≤ r) → c₃.nreg r = c₂.nreg r :=
    fun r hr => by rw [hK3 r (by omega)]; config_simp; upd_tac
  have hR3' : RCtx p c₃ := hR2.of fun r h1 h2 => k3 r (by omega)
  have v : c₃.nreg 352 = p.s ∧ c₃.nreg 353 = 0 ∧ c₃.nreg 354 = 0 ∧
      c₃.nreg 355 = cntP (Arr c.nmem p p.T 0 0) (p.s - 1) (c.nreg 312) ∧
      c₃.nreg 356 = cntP (Arr c.nmem p p.T 0 0) (p.s - 1) (c.nreg 312) ∧
      c₃.nreg 357 = cell p p.T 0 0 ∧ c₃.nreg 315 = c.nreg 313 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hK3 _ (by omega)] <;> config_simp
    · exact hR2.r301
    · exact e2
    · exact e2
    · exact v257
    · exact k2 313 (by omega) (by omega)
  obtain ⟨v252, v253, v254, v255, v256, v257', v215⟩ := v
  have kk : ∀ r, (r < 308 ∨ (312 ≤ r ∧ r < 315) ∨ 370 ≤ r) → c₄.nreg r = c.nreg r :=
    fun r hr => by rw [f4n, k3 r (by omega), k2 r (by omega) (by omega)]
  have hR4 : RCtx p c₄ := hR3'.of fun r h1 h2 => by rw [f4n]
  have hIQ : IQ p c₄ c₄ p.T := by
    refine ⟨hw₄, fun r _ => rfl, fun r _ => rfl, rfl, rfl, rfl, le_rfl, by rw [f4n, v252]; rfl,
      by rw [f4n, v257'], ?_, ?_, ?_, ?_, by rw [f4n, v253]; exact dvd_zero _,
      by rw [f4n, v254]; exact dvd_zero _⟩
    · rw [f4n, v253, v254, v215, ← f4n, kk 313 (by omega), kk 314 (by omega)]
      exact QCov.init h12 h2
    · rw [f4r, e3, f4rm, f4n, v215, ← f4n, kk 312 (by omega)]
    · rw [f4n, v255, v253, ← f4n, kk 312 (by omega), f4m]; rfl
    · rw [f4n, v256, v254, ← f4n, kk 312 (by omega), f4m]; rfl
  obtain ⟨jf, c₅, k₅, e5, hI5, hn5, hk5⟩ := Exec.whileLtN_ghost (P := I) (W := p.W) (a := 308)
    (b := 352) (body := qBody) (fun j c' => IQ p c₄ c' j) (fun j _ => 63 * j)
    (fun _ _ h => h.wb)
    (fun j c' hI' hlt => qBody_exec hL hR4 (by rw [kk 312 (by omega)]; exact hσ)
      (by rw [kk 314 (by omega)]; exact h2) (by rw [f4m, f4rm]; exact hB) c' hI' hlt) hIQ
  refine ⟨c₅, k₅, e5, ?_⟩
  have hR5 : RCtx p c₅ := hR4.of fun r h1 h2 => hI5.keep r (by omega)
  have hjf : jf = 0 := by
    rw [hR5.r308, hI5.n] at hn5
    by_contra h
    have : 2 ≤ 2 ^ jf := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ jf := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  subst hjf
  have hq := hI5.q
  rw [pow_zero] at hq
  have g5 : ∀ r, (r < 308 ∨ (312 ≤ r ∧ r < 315) ∨ 370 ≤ r) → c₅.nreg r = c.nreg r :=
    fun r hr => (hI5.keep r (by omega)).trans (kk r hr)
  simp only [kk 312 (by omega), kk 313 (by omega), kk 314 (by omega), f4rm] at hq
  have hvb5 : c₅.rreg 300 = rmF c.rmem p (c₅.nreg 315) (c.nreg 312) := by
    rw [hI5.vb, f4rm, kk 312 (by omega)]
  have hw₅ : WordsBounded p.W c₅ := hI5.wb
  refine spec_seq ?_
  exec_block
  refine spec_seq ?_
  refine spec_use (rmEv_exec (I := I) hL _ ‹_› (hR5.of fun r h1 h2 => by config_simp; upd_tac)
    (by config_simp; rw [g5 312 (by omega)]; exact hσ)) ?_
  intro c₆ k₆ hk₆ hw₆ ⟨e6, hK6, hR6, hn6, hrm6, ho6⟩
  config_simp at e6; config_simp at hn6; config_simp at hrm6; config_simp at ho6
  rw [g5 312 (by omega), g5 314 (by omega), hI5.rm, f4rm] at e6
  have k6 : ∀ r, (r < 316 ∨ 320 ≤ r) → c₆.nreg r = c₅.nreg r := fun r hr => by
    rw [hK6 r (by omega)]; config_simp; upd_tac
  have hR6' : ∀ r, (r < 301 ∨ 303 ≤ r) → c₆.rreg r = c₅.rreg r := fun r hr => hR6 r hr
  have hfr : ∀ r, (r < 300 ∨ 310 ≤ r) → c₅.rreg r = c.rreg r := fun r hr => by
    rw [hI5.rr r hr, f4r' r (by omega), hR3 r (by omega)]; config_simp
    rw [hrr2, hrr1]
  have hfn : ∀ r, (r < 308 ∨ 370 ≤ r) → c₅.nreg r = c.nreg r := fun r hr => g5 r (by omega)
  have hmem : c₆.nmem = c.nmem := by rw [hn6, hI5.nm, f4m]
  have hrmem : c₆.rmem = c.rmem := by rw [hrm6, hI5.rm, f4rm]
  have hout : c₆.output = c.output := by rw [ho6, hI5.out, f4o]
  have v216 : c₆.nreg 316 = c.nreg 314 := by
    rw [hK6 316 (by omega)]; config_simp; exact g5 314 (by omega)
  have v215 : c₆.nreg 315 = c₅.nreg 315 := k6 315 (by omega)
  by_cases hlt6 : c₆.rreg 301 < c₆.rreg 300
  · refine spec_ifLtR_true hlt6 ?_
    exec_block
    rw [e6, hR6' 300 (by omega), hvb5] at hlt6
    refine ⟨by omega, QCov.final hq (Or.inr (by config_simp; rw [v216]))
        (by config_simp; rw [v216]; exact hlt6.le) (by config_simp; rw [v216]),
      by config_simp; rw [v216, e6], fun r hr => ?_, fun r hr => ?_, by config_simp; exact hmem,
      by config_simp; exact hrmem, by config_simp; exact hout⟩
    · config_simp; simp only [upd_apply, show r ≠ 315 by omega, ↓reduceIte]
      rw [k6 r (by omega), hfn r hr]
    · config_simp; simp only [upd_apply, show r ≠ 300 by omega, ↓reduceIte]
      rw [hR6' r (by omega), hfr r hr]
  · refine spec_ifLtR_false hlt6 ?_
    rw [e6, hR6' 300 (by omega), hvb5] at hlt6
    refine spec_skip ‹_› ⟨by omega, QCov.final hq (Or.inl v215) (by rw [v215]) (by
        rw [v215]; exact not_lt.1 hlt6), by rw [hR6' 300 (by omega), hvb5, v215],
      fun r hr => by rw [k6 r (by omega), hfn r hr],
      fun r hr => by rw [hR6' r (by omega), hfr r hr],
      hmem, hrmem, hout⟩

end RM

end Monge

end PlanarFlow
