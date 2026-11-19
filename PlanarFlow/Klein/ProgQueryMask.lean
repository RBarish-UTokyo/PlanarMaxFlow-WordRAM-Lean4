module

public import PlanarFlow.Klein.ProgQuery

/-!
# Klein's algorithm on the machine: the queries at the flagged moves only

The program `kleinProg` (`PlanarFlow/Klein/ProgTrip.lean`) answers the `t` targets at the start
of each of the `k` moves, `k t` path-sum queries in all. On the cuts on which the maximum-flow
algorithm calls multiple-source shortest paths there is one move per dart leaving the path, so
`k` can be of the order of the size of the piece while only one root per face along the path is
asked for. This file gives the masked query phase of a move: the queries run only when the move
is flagged.

* `kRank fl J`: the number of flagged moves `j < J` (the slot of the answers of a flagged move
  `J` in the output arrays); `kRank_succ`, `kRank_le`, `kRank_mono`, `kRank_succ_le`, `sum_flag`.
* `qMaskS`: `if r107 < r108` (`r107 = 0`, `r108` the flag of the move) the query loop `qLoopS`
  and the slot counter `r82` advanced, else nothing.
* `qMask_orun`: counted `t` operations and `14 t + 5` further steps when the move is flagged,
  no operation and `2` further steps otherwise, with the answers of `qry_orun` when it is.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs

/-! ### The ranks of the flagged moves -/

/-- **The number of flagged moves before `J`**: the slot of the answers of a flagged move `J`
in the output arrays. -/
def kRank (fl : ℕ → Bool) (J : ℕ) : ℕ := ((range J).filter fun j => fl j = true).card

lemma kRank_succ (fl : ℕ → Bool) (J : ℕ) :
    kRank fl (J + 1) = kRank fl J + if fl J then 1 else 0 := by
  unfold kRank
  rw [range_add_one, filter_insert]
  by_cases h : fl J = true
  · simp only [h, ↓reduceIte]
    rw [card_insert_of_notMem (by simp)]
  · simp [h]

lemma kRank_mono (fl : ℕ → Bool) {J J' : ℕ} (h : J ≤ J') : kRank fl J ≤ kRank fl J' :=
  card_le_card (filter_subset_filter _ (range_subset_range.2 h))

lemma kRank_le (fl : ℕ → Bool) (J : ℕ) : kRank fl J ≤ J :=
  (card_filter_le _ _).trans (card_range J).le

lemma kRank_succ_le (fl : ℕ → Bool) {j J : ℕ} (h : j < J) (hj : fl j = true) :
    kRank fl j + 1 ≤ kRank fl J := by
  have := kRank_mono fl (show j + 1 ≤ J by omega)
  simpa [kRank_succ, hj] using this

/-- The queries of the flagged moves: `t` per flagged move. -/
lemma sum_flag (fl : ℕ → Bool) (k t : ℕ) :
    ∑ j ∈ range k, (if fl j = true then t else 0) = kRank fl k * t := by
  rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul]
  rfl

/-! ### The masked query phase -/

/-- **The masked queries of a move**: when `r107 < r108` (`r107 = 0`, `r108` the flag of the
move), the query loop and the slot counter `r82` advanced; otherwise nothing. -/
def qMaskS (B nD n k t : ℕ) : Stmt :=
  .ifLtN 107 108 (.seq (qLoopS B nD n k t) (block [.constN 92 1, .addN 82 82 92])) .skip

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {nD : ℕ} {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ}
  {ιe : D → ℕ}

section
variable {P : Input} {W B : ℕ}

/-- **The masked queries of a move**: when the flag `b` is set, the `t` answers of `qry_orun`
(counted `t` operations and `14 t + 5` further steps) and the slot counter advanced; otherwise
no operation and two further steps. -/
theorem qMask_orun (hW : B + 16 * (n + 1) ≤ W) {k t : ℕ} (hWa : iXT nD n k + 2 * t ≤ W)
    (hP : ∀ i, P.data.getD i 0 ≤ W) (hL : Layout M n ιv ιg ιf ιe) {X : ℕ → V} {xb : ℕ → ℕ}
    (hX : ∀ i < t, P.data.getD (iXT nD n k + i) 0 = ιv (X i))
    (hXb : ∀ i < t, P.data.getD (iXT nD n k + t + i) 0 = xb i) {base rbase : ℕ}
    (b : Bool) (hbase : b = true → base + t ≤ B) (hrbase : b = true → rbase + t ≤ B)
    {c : Config} (hc : WordsBounded W c)
    {F₀ : Forest} {G : List VT} (hS : LCTE B n F₀ G c) (h104 : c.nreg 104 = 0)
    (h105 : c.nreg 105 = t) (h106 : c.nreg 106 = base) (h109 : c.nreg 109 = rbase)
    (h107 : c.nreg 107 = 0) (h108 : c.nreg 108 = if b then 1 else 0) {q : ℕ}
    (h82 : c.nreg 82 = q) (hq : q + 1 ≤ W) :
    ∃ c' G', ORun P W B n (qMaskS B nD n k t) c F₀ G c' [] G' (if b then t else 0)
        (14 * (if b then t else 0) + 5) ∧
      (b = true → ∀ i < t,
        c'.rmem (base + i) = pathSum F₀ n (ιv (X i)) ∧ c'.nmem (rbase + i) = xb i) ∧
      c'.nreg 82 = q + (if b then 1 else 0) ∧
      (∀ r, r < 104 → r ≠ 82 → r ≠ 92 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧
      c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (b = true → a < rbase ∨ rbase + t ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (b = true → a < base ∨ base + t ≤ a) →
        c'.rmem a = c.rmem a) := by
  cases b with
  | false =>
    have o : ORun P W B n (qMaskS B nD n k t) c F₀ G c [] G 0 (0 + 2) :=
      ORun.ifLtN_false (by simp [h107, h108]) ⟨trivial, LRun.skip hc hS⟩
    refine ⟨c, G, o.mono (by simp) (by simp), fun h => absurd h (by simp), by simp [h82],
      fun _ _ _ _ => ⟨rfl, rfl⟩, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  | true =>
    obtain ⟨c₁, G₁, o₁, q₁, rg₁, out₁, nm₁, rm₁, -⟩ := qry_orun (P := P) (k := k) (X := X)
      (xb := xb) hW hWa hP hL hX hXb (hbase rfl) (hrbase rfl) hc hS h104 h105 h106 h109
    have hc₁ := o₁.2.wb
    have p82 : c₁.nreg 82 = q := by rw [(rg₁ 82 (by omega)).1, h82]
    obtain ⟨c₂, k₂, e₂, hk₂, s82, n₂, r₂, mm₂, rm₂, out₂⟩ : ∃ c' k', Exec P W
        (block [.constN 92 1, .addN 82 82 92]) c₁ c' k' ∧ k' = 2 ∧ c'.nreg 82 = q + 1 ∧
        (∀ r, r ≠ 82 → r ≠ 92 → c'.nreg r = c₁.nreg r) ∧ c'.rreg = c₁.rreg ∧
        c'.nmem = c₁.nmem ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
      exec_block
      · omega
      · config_simp; rw [p82]; omega
      · refine ⟨rfl, by config_simp; rw [p82], fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
        config_simp; simp only [upd_other _ _ _ h1, upd_other _ _ _ h2]
    have o₂ : ORun P W B n _ c₁ _ G₁ c₂ [] G₁ 0 k₂ := ORun.glue e₂ o₁.2.lcte
      (fun a _ _ => by rw [mm₂, rm₂]; exact ⟨rfl, rfl⟩) (n₂ 151 (by omega) (by omega))
    have o := ORun.ifLtN_true (e := .skip)
      (show c.nreg 107 < c.nreg 108 by simp [h107, h108]) (o₁.seq o₂)
    try simp only [List.nil_append] at o
    refine ⟨c₂, G₁, o.mono (by simp) (by simp; omega), fun _ i hi => ?_, by simp [s82],
      fun r hr h1 h2 => ?_, by rw [out₂, out₁], fun a ha hb => ?_, fun a ha hb => ?_⟩
    · rw [mm₂, rm₂]; exact q₁ i hi
    · rw [n₂ r h1 h2, r₂]; exact rg₁ r hr
    · rw [mm₂]; exact nm₁ a ha (hb rfl)
    · rw [rm₂]; exact rm₁ a ha (hb rfl)

end

end Klein

end PlanarFlow
