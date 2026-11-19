module

public import PlanarSeparator.Machine.MillerConc
public import PlanarSeparator.Machine.LevelStat

/-!
# Miller's separator on the machine: the thin levels

Step 5 of the plan in `PlanarSeparator/Machine/Miller.lean`. With the levels `L v < n` of the
vertices at `bLv` and the last heavy level `ls < n` in `r180` (`bsearch_exec`), the program
`thin` computes

* `lcnt`: the number `lcF L n l` of vertices of each level `l ≤ 2 n` at `bLC + l`;
* `msqrt`: `t = ⌊√n⌋` in `r201`, by counting;
* `thinJ`, twice, as `findJ` of `PlanarSeparator/Machine/LevelStat.lean` (`thinLoop`): the first
  `j₂` (in `r210`) such that the level `ls + 1 + j₂` has at most `n / (t + 1)` vertices, and the
  first `j₀` (in `r204`) such that the level `ls - t + j₀` has; both are at most `t`, since the
  `t + 1` candidate levels are disjoint (`PlanarSeparator.Map.exists_small_level`).

`thin_exec`: for a breadth-first tree `T` of a plane map with `n` vertices whose levels are in
memory (read through a numbering of the vertices), within `24 n + 16 ⌊√n⌋ + 43` steps,
`r201 = ⌊√n⌋` and `(⌊√n⌋ + 1) #(T.lvl l) ≤ n` at the levels `l = ls + 1 + j₂` and
`l = ls - ⌊√n⌋ + j₀`, as the proof of `PlanarSeparator.Map.exists_short_cycle_separator` chooses
them.

Registers: `r140`, `r141` (`0`, `1`), `r161 = n`, `r163 = bLv`, `r180 = ls`, `r200 = bLC`; the
program writes `r84 … r86`, `r101`, `r201 … r210`.
-/

@[expose] public section

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset SepProg

/-! ### The programs -/

/-- Clear one count `r202`. -/
def lzbody : Stmt := block [.addN 206 200 202, .storeN 206 140, .addN 202 202 141]

/-- Count the vertex `r202`. -/
def lcbody : Stmt := block [.addN 206 163 202, .loadN 205 206, .addN 206 200 205,
  .loadN 205 206, .addN 205 205 141, .storeN 206 205, .addN 202 202 141]

/-- **The sizes of the levels** `l ≤ 2 n`. -/
def lcnt : Stmt :=
  .seq (block [.copyN 202 140, .addN 207 161 161, .addN 207 207 141])
    (.seq (.whileLtN 202 207 lzbody) (.seq (.instr (.copyN 202 140)) (.whileLtN 202 161 lcbody)))

/-- **`⌊√n⌋`** in `r201`. -/
def msqrt : Stmt :=
  .seq (block [.copyN 201 140, .copyN 207 141, .addN 208 161 141])
    (.whileLtN 207 208 (block [.addN 201 201 141, .addN 209 201 141, .mulN 207 209 209]))

/-- `r84 :=` the size of the level `a + j`, `a = r203`, `j = r204`. -/
def tcnt : Stmt := block [.addN 86 203 204, .addN 86 86 200, .loadN 84 86]

/-- **A thin level** from `a = r203`: `j` in `r204`. -/
def thinJ : Stmt :=
  .seq (block [.copyN 101 141, .addN 205 201 141, .divN 85 161 205, .copyN 204 140])
    (thinLoop tcnt 204)

/-- **The thin levels** above and below the last heavy level `r180`. -/
def thin : Stmt :=
  .seq lcnt (.seq msqrt (.seq (.instr (.addN 203 180 141)) (.seq thinJ
    (.seq (.instr (.copyN 210 204)) (.seq (.instr (.subN 203 180 201)) thinJ)))))

section proofs

variable {W : ℕ} {P : Input} {n bLv bLC : ℕ} {L : ℕ → ℕ}

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The sizes of the levels.** -/
theorem lcnt_exec (hlay : bLv + n ≤ bLC) (hW : bLC + 2 * n + 1 ≤ W) (c : Config)
    (hc : WordsBounded W c) (h140 : c.nreg 140 = 0) (h141 : c.nreg 141 = 1)
    (h161 : c.nreg 161 = n) (h163 : c.nreg 163 = bLv) (h200 : c.nreg 200 = bLC)
    (hL : ∀ v < n, c.nmem (bLv + v) = L v) (hLn : ∀ v < n, L v < n) :
    ∃ c' t, Exec P W lcnt c c' t ∧ t ≤ 19 * n + 13 ∧
      (∀ l ≤ 2 * n, c'.nmem (bLC + l) = lcF L n l) ∧
      (∀ r, r < 202 ∨ 208 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bLC ∨ bLC + 2 * n + 1 ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hw₁, h202, h207, hr₁, hm₁, ho₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block
      [.copyN 202 140, .addN 207 161 161, .addN 207 207 141]) c c₁ k₁ ∧ WordsBounded W c₁ ∧
      c₁.nreg 202 = 0 ∧ c₁.nreg 207 = 2 * n + 1 ∧
      (∀ r, r < 202 ∨ 208 ≤ r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.output = c.output ∧ k₁ = 3 := by
    exec_block
    · config_simp; rw [h161]; omega
    · config_simp; rw [h161, h141]; omega
    exact ⟨‹_›, by config_simp; exact h140, by config_simp; rw [h161, h141]; omega,
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl, rfl, rfl⟩
  -- clear the counts
  obtain ⟨c₂, k₂, e₂, ⟨hw₂, -, h207₂, hz₂, hr₂, hf₂, ho₂⟩, hk₂⟩ := Exec.forN (P := P) (W := W)
    (ri := 202) (rN := 207) (N := 2 * n + 1) (lo := 0) (B := 3) (body := lzbody)
    (fun i c' => WordsBounded W c' ∧ c'.nreg 202 = i ∧ c'.nreg 207 = 2 * n + 1 ∧
      (∀ l < i, c'.nmem (bLC + l) = 0) ∧ (∀ r, r < 202 ∨ 208 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bLC ∨ bLC + 2 * n + 1 ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output)
    (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c' ⟨hw, g202, g207, hz, hr, hf, ho⟩ hi => by
      have g200 : c'.nreg 200 = bLC := by rw [hr 200 (by omega)]; exact h200
      have g140 : c'.nreg 140 = 0 := by rw [hr 140 (by omega)]; exact h140
      have g141 : c'.nreg 141 = 1 := by rw [hr 141 (by omega)]; exact h141
      unfold lzbody
      exec_block
      · rw [g200, g202]; omega
      · config_simp; rw [g202, g141]; omega
      refine ⟨⟨‹_›, by config_simp; rw [g202, g141], by config_simp; exact g207,
        fun l hl => ?_, fun r hr' => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr',
        fun a ha => ?_, by config_simp; exact ho⟩, by omega⟩
      · config_simp; rw [g200, g202, g140]
        by_cases hl' : l = i
        · subst hl'; simp
        · rw [upd_other _ _ _ (by omega)]; exact hz l (by omega)
      · config_simp; rw [g200, g202, upd_other _ _ _ (by omega)]; exact hf a ha)
    (by omega) ⟨hw₁, h202, h207, fun l hl => absurd hl (by omega), hr₁,
      fun a _ => by rw [hm₁], ho₁⟩
  have e₃ := Exec.copyN (P := P) hw₂ 202 140
  have hlc_le : ∀ i l, lcF L i l ≤ i := fun i l => (card_le_card (filter_subset _ _)).trans
    (by simp)
  -- count
  obtain ⟨c₄, k₄, e₄, ⟨-, -, -, hc₄, hr₄, hf₄, ho₄⟩, hk₄⟩ := Exec.forN (P := P) (W := W)
    (ri := 202) (rN := 161) (N := n) (lo := 0) (B := 7) (body := lcbody)
    (fun i c' => WordsBounded W c' ∧ c'.nreg 202 = i ∧ c'.nreg 161 = n ∧
      (∀ l ≤ 2 * n, c'.nmem (bLC + l) = lcF L i l) ∧
      (∀ r, r < 202 ∨ 208 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bLC ∨ bLC + 2 * n + 1 ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output)
    (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c' ⟨hw, g202, g161, hcnt, hr, hf, ho⟩ hi => by
      have g200 : c'.nreg 200 = bLC := by rw [hr 200 (by omega)]; exact h200
      have g163 : c'.nreg 163 = bLv := by rw [hr 163 (by omega)]; exact h163
      have g141 : c'.nreg 141 = 1 := by rw [hr 141 (by omega)]; exact h141
      have hLi := hLn i hi
      have mL : c'.nmem (bLv + i) = L i := by rw [hf _ (Or.inl (by omega))]; exact hL i hi
      have mC : c'.nmem (bLC + L i) = lcF L i (L i) := hcnt _ (by omega)
      have hlco : ∀ l, l ≠ L i → lcF L (i + 1) l = lcF L i l := fun l hl => by
        simp [lcF, range_add_one, filter_insert, Ne.symm hl]
      have hlci' : lcF L (i + 1) (L i) = lcF L i (L i) + 1 := by
        simp [lcF, range_add_one, filter_insert]
      have hb := hlc_le i (L i)
      unfold lcbody
      exec_block
      all_goals try (config_simp; (try simp only [g163, g202, mL, g200, mC, g141]); omega)
      rename_i hwb
      simp only [g163, g202, mL, g200, mC, g141] at hwb ⊢
      refine ⟨⟨‹_›, by config_simp; try omega, by config_simp; exact g161,
        fun l hl => ?_, fun r hr' => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr',
        fun a ha => ?_, by config_simp; exact ho⟩, by omega⟩
      · config_simp
        by_cases hl' : l = L i
        · subst hl'; rw [upd_same, hlci']
        · rw [upd_other _ _ _ (by omega), hlco l hl']; exact hcnt l hl
      · config_simp; rw [upd_other _ _ _ (by omega)]; exact hf a ha)
    (by omega) ⟨e₃.wb_right, by config_simp; rw [hr₂ 140 (by omega)]; exact h140,
      by config_simp; rw [hr₂ 161 (by omega)]; exact h161,
      fun l hl => by config_simp; rw [hz₂ l (by omega)]; simp [lcF],
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> first | omega |
        exact hr₂ r hr, fun a ha => by config_simp; exact hf₂ a ha, by config_simp; exact ho₂⟩
  exact ⟨c₄, 3 + (k₂ + (1 + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, hc₄, hr₄, hf₄,
    ho₄⟩

/-- **`⌊√n⌋`.** -/
theorem msqrt_exec (hW : 4 * n + 4 ≤ W) (c : Config) (hc : WordsBounded W c)
    (h140 : c.nreg 140 = 0) (h141 : c.nreg 141 = 1) (h161 : c.nreg 161 = n) :
    ∃ c' t, Exec P W msqrt c c' t ∧ t ≤ 5 * n + 5 ∧ c'.nreg 201 = Nat.sqrt n ∧
      (∀ r, r < 201 ∨ 210 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.output = c.output := by
  let I : Config → Prop := fun c' => WordsBounded W c' ∧ c'.nmem = c.nmem ∧
    c'.output = c.output ∧ (∀ r, r < 201 ∨ 210 ≤ r → c'.nreg r = c.nreg r) ∧
    c'.nreg 201 * c'.nreg 201 ≤ n ∧ c'.nreg 207 = (c'.nreg 201 + 1) * (c'.nreg 201 + 1) ∧
    c'.nreg 208 = n + 1
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 201 140, .copyN 207 141,
      .addN 208 161 141]) c c₁ k₁ ∧ I c₁ ∧ k₁ = 3 := by
    exec_block
    · config_simp; rw [h161, h141]; omega
    refine ⟨⟨‹_›, rfl, rfl,
      fun r h1 => by config_simp; simp only [upd_apply]; split_ifs <;> omega,
      by config_simp; rw [h140]; omega, by config_simp; rw [h140, h141],
      by config_simp; rw [h161, h141]⟩, rfl⟩
  obtain ⟨c₂, k₂, e₂, ⟨hw₂, hm₂, ho₂, hr₂, h₂, h207, h208⟩, hn₂, hk₂⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 207) (b := 208)
    (body := block [.addN 201 201 141, .addN 209 201 141, .mulN 207 209 209]) I
    (fun c' => 5 * (n - c'.nreg 201)) (fun c' h => h.1)
    (fun c' h hlt => by
      obtain ⟨hw, hm, ho, hr, h1, h207, h208⟩ := h
      have g141 : c'.nreg 141 = 1 := by rw [hr 141 (by omega), h141]
      generalize ht : c'.nreg 201 = t at h1 h207
      have hsq : (t + 1) * (t + 1) ≤ n := by omega
      have hsq' : (t + 1 + 1) * (t + 1 + 1) = (t + 1) * (t + 1) + 2 * (t + 1) + 1 := by
        simp only [Nat.add_mul, Nat.mul_add]; omega
      have htn : t + 1 ≤ n := le_trans (Nat.le_mul_self _) hsq
      exec_block
      all_goals try (config_simp; rw [g141, ht]; omega)
      refine ⟨⟨‹_›, hm, ho,
        fun r h1 => by config_simp; simp only [upd_apply]; split_ifs <;> first | omega |
          exact hr r h1,
        by config_simp; rw [g141, ht]; exact hsq, by config_simp; rw [g141, ht],
        by config_simp; exact h208⟩, ?_⟩
      config_simp; rw [g141, ht]; omega) hI₁
  refine ⟨c₂, 3 + k₂, .seq e₁ e₂, ?_, ?_, hr₂, hm₂, ho₂⟩
  · have := hI₁.2.2.2.2.1; omega
  · exact Nat.eq_sqrt.2 ⟨h₂, by rw [← h207]; omega⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **A thin level** from `a`: the first `j ≤ t` such that the level `a + j` has at most
`n / (t + 1)` vertices, if there is one. -/
theorem thinJ_exec (lc : ℕ → ℕ) (a t : ℕ) (htW : t + 1 ≤ W) (hadd : bLC + a + t ≤ W)
    (c : Config) (hc : WordsBounded W c) (h140 : c.nreg 140 = 0) (h141 : c.nreg 141 = 1)
    (h161 : c.nreg 161 = n) (h200 : c.nreg 200 = bLC) (h201 : c.nreg 201 = t)
    (h203 : c.nreg 203 = a) (hlc : ∀ j ≤ t, c.nmem (bLC + (a + j)) = lc (a + j))
    (hex : ∃ j, j ≤ t ∧ lc (a + j) ≤ n / (t + 1)) :
    ∃ c' k, Exec P W thinJ c c' k ∧ k ≤ 8 * t + 11 ∧ c'.nreg 204 ≤ t ∧
      lc (a + c'.nreg 204) ≤ n / (t + 1) ∧
      (∀ r, r ≠ 84 → r ≠ 85 → r ≠ 86 → r ≠ 101 → r ≠ 204 → r ≠ 205 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hw₁, h101, h85, h204, hr₁, hm₁, ho₁, rfl⟩ : ∃ c₁ k₁, Exec P W
      (block [.copyN 101 141, .addN 205 201 141, .divN 85 161 205, .copyN 204 140]) c c₁ k₁ ∧
      WordsBounded W c₁ ∧ c₁.nreg 101 = 1 ∧ c₁.nreg 85 = n / (t + 1) ∧ c₁.nreg 204 = 0 ∧
      (∀ r, r ≠ 85 → r ≠ 101 → r ≠ 204 → r ≠ 205 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.output = c.output ∧ k₁ = 4 := by
    exec_block
    · config_simp; rw [h201, h141]; omega
    exact ⟨‹_›, by config_simp; exact h141, by config_simp; rw [h161, h201, h141],
      by config_simp; exact h140,
      fun r h1 h2 h3 h4 => by config_simp; simp only [upd_apply]; split_ifs <;> omega,
      rfl, rfl, rfl⟩
  let Inv : Config → Prop := fun c' => WordsBounded W c' ∧ c'.nreg 85 = n / (t + 1) ∧
    c'.nreg 101 = 1 ∧ (∀ r, r ≠ 84 → r ≠ 86 → r ≠ 204 → c'.nreg r = c₁.nreg r) ∧
    c'.nmem = c.nmem ∧ c'.output = c.output
  have g200 : c₁.nreg 200 = bLC := by
    rw [hr₁ 200 (by omega) (by omega) (by omega) (by omega)]; exact h200
  have g203 : c₁.nreg 203 = a := by
    rw [hr₁ 203 (by omega) (by omega) (by omega) (by omega)]; exact h203
  have hInc : ∀ c, Inv c → c.nreg 204 < t →
      Inv { c with nreg := upd c.nreg 204 (c.nreg 204 + c.nreg 101) } := by
    intro c ⟨hw, h85', h101', hr, hm, ho⟩ hlt
    refine ⟨⟨fun r => ?_, hw.2⟩, ?_, ?_, fun r h1 h2 h3 => ?_, hm, ho⟩
    · show upd c.nreg 204 (c.nreg 204 + c.nreg 101) r ≤ W
      simp only [upd_apply]
      split_ifs
      · rw [h101']; omega
      · exact hw.1 r
    · show upd c.nreg 204 (c.nreg 204 + c.nreg 101) 85 = _
      rw [upd_other _ _ _ (by omega)]; exact h85'
    · show upd c.nreg 204 (c.nreg 204 + c.nreg 101) 101 = _
      rw [upd_other _ _ _ (by omega)]; exact h101'
    · show upd c.nreg 204 (c.nreg 204 + c.nreg 101) r = _
      rw [upd_other _ _ _ h3]; exact hr r h1 h2 h3
  obtain ⟨c', k', e', hk', ⟨hw', -, -, hr', hm', ho'⟩, hj, hf⟩ := thinLoop_exec (P := P)
    (W := W) (cnt := tcnt) (rj := 204) (fun j => lc (a + j)) (n / (t + 1)) t c₁ Inv
    (fun c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    hInc
    (fun c ⟨hw, h85', h101', hr, hm, ho⟩ hj => by
      have g200' : c.nreg 200 = bLC := by rw [hr 200 (by omega) (by omega) (by omega)]; exact g200
      have g203' : c.nreg 203 = a := by rw [hr 203 (by omega) (by omega) (by omega)]; exact g203
      have ml : c.nmem (a + c.nreg 204 + bLC) = lc (a + c.nreg 204) := by
        rw [hm, show a + c.nreg 204 + bLC = bLC + (a + c.nreg 204) by omega]; exact hlc _ hj
      unfold tcnt
      exec_block
      all_goals try (config_simp; (try simp only [g203', g200']); omega)
      rename_i hwb
      simp only [g203', g200'] at hwb ⊢
      refine ⟨⟨‹_›, by config_simp; exact h85', by config_simp; exact h101',
        fun r h1 h2 h3 => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r h1 h2 h3,
        by config_simp; exact hm, by config_simp; exact ho⟩, ?_, by config_simp, by omega⟩
      config_simp; exact ml)
    hex htW c₁ ⟨hw₁, h85, h101, fun r _ _ _ => rfl, hm₁, ho₁⟩ h204
  refine ⟨c', 4 + k', .seq e₁ e', by omega, hj, hf, fun r h1 h2 h3 h4 h5 h6 => ?_,
    hm', ho'⟩
  rw [hr' r h1 h3 h5, hr₁ r h2 h4 h5 h6]

end proofs

/-! ### The thin levels of a breadth-first tree -/

section Thin

open Map

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] {M : Map D P}
  {T : M.SpTree} {n : ℕ} (vi : P ≃ Fin n) {L : ℕ → ℕ} (hL : ∀ v, L (vi v) = T.height v)
include hL

/-- The counts are the sizes of the levels. -/
theorem lcF_eq_card (l : ℕ) : lcF L n l = #(T.lvl l) := by
  have e : (range n).filter (fun v => L v = l) =
      (T.lvl l).map ⟨fun v : P => (vi v : ℕ), fun a b h => vi.injective (Fin.ext h)⟩ := by
    ext x
    simp only [mem_filter, mem_range, mem_map, SpTree.mem_lvl]
    constructor
    · rintro ⟨hx, hlx⟩
      refine ⟨vi.symm ⟨x, hx⟩, ?_, ?_⟩
      · rw [← hL]; simpa using hlx
      · show ((vi (vi.symm ⟨x, hx⟩) : Fin n) : ℕ) = x
        simp
    · rintro ⟨v, hv, rfl⟩
      exact ⟨(vi v).2, by show L (vi v : ℕ) = l; rw [hL]; exact hv⟩
  unfold lcF
  rw [e, card_map]

/-- A thin level among `a, …, a + t`, in the counts. -/
theorem exists_thin (a t : ℕ) : ∃ j, j ≤ t ∧ lcF L n (a + j) ≤ n / (t + 1) := by
  obtain ⟨j, hj, h⟩ := exists_small_level T a t
  refine ⟨j, by omega, ?_⟩
  rw [lcF_eq_card vi hL, Nat.le_div_iff_mul_le (by omega), mul_comm]
  rwa [Fintype.card_congr vi, Fintype.card_fin] at h

theorem mul_card_le {l t : ℕ} (h : lcF L n l ≤ n / (t + 1)) : (t + 1) * #(T.lvl l) ≤ n := by
  rw [lcF_eq_card vi hL, Nat.le_div_iff_mul_le (by omega)] at h
  rw [mul_comm]; exact h

variable {W : ℕ} {P' : Input} {bLv bLC : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The thin levels on the machine.** For a breadth-first tree `T` of a plane map with `n`
vertices whose levels are at `bLv` (read through a numbering `vi` of the vertices), and a level
`ls < n` in `r180`, the program `thin` ends within `24 n + 16 ⌊√n⌋ + 43` steps with
`r201 = ⌊√n⌋`, and `j₂ = r210 ≤ ⌊√n⌋`, `j₀ = r204 ≤ ⌊√n⌋` such that the levels `ls + 1 + j₂`
and `ls - ⌊√n⌋ + j₀` have at most `n / (⌊√n⌋ + 1)` vertices each. -/
theorem thin_exec (hT : IsBFS T) (hlay : bLv + n ≤ bLC) (hW : bLC + 4 * n + 4 ≤ W)
    (c : Config) (hc : WordsBounded W c) (h140 : c.nreg 140 = 0) (h141 : c.nreg 141 = 1)
    (h161 : c.nreg 161 = n) (h163 : c.nreg 163 = bLv) (h200 : c.nreg 200 = bLC) {ls : ℕ}
    (h180 : c.nreg 180 = ls) (hls : ls < n) (hLm : ∀ v < n, c.nmem (bLv + v) = L v) :
    ∃ c' t, Exec P' W thin c c' t ∧ t ≤ 24 * n + 16 * Nat.sqrt n + 43 ∧
      c'.nreg 201 = Nat.sqrt n ∧
      c'.nreg 210 ≤ Nat.sqrt n ∧ (Nat.sqrt n + 1) * #(T.lvl (ls + 1 + c'.nreg 210)) ≤ n ∧
      c'.nreg 204 ≤ Nat.sqrt n ∧
      (Nat.sqrt n + 1) * #(T.lvl (ls - Nat.sqrt n + c'.nreg 204)) ≤ n ∧
      (∀ r, r < 84 ∨ (86 < r ∧ r < 101) ∨ (101 < r ∧ r < 201) ∨ 211 ≤ r →
        c'.nreg r = c.nreg r) ∧
      (∀ a, a < bLC ∨ bLC + 2 * n + 1 ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  have hLn : ∀ v < n, L v < n := fun v hv => by
    have e : L v = T.height (vi.symm ⟨v, hv⟩) := by rw [← hL]; simp
    rw [e]
    have := height_lt_card hT (vi.symm ⟨v, hv⟩)
    rwa [Fintype.card_congr vi, Fintype.card_fin] at this
  set t := Nat.sqrt n with ht
  have htn : t ≤ n := Nat.sqrt_le_self n
  unfold thin
  -- the counts
  obtain ⟨c₁, t₁, e₁, ht₁, hlc₁, hr₁, hf₁, ho₁⟩ :=
    lcnt_exec (P := P') (L := L) hlay (by omega) c hc h140 h141 h161 h163 h200 hLm hLn
  have g₁ : ∀ r, r < 202 → c₁.nreg r = c.nreg r := fun r hr => hr₁ r (Or.inl hr)
  -- `⌊√n⌋`
  obtain ⟨c₂, t₂, e₂, ht₂, h201, hr₂, hm₂, ho₂⟩ := msqrt_exec (P := P') (n := n) (by omega) c₁
    e₁.wb_right
    (by rw [g₁ 140 (by omega)]; exact h140) (by rw [g₁ 141 (by omega)]; exact h141)
    (by rw [g₁ 161 (by omega)]; exact h161)
  have g₂ : ∀ r, r < 201 → c₂.nreg r = c.nreg r := fun r hr => by
    rw [hr₂ r (Or.inl hr), g₁ r (by omega)]
  have hlc₂ : ∀ l ≤ 2 * n, c₂.nmem (bLC + l) = lcF L n l := fun l hl => by
    rw [hm₂]; exact hlc₁ l hl
  -- `a = ls + 1`
  obtain ⟨c₃, e₃, k₃, h203, hm₃, ho₃⟩ : ∃ c₃, Exec P' W (.instr (.addN 203 180 141)) c₂ c₃ 1 ∧
      (∀ r, r ≠ 203 → c₃.nreg r = c₂.nreg r) ∧ c₃.nreg 203 = ls + 1 ∧ c₃.nmem = c₂.nmem ∧
      c₃.output = c₂.output :=
    ⟨_, Exec.addN (P := P') e₂.wb_right 203 180 141
      (by rw [g₂ 180 (by omega), g₂ 141 (by omega), h180, h141]; omega),
      fun r hr => upd_other _ _ _ hr, by
        config_simp; rw [g₂ 180 (by omega), g₂ 141 (by omega), h180, h141], rfl, rfl⟩
  obtain ⟨c₄, t₄, e₄, ht₄, hj₂, hf₂, hr₄, hm₄, ho₄⟩ := thinJ_exec (P := P') (n := n)
    (bLC := bLC) (lcF L n) (ls + 1) t (by omega) (by omega) c₃ e₃.wb_right
    (by rw [k₃ _ (by omega), g₂ _ (by omega)]; exact h140)
    (by rw [k₃ _ (by omega), g₂ _ (by omega)]; exact h141)
    (by rw [k₃ _ (by omega), g₂ _ (by omega)]; exact h161)
    (by rw [k₃ _ (by omega), hr₂ _ (Or.inl (by omega)), hr₁ _ (Or.inl (by omega))]; exact h200)
    (by rw [k₃ _ (by omega)]; exact h201) h203
    (fun j hj => by rw [hm₃]; exact hlc₂ _ (by omega)) (exists_thin vi hL _ _)
  -- `j₂` kept in `r210`
  obtain ⟨c₅, e₅, k₅, h210, hm₅, ho₅⟩ : ∃ c₅, Exec P' W (.instr (.copyN 210 204)) c₄ c₅ 1 ∧
      (∀ r, r ≠ 210 → c₅.nreg r = c₄.nreg r) ∧ c₅.nreg 210 = c₄.nreg 204 ∧ c₅.nmem = c₄.nmem ∧
      c₅.output = c₄.output :=
    ⟨_, Exec.copyN (P := P') e₄.wb_right 210 204, fun r hr => upd_other _ _ _ hr, by
      config_simp, rfl, rfl⟩
  -- `a = ls - t`
  have g₄ : ∀ r, r ≠ 84 → r ≠ 85 → r ≠ 86 → r ≠ 101 → r ≠ 204 → r ≠ 205 → r ≠ 203 →
      c₄.nreg r = c₂.nreg r := fun r h1 h2 h3 h4 h5 h6 h7 => by
    rw [hr₄ r h1 h2 h3 h4 h5 h6, k₃ r h7]
  obtain ⟨c₆, e₆, k₆, h203', hm₆, ho₆⟩ : ∃ c₆, Exec P' W (.instr (.subN 203 180 201)) c₅ c₆ 1 ∧
      (∀ r, r ≠ 203 → c₆.nreg r = c₅.nreg r) ∧ c₆.nreg 203 = ls - t ∧ c₆.nmem = c₅.nmem ∧
      c₆.output = c₅.output :=
    ⟨_, Exec.subN (P := P') e₅.wb_right 203 180 201, fun r hr => upd_other _ _ _ hr, by
      config_simp
      rw [k₅ _ (by omega), k₅ _ (by omega), g₄ _ (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega), g₄ _ (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega), g₂ 180 (by omega), h180, h201], rfl, rfl⟩
  have g₆ : ∀ r, r ≠ 84 → r ≠ 85 → r ≠ 86 → r ≠ 101 → r ≠ 204 → r ≠ 205 → r ≠ 203 →
      r ≠ 210 → c₆.nreg r = c₂.nreg r := fun r h1 h2 h3 h4 h5 h6 h7 h8 => by
    rw [k₆ r h7, k₅ r h8, g₄ r h1 h2 h3 h4 h5 h6 h7]
  obtain ⟨c₇, t₇, e₇, ht₇, hj₀, hf₀, hr₇, hm₇, ho₇⟩ := thinJ_exec (P := P') (n := n)
    (bLC := bLC) (lcF L n) (ls - t) t (by omega) (by omega) c₆ e₆.wb_right
    (by rw [g₆ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), g₂ _ (by omega)]; exact h140)
    (by rw [g₆ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), g₂ _ (by omega)]; exact h141)
    (by rw [g₆ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), g₂ _ (by omega)]; exact h161)
    (by rw [g₆ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), hr₂ _ (Or.inl (by omega)), hr₁ _ (Or.inl (by omega))]; exact h200)
    (by rw [g₆ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; exact h201) h203'
    (fun j hj => by rw [hm₆, hm₅, hm₄, hm₃]; exact hlc₂ _ (by omega)) (exists_thin vi hL _ _)
  refine ⟨c₇, t₁ + (t₂ + (1 + (t₄ + (1 + (1 + t₇))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), by omega,
    ?_, ?_, ?_, hj₀, mul_card_le vi hL hf₀, fun r hr => ?_, fun a ha => ?_, ?_⟩
  · rw [hr₇ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      g₆ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; exact h201
  · rw [hr₇ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      k₆ _ (by omega), h210]; exact hj₂
  · rw [hr₇ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      k₆ _ (by omega), h210]; exact mul_card_le vi hL hf₂
  · have hne : r ≠ 84 ∧ r ≠ 85 ∧ r ≠ 86 ∧ r ≠ 101 ∧ r ≠ 204 ∧ r ≠ 205 ∧ r ≠ 203 ∧ r ≠ 210 :=
      by omega
    rw [hr₇ _ hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2.1,
      g₆ _ hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2.1 hne.2.2.2.2.2.2.1
        hne.2.2.2.2.2.2.2]
    by_cases h : r < 201
    · exact g₂ r h
    · rw [hr₂ r (Or.inr (by omega)), hr₁ r (Or.inr (by omega))]
  · rw [hm₇, hm₆, hm₅, hm₄, hm₃, hm₂]; exact hf₁ a ha
  · rw [ho₇, ho₆, ho₅, ho₄, ho₃, ho₂, ho₁]

end Thin

end MillerProg

end PlanarSeparator
