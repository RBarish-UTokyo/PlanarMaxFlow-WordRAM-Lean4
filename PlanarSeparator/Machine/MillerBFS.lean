module

public import PlanarSeparator.Machine.MillerDart

/-!
# Miller's separator on the machine: breadth-first search on the coded map

Step 1 of the plan in `PlanarSeparator/Machine/Miller.lean`. The coded map holds, for every dart
`x < K = 3 k`, its reversal `A x` (at `bR + x`) and its vertex `V x < n` (at `bV + x`). The
program `bprog`

* clears the marks of the vertices (at `bMk + v`) and empties the lists of darts at the
  vertices (`ipass`);
* links the darts at every vertex into a list (`lpass`): the head of the list of `v` (at
  `bHd + v`) is the last dart at `v`, and the next dart after `x` (at `bNx + x`) is the last dart
  at `V x` before `x` (`lastAt`), `K` ending the lists;
* searches the map breadth-first from vertex `0` (`bfsL`), with a queue at `bQ`, writing the
  level of every vertex at `bLv + v` and the dart from every vertex other than `0` to its parent
  at `bPr + v`.

`bprog_exec`: within `19 n + 90 k + 14` steps every vertex reached is closed (all its darts lead
to reached vertices at most one level further), the parent dart of every reached vertex other
than `0` lies at it and leads one level down to a reached vertex, and `0` is reached at level
`0`. For a plane map coded by `cd`, with its vertices numbered by `vi`, every vertex is reached,
and the levels are the heights of a breadth-first tree `T` (`PlanarSeparator.Map.IsBFS`) rooted
at the vertex numbered `0`, whose parent darts are those at `bPr` (`bfs_tree`; with the program,
`bprog_tree`).

Registers: `r140 = 0`, `r141 = 1`, `r142 = 3`, `r143 = k`, `r147 = bR`, `r161 = n`,
`r162 = bV`, `r163 = bLv`, and `r215 = bPr`, `r216 = bMk`, `r217 = bQ`, `r218 = bHd`,
`r219 = bNx`; the program writes `r220 … r229`.
-/

@[expose] public section

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The lists of darts at the vertices -/

/-- The last dart `y < i` at the vertex `v` (by the vertices `V y`), or `s` if there is none. -/
def lastAt (V : ℕ → ℕ) (s v : ℕ) : ℕ → ℕ
  | 0 => s
  | i + 1 => if V i = v then i else lastAt V s v i

theorem lastAt_spec (V : ℕ → ℕ) (s v : ℕ) : ∀ i, i ≤ s →
    (lastAt V s v i = s ∧ ∀ y < i, V y ≠ v) ∨
    (lastAt V s v i < i ∧ V (lastAt V s v i) = v ∧ ∀ y < i, V y = v → y ≤ lastAt V s v i)
  | 0, _ => Or.inl ⟨rfl, fun y hy => absurd hy (by omega)⟩
  | i + 1, hi => by
    simp only [lastAt]
    split_ifs with h
    · exact Or.inr ⟨by omega, h, fun y hy _ => by omega⟩
    · rcases lastAt_spec V s v i (by omega) with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · refine Or.inl ⟨h1, fun y hy => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | rfl
        · exact h2 y hy
        · exact h
      · refine Or.inr ⟨by omega, h2, fun y hy hy' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | rfl
        · exact h3 y hy hy'
        · exact absurd hy' h

theorem lastAt_succ_ne {V : ℕ → ℕ} {s v i : ℕ} (h : V i ≠ v) :
    lastAt V s v (i + 1) = lastAt V s v i := by simp [lastAt, h]

theorem lastAt_succ_eq {V : ℕ → ℕ} {s v i : ℕ} (h : V i = v) : lastAt V s v (i + 1) = i := by
  simp [lastAt, h]

/-- The number of darts `y < j` at `v`. -/
def cntB (V : ℕ → ℕ) (v j : ℕ) : ℕ := ∑ y ∈ range j, if V y = v then 1 else 0

theorem cntB_congr {V : ℕ → ℕ} {v p : ℕ} :
    ∀ j, p < j → (∀ y, p < y → y < j → V y ≠ v) → cntB V v j = cntB V v (p + 1) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; rfl
  | succ j hj ih =>
    intro h
    rw [cntB, sum_range_succ, ite_eq_right (h j (by omega) (by omega)), add_zero]
    exact ih fun y h1 h2 => h y h1 (by omega)

/-- The count of the darts still to be scanned at `v` from the dart `p` of its list. -/
def remB (V : ℕ → ℕ) (s v p : ℕ) : ℕ := if p < s then cntB V v (p + 1) else 0

theorem remB_lastAt {V : ℕ → ℕ} {s v j : ℕ} (hj : j ≤ s) :
    remB V s v (lastAt V s v j) = cntB V v j := by
  rcases lastAt_spec V s v j hj with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · rw [remB, h1, ite_eq_right (lt_irrefl _), cntB]
    exact (sum_eq_zero fun y hy => ite_eq_right (h2 y (mem_range.1 hy))).symm
  · rw [remB, ite_eq_left (by omega)]
    exact (cntB_congr j h1 fun y hy1 hy2 hy => by have := h3 y hy2 hy; omega).symm

theorem cntB_succ_eq {V : ℕ → ℕ} {v p : ℕ} (h : V p = v) : cntB V v (p + 1) = cntB V v p + 1 := by
  rw [cntB, sum_range_succ, ite_eq_left h]; rfl

/-- The darts at distinct vertices are distinct. -/
theorem sum_cntB_le (V : ℕ → ℕ) (S : Finset ℕ) (K : ℕ) : ∑ u ∈ S, cntB V u K ≤ K := by
  unfold cntB
  rw [sum_comm]
  calc ∑ y ∈ range K, ∑ u ∈ S, (if V y = u then 1 else 0)
      = ∑ y ∈ range K, (if V y ∈ S then 1 else 0) := sum_congr rfl fun y _ => sum_ite_eq _ _ _
    _ ≤ ∑ _y ∈ range K, 1 := sum_le_sum fun y _ => by split_ifs <;> omega
    _ = K := by simp

/-! ### The programs -/

/-- **One vertex** `r221 = v`: an empty list, no mark. -/
def ibody : Stmt :=
  block [.addN 226 218 221, .storeN 226 220, .addN 226 216 221, .storeN 226 140, .addN 221 221 141]

/-- **One dart** `r221 = x`: put it at the head of the list of its vertex. -/
def lbody : Stmt :=
  block [.addN 226 162 221, .loadN 227 226, .addN 226 218 227, .loadN 228 226,
    .addN 226 219 221, .storeN 226 228, .addN 226 218 227, .storeN 226 221, .addN 221 221 141]

/-- **The lists of darts at the vertices.** -/
def lpass : Stmt := .seq (.instr (.copyN 221 140)) (.whileLtN 221 220 lbody)

/-- Start: mark `0`, queue it at level `0`; `r221 = 0` is the head, `r222 = 1` the tail of the
queue. -/
def bStart : Stmt :=
  block [.storeN 216 141, .storeN 217 140, .storeN 163 140, .copyN 221 140, .copyN 222 141]

/-- Dequeue `r223 = u`; `r224 = L u + 1`, `r225` the head of the list of `u`. -/
def bDeq : Stmt :=
  block [.addN 226 217 221, .loadN 223 226, .addN 221 221 141, .addN 226 163 223,
    .loadN 224 226, .addN 224 224 141, .addN 226 218 223, .loadN 225 226]

/-- A new vertex `r228 = v` reached through the dart `r227 = A x`. -/
def bNew : Stmt :=
  block [.storeN 226 141, .addN 226 163 228, .storeN 226 224, .addN 226 215 228,
    .storeN 226 227, .addN 226 217 222, .storeN 226 228, .addN 222 222 141]

/-- The dart `r225 = x` of `u`. -/
def bVisit : Stmt :=
  .seq (block [.addN 226 147 225, .loadN 227 226, .addN 226 162 227, .loadN 228 226,
      .addN 226 216 228, .loadN 229 226])
    (.seq (.ifLtN 229 141 bNew .skip) (block [.addN 226 219 225, .loadN 225 226]))

/-- One vertex of the search. -/
def bBody : Stmt := .seq bDeq (.whileLtN 225 220 bVisit)

/-- The search. -/
def bfsL : Stmt := .seq bStart (.whileLtN 221 222 bBody)

/-- **Breadth-first search on the coded map.** -/
def bprog : Stmt :=
  .seq (block [.mulN 220 143 142, .copyN 221 140])
    (.seq (.whileLtN 221 161 ibody) (.seq lpass bfsL))

section proofs

variable {W : ℕ} {P : Input} {n K bR bV bLv bPr bMk bQ bHd bNx : ℕ} {A V : ℕ → ℕ}

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem ipass_exec (hlay : bMk + n ≤ bHd) (hW : bHd + n ≤ W) (c : Config)
    (hc : WordsBounded W c) (h140 : c.nreg 140 = 0) (h141 : c.nreg 141 = 1)
    (h161 : c.nreg 161 = n) (h216 : c.nreg 216 = bMk) (h218 : c.nreg 218 = bHd)
    (h220 : c.nreg 220 = K) (h221 : c.nreg 221 = 0) :
    ∃ c' t, Exec P W (.whileLtN 221 161 ibody) c c' t ∧ t ≤ 7 * n + 2 ∧
      (∀ v < n, c'.nmem (bHd + v) = K ∧ c'.nmem (bMk + v) = 0) ∧
      (∀ r, r < 221 ∨ 227 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bMk ∨ (bMk + n ≤ a ∧ a < bHd) ∨ bHd + n ≤ a → c'.nmem a = c.nmem a) ∧
      c'.output = c.output := by
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 221 = i ∧
    c'.nreg 161 = n ∧ (∀ v < i, c'.nmem (bHd + v) = K ∧ c'.nmem (bMk + v) = 0) ∧
    (∀ r, r < 221 ∨ 227 ≤ r → c'.nreg r = c.nreg r) ∧
    (∀ a, a < bMk ∨ (bMk + n ≤ a ∧ a < bHd) ∨ bHd + n ≤ a → c'.nmem a = c.nmem a) ∧
    c'.output = c.output
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 221) (rN := 161) (N := n)
    (lo := 0) (B := 5) (body := ibody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, g221, g161, hP, hr, hf, ho⟩ hi => by
      have g140 : c₁.nreg 140 = 0 := by rw [hr 140 (by omega)]; exact h140
      have g141 : c₁.nreg 141 = 1 := by rw [hr 141 (by omega)]; exact h141
      have g216 : c₁.nreg 216 = bMk := by rw [hr 216 (by omega)]; exact h216
      have g218 : c₁.nreg 218 = bHd := by rw [hr 218 (by omega)]; exact h218
      have g220 : c₁.nreg 220 = K := by rw [hr 220 (by omega)]; exact h220
      unfold ibody
      exec_block
      all_goals try (config_simp; (try simp only [g216, g218, g221, g141]); omega)
      refine ⟨⟨‹_›, by config_simp; rw [g221, g141], by config_simp; exact g161,
        fun v hv => ?_, fun r hr' => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr',
        fun a ha => by
          config_simp; simp only [g216, g218, g221]
          rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact hf a ha,
        by config_simp; exact ho⟩, by omega⟩
      config_simp; simp only [g216, g218, g221, g140, g220]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
      · refine ⟨?_, ?_⟩ <;> simp only [upd_apply] <;> split_ifs <;>
          first | omega | exact (hP v hv).1 | exact (hP v hv).2
      · refine ⟨?_, ?_⟩ <;> simp only [upd_apply] <;> split_ifs <;> omega)
    (by omega) ⟨hc, h221, h161, fun v hv => absurd hv (by omega), fun _ _ => rfl,
      fun _ _ => rfl, rfl⟩
  obtain ⟨-, -, -, hP', hr', hf', ho'⟩ := hI
  exact ⟨c', t, e, by omega, hP', hr', hf', ho'⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem lpass_exec (hlay : bV + K ≤ bHd ∧ bHd + n ≤ bNx) (hW : bNx + K ≤ W) (c : Config)
    (hc : WordsBounded W c) (h140 : c.nreg 140 = 0) (h141 : c.nreg 141 = 1)
    (h162 : c.nreg 162 = bV) (h218 : c.nreg 218 = bHd) (h219 : c.nreg 219 = bNx)
    (h220 : c.nreg 220 = K) (hV : ∀ x < K, c.nmem (bV + x) = V x ∧ V x < n)
    (hH : ∀ v < n, c.nmem (bHd + v) = K) :
    ∃ c' t, Exec P W lpass c c' t ∧ t ≤ 11 * K + 3 ∧
      (∀ v < n, c'.nmem (bHd + v) = lastAt V K v K) ∧
      (∀ x < K, c'.nmem (bNx + x) = lastAt V K (V x) x) ∧
      (∀ r, r < 221 ∨ 229 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bHd ∨ bNx + K ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 221 = i ∧
    c'.nreg 220 = K ∧ (∀ v < n, c'.nmem (bHd + v) = lastAt V K v i) ∧
    (∀ x < i, c'.nmem (bNx + x) = lastAt V K (V x) x) ∧
    (∀ r, r < 221 ∨ 229 ≤ r → c'.nreg r = c.nreg r) ∧
    (∀ a, a < bHd ∨ bNx + K ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  have e₁ := Exec.copyN (P := P) hc 221 140
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 221) (rN := 220) (N := K)
    (lo := 0) (B := 9) (body := lbody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, g221, g220, hP, hN, hr, hf, ho⟩ hi => by
      have g141 : c₁.nreg 141 = 1 := by rw [hr 141 (by omega)]; exact h141
      have g162 : c₁.nreg 162 = bV := by rw [hr 162 (by omega)]; exact h162
      have g218 : c₁.nreg 218 = bHd := by rw [hr 218 (by omega)]; exact h218
      have g219 : c₁.nreg 219 = bNx := by rw [hr 219 (by omega)]; exact h219
      have mV : c₁.nmem (bV + i) = V i := by rw [hf _ (Or.inl (by omega))]; exact (hV i hi).1
      have hVi := (hV i hi).2
      have mH : c₁.nmem (bHd + V i) = lastAt V K (V i) i := hP _ hVi
      unfold lbody
      exec_block
      all_goals try (config_simp; (try simp only [g162, g221, mV, g218, g219, g141]); omega)
      rename_i hwb
      simp only [g162, g221, mV, g218, g219, g141] at hwb ⊢
      refine ⟨⟨‹_›, by config_simp, by config_simp; exact g220, fun v hv => ?_,
        fun x hx => ?_, fun r hr' => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr',
        fun a ha => by
          config_simp
          rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact hf a ha,
        by config_simp; exact ho⟩, by omega⟩
      · config_simp
        by_cases hvi : v = V i
        · subst hvi; rw [upd_same, lastAt_succ_eq rfl]
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), hP v hv,
            lastAt_succ_ne (Ne.symm hvi)]
      · config_simp
        rw [upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
        · rw [upd_other _ _ _ (by omega)]; exact hN x hx
        · rw [upd_same, mH])
    (by omega) ⟨e₁.wb_right, by config_simp; exact h140, by config_simp; exact h220,
      fun v hv => by config_simp; exact hH v hv, fun x hx => absurd hx (by omega),
      fun r hr => by
        show upd c.nreg 221 (c.nreg 140) r = c.nreg r
        simp only [upd_apply]; split_ifs <;> omega, fun a _ => rfl, rfl⟩
  obtain ⟨-, -, -, hP', hN', hr', hf', ho'⟩ := hI
  exact ⟨c', 1 + t, .seq e₁ e, by omega, hP', hN', hr', hf', ho'⟩

end proofs

/-! ### The invariants of the search -/

/-- The cell `b + i` of the memory. -/
def rd (mem : ℕ → ℕ) (b i : ℕ) : ℕ := mem (b + i)

theorem rd_upd (mem : ℕ → ℕ) (a x b i : ℕ) :
    rd (upd mem a x) b i = if b + i = a then x else rd mem b i := rfl

/-- The registers and the memory the search reads, in the configuration `c₀` it starts from. -/
structure BFix (n K bR bV bLv bPr bMk bQ bHd bNx : ℕ) (A V : ℕ → ℕ) (c : Config) : Prop where
  r140 : c.nreg 140 = 0
  r141 : c.nreg 141 = 1
  r147 : c.nreg 147 = bR
  r162 : c.nreg 162 = bV
  r163 : c.nreg 163 = bLv
  r215 : c.nreg 215 = bPr
  r216 : c.nreg 216 = bMk
  r217 : c.nreg 217 = bQ
  r218 : c.nreg 218 = bHd
  r219 : c.nreg 219 = bNx
  r220 : c.nreg 220 = K
  mA : ∀ x < K, c.nmem (bR + x) = A x
  mV : ∀ x < K, c.nmem (bV + x) = V x
  mH : ∀ v < n, c.nmem (bHd + v) = lastAt V K v K
  mN : ∀ x < K, c.nmem (bNx + x) = lastAt V K (V x) x

section inv

variable (n K bLv bPr bMk bQ : ℕ) (A V : ℕ → ℕ) (W : ℕ) (c₀ : Config)

/-- All darts at `u` lead to marked vertices at most one level further. -/
def Closed (mem : ℕ → ℕ) (u : ℕ) : Prop :=
  ∀ x < K, V x = u → rd mem bMk (V (A x)) = 1 ∧ rd mem bLv (V (A x)) ≤ rd mem bLv u + 1

/-- The state of the search. -/
structure BS (c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ r, r < 221 ∨ 230 ≤ r → c.nreg r = c₀.nreg r
  out : c.output = c₀.output
  frame : ∀ a, a < bLv ∨ (bLv + n ≤ a ∧ a < bPr) ∨ bQ + n ≤ a → c.nmem a = c₀.nmem a
  head_le : c.nreg 221 ≤ c.nreg 222
  tail_le : c.nreg 222 ≤ n
  q_lt : ∀ i < c.nreg 222, rd c.nmem bQ i < n
  q_inj : ∀ i < c.nreg 222, ∀ j < c.nreg 222, rd c.nmem bQ i = rd c.nmem bQ j → i = j
  q0 : 0 < c.nreg 222 ∧ rd c.nmem bQ 0 = 0
  mk01 : ∀ v < n, rd c.nmem bMk v = 0 ∨ rd c.nmem bMk v = 1
  mk_iff : ∀ v < n, rd c.nmem bMk v = 1 ↔ ∃ i < c.nreg 222, rd c.nmem bQ i = v
  lv0 : rd c.nmem bLv 0 = 0
  par : ∀ i, 1 ≤ i → i < c.nreg 222 →
    rd c.nmem bPr (rd c.nmem bQ i) < K ∧
      V (rd c.nmem bPr (rd c.nmem bQ i)) = rd c.nmem bQ i ∧
      rd c.nmem bLv (V (A (rd c.nmem bPr (rd c.nmem bQ i)))) + 1 =
        rd c.nmem bLv (rd c.nmem bQ i) ∧
      ∃ i' < i, rd c.nmem bQ i' = V (A (rd c.nmem bPr (rd c.nmem bQ i)))
  mono : ∀ i i', i ≤ i' → i' < c.nreg 222 →
    rd c.nmem bLv (rd c.nmem bQ i) ≤ rd c.nmem bLv (rd c.nmem bQ i')
  span : ∀ i' < c.nreg 222, 1 ≤ c.nreg 221 →
    rd c.nmem bLv (rd c.nmem bQ i') ≤ rd c.nmem bLv (rd c.nmem bQ (c.nreg 221 - 1)) + 1
  lv_le : ∀ i < c.nreg 222, rd c.nmem bLv (rd c.nmem bQ i) ≤ i
  t1 : c.nreg 221 = 0 → c.nreg 222 = 1

/-- Between two vertices. -/
structure IS (c : Config) : Prop extends BS n K bLv bPr bMk bQ A V W c₀ c where
  closed : ∀ i < c.nreg 221, Closed K bLv bMk A V c.nmem (rd c.nmem bQ i)

/-- While scanning the darts of `r223 = u`, those `x ≥ j` done. -/
structure VC (j : ℕ) (c : Config) : Prop extends BS n K bLv bPr bMk bQ A V W c₀ c where
  head_pos : 1 ≤ c.nreg 221
  cur : c.nreg 223 = rd c.nmem bQ (c.nreg 221 - 1)
  r224 : c.nreg 224 = rd c.nmem bLv (c.nreg 223) + 1
  j_le : j ≤ K
  closed : ∀ i, i + 1 < c.nreg 221 → Closed K bLv bMk A V c.nmem (rd c.nmem bQ i)
  closed_cur : ∀ x < K, j ≤ x → V x = c.nreg 223 →
    rd c.nmem bMk (V (A x)) = 1 ∧ rd c.nmem bLv (V (A x)) ≤ rd c.nmem bLv (c.nreg 223) + 1

end inv

section steps

variable {n K bLv bPr bMk bQ : ℕ} {A V : ℕ → ℕ} {W : ℕ} {c₀ : Config}

theorem BS.tail_lt {c : Config} (hI : BS n K bLv bPr bMk bQ A V W c₀ c) {v : ℕ} (hv : v < n)
    (hnot : ∀ i < c.nreg 222, rd c.nmem bQ i ≠ v) : c.nreg 222 < n := by
  have h := Finset.card_le_card_of_injOn (rd c.nmem bQ) (s := range (c.nreg 222))
    (t := (range n).erase v)
    (fun i hi => by
      simp only [coe_range, Set.mem_Iio] at hi
      simp only [coe_erase, coe_range, Set.mem_sdiff, Set.mem_Iio, Set.mem_singleton_iff]
      exact ⟨hI.q_lt i hi, hnot i hi⟩)
    (fun i hi j hj e => hI.q_inj i (by simpa using hi) j (by simpa using hj) e)
  rw [card_range, card_erase_of_mem (mem_range.2 hv), card_range] at h
  omega

/-- A dart `p` leading to a vertex already marked. -/
theorem VC.next_skip {j : ℕ} {c c' : Config} (hJ : VC n K bLv bPr bMk bQ A V W c₀ j c)
    {p : ℕ} (hpj : p < j) (hVp : V p = c.nreg 223)
    (hptr : ∀ x, p < x → x < j → V x ≠ c.nreg 223)
    (hv : rd c.nmem bMk (V (A p)) = 1 ∧
      rd c.nmem bLv (V (A p)) ≤ rd c.nmem bLv (c.nreg 223) + 1)
    (hwb : WordsBounded W c') (hK : ∀ r, r < 225 ∨ 230 ≤ r → c'.nreg r = c.nreg r)
    (hout : c'.output = c.output) (hmem : c'.nmem = c.nmem) :
    VC n K bLv bPr bMk bQ A V W c₀ p c' := by
  have g221 := hK 221 (by omega); have g222 := hK 222 (by omega)
  have g223 := hK 223 (by omega); have g224 := hK 224 (by omega)
  obtain ⟨⟨_, hregs, ho, hfr, hhl, htl, hql, hqi, hq0, hm01, hmi, hl0, hpar, hmono, hspan,
    hlvle, ht1⟩, hhp, hcur, h224, hjK, hcl, hclc⟩ := hJ
  refine ⟨⟨hwb, fun r hr => (hK r (by omega)).trans (hregs r hr), hout.trans ho, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, by omega, ?_, ?_⟩
  all_goals simp only [hmem, g221, g222, g223, g224]
  all_goals first | assumption | omega | skip
  · intro x hx h1 h2
    rcases Nat.lt_or_ge x j with h | h
    · rcases Nat.lt_or_ge p x with h' | h'
      · exact absurd h2 (hptr x h' h)
      · obtain rfl : x = p := by omega
        exact hv
    · exact hclc x hx h h2

/-- A dart `p` leading to a new vertex `v`: mark it, record its level and parent dart `A p`,
queue it. -/
theorem VC.next_new (hA : ∀ x < K, A x < K ∧ A (A x) = x) (hVn : ∀ x < K, V x < n)
    (hlay : bLv + n ≤ bPr ∧ bPr + n ≤ bMk ∧ bMk + n ≤ bQ) {j : ℕ} {c c' : Config}
    (hJ : VC n K bLv bPr bMk bQ A V W c₀ j c) {p : ℕ} (hpK : p < K) (hpj : p < j)
    (hVp : V p = c.nreg 223) (hptr : ∀ x, p < x → x < j → V x ≠ c.nreg 223)
    (hv : rd c.nmem bMk (V (A p)) = 0)
    (hwb : WordsBounded W c')
    (hK : ∀ r, r < 222 ∨ (223 ≤ r ∧ r < 225) ∨ 230 ≤ r → c'.nreg r = c.nreg r)
    (h222 : c'.nreg 222 = c.nreg 222 + 1) (hout : c'.output = c.output)
    (hmem : c'.nmem = upd (upd (upd (upd c.nmem (bMk + V (A p)) 1)
      (bLv + V (A p)) (rd c.nmem bLv (c.nreg 223) + 1))
      (bPr + V (A p)) (A p)) (bQ + c.nreg 222) (V (A p))) :
    VC n K bLv bPr bMk bQ A V W c₀ p c' := by
  have g221 := hK 221 (by omega); have g223 := hK 223 (by omega)
  have g224 := hK 224 (by omega)
  have hhp := hJ.head_pos; have hhl := hJ.head_le; have htl := hJ.tail_le
  have hu := hJ.q_lt _ (show c.nreg 221 - 1 < c.nreg 222 by omega)
  rw [← hJ.cur] at hu
  have hAp := (hA p hpK).1
  have hAA := (hA p hpK).2
  have htlv := hVn _ hAp
  generalize hgv : V (A p) = v at hv hmem htlv
  have hnot : ∀ i < c.nreg 222, rd c.nmem bQ i ≠ v := fun i hi e => by
    have := (hJ.mk_iff v htlv).2 ⟨i, hi, e⟩; omega
  have htl' := hJ.tail_lt htlv hnot
  have huv : c.nreg 223 ≠ v := by
    intro e; apply hnot (c.nreg 221 - 1) (by omega); rw [← hJ.cur, e]
  have hmk : ∀ x < n, rd c'.nmem bMk x = if x = v then 1 else rd c.nmem bMk x := fun x hx => by
    simp only [hmem, rd_upd]; split_ifs <;> omega
  have hlv : ∀ x < n, rd c'.nmem bLv x = if x = v then rd c.nmem bLv (c.nreg 223) + 1 else
      rd c.nmem bLv x := fun x hx => by
    simp only [hmem, rd_upd]; split_ifs <;> omega
  have hpr : ∀ x < n, rd c'.nmem bPr x = if x = v then A p else rd c.nmem bPr x :=
    fun x hx => by simp only [hmem, rd_upd]; split_ifs <;> omega
  have hq : ∀ i < n, rd c'.nmem bQ i = if i = c.nreg 222 then v else rd c.nmem bQ i :=
    fun i hi => by simp only [hmem, rd_upd]; split_ifs <;> omega
  have hq_lt : ∀ i < c.nreg 222, rd c'.nmem bQ i = rd c.nmem bQ i := fun i hi => by
    rw [hq i (by omega)]; simp [show i ≠ c.nreg 222 by omega]
  have hlv_q : ∀ i < c.nreg 222, rd c'.nmem bLv (rd c.nmem bQ i) =
      rd c.nmem bLv (rd c.nmem bQ i) :=
    fun i hi => by rw [hlv _ (hJ.q_lt i hi)]; simp [hnot i hi]
  have hlvu : rd c'.nmem bLv (c.nreg 223) = rd c.nmem bLv (c.nreg 223) := by
    rw [hlv _ hu]; simp [huv]
  have hmk_ge : ∀ x < n, rd c.nmem bMk x = 1 → rd c'.nmem bMk x = 1 := fun x hx h => by
    rw [hmk x hx]; split_ifs <;> simp [h]
  have hlv_m : ∀ x < n, rd c.nmem bMk x = 1 → rd c'.nmem bLv x = rd c.nmem bLv x :=
    fun x hx h => by
      rw [hlv x hx]; split_ifs with e
      · subst e; rw [hv] at h; exact absurd h (by omega)
      · rfl
  have hvl : rd c'.nmem bLv v = rd c.nmem bLv (c.nreg 223) + 1 := by rw [hlv v htlv]; simp
  have hspan := hJ.span
  have hcurq : rd c.nmem bQ (c.nreg 221 - 1) = c.nreg 223 := hJ.cur.symm
  refine ⟨⟨hwb, fun r hr => ?_, hout.trans hJ.out, fun a ha => ?_, by rw [h222, g221]; omega,
    by rw [h222]; omega, fun i hi => ?_, fun i hi j hj e => ?_, ?_, fun x hx => ?_,
    fun x hx => ?_, ?_, fun i hi1 hi2 => ?_, fun i i' hii hi' => ?_, fun i' hi' h1 => ?_,
    fun i hi => ?_, fun h => absurd h (by rw [g221]; omega)⟩, by rw [g221]; exact hhp, ?_, ?_,
    by omega, fun i hi => ?_, fun x hx h1 h2 => ?_⟩
  · rcases hr with hr | hr
    · rcases Nat.lt_or_ge r 222 with h | h
      · rw [hK r (by omega)]; exact hJ.regs r (by omega)
      · obtain rfl : r = 222 := by omega
        exact absurd hr (by omega)
    · rw [hK r (by omega)]; exact hJ.regs r (by omega)
  · rw [hmem, ← hJ.frame a ha]; simp only [upd_apply]; split_ifs <;> omega
  · rw [h222] at hi; rw [hq i (by omega)]; split_ifs
    · exact htlv
    · exact hJ.q_lt i (by omega)
  · rw [h222] at hi hj
    rw [hq i (by omega), hq j (by omega)] at e
    split_ifs at e with e1 e2 e2
    · omega
    · exact absurd e.symm (hnot j (by omega))
    · exact absurd e (hnot i (by omega))
    · exact hJ.q_inj i (by omega) j (by omega) e
  · rw [h222]; refine ⟨by omega, ?_⟩; rw [hq_lt 0 hJ.q0.1]; exact hJ.q0.2
  · rw [hmk x hx]; split_ifs
    · right; rfl
    · exact hJ.mk01 x hx
  · rw [hmk x hx, h222]
    split_ifs with hxv
    · subst hxv; simp only [true_iff]; exact ⟨c.nreg 222, by omega, by rw [hq _ htl']; simp⟩
    · rw [hJ.mk_iff x hx]
      constructor
      · rintro ⟨i, hi, e⟩; exact ⟨i, by omega, by rw [hq_lt i hi]; exact e⟩
      · rintro ⟨i, hi, e⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ⟨i, hi, by rw [← hq_lt i hi]; exact e⟩
        · rw [hq _ htl'] at e; simp at e; exact absurd e.symm hxv
  · have h0 := hJ.q0
    rw [← h0.2, ← hq_lt 0 h0.1, hq_lt 0 h0.1, hlv_q 0 h0.1, h0.2]; exact hJ.lv0
  · rw [h222] at hi2
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi2 with hi2 | rfl
    · rw [hq_lt i hi2, hpr _ (hJ.q_lt i hi2)]
      simp only [hnot i hi2, ↓reduceIte]
      obtain ⟨p1, p2, p3, i', hi', p4⟩ := hJ.par i hi1 hi2
      refine ⟨p1, p2, ?_, i', hi', by rw [hq_lt i' (by omega), p4]⟩
      rw [← p4, hlv_q i' (by omega), hlv_q i hi2, p4, p3]
    · simp only [hq _ htl', ↓reduceIte]; rw [hpr _ htlv]; simp only [↓reduceIte]
      refine ⟨hAp, hgv, ?_, c.nreg 221 - 1, by omega, ?_⟩
      · rw [hAA, hVp, hvl, hlvu]
      · rw [hq_lt _ (by omega), hcurq, hAA, hVp]
  · rw [h222] at hi'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
    · rw [hq_lt i (by omega), hq_lt i' hi', hlv_q i (by omega), hlv_q i' hi']
      exact hJ.mono i i' hii hi'
    · rw [hq _ htl', ite_eq_left rfl, hvl]
      rcases Nat.lt_or_ge i (c.nreg 222) with h | h
      · rw [hq_lt i h, hlv_q i h, ← hcurq]
        exact hspan i h hhp
      · rw [show i = c.nreg 222 by omega, hq _ htl', ite_eq_left rfl, hvl]
  · have e1 : rd c'.nmem bQ (c'.nreg 221 - 1) = c.nreg 223 := by
      rw [g221, hq_lt _ (by omega), hcurq]
    rw [e1, hlvu]
    rw [h222] at hi'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
    · rw [hq_lt i' hi', hlv_q i' hi', ← hcurq]; exact hspan i' hi' hhp
    · rw [hq _ htl', ite_eq_left rfl, hvl]
  · rw [h222] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [hq_lt i hi, hlv_q i hi]; exact hJ.lv_le i hi
    · rw [hq _ htl', ite_eq_left rfl, hvl]
      have := hJ.lv_le (c.nreg 221 - 1) (by omega)
      rw [hcurq] at this
      omega
  · rw [g223, g221, hq_lt _ (by omega)]; exact hJ.cur
  · rw [g224, g223, hlvu]; exact hJ.r224
  · rw [g221] at hi
    rw [hq_lt i (by omega)]
    intro x hx h1
    have hqi := hJ.q_lt i (by omega)
    obtain ⟨e1, e2⟩ := hJ.closed i hi x hx h1
    have hx' := hVn _ (hA x hx).1
    refine ⟨hmk_ge _ hx' e1, ?_⟩
    rw [hlv_m _ hx' e1, hlv_q i (by omega)]; exact e2
  · rw [g223] at h2 ⊢
    have hx' := hVn _ (hA x hx).1
    rcases Nat.lt_or_ge x j with h | h
    · rcases Nat.lt_or_ge p x with h' | h'
      · exact absurd h2 (hptr x h' h)
      · obtain rfl : x = p := by omega
        rw [hgv, hmk v htlv, ite_eq_left rfl, hvl, hlvu]; exact ⟨rfl, le_rfl⟩
    · obtain ⟨e1, e2⟩ := hJ.closed_cur x hx h h2
      refine ⟨hmk_ge _ hx' e1, ?_⟩
      rw [hlv_m _ hx' e1, hlvu]; exact e2

variable {bR bV bHd bNx : ℕ} {P : Input}
  (hF : BFix n K bR bV bLv bPr bMk bQ bHd bNx A V c₀)
  (hA : ∀ x < K, A x < K ∧ A (A x) = x) (hVn : ∀ x < K, V x < n)
  (hlay : bR + K ≤ bLv ∧ bV + K ≤ bLv ∧ bLv + n ≤ bPr ∧ bPr + n ≤ bMk ∧ bMk + n ≤ bQ ∧
    bQ + n ≤ bHd ∧ bHd + n ≤ bNx)
  (hW : bNx + K ≤ W)
include hF hA hVn hlay hW

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- One dart of the current vertex. -/
theorem bfsVisit_exec {j : ℕ} (c : Config) (hJ : VC n K bLv bPr bMk bQ A V W c₀ j c)
    (hp : c.nreg 225 = lastAt V K (c.nreg 223) j) (hpK : c.nreg 225 < K) :
    ∃ c' k, Exec P W bVisit c c' k ∧ VC n K bLv bPr bMk bQ A V W c₀ (c.nreg 225) c' ∧
      c'.nreg 225 = lastAt V K (c'.nreg 223) (c.nreg 225) ∧ c'.nreg 223 = c.nreg 223 ∧
      c'.nreg 221 = c.nreg 221 ∧ k ≤ 17 ∧ c.nreg 222 ≤ c'.nreg 222 ∧
      (∀ i < c.nreg 222, rd c'.nmem bQ i = rd c.nmem bQ i) := by
  have hc := hJ.wb
  have hjK := hJ.j_le
  have hr : ∀ r, r < 221 ∨ 230 ≤ r → c.nreg r = c₀.nreg r := hJ.regs
  have g141 : c.nreg 141 = 1 := (hr 141 (by omega)).trans hF.r141
  have g147 : c.nreg 147 = bR := (hr 147 (by omega)).trans hF.r147
  have g162 : c.nreg 162 = bV := (hr 162 (by omega)).trans hF.r162
  have g163 : c.nreg 163 = bLv := (hr 163 (by omega)).trans hF.r163
  have g215 : c.nreg 215 = bPr := (hr 215 (by omega)).trans hF.r215
  have g216 : c.nreg 216 = bMk := (hr 216 (by omega)).trans hF.r216
  have g217 : c.nreg 217 = bQ := (hr 217 (by omega)).trans hF.r217
  have g219 : c.nreg 219 = bNx := (hr 219 (by omega)).trans hF.r219
  have hhp := hJ.head_pos; have hhl := hJ.head_le; have htl := hJ.tail_le
  have hu := hJ.q_lt _ (show c.nreg 221 - 1 < c.nreg 222 by omega)
  rw [← hJ.cur] at hu
  generalize hpv : c.nreg 225 = p at hp hpK ⊢
  generalize huv : c.nreg 223 = u at hp hu ⊢
  have hJc := hJ.cur; rw [huv] at hJc
  obtain ⟨hpj, hVp, hmax⟩ : p < j ∧ V p = u ∧ ∀ y < j, V y = u → y ≤ p := by
    rcases lastAt_spec V K u j hjK with ⟨h1, -⟩ | ⟨h1, h2, h3⟩
    · omega
    · rw [← hp] at h1 h2 h3; exact ⟨h1, h2, h3⟩
  have hptr : ∀ x, p < x → x < j → V x ≠ u := fun x h1 h2 h3 => by
    have := hmax x h2 h3; omega
  have hAp := (hA p hpK).1
  have hv := hVn _ hAp
  have mA : c.nmem (bR + p) = A p := by
    rw [hJ.frame _ (Or.inl (by omega))]; exact hF.mA p hpK
  have mV : c.nmem (bV + A p) = V (A p) := by
    rw [hJ.frame _ (Or.inl (by omega))]; exact hF.mV _ hAp
  have mMk : c.nmem (bMk + V (A p)) = rd c.nmem bMk (V (A p)) := rfl
  have h224 : c.nreg 224 = rd c.nmem bLv u + 1 := by rw [hJ.r224, huv]
  have hlvu : rd c.nmem bLv u ≤ n := by
    rw [hJc]; have := hJ.lv_le _ (show c.nreg 221 - 1 < c.nreg 222 by omega); omega
  unfold bVisit
  refine spec_seq ?_
  exec_block
  all_goals try (config_simp; (try simp only [g147, hpv, mA, g162, mV, g216]); omega)
  rename_i hwb
  simp only [g147, hpv, mA, g162, mV, g216, mMk] at hwb ⊢
  refine spec_seq ?_
  rcases hJ.mk01 _ hv with hm | hm
  · -- a new vertex
    refine spec_ifLtN_true (by config_simp; rw [hm, g141]; omega) ?_
    have htl' : c.nreg 222 < n := hJ.tail_lt hv fun i hi e => by
      have := (hJ.mk_iff _ hv).2 ⟨i, hi, e⟩; omega
    have hnx : upd (upd (upd (upd c.nmem (bMk + V (A p)) 1) (bLv + V (A p)) (c.nreg 224))
        (bPr + V (A p)) (A p)) (bQ + c.nreg 222) (V (A p)) (bNx + p) = lastAt V K u p := by
      simp only [upd_apply]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), hJ.frame _ (Or.inr (Or.inr (by omega))), hF.mN p hpK, hVp]
    unfold bNew
    exec_block
    all_goals try (config_simp; (try simp only [g163, g215, g217, g141, g219, hpv]); omega)
    rename_i hwc
    simp only [g163, g215, g217, g141, g219, hpv] at hwc ⊢
    refine ⟨hJ.next_new hA hVn ⟨hlay.2.2.1, hlay.2.2.2.1, hlay.2.2.2.2.1⟩ hpK hpj
        (by rw [huv]; exact hVp) (by rw [huv]; exact hptr) hm ‹_› (fun r hr' => ?_)
        (by config_simp) rfl (by config_simp; rw [h224, huv]), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
    · config_simp; rw [hnx, huv]
    · config_simp; exact huv
    · config_simp
    · omega
    · config_simp; omega
    · intro i hi; config_simp; simp only [rd, upd_apply]; split_ifs <;> omega
  · refine spec_ifLtN_false (by config_simp; rw [hm, g141]; omega) ?_
    refine spec_skip ‹_› ?_
    have hm1 := (hJ.mk_iff _ hv).1 hm
    have hnx : c.nmem (bNx + p) = lastAt V K u p := by
      rw [hJ.frame _ (Or.inr (Or.inr (by omega))), hF.mN p hpK, hVp]
    exec_block
    · config_simp; rw [g219]; omega
    rename_i hwc
    simp only [g219, hpv, hnx] at hwc ⊢
    refine ⟨hJ.next_skip hpj (by rw [huv]; exact hVp) (by rw [huv]; exact hptr) ⟨hm, ?_⟩ ‹_›
      (fun r hr' => ?_) (by config_simp) (by config_simp), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨i, hi, e⟩ := hm1
      have := hJ.span i hi hhp
      rw [e, ← hJ.cur, huv] at this
      rw [huv]; exact this
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
    · config_simp; rw [huv]
    · config_simp; exact huv
    · config_simp
    · omega
    · config_simp; omega
    · intro i hi; config_simp

omit hA hVn in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- Dequeue the next vertex. -/
theorem bfsDeq_exec (c : Config) (hI : IS n K bLv bPr bMk bQ A V W c₀ c)
    (hlt : c.nreg 221 < c.nreg 222) :
    ∃ c' k, Exec P W bDeq c c' k ∧ VC n K bLv bPr bMk bQ A V W c₀ K c' ∧
      c'.nreg 225 = lastAt V K (c'.nreg 223) K ∧
      c'.nreg 221 = c.nreg 221 + 1 ∧ c'.nreg 222 = c.nreg 222 ∧ c'.nmem = c.nmem ∧
      c'.nreg 223 = rd c.nmem bQ (c.nreg 221) ∧ k = 8 := by
  have hc := hI.wb
  have hr := hI.regs
  have g141 : c.nreg 141 = 1 := (hr 141 (by omega)).trans hF.r141
  have g163 : c.nreg 163 = bLv := (hr 163 (by omega)).trans hF.r163
  have g217 : c.nreg 217 = bQ := (hr 217 (by omega)).trans hF.r217
  have g218 : c.nreg 218 = bHd := (hr 218 (by omega)).trans hF.r218
  have htl := hI.tail_le
  have hu := hI.q_lt _ hlt
  have hlu := hI.lv_le _ hlt
  have mq : c.nmem (bQ + c.nreg 221) = rd c.nmem bQ (c.nreg 221) := rfl
  have ml : c.nmem (bLv + rd c.nmem bQ (c.nreg 221)) =
      rd c.nmem bLv (rd c.nmem bQ (c.nreg 221)) := rfl
  have mh : c.nmem (bHd + rd c.nmem bQ (c.nreg 221)) =
      lastAt V K (rd c.nmem bQ (c.nreg 221)) K := by
    rw [hI.frame _ (Or.inr (Or.inr (by omega)))]; exact hF.mH _ hu
  have hspan' : ∀ i' < c.nreg 222, rd c.nmem bLv (rd c.nmem bQ i') ≤
      rd c.nmem bLv (rd c.nmem bQ (c.nreg 221)) + 1 := by
    intro i' hi'
    rcases Nat.eq_zero_or_pos (c.nreg 221) with h0 | h0
    · have := hI.t1 h0
      obtain rfl : i' = 0 := by omega
      rw [h0]; omega
    · have := hI.span i' hi' h0
      have := hI.mono (c.nreg 221 - 1) (c.nreg 221) (by omega) hlt
      omega
  unfold bDeq
  exec_block
  all_goals try (config_simp; (try simp only [g217, g163, g218, g141, mq, ml]); omega)
  rename_i hwb
  simp only [g217, g163, g218, g141, mq, ml, mh] at hwb ⊢
  refine ⟨⟨⟨‹_›, fun r hr' => ?_, by config_simp; exact hI.out, fun a ha => ?_,
    by config_simp; omega, by config_simp; exact hI.tail_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, by config_simp; omega, ?_, by config_simp, le_rfl, ?_,
    fun x hx h _ => absurd hx (by omega)⟩, by config_simp, by config_simp, by config_simp,
    by config_simp, by config_simp, by first | rfl | trivial⟩
  · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr'
  all_goals config_simp
  · exact hI.frame a ha
  · exact hI.q_lt
  · exact hI.q_inj
  · exact hI.q0
  · exact hI.mk01
  · exact hI.mk_iff
  · exact hI.lv0
  · exact hI.par
  · exact hI.mono
  · intro i' hi' _; rw [show c.nreg 221 + 1 - 1 = c.nreg 221 by omega]; exact hspan' i' hi'
  · exact hI.lv_le
  · intro h; exact h.elim
  · rw [show c.nreg 221 + 1 - 1 = c.nreg 221 by omega]
  · intro i hi; exact hI.closed i (by omega)

/-- One vertex: dequeue it and scan its darts. -/
theorem bfsBody_exec (c : Config) (hI : IS n K bLv bPr bMk bQ A V W c₀ c)
    (hlt : c.nreg 221 < c.nreg 222) :
    ∃ c' k, Exec P W bBody c c' k ∧ IS n K bLv bPr bMk bQ A V W c₀ c' ∧
      c'.nreg 221 = c.nreg 221 + 1 ∧
      k ≤ 19 * cntB V (rd c.nmem bQ (c.nreg 221)) K + 10 ∧
      c.nreg 222 ≤ c'.nreg 222 ∧ (∀ i < c.nreg 222, rd c'.nmem bQ i = rd c.nmem bQ i) := by
  obtain ⟨c₁, k₁, e₁, hJ₁, h225, h221, h222, hm, h223, rfl⟩ :=
    bfsDeq_exec hF hlay hW c hI hlt
  generalize hu : rd c.nmem bQ (c.nreg 221) = u at h223
  have hun : u < n := hu ▸ hI.q_lt _ hlt
  obtain ⟨c₂, k₂, e₂, ⟨⟨j, hJ₂, hp₂⟩, h223₂, h221₂, h222₂, hq₂⟩, hn₂, hk₂⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 225) (b := 220) (body := bVisit)
    (fun c' => (∃ j, VC n K bLv bPr bMk bQ A V W c₀ j c' ∧
      c'.nreg 225 = lastAt V K (c'.nreg 223) j) ∧ c'.nreg 223 = u ∧
      c'.nreg 221 = c.nreg 221 + 1 ∧ c₁.nreg 222 ≤ c'.nreg 222 ∧
      ∀ i < c₁.nreg 222, rd c'.nmem bQ i = rd c₁.nmem bQ i)
    (fun c' => 19 * remB V K u (c'.nreg 225)) (fun c' h => h.1.choose_spec.1.wb)
    (fun c' ⟨⟨j, hJ, hp⟩, g223, g221, g222, gq⟩ hlt' => by
      have g220 : c'.nreg 220 = K := (hJ.regs 220 (by omega)).trans hF.r220
      rw [g220] at hlt'
      obtain ⟨c'', k, e, hJ', f225, f223, f221, hk, f222, fq⟩ :=
        bfsVisit_exec hF hA hVn hlay hW c' hJ hp hlt'
      refine ⟨c'', k, e, ⟨⟨c'.nreg 225, hJ', f225⟩, by rw [f223, g223], by rw [f221, g221],
        by omega, fun i hi => by rw [fq i (by omega), gq i hi]⟩, ?_⟩
      have hjK := hJ.j_le
      obtain ⟨-, hVp, -⟩ : c'.nreg 225 < j ∧ V (c'.nreg 225) = u ∧ True := by
        rw [g223] at hp
        rcases lastAt_spec V K u j hjK with ⟨h1, -⟩ | ⟨h1, h2, -⟩
        · rw [← hp] at h1; omega
        · rw [← hp] at h1 h2; exact ⟨h1, h2, trivial⟩
      have e2 : remB V K u (c''.nreg 225) = cntB V u (c'.nreg 225) := by
        rw [f225, f223, g223]; exact remB_lastAt (le_of_lt hlt')
      have e3 : remB V K u (c'.nreg 225) = cntB V u (c'.nreg 225 + 1) := by
        rw [remB, ite_eq_left hlt']
      rw [e2, e3, cntB_succ_eq hVp]
      omega)
    ⟨⟨K, hJ₁, by rw [h225]⟩, h223, h221, le_rfl, fun _ _ => rfl⟩
  have hjK := hJ₂.j_le
  have g220 : c₂.nreg 220 = K := (hJ₂.regs 220 (by omega)).trans hF.r220
  rw [g220, hp₂, h223₂] at hn₂
  have hnone : ∀ y < j, V y ≠ u := by
    rcases lastAt_spec V K u j hjK with ⟨-, h2⟩ | ⟨h1, -, -⟩
    · exact h2
    · omega
  refine ⟨c₂, 8 + k₂, .seq e₁ e₂, ⟨hJ₂.toBS, fun i hi => ?_⟩, h221₂, ?_, by omega,
    fun i hi => by rw [hq₂ i (by omega), hm]⟩
  · rw [h221₂] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact hJ₂.closed i (by omega)
    · have : rd c₂.nmem bQ (c.nreg 221) = u := by rw [hq₂ _ (by omega), hm, hu]
      rw [this]
      intro x hx h1
      have hxj : j ≤ x := by by_contra h; exact hnone x (by omega) h1
      have := hJ₂.closed_cur x hx hxj (by rw [h223₂]; exact h1)
      rwa [h223₂] at this
  · rw [h225, h223, remB_lastAt le_rfl] at hk₂
    omega

/-- The total degree of the first `h` vertices of the queue. -/
def bsum (K bQ : ℕ) (V : ℕ → ℕ) (mem : ℕ → ℕ) (h : ℕ) : ℕ :=
  ∑ i ∈ range h, cntB V (rd mem bQ i) K

omit hF hA hVn hlay hW in
theorem BS.bsum_le {c : Config} (hI : BS n K bLv bPr bMk bQ A V W c₀ c) {h : ℕ}
    (hh : h ≤ c.nreg 222) : bsum K bQ V c.nmem h ≤ K := by
  unfold bsum
  rw [← sum_image (g := rd c.nmem bQ) (f := fun v => cntB V v K)
    (fun i hi j hj e => hI.q_inj i (by simp at hi; omega) j (by simp at hj; omega) e)]
  exact sum_cntB_le V _ K

omit hF hA hVn hW in
theorem IS_start (hn : 1 ≤ n) (hz : ∀ v < n, c₀.nmem (bMk + v) = 0) {c : Config}
    (hwb : WordsBounded W c) (hr : ∀ r, r < 221 ∨ 230 ≤ r → c.nreg r = c₀.nreg r)
    (h221 : c.nreg 221 = 0) (h222 : c.nreg 222 = 1) (ho : c.output = c₀.output)
    (hmem : ∀ a, c.nmem a =
      if a = bLv then 0 else if a = bQ then 0 else if a = bMk then 1 else c₀.nmem a) :
    IS n K bLv bPr bMk bQ A V W c₀ c := by
  have hq0 : rd c.nmem bQ 0 = 0 := by simp only [rd, hmem]; split_ifs <;> omega
  have hl0 : rd c.nmem bLv 0 = 0 := by simp only [rd, hmem]; split_ifs <;> omega
  have hmk : ∀ v < n, rd c.nmem bMk v = if v = 0 then 1 else 0 := fun v hv => by
    simp only [rd, hmem]; split_ifs <;> first | omega | exact hz v hv
  refine ⟨⟨hwb, hr, ho, fun a ha => ?_, by omega, by omega, fun i hi => ?_,
    fun i hi j hj _ => by omega, ⟨by omega, hq0⟩, fun v hv => ?_, fun v hv => ?_, hl0,
    fun i h1 h2 => by omega, fun i i' h1 h2 => ?_, fun i' _ h => by omega, fun i hi => ?_,
    fun _ => h222⟩, fun i hi => by omega⟩
  · rw [hmem]; split_ifs <;> omega
  · obtain rfl : i = 0 := by omega
    rw [hq0]; omega
  · rw [hmk v hv]; split_ifs <;> simp
  · rw [hmk v hv, h222]
    constructor
    · intro h; split_ifs at h with e
      exact ⟨0, by omega, by rw [hq0, e]⟩
    · rintro ⟨i, hi, e⟩; obtain rfl : i = 0 := by omega
      rw [hq0] at e; subst e; simp
  · obtain rfl : i' = 0 := by omega
    obtain rfl : i = 0 := by omega
    exact le_rfl
  · obtain rfl : i = 0 := by omega
    rw [hq0, hl0]

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The search.** -/
theorem bfsL_exec (hn : 1 ≤ n) (hz : ∀ v < n, c₀.nmem (bMk + v) = 0)
    (hc : WordsBounded W c₀) :
    ∃ c' t, Exec P W bfsL c₀ c' t ∧ t ≤ 12 * n + 19 * K + 7 ∧
      (∀ v < n, rd c'.nmem bMk v = 1 → Closed K bLv bMk A V c'.nmem v) ∧
      rd c'.nmem bMk 0 = 1 ∧ rd c'.nmem bLv 0 = 0 ∧
      (∀ v < n, rd c'.nmem bMk v = 1 → v ≠ 0 →
        rd c'.nmem bPr v < K ∧ V (rd c'.nmem bPr v) = v ∧
        rd c'.nmem bLv (V (A (rd c'.nmem bPr v))) + 1 = rd c'.nmem bLv v ∧
        rd c'.nmem bMk (V (A (rd c'.nmem bPr v))) = 1) ∧
      (∀ r, r < 221 ∨ 230 ≤ r → c'.nreg r = c₀.nreg r) ∧
      (∀ a, a < bLv ∨ (bLv + n ≤ a ∧ a < bPr) ∨ bQ + n ≤ a → c'.nmem a = c₀.nmem a) ∧
      c'.output = c₀.output := by
  have hmem : ∀ a, upd (upd (upd c₀.nmem bMk 1) bQ 0) bLv 0 a =
      if a = bLv then 0 else if a = bQ then 0 else if a = bMk then 1 else c₀.nmem a := by
    intro a; simp only [upd_apply]
  obtain ⟨c₁, k₁, e₁, hI₁, h221, rfl⟩ : ∃ c₁ k₁, Exec P W bStart c₀ c₁ k₁ ∧
      IS n K bLv bPr bMk bQ A V W c₀ c₁ ∧ c₁.nreg 221 = 0 ∧ k₁ = 5 := by
    unfold bStart
    exec_block
    rename_i hwb
    simp only [hF.r216, hF.r217, hF.r163, hF.r141, hF.r140, Nat.add_zero] at hwb ⊢
    refine ⟨IS_start hlay hn hz ‹_› (fun r hr => ?_) (by config_simp) (by config_simp)
      (by config_simp) (fun a => by config_simp; exact hmem a), by config_simp,
      by first | rfl | trivial⟩
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c', k', e, hI', hn', hk'⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 221)
    (b := 222) (body := bBody) (IS n K bLv bPr bMk bQ A V W c₀)
    (fun c => 12 * (n - c.nreg 221) + 19 * (K - bsum K bQ V c.nmem (c.nreg 221)))
    (fun c h => h.wb)
    (fun c₂ hI hlt => by
      obtain ⟨c₃, k₃, e₃, hI₃, g221, hk₃, g222, gq⟩ := bfsBody_exec hF hA hVn hlay hW c₂ hI hlt
      refine ⟨c₃, k₃, e₃, hI₃, ?_⟩
      have hd : bsum K bQ V c₃.nmem (c₃.nreg 221) = bsum K bQ V c₂.nmem (c₂.nreg 221) +
          cntB V (rd c₂.nmem bQ (c₂.nreg 221)) K := by
        rw [g221]; unfold bsum; rw [sum_range_succ, gq _ hlt]
        congr 1
        exact sum_congr rfl fun i hi => by rw [gq i (by simp at hi; omega)]
      have hle := hI₃.bsum_le (h := c₃.nreg 221) (by have := hI₃.head_le; omega)
      have := hI.tail_le
      omega) hI₁
  have hfin : c'.nreg 221 = c'.nreg 222 := by have := hI'.head_le; omega
  refine ⟨c', 5 + k', .seq e₁ e, by rw [h221] at hk'; simp [bsum] at hk'; omega,
    fun v hv h1 => ?_, ?_, hI'.lv0, fun v hv h1 h0 => ?_, hI'.regs, hI'.frame, hI'.out⟩
  · obtain ⟨i, hi, rfl⟩ := (hI'.mk_iff v hv).1 h1
    exact hI'.closed i (by omega)
  · rw [hI'.mk_iff 0 (by omega)]; exact ⟨0, hI'.q0.1, hI'.q0.2⟩
  · obtain ⟨i, hi, rfl⟩ := (hI'.mk_iff v hv).1 h1
    have hi1 : 1 ≤ i := by
      by_contra h; obtain rfl : i = 0 := by omega
      exact h0 hI'.q0.2
    obtain ⟨p1, p2, p3, i', hi', p4⟩ := hI'.par i hi1 hi
    refine ⟨p1, p2, p3, ?_⟩
    rw [hI'.mk_iff _ (hVn _ (hA _ p1).1)]
    exact ⟨i', by omega, p4⟩

end steps

section whole

variable {W : ℕ} {P : Input} {k n bR bV bLv bPr bMk bQ bHd bNx : ℕ} {A V : ℕ → ℕ}

/-- **Breadth-first search on the coded map.** From the reversals `A` at `bR` and the vertices
`V` at `bV` of the darts `x < 3 k`, within `19 n + 90 k + 14` steps: every marked vertex is
closed, `0` is marked at level `0`, and the parent dart of every marked vertex `v ≠ 0` lies at
`v` and leads one level down to a marked vertex. -/
theorem bprog_exec (hn : 1 ≤ n) (hA : ∀ x < 3 * k, A x < 3 * k ∧ A (A x) = x)
    (hVn : ∀ x < 3 * k, V x < n)
    (hlay : bR + 3 * k ≤ bLv ∧ bV + 3 * k ≤ bLv ∧ bLv + n ≤ bPr ∧ bPr + n ≤ bMk ∧
      bMk + n ≤ bQ ∧ bQ + n ≤ bHd ∧ bHd + n ≤ bNx)
    (hW : bNx + 3 * k ≤ W) (c : Config) (hc : WordsBounded W c) (h140 : c.nreg 140 = 0)
    (h141 : c.nreg 141 = 1) (h142 : c.nreg 142 = 3) (h143 : c.nreg 143 = k)
    (h147 : c.nreg 147 = bR) (h161 : c.nreg 161 = n) (h162 : c.nreg 162 = bV)
    (h163 : c.nreg 163 = bLv) (h215 : c.nreg 215 = bPr) (h216 : c.nreg 216 = bMk)
    (h217 : c.nreg 217 = bQ) (h218 : c.nreg 218 = bHd) (h219 : c.nreg 219 = bNx)
    (hAm : ∀ x < 3 * k, c.nmem (bR + x) = A x) (hVm : ∀ x < 3 * k, c.nmem (bV + x) = V x) :
    ∃ c' t, Exec P W bprog c c' t ∧ t ≤ 19 * n + 90 * k + 14 ∧
      (∀ v < n, rd c'.nmem bMk v = 1 → Closed (3 * k) bLv bMk A V c'.nmem v) ∧
      rd c'.nmem bMk 0 = 1 ∧ rd c'.nmem bLv 0 = 0 ∧
      (∀ v < n, rd c'.nmem bMk v = 1 → v ≠ 0 →
        rd c'.nmem bPr v < 3 * k ∧ V (rd c'.nmem bPr v) = v ∧
        rd c'.nmem bLv (V (A (rd c'.nmem bPr v))) + 1 = rd c'.nmem bLv v ∧
        rd c'.nmem bMk (V (A (rd c'.nmem bPr v))) = 1) ∧
      (∀ r, r < 220 ∨ 230 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bLv ∨ (bLv + n ≤ a ∧ a < bPr) ∨ bNx + 3 * k ≤ a → c'.nmem a = c.nmem a) ∧
      c'.output = c.output := by
  -- the counters
  obtain ⟨c₁, k₁, e₁, hw₁, g220, g221, gr₁, gm₁, go₁, rfl⟩ : ∃ c₁ k₁,
      Exec P W (block [.mulN 220 143 142, .copyN 221 140]) c c₁ k₁ ∧ WordsBounded W c₁ ∧
      c₁.nreg 220 = 3 * k ∧ c₁.nreg 221 = 0 ∧ (∀ r, r < 220 ∨ 222 ≤ r → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.output = c.output ∧ k₁ = 2 := by
    exec_block
    · rw [h143, h142]; omega
    refine ⟨‹_›, by config_simp; rw [h143, h142]; ring, by config_simp; exact h140,
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl, rfl, rfl⟩
  have f : ∀ r, r < 220 ∨ 222 ≤ r → c₁.nreg r = c.nreg r := gr₁
  -- the empty lists and the marks
  obtain ⟨c₂, k₂, e₂, hk₂, hz₂, gr₂, gm₂, go₂⟩ := ipass_exec (P := P) (n := n) (K := 3 * k)
    (bMk := bMk) (bHd := bHd) (by omega) (by omega) c₁ hw₁ ((f 140 (by omega)).trans h140)
    ((f 141 (by omega)).trans h141) ((f 161 (by omega)).trans h161)
    ((f 216 (by omega)).trans h216) ((f 218 (by omega)).trans h218) g220 g221
  have hw₂ := e₂.wb_right
  have f₂ : ∀ r, r < 220 ∨ 230 ≤ r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [gr₂ r (by omega), f r (by omega)]
  have m₂ : ∀ a, a < bMk ∨ (bMk + n ≤ a ∧ a < bHd) ∨ bHd + n ≤ a → c₂.nmem a = c.nmem a :=
    fun a ha => by rw [gm₂ a ha, gm₁]
  -- the lists
  obtain ⟨c₃, k₃, e₃, hk₃, hH₃, hN₃, gr₃, gm₃, go₃⟩ := lpass_exec (P := P) (n := n)
    (K := 3 * k) (bV := bV) (bHd := bHd) (bNx := bNx) (V := V) (by omega) hW c₂ hw₂
    ((f₂ 140 (by omega)).trans h140) ((f₂ 141 (by omega)).trans h141)
    ((f₂ 162 (by omega)).trans h162) ((f₂ 218 (by omega)).trans h218)
    ((f₂ 219 (by omega)).trans h219) (by rw [gr₂ 220 (by omega)]; exact g220)
    (fun x hx => ⟨by rw [m₂ _ (Or.inl (by omega))]; exact hVm x hx, hVn x hx⟩)
    (fun v hv => (hz₂ v hv).1)
  have hw₃ := e₃.wb_right
  have f₃ : ∀ r, r < 220 ∨ 230 ≤ r → c₃.nreg r = c.nreg r := fun r hr => by
    rw [gr₃ r (by omega), f₂ r hr]
  have hF : BFix n (3 * k) bR bV bLv bPr bMk bQ bHd bNx A V c₃ :=
    { r140 := (f₃ 140 (by omega)).trans h140, r141 := (f₃ 141 (by omega)).trans h141,
      r147 := (f₃ 147 (by omega)).trans h147, r162 := (f₃ 162 (by omega)).trans h162,
      r163 := (f₃ 163 (by omega)).trans h163, r215 := (f₃ 215 (by omega)).trans h215,
      r216 := (f₃ 216 (by omega)).trans h216, r217 := (f₃ 217 (by omega)).trans h217,
      r218 := (f₃ 218 (by omega)).trans h218, r219 := (f₃ 219 (by omega)).trans h219,
      r220 := by rw [gr₃ 220 (by omega), gr₂ 220 (by omega)]; exact g220
      mA := fun x hx => by
        rw [gm₃ _ (Or.inl (by omega)), m₂ _ (Or.inl (by omega))]; exact hAm x hx
      mV := fun x hx => by
        rw [gm₃ _ (Or.inl (by omega)), m₂ _ (Or.inl (by omega))]; exact hVm x hx
      mH := hH₃
      mN := hN₃ }
  obtain ⟨c', t, e, ht, hcl, h0, hl0, hpar, gr, gm, go⟩ := bfsL_exec (P := P) hF hA hVn hlay
    (by omega) hn (fun v hv => by rw [gm₃ _ (Or.inl (by omega))]; exact (hz₂ v hv).2) hw₃
  refine ⟨c', 2 + (k₂ + (k₃ + t)), .seq e₁ (.seq e₂ (.seq e₃ e)), by omega, hcl, h0, hl0,
    hpar, fun r hr => ?_, fun a ha => ?_, by rw [go, go₃, go₂, go₁]⟩
  · rcases Nat.lt_or_ge r 221 with h | h
    · rw [gr r (by omega)]; exact f₃ r (by omega)
    · rw [gr r (by omega)]; exact f₃ r (by omega)
  · rw [gm a (by omega), gm₃ a (by omega), m₂ a (by omega)]

end whole

/-! ### The breadth-first tree -/

section Bridge

open Map

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}
  {k n : ℕ} (cd : D ≃ Fin (3 * k)) (vi : Q ≃ Fin n) {A V : ℕ → ℕ}

omit [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] in
theorem revOk_of (hAcd : ∀ x, A (cd x) = cd (M.α x)) :
    ∀ x < 3 * k, A x < 3 * k ∧ A (A x) = x := fun x hx => by
  have e : x = cd (cd.symm ⟨x, hx⟩) := by simp
  rw [e, hAcd, hAcd, M.α_α]
  exact ⟨(cd _).2, rfl⟩

omit [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] in
theorem vlt_of (hV : ∀ x, V (cd x) = vi (M.vert x)) : ∀ x < 3 * k, V x < n := fun x hx => by
  have e : x = cd (cd.symm ⟨x, hx⟩) := by simp
  rw [e, hV]; exact (vi _).2

/-- **The breadth-first tree.** For a plane map coded by `cd` (reversals `A`, vertices `V`
read through a numbering `vi` of the vertices), the marks, levels and parent darts left by the
search (`bprog_exec`) are those of a breadth-first tree `T` rooted at the vertex numbered `0`:
every vertex is marked, the levels are the heights of `T`, and the parent darts its darts. -/
theorem bfs_tree (hM : M.IsPlane) (hn : 0 < n) (hAcd : ∀ x, A (cd x) = cd (M.α x))
    (hV : ∀ x, V (cd x) = vi (M.vert x)) {mem : ℕ → ℕ} {bLv bPr bMk : ℕ}
    (hcl : ∀ v < n, rd mem bMk v = 1 → Closed (3 * k) bLv bMk A V mem v)
    (h0 : rd mem bMk 0 = 1) (hl0 : rd mem bLv 0 = 0)
    (hpar : ∀ v < n, rd mem bMk v = 1 → v ≠ 0 →
      rd mem bPr v < 3 * k ∧ V (rd mem bPr v) = v ∧
      rd mem bLv (V (A (rd mem bPr v))) + 1 = rd mem bLv v) :
    ∃ T : M.SpTree, T.root = vi.symm ⟨0, hn⟩ ∧ IsBFS T ∧
      (∀ v, rd mem bLv (vi v) = T.height v) ∧
      ∀ v (h : v ≠ T.root), (cd (T.par v h) : ℕ) = rd mem bPr (vi v) := by
  have hVA : ∀ x, V (A (cd x)) = vi (M.vert (M.α x)) := fun x => by rw [hAcd, hV]
  -- every vertex is marked
  have hall : ∀ v : Q, rd mem bMk (vi v) = 1 := by
    obtain ⟨d₀, hd₀⟩ := hM.exists_dart (vi.symm ⟨0, hn⟩)
    have hm0 : rd mem bMk (vi (M.vert d₀)) = 1 := by rw [hd₀]; simpa using h0
    have key : ∀ b, Relation.ReflTransGen (fun a b => ∃ d' : D, M.vert d' = a ∧
        M.vert (M.α d') = b) (M.vert d₀) b → rd mem bMk (vi b) = 1 := by
      intro b hb
      induction hb with
      | refl => exact hm0
      | @tail a b _ hab ih =>
        obtain ⟨e, rfl, rfl⟩ := hab
        have := (hcl _ (vi _).2 ih (cd e) (cd e).2 (hV e)).1
        rwa [hVA] at this
    intro v
    obtain ⟨d, rfl⟩ := hM.exists_dart v
    exact key _ (hM.connected.reach_vert d₀ d)
  have hne : ∀ v, v ≠ vi.symm ⟨0, hn⟩ → (vi v : ℕ) ≠ 0 := fun v h e => h (by
    rw [Equiv.eq_symm_apply]; exact Fin.ext e)
  have hp : ∀ v (h : v ≠ vi.symm ⟨0, hn⟩), rd mem bPr (vi v) < 3 * k ∧
      V (rd mem bPr (vi v)) = vi v ∧
      rd mem bLv (V (A (rd mem bPr (vi v)))) + 1 = rd mem bLv (vi v) :=
    fun v h => hpar _ (vi v).2 (hall v) (hne v h)
  have hcd : ∀ v (h : v ≠ vi.symm ⟨0, hn⟩),
      cd (cd.symm ⟨rd mem bPr (vi v), (hp v h).1⟩) = ⟨rd mem bPr (vi v), (hp v h).1⟩ :=
    fun v h => by simp
  have hvert : ∀ v (h : v ≠ vi.symm ⟨0, hn⟩),
      M.vert (cd.symm ⟨rd mem bPr (vi v), (hp v h).1⟩) = v := fun v h => by
    apply vi.injective; apply Fin.ext
    rw [← hV, hcd v h]; exact (hp v h).2.1
  have hht : ∀ v (h : v ≠ vi.symm ⟨0, hn⟩),
      rd mem bLv (vi (M.vert (M.α (cd.symm ⟨rd mem bPr (vi v), (hp v h).1⟩)))) + 1 =
        rd mem bLv (vi v) := fun v h => by
    rw [← hVA, hcd v h]; exact (hp v h).2.2
  let T : M.SpTree :=
    { root := vi.symm ⟨0, hn⟩
      par := fun v h => cd.symm ⟨rd mem bPr (vi v), (hp v h).1⟩
      height := fun v => rd mem bLv (vi v)
      vert_par := hvert
      height_lt := fun v h => by have := hht v h; omega }
  refine ⟨T, rfl, ⟨fun d => ?_, fun v h => hht v h, by simpa [T] using hl0⟩, fun v => rfl,
    fun v h => by simp [T]⟩
  have := (hcl _ (vi _).2 (hall (M.vert d)) (cd d) (cd d).2 (hV d)).2
  rwa [hVA] at this

/-- **Breadth-first search on the machine.** For a plane map coded by `cd` (the reversals `A`
at `bR`, the vertices `V` at `bV`, read through a numbering `vi` of its `n ≥ 1` vertices), the
program `bprog` ends within `19 n + 90 k + 14` steps with the heights of a breadth-first tree
`T` rooted at the vertex numbered `0` at `bLv` and its parent darts at `bPr`. -/
theorem bprog_tree {W : ℕ} {P' : Input} {bR bV bLv bPr bMk bQ bHd bNx : ℕ} (hM : M.IsPlane)
    (hn : 0 < n) (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hV : ∀ x, V (cd x) = vi (M.vert x))
    (hlay : bR + 3 * k ≤ bLv ∧ bV + 3 * k ≤ bLv ∧ bLv + n ≤ bPr ∧ bPr + n ≤ bMk ∧
      bMk + n ≤ bQ ∧ bQ + n ≤ bHd ∧ bHd + n ≤ bNx)
    (hW : bNx + 3 * k ≤ W) (c : Config) (hc : WordsBounded W c) (h140 : c.nreg 140 = 0)
    (h141 : c.nreg 141 = 1) (h142 : c.nreg 142 = 3) (h143 : c.nreg 143 = k)
    (h147 : c.nreg 147 = bR) (h161 : c.nreg 161 = n) (h162 : c.nreg 162 = bV)
    (h163 : c.nreg 163 = bLv) (h215 : c.nreg 215 = bPr) (h216 : c.nreg 216 = bMk)
    (h217 : c.nreg 217 = bQ) (h218 : c.nreg 218 = bHd) (h219 : c.nreg 219 = bNx)
    (hAm : ∀ x < 3 * k, c.nmem (bR + x) = A x) (hVm : ∀ x < 3 * k, c.nmem (bV + x) = V x) :
    ∃ c' t, Exec P' W bprog c c' t ∧ t ≤ 19 * n + 90 * k + 14 ∧
      (∃ T : M.SpTree, T.root = vi.symm ⟨0, hn⟩ ∧ IsBFS T ∧
        (∀ v, c'.nmem (bLv + vi v) = T.height v) ∧
        ∀ v (h : v ≠ T.root), (cd (T.par v h) : ℕ) = c'.nmem (bPr + vi v)) ∧
      (∀ r, r < 220 ∨ 230 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bLv ∨ (bLv + n ≤ a ∧ a < bPr) ∨ bNx + 3 * k ≤ a → c'.nmem a = c.nmem a) ∧
      c'.output = c.output := by
  obtain ⟨c', t, e, ht, hcl, h0, hl0, hpar, gr, gm, go⟩ := bprog_exec (P := P') hn
    (revOk_of cd hAcd) (vlt_of cd vi hV) hlay hW c hc h140 h141 h142 h143 h147 h161 h162 h163
    h215 h216 h217 h218 h219 hAm hVm
  exact ⟨c', t, e, ht, bfs_tree cd vi hM hn hAcd hV hcl h0 hl0
    fun v hv h1 h2 => ⟨(hpar v hv h1 h2).1, (hpar v hv h1 h2).2.1, (hpar v hv h1 h2).2.2.1⟩,
    gr, gm, go⟩

end Bridge

end MillerProg

end PlanarSeparator
