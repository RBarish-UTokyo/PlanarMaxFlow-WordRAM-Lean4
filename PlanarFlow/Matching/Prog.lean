module

public import PlanarFlow.Matching.Spec

/-!
# Maximum bipartite matching on the machine: the program and the search state

The program repeats *phases*. A phase marks the free white vertices, puts them in a queue, and
searches the graph along alternating paths: a white vertex `w` taken from the queue visits every
unvisited black vertex `b` at the end of one of its arcs, recording `w` as the parent of `b`; if
`b` is free, the search stops and the matching is augmented along the path `b, par b, mate
(par b), …` back to a free white vertex; otherwise the mate of `b` is visited and queued. Every
visited vertex gets a time stamp; along the path the time stamps decrease. A phase that finds no
free black vertex leaves König's certificate (`PlanarFlow.BM.card_le_size`): the matching is
maximum, and its size is printed.

Memory: mates at `v` (`u + 1` for the mate `u`, `0` if free), visit marks at `n + v`, parents at
`2n + v`, time stamps at `3n + v`, the queue at `4n + k`.
Registers: `r1 = 1`, `r2 = n`, `r4 = n + 2`, `r5 = 2n + 3`, `r6 = 2`, `r8 = 2n`, `r9 = 3n`,
`r10 = 4n`; `r20` the size of the matching, `r21` the flag of the outer loop, `r22` the head of
the queue, `r23` its tail, `r24` the clock, `r25` the free black vertex found (`b + 1`, or `0`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BM

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

lemma word_inp (d : List ℕ) (i : ℕ) : (inp d).data.getD i 0 = word d i := rfl

/-! ### The program -/

/-- Constants. -/
def setup : Stmt := block [.constN 1 1, .readIn 2 0, .constN 6 2, .addN 4 2 6, .addN 5 2 2,
  .addN 5 5 6, .addN 5 5 1, .addN 8 2 2, .addN 9 8 2, .addN 10 9 2, .constN 21 1, .copyN 20 0]

/-- Queue the vertex `r22`. -/
def enq : Stmt := block [.storeN 26 1, .addN 27 10 23, .storeN 27 22, .addN 27 9 22, .storeN 27 24,
  .addN 24 24 1, .addN 23 23 1]

/-- Clear the mark of `r22`; queue it if it is a free white vertex. -/
def clearBody : Stmt :=
  .seq (block [.addN 26 2 22, .storeN 26 0, .addN 27 22 6, .readIn 28 27, .loadN 29 22])
    (.seq (.ifLtN 0 28 (.ifLtN 0 29 .skip enq) .skip) (.instr (.addN 22 22 1)))

/-- Queue the white mate `r36` of a visited black vertex if it is new. -/
def enqW : Stmt := block [.storeN 27 1, .addN 27 10 23, .storeN 27 36, .addN 27 9 36, .storeN 27 24,
  .addN 24 24 1, .addN 23 23 1]

/-- Visit the black vertex `r33` from `r30`. -/
def visitB : Stmt :=
  .seq (block [.storeN 26 1, .addN 27 8 33, .storeN 27 30, .addN 27 9 33, .storeN 27 24,
      .addN 24 24 1, .loadN 35 33])
    (.ifLtN 0 35 (.seq (block [.subN 36 35 1, .addN 27 2 36, .loadN 37 27])
        (.ifLtN 37 1 enqW .skip))
      (block [.addN 25 33 1, .copyN 31 32, .copyN 22 23]))

/-- The arc `r31` of the white vertex `r30`. -/
def scanArc : Stmt :=
  .seq (block [.addN 26 31 5, .readIn 33 26, .addN 26 2 33, .loadN 34 26])
    (.seq (.ifLtN 34 1 visitB .skip) (.instr (.addN 31 31 1)))

/-- Take the next white vertex `r30` from the queue; its arcs are `r31 … r32 - 1`. -/
def deq : Stmt := block [.addN 26 10 22, .loadN 30 26, .addN 22 22 1, .addN 26 30 4, .readIn 31 26,
  .addN 26 26 1, .readIn 32 26]

/-- One step of the augmentation from the black vertex `r39 - 1`. -/
def augBody : Stmt := block [.subN 38 39 1, .addN 27 8 38, .loadN 40 27, .loadN 41 40,
  .addN 42 38 1, .storeN 40 42, .addN 42 40 1, .storeN 38 42, .copyN 39 41]

/-- The end of a phase: augment, or stop. -/
def finish : Stmt :=
  .ifLtN 0 25 (.seq (.instr (.copyN 39 25)) (.seq (.whileLtN 0 39 augBody)
    (.instr (.addN 20 20 1)))) (.instr (.copyN 21 0))

/-- A phase. -/
def phase : Stmt :=
  .seq (block [.copyN 22 0, .copyN 23 0, .copyN 24 0, .copyN 25 0]) <|
  .seq (.whileLtN 22 2 clearBody) <| .seq (.instr (.copyN 22 0)) <|
  .seq (.whileLtN 22 23 (.seq deq (.whileLtN 31 32 scanArc))) finish

/-- **The maximum matching program.** -/
def prog : Stmt := .seq setup (.seq (.whileLtN 0 21 phase) (.instr (.outN 20)))

/-! ### Registers and memory -/

/-- The constant registers. -/
def Regs (d : List ℕ) (c : Config) : Prop :=
  c.nreg 0 = 0 ∧ c.nreg 1 = 1 ∧ c.nreg 2 = nn d ∧ c.nreg 4 = nn d + 2 ∧
    c.nreg 5 = 2 * nn d + 3 ∧ c.nreg 6 = 2 ∧ c.nreg 8 = 2 * nn d ∧ c.nreg 9 = 3 * nn d ∧
    c.nreg 10 = 4 * nn d

theorem regs_of {d : List ℕ} {c c' : Config} (hR : Regs d c) (h : ∀ r < 20, c'.nreg r = c.nreg r) :
    Regs d c' := by
  obtain ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ := hR
  exact ⟨(h 0 (by omega)).trans h0, (h 1 (by omega)).trans h1, (h 2 (by omega)).trans h2,
    (h 4 (by omega)).trans h4, (h 5 (by omega)).trans h5, (h 6 (by omega)).trans h6,
    (h 8 (by omega)).trans h8, (h 9 (by omega)).trans h9, (h 10 (by omega)).trans h10⟩

/-- Visit marks. -/
def vs (d : List ℕ) (m : ℕ → ℕ) (v : ℕ) : ℕ := m (nn d + v)
/-- Parents. -/
def pa (d : List ℕ) (m : ℕ → ℕ) (v : ℕ) : ℕ := m (2 * nn d + v)
/-- Time stamps. -/
def tmv (d : List ℕ) (m : ℕ → ℕ) (v : ℕ) : ℕ := m (3 * nn d + v)
/-- The queue. -/
def qu (d : List ℕ) (m : ℕ → ℕ) (k : ℕ) : ℕ := m (4 * nn d + k)

/-- The number of visited vertices. -/
def nvis (d : List ℕ) (m : ℕ → ℕ) : ℕ := ((range (nn d)).filter fun v => vs d m v = 1).card

/-! ### The state of the search

`BS d μ D m head tail t found`: the matching is `μ` (stored at `0 … n-1`), the white vertices `D`
have had all their arcs scanned, the queue holds `qu 0, …, qu (tail - 1)`, the clock is `t`. -/

/-- The state of the search. -/
structure BS (d : List ℕ) (μ : ℕ → ℕ) (D : ℕ → Prop) (m : ℕ → ℕ) (tail t found : ℕ) : Prop where
  mate : ∀ v < nn d, m v = μ v
  vis01 : ∀ v < nn d, vs d m v = 0 ∨ vs d m v = 1
  tl : tail ≤ nn d
  q : ∀ k < tail, qu d m k < nn d ∧ col d (qu d m k) = 1 ∧ vs d m (qu d m k) = 1
  qinj : ∀ k < tail, ∀ l < tail, qu d m k = qu d m l → k = l
  wvis : ∀ w < nn d, col d w = 1 → vs d m w = 1 → ∃ k < tail, qu d m k = w
  free : ∀ w < nn d, col d w = 1 → μ w = 0 → vs d m w = 1
  cl : found = 0 → ∀ w b, D w → Arc d w b → vs d m b = 1
  bvis : ∀ b < nn d, col d b = 0 → vs d m b = 1 → pa d m b < nn d ∧ vs d m (pa d m b) = 1 ∧
    Arc d (pa d m b) b ∧ tmv d m (pa d m b) < tmv d m b ∧ (μ b = 0 → found = b + 1) ∧
    (μ b ≠ 0 → vs d m (μ b - 1) = 1)
  wmat : ∀ w < nn d, col d w = 1 → vs d m w = 1 → μ w ≠ 0 →
    vs d m (μ w - 1) = 1 ∧ tmv d m (μ w - 1) < tmv d m w
  tmlt : ∀ v < nn d, vs d m v = 1 → tmv d m v < t
  tcnt : t = nvis d m
  fnd : found ≠ 0 → found - 1 < nn d ∧ col d (found - 1) = 0 ∧ vs d m (found - 1) = 1 ∧
    μ (found - 1) = 0

variable {d : List ℕ} {W : ℕ}

lemma nvis_le (m : ℕ → ℕ) : nvis d m ≤ nn d := by
  unfold nvis; exact (card_filter_le _ _).trans (by simp)

/-- Marking an unmarked vertex raises the number of marked vertices by one. -/
lemma nvis_mark {m m' : ℕ → ℕ} {x : ℕ} (hx : x < nn d) (h0 : vs d m x = 0) (h1 : vs d m' x = 1)
    (heq : ∀ v < nn d, v ≠ x → vs d m' v = vs d m v) : nvis d m' = nvis d m + 1 := by
  unfold nvis
  rw [← card_insert_of_notMem (s := (range (nn d)).filter fun v => vs d m v = 1) (a := x)
    (by simp [h0])]
  congr 1; ext v
  simp only [mem_filter, mem_range, mem_insert]
  by_cases hv : v = x
  · subst hv; simp [h1, hx]
  · by_cases hvn : v < nn d
    · rw [heq v hvn hv]; simp [hv, hvn]
    · simp [hv, hvn]

end BM

end PlanarFlow
