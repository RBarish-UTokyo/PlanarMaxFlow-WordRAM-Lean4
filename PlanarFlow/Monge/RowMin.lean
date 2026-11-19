module

public import WordRAM
public import PlanarFlow.Monge.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Nat.Log

/-!
# Row minima of a totally monotone matrix on the machine

`rowMin ent` computes the leftmost minimum of every row of an `m × n` totally monotone matrix
`A` whose entries are produced by the statement `ent` (an *entry oracle*: from the row `i` in
`r70` and the column `j` in `r71` it leaves `A i j` in the real register `r70`; `EntSpec`). The
entries may be stored in memory or computed from memory arrays (for example `d i + w i j`).

The algorithm is the divide and conquer of Aggarwal, Klawe, Moran, Shor and Wilber, in an
iterative form. Number the rows `1, …, m` (row `r` is the row `r - 1` of `A`). At level
`s = 2 ^ t` (from the largest power of two `≤ m` down to `1`) the rows `r = s, 3s, 5s, …` are
processed from left to right: the leftmost minimum of row `r` lies between those of the rows
`r - s` and `r + s`, both multiples of `2s` and known from the earlier levels
(`PlanarFlow.Monge.IsTotMono.lmin_mono`), so a scan of that window finds it
(`PlanarFlow.Monge.lmin_eq_of_window`). The windows of one level overlap only at their ends, so
a level costs `O(n + rows)` entry evaluations, and the whole run `O(n log m + m)`.

Results: for every row `i < m`, the position `lmin n A i` at `pb + i + 1` of the natural memory
and the value `A i (lmin n A i)` at `pb + i + 1` of the real memory.

**`PlanarFlow.Monge.rowMin_exec`.** With `m, n ≥ 1` in `r60, r61`, the output base `pb` in `r62`,
`pb + 3m + n + 2 ≤ W` and an entry oracle of cost `≤ E`, `rowMin ent` runs within
`((E + 6) n + 8) (log₂ m + 1) + (E + 22) m + 8` steps, writes the row minima, and changes nothing
else outside the registers `r60 … r79`, the registers the oracle may use (`≥ 80`) and the output
cells (`Agree`).

Registers: `r60 = m`, `r61 = n`, `r62 = pb` (inputs, kept), `r63 = 1`, `r64 = 2`, `r65 = s`,
`r67 = m + 1`, `r68` the row `r`, `r69` the left end of its window, `r72 = 2s`, `r73 = r + s`,
`r74` an address, `r75` the right end of the window, `r70 = r - 1` and `r71 = j` (the arguments
of the oracle), `r76` the position and the real `r71` the value of the best entry so far,
`r77 = r75 + 1`.

## References

* A. Aggarwal, M. M. Klawe, S. Moran, P. Shor, R. Wilber, *Geometric applications of a
  matrix-searching algorithm*, Algorithmica 2 (1987), 195–208.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The program -/

/-- One step of the scan of a window. -/
def scanBody (ent : Stmt) : Stmt :=
  .seq ent (.seq (.ifLtR 70 71 (block [.copyR 71 70, .copyN 76 71]) .skip)
    (.instr (.addN 71 71 63)))

/-- The right end of the window of row `r68`: the position of row `r68 + r65`, or `n - 1`. -/
def hiS : Stmt := .ifLtN 73 67 (block [.addN 74 62 73, .loadN 75 74]) (block [.subN 75 61 63])

/-- One row of a level. -/
def rowBody (ent : Stmt) : Stmt :=
  .seq (.instr (.addN 73 68 65)) <| .seq hiS <| .seq (block [.subN 70 68 63, .copyN 71 69]) <|
  .seq ent <| .seq (block [.copyR 71 70, .copyN 76 71, .addN 71 71 63, .addN 77 75 63]) <|
  .seq (.whileLtN 71 77 (scanBody ent)) <|
  block [.addN 74 62 68, .storeN 74 76, .storeR 74 71, .copyN 69 75, .addN 68 68 72]

/-- One level: halve `s` and process the rows `s, 3s, 5s, …`. -/
def levelBody (ent : Stmt) : Stmt :=
  .seq (block [.divN 65 65 64, .copyN 68 65, .constN 69 0, .addN 72 65 65])
    (.whileLtN 68 67 (rowBody ent))

/-- **Row minima of a totally monotone matrix.** -/
def rowMin (ent : Stmt) : Stmt :=
  .seq (block [.constN 63 1, .constN 64 2, .constN 65 1, .addN 67 60 63]) <|
  .seq (.whileLtN 65 67 (.instr (.addN 65 65 65))) <|
  .whileLtN 63 65 (levelBody ent)

/-! ### The interface -/

/-- `c` agrees with `c₀` on the registers below `60`, on the memory outside the output cells
`pb + 1, …, pb + m`, and on the output. -/
def Agree (pb m : ℕ) (c₀ c : Config) : Prop :=
  (∀ r < 60, c.nreg r = c₀.nreg r) ∧ (∀ r < 60, c.rreg r = c₀.rreg r) ∧
    (∀ a, (a ≤ pb ∨ pb + m < a) → c.nmem a = c₀.nmem a) ∧
    (∀ a, (a ≤ pb ∨ pb + m < a) → c.rmem a = c₀.rmem a) ∧ c.output = c₀.output

theorem Agree.refl (pb m : ℕ) (c : Config) : Agree pb m c c :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem Agree.of_eq {pb m : ℕ} {c₀ c c' : Config} (h : Agree pb m c₀ c)
    (hn : ∀ r < 60, c'.nreg r = c.nreg r) (hr : ∀ r < 60, c'.rreg r = c.rreg r)
    (hnm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) :
    Agree pb m c₀ c' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨fun r hr' => (hn r hr').trans (h1 r hr'), fun r hr' => (hr r hr').trans (h2 r hr'),
    fun a ha => by rw [hnm]; exact h3 a ha, fun a ha => by rw [hrm]; exact h4 a ha, ho.trans h5⟩

/-- The entry oracle: from any configuration agreeing with `c₀`, with a row `< m` in `r70` and a
column `< n` in `r71`, `ent` leaves the entry in the real register `r70` within `E` steps,
changing only the registers from `80` on and the real register `r70`. -/
def EntSpec (P : Input) (W : ℕ) (ent : Stmt) (A : ℕ → ℕ → ℝ) (E m n pb : ℕ) (c₀ : Config) :
    Prop :=
  ∀ c, WordsBounded W c → Agree pb m c₀ c → c.nreg 70 < m → c.nreg 71 < n →
    ∃ c' k, Exec P W ent c c' k ∧ k ≤ E ∧ c'.rreg 70 = A (c.nreg 70) (c.nreg 71) ∧
      (∀ r < 80, c'.nreg r = c.nreg r) ∧ (∀ r < 80, r ≠ 70 → c'.rreg r = c.rreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output

/-- Read a register of an explicitly updated register file away from the updated registers. -/
macro "upd_tac" : tactic => `(tactic| (simp only [upd_apply]; split_ifs <;> first | rfl | omega))

/-- A `whileLtN` loop with a potential, on a spec goal. -/
theorem spec_while {P : Input} {W : ℕ} {a b : ℕ} {body : Stmt} {c : Config}
    {Q : Config → ℕ → Prop} (I : Config → Prop) (Φ : Config → ℕ)
    (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c)
    (hc : I c) (hQ : ∀ c' k, I c' → ¬ c'.nreg a < c'.nreg b → k ≤ Φ c + 2 → Q c' k) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ Q c' k := by
  obtain ⟨c', k, e, hI', hn, hk⟩ := Exec.whileLtN_potential I Φ hI hbody hc
  exact ⟨c', k, e, hQ c' k hI' hn hk⟩

lemma mul_pred_add {a x : ℕ} (h : 1 ≤ x) : a * (x - 1) + a = a * x := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one]

/-! ### The scan of a window -/

variable {P : Input} {W : ℕ} {ent : Stmt} {A : ℕ → ℕ → ℝ} {E m n pb : ℕ} {c₀ : Config}

/-- The state of the scan of the window `[lo, hi]` of row `i`, started from `c₁`. -/
structure IS (W : ℕ) (A : ℕ → ℕ → ℝ) (c₁ : Config) (i lo hi : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  nreg : ∀ r < 80, r ≠ 71 → r ≠ 76 → c.nreg r = c₁.nreg r
  rreg : ∀ r < 80, r ≠ 70 → r ≠ 71 → c.rreg r = c₁.rreg r
  nmem : c.nmem = c₁.nmem
  rmem : c.rmem = c₁.rmem
  out : c.output = c₁.output
  j_gt : lo < c.nreg 71
  j_le : c.nreg 71 ≤ hi + 1
  best : IsLMin (A i) lo (c.nreg 71 - 1) (c.nreg 76)
  val : c.rreg 71 = A i (c.nreg 76)

theorem scanBody_exec (hent : EntSpec P W ent A E m n pb c₀) {c₁ : Config} {i lo hi : ℕ}
    (hA : Agree pb m c₀ c₁) (h70 : c₁.nreg 70 = i) (h63 : c₁.nreg 63 = 1)
    (h77 : c₁.nreg 77 = hi + 1) (hi_m : i < m) (hhi : hi < n) (hnW : n + 1 ≤ W)
    (c : Config) (hI : IS W A c₁ i lo hi c) (hlt : c.nreg 71 < c.nreg 77) :
    ∃ c' k, Exec P W (scanBody ent) c c' k ∧ IS W A c₁ i lo hi c' ∧
      (E + 6) * (hi + 1 - c'.nreg 71) + k + 2 ≤ (E + 6) * (hi + 1 - c.nreg 71) := by
  have hc := hI.wb
  rw [hI.nreg 77 (by omega) (by omega) (by omega), h77] at hlt
  have hAc : Agree pb m c₀ c := hA.of_eq (fun r hr => hI.nreg r (by omega) (by omega) (by omega))
    (fun r hr => hI.rreg r (by omega) (by omega) (by omega)) hI.nmem hI.rmem hI.out
  have h70c : c.nreg 70 = i := (hI.nreg 70 (by omega) (by omega) (by omega)).trans h70
  have h63c : c.nreg 63 = 1 := (hI.nreg 63 (by omega) (by omega) (by omega)).trans h63
  have hj := hI.j_gt
  unfold scanBody
  refine spec_seq ?_
  refine spec_use (hent c hc hAc (by omega) (by omega)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hv, hn₂, hr₂, hnm₂, hrm₂, ho₂⟩
  rw [h70c] at hv
  have h71 : c₂.nreg 71 = c.nreg 71 := hn₂ 71 (by omega)
  have h76 : c₂.nreg 76 = c.nreg 76 := hn₂ 76 (by omega)
  have hb : c₂.rreg 71 = c.rreg 71 := hr₂ 71 (by omega) (by omega)
  have hbest := hI.best
  have hj1 : c.nreg 71 - 1 + 1 = c.nreg 71 := by omega
  -- the frame of the whole step
  have hfin : ∀ (c' : Config), WordsBounded W c' →
      (∀ r < 80, r ≠ 71 → r ≠ 76 → c'.nreg r = c₂.nreg r) →
      (∀ r < 80, r ≠ 70 → r ≠ 71 → c'.rreg r = c₂.rreg r) → c'.nmem = c₂.nmem →
      c'.rmem = c₂.rmem → c'.output = c₂.output → c'.nreg 71 = c.nreg 71 + 1 →
      IsLMin (A i) lo (c.nreg 71) (c'.nreg 76) → c'.rreg 71 = A i (c'.nreg 76) →
      IS W A c₁ i lo hi c' := by
    intro c' hw' hn' hr' hnm' hrm' ho' hj' hb' hv'
    refine ⟨hw', fun r hr a b => ?_, fun r hr a b => ?_, by rw [hnm', hnm₂, hI.nmem],
      by rw [hrm', hrm₂, hI.rmem], by rw [ho', ho₂, hI.out], by omega, by omega,
      by rw [hj', Nat.add_sub_cancel]; exact hb', hv'⟩
    · rw [hn' r hr a b, hn₂ r hr, hI.nreg r hr a b]
    · rw [hr' r hr a b, hr₂ r hr (by omega), hI.rreg r hr a b]
  by_cases hcmp : A i (c.nreg 71) < A i (c.nreg 76)
  · refine spec_seq ?_
    refine spec_ifLtR_true (by rw [hv, hb, hI.val]; exact hcmp) ?_
    exec_block
    refine spec_instr (Exec.addN ‹_› _ _ _ ?_) fun hw₃ => ?_
    · config_simp; rw [h71, hn₂ 63 (by omega), h63c]; omega
    refine ⟨hfin _ hw₃ (fun r hr a b => ?_) (fun r hr a b => ?_) rfl rfl rfl ?_ ?_ ?_, ?_⟩
    · config_simp; rw [upd_other _ _ _ a, upd_other _ _ _ b]
    · config_simp; rw [upd_other _ _ _ b]
    · config_simp; rw [h71, hn₂ 63 (by omega), h63c]
    · config_simp; rw [h71]
      have := hbest.scan_succ_lt (hi := c.nreg 71 - 1) (by rw [hj1]; exact hcmp)
      rwa [hj1] at this
    · config_simp; rw [h71]; exact hv
    · config_simp; rw [h71, hn₂ 63 (by omega), h63c]
      have := mul_pred_add (a := E + 6) (x := hi + 1 - c.nreg 71) (by omega)
      rw [show hi + 1 - (c.nreg 71 + 1) = hi + 1 - c.nreg 71 - 1 by omega]
      omega
  · refine spec_seq ?_
    refine spec_ifLtR_false (by rw [hv, hb, hI.val]; exact hcmp) ?_
    refine spec_skip hw₂ ?_
    refine spec_instr (Exec.addN hw₂ _ _ _ ?_) fun hw₃ => ?_
    · rw [h71, hn₂ 63 (by omega), h63c]; omega
    refine ⟨hfin _ hw₃ (fun r hr a b => ?_) (fun r hr a b => rfl) rfl rfl rfl ?_ ?_ ?_, ?_⟩
    · config_simp; rw [upd_other _ _ _ a]
    · config_simp; rw [h71, hn₂ 63 (by omega), h63c]
    · config_simp; rw [h76]
      have := hbest.scan_succ_ge (hi := c.nreg 71 - 1) (by rw [hj1]; exact hcmp)
      rwa [hj1] at this
    · config_simp; rw [h76, hb]; exact hI.val
    · config_simp; rw [h71, hn₂ 63 (by omega), h63c]
      have := mul_pred_add (a := E + 6) (x := hi + 1 - c.nreg 71) (by omega)
      rw [show hi + 1 - (c.nreg 71 + 1) = hi + 1 - c.nreg 71 - 1 by omega]
      omega

theorem scan_exec (hent : EntSpec P W ent A E m n pb c₀) {c₁ : Config} {i lo hi : ℕ}
    (hw : WordsBounded W c₁) (hA : Agree pb m c₀ c₁) (h70 : c₁.nreg 70 = i) (h63 : c₁.nreg 63 = 1)
    (h77 : c₁.nreg 77 = hi + 1) (h71 : c₁.nreg 71 = lo + 1) (h76 : c₁.nreg 76 = lo)
    (hv : c₁.rreg 71 = A i lo) (hi_m : i < m) (hhi : hi < n) (hlohi : lo ≤ hi) (hnW : n + 1 ≤ W) :
    ∃ c' k, Exec P W (.whileLtN 71 77 (scanBody ent)) c₁ c' k ∧ k ≤ (E + 6) * (hi - lo) + 2 ∧
      (IS W A c₁ i lo hi c' ∧ c'.nreg 71 = hi + 1) := by
  obtain ⟨c', k, e, hI, hn, hk⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 71) (b := 77)
    (body := scanBody ent) (IS W A c₁ i lo hi) (fun c => (E + 6) * (hi + 1 - c.nreg 71))
    (fun c h => h.wb)
    (fun c hc hlt => scanBody_exec hent hA h70 h63 h77 hi_m hhi hnW c hc hlt)
    ⟨hw, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, rfl, by omega, by omega,
      by rw [h71, h76, Nat.add_sub_cancel]; exact isLMin_self _ _, by rw [hv, h76]⟩
  have h77' : c'.nreg 77 = hi + 1 := (hI.nreg 77 (by omega) (by omega) (by omega)).trans h77
  refine ⟨c', k, e, ?_, hI, by have := hI.j_le; omega⟩
  rw [h71, show hi + 1 - (lo + 1) = hi - lo by omega] at hk
  exact hk

/-! ### The window of a row -/

/-- The window bound of the row `r` (rows numbered from `1`): `0` for `r = 0`, the leftmost
minimum of the row `r - 1` of `A` for `1 ≤ r ≤ m`, and `n - 1` beyond. -/
noncomputable def pv (m n : ℕ) (A : ℕ → ℕ → ℝ) (r : ℕ) : ℕ :=
  if r = 0 then 0 else if r ≤ m then lmin n A (r - 1) else n - 1

lemma pv_of_le {r : ℕ} (h1 : 1 ≤ r) (h2 : r ≤ m) : pv m n A r = lmin n A (r - 1) := by
  unfold pv; split_ifs <;> first | rfl | omega

lemma pv_of_gt {r : ℕ} (h : m < r) : pv m n A r = n - 1 := by
  unfold pv; split_ifs <;> first | rfl | omega

lemma pv_lt (hn : 0 < n) (r : ℕ) : pv m n A r < n := by
  unfold pv; split_ifs
  · exact hn
  · exact lmin_lt A _ hn
  · omega

lemma pv_mono (hA : IsTotMono m n A) (hn : 0 < n) {r r' : ℕ} (h : r ≤ r') :
    pv m n A r ≤ pv m n A r' := by
  unfold pv
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  all_goals first | omega | exact Nat.zero_le _ | skip
  · exact hA.lmin_mono (by omega) (by omega) hn
  · have := lmin_lt A (r - 1) hn; omega

/-- The row `r` is done: its position and its value are stored. -/
def Done (A : ℕ → ℕ → ℝ) (n pb : ℕ) (c : Config) (r : ℕ) : Prop :=
  c.nmem (pb + r) = lmin n A (r - 1) ∧ c.rmem (pb + r) = A (r - 1) (lmin n A (r - 1))

theorem hiS_exec (c : Config) (hc : WordsBounded W c) (h61 : c.nreg 61 = n) (h62 : c.nreg 62 = pb)
    (h63 : c.nreg 63 = 1) (h67 : c.nreg 67 = m + 1) (hW : pb + m ≤ W) {x : ℕ}
    (h73 : c.nreg 73 = x) (hx : 1 ≤ x) (hdone : x ≤ m → c.nmem (pb + x) = lmin n A (x - 1)) :
    ∃ c' k, Exec P W hiS c c' k ∧ k ≤ 3 ∧ (c'.nreg 75 = pv m n A x ∧
      (∀ r, r ≠ 74 → r ≠ 75 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold hiS
  by_cases hlt : x < m + 1
  · refine spec_ifLtN_true (by rw [h73, h67]; exact hlt) ?_
    exec_block
    · rw [h62, h73]; omega
    refine ⟨by omega, ?_, fun r a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [h62, h73, hdone (by omega)]
      unfold pv; split_ifs <;> first | rfl | omega
    · config_simp; rw [upd_other _ _ _ b, upd_other _ _ _ a]
  · refine spec_ifLtN_false (by rw [h73, h67]; exact hlt) ?_
    exec_block
    refine ⟨by omega, ?_, fun r a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [h61, h63]
      unfold pv; split_ifs <;> first | rfl | omega
    · config_simp; rw [upd_other _ _ _ b]

/-! ### One row -/

/-- The registers fixed during the level `s`. -/
structure RR (m n pb s : ℕ) (c : Config) : Prop where
  r60 : c.nreg 60 = m
  r61 : c.nreg 61 = n
  r62 : c.nreg 62 = pb
  r63 : c.nreg 63 = 1
  r64 : c.nreg 64 = 2
  r65 : c.nreg 65 = s
  r67 : c.nreg 67 = m + 1
  r72 : c.nreg 72 = 2 * s

theorem RR.of {s : ℕ} {c c' : Config} (h : RR m n pb s c)
    (h' : ∀ r, 60 ≤ r → r < 73 → r ≠ 66 → r ≠ 68 → r ≠ 69 → r ≠ 70 → r ≠ 71 → c'.nreg r = c.nreg r) :
    RR m n pb s c' :=
  ⟨(h' 60 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r60,
    (h' 61 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r61,
    (h' 62 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r62,
    (h' 63 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r63,
    (h' 64 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r64,
    (h' 65 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r65,
    (h' 67 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r67,
    (h' 72 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r72⟩

/-- The state of the level `s`: the rows divisible by `2s` and the rows `s, 3s, …` below the
current row `r68` are done, and `r69` is the window bound of the row `r68 - s`. -/
structure IR (W : ℕ) (A : ℕ → ℕ → ℝ) (m n pb : ℕ) (c₀ : Config) (s : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  agree : Agree pb m c₀ c
  regs : RR m n pb s c
  spos : 0 < s
  sle : s ≤ m
  cur : ∃ u, c.nreg 68 = s + 2 * s * u
  curle : c.nreg 68 ≤ m + 2 * s
  lo : c.nreg 69 = pv m n A (c.nreg 68 - s)
  done : ∀ r, 1 ≤ r → r ≤ m → (2 * s ∣ r ∨ (s ∣ r ∧ r < c.nreg 68)) → Done A n pb c r

/-- A multiple of `s` below the next odd multiple, other than the current one and not a
multiple of `2s`, is below the current one. -/
lemma odd_mul_lt {s u r : ℕ} (hs : 0 < s) (hd : s ∣ r) (hlt : r < s + 2 * s * u + 2 * s)
    (hne : r ≠ s + 2 * s * u) (hnd : ¬ 2 * s ∣ r) : r < s + 2 * s * u := by
  obtain ⟨v, rfl⟩ := hd
  have hv : v < 2 * u + 3 := by
    have : s * v < s * (2 * u + 3) := by rw [show s * (2 * u + 3) = s + 2 * s * u + 2 * s by ring]; exact hlt
    exact Nat.lt_of_mul_lt_mul_left this
  have h1 : v ≠ 2 * u + 1 := fun h => hne (by rw [h]; ring)
  have h2 : v ≠ 2 * u + 2 := fun h => hnd ⟨u + 1, by rw [h]; ring⟩
  have : v ≤ 2 * u := by omega
  calc s * v ≤ s * (2 * u) := Nat.mul_le_mul_left _ this
    _ < s + 2 * s * u := by rw [show s * (2 * u) = 2 * s * u by ring]; omega

theorem rowBody_exec (hent : EntSpec P W ent A E m n pb c₀) (hA : IsTotMono m n A) (hn : 0 < n)
    (hW : pb + 3 * m + n + 2 ≤ W) {s : ℕ} (c : Config) (hI : IR W A m n pb c₀ s c)
    (hlt : c.nreg 68 < c.nreg 67) :
    ∃ c' k, Exec P W (rowBody ent) c c' k ∧ IR W A m n pb c₀ s c' ∧
      (E + 6) * (n - c'.nreg 69) + (E + 19) * ((m + 2 * s - c'.nreg 68) / (2 * s)) + k + 2 ≤
        (E + 6) * (n - c.nreg 69) + (E + 19) * ((m + 2 * s - c.nreg 68) / (2 * s)) := by
  have hc := hI.wb
  have hR := hI.regs
  have hs := hI.spos
  have hsm := hI.sle
  rw [hR.r67] at hlt
  generalize hcur : c.nreg 68 = cur at hlt
  have hlo := hI.lo
  rw [hcur] at hlo
  obtain ⟨u, hu⟩ := hI.cur
  rw [hcur] at hu
  -- the window
  generalize hlov : pv m n A (cur - s) = lo at hlo
  generalize hhiv : pv m n A (cur + s) = hi
  have hlohi : lo ≤ hi := by rw [← hlov, ← hhiv]; exact pv_mono hA hn (by omega)
  have hhin : hi < n := by rw [← hhiv]; exact pv_lt hn _
  have hwin1 : lo ≤ lmin n A (cur - 1) := by
    rw [← hlov]; have := pv_mono hA hn (r := cur - s) (r' := cur) (by omega)
    rwa [pv_of_le (r := cur) (by omega) (by omega)] at this
  have hwin2 : lmin n A (cur - 1) ≤ hi := by
    rw [← hhiv]; have := pv_mono hA hn (r := cur) (r' := cur + s) (by omega)
    rwa [pv_of_le (r := cur) (by omega) (by omega)] at this
  have hdone_hi : cur + s ≤ m → c.nmem (pb + (cur + s)) = lmin n A (cur + s - 1) := fun h =>
    (hI.done (cur + s) (by omega) h (Or.inl ⟨u + 1, by rw [hu]; ring⟩)).1
  unfold rowBody
  -- `r73 := r + s`
  refine spec_seq ?_
  refine spec_instr (Exec.addN hc 73 68 65 (by rw [hcur, hR.r65]; omega)) fun hw₁ => ?_
  -- the right end of the window
  refine spec_seq ?_
  refine spec_use (hiS_exec (A := A) _ hw₁ (by config_simp; exact hR.r61)
    (by config_simp; exact hR.r62) (by config_simp; exact hR.r63) (by config_simp; exact hR.r67)
    (by omega) (x := cur + s) (by config_simp; rw [hcur, hR.r65]) (by omega)
    (by config_simp; exact hdone_hi)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨h75, hn₂, hr₂, hnm₂, hrm₂, ho₂⟩
  rw [hhiv] at h75
  have e₂ : ∀ r, r ≠ 73 → r ≠ 74 → r ≠ 75 → c₂.nreg r = c.nreg r := fun r a b d => by
    rw [hn₂ r b d]; config_simp; rw [upd_other _ _ _ a]
  have R₂ : RR m n pb s c₂ := hR.of fun r _ _ _ _ _ _ _ => e₂ r (by omega) (by omega) (by omega)
  have g68₂ : c₂.nreg 68 = cur := (e₂ 68 (by omega) (by omega) (by omega)).trans hcur
  have g69₂ : c₂.nreg 69 = lo := (e₂ 69 (by omega) (by omega) (by omega)).trans hlo
  have A₂ : Agree pb m c₀ c₂ := hI.agree.of_eq
    (fun r hr => e₂ r (by omega) (by omega) (by omega)) (fun r _ => by rw [hr₂]) hnm₂ hrm₂ ho₂
  -- the arguments of the oracle: the row `r - 1` and the column `lo`
  refine spec_seq ?_
  exec_block
  refine spec_seq ?_
  refine spec_use (hent _ ‹_› ?_ ?_ ?_) ?_
  · exact A₂.of_eq (fun r hr => by config_simp; rw [upd_other _ _ _ (by omega),
      upd_other _ _ _ (by omega)]) (fun r _ => rfl) rfl rfl rfl
  · config_simp; rw [g68₂, R₂.r63]; omega
  · config_simp; rw [g69₂]; omega
  intro c₄ k₄ hk₄ hw₄ ⟨hv₄, hn₄, hr₄, hnm₄, hrm₄, ho₄⟩
  config_simp at hv₄
  rw [g68₂, R₂.r63, g69₂] at hv₄
  have e₄ : ∀ r < 80, r ≠ 70 → r ≠ 71 → c₄.nreg r = c₂.nreg r := fun r hr a b => by
    rw [hn₄ r hr]; config_simp; rw [upd_other _ _ _ b, upd_other _ _ _ a]
  have R₄ : RR m n pb s c₄ := R₂.of fun r _ h _ _ _ a b => e₄ r (by omega) a b
  have g68₄ : c₄.nreg 68 = cur := (e₄ 68 (by omega) (by omega) (by omega)).trans g68₂
  have g69₄ : c₄.nreg 69 = lo := (e₄ 69 (by omega) (by omega) (by omega)).trans g69₂
  have g75₄ : c₄.nreg 75 = hi := (e₄ 75 (by omega) (by omega) (by omega)).trans h75
  have g70₄ : c₄.nreg 70 = cur - 1 := by
    rw [hn₄ 70 (by omega)]; config_simp; rw [g68₂, R₂.r63]
  have g71₄ : c₄.nreg 71 = lo := by rw [hn₄ 71 (by omega)]; config_simp; exact g69₂
  have A₄ : Agree pb m c₀ c₄ := A₂.of_eq (fun r hr => e₄ r (by omega) (by omega) (by omega))
    (fun r hr => by rw [hr₄ r (by omega) (by omega)]) hnm₄ hrm₄ ho₄
  -- the start of the scan
  refine spec_seq ?_
  exec_block
  · config_simp; rw [g71₄, R₄.r63]; omega
  · config_simp; rw [g75₄, R₄.r63]; omega
  refine spec_seq ?_
  refine spec_use (scan_exec hent (i := cur - 1) (lo := lo) (hi := hi) ‹_› ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by omega) hhin hlohi (by omega)) ?_
  · exact A₄.of_eq (fun r hr => by config_simp; rw [upd_other _ _ _ (by omega),
      upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]) (fun r hr => by
      config_simp; rw [upd_other _ _ _ (by omega)]) rfl rfl rfl
  · config_simp; exact g70₄
  · config_simp; exact R₄.r63
  · config_simp; rw [g75₄, R₄.r63]
  · config_simp; rw [g71₄, R₄.r63]
  · config_simp; exact g71₄
  · config_simp; exact hv₄
  intro c₆ k₆ hk₆ hw₆ ⟨hIS, hj₆⟩
  have e₆ : ∀ r < 80, r ≠ 71 → r ≠ 76 → r ≠ 77 → c₆.nreg r = c₄.nreg r := fun r hr a b d => by
    rw [hIS.nreg r hr a b]; config_simp; upd_tac
  have R₆ : RR m n pb s c₆ := R₄.of fun r _ h _ _ _ _ _ => e₆ r (by omega) (by omega) (by omega)
    (by omega)
  have g68₆ : c₆.nreg 68 = cur := (e₆ 68 (by omega) (by omega) (by omega) (by omega)).trans g68₄
  have g75₆ : c₆.nreg 75 = hi := (e₆ 75 (by omega) (by omega) (by omega) (by omega)).trans g75₄
  have hpos : lmin n A (cur - 1) = c₆.nreg 76 := by
    have hb := hIS.best
    rw [hj₆, Nat.add_sub_cancel] at hb
    exact lmin_eq_of_window hn hwin1 hwin2 hhin hb
  have hval : c₆.rreg 71 = A (cur - 1) (c₆.nreg 76) := hIS.val
  have hm₆ : c₆.nmem = c.nmem := by rw [hIS.nmem]; exact hnm₄.trans (hnm₂)
  have hr₆ : c₆.rmem = c.rmem := by rw [hIS.rmem]; exact hrm₄.trans (hrm₂)
  have A₆ : Agree pb m c₀ c₆ := A₄.of_eq
    (fun r hr => by rw [e₆ r (by omega) (by omega) (by omega) (by omega)])
    (fun r hr => by rw [hIS.rreg r (by omega) (by omega) (by omega)]; config_simp
                    rw [upd_other _ _ _ (by omega)]) (by rw [hIS.nmem]) (by rw [hIS.rmem])
    (by rw [hIS.out])
  -- store the result and move to the next row
  exec_block
  · rw [R₆.r62, g68₆]; omega
  · config_simp; rw [g68₆, R₆.r72]; omega
  obtain ⟨a1, a2, a3, a4, a5⟩ := A₆
  refine ⟨⟨‹_›, ⟨fun r hr => ?_, fun r hr => a2 r hr, fun a ha => ?_, fun a ha => ?_, a5⟩,
    R₆.of fun r _ _ _ _ _ _ _ => ?_, hs, hsm, ?_, ?_, ?_, ?_⟩, ?_⟩
  · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact a1 r hr
  · config_simp; rw [R₆.r62, g68₆, upd_other _ _ _ (by omega)]; exact a3 a ha
  · config_simp; rw [R₆.r62, g68₆, upd_other _ _ _ (by omega)]; exact a4 a ha
  · config_simp; upd_tac
  · config_simp; rw [g68₆, R₆.r72]; exact ⟨u + 1, by rw [hu]; ring⟩
  · config_simp; rw [g68₆, R₆.r72]; omega
  · config_simp; rw [g75₆, g68₆, R₆.r72, ← hhiv]; congr 1; omega
  · intro r h1 h2 hr
    unfold Done
    config_simp
    rw [R₆.r62, g68₆] at hr ⊢
    rw [R₆.r72] at hr
    by_cases hrc : r = cur
    · subst hrc
      simp only [upd_same]
      exact ⟨hpos.symm, by rw [hval, hpos]⟩
    · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), hm₆, hr₆]
      refine hI.done r h1 h2 ?_
      rw [hcur]
      rcases hr with hr | ⟨hd, hr⟩
      · exact Or.inl hr
      · by_cases h2s : 2 * s ∣ r
        · exact Or.inl h2s
        · refine Or.inr ⟨hd, ?_⟩
          have hr' : r < s + 2 * s * u + 2 * s := by rw [← hu]; exact hr
          rw [hu] at hrc ⊢
          exact odd_mul_lt hs hd hr' hrc h2s
  · config_simp
    rw [g75₆, g68₆, R₆.r72, hlo]
    have q1 : m + 2 * s - (cur + 2 * s) = m - cur := by omega
    have q2 : (m + 2 * s - cur) / (2 * s) = (m - cur) / (2 * s) + 1 := by
      rw [show m + 2 * s - cur = m - cur + 2 * s by omega, Nat.add_div_right _ (by omega)]
    have q3 : (E + 6) * (n - lo) = (E + 6) * (n - hi) + (E + 6) * (hi - lo) := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [q1, q2, q3, Nat.mul_add, Nat.mul_one]
    omega

/-! ### One level -/

/-- The state between levels: the rows divisible by `s = r65` are done. -/
structure IO (W : ℕ) (A : ℕ → ℕ → ℝ) (m n pb : ℕ) (c₀ : Config) (c : Config) : Prop where
  wb : WordsBounded W c
  agree : Agree pb m c₀ c
  r60 : c.nreg 60 = m
  r61 : c.nreg 61 = n
  r62 : c.nreg 62 = pb
  r63 : c.nreg 63 = 1
  r64 : c.nreg 64 = 2
  r67 : c.nreg 67 = m + 1
  pow : ∃ t, c.nreg 65 = 2 ^ t
  sle : c.nreg 65 ≤ 2 * m
  done : ∀ r, 1 ≤ r → r ≤ m → c.nreg 65 ∣ r → Done A n pb c r

/-- The number of rows `r ≤ m` processed at the level `s`. -/
lemma rows_level {m s : ℕ} (hs : 0 < s) : (m + s) / (2 * s) + m / (2 * s) = m / s := by
  have e1 : (m + s) / (2 * s) = (m / s + 1) / 2 := by
    rw [show 2 * s = s * 2 by ring, ← Nat.div_div_eq_div_mul, Nat.add_div_right _ hs]
  have e2 : m / (2 * s) = m / s / 2 := by
    rw [show 2 * s = s * 2 by ring, ← Nat.div_div_eq_div_mul]
  rw [e1, e2]; omega

theorem levelBody_exec (hent : EntSpec P W ent A E m n pb c₀) (hA : IsTotMono m n A) (hn : 0 < n)
    (hW : pb + 3 * m + n + 2 ≤ W) (c : Config) (hI : IO W A m n pb c₀ c)
    (hlt : c.nreg 63 < c.nreg 65) :
    ∃ c' k, Exec P W (levelBody ent) c c' k ∧ IO W A m n pb c₀ c' ∧
      ((E + 6) * n + 8) * Nat.log 2 (c'.nreg 65) + (E + 19) * (m - m / c'.nreg 65) + k + 2 ≤
        ((E + 6) * n + 8) * Nat.log 2 (c.nreg 65) + (E + 19) * (m - m / c.nreg 65) := by
  have hc := hI.wb
  obtain ⟨t, ht⟩ := hI.pow
  rw [hI.r63, ht] at hlt
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h] at hlt; simp at hlt
    · exact h
  obtain ⟨t₀, rfl⟩ : ∃ t₀, t = t₀ + 1 := ⟨t - 1, by omega⟩
  generalize hs₀ : 2 ^ t₀ = s₀
  have hs : c.nreg 65 = 2 * s₀ := by rw [ht, pow_succ, ← hs₀]; ring
  have hs₀p : 0 < s₀ := by rw [← hs₀]; exact Nat.two_pow_pos _
  have hsle := hI.sle
  rw [hs] at hsle
  have hdiv : 2 * s₀ / c.nreg 64 = s₀ := by rw [hI.r64]; omega
  unfold levelBody
  refine spec_seq ?_
  exec_block
  · omega
  · config_simp; rw [hs, hdiv]; omega
  -- the rows of the level
  refine spec_while (IR W A m n pb c₀ s₀)
    (fun c => (E + 6) * (n - c.nreg 69) + (E + 19) * ((m + 2 * s₀ - c.nreg 68) / (2 * s₀)))
    (fun c h => h.wb) (fun c' hc' hlt' => rowBody_exec hent hA hn hW c' hc' hlt')
    ⟨‹_›, hI.agree.of_eq (fun r hr => by config_simp; upd_tac) (fun r _ => rfl) rfl rfl rfl,
      ⟨by config_simp; exact hI.r60, by config_simp; exact hI.r61, by config_simp; exact hI.r62,
        by config_simp; exact hI.r63, by config_simp; exact hI.r64, by config_simp; rw [hs, hdiv],
        by config_simp; exact hI.r67, by config_simp; rw [hs, hdiv]; ring⟩, hs₀p, by omega,
      ⟨0, by config_simp; rw [hs, hdiv]; ring⟩, by config_simp; rw [hs, hdiv]; omega,
      by config_simp; rw [hs, hdiv, Nat.sub_self]; rfl, fun r h1 h2 hr => ?_⟩ ?_
  · unfold Done; config_simp; config_simp at hr
    rw [hs, hdiv] at hr
    rcases hr with hr | ⟨hd, hr⟩
    · exact hI.done r h1 h2 (by rw [hs]; exact hr)
    · obtain ⟨v, rfl⟩ := hd
      rcases Nat.eq_zero_or_pos v with hv | hv
      · rw [hv] at h1; omega
      · have : s₀ * 1 ≤ s₀ * v := Nat.mul_le_mul_left _ hv
        omega
  intro c₂ k₂ hI₂ hn₂ hk₂
  refine ⟨⟨hI₂.wb, hI₂.agree, hI₂.regs.r60, hI₂.regs.r61, hI₂.regs.r62, hI₂.regs.r63,
      hI₂.regs.r64, hI₂.regs.r67, ⟨t₀, by rw [hI₂.regs.r65, hs₀]⟩, by rw [hI₂.regs.r65]; omega,
      fun r h1 h2 hr => hI₂.done r h1 h2 ?_⟩, ?_⟩
  · rw [hI₂.regs.r65] at hr
    by_cases h2 : 2 * s₀ ∣ r
    · exact Or.inl h2
    · refine Or.inr ⟨hr, ?_⟩
      have := hI₂.regs.r67; omega
  · have l1 : Nat.log 2 s₀ = t₀ := by rw [← hs₀, Nat.log_pow (by norm_num)]
    have l2 : Nat.log 2 (2 * s₀) = t₀ + 1 := by rw [← hs₀, ← pow_succ', Nat.log_pow (by norm_num)]
    rw [hI₂.regs.r65, hs, l1, l2]
    beta_reduce at hk₂
    config_simp at hk₂
    rw [hs, hdiv, Nat.sub_zero, show m + 2 * s₀ - s₀ = m + s₀ by omega] at hk₂
    have h1 := rows_level (m := m) hs₀p
    have h2 : m / (2 * s₀) ≤ m / s₀ := Nat.div_le_div_left (by omega) hs₀p
    have h3 : m / s₀ ≤ m := Nat.div_le_self _ _
    have h4 := mul_pred_add (a := (E + 6) * n + 8) (x := t₀ + 1) (by omega)
    rw [Nat.add_sub_cancel] at h4
    have h5 : (E + 19) * (m - m / s₀) + (E + 19) * ((m + s₀) / (2 * s₀)) =
        (E + 19) * (m - m / (2 * s₀)) := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [← h4, ← h5]
    omega

/-! ### The whole run -/

/-- The state of the search for the first power of two above `m`. -/
structure IP (W : ℕ) (m n pb : ℕ) (c₀ : Config) (c : Config) : Prop where
  wb : WordsBounded W c
  agree : Agree pb m c₀ c
  r60 : c.nreg 60 = m
  r61 : c.nreg 61 = n
  r62 : c.nreg 62 = pb
  r63 : c.nreg 63 = 1
  r64 : c.nreg 64 = 2
  r67 : c.nreg 67 = m + 1
  pow : ∃ t, c.nreg 65 = 2 ^ t
  sle : c.nreg 65 ≤ 2 * m
  mem : c.nmem = c₀.nmem ∧ c.rmem = c₀.rmem

/-- **Row minima of a totally monotone matrix on the machine.** With `m, n ≥ 1` in `r60, r61`
and the output base `pb` in `r62`, `rowMin ent` stores, for every row `i < m`, the leftmost
position `lmin n A i` of a minimum of the row at `pb + i + 1` of the natural memory and the
minimum `A i (lmin n A i)` at `pb + i + 1` of the real memory, within
`((E + 6) n + 8) (log₂ m + 1) + (E + 22) m + 8` steps, where `E` bounds the cost of an entry. It
changes nothing outside the registers `r63 … r79`, the registers the oracle uses and the output
cells. -/
theorem rowMin_exec (hent : EntSpec P W ent A E m n pb c₀) (hA : IsTotMono m n A) (hm : 0 < m)
    (hn : 0 < n) (hW : pb + 3 * m + n + 2 ≤ W) (hc : WordsBounded W c₀) (h60 : c₀.nreg 60 = m)
    (h61 : c₀.nreg 61 = n) (h62 : c₀.nreg 62 = pb) :
    ∃ c' k, Exec P W (rowMin ent) c₀ c' k ∧
      k ≤ ((E + 6) * n + 8) * (Nat.log 2 m + 1) + (E + 22) * m + 8 ∧
      (Agree pb m c₀ c' ∧ c'.nreg 60 = m ∧ c'.nreg 61 = n ∧ c'.nreg 62 = pb ∧
        ∀ i < m, c'.nmem (pb + i + 1) = lmin n A i ∧ c'.rmem (pb + i + 1) = A i (lmin n A i)) := by
  unfold rowMin
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  · omega
  · config_simp; rw [h60]; omega
  refine spec_seq ?_
  -- the first power of two above `m`
  refine spec_while (IP W m n pb c₀) (fun c => 3 * (m + 1 - c.nreg 65)) (fun c h => h.wb)
    (fun c hP hlt => by
      rw [hP.r67] at hlt
      have hw := hP.wb
      refine ⟨_, 1, Exec.addN hw 65 65 65 (by omega),
        ⟨(Exec.addN (P := P) hw 65 65 65 (by omega)).wb_right,
        hP.agree.of_eq (fun r hr => by config_simp; upd_tac) (fun r _ => rfl) rfl rfl rfl,
        by config_simp; exact hP.r60, by config_simp; exact hP.r61, by config_simp; exact hP.r62,
        by config_simp; exact hP.r63, by config_simp; exact hP.r64, by config_simp; exact hP.r67,
        ?_, by config_simp; omega, hP.mem⟩, ?_⟩
      · obtain ⟨t, ht⟩ := hP.pow
        exact ⟨t + 1, by config_simp; rw [ht, pow_succ]; ring⟩
      · config_simp
        obtain ⟨t, ht⟩ := hP.pow
        have : 1 ≤ c.nreg 65 := by rw [ht]; exact Nat.one_le_two_pow
        omega)
    ⟨‹_›, (Agree.refl pb m c₀).of_eq (fun r hr => by config_simp; upd_tac) (fun r _ => rfl) rfl rfl
      rfl, by config_simp; exact h60, by config_simp; exact h61, by config_simp; exact h62,
      by config_simp, by config_simp, by config_simp; rw [h60], ⟨0, by config_simp; rfl⟩,
      by config_simp; omega, rfl, rfl⟩ ?_
  intro c₁ k₁ hP₁ hn₁ hk₁
  rw [hP₁.r67] at hn₁
  -- the levels
  refine spec_while (IO W A m n pb c₀)
    (fun c => ((E + 6) * n + 8) * Nat.log 2 (c.nreg 65) + (E + 19) * (m - m / c.nreg 65))
    (fun c h => h.wb) (fun c' hc' hlt' => levelBody_exec hent hA hn hW c' hc' hlt')
    ⟨hP₁.wb, hP₁.agree, hP₁.r60, hP₁.r61, hP₁.r62, hP₁.r63, hP₁.r64, hP₁.r67, hP₁.pow, hP₁.sle,
      fun r h1 h2 hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)⟩ ?_
  intro c₂ k₂ hI₂ hn₂ hk₂
  refine ⟨?_, hI₂.agree, hI₂.r60, hI₂.r61, hI₂.r62, fun i hi => ?_⟩
  · obtain ⟨t, ht⟩ := hP₁.pow
    have hsle := hP₁.sle
    have htl : t ≤ Nat.log 2 m + 1 := by
      have := Nat.le_log_of_pow_le (b := 2) (by norm_num) (show 2 ^ t ≤ m * 2 by rw [← ht]; omega)
      rwa [Nat.log_mul_base (by norm_num) (by omega)] at this
    beta_reduce at hk₁ hk₂
    rw [ht, Nat.log_pow (by norm_num), Nat.div_eq_of_lt (by rw [← ht]; omega), Nat.sub_zero] at hk₂
    have := Nat.mul_le_mul_left ((E + 6) * n + 8) htl
    config_simp at hk₁
    have hm1 : m + 1 - 1 = m := by omega
    rw [hm1] at hk₁
    nlinarith
  · obtain ⟨t, ht⟩ := hI₂.pow
    have hs1 : c₂.nreg 65 = 1 := by
      rw [hI₂.r63] at hn₂
      have : 1 ≤ c₂.nreg 65 := by rw [ht]; exact Nat.one_le_two_pow
      omega
    have := hI₂.done (i + 1) (by omega) (by omega) (by rw [hs1]; exact one_dvd _)
    simp only [Done, Nat.add_sub_cancel] at this
    rw [← Nat.add_assoc] at this
    exact this

end Monge

end PlanarFlow
