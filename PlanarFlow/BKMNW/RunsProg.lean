module

public import PlanarFlow.BKMNW.ExistSegsD
public import PlanarFlow.BKMNW.TwoGroupsProg
public import Mathlib.Data.List.GetD

/-!
# The runs of a separator off the holes on the machine

`PlanarFlow.BKMNW.HPath.runsF hρ 0` (the maximal runs of the path off the holes, the parts
`segsF` of a split) is determined by the pairs of indices `(a, b)` of its runs
(`runsF_data`): the run `(a, b)` has `b - a` darts `ρ.d (a + i)` and vertices `ρ.p (a + i)`.
The pairs are `runIdx H k 0` for the flags `H j = [ρ.p j ∈ hunion Hs]`, `k = ρ.k`
(`runEndF`, `runIdx`: plain recursions on the flags). A natural-word program computes them in
one scan of a flag array `HF[j] = nmem (Hb + j)` (`j ≤ k + 1`, nonzero = in a hole), writing the
pairs at `Ob + 2 j`, `Ob + 2 j + 1`.

Registers: `4100 = k`, `4101 = Hb`, `4102 = Ob`; written: `4103 = 1`, `4104 = 0`, index `4105`,
in-run flag `4106`, start `4107`, count `4108`, scratch `4109 … 4113`.

* `runEndF`, `runIdx` and their equations, **`runEnd_eq_runEndF`**, **`runsF_data`**;
* `RnInv` (the state of the scan) and its steps, `runEndF_congr`, `runIdx_congr`, `rnMem_eq`;
* `rnEmit`, `rnOff`, `rnBody`, **`rnProg`**, **`rnProg_exec`**: within `23 (k + 1) + 8` steps
  (`Hb + k + 2 ≤ Ob`, `Ob + 2 (k + 1) + 1 ≤ W`), the count `r = r4108` and the pairs in memory
  are `runIdx H k 0` (`H j = decide (0 < HF[j])`); **`rnProg_runsF`**: for a simple path with its
  hole flags stored, the runs `runsF hρ 0` read back from the machine's pairs.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The runs as pairs of indices -/

section Pure

/-- **The end of the run from `s`** on the flags `H` (`true` = in a hole): the least `b ≥ s`
with `b ≥ k` or `H (b + 1)`. -/
def runEndF (H : ℕ → Bool) (k s : ℕ) : ℕ :=
  if k ≤ s ∨ H (s + 1) = true then s else runEndF H k (s + 1)
termination_by k - s

lemma runEndF_eq (H : ℕ → Bool) (k s : ℕ) :
    runEndF H k s = if k ≤ s ∨ H (s + 1) = true then s else runEndF H k (s + 1) := by
  rw [runEndF]

lemma runEndF_ge (H : ℕ → Bool) (k : ℕ) : ∀ s, s ≤ runEndF H k s := by
  intro s
  induction h : k - s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    rw [runEndF_eq]
    split_ifs with hc
    · exact le_rfl
    · exact Nat.le_of_succ_le (ih (k - (s + 1)) (by omega) (s + 1) rfl)

lemma runEndF_spec (H : ℕ → Bool) (k : ℕ) : ∀ s, k ≤ runEndF H k s ∨ H (runEndF H k s + 1) = true := by
  intro s
  induction h : k - s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    rw [runEndF_eq]
    split_ifs with hc
    · rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr hc
    · exact ih (k - (s + 1)) (by omega) (s + 1) rfl

/-- `runEndF` is the least end. -/
lemma runEndF_le (H : ℕ → Bool) (k : ℕ) : ∀ s b, s ≤ b → (k ≤ b ∨ H (b + 1) = true) →
    runEndF H k s ≤ b := by
  intro s
  induction h : k - s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    intro b hsb hb
    rw [runEndF_eq]
    split_ifs with hc
    · exact hsb
    · rcases Nat.eq_or_lt_of_le hsb with rfl | hlt
      · exact absurd hb hc
      · exact ih (k - (s + 1)) (by omega) (s + 1) rfl b hlt hb

lemma runEndF_le_k (H : ℕ → Bool) {k s : ℕ} (hs : s ≤ k) : runEndF H k s ≤ k :=
  runEndF_le H k s k hs (Or.inl le_rfl)

/-- The indices of a run are off the holes. -/
lemma runEndF_off (H : ℕ → Bool) (k : ℕ) {s : ℕ} (hs : H s = false) :
    ∀ j, s ≤ j → j ≤ runEndF H k s → H j = false := by
  intro j hj hjb
  rcases Nat.eq_or_lt_of_le hj with rfl | hlt
  · exact hs
  · by_contra hH
    have := runEndF_le H k s (j - 1) (by omega)
      (Or.inr (by rw [show j - 1 + 1 = j by omega]; simpa using hH))
    omega

/-- **The runs as pairs of indices**, from `s` on. -/
def runIdx (H : ℕ → Bool) (k s : ℕ) : List (ℕ × ℕ) :=
  if k < s then [] else if H s = true then runIdx H k (s + 1)
  else (s, runEndF H k s) :: runIdx H k (runEndF H k s + 2)
termination_by k + 1 - s
decreasing_by
  · omega
  · have := runEndF_ge H k s; omega

lemma runIdx_of_lt (H : ℕ → Bool) {k s : ℕ} (hs : k < s) : runIdx H k s = [] := by
  rw [runIdx]; simp [hs]

lemma runIdx_of_mem (H : ℕ → Bool) {k s : ℕ} (hs : s ≤ k) (hH : H s = true) :
    runIdx H k s = runIdx H k (s + 1) := by
  rw [runIdx]; simp [show ¬ k < s by omega, hH]

lemma runIdx_of_not_mem (H : ℕ → Bool) {k s : ℕ} (hs : s ≤ k) (hH : H s = false) :
    runIdx H k s = (s, runEndF H k s) :: runIdx H k (runEndF H k s + 2) := by
  rw [runIdx]; simp [show ¬ k < s by omega, hH]

/-- **The state of the scan** before the index `i`: no run open and the rest of the pairs are
`runIdx H k i` (`f = 0`), or a run open from `a` (`f = 1`). -/
def RnInv (H : ℕ → Bool) (k i f a : ℕ) (out : List (ℕ × ℕ)) : Prop :=
  (f = 0 ∧ runIdx H k 0 = out ++ runIdx H k i) ∨
  (f = 1 ∧ H a = false ∧ a < i ∧ i ≤ runEndF H k a ∧
    runIdx H k 0 = out ++ (a, runEndF H k a) :: runIdx H k (runEndF H k a + 2))

lemma rnInv_le {H : ℕ → Bool} {k i f a : ℕ} {out : List (ℕ × ℕ)} (h : RnInv H k i f a out) :
    f ≤ 1 := by rcases h with h | h <;> omega

lemma rnInv_start (H : ℕ → Bool) (k a : ℕ) : RnInv H k 0 0 a [] := Or.inl ⟨rfl, rfl⟩

lemma rnInv_hole {H : ℕ → Bool} {k i f a : ℕ} {out : List (ℕ × ℕ)} (h : RnInv H k i f a out)
    (hi : i ≤ k) (hH : H i = true) : RnInv H k (i + 1) f a out := by
  rcases h with ⟨hf, h⟩ | ⟨hf, ha, hai, hie, h⟩
  · exact Or.inl ⟨hf, by rw [h, runIdx_of_mem H hi hH]⟩
  · have := runEndF_off H k ha i hai.le hie
    rw [this] at hH; exact absurd hH (by simp)

/-- The open run after the index `i` off the holes. -/
lemma rnInv_open {H : ℕ → Bool} {k i f a : ℕ} {out : List (ℕ × ℕ)} (h : RnInv H k i f a out)
    (hi : i ≤ k) (hH : H i = false) :
    H (if f = 0 then i else a) = false ∧ (if f = 0 then i else a) ≤ i ∧
      i ≤ runEndF H k (if f = 0 then i else a) ∧
      runIdx H k 0 = out ++ ((if f = 0 then i else a), runEndF H k (if f = 0 then i else a)) ::
        runIdx H k (runEndF H k (if f = 0 then i else a) + 2) := by
  rcases h with ⟨hf, h⟩ | ⟨hf, ha, hai, hie, h⟩
  · simp only [hf, ↓reduceIte]
    exact ⟨hH, le_rfl, runEndF_ge H k i, by rw [h, runIdx_of_not_mem H hi hH]⟩
  · simp only [hf, one_ne_zero, ↓reduceIte]
    exact ⟨ha, hai.le, hie, h⟩

lemma rnInv_end {H : ℕ → Bool} {k i f a : ℕ} {out : List (ℕ × ℕ)} (h : RnInv H k i f a out)
    (hi : i ≤ k) (hH : H i = false) (hE : k ≤ i ∨ H (i + 1) = true) (a' : ℕ) :
    RnInv H k (i + 1) 0 a' (out ++ [((if f = 0 then i else a), i)]) := by
  obtain ⟨h1, h2, h3, h4⟩ := rnInv_open h hi hH
  have he : runEndF H k (if f = 0 then i else a) = i :=
    le_antisymm (runEndF_le H k _ i h2 hE) h3
  rw [he] at h4
  refine Or.inl ⟨rfl, ?_⟩
  rw [h4, List.append_assoc, List.singleton_append]
  congr 2
  by_cases hik : k ≤ i
  · rw [runIdx_of_lt H (by omega), runIdx_of_lt H (by omega)]
  · have hH' : H (i + 1) = true := hE.resolve_left hik
    rw [runIdx_of_mem H (by omega) hH']

lemma rnInv_cont {H : ℕ → Bool} {k i f a : ℕ} {out : List (ℕ × ℕ)} (h : RnInv H k i f a out)
    (hi : i ≤ k) (hH : H i = false) (hE : ¬ (k ≤ i ∨ H (i + 1) = true)) :
    RnInv H k (i + 1) 1 (if f = 0 then i else a) out := by
  obtain ⟨h1, h2, h3, h4⟩ := rnInv_open h hi hH
  refine Or.inr ⟨rfl, h1, by omega, ?_, h4⟩
  rcases Nat.eq_or_lt_of_le h3 with h3 | h3
  · have := runEndF_spec H k (if f = 0 then i else a)
    rw [← h3] at this; exact absurd this hE
  · exact h3

lemma rnInv_final {H : ℕ → Bool} {k f a : ℕ} {out : List (ℕ × ℕ)}
    (h : RnInv H k (k + 1) f a out) : runIdx H k 0 = out := by
  rcases h with ⟨-, h⟩ | ⟨-, -, hai, hie, -⟩
  · rw [h, runIdx_of_lt H (by omega), List.append_nil]
  · have := runEndF_le_k H (k := k) (s := a) (by omega); omega

/-- The pairs `out` stored at `Ob + 2 j`, `Ob + 2 j + 1`. -/
def RnMem (m : ℕ → ℕ) (Ob : ℕ) (out : List (ℕ × ℕ)) : Prop :=
  ∀ j < out.length, m (Ob + 2 * j) = (out.getD j (0, 0)).1 ∧
    m (Ob + 2 * j + 1) = (out.getD j (0, 0)).2

lemma runEndF_congr {H H' : ℕ → Bool} {k : ℕ} (h : ∀ j ≤ k, H j = H' j) :
    ∀ s, runEndF H k s = runEndF H' k s := by
  intro s
  induction hn : k - s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    rw [runEndF_eq, runEndF_eq H']
    by_cases hks : k ≤ s
    · simp [hks]
    · rw [h (s + 1) (by omega), ih (k - (s + 1)) (by omega) (s + 1) rfl]

lemma runIdx_congr {H H' : ℕ → Bool} {k : ℕ} (h : ∀ j ≤ k, H j = H' j) :
    ∀ s, runIdx H k s = runIdx H' k s := by
  intro s
  induction hn : k + 1 - s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases hs : k < s
    · rw [runIdx_of_lt _ hs, runIdx_of_lt _ hs]
    · push Not at hs
      cases hHs : H s
      · have hH's : H' s = false := by rw [← h s hs]; exact hHs
        rw [runIdx_of_not_mem _ hs hHs, runIdx_of_not_mem _ hs hH's, runEndF_congr h s]
        have := runEndF_ge H' k s
        rw [ih _ (by omega) _ rfl]
      · have hH's : H' s = true := by rw [← h s hs]; exact hHs
        rw [runIdx_of_mem _ hs hHs, runIdx_of_mem _ hs hH's, ih _ (by omega) _ rfl]

/-- A list stored as pairs is read back from the memory. -/
lemma rnMem_eq {m : ℕ → ℕ} {Ob : ℕ} {out : List (ℕ × ℕ)} (h : RnMem m Ob out) :
    out = (List.range out.length).map fun j => (m (Ob + 2 * j), m (Ob + 2 * j + 1)) := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  obtain ⟨a, b⟩ := h j h1
  rw [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ h1] at a b
  rw [a, b]

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The flags of a path: `true` at the indices whose vertex is in a hole. -/
noncomputable def pathFlags (ρ : HPath M) (Hs : List (Finset V)) (j : ℕ) : Bool := by
  classical exact decide (ρ.p j ∈ hunion Hs)

lemma pathFlags_iff {ρ : HPath M} {Hs : List (Finset V)} {j : ℕ} :
    pathFlags ρ Hs j = true ↔ ρ.p j ∈ hunion Hs := by
  classical simp [pathFlags]

/-- **The end of a run is `runEndF` of the flags.** -/
theorem runEnd_eq_runEndF (ρ : HPath M) (Hs : List (Finset V)) (s : ℕ) (hs : s ≤ ρ.k) :
    ρ.runEnd Hs s hs = runEndF (pathFlags ρ Hs) ρ.k s := by
  classical
  apply le_antisymm
  · have h1 := runEndF_ge (pathFlags ρ Hs) ρ.k s
    have h2 := runEndF_spec (pathFlags ρ Hs) ρ.k s
    exact Nat.find_le ⟨h1, h2.imp id pathFlags_iff.1⟩
  · exact runEndF_le _ _ s _ (ρ.runEnd_ge Hs s hs)
      ((ρ.runEnd_next Hs s hs).imp id pathFlags_iff.2)

/-- **The runs are determined by their pairs of indices**: the data `(k, d, p)` of the runs
`runsF hρ s` are those of the pairs `runIdx (pathFlags ρ Hs) ρ.k s`. -/
theorem runsF_data (ρ : HPath M) {Hs : List (Finset V)} (hρ : ρ.Simple Hs) :
    ∀ s, (ρ.runsF hρ s).map (fun σ => (σ.k, σ.d, σ.p)) =
      (runIdx (pathFlags ρ Hs) ρ.k s).map
        (fun ab => (ab.2 - ab.1, fun i => ρ.d (ab.1 + i), fun i => ρ.p (ab.1 + i))) := by
  intro s
  induction h : ρ.k + 1 - s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases hs : ρ.k < s
    · rw [ρ.runsF_of_lt hρ hs, runIdx_of_lt _ hs]; rfl
    · push Not at hs
      by_cases hps : ρ.p s ∈ hunion Hs
      · rw [ρ.runsF_of_mem hρ hs hps, runIdx_of_mem _ hs (pathFlags_iff.2 hps)]
        exact ih _ (by omega) (s + 1) rfl
      · have hf : pathFlags ρ Hs s = false := by
          cases h' : pathFlags ρ Hs s
          · rfl
          · exact absurd (pathFlags_iff.1 h') hps
        rw [ρ.runsF_of_not_mem hρ hs hps, runIdx_of_not_mem _ hs hf, List.map_cons,
          List.map_cons, ← runEnd_eq_runEndF ρ Hs s hs]
        have hge := ρ.runEnd_ge Hs s hs
        rw [ih _ (by omega) _ rfl]
        rfl

end Pure

/-! ### The programs -/

/-- Write the pair `(r4107, r4105)` at `Ob + 2 r`, `r := r + 1`, leave the run. -/
def rnEmit : Stmt :=
  block [.addN 4111 4102 4108, .addN 4111 4111 4108, .storeN 4111 4107, .addN 4111 4111 4103,
    .storeN 4111 4105, .addN 4108 4108 4103, .constN 4106 0]

/-- At an index off the holes: start a run if none, then end it if the next index is in a hole
or this is the last index. -/
def rnOff : Stmt :=
  .seq (.ifLtN 4104 4106 .skip (block [.copyN 4107 4105, .constN 4106 1]))
    (.seq (block [.addN 4112 4105 4103, .addN 4110 4101 4112, .loadN 4110 4110])
      (.ifLtN 4105 4100 (.ifLtN 4104 4110 rnEmit .skip) rnEmit))

/-- One index of the scan. -/
def rnBody : Stmt :=
  .seq (block [.addN 4109 4101 4105, .loadN 4109 4109])
    (.seq (.ifLtN 4104 4109 .skip rnOff) (block [.addN 4105 4105 4103]))

/-- **The runs on the machine.** -/
def rnProg : Stmt :=
  .seq (block [.constN 4103 1, .constN 4104 0, .constN 4105 0, .constN 4106 0, .constN 4108 0,
    .addN 4113 4100 4103]) (.whileLtN 4105 4113 rnBody)

section Exec

variable {P : Input} {W : ℕ}

/-- The memory after writing a pair. -/
def rnW (m : ℕ → ℕ) (Ob r a b : ℕ) : ℕ → ℕ := upd (upd m (Ob + 2 * r) a) (Ob + 2 * r + 1) b

theorem rnEmit_exec (c : Config) (hc : WordsBounded W c) {Ob r : ℕ}
    (r2 : c.nreg 4102 = Ob) (r3 : c.nreg 4103 = 1) (r8 : c.nreg 4108 = r)
    (w1 : Ob + 2 * r + 1 ≤ W) :
    ∃ c' k, Exec P W rnEmit c c' k ∧ k = 7 ∧ c'.nreg 4108 = r + 1 ∧ c'.nreg 4106 = 0 ∧
      c'.nmem = rnW c.nmem Ob r (c.nreg 4107) (c.nreg 4105) ∧
      (∀ x, x ≠ 4106 → x ≠ 4108 → x ≠ 4111 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rnEmit
  exec_block
  all_goals try ((try config_simp); (try simp only [r2, r3, r8]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r3, r8]
  · config_simp
  · config_simp; simp only [r2, r3, r8, rnW]
    rw [show Ob + r + r = Ob + 2 * r by ring]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

lemma rnIteT {α : Sort*} {p : Prop} [Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := by simp [h]

lemma rnIteF {α : Sort*} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by simp [h]

/-- The end test at the index `i`: the last index, or the next one in a hole. -/
def rnEnd (m : ℕ → ℕ) (Hb k i : ℕ) : Prop := ¬ i < k ∨ 0 < m (Hb + i + 1)

instance (m : ℕ → ℕ) (Hb k i : ℕ) : Decidable (rnEnd m Hb k i) := by
  unfold rnEnd; infer_instance

/-- **An index off the holes.** -/
theorem rnOff_exec (c : Config) (hc : WordsBounded W c) {k Hb Ob i f r : ℕ}
    (r0 : c.nreg 4100 = k) (r1 : c.nreg 4101 = Hb) (r2 : c.nreg 4102 = Ob)
    (r3 : c.nreg 4103 = 1) (r4 : c.nreg 4104 = 0) (r5 : c.nreg 4105 = i) (r6 : c.nreg 4106 = f)
    (r8 : c.nreg 4108 = r) (hf : f ≤ 1) (w1 : Hb + i + 1 ≤ W) (w2 : Ob + 2 * r + 1 ≤ W)
    (w3 : i + 1 ≤ W) :
    ∃ c' t, Exec P W rnOff c c' t ∧ t ≤ 16 ∧
      c'.nreg 4107 = (if f = 0 then i else c.nreg 4107) ∧
      (rnEnd c.nmem Hb k i → c'.nmem = rnW c.nmem Ob r (if f = 0 then i else c.nreg 4107) i ∧
        c'.nreg 4108 = r + 1 ∧ c'.nreg 4106 = 0) ∧
      (¬ rnEnd c.nmem Hb k i → c'.nmem = c.nmem ∧ c'.nreg 4108 = r ∧ c'.nreg 4106 = 1) ∧
      (∀ x, x ≠ 4106 → x ≠ 4107 → x ≠ 4108 → x ≠ 4110 → x ≠ 4111 → x ≠ 4112 →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rnOff
  set st := if f = 0 then i else c.nreg 4107 with hst
  -- the start
  obtain ⟨c₁, k₁, e₁, hk₁, g6, g7, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (.ifLtN 4104 4106 .skip (block [.copyN 4107 4105, .constN 4106 1])) c c₁ k₁ ∧
      k₁ ≤ 4 ∧ c₁.nreg 4106 = 1 ∧ c₁.nreg 4107 = st ∧
      (∀ x, x ≠ 4106 → x ≠ 4107 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    by_cases h0 : c.nreg 4104 < c.nreg 4106
    · have hf1 : f = 1 := by rw [r4, r6] at h0; omega
      refine ⟨c, 1, .ifLtN_true h0 (.skip hc), by omega, by rw [r6, hf1], ?_, fun _ _ _ => rfl,
        rfl, rfl, rfl, rfl⟩
      rw [hst, rnIteF (by omega)]
    · have hf0 : f = 0 := by rw [r4, r6] at h0; omega
      obtain ⟨c₂, k₂, e₂, hk₂, h6, h7, hn₂, hm₂, hr₂, hrm₂, ho₂⟩ : ∃ c₂ k₂,
          Exec P W (block [.copyN 4107 4105, .constN 4106 1]) c c₂ k₂ ∧ k₂ = 2 ∧
          c₂.nreg 4106 = 1 ∧ c₂.nreg 4107 = i ∧
          (∀ x, x ≠ 4106 → x ≠ 4107 → c₂.nreg x = c.nreg x) ∧ c₂.nmem = c.nmem ∧
          c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
        exec_block
        all_goals try ((try config_simp); omega)
        refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp
        · config_simp; exact r5
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      refine ⟨c₂, k₂ + 2, .ifLtN_false h0 e₂, by omega, h6, ?_, hn₂, hm₂, hr₂, hrm₂, ho₂⟩
      rw [h7, hst, rnIteT hf0]
  have hw₁ := e₁.wb_right
  have q0 : c₁.nreg 4100 = k := by rw [gn₁ _ (by omega) (by omega), r0]
  have q1 : c₁.nreg 4101 = Hb := by rw [gn₁ _ (by omega) (by omega), r1]
  have q2 : c₁.nreg 4102 = Ob := by rw [gn₁ _ (by omega) (by omega), r2]
  have q3 : c₁.nreg 4103 = 1 := by rw [gn₁ _ (by omega) (by omega), r3]
  have q4 : c₁.nreg 4104 = 0 := by rw [gn₁ _ (by omega) (by omega), r4]
  have q5 : c₁.nreg 4105 = i := by rw [gn₁ _ (by omega) (by omega), r5]
  have q8 : c₁.nreg 4108 = r := by rw [gn₁ _ (by omega) (by omega), r8]
  -- the next flag
  obtain ⟨c₂, k₂, e₂, hk₂, h10, hn₂, hm₂, hr₂, hrm₂, ho₂⟩ : ∃ c₂ k₂,
      Exec P W (block [.addN 4112 4105 4103, .addN 4110 4101 4112, .loadN 4110 4110]) c₁ c₂ k₂ ∧
      k₂ = 3 ∧ c₂.nreg 4110 = c.nmem (Hb + i + 1) ∧
      (∀ x, x ≠ 4110 → x ≠ 4112 → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [q1, q3, q5]); omega)
    refine ⟨rfl, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [q1, q3, q5, gm₁]; rw [add_assoc]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₂ := e₂.wb_right
  have p0 : c₂.nreg 4100 = k := by rw [hn₂ _ (by omega) (by omega), q0]
  have p2 : c₂.nreg 4102 = Ob := by rw [hn₂ _ (by omega) (by omega), q2]
  have p3 : c₂.nreg 4103 = 1 := by rw [hn₂ _ (by omega) (by omega), q3]
  have p4 : c₂.nreg 4104 = 0 := by rw [hn₂ _ (by omega) (by omega), q4]
  have p5 : c₂.nreg 4105 = i := by rw [hn₂ _ (by omega) (by omega), q5]
  have p7 : c₂.nreg 4107 = st := by rw [hn₂ _ (by omega) (by omega), g7]
  have p8 : c₂.nreg 4108 = r := by rw [hn₂ _ (by omega) (by omega), q8]
  have pm : c₂.nmem = c.nmem := by rw [hm₂, gm₁]
  -- the emission
  obtain ⟨c₃, k₃, e₃, hk₃, h8, h6, hm₃, hn₃, hr₃, hrm₃, ho₃⟩ :=
    rnEmit_exec (P := P) c₂ hw₂ p2 p3 p8 w2
  rw [p7, p5, pm] at hm₃
  have fr : ∀ x, x ≠ 4106 → x ≠ 4107 → x ≠ 4108 → x ≠ 4110 → x ≠ 4111 → x ≠ 4112 →
      c₂.nreg x = c.nreg x := fun x a b d e f g => by rw [hn₂ x e g, gn₁ x a b]
  by_cases hk : c₂.nreg 4105 < c₂.nreg 4100
  · have hik : i < k := by rw [p5, p0] at hk; exact hk
    by_cases hh : c₂.nreg 4104 < c₂.nreg 4110
    · have hE : rnEnd c.nmem Hb k i := Or.inr (by rw [p4, h10] at hh; exact hh)
      refine ⟨c₃, k₁ + (k₂ + (k₃ + 1 + 1)), .seq e₁ (.seq e₂ (.ifLtN_true hk (.ifLtN_true hh e₃))),
        by omega, by rw [hn₃ _ (by omega) (by omega) (by omega), p7], fun _ => ⟨hm₃, h8, h6⟩,
        fun h => absurd hE h, fun x a b d e f g => by rw [hn₃ x a d f, fr x a b d e f g],
        by rw [hr₃, hr₂, gr₁], by rw [hrm₃, hrm₂, grm₁], by rw [ho₃, ho₂, go₁]⟩
    · have hE : ¬ rnEnd c.nmem Hb k i := by
        rintro (h | h)
        · exact h hik
        · rw [p4, h10] at hh; exact hh h
      refine ⟨c₂, k₁ + (k₂ + (0 + 2 + 1)), .seq e₁ (.seq e₂ (.ifLtN_true hk (.ifLtN_false hh
        (.skip hw₂)))), by omega, p7, fun h => absurd h hE, fun _ => ⟨pm, p8, ?_⟩,
        fr, by rw [hr₂, gr₁], by rw [hrm₂, grm₁], by rw [ho₂, go₁]⟩
      rw [hn₂ _ (by omega) (by omega), g6]
  · have hE : rnEnd c.nmem Hb k i := Or.inl (by rw [p5, p0] at hk; exact hk)
    refine ⟨c₃, k₁ + (k₂ + (k₃ + 2)), .seq e₁ (.seq e₂ (.ifLtN_false hk e₃)),
      by omega, by rw [hn₃ _ (by omega) (by omega) (by omega), p7], fun _ => ⟨hm₃, h8, h6⟩,
      fun h => absurd hE h, fun x a b d e f g => by rw [hn₃ x a d f, fr x a b d e f g],
      by rw [hr₃, hr₂, gr₁], by rw [hrm₃, hrm₂, grm₁], by rw [ho₃, ho₂, go₁]⟩

/-- **One index of the scan.** -/
theorem rnBody_exec (c : Config) (hc : WordsBounded W c) {k Hb Ob i f r : ℕ}
    (r0 : c.nreg 4100 = k) (r1 : c.nreg 4101 = Hb) (r2 : c.nreg 4102 = Ob)
    (r3 : c.nreg 4103 = 1) (r4 : c.nreg 4104 = 0) (r5 : c.nreg 4105 = i) (r6 : c.nreg 4106 = f)
    (r8 : c.nreg 4108 = r) (hf : f ≤ 1) (w1 : Hb + i + 1 ≤ W) (w2 : Ob + 2 * r + 1 ≤ W)
    (w3 : i + 1 ≤ W) :
    ∃ c' t, Exec P W rnBody c c' t ∧ t ≤ 21 ∧ c'.nreg 4105 = i + 1 ∧
      (0 < c.nmem (Hb + i) → c'.nmem = c.nmem ∧ c'.nreg 4106 = f ∧
        c'.nreg 4107 = c.nreg 4107 ∧ c'.nreg 4108 = r) ∧
      (¬ 0 < c.nmem (Hb + i) →
        c'.nreg 4107 = (if f = 0 then i else c.nreg 4107) ∧
        (rnEnd c.nmem Hb k i → c'.nmem = rnW c.nmem Ob r (if f = 0 then i else c.nreg 4107) i ∧
          c'.nreg 4108 = r + 1 ∧ c'.nreg 4106 = 0) ∧
        (¬ rnEnd c.nmem Hb k i → c'.nmem = c.nmem ∧ c'.nreg 4108 = r ∧ c'.nreg 4106 = 1)) ∧
      (∀ x, (x < 4105 ∨ 4112 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rnBody
  obtain ⟨c₁, k₁, e₁, hk₁, g9, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 4109 4101 4105, .loadN 4109 4109]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 4109 = c.nmem (Hb + i) ∧ (∀ x, x ≠ 4109 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r1, r5]); omega)
    refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r1, r5]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 4109 → c₁.nreg x = c.nreg x := gn₁
  obtain ⟨c₂, k₂, e₂, hk₂, H1, H2, gn₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (.ifLtN 4104 4109 .skip rnOff) c₁ c₂ k₂ ∧ k₂ ≤ 18 ∧
      (0 < c.nmem (Hb + i) → c₂.nmem = c.nmem ∧ c₂.nreg 4106 = f ∧
        c₂.nreg 4107 = c.nreg 4107 ∧ c₂.nreg 4108 = r) ∧
      (¬ 0 < c.nmem (Hb + i) →
        c₂.nreg 4107 = (if f = 0 then i else c.nreg 4107) ∧
        (rnEnd c.nmem Hb k i → c₂.nmem = rnW c.nmem Ob r (if f = 0 then i else c.nreg 4107) i ∧
          c₂.nreg 4108 = r + 1 ∧ c₂.nreg 4106 = 0) ∧
        (¬ rnEnd c.nmem Hb k i → c₂.nmem = c.nmem ∧ c₂.nreg 4108 = r ∧ c₂.nreg 4106 = 1)) ∧
      (∀ x, (x < 4105 ∨ 4112 < x ∨ x = 4105) → c₂.nreg x = c.nreg x) ∧
      c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    by_cases hh : c₁.nreg 4104 < c₁.nreg 4109
    · have hH : 0 < c.nmem (Hb + i) := by rw [q _ (by omega), r4, g9] at hh; exact hh
      refine ⟨c₁, 1, .ifLtN_true hh (.skip hw₁), by omega, fun _ => ⟨gm₁, ?_, ?_, ?_⟩,
        fun h => absurd hH h, fun x hx => q x (by omega), gr₁, grm₁, go₁⟩
      · rw [q _ (by omega), r6]
      · rw [q _ (by omega)]
      · rw [q _ (by omega), r8]
    · have hH : ¬ 0 < c.nmem (Hb + i) := by rw [q _ (by omega), r4, g9] at hh; exact hh
      obtain ⟨c₂, k₂, e₂, hk₂, h7, hE, hnE, hn₂, hr₂, hrm₂, ho₂⟩ := rnOff_exec (P := P) c₁ hw₁
        (by rw [q _ (by omega), r0]) (by rw [q _ (by omega), r1]) (by rw [q _ (by omega), r2])
        (by rw [q _ (by omega), r3]) (by rw [q _ (by omega), r4]) (by rw [q _ (by omega), r5])
        (by rw [q _ (by omega), r6]) (by rw [q _ (by omega), r8]) hf w1 w2 w3
      rw [gm₁, q 4107 (by omega)] at hE
      rw [gm₁] at hnE
      rw [q 4107 (by omega)] at h7
      refine ⟨c₂, k₂ + 2, .ifLtN_false hh e₂, by omega, fun h => absurd h hH,
        fun _ => ⟨h7, hE, hnE⟩, fun x hx => ?_, by rw [hr₂, gr₁], by rw [hrm₂, grm₁],
        by rw [ho₂, go₁]⟩
      rw [hn₂ x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        q x (by omega)]
  have hw₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, h5, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.addN 4105 4105 4103]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 4105 = i + 1 ∧
      (∀ x, x ≠ 4105 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have p3 : c₂.nreg 4103 = 1 := by rw [gn₂ _ (by omega), r3]
    have p5 : c₂.nreg 4105 = i := by rw [gn₂ _ (by omega), r5]
    exec_block
    all_goals try ((try config_simp); (try simp only [p3, p5]); omega)
    refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [p3, p5]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, h5, fun h => ?_, fun h => ?_,
    fun x hx => by rw [hn₃ x (by omega), gn₂ x (by omega)], by rw [hr₃, gr₂],
    by rw [hrm₃, grm₂], by rw [ho₃, go₂]⟩
  · obtain ⟨a, b, d, e⟩ := H1 h
    exact ⟨by rw [hm₃, a], by rw [hn₃ _ (by omega), b], by rw [hn₃ _ (by omega), d],
      by rw [hn₃ _ (by omega), e]⟩
  · obtain ⟨a, b, d⟩ := H2 h
    refine ⟨by rw [hn₃ _ (by omega), a], fun hE => ?_, fun hE => ?_⟩
    · obtain ⟨x, y, z⟩ := b hE
      exact ⟨by rw [hm₃, x], by rw [hn₃ _ (by omega), y], by rw [hn₃ _ (by omega), z]⟩
    · obtain ⟨x, y, z⟩ := d hE
      exact ⟨by rw [hm₃, x], by rw [hn₃ _ (by omega), y], by rw [hn₃ _ (by omega), z]⟩

lemma rnMem_push {m : ℕ → ℕ} {Ob : ℕ} {out : List (ℕ × ℕ)} (h : RnMem m Ob out) (a b : ℕ) :
    RnMem (rnW m Ob out.length a b) Ob (out ++ [(a, b)]) := by
  intro j hj
  rw [List.length_append, List.length_singleton] at hj
  simp only [rnW, upd_apply]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · rw [List.getD_append _ _ _ _ hj]
    have := h j hj
    split_ifs <;> first | omega | exact this.1 | exact this.2
  · rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    simp

/-- **The runs on the machine**: from the flags `HF[j] = nmem (Hb + j)` (`j ≤ k + 1`,
`Hb + k + 2 ≤ Ob`), within `23 (k + 1) + 8` steps, the count `r4108` and the pairs at
`Ob + 2 j`, `Ob + 2 j + 1` are the list `runIdx H k 0` (`H j = decide (0 < HF[j])`); the memory
outside `[Ob, Ob + 2 r4108)` and the registers outside `4103 … 4113` are kept. -/
theorem rnProg_exec (c : Config) (hc : WordsBounded W c) {k Hb Ob : ℕ}
    (r0 : c.nreg 4100 = k) (r1 : c.nreg 4101 = Hb) (r2 : c.nreg 4102 = Ob)
    (hHO : Hb + k + 2 ≤ Ob) (w1 : Ob + 2 * (k + 1) + 1 ≤ W) :
    ∃ c' t, Exec P W rnProg c c' t ∧ t ≤ 23 * (k + 1) + 8 ∧
      c'.nreg 4108 = (runIdx (fun j => decide (0 < c.nmem (Hb + j))) k 0).length ∧
      RnMem c'.nmem Ob (runIdx (fun j => decide (0 < c.nmem (Hb + j))) k 0) ∧
      (∀ a, (a < Ob ∨ Ob + 2 * c'.nreg 4108 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4103 ∨ 4113 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rnProg
  set H : ℕ → Bool := fun j => decide (0 < c.nmem (Hb + j)) with hH
  obtain ⟨c₁, k₁, e₁, hk₁, g3, g4, g5, g6, g8, g13, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4103 1, .constN 4104 0, .constN 4105 0, .constN 4106 0,
        .constN 4108 0, .addN 4113 4100 4103]) c c₁ k₁ ∧ k₁ = 6 ∧ c₁.nreg 4103 = 1 ∧
      c₁.nreg 4104 = 0 ∧ c₁.nreg 4105 = 0 ∧ c₁.nreg 4106 = 0 ∧ c₁.nreg 4108 = 0 ∧
      c₁.nreg 4113 = k + 1 ∧
      (∀ x, (x < 4103 ∨ 4113 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r0]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; try simp only [r0]; done)
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4105 ∨ 4112 < x) → c'.nreg x = c₁.nreg x) ∧ c'.nreg 4108 ≤ i ∧
    (∀ a, (a < Ob ∨ Ob + 2 * c'.nreg 4108 ≤ a) → c'.nmem a = c.nmem a) ∧
    (∃ out : List (ℕ × ℕ), out.length = c'.nreg 4108 ∧ RnMem c'.nmem Ob out ∧
      RnInv H k i (c'.nreg 4106) (c'.nreg 4107) out) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h5₂, j1, j2, j3, ⟨out, hlen, hmem, hinv⟩, j5, j6, j7⟩ :=
    tgRange (P := P) (a := 4105) (b := 4113) (body := rnBody) J (B := 21) c₁ hw₁ g5 g13
    (Nat.zero_le _)
    ⟨fun _ _ => rfl, by rw [g8], fun a _ => by rw [gm₁], ⟨[], by rw [g8]; rfl,
      fun j hj => absurd hj (by simp), by rw [g6]; exact rnInv_start H k _⟩, rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h5 h13 ⟨j1, j2, j3, ⟨out, hlen, hmem, hinv⟩, j5, j6, j7⟩ => by
      have q0 : c'.nreg 4100 = k := by rw [j1 _ (by omega), gn₁ _ (by omega), r0]
      have q1 : c'.nreg 4101 = Hb := by rw [j1 _ (by omega), gn₁ _ (by omega), r1]
      have q2 : c'.nreg 4102 = Ob := by rw [j1 _ (by omega), gn₁ _ (by omega), r2]
      have q3 : c'.nreg 4103 = 1 := by rw [j1 _ (by omega), g3]
      have q4 : c'.nreg 4104 = 0 := by rw [j1 _ (by omega), g4]
      have hik : i ≤ k := by omega
      have m1 : c'.nmem (Hb + i) = c.nmem (Hb + i) := j3 _ (Or.inl (by omega))
      have m2 : c'.nmem (Hb + i + 1) = c.nmem (Hb + i + 1) := j3 _ (Or.inl (by omega))
      have hEiff : rnEnd c'.nmem Hb k i ↔ (k ≤ i ∨ H (i + 1) = true) := by
        unfold rnEnd; rw [m2, hH]; simp only [decide_eq_true_eq, not_lt, add_assoc]
      obtain ⟨c'', t, ex, ht, h5', HH, HO, hfr, hr', hrm', ho'⟩ := rnBody_exec (P := P) c' hw q0
        q1 q2 q3 q4 h5 rfl rfl (rnInv_le hinv) (by omega) (by omega) (by omega)
      have h13' : c''.nreg 4113 = k + 1 := by rw [hfr _ (by omega)]; exact h13
      have fr' : ∀ x, (x < 4105 ∨ 4112 < x) → c''.nreg x = c₁.nreg x := fun x hx => by
        rw [hfr x hx]; exact j1 x hx
      refine ⟨c'', t, ex, ht, h5', h13', fr', ?_⟩
      by_cases hh : 0 < c'.nmem (Hb + i)
      · obtain ⟨a1, a2, a3, a4⟩ := HH hh
        have hHi : H i = true := by simp only [hH]; rw [← m1]; exact decide_eq_true hh
        refine ⟨by rw [a4]; omega, fun a ha => by rw [a1]; exact j3 a (by rw [← a4]; exact ha),
          ⟨out, by rw [a4, hlen], by rw [a1]; exact hmem, by
            rw [a2, a3]; exact rnInv_hole hinv hik hHi⟩, by rw [hr', j5], by rw [hrm', j6],
          by rw [ho', j7]⟩
      · obtain ⟨a7, aE, aN⟩ := HO hh
        have hHi : H i = false := by simp only [hH]; rw [← m1]; exact decide_eq_false hh
        by_cases hE : rnEnd c'.nmem Hb k i
        · obtain ⟨b1, b2, b3⟩ := aE hE
          refine ⟨by rw [b2]; omega, fun a ha => ?_,
            ⟨out ++ [((if c'.nreg 4106 = 0 then i else c'.nreg 4107), i)],
              by rw [b2, List.length_append, hlen]; rfl, ?_, ?_⟩,
            by rw [hr', j5], by rw [hrm', j6], by rw [ho', j7]⟩
          · rw [b1, rnW, upd_apply, upd_apply, ← j3 a (by rw [b2] at ha; omega)]
            split_ifs <;> first | omega | rfl
          · rw [b1, ← hlen]; exact rnMem_push hmem _ _
          · rw [b3]; exact rnInv_end hinv hik hHi (hEiff.1 hE) _
        · obtain ⟨b1, b2, b3⟩ := aN hE
          refine ⟨by rw [b2]; omega, fun a ha => by rw [b1]; exact j3 a (by rw [← b2]; exact ha),
            ⟨out, by rw [b2, hlen], by rw [b1]; exact hmem, ?_⟩, by rw [hr', j5],
            by rw [hrm', j6], by rw [ho', j7]⟩
          rw [b3, a7]
          exact rnInv_cont hinv hik hHi (fun h => hE (hEiff.2 h)))
  have hout := rnInv_final hinv
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, ?_, by rw [← hlen, hout], by rw [hout]; exact hmem, j3,
    fun x hx => by rw [j1 x (by omega), gn₁ x hx], by rw [j5, gr₁], by rw [j6, grm₁],
    by rw [j7, go₁]⟩
  simp only [Nat.sub_zero] at hk₂
  omega

/-- **The runs of a separator on the machine**: for a simple path through the holes whose flags
`[ρ.p j ∈ hunion Hs]` (`j ≤ ρ.k`) are stored as `0 < HF[j]`, the run of `rnProg` gives the
runs `runsF hρ 0` (the parts `segsF` of the split) as the pairs of indices in memory: the `j`-th
run has `e - a` darts `ρ.d (a + i)` and vertices `ρ.p (a + i)`, `a = nmem (Ob + 2 j)`,
`e = nmem (Ob + 2 j + 1)`, `j < r4108`. -/
theorem rnProg_runsF {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} (ρ : HPath M) {Hs : List (Finset V)}
    (hρ : ρ.Simple Hs) (c : Config) (hc : WordsBounded W c) {Hb Ob : ℕ}
    (r0 : c.nreg 4100 = ρ.k) (r1 : c.nreg 4101 = Hb) (r2 : c.nreg 4102 = Ob)
    (hHO : Hb + ρ.k + 2 ≤ Ob) (w1 : Ob + 2 * (ρ.k + 1) + 1 ≤ W)
    (hF : ∀ j ≤ ρ.k, (0 < c.nmem (Hb + j) ↔ ρ.p j ∈ hunion Hs)) :
    ∃ c' t, Exec P W rnProg c c' t ∧ t ≤ 23 * (ρ.k + 1) + 8 ∧
      (ρ.runsF hρ 0).map (fun σ => (σ.k, σ.d, σ.p)) =
        (List.range (c'.nreg 4108)).map (fun j =>
          (c'.nmem (Ob + 2 * j + 1) - c'.nmem (Ob + 2 * j),
            fun i => ρ.d (c'.nmem (Ob + 2 * j) + i), fun i => ρ.p (c'.nmem (Ob + 2 * j) + i))) ∧
      (∀ a, (a < Ob ∨ Ob + 2 * c'.nreg 4108 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4103 ∨ 4113 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, e, ht, hlen, hmem, rest⟩ := rnProg_exec (P := P) c hc r0 r1 r2 hHO w1
  refine ⟨c', t, e, ht, ?_, rest⟩
  have hH : ∀ j ≤ ρ.k, pathFlags ρ Hs j = decide (0 < c.nmem (Hb + j)) := fun j hj => by
    cases h : pathFlags ρ Hs j
    · have : ρ.p j ∉ hunion Hs := fun h' => by rw [pathFlags_iff.2 h'] at h; cases h
      exact (decide_eq_false (fun h' => this ((hF j hj).1 h'))).symm
    · exact (decide_eq_true ((hF j hj).2 (pathFlags_iff.1 h))).symm
  rw [runsF_data ρ hρ 0, runIdx_congr hH 0, rnMem_eq hmem, ← hlen, List.map_map]
  rfl

end Exec

end BKMNW

end PlanarFlow
