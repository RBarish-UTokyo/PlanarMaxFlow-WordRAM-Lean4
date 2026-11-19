module

public import PlanarFlow.BKMNW.LevelCnt
public import PlanarFlow.BKMNW.ScertIter

/-!
# The loop over the levels of `scertD` as one program

`slProg` runs the levels of the certificate recursion (`lvProg`, `LevelProg.lean`) until a level
is not a prune: `IXb := off; lvProg; if kind = 1 then push the record (off, r4828, r4902) and
off += r4828 else stop`. The pruned indices of the levels lie one after another from `IX0`, the
records (offset, count, anchor index) at `RECb`.

* pure: `scStep_scChoiceE_rec` (the anchor of a prune lies in the kept component, which lies in
  `N`), `scIter_depth` (the depth drops by the number of levels taken), the two word-bound facts
  **`sum_exP`** (a prune keeps the total weight `Σ_N (1 + ex)`) and **`sum_range_exP`** (the weight
  array grows by the pruned weight only);
* `RecOK` (the records in memory), `RecOK.congr`, `RecOK.push`;
* `whileLtN_ghost'` (`whileLtN_ghost` for a ghost state in any universe);
* `slInit`, `slPush`, `slDone`, `slBody`, **`slProg`** (registers `4930 = done`, `4931 = 1`,
  `4932 = off`, `4933 = ℓ`, `4935` scratch written; inputs `4936 = RECb`, `4937 = IX0`);
* **`slProg_exec`**: for the choices `scChoiceE`, a bound `L ≥ scDepth` (at most `nTouch ≤ 6`
  on the pieces of the decomposition, `scDepth_le_nTouch`), within
  `(L + 1) (|Hs| (160 n + 36) + 244 n + 110) + 6` steps the loop stops after `ℓ ≤ L` prunes at a
  state `s` with `scIter … ℓ (N, τ, ex) = some (s, rs)`, `scStep … s = none`,
  **`scertD … N τ ex = (scBase … s).map (·.1, applyPr Hs ·.1 rs ·.2)`**, the final level's outcome
  `LvOut` (kind `0`: `NoCut`, Miller's case; `2`: the cut; `3`: failure) and the input `LvIn` of `s`
  in memory, and the records `rs` in memory (`RecOK`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### Pure facts -/

section Pure

open Equiv Orbit

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

open Classical in
/-- **The record of a prune** for the choices `scChoiceE`: the anchor lies in the kept
component, which lies in the darts before the prune. -/
theorem scStep_scChoiceE_rec {sepF : SepFn M} {e : ℕ → D} {n : ℕ} {Hs : List (Finset V)}
    {A W₀ : ℕ} {s s' : ScSt D} {r : ScRec D}
    (h : scStep (scChoiceE M sepF e n Hs A W₀) Hs s = some (s', r)) :
    r.2.2 ∈ r.2.1 ∧ r.2.1 ⊆ r.1 := by
  obtain ⟨N, τ, ex⟩ := s
  set ch := scChoiceE M sepF e n Hs A W₀ with hch
  by_cases hnc : NoCut M N Hs
  · simp [scStep, hnc] at h
  rcases hh : ch.hole N with _ | g
  · simp [scStep, hnc, hh] at h
  rcases hz : ch.heavy N g ex with _ | z
  · simp [scStep, hnc, hh, hz] at h
  rcases ha : ch.anchor (comp M N Hs g z) g with _ | a₀
  · simp [scStep, hnc, hh, hz, ha] at h
  by_cases hK : (comp M N Hs g z).card < N.card
  · simp only [scStep, hnc, hh, hz, ha, hK, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    refine ⟨?_, fun d hd => (mem_comp.1 hd).1⟩
    exact (mem_filter.1 (findE_some (X := (comp M N Hs g z).filter fun a => M.tail a ∈ g) ha)).1
  · simp [scStep, hnc, hh, hz, ha, hK] at h

/-- **The depth along the levels taken**: `ℓ` prunes lower the depth by `ℓ` and give `ℓ`
records. -/
theorem scIter_depth (ch : ScChoice M) (Hs : List (Finset V)) :
    ∀ (ℓ : ℕ) (s s' : ScSt D) (rs : List (ScRec D)), scIter ch Hs ℓ s = some (s', rs) →
      scDepth ch Hs s.1 s.2.1 s.2.2 = scDepth ch Hs s'.1 s'.2.1 s'.2.2 + ℓ ∧ rs.length = ℓ := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro s s' rs h
    simp only [scIter, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | succ ℓ ih =>
    intro s s' rs h
    rw [scIter] at h
    cases hs : scStep ch Hs s with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨s₁, r₁⟩ := p
      rw [hs] at h
      simp only at h
      cases h1 : scIter ch Hs ℓ s₁ with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some q =>
        obtain ⟨s₂, rs₂⟩ := q
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨d1, d2⟩ := ih s₁ s₂ rs₂ h1
        refine ⟨by rw [scDepth_step hs, d1]; omega, by simp [d2]⟩

/-- **A prune keeps the total weight** (word-bound fact 1): with the anchor in the kept component
`K ⊆ N`, `Σ_K (1 + ex') = Σ_N (1 + ex)`. -/
theorem sum_exP {N K : Finset D} {ex : D → ℕ} {a₀ : D} (ha : a₀ ∈ K) (hK : K ⊆ N) :
    ∑ d ∈ K, (1 + exP N K ex a₀ d) = ∑ d ∈ N, (1 + ex d) := by
  unfold exP
  have h1 : ∑ d ∈ K, (1 + (ex d + if d = a₀ then ∑ d ∈ N \ K, (1 + ex d) else 0)) =
      ∑ d ∈ K, (1 + ex d) + ∑ d ∈ K, (if d = a₀ then ∑ d ∈ N \ K, (1 + ex d) else 0) := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun d _ => by omega
  rw [h1, sum_ite_eq' K a₀]
  simp only [ha, ↓reduceIte]
  have := sum_sdiff hK (f := fun d => 1 + ex d)
  omega

/-- **The weight array after a prune** (word-bound fact 2): one cell grows by the pruned weight,
so the total over the indices grows by `Σ_{N \ K} (1 + ex)`. -/
theorem sum_range_exP {e : ℕ → D} {n a : ℕ} (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    (ha : a < n) (N K : Finset D) (ex : D → ℕ) :
    ∑ j ∈ range n, (1 + exP N K ex (e a) (e j)) =
      ∑ j ∈ range n, (1 + ex (e j)) + ∑ d ∈ N \ K, (1 + ex d) := by
  unfold exP
  have h1 : ∀ j ∈ range n, (1 + (ex (e j) + if e j = e a then ∑ d ∈ N \ K, (1 + ex d) else 0)) =
      (1 + ex (e j)) + if j = a then ∑ d ∈ N \ K, (1 + ex d) else 0 := fun j hj => by
    have hj' := mem_range.1 hj
    by_cases hja : j = a
    · subst hja; simp only [↓reduceIte]; omega
    · have : e j ≠ e a := fun h => hja (hinj j hj' a ha h)
      simp [this, hja]
  rw [sum_congr rfl h1, sum_add_distrib, sum_ite_eq' (range n) a]
  simp only [mem_range.2 ha, ↓reduceIte]

/-- The total weight of `N` is at most the total of the weight array. -/
theorem sum_le_range {e : ℕ → D} {n : ℕ} {N : Finset D} {nf exA : ℕ → ℕ} {ex : D → ℕ}
    (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) (hsurjN : ∀ d ∈ N, ∃ i < n, e i = d)
    (hnf : ∀ i < n, (nf i ≠ 0 ↔ e i ∈ N)) (hex : ∀ i < n, exA i = ex (e i)) :
    ∑ d ∈ N, (1 + ex d) ≤ ∑ j ∈ range n, (1 + exA j) := by
  rw [← sum_lpV hinj hsurjN hnf hex]
  exact sum_le_sum fun j _ => lpV_le _ _

end Pure

/-! ### The records in memory -/

section Rec

variable {D : Type*} [DecidableEq D]

/-- **The records of the levels in memory**: record `k` (the `k`-th prune, i.e. `rs.reverse[k]`)
is `(OFF, CNT, AI)` at `RECb + 3 k`: the anchor index `AI < n` (the anchor is `e AI`), `0 < CNT ≤ n`
pruned indices `< n` at `OFF … OFF + CNT - 1` (between `IX0` and `top`), whose image under `e` is
`N \ K` of the record. -/
def RecOK (m : ℕ → ℕ) (RECb IX0 top n : ℕ) (e : ℕ → D) (rs : List (Finset D × Finset D × D)) :
    Prop :=
  ∀ k (hk : k < rs.length),
    m (RECb + 3 * k + 2) < n ∧ 0 < m (RECb + 3 * k + 1) ∧ m (RECb + 3 * k + 1) ≤ n ∧
    IX0 ≤ m (RECb + 3 * k) ∧ m (RECb + 3 * k) + m (RECb + 3 * k + 1) ≤ top ∧
    (∀ j < m (RECb + 3 * k + 1), m (m (RECb + 3 * k) + j) < n) ∧
    (rs.reverse[k]'(by simpa using hk)).2.2 = e (m (RECb + 3 * k + 2)) ∧
    ((range (m (RECb + 3 * k + 1))).image fun j => m (m (RECb + 3 * k) + j)).image e =
      (rs.reverse[k]'(by simpa using hk)).1 \ (rs.reverse[k]'(by simpa using hk)).2.1

lemma RecOK.nil (m : ℕ → ℕ) (RECb IX0 top n : ℕ) (e : ℕ → D) : RecOK m RECb IX0 top n e [] :=
  fun k hk => absurd hk (by simp)

lemma RecOK.congr {m m' : ℕ → ℕ} {RECb IX0 top top' n : ℕ} {e : ℕ → D}
    {rs : List (Finset D × Finset D × D)} (h : RecOK m RECb IX0 top n e rs) (htop : top ≤ top')
    (h1 : ∀ a, RECb ≤ a → a < RECb + 3 * rs.length → m' a = m a)
    (h2 : ∀ a, IX0 ≤ a → a < top → m' a = m a) : RecOK m' RECb IX0 top' n e rs := by
  intro k hk
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h k hk
  have q0 : m' (RECb + 3 * k) = m (RECb + 3 * k) := h1 _ (by omega) (by omega)
  have q1 : m' (RECb + 3 * k + 1) = m (RECb + 3 * k + 1) := h1 _ (by omega) (by omega)
  have q2 : m' (RECb + 3 * k + 2) = m (RECb + 3 * k + 2) := h1 _ (by omega) (by omega)
  have q3 : ∀ j < m (RECb + 3 * k + 1), m' (m (RECb + 3 * k) + j) = m (m (RECb + 3 * k) + j) :=
    fun j hj => h2 _ (by omega) (by omega)
  refine ⟨by rw [q2]; exact a1, by rw [q1]; exact a2, by rw [q1]; exact a3, by rw [q0]; exact a4,
    by rw [q0, q1]; omega, fun j hj => by rw [q0] ; rw [q1] at hj; rw [q3 j hj]; exact a6 j hj,
    by rw [q2]; exact a7, ?_⟩
  rw [q0, q1, image_congr (g := fun j => m (m (RECb + 3 * k) + j))
    (fun j hj => q3 j (mem_range.1 (mem_coe.1 hj)))]
  exact a8

lemma RecOK.push {m m' : ℕ → ℕ} {RECb IX0 top n ℓ cnt a : ℕ} {e : ℕ → D}
    {rs : List (Finset D × Finset D × D)} {r : Finset D × Finset D × D}
    (h : RecOK m RECb IX0 top n e rs) (hlen : rs.length = ℓ) (hlay : RECb + 3 * ℓ + 3 ≤ IX0)
    (hIX : IX0 ≤ top)
    (m0 : m' (RECb + 3 * ℓ) = top) (m1 : m' (RECb + 3 * ℓ + 1) = cnt)
    (m2 : m' (RECb + 3 * ℓ + 2) = a)
    (hm : ∀ x, x ≠ RECb + 3 * ℓ → x ≠ RECb + 3 * ℓ + 1 → x ≠ RECb + 3 * ℓ + 2 → m' x = m x)
    (ha : a < n) (hc0 : 0 < cnt) (hcn : cnt ≤ n) (hent : ∀ j < cnt, m (top + j) < n)
    (hr : r.2.2 = e a) (himg : ((range cnt).image fun j => m (top + j)).image e = r.1 \ r.2.1)
    (hrec : ∀ k < ℓ, RECb + 3 * k + 2 < RECb + 3 * ℓ) :
    RecOK m' RECb IX0 (top + cnt) n e (r :: rs) := by
  have hold : RecOK m' RECb IX0 (top + cnt) n e rs := h.congr (by omega)
    (fun x h1 h2 => hm x (by omega) (by omega) (by omega))
    (fun x h1 h2 => hm x (by omega) (by omega) (by omega))
  intro k hk
  simp only [List.length_cons] at hk
  have hrev : (r :: rs).reverse = rs.reverse ++ [r] := List.reverse_cons
  by_cases hkl : k < ℓ
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hold k (by omega)
    have g : ((r :: rs).reverse[k]'(by simp; omega)) = rs.reverse[k]'(by simp; omega) := by
      simp only [hrev]
      exact List.getElem_append_left (by simp; omega)
    rw [g]
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
  · have hk' : k = ℓ := by omega
    subst hk'
    have g : ((r :: rs).reverse[k]'(by simp; omega)) = r := by
      simp only [hrev]
      rw [List.getElem_append_right (by simp; omega)]
      simp [hlen]
    rw [g]
    have q : ∀ j < cnt, m' (top + j) = m (top + j) := fun j hj => hm _ (by omega) (by omega) (by omega)
    refine ⟨by rw [m2]; exact ha, by rw [m1]; exact hc0, by rw [m1]; exact hcn, by rw [m0]; exact hIX,
      by rw [m0, m1], fun j hj => by rw [m0]; rw [m1] at hj; rw [q j hj]; exact hent j hj,
      by rw [m2]; exact hr, ?_⟩
    rw [m0, m1, image_congr (g := fun j => m (top + j)) (fun j hj => q j (mem_range.1 (mem_coe.1 hj)))]
    exact himg

end Rec

/-! ### The program -/

/-- A loop with a ghost state in any universe (`whileLtN_ghost`). -/
theorem whileLtN_ghost' {P : Input} {W : ℕ} {α : Type*} {a b : ℕ} {body : Stmt}
    (I : α → Config → Prop)
    (Φ : α → Config → ℕ) (hI : ∀ x c, I x c → WordsBounded W c)
    (hbody : ∀ x c, I x c → c.nreg a < c.nreg b →
      ∃ x' c' k, Exec P W body c c' k ∧ I x' c' ∧ Φ x' c' + k + 2 ≤ Φ x c)
    {x : α} {c : Config} (hc : I x c) :
    ∃ x' c' k, Exec P W (.whileLtN a b body) c c' k ∧ I x' c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ Φ x c + 2 := by
  induction hn : Φ x c using Nat.strong_induction_on generalizing x c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨x₁, c₁, k₁, hb, hI₁, hΦ⟩ := hbody x c hc ht
      obtain ⟨x', c', k₂, hl, hI', ht', hk₂⟩ := ih (Φ x₁ c₁) (by omega) hI₁ rfl
      exact ⟨x', c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', by omega⟩
    · exact ⟨x, c, 2, .whileLtN_false ht (hI x c hc), hc, ht, by omega⟩

/-- The start of the loop (`done := 0`, `1`, `off := IX0`, `ℓ := 0`). -/
def slInit : Stmt := block [.constN 4930 0, .constN 4931 1, .copyN 4932 4937, .constN 4933 0]

/-- Push the record `(off, r4828, r4902)` at `RECb + 3 ℓ`; `off += r4828`; `ℓ += 1`. -/
def slPush : Stmt :=
  block [.addN 4935 4933 4933, .addN 4935 4935 4933, .addN 4935 4935 4936, .storeN 4935 4932,
    .addN 4935 4935 4931, .storeN 4935 4828, .addN 4935 4935 4931, .storeN 4935 4902,
    .addN 4932 4932 4828, .addN 4933 4933 4931]

/-- Stop. -/
def slDone : Stmt := block [.constN 4930 1]

/-- One level: `IXb := off`, the level, then the push (kind `1`) or stop. -/
def slBody : Stmt :=
  .seq (block [.copyN 4825 4932])
    (.seq lvProg (.ifLtN 4900 4931 slDone (.ifLtN 4931 4900 slDone slPush)))

/-- **The loop over the levels of `scertD`.** -/
def slProg : Stmt := .seq slInit (.whileLtN 4930 4931 slBody)

section Exec

variable {P : Input} {W : ℕ}

theorem slInit_exec (c : Config) (hc : WordsBounded W c) {IX0 : ℕ} (r37 : c.nreg 4937 = IX0)
    (w : 1 ≤ W) :
    ∃ c' t, Exec P W slInit c c' t ∧ t = 4 ∧ c'.nreg 4930 = 0 ∧ c'.nreg 4931 = 1 ∧
      c'.nreg 4932 = IX0 ∧ c'.nreg 4933 = 0 ∧
      (∀ x, (x < 4930 ∨ 4933 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold slInit
  exec_block
  all_goals try (config_simp; (try simp only [r37]); omega)
  refine ⟨rfl, by config_simp, by config_simp, by config_simp; exact r37, by config_simp,
    fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  simp only [Config.nreg_mk, upd_other _ _ _ (show x ≠ 4930 by omega),
    upd_other _ _ _ (show x ≠ 4931 by omega), upd_other _ _ _ (show x ≠ 4932 by omega),
    upd_other _ _ _ (show x ≠ 4933 by omega)]

theorem slDone_exec (c : Config) (hc : WordsBounded W c) (w : 1 ≤ W) :
    ∃ c' t, Exec P W slDone c c' t ∧ t = 1 ∧ c'.nreg 4930 = 1 ∧
      (∀ x, x ≠ 4930 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold slDone
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, by config_simp, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  simp only [Config.nreg_mk, upd_other _ _ _ hx]

theorem slPush_exec (c : Config) (hc : WordsBounded W c) {ℓ RECb off cnt a : ℕ}
    (r33 : c.nreg 4933 = ℓ) (r36 : c.nreg 4936 = RECb) (r31 : c.nreg 4931 = 1)
    (r32 : c.nreg 4932 = off) (r28 : c.nreg 4828 = cnt) (r02 : c.nreg 4902 = a)
    (w1 : RECb + 3 * ℓ + 2 ≤ W) (w2 : off + cnt ≤ W) (w3 : ℓ + 1 ≤ W) :
    ∃ c' t, Exec P W slPush c c' t ∧ t = 10 ∧ c'.nreg 4932 = off + cnt ∧ c'.nreg 4933 = ℓ + 1 ∧
      c'.nmem (RECb + 3 * ℓ) = off ∧ c'.nmem (RECb + 3 * ℓ + 1) = cnt ∧
      c'.nmem (RECb + 3 * ℓ + 2) = a ∧
      (∀ x, x ≠ RECb + 3 * ℓ → x ≠ RECb + 3 * ℓ + 1 → x ≠ RECb + 3 * ℓ + 2 →
        c'.nmem x = c.nmem x) ∧
      (∀ x, x ≠ 4932 → x ≠ 4933 → x ≠ 4935 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold slPush
  exec_block
  all_goals try (config_simp; (try simp only [r31, r32, r33, r36, r28, r02]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 h3 => ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp only [r31, r32, r33, r36, r28, r02, upd_apply]
  all_goals split_ifs <;> omega

end Exec

/-! ### The loop -/

/-- `LvRegs.of_frame` from the registers below `4921` only. -/
theorem LvRegs.of_frame' {c c' : Config} {n b nH A W₀ : ℕ} (h : LvRegs c n b nH A W₀)
    (hf : ∀ x, LvFr x → x < 4921 → c'.nreg x = c.nreg x) : LvRegs c' n b nH A W₀ := by
  have f : ∀ x, LvFr x → x < 4921 → c'.nreg x = c.nreg x := hf
  obtain ⟨p0, p1, p2, p3, p6, p7, p8, p9, p10, r0, r1, r2, r3, r4, r5, r6, s0, s1, s2, s3, s4,
    u0, u1, u2, v4, l0, l1, l2, l3, l5, l6, l7, l8, a0, a1, a2, a3, a4, h0, h1, h2, h3, h4, h5,
    c0, k0, k1, k2, k4, y0, y1, y2⟩ := h
  exact ⟨by rw [f _ (by unfold LvFr; omega) (by omega), p0], by rw [f _ (by unfold LvFr; omega) (by omega), p1],
    by rw [f _ (by unfold LvFr; omega) (by omega), p2], by rw [f _ (by unfold LvFr; omega) (by omega), p3],
    by rw [f _ (by unfold LvFr; omega) (by omega), p6], by rw [f _ (by unfold LvFr; omega) (by omega), p7],
    by rw [f _ (by unfold LvFr; omega) (by omega), p8], by rw [f _ (by unfold LvFr; omega) (by omega), p9],
    by rw [f _ (by unfold LvFr; omega) (by omega), p10], by rw [f _ (by unfold LvFr; omega) (by omega), r0],
    by rw [f _ (by unfold LvFr; omega) (by omega), r1], by rw [f _ (by unfold LvFr; omega) (by omega), r2],
    by rw [f _ (by unfold LvFr; omega) (by omega), r3], by rw [f _ (by unfold LvFr; omega) (by omega), r4],
    by rw [f _ (by unfold LvFr; omega) (by omega), r5], by rw [f _ (by unfold LvFr; omega) (by omega), r6],
    by rw [f _ (by unfold LvFr; omega) (by omega), s0], by rw [f _ (by unfold LvFr; omega) (by omega), s1],
    by rw [f _ (by unfold LvFr; omega) (by omega), s2], by rw [f _ (by unfold LvFr; omega) (by omega), s3],
    by rw [f _ (by unfold LvFr; omega) (by omega), s4], by rw [f _ (by unfold LvFr; omega) (by omega), u0],
    by rw [f _ (by unfold LvFr; omega) (by omega), u1], by rw [f _ (by unfold LvFr; omega) (by omega), u2],
    by rw [f _ (by unfold LvFr; omega) (by omega), v4], by rw [f _ (by unfold LvFr; omega) (by omega), l0],
    by rw [f _ (by unfold LvFr; omega) (by omega), l1], by rw [f _ (by unfold LvFr; omega) (by omega), l2],
    by rw [f _ (by unfold LvFr; omega) (by omega), l3], by rw [f _ (by unfold LvFr; omega) (by omega), l5],
    by rw [f _ (by unfold LvFr; omega) (by omega), l6], by rw [f _ (by unfold LvFr; omega) (by omega), l7],
    by rw [f _ (by unfold LvFr; omega) (by omega), l8], by rw [f _ (by unfold LvFr; omega) (by omega), a0],
    by rw [f _ (by unfold LvFr; omega) (by omega), a1], by rw [f _ (by unfold LvFr; omega) (by omega), a2],
    by rw [f _ (by unfold LvFr; omega) (by omega), a3], by rw [f _ (by unfold LvFr; omega) (by omega), a4],
    by rw [f _ (by unfold LvFr; omega) (by omega), h0], by rw [f _ (by unfold LvFr; omega) (by omega), h1],
    by rw [f _ (by unfold LvFr; omega) (by omega), h2], by rw [f _ (by unfold LvFr; omega) (by omega), h3],
    by rw [f _ (by unfold LvFr; omega) (by omega), h4], by rw [f _ (by unfold LvFr; omega) (by omega), h5],
    by rw [f _ (by unfold LvFr; omega) (by omega), c0], by rw [f _ (by unfold LvFr; omega) (by omega), k0],
    by rw [f _ (by unfold LvFr; omega) (by omega), k1], by rw [f _ (by unfold LvFr; omega) (by omega), k2],
    by rw [f _ (by unfold LvFr; omega) (by omega), k4], by rw [f _ (by unfold LvFr; omega) (by omega), y0],
    by rw [f _ (by unfold LvFr; omega) (by omega), y1], by rw [f _ (by unfold LvFr; omega) (by omega), y2]⟩


section Loop

open Equiv Orbit

variable {P : Input} {W : ℕ}
variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The memory cells the loop keeps: below the layout, between the layout and the records,
between the records and the pruned indices, above the pruned indices. -/
def SlKept (n b RECb IX0 L a : ℕ) : Prop :=
  a < b ∨ (b + 20 * n + 3 ≤ a ∧ a < RECb) ∨ (RECb + 3 * L ≤ a ∧ a < IX0) ∨
    IX0 + L * n + n + 1 ≤ a

/-- The registers the loop keeps. -/
def SlFr (x : ℕ) : Prop := LvFr x ∧ (x < 4930 ∨ 4935 < x)

/-- The cost bound of one iteration. -/
def slBk (nH n : ℕ) : ℕ := nH * (160 * n + 36) + 244 * n + 110

/-- The potential of the loop. -/
def slPot (L Bk : ℕ) (x : ℕ × ScSt D × List (ScRec D)) (c : Config) : ℕ :=
  (1 - c.nreg 4930) * ((L + 1 - x.1) * Bk)

lemma LvOut.ne_one {ch : ScChoice M} {Hs : List (Finset V)} {s : ScSt D} {m₀ : ℕ → ℕ}
    {c' : Config} {n b IXb : ℕ} {e : ℕ → D} (h : LvOut M ch Hs s m₀ c' n b IXb e)
    (h1 : c'.nreg 4900 ≠ 1) :
    scStep ch Hs s = none ∧ (∀ i < n, c'.nmem (b + i) = m₀ (b + i)) ∧
      ∀ i < n, c'.nmem (b + 3 * n + i) = m₀ (b + 3 * n + i) := by
  rcases h with ⟨a1, a2, a3, a4⟩ | ⟨a1, -⟩ | ⟨a1, a2, g, -, -, -, a6, a7⟩ | ⟨a1, a2, -, a4, a5⟩
  · exact ⟨scStep_noCut a2, a3, a4⟩
  · exact absurd a1 h1
  · exact ⟨a2, a6, a7⟩
  · exact ⟨a2, a4, a5⟩

open Classical in
lemma LvOut.one {ch : ScChoice M} {Hs : List (Finset V)} {s : ScSt D} {m₀ : ℕ → ℕ}
    {c' : Config} {n b IXb : ℕ} {e : ℕ → D} (h : LvOut M ch Hs s m₀ c' n b IXb e)
    (h1 : c'.nreg 4900 = 1) :
    ∃ K : Finset D, ∃ a₀ < n, c'.nreg 4902 = a₀ ∧
      scStep ch Hs s = some ((K, ret s.2.1 K, exP s.1 K s.2.2 (e a₀)), (s.1, K, e a₀)) ∧
      (∀ i < n, (c'.nmem (b + i) ≠ 0 ↔ e i ∈ K)) ∧
      (∀ i < n, c'.nmem (b + 3 * n + i) = exP s.1 K s.2.2 (e a₀) (e i)) ∧
      0 < c'.nreg 4828 ∧ (∀ k < c'.nreg 4828, c'.nmem (IXb + k) < n) ∧
      ((range (c'.nreg 4828)).image fun k => c'.nmem (IXb + k)).image e = s.1 \ K := by
  rcases h with ⟨a1, -⟩ | ⟨-, h⟩ | ⟨a1, -⟩ | ⟨a1, -⟩
  · rw [a1] at h1; exact absurd h1 (by decide)
  · exact h
  · rw [a1] at h1; exact absurd h1 (by decide)
  · rw [a1] at h1; exact absurd h1 (by decide)

lemma LvOut.congrC {ch : ScChoice M} {Hs : List (Finset V)} {s : ScSt D} {m₀ : ℕ → ℕ}
    {c' c'' : Config} {n b IXb : ℕ} {e : ℕ → D} (h : LvOut M ch Hs s m₀ c' n b IXb e)
    (hm : c''.nmem = c'.nmem) (h0 : c''.nreg 4900 = c'.nreg 4900)
    (h1 : c''.nreg 4901 = c'.nreg 4901) (h2 : c''.nreg 4902 = c'.nreg 4902)
    (h28 : c''.nreg 4828 = c'.nreg 4828) : LvOut M ch Hs s m₀ c'' n b IXb e := by
  unfold LvOut at h ⊢
  rw [hm, h0, h1, h2, h28]
  exact h

/-- The input of a level from its cells: the kept cells `TH`, `RV0`, `TK`, new flags and
weights. -/
lemma LvIn.of_cells {m m' : ℕ → ℕ} {n b : ℕ} {e : ℕ → D} {B N K : Finset D}
    {Hs : List (Finset V)} {ex ex' : D → ℕ} (h : LvIn M m n b e B N Hs ex) (hK : K ⊆ N)
    (hk : ∀ a, ((b + n ≤ a ∧ a < b + 3 * n) ∨ (b + 6 * n ≤ a ∧ a < b + 7 * n)) → m' a = m a)
    (hnf : ∀ i < n, (m' (b + i) ≠ 0 ↔ e i ∈ K)) (hex : ∀ i < n, m' (b + 3 * n + i) = ex' (e i)) :
    LvIn M m' n b e B K Hs ex' :=
  ⟨h.mem, h.surj, h.inj, hK.trans h.sub,
    fun i hi => by rw [hk _ (by omega)]; exact h.rv0 i hi, hnf,
    fun i hi j hj => by rw [hk _ (by omega)]; exact h.th i hi j hj,
    fun i hi => by rw [hk _ (by omega)]; exact h.tk i hi,
    fun i hi j hj => by rw [hk _ (by omega), hk _ (by omega)]; exact h.key i hi j hj, hex⟩

variable (W M) in
/-- **The invariant of the level loop** (ghost state `x = (ℓ, s, rs)`: `ℓ` prunes taken from
`s₀`, reaching `s` with the records `rs`). -/
structure SlInv (ch : ScChoice M) (Hs : List (Finset V)) (s₀ : ScSt D) (c₀ : Config)
    (n b A W₀ RECb IX0 L T₀ : ℕ) (e : ℕ → D) (B : Finset D)
    (x : ℕ × ScSt D × List (ScRec D)) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : LvRegs c n b Hs.length A W₀
  one : c.nreg 4931 = 1
  recb : c.nreg 4936 = RECb
  cnt : c.nreg 4933 = x.1
  iter : scIter ch Hs x.1 s₀ = some (x.2.1, x.2.2)
  dep : x.1 + scDepth ch Hs x.2.1.1 x.2.1.2.1 x.2.1.2.2 ≤ L
  off1 : IX0 ≤ c.nreg 4932
  off2 : c.nreg 4932 ≤ IX0 + x.1 * n
  recs : RecOK c.nmem RECb IX0 (c.nreg 4932) n e x.2.2
  len : x.2.2.length = x.1
  mem : ∀ a, SlKept n b RECb IX0 L a → c.nmem a = c₀.nmem a
  reg : ∀ r, SlFr r → c.nreg r = c₀.nreg r
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
  st : (c.nreg 4930 = 0 ∧ LvIn M c.nmem n b e B x.2.1.1 Hs x.2.1.2.2 ∧
      ∑ j ∈ range n, (1 + c.nmem (b + 3 * n + j)) ≤ (x.1 + 1) * T₀ ∧
      ∑ d ∈ x.2.1.1, (1 + x.2.1.2.2 d) ≤ T₀) ∨
    (c.nreg 4930 = 1 ∧ c.nreg 4900 ≠ 1 ∧ LvIn M c.nmem n b e B x.2.1.1 Hs x.2.1.2.2 ∧
      LvOut M ch Hs x.2.1 c.nmem c n b (c.nreg 4932) e ∧
      (c.nreg 4900 = 2 → ∀ i < n, 0 < c.nmem (b + 13 * n + 1 + i) ∧
        c.nmem (b + 13 * n + 1 + i) ≤ n))

set_option maxHeartbeats 1600000 in
open Classical in
/-- **One iteration of the level loop.** -/
theorem slBody_step (sepF : SepFn M) {e : ℕ → D} {B : Finset D} {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) {s₀ : ScSt D} {c₀ : Config} {n b A W₀ RECb IX0 L T₀ : ℕ}
    (hHW : Hs.length + 1 ≤ W)
    (lay : b + 20 * n + 3 ≤ RECb ∧ RECb + 3 * L ≤ IX0 ∧ IX0 + L * n + n + 1 ≤ W)
    (hS : A + 2 * ((L + 1) * T₀) ≤ W)
    (x : ℕ × ScSt D × List (ScRec D)) (c : Config)
    (hI : SlInv W M (scChoiceE M sepF e n Hs A W₀) Hs s₀ c₀ n b A W₀ RECb IX0 L T₀ e B x c)
    (ht : c.nreg 4930 < c.nreg 4931) :
    ∃ x' c' k, Exec P W slBody c c' k ∧
      SlInv W M (scChoiceE M sepF e n Hs A W₀) Hs s₀ c₀ n b A W₀ RECb IX0 L T₀ e B x' c' ∧
      slPot L (slBk Hs.length n) x' c' + k + 2 ≤ slPot L (slBk Hs.length n) x c := by
  obtain ⟨ℓ, ⟨N, τ, ex⟩, rs⟩ := x
  obtain ⟨wb, hR, one, recb, cnt, iter, dep, o1, o2, recs, len, mem, reg, rr, rm, out, st⟩ := hI
  dsimp only at cnt iter dep o2 recs len st
  rcases st with ⟨d0, hIn, hT, hSb⟩ | ⟨d1, -⟩
  swap
  · rw [d1, one] at ht; omega
  obtain ⟨l1, l2, l3⟩ := lay
  set Bk := slBk Hs.length n with hBk
  have hℓ : ℓ ≤ L := by omega
  set off := c.nreg 4932 with hoff
  have hℓn : ℓ * n ≤ L * n := Nat.mul_le_mul_right n hℓ
  have hBk1 : Bk ≤ (L + 1 - ℓ) * Bk := Nat.le_mul_of_pos_left _ (by omega)
  -- 1. `IXb := off`
  obtain ⟨c₁, k₁, e₁, hk₁, g25, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 4825 4932]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 4825 = off ∧
      (∀ x, x ≠ 4825 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    refine ⟨rfl, by config_simp; exact hoff.symm, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    simp only [Config.nreg_mk, upd_other _ _ _ h1]
  have hw₁ := e₁.wb_right
  have hR₁ : LvRegs c₁ n b Hs.length A W₀ :=
    hR.of_frame fun x hx => gn₁ x (by unfold LvFr at hx; omega)
  have hIn₁ : LvIn M c₁.nmem n b e B N Hs ex := by rw [gm₁]; exact hIn
  have hT' : (ℓ + 1) * T₀ ≤ (L + 1) * T₀ := Nat.mul_le_mul_right _ (by omega)
  have hS₁ : A + 2 * ∑ j ∈ range n, (1 + c₁.nmem (b + 3 * n + j)) ≤ W := by rw [gm₁]; omega
  -- 2. the level
  obtain ⟨c₂, k₂, e₂, hk₂, ⟨LO, LC, LC2⟩, LK, LF, L25, Lr, Lrm, Lo⟩ := lvProg_exec' (P := P) (τ := τ)
    sepF hd c₁ hw₁ hR₁ hIn₁ g25 hHW ⟨by omega, by omega⟩ hS₁
  have hw₂ := e₂.wb_right
  have f₂ : ∀ x, LvFr x → c₂.nreg x = c.nreg x := fun x hx => by
    have hx' := hx; unfold LvFr at hx'; rw [LF x hx, gn₁ x (by omega)]
  have t30 : c₂.nreg 4930 = 0 := by rw [f₂ _ (by unfold LvFr; omega), d0]
  have t31 : c₂.nreg 4931 = 1 := by rw [f₂ _ (by unfold LvFr; omega), one]
  have t32 : c₂.nreg 4932 = off := by rw [f₂ _ (by unfold LvFr; omega)]
  have t33 : c₂.nreg 4933 = ℓ := by rw [f₂ _ (by unfold LvFr; omega), cnt]
  have t36 : c₂.nreg 4936 = RECb := by rw [f₂ _ (by unfold LvFr; omega), recb]
  have hR₂ : LvRegs c₂ n b Hs.length A W₀ := hR₁.of_frame LF
  have mk : ∀ a, LvKept n b off a → c₂.nmem a = c.nmem a := fun a ha => by rw [LK a ha, gm₁]
  have recs₂ : RecOK c₂.nmem RECb IX0 off n e rs := recs.congr le_rfl
    (fun a h1 h2 => mk a (by unfold LvKept; omega)) (fun a h1 h2 => mk a (by unfold LvKept; omega))
  have mem₂ : ∀ a, SlKept n b RECb IX0 L a → c₂.nmem a = c₀.nmem a := fun a ha => by
    rw [mk a (by unfold SlKept at ha; unfold LvKept; omega), mem a ha]
  have hlay : ∀ a, ((b + n ≤ a ∧ a < b + 3 * n) ∨ (b + 6 * n ≤ a ∧ a < b + 7 * n)) →
      c₂.nmem a = c₁.nmem a := fun a ha => LK a (by unfold LvKept; omega)
  by_cases hk1 : c₂.nreg 4900 = 1
  · -- a prune: push the record
    obtain ⟨K, a₀, ha₀, h02, hstep, hNF, hEX, hpos, hIX, himg⟩ := LO.one hk1
    have hcn := LC hk1
    obtain ⟨haK, hKN⟩ := scStep_scChoiceE_rec hstep
    have hdep := scDepth_step hstep
    dsimp only at hdep haK hKN hNF hEX himg hstep
    have hℓ1 : ℓ + 1 ≤ L := by omega
    have hℓn1 : ℓ * n + n ≤ L * n := by
      have := Nat.mul_le_mul_right n hℓ1; rw [Nat.succ_mul] at this; exact this
    have hnlt0 : ¬ c₂.nreg 4900 < c₂.nreg 4931 := by rw [hk1, t31]; omega
    have hnlt1 : ¬ c₂.nreg 4931 < c₂.nreg 4900 := by rw [hk1, t31]; omega
    obtain ⟨c₃, k₃, e₃, hk₃, P32, P33, P0, P1, P2, Pm, Pn, Pr, Prm, Po⟩ :=
      slPush_exec (P := P) c₂ hw₂ t33 t36 t31 t32 rfl h02 (by omega) (by omega) (by omega)
    have Pm' : ∀ a, a < RECb → c₃.nmem a = c₂.nmem a := fun a ha => Pm a (by omega) (by omega)
      (by omega)
    have hInK : LvIn M c₃.nmem n b e B K Hs (exP N K ex (e a₀)) :=
      hIn₁.of_cells hKN (fun a ha => by rw [Pm' a (by omega), hlay a ha])
        (fun i hi => by rw [Pm' _ (by omega)]; exact hNF i hi)
        (fun i hi => by rw [Pm' _ (by omega)]; exact hEX i hi)
    have hTK : ∑ j ∈ range n, (1 + c₃.nmem (b + 3 * n + j)) ≤ (ℓ + 1 + 1) * T₀ := by
      rw [sum_congr rfl fun j hj => by rw [Pm' _ (by have := mem_range.1 hj; omega),
        hEX j (mem_range.1 hj)], sum_range_exP hIn.inj ha₀,
        sum_congr rfl fun j hj => by rw [← hIn.ex j (mem_range.1 hj)]]
      have h1 : ∑ d ∈ N \ K, (1 + ex d) ≤ ∑ d ∈ N, (1 + ex d) :=
        sum_le_sum_of_subset sdiff_subset
      rw [add_mul, one_mul]
      omega
    have hSK : ∑ d ∈ K, (1 + exP N K ex (e a₀) d) ≤ T₀ := by rw [sum_exP haK hKN]; exact hSb
    refine ⟨(ℓ + 1, (K, ret τ K, exP N K ex (e a₀)), (N, K, e a₀) :: rs), c₃,
      k₁ + (k₂ + (k₃ + 2 + 2)), .seq e₁ (.seq e₂ (.ifLtN_false hnlt0 (.ifLtN_false hnlt1 e₃))),
      ⟨e₃.wb_right, hR₂.of_frame' fun x hx hlt => Pn x (by omega) (by omega) (by omega),
        by rw [Pn _ (by omega) (by omega) (by omega), t31],
        by rw [Pn _ (by omega) (by omega) (by omega), t36], P33,
        scIter_snoc (scChoiceE M sepF e n Hs A W₀) Hs ℓ s₀ (N, τ, ex) _ rs _ iter hstep, by dsimp only; omega,
        by rw [P32]; omega, by rw [P32, Nat.succ_mul]; omega,
        by
          rw [P32]
          exact recs₂.push len (by omega) o1 P0 P1 P2 Pm ha₀ hpos hcn hIX rfl himg
            (fun k hk => by omega),
        by simp [len],
        fun a ha => by
          rw [Pm a (by unfold SlKept at ha; omega) (by unfold SlKept at ha; omega)
            (by unfold SlKept at ha; omega), mem₂ a ha],
        fun r hr => by
          obtain ⟨h1, h2⟩ := hr
          rw [Pn r (by omega) (by omega) (by omega), f₂ r h1, reg r ⟨h1, h2⟩],
        by rw [Pr, Lr, gr₁, rr], by rw [Prm, Lrm, grm₁, rm], by rw [Po, Lo, go₁, out],
        Or.inl ⟨by rw [Pn _ (by omega) (by omega) (by omega), t30], hInK, hTK, hSK⟩⟩, ?_⟩
    simp only [slPot, Pn 4930 (by omega) (by omega) (by omega), t30, d0]
    have e1 : L + 1 - ℓ = (L + 1 - (ℓ + 1)) + 1 := by omega
    rw [e1, add_mul, one_mul]
    simp only [hBk, slBk] at hk₂ ⊢
    omega
  · -- stop
    obtain ⟨hst, hNF, hEX⟩ := LO.ne_one hk1
    obtain ⟨c₃, k₃, e₃, hk₃, D30, Dn, Dm, Dr, Drm, Do⟩ := slDone_exec (P := P) c₂ hw₂ (by omega)
    have hif : ∃ k, Exec P W (.ifLtN 4900 4931 slDone (.ifLtN 4931 4900 slDone slPush)) c₂ c₃ k ∧
        k ≤ 4 := by
      by_cases h0 : c₂.nreg 4900 < c₂.nreg 4931
      · exact ⟨k₃ + 1, .ifLtN_true h0 e₃, by omega⟩
      · have h1 : c₂.nreg 4931 < c₂.nreg 4900 := by rw [t31] at h0 ⊢; omega
        exact ⟨k₃ + 1 + 2, .ifLtN_false h0 (.ifLtN_true h1 e₃), by omega⟩
    obtain ⟨k₃', e₃', hk₃'⟩ := hif
    have hIn₃ : LvIn M c₃.nmem n b e B N Hs ex :=
      hIn₁.of_cells subset_rfl (fun a ha => by rw [Dm, hlay a ha])
        (fun i hi => by rw [Dm, hNF i hi]; exact hIn₁.nf i hi)
        (fun i hi => by rw [Dm, hEX i hi]; exact hIn₁.ex i hi)
    have hLO₃ : LvOut M (scChoiceE M sepF e n Hs A W₀) Hs (N, τ, ex) c₃.nmem c₃ n b (c₃.nreg 4932) e := by
      rw [Dn _ (by omega), t32]
      exact (LO.congr (m₀' := c₃.nmem) (fun i hi => by rw [Dm, hNF i hi])
        (fun i hi => by rw [Dm, hEX i hi])).congrC Dm (Dn _ (by omega)) (Dn _ (by omega))
        (Dn _ (by omega)) (Dn _ (by omega))
    refine ⟨(ℓ, (N, τ, ex), rs), c₃, k₁ + (k₂ + k₃'), .seq e₁ (.seq e₂ e₃'),
      ⟨e₃.wb_right, hR₂.of_frame' fun x hx hlt => Dn x (by omega),
        by rw [Dn _ (by omega), t31], by rw [Dn _ (by omega), t36],
        by rw [Dn _ (by omega), t33], iter, dep,
        by rw [Dn _ (by omega), t32]; exact o1, by rw [Dn _ (by omega), t32]; exact o2,
        by rw [Dm, Dn _ (by omega), t32]; exact recs₂, len,
        fun a ha => by rw [Dm, mem₂ a ha],
        fun r hr => by
          obtain ⟨h1, h2⟩ := hr
          rw [Dn r (by omega), f₂ r h1, reg r ⟨h1, h2⟩],
        by rw [Dr, Lr, gr₁, rr], by rw [Drm, Lrm, grm₁, rm], by rw [Do, Lo, go₁, out],
        Or.inr ⟨D30, by rw [Dn _ (by omega)]; exact hk1, hIn₃, hLO₃, fun h i hi => by
          rw [Dm]; exact LC2 (by rw [Dn _ (by omega)] at h; exact h) i hi⟩⟩, ?_⟩
    simp only [slPot, D30, d0]
    simp only [hBk, slBk] at hk₂ hBk1 ⊢
    omega

open Classical in
/-- **The loop over the levels of `scertD` on the machine** (the choices `scChoiceE`, any
separator `sepF`, a bound `L ≥ scDepth`, e.g. `nTouch M N Hs ≤ 6` by `scDepth_le_nTouch`): within
`(L + 1) (|Hs| (160 n + 36) + 244 n + 110) + 6` steps the loop stops after `ℓ ≤ L` prunes at a
state `s` that is not a prune (`scStep … s = none`), with
`scertD … N τ ex = (scBase … s).map fun x => (x.1, applyPr Hs x.1 rs x.2)`; the outcome `LvOut`
of the final level (kind `0`: `NoCut` (Miller's case), `2`: the cut at a hole with its labels,
`3`: failure), the input `LvIn` of `s` and the records `rs` (`RecOK`, pruned indices between
`IX0` and `r4932 ≤ IX0 + ℓ n`) in memory; the kept memory `SlKept`, registers `SlFr`. -/
theorem slProg_exec (sepF : SepFn M) {e : ℕ → D} {B N : Finset D} {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) {τ : Perm D} {ex : D → ℕ} {n b A W₀ RECb IX0 L : ℕ}
    (c : Config) (hc : WordsBounded W c) (hR : LvRegs c n b Hs.length A W₀)
    (hI : LvIn M c.nmem n b e B N Hs ex) (r36 : c.nreg 4936 = RECb) (r37 : c.nreg 4937 = IX0)
    (hHW : Hs.length + 1 ≤ W)
    (hL : scDepth (scChoiceE M sepF e n Hs A W₀) Hs N τ ex ≤ L)
    (lay : b + 20 * n + 3 ≤ RECb ∧ RECb + 3 * L ≤ IX0 ∧ IX0 + L * n + n + 1 ≤ W)
    (hS : A + 2 * ((L + 1) * ∑ j ∈ range n, (1 + c.nmem (b + 3 * n + j))) ≤ W) :
    ∃ c' t, Exec P W slProg c c' t ∧
      t ≤ (L + 1) * (Hs.length * (160 * n + 36) + 244 * n + 110) + 6 ∧
      ∃ ℓ s rs, scIter (scChoiceE M sepF e n Hs A W₀) Hs ℓ (N, τ, ex) = some (s, rs) ∧
        scStep (scChoiceE M sepF e n Hs A W₀) Hs s = none ∧
        scertD (scChoiceE M sepF e n Hs A W₀) Hs N τ ex =
          (scBase (scChoiceE M sepF e n Hs A W₀) Hs s).map
            (fun x => (x.1, applyPr Hs x.1 rs x.2)) ∧
        ℓ ≤ L ∧ rs.length = ℓ ∧ c'.nreg 4933 = ℓ ∧ c'.nreg 4900 ≠ 1 ∧
        LvIn M c'.nmem n b e B s.1 Hs s.2.2 ∧
        LvOut M (scChoiceE M sepF e n Hs A W₀) Hs s c'.nmem c' n b (c'.nreg 4932) e ∧
        (c'.nreg 4900 = 2 → ∀ i < n, 0 < c'.nmem (b + 13 * n + 1 + i) ∧
          c'.nmem (b + 13 * n + 1 + i) ≤ n) ∧
        IX0 ≤ c'.nreg 4932 ∧ c'.nreg 4932 ≤ IX0 + ℓ * n ∧
        RecOK c'.nmem RECb IX0 (c'.nreg 4932) n e rs ∧
        LvRegs c' n b Hs.length A W₀ ∧ c'.nreg 4936 = RECb ∧ c'.nreg 4931 = 1 ∧
        (∀ a, SlKept n b RECb IX0 L a → c'.nmem a = c.nmem a) ∧
        (∀ r, SlFr r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, i30, i31, i32, i33, in₁, im₁, ir₁, irm₁, io₁⟩ :=
    slInit_exec (P := P) c hc r37 (by omega)
  set T₀ := ∑ j ∈ range n, (1 + c.nmem (b + 3 * n + j)) with hT₀
  have hI₁ : SlInv W M (scChoiceE M sepF e n Hs A W₀) Hs (N, τ, ex) c n b A W₀ RECb IX0 L T₀ e B
      (0, (N, τ, ex), []) c₁ :=
    ⟨e₁.wb_right, hR.of_frame' fun x hx hlt => in₁ x (by omega), i31,
      by rw [in₁ _ (by omega), r36], i33, rfl, by dsimp only; omega, by rw [i32],
      by rw [i32]; simp, RecOK.nil _ _ _ _ _ _, rfl, fun a _ => by rw [im₁],
      fun r hr => in₁ r (by obtain ⟨-, h⟩ := hr; omega), ir₁, irm₁, io₁,
      Or.inl ⟨i30, by rw [im₁]; exact hI, by rw [im₁]; simp only [zero_add, one_mul]; exact le_rfl,
        sum_le_range hI.inj (fun d hd => hI.surj d (hI.sub hd)) hI.nf hI.ex⟩⟩
  obtain ⟨x', c', k₂, e₂, hI', hnt, hk₂⟩ := whileLtN_ghost' (P := P) (W := W) (a := 4930)
    (b := 4931) (body := slBody)
    (fun x c' => SlInv W M (scChoiceE M sepF e n Hs A W₀) Hs (N, τ, ex) c n b A W₀ RECb IX0 L T₀
      e B x c') (fun x c' => slPot L (slBk Hs.length n) x c')
    (fun x c' h => h.wb) (fun x c' h ht => slBody_step sepF hd hHW lay hS x c' h ht) hI₁
  obtain ⟨ℓ, s, rs⟩ := x'
  obtain ⟨wb, hR', one, recb, cnt, iter, dep, o1, o2, recs, len, mem, reg, rr, rm, out, st⟩ := hI'
  dsimp only at cnt iter dep o2 recs len st
  rcases st with ⟨d0, -⟩ | ⟨d1, hk1, hIn, hLO, hLAB⟩
  · rw [d0, one] at hnt; omega
  have hst := (hLO.ne_one hk1).1
  have hk₂' : k₂ ≤ (L + 1) * slBk Hs.length n + 2 := by
    simp only [slPot, i30] at hk₂; simpa using hk₂
  refine ⟨c', k₁ + k₂, .seq e₁ e₂, by unfold slBk at hk₂'; omega, ℓ, s, rs, iter, hst,
    scertD_iter _ Hs iter hst, by omega, len, cnt, hk1, hIn, hLO, hLAB, o1, o2, recs, hR', recb, one,
    mem, reg, rr, rm, out⟩

end Loop

end BKMNW

end PlanarFlow
