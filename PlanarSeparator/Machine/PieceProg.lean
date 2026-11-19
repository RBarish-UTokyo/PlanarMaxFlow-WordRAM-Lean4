module

public import PlanarSeparator.Machine.PieceWords
public import PlanarSeparator.Machine.Front

/-!
# The program of a piece: labels, ranks, words

The passes of the program writing the input `sepInput` of the separator program for a piece
`C` (a list `L` of `k` vertices in increasing order in memory) from the global arrays of the
graph (offsets `ofs`, tails `tl`, reversals `rv`, rotation `ro` of the darts numbered by
`dartNum`, weights), stated for arbitrary numeric arrays (the link with `ltIn` is
`PlanarSeparator.Piece.ltIn_words`):

* `labA`, **`labA_exec`**: the label `j + 1` of the vertex `L[j]` at `aLab + L[j]`.
* `rankLoop`, **`rankLoop_exec`**: for every vertex `L[j]`, the number `cntB j` of marked darts
  (head labelled) of the earlier vertices at `bO + j` (the offsets of the piece), its weight at
  `bW + j`, and the rank `cntB j + cntI … g + 1` at `aRk + g` of every marked dart `g` of it
  (`rankInner_exec` for one vertex); the number of marked darts and the total weight in
  registers.
* `frLoop_exec`: the first return of the rotation to the darts of positive rank.
* `dartLoop`, **`dartLoop_exec`**: for every marked dart `g` of a vertex `L[j]`, the words `j`,
  `rk[rv g] - 1`, `rk[fr g] - 1` at the slot `bD + 3 (rk[g] - 1)` (`dartInner_exec` for one
  vertex).

Registers (all `≥ 1000`, so that the separator program can be called afterwards,
`PlanarSeparator.ltSubR_exec`): `1001` holds `1`; bases `1010` offsets, `1011` tails,
`1012` reversals, `1013` rotation, `1014` weights, `1015` the list, `1017` labels, `1018` ranks,
`1050` `bO`, `1051` `bW`, `1052` `bD`; `1016` the length `k`; `1030`–`1041` scratch (`1037` the
count, `1038` the total weight).
-/
@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The body of the label pass: `lab[L[j]] := j + 1; j := j + 1`. -/
def labBody : Stmt :=
  block [.addN 1034 1015 1030, .loadN 1031 1034, .addN 1034 1017 1031, .addN 1035 1030 1001,
    .storeN 1034 1035, .addN 1030 1030 1001]

/-- **The label pass.** -/
def labA : Stmt := .seq (.instr (.constN 1030 0)) (.whileLtN 1030 1016 labBody)

variable {P : Input} {W : ℕ}

/-- **The label pass**: `lab[L[j]] = j + 1` for `j < k`, the other cells kept. -/
theorem labA_exec {c : Config} (hc : WordsBounded W c) {k : ℕ} (Lv : ℕ → ℕ)
    (h1 : c.nreg 1001 = 1) (hk : c.nreg 1016 = k)
    (hL : ∀ j < k, c.nmem (c.nreg 1015 + j) = Lv j)
    (hinj : ∀ i < k, ∀ j < k, Lv i = Lv j → i = j)
    (hdis : ∀ i < k, ∀ j < k, c.nreg 1017 + Lv i ≠ c.nreg 1015 + j)
    (hW : k + 1 ≤ W) (hWL : c.nreg 1015 + k ≤ W) (hWl : ∀ j < k, c.nreg 1017 + Lv j ≤ W) :
    ∃ c' k', Exec P W labA c c' k' ∧ k' ≤ 8 * k + 3 ∧
      (∀ j < k, c'.nmem (c.nreg 1017 + Lv j) = j + 1) ∧
      (∀ a, (∀ j < k, a ≠ c.nreg 1017 + Lv j) → c'.nmem a = c.nmem a) := by
  set aL := c.nreg 1015
  set aLab := c.nreg 1017
  let I : ℕ → Config → Prop := fun j d => WordsBounded W d ∧ d.nreg 1030 = j ∧
    d.nreg 1016 = k ∧ d.nreg 1001 = 1 ∧ d.nreg 1015 = aL ∧ d.nreg 1017 = aLab ∧
    (∀ j' < j, d.nmem (aLab + Lv j') = j' + 1) ∧
    (∀ a, (∀ j' < j, a ≠ aLab + Lv j') → d.nmem a = c.nmem a)
  have e₀ := Exec.constN (P := P) hc 1030 0 (Nat.zero_le _)
  obtain ⟨c', k', e', hI', hk'⟩ := Exec.forN (P := P) (W := W) (ri := 1030) (rN := 1016) (N := k)
    (lo := 0) (B := 6) (body := labBody) I (fun j d h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j d h hj => by
      obtain ⟨hw, h30, h16, h01, h15, h17, hA, hB⟩ := h
      have hv : d.nmem (d.nreg 1015 + d.nreg 1030) = Lv j := by
        rw [h15, h30, hB _ (fun j' _ => (hdis j' (by omega) j hj).symm)]; exact hL j hj
      unfold labBody
      exec_block
      · config_simp; rw [h15, h30]; omega
      · config_simp; rw [hv, h17]; exact hWl j hj
      · config_simp; rw [h30, h01]; omega
      · config_simp; rw [h30, h01]; omega
      · refine ⟨⟨‹WordsBounded _ _›, ?_⟩, by omega⟩
        config_simp
        rw [hv, h17, h30, h01]
        refine ⟨rfl, h16, rfl, h15, rfl, fun j' hj' => ?_, fun a ha => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
          · rw [upd_other _ _ _ (fun e => by
              have := hinj j' (by omega) j hj (by omega); omega)]
            exact hA j' hj'
          · rw [upd_same]
        · rw [upd_other _ _ _ (ha j (by omega))]
          exact hB a (fun j' hj' => ha j' (by omega)))
    (Nat.zero_le _)
    ⟨e₀.wb_right, by config_simp, by config_simp; exact hk, by config_simp; exact h1,
      by config_simp; rfl, by config_simp; rfl, fun j' hj' => by omega, fun a _ => rfl⟩
  exact ⟨c', 1 + k', .seq e₀ e', by omega, hI'.2.2.2.2.2.2.1, hI'.2.2.2.2.2.2.2⟩

/-! ### Ranks of the darts of one vertex -/

/-- The number of `g' ∈ [lo, g)` with `q g'`. -/
def cntI (q : ℕ → Prop) [DecidablePred q] (lo g : ℕ) : ℕ := ((Finset.Ico lo g).filter q).card

theorem cntI_succ (q : ℕ → Prop) [DecidablePred q] {lo g : ℕ} (h : lo ≤ g) :
    cntI q lo (g + 1) = cntI q lo g + if q g then 1 else 0 := by
  unfold cntI
  rw [← Nat.succ_eq_add_one, Nat.Ico_succ_right_eq_insert_Ico h, Finset.filter_insert]
  split_ifs with hq
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem cntI_self (q : ℕ → Prop) [DecidablePred q] (lo : ℕ) : cntI q lo lo = 0 := by
  simp [cntI]

theorem cntI_le (q : ℕ → Prop) [DecidablePred q] (lo g : ℕ) : cntI q lo g ≤ g - lo := by
  unfold cntI
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The body of the rank pass over the darts of a vertex: if the head of the dart `g` has a
label, `cnt := cnt + 1; rk[g] := cnt`; then `g := g + 1`. -/
def rankBody : Stmt :=
  .seq (block [.addN 1034 1012 1032, .loadN 1035 1034, .addN 1034 1011 1035, .loadN 1035 1034,
    .addN 1034 1017 1035, .loadN 1035 1034, .constN 1036 0])
  (.seq (.ifLtN 1036 1035 (block [.addN 1034 1018 1032, .addN 1037 1037 1001, .storeN 1034 1037])
    .skip) (.instr (.addN 1032 1032 1001)))

/-- **The ranks of the darts of a vertex**: the darts `g ∈ [ofs v, ofs (v + 1))` (register
`1032` to `1033`) whose head `tl (rv g)` has a nonzero label get the rank `cnt + 1` at `aRk + g`,
counted from the value `cnt₀` of `1037`. -/
theorem rankInner_exec {c : Config} (hc : WordsBounded W c) {M N lo hi cnt₀ : ℕ}
    (tlF rvF labF : ℕ → ℕ)
    (h1 : c.nreg 1001 = 1) (hg : c.nreg 1032 = lo) (hgE : c.nreg 1033 = hi)
    (hcnt : c.nreg 1037 = cnt₀) (hle : lo ≤ hi) (hM : hi ≤ M)
    (hrv : ∀ g < M, c.nmem (c.nreg 1012 + g) = rvF g ∧ rvF g < M)
    (htl : ∀ g < M, c.nmem (c.nreg 1011 + g) = tlF g ∧ tlF g < N)
    (hlab : ∀ x < N, c.nmem (c.nreg 1017 + x) = labF x)
    (c1 : c.nreg 1011 + M ≤ c.nreg 1012) (c2 : c.nreg 1012 + M ≤ c.nreg 1017)
    (c3 : c.nreg 1017 + N ≤ c.nreg 1018) (c4 : c.nreg 1018 + M ≤ W)
    (hW : cnt₀ + (hi - lo) + 1 ≤ W) :
    ∃ c' k', Exec P W (.whileLtN 1032 1033 rankBody) c c' k' ∧ k' ≤ 14 * (hi - lo) + 2 ∧
      c'.nreg 1037 = cnt₀ + cntI (fun g => 0 < labF (tlF (rvF g))) lo hi ∧
      (∀ g, lo ≤ g → g < hi → 0 < labF (tlF (rvF g)) →
        c'.nmem (c.nreg 1018 + g) = cnt₀ + cntI (fun g => 0 < labF (tlF (rvF g))) lo g + 1) ∧
      (∀ a, (∀ g, lo ≤ g → g < hi → 0 < labF (tlF (rvF g)) → a ≠ c.nreg 1018 + g) →
        c'.nmem a = c.nmem a) := by
  set q : ℕ → Prop := fun g => 0 < labF (tlF (rvF g)) with hq
  set aTl := c.nreg 1011
  set aRv := c.nreg 1012
  set aLab := c.nreg 1017
  set aRk := c.nreg 1018
  let I : ℕ → Config → Prop := fun g d => WordsBounded W d ∧ d.nreg 1032 = g ∧
    d.nreg 1033 = hi ∧ d.nreg 1001 = 1 ∧ d.nreg 1011 = aTl ∧ d.nreg 1012 = aRv ∧
    d.nreg 1017 = aLab ∧ d.nreg 1018 = aRk ∧ d.nreg 1037 = cnt₀ + cntI q lo g ∧ lo ≤ g ∧
    (∀ g', lo ≤ g' → g' < g → q g' → d.nmem (aRk + g') = cnt₀ + cntI q lo g' + 1) ∧
    (∀ a, (∀ g', lo ≤ g' → g' < g → q g' → a ≠ aRk + g') → d.nmem a = c.nmem a)
  obtain ⟨c', k', e', hI', hk'⟩ := Exec.forN (P := P) (W := W) (ri := 1032) (rN := 1033) (N := hi)
    (lo := lo) (B := 12) (body := rankBody) I (fun g d h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun g d h hgi => by
      obtain ⟨hw, h32, h33, h01, h11, h12, h17, h18, h37, hglo, hA, hB⟩ := h
      have hgM : g < M := by omega
      obtain ⟨hrv1, hrv2⟩ := hrv g hgM
      obtain ⟨htl1, htl2⟩ := htl (rvF g) hrv2
      have hcI := cntI_le q lo g
      have r1 : d.nmem (d.nreg 1012 + d.nreg 1032) = rvF g := by
        rw [h12, h32, hB _ (fun g' _ _ _ => by omega)]; exact hrv1
      have r2 : d.nmem (d.nreg 1011 + rvF g) = tlF (rvF g) := by
        rw [h11, hB _ (fun g' _ _ _ => by omega)]; exact htl1
      have r3 : d.nmem (d.nreg 1017 + tlF (rvF g)) = labF (tlF (rvF g)) := by
        rw [h17, hB _ (fun g' _ _ _ => by omega)]; exact hlab _ htl2
      obtain ⟨d₁, k₁, e₁, hw₁, h35, h36, hm₁, hr₁, hk₁⟩ : ∃ d₁ k₁, Exec P W
          (block [.addN 1034 1012 1032, .loadN 1035 1034, .addN 1034 1011 1035, .loadN 1035 1034,
            .addN 1034 1017 1035, .loadN 1035 1034, .constN 1036 0]) d d₁ k₁ ∧
          WordsBounded W d₁ ∧ d₁.nreg 1035 = labF (tlF (rvF g)) ∧ d₁.nreg 1036 = 0 ∧
          d₁.nmem = d.nmem ∧ (∀ r, r ≠ 1034 → r ≠ 1035 → r ≠ 1036 → d₁.nreg r = d.nreg r) ∧
          k₁ = 7 := by
        exec_block
        · config_simp; rw [h12, h32]; omega
        · config_simp; rw [r1, h11]; omega
        · config_simp; rw [r1, r2, h17]; omega
        · omega
        refine ⟨‹WordsBounded _ _›, ?_, by config_simp, rfl, fun r ha hb hc => ?_, rfl⟩
        · config_simp; rw [r1, r2, r3]
        · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl
      have g32 : d₁.nreg 1032 = g := by rw [hr₁ _ (by omega) (by omega) (by omega), h32]
      have g33 : d₁.nreg 1033 = hi := by rw [hr₁ _ (by omega) (by omega) (by omega), h33]
      have g01 : d₁.nreg 1001 = 1 := by rw [hr₁ _ (by omega) (by omega) (by omega), h01]
      have g11 : d₁.nreg 1011 = aTl := by rw [hr₁ _ (by omega) (by omega) (by omega), h11]
      have g12 : d₁.nreg 1012 = aRv := by rw [hr₁ _ (by omega) (by omega) (by omega), h12]
      have g17 : d₁.nreg 1017 = aLab := by rw [hr₁ _ (by omega) (by omega) (by omega), h17]
      have g18 : d₁.nreg 1018 = aRk := by rw [hr₁ _ (by omega) (by omega) (by omega), h18]
      have g37 : d₁.nreg 1037 = cnt₀ + cntI q lo g := by
        rw [hr₁ _ (by omega) (by omega) (by omega), h37]
      clear h32 h33 h01 h11 h12 h17 h18 h37 r1 r2 r3
      unfold rankBody
      refine spec_seq ⟨d₁, k₁, e₁, ?_⟩
      rw [hk₁]
      rw [← hm₁] at hA hB
      clear hm₁ hr₁ e₁ hk₁ hw
      by_cases hqg : q g
      · refine spec_seq (spec_ifLtN_true (by rw [h36, h35]; exact hqg) ?_)
        exec_block
        · config_simp; rw [g18, g32]; omega
        · config_simp; rw [g37, g01]; omega
        refine spec_instr (Exec.addN ‹WordsBounded _ _› 1032 1032 1001 (by
          config_simp; rw [g32, g01]; omega)) (fun hw' => ?_)
        refine ⟨⟨hw', ?_⟩, by omega⟩
        config_simp
        rw [g32, g01, g18, g37, g33, g11, g12, g17]
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, by omega, fun g' hg1 hg2 hq' => ?_,
          fun a ha => ?_⟩
        · rw [cntI_succ q hglo]; simp only [hqg, ↓reduceIte]; omega
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hg2 with hg2 | rfl
          · rw [upd_other _ _ _ (by omega)]; exact hA g' hg1 hg2 hq'
          · rw [upd_same]
        · rw [upd_other _ _ _ (ha g hglo (by omega) hqg)]
          exact hB a (fun g' h1 h2 h3 => ha g' h1 (by omega) h3)
      · refine spec_seq (spec_ifLtN_false (by rw [h36, h35]; exact hqg) ?_)
        refine spec_skip ‹WordsBounded _ _› ?_
        refine spec_instr (Exec.addN ‹WordsBounded _ _› 1032 1032 1001 (by
          config_simp; rw [g32, g01]; omega)) (fun hw' => ?_)
        refine ⟨⟨hw', ?_⟩, by omega⟩
        config_simp
        rw [g32, g01, g18, g37, g33, g11, g12, g17]
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, by omega, fun g' hg1 hg2 hq' => ?_,
          fun a ha => ?_⟩
        · rw [cntI_succ q hglo]; simp only [hqg, ↓reduceIte]; omega
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hg2 with hg2 | rfl
          · exact hA g' hg1 hg2 hq'
          · exact absurd hq' hqg
        · exact hB a (fun g' h1 h2 h3 => ha g' h1 (by omega) h3))
    hle ⟨hc, hg, hgE, h1, rfl, rfl, rfl, rfl, by rw [hcnt, cntI_self]; rfl, le_rfl,
      fun g' h1 h2 _ => by omega, fun a _ => rfl⟩
  exact ⟨c', k', e', hk', hI'.2.2.2.2.2.2.2.2.1, hI'.2.2.2.2.2.2.2.2.2.2.1,
    hI'.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ### The rank pass -/

/-- The sum of the numbers of darts of the first `j` vertices of the list. -/
def psum (ofsF Lv : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ j' ∈ Finset.range j, (ofsF (Lv j' + 1) - ofsF (Lv j'))

/-- The number of marked darts of the first `j` vertices of the list. -/
def cntB (q : ℕ → Prop) [DecidablePred q] (ofsF Lv : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ j' ∈ Finset.range j, cntI q (ofsF (Lv j')) (ofsF (Lv j' + 1))

/-- The sum of the weights of the first `j` vertices of the list. -/
def wsum (wF Lv : ℕ → ℕ) (j : ℕ) : ℕ := ∑ j' ∈ Finset.range j, wF (Lv j')

theorem psum_le {ofsF Lv : ℕ → ℕ} {N k : ℕ}
    (hmono : ∀ v v', v ≤ v' → v' ≤ N → ofsF v ≤ ofsF v')
    (hLN : ∀ j < k, Lv j < N) (hinc : ∀ i j, i < j → j < k → Lv i < Lv j) :
    ∀ j, 0 < j → j ≤ k → psum ofsF Lv j ≤ ofsF (Lv (j - 1) + 1) := by
  intro j hj hjk
  induction j with
  | zero => omega
  | succ j ih =>
    unfold psum at ih ⊢
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · have h1 := ih hj0 (by omega)
      have h2 := hinc (j - 1) j (by omega) (by omega)
      have h3 := hmono (Lv (j - 1) + 1) (Lv j) (by omega) (by have := hLN j (by omega); omega)
      have h4 := hmono (Lv j) (Lv j + 1) (by omega) (by have := hLN j (by omega); omega)
      simp only [Nat.add_sub_cancel]
      omega

theorem psum_mono (ofsF Lv : ℕ → ℕ) {j j' : ℕ} (h : j ≤ j') :
    psum ofsF Lv j ≤ psum ofsF Lv j' :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 h)

theorem cntB_le_psum (q : ℕ → Prop) [DecidablePred q] (ofsF Lv : ℕ → ℕ) (j : ℕ) :
    cntB q ofsF Lv j ≤ psum ofsF Lv j :=
  Finset.sum_le_sum fun j' _ => cntI_le q _ _

/-- The body of the rank pass: for the vertex `v = L[j]`, the offset `cnt` at `bO + j`, its
weight at `bW + j` (added to `sw`), and the ranks of its darts. -/
def rankOBody : Stmt :=
  .seq (block [.addN 1034 1015 1030, .loadN 1031 1034, .addN 1034 1050 1030, .storeN 1034 1037,
    .addN 1034 1014 1031, .loadN 1036 1034, .addN 1034 1051 1030, .storeN 1034 1036,
    .addN 1038 1038 1036, .addN 1034 1010 1031, .loadN 1032 1034, .addN 1034 1034 1001,
    .loadN 1033 1034])
  (.seq (.whileLtN 1032 1033 rankBody) (.instr (.addN 1030 1030 1001)))

/-- **The rank pass** (loop over the list). -/
def rankLoop : Stmt :=
  .seq (block [.constN 1030 0, .constN 1037 0, .constN 1038 0]) (.whileLtN 1030 1016 rankOBody)

/-- **The rank pass**: for every vertex `v = L[j]` of the list, the number `cntB j` of marked
darts (head labelled) of the earlier vertices at `bO + j`, the weight of `v` at `bW + j`, and the
rank `cntB j + cntI … g + 1` at `aRk + g` of every marked dart `g` of `v`; in `1037` the number
of marked darts, in `1038` the total weight. -/
theorem rankLoop_exec {c : Config} (hc : WordsBounded W c) {N M k : ℕ}
    (Lv ofsF tlF rvF wF labF : ℕ → ℕ)
    (h1 : c.nreg 1001 = 1) (hk : c.nreg 1016 = k)
    (hL : ∀ j < k, c.nmem (c.nreg 1015 + j) = Lv j) (hLN : ∀ j < k, Lv j < N)
    (hinc : ∀ i j, i < j → j < k → Lv i < Lv j)
    (hofs : ∀ v ≤ N, c.nmem (c.nreg 1010 + v) = ofsF v)
    (hmono : ∀ v v', v ≤ v' → v' ≤ N → ofsF v ≤ ofsF v') (hofsM : ofsF N ≤ M)
    (hwt : ∀ v < N, c.nmem (c.nreg 1014 + v) = wF v)
    (hrv : ∀ g < M, c.nmem (c.nreg 1012 + g) = rvF g ∧ rvF g < M)
    (htl : ∀ g < M, c.nmem (c.nreg 1011 + g) = tlF g ∧ tlF g < N)
    (hlab : ∀ x < N, c.nmem (c.nreg 1017 + x) = labF x)
    (cO : c.nreg 1050 + k < c.nreg 1051) (cW : c.nreg 1051 + k ≤ c.nreg 1010)
    (c0 : c.nreg 1010 + N < c.nreg 1011) (c1 : c.nreg 1011 + M ≤ c.nreg 1012)
    (c2 : c.nreg 1012 + M ≤ c.nreg 1014) (c5 : c.nreg 1014 + N ≤ c.nreg 1015)
    (c6 : c.nreg 1015 + k ≤ c.nreg 1017) (c3 : c.nreg 1017 + N ≤ c.nreg 1018)
    (c4 : c.nreg 1018 + M ≤ W) (hsw : wsum wF Lv k ≤ W) :
    ∃ c' k', Exec P W rankLoop c c' k' ∧ k' ≤ 32 * k + 14 * psum ofsF Lv k + 5 ∧
      c'.nreg 1037 = cntB (fun g => 0 < labF (tlF (rvF g))) ofsF Lv k ∧
      c'.nreg 1038 = wsum wF Lv k ∧
      (∀ j < k, c'.nmem (c.nreg 1050 + j) = cntB (fun g => 0 < labF (tlF (rvF g))) ofsF Lv j) ∧
      (∀ j < k, c'.nmem (c.nreg 1051 + j) = wF (Lv j)) ∧
      (∀ j < k, ∀ g, ofsF (Lv j) ≤ g → g < ofsF (Lv j + 1) → 0 < labF (tlF (rvF g)) →
        c'.nmem (c.nreg 1018 + g) = cntB (fun g => 0 < labF (tlF (rvF g))) ofsF Lv j +
          cntI (fun g => 0 < labF (tlF (rvF g))) (ofsF (Lv j)) g + 1) ∧
      (∀ a, (∀ j < k, a ≠ c.nreg 1050 + j ∧ a ≠ c.nreg 1051 + j ∧ ∀ g, ofsF (Lv j) ≤ g →
        g < ofsF (Lv j + 1) → 0 < labF (tlF (rvF g)) → a ≠ c.nreg 1018 + g) →
        c'.nmem a = c.nmem a) := by
  set q : ℕ → Prop := fun g => 0 < labF (tlF (rvF g)) with hq
  set aOfs := c.nreg 1010
  set aTl := c.nreg 1011
  set aRv := c.nreg 1012
  set aW := c.nreg 1014
  set aL := c.nreg 1015
  set aLab := c.nreg 1017
  set aRk := c.nreg 1018
  set bO := c.nreg 1050
  set bW := c.nreg 1051
  have hps : ∀ j ≤ k, psum ofsF Lv j ≤ M := fun j hj => by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [psum]
    · have := psum_le hmono hLN hinc j hj0 hj
      have := hmono (Lv (j - 1) + 1) N (by have := hLN (j - 1) (by omega); omega) le_rfl
      omega
  -- the frame of the cells written by the first `j` iterations
  let Wr : ℕ → ℕ → Prop := fun j a => ∀ j' < j, a ≠ bO + j' ∧ a ≠ bW + j' ∧
    ∀ g, ofsF (Lv j') ≤ g → g < ofsF (Lv j' + 1) → q g → a ≠ aRk + g
  let Inv : ℕ → Config → Prop := fun j d => WordsBounded W d ∧ d.nreg 1030 = j ∧ j ≤ k ∧
    d.nreg 1016 = k ∧ d.nreg 1001 = 1 ∧ d.nreg 1010 = aOfs ∧ d.nreg 1011 = aTl ∧
    d.nreg 1012 = aRv ∧ d.nreg 1014 = aW ∧ d.nreg 1015 = aL ∧ d.nreg 1017 = aLab ∧
    d.nreg 1018 = aRk ∧ d.nreg 1050 = bO ∧ d.nreg 1051 = bW ∧
    d.nreg 1037 = cntB q ofsF Lv j ∧ d.nreg 1038 = wsum wF Lv j ∧
    (∀ j' < j, d.nmem (bO + j') = cntB q ofsF Lv j') ∧
    (∀ j' < j, d.nmem (bW + j') = wF (Lv j')) ∧
    (∀ j' < j, ∀ g, ofsF (Lv j') ≤ g → g < ofsF (Lv j' + 1) → q g →
      d.nmem (aRk + g) = cntB q ofsF Lv j' + cntI q (ofsF (Lv j')) g + 1) ∧
    (∀ a, Wr j a → d.nmem a = c.nmem a)
  -- reading the read-only arrays
  have rd : ∀ j ≤ k, ∀ a, (a < bO ∨ (bO + k < a ∧ a < bW) ∨ (bW + k ≤ a ∧ a < aRk)) →
      Wr j a := fun j hj a ha j' hj' => ⟨by omega, by omega, fun g h1 h2 h3 => by omega⟩
  obtain ⟨c₀, k₀, e₀, hI₀⟩ : ∃ c₀ k₀, Exec P W (block [.constN 1030 0, .constN 1037 0,
      .constN 1038 0]) c c₀ k₀ ∧ Inv 0 c₀ ∧ k₀ = 3 := by
    exec_block
    · omega
    · omega
    · omega
    refine ⟨⟨‹WordsBounded _ _›, by config_simp, by omega, by config_simp; exact hk,
      by config_simp; exact h1, by config_simp; rfl, by config_simp; rfl, by config_simp; rfl,
      by config_simp; rfl, by config_simp; rfl, by config_simp; rfl, by config_simp; rfl,
      by config_simp; rfl, by config_simp; rfl, by config_simp; simp [cntB],
      by config_simp; simp [wsum], fun j' h => by omega, fun j' h => by omega,
      fun j' h => by omega, fun a _ => rfl⟩, rfl⟩
  obtain ⟨c', k', e', ⟨j, hjk, hI'⟩, hn, hk'⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 1030) (b := 1016) (body := rankOBody) (fun d => ∃ j ≤ k, Inv j d)
    (fun d => 32 * (k - d.nreg 1030) + 14 * (psum ofsF Lv k - psum ofsF Lv (d.nreg 1030)))
    (fun d ⟨_, _, h⟩ => h.1)
    (fun d ⟨j, _, h⟩ hlt => by
      obtain ⟨hw, h30, hjk, h16, h01, h10, h11, h12, h14, h15, h17, h18, h50, h51, h37, h38,
        hO, hWt, hRk, hB⟩ := h
      rw [h30, h16] at hlt
      have hv := hLN j hlt
      have hpsj := hps (j + 1) hlt
      have hcB := cntB_le_psum q ofsF Lv j
      have hpsS : psum ofsF Lv (j + 1) = psum ofsF Lv j + (ofsF (Lv j + 1) - ofsF (Lv j)) := by
        simp [psum, Finset.sum_range_succ]
      have hwS : wsum wF Lv (j + 1) = wsum wF Lv j + wF (Lv j) := by
        simp [wsum, Finset.sum_range_succ]
      have hcS : cntB q ofsF Lv (j + 1) =
          cntB q ofsF Lv j + cntI q (ofsF (Lv j)) (ofsF (Lv j + 1)) := by
        simp [cntB, Finset.sum_range_succ]
      have hwsk : wsum wF Lv (j + 1) ≤ wsum wF Lv k := by
        unfold wsum
        exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
      have hmv := hmono (Lv j) (Lv j + 1) (by omega) (by omega)
      have r1 : d.nmem (aL + j) = Lv j := by
        rw [hB _ (rd j hjk _ (by right; right; omega))]; exact hL j hlt
      have r2 : d.nmem (aW + Lv j) = wF (Lv j) := by
        rw [hB _ (rd j hjk _ (by right; right; omega))]; exact hwt _ hv
      have r3 : d.nmem (aOfs + Lv j) = ofsF (Lv j) := by
        rw [hB _ (rd j hjk _ (by right; right; omega))]; exact hofs _ hv.le
      have r4 : d.nmem (aOfs + Lv j + 1) = ofsF (Lv j + 1) := by
        rw [hB _ (rd j hjk _ (by right; right; omega)), Nat.add_assoc]; exact hofs _ hv
      have n1 : aW + Lv j ≠ bO + j := by omega
      have n2 : aOfs + Lv j ≠ bO + j := by omega
      have n3 : aOfs + Lv j ≠ bW + j := by omega
      have n4 : aOfs + Lv j + 1 ≠ bO + j := by omega
      have n5 : aOfs + Lv j + 1 ≠ bW + j := by omega
      -- the block
      obtain ⟨d₁, k₁, e₁, hw₁, g31, g32, g33, g38, hm₁, hr₁, hk₁⟩ : ∃ d₁ k₁, Exec P W
          (block [.addN 1034 1015 1030, .loadN 1031 1034, .addN 1034 1050 1030,
            .storeN 1034 1037, .addN 1034 1014 1031, .loadN 1036 1034, .addN 1034 1051 1030,
            .storeN 1034 1036, .addN 1038 1038 1036, .addN 1034 1010 1031, .loadN 1032 1034,
            .addN 1034 1034 1001, .loadN 1033 1034]) d d₁ k₁ ∧ WordsBounded W d₁ ∧
          d₁.nreg 1031 = Lv j ∧ d₁.nreg 1032 = ofsF (Lv j) ∧ d₁.nreg 1033 = ofsF (Lv j + 1) ∧
          d₁.nreg 1038 = wsum wF Lv (j + 1) ∧
          d₁.nmem = upd (upd d.nmem (bO + j) (cntB q ofsF Lv j)) (bW + j)
            (wF (Lv j)) ∧
          (∀ r, r ≠ 1031 → r ≠ 1032 → r ≠ 1033 → r ≠ 1034 → r ≠ 1036 → r ≠ 1038 →
            d₁.nreg r = d.nreg r) ∧ k₁ = 13 := by
        exec_block
        rotate_right
        refine ⟨‹WordsBounded _ _›, ?_⟩
        all_goals config_simp
        all_goals simp only [h15, h30, h50, h51, h14, h10, h01, h37, h38, r1]
        · rw [upd_other _ _ _ n1, r2, upd_other _ _ _ n3, upd_other _ _ _ n2, r3,
            upd_other _ _ _ n5,
            upd_other _ _ _ n4, r4, hwS]
          refine ⟨trivial, rfl, rfl, rfl, rfl, fun r ha hb hc hd he hf => ?_⟩
          simp only [upd_apply]; split_ifs <;> first | omega | rfl
        · omega
        · omega
        · omega
        · omega
        · rw [upd_other _ _ _ n1, r2]; omega
        · omega
        · omega
      have hr₁' : ∀ r, 1037 ≤ r → r ≠ 1038 → d₁.nreg r = d.nreg r := fun r h h' =>
        hr₁ r (by omega) (by omega) (by omega) (by omega) (by omega) h'
      have hr₁'' : ∀ r, r ≤ 1030 → d₁.nreg r = d.nreg r := fun r h =>
        hr₁ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have m₁ : ∀ a, a ≠ bO + j → a ≠ bW + j → d₁.nmem a = d.nmem a := fun a h h' => by
        rw [hm₁, upd_other _ _ _ h', upd_other _ _ _ h]
      have hM' : ofsF (Lv j + 1) ≤ M := (hmono _ N (by omega) le_rfl).trans hofsM
      obtain ⟨d₂, k₂, e₂, hk₂, h37₂, hRk₂, hfr₂⟩ := rankInner_exec (P := P) hw₁ (N := N)
        (M := M) tlF rvF labF (by rw [hr₁'' _ (by omega), h01]) g32 g33
        (by rw [hr₁' _ le_rfl (by omega), h37]) hmv hM'
        (fun g hg => by
          rw [hr₁'' _ (by omega), h12, m₁ _ (by omega) (by omega),
            hB _ (rd j hjk _ (by right; right; omega))]; exact hrv g hg)
        (fun g hg => by
          rw [hr₁'' _ (by omega), h11, m₁ _ (by omega) (by omega),
            hB _ (rd j hjk _ (by right; right; omega))]; exact htl g hg)
        (fun x hx => by
          rw [hr₁'' _ (by omega), h17, m₁ _ (by omega) (by omega),
            hB _ (rd j hjk _ (by right; right; omega))]; exact hlab x hx)
        (by rw [hr₁'' _ (by omega), hr₁'' _ (by omega), h11, h12]; omega)
        (by rw [hr₁'' _ (by omega), hr₁'' _ (by omega), h12, h17]; omega)
        (by rw [hr₁'' 1017 (by omega), hr₁'' 1018 (by omega), h17, h18]; omega)
        (by rw [hr₁'' 1018 (by omega), h18]; omega)
        (by omega)
      rw [hr₁'' 1018 (by omega), h18] at hRk₂ hfr₂
      have f₂ : ∀ r, rankBody.wr r = false → d₂.nreg r = d₁.nreg r := fun r hr =>
        Exec.nreg_of_wr e₂ (by simpa [Stmt.wr] using hr)
      have f30 : d₂.nreg 1030 = j := by
        rw [f₂ 1030 (by decide), hr₁'' _ le_rfl, h30]
      have f01 : d₂.nreg 1001 = 1 := by rw [f₂ 1001 (by decide), hr₁'' _ (by omega), h01]
      refine ⟨_, k₁ + (k₂ + 1), .seq e₁ (.seq e₂ (Exec.addN e₂.wb_right 1030 1030 1001
        (by rw [f30, f01]; omega))), ⟨j + 1, by omega, ?_⟩, ?_⟩
      · refine ⟨Exec.wb_right (Exec.addN (P := P) e₂.wb_right 1030 1030 1001
          (by rw [f30, f01]; omega)), ?_⟩
        config_simp
        rw [f30, f01]
        rw [f₂ 1016 (by decide), f₂ 1010 (by decide), f₂ 1011 (by decide), f₂ 1012 (by decide),
          f₂ 1014 (by decide), f₂ 1015 (by decide), f₂ 1017 (by decide), f₂ 1018 (by decide),
          f₂ 1050 (by decide), f₂ 1051 (by decide), f₂ 1038 (by decide)]
        rw [hr₁' 1050 (by omega) (by omega), hr₁' 1051 (by omega) (by omega),
          hr₁'' 1016 (by omega), hr₁'' 1010 (by omega), hr₁'' 1011 (by omega),
          hr₁'' 1012 (by omega), hr₁'' 1014 (by omega), hr₁'' 1015 (by omega),
          hr₁'' 1017 (by omega), hr₁'' 1018 (by omega), g38]
        refine ⟨by trivial, by omega, h16, rfl, h10, h11, h12, h14, h15, h17, h18, h50, h51,
          by rw [h37₂, hcS], rfl, fun j' hj' => ?_,
          fun j' hj' => ?_, fun j' hj' g hg1 hg2 hqg => ?_, fun a ha => ?_⟩
        · rw [hfr₂ _ (fun g _ _ _ => by omega)]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
          · rw [m₁ _ (by omega) (by omega)]; exact hO j' hj'
          · rw [hm₁, upd_other _ _ _ (by omega), upd_same]
        · rw [hfr₂ _ (fun g _ _ _ => by omega)]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
          · rw [m₁ _ (by omega) (by omega)]; exact hWt j' hj'
          · rw [hm₁, upd_same]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
          · have h3 := hinc j' j hj' hlt
            have h4 := hmono (Lv j' + 1) (Lv j) (by omega) (by omega)
            rw [hfr₂ _ (fun g' h5 _ _ => by omega), m₁ _ (by omega) (by omega)]
            exact hRk j' hj' g hg1 hg2 hqg
          · exact hRk₂ g hg1 hg2 hqg
        · have ha' := ha j (by omega)
          rw [hfr₂ _ (fun g h1 h2 h3 => ha'.2.2 g h1 h2 h3), m₁ _ ha'.1 ha'.2.1]
          exact hB a (fun j' hj' => ha j' (by omega))
      · simp only [upd_same, f30, f01]
        rw [hpsS]
        have hpk := psum_mono ofsF Lv (show j + 1 ≤ k by omega)
        have : ofsF (Lv j + 1) - ofsF (Lv j) ≤ psum ofsF Lv k - psum ofsF Lv j := by omega
        rw [h30]
        omega)
    ⟨0, Nat.zero_le _, hI₀.1⟩
  obtain ⟨hw', h30', -, h16', -, -, -, -, -, -, -, -, -, -, h37', h38', hO', hWt', hRk', hB'⟩ :=
    hI'
  rw [h30', h16'] at hn
  obtain rfl : j = k := by omega
  have hc₀30 : c₀.nreg 1030 = 0 := hI₀.1.2.1
  refine ⟨c', k₀ + k', .seq e₀ e', ?_, h37', h38', hO', hWt', hRk', hB'⟩
  rw [hc₀30, show psum ofsF Lv 0 = 0 by simp [psum]] at hk'
  have := hI₀.2
  omega

/-! ### The first return of the rotation -/

/-- The body of the first-return loop: `x := ro[x]; y := rk[x]`. -/
def frBody : Stmt :=
  block [.addN 1041 1013 1035, .loadN 1035 1041, .addN 1041 1018 1035, .loadN 1036 1041]

/-- **The first return**: from `x = ro^[i₀] g` (register `1035`) with `y = rk[x]` (register
`1036`), the loop `while y < 1 do x := ro[x]; y := rk[x]` stops at the first `n ≥ i₀` with
`rk[ro^[n] g] > 0`. -/
theorem frLoop_exec {c : Config} (hc : WordsBounded W c) {M n i₀ g : ℕ} (rkF roF : ℕ → ℕ)
    (h1 : c.nreg 1001 = 1) (hx : c.nreg 1035 = roF^[i₀] g) (hy : c.nreg 1036 = rkF (roF^[i₀] g))
    (hi₀n : i₀ ≤ n) (hn : 0 < rkF (roF^[n] g))
    (hmin : ∀ i, i₀ ≤ i → i < n → rkF (roF^[i] g) = 0) (hlt : ∀ i ≤ n, roF^[i] g < M)
    (hro : ∀ x < M, c.nmem (c.nreg 1013 + x) = roF x)
    (hrk : ∀ x < M, c.nmem (c.nreg 1018 + x) = rkF x)
    (cW : c.nreg 1013 + M ≤ W) (cW' : c.nreg 1018 + M ≤ W) :
    ∃ c' k', Exec P W (.whileLtN 1036 1001 frBody) c c' k' ∧ k' ≤ 6 * (n - i₀) + 2 ∧
      c'.nreg 1035 = roF^[n] g ∧ c'.nreg 1036 = rkF (roF^[n] g) ∧ c'.nmem = c.nmem ∧
      (∀ r, r ≠ 1035 → r ≠ 1036 → r ≠ 1041 → c'.nreg r = c.nreg r) := by
  let I : ℕ → Config → Prop := fun i d => i₀ ≤ i ∧ i ≤ n ∧ WordsBounded W d ∧
    d.nreg 1035 = roF^[i] g ∧ d.nreg 1036 = rkF (roF^[i] g) ∧ d.nmem = c.nmem ∧
    (∀ r, r ≠ 1035 → r ≠ 1036 → r ≠ 1041 → d.nreg r = c.nreg r)
  obtain ⟨i, c', k', e', ⟨hi1, hi2, -, h35, h36, hm, hr⟩, hn', hk'⟩ :=
    Exec.whileLtN_ghost (P := P) (W := W) (a := 1036) (b := 1001) (body := frBody) I
    (fun i _ => 6 * (n - i)) (fun _ _ h => h.2.2.1)
    (fun i d ⟨hi1, hi2, hw, h35, h36, hm, hr⟩ ht => by
      have h01 : d.nreg 1001 = 1 := by rw [hr _ (by omega) (by omega) (by omega), h1]
      rw [h01, h36] at ht
      have hin : i < n := by
        rcases Nat.lt_or_ge i n with h | h
        · exact h
        · obtain rfl : i = n := by omega
          omega
      have hiM := hlt i hin.le
      have hi1M := hlt (i + 1) hin
      have g13 : d.nreg 1013 = c.nreg 1013 := hr _ (by omega) (by omega) (by omega)
      have g18 : d.nreg 1018 = c.nreg 1018 := hr _ (by omega) (by omega) (by omega)
      have r1 : d.nmem (c.nreg 1013 + roF^[i] g) = roF^[i + 1] g := by
        rw [hm, hro _ hiM, Function.iterate_succ_apply']
      have r2 : d.nmem (c.nreg 1018 + roF^[i + 1] g) = rkF (roF^[i + 1] g) := by
        rw [hm, hrk _ hi1M]
      refine ⟨i + 1, ?_⟩
      unfold frBody
      exec_block
      rotate_right
      refine ⟨⟨by omega, hin, ‹WordsBounded _ _›, ?_⟩, by omega⟩
      all_goals config_simp
      all_goals simp only [g13, h35, r1, g18]
      · rw [r2]
        exact ⟨trivial, rfl, hm, fun r ha hb hc' => by
          simp only [upd_apply]; split_ifs <;> first | omega | exact hr r ha hb hc'⟩
      · omega
      · omega)
    ⟨le_rfl, hi₀n, hc, hx, hy, rfl, fun _ _ _ _ => rfl⟩
  have h01 : c'.nreg 1001 = 1 := by rw [hr _ (by omega) (by omega) (by omega), h1]
  rw [h01, h36] at hn'
  have hin : i = n := by
    by_contra hne
    have := hmin i hi1 (by omega)
    omega
  subst hin
  exact ⟨c', k', e', by omega, h35, h36, hm, hr⟩

/-! ### The words of the darts of one vertex -/

/-- The first part of the words of a marked dart `g` (rank `y = rk[g] > 0`, slot
`t = bD + 3 (y - 1)`): `mem[t] := j`, `mem[t + 1] := rk[rv g] - 1`, then `x := ro[g]`,
`y := rk[x]`. -/
def dartW1 : List Instr :=
  [.subN 1035 1036 1001, .addN 1034 1035 1035, .addN 1034 1034 1035, .addN 1034 1034 1052,
    .storeN 1034 1030, .addN 1041 1012 1032, .loadN 1035 1041, .addN 1041 1018 1035,
    .loadN 1035 1041, .subN 1035 1035 1001, .addN 1034 1034 1001, .storeN 1034 1035,
    .addN 1041 1013 1032, .loadN 1035 1041, .addN 1041 1018 1035, .loadN 1036 1041]

/-- The words of a marked dart: the tail, the reversal, the first return. -/
def dartWrite : Stmt :=
  .seq (block dartW1) (.seq (.whileLtN 1036 1001 frBody)
    (block [.subN 1036 1036 1001, .addN 1034 1034 1001, .storeN 1034 1036]))

/-- The body of the dart pass over the darts of a vertex. -/
def dartBody : Stmt :=
  .seq (block [.addN 1041 1018 1032, .loadN 1036 1041, .constN 1040 0])
    (.seq (.ifLtN 1040 1036 dartWrite .skip) (.instr (.addN 1032 1032 1001)))

/-- **The words of the darts of a vertex**: for every dart `g ∈ [lo, hi)` (registers `1032`,
`1033`) of rank `rk[g] > 0`, at the slot `bD + 3 (rk[g] - 1)` (`bD` in `1052`): the index `j`
of the vertex (register `1030`), `rk[rv g] - 1` and `rk[fr g] - 1`, `fr g` the first return
of the rotation to the darts of positive rank. -/
theorem dartInner_exec {c : Config} (hc : WordsBounded W c) {M m' Δ lo hi j : ℕ}
    (rkF rvF roF frF : ℕ → ℕ)
    (h1 : c.nreg 1001 = 1) (h30 : c.nreg 1030 = j) (hg : c.nreg 1032 = lo)
    (hgE : c.nreg 1033 = hi) (hle : lo ≤ hi) (hM : hi ≤ M)
    (hrk : ∀ x < M, c.nmem (c.nreg 1018 + x) = rkF x)
    (hro : ∀ x < M, c.nmem (c.nreg 1013 + x) = roF x)
    (hrv : ∀ g, lo ≤ g → g < hi → 0 < rkF g → c.nmem (c.nreg 1012 + g) = rvF g ∧ rvF g < M)
    (hm' : ∀ g, lo ≤ g → g < hi → rkF g ≤ m')
    (hfr : ∀ g, lo ≤ g → g < hi → 0 < rkF g → ∃ n, 0 < n ∧ n ≤ Δ ∧ 0 < rkF (roF^[n] g) ∧
      (∀ i, 0 < i → i < n → rkF (roF^[i] g) = 0) ∧ (∀ i ≤ n, roF^[i] g < M) ∧
      roF^[n] g = frF g)
    (hinj : ∀ g g', lo ≤ g → g < hi → lo ≤ g' → g' < hi → 0 < rkF g → rkF g = rkF g' → g = g')
    (cD : c.nreg 1052 + 3 * m' ≤ c.nreg 1012) (c1 : c.nreg 1012 + M ≤ c.nreg 1013)
    (c2 : c.nreg 1013 + M ≤ c.nreg 1018) (c3 : c.nreg 1018 + M ≤ W) :
    ∃ c' k', Exec P W (.whileLtN 1032 1033 dartBody) c c' k' ∧
      k' ≤ (6 * Δ + 22) * (hi - lo) + 2 ∧
      (∀ g, lo ≤ g → g < hi → 0 < rkF g →
        c'.nmem (c.nreg 1052 + 3 * (rkF g - 1)) = j ∧
        c'.nmem (c.nreg 1052 + 3 * (rkF g - 1) + 1) = rkF (rvF g) - 1 ∧
        c'.nmem (c.nreg 1052 + 3 * (rkF g - 1) + 2) = rkF (frF g) - 1) ∧
      (∀ a, (∀ g, lo ≤ g → g < hi → 0 < rkF g → a ≠ c.nreg 1052 + 3 * (rkF g - 1) ∧
        a ≠ c.nreg 1052 + 3 * (rkF g - 1) + 1 ∧ a ≠ c.nreg 1052 + 3 * (rkF g - 1) + 2) →
        c'.nmem a = c.nmem a) := by
  set aRv := c.nreg 1012
  set aRo := c.nreg 1013
  set aRk := c.nreg 1018
  set bD := c.nreg 1052
  let Cl : ℕ → ℕ → Prop := fun g a => ∀ g', lo ≤ g' → g' < g → 0 < rkF g' →
    a ≠ bD + 3 * (rkF g' - 1) ∧ a ≠ bD + 3 * (rkF g' - 1) + 1 ∧ a ≠ bD + 3 * (rkF g' - 1) + 2
  let I : ℕ → Config → Prop := fun g d => WordsBounded W d ∧ d.nreg 1032 = g ∧
    d.nreg 1033 = hi ∧ d.nreg 1001 = 1 ∧ d.nreg 1030 = j ∧ d.nreg 1012 = aRv ∧
    d.nreg 1013 = aRo ∧ d.nreg 1018 = aRk ∧ d.nreg 1052 = bD ∧ lo ≤ g ∧
    (∀ g', lo ≤ g' → g' < g → 0 < rkF g' →
      d.nmem (bD + 3 * (rkF g' - 1)) = j ∧
      d.nmem (bD + 3 * (rkF g' - 1) + 1) = rkF (rvF g') - 1 ∧
      d.nmem (bD + 3 * (rkF g' - 1) + 2) = rkF (frF g') - 1) ∧
    (∀ a, Cl g a → d.nmem a = c.nmem a)
  have arr : ∀ g ≤ hi, ∀ a, aRv ≤ a → Cl g a := fun g hg a ha g' h1 h2 hp => by
    have := hm' g' h1 (by omega); refine ⟨by omega, by omega, by omega⟩
  obtain ⟨c', k', e', hI', hk'⟩ := Exec.forN (P := P) (W := W) (ri := 1032) (rN := 1033) (N := hi)
    (lo := lo) (B := 6 * Δ + 20) (body := dartBody) I (fun g d h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun g d h hgi => by
      obtain ⟨hw, h32, h33, h01, h30', h12, h13, h18, h52, hglo, hA, hB⟩ := h
      have hgM : g < M := by omega
      have r0 : d.nmem (aRk + g) = rkF g := by rw [hB _ (arr g hgi.le _ (by omega))]; exact hrk g hgM
      obtain ⟨d₁, k₁, e₁, hw₁, g36, g40, hm₁, hr₁, hk₁⟩ : ∃ d₁ k₁, Exec P W
          (block [.addN 1041 1018 1032, .loadN 1036 1041, .constN 1040 0]) d d₁ k₁ ∧
          WordsBounded W d₁ ∧ d₁.nreg 1036 = rkF g ∧ d₁.nreg 1040 = 0 ∧ d₁.nmem = d.nmem ∧
          (∀ r, r ≠ 1036 → r ≠ 1040 → r ≠ 1041 → d₁.nreg r = d.nreg r) ∧ k₁ = 3 := by
        exec_block
        rotate_right
        refine ⟨‹WordsBounded _ _›, ?_⟩
        all_goals config_simp
        all_goals (try simp only [h18, h32])
        · refine ⟨r0, fun r ha hb hc' => ?_⟩
          simp only [upd_apply]; split_ifs <;> first | omega | rfl
        all_goals omega
      have q : ∀ r, r ≠ 1036 → r ≠ 1040 → r ≠ 1041 → r ≠ 1034 → r ≠ 1035 →
          d₁.nreg r = d.nreg r := fun r a b c' _ _ => hr₁ r a b c'
      unfold dartBody
      refine spec_seq ⟨d₁, k₁, e₁, ?_⟩
      rw [hk₁]
      have p01 : d₁.nreg 1001 = 1 := by rw [hr₁ _ (by omega) (by omega) (by omega), h01]
      have p12 : d₁.nreg 1012 = aRv := by rw [hr₁ _ (by omega) (by omega) (by omega), h12]
      have p13 : d₁.nreg 1013 = aRo := by rw [hr₁ _ (by omega) (by omega) (by omega), h13]
      have p18 : d₁.nreg 1018 = aRk := by rw [hr₁ _ (by omega) (by omega) (by omega), h18]
      have p30 : d₁.nreg 1030 = j := by rw [hr₁ _ (by omega) (by omega) (by omega), h30']
      have p32 : d₁.nreg 1032 = g := by rw [hr₁ _ (by omega) (by omega) (by omega), h32]
      have p33 : d₁.nreg 1033 = hi := by rw [hr₁ _ (by omega) (by omega) (by omega), h33]
      have p52 : d₁.nreg 1052 = bD := by rw [hr₁ _ (by omega) (by omega) (by omega), h52]
      by_cases hp : 0 < rkF g
      · obtain ⟨n, hn0, hnΔ, hnpos, hmin, hlt, hfrn⟩ := hfr g hglo hgi hp
        obtain ⟨hrv1, hrv2⟩ := hrv g hglo hgi hp
        have hm'g := hm' g hglo hgi
        have rd : ∀ a, aRv ≤ a → d.nmem a = c.nmem a := fun a ha => hB a (arr g hgi.le a ha)
        have hro1 : roF g < M := by have := hlt 1 hn0; simpa using this
        have e1 : d.nmem (aRv + g) = rvF g := by rw [rd _ (by omega)]; exact hrv1
        have e2 : d.nmem (aRk + rvF g) = rkF (rvF g) := by
          rw [rd _ (by omega)]; exact hrk _ hrv2
        have e3 : d.nmem (aRo + g) = roF g := by rw [rd _ (by omega)]; exact hro _ hgM
        have e4 : d.nmem (aRk + roF g) = rkF (roF g) := by
          rw [rd _ (by omega)]; exact hrk _ hro1
        have hs : rkF g - 1 + (rkF g - 1) + (rkF g - 1) + bD = bD + 3 * (rkF g - 1) := by omega
        have n1 : aRv + g ≠ bD + 3 * (rkF g - 1) := by omega
        have n2 : aRk + rvF g ≠ bD + 3 * (rkF g - 1) := by omega
        have n3 : aRo + g ≠ bD + 3 * (rkF g - 1) := by omega
        have n3' : aRo + g ≠ bD + 3 * (rkF g - 1) + 1 := by omega
        have n4 : aRk + roF g ≠ bD + 3 * (rkF g - 1) := by omega
        have n4' : aRk + roF g ≠ bD + 3 * (rkF g - 1) + 1 := by omega
        refine spec_seq (spec_ifLtN_true (by rw [g40, g36]; exact hp) ?_)
        obtain ⟨d₂, k₂, e₂, hw₂, f34, f35, f36, fm₂, fr₂, fk₂⟩ : ∃ d₂ k₂, Exec P W (block dartW1)
            d₁ d₂ k₂ ∧ WordsBounded W d₂ ∧ d₂.nreg 1034 = bD + 3 * (rkF g - 1) + 1 ∧
            d₂.nreg 1035 = roF g ∧ d₂.nreg 1036 = rkF (roF g) ∧
            d₂.nmem = upd (upd d.nmem (bD + 3 * (rkF g - 1)) j) (bD + 3 * (rkF g - 1) + 1)
              (rkF (rvF g) - 1) ∧
            (∀ r, r ≠ 1034 → r ≠ 1035 → r ≠ 1036 → r ≠ 1041 → d₂.nreg r = d₁.nreg r) ∧
            k₂ = 16 := by
          unfold dartW1
          exec_block
          rotate_right
          refine ⟨‹WordsBounded _ _›, ?_⟩
          all_goals config_simp
          all_goals (try simp only [g36, p52, p30, p12, p32, p18, p13, p01, hm₁, hs])
          · rw [upd_other _ _ _ n1, e1, upd_other _ _ _ n2, e2, upd_other _ _ _ n3',
              upd_other _ _ _ n3, e3, upd_other _ _ _ n4', upd_other _ _ _ n4, e4]
            refine ⟨by trivial, rfl, rfl, rfl, fun r ha hb hc' hd => ?_⟩
            simp only [upd_apply]; split_ifs <;> first | omega | rfl
          all_goals (try rw [upd_other _ _ _ n1, e1])
          all_goals (try rw [upd_other _ _ _ n3', upd_other _ _ _ n3, e3])
          all_goals omega
        have fr : ∀ r, r ≠ 1034 → r ≠ 1035 → r ≠ 1036 → r ≠ 1040 → r ≠ 1041 →
            d₂.nreg r = d.nreg r := fun r a b c' e f => by
          rw [fr₂ r a b c' f, hr₁ r c' e f]
        have rd₂ : ∀ a, aRv ≤ a → d₂.nmem a = c.nmem a := fun a ha => by
          rw [fm₂, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact rd a ha
        obtain ⟨d₃, k₃, e₃, hk₃, x35, x36, xm, xr⟩ := frLoop_exec (P := P) hw₂ (M := M) (n := n)
          (i₀ := 1) (g := g) rkF roF
          (by rw [fr _ (by omega) (by omega) (by omega) (by omega) (by omega), h01])
          (by rw [f35]; rfl) (by rw [f36]; rfl) hn0 hnpos (fun i hi1 hin => hmin i hi1 hin) hlt
          (fun x hx => by
            rw [fr _ (by omega) (by omega) (by omega) (by omega) (by omega), h13,
              rd₂ _ (by omega)]; exact hro x hx)
          (fun x hx => by
            rw [fr _ (by omega) (by omega) (by omega) (by omega) (by omega), h18,
              rd₂ _ (by omega)]; exact hrk x hx)
          (by rw [fr _ (by omega) (by omega) (by omega) (by omega) (by omega), h13]; omega)
          (by rw [fr _ (by omega) (by omega) (by omega) (by omega) (by omega), h18]; omega)
        rw [hfrn] at x35 x36
        have hw₃ := e₃.wb_right
        have y34 : d₃.nreg 1034 = bD + 3 * (rkF g - 1) + 1 := by
          rw [xr _ (by omega) (by omega) (by omega), f34]
        have y01 : d₃.nreg 1001 = 1 := by
          rw [xr _ (by omega) (by omega) (by omega),
            fr _ (by omega) (by omega) (by omega) (by omega) (by omega), h01]
        have yr : ∀ r, r ≠ 1034 → r ≠ 1035 → r ≠ 1036 → r ≠ 1040 → r ≠ 1041 →
            d₃.nreg r = d.nreg r := fun r a b c' e f => by
          rw [xr r b c' f, fr r a b c' e f]
        obtain ⟨d₄, k₄, e₄, hw₄, z34, zm, zr, zk⟩ : ∃ d₄ k₄, Exec P W
            (block [.subN 1036 1036 1001, .addN 1034 1034 1001, .storeN 1034 1036]) d₃ d₄ k₄ ∧
            WordsBounded W d₄ ∧ d₄.nreg 1034 = bD + 3 * (rkF g - 1) + 2 ∧
            d₄.nmem = upd d₃.nmem (bD + 3 * (rkF g - 1) + 2) (rkF (frF g) - 1) ∧
            (∀ r, r ≠ 1034 → r ≠ 1036 → d₄.nreg r = d₃.nreg r) ∧ k₄ = 3 := by
          exec_block
          rotate_right
          refine ⟨‹WordsBounded _ _›, ?_⟩
          all_goals config_simp
          all_goals (try simp only [y34, y01, x36])
          · refine ⟨trivial, trivial, fun r ha hb => ?_⟩
            simp only [upd_apply]; split_ifs <;> first | omega | rfl
          all_goals omega
        have w32 : d₄.nreg 1032 = g := by
          rw [zr _ (by omega) (by omega), yr _ (by omega) (by omega) (by omega) (by omega)
            (by omega), h32]
        have w01 : d₄.nreg 1001 = 1 := by rw [zr _ (by omega) (by omega), y01]
        have wr : ∀ r, r ≠ 1034 → r ≠ 1035 → r ≠ 1036 → r ≠ 1040 → r ≠ 1041 →
            d₄.nreg r = d.nreg r := fun r a b c' e f => by rw [zr r a c', yr r a b c' e f]
        refine ⟨d₄, k₂ + (k₃ + k₄), .seq e₂ (.seq e₃ e₄), ?_⟩
        refine spec_instr (Exec.addN hw₄ 1032 1032 1001 (by rw [w32, w01]; omega))
          (fun hw' => ?_)
        refine ⟨⟨hw', ?_⟩, by rw [fk₂, zk]; omega⟩
        config_simp
        rw [w32, w01]
        rw [wr 1033 (by omega) (by omega) (by omega) (by omega) (by omega),
          wr 1030 (by omega) (by omega) (by omega) (by omega) (by omega),
          wr 1012 (by omega) (by omega) (by omega) (by omega) (by omega),
          wr 1013 (by omega) (by omega) (by omega) (by omega) (by omega),
          wr 1018 (by omega) (by omega) (by omega) (by omega) (by omega),
          wr 1052 (by omega) (by omega) (by omega) (by omega) (by omega)]
        have hmem : ∀ a, d₄.nmem a = if a = bD + 3 * (rkF g - 1) + 2 then rkF (frF g) - 1
            else if a = bD + 3 * (rkF g - 1) + 1 then rkF (rvF g) - 1
            else if a = bD + 3 * (rkF g - 1) then j else d.nmem a := fun a => by
          rw [zm, xm, fm₂]; simp only [upd_apply]
        refine ⟨by trivial, h33, rfl, h30', h12, h13, h18, h52, by omega,
          fun g' hg1 hg2 hg3 => ?_, fun a ha => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hg2 with hg2 | rfl
          · have hne : rkF g' ≠ rkF g := fun e => by
              have := hinj g' g hg1 (by omega) hglo hgi hg3 e; omega
            have := hm' g' hg1 (by omega)
            rw [hmem, hmem, hmem]
            simp only [show ¬ bD + 3 * (rkF g' - 1) = bD + 3 * (rkF g - 1) + 2 by omega,
              show ¬ bD + 3 * (rkF g' - 1) = bD + 3 * (rkF g - 1) + 1 by omega,
              show ¬ bD + 3 * (rkF g' - 1) = bD + 3 * (rkF g - 1) by omega,
              show ¬ bD + 3 * (rkF g' - 1) + 1 = bD + 3 * (rkF g - 1) + 2 by omega,
              show ¬ bD + 3 * (rkF g' - 1) + 1 = bD + 3 * (rkF g - 1) + 1 by omega,
              show ¬ bD + 3 * (rkF g' - 1) + 1 = bD + 3 * (rkF g - 1) by omega,
              show ¬ bD + 3 * (rkF g' - 1) + 2 = bD + 3 * (rkF g - 1) + 2 by omega,
              show ¬ bD + 3 * (rkF g' - 1) + 2 = bD + 3 * (rkF g - 1) + 1 by omega,
              show ¬ bD + 3 * (rkF g' - 1) + 2 = bD + 3 * (rkF g - 1) by omega, ↓reduceIte]
            exact hA g' hg1 hg2 hg3
          · rw [hmem, hmem, hmem]
            simp only [show ¬ bD + 3 * (rkF g' - 1) = bD + 3 * (rkF g' - 1) + 2 by omega,
              show ¬ bD + 3 * (rkF g' - 1) = bD + 3 * (rkF g' - 1) + 1 by omega,
              show ¬ bD + 3 * (rkF g' - 1) + 1 = bD + 3 * (rkF g' - 1) + 2 by omega,
              ↓reduceIte, and_self]
        · have ha' := ha g hglo (by omega) hp
          rw [hmem]
          simp only [ha'.1, ha'.2.1, ha'.2.2, ↓reduceIte]
          exact hB a (fun g' h1 h2 h3 => ha g' h1 (by omega) h3)
      · refine spec_seq (spec_ifLtN_false (by rw [g36, g40]; exact hp) ?_)
        refine spec_skip hw₁ ?_
        refine spec_instr (Exec.addN hw₁ 1032 1032 1001 (by
          rw [q 1032 (by omega) (by omega) (by omega) (by omega) (by omega),
            q 1001 (by omega) (by omega) (by omega) (by omega) (by omega), h32, h01]; omega))
          (fun hw' => ?_)
        refine ⟨⟨hw', ?_⟩, by omega⟩
        config_simp
        rw [q 1032 (by omega) (by omega) (by omega) (by omega) (by omega),
          q 1001 (by omega) (by omega) (by omega) (by omega) (by omega), h32, h01, hm₁]
        rw [q 1033 (by omega) (by omega) (by omega) (by omega) (by omega),
          q 1030 (by omega) (by omega) (by omega) (by omega) (by omega),
          q 1012 (by omega) (by omega) (by omega) (by omega) (by omega),
          q 1013 (by omega) (by omega) (by omega) (by omega) (by omega),
          q 1018 (by omega) (by omega) (by omega) (by omega) (by omega),
          q 1052 (by omega) (by omega) (by omega) (by omega) (by omega)]
        refine ⟨by trivial, h33, rfl, h30', h12, h13, h18, h52, by omega, fun g' h1 h2 h3 => ?_,
          fun a ha => hB a (fun g' h1 h2 h3 => ha g' h1 (by omega) h3)⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
        · exact hA g' h1 h2 h3
        · exact absurd h3 hp)
    hle ⟨hc, hg, hgE, h1, h30, rfl, rfl, rfl, rfl, le_rfl, fun g' h1 h2 _ => by omega,
      fun a _ => rfl⟩
  exact ⟨c', k', e', by have := hk'; nlinarith, hI'.2.2.2.2.2.2.2.2.2.2.1,
    fun a ha => hI'.2.2.2.2.2.2.2.2.2.2.2 a ha⟩

/-! ### The dart pass -/

/-- The body of the dart pass: the darts of the vertex `L[j]`. -/
def dartOBody : Stmt :=
  .seq (block [.addN 1034 1015 1030, .loadN 1031 1034, .addN 1034 1010 1031, .loadN 1032 1034,
    .addN 1034 1034 1001, .loadN 1033 1034])
  (.seq (.whileLtN 1032 1033 dartBody) (.instr (.addN 1030 1030 1001)))

/-- **The dart pass** (loop over the list). -/
def dartLoop : Stmt := .seq (.instr (.constN 1030 0)) (.whileLtN 1030 1016 dartOBody)

/-- **The dart pass**: for every vertex `L[j]` and every dart `g` of it of rank `rk[g] > 0`, the
three words `j`, `rk[rv g] - 1`, `rk[fr g] - 1` at the slot `bD + 3 (rk[g] - 1)`; the memory
outside `[bD, bD + 3 m')` is kept. -/
theorem dartLoop_exec {c : Config} (hc : WordsBounded W c) {N M k m' Δ : ℕ}
    (Lv ofsF rkF rvF roF frF : ℕ → ℕ)
    (h1 : c.nreg 1001 = 1) (hk : c.nreg 1016 = k)
    (hL : ∀ j < k, c.nmem (c.nreg 1015 + j) = Lv j) (hLN : ∀ j < k, Lv j < N)
    (hinc : ∀ i j, i < j → j < k → Lv i < Lv j)
    (hofs : ∀ v ≤ N, c.nmem (c.nreg 1010 + v) = ofsF v)
    (hmono : ∀ v v', v ≤ v' → v' ≤ N → ofsF v ≤ ofsF v') (hofsM : ofsF N ≤ M)
    (hrk : ∀ x < M, c.nmem (c.nreg 1018 + x) = rkF x)
    (hro : ∀ x < M, c.nmem (c.nreg 1013 + x) = roF x)
    (hrv : ∀ g < M, 0 < rkF g → c.nmem (c.nreg 1012 + g) = rvF g ∧ rvF g < M)
    (hm' : ∀ g < M, rkF g ≤ m')
    (hfr : ∀ g < M, 0 < rkF g → ∃ n, 0 < n ∧ n ≤ Δ ∧ 0 < rkF (roF^[n] g) ∧
      (∀ i, 0 < i → i < n → rkF (roF^[i] g) = 0) ∧ (∀ i ≤ n, roF^[i] g < M) ∧
      roF^[n] g = frF g)
    (hinj : ∀ g g', g < M → g' < M → 0 < rkF g → rkF g = rkF g' → g = g')
    (cD : c.nreg 1052 + 3 * m' ≤ c.nreg 1010) (c0 : c.nreg 1010 + N < c.nreg 1012)
    (c1 : c.nreg 1012 + M ≤ c.nreg 1013) (c2 : c.nreg 1013 + M ≤ c.nreg 1015)
    (c5 : c.nreg 1015 + k ≤ c.nreg 1018) (c3 : c.nreg 1018 + M ≤ W) :
    ∃ c' k', Exec P W dartLoop c c' k' ∧ k' ≤ (6 * Δ + 22) * psum ofsF Lv k + 12 * k + 4 ∧
      (∀ j < k, ∀ g, ofsF (Lv j) ≤ g → g < ofsF (Lv j + 1) → 0 < rkF g →
        c'.nmem (c.nreg 1052 + 3 * (rkF g - 1)) = j ∧
        c'.nmem (c.nreg 1052 + 3 * (rkF g - 1) + 1) = rkF (rvF g) - 1 ∧
        c'.nmem (c.nreg 1052 + 3 * (rkF g - 1) + 2) = rkF (frF g) - 1) ∧
      (∀ a, (a < c.nreg 1052 ∨ c.nreg 1052 + 3 * m' ≤ a) → c'.nmem a = c.nmem a) := by
  set aOfs := c.nreg 1010
  set aRv := c.nreg 1012
  set aRo := c.nreg 1013
  set aL := c.nreg 1015
  set aRk := c.nreg 1018
  set bD := c.nreg 1052
  have hps : ∀ j ≤ k, psum ofsF Lv j ≤ M := fun j hj => by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [psum]
    · have := psum_le hmono hLN hinc j hj0 hj
      have := hmono (Lv (j - 1) + 1) N (by have := hLN (j - 1) (by omega); omega) le_rfl
      omega
  let Wr : ℕ → ℕ → Prop := fun j a => ∀ j' < j, ∀ g, ofsF (Lv j') ≤ g → g < ofsF (Lv j' + 1) →
    0 < rkF g → a ≠ bD + 3 * (rkF g - 1) ∧
    a ≠ bD + 3 * (rkF g - 1) + 1 ∧ a ≠ bD + 3 * (rkF g - 1) + 2
  let Inv : ℕ → Config → Prop := fun j d => WordsBounded W d ∧ d.nreg 1030 = j ∧ j ≤ k ∧
    d.nreg 1016 = k ∧ d.nreg 1001 = 1 ∧ d.nreg 1010 = aOfs ∧ d.nreg 1012 = aRv ∧
    d.nreg 1013 = aRo ∧ d.nreg 1015 = aL ∧ d.nreg 1018 = aRk ∧ d.nreg 1052 = bD ∧
    (∀ j' < j, ∀ g, ofsF (Lv j') ≤ g → g < ofsF (Lv j' + 1) → 0 < rkF g →
      d.nmem (bD + 3 * (rkF g - 1)) = j' ∧
      d.nmem (bD + 3 * (rkF g - 1) + 1) = rkF (rvF g) - 1 ∧
      d.nmem (bD + 3 * (rkF g - 1) + 2) = rkF (frF g) - 1) ∧
    (∀ a, Wr j a → d.nmem a = c.nmem a)
  have outside : ∀ j ≤ k, ∀ a, (a < bD ∨ bD + 3 * m' ≤ a) → Wr j a :=
    fun j hj a ha j' hj' g _ hg2 hp => by
      have := hLN j' (by omega)
      have := hmono (Lv j' + 1) N (by omega) le_rfl
      have := hm' g (by omega)
      refine ⟨by omega, by omega, by omega⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = 6 * Δ + 22 := ⟨_, rfl⟩
  have e₀ := Exec.constN (P := P) hc 1030 0 (Nat.zero_le _)
  obtain ⟨c', k', e', ⟨j, hjk, hI'⟩, hn, hk'⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 1030) (b := 1016) (body := dartOBody) (fun d => ∃ j ≤ k, Inv j d)
    (fun d => 12 * (k - d.nreg 1030) + B * (psum ofsF Lv k - psum ofsF Lv (d.nreg 1030)))
    (fun d h => by obtain ⟨_, _, h⟩ := h; exact h.1)
    (fun d h hlt => by
      obtain ⟨j, -, hw, h30, hjk, h16, h01, h10, h12, h13, h15, h18, h52, hA, hB'⟩ := h
      rw [h30, h16] at hlt
      have hv := hLN j hlt
      have hpsj := hps (j + 1) hlt
      have hpsS : psum ofsF Lv (j + 1) = psum ofsF Lv j + (ofsF (Lv j + 1) - ofsF (Lv j)) := by
        simp [psum, Finset.sum_range_succ]
      have hmv := hmono (Lv j) (Lv j + 1) (by omega) (by omega)
      have hM' : ofsF (Lv j + 1) ≤ M := (hmono _ N (by omega) le_rfl).trans hofsM
      have r1 : d.nmem (aL + j) = Lv j := by
        rw [hB' _ (outside j hjk _ (by right; omega))]; exact hL j hlt
      have r3 : d.nmem (aOfs + Lv j) = ofsF (Lv j) := by
        rw [hB' _ (outside j hjk _ (by right; omega))]; exact hofs _ hv.le
      have r4 : d.nmem (aOfs + Lv j + 1) = ofsF (Lv j + 1) := by
        rw [hB' _ (outside j hjk _ (by right; omega)), Nat.add_assoc]; exact hofs _ hv
      obtain ⟨d₁, k₁, e₁, hw₁, g32, g33, hm₁, hr₁, hk₁⟩ : ∃ d₁ k₁, Exec P W
          (block [.addN 1034 1015 1030, .loadN 1031 1034, .addN 1034 1010 1031, .loadN 1032 1034,
            .addN 1034 1034 1001, .loadN 1033 1034]) d d₁ k₁ ∧ WordsBounded W d₁ ∧
          d₁.nreg 1032 = ofsF (Lv j) ∧ d₁.nreg 1033 = ofsF (Lv j + 1) ∧ d₁.nmem = d.nmem ∧
          (∀ r, r ≠ 1031 → r ≠ 1032 → r ≠ 1033 → r ≠ 1034 → d₁.nreg r = d.nreg r) ∧
          k₁ = 6 := by
        exec_block
        rotate_right
        refine ⟨‹WordsBounded _ _›, ?_, ?_, rfl, fun r ha hb hc' hd => ?_, rfl⟩
        · config_simp; simp only [h15, h30, h10, r1, r3]
        · config_simp; simp only [h15, h30, h10, h01, r1, r4]
        · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl
        all_goals (config_simp; simp only [h15, h30, h10, h01, r1]; omega)
      have q : ∀ r, 1034 < r → d₁.nreg r = d.nreg r := fun r hr =>
        hr₁ r (by omega) (by omega) (by omega) (by omega)
      have q' : ∀ r, r < 1031 → d₁.nreg r = d.nreg r := fun r hr =>
        hr₁ r (by omega) (by omega) (by omega) (by omega)
      have rdc : ∀ a, bD + 3 * m' ≤ a → d₁.nmem a = c.nmem a := fun a ha => by
        rw [hm₁, hB' _ (outside j hjk _ (by right; exact ha))]
      have inr : ∀ g, ofsF (Lv j) ≤ g → g < ofsF (Lv j + 1) → g < M := fun g _ h => by omega
      obtain ⟨d₂, k₂, e₂, hk₂, hcells, hfr₂⟩ := dartInner_exec (P := P) hw₁ (M := M) (m' := m')
        (Δ := Δ) (j := j) rkF rvF roF frF (by rw [q' _ (by omega), h01])
        (by rw [q' _ (by omega), h30]) g32 g33 hmv hM'
        (fun x hx => by rw [q' 1018 (by omega), h18, rdc _ (by omega)]; exact hrk x hx)
        (fun x hx => by rw [q' 1013 (by omega), h13, rdc _ (by omega)]; exact hro x hx)
        (fun g h1 h2 hp => by
          have := inr g h1 h2
          rw [q' 1012 (by omega), h12, rdc _ (by omega)]; exact hrv g this hp)
        (fun g h1 h2 => hm' g (inr g h1 h2))
        (fun g h1 h2 hp => hfr g (inr g h1 h2) hp)
        (fun g g' h1 h2 h3 h4 hp he => hinj g g' (inr g h1 h2) (inr g' h3 h4) hp he)
        (by rw [q 1052 (by omega), q' 1012 (by omega), h52, h12]; omega)
        (by rw [q' 1012 (by omega), q' 1013 (by omega), h12, h13]; omega)
        (by rw [q' 1013 (by omega), q' 1018 (by omega), h13, h18]; omega)
        (by rw [q' 1018 (by omega), h18]; omega)
      rw [q 1052 (by omega), h52] at hcells hfr₂
      have f₂ : ∀ r, dartBody.wr r = false → d₂.nreg r = d₁.nreg r := fun r hr =>
        Exec.nreg_of_wr e₂ (by simpa [Stmt.wr] using hr)
      have f30 : d₂.nreg 1030 = j := by rw [f₂ 1030 (by decide), q' _ (by omega), h30]
      have f01 : d₂.nreg 1001 = 1 := by rw [f₂ 1001 (by decide), q' _ (by omega), h01]
      refine ⟨_, k₁ + (k₂ + 1), .seq e₁ (.seq e₂ (Exec.addN e₂.wb_right 1030 1030 1001
        (by rw [f30, f01]; omega))), ⟨j + 1, by omega, ?_⟩, ?_⟩
      · refine ⟨Exec.wb_right (Exec.addN (P := P) e₂.wb_right 1030 1030 1001
          (by rw [f30, f01]; omega)), ?_⟩
        config_simp
        rw [f30, f01]
        rw [f₂ 1016 (by decide), f₂ 1010 (by decide), f₂ 1012 (by decide), f₂ 1013 (by decide),
          f₂ 1015 (by decide), f₂ 1018 (by decide), f₂ 1052 (by decide)]
        rw [q' 1016 (by omega), q' 1010 (by omega), q' 1012 (by omega), q' 1013 (by omega),
          q' 1015 (by omega), q' 1018 (by omega), q 1052 (by omega)]
        refine ⟨by trivial, by omega, h16, rfl, h10, h12, h13, h15, h18, h52,
          fun j' hj' g hg1 hg2 hp => ?_, fun a ha => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
          · have h3 := hinc j' j hj' hlt
            have h4 := hmono (Lv j' + 1) (Lv j) (by omega) (by omega)
            have hgM : g < M := by omega
            have hne : ∀ g', ofsF (Lv j) ≤ g' → g' < ofsF (Lv j + 1) → 0 < rkF g' →
                rkF g ≠ rkF g' := fun g' h5 h6 h7 he => by
              have := hinj g g' hgM (by omega) hp he; omega
            have hmg := hm' g hgM
            have hcl : ∀ g', ofsF (Lv j) ≤ g' → g' < ofsF (Lv j + 1) → 0 < rkF g' →
                ∀ t < 3, bD + 3 * (rkF g - 1) + t ≠ bD + 3 * (rkF g' - 1) ∧
                  bD + 3 * (rkF g - 1) + t ≠ bD + 3 * (rkF g' - 1) + 1 ∧
                  bD + 3 * (rkF g - 1) + t ≠ bD + 3 * (rkF g' - 1) + 2 :=
              fun g' h5 h6 h7 t ht => by
                have := hne g' h5 h6 h7
                refine ⟨by omega, by omega, by omega⟩
            rw [hfr₂ _ (fun g' h5 h6 h7 => by simpa using hcl g' h5 h6 h7 0 (by omega)),
              hfr₂ _ (fun g' h5 h6 h7 => hcl g' h5 h6 h7 1 (by omega)),
              hfr₂ _ (fun g' h5 h6 h7 => hcl g' h5 h6 h7 2 (by omega)), hm₁]
            exact hA j' hj' g hg1 hg2 hp
          · exact hcells g hg1 hg2 hp
        · have ha' := ha j (by omega)
          rw [hfr₂ _ (fun g h1 h2 h3 => ha' g h1 h2 h3), hm₁]
          exact hB' a (fun j' hj' => ha j' (by omega))
      · simp only [upd_same, f30, f01]
        rw [h30, hpsS]
        have hpk := psum_mono ofsF Lv (show j + 1 ≤ k by omega)
        have key : B * (psum ofsF Lv k - (psum ofsF Lv j + (ofsF (Lv j + 1) - ofsF (Lv j)))) +
            B * (ofsF (Lv j + 1) - ofsF (Lv j)) = B * (psum ofsF Lv k - psum ofsF Lv j) := by
          rw [← Nat.mul_add]; congr 1; omega
        have hk2 : k₂ ≤ B * (ofsF (Lv j + 1) - ofsF (Lv j)) + 2 := by rw [hBd]; exact hk₂
        omega)
    ⟨0, Nat.zero_le _, e₀.wb_right, by config_simp, Nat.zero_le _, by config_simp; exact hk,
      by config_simp; exact h1, by config_simp; rfl, by config_simp; rfl, by config_simp; rfl,
      by config_simp; rfl, by config_simp; rfl, by config_simp; rfl, fun j' h => by omega,
      fun a _ => rfl⟩
  obtain ⟨hw', h30', -, h16', -, -, -, -, -, -, -, hA', hB''⟩ := hI'
  rw [h30', h16'] at hn
  have hjk' : j = k := by omega
  rw [hjk'] at hA' hB''
  refine ⟨c', 1 + k', .seq e₀ e', ?_, hA', fun a ha => hB'' a (outside k le_rfl a ha)⟩
  simp only [upd_same, show psum ofsF Lv 0 = 0 by simp [psum], Nat.sub_zero] at hk'
  rw [← hBd]
  omega

end Piece

end PlanarSeparator
