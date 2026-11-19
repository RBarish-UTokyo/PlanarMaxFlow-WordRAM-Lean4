module

public import PlanarFlow.Monge.FRTree

/-!
# Range minima in an anti-Monge matrix: the mathematics

A half block of FR-Dijkstra has the targets (rows) `ρ` and the sources (columns) `σ < nc`, and
an anti-Monge matrix `F` (`PlanarFlow.Monge.FR.AntiM`; with the prices of a run on the targets,
`F ρ σ = D σ ρ - p ρ`, and the entry offered by an active source is `E ρ σ = e σ + F ρ σ`, so a
row minimises `E · σ` over a set of rows exactly when it minimises `F · σ`).
The triplets of FR need, for a source `σ` and an interval of rows `[j1, j2]`, a row minimising
`F · σ` over the interval. This file is the mathematics of a structure answering this in
`O(log s)` steps after a build in `O(s log s)` steps.

The rows `ρ < s` (`s = 2 ^ T`) are the leaves of a complete binary tree; the *node* of height `j`
at the offset `o` (a multiple of `2 ^ j`) has the rows `[o, o + 2 ^ j)`. Every internal node has
a **threshold** `θ`: for `σ < nc`, the right child holds a strictly smaller minimum exactly when
`σ < θ` (`win_down`: these sources form an initial segment, by the anti-Monge inequality).
A node stores

* `A`: the thresholds of all the internal nodes below it (itself included), **sorted**, followed
  by the sentinel `nc + 1` (`LOK`); the *gap* of a source `σ` at the node is `cntP A (2 ^ j - 1)
  σ`, the number of these thresholds at most `σ`. The minimum row of a node is the same for all
  the sources of a gap, so a node also stores
* `ROW`: for every gap, a row minimising `F · σ` over the rows of the node, for the sources `σ`
  of the gap;
* `GL`, `GR`: for every gap, the gaps of its sources at the two children. This is the
  *cascading*: once the gap of `σ` is known at a node, the gaps at the children cost one read.

The arrays of a node are the merge of the arrays of its children and its own threshold:
`MS` is the state of the merge, `MS.emitX` a step, `node_ok` the result (the sorted array, and
the correctness of `ROW`, `GL`, `GR`). `QCov`, `QCov.step`, `QCov.final`: the query descends
along the two paths from the root to the leaves `j1` and `j2`, carrying the gaps; a child hanging
inside the interval between the two paths is a canonical node and offers its stored row.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace RM

open FR

/-! ### Minima -/

/-- `ρ` minimises `F · σ` over the rows `[lo, hi)`. -/
def IsArgmin (F : ℕ → ℕ → ℝ) (σ lo hi ρ : ℕ) : Prop :=
  lo ≤ ρ ∧ ρ < hi ∧ ∀ ρ', lo ≤ ρ' → ρ' < hi → F ρ σ ≤ F ρ' σ

/-! ### Counting in arrays -/

/-- The number of entries `e < n` of `f` that are at most `σ`. -/
def cntP (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, σ => cntP f n σ + if f n ≤ σ then 1 else 0

variable {f g : ℕ → ℕ} {n σ : ℕ}

lemma cntP_le (n : ℕ) : cntP f n σ ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => simp only [cntP]; split_ifs <;> omega

lemma cntP_mono {n n' : ℕ} (h : n ≤ n') : cntP f n σ ≤ cntP f n' σ := by
  induction n', h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => simp only [cntP]; omega

lemma cntP_congr (h : ∀ e < n, f e = g e) : cntP f n σ = cntP g n σ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [cntP, ih (fun e he => h e (by omega)), h n (by omega)]

/-- All entries at most `σ` are counted. -/
lemma cntP_all (h : ∀ e < n, f e ≤ σ) : cntP f n σ = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cntP, ih (fun e he => h e (by omega)), h n (by omega), ↓reduceIte]

/-- An array whose first `k` entries are at most `σ` and the next ones above. -/
lemma cntP_eq_of {k : ℕ} (hk : k ≤ n) (h1 : ∀ e < k, f e ≤ σ)
    (h2 : ∀ e, k ≤ e → e < n → σ < f e) : cntP f n σ = k := by
  induction n with
  | zero => simp only [cntP]; omega
  | succ n ih =>
    by_cases hkn : k = n + 1
    · subst hkn; exact cntP_all h1
    · simp only [cntP]
      rw [ih (by omega) (fun e a b => h2 e a (by omega))]
      simp only [not_le.2 (h2 n (by omega) (by omega)), ↓reduceIte, Nat.add_zero]

/-- The array is sorted on `[0, n)`. -/
def SortedTo (f : ℕ → ℕ) (n : ℕ) : Prop := ∀ e, e + 1 < n → f e ≤ f (e + 1)

lemma SortedTo.le (h : SortedTo f n) {e e' : ℕ} (he : e ≤ e') (he' : e' < n) : f e ≤ f e' := by
  induction e', he using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact (ih (by omega)).trans (h m he')

lemma SortedTo.mono {n' : ℕ} (h : SortedTo f n) (hn : n' ≤ n) : SortedTo f n' :=
  fun e he => h e (by omega)

/-- In a sorted array, the counted entries are the first ones. -/
lemma SortedTo.lt_cnt (h : SortedTo f n) {e : ℕ} (he : e < cntP f n σ) : f e ≤ σ := by
  induction n with
  | zero => simp [cntP] at he
  | succ n ih =>
    simp only [cntP] at he
    split_ifs at he with hn
    · have := cntP_le (f := f) (σ := σ) n
      exact (h.le (by omega) (by omega)).trans hn
    · exact ih (h.mono (by omega)) (by omega)

/-- A sorted array of the thresholds `< m`, with the sentinel `nc + 1` at `m`. -/
def LOK (L : ℕ → ℕ) (m nc : ℕ) : Prop := SortedTo L (m + 1) ∧ L m = nc + 1 ∧ ∀ e < m, L e ≤ nc

/-- The array of a single threshold. -/
def Ac (θ nc : ℕ) (e : ℕ) : ℕ := if e = 0 then θ else nc + 1

lemma lok_ac {θ nc : ℕ} (h : θ ≤ nc) : LOK (Ac θ nc) 1 nc :=
  ⟨fun e he => by unfold Ac; split_ifs <;> omega, by simp [Ac], fun e he => by
    unfold Ac; split_ifs <;> omega⟩

lemma cntP_ac {θ nc σ : ℕ} : cntP (Ac θ nc) 1 σ = if θ ≤ σ then 1 else 0 := by
  simp [cntP, Ac]

lemma LOK.lt_of_le {L : ℕ → ℕ} {m nc i : ℕ} (h : LOK L m nc) (hi : i ≤ m) (h' : L i ≤ nc) :
    i < m := by
  rcases Nat.eq_or_lt_of_le hi with rfl | hi
  · rw [h.2.1] at h'; omega
  · exact hi

/-! ### The merge -/

/-- **The state of the merge** of three sorted arrays `X`, `Y`, `Z` (of `mx`, `my`, `mz`
thresholds, each with its sentinel) into `Av`: the first `g` entries of `Av` are sorted, are the
union of the first `ix`, `iy`, `iz` entries of the three arrays (counted below every `σ`), and
are at most the next entries of the three arrays. -/
structure MS (Av X Y Z : ℕ → ℕ) (mx my mz nc g ix iy iz : ℕ) : Prop where
  ix_le : ix ≤ mx
  iy_le : iy ≤ my
  iz_le : iz ≤ mz
  g_eq : g = ix + iy + iz
  cnt : ∀ σ, cntP Av g σ = cntP X ix σ + cntP Y iy σ + cntP Z iz σ
  sorted : SortedTo Av g
  le : ∀ e < g, Av e ≤ nc
  last : 0 < g → Av (g - 1) ≤ X ix ∧ Av (g - 1) ≤ Y iy ∧ Av (g - 1) ≤ Z iz

variable {Av X Y Z : ℕ → ℕ} {mx my mz nc g ix iy iz : ℕ}

lemma MS.init : MS Av X Y Z mx my mz nc 0 0 0 0 :=
  ⟨by omega, by omega, by omega, rfl, fun _ => rfl, fun e he => by omega, fun e he => by omega,
    fun h => by omega⟩

lemma MS.swap12 (h : MS Av X Y Z mx my mz nc g ix iy iz) : MS Av Y X Z my mx mz nc g iy ix iz :=
  ⟨h.iy_le, h.ix_le, h.iz_le, by rw [h.g_eq]; ring, fun σ => by rw [h.cnt σ]; ring, h.sorted,
    h.le, fun hg => ⟨(h.last hg).2.1, (h.last hg).1, (h.last hg).2.2⟩⟩

lemma MS.swap13 (h : MS Av X Y Z mx my mz nc g ix iy iz) : MS Av Z Y X mz my mx nc g iz iy ix :=
  ⟨h.iz_le, h.iy_le, h.ix_le, by rw [h.g_eq]; ring, fun σ => by rw [h.cnt σ]; ring, h.sorted,
    h.le, fun hg => ⟨(h.last hg).2.2, (h.last hg).2.1, (h.last hg).1⟩⟩

/-- **A step of the merge**: the next entry is the head of `X`, not above the other heads. -/
theorem MS.emitX (hX : LOK X mx nc) (hY : LOK Y my nc) (hZ : LOK Z mz nc)
    (h : MS Av X Y Z mx my mz nc g ix iy iz) (hg : g < mx + my + mz) {Av' : ℕ → ℕ}
    (hAv : ∀ e < g, Av' e = Av e) (hnew : Av' g = X ix) (hxy : X ix ≤ Y iy)
    (hxz : X ix ≤ Z iz) : MS Av' X Y Z mx my mz nc (g + 1) (ix + 1) iy iz := by
  have hix := h.ix_le; have hiy := h.iy_le; have hiz := h.iz_le; have hge := h.g_eq
  have hx : X ix ≤ nc := by
    by_contra hc
    have e1 : ix = mx := by
      rcases Nat.eq_or_lt_of_le hix with e | e
      · exact e
      · exact absurd (hX.2.2 ix e) hc
    have e2 : iy = my := by
      rcases Nat.eq_or_lt_of_le hiy with e | e
      · exact e
      · have := hY.2.2 iy e; omega
    have e3 : iz = mz := by
      rcases Nat.eq_or_lt_of_le hiz with e | e
      · exact e
      · have := hZ.2.2 iz e; omega
    omega
  have hlt := hX.lt_of_le hix hx
  refine ⟨by omega, hiy, hiz, by omega, fun σ => ?_, fun e he => ?_, fun e he => ?_, fun _ => ?_⟩
  · simp only [cntP]
    rw [cntP_congr (g := Av) hAv, h.cnt σ, hnew]; split_ifs <;> omega
  · rcases Nat.lt_succ_iff_lt_or_eq.1 (show e + 1 < g + 1 from he) with he' | he'
    · rw [hAv e (by omega), hAv (e + 1) he']; exact h.sorted e he'
    · have he'' : e = g - 1 := by omega
      rw [hAv e (by omega), show e + 1 = g by omega, hnew, he'']
      exact (h.last (by omega)).1
  · rcases Nat.lt_succ_iff_lt_or_eq.1 he with he' | rfl
    · rw [hAv e he']; exact h.le e he'
    · rw [hnew]; exact hx
  · rw [Nat.add_sub_cancel, hnew]
    exact ⟨hX.1 ix (by omega), hxy, hxz⟩

/-! ### A node from its children -/

/-- **The arrays of a node from the merge of its children's arrays and its threshold.** The
children have `m` thresholds each (`h = m + 1` rows), their gap tables `RL`, `RR` give rows
minimising over their rows, and the threshold `θ` separates the sources where the right child
is strictly better. If the merge is complete, and every gap `g` of the result recorded the
pointers `GL g`, `GR g` (and whether `θ` was merged) at the time it was written, then the result
is sorted, and `RV`, `GL`, `GR` are correct for every source. -/
theorem node_ok {F : ℕ → ℕ → ℝ} {Al Ar Av GL GR RL RR RV : ℕ → ℕ} {m o θ : ℕ}
    (hRl : ∀ σ < nc, IsArgmin F σ o (o + (m + 1)) (RL (cntP Al m σ)))
    (hRr : ∀ σ < nc, IsArgmin F σ (o + (m + 1)) (o + 2 * (m + 1)) (RR (cntP Ar m σ)))
    (hθlo : ∀ σ < θ, F (RR (cntP Ar m σ)) σ < F (RL (cntP Al m σ)) σ)
    (hθhi : ∀ σ, θ ≤ σ → σ < nc → ¬ F (RR (cntP Ar m σ)) σ < F (RL (cntP Al m σ)) σ)
    (hM : MS Av Al Ar (Ac θ nc) m m 1 nc (2 * m + 1) m m 1) (hsent : Av (2 * m + 1) = nc + 1)
    (hgap : ∀ g ≤ 2 * m + 1, ∃ iz ≤ 1, GL g ≤ m ∧ GR g ≤ m ∧ GL g + GR g + iz = g ∧
      (∀ σ, cntP Av g σ = cntP Al (GL g) σ + cntP Ar (GR g) σ + cntP (Ac θ nc) iz σ) ∧
      RV g = if iz = 1 then RL (GL g) else RR (GR g)) :
    LOK Av (2 * m + 1) nc ∧ ∀ σ < nc,
      IsArgmin F σ o (o + 2 * (m + 1)) (RV (cntP Av (2 * m + 1) σ)) ∧
      GL (cntP Av (2 * m + 1) σ) = cntP Al m σ ∧ GR (cntP Av (2 * m + 1) σ) = cntP Ar m σ := by
  have hsort : SortedTo Av (2 * m + 1 + 1) := by
    intro e he
    rcases Nat.lt_succ_iff_lt_or_eq.1 he with he' | he'
    · exact hM.sorted e he'
    · rw [he', hsent]; exact (hM.le e (by omega)).trans (by omega)
  refine ⟨⟨hsort, hsent, hM.le⟩, fun σ hσ => ?_⟩
  generalize hg : cntP Av (2 * m + 1) σ = g
  have hgle : g ≤ 2 * m + 1 := hg ▸ cntP_le _
  obtain ⟨iz, hiz, hGL, hGR, hsum, hcnt, hRV⟩ := hgap g hgle
  -- the first `g` entries are at most `σ`
  have hfull : cntP Av g σ = g := by
    have : ∀ e < g, Av e ≤ σ := fun e he =>
      (hsort.mono (n' := 2 * m + 1) (by omega)).lt_cnt (by omega)
    exact cntP_eq_of le_rfl this (fun e a b => by omega)
  have c1 := cntP_le (f := Al) (σ := σ) (GL g)
  have c2 := cntP_le (f := Ar) (σ := σ) (GR g)
  have c3 := cntP_le (f := Ac θ nc) (σ := σ) iz
  have e0 := hcnt σ
  have d1 := cntP_mono (f := Al) (σ := σ) hGL
  have d2 := cntP_mono (f := Ar) (σ := σ) hGR
  have d3 := cntP_mono (f := Ac θ nc) (σ := σ) hiz
  have hfin := hM.cnt σ
  rw [hg] at hfin
  have hac := cntP_ac (θ := θ) (nc := nc) (σ := σ)
  have f1 : cntP Al m σ = GL g := by omega
  have f2 : cntP Ar m σ = GR g := by omega
  have f3 : cntP (Ac θ nc) iz σ = iz := by omega
  refine ⟨?_, f1.symm, f2.symm⟩
  rw [hRV]
  rcases Nat.eq_or_lt_of_le hiz with rfl | hiz0
  · -- `θ ≤ σ`: the left child is not worse
    have hθσ : θ ≤ σ := by
      rw [show (1 : ℕ) = 0 + 1 from rfl] at f3
      simp only [cntP, Ac] at f3; split_ifs at f3 with h' <;> omega
    simp only [↓reduceIte]; rw [← f1]
    have hn := hθhi σ hθσ hσ
    obtain ⟨a1, a2, a3⟩ := hRl σ hσ
    obtain ⟨b1, b2, b3⟩ := hRr σ hσ
    refine ⟨a1, by omega, fun ρ' h1 h2 => ?_⟩
    by_cases hρ : ρ' < o + (m + 1)
    · exact a3 ρ' h1 hρ
    · exact (not_lt.1 hn).trans (b3 ρ' (by omega) h2)
  · have hiz0' : iz = 0 := by omega
    subst hiz0'
    have hθσ : σ < θ := by
      by_contra hc
      have := hM.cnt σ; rw [hg] at this
      simp only [hac, not_lt.1 hc, ↓reduceIte] at this
      simp only [cntP] at f3 c3; omega
    simp only [show (0 : ℕ) ≠ 1 by omega, ↓reduceIte]; rw [← f2]
    have hy := hθlo σ hθσ
    obtain ⟨a1, a2, a3⟩ := hRl σ hσ
    obtain ⟨b1, b2, b3⟩ := hRr σ hσ
    refine ⟨by omega, b2, fun ρ' h1 h2 => ?_⟩
    by_cases hρ : ρ' < o + (m + 1)
    · exact hy.le.trans (a3 ρ' h1 hρ)
    · exact b3 ρ' (by omega) h2

/-- **The sources where the right child is strictly better form an initial segment**, for any
choice of minimising rows `rl σ`, `rr σ` of the two children. -/
theorem win_down {s nc : ℕ} {F : ℕ → ℕ → ℝ} (hA : AntiM s nc F) {o h : ℕ} (hs : o + 2 * h ≤ s)
    {rl rr : ℕ → ℕ} (hl : ∀ σ < nc, IsArgmin F σ o (o + h) (rl σ))
    (hr : ∀ σ < nc, IsArgmin F σ (o + h) (o + 2 * h) (rr σ)) {σ σ' : ℕ} (hσ : σ < σ')
    (hσ' : σ' < nc) (hP : F (rr σ') σ' < F (rl σ') σ') : F (rr σ) σ < F (rl σ) σ := by
  obtain ⟨a1, a2, a3⟩ := hl σ (by omega)
  obtain ⟨-, -, a3'⟩ := hl σ' hσ'
  obtain ⟨b1, b2, b3⟩ := hr σ (by omega)
  obtain ⟨b1', b2', -⟩ := hr σ' hσ'
  have h1 : F (rr σ') σ' < F (rl σ) σ' := lt_of_lt_of_le hP (a3' _ a1 a2)
  have key := hA (rl σ) (rr σ') σ σ' (by omega) (by omega) hσ hσ'
  have : F (rr σ') σ < F (rl σ) σ := by linarith
  exact lt_of_le_of_lt (b3 _ b1' b2') this

/-! ### The query -/

/-- **The state of the query** at the node size `n`: the paths to `j1` and `j2` are at the nodes
`[ox, ox + n)` and `[oy, oy + n)` (equal or disjoint), and the row `b` of `[j1, j2]` is not worse
than `j1` and than every row of `[j1, j2]` outside these two nodes. -/
structure QCov (F : ℕ → ℕ → ℝ) (σ j1 j2 n ox oy b : ℕ) : Prop where
  x1 : ox ≤ j1
  x2 : j1 < ox + n
  y1 : oy ≤ j2
  y2 : j2 < oy + n
  dxy : ox < oy → ox + n ≤ oy
  dyx : oy < ox → oy + n ≤ ox
  b1 : j1 ≤ b
  b2 : b ≤ j2
  cov : ∀ ρ, j1 ≤ ρ → ρ ≤ j2 → (ρ = j1 ∨ ((ρ < ox ∨ ox + n ≤ ρ) ∧ (ρ < oy ∨ oy + n ≤ ρ))) →
    F b σ ≤ F ρ σ

/-- The start of the query, at the root. -/
lemma QCov.init {F : ℕ → ℕ → ℝ} {σ j1 j2 s : ℕ} (h12 : j1 ≤ j2) (h2 : j2 < s) :
    QCov F σ j1 j2 s 0 0 j1 :=
  ⟨by omega, by omega, by omega, by omega, fun h => by omega, fun h => by omega, le_rfl, h12,
    fun ρ h1 h2' h3 => by rcases h3 with rfl | h3 <;> first | exact le_rfl | omega⟩

/-- **A step of the query** from the node size `2 h` to `h`: each path goes to the child holding
its leaf; a child hanging between the paths (the right child of the left path, or the left child
of the right path, when the paths are apart) lies inside `[j1, j2]`, and the new row `b'` is not
worse than its rows. -/
theorem QCov.step {F : ℕ → ℕ → ℝ} {σ j1 j2 h ox oy b b' : ℕ}
    (hq : QCov F σ j1 j2 (2 * h) ox oy b) (hb1 : j1 ≤ b') (hb2 : b' ≤ j2) (hbb : F b' σ ≤ F b σ)
    (hx : j1 < ox + h → ox < oy → ∀ ρ, ox + h ≤ ρ → ρ < ox + 2 * h → F b' σ ≤ F ρ σ)
    (hy : oy + h ≤ j2 → ox < oy → ∀ ρ, oy ≤ ρ → ρ < oy + h → F b' σ ≤ F ρ σ) :
    QCov F σ j1 j2 h (if ox + h ≤ j1 then ox + h else ox) (if oy + h ≤ j2 then oy + h else oy)
      b' := by
  obtain ⟨x1, x2, y1, y2, dxy, dyx, -, -, cov⟩ := hq
  refine ⟨by split_ifs <;> omega, by split_ifs <;> omega, by split_ifs <;> omega,
    by split_ifs <;> omega, fun h' => by split_ifs at h' ⊢ <;> omega,
    fun h' => by split_ifs at h' ⊢ <;> omega, hb1, hb2, fun ρ h1 h2 h3 => ?_⟩
  by_cases hold : ρ = j1 ∨ ((ρ < ox ∨ ox + 2 * h ≤ ρ) ∧ (ρ < oy ∨ oy + 2 * h ≤ ρ))
  · exact hbb.trans (cov ρ h1 h2 hold)
  · rcases h3 with rfl | h3
    · exact absurd (Or.inl rfl) hold
    have hxy : ox ≤ oy := by
      by_contra hc; have := dyx (by omega); omega
    by_cases hin : ox ≤ ρ ∧ ρ < ox + 2 * h
    · -- `ρ` is in the node of the left path, not in its child
      split_ifs at h3 with c1 c2 c2 <;> try omega
      · have hne : ox < oy := by
          by_contra hc
          have : ox = oy := by omega
          subst this; omega
        exact hx (by omega) hne ρ (by omega) (by omega)
      · have hne : ox < oy := by
          by_contra hc
          have : ox = oy := by omega
          subst this; omega
        exact hx (by omega) hne ρ (by omega) (by omega)
    · have hiny : oy ≤ ρ ∧ ρ < oy + 2 * h := by omega
      have hne : ox < oy := by
        by_contra hc
        have : ox = oy := by omega
        subst this; omega
      split_ifs at h3 with c1 c2 c2 <;> try omega
      · exact hy c2 hne ρ (by omega) (by omega)
      · exact hy c2 hne ρ (by omega) (by omega)

/-- **The end of the query**: at the leaves, the better of `b` and `j2` minimises over
`[j1, j2]`. -/
theorem QCov.final {F : ℕ → ℕ → ℝ} {σ j1 j2 ox oy b b' : ℕ}
    (hq : QCov F σ j1 j2 1 ox oy b) (hb' : b' = b ∨ b' = j2) (hbb : F b' σ ≤ F b σ)
    (hbj : F b' σ ≤ F j2 σ) : IsArgmin F σ j1 (j2 + 1) b' := by
  obtain ⟨x1, x2, y1, y2, -, -, b1, b2, cov⟩ := hq
  refine ⟨by rcases hb' with rfl | rfl <;> omega, by rcases hb' with rfl | rfl <;> omega,
    fun ρ h1 h2 => ?_⟩
  by_cases hρ : ρ = j2
  · rw [hρ]; exact hbj
  · exact hbb.trans (cov ρ h1 (by omega) (by
      by_cases hρ1 : ρ = j1
      · exact Or.inl hρ1
      · right; omega))

end RM

end Monge

end PlanarFlow
