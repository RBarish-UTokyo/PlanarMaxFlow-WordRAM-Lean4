module

public import PlanarSeparator.Machine.MillerWalk

/-!
# Miller's separator on the machine: step 8, a balanced simple fundamental cycle

Step 8 of the plan in `PlanarSeparator/Machine/Miller.lean`: after the search of the dual tree
(`PlanarSeparator/Machine/Search.lean`), with the vertices of the darts, the root sums, the weights,
the depths and the table of ancestors of a spanning tree `T` in memory, the program `step8` runs

* `bpass` and the pass of Lipton and Tarjan: the weights of the strict insides of the darts
  `pd F` (`PlanarSeparator/Machine/MillerInC.lean`);
* `wsum`: the total weight `tot`;
* the walk `mwalk` (`PlanarSeparator/Machine/MillerWalk.lean`).

This file identifies the numbers of the walk with the weights of the plane map (`cwN_eq`: the
weight of a fundamental cycle, `IvM_eq`: the weight of the strict inside of any dart off the tree,
`mwh_tree`: the rules `MWH`) and proves **`step8_tree`**: within
`(125 L + 347) k + 6 n + 100 L + 312` steps, `r353` is the number of a dart `δ` off the tree with
`3 W (inC δ) ≤ 2 W` and `3 W (outC δ) ≤ 2 W` (`W` the total weight): the conclusion of
`PlanarSeparator.Map.SpTree.exists_simple_balanced`.

Registers: those of `MillerWalk.lean`; `wsum` writes `r320`, `r365 … r367`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset CycleSearch

/-! ### The total weight -/

/-- One vertex `r365 = u` of the total `r320`. -/
def wsumBody : Stmt :=
  block [.addN 366 250 365, .loadN 367 366, .addN 320 320 367, .addN 365 365 141]

/-- **The total weight** `r320 = Σ_{u < n} w u`. -/
def wsum : Stmt := .seq (block [.copyN 365 140, .copyN 320 140]) (.whileLtN 365 161 wsumBody)

/-- **The total weight.** Within `6 n + 4` steps, `r320` is the sum of the weights at `bW`. -/
theorem wsum_exec {W : ℕ} {P : Input} {n bW : ℕ} {w : ℕ → ℕ} (hW : bW + n ≤ W)
    (htot : ∑ u ∈ range n, w u ≤ W) (c : Config) (hc : WordsBounded W c) (h140 : c.nreg 140 = 0)
    (h141 : c.nreg 141 = 1) (h161 : c.nreg 161 = n) (h250 : c.nreg 250 = bW)
    (hm : ∀ u < n, c.nmem (bW + u) = w u) :
    ∃ c' t, Exec P W wsum c c' t ∧ t ≤ 6 * n + 4 ∧ c'.nreg 320 = ∑ u ∈ range n, w u ∧
      (∀ r, r ≠ 320 → r ≠ 365 → r ≠ 366 → r ≠ 367 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.output = c.output := by
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 365 = i ∧ i ≤ n ∧
    c'.nreg 320 = ∑ u ∈ range i, w u ∧
    (∀ r, r ≠ 320 → r ≠ 365 → r ≠ 366 → r ≠ 367 → c'.nreg r = c.nreg r) ∧
    c'.nmem = c.nmem ∧ c'.output = c.output
  have hle : ∀ i ≤ n, ∑ u ∈ range i, w u ≤ ∑ u ∈ range n, w u := fun i hi =>
    sum_le_sum_of_subset (range_subset_range.2 hi)
  obtain ⟨c₁, t₁, e₁, hI₁, rfl⟩ : ∃ c₁ t₁, Exec P W (block [.copyN 365 140, .copyN 320 140])
      c c₁ t₁ ∧ I 0 c₁ ∧ t₁ = 2 := by
    exec_block
    refine ⟨⟨‹_›, by config_simp; exact h140, by omega, by config_simp; rw [h140]; simp,
      fun r a b _ _ => by config_simp; rw [upd_other _ _ _ a, upd_other _ _ _ b], rfl, rfl⟩, rfl⟩
  obtain ⟨c', t, e, hI', ht⟩ := Exec.forN (P := P) (W := W) (ri := 365) (rN := 161) (N := n)
    (lo := 0) (B := 4) (body := wsumBody) I
    (fun i c' h => ⟨h.1, h.2.1, (h.2.2.2.2.1 161 (by omega) (by omega) (by omega) (by omega)).trans h161⟩)
    (fun i c₁ ⟨hw, h365, hi, h320, hr, hm₁, ho⟩ hlt => by
      have hc := hw
      have g250 := (hr 250 (by omega) (by omega) (by omega) (by omega)).trans h250
      have g141 := (hr 141 (by omega) (by omega) (by omega) (by omega)).trans h141
      have mw : c₁.nmem (bW + i) = w i := by rw [hm₁]; exact hm i hlt
      have hs := hle (i + 1) hlt
      rw [sum_range_succ] at hs
      unfold wsumBody
      exec_block
      all_goals try (config_simp; simp only [g250, h365, mw, h320, g141]; omega)
      refine ⟨⟨‹_›, ?_, by omega, ?_, fun r a b c' d' => ?_, hm₁, ho⟩, le_rfl⟩
      all_goals config_simp
      · rw [h365, g141]
      · rw [g250, h365, mw, h320, sum_range_succ]
      · simp only [upd_apply]; split_ifs <;> first | omega | exact hr r a b c' d')
    (by omega) hI₁
  exact ⟨c', 2 + t, .seq e₁ e, by omega, hI'.2.2.2.1, hI'.2.2.2.2.1, hI'.2.2.2.2.2.1,
    hI'.2.2.2.2.2.2⟩

/-! ### The numbers of the walk on a plane triangulation -/

section Bridge

open Map Coded

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}
  {T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n} {A Tm : ℕ → ℕ}
  {V f R w Jf : ℕ → ℕ} {Lc : ℕ → ℕ → ℕ} (wv : Q → ℕ) {Fw : ℕ → ℕ} {W : ℕ} {o : List ℕ}
  {c₀ : Config}

/-- The weights of the strict insides, outsides and cycles add up to the total. -/
theorem sum_inC_outC_cycV (T : M.SpTree) (δ : D) :
    ∑ v ∈ T.inC δ, wv v + ∑ v ∈ T.outC δ, wv v + ∑ v ∈ T.cycV δ, wv v = ∑ v, wv v := by
  rw [T.outC_eq, add_comm (∑ v ∈ T.inC δ, wv v), sum_sdiff (T.inC_subset δ), add_comm,
    sum_add_sum_compl]

/-- The data of the walk for a coded triangulation. -/
abbrev wdOf (k : ℕ) (A Tm pdf Jf V R w : ℕ → ℕ) (Lc : ℕ → ℕ → ℕ) (tot : ℕ) : WD :=
  ⟨k, A, Tm, pdf, Jf, V, R, w, Lc, tot⟩

variable (hC : Coded M T k cd A Tm) (hk : 0 < k) (hV : ∀ x, V (cd x) = vi (M.vert x))
  (hf : ∀ x, f (vi x) = vi (T.parent x)) (hR : ∀ x, R (vi x) = rsT T wv x)
  (hw : ∀ x, w (vi x) = wv x) (hLc : ∀ u v, u < n → v < n → IsLCA f u v (Lc u v))

include hC hV hf hR hw hLc in
/-- **The weight of a fundamental cycle**, numerically. -/
theorem cwN_eq (pdf : ℕ → ℕ) (tot : ℕ) {y : ℕ} (hy : y < 3 * k) (hT : Tm y = 0) :
    cwN (wdOf k A Tm pdf Jf V R w Lc tot) y =
      ∑ v ∈ T.cycV (dartN (cd := cd) hk y), wv v := by
  set δ := dartN (cd := cd) hk y
  have e0 : (cd δ : ℕ) = y := cd_dartN hk hy
  have hnt : ¬ T.IsTree δ := (hC.T_cd δ).1 (by rw [e0]; exact hT)
  have hx : V y = vi (M.vert δ) := by rw [← e0, hV]
  have hz : V (A y) = vi (M.vert (M.α δ)) := by rw [← e0, hC.A_cd, hV]
  have hl := Lc_dart (hf := hf) (hLc := hLc) δ
  have hs := SpTree.sum_cycV (T := T) (fun v => (wv v : ℤ)) hnt
  have cast : ∀ v, (∑ u ∈ T.anc v, (wv u : ℤ)) = (rsT T wv v : ℤ) := fun v => by
    unfold rsT; push_cast; rfl
  rw [cast, cast, cast] at hs
  have hS : (∑ v ∈ T.cycV δ, (wv v : ℤ)) = ((∑ v ∈ T.cycV δ, wv v : ℕ) : ℤ) := by push_cast; rfl
  rw [hS] at hs
  have e1 := rsT_mono wv (SpTree.lca_mem_anc (T := T) δ)
  have e2 := rsT_mono wv (SpTree.lca_mem_anc' (T := T) δ)
  unfold cwN
  simp only [wdOf]
  rw [hx, hz, hl, hR, hR, hR, hw]
  apply Nat.cast_injective (R := ℤ)
  rw [hs]
  push_cast [Nat.cast_sub e1, Nat.cast_sub e2]
  ring

variable (hS : SB k A Tm Fw W o c₀) (hall : c₀.nreg 11 = k)
  (hJ : ∀ f < k, f ≠ 0 → Jf f = IvalC (T := T) (cd := cd) (c₀ := c₀) wv hk f)

include hC hV hf hR hw hLc hS hall hJ in
/-- **The weight of the strict inside of any dart off the tree**, numerically. -/
theorem IvM_eq (hM : M.IsPlane) {y : ℕ} (hy : y < 3 * k) (hT : Tm y = 0) :
    IvM (wdOf k A Tm (pd k c₀.nmem) Jf V R w Lc (∑ v, wv v)) y =
      ∑ v ∈ T.inC (dartN (cd := cd) hk y), wv v := by
  set δ := dartN (cd := cd) hk y
  have e0 : (cd δ : ℕ) = y := cd_dartN hk hy
  have hnt : ¬ T.IsTree δ := (hC.T_cd δ).1 (by rw [e0]; exact hT)
  by_cases h : y / 3 ≠ 0 ∧ pd k c₀.nmem (y / 3) = y
  · have h1 := h.1
    have h2 := h.2
    simp only [IvM, wdOf, h1, h2, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    rw [hJ _ (by omega) h1]; unfold IvalC; rw [h2]
  · simp only [IvM, wdOf, h, ↓reduceIte]
    rcases hC.pdor hk hS hall hM y hy hT with h' | ⟨h1, h2⟩
    · exact absurd h' h
    · have hAy := hC.tri.A_lt y hy
      have hTA : Tm (A y) = 0 := by rw [hC.tri.T_A y hy]; exact hT
      have e1 : Jf (A y / 3) = ∑ v ∈ T.inC (M.α δ), wv v := by
        rw [hJ _ (by omega) h1]; unfold IvalC; rw [h2, hC.dartN_A hk hy]
      have hcw := cwN_eq wv hC hk hV hf hR hw hLc (pd k c₀.nmem) (∑ v, wv v) hAy hTA
        (Jf := Jf)
      have e2 : cwN (wdOf k A Tm (pd k c₀.nmem) Jf V R w Lc (∑ v, wv v)) (A y) =
          ∑ v ∈ T.cycV δ, wv v := by
        rw [hcw, hC.dartN_A hk hy, SpTree.cycV_α]
      have hntα : ¬ T.IsTree (M.α δ) := by rwa [T.isTree_α]
      have hio := SpTree.inC_α (T := T) hM hntα
      rw [M.α_α] at hio
      have hsum := sum_inC_outC_cycV wv T (M.α δ)
      rw [SpTree.cycV_α] at hsum
      simp only [wdOf] at e2
      rw [e1, e2, hio]
      omega

include hC hV hf hR hw hLc hS hall hJ in
theorem cvM_eq (hM : M.IsPlane) {z : ℕ} (hz : z < 3 * k) :
    cvM (wdOf k A Tm (pd k c₀.nmem) Jf V R w Lc (∑ v, wv v)) z =
      ∑ v ∈ T.inC (dartN (cd := cd) hk z), wv v := by
  dsimp only [cvM]
  split_ifs with hT
  · exact IvM_eq wv hC hk hV hf hR hw hLc hS hall hJ hM hz hT
  · have ht : T.IsTree (dartN (cd := cd) hk z) := by
      by_contra h; exact hT (by rw [← cd_dartN (cd := cd) hk hz]; exact (hC.T_cd _).2 h)
    rw [SpTree.inC_eq_empty hM ht, sum_empty]

include hC hV hf hR hw hLc hS hall hJ in
/-- **The rules of the walk** for a coded triangulation: the recurrence of the strict insides
with `Bs y = W (bset y)`, `bset` on the cycles of the children, the complement rule, and the
size `#(inside y)`. -/
theorem mwh_tree (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ) :
    MWH (wdOf k A Tm (pd k c₀.nmem) Jf V R w Lc (∑ v, wv v))
      (fun y => #(T.inside (dartN (cd := cd) hk y)))
      (fun y => ∑ v ∈ SpTree.bset (T := T) (dartN (cd := cd) hk y), wv v) := by
  have nt : ∀ y < 3 * k, Tm y = 0 → ¬ T.IsTree (dartN (cd := cd) hk y) := fun y hy hT =>
    (hC.T_cd _).1 (by rw [cd_dartN hk hy]; exact hT)
  have ch₁ : ∀ y < 3 * k, dartN (cd := cd) hk (A (phi3 y)) =
      M.α (M.φ (dartN (cd := cd) hk y)) := fun y hy => by
    rw [hC.dartN_A hk (phi3_lt hy), hC.dartN_phi3 hk hy]
  have ch₂ : ∀ y < 3 * k, dartN (cd := cd) hk (A (phi3 (phi3 y))) =
      M.α (M.φ (M.φ (dartN (cd := cd) hk y))) := fun y hy => by
    rw [hC.dartN_A hk (phi3_lt (phi3_lt hy)), hC.dartN_phi3 hk (phi3_lt hy), hC.dartN_phi3 hk hy]
  have nt' : ∀ z < 3 * k, Tm z = 0 → ¬ T.IsTree (dartN (cd := cd) hk z) := nt
  refine ⟨fun y hy hT => ?_, fun y hy hT h₁ => ?_, fun y hy hT h₂ => ?_,
    fun y hy hT h₁ h₂ => ?_, fun y hy hT => ?_, fun y hy hT _ => ?_, fun y hy hT _ => ?_,
    fun y _ => ?_⟩
  all_goals dsimp only [wdOf] at *
  · have ha1 := hC.tri.A_lt _ (phi3_lt hy)
    have ha2 := hC.tri.A_lt _ (phi3_lt (phi3_lt hy))
    rw [IvM_eq wv hC hk hV hf hR hw hLc hS hall hJ hM hy hT,
      cvM_eq wv hC hk hV hf hR hw hLc hS hall hJ hM ha1,
      cvM_eq wv hC hk hV hf hR hw hLc hS hall hJ hM ha2, ch₁ y hy, ch₂ y hy]
    exact SpTree.sum_inC (T := T) hM (hT3 _) (nt y hy hT) wv
  · have ha1 := hC.tri.A_lt _ (phi3_lt hy)
    have hcw := cwN_eq wv hC hk hV hf hR hw hLc (pd k c₀.nmem) (∑ v, wv v) ha1 h₁ (Jf := Jf)
    try simp only [wdOf] at hcw ⊢
    rw [hcw, ch₁ y hy]
    have hn1 := nt' _ ha1 h₁
    rw [ch₁ y hy] at hn1
    exact sum_le_sum_of_subset (SpTree.bset_subset₁ (hT3 _) (nt y hy hT) hn1)
  · have ha2 := hC.tri.A_lt _ (phi3_lt (phi3_lt hy))
    have hcw := cwN_eq wv hC hk hV hf hR hw hLc (pd k c₀.nmem) (∑ v, wv v) ha2 h₂ (Jf := Jf)
    try simp only [wdOf] at hcw ⊢
    rw [hcw, ch₂ y hy]
    have hn2 := nt' _ ha2 h₂
    rw [ch₂ y hy] at hn2
    exact sum_le_sum_of_subset (SpTree.bset_subset₂ (hT3 _) (nt y hy hT) hn2)
  · have ha1 := hC.tri.A_lt _ (phi3_lt hy)
    have ha2 := hC.tri.A_lt _ (phi3_lt (phi3_lt hy))
    have t1 : T.IsTree (dartN (cd := cd) hk (A (phi3 y))) := by
      by_contra h; exact h₁ (by rw [← cd_dartN (cd := cd) hk ha1]; exact (hC.T_cd _).2 h)
    have t2 : T.IsTree (dartN (cd := cd) hk (A (phi3 (phi3 y)))) := by
      by_contra h; exact h₂ (by rw [← cd_dartN (cd := cd) hk ha2]; exact (hC.T_cd _).2 h)
    rw [ch₁ y hy] at t1
    rw [ch₂ y hy] at t2
    try simp only
    rw [SpTree.bset_eq_empty (T := T) (hT3 _) (nt y hy hT) t1 t2, sum_empty]
  · have hAy := hC.tri.A_lt y hy
    have hTA : Tm (A y) = 0 := by rw [hC.tri.T_A y hy]; exact hT
    rw [IvM_eq wv hC hk hV hf hR hw hLc hS hall hJ hM hy hT,
      IvM_eq wv hC hk hV hf hR hw hLc hS hall hJ hM hAy hTA,
      cwN_eq wv hC hk hV hf hR hw hLc (pd k c₀.nmem) (∑ v, wv v) hy hT (Jf := Jf),
      hC.dartN_A hk hy, SpTree.inC_α (T := T) hM (nt y hy hT)]
    exact sum_inC_outC_cycV wv T _
  · try simp only
    rw [ch₁ y hy]; exact Map.SpTree.card_inside_lt₁ hM (hT3 _) (nt y hy hT)
  · try simp only
    rw [ch₂ y hy]; exact Map.SpTree.card_inside_lt₂ hM (hT3 _) (nt y hy hT)
  · exact (card_le_univ _).trans hC.card_face.le

/-! ### Step 8 -/

/-- **Step 8**: the weights of the strict insides, the total weight and the walk. -/
def step8 : Stmt := .seq bpass (.seq CycleSearch.pass (.seq wsum mwalk))

theorem sum_range_ofvi {Q : Type*} [Fintype Q] {n : ℕ} (vi : Q ≃ Fin n) {w : ℕ → ℕ} {wv : Q → ℕ}
    (hw : ∀ x, w (vi x) = wv x) : ∑ u ∈ range n, w u = ∑ v, wv v := by
  rw [← Fin.sum_univ_eq_sum_range, ← Equiv.sum_comp vi (fun i : Fin n => w i)]
  simp [hw]

set_option maxHeartbeats 4000000 in
/-- **A balanced simple fundamental cycle on the machine** (step 8 of Miller's separator). Let `M`
be a coded plane triangulation (`Coded`) with `k ≥ 2` faces and a spanning tree `T`, after the
search of the dual tree has found every face (`SB`, `r11 = k`). Let the vertices of the darts,
the root sums `R (vi x) = Σ_{u ∈ anc x} wv u` and the weights `wv` of `T` be in memory
(`BSFix`), with the table of ancestors and the depths (`QFix`), all above `11 k`. Then within
`(125 L + 347) k + 6 n + 100 L + 312` steps `step8` leaves in `r353` the number of a dart `δ` off
the tree whose strict inside and strict outside each weigh at most `2/3` of the total weight. -/
theorem step8_tree {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]
    {M : Map D Q} {T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n}
    {A Tm V f dep R w Fw : ℕ → ℕ} (wv : Q → ℕ) {W : ℕ} {P : Input} {o : List ℕ} {c₀ : Config}
    {bD bU L bV bS bW : ℕ}
    (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ) (hC : CycleSearch.Coded M T k cd A Tm)
    (hk2 : 2 ≤ k) (hS : CycleSearch.SB k A Tm Fw W o c₀) (hall : c₀.nreg 11 = k)
    (hB : BSFix k n bV bS bW W A V R w (CycleSearch.pd k c₀.nmem) c₀)
    (hQ : QFix n (vi T.root) bD bU L W f dep c₀)
    (h11 : 11 * k ≤ bV ∧ 11 * k ≤ bS ∧ 11 * k ≤ bW ∧ 11 * k ≤ bU ∧ 11 * k ≤ bD)
    (hV : ∀ x, V (cd x) = vi (M.vert x)) (hf : ∀ x, f (vi x) = vi (T.parent x))
    (hR : ∀ x, R (vi x) = ∑ u ∈ T.anc x, wv u) (hw : ∀ x, w (vi x) = wv x)
    (hWt : 11 * k + 3 * ∑ v, wv v + 4 ≤ W) :
    ∃ c' t, Exec P W step8 c₀ c' t ∧ t ≤ (125 * L + 347) * k + 6 * n + 100 * L + 312 ∧
      c'.output = o ∧ (∀ a, 11 * k ≤ a → c'.nmem a = c₀.nmem a) ∧
      (∀ a < 3 * k, c'.nmem a = c₀.nmem a) ∧
      ∃ δ : D, (cd δ : ℕ) = c'.nreg 353 ∧ ¬ T.IsTree δ ∧
        3 * ∑ v ∈ T.inC δ, wv v ≤ 2 * ∑ v, wv v ∧ 3 * ∑ v ∈ T.outC δ, wv v ≤ 2 * ∑ v, wv v := by
  classical
  have hk : 0 < k := by omega
  obtain ⟨hlV, hlS, hlW, hlU, hlD⟩ := h11
  let Lc : ℕ → ℕ → ℕ := fun u v => Classical.epsilon (IsLCA f u v)
  have hLc : ∀ u v, u < n → v < n → IsLCA f u v (Lc u v) := fun u v hu hv =>
    Classical.epsilon_spec (hQ.tree.exists_isLCA hu hv)
  have hR' : ∀ x, R (vi x) = rsT T wv x := hR
  have htot : ∀ X : Finset Q, ∑ v ∈ X, wv v ≤ W := fun X =>
    (sum_le_sum_of_subset (subset_univ X)).trans (by omega)
  have hRW : ∀ u < n, R u ≤ W := fun u hu => by
    obtain ⟨x, rfl⟩ := exists_vi vi hu
    rw [hR]; exact htot _
  have hBW : ∀ F, 1 ≤ F → F < k → bnum V A R w Lc (CycleSearch.pd k c₀.nmem F) F ≤ W := by
    intro F h1 hF
    obtain ⟨hpF, hlt, hT0⟩ := hC.pd_spec hk hS hall hF (by omega)
    set pD := CycleSearch.Coded.dartN (cd := cd) hk (CycleSearch.pd k c₀.nmem F)
    have e0 : (cd pD : ℕ) = CycleSearch.pd k c₀.nmem F := CycleSearch.Coded.cd_dartN hk hlt
    have hnt : ¬ T.IsTree pD := (hC.T_cd pD).1 (by rw [e0]; exact hT0)
    have := bnum_dart wv hf hR' hw hLc hV hC hM (hT3 pD) hnt
    rw [e0, hpF] at this
    rw [this]; exact htot _
  -- the weights of `bset`
  obtain ⟨c₁, t₁, e₁, ht₁, hd₁, hr₁, hm₁, ho₁⟩ := bpass_exec (P := P) hB hQ (by omega) (by omega)
    hLc hRW hBW (by omega) hS.wb
  have hS₁ := SB.of_fw hS e₁.wb_right (fun r hr => hr₁ r (Or.inl hr)) hm₁ ho₁
  have hpd : CycleSearch.pd k c₁.nmem = CycleSearch.pd k c₀.nmem :=
    funext fun F => hm₁ _ (Or.inr (by omega))
  have hall₁ : c₁.nreg 11 = k := (hr₁ 11 (Or.inl (by omega))).trans hall
  have hrec₁ : CycleSearch.RecHolds k A Tm (fun f => c₁.nmem (6 * k + f)) (CycleSearch.pd k c₁.nmem)
      (IvalC (T := T) (cd := cd) (c₀ := c₀) wv hk) := by
    intro F hF hF0
    rw [hpd]
    simp only
    rw [hd₁ F (by omega) hF]
    exact recHoldsC wv hf hR' hw hLc hV hC hk hS hall hM hT3 F hF hF0
  -- the pass
  obtain ⟨c₂, t₂, e₂, hw₂, hR₂, -, hm₂, ho₂, hj₂, ht₂⟩ := pass_exec (P := P) hC.tri hS₁ hall₁
    (by rw [hpd]; exact hC.childOk hk hS hall hM) (Ival := IvalC (T := T) (cd := cd) (c₀ := c₀) wv hk)
    (tot := ∑ v, wv v) (fun F _ => sum_le_sum_of_subset (subset_univ _)) hrec₁ hWt hk
  have hwm : CycleSearch.pass.wmax < 27 := by decide
  have fr₂ : ∀ r, 27 ≤ r → c₂.nreg r = c₁.nreg r := fun r hr =>
    e₂.nreg_of_wr (Stmt.wr_of_wmax (by omega))
  have m₂ : ∀ a, a < 6 * k ∨ (7 * k ≤ a ∧ a < 10 * k) ∨ 11 * k ≤ a → c₂.nmem a = c₀.nmem a :=
    fun a ha => by rw [hm₂ a (by omega), hm₁ a (by omega)]
  -- the total weight
  have hsumw := sum_range_ofvi vi hw
  have g140 : c₂.nreg 140 = 0 := by rw [fr₂ 140 (by omega), hr₁ 140 (Or.inl (by omega))]; exact hQ.r140
  have g141 : c₂.nreg 141 = 1 := by rw [fr₂ 141 (by omega), hr₁ 141 (Or.inl (by omega))]; exact hQ.r141
  have g161 : c₂.nreg 161 = n := by rw [fr₂ 161 (by omega), hr₁ 161 (Or.inl (by omega))]; exact hQ.r161
  have g250 : c₂.nreg 250 = bW := by rw [fr₂ 250 (by omega), hr₁ 250 (Or.inl (by omega))]; exact hB.r250
  obtain ⟨c₃, t₃, e₃, ht₃, h320, fr₃, hm₃, ho₃⟩ := wsum_exec (P := P) (n := n) (bW := bW) (w := w)
    hB.hW (by rw [hsumw]; exact htot _) c₂ hw₂ g140 g141 g161 g250
    (fun u hu => by rw [m₂ _ (by omega)]; exact hB.mW u hu)
  rw [hsumw] at h320
  have hw₃ := e₃.wb_right
  -- the state of the walk
  set Jf := CycleSearch.jv k c₂.nmem
  have hJ : ∀ F < k, F ≠ 0 → Jf F = IvalC (T := T) (cd := cd) (c₀ := c₀) wv hk F := hj₂
  set d := wdOf k A Tm (CycleSearch.pd k c₀.nmem) Jf V R w Lc (∑ v, wv v)
  let e : WL := ⟨n, vi T.root, bD, bU, L, bV, bS, bW, f, dep⟩
  have m₃ : ∀ a, a < 6 * k ∨ (7 * k ≤ a ∧ a < 10 * k) ∨ 11 * k ≤ a → c₃.nmem a = c₀.nmem a :=
    fun a ha => by rw [hm₃, m₂ a ha]
  have keepR : ∀ r, 27 ≤ r → r < 280 → c₃.nreg r = c₀.nreg r := fun r h1 h2 => by
    rw [fr₃ r (by omega) (by omega) (by omega) (by omega), fr₂ r h1, hr₁ r (Or.inl h2)]
  have hQ₃ : QFix n (vi T.root) bD bU L W f dep c₃ :=
    ⟨(keepR 140 (by omega) (by omega)).trans hQ.r140, (keepR 141 (by omega) (by omega)).trans hQ.r141,
      (keepR 161 (by omega) (by omega)).trans hQ.r161, (keepR 253 (by omega) (by omega)).trans hQ.r253,
      (keepR 254 (by omega) (by omega)).trans hQ.r254, (keepR 271 (by omega) (by omega)).trans hQ.r271,
      hQ.tree, fun j hj v hv => by
        rw [m₃ _ (Or.inr (Or.inr (by omega)))]; exact hQ.tab j hj v hv,
      fun v hv => by rw [m₃ _ (Or.inr (Or.inr (by omega)))]; exact hQ.mdep v hv,
      hQ.pow, hQ.hL, hQ.hU, hQ.hD⟩
  have hWS : WSm d e W c₃ :=
    { wb := hw₃
      regs := cregs_of hR₂ fun r hr => fr₃ r (by omega) (by omega) (by omega) (by omega)
      A_m := fun x (hx : x < 3 * k) => by rw [m₃ _ (Or.inl (by omega))]; exact hS.hold.1 x hx
      T_m := fun x (hx : x < 3 * k) => by
        show c₃.nmem (3 * k + x) = Tm x
        rw [m₃ _ (Or.inl (by omega))]; exact hS.hold.2.1 x hx
      pd_m := fun F (hF : F < k) => by
        show c₃.nmem (8 * k + F) = CycleSearch.pd k c₀.nmem F
        rw [m₃ _ (Or.inr (Or.inl (by omega)))]; rfl
      J_m := fun F hF _ => by rw [hm₃]; rfl
      V_m := fun x (hx : x < 3 * k) => by
        show c₃.nmem (bV + x) = V x
        rw [m₃ _ (Or.inr (Or.inr (by omega)))]; exact hB.mV x hx
      S_m := fun u (hu : u < n) => by
        show c₃.nmem (bS + u) = R u
        rw [m₃ _ (Or.inr (Or.inr (by omega)))]; exact hB.mS u hu
      W_m := fun u (hu : u < n) => by
        show c₃.nmem (bW + u) = w u
        rw [m₃ _ (Or.inr (Or.inr (by omega)))]; exact hB.mW u hu
      r162 := (keepR 162 (by omega) (by omega)).trans hB.r162
      r250 := (keepR 250 (by omega) (by omega)).trans hB.r250
      r252 := (keepR 252 (by omega) (by omega)).trans hB.r252
      r320 := h320
      qfix := hQ₃ }
  have hWA : WAm d e W :=
    { tri := hC.tri
      pdor := hC.pdor hk hS hall hM
      J_le := fun F (hF : F < k) hF0 => by
        show Jf F ≤ _
        rw [hJ F hF hF0]; exact sum_le_sum_of_subset (subset_univ _)
      V_lt := hB.V_lt
      lc := hLc
      cw_le := fun y (hy : y < 3 * k) hT => by
        rw [cwN_eq wv hC hk hV hf hR' hw hLc (CycleSearch.pd k c₀.nmem) (∑ v, wv v) hy hT
          (Jf := Jf)]
        exact sum_le_sum_of_subset (subset_univ _)
      hV := hB.hV
      hS := hB.hS
      hW := hB.hW
      hk := hWt }
  have hH := mwh_tree wv hC hk hV hf hR' hw hLc hS hall hJ hM hT3
  -- the start
  have hq1 : CycleSearch.qu k c₀.nmem 1 < k := hS.q_lt 1 (by omega)
  have hq10 : CycleSearch.qu k c₀.nmem 1 ≠ 0 := fun e' => by
    have := hS.q_inj 1 (by omega) 0 hS.q0.1 (by rw [e', hS.q0.2]); omega
  obtain ⟨-, hd0, hT0⟩ := hC.pd_spec hk hS hall hq1 hq10
  have hmq : c₃.nmem (9 * k + 1) = CycleSearch.qu k c₀.nmem 1 := by
    rw [m₃ _ (Or.inr (Or.inl (by omega)))]; rfl
  obtain ⟨c₄, t₄, e₄, ht₄, -, ho₄, hgood⟩ := mwalk_exec (P := P) (o := c₃.output) hWA hH c₃ hWS rfl
    (by rw [hmq]; exact hq1) (by rw [hmq]; exact hd0) (by rw [hmq]; exact hT0)
  obtain ⟨-, hlt, hT, h1, h2⟩ := hgood
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_,
    by rw [ho₄, ho₃, ho₂], fun a ha => by
      rw [e₄.nmem_of_st (by decide), m₃ a (Or.inr (Or.inr ha))], fun a ha => by
      rw [e₄.nmem_of_st (by decide), m₃ a (Or.inl (by omega))], ?_⟩
  · have a1 : (50 * L + 160) * (k + 1) = (50 * L + 160) * k + 50 * L + 160 := by ring
    have a2 : (75 * L + 125) * k + 62 * k + (50 * L + 160) * k = (125 * L + 347) * k := by ring
    change t₄ ≤ (50 * L + 160) * (k + 1) + 50 * L + 142 at ht₄
    omega
  · set y := c₄.nreg 353
    set δ := CycleSearch.Coded.dartN (cd := cd) hk y
    have e0 : (cd δ : ℕ) = y := CycleSearch.Coded.cd_dartN hk hlt
    have hnt : ¬ T.IsTree δ := (hC.T_cd δ).1 (by rw [e0]; exact hT)
    have hAy := hC.tri.A_lt y hlt
    have hTA : Tm (A y) = 0 := by rw [hC.tri.T_A y hlt]; exact hT
    have i1 := IvM_eq wv hC hk hV hf hR' hw hLc hS hall hJ hM hlt hT
    have i2 := IvM_eq wv hC hk hV hf hR' hw hLc hS hall hJ hM hAy hTA
    rw [hC.dartN_A hk hlt, SpTree.inC_α (T := T) hM hnt] at i2
    refine ⟨δ, e0, hnt, ?_, ?_⟩
    · rw [← i1]; exact h1
    · rw [← i2]; exact h2

end Bridge

end MillerProg

end PlanarSeparator
