module

public import PlanarFlow.Monge.FRProg

/-!
# FR-Dijkstra on the machine: the distances and the cost

The input of `frProg` as a graph (`frGraph`): the vertices `Fin N`, the dense distance graph on
the corners `0, …, b - 1` (`PlanarFlow.Monge.ddgPlus` with the identity on the corners), and the
explicit arcs `(tail, head, length)` (`exArcs`, the tail of the arc `e` the vertex `x` with
`off x ≤ e < off (x + 1)`). A run of the machine is a run of Dijkstra's algorithm with the
price function on this graph (`dijkRun_of_res`), whose correctness is
`PlanarFlow.Monge.DijkRun.gdist`.

* `frProg_dist`: **the run of `frProg` computes the distances from the root**
  (`PlanarFlow.Monge.GDist`) in the graph of the input (`frGraph`), for a price function feasible
  on it (`IsPot`), and a Monge (crossing) dense distance graph.
* `frCost_le`: the number of steps is at most `6000 b L ^ 2 + 150 (N + m) G + 150` with
  `L = ⌊log₂ b⌋ + 1`, `G = lg N = ⌊log₂ N⌋ + 1`: `O(b log² b + (N + m) log N)`;
  `frCost_le_fr`: at most `6300 (N G ^ 2 + m G)`, the form of the bound of FR-Dijkstra in the
  maximum-flow recursion (`PlanarFlow.BKMNW.SubCosts.Bounds`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

variable {P : Prm} {I : Input}

/-! ### The input as a graph -/

lemma Lay.N_pos (hL : Lay P) : 0 < P.N := by have := hL.b_pos; have := hL.bN; omega

/-- A vertex of the graph. -/
def fv (P : Prm) (hN : 0 < P.N) (y : ℕ) : Fin P.N := ⟨y % P.N, Nat.mod_lt _ hN⟩

/-- The tail of the explicit arc `e`. -/
noncomputable def tl (P : Prm) (e : ℕ) : ℕ := Nat.findGreatest (fun u => P.off u ≤ e) (P.N - 1)

/-- The explicit arcs: tail, head, length. -/
noncomputable def exArcs (P : Prm) (hN : 0 < P.N) : List (Fin P.N × Fin P.N × ℤ) :=
  List.ofFn fun e : Fin P.m => (fv P hN (tl P e), fv P hN (P.dst e), P.len e)

/-- **The graph of the input**: the dense distance graph on the corners and the explicit arcs. -/
noncomputable def frGraph (P : Prm) (hN : 0 < P.N) :
    Digraph (Fin P.N) (Arc P.b ⊕ Fin (exArcs P hN).length) :=
  ddgPlus (fv P hN) P.b P.D (exArcs P hN)

lemma fv_val {hN : 0 < P.N} {y : ℕ} (hy : y < P.N) : (fv P hN y : ℕ) = y := Nat.mod_eq_of_lt hy

lemma fv_inj {hN : 0 < P.N} {y z : ℕ} (hy : y < P.N) (hz : z < P.N) (h : fv P hN y = fv P hN z) :
    y = z := by
  have := congrArg Fin.val h; rwa [fv_val hy, fv_val hz] at this

/-- The tail of an explicit arc. -/
lemma tl_spec (hL : Lay P) (h0 : P.off 0 = 0) {e : ℕ} (he : e < P.m) :
    tl P e < P.N ∧ P.off (tl P e) ≤ e ∧ e < P.off (tl P e + 1) := by
  have hN := hL.N_pos
  have h1 : tl P e ≤ P.N - 1 := Nat.findGreatest_le _
  have h2 : P.off (tl P e) ≤ e := Nat.findGreatest_spec (P := fun u => P.off u ≤ e)
    (Nat.zero_le _) (by rw [h0]; omega)
  refine ⟨by omega, h2, ?_⟩
  by_contra hc
  rcases Nat.lt_or_ge (tl P e + 1) P.N with h3 | h3
  · exact Nat.findGreatest_is_greatest (P := fun u => P.off u ≤ e) (n := P.N - 1)
      (k := tl P e + 1) (by unfold tl; omega) (by omega) (show P.off (tl P e + 1) ≤ e by omega)
  · rw [show tl P e + 1 = P.N by omega, hL.off_last] at hc; omega

lemma tl_eq (hL : Lay P) {u e : ℕ} (hu : u < P.N) (h1 : P.off u ≤ e) (h2 : e < P.off (u + 1)) :
    tl P e = u := by
  unfold tl
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun _ => h1, fun n' hn' hn'N h => ?_⟩
  have := off_mono' hL (u + 1) n' (by omega) (by omega)
  omega

lemma exArcs_get (hN : 0 < P.N) (e : Fin (exArcs P hN).length) :
    (exArcs P hN).get e = (fv P hN (tl P e), fv P hN (P.dst e), P.len e) := by
  exact List.get_ofFn _ e

lemma exArcs_length (hN : 0 < P.N) : (exArcs P hN).length = P.m := by unfold exArcs; simp

/-- **An arc of the machine is an arc of the graph.** -/
lemma arc_of_isArc (hL : Lay P) {u y : ℕ} {ℓ : ℤ} (hu : u < P.N)
    (h : IsArc P u y ℓ) :
    ∃ a, (frGraph P hL.N_pos).src a = fv P hL.N_pos u ∧
      (frGraph P hL.N_pos).dst a = fv P hL.N_pos y ∧
      (frGraph P hL.N_pos).len a = ℓ := by
  rcases h with ⟨hub, hyb, hne, rfl⟩ | ⟨-, e, h1, h2, rfl, rfl⟩
  · refine ⟨.inl ⟨(⟨u, hub⟩, ⟨y, hyb⟩), fun h => hne (congrArg Fin.val h)⟩, rfl, rfl, rfl⟩
  · have hm : e < P.m := by
      have := off_mono' hL (u + 1) P.N (by omega) le_rfl; rw [hL.off_last] at this; omega
    refine ⟨.inr ⟨e, by rw [exArcs_length]; exact hm⟩, ?_, ?_, ?_⟩
    · show ((exArcs P hL.N_pos).get _).1 = _
      rw [exArcs_get]; simp only; rw [tl_eq hL hu h1 h2]
    · show ((exArcs P hL.N_pos).get _).2.1 = _
      rw [exArcs_get]
    · show ((exArcs P hL.N_pos).get _).2.2 = _
      rw [exArcs_get]

/-- **An arc of the graph is an arc of the machine.** -/
lemma isArc_of_arc (hL : Lay P) (h0 : P.off 0 = 0) {u : ℕ} (hu : u < P.N)
    (a : Arc P.b ⊕ Fin (exArcs P hL.N_pos).length)
    (h : (frGraph P hL.N_pos).src a = fv P hL.N_pos u) :
    IsArc P u ((frGraph P hL.N_pos).dst a) ((frGraph P hL.N_pos).len a) := by
  have hbN := hL.bN
  rcases a with ⟨⟨i, j⟩, hne⟩ | e
  · change fv P hL.N_pos i = fv P hL.N_pos u at h
    have hi := fv_inj (by omega) hu h
    subst hi
    have hy : ((frGraph P hL.N_pos).dst (.inl ⟨(i, j), hne⟩) : ℕ) = j :=
      fv_val (hN := hL.N_pos) (by omega)
    rw [hy]
    exact Or.inl ⟨i.2, j.2, fun h' => hne (Fin.ext h'), rfl⟩
  · have he : (e : ℕ) < P.m := lt_of_lt_of_eq e.2 (exArcs_length _)
    obtain ⟨t1, t2, t3⟩ := tl_spec hL h0 he
    change ((exArcs P hL.N_pos).get e).1 = _ at h
    rw [exArcs_get] at h
    have hut := fv_inj t1 hu h
    have hdst : P.dst e < P.N := hL.dst_lt e he
    refine Or.inr ⟨hu, e, by rw [← hut]; exact t2, by rw [← hut]; exact t3, ?_, ?_⟩
    · change ((((exArcs P hL.N_pos).get e).2.1 : Fin P.N) : ℕ) = P.dst e
      rw [exArcs_get]; exact fv_val (hN := hL.N_pos) hdst
    · change ((exArcs P hL.N_pos).get e).2.2 = _
      rw [exArcs_get]

/-- **The result of the machine is a run of Dijkstra's algorithm on the graph.** -/
theorem dijkRun_of_res (hL : Lay P) (h0 : P.off 0 = 0) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ}
    {nm : ℕ → ℕ} {rm : ℕ → ℝ} (h : FRes P K v d nm rm) :
    DijkRun (frGraph P hL.N_pos) (fun y => P.p y) (fv P hL.N_pos P.r) K
      (fun i => fv P hL.N_pos (v i)) d := by
  obtain ⟨hR, hK, hvl, hcl, -, -⟩ := h
  have hN := hL.N_pos
  refine ⟨hK, show fv P hN (v 0) = _ by rw [hR.root hK], hR.root_d hK, fun i j hi hj e => ?_,
    fun k hk0 hk => ?_, fun k hk i hik a ha hy => ?_, fun i hi a ha => ?_⟩
  · exact hR.inj i j hi hj (fv_inj (hvl i hi) (hvl j hj) e)
  · obtain ⟨i, hi, ℓ, harc, he⟩ := hR.parent k hk0 hk
    obtain ⟨a, h1, h2, h3⟩ := arc_of_isArc hL (hvl i (by omega)) harc
    exact ⟨i, hi, a, h1, h2, by rw [h3, he]⟩
  · have harc := isArc_of_arc hL h0 (hvl i (by omega)) a ha
    have := hR.least k hk i hik _ _ harc fun j hj e => hy j hj (by
      apply Fin.ext; rw [fv_val (hvl j (by omega))]; exact e)
    show (d k : ℤ) - P.p (fv P hN (v k) : ℕ) ≤ _
    rw [fv_val (hvl k hk)]; exact this
  · have harc := isArc_of_arc hL h0 (hvl i hi) a ha
    obtain ⟨j, hj, e⟩ := hcl i hi _ _ harc
    exact ⟨j, hj, Fin.ext (by rw [fv_val (hvl j hj)]; exact e)⟩

/-! ### The distances -/

/-- A price function feasible on the graph of the input is feasible on the machine's arcs. -/
lemma feas_of_isPot (hL : Lay P) (hp : (frGraph P hL.N_pos).IsPot (fun y => P.p y)) :
    Feas P := by
  intro u y ℓ ha
  have hu : u < P.N := by
    rcases ha with ⟨hu, -⟩ | ⟨hu, -⟩
    · have := hL.bN; omega
    · exact hu
  have hy := ha.dst_lt hL
  obtain ⟨a, h1, h2, h3⟩ := arc_of_isArc hL hu ha
  have := hp a
  simp only at this
  rw [h1, h2, h3, fv_val hu, fv_val hy] at this
  exact this

/-- **The run of `frProg` computes the distances from the root** in the graph of the input:
the settled flags mark exactly the reachable vertices, and the distances in the memory are the
least lengths of walks. -/
theorem frProg_dist (hL : Lay P) (h0 : P.off 0 = 0) (hDc : Crossing P.b P.D)
    (hA : Nonempty (Arc P.b ⊕ Fin (exArcs P hL.N_pos).length))
    (hp : (frGraph P hL.N_pos).IsPot (fun y => P.p y)) (c : Config) (hc : WordsBounded P.W c)
    (hin : Inp P c) (hDa : Data P c) :
    ∃ c' k, Exec I P.W frProg c c' k ∧ k ≤ frCost P ∧ Data P c' ∧ c'.output = c.output ∧
      ∃ δ : Fin P.N → Option ℤ, GDist (frGraph P hL.N_pos) (fv P hL.N_pos P.r) δ ∧
        ∀ y : Fin P.N, (c'.nmem (P.sb + y) = 1 ↔ δ y ≠ none) ∧
          ∀ ℓ, δ y = some ℓ → c'.rmem (P.db + y) = ℓ := by
  obtain ⟨c', k, e, hk, hDa', hO, -, -, K, v, d, hres⟩ :=
    frProg_exec (I := I) hL hDc (feas_of_isPot hL hp) c hc hin hDa
  have hrun := dijkRun_of_res hL h0 hres
  obtain ⟨-, -, hvl, -, hsf, hdist⟩ := hres
  have hvy : ∀ (y : Fin P.N) i, i < K → (fv P hL.N_pos (v i) = y ↔ v i = y) := fun y i hi =>
    ⟨fun h => by rw [← h, fv_val (hvl i hi)], fun h => Fin.ext (by rw [fv_val (hvl i hi)]; exact h)⟩
  refine ⟨c', k, e, hk, hDa', hO, _, hrun.gdist hp, fun y => ⟨?_, fun ℓ hℓ => ?_⟩⟩
  · rw [hsf y y.2]
    split_ifs with h
    · simp only [ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
      obtain ⟨i, hi, hv⟩ := h
      exact ⟨i, hi, (hvy y i hi).1 hv⟩
    · simp only [ne_eq, not_true_eq_false, iff_false]
      rintro ⟨i, hi, hv⟩
      exact h ⟨i, hi, (hvy y i hi).2 hv⟩
  · split_ifs at hℓ with hy
    obtain ⟨hi, hv⟩ := Classical.choose_spec hy
    rw [← Option.some_inj.1 hℓ, ← hdist _ hi, (hvy y _ hi).1 hv]

/-! ### The cost in closed form -/

lemma sum_off (hL : Lay P) : ∀ n ≤ P.N,
    ∑ y ∈ Finset.range n, (P.off (y + 1) - P.off y) = P.off n - P.off 0 := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [Finset.sum_range_succ, ih (by omega)]
    have := off_mono' hL 0 n (by omega) (by omega)
    have := hL.off_mono n (by omega)
    omega

lemma sum_corner (A : ℕ) :
    ∀ n, ∑ y ∈ Finset.range n, (if y < P.b then A else 2) ≤ P.b * A + 2 * n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    split_ifs with h
    · have : n * A + A ≤ P.b * A := by
        have := Nat.mul_le_mul_right A (show n + 1 ≤ P.b by omega)
        rwa [Nat.add_mul, Nat.one_mul] at this
      -- the sum over the first `n` vertices, all corners
      have hs : ∑ y ∈ Finset.range n, (if y < P.b then A else 2) = ∑ y ∈ Finset.range n, A :=
        Finset.sum_congr rfl fun y hy => by
          have := Finset.mem_range.1 hy; simp only [show y < P.b by omega, ↓reduceIte]
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hs
      omega
    · omega

lemma Lv_pos : 1 ≤ P.Lv := by unfold Prm.Lv; omega

/-- `TB ≤ 2 Lv`: `b Lv ≤ b ^ 2 < 4 ^ Lv`. -/
lemma TB_le (hL : Lay P) : P.TB ≤ 2 * P.Lv := by
  obtain ⟨hLv, -, -⟩ := lay_gx hL
  have hb := hL.b_pos
  have h1 : P.b < 2 ^ P.Lv := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : P.b * P.Lv < 2 ^ (2 * P.Lv) := by
    rw [two_mul, pow_add]
    calc P.b * P.Lv ≤ P.b * P.b := Nat.mul_le_mul_left _ hLv
      _ < 2 ^ P.Lv * 2 ^ P.Lv := Nat.mul_lt_mul'' h1 h1
  have := Nat.log_lt_of_lt_pow (b := 2) (Nat.mul_ne_zero (by omega)
    (by have := Lv_pos (P := P); omega)) h2
  unfold Prm.TB; omega

/-- The levels of the half blocks: `2 ^ t ≤ b` for `t < Lv`. -/
lemma pow_le_b (hL : Lay P) {t : ℕ} (ht : t < P.Lv) : 2 ^ t ≤ P.b := by
  unfold Prm.Lv at ht
  exact Nat.pow_le_of_le_log (by have := hL.b_pos; omega) (by omega)

/-- **The initialization of a level** costs `O(b Lv)`. -/
lemma levC_le (hL : Lay P) {t : ℕ} (ht : t < P.Lv) : levC P t ≤ 984 * P.b * P.Lv + 12 := by
  have hb := hL.b_pos
  have h2 := pow_le_b hL ht
  have hL1 := Lv_pos (P := P)
  have hd : P.b / 2 ^ t * 2 ^ t ≤ P.b := Nat.div_mul_le_self _ _
  have hd' : P.b / 2 ^ t ≤ P.b := Nat.div_le_self _ _
  unfold levC bInitC
  have e : (P.b / 2 ^ t + 1) * (83 * 2 ^ t * (2 * t + 2) + 62 * 2 ^ t + 4 * t + 90 + 4) =
      (P.b / 2 ^ t * 2 ^ t + 2 ^ t) * (166 * t + 228) + (P.b / 2 ^ t + 1) * (4 * t + 94) := by
    ring
  rw [e]
  have a1 : (P.b / 2 ^ t * 2 ^ t + 2 ^ t) * (166 * t + 228) ≤ (2 * P.b) * (394 * P.Lv) :=
    Nat.mul_le_mul (by omega) (by omega)
  have a2 : (P.b / 2 ^ t + 1) * (4 * t + 94) ≤ (2 * P.b) * (98 * P.Lv) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

lemma sum_levC_le (hL : Lay P) :
    ∑ t ∈ Finset.range P.Lv, levC P t ≤ 984 * P.b * P.Lv ^ 2 + 12 * P.Lv := by
  have := Finset.sum_le_card_nsmul (Finset.range P.Lv) (levC P) (984 * P.b * P.Lv + 12)
    fun t ht => levC_le hL (Finset.mem_range.1 ht)
  rw [Finset.card_range, smul_eq_mul] at this
  nlinarith

/-- The costs of the rounds settling the vertices. -/
theorem sum_vc_le (hL : Lay P) : ∑ y ∈ Finset.range P.N, vc P y ≤
    P.N * (25 * lg P.N + 61) + P.b * (P.Lv * lvC P + 7) + P.m * (decCost P.N + 15) := by
  have e : ∀ y, vc P y = (25 * lg P.N + 59) + (if y < P.b then P.Lv * lvC P + 7 else 2) +
      (P.off (y + 1) - P.off y) * (decCost P.N + 15) := fun y => by
    unfold vc settleCost; omega
  rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.sum_mul, sum_off hL P.N le_rfl,
    hL.off_last]
  have h1 := sum_corner (P := P) (P.Lv * lvC P + 7) P.N
  have h2 : (P.m - P.off 0) * (decCost P.N + 15) ≤ P.m * (decCost P.N + 15) :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have h3 : P.N * (25 * lg P.N + 61) = P.N * (25 * lg P.N + 59) + 2 * P.N := by ring
  omega

/-- **The cost of FR-Dijkstra with the bipartite Monge heaps in closed form**: with
`L = ⌊log₂ b⌋ + 1` and `G = lg N = ⌊log₂ N⌋ + 1`, at most `6000 b L ^ 2 + 150 (N + m) G + 150`
steps: `O(b log² b + (N + m) log N)`. -/
theorem frCost_le (hL : Lay P) : frCost P ≤
    6000 * P.b * P.Lv ^ 2 + 150 * (P.N + P.m) * lg P.N + 150 := by
  have hs := sum_vc_le hL
  have hl := sum_levC_le hL
  have hTB := TB_le hL
  have hTB2 := two_pow_TB_le hL
  have hb := hL.b_pos
  have hN := hL.N_pos
  have hL1 := Lv_pos (P := P)
  have hG1 : 1 ≤ lg P.N := by rw [lg_pos hN]; omega
  unfold frCost
  unfold lvC Cx actCost extCost LD rmqCost decCost at *
  generalize P.Lv = L at *
  generalize lg P.N = G at *
  generalize P.TB = T at *
  generalize 2 ^ T = S at *
  generalize P.b = b at *
  generalize P.N = N at *
  generalize P.m = m at *
  have a1 : b * L ≤ b * L ^ 2 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
  have a4 : b ≤ b * L ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have a5 : L ≤ b * L ^ 2 := le_trans (Nat.le_self_pow (by norm_num) _) (Nat.le_mul_of_pos_left _
      hb)
  have a6 : N ≤ N * G := Nat.le_mul_of_pos_right _ hG1
  have a7 : G ≤ N * G := Nat.le_mul_of_pos_left _ hN
  have a8 : m ≤ m * G := Nat.le_mul_of_pos_right _ hG1
  have a9 : b * (L * (752 * L + 1110 + 49 * T)) ≤ b * (L * (850 * L + 1110)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  have a10 : (2 * (84 * L + 110) + 147 * L + 70 + (70 * L + 140) + 49 * T + 100) * (2 * b * L) ≤
      (483 * L + 530) * (2 * b * L) := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- **The cost of FR-Dijkstra in the form of the maximum-flow recursion**: with
`G = lg N = ⌊log₂ N⌋ + 1`, at most `6300 (N G ^ 2 + m G)` steps. -/
theorem frCost_le_fr (hL : Lay P) : frCost P ≤ 6300 * (P.N * lg P.N ^ 2 + P.m * lg P.N) := by
  have h := frCost_le hL
  have hb := hL.b_pos
  have hbN := hL.bN
  have hN := hL.N_pos
  have hLG : P.Lv ≤ lg P.N := by
    rw [lg_eq_log hN]; unfold Prm.Lv; have := Nat.log_mono_right (b := 2) hbN; omega
  have hG1 : 1 ≤ lg P.N := by rw [lg_pos hN]; omega
  have a1 : P.b * P.Lv ^ 2 ≤ P.N * lg P.N ^ 2 :=
    Nat.mul_le_mul hbN (Nat.pow_le_pow_left hLG 2)
  have a2 : P.N * lg P.N ≤ P.N * lg P.N ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
  have a3 : 1 ≤ P.N * lg P.N ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
  nlinarith

end FR

end Monge

end PlanarFlow
