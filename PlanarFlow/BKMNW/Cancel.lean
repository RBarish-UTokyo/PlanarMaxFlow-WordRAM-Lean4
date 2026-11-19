module

public import PlanarFlow.BKMNW.Algorithm
public import PlanarFlow.BKMNW.MongeBridge

/-!
# Cancelling the flow cycles of a plane flow

The push-back of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J. Comput. 46(4),
2017, Appendix C) first makes the flow acyclic, with the technique of Kaplan and Nussbaum: on a
plane map, a flow `g` and a face potential `φ` give the flow `g + cob φ` with the same net
outflows, and the darts where it is positive are among those where `g` is positive (it is
*conformal* to `g`) exactly when `φ` is a feasible potential of the dual graph with the lengths
`max 0 (- g d)` (`conf_of_pot`).

* `cpass`: the potential is the distance from a root face in that dual graph, computed by
  FR-Dijkstra used as Dijkstra's algorithm (no dense distance graph, every dual arc explicit,
  `isDist_dualDijkstra`). The distances are the **largest** feasible potential vanishing at the
  root (`le_dist_scaled`), so no circulation can still be subtracted on the positive darts
  (`pass_extremal`).
* `cancel`: one pass on `g`, then one pass on the reversed flow. A positive closed walk of the
  result is a circulation (`circ`), the coboundary of a face potential `ψ` (plane maps,
  `CombMap.exists_int_potential`). The first pass gives `ψ ≥ 0`, the second `ψ ≤ 0`, so the
  circulation vanishes, which it does not: **the result is acyclic** (`cancel_spec`).

The article cancels the cycles in linear time with linear-time shortest paths for nonnegative
lengths in plane graphs; here both passes use FR-Dijkstra (`FRSpec`), the shortest-path
subroutine of the specifications, at a cost of `O(m log² m)` (`PlanarFlow/BKMNW/Cost.lean`).

Finally `rk g v`, the height of `v` (the number of darts of a longest walk of positive darts
ending at `v`), is a topological rank of an acyclic flow: it increases along every positive dart
(`rk_lt`). It is computed in linear time along a topological order of the acyclic flow.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-! ### Conformal flows -/

/-- `g'` is **conformal** to `g`: on every dart where `g` is nonnegative, `g'` lies between `0`
and `g`. -/
def Conf (g g' : D → ℤ) : Prop := ∀ d, 0 ≤ g d → 0 ≤ g' d ∧ g' d ≤ g d

lemma Conf.refl (g : D → ℤ) : Conf g g := fun _ h => ⟨h, le_rfl⟩

lemma Conf.trans {g g' g'' : D → ℤ} (h : Conf g g') (h' : Conf g' g'') : Conf g g'' :=
  fun d hd => ⟨(h' d (h d hd).1).1, (h' d (h d hd).1).2.trans (h d hd).2⟩

/-- A dart positive for a conformal flow is positive for the original one. -/
lemma Conf.pos {g g' : D → ℤ} (hg : M.IsAntisymm g) (hg' : M.IsAntisymm g') (h : Conf g g')
    {d : D} (hd : 0 < g' d) : 0 < g d := by
  by_contra hn
  have := (h (M.rev d) (by rw [hg d]; omega)).1
  rw [hg' d] at this; omega

lemma Conf.neg {g g' : D → ℤ} (hg : M.IsAntisymm g) (hg' : M.IsAntisymm g') (h : Conf g g') :
    Conf (-g) (-g') := by
  intro d hd
  simp only [Pi.neg_apply] at hd ⊢
  by_cases h0 : g d = 0
  · have h1 := h d (by omega)
    have h2 := h (M.rev d) (by rw [hg d]; omega)
    rw [hg' d, hg d] at h2; omega
  · have h2 := h (M.rev d) (by rw [hg d]; omega)
    rw [hg' d, hg d] at h2; omega

/-- A conformal antisymmetric function of a pseudoflow is a pseudoflow, for nonnegative
capacities. -/
lemma IsPseudo.of_conf {c g g' : D → ℤ} (hc : ∀ d, 0 ≤ c d) (hg : IsPseudo M c g)
    (hg' : M.IsAntisymm g') (h : Conf g g') : IsPseudo M c g' := by
  refine ⟨hg', fun d => ?_⟩
  by_cases hd : 0 ≤ g d
  · exact (h d hd).2.trans (hg.le_cap d)
  · have := (h (M.rev d) (by rw [hg.antisymm d]; omega)).1
    rw [hg' d] at this; have := hc d; omega

/-! ### The lengths of a cancellation -/

/-- The dual lengths of the cancellation for `g`. -/
def canLen (g : D → ℤ) (d : D) : ℤ := max 0 (- g d)

lemma canLen_nonneg (g : D → ℤ) (d : D) : 0 ≤ canLen g d := le_max_left _ _

/-- **A feasible potential for `canLen g` gives a conformal flow.** -/
lemma conf_of_pot {g : D → ℤ} (hg : M.IsAntisymm g) {φ : F → ℤ}
    (hφ : M.IsPotential (canLen g) φ) : Conf g (g + M.cob φ) := by
  intro d hd
  have h1 := hφ d
  have h2 := hφ (M.rev d)
  simp only [canLen] at h1 h2
  rw [M.cob_antisymm φ d, hg d, neg_neg, max_eq_right hd] at h2
  rw [max_eq_left (by linarith : -g d ≤ 0)] at h1
  simp only [Pi.add_apply]
  constructor <;> linarith

/-! ### Dijkstra in the dual by FR-Dijkstra -/

variable (M) in
/-- The dual arcs, all explicit. -/
noncomputable def dualArcs (ℓ : D → ℤ) : List (F × F × ℤ) :=
  explicitArcs (M.dualGraph ℓ) (univ : Finset D).toList

/-- The empty dense distance graph. -/
def emptyDDG : DDG F := ⟨∅, fun _ _ => none⟩

variable (M) in
/-- **Distances in the dual graph**, by FR-Dijkstra with no dense distance graph. -/
noncomputable def dualDijkstra (fr : FRFun F) (ℓ : D → ℤ) (r : F) : F → Option ℤ :=
  fr emptyDDG (dualArcs M ℓ) r 0

lemma arcsIn_dual_union (ℓ : D → ℤ) :
    ArcsIn (M.dualGraph ℓ) ((emptyDDG (F := F)).union (dualArcs M ℓ)) := by
  intro d
  obtain ⟨i, hi⟩ := List.get_of_mem (Finset.mem_toList.2 (mem_univ d))
  refine ⟨.inr ⟨i.1, by simpa [dualArcs, length_explicitArcs] using i.2⟩, ?_, ?_, ?_⟩ <;>
  · simp only [DDG.union_src_inr, DDG.union_dst_inr, DDG.union_len_inr, dualArcs,
      explicitArcs_getElem]
    have : (univ : Finset D).toList[i.1] = d := by simpa using hi
    simp [this, dualGraph]

lemma arcsIn_union_dual (ℓ : D → ℤ) :
    ArcsIn ((emptyDDG (F := F)).union (dualArcs M ℓ)) (M.dualGraph ℓ) := by
  rintro (⟨p, hp, -⟩ | i)
  · simp [emptyDDG] at hp
  · refine ⟨(univ : Finset D).toList[i.1]'(by
      simpa [dualArcs, length_explicitArcs] using i.2), ?_, ?_, ?_⟩ <;>
      simp only [DDG.union, dualArcs, explicitArcs, List.get_eq_getElem,
        List.getElem_map] <;> rfl

/-- **FR-Dijkstra used as Dijkstra** gives the distances in the dual graph with nonnegative
lengths. -/
theorem isDist_dualDijkstra {fr : FRFun F} (hfr : FRSpec fr) {ℓ : D → ℤ} (hℓ : ∀ d, 0 ≤ ℓ d)
    (r : F) : IsDist (M.dualGraph ℓ) r (dualDijkstra M fr ℓ r) := by
  have hpot : ((emptyDDG (F := F)).union (dualArcs M ℓ)).IsPot 0 := by
    rintro (⟨p, hp, -⟩ | i)
    · simp [emptyDDG] at hp
    · simp only [Pi.zero_apply, zero_add, DDG.union, dualArcs, explicitArcs,
        List.get_eq_getElem, List.getElem_map]
      exact hℓ _
  exact isDist_of_arcsIn (arcsIn_union_dual ℓ) (arcsIn_dual_union ℓ)
    (hfr emptyDDG (dualArcs M ℓ) r 0 hpot)

/-- Every face is reachable in the dual graph of a plane map. -/
lemma dual_reach_all (hM : M.IsPlane) (ℓ : D → ℤ) (r y : F) :
    ∃ l, IsWalk (M.dualGraph ℓ) r l y := by
  induction hM.dualConn r y with
  | refl => exact ⟨[], rfl⟩
  | @tail a b _ hab ih =>
    obtain ⟨l, hl⟩ := ih
    obtain ⟨d, rfl, rfl⟩ := hab
    exact ⟨l ++ [d], hl.append (isWalk_singleton.2 ⟨rfl, rfl⟩)⟩

/-- Distances are defined everywhere on a plane map. -/
lemma dist_ne_none (hM : M.IsPlane) {ℓ : D → ℤ} {r : F} {δ : F → Option ℤ}
    (h : IsDist (M.dualGraph ℓ) r δ) (y : F) : δ y ≠ none := by
  intro hy
  obtain ⟨l, hl⟩ := dual_reach_all hM ℓ r y
  exact h.none y hy l hl

/-- **The distances are the largest feasible potential**, here in a scaled form: a potential
feasible for the lengths `N ℓ` grows from the root by at most `N` times the distance. -/
lemma le_dist_scaled {X A : Type*} {G : Digraph X A} {r : X} {δ : X → Option ℤ}
    (h : IsDist G r δ) (hreach : ∀ y, δ y ≠ none) {N : ℤ} {q : X → ℤ}
    (hq : ∀ a, q (G.dst a) ≤ q (G.src a) + N * G.len a) (y : X) :
    q y - q r ≤ N * (δ y).getD 0 := by
  obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 (hreach y)
  obtain ⟨l, hl, hlen⟩ := h.some_walk y ℓ hℓ
  let G' : Digraph X A := ⟨G.src, G.dst, fun a => N * G.len a⟩
  have hw' : ∀ (x : X) (l : List A), IsWalk G x l y → IsWalk G' x l y := by
    intro x l
    induction l generalizing x with
    | nil => exact id
    | cons a l ih => exact fun h => ⟨h.1, ih _ h.2⟩
  have := (hw' r l hl).le_wlen (G := G') hq
  have e : ∀ l : List A, wlen G' l = N * wlen G l := by
    intro l
    induction l with
    | nil => simp [wlen]
    | cons a l ih =>
      rw [wlen_cons, wlen_cons, ih, mul_add]
  rw [hℓ, Option.getD_some, ← hlen, ← e]; exact this

/-! ### One pass -/

variable (M) in
/-- **One pass of the cancellation**: add the coboundary of the distances from `r` for the lengths
`canLen g`. -/
noncomputable def cpass (fr : FRFun F) (r : F) (g : D → ℤ) : D → ℤ :=
  g + M.cob fun y => (dualDijkstra M fr (canLen g) r y).getD 0

lemma cpass_pot (hM : M.IsPlane) {fr : FRFun F} (hfr : FRSpec fr) (r : F) (g : D → ℤ) :
    M.IsPotential (canLen g) fun y => (dualDijkstra M fr (canLen g) r y).getD 0 := by
  rw [isPotential_iff_isPot]
  exact (isDist_dualDijkstra hfr (canLen_nonneg g) r).isPot
    (dist_ne_none hM (isDist_dualDijkstra hfr (canLen_nonneg g) r))

lemma cpass_antisymm {fr : FRFun F} {r : F} {g : D → ℤ} (hg : M.IsAntisymm g) :
    M.IsAntisymm (cpass M fr r g) := fun d => by
  simp only [cpass, Pi.add_apply, hg d, M.cob_antisymm _ d]; ring

lemma cpass_conf (hM : M.IsPlane) {fr : FRFun F} (hfr : FRSpec fr) (r : F) {g : D → ℤ}
    (hg : M.IsAntisymm g) : Conf g (cpass M fr r g) :=
  conf_of_pot hg (cpass_pot hM hfr r g)

lemma div_cpass {fr : FRFun F} {r : F} (g : D → ℤ) (v : V) :
    M.div (cpass M fr r g) v = M.div g v := by
  simp only [cpass]; rw [div_add', show M.div (M.cob _) v = 0 from M.div_cob _ v, add_zero]

/-- **The extremality of one pass**: a circulation `cob ψ` (with `ψ` vanishing at the root) that
could still be subtracted from the result, keeping it conformal, has `ψ ≥ 0`. The hypothesis on
the circulation: where it is negative, the result is positive on the reversed dart, and it is at
least `-N`. -/
theorem pass_extremal (hM : M.IsPlane) {fr : FRFun F} (hfr : FRSpec fr) (r : F) {g : D → ℤ}
    (hg : M.IsAntisymm g) {ψ : F → ℤ} (hψr : ψ r = 0) {N : ℤ} (hN : 0 ≤ N)
    (hκ : ∀ d, M.cob ψ d < 0 → 0 < cpass M fr r g (M.rev d) ∧ - M.cob ψ d ≤ N) (y : F) :
    0 ≤ ψ y := by
  have hδ := isDist_dualDijkstra (M := M) hfr (canLen_nonneg g) r
  have hpot := cpass_pot hM hfr r g
  have hφr : (dualDijkstra M fr (canLen g) r r).getD 0 = 0 := by
    rw [hδ.self (p := 0) (fun d => by simp [dualGraph, canLen_nonneg])]; rfl
  have hineq : ∀ d, N * M.cob (fun y => (dualDijkstra M fr (canLen g) r y).getD 0) d -
      M.cob ψ d ≤ N * canLen g d := by
    intro d
    have h1 := hpot d
    by_cases hneg : M.cob ψ d < 0
    · obtain ⟨hpos, hle⟩ := hκ d hneg
      simp only [cpass, Pi.add_apply] at hpos
      rw [hg d, M.cob_antisymm _ d] at hpos
      have hL : -g d ≤ canLen g d := le_max_right _ _
      nlinarith
    · push Not at hneg; nlinarith
  have key := le_dist_scaled hδ (dist_ne_none hM hδ) (N := N)
    (q := fun y => N * (dualDijkstra M fr (canLen g) r y).getD 0 - ψ y)
    (fun d => by have := hineq d; simp only [cob] at this; simp only [dualGraph]; linarith) y
  simp only [hφr, hψr] at key
  linarith

/-! ### Closed walks of positive darts -/

variable (M) in
/-- The circulation of a list of darts: each dart counted positively, its reverse negatively. -/
def circ (ds : List D) (e : D) : ℤ := (ds.count e : ℤ) - ds.count (M.rev e)

lemma circ_antisymm (ds : List D) : M.IsAntisymm (circ M ds) := fun e => by
  simp only [circ, M.rev_rev]; ring

lemma circ_single (d : D) : circ M [d] = Pi.single d 1 - Pi.single (M.rev d) 1 := by
  funext e
  simp only [circ, List.count_singleton, Pi.sub_apply, Pi.single_apply, beq_iff_eq]
  by_cases h1 : e = d
  · subst h1; simp [(M.rev_ne e).symm]
  · by_cases h2 : e = M.rev d
    · subst h2; simp [M.rev_rev, M.rev_ne d, (M.rev_ne d).symm]
    · have : M.rev e ≠ d := fun h => h2 (by rw [← h, M.rev_rev])
      simp [h1, h2, Ne.symm this, Ne.symm h1]

lemma circ_append (l₁ l₂ : List D) : circ M (l₁ ++ l₂) = circ M l₁ + circ M l₂ := by
  funext e; simp only [circ, List.count_append, Pi.add_apply]; push_cast; ring

variable (M) in
/-- A dart from `u` to `v` positive for `g`. -/
def Pos (g : D → ℤ) (u v : V) : Prop := ∃ d, M.tail d = u ∧ M.head d = v ∧ 0 < g d

/-- A walk of positive darts gives a list of positive darts whose circulation has net outflow
`1` at the start and `-1` at the end. -/
lemma exists_circ_of_transGen {g : D → ℤ} {u v : V} (h : Relation.TransGen (Pos M g) u v) :
    ∃ ds : List D, ds ≠ [] ∧ (∀ d ∈ ds, 0 < g d) ∧
      ∀ w, M.div (circ M ds) w = (if u = w then 1 else 0) - (if v = w then 1 else 0) := by
  induction h with
  | single h =>
    obtain ⟨d, rfl, rfl, hd⟩ := h
    exact ⟨[d], by simp, by simpa using hd, fun w => by rw [circ_single, div_dart]⟩
  | tail _ h ih =>
    obtain ⟨ds, hne, hpos, hdiv⟩ := ih
    obtain ⟨d, hd1, rfl, hd⟩ := h
    refine ⟨ds ++ [d], by simp, fun e he => ?_, fun w => ?_⟩
    · rcases List.mem_append.1 he with he | he
      · exact hpos e he
      · rw [List.mem_singleton.1 he]; exact hd
    · rw [circ_append, div_add', hdiv, circ_single, div_dart, hd1]; ring

lemma circ_neg_mem {ds : List D} {e : D} (h : circ M ds e < 0) : M.rev e ∈ ds := by
  by_contra hn
  simp only [circ, List.count_eq_zero_of_not_mem hn] at h
  omega

lemma neg_circ_le (ds : List D) (e : D) : - circ M ds e ≤ ds.length := by
  simp only [circ]
  have := List.count_le_length (a := M.rev e) (l := ds)
  omega

lemma circ_le (ds : List D) (e : D) : circ M ds e ≤ ds.length := by
  simp only [circ]
  have := List.count_le_length (a := e) (l := ds)
  omega

/-! ### The cancellation -/

open Classical in
variable (M) in
/-- **The cancellation of the flow cycles**: one pass on `g`, one pass on the reversed flow. -/
noncomputable def cancel (fr : FRFun F) (g : D → ℤ) : D → ℤ :=
  if h : Nonempty F then -(cpass M fr h.some (-(cpass M fr h.some g))) else g

/-- **The cancellation**: a conformal flow with the same net outflows and no closed walk of
positive darts. -/
theorem cancel_spec (hM : M.IsPlane) {fr : FRFun F} (hfr : FRSpec fr) {g : D → ℤ}
    (hg : M.IsAntisymm g) :
    M.IsAntisymm (cancel M fr g) ∧ Conf g (cancel M fr g) ∧
      (∀ v, M.div (cancel M fr g) v = M.div g v) ∧
      ∀ v, ¬ Relation.TransGen (Pos M (cancel M fr g)) v v := by
  unfold cancel
  split_ifs with hF
  swap
  · refine ⟨hg, Conf.refl g, fun _ => rfl, fun v h => ?_⟩
    obtain ⟨c, ⟨d, -, -, -⟩, -⟩ := Relation.TransGen.head'_iff.1 h
    exact hF ⟨M.face d⟩
  generalize hr : hF.some = r
  have a₁ := cpass_antisymm (fr := fr) (r := r) hg
  generalize hg₁ : cpass M fr r g = g₁ at a₁
  have hn₁ : M.IsAntisymm (-g₁) := fun d => by simp [a₁ d]
  have a₂ := cpass_antisymm (fr := fr) (r := r) hn₁
  have c₁ : Conf g g₁ := hg₁ ▸ cpass_conf hM hfr r hg
  have c₂ : Conf (-g₁) (cpass M fr r (-g₁)) := cpass_conf hM hfr r hn₁
  generalize hg₂' : cpass M fr r (-g₁) = g₂' at a₂ c₂
  have a₂' : M.IsAntisymm (-g₂') := fun d => by simp [a₂ d]
  have c₂' : Conf g₁ (-g₂') := by
    have := c₂.neg hn₁ a₂; simpa using this
  refine ⟨a₂', c₁.trans c₂', fun v => ?_, fun v hv => ?_⟩
  · have e₂ : M.div g₂' v = M.div (-g₁) v := by rw [← hg₂']; exact div_cpass _ v
    have e₁ : M.div g₁ v = M.div g v := by rw [← hg₁]; exact div_cpass _ v
    have hn : ∀ h : D → ℤ, M.div (-h) v = - M.div h v := fun h => by
      simp [CombMap.div, sum_neg_distrib]
    rw [hn, e₂, hn, e₁, neg_neg]
  · obtain ⟨ds, hne, hpos, hdiv⟩ := exists_circ_of_transGen hv
    obtain ⟨ψ₀, hψ₀⟩ := exists_int_potential hM
      (f := circ M ds) ⟨circ_antisymm ds, fun w => by rw [hdiv]; simp⟩
    let ψ : F → ℤ := fun y => ψ₀ y - ψ₀ r
    have hψ : ∀ d, circ M ds d = M.cob ψ d := fun d => by rw [hψ₀]; simp [cob, ψ]
    have hψr : ψ r = 0 := by simp [ψ]
    have hNn : (0 : ℤ) ≤ ds.length := by positivity
    -- the dart positive for the result is positive for the first pass
    have hpos₁ : ∀ d ∈ ds, 0 < g₁ d := fun d hd => c₂'.pos a₁ a₂' (hpos d hd)
    -- the first pass: `ψ ≥ 0`
    have hge : ∀ y, 0 ≤ ψ y := by
      intro y
      refine pass_extremal hM hfr r hg hψr hNn (fun d hd => ?_) y
      rw [← hψ] at hd
      rw [hg₁]
      exact ⟨hpos₁ _ (circ_neg_mem hd), by rw [← hψ]; exact neg_circ_le ds d⟩
    -- the second pass: `ψ ≤ 0`
    have hle : ∀ y, 0 ≤ -ψ y := by
      intro y
      have hψr' : (fun y => -ψ y) r = 0 := by simp [hψr]
      refine pass_extremal hM hfr r hn₁ (ψ := fun y => -ψ y) hψr' hNn (fun d hd => ?_) y
      have e : M.cob (fun y => -ψ y) d = - circ M ds d := by rw [hψ]; simp [cob]; ring
      rw [e] at hd ⊢
      have hd' : 0 < circ M ds d := by omega
      have hmem : d ∈ ds := by
        by_contra hn; simp [circ, List.count_eq_zero_of_not_mem hn] at hd'; omega
      rw [hg₂', a₂ d]
      refine ⟨?_, by rw [neg_neg]; exact circ_le ds d⟩
      have := hpos d hmem; simp only [Pi.neg_apply] at this; omega
    -- the circulation vanishes, but not on the first dart
    obtain ⟨d₀, hd₀⟩ := List.exists_mem_of_ne_nil ds hne
    have h0 : circ M ds d₀ = 0 := by
      rw [hψ]; simp only [cob]
      have := hge (M.face (M.rev d₀)); have := hle (M.face (M.rev d₀))
      have := hge (M.face d₀); have := hle (M.face d₀)
      omega
    have hrev : M.rev d₀ ∉ ds := fun h => by
      have h1 := hpos _ h; have h2 := hpos _ hd₀
      simp only [Pi.neg_apply] at h1 h2; rw [a₂ d₀] at h1; omega
    simp only [circ, List.count_eq_zero_of_not_mem hrev] at h0
    have := List.count_pos_iff.2 hd₀
    omega

/-! ### The topological rank -/

variable (M) in
/-- A walk of `j` positive darts from `u` to `v`. -/
def PosW (g : D → ℤ) : ℕ → V → V → Prop
  | 0, u, v => u = v
  | j + 1, u, w => ∃ v, PosW g j u v ∧ Pos M g v w

lemma PosW.transGen {g : D → ℤ} : ∀ {j : ℕ} {u v : V}, PosW M g (j + 1) u v →
    Relation.TransGen (Pos M g) u v
  | 0, _, _, ⟨_, rfl, h⟩ => .single h
  | _ + 1, _, _, ⟨_, h, h'⟩ => .tail h.transGen h'

/-- A walk of `j` positive darts visits the vertices `p 0, …, p j`. -/
lemma PosW.seq {g : D → ℤ} : ∀ {j : ℕ} {u v : V}, PosW M g j u v →
    ∃ p : ℕ → V, p 0 = u ∧ p j = v ∧ ∀ i < j, Pos M g (p i) (p (i + 1))
  | 0, u, _, h => ⟨fun _ => u, rfl, h, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | j + 1, u, w, ⟨v, h, h'⟩ => by
    obtain ⟨p, h0, hj, hp⟩ := h.seq
    refine ⟨fun i => if i = j + 1 then w else p i, by simp [h0], by simp, fun i hi => ?_⟩
    have hi' : i ≠ j + 1 := by omega
    simp only [hi', ite_false]
    by_cases hij : i + 1 = j + 1
    · have : i = j := by omega
      subst this; simpa [hj] using h'
    · simp only [hij, ite_false]; exact hp i (by omega)

/-- **A walk of positive darts with at least as many darts as there are vertices closes a
positive cycle.** -/
lemma PosW.cycle {g : D → ℤ} {j : ℕ} {u v : V} (h : PosW M g j u v)
    (hj : Fintype.card V ≤ j) : ∃ x, Relation.TransGen (Pos M g) x x := by
  obtain ⟨p, -, -, hp⟩ := h.seq
  have hlt : Fintype.card V < Fintype.card (Fin (j + 1)) := by simp; omega
  obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (j + 1) => p i) hlt
  have key : ∀ a b : ℕ, a < b → b ≤ j → Relation.TransGen (Pos M g) (p a) (p b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | rfl
      · exact .tail (ih h' (by omega)) (hp b (by omega))
      · exact .single (hp a (by omega))
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h' | h'
  · exact ⟨p a, by simpa [he] using key a b h' (by omega)⟩
  · exact ⟨p b, by simpa [he] using key b a h' (by omega)⟩

variable (M) in
/-- **The height of a vertex**: the number of darts of a longest walk of positive darts ending at
`v` (at most the number of vertices). For an acyclic flow, the heights are computed in linear
time along a topological order. -/
noncomputable def rk (g : D → ℤ) (v : V) : ℕ := by
  classical exact Nat.findGreatest (fun j => ∃ u, PosW M g j u v) (Fintype.card V)

/-- **The height increases along every positive dart** of an acyclic flow. -/
lemma rk_lt {g : D → ℤ} (hac : ∀ v, ¬ Relation.TransGen (Pos M g) v v) {d : D} (hd : 0 < g d) :
    rk M g (M.tail d) < rk M g (M.head d) := by
  classical
  unfold rk
  generalize hh : Nat.findGreatest (fun j => ∃ u, PosW M g j u (M.tail d)) (Fintype.card V) = h
  have hs : ∃ u, PosW M g h u (M.tail d) := by
    rw [← hh]
    exact Nat.findGreatest_spec (P := fun j => ∃ u, PosW M g j u (M.tail d)) (m := 0)
      (Nat.zero_le _) ⟨M.tail d, rfl⟩
  obtain ⟨u, hu⟩ := hs
  have hle : h + 1 ≤ Fintype.card V := by
    by_contra hn
    obtain ⟨x, hx⟩ := hu.cycle (by omega)
    exact hac x hx
  exact Nat.lt_of_succ_le (Nat.le_findGreatest hle ⟨u, M.tail d, hu, d, rfl, rfl, hd⟩)

end BKMNW

end PlanarFlow
