module

public import PlanarFlow.BKMNW.Cancel

/-!
# Pushing excess back: line 13 of Algorithm 1 (Appendix C)

Appendix C of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J. Comput. 46(4), 2017)
turns a pseudoflow into a flow: cancel the flow cycles, then, in a topological order of the
acyclic flow, reduce the flow on the darts carrying the unwanted excess. This file implements the
procedure in a general form, `pushFwd`, used by line 13 of Algorithm 1 (`frmImpl`, `retImpl`) and
by line 10 of CycleToSingleSinkLimitedMaxFlow (`PlanarFlow/BKMNW/CycleSink.lean`).

## The procedure (`pushFwd β Fr g`)

Every vertex `v` outside a set `Fr` (the *free* vertices, which may absorb any amount) has a bound
`β v` on its net outflow. The procedure

1. cancels the flow cycles of `g` (`PlanarFlow.BKMNW.cancel`);
2. visits the vertices by increasing height (`pushOrder`, `PlanarFlow.BKMNW.rk`: the number of
   darts of a longest walk of positive darts ending at the vertex); at a vertex `v ∉ Fr` whose net
   outflow exceeds `β v`, it reduces the flow on the positive darts leaving `v` by the excess, one
   dart after the other (`pushAt`, `redStep`).

The flow on every dart is reduced at most once: the excess moves to the heads of the reduced darts,
which come later in the topological order, so a visited vertex is never changed again. The
heights are computed in linear time along a topological order of the acyclic flow, and the
stable sort by height (`pushOrder`, a merge sort) is the list that a counting sort by height,
linear, gives (the heights are less than the number of vertices). The loop over the vertices and
their darts is linear; the cost is that of the cancellation.

`pushFwd_spec`: if no positive dart leaves a set `W` outside which every non-free vertex is within
its bound, and `β ≥ 0` on the non-free vertices of `W`, the result is a pseudoflow conformal to
`g`, every non-free vertex ends within its bound and with a net outflow at least
`min (div g v) (β v)`, and the net outflow of a free vertex does not decrease.

## Line 13

* `frmImpl`, `frm_spec`: **pushing flow back from the sinks** meets `FromOut` (the bound is `0` on
  `X`, the original net outflow elsewhere, and the sinks are free).
* `retImpl`, `ret_spec`: **pushing excess back to the sources**, the same on the reversed flow,
  meets `RetOut`.

The preconditions are those under which Algorithm 1 calls them (`NodeOracles.Spec`), together with
nonnegative capacities.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

lemma div_neg' (h : D → ℤ) (v : V) : M.div (-h) v = - M.div h v := by
  simp [CombMap.div, sum_neg_distrib]

/-! ### The procedure -/

variable (M) in
/-- Reduce the flow on `d` by at most the remaining amount (if both are positive). -/
def redStep (st : (D → ℤ) × ℤ) (d : D) : (D → ℤ) × ℤ :=
  if 0 < st.1 d ∧ 0 < st.2 then
    (setPair M st.1 d (st.1 d - min st.2 (st.1 d)), st.2 - min st.2 (st.1 d))
  else st

variable (M) in
/-- The darts leaving `v`. -/
noncomputable def outDarts (v : V) : List D := (univ.filter fun d => M.tail d = v).toList

variable (M) in
/-- The visit of `v`: if `v` is not free and its net outflow exceeds `β v`, reduce the darts
leaving it by the excess. -/
noncomputable def pushAt (β : V → ℤ) (Fr : Finset V) (g : D → ℤ) (v : V) : D → ℤ :=
  if v ∉ Fr ∧ β v < M.div g v then ((outDarts M v).foldl (redStep M) (g, M.div g v - β v)).1
  else g

variable (M) in
/-- The vertices by increasing height (a stable sort). -/
noncomputable def pushOrder (g : D → ℤ) : List V :=
  (univ : Finset V).toList.mergeSort fun a b => decide (rk M g a ≤ rk M g b)

variable (M) in
/-- **The push-back** (Appendix C): cancel the flow cycles, then visit the vertices in topological
order. -/
noncomputable def pushFwd (fr : FRFun F) (β : V → ℤ) (Fr : Finset V) (g : D → ℤ) : D → ℤ :=
  (pushOrder M (cancel M fr g)).foldl (pushAt M β Fr) (cancel M fr g)

/-! ### The reductions at one vertex -/

/-- **The reductions at a vertex `v`** along a list of darts leaving it: the result is conformal,
the net outflow of `v` decreases by the amount used, the whole amount is used if the darts carry
enough flow, and the other vertices only gain, and only at the heads of positive darts. -/
theorem redFold_spec {v : V} :
    ∀ (ds : List D) (g : D → ℤ) (rem : ℤ), M.IsAntisymm g → 0 ≤ rem → ds.Nodup →
      (∀ d ∈ ds, M.tail d = v) → (∀ d ∈ ds, 0 < g d → M.head d ≠ v) →
      M.IsAntisymm (ds.foldl (redStep M) (g, rem)).1 ∧ Conf g (ds.foldl (redStep M) (g, rem)).1 ∧
      0 ≤ (ds.foldl (redStep M) (g, rem)).2 ∧
      M.div (ds.foldl (redStep M) (g, rem)).1 v =
        M.div g v - (rem - (ds.foldl (redStep M) (g, rem)).2) ∧
      (rem ≤ (ds.map fun d => max 0 (g d)).sum → (ds.foldl (redStep M) (g, rem)).2 = 0) ∧
      (∀ w, w ≠ v → (∀ d ∈ ds, 0 < g d → M.head d ≠ w) →
        M.div (ds.foldl (redStep M) (g, rem)).1 w = M.div g w) ∧
      (∀ w, w ≠ v → M.div g w ≤ M.div (ds.foldl (redStep M) (g, rem)).1 w) := by
  intro ds
  induction ds with
  | nil =>
    intro g rem hg hrem _ _ _
    simp only [List.foldl_nil, List.map_nil, List.sum_nil]
    exact ⟨hg, Conf.refl g, hrem, by simp, fun h => by omega, by simp,
      fun _ _ => le_rfl⟩
  | cons d ds ih =>
    intro g rem hg hrem hnd htail hloop
    obtain ⟨hdn, hnd'⟩ := List.nodup_cons.1 hnd
    have htd : M.tail d = v := htail d (List.mem_cons_self ..)
    rw [List.foldl_cons]
    by_cases hc : 0 < g d ∧ 0 < rem
    · have hstep : redStep M (g, rem) d =
          (setPair M g d (g d - min rem (g d)), rem - min rem (g d)) := by
        simp only [redStep, hc, and_self, ite_true]
      rw [hstep]
      have hhd : M.head d ≠ v := hloop d (List.mem_cons_self ..) hc.1
      generalize ha : min rem (g d) = a
      have ha1 : 0 < a := by rw [← ha]; exact lt_min hc.2 hc.1
      have ha2 : a ≤ rem := by rw [← ha]; exact min_le_left _ _
      have ha3 : a ≤ g d := by rw [← ha]; exact min_le_right _ _
      have hg₁ := setPair_antisymm hg d (g d - a)
      -- the other darts are unchanged
      have hsame : ∀ d' ∈ ds, setPair M g d (g d - a) d' = g d' := by
        intro d' hd'
        refine setPair_of_ne _ _ (fun h => hdn (h ▸ hd')) (fun h => ?_)
        have h1 := htail d' (List.mem_cons_of_mem _ hd')
        rw [h, M.tail_rev] at h1
        exact hhd h1
      have hdiv : ∀ w, M.div (setPair M g d (g d - a)) w =
          M.div g w - a * ((if v = w then 1 else 0) - (if M.head d = w then 1 else 0)) := by
        intro w; rw [div_setPair hg, htd]; ring
      obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := ih (setPair M g d (g d - a)) (rem - a) hg₁
        (by omega) hnd' (fun d' hd' => htail d' (List.mem_cons_of_mem _ hd'))
        (fun d' hd' hp => hloop d' (List.mem_cons_of_mem _ hd') (by rwa [hsame d' hd'] at hp))
      have hmap : (ds.map fun d' => max 0 (setPair M g d (g d - a) d')) =
          ds.map fun d' => max 0 (g d') := List.map_congr_left fun d' hd' => by rw [hsame d' hd']
      have hconf : Conf g (setPair M g d (g d - a)) := by
        intro e he
        by_cases h1 : e = d
        · subst h1; rw [setPair_self]; omega
        · by_cases h2 : e = M.rev d
          · subst h2; rw [hg d] at he; omega
          · rw [setPair_of_ne _ _ h1 h2]; exact ⟨he, le_rfl⟩
      refine ⟨i1, hconf.trans i2, i3, ?_, fun hs => ?_, fun w hw hpos => ?_, fun w hw => ?_⟩
      · rw [i4, hdiv v]; simp only [ite_true, hhd, ite_false]; ring
      · apply i5
        rw [hmap]
        simp only [List.map_cons, List.sum_cons] at hs
        have hs0 : 0 ≤ (ds.map fun d' => max 0 (g d')).sum :=
          List.sum_nonneg (by simp)
        rw [max_eq_right hc.1.le] at hs
        rcases le_total rem (g d) with h | h
        · have : a = rem := by rw [← ha]; exact min_eq_left h
          omega
        · have : a = g d := by rw [← ha]; exact min_eq_right h
          omega
      · have hhw : M.head d ≠ w := hpos d (List.mem_cons_self ..) hc.1
        rw [i6 w hw (fun d' hd' hp => hpos d' (List.mem_cons_of_mem _ hd')
          (by rwa [hsame d' hd'] at hp)), hdiv w]
        simp [Ne.symm hw, hhw]
      · refine le_trans ?_ (i7 w hw)
        rw [hdiv w]
        simp only [Ne.symm hw, ite_false]
        split_ifs <;> nlinarith
    · have hstep : redStep M (g, rem) d = (g, rem) := by
        simp only [redStep, hc, ite_false]
      rw [hstep]
      obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := ih g rem hg hrem hnd'
        (fun d' hd' => htail d' (List.mem_cons_of_mem _ hd'))
        (fun d' hd' hp => hloop d' (List.mem_cons_of_mem _ hd') hp)
      refine ⟨i1, i2, i3, i4, fun hs => i5 ?_, fun w hw hpos => i6 w hw
        (fun d' hd' hp => hpos d' (List.mem_cons_of_mem _ hd') hp), i7⟩
      simp only [List.map_cons, List.sum_cons] at hs
      have hs0 : 0 ≤ (ds.map fun d' => max 0 (g d')).sum := List.sum_nonneg (by simp)
      by_cases hgd : 0 < g d
      · have : rem ≤ 0 := by by_contra h; exact hc ⟨hgd, by omega⟩
        omega
      · rw [max_eq_left (by omega)] at hs; omega

/-! ### The visits -/

/-- The invariant of the visits, relative to the acyclic flow `g₀`, after the vertices `P`. -/
structure PInv (β : V → ℤ) (Fr W : Finset V) (g₀ g : D → ℤ) (P : Finset V) : Prop where
  antisymm : M.IsAntisymm g
  conf : Conf g₀ g
  out : ∀ w, w ∉ W → M.div g w = M.div g₀ w
  done : ∀ w ∈ P, w ∉ Fr → M.div g w ≤ β w
  low : ∀ w, M.div g₀ w ≤ M.div g w ∨ (w ∈ P ∧ w ∉ Fr ∧ M.div g w = β w)

lemma sum_out_le (g : D → ℤ) (v : V) :
    M.div g v ≤ ((outDarts M v).map fun d => max 0 (g d)).sum := by
  rw [outDarts, Finset.sum_map_toList]
  exact sum_le_sum fun d _ => le_max_right _ _

/-- **The visits in topological order.** -/
theorem pushLoop_spec {β : V → ℤ} {Fr W : Finset V} {g₀ : D → ℤ} {rkf : V → ℕ}
    (hrk : ∀ d, 0 < g₀ d → rkf (M.tail d) < rkf (M.head d))
    (hW : ∀ d, M.tail d ∈ W → M.head d ∉ W → g₀ d ≤ 0)
    (hout : ∀ v, v ∉ W → v ∉ Fr → M.div g₀ v ≤ β v)
    (hin : ∀ v ∈ W, v ∉ Fr → 0 ≤ β v) (ha : M.IsAntisymm g₀) :
    ∀ (L : List V) (g : D → ℤ) (P : Finset V), L.Nodup →
      L.Pairwise (fun a b => rkf a ≤ rkf b) → (∀ v ∈ L, v ∉ P) →
      (∀ w ∈ P, ∀ v ∈ L, rkf w ≤ rkf v) → PInv (M := M) β Fr W g₀ g P →
      PInv (M := M) β Fr W g₀ (L.foldl (pushAt M β Fr) g) (P ∪ L.toFinset) := by
  intro L
  induction L with
  | nil => intro g P _ _ _ _ h; simpa using h
  | cons v L ih =>
    intro g P hnd hpw hLP hrkP h
    obtain ⟨hvL, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨hpv, hpw'⟩ := List.pairwise_cons.1 hpw
    have hvP : v ∉ P := hLP v (List.mem_cons_self ..)
    rw [List.foldl_cons]
    have heq : P ∪ (v :: L).toFinset = insert v P ∪ L.toFinset := by
      ext x; simp only [mem_union, List.mem_toFinset, List.mem_cons, mem_insert]; tauto
    rw [heq]
    refine ih _ _ hnd' hpw' (fun x hx => ?_) (fun w hw x hx => ?_) ?_
    · rw [mem_insert]; push Not
      exact ⟨fun h => hvL (h ▸ hx), hLP x (List.mem_cons_of_mem _ hx)⟩
    · rcases mem_insert.1 hw with rfl | hw
      · exact hpv x hx
      · exact hrkP w hw x (List.mem_cons_of_mem _ hx)
    -- one visit
    have hrkv : ∀ w ∈ P, rkf w ≤ rkf v := fun w hw => hrkP w hw v (List.mem_cons_self ..)
    unfold pushAt
    split_ifs with hc
    swap
    · refine ⟨h.antisymm, h.conf, h.out, fun w hw hwF => ?_, fun w => ?_⟩
      · rcases mem_insert.1 hw with rfl | hw
        · push Not at hc; exact hc hwF
        · exact h.done w hw hwF
      · rcases h.low w with h' | ⟨h1, h2, h3⟩
        · exact Or.inl h'
        · exact Or.inr ⟨mem_insert_of_mem h1, h2, h3⟩
    obtain ⟨hvF, hlt⟩ := hc
    have hvW : v ∈ W := by
      by_contra hn
      have := h.out v hn; have := hout v hn hvF; omega
    have hβ := hin v hvW hvF
    have hpos₀ : ∀ d, 0 < g d → 0 < g₀ d := fun d hd => h.conf.pos ha h.antisymm hd
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := redFold_spec (M := M) (v := v) (outDarts M v) g
      (M.div g v - β v) h.antisymm (by omega) (Finset.nodup_toList _)
      (fun d hd => by simpa [outDarts] using hd)
      (fun d hd hp => by
        have h1 : M.tail d = v := by simpa [outDarts] using hd
        have := hrk d (hpos₀ d hp)
        rw [h1] at this; intro h2; rw [h2] at this; omega)
    have h0 := i5 (by have := sum_out_le (M := M) g v; omega)
    rw [h0] at i4
    generalize (outDarts M v).foldl (redStep M) (g, M.div g v - β v) = st at *
    -- the heads of the positive darts leaving `v`
    have hheads : ∀ d ∈ outDarts M v, 0 < g d → rkf v < rkf (M.head d) ∧ M.head d ∈ W := by
      intro d hd hp
      have h1 : M.tail d = v := by simpa [outDarts] using hd
      refine ⟨h1 ▸ hrk d (hpos₀ d hp), ?_⟩
      by_contra hn
      have := hW d (h1 ▸ hvW) hn; have := hpos₀ d hp; omega
    have hunch : ∀ w, w ≠ v → (rkf w ≤ rkf v ∨ w ∉ W) → M.div st.1 w = M.div g w := by
      intro w hw hw'
      refine i6 w hw fun d hd hp hdw => ?_
      obtain ⟨h1, h2⟩ := hheads d hd hp
      rw [hdw] at h1 h2
      rcases hw' with h3 | h3
      · omega
      · exact h3 h2
    refine ⟨i1, h.conf.trans i2, fun w hw => ?_, fun w hw hwF => ?_, fun w => ?_⟩
    · rw [hunch w (fun h' => hw (h' ▸ hvW)) (Or.inr hw)]; exact h.out w hw
    · rcases mem_insert.1 hw with rfl | hw
      · omega
      · rw [hunch w (fun h' => hvP (h' ▸ hw)) (Or.inl (hrkv w hw))]; exact h.done w hw hwF
    · by_cases hwv : w = v
      · subst hwv; exact Or.inr ⟨mem_insert_self _ _, hvF, by omega⟩
      · rcases h.low w with h' | ⟨h1, h2, h3⟩
        · exact Or.inl (h'.trans (i7 w hwv))
        · refine Or.inr ⟨mem_insert_of_mem h1, h2, ?_⟩
          rw [hunch w hwv (Or.inl (hrkv w h1))]; exact h3

/-- **The specification of the push-back.** -/
theorem pushFwd_spec (hM : M.IsPlane) {fr : FRFun F} (hfr : FRSpec fr) {c g : D → ℤ}
    (hc : ∀ d, 0 ≤ c d) (hg : IsPseudo M c g) {β : V → ℤ} {Fr W : Finset V}
    (hW : ∀ d, M.tail d ∈ W → M.head d ∉ W → g d ≤ 0)
    (hout : ∀ v, v ∉ W → v ∉ Fr → M.div g v ≤ β v) (hin : ∀ v ∈ W, v ∉ Fr → 0 ≤ β v) :
    IsPseudo M c (pushFwd M fr β Fr g) ∧ Conf g (pushFwd M fr β Fr g) ∧
      (∀ v, v ∉ Fr → M.div (pushFwd M fr β Fr g) v ≤ β v) ∧
      (∀ v, v ∉ Fr → min (M.div g v) (β v) ≤ M.div (pushFwd M fr β Fr g) v) ∧
      (∀ v ∈ Fr, M.div g v ≤ M.div (pushFwd M fr β Fr g) v) := by
  classical
  obtain ⟨a₀, c₀, d₀, ac₀⟩ := cancel_spec hM hfr hg.antisymm
  have hall : ∀ v, v ∈ pushOrder M (cancel M fr g) := fun v => by simp [pushOrder]
  have h := pushLoop_spec (M := M) (β := β) (Fr := Fr) (W := W) (rkf := rk M (cancel M fr g))
    (fun d hd => rk_lt ac₀ hd)
    (fun d h1 h2 => by
      by_contra hn
      have := hW d h1 h2; have := c₀.pos hg.antisymm a₀ (by omega : 0 < cancel M fr g d); omega)
    (fun v h1 h2 => by rw [d₀]; exact hout v h1 h2) (fun v h1 h2 => hin v h1 h2) a₀
    (pushOrder M (cancel M fr g)) (cancel M fr g) ∅
    ((List.mergeSort_perm _ _).nodup_iff.2 (Finset.nodup_toList _))
    ((List.pairwise_mergeSort (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _).imp
      (fun h => by simpa using h))
    (fun _ _ => notMem_empty _) (fun _ h => absurd h (notMem_empty _))
    ⟨a₀, Conf.refl _, fun _ _ => rfl, fun _ h => absurd h (notMem_empty _),
      fun _ => Or.inl le_rfl⟩
  have hmem : ∀ v, v ∈ ∅ ∪ (pushOrder M (cancel M fr g)).toFinset := fun v => by
    simp [hall v]
  unfold pushFwd
  generalize (pushOrder M (cancel M fr g)).foldl (pushAt M β Fr) (cancel M fr g) = g' at h ⊢
  refine ⟨hg.of_conf hc h.antisymm (c₀.trans h.conf), c₀.trans h.conf,
    fun v hv => h.done v (hmem v) hv, fun v hv => ?_, fun v hv => ?_⟩
  · rcases h.low v with h' | ⟨-, -, h3⟩
    · rw [← d₀]; exact (min_le_left _ _).trans h'
    · rw [h3]; exact min_le_right _ _
  · rcases h.low v with h' | ⟨-, h2, -⟩
    · rw [← d₀]; exact h'
    · exact absurd hv h2

/-! ### Line 13 -/

variable (M) in
/-- **Pushing flow back from the sinks `T`** so that the vertices of `X` become balanced. -/
noncomputable def frmImpl (fr : FRFun F) (f : D → ℤ) (T X : Finset V) : D → ℤ :=
  pushFwd M fr (fun v => if v ∈ X then 0 else M.div f v) T f

variable (M) in
/-- **Pushing excess back to the sources `S`** so that the vertices of `X` become balanced: the
push-back from the sinks on the reversed flow. -/
noncomputable def retImpl (fr : FRFun F) (f : D → ℤ) (X S : Finset V) : D → ℤ :=
  -(frmImpl M fr (-f) S X)

/-- **The push-back from the sinks meets `FromOut`.** -/
theorem frm_spec (hM : M.IsPlane) {fr : FRFun F} (hfr : FRSpec fr) {U f : D → ℤ}
    (hU : ∀ d, 0 ≤ U d) (hf : IsPseudo M U f) {T X : Finset V} (hXT : Disjoint X T)
    (hX : ∀ v ∈ X, 0 ≤ M.div f v)
    (hW : ∃ W, X ⊆ W ∧ Closed M U f (univ \ W) ∧ ∀ v ∈ W, v ∉ T → v ∉ X → M.div f v = 0) :
    FromOut M U f (frmImpl M fr f T X) T X := by
  obtain ⟨W, hXW, hcl, hbal⟩ := hW
  obtain ⟨p1, -, p3, p4, p5⟩ := pushFwd_spec (W := W) hM hfr hU hf
    (β := fun v => if v ∈ X then 0 else M.div f v) (Fr := T)
    (fun d h1 h2 => by
      have := hcl (M.rev d) (by simpa using h2) (by simpa using h1)
      rw [hf.antisymm d] at this; have := hU (M.rev d); omega)
    (fun v h1 _ => by
      have : v ∉ X := fun h => h1 (hXW h)
      simp [this])
    (fun v h1 h2 => by
      by_cases hv : v ∈ X
      · simp [hv]
      · simp only [hv, ite_false]; rw [hbal v h1 h2 hv])
  refine ⟨p1, fun v hv => ?_, fun v h1 h2 => ?_, p5⟩
  · have hvT : v ∉ T := disjoint_left.1 hXT hv
    have a := p3 v hvT; have b := p4 v hvT
    simp only [hv, ite_true] at a b
    have := hX v hv
    rw [min_eq_right this] at b
    exact le_antisymm a b
  · have a := p3 v h2; have b := p4 v h2
    simp only [h1, ite_false, min_self] at a b
    exact le_antisymm a b

/-- **The push-back to the sources meets `RetOut`.** -/
theorem ret_spec (hM : M.IsPlane) {fr : FRFun F} (hfr : FRSpec fr) {U f : D → ℤ}
    (hU : ∀ d, 0 ≤ U d) (hf : IsPseudo M U f) {X S : Finset V} (hXS : Disjoint X S)
    (hX : ∀ v ∈ X, M.div f v ≤ 0)
    (hW : ∃ W, X ⊆ W ∧ Closed M U f W ∧ ∀ v ∈ W, v ∉ S → v ∉ X → M.div f v = 0) :
    RetOut M U f (retImpl M fr f X S) X S := by
  obtain ⟨W, hXW, hcl, hbal⟩ := hW
  have hf' : IsPseudo M (fun d => U (M.rev d)) (-f) :=
    ⟨fun d => by simp [hf.antisymm d], fun d => by
      have := hf.le_cap (M.rev d); rw [hf.antisymm d] at this; simp only [Pi.neg_apply]; omega⟩
  have o := frm_spec hM hfr (fun d => hU (M.rev d)) hf' hXS (fun v hv => by
      rw [div_neg']; have := hX v hv; omega)
    ⟨W, hXW, fun d h1 h2 => by
      have := hcl (M.rev d) (by simpa using h2) (by simpa using h1)
      rw [hf.antisymm d] at this; simp only [Pi.neg_apply]; omega,
      fun v h1 h2 h3 => by rw [div_neg', hbal v h1 h2 h3, neg_zero]⟩
  obtain ⟨o1, o2, o3, o4⟩ := o
  unfold retImpl
  generalize frmImpl M fr (-f) S X = g at o1 o2 o3 o4
  refine ⟨⟨fun d => by simp [o1.antisymm d], fun d => ?_⟩, fun v hv => ?_, fun v h1 h2 => ?_,
    fun v hv => ?_⟩
  · have := o1.le_cap (M.rev d); rw [o1.antisymm d] at this
    simp only [Pi.neg_apply, M.rev_rev] at this ⊢; omega
  · rw [div_neg', o2 v hv, neg_zero]
  · rw [div_neg', o3 v h1 h2, div_neg', neg_neg]
  · have := o4 v hv; rw [div_neg'] at this ⊢; omega

/-! ### Satisfiability -/

/-- **`FRSpec` is satisfiable** (by the distances themselves; not an algorithm). -/
theorem exists_frSpec (X : Type*) [Fintype X] [DecidableEq X] :
    ∃ fr : FRFun X, FRSpec fr := by
  classical
  refine ⟨fun H E r p => if h : (DDG.union H E).IsPot p then (exists_isDist h r).choose
    else fun _ => none, fun H E r p hp => ?_⟩
  simp only [hp, dite_true]
  exact (exists_isDist hp r).choose_spec

/-- **The specification `RetOut` is satisfiable** under the preconditions of line 13. -/
theorem exists_retOut (hM : M.IsPlane) {U f : D → ℤ} (hU : ∀ d, 0 ≤ U d) (hf : IsPseudo M U f)
    {X S : Finset V} (hXS : Disjoint X S) (hX : ∀ v ∈ X, M.div f v ≤ 0)
    (hW : ∃ W, X ⊆ W ∧ Closed M U f W ∧ ∀ v ∈ W, v ∉ S → v ∉ X → M.div f v = 0) :
    ∃ f', RetOut M U f f' X S :=
  ⟨_, ret_spec hM (exists_frSpec F).choose_spec hU hf hXS hX hW⟩

/-- **The specification `FromOut` is satisfiable** under the preconditions of line 13. -/
theorem exists_fromOut (hM : M.IsPlane) {U f : D → ℤ} (hU : ∀ d, 0 ≤ U d) (hf : IsPseudo M U f)
    {T X : Finset V} (hXT : Disjoint X T) (hX : ∀ v ∈ X, 0 ≤ M.div f v)
    (hW : ∃ W, X ⊆ W ∧ Closed M U f (univ \ W) ∧ ∀ v ∈ W, v ∉ T → v ∉ X → M.div f v = 0) :
    ∃ f', FromOut M U f f' T X :=
  ⟨_, frm_spec hM (exists_frSpec F).choose_spec hU hf hXT hX hW⟩

end BKMNW

end PlanarFlow
