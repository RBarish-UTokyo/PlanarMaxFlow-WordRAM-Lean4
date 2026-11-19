module

public import PlanarFlow.BKMNW.PushBack
public import PlanarFlow.BKMNW.FixFrozen
public import PlanarFlow.Flow.Network

/-!
# CycleToSingleSinkLimitedMaxFlow and SingleSourceToCycleLimitedMaxFlow

Section 4 and Appendix F of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J. Comput.
46(4), 2017): Algorithm 5 pushes the excess inflow of the vertices of the separator `C` to a hole
`H`.

## Single-source single-sink maximum flow (`STFlowSpec`)

The article calls **SingleSourceSingleSinkMaxFlow**, the `O(n log n)` maximum `st`-flow algorithm
of Borradaile and Klein for directed planar graphs, with the vertices of `C⁺` contracted into the
source (through artificial arcs, lines 4–6) and the sink a hole (a contracted separator of an
ancestor). Here the source and the sink are the vertex sets of two disjoint simple paths: the
contraction of the edges of a simple path keeps a plane graph plane, so the subroutine runs on a
plane graph with one source and one sink. Its specification `STOut`: a pseudoflow conserved off
the two sets, no residual path from the source to the sink, and nothing sent out of the sink: no
vertex of the sink has positive net outflow (a maximum flow can always be chosen so).
`exists_stFlowSpec`: the specification is satisfiable (by the max-flow min-cut theorem,
`PlanarFlow.Network.max_flow_min_cut`). The algorithm uses the perturbed implementation
`PlanarFlow.STFlow.pstflowW` (`PlanarFlow.BKMNW.planeOracles`), which meets the specification on
every plane map (`PlanarFlow.STFlow.pstflowW_spec`); the capacities it is called with are
nonnegative (`c2sCap_nonneg`).

## The procedure (`c2sImpl`, Algorithm 5)

With `C⁺` the vertices of `C` reachable by residual paths from those with positive inflow and
`Del = C - C⁺`:

1. lines 2–7: a maximum flow from `C` to the hole in the residual graph from which the darts
   touching `Del` are deleted (capacity `0`): the vertices of `Del` are isolated, so this is the
   maximum flow from `C⁺` of the article;
2. line 9: FixConservationOnPath along the separator path with the vertices of `Del` frozen
   (`PlanarFlow.BKMNW.fixFrozen`, on the map with pendant edges). **Modelling:** the article runs
   it along a path of artificial arcs through `C⁺` in the graph without `Del`; the fixed map
   cannot gain arcs, so the separator path itself is used, and freezing `Del` keeps its vertices
   (and their contribution to the inflow of the vertices of `C⁺`) unchanged, as deleting them
   does in the article;
3. line 10: push the flow added so far back (`PlanarFlow.BKMNW.pushFwd`, in the residual graph of
   the initial flow) until no vertex of `C⁺` has negative inflow and no vertex of the hole sends
   flow out.

`c2s_spec`: **the procedure meets `C2SOut`** (Lemma F.1), from the specifications of the planar
subroutines. `s2cImpl`, `s2c_spec`: SingleSourceToCycleLimitedMaxFlow is the same procedure on the
reversed flow, and meets `S2COut`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-! ### Single-source single-sink maximum flow -/

variable (M) in
/-- **The output of a maximum flow** from the vertices `X` to the vertices `Y`, each contracted
into one vertex. -/
structure STOut (c : D → ℤ) (X Y : Finset V) (g : D → ℤ) : Prop where
  pseudo : IsPseudo M c g
  cons : ∀ v, v ∉ X → v ∉ Y → M.div g v = 0
  sink : ∀ v ∈ Y, M.div g v ≤ 0
  cut : NoPath M c g X Y

variable (M) in
/-- **The specification of SingleSourceSingleSinkMaxFlow** (Borradaile and Klein): for
nonnegative capacities, the source and the sink the vertex sets of two disjoint simple paths
(contracted for the call), a maximum flow from the source to the sink. -/
def STFlowSpec (stflow : (D → ℤ) → Finset V → Finset V → D → ℤ) : Prop :=
  ∀ (c : D → ℤ) (πs πt : SPath M), (∀ d, 0 ≤ c d) → Disjoint πs.verts πt.verts →
    STOut M c πs.verts πt.verts (stflow c πs.verts πt.verts)

lemma sum_rev_tail (h : D → ℤ) (v : V) :
    ∑ d with M.tail d = v, h (M.rev d) = ∑ d with M.head d = v, h d := by
  refine Finset.sum_nbij' M.rev M.rev (fun d hd => ?_) (fun d hd => ?_) (fun d _ => M.rev_rev d)
    (fun d _ => M.rev_rev d) (fun d _ => rfl)
  · simp only [mem_filter, mem_univ, true_and] at hd ⊢; simp [CombMap.head, M.rev_rev, hd]
  · simp only [mem_filter, mem_univ, true_and] at hd ⊢; exact hd

/-- **A maximum flow from `X` to `Y` exists**, by the max-flow min-cut theorem in the network of
the darts, the darts leaving `Y` removed. -/
theorem exists_stOut {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) {X Y : Finset V} (hXY : Disjoint X Y) :
    ∃ g, STOut M c X Y g := by
  classical
  let N : Network V D := ⟨M.tail, M.head, fun d => if M.tail d ∈ Y then 0 else c d⟩
  obtain ⟨φ, W, hφ, hW, hv⟩ := N.max_flow_min_cut hXY (fun d => by
    show 0 ≤ (if M.tail d ∈ Y then 0 else c d); split_ifs
    · exact le_rfl
    · exact hc d)
  have hcap : ∀ d, φ d ≤ c d := fun d => (hφ.le_cap d).trans (by
    show (if M.tail d ∈ Y then 0 else c d) ≤ c d; split_ifs
    · exact hc d
    · exact le_rfl)
  have hdiv : ∀ v, M.div (fun d => φ d - φ (M.rev d)) v = N.netOut φ v := by
    intro v
    simp only [CombMap.div, sum_sub_distrib, sum_rev_tail]
    rfl
  have hps : IsPseudo M c (fun d => φ d - φ (M.rev d)) :=
    ⟨fun d => by simp [M.rev_rev], fun d => by have := hcap d; have := hφ.nonneg (M.rev d); omega⟩
  refine ⟨_, hps, fun v h1 h2 => by rw [hdiv]; exact hφ.conserve v h1 h2,
    fun v hvY => ?_, ⟨W, hW.1, hW.2, (tight_iff_closed hps W).1 ?_⟩⟩
  · rw [hdiv]
    have : ∑ d with N.tail d = v, φ d = 0 := sum_eq_zero fun d hd => by
      simp only [mem_filter, mem_univ, true_and] at hd
      have := hφ.le_cap d; have := hφ.nonneg d
      have hy : M.tail d ∈ Y := by rw [show M.tail d = v from hd]; exact hvY
      have h' : N.cap d = 0 := by
        show (if M.tail d ∈ Y then 0 else c d) = 0; simp [hy]
      omega
    simp only [Network.netOut, this, zero_sub, neg_nonpos]
    exact sum_nonneg fun d _ => hφ.nonneg d
  · simp only [hdiv]
    rw [N.sum_netOut, ← N.value_eq_flowAcross hφ hW, hv, Network.cutCap, BKMNW.cutCap]
    refine sum_congr rfl fun d hd => ?_
    simp only [mem_filter, mem_univ, true_and] at hd
    show (if M.tail d ∈ Y then 0 else c d) = c d
    simp [fun h => disjoint_left.1 hW.2 hd.1 h]

/-- **`STFlowSpec` is satisfiable** (by maximum flows; not an algorithm). -/
theorem exists_stFlowSpec (M : CombMap D V F) : ∃ stflow, STFlowSpec M stflow := by
  classical
  refine ⟨fun (c : D → ℤ) (X Y : Finset V) => if h : (∀ d, 0 ≤ c d) ∧ Disjoint X Y then
    (exists_stOut (M := M) h.1 h.2).choose else 0, fun c πs πt hc hd => ?_⟩
  simp only [hc, hd, implies_true, and_self, dite_true]
  exact (exists_stOut (M := M) hc hd).choose_spec

/-! ### The procedure -/

variable (M) in
/-- The vertices of `C` not reachable from those with positive inflow (`C - C⁺`). -/
noncomputable def delSet (U f : D → ℤ) (C : Finset V) : Finset V :=
  C \ fwdReach M U f (posSet M f C) C

variable (M) in
/-- The residual capacities with the darts touching `C - C⁺` deleted. -/
noncomputable def c2sCap (U f : D → ℤ) (C : Finset V) (d : D) : ℤ :=
  if d ∈ incSet M (delSet M U f C) then 0 else U d - f d

/-- The capacities of the maximum flow of lines 2–7 are nonnegative when `f` is a pseudoflow:
the hypothesis on the capacities of the cost bound of the s-t flow subroutine
(`PlanarFlow.STFlow.pstflowWCost_le`) holds at every call. -/
lemma c2sCap_nonneg {U f : D → ℤ} (hf : IsPseudo M U f) (C : Finset V) (d : D) :
    0 ≤ c2sCap M U f C d := by
  unfold c2sCap
  split_ifs
  · exact le_rfl
  · have := hf.le_cap d; omega

variable (M) in
/-- The bounds of line 10: the inflow of the vertices of `C⁺` stays nonnegative. -/
noncomputable def c2sBeta (U f : D → ℤ) (C : Finset V) (v : V) : ℤ :=
  if v ∈ fwdReach M U f (posSet M f C) C then - M.div f v else 0

variable (M) in
/-- **CycleToSingleSinkLimitedMaxFlow** (Algorithm 5), from the separator path `π` to the hole
`H`. -/
noncomputable def c2sImpl (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F)
    (neg : (D → ℤ) → Option (F → ℤ)) (stflow : (D → ℤ) → Finset V → Finset V → D → ℤ)
    (U f : D → ℤ) (π : SPath M) (H : Finset V) : D → ℤ := by
  classical
  exact if he : ∀ v, ∃ d, M.tail d = v then
    f + pushFwd M fr (c2sBeta M U f π.verts) ∅
      (fixFrozen M (fun v => (he v).choose) (fun v => (he v).choose_spec) mssp fr neg U
        (f + stflow (c2sCap M U f π.verts) π.verts H) π (delSet M U f π.verts) - f)
  else f

/-- On a plane map, a vertex without darts means that there are no darts. -/
lemma isEmpty_of_no_dart (hM : M.IsPlane) (h : ¬ ∀ v, ∃ d, M.tail d = v) : IsEmpty D := by
  push Not at h
  obtain ⟨v, hv⟩ := h
  refine ⟨fun d => ?_⟩
  rcases Relation.ReflTransGen.cases_head (hM.conn v (M.tail d)) with h | ⟨w, ⟨d', h1, -⟩, -⟩
  · exact hv d h.symm
  · exact hv d' h1

/-- **CycleToSingleSinkLimitedMaxFlow meets its specification** (Lemma F.1). -/
theorem c2s_spec (hM : M.IsPlane) {U f : D → ℤ} (hU : ∀ d, 0 ≤ U d) (hf : IsPseudo M U f)
    {π : SPath M} {H : Finset V} (hCH : Disjoint π.verts H) (hH : ∃ πH : SPath M, πH.verts = H)
    (hpre : ∀ v ∈ fwdReach M U f (posSet M f π.verts) π.verts, M.div f v ≤ 0)
    {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp π)
    {fr : FRFun F} (hfr : FRSpec fr) {neg : (D → ℤ) → Option (F → ℤ)} (hneg : NegSSSPSpec M neg)
    {stflow : (D → ℤ) → Finset V → Finset V → D → ℤ} (hst : STFlowSpec M stflow) :
    C2SOut M U f (c2sImpl M mssp fr neg stflow U f π H) π.verts H := by
  classical
  unfold c2sImpl
  split_ifs with he
  swap
  · -- no darts at all
    have hD := isEmpty_of_no_dart hM he
    have h0 : ∀ (h : D → ℤ) v, M.div h v = 0 := fun h v => by simp [CombMap.div]
    refine ⟨hf, fun v _ _ => rfl, fun v _ => by rw [h0], fun v _ => le_rfl,
      ⟨∅, fun v hv => by simp [mem_posSet, h0] at hv, by simp, fun d => isEmptyElim d⟩⟩
  generalize hC : π.verts = C at *
  generalize hCp : fwdReach M U f (posSet M f C) C = Cp at hpre
  have hDel : delSet M U f C = C \ Cp := by rw [delSet, hCp]
  have hβ : c2sBeta M U f C = fun v => if v ∈ Cp then - M.div f v else 0 := by
    funext v; rw [c2sBeta, hCp]
  rw [hβ, hDel]
  have hcap : c2sCap M U f C = fun d => if d ∈ incSet M (C \ Cp) then 0 else U d - f d := by
    funext d; rw [c2sCap, hDel]
  rw [hcap]
  generalize hDel' : C \ Cp = Del
  generalize hinc : incSet M Del = inc
  have hincD : ∀ d, d ∈ inc ↔ M.tail d ∈ Del ∨ M.head d ∈ Del := fun d => by
    rw [← hinc]; simp [incSet]
  have hrinc : ∀ d, M.rev d ∈ inc ↔ d ∈ inc := fun d => by rw [← hinc]; exact rev_mem_incSet
  -- the reachable set `R` and `C⁺ = C ∩ R`
  let R : Finset V := univ.filter fun v => ∃ x ∈ posSet M f C,
    Relation.ReflTransGen (ResAdj M U f) x v
  have hmemCp : ∀ v, v ∈ Cp ↔ v ∈ C ∧ v ∈ R := fun v => by
    rw [← hCp]; simp [fwdReach, R]
  have hRcl : Closed M U f R := by
    intro d hd1 hd2
    simp only [R, mem_filter, mem_univ, true_and] at hd1 hd2
    obtain ⟨x, hx, hr⟩ := hd1
    by_contra hne
    exact hd2 ⟨x, hx, hr.tail ⟨d, rfl, rfl, lt_of_le_of_ne (hf.le_cap d) hne⟩⟩
  have hposCp : posSet M f C ⊆ Cp := fun v hv =>
    (hmemCp v).2 ⟨posSet_subset hv, by simp only [R, mem_filter, mem_univ, true_and]; exact ⟨v, hv, .refl⟩⟩
  have hDelR : ∀ v ∈ Del, v ∉ R := fun v hv hvR => by
    rw [← hDel'] at hv; obtain ⟨h1, h2⟩ := mem_sdiff.1 hv; exact h2 ((hmemCp v).2 ⟨h1, hvR⟩)
  have hDelC : ∀ v ∈ Del, v ∈ C := fun v hv => by rw [← hDel'] at hv; exact (mem_sdiff.1 hv).1
  have hDelf : ∀ v ∈ Del, 0 ≤ M.div f v := fun v hv => by
    by_contra hn
    have := hposCp (mem_posSet.2 ⟨hDelC v hv, by omega⟩)
    exact hDelR v hv ((hmemCp v).1 this).2
  have hCpC : ∀ v ∈ Cp, v ∈ C := fun v hv => ((hmemCp v).1 hv).1
  have hnCp : ∀ v, v ∉ Cp → v ∉ C ∨ v ∈ Del := fun v hv => by
    by_cases hC : v ∈ C
    · right; rw [← hDel']; exact mem_sdiff.2 ⟨hC, hv⟩
    · left; exact hC
  -- line 7: the maximum flow
  obtain ⟨πH, rfl⟩ := hH
  have hc₁ : ∀ d, 0 ≤ (fun d => if d ∈ inc then 0 else U d - f d) d := fun d => by
    simp only; split_ifs
    · exact le_rfl
    · have := hf.le_cap d; omega
  have hst' := hst (fun d => if d ∈ inc then 0 else U d - f d) π πH hc₁ (by rw [hC]; exact hCH)
  rw [hC] at hst'
  generalize stflow (fun d => if d ∈ inc then 0 else U d - f d) C πH.verts = g at hst' ⊢
  generalize πH.verts = H at *
  obtain ⟨gps, gcons, gsink, ⟨W, hCW, hWH, hWcl⟩⟩ := hst'
  -- `g` vanishes on the deleted darts
  have hg0 : ∀ d ∈ inc, g d = 0 := by
    intro d hd
    have h1 := gps.le_cap d
    have h2 := gps.le_cap (M.rev d)
    rw [gps.antisymm d] at h2
    simp only [hd, (hrinc d).2 hd, ite_true] at h1 h2
    omega
  have hgDel : ∀ v ∈ Del, M.div g v = 0 := by
    intro v hv
    refine sum_eq_zero fun d hd => hg0 d ((hincD d).2 (Or.inl ?_))
    simp only [mem_filter, mem_univ, true_and] at hd; rw [hd]; exact hv
  have hf₁ : IsPseudo M U (f + g) := by
    refine ⟨fun d => by simp only [Pi.add_apply, hf.antisymm d, gps.antisymm d]; ring,
      fun d => ?_⟩
    have a := gps.le_cap d; have b := hf.le_cap d
    simp only [Pi.add_apply]
    split_ifs at a <;> omega
  -- `R` stays closed
  have hR₁ : Closed M U (f + g) R := by
    refine hRcl.of_sum_le hf hf₁ ?_
    simp only [div_add', sum_add_distrib]
    suffices 0 ≤ ∑ v ∈ R, M.div g v by linarith
    have htot := M.sum_div gps.antisymm
    have hout : ∑ v ∈ univ \ R, M.div g v ≤ 0 := sum_nonpos fun v hv => by
      have hvR : v ∉ R := (mem_sdiff.1 hv).2
      by_cases hvH : v ∈ H
      · exact gsink v hvH
      · by_cases hvC : v ∈ C
        · have : v ∈ Del := by
            rw [← hDel']; exact mem_sdiff.2 ⟨hvC, fun h => hvR ((hmemCp v).1 h).2⟩
          rw [hgDel v this]
        · rw [gcons v hvC hvH]
    have := sum_sdiff (s₁ := R) (s₂ := univ) (f := fun v => M.div g v) (subset_univ R)
    linarith
  have hY₁ : Closed M U (f + g) (W ∩ R) := by
    intro d hd1 hd2
    rw [mem_inter] at hd1
    by_cases hhR : M.head d ∈ R
    · have hhW : M.head d ∉ W := fun h => hd2 (mem_inter.2 ⟨h, hhR⟩)
      have hni : d ∉ inc := by
        rw [hincD]; push Not
        exact ⟨fun h => hDelR _ h hd1.2, fun h => hDelR _ h hhR⟩
      have := hWcl d hd1.1 hhW
      simp only [hni, ite_false] at this
      simp only [Pi.add_apply]; omega
    · exact hR₁ d hd1.2 hhR
  have hCpY₁ : Cp ⊆ W ∩ R := fun v hv =>
    mem_inter.2 ⟨hCW (hCpC v hv), ((hmemCp v).1 hv).2⟩
  have hY₁H : Disjoint (W ∩ R) H := disjoint_of_subset_left inter_subset_left hWH
  -- line 9
  obtain ⟨p1, p2, p3, ⟨Z, hZ1, hZ2, hZ3⟩⟩ := fixFrozen_spec (e := fun v => (he v).choose)
    (he := fun v => (he v).choose_spec) hM hU hf₁ hmssp hfr hneg Del
  rw [hinc] at p2 hZ3
  rw [hC] at p3 hZ1 hZ2
  generalize fixFrozen M (fun v => (he v).choose) (fun v => (he v).choose_spec) mssp fr neg U
    (f + g) π Del = f₂ at p1 p2 p3 hZ1 hZ2 hZ3 ⊢
  have hdiv₂ : ∀ v, v ∉ Cp → M.div f₂ v = M.div f v + M.div g v := fun v hv => by
    rw [p3 v (hnCp v hv), div_add']
  have hY₁' : Closed M U f₂ (W ∩ R) :=
    hY₁.src (X := Cp) (Z := ∅) hf₁ p1 hCpY₁ (fun v hv _ => p3 v (hnCp v hv)) (by simp)
  have hY₂ : Closed M U f₂ (Z ∩ (W ∩ R)) := by
    intro d hd1 hd2
    rw [mem_inter] at hd1
    by_cases hh : M.head d ∈ W ∩ R
    · have hhZ : M.head d ∉ Z := fun h => hd2 (mem_inter.2 ⟨h, hh⟩)
      have hni : d ∉ inc := by
        rw [hincD]; push Not
        exact ⟨fun h => hDelR _ h (mem_inter.1 hd1.2).2, fun h => hDelR _ h (mem_inter.1 hh).2⟩
      exact hZ3 d hni hd1.1 hhZ
    · exact hY₁' d hd1.2 hh
  have hgC : ∀ v, v ∉ Cp → v ∉ H → M.div g v = 0 := fun v h1 h2 => by
    rcases hnCp v h1 with h | h
    · exact gcons v h h2
    · exact hgDel v h
  have hpos₂ : posSet M f₂ C ⊆ Z ∩ (W ∩ R) := by
    intro v hv
    obtain ⟨hvC, hlt⟩ := mem_posSet.1 hv
    refine mem_inter.2 ⟨hZ1 (mem_filter.2 ⟨hvC, hlt⟩), hCpY₁ ?_⟩
    by_contra hn
    rcases hnCp v hn with h | h
    · exact h hvC
    · have := hdiv₂ v hn; rw [hgDel v h] at this; have := hDelf v h; omega
  have hY₂H : Disjoint (Z ∩ (W ∩ R)) H := disjoint_of_subset_left inter_subset_right hY₁H
  have hY₂N : Disjoint (Z ∩ (W ∩ R)) (negSet M f₂ C) := by
    rw [disjoint_left]; intro v hv hv'
    exact disjoint_left.1 hZ2 (mem_inter.1 hv).1 hv'
  -- line 10
  have hβ0 : ∀ v, 0 ≤ (if v ∈ Cp then - M.div f v else 0) := fun v => by
    split_ifs with h
    · have := hpre v h; omega
    · exact le_rfl
  have hc' : ∀ d, 0 ≤ (U - f) d := fun d => by
    have := hf.le_cap d; simp only [Pi.sub_apply]; omega
  have hg₂ : IsPseudo M (U - f) (f₂ - f) :=
    ⟨fun d => by simp only [Pi.sub_apply, p1.antisymm d, hf.antisymm d]; ring,
      fun d => by have := p1.le_cap d; simp only [Pi.sub_apply]; omega⟩
  obtain ⟨q1, -, q3, q4, -⟩ := pushFwd_spec (W := univ) hM hfr hc' hg₂
    (β := fun v => if v ∈ Cp then - M.div f v else 0) (Fr := ∅)
    (fun d _ h => absurd (mem_univ _) h) (fun v h => absurd (mem_univ v) h)
    (fun v _ _ => hβ0 v)
  generalize pushFwd M fr (fun v => if v ∈ Cp then - M.div f v else 0) ∅ (f₂ - f) = g₃
    at q1 q3 q4 ⊢
  have hd3 : ∀ v, M.div (f + g₃) v = M.div f v + M.div g₃ v := fun v => div_add' f g₃ v
  have r3 : ∀ v, M.div g₃ v ≤ (if v ∈ Cp then - M.div f v else 0) :=
    fun v => q3 v (notMem_empty v)
  have r4 : ∀ v, min (M.div f₂ v - M.div f v) (if v ∈ Cp then - M.div f v else 0) ≤
      M.div g₃ v := fun v => by rw [← div_sub']; exact q4 v (notMem_empty v)
  have hf₃ : IsPseudo M U (f + g₃) :=
    ⟨fun d => by simp only [Pi.add_apply, hf.antisymm d, q1.antisymm d]; ring,
      fun d => by have := q1.le_cap d; simp only [Pi.add_apply, Pi.sub_apply] at this ⊢; omega⟩
  refine ⟨hf₃, fun v h1 h2 => ?_, fun v hv => ?_, fun v hv => ?_, ?_⟩
  · rw [hCp] at h1
    have a := r3 v; have b := r4 v
    simp only [h1, ite_false] at a b
    rw [hdiv₂ v h1, hgC v h1 h2] at b
    rw [hd3]; omega
  · rw [hCp] at hv
    have a := r3 v
    simp only [hv, ite_true] at a
    rw [hd3]; omega
  · have hvCp : v ∉ Cp := fun h => disjoint_left.1 hCH (hCpC v h) hv
    have a := r3 v
    simp only [hvCp, ite_false] at a
    rw [hd3]; omega
  · refine ⟨Z ∩ (W ∩ R), fun v hv => ?_, hY₂H, ?_⟩
    · obtain ⟨hvC, hlt⟩ := mem_posSet.1 hv
      rw [hd3] at hlt
      have hvCp : v ∈ Cp := by
        by_contra hn
        rcases hnCp v hn with h | h
        · exact h hvC
        · have b := r4 v; simp only [hn, ite_false] at b
          rw [hdiv₂ v hn, hgDel v h] at b; have := hDelf v h; omega
      have a := r3 v; have b := r4 v
      simp only [hvCp, ite_true] at a b
      exact hpos₂ (mem_posSet.2 ⟨hvC, by omega⟩)
    · refine hY₂.snk (X := negSet M f₂ C) (Z := univ \ negSet M f₂ C) p1 hf₃ hY₂N.symm
        (fun v h1 h2 => absurd (mem_sdiff.2 ⟨mem_univ v, h1⟩) h2) (fun v hv => ?_)
      have hvN : v ∉ negSet M f₂ C := (mem_sdiff.1 hv).2
      rw [hd3]
      have b := r4 v
      by_cases hvCp : v ∈ Cp
      · simp only [hvCp, ite_true] at b
        have : M.div f₂ v ≤ 0 := by
          by_contra h; exact hvN (mem_negSet.2 ⟨hCpC v hvCp, by omega⟩)
        omega
      · simp only [hvCp, ite_false] at b
        have : M.div f₂ v - M.div f v ≤ 0 := by
          rw [hdiv₂ v hvCp]
          by_cases hvH : v ∈ H
          · have := gsink v hvH; omega
          · rw [hgC v hvCp hvH]; omega
        omega

/-! ### SingleSourceToCycleLimitedMaxFlow: the reversed flow -/

lemma resAdj_mirror {U f : D → ℤ} (hf : M.IsAntisymm f) {a b : V} :
    ResAdj M (fun d => U (M.rev d)) (-f) a b ↔ ResAdj M U f b a := by
  constructor
  · rintro ⟨d, h1, h2, h3⟩
    refine ⟨M.rev d, by rw [CombMap.tail_rev, h2], by rw [CombMap.head_rev, h1], ?_⟩
    rw [hf d]; simpa using h3
  · rintro ⟨d, h1, h2, h3⟩
    refine ⟨M.rev d, by rw [CombMap.tail_rev, h2], by rw [CombMap.head_rev, h1], ?_⟩
    simp only [Pi.neg_apply, M.rev_rev, hf d, neg_neg]; exact h3

lemma posSet_neg (f : D → ℤ) (C : Finset V) : posSet M (-f) C = negSet M f C := by
  ext v; simp only [mem_posSet, mem_negSet, div_neg']; constructor <;> rintro ⟨h1, h2⟩ <;>
    exact ⟨h1, by omega⟩

lemma fwdReach_mirror {U f : D → ℤ} (hf : M.IsAntisymm f) (X C : Finset V) :
    fwdReach M (fun d => U (M.rev d)) (-f) X C = bwdReach M U f X C := by
  classical
  have e : ResAdj M (fun d => U (M.rev d)) (-f) = Function.swap (ResAdj M U f) := by
    funext a b; exact propext (resAdj_mirror hf)
  ext v
  simp only [fwdReach, bwdReach, mem_filter, e, Relation.reflTransGen_swap]

lemma noPath_mirror {U f : D → ℤ} (hf : M.IsAntisymm f) {A B : Finset V}
    (h : NoPath M (fun d => U (M.rev d)) (-f) A B) : NoPath M U f B A := by
  obtain ⟨Y, h1, h2, h3⟩ := h
  refine ⟨univ \ Y, fun v hv => mem_sdiff.2 ⟨mem_univ v, disjoint_right.1 h2 hv⟩,
    disjoint_of_subset_right h1 disjoint_sdiff_self_left, fun d hd1 hd2 => ?_⟩
  have := h3 (M.rev d) (by simpa using hd2) (by simpa using hd1)
  simp only [Pi.neg_apply, M.rev_rev, hf d, neg_neg] at this
  exact this

variable (M) in
/-- **SingleSourceToCycleLimitedMaxFlow**: CycleToSingleSinkLimitedMaxFlow on the reversed flow. -/
noncomputable def s2cImpl (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F)
    (neg : (D → ℤ) → Option (F → ℤ)) (stflow : (D → ℤ) → Finset V → Finset V → D → ℤ)
    (U f : D → ℤ) (π : SPath M) (H : Finset V) : D → ℤ :=
  -(c2sImpl M mssp fr neg stflow (fun d => U (M.rev d)) (-f) π H)

/-- **SingleSourceToCycleLimitedMaxFlow meets its specification.** -/
theorem s2c_spec (hM : M.IsPlane) {U f : D → ℤ} (hU : ∀ d, 0 ≤ U d) (hf : IsPseudo M U f)
    {π : SPath M} {H : Finset V} (hCH : Disjoint π.verts H) (hH : ∃ πH : SPath M, πH.verts = H)
    (hpre : ∀ v ∈ bwdReach M U f (negSet M f π.verts) π.verts, 0 ≤ M.div f v)
    {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp π)
    {fr : FRFun F} (hfr : FRSpec fr) {neg : (D → ℤ) → Option (F → ℤ)} (hneg : NegSSSPSpec M neg)
    {stflow : (D → ℤ) → Finset V → Finset V → D → ℤ} (hst : STFlowSpec M stflow) :
    S2COut M U f (s2cImpl M mssp fr neg stflow U f π H) π.verts H := by
  have hf' : IsPseudo M (fun d => U (M.rev d)) (-f) :=
    ⟨fun d => by simp [hf.antisymm d], fun d => by
      have := hf.le_cap (M.rev d); rw [hf.antisymm d] at this; simp only [Pi.neg_apply]; omega⟩
  have hre := fwdReach_mirror (U := U) hf.antisymm (negSet M f π.verts) π.verts
  have o := c2s_spec hM (fun d => hU (M.rev d)) hf' hCH hH (fun v hv => by
      rw [posSet_neg, hre] at hv; rw [div_neg']; have := hpre v hv; omega)
    hmssp hfr hneg hst
  obtain ⟨o1, o2, o3, o4, o5⟩ := o
  rw [posSet_neg, hre] at o2 o3
  unfold s2cImpl
  generalize c2sImpl M mssp fr neg stflow (fun d => U (M.rev d)) (-f) π H = g at o1 o2 o3 o4 o5 ⊢
  have hg : M.IsAntisymm (-g) := fun d => by simp [o1.antisymm d]
  refine ⟨⟨hg, fun d => ?_⟩, fun v h1 h2 => ?_, fun v hv => ?_, fun v hv => ?_, ?_⟩
  · have := o1.le_cap (M.rev d); rw [o1.antisymm d] at this
    simp only [Pi.neg_apply, M.rev_rev] at this ⊢; omega
  · have := o2 v h1 h2; rw [div_neg'] at this; rw [div_neg']; omega
  · have := o3 v hv; rw [div_neg']; omega
  · have := o4 v hv; rw [div_neg'] at this; rw [div_neg']; omega
  · refine noPath_mirror hg ?_
    have e : negSet M (-g) π.verts = posSet M g π.verts := by
      rw [← posSet_neg, neg_neg]
    rw [e]; simpa using o5

end BKMNW

end PlanarFlow
