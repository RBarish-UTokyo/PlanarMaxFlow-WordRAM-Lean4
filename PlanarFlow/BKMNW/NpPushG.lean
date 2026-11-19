module

public import PlanarFlow.BKMNW.Main

/-!
# The subroutines of Algorithm 1 with any push-back meeting its specification

`impl` (`PlanarFlow/BKMNW/Main.lean`) implements lines 10 and 13 of Algorithm 1 with
`pushFwd M fr` (Appendix C), which makes **three classical choices**: the order in which the
darts leaving a vertex are reduced (`outDarts v = (univ.filter (tail · = v)).toList`, a
`Multiset.toList`, i.e. `Quot.out`), the order of the vertices of equal height
(`(univ : Finset V).toList.mergeSort`) and the root of the cancellation (`Nonempty.some` in
`cancel`). The result of `pushFwd` depends in general on the order of the reductions (two
positive darts leaving the same vertex, an excess smaller than their flows), and the
cancellation on its root, so **no program can be proved to output `pushFwd`, `frmImpl`,
`retImpl`, `c2sImpl` or `s2cImpl` exactly** (the value of `Quot.out` is not determined), which
the step specifications `C2SPSpecO'`, `S2CPSpecO'`, `RetPSpecO'`, `FrmPSpecO'` ask for. (The
pendant choice of `c2sImpl` is harmless, `c2sImpl_eq`, `FixIndep.lean`.)

This file abstracts the push-back: **`PushSpec M push`** is the conclusion of `pushFwd_spec`, and
`frmG`, `retG`, `c2sG`, `s2cG`, **`implG`** are `frmImpl`, `retImpl`, `c2sImpl`, `s2cImpl`, `impl`
with `push` in place of `pushFwd M fr` (the proofs are those of `PushBack.lean`,
`CycleSink.lean`, `Main.lean` with `pushFwd_spec` replaced by `PushSpec`):

* `pushSpec_pushFwd` (`pushFwd M fr` meets `PushSpec`); `impl_eq_implG` (`impl` is
  `implG (pushFwd M fr)`);
* `frmG_spec`, `retG_spec`, `c2sG_spec`, `s2cG_spec`, **`implG_spec`**: the subroutines meet the
  specifications of Algorithm 1 for any push-back meeting `PushSpec`.

A machine push-back with explicit orders is in `NpPushL.lean`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-- The type of a push-back procedure: bounds `β`, free vertices `Fr`, flow. -/
abbrev PushFn (D V : Type*) := (V → ℤ) → Finset V → (D → ℤ) → D → ℤ

variable (M) in
/-- **The specification of the push-back** (the conclusion of `pushFwd_spec`). -/
def PushSpec (push : PushFn D V) : Prop :=
  ∀ {c g : D → ℤ}, (∀ d, 0 ≤ c d) → IsPseudo M c g → ∀ {β : V → ℤ} {Fr W : Finset V},
    (∀ d, M.tail d ∈ W → M.head d ∉ W → g d ≤ 0) →
    (∀ v, v ∉ W → v ∉ Fr → M.div g v ≤ β v) → (∀ v ∈ W, v ∉ Fr → 0 ≤ β v) →
    IsPseudo M c (push β Fr g) ∧ Conf g (push β Fr g) ∧
      (∀ v, v ∉ Fr → M.div (push β Fr g) v ≤ β v) ∧
      (∀ v, v ∉ Fr → min (M.div g v) (β v) ≤ M.div (push β Fr g) v) ∧
      (∀ v ∈ Fr, M.div g v ≤ M.div (push β Fr g) v)

/-- `pushFwd` meets `PushSpec`. -/
theorem pushSpec_pushFwd (hM : M.IsPlane) {fr : FRFun F} (hfr : FRSpec fr) :
    PushSpec M (pushFwd M fr) := by
  intro c g hc hg β Fr W hW hout hin
  exact pushFwd_spec hM hfr hc hg hW hout hin

/-! ### Line 13 with any push-back -/

variable (M) in
/-- **Pushing flow back from the sinks `T`** so that the vertices of `X` become balanced. -/
noncomputable def frmG (push : PushFn D V) (f : D → ℤ) (T X : Finset V) : D → ℤ :=
  push (fun v => if v ∈ X then 0 else M.div f v) T f

variable (M) in
/-- **Pushing excess back to the sources `S`** so that the vertices of `X` become balanced: the
push-back from the sinks on the reversed flow. -/
noncomputable def retG (push : PushFn D V) (f : D → ℤ) (X S : Finset V) : D → ℤ :=
  -(frmG M push (-f) S X)

/-- **The push-back from the sinks meets `FromOut`.** -/
theorem frmG_spec {push : PushFn D V} (hpush : PushSpec M push) {U f : D → ℤ}
    (hU : ∀ d, 0 ≤ U d) (hf : IsPseudo M U f) {T X : Finset V} (hXT : Disjoint X T)
    (hX : ∀ v ∈ X, 0 ≤ M.div f v)
    (hW : ∃ W, X ⊆ W ∧ Closed M U f (univ \ W) ∧ ∀ v ∈ W, v ∉ T → v ∉ X → M.div f v = 0) :
    FromOut M U f (frmG M push f T X) T X := by
  obtain ⟨W, hXW, hcl, hbal⟩ := hW
  obtain ⟨p1, -, p3, p4, p5⟩ := hpush (W := W) hU hf
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
theorem retG_spec {push : PushFn D V} (hpush : PushSpec M push) {U f : D → ℤ}
    (hU : ∀ d, 0 ≤ U d) (hf : IsPseudo M U f) {X S : Finset V} (hXS : Disjoint X S)
    (hX : ∀ v ∈ X, M.div f v ≤ 0)
    (hW : ∃ W, X ⊆ W ∧ Closed M U f W ∧ ∀ v ∈ W, v ∉ S → v ∉ X → M.div f v = 0) :
    RetOut M U f (retG M push f X S) X S := by
  obtain ⟨W, hXW, hcl, hbal⟩ := hW
  have hf' : IsPseudo M (fun d => U (M.rev d)) (-f) :=
    ⟨fun d => by simp [hf.antisymm d], fun d => by
      have := hf.le_cap (M.rev d); rw [hf.antisymm d] at this; simp only [Pi.neg_apply]; omega⟩
  have o := frmG_spec hpush (fun d => hU (M.rev d)) hf' hXS (fun v hv => by
      rw [div_neg']; have := hX v hv; omega)
    ⟨W, hXW, fun d h1 h2 => by
      have := hcl (M.rev d) (by simpa using h2) (by simpa using h1)
      rw [hf.antisymm d] at this; simp only [Pi.neg_apply]; omega,
      fun v h1 h2 h3 => by rw [div_neg', hbal v h1 h2 h3, neg_zero]⟩
  obtain ⟨o1, o2, o3, o4⟩ := o
  unfold retG
  generalize frmG M push (-f) S X = g at o1 o2 o3 o4
  refine ⟨⟨fun d => by simp [o1.antisymm d], fun d => ?_⟩, fun v hv => ?_, fun v h1 h2 => ?_,
    fun v hv => ?_⟩
  · have := o1.le_cap (M.rev d); rw [o1.antisymm d] at this
    simp only [Pi.neg_apply, M.rev_rev] at this ⊢; omega
  · rw [div_neg', o2 v hv, neg_zero]
  · rw [div_neg', o3 v h1 h2, div_neg', neg_neg]
  · have := o4 v hv; rw [div_neg'] at this ⊢; omega


variable (M) in
/-- **CycleToSingleSinkLimitedMaxFlow** (Algorithm 5) with the push-back `push`. -/
noncomputable def c2sG (push : PushFn D V) (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F)
    (neg : (D → ℤ) → Option (F → ℤ)) (stflow : (D → ℤ) → Finset V → Finset V → D → ℤ)
    (U f : D → ℤ) (π : SPath M) (H : Finset V) : D → ℤ := by
  classical
  exact if he : ∀ v, ∃ d, M.tail d = v then
    f + push (c2sBeta M U f π.verts) ∅
      (fixFrozen M (fun v => (he v).choose) (fun v => (he v).choose_spec) mssp fr neg U
        (f + stflow (c2sCap M U f π.verts) π.verts H) π (delSet M U f π.verts) - f)
  else f

/-- **CycleToSingleSinkLimitedMaxFlow with any push-back meeting `PushSpec` meets its
specification** (Lemma F.1). -/
theorem c2sG_spec (hM : M.IsPlane) {push : PushFn D V} (hpush : PushSpec M push) {U f : D → ℤ} (hU : ∀ d, 0 ≤ U d) (hf : IsPseudo M U f)
    {π : SPath M} {H : Finset V} (hCH : Disjoint π.verts H) (hH : ∃ πH : SPath M, πH.verts = H)
    (hpre : ∀ v ∈ fwdReach M U f (posSet M f π.verts) π.verts, M.div f v ≤ 0)
    {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp π)
    {fr : FRFun F} (hfr : FRSpec fr) {neg : (D → ℤ) → Option (F → ℤ)} (hneg : NegSSSPSpec M neg)
    {stflow : (D → ℤ) → Finset V → Finset V → D → ℤ} (hst : STFlowSpec M stflow) :
    C2SOut M U f (c2sG M push mssp fr neg stflow U f π H) π.verts H := by
  classical
  unfold c2sG
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
  obtain ⟨q1, -, q3, q4, -⟩ := hpush (W := univ) hc' hg₂
    (β := fun v => if v ∈ Cp then - M.div f v else 0) (Fr := ∅)
    (fun d _ h => absurd (mem_univ _) h) (fun v h => absurd (mem_univ v) h)
    (fun v _ _ => hβ0 v)
  generalize push (fun v => if v ∈ Cp then - M.div f v else 0) ∅ (f₂ - f) = g₃
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

variable (M) in
/-- **SingleSourceToCycleLimitedMaxFlow** with the push-back `push`. -/
noncomputable def s2cG (push : PushFn D V) (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F)
    (neg : (D → ℤ) → Option (F → ℤ)) (stflow : (D → ℤ) → Finset V → Finset V → D → ℤ)
    (U f : D → ℤ) (π : SPath M) (H : Finset V) : D → ℤ :=
  -(c2sG M push mssp fr neg stflow (fun d => U (M.rev d)) (-f) π H)

/-- **SingleSourceToCycleLimitedMaxFlow meets its specification.** -/
theorem s2cG_spec (hM : M.IsPlane) {push : PushFn D V} (hpush : PushSpec M push) {U f : D → ℤ} (hU : ∀ d, 0 ≤ U d) (hf : IsPseudo M U f)
    {π : SPath M} {H : Finset V} (hCH : Disjoint π.verts H) (hH : ∃ πH : SPath M, πH.verts = H)
    (hpre : ∀ v ∈ bwdReach M U f (negSet M f π.verts) π.verts, 0 ≤ M.div f v)
    {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp π)
    {fr : FRFun F} (hfr : FRSpec fr) {neg : (D → ℤ) → Option (F → ℤ)} (hneg : NegSSSPSpec M neg)
    {stflow : (D → ℤ) → Finset V → Finset V → D → ℤ} (hst : STFlowSpec M stflow) :
    S2COut M U f (s2cG M push mssp fr neg stflow U f π H) π.verts H := by
  have hf' : IsPseudo M (fun d => U (M.rev d)) (-f) :=
    ⟨fun d => by simp [hf.antisymm d], fun d => by
      have := hf.le_cap (M.rev d); rw [hf.antisymm d] at this; simp only [Pi.neg_apply]; omega⟩
  have hre := fwdReach_mirror (U := U) hf.antisymm (negSet M f π.verts) π.verts
  have o := c2sG_spec hM hpush (fun d => hU (M.rev d)) hf' hCH hH (fun v hv => by
      rw [posSet_neg, hre] at hv; rw [div_neg']; have := hpre v hv; omega)
    hmssp hfr hneg hst
  obtain ⟨o1, o2, o3, o4, o5⟩ := o
  rw [posSet_neg, hre] at o2 o3
  unfold s2cG
  generalize c2sG M push mssp fr neg stflow (fun d => U (M.rev d)) (-f) π H = g at o1 o2 o3 o4 o5 ⊢
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

variable (M) in
/-- **The subroutines of Algorithm 1 with the push-back `push`.** -/
noncomputable def implG (push : PushFn D V) (mssp : List D → (D → ℤ) → F → F → Option ℤ)
    (fr : FRFun F) (negSSSP : (D → ℤ) → Option (F → ℤ))
    (stflow : (D → ℤ) → Finset V → Finset V → D → ℤ) : NodeOracles M where
  leaf U S T A := leafSolve M U S T A
  fix U f π := fixPath M U f π mssp fr negSSSP
  c2s U f π H := c2sG M push mssp fr negSSSP stflow U f π H
  s2c U f π H := s2cG M push mssp fr negSSSP stflow U f π H
  ret _ f X S := retG M push f X S
  frm _ f T X := frmG M push f T X

/-- `impl` is `implG` with `pushFwd`. -/
theorem impl_eq_implG (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F)
    (negSSSP : (D → ℤ) → Option (F → ℤ)) (stflow : (D → ℤ) → Finset V → Finset V → D → ℤ) :
    impl M mssp fr negSSSP stflow = implG M (pushFwd M fr) mssp fr negSSSP stflow := rfl

/-- **The subroutines with any push-back meeting `PushSpec` meet the specifications of
Algorithm 1**, from the specifications of the planar subroutines. -/
theorem implG_spec (hM : M.IsPlane) {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {push : PushFn D V}
    (hpush : PushSpec M push) {mssp : List D → (D → ℤ) → F → F → Option ℤ}
    (hmssp : MSSPSpec M mssp) {fr : FRFun F} (hfr : FRSpec fr)
    {negSSSP : (D → ℤ) → Option (F → ℤ)} (hneg : NegSSSPSpec M negSSSP)
    {stflow : (D → ℤ) → Finset V → Finset V → D → ℤ} (hst : STFlowSpec M stflow) :
    (implG M push mssp fr negSSSP stflow).Spec u := by
  have hcap : ∀ (P : Finset D) d, 0 ≤ capOn u P d := fun P d => by
    unfold capOn; split_ifs
    · exact hu d
    · exact le_rfl
  exact ⟨fun Q S T A hQ hQ2 hST hSA hTA => leafSolve_spec hu hQ hQ2 hST hSA hTA,
    fun P f π hf => fixPath_spec hM (hcap P) hf π (hmssp π) hfr hneg,
    fun P f π H hf h1 h2 h3 => c2sG_spec hM hpush (hcap P) hf h1 h2 h3 (hmssp π) hfr hneg hst,
    fun P f π H hf h1 h2 h3 => s2cG_spec hM hpush (hcap P) hf h1 h2 h3 (hmssp π) hfr hneg hst,
    fun P f X S hf h1 h2 h3 => retG_spec hpush (hcap P) hf h1 h2 h3,
    fun P f T X hf h1 h2 h3 => frmG_spec hpush (hcap P) hf h1 h2 h3⟩

end BKMNW

end PlanarFlow
