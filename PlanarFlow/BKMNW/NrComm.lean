module

public import PlanarFlow.BKMNW.NpPushC

/-!
# The visits of the push-back in any topological order

`pushFwdL M fr r ord outs` visits the vertices in the order `ord g` (for `pchL`, the vertices
stably sorted by their height `rk`). A machine computes a topological order more easily (Kahn's
algorithm) than this particular one. The visits of two vertices with no positive dart between
them commute, so **every topological order gives the same result**:

* `nr_fold_out` (the reductions along `ds` change only the darts of `ds` and their reverses),
  `nr_fold_zero` (nor a dart `e` with `g e ≤ 0`, `g (rev e) ≤ 0`), `nr_fold_local` (the result on
  those darts depends only on `g` there);
* `nr_push_out`, `nr_push_zero`, `nr_push_local`, `nr_push_div`: the same for one visit
  `pushAtL`, with `touch v e` (`e` leaves or enters `v`);
* **`nr_push_comm`**: two visits commute when no dart between the two vertices is positive;
* **`nr_fold_perm`**: the visits along two orders, both permutations without duplicates and
  topological for an acyclic `g₀`, from a flow conformal to `g₀`, agree;
* **`nr_pushFwdL_eq`**: `pushFwdL M fr r ord outs β Fr g` is the fold of the visits along any
  topological order of the cancelled flow `cancelR M fr r g` listing every vertex once.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-! ### The reductions along a list -/

/-- The reductions change only the darts of the list and their reverses. -/
lemma nr_fold_out : ∀ (ds : List D) (g : D → ℤ) (rem : ℤ) (e : D), e ∉ ds → M.rev e ∉ ds →
    (ds.foldl (redStep M) (g, rem)).1 e = g e
  | [], g, rem, e, _, _ => rfl
  | d :: ds, g, rem, e, h1, h2 => by
    rw [List.foldl_cons]
    have hd : e ≠ d := fun h => h1 (h ▸ List.mem_cons_self ..)
    have hd' : e ≠ M.rev d := fun h => h2 (by rw [h, M.rev_rev]; exact List.mem_cons_self ..)
    rw [nr_fold_out ds _ _ e (fun h => h1 (List.mem_cons_of_mem _ h))
      (fun h => h2 (List.mem_cons_of_mem _ h))]
    unfold redStep; dsimp only; split_ifs
    · exact setPair_of_ne _ _ hd hd'
    · rfl

/-- The reductions do not change a dart carrying no positive flow either way. -/
lemma nr_fold_zero (e : D) : ∀ (ds : List D) (g : D → ℤ) (rem : ℤ), g e ≤ 0 → g (M.rev e) ≤ 0 →
    (ds.foldl (redStep M) (g, rem)).1 e = g e
  | [], g, rem, _, _ => rfl
  | d :: ds, g, rem, h1, h2 => by
    rw [List.foldl_cons]
    have key : (redStep M (g, rem) d).1 e = g e ∧
        (redStep M (g, rem) d).1 (M.rev e) = g (M.rev e) := by
      unfold redStep; dsimp only
      split_ifs with hc
      · have hd : d ≠ e := fun h => by subst h; omega
        have hd' : d ≠ M.rev e := fun h => by subst h; omega
        refine ⟨setPair_of_ne _ _ (Ne.symm hd) (fun h => hd' (by rw [h, M.rev_rev])), ?_⟩
        exact setPair_of_ne _ _ (Ne.symm hd') (fun h => hd (M.rev_injective h.symm))
      · exact ⟨rfl, rfl⟩
    rw [nr_fold_zero e ds _ _ (by rw [key.1]; exact h1) (by rw [key.2]; exact h2), key.1]

/-- The reductions on two flows agreeing on the darts of the list and their reverses agree
there, with the same remainder. -/
lemma nr_fold_local : ∀ (ds : List D) (g g' : D → ℤ) (rem : ℤ),
    (∀ e, e ∈ ds ∨ M.rev e ∈ ds → g e = g' e) →
    (ds.foldl (redStep M) (g, rem)).2 = (ds.foldl (redStep M) (g', rem)).2 ∧
      ∀ e, e ∈ ds ∨ M.rev e ∈ ds →
        (ds.foldl (redStep M) (g, rem)).1 e = (ds.foldl (redStep M) (g', rem)).1 e
  | [], g, g', rem, h => ⟨rfl, fun e he => h e he⟩
  | d :: ds, g, g', rem, h => by
    simp only [List.foldl_cons]
    have hdd : g d = g' d := h d (Or.inl (List.mem_cons_self ..))
    have hstep : (redStep M (g, rem) d).2 = (redStep M (g', rem) d).2 ∧
        ∀ e, e ∈ d :: ds ∨ M.rev e ∈ d :: ds →
          (redStep M (g, rem) d).1 e = (redStep M (g', rem) d).1 e := by
      unfold redStep; dsimp only
      simp only [hdd]
      split_ifs with hc
      · refine ⟨rfl, fun e he => ?_⟩
        simp only [setPair]
        split_ifs
        · rfl
        · rfl
        · exact h e he
      · exact ⟨rfl, h⟩
    have e2 : (redStep M (g, rem) d) = ((redStep M (g, rem) d).1, (redStep M (g, rem) d).2) :=
      rfl
    have e2' : (redStep M (g', rem) d) =
        ((redStep M (g', rem) d).1, (redStep M (g', rem) d).2) := rfl
    rw [e2, e2', hstep.1]
    have ih := nr_fold_local ds _ _ (redStep M (g', rem) d).2 fun e he => hstep.2 e (by
      rcases he with he | he
      · exact Or.inl (List.mem_cons_of_mem _ he)
      · exact Or.inr (List.mem_cons_of_mem _ he))
    refine ⟨ih.1, fun e he => ?_⟩
    by_cases h' : e ∈ ds ∨ M.rev e ∈ ds
    · exact ih.2 e h'
    · push Not at h'
      rw [nr_fold_out ds _ _ e h'.1 h'.2, nr_fold_out ds _ _ e h'.1 h'.2]
      exact hstep.2 e he

/-! ### One visit -/

variable (M) in
/-- The dart `e` leaves or enters `v`. -/
def touch (v : V) (e : D) : Prop := M.tail e = v ∨ M.head e = v

lemma touch_iff {outs : V → List D} (houts : OutsOK M outs) (v : V) (e : D) :
    touch M v e ↔ e ∈ outs v ∨ M.rev e ∈ outs v := by
  rw [(houts v).2, (houts v).2, M.tail_rev]; rfl

lemma nr_push_out {outs : V → List D} (houts : OutsOK M outs) (β : V → ℤ) (Fr : Finset V)
    (g : D → ℤ) (v : V) (e : D) (he : ¬ touch M v e) : pushAtL M outs β Fr g v e = g e := by
  rw [touch_iff houts] at he
  push Not at he
  unfold pushAtL; split_ifs
  · exact nr_fold_out _ _ _ e he.1 he.2
  · rfl

lemma nr_push_zero {outs : V → List D} (β : V → ℤ) (Fr : Finset V) (g : D → ℤ) (v : V)
    (e : D) (h1 : g e ≤ 0) (h2 : g (M.rev e) ≤ 0) : pushAtL M outs β Fr g v e = g e := by
  unfold pushAtL; split_ifs
  · exact nr_fold_zero e _ _ _ h1 h2
  · rfl

lemma nr_push_div {outs : V → List D} (houts : OutsOK M outs) (g g' : D → ℤ) (v : V)
    (h : ∀ e, touch M v e → g e = g' e) : M.div g v = M.div g' v := by
  unfold CombMap.div
  exact sum_congr rfl fun e he => h e (Or.inl (mem_filter.1 he).2)

lemma nr_push_local {outs : V → List D} (houts : OutsOK M outs) (β : V → ℤ) (Fr : Finset V)
    (g g' : D → ℤ) (v : V) (h : ∀ e, touch M v e → g e = g' e) (e : D) (he : touch M v e) :
    pushAtL M outs β Fr g v e = pushAtL M outs β Fr g' v e := by
  have hdiv := nr_push_div houts g g' v h
  have h' : ∀ e, e ∈ outs v ∨ M.rev e ∈ outs v → g e = g' e :=
    fun e he => h e ((touch_iff houts v e).2 he)
  unfold pushAtL
  rw [hdiv]
  split_ifs
  · exact (nr_fold_local _ g g' _ h').2 e ((touch_iff houts v e).1 he)
  · exact h e he

/-- **Two visits commute** when no dart between the two vertices carries positive flow. -/
theorem nr_push_comm {outs : V → List D} (houts : OutsOK M outs) (β : V → ℤ) (Fr : Finset V)
    (g : D → ℤ) {v w : V} (hvw : v ≠ w)
    (hz : ∀ e, M.tail e = v → M.head e = w → g e ≤ 0 ∧ g (M.rev e) ≤ 0) :
    pushAtL M outs β Fr (pushAtL M outs β Fr g w) v =
      pushAtL M outs β Fr (pushAtL M outs β Fr g v) w := by
  -- the darts between `v` and `w` are kept by both visits
  have hbet : ∀ e, touch M v e → touch M w e → g e ≤ 0 ∧ g (M.rev e) ≤ 0 := by
    intro e h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.symm.trans h2) hvw
    · exact hz e h1 h2
    · have := hz (M.rev e) (by rw [M.tail_rev]; exact h1) (by rw [M.head_rev]; exact h2)
      rw [M.rev_rev] at this; exact this.symm
    · exact absurd (h1.symm.trans h2) hvw
  have kA : ∀ x y, x ≠ y → (∀ e, touch M x e → touch M y e → g e ≤ 0 ∧ g (M.rev e) ≤ 0) →
      ∀ e, touch M x e → pushAtL M outs β Fr g y e = g e := by
    intro x y hxy hb e hx
    by_cases hy : touch M y e
    · exact nr_push_zero β Fr g y e (hb e hx hy).1 (hb e hx hy).2
    · exact nr_push_out houts β Fr g y e hy
  have hbet' : ∀ e, touch M w e → touch M v e → g e ≤ 0 ∧ g (M.rev e) ≤ 0 :=
    fun e h1 h2 => hbet e h2 h1
  have kw := kA v w hvw hbet
  have kv := kA w v (Ne.symm hvw) hbet'
  funext e
  by_cases hv : touch M v e <;> by_cases hw : touch M w e
  · rw [nr_push_local houts β Fr _ g v (fun e h => kw e h) e hv,
      nr_push_local houts β Fr _ g w (fun e h => kv e h) e hw,
      nr_push_zero β Fr g v e (hbet e hv hw).1 (hbet e hv hw).2,
      nr_push_zero β Fr g w e (hbet e hv hw).1 (hbet e hv hw).2]
  · rw [nr_push_local houts β Fr _ g v (fun e h => kw e h) e hv,
      nr_push_out houts β Fr _ w e hw]
  · rw [nr_push_out houts β Fr _ v e hv,
      nr_push_local houts β Fr _ g w (fun e h => kv e h) e hw]
  · rw [nr_push_out houts β Fr _ v e hv, nr_push_out houts β Fr _ w e hw,
      nr_push_out houts β Fr _ w e hw, nr_push_out houts β Fr _ v e hv]

/-- One visit keeps the antisymmetry and the conformality to an acyclic `g₀`. -/
lemma nr_push_inv {outs : V → List D} (houts : OutsOK M outs) (β : V → ℤ) (Fr : Finset V)
    {g₀ g : D → ℤ} (ha₀ : M.IsAntisymm g₀) (hac : ∀ v, ¬ Relation.TransGen (Pos M g₀) v v)
    (ha : M.IsAntisymm g) (hc : Conf g₀ g) (v : V) :
    M.IsAntisymm (pushAtL M outs β Fr g v) ∧ Conf g₀ (pushAtL M outs β Fr g v) := by
  unfold pushAtL
  split_ifs with h
  · obtain ⟨i1, i2, -⟩ := redFold_spec (M := M) (v := v) (outs v) g (M.div g v - β v) ha
      (by omega) (houts v).1 (fun d hd => ((houts v).2 d).1 hd)
      (fun d hd hp hh => hac v (.single ⟨d, ((houts v).2 d).1 hd, hh, hc.pos ha₀ ha hp⟩))
    exact ⟨i1, hc.trans i2⟩
  · exact ⟨ha, hc⟩

/-- No positive dart of `g₀` from `b` to `a`. -/
def NoPosTo (M : CombMap D V F) (g₀ : D → ℤ) (a b : V) : Prop :=
  ∀ d, 0 < g₀ d → M.tail d = b → M.head d ≠ a

/-- **The visits along two topological orders agree.** -/
theorem nr_fold_perm {outs : V → List D} (houts : OutsOK M outs) (β : V → ℤ) (Fr : Finset V)
    {g₀ : D → ℤ} (ha₀ : M.IsAntisymm g₀) (hac : ∀ v, ¬ Relation.TransGen (Pos M g₀) v v) :
    ∀ (L₁ L₂ : List V) (g : D → ℤ), L₁.Perm L₂ → L₁.Nodup → L₁.Pairwise (NoPosTo M g₀) →
      L₂.Pairwise (NoPosTo M g₀) → M.IsAntisymm g → Conf g₀ g →
      L₁.foldl (pushAtL M outs β Fr) g = L₂.foldl (pushAtL M outs β Fr) g := by
  -- moving `a` to the front past vertices with no positive dart to or from `a`
  have hmove : ∀ (a : V) (P Q : List V) (g : D → ℤ), a ∉ P →
      (∀ x ∈ P, NoPosTo M g₀ x a ∧ NoPosTo M g₀ a x) → M.IsAntisymm g → Conf g₀ g →
      (P ++ a :: Q).foldl (pushAtL M outs β Fr) g =
        (P ++ Q).foldl (pushAtL M outs β Fr) (pushAtL M outs β Fr g a) := by
    intro a P
    induction P with
    | nil => intro Q g _ _ _ _; rfl
    | cons x P ih =>
      intro Q g haP hP ha hc
      have hxa : x ≠ a := fun h => haP (h ▸ List.mem_cons_self ..)
      obtain ⟨hx1, hx2⟩ := hP x (List.mem_cons_self ..)
      obtain ⟨a1, c1⟩ := nr_push_inv houts β Fr ha₀ hac ha hc x
      simp only [List.cons_append, List.foldl_cons]
      rw [ih Q _ (fun h => haP (List.mem_cons_of_mem _ h))
        (fun y hy => hP y (List.mem_cons_of_mem _ hy)) a1 c1]
      congr 1
      refine nr_push_comm houts β Fr g (Ne.symm hxa) fun e h1 h2 => ⟨?_, ?_⟩
      · by_contra hp; push Not at hp
        exact hx1 e (hc.pos ha₀ ha hp) h1 h2
      · by_contra hp; push Not at hp
        exact hx2 (M.rev e) (hc.pos ha₀ ha hp) (by rw [M.tail_rev, h2]) (by rw [M.head_rev, h1])
  intro L₁
  induction L₁ with
  | nil => intro L₂ g hp _ _ _ _ _; rw [List.perm_nil.1 hp.symm]
  | cons a L₁ ih =>
    intro L₂ g hp hnd hpw₁ hpw₂ ha hc
    have haL₂ : a ∈ L₂ := hp.subset (List.mem_cons_self ..)
    obtain ⟨P, Q, rfl⟩ := List.append_of_mem haL₂
    have hnd₂ : (P ++ a :: Q).Nodup := hp.nodup_iff.1 hnd
    have haP : a ∉ P := fun h => by
      have := List.nodup_append.1 hnd₂
      exact this.2.2 a h a (List.mem_cons_self ..) rfl
    obtain ⟨hpa, hpw₁'⟩ := List.pairwise_cons.1 hpw₁
    have hP : ∀ x ∈ P, NoPosTo M g₀ x a ∧ NoPosTo M g₀ a x := by
      intro x hx
      refine ⟨(List.pairwise_append.1 hpw₂).2.2 x hx a (List.mem_cons_self ..), hpa x ?_⟩
      rcases List.mem_cons.1 (hp.symm.subset (List.mem_append_left _ hx)) with h | h
      · exact absurd (h ▸ hx) haP
      · exact h
    rw [hmove a P Q g haP hP ha hc, List.foldl_cons]
    obtain ⟨a1, c1⟩ := nr_push_inv houts β Fr ha₀ hac ha hc a
    refine ih (P ++ Q) _ ?_ (List.nodup_cons.1 hnd).2 hpw₁' ?_ a1 c1
    · have h1 := hp.erase a
      simp only [List.erase_cons_head] at h1
      rwa [List.erase_append_right _ haP, List.erase_cons_head] at h1
    · obtain ⟨q1, q2, q3⟩ := List.pairwise_append.1 hpw₂
      exact List.pairwise_append.2 ⟨q1, (List.pairwise_cons.1 q2).2,
        fun x hx y hy => q3 x hx y (List.mem_cons_of_mem _ hy)⟩

/-- A topological order in the sense of positions is pairwise without backward positive darts. -/
lemma nr_pairwise_of_idx {g₀ : D → ℤ} {L : List V} (hnd : L.Nodup)
    (h : ∀ d, 0 < g₀ d → L.idxOf (M.tail d) < L.idxOf (M.head d)) :
    L.Pairwise (NoPosTo M g₀) := by
  refine ((pairwise_idxOf hnd).and hnd).imp_of_mem fun {a b} ha hb ⟨hab, hne⟩ d hd h1 h2 => ?_
  have := h d hd
  rw [h1, h2] at this
  omega

/-- **The push-back of explicit choices along any topological order of the cancelled flow.** -/
theorem nr_pushFwdL_eq (hM : M.IsPlane) {fr : FRFun F} (hfr : FRSpec fr) (r : F)
    {ord : (D → ℤ) → List V} (hord : TopoOK M ord) {outs : V → List D} (houts : OutsOK M outs)
    (β : V → ℤ) (Fr : Finset V) {g : D → ℤ} (hg : M.IsAntisymm g) (K : List V) (hK : K.Nodup)
    (hall : ∀ v, v ∈ K)
    (htopo : ∀ d, 0 < cancelR M fr r g d → K.idxOf (M.tail d) < K.idxOf (M.head d)) :
    pushFwdL M fr r ord outs β Fr g = K.foldl (pushAtL M outs β Fr) (cancelR M fr r g) := by
  obtain ⟨a₀, -, -, ac₀⟩ := cancelR_spec hM hfr r hg
  obtain ⟨o1, hall', o3⟩ := hord _ a₀ ac₀
  unfold pushFwdL
  exact nr_fold_perm houts β Fr a₀ ac₀ _ K _
    ((List.perm_ext_iff_of_nodup o1 hK).2 fun v => ⟨fun _ => hall v, fun _ => hall' v⟩) o1
    (nr_pairwise_of_idx o1 o3) (nr_pairwise_of_idx hK htopo) a₀ (Conf.refl _)

end BKMNW

end PlanarFlow
