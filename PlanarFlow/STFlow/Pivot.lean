module

public import PlanarFlow.STFlow.Cotree

/-!
# The augmenting-path algorithm with pivots, and its correctness

The algorithm of Borradaile and Klein (J. ACM 56(2), 2009), in the parametric formulation of
Erickson (SODA 2010), for one source `s` and one sink `t ≠ s` in a plane map with nonnegative
capacities `c`. The state (`St`) is a pseudoflow `g` and a spanning tree `T*` of the dual graph
rooted at a face `o`; the invariant (`Inv`) is that `g` is conserved off `s` and `t` and that the
darts of `T*` are saturated. (So every face is reached from `o` by non-residual dual darts: the
residual graph has no clockwise cycle with respect to `o`, the condition under which the path of
the cotree is the leftmost residual path of Borradaile and Klein.)

One step (`step`):

1. the path `Q` from `s` to `t` in the cotree `C` (the edges off `T*`), as the unit flow
   `chi T s t`;
2. its bottleneck `e` (`bott`), a dart of `Q` of least residual capacity `δ`;
3. **augment**: push `δ` along `Q` (`aug`); `e` is now saturated, and the darts of `T*` are
   untouched;
4. **pivot**: let `a = face e`, `b = face (rev e)`; if `b` is on the path from `a` to the root,
   stop; otherwise `e` becomes the parent dart of `b` (`PlanarFlow.STFlow.DTree.reparent`), and
   the old parent dart of `b` moves to the cotree.

The step at a given dart `e` is `stepE`; `step` is `stepE` at the bottleneck `bott`. The results
on one step hold for `stepE` at any bottleneck (`IsBott`: a dart of the path of least residual
capacity), so they apply to any rule choosing among the bottlenecks (the perturbed rule of
`PlanarFlow/STFlow/Lex.lean`).

## Results

* `step_inv`: the invariant is preserved.
* `step_noPath`: **when the algorithm stops, no residual path leads from `s` to `t`.** The
  dual walk `Γ` from `b` down `T*` to `a` and back through `e` is a closed walk of saturated
  darts, which `Q` crosses exactly once (at `e`). A residual path `R` from `s` to `t` differs from
  `Q` by a circulation, the coboundary of a face potential, whose sum over `Γ` telescopes to `0`;
  so `R` crosses `Γ` once as well, through a residual dart of `Γ`, a contradiction.
* `step_pot`: **each pivot raises the levels.** For a fixed unit flow `P` from `s` to `t`, the
  level of a face is the sum of `P` along its path in `T*` (Erickson's crossing number with an
  `s`–`t` path); a pivot raises the levels of the subtree of `b` by exactly `1` (the fundamental
  cycle of `e` crosses `Q` once). The levels are at most the number of faces in absolute value,
  so there are at most `2 F²` pivots (`run_done`), and the algorithm terminates.
* `run_spec`: from a state satisfying the invariant, the run stops within `2 F² + 1` steps with
  a pseudoflow conserved off `s` and `t` and no residual path from `s` to `t`.

The number of steps is `O(n)` by the analysis of Borradaile and Klein (each dart pivots into the
tree at most once; Erickson, SODA 2010); that bound is the hypothesis of the cost theorem
(`PlanarFlow/STFlow/Cost.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

lemma DTree.anc_root (T : DTree M) (x : F) : T.Anc T.root x := T.reach x

lemma DTree.ne_root_of_not_anc (T : DTree M) {b x : F} (h : ¬ T.Anc b x) : b ≠ T.root :=
  fun hb => h (hb ▸ T.anc_root x)

variable (M) in
/-- The state: a flow and a spanning tree of the dual. -/
structure St where
  /-- The flow. -/
  g : D → ℤ
  /-- The spanning tree of the dual. -/
  T : DTree M

variable (c : D → ℤ) (s t : V)

/-- The darts of the path of the cotree from `s` to `t`. -/
noncomputable def pathSet (T : DTree M) : Finset D := univ.filter fun d => T.chi s t d = 1

/-- **The bottleneck**: a dart of the path of least residual capacity. -/
noncomputable def bott (g : D → ℤ) (T : DTree M) (h : (pathSet s t T).Nonempty) : D :=
  ((pathSet s t T).exists_min_image (fun d => c d - g d) h).choose

lemma bott_mem (g : D → ℤ) (T : DTree M) (h : (pathSet s t T).Nonempty) :
    T.chi s t (bott c s t g T h) = 1 := by
  have := ((pathSet s t T).exists_min_image (fun d => c d - g d) h).choose_spec.1
  unfold bott
  simpa [pathSet] using this

lemma bott_min (g : D → ℤ) (T : DTree M) (h : (pathSet s t T).Nonempty) {d : D}
    (hd : T.chi s t d = 1) : c (bott c s t g T h) - g (bott c s t g T h) ≤ c d - g d :=
  ((pathSet s t T).exists_min_image (fun d => c d - g d) h).choose_spec.2 d (by simp [pathSet, hd])

/-- `e` **is a bottleneck**: a dart of the path of the cotree of least residual capacity. -/
def IsBott (g : D → ℤ) (T : DTree M) (e : D) : Prop :=
  T.chi s t e = 1 ∧ ∀ d, T.chi s t d = 1 → c e - g e ≤ c d - g d

lemma bott_isBott (g : D → ℤ) (T : DTree M) (h : (pathSet s t T).Nonempty) :
    IsBott c s t g T (bott c s t g T h) :=
  ⟨bott_mem c s t g T h, fun _ hd => bott_min c s t g T h hd⟩

/-- Pushing `δ` units along the unit flow `χ`. -/
def aug (g χ : D → ℤ) (δ : ℤ) (d : D) : ℤ := g d + δ * χ d

variable (M) in
open Classical in
/-- **The step at the dart `e`**: augment along the path of the cotree by the residual capacity of
`e`, then pivot `e` into the tree, or stop (`true`) when the head face of `e` is above its tail
face. -/
noncomputable def stepE (st : St M) (e : D) : St M × Bool :=
  if ha : st.T.Anc (M.face (M.rev e)) (M.face e)
  then (⟨aug st.g (st.T.chi s t) (c e - st.g e), st.T⟩, true)
  else (⟨aug st.g (st.T.chi s t) (c e - st.g e),
    st.T.reparent _ e (st.T.ne_root_of_not_anc ha) rfl ha⟩, false)

variable (M) in
open Classical in
/-- **One step**: augment along the path of the cotree, then pivot the bottleneck into the tree,
or stop (`true`). -/
noncomputable def step (st : St M) : St M × Bool :=
  if h : (pathSet s t st.T).Nonempty then stepE M c s t st (bott c s t st.g st.T h)
  else (st, true)

/-- **The invariant**: a pseudoflow conserved off `s` and `t`, saturating the darts of the
tree. -/
structure Inv (st : St M) : Prop where
  pseudo : IsPseudo M c st.g
  cons : ∀ v, v ≠ s → v ≠ t → M.div st.g v = 0
  sat : ∀ x, x ≠ st.T.root → st.g (st.T.par x) = c (st.T.par x)

/-! ### The augmentation -/

section Aug

variable {c s t}

/-- The path is nonempty: some dart leaving `s` has value `1`. -/
lemma pathSet_nonempty (hM : M.IsPlane) (hst : s ≠ t) (T : DTree M) :
    (pathSet s t T).Nonempty := by
  obtain ⟨-, hdiv, -, hle⟩ := T.chi_spec hM s t
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hd : ∀ d, T.chi s t d ≤ 0 := fun d => by
    have h1 := hle d
    have h2 : T.chi s t d ≠ 1 := fun h' => by
      have : d ∈ pathSet s t T := by simp [pathSet, h']
      rw [h] at this; simp at this
    omega
  have := hdiv s
  simp [Ne.symm hst] at this
  have h0 : M.div (T.chi s t) s ≤ 0 := sum_nonpos fun d _ => hd d
  omega

lemma div_aug (g χ : D → ℤ) (δ : ℤ) (v : V) :
    M.div (aug g χ δ) v = M.div g v + δ * M.div χ v := by
  have : aug g χ δ = g + fun d => δ * χ d := rfl
  rw [this, BKMNW.div_add', div_smul]

/-- **The augmentation at a bottleneck keeps the invariant**, and saturates the bottleneck. -/
lemma aug_spec (hM : M.IsPlane) {st : St M} (hI : Inv c s t st) {e : D}
    (he : IsBott c s t st.g st.T e) :
    IsPseudo M c (aug st.g (st.T.chi s t) (c e - st.g e)) ∧
    (∀ v, v ≠ s → v ≠ t → M.div (aug st.g (st.T.chi s t) (c e - st.g e)) v = 0) ∧
    (∀ d, st.T.InT d → aug st.g (st.T.chi s t) (c e - st.g e) d = st.g d) ∧
    aug st.g (st.T.chi s t) (c e - st.g e) e = c e := by
  obtain ⟨hχa, hχdiv, hχoff, hχle⟩ := st.T.chi_spec hM s t
  obtain ⟨he1, hmin⟩ := he
  have hδ : 0 ≤ c e - st.g e := by have := hI.pseudo.le_cap e; omega
  refine ⟨⟨fun d => ?_, fun d => ?_⟩, fun v hs ht => ?_, fun d hd => ?_, ?_⟩
  · simp only [aug, hI.pseudo.antisymm d, hχa d]; ring
  · simp only [aug]
    by_cases hd : st.T.chi s t d = 1
    · have := hmin d hd; rw [hd]; omega
    · have h1 := hχle d
      have : st.T.chi s t d ≤ 0 := by omega
      have := hI.pseudo.le_cap d
      nlinarith
  · rw [div_aug, hI.cons v hs ht, hχdiv]; simp [Ne.symm hs, Ne.symm ht]
  · simp [aug, hχoff d hd]
  · simp only [aug, he1]; ring

end Aug

/-! ### The step -/

section Step

variable {c s t}

/-- **The step at a bottleneck keeps the invariant.** -/
theorem stepE_inv (hM : M.IsPlane) {st : St M} (hI : Inv c s t st) {e : D}
    (he : IsBott c s t st.g st.T e) : Inv c s t (stepE M c s t st e).1 := by
  obtain ⟨hp, hc, htree, hsat⟩ := aug_spec hM hI he
  unfold stepE
  split_ifs with ha
  · exact ⟨hp, hc, fun x hx => by
      simp only at hx ⊢; rw [htree _ (st.T.inT_par hx)]; exact hI.sat x hx⟩
  · refine ⟨hp, hc, fun x hx => ?_⟩
    simp only at hx ⊢
    rw [DTree.reparent_par]
    split_ifs with hxb
    · exact hsat
    · rw [htree _ (st.T.inT_par hx)]; exact hI.sat x hx

/-- **The step keeps the invariant.** -/
theorem step_inv (hM : M.IsPlane) {st : St M} (hI : Inv c s t st) :
    Inv c s t (step M c s t st).1 := by
  unfold step
  split_ifs with h
  · exact stepE_inv hM hI (bott_isBott c s t _ _ h)
  · exact hI

/-- **When the step at a bottleneck stops, no residual path leads from `s` to `t`.** -/
theorem stepE_noPath (hM : M.IsPlane) {st : St M} (hI : Inv c s t st) {e : D}
    (he : IsBott c s t st.g st.T e) (hdone : (stepE M c s t st e).2 = true) :
    ¬ Relation.ReflTransGen (ResAdj M c (stepE M c s t st e).1.g) s t := by
  obtain ⟨hp, -, htree, hsat⟩ := aug_spec hM hI he
  have he1 := he.1
  unfold stepE at hdone ⊢
  split_ifs at hdone ⊢ with ha
  simp only
  obtain ⟨hχa, hχdiv, hχoff, -⟩ := st.T.chi_spec hM s t
  generalize hg : aug st.g (st.T.chi s t) (c e - st.g e) = g' at hp hsat htree ⊢
  intro hR
  -- a residual path gives a unit flow, positive only on residual darts
  obtain ⟨χR, hRa, hRdiv, hRpos⟩ := exists_pathFlow hR
  -- it differs from the path of the cotree by a coboundary
  have hcirc : M.IsCirc (χR - st.T.chi s t) := ⟨fun d => by
    simp only [Pi.sub_apply, hRa d, hχa d]; ring, fun v => by rw [div_sub, hRdiv, hχdiv]; ring⟩
  obtain ⟨ψ, hψ⟩ := exists_int_potential hM hcirc
  have hR : ∀ d, χR d = st.T.chi s t d + M.cob ψ d := fun d => by
    have := hψ d; simp only [Pi.sub_apply] at this; omega
  -- path sums
  have hps : ∀ x, st.T.psum χR x = ψ x - ψ st.T.root := fun x => by
    have : χR = st.T.chi s t + M.cob ψ := funext hR
    rw [this, DTree.psum_add, st.T.psum_eq_zero (fun y hy => hχoff _ (st.T.inT_par hy)),
      DTree.psum_cob, zero_add]
  obtain ⟨n, hn, hfirst⟩ := st.T.exists_first ha
  have hanc := st.T.psum_anc χR hn (fun i hi => (hfirst i hi).2)
  rw [hps, hps] at hanc
  have hsum : ∑ i ∈ range n, χR (st.T.par (st.T.up^[i] (M.face e))) + χR e = 1 := by
    rw [hR e, he1]; simp only [cob]; linarith
  -- some dart of the closed walk carries `χR > 0`, so it is residual, but it is saturated
  have hpos : (∃ i ∈ range n, 0 < χR (st.T.par (st.T.up^[i] (M.face e)))) ∨ 0 < χR e := by
    by_contra hcon
    push Not at hcon
    have := sum_nonpos fun i hi => hcon.1 i hi
    omega
  rcases hpos with ⟨i, hi, hpi⟩ | hpe
  · have hx := (hfirst i (mem_range.1 hi)).2
    have h1 := hRpos _ hpi
    rw [htree _ (st.T.inT_par hx), hI.sat _ hx] at h1
    exact lt_irrefl _ h1
  · have h1 := hRpos _ hpe
    rw [hsat] at h1
    exact lt_irrefl _ h1

/-- **When the algorithm stops, no residual path leads from `s` to `t`.** -/
theorem step_noPath (hM : M.IsPlane) (hst : s ≠ t) {st : St M} (hI : Inv c s t st)
    (hdone : (step M c s t st).2 = true) :
    ¬ Relation.ReflTransGen (ResAdj M c (step M c s t st).1.g) s t := by
  have hne := pathSet_nonempty hM hst st.T (s := s) (t := t)
  unfold step at hdone ⊢
  simp only [hne, ↓reduceDIte] at hdone ⊢
  exact stepE_noPath hM hI (bott_isBott c s t _ _ hne) hdone

/-- The levels: the sum over the faces of the path sums of `P`. -/
noncomputable def pot (P : D → ℤ) (T : DTree M) : ℤ := ∑ x, T.psum P x

/-- A unit flow from `s` to `t`. -/
structure IsUnit (P : D → ℤ) : Prop where
  antisymm : M.IsAntisymm P
  div_eq : ∀ v, M.div P v = (if s = v then 1 else 0) - (if t = v then 1 else 0)
  le_one : ∀ d, P d ≤ 1

lemma IsUnit.abs_le {P : D → ℤ} (hP : IsUnit (M := M) (s := s) (t := t) P) (d : D) :
    |P d| ≤ 1 := by
  have h1 := hP.le_one d
  have h2 := hP.le_one (M.rev d)
  rw [hP.antisymm d] at h2
  rw [_root_.abs_le]; constructor <;> omega

/-- The levels are at most `F²` in absolute value. -/
lemma abs_pot_le {P : D → ℤ} (hP : IsUnit (M := M) (s := s) (t := t) P) (T : DTree M) :
    |pot P T| ≤ Fintype.card F * Fintype.card F := by
  unfold pot
  calc |∑ x, T.psum P x| ≤ ∑ x, |T.psum P x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : F, (Fintype.card F : ℤ) := sum_le_sum fun x _ => by
        have := T.abs_psum_le hP.abs_le x
        have := T.depth_lt_card x
        omega
    _ = Fintype.card F * Fintype.card F := by simp

/-- **A pivot at a dart crossed forward by the path of the cotree raises the levels of the
subtree of `b` by exactly `1`.** -/
theorem stepE_pot (hM : M.IsPlane) {st : St M} {e : D} (he1 : st.T.chi s t e = 1) {P : D → ℤ}
    (hP : IsUnit (M := M) (s := s) (t := t) P) (hdone : (stepE M c s t st e).2 = false) :
    pot P st.T + 1 ≤ pot P (stepE M c s t st e).1.T ∧
      (stepE M c s t st e).1.T.root = st.T.root := by
  classical
  unfold stepE at hdone ⊢
  split_ifs at hdone ⊢ with ha
  refine ⟨?_, rfl⟩
  simp only
  obtain ⟨hχa, hχdiv, hχoff, -⟩ := st.T.chi_spec hM s t
  -- the increment is `1`
  have hcirc : M.IsCirc (P - st.T.chi s t) := ⟨fun d => by
    simp only [Pi.sub_apply, hP.antisymm d, hχa d]; ring, fun v => by
      rw [div_sub, hP.div_eq, hχdiv]; ring⟩
  obtain ⟨ψ, hψ⟩ := exists_int_potential hM hcirc
  have hPd : ∀ d, P d = st.T.chi s t d + M.cob ψ d := fun d => by
    have := hψ d; simp only [Pi.sub_apply] at this; omega
  have hps : ∀ x, st.T.psum P x = ψ x - ψ st.T.root := fun x => by
    have : P = st.T.chi s t + M.cob ψ := funext hPd
    rw [this, DTree.psum_add, st.T.psum_eq_zero (fun y hy => hχoff _ (st.T.inT_par hy)),
      DTree.psum_cob, zero_add]
  have hinc : st.T.psum P (M.face e) + P e - st.T.psum P (M.face (M.rev e)) = 1 := by
    rw [hps, hps, hPd e, he1]; simp only [cob]; ring
  unfold pot
  simp only [DTree.psum_reparent, hinc, sum_add_distrib]
  generalize M.face (M.rev e) = b
  have : 1 ≤ ∑ x, (if st.T.Anc b x then (1 : ℤ) else 0) := by
    rw [← Finset.sum_erase_add _ _ (mem_univ b)]
    have := sum_nonneg (s := univ.erase b)
      (f := fun x => if st.T.Anc b x then (1 : ℤ) else 0)
      (fun x _ => by split_ifs <;> omega)
    simp only [st.T.anc_self b, ↓reduceIte]
    omega
  linarith

/-- **A pivot raises the levels of the subtree of `b` by exactly `1`.** -/
theorem step_pot (hM : M.IsPlane) (hst : s ≠ t) {st : St M} {P : D → ℤ}
    (hP : IsUnit (M := M) (s := s) (t := t) P) (hdone : (step M c s t st).2 = false) :
    pot P st.T + 1 ≤ pot P (step M c s t st).1.T ∧ (step M c s t st).1.T.root = st.T.root := by
  have hne := pathSet_nonempty hM hst st.T (s := s) (t := t)
  unfold step at hdone ⊢
  simp only [hne, ↓reduceDIte] at hdone ⊢
  exact stepE_pot hM (bott_mem c s t _ _ hne) hP hdone

open Classical in
/-- **The facts of a pivot at `e`**: when the step at `e` does not stop, it gives the face
`b = face (rev e)` the parent dart `e`, from a face not below `b`. -/
lemma stepE_facts {st : St M} {e : D} (h : (stepE M c s t st e).2 = false) :
    M.face (M.rev e) ≠ st.T.root ∧ ¬ st.T.Anc (M.face (M.rev e)) (M.face e) ∧
      (stepE M c s t st e).1.T.root = st.T.root ∧
      (∀ x, (stepE M c s t st e).1.T.par x =
        if x = M.face (M.rev e) then e else st.T.par x) ∧
      ∀ φ x, (stepE M c s t st e).1.T.psum φ x = st.T.psum φ x +
        if st.T.Anc (M.face (M.rev e)) x then
          st.T.psum φ (M.face e) + φ e - st.T.psum φ (M.face (M.rev e)) else 0 := by
  classical
  unfold stepE at h ⊢
  split_ifs at h ⊢ with ha
  exact ⟨st.T.ne_root_of_not_anc ha, ha, rfl,
    fun x => st.T.reparent_par (hb := st.T.ne_root_of_not_anc ha) (he := rfl) (hna := ha) x,
    fun φ x => st.T.psum_reparent (hb := st.T.ne_root_of_not_anc ha) (he := rfl) (hna := ha) φ x⟩

lemma stepE_g (st : St M) (e : D) :
    (stepE M c s t st e).1.g = aug st.g (st.T.chi s t) (c e - st.g e) := by
  unfold stepE; split_ifs <;> rfl

end Step

/-! ### The run -/

variable (M) in
/-- **The run** with at most `n` steps: the final state, the number of steps, and whether the
algorithm stopped. -/
noncomputable def run : ℕ → St M → St M × ℕ × Bool
  | 0, st => (st, 0, false)
  | n + 1, st =>
    if (step M c s t st).2 then ((step M c s t st).1, 1, true)
    else ((run n (step M c s t st).1).1, (run n (step M c s t st).1).2.1 + 1,
      (run n (step M c s t st).1).2.2)

section Run

variable {c s t}

theorem run_inv (hM : M.IsPlane) : ∀ n (st : St M), Inv c s t st → Inv c s t (run M c s t n st).1
  | 0, _, hI => hI
  | n + 1, st, hI => by
    unfold run
    split_ifs
    · exact step_inv hM hI
    · exact run_inv hM n _ (step_inv hM hI)

theorem run_noPath (hM : M.IsPlane) (hst : s ≠ t) : ∀ n (st : St M), Inv c s t st →
    (run M c s t n st).2.2 = true →
    ¬ Relation.ReflTransGen (ResAdj M c (run M c s t n st).1.g) s t
  | 0, _, _, h => by simp [run] at h
  | n + 1, st, hI, h => by
    unfold run at h ⊢
    split_ifs at h ⊢ with hd
    · exact step_noPath hM hst hI hd
    · exact run_noPath hM hst n _ (step_inv hM hI) h

theorem run_pot (hM : M.IsPlane) (hst : s ≠ t) {P : D → ℤ}
    (hP : IsUnit (M := M) (s := s) (t := t) P) :
    ∀ n (st : St M), (run M c s t n st).2.2 = false →
      pot P st.T + n ≤ pot P (run M c s t n st).1.T
  | 0, _, _ => by simp [run]
  | n + 1, st, h => by
    unfold run at h ⊢
    split_ifs at h ⊢ with hd
    · have h1 := (step_pot hM hst hP (by simpa using hd)).1
      have h2 := run_pot hM hst hP n _ h
      simp only; push_cast; linarith

theorem run_steps_le : ∀ n (st : St M), (run M c s t n st).2.1 ≤ n
  | 0, _ => by simp [run]
  | n + 1, st => by
    unfold run
    split_ifs
    · simp
    · have := run_steps_le n (step M c s t st).1; simp only; omega

/-- **The run stops** within `2 F² + 1` steps. -/
theorem run_done (hM : M.IsPlane) (hst : s ≠ t) {P : D → ℤ}
    (hP : IsUnit (M := M) (s := s) (t := t) P)
    (st : St M) {n : ℕ} (hn : 2 * Fintype.card F * Fintype.card F < n) :
    (run M c s t n st).2.2 = true := by
  by_contra h
  have h1 := run_pot hM hst hP n st (by simpa using h)
  have h2 := abs_pot_le hP st.T
  have h3 := abs_pot_le hP (run M c s t n st).1.T
  rw [abs_le] at h2 h3
  have : (n : ℤ) > 2 * Fintype.card F * Fintype.card F := by exact_mod_cast hn
  linarith

/-- **Correctness of the run**: from a state satisfying the invariant, with enough steps, the run
stops with a pseudoflow conserved off `s` and `t` and no residual path from `s` to `t`. -/
theorem run_spec (hM : M.IsPlane) (hst : s ≠ t) {P : D → ℤ}
    (hP : IsUnit (M := M) (s := s) (t := t) P)
    {st : St M} (hI : Inv c s t st) {n : ℕ} (hn : 2 * Fintype.card F * Fintype.card F < n) :
    IsPseudo M c (run M c s t n st).1.g ∧
      (∀ v, v ≠ s → v ≠ t → M.div (run M c s t n st).1.g v = 0) ∧
      NoPath M c (run M c s t n st).1.g {s} {t} := by
  have hI' := run_inv hM n st hI
  refine ⟨hI'.pseudo, hI'.cons, (noPath_iff hI'.pseudo).2 fun a ha b hb => ?_⟩
  rw [mem_singleton] at ha hb
  subst ha hb
  exact run_noPath hM hst n st hI (run_done hM hst hP st hn)

end Run

end STFlow

end PlanarFlow
