module

public import PlanarFlow.STFlow.Lex

/-!
# The perturbed run computes parametric shortest-path trees

Erickson's formulation (SODA 2010) of the algorithm of Borradaile and Klein: for a fixed unit flow
`P` from `s` to `t` and a parameter `λ`, give the dart `d` of the dual the length `c d - λ P d`;
the dual tree of the algorithm is a shortest-path tree for these lengths, `λ` being the value of
the flow. With the perturbation of `PlanarFlow/STFlow/Lex.lean` the lengths are pairs, compared
lexicographically: `(c d, ε d) - (λ, μ) P d`, with `(λ, μ)` the values of the two flows.

* `DWalk M x l y`: the darts `l` form a walk of the dual from the face `x` to the face `y`;
  `dsum φ l`: the sum of `φ` along it. The sum of a coboundary telescopes (`dsum_cob`).
* `DTree.psum_congr`: path sums only see the parent darts.
* `linv_shortest`: **the dual tree of a state satisfying `LInv` is a shortest-path tree for the
  lexicographic lengths `(c, ε) - (λ, μ) P`**: for every dual walk `l` from the root to `x`,
  `Σ_l c - λ Σ_l P ≥ psum c x - λ psum P x`, and in case of equality
  `Σ_l ε - μ Σ_l P ≥ psum ε x - μ psum P x`.
* `linv_shortest_level`: in particular, among the dual walks from the root to `x` whose sum of
  `P` is the level `psum P x` of `x` (Erickson's crossing number: the walks that lift, in the
  cyclic cover, to the same lift of `x` as the path of the tree), the path of the tree is
  lexicographically shortest for the fixed lengths `(c, ε)`. This is what the analysis of the
  number of pivots uses: the parameter disappears in the cover.
* `lstep_value`: a step raises the value of the flow by the residual capacity of the bottleneck
  (`λ` moves to the next breakpoint, where the bottleneck becomes tight).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
/-- The darts `l` form a walk of the dual graph from the face `x` to the face `y`. -/
def DWalk (x : F) (l : List D) (y : F) : Prop := IsWalk (M.dualGraph fun _ => 0) x l y

/-- The sum of `φ` along a list of darts. -/
def dsum (φ : D → ℤ) (l : List D) : ℤ := (l.map φ).sum

@[simp] lemma dsum_nil (φ : D → ℤ) : dsum φ [] = 0 := rfl

@[simp] lemma dsum_cons (φ : D → ℤ) (a : D) (l : List D) : dsum φ (a :: l) = φ a + dsum φ l := by
  simp [dsum]

lemma dsum_append (φ : D → ℤ) (l l' : List D) : dsum φ (l ++ l') = dsum φ l + dsum φ l' := by
  simp [dsum]

lemma dsum_sub (φ φ' : D → ℤ) (l : List D) : dsum (φ - φ') l = dsum φ l - dsum φ' l := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [dsum_cons, ih, Pi.sub_apply]; ring

lemma dsum_add (φ φ' : D → ℤ) (l : List D) : dsum (φ + φ') l = dsum φ l + dsum φ' l := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [dsum_cons, ih, Pi.add_apply]; ring

lemma dsum_smul (N : ℤ) (φ : D → ℤ) (l : List D) :
    dsum (fun d => N * φ d) l = N * dsum φ l := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [dsum_cons, ih]; ring

lemma dsum_nonneg {φ : D → ℤ} {l : List D} (h : ∀ d ∈ l, 0 ≤ φ d) : 0 ≤ dsum φ l :=
  List.sum_nonneg (by simpa using h)

/-- A sum of nonnegative terms vanishes only if every term does. -/
lemma eq_zero_of_dsum {φ : D → ℤ} {l : List D} (h : ∀ d ∈ l, 0 ≤ φ d) (h0 : dsum φ l = 0) :
    ∀ d ∈ l, φ d = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [dsum_cons] at h0
    have ha := h a (by simp)
    have hl := dsum_nonneg (fun d hd => h d (List.mem_cons_of_mem a hd))
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · omega
    · exact ih (fun d hd => h d (List.mem_cons_of_mem a hd)) (by omega) d hd

/-- **The sum of a coboundary along a dual walk telescopes.** -/
lemma dsum_cob {x y : F} {l : List D} (h : DWalk M x l y) (ψ : F → ℤ) :
    dsum (M.cob ψ) l = ψ y - ψ x :=
  IsWalk.sum_sub (G := M.dualGraph fun _ => 0) ψ h

/-- **Path sums only see the parent darts.** -/
lemma DTree.psum_congr (T : DTree M) {φ φ' : D → ℤ} (h : ∀ x, x ≠ T.root → φ (T.par x) =
    φ' (T.par x)) (x : F) : T.psum φ x = T.psum φ' x :=
  (T.psum_unique φ (k := T.psum φ') (T.psum_root φ') (fun y hy => by
    rw [T.psum_of_ne φ' hy, h y hy]) x).symm

variable {c ε : D → ℤ} {s t : V}

/-- A flow conserved off `s` and `t`, minus its value times a unit flow, is a circulation, hence a
coboundary. -/
lemma exists_cob_of_cons (hM : M.IsPlane) {g : D → ℤ} (hg : M.IsAntisymm g)
    (hcons : ∀ v, v ≠ s → v ≠ t → M.div g v = 0) {P : D → ℤ}
    (hP : IsUnit (M := M) (s := s) (t := t) P) (hst : s ≠ t) :
    ∃ ψ : F → ℤ, ∀ d, g d = M.div g s * P d + M.cob ψ d := by
  have htot := M.sum_div hg
  rw [Fintype.sum_eq_add s t hst (fun v hv => hcons v hv.1 hv.2)] at htot
  have hdt : M.div g t = - M.div g s := by omega
  have hcirc : M.IsCirc (fun d => g d - M.div g s * P d) := by
    refine ⟨fun d => by simp only [hg d, hP.antisymm d]; ring, fun v => ?_⟩
    have : (fun d => g d - M.div g s * P d) = g - fun d => M.div g s * P d := rfl
    rw [this, div_sub, div_smul, hP.div_eq]
    by_cases hvs : v = s
    · subst hvs; simp [Ne.symm hst]
    · by_cases hvt : v = t
      · subst hvt; simp [hst, hdt]
      · simp [Ne.symm hvs, Ne.symm hvt, hcons v hvs hvt]
  obtain ⟨ψ, hψ⟩ := exists_int_potential hM hcirc
  exact ⟨ψ, fun d => by have := hψ d; omega⟩

/-- **The dual tree of the perturbed run is a parametric shortest-path tree**: with `λ` and `μ`
the values of the two flows, for every dual walk `l` from the root to `x`, the lengths
`c - λ P` give `l` at least the length of the path of the tree, and in case of equality the
lengths `ε - μ P` do. -/
theorem linv_shortest (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M} (hI : LInv c ε s t st)
    {P : D → ℤ} (hP : IsUnit (M := M) (s := s) (t := t) P) {x : F} {l : List D}
    (hl : DWalk M st.T.root l x) :
    st.T.psum c x - M.div st.g s * st.T.psum P x ≤ dsum c l - M.div st.g s * dsum P l ∧
      (dsum c l - M.div st.g s * dsum P l = st.T.psum c x - M.div st.g s * st.T.psum P x →
        st.T.psum ε x - M.div st.h s * st.T.psum P x ≤ dsum ε l - M.div st.h s * dsum P l) := by
  obtain ⟨ψ, hψ⟩ := exists_cob_of_cons hM hI.base.pseudo.antisymm hI.base.cons hP hst
  simp only [LSt.base_g] at hψ
  obtain ⟨ψ', hψ'⟩ := exists_cob_of_cons hM hI.antisymm hI.cons hP hst
  set lam := M.div st.g s
  set mu := M.div st.h s
  -- the path sums of the tree: the darts of the tree are saturated
  have hpc : st.T.psum c x = lam * st.T.psum P x + (ψ x - ψ st.T.root) := by
    rw [st.T.psum_congr (φ' := st.g) (fun y hy => (hI.base.sat y hy).symm)]
    have : st.g = (fun d => lam * P d) + M.cob ψ := funext fun d => by simp [hψ d]
    rw [this, DTree.psum_add, DTree.psum_smul, DTree.psum_cob]
  have hpe : st.T.psum ε x = mu * st.T.psum P x + (ψ' x - ψ' st.T.root) := by
    rw [st.T.psum_congr (φ' := st.h) (fun y hy => (hI.sat y hy).symm)]
    have : st.h = (fun d => mu * P d) + M.cob ψ' := funext fun d => by simp [hψ' d]
    rw [this, DTree.psum_add, DTree.psum_smul, DTree.psum_cob]
  -- the sums along the walk
  have hlc : dsum c l = dsum (c - st.g) l + lam * dsum P l + (ψ x - ψ st.T.root) := by
    have : c = (c - st.g) + ((fun d => lam * P d) + M.cob ψ) := funext fun d => by
      simp [hψ d]
    conv_lhs => rw [this]
    rw [dsum_add, dsum_add, dsum_smul, dsum_cob hl]; ring
  have hle : dsum ε l = dsum (ε - st.h) l + mu * dsum P l + (ψ' x - ψ' st.T.root) := by
    have : ε = (ε - st.h) + ((fun d => mu * P d) + M.cob ψ') := funext fun d => by
      simp [hψ' d]
    conv_lhs => rw [this]
    rw [dsum_add, dsum_add, dsum_smul, dsum_cob hl]; ring
  have hres : ∀ d ∈ l, 0 ≤ (c - st.g) d := fun d _ => by
    have := hI.base.pseudo.le_cap d; simp only [Pi.sub_apply, LSt.base_g] at this ⊢; omega
  refine ⟨by have := dsum_nonneg hres; linarith, fun heq => ?_⟩
  have h0 : dsum (c - st.g) l = 0 := by linarith
  have hz := eq_zero_of_dsum hres h0
  have hres' : ∀ d ∈ l, 0 ≤ (ε - st.h) d := fun d hd => by
    have := hz d hd
    simp only [Pi.sub_apply] at this ⊢
    have := hI.lex d (by omega)
    omega
  have := dsum_nonneg hres'
  linarith

/-- **Among the dual walks from the root to `x` at the level of `x`, the path of the tree is
lexicographically shortest for the lengths `(c, ε)`.** -/
theorem linv_shortest_level (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M}
    (hI : LInv c ε s t st) {P : D → ℤ} (hP : IsUnit (M := M) (s := s) (t := t) P) {x : F}
    {l : List D} (hl : DWalk M st.T.root l x) (hlev : dsum P l = st.T.psum P x) :
    st.T.psum c x ≤ dsum c l ∧ (dsum c l = st.T.psum c x → st.T.psum ε x ≤ dsum ε l) := by
  obtain ⟨h1, h2⟩ := linv_shortest hM hst hI hP hl
  rw [hlev] at h1 h2
  exact ⟨by linarith, fun h => by have := h2 (by linarith); linarith⟩

/-- **A step raises the value of the flow by the residual capacity of the bottleneck.** -/
theorem lstep_value (hM : M.IsPlane) (hst : s ≠ t) (st : LSt M) :
    ∃ e, st.T.chi s t e = 1 ∧ M.div (lstep M c ε s t st).1.g s = M.div st.g s + (c e - st.g e) ∧
      M.div (lstep M c ε s t st).1.h s = M.div st.h s + (ε e - st.h e) := by
  have hne := pathSet_nonempty hM hst st.T (s := s) (t := t)
  obtain ⟨-, hχdiv, -, -⟩ := st.T.chi_spec hM s t
  refine ⟨lbott c ε s t st.g st.h st.T hne, lbott_mem c ε s t _ _ _ hne, ?_, ?_⟩
  · rw [lstep_of_ne hne]
    simp only
    rw [stepE_g, div_aug]
    simp [hχdiv, Ne.symm hst]
  · rw [lstep_of_ne hne]
    simp only
    rw [div_aug, hχdiv]
    simp [Ne.symm hst]

end STFlow

end PlanarFlow
