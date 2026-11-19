module

public import PlanarFlow.STFlow.ProgKey
public import PlanarFlow.STFlow.LexTree

/-!
# Comparing the perturbed residual capacities with the indices of tree paths

The perturbed run (`PlanarFlow/STFlow/Lex.lean`) chooses, on the path of the cotree from `s` to
`t`, the dart of lexicographically least residual capacity `(c - g, ε - h)`. Under the invariant
the second coordinates on that path are `lred ε T d - μ` (`linv_slack2`), with
`lred ε T d = ε d + psum ε (face d) - psum ε (face (rev d))` and `ε = lexEps` (`(4 F + 5)` to the
power of the index). Following Cabello, Chambers and Erickson (Section 6.2), this file resolves
the comparison of two such second coordinates symbolically, from the indices of the darts of four
paths of the dual tree, so that a program needs to store only the unperturbed values.

## The sides of a dart of the cotree

* `DTree.side T d`: the vertices reached from the tail of a dart `d` off the tree in the cotree
  without the edge of `d`; `DTree.head_not_mem_side`: the head of `d` is not among them (the
  cotree is acyclic), and `DTree.flow_eq_side`: **the value of a flow of the cotree at `d` is the
  net divergence of the side of `d`**.
* `DTree.no_cross`: **two darts of the path of the cotree from `s` to `t` cannot be crossed in
  opposite directions by a unit flow of the cotree** (the sides of the darts of the path are
  nested; this is where planarity enters, through the acyclicity of the cotree).

## The fundamental cycles

* `DTree.subFlow T y`: the coboundary of the subtree of a face `y ≠ root` minus the parent dart of
  `y`: a unit flow of the cotree.
* `DTree.not_cross`: hence **for two darts `d₁`, `d₂` of the path, no subtree of the dual tree
  contains `face d₁` and `face (rev d₂)` without `face (rev d₁)` and `face d₂`**, nor the reverse.
  So in the difference of the two fundamental cycles, the parent dart of every face has the
  coefficient `-1`, `0` or `1`.

## The comparison

* `DTree.lcoef T d₁ d₂ e`: the coefficient of `e` in `lred ε T d₁ - lred ε T d₂`
  (`DTree.lred_sub_eq`): `1` at `d₁`, `-1` at `d₂`, and on the parent dart of a face `y` the
  number of the faces `face d₁`, `face (rev d₂)` below `y` minus that of `face (rev d₁)`,
  `face d₂`; `DTree.abs_lcoef_le`: it is `-1`, `0` or `1` for two darts of the path.
* `sum_pos_of_top`: a sum of `±B ^ (index)` (`B ≥ 2`) has the sign of its top coefficient.
* `DTree.lred_lt_iff`: **`lred d₁ < lred d₂` exactly when the coefficient of the largest index
  with a nonzero coefficient is `-1`**: a comparison of the largest indices of darts on four
  paths of the dual tree, the paths from the root to the faces of `d₁` and `d₂`, after the
  cancellation of their common parts. A minimum-index (here: maximum-index) dynamic tree answers
  it with path queries (Cabello, Chambers and Erickson, Section 6.2).
* `lslack_lt_iff`: **the comparison of the perturbed run** (`lbott`) on two darts of the path:
  the unperturbed residual capacities first, then `lred_lt_iff`. No number of more than the
  size of the residual capacities and the indices is involved.
* `lbott_eq_of_lt`: a dart of the path below all the others for this comparison is `lbott`.
* `DTree.lred_pos_iff`, `DTree.lred_ne_zero`, `lexFeas_iff_top`: the sign of `lred` of one dart
  off the tree is that of its top coefficient (`lcoef1`, two tree paths); so **the feasibility
  of a given initial tree for the lexicographic lengths** (`DTree.LexFeas`, the precondition of
  `pstflow_exec_lex`) **is checked with unperturbed values and indices**.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

namespace DTree

variable (T : DTree M)

/-! ### The sides of a dart of the cotree -/

/-- Adjacency in the cotree without the edge of `d`. -/
def CAdjA (d : D) : V → V → Prop :=
  fun a b => ∃ e, (¬ T.InT e ∧ e ≠ d ∧ e ≠ M.rev d) ∧ M.tail e = a ∧ M.head e = b

variable {T}

lemma CAdjA.symm {d : D} {a b : V} (h : T.CAdjA d a b) : T.CAdjA d b a := by
  obtain ⟨e, ⟨h1, h2, h3⟩, rfl, rfl⟩ := h
  refine ⟨M.rev e, ⟨fun h => h1 (T.inT_rev_iff.1 h), fun h => h3 ?_, fun h => h2 ?_⟩, by simp,
    by simp⟩
  · rw [← h, M.rev_rev]
  · exact M.rev_injective h

lemma rtg_symm {d : D} {a b : V} (h : Relation.ReflTransGen (T.CAdjA d) a b) :
    Relation.ReflTransGen (T.CAdjA d) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head hbc.symm ih

lemma cAdjA_rev (d : D) : T.CAdjA (M.rev d) = T.CAdjA d := by
  funext a b
  apply propext
  constructor <;> rintro ⟨e, ⟨h1, h2, h3⟩, h4, h5⟩
  · exact ⟨e, ⟨h1, fun h => h3 (by rw [h, M.rev_rev]), h2⟩, h4, h5⟩
  · exact ⟨e, ⟨h1, h3, by rwa [M.rev_rev]⟩, h4, h5⟩

variable (T) in
open Classical in
/-- **The side of `d`**: the vertices reached from its tail in the cotree without its edge. -/
noncomputable def side (d : D) : Finset V :=
  univ.filter fun v => Relation.ReflTransGen (T.CAdjA d) (M.tail d) v

lemma mem_side {d : D} {v : V} :
    v ∈ T.side d ↔ Relation.ReflTransGen (T.CAdjA d) (M.tail d) v := by
  simp [side]

/-- **The head of a dart off the tree is not on its side**: the cotree is acyclic. -/
theorem head_not_mem_side (hM : M.IsPlane) {d : D} (hd : ¬ T.InT d) : M.head d ∉ T.side d := by
  intro hh
  obtain ⟨π, hπ, hπdiv, hπpos⟩ :=
    exists_pathFlow_of (A := fun e => ¬ T.InT e ∧ e ≠ d ∧ e ≠ M.rev d) (mem_side.1 hh)
  have hdd : d ≠ M.rev d := (M.rev_ne d).symm
  let κ : D → ℤ := π - (Pi.single d 1 - Pi.single (M.rev d) 1)
  have hcirc : M.IsCirc κ := by
    refine ⟨fun e => ?_, fun v => ?_⟩
    · have h1 := hπ e
      have h2 := isAntisymm_dart (M := M) d e
      simp only [κ, Pi.sub_apply] at h1 h2 ⊢
      rw [h1, h2]; ring
    · simp only [κ]
      rw [div_sub, hπdiv, div_dart]; ring
  have hoffκ : T.OffT κ := by
    intro e he
    have h1 : π e = 0 := pathFlow_zero hπ hπpos (fun h => h.1 he)
      (fun h => h.1 (T.inT_rev he))
    have h2 : e ≠ d := fun h => hd (h ▸ he)
    have h3 : e ≠ M.rev d := fun h => hd (T.inT_rev_iff.1 (h ▸ he))
    simp [κ, h1, h2, h3]
  have hκd := T.circ_eq_zero hM hcirc hoffκ d
  have hπd : π d ≤ 0 := by
    by_contra h
    exact (hπpos d (by omega)).2.1 rfl
  simp only [κ, Pi.sub_apply, Pi.single_apply, ite_true, hdd, ite_false] at hκd
  omega

/-- **The value of a flow of the cotree at a dart off the tree is the net divergence of its
side.** -/
theorem flow_eq_side (hM : M.IsPlane) {f : D → ℤ} (hf : M.IsAntisymm f) (hoff : T.OffT f)
    {d : D} (hd : ¬ T.InT d) : f d = ∑ v ∈ T.side d, M.div f v := by
  have hh := head_not_mem_side hM hd
  rw [sum_div_eq_out hf]
  symm
  refine sum_eq_single d (fun e he hne => ?_) (fun h => absurd ?_ h)
  · simp only [mem_filter, mem_univ, true_and] at he
    by_contra h0
    have hT : ¬ T.InT e := fun h => h0 (hoff e h)
    have hre : e ≠ M.rev d := by
      rintro rfl
      exact hh (by simpa using he.1)
    exact he.2 (mem_side.2 ((mem_side.1 he.1).tail ⟨e, ⟨hT, hne, hre⟩, rfl, rfl⟩))
  · simp only [mem_filter, mem_univ, true_and]
    exact ⟨mem_side.2 .refl, hh⟩

/-- The value at a dart off the tree of a unit flow of the cotree from `a` to `b`. -/
lemma unit_side (hM : M.IsPlane) {f : D → ℤ} (hf : M.IsAntisymm f) (hoff : T.OffT f) {a b : V}
    (hdiv : ∀ w, M.div f w = (if a = w then 1 else 0) - (if b = w then 1 else 0)) {d : D}
    (hd : ¬ T.InT d) :
    f d = (if a ∈ T.side d then 1 else 0) - (if b ∈ T.side d then 1 else 0) := by
  rw [flow_eq_side hM hf hoff hd]
  simp only [hdiv, sum_sub_distrib, sum_ite_eq]

/-- A walk avoiding the endpoints of `d₂` avoids its edge. -/
lemma rtg_avoid {d d₂ : D} {a b : V} (h : Relation.ReflTransGen (T.CAdjA d) a b)
    (hout : ∀ x, Relation.ReflTransGen (T.CAdjA d) a x → x ≠ M.tail d₂ ∧ x ≠ M.head d₂) :
    Relation.ReflTransGen (T.CAdjA d₂) a b := by
  induction h with
  | refl => exact .refl
  | tail hab hbc ih =>
    obtain ⟨e, ⟨h1, -, -⟩, he1, he2⟩ := hbc
    refine ih.tail ⟨e, ⟨h1, fun h => ?_, fun h => ?_⟩, he1, he2⟩
    · exact (hout _ hab).1 (by rw [← he1, h])
    · exact (hout _ hab).2 (by rw [← he1, h, M.tail_rev])

lemma ind_sub_eq_one {p q : Prop} [Decidable p] [Decidable q]
    (h : ((if p then 1 else 0) - (if q then 1 else 0) : ℤ) = 1) : p ∧ ¬ q := by
  split_ifs at h with hp hq <;> simp_all

lemma ind_sub_eq_neg_one {p q : Prop} [Decidable p] [Decidable q]
    (h : ((if p then 1 else 0) - (if q then 1 else 0) : ℤ) = -1) : ¬ p ∧ q := by
  split_ifs at h with hp hq <;> simp_all

/-- **Two darts of the path of the cotree are not crossed in opposite directions by a unit flow
of the cotree**: their sides are nested. -/
theorem no_cross (hM : M.IsPlane) {s t : V} {d₁ d₂ : D} (h₁ : T.chi s t d₁ = 1)
    (h₂ : T.chi s t d₂ = 1) {ρ : D → ℤ} (hρ : M.IsAntisymm ρ) (hoff : T.OffT ρ) {u v : V}
    (hdiv : ∀ w, M.div ρ w = (if v = w then 1 else 0) - (if u = w then 1 else 0))
    (hρ₁ : ρ d₁ = -1) (hρ₂ : ρ d₂ = 1) : False := by
  obtain ⟨χa, χdiv, χoff, -⟩ := T.chi_spec hM s t
  have hn : ∀ d, T.chi s t d = 1 → ¬ T.InT d := fun d h hT => by
    rw [χoff d hT] at h; exact absurd h (by norm_num)
  have hn₁ := hn d₁ h₁
  have hn₂ := hn d₂ h₂
  have hn₁' : ¬ T.InT (M.rev d₁) := fun h => hn₁ (T.inT_rev_iff.1 h)
  have c₁ := unit_side hM χa χoff χdiv hn₁
  have c₂ := unit_side hM χa χoff χdiv hn₂
  have cV := unit_side hM χa χoff χdiv hn₁'
  have r₁ := unit_side hM hρ hoff hdiv hn₁
  have r₂ := unit_side hM hρ hoff hdiv hn₂
  have rV := unit_side hM hρ hoff hdiv hn₁'
  rw [χa, h₁] at cV
  rw [hρ, hρ₁] at rV
  rw [h₁] at c₁
  rw [h₂] at c₂
  rw [hρ₁] at r₁
  rw [hρ₂] at r₂
  obtain ⟨hs₁, -⟩ := ind_sub_eq_one c₁.symm
  obtain ⟨hs₂, ht₂⟩ := ind_sub_eq_one c₂.symm
  obtain ⟨-, hu₁⟩ := ind_sub_eq_neg_one r₁.symm
  obtain ⟨hv₂, hu₂⟩ := ind_sub_eq_one r₂.symm
  obtain ⟨-, htV⟩ := ind_sub_eq_neg_one cV.symm
  obtain ⟨hvV, -⟩ := ind_sub_eq_one (by rw [← rV]; ring)
  have hne₁ : d₂ ≠ d₁ := by rintro rfl; rw [hρ₁] at hρ₂; norm_num at hρ₂
  have hne₂ : d₂ ≠ M.rev d₁ := by
    rintro rfl; rw [χa, h₁] at h₂; norm_num at h₂
  have hd₂ : T.CAdjA d₁ (M.tail d₂) (M.head d₂) := ⟨d₂, ⟨hn₂, hne₁, hne₂⟩, rfl, rfl⟩
  have hmemV : ∀ x, x ∈ T.side (M.rev d₁) →
      Relation.ReflTransGen (T.CAdjA d₁) (M.head d₁) x := fun x hx => by
    have := mem_side.1 hx
    rwa [cAdjA_rev, M.tail_rev] at this
  by_cases hA : M.tail d₂ ∈ T.side d₁
  · have hA' : M.head d₂ ∈ T.side d₁ := mem_side.2 ((mem_side.1 hA).tail hd₂)
    have hVout : ∀ x, Relation.ReflTransGen (T.CAdjA d₁) (M.head d₁) x → x ∉ T.side d₁ :=
      fun x hx hxU => head_not_mem_side hM hn₁ (mem_side.2 ((mem_side.1 hxU).trans
        (rtg_symm hx)))
    have hp : ∀ x, Relation.ReflTransGen (T.CAdjA d₁) (M.head d₁) x →
        Relation.ReflTransGen (T.CAdjA d₂) (M.head d₁) x := fun x hx =>
      rtg_avoid hx fun y hy => ⟨fun e => hVout y hy (by rw [e]; exact hA),
        fun e => hVout y hy (by rw [e]; exact hA')⟩
    have ht := hp _ (hmemV _ htV)
    have hv := hp _ (hmemV _ hvV)
    exact ht₂ (mem_side.2 ((mem_side.1 hv₂).trans ((rtg_symm hv).trans ht)))
  · have hB' : M.head d₂ ∉ T.side d₁ := fun h =>
      hA (mem_side.2 ((mem_side.1 h).tail hd₂.symm))
    have hp : ∀ x, Relation.ReflTransGen (T.CAdjA d₁) (M.tail d₁) x →
        Relation.ReflTransGen (T.CAdjA d₂) (M.tail d₁) x := fun x hx =>
      rtg_avoid hx fun y hy => ⟨fun e => hA (by rw [← e]; exact mem_side.2 hy),
        fun e => hB' (by rw [← e]; exact mem_side.2 hy)⟩
    have hs := hp _ (mem_side.1 hs₁)
    have hu := hp _ (mem_side.1 hu₁)
    exact hu₂ (mem_side.2 ((mem_side.1 hs₂).trans ((rtg_symm hs).trans hu)))

/-! ### The fundamental cycles -/

section Fund

open Classical

variable (T) in
/-- **The unit flow of the cotree of a subtree**: the coboundary of the indicator of the subtree
of the face `y`, minus the parent dart of `y`. -/
noncomputable def subFlow (y : F) : D → ℤ :=
  M.cob (fun x => if T.Anc y x then 1 else 0) -
    (Pi.single (T.par y) 1 - Pi.single (M.rev (T.par y)) 1)

lemma subFlow_antisymm (y : F) : M.IsAntisymm (T.subFlow y) := by
  intro d
  have h1 := M.cob_antisymm (fun x => if T.Anc y x then (1 : ℤ) else 0) d
  have h2 := isAntisymm_dart (M := M) (T.par y) d
  simp only [subFlow, Pi.sub_apply] at h1 h2 ⊢
  rw [h1, h2]; ring

lemma subFlow_div (y : F) (w : V) :
    M.div (T.subFlow y) w =
      (if M.head (T.par y) = w then 1 else 0) - (if M.tail (T.par y) = w then 1 else 0) := by
  rw [subFlow, div_sub, div_dart]
  have : M.div (M.cob (fun x => if T.Anc y x then (1 : ℤ) else 0)) w = 0 := M.div_cob _ w
  rw [this]; ring

/-- Off the parent darts, `subFlow` is the coboundary of the subtree. -/
lemma subFlow_of_ne {y : F} {d : D} (h1 : d ≠ T.par y) (h2 : d ≠ M.rev (T.par y)) :
    T.subFlow y d = (if T.Anc y (M.face (M.rev d)) then 1 else 0) -
      (if T.Anc y (M.face d) then 1 else 0) := by
  simp [subFlow, cob, h1, h2]

lemma subFlow_par {y : F} (hy : y ≠ T.root) {x : F} (hx : x ≠ T.root) :
    T.subFlow y (T.par x) = 0 := by
  have hpp : T.par y ≠ M.rev (T.par y) := (M.rev_ne _).symm
  by_cases hxy : x = y
  · subst hxy
    simp only [subFlow, Pi.sub_apply, cob, Pi.single_apply, ite_true, hpp, ite_false]
    rw [T.head_par x hx, ← T.up_of_ne hx]
    simp [T.anc_self x, T.not_anc_up hx]
  · have hne1 : T.par x ≠ T.par y := fun h => hxy (by
      rw [← T.head_par x hx, ← T.head_par y hy, h])
    have hne2 : T.par x ≠ M.rev (T.par y) := fun h => by
      have e1 : x = T.up y := by
        rw [← T.head_par x hx, h, M.rev_rev, T.up_of_ne hy]
      have e2 : T.up x = y := by
        rw [T.up_of_ne hx, h, T.head_par y hy]
      exact T.not_anc_up hy ⟨1, by rw [← e1]; simpa using e2⟩
    rw [subFlow_of_ne hne1 hne2, T.head_par x hx, ← T.up_of_ne hx, T.anc_up_iff hxy]
    simp

lemma subFlow_offT {y : F} (hy : y ≠ T.root) : T.OffT (T.subFlow y) := by
  rintro d ⟨x, hx, rfl | rfl⟩
  · exact subFlow_par hy hx
  · rw [subFlow_antisymm, subFlow_par hy hx, neg_zero]

/-- **The difference of the fundamental cycles of two darts of the path has the coefficients
`-1`, `0`, `1`**: no subtree of the dual tree contains `face d₁` and `face (rev d₂)` without
`face (rev d₁)` and `face d₂`, nor `face (rev d₁)` and `face d₂` without `face d₁` and
`face (rev d₂)`. -/
theorem not_cross (hM : M.IsPlane) {s t : V} {d₁ d₂ : D} (h₁ : T.chi s t d₁ = 1)
    (h₂ : T.chi s t d₂ = 1) {y : F} (hy : y ≠ T.root) :
    ¬ (T.Anc y (M.face d₁) ∧ ¬ T.Anc y (M.face (M.rev d₁)) ∧ T.Anc y (M.face (M.rev d₂)) ∧
        ¬ T.Anc y (M.face d₂)) ∧
      ¬ (T.Anc y (M.face (M.rev d₁)) ∧ ¬ T.Anc y (M.face d₁) ∧ T.Anc y (M.face d₂) ∧
        ¬ T.Anc y (M.face (M.rev d₂))) := by
  obtain ⟨-, -, χoff, -⟩ := T.chi_spec hM s t
  have hn : ∀ d, T.chi s t d = 1 → d ≠ T.par y ∧ d ≠ M.rev (T.par y) := fun d h => by
    have hT : ¬ T.InT d := fun hT => by rw [χoff d hT] at h; exact absurd h (by norm_num)
    exact ⟨fun e => hT (e ▸ T.inT_par hy), fun e => hT (e ▸ T.inT_rev (T.inT_par hy))⟩
  have e₁ := subFlow_of_ne (hn d₁ h₁).1 (hn d₁ h₁).2
  have e₂ := subFlow_of_ne (hn d₂ h₂).1 (hn d₂ h₂).2
  constructor
  · rintro ⟨a1, a2, a3, a4⟩
    exact no_cross hM h₁ h₂ (subFlow_antisymm y) (subFlow_offT hy) (subFlow_div y)
      (by rw [e₁]; simp [a1, a2]) (by rw [e₂]; simp [a3, a4])
  · rintro ⟨a1, a2, a3, a4⟩
    have hneg : M.IsAntisymm (-T.subFlow y) := fun d => by
      simp only [Pi.neg_apply, subFlow_antisymm y d]
    have hoffn : T.OffT (-T.subFlow y) := fun d hd => by
      simp only [Pi.neg_apply, subFlow_offT hy d hd, neg_zero]
    refine no_cross hM h₁ h₂ hneg hoffn (u := M.head (T.par y)) (v := M.tail (T.par y))
      (fun w => ?_) (by simp only [Pi.neg_apply]; rw [e₁]; simp [a1, a2])
      (by simp only [Pi.neg_apply]; rw [e₂]; simp [a3, a4])
    rw [div_neg' (T.subFlow y) w, subFlow_div]; ring

end Fund

end DTree

/-! ### The base-`B` expansion of the comparison -/

/-- The index of a dart (the exponent of its perturbation). -/
noncomputable def didx (e : D) : ℕ := Fintype.equivFin D e

lemma didx_injective : Function.Injective (didx (D := D)) := fun _ _ h =>
  (Fintype.equivFin D).injective (Fin.ext h)

lemma lexEps_eq (e : D) : lexEps D F e = (lexBase F : ℤ) ^ didx e := rfl

lemma geom_lt {B : ℕ} (hB : 2 ≤ B) : ∀ k : ℕ, ∑ j ∈ range k, (B : ℤ) ^ j < (B : ℤ) ^ k
  | 0 => by simp
  | k + 1 => by
    rw [sum_range_succ, pow_succ]
    have := geom_lt hB k
    have h0 : (0 : ℤ) ≤ (B : ℤ) ^ k := by positivity
    have h2 : (2 : ℤ) ≤ B := by exact_mod_cast hB
    nlinarith

/-- **A sum of `±B ^ (index)` with coefficients `-1`, `0`, `1` has the sign of its top
coefficient.** -/
theorem sum_pos_of_top {B : ℕ} (hB : 2 ≤ B) {a : D → ℤ} (ha : ∀ e, |a e| ≤ 1) {e₀ : D}
    (h0 : a e₀ = 1) (htop : ∀ e, didx e₀ < didx e → a e = 0) :
    0 < ∑ e, a e * (B : ℤ) ^ didx e := by
  classical
  set k := didx e₀
  let g : D → ℤ := fun e => if e = e₀ then (B : ℤ) ^ k else if didx e < k then -(B : ℤ) ^ didx e
    else 0
  have hg : ∀ e, g e ≤ a e * (B : ℤ) ^ didx e := by
    intro e
    have hp : (0 : ℤ) ≤ (B : ℤ) ^ didx e := by positivity
    have hae := abs_le.1 (ha e)
    by_cases he : e = e₀
    · subst he; simp [g, h0, k]
    · simp only [g, he, ite_false]
      split_ifs with hlt
      · nlinarith
      · have hne : didx e ≠ k := fun h => he (didx_injective h)
        rw [htop e (by omega), zero_mul]
  have hsum : ∑ e, g e = (B : ℤ) ^ k - ∑ e ∈ univ.filter (fun e : D => didx e < k), (B : ℤ) ^ didx e
      := by
    have : ∀ e, g e = (if e = e₀ then (B : ℤ) ^ k else 0) -
        (if didx e < k then (B : ℤ) ^ didx e else 0) := fun e => by
      by_cases he : e = e₀
      · subst he; simp [g, k]
      · simp only [g, he, ite_false]; split_ifs <;> ring
    simp only [this, sum_sub_distrib, sum_ite_eq', mem_univ, ite_true, sum_filter]
  have himg : ∑ e ∈ univ.filter (fun e : D => didx e < k), (B : ℤ) ^ didx e ≤
      ∑ j ∈ range k, (B : ℤ) ^ j := by
    rw [← sum_image (fun _ _ _ _ h => didx_injective h)]
    refine sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun j _ _ => by positivity)
    obtain ⟨e, he, rfl⟩ := mem_image.1 hj
    simpa using (mem_filter.1 he).2
  have := geom_lt hB k
  calc (0 : ℤ) < ∑ e, g e := by rw [hsum]; linarith
    _ ≤ _ := sum_le_sum fun e _ => hg e

namespace DTree

variable {T : DTree M}

lemma psum_eq_sum (T : DTree M) (φ : D → ℤ) (x : F) :
    T.psum φ x = ∑ e, (if e ∈ T.tpath x then 1 else 0) * φ e := by
  rw [← T.dsum_tpath, dsum_eq_count]
  refine sum_congr rfl fun e _ => ?_
  congr 1
  split_ifs with h
  · exact_mod_cast List.count_eq_one_of_mem (T.nodup_tpath x) h
  · exact_mod_cast List.count_eq_zero.2 h

variable (T) in
/-- **The coefficient of the dart `e` in `lred ε T d₁ - lred ε T d₂`**: `±1` at `d₁`, `d₂`, and
the signed count of the four tree paths from the root to the faces of `d₁` and `d₂`. -/
noncomputable def lcoef (d₁ d₂ e : D) : ℤ :=
  (if e = d₁ then 1 else 0) - (if e = d₂ then 1 else 0) +
    (if e ∈ T.tpath (M.face d₁) then 1 else 0) -
    (if e ∈ T.tpath (M.face (M.rev d₁)) then 1 else 0) -
    (if e ∈ T.tpath (M.face d₂) then 1 else 0) +
    (if e ∈ T.tpath (M.face (M.rev d₂)) then 1 else 0)

/-- **The difference of the perturbation parts is the sum of the coefficients times `ε`.** -/
theorem lred_sub_eq (ε : D → ℤ) (d₁ d₂ : D) :
    lred ε T d₁ - lred ε T d₂ = ∑ e, T.lcoef d₁ d₂ e * ε e := by
  simp only [lred, cob, psum_eq_sum T ε, lcoef, add_mul, sub_mul, sum_add_distrib,
    sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
  ring

lemma not_mem_tpath_of_not_inT {d : D} (hd : ¬ T.InT d) (x : F) : d ∉ T.tpath x := fun h => by
  obtain ⟨y, hy, -, rfl⟩ := T.mem_tpath.1 h
  exact hd (T.inT_par hy)

/-- On the parent dart of `y`, membership in the path to `x` is `Anc y x`. -/
lemma mem_tpath_par {y x : F} (hy : y ≠ T.root) : T.par y ∈ T.tpath x ↔ T.Anc y x := by
  rw [T.mem_tpath]
  constructor
  · rintro ⟨y', hy', ha, he⟩
    have : y' = y := by rw [← T.head_par y' hy', he, T.head_par y hy]
    exact this ▸ ha
  · exact fun ha => ⟨y, hy, ha, rfl⟩

/-- **The coefficients are `-1`, `0` or `1`** for two distinct darts of the path of the cotree
(`not_cross`). -/
theorem abs_lcoef_le (hM : M.IsPlane) {s t : V} {d₁ d₂ : D} (h₁ : T.chi s t d₁ = 1)
    (h₂ : T.chi s t d₂ = 1) (hne : d₁ ≠ d₂) (e : D) : |T.lcoef d₁ d₂ e| ≤ 1 := by
  obtain ⟨-, -, χoff, -⟩ := T.chi_spec hM s t
  have hn : ∀ d, T.chi s t d = 1 → ¬ T.InT d := fun d h hT => by
    rw [χoff d hT] at h; exact absurd h (by norm_num)
  by_cases hin : e ∈ T.tpath (M.face d₁) ∨ e ∈ T.tpath (M.face (M.rev d₁)) ∨
      e ∈ T.tpath (M.face d₂) ∨ e ∈ T.tpath (M.face (M.rev d₂))
  · obtain ⟨x, hx⟩ : ∃ x, e ∈ T.tpath x := by
      rcases hin with h | h | h | h <;> exact ⟨_, h⟩
    obtain ⟨hy, -, hpar⟩ := T.head_tpath hx
    set y := M.face (M.rev e)
    have hTe : T.InT e := hpar ▸ T.inT_par hy
    have he1 : e ≠ d₁ := fun h => hn d₁ h₁ (h ▸ hTe)
    have he2 : e ≠ d₂ := fun h => hn d₂ h₂ (h ▸ hTe)
    obtain ⟨nc1, nc2⟩ := not_cross hM h₁ h₂ hy
    have hm : ∀ x, e ∈ T.tpath x ↔ T.Anc y x := fun x => hpar ▸ mem_tpath_par hy
    simp only [lcoef, he1, he2, ite_false, hm]
    rw [abs_le]
    by_cases a1 : T.Anc y (M.face d₁) <;> by_cases a2 : T.Anc y (M.face (M.rev d₁)) <;>
      by_cases a3 : T.Anc y (M.face d₂) <;> by_cases a4 : T.Anc y (M.face (M.rev d₂)) <;>
      simp_all
  · push Not at hin
    obtain ⟨n1, n2, n3, n4⟩ := hin
    simp only [lcoef, n1, n2, n3, n4, ite_false]
    rw [abs_le]
    by_cases a : e = d₁
    · subst a; simp [hne]
    · simp only [a, ite_false]; split_ifs <;> norm_num

/-- **The comparison of the perturbation parts of two darts of the path**: `lred d₁ < lred d₂`
exactly when the coefficient of the top index (the largest index with a nonzero coefficient) is
`-1`. -/
theorem lred_lt_iff (hM : M.IsPlane) {s t : V} {d₁ d₂ : D} (h₁ : T.chi s t d₁ = 1)
    (h₂ : T.chi s t d₂ = 1) (hne : d₁ ≠ d₂) :
    lred (lexEps D F) T d₁ < lred (lexEps D F) T d₂ ↔
      ∃ e, T.lcoef d₁ d₂ e = -1 ∧ ∀ e', didx e < didx e' → T.lcoef d₁ d₂ e' = 0 := by
  classical
  obtain ⟨-, -, χoff, -⟩ := T.chi_spec hM s t
  have hn1 : ¬ T.InT d₁ := fun hT => by rw [χoff d₁ hT] at h₁; exact absurd h₁ (by norm_num)
  have ha := abs_lcoef_le hM h₁ h₂ hne
  have hB : 2 ≤ lexBase F := by unfold lexBase; omega
  have hsub := lred_sub_eq (T := T) (lexEps D F) d₁ d₂
  simp only [lexEps_eq] at hsub
  have hd1 : T.lcoef d₁ d₂ d₁ = 1 := by
    simp [lcoef, hne, not_mem_tpath_of_not_inT hn1]
  obtain ⟨e₀, he₀, hmax⟩ := (univ.filter fun e => T.lcoef d₁ d₂ e ≠ 0).exists_max_image didx
    ⟨d₁, by simp [hd1]⟩
  simp only [mem_filter, mem_univ, true_and] at he₀ hmax
  have htop : ∀ e, didx e₀ < didx e → T.lcoef d₁ d₂ e = 0 := fun e he => by
    by_contra h; have := hmax e h; omega
  have hcases := abs_le.1 (ha e₀)
  have hval : T.lcoef d₁ d₂ e₀ = 1 ∨ T.lcoef d₁ d₂ e₀ = -1 := by omega
  rcases hval with hv | hv
  · have hpos := sum_pos_of_top hB ha hv htop
    constructor
    · intro h; linarith
    · rintro ⟨e, he, he'⟩
      have h1 : didx e ≤ didx e₀ := hmax e (by rw [he]; norm_num)
      rcases h1.lt_or_eq with h1 | h1
      · rw [he' e₀ h1] at hv; norm_num at hv
      · rw [didx_injective h1, hv] at he; norm_num at he
  · have hneg := sum_pos_of_top hB (a := fun e => -T.lcoef d₁ d₂ e) (fun e => by
      rw [abs_neg]; exact ha e) (show -T.lcoef d₁ d₂ e₀ = 1 by rw [hv]; norm_num)
      (fun e he => by simp [htop e he])
    simp only [neg_mul, sum_neg_distrib] at hneg
    refine ⟨fun _ => ⟨e₀, hv, htop⟩, fun _ => by linarith⟩

variable (T) in
/-- The coefficient of `e` in `lred ε T d`: `1` at `d`, and the paths to the faces of `d`. -/
noncomputable def lcoef1 (d e : D) : ℤ :=
  (if e = d then 1 else 0) + (if e ∈ T.tpath (M.face d) then 1 else 0) -
    (if e ∈ T.tpath (M.face (M.rev d)) then 1 else 0)

lemma lred_eq_sum (ε : D → ℤ) (d : D) : lred ε T d = ∑ e, T.lcoef1 d e * ε e := by
  simp only [lred, cob, psum_eq_sum T ε, lcoef1, add_mul, sub_mul, sum_add_distrib,
    sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
  ring

/-- **The sign of the perturbation part of one dart off the tree**: `lred d > 0` exactly when
the coefficient of the top index is `1`; so the feasibility of a tree for the lexicographic
lengths (`DTree.LexFeas`, on the darts tight in the first coordinate) is checked with the
indices of two tree paths. -/
theorem lred_pos_iff {d : D} (hd : ¬ T.InT d) :
    0 < lred (lexEps D F) T d ↔
      ∃ e, T.lcoef1 d e = 1 ∧ ∀ e', didx e < didx e' → T.lcoef1 d e' = 0 := by
  classical
  have hB : 2 ≤ lexBase F := by unfold lexBase; omega
  have hsum := lred_eq_sum (T := T) (lexEps D F) d
  simp only [lexEps_eq] at hsum
  have ha : ∀ e, |T.lcoef1 d e| ≤ 1 := fun e => by
    unfold lcoef1
    by_cases h1 : e = d
    · subst h1; simp [not_mem_tpath_of_not_inT hd]
    · simp only [h1, ite_false, zero_add]
      rw [abs_le]; constructor <;> split_ifs <;> norm_num
  have hd1 : T.lcoef1 d d = 1 := by simp [lcoef1, not_mem_tpath_of_not_inT hd]
  obtain ⟨e₀, he₀, hmax⟩ := (univ.filter fun e => T.lcoef1 d e ≠ 0).exists_max_image didx
    ⟨d, by simp [hd1]⟩
  simp only [mem_filter, mem_univ, true_and] at he₀ hmax
  have htop : ∀ e, didx e₀ < didx e → T.lcoef1 d e = 0 := fun e he => by
    by_contra h; have := hmax e h; omega
  have hcases := abs_le.1 (ha e₀)
  rcases (show T.lcoef1 d e₀ = 1 ∨ T.lcoef1 d e₀ = -1 by omega) with hv | hv
  · exact ⟨fun _ => ⟨e₀, hv, htop⟩, fun _ => by rw [hsum]; exact sum_pos_of_top hB ha hv htop⟩
  · have hneg := sum_pos_of_top hB (a := fun e => -T.lcoef1 d e) (fun e => by
      rw [abs_neg]; exact ha e) (show -T.lcoef1 d e₀ = 1 by rw [hv]; norm_num)
      (fun e he => by simp [htop e he])
    simp only [neg_mul, sum_neg_distrib] at hneg
    constructor
    · intro h; rw [hsum] at h; linarith
    · rintro ⟨e, he, he'⟩
      have h1 : didx e ≤ didx e₀ := hmax e (by rw [he]; norm_num)
      rcases h1.lt_or_eq with h1 | h1
      · rw [he' e₀ h1] at hv; norm_num at hv
      · rw [← didx_injective h1, he] at hv; norm_num at hv

/-- **The perturbation part of a dart off the tree is not zero.** -/
theorem lred_ne_zero {d : D} (hd : ¬ T.InT d) : lred (lexEps D F) T d ≠ 0 := by
  intro h0
  by_cases hp : 0 < lred (lexEps D F) T d
  · linarith
  · obtain ⟨e, he, he'⟩ : ∃ e, T.lcoef1 d e = 1 ∧ ∀ e', didx e < didx e' → T.lcoef1 d e' = 0 :=
      by
      classical
      have hB : 2 ≤ lexBase F := by unfold lexBase; omega
      have hsum := lred_eq_sum (T := T) (lexEps D F) d
      simp only [lexEps_eq] at hsum
      have ha : ∀ e, |T.lcoef1 d e| ≤ 1 := fun e => by
        unfold lcoef1
        by_cases h1 : e = d
        · subst h1; simp [not_mem_tpath_of_not_inT hd]
        · simp only [h1, ite_false, zero_add]
          rw [abs_le]; constructor <;> split_ifs <;> norm_num
      have hd1 : T.lcoef1 d d = 1 := by simp [lcoef1, not_mem_tpath_of_not_inT hd]
      obtain ⟨e₀, he₀, hmax⟩ := (univ.filter fun e => T.lcoef1 d e ≠ 0).exists_max_image didx
        ⟨d, by simp [hd1]⟩
      simp only [mem_filter, mem_univ, true_and] at he₀ hmax
      have htop : ∀ e, didx e₀ < didx e → T.lcoef1 d e = 0 := fun e he => by
        by_contra h; have := hmax e h; omega
      have hcases := abs_le.1 (ha e₀)
      rcases (show T.lcoef1 d e₀ = 1 ∨ T.lcoef1 d e₀ = -1 by omega) with hv | hv
      · exact ⟨e₀, hv, htop⟩
      · exfalso
        have hneg := sum_pos_of_top hB (a := fun e => -T.lcoef1 d e) (fun e => by
          rw [abs_neg]; exact ha e) (show -T.lcoef1 d e₀ = 1 by rw [hv]; norm_num)
          (fun e he => by simp [htop e he])
        simp only [neg_mul, sum_neg_distrib] at hneg
        rw [hsum] at h0; linarith
    exact hp ((lred_pos_iff hd).2 ⟨e, he, he'⟩)

end DTree

/-! ### Checking the feasibility of a tree -/

/-- **The feasibility of a tree for the lexicographic lengths, on unperturbed values and
indices**: `T.LexFeas c (lexEps D F)` holds exactly when no dart is shorter than the difference
of the path sums of `c` at its ends, and every dart off the tree that is tight for `c` has the
top coefficient `1` in `lred` (`lred_pos_iff`): a condition checked with word-size numbers and
the indices of the darts of two tree paths per dart. -/
theorem lexFeas_iff_top (T : DTree M) (c : D → ℤ) :
    T.LexFeas c (lexEps D F) ↔ ∀ d, M.cob (T.psum c) d ≤ c d ∧
      (M.cob (T.psum c) d = c d → ¬ T.InT d →
        ∃ e, T.lcoef1 d e = 1 ∧ ∀ e', didx e < didx e' → T.lcoef1 d e' = 0) := by
  have hle : ∀ d, M.cob (T.psum (lexEps D F)) d ≤ lexEps D F d ↔ 0 ≤ lred (lexEps D F) T d :=
    fun d => by unfold lred; constructor <;> intro h <;> linarith
  have htree : ∀ d, T.InT d → 0 ≤ lred (lexEps D F) T d := by
    rintro d ⟨x, hx, rfl | rfl⟩
    · have := T.psum_of_ne (lexEps D F) hx
      unfold lred; simp only [cob]
      rw [T.head_par x hx, ← T.up_of_ne hx]; linarith
    · have := T.psum_of_ne (lexEps D F) hx
      have h1 := lexEps_nonneg (F := F) (T.par x)
      have h2 := lexEps_nonneg (F := F) (M.rev (T.par x))
      unfold lred; simp only [cob, M.rev_rev]
      rw [T.head_par x hx, ← T.up_of_ne hx]; linarith
  refine forall_congr' fun d => and_congr Iff.rfl (imp_congr_right fun _ => ?_)
  rw [hle]
  constructor
  · intro h hd
    exact (DTree.lred_pos_iff hd).1 (lt_of_le_of_ne h (Ne.symm (DTree.lred_ne_zero hd)))
  · intro h
    by_cases hd : T.InT d
    · exact htree d hd
    · exact ((DTree.lred_pos_iff hd).2 (h hd)).le

/-! ### The comparisons of the perturbed run -/

/-- **The comparison of two darts of the path of the cotree made by the perturbed run**
(`lbott`), on the unperturbed residual capacities and the indices of four tree paths: the
residual pair of `d₁` is lexicographically below that of `d₂` exactly when its unperturbed
residual capacity is smaller, or equal with the top coefficient of `lcoef` equal to `-1`. -/
theorem lslack_lt_iff (hM : M.IsPlane) {s t : V} (hst : s ≠ t) {c : D → ℤ} {st : LSt M}
    (hI : LInv c (lexEps D F) s t st) {d₁ d₂ : D} (h₁ : st.T.chi s t d₁ = 1)
    (h₂ : st.T.chi s t d₂ = 1) (hne : d₁ ≠ d₂) :
    lslack c (lexEps D F) st.g st.h d₁ < lslack c (lexEps D F) st.g st.h d₂ ↔
      c d₁ - st.g d₁ < c d₂ - st.g d₂ ∨ (c d₁ - st.g d₁ = c d₂ - st.g d₂ ∧
        ∃ e, st.T.lcoef d₁ d₂ e = -1 ∧ ∀ e', didx e < didx e' → st.T.lcoef d₁ d₂ e' = 0) := by
  rw [lslack, lslack, Prod.Lex.toLex_lt_toLex, linv_slack2 hM hst hI h₁,
    linv_slack2 hM hst hI h₂, ← DTree.lred_lt_iff hM h₁ h₂ hne, sub_lt_sub_iff_right]

/-- **A dart of the path below every other dart of the path is the perturbed bottleneck.** -/
theorem lbott_eq_of_lt {c ε : D → ℤ} {s t : V} {g h : D → ℤ} {T : DTree M}
    (hne : (pathSet s t T).Nonempty) {e : D} (he : T.chi s t e = 1)
    (hlt : ∀ d, T.chi s t d = 1 → d ≠ e → lslack c ε g h e < lslack c ε g h d) :
    lbott c ε s t g h T hne = e := by
  by_contra hb
  exact absurd (lbott_min c ε s t g h T hne he)
    (not_le.2 (hlt _ (lbott_mem c ε s t g h T hne) hb))

end STFlow

end PlanarFlow
