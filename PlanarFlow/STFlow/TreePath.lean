module

public import PlanarFlow.STFlow.Param
public import PlanarFlow.STFlow.PivotCount

/-!
# The paths of a dual tree as walks, and the uniqueness of the perturbed lengths

* `DTree.tpath T x`: the darts of the path of the tree from the root to `x`, as a dual walk
  (`DTree.dWalk_tpath`); the sum of `φ` along it is the path sum `psum φ x` (`dsum_tpath`); its
  darts are the parent darts of the ancestors of `x` other than the root, each once.
* `DTree.eq_tpath_of_count`: **a dual walk from the root to `x` using every dart as often as the
  path of the tree is the path of the tree.**
* `eq_of_sum_pow`: **base-`B` digits**: two families of digits `< B` with the same value are
  equal; so the perturbation `ε d = B ^ (index of d)` separates the multisets of darts with
  multiplicities `< B` (`count_eq_of_dsum_eq`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-! ### Dual walks -/

lemma dWalk_nil {x y : F} : DWalk M x [] y ↔ x = y := Iff.rfl

lemma dWalk_append {x z : F} {l l' : List D} :
    DWalk M x (l ++ l') z ↔ ∃ y, DWalk M x l y ∧ DWalk M y l' z :=
  isWalk_append_iff

lemma dWalk_singleton {x y : F} {d : D} :
    DWalk M x [d] y ↔ M.face d = x ∧ M.face (M.rev d) = y :=
  isWalk_singleton

lemma dWalk_concat {x z : F} {l : List D} {d : D} :
    DWalk M x (l ++ [d]) z ↔ DWalk M x l (M.face d) ∧ M.face (M.rev d) = z := by
  rw [dWalk_append]
  constructor
  · rintro ⟨y, h1, h2⟩
    obtain ⟨rfl, rfl⟩ := dWalk_singleton.1 h2
    exact ⟨h1, rfl⟩
  · rintro ⟨h1, rfl⟩
    exact ⟨_, h1, dWalk_singleton.2 ⟨rfl, rfl⟩⟩

/-! ### The paths of a tree -/

namespace DTree

variable (T : DTree M)

/-- The last `n` steps of the path to `x`, from the root side. -/
def tpathAux : ℕ → F → List D
  | 0, _ => []
  | n + 1, x => tpathAux n (T.up x) ++ [T.par x]

/-- **The path of the tree from the root to `x`**, as a list of darts. -/
def tpath (x : F) : List D := T.tpathAux (T.depth x) x

lemma tpath_root : T.tpath T.root = [] := by simp [tpath, depth_root, tpathAux]

lemma tpath_of_ne {x : F} (hx : x ≠ T.root) : T.tpath x = T.tpath (T.up x) ++ [T.par x] := by
  rw [tpath, T.depth_up hx]; rfl

/-- An induction principle on the depth. -/
lemma depth_induction {p : F → Prop} (h0 : p T.root) (h1 : ∀ x, x ≠ T.root → p (T.up x) → p x)
    (x : F) : p x := by
  induction hn : T.depth x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases hx : x = T.root
    · subst hx; exact h0
    · exact h1 x hx (ih _ (by rw [← hn, T.depth_up hx]; omega) _ rfl)

lemma dWalk_tpath (x : F) : DWalk M T.root (T.tpath x) x := by
  refine T.depth_induction (p := fun x => DWalk M T.root (T.tpath x) x) ?_ ?_ x
  · rw [tpath_root]; exact rfl
  · intro x hx ih
    rw [T.tpath_of_ne hx, dWalk_concat, ← T.up_of_ne hx]
    exact ⟨ih, T.head_par x hx⟩

lemma dsum_tpath (φ : D → ℤ) (x : F) : dsum φ (T.tpath x) = T.psum φ x := by
  refine T.depth_induction (p := fun x => dsum φ (T.tpath x) = T.psum φ x) ?_ ?_ x
  · rw [tpath_root, psum_root]; rfl
  · intro x hx ih
    rw [T.tpath_of_ne hx, dsum_append, ih, T.psum_of_ne φ hx]
    simp

lemma mem_tpath {x : F} {d : D} :
    d ∈ T.tpath x ↔ ∃ y, y ≠ T.root ∧ T.Anc y x ∧ T.par y = d := by
  refine T.depth_induction (p := fun x => d ∈ T.tpath x ↔
    ∃ y, y ≠ T.root ∧ T.Anc y x ∧ T.par y = d) ?_ ?_ x
  · rw [tpath_root]
    simp only [List.not_mem_nil, false_iff, not_exists, not_and]
    intro y hy ha
    exact absurd (T.anc_root_iff.1 ha) hy
  · intro x hx ih
    rw [T.tpath_of_ne hx, List.mem_append, ih, List.mem_singleton]
    constructor
    · rintro (⟨y, hy, ha, rfl⟩ | rfl)
      · exact ⟨y, hy, T.anc_of_up ha, rfl⟩
      · exact ⟨x, hx, T.anc_self x, rfl⟩
    · rintro ⟨y, hy, ha, rfl⟩
      by_cases hyx : x = y
      · subst hyx; right; rfl
      · left; exact ⟨y, hy, (T.anc_up_iff hyx).1 ha, rfl⟩

/-- The darts of the path enter distinct faces. -/
lemma head_tpath {x : F} {d : D} (hd : d ∈ T.tpath x) :
    M.face (M.rev d) ≠ T.root ∧ T.Anc (M.face (M.rev d)) x ∧ T.par (M.face (M.rev d)) = d := by
  obtain ⟨y, hy, ha, rfl⟩ := T.mem_tpath.1 hd
  rw [T.head_par y hy]
  exact ⟨hy, ha, rfl⟩

lemma nodup_tpath (x : F) : (T.tpath x).Nodup := by
  refine T.depth_induction (p := fun x => (T.tpath x).Nodup) ?_ ?_ x
  · rw [tpath_root]; exact List.nodup_nil
  · intro x hx ih
    rw [T.tpath_of_ne hx, List.nodup_append]
    refine ⟨ih, List.nodup_singleton _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    rintro rfl
    obtain ⟨-, hanc, -⟩ := T.head_tpath ha
    rw [T.head_par x hx] at hanc
    exact T.not_anc_up hx hanc

/-- **A dual walk from the root to `x` using every dart as often as the path of the tree is the
path of the tree.** -/
theorem eq_tpath_of_count {x : F} {l : List D} (hl : DWalk M T.root l x)
    (hc : ∀ d, l.count d = (T.tpath x).count d) : l = T.tpath x := by
  induction hn : T.depth x using Nat.strong_induction_on generalizing x l with
  | _ n ih =>
    by_cases hx : x = T.root
    · subst hx
      rw [tpath_root] at hc ⊢
      exact List.eq_nil_iff_forall_not_mem.2 fun d hd => by
        have := hc d
        rw [List.count_nil, List.count_eq_zero] at this
        exact this hd
    · rcases List.eq_nil_or_concat' l with rfl | ⟨l', a, rfl⟩
      · exact absurd (dWalk_nil.1 hl).symm hx
      obtain ⟨hl', ha⟩ := dWalk_concat.1 hl
      have hmem : a ∈ T.tpath x := by
        rw [← List.count_pos_iff, ← hc]; simp
      obtain ⟨-, -, hpar⟩ := T.head_tpath hmem
      rw [ha] at hpar
      subst hpar
      rw [T.tpath_of_ne hx]
      rw [← T.up_of_ne hx] at hl'
      congr 1
      refine ih _ (by rw [← hn, T.depth_up hx]; omega) hl' (fun d => ?_) rfl
      have := hc d
      rw [T.tpath_of_ne hx, List.count_append, List.count_append] at this
      omega

end DTree

/-! ### Base-`B` digits -/

lemma eq_of_sum_pow_fin {B : ℕ} : ∀ {n : ℕ} {f g : Fin n → ℕ}, (∀ i, f i < B) → (∀ i, g i < B) →
    ∑ i, f i * B ^ (i : ℕ) = ∑ i, g i * B ^ (i : ℕ) → f = g
  | 0, f, g, _, _, _ => funext fun i => i.elim0
  | n + 1, f, g, hf, hg, h => by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ] at h
    have e : ∀ u : Fin (n + 1) → ℕ, ∑ i : Fin n, u i.succ * (B ^ (i : ℕ) * B) =
        B * ∑ i : Fin n, u i.succ * B ^ (i : ℕ) := fun u => by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    rw [e f, e g] at h
    have h0 : f 0 = g 0 := by
      have := congrArg (· % B) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf 0), Nat.mod_eq_of_lt (hg 0)]
        at this
      exact this
    have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (hf 0)
    have hrest : ∑ i : Fin n, f i.succ * B ^ (i : ℕ) = ∑ i : Fin n, g i.succ * B ^ (i : ℕ) := by
      rw [h0] at h
      have := Nat.add_left_cancel h
      exact Nat.eq_of_mul_eq_mul_left hB this
    have := eq_of_sum_pow_fin (f := fun i => f i.succ) (g := fun i => g i.succ)
      (fun i => hf _) (fun i => hg _) hrest
    funext i
    refine Fin.cases h0 (fun j => ?_) i
    exact congrFun this j

/-- **Base-`B` digits indexed by the darts**: two families of digits `< B` with the same value
`Σ f d B ^ (index of d)` are equal. -/
lemma eq_of_sum_pow {B : ℕ} {f g : D → ℕ} (hf : ∀ d, f d < B) (hg : ∀ d, g d < B)
    (h : ∑ d, f d * B ^ (Fintype.equivFin D d : ℕ) = ∑ d, g d * B ^ (Fintype.equivFin D d : ℕ)) :
    f = g := by
  have e : ∀ u : D → ℕ, ∑ d, u d * B ^ (Fintype.equivFin D d : ℕ) =
      ∑ i, u ((Fintype.equivFin D).symm i) * B ^ (i : ℕ) := fun u =>
    (Equiv.sum_comp (Fintype.equivFin D).symm _).symm.trans (by simp)
  rw [e f, e g] at h
  have := eq_of_sum_pow_fin (fun i => hf _) (fun i => hg _) h
  funext d
  have := congrFun this (Fintype.equivFin D d)
  simpa using this

/-- The sum of `φ` along a list, by the multiplicities of the darts. -/
lemma dsum_eq_count (φ : D → ℤ) (l : List D) : dsum φ l = ∑ d, (l.count d : ℤ) * φ d := by
  unfold dsum
  rw [Finset.sum_list_map_count]
  rw [← sum_subset (subset_univ l.toFinset) (fun d _ hd => by
    rw [List.mem_toFinset, ← List.count_eq_zero] at hd; simp [hd])]
  simp

/-- **The perturbation separates multisets of darts with multiplicities `< B`.** -/
lemma count_eq_of_dsum_eq {B : ℕ} {l l' : List D} (hl : ∀ d, l.count d < B)
    (hl' : ∀ d, l'.count d < B)
    (h : dsum (fun d => (B : ℤ) ^ (Fintype.equivFin D d : ℕ)) l =
      dsum (fun d => (B : ℤ) ^ (Fintype.equivFin D d : ℕ)) l') (d : D) :
    l.count d = l'.count d := by
  rw [dsum_eq_count, dsum_eq_count] at h
  have h' : ∑ d, l.count d * B ^ (Fintype.equivFin D d : ℕ) =
      ∑ d, l'.count d * B ^ (Fintype.equivFin D d : ℕ) := by exact_mod_cast h
  exact congrFun (eq_of_sum_pow (f := fun d => l.count d) (g := fun d => l'.count d) hl hl' h') d

end STFlow

end PlanarFlow
