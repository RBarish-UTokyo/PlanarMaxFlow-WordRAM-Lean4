module

public import PlanarFlow.BKMNW.Algorithm

/-!
# Transferring the output of the recursion between maps

The recursion of the article runs on the piece maps (`PlanarFlow/BKMNW/PieceMap.lean`), each with
its own darts and vertices: a child piece map has fewer darts than its parent, and one more hole
contracted. This file transfers the output `MSOut` of the recursion along an **embedding of maps**
(`Emb`): an injective map `e` of the darts of `M₁` into those of `M₂`, commuting with the
reversal, with a map `φ` of the vertices of `M₂` to those of `M₁` compatible with the tails (the
vertices of `M₂` merged in `M₁`).

* `Emb.ext`: a function on the darts of `M₁` extended by zero to the darts of `M₂`.
* `Emb.div_ext`: the net outflow at a vertex `w` of `M₂` of an extended function is the sum over
  the darts of `M₁` whose tail is `w`.
* `MSOut.transfer`: **the output of the recursion on `M₁`, extended by zero, is an output of the
  recursion on `M₂`** with the capacities extended by zero, if the vertices of `M₂` that are not
  terminals or holes are not merged by `φ`, and the terminals and holes of `M₂` touched by `M₁`
  are sent to those of `M₁`.
* `MSOut.widen`: adding to the piece darts with both ends in the holes, with nonnegative
  capacities and no flow, keeps the output of the recursion (the article leaves the contracted
  separators out of the pieces).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function CombMap

/-! ### Widening a piece by darts inside the holes -/

section Widen

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-- **Darts inside the holes do not matter**: adding to the piece darts with both ends in the
holes, with nonnegative capacities, keeps the output of the recursion. -/
theorem MSOut.widen {u f : D → ℤ} {P Q : Finset D} (hP : RevClosed M P) (hPQ : P ⊆ Q)
    {S T A : Finset V} (hin : ∀ d ∈ Q, d ∉ P → M.tail d ∈ A ∧ M.head d ∈ A) (hu : ∀ d, 0 ≤ u d)
    (h : MSOut M (capOn u P) S T A f) : MSOut M (capOn u Q) S T A f := by
  have hz : ∀ d, d ∉ P → f d = 0 := fun d hd => h.pseudo.eq_zero_of_not_mem hP hd
  have hps : IsPseudo M (capOn u Q) f := ⟨h.pseudo.antisymm, fun d => by
    by_cases hd : d ∈ P
    · have := h.pseudo.le_cap d; simp only [capOn, hd, hPQ hd, ite_true] at this ⊢; exact this
    · rw [hz d hd]; unfold capOn; split_ifs
      · exact hu d
      · exact le_rfl⟩
  -- a closed set containing all of `A` or none of `A` stays closed
  have hcl : ∀ Y : Finset V, Closed M (capOn u P) f Y → (A ⊆ Y ∨ Disjoint Y A) →
      Closed M (capOn u Q) f Y := by
    intro Y hY hA d h1 h2
    have e := hY d h1 h2
    by_cases hdP : d ∈ P
    · simp only [capOn, hdP, hPQ hdP, ite_true] at e ⊢; exact e
    · by_cases hdQ : d ∈ Q
      · exfalso
        obtain ⟨ht, hh⟩ := hin d hdQ hdP
        rcases hA with hA | hA
        · exact h2 (hA hh)
        · exact disjoint_left.1 hA h1 ht
      · simp only [capOn, hdP, hdQ, ite_false] at e ⊢; exact e
  obtain ⟨Y₁, hY₁1, hY₁2, hY₁3⟩ := h.st.union_right h.sa
  obtain ⟨Y₂, hY₂1, hY₂2, hY₂3⟩ := h.at'.union_left h.st
  have c1 := hcl Y₁ hY₁3 (Or.inr (disjoint_of_subset_right subset_union_right hY₁2))
  have c2 := hcl Y₂ hY₂3 (Or.inl (subset_union_left.trans hY₂1))
  exact ⟨hps, h.cons,
    ⟨Y₁, hY₁1, disjoint_of_subset_right subset_union_left hY₁2, c1⟩,
    ⟨Y₁, hY₁1, disjoint_of_subset_right subset_union_right hY₁2, c1⟩,
    ⟨Y₂, subset_union_left.trans hY₂1, hY₂2, c2⟩⟩

end Widen

/-! ### Embeddings of maps -/

variable {D₁ V₁ F₁ D₂ V₂ F₂ : Type*} [Fintype D₁] [DecidableEq D₁] [Fintype V₁] [DecidableEq V₁]
  [Fintype F₁] [DecidableEq F₁] [Fintype D₂] [DecidableEq D₂] [Fintype V₂] [DecidableEq V₂]
  [Fintype F₂] [DecidableEq F₂]

/-- **An embedding of maps**: the darts of `M₁` among the darts of `M₂`, with a map of the
vertices of `M₂` to those of `M₁` compatible with the tails. -/
structure Emb (M₁ : CombMap D₁ V₁ F₁) (M₂ : CombMap D₂ V₂ F₂) where
  /-- The darts. -/
  e : D₁ → D₂
  inj : Injective e
  rev : ∀ x, e (M₁.rev x) = M₂.rev (e x)
  /-- The vertices. -/
  φ : V₂ → V₁
  tail : ∀ x, φ (M₂.tail (e x)) = M₁.tail x

namespace Emb

variable {M₁ : CombMap D₁ V₁ F₁} {M₂ : CombMap D₂ V₂ F₂} (E : Emb M₁ M₂)

/-- A function on the darts of `M₁`, extended by zero. -/
noncomputable def ext (g : D₁ → ℤ) : D₂ → ℤ := Function.extend E.e g 0

lemma ext_apply (g : D₁ → ℤ) (x : D₁) : E.ext g (E.e x) = g x := E.inj.extend_apply g 0 x

lemma ext_of_not_mem (g : D₁ → ℤ) {d : D₂} (hd : ∀ x, E.e x ≠ d) : E.ext g d = 0 := by
  unfold ext; rw [Function.extend_apply' _ _ _ (fun ⟨x, hx⟩ => hd x hx)]; rfl

lemma head (x : D₁) : E.φ (M₂.head (E.e x)) = M₁.head x := by
  rw [CombMap.head, ← E.rev, E.tail]; rfl

/-- A vertex of `M₂` touched by a dart of `M₁`. -/
def Touched (w : V₂) : Prop := ∃ x, M₂.tail (E.e x) = w

lemma rev_not_mem {d : D₂} (hd : ∀ x, E.e x ≠ d) : ∀ x, E.e x ≠ M₂.rev d := fun x h =>
  hd (M₁.rev x) (by rw [E.rev, h, M₂.rev_rev])

lemma ext_antisymm {g : D₁ → ℤ} (hg : M₁.IsAntisymm g) : M₂.IsAntisymm (E.ext g) := by
  intro d
  by_cases h : ∃ x, E.e x = d
  · obtain ⟨x, rfl⟩ := h
    rw [← E.rev, ext_apply, ext_apply, hg x]
  · push Not at h
    rw [ext_of_not_mem _ _ h, ext_of_not_mem _ _ (E.rev_not_mem h), neg_zero]

lemma ext_pseudo {U g : D₁ → ℤ} (h : IsPseudo M₁ U g) : IsPseudo M₂ (E.ext U) (E.ext g) := by
  refine ⟨E.ext_antisymm h.antisymm, fun d => ?_⟩
  by_cases hd : ∃ x, E.e x = d
  · obtain ⟨x, rfl⟩ := hd; rw [ext_apply, ext_apply]; exact h.le_cap x
  · push Not at hd; rw [ext_of_not_mem _ _ hd, ext_of_not_mem _ _ hd]

/-- **The net outflow of an extended function** at a vertex of `M₂`: the sum over the darts of
`M₁` whose tail is that vertex. -/
lemma div_ext (g : D₁ → ℤ) (w : V₂) :
    M₂.div (E.ext g) w = ∑ x with M₂.tail (E.e x) = w, g x := by
  classical
  unfold CombMap.div
  have h1 : ∑ d with M₂.tail d = w, E.ext g d =
      ∑ d ∈ (univ.filter fun x => M₂.tail (E.e x) = w).image E.e, E.ext g d := by
    refine (sum_subset (fun d hd => ?_) (fun d hd hnd => ?_)).symm
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hd
      simpa using hx
    · refine ext_of_not_mem _ _ fun x hx => hnd (mem_image.2 ⟨x, ?_, hx⟩)
      simp only [mem_filter, mem_univ, true_and] at hd ⊢; rw [hx]; exact hd
  rw [h1, sum_image (fun x _ y _ h => E.inj h)]
  exact sum_congr rfl fun x _ => E.ext_apply g x

/-- The net outflow at an untouched vertex is zero. -/
lemma div_ext_untouched (g : D₁ → ℤ) {w : V₂} (hw : ¬ E.Touched w) : M₂.div (E.ext g) w = 0 := by
  rw [div_ext]
  exact sum_eq_zero fun x hx => absurd ⟨x, (mem_filter.1 hx).2⟩ hw

/-- **The net outflow at a vertex not merged with any other**. -/
lemma div_ext_eq (g : D₁ → ℤ) {w : V₂}
    (hfib : ∀ x, E.φ (M₂.tail (E.e x)) = E.φ w → M₂.tail (E.e x) = w) :
    M₂.div (E.ext g) w = M₁.div g (E.φ w) := by
  rw [div_ext, CombMap.div]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro rfl; exact (E.tail x).symm
  · intro h; exact hfib x (by rw [E.tail, h])

/-- **Closed sets transfer** along an embedding: the vertices of `M₂` sent into a closed set of
`M₁`, and the untouched vertices of `X`. -/
theorem noPath_transfer {U g : D₁ → ℤ} {X₁ Y₁ : Finset V₁} {X₂ Y₂ : Finset V₂}
    (h : NoPath M₁ U g X₁ Y₁) (hX : ∀ w ∈ X₂, E.Touched w → E.φ w ∈ X₁)
    (hY : ∀ w ∈ Y₂, E.Touched w → E.φ w ∈ Y₁) (hXY : Disjoint X₂ Y₂) :
    NoPath M₂ (E.ext U) (E.ext g) X₂ Y₂ := by
  classical
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ := h
  refine ⟨univ.filter fun w => if E.Touched w then E.φ w ∈ Z else w ∈ X₂, fun w hw => ?_,
    disjoint_left.2 fun w hw hwY => ?_, fun d hd1 hd2 => ?_⟩
  · simp only [mem_filter, mem_univ, true_and]
    split_ifs with ht
    · exact hZ1 (hX w hw ht)
    · exact hw
  · simp only [mem_filter, mem_univ, true_and] at hw
    split_ifs at hw with ht
    · exact disjoint_left.1 hZ2 hw (hY w hwY ht)
    · exact disjoint_left.1 hXY hw hwY
  · simp only [mem_filter, mem_univ, true_and] at hd1 hd2
    by_cases hd : ∃ x, E.e x = d
    · obtain ⟨x, rfl⟩ := hd
      have t1 : E.Touched (M₂.tail (E.e x)) := ⟨x, rfl⟩
      have t2 : E.Touched (M₂.head (E.e x)) := ⟨M₁.rev x, by rw [E.rev]; rfl⟩
      simp only [t1, ite_true, E.tail] at hd1
      simp only [t2, ite_true, E.head] at hd2
      rw [ext_apply, ext_apply]
      exact hZ3 x hd1 hd2
    · push Not at hd
      rw [ext_of_not_mem _ _ hd, ext_of_not_mem _ _ hd]

/-- **The output of the recursion transfers along an embedding of maps.** -/
theorem msOut_transfer {U g : D₁ → ℤ} {S₁ T₁ A₁ : Finset V₁} {S₂ T₂ A₂ : Finset V₂}
    (h : MSOut M₁ U S₁ T₁ A₁ g)
    (hcons : ∀ w, w ∉ S₂ → w ∉ T₂ → w ∉ A₂ → E.Touched w →
      E.φ w ∉ S₁ ∧ E.φ w ∉ T₁ ∧ E.φ w ∉ A₁ ∧
        ∀ x, E.φ (M₂.tail (E.e x)) = E.φ w → M₂.tail (E.e x) = w)
    (hS : ∀ w ∈ S₂, E.Touched w → E.φ w ∈ S₁) (hT : ∀ w ∈ T₂, E.Touched w → E.φ w ∈ T₁)
    (hA : ∀ w ∈ A₂, E.Touched w → E.φ w ∈ A₁) (hST : Disjoint S₂ T₂) (hSA : Disjoint S₂ A₂)
    (hAT : Disjoint A₂ T₂) : MSOut M₂ (E.ext U) S₂ T₂ A₂ (E.ext g) := by
  refine ⟨E.ext_pseudo h.pseudo, fun w h1 h2 h3 => ?_, E.noPath_transfer h.st hS hT hST,
    E.noPath_transfer h.sa hS hA hSA, E.noPath_transfer h.at' hA hT hAT⟩
  by_cases ht : E.Touched w
  · obtain ⟨c1, c2, c3, c4⟩ := hcons w h1 h2 h3 ht
    rw [E.div_ext_eq g c4]
    exact h.cons _ c1 c2 c3
  · exact E.div_ext_untouched g ht

end Emb

end BKMNW

end PlanarFlow
