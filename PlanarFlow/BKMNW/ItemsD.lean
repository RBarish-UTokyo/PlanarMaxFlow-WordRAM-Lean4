module

public import PlanarFlow.BKMNW.FirstProg

/-!
# Items as label arrays; `pruneI` as a fill of labels

The items of a certificate (pairwise disjoint sets of darts) are held on the machine as a label
array: `lab i ≠ 0` is the item of the dart `e i`, `0` no item. The items represented are the
label classes `labItems e n lab` (empty items are not represented: `I.erase ∅`).

* `clsL e n lab l` (the darts of label `l`), `labItems e n lab`, `mem_labItems`,
  `ItemRep e n I lab := I.erase ∅ = labItems e n lab`;
* `fillL S v lab` (the labels `v` on the indices of `S`), `clsL_fill_ne`, `clsL_fill_v`,
  **`labItems_fill_fresh`** (a fresh label: a new item `S.image e`), **`labItems_fill_old`**
  (the label of `e i₀`: its item grows by `S.image e`);
* **`pruneI_rep`**: `pruneI Hs N K (e i₀) ρ I` is represented by the fill of the indices of
  `N \ K` with `v = if b ∨ lab i₀ = 0 then L else lab i₀` (`L` fresh, `b` the test
  `tail (e i₀) ∈ newHole Hs ρ.mverts`), for items inside `K`, `N \ K ≠ ∅`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset

variable {D : Type*} [DecidableEq D]

/-- The darts of label `l`. -/
def clsL (e : ℕ → D) (n : ℕ) (lab : ℕ → ℕ) (l : ℕ) : Finset D :=
  ((range n).filter fun j => lab j = l).image e

/-- **The items of a label array**: the classes of the nonzero labels. -/
def labItems (e : ℕ → D) (n : ℕ) (lab : ℕ → ℕ) : Finset (Finset D) :=
  ((range n).filter fun i => lab i ≠ 0).image fun i => clsL e n lab (lab i)

/-- **The label array `lab` represents the items `I`** (up to an empty item). -/
def ItemRep (e : ℕ → D) (n : ℕ) (I : Finset (Finset D)) (lab : ℕ → ℕ) : Prop :=
  I.erase ∅ = labItems e n lab

variable {e : ℕ → D} {n : ℕ}

lemma mem_clsL {lab : ℕ → ℕ} {l : ℕ} {d : D} : d ∈ clsL e n lab l ↔ ∃ j < n, lab j = l ∧ e j = d := by
  simp [clsL, and_assoc]

lemma mem_labItems {lab : ℕ → ℕ} {X : Finset D} :
    X ∈ labItems e n lab ↔ ∃ i < n, lab i ≠ 0 ∧ X = clsL e n lab (lab i) := by
  simp only [labItems, mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨i, ⟨hi, hl⟩, rfl⟩; exact ⟨i, hi, hl, rfl⟩
  · rintro ⟨i, hi, hl, rfl⟩; exact ⟨i, ⟨hi, hl⟩, rfl⟩

lemma self_mem_clsL {lab : ℕ → ℕ} {i : ℕ} (hi : i < n) : e i ∈ clsL e n lab (lab i) :=
  mem_clsL.2 ⟨i, hi, rfl, rfl⟩

/-- The labels `v` on the indices of `S`. -/
def fillL (S : Finset ℕ) (v : ℕ) (lab : ℕ → ℕ) (i : ℕ) : ℕ := if i ∈ S then v else lab i

variable {S : Finset ℕ} {v : ℕ} {lab : ℕ → ℕ}

lemma clsL_fill_ne (h0 : ∀ i ∈ S, lab i = 0) {l : ℕ} (hl : l ≠ 0) (hv : l ≠ v) :
    clsL e n (fillL S v lab) l = clsL e n lab l := by
  ext d
  simp only [mem_clsL, fillL]
  constructor
  · rintro ⟨j, hj, h, rfl⟩
    refine ⟨j, hj, ?_, rfl⟩
    split_ifs at h with hS
    · exact absurd h.symm hv
    · exact h
  · rintro ⟨j, hj, h, rfl⟩
    refine ⟨j, hj, ?_, rfl⟩
    split_ifs with hS
    · exact absurd (h0 j hS ▸ h).symm hl
    · exact h

lemma clsL_fill_v (hS : S ⊆ range n) :
    clsL e n (fillL S v lab) v = clsL e n lab v ∪ S.image e := by
  ext d
  simp only [mem_clsL, fillL, mem_union, mem_image]
  constructor
  · rintro ⟨j, hj, h, rfl⟩
    by_cases hjS : j ∈ S
    · exact Or.inr ⟨j, hjS, rfl⟩
    · rw [iteF hjS] at h; exact Or.inl ⟨j, hj, h, rfl⟩
  · rintro (⟨j, hj, h, rfl⟩ | ⟨j, hjS, rfl⟩)
    · refine ⟨j, hj, ?_, rfl⟩
      split_ifs <;> first | rfl | exact h
    · exact ⟨j, mem_range.1 (hS hjS), by rw [iteT hjS], rfl⟩

/-- **A fill with a fresh label adds the item `S.image e`.** -/
theorem labItems_fill_fresh (hS : S ⊆ range n) (hSne : S.Nonempty) (h0 : ∀ i ∈ S, lab i = 0)
    (hv : v ≠ 0) (hfresh : ∀ i < n, lab i ≠ v) :
    labItems e n (fillL S v lab) = insert (S.image e) (labItems e n lab) := by
  have hcv : clsL e n lab v = ∅ := by
    ext d; simp only [mem_clsL, Finset.notMem_empty, iff_false]
    rintro ⟨j, hj, h, -⟩; exact hfresh j hj h
  ext X
  rw [mem_insert, mem_labItems, mem_labItems]
  constructor
  · rintro ⟨i, hi, hl, rfl⟩
    by_cases hiS : i ∈ S
    · left
      simp only [fillL, iteT hiS]
      rw [clsL_fill_v hS, hcv, empty_union]
    · right
      have e1 : fillL S v lab i = lab i := iteF hiS
      rw [e1] at hl ⊢
      exact ⟨i, hi, hl, clsL_fill_ne h0 hl (hfresh i hi)⟩
  · rintro (rfl | ⟨i, hi, hl, rfl⟩)
    · obtain ⟨i, hiS⟩ := hSne
      refine ⟨i, mem_range.1 (hS hiS), by simp only [fillL, iteT hiS]; exact hv, ?_⟩
      simp only [fillL, iteT hiS]
      rw [clsL_fill_v hS, hcv, empty_union]
    · have hiS : i ∉ S := fun h => hl (h0 i h)
      have e1 : fillL S v lab i = lab i := iteF hiS
      exact ⟨i, hi, by rw [e1]; exact hl, by rw [e1, clsL_fill_ne h0 hl (hfresh i hi)]⟩

/-- **A fill with the label of `e i₀` adds `S.image e` to the item of `e i₀`.** -/
theorem labItems_fill_old (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) (hS : S ⊆ range n)
    (h0 : ∀ i ∈ S, lab i = 0) {i₀ : ℕ} (hi₀ : i₀ < n) (hl₀ : lab i₀ ≠ 0) :
    labItems e n (fillL S (lab i₀) lab) =
      insert (clsL e n lab (lab i₀) ∪ S.image e) ((labItems e n lab).filter (e i₀ ∉ ·)) := by
  have hi₀S : i₀ ∉ S := fun h => hl₀ (h0 i₀ h)
  have hmem : ∀ i < n, (e i₀ ∈ clsL e n lab (lab i) ↔ lab i = lab i₀) := by
    intro i hi
    constructor
    · intro h
      obtain ⟨j, hj, hlj, hej⟩ := mem_clsL.1 h
      rw [← hlj, hinj j hj i₀ hi₀ hej]
    · intro h; rw [h]; exact self_mem_clsL hi₀
  ext X
  rw [mem_insert, mem_labItems, mem_filter, mem_labItems]
  constructor
  · rintro ⟨i, hi, hl, rfl⟩
    by_cases hiS : i ∈ S
    · left
      simp only [fillL, iteT hiS]
      exact clsL_fill_v hS
    · have e1 : fillL S (lab i₀) lab i = lab i := iteF hiS
      rw [e1] at hl ⊢
      by_cases hv : lab i = lab i₀
      · left; rw [hv]; exact clsL_fill_v hS
      · right
        rw [clsL_fill_ne h0 hl hv]
        exact ⟨⟨i, hi, hl, rfl⟩, fun h => hv ((hmem i hi).1 h)⟩
  · rintro (rfl | ⟨⟨i, hi, hl, rfl⟩, hn⟩)
    · have e1 : fillL S (lab i₀) lab i₀ = lab i₀ := iteF hi₀S
      exact ⟨i₀, hi₀, by rw [e1]; exact hl₀, by rw [e1, clsL_fill_v hS]⟩
    · have hv : lab i ≠ lab i₀ := fun h => hn ((hmem i hi).2 h)
      have hiS : i ∉ S := fun h => hl (h0 i h)
      have e1 : fillL S (lab i₀) lab i = lab i := iteF hiS
      exact ⟨i, hi, by rw [e1]; exact hl, by rw [e1, clsL_fill_ne h0 hl hv]⟩

/-! ### `pruneI` on labels -/

section Prune

variable {V F : Type*} [Fintype D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  {M : CombMap D V F}

/-- **`pruneI` as a fill of labels.** Items `I` represented by `lab`, pairwise disjoint, inside
`K`; `S` the indices of `N \ K` (nonempty); `e i₀` the anchor; `L ≠ 0` a fresh label and
`b` the test `tail (e i₀) ∈ newHole Hs ρ.mverts`. Then `pruneI Hs N K (e i₀) ρ I` is represented by
the labels `v = if b ∨ lab i₀ = 0 then L else lab i₀` on `S`. -/
theorem pruneI_rep (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    {Hs : List (Finset V)} {N K : Finset D} {ρ : HPath M} {I : Finset (Finset D)}
    (hrep : ItemRep e n I lab) (hdisj : ∀ X ∈ I, ∀ Y ∈ I, X ≠ Y → Disjoint X Y)
    (hIK : ∀ X ∈ I, X ⊆ K) (hS : S ⊆ range n) (hSN : S.image e = N \ K) (hSne : S.Nonempty)
    {i₀ : ℕ} (hi₀ : i₀ < n) {L : ℕ} (hL : L ≠ 0) (hfresh : ∀ i < n, lab i ≠ L)
    (b : Prop) [Decidable b] (hb : b ↔ M.tail (e i₀) ∈ newHole Hs ρ.mverts) :
    ItemRep e n (pruneI Hs N K (e i₀) ρ I)
      (fillL S (if b ∨ lab i₀ = 0 then L else lab i₀) lab) := by
  classical
  -- the labels on `S` are `0`
  have h0 : ∀ i ∈ S, lab i = 0 := by
    intro i hiS
    by_contra hl
    have hi := mem_range.1 (hS hiS)
    have hX : clsL e n lab (lab i) ∈ labItems e n lab := mem_labItems.2 ⟨i, hi, hl, rfl⟩
    rw [← hrep] at hX
    have hK := hIK _ (mem_of_mem_erase hX) (self_mem_clsL hi)
    have hNK : e i ∈ N \ K := hSN ▸ mem_image_of_mem e hiS
    exact (mem_sdiff.1 hNK).2 hK
  have hNK0 : N \ K ≠ ∅ := by
    rw [← hSN]; exact (hSne.image e).ne_empty
  -- an item containing the anchor is the class of its label
  have hanc : ∀ X ∈ I, e i₀ ∈ X → lab i₀ ≠ 0 ∧ X = clsL e n lab (lab i₀) := by
    intro X hX ha
    have hX' : X ∈ labItems e n lab := by
      rw [← hrep]; exact mem_erase.2 ⟨ne_empty_of_mem ha, hX⟩
    obtain ⟨i, hi, hl, rfl⟩ := mem_labItems.1 hX'
    obtain ⟨j, hj, hlj, hej⟩ := mem_clsL.1 ha
    rw [hinj j hj i₀ hi₀ hej] at hlj
    rw [hlj]; exact ⟨hlj ▸ hl, rfl⟩
  unfold ItemRep pruneI
  by_cases hA : b ∨ lab i₀ = 0
  · rw [iteT hA, labItems_fill_fresh hS hSne h0 hL hfresh, hSN, ← hrep]
    have hins : (insert (N \ K) I).erase ∅ = insert (N \ K) (I.erase ∅) :=
      erase_insert_of_ne hNK0
    by_cases hbt : M.tail (e i₀) ∈ newHole Hs ρ.mverts
    · rw [iteT hbt, hins]
    · rw [iteF hbt]
      have hl0 : lab i₀ = 0 := by
        rcases hA with h | h
        · exact absurd (hb.1 h) hbt
        · exact h
      have hnone : I.filter (e i₀ ∈ ·) = ∅ := by
        ext X; simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hX ha; exact (hanc X hX ha).1 hl0
      have hall : I.filter (e i₀ ∉ ·) = I := by
        ext X; simp only [mem_filter, and_iff_left_iff_imp]
        intro hX ha; exact (hanc X hX ha).1 hl0
      rw [hnone, hall, biUnion_empty, empty_union, hins]
  · rw [iteF hA]
    push Not at hA
    obtain ⟨hnb, hl0⟩ := hA
    rw [iteF (fun h => hnb (hb.2 h)), labItems_fill_old hinj hS h0 hi₀ hl0, hSN, ← hrep]
    have hX₀ : clsL e n lab (lab i₀) ∈ I := by
      have : clsL e n lab (lab i₀) ∈ labItems e n lab := mem_labItems.2 ⟨i₀, hi₀, hl0, rfl⟩
      rw [← hrep] at this; exact mem_of_mem_erase this
    rw [biUnion_filter_mem hdisj hX₀ (self_mem_clsL hi₀)]
    have hne : clsL e n lab (lab i₀) ∪ N \ K ≠ ∅ := by
      intro h; exact hNK0 (subset_empty.1 (h ▸ subset_union_right))
    rw [erase_insert_of_ne hne]
    congr 1
    ext X
    simp only [mem_erase, mem_filter]
    tauto

end Prune

end BKMNW

end PlanarFlow
