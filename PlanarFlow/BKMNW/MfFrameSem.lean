module

public import PlanarFlow.BKMNW.MfFrameSplit
public import PlanarFlow.BKMNW.MfFrameFlags

/-!
# The machine's values of the child data are the child's data

The value functions of `MfFrameFlags.lean` (`nhF`, `flL`, `flR`, `kcF`, `hcF`, `hfF`) on the
flags of the parent's frame and of the separator give the data of the child frames:

* `hpath_ends`, `hpath_rev`: the ends of a dart of the separator are on it,
  its darts are closed under reversal.
* **`pdarts_child_sub`**: the darts of a child piece map are darts of the parent piece map off the
  separator; `pdarts_child_rev` (closed under reversal).
* `nhF_eq` (the tail in the new hole), `flL_eq`, `flR_eq` (the child flags), `kcF_eq` (the
  child's rank, through `lrk_child`), `hcF_eq` (the child's hole label, through `hlab_child`),
  `hfF_eq`, `cnt_hfF` (the count of the kept holes is `hcnt`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

lemma hpath_ends (ρ : HPath M) {e : D} (he : e ∈ ρ.darts) :
    M.tail e ∈ ρ.mverts ∧ M.tail (M.rev e) ∈ ρ.mverts := by
  obtain ⟨j, hj, rfl | rfl⟩ := ρ.mem_darts.1 he
  · refine ⟨by rw [ρ.tail_d j hj]; exact ρ.p_mem_mverts hj.le, ?_⟩
    exact mem_union_right _ (mem_image.2 ⟨j, mem_range.2 hj, rfl⟩)
  · rw [M.rev_rev]
    refine ⟨mem_union_right _ (mem_image.2 ⟨j, mem_range.2 hj, rfl⟩), ?_⟩
    rw [ρ.tail_d j hj]; exact ρ.p_mem_mverts hj.le

lemma hpath_rev (ρ : HPath M) : ∀ e ∈ ρ.darts, M.rev e ∈ ρ.darts := fun e he => by
  obtain ⟨j, hj, rfl | rfl⟩ := ρ.mem_darts.1 he
  · exact ρ.mem_darts.2 ⟨j, hj, Or.inr rfl⟩
  · rw [M.rev_rev]; exact ρ.mem_darts.2 ⟨j, hj, Or.inl rfl⟩

/-- **The darts of a child piece map are darts of the parent piece map off the separator.** -/
lemma pdarts_child_sub {P Pc : Finset D} {Hs : List (Finset V)} (ρ : HPath M) (hPc : Pc ⊆ P) :
    pdarts M Pc (childHoles Hs ρ.mverts) ⊆ pdarts M P Hs \ ρ.darts.toFinset := by
  intro y hy
  have hyB := pdarts_childHoles_subset (Hs := Hs) (C := ρ.mverts) hPc hy
  refine mem_sdiff.2 ⟨hyB, fun hL => ?_⟩
  have hL' : y ∈ ρ.darts := List.mem_toFinset.1 hL
  obtain ⟨h1, h2⟩ := hpath_ends ρ hL'
  exact ((mem_pdarts_child hyB).1 hy).2 ⟨subset_newHole h1, subset_newHole h2⟩

/-- The darts of a child piece map are closed under reversal. -/
lemma pdarts_child_rev {Pc : Finset D} (hPc : RevClosed M Pc) (Hs' : List (Finset V)) :
    ∀ y ∈ pdarts M Pc Hs', M.rev y ∈ pdarts M Pc Hs' := fun y hy =>
  stable_pdarts hPc Hs' y hy

/-- The flag of a proposition. -/
def bf (p : Prop) [Decidable p] : ℕ := if p then 1 else 0

lemma bf_pos {p : Prop} [Decidable p] : 0 < bf p ↔ p := by
  unfold bf; split_ifs with h <;> simp [h]

/-- **The tail in the new hole.** -/
lemma nhF_eq {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {C : Finset V} (v : V) :
    nhF (bf (v ∈ C)) (hlab Hs v) (bf (¬ Disjoint (Hs.getD (hlab Hs v - 1) ∅) C)) =
      bf (v ∈ newHole Hs C) := by
  have key := mem_newHole_iff' hd (C := C) (v := v)
  unfold nhF bf
  by_cases h1 : v ∈ C
  · have : v ∈ newHole Hs C := key.2 (Or.inl h1)
    rw [iteT h1, iteT this, iteT (by omega)]
  · rw [iteF h1, iteF (by omega)]
    by_cases h2 : 0 < hlab Hs v
    · rw [iteT h2]
      by_cases h3 : Disjoint (Hs.getD (hlab Hs v - 1) ∅) C
      · have : v ∉ newHole Hs C := fun h => by
          rcases key.1 h with h | ⟨_, h'⟩
          · exact h1 h
          · exact h' h3
        rw [iteF (not_not.2 h3), iteF this]
      · have : v ∈ newHole Hs C := key.2 (Or.inr ⟨h2, h3⟩)
        rw [iteT h3, iteT this]
    · have : v ∉ newHole Hs C := fun h => by
        rcases key.1 h with h | ⟨h', _⟩
        · exact h1 h
        · exact h2 h'
      rw [iteF h2, iteF this]

/-- **The flag of a dart of the left child.** -/
lemma flL_eq (a b b' : Prop) [Decidable a] [Decidable b] [Decidable b'] :
    flL (bf a) (bf b) (bf b') = bf (a ∧ ¬ (b ∧ b')) := by
  unfold flL inF bf
  by_cases ha : a <;> by_cases hb : b <;> by_cases hb' : b' <;> simp [ha, hb, hb']

/-- **The flag of a dart of the right child.** -/
lemma flR_eq (a b b' : Prop) [Decidable a] [Decidable b] [Decidable b'] :
    flR (bf a) (bf b) (bf b') = bf (¬ a ∧ ¬ (b ∧ b')) := by
  unfold flR inF bf
  by_cases ha : a <;> by_cases hb : b <;> by_cases hb' : b' <;> simp [ha, hb, hb']

/-- **The child's rank.** -/
lemma kcF_eq {S T : Finset V} {Hs : List (Finset V)} {C : Finset V} (hSC : Disjoint S C)
    (hTC : Disjoint T C) (hS : Disjoint S (hunion Hs)) (v : V) :
    kcF (bf (v ∈ newHole Hs C)) (lrk S T (hunion Hs) v) = lrk S T (hunion (childHoles Hs C)) v := by
  rw [lrk_child hSC hTC hS]
  unfold kcF bf
  by_cases h : v ∈ newHole Hs C <;> simp [h]

lemma hfF_eq (p : Prop) [Decidable p] : hfF (bf (¬ p)) = bf p := by
  unfold hfF bf; by_cases h : p <;> simp [h]

/-- The count of the kept holes. -/
lemma cnt_hfF (Hs : List (Finset V)) (C : Finset V) {j : ℕ} (hj : j ≤ Hs.length) :
    cnt (fun i => hfF (bf (¬ Disjoint (Hs.getD i ∅) C))) j = hcnt Hs C j := by
  rw [← cnt_hcnt Hs C j hj]
  unfold cnt; congr 1
  apply filter_congr; intro i _
  show 0 < hfF (bf ¬Disjoint (Hs.getD i ∅) C) ↔ _
  rw [hfF_eq]; rfl

lemma hcnt_length (Hs : List (Finset V)) (C : Finset V) :
    hcnt Hs C Hs.length = (Hs.filter fun H => decide (Disjoint H C)).length := by
  simp [hcnt]

/-- **The child's hole label.** -/
lemma hcF_eq {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {C : Finset V} (v : V)
    {hci : ℕ} (hhci : v ∉ newHole Hs C → 0 < hlab Hs v → hci = hcnt Hs C (hlab Hs v - 1)) :
    hcF (bf (v ∈ newHole Hs C)) (hlab Hs v) hci (hcnt Hs C Hs.length + 1) =
      hlab (childHoles Hs C) v := by
  rw [hlab_child hd, hcnt_length]
  unfold hcF bf
  by_cases h : v ∈ newHole Hs C
  · simp [h]
  · by_cases h2 : 0 < hlab Hs v
    · simp [h, h2, hhci h h2]; omega
    · have : hlab Hs v = 0 := by omega
      simp [h, this]

end MfDrv

end BKMNW

end PlanarFlow
