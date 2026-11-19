module

public import PlanarFlow.Spec
public import WordRAM
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Maximum bipartite matching: the input and the mathematics

The input is `[n, m, col 0, …, col (n-1), off 0, …, off n, dst 0, …, dst (m-1)]`: a bipartite
graph on the vertices `0 … n-1`, coloured white (`col v = 1`) and black (`col v = 0`), with the
arcs from each white vertex `u` listed as `dst j` for `off u ≤ j < off (u + 1)` (black vertices
have no arcs; arcs go to black vertices).

A *matching* (`PlanarFlow.BM.IsMatching`) is a set of pairs `(w, b)` along arcs, no two sharing a
vertex. The program keeps a matching as an array of mates (`μ v = u + 1` if `v` is matched to
`u`, `0` if `v` is free), valid when symmetric and along arcs (`PlanarFlow.BM.Valid`); its size
is the number of matched white vertices.

* `PlanarFlow.BM.card_le_size` (**König's certificate**): if a set `R` of vertices contains every
  free white vertex, contains the head of every arc from a white vertex of `R`, and every black
  vertex of `R` is matched to a vertex of `R`, then no matching is larger than `μ`. (The white
  vertices outside `R` and the black vertices in `R` form a vertex cover of the size of `μ`.)
  This is what an alternating search that finds no free black vertex leaves behind.
* `PlanarFlow.BM.toM`: the matching of a valid array of mates, of the same size.
* `PlanarFlow.BM.flip_step`, `PlanarFlow.BM.flip_last`: one step of the augmentation along an
  alternating path, and the last.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BM

open Finset

/-- A valid array of mates. -/
def Valid (d : List ℕ) (μ : ℕ → ℕ) : Prop :=
  ∀ x < nn d, μ x ≠ 0 → μ x - 1 < nn d ∧ μ (μ x - 1) = x + 1 ∧
    (col d x = 1 → Arc d x (μ x - 1)) ∧ (col d x = 0 → Arc d (μ x - 1) x)

/-- The size of an array of mates: the number of matched white vertices. -/
def size (d : List ℕ) (μ : ℕ → ℕ) : ℕ := ((range (nn d)).filter fun w => col d w = 1 ∧ μ w ≠ 0).card

/-- The matching of an array of mates. -/
def toM (d : List ℕ) (μ : ℕ → ℕ) : Finset (ℕ × ℕ) :=
  ((range (nn d)).filter fun w => col d w = 1 ∧ μ w ≠ 0).image fun w => (w, μ w - 1)

variable {d : List ℕ}

lemma toM_isMatching (hw : Wf d) {μ : ℕ → ℕ} (hμ : Valid d μ) : IsMatching d (toM d μ) := by
  refine ⟨fun p hp => ?_, fun p hp q hq h => ?_, fun p hp q hq h => ?_⟩
  · obtain ⟨w, hw', rfl⟩ := mem_image.1 hp
    simp only [mem_filter, mem_range] at hw'
    exact ⟨(hμ w hw'.1 hw'.2.2).2.2.1 hw'.2.1, hw'.2.1⟩
  · obtain ⟨w, -, rfl⟩ := mem_image.1 hp
    obtain ⟨w', -, rfl⟩ := mem_image.1 hq
    simp only at h; subst h; rfl
  · obtain ⟨w, hw1, rfl⟩ := mem_image.1 hp
    obtain ⟨w', hw2, rfl⟩ := mem_image.1 hq
    simp only [mem_filter, mem_range] at hw1 hw2
    simp only at h
    have e1 := (hμ w hw1.1 hw1.2.2).2.1
    have e2 := (hμ w' hw2.1 hw2.2.2).2.1
    rw [h, e2] at e1
    have : w = w' := by omega
    subst this; rfl

lemma card_toM {μ : ℕ → ℕ} : (toM d μ).card = size d μ :=
  card_image_of_injOn fun a _ b _ h => by simpa using congrArg Prod.fst h

/-- **König's certificate of maximality.** -/
theorem card_le_size (hw : Wf d) {μ : ℕ → ℕ} (hμ : Valid d μ) (R : ℕ → Prop) [DecidablePred R]
    (hfree : ∀ w < nn d, col d w = 1 → μ w = 0 → R w)
    (hclosed : ∀ w b, Arc d w b → R w → R b)
    (hblack : ∀ b < nn d, col d b = 0 → R b → μ b ≠ 0 ∧ R (μ b - 1))
    {M : Finset (ℕ × ℕ)} (hM : IsMatching d M) : M.card ≤ size d μ := by
  classical
  -- the vertex cover
  let C : Finset ℕ := (range (nn d)).filter fun v => (col d v = 1 ∧ ¬ R v) ∨ (col d v = 0 ∧ R v)
  have h1 : M.card ≤ C.card := by
    refine card_le_card_of_injOn (fun p => if R p.1 then p.2 else p.1) (fun p hp => ?_)
      (fun p hp q hq h => ?_)
    · obtain ⟨harc, hcol⟩ := hM.1 p hp
      have hb := hw.arc_lt _ _ harc
      have hc := hw.arc_col _ _ harc
      simp only [C, coe_filter, mem_range, Set.mem_ofPred_eq]
      by_cases hR : R p.1
      · simp only [hR, ite_true]; exact ⟨hb, Or.inr ⟨hc.2, hclosed _ _ harc hR⟩⟩
      · simp only [hR, ite_false]; exact ⟨harc.1, Or.inl ⟨hcol, not_false⟩⟩
    · have hp' := hM.1 p hp
      have hq' := hM.1 q hq
      have hcp := hw.arc_col _ _ hp'.1
      have hcq := hw.arc_col _ _ hq'.1
      simp only at h
      by_cases hRp : R p.1 <;> by_cases hRq : R q.1 <;> simp only [hRp, hRq, ite_true, ite_false] at h
      · exact hM.2.2 p hp q hq h
      · rw [h] at hcp; omega
      · rw [← h] at hcq; omega
      · exact hM.2.1 p hp q hq h
  have h2 : C.card ≤ size d μ := by
    refine card_le_card_of_injOn (fun v => if col d v = 1 then v else μ v - 1) (fun v hv => ?_)
      (fun v hv v' hv' h => ?_)
    · simp only [C, coe_filter, mem_range, Set.mem_ofPred_eq] at hv
      simp only [size, coe_filter, mem_range, Set.mem_ofPred_eq]
      rcases hv with ⟨hvn, ⟨hc, hR⟩ | ⟨hc, hR⟩⟩
      · simp only [hc, ite_true, true_and]
        exact ⟨hvn, fun h0 => hR (hfree v hvn hc h0)⟩
      · simp only [hc, show (0 : ℕ) ≠ 1 by omega, ite_false]
        obtain ⟨hm, -⟩ := hblack v hvn hc hR
        obtain ⟨hlt, hback, -, harc⟩ := hμ v hvn hm
        exact ⟨hlt, (hw.arc_col _ _ (harc hc)).1, by rw [hback]; omega⟩
    · simp only [C, coe_filter, mem_range, Set.mem_ofPred_eq] at hv hv'
      simp only at h
      rcases hv with ⟨hvn, ⟨hc, hR⟩ | ⟨hc, hR⟩⟩ <;>
        rcases hv' with ⟨hvn', ⟨hc', hR'⟩ | ⟨hc', hR'⟩⟩ <;>
        simp only [hc, hc', show (0 : ℕ) ≠ 1 by omega, ite_true, ite_false] at h
      · exact h
      · exfalso
        obtain ⟨-, hRm⟩ := hblack v' hvn' hc' hR'
        rw [← h] at hRm; exact hR hRm
      · exfalso
        obtain ⟨-, hRm⟩ := hblack v hvn hc hR
        rw [h] at hRm; exact hR' hRm
      · obtain ⟨hm, -⟩ := hblack v hvn hc hR
        obtain ⟨hm', -⟩ := hblack v' hvn' hc' hR'
        have e1 := (hμ v hvn hm).2.1
        have e2 := (hμ v' hvn' hm').2.1
        rw [h, e2] at e1; omega
  exact h1.trans h2

/-! ### Augmentation along an alternating path

During the augmentation, the array of mates is a matching except at the current black vertex
`b`, whose entry is stale: no other vertex points to `b`. -/

/-- The array is consistent except at `b`. -/
def ValidExc (d : List ℕ) (μ : ℕ → ℕ) (b : ℕ) : Prop :=
  ∀ x < nn d, x ≠ b → μ x ≠ 0 → μ x - 1 < nn d ∧ μ x - 1 ≠ b ∧ μ (μ x - 1) = x + 1 ∧
    (col d x = 1 → Arc d x (μ x - 1)) ∧ (col d x = 0 → Arc d (μ x - 1) x)

lemma validExc_of_valid {μ : ℕ → ℕ} (hμ : Valid d μ) {b : ℕ} (hb : b < nn d) (hfree : μ b = 0) :
    ValidExc d μ b := by
  intro x hx hxb hm
  obtain ⟨h1, h2, h3, h4⟩ := hμ x hx hm
  refine ⟨h1, fun e => ?_, h2, h3, h4⟩
  rw [e, hfree] at h2; omega

/-- One step: `w` (with `Arc w b`) is matched to `b`; its old mate `b' = μ w - 1` (a black vertex,
`μ b' = w + 1`) becomes the current vertex. -/
lemma flip_step (hw : Wf d) {μ : ℕ → ℕ} {b w : ℕ} (hE : ValidExc d μ b) (hb : b < nn d)
    (harc : Arc d w b) (hwb : w ≠ b) (hm : μ w ≠ 0) (hb' : μ w - 1 ≠ b) :
    ValidExc d (Function.update (Function.update μ w (b + 1)) b (w + 1)) (μ w - 1) := by
  have hwn := harc.1
  obtain ⟨hb'n, -, hback, harcw, -⟩ := hE w hwn hwb hm
  have hcw := (hw.arc_col _ _ harc).1
  have hcb' : col d (μ w - 1) = 0 := (hw.arc_col _ _ (harcw hcw)).2
  have hwb' : w ≠ μ w - 1 := fun e => by rw [← e] at hcb'; omega
  intro x hx hxb' hm'
  by_cases hxb : x = b
  · rw [hxb] at hm' ⊢
    simp only [Function.update_self, Nat.add_sub_cancel]
    refine ⟨hwn, hwb', by simp [Function.update_apply, hwb], fun h => ?_, fun _ => harc⟩
    have := (hw.arc_col _ _ harc).2; omega
  · by_cases hxw : x = w
    · rw [hxw] at hm' ⊢
      simp only [Function.update_of_ne hwb, Function.update_self, Nat.add_sub_cancel]
      refine ⟨hb, fun e => hb' e.symm, by simp, fun _ => harc, fun h => by omega⟩
    · simp only [Function.update_of_ne hxb, Function.update_of_ne hxw] at hm' ⊢
      obtain ⟨h1, h2, h3, h4, h5⟩ := hE x hx hxb hm'
      have hy1 : μ x - 1 ≠ w := fun e => by
        rw [e] at h3; exact hxb' (by omega)
      refine ⟨h1, fun e => ?_, ?_, h4, h5⟩
      · rw [e, hback] at h3; omega
      · rw [Function.update_of_ne h2, Function.update_of_ne hy1]; exact h3

/-- The last step: `w` was free; the array is a valid matching again. -/
lemma flip_last (hw : Wf d) {μ : ℕ → ℕ} {b w : ℕ} (hE : ValidExc d μ b) (hb : b < nn d)
    (harc : Arc d w b) (hwb : w ≠ b) (hm : μ w = 0) :
    Valid d (Function.update (Function.update μ w (b + 1)) b (w + 1)) := by
  have hwn := harc.1
  have hc := hw.arc_col _ _ harc
  intro x hx hm'
  by_cases hxb : x = b
  · subst hxb
    simp only [Function.update_self, Nat.add_sub_cancel]
    exact ⟨hwn, by simp [Function.update_apply, hwb], fun h => by omega, fun _ => harc⟩
  · by_cases hxw : x = w
    · subst hxw
      simp only [Function.update_of_ne hxb, Function.update_self, Nat.add_sub_cancel]
      exact ⟨hb, by simp, fun _ => harc, fun h => by omega⟩
    · simp only [Function.update_of_ne hxb, Function.update_of_ne hxw] at hm' ⊢
      obtain ⟨h1, h2, h3, h4, h5⟩ := hE x hx hxb hm'
      have hy1 : μ x - 1 ≠ w := fun e => by rw [e, hm] at h3; omega
      refine ⟨h1, ?_, h4, h5⟩
      rw [Function.update_of_ne h2, Function.update_of_ne hy1]; exact h3

/-- The size does not change in a step, and grows by one in the last step. -/
lemma size_flip {μ : ℕ → ℕ} {b w : ℕ} (hwn : w < nn d) (hcw : col d w = 1) (hcb : col d b = 0) :
    size d (Function.update (Function.update μ w (b + 1)) b (w + 1)) =
      size d μ + (if μ w = 0 then 1 else 0) := by
  unfold size
  have hwb : w ≠ b := fun e => by rw [e] at hcw; omega
  by_cases h0 : μ w = 0
  · simp only [h0, ite_true]
    rw [← card_insert_of_notMem (s := (range (nn d)).filter fun x => col d x = 1 ∧ μ x ≠ 0)
      (a := w) (by simp [h0])]
    congr 1; ext x
    simp only [mem_filter, mem_range, mem_insert]
    by_cases hxb : x = b
    · subst hxb; simp [hcb, hwb.symm]
    · by_cases hxw : x = w
      · subst hxw; simp [hcw, hwn, Function.update_of_ne hxb]
      · simp [Function.update_of_ne hxb, Function.update_of_ne hxw, hxw]
  · simp only [h0, ite_false, add_zero]
    congr 1; ext x
    simp only [mem_filter, mem_range]
    by_cases hxb : x = b
    · subst hxb; simp [hcb]
    · by_cases hxw : x = w
      · subst hxw; simp [hcw, h0, Function.update_of_ne hxb]
      · simp [Function.update_of_ne hxb, Function.update_of_ne hxw]

/-- The size is at most the number of vertices. -/
lemma size_le (μ : ℕ → ℕ) : size d μ ≤ nn d := by
  unfold size
  exact (card_filter_le _ _).trans (by simp)

end BM

end PlanarFlow
