module

public import PlanarFlow.Plane.Potential
public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# The two sides of a simple cycle in a plane map

A combinatorial form of the Jordan curve theorem for a plane map `M`: a simple cycle `c 0, …,
c (n - 1)` of darts (consecutive darts meet, the tails are pairwise distinct, `n ≥ 3`) defines a
circulation `cyc` (`1` on the darts of the cycle, `-1` on their reverses, `0` elsewhere), which is
the coboundary of a *winding function* `φ` on the faces (`exists_winding`, from
`PlanarFlow.CombMap.exists_int_potential`). Crossing a dart off the cycle does not change `φ`;
crossing the cycle changes it by one.

With rotations transitive at every vertex (`RotTrans`, which holds for the maps of rotation
systems), this gives:

* `side_eq`: all the faces at a vertex off the cycle have the same value of `φ` (its *side*);
* `face_cycle`: all the darts of the cycle have their face on the same side, `φ (face (c 0))`;
* `rotBetween_side`: at a vertex `tail (c t)` of the cycle, the darts strictly after the outgoing
  dart `c t` and up to the reverse of the incoming dart, in the rotation order, have their faces
  on the other side, `φ (face (c 0)) + 1`;
* `side_arc`: the two ends of a dart off the cycle are on the same side.

These are the planarity facts behind the non-crossing of shortest paths from a face, used by the
multiple-source shortest path algorithm of Das, Kipouridis, Probst Gutenberg and Wulff-Nilsen
(SOSA 2022, Lemma 5.4).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace CombMap

open Finset

variable {D V F : Type*} (M : CombMap D V F)

/-- **Transitive rotations**: the darts leaving a vertex form one orbit of the rotation. -/
def RotTrans : Prop := ∀ d d', M.tail d = M.tail d' → ∃ k, M.rot^[k] d = d'

/-- `e` comes strictly after `b` in the rotation at `tail b`, not after `c`: the first `i ≥ 1`
with `rot^[i] b = e` comes before or at the first `j ≥ 1` with `rot^[j] b = c`. -/
def RotBetween (b c e : D) : Prop :=
  ∃ i, 0 < i ∧ M.rot^[i] b = e ∧ ∀ j, 0 < j → j < i → M.rot^[j] b ≠ c

lemma tail_rot_iterate (k : ℕ) (d : D) : M.tail (M.rot^[k] d) = M.tail d := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, M.tail_rot]

/-- A simple cycle of `n ≥ 3` darts: consecutive darts meet and the tails are pairwise distinct. -/
structure IsSimpleCycle (n : ℕ) (c : ℕ → D) : Prop where
  three_le : 3 ≤ n
  step : ∀ t < n, M.head (c t) = M.tail (c ((t + 1) % n))
  inj : ∀ s < n, ∀ t < n, M.tail (c s) = M.tail (c t) → s = t

/-- The vertex `v` lies on the cycle. -/
def OnCyc (n : ℕ) (c : ℕ → D) (v : V) : Prop := ∃ t < n, M.tail (c t) = v

section Arith

lemma succ_mod {t n : ℕ} (h : t < n) : (t + 1) % n = if t + 1 = n then 0 else t + 1 := by
  split_ifs with h1
  · rw [h1, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

lemma pred_mod {t n : ℕ} (h : t < n) : (t + n - 1) % n = if t = 0 then n - 1 else t - 1 := by
  split_ifs with h1
  · subst h1; rw [zero_add]; exact Nat.mod_eq_of_lt (by omega)
  · rw [show t + n - 1 = (t - 1) + n by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

lemma mod_lt' {t n : ℕ} (h : 0 < n) : t % n < n := Nat.mod_lt _ h

end Arith

variable [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]

/-- The circulation of a cycle: `1` on its darts, `-1` on their reverses. -/
def cyc (n : ℕ) (c : ℕ → D) (d : D) : ℤ :=
  (#{t ∈ range n | c t = d} : ℤ) - #{t ∈ range n | c t = M.rev d}

variable {M} {n : ℕ} {c : ℕ → D}

lemma cyc_rev (d : D) : M.cyc n c (M.rev d) = - M.cyc n c d := by
  simp [cyc, M.rev_rev]

namespace IsSimpleCycle

variable (hC : M.IsSimpleCycle n c)
include hC

lemma pos : 0 < n := by have := hC.three_le; omega

lemma head_eq (t : ℕ) (ht : t < n) : M.head (c t) = M.tail (c ((t + 1) % n)) := hC.step t ht

/-- The dart of the cycle ending at `tail (c t)`. -/
lemma head_pred {t : ℕ} (ht : t < n) : M.head (c ((t + n - 1) % n)) = M.tail (c t) := by
  rw [hC.step _ (mod_lt' hC.pos), pred_mod ht]
  congr 2
  split_ifs with h
  · subst h; rw [show n - 1 + 1 = n by omega, Nat.mod_self]
  · rw [show t - 1 + 1 = t by omega, Nat.mod_eq_of_lt ht]

/-- The only dart of the cycle ending at `tail (c t)` is `c (t - 1)`. -/
lemma eq_pred {s t : ℕ} (hs : s < n) (ht : t < n) (h : M.head (c s) = M.tail (c t)) :
    s = (t + n - 1) % n := by
  rw [hC.step s hs] at h
  have := hC.inj _ (mod_lt' hC.pos) _ ht h
  rw [succ_mod hs] at this
  rw [pred_mod ht]
  split_ifs at this ⊢ with h1 h2 h2 <;> omega

lemma not_rev_mem {s t : ℕ} (hs : s < n) (ht : t < n) : c t ≠ M.rev (c s) := by
  intro h
  have h1 : M.tail (c t) = M.head (c s) := by rw [h]; simp
  rw [hC.step s hs] at h1
  have e1 := hC.inj _ ht _ (mod_lt' hC.pos) h1
  have h2 : M.head (c t) = M.tail (c s) := by rw [h, CombMap.head_rev]
  have e2 := hC.eq_pred ht hs h2
  have := hC.three_le
  rw [succ_mod hs] at e1
  rw [pred_mod hs] at e2
  split_ifs at e1 e2 <;> omega

lemma cyc_cycle {s : ℕ} (hs : s < n) : M.cyc n c (c s) = 1 := by
  have h1 : ({t ∈ range n | c t = c s} : Finset ℕ) = {s} := by
    ext t
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨ht, h⟩; exact hC.inj _ ht _ hs (by rw [h])
    · rintro rfl; exact ⟨hs, rfl⟩
  have h2 : ({t ∈ range n | c t = M.rev (c s)} : Finset ℕ) = ∅ := by
    ext t
    simp only [mem_filter, mem_range, Finset.notMem_empty, iff_false, not_and]
    exact fun ht => hC.not_rev_mem hs ht
  simp [cyc, h1, h2]

lemma cyc_eq_zero {e : D} (h1 : ∀ t < n, c t ≠ e) (h2 : ∀ t < n, c t ≠ M.rev e) :
    M.cyc n c e = 0 := by
  have e1 : ({t ∈ range n | c t = e} : Finset ℕ) = ∅ := by
    ext t; simp only [mem_filter, mem_range, Finset.notMem_empty, iff_false, not_and]
    exact h1 t
  have e2 : ({t ∈ range n | c t = M.rev e} : Finset ℕ) = ∅ := by
    ext t; simp only [mem_filter, mem_range, Finset.notMem_empty, iff_false, not_and]
    exact h2 t
  simp [cyc, e1, e2]

/-- A dart leaving a vertex off the cycle is not on the cycle. -/
lemma cyc_off {e : D} (he : ¬ M.OnCyc n c (M.tail e)) : M.cyc n c e = 0 := by
  refine hC.cyc_eq_zero (fun t ht h => he ⟨t, ht, by rw [h]⟩) (fun t ht h => he ?_)
  refine ⟨(t + 1) % n, mod_lt' hC.pos, ?_⟩
  rw [← hC.step t ht, h, CombMap.head_rev]

/-- The darts leaving a vertex of the cycle: `1` on the outgoing dart of the cycle, `-1` on the
reverse of the incoming one, `0` elsewhere. -/
lemma cyc_at {t : ℕ} (ht : t < n) {e : D} (he : M.tail e = M.tail (c t)) (h1 : e ≠ c t)
    (h2 : e ≠ M.rev (c ((t + n - 1) % n))) : M.cyc n c e = 0 := by
  refine hC.cyc_eq_zero (fun s hs h => h1 ?_) (fun s hs h => h2 ?_)
  · rw [← h]; rw [← h] at he; rw [hC.inj _ hs _ ht he]
  · have : M.head (c s) = M.tail (c t) := by rw [h, CombMap.head_rev, he]
    rw [← hC.eq_pred hs ht this, h, M.rev_rev]

/-- **The circulation of a simple cycle.** -/
lemma isCirc : M.IsCirc (M.cyc n c) := by
  refine ⟨fun d => cyc_rev d, fun v => ?_⟩
  simp only [CombMap.div, cyc, sum_sub_distrib]
  have k1 : ∑ d with M.tail d = v, (#{t ∈ range n | c t = d} : ℤ) =
      #{t ∈ range n | M.tail (c t) = v} := by
    rw [card_eq_sum_card_fiberwise (f := c) (t := ({d | M.tail d = v} : Finset D))
      (fun t ht => mem_filter.2 ⟨mem_univ _, (mem_filter.1 ht).2⟩)]
    push_cast
    refine sum_congr rfl fun d hd => ?_
    simp only [mem_filter, mem_univ, true_and] at hd
    congr 2; ext t; simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨ht, rfl⟩; exact ⟨⟨ht, hd⟩, rfl⟩
    · rintro ⟨⟨ht, -⟩, rfl⟩; exact ⟨ht, rfl⟩
  have k2 : ∑ d with M.tail d = v, (#{t ∈ range n | c t = M.rev d} : ℤ) =
      #{t ∈ range n | M.head (c t) = v} := by
    rw [card_eq_sum_card_fiberwise (f := fun t => M.rev (c t))
      (t := ({d | M.tail d = v} : Finset D))
      (fun t ht => mem_filter.2 ⟨mem_univ _, by
        have := (mem_filter.1 ht).2; rw [← this]; rfl⟩)]
    push_cast
    refine sum_congr rfl fun d hd => ?_
    simp only [mem_filter, mem_univ, true_and] at hd
    congr 2; ext t; simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨ht, h⟩
      refine ⟨⟨ht, ?_⟩, by rw [h, M.rev_rev]⟩
      rw [← hd, h]; simp
    · rintro ⟨⟨ht, -⟩, rfl⟩; exact ⟨ht, by rw [M.rev_rev]⟩
  have k3 : #{t ∈ range n | M.head (c t) = v} = #{t ∈ range n | M.tail (c t) = v} := by
    refine card_nbij (fun t => (t + 1) % n) (fun t ht => ?_) (fun s hs t ht h => ?_) ?_
    · simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ht ⊢
      exact ⟨mod_lt' hC.pos, by rw [← hC.step _ ht.1, ht.2]⟩
    · simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hs ht
      simp only at h
      rw [succ_mod hs.1, succ_mod ht.1] at h
      split_ifs at h <;> omega
    · intro s hs
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hs
      refine ⟨(s + n - 1) % n, ?_, ?_⟩
      · simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
        exact ⟨mod_lt' hC.pos, by rw [hC.head_pred hs.1, hs.2]⟩
      · simp only
        rw [pred_mod hs.1]
        split_ifs with h
        · subst h; rw [show n - 1 + 1 = n by omega, Nat.mod_self]
        · rw [show s - 1 + 1 = s by omega, Nat.mod_eq_of_lt hs.1]
  rw [k1, k2, k3, sub_self]

end IsSimpleCycle

/-- **The winding function of a simple cycle in a plane map**: a function on the faces whose
coboundary is the circulation of the cycle. -/
theorem exists_winding (hM : M.IsPlane) (hC : M.IsSimpleCycle n c) :
    ∃ φ : F → ℤ, ∀ d, φ (M.face (M.rev d)) = φ (M.face d) + M.cyc n c d := by
  obtain ⟨φ, hφ⟩ := exists_int_potential hM hC.isCirc
  exact ⟨φ, fun d => by rw [hφ d, CombMap.cob]; ring⟩

/-! ### Sides -/

section Sides

variable {φ : F → ℤ} (hC : M.IsSimpleCycle n c)
  (hφ : ∀ d, φ (M.face (M.rev d)) = φ (M.face d) + M.cyc n c d)
include hC hφ

lemma face_rot_eq (d : D) : φ (M.face (M.rot d)) = φ (M.face d) + M.cyc n c d := by
  rw [M.face_rot, hφ]

/-- **All the faces at a vertex off the cycle are on the same side.** -/
lemma side_eq (hrot : M.RotTrans) {d d' : D} (h : M.tail d = M.tail d')
    (hoff : ¬ M.OnCyc n c (M.tail d)) : φ (M.face d) = φ (M.face d') := by
  obtain ⟨k, rfl⟩ := hrot d d' h
  clear h
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', face_rot_eq hC hφ, ih,
      hC.cyc_off (by rwa [M.tail_rot_iterate]), add_zero]

/-- **The two ends of a dart off the cycle are on the same side.** -/
lemma side_arc {d : D} (hoff : ¬ M.OnCyc n c (M.tail d)) :
    φ (M.face (M.rev d)) = φ (M.face d) := by
  rw [hφ, hC.cyc_off hoff, add_zero]

/-- **The rotation at a vertex of the cycle**: the darts strictly after the outgoing dart, up to
the reverse of the incoming dart, are on the other side. -/
lemma rotBetween_side (hrot : M.RotTrans) {t : ℕ} (ht : t < n) {e : D}
    (he : M.RotBetween (c t) (M.rev (c ((t + n - 1) % n))) e) :
    φ (M.face e) = φ (M.face (c t)) + 1 := by
  obtain ⟨i, hi, rfl, hnot⟩ := he
  set a := c ((t + n - 1) % n) with ha
  set b := c t with hb
  have hab : b ≠ M.rev a := fun h => hC.not_rev_mem (mod_lt' hC.pos) ht h
  -- the rotation does not come back to `b` before step `i`
  have hnb : ∀ j, 0 < j → j < i → M.rot^[j] b ≠ b := by
    intro j hj hji hjb
    have hta : M.tail b = M.tail (M.rev a) := by
      rw [CombMap.tail_rev, ha, hC.head_pred ht]
    obtain ⟨k, hk⟩ := hrot b (M.rev a) hta
    have hper : Function.IsPeriodicPt M.rot j b := hjb
    rw [← hper.iterate_mod_apply k] at hk
    have hlt := Nat.mod_lt k hj
    rcases Nat.eq_zero_or_pos (k % j) with h0 | h0
    · rw [h0] at hk; exact hab hk
    · exact hnot _ h0 (by omega) hk
  have key : ∀ j, 0 < j → j ≤ i → φ (M.face (M.rot^[j] b)) = φ (M.face b) + 1 := by
    intro j hj hji
    induction j with
    | zero => omega
    | succ j ih =>
      rw [Function.iterate_succ_apply', face_rot_eq hC hφ]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp only [Function.iterate_zero, id_eq]; rw [hb, hC.cyc_cycle ht]
      · rw [ih hj0 (by omega), hC.cyc_at ht (M.tail_rot_iterate j _) (hnb j hj0 (by omega))
          (hnot j hj0 (by omega)), add_zero]
  exact key i hi le_rfl

/-- **All the darts of the cycle have their faces on the same side.** -/
lemma face_cycle (hrot : M.RotTrans) {t : ℕ} (ht : t < n) :
    φ (M.face (c t)) = φ (M.face (c 0)) := by
  -- consecutive darts: the incoming dart and the outgoing dart at every vertex
  have step : ∀ s, s + 1 < n → φ (M.face (c s)) = φ (M.face (c (s + 1))) := by
    intro s hs
    have hpred : (s + 1 + n - 1) % n = s := by
      rw [show s + 1 + n - 1 = s + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hab : c (s + 1) ≠ M.rev (c s) := hC.not_rev_mem (by omega) hs
    have hta : M.tail (c (s + 1)) = M.tail (M.rev (c s)) := by
      rw [CombMap.tail_rev, hC.step s (by omega), Nat.mod_eq_of_lt hs]
    obtain ⟨k, hk⟩ := hrot _ _ hta
    classical
    have hex : ∃ k, M.rot^[k] (c (s + 1)) = M.rev (c s) := ⟨k, hk⟩
    have hk0 : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · have := Nat.find_spec hex; rw [h] at this; exact absurd this hab
      · exact h
    have hb : M.RotBetween (c (s + 1)) (M.rev (c ((s + 1 + n - 1) % n))) (M.rev (c s)) := by
      rw [hpred]
      exact ⟨Nat.find hex, hk0, Nat.find_spec hex, fun j _ hj => Nat.find_min hex hj⟩
    have h1 := rotBetween_side hC hφ hrot hs hb
    rw [hφ, hC.cyc_cycle (by omega)] at h1
    omega
  induction t with
  | zero => rfl
  | succ t ih => rw [← step t ht, ih (by omega)]

end Sides

end CombMap

end PlanarFlow
