module

public import PlanarFlow.MSSP.Winding

/-!
# The circulation of a positive curl along a simple cycle

A word-size perturbation of the capacities of the perturbed run (`PlanarFlow/STFlow/IsoEps.lean`)
separates shortest paths by the *circulation* of an antisymmetric function along the cycles they
form (the isolation of Bourke, Tewari and Vinodchandran, *Directed planar reachability is in
unambiguous log-space*, ACM TOCT 1 (2009), for directed planar graphs): if the *curl*
`κ f = ∑_{face d = f} w d` of an antisymmetric `w` is positive at every face but one, then the
sum of `w` along any simple cycle is nonzero, and at most the total positive curl in absolute
value. This is the Jordan curve theorem for plane maps: the cycle is the coboundary of a winding
function (`exists_winding`) which takes two consecutive values only (`two_val`), so the sum is
the curl of one of the two sides.

The cycles here have `n ≥ 2` darts (`IsSCycle`: a cycle of two parallel darts is allowed); the
facts of `PlanarFlow/MSSP/Winding.lean` (stated there for `n ≥ 3`) are reproved in this
generality.

* `IsSCycle.isCirc`, `exists_winding2`: the circulation of the cycle is a coboundary;
* `face_cycle2`: the darts of the cycle have their faces on one side;
* `two_val`: **the winding function takes two consecutive values**;
* `sum_cycle_eq`: the sum of `w` along the cycle is `-∑_f φ f κ f`;
* `cycle_curl`: **the sum of `w` along a simple cycle is nonzero and at most the positive
  curl** (`κ > 0` off one face `f₀`).
* `isSCycle_of_list`: a closed walk with distinct tails is a simple cycle.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace CombMap

open Finset

variable {D V F : Type*} (M : CombMap D V F)

/-- **A simple cycle of `n ≥ 2` darts**: consecutive darts meet, the tails are pairwise distinct,
and no dart of the cycle is the reverse of another. -/
structure IsSCycle (n : ℕ) (c : ℕ → D) : Prop where
  two_le : 2 ≤ n
  step : ∀ t < n, M.head (c t) = M.tail (c ((t + 1) % n))
  inj : ∀ s < n, ∀ t < n, M.tail (c s) = M.tail (c t) → s = t
  norev : ∀ s < n, ∀ t < n, c t ≠ M.rev (c s)

variable [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]

variable {M} {n : ℕ} {c : ℕ → D}

namespace IsSCycle

variable (hC : M.IsSCycle n c)
include hC

lemma pos : 0 < n := by have := hC.two_le; omega

lemma head_pred {t : ℕ} (ht : t < n) : M.head (c ((t + n - 1) % n)) = M.tail (c t) := by
  rw [hC.step _ (mod_lt' hC.pos), pred_mod ht]
  congr 2
  split_ifs with h
  · subst h; rw [show n - 1 + 1 = n by omega, Nat.mod_self]
  · rw [show t - 1 + 1 = t by omega, Nat.mod_eq_of_lt ht]

lemma eq_pred {s t : ℕ} (hs : s < n) (ht : t < n) (h : M.head (c s) = M.tail (c t)) :
    s = (t + n - 1) % n := by
  rw [hC.step s hs] at h
  have := hC.inj _ (mod_lt' hC.pos) _ ht h
  rw [succ_mod hs] at this
  rw [pred_mod ht]
  split_ifs at this ⊢ with h1 h2 h2 <;> omega

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
    exact fun ht => hC.norev s hs t ht
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

lemma cyc_at {t : ℕ} (ht : t < n) {e : D} (he : M.tail e = M.tail (c t)) (h1 : e ≠ c t)
    (h2 : e ≠ M.rev (c ((t + n - 1) % n))) : M.cyc n c e = 0 := by
  refine hC.cyc_eq_zero (fun s hs h => h1 ?_) (fun s hs h => h2 ?_)
  · rw [← h]; rw [← h] at he; rw [hC.inj _ hs _ ht he]
  · have : M.head (c s) = M.tail (c t) := by rw [h, CombMap.head_rev, he]
    rw [← hC.eq_pred hs ht this, h, M.rev_rev]

/-- The values of the circulation of the cycle: `1` on a dart of the cycle, `-1` on the reverse
of one, `0` elsewhere. -/
lemma cyc_cases (e : D) :
    (M.cyc n c e = 1 ∧ ∃ t < n, c t = e) ∨ (M.cyc n c e = -1 ∧ ∃ t < n, c t = M.rev e) ∨
      M.cyc n c e = 0 := by
  by_cases h1 : ∃ t < n, c t = e
  · obtain ⟨t, ht, rfl⟩ := h1
    exact Or.inl ⟨hC.cyc_cycle ht, t, ht, rfl⟩
  · by_cases h2 : ∃ t < n, c t = M.rev e
    · obtain ⟨t, ht, h⟩ := h2
      have : M.cyc n c e = - M.cyc n c (c t) := by
        rw [h, cyc_rev, neg_neg]
      rw [hC.cyc_cycle ht] at this
      exact Or.inr (Or.inl ⟨this, t, ht, h⟩)
    · push Not at h1 h2
      exact Or.inr (Or.inr (hC.cyc_eq_zero h1 h2))

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

end IsSCycle

/-- **The winding function of a simple cycle in a plane map.** -/
theorem exists_winding2 (hM : M.IsPlane) (hC : M.IsSCycle n c) :
    ∃ φ : F → ℤ, ∀ d, φ (M.face (M.rev d)) = φ (M.face d) + M.cyc n c d := by
  obtain ⟨φ, hφ⟩ := exists_int_potential hM hC.isCirc
  exact ⟨φ, fun d => by rw [hφ d, CombMap.cob]; ring⟩

/-! ### Sides -/

section Sides

variable {φ : F → ℤ} (hC : M.IsSCycle n c)
  (hφ : ∀ d, φ (M.face (M.rev d)) = φ (M.face d) + M.cyc n c d)
include hC hφ

lemma face_rot_eq2 (d : D) : φ (M.face (M.rot d)) = φ (M.face d) + M.cyc n c d := by
  rw [M.face_rot, hφ]

lemma rotBetween_side2 (hrot : M.RotTrans) {t : ℕ} (ht : t < n) {e : D}
    (he : M.RotBetween (c t) (M.rev (c ((t + n - 1) % n))) e) :
    φ (M.face e) = φ (M.face (c t)) + 1 := by
  obtain ⟨i, hi, rfl, hnot⟩ := he
  set a := c ((t + n - 1) % n) with ha
  set b := c t with hb
  have hab : b ≠ M.rev a := hC.norev _ (mod_lt' hC.pos) t ht
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
      rw [Function.iterate_succ_apply', face_rot_eq2 hC hφ]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp only [Function.iterate_zero, id_eq]; rw [hb, hC.cyc_cycle ht]
      · rw [ih hj0 (by omega), hC.cyc_at ht (M.tail_rot_iterate j _) (hnb j hj0 (by omega))
          (hnot j hj0 (by omega)), add_zero]
  exact key i hi le_rfl

/-- **All the darts of the cycle have their faces on the same side.** -/
lemma face_cycle2 (hrot : M.RotTrans) {t : ℕ} (ht : t < n) :
    φ (M.face (c t)) = φ (M.face (c 0)) := by
  have step : ∀ s, s + 1 < n → φ (M.face (c s)) = φ (M.face (c (s + 1))) := by
    intro s hs
    have hpred : (s + 1 + n - 1) % n = s := by
      rw [show s + 1 + n - 1 = s + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hab : c (s + 1) ≠ M.rev (c s) := hC.norev s (by omega) (s + 1) hs
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
    have h1 := rotBetween_side2 hC hφ hrot hs hb
    rw [hφ, hC.cyc_cycle (by omega)] at h1
    omega
  induction t with
  | zero => rfl
  | succ t ih => rw [← step t ht, ih (by omega)]

/-- **The winding function takes two consecutive values**: `φ (face (c 0))` and one more. -/
theorem two_val (hM : M.IsPlane) (hrot : M.RotTrans) (f : F) :
    φ f = φ (M.face (c 0)) ∨ φ f = φ (M.face (c 0)) + 1 := by
  have hreach := hM.dualConn (M.face (c 0)) f
  induction hreach with
  | refl => exact Or.inl rfl
  | tail _ hyz ih =>
    obtain ⟨d, rfl, rfl⟩ := hyz
    rw [hφ d]
    rcases hC.cyc_cases d with ⟨h1, t, ht, rfl⟩ | ⟨h1, t, ht, h⟩ | h1
    · rw [h1, face_cycle2 hC hφ hrot ht]; exact Or.inr rfl
    · have e := face_cycle2 hC hφ hrot ht
      rw [h] at e
      rw [h1]
      rcases ih with h2 | h2
      · exfalso
        have := hφ d; rw [e] at this; omega
      · omega
    · rw [h1, add_zero]; exact ih

end Sides

/-! ### The sum along the cycle -/

variable (M) in
/-- The curl of `w` at the face `f`: the sum of `w` along its boundary. -/
def curl (w : D → ℤ) (f : F) : ℤ := ∑ d with M.face d = f, w d

lemma sum_curl (w : D → ℤ) (φ : F → ℤ) : ∑ f, φ f * M.curl w f = ∑ d, φ (M.face d) * w d := by
  simp only [curl, mul_sum]
  rw [← sum_fiberwise (s := univ) (g := M.face) (f := fun d => φ (M.face d) * w d)]
  refine sum_congr rfl fun f _ => sum_congr rfl fun d hd => ?_
  simp only [mem_filter, mem_univ, true_and] at hd
  rw [hd]

lemma sum_curl_univ {w : D → ℤ} (hw : M.IsAntisymm w) : ∑ f, M.curl w f = 0 := by
  have h1 : ∑ f, M.curl w f = ∑ d, w d := by
    have := sum_curl (M := M) w (fun _ => 1)
    simpa using this
  have h2 : ∑ d, w d = ∑ d, w (M.rev d) :=
    (Fintype.sum_equiv ⟨M.rev, M.rev, M.rev_rev, M.rev_rev⟩ _ _ fun d => rfl).symm
  have hw' : ∀ d, w (M.rev d) = - w d := hw
  simp only [hw'] at h2
  rw [sum_neg_distrib] at h2
  linarith

/-- **The sum along a simple cycle as a sum over the faces.** -/
theorem sum_cycle_eq {φ : F → ℤ}
    (hφ : ∀ d, φ (M.face (M.rev d)) = φ (M.face d) + M.cyc n c d) {w : D → ℤ}
    (hw : M.IsAntisymm w) :
    ∑ t ∈ range n, w (c t) = - ∑ f, φ f * M.curl w f := by
  have hw' : ∀ d, w (M.rev d) = - w d := hw
  -- `∑ cyc · w = 2 ∑ w (c t)`
  have hcnt : ∀ g : ℕ → D, ∑ d, (#{t ∈ range n | g t = d} : ℤ) * w d = ∑ t ∈ range n, w (g t) := by
    intro g
    rw [← sum_fiberwise (s := range n) (g := g) (f := fun t => w (g t))]
    refine sum_congr rfl fun d _ => ?_
    rw [sum_congr rfl (g := fun _ => w d) (fun t ht => by
      simp only [mem_filter] at ht; rw [ht.2]), sum_const, nsmul_eq_mul]
  have h1 : ∑ d, M.cyc n c d * w d = 2 * ∑ t ∈ range n, w (c t) := by
    simp only [cyc, sub_mul, sum_sub_distrib]
    rw [hcnt c]
    have : ∑ d, (#{t ∈ range n | c t = M.rev d} : ℤ) * w d =
        ∑ d, (#{t ∈ range n | c t = d} : ℤ) * w (M.rev d) :=
      Fintype.sum_equiv ⟨M.rev, M.rev, M.rev_rev, M.rev_rev⟩ _ _ fun d => by simp [M.rev_rev]
    rw [this]
    simp only [hw', mul_neg, sum_neg_distrib]
    rw [hcnt c]; ring
  have h2 : ∑ d, M.cyc n c d * w d = -2 * ∑ d, φ (M.face d) * w d := by
    have e : ∀ d, M.cyc n c d = φ (M.face (M.rev d)) - φ (M.face d) := fun d => by
      rw [hφ d]; ring
    simp only [e, sub_mul, sum_sub_distrib]
    have : ∑ d, φ (M.face (M.rev d)) * w d = ∑ d, φ (M.face d) * w (M.rev d) :=
      Fintype.sum_equiv ⟨M.rev, M.rev, M.rev_rev, M.rev_rev⟩ _ _ fun d => by simp [M.rev_rev]
    rw [this]
    simp only [hw', mul_neg, sum_neg_distrib]
    ring
  rw [sum_curl]
  linarith

/-- **The sum of a function of positive curl along a simple cycle is nonzero**, and at most the
curl of the faces other than `f₀` in absolute value: for `w` antisymmetric with `curl w f > 0` at
every face `f ≠ f₀`. -/
theorem cycle_curl (hM : M.IsPlane) (hrot : M.RotTrans) (hC : M.IsSCycle n c) {w : D → ℤ}
    (hw : M.IsAntisymm w) {f₀ : F} (hpos : ∀ f, f ≠ f₀ → 0 < M.curl w f) :
    ∑ t ∈ range n, w (c t) ≠ 0 ∧
      |∑ t ∈ range n, w (c t)| ≤ ∑ f ∈ univ.erase f₀, M.curl w f := by
  obtain ⟨φ, hφ⟩ := exists_winding2 hM hC
  have hS := sum_cycle_eq hφ hw
  set a := φ (M.face (c 0))
  set ψ : F → ℤ := fun f => φ f - φ f₀
  have hshift : ∑ f, φ f * M.curl w f = ∑ f ∈ univ.erase f₀, ψ f * M.curl w f := by
    have e1 : ∑ f, φ f * M.curl w f = ∑ f, ψ f * M.curl w f := by
      simp only [ψ, sub_mul, sum_sub_distrib, ← mul_sum, sum_curl_univ hw, mul_zero, sub_zero]
    rw [e1, ← sum_erase_add _ _ (mem_univ f₀)]
    simp [ψ]
  rw [hshift] at hS
  rw [hS, abs_neg]
  have h0 := hC.cyc_cycle (show 0 < n from hC.pos)
  have hrev : φ (M.face (M.rev (c 0))) = a + 1 := by rw [hφ, h0]
  have hκ : 0 ≤ ∑ f ∈ univ.erase f₀, M.curl w f :=
    sum_nonneg fun f hf => (hpos f (ne_of_mem_erase hf)).le
  rcases two_val hC hφ hM hrot f₀ with hf₀ | hf₀
  · -- `ψ` is `0` or `1`, and `1` at the face of the reverse of `c 0`
    have hψ : ∀ f, ψ f = 0 ∨ ψ f = 1 := fun f => by
      rcases two_val hC hφ hM hrot f with h | h <;> simp only [ψ] <;> omega
    have hne : M.face (M.rev (c 0)) ≠ f₀ := fun h => by rw [h] at hrev; omega
    have hlow : M.curl w (M.face (M.rev (c 0))) ≤ ∑ f ∈ univ.erase f₀, ψ f * M.curl w f := by
      rw [← sum_erase_add _ _ (mem_erase.2 ⟨hne, mem_univ _⟩)]
      have : ψ (M.face (M.rev (c 0))) = 1 := by simp only [ψ]; omega
      rw [this, one_mul]
      have : 0 ≤ ∑ f ∈ (univ.erase f₀).erase (M.face (M.rev (c 0))), ψ f * M.curl w f :=
        sum_nonneg fun f hf => by
          have := hpos f (ne_of_mem_erase (mem_of_mem_erase hf))
          rcases hψ f with h | h <;> rw [h] <;> omega
      omega
    have hup : ∑ f ∈ univ.erase f₀, ψ f * M.curl w f ≤ ∑ f ∈ univ.erase f₀, M.curl w f :=
      sum_le_sum fun f hf => by
        have := hpos f (ne_of_mem_erase hf)
        rcases hψ f with h | h <;> rw [h] <;> omega
    have := hpos _ hne
    refine ⟨by omega, ?_⟩
    rw [abs_of_pos (by omega)]; exact hup
  · -- `ψ` is `0` or `-1`, and `-1` at the face of `c 0`
    have hψ : ∀ f, ψ f = 0 ∨ ψ f = -1 := fun f => by
      rcases two_val hC hφ hM hrot f with h | h <;> simp only [ψ] <;> omega
    have hne : M.face (c 0) ≠ f₀ := fun h => by
      have : a = a + 1 := by rw [← hf₀, ← h]
      omega
    have hlow : ∑ f ∈ univ.erase f₀, ψ f * M.curl w f ≤ - M.curl w (M.face (c 0)) := by
      rw [← sum_erase_add _ _ (mem_erase.2 ⟨hne, mem_univ _⟩)]
      have : ψ (M.face (c 0)) = -1 := by simp only [ψ]; omega
      rw [this]
      have : ∑ f ∈ (univ.erase f₀).erase (M.face (c 0)), ψ f * M.curl w f ≤ 0 :=
        sum_nonpos fun f hf => by
          have := hpos f (ne_of_mem_erase (mem_of_mem_erase hf))
          rcases hψ f with h | h <;> rw [h] <;> omega
      linarith
    have hup : - ∑ f ∈ univ.erase f₀, M.curl w f ≤ ∑ f ∈ univ.erase f₀, ψ f * M.curl w f := by
      rw [← sum_neg_distrib]
      exact sum_le_sum fun f hf => by
        have := hpos f (ne_of_mem_erase hf)
        rcases hψ f with h | h <;> rw [h] <;> omega
    have := hpos _ hne
    refine ⟨by omega, ?_⟩
    rw [abs_of_neg (by omega)]; linarith

/-! ### Closed walks with distinct tails -/

/-- **A closed walk of at least two darts with distinct tails is a simple cycle** (for two darts,
the second must not be the reverse of the first). -/
theorem isSCycle_of_list (d₀ : D) {cl : List D} (h2 : 2 ≤ cl.length)
    (hstep : ∀ t (ht : t + 1 < cl.length), M.head cl[t] = M.tail cl[t + 1])
    (hlast : M.head (cl[cl.length - 1]'(by omega)) = M.tail (cl[0]'(by omega)))
    (hnd : (cl.map M.tail).Nodup)
    (htwo : ∀ (h : cl.length = 2), cl[1]'(by omega) ≠ M.rev (cl[0]'(by omega))) :
    M.IsSCycle cl.length (fun t => cl.getD t d₀) := by
  have hg : ∀ t (ht : t < cl.length), cl.getD t d₀ = cl[t] := fun t ht => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  have hinj : ∀ s < cl.length, ∀ t < cl.length, M.tail (cl.getD s d₀) = M.tail (cl.getD t d₀) →
      s = t := by
    intro s hs t ht h
    rw [hg s hs, hg t ht] at h
    have := (List.Nodup.getElem_inj_iff hnd (i := s) (j := t) (hi := by simpa using hs)
      (hj := by simpa using ht)).1 (by simpa using h)
    exact this
  have hstep' : ∀ t < cl.length,
      M.head (cl.getD t d₀) = M.tail (cl.getD ((t + 1) % cl.length) d₀) := by
    intro t ht
    rw [succ_mod ht]
    split_ifs with h
    · rw [hg t ht, hg 0 (by omega)]
      have : t = cl.length - 1 := by omega
      subst this; exact hlast
    · rw [hg t ht, hg (t + 1) (by omega)]; exact hstep t (by omega)
  refine ⟨h2, hstep', hinj, fun s hs t ht h => ?_⟩
  -- `c t = rev (c s)`: then `t = s + 1` and `s = t + 1` modulo the length
  have e1 : M.tail (cl.getD t d₀) = M.tail (cl.getD ((s + 1) % cl.length) d₀) := by
    rw [h, CombMap.tail_rev, hstep' s hs]
  have e2 : M.tail (cl.getD s d₀) = M.tail (cl.getD ((t + 1) % cl.length) d₀) := by
    rw [← hstep' t ht, h, CombMap.head_rev]
  have i1 := hinj _ ht _ (mod_lt' (by omega)) e1
  have i2 := hinj _ hs _ (mod_lt' (by omega)) e2
  rw [succ_mod hs] at i1
  rw [succ_mod ht] at i2
  have hst : s ≠ t := by
    rintro rfl
    exact M.rev_ne _ h.symm
  have hlen : cl.length = 2 := by split_ifs at i1 i2 <;> omega
  have := htwo hlen
  rcases (show (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hg 1 ht, hg 0 hs] at h; exact this h
  · rw [hg 0 ht, hg 1 hs] at h
    exact this (by rw [h, M.rev_rev])

end CombMap

end PlanarFlow
