module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Data.Fintype.Card

/-!
# Orbits of permutations: counting, transpositions and first returns

The combinatorial facts on permutations behind the planarity of submaps
(`PlanarFlow/Plane/Submap.lean`): a combinatorial map is given by permutations of its darts, its
vertices and faces are the orbits of two of them, and deleting or contracting an edge changes
these permutations in two ways only.

* `nOrb π A`: the number of orbits of `π` meeting the finite set `A`.
* **Composing with a transposition** (`sameCycle_mul_swap`, `nOrb_mul_swap_merge`,
  `nOrb_mul_swap_split`): `π * swap a b` merges the orbits of `a` and `b` when they differ, and
  splits it in two when they coincide.
* **The first return** `ret π A` to a set `A`: on `A`, the first element of `A` after `x` along
  the orbit of `x`; outside `A`, the identity. Its orbits are the orbits of `π` cut down to `A`
  (`sameCycle_ret`, `nOrb_ret`), and first returns compose (`ret_ret`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Orbit

open Finset Function Equiv

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Iterates -/

lemma sameCycle_iff {π : Perm α} {x y : α} : π.SameCycle x y ↔ ∃ n : ℕ, π^[n] x = y := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by rw [← Perm.coe_pow]; exact hn⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by rw [zpow_natCast, Perm.coe_pow]⟩

lemma sameCycle_iterate (π : Perm α) (x : α) (n : ℕ) : π.SameCycle x (π^[n] x) :=
  sameCycle_iff.2 ⟨n, rfl⟩

lemma period_pos (π : Perm α) (x : α) : 0 < minimalPeriod π x :=
  minimalPeriod_pos_of_mem_periodicPts (π.injective.mem_periodicPts x)

lemma iterate_period (π : Perm α) (x : α) : π^[minimalPeriod π x] x = x := iterate_minimalPeriod

lemma iterate_mod (π : Perm α) (x : α) (n : ℕ) : π^[n % minimalPeriod π x] x = π^[n] x :=
  iterate_mod_minimalPeriod_eq

lemma iterate_inj {π : Perm α} {x : α} {i j : ℕ} (hi : i < minimalPeriod π x)
    (hj : j < minimalPeriod π x) (h : π^[i] x = π^[j] x) : i = j :=
  (iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).1 h

/-- Every element of the orbit of `x` is `π^[r] x` for some `0 < r ≤ period`. -/
lemma exists_iterate_pos {π : Perm α} {x y : α} (h : π.SameCycle x y) :
    ∃ r, 0 < r ∧ r ≤ minimalPeriod π x ∧ π^[r] x = y := by
  obtain ⟨n, rfl⟩ := sameCycle_iff.1 h
  have hp := period_pos π x
  by_cases h0 : n % minimalPeriod π x = 0
  · refine ⟨_, hp, le_rfl, ?_⟩
    rw [iterate_period, ← iterate_mod, h0]; rfl
  · exact ⟨_, Nat.pos_of_ne_zero h0, (Nat.mod_lt _ hp).le, iterate_mod π x n⟩

/-- Every element of the orbit of `x` is `π^[r] x` for some `r < period`. -/
lemma exists_iterate_lt {π : Perm α} {x y : α} (h : π.SameCycle x y) :
    ∃ r, r < minimalPeriod π x ∧ π^[r] x = y := by
  obtain ⟨n, rfl⟩ := sameCycle_iff.1 h
  exact ⟨_, Nat.mod_lt _ (period_pos π x), iterate_mod π x n⟩

/-! ### Counting orbits -/

/-- The orbit of `x`, as a finite set. -/
noncomputable def cls (π : Perm α) (x : α) : Finset α := by classical exact univ.filter (π.SameCycle x)

lemma mem_cls {π : Perm α} {x y : α} : y ∈ cls π x ↔ π.SameCycle x y := by
  classical simp [cls]

lemma cls_eq_iff {π : Perm α} {x y : α} : cls π x = cls π y ↔ π.SameCycle x y := by
  constructor
  · intro h
    have : y ∈ cls π x := h ▸ mem_cls.2 (Perm.SameCycle.refl _ _)
    exact mem_cls.1 this
  · intro h
    ext z; simp only [mem_cls]
    exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

/-- **The number of orbits of `π` meeting `A`.** -/
noncomputable def nOrb (π : Perm α) (A : Finset α) : ℕ := (A.image (cls π)).card

/-- A coarser function on `s` has an image of at most the same size. -/
lemma card_image_le_of_fiber {β γ : Type*} [DecidableEq β] [DecidableEq γ] {s : Finset α}
    {f : α → β} {g : α → γ} (h : ∀ x ∈ s, ∀ y ∈ s, g x = g y → f x = f y) :
    (s.image f).card ≤ (s.image g).card := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨x0, -⟩
  · simp
  have key : ∀ z, ∃ x, z ∈ s.image f → x ∈ s ∧ f x = z := fun z => by
    by_cases hz : z ∈ s.image f
    · obtain ⟨x, hx, e⟩ := mem_image.1 hz; exact ⟨x, fun _ => ⟨hx, e⟩⟩
    · exact ⟨x0, fun h => absurd h hz⟩
  choose r hr using key
  have hr1 : ∀ z ∈ s.image f, r z ∈ s := fun z hz => (hr z hz).1
  have hr2 : ∀ z ∈ s.image f, f (r z) = z := fun z hz => (hr z hz).2
  refine card_le_card_of_injOn (fun z => g (r z)) (fun z hz => ?_) (fun z hz z' hz' he => ?_)
  · exact mem_image_of_mem _ (hr1 z hz)
  · rw [← hr2 z hz, ← hr2 z' hz']
    exact h _ (hr1 z hz) _ (hr1 z' hz') he

/-- `nOrb` depends only on the relation "same orbit" between the elements of `A`. -/
lemma nOrb_congr {π π' : Perm α} {A : Finset α}
    (h : ∀ x ∈ A, ∀ y ∈ A, π.SameCycle x y ↔ π'.SameCycle x y) : nOrb π A = nOrb π' A :=
  le_antisymm
    (card_image_le_of_fiber fun x hx y hy e =>
      cls_eq_iff.2 ((h x hx y hy).2 (cls_eq_iff.1 e)))
    (card_image_le_of_fiber fun x hx y hy e =>
      cls_eq_iff.2 ((h x hx y hy).1 (cls_eq_iff.1 e)))

/-- Removing an element whose orbit meets the rest of `A` keeps the count. -/
lemma nOrb_erase_of {π : Perm α} {A : Finset α} {x y : α} (hy : y ∈ A) (hyx : y ≠ x)
    (h : π.SameCycle x y) : nOrb π (A.erase x) = nOrb π A := by
  unfold nOrb
  congr 1
  ext z
  simp only [mem_image, mem_erase]
  constructor
  · rintro ⟨w, ⟨-, hw⟩, rfl⟩; exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    by_cases hwx : w = x
    · subst hwx; exact ⟨y, ⟨hyx, hy⟩, cls_eq_iff.2 h.symm⟩
    · exact ⟨w, ⟨hwx, hw⟩, rfl⟩

/-- Removing an element whose orbit meets `A` only there decreases the count by one. -/
lemma nOrb_erase_alone {π : Perm α} {A : Finset α} {x : α} (hx : x ∈ A)
    (h : ∀ y ∈ A, π.SameCycle x y → y = x) : nOrb π (A.erase x) + 1 = nOrb π A := by
  unfold nOrb
  have e : A.image (cls π) = insert (cls π x) ((A.erase x).image (cls π)) := by
    rw [← image_insert, insert_erase hx]
  have hn : cls π x ∉ (A.erase x).image (cls π) := by
    simp only [mem_image, mem_erase, not_exists, not_and]
    intro y hyx hy
    exact hyx.1 (h y hyx.2 (cls_eq_iff.1 hy.symm))
  rw [e, card_insert_of_notMem hn]

lemma nOrb_le_card (π : Perm α) (A : Finset α) : nOrb π A ≤ A.card := card_image_le

lemma nOrb_empty (π : Perm α) : nOrb π ∅ = 0 := by simp [nOrb]

/-! ### Composing with a transposition -/

section Swap

variable {π : Perm α} {a b : α}

/-- Outside the orbits of `a` and `b`, `π * swap a b` acts as `π`. -/
lemma iterate_mul_swap_of {x : α} (ha : ¬ π.SameCycle a x) (hb : ¬ π.SameCycle b x) (n : ℕ) :
    (π * swap a b)^[n] x = π^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih, Perm.mul_apply, swap_apply_of_ne_of_ne]
    · exact fun h => ha ((sameCycle_iterate π x n).trans (by rw [h])).symm
    · exact fun h => hb ((sameCycle_iterate π x n).trans (by rw [h])).symm

/-- When the orbits of `a` and `b` differ, `π * swap a b` runs from `a` along the orbit of `b`. -/
lemma iterate_mul_swap_merge (hab : ¬ π.SameCycle a b) :
    ∀ j, 0 < j → j ≤ minimalPeriod π b → (π * swap a b)^[j] a = π^[j] b := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro _ hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [swap_apply_left]
    rw [iterate_succ_apply', ih hj0 (by omega), iterate_succ_apply' (f := π), Perm.mul_apply,
      swap_apply_of_ne_of_ne]
    · intro h; exact hab ((sameCycle_iterate π b j).trans (by rw [h])).symm
    · intro h
      have := iterate_inj (by omega) (period_pos π b) (h.trans (iterate_zero_apply π b).symm)
      omega

lemma sameCycle_mul_swap_of_left (hab : ¬ π.SameCycle a b) {y : α} (hy : π.SameCycle b y) :
    (π * swap a b).SameCycle a y := by
  obtain ⟨r, hr0, hrp, rfl⟩ := exists_iterate_pos hy
  rw [← iterate_mul_swap_merge hab r hr0 hrp]
  exact sameCycle_iterate _ _ _

/-- **Composing with a transposition merges two distinct orbits**: the orbits of
`π * swap a b` are those of `π`, with the orbits of `a` and `b` joined. -/
theorem sameCycle_mul_swap (hab : ¬ π.SameCycle a b) {x y : α} :
    (π * swap a b).SameCycle x y ↔ π.SameCycle x y ∨
      ((π.SameCycle a x ∨ π.SameCycle b x) ∧ (π.SameCycle a y ∨ π.SameCycle b y)) := by
  have hba : ¬ π.SameCycle b a := fun h => hab h.symm
  have hsw : π * swap a b = π * swap b a := by rw [swap_comm]
  -- the joined orbit is one orbit
  have hU : ∀ z, (π.SameCycle a z ∨ π.SameCycle b z) → (π * swap a b).SameCycle a z := by
    rintro z (h | h)
    · have h1 : (π * swap a b).SameCycle b z := hsw ▸ sameCycle_mul_swap_of_left hba h
      exact (sameCycle_mul_swap_of_left hab (Perm.SameCycle.refl _ _)).trans h1
    · exact sameCycle_mul_swap_of_left hab h
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := sameCycle_iff.1 h
    clear h
    induction n with
    | zero => exact Or.inl (Perm.SameCycle.refl _ _)
    | succ n ih =>
      rw [iterate_succ_apply']
      generalize (π * swap a b)^[n] x = z at ih
      rcases ih with h | ⟨hx, hz⟩
      · by_cases hza : z = a
        · subst hza
          refine Or.inr ⟨Or.inl h.symm, Or.inr ?_⟩
          rw [Perm.mul_apply, swap_apply_left]; exact (sameCycle_iterate π b 1)
        by_cases hzb : z = b
        · subst hzb
          refine Or.inr ⟨Or.inr h.symm, Or.inl ?_⟩
          rw [Perm.mul_apply, swap_apply_right]; exact (sameCycle_iterate π a 1)
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hza hzb]
        exact Or.inl (h.trans (sameCycle_iterate π z 1))
      · refine Or.inr ⟨hx, ?_⟩
        rw [Perm.mul_apply]
        by_cases hza : z = a
        · subst hza; rw [swap_apply_left]; exact Or.inr (sameCycle_iterate π b 1)
        by_cases hzb : z = b
        · subst hzb; rw [swap_apply_right]; exact Or.inl (sameCycle_iterate π a 1)
        rw [swap_apply_of_ne_of_ne hza hzb]
        rcases hz with hz | hz
        · exact Or.inl (hz.trans (sameCycle_iterate π z 1))
        · exact Or.inr (hz.trans (sameCycle_iterate π z 1))
  · rintro (h | ⟨hx, hy⟩)
    · by_cases hx : π.SameCycle a x ∨ π.SameCycle b x
      · have hy : π.SameCycle a y ∨ π.SameCycle b y := by
          rcases hx with hx | hx
          · exact Or.inl (hx.trans h)
          · exact Or.inr (hx.trans h)
        exact (hU x hx).symm.trans (hU y hy)
      · push Not at hx
        obtain ⟨n, rfl⟩ := sameCycle_iff.1 h
        rw [← iterate_mul_swap_of hx.1 hx.2 n]
        exact sameCycle_iterate _ _ _
    · exact (hU x hx).symm.trans (hU y hy)

/-- **Merging two orbits decreases the count by one.** -/
theorem nOrb_mul_swap_merge {A : Finset α} (hab : ¬ π.SameCycle a b) (ha : a ∈ A)
    (hb : b ∈ A) : nOrb (π * swap a b) A + 1 = nOrb π A := by
  classical
  have hne : a ≠ b := fun h => hab (h ▸ Perm.SameCycle.refl _ _)
  let inU : α → Prop := fun x => π.SameCycle a x ∨ π.SameCycle b x
  let Ab := A.filter fun x => ¬ inU x
  have hcl : ∀ x ∈ Ab, cls (π * swap a b) x = cls π x := fun x hx => by
    simp only [Ab, mem_filter, inU] at hx
    ext y; simp only [mem_cls, sameCycle_mul_swap hab]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact h
      · exact absurd h hx.2
    · exact Or.inl
  have hAb : Ab.image (cls (π * swap a b)) = Ab.image (cls π) := image_congr hcl
  have e1 : A.image (cls π) = insert (cls π a) (insert (cls π b) (Ab.image (cls π))) := by
    ext z; simp only [mem_image, mem_insert, Ab, mem_filter, inU]
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases h1 : π.SameCycle a x
      · exact Or.inl (cls_eq_iff.2 h1.symm)
      by_cases h2 : π.SameCycle b x
      · exact Or.inr (Or.inl (cls_eq_iff.2 h2.symm))
      exact Or.inr (Or.inr ⟨x, ⟨hx, by tauto⟩, rfl⟩)
    · rintro (rfl | rfl | ⟨x, ⟨hx, -⟩, rfl⟩)
      · exact ⟨a, ha, rfl⟩
      · exact ⟨b, hb, rfl⟩
      · exact ⟨x, hx, rfl⟩
  have e2 : A.image (cls (π * swap a b)) = insert (cls (π * swap a b) a)
      (Ab.image (cls (π * swap a b))) := by
    ext z; simp only [mem_image, mem_insert, Ab, mem_filter, inU]
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases h : π.SameCycle a x ∨ π.SameCycle b x
      · left; apply cls_eq_iff.2
        exact (sameCycle_mul_swap hab).2 (Or.inr ⟨h, Or.inl (Perm.SameCycle.refl _ _)⟩)
      · exact Or.inr ⟨x, ⟨hx, h⟩, rfl⟩
    · rintro (rfl | ⟨x, ⟨hx, -⟩, rfl⟩)
      · exact ⟨a, ha, rfl⟩
      · exact ⟨x, hx, rfl⟩
  have nA : ∀ c, (π.SameCycle a c ∨ π.SameCycle b c) → cls π c ∉ Ab.image (cls π) := by
    intro c hc h
    obtain ⟨x, hx, e⟩ := mem_image.1 h
    simp only [Ab, mem_filter, inU] at hx
    have := cls_eq_iff.1 e
    rcases hc with hc | hc
    · exact hx.2 (Or.inl (hc.trans this.symm))
    · exact hx.2 (Or.inr (hc.trans this.symm))
  have nU : cls (π * swap a b) a ∉ Ab.image (cls π) := by
    intro h
    obtain ⟨x, hx, e⟩ := mem_image.1 h
    simp only [Ab, mem_filter, inU] at hx
    have : a ∈ cls π x := e ▸ mem_cls.2 (Perm.SameCycle.refl _ _)
    exact hx.2 (Or.inl (mem_cls.1 this).symm)
  unfold nOrb
  rw [e1, e2, hAb, card_insert_of_notMem nU, card_insert_of_notMem, card_insert_of_notMem]
  · exact nA b (Or.inr (Perm.SameCycle.refl _ _))
  · rw [mem_insert, not_or]
    exact ⟨fun h => hab (cls_eq_iff.1 h), nA a (Or.inl (Perm.SameCycle.refl _ _))⟩

/-- Composing with a transposition of two elements of one orbit separates them. -/
theorem not_sameCycle_mul_swap (hab : π.SameCycle a b) (hne : a ≠ b) :
    ¬ (π * swap a b).SameCycle a b := by
  obtain ⟨k, hk, hkb⟩ := exists_iterate_lt hab
  generalize hp : minimalPeriod π a = p at hk
  have hp0 : 0 < p := hp ▸ period_pos π a
  have hk0 : k ≠ 0 := by rintro rfl; exact hne hkb
  -- along the arc from `b` back to `a`
  have arc : ∀ j, 0 < j → j ≤ p - k → (π * swap a b)^[j] a = π^[k + j] a := by
    intro j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro _ hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp only [zero_add, iterate_one, Perm.mul_apply, swap_apply_left, ← hkb]
        rw [← iterate_succ_apply' π]
      rw [iterate_succ_apply', ih hj0 (by omega), ← add_assoc, iterate_succ_apply' (f := π),
        Perm.mul_apply, swap_apply_of_ne_of_ne]
      · intro h
        have := iterate_inj (x := a) (by omega) (by omega)
          (h.trans (iterate_zero_apply π a).symm)
        omega
      · intro h
        have := iterate_inj (x := a) (by omega) (by omega) (h.trans hkb.symm)
        omega
  have hper : (π * swap a b)^[p - k] a = a := by
    rw [arc _ (by omega) le_rfl, show k + (p - k) = p by omega, ← hp, iterate_period]
  intro h
  obtain ⟨n, hn⟩ := sameCycle_iff.1 h
  have hq : 0 < p - k := by omega
  have hmod : (π * swap a b)^[n % (p - k)] a = b :=
    (IsPeriodicPt.iterate_mod_apply hper n).trans hn
  rcases Nat.eq_zero_or_pos (n % (p - k)) with h0 | h0
  · rw [h0] at hmod; exact hne hmod
  · rw [arc _ h0 (Nat.mod_lt _ hq).le] at hmod
    have := iterate_inj (x := a) (by have := Nat.mod_lt n hq; omega) (by omega)
      (hmod.trans hkb.symm)
    omega

/-- **Splitting an orbit increases the count by one.** -/
theorem nOrb_mul_swap_split {A : Finset α} (hab : π.SameCycle a b) (hne : a ≠ b) (ha : a ∈ A)
    (hb : b ∈ A) : nOrb (π * swap a b) A = nOrb π A + 1 := by
  have := nOrb_mul_swap_merge (π := π * swap a b) (not_sameCycle_mul_swap hab hne) ha hb
  rwa [mul_assoc, swap_mul_self, mul_one, eq_comm] at this

end Swap

/-! ### First returns -/

section Ret

variable (π : Perm α) (A : Finset α)

lemma ret_ex (x : α) : ∃ n, 0 < n ∧ (x ∈ A → π^[n] x ∈ A) :=
  ⟨minimalPeriod π x, period_pos π x, fun h => by rw [iterate_period]; exact h⟩

/-- The number of steps to the first return to `A`. -/
def retIdx (x : α) : ℕ := Nat.find (ret_ex π A x)

/-- The first return to `A` (the identity outside `A`). -/
def retFun (x : α) : α := if x ∈ A then π^[retIdx π A x] x else x

variable {π A}

lemma retIdx_pos (x : α) : 0 < retIdx π A x := (Nat.find_spec (ret_ex π A x)).1

lemma iterate_retIdx_mem {x : α} (hx : x ∈ A) : π^[retIdx π A x] x ∈ A :=
  (Nat.find_spec (ret_ex π A x)).2 hx

lemma not_mem_of_lt_retIdx {x : α} (_hx : x ∈ A) {m : ℕ} (hm0 : 0 < m) (hm : m < retIdx π A x) :
    π^[m] x ∉ A := fun h => Nat.find_min (ret_ex π A x) hm ⟨hm0, fun _ => h⟩

lemma retIdx_le {x : α} (_hx : x ∈ A) {m : ℕ} (hm0 : 0 < m) (hm : π^[m] x ∈ A) :
    retIdx π A x ≤ m := Nat.find_min' _ ⟨hm0, fun _ => hm⟩

lemma retFun_injective : Injective (retFun π A) := by
  -- if `π^[n] x = π^[m] y` with `n ≤ m` minimal, then `x = π^[m - n] y` returns earlier
  have key : ∀ x y, x ∈ A → y ∈ A → retIdx π A x ≤ retIdx π A y →
      π^[retIdx π A x] x = π^[retIdx π A y] y → x = y := by
    intro x y hx hy hle h
    have e : π^[retIdx π A y - retIdx π A x] y = x := by
      apply π.injective.iterate (retIdx π A x)
      rw [← iterate_add_apply, Nat.add_sub_cancel' hle, h]
    by_contra hne
    have h0 : 0 < retIdx π A y - retIdx π A x := by
      rcases Nat.eq_zero_or_pos (retIdx π A y - retIdx π A x) with h0 | h0
      · rw [h0] at e; exact absurd e.symm hne
      · exact h0
    exact not_mem_of_lt_retIdx hy h0 (by have := retIdx_pos (π := π) (A := A) x; omega)
      (e ▸ hx)
  intro x y h
  unfold retFun at h
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp only [hx, hy, ite_true, ite_false] at h
  · rcases le_total (retIdx π A x) (retIdx π A y) with hle | hle
    · exact key x y hx hy hle h
    · exact (key y x hy hx hle h.symm).symm
  · exact absurd (h ▸ iterate_retIdx_mem hx) hy
  · exact absurd (h ▸ iterate_retIdx_mem hy) hx
  · exact h

variable (π A) in
/-- **The first return to `A`**: on `A`, the first element of `A` after `x` along the orbit of
`x`; outside `A`, the identity. -/
noncomputable def ret : Perm α :=
  Equiv.ofBijective (retFun π A) (Finite.injective_iff_bijective.1 retFun_injective)

lemma ret_apply_of_mem {x : α} (hx : x ∈ A) : ret π A x = π^[retIdx π A x] x := by
  simp [ret, retFun, hx]

lemma ret_apply_of_not_mem {x : α} (hx : x ∉ A) : ret π A x = x := by
  simp [ret, retFun, hx]

lemma ret_mem {x : α} (hx : x ∈ A) : ret π A x ∈ A := by
  rw [ret_apply_of_mem hx]; exact iterate_retIdx_mem hx

lemma ret_mem_iff {x : α} : ret π A x ∈ A ↔ x ∈ A := by
  by_cases hx : x ∈ A
  · exact iff_of_true (ret_mem hx) hx
  · rw [ret_apply_of_not_mem hx]

/-- The first return is characterized by its index. -/
lemma ret_eq_of {x : α} (hx : x ∈ A) {n : ℕ} (hn0 : 0 < n) (hn : π^[n] x ∈ A)
    (hmin : ∀ m, 0 < m → m < n → π^[m] x ∉ A) : ret π A x = π^[n] x := by
  have h1 := retIdx_le hx hn0 hn
  have h2 : ¬ retIdx π A x < n := fun h =>
    hmin _ (retIdx_pos x) h (iterate_retIdx_mem hx)
  rw [ret_apply_of_mem hx, show retIdx π A x = n by omega]

/-- A step of the first return is a step of `π` when it lands in `A`. -/
lemma ret_eq_self_of {x : α} (hx : x ∈ A) (h : π x ∈ A) : ret π A x = π x := by
  rw [ret_eq_of hx one_pos (by simpa using h) (fun m h0 h1 => by omega)]; rfl

lemma ret_iterate_eq (x : α) (j : ℕ) : ∃ N, (ret π A)^[j] x = π^[N] x := by
  induction j with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    obtain ⟨N, hN⟩ := ih
    rw [iterate_succ_apply', hN]
    by_cases h : π^[N] x ∈ A
    · rw [ret_apply_of_mem h, ← iterate_add_apply]; exact ⟨_, rfl⟩
    · rw [ret_apply_of_not_mem h]; exact ⟨N, rfl⟩

/-- Every element of `A` along the orbit of `x ∈ A` is reached by the first return, after
elements reached earlier along the orbit. -/
lemma ret_reach : ∀ (N : ℕ) (x : α), x ∈ A → π^[N] x ∈ A →
    ∃ j, (ret π A)^[j] x = π^[N] x ∧ ∀ i < j, ∃ N' < N, (ret π A)^[i] x = π^[N'] x := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro x hx hN
    rcases Nat.eq_zero_or_pos N with rfl | hN0
    · exact ⟨0, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    have hr := retIdx_le hx hN0 hN
    have hr0 := retIdx_pos (π := π) (A := A) x
    have e : π^[N] x = π^[N - retIdx π A x] (ret π A x) := by
      rw [ret_apply_of_mem hx, ← iterate_add_apply, Nat.sub_add_cancel hr]
    obtain ⟨j, hj, hlt⟩ := ih (N - retIdx π A x) (by omega) _ (ret_mem hx) (e ▸ hN)
    refine ⟨j + 1, by rw [iterate_succ_apply, hj, ← e], fun i hi => ?_⟩
    rcases i with _ | i
    · exact ⟨0, hN0, rfl⟩
    · obtain ⟨N', hN', h'⟩ := hlt i (by omega)
      refine ⟨N' + retIdx π A x, by omega, ?_⟩
      rw [iterate_succ_apply, h', ret_apply_of_mem hx, ← iterate_add_apply]

/-- **The orbits of the first return** are the orbits of `π` cut down to `A`. -/
theorem sameCycle_ret {x y : α} (hx : x ∈ A) (hy : y ∈ A) :
    (ret π A).SameCycle x y ↔ π.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨j, rfl⟩ := sameCycle_iff.1 h
    obtain ⟨N, hN⟩ := ret_iterate_eq (π := π) (A := A) x j
    rw [hN]; exact sameCycle_iterate _ _ _
  · intro h
    obtain ⟨N, rfl⟩ := sameCycle_iff.1 h
    obtain ⟨j, hj, -⟩ := ret_reach N x hx hy
    rw [← hj]; exact sameCycle_iterate _ _ _

theorem nOrb_ret : nOrb (ret π A) A = nOrb π A :=
  nOrb_congr fun _ hx _ hy => sameCycle_ret hx hy

lemma nOrb_ret_of_subset {B : Finset α} (hB : B ⊆ A) : nOrb (ret π A) B = nOrb π B :=
  nOrb_congr fun _ hx _ hy => sameCycle_ret (hB hx) (hB hy)

/-- **First returns compose.** -/
theorem ret_ret {B : Finset α} (hB : B ⊆ A) : ret (ret π A) B = ret π B := by
  ext x
  by_cases hx : x ∈ B
  swap
  · rw [ret_apply_of_not_mem hx, ret_apply_of_not_mem hx]
  have hxA := hB hx
  generalize hn : retIdx π B x = n
  have hn0 : 0 < n := hn ▸ retIdx_pos x
  have hy : π^[n] x ∈ B := hn ▸ iterate_retIdx_mem hx
  have hmin : ∀ m, 0 < m → m < n → π^[m] x ∉ B := fun m h0 h1 =>
    not_mem_of_lt_retIdx hx h0 (hn ▸ h1)
  rw [ret_apply_of_mem (π := π) (A := B) hx, hn]
  have hr := retIdx_le hxA hn0 (hB hy)
  have hr0 := retIdx_pos (π := π) (A := A) x
  have e : π^[n] x = π^[n - retIdx π A x] (ret π A x) := by
    rw [ret_apply_of_mem hxA, ← iterate_add_apply, Nat.sub_add_cancel hr]
  obtain ⟨j, hj, hlt⟩ := ret_reach (n - retIdx π A x) _ (ret_mem hxA) (e ▸ hB hy)
  rw [ret_eq_of hx (n := j + 1) (by omega) ?_ ?_, iterate_succ_apply, hj, ← e]
  · rw [iterate_succ_apply, hj, ← e]; exact hy
  · intro m hm0 hm
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    obtain ⟨N', hN', h'⟩ := hlt i (by omega)
    rw [iterate_succ_apply, h', ret_apply_of_mem hxA, ← iterate_add_apply]
    exact hmin _ (by omega) (by omega)

lemma ret_univ : ret π univ = π := by
  ext x
  rw [ret_eq_self_of (mem_univ x) (mem_univ _)]

end Ret

end Orbit

end PlanarFlow
