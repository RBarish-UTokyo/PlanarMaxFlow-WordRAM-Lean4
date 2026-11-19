module

public import PlanarFlow.Plane.Orbit

/-!
# Deleting and contracting edges of a map: Euler's formula by counting orbits

A combinatorial map on a finite set of darts is given by the reversal `ι` (an involution without
fixed points) and the rotation `σ` around the vertices; the boundary walk of the faces is
`σ * ι` (`x ↦ σ (ι x)`). The vertices are the orbits of `σ`, the faces those of `σ * ι`, and two
darts are connected when a chain of steps `x ↦ σ x`, `x ↦ ι x` leads from one to the other
(`Conn`).

Here a *submap* is a set `A` of darts closed under `ι` with a rotation `σ` mapping `A` into
itself (`Stable`). Deleting the edges outside `B ⊆ A` replaces the rotation by its first return
to `B` (`PlanarFlow.Orbit.ret σ B`); contracting them is deleting them in the dual map, whose
rotation is the face walk `σ * ι` (`con`).

The **Euler gap** of a submap (`gap`) is `2 (V + F) - |A| - 4 c`, with `V` and `F` the
numbers of vertices and faces and `c` the number of connected components: twice
`V - E + F - 2 c`. It is `0` exactly when every component satisfies Euler's formula
`V + F = E + 2`.

## Main results

* `gap_le_erase`: **deleting one edge does not decrease the gap.** The two darts of the
  edge lie on two distinct faces, which merge, or on one face, which splits
  (`PlanarFlow.Orbit.nOrb_mul_swap_merge`, `PlanarFlow.Orbit.nOrb_mul_swap_split`: the new face
  walk is the old one composed with the transposition of the two darts, then cut down to the
  remaining darts); a vertex disappears exactly when the edge is pendant or an isolated loop; and
  the component of the edge splits into at most as many components as the edge has remaining
  neighbours, which are connected when the two faces differ.
* `gap_le_ret`, `gap_nonpos`: deleting any set of edges does not decrease the gap, and
  the gap is never positive (**Euler's inequality** `V - E + F ≤ 2 c`, by deleting all the
  edges).
* `gap_ret_eq_zero`, `gap_con_eq_zero`: **deleting or contracting any set of edges of a
  submap whose components satisfy Euler's formula gives a submap whose components satisfy it.**
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Orbit

open Finset Function Equiv Relation

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Stable sets -/

/-- `π` maps `A` into itself. -/
def Stable (π : Perm α) (A : Finset α) : Prop := ∀ x ∈ A, π x ∈ A

lemma Stable.iterate {π : Perm α} {A : Finset α} (h : Stable π A) {x : α} (hx : x ∈ A) :
    ∀ n, π^[n] x ∈ A
  | 0 => hx
  | n + 1 => by rw [iterate_succ_apply']; exact h _ (h.iterate hx n)

lemma Stable.of_sameCycle {π : Perm α} {A : Finset α} (h : Stable π A) {x y : α} (hx : x ∈ A)
    (hxy : π.SameCycle x y) : y ∈ A := by
  obtain ⟨n, rfl⟩ := sameCycle_iff.1 hxy; exact h.iterate hx n

lemma stable_ret (π : Perm α) (A : Finset α) : Stable (ret π A) A := fun _ hx => ret_mem hx

lemma Stable.mul {π π' : Perm α} {A : Finset α} (h : Stable π A) (h' : Stable π' A) :
    Stable (π * π') A := fun x hx => h _ (h' x hx)

/-- Two permutations agreeing on a stable set have the same iterates from it. -/
lemma iterate_congr {π π' : Perm α} {A : Finset α} (hS : Stable π A)
    (h : ∀ z ∈ A, π z = π' z) {x : α} (hx : x ∈ A) : ∀ n, π^[n] x = π'^[n] x
  | 0 => rfl
  | n + 1 => by
    rw [iterate_succ_apply', iterate_succ_apply', ← iterate_congr hS h hx n,
      h _ (hS.iterate hx n)]

lemma sameCycle_congr {π π' : Perm α} {A : Finset α} (hS : Stable π A)
    (h : ∀ z ∈ A, π z = π' z) {x y : α} (hx : x ∈ A) : π.SameCycle x y ↔ π'.SameCycle x y := by
  simp only [sameCycle_iff, iterate_congr hS h hx]

lemma nOrb_congr_of_eq {π π' : Perm α} {A : Finset α} (hS : Stable π A)
    (h : ∀ z ∈ A, π z = π' z) : nOrb π A = nOrb π' A :=
  nOrb_congr fun _ hx _ _ => sameCycle_congr hS h hx

/-! ### Connectivity -/

section Conn

variable (ι : Perm α)

/-- One step in a map: along the rotation, or to the reverse dart. -/
def Step (σ : Perm α) (x y : α) : Prop := y = σ x ∨ y = ι x

/-- Two darts are connected by steps along the rotation and the reversal. -/
def Conn (σ : Perm α) : α → α → Prop := ReflTransGen (Step ι σ)

/-- The connected component of a dart. -/
noncomputable def ccls (σ : Perm α) (x : α) : Finset α := by
  classical exact univ.filter (Conn ι σ x)

/-- The number of connected components meeting `A`. -/
noncomputable def comp (σ : Perm α) (A : Finset α) : ℕ := (A.image (ccls ι σ)).card

/-- The number of vertices and faces meeting `A`. -/
noncomputable def eul (σ : Perm α) (A : Finset α) : ℕ := nOrb σ A + nOrb (σ * ι) A

/-- **The Euler gap** `2 (V + F) - |A| - 4 c`: zero when every component satisfies Euler's
formula. -/
noncomputable def gap (σ : Perm α) (A : Finset α) : ℤ :=
  2 * (eul ι σ A : ℤ) - A.card - 4 * (comp ι σ A : ℤ)

/-- The reversal: an involution without fixed points. -/
structure IsInv : Prop where
  invol : ∀ x, ι (ι x) = x
  ne : ∀ x, ι x ≠ x

variable {ι}

lemma IsInv.mul_self (hι : IsInv ι) : ι * ι = 1 := by
  ext x; exact hι.invol x

lemma conn_iterate (σ : Perm α) (x : α) : ∀ n, Conn ι σ x (σ^[n] x)
  | 0 => .refl
  | n + 1 => by rw [iterate_succ_apply']; exact .tail (conn_iterate σ x n) (Or.inl rfl)

lemma conn_of_sameCycle {σ : Perm α} {x y : α} (h : σ.SameCycle x y) : Conn ι σ x y := by
  obtain ⟨n, rfl⟩ := sameCycle_iff.1 h; exact conn_iterate σ x n

lemma conn_inv {σ : Perm α} (x : α) : Conn ι σ x (ι x) := .single (Or.inr rfl)

lemma conn_symm (hι : IsInv ι) {σ : Perm α} {x y : α} (h : Conn ι σ x y) : Conn ι σ y x := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih =>
    rename_i b c _
    refine ReflTransGen.trans ?_ ih
    rcases hst with rfl | rfl
    · have := conn_iterate (ι := ι) σ (σ b) (minimalPeriod σ b - 1)
      rw [← iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel (period_pos σ b),
        iterate_period] at this
      exact this
    · have := conn_inv (ι := ι) (σ := σ) (ι b); rwa [hι.invol] at this

lemma mem_ccls {σ : Perm α} {x y : α} : y ∈ ccls ι σ x ↔ Conn ι σ x y := by
  classical simp [ccls]

lemma ccls_eq_iff (hι : IsInv ι) {σ : Perm α} {x y : α} :
    ccls ι σ x = ccls ι σ y ↔ Conn ι σ x y := by
  constructor
  · intro h
    have : y ∈ ccls ι σ x := h ▸ mem_ccls.2 .refl
    exact mem_ccls.1 this
  · intro h
    ext z; simp only [mem_ccls]
    exact ⟨fun h' => (conn_symm hι h).trans h', fun h' => h.trans h'⟩

/-- The dual map has the same connected components. -/
lemma conn_mul_iff (hι : IsInv ι) {σ : Perm α} {x y : α} :
    Conn ι (σ * ι) x y ↔ Conn ι σ x y := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hst ih =>
      rcases hst with rfl | rfl
      · exact ih.trans ((conn_inv _).trans (.single (Or.inl rfl)))
      · exact ih.tail (Or.inr rfl)
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hst ih =>
      rename_i b c _
      rcases hst with rfl | rfl
      · refine ih.trans ((conn_inv b).trans (.single (Or.inl ?_)))
        rw [Perm.mul_apply, hι.invol]
      · exact ih.tail (Or.inr rfl)

lemma Stable.of_conn {σ : Perm α} {A : Finset α} (hσ : Stable σ A) (hA : Stable ι A) {x y : α}
    (hx : x ∈ A) (h : Conn ι σ x y) : y ∈ A := by
  induction h with
  | refl => exact hx
  | tail _ hst ih => rcases hst with rfl | rfl; exacts [hσ _ ih, hA _ ih]

lemma conn_ret_le {σ : Perm α} {B : Finset α} {x y : α} (h : Conn ι (ret σ B) x y) :
    Conn ι σ x y := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih =>
    rename_i b c _
    rcases hst with rfl | rfl
    · by_cases hb : b ∈ B
      · rw [ret_apply_of_mem hb]; exact ih.trans (conn_iterate σ b _)
      · rw [ret_apply_of_not_mem hb]; exact ih
    · exact ih.tail (Or.inr rfl)

lemma conn_congr {σ σ' : Perm α} {A : Finset α} (hσ : Stable σ A) (hA : Stable ι A)
    (h : ∀ z ∈ A, σ z = σ' z) {x y : α} (hx : x ∈ A) (hxy : Conn ι σ x y) : Conn ι σ' x y := by
  have key : ∀ y, Conn ι σ x y → y ∈ A ∧ Conn ι σ' x y := by
    intro y hxy
    induction hxy with
    | refl => exact ⟨hx, .refl⟩
    | tail _ hst ih =>
      rename_i b c _
      rcases hst with rfl | rfl
      · exact ⟨hσ _ ih.1, ih.2.tail (Or.inl (h b ih.1))⟩
      · exact ⟨hA _ ih.1, ih.2.tail (Or.inr rfl)⟩
  exact (key y hxy).2

lemma comp_congr (hι : IsInv ι) {σ σ' : Perm α} {A : Finset α} (hσ : Stable σ A)
    (hA : Stable ι A) (h : ∀ z ∈ A, σ z = σ' z) : comp ι σ A = comp ι σ' A := by
  have hσ' : Stable σ' A := fun x hx => h x hx ▸ hσ x hx
  have h' : ∀ z ∈ A, σ' z = σ z := fun z hz => (h z hz).symm
  exact le_antisymm
    (card_image_le_of_fiber fun x hx y _ e => (ccls_eq_iff hι).2
      (conn_congr hσ' hA h' hx ((ccls_eq_iff hι).1 e)))
    (card_image_le_of_fiber fun x hx y _ e => (ccls_eq_iff hι).2
      (conn_congr hσ hA h hx ((ccls_eq_iff hι).1 e)))

/-- The gap depends only on the rotation on `A`. -/
lemma gap_congr (hι : IsInv ι) {σ σ' : Perm α} {A : Finset α} (hσ : Stable σ A)
    (hA : Stable ι A) (h : ∀ z ∈ A, σ z = σ' z) : gap ι σ A = gap ι σ' A := by
  have h1 := nOrb_congr_of_eq hσ h
  have h2 := nOrb_congr_of_eq (π := σ * ι) (π' := σ' * ι) (hσ.mul hA)
    (fun z hz => by simp only [Perm.mul_apply]; exact h _ (hA z hz))
  unfold gap eul
  rw [h1, h2, comp_congr hι hσ hA h]

/-- **The gap of the dual map** is the gap of the map. -/
lemma gap_mul (hι : IsInv ι) (σ : Perm α) (A : Finset α) :
    gap ι (σ * ι) A = gap ι σ A := by
  have h1 : σ * ι * ι = σ := by rw [mul_assoc, hι.mul_self, mul_one]
  have h2 : comp ι (σ * ι) A = comp ι σ A := by
    unfold comp ccls
    congr 1
    refine image_congr fun x _ => ?_
    ext y; simp [conn_mul_iff hι]
  unfold gap eul
  rw [h1, h2]; omega

lemma gap_empty (σ : Perm α) : gap ι σ ∅ = 0 := by
  simp [gap, eul, comp, nOrb_empty]

end Conn

/-! ### Deleting one edge -/

section Erase

variable {ι : Perm α} (hι : IsInv ι) {σ : Perm α} {A : Finset α} (hσ : Stable σ A)
  (hA : Stable ι A) {d : α} (hd : d ∈ A)
include hι hσ hA hd

omit hσ in
lemma mem_erase_pair {x : α} : x ∈ (A.erase d).erase (ι d) ↔ x ≠ ι d ∧ x ≠ d ∧ x ∈ A := by
  simp only [mem_erase]

omit hσ in
lemma eq_of_not_mem_erase_pair {x : α} (hx : x ∈ A) (h : x ∉ (A.erase d).erase (ι d)) :
    x = d ∨ x = ι d := by
  rw [mem_erase_pair hι hA hd] at h; tauto

omit hσ in
lemma stable_erase_pair : Stable ι ((A.erase d).erase (ι d)) := by
  intro x hx
  rw [mem_erase_pair hι hA hd] at hx ⊢
  refine ⟨fun h => hx.2.1 ?_, fun h => hx.1 ?_, hA _ hx.2.2⟩
  · rw [← hι.invol x, h, hι.invol]
  · rw [← hι.invol x, h]

omit hσ in
lemma card_erase_pair : ((A.erase d).erase (ι d)).card + 2 = A.card := by
  have h1 : ι d ∈ A.erase d := mem_erase.2 ⟨hι.ne d, hA d hd⟩
  rw [card_erase_of_mem h1, card_erase_of_mem hd]
  have : 2 ≤ A.card := by
    rw [← card_pair (hι.ne d).symm]
    exact card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hd, hA _ hd])
  omega

/-- The number of orbits lost by removing the two darts of an edge, in terms of the images of the
two darts. -/
def loss (d d' a b : α) : ℕ :=
  if a = d ∧ b = d' then 2 else if a = d ∨ b = d' ∨ (a = d' ∧ b = d) then 1 else 0

omit hσ in
lemma nOrb_erase_pair (π : Perm α) (hπ : Stable π A) :
    nOrb π ((A.erase d).erase (ι d)) + loss d (ι d) (π d) (π (ι d)) = nOrb π A := by
  have hne : ι d ≠ d := hι.ne d
  have hd' : ι d ∈ A.erase d := mem_erase.2 ⟨hne, hA d hd⟩
  have fix : ∀ x, π x = x → ∀ y, π.SameCycle x y → y = x := fun x hx y h => by
    obtain ⟨n, rfl⟩ := sameCycle_iff.1 h; exact iterate_fixed hx n
  -- the first dart
  have s1 : nOrb π (A.erase d) + (if π d = d then 1 else 0) = nOrb π A := by
    split_ifs with h
    · exact nOrb_erase_alone hd fun y _ => fix d h y
    · rw [nOrb_erase_of (hπ d hd) h (sameCycle_iterate π d 1), add_zero]
  -- the second dart
  have s2 : nOrb π ((A.erase d).erase (ι d)) +
      (if π (ι d) = ι d ∨ (π (ι d) = d ∧ π d = ι d) then 1 else 0) = nOrb π (A.erase d) := by
    split_ifs with h
    · rcases h with h | ⟨h1, h2⟩
      · exact nOrb_erase_alone hd' fun y _ => fix _ h y
      · refine nOrb_erase_alone hd' fun y hy hsc => ?_
        have hS : Stable π {d, ι d} := by
          intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢
          rcases hx with rfl | rfl
          · exact Or.inr h2
          · exact Or.inl h1
        have := hS.of_sameCycle (by simp) hsc
        simp only [mem_insert, mem_singleton] at this
        rcases this with rfl | rfl
        · exact absurd rfl (mem_erase.1 hy).1
        · rfl
    · push Not at h
      rw [add_zero]
      by_cases h3 : π (ι d) = d
      · have h4 : π d ≠ ι d := h.2 h3
        have h5 : π d ≠ d := fun e => hne (π.injective (h3.trans e.symm))
        refine nOrb_erase_of (y := π d) (mem_erase.2 ⟨h5, hπ d hd⟩) h4 ?_
        have := sameCycle_iterate π (ι d) 2
        simp only [iterate_succ, comp_apply, iterate_zero, id_eq, h3] at this
        exact this
      · exact nOrb_erase_of (y := π (ι d)) (mem_erase.2 ⟨h3, hπ _ (hA d hd)⟩) h.1
          (sameCycle_iterate π (ι d) 1)
  rw [← s1, ← s2, add_assoc]
  congr 1
  unfold loss
  by_cases a : π d = d <;> by_cases b : π (ι d) = ι d
  · simp [a, b]
  · have : π (ι d) ≠ d := fun e => hne (π.injective (e.trans a.symm))
    simp [a, b, this, Ne.symm hne]
  · simp [a, b]
  · by_cases c : π (ι d) = d ∧ π d = ι d
    · simp [c.1, c.2, hne]
    · simp only [a, b, false_and, false_or, ite_false]
      split_ifs <;> tauto

/-- The face walk after deleting the edge: the face walk composed with the transposition of its
two darts, then cut down to the remaining darts. -/
lemma ret_mul_eq {x : α} (hx : x ∈ (A.erase d).erase (ι d)) :
    (ret σ ((A.erase d).erase (ι d)) * ι) x =
      ret (σ * ι * swap d (ι d)) ((A.erase d).erase (ι d)) x := by
  generalize hA' : (A.erase d).erase (ι d) = A' at hx
  have mA : ∀ {z}, z ∈ A' ↔ z ≠ ι d ∧ z ≠ d ∧ z ∈ A := fun {z} => by
    rw [← hA', mem_erase_pair hι hA hd]
  have hix : ι x ∈ A' := hA' ▸ stable_erase_pair hι hA hd x (hA' ▸ hx)
  have hxe : x ≠ d ∧ x ≠ ι d := ⟨(mA.1 hx).2.1, (mA.1 hx).1⟩
  have hψe : ∀ z, z = d ∨ z = ι d → (σ * ι * swap d (ι d)) z = σ z := by
    rintro z (rfl | rfl)
    · simp [Perm.mul_apply, swap_apply_left, hι.invol]
    · simp [Perm.mul_apply, swap_apply_right]
  rw [Perm.mul_apply, ret_apply_of_mem hix]
  generalize hn : retIdx σ A' (ι x) = n
  have hn0 : 0 < n := hn ▸ retIdx_pos _
  have hnA : σ^[n] (ι x) ∈ A' := hn ▸ iterate_retIdx_mem hix
  have hmin : ∀ m, 0 < m → m < n → σ^[m] (ι x) ∉ A' := fun m h0 h1 =>
    not_mem_of_lt_retIdx hix h0 (hn ▸ h1)
  have key : ∀ j, 0 < j → j ≤ n → (σ * ι * swap d (ι d))^[j] x = σ^[j] (ι x) := by
    intro j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro _ hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp [swap_apply_of_ne_of_ne hxe.1 hxe.2]
      rw [iterate_succ_apply', ih hj0 (by omega), iterate_succ_apply']
      have hz : σ^[j] (ι x) ∈ A := hσ.iterate (mA.1 hix).2.2 j
      have hz' := hmin j hj0 (by omega)
      exact hψe _ (by rw [mA] at hz'; tauto)
  rw [ret_eq_of hx hn0 (by rw [key n hn0 le_rfl]; exact hnA)
    (fun m h0 h1 => by rw [key m h0 h1.le]; exact hmin m h0 h1), key n hn0 le_rfl]

/-- The number of vertices and faces after deleting the edge. -/
lemma eul_erase :
    eul ι (ret σ ((A.erase d).erase (ι d))) ((A.erase d).erase (ι d)) =
      nOrb σ ((A.erase d).erase (ι d)) +
        nOrb (σ * ι * swap d (ι d)) ((A.erase d).erase (ι d)) := by
  unfold eul
  rw [nOrb_ret]
  congr 1
  rw [nOrb_congr_of_eq (π' := ret (σ * ι * swap d (ι d)) ((A.erase d).erase (ι d)))
    ((stable_ret _ _).mul (stable_erase_pair hι hA hd)) (fun z hz => ret_mul_eq hι hσ hA hd hz),
    nOrb_ret]

/-- **Rerouting around the deleted edge**: a chain of steps from a remaining dart either stays
among the remaining darts, or reaches a remaining dart whose rotation is a dart of the edge. -/
lemma conn_erase_route {x y : α} (hx : x ∈ (A.erase d).erase (ι d)) (h : Conn ι σ x y) :
    (y ∈ (A.erase d).erase (ι d) ∧ Conn ι (ret σ ((A.erase d).erase (ι d))) x y) ∨
      ∃ w ∈ (A.erase d).erase (ι d), Conn ι (ret σ ((A.erase d).erase (ι d))) x w ∧
        (σ w = d ∨ σ w = ι d) := by
  generalize hA' : (A.erase d).erase (ι d) = A' at hx ⊢
  have hι' : Stable ι A' := hA' ▸ stable_erase_pair hι hA hd
  have mA : ∀ {z}, z ∈ A' → z ∈ A := fun {z} hz => by
    rw [← hA', mem_erase_pair hι hA hd] at hz; exact hz.2.2
  have nA : ∀ {z}, z ∈ A → z ∉ A' → z = d ∨ z = ι d := fun {z} hz h =>
    eq_of_not_mem_erase_pair hι hA hd hz (hA' ▸ h)
  induction h with
  | refl => exact Or.inl ⟨hx, .refl⟩
  | tail _ hst ih =>
    rename_i b c _
    rcases ih with ⟨hb, hc⟩ | hw
    · rcases hst with rfl | rfl
      · by_cases h' : σ b ∈ A'
        · exact Or.inl ⟨h', hc.tail (Or.inl (ret_eq_self_of hb h').symm)⟩
        · exact Or.inr ⟨b, hb, hc, nA (hσ _ (mA hb)) h'⟩
      · exact Or.inl ⟨hι' _ hb, hc.tail (Or.inr rfl)⟩
    · exact Or.inr hw

/-- **The components after deleting the edge**: the component of the edge splits into at most
as many components as the remaining darts `W` whose rotation is a dart of the edge. -/
lemma comp_erase_le :
    comp ι (ret σ ((A.erase d).erase (ι d))) ((A.erase d).erase (ι d)) + 1 ≤
      comp ι σ A + ((({σ.symm d, σ.symm (ι d)} : Finset α).filter
        (· ∈ (A.erase d).erase (ι d))).image (ccls ι (ret σ ((A.erase d).erase (ι d))))).card := by
  classical
  generalize hA' : (A.erase d).erase (ι d) = A'
  have route : ∀ {x y}, x ∈ A' → Conn ι σ x y → (y ∈ A' ∧ Conn ι (ret σ A') x y) ∨
      ∃ w ∈ A', Conn ι (ret σ A') x w ∧ (σ w = d ∨ σ w = ι d) := fun {x y} hx h => by
    have := conn_erase_route hι hσ hA hd (hA' ▸ hx) h; rwa [hA'] at this
  have mA : ∀ {z}, z ∈ A' → z ∈ A := fun {z} hz => by
    rw [← hA', mem_erase_pair hι hA hd] at hz; exact hz.2.2
  have hdA' : d ∉ A' := by rw [← hA', mem_erase_pair hι hA hd]; tauto
  have toD : ∀ {w}, (σ w = d ∨ σ w = ι d) → Conn ι σ w d := fun {w} h => by
    have h1 : Conn ι σ w (σ w) := .single (Or.inl rfl)
    have h2 : Conn ι σ (σ w) (ι (σ w)) := conn_inv _
    rcases h with h | h
    · rwa [h] at h1
    · rw [h, hι.invol] at h2; rw [h] at h1; exact h1.trans h2
  set W := ({σ.symm d, σ.symm (ι d)} : Finset α).filter (· ∈ A')
  let Ain := A'.filter (Conn ι σ · d)
  let Aout := A'.filter (fun x => ¬ Conn ι σ x d)
  have hsplit : A' = Ain ∪ Aout := (filter_union_filter_not_eq _ _).symm
  have h1 : Ain.image (ccls ι (ret σ A')) ⊆ W.image (ccls ι (ret σ A')) := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
    simp only [Ain, mem_filter] at hx
    rcases route hx.1 hx.2 with ⟨h, -⟩ | ⟨w, hw, hxw, hσw⟩
    · exact absurd h hdA'
    · refine mem_image.2 ⟨w, ?_, ((ccls_eq_iff hι).2 hxw).symm⟩
      simp only [W, mem_filter, mem_insert, mem_singleton]
      refine ⟨?_, hw⟩
      rcases hσw with h | h
      · exact Or.inl ((Equiv.eq_symm_apply σ).2 h)
      · exact Or.inr ((Equiv.eq_symm_apply σ).2 h)
  have h2 : (Aout.image (ccls ι (ret σ A'))).card ≤ (Aout.image (ccls ι σ)).card := by
    refine card_image_le_of_fiber fun x hx y hy e => (ccls_eq_iff hι).2 ?_
    simp only [Aout, mem_filter] at hx hy
    rcases route hx.1 ((ccls_eq_iff hι).1 e) with ⟨-, h⟩ | ⟨w, -, hxw, hσw⟩
    · exact h
    · exact absurd ((conn_ret_le hxw).trans (toD hσw)) hx.2
  have h3 : (Aout.image (ccls ι σ)).card + 1 ≤ comp ι σ A := by
    have hsub : Aout.image (ccls ι σ) ⊆ (A.image (ccls ι σ)).erase (ccls ι σ d) := by
      intro c hc
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
      simp only [Aout, mem_filter] at hx
      refine mem_erase.2 ⟨fun e => hx.2 ((ccls_eq_iff hι).1 e), mem_image_of_mem _ (mA hx.1)⟩
    have c1 := card_le_card hsub
    rw [card_erase_of_mem (mem_image_of_mem _ hd)] at c1
    have c2 : 0 < (A.image (ccls ι σ)).card := card_pos.2 ⟨_, mem_image_of_mem _ hd⟩
    unfold comp; omega
  have h4 : comp ι (ret σ A') A' ≤
      (Ain.image (ccls ι (ret σ A'))).card + (Aout.image (ccls ι (ret σ A'))).card := by
    unfold comp
    have : A'.image (ccls ι (ret σ A')) =
        Ain.image (ccls ι (ret σ A')) ∪ Aout.image (ccls ι (ret σ A')) := by
      rw [← image_union, ← hsplit]
    rw [this]
    exact card_union_le _ _
  have := card_le_card h1
  omega

/-- When the two darts of the edge lie on distinct faces, the remaining neighbours of the edge are
connected after the deletion (along the merged face). -/
lemma conn_erase_of_face (hf : ¬ (σ * ι).SameCycle d (ι d)) {w₁ w₂ : α}
    (h₁ : w₁ ∈ (A.erase d).erase (ι d)) (h₂ : w₂ ∈ (A.erase d).erase (ι d)) (e₁ : σ w₁ = d)
    (e₂ : σ w₂ = ι d) : Conn ι (ret σ ((A.erase d).erase (ι d))) w₁ w₂ := by
  have hS := stable_erase_pair hι hA hd
  have i₁ := hS _ h₁
  have i₂ := hS _ h₂
  have f₁ : (σ * ι).SameCycle d (ι w₁) := by
    have := sameCycle_iterate (σ * ι) (ι w₁) 1
    simp only [iterate_one, Perm.mul_apply, hι.invol, e₁] at this
    exact this.symm
  have f₂ : (σ * ι).SameCycle (ι d) (ι w₂) := by
    have := sameCycle_iterate (σ * ι) (ι w₂) 1
    simp only [iterate_one, Perm.mul_apply, hι.invol, e₂] at this
    exact this.symm
  have hψ : (σ * ι * swap d (ι d)).SameCycle (ι w₁) (ι w₂) :=
    (sameCycle_mul_swap hf).2 (Or.inr ⟨Or.inl f₁, Or.inr f₂⟩)
  have hr := (sameCycle_ret i₁ i₂).2 hψ
  have hc : (ret σ ((A.erase d).erase (ι d)) * ι).SameCycle (ι w₁) (ι w₂) :=
    (sameCycle_congr (stable_ret _ _) (fun z hz => (ret_mul_eq hι hσ hA hd hz).symm) i₁).1 hr
  have := (conn_mul_iff hι).1 (conn_of_sameCycle hc)
  refine (conn_inv w₁).trans (this.trans ?_)
  have := conn_inv (ι := ι) (σ := ret σ ((A.erase d).erase (ι d))) (ι w₂)
  rwa [hι.invol] at this

/-- **Deleting an edge does not decrease the Euler gap.** -/
theorem gap_le_erase :
    gap ι σ A ≤ gap ι (ret σ ((A.erase d).erase (ι d))) ((A.erase d).erase (ι d)) := by
  classical
  have hne : ι d ≠ d := hι.ne d
  have hid : ι d ∈ A := hA d hd
  have hS := stable_erase_pair hι hA hd
  have hψ : Stable (σ * ι * swap d (ι d)) A := by
    intro x hx
    simp only [Perm.mul_apply]
    refine hσ _ (hA _ ?_)
    by_cases h1 : x = d
    · subst h1; rw [swap_apply_left]; exact hid
    by_cases h2 : x = ι d
    · subst h2; rw [swap_apply_right]; exact hd
    rw [swap_apply_of_ne_of_ne h1 h2]; exact hx
  have ψd : (σ * ι * swap d (ι d)) d = σ d := by
    simp [Perm.mul_apply, swap_apply_left, hι.invol]
  have ψd' : (σ * ι * swap d (ι d)) (ι d) = σ (ι d) := by
    simp [Perm.mul_apply, swap_apply_right]
  have e1 := nOrb_erase_pair hι hA hd σ hσ
  have e2 := nOrb_erase_pair hι hA hd _ hψ
  rw [ψd, ψd'] at e2
  have e3 := eul_erase hι hσ hA hd
  have e4 := card_erase_pair hι hA hd
  have e5 := comp_erase_le hι hσ hA hd
  generalize hA' : (A.erase d).erase (ι d) = A' at e1 e2 e3 e4 e5 hS
  generalize hk : ((({σ.symm d, σ.symm (ι d)} : Finset α).filter (· ∈ A')).image
    (ccls ι (ret σ A'))).card = k at e5
  have mA : ∀ {z}, z ∈ A' ↔ z ≠ ι d ∧ z ≠ d ∧ z ∈ A := fun {z} => by
    rw [← hA', mem_erase_pair hι hA hd]
  -- the number of remaining neighbours of the edge
  have k2 : k ≤ 2 := hk ▸ (card_image_le.trans ((card_filter_le _ _).trans card_le_two))
  have k_le_one : (σ d = d ∨ σ (ι d) = ι d) → k ≤ 1 := by
    intro h
    rw [← hk]
    refine card_image_le.trans ((card_le_card ?_).trans (card_singleton
      (if σ d = d then σ.symm (ι d) else σ.symm d)).le)
    intro x hx
    simp only [mem_filter, mem_insert, mem_singleton, mA] at hx
    simp only [mem_singleton]
    rcases h with h | h
    · have hs : σ.symm d = d := by rw [Equiv.symm_apply_eq]; exact h.symm
      rcases hx with ⟨rfl | rfl, hx⟩
      · exact absurd hs hx.2.1
      · simp [h]
    · have hs : σ.symm (ι d) = ι d := by rw [Equiv.symm_apply_eq]; exact h.symm
      rcases hx with ⟨rfl | rfl, hx⟩
      · split_ifs with h'
        · have : σ.symm d = d := by rw [Equiv.symm_apply_eq]; exact h'.symm
          rw [this]; exact absurd this hx.2.1
        · rfl
      · exact absurd hs hx.1
  have k_zero : (σ d = d ∧ σ (ι d) = ι d) ∨ (σ d = ι d ∧ σ (ι d) = d) → k = 0 := by
    intro h
    rw [← hk, card_eq_zero, image_eq_empty, filter_eq_empty_iff]
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mA]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have s1 : σ.symm d = d := by rw [Equiv.symm_apply_eq]; exact h1.symm
      have s2 : σ.symm (ι d) = ι d := by rw [Equiv.symm_apply_eq]; exact h2.symm
      rcases hx with rfl | rfl <;> simp [s1, s2]
    · have s1 : σ.symm d = ι d := by rw [Equiv.symm_apply_eq]; exact h2.symm
      have s2 : σ.symm (ι d) = d := by rw [Equiv.symm_apply_eq]; exact h1.symm
      rcases hx with rfl | rfl <;> simp [s1, s2]
  -- faces: merging or splitting
  unfold gap
  rw [e3]
  unfold eul
  by_cases hf : (σ * ι).SameCycle d (ι d)
  · have m := nOrb_mul_swap_split hf hne.symm hd hid
    -- the two darts on one face: no isolated loop
    have nsw : ¬ (σ d = ι d ∧ σ (ι d) = d) := by
      rintro ⟨h1, h2⟩
      have : (σ * ι) d = d := by simp [Perm.mul_apply, h2]
      obtain ⟨n, hn⟩ := sameCycle_iff.1 hf
      rw [iterate_fixed this] at hn
      exact hne hn.symm
    unfold loss at e1 e2
    split_ifs at e1 e2 with c1 c2
    · have := k_zero (Or.inl c1); push_cast; omega
    · have := k_le_one (by tauto); push_cast; omega
    · push_cast; omega
  · have m := nOrb_mul_swap_merge hf hd hid
    have hk1 : k ≤ 1 := by
      rw [← hk]
      refine card_le_one.2 fun a ha b hb => ?_
      simp only [mem_image, mem_filter, mem_insert, mem_singleton] at ha hb
      obtain ⟨x, ⟨hx1, hx2⟩, rfl⟩ := ha
      obtain ⟨y, ⟨hy1, hy2⟩, rfl⟩ := hb
      have ex : ∀ {z}, (z = σ.symm d ∨ z = σ.symm (ι d)) → σ z = d ∨ σ z = ι d := by
        rintro z (rfl | rfl) <;> simp
      refine (ccls_eq_iff hι).2 ?_
      have hA'' : ∀ {z}, z ∈ A' → z ∈ (A.erase d).erase (ι d) := fun h => hA' ▸ h
      have C : ∀ {a b}, a ∈ A' → b ∈ A' → σ a = d → σ b = ι d → Conn ι (ret σ A') a b :=
        fun ha hb ea eb => by
          have := conn_erase_of_face hι hσ hA hd hf (hA'' ha) (hA'' hb) ea eb; rwa [hA'] at this
      rcases ex hx1 with h1 | h1 <;> rcases ex hy1 with h2 | h2
      · obtain rfl := σ.injective (h1.trans h2.symm); exact .refl
      · exact C hx2 hy2 h1 h2
      · exact conn_symm hι (C hy2 hx2 h2 h1)
      · obtain rfl := σ.injective (h1.trans h2.symm); exact .refl
    -- the two darts on distinct faces: not pendant
    have np1 : σ d ≠ d := fun h => hf (by
      have := sameCycle_iterate (σ * ι) (ι d) 1
      simp only [iterate_one, Perm.mul_apply, hι.invol, h] at this
      exact this.symm)
    have np2 : σ (ι d) ≠ ι d := fun h => hf (by
      have := sameCycle_iterate (σ * ι) d 1
      simp only [iterate_one, Perm.mul_apply, h] at this
      exact this)
    unfold loss at e1 e2
    split_ifs at e1 e2 with c1 c2
    · exact absurd c1.1 np1
    · have hsw : σ d = ι d ∧ σ (ι d) = d := by tauto
      have := k_zero (Or.inr hsw); push_cast; omega
    · push_cast; omega

end Erase

/-! ### Deleting and contracting sets of edges -/

section Sets

variable {ι : Perm α} (hι : IsInv ι)
include hι

/-- A set closed under the reversal has an even number of darts. -/
theorem even_card {B : Finset α} (hB : Stable ι B) : Even B.card := by
  induction h : B.card using Nat.strong_induction_on generalizing B with
  | _ n ih =>
    rcases B.eq_empty_or_nonempty with rfl | ⟨d, hd⟩
    · subst h; simp
    have e := card_erase_pair hι hB hd
    obtain ⟨k, hk⟩ := ih _ (by omega) (stable_erase_pair hι hB hd) rfl
    exact ⟨k + 1, by omega⟩

/-- **Deleting the edges outside `B` does not decrease the Euler gap.** -/
theorem gap_le_ret {σ : Perm α} {A B : Finset α} (hσ : Stable σ A) (hA : Stable ι A)
    (hB : B ⊆ A) (hBι : Stable ι B) : gap ι σ A ≤ gap ι (ret σ B) B := by
  induction h : (A \ B).card using Nat.strong_induction_on generalizing A σ with
  | _ n ih =>
    by_cases hAB : A = B
    · subst hAB
      exact (gap_congr hι hσ hA fun z hz => (ret_eq_self_of hz (hσ z hz)).symm).le
    obtain ⟨d, hdA, hdB⟩ : ∃ d ∈ A, d ∉ B := by
      by_contra hc; push Not at hc; exact hAB (Subset.antisymm hc hB)
    have hidB : ι d ∉ B := fun h' => hdB (by rw [← hι.invol d]; exact hBι _ h')
    have hB' : B ⊆ (A.erase d).erase (ι d) := fun x hx =>
      mem_erase.2 ⟨fun e => hidB (e ▸ hx), mem_erase.2 ⟨fun e => hdB (e ▸ hx), hB hx⟩⟩
    have hlt : ((A.erase d).erase (ι d) \ B).card < n := by
      rw [← h]
      refine card_lt_card ⟨sdiff_subset_sdiff (erase_subset _ _ |>.trans (erase_subset _ _))
        subset_rfl, fun hc => hdB ?_⟩
      have := hc (mem_sdiff.2 ⟨hdA, hdB⟩)
      simp at this
    have := ih _ hlt (stable_ret σ _) (stable_erase_pair hι hA hdA) hB' rfl
    rw [ret_ret hB'] at this
    exact (gap_le_erase hι hσ hA hdA).trans this

/-- **Euler's inequality**: the gap is never positive. -/
theorem gap_nonpos {σ : Perm α} {A : Finset α} (hσ : Stable σ A) (hA : Stable ι A) :
    gap ι σ A ≤ 0 :=
  (gap_le_ret hι hσ hA (empty_subset A) (by simp [Stable])).trans (gap_empty _).le

/-- **Deleting edges keeps Euler's formula** in every component. -/
theorem gap_ret_eq_zero {σ : Perm α} {A B : Finset α} (hσ : Stable σ A) (hA : Stable ι A)
    (hB : B ⊆ A) (hBι : Stable ι B) (h0 : gap ι σ A = 0) : gap ι (ret σ B) B = 0 :=
  le_antisymm (gap_nonpos hι (stable_ret σ B) hBι) (h0 ▸ gap_le_ret hι hσ hA hB hBι)

variable (ι) in
/-- **Contracting the edges outside `B`**: deleting them in the dual map. -/
noncomputable def con (σ : Perm α) (B : Finset α) : Perm α := ret (σ * ι) B * ι

lemma stable_con {σ : Perm α} {B : Finset α} (hBι : Stable ι B) : Stable (con ι σ B) B :=
  (stable_ret _ _).mul hBι

/-- **Contracting edges keeps Euler's formula** in every component. -/
theorem gap_con_eq_zero {σ : Perm α} {A B : Finset α} (hσ : Stable σ A) (hA : Stable ι A)
    (hB : B ⊆ A) (hBι : Stable ι B) (h0 : gap ι σ A = 0) : gap ι (con ι σ B) B = 0 := by
  unfold con
  rw [gap_mul hι]
  exact gap_ret_eq_zero hι (hσ.mul hA) hA hB hBι (by rw [gap_mul hι]; exact h0)

/-- Contractions compose. -/
lemma con_con {σ : Perm α} {A B : Finset α} (hB : B ⊆ A) : con ι (con ι σ A) B = con ι σ B := by
  unfold con
  rw [mul_assoc, hι.mul_self, mul_one, ret_ret hB]

/-- Contracting nothing: on `A`, the contraction of no edge is the rotation. -/
lemma con_self_apply {σ : Perm α} {A : Finset α} (hσ : Stable σ A) (hA : Stable ι A) {x : α}
    (hx : x ∈ A) : con ι σ A x = σ x := by
  unfold con
  rw [Perm.mul_apply, ret_eq_self_of (hA x hx) ((hσ.mul hA) _ (hA x hx)), Perm.mul_apply,
    hι.invol]

/-- **Contracting one edge**: on the remaining darts, the rotation composed with the transposition
of the two darts of the edge, cut down to the remaining darts. -/
lemma con_erase_apply {σ : Perm α} {A : Finset α} (hσ : Stable σ A) (hA : Stable ι A) {d : α}
    (hd : d ∈ A) {x : α} (hx : x ∈ (A.erase d).erase (ι d)) :
    con ι σ ((A.erase d).erase (ι d)) x = ret (σ * swap d (ι d)) ((A.erase d).erase (ι d)) x := by
  have := ret_mul_eq hι (hσ.mul hA) hA hd hx
  rwa [mul_assoc σ ι ι, hι.mul_self, mul_one] at this

/-- **Contracting an edge between two distinct vertices merges them.** -/
theorem sameCycle_con_erase {σ : Perm α} {A : Finset α} (hσ : Stable σ A) (hA : Stable ι A)
    {d : α} (hd : d ∈ A) (hne : ¬ σ.SameCycle d (ι d)) {x y : α}
    (hx : x ∈ (A.erase d).erase (ι d)) (hy : y ∈ (A.erase d).erase (ι d)) :
    (con ι σ ((A.erase d).erase (ι d))).SameCycle x y ↔ σ.SameCycle x y ∨
      ((σ.SameCycle d x ∨ σ.SameCycle (ι d) x) ∧ (σ.SameCycle d y ∨ σ.SameCycle (ι d) y)) :=
  (sameCycle_congr (stable_con hι (stable_erase_pair hι hA hd))
    (fun _ hz => con_erase_apply hι hσ hA hd hz) hx).trans
    ((sameCycle_ret hx hy).trans (sameCycle_mul_swap hne))

end Sets

end Orbit

end PlanarFlow
