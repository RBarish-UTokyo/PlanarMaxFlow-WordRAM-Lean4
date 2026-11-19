module

public import PlanarFlow.NegSSSP.Frame

/-!
# The canonical numbering of a child, from the numbering of its parent

The child encodings of the split (`ChildProg.lean`) number the darts of the closure of a side
`Q` of a piece `P` by a list `L` of indices of the parent's numbering `cδ P`: first the indices
`h < #P` of the darts of `Q` in order (`oldA`), then, appended in order, the reverses `cα P h`
of these darts not yet listed (`apnd`). This file shows that this list is the canonical numbering
of the child (`fL_child`: `L.map (cδ P) = fL Q`), and that the child's first return of the
rotation is the first return of the parent's along the list (`walk_eq`), with the sum of the
walks at most the closure of the parent (`sum_walk_le`, from `Orbit.sum_retIdx_le`: the sum of
the indices of the first returns to `B ⊆ A` of a permutation keeping `A` is at most `#A`).

* `apnd L xs`: the list `L` with the elements of `xs` not yet in it appended in order;
  `apnd_eq`: for `xs` without repetition, `L ++ xs.filter (· ∉ L)`.
* `oldA`: the indices `h < m` with side `SD h = s`.
* **`fL_child`**, `mem_child`, `idx_child` (the index of a dart of the child in the list).
* **`sum_retIdx_le`**, `walkIdx`, **`walk_eq`**, **`sum_walk_le`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Orbit

open Equiv Function Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {π : Perm α}

/-- **The returns to `B` cover disjoint stretches of the orbits**: the sum of the indices of the
first returns to `B ⊆ A` is at most `#A` when `π` keeps `A`. -/
theorem sum_retIdx_le {A B : Finset α} (hB : B ⊆ A) (hA : ∀ x ∈ A, π x ∈ A) :
    ∑ x ∈ B, retIdx π B x ≤ A.card := by
  classical
  have hit : ∀ x ∈ A, ∀ i, (π^[i]) x ∈ A := fun x hx i => by
    induction i with
    | zero => exact hx
    | succ i ih => rw [iterate_succ_apply']; exact hA _ ih
  set V : α → Finset α := fun x => (range (retIdx π B x)).image fun i => (π^[i + 1]) x
  have hinj : ∀ x ∈ B, ∀ a b, a ≤ b → b ≤ retIdx π B x → 0 < a →
      (π^[a]) x = (π^[b]) x → a = b := by
    intro x hx a b hab hb ha e
    by_contra hne
    have e' : (π^[b - a]) x = x := by
      apply π.injective.iterate a
      rw [← iterate_add_apply, Nat.add_sub_cancel' hab, e]
    have h0 : 0 < b - a := by omega
    exact not_mem_of_lt_retIdx hx h0 (by omega) (e' ▸ hx)
  have hcard : ∀ x ∈ B, (V x).card = retIdx π B x := fun x hx => by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj e
    simp only [coe_range, Set.mem_Iio] at hi hj
    simp only at e
    rcases le_total i j with h | h
    · have := hinj x hx (i + 1) (j + 1) (by omega) (by omega) (by omega) e; omega
    · have := hinj x hx (j + 1) (i + 1) (by omega) (by omega) (by omega) e.symm; omega
  have hsub : ∀ x ∈ B, V x ⊆ A := fun x hx y hy => by
    obtain ⟨i, -, rfl⟩ := mem_image.1 hy
    exact hit x (hB hx) _
  have hdisj : (B : Set α).PairwiseDisjoint V := by
    intro x hx y hy hxy
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro z hzx hzy
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hzx
    obtain ⟨b, hb, e⟩ := mem_image.1 hzy
    rw [mem_range] at ha hb
    -- `π^[b+1] y = π^[a+1] x`
    have key : ∀ x y : α, x ∈ B → y ∈ B → ∀ a b, a ≤ b → b ≤ retIdx π B y → 0 < a →
        (π^[b]) y = (π^[a]) x → x = y := by
      intro x y hx hy a b hab hb ha e
      have e' : (π^[b - a]) y = x := by
        apply π.injective.iterate a
        rw [← iterate_add_apply, Nat.add_sub_cancel' hab, e]
      rcases Nat.eq_zero_or_pos (b - a) with h0 | h0
      · rw [h0] at e'; exact e'.symm
      · exact absurd (e' ▸ hx) (not_mem_of_lt_retIdx hy h0 (by omega))
    rcases le_total (a + 1) (b + 1) with h | h
    · exact hxy (key x y hx hy (a + 1) (b + 1) h (by omega) (by omega) e)
    · exact hxy (key y x hy hx (b + 1) (a + 1) h (by omega) (by omega) e.symm).symm
  calc ∑ x ∈ B, retIdx π B x = ∑ x ∈ B, (V x).card := sum_congr rfl fun x hx => (hcard x hx).symm
    _ = (B.biUnion V).card := (card_biUnion hdisj).symm
    _ ≤ A.card := card_le_card (biUnion_subset.2 hsub)

end Orbit

namespace NegSSSP

namespace Frame

open Finset Orbit CombMap BKMNW

/-! ### Appending the new elements of a list -/

/-- `L` with the elements of `xs` not yet in it appended in order. -/
def apnd (L : List ℕ) : List ℕ → List ℕ
  | [] => L
  | x :: xs => apnd (if x ∈ L then L else L ++ [x]) xs

theorem apnd_eq : ∀ (L xs : List ℕ), xs.Nodup → apnd L xs = L ++ xs.filter (· ∉ L)
  | L, [], _ => by simp [apnd]
  | L, x :: xs, h => by
    rw [List.nodup_cons] at h
    simp only [apnd]
    by_cases hx : x ∈ L
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hx), apnd_eq L xs h.2, List.filter_cons]
      simp [hx]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hx), apnd_eq _ xs h.2, List.filter_cons]
      simp only [hx, not_false_eq_true, decide_true, ite_true, List.append_assoc,
        List.singleton_append]
      congr 2
      apply List.filter_congr
      intro y hy
      have : y ≠ x := fun e => h.1 (e ▸ hy)
      simp [this]

/-- The indices `h < m` with side `s`. -/
def oldA (s m : ℕ) (SD : ℕ → ℕ) : List ℕ := (List.range m).filter fun h => SD h = s

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

theorem cL_range (P : Finset D) : cL g P = (List.range P.card).map (cδ g N P) := by
  apply List.ext_getElem
  · simp [length_cL]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, cδ_lt (by rw [← length_cL (g := g)]; exact h1),
      List.getD_eq_getElem _ _ h1]

theorem idxOf_map {β : Type*} [DecidableEq β] {f : ℕ → β} :
    ∀ {L : List ℕ} {x : ℕ}, (∀ y ∈ L, f y = f x → y = x) →
      (L.map f).idxOf (f x) = L.idxOf x
  | [], _, _ => by simp
  | y :: L, x, h => by
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons]
    by_cases hy : y = x
    · subst hy; simp
    · have : f y ≠ f x := fun e => hy (h y List.mem_cons_self e)
      simp only [beq_iff_eq, this, hy, ite_false]
      rw [idxOf_map (fun z hz => h z (List.mem_cons_of_mem _ hz))]

variable (g N) in
/-- The list of the child of side `s`. -/
noncomputable def chL (P : Finset D) (s : ℕ) (SD : ℕ → ℕ) : List ℕ :=
  apnd (oldA s P.card SD) ((oldA s P.card SD).map (cα g N P))

/-- The side of a dart: `SD h = s` exactly on the side `Q`. -/
def SideOK (P : Finset D) (Q : Finset D) (s : ℕ) (SD : ℕ → ℕ) (δ : ℕ → D) : Prop :=
  Q ⊆ P ∧ ∀ h < P.card, (SD h = s ↔ δ h ∈ Q)

/-- **The list of the child is its canonical numbering.** -/
theorem fL_child {P Q : Finset D} {s : ℕ} {SD : ℕ → ℕ} (hs : SideOK P Q s SD (cδ g N P)) :
    (chL g N P s SD).map (cδ g N P) = fL g N Q := by
  have he := penc_canon (g := g) (N := N) P
  have hk := he.mle
  set δ := cδ g N P
  set A := oldA s P.card SD with hA
  have hAlt : ∀ h ∈ A, h < P.card := fun h hh => by
    rw [hA, oldA, List.mem_filter, List.mem_range] at hh; exact hh.1
  have hAmem : ∀ h < ck N P, (h ∈ A ↔ δ h ∈ Q) := fun h hh => by
    rw [hA, oldA, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact (hs.2 h h1).1 (by simpa using h2)
    · intro hq
      have h1 : h < P.card := (he.mem_iff hh).1 (hs.1 hq)
      exact ⟨h1, by simpa using (hs.2 h h1).2 hq⟩
  have hAnd : A.Nodup := (List.nodup_range).filter _
  -- the darts of `Q`
  have h1 : A.map δ = cL g Q := by
    rw [cL_sub hs.1, cL_range (N := N) P, List.filter_map]
    congr 1
    rw [hA, oldA]
    apply List.filter_congr
    intro h hh
    rw [List.mem_range] at hh
    simp only [Function.comp_apply]
    have := hs.2 h hh
    by_cases hq : δ h ∈ Q <;> simp_all <;> first | exact hq | exact fun h' => hq h'
  -- the reverses
  have hαnd : (A.map (cα g N P)).Nodup := by
    refine hAnd.map_on fun x hx y hy e => ?_
    have hx' := hAlt x hx
    have hy' := hAlt y hy
    exact he.enum.inj x (by omega) y (by omega) (by
      have := congrArg N.rev (congrArg δ e)
      rwa [he.α_eq x (by omega), he.α_eq y (by omega), N.rev_rev, N.rev_rev] at this)
  unfold chL
  rw [← hA, apnd_eq _ _ hαnd, List.map_append, h1]
  unfold fL rL
  congr 1
  rw [← h1, List.filter_map, List.map_map, List.filter_map, List.map_map]
  have hf : List.filter ((fun x => decide (x ∉ A)) ∘ cα g N P) A =
      List.filter ((fun d => decide (N.rev d ∉ Q)) ∘ δ) A := by
    apply List.filter_congr
    intro h hh
    have h' := hAlt h hh
    have hα := he.α_lt h (by omega)
    simp only [Function.comp_apply]
    have e1 := hAmem _ hα
    rw [he.α_eq h (by omega)] at e1
    simp only [decide_eq_decide, e1]
  rw [hf]
  apply List.map_congr_left
  intro h hh
  have h' := hAlt h (List.mem_of_mem_filter hh)
  simp only [Function.comp_apply]
  exact he.α_eq h (by omega)

theorem rcl_mono' {K P : Finset D} (hK : K ⊆ P) : rcl N K ⊆ rcl N P := fun x hx => by
  rw [mem_rcl] at hx ⊢
  rcases hx with h | h
  · exact Or.inl (hK h)
  · exact Or.inr (hK h)

section Child

variable {P Q : Finset D} {s : ℕ} {SD : ℕ → ℕ}

theorem chL_lt (x : ℕ) (hx : x ∈ chL g N P s SD) : x < ck N P := by
  have he := penc_canon (g := g) (N := N) P
  have hk := he.mle
  have hA : ∀ h ∈ oldA s P.card SD, h < P.card := fun h hh => by
    rw [oldA, List.mem_filter, List.mem_range] at hh; exact hh.1
  have key : ∀ (L xs : List ℕ), (∀ y ∈ L, y < ck N P) → (∀ y ∈ xs, y < ck N P) →
      ∀ y ∈ apnd L xs, y < ck N P := by
    intro L xs
    induction xs generalizing L with
    | nil => intro h1 _; simpa [apnd] using h1
    | cons z zs ih =>
      intro h1 h2
      simp only [apnd]
      apply ih _ _ (fun y hy => h2 y (List.mem_cons_of_mem _ hy))
      intro y hy
      split_ifs at hy
      · exact h1 y hy
      · rcases List.mem_append.1 hy with hy | hy
        · exact h1 y hy
        · rw [List.mem_singleton] at hy; subst hy; exact h2 _ List.mem_cons_self
  refine key _ _ (fun y hy => by have := hA y hy; unfold ck; omega) (fun y hy => ?_) x hx
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hy
  have := hA h hh
  exact he.α_lt h (by omega)

/-- The numbering of the child is a list of parent indices. -/
theorem chL_nodup : (chL g N P s SD).Nodup := by
  have key : ∀ (L xs : List ℕ), L.Nodup → (apnd L xs).Nodup := by
    intro L xs
    induction xs generalizing L with
    | nil => intro h; simpa [apnd] using h
    | cons z zs ih =>
      intro h
      simp only [apnd]
      apply ih
      split_ifs with hz
      · exact h
      · rw [List.nodup_append]
        exact ⟨h, List.nodup_singleton z, fun a ha b hb e => by
          rw [List.mem_singleton] at hb; subst hb; subst e; exact hz ha⟩
  exact key _ _ ((List.nodup_range).filter _)

/-- The first return of the parent. -/
noncomputable abbrev ρP (N : CombMap D V F) (P : Finset D) : Equiv.Perm D :=
  ret (rotPerm N) (rcl N P)

theorem iter_cσ (x : ℕ) (hx : x < ck N P) (i : ℕ) :
    (cσ g N P)^[i] x < ck N P ∧ cδ g N P ((cσ g N P)^[i] x) = (ρP N P)^[i] (cδ g N P x) := by
  have he := penc_canon (g := g) (N := N) P
  induction i with
  | zero => exact ⟨hx, rfl⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih.2]
    exact ⟨he.σ_lt _ ih.1, he.σ_eq _ ih.1⟩

variable (hs : SideOK P Q s SD (cδ g N P))
include hs

theorem length_chL : (chL g N P s SD).length = ck N Q := by
  rw [← List.length_map (f := cδ g N P), fL_child hs, length_fL]; rfl

theorem cδ_child {j : ℕ} (hj : j < (chL g N P s SD).length) :
    cδ g N Q j = cδ g N P ((chL g N P s SD)[j]) := by
  have hj' : j < (fL g N Q).length := by rw [← fL_child hs, List.length_map]; exact hj
  rw [cδ_eq hj']
  simp only [← fL_child hs, List.getElem_map]

theorem mem_chL {x : ℕ} (hx : x < ck N P) :
    x ∈ chL g N P s SD ↔ cδ g N P x ∈ rcl N Q := by
  have he := penc_canon (g := g) (N := N) P
  rw [← mem_fL (g := g), ← fL_child hs, List.mem_map]
  constructor
  · intro h; exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, e⟩
    rw [he.enum.inj y (chL_lt y hy) x hx e] at hy; exact hy

theorem idx_chL {x : ℕ} (hx : x ∈ chL g N P s SD) :
    (fL g N Q).idxOf (cδ g N P x) = (chL g N P s SD).idxOf x := by
  have he := penc_canon (g := g) (N := N) P
  rw [← fL_child hs]
  exact idxOf_map fun y hy e => he.enum.inj y (chL_lt y hy) x (chL_lt x hx) e

/-- **The reversal of the child.** -/
theorem cα_child {j : ℕ} (hj : j < (chL g N P s SD).length) :
    cα g N Q j = (chL g N P s SD).idxOf (cα g N P ((chL g N P s SD)[j])) := by
  have he := penc_canon (g := g) (N := N) P
  set L := chL g N P s SD
  have hx : L[j] < ck N P := chL_lt _ (List.getElem_mem hj)
  have hα := he.α_lt _ hx
  have hm : cα g N P L[j] ∈ L := by
    rw [mem_chL hs hα, he.α_eq _ hx]
    apply rev_mem_rcl'
    rw [← mem_chL hs hx]; exact List.getElem_mem hj
  show (fL g N Q).idxOf (N.rev (cδ g N Q j)) = _
  rw [cδ_child hs hj, ← he.α_eq _ hx]
  exact idx_chL hs hm

/-- **The walk of the child's first return**: from `x = L[j]`, the iterates of the parent's
`cσ` leave the list until the index `retIdx`, where they return to it. -/
theorem walk_child {j : ℕ} (hj : j < (chL g N P s SD).length) :
    let L := chL g N P s SD
    let t := retIdx (ρP N P) (rcl N Q) (cδ g N P L[j])
    0 < t ∧ (cσ g N P)^[t] L[j] ∈ L ∧
      (∀ i, 0 < i → i < t → (cσ g N P)^[i] L[j] ∉ L) ∧
      cσ g N Q j = L.idxOf ((cσ g N P)^[t] L[j]) := by
  intro L t
  have hx : L[j] < ck N P := chL_lt _ (List.getElem_mem hj)
  have hxB : cδ g N P L[j] ∈ rcl N Q := (mem_chL hs hx).1 (List.getElem_mem hj)
  have it := iter_cσ (g := g) (N := N) _ hx t
  have hmem : (cσ g N P)^[t] L[j] ∈ L := by
    rw [mem_chL hs it.1, it.2]; exact iterate_retIdx_mem hxB
  refine ⟨retIdx_pos _, hmem, fun i h0 hi hin => ?_, ?_⟩
  · have it' := iter_cσ (g := g) (N := N) _ hx i
    rw [mem_chL hs it'.1, it'.2] at hin
    exact not_mem_of_lt_retIdx hxB h0 hi hin
  · unfold cσ
    rw [cδ_child hs hj, ← ret_ret (π := rotPerm N) (rcl_mono' hs.1),
      ret_apply_of_mem hxB, ← it.2]
    exact idx_chL hs hmem

/-- **The walks of the child sum to at most the closure of the parent.** -/
theorem sum_walk_le :
    ((chL g N P s SD).map fun x => retIdx (ρP N P) (rcl N Q) (cδ g N P x)).sum ≤ ck N P := by
  have h1 : ((chL g N P s SD).map fun x => retIdx (ρP N P) (rcl N Q) (cδ g N P x)) =
      (fL g N Q).map (retIdx (ρP N P) (rcl N Q)) := by
    rw [← fL_child hs, List.map_map]; rfl
  rw [h1, ← List.sum_toFinset _ (fL_nodup Q)]
  have h2 : (fL g N Q).toFinset = rcl N Q := by ext x; rw [List.mem_toFinset, mem_fL]
  rw [h2]
  exact sum_retIdx_le (rcl_mono' hs.1) fun x hx => ret_mem hx

/-- The darts of the side, in the parent's order. -/
theorem oldA_map :
    (oldA s P.card SD).map (cδ g N P) = cL g Q := by
  rw [cL_sub hs.1, cL_range (N := N) P, List.filter_map]
  congr 1
  rw [oldA]
  apply List.filter_congr
  intro h hh
  rw [List.mem_range] at hh
  simp only [Function.comp_apply]
  have := hs.2 h hh
  by_cases hq : cδ g N P h ∈ Q <;> simp_all

theorem length_oldA :
    (oldA s P.card SD).length = Q.card := by
  rw [← List.length_map (f := cδ g N P), oldA_map hs, length_cL]

theorem cα_mem_chL {j : ℕ} (hj : j < (chL g N P s SD).length) :
    cα g N P ((chL g N P s SD)[j]) ∈ chL g N P s SD := by
  have he := penc_canon (g := g) (N := N) P
  have hx : (chL g N P s SD)[j] < ck N P := chL_lt _ (List.getElem_mem hj)
  rw [mem_chL hs (he.α_lt _ hx), he.α_eq _ hx]
  apply rev_mem_rcl'
  rw [← mem_chL hs hx]; exact List.getElem_mem hj

end Child

end Frame

end NegSSSP

end PlanarFlow
