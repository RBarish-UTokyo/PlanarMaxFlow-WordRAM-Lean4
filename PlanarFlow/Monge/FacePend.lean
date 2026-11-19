module

public import PlanarFlow.Monge.Meet

/-!
# The crossing inequality of a face: subsequences, potentials, pendant targets

Complements to `PlanarFlow.Monge.crossing_face` (`PlanarFlow/Monge/Meet.lean`), the crossing
inequality of the distances between the corners of one face of a plane map.

* `Crossing.comp`: the crossing inequality passes to every increasing subsequence of the
  corners (only some of the corners of a face are used as vertices of a dense distance graph).
* `Crossing.congr`: only the entries between the corners matter.
* `Crossing.add_pot`: adding `f j - f i` to the entry `(i, j)` (distances shifted back by a
  potential, as in the dense distance graphs of the negative-length recursion) keeps it.
* `crossing_face_pend`: **the crossing inequality for distances to pendant targets.** The sources
  are corners of a face, as in `crossing_face`, but the target of the corner `j` is a vertex
  `w j` joined to the corner by a dart of the map (which need not be an arc of the digraph), and
  no arc of the digraph enters a corner. This is the setting of the cut of the dual graph along
  a path (`PlanarFlow.BKMNW.Cut`), where each corner is a new root vertex with a pendant arc to
  the face of the dual it stands for.
* `CrossingO`, `crossingO_face`: **with missing arcs** (`none` read as an infinite length): for
  interleaved ends, if the lengths from `i` to `j` and from `i'` to `j'` are finite, so are those
  from `i` to `j'` and from `i'` to `j`, and the crossing inequality holds. `CrossingO.crossing`:
  with all the lengths finite it is `Crossing`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open PlanarSeparator

/-! ### Subsequences and potentials -/

section Algebra

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- **The crossing inequality on an increasing subsequence of the corners.** -/
theorem Crossing.comp {b : ℕ} {D : ℕ → ℕ → α} (h : Crossing b D) {b' : ℕ} {s : ℕ → ℕ}
    (hs : ∀ i j, i < j → j < b' → s i < s j) (hsb : ∀ i < b', s i < b) :
    Crossing b' (fun i j => D (s i) (s j)) := by
  intro i i' j j' hi hj hi' hj' hsep
  refine h (s i) (s i') (s j) (s j') (hs i i' hi hi') (hs j j' hj hj') (hsb i' hi') (hsb j' hj')
    ?_
  rcases hsep with h' | h'
  · exact Or.inl (hs i' j h' (by omega))
  · exact Or.inr (hs j' i h' (by omega))

/-- **Adding a function of the row and a function of the column keeps the crossing
inequality** (in particular `f j - f i`, a shift by a potential). -/
theorem Crossing.add_pot {b : ℕ} {D : ℕ → ℕ → α} (h : Crossing b D) (r c : ℕ → α) :
    Crossing b (fun i j => D i j + (r i + c j)) := by
  intro i i' j j' hi hj hi' hj' hsep
  have key := h i i' j j' hi hj hi' hj' hsep
  calc D i j' + (r i + c j') + (D i' j + (r i' + c j))
      = (D i j' + D i' j) + (r i + r i' + c j + c j') := by abel
    _ ≤ (D i j + D i' j') + (r i + r i' + c j + c j') := add_le_add key le_rfl
    _ = D i j + (r i + c j) + (D i' j' + (r i' + c j')) := by abel

/-- The crossing inequality is a property of the entries between the corners only. -/
theorem Crossing.congr {b : ℕ} {D D' : ℕ → ℕ → α} (h : Crossing b D)
    (hDD' : ∀ i j, i < b → j < b → D i j = D' i j) : Crossing b D' := by
  intro i i' j j' hi hj hi' hj' hsep
  rw [← hDD' i j' (by omega) hj', ← hDD' i' j hi' (by omega), ← hDD' i j (by omega) (by omega),
    ← hDD' i' j' hi' hj']
  exact h i i' j j' hi hj hi' hj' hsep

end Algebra

/-! ### Walks extended by one dart -/

section Concat

variable {D P : Type*} {M : PlanarSeparator.Map D P}

/-- A walk of darts extended by a dart at its end. -/
lemma IsMWalk.concat {y z : P} {m : ℕ} {c : ℕ → D} (h : IsMWalk M y z m c) {e : D}
    (he : M.vert e = z) :
    IsMWalk M y (M.vert (M.α e)) (m + 1) (fun s => if s < m then c s else e) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hm, h0, hz, hs⟩
  · exact Or.inr ⟨by omega, by simpa using he, by simp, fun s hs => by omega⟩
  · refine Or.inr ⟨by omega, by simpa [hm] using h0, by simp, fun s hs' => ?_⟩
    by_cases h' : s + 1 < m
    · simp only [h', show s < m by omega, ↓reduceIte]
      exact hs s h'
    · obtain rfl : s = m - 1 := by omega
      simp only [show m - 1 < m by omega, show ¬ m - 1 + 1 < m by omega, ↓reduceIte]
      rw [hz, he]

/-- A vertex of an extended walk is a vertex of the walk or the end of the added dart. -/
lemma OnMWalk.of_concat {y : P} {m : ℕ} {c : ℕ → D} {e : D} {v : P}
    (h : OnMWalk M y (m + 1) (fun s => if s < m then c s else e) v) :
    OnMWalk M y m c v ∨ v = M.vert (M.α e) := by
  rcases h with h | ⟨s, hs, hv⟩
  · exact Or.inl (Or.inl h)
  · by_cases hsm : s < m
    · simp only [hsm, ↓reduceIte] at hv
      exact Or.inl (Or.inr ⟨s, hsm, hv⟩)
    · simp only [hsm, ↓reduceIte] at hv
      exact Or.inr hv.symm

end Concat

/-! ### Pendant targets -/

section Pend

variable {D P A : Type*} {M : PlanarSeparator.Map D P} [Fintype D] [DecidableEq D] [Fintype P]
  [DecidableEq P] [Fintype A] {G : Digraph P A}

/-- **The crossing inequality for distances from the corners of a face to pendant targets.** Let
`G` be a digraph whose arcs are darts of a plane map (`emb`), `d₀` a dart of a face whose boundary
walk has period `N`, and `t 0 < t 1 < ⋯ < t (b - 1) < N` positions along it, at pairwise distinct
corners `v i = vert (φ ^ t i d₀)` that no arc of `G` enters. Let `w j` be joined to `v j` by a
dart `pd j` of the map. If the distances in `G` from every corner `v i` are given (`GDist`), the
distance from `v i` to `w j` being `Dm i j`, then `Dm` satisfies the crossing inequality. -/
theorem crossing_face_pend (hM : M.IsPlane) {emb : A → D} (hs : ∀ a, G.src a = M.vert (emb a))
    (hd : ∀ a, G.dst a = M.vert (M.α (emb a))) {d₀ : D} {N : ℕ} (hN0 : (M.φ ^ N) d₀ = d₀)
    (hmin : ∀ k, 0 < k → k < N → (M.φ ^ k) d₀ ≠ d₀) {b : ℕ} {t : ℕ → ℕ}
    (ht : ∀ i j, i < j → j < b → t i < t j) (htN : ∀ i < b, t i < N)
    (hcor : ∀ i < b, ∀ j < b, M.vert ((M.φ ^ t i) d₀) = M.vert ((M.φ ^ t j) d₀) → i = j)
    (hin : ∀ a, ∀ j < b, G.dst a ≠ M.vert ((M.φ ^ t j) d₀)) {w : ℕ → P} {pd : ℕ → D}
    (hpw : ∀ j < b, M.vert (pd j) = w j)
    (hpv : ∀ j < b, M.vert (M.α (pd j)) = M.vert ((M.φ ^ t j) d₀)) {Dm : ℕ → ℕ → ℤ}
    (hδ : ∀ i < b, ∃ δ, GDist G (M.vert ((M.φ ^ t i) d₀)) δ ∧
      ∀ j < b, δ (w j) = some (Dm i j)) :
    Crossing b Dm := by
  intro i i' j j' hi hj hi' hj' hsep
  have hjb : j < b := by omega
  have hib : i < b := by omega
  obtain ⟨δ, hδ1, hδ2⟩ := hδ i hib
  obtain ⟨δ', hδ1', hδ2'⟩ := hδ i' hi'
  refine exchange hd hδ1 hδ1' (hδ2 j hjb) (hδ2 j' hj') (hδ2' j hjb)
    (hδ2' j' hj') fun m p n q hp hq => ?_
  have hp' := (isMWalk_of_isWalk hs hd hp).concat (hpw j hjb)
  have hq' := (isMWalk_of_isWalk hs hd hq).concat (hpw j' hj')
  rw [hpv j hjb] at hp'
  rw [hpv j' hj'] at hq'
  -- the extended walks meet
  have hmeet : ∃ v, OnMWalk M (M.vert ((M.φ ^ t i) d₀)) (m + 1)
      (fun s => if s < m then emb (p s) else pd j) v ∧
      OnMWalk M (M.vert ((M.φ ^ t i') d₀)) (n + 1)
      (fun s => if s < n then emb (q s) else pd j') v := by
    rcases hsep with hsep | hsep
    · -- `i < i' < j < j'`
      have l1 := ht i i' hi hi'
      have l2 := ht i' j hsep hjb
      have l3 := ht j j' hj hj'
      have l4 := htN j' hj'
      exact meet_corners hM hN0 hmin (s := t i) (sa := t j') (sb := t j) (sc := t i')
        (a := N + t i - t j') (b := N + t i - t j) (c' := N + t i - t i') (by omega) (by omega)
        (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) hp' hq'
    · -- `j < j' < i < i'`
      have l1 := ht j j' hj (by omega)
      have l2 := ht j' i hsep hib
      have l3 := ht i i' hi hi'
      have l4 := htN i' hi'
      exact meet_corners hM hN0 hmin (s := t i) (sa := t j') (sb := t j) (sc := t i')
        (a := t i - t j') (b := t i - t j) (c' := N + t i - t i') (by omega) (by omega)
        (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) hp' hq'
  obtain ⟨v, hv1, hv2⟩ := hmeet
  -- a corner lies on a walk of `G` only as its start
  have key : ∀ {x : P} {k : ℕ} {c : ℕ → A} {l : ℕ}, l < b →
      OnMWalk M x k (fun s => emb (c s)) (M.vert ((M.φ ^ t l) d₀)) →
      M.vert ((M.φ ^ t l) d₀) = x := by
    intro x k c l hl h
    rcases h with h | ⟨s, -, h⟩
    · exact h
    · exact absurd (by rw [hd]; exact h) (hin (c s) l hl)
  have hne1 : j' ≠ i := by rcases hsep with h | h <;> omega
  have hne2 : j ≠ i' := by rcases hsep with h | h <;> omega
  rcases hv1.of_concat with hv1 | hv1 <;> rcases hv2.of_concat with hv2 | hv2
  · exact ⟨v, hv1, hv2⟩
  · rw [hpv j' hj'] at hv2
    subst hv2
    exact absurd (hcor j' hj' i hib (key hj' hv1)) hne1
  · rw [hpv j hjb] at hv1
    subst hv1
    exact absurd (hcor j hjb i' hi' (key hjb hv2)) hne2
  · rw [hpv j hjb] at hv1
    rw [hpv j' hj', hv1] at hv2
    exact absurd (hcor j hjb j' hj' hv2) (by omega)

end Pend

/-! ### Missing arcs -/

section Option

/-- **The crossing inequality with missing arcs** (`none` read as an infinite length): for
interleaved ends, if the lengths from `i` to `j` and from `i'` to `j'` are finite, so are those
from `i` to `j'` and from `i'` to `j`, and `D i j' + D i' j ≤ D i j + D i' j'`. -/
def CrossingO (b : ℕ) (D : ℕ → ℕ → Option ℤ) : Prop :=
  ∀ i i' j j', i < i' → j < j' → i' < b → j' < b → (i' < j ∨ j' < i) →
    ∀ a a', D i j = some a → D i' j' = some a' →
      ∃ x y, D i j' = some x ∧ D i' j = some y ∧ x + y ≤ a + a'

/-- With all the lengths finite, `CrossingO` is `Crossing`. -/
theorem CrossingO.crossing {b : ℕ} {D : ℕ → ℕ → Option ℤ} (h : CrossingO b D)
    {Dm : ℕ → ℕ → ℤ} (hD : ∀ i < b, ∀ j < b, D i j = some (Dm i j)) : Crossing b Dm := by
  intro i i' j j' hi hj hi' hj' hsep
  obtain ⟨x, y, hx, hy, hle⟩ := h i i' j j' hi hj hi' hj' hsep _ _ (hD i (by omega) j (by omega))
    (hD i' hi' j' hj')
  rw [hD i (by omega) j' hj', Option.some_inj] at hx
  rw [hD i' hi' j (by omega), Option.some_inj] at hy
  rw [hx, hy]
  exact hle

/-- `CrossingO` is a property of the entries between the corners only. -/
theorem CrossingO.congr {b : ℕ} {D D' : ℕ → ℕ → Option ℤ} (h : CrossingO b D)
    (hDD' : ∀ i j, i < b → j < b → D i j = D' i j) : CrossingO b D' := by
  intro i i' j j' hi hj hi' hj' hsep a a' ha ha'
  rw [← hDD' i j' (by omega) hj', ← hDD' i' j hi' (by omega)]
  rw [← hDD' i j (by omega) (by omega)] at ha
  rw [← hDD' i' j' hi' hj'] at ha'
  exact h i i' j j' hi hj hi' hj' hsep a a' ha ha'

/-- Adding a function of the row and a function of the column to the finite lengths keeps
`CrossingO`. -/
theorem CrossingO.add_pot {b : ℕ} {D : ℕ → ℕ → Option ℤ} (h : CrossingO b D) (r c : ℕ → ℤ) :
    CrossingO b (fun i j => (D i j).map (· + (r i + c j))) := by
  intro i i' j j' hi hj hi' hj' hsep a a' ha ha'
  obtain ⟨a₀, ha₀, rfl⟩ := Option.map_eq_some_iff.1 ha
  obtain ⟨a₀', ha₀', rfl⟩ := Option.map_eq_some_iff.1 ha'
  obtain ⟨x, y, hx, hy, hle⟩ := h i i' j j' hi hj hi' hj' hsep a₀ a₀' ha₀ ha₀'
  refine ⟨x + (r i + c j'), y + (r i' + c j), by simp [hx], by simp [hy], ?_⟩
  linarith

variable {D P A : Type*} {M : PlanarSeparator.Map D P} [Fintype D] [DecidableEq D] [Fintype P]
  [DecidableEq P] [Fintype A] {G : Digraph P A}

/-- **The exchange of tails, with missing arcs.** If every shortest walk from `x` to `y` meets
every one from `x'` to `y'`, and both distances are finite, then `y'` is reached from `x`, `y` is
reached from `x'`, and `δ x y' + δ x' y ≤ δ x y + δ x' y'`. -/
lemma exchangeO {emb : A → D} (hd : ∀ a, G.dst a = M.vert (M.α (emb a))) {x x' y y' : P}
    {δ δ' : P → Option ℤ} (hδ : GDist G x δ) (hδ' : GDist G x' δ') {a a' : ℤ}
    (h1 : δ y = some a) (h4 : δ' y' = some a')
    (hmeet : ∀ m p n q, GWalk G x y m p → GWalk G x' y' n q →
      ∃ v, OnMWalk M x m (fun t => emb (p t)) v ∧ OnMWalk M x' n (fun t => emb (q t)) v) :
    ∃ u w, δ y' = some u ∧ δ' y = some w ∧ u + w ≤ a + a' := by
  obtain ⟨m, p, hp, hpl⟩ := hδ.some_walk y _ h1
  obtain ⟨n, q, hq, hql⟩ := hδ'.some_walk y' _ h4
  obtain ⟨v, hv1, hv2⟩ := hmeet m p n q hp hq
  obtain ⟨m₁, c₁, m₂, c₂, w₁, w₂, e₁⟩ := isWalk_split hd hp hv1
  obtain ⟨n₁, d₁, n₂, d₂, w₃, w₄, e₂⟩ := isWalk_split hd hq hv2
  have k1 := isWalk_append w₁ w₄
  have k2 := isWalk_append w₃ w₂
  cases hu : δ y' with
  | none => exact absurd k1 (hδ.none y' hu _ _)
  | some u =>
    cases hw : δ' y with
    | none => exact absurd k2 (hδ'.none y hw _ _)
    | some w =>
      refine ⟨u, w, rfl, rfl, ?_⟩
      have l1 := hδ.some_le y' _ hu _ _ k1
      have l2 := hδ'.some_le y _ hw _ _ k2
      rw [walkLen_append] at l1 l2
      omega

/-- **The crossing inequality of a face, with missing arcs**: `crossing_face` without assuming
the distances between the corners finite. -/
theorem crossingO_face (hM : M.IsPlane) {emb : A → D} (hs : ∀ a, G.src a = M.vert (emb a))
    (hd : ∀ a, G.dst a = M.vert (M.α (emb a))) {d₀ : D} {N : ℕ} (hN0 : (M.φ ^ N) d₀ = d₀)
    (hmin : ∀ k, 0 < k → k < N → (M.φ ^ k) d₀ ≠ d₀) {b : ℕ} {t : ℕ → ℕ}
    (ht : ∀ i j, i < j → j < b → t i < t j) (htN : ∀ i < b, t i < N) {Dm : ℕ → ℕ → Option ℤ}
    (hδ : ∀ i < b, ∃ δ, GDist G (M.vert ((M.φ ^ t i) d₀)) δ ∧
      ∀ j < b, δ (M.vert ((M.φ ^ t j) d₀)) = Dm i j) :
    CrossingO b Dm := by
  intro i i' j j' hi hj hi' hj' hsep a a' ha ha'
  obtain ⟨δ, hδ1, hδ2⟩ := hδ i (by omega)
  obtain ⟨δ', hδ1', hδ2'⟩ := hδ i' hi'
  rw [← hδ2 j (by omega)] at ha
  rw [← hδ2' j' hj'] at ha'
  rw [← hδ2 j' hj', ← hδ2' j (by omega)]
  refine exchangeO hd hδ1 hδ1' ha ha' fun m p n q hp hq => ?_
  have hp' := isMWalk_of_isWalk hs hd hp
  have hq' := isMWalk_of_isWalk hs hd hq
  rcases hsep with hsep | hsep
  · have l1 := ht i i' hi hi'
    have l2 := ht i' j hsep (by omega)
    have l3 := ht j j' hj hj'
    have l4 := htN j' hj'
    exact meet_corners hM hN0 hmin (s := t i) (sa := t j') (sb := t j) (sc := t i')
      (a := N + t i - t j') (b := N + t i - t j) (c' := N + t i - t i') (by omega) (by omega)
      (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) hp' hq'
  · have l1 := ht j j' hj (by omega)
    have l2 := ht j' i hsep (by omega)
    have l3 := ht i i' hi hi'
    have l4 := htN i' hi'
    exact meet_corners hM hN0 hmin (s := t i) (sa := t j') (sb := t j) (sc := t i')
      (a := t i - t j') (b := t i - t j) (c' := N + t i - t i') (by omega) (by omega)
      (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) hp' hq'

end Option

end Monge

end PlanarFlow
