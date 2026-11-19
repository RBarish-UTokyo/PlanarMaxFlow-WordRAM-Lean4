module

public import PlanarFlow.BKMNW.DKPW

/-!
# The cut of the dual graph minus a simple path

`PlanarFlow/BKMNW/DKPW.lean` reduces the specification `MSSPSpec` of multiple-source shortest
paths in the dual graph minus a simple path `P` to the existence of a cut (`Cut`): a plane map in
the setting `MSSP.HypNN` of the data structure of Das, Kipouridis, Probst Gutenberg and
Wulff-Nilsen, containing a copy of the dual graph minus the darts `L` of `P`, with a ring of roots
inside the face that `P` opens. This file builds the cut and proves its properties, for a plane
map `M` with transitive rotations (`RotTrans`) and transitive faces (`FaceTrans`).

## The walk around the path

The dual map of `M` has the faces of `M` as vertices, `rot` as the boundary walk of its faces
and the vertices of `M` as faces. Deleting the darts of `P` merges the faces `p 0, …, p k` of the
dual into one face (Section 3 and Figure 1 of the article of Borradaile, Klein, Mozes, Nussbaum
and Wulff-Nilsen). Its boundary is traced by the walk around the path `tour`: around a vertex of
the path by the rotation, along a dart of the path by `next`. Every dart leaving the path is
visited (`tour_reach`): from `d j` the walk goes up the path and comes back by `rev (d j)`,
visiting every dart leaving `p (j + 1), …, p k` in between (`tour_up`).

## The cut

There is one root for every dart `t` leaving the path (`CutT`), standing for the face of `t`; the
roots are visited in the order of `tour` (`tourT`). The map `cutMap` has

* vertices `CutV`: the faces of `M` (the copy) and the roots;
* darts `CutD`: the copies of the darts off `L` (from `face e` to `face (rev e)`), and for every
  root `t` a pendant dart from `t` to the face of `t` with its reverse, and a dart of the ring from
  `t` to `tour t` with its reverse;
* faces `CutF`: the vertices of `M` off the path (untouched faces of the dual), for every root `t`
  the face between the pendant darts of `t` and `tour t` (a triangle when `t` lies on `P`, a
  quadrilateral through the copy of `t` otherwise), and the face of the ring.

Euler's formula holds by counting (`cutMap_isPlane`): the path has `k + 1` vertices and `2 k`
darts, so the copy has Euler characteristic `2`, and the roots add `r` vertices, `2 r` edges and
`r` faces. The rotation at a root has three darts, and the rotation at the copy of a face follows
the boundary walk of the face in `M`, with the reverse pendant darts inserted
(`cutMap_rotTrans`). The face of the ring is a simple cycle through all roots
(`cutMap_faceCycle`), the piece consists of the copies and the pendant darts, and no dart of it
enters a root.

## Main results

* `cutOf`, `exists_cut`: **a cut of the dual graph minus a simple path exists.**
* `msspPlane`, `msspPlane_spec`: **the data structure, run on the cut, meets `MSSPSpec`** for
  every plane map with transitive rotations and transitive faces.
* `msspPlane_spec_ofRotation`: the same for plane rotation systems.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace CombMap

variable {D V F : Type*} (M : CombMap D V F)

/-- **Transitive faces**: the darts of a face form one orbit of `next`. -/
def FaceTrans : Prop := ∀ d d', M.face d = M.face d' → ∃ k, M.next^[k] d = d'

end CombMap

namespace BKMNW

open Finset CombMap Function

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-! ### Iterates -/

/-- `y` is reached from `x` by iterating `f`. -/
def ItReach {α : Type*} (f : α → α) (x y : α) : Prop := ∃ n, f^[n] x = y

namespace ItReach

variable {α : Type*} {f : α → α} {x y z : α}

lemma rfl' : ItReach f x x := ⟨0, rfl⟩

lemma trans (h1 : ItReach f x y) (h2 : ItReach f y z) : ItReach f x z := by
  obtain ⟨m, rfl⟩ := h1
  obtain ⟨n, rfl⟩ := h2
  exact ⟨n + m, by rw [iterate_add_apply]⟩

lemma of_eq (h : f x = y) : ItReach f x y := ⟨1, h⟩

end ItReach

/-! ### The walk around a simple path -/

section Tour

variable (M : CombMap D V F) (L : List D)

/-- **The walk around the darts `L`**: along a dart of `L` (`next`), around the vertex otherwise
(`rot`). Around a simple path it visits every dart leaving the path, in the order of the boundary
of the face that the path opens in the dual. -/
def tour (x : D) : D := if x ∈ L then M.next x else M.rot x

variable {M L}

lemma tour_of_mem {x : D} (h : x ∈ L) : tour M L x = M.next x := by simp [tour, h]

lemma tour_of_not_mem {x : D} (h : x ∉ L) : tour M L x = M.rot x := by simp [tour, h]

lemma tour_injective (hL : ∀ e ∈ L, M.rev e ∈ L) : Injective (tour M L) := by
  have key : ∀ x y, x ∈ L → y ∉ L → tour M L x ≠ tour M L y := by
    intro x y hx hy h
    rw [tour_of_mem hx, tour_of_not_mem hy, CombMap.rot] at h
    have e := M.next_injective h
    exact hy (by rw [← M.rev_rev y, ← e]; exact hL x hx)
  intro x y h
  by_cases hx : x ∈ L <;> by_cases hy : y ∈ L
  · rw [tour_of_mem hx, tour_of_mem hy] at h; exact M.next_injective h
  · exact absurd h (key x y hx hy)
  · exact absurd h.symm (key y x hy hx)
  · rw [tour_of_not_mem hx, tour_of_not_mem hy] at h; exact M.rot_injective h

lemma rot_period_pos (x : D) : 0 < minimalPeriod M.rot x :=
  minimalPeriod_pos_of_mem_periodicPts (M.rot_injective.mem_periodicPts x)

lemma rot_iterate_ne {x : D} {i : ℕ} (h0 : 0 < i) (h1 : i < minimalPeriod M.rot x) :
    M.rot^[i] x ≠ x := fun h => by
  have := (iterate_eq_iterate_iff_of_lt_minimalPeriod h1 (rot_period_pos x)).1 h
  omega

lemma rot_iterate_inj {x : D} {i j : ℕ} (hi : i < minimalPeriod M.rot x)
    (hj : j < minimalPeriod M.rot x) (h : M.rot^[i] x = M.rot^[j] x) : i = j :=
  (iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).1 h

/-- With transitive rotations, every dart at the tail of `x` is `rot^[i] x` for some
`0 < i ≤ period`. -/
lemma rot_cover (hrot : M.RotTrans) {x y : D} (h : M.tail x = M.tail y) :
    ∃ i, 0 < i ∧ i ≤ minimalPeriod M.rot x ∧ M.rot^[i] x = y := by
  have hp := rot_period_pos (M := M) x
  obtain ⟨m, hm⟩ := hrot x y h
  by_cases h0 : m % minimalPeriod M.rot x = 0
  · refine ⟨minimalPeriod M.rot x, hp, le_rfl, ?_⟩
    rw [iterate_minimalPeriod, ← hm, ← iterate_mod_minimalPeriod_eq, h0]; rfl
  · exact ⟨_, Nat.pos_of_ne_zero h0, (Nat.mod_lt _ hp).le, by rw [iterate_mod_minimalPeriod_eq, hm]⟩

/-- Around a vertex, the walk follows the rotation while it meets no dart of `L`. -/
lemma tour_seg {x : D} {a c : ℕ} (h : ∀ i, a ≤ i → i < a + c → M.rot^[i] x ∉ L) :
    ItReach (tour M L) (M.rot^[a] x) (M.rot^[a + c] x) := by
  induction c with
  | zero => exact .rfl'
  | succ c ih =>
    refine (ih fun i h1 h2 => h i h1 (by omega)).trans (.of_eq ?_)
    rw [tour_of_not_mem (h _ le_self_add (by omega)), ← add_assoc, iterate_succ_apply']

end Tour

namespace SPath

variable {M : CombMap D V F} (P : SPath M)

/-- The darts of the path leaving `p j`: `d j` and `rev (d (j - 1))`. -/
lemma mem_darts_tail {e : D} (he : e ∈ P.darts) {j : ℕ} (hj : j ≤ P.k) (h : M.tail e = P.p j) :
    (j < P.k ∧ e = P.d j) ∨ ∃ i, j = i + 1 ∧ e = M.rev (P.d i) := by
  obtain ⟨i, hi, rfl | rfl⟩ := P.mem_darts.1 he
  · rw [P.tail_d i hi] at h
    obtain rfl := P.inj i hi.le j hj h
    exact Or.inl ⟨hi, rfl⟩
  · rw [M.tail_rev, P.head_d i hi] at h
    exact Or.inr ⟨i, (P.inj (i + 1) hi j hj h).symm, rfl⟩

lemma rev_mem_darts' : ∀ e ∈ P.darts, M.rev e ∈ P.darts := fun _ => P.rev_mem_darts

/-- The tails of the darts of the path are its vertices. -/
lemma tail_mem_darts {e : D} (he : e ∈ P.darts) : ∃ i ≤ P.k, M.tail e = P.p i := by
  obtain ⟨i, hi, rfl | rfl⟩ := P.mem_darts.1 he
  · exact ⟨i, hi.le, P.tail_d i hi⟩
  · exact ⟨i + 1, hi, by rw [M.tail_rev, P.head_d i hi]⟩

end SPath

section Orbit

variable {M : CombMap D V F}

/-- **Above `p j`, the walk around the path goes up along `d j` and comes back along its
reverse**, visiting every dart leaving `p (j + 1), …, p k` in between. -/
theorem tour_up (hrot : M.RotTrans) (P : SPath M) :
    ∀ m j, j + m + 1 = P.k → ItReach (tour M P.darts) (P.d j) (M.rev (P.d j)) ∧
      ∀ t i, j < i → i ≤ P.k → M.tail t = P.p i → ItReach (tour M P.darts) (P.d j) t := by
  intro m
  induction m with
  | zero =>
    intro j hj
    have hjk : j < P.k := by omega
    have hx0 : M.tail (M.rev (P.d j)) = P.p (j + 1) := by rw [M.tail_rev, P.head_d j hjk]
    have hp := rot_period_pos (M := M) (M.rev (P.d j))
    have h0 : ItReach (tour M P.darts) (P.d j) (M.rot^[1] (M.rev (P.d j))) :=
      .of_eq (by rw [tour_of_mem (P.d_mem j hjk), iterate_one, CombMap.rot, M.rev_rev])
    have hnot : ∀ i, 1 ≤ i → i < minimalPeriod M.rot (M.rev (P.d j)) →
        M.rot^[i] (M.rev (P.d j)) ∉ P.darts := by
      intro i h1 h2 hm
      have ht : M.tail (M.rot^[i] (M.rev (P.d j))) = P.p (j + 1) := by
        rw [M.tail_rot_iterate, hx0]
      rcases P.mem_darts_tail hm (by omega) ht with ⟨h3, -⟩ | ⟨i', h3, h4⟩
      · omega
      · obtain rfl : i' = j := by omega
        exact rot_iterate_ne (by omega) h2 h4
    have seg : ∀ i', 0 < i' → i' ≤ minimalPeriod M.rot (M.rev (P.d j)) →
        ItReach (tour M P.darts) (P.d j) (M.rot^[i'] (M.rev (P.d j))) := by
      intro i' h1 h2
      have := tour_seg (L := P.darts) (a := 1) (c := i' - 1) (x := M.rev (P.d j))
        (fun i hi1 hi2 => hnot i hi1 (by omega))
      rw [show 1 + (i' - 1) = i' by omega] at this
      exact h0.trans this
    refine ⟨?_, fun t i hi1 hi2 ht => ?_⟩
    · have := seg _ hp le_rfl
      rwa [iterate_minimalPeriod] at this
    · obtain rfl : i = j + 1 := by omega
      obtain ⟨i', h1, h2, rfl⟩ := rot_cover hrot (hx0.trans ht.symm)
      exact seg i' h1 h2
  | succ m ih =>
    intro j hj
    obtain ⟨ih1, ih2⟩ := ih (j + 1) (by omega)
    have hjk : j + 1 < P.k := by omega
    have hx0 : M.tail (M.rev (P.d j)) = P.p (j + 1) := by rw [M.tail_rev, P.head_d j (by omega)]
    have hp := rot_period_pos (M := M) (M.rev (P.d j))
    have h0 : ItReach (tour M P.darts) (P.d j) (M.rot^[1] (M.rev (P.d j))) :=
      .of_eq (by rw [tour_of_mem (P.d_mem j (by omega)), iterate_one, CombMap.rot, M.rev_rev])
    obtain ⟨m', hm1, hm2, hm⟩ := rot_cover hrot (hx0.trans (P.tail_d (j + 1) hjk).symm)
    have hmω : m' < minimalPeriod M.rot (M.rev (P.d j)) := by
      refine lt_of_le_of_ne hm2 fun h => P.d_ne_rev hjk (by omega : j < P.k) ?_
      rw [← hm, h, iterate_minimalPeriod]
    have hnot : ∀ i, 1 ≤ i → i < minimalPeriod M.rot (M.rev (P.d j)) → i ≠ m' →
        M.rot^[i] (M.rev (P.d j)) ∉ P.darts := by
      intro i h1 h2 h3 hmem
      have ht : M.tail (M.rot^[i] (M.rev (P.d j))) = P.p (j + 1) := by
        rw [M.tail_rot_iterate, hx0]
      rcases P.mem_darts_tail hmem (by omega) ht with ⟨-, h4⟩ | ⟨i', h4, h5⟩
      · exact h3 (rot_iterate_inj h2 hmω (h4.trans hm.symm))
      · obtain rfl : i' = j := by omega
        exact rot_iterate_ne (by omega) h2 h5
    -- up to `d (j + 1)`
    have seg1 : ∀ i', 0 < i' → i' ≤ m' →
        ItReach (tour M P.darts) (P.d j) (M.rot^[i'] (M.rev (P.d j))) := by
      intro i' h1 h2
      have := tour_seg (L := P.darts) (a := 1) (c := i' - 1) (x := M.rev (P.d j))
        (fun i hi1 hi2 => hnot i hi1 (by omega) (by omega))
      rw [show 1 + (i' - 1) = i' by omega] at this
      exact h0.trans this
    -- back from `rev (d (j + 1))`
    have h1 : ItReach (tour M P.darts) (P.d j) (M.rot^[m' + 1] (M.rev (P.d j))) := by
      have e1 : ItReach (tour M P.darts) (P.d j) (M.rev (P.d (j + 1))) := by
        have := seg1 m' hm1 le_rfl
        rw [hm] at this
        exact this.trans ih1
      exact e1.trans (.of_eq (by
        rw [tour_of_mem (P.rev_d_mem _ hjk), iterate_succ_apply', hm, CombMap.rot]))
    have seg2 : ∀ i', m' < i' → i' ≤ minimalPeriod M.rot (M.rev (P.d j)) →
        ItReach (tour M P.darts) (P.d j) (M.rot^[i'] (M.rev (P.d j))) := by
      intro i' h2 h3
      have := tour_seg (L := P.darts) (a := m' + 1) (c := i' - (m' + 1)) (x := M.rev (P.d j))
        (fun i hi1 hi2 => hnot i (by omega) (by omega) (by omega))
      rw [show m' + 1 + (i' - (m' + 1)) = i' by omega] at this
      exact h1.trans this
    refine ⟨?_, fun t i hi1 hi2 ht => ?_⟩
    · have := seg2 _ hmω le_rfl
      rwa [iterate_minimalPeriod] at this
    · rcases Nat.lt_or_ge (j + 1) i with h | h
      · have := seg1 m' hm1 le_rfl
        rw [hm] at this
        exact this.trans (ih2 t i h hi2 ht)
      · obtain rfl : i = j + 1 := by omega
        obtain ⟨i', h1, h2, rfl⟩ := rot_cover hrot (hx0.trans ht.symm)
        rcases Nat.lt_or_ge m' i' with h3 | h3
        · exact seg2 i' h3 h2
        · exact seg1 i' h1 h3

/-- **The walk around a simple path visits every dart leaving the path**, from `d 0`. -/
theorem tour_reach (hrot : M.RotTrans) (P : SPath M) (hk : 0 < P.k) {t : D} {i : ℕ}
    (hi : i ≤ P.k) (ht : M.tail t = P.p i) : ItReach (tour M P.darts) (P.d 0) t := by
  obtain ⟨hup1, hup2⟩ := tour_up hrot P (P.k - 1) 0 (by omega)
  rcases Nat.eq_zero_or_pos i with rfl | h
  · have hx0 : M.tail (P.d 0) = P.p 0 := P.tail_d 0 hk
    have h0 : ItReach (tour M P.darts) (P.d 0) (M.rot^[1] (P.d 0)) :=
      hup1.trans (.of_eq (by rw [tour_of_mem (P.rev_d_mem 0 hk), iterate_one, CombMap.rot]))
    have hnot : ∀ i, 1 ≤ i → i < minimalPeriod M.rot (P.d 0) → M.rot^[i] (P.d 0) ∉ P.darts := by
      intro i h1 h2 hm
      have ht : M.tail (M.rot^[i] (P.d 0)) = P.p 0 := by rw [M.tail_rot_iterate, hx0]
      rcases P.mem_darts_tail hm (by omega) ht with ⟨-, h4⟩ | ⟨i', h4, -⟩
      · exact rot_iterate_ne (by omega) h2 h4
      · omega
    obtain ⟨i', h1, h2, rfl⟩ := rot_cover hrot (hx0.trans ht.symm)
    have := tour_seg (L := P.darts) (a := 1) (c := i' - 1) (x := P.d 0)
      (fun i hi1 hi2 => hnot i hi1 (by omega))
    rw [show 1 + (i' - 1) = i' by omega] at this
    exact h0.trans this
  · exact hup2 t i h hi ht

end Orbit

/-! ### The map -/

section Map

variable (M : CombMap D V F) (L : List D)

/-- The tails of the darts of `L` (for a path, its vertices: the faces of the dual merged into
one). -/
def cutS : Finset V := (L.map M.tail).toFinset

/-- The darts leaving `cutS`: one root for each of them. -/
abbrev CutT := {e : D // M.tail e ∈ cutS M L}

/-- The darts of the cut: the copies of the darts off `L`, and for every root `t` the pendant
dart from the root to the face of `t`, its reverse, the dart of the ring from `t` to the next
root `tour t`, and its reverse. -/
abbrev CutD := {e : D // e ∉ L} ⊕ CutT M L ⊕ CutT M L ⊕ CutT M L ⊕ CutT M L

/-- The vertices of the cut: the faces of `M` and the roots. -/
abbrev CutV := F ⊕ CutT M L

/-- The faces of the cut: the vertices of `M` off `cutS`, one face between consecutive roots, and
the face of the ring. -/
abbrev CutF := {v : V // v ∉ cutS M L} ⊕ CutT M L ⊕ Unit

variable {M L}

lemma mem_cutS {v : V} : v ∈ cutS M L ↔ ∃ e ∈ L, M.tail e = v := by simp [cutS]

lemma tail_mem_cutS {e : D} (h : e ∈ L) : M.tail e ∈ cutS M L := mem_cutS.2 ⟨e, h, rfl⟩

variable (hL : ∀ e ∈ L, M.rev e ∈ L)
include hL

lemma tail_tour (x : D) : M.tail (tour M L x) ∈ cutS M L ↔ M.tail x ∈ cutS M L := by
  by_cases hx : x ∈ L
  · rw [tour_of_mem hx, M.tail_next]
    exact iff_of_true (tail_mem_cutS (hL x hx)) (tail_mem_cutS hx)
  · rw [tour_of_not_mem hx, M.tail_rot]

lemma rev_not_mem {e : D} (he : e ∉ L) : M.rev e ∉ L := fun h => he (by
  have := hL _ h; rwa [M.rev_rev] at this)

lemma not_mem_of_tail {e : D} (he : M.tail e ∉ cutS M L) : e ∉ L := fun h => he (tail_mem_cutS h)

/-- The walk around `L`, as a permutation of the roots. -/
noncomputable def tourT : Equiv.Perm (CutT M L) :=
  Equiv.Perm.subtypePerm
    (Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (tour_injective hL))) (tail_tour hL)

@[simp] lemma tourT_val (t : CutT M L) : (tourT hL t).1 = tour M L t.1 := rfl

lemma tourT_mk (x : D) (h : M.tail x ∈ cutS M L) :
    tourT hL ⟨x, h⟩ = ⟨tour M L x, (tail_tour hL x).2 h⟩ := rfl

lemma tourT_iterate_val (n : ℕ) (t : CutT M L) : ((tourT hL)^[n] t).1 = (tour M L)^[n] t.1 := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, iterate_succ_apply, ih, tourT_val]

omit hL in
/-- The reverse of a dart of the cut. -/
def cutRev (hL : ∀ e ∈ L, M.rev e ∈ L) : CutD M L → CutD M L
  | .inl e => .inl ⟨M.rev e.1, rev_not_mem hL e.2⟩
  | .inr (.inl t) => .inr (.inr (.inl t))
  | .inr (.inr (.inl t)) => .inr (.inl t)
  | .inr (.inr (.inr (.inl t))) => .inr (.inr (.inr (.inr t)))
  | .inr (.inr (.inr (.inr t))) => .inr (.inr (.inr (.inl t)))

omit hL in
/-- The tail of a dart of the cut. -/
noncomputable def cutTail (hL : ∀ e ∈ L, M.rev e ∈ L) : CutD M L → CutV M L
  | .inl e => .inl (M.face e.1)
  | .inr (.inl t) => .inr t
  | .inr (.inr (.inl t)) => .inl (M.face t.1)
  | .inr (.inr (.inr (.inl t))) => .inr t
  | .inr (.inr (.inr (.inr t))) => .inr (tourT hL t)

omit hL in
/-- The next dart along the boundary walk of a face of the cut. -/
noncomputable def cutNext (hL : ∀ e ∈ L, M.rev e ∈ L) : CutD M L → CutD M L
  | .inl e => if h : M.tail e.1 ∈ cutS M L then .inr (.inr (.inl (tourT hL ⟨e.1, h⟩)))
      else .inl ⟨M.rot e.1, not_mem_of_tail hL (by rwa [M.tail_rot])⟩
  | .inr (.inl t) => if h : t.1 ∈ L then .inr (.inr (.inl (tourT hL t))) else .inl ⟨t.1, h⟩
  | .inr (.inr (.inl t)) => .inr (.inr (.inr (.inr ((tourT hL).symm t))))
  | .inr (.inr (.inr (.inl t))) => .inr (.inr (.inr (.inl (tourT hL t))))
  | .inr (.inr (.inr (.inr t))) => .inr (.inl t)

omit hL in
/-- The face of a dart of the cut. -/
noncomputable def cutFace (hL : ∀ e ∈ L, M.rev e ∈ L) : CutD M L → CutF M L
  | .inl e => if h : M.tail e.1 ∈ cutS M L then .inr (.inl ⟨e.1, h⟩) else .inl ⟨M.tail e.1, h⟩
  | .inr (.inl t) => .inr (.inl t)
  | .inr (.inr (.inl t)) => .inr (.inl ((tourT hL).symm t))
  | .inr (.inr (.inr (.inl _))) => .inr (.inr ())
  | .inr (.inr (.inr (.inr t))) => .inr (.inl t)

lemma cutNext_injective : Injective (cutNext hL) := by
  intro x y h
  rcases x with ⟨e, he⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ <;>
    rcases y with ⟨e', he'⟩ | ⟨t', ht'⟩ | ⟨t', ht'⟩ | ⟨t', ht'⟩ | ⟨t', ht'⟩ <;>
    simp only [cutNext] at h
  all_goals (try split_ifs at h) <;> simp at h ⊢
  all_goals first
    | exact h
    | exact M.rot_injective h
    | (subst h; exact he ‹_›)
    | (subst h; exact he' ‹_›)
    | (rename_i h1 h2; exact h1 (by rw [← M.tail_rot, h]; exact ht'))
    | (rename_i h1 h2; exact h2 (by rw [← M.tail_rot, ← h]; exact ht))

/-- **The cut** as a combinatorial map. -/
noncomputable def cutMap : CombMap (CutD M L) (CutV M L) (CutF M L) where
  rev := cutRev hL
  rev_rev d := by rcases d with e | t | t | t | t <;> simp [cutRev, M.rev_rev]
  rev_ne d := by
    rcases d with e | t | t | t | t <;> simp [cutRev]
    exact fun h => M.rev_ne e.1 (congrArg Subtype.val h)
  tail := cutTail hL
  face := cutFace hL
  next := cutNext hL
  next_injective := cutNext_injective hL
  face_next d := by
    rcases d with ⟨e, he⟩ | ⟨t, ht⟩ | t | t | t <;> simp only [cutNext]
    · by_cases h : M.tail e ∈ cutS M L
      · simp [h, cutFace]
      · simp [h, cutFace, M.tail_rot]
    · by_cases h : t ∈ L
      · simp [h, cutFace]
      · simp [h, cutFace, ht]
    all_goals simp [cutFace]
  tail_next d := by
    rcases d with ⟨e, he⟩ | ⟨t, ht⟩ | t | t | t <;> simp only [cutNext]
    · by_cases h : M.tail e ∈ cutS M L
      · simp [h, cutTail, cutRev, tour_of_not_mem he, M.face_rot]
      · simp [h, cutTail, cutRev, M.face_rot]
    · by_cases h : t ∈ L
      · simp [h, cutTail, cutRev, tour_of_mem h, M.face_next]
      · simp [h, cutTail, cutRev]
    all_goals simp [cutTail, cutRev]

end Map

/-! ### Transitive rotations -/

section Rot

variable {M : CombMap D V F} {L : List D} (hL : ∀ e ∈ L, M.rev e ∈ L)

/-- The first dart of the cut leaving the copy of `face x` for the dart `x`: the reverse pendant
dart of the root `x`, or the copy of `x`. -/
noncomputable def cutFirst (x : D) : CutD M L :=
  if h : M.tail x ∈ cutS M L then .inr (.inr (.inl ⟨x, h⟩)) else .inl ⟨x, not_mem_of_tail hL h⟩

lemma cutMap_rot (d : CutD M L) : (cutMap hL).rot d = cutNext hL (cutRev hL d) := rfl

lemma rot_inl {x : D} (hx : x ∉ L) :
    ItReach (cutMap hL).rot (.inl ⟨x, hx⟩) (cutFirst hL (M.next x)) := by
  refine .of_eq ?_
  rw [cutMap_rot]
  have e1 : M.rot (M.rev x) = M.next x := by rw [CombMap.rot, M.rev_rev]
  have e2 : M.tail (M.next x) = M.head x := M.tail_next x
  by_cases h : M.head x ∈ cutS M L
  · have h' : M.tail (M.next x) ∈ cutS M L := e2 ▸ h
    simp [cutRev, cutNext, cutFirst, h, h', tourT_mk, tour_of_not_mem (rev_not_mem hL hx), e1]
  · have h' : M.tail (M.next x) ∉ cutS M L := e2 ▸ h
    simp [cutRev, cutNext, cutFirst, h, h', e1]

lemma rot_first (x : D) : ItReach (cutMap hL).rot (cutFirst hL x) (cutFirst hL (M.next x)) := by
  by_cases h : M.tail x ∈ cutS M L
  · by_cases hx : x ∈ L
    · refine .of_eq ?_
      have h' : M.tail (M.next x) ∈ cutS M L := by
        rw [M.tail_next]; exact tail_mem_cutS (hL x hx)
      simp [cutMap_rot, cutRev, cutNext, cutFirst, h, h', hx, tourT_mk, tour_of_mem hx]
    · refine .trans (.of_eq ?_) (rot_inl hL hx)
      simp [cutMap_rot, cutRev, cutNext, cutFirst, h, hx]
  · have := rot_inl hL (not_mem_of_tail hL h)
    simpa [cutFirst, h] using this

lemma rot_first_iterate (m : ℕ) (x : D) :
    ItReach (cutMap hL).rot (cutFirst hL x) (cutFirst hL (M.next^[m] x)) := by
  induction m generalizing x with
  | zero => exact .rfl'
  | succ m ih => rw [iterate_succ_apply]; exact (rot_first hL x).trans (ih _)

lemma rot_at_face {d : CutD M L} {f : F} (h : (cutMap hL).tail d = .inl f) :
    ∃ x, M.face x = f ∧ ItReach (cutMap hL).rot (cutFirst hL x) d ∧
      ItReach (cutMap hL).rot d (cutFirst hL (M.next x)) := by
  rcases d with ⟨e, he⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ <;>
    simp [cutMap, cutTail] at h
  · subst h
    refine ⟨e, rfl, ?_, rot_inl hL he⟩
    by_cases h : M.tail e ∈ cutS M L
    · refine .of_eq ?_
      simp [cutFirst, h, cutMap_rot, cutRev, cutNext, he]
    · simpa [cutFirst, h] using (ItReach.rfl' : ItReach (cutMap hL).rot (.inl ⟨e, he⟩) _)
  · subst h
    have e1 : cutFirst hL t = .inr (.inr (.inl ⟨t, ht⟩)) := by simp [cutFirst, ht]
    exact ⟨t, rfl, by rw [e1]; exact .rfl', by rw [← e1]; exact rot_first hL t⟩

lemma rot_at_root {d : CutD M L} {t : CutT M L} (h : (cutMap hL).tail d = .inr t) :
    ItReach (cutMap hL).rot d (.inr (.inl t)) ∧ ItReach (cutMap hL).rot (.inr (.inl t)) d := by
  have s1 : ∀ t : CutT M L, (cutMap hL).rot (.inr (.inl t)) =
      .inr (.inr (.inr (.inr ((tourT hL).symm t)))) := fun t => rfl
  have s2 : ∀ t : CutT M L, (cutMap hL).rot (.inr (.inr (.inr (.inr t)))) =
      .inr (.inr (.inr (.inl (tourT hL t)))) := fun t => rfl
  have s3 : ∀ t : CutT M L, (cutMap hL).rot (.inr (.inr (.inr (.inl t)))) = .inr (.inl t) :=
    fun t => rfl
  rcases d with ⟨e, he⟩ | s | s | s | s <;> simp [cutMap, cutTail] at h
  · subst h; exact ⟨.rfl', .rfl'⟩
  · subst h
    refine ⟨.of_eq (s3 _), ⟨2, ?_⟩⟩
    rw [iterate_succ_apply, iterate_one, s1, s2, Equiv.apply_symm_apply]
  · subst h
    refine ⟨⟨2, ?_⟩, .of_eq ?_⟩
    · rw [iterate_succ_apply, iterate_one, s2, s3]
    · rw [s1, Equiv.symm_apply_apply]

/-- **The cut has transitive rotations**, if the faces of `M` are transitive. -/
theorem cutMap_rotTrans (hface : M.FaceTrans) : (cutMap hL).RotTrans := by
  intro d d' h
  rcases hd : (cutMap hL).tail d with f | t
  · obtain ⟨x, hx, -, h1⟩ := rot_at_face hL hd
    obtain ⟨x', hx', h2, -⟩ := rot_at_face hL (h.symm.trans hd)
    obtain ⟨m, hm⟩ := hface (M.next x) x' (by rw [M.face_next, hx, hx'])
    have := rot_first_iterate hL m (M.next x)
    rw [hm] at this
    exact (h1.trans this).trans h2
  · exact (rot_at_root hL hd).1.trans (rot_at_root hL (h.symm.trans hd)).2

end Rot

/-! ### Planarity -/

section Plane

open Relation

lemma reflTransGen_symm' {α : Type*} {r : α → α → Prop} (hr : ∀ a b, r a b → r b a) {a b : α}
    (h : ReflTransGen r a b) : ReflTransGen r b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (hr _ _ hbc) ih

variable {M : CombMap D V F} {L : List D} (hL : ∀ e ∈ L, M.rev e ∈ L) (t0 : CutT M L)

lemma cutMap_adj_symm (a b : CutV M L) (h : (cutMap hL).Adj a b) : (cutMap hL).Adj b a := by
  obtain ⟨d, rfl, rfl⟩ := h
  exact ⟨(cutMap hL).rev d, rfl, (cutMap hL).head_rev d⟩

lemma cutMap_dualAdj_symm (a b : CutF M L) (h : (cutMap hL).DualAdj a b) :
    (cutMap hL).DualAdj b a := by
  obtain ⟨d, rfl, rfl⟩ := h
  exact ⟨(cutMap hL).rev d, rfl, by rw [(cutMap hL).rev_rev]⟩

/-- The ring connects the roots. -/
lemma root_conn (n : ℕ) :
    ReflTransGen (cutMap hL).Adj (.inr ((tourT hL)^[n] t0)) (.inr t0) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    refine .head ⟨.inr (.inr (.inr (.inr ((tourT hL)^[n] t0)))), ?_, rfl⟩ ih
    rw [iterate_succ_apply']; rfl

/-- **The cut is connected.** -/
lemma cutMap_conn (hM : M.IsPlane) (horb : ∀ t, ItReach (tourT hL) t0 t) (a b : CutV M L) :
    ReflTransGen (cutMap hL).Adj a b := by
  have hroot : ∀ t, ReflTransGen (cutMap hL).Adj (.inr t) (.inr t0) := fun t => by
    obtain ⟨n, rfl⟩ := horb t; exact root_conn hL t0 n
  have key : ∀ f, ReflTransGen M.DualAdj f (M.face t0.1) →
      ReflTransGen (cutMap hL).Adj (.inl f) (.inr t0) := by
    intro f hf
    induction hf using Relation.ReflTransGen.head_induction_on with
    | refl => exact .single ⟨.inr (.inr (.inl t0)), rfl, rfl⟩
    | head h _ ih =>
      obtain ⟨d, rfl, rfl⟩ := h
      by_cases hd : d ∈ L
      · exact .head ⟨.inr (.inr (.inl ⟨d, tail_mem_cutS hd⟩)), rfl, rfl⟩ (hroot _)
      · exact .head ⟨.inl ⟨d, hd⟩, rfl, rfl⟩ ih
  have hall : ∀ a, ReflTransGen (cutMap hL).Adj a (.inr t0) := by
    rintro (f | t)
    · exact key f (hM.dualConn _ _)
    · exact hroot t
  exact (hall a).trans (reflTransGen_symm' (cutMap_adj_symm hL) (hall b))

/-- **The dual of the cut is connected.** -/
lemma cutMap_dualConn (t0 : CutT M L) (hM : M.IsPlane) (a b : CutF M L) :
    ReflTransGen (cutMap hL).DualAdj a b := by
  have hQ : ∀ t, ReflTransGen (cutMap hL).DualAdj (.inr (.inl t)) (.inr (.inr ())) := fun t =>
    .single ⟨.inr (.inr (.inr (.inr t))), rfl, rfl⟩
  have key : ∀ v, ReflTransGen M.Adj v (M.tail t0.1) → ∀ hv : v ∉ cutS M L,
      ReflTransGen (cutMap hL).DualAdj (.inl ⟨v, hv⟩) (.inr (.inr ())) := by
    intro v hv
    induction hv using Relation.ReflTransGen.head_induction_on with
    | refl => intro h; exact absurd t0.2 h
    | head h _ ih =>
      intro hv
      obtain ⟨d, rfl, rfl⟩ := h
      have hd : d ∉ L := not_mem_of_tail hL hv
      have e1 : (cutMap hL).face (.inl ⟨d, hd⟩) = .inl ⟨M.tail d, hv⟩ := by
        simp [cutMap, cutFace, hv]
      by_cases hw : M.head d ∈ cutS M L
      · refine .head ⟨.inl ⟨d, hd⟩, e1, ?_⟩ (hQ ⟨M.rev d, hw⟩)
        simp [cutMap, cutFace, cutRev, hw]
      · refine .head ⟨.inl ⟨d, hd⟩, e1, ?_⟩ (ih hw)
        simp [cutMap, cutFace, cutRev, hw]
  have hall : ∀ a, ReflTransGen (cutMap hL).DualAdj a (.inr (.inr ())) := by
    rintro (⟨v, hv⟩ | t | ⟨⟩)
    · exact key v (hM.conn _ _) hv
    · exact hQ t
    · exact .refl
  exact (hall a).trans (reflTransGen_symm' (cutMap_dualAdj_symm hL) (hall b))

lemma card_not_mem_list {α : Type*} [Fintype α] [DecidableEq α] (s : List α) :
    Fintype.card {x // x ∉ s} = Fintype.card α - s.toFinset.card := by
  rw [← Fintype.card_coe, ← Fintype.card_subtype_compl]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (by simp))

/-- **The cut is plane**, when `L` has two darts for every vertex of `cutS` but one (a tree). -/
theorem cutMap_isPlane (hM : M.IsPlane) (horb : ∀ t, ItReach (tourT hL) t0 t)
    (hcount : L.toFinset.card + 2 = 2 * (cutS M L).card) : (cutMap hL).IsPlane where
  nonempty := ⟨.inr t0⟩
  conn := cutMap_conn hL t0 hM horb
  dualConn := cutMap_dualConn hL t0 hM
  euler := by
    have e := hM.euler
    have h1 : (cutS M L).card ≤ Fintype.card V := card_le_univ _
    have h2 : L.toFinset.card ≤ Fintype.card D := card_le_univ _
    simp only [Fintype.card_sum, Fintype.card_unit, card_not_mem_list,
      Fintype.card_subtype_compl, Fintype.card_coe]
    omega

end Plane

/-! ### The cut -/

section Build

variable (M : CombMap D V F) (L : List D)

/-- The darts of the piece: the copies of the darts off `L` and the pendant darts. -/
def inPiece : CutD M L → Bool
  | .inl _ => true
  | .inr (.inl _) => true
  | _ => false

/-- The piece of the cut. -/
def cutPiece : Finset (CutD M L) := univ.filter fun d => inPiece M L d = true

omit [Fintype V] in
lemma mem_cutPiece {d : CutD M L} : d ∈ cutPiece M L ↔ inPiece M L d = true := by
  simp [cutPiece]

/-- The lengths of the cut: those of `M` on the copies, `0` elsewhere. -/
def cutLen (ℓ : D → ℤ) : CutD M L → ℤ
  | .inl e => ℓ e.1
  | _ => 0

variable {M L} (hL : ∀ e ∈ L, M.rev e ∈ L) (t0 : CutT M L)

/-- The boundary walk of the face of the ring: the darts of the ring from the roots
`tour^[i] t0`. -/
noncomputable def cutG (i : ℕ) : CutD M L := .inr (.inr (.inr (.inl ((tourT hL)^[i] t0))))

lemma tourT_period_pos : 0 < minimalPeriod (tourT hL) t0 :=
  minimalPeriod_pos_of_mem_periodicPts ((tourT hL).injective.mem_periodicPts t0)

lemma tourT_orbit (horb : ∀ t, ItReach (tourT hL) t0 t) (t : CutT M L) :
    ∃ j < minimalPeriod (tourT hL) t0, (tourT hL)^[j] t0 = t := by
  obtain ⟨m, rfl⟩ := horb t
  exact ⟨m % _, Nat.mod_lt _ (tourT_period_pos hL t0), iterate_mod_minimalPeriod_eq⟩

/-- **The face of the ring is a simple cycle.** -/
lemma cutMap_faceCycle (htwo : tourT hL t0 ≠ t0) :
    MSSP.FaceCycle (cutMap hL) (minimalPeriod (tourT hL) t0) (cutG hL t0) where
  two_le := by
    have := tourT_period_pos hL t0
    by_contra h
    have h1 : minimalPeriod (tourT hL) t0 = 1 := by omega
    have := iterate_minimalPeriod (f := tourT hL) (x := t0)
    rw [h1, iterate_one] at this
    exact htwo this
  face _ _ := rfl
  next i _ := by
    simp only [cutMap, cutG, cutNext]
    rw [iterate_mod_minimalPeriod_eq, iterate_succ_apply']
  inj i hi j hj h := by
    simp only [cutMap, cutTail, cutG, Sum.inr.injEq] at h
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).1 h

/-- **The cut of the dual graph minus `L`**, from a plane map with transitive faces, when `L` is
closed under reversal, the walk around `L` visits every root, and `L` is a tree. -/
noncomputable def cutOf (ℓ : D → ℤ) (hnn : ∀ e, e ∉ L → 0 ≤ ℓ e) (hM : M.IsPlane)
    (hface : M.FaceTrans) (horb : ∀ t, ItReach (tourT hL) t0 t) (htwo : tourT hL t0 ≠ t0)
    (hcount : L.toFinset.card + 2 = 2 * (cutS M L).card) :
    Cut M ℓ L (CutD M L) (CutV M L) (CutF M L) where
  map := cutMap hL
  k := minimalPeriod (tourT hL) t0
  g := cutG hL t0
  piece := cutPiece M L
  len := cutLen M L ℓ
  hyp :=
    { plane := cutMap_isPlane hL t0 hM horb hcount
      rot := cutMap_rotTrans hL hface
      face := cutMap_faceCycle hL t0 htwo
      nonneg := by
        rintro (⟨e, he⟩ | t | t | t | t) hd <;>
          simp [mem_cutPiece, inPiece, cutLen] at hd ⊢
        exact hnn e he
      noIn := by
        rintro (e | t | t | t | t) hd ⟨i, -, h⟩ <;>
          simp [mem_cutPiece, inPiece, cutMap, cutG, cutTail, CombMap.head, cutRev] at hd h }
  vx := Sum.inl
  vx_inj := Sum.inl_injective
  arc e := ⟨.inl e, by simp [mem_cutPiece, inPiece]⟩
  tail_arc _ := rfl
  head_arc _ := rfl
  len_arc _ := rfl
  root j := M.face ((tourT hL)^[j] t0).1
  root_ne j _ y := by simp [cutMap, cutTail, cutG]
  pend j _ := ⟨.inr (.inl ((tourT hL)^[j] t0)), by simp [mem_cutPiece, inPiece], rfl⟩
  cover := by
    rintro (e | t | t | t | t) hd <;> simp [mem_cutPiece, inPiece] at hd
    · exact Or.inl ⟨e, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := tourT_orbit hL t0 horb t
      exact Or.inr ⟨j, hj, rfl, rfl, rfl⟩
  srcs x hx := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
    obtain ⟨j, hj, h⟩ := tourT_orbit hL t0 horb ⟨e, tail_mem_cutS he⟩
    exact ⟨j, hj, by simp only [h]⟩

end Build

/-! ### The cut of the dual graph minus a simple path -/

section PathCut

variable {M : CombMap D V F}

lemma SPath.cutS_eq (P : SPath M) (hk : 0 < P.k) :
    cutS M P.darts = (range (P.k + 1)).image P.p := by
  ext v
  rw [mem_cutS, mem_image]
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨i, hi, h⟩ := P.tail_mem_darts he
    exact ⟨i, mem_range.2 (by omega), h.symm⟩
  · rintro ⟨i, hi, rfl⟩
    rw [mem_range] at hi
    rcases Nat.lt_or_ge i P.k with h | h
    · exact ⟨P.d i, P.d_mem i h, P.tail_d i h⟩
    · obtain rfl : i = P.k := by omega
      refine ⟨M.rev (P.d (P.k - 1)), P.rev_d_mem _ (by omega), ?_⟩
      rw [M.tail_rev, P.head_d _ (by omega), Nat.sub_add_cancel hk]

/-- A simple path of `k ≥ 1` darts has `k + 1` vertices. -/
lemma SPath.card_cutS (P : SPath M) (hk : 0 < P.k) : (cutS M P.darts).card = P.k + 1 := by
  rw [P.cutS_eq hk, card_image_of_injOn, card_range]
  intro i hi j hj h
  exact P.inj i (by simp at hi; omega) j (by simp at hj; omega) h

/-- A simple path of `k` darts has `2 k` darts and reverses. -/
lemma SPath.card_darts (P : SPath M) : P.darts.toFinset.card = 2 * P.k := by
  have e : P.darts.toFinset =
      (range P.k).image P.d ∪ (range P.k).image (fun j => M.rev (P.d j)) := by
    ext e
    simp only [List.mem_toFinset, mem_union, mem_image, mem_range, P.mem_darts]
    constructor
    · rintro ⟨j, hj, rfl | rfl⟩
      · exact Or.inl ⟨j, hj, rfl⟩
      · exact Or.inr ⟨j, hj, rfl⟩
    · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨j, hj, Or.inl rfl⟩
      · exact ⟨j, hj, Or.inr rfl⟩
  have h1 : ((range P.k).image P.d).card = P.k := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj h
    exact P.d_inj (by simpa using hi) (by simpa using hj) h
  have h2 : ((range P.k).image (fun j => M.rev (P.d j))).card = P.k := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj h
    exact P.d_inj (by simpa using hi) (by simpa using hj) (M.rev_injective h)
  have hd : Disjoint ((range P.k).image P.d) ((range P.k).image (fun j => M.rev (P.d j))) := by
    rw [disjoint_left]
    rintro _ h3 h4
    obtain ⟨i, hi, rfl⟩ := mem_image.1 h3
    obtain ⟨j, hj, h⟩ := mem_image.1 h4
    exact P.d_ne_rev (by simpa using hi) (by simpa using hj) h.symm
  rw [e, card_union_of_disjoint hd, h1, h2]
  ring

/-- **A cut of the dual graph minus a simple path exists**, for a plane map with transitive
rotations and transitive faces, and lengths that are nonnegative off the path. -/
theorem exists_cut (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) (P : SPath M)
    (ℓ : D → ℤ) (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e) (hk : 0 < P.k) :
    Nonempty (Cut M ℓ P.darts (CutD M P.darts) (CutV M P.darts) (CutF M P.darts)) := by
  have hL := P.rev_mem_darts'
  refine ⟨cutOf hL ⟨P.d 0, tail_mem_cutS (P.d_mem 0 hk)⟩ ℓ hnn hM hface ?_ ?_ ?_⟩
  · intro t
    obtain ⟨e, he, h⟩ := mem_cutS.1 t.2
    obtain ⟨i, hi, hi'⟩ := P.tail_mem_darts he
    obtain ⟨n, hn⟩ := tour_reach hrot P hk hi (h.symm.trans hi')
    exact ⟨n, Subtype.ext (by rw [tourT_iterate_val]; exact hn)⟩
  · intro h
    have h1 := congrArg Subtype.val h
    rw [tourT_val, tour_of_mem (P.d_mem 0 hk)] at h1
    have h2 := congrArg M.tail h1
    rw [M.tail_next, M.tail_rev, P.head_d 0 hk, P.tail_d 0 hk] at h2
    exact absurd (P.inj 1 hk 0 (Nat.zero_le _) h2) one_ne_zero
  · rw [P.card_darts, P.card_cutS hk]
    ring

end PathCut

/-! ### Multiple-source shortest paths in the dual graph minus a path -/

/-- **Multiple-source shortest paths in the dual graph minus the darts `L`**: the answer of the
data structure of Das, Kipouridis, Probst Gutenberg and Wulff-Nilsen on the cut of `M` along `L`
(`msspCut`, with the dart, vertex and face types `CutD`, `CutV`, `CutF` of the cut). -/
noncomputable def msspPlane (M : CombMap D V F) (L : List D) (ℓ : D → ℤ) (x y : F) : Option ℤ :=
  msspCut M (CutD M L) (CutV M L) (CutF M L) L ℓ x y

/-- **The data structure meets the specification of multiple-source shortest paths in the dual
graph minus a path**, for every plane map with transitive rotations and transitive faces. -/
theorem msspPlane_spec {M : CombMap D V F} (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) : MSSPSpec M (msspPlane M) := by
  intro P ℓ hnn x hx
  have hk : 0 < P.k := by
    rcases Nat.eq_zero_or_pos P.k with h | h
    · simp [SPath.faces, SPath.darts, h] at hx
    · exact h
  exact msspCut_isDist (exists_cut hM hrot hface P ℓ hnn hk) hx

/-- **The maps of rotation systems have transitive faces.** -/
theorem ofRotation_faceTrans {W : Type*} [Fintype W] [DecidableEq W] {Γ : SimpleGraph W}
    [DecidableRel Γ.Adj] (R : Kasteleyn.RotationSystem Γ) : (CombMap.ofRotation R).FaceTrans := by
  intro d d' h
  obtain ⟨n, hn⟩ := (R.face_eq_face_iff.1 h).exists_nat_pow_eq
  have e : (CombMap.ofRotation R).next = ⇑R.faceNext := rfl
  exact ⟨n, by rw [e, Equiv.Perm.iterate_eq_pow]; exact hn⟩

/-- **The data structure meets the specification of multiple-source shortest paths in the dual
graph minus a path, for plane rotation systems.** -/
theorem msspPlane_spec_ofRotation {W : Type*} [Fintype W] [DecidableEq W] {Γ : SimpleGraph W}
    [DecidableRel Γ.Adj] {R : Kasteleyn.RotationSystem Γ} (hR : R.IsPlane) :
    MSSPSpec (CombMap.ofRotation R) (msspPlane (CombMap.ofRotation R)) :=
  msspPlane_spec (CombMap.ofRotation_isPlane hR) (MSSP.ofRotation_rotTrans R)
    (ofRotation_faceTrans R)

end BKMNW

end PlanarFlow
