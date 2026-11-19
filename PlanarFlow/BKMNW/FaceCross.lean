module

public import PlanarFlow.BKMNW.SubMap
public import PlanarFlow.BKMNW.Triangulate
public import PlanarFlow.BKMNW.MongeBridge
public import PlanarFlow.Monge.FacePend

/-!
# The crossing inequality on a face cycle of a plane combinatorial map

The crossing inequality of a face (`PlanarFlow.Monge.crossing_face`,
`PlanarFlow.Monge.crossing_face_pend`) is proved for the maps of `PlanarSeparator`. This file
carries it to the maps of `PlanarFlow` (`PlanarFlow.CombMap`) in the setting of Klein's algorithm
and of the data structure of Das, Kipouridis, Probst Gutenberg and Wulff-Nilsen: a plane map with
transitive rotations, a face whose boundary walk is a simple cycle `g 0, …, g (k - 1)`
(`PlanarFlow.MSSP.FaceCycle`), and the digraph `PlanarFlow.MSSP.pieceGraph` of a set of darts,
with the distances of the specifications (`PlanarFlow.BKMNW.IsDist`).

* `faceTrans_of_plane`: **a plane map with transitive rotations has transitive faces** (by
  Euler's inequality `PlanarFlow.Orbit.gap_nonpos`: if a face were the union of two orbits of the
  boundary walk, the orbits would be more than the faces, against Euler's formula).
* `crossing_faceCycle`: the distances in the piece between the corners
  `tail (g (t 0)), …, tail (g (t (b - 1)))` (`t` increasing, below `k`) satisfy the crossing
  inequality `PlanarFlow.Monge.Crossing`, for any lengths, as soon as they are all finite.
* `crossingO_faceCycle`: the same with missing arcs (`Monge.CrossingO`), for all lengths.
* `crossing_faceCycle_pend`: the same for the distances from the corners to pendant targets
  `w j`, joined to the corner `tail (g (t j))` by a dart of the map, when no dart of the piece
  enters a corner.

Both are exactly the hypothesis `Monge.Crossing P.b P.D` of FR-Dijkstra on the machine
(`PlanarFlow.Monge.FR.frProg_dist`, `PlanarFlow.BKMNW.frProg_isDist`) and of Bellman–Ford over a
dense distance graph (`PlanarFlow.Monge.bfDDG_exec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv CombMap Orbit

/-! ### Plane maps with transitive rotations have transitive faces -/

section FaceTrans

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

lemma face_eq_of_sameCycle {x y : D} (h : (rotPerm M * revPerm M).SameCycle x y) :
    M.face x = M.face y := by
  obtain ⟨n, rfl⟩ := sameCycle_iff.1 h
  rw [iterate_nextPerm, CombMap.face_next_iterate]

/-- **A plane map with transitive rotations and a dart has transitive faces.** -/
theorem faceTrans_of_plane (hM : M.IsPlane) (hrot : M.RotTrans) [hD : Nonempty D] :
    M.FaceTrans := by
  classical
  have hconn : ∀ x y, Conn (revPerm M) (rotPerm M) x y := by
    have key : ∀ a b, Relation.ReflTransGen M.Adj a b → ∀ x y, M.tail x = a → M.tail y = b →
        Conn (revPerm M) (rotPerm M) x y := by
      intro a b h
      induction h with
      | refl =>
        intro x y hx hy
        exact conn_of_sameCycle ((sameCycle_rotPerm hrot).2 (hx.trans hy.symm))
      | tail _ hst ih =>
        obtain ⟨e, he, rfl⟩ := hst
        intro x y hx hy
        refine (ih x e hx he).trans ((conn_inv (ι := revPerm M) e).trans ?_)
        exact conn_of_sameCycle ((sameCycle_rotPerm hrot).2 (by rw [revPerm_apply, hy]; rfl))
    exact fun x y => key _ _ (hM.conn (M.tail x) (M.tail y)) x y rfl rfl
  obtain ⟨d₀⟩ := hD
  have hc := comp_eq_one (revPerm_isInv M) (mem_univ d₀) (fun x _ y _ => hconn x y)
  have hV : nOrb (rotPerm M) univ = Fintype.card V :=
    card_image_eq_of_iff (fun x y => by rw [cls_eq_iff, sameCycle_rotPerm hrot])
      (tail_surjective hM ⟨d₀⟩)
  have hgap := gap_nonpos (revPerm_isInv M) (σ := rotPerm M) (A := univ)
    (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
  have he := hM.euler
  obtain ⟨k, hk⟩ := even_card (revPerm_isInv M) (B := univ) (fun _ _ => mem_univ _)
  unfold gap eul at hgap
  rw [hc, hV, card_univ] at hgap
  rw [card_univ] at hk
  have hF : nOrb (rotPerm M * revPerm M) univ ≤ Fintype.card F := by omega
  intro d d' hdd
  by_contra hne
  have hsc : ¬ (rotPerm M * revPerm M).SameCycle d d' := fun h => hne (by
    obtain ⟨n, hn⟩ := sameCycle_iff.1 h
    exact ⟨n, by rw [← iterate_nextPerm]; exact hn⟩)
  set π := rotPerm M * revPerm M with hπ
  let g' : D → Finset D := fun z => if M.face z = M.face d then Orbit.cls π d else Orbit.cls π z
  have h1 : univ.image g' ⊆ (univ.image (Orbit.cls π)).erase (Orbit.cls π d') := by
    intro s hs
    obtain ⟨z, -, rfl⟩ := mem_image.1 hs
    refine mem_erase.2 ⟨?_, ?_⟩
    · by_cases hz : M.face z = M.face d
      · simp only [g', hz, ↓reduceIte]
        exact fun h => hsc (cls_eq_iff.1 h)
      · simp only [g', hz, ↓reduceIte]
        exact fun h => hz ((face_eq_of_sameCycle (cls_eq_iff.1 h)).trans hdd.symm)
    · by_cases hz : M.face z = M.face d
      · simp only [g', hz, ↓reduceIte]; exact mem_image_of_mem _ (mem_univ _)
      · simp only [g', hz, ↓reduceIte]; exact mem_image_of_mem _ (mem_univ _)
  have h2 : (univ.image M.face).card ≤ (univ.image g').card := by
    refine card_image_le_of_fiber fun x _ y _ hxy => ?_
    by_cases hx : M.face x = M.face d <;> by_cases hy : M.face y = M.face d
    · rw [hx, hy]
    · simp only [g', hx, hy, ↓reduceIte] at hxy
      exact absurd ((face_eq_of_sameCycle (cls_eq_iff.1 hxy)).symm) hy
    · simp only [g', hx, hy, ↓reduceIte] at hxy
      exact absurd (face_eq_of_sameCycle (cls_eq_iff.1 hxy)) hx
    · simp only [g', hx, hy, ↓reduceIte] at hxy
      exact face_eq_of_sameCycle (cls_eq_iff.1 hxy)
  rw [image_univ_of_surjective (face_surjective hM ⟨d₀⟩), card_univ] at h2
  have h3 := card_le_card h1
  rw [card_erase_of_mem (mem_image_of_mem _ (mem_univ d'))] at h3
  unfold nOrb at hF
  have hpos : 0 < (univ.image (Orbit.cls π)).card :=
    card_pos.2 ⟨_, mem_image_of_mem _ (mem_univ d₀)⟩
  omega

end FaceTrans

/-! ### The face cycle in the map of `PlanarSeparator` -/

section FaceCycle

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {Q : CombMap D V F} {k : ℕ} {g : ℕ → D}

lemma _root_.PlanarFlow.MSSP.FaceCycle.next_iterate (hfc : MSSP.FaceCycle Q k g) (n : ℕ) :
    Q.next^[n] (g 0) = g (n % k) := by
  have hk := hfc.two_le
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih, hfc.next _ (Nat.mod_lt _ (by omega)), Nat.add_mod n 1 k,
      Nat.mod_eq_of_lt (show 1 < k by omega)]

lemma _root_.PlanarFlow.MSSP.FaceCycle.sep_pow (hrot : Q.RotTrans) (hfc : MSSP.FaceCycle Q k g)
    {n : ℕ} (hn : n < k) :
    ((Q.toSep hrot).φ ^ n) (g 0) = g n := by
  rw [toSep_φ_pow, hfc.next_iterate, Nat.mod_eq_of_lt hn]

lemma _root_.PlanarFlow.MSSP.FaceCycle.sep_period (hrot : Q.RotTrans) (hfc : MSSP.FaceCycle Q k g) :
    ((Q.toSep hrot).φ ^ k) (g 0) = g 0 := by
  rw [toSep_φ_pow, hfc.next_iterate, Nat.mod_self]

lemma _root_.PlanarFlow.MSSP.FaceCycle.sep_min (hrot : Q.RotTrans) (hfc : MSSP.FaceCycle Q k g) :
    ∀ n, 0 < n → n < k → ((Q.toSep hrot).φ ^ n) (g 0) ≠ g 0 := by
  intro n hn hnk h
  rw [hfc.sep_pow hrot hnk] at h
  have := hfc.inj n hnk 0 (by omega) (by rw [h])
  omega

/-- The map of `PlanarSeparator` of a plane map with transitive rotations and a dart is plane. -/
lemma sep_isPlane (hQ : Q.IsPlane) (hrot : Q.RotTrans) (d₀ : D) : (Q.toSep hrot).IsPlane := by
  have : Nonempty D := ⟨d₀⟩
  exact toSep_isPlane hQ hrot (faceTrans_of_plane hQ hrot)

end FaceCycle

/-! ### The crossing inequality -/

section Crossing

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {Q : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

/-- Without arcs, every finite distance is `0`. -/
lemma eq_zero_of_isEmpty (hS : IsEmpty {d // d ∈ S}) {x y : V} {δ : V → Option ℤ}
    (hδ : IsDist (MSSP.pieceGraph Q S ℓ) x δ) {a : ℤ} (h : δ y = some a) : a = 0 := by
  obtain ⟨l, -, hl⟩ := hδ.some_walk y a h
  rcases l with _ | ⟨c, l⟩
  · rw [← hl]; rfl
  · exact hS.elim c

/-- **The crossing inequality of the distances between corners of a face cycle.** For a plane
map `Q` with transitive rotations, a face cycle `g` of `k` darts, increasing positions
`t 0 < ⋯ < t (b - 1) < k`, and any set `S` of darts with any lengths: if the distances in the
piece `S` from every corner `tail (g (t i))` are given, all finite between the corners (`Dm i j`
from the corner `i` to the corner `j`), then `Dm` satisfies the crossing inequality. -/
theorem crossing_faceCycle (hQ : Q.IsPlane) (hrot : Q.RotTrans) (hfc : MSSP.FaceCycle Q k g)
    {b : ℕ} {t : ℕ → ℕ} (ht : ∀ i j, i < j → j < b → t i < t j) (htk : ∀ i < b, t i < k)
    {Dm : ℕ → ℕ → ℤ}
    (hδ : ∀ i < b, ∃ δ, IsDist (MSSP.pieceGraph Q S ℓ) (Q.tail (g (t i))) δ ∧
      ∀ j < b, δ (Q.tail (g (t j))) = some (Dm i j)) :
    Monge.Crossing b Dm := by
  rcases isEmpty_or_nonempty {d // d ∈ S} with hS | hS
  · intro i i' j j' hi hj hi' hj' _
    have e : ∀ x y, x < b → y < b → Dm x y = 0 := fun x y hx hy => by
      obtain ⟨δ, h1, h2⟩ := hδ x hx
      exact eq_zero_of_isEmpty hS h1 (h2 y hy)
    rw [e i j' (by omega) hj', e i' j hi' (by omega), e i j (by omega) (by omega), e i' j' hi' hj']
  refine Monge.crossing_face (sep_isPlane hQ hrot (g 0)) (G := MSSP.pieceGraph Q S ℓ)
    (emb := Subtype.val) (fun _ => rfl) (fun _ => rfl) (hfc.sep_period hrot) (hfc.sep_min hrot)
    ht htk fun i hi => ?_
  obtain ⟨δ, h1, h2⟩ := hδ i hi
  refine ⟨δ, ?_, fun j hj => ?_⟩
  · rw [hfc.sep_pow hrot (htk i hi)]
    exact gdist_iff.2 h1
  · rw [hfc.sep_pow hrot (htk j hj)]
    exact h2 j hj

/-- **The crossing inequality of the distances from the corners of a face cycle to pendant
targets.** As `crossing_faceCycle`, with the target of the corner `j` a vertex `w j` joined to the
corner by a dart `pd j` of `Q` (from `w j` to the corner, not necessarily in `S`), when no dart of
`S` enters a corner of the face. -/
theorem crossing_faceCycle_pend (hQ : Q.IsPlane) (hrot : Q.RotTrans)
    (hfc : MSSP.FaceCycle Q k g) (hin : ∀ d ∈ S, ∀ i < k, Q.head d ≠ Q.tail (g i))
    {b : ℕ} {t : ℕ → ℕ} (ht : ∀ i j, i < j → j < b → t i < t j) (htk : ∀ i < b, t i < k)
    {w : ℕ → V} {pd : ℕ → D} (hpw : ∀ j < b, Q.tail (pd j) = w j)
    (hpv : ∀ j < b, Q.head (pd j) = Q.tail (g (t j))) {Dm : ℕ → ℕ → ℤ}
    (hδ : ∀ i < b, ∃ δ, IsDist (MSSP.pieceGraph Q S ℓ) (Q.tail (g (t i))) δ ∧
      ∀ j < b, δ (w j) = some (Dm i j)) :
    Monge.Crossing b Dm := by
  rcases isEmpty_or_nonempty {d // d ∈ S} with hS | hS
  · intro i i' j j' hi hj hi' hj' _
    have e : ∀ x y, x < b → y < b → Dm x y = 0 := fun x y hx hy => by
      obtain ⟨δ, h1, h2⟩ := hδ x hx
      exact eq_zero_of_isEmpty hS h1 (h2 y hy)
    rw [e i j' (by omega) hj', e i' j hi' (by omega), e i j (by omega) (by omega), e i' j' hi' hj']
  refine Monge.crossing_face_pend (sep_isPlane hQ hrot (g 0)) (G := MSSP.pieceGraph Q S ℓ)
    (emb := Subtype.val) (fun _ => rfl) (fun _ => rfl) (hfc.sep_period hrot) (hfc.sep_min hrot)
    ht htk (fun i hi j hj h => ?_) (fun a j hj => ?_) (pd := pd) hpw (fun j hj => ?_)
    fun i hi => ?_
  · rw [hfc.sep_pow hrot (htk i hi), hfc.sep_pow hrot (htk j hj)] at h
    have := hfc.inj _ (htk i hi) _ (htk j hj) h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact absurd this (ht i j h' hj).ne
    · exact absurd this (ht j i h' hi).ne'
  · rw [hfc.sep_pow hrot (htk j hj)]
    exact hin a.1 a.2 _ (htk j hj)
  · rw [hfc.sep_pow hrot (htk j hj)]
    exact hpv j hj
  · obtain ⟨δ, h1, h2⟩ := hδ i hi
    refine ⟨δ, ?_, h2⟩
    rw [hfc.sep_pow hrot (htk i hi)]
    exact gdist_iff.2 h1

/-- **The crossing inequality between the corners of a face cycle, with missing arcs**
(`Monge.CrossingO`): `crossing_faceCycle` without assuming the distances between the corners
finite. -/
theorem crossingO_faceCycle (hQ : Q.IsPlane) (hrot : Q.RotTrans) (hfc : MSSP.FaceCycle Q k g)
    {b : ℕ} {t : ℕ → ℕ} (ht : ∀ i j, i < j → j < b → t i < t j) (htk : ∀ i < b, t i < k)
    {Dm : ℕ → ℕ → Option ℤ}
    (hδ : ∀ i < b, ∃ δ, IsDist (MSSP.pieceGraph Q S ℓ) (Q.tail (g (t i))) δ ∧
      ∀ j < b, δ (Q.tail (g (t j))) = Dm i j) :
    Monge.CrossingO b Dm := by
  rcases isEmpty_or_nonempty {d // d ∈ S} with hS | hS
  · intro i i' j j' hi hj hi' hj' hsep a a' ha _
    exfalso
    obtain ⟨δ, h1, h2⟩ := hδ i (by omega)
    rw [← h2 j (by omega)] at ha
    obtain ⟨l, hl, -⟩ := h1.some_walk _ a ha
    rcases l with _ | ⟨c, l⟩
    · have := hfc.inj _ (htk i (by omega)) _ (htk j (by omega)) (isWalk_nil.1 hl)
      rcases hsep with h' | h'
      · exact absurd this (ht i j (by omega) (by omega)).ne
      · exact absurd this (ht j i (by omega) (by omega)).ne'
    · exact hS.elim c
  refine Monge.crossingO_face (sep_isPlane hQ hrot (g 0)) (G := MSSP.pieceGraph Q S ℓ)
    (emb := Subtype.val) (fun _ => rfl) (fun _ => rfl) (hfc.sep_period hrot) (hfc.sep_min hrot)
    ht htk fun i hi => ?_
  obtain ⟨δ, h1, h2⟩ := hδ i hi
  refine ⟨δ, ?_, fun j hj => ?_⟩
  · rw [hfc.sep_pow hrot (htk i hi)]
    exact gdist_iff.2 h1
  · rw [hfc.sep_pow hrot (htk j hj)]
    exact h2 j hj

end Crossing

end BKMNW

end PlanarFlow
