module

public import PlanarFlow.BKMNW.SubMap
public import PlanarSeparator.MillerFace

/-!
# Maps of `PlanarFlow` and of `PlanarSeparator`, and piece maps

The two kinds of maps describe the same objects. The conversions of
`PlanarFlow/BKMNW/Triangulate.lean` (`PlanarFlow.CombMap.ofSep`, `PlanarFlow.CombMap.toSep`) and
the piece maps of `PlanarFlow/BKMNW/ExistMiller.lean` (`PlanarFlow.BKMNW.psep`) are restated here
under other names (`combOfSep`, `sepOfComb`, `pieceSep`), with the same proofs, for use below the
maximum-flow algorithm (those files import it): the shortest paths with negative lengths used by
the algorithm rely on them.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap

/-- With a dart, every vertex of a plane map is the tail of a dart. -/
lemma exists_tail_eq' {D V F : Type*} [Fintype D] [Fintype V] [Fintype F] {M : CombMap D V F}
    [Nonempty D] (hM : M.IsPlane) : ∃ e : V → D, ∀ v, M.tail (e v) = v := by
  obtain ⟨d₀⟩ := ‹Nonempty D›
  have h : ∀ v, ∃ d, M.tail d = v := fun v => by
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hM.conn (M.tail d₀) v) with
      h | ⟨c, -, d, -, hd⟩
    · exact ⟨d₀, h.symm⟩
    · exact ⟨M.rev d, by rw [tail_rev, hd]⟩
  exact ⟨fun v => (h v).choose, fun v => (h v).choose_spec⟩

section OfSep

variable {D P : Type*} (N : PlanarSeparator.Map D P)

/-- **The map of `PlanarFlow` of a map of `PlanarSeparator`**: the reversal `α`, the vertices,
the faces (the cycles of the face permutation `φ`), and `next = φ`. -/
def combOfSep : CombMap D P N.Face where
  rev := N.α
  rev_rev := N.α_α
  rev_ne := N.α_ne
  tail := N.vert
  face := N.face
  next := N.φ
  next_injective := N.φ.injective
  face_next := N.face_φ
  tail_next d := N.vert_φ d

@[simp] lemma combOfSep_rev (d : D) : (combOfSep N).rev d = N.α d := rfl
@[simp] lemma combOfSep_tail (d : D) : (combOfSep N).tail d = N.vert d := rfl
@[simp] lemma combOfSep_face (d : D) : (combOfSep N).face d = N.face d := rfl
@[simp] lemma combOfSep_next (d : D) : (combOfSep N).next d = N.φ d := rfl

lemma combOfSep_rot (d : D) : (combOfSep N).rot d = N.σ d := by
  simp [CombMap.rot, PlanarSeparator.Map.φ_apply, N.α_α]

variable [Fintype D]

theorem combOfSep_rotTrans : (combOfSep N).RotTrans := fun d d' h => by
  obtain ⟨n, hn⟩ := (N.sameCycle d d' h).exists_nat_pow_eq
  refine ⟨n, ?_⟩
  have e : (combOfSep N).rot = N.σ := funext (combOfSep_rot N)
  rw [e, ← Equiv.Perm.coe_pow]
  exact hn

theorem combOfSep_faceTrans : (combOfSep N).FaceTrans := fun d d' h => by
  obtain ⟨n, hn⟩ := (N.face_eq_face_iff.1 h).exists_nat_pow_eq
  refine ⟨n, ?_⟩
  have e : (combOfSep N).next = N.φ := rfl
  rw [e, ← Equiv.Perm.coe_pow]
  exact hn

variable [DecidableEq D] [Fintype P] [DecidableEq P]

/-- **The map of a plane map of `PlanarSeparator` is plane.** -/
theorem combOfSep_isPlane {N : PlanarSeparator.Map D P} (hN : N.IsPlane) :
    (combOfSep N).IsPlane where
  nonempty := hN.nonempty
  conn a b := by
    obtain ⟨da, rfl⟩ := hN.exists_dart a
    obtain ⟨db, rfl⟩ := hN.exists_dart b
    induction hN.connected da db with
    | refl => exact .refl
    | tail _ hst ih =>
      rcases hst with rfl | rfl
      · rwa [N.vert_σ]
      · exact ih.tail ⟨_, rfl, rfl⟩
  dualConn x y := by
    obtain ⟨dx, rfl⟩ := N.face_surjective x
    obtain ⟨dy, rfl⟩ := N.face_surjective y
    induction hN.connected dx dy with
    | refl => exact .refl
    | tail _ hst ih =>
      rcases hst with rfl | rfl
      · exact ih.tail ⟨_, rfl, (N.face_σ _).symm⟩
      · exact ih.tail ⟨_, rfl, rfl⟩
  euler := by
    have h1 := hN.euler
    have h2 := N.card_darts
    omega

end OfSep

/-! ### To the maps of `PlanarSeparator` -/

section ToSep

variable {D V F : Type*} [Fintype D] [DecidableEq D] (M : CombMap D V F)

/-- **The map of `PlanarSeparator` of a map with transitive rotations**: the reversal and the
rotation as permutations, the tails as vertices. -/
noncomputable def sepOfComb (hrot : M.RotTrans) : PlanarSeparator.Map D V where
  α := Function.Involutive.toPerm M.rev M.rev_rev
  σ := Equiv.ofBijective M.rot (Finite.injective_iff_bijective.1 M.rot_injective)
  vert := M.tail
  α_α := M.rev_rev
  α_ne := M.rev_ne
  vert_σ := M.tail_rot
  sameCycle d d' h := by
    obtain ⟨k, hk⟩ := hrot d d' h
    exact ⟨k, by rw [zpow_natCast, Equiv.Perm.coe_pow]; exact hk⟩

variable {M}

@[simp] lemma sepOfComb_α (hrot : M.RotTrans) (d : D) : (sepOfComb M hrot).α d = M.rev d := rfl
@[simp] lemma sepOfComb_σ (hrot : M.RotTrans) (d : D) : (sepOfComb M hrot).σ d = M.rot d := rfl
@[simp] lemma sepOfComb_vert (hrot : M.RotTrans) (d : D) : (sepOfComb M hrot).vert d = M.tail d :=
  rfl

@[simp] lemma sepOfComb_φ (hrot : M.RotTrans) (d : D) : (sepOfComb M hrot).φ d = M.next d := by
  simp [PlanarSeparator.Map.φ_apply, CombMap.rot, M.rev_rev]

lemma sepOfComb_φ_pow (hrot : M.RotTrans) (n : ℕ) (d : D) :
    ((sepOfComb M hrot).φ ^ n) d = M.next^[n] d := by
  rw [Equiv.Perm.coe_pow]
  have e : ⇑(sepOfComb M hrot).φ = M.next := funext (sepOfComb_φ hrot)
  rw [e]

lemma face_next_iterate' (n : ℕ) (d : D) : M.face (M.next^[n] d) = M.face d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', M.face_next, ih]

/-- The faces of `sepOfComb M hrot` to the faces of `M`. -/
noncomputable def sepOfCombFace (hrot : M.RotTrans) : (sepOfComb M hrot).Face → F :=
  Quotient.lift M.face fun d d' h => by
    obtain ⟨n, hn⟩ := (show (sepOfComb M hrot).φ.SameCycle d d' from h).exists_nat_pow_eq
    rw [← hn, sepOfComb_φ_pow, face_next_iterate']

@[simp] lemma sepOfCombFace_face (hrot : M.RotTrans) (d : D) :
    sepOfCombFace hrot ((sepOfComb M hrot).face d) = M.face d := rfl

variable [Fintype F]

/-- **The faces of `sepOfComb M hrot` are those of `M`**, for a plane map with transitive rotations
and faces and a dart. -/
theorem card_sepOfComb_face [Fintype V] (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    [Nonempty D] : Fintype.card (sepOfComb M hrot).Face = Fintype.card F := by
  refine Fintype.card_of_bijective (f := sepOfCombFace hrot) ⟨fun x y h => ?_, fun x => ?_⟩
  · obtain ⟨d, rfl⟩ := (sepOfComb M hrot).face_surjective x
    obtain ⟨d', rfl⟩ := (sepOfComb M hrot).face_surjective y
    simp only [sepOfCombFace_face] at h
    obtain ⟨k, hk⟩ := hface d d' h
    exact (sepOfComb M hrot).face_eq_face_iff.2 ⟨k, by rw [zpow_natCast, sepOfComb_φ_pow, hk]⟩
  · obtain ⟨d₀⟩ := ‹Nonempty D›
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hM.dualConn (M.face d₀) x) with
      h | ⟨c, -, d, -, hd⟩
    · exact ⟨(sepOfComb M hrot).face d₀, by rw [sepOfCombFace_face, h]⟩
    · exact ⟨(sepOfComb M hrot).face (M.rev d), by rw [sepOfCombFace_face, hd]⟩

lemma reach_rot_iterate' (hrot : M.RotTrans) (k : ℕ) (d : D) :
    Relation.ReflTransGen (fun a b => b = (sepOfComb M hrot).σ a ∨ b = (sepOfComb M hrot).α a) d
      (M.rot^[k] d) := by
  induction k with
  | zero => exact .refl
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.tail (Or.inl rfl)

/-- **The map of `PlanarSeparator` of a plane map with transitive rotations and faces and a dart
is plane.** -/
theorem sepOfComb_isPlane [Fintype V] [DecidableEq V] (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) [Nonempty D] : (sepOfComb M hrot).IsPlane where
  exists_dart v := by
    obtain ⟨e, he⟩ := exists_tail_eq' hM
    exact ⟨e v, he v⟩
  connected d d' := by
    have key : ∀ b, Relation.ReflTransGen M.Adj (M.tail d) b → ∃ x, M.tail x = b ∧
        Relation.ReflTransGen (fun a b => b = (sepOfComb M hrot).σ a ∨ b = (sepOfComb M hrot).α a)
          d x := by
      intro b hb
      induction hb with
      | refl => exact ⟨d, rfl, .refl⟩
      | tail _ hst ih =>
        obtain ⟨x, hx, hdx⟩ := ih
        obtain ⟨e, he1, he2⟩ := hst
        obtain ⟨k, hk⟩ := hrot x e (by rw [hx, he1])
        refine ⟨M.rev e, by rw [tail_rev, he2], ?_⟩
        exact (hdx.trans (hk ▸ reach_rot_iterate' hrot k x)).tail (Or.inr rfl)
    obtain ⟨x, hx, hdx⟩ := key _ (hM.conn (M.tail d) (M.tail d'))
    obtain ⟨k, hk⟩ := hrot x d' hx
    exact hdx.trans (hk ▸ reach_rot_iterate' hrot k x)
  euler := by
    have h1 := hM.euler
    have h2 := (sepOfComb M hrot).card_darts
    have h3 := card_sepOfComb_face hM hrot hface
    omega

end ToSep

section Pieces

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

section PSep

variable {σ : Perm D} {B : Finset D} (hσ : Stable σ B) (hB : Stable (revPerm M) B)

variable (M) in
/-- **The piece map of the darts `B` with rotation `σ`**, as a map of `PlanarSeparator`: darts the
darts of `B`, vertices the orbits of `σ`. -/
noncomputable def pieceSep : PlanarSeparator.Map (SDart B) (SVert σ B) :=
  sepOfComb (subMap B (revPerm_isInv M) hσ hB) (subMap_rotTrans (revPerm_isInv M) hσ hB)

@[simp] lemma pieceSep_α (x : SDart B) : ((pieceSep M hσ hB).α x).1 = M.rev x.1 := rfl

@[simp] lemma pieceSep_σ (x : SDart B) : ((pieceSep M hσ hB).σ x).1 = σ x.1 := by
  simp [pieceSep]

lemma pieceSep_vert (x : SDart B) : (pieceSep M hσ hB).vert x = Quotient.mk _ x := rfl

lemma pieceSep_vert_eq {x y : SDart B} :
    (pieceSep M hσ hB).vert x = (pieceSep M hσ hB).vert y ↔ σ.SameCycle x.1 y.1 := sVert_eq_iff

@[simp] lemma pieceSep_φ (x : SDart B) : ((pieceSep M hσ hB).φ x).1 = σ (M.rev x.1) := by
  simp [pieceSep, PlanarSeparator.Map.φ_apply]

lemma pieceSep_φ_pow (n : ℕ) (x : SDart B) :
    (((pieceSep M hσ hB).φ ^ n) x).1 = ((σ * revPerm M)^[n]) x.1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Perm.mul_apply, ih, pieceSep_φ, iterate_succ_apply]
    rfl

lemma pieceSep_φ_symm (x : SDart B) :
    ((pieceSep M hσ hB).φ.symm x).1 = (σ * revPerm M).symm x.1 := by
  have h := pieceSep_φ hσ hB ((pieceSep M hσ hB).φ.symm x)
  rw [Equiv.apply_symm_apply] at h
  rw [Equiv.eq_symm_apply, Perm.mul_apply]; exact h.symm

lemma pieceSep_face_eq {x y : SDart B} :
    (pieceSep M hσ hB).face x = (pieceSep M hσ hB).face y ↔ (σ * revPerm M).SameCycle x.1 y.1 := by
  rw [PlanarSeparator.Map.face_eq_face_iff]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact sameCycle_iff.2 ⟨n, by rw [← pieceSep_φ_pow hσ hB, hn]⟩
  · intro h
    obtain ⟨n, hn⟩ := sameCycle_iff.1 h
    refine ⟨n, ?_⟩
    rw [zpow_natCast]
    exact Subtype.ext (by rw [pieceSep_φ_pow hσ hB, hn])

/-- **The piece map is plane** when the darts are connected and the Euler gap vanishes. -/
theorem pieceSep_isPlane {x₀ : D} (hx₀ : x₀ ∈ B)
    (hconn : ∀ x ∈ B, ∀ y ∈ B, Conn (revPerm M) σ x y) (h0 : gap (revPerm M) σ B = 0) :
    (pieceSep M hσ hB).IsPlane := by
  have : Nonempty (SDart B) := ⟨⟨x₀, hx₀⟩⟩
  exact sepOfComb_isPlane (subMap_isPlane (revPerm_isInv M) hσ hB hx₀ hconn h0)
    (subMap_rotTrans (revPerm_isInv M) hσ hB) (subMap_faceTrans (revPerm_isInv M) hσ hB)

end PSep

/-- The number of vertices and of faces of the piece map are at most its number of darts. -/
lemma card_pieceSep_le {σ : Perm D} {B : Finset D} (hσ : Stable σ B) (hB : Stable (revPerm M) B) :
    Fintype.card (SVert σ B) + Fintype.card (pieceSep M hσ hB).Face ≤ 2 * B.card := by
  have h1 : Fintype.card (SVert σ B) ≤ Fintype.card (SDart B) :=
    Fintype.card_le_of_surjective _ Quotient.mk_surjective
  have h2 : Fintype.card (pieceSep M hσ hB).Face ≤ Fintype.card (SDart B) :=
    Fintype.card_le_of_surjective _ (pieceSep M hσ hB).face_surjective
  have h3 : Fintype.card (SDart B) = B.card := Fintype.card_coe B
  omega


end Pieces

end NegSSSP

end PlanarFlow
