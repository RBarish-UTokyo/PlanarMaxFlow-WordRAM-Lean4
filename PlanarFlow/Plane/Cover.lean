module

public import PlanarFlow.BKMNW.CutBuild
public import PlanarFlow.Plane.Submap
public import Mathlib.Tactic.LinearCombination

/-!
# The cyclic cover of a plane map branched at two vertices

Erickson's analysis of the algorithm of Borradaile and Klein (SODA 2010, Section 2.4), like the
reduction of Borradaile and Harutyunyan (*Maximum st-flow in directed planar graphs via shortest
paths*, 2013, Section 2), works in the infinite cyclic cover of the sphere minus `s` and `t`. Here
we build its finite quotient: the `K`-fold cyclic cover of the sphere **branched** at `s` and
`t`, which is again a sphere, as a combinatorial map `cover C K`. Cutting it along one lift of a
simple path from `s` to `t` gives `K` consecutive sheets of the infinite cover.

The cover is determined by an antisymmetric `P : D → ℤ` with zero net flow at every vertex other
than `s` and `t` (in the application, the unit flow of a simple path from `s` to `t`): the dual
dart `d` lifts to the darts `(d, i)`, `i : ZMod K`, from the face `(face d, i)` to the face
`(face (rev d), i + P d)`, so that walking around the vertex `v` the sheet changes by the net flow
of `P` out of `v`: by `0` for `v ≠ s, t`, by `±1` around `s` and `t`.

* `rotSum`, `rotSum_period`: the sum of `P` along the rotation; over one turn it is the net flow
  out of the vertex.
* `exists_rotPot`: **a rotation potential**: `pos (rot d) = pos d + P d` at the vertices other
  than `s` and `t` (`CovData`).
* `cover`: the map: darts `D × ZMod K`, faces `F × ZMod K`, vertices `CovV`: `s` and `t` once
  (the branch points) and `K` lifts `(v, i)` of every other vertex; the tail of `(d, i)` is
  `(tail d, i - pos d)`.
* `cover_rotTrans`, `cover_faceTrans`, `cover_isPlane`: **the cover of a plane map with
  transitive rotations and faces is a plane map with transitive rotations and faces** (Euler's
  formula: `2 + (V - 2) K` vertices, `F K` faces, `E K` edges).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace CombMap

open Finset Function

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable (M : CombMap D V F)

/-! ### Sums along the rotation -/

/-- The sum of `P` along the first `n` darts of the rotation from `d`. -/
def rotSum (P : D → ℤ) (d : D) (n : ℕ) : ℤ := ∑ j ∈ range n, P (M.rot^[j] d)

variable {M}

lemma rotSum_add (P : D → ℤ) (d : D) (m n : ℕ) :
    M.rotSum P d (m + n) = M.rotSum P d m + M.rotSum P (M.rot^[m] d) n := by
  unfold rotSum
  rw [sum_range_add]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [add_comm, iterate_add_apply]

lemma rotSum_succ (P : D → ℤ) (d : D) (n : ℕ) :
    M.rotSum P d (n + 1) = M.rotSum P d n + P (M.rot^[n] d) := by
  simp [rotSum, sum_range_succ]

lemma rotSum_mul_period (P : D → ℤ) (d : D) (q : ℕ) :
    M.rotSum P d (minimalPeriod M.rot d * q) = q * M.rotSum P d (minimalPeriod M.rot d) := by
  induction q with
  | zero => simp [rotSum]
  | succ q ih =>
    rw [Nat.mul_succ, rotSum_add, ih, iterate_mul, iterate_fixed (iterate_minimalPeriod)]
    push_cast; ring

/-- The sum along the rotation only depends on the dart reached, up to whole turns. -/
lemma rotSum_mod (P : D → ℤ) (d : D) (n : ℕ) :
    M.rotSum P d n = M.rotSum P d (n % minimalPeriod M.rot d) +
      (n / minimalPeriod M.rot d : ℕ) * M.rotSum P d (minimalPeriod M.rot d) := by
  conv_lhs => rw [← Nat.div_add_mod n (minimalPeriod M.rot d)]
  rw [rotSum_add, rotSum_mul_period, iterate_mul, iterate_fixed iterate_minimalPeriod]
  ring

/-- **Over one turn, the sum along the rotation is the net flow out of the vertex.** -/
lemma rotSum_period (hrot : M.RotTrans) (P : D → ℤ) (d : D) :
    M.rotSum P d (minimalPeriod M.rot d) = M.div P (M.tail d) := by
  unfold rotSum div
  have hp := BKMNW.rot_period_pos (M := M) d
  refine sum_nbij (fun j => M.rot^[j] d) (fun j _ => ?_) (fun i hi j hj h => ?_) (fun e he => ?_)
    (fun _ _ => rfl)
  · simp [tail_rot_iterate]
  · exact BKMNW.rot_iterate_inj (mem_range.1 hi) (mem_range.1 hj) h
  · have he' : M.tail e = M.tail d := by simpa using he
    obtain ⟨n, hn⟩ := hrot d e he'.symm
    refine ⟨n % minimalPeriod M.rot d, by simp [Nat.mod_lt _ hp], ?_⟩
    simp only
    rw [iterate_mod_minimalPeriod_eq, hn]

/-! ### A rotation potential -/

/-- **A rotation potential**: if `P` has zero net flow at every vertex other than `s` and `t`,
some `pos` increases by `P d` from `d` to `rot d` at those vertices. -/
theorem exists_rotPot (hrot : M.RotTrans) {P : D → ℤ} {s t : V}
    (hP : ∀ v, v ≠ s → v ≠ t → M.div P v = 0) :
    ∃ pos : D → ℤ, ∀ d, M.tail d ≠ s → M.tail d ≠ t → pos (M.rot d) = pos d + P d := by
  classical
  -- a base dart at every vertex
  let b : D → D := fun d => (⟨d, rfl⟩ : ∃ e, M.tail e = M.tail d).choose
  have hb : ∀ d, M.tail (b d) = M.tail d := fun d =>
    (⟨d, rfl⟩ : ∃ e, M.tail e = M.tail d).choose_spec
  have hbeq : ∀ d d', M.tail d = M.tail d' → b d = b d' := fun d d' h => by
    simp only [b]
    congr 1
    rw [h]
  have hex : ∀ d, ∃ n, M.rot^[n] (b d) = d := fun d => hrot _ _ (hb d)
  let pos : D → ℤ := fun d => M.rotSum P (b d) (Nat.find (hex d))
  -- the potential at any iterate
  have hpos : ∀ d n, M.tail d ≠ s → M.tail d ≠ t → M.rot^[n] (b d) = d →
      pos d = M.rotSum P (b d) n := by
    intro d n hs ht hn
    have h0 : M.rotSum P (b d) (minimalPeriod M.rot (b d)) = 0 := by
      rw [rotSum_period hrot, hb]; exact hP _ hs ht
    have hm : Nat.find (hex d) % minimalPeriod M.rot (b d) = n % minimalPeriod M.rot (b d) :=
      (iterate_eq_iterate_iff_of_lt_minimalPeriod (Nat.mod_lt _ (BKMNW.rot_period_pos _))
        (Nat.mod_lt _ (BKMNW.rot_period_pos _))).1 (by
          rw [iterate_mod_minimalPeriod_eq, iterate_mod_minimalPeriod_eq, Nat.find_spec (hex d),
            hn])
    show M.rotSum P (b d) (Nat.find (hex d)) = _
    rw [rotSum_mod, rotSum_mod (n := n), hm, h0]
    ring
  refine ⟨pos, fun d hs ht => ?_⟩
  have hbr : b (M.rot d) = b d := hbeq _ _ (M.tail_rot d)
  have hs' : M.tail (M.rot d) ≠ s := by rwa [M.tail_rot]
  have ht' : M.tail (M.rot d) ≠ t := by rwa [M.tail_rot]
  have hn := Nat.find_spec (hex d)
  rw [hpos d _ hs ht hn, hpos (M.rot d) (Nat.find (hex d) + 1) hs' ht' (by
    rw [hbr, iterate_succ_apply', hn]), hbr, rotSum_succ, hn]

/-! ### The cover -/

/-- **The data of a cyclic cover branched at `s` and `t`**: an antisymmetric `P` and a rotation
potential `pos` at the vertices other than `s` and `t`. -/
structure CovData (M : CombMap D V F) (s t : V) where
  /-- The cocycle: the change of sheet across a dart. -/
  P : D → ℤ
  /-- The rotation potential. -/
  pos : D → ℤ
  antisymm : M.IsAntisymm P
  pos_rot : ∀ d, M.tail d ≠ s → M.tail d ≠ t → pos (M.rot d) = pos d + P d

variable (V) in
/-- The vertices of the cover: `s` and `t` once, and `K` lifts of every other vertex. -/
abbrev CovV (s t : V) (K : ℕ) := {v : V // v = s ∨ v = t} ⊕ ({v : V // v ≠ s ∧ v ≠ t} × ZMod K)

variable {s t : V} (C : CovData M s t) (K : ℕ)

/-- The tail of a dart of the cover. -/
def covTail (x : D × ZMod K) : CovV V s t K :=
  if h : M.tail x.1 = s ∨ M.tail x.1 = t then .inl ⟨M.tail x.1, h⟩
  else .inr (⟨M.tail x.1, by push Not at h; exact h⟩, x.2 - (C.pos x.1 : ZMod K))

lemma rot_rev (d : D) : M.rot (M.rev d) = M.next d := by simp [CombMap.rot, M.rev_rev]

/-- **The cyclic cover of `M` with `K` sheets, branched at `s` and `t`.** -/
def cover : CombMap (D × ZMod K) (CovV V s t K) (F × ZMod K) where
  rev x := (M.rev x.1, x.2 + (C.P x.1 : ZMod K))
  rev_rev x := by
    ext
    · simp [M.rev_rev]
    · simp only [C.antisymm x.1]; push_cast; ring
  rev_ne x h := M.rev_ne x.1 (congrArg Prod.fst h)
  tail := covTail C K
  face x := (M.face x.1, x.2)
  next x := (M.next x.1, x.2)
  next_injective x y h := by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (M.next_injective h.1) h.2
  face_next x := by simp [M.face_next]
  tail_next x := by
    obtain ⟨d, i⟩ := x
    simp only [covTail, M.tail_next]
    split_ifs with h
    · rfl
    · push Not at h
      have := C.pos_rot (M.rev d) h.1 h.2
      rw [rot_rev] at this
      simp only [this, C.antisymm d]
      congr 2
      push_cast; ring

/-! ### The rotation and the faces of the cover -/

variable {C K}

@[simp] lemma cover_tail (x : D × ZMod K) : (cover C K).tail x = covTail C K x := rfl

@[simp] lemma cover_face (x : D × ZMod K) : (cover C K).face x = (M.face x.1, x.2) := rfl

@[simp] lemma cover_rev (x : D × ZMod K) :
    (cover C K).rev x = (M.rev x.1, x.2 + (C.P x.1 : ZMod K)) := rfl

@[simp] lemma cover_next (x : D × ZMod K) : (cover C K).next x = (M.next x.1, x.2) := rfl

lemma cover_rot (x : D × ZMod K) :
    (cover C K).rot x = (M.rot x.1, x.2 + (C.P x.1 : ZMod K)) := rfl

lemma cover_rot_iterate (x : D × ZMod K) (n : ℕ) :
    (cover C K).rot^[n] x = (M.rot^[n] x.1, x.2 + (M.rotSum C.P x.1 n : ZMod K)) := by
  induction n with
  | zero => simp [rotSum]
  | succ n ih =>
    rw [iterate_succ_apply', ih, cover_rot, rotSum_succ]
    ext
    · simp [iterate_succ_apply']
    · simp only; push_cast; ring

/-- The vertex of `M` below a vertex of the cover. -/
def covProj : CovV V s t K → V := Sum.elim Subtype.val fun p => p.1.1

@[simp] lemma covProj_tail (x : D × ZMod K) : covProj (covTail C K x) = M.tail x.1 := by
  unfold covTail; split_ifs <;> rfl

lemma covProj_head (x : D × ZMod K) : covProj ((cover C K).head x) = M.head x.1 :=
  covProj_tail (C := C) ((cover C K).rev x)

/-- Every dart of `M` lifts to a dart of the cover at every lift of its tail. -/
lemma exists_lift (d : D) {a : CovV V s t K} (ha : covProj a = M.tail d) :
    ∃ i, covTail C K (d, i) = a := by
  rcases a with ⟨v, hv⟩ | ⟨⟨v, hv⟩, j⟩
  · refine ⟨0, ?_⟩
    simp only [covProj, Sum.elim_inl] at ha
    subst ha
    simp [covTail, hv]
  · simp only [covProj, Sum.elim_inr] at ha
    subst ha
    refine ⟨j + (C.pos d : ZMod K), ?_⟩
    simp [covTail, hv.1, hv.2]

lemma rotSum_eq_pos {d : D} (hs : M.tail d ≠ s) (ht : M.tail d ≠ t) (n : ℕ) :
    M.rotSum C.P d n = C.pos (M.rot^[n] d) - C.pos d := by
  induction n with
  | zero => simp [rotSum]
  | succ n ih =>
    rw [rotSum_succ, ih, iterate_succ_apply', C.pos_rot _ (by rwa [tail_rot_iterate])
      (by rwa [tail_rot_iterate])]
    ring

/-- **The faces of the cover are transitive.** -/
theorem cover_faceTrans (hface : M.FaceTrans) : (cover C K).FaceTrans := by
  rintro ⟨d, i⟩ ⟨d', i'⟩ h
  simp only [cover_face, Prod.mk.injEq] at h
  obtain ⟨n, hn⟩ := hface d d' h.1
  refine ⟨n, ?_⟩
  have : ∀ m, (cover C K).next^[m] (d, i) = (M.next^[m] d, i) := fun m => by
    induction m with
    | zero => rfl
    | succ m ih => rw [iterate_succ_apply', ih, iterate_succ_apply']; rfl
  rw [this, hn, h.2]

/-- **The rotations of the cover are transitive**, when `P` has net flow `1` out of `s` and `-1`
out of `t`. -/
theorem cover_rotTrans [NeZero K] (hrot : M.RotTrans) (hs : M.div C.P s = 1)
    (ht : M.div C.P t = -1) : (cover C K).RotTrans := by
  rintro ⟨d, i⟩ ⟨d', i'⟩ h
  simp only [cover_tail, covTail] at h
  split_ifs at h with h1 h2 h2
  · -- at a branch point
    simp only [Sum.inl.injEq, Subtype.mk.injEq] at h
    obtain ⟨n0, hn0⟩ := hrot d d' h
    set σ : ℤ := M.div C.P (M.tail d)
    have hσ : σ * σ = 1 := by
      rcases h1 with h1 | h1 <;> simp only [σ, h1, hs, ht] <;> norm_num
    set per := minimalPeriod M.rot d
    set m := (((i' - i - (M.rotSum C.P d n0 : ZMod K)) * (σ : ZMod K)) : ZMod K).val
    refine ⟨per * m + n0, ?_⟩
    rw [cover_rot_iterate]
    ext
    · simp only
      rw [show per * m + n0 = n0 + per * m by ring, iterate_add_apply, iterate_mul,
        iterate_fixed iterate_minimalPeriod, hn0]
    · simp only
      rw [rotSum_add, rotSum_mul_period, iterate_mul, iterate_fixed iterate_minimalPeriod,
        rotSum_period hrot]
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id', id]
      have : ((σ : ℤ) : ZMod K) * (σ : ZMod K) = 1 := by
        have := congrArg (Int.cast (R := ZMod K)) hσ
        push_cast at this
        exact this
      linear_combination (i' - i - ((M.rotSum C.P d n0 : ℤ) : ZMod K)) * this
  all_goals try (simp at h; done)
  · -- at a lift of another vertex
    simp only [Sum.inr.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
    push Not at h1
    obtain ⟨n0, hn0⟩ := hrot d d' h.1
    refine ⟨n0, ?_⟩
    rw [cover_rot_iterate, hn0, rotSum_eq_pos h1.1 h1.2, hn0]
    ext
    · rfl
    · simp only
      push_cast
      linear_combination h.2

/-! ### The cover is plane -/

section Plane

variable [NeZero K]

open Relation

/-- The branch point over `s`. -/
def covS (s t : V) (K : ℕ) : CovV V s t K := .inl ⟨s, Or.inl rfl⟩

lemma eq_covS {a : CovV V s t K} (h : covProj a = s) : a = covS s t K := by
  rcases a with ⟨v, hv⟩ | ⟨⟨v, hv⟩, j⟩
  · simp only [covProj, Sum.elim_inl] at h
    subst h; rfl
  · simp only [covProj, Sum.elim_inr] at h
    exact absurd h hv.1

lemma cover_adj_symm (a b : CovV V s t K) (h : (cover C K).Adj a b) : (cover C K).Adj b a := by
  obtain ⟨x, rfl, rfl⟩ := h
  exact ⟨(cover C K).rev x, rfl, by rw [CombMap.head_rev]⟩

lemma cover_dualAdj_symm (a b : F × ZMod K) (h : (cover C K).DualAdj a b) :
    (cover C K).DualAdj b a := by
  obtain ⟨x, rfl, rfl⟩ := h
  exact ⟨(cover C K).rev x, rfl, by rw [(cover C K).rev_rev]⟩

/-- Walks of `M` lift to the cover. -/
lemma lift_reach {v w : V} (h : ReflTransGen M.Adj v w) {a : CovV V s t K}
    (ha : covProj a = v) : ∃ b, covProj b = w ∧ ReflTransGen (cover C K).Adj a b := by
  induction h with
  | refl => exact ⟨a, ha, .refl⟩
  | tail _ huw ih =>
    obtain ⟨b, hb, hab⟩ := ih
    obtain ⟨d, hd1, hd2⟩ := huw
    obtain ⟨i, hi⟩ := exists_lift (C := C) d (hb.trans hd1.symm)
    exact ⟨(cover C K).head (d, i), by rw [covProj_head, hd2],
      hab.tail ⟨(d, i), hi, rfl⟩⟩

/-- Dual walks of `M` lift to the cover. -/
lemma lift_dualReach {f f' : F} (h : ReflTransGen M.DualAdj f f') (i : ZMod K) :
    ∃ j, ReflTransGen (cover C K).DualAdj (f, i) (f', j) := by
  induction h with
  | refl => exact ⟨i, .refl⟩
  | tail _ hgf ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨d, rfl, rfl⟩ := hgf
    exact ⟨j + (C.P d : ZMod K), hj.tail ⟨(d, j), rfl, rfl⟩⟩

/-- Around a dart leaving `s`, the faces of all sheets are connected. -/
lemma sheets_conn (hrot : M.RotTrans) (hs : M.div C.P s = 1) {d : D} (hd : M.tail d = s)
    (i : ZMod K) (n : ℕ) :
    ReflTransGen (cover C K).DualAdj (M.face d, i) (M.face d, i + n) := by
  have hturn : ∀ x : D × ZMod K, ∀ m,
      ReflTransGen (cover C K).DualAdj ((cover C K).face x) ((cover C K).face
        ((cover C K).rot^[m] x)) := by
    intro x m
    induction m with
    | zero => exact .refl
    | succ m ih =>
      refine ih.tail ⟨(cover C K).rot^[m] x, rfl, ?_⟩
      rw [iterate_succ_apply', (cover C K).face_rot]
  induction n with
  | zero => simpa using ReflTransGen.refl
  | succ n ih =>
    refine ih.trans ?_
    have := hturn (d, i + n) (minimalPeriod M.rot d)
    rw [cover_rot_iterate, iterate_minimalPeriod, rotSum_period hrot, hd, hs] at this
    simpa [add_assoc] using this

/-- **The cover is plane**, for a plane map with transitive rotations, `s ≠ t` and `P` of net
flow `1` out of `s`. -/
theorem cover_isPlane (hM : M.IsPlane) (hrot : M.RotTrans) (hst : s ≠ t)
    (hs : M.div C.P s = 1) : (cover C K).IsPlane where
  nonempty := ⟨covS s t K⟩
  conn a b := by
    have key : ∀ a : CovV V s t K, ReflTransGen (cover C K).Adj a (covS s t K) := fun a => by
      obtain ⟨b, hb, hab⟩ := lift_reach (C := C) (hM.conn (covProj a) s) rfl
      rwa [eq_covS hb] at hab
    exact (key a).trans (BKMNW.reflTransGen_symm' (cover_adj_symm (C := C)) (key b))
  dualConn a b := by
    obtain ⟨d, hd⟩ : ∃ d, M.tail d = s := by
      rcases ReflTransGen.cases_head (hM.conn s t) with h | ⟨w, ⟨d, h1, -⟩, -⟩
      · exact absurd h hst
      · exact ⟨d, h1⟩
    have key : ∀ y : F × ZMod K,
        ReflTransGen (cover C K).DualAdj y (M.face d, 0) := fun y => by
      obtain ⟨j, hj⟩ := lift_dualReach (C := C) (hM.dualConn y.1 (M.face d)) y.2
      refine hj.trans ?_
      have := sheets_conn (C := C) hrot hs hd j ((-j : ZMod K).val)
      rwa [ZMod.natCast_val, ZMod.cast_id', id, add_neg_cancel] at this
    exact (key a).trans (BKMNW.reflTransGen_symm' (cover_dualAdj_symm (C := C)) (key b))
  euler := by
    have he := hM.euler
    have hD : Even (Fintype.card D) := by
      have := Orbit.even_card (ι := Function.Involutive.toPerm M.rev M.rev_rev)
        ⟨M.rev_rev, M.rev_ne⟩ (B := univ) (fun _ _ => mem_univ _)
      rwa [card_univ] at this
    have h2 : Fintype.card {v : V // v = s ∨ v = t} = 2 := by
      rw [Fintype.card_subtype]
      have : (univ.filter fun v : V => v = s ∨ v = t) = {s, t} := by ext; simp
      rw [this, card_pair hst]
    have hrest : Fintype.card {v : V // v ≠ s ∧ v ≠ t} + 2 = Fintype.card V := by
      rw [← h2, Fintype.card_subtype, Fintype.card_subtype, ← card_union_of_disjoint
        (disjoint_filter.2 fun v _ h h' => by tauto)]
      rw [← card_univ]; congr 1; ext v; simp; tauto
    simp only [Fintype.card_sum, Fintype.card_prod, ZMod.card, h2]
    obtain ⟨k, hk⟩ := hD
    rw [hk] at he ⊢
    have : (k + k) * K / 2 = k * K := by
      rw [show (k + k) * K = 2 * (k * K) by ring]; omega
    rw [this]
    have hk2 : (k + k) / 2 = k := by omega
    rw [hk2] at he
    nlinarith

end Plane

end CombMap

end PlanarFlow
