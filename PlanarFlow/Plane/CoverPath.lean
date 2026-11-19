module

public import PlanarFlow.Plane.Cover

/-!
# A simple path, its unit flow, and its lift to the cyclic cover

* `exists_sPath`: on a connected map, **two distinct vertices are joined by a simple path**
  (a shortest walk).
* `pflow`: the unit flow of a simple path; `pflow_spec`: it is antisymmetric, `1` on the darts of
  the path, `-1` on their reverses, `0` elsewhere, with net flow `1` out of the first vertex,
  `-1` out of the last, `0` elsewhere.
* `pathCov`: the cyclic cover branched at the ends of a simple path `π`, determined by its unit
  flow (`CovData`).
* `liftPath`: **the lift of `π` to the cover**, a simple path through the darts `(d j, -1)`; the
  dual darts it deletes are exactly the lifts crossing from the sheet `-1` to the sheet `0`
  (`mem_liftPath_darts`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace CombMap

open Finset Function BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-! ### Walks and their vertices -/

section Walks

variable {X A : Type*} {G : Digraph X A}

/-- The vertex reached by the arcs `l` from `x`. -/
def endp (G : Digraph X A) (x : X) (l : List A) : X := (l.getLast?.map G.dst).getD x

@[simp] lemma endp_nil (x : X) : endp G x [] = x := rfl

lemma endp_cons (x : X) (a : A) (l : List A) : endp G x (a :: l) = endp G (G.dst a) l := by
  unfold endp
  rw [List.getLast?_cons]
  cases l.getLast? <;> rfl

lemma endp_of_isWalk {x y : X} {l : List A} (h : IsWalk G x l y) : endp G x l = y := by
  induction l generalizing x with
  | nil => exact h
  | cons a l ih =>
    obtain ⟨-, h2⟩ := h
    rw [endp_cons, ih h2]

lemma isWalk_take_drop {x y : X} {l : List A} (h : IsWalk G x l y) (i : ℕ) :
    IsWalk G x (l.take i) (endp G x (l.take i)) ∧ IsWalk G (endp G x (l.take i)) (l.drop i) y := by
  obtain ⟨z, h1, h2⟩ := isWalk_append_iff.1 ((List.take_append_drop i l).symm ▸ h)
  rw [endp_of_isWalk h1]
  exact ⟨h1, h2⟩

lemma exists_walk_of_reach {G : Digraph X A} {x y : X}
    (h : Relation.ReflTransGen (fun a b => ∃ e, G.src e = a ∧ G.dst e = b) x y) :
    ∃ l, IsWalk G x l y := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | tail _ hbc ih =>
    obtain ⟨l, hl⟩ := ih
    obtain ⟨e, h1, h2⟩ := hbc
    exact ⟨l ++ [e], hl.append (isWalk_singleton.2 ⟨h1, h2⟩)⟩

end Walks

/-! ### Simple paths -/

variable {M : CombMap D V F}

/-- The primal graph of a map. -/
def pgraph (M : CombMap D V F) : Digraph V D := ⟨M.tail, M.head, fun _ => 0⟩

/-- **Two vertices of a connected map are joined by a simple path**: a shortest walk. -/
theorem exists_sPath (hM : M.IsPlane) {s t : V} (hst : s ≠ t) :
    ∃ π : SPath M, 0 < π.k ∧ π.p 0 = s ∧ π.p π.k = t := by
  classical
  have hex : ∃ n l, IsWalk (pgraph M) s l t ∧ l.length = n := by
    obtain ⟨l, hl⟩ := exists_walk_of_reach (G := pgraph M) (hM.conn s t)
    exact ⟨_, l, hl, rfl⟩
  obtain ⟨l, hl, hlen⟩ := Nat.find_spec hex
  have hmin : ∀ l', IsWalk (pgraph M) s l' t → Nat.find hex ≤ l'.length := fun l' hl' =>
    Nat.find_min' hex ⟨l', hl', rfl⟩
  have hl0 : l ≠ [] := by rintro rfl; exact hst hl
  refine ⟨⟨l.length, fun j => l.getD j (l.head hl0), fun j => endp (pgraph M) s (l.take j), ?_,
    ?_, ?_⟩, List.length_pos_of_ne_nil hl0, ?_, ?_⟩
  · intro j hj
    obtain ⟨-, h2⟩ := isWalk_take_drop hl j
    rw [List.drop_eq_getElem_cons hj] at h2
    obtain ⟨h3, -⟩ := h2
    rw [← h3]
    simp [pgraph, List.getElem?_eq_getElem hj]
  · intro j hj
    have e1 : endp (pgraph M) s (l.take (j + 1)) = (pgraph M).dst l[j] := by
      unfold endp
      rw [List.getLast?_take]
      simp [List.getElem?_eq_getElem hj]
    rw [e1]
    simp only [pgraph, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some]
  · intro i hi j hj hij
    by_contra hne
    wlog hlt : i < j generalizing i j
    · exact this j hj i hi hij.symm (Ne.symm hne) (by omega)
    obtain ⟨h1, -⟩ := isWalk_take_drop hl i
    obtain ⟨-, h2⟩ := isWalk_take_drop hl j
    rw [hij] at h1
    have hw := h1.append h2
    have := hmin _ hw
    simp only [List.length_append, List.length_take, List.length_drop] at this
    have : l.length = Nat.find hex := hlen
    omega
  · simp
  · simp only [List.take_length]
    exact endp_of_isWalk hl

/-! ### The unit flow of a simple path -/

/-- **The unit flow of a simple path**: `1` on its darts, `-1` on their reverses. -/
def pflow (π : SPath M) (d : D) : ℤ :=
  ∑ j ∈ range π.k, ((if d = π.d j then 1 else 0) - (if d = M.rev (π.d j) then 1 else 0))

variable (π : SPath M)

lemma pflow_d {j : ℕ} (hj : j < π.k) : pflow π (π.d j) = 1 := by
  unfold pflow
  rw [sum_eq_single j (fun i hi hij => by
    have h1 : π.d j ≠ π.d i := fun h => hij (π.d_inj (mem_range.1 hi) hj h.symm)
    have h2 : π.d j ≠ M.rev (π.d i) := π.d_ne_rev hj (mem_range.1 hi)
    simp [h1, h2]) (fun h => absurd (mem_range.2 hj) h)]
  simp [π.d_ne_rev hj hj]

lemma pflow_rev_d {j : ℕ} (hj : j < π.k) : pflow π (M.rev (π.d j)) = -1 := by
  unfold pflow
  rw [sum_eq_single j (fun i hi hij => by
    have h1 : M.rev (π.d j) ≠ π.d i := fun h =>
      π.d_ne_rev (mem_range.1 hi) hj h.symm
    have h2 : M.rev (π.d j) ≠ M.rev (π.d i) := fun h =>
      hij (π.d_inj (mem_range.1 hi) hj (M.rev_injective h).symm)
    simp [h1, h2]) (fun h => absurd (mem_range.2 hj) h)]
  have : M.rev (π.d j) ≠ π.d j := fun h => π.d_ne_rev hj hj h.symm
  simp [this]

lemma pflow_of_not_mem {d : D} (h : d ∉ π.darts) : pflow π d = 0 := by
  unfold pflow
  refine sum_eq_zero fun j hj => ?_
  have h1 : d ≠ π.d j := fun e => h (e ▸ π.d_mem j (mem_range.1 hj))
  have h2 : d ≠ M.rev (π.d j) := fun e => h (e ▸ π.rev_d_mem j (mem_range.1 hj))
  simp [h1, h2]

lemma pflow_antisymm : M.IsAntisymm (pflow π) := by
  intro d
  by_cases hd : d ∈ π.darts
  · obtain ⟨j, hj, rfl | rfl⟩ := π.mem_darts.1 hd
    · rw [pflow_d π hj, pflow_rev_d π hj]
    · rw [M.rev_rev, pflow_d π hj, pflow_rev_d π hj]; ring
  · rw [pflow_of_not_mem π hd, pflow_of_not_mem π (fun h => hd (by
      have := π.rev_mem_darts h; rwa [M.rev_rev] at this))]
    simp

/-- **The net flow of the path flow**: `1` out of the first vertex, `-1` out of the last. -/
lemma div_pflow (v : V) :
    M.div (pflow π) v = (if π.p 0 = v then 1 else 0) - (if π.p π.k = v then 1 else 0) := by
  unfold CombMap.div pflow
  rw [sum_comm]
  have hstep : ∀ j ∈ range π.k, (∑ e with M.tail e = v,
      ((if e = π.d j then (1 : ℤ) else 0) - (if e = M.rev (π.d j) then 1 else 0))) =
      (if π.p j = v then 1 else 0) - (if π.p (j + 1) = v then 1 else 0) := by
    intro j hj
    rw [sum_sub_distrib, sum_ite_eq', sum_ite_eq']
    simp only [mem_filter, mem_univ, true_and, M.tail_rev, π.tail_d j (mem_range.1 hj),
      π.head_d j (mem_range.1 hj)]
  rw [sum_congr rfl hstep, sum_range_sub' (fun j => if π.p j = v then (1 : ℤ) else 0)]

/-- At an inner vertex of the path, only the two darts of the path have a nonzero flow. -/
lemma pflow_ne_zero_inner {e : D} {j : ℕ} (hj : j + 1 < π.k) (he : M.tail e = π.p (j + 1))
    (h0 : pflow π e ≠ 0) : e = π.d (j + 1) ∨ e = M.rev (π.d j) := by
  by_cases hd : e ∈ π.darts
  · obtain ⟨i, hi, rfl | rfl⟩ := π.mem_darts.1 hd
    · left
      rw [π.tail_d i hi] at he
      rw [π.inj i hi.le (j + 1) hj.le he]
    · right
      rw [M.tail_rev, π.head_d i hi] at he
      have := π.inj (i + 1) hi (j + 1) hj.le he
      rw [show i = j by omega]
  · exact absurd (pflow_of_not_mem π hd) h0

/-! ### The lift of the path -/

section Lift

variable {π}

lemma div_pflow_inner {v : V} (hs : v ≠ π.p 0) (ht : v ≠ π.p π.k) : M.div (pflow π) v = 0 := by
  rw [div_pflow]; simp [Ne.symm hs, Ne.symm ht]

/-- **The cyclic cover branched at the ends of a simple path**, given by its unit flow. -/
noncomputable def pathCov (hrot : M.RotTrans) (π : SPath M) : CovData M (π.p 0) (π.p π.k) where
  P := pflow π
  pos := (exists_rotPot hrot (fun _ hs ht => div_pflow_inner (π := π) hs ht)).choose
  antisymm := pflow_antisymm π
  pos_rot := (exists_rotPot hrot (fun _ hs ht => div_pflow_inner (π := π) hs ht)).choose_spec

variable {s t : V} {C : CovData M s t} {K : ℕ}

lemma covTail_branch {d : D} (i : ZMod K) (h : M.tail d = s ∨ M.tail d = t) :
    covTail C K (d, i) = .inl ⟨M.tail d, h⟩ := by
  simp [covTail, h]

lemma covTail_inner {d : D} (i : ZMod K) (h : M.tail d ≠ s ∧ M.tail d ≠ t) :
    covTail C K (d, i) = .inr (⟨M.tail d, h⟩, i - (C.pos d : ZMod K)) := by
  simp [covTail, h.1, h.2]

variable (hrot : M.RotTrans)

lemma pathCov_P : (pathCov hrot π).P = pflow π := rfl

/-- At an inner vertex of the path, from the dart entering by the path to the dart leaving by
the path, the rotation potential drops by `1`. -/
lemma pos_inner {j : ℕ} (hj : j + 1 < π.k) :
    (pathCov hrot π).pos (π.d (j + 1)) - (pathCov hrot π).pos (M.rev (π.d j)) = -1 := by
  set y := M.rev (π.d j)
  set x := π.d (j + 1)
  have hty : M.tail y = π.p (j + 1) := by simp [y, π.head_d j (by omega)]
  have htx : M.tail x = π.p (j + 1) := π.tail_d _ hj
  have hs : π.p (j + 1) ≠ π.p 0 := fun h => by have := π.inj _ hj.le 0 (by omega) h; omega
  have ht : π.p (j + 1) ≠ π.p π.k := fun h => by have := π.inj _ hj.le _ le_rfl h; omega
  obtain ⟨n0, hn0⟩ := hrot y x (hty.trans htx.symm)
  set per := minimalPeriod M.rot y
  have hper := BKMNW.rot_period_pos (M := M) y
  set n := n0 % per
  have hn : M.rot^[n] y = x := by rw [iterate_mod_minimalPeriod_eq, hn0]
  have hxy : x ≠ y := π.d_ne_rev hj (by omega)
  have hn1 : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    rw [this] at hn
    exact hxy hn.symm
  have hnlt : n < per := Nat.mod_lt _ hper
  clear_value n
  have key := rotSum_eq_pos (C := pathCov hrot π) (hty ▸ hs) (hty ▸ ht) n
  rw [hn] at key
  rw [← key]
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + m := ⟨n - 1, by omega⟩
  rw [rotSum_add]
  have h1 : M.rotSum (pathCov hrot π).P y 1 = -1 := by
    simp [rotSum, pathCov_P, y, pflow_rev_d π (show j < π.k by omega)]
  have h2 : M.rotSum (pathCov hrot π).P (M.rot^[1] y) m = 0 := by
    refine sum_eq_zero fun i hi => ?_
    have hi' := mem_range.1 hi
    rw [← iterate_add_apply]
    by_contra h0
    have hti : M.tail (M.rot^[i + 1] y) = π.p (j + 1) := by rw [tail_rot_iterate, hty]
    rcases pflow_ne_zero_inner π (by omega) hti h0 with h | h
    · have := BKMNW.rot_iterate_inj (M := M) (x := y) (i := i + 1) (j := 1 + m) (by omega)
        hnlt (h.trans hn.symm)
      omega
    · have := BKMNW.rot_iterate_ne (M := M) (x := y) (i := i + 1) (by omega)
        (by omega)
      exact this h
  rw [h1, h2]; ring

/-- The vertex of the lifted path. -/
noncomputable def liftP (π : SPath M) (K : ℕ) (j : ℕ) : CovV V (π.p 0) (π.p π.k) K :=
  if j < π.k then covTail (pathCov hrot π) K (π.d j, -1) else .inl ⟨π.p π.k, Or.inr rfl⟩

lemma covProj_liftP (π : SPath M) (K : ℕ) {j : ℕ} (hj : j ≤ π.k) :
    covProj (liftP hrot π K j) = π.p j := by
  unfold liftP
  split_ifs with h
  · rw [covProj_tail, π.tail_d j h]
  · simp only [covProj, Sum.elim_inl]; rw [show j = π.k by omega]

/-- **The lift of the path**: the darts `(d j, -1)`. -/
noncomputable def liftPath (π : SPath M) (K : ℕ) (hk : 0 < π.k) :
    SPath (cover (pathCov hrot π) K) where
  k := π.k
  d j := (π.d j, -1)
  p := liftP hrot π K
  tail_d j hj := by simp [liftP, hj]
  head_d j hj := by
    have hP : ((pathCov hrot π).P (π.d j) : ZMod K) = 1 := by
      rw [pathCov_P, pflow_d π hj]; simp
    show covTail _ K ((cover (pathCov hrot π) K).rev (π.d j, -1)) = _
    rw [cover_rev]
    simp only [hP, neg_add_cancel]
    unfold liftP
    split_ifs with h
    · have hs : π.p (j + 1) ≠ π.p 0 := fun e => by
        have := π.inj _ h.le 0 (by omega) e; omega
      have ht : π.p (j + 1) ≠ π.p π.k := fun e => by
        have := π.inj _ h.le _ le_rfl e; omega
      have h1 : M.tail (M.rev (π.d j)) = π.p (j + 1) := by simp [π.head_d j hj]
      have h2 : M.tail (π.d (j + 1)) = π.p (j + 1) := π.tail_d _ h
      rw [covTail_inner _ ⟨h1 ▸ hs, h1 ▸ ht⟩, covTail_inner _ ⟨h2 ▸ hs, h2 ▸ ht⟩]
      have := pos_inner hrot (π := π) h
      congr 1
      · exact Prod.ext (Subtype.ext (h1.trans h2.symm)) (by
          simp only
          have e : ((pathCov hrot π).pos (π.d (j + 1)) : ZMod K) =
              ((pathCov hrot π).pos (M.rev (π.d j)) : ZMod K) - 1 := by
            rw [show (pathCov hrot π).pos (π.d (j + 1)) =
              (pathCov hrot π).pos (M.rev (π.d j)) - 1 by omega]
            push_cast; ring
          rw [e]; ring)
    · have h1 : M.tail (M.rev (π.d j)) = π.p π.k := by
        simp [π.head_d j hj, show j + 1 = π.k by omega]
      rw [covTail_branch _ (Or.inr h1)]
      simp [h1]
  inj i hi j hj h := by
    have := congrArg covProj h
    rw [covProj_liftP hrot π K hi, covProj_liftP hrot π K hj] at this
    exact π.inj i hi j hj this

lemma liftPath_k (π : SPath M) (K : ℕ) (hk : 0 < π.k) : (liftPath hrot π K hk).k = π.k := rfl

lemma liftPath_d (π : SPath M) (K : ℕ) (hk : 0 < π.k) (j : ℕ) :
    (liftPath hrot π K hk).d j = (π.d j, -1) := rfl

/-- **The darts deleted by the lift of the path**: the lifts `(d j, -1)` of the darts of `π`,
crossing from the sheet `-1` to the sheet `0`, and their reverses `(rev (d j), 0)`. -/
lemma mem_liftPath_darts (π : SPath M) (K : ℕ) [NeZero K] (hk : 0 < π.k) {x : D × ZMod K} :
    x ∈ (liftPath hrot π K hk).darts ↔
      ∃ j < π.k, x = (π.d j, -1) ∨ x = (M.rev (π.d j), 0) := by
  rw [SPath.mem_darts]
  refine exists_congr fun j => and_congr_right fun hj => or_congr_right ?_
  rw [liftPath_d, cover_rev, pathCov_P, pflow_d π hj]
  simp

end Lift

end CombMap

end PlanarFlow
