module

public import PlanarFlow.Klein.LCTInit
public import PlanarFlow.Klein.Cost

/-!
# The full trip around the face on the stored trees

* `exists_cotree`: on a plane map every spanning tree has a cotree rooted at any face (a
  breadth-first search tree, `exists_dtree_of_conn`, of the faces through the darts off the
  tree, connected by `PlanarFlow.STFlow.DTree.cotree_conn`); `exists_layout`: the nodes of the
  vertices, of the edges of the spanning tree, of the faces and of the edges of the cotree, on
  `2 (#V + #F + #D)` nodes.
* `recot_stored`: `evert` at the node of a face re-roots the stored cotree there.
* `dart_stored`, `darts_stored`: **changing the values of darts** of the stored cotree (`pointOps`,
  four operations per dart whose edge is in the cotree, none for the others).
* `tripΔ j`, `tripWt_succ`, `sum_tripΔ_le`: **the weights `tripWt` change between the moves `j`
  and `j + 1` only on the darts of the piece leaving the targets of the two moves** (the other
  vertices are reached from every root or from none, and a root only from itself); over the `k`
  moves around the face these are at most `2 #S` darts.
* `next_stored`: **from the end of the move `j` to the start of the move `j + 1` on the stored
  data**: at most `18 + 4 #(tripΔ j)` valid operations, printing nothing, the data linked as in
  `IsTrip`.
* `IsTripUpTo J`: the first `J` moves of a trip (`IsTrip.upTo`); `MoveSpec.labels`,
  `IsTripUpTo.pivots`: the labels and the pivot bound of `IsTrip.labels`, `IsTrip.pivots` need only
  these.
* `TripStored`, `tripStored_zero`, `tripStored_succ`, `trip_stored`: **the first `J` moves on the
  stored data**: a list of valid operations from the empty forest (`init_stored`, then per move
  `move_stored` and `next_stored`) storing, after a prefix, the data at the start of every move,
  with the data of the moves forming `IsTripUpTo J`; `TripStored.labels`: after those prefixes
  the path sums at the nodes of the vertices are the distances from the source of the move.
* `klein_trip_stored`, `klein_trip_ops`: **the trip around the face** (`J = k`): on
  `2 (#V + #F + #D)` nodes, at most `6 (#V + #F) + 17 p + 19 k + 8 #S ≤ 25 (#V + #F + #D)`
  operations (`p ≤ #S` pivots, `IsTripUpTo.pivots`; at most `2 #S` weight changes,
  `sum_tripΔ_le`).

* `klein_trip_cost`: **the allowances of the counted cost** (`Klein/Cost.lean`) **are met**: the
  list has length at most `tripOps N #S k p 0`, and run as a fixed list on the machine
  (`PlanarFlow.DynTree.lctE_runsWithin`) it takes at most `400000 (82 N + 1) (⌊log₂ n⌋ + 1)`
  steps.

The lists are given by their existence: each pivot depends on the answer of the query `min2`
before it (`move_stored`), so the list is adaptive; the machine program computing it is
`PlanarFlow.Klein.kleinProg` (`klein_exec`, `PlanarFlow/Klein/ProgTrip.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree

/-! ### A tree from connectivity -/

section Generic

variable {D X Y : Type*} [Fintype D] [DecidableEq D] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]
variable {N : CombMap D X Y}

variable (N) in
/-- `Within N A r m y`: the face `y` is reached from `r` through at most `m` darts satisfying `A`
(each from its face to the face of its reverse). -/
inductive Within (A : D → Prop) (r : Y) : ℕ → Y → Prop
  | base : Within A r 0 r
  | mono {m : ℕ} {y : Y} : Within A r m y → Within A r (m + 1) y
  | step {m : ℕ} {d : D} : A d → Within A r m (N.face d) → Within A r (m + 1) (N.face (N.rev d))

/-- **A tree from connectivity**: if every face is reached from `r` through darts satisfying `A`,
a tree rooted at `r` has all its parent darts satisfying `A` (a breadth-first search tree). -/
theorem exists_dtree_of_conn [Nonempty D] {A : D → Prop} (r : Y)
    (h : ∀ y, Relation.ReflTransGen (fun a b => ∃ d, A d ∧ N.face d = a ∧ N.face (N.rev d) = b)
      r y) :
    ∃ C : DTree N, C.root = r ∧ ∀ y, y ≠ C.root → A (C.par y) := by
  classical
  have hex : ∀ y, ∃ m, Within N A r m y := by
    intro y
    induction h y with
    | refl => exact ⟨0, .base⟩
    | tail _ hab ih =>
      obtain ⟨d, hd, rfl, rfl⟩ := hab
      obtain ⟨m, hm⟩ := ih
      exact ⟨m + 1, .step hd hm⟩
  set hop : Y → ℕ := fun y => Nat.find (hex y) with hhop
  have hq : ∀ y, y ≠ r → ∃ d, A d ∧ N.face (N.rev d) = y ∧ hop (N.face d) < hop y := by
    intro y hy
    have hs := Nat.find_spec (hex y)
    rcases hn : Nat.find (hex y) with _ | m
    · rw [hn] at hs
      cases hs
      exact absurd rfl hy
    · rw [hn] at hs
      have hmin : ¬ Within N A r m y := Nat.find_min (hex y) (by omega)
      cases hs with
      | mono h' => exact absurd h' hmin
      | @step _ d hd h' =>
        refine ⟨d, hd, rfl, ?_⟩
        have : hop (N.face d) ≤ m := Nat.find_min' _ h'
        simp only [hhop] at this ⊢
        omega
  choose! q hq using hq
  let par : Y → D := fun y => if y = r then Classical.arbitrary D else q y
  have hhead : ∀ y, y ≠ r → N.face (N.rev (par y)) = y := fun y hy => by
    simp only [par, hy, ↓reduceIte]; exact (hq y hy).2.1
  have hreach : ∀ y, ∃ m, (upF N r par)^[m] y = r := by
    intro y
    induction hn : hop y using Nat.strong_induction_on generalizing y with
    | _ m ih =>
      by_cases hy : y = r
      · exact ⟨0, hy⟩
      obtain ⟨m', hm'⟩ := ih _ (hn ▸ (hq y hy).2.2) (N.face (q y)) rfl
      refine ⟨m' + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      have : upF N r par y = N.face (q y) := by simp [upF, hy, par]
      rw [this]; exact hm'
  exact ⟨⟨r, par, hhead, hreach⟩, rfl, fun y hy => by
    have hy' : y ≠ r := hy
    simp only [par, hy', ↓reduceIte]; exact (hq y hy').1⟩

end Generic

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-- **A cotree of a spanning tree** (on a plane map): a tree of the faces rooted at any face,
whose parent darts are off the spanning tree. -/
theorem exists_cotree [Nonempty D] (hM : M.IsPlane) (T : DTree M.dual) (fe : F) :
    ∃ C : DTree M, C.root = fe ∧ ∀ x, x ≠ C.root → ¬ T.InT (C.par x) :=
  exists_dtree_of_conn fe fun y => T.cotree_conn hM.dual fe y

/-! ### A layout of the nodes -/

/-- The index of the edge of a dart: the least index of its two darts. -/
noncomputable def edgeIx (M : CombMap D V F) (d : D) : ℕ :=
  min (Fintype.equivFin D d : ℕ) (Fintype.equivFin D (M.rev d) : ℕ)

lemma edgeIx_rev (d : D) : edgeIx M (M.rev d) = edgeIx M d := by
  unfold edgeIx; rw [M.rev_rev, min_comm]

lemma edgeIx_lt (d : D) : edgeIx M d < Fintype.card D :=
  lt_of_le_of_lt (min_le_left _ _) (Fintype.equivFin D d).2

lemma edgeIx_eq {d d' : D} (h : edgeIx M d = edgeIx M d') : d' = d ∨ d' = M.rev d := by
  have key : ∀ d : D, ∃ x, (x = d ∨ x = M.rev d) ∧ (Fintype.equivFin D x : ℕ) = edgeIx M d := by
    intro d
    rcases min_choice (Fintype.equivFin D d : ℕ) (Fintype.equivFin D (M.rev d) : ℕ) with h | h
    · exact ⟨d, Or.inl rfl, h.symm⟩
    · exact ⟨M.rev d, Or.inr rfl, h.symm⟩
  obtain ⟨x, hx, hx'⟩ := key d
  obtain ⟨y, hy, hy'⟩ := key d'
  have hxy : x = y := (Fintype.equivFin D).injective (Fin.ext (by rw [hx', hy', h]))
  subst hxy
  rcases hx with rfl | rfl <;> rcases hy with h1 | h1
  · exact Or.inl h1.symm
  · exact Or.inr (by rw [h1, M.rev_rev])
  · exact Or.inr h1.symm
  · left
    have := congrArg M.rev h1
    rwa [M.rev_rev, M.rev_rev, eq_comm] at this

/-- **A layout exists** on `2 (#V + #F + #D)` nodes: the vertices, the edges of the spanning
tree, the faces, the edges of the cotree. -/
theorem exists_layout (M : CombMap D V F) :
    ∃ (ιv : V → ℕ) (ιg : D → ℕ) (ιf : F → ℕ) (ιe : D → ℕ),
      Layout M (2 * (Fintype.card V + Fintype.card F + Fintype.card D)) ιv ιg ιf ιe := by
  set a := Fintype.card V
  set b := Fintype.card D
  set c := Fintype.card F
  have hv : ∀ x : V, (Fintype.equivFin V x : ℕ) < a := fun x => (Fintype.equivFin V x).2
  have hf : ∀ y : F, (Fintype.equivFin F y : ℕ) < c := fun y => (Fintype.equivFin F y).2
  have he : ∀ d : D, edgeIx M d < b := edgeIx_lt
  refine ⟨fun x => Fintype.equivFin V x, fun d => a + edgeIx M d,
    fun y => a + b + Fintype.equivFin F y, fun d => a + b + c + edgeIx M d,
    ⟨⟨fun x y h => (Fintype.equivFin V).injective (Fin.ext h), fun d => ?_, fun d d' h => ?_,
      fun x d => ?_, fun x => ?_, fun d => ?_⟩,
    ⟨fun x y h => (Fintype.equivFin F).injective (Fin.ext (by simpa using h)), fun d => ?_,
      fun d d' h => ?_, fun x d => ?_, fun x => ?_, fun d => ?_⟩,
    by omega, by omega, fun x y => ?_, fun x d => ?_, fun d y => ?_, fun d d' => ?_⟩⟩
  · show a + edgeIx M (M.rev d) = _; rw [edgeIx_rev]
  · exact edgeIx_eq (M := M) (by simpa using h)
  · have := hv x; omega
  · have := hv x; omega
  · have := he d; omega
  · show a + b + c + edgeIx M (M.rev d) = _; rw [edgeIx_rev]
  · exact edgeIx_eq (by simpa using h)
  · have := hf x; omega
  · have := hf x; omega
  · have := he d; omega
  · have := hv x; omega
  · have := hv x; omega
  · have := he d; omega
  · have := he d; omega

/-! ### Operations on the stored data -/

section StoredOps

variable {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

/-- Two lists of valid operations printing nothing, one after the other. -/
lemma ops_seq {Fo : Forest} {os os' : List EOp} (hv : ValidOpsE n Fo os)
    (ho : (runOpsE n Fo os).2 = []) (hv' : ValidOpsE n (runOpsE n Fo os).1 os')
    (ho' : (runOpsE n (runOpsE n Fo os).1 os').2 = []) :
    ValidOpsE n Fo (os ++ os') ∧ (runOpsE n Fo (os ++ os')).2 = [] ∧
      (runOpsE n Fo (os ++ os')).1 = (runOpsE n (runOpsE n Fo os).1 os').1 := by
  refine ⟨(validOpsE_append n _ _ _).2 ⟨hv, hv'⟩, ?_, ?_⟩ <;> rw [runOpsE_append]
  rw [ho, ho']; rfl

/-- The bound of the values at the nodes of the faces can be lowered. -/
lemma Stored.mono {φ : D → ℤ} {fe : F} {Lo Lo' : ℝ} {Fo : Forest} {T : DTree M.dual}
    {val : D → ℤ} (hS : Stored M n ιv ιg ιf ιe φ fe Lo Fo T val) (h : Lo' ≤ Lo) :
    Stored M n ιv ιg ιf ιe φ fe Lo' Fo T val := by
  obtain ⟨C, β, β₂, h1, h2, h3, h4, h5⟩ := hS.cot
  exact ⟨hS.tree, hS.treeIso, ⟨C, β, β₂, h1, h2, h3, h4,
    fun x => ⟨h.trans (h5 x).1, h.trans (h5 x).2⟩⟩, hS.int⟩

/-- **Re-rooting the stored cotree** at the face `fe'`: `evert` at its node. -/
theorem recot_stored (hL : Layout M n ιv ιg ιf ιe) {φ : D → ℤ} {fe : F} {Lo : ℝ}
    {Fo : Forest} {T : DTree M.dual} {val : D → ℤ}
    (hS : Stored M n ιv ιg ιf ιe φ fe Lo Fo T val) (fe' : F) :
    ValidOpsE n Fo [.evert (ιf fe')] ∧ (runOpsE n Fo [.evert (ιf fe')]).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ fe' Lo (runOpsE n Fo [.evert (ιf fe')]).1 T val := by
  have hrun : runOpsE n Fo [.evert (ιf fe')] = (evert Fo n (ιf fe'), []) := rfl
  have hint := intF_runOpsE (n := n) [.evert (ιf fe')] hS.int
  rw [hrun] at hint ⊢
  obtain ⟨C, β, β₂, hroot, hoff, hRc, hIc, hLo⟩ := hS.cot
  have h1 := evert_trep hRc hL.dual hL.hf fe'
  have i1 := evert_iso hRc hIc hL.dual hL.hf fe'
  have hag : ∀ u, (∀ y, u ≠ ιf y) → (∀ d, u ≠ ιe d) → Agree Fo (evert Fo n (ιf fe')) u := i1.2
  refine ⟨⟨hL.dual.f_lt fe', trivial⟩, rfl,
    hS.tree.congr (fun x => hag _ (hL.vf x) (hL.ve x)) (fun d => hag _ (hL.gf d) (hL.ge d)),
    hS.treeIso.congr (fun d => hag _ (hL.gf d) (hL.ge d)),
    ⟨C.reroot fe', _, _, rfl, hoff_reroot hoff fe', h1, i1.1, fun x => ?_⟩, hint⟩
  split_ifs
  · exact ⟨(hLo x).2, (hLo x).1⟩
  · exact hLo x

/-- **Changing the value of one dart** of the stored cotree (`pointOps` when its edge is in the
cotree, nothing otherwise): at most four valid operations, printing nothing. -/
theorem dart_stored (hL : Layout M n ιv ιg ιf ιe) {φ : D → ℤ} {fe : F} {Lo : ℝ}
    {Fo : Forest} {T : DTree M.dual} {val : D → ℤ}
    (hS : Stored M n ιv ιg ιf ιe φ fe Lo Fo T val) (d : D) (z : ℤ) :
    ∃ os : List EOp, os.length ≤ 4 ∧ ValidOpsE n Fo os ∧ (runOpsE n Fo os).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ fe Lo (runOpsE n Fo os).1 T (Function.update val d z) := by
  classical
  obtain ⟨C, β, β₂, hroot, hoff, hRc, hIc, hLo⟩ := hS.cot
  have hpt : ∀ y, y ≠ C.root → ∀ δ₁ δ₂ : ℤ, (∀ d', (val d' : ℝ) +
      (if d' = C.par y then (δ₂ : ℝ) else 0) + (if d' = M.rev (C.par y) then (δ₁ : ℝ) else 0) =
        ((Function.update val d z d' : ℤ) : ℝ)) →
      ∃ os : List EOp, os.length ≤ 4 ∧ ValidOpsE n Fo os ∧ (runOpsE n Fo os).2 = [] ∧
        Stored M n ιv ιg ιf ιe φ fe Lo (runOpsE n Fo os).1 T (Function.update val d z) := by
    intro y hy δ₁ δ₂ hκ
    obtain ⟨hv, ho, hR', hpar, hag⟩ := point_trep hRc hL.dual hL.hf hy δ₁ δ₂
    have hint := intF_runOpsE (n := n) (pointOps ιf ιe C y δ₁ δ₂) hS.int
    exact ⟨pointOps ιf ιe C y δ₁ δ₂, by simp [pointOps], hv, ho,
      ⟨hS.tree.congr (fun x => hag _ (hL.ve x _)) (fun d' => hag _ (hL.ge d' _)),
        hS.treeIso.congr (fun d' => hag _ (hL.ge d' _)),
        ⟨C, β, β₂, hroot, hoff, hR'.congrκ hκ,
          fun d' hd' => (congrFun hpar _).trans (hIc d' hd'), hLo⟩, hint⟩⟩
  by_cases h1 : ∃ y, y ≠ C.root ∧ C.par y = d
  · obtain ⟨y, hy, rfl⟩ := h1
    refine hpt y hy 0 (z - val (C.par y)) fun d' => ?_
    by_cases hd : d' = C.par y
    · subst hd
      simp [Function.update_self]
    · simp [hd]
  by_cases h2 : ∃ y, y ≠ C.root ∧ C.par y = M.rev d
  · obtain ⟨y, hy, hyd⟩ := h2
    have hd : d = M.rev (C.par y) := by rw [hyd, M.rev_rev]
    subst hd
    refine hpt y hy (z - val (M.rev (C.par y))) 0 fun d' => ?_
    by_cases hd : d' = M.rev (C.par y)
    · subst hd
      simp [Function.update_self, M.rev_ne]
    · simp [hd]
  push Not at h1 h2
  refine ⟨[], by simp, trivial, rfl, hS.tree, hS.treeIso,
    ⟨C, β, β₂, hroot, hoff, ⟨hRc.pf, hRc.pr, hRc.pe, fun y hy => ?_, fun y hy => ?_, hRc.vf,
      hRc.vf2⟩, hIc, hLo⟩, hS.int⟩
  · have hne : M.rev (C.par y) ≠ d := fun h => h2 y hy (by rw [← h, M.rev_rev])
    show Fo.val _ = ((Function.update val d z (M.rev (C.par y)) : ℤ) : ℝ)
    rw [Function.update_of_ne hne]; exact hRc.ve y hy
  · show Fo.val2 _ = ((Function.update val d z (C.par y) : ℤ) : ℝ)
    rw [Function.update_of_ne (h1 y hy)]; exact hRc.ve2 y hy

/-- **Changing the values of the darts of a list**: at most four valid operations per dart,
printing nothing. -/
theorem darts_stored (hL : Layout M n ιv ιg ιf ιe) {φ : D → ℤ} {fe : F} {Lo : ℝ}
    {T : DTree M.dual} : ∀ (ds : List D) {Fo : Forest} {val val' : D → ℤ},
    Stored M n ιv ιg ιf ιe φ fe Lo Fo T val → (∀ d, d ∉ ds → val' d = val d) →
    ∃ os : List EOp, os.length ≤ 4 * ds.length ∧ ValidOpsE n Fo os ∧
      (runOpsE n Fo os).2 = [] ∧ Stored M n ιv ιg ιf ιe φ fe Lo (runOpsE n Fo os).1 T val'
  | [], Fo, val, val', hS, h => by
    have : val' = val := funext fun d => h d (List.not_mem_nil)
    subst this
    exact ⟨[], le_rfl, trivial, rfl, hS⟩
  | d :: ds, Fo, val, val', hS, h => by
    obtain ⟨os1, hl1, hv1, ho1, hS1⟩ := dart_stored hL hS d (val' d)
    obtain ⟨os2, hl2, hv2, ho2, hS2⟩ := darts_stored hL ds hS1 (val' := val') fun x hx => by
      by_cases hxd : x = d
      · subst hxd; simp
      · rw [Function.update_of_ne hxd]; exact h x (by simp [hxd, hx])
    obtain ⟨hv, ho, hr⟩ := ops_seq hv1 ho1 hv2 ho2
    refine ⟨os1 ++ os2, by simp only [List.length_append, List.length_cons]; omega, hv, ho, ?_⟩
    rw [hr]; exact hS2

end StoredOps

/-! ### The changes of the weights between two moves -/

section Weights

variable {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

local notation "𝒢" => pieceGraph M S ℓ

variable (M k g S) in
/-- **The darts whose weight may change** between the move `j` and the move `j + 1`: the darts of
the piece leaving the targets of the two moves. -/
def tripΔ (j : ℕ) : Finset D :=
  S.filter fun d => M.tail d = tripDst M k g j ∨ M.tail d = tripDst M k g (j + 1)

/-- **The weights change only on `tripΔ`** (the reach of the other vertices does not depend on
the root, and a root is reached only from itself). -/
lemma tripWt_succ (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (j : ℕ) {d : D}
    (hd : d ∉ tripΔ M k g S j) : tripWt M k g S ℓ (j + 1) d = tripWt M k g S ℓ j d := by
  unfold tripWt
  by_cases hS : d ∈ S
  · have hne : ¬ (M.tail d = tripDst M k g j ∨ M.tail d = tripDst M k g (j + 1)) := fun h =>
      hd (mem_filter.2 ⟨hS, h⟩)
    have key : Reach 𝒢 (tripDst M k g (j + 1)) (M.tail d) ↔
        Reach 𝒢 (tripDst M k g j) (M.tail d) := by
      by_cases hr : IsRoot M k g (M.tail d)
      · constructor <;> intro h <;> exact absurd (H.eq_of_reach_root h hr) (by tauto)
      · exact ⟨hR _ (H.mod_lt (j + 1 + 1)) _ (H.mod_lt (j + 1)) _ hr,
          hR _ (H.mod_lt (j + 1)) _ (H.mod_lt (j + 1 + 1)) _ hr⟩
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ⟨hS, key.1 h1.2⟩ h2
    · exact absurd ⟨hS, key.2 h2.2⟩ h1
    · rfl
  · simp [hS]

lemma card_dst_le (H : Hyp M k g S ℓ) (c : ℕ) (x : V) :
    ((range k).filter fun j => x = tripDst M k g (j + c)).card ≤ 1 := by
  refine card_le_one.2 fun a ha b hb => ?_
  simp only [mem_filter, mem_range] at ha hb
  have h := H.face.inj _ (H.mod_lt _) _ (H.mod_lt _) (ha.2.symm.trans hb.2)
  have h2 : a ≡ b [MOD k] := Nat.ModEq.add_right_cancel' (c + 1) (by
    unfold Nat.ModEq; simpa [add_assoc] using h)
  rwa [Nat.ModEq, Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at h2

/-- **At most `2 #S` weight changes over the `k` moves**: each dart of the piece leaves one
vertex, the target of one move only. -/
theorem sum_tripΔ_le (H : Hyp M k g S ℓ) :
    ∑ j ∈ range k, (tripΔ M k g S j).card ≤ 2 * S.card := by
  classical
  have e : ∀ j, (tripΔ M k g S j).card = ∑ d ∈ S,
      if M.tail d = tripDst M k g j ∨ M.tail d = tripDst M k g (j + 1) then 1 else 0 :=
    fun j => by rw [tripΔ, card_filter]
  simp_rw [e]
  rw [sum_comm]
  calc ∑ d ∈ S, ∑ j ∈ range k,
          (if M.tail d = tripDst M k g j ∨ M.tail d = tripDst M k g (j + 1) then 1 else 0)
        ≤ ∑ d ∈ S, 2 := sum_le_sum fun d _ => ?_
    _ = 2 * S.card := by rw [sum_const, smul_eq_mul, mul_comm]
  rw [← card_filter, filter_or]
  have h0 := card_dst_le H 0 (M.tail d)
  have h1 := card_dst_le H 1 (M.tail d)
  simp only [add_zero] at h0
  exact (card_union_le _ _).trans (by omega)

end Weights

/-! ### From one move to the next on the stored data -/

section Next

variable {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
variable {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

variable (V S ℓ) in
/-- The bound of the shift of the values at the nodes of the faces in one pivot of the trip. -/
def tripK : ℤ := driftK (tripL V S ℓ) (tripW S ℓ) (Fintype.card V)

lemma tripK_nonneg : 0 ≤ tripK V S ℓ := by
  unfold tripK driftK; positivity

variable (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hLay : Layout M n ιv ιg ιf ιe)
include H hR hLay

/-- **From the end of the move `j` to the start of the move `j + 1` on the stored data**: `evert`
at the node of the next source (`rerootChild_stored`), the reparenting of the next target on the
next boundary dart when it is not its parent dart already (`pivot_stored`, with the value of
`reparent_vinv`), `evert` at the node of the face of the next boundary dart (the cotree re-rooted
there), and the changes of the values of the darts of `tripΔ j` (`darts_stored`): at most
`18 + 4 #(tripΔ j)` valid operations, printing nothing, store data at the start of the move
`j + 1` (`StartOK`), linked to the end of the move `j` as in `IsTrip`; the values at the nodes of
the faces are lowered by at most `tripK`. -/
theorem next_stored {j : ℕ} {R : MoveData M S} (h : MoveSpec M k g S ℓ j R) {Fo : Forest}
    {Lo : ℝ} (hS : Stored M n ιv ιg ιf ιe (tripφ S ℓ) (M.face (g (j % k))) Lo Fo (R.T R.m)
      (R.val R.m)) :
    ∃ (os : List EOp) (T' : DTree M.dual) (val' : D → ℤ),
      os.length ≤ 18 + 4 * (tripΔ M k g S j).card ∧ ValidOpsE n Fo os ∧
      (runOpsE n Fo os).2 = [] ∧
      Stored M n ιv ιg ιf ιe (tripφ S ℓ) (M.face (g ((j + 1) % k))) (Lo - tripK V S ℓ)
        (runOpsE n Fo os).1 T' val' ∧
      StartOK M k g S ℓ (j + 1) T' val' ∧ T'.root = tripDst M k g j ∧
      T'.par (tripDst M k g (j + 1)) = g ((j + 1) % k) ∧
      (tripDst M k g (j + 1) ≠ tripSrc M k g j →
        T'.par (tripSrc M k g j) = M.rev (g (j % k))) ∧
      ∀ x, x ≠ tripSrc M k g j → x ≠ tripDst M k g (j + 1) → T'.par x = (R.T R.m).par x := by
  classical
  have hC := h.1.compat R.m le_rfl
  rw [end_tpar H hR h] at hC
  have hV := h.1.vinv R.m le_rfl
  have hk := H.two_le_k
  have hK0 : (0 : ℝ) ≤ tripK V S ℓ := by exact_mod_cast tripK_nonneg
  have e1 : (j + 1 + 1) % k = ((j + 1) % k + 1) % k := (Nat.mod_add_mod _ _ _).symm
  have hwv : tripDst M k g (j + 1) ≠ tripDst M k g j := by
    intro h'
    exact H.mod_ne (j + 1) (H.face.inj _ (H.mod_lt (j + 1 + 1)) _ (H.mod_lt (j + 1)) h').symm
  have hvu : tripDst M k g j ≠ tripSrc M k g j := fun h' =>
    H.mod_ne j (H.face.inj _ (H.mod_lt j) _ (H.mod_lt (j + 1)) h'.symm)
  have he'w : M.head (g ((j + 1) % k)) = tripDst M k g (j + 1) := by
    rw [H.head_g _ (H.mod_lt _)]; unfold tripDst; rw [e1]
  -- re-rooting the spanning tree at the next source
  have hv : tripDst M k g j ≠ (R.T R.m).root := by rw [hC.root]; exact hvu
  have hup : M.tail ((R.T R.m).par (tripDst M k g j)) = (R.T R.m).root := by
    rw [hC.par_v, hC.tail, hC.root]
  obtain ⟨hv1, ho1, hS1⟩ := rerootChild_stored hLay hS hv hup
  set T₁ := rerootChild (R.T R.m) _ hv hup with hT₁
  set F1 := (runOpsE n Fo [.evert (ιv (tripDst M k g j))]).1 with hF1
  have hV₁ : VInv T₁ (tripφ S ℓ) (tripWt M k g S ℓ j) (R.val R.m) :=
    rerootChild_vinv _ hv hup (by rw [hC.par_v]; exact H.tripφ_g j)
      (by rw [hC.par_v]; exact H.tripφ_rev_g j) hV
  have hr₁ : T₁.root = tripDst M k g j := rfl
  have hpu : T₁.par (tripSrc M k g j) = M.rev (g (j % k)) := by
    rw [← hC.root, hT₁, rerootChild_par_root, hC.par_v]
  have hpx : ∀ x, x ≠ tripSrc M k g j → T₁.par x = (R.T R.m).par x := fun x hx =>
    rerootChild_par _ hv hup x (by rw [hC.root]; exact hx)
  -- the reparenting of the next target
  have step2 : ∃ (os : List EOp) (T₂ : DTree M.dual) (val₂ : D → ℤ), os.length ≤ 16 ∧
      ValidOpsE n F1 os ∧ (runOpsE n F1 os).2 = [] ∧
      Stored M n ιv ιg ιf ιe (tripφ S ℓ) (M.face (g (j % k))) (Lo - tripK V S ℓ)
        (runOpsE n F1 os).1 T₂ val₂ ∧ VInv T₂ (tripφ S ℓ) (tripWt M k g S ℓ j) val₂ ∧
      T₂.root = tripDst M k g j ∧ T₂.par (tripDst M k g (j + 1)) = g ((j + 1) % k) ∧
      (tripDst M k g (j + 1) ≠ tripSrc M k g j →
        T₂.par (tripSrc M k g j) = M.rev (g (j % k))) ∧
      ∀ x, x ≠ tripSrc M k g j → x ≠ tripDst M k g (j + 1) → T₂.par x = (R.T R.m).par x := by
    by_cases hin : T₁.par (tripDst M k g (j + 1)) = g ((j + 1) % k)
    · exact ⟨[], T₁, R.val R.m, by simp, trivial, rfl, hS1.mono (by linarith), hV₁, hr₁, hin,
        fun _ => hpu, fun x hx _ => hpx x hx⟩
    have hw₁ : tripDst M k g (j + 1) ≠ T₁.root := hwv
    have hby : M.dual.face (M.dual.rev (g ((j + 1) % k))) = tripDst M k g (j + 1) := he'w
    have hna : ¬ T₁.Anc (tripDst M k g (j + 1)) (M.dual.face (g ((j + 1) % k))) := by
      change ¬ T₁.Anc (tripDst M k g (j + 1)) T₁.root
      rw [T₁.anc_root_iff]; exact hwv
    have hbT : ¬ T₁.InT (g ((j + 1) % k)) := by
      rintro ⟨x, hx, hd | hd⟩
      · have : x = tripDst M k g (j + 1) := by rw [← tpar_head T₁ hx, ← hd, he'w]
        subst this; exact hin hd.symm
      · have hd' : g ((j + 1) % k) = M.rev (T₁.par x) := hd
        have : M.head (T₁.par x) = tripDst M k g j := by
          rw [← M.tail_rev, ← hd']; rfl
        rw [tpar_head T₁ hx] at this
        exact hx this
    set c := R.val R.m (g ((j + 1) % k)) - tripWt M k g S ℓ j (g ((j + 1) % k)) +
      tripφ S ℓ (g ((j + 1) % k)) with hc
    have hcK : |(c : ℝ)| ≤ tripK V S ℓ := by
      have hc' : |c| ≤ tripK V S ℓ := by
        have e2 := hV₁ _ hbT
        have hB3 := abs_le.1 (abs_psum_le_mul T₁ (abs_tripφ_le (S := S) (ℓ := ℓ))
          (M.tail (g ((j + 1) % k))))
        have hB4 := abs_le.1 (abs_psum_le_mul T₁ (abs_tripφ_le (S := S) (ℓ := ℓ))
          (M.head (g ((j + 1) % k))))
        have hWd := abs_le.1 (abs_tripφ_le (S := S) (ℓ := ℓ) (g ((j + 1) % k)))
        have l1 := abs_nonneg (tripL V S ℓ)
        have l3 := le_abs_self (tripW S ℓ)
        have l5 := le_abs_self ((Fintype.card V : ℤ) * tripW S ℓ)
        unfold tripK driftK
        rw [hc, e2]
        exact abs_le.2 ⟨by linarith, by linarith⟩
      rw [← Int.cast_abs]; exact_mod_cast hc'
    obtain ⟨os2, hl2, hv2, ho2, hS2⟩ :=
      pivot_stored H.plane hLay hS1 hw₁ hby hna hbT (tripWt M k g S ℓ j) c
    refine ⟨os2, _, _, hl2.le, hv2, ho2, hS2.mono (by linarith),
      reparent_vinv H.plane T₁ hw₁ hby hna hbT hV₁, hr₁, ?_, ?_, fun x hx hxw => ?_⟩
    · show Function.update T₁.par _ _ _ = _
      exact Function.update_self _ _ _
    · intro hwu
      show Function.update T₁.par _ _ _ = _
      rw [Function.update_of_ne (Ne.symm hwu)]; exact hpu
    · show Function.update T₁.par _ _ _ = _
      rw [Function.update_of_ne hxw]; exact hpx x hx
  obtain ⟨os2, T₂, val₂, hl2, hv2, ho2, hS2, hV₂, hr₂, hpw₂, hpu₂, hpx₂⟩ := step2
  -- the cotree re-rooted at the face of the next boundary dart
  obtain ⟨hv3, ho3, hS3⟩ := recot_stored hLay hS2 (M.face (g ((j + 1) % k)))
  -- the changes of the weights
  obtain ⟨os4, hl4, hv4, ho4, hS4⟩ := darts_stored hLay (tripΔ M k g S j).toList hS3
    (val' := fun d => val₂ d + tripWt M k g S ℓ (j + 1) d - tripWt M k g S ℓ j d)
    fun d hd => by
      rw [tripWt_succ H hR j (fun h' => hd (mem_toList.2 h'))]; ring
  obtain ⟨hv34, ho34, hr34⟩ := ops_seq hv3 ho3 hv4 ho4
  obtain ⟨hv24, ho24, hr24⟩ := ops_seq hv2 ho2 hv34 ho34
  obtain ⟨hv14, ho14, hr14⟩ := ops_seq hv1 ho1 hv24 ho24
  refine ⟨_ ++ (os2 ++ (_ ++ os4)), T₂,
    fun d => val₂ d + tripWt M k g S ℓ (j + 1) d - tripWt M k g S ℓ j d, ?_, hv14, ho14, ?_,
    ⟨⟨hr₂, hpw₂, rfl, ?_⟩, ?_⟩, hr₂, hpw₂, hpu₂, hpx₂⟩
  · simp only [List.length_append, List.length_singleton, length_toList] at hl4 ⊢
    omega
  · rw [hr14, ← hF1, hr24, hr34]; exact hS4
  · intro x a hx
    obtain ⟨-, hd, -⟩ := tpar_spec hx
    have hnr : ∀ i < k, x ≠ M.tail (g i) := fun i hi h' =>
      H.noIn a.1 a.2 ⟨i, hi, by rw [← h', ← hd]; rfl⟩
    rw [hpx₂ x (hnr _ (H.mod_lt j)) (hnr _ (H.mod_lt (j + 1 + 1)))]
    exact hC.par x a hx
  · intro d hd
    show val₂ d + _ - _ = _
    rw [hV₂ d hd]; ring

end Next

/-! ### The trip up to a number of moves -/

section UpTo

variable {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

local notation "𝒢" => pieceGraph M S ℓ

variable (M k g S ℓ) in
/-- **The first `J` moves of a trip**: the moves `j < J` meet `MoveSpec`, and the tree at the
start of the move `j + 1 ≤ J` is linked to the tree at the end of the move `j` as in `IsTrip`. -/
structure IsTripUpTo (J : ℕ) (R : ℕ → MoveData M S) : Prop where
  move : ∀ j < J, MoveSpec M k g S ℓ j (R j)
  root : ∀ j < J, ((R (j + 1)).T 0).root = tripDst M k g j
  par_dst : ∀ j < J, ((R (j + 1)).T 0).par (tripDst M k g (j + 1)) = g ((j + 1) % k)
  par_src : ∀ j < J, tripDst M k g (j + 1) ≠ tripSrc M k g j →
    ((R (j + 1)).T 0).par (tripSrc M k g j) = M.rev (g (j % k))
  par_other : ∀ j < J, ∀ x, x ≠ tripSrc M k g j → x ≠ tripDst M k g (j + 1) →
    ((R (j + 1)).T 0).par x = ((R j).T (R j).m).par x

/-- A trip gives its first `J` moves. -/
lemma IsTrip.upTo {R : ℕ → MoveData M S} (hT : IsTrip M k g S ℓ R) (J : ℕ) :
    IsTripUpTo M k g S ℓ J R :=
  ⟨fun j _ => hT.move j, fun j _ => hT.root j, fun j _ => hT.par_dst j,
    fun j _ => hT.par_src j, fun j _ => hT.par_other j⟩

variable (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ)
include H hR

/-- **The labels at the start of a move are the distances from its source** (as
`IsTrip.labels`, for one move). -/
theorem MoveSpec.labels {j : ℕ} {R : MoveData M S} (h : MoveSpec M k g S ℓ j R) {x : V}
    (hx : Reach 𝒢 (tripSrc M k g j) x) :
    (R.T 0).psum (tripφ S ℓ) x = dist 𝒢 (tripSrc M k g j) x := by
  have Hm := H.tripMoveHyp hR j
  have hd := h.1
  have hC := hd.compat 0 (Nat.zero_le _)
  rw [hd.init] at hC
  have hI : RInv 𝒢 _ _ (tpar 𝒢 (tripSrc M k g j)) := rInv_init Hm
  have hb : ∀ y, Hang 𝒢 (tpar 𝒢 (tripSrc M k g j)) (tripDst M k g j) y →
      y = tripDst M k g j := by
    intro y h
    induction h with
    | root => rfl
    | step ha _ ih =>
      obtain ⟨⟨hz, -⟩, -, -⟩ := tpar_spec ha
      rw [ih] at hz
      exact absurd hz Hm.not_reach_uv
  have hxv : x ≠ tripDst M k g j := fun h => Hm.not_reach_uv (h ▸ hx)
  refine psum_red Hm hI hC (fun d hd => tripφ_of_mem hd) ?_ (fun h => hxv (hb x h))
  by_cases hxu : x = tripSrc M k g j
  · rw [hxu]; exact .root
  · rcases hI.forest Hm x (Hm.mem_moveSet.2 ⟨hxu, hxv, hx⟩) with h | h
    · exact h
    · exact absurd (hb x h) hxv

/-- **The `k` moves around the face make at most `#S` pivots in total** (as `IsTrip.pivots`). -/
theorem IsTripUpTo.pivots {J : ℕ} {R : ℕ → MoveData M S} (hT : IsTripUpTo M k g S ℓ J R)
    (hJ : k ≤ J) : ∑ j ∈ range k, (R j).m ≤ S.card := by
  by_cases hS : S.Nonempty
  · refine klein_run_pivots H hR (fun j => (R j).m) fun j hj => ?_
    have hjk : j % k = j := Nat.mod_eq_of_lt hj
    have hrun := dataRun_isRun H.plane (H.tripMoveHyp hR j) H.uniq (H.g_not_mem j)
      (H.rev_g_not_mem j) (fun d hd => tripφ_of_mem hd) (fun d hd hr => tripWt_elig j hd hr)
      (fun d hd => tripWt_inelig j hd) (fun d hd => tripL_gt hd) (hT.move j (by omega)).1
      ⟨_, hS.choose_spec⟩
    unfold tripSrc tripDst at hrun
    rw [hjk] at hrun
    exact ⟨_, _, hrun⟩
  · have hm : ∀ j ∈ range k, (R j).m = 0 := fun j hj => by
      by_contra h0
      obtain ⟨h, -⟩ := (hT.move j (by simp at hj; omega)).1.next 0 (by omega)
      exact hS ⟨_, h⟩
    simp [sum_eq_zero hm]

end UpTo

/-! ### The trip on the stored data -/

section TripStored

variable {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
variable {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

local notation "𝒢" => pieceGraph M S ℓ

variable (M k g S ℓ n ιv ιg ιf ιe) in
/-- **The first `J` moves of a trip on the stored data**: the data `R` of the first `J` moves
(`IsTripUpTo`; `R J` holds the data at the start of the move `J`, `StartOK`) and a list of valid
operations from the empty forest whose run stores, after a prefix, the data at the start of every
move `j ≤ J` (`Stored`: the tree `(R j).T 0` with the weights `tripφ`, a cotree rooted at the face
of the boundary dart `g (j % k)` with the values `(R j).val 0`), the whole list storing the data
at the start of the move `J` with the bound `Lo` of the values at the nodes of the faces; its
length is at most `6 (#V + #F)` plus, per move `j < J`, `17` per pivot, `19`, and `4` per dart of
`tripΔ j`. -/
structure TripStored (J : ℕ) (R : ℕ → MoveData M S) (os : List EOp) (Lo : ℝ) : Prop where
  trip : IsTripUpTo M k g S ℓ J R
  start : StartOK M k g S ℓ J ((R J).T 0) ((R J).val 0)
  valid : ValidOpsE n (Forest.init n) os
  len : os.length ≤ 6 * (Fintype.card V + Fintype.card F) +
    ∑ j ∈ range J, (17 * (R j).m + 19 + 4 * (tripΔ M k g S j).card)
  stored : Stored M n ιv ιg ιf ιe (tripφ S ℓ) (M.face (g (J % k))) Lo
    (runOpsE n (Forest.init n) os).1 ((R J).T 0) ((R J).val 0)
  pre : ∀ j ≤ J, ∃ (p r : List EOp) (Lo' : ℝ), os = p ++ r ∧
    Stored M n ιv ιg ιf ιe (tripφ S ℓ) (M.face (g (j % k))) Lo'
      (runOpsE n (Forest.init n) p).1 ((R j).T 0) ((R j).val 0)

/-- The data of a move with no pivot, at the given start. -/
def startData (T : DTree M.dual) (val : D → ℤ) (d₀ : D) : MoveData M S :=
  ⟨fun _ => T, fun _ => val, fun _ _ => none, fun _ => d₀, 0⟩

variable (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hLay : Layout M n ιv ιg ιf ιe)
include H hR hLay

/-- **The start of the trip on the stored data**: the data `tripStart`-like at the start of the
move `0` (`exists_start0`), a cotree rooted at the face of `g 0` (`exists_cotree`), stored from
the empty forest (`init_stored`) with the value `H₀` at the nodes of the faces. -/
theorem tripStored_zero (H₀ : ℤ) :
    ∃ (R : ℕ → MoveData M S) (os : List EOp),
      TripStored M k g S ℓ n ιv ιg ιf ιe 0 R os H₀ := by
  obtain ⟨T, val, hs⟩ := exists_start0 H hR
  have : Nonempty D := ⟨g 0⟩
  obtain ⟨C, hCr, hoff⟩ := exists_cotree H.plane T (M.face (g (0 % k)))
  obtain ⟨os, hl, hv, -, hS⟩ := init_stored hLay hoff (tripφ S ℓ) val H₀
  rw [hCr] at hS
  refine ⟨fun _ => startData T val (g 0), os, ⟨⟨fun j hj => absurd hj (by omega),
    fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
    fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega)⟩, hs, hv, by simpa using hl,
    hS, fun j hj => ⟨os, [], H₀, by simp, ?_⟩⟩⟩
  obtain rfl : j = 0 := by omega
  exact hS

/-- **One more move on the stored data**: from the stored data at the start of the move `J`
(with the values at the nodes of the faces high enough), the move (`move_stored`) and the step to
the next move (`next_stored`); the bound of the values at the nodes of the faces drops by at most
`(#V + 1) tripK`. -/
theorem tripStored_succ {J : ℕ} {R : ℕ → MoveData M S} {os : List EOp} {Lo : ℝ}
    (hT : TripStored M k g S ℓ n ιv ιg ιf ιe J R os Lo)
    (hLo : ((tripL V S ℓ - 2 * (Fintype.card V * tripW S ℓ) : ℤ) : ℝ) +
      Fintype.card V * (tripK V S ℓ : ℝ) ≤ Lo) :
    ∃ (R' : ℕ → MoveData M S) (os' : List EOp) (Lo' : ℝ),
      TripStored M k g S ℓ n ιv ιg ιf ιe (J + 1) R' os' Lo' ∧
        Lo - (Fintype.card V + 1) * (tripK V S ℓ : ℝ) ≤ Lo' := by
  classical
  have hs := hT.start
  obtain ⟨T, val, d, m, os1, w, Lo1, hT0, hv0, hrun, hTs, hl1, hv1, -, hS1, hLo1⟩ :=
    move_stored H.plane (H.tripMoveHyp hR J) H.uniq (H.g_not_mem J) (H.rev_g_not_mem J)
      (fun d hd => tripφ_of_mem hd) (W := tripW S ℓ) abs_tripφ_le
      (fun d hd hr => tripWt_elig J hd hr) (fun d hd => tripWt_inelig J hd)
      (fun d hd => tripL_gt hd) hLay hs.1 hs.2 hT.stored hLo
  set RJ : MoveData M S := ⟨T, val, selForest M S (tpar 𝒢 (tripSrc M k g J)) d, d, m⟩ with hRJ
  have hMJ : MoveSpec M k g S ℓ J RJ := ⟨hrun, hTs⟩
  obtain ⟨os2, T', val', hl2, hv2, ho2, hS2, hstart, hr, hpw, hpu, hpx⟩ :=
    next_stored H hR hLay hMJ hS1
  set R' : ℕ → MoveData M S := fun i =>
    if i < J then R i else if i = J then RJ else startData T' val' (g 0) with hR'
  have hlt : ∀ i < J, R' i = R i := fun i hi => by simp [hR', hi]
  have hJ : R' J = RJ := by simp [hR']
  have hJ1 : R' (J + 1) = startData T' val' (g 0) := by simp [hR']
  have hT0' : ∀ i ≤ J, (R' i).T 0 = (R i).T 0 ∧ (R' i).val 0 = (R i).val 0 := by
    intro i hi
    rcases Nat.lt_or_ge i J with h | h
    · rw [hlt i h]; exact ⟨rfl, rfl⟩
    · obtain rfl : i = J := by omega
      rw [hJ]; exact ⟨hT0, hv0⟩
  have hrun1 : (runOpsE n (Forest.init n) (os ++ (os1 ++ os2))).1 =
      (runOpsE n (runOpsE n (runOpsE n (Forest.init n) os).1 os1).1 os2).1 := by
    rw [runOpsE_append, runOpsE_append]
  have hK0 : (0 : ℝ) ≤ tripK V S ℓ := by exact_mod_cast tripK_nonneg
  refine ⟨R', os ++ (os1 ++ os2), Lo1 - tripK V S ℓ, ⟨⟨fun j hj => ?_, fun j hj => ?_,
    fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩, ?_, ?_, ?_, ?_, fun j hj => ?_⟩, ?_⟩
  · rcases Nat.lt_or_ge j J with h | h
    · rw [hlt j h]; exact hT.trip.move j h
    · obtain rfl : j = J := by omega
      rw [hJ]; exact hMJ
  · rcases Nat.lt_or_ge j J with h | h
    · rw [(hT0' (j + 1) h).1]; exact hT.trip.root j h
    · obtain rfl : j = J := by omega
      rw [hJ1]; exact hr
  · rcases Nat.lt_or_ge j J with h | h
    · rw [(hT0' (j + 1) h).1]; exact hT.trip.par_dst j h
    · obtain rfl : j = J := by omega
      rw [hJ1]; exact hpw
  · rcases Nat.lt_or_ge j J with h | h
    · rw [(hT0' (j + 1) h).1]; exact hT.trip.par_src j h
    · obtain rfl : j = J := by omega
      rw [hJ1]; exact hpu
  · rcases Nat.lt_or_ge j J with h | h
    · intro x hx1 hx2
      rw [(hT0' (j + 1) h).1, hlt j h]; exact hT.trip.par_other j h x hx1 hx2
    · obtain rfl : j = J := by omega
      rw [hJ1, hJ]; exact hpx
  · rw [hJ1]; exact hstart
  · refine (validOpsE_append n _ _ _).2 ⟨hT.valid, (validOpsE_append n _ _ _).2 ⟨hv1, hv2⟩⟩
  · rw [sum_range_succ, hJ, sum_congr rfl fun i hi => by rw [hlt i (mem_range.1 hi)]]
    have := hT.len
    have hm : RJ.m = m := rfl
    simp only [List.length_append, hl1, hm]
    omega
  · rw [hrun1, hJ1]; exact hS2
  · rcases Nat.lt_or_ge j (J + 1) with h | h
    · obtain ⟨p, r, Lo', hpr, hp⟩ := hT.pre j (by omega)
      refine ⟨p, r ++ (os1 ++ os2), Lo', by rw [hpr, List.append_assoc], ?_⟩
      rw [(hT0' j (by omega)).1, (hT0' j (by omega)).2]; exact hp
    · obtain rfl : j = J + 1 := by omega
      refine ⟨os ++ (os1 ++ os2), [], Lo1 - tripK V S ℓ, by simp, ?_⟩
      rw [hrun1, hJ1]; exact hS2
  · have e : (tripK V S ℓ : ℝ) = (driftK (tripL V S ℓ) (tripW S ℓ) (Fintype.card V) : ℝ) := rfl
    rw [← e] at hLo1
    linarith

/-- **The first `J` moves of a trip on the stored data**, from the empty forest (the value at the
nodes of the faces chosen high enough for `J` moves). -/
theorem trip_stored (J : ℕ) : ∃ (R : ℕ → MoveData M S) (os : List EOp) (Lo : ℝ),
    TripStored M k g S ℓ n ιv ιg ιf ιe J R os Lo := by
  set z : ℝ := ((tripL V S ℓ - 2 * (Fintype.card V * tripW S ℓ) : ℤ) : ℝ) with hz
  set c : ℝ := (Fintype.card V + 1) * (tripK V S ℓ : ℝ) with hc
  have hK0 : (0 : ℝ) ≤ tripK V S ℓ := by exact_mod_cast tripK_nonneg
  have hc0 : 0 ≤ c := by positivity
  have hVc : (Fintype.card V : ℝ) * tripK V S ℓ ≤ c := by rw [hc]; nlinarith
  set H₀ : ℤ := (tripL V S ℓ - 2 * (Fintype.card V * tripW S ℓ)) +
    (J + 1) * ((Fintype.card V + 1) * tripK V S ℓ) with hH₀def
  have hH₀ : (H₀ : ℝ) = z + (J + 1) * c := by
    rw [hH₀def, hz, hc]; push_cast; ring
  have key : ∀ i ≤ J, ∃ (R : ℕ → MoveData M S) (os : List EOp) (Lo : ℝ),
      TripStored M k g S ℓ n ιv ιg ιf ιe i R os Lo ∧ z + (J + 1) * c ≤ Lo + i * c := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨R, os, h⟩ := tripStored_zero H hR hLay H₀
      exact ⟨R, os, _, h, by rw [hH₀]; simp⟩
    | succ i ih =>
      intro hi
      obtain ⟨R, os, Lo, h, hLo⟩ := ih (by omega)
      have hi' : (i : ℝ) + 1 ≤ J := by exact_mod_cast hi
      obtain ⟨R', os', Lo', h', hLo'⟩ := tripStored_succ H hR hLay h (by
        rw [← hz]
        nlinarith [mul_nonneg (sub_nonneg.2 hi') hc0])
      exact ⟨R', os', Lo', h', by push_cast; linarith⟩
  obtain ⟨R, os, Lo, h, -⟩ := key J le_rfl
  exact ⟨R, os, Lo, h⟩

/-- **The labels at the start of every move are stored**: after a prefix of the list, the path
sums at the nodes of the vertices are the distances from the source of the move. -/
theorem TripStored.labels {J : ℕ} {R : ℕ → MoveData M S} {os : List EOp} {Lo : ℝ}
    (hT : TripStored M k g S ℓ n ιv ιg ιf ιe J R os Lo) {j : ℕ} (hj : j < J) :
    ∃ p r : List EOp, os = p ++ r ∧ ∀ x, Reach 𝒢 (tripSrc M k g j) x →
      pathSum (runOpsE n (Forest.init n) p).1 n (ιv x) = dist 𝒢 (tripSrc M k g j) x := by
  obtain ⟨p, r, Lo', hpr, hp⟩ := hT.pre j hj.le
  refine ⟨p, r, hpr, fun x hx => ?_⟩
  rw [lct_label hp.tree hLay.prim.f_lt hLay.prim.e_lt hLay.hv x]
  exact_mod_cast MoveSpec.labels H hR (hT.trip.move j hj) hx

end TripStored

/-! ### The trip around the face -/

section Headline

variable {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

local notation "𝒢" => pieceGraph M S ℓ

variable (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ)
include H hR

/-- **The trip around the face on the stored data**: on `2 (#V + #F + #D)` nodes, the data `R`
of the `k` moves around the face (`IsTripUpTo k`, inside `TripStored`) and a list of valid
operations from the empty forest storing them, of length at most
`6 (#V + #F) + 17 p + 19 k + 8 #S` with `p ≤ #S` the number of pivots. -/
theorem klein_trip_stored :
    ∃ (n : ℕ) (ιv : V → ℕ) (ιg : D → ℕ) (ιf : F → ℕ) (ιe : D → ℕ) (R : ℕ → MoveData M S)
      (os : List EOp) (Lo : ℝ), Layout M n ιv ιg ιf ιe ∧
      n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D) ∧
      TripStored M k g S ℓ n ιv ιg ιf ιe k R os Lo ∧
      os.length ≤ 6 * (Fintype.card V + Fintype.card F) + 17 * ∑ j ∈ range k, (R j).m +
        19 * k + 8 * S.card ∧
      ∑ j ∈ range k, (R j).m ≤ S.card := by
  obtain ⟨ιv, ιg, ιf, ιe, hLay⟩ := exists_layout M
  obtain ⟨R, os, Lo, hT⟩ := trip_stored H hR hLay k
  have hΔ := sum_tripΔ_le H
  have e : ∑ j ∈ range k, (17 * (R j).m + 19 + 4 * (tripΔ M k g S j).card) =
      17 * ∑ j ∈ range k, (R j).m + 19 * k + 4 * ∑ j ∈ range k, (tripΔ M k g S j).card := by
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, card_range,
      smul_eq_mul, mul_comm k 19]
  have hl := hT.len
  rw [e] at hl
  exact ⟨_, ιv, ιg, ιf, ιe, R, os, Lo, hLay, rfl, hT, by omega, hT.trip.pivots H hR le_rfl⟩

/-- **The trip around the face as a list of operations** (Klein's algorithm, in the form of
Cabello, Chambers and Erickson, on the evertable link-cut trees): on `n = 2 (#V + #F + #D)`
nodes, a list of valid operations from the empty forest, of length at most `25 (#V + #F + #D)`,
after a prefix of which, for every move `j < k` around the face, the path sum at the node `ιv x`
of every vertex `x` reached from the source `tripSrc j` of the move is the distance from that
source (the query `sum` reads the path sum). The list is adaptive: it is chosen from the answers
of the queries `min2` printed before (`move_stored`). -/
theorem klein_trip_ops :
    ∃ (n : ℕ) (ιv : V → ℕ) (os : List EOp),
      n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D) ∧ Function.Injective ιv ∧
      (∀ x, ιv x < n) ∧ ValidOpsE n (Forest.init n) os ∧
      os.length ≤ 25 * (Fintype.card V + Fintype.card F + Fintype.card D) ∧
      ∀ j < k, ∃ p r : List EOp, os = p ++ r ∧ ∀ x, Reach 𝒢 (tripSrc M k g j) x →
        pathSum (runOpsE n (Forest.init n) p).1 n (ιv x) = dist 𝒢 (tripSrc M k g j) x := by
  obtain ⟨n, ιv, ιg, ιf, ιe, R, os, Lo, hLay, hn, hT, hl, hp⟩ := klein_trip_stored H hR
  have hk := H.k_le_card
  have hS : S.card ≤ Fintype.card D := card_le_univ S
  exact ⟨n, ιv, os, hn, hLay.prim.f_inj, hLay.prim.f_lt, hT.valid, by omega,
    fun j hj => hT.labels H hR hLay hj⟩

end Headline

/-! ### The cost of running the list -/

section Cost

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

local notation "𝒢" => pieceGraph M S ℓ

variable (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ)
include H hR

/-- **The allowances of the counted cost are met** (`Klein/Cost.lean`): the list of operations
of the trip around the face (`klein_trip_stored`) has length at most `tripOps N #S k p 0`
(`N = #V + #F + #D`, `p` the number of pivots), and run as a fixed list on the machine
(`PlanarFlow.DynTree.lctE_runsWithin`) it prints its answers within
`400000 (n + tripOps N #S k p 0 + 1) (⌊log₂ n⌋ + 1)` steps, `n = 2 N`, hence within
`400000 (82 N + 1) (⌊log₂ n⌋ + 1)` steps. The list is adaptive (each pivot is chosen from the
answer of the query `min2` before it): this is the cost of running the list once it is known;
the program that chooses it is `kleinProg` (`klein_exec`). -/
theorem klein_trip_cost :
    ∃ (n : ℕ) (ιv : V → ℕ) (R : ℕ → MoveData M S) (os : List EOp),
      n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D) ∧ IsTripUpTo M k g S ℓ k R ∧
      ValidOpsE n (Forest.init n) os ∧
      os.length ≤ tripOps (Fintype.card V + Fintype.card F + Fintype.card D) S.card k
        (∑ j ∈ range k, (R j).m) 0 ∧
      (∀ j < k, ∃ p r : List EOp, os = p ++ r ∧ ∀ x, Reach 𝒢 (tripSrc M k g j) x →
        pathSum (runOpsE n (Forest.init n) p).1 n (ιv x) = dist 𝒢 (tripSrc M k g j) x) ∧
      ∀ (B : ℕ) (P : Input), RunsWithin (compile (runSE B n os) 0 ++ [Instr.halt]) P
        (B + 16 * (n + 1))
        (400000 * (n + tripOps (Fintype.card V + Fintype.card F + Fintype.card D) S.card k
          (∑ j ∈ range k, (R j).m) 0 + 1) * (Nat.log 2 n + 1))
        (runOpsE n (Forest.init n) os).2 ∧
      RunsWithin (compile (runSE B n os) 0 ++ [Instr.halt]) P (B + 16 * (n + 1))
        (400000 * (82 * (Fintype.card V + Fintype.card F + Fintype.card D) + 1) *
          (Nat.log 2 n + 1))
        (runOpsE n (Forest.init n) os).2 := by
  obtain ⟨n, ιv, ιg, ιf, ιe, R, os, Lo, hLay, hn, hT, hl, hp⟩ := klein_trip_stored H hR
  have hk := H.k_le_card
  have hS : S.card ≤ Fintype.card D := card_le_univ S
  have hops : os.length ≤ tripOps (Fintype.card V + Fintype.card F + Fintype.card D) S.card k
      (∑ j ∈ range k, (R j).m) 0 := by
    unfold tripOps opsInit opsPivot opsMove opsWt; omega
  have hops' : tripOps (Fintype.card V + Fintype.card F + Fintype.card D) S.card k
      (∑ j ∈ range k, (R j).m) 0 ≤ 80 * (Fintype.card V + Fintype.card F + Fintype.card D) := by
    unfold tripOps opsInit opsPivot opsMove opsWt; omega
  refine ⟨n, ιv, R, os, hn, hT.trip, hT.valid, hops, fun j hj => hT.labels H hR hLay hj,
    fun B P => ⟨?_, ?_⟩⟩
  · refine RunsWithin.mono_steps (lctE_runsWithin B n os hT.valid P) ?_
    gcongr
  · refine RunsWithin.mono_steps (lctE_runsWithin B n os hT.valid P) ?_
    gcongr
    omega

end Cost

end Klein

end PlanarFlow
