module

public import PlanarFlow.BKMNW.SplitRot
public import PlanarFlow.BKMNW.DecS
public import PlanarFlow.BKMNW.SplitDHead
public import PlanarFlow.BKMNW.ExistRoot

/-!
# The headline with the rotation carried down the recursion

The headline `maxflow_plane_cost_decDD` with the rotation of the core piece map no longer a
parameter `σf P Hs`: the decomposition is `decS` (`PlanarFlow/BKMNW/DecS.lean`) with the state
`σ : Perm D`, started at the explicit root rotation `rootRot N Q = ret (rotPerm N) (core N Q univ)`
(the rotation of the map cut down to the core) and updated by the explicit child rotation `chRot`
(contract the separator path, keep the child's darts; `PlanarFlow/BKMNW/SplitRot.lean`).

* `rootRot`, **`cinvS_pendant`** (the invariant at the root for `rootRot`);
* **`splitFnsS_R`**: `SplitFnsS … (CInvS M Q) (spSR …) (spHR …) (smD M pc.pick S T) (chRot M Q)`;
* `decS_balDecA_pre`, `decS_balDecA_lpre`;
* **`maxflow_plane_cost_decDD'`**: the headline bound for
  `τ = decS (lpreMap M) (spSR …) (spHR …) (smD …) (chRot …) 100000 univ [] (rootRot …) true`;
  the only remaining parameters are the choice functions `pc : PcChoice` and
  `sc : List (Finset V) → ℕ → ℕ → ScChoice` under their local specifications.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation CombMap

universe w

section Gen

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

/-- **The root rotation**: the rotation of the map cut down to the core of the whole map. -/
noncomputable def rootRot (M : CombMap D V F) (Q : Finset V) : Perm D :=
  ret (rotPerm M) (core M Q univ)

section Pend

variable {M : CombMap D V F} {e : V → D} (he : ∀ v, M.tail (e v) = v)

/-- **The invariant at the root of a map with pendant edges, with the rotation named**: `cinv_pendant`
for the rotation `rootRot` (the rotation of the map cut down to the core). -/
theorem cinvS_pendant (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (htri : ∀ d, M.next (M.next (M.next d)) = d) :
    CInvS (M.pendant e he) (pendQ V) univ [] (rootRot (M.pendant e he) (pendQ V)) := by
  unfold rootRot
  set M' := M.pendant e he with hM'
  set K := core M' (pendQ V) univ with hK
  have hD : Nonempty D := ⟨e hM.nonempty.some⟩
  have hP' : M'.IsPlane := CombMap.pendant_isPlane he hM
  have hrot' : M'.RotTrans := CombMap.pendant_rotTrans he hrot
  have hface' : M'.FaceTrans := CombMap.pendant_faceTrans he hface
  have hroot := pieceInv_root hP' hrot' hface' ⟨Sum.inl hD.some⟩
  have hKrev : Stable (revPerm M') K := fun x hx =>
    revClosed_core (Q := pendQ V) (fun _ _ => mem_univ _) x hx
  have hKl : ∀ x ∈ K, ∃ d, x = Sum.inl d := fun x hx => by
    rcases x with d | x
    · exact ⟨d, rfl⟩
    · exact absurd ((mem_core_pendant he).1 hx) (by simp)
  have hinK : ∀ d : D, (Sum.inl d : D ⊕ (V × Bool)) ∈ K := fun d => (mem_core_pendant he).2 rfl
  refine ⟨by simp [hunion_nil'], ⟨revClosed_core (fun _ _ => mem_univ _),
    ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try simp only [pdarts_nil]
  · exact stable_ret _ _
  · have h0 := hroot.gap
    rw [pdarts_univ_nil] at h0
    exact gap_ret_eq_zero (revPerm_isInv M') (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
      (subset_univ K) hKrev h0
  · intro x hx y hy
    rw [sameCycle_ret hx hy]
    exact hroot.vert x (by rw [pdarts_univ_nil]; exact mem_univ _) y
      (by rw [pdarts_univ_nil]; exact mem_univ _)
  · -- the faces are triangles
    intro x hx
    left
    intro z hz
    obtain ⟨d, rfl⟩ := hKl x hx
    set φ := ret (rotPerm M') K * revPerm M' with hφ
    have hit : ∀ n t, φ^[n] (Sum.inl t) = Sum.inl (M.next^[n] t) := by
      intro n
      induction n with
      | zero => intro t; rfl
      | succ n ih =>
        intro t
        rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
        exact ret_rot_pendant he _
    obtain ⟨n, rfl⟩ := sameCycle_iff.1 (mem_pface.1 hz).2
    have h3 : M.next^[3] d = d := htri d
    have hmod : M.next^[n] d = M.next^[n % 3] d := by
      conv_lhs => rw [← Nat.mod_add_div n 3]
      rw [Function.iterate_add_apply]
      congr 1
      induction n / 3 with
      | zero => rfl
      | succ q ih => rw [Nat.mul_succ, Function.iterate_add_apply, h3, ih]
    rw [hit, hmod]
    have hlt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases (n % 3)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (by rw [← Function.iterate_one φ, hit]))
    · refine Or.inr (Or.inr ((Equiv.eq_symm_apply _).2 ?_))
      have := hit 1 (M.next^[2] d)
      rw [Function.iterate_one] at this
      rw [this, ← Function.iterate_add_apply]
      exact congrArg Sum.inl h3
  · -- connected
    have hc := (pcOK_univ hM hrot hface (∅ : Finset V) ∅).conn
    unfold HConn
    simp only [pdarts_nil]
    intro x hx y hy
    obtain ⟨a, rfl⟩ := hKl x hx
    obtain ⟨b, rfl⟩ := hKl y hy
    have h := hc a (by rw [pdarts_univ_nil]; exact mem_univ _) b
      (by rw [pdarts_univ_nil]; exact mem_univ _)
    refine ReflTransGen.lift Sum.inl ?_ _ _ h
    intro s t hst
    refine ⟨hinK t, ?_⟩
    rcases hst.2 with h1 | h1
    · exact Or.inl (by rw [h1]; rfl)
    · rcases h1 with h1 | ⟨H, hH, -⟩
      · exact Or.inr (Or.inl (show (Sum.inl (M.tail s) : V ⊕ V) = Sum.inl (M.tail t) by
          rw [h1]))
      · simp at hH

end Pend

variable {M : CombMap D V F}

/-- **The explicit split functions with the rotation carried as a state meet `SplitFnsS`** (the
invariant `CInvS M Q`, the children's rotations `chRot M Q`, `κ = 9`, `s = 100000`, the small
pieces by `smD`), for choice functions `pc`, `sc` meeting their specifications. -/
theorem splitFnsS_R (hloop : ∀ d, M.head d ≠ M.tail d) {S T Q : Finset V} (hSTQ : S ∪ T ⊆ Q)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) (pc : PcChoice D V)
    (hpc : ∀ P Hs, pc.OK M Q P Hs) (sc : List (Finset V) → ℕ → ℕ → ScChoice M)
    (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W) :
    SplitFnsS M S T 9 100000 (CInvS M Q) (spSR M pc sc Q) (spHR M pc sc Q)
      (smD M pc.pick S T) (chRot M Q) :=
  ⟨fun P Hs hP hs ht b => smD_spec (by norm_num) (by norm_num) hloop
    (fun t ht => hQdeg t (hSTQ ht)) (hpc ∅ []).pick _ P Hs rfl hP hs ht b,
   fun P Hs _ hP hI hs ht => split_size_S hSTQ hloop hQdeg hQ5 hP hI hs ht pc (hpc P Hs) sc hsc,
   fun P Hs _ hP hI hs ht => split_hole_S hSTQ hloop hQdeg hQ5 hP hI hs ht pc (hpc P Hs) sc hsc⟩

end Gen

section Pre

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **`BalDecA` for the decomposition with the rotation as a state on the preprocessed map**,
started at the root rotation `rootRot`. -/
theorem decS_balDecA_pre (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (hl : ∀ d, M.head d ≠ M.tail d) {e₀ : V → D} (he₀ : ∀ v, M.tail (e₀ v) = v) {S T : Finset V}
    {spS spH : Finset _ → List (Finset _) → Perm _ → SplitAns (preMap hrot he₀)}
    {sm : Finset _ → List (Finset _) → ADec (preMap hrot he₀)}
    {chS : Finset _ → List (Finset _) → Perm _ → HSep (preMap hrot he₀) → Finset _ → Perm _}
    (hF : SplitFnsS (preMap hrot he₀) (preTerm S) (preTerm T) 9 100000
      (CInvS (preMap hrot he₀) (pendQ _)) spS spH sm chS) :
    BalDecA (preMap hrot he₀) (preTerm S) (preTerm T) 9 6 100000
      (decS (preMap hrot he₀) spS spH sm chS 100000 univ []
        (rootRot (preMap hrot he₀) (pendQ _)) true) := by
  have : Nonempty D := ⟨e₀ hM.nonempty.some⟩
  have hP := triMap_isPlane hM hrot hface
  have he := triE_tail (hrot := hrot) he₀
  exact decS_balDecA (CombMap.pendant_isPlane he hP)
    (CombMap.pendant_rotTrans he (triMap_rotTrans hrot))
    (CombMap.pendant_faceTrans he (triMap_faceTrans hrot)) hF
    (cinvS_pendant he hP (triMap_rotTrans hrot) (triMap_faceTrans hrot)
      fun d => (triMap_isTriangle hrot hl d).φ_three)

end Pre

section Loops

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **`BalDecA` for the decomposition with the rotation as a state on `lpreMap M`**, for every
map (the map without darts handled by `decS_balDecA_of_isEmpty`). -/
theorem decS_balDecA_lpre (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {S T : Finset V} {spS spH : Finset _ → List (Finset _) → Perm _ → SplitAns (lpreMap M)}
    {sm : Finset _ → List (Finset _) → ADec (lpreMap M)}
    {chS : Finset _ → List (Finset _) → Perm _ → HSep (lpreMap M) → Finset _ → Perm _}
    (hF : SplitFnsS (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 100000
      (CInvS (lpreMap M) (pendQ _)) spS spH sm chS) :
    BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000
      (decS (lpreMap M) spS spH sm chS 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true) := by
  by_cases hB : (nlDarts M).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hB
    exact decS_balDecA_pre (nlMap_isPlane hM hrot hface hx₀) nlMap_rotTrans nlMap_faceTrans
      nlMap_loopless nlE_tail hF
  · rw [not_nonempty_iff_eq_empty] at hB
    have hD0 : Fintype.card (SDart (nlDarts M)) = 0 := by rw [Fintype.card_coe, hB]; rfl
    have : IsEmpty (SDart (nlDarts M)) := Fintype.card_eq_zero_iff.1 hD0
    have hV0 : Fintype.card (SVert (nlRot M) (nlDarts M)) = 0 :=
      le_zero_iff.1 (hD0 ▸ Fintype.card_le_of_surjective (nlMap M).tail
        fun w => ⟨nlE M w, nlE_tail w⟩)
    have hF0 : Fintype.card ((nlMap M).toSep nlMap_rotTrans).Face = 0 :=
      le_zero_iff.1 (hD0 ▸ Fintype.card_le_of_surjective _
        ((nlMap M).toSep nlMap_rotTrans).face_surjective)
    have hS0 : Fintype.card (PlanarSeparator.StDart (SDart (nlDarts M))) = 0 := by
      rw [card_triMap_darts, hD0]
    have hP0 : Fintype.card (PlanarSeparator.StDart (SDart (nlDarts M)) ⊕
        ((SVert (nlRot M) (nlDarts M) ⊕ ((nlMap M).toSep nlMap_rotTrans).Face) × Bool)) = 0 := by
      simp only [Fintype.card_sum, Fintype.card_prod, hS0, hV0, hF0, zero_add, zero_mul]
    have : IsEmpty (PlanarSeparator.StDart (SDart (nlDarts M)) ⊕
        ((SVert (nlRot M) (nlDarts M) ⊕ ((nlMap M).toSep nlMap_rotTrans).Face) × Bool)) :=
      Fintype.card_eq_zero_iff.1 hP0
    exact decS_balDecA_of_isEmpty hF _

/-- `splitFnsS_R` on `lpreMap M`. -/
theorem splitFnsS_lpreR (S T : Finset V) (pc : PcChoice _ _)
    (hpc : ∀ P Hs, pc.OK (lpreMap M) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMap M)) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W) :
    SplitFnsS (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 100000
      (CInvS (lpreMap M) (pendQ _)) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) := by
  obtain ⟨h1, h2, h3⟩ := pendQ_hyps (hrot := nlMap_rotTrans) (nlE_tail (M := M)) (nlTerm M S)
    (nlTerm M T)
  exact splitFnsS_R (preMap_loopless nlMap_loopless nlE_tail) h1 h2 h3 pc hpc sc hsc

/-- **Maximum flow in plane graphs in `O(n log³ n)` with the rotation carried down the
recursion**: `maxflow_plane_cost_decDD` for `τ = decS (lpreMap M) (spSR …) (spHR …) (smD …)
(chRot …) 100000 univ [] (rootRot …) true` — the rotation of each core piece map is now the
explicit `chRot` of its parent's, from the explicit root rotation, not a parameter; the only
parameters are the choice functions `pc`, `sc` under their local specifications. Constants as in
`maxflow_plane_cost`. -/
theorem maxflow_plane_cost_decDD' (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) (pc : PcChoice _ _)
    (hpc : ∀ P Hs, pc.OK (lpreMap M) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMap M)) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W)
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀) :
    let τ := decS (lpreMap M) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) ∧
      runLCost (lpreMap M) c τ ≤
        (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) := by
  intro τ
  have hτ : BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ :=
    decS_balDecA_lpre hM hrot hface (splitFnsS_lpreR S T pc hpc sc hsc)
  obtain ⟨h1, h2⟩ := maxflow_cost_of hM hrot hface hu hST
    (planeOracles_spec _ fun X => frRef_spec X) hc hτ
  exact ⟨hτ, h1, h2.trans (cost_bound_le K K₀ _)⟩

end Loops

end BKMNW

end PlanarFlow
