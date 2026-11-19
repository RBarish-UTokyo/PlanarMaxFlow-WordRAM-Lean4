module

public import PlanarFlow.STFlow.ProgLoop

/-!
# Reading the flow from the stored state

At the end of the run the forest stores the dual tree `T*` with the perturbed lengths and the
cotree with the keys; the flow `g` is not stored. It is recovered as follows (all three facts are
consequences of the invariant `LInv`):

* `lfinal_g`: **the flow is `g = λ χ + cob (psum c)`**, `χ` the path of the cotree, where the
  value `λ = c e - cob (psum c) e` is read at any saturated dart `e` of the path, such as the last
  bottleneck;
* `conv_trep`: changing the values of the edges of a stored tree (Klein's `pointOps` for every
  face but the root) stores the tree with new values: `T*` with the capacities, whose path sums
  are `psum c`;
* `chi_read`: **the path of the cotree is read from the second values** of the nodes of the
  edges: adding `1` to the second values of the root path of the node of `t` changes the second
  value of the node of the edge of a dart `d` by `|χ d|`, and the parent of that node gives the
  sign.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW Klein DynTree

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-! ### The flow from the tree and its value -/

section Flow

variable {M : CombMap D V F} {c ε : D → ℤ} {s t : V}

/-- **The flow of a state**, from the value read at a saturated dart `e` of the path. -/
theorem lfinal_g (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M} (hI : LInv c ε s t st) {e : D}
    (he : st.T.chi s t e = 1) (hsat : st.g e = c e) (d : D) :
    st.g d = (c e - M.cob (st.T.psum c) e) * st.T.chi s t d + M.cob (st.T.psum c) d := by
  have h1 := linv_g hM hst hI d
  have h2 := linv_g hM hst hI e
  rw [he, hsat] at h2
  rw [h1]
  have : M.div st.g s = c e - M.cob (st.T.psum c) e := by linarith
  rw [this]

end Flow

/-! ### Changing the values of a stored tree -/

section Conv

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
variable {N : CombMap D X Y} {n : ℕ} {C : DTree N} {ιf : Y → ℕ} {ιe : D → ℕ}

/-- The operations changing the values `κ₀` of the edges of the parent darts of the faces `ys`
to `κ'`. -/
def convOps (ιf : Y → ℕ) (ιe : D → ℕ) (C : DTree N) (κ₀ κ' : D → ℤ) (ys : List Y) :
    List EOp :=
  ys.flatMap fun y => pointOps ιf ιe C y (κ' (N.rev (C.par y)) - κ₀ (N.rev (C.par y)))
    (κ' (C.par y) - κ₀ (C.par y))

lemma convOps_congr {κ₀ κ₁ κ' : D → ℤ} {ys : List Y}
    (h : ∀ y ∈ ys, κ₁ (C.par y) = κ₀ (C.par y) ∧ κ₁ (N.rev (C.par y)) = κ₀ (N.rev (C.par y))) :
    convOps ιf ιe C κ₁ κ' ys = convOps ιf ιe C κ₀ κ' ys :=
  List.flatMap_congr fun y hy => by rw [(h y hy).1, (h y hy).2]

open Classical in
/-- **Changing the values of the edges of the parent darts of distinct faces** other than the
root: valid, printing nothing, storing the tree with the values `κ'` on those edges, and changing
nothing but the nodes of those edges. -/
theorem conv_trep {β β₂ : Y → ℝ} (hN : Nodes n N ιf ιe) (hn : 2 * Fintype.card Y ≤ n)
    (κ' : D → ℤ) : ∀ (ys : List Y) {κ₀ : D → ℤ} {Fo : Forest},
    TRep n Fo C ιf ιe (fun d => (κ₀ d : ℝ)) β β₂ → ys.Nodup → (∀ y ∈ ys, y ≠ C.root) →
    ValidOpsE n Fo (convOps ιf ιe C κ₀ κ' ys) ∧ (runOpsE n Fo (convOps ιf ιe C κ₀ κ' ys)).2 = [] ∧
      TRep n (runOpsE n Fo (convOps ιf ιe C κ₀ κ' ys)).1 C ιf ιe
        (fun d => ((if ∃ y ∈ ys, d = C.par y ∨ d = N.rev (C.par y) then κ' d else κ₀ d : ℤ) :
          ℝ)) β β₂ ∧
      (runOpsE n Fo (convOps ιf ιe C κ₀ κ' ys)).1.par = Fo.par ∧
      ∀ u, (∀ d, u ≠ ιe d) → Agree Fo (runOpsE n Fo (convOps ιf ιe C κ₀ κ' ys)).1 u
  | [], κ₀, Fo, hR, _, _ => by
    refine ⟨trivial, rfl, ?_, rfl, fun u _ => ⟨rfl, rfl, rfl⟩⟩
    simpa [convOps, runOpsE] using hR
  | y :: ys, κ₀, Fo, hR, hnd, hyr => by
    have hy := hyr y (by simp)
    obtain ⟨hv₁, ho₁, hR₁, hp₁, hag₁⟩ := point_trep hR hN hn hy
      (κ' (N.rev (C.par y)) - κ₀ (N.rev (C.par y))) (κ' (C.par y) - κ₀ (C.par y))
    set κ₁ : D → ℤ := fun d => if d = C.par y ∨ d = N.rev (C.par y) then κ' d else κ₀ d
      with hκ₁
    have hne : C.par y ≠ N.rev (C.par y) := (N.rev_ne _).symm
    have hR₁' : TRep n (runOpsE n Fo (pointOps ιf ιe C y
        (κ' (N.rev (C.par y)) - κ₀ (N.rev (C.par y))) (κ' (C.par y) - κ₀ (C.par y)))).1 C ιf ιe
        (fun d => (κ₁ d : ℝ)) β β₂ := hR₁.congrκ fun d => by
      simp only [hκ₁]
      by_cases h1 : d = C.par y
      · subst h1; simp [hne]
      · by_cases h2 : d = N.rev (C.par y)
        · subst h2; simp [h1]
        · simp [h1, h2]
    have hys : ∀ y' ∈ ys, κ₁ (C.par y') = κ₀ (C.par y') ∧
        κ₁ (N.rev (C.par y')) = κ₀ (N.rev (C.par y')) := by
      intro y' hy'
      have hy'y : y' ≠ y := fun h => (List.nodup_cons.1 hnd).1 (h ▸ hy')
      have hy'r := hyr y' (by simp [hy'])
      have a1 : ¬ (C.par y' = C.par y ∨ C.par y' = N.rev (C.par y)) := fun h =>
        hy'y (C.par_eq_or hy hy'r h)
      have a2 : ¬ (N.rev (C.par y') = C.par y ∨ N.rev (C.par y') = N.rev (C.par y)) := by
        rintro (h | h)
        · exact a1 (Or.inr (by rw [← h, N.rev_rev]))
        · exact a1 (Or.inl (N.rev_injective h))
      refine ⟨?_, ?_⟩ <;> simp [hκ₁, a1, a2]
    obtain ⟨hv₂, ho₂, hR₂, hp₂, hag₂⟩ := conv_trep hN hn κ' ys hR₁' (List.nodup_cons.1 hnd).2
      (fun y' hy' => hyr y' (by simp [hy']))
    rw [convOps_congr hys] at hv₂ ho₂ hR₂ hp₂ hag₂
    have hsplit : convOps ιf ιe C κ₀ κ' (y :: ys) = pointOps ιf ιe C y
        (κ' (N.rev (C.par y)) - κ₀ (N.rev (C.par y))) (κ' (C.par y) - κ₀ (C.par y)) ++
          convOps ιf ιe C κ₀ κ' ys := by simp [convOps]
    rw [hsplit, runOpsE_append]
    refine ⟨(validOpsE_append n _ _ _).2 ⟨hv₁, hv₂⟩, by rw [ho₁, ho₂]; rfl,
      hR₂.congrκ fun d => ?_, hp₂.trans hp₁, fun u hu => (hag₁ u (hu _)).trans (hag₂ u hu)⟩
    simp only [hκ₁, List.mem_cons, exists_eq_or_imp]
    by_cases h : d = C.par y ∨ d = N.rev (C.par y)
    · simp [h]
    · simp [h]

/-- A stored tree whose values agree on its edges with `κ'` stores it with `κ'`. -/
lemma trep_congr_edges {κ κ' : D → ℝ} {β β₂ : Y → ℝ} {Fo : Forest}
    (hR : TRep n Fo C ιf ιe κ β β₂)
    (h : ∀ y, y ≠ C.root →
      κ (C.par y) = κ' (C.par y) ∧ κ (N.rev (C.par y)) = κ' (N.rev (C.par y))) :
    TRep n Fo C ιf ιe κ' β β₂ :=
  ⟨hR.pf, hR.pr, hR.pe, fun y hy => (hR.ve y hy).trans (h y hy).2,
    fun y hy => (hR.ve2 y hy).trans (h y hy).1, hR.vf, hR.vf2⟩

end Conv

/-! ### Reading the path of the cotree -/

section Read

variable {M : CombMap D V F} {n : ℕ} {ιF : F → ℕ} {ιG : D → ℕ} {ιV : V → ℕ} {ιE : D → ℕ}

/-- **The path of the cotree from the second values**: adding `1` to the second values of the
root path of the node of `t` changes the second value of the node of the edge of `d` by `|χ d|`;
the sign of `χ d` is `+` when the parent of that node is the node of the tail of `d`. -/
theorem chi_read (hM : M.IsPlane) (hL : Layout M.dual n ιF ιG ιV ιE) {φ : D → ℤ} {s : V}
    {Lo : ℝ} {Fo : Forest} {T : DTree M} {κ : D → ℤ}
    (hS : Stored M.dual n ιF ιG ιV ιE φ s Lo Fo (toDD T) κ) (t : V) (d : D) :
    ((T.chi s t d : ℤ) : ℝ) = (if Fo.par (ιE d) = ιV (M.tail d) then 1 else -1) *
      ((runOpsE n Fo [.add2 (ιV t) 1]).1.val2 (ιE d) - Fo.val2 (ιE d)) := by
  classical
  obtain ⟨C, β, β₂, hroot, hoff, hR, hI, -⟩ := hS.cot
  have hN := hL.dual
  have hrun : (runOpsE n Fo [.add2 (ιV t) 1]).1 = addPath2 Fo n (ιV t) 1 := by
    simp [runOpsE, EOp.apply]
  have hrp := rootPath_rep hR hN.f_lt hN.e_lt hL.hf t
  have hdiff : (runOpsE n Fo [.add2 (ιV t) 1]).1.val2 (ιE d) - Fo.val2 (ιE d) =
      if ιE d ∈ tpath C ιV ιE (C.depth t) t then 1 else 0 := by
    rw [hrun]; simp only [addPath2, hrp]; split_ifs <;> ring
  have hchi : (toDD T).chi C.root t = pflow C t := chi_eq_pflow hM.dual (toDD T) C hoff t
  rw [hroot] at hchi
  have hchi' : T.chi s t d = pflow C t d := congrFun hchi d
  rw [hdiff, hchi']
  by_cases h1 : ∃ z, z ≠ C.root ∧ d = C.par z
  · obtain ⟨z, hz, rfl⟩ := h1
    have hp : Fo.par (ιE (C.par z)) = ιV (M.tail (C.par z)) := hR.pe z hz
    rw [ite_eq_left hp, pflow_par t hz]
    by_cases hm : ∃ i < C.depth t, C.up^[i] t = z
    · rw [ite_eq_left hm, ite_eq_left ((mem_tpath_edge hN le_rfl hz).2 hm)]; simp
    · rw [ite_eq_right hm, ite_eq_right (fun h => hm ((mem_tpath_edge hN le_rfl hz).1 h))]
      simp
  · push Not at h1
    by_cases h2 : ∃ z, z ≠ C.root ∧ d = M.rev (C.par z)
    · obtain ⟨z, hz, rfl⟩ := h2
      have hp : Fo.par (ιE (M.rev (C.par z))) = ιV (M.tail (C.par z)) := by
        rw [show M.rev (C.par z) = M.dual.rev (C.par z) from rfl, hN.e_rev]; exact hR.pe z hz
      have hne : ιV (M.tail (C.par z)) ≠ ιV (M.tail (M.rev (C.par z))) := by
        intro h
        have h' := hN.f_inj h
        have hh := C.head_par z hz
        have hup : C.up z = z := by
          rw [C.up_of_ne hz]; exact h'.trans hh
        have hdep := C.depth_up hz
        rw [hup] at hdep
        omega
      have hmem : ιE (M.rev (C.par z)) ∈ tpath C ιV ιE (C.depth t) t ↔
          ιE (C.par z) ∈ tpath C ιV ιE (C.depth t) t := by
        rw [show M.rev (C.par z) = M.dual.rev (C.par z) from rfl, hN.e_rev]
      rw [ite_eq_right (by rw [hp]; exact hne),
        show M.rev (C.par z) = M.dual.rev (C.par z) from rfl,
        pflow_rev_par t hz, hN.e_rev]
      by_cases hm : ∃ i < C.depth t, C.up^[i] t = z
      · rw [ite_eq_left hm, ite_eq_left ((mem_tpath_edge hN le_rfl hz).2 hm)]; simp
      · rw [ite_eq_right hm, ite_eq_right (fun h => hm ((mem_tpath_edge hN le_rfl hz).1 h))]
        simp
    · push Not at h2
      have hoffd : ∀ z, z ≠ C.root → d ≠ C.par z ∧ d ≠ M.dual.rev (C.par z) :=
        fun z hz => ⟨h1 z hz, h2 z hz⟩
      have hnot : ιE d ∉ tpath C ιV ιE (C.depth t) t := fun h => by
        rcases mem_tpath_cases h with ⟨x, hx⟩ | ⟨i, hi, hx⟩
        · exact hN.fe _ _ hx.symm
        · rcases hN.e_eq _ _ hx with h | h
          · exact h1 _ (C.iterate_ne_root hi) h.symm
          · exact h2 _ (C.iterate_ne_root hi) (by rw [h]; exact (M.rev_rev d).symm)
      rw [pflow_eq_zero t hoffd, ite_eq_right hnot]
      simp

end Read

end STFlow

end PlanarFlow
