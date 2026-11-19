module

public import PlanarFlow.BKMNW.CycleSink

/-!
# FixConservationOnPath only sees the faces of the path's darts; the pendant choice is harmless

`c2sImpl` (CycleToSingleSinkLimitedMaxFlow, `PlanarFlow/BKMNW/CycleSink.lean`) runs
FixConservationOnPath with frozen vertices (`fixFrozen`) on the map with pendant edges
`M.pendant e he`, for the **classically chosen** dart `e v = (he v).choose` at every vertex. A
machine program cannot reproduce a classical choice; this file shows that it does not need to:

* **`fpStep_congr`**, **`fixPath_congr`**: two maps with the same reverse and tails, and two simple
  paths with the same darts and vertices, the faces of the two maps agreeing on the darts of the
  path: one stage of FixConservationOnPath, and its whole result at every dart `x` with the faces
  of `x` and `rev x` agreeing, are the same (the run only reads the faces of the path's darts);
* **`fixFrozen_indep`**: `fixFrozen` does not depend on the choice of the darts `e` at which the
  pendant edges are attached;
* **`c2sImpl_eq`**: `c2sImpl` is the same expression with **any** dart `e v` at each vertex `v`
  (e.g. the one of least index chosen by a machine program); `s2cImpl` is built from it.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap SPath

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

section Congr

variable {M₁ M₂ : CombMap D V F} {P₁ : SPath M₁} {P₂ : SPath M₂}

/-- Two simple paths with the same darts and vertices on maps with the same reverse. -/
structure PathAgree (P₁ : SPath M₁) (P₂ : SPath M₂) : Prop where
  rev : M₁.rev = M₂.rev
  tail : M₁.tail = M₂.tail
  k : P₁.k = P₂.k
  d : P₁.d = P₂.d
  p : P₁.p = P₂.p
  face : ∀ e ∈ P₁.darts, M₁.face e = M₂.face e

lemma PathAgree.darts_eq (h : PathAgree P₁ P₂) : P₁.darts = P₂.darts := by
  unfold SPath.darts; rw [h.k, h.d, h.rev]

lemma PathAgree.face₂ (h : PathAgree P₁ P₂) {e : D} (he : e ∈ P₁.darts) :
    M₁.face (M₁.rev e) = M₂.face (M₂.rev e) := by
  rw [← h.rev]; exact h.face _ (P₁.rev_mem_darts he)

lemma PathAgree.faces_eq (h : PathAgree P₁ P₂) : P₁.faces = P₂.faces := by
  unfold SPath.faces
  rw [← h.darts_eq]
  congr 1
  exact List.map_congr_left fun e he => h.face e he

lemma PathAgree.cap_eq (h : PathAgree P₁ P₂) (c : D → ℤ) (Mb : ℤ) (i : ℕ) :
    P₁.cap c Mb i = P₂.cap c Mb i := by
  funext e
  unfold SPath.cap SPath.Boost
  rw [h.k, h.d, h.rev]

lemma PathAgree.div_eq (h : PathAgree P₁ P₂) : M₁.div = M₂.div := by
  funext f v; unfold CombMap.div; rw [h.tail]

lemma PathAgree.setPair_eq (h : PathAgree P₁ P₂) : BKMNW.setPair M₁ = BKMNW.setPair M₂ := by
  funext g e a; unfold BKMNW.setPair; rw [h.rev]

lemma PathAgree.arcs_eq (h : PathAgree P₁ P₂) (L : D → ℤ) :
    explicitArcs (M₁.dualGraph L) P₁.darts = explicitArcs (M₂.dualGraph L) P₂.darts := by
  rw [← h.darts_eq]
  unfold explicitArcs
  refine List.map_congr_left fun e he => ?_
  simp only [dualGraph]
  rw [h.face e he, h.face₂ he]

/-- **One stage of FixConservationOnPath only reads the faces of the path's darts.** -/
theorem fpStep_congr (h : PathAgree P₁ P₂) (c : D → ℤ) (Dst : DDG F) (fr : FRFun F) {i : ℕ}
    (hi : i < P₁.k) (s : (D → ℤ) × (F → ℤ)) :
    fpStep M₁ c P₁ Dst fr i s = fpStep M₂ c P₂ Dst fr i s := by
  have hd : P₁.d i ∈ P₁.darts := P₁.d_mem i hi
  have hdr : M₁.rev (P₁.d i) ∈ P₁.darts := P₁.rev_mem_darts hd
  have fa : M₁.face (P₂.d i) = M₂.face (P₂.d i) := by rw [← h.d]; exact h.face _ hd
  have fb : M₁.face (M₂.rev (P₂.d i)) = M₂.face (M₂.rev (P₂.d i)) := by
    rw [← h.d, ← h.rev]; exact h.face _ hdr
  have ca : ∀ φ : F → ℤ, M₁.cob φ (P₂.d i) = M₂.cob φ (P₂.d i) := fun φ => by
    unfold CombMap.cob; rw [h.rev, fa, fb]
  have cb : ∀ φ : F → ℤ, M₁.cob φ (M₂.rev (P₂.d i)) = M₂.cob φ (M₂.rev (P₂.d i)) := fun φ => by
    unfold CombMap.cob; rw [h.rev, M₂.rev_rev, fa, fb]
  have sp := h.setPair_eq
  have dv := h.div_eq
  have ar := h.arcs_eq
  have cp := h.cap_eq
  have fs := h.faces_eq
  have hrev := h.rev
  have hdd := h.d
  have hpp := h.p
  unfold fpStep
  simp only [sp, dv, ar, cp, fs, hdd, hpp, hrev, apply_ite (M₁.cob s.2), apply_ite M₁.face,
    apply_ite (M₂.cob s.2), apply_ite M₂.face,
    apply_ite M₂.rev, ca, cb, fa, fb, M₂.rev_rev]

/-- **FixConservationOnPath only reads the faces of the path's darts**: at every dart `x` with the
faces of `x` and `rev x` agreeing, the two runs agree. -/
theorem fixPath_congr (h : PathAgree P₁ P₂) (c f₀ : D → ℤ)
    (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F)
    (negSSSP : (D → ℤ) → Option (F → ℤ)) {x : D} (hx : M₁.face x = M₂.face x)
    (hxr : M₁.face (M₁.rev x) = M₂.face (M₂.rev x)) :
    fixPath M₁ c f₀ P₁ mssp fr negSSSP x = fixPath M₂ c f₀ P₂ mssp fr negSSSP x := by
  have hfold : ∀ (n : ℕ), n ≤ P₁.k → ∀ s : (D → ℤ) × (F → ℤ),
      (List.range n).foldl (fun s i => fpStep M₁ c P₁ ⟨P₁.faces, mssp P₁.darts (c - f₀)⟩ fr i s) s =
      (List.range n).foldl (fun s i => fpStep M₂ c P₂ ⟨P₂.faces, mssp P₂.darts (c - f₀)⟩ fr i s)
        s := by
    intro n
    induction n with
    | zero => intro _ s; rfl
    | succ n ih =>
      intro hn s
      rw [List.range_succ, List.foldl_append, List.foldl_append, ih (by omega) s]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [fpStep_congr h c _ fr (by omega), h.faces_eq, h.darts_eq]
  unfold fixPath
  rw [hfold P₁.k le_rfl, h.k]
  rcases negSSSP (c - (List.foldl (fun s i => fpStep M₂ c P₂
    ⟨P₂.faces, mssp P₂.darts (c - f₀)⟩ fr i s) (f₀, 0) (List.range P₂.k)).1) with _ | χ
  · rfl
  · simp only [Pi.add_apply, CombMap.cob, hx, hxr]

end Congr

section Pendant

variable {M : CombMap D V F}

/-- The lifts of a simple path to the maps with pendant edges at two choices agree. -/
lemma pathAgree_lift {e e' : V → D} (he : ∀ v, M.tail (e v) = v) (he' : ∀ v, M.tail (e' v) = v)
    (π : SPath M) : PathAgree (π.lift e he) (π.lift e' he') where
  rev := rfl
  tail := rfl
  k := rfl
  d := rfl
  p := rfl
  face x hx := by
    rw [SPath.lift_darts] at hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    rfl

/-- **`fixFrozen` does not depend on the darts at which the pendant edges are attached.** -/
theorem fixFrozen_indep {e e' : V → D} (he : ∀ v, M.tail (e v) = v)
    (he' : ∀ v, M.tail (e' v) = v) (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F)
    (neg : (D → ℤ) → Option (F → ℤ)) (U f₁ : D → ℤ) (π : SPath M) (Del : Finset V) :
    fixFrozen M e he mssp fr neg U f₁ π Del = fixFrozen M e' he' mssp fr neg U f₁ π Del := by
  funext d
  unfold fixFrozen
  split_ifs
  · rfl
  · exact fixPath_congr (pathAgree_lift he he' π) _ _ _ _ _ rfl rfl

/-- **`c2sImpl` with any dart at each vertex**: the classical choice in `c2sImpl` can be replaced
by any choice `e` of a dart at every vertex. -/
theorem c2sImpl_eq (e : V → D) (he : ∀ v, M.tail (e v) = v)
    (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F)
    (neg : (D → ℤ) → Option (F → ℤ)) (stflow : (D → ℤ) → Finset V → Finset V → D → ℤ)
    (U f : D → ℤ) (π : SPath M) (H : Finset V) :
    c2sImpl M mssp fr neg stflow U f π H =
      f + pushFwd M fr (c2sBeta M U f π.verts) ∅
        (fixFrozen M e he mssp fr neg U (f + stflow (c2sCap M U f π.verts) π.verts H) π
          (delSet M U f π.verts) - f) := by
  have hall : ∀ v, ∃ d, M.tail d = v := fun v => ⟨e v, he v⟩
  unfold c2sImpl
  simp only [hall, implies_true, ↓reduceDIte]
  rw [fixFrozen_indep (fun v => (hall v).choose_spec) he]

end Pendant

end BKMNW

end PlanarFlow
