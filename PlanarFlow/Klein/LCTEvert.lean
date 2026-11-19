module

public import PlanarFlow.Klein.LCTUpdate
public import PlanarFlow.DynTree.Evert

/-!
# Re-rooting a stored tree: `evert`

* `DTree.reroot`: **a tree re-rooted at `w`**: the parent darts of the faces on the path from `w`
  to the old root are reversed (the face `up^(i+1) w` gets the reverse of the parent dart of
  `up^i w`), the others are kept.
* `evert_trep`: **`evert` at the node of the face `w` stores the re-rooted tree** with the same
  values of the darts (the dart semantics: the two values of the nodes of the edges of the path
  are exchanged, and so are the values `β`, `β₂` of the nodes of the faces of the path).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap STFlow DynTree

variable {D X Y : Type*} [Fintype D] [DecidableEq D] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]
variable {N : CombMap D X Y} {n : ℕ} {C : DTree N} {ιf : Y → ℕ} {ιe : D → ℕ}

/-! ### Re-rooting a tree -/

/-- The face `x` is a strict ancestor of `w`: `x = up^(i+1) w` for some `i < depth w`. -/
def SAnc (C : DTree N) (w x : Y) : Prop := ∃ i < C.depth w, C.up^[i + 1] w = x

lemma sAnc_index {C : DTree N} {w : Y} {i j : ℕ} (hi : i < C.depth w) (hj : j < C.depth w)
    (h : C.up^[i + 1] w = C.up^[j + 1] w) : i = j := by
  have := C.iterate_inj (show i + 1 ≤ C.depth w by omega) (show j + 1 ≤ C.depth w by omega) h
  omega

open Classical in
/-- The parent darts of the tree re-rooted at `w`. -/
noncomputable def rerootPar (C : DTree N) (w x : Y) : D :=
  if h : SAnc C w x then N.rev (C.par (C.up^[Nat.find h] w)) else C.par x

lemma rerootPar_anc (C : DTree N) {w : Y} {i : ℕ} (hi : i < C.depth w) :
    rerootPar C w (C.up^[i + 1] w) = N.rev (C.par (C.up^[i] w)) := by
  classical
  have h : SAnc C w (C.up^[i + 1] w) := ⟨i, hi, rfl⟩
  unfold rerootPar
  rw [dite_eq_left h]
  have hs := Nat.find_spec h
  have : Nat.find h = i := sAnc_index hs.1 hi hs.2
  rw [this]

lemma rerootPar_not (C : DTree N) {w x : Y} (h : ¬ SAnc C w x) : rerootPar C w x = C.par x := by
  classical
  unfold rerootPar
  rw [dite_eq_right h]

lemma root_sAnc (C : DTree N) {w : Y} (hw : w ≠ C.root) : SAnc C w C.root := by
  have hd : 0 < C.depth w := by
    rcases Nat.eq_zero_or_pos (C.depth w) with h | h
    · have := C.iterate_depth w; rw [h] at this; exact absurd this hw
    · exact h
  exact ⟨C.depth w - 1, by omega, by rw [Nat.sub_add_cancel hd, C.iterate_depth]⟩

/-- **The tree re-rooted at `w`.** -/
noncomputable def _root_.PlanarFlow.STFlow.DTree.reroot (C : DTree N) (w : Y) : DTree N where
  root := w
  par := rerootPar C w
  head_par x hx := by
    by_cases h : SAnc C w x
    · obtain ⟨i, hi, rfl⟩ := h
      rw [rerootPar_anc C hi, N.rev_rev, Function.iterate_succ_apply',
        C.up_of_ne (C.iterate_ne_root hi)]
    · rw [rerootPar_not C h]
      refine C.head_par x fun hxr => h ?_
      rw [hxr]
      exact root_sAnc C (fun hw => hx (hxr.trans hw.symm))
  reach x := by
    -- the faces on the path from `w` to the root go down to `w`
    have hpath : ∀ j ≤ C.depth w, ∃ m, (upF N w (rerootPar C w))^[m] (C.up^[j] w) = w := by
      intro j
      induction j with
      | zero => intro _; exact ⟨0, rfl⟩
      | succ j ih =>
        intro hj
        obtain ⟨m, hm⟩ := ih (by omega)
        refine ⟨m + 1, ?_⟩
        rw [Function.iterate_succ_apply]
        have hne : C.up^[j + 1] w ≠ w := fun h => by
          have := C.iterate_inj hj (Nat.zero_le _) (h.trans rfl)
          omega
        have : upF N w (rerootPar C w) (C.up^[j + 1] w) = C.up^[j] w := by
          unfold upF
          rw [ite_eq_right hne, rerootPar_anc C (by omega), C.head_par _ (C.iterate_ne_root
            (by omega))]
        rw [this, hm]
    -- the other faces climb to the path
    have hother : ∀ k, ∀ x, C.depth x = k → ∃ m,
        (upF N w (rerootPar C w))^[m] x = w := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro x hk
        by_cases hx : ∃ j ≤ C.depth w, C.up^[j] w = x
        · obtain ⟨j, hj, rfl⟩ := hx
          exact hpath j hj
        · push Not at hx
          have hxw : x ≠ w := fun h => hx 0 (Nat.zero_le _) h.symm
          have hs : ¬ SAnc C w x := fun ⟨i, hi, h⟩ => hx (i + 1) (by omega) h
          have hxr : x ≠ C.root := fun h => hs (by
            rw [h]; exact root_sAnc C (fun hw => hx 0 (Nat.zero_le _) (by rw [h, hw]; rfl)))
          obtain ⟨m, hm⟩ := ih (C.depth (C.up x)) (by rw [← hk, C.depth_up hxr]; omega)
            (C.up x) rfl
          refine ⟨m + 1, ?_⟩
          rw [Function.iterate_succ_apply]
          have : upF N w (rerootPar C w) x = C.up x := by
            unfold upF
            rw [ite_eq_right hxw, rerootPar_not C hs, C.up_of_ne hxr]
          rw [this, hm]
    exact hother _ x rfl

lemma reroot_root (C : DTree N) (w : Y) : (C.reroot w).root = w := rfl

lemma reroot_par (C : DTree N) (w x : Y) : (C.reroot w).par x = rerootPar C w x := rfl

/-! ### `revPar` along a path -/

lemma tpath_cons_cons (k : ℕ) (y : Y) :
    tpath C ιf ιe (k + 1) y = ιf y :: ιe (C.par y) :: tpath C ιf ιe k (C.up y) := rfl

lemma tpath_head (k : ℕ) (y : Y) : ∃ L, tpath C ιf ιe k y = ιf y :: L := by
  cases k <;> exact ⟨_, rfl⟩

lemma revPar_tpath_self (k : ℕ) (y : Y) (q : ℕ) : revPar q (tpath C ιf ιe k y) (ιf y) = some q := by
  obtain ⟨L, hL⟩ := tpath_head (C := C) (ιe := ιe) k y
  rw [hL]
  simp [revPar]

lemma revPar_tpath_edge (hN : Nodes n N ιf ιe) :
    ∀ (k : ℕ) (y : Y), k ≤ C.depth y → ∀ i < k, ∀ q,
      revPar q (tpath C ιf ιe k y) (ιe (C.par (C.up^[i] y))) = some (ιf (C.up^[i] y)) := by
  intro k
  induction k with
  | zero => intro y _ i hi; omega
  | succ k ih =>
    intro y hk i hi q
    have hyr : y ≠ C.root := by intro h; rw [h, C.depth_root] at hk; omega
    rw [tpath_cons_cons]
    simp only [revPar]
    rw [ite_eq_right (Ne.symm (hN.fe _ _))]
    rcases i with _ | i
    · simp
    · have hne : ιe (C.par (C.up^[i + 1] y)) ≠ ιe (C.par y) := fun h => by
        have := C.par_eq_or hyr (C.iterate_ne_root (show i + 1 < C.depth y by omega))
          (hN.e_eq _ _ h.symm)
        have := C.iterate_inj (show i + 1 ≤ C.depth y by omega) (Nat.zero_le _) this
        omega
      rw [ite_eq_right hne]
      obtain ⟨L, hL⟩ := tpath_head (C := C) (ιe := ιe) (ιf := ιf) k (C.up y)
      have := ih (C.up y) (by rw [C.depth_up hyr] at hk; omega) i (by omega) (ιe (C.par y))
      rw [hL] at this ⊢
      simp only [revPar] at this ⊢
      rw [← Function.iterate_succ_apply] at this
      exact this

lemma revPar_tpath_face (hN : Nodes n N ιf ιe) :
    ∀ (k : ℕ) (y : Y), k ≤ C.depth y → ∀ i < k, ∀ q,
      revPar q (tpath C ιf ιe k y) (ιf (C.up^[i + 1] y)) = some (ιe (C.par (C.up^[i] y))) := by
  intro k
  induction k with
  | zero => intro y _ i hi; omega
  | succ k ih =>
    intro y hk i hi q
    have hyr : y ≠ C.root := by intro h; rw [h, C.depth_root] at hk; omega
    rw [tpath_cons_cons]
    simp only [revPar]
    have hne : ιf (C.up^[i + 1] y) ≠ ιf y := fun h => by
      have := C.iterate_inj (show i + 1 ≤ C.depth y by omega) (Nat.zero_le _) (hN.f_inj h)
      omega
    rw [ite_eq_right hne, ite_eq_right (hN.fe _ _)]
    rcases i with _ | i
    · obtain ⟨L, hL⟩ := tpath_head (C := C) (ιe := ιe) (ιf := ιf) k (C.up y)
      rw [hL]
      simp [revPar]
    · have := ih (C.up y) (by rw [C.depth_up hyr] at hk; omega) i (by omega) (ιe (C.par y))
      rw [← Function.iterate_succ_apply, ← Function.iterate_succ_apply] at this
      obtain ⟨L, hL⟩ := tpath_head (C := C) (ιe := ιe) (ιf := ιf) k (C.up y)
      rw [hL] at this ⊢
      simp only [revPar] at this ⊢
      exact this

/-! ### Evert -/

/-- **`evert` at the node of the face `w` stores the tree re-rooted at `w`**, with the same values
of the darts; the values of the nodes of the faces on the path are exchanged. -/
theorem evert_trep {κ : D → ℝ} {β β₂ : Y → ℝ} {Fo : Forest}
    (hR : TRep n Fo C ιf ιe κ β β₂) (hN : Nodes n N ιf ιe) (hn : 2 * Fintype.card Y ≤ n)
    (w : Y) :
    TRep n (evert Fo n (ιf w)) (C.reroot w) ιf ιe κ
      (fun y => if ∃ j ≤ C.depth w, C.up^[j] w = y then β₂ y else β y)
      (fun y => if ∃ j ≤ C.depth w, C.up^[j] w = y then β y else β₂ y) := by
  classical
  have hrp : rootPath Fo n (ιf w) = tpath C ιf ιe (C.depth w) w :=
    rootPath_rep hR hN.f_lt hN.e_lt hn w
  -- the faces off the path keep their parent dart
  have hoff : ∀ x, x ≠ w → ¬ SAnc C w x → ¬ ∃ j ≤ C.depth w, C.up^[j] w = x := by
    rintro x hxw hs ⟨j, hj, rfl⟩
    rcases j with _ | j
    · exact hxw rfl
    · exact hs ⟨j, by omega, rfl⟩
  have hxr : ∀ x, x ≠ w → ¬ SAnc C w x → x ≠ C.root := fun x hxw hs h =>
    hs (h ▸ root_sAnc C (fun hw => hxw (h.trans hw.symm)))
  have hedge_off : ∀ x, x ≠ w → ¬ SAnc C w x → ιe (C.par x) ∉ tpath C ιf ιe (C.depth w) w := by
    intro x hxw hs hm
    rw [mem_tpath_edge hN le_rfl (hxr x hxw hs)] at hm
    obtain ⟨i, hi, h⟩ := hm
    exact hoff x hxw hs ⟨i, hi.le, h⟩
  refine ⟨fun x hx => ?_, ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun y => ?_,
    fun y => ?_⟩
  · -- the parent of the node of a face
    change (revPar n (rootPath Fo n (ιf w)) (ιf x)).getD (Fo.par (ιf x)) = ιe (rerootPar C w x)
    rw [hrp]
    by_cases hs : SAnc C w x
    · obtain ⟨i, hi, rfl⟩ := hs
      rw [revPar_tpath_face hN _ w le_rfl i hi, rerootPar_anc C hi, hN.e_rev]
      rfl
    · rw [revPar_of_not_mem (by rw [mem_tpath_face hN]; exact hoff x hx hs), rerootPar_not C hs]
      exact hR.pf x (hxr x hx hs)
  · change (revPar n (rootPath Fo n (ιf w)) (ιf w)).getD (Fo.par (ιf w)) = n
    rw [hrp, revPar_tpath_self]
    rfl
  · change (revPar n (rootPath Fo n (ιf w)) (ιe (rerootPar C w x))).getD
      (Fo.par (ιe (rerootPar C w x))) = ιf (N.face (rerootPar C w x))
    rw [hrp]
    by_cases hs : SAnc C w x
    · obtain ⟨i, hi, rfl⟩ := hs
      rw [rerootPar_anc C hi, hN.e_rev, revPar_tpath_edge hN _ w le_rfl i hi,
        C.head_par _ (C.iterate_ne_root hi)]
      rfl
    · rw [rerootPar_not C hs, revPar_of_not_mem (hedge_off x hx hs)]
      exact hR.pe x (hxr x hx hs)
  · change (if ιe (rerootPar C w x) ∈ rootPath Fo n (ιf w) then Fo.val2 (ιe (rerootPar C w x))
      else Fo.val (ιe (rerootPar C w x))) = κ (N.rev (rerootPar C w x))
    rw [hrp]
    by_cases hs : SAnc C w x
    · obtain ⟨i, hi, rfl⟩ := hs
      rw [rerootPar_anc C hi, hN.e_rev, ite_eq_left ((mem_tpath_edge hN le_rfl
        (C.iterate_ne_root hi)).2 ⟨i, hi, rfl⟩), hR.ve2 _ (C.iterate_ne_root hi), N.rev_rev]
    · rw [rerootPar_not C hs, ite_eq_right (hedge_off x hx hs)]
      exact hR.ve x (hxr x hx hs)
  · change (if ιe (rerootPar C w x) ∈ rootPath Fo n (ιf w) then Fo.val (ιe (rerootPar C w x))
      else Fo.val2 (ιe (rerootPar C w x))) = κ (rerootPar C w x)
    rw [hrp]
    by_cases hs : SAnc C w x
    · obtain ⟨i, hi, rfl⟩ := hs
      rw [rerootPar_anc C hi, hN.e_rev, ite_eq_left ((mem_tpath_edge hN le_rfl
        (C.iterate_ne_root hi)).2 ⟨i, hi, rfl⟩), hR.ve _ (C.iterate_ne_root hi)]
    · rw [rerootPar_not C hs, ite_eq_right (hedge_off x hx hs)]
      exact hR.ve2 x (hxr x hx hs)
  · change (if ιf y ∈ rootPath Fo n (ιf w) then Fo.val2 (ιf y) else Fo.val (ιf y)) = _
    simp only [hrp, mem_tpath_face hN, hR.vf2, hR.vf]
  · change (if ιf y ∈ rootPath Fo n (ιf w) then Fo.val (ιf y) else Fo.val2 (ιf y)) = _
    simp only [hrp, mem_tpath_face hN, hR.vf2, hR.vf]

end Klein

end PlanarFlow
