module

public import PlanarFlow.Klein.LCTRep

/-!
# Updating a stored tree: `ADDPATH`

The update of the values of Klein's algorithm after a pivot adds `c` along the path of the
cotree between the two faces of the old parent dart `a` (`c · T.chi (face a) (face (rev a))`,
`PlanarFlow.Klein.pivotVal`). With the cotree `C` stored in the forest (`TRep`) and rooted at a
fixed face, this path is the difference of the two root paths, and the update is four additions
of the dynamic trees, on the two values of the two root paths.

* `mem_tpath_face`, `mem_tpath_edge`: the nodes of `tpath` (for node maps meeting `Nodes`).
* `pflow_par`, `pflow_rev_par`, `pflow_eq_zero`: the values of the unit flow along a path of the
  tree.
* `addBoth_trep`: **adding `c` to the first values and `-c` to the second values of the root path
  of the node of the face `p`** gives the representation of the same tree with the values of the
  darts `κ - c · pflow C p` (the values `β`, `β₂` of the nodes of the faces on the path shift by
  `c` and `-c`).
* `chi_sub`: the path of the cotree from `s` to `t` is the difference of the paths from a third
  face `r` (uniqueness of unit flows off the tree).
* `addPath_trep`: **`ADDPATH`**: the four additions at the faces of `a` and of its reverse give
  the values `κ + c · T.chi (face a) (face (rev a))` on all darts.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap STFlow DynTree

/-! ### Root paths in forests -/

lemma upPath_congr {n : ℕ} {Fo Fo' : Forest} :
    ∀ (fuel x : ℕ), (∀ u ∈ upPath Fo n fuel x, Fo'.par u = Fo.par u) →
      upPath Fo' n fuel x = upPath Fo n fuel x := by
  intro fuel
  induction fuel with
  | zero => intro x _; rfl
  | succ f ih =>
    intro x h
    simp only [upPath]
    split_ifs with hx
    · have hx' : x ∈ upPath Fo n (f + 1) x := by simp [upPath, hx]
      rw [h x hx', ih _ fun u hu => h u (by simp [upPath, hx, hu])]
    · rfl

lemma rootPath_congr {n : ℕ} {Fo Fo' : Forest} (hp : Fo'.par = Fo.par) (x : ℕ) :
    rootPath Fo' n x = rootPath Fo n x :=
  upPath_congr n x fun u _ => congrFun hp u

variable {D X Y : Type*} [Fintype D] [DecidableEq D] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]
variable {N : CombMap D X Y} {n : ℕ} {C : DTree N} {ιf : Y → ℕ} {ιe : D → ℕ}

/-! ### The nodes of a path -/

lemma mem_tpath (k : ℕ) (y : Y) (u : ℕ) :
    u ∈ tpath C ιf ιe k y ↔ (∃ i ≤ k, u = ιf (C.up^[i] y)) ∨
      ∃ i < k, u = ιe (C.par (C.up^[i] y)) := by
  induction k generalizing y with
  | zero => simp [tpath]
  | succ k ih =>
    simp only [tpath, List.mem_cons, ih]
    constructor
    · rintro (rfl | rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · exact Or.inl ⟨0, by omega, rfl⟩
      · exact Or.inr ⟨0, by omega, rfl⟩
      · exact Or.inl ⟨i + 1, by omega, by rw [Function.iterate_succ_apply]⟩
      · exact Or.inr ⟨i + 1, by omega, by rw [Function.iterate_succ_apply]⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · rcases i with _ | i
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl ⟨i, by omega, by rw [Function.iterate_succ_apply]⟩))
      · rcases i with _ | i
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr ⟨i, by omega, by rw [Function.iterate_succ_apply]⟩))

lemma mem_tpath_face (hN : Nodes n N ιf ιe) (k : ℕ) (y z : Y) :
    ιf z ∈ tpath C ιf ιe k y ↔ ∃ i ≤ k, C.up^[i] y = z := by
  rw [mem_tpath]
  constructor
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    · exact ⟨i, hi, (hN.f_inj h).symm⟩
    · exact absurd h (hN.fe _ _)
  · rintro ⟨i, hi, rfl⟩
    exact Or.inl ⟨i, hi, rfl⟩

lemma mem_tpath_edge (hN : Nodes n N ιf ιe) {k : ℕ} {y : Y} (hk : k ≤ C.depth y) {z : Y}
    (hz : z ≠ C.root) :
    ιe (C.par z) ∈ tpath C ιf ιe k y ↔ ∃ i < k, C.up^[i] y = z := by
  rw [mem_tpath]
  constructor
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    · exact absurd h.symm (hN.fe _ _)
    · exact ⟨i, hi, C.par_eq_or hz (C.iterate_ne_root (by omega))
        (hN.e_eq _ _ h)⟩
  · rintro ⟨i, hi, rfl⟩
    exact Or.inr ⟨i, hi, rfl⟩

/-! ### The unit flow along a path -/

lemma pflow_par (p : Y) {z : Y} (hz : z ≠ C.root) :
    pflow C p (C.par z) = if ∃ i < C.depth p, C.up^[i] p = z then 1 else 0 := by
  unfold pflow
  have hr : ∀ i < C.depth p, C.par z ≠ N.rev (C.par (C.up^[i] p)) := fun i hi h =>
    absurd (C.par_eq_or (C.iterate_ne_root hi) hz (Or.inr h)) (fun e => by
      subst e
      exact N.rev_ne _ h.symm)
  split_ifs with h
  · obtain ⟨i, hi, rfl⟩ := h
    rw [sum_eq_single i]
    · simp [hr i hi]
    · intro j hj hji
      have : C.par (C.up^[i] p) ≠ C.par (C.up^[j] p) := fun e =>
        hji (C.iterate_inj hi.le (mem_range.1 hj).le
          (C.par_eq_or (C.iterate_ne_root (mem_range.1 hj)) hz (Or.inl e))).symm
      simp [this, hr j (mem_range.1 hj)]
    · intro h; exact absurd (mem_range.2 hi) h
  · push Not at h
    refine sum_eq_zero fun i hi => ?_
    have : C.par z ≠ C.par (C.up^[i] p) := fun e =>
      h i (mem_range.1 hi) (C.par_eq_or hz (C.iterate_ne_root (mem_range.1 hi)) (Or.inl e.symm))
    simp [this, hr i (mem_range.1 hi)]

lemma pflow_rev_par (p : Y) {z : Y} (hz : z ≠ C.root) :
    pflow C p (N.rev (C.par z)) = - if ∃ i < C.depth p, C.up^[i] p = z then 1 else 0 := by
  have := pflow_antisymm C p (C.par z)
  change pflow C p (N.rev (C.par z)) = _ at this
  rw [this, pflow_par p hz]

lemma pflow_eq_zero (p : Y) {d : D} (hd : ∀ z, z ≠ C.root → d ≠ C.par z ∧ d ≠ N.rev (C.par z)) :
    pflow C p d = 0 := by
  unfold pflow
  refine sum_eq_zero fun i hi => ?_
  have h := hd _ (C.iterate_ne_root (mem_range.1 hi))
  simp [h.1, h.2]

/-! ### Adding along a root path -/

/-- **Adding `c` to the first values and `-c` to the second values of the root path** of the
node of the face `p`. -/
theorem addBoth_trep {κ : D → ℝ} {β β₂ : Y → ℝ} {Fo : Forest}
    (hR : TRep n Fo C ιf ιe κ β β₂) (hN : Nodes n N ιf ιe) (hn : 2 * Fintype.card Y ≤ n)
    (p : Y) (c : ℝ) :
    TRep n (addPath2 (addPath Fo n (ιf p) c) n (ιf p) (-c)) C ιf ιe
      (fun d => κ d - c * pflow C p d)
      (fun y => β y + if ∃ i ≤ C.depth p, C.up^[i] p = y then c else 0)
      (fun y => β₂ y - if ∃ i ≤ C.depth p, C.up^[i] p = y then c else 0) := by
  classical
  have hrp' : rootPath Fo n (ιf p) = tpath C ιf ιe (C.depth p) p :=
    rootPath_rep hR hN.f_lt hN.e_lt hn p
  have hrp : rootPath (addPath Fo n (ιf p) c) n (ιf p) = tpath C ιf ιe (C.depth p) p :=
    (rootPath_congr (Fo := Fo) (Fo' := addPath Fo n (ιf p) c) rfl _).trans hrp'
  refine ⟨hR.pf, hR.pr, hR.pe, fun y hy => ?_, fun y hy => ?_, fun y => ?_, fun y => ?_⟩
  · simp only [addPath2]
    simp only [addPath, hrp', mem_tpath_edge hN le_rfl hy, hR.ve y hy, pflow_rev_par p hy]
    split_ifs <;> push_cast <;> ring
  · simp only [addPath2]
    rw [hrp]
    simp only [addPath, mem_tpath_edge hN le_rfl hy, hR.ve2 y hy, pflow_par p hy]
    split_ifs <;> push_cast <;> ring
  · simp only [addPath2]
    simp only [addPath, hrp', mem_tpath_face hN, hR.vf y]
    split_ifs <;> ring
  · simp only [addPath2]
    rw [hrp]
    simp only [addPath, mem_tpath_face hN, hR.vf2 y]
    split_ifs <;> ring

/-! ### The path of the cotree between two faces -/

section Chi

variable {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-- **The path of the cotree from `s` to `t` is the difference of the paths from `r`.** -/
theorem chi_sub (hM : M.IsPlane) (T : DTree M.dual) (r s t : F) :
    T.chi s t = T.chi r t - T.chi r s := by
  obtain ⟨a1, d1, o1, -⟩ := T.chi_spec hM.dual s t
  obtain ⟨a2, d2, o2, -⟩ := T.chi_spec hM.dual r t
  obtain ⟨a3, d3, o3, -⟩ := T.chi_spec hM.dual r s
  funext d
  have hc : M.dual.IsCirc (T.chi s t - (T.chi r t - T.chi r s)) := by
    refine ⟨fun d => ?_, fun v => ?_⟩
    · simp only [Pi.sub_apply, a1 d, a2 d, a3 d]; ring
    · have e : ∀ f g : D → ℤ, M.dual.div (f - g) v = M.dual.div f v - M.dual.div g v :=
        fun f g => by unfold CombMap.div; rw [← sum_sub_distrib]; rfl
      rw [e, e, d1, d2, d3]; split_ifs <;> ring
  have := T.circ_eq_zero hM.dual hc (fun d hd => by simp [o1 d hd, o2 d hd, o3 d hd]) d
  simp only [Pi.sub_apply] at this
  simp only [Pi.sub_apply]
  linarith

/-- **`ADDPATH` on the stored cotree**: with the cotree `C` (its parent darts off `T`) stored in
the forest, adding `-c` and `c` along the root path of the face `p`, then `c` and `-c` along the
root path of the face `q`, gives the values `κ + c · T.chi p q` of the darts. -/
theorem addPath_trep (hM : M.IsPlane) {T : DTree M.dual} {C : DTree M}
    (hoff : ∀ y, y ≠ C.root → ¬ T.InT (C.par y)) {ιf : F → ℕ} {ιe : D → ℕ}
    (hN : Nodes n M ιf ιe) (hn : 2 * Fintype.card F ≤ n) {κ : D → ℝ} {β β₂ : F → ℝ}
    {Fo : Forest} (hR : TRep n Fo C ιf ιe κ β β₂) (p q : F) (c : ℝ) :
    ∃ β' β₂' : F → ℝ, TRep n
      (addPath2 (addPath (addPath2 (addPath Fo n (ιf p) c) n (ιf p) (-c)) n (ιf q) (-c)) n
        (ιf q) c) C ιf ιe (fun d => κ d + c * T.chi p q d) β' β₂' ∧
      (∀ y, β' y = β y + (if ∃ i ≤ C.depth p, C.up^[i] p = y then c else 0) -
        (if ∃ i ≤ C.depth q, C.up^[i] q = y then c else 0)) ∧
      ∀ y, β₂' y = β₂ y - (if ∃ i ≤ C.depth p, C.up^[i] p = y then c else 0) +
        (if ∃ i ≤ C.depth q, C.up^[i] q = y then c else 0) := by
  have h1 := addBoth_trep hR hN hn p c
  have h2 := addBoth_trep h1 hN hn q (-c)
  rw [neg_neg] at h2
  refine ⟨fun y => (β y + if ∃ i ≤ C.depth p, C.up^[i] p = y then c else 0) +
      if ∃ i ≤ C.depth q, C.up^[i] q = y then -c else 0,
    fun y => (β₂ y - if ∃ i ≤ C.depth p, C.up^[i] p = y then c else 0) -
      if ∃ i ≤ C.depth q, C.up^[i] q = y then -c else 0, ?_, ?_, ?_⟩
  · convert h2 using 2 with d
    rw [chi_sub hM T C.root p q, chi_eq_pflow hM T C hoff, chi_eq_pflow hM T C hoff,
      Pi.sub_apply]
    push_cast
    ring
  · intro y; beta_reduce; split_ifs <;> ring
  · intro y; beta_reduce; split_ifs <;> ring

end Chi

end Klein

end PlanarFlow
