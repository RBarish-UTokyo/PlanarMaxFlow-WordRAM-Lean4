module

public import PlanarFlow.STFlow.TreePath

/-!
# The perturbed shortest-path tree is unique

The perturbed run (`PlanarFlow/STFlow/Lex.lean`) starts from the state chosen by `linit`: a
spanning tree of the dual, rooted at a given face, which is a shortest-path tree for the
lexicographic lengths `(c, ε)`, with the coboundaries of its path sums as the flows. With the
perturbation `ε = lexEps D F` (`ε d = (4 F + 5) ^ (index of d)`) any two simple dual paths have
distinct perturbed lengths (Cabello, Chambers and Erickson, Section 6.2), so this tree is unique:
the initial tree can be computed by any correct procedure and handed to the machine program.

* `DTree.LexFeas T c ε`: **the tree is a shortest-path tree for `(c, ε)`**, stated on its
  potentials: for every dart `d`, `cob (psum c) d ≤ c d`, and `cob (psum ε) d ≤ ε d` when the
  first is an equality. This is a finite list of integer inequalities on the darts: a checkable
  condition on a given tree.
* `DTree.LexFeas.le_walk`: for a lexicographically feasible tree, the path of the tree to `x` is
  lexicographically shortest among the dual walks from the root to `x`.
* `lexFeas_par_eq`: **two lexicographically feasible trees with the same root have the same
  parent darts** (for `ε = lexEps D F`): their paths have the same perturbed length, hence the
  same darts (`count_eq_of_dsum_eq`), hence they are equal (`DTree.eq_tpath_of_count`).
* `linit_lexFeas`: the tree chosen by `linit` is lexicographically feasible; so
  `linit_par_eq`: **every lexicographically feasible tree with the root `o` has the parent darts
  of the tree of `linit`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-! ### Trees with the same parent darts -/

section Congr

variable {T T' : DTree M}

/-- Two trees with the same root and the same parent darts off the root have the same parent
function. -/
lemma DTree.up_eq_of (hr : T.root = T'.root) (hp : ∀ x, x ≠ T.root → T.par x = T'.par x) :
    T.up = T'.up := by
  funext x
  by_cases hx : x = T.root
  · rw [hx, T.up_root, hr, T'.up_root]
  · rw [T.up_of_ne hx, T'.up_of_ne (hr ▸ hx), hp x hx]

/-- ... and the same depths. -/
lemma DTree.depth_eq_of (hr : T.root = T'.root) (hp : ∀ x, x ≠ T.root → T.par x = T'.par x)
    (x : F) : T.depth x = T'.depth x := by
  have hu := DTree.up_eq_of hr hp
  have h1 : T.up^[T'.depth x] x = T.root := by rw [hu, hr]; exact T'.iterate_depth x
  have h2 : T'.up^[T.depth x] x = T'.root := by rw [← hu, ← hr]; exact T.iterate_depth x
  exact le_antisymm (Nat.find_min' (T.reach x) h1) (Nat.find_min' (T'.reach x) h2)

/-- ... and the same edges. -/
lemma DTree.inT_iff_of (hr : T.root = T'.root) (hp : ∀ x, x ≠ T.root → T.par x = T'.par x)
    (d : D) : T.InT d ↔ T'.InT d := by
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hr ▸ hx, by rwa [← hp x hx]⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hr ▸ hx, by rwa [hp x (hr ▸ hx)]⟩

end Congr

/-- **A shortest-path tree for the lexicographic lengths `(c, ε)`**, on its potentials: no dart
is shorter than the difference of the path sums at its ends, in the first coordinate, and in the
second coordinate when the first is tight. -/
def DTree.LexFeas (T : DTree M) (c ε : D → ℤ) : Prop :=
  ∀ d, M.cob (T.psum c) d ≤ c d ∧ (M.cob (T.psum c) d = c d → M.cob (T.psum ε) d ≤ ε d)

/-- **The path of a lexicographically feasible tree is lexicographically shortest** among the
dual walks from the root. -/
theorem DTree.LexFeas.le_walk {T : DTree M} {c ε : D → ℤ} (hT : T.LexFeas c ε) {x : F}
    {l : List D} (hl : DWalk M T.root l x) :
    T.psum c x ≤ dsum c l ∧ (dsum c l = T.psum c x → T.psum ε x ≤ dsum ε l) := by
  have hc := dsum_cob hl (T.psum c)
  have he := dsum_cob hl (T.psum ε)
  rw [T.psum_root] at hc he
  have hres : ∀ d ∈ l, 0 ≤ (c - M.cob (T.psum c)) d := fun d _ => by
    have := (hT d).1; simp only [Pi.sub_apply]; omega
  have hsplit : dsum c l = dsum (c - M.cob (T.psum c)) l + dsum (M.cob (T.psum c)) l := by
    rw [dsum_sub]; ring
  refine ⟨by have := dsum_nonneg hres; linarith, fun heq => ?_⟩
  have hz := eq_zero_of_dsum hres (by linarith)
  have hres' : ∀ d ∈ l, 0 ≤ (ε - M.cob (T.psum ε)) d := fun d hd => by
    have h1 := hz d hd
    simp only [Pi.sub_apply] at h1 ⊢
    have := (hT d).2 (by omega)
    omega
  have hsplit' : dsum ε l = dsum (ε - M.cob (T.psum ε)) l + dsum (M.cob (T.psum ε)) l := by
    rw [dsum_sub]; ring
  have := dsum_nonneg hres'
  linarith

/-- **Two lexicographically feasible trees for the perturbation `lexEps` with the same root have
the same paths.** -/
theorem lexFeas_tpath_eq {T T' : DTree M} {c : D → ℤ} (hT : T.LexFeas c (lexEps D F))
    (hT' : T'.LexFeas c (lexEps D F)) (hr : T.root = T'.root) (x : F) :
    T'.tpath x = T.tpath x := by
  have hw : DWalk M T.root (T'.tpath x) x := hr ▸ T'.dWalk_tpath x
  have hw' : DWalk M T'.root (T.tpath x) x := hr ▸ T.dWalk_tpath x
  obtain ⟨h1, h2⟩ := hT.le_walk hw
  obtain ⟨h1', h2'⟩ := hT'.le_walk hw'
  simp only [T'.dsum_tpath] at h1 h2
  simp only [T.dsum_tpath] at h1' h2'
  have hc : T.psum c x = T'.psum c x := le_antisymm h1 h1'
  have he : T.psum (lexEps D F) x = T'.psum (lexEps D F) x :=
    le_antisymm (h2 hc.symm) (h2' hc)
  have hB : 1 < lexBase F := by unfold lexBase; omega
  have hcnt : ∀ (S : DTree M) d, (S.tpath x).count d < lexBase F := fun S d => by
    have := List.nodup_iff_count_le_one.1 (S.nodup_tpath x) d
    omega
  refine T.eq_tpath_of_count hw fun d => ?_
  refine count_eq_of_dsum_eq (hcnt T') (hcnt T) ?_ d
  change dsum (lexEps D F) (T'.tpath x) = dsum (lexEps D F) (T.tpath x)
  rw [T'.dsum_tpath, T.dsum_tpath, he]

/-- **Two lexicographically feasible trees for the perturbation `lexEps` with the same root have
the same parent darts.** -/
theorem lexFeas_par_eq {T T' : DTree M} {c : D → ℤ} (hT : T.LexFeas c (lexEps D F))
    (hT' : T'.LexFeas c (lexEps D F)) (hr : T.root = T'.root) {x : F} (hx : x ≠ T.root) :
    T'.par x = T.par x := by
  have h := lexFeas_tpath_eq hT hT' hr x
  rw [T.tpath_of_ne hx, T'.tpath_of_ne (hr ▸ hx)] at h
  exact List.singleton_inj.1 (List.append_inj' h rfl).2

/-- **The tree of a state satisfying `LInv` is lexicographically feasible.** -/
lemma LInv.lexFeas_of_cob {c ε : D → ℤ} {s t : V} {st : LSt M} (hI : LInv c ε s t st)
    (hg : st.g = M.cob (st.T.psum c)) (hh : st.h = M.cob (st.T.psum ε)) :
    st.T.LexFeas c ε := fun d => by
  have h1 := hI.base.pseudo.le_cap d
  simp only [LSt.base_g] at h1
  refine ⟨hg ▸ h1, fun he => ?_⟩
  rw [← hh]
  exact hI.lex d (by rw [hg]; exact he)

/-- **The tree of `linit` is lexicographically feasible.** -/
theorem linit_lexFeas {c ε : D → ℤ} {s t : V} {o : F} {st : LSt M}
    (h : linit M c ε s t o = some st) : st.T.LexFeas c ε := by
  unfold linit at h
  split_ifs at h with hex
  obtain rfl := Option.some.inj h
  obtain ⟨-, hI, hg, hh⟩ := hex.choose_spec
  exact hI.lexFeas_of_cob hg hh

/-- **Every lexicographically feasible tree rooted at `o` has the parent darts of the tree of
`linit`** (for the perturbation `lexEps`): the initial tree of the perturbed run is determined by
its root, so any correct shortest-path procedure computes it. -/
theorem linit_par_eq {c : D → ℤ} {s t : V} {o : F} {st : LSt M}
    (h : linit M c (lexEps D F) s t o = some st) {T : DTree M} (hT : T.LexFeas c (lexEps D F))
    (hr : T.root = o) {x : F} (hx : x ≠ o) : T.par x = st.T.par x := by
  have hr' : st.T.root = o := (linit_inv _ _ h).1
  exact lexFeas_par_eq (linit_lexFeas h) hT (hr'.trans hr.symm) (hr' ▸ hx)

end STFlow

end PlanarFlow
