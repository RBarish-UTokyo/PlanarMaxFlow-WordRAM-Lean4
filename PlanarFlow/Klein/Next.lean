module

public import PlanarFlow.Klein.Values

/-!
# From one move to the next

At the end of the move from `u` to `v` (with the dart `e` from `u` to `v` the parent dart of `v`),
the next move goes from `v` to `w` with the dart `e'` from `v` to `w`. The spanning tree is
re-rooted at `v` (`rerootChild`: `u` gets the parent dart `rev e`; no edge changes, so the dual
cotree does not change), and `w` gets the parent dart `e'` (a reparenting, with the update of
the values of `reparent_vinv`: one `ADDPATH`, one `CUT`, one `LINK` in the dual cotree).

* `rerootChild_psum`: the labels after re-rooting change by `-φ e` below `v` and by `φ (rev e)`
  elsewhere; with `φ e = φ (rev e) = 0` (the weights of the boundary darts) they do not change,
  and neither do the values (`rerootChild_vinv`).
* `next_move`: **the data for the next move**: a tree rooted at `v`, with `e'` the parent dart of
  `w`, `rev e` the parent dart of `u` (when `w ≠ u`), the other parent darts unchanged, and values
  satisfying the invariant `VInv`.
* `next_compat`: the same in the setting `PlanarFlow.MSSP.Hyp`: from the end of the move `j` to
  the start of the move `(j + 1) % k`, the tree extends the forest of the start of the pivot loop
  of the next move (`Compat`), so `minpath_spec`, `pivot_values` and `dataRun_isRun` apply to it.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-- **Re-rooting a tree at a child of the root**: the old root gets the reverse of the parent
dart of the new root. -/
def rerootChild (T : DTree M.dual) (v : V) (hv : v ≠ T.root) (hup : M.tail (T.par v) = T.root) :
    DTree M.dual where
  root := v
  par := Function.update T.par T.root (M.rev (T.par v))
  head_par x hx := by
    by_cases h : x = T.root
    · subst h
      simp only [Function.update_self]
      change M.head (M.rev (T.par v)) = _
      rw [M.head_rev, hup]
    · rw [Function.update_of_ne h]; exact T.head_par x h
  reach x := by
    have hup' : ∀ y, upF M.dual v (Function.update T.par T.root (M.rev (T.par v))) y =
        if y = v then v else if y = T.root then v else T.up y := by
      intro y
      unfold upF
      by_cases hyv : y = v
      · simp [hyv]
      by_cases hyr : y = T.root
      · subst hyr
        simp only [hyv, ↓reduceIte, Function.update_self]
        change M.head (T.par v) = v
        exact tpar_head T hv
      · simp only [hyv, hyr, ↓reduceIte, Function.update_of_ne hyr]
        exact (tup_eq T hyr).symm
    suffices ∀ n y, T.up^[n] y = T.root →
        ∃ m, (upF M.dual v (Function.update T.par T.root (M.rev (T.par v))))^[m] y = v from
      this _ x (T.iterate_depth x)
    intro n
    induction n with
    | zero =>
      intro y hy
      have hy' : y = T.root := hy
      exact ⟨1, by rw [Function.iterate_one, hup']; simp [hy', hv.symm]⟩
    | succ n ih =>
      intro y hy
      by_cases hyv : y = v
      · exact ⟨0, hyv⟩
      by_cases hyr : y = T.root
      · exact ⟨1, by simp only [Function.iterate_one, hup', hyr]; simp [hv.symm]⟩
      obtain ⟨m, hm⟩ := ih (T.up y) (by rwa [← Function.iterate_succ_apply])
      refine ⟨m + 1, ?_⟩
      rw [Function.iterate_succ_apply, hup']
      simpa [hyv, hyr] using hm

section Reroot

variable (T : DTree M.dual) {v : V} (hv : v ≠ T.root) (hup : M.tail (T.par v) = T.root)

lemma rerootChild_par (x : V) (hx : x ≠ T.root) : (rerootChild T v hv hup).par x = T.par x :=
  Function.update_of_ne hx _ _

lemma rerootChild_par_root : (rerootChild T v hv hup).par T.root = M.rev (T.par v) :=
  Function.update_self _ _ _

/-- **The edges do not change** when re-rooting. -/
lemma rerootChild_inT (d : D) : (rerootChild T v hv hup).InT d ↔ T.InT d := by
  constructor
  · rintro ⟨x, hx, hd⟩
    by_cases hxr : x = T.root
    · subst hxr
      rw [rerootChild_par_root] at hd
      refine ⟨v, hv, ?_⟩
      rcases hd with h | h
      · exact Or.inr h
      · exact Or.inl (by rw [h]; exact M.rev_rev _)
    · rw [rerootChild_par T hv hup x hxr] at hd
      exact ⟨x, hxr, hd⟩
  · rintro ⟨x, hx, hd⟩
    by_cases hxv : x = v
    · subst hxv
      refine ⟨T.root, Ne.symm hv, ?_⟩
      rw [rerootChild_par_root]
      rcases hd with h | h
      · exact Or.inr (by rw [h]; exact (M.rev_rev _).symm)
      · exact Or.inl h
    · refine ⟨x, hxv, ?_⟩
      rw [rerootChild_par T hv hup x hx]
      exact hd

open Classical in
/-- **The labels after re-rooting**: `-φ e` below `v`, `+φ (rev e)` elsewhere. -/
theorem rerootChild_psum (φ : D → ℤ) (x : V) :
    (rerootChild T v hv hup).psum φ x =
      T.psum φ x - if T.Anc v x then φ (T.par v) else -φ (M.rev (T.par v)) := by
  refine ((rerootChild T v hv hup).psum_unique φ (k := fun x => T.psum φ x -
    if T.Anc v x then φ (T.par v) else -φ (M.rev (T.par v))) ?_ ?_ x).symm
  · show T.psum φ v - (if T.Anc v v then _ else _) = 0
    simp only [T.anc_self v, ↓reduceIte]
    rw [T.psum_of_ne φ hv, tup_eq T hv, hup, T.psum_root]
    ring
  · intro y hy
    change y ≠ v at hy
    have hupy : (rerootChild T v hv hup).up y =
        if y = T.root then v else T.up y := by
      unfold DTree.up
      change upF M.dual v (Function.update T.par T.root (M.rev (T.par v))) y = _
      unfold upF
      by_cases hyr : y = T.root
      · subst hyr
        simp only [hy, ↓reduceIte, Function.update_self]
        change M.head (T.par v) = v
        exact tpar_head T hv
      · simp only [hy, hyr, ↓reduceIte, Function.update_of_ne hyr]
    rw [hupy]
    by_cases hyr : y = T.root
    · subst hyr
      have hna : ¬ T.Anc v T.root := fun h => hv (T.anc_root_iff.1 h)
      simp only [↓reduceIte, rerootChild_par_root, hna, T.anc_self v, T.psum_root,
        T.psum_of_ne φ hv, tup_eq T hv, hup]
      ring
    · simp only [hyr, ↓reduceIte, rerootChild_par T hv hup y hyr, T.anc_up_iff hy,
        T.psum_of_ne φ hyr]
      split_ifs <;> ring

/-- **With weight `0` on both darts of the edge to the new root, the values keep the
invariant.** -/
theorem rerootChild_vinv {φ wt val : D → ℤ} (h0 : φ (T.par v) = 0)
    (h1 : φ (M.rev (T.par v)) = 0) (hV : VInv T φ wt val) :
    VInv (rerootChild T v hv hup) φ wt val := by
  intro d hd
  rw [rerootChild_inT] at hd
  rw [hV d hd, rerootChild_psum, rerootChild_psum, h0, h1]
  split_ifs <;> ring

end Reroot

/-- **The data for the next move**: from a tree rooted at `u` in which the dart `e` from `u`
(of weight `0` both ways) is the parent dart of `v`, and values satisfying the invariant, a tree
rooted at `v` in which the dart `e'` from `v` to `w` is the parent dart of `w`, `rev e` that of
`u`, every other parent dart unchanged, and values satisfying the invariant. -/
theorem next_move (hM : M.IsPlane) {T : DTree M.dual} {u v w : V} {e e' : D}
    {φ wt val : D → ℤ} (hroot : T.root = u) (hpar : T.par v = e) (heu : M.tail e = u)
    (hvu : v ≠ u) (h0 : φ e = 0) (h1 : φ (M.rev e) = 0) (hV : VInv T φ wt val)
    (he'v : M.tail e' = v) (he'w : M.head e' = w) (hwv : w ≠ v) :
    ∃ (T' : DTree M.dual) (val' : D → ℤ), T'.root = v ∧ T'.par w = e' ∧
      (w ≠ u → T'.par u = M.rev e) ∧ (∀ x, x ≠ u → x ≠ w → T'.par x = T.par x) ∧
      VInv T' φ wt val' := by
  have hv : v ≠ T.root := hroot ▸ hvu
  have hup : M.tail (T.par v) = T.root := by rw [hpar, heu, hroot]
  set T₁ := rerootChild T v hv hup with hT₁
  have hV₁ : VInv T₁ φ wt val := rerootChild_vinv T hv hup (hpar ▸ h0) (hpar ▸ h1) hV
  have hr₁ : T₁.root = v := rfl
  have hpu : T₁.par u = M.rev e := by
    rw [← hroot, hT₁, rerootChild_par_root, hpar]
  have hpx : ∀ x, x ≠ u → T₁.par x = T.par x := fun x hx =>
    rerootChild_par T hv hup x (hroot ▸ hx)
  by_cases hin : T₁.par w = e'
  · exact ⟨T₁, val, hr₁, hin, fun _ => hpu, fun x hx _ => hpx x hx, hV₁⟩
  -- `w` gets the parent dart `e'`
  have hw₁ : w ≠ T₁.root := hwv
  have hby : M.dual.face (M.dual.rev e') = w := he'w
  have hna : ¬ T₁.Anc w (M.dual.face e') := by
    change ¬ T₁.Anc w (M.tail e')
    rw [he'v, ← hr₁, T₁.anc_root_iff]; exact hwv
  have hbT : ¬ T₁.InT e' := by
    rintro ⟨x, hx, hd | hd⟩
    · have : x = w := by rw [← tpar_head T₁ hx, ← hd, he'w]
      subst this; exact hin hd.symm
    · have hd' : e' = M.rev (T₁.par x) := hd
      have : M.head (T₁.par x) = v := by rw [← M.tail_rev, ← hd', he'v]
      rw [tpar_head T₁ hx] at this
      exact hx this
  refine ⟨T₁.reparent w e' hw₁ hby hna, _, rfl, ?_, ?_, fun x hx hxw => ?_,
    reparent_vinv hM T₁ hw₁ hby hna hbT hV₁⟩
  · show Function.update T₁.par w e' w = e'
    exact Function.update_self _ _ _
  · intro hwu
    show Function.update T₁.par w e' u = M.rev e
    rw [Function.update_of_ne (Ne.symm hwu)]; exact hpu
  · show Function.update T₁.par w e' x = T.par x
    rw [Function.update_of_ne hxw]; exact hpx x hx

/-- **The next move in the setting of the face**: at the end of the move `j` (the tree extends
the shortest-path tree of the next root, with the boundary dart `g j` of weight `0` both ways),
the data for the move `j' = (j + 1) % k` exist: a tree extending the shortest-path tree of the
root `tail (g j')` (the start of the pivot loop of that move) with `g j'` the parent dart of the
following root, and values satisfying the invariant. -/
theorem next_compat {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ} (H : Hyp M k g S ℓ)
    {j : ℕ} (hj : j < k) {T : DTree M.dual} {φ wt val : D → ℤ}
    (hC : Compat T (M.tail (g j)) (M.tail (g ((j + 1) % k))) (g j)
      (tpar (pieceGraph M S ℓ) (M.tail (g ((j + 1) % k)))))
    (h0 : φ (g j) = 0) (h1 : φ (M.rev (g j)) = 0) (hV : VInv T φ wt val) :
    ∃ (T' : DTree M.dual) (val' : D → ℤ),
      Compat T' (M.tail (g ((j + 1) % k))) (M.tail (g (((j + 1) % k + 1) % k))) (g ((j + 1) % k))
        (tpar (pieceGraph M S ℓ) (M.tail (g ((j + 1) % k)))) ∧ VInv T' φ wt val' := by
  have hk : 2 ≤ k := H.face.two_le
  set j' := (j + 1) % k with hj'
  have hj'k : j' < k := Nat.mod_lt _ (by omega)
  have hne : ∀ i < k, i ≠ (i + 1) % k := fun i hi => by
    rcases Nat.lt_or_ge (i + 1) k with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [show i + 1 = k by omega, Nat.mod_self]; omega
  have hhead : ∀ i < k, M.head (g i) = M.tail (g ((i + 1) % k)) := fun i hi => by
    rw [CombMap.head, ← M.tail_next, H.face.next i hi]
  have hvu : M.tail (g j') ≠ M.tail (g j) := fun h =>
    hne j hj (H.face.inj _ hj'k _ hj h).symm
  have hwv : M.tail (g ((j' + 1) % k)) ≠ M.tail (g j') := fun h =>
    hne j' hj'k (H.face.inj _ (Nat.mod_lt _ (by omega)) _ hj'k h).symm
  obtain ⟨T', val', hr, hpw, -, hpx, hV'⟩ := next_move H.plane hC.root hC.par_v hC.tail hvu h0 h1
    hV rfl (hhead j' hj'k) hwv
  refine ⟨T', val', ⟨hr, hpw, rfl, fun x a hx => ?_⟩, hV'⟩
  obtain ⟨-, hd, -⟩ := tpar_spec hx
  have hnr : ∀ i < k, x ≠ M.tail (g i) := fun i hi h =>
    H.noIn a.1 a.2 ⟨i, hi, by rw [← h, ← hd]; rfl⟩
  rw [hpx x (hnr j hj) (hnr _ (Nat.mod_lt _ (by omega)))]
  exact hC.par x a hx

end Klein

end PlanarFlow
