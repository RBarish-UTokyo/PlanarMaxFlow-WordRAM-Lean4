module

public import PlanarFlow.NegSSSP.Enc.SrcArrRun

/-!
# The initial spanning tree of Klein's encoding from parent darts

Klein's encoding (`Klein.KValNL`) needs a spanning tree `T : DTree M.dual` of the vertices,
rooted at the first root `u = tripSrc 0`, whose parent dart of `v = tripDst 0` is the boundary
dart `e = g 0` and whose parent darts of the vertices reached in the piece are those of the
shortest-path tree (`Klein.Compat`). The programs can compute the parents of the reached vertices
(`spTreeProg_tpar`) and, by a search of the whole map, a spanning tree `C₀` rooted at `u`
(`dtree_of_ct`); here **the combination is a tree**:

* `dtree_of_rank`: parent darts entering every node but the root, with a rank decreasing along
  the parents, are the parents of a `DTree`.
* `parT C₀ u v e`: the parent dart of `x` is `e` for `x = v`, the parent of `x` in the
  shortest-path tree of `u` when `x` is reached, its parent in `C₀` otherwise.
* `tree_compat`: **`parT` is the parent function of a `DTree M.dual` rooted at `u` meeting
  `Klein.Compat`**, when the lengths are positive on the piece, `e` goes from `u` to `v`, `v ≠ u`
  is not reached from `u` in the piece (as for the second root of the map with the sources copied,
  no dart of the piece entering a root), and `C₀` is any tree rooted at `u`. The rank: the distance
  from `u` for the reached vertices, a bound on the distances plus the depth in `C₀` for the
  others.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset MSSP Klein

/-- **A tree from parent darts with a decreasing rank.** -/
theorem dtree_of_rank {D X Y : Type*} [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y]
    {N : CombMap D X Y} (r : Y) (par : Y → D) (ρ : Y → ℕ)
    (hh : ∀ y, y ≠ r → N.face (N.rev (par y)) = y)
    (hρ : ∀ y, y ≠ r → ρ (N.face (par y)) < ρ y) :
    ∃ T : STFlow.DTree N, T.root = r ∧ ∀ y, y ≠ r → T.par y = par y := by
  have hreach : ∀ y, ∃ m, (STFlow.upF N r par)^[m] y = r := by
    intro y
    induction hn : ρ y using Nat.strong_induction_on generalizing y with
    | _ m ih =>
      by_cases hy : y = r
      · exact ⟨0, hy⟩
      obtain ⟨m', hm'⟩ := ih _ (hn ▸ hρ y hy) (N.face (par y)) rfl
      refine ⟨m' + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      have : STFlow.upF N r par y = N.face (par y) := by simp [STFlow.upF, hy]
      rw [this]; exact hm'
  exact ⟨⟨r, par, hh, hreach⟩, rfl, fun _ _ => rfl⟩

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ}

variable (M S ℓ) in
/-- **The combined parent darts**: `e` at `v`, the shortest-path tree of `u` at the reached
vertices, the tree `C₀` elsewhere. -/
noncomputable def parT (C₀ : STFlow.DTree M.dual) (u v : V) (e : D) (x : V) : D :=
  if x = v then e else
    match tpar (pieceGraph M S ℓ) u x with
    | some a => a.1
    | none => C₀.par x

/-- **The combined parents form a tree meeting `Compat`** (see the module docstring). -/
theorem tree_compat (hpos : ∀ d ∈ S, 0 < ℓ d) {u v : V} {e : D} (hu : M.tail e = u)
    (hv : M.head e = v) (huv : u ≠ v) (hvr : ¬ Reach (pieceGraph M S ℓ) u v)
    (C₀ : STFlow.DTree M.dual) (hC₀ : C₀.root = u) :
    ∃ T : STFlow.DTree M.dual, Compat T u v e (tpar (pieceGraph M S ℓ) u) ∧
      ∀ x, x ≠ u → T.par x = parT M S ℓ C₀ u v e x := by
  classical
  set G := pieceGraph M S ℓ with hG
  have hnn : ∀ a, 0 ≤ G.len a := fun a => (hpos a.1 a.2).le
  let Bd : ℕ := univ.sup fun x => (dist G u x).toNat
  have hBd : ∀ x, (dist G u x).toNat ≤ Bd := fun x =>
    Finset.le_sup (f := fun x => (dist G u x).toNat) (mem_univ x)
  let ρ : V → ℕ := fun x => if Reach G u x then (dist G u x).toNat else Bd + 1 + C₀.depth x
  -- the parents of the reached vertices
  have hreach_t : ∀ x a, tpar G u x = some a → Reach G u x := fun x a h => by
    obtain ⟨⟨h1, -⟩, h2, -⟩ := tpar_spec h
    rw [← h2]; exact h1.arc
  have hhead : ∀ x, x ≠ u → M.dual.face (M.dual.rev (parT M S ℓ C₀ u v e x)) = x := by
    intro x hx
    show M.tail (M.rev (parT M S ℓ C₀ u v e x)) = x
    unfold parT
    by_cases hxv : x = v
    · simp only [hxv, ↓reduceIte]; exact hv
    · simp only [hxv, ↓reduceIte]
      rcases h : tpar G u x with _ | a
      · have := C₀.head_par x (by rw [hC₀]; exact hx)
        simpa [CombMap.dual] using this
      · exact (tpar_spec h).2.1
  have hrank : ∀ x, x ≠ u → ρ (M.dual.face (parT M S ℓ C₀ u v e x)) < ρ x := by
    intro x hx
    show ρ (M.tail (parT M S ℓ C₀ u v e x)) < ρ x
    have hu0 : ρ u = 0 := by simp [ρ, Reach.refl, dist_self hnn]
    unfold parT
    by_cases hxv : x = v
    · simp only [hxv, ↓reduceIte, hu, hu0]
      simp [ρ, hvr]
    · simp only [hxv, ↓reduceIte]
      rcases h : tpar G u x with _ | a
      · -- not reached: the parent in `C₀`
        have hxr : ¬ Reach G u x := fun hr => by
          obtain ⟨a, ha⟩ := tpar_isSome hnn hr hx
          rw [ha] at h; exact absurd h (by simp)
        have hup : M.tail (C₀.par x) = C₀.up x := by
          rw [C₀.up_of_ne (by rw [hC₀]; exact hx)]; rfl
        have hd := C₀.depth_up (show x ≠ C₀.root by rw [hC₀]; exact hx)
        simp only [hup]
        by_cases hpr : Reach G u (C₀.up x)
        · have := hBd (C₀.up x)
          simp only [ρ, hpr, hxr, ↓reduceIte]; omega
        · simp only [ρ, hpr, hxr, ↓reduceIte]; omega
      · -- reached: the parent in the shortest-path tree
        obtain ⟨hs, hd⟩ := tpar_dist h
        have hl : 0 < G.len a := hpos a.1 a.2
        have h0 := dist_nonneg hnn hs
        have hr := hreach_t x a h
        show ρ (G.src a) < ρ x
        simp only [ρ, hs, hr, ↓reduceIte]
        omega
  obtain ⟨T, hTr, hTp⟩ := dtree_of_rank (N := M.dual) u (parT M S ℓ C₀ u v e) ρ
    hhead hrank
  refine ⟨T, ⟨hTr, ?_, hu, fun x a h => ?_⟩, hTp⟩
  · rw [hTp v (Ne.symm huv)]; simp [parT]
  · have hxu : x ≠ u := (tpar_spec h).2.2
    have hxv : x ≠ v := fun e' => hvr (e' ▸ hreach_t x a h)
    rw [hTp x hxu]
    simp only [parT, hxv, ↓reduceIte]
    rw [show tpar (pieceGraph M S ℓ) u x = some a from h]

/-- A walk ends where it starts or with an arc entering its end. -/
lemma lwalk_last {X A : Type*} {G : Digraph X A} {x y : X} {l : List A} (h : LWalk G x y l) :
    x = y ∨ ∃ a ∈ l, G.dst a = y := by
  induction h with
  | nil x => exact Or.inl rfl
  | @cons a y l h ih =>
    rcases ih with e | ⟨a', ha', e⟩
    · exact Or.inr ⟨a, List.mem_cons_self .., e⟩
    · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', e⟩

/-- **The initial tree of Klein's encoding**, in the setting of Klein's algorithm (`Hyp`): for
any tree `C₀` of the vertices rooted at the first root, the combined parents (the dart `g 0` at
the second root, the shortest-path tree of the first root at the reached vertices, `C₀`
elsewhere) form a tree `T` meeting `Compat` (the last hypothesis of `KValNL`). -/
theorem tree_compat_hyp {k : ℕ} {g : ℕ → D} (H : Hyp M k g S ℓ) (C₀ : STFlow.DTree M.dual)
    (hC₀ : C₀.root = tripSrc M k g 0) :
    ∃ T : STFlow.DTree M.dual,
      Compat T (tripSrc M k g 0) (tripDst M k g 0) (g (0 % k))
        (tpar (pieceGraph M S ℓ) (tripSrc M k g 0)) ∧
      ∀ x, x ≠ tripSrc M k g 0 →
        T.par x = parT M S ℓ C₀ (tripSrc M k g 0) (tripDst M k g 0) (g (0 % k)) x := by
  have hk := H.face.two_le
  have h1 : (0 + 1) % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hu : M.tail (g (0 % k)) = tripSrc M k g 0 := rfl
  have hv : M.head (g (0 % k)) = tripDst M k g 0 := by
    unfold tripDst CombMap.head
    rw [← M.tail_next, Nat.zero_mod, H.face.next 0 (by omega)]
  have huv : tripSrc M k g 0 ≠ tripDst M k g 0 := by
    unfold tripSrc tripDst
    rw [Nat.zero_mod, h1]
    intro e
    exact absurd (H.face.inj 0 (by omega) 1 (by omega) e) (by omega)
  have hvr : ¬ Reach (pieceGraph M S ℓ) (tripSrc M k g 0) (tripDst M k g 0) := by
    rintro ⟨l, hl⟩
    rcases lwalk_last hl with e | ⟨a, -, e⟩
    · exact huv e
    · refine H.noIn a.1 a.2 ⟨1, by omega, ?_⟩
      show M.tail (g 1) = M.head a.1
      rw [← h1]; exact e.symm
  exact tree_compat H.pos hu hv huv hvr C₀ hC₀

/-- **The parent array of the combined tree**: the parents of a search tree `C₀` at `PAb + ιv y`
(`y ≠ u`), overwritten by the shortest-path parents at the reached vertices and by `e` at `v`,
are the parents `parT` (the hypothesis of `toProg_orders` for `T`). -/
lemma parT_mem {C₀ : STFlow.DTree M.dual} {u v : V} {e : D} {nD : ℕ} (σ : D ≃ Fin nD)
    (ιv : V → ℕ) {mem : ℕ → ℕ} {PAb : ℕ}
    (h1 : ∀ x a, tpar (pieceGraph M S ℓ) u x = some a → x ≠ v → mem (PAb + ιv x) = σ a.1)
    (h2 : ∀ y, y ≠ u → y ≠ v → tpar (pieceGraph M S ℓ) u y = none →
      mem (PAb + ιv y) = σ (C₀.par y))
    (h3 : mem (PAb + ιv v) = σ e) (y : V) (hy : y ≠ u) :
    mem (PAb + ιv y) = σ (parT M S ℓ C₀ u v e y) := by
  unfold parT
  by_cases hyv : y = v
  · simp only [hyv, ↓reduceIte]; exact h3
  · simp only [hyv, ↓reduceIte]
    rcases h : tpar (pieceGraph M S ℓ) u y with _ | a
    · exact h2 y hy hyv h
    · exact h1 y a h hyv

end NegSSSP

end PlanarFlow
