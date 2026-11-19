module

public import PlanarSeparator.Machine.MillerComp
public import PlanarSeparator.Machine.CycleBridge
public import PlanarSeparator.MillerTri

/-!
# Miller's separator on the machine: components and heavy levels of a coded map

For a plane map `M` coded as in `PlanarSeparator.CycleSearch.Coded` (darts numbered so that the
face permutation is `phi3`, the face `F` with index `fi cd F`), and flags on the faces marking
the faces off `zone B` for a set of vertices `B`:

* `MillerProg.fa_iff`: the numeric adjacency `FA` of the program `clab` is the adjacency `FAdj`
  of the faces off `zone B`;
* `MillerProg.rtg_iff`: hence the classes of `FA` are the components `comp B`, and the labels of
  `clab` are the components (`MillerProg.label_eq_iff`).

For a breadth-first tree `T` of a triangulation and a level `l ≥ 1`:

* `MillerProg.mem_ins_comp_iff`: a vertex lies in the strict inside of the component of a face
  at level `l` if and only if its level is `> l` and the face of one (any) of its darts lies in
  the component;
* `MillerProg.heavy_iff`: the level `l` is heavy (`PlanarSeparator.Map.Heavy`) for the weights
  `w v / Σ w` exactly when some vertex `v` of level `> l` has, together with the vertices of
  level `> l` whose first darts lie in the component of the first dart of `v`, more than `2/3`
  of the total weight. This is the test a program computes from the labels of `clab`.
-/

@[expose] public section

namespace PlanarSeparator

namespace MillerProg

open Finset Map CycleSearch

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] {M : Map D P}

/-! ### The labels are the components -/

section Coded

variable {T₀ : M.SpTree} {k : ℕ} {cd : D ≃ Fin (3 * k)} {A Tm : ℕ → ℕ}
  (hC : Coded M T₀ k cd A Tm)
include hC

theorem revOk : RevOk k A := fun x hx => ⟨hC.tri.A_lt x hx, hC.tri.A_A x hx⟩

/-- The numeric adjacency is the adjacency of the faces off `zone B`. -/
theorem fa_iff {B : Finset P} {Av : ℕ → ℕ} (hAv : ∀ F : M.Face, 0 < Av (fi cd F) ↔ F ∉ M.zone B)
    {F G : M.Face} : FA k A Av (fi cd F) (fi cd G) ↔ FAdj (M.zone B)ᶜ F G := by
  constructor
  · rintro ⟨hFk, hF, hG, j, hj, hjG⟩
    set y := cd.symm ⟨3 * fi cd F + j, by omega⟩ with hy
    have hcy : (cd y : ℕ) = 3 * fi cd F + j := by rw [hy]; simp
    have hyF : M.face y = F := hC.fi_inj (by rw [hC.fi_face, hcy]; omega)
    have hyG : M.face (M.α y) = G := hC.fi_inj (by rw [hC.fi_face, ← hC.A_cd, hcy, hjG])
    exact ⟨mem_compl.2 ((hAv F).1 hF), mem_compl.2 ((hAv G).1 hG), y, hyF, hyG⟩
  · rintro ⟨hF, hG, d, rfl, rfl⟩
    refine ⟨hC.fi_lt _, (hAv _).2 (mem_compl.1 hF), (hAv _).2 (mem_compl.1 hG),
      (cd d : ℕ) % 3, Nat.mod_lt _ (by omega), ?_⟩
    rw [hC.fi_face, hC.fi_face, Nat.div_add_mod, hC.A_cd]

/-- The classes of the numeric adjacency are the components. -/
theorem rtg_iff {B : Finset P} {Av : ℕ → ℕ} (hAv : ∀ F : M.Face, 0 < Av (fi cd F) ↔ F ∉ M.zone B)
    {F G : M.Face} (hF : F ∉ M.zone B) :
    Relation.ReflTransGen (FA k A Av) (fi cd F) (fi cd G) ↔ G ∈ M.comp B F := by
  constructor
  · intro h
    have key : ∀ n, Relation.ReflTransGen (FA k A Av) (fi cd F) n →
        ∀ G : M.Face, fi cd G = n → G ∈ M.comp B F := by
      intro n hn
      induction hn with
      | refl => intro G hG; rw [hC.fi_inj hG]; exact Map.mem_comp_self hF
      | tail _ hbc ih =>
        intro G hG
        obtain ⟨G', hG'⟩ := hC.exists_fi hbc.1
        rw [← hG', ← hG] at hbc
        obtain ⟨-, hG2, d, hd1, hd2⟩ := (fa_iff hC hAv).1 hbc
        rw [← hd2]
        exact Map.mem_comp_of_adj (by rw [hd1]; exact ih G' hG')
          (by rw [hd2]; exact mem_compl.1 hG2)
    exact key _ h G rfl
  · intro h
    obtain ⟨-, hr⟩ := Map.mem_comp.1 h
    exact Relation.ReflTransGen.lift (fi cd) (fun a b hab => (fa_iff hC hAv).2 hab) _ _ hr

/-- **The labels of `clab` are the components.** -/
theorem label_eq_iff {B : Finset P} {Av lb : ℕ → ℕ}
    (hAv : ∀ F : M.Face, 0 < Av (fi cd F) ↔ F ∉ M.zone B)
    (hlb : ∀ f < k, ∀ g < k, 0 < Av f → 0 < Av g →
      (lb f = lb g ↔ Relation.ReflTransGen (FA k A Av) f g))
    {F G : M.Face} (hF : F ∉ M.zone B) (hG : G ∉ M.zone B) :
    lb (fi cd F) = lb (fi cd G) ↔ G ∈ M.comp B F := by
  rw [hlb _ (hC.fi_lt F) _ (hC.fi_lt G) ((hAv F).2 hF) ((hAv G).2 hG), rtg_iff hC hAv hF]

end Coded

/-! ### Heavy levels -/

section Heavy

variable {T : M.SpTree} (hM : M.IsPlane) (hT : IsBFS T) (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d)
include hM hT h3

/-- **The strict inside of a component** at a level `l ≥ 1`: the vertices of level `> l` with a
face in it, read at any of their darts. -/
theorem mem_ins_comp_iff {l : ℕ} (hl : 1 ≤ l) {f : M.Face} {v : P} {d : D} (hd : M.vert d = v) :
    v ∈ ins (M.comp (T.low l) f) ↔ l < T.height v ∧ M.face d ∈ M.comp (T.low l) f :=
  ⟨fun h => ⟨lt_of_mem_ins hM hT hl h, mem_ins.1 h d hd⟩,
    fun h => mem_ins_of_lt hT h3 h.1 hd h.2⟩

/-- **The heavy test.** For natural weights `w` and a dart `fd v` at every vertex, the level
`l ≥ 1` is heavy for the weights `w v / Σ w` if and only if some vertex `v` of level `> l`
gathers, with the vertices of level `> l` whose darts `fd` lie in the component of `fd v`, more
than `2/3` of the total weight. -/
theorem heavy_iff {l : ℕ} (hl : 1 ≤ l) (w : P → ℕ) {fd : P → D} (hfd : ∀ v, M.vert (fd v) = v) :
    Heavy T (fun v => (w v : ℝ) / ∑ u, (w u : ℝ)) l ↔
      ∃ v, l < T.height v ∧ 2 * ∑ u, w u < 3 * ∑ u ∈ univ.filter (fun u =>
        l < T.height u ∧ M.face (fd u) ∈ M.comp (T.low l) (M.face (fd v))), w u := by
  classical
  have hins : ∀ f, ins (M.comp (T.low l) f) = univ.filter (fun u =>
      l < T.height u ∧ M.face (fd u) ∈ M.comp (T.low l) f) := fun f => by
    ext u; rw [mem_filter, mem_ins_comp_iff hM hT h3 hl (hfd u)]; simp
  have hdiv : ∀ S : Finset P, (∑ u ∈ S, (w u : ℝ) / ∑ u, (w u : ℝ)) =
      (∑ u ∈ S, (w u : ℝ)) / ∑ u, (w u : ℝ) := fun S => by rw [sum_div]
  have hcmp : ∀ S : Finset P, 2 / 3 < (∑ u ∈ S, (w u : ℝ)) / ∑ u, (w u : ℝ) ↔
      2 * ∑ u, w u < 3 * ∑ u ∈ S, w u := by
    intro S
    have hS : ∑ u ∈ S, w u ≤ ∑ u, w u := sum_le_sum_of_subset (subset_univ _)
    by_cases h0 : ∑ u, w u = 0
    · have : (∑ u, (w u : ℝ)) = 0 := by exact_mod_cast h0
      rw [this, div_zero]; norm_num; omega
    · have hpos : (0 : ℝ) < ∑ u, (w u : ℝ) := by
        have : 0 < ∑ u, w u := Nat.pos_of_ne_zero h0
        exact_mod_cast this
      rw [lt_div_iff₀ hpos]
      constructor
      · intro h
        have : (2 * ∑ u, w u : ℝ) < 3 * ∑ u ∈ S, w u := by push_cast; linarith
        exact_mod_cast this
      · intro h
        have : (2 * ∑ u, w u : ℝ) < 3 * ∑ u ∈ S, w u := by exact_mod_cast h
        push_cast at this; linarith
  constructor
  · rintro ⟨f, hf, hh⟩
    rw [hdiv, hcmp] at hh
    obtain ⟨v, hv⟩ : (ins (M.comp (T.low l) f)).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      rw [hne, sum_empty] at hh; omega
    have hv' := (mem_ins_comp_iff hM hT h3 hl (hfd v)).1 hv
    refine ⟨v, hv'.1, ?_⟩
    rw [comp_eq_of_mem hv'.2, ← hins]
    exact hh
  · rintro ⟨v, hv, hh⟩
    refine ⟨M.face (fd v), notMem_zone_of_lt hT h3 hv (hfd v), ?_⟩
    rw [hdiv, hcmp, hins]
    exact hh

end Heavy

end MillerProg

end PlanarSeparator
