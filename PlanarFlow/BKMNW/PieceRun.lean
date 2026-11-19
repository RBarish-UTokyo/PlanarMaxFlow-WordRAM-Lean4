module

public import PlanarFlow.BKMNW.PieceMap
public import PlanarFlow.BKMNW.Transfer

/-!
# Running the recursion on the piece maps: the terminals, the holes and the separator

On the piece map of a piece `P` with holes `Hs` (`pmap`, with darts `pdarts M P Hs` and the holes
contracted), the sources, the sinks and the holes are the images of those of `M` (`vimg`): a hole
becomes one vertex (or none, when the piece does not touch it), the vertex of a one-vertex path
(`SPath.point`); the separator becomes a simple path of the piece map (`SPath.toPiece`), whose
vertices are the images of its vertices. The separator may be a path of one vertex: its image is
then the path of one vertex at the image of that vertex, given by a dart of the piece map at it.

The embeddings of maps (`PlanarFlow.BKMNW.Emb`) from a child piece map into its parent
(`childEmb`) and from the piece map of the whole map into `M` (`rootEmb`) transfer the outputs of
the recursion (`msOut_child`, `msOut_root`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv CombMap Relation Orbit

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-! ### The piece map -/

/-- **The piece map** of a piece satisfying `PieceInv`. -/
noncomputable def pmap {P : Finset D} {Hs : List (Finset V)} {σ : Perm D}
    (h : PieceInv M P Hs σ) :
    CombMap (SDart (pdarts M P Hs)) (SVert σ (pdarts M P Hs))
      (SFace σ (pdarts M P Hs) (revPerm M)) :=
  subMap (pdarts M P Hs) (revPerm_isInv M) h.stable (stable_pdarts h.rev Hs)

section Piece

variable {P : Finset D} {Hs : List (Finset V)} {σ : Perm D}

lemma pmap_tail (h : PieceInv M P Hs σ) (x : SDart (pdarts M P Hs)) :
    (pmap h).tail x = Quotient.mk _ x := rfl

@[simp] lemma pmap_rev (h : PieceInv M P Hs σ) (x : SDart (pdarts M P Hs)) :
    ((pmap h).rev x).1 = M.rev x.1 := rfl

variable (M) in
/-- The image of a set of vertices of `M` among the vertices of a submap. -/
noncomputable def vimg (σ : Perm D) (B : Finset D) (X : Finset V) : Finset (SVert σ B) := by
  classical exact (univ.filter fun x : SDart B => M.tail x.1 ∈ X).image (Quotient.mk _)

lemma mem_vimg {B : Finset D} {X : Finset V} {w : SVert σ B} :
    w ∈ vimg M σ B X ↔ ∃ x : SDart B, M.tail x.1 ∈ X ∧ Quotient.mk _ x = w := by
  classical simp [vimg]

lemma mk_mem_vimg (h : PieceInv M P Hs σ) {X : Finset V} {x : SDart (pdarts M P Hs)} :
    Quotient.mk _ x ∈ vimg M σ (pdarts M P Hs) X ↔
      ∃ y ∈ pdarts M P Hs, M.tail y ∈ X ∧ HRel Hs (M.tail y) (M.tail x.1) := by
  rw [mem_vimg]
  constructor
  · rintro ⟨y, hy, e⟩
    exact ⟨y.1, y.2, hy, (h.vert _ y.2 _ x.2).1 (Quotient.exact e)⟩
  · rintro ⟨y, hyB, hy, e⟩
    exact ⟨⟨y, hyB⟩, hy, Quotient.sound ((h.vert _ hyB _ x.2).2 e)⟩

/-- Off the holes, the image of a set is the set itself. -/
lemma mk_mem_vimg_iff (h : PieceInv M P Hs σ) {X : Finset V} (hX : Disjoint X (hunion Hs))
    {x : SDart (pdarts M P Hs)} :
    Quotient.mk _ x ∈ vimg M σ (pdarts M P Hs) X ↔ M.tail x.1 ∈ X := by
  rw [mk_mem_vimg h]
  constructor
  · rintro ⟨y, -, hy, e⟩
    rwa [(hRel_of_not_mem (disjoint_left.1 hX hy)).1 e]
  · intro hx; exact ⟨x.1, x.2, hx, Or.inl rfl⟩

lemma mk_mem_vimg_hunion (h : PieceInv M P Hs σ) {Hs' : List (Finset V)}
    (hHs : ∀ H ∈ Hs, H ⊆ hunion Hs') {x : SDart (pdarts M P Hs)} :
    Quotient.mk _ x ∈ vimg M σ (pdarts M P Hs) (hunion Hs') ↔ M.tail x.1 ∈ hunion Hs' := by
  rw [mk_mem_vimg h]
  constructor
  · rintro ⟨y, -, hy, e | ⟨H, hH, -, hx⟩⟩
    · rwa [← e]
    · exact hHs H hH hx
  · intro hx; exact ⟨x.1, x.2, hx, Or.inl rfl⟩

lemma vimg_mono {B : Finset D} {X Y : Finset V} (hXY : X ⊆ Y) :
    vimg M σ B X ⊆ vimg M σ B Y := fun w hw => by
  obtain ⟨x, hx, e⟩ := mem_vimg.1 hw; exact mem_vimg.2 ⟨x, hXY hx, e⟩

lemma vimg_union {B : Finset D} (X Y : Finset V) :
    vimg M σ B (X ∪ Y) = vimg M σ B X ∪ vimg M σ B Y := by
  ext w; simp only [mem_union, mem_vimg]
  constructor
  · rintro ⟨x, hx | hx, e⟩
    · exact Or.inl ⟨x, hx, e⟩
    · exact Or.inr ⟨x, hx, e⟩
  · rintro (⟨x, hx, e⟩ | ⟨x, hx, e⟩)
    · exact ⟨x, Or.inl hx, e⟩
    · exact ⟨x, Or.inr hx, e⟩

/-- Images of disjoint sets, one of them off the holes, are disjoint. -/
lemma disjoint_vimg (h : PieceInv M P Hs σ) {X Y : Finset V} (hXY : Disjoint X Y)
    (hX : Disjoint X (hunion Hs)) :
    Disjoint (vimg M σ (pdarts M P Hs) X) (vimg M σ (pdarts M P Hs) Y) := by
  rw [disjoint_left]
  intro w hw hw'
  obtain ⟨x, hx, rfl⟩ := mem_vimg.1 hw
  rw [mk_mem_vimg_iff h hX] at hw
  obtain ⟨y, hyB, hy, e⟩ := (mk_mem_vimg h).1 hw'
  rcases e with e | ⟨H, hH, h1, -⟩
  · exact disjoint_left.1 hXY hw (e ▸ hy)
  · obtain ⟨y', hy'B, hy', e'⟩ := (mk_mem_vimg h).1 hw'
    rcases e' with e' | ⟨H', hH', -, h2⟩
    · exact disjoint_left.1 hXY hw (e' ▸ hy')
    · exact disjoint_left.1 hX hw (subset_hunion hH' h2)

variable (M) in
/-- **The holes of a piece map**: the images of the holes it touches, one vertex each. -/
noncomputable def pholes (σ : Perm D) (B : Finset D) (Hs : List (Finset V)) :
    List (Finset (SVert σ B)) :=
  (Hs.map (vimg M σ B)).filter fun H => H.Nonempty

lemma hunion_pholes {B : Finset D} (Hs : List (Finset V)) :
    hunion (pholes M σ B Hs) = vimg M σ B (hunion Hs) := by
  induction Hs with
  | nil =>
    ext w; simp [pholes, hunion, mem_vimg]
  | cons H Hs ih =>
    simp only [pholes, List.map_cons, List.filter_cons] at ih ⊢
    rw [show hunion (H :: Hs) = H ∪ hunion Hs from rfl, vimg_union]
    split_ifs with hne
    · rw [show hunion (vimg M σ B H :: List.filter (fun H => decide H.Nonempty)
        (List.map (vimg M σ B) Hs)) = vimg M σ B H ∪ hunion (List.filter
          (fun H => decide H.Nonempty) (List.map (vimg M σ B) Hs)) from rfl, ih]
    · rw [ih]
      simp only [decide_eq_true_eq, not_nonempty_iff_eq_empty] at hne
      rw [hne, empty_union]

/-- A piece map has one vertex for each hole it touches. -/
lemma pholes_singleton (h : PieceInv M P Hs σ) {H : Finset (SVert σ (pdarts M P Hs))}
    (hH : H ∈ pholes M σ (pdarts M P Hs) Hs) : ∃ w, H = {w} := by
  simp only [pholes, List.mem_filter, List.mem_map, decide_eq_true_eq] at hH
  obtain ⟨⟨H₀, hH₀, rfl⟩, ⟨w, hw⟩⟩ := hH
  refine ⟨w, eq_singleton_iff_unique_mem.2 ⟨hw, fun w' hw' => ?_⟩⟩
  obtain ⟨x, hx, rfl⟩ := mem_vimg.1 hw
  obtain ⟨x', hx', rfl⟩ := mem_vimg.1 hw'
  exact Quotient.sound ((h.vert _ x'.2 _ x.2).2 (Or.inr ⟨H₀, hH₀, hx', hx⟩))

/-! ### Paths in a piece map -/

/-- **A one-vertex path.** -/
def SPath.point {D' V' F' : Type*} {M' : CombMap D' V' F'} (x : D') (w : V') : SPath M' where
  k := 0
  d _ := x
  p _ := w
  tail_d j hj := absurd hj (Nat.not_lt_zero _)
  head_d j hj := absurd hj (Nat.not_lt_zero _)
  inj i hi j hj _ := by omega

lemma SPath.point_verts {D' V' F' : Type*} [DecidableEq V'] {M' : CombMap D' V' F'} (x : D')
    (w : V') : (SPath.point (M' := M') x w).verts = {w} := by
  ext v; simp [SPath.verts, SPath.init, SPath.point, eq_comm]

/-- Every hole of a piece map is the vertex set of a one-vertex path. -/
lemma pholes_path (h : PieceInv M P Hs σ) {H : Finset (SVert σ (pdarts M P Hs))}
    (hH : H ∈ pholes M σ (pdarts M P Hs) Hs) : ∃ πH : SPath (pmap h), πH.verts = H := by
  obtain ⟨w, rfl⟩ := pholes_singleton h hH
  exact ⟨SPath.point w.out w, SPath.point_verts _ _⟩

variable (h : PieceInv M P Hs σ) (π : SPath M) (x₀ : SDart (pdarts M P Hs))
  (hx₀ : M.tail x₀.1 = π.p π.k)
  (hπ : ∀ e ∈ π.darts, e ∈ pdarts M P Hs) (hav : Disjoint π.verts (hunion Hs))

/-- A dart of the separator, as a dart of the piece map (`x₀` past the end of the path). -/
def SPath.pdart (j : ℕ) : SDart (pdarts M P Hs) :=
  if hj : j < π.k then ⟨π.d j, hπ _ (π.d_mem j hj)⟩ else x₀

lemma SPath.pdart_of_lt {j : ℕ} (hj : j < π.k) : (π.pdart x₀ hπ j).1 = π.d j := by
  simp [SPath.pdart, hj]

/-- Every vertex of the separator is the tail of a dart of the piece map: of the dart `d j`, or,
for the last vertex, of the dart `x₀`. -/
lemma SPath.tail_pdart {j : ℕ} (hj : j ≤ π.k) (hx₀ : M.tail x₀.1 = π.p π.k) :
    M.tail (π.pdart x₀ hπ j).1 = π.p j := by
  by_cases hj' : j < π.k
  · rw [π.pdart_of_lt x₀ hπ hj']; exact π.tail_d j hj'
  · obtain rfl : j = π.k := by omega
    simp only [SPath.pdart, lt_irrefl, dite_false]; exact hx₀

include hx₀ hav in
/-- **The separator, as a simple path of the piece map**, from a dart `x₀` of the piece map at its
last vertex (the reverse of its last dart, or, for a path of one vertex, any dart at it). -/
noncomputable def SPath.toPiece : SPath (pmap h) where
  k := π.k
  d := π.pdart x₀ hπ
  p j := Quotient.mk _ (π.pdart x₀ hπ j)
  tail_d j hj := rfl
  head_d j hj := by
    show Quotient.mk _ ((pmap h).rev (π.pdart x₀ hπ j)) = _
    apply Quotient.sound
    show σ.SameCycle (M.rev (π.pdart x₀ hπ j).1) (π.pdart x₀ hπ (j + 1)).1
    refine (h.vert _ (hπ _ (by rw [π.pdart_of_lt x₀ hπ hj]; exact π.rev_d_mem j hj)) _
      (π.pdart x₀ hπ (j + 1)).2).2 (Or.inl ?_)
    rw [π.pdart_of_lt x₀ hπ hj, tail_rev, π.head_d j hj, π.tail_pdart x₀ hπ (by omega) hx₀]
  inj i hi j hj e := by
    have := (h.vert _ (π.pdart x₀ hπ i).2 _ (π.pdart x₀ hπ j).2).1 (Quotient.exact e)
    rw [π.tail_pdart x₀ hπ hi hx₀, π.tail_pdart x₀ hπ hj hx₀,
      hRel_of_not_mem (disjoint_left.1 hav (π.p_mem_init hi))] at this
    exact π.inj i hi j hj this.symm

lemma SPath.toPiece_k : (π.toPiece h x₀ hx₀ hπ hav).k = π.k := rfl

/-- **The vertices of the transported separator** are the images of its vertices. -/
lemma SPath.toPiece_verts :
    (π.toPiece h x₀ hx₀ hπ hav).verts = vimg M σ (pdarts M P Hs) π.verts := by
  ext w
  rw [mem_vimg, SPath.verts, SPath.mem_init]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨π.pdart x₀ hπ t, by rw [π.tail_pdart x₀ hπ ht hx₀]; exact π.p_mem_init ht, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, e⟩ := π.mem_init.1 hx
    refine ⟨t, ht, Quotient.sound ((h.vert _ (π.pdart x₀ hπ t).2 _ x.2).2 (Or.inl ?_))⟩
    rw [π.tail_pdart x₀ hπ ht hx₀, e]

end Piece

/-! ### The parts of a separator in a piece map -/

section Parts

variable {P : Finset D} {Hs : List (Finset V)} {σ : Perm D}

lemma vimg_empty {B : Finset D} : vimg M σ B (∅ : Finset V) = ∅ := by
  ext w; simp [mem_vimg]

lemma vimg_hunion {B : Finset D} (L : List (Finset V)) :
    vimg M σ B (hunion L) = hunion (L.map (vimg M σ B)) := by
  induction L with
  | nil => exact vimg_empty
  | cons H L ih => rw [hunion_cons, vimg_union, ih, List.map_cons, hunion_cons]

variable (M) in
/-- **A part of a separator in a piece map**: it ends at the tail of a dart of the piece map, its
darts are darts of the piece map, and it avoids the holes. -/
def SegIn (P : Finset D) (Hs : List (Finset V)) (π : SPath M) : Prop :=
  (∃ x : SDart (pdarts M P Hs), M.tail x.1 = π.p π.k) ∧ (∀ e ∈ π.darts, e ∈ pdarts M P Hs) ∧
    Disjoint π.verts (hunion Hs)

/-- **The parts of a separator, as simple paths of the piece map** (`SPath.toPiece`). -/
noncomputable def segsP (h : PieceInv M P Hs σ) :
    (L : List (SPath M)) → (∀ π ∈ L, SegIn M P Hs π) → List (SPath (pmap h))
  | [], _ => []
  | π :: L, hL =>
    π.toPiece h (hL π (List.mem_cons_self ..)).1.choose
      (hL π (List.mem_cons_self ..)).1.choose_spec (hL π (List.mem_cons_self ..)).2.1
      (hL π (List.mem_cons_self ..)).2.2 ::
      segsP h L fun π' h' => hL π' (List.mem_cons_of_mem _ h')

lemma segsP_verts (h : PieceInv M P Hs σ) :
    ∀ (L : List (SPath M)) (hL : ∀ π ∈ L, SegIn M P Hs π),
      (segsP h L hL).map SPath.verts = L.map fun π => vimg M σ (pdarts M P Hs) π.verts
  | [], _ => rfl
  | π :: L, hL => by
    rw [segsP, List.map_cons, List.map_cons, SPath.toPiece_verts, segsP_verts h L]

lemma segsP_k (h : PieceInv M P Hs σ) :
    ∀ (L : List (SPath M)) (hL : ∀ π ∈ L, SegIn M P Hs π),
      (segsP h L hL).map SPath.k = L.map SPath.k
  | [], _ => rfl
  | π :: L, hL => by
    rw [segsP, List.map_cons, List.map_cons, SPath.toPiece_k, segsP_k h L]

end Parts

/-! ### From a child piece map to its parent -/

section Child

variable {P Pc : Finset D} {Hs Hs' : List (Finset V)} {σ σc : Perm D}
  (h : PieceInv M P Hs σ) (hc : PieceInv M Pc Hs' σc)
  (hsub : pdarts M Pc Hs' ⊆ pdarts M P Hs) (hHs : ∀ a b, HRel Hs a b → HRel Hs' a b)

/-- **The embedding of a child piece map into its parent**: the darts of the child are darts of
the parent; a vertex of the parent goes to the vertex of the child containing its darts. -/
noncomputable def childEmb (x₀ : SDart (pdarts M Pc Hs')) : Emb (pmap hc) (pmap h) where
  e x := ⟨x.1, hsub x.2⟩
  inj x y e := Subtype.ext (by simpa using congrArg Subtype.val e)
  rev _ := rfl
  φ w := by
    classical
    exact if hw : ∃ x : SDart (pdarts M Pc Hs'),
        Quotient.mk (orbSetoid σ (pdarts M P Hs)) ⟨x.1, hsub x.2⟩ = w
      then Quotient.mk _ hw.choose else Quotient.mk _ x₀
  tail x := by
    classical
    have hw : ∃ y : SDart (pdarts M Pc Hs'),
        Quotient.mk (orbSetoid σ (pdarts M P Hs)) ⟨y.1, hsub y.2⟩ = (pmap h).tail ⟨x.1, hsub x.2⟩ :=
      ⟨x, rfl⟩
    simp only [hw, dite_true]
    apply Quotient.sound
    exact (hc.vert _ hw.choose.2 _ x.2).2 (hHs _ _ ((h.vert _ (hsub hw.choose.2) _ (hsub x.2)).1
      (Quotient.exact hw.choose_spec)))

lemma childEmb_e (x₀ : SDart (pdarts M Pc Hs')) (x : SDart (pdarts M Pc Hs')) :
    ((childEmb h hc hsub hHs x₀).e x).1 = x.1 := rfl

lemma childEmb_ext_cap (x₀ : SDart (pdarts M Pc Hs')) (u : D → ℤ) :
    (childEmb h hc hsub hHs x₀).ext (fun x => u x.1) =
      capOn (fun x : SDart (pdarts M P Hs) => u x.1)
        (univ.filter fun x => x.1 ∈ pdarts M Pc Hs') := by
  classical
  funext x
  by_cases hx : x.1 ∈ pdarts M Pc Hs'
  · have : x = (childEmb h hc hsub hHs x₀).e ⟨x.1, hx⟩ := rfl
    conv_lhs => rw [this]
    rw [Emb.ext_apply]
    simp [capOn, hx]
  · rw [Emb.ext_of_not_mem _ _ fun y e => hx (by rw [← e]; exact y.2)]
    simp [capOn, hx]

lemma childEmb_ext_eq (x₀ : SDart (pdarts M Pc Hs')) (g : SDart (pdarts M Pc Hs') → ℤ) :
    (childEmb h hc hsub hHs x₀).ext g =
      fun x => if hx : x.1 ∈ pdarts M Pc Hs' then g ⟨x.1, hx⟩ else 0 := by
  funext x
  by_cases hx : x.1 ∈ pdarts M Pc Hs'
  · have : x = (childEmb h hc hsub hHs x₀).e ⟨x.1, hx⟩ := rfl
    conv_lhs => rw [this]
    rw [Emb.ext_apply]; simp [hx]
  · rw [Emb.ext_of_not_mem _ _ fun y e => hx (by rw [← e]; exact y.2)]; simp [hx]

/-- **The output of the recursion on a child piece map is an output on its parent**, with the
capacities of the child, the holes of the child (the separator contracted in the child is a set
of vertices of the parent). -/
theorem msOut_child (x₀ : SDart (pdarts M Pc Hs')) {u : D → ℤ} {S T : Finset V}
    (hS : Disjoint S (hunion Hs')) (hT : Disjoint T (hunion Hs')) (hST : Disjoint S T)
    (hsubH : ∀ H ∈ Hs, H ⊆ hunion Hs')
    (hmerge : ∀ a b, HRel Hs' a b → HRel Hs a b ∨ (a ∈ hunion Hs' ∧ b ∈ hunion Hs'))
    {g : SDart (pdarts M Pc Hs') → ℤ}
    (hg : MSOut (pmap hc) (fun x => u x.1) (vimg M σc (pdarts M Pc Hs') S)
      (vimg M σc (pdarts M Pc Hs') T) (vimg M σc (pdarts M Pc Hs') (hunion Hs')) g) :
    MSOut (pmap h)
      (capOn (fun x : SDart (pdarts M P Hs) => u x.1) (univ.filter fun x => x.1 ∈ pdarts M Pc Hs'))
      (vimg M σ (pdarts M P Hs) S) (vimg M σ (pdarts M P Hs) T)
      (vimg M σ (pdarts M P Hs) (hunion Hs')) ((childEmb h hc hsub hHs x₀).ext g) := by
  set E := childEmb h hc hsub hHs x₀
  rw [← childEmb_ext_cap h hc hsub hHs x₀ u]
  have hsubU : hunion Hs ⊆ hunion Hs' := fun v hv => by
    obtain ⟨H, hH, hv⟩ := mem_hunion.1 hv; exact hsubH H hH hv
  have hS0 := disjoint_of_subset_right hsubU hS
  have hT0 := disjoint_of_subset_right hsubU hT
  have iS : ∀ x, (pmap h).tail (E.e x) ∈ vimg M σ _ S ↔ M.tail x.1 ∈ S := fun x =>
    mk_mem_vimg_iff h hS0
  have iS' : ∀ x, (pmap hc).tail x ∈ vimg M σc _ S ↔ M.tail x.1 ∈ S := fun x =>
    mk_mem_vimg_iff hc hS
  have iT : ∀ x, (pmap h).tail (E.e x) ∈ vimg M σ _ T ↔ M.tail x.1 ∈ T := fun x =>
    mk_mem_vimg_iff h hT0
  have iT' : ∀ x, (pmap hc).tail x ∈ vimg M σc _ T ↔ M.tail x.1 ∈ T := fun x =>
    mk_mem_vimg_iff hc hT
  have iA : ∀ x, (pmap h).tail (E.e x) ∈ vimg M σ _ (hunion Hs') ↔ M.tail x.1 ∈ hunion Hs' :=
    fun x => mk_mem_vimg_hunion h hsubH
  have iA' : ∀ x, (pmap hc).tail x ∈ vimg M σc _ (hunion Hs') ↔ M.tail x.1 ∈ hunion Hs' :=
    fun x => mk_mem_vimg_hunion hc fun _ hH => subset_hunion hH
  refine E.msOut_transfer hg ?_ ?_ ?_ ?_ (disjoint_vimg h hST hS0) (disjoint_vimg h hS hS0)
    (disjoint_vimg h hT hT0).symm
  · rintro w h1 h2 h3 ⟨x, rfl⟩
    rw [E.tail]
    refine ⟨fun hc' => h1 ((iS x).2 ((iS' x).1 hc')), fun hc' => h2 ((iT x).2 ((iT' x).1 hc')),
      fun hc' => h3 ((iA x).2 ((iA' x).1 hc')), fun y hy => ?_⟩
    rw [E.tail] at hy
    have := (hc.vert _ y.2 _ x.2).1 (Quotient.exact hy)
    rcases hmerge _ _ this with e | ⟨-, hx⟩
    · exact Quotient.sound ((h.vert _ (hsub y.2) _ (hsub x.2)).2 e)
    · exact absurd ((iA x).2 hx) h3
  · rintro w hw ⟨x, rfl⟩; rw [E.tail]; exact (iS' x).2 ((iS x).1 hw)
  · rintro w hw ⟨x, rfl⟩; rw [E.tail]; exact (iT' x).2 ((iT x).1 hw)
  · rintro w hw ⟨x, rfl⟩; rw [E.tail]; exact (iA' x).2 ((iA x).1 hw)

end Child

/-! ### From the piece map of the whole map to the map -/

section Root

variable {P : Finset D} {σ : Perm D} (h0 : PieceInv M P [] σ) (hP : ∀ d, d ∈ P)
  (x₀ : SDart (pdarts M P []))

include hP in
lemma mem_pdarts_nil (d : D) : d ∈ pdarts M P [] := by
  rw [mem_pdarts]; exact ⟨hP d, fun ⟨H, hH, _⟩ => by simp at hH⟩

/-- **The embedding of the piece map of the whole map into the map.** -/
noncomputable def rootEmb : Emb (pmap h0) M where
  e x := x.1
  inj _ _ e := Subtype.ext e
  rev _ := rfl
  φ v := by
    classical
    exact if hv : ∃ x : SDart (pdarts M P []), M.tail x.1 = v then Quotient.mk _ hv.choose
      else Quotient.mk _ x₀
  tail x := by
    classical
    have hv : ∃ y : SDart (pdarts M P []), M.tail y.1 = M.tail x.1 := ⟨x, rfl⟩
    simp only [hv, dite_true]
    exact Quotient.sound ((h0.vert _ hv.choose.2 _ x.2).2 (Or.inl hv.choose_spec))

include hP in
lemma rootEmb_ext_cap (u : D → ℤ) : (rootEmb h0 x₀).ext (fun x => u x.1) = u := by
  funext d
  exact (rootEmb h0 x₀).ext_apply _ ⟨d, mem_pdarts_nil hP d⟩

include hP in
/-- **The output of the recursion on the piece map of the whole map is an output on the map.** -/
theorem msOut_root {u : D → ℤ} {S T : Finset V} (hST : Disjoint S T)
    {g : SDart (pdarts M P []) → ℤ}
    (hg : MSOut (pmap h0) (fun x => u x.1) (vimg M σ (pdarts M P []) S)
      (vimg M σ (pdarts M P []) T) (vimg M σ (pdarts M P []) (hunion [])) g) :
    MSOut M u S T ∅ ((rootEmb h0 x₀).ext g) := by
  set E := rootEmb h0 x₀
  rw [← rootEmb_ext_cap h0 hP x₀ u]
  have e0 : hunion ([] : List (Finset V)) = ∅ := rfl
  have iS : ∀ x, (pmap h0).tail x ∈ vimg M σ _ S ↔ M.tail x.1 ∈ S := fun x =>
    mk_mem_vimg_iff h0 (by rw [e0]; exact disjoint_empty_right _)
  have iT : ∀ x, (pmap h0).tail x ∈ vimg M σ _ T ↔ M.tail x.1 ∈ T := fun x =>
    mk_mem_vimg_iff h0 (by rw [e0]; exact disjoint_empty_right _)
  have iA : ∀ w, w ∉ vimg M σ (pdarts M P []) (hunion []) := fun w hw => by
    obtain ⟨x, hx, -⟩ := mem_vimg.1 hw; rw [e0] at hx; simp at hx
  refine E.msOut_transfer hg ?_ ?_ ?_ ?_ hST (disjoint_empty_right _) (disjoint_empty_left _)
  · rintro w h1 h2 - ⟨x, rfl⟩
    rw [E.tail]
    refine ⟨fun hc => h1 ((iS x).1 hc), fun hc => h2 ((iT x).1 hc), iA _, fun y hy => ?_⟩
    rw [E.tail] at hy
    rcases (h0.vert _ y.2 _ x.2).1 (Quotient.exact hy) with e | ⟨H, hH, -⟩
    · exact e
    · simp at hH
  · rintro w hw ⟨x, rfl⟩; rw [E.tail]; exact (iS x).2 hw
  · rintro w hw ⟨x, rfl⟩; rw [E.tail]; exact (iT x).2 hw
  · intro w hw; simp at hw

end Root

/-- An output of the recursion on the whole map with no holes is a maximum flow. -/
theorem MSOut.isMax {u f : D → ℤ} {S T : Finset V} (h : MSOut M u S T ∅ f) :
    IsMax M u S T f := by
  obtain ⟨Y, hY1, hY2, hY3⟩ := h.st
  have hflow : IsFlow M u S T f := ⟨h.pseudo, fun v hS hT => h.cons v hS hT (notMem_empty v)⟩
  refine ⟨hflow, fun g hg => ?_⟩
  rw [val_eq_sum hflow hY1 hY2, (tight_iff_closed h.pseudo Y).2 hY3]
  exact val_le_cutCap hg hY1 hY2

end BKMNW

end PlanarFlow
