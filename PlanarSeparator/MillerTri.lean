module

public import PlanarSeparator.MillerBand
public import PlanarSeparator.Separator
public import PlanarSeparator.Stellar

/-!
# Miller's simple cycle separator theorem for triangulations

Let `M` be a plane map with `n` vertices, all of whose faces are triangles, and `w ≥ 0` weights
on its vertices of total at most `1`. Then `M` has a simple cycle of at most `6 √n + 4` darts
bounding a set of faces `Z`, such that the vertices strictly inside (those off the cycle with
their faces in `Z`) and strictly outside weigh at most `2/3` each
(`PlanarSeparator.Map.exists_short_cycle_separator`). This is the triangulated case of
G. L. Miller, *Finding small simple cycle separators for 2-connected planar graphs*, J. Comput.
Syst. Sci. 32 (1986), 265–279.

## The proof

Take a breadth-first tree from any root. A level `l` is *heavy* if some component of the faces
avoiding the levels `< l` has a strict inside of weight `> 2/3`; heavy levels form an initial
segment, ending at `l*`. With `t = ⌊√n⌋`, choose a level `l₀ ∈ [l* - t, l*]` with at most `t`
vertices (or `l₀ = 0` if `l* ≤ t`) and a level `l₂ ∈ [l* + 1, l* + t + 1]` with at most `t`
vertices. The heavy component at level `l₀` is bounded by a simple cycle at level `l₀`
(`PlanarSeparator.Map.IsPlane.exists_scycle_comp`); redirecting the tree along this cycle gives
an inner region (`PlanarSeparator.Map.Inner`) for the band theorem
(`PlanarSeparator.Map.exists_band_separator`), which gives a cycle of at most
`2 (2 t + 1) + t + t` darts.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

open Finset

namespace Map

variable {D P : Type*} {M : Map D P} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-! ### The inner region at level `0` -/

lemma ins_univ : ins (univ : Finset M.Face) = (univ : Finset P) := by
  ext v
  simp [mem_ins]

/-- With no inner cycle: all faces, the root, and the tree itself. -/
theorem inner_univ (hM : M.IsPlane) {T : M.SpTree} (hT : IsBFS T) {w : P → ℝ}
    (hheavy : 2 / 3 < ∑ v, w v) : Inner T w 0 univ {T.root} T.root T where
  conn := fConn_univ hM
  heavy := by rwa [ins_univ]
  closed _ _ _ := mem_univ _
  touch d _ _ := by rw [ins_univ]; exact mem_univ _
  touch0 d _ h := mem_singleton.2 (hT.eq_root_of_height (by omega))
  insLv v _ := by
    by_cases h : T.height v = 0
    · exact Or.inr (mem_singleton.2 (hT.eq_root_of_height h))
    · exact Or.inl (by omega)
  root₁ := rfl
  bfs₁ v h _ := hT.parent v h
  height₁ := ⟨0, fun v _ => by ring⟩
  K₀lv v hv := by rw [mem_singleton.1 hv, hT.root]
  c₀mem := mem_singleton_self _
  band u _ := by
    refine ⟨T.root_mem_anc u, fun v hv hvr => Or.inl ⟨by rw [ins_univ]; exact mem_univ _, ?_,
      T.height_le_of_mem_anc hv⟩⟩
    by_contra h
    exact hvr (by
      rw [hT.eq_root_of_height (v := v) (by omega), T.anc_root]
      exact mem_singleton_self _)
  bad δ _ h := by simp at h

/-! ### The inner region at a level `l₀ ≥ 1` -/

/-- **The inner region of a heavy component, from its boundary cycle.** For a component `H` at a
level `l₀ ≥ 1` and any simple cycle `C` bounding it, the tree redirected along `C` from its first
dart (`PlanarSeparator.Map.SpTree.arcTree`) makes an inner region with `K₀` the vertices of `C`
and `c₀` the vertex of its first dart. -/
theorem inner_of_scycle (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ) {T : M.SpTree}
    (hT : IsBFS T) {w : P → ℝ} {l₀ : ℕ} (hl0 : 1 ≤ l₀) {f : M.Face}
    (hheavy : 2 / 3 < ∑ v ∈ ins (M.comp (T.low l₀) f), w v) (C : M.SCycle)
    (hC : ∀ d, (M.face d ∈ M.comp (T.low l₀) f ↔ M.face (M.α d) ∈ M.comp (T.low l₀) f) ↔
      ¬ C.Mem d) :
    ∃ (hr : T.root ∉ C.verts)
      (hCh : ∀ i < C.k, T.height (M.vert (C.d i)) = T.height (M.vert (C.d 0))),
      Inner T w l₀ (M.comp (T.low l₀) f) C.verts (M.vert (C.d 0))
        (T.arcTree C 0 (C.k - 1) C.pos hr hCh) ∧ C.verts ⊆ T.lvl l₀ := by
  classical
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (htri d).φ_three
  set H := M.comp (T.low l₀) f with hHdef
  have hlevC : ∀ v ∈ C.verts, T.height v = l₀ := fun v hv => level_of_mem_verts hT h3 hC hv
  have hk : 0 < C.k := C.pos
  have hr : T.root ∉ C.verts := fun h => by
    have := hlevC _ h
    rw [hT.root] at this
    omega
  have hCh : ∀ i < C.k, T.height (M.vert (C.d i)) = T.height (M.vert (C.d 0)) := fun i hi => by
    rw [hlevC _ (C.mem_verts.2 ⟨i, hi, rfl⟩), hlevC _ (C.mem_verts.2 ⟨0, hk, rfl⟩)]
  set T₁ := T.arcTree C 0 (C.k - 1) hk hr hCh with hT₁
  set c₀ := M.vert (C.d 0) with hc₀
  have hinsC : ∀ v ∈ ins H, v ∉ C.verts := fun v hv hvC => by
    have := lt_of_mem_ins hM hT hl0 hv
    rw [hlevC v hvC] at this
    omega
  have hR : ∀ v, v ∈ C.arcR 0 (C.k - 1) ↔ v ∈ C.verts ∧ v ≠ c₀ := by
    intro v
    rw [C.mem_arcR]
    constructor
    · rintro ⟨hv, h1, -⟩
      refine ⟨hv, fun h => ?_⟩
      rw [h, C.idx_vert hk] at h1
      unfold SCycle.off at h1
      simp at h1
    · rintro ⟨hv, hne⟩
      obtain ⟨hi, he⟩ := C.idx_spec hv
      refine ⟨hv, ?_, ?_⟩ <;> unfold SCycle.off <;> simp only [Nat.zero_le, ↓reduceIte,
        Nat.sub_zero]
      · by_contra h0
        apply hne
        rw [← he, show C.idx v = 0 by omega]
      · omega
  have hroot₁ : T₁.root = T.root := rfl
  have hpar_out : ∀ v (h : v ≠ T₁.root), v ∉ C.verts → T₁.par v h = T.par v h := by
    intro v h hv
    show (T.arcTree C 0 (C.k - 1) hk hr hCh).par v h = _
    unfold SpTree.arcTree
    exact T.redirect_par_of_notMem h (fun h' => hv ((hR v).1 h').1)
  have hparent_out : ∀ v, v ∉ C.verts → T₁.parent v = T.parent v := by
    intro v hv
    show (T.arcTree C 0 (C.k - 1) hk hr hCh).parent v = _
    unfold SpTree.arcTree
    exact T.redirect_parent_of_notMem (fun h' => hv ((hR v).1 h').1)
  have hparent_in : ∀ v, v ∈ C.verts → v ≠ c₀ → T₁.parent v ∈ C.verts := by
    intro v hv hne
    show (T.arcTree C 0 (C.k - 1) hk hr hCh).parent v ∈ _
    unfold SpTree.arcTree
    rw [T.redirect_parent_of_mem ((hR v).2 ⟨hv, hne⟩), C.vert_α_arcNxt]
    exact C.mem_verts.2 ⟨_, C.pre_lt (C.idx_spec hv).1, rfl⟩
  have hpar_in : ∀ v (h : v ≠ T₁.root), v ∈ C.verts → v ≠ c₀ → C.Mem (T₁.par v h) := by
    intro v h hv hne
    have : T₁.par v h = C.arcNxt v := by
      show (T.arcTree C 0 (C.k - 1) hk hr hCh).par v h = _
      unfold SpTree.arcTree
      exact T.redirect_par_of_mem h ((hR v).2 ⟨hv, hne⟩)
    rw [this, SCycle.arcNxt]
    exact (C.mem_α_iff).2 (C.mem_d (C.pre_lt (C.idx_spec hv).1))
  -- faces at a vertex of level `> l₀` all lie in `H` or all off `H`
  have hall : ∀ v, l₀ < T.height v → v ∉ ins H → ∀ d, M.vert d = v → M.face d ∉ H := by
    intro v hv hvH d hd hdH
    exact hvH (mem_ins_of_lt hT h3 hv hd hdH)
  -- the root paths from off the strict inside of `H` stay off it
  have hpath : ∀ u, u ∉ ins H → ∀ d, T₁.pathC u d ≠ 0 →
      (M.face d ∉ H ∨ M.face (M.α d) ∉ H) ∧ M.vert d ∉ ins H := by
    intro u
    induction u using T₁.induction with
    | hroot =>
      intro _ d hd
      exact absurd (by rw [SpTree.pathC_root]; rfl) hd
    | hstep u hu ih =>
      intro hu' d hd
      have hedge : (M.face (T₁.par u hu) ∉ H ∨ M.face (M.α (T₁.par u hu)) ∉ H) ∧
          T₁.parent u ∉ ins H := by
        by_cases huC : u ∈ C.verts ∧ u ≠ c₀
        · refine ⟨?_, fun h => hinsC _ h (hparent_in u huC.1 huC.2)⟩
          have := (hC _).not.2 (not_not.2 (hpar_in u hu huC.1 huC.2))
          by_contra h
          push Not at h
          exact this (iff_of_true h.1 h.2)
        · have hpo : T₁.par u hu = T.par u hu := by
            show (T.arcTree C 0 (C.k - 1) hk hr hCh).par u hu = _
            unfold SpTree.arcTree
            exact T.redirect_par_of_notMem hu (fun h' => huC ((hR u).1 h'))
          have hpp : T₁.parent u = T.parent u := by
            show (T.arcTree C 0 (C.k - 1) hk hr hCh).parent u = _
            unfold SpTree.arcTree
            exact T.redirect_parent_of_notMem (fun h' => huC ((hR u).1 h'))
          rw [hpo, hpp, T.parent_of_ne hu]
          have hfaces : M.face (T.par u hu) ∉ H ∧ M.face (M.α (T.par u hu)) ∉ H := by
            by_cases hlu : T.height u ≤ l₀
            · have hp := hT.parent u hu
              have := zone_of_end (T := T) (l := l₀) (d := T.par u hu) (Or.inr (by omega))
              exact ⟨fun h => (mem_comp.1 h).1 this.1, fun h => (mem_comp.1 h).1 this.2⟩
            · push Not at hlu
              refine ⟨hall u hlu hu' _ (T.vert_par u hu), ?_⟩
              rw [← face_σ]
              exact hall u hlu hu' _ (by rw [M.vert_σ]; exact T.vert_par u hu)
          exact ⟨Or.inl hfaces.1, fun h => hfaces.2 (mem_ins.1 h _ rfl)⟩
      rw [SpTree.pathC_of_ne _ hu, Pi.add_apply] at hd
      by_cases h1 : M.edgeInd (T₁.par u hu) d = 0
      · rw [h1, zero_add] at hd
        exact ih hedge.2 d hd
      · rcases edgeInd_ne_zero h1 with rfl | rfl
        · exact ⟨hedge.1, by rw [T₁.vert_par]; exact hu'⟩
        · refine ⟨by rw [M.α_α]; exact hedge.1.symm, ?_⟩
          rw [← T₁.parent_of_ne hu]
          exact hedge.2
  refine ⟨hr, hCh, ⟨comp_fConn _ _, hheavy, fun d h1 h2 => mem_comp_of_adj h1 h2,
    fun d hd hl => mem_ins_of_lt hT h3 hl rfl hd, fun d hd hl => ?_, fun v hv => ?_, hroot₁,
    fun v h hl => ?_, ⟨C.k, fun v hv => ?_⟩, fun v hv => (hlevC v hv).le,
    C.mem_verts.2 ⟨0, hk, rfl⟩, fun u => ?_, fun δ hδ hbad => ?_⟩,
    fun v hv => SpTree.mem_lvl.2 (hlevC v hv)⟩
  · -- touch0: a vertex of level `≤ l₀` touching `H` lies on the cycle
    have hnz := (mem_comp.1 hd).1
    rw [notMem_zone_iff] at hnz
    have h0 := hnz d rfl
    rw [mem_low] at h0
    have hvr : M.vert d ≠ T.root := fun h => by rw [h, hT.root] at h0; omega
    have hp := hT.parent _ hvr
    have hz := zone_of_end (T := T) (l := l₀) (d := T.par _ hvr) (Or.inr (by omega))
    exact mem_verts_of_touch hC (T.vert_par _ hvr).symm hd fun h => (mem_comp.1 h).1 hz.1
  · exact Or.inl (lt_of_mem_ins hM hT hl0 hv)
  · have hv : v ∉ C.verts := fun h' => by rw [hlevC v h'] at hl; omega
    rw [hpar_out v h hv]
    exact hT.parent v h
  · have hv' : v ∉ C.arcR 0 (C.k - 1) := fun h' => by
      rw [hlevC v ((hR v).1 h').1] at hv
      omega
    show (T.arcTree C 0 (C.k - 1) hk hr hCh).height v = _
    unfold SpTree.arcTree
    rw [SpTree.redirect_height]
    simp [SCycle.arcPos, hv']
  · -- the root paths through the band
    induction u using T₁.induction with
    | hroot =>
      intro hu
      exfalso
      rcases hu with hu | hu
      · have := lt_of_mem_ins hM hT hl0 hu
        rw [hroot₁, hT.root] at this
        omega
      · exact hr (by rw [← hroot₁]; exact hu)
    | hstep u hu ih =>
      intro hmem
      by_cases huc : u = c₀
      · rw [huc]
        exact ⟨T₁.mem_anc_self _, fun v hv hv' => absurd hv hv'⟩
      have hp : (T₁.parent u ∈ ins H ∨ T₁.parent u ∈ C.verts) ∧
          T.height (T₁.parent u) ≤ T.height u := by
        rcases hmem with hmem | hmem
        · have huC := hinsC u hmem
          rw [hparent_out u huC, T.parent_of_ne hu]
          refine ⟨touch_comp hC (faces_of_mem_ins (d := T.par u hu)
            (by rw [show M.vert (T.par u hu) = u from T.vert_par u hu]; exact hmem)).2, ?_⟩
          have := hT.parent u hu
          omega
        · have hpC := hparent_in u hmem huc
          exact ⟨Or.inr hpC, by rw [hlevC _ hpC, hlevC _ hmem]⟩
      obtain ⟨hc, hrest⟩ := ih hp.1
      refine ⟨by rw [T₁.anc_of_ne hu]; exact mem_insert_of_mem hc, fun v hv hv' => ?_⟩
      rw [T₁.anc_of_ne hu] at hv
      rcases mem_insert.1 hv with rfl | hv
      · rcases hmem with h | h
        · exact Or.inl ⟨h, lt_of_mem_ins hM hT hl0 h, le_rfl⟩
        · exact Or.inr h
      · rcases hrest v hv hv' with ⟨h1, h2, h4⟩ | h
        · exact Or.inl ⟨h1, h2, h4.trans hp.2⟩
        · exact Or.inr h
  · -- a dart with a face off `H`
    have hx : M.vert δ ∉ ins H := fun h => by
      rcases hbad with hb | hb
      · exact hb (mem_ins.1 h δ rfl)
      · exact hb (by rw [← face_σ]; exact mem_ins.1 h _ (M.vert_σ δ))
    have hz : M.vert (M.α δ) ∉ ins H := fun h => by
      rcases hbad with hb | hb
      · exact hb (by
          have := mem_ins.1 h _ (M.vert_σ (M.α δ))
          rwa [face_σ, M.α_α] at this)
      · exact hb (mem_ins.1 h _ rfl)
    have hfund : ∀ d, T₁.fund δ d ≠ 0 →
        (M.face d ∉ H ∨ M.face (M.α d) ∉ H) ∧ M.vert d ∉ ins H := by
      intro d hd
      rw [SpTree.fund_apply, add_assoc] at hd
      by_cases h1 : M.edgeInd δ d = 0
      · rw [h1, zero_add] at hd
        by_cases h2 : T₁.pathC (M.vert δ) d = 0
        · rw [h2, zero_add] at hd
          exact hpath _ hz d hd
        · exact hpath _ hx d h2
      · rcases edgeInd_ne_zero h1 with rfl | rfl
        · exact ⟨hbad, hx⟩
        · rw [M.α_α]
          exact ⟨hbad.symm, hz⟩
    refine ⟨fun v hv hvc => ?_, fun f' hf' g hg => ?_⟩
    · obtain ⟨d, rfl, hd⟩ := T₁.mem_cycV.1 hvc
      exact (hfund d hd).2 hv
    · refine T₁.same_side hM (comp_fConn _ _) (fun d h1 h2 => ?_) hf' hg
      by_contra hd
      rcases (hfund d hd).1 with h | h
      · exact h h1
      · exact h h2

/-- **The inner region of a heavy component.** For a component `H` at a level `l₀ ≥ 1`, the
tree redirected along the boundary cycle of `H` (a simple cycle at level `l₀`) makes an inner
region with `K₀` the vertices of the cycle. -/
theorem exists_inner_comp (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ) {T : M.SpTree}
    (hT : IsBFS T) {w : P → ℝ} {l₀ : ℕ} (hl0 : 1 ≤ l₀) {f : M.Face}
    (hf : f ∉ M.zone (T.low l₀)) (hheavy : 2 / 3 < ∑ v ∈ ins (M.comp (T.low l₀) f), w v) :
    ∃ (K₀ : Finset P) (c₀ : P) (T₁ : M.SpTree),
      Inner T w l₀ (M.comp (T.low l₀) f) K₀ c₀ T₁ ∧ K₀ ⊆ T.lvl l₀ := by
  obtain ⟨C, -, hC, -⟩ := hM.exists_scycle_comp T (root_mem_low hT hl0)
    (fun v hv => parent_mem_low hT hv) hf
  obtain ⟨hr, hCh, hI, hK⟩ := inner_of_scycle hM htri hT hl0 hheavy C hC
  exact ⟨_, _, _, hI, hK⟩

/-! ### Heavy levels and the choice of the levels -/

/-- A level is *heavy* if some component of the faces avoiding the lower levels has a strict
inside of weight `> 2/3`. -/
def Heavy (T : M.SpTree) (w : P → ℝ) (l : ℕ) : Prop :=
  ∃ f, f ∉ M.zone (T.low l) ∧ 2 / 3 < ∑ v ∈ ins (M.comp (T.low l) f), w v

lemma heavy_mono {T : M.SpTree} {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) {l l' : ℕ} (hl : l ≤ l')
    (h : Heavy T w l') : Heavy T w l := by
  obtain ⟨f, hf, hh⟩ := h
  refine ⟨f, fun h' => hf (zone_low_mono hl h'), hh.trans_le ?_⟩
  exact sum_le_sum_of_subset_of_nonneg (ins_mono fun g hg => comp_mono hl hg)
    fun v _ _ => hw v

lemma height_lt_card {T : M.SpTree} (hT : IsBFS T) (v : P) :
    T.height v < Fintype.card P := by
  have : #(range (T.height v + 1)) ≤ #(univ : Finset P) := by
    refine card_le_card_of_injOn (fun i => T.parent^[i] v) (fun _ _ => mem_coe.2 (mem_univ _))
      fun i hi j hj hij => ?_
    simp only [coe_range, Set.mem_Iio] at hi hj
    have e1 := hT.height_iterate (v := v) (n := i) (by omega)
    have e2 := hT.height_iterate (v := v) (n := j) (by omega)
    simp only at hij
    rw [hij] at e1
    omega
  rw [card_range, card_univ] at this
  omega

lemma heavy_lt (hM : M.IsPlane) {T : M.SpTree} (hT : IsBFS T) {w : P → ℝ} {l : ℕ}
    (hl : 1 ≤ l) (h : Heavy T w l) : l < Fintype.card P := by
  obtain ⟨f, -, hh⟩ := h
  obtain ⟨v, hv⟩ : (ins (M.comp (T.low l) f)).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, sum_empty] at hh
    norm_num at hh
  exact (lt_of_mem_ins hM hT hl hv).trans (height_lt_card hT v)

lemma exists_small_level (T : M.SpTree) (a t : ℕ) :
    ∃ j < t + 1, (t + 1) * #(T.lvl (a + j)) ≤ Fintype.card P := by
  have := exists_mul_card_le (univ : Finset P) (fun j => T.lvl (a + j))
    (fun _ => subset_univ _) (fun i j hij => disjoint_left.2 fun v h1 h2 => hij (by
      rw [SpTree.mem_lvl] at h1 h2
      omega)) (Nat.succ_pos t)
  rwa [card_univ] at this

lemma le_sqrt_of_mul_le' {n c : ℕ} (h : (Nat.sqrt n + 1) * c ≤ n) : c ≤ Nat.sqrt n := by
  by_contra hc
  push Not at hc
  have h1 := Nat.lt_succ_sqrt' n
  have h2 : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ (Nat.sqrt n + 1) * c :=
    Nat.mul_le_mul_left _ hc
  rw [Nat.succ_eq_add_one, sq] at h1
  omega

/-! ### Miller's theorem for triangulations -/

/-- The theorem when the total weight exceeds `2/3`. -/
theorem exists_short_cycle_separator_of_heavy (hM : M.IsPlane)
    (htri : ∀ δ : D, M.IsTriangle δ) {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) (h1 : ∑ v, w v ≤ 1)
    (hheavy : 2 / 3 < ∑ v, w v) :
    ∃ (C : M.SCycle) (Z : Finset M.Face), C.k ≤ 6 * Nat.sqrt (Fintype.card P) + 4 ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      ∑ v ∈ sideIn C Z, w v ≤ 2 / 3 ∧ ∑ v ∈ sideOut C Z, w v ≤ 2 / 3 := by
  classical
  obtain ⟨r⟩ : Nonempty P := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [univ_eq_empty, sum_empty] at hheavy
    norm_num at hheavy
  obtain ⟨T, -, hT⟩ := exists_bfs hM r
  set n := Fintype.card P
  set t := Nat.sqrt n
  set ls := Nat.findGreatest (fun l => 1 ≤ l ∧ Heavy T w l) n with hlsdef
  have hls : ∀ l, 1 ≤ l → Heavy T w l → l ≤ ls := fun l hl h =>
    Nat.le_findGreatest (heavy_lt hM hT hl h).le ⟨hl, h⟩
  -- the outer level
  obtain ⟨j₂, hj₂, hc₂⟩ := exists_small_level T (ls + 1) t
  have hlight : ∀ f, f ∉ M.zone (T.low (ls + 1 + j₂)) →
      ∑ v ∈ ins (M.comp (T.low (ls + 1 + j₂)) f), w v ≤ 2 / 3 := fun f hf => by
    by_contra h
    push Not at h
    have := hls _ (by omega) ⟨f, hf, h⟩
    omega
  have hc₂' := le_sqrt_of_mul_le' hc₂
  by_cases hsmall : ls ≤ t
  · obtain ⟨C, Z, hk, rest⟩ := exists_band_separator hM htri hT hw h1 (inner_univ hM hT hheavy)
      (by omega : 0 < ls + 1 + j₂) hlight
    refine ⟨C, Z, ?_, rest⟩
    rw [card_singleton] at hk
    omega
  · push Not at hsmall
    obtain ⟨j₀, hj₀, hc₀⟩ := exists_small_level T (ls - t) t
    have hheavy_ls : Heavy T w ls :=
      (Nat.findGreatest_of_ne_zero hlsdef.symm (by omega)).2
    obtain ⟨f₀, hf₀, hh₀⟩ := heavy_mono hw (by omega : ls - t + j₀ ≤ ls) hheavy_ls
    obtain ⟨K₀, c₀, T₁, hI, hK₀⟩ := exists_inner_comp hM htri hT (by omega) hf₀ hh₀
    have hc₀' : #K₀ ≤ t := (card_le_card hK₀).trans (le_sqrt_of_mul_le' hc₀)
    obtain ⟨C, Z, hk, rest⟩ := exists_band_separator hM htri hT hw h1 hI
      (by omega : ls - t + j₀ < ls + 1 + j₂) hlight
    exact ⟨C, Z, by omega, rest⟩

/-- A plane map has a vertex. -/
lemma IsPlane.nonempty (hM : M.IsPlane) : Nonempty P := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hD : IsEmpty D := ⟨fun d => h.false (M.vert d)⟩
  have e1 : Fintype.card M.Face = 0 := Fintype.card_eq_zero_iff.2
    ⟨fun f => by obtain ⟨d, -⟩ := M.face_surjective f; exact hD.false d⟩
  have e2 : Fintype.card M.Edge = 0 := Fintype.card_eq_zero_iff.2
    ⟨fun e => by obtain ⟨d, -⟩ := M.edge_surjective e; exact hD.false d⟩
  have := hM.euler
  rw [e1, e2, Fintype.card_eq_zero_iff.2 h] at this
  omega

/-- **Miller's simple cycle separator theorem for triangulations.** Let `M` be a plane map with
`n` vertices all of whose faces are triangles, and `w` nonnegative weights on the vertices of
total at most `1`. Then there are a simple cycle `C` of at most `6 √n + 4` darts and a set `Z` of
faces bounded by `C`, such that the vertices strictly inside (off `C`, with their faces in `Z`)
and strictly outside weigh at most `2/3` each; no edge joins the two sides. -/
theorem exists_short_cycle_separator (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ)
    {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) (h1 : ∑ v, w v ≤ 1) :
    ∃ (C : M.SCycle) (Z : Finset M.Face), C.k ≤ 6 * Nat.sqrt (Fintype.card P) + 4 ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      ∑ v ∈ sideIn C Z, w v ≤ 2 / 3 ∧ ∑ v ∈ sideOut C Z, w v ≤ 2 / 3 := by
  by_cases hheavy : 2 / 3 < ∑ v, w v
  · exact exists_short_cycle_separator_of_heavy hM htri hw h1 hheavy
  push Not at hheavy
  -- with uniform weights
  have := hM.nonempty
  have hn : (0 : ℝ) < Fintype.card P := by exact_mod_cast Fintype.card_pos
  obtain ⟨C, Z, hk, hsep, -, -⟩ := exists_short_cycle_separator_of_heavy hM htri
    (w := fun _ => 1 / (Fintype.card P : ℝ)) (fun _ => by positivity)
    (by rw [sum_const, card_univ, nsmul_eq_mul]; field_simp; exact le_rfl)
    (by rw [sum_const, card_univ, nsmul_eq_mul]; field_simp; norm_num)
  refine ⟨C, Z, hk, hsep, ?_, ?_⟩
  · exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun v _ _ => hw v).trans hheavy
  · exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun v _ _ => hw v).trans hheavy

/-- **Miller's theorem with weights on vertices and faces**, for the stellar subdivision. Let `M`
be a plane map without loops, with `n` vertices and `F` faces, and `w` nonnegative weights of
total at most `1` on its vertices and faces (the vertices of the stellar subdivision). Then the
stellar subdivision has a simple cycle of at most `6 √(n + F) + 4` darts bounding a set of faces,
such that the vertices and faces of `M` strictly inside and strictly outside weigh at most `2/3`
each. -/
theorem exists_short_cycle_separator_stellar (hM : M.IsPlane)
    (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) {w : P ⊕ M.Face → ℝ} (hw : ∀ x, 0 ≤ w x)
    (h1 : ∑ x, w x ≤ 1) :
    ∃ (C : M.stellar.SCycle) (Z : Finset M.stellar.Face),
      C.k ≤ 6 * Nat.sqrt (Fintype.card P + Fintype.card M.Face) + 4 ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      ∑ x ∈ sideIn C Z, w x ≤ 2 / 3 ∧ ∑ x ∈ sideOut C Z, w x ≤ 2 / 3 := by
  have := exists_short_cycle_separator (isPlane_stellar hM) (M.isTriangle_stellar hl) hw h1
  rwa [Fintype.card_sum] at this

end Map

end PlanarSeparator
