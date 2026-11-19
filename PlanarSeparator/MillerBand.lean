module

public import PlanarSeparator.MillerLevel

/-!
# The band argument of Miller's theorem

Let `M` be a plane map all of whose faces are triangles, `T` a breadth-first tree of `M`, and
`w ≥ 0` weights on the vertices of total at most `1`. Suppose given an *inner region* at level
`l₀` (`PlanarSeparator.Map.Inner`): a connected set `H` of faces avoiding the levels `< l₀`
whose strict inside weighs more than `2/3`, with a spanning tree `T₁` which is breadth-first
above `l₀` and in which every vertex of `H` reaches a fixed vertex `c₀` through `H` and a set
`K₀` of vertices of level `≤ l₀` (the boundary cycle of `H`, made a tree path). Suppose that at a
level `l₂ > l₀` every component of the faces avoiding the levels `< l₂` weighs at most `2/3`.
Then there is a simple cycle separator with at most `2 (l₂ - l₀) + #K₀ + #L` darts, where `L` is
the set of vertices of level `l₂` (`PlanarSeparator.Map.exists_band_separator`).

## The proof

The weight of the strict inside of every component `Y` at level `l₂` is moved to a single vertex
of it, `rep Y`, giving weights `w'`. The balanced fundamental cycle of `T₁` for `w'`
(`PlanarSeparator.Map.SpTree.exists_simple_balanced`) is the boundary of a dart `δ`.

* If a face of `δ` lies off `H`, the cycle stays off the strict inside of `H`, which lies on one
  side and weighs more than `2/3`: impossible.
* If no face of `δ` avoids the levels `< l₂`, the cycle runs between the levels `l₀` and `l₂` and
  along `K₀`, it is short, and every component `Y` lies on one side of it, so that `w` and `w'`
  give the same weights to the sides.
* Otherwise both faces of `δ` lie in a component `Y`. Let `a` and `b` be the ancestors at level
  `l₂` of the ends of `δ`, on the boundary cycle `C` of `Y`. If `a = b`, the cycle stays in `Y`
  and `C` itself separates. Otherwise the part of the cycle above level `l₂` is replaced by one
  of the two arcs of `C` between `b` and `a`: redirecting `T₁` along the arc
  (`PlanarSeparator.Map.SpTree.arcTree`) makes the new cycle the fundamental cycle of the last
  dart of the arc. Outside `Y` the sides do not change, and `Y` lies on the side chosen by the
  arc; if `rep Y` was on the cycle, `Y` goes to the lighter side (if `Y` weighs at least `1/3`,
  `C` itself separates).

The argument uses of `rep` only that it is a vertex of level `> l₂` of the component, the same
for the whole component: the theorem holds for the weights moved by any such map
(`PlanarSeparator.Map.IsConc`, `PlanarSeparator.Map.exists_band_separator_of`), and from any
balanced dart (`PlanarSeparator.Map.band_separator_of_dart`), as a program computes them.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

open Finset

namespace Map

variable {D P : Type*} {M : Map D P} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-! ### Concentrating the weight of the outer regions -/

section Conc

variable (T : M.SpTree) (l₂ : ℕ)

open Classical in
/-- The component, at level `l₂`, of the faces at a vertex. -/
noncomputable def Yof (v : P) : Finset M.Face :=
  {g | ∃ d, M.vert d = v ∧ g ∈ M.comp (T.low l₂) (M.face d)}

open Classical in
/-- A representative vertex of level `> l₂` of a component. -/
noncomputable def rep (Y : Finset M.Face) : P :=
  if h : ∃ u, l₂ < T.height u ∧ Yof T l₂ u = Y then h.choose else T.root

open Classical in
/-- Vertices of level `> l₂` are sent to the representative of their component. -/
noncomputable def conc (v : P) : P := if l₂ < T.height v then rep T l₂ (Yof T l₂ v) else v

/-- The concentrated weights. -/
noncomputable def wc (w : P → ℝ) (u : P) : ℝ := ∑ v with conc T l₂ v = u, w v

variable {T l₂}

lemma conc_of_le {v : P} (h : T.height v ≤ l₂) : conc T l₂ v = v := by
  simp [conc, not_lt.2 h]

lemma conc_spec {v : P} (h : l₂ < T.height v) :
    l₂ < T.height (conc T l₂ v) ∧ Yof T l₂ (conc T l₂ v) = Yof T l₂ v := by
  have hex : ∃ u, l₂ < T.height u ∧ Yof T l₂ u = Yof T l₂ v := ⟨v, h, rfl⟩
  simp only [conc, h, ↓reduceIte, rep, dite_eq_left hex]
  exact hex.choose_spec

lemma wc_nonneg {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) (u : P) : 0 ≤ wc T l₂ w u :=
  sum_nonneg fun v _ => hw v

lemma sum_wc (w : P → ℝ) : ∑ u, wc T l₂ w u = ∑ v, w v := by
  unfold wc
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := conc T l₂)
    (fun _ _ => mem_univ _) w]

/-- **Weights move only within the components.** If every vertex of `S` is sent into `S'`, then
`S` weighs at most `S'` for the concentrated weights. -/
lemma sum_le_sum_wc {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) {S S' : Finset P}
    (h : ∀ v ∈ S, conc T l₂ v ∈ S') : ∑ v ∈ S, w v ≤ ∑ u ∈ S', wc T l₂ w u := by
  classical
  unfold wc
  rw [sum_comm' (t' := univ.filter fun v => conc T l₂ v ∈ S') (s' := fun v => {conc T l₂ v})
    (fun u v => by
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨h1, rfl⟩; exact ⟨rfl, h1⟩
      · rintro ⟨rfl, h1⟩; exact ⟨h1, rfl⟩)]
  · simp only [sum_singleton]
    exact sum_le_sum_of_subset_of_nonneg (fun v hv => by simpa using h v hv)
      fun v _ _ => hw v

end Conc

/-! ### Any choice of representatives -/

section ConcGen

/-- **A concentration map** at level `l₂`: it fixes the vertices of level `≤ l₂`, and sends
every vertex of level `> l₂` to a vertex of level `> l₂` of the same component, the same vertex
for all the vertices of a component. The band theorem holds for the weights moved by any such
map (`PlanarSeparator.Map.exists_band_separator_of`); `conc` is one (`isConc_conc`). -/
structure IsConc (T : M.SpTree) (l₂ : ℕ) (cn : P → P) : Prop where
  of_le : ∀ v, T.height v ≤ l₂ → cn v = v
  spec : ∀ v, l₂ < T.height v → l₂ < T.height (cn v) ∧ Yof T l₂ (cn v) = Yof T l₂ v
  eq : ∀ u v, l₂ < T.height u → l₂ < T.height v → Yof T l₂ u = Yof T l₂ v → cn u = cn v

/-- The weights moved by a map `cn`: the weight of `u` is that of the vertices sent to `u`. -/
noncomputable def wcf (cn : P → P) (w : P → ℝ) (u : P) : ℝ := ∑ v with cn v = u, w v

theorem wc_eq_wcf (T : M.SpTree) (l₂ : ℕ) (w : P → ℝ) : wc T l₂ w = wcf (conc T l₂) w := rfl

theorem isConc_conc (T : M.SpTree) (l₂ : ℕ) : IsConc T l₂ (conc T l₂) :=
  ⟨fun _ h => conc_of_le h, fun _ h => conc_spec h, fun u v hu hv h => by
    simp only [conc, hu, hv, ↓reduceIte, h]⟩

lemma wcf_nonneg {cn : P → P} {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) (u : P) : 0 ≤ wcf cn w u :=
  sum_nonneg fun v _ => hw v

lemma sum_wcf (cn : P → P) (w : P → ℝ) : ∑ u, wcf cn w u = ∑ v, w v := by
  unfold wcf
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := cn) (fun _ _ => mem_univ _) w]

/-- **Weights move only along `cn`.** If every vertex of `S` is sent into `S'`, then `S` weighs
at most `S'` for the moved weights. -/
lemma sum_le_sum_wcf {cn : P → P} {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) {S S' : Finset P}
    (h : ∀ v ∈ S, cn v ∈ S') : ∑ v ∈ S, w v ≤ ∑ u ∈ S', wcf cn w u := by
  classical
  unfold wcf
  rw [sum_comm' (t' := univ.filter fun v => cn v ∈ S') (s' := fun v => {cn v})
    (fun u v => by
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨h1, rfl⟩; exact ⟨rfl, h1⟩
      · rintro ⟨rfl, h1⟩; exact ⟨h1, rfl⟩)]
  · simp only [sum_singleton]
    exact sum_le_sum_of_subset_of_nonneg (fun v hv => by simpa using h v hv)
      fun v _ _ => hw v

end ConcGen

section Facts

variable {T : M.SpTree} (hT : IsBFS T) (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d)
include hT h3

/-- The faces at a vertex of level `> l` avoid the levels `< l`. -/
lemma notMem_zone_of_lt {l : ℕ} {v : P} (hv : l < T.height v) {d : D} (hd : M.vert d = v) :
    M.face d ∉ M.zone (T.low l) := by
  rw [notMem_zone_iff]
  intro e he
  have := hT.corner (h3 e) he.symm
  rw [mem_low]
  rw [hd] at this
  omega

lemma Yof_eq {l₂ : ℕ} {v : P} (hv : l₂ < T.height v) {d : D} (hd : M.vert d = v) :
    Yof T l₂ v = M.comp (T.low l₂) (M.face d) := by
  ext g
  simp only [Yof, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨d', hd', hg⟩
    have h1 : M.face d' ∈ M.comp (T.low l₂) (M.face d) :=
      mem_comp_of_lt hT h3 hv hd hd' (mem_comp_self (notMem_zone_of_lt hT h3 hv hd))
    rwa [← comp_eq_of_mem h1]
  · exact fun hg => ⟨d, hd, hg⟩

lemma mem_ins_Yof {l₂ : ℕ} {v : P} (hv : l₂ < T.height v) (hM : M.IsPlane) :
    v ∈ ins (Yof T l₂ v) := by
  obtain ⟨d, hd⟩ := hM.exists_dart v
  rw [Yof_eq hT h3 hv hd]
  exact mem_ins_of_lt hT h3 hv hd (mem_comp_self (notMem_zone_of_lt hT h3 hv hd))

lemma conc_mem_ins {l₂ : ℕ} {v : P} (hv : l₂ < T.height v) (hM : M.IsPlane) :
    conc T l₂ v ∈ ins (Yof T l₂ v) := by
  obtain ⟨h1, h2⟩ := conc_spec (T := T) hv
  rw [← h2]
  exact mem_ins_Yof hT h3 h1 hM

lemma cn_mem_ins {l₂ : ℕ} {cn : P → P} (hcn : IsConc T l₂ cn) {v : P} (hv : l₂ < T.height v)
    (hM : M.IsPlane) : cn v ∈ ins (Yof T l₂ v) := by
  obtain ⟨h1, h2⟩ := hcn.spec v hv
  rw [← h2]
  exact mem_ins_Yof hT h3 h1 hM

/-- On the strict inside of a component `Y` at level `l₂ ≥ 1`, the concentration is
`rep Y`. -/
lemma conc_of_mem_ins {l₂ : ℕ} (hl : 1 ≤ l₂) (hM : M.IsPlane) {f : M.Face} {v : P}
    (hv : v ∈ ins (M.comp (T.low l₂) f)) :
    l₂ < T.height v ∧ Yof T l₂ v = M.comp (T.low l₂) f ∧
      conc T l₂ v = rep T l₂ (M.comp (T.low l₂) f) := by
  have hlt := lt_of_mem_ins hM hT hl hv
  obtain ⟨d, hd⟩ := hM.exists_dart v
  have hY : Yof T l₂ v = M.comp (T.low l₂) f := by
    rw [Yof_eq hT h3 hlt hd, comp_eq_of_mem (mem_ins.1 hv d hd)]
  refine ⟨hlt, hY, ?_⟩
  simp [conc, hlt, hY]

end Facts

/-! ### Sides of fundamental cycles -/

section Sides

variable (hM : M.IsPlane) (T : M.SpTree)
include hM

/-- A connected set of faces crossed by no edge of a fundamental cochain lies on one side. -/
lemma SpTree.same_side {δ : D} {W : Finset M.Face} (hW : FConn W)
    (h : ∀ d, M.face d ∈ W → M.face (M.α d) ∈ W → T.fund δ d = 0) {f g : M.Face} (hf : f ∈ W)
    (hg : g ∈ W) : f ∈ T.inside δ ↔ g ∈ T.inside δ :=
  Iff.of_eq (hW.const (h := fun x => x ∈ T.inside δ)
    (fun d h1 h2 => propext ((SpTree.inside_iff hM δ d).2 (h d h1 h2))) hf hg)

/-- The vertices of the strict inside of such a set, off the cycle, lie on one side. -/
lemma SpTree.same_side_vert {δ : D} {W : Finset M.Face} (hW : FConn W)
    (h : ∀ d, M.face d ∈ W → M.face (M.α d) ∈ W → T.fund δ d = 0) {u v : P} (hu : u ∈ ins W)
    (hv : v ∈ ins W) (hu' : u ∉ T.cycV δ) (hv' : v ∉ T.cycV δ) :
    u ∈ T.inC δ ↔ v ∈ T.inC δ := by
  obtain ⟨d, hd⟩ := hM.exists_dart u
  obtain ⟨e, he⟩ := hM.exists_dart v
  rw [SpTree.mem_inC_iff hM hu' hd, SpTree.mem_inC_iff hM hv' he]
  exact T.same_side hM hW h (mem_ins.1 hu d hd) (mem_ins.1 hv e he)

end Sides

/-! ### The inner region -/

open Classical in
/-- The vertices of level `l`. -/
noncomputable def SpTree.lvl (T : M.SpTree) (l : ℕ) : Finset P := {v | T.height v = l}

lemma SpTree.mem_lvl {T : M.SpTree} {l : ℕ} {v : P} : v ∈ T.lvl l ↔ T.height v = l := by
  classical
  simp [SpTree.lvl]

/-- **The inner region** of the band argument, at level `l₀`: a connected set `H` of faces
whose strict inside weighs more than `2/3`, closed under adjacency among the faces avoiding the
levels `< l₀`, with a set `K₀` of vertices of level `≤ l₀` (the vertices of level `≤ l₀`
touching `H`) and a spanning tree `T₁`, breadth-first above level `l₀`, in which the root path
of every vertex of `H` reaches the vertex `c₀` through the strict inside of `H` (one vertex at
each level) and through `K₀`. A dart of `T₁` with a face off `H` has a fundamental cycle which
stays off the strict inside of `H` and leaves `H` on one side. -/
structure Inner (T : M.SpTree) (w : P → ℝ) (l₀ : ℕ) (H : Finset M.Face) (K₀ : Finset P)
    (c₀ : P) (T₁ : M.SpTree) : Prop where
  conn : FConn H
  heavy : 2 / 3 < ∑ v ∈ ins H, w v
  closed : ∀ d, M.face d ∈ H → M.face (M.α d) ∉ M.zone (T.low l₀) → M.face (M.α d) ∈ H
  touch : ∀ d, M.face d ∈ H → l₀ < T.height (M.vert d) → M.vert d ∈ ins H
  touch0 : ∀ d, M.face d ∈ H → T.height (M.vert d) ≤ l₀ → M.vert d ∈ K₀
  insLv : ∀ v ∈ ins H, l₀ < T.height v ∨ v ∈ K₀
  root₁ : T₁.root = T.root
  bfs₁ : ∀ v (h : v ≠ T₁.root), l₀ < T.height v →
    T.height (M.vert (M.α (T₁.par v h))) + 1 = T.height v
  height₁ : ∃ N, ∀ v, l₀ < T.height v → T₁.height v = T.height v * (N + 1)
  K₀lv : ∀ v ∈ K₀, T.height v ≤ l₀
  c₀mem : c₀ ∈ K₀
  band : ∀ u, (u ∈ ins H ∨ u ∈ K₀) → c₀ ∈ T₁.anc u ∧ ∀ v ∈ T₁.anc u, v ∉ T₁.anc c₀ →
    (v ∈ ins H ∧ l₀ < T.height v ∧ T.height v ≤ T.height u) ∨ v ∈ K₀
  bad : ∀ δ, ¬ T₁.IsTree δ → (M.face δ ∉ H ∨ M.face (M.α δ) ∉ H) →
    (∀ v ∈ ins H, v ∉ T₁.cycV δ) ∧ ∀ f ∈ H, ∀ g ∈ H, (f ∈ T₁.inside δ ↔ g ∈ T₁.inside δ)

/-! ### The boundary cycle of an outer component as a separator -/

section Fallback

variable {T : M.SpTree} (hM : M.IsPlane) (hT : IsBFS T) (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d)
include hM hT h3

/-- **The boundary cycle of a component separates**, if the component weighs at most `2/3` and
the rest off the cycle weighs at most `2/3`. -/
lemma fallback {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) {l₂ : ℕ} (hl : 1 ≤ l₂) {f : M.Face}
    {C : M.SCycle}
    (hC : ∀ d, (M.face d ∈ M.comp (T.low l₂) f ↔ M.face (M.α d) ∈ M.comp (T.low l₂) f) ↔
      ¬ C.Mem d)
    (hY1 : ∑ v ∈ ins (M.comp (T.low l₂) f), w v ≤ 2 / 3)
    (hY2 : ∑ v, w v - ∑ v ∈ ins (M.comp (T.low l₂) f), w v - ∑ v ∈ C.verts, w v ≤ 2 / 3) :
    ∃ (C : M.SCycle) (Z : Finset M.Face), C.k ≤ #(T.lvl l₂) ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      ∑ v ∈ sideIn C Z, w v ≤ 2 / 3 ∧ ∑ v ∈ sideOut C Z, w v ≤ 2 / 3 := by
  set Y := M.comp (T.low l₂) f
  have hlev : ∀ v ∈ C.verts, T.height v = l₂ := fun v hv => level_of_mem_verts hT h3 hC hv
  have hinsC : Disjoint (ins Y) C.verts := disjoint_left.2 fun v h1 h2 => by
    have := lt_of_mem_ins hM hT hl h1
    rw [hlev v h2] at this
    omega
  have hin : sideIn C Y ⊆ ins Y := fun v hv => by
    obtain ⟨hvC, d, hd, hdY⟩ := mem_sideIn.1 hv
    exact mem_ins.2 fun d' hd' => (face_iff_of_notMem_verts hC hvC hd hd').1 hdY
  have hout : Disjoint (sideOut C Y) (ins Y ∪ C.verts) := disjoint_left.2 fun v h1 h2 => by
    obtain ⟨hvC, hvI⟩ := mem_sideOut.1 h1
    rcases mem_union.1 h2 with h2 | h2
    · obtain ⟨d, hd⟩ := hM.exists_dart v
      exact hvI (mem_sideIn.2 ⟨hvC, d, hd, mem_ins.1 h2 d hd⟩)
    · exact hvC h2
  refine ⟨C, Y, ?_, isCycleSep_of_bd hC, ?_, ?_⟩
  · rw [← C.card_verts]
    exact card_le_card fun v hv => SpTree.mem_lvl.2 (hlev v hv)
  · exact (sum_le_sum_of_subset_of_nonneg hin fun v _ _ => hw v).trans hY1
  · have := sum_le_sum_of_subset_of_nonneg (subset_univ (sideOut C Y ∪ (ins Y ∪ C.verts)))
      fun v _ _ => hw v
    rw [sum_union hout, sum_union hinsC] at this
    linarith

end Fallback

/-! ### Paths in the band -/

section BandPaths

variable {T : M.SpTree} (hT : IsBFS T) (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d) {w : P → ℝ}
  {l₀ l₂ : ℕ} {H : Finset M.Face} {K₀ : Finset P} {c₀ : P} {T₁ : M.SpTree}
  (hI : Inner T w l₀ H K₀ c₀ T₁) (hl : l₀ < l₂)
include hT h3 hI hl

open Classical in
/-- The ancestors of `u` in the band: in the strict inside of `H`, of level in `(l₀, l₂]`. -/
noncomputable def bandF (T T₁ : M.SpTree) (H : Finset M.Face) (l₀ l₂ : ℕ) (u : P) : Finset P :=
  (T₁.anc u).filter fun v => v ∈ ins H ∧ l₀ < T.height v ∧ T.height v ≤ l₂

omit h3 hl in
/-- **One vertex per level in the band.** -/
lemma card_bandF (u : P) : #(bandF T T₁ H l₀ l₂ u) ≤ l₂ - l₀ := by
  classical
  obtain ⟨N, hN⟩ := hI.height₁
  have : #(bandF T T₁ H l₀ l₂ u) ≤ #(Ioc l₀ l₂) := by
    refine card_le_card_of_injOn T.height (fun v hv => ?_) ?_
    · simp only [bandF, coe_filter, Set.mem_ofPred_eq] at hv
      simp [hv.2.2.1, hv.2.2.2]
    · intro a ha b hb hab
      simp only [bandF, coe_filter, Set.mem_ofPred_eq] at ha hb
      refine T₁.height_injOn_anc u ha.1 hb.1 ?_
      rw [hN a ha.2.2.1, hN b hb.2.2.1, hab]
  simpa using this

omit h3 in
/-- **The tree path between two vertices of the band** meets only `K₀` and the band ancestors
of its ends, and each of its edges has an end below level `l₂`. -/
lemma pathC_band {u u' : P} (hu : u ∈ ins H ∨ u ∈ K₀) (hu' : u' ∈ ins H ∨ u' ∈ K₀)
    (hul : T.height u ≤ l₂) (hul' : T.height u' ≤ l₂) {d : D}
    (hd : T₁.pathC u d + T₁.pathC u' d ≠ 0) :
    (M.vert d ∈ K₀ ∨ M.vert d ∈ bandF T T₁ H l₀ l₂ u ∨ M.vert d ∈ bandF T T₁ H l₀ l₂ u') ∧
      T₁.IsTree d ∧ (T.height (M.vert d) < l₂ ∨ T.height (M.vert (M.α d)) < l₂) := by
  obtain ⟨hc, hb⟩ := hI.band u hu
  obtain ⟨hc', hb'⟩ := hI.band u' hu'
  have hsplit : T₁.pathC u d + T₁.pathC u' d =
      (T₁.pathC u d + T₁.pathC c₀ d) + (T₁.pathC u' d + T₁.pathC c₀ d) := by
    rw [add_add_add_comm, Kasteleyn.ZMod.two_add_self, add_zero]
  rw [hsplit] at hd
  have key : ∀ {y : P}, (y ∈ ins H ∨ y ∈ K₀) → T.height y ≤ l₂ → c₀ ∈ T₁.anc y →
      (∀ v ∈ T₁.anc y, v ∉ T₁.anc c₀ →
        (v ∈ ins H ∧ l₀ < T.height v ∧ T.height v ≤ T.height y) ∨ v ∈ K₀) →
      T₁.pathC y d + T₁.pathC c₀ d ≠ 0 →
      (M.vert d ∈ K₀ ∨ M.vert d ∈ bandF T T₁ H l₀ l₂ y) ∧ T₁.IsTree d ∧
        (T.height (M.vert d) < l₂ ∨ T.height (M.vert (M.α d)) < l₂) := by
    intro y hy hyl hcy hby h
    refine ⟨?_, ?_, ?_⟩
    · rcases T₁.vert_of_pathC_add_ne_zero hcy h with h1 | ⟨h1, h2⟩
      · exact Or.inl (h1 ▸ hI.c₀mem)
      · rcases hby _ h1 h2 with ⟨h3, h4, h5⟩ | h3
        · exact Or.inr (mem_filter.2 ⟨h1, h3, h4, h5.trans hyl⟩)
        · exact Or.inl h3
    · obtain ⟨v, -, -, hv, h1⟩ := T₁.pathC_add_ne_zero hcy h
      exact ⟨v, hv, h1⟩
    · obtain ⟨v, hv1, hv2, hv, h1⟩ := T₁.pathC_add_ne_zero hcy h
      have hlv : T.height v < l₂ ∨ T.height (M.vert (M.α (T₁.par v hv))) < l₂ := by
        rcases hby _ hv1 hv2 with ⟨-, h4, h5⟩ | h4
        · have := hI.bfs₁ v hv h4
          right
          omega
        · left
          have := hI.K₀lv v h4
          omega
      rcases h1 with rfl | rfl
      · rwa [T₁.vert_par]
      · rw [M.α_α, T₁.vert_par]
        exact hlv.symm
  by_cases h1 : T₁.pathC u d + T₁.pathC c₀ d = 0
  · rw [h1, zero_add] at hd
    obtain ⟨h2, h3, h4⟩ := key hu' hul' hc' hb' hd
    exact ⟨by tauto, h3, h4⟩
  · obtain ⟨h2, h3, h4⟩ := key hu hul hc hb h1
    exact ⟨by tauto, h3, h4⟩

end BandPaths

/-- An edge with an end below level `l` has both faces touching the levels `< l`. -/
lemma zone_of_end {T : M.SpTree} {l : ℕ} {d : D}
    (h : T.height (M.vert d) < l ∨ T.height (M.vert (M.α d)) < l) :
    M.face d ∈ M.zone (T.low l) ∧ M.face (M.α d) ∈ M.zone (T.low l) := by
  rcases h with h | h
  · refine ⟨face_mem_zone ((mem_low T).2 h), ?_⟩
    rw [← M.face_φ]
    exact face_mem_zone (by rw [mem_low, M.vert_φ, M.α_α]; exact h)
  · refine ⟨?_, face_mem_zone ((mem_low T).2 h)⟩
    rw [← M.face_φ]
    exact face_mem_zone (by rw [mem_low, M.vert_φ]; exact h)

/-! ### The band case -/

section BandCase

variable (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ) {T : M.SpTree} (hT : IsBFS T)
  {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) {l₀ l₂ : ℕ} {H : Finset M.Face} {K₀ : Finset P} {c₀ : P}
  {T₁ : M.SpTree} (hI : Inner T w l₀ H K₀ c₀ T₁) (hl : l₀ < l₂)

include hI in
lemma ends_mem {δ : D} (hδH : M.face δ ∈ H ∧ M.face (M.α δ) ∈ H) :
    (M.vert δ ∈ ins H ∨ M.vert δ ∈ K₀) ∧ (M.vert (M.α δ) ∈ ins H ∨ M.vert (M.α δ) ∈ K₀) := by
  constructor
  · by_cases h : l₀ < T.height (M.vert δ)
    · exact Or.inl (hI.touch δ hδH.1 h)
    · exact Or.inr (hI.touch0 δ hδH.1 (not_lt.1 h))
  · by_cases h : l₀ < T.height (M.vert (M.α δ))
    · exact Or.inl (hI.touch _ hδH.2 h)
    · exact Or.inr (hI.touch0 _ hδH.2 (not_lt.1 h))

include hT htri in
lemma ends_le_of_zone {l : ℕ} {δ : D}
    (hz : M.face δ ∈ M.zone (T.low l) ∨ M.face (M.α δ) ∈ M.zone (T.low l)) :
    T.height (M.vert δ) ≤ l ∧ T.height (M.vert (M.α δ)) ≤ l := by
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (htri d).φ_three
  rcases hz with hz | hz
  · obtain ⟨e, he, hel⟩ := mem_zone.1 hz
    rw [mem_low] at hel
    have e1 := hT.corner (h3 e) (d' := δ) he.symm
    have e2 := hT.corner (h3 e) (d' := M.φ δ) (by rw [M.face_φ, he])
    rw [M.vert_φ] at e2
    omega
  · obtain ⟨e, he, hel⟩ := mem_zone.1 hz
    rw [mem_low] at hel
    have e1 := hT.corner (h3 e) (d' := M.α δ) he.symm
    have e2 := hT.corner (h3 e) (d' := M.φ (M.α δ)) (by rw [M.face_φ, he])
    rw [M.vert_φ, M.α_α] at e2
    omega

include hT htri hI hl in
/-- The vertices and edges of the fundamental cycle of a dart with both ends in the band. -/
lemma cycV_band {δ : D} (hx : M.vert δ ∈ ins H ∨ M.vert δ ∈ K₀)
    (hz : M.vert (M.α δ) ∈ ins H ∨ M.vert (M.α δ) ∈ K₀) (hxl : T.height (M.vert δ) ≤ l₂)
    (hzl : T.height (M.vert (M.α δ)) ≤ l₂) {d : D} (hd : T₁.fund δ d ≠ 0) :
    (M.vert d ∈ K₀ ∨ M.vert d ∈ bandF T T₁ H l₀ l₂ (M.vert δ) ∨
      M.vert d ∈ bandF T T₁ H l₀ l₂ (M.vert (M.α δ))) ∧
    ((d = δ ∨ d = M.α δ) ∨ (T₁.IsTree d ∧
      (T.height (M.vert d) < l₂ ∨ T.height (M.vert (M.α d)) < l₂))) := by
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (htri d).φ_three
  rw [SpTree.fund_apply, add_assoc] at hd
  have hend : ∀ y, (y ∈ ins H ∨ y ∈ K₀) → T.height y ≤ l₂ →
      y ∈ K₀ ∨ y ∈ bandF T T₁ H l₀ l₂ y := by
    intro y hy hyl
    rcases hy with hy | hy
    · rcases hI.insLv y hy with h | h
      · exact Or.inr (mem_filter.2 ⟨T₁.mem_anc_self y, hy, h, hyl⟩)
      · exact Or.inl h
    · exact Or.inl hy
  by_cases h1 : M.edgeInd δ d = 0
  · rw [h1, zero_add] at hd
    obtain ⟨h2, h4, h5⟩ := pathC_band hT hI hl hx hz hxl hzl hd
    exact ⟨h2, Or.inr ⟨h4, h5⟩⟩
  · rcases edgeInd_ne_zero h1 with rfl | rfl
    · rcases hend _ hx hxl with h | h
      · exact ⟨Or.inl h, Or.inl (Or.inl rfl)⟩
      · exact ⟨Or.inr (Or.inl h), Or.inl (Or.inl rfl)⟩
    · rcases hend _ hz hzl with h | h
      · exact ⟨Or.inl h, Or.inl (Or.inr rfl)⟩
      · exact ⟨Or.inr (Or.inr h), Or.inl (Or.inr rfl)⟩

/-- A vertex above `l₂` and its representative lie on the same side of a fundamental cycle
which crosses no edge inside their component. -/
lemma conc_same_side (hM : M.IsPlane) {T : M.SpTree} (hT : IsBFS T)
    (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d) {l₂ : ℕ} (T₁ : M.SpTree) {cn : P → P}
    (hcn : IsConc T l₂ cn) {δ : D} {v : P} (hv : l₂ < T.height v)
    (hfund : ∀ d, M.face d ∈ Yof T l₂ v → M.face (M.α d) ∈ Yof T l₂ v → T₁.fund δ d = 0)
    (hv' : v ∉ T₁.cycV δ) (hc' : cn v ∉ T₁.cycV δ) :
    v ∈ T₁.inC δ ↔ cn v ∈ T₁.inC δ := by
  obtain ⟨d, hd⟩ := hM.exists_dart v
  have hY := Yof_eq hT h3 hv hd
  refine T₁.same_side_vert hM ?_ hfund (mem_ins_Yof hT h3 hv hM) (cn_mem_ins hT h3 hcn hv hM) hv'
    hc'
  rw [hY]
  exact comp_fConn _ _

lemma sideOut_inside (T : M.SpTree) {δ : D} (hδ : ¬ T.IsTree δ) :
    sideOut (T.fcycle δ) (T.inside δ) = T.outC δ := by
  ext v
  rw [mem_sideOut, T.sideIn_inside hδ, SpTree.fcycle_verts hδ]
  simp [SpTree.outC]

include hM htri hT hw hI hl in
/-- **The band case, explicitly**: for a dart with both faces in `H`, one of them touching the
levels `< l₂`, the fundamental cycle of the dart in `T₁` with its inside separates. -/
theorem band_case_fcycle {cn : P → P} (hcn : IsConc T l₂ cn) {δ : D} (hδ : ¬ T₁.IsTree δ)
    (hδH : M.face δ ∈ H ∧ M.face (M.α δ) ∈ H)
    (hz : M.face δ ∈ M.zone (T.low l₂) ∨ M.face (M.α δ) ∈ M.zone (T.low l₂))
    (hA : ∑ v ∈ T₁.inC δ, wcf cn w v ≤ 2 / 3) (hB : ∑ v ∈ T₁.outC δ, wcf cn w v ≤ 2 / 3) :
    (T₁.fcycle δ).k ≤ 2 * (l₂ - l₀) + #K₀ ∧
      IsCycleSep (T₁.fcycle δ) (T₁.inside δ) (sideIn (T₁.fcycle δ) (T₁.inside δ))
        (sideOut (T₁.fcycle δ) (T₁.inside δ)) ∧
      ∑ v ∈ sideIn (T₁.fcycle δ) (T₁.inside δ), w v ≤ 2 / 3 ∧
      ∑ v ∈ sideOut (T₁.fcycle δ) (T₁.inside δ), w v ≤ 2 / 3 := by
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (htri d).φ_three
  obtain ⟨hx, hz'⟩ := ends_mem hI hδH
  obtain ⟨hxl, hzl⟩ := ends_le_of_zone htri hT hz
  have hcyc := fun {d : D} (hd : T₁.fund δ d ≠ 0) => cycV_band htri hT hI hl hx hz' hxl hzl hd
  have hlev : ∀ v ∈ T₁.cycV δ, T.height v ≤ l₂ := by
    intro v hv
    obtain ⟨d, rfl, hd⟩ := (T₁.mem_cycV).1 hv
    rcases (hcyc hd).1 with h | h | h
    · have := hI.K₀lv _ h; omega
    · exact (mem_filter.1 h).2.2.2
    · exact (mem_filter.1 h).2.2.2
  have hsub : T₁.cycV δ ⊆ K₀ ∪ bandF T T₁ H l₀ l₂ (M.vert δ) ∪
      bandF T T₁ H l₀ l₂ (M.vert (M.α δ)) := by
    intro v hv
    obtain ⟨d, rfl, hd⟩ := (T₁.mem_cycV).1 hv
    rcases (hcyc hd).1 with h | h | h <;> simp [h]
  -- the components above `l₂` are not crossed
  have hfund : ∀ v, l₂ < T.height v → ∀ d, M.face d ∈ Yof T l₂ v →
      M.face (M.α d) ∈ Yof T l₂ v → T₁.fund δ d = 0 := by
    intro v hv d h1 h2
    obtain ⟨e, he⟩ := hM.exists_dart v
    rw [Yof_eq hT h3 hv he] at h1 h2
    have n1 := (mem_comp.1 h1).1
    have n2 := (mem_comp.1 h2).1
    by_contra hd
    rcases (hcyc hd).2 with (rfl | rfl) | ⟨-, h5⟩
    · rcases hz with h | h
      · exact n1 h
      · exact n2 h
    · rw [M.α_α] at n2
      rcases hz with h | h
      · exact n2 h
      · exact n1 h
    · exact n1 (zone_of_end h5).1
  have hside : ∀ v, l₂ < T.height v → (v ∈ T₁.inC δ ↔ cn v ∈ T₁.inC δ) ∧
      cn v ∉ T₁.cycV δ := by
    intro v hv
    have hc := (hcn.spec _ hv).1
    have hc' : cn v ∉ T₁.cycV δ := fun h => by have := hlev _ h; omega
    exact ⟨conc_same_side hM hT h3 T₁ hcn hv (hfund v hv) (fun h => by have := hlev _ h; omega) hc',
      hc'⟩
  refine ⟨?_, isCycleSep_of_bd (T₁.bd_inside hM hδ), ?_, ?_⟩
  · rw [← SpTree.card_cycV hδ]
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    have := card_union_le K₀ (bandF T T₁ H l₀ l₂ (M.vert δ))
    have := card_bandF (l₂ := l₂) hT hI (M.vert δ)
    have := card_bandF (l₂ := l₂) hT hI (M.vert (M.α δ))
    omega
  · rw [T₁.sideIn_inside hδ]
    refine (sum_le_sum_wcf hw fun v hv => ?_).trans hA
    by_cases hvl : T.height v ≤ l₂
    · rwa [hcn.of_le _ hvl]
    · exact ((hside v (not_le.1 hvl)).1).1 hv
  · rw [sideOut_inside T₁ hδ]
    refine (sum_le_sum_wcf hw fun v hv => ?_).trans hB
    by_cases hvl : T.height v ≤ l₂
    · rwa [hcn.of_le _ hvl]
    · obtain ⟨h1, h2⟩ := hside v (not_le.1 hvl)
      simp only [SpTree.outC, mem_filter, mem_univ, true_and] at hv ⊢
      exact ⟨h2, fun h => hv.2 (h1.2 h)⟩

include hM htri hT hw hI hl in
/-- **The band case**: a dart with both faces in `H`, one of them touching the levels `< l₂`. -/
theorem band_case {cn : P → P} (hcn : IsConc T l₂ cn) {δ : D} (hδ : ¬ T₁.IsTree δ)
    (hδH : M.face δ ∈ H ∧ M.face (M.α δ) ∈ H)
    (hz : M.face δ ∈ M.zone (T.low l₂) ∨ M.face (M.α δ) ∈ M.zone (T.low l₂))
    (hA : ∑ v ∈ T₁.inC δ, wcf cn w v ≤ 2 / 3) (hB : ∑ v ∈ T₁.outC δ, wcf cn w v ≤ 2 / 3) :
    ∃ (C : M.SCycle) (Z : Finset M.Face), C.k ≤ 2 * (l₂ - l₀) + #K₀ ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      ∑ v ∈ sideIn C Z, w v ≤ 2 / 3 ∧ ∑ v ∈ sideOut C Z, w v ≤ 2 / 3 := by
  exact ⟨_, _, band_case_fcycle hM htri hT hw hI hl hcn hδ hδH hz hA hB⟩

end BandCase

/-! ### Helpers for the deep case -/

section DeepHelpers

/-- Comparison of the sides of two fundamental cycles on a connected set of faces on which
their cochains agree. -/
lemma side_cmp (hM : M.IsPlane) (T T' : M.SpTree) {δ e : D} {W : Finset M.Face} (hW : FConn W)
    (h : ∀ d, M.face d ∈ W → M.face (M.α d) ∈ W → T.fund δ d = T'.fund e d) {f g : M.Face}
    (hf : f ∈ W) (hg : g ∈ W) :
    (f ∈ T.inside δ ↔ f ∈ T'.inside e) ↔ (g ∈ T.inside δ ↔ g ∈ T'.inside e) := by
  refine Iff.of_eq (hW.const (h := fun x => (x ∈ T.inside δ ↔ x ∈ T'.inside e))
    (fun d h1 h2 => propext ?_) hf hg)
  have e1 := SpTree.inside_iff (T := T) hM δ d
  have e2 := SpTree.inside_iff (T := T') hM e d
  rw [h d h1 h2, ← e2] at e1
  generalize (M.face d ∈ T.inside δ) = p₁ at e1 ⊢
  generalize (M.face (M.α d) ∈ T.inside δ) = p₂ at e1 ⊢
  generalize (M.face d ∈ T'.inside e) = q₁ at e1 ⊢
  generalize (M.face (M.α d) ∈ T'.inside e) = q₂ at e1 ⊢
  tauto

/-- A vertex touching a component lies in its strict inside or on its boundary cycle. -/
lemma touch_comp {B : Finset P} {f : M.Face} {C : M.SCycle}
    (hC : ∀ d, (M.face d ∈ M.comp B f ↔ M.face (M.α d) ∈ M.comp B f) ↔ ¬ C.Mem d) {d : D}
    (hd : M.face d ∈ M.comp B f) : M.vert d ∈ ins (M.comp B f) ∨ M.vert d ∈ C.verts := by
  by_cases h : M.vert d ∈ ins (M.comp B f)
  · exact Or.inl h
  · right
    obtain ⟨d', hd', hn⟩ : ∃ d', M.vert d' = M.vert d ∧ M.face d' ∉ M.comp B f := by
      by_contra hno
      push Not at hno
      exact h (mem_ins.2 fun d' h' => hno d' h')
    exact mem_verts_of_touch hC hd'.symm hd hn

/-- The two faces at an edge from a vertex of the strict inside lie in the set. -/
lemma faces_of_mem_ins {W : Finset M.Face} {d : D} (h : M.vert d ∈ ins W) :
    M.face d ∈ W ∧ M.face (M.α d) ∈ W := by
  refine ⟨mem_ins.1 h d rfl, ?_⟩
  rw [← face_σ]
  exact mem_ins.1 h _ (M.vert_σ d)

lemma SCycle.mem_of_arcS_ne_zero (C : M.SCycle) {s m : ℕ} (hs : s < C.k) (hm : m ≤ C.k) {d : D}
    (h : C.arcS s m d ≠ 0) : C.Mem d := by
  unfold SCycle.arcS at h
  rw [Finset.sum_apply] at h
  obtain ⟨j, hj, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  rcases edgeInd_ne_zero hne with rfl | rfl
  · exact C.mem_d (C.idxAt_lt hs (by rw [mem_range] at hj; omega))
  · exact (C.mem_α_iff).2 (C.mem_d (C.idxAt_lt hs (by rw [mem_range] at hj; omega)))

lemma SCycle.arcS_at (C : M.SCycle) (hC : C.Proper) {s m j : ℕ} (hs : s < C.k) (hm : m ≤ C.k)
    (hj : j < m) : C.arcS s m (C.d (C.idxAt s j)) = 1 := by
  unfold SCycle.arcS
  rw [Finset.sum_apply, sum_eq_single_of_mem j (mem_range.2 hj) fun i hi hij => ?_]
  · exact edgeInd_self _
  · have hi' := mem_range.1 hi
    have hne : C.idxAt s i ≠ C.idxAt s j := by
      intro e
      have := congrArg (C.off s) e
      rw [C.off_idxAt hs (by omega), C.off_idxAt hs (by omega)] at this
      exact hij this
    obtain ⟨h1, h2⟩ := C.ne_of_proper hC (C.idxAt_lt hs (by omega)) (C.idxAt_lt hs (by omega)) hne
    exact edgeInd_eq_zero h1 h2

lemma SCycle.idxAt_idxAt_k (C : M.SCycle) {s L : ℕ} (hs : s < C.k) (hL : L ≤ C.k) :
    C.idxAt (C.idxAt s L) (C.k - L) = s := by
  unfold SCycle.idxAt
  split_ifs <;> first | contradiction | omega

end DeepHelpers

section DeepHelpers2

variable (hM : M.IsPlane) {T : M.SpTree} (hT : IsBFS T) (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d)
  {w : P → ℝ} {l₀ l₂ : ℕ} {H : Finset M.Face} {K₀ : Finset P} {c₀ : P} {T₁ : M.SpTree}
  (hI : Inner T w l₀ H K₀ c₀ T₁) (hl : l₀ < l₂)

lemma zone_low_mono {T : M.SpTree} {l l' : ℕ} (h : l ≤ l') :
    M.zone (T.low l) ⊆ M.zone (T.low l') := fun x hx => by
  obtain ⟨d, rfl, hd⟩ := mem_zone.1 hx
  exact face_mem_zone (by rw [mem_low] at *; omega)

include hI hl in
/-- The components at level `l₂` of faces of `H` lie in `H`. -/
lemma comp_subset_H {g : M.Face} (hg : g ∈ H) : M.comp (T.low l₂) g ⊆ H := by
  intro x hx
  obtain ⟨-, hr⟩ := mem_comp.1 hx
  clear hx
  induction hr with
  | refl => exact hg
  | tail _ hbc ih =>
    obtain ⟨-, hc, d, rfl, rfl⟩ := hbc
    exact hI.closed d ih fun h => mem_compl.1 hc (zone_low_mono hl.le h)

include hM hT hI hl in
/-- **The ancestor at level `l₂`.** The root path of a vertex of the strict inside or of the
boundary cycle of a component at level `l₂` leaves it at a vertex of the boundary cycle, after
running through the strict inside. -/
lemma exists_top {f : M.Face} {C : M.SCycle}
    (hC : ∀ d, (M.face d ∈ M.comp (T.low l₂) f ↔ M.face (M.α d) ∈ M.comp (T.low l₂) f) ↔
      ¬ C.Mem d) (u : P) (hu : u ∈ ins (M.comp (T.low l₂) f) ∨ u ∈ C.verts) :
    ∃ a ∈ T₁.anc u, a ∈ C.verts ∧
      ∀ v ∈ T₁.anc u, v ∉ T₁.anc a → v ∈ ins (M.comp (T.low l₂) f) := by
  induction hn : T.height u using Nat.strong_induction_on generalizing u with
  | _ n ih =>
  by_cases huC : u ∈ C.verts
  · exact ⟨u, T₁.mem_anc_self u, huC, fun v hv hva => absurd hv hva⟩
  have huY := hu.resolve_right huC
  have hlt := lt_of_mem_ins hM hT (by omega) huY
  have hur : u ≠ T₁.root := by
    rw [hI.root₁]
    intro h
    rw [h, hT.root] at hlt
    omega
  have hbfs := hI.bfs₁ u hur (by omega)
  have hpY := (faces_of_mem_ins (d := T₁.par u hur) (by rw [T₁.vert_par]; exact huY)).2
  obtain ⟨a, ha, haC, hrest⟩ := ih _ (by omega) _ (touch_comp hC hpY) rfl
  refine ⟨a, ?_, haC, fun v hv hva => ?_⟩
  · rw [T₁.anc_of_ne hur, T₁.parent_of_ne hur]
    exact mem_insert_of_mem ha
  · rw [T₁.anc_of_ne hur, T₁.parent_of_ne hur] at hv
    rcases mem_insert.1 hv with rfl | hv
    · exact huY
    · exact hrest v hv hva

include hM hT h3 in
lemma conc_ins_iff {l₂ : ℕ} {cn : P → P} (hcn : IsConc T l₂ cn) (hl2 : 1 ≤ l₂) {f : M.Face}
    {v : P} (hv : l₂ < T.height v) :
    v ∈ ins (M.comp (T.low l₂) f) ↔ cn v ∈ ins (M.comp (T.low l₂) f) := by
  constructor
  · intro h
    obtain ⟨-, hY, -⟩ := conc_of_mem_ins hT h3 hl2 hM h
    rw [← hY]
    exact cn_mem_ins hT h3 hcn hv hM
  · intro h
    obtain ⟨-, hY, -⟩ := conc_of_mem_ins hT h3 hl2 hM h
    rw [(hcn.spec _ hv).2] at hY
    rw [← hY]
    exact mem_ins_Yof hT h3 hv hM

include hM hT h3 in
/-- The moved weight of the representative of a component is at most the weight of its strict
inside. -/
lemma wc_le {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) {l₂ : ℕ} {cn : P → P} (hcn : IsConc T l₂ cn)
    (hl2 : 1 ≤ l₂) {f : M.Face} {v₀ : P} (hv₀ : v₀ ∈ ins (M.comp (T.low l₂) f)) :
    wcf cn w (cn v₀) ≤ ∑ v ∈ ins (M.comp (T.low l₂) f), w v := by
  unfold wcf
  refine sum_le_sum_of_subset_of_nonneg (fun v hv => ?_) fun v _ _ => hw v
  have hv' := (mem_filter.1 hv).2
  have hc := (conc_ins_iff hM hT h3 hcn hl2 (lt_of_mem_ins hM hT hl2 hv₀)).1 hv₀
  by_cases hvl : l₂ < T.height v
  · rw [conc_ins_iff hM hT h3 hcn hl2 hvl, hv']
    exact hc
  · rw [hcn.of_le _ (not_lt.1 hvl)] at hv'
    rw [hv']
    exact hc

include hM hT h3 in
lemma conc_eq_of_mem_ins {l₂ : ℕ} {cn : P → P} (hcn : IsConc T l₂ cn) (hl2 : 1 ≤ l₂)
    {f : M.Face} {v v₀ : P} (hv : v ∈ ins (M.comp (T.low l₂) f))
    (hv₀ : v₀ ∈ ins (M.comp (T.low l₂) f)) : cn v = cn v₀ := by
  obtain ⟨h1, h2, -⟩ := conc_of_mem_ins hT h3 hl2 hM hv
  obtain ⟨h1', h2', -⟩ := conc_of_mem_ins hT h3 hl2 hM hv₀
  exact hcn.eq _ _ h1 h1' (h2.trans h2'.symm)

end DeepHelpers2

/-- Comparison of two sets of faces bounded by cochains which agree inside a connected set of
faces. -/
lemma side_cmp' {Z Z' W : Finset M.Face} {c c' : D → ZMod 2}
    (hZ : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ c d = 0)
    (hZ' : ∀ d, (M.face d ∈ Z' ↔ M.face (M.α d) ∈ Z') ↔ c' d = 0) (hW : FConn W)
    (h : ∀ d, M.face d ∈ W → M.face (M.α d) ∈ W → c d = c' d) {f g : M.Face} (hf : f ∈ W)
    (hg : g ∈ W) : (f ∈ Z ↔ f ∈ Z') ↔ (g ∈ Z ↔ g ∈ Z') := by
  refine Iff.of_eq (hW.const (h := fun x => (x ∈ Z ↔ x ∈ Z')) (fun d h1 h2 => propext ?_) hf hg)
  have e1 := hZ d
  have e2 := hZ' d
  rw [h d h1 h2, ← e2] at e1
  generalize (M.face d ∈ Z) = p₁ at e1 ⊢
  generalize (M.face (M.α d) ∈ Z) = p₂ at e1 ⊢
  generalize (M.face d ∈ Z') = q₁ at e1 ⊢
  generalize (M.face (M.α d) ∈ Z') = q₂ at e1 ⊢
  tauto

section Reroute

variable (hM : M.IsPlane) {T₁ : M.SpTree} {C : M.SCycle}

include hM in
/-- **One rerouting option.** Redirecting `T₁` along the arc of `L'` steps of `C` from `s'`
gives a simple cycle bounding a set of faces `Z` whose boundary cochain is the arc plus the
tree path `P` between its ends; `Z` can be oriented to agree with a given set at a face `g₀`. -/
lemma reroute_option {s' L' : ℕ} (hs' : s' < C.k) (hL1 : 1 ≤ L') (hLk : L' < C.k)
    (hr : T₁.root ∉ C.verts)
    (hC : ∀ i < C.k, T₁.height (M.vert (C.d i)) = T₁.height (M.vert (C.d s')))
    (hnt : ∀ i < C.k, ¬ T₁.IsTree (C.d i)) (hCp : C.Proper) (P : D → ZMod 2)
    (hP : T₁.pathC (M.vert (C.d s')) + T₁.pathC (M.vert (C.d (C.idxAt s' L'))) = P)
    (Z₀ : Finset M.Face) (g₀ : M.Face) :
    ∃ (Cf : M.SCycle) (Z : Finset M.Face),
      (∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ Cf.Mem d) ∧
      (∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ C.arcS s' L' d + P d = 0) ∧
      (∀ v, v ∈ Cf.verts ↔ ∃ d, M.vert d = v ∧ C.arcS s' L' d + P d ≠ 0) ∧
      (g₀ ∈ Z ↔ g₀ ∈ Z₀) := by
  set T₂ := T₁.arcTree C s' (L' - 1) hs' hr hC
  set e := C.d (C.idxAt s' (L' - 1))
  have he : ¬ T₂.IsTree e := T₁.not_isTree_arcTree C hCp hnt hL1 hLk
  have hfund : T₂.fund e = C.arcS s' L' + P := by
    rw [T₁.fund_arcTree C hL1 hLk, ← hP, add_assoc]
  have hbd := T₂.bd_inside hM he
  have hbd' : ∀ d, (M.face d ∈ T₂.inside e ↔ M.face (M.α d) ∈ T₂.inside e) ↔
      C.arcS s' L' d + P d = 0 := fun d => by
    rw [SpTree.inside_iff hM, hfund, Pi.add_apply]
  have hverts : ∀ v, v ∈ (T₂.fcycle e).verts ↔
      ∃ d, M.vert d = v ∧ C.arcS s' L' d + P d ≠ 0 := fun v => by
    rw [SpTree.fcycle_verts he, SpTree.mem_cycV, hfund]
    rfl
  by_cases hg : g₀ ∈ T₂.inside e ↔ g₀ ∈ Z₀
  · exact ⟨T₂.fcycle e, T₂.inside e, hbd, hbd', hverts, hg⟩
  · refine ⟨T₂.fcycle e, (T₂.inside e)ᶜ, bd_compl hbd, fun d => ?_, hverts, ?_⟩
    · rw [mem_compl, mem_compl, ← hbd' d]
      tauto
    · rw [mem_compl]
      tauto

end Reroute

lemma exists_dart_face_of_mem_verts {W : Finset M.Face} {C : M.SCycle}
    (hC : ∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) ↔ ¬ C.Mem d) {v : P} (hv : v ∈ C.verts) :
    ∃ d, M.vert d = v ∧ M.face d ∈ W := by
  obtain ⟨i, hi, rfl⟩ := C.mem_verts.1 hv
  have hb := (hC (C.d i)).not.2 (not_not.2 (C.mem_d hi))
  by_cases h : M.face (C.d i) ∈ W
  · exact ⟨_, rfl, h⟩
  · refine ⟨M.σ (C.d i), M.vert_σ _, ?_⟩
    rw [face_σ]
    tauto

lemma fConn_univ (hM : M.IsPlane) : FConn (univ : Finset M.Face) := fun f _ g _ =>
  Relation.ReflTransGen.mono (fun _ _ h => ⟨mem_univ _, mem_univ _, h⟩) _ _
    (hM.connected.face_rtg f g)

lemma bd_symmDiff {Z Y : Finset M.Face} {c c' : D → ZMod 2}
    (hZ : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ c d = 0)
    (hY : ∀ d, (M.face d ∈ Y ↔ M.face (M.α d) ∈ Y) ↔ c' d = 0) (d : D) :
    (M.face d ∈ symmDiff Z Y ↔ M.face (M.α d) ∈ symmDiff Z Y) ↔ c d + c' d = 0 := by
  have key : ∀ x y : ZMod 2, x + y = 0 ↔ (x = 0 ↔ y = 0) := by decide
  rw [key, ← hZ d, ← hY d, mem_symmDiff, mem_symmDiff]
  tauto

lemma iff_of_not_iff_of_iff_not {p q r : Prop} (h1 : ¬ (p ↔ r)) (h2 : p ↔ ¬ q) : q ↔ r := by
  tauto

/-! ### The deep case -/

section DeepCase

variable (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ) {T : M.SpTree} (hT : IsBFS T)
  {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) (h1 : ∑ v, w v ≤ 1) {l₀ l₂ : ℕ} {H : Finset M.Face}
  {K₀ : Finset P} {c₀ : P} {T₁ : M.SpTree} (hI : Inner T w l₀ H K₀ c₀ T₁) (hl : l₀ < l₂)

include hM htri hT hw h1 hI hl in
/-- **The deep case, from the boundary cycle**: a dart both of whose faces avoid the levels
`< l₂`, and any proper simple cycle `C` bounding the component `Y` of the dart at level `l₂`
(given, rather than chosen by `PlanarSeparator.Map.IsPlane.exists_scycle_comp`). The proof takes
`C` itself (`fallback`), or the fundamental cycle of the last dart of one of the two arcs of `C`
between the vertices where the root paths of the ends of the dart meet `C`, in the tree
redirected along the arc (`reroute_option`); the statement does not say which. -/
theorem deep_case_of_scycle {cn : P → P} (hcn : IsConc T l₂ cn) {δ : D} (hδ : ¬ T₁.IsTree δ)
    (hδH : M.face δ ∈ H ∧ M.face (M.α δ) ∈ H)
    (hz1 : M.face δ ∉ M.zone (T.low l₂)) (hz2 : M.face (M.α δ) ∉ M.zone (T.low l₂))
    (hA : ∑ v ∈ T₁.inC δ, wcf cn w v ≤ 2 / 3) (hB : ∑ v ∈ T₁.outC δ, wcf cn w v ≤ 2 / 3)
    (hlight : ∀ f, f ∉ M.zone (T.low l₂) → ∑ v ∈ ins (M.comp (T.low l₂) f), w v ≤ 2 / 3)
    (C : M.SCycle) (hCp : C.Proper)
    (hC : ∀ d, (M.face d ∈ M.comp (T.low l₂) (M.face δ) ↔
      M.face (M.α d) ∈ M.comp (T.low l₂) (M.face δ)) ↔ ¬ C.Mem d) :
    ∃ (C : M.SCycle) (Z : Finset M.Face), C.k ≤ 2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂) ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      ∑ v ∈ sideIn C Z, w v ≤ 2 / 3 ∧ ∑ v ∈ sideOut C Z, w v ≤ 2 / 3 := by
  classical
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (htri d).φ_three
  have hl2 : 1 ≤ l₂ := by omega
  set Y := M.comp (T.low l₂) (M.face δ) with hYdef
  have hδY : M.face δ ∈ Y := mem_comp_self hz1
  have hαY : M.face (M.α δ) ∈ Y := mem_comp_of_adj hδY hz2
  have hYz : ∀ g ∈ Y, g ∉ M.zone (T.low l₂) := fun g hg => (mem_comp.1 hg).1
  have hYH : Y ⊆ H := comp_subset_H hI hl hδH.1
  have hr2 : T.root ∈ T.low l₂ := root_mem_low hT hl2
  have hlevC : ∀ v ∈ C.verts, T.height v = l₂ := fun v hv => level_of_mem_verts hT h3 hC hv
  have hinsl : ∀ v ∈ ins Y, l₂ < T.height v := fun v hv => lt_of_mem_ins hM hT hl2 hv
  have hinsC : ∀ v ∈ ins Y, v ∉ C.verts := fun v hv hvC => by
    have := hinsl v hv
    rw [hlevC v hvC] at this
    omega
  -- a face off `Y`
  obtain ⟨d₀, hd₀⟩ := hM.exists_dart T.root
  set g₀ := M.face d₀
  have hg₀ : g₀ ∉ Y := fun h => hYz g₀ h (face_mem_zone (hd₀ ▸ hr2))
  have hYc : FConn Yᶜ := compl_comp_fConn hM (zone_fConn hM T hr2
    (fun v hv => parent_mem_low hT hv)) (hd₀ ▸ hr2) (M.face δ)
  -- the fallback
  have hfb : ∑ v, w v - ∑ v ∈ ins Y, w v - ∑ v ∈ C.verts, w v ≤ 2 / 3 →
      ∃ (C : M.SCycle) (Z : Finset M.Face), C.k ≤ 2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂) ∧
        IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
        ∑ v ∈ sideIn C Z, w v ≤ 2 / 3 ∧ ∑ v ∈ sideOut C Z, w v ≤ 2 / 3 := fun h => by
    obtain ⟨C', Z', hk, rest⟩ := fallback hM hT h3 hw hl2 hC (hlight _ hz1) h
    exact ⟨C', Z', by omega, rest⟩
  -- the ends of `δ` and their ancestors at level `l₂`
  obtain ⟨a, hax, haC, hxa⟩ := exists_top hM hT hI hl hC _ (touch_comp hC hδY)
  obtain ⟨b, hbz, hbC, hzb⟩ := exists_top hM hT hI hl hC _ (touch_comp hC hαY)
  have hend : ∀ {u t : P}, t ∈ T₁.anc u → t ∈ C.verts →
      (∀ v ∈ T₁.anc u, v ∉ T₁.anc t → v ∈ ins Y) → u ∈ ins Y ∨ u = t := by
    intro u t ht htC hrest
    by_cases hu : u ∈ T₁.anc t
    · exact Or.inr (T₁.eq_of_mem_anc_of_mem_anc hu ht)
    · exact Or.inl (hrest u (T₁.mem_anc_self u) hu)
  have hxa' := hend hax haC hxa
  have hzb' := hend hbz hbC hzb
  have hHa : ∀ t ∈ C.verts, t ∈ ins H := fun t ht => by
    obtain ⟨d, hd, hdY⟩ := exists_dart_face_of_mem_verts hC ht
    rw [← hd]
    exact hI.touch d (hYH hdY) (by rw [hd, hlevC t ht]; exact hl)
  -- the deep part `Q` and the band part `P` of the fundamental cochain of `δ`
  set Pc : D → ZMod 2 := T₁.pathC a + T₁.pathC b with hPdef
  set Qc : D → ZMod 2 := M.edgeInd δ + (T₁.pathC (M.vert δ) + T₁.pathC a) +
    (T₁.pathC (M.vert (M.α δ)) + T₁.pathC b) with hQdef
  have hfQP : T₁.fund δ = Qc + Pc := by
    funext d
    simp only [SpTree.fund_apply, hQdef, hPdef, Pi.add_apply]
    generalize M.edgeInd δ d = e₁
    generalize T₁.pathC (M.vert δ) d = p₁
    generalize T₁.pathC (M.vert (M.α δ)) d = p₂
    generalize T₁.pathC a d = p₃
    generalize T₁.pathC b d = p₄
    revert e₁ p₁ p₂ p₃ p₄
    decide
  have hQ : ∀ d, Qc d ≠ 0 → (M.face d ∈ Y ∧ M.face (M.α d) ∈ Y) ∧
      (M.vert d ∈ ins Y ∨ M.vert d = a ∨ M.vert d = b) := by
    have hpart : ∀ {u t : P}, t ∈ T₁.anc u → (∀ v ∈ T₁.anc u, v ∉ T₁.anc t → v ∈ ins Y) →
        ∀ d, T₁.pathC u d + T₁.pathC t d ≠ 0 →
          (M.face d ∈ Y ∧ M.face (M.α d) ∈ Y) ∧ (M.vert d ∈ ins Y ∨ M.vert d = t) := by
      intro u t ht hrest d hd
      refine ⟨?_, ?_⟩
      · obtain ⟨v, hv1, hv2, hv, rfl | rfl⟩ := T₁.pathC_add_ne_zero ht hd
        · exact faces_of_mem_ins (by rw [T₁.vert_par]; exact hrest v hv1 hv2)
        · rw [M.α_α]
          exact (faces_of_mem_ins (by rw [T₁.vert_par]; exact hrest v hv1 hv2)).symm
      · rcases T₁.vert_of_pathC_add_ne_zero ht hd with h | ⟨h1, h2⟩
        · exact Or.inr h
        · exact Or.inl (hrest _ h1 h2)
    intro d hd
    simp only [hQdef, Pi.add_apply] at hd
    by_cases e1 : M.edgeInd δ d = 0
    · rw [e1, zero_add] at hd
      by_cases e2 : T₁.pathC (M.vert δ) d + T₁.pathC a d = 0
      · rw [e2, zero_add] at hd
        obtain ⟨h1, h2⟩ := hpart hbz hzb d hd
        exact ⟨h1, h2.elim Or.inl fun h => Or.inr (Or.inr h)⟩
      · obtain ⟨h1, h2⟩ := hpart hax hxa d e2
        exact ⟨h1, h2.elim Or.inl fun h => Or.inr (Or.inl h)⟩
    · rcases edgeInd_ne_zero e1 with rfl | rfl
      · exact ⟨⟨hδY, hαY⟩, hxa'.elim Or.inl fun h => Or.inr (Or.inl h)⟩
      · rw [M.α_α]
        exact ⟨⟨hαY, hδY⟩, hzb'.elim Or.inl fun h => Or.inr (Or.inr h)⟩
  have hPb := fun {d : D} (hd : Pc d ≠ 0) =>
    pathC_band hT hI hl (Or.inl (hHa a haC)) (Or.inl (hHa b hbC)) (hlevC a haC).le
      (hlevC b hbC).le hd
  have hPz : ∀ d, Pc d ≠ 0 → M.face d ∉ Y ∧ M.face (M.α d) ∉ Y := fun d hd => by
    obtain ⟨-, -, h⟩ := hPb hd
    have := zone_of_end h
    exact ⟨fun h' => hYz _ h' this.1, fun h' => hYz _ h' this.2⟩
  have hCc : ∀ d, (M.face d ∈ Y ↔ M.face (M.α d) ∈ Y) ↔ C.cochain d = 0 := fun d => by
    rw [hC d, ← C.cochain_ne_zero_iff, not_not]
  -- the darts of `C` are not tree darts of `T₁`
  have hnt : ∀ i < C.k, ¬ T₁.IsTree (C.d i) := by
    rintro i hi ⟨v, hv, h⟩
    have e1 : T.height (M.vert (C.d i)) = l₂ := hlevC _ (C.mem_verts.2 ⟨i, hi, rfl⟩)
    have e2 : T.height (M.vert (M.α (C.d i))) = l₂ := by
      rw [C.vert_α_d_suc hi]
      exact hlevC _ (C.mem_verts.2 ⟨_, C.suc_lt hi, rfl⟩)
    rcases h with h | h
    · have hv' : M.vert (C.d i) = v := by rw [h, T₁.vert_par]
      have := hI.bfs₁ v hv (by rw [← hv', e1]; exact hl)
      rw [← h, e2, ← hv', e1] at this
      omega
    · have hv' : M.vert (M.α (C.d i)) = v := by rw [h, M.α_α, T₁.vert_par]
      have := hI.bfs₁ v hv (by rw [← hv', e2]; exact hl)
      rw [← h, e1, ← hv', e2] at this
      omega
  have hntm : ∀ d, C.Mem d → ¬ T₁.IsTree d := by
    rintro d ⟨i, hi, rfl | rfl⟩
    · exact hnt i hi
    · rw [T₁.isTree_α]
      exact hnt i hi
  have hPC : ∀ d, C.Mem d → Pc d = 0 := fun d hd => by
    by_contra h
    exact hntm d hd (hPb h).2.1
  -- the case `a = b`: the cycle of `δ` stays in `Y`
  by_cases hab : a = b
  · subst hab
    have hP0 : Pc = 0 := by
      funext d
      simp only [hPdef, Pi.add_apply, Pi.zero_apply]
      exact Kasteleyn.ZMod.two_add_self _
    have hf : T₁.fund δ = Qc := by rw [hfQP, hP0, add_zero]
    have hside : ∀ f, f ∉ Y → ∀ g, g ∉ Y → (f ∈ T₁.inside δ ↔ g ∈ T₁.inside δ) :=
      fun f hf' g hg' => T₁.same_side hM hYc (fun d h1 h2 => by
        rw [hf]
        by_contra h
        exact mem_compl.1 h1 (hQ d h).1.1) (mem_compl.2 hf') (mem_compl.2 hg')
    have hcyc : ∀ v ∈ T₁.cycV δ, v ∈ ins Y ∨ v = a := by
      intro v hv
      obtain ⟨d, rfl, hd⟩ := T₁.mem_cycV.1 hv
      rw [hf] at hd
      rcases (hQ d hd).2 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inr h
    have hoff : ∀ v, v ∉ ins Y → ∃ d, M.vert d = v ∧ M.face d ∉ Y := by
      intro v hv
      by_contra hno
      push Not at hno
      exact hv (mem_ins.2 hno)
    obtain ⟨S, hS1, hS2⟩ : ∃ S : Finset P, (S = T₁.inC δ ∨ S = T₁.outC δ) ∧
        ∀ v, v ∉ ins Y → v ≠ a → v ∈ S := by
      by_cases hg : g₀ ∈ T₁.inside δ
      · refine ⟨T₁.inC δ, Or.inl rfl, fun v hv hva => ?_⟩
        have hvc : v ∉ T₁.cycV δ := fun h => (hcyc v h).elim hv hva
        obtain ⟨d, hd, hdY⟩ := hoff v hv
        rw [SpTree.mem_inC_iff hM hvc hd]
        exact (hside _ hdY _ hg₀).2 hg
      · refine ⟨T₁.outC δ, Or.inr rfl, fun v hv hva => ?_⟩
        have hvc : v ∉ T₁.cycV δ := fun h => (hcyc v h).elim hv hva
        obtain ⟨d, hd, hdY⟩ := hoff v hv
        simp only [SpTree.outC, mem_filter, mem_univ, true_and]
        exact ⟨hvc, fun h => hg ((hside _ hdY _ hg₀).1 ((SpTree.mem_inC_iff hM hvc hd).1 h))⟩
    have hSle : ∑ v ∈ S, wcf cn w v ≤ 2 / 3 := by
      rcases hS1 with rfl | rfl
      · exact hA
      · exact hB
    have hrest : ∑ v ∈ univ.filter (fun v => v ∉ ins Y ∧ v ≠ a), w v ≤ 2 / 3 := by
      refine (sum_le_sum_wcf hw fun v hv => ?_).trans hSle
      obtain ⟨hv1, hv2⟩ := (mem_filter.1 hv).2
      refine hS2 _ ?_ ?_
      · by_cases hvl : l₂ < T.height v
        · rwa [← conc_ins_iff hM hT h3 hcn hl2 hvl]
        · rwa [hcn.of_le _ (not_lt.1 hvl)]
      · by_cases hvl : l₂ < T.height v
        · intro h
          have := (hcn.spec _ hvl).1
          rw [h, hlevC a haC] at this
          omega
        · rwa [hcn.of_le _ (not_lt.1 hvl)]
    apply hfb
    have hsplit := sum_filter_add_sum_filter_not univ (fun v => v ∉ ins Y ∧ v ≠ a) w
    have hrest2 : ∑ v ∈ univ.filter (fun v => ¬ (v ∉ ins Y ∧ v ≠ a)), w v ≤
        ∑ v ∈ ins Y, w v + ∑ v ∈ C.verts, w v := by
      rw [← sum_union (disjoint_left.2 fun v h1 h2 => hinsC v h1 h2)]
      refine sum_le_sum_of_subset_of_nonneg (fun v hv => ?_) fun v _ _ => hw v
      have := (mem_filter.1 hv).2
      rw [mem_union]
      by_cases h : v ∈ ins Y
      · exact Or.inl h
      · right
        have hva : v = a := by
          by_contra hva
          exact this ⟨h, hva⟩
        rw [hva]
        exact haC
    linarith
  -- a heavy component: its boundary cycle separates
  by_cases hω : 1 / 3 ≤ ∑ v ∈ ins Y, w v
  · apply hfb
    have := sum_nonneg fun v (_ : v ∈ C.verts) => hw v
    linarith
  push Not at hω
  -- the indices of `b` and `a` on `C`
  obtain ⟨hsk, hsb⟩ := C.idx_spec hbC
  obtain ⟨htk, hta⟩ := C.idx_spec haC
  set s := C.idx b with hsdef
  set t₀ := C.idx a with ht₀def
  have hst : s ≠ t₀ := fun h => hab (by rw [← hta, ← hsb, h])
  set L := C.off s t₀ with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    unfold SCycle.off
    split_ifs <;> omega
  have hLk : L < C.k := C.off_lt hsk htk
  have hat : C.idxAt s L = t₀ := C.idxAt_off hsk htk
  have hbt : C.idxAt t₀ (C.k - L) = s := by
    rw [← hat]
    exact C.idxAt_idxAt_k hsk hLk.le
  -- `T₁` is flat on `C`
  obtain ⟨N, hN⟩ := hI.height₁
  have hflat : ∀ i < C.k, ∀ j < C.k,
      T₁.height (M.vert (C.d i)) = T₁.height (M.vert (C.d j)) := fun i hi j hj => by
    have e1 := hlevC _ (C.mem_verts.2 ⟨i, hi, rfl⟩)
    have e2 := hlevC _ (C.mem_verts.2 ⟨j, hj, rfl⟩)
    rw [hN _ (by rw [e1]; exact hl), hN _ (by rw [e2]; exact hl), e1, e2]
  have hr : T₁.root ∉ C.verts := fun h => by
    have := hlevC _ h
    rw [hI.root₁, hT.root] at this
    omega
  -- the two options
  obtain ⟨C₁, Z₁, bd₁, bdΓ₁, verts₁, g₁⟩ := reroute_option hM hsk hL1 hLk hr
    (fun i hi => hflat i hi s hsk) hnt hCp Pc (by rw [hsb, hat, hta, hPdef, add_comm])
    (T₁.inside δ) g₀
  obtain ⟨C₂, Z₂, bd₂, bdΓ₂, verts₂, g₂⟩ := reroute_option hM htk (by omega : 1 ≤ C.k - L)
    (by omega) hr (fun i hi => hflat i hi t₀ htk) hnt hCp Pc (by rw [hta, hbt, hsb])
    (T₁.inside δ) g₀
  -- outside `Y` the sides agree with those of `δ`
  have hK1 : ∀ {s' L' : ℕ} {Z : Finset M.Face}, s' < C.k → L' ≤ C.k →
      (∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ C.arcS s' L' d + Pc d = 0) →
      (g₀ ∈ Z ↔ g₀ ∈ T₁.inside δ) → ∀ g, g ∉ Y → (g ∈ Z ↔ g ∈ T₁.inside δ) := by
    intro s' L' Z hs' hL' hbdΓ hg g hg'
    have := side_cmp' hbdΓ (fun d => SpTree.inside_iff (T := T₁) hM δ d) hYc (fun d h1 h2 => ?_)
      (mem_compl.2 hg') (mem_compl.2 hg₀)
    · exact this.2 hg
    · rw [hfQP, Pi.add_apply]
      have hq : Qc d = 0 := by
        by_contra h
        exact mem_compl.1 h1 (hQ d h).1.1
      have ha : C.arcS s' L' d = 0 := by
        by_contra h
        exact (hC d).1 (iff_of_false (mem_compl.1 h1) (mem_compl.1 h2))
          (C.mem_of_arcS_ne_zero hs' hL' h)
      rw [hq, ha]
  -- inside `Y` the sides are constant
  have hK2 : ∀ {s' L' : ℕ} {Z : Finset M.Face}, s' < C.k → L' ≤ C.k →
      (∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ C.arcS s' L' d + Pc d = 0) →
      ∀ g ∈ Y, ∀ g' ∈ Y, (g ∈ Z ↔ g' ∈ Z) := by
    intro s' L' Z hs' hL' hbdΓ g hg g' hg'
    have := side_cmp' (Z' := ∅) (c' := 0) hbdΓ (fun d => by simp) (comp_fConn _ _)
      (fun d h1 h2 => ?_) hg hg'
    · exact not_iff_not.1 (by simpa using this)
    · have ha : C.arcS s' L' d = 0 := by
        by_contra h
        exact (hC d).1 (iff_of_true h1 h2) (C.mem_of_arcS_ne_zero hs' hL' h)
      have hp : Pc d = 0 := by
        by_contra h
        exact (hPz d h).1 h1
      rw [ha, hp]
      rfl
  -- the two options differ exactly on `Y`
  have hsum := C.arcS_add_arcS hCp hsk hLk.le
  rw [hat] at hsum
  have hK3 : ∀ g ∈ Y, (g ∈ Z₁ ↔ g ∉ Z₂) := by
    intro g hg
    have := side_cmp' bdΓ₁ (bd_symmDiff bdΓ₂ hCc) (fConn_univ hM) (fun d _ _ => ?_)
      (mem_univ g) (mem_univ g₀)
    · have e1 := hK1 hsk hLk.le bdΓ₁ g₁ g₀ hg₀
      have e2 := hK1 htk (by omega) bdΓ₂ g₂ g₀ hg₀
      have hg₀' : g₀ ∈ Z₁ ↔ g₀ ∈ symmDiff Z₂ Y := by
        rw [mem_symmDiff]
        constructor
        · intro h
          exact Or.inl ⟨e2.2 (e1.1 h), hg₀⟩
        · rintro (⟨h, -⟩ | ⟨h, -⟩)
          · exact e1.2 (e2.1 h)
          · exact absurd h hg₀
      rw [this.2 hg₀', mem_symmDiff]
      constructor
      · rintro (⟨-, h⟩ | ⟨-, h⟩)
        · exact absurd hg h
        · exact h
      · intro h
        exact Or.inr ⟨hg, h⟩
    · have := congrFun hsum d
      simp only [Pi.add_apply] at this ⊢
      rw [← this]
      generalize C.arcS s L d = x
      generalize C.arcS t₀ (C.k - L) d = y
      generalize Pc d = z
      revert x y z
      decide
  -- the ends of an arc lie on the new cycle
  have hends : ∀ {s' L' : ℕ} {Cf : M.SCycle}, s' < C.k → 1 ≤ L' → L' < C.k →
      (∀ v, v ∈ Cf.verts ↔ ∃ d, M.vert d = v ∧ C.arcS s' L' d + Pc d ≠ 0) →
      M.vert (C.d s') ∈ Cf.verts ∧ M.vert (C.d (C.idxAt s' L')) ∈ Cf.verts := by
    intro s' L' Cf hs' hL1' hLk' hv
    have hm0 : C.idxAt s' 0 = s' := by
      unfold SCycle.idxAt
      simp [hs']
    constructor
    · refine (hv _).2 ⟨C.d s', rfl, ?_⟩
      rw [hPC _ (C.mem_d hs'), add_zero]
      have := C.arcS_at hCp hs' hLk'.le (show 0 < L' by omega)
      rw [hm0] at this
      rw [this]
      exact one_ne_zero
    · have hi := C.idxAt_lt hs' (show L' - 1 < C.k by omega)
      have hsuc : C.suc (C.idxAt s' (L' - 1)) = C.idxAt s' L' := by
        unfold SCycle.suc SCycle.idxAt
        split_ifs <;> first | contradiction | omega
      refine (hv _).2 ⟨M.α (C.d (C.idxAt s' (L' - 1))), by rw [C.vert_α_d_suc hi, hsuc], ?_⟩
      rw [hPC _ ((C.mem_α_iff).2 (C.mem_d hi)), add_zero]
      have : C.arcS s' L' (M.α (C.d (C.idxAt s' (L' - 1)))) =
          C.arcS s' L' (C.d (C.idxAt s' (L' - 1))) := by
        unfold SCycle.arcS
        simp only [Finset.sum_apply, edgeInd_α]
      rw [this, C.arcS_at hCp hs' hLk'.le (show L' - 1 < L' by omega)]
      exact one_ne_zero
  -- the side wanted for `Y`
  obtain ⟨lighter, hlighter⟩ : ∃ p : Prop,
      p ↔ ∑ v ∈ T₁.inC δ, wcf cn w v ≤ ∑ v ∈ T₁.outC δ, wcf cn w v := ⟨_, Iff.rfl⟩
  obtain ⟨want, hwantdef⟩ : ∃ p : Prop,
      p ↔ ∀ v ∈ ins Y, cn v ∈ T₁.inC δ ∨ (cn v ∈ T₁.cycV δ ∧ lighter) :=
    ⟨_, Iff.rfl⟩
  obtain ⟨Cf, Zf, s', L', hs', hL1', hLk', bdf, bdΓf, vertsf, hgf, hendsab, hwant⟩ :
      ∃ (Cf : M.SCycle) (Zf : Finset M.Face) (s' L' : ℕ), s' < C.k ∧ 1 ≤ L' ∧ L' < C.k ∧
        (∀ d, (M.face d ∈ Zf ↔ M.face (M.α d) ∈ Zf) ↔ ¬ Cf.Mem d) ∧
        (∀ d, (M.face d ∈ Zf ↔ M.face (M.α d) ∈ Zf) ↔ C.arcS s' L' d + Pc d = 0) ∧
        (∀ v, v ∈ Cf.verts ↔ ∃ d, M.vert d = v ∧ C.arcS s' L' d + Pc d ≠ 0) ∧
        (g₀ ∈ Zf ↔ g₀ ∈ T₁.inside δ) ∧
        ((M.vert (C.d s') = a ∧ M.vert (C.d (C.idxAt s' L')) = b) ∨
          (M.vert (C.d s') = b ∧ M.vert (C.d (C.idxAt s' L')) = a)) ∧
        (M.face δ ∈ Zf ↔ want) := by
    by_cases h : M.face δ ∈ Z₁ ↔ want
    · exact ⟨C₁, Z₁, s, L, hsk, hL1, hLk, bd₁, bdΓ₁, verts₁, g₁,
        Or.inr ⟨hsb, by rw [hat, hta]⟩, h⟩
    · exact ⟨C₂, Z₂, t₀, C.k - L, htk, by omega, by omega, bd₂, bdΓ₂, verts₂, g₂,
        Or.inl ⟨hta, by rw [hbt, hsb]⟩, iff_of_not_iff_of_iff_not h (hK3 _ hδY)⟩
  have hK1f := hK1 hs' hLk'.le bdΓf hgf
  have hK2f := hK2 hs' hLk'.le bdΓf
  have habf : a ∈ Cf.verts ∧ b ∈ Cf.verts := by
    obtain ⟨e1, e2⟩ := hends hs' hL1' hLk' vertsf
    rcases hendsab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at e1
      rw [h2] at e2
      exact ⟨e1, e2⟩
    · rw [h1] at e1
      rw [h2] at e2
      exact ⟨e2, e1⟩
  -- the vertices of the new cycle
  have hPv : ∀ d, Pc d ≠ 0 → M.vert d ∈ Cf.verts := fun d hd => by
    refine (vertsf _).2 ⟨d, rfl, ?_⟩
    have : C.arcS s' L' d = 0 := by
      by_contra h
      exact hd (hPC d (C.mem_of_arcS_ne_zero hs' hLk'.le h))
    rw [this, zero_add]
    exact hd
  have hCfv : ∀ v ∈ Cf.verts, v ∈ C.verts ∨ v ∈ K₀ ∨ v ∈ bandF T T₁ H l₀ l₂ a ∨
      v ∈ bandF T T₁ H l₀ l₂ b := by
    intro v hv
    obtain ⟨d, rfl, hd⟩ := (vertsf _).1 hv
    by_cases h : C.arcS s' L' d = 0
    · rw [h, zero_add] at hd
      rcases (hPb hd).1 with h' | h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr h'))
    · exact Or.inl (C.mem_verts_of_mem (C.mem_of_arcS_ne_zero hs' hLk'.le h))
  have hCfl : ∀ v ∈ Cf.verts, T.height v ≤ l₂ := by
    intro v hv
    rcases hCfv v hv with h | h | h | h
    · exact (hlevC v h).le
    · have := hI.K₀lv v h
      omega
    · exact (mem_filter.1 h).2.2.2
    · exact (mem_filter.1 h).2.2.2
  have hcyc : ∀ v ∈ T₁.cycV δ, v ∈ ins Y ∨ v ∈ Cf.verts := by
    intro v hv
    obtain ⟨d, rfl, hd⟩ := T₁.mem_cycV.1 hv
    rw [hfQP, Pi.add_apply] at hd
    by_cases hq : Qc d = 0
    · rw [hq, zero_add] at hd
      exact Or.inr (hPv d hd)
    · rcases (hQ d hq).2 with h | h | h
      · exact Or.inl h
      · rw [h]
        exact Or.inr habf.1
      · rw [h]
        exact Or.inr habf.2
  have hoff : ∀ v, v ∉ ins Y → ∃ d, M.vert d = v ∧ M.face d ∉ Y := by
    intro v hv
    by_contra hno
    push Not at hno
    exact hv (mem_ins.2 hno)
  -- vertices off `Y` keep their side, and so do their representatives
  have hconcS : ∀ v, v ∉ ins Y → v ∉ Cf.verts →
      (v ∈ T₁.inC δ ↔ cn v ∈ T₁.inC δ) ∧ cn v ∉ T₁.cycV δ ∧
        v ∉ T₁.cycV δ := by
    intro v hv hvf
    have hvc : v ∉ T₁.cycV δ := fun h => (hcyc v h).elim hv hvf
    by_cases hvl : l₂ < T.height v
    · have hcY : cn v ∉ ins Y := fun h => hv ((conc_ins_iff hM hT h3 hcn hl2 hvl).2 h)
      have hcl := (hcn.spec _ hvl).1
      have hcc : cn v ∉ T₁.cycV δ := fun h =>
        (hcyc _ h).elim hcY fun h' => by have := hCfl _ h'; omega
      refine ⟨conc_same_side hM hT h3 T₁ hcn hvl (fun d h1' h2' => ?_) hvc hcc, hcc, hvc⟩
      obtain ⟨e, he⟩ := hM.exists_dart v
      rw [Yof_eq hT h3 hvl he] at h1' h2'
      rw [hfQP, Pi.add_apply]
      have hq : Qc d = 0 := by
        by_contra h
        have hdY := (hQ d h).1.1
        apply hv
        have hYe : M.comp (T.low l₂) (M.face e) = Y := by
          rw [← comp_eq_of_mem h1', comp_eq_of_mem hdY]
        rw [← hYe]
        exact mem_ins_of_lt hT h3 hvl he (mem_comp_self (notMem_zone_of_lt hT h3 hvl he))
      have hp : Pc d = 0 := by
        by_contra h
        exact (mem_comp.1 h1').1 (zone_of_end (hPb h).2.2).1
      rw [hq, hp, add_zero]
    · rw [hcn.of_le _ (not_lt.1 hvl)]
      exact ⟨Iff.rfl, hvc, hvc⟩
  -- the two sides of the new cycle
  have hInA : ∀ v ∈ sideIn Cf Zf, cn v ∈ T₁.inC δ ∨
      (v ∈ ins Y ∧ cn v ∈ T₁.cycV δ ∧ lighter) := by
    intro v hv
    obtain ⟨hvf, d, hd, hdZ⟩ := mem_sideIn.1 hv
    by_cases hvY : v ∈ ins Y
    · have hδZ : M.face δ ∈ Zf := (hK2f _ (mem_ins.1 hvY d hd) _ hδY).1 hdZ
      rcases (hwantdef.1 (hwant.1 hδZ)) v hvY with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hvY, h⟩
    · left
      obtain ⟨hS, -, hvc⟩ := hconcS v hvY hvf
      obtain ⟨e, he, heY⟩ := hoff v hvY
      have heZ : M.face e ∈ Zf := (face_iff_of_notMem_verts bdf hvf hd he).1 hdZ
      rw [← hS, SpTree.mem_inC_iff hM hvc he]
      exact (hK1f _ heY).1 heZ
  have hInB : ∀ v ∈ sideOut Cf Zf, cn v ∈ T₁.outC δ ∨
      (v ∈ ins Y ∧ cn v ∈ T₁.cycV δ ∧ ¬ lighter) := by
    intro v hv
    obtain ⟨hvf, hvn⟩ := mem_sideOut.1 hv
    have hnoZ : ∀ d, M.vert d = v → M.face d ∉ Zf := fun d hd h =>
      hvn (mem_sideIn.2 ⟨hvf, d, hd, h⟩)
    obtain ⟨d, hd⟩ := hM.exists_dart v
    by_cases hvY : v ∈ ins Y
    · have hδZ : M.face δ ∉ Zf := fun h =>
        hnoZ d hd ((hK2f _ hδY _ (mem_ins.1 hvY d hd)).1 h)
      have hnw : ¬ want := fun h => hδZ (hwant.2 h)
      rw [hwantdef] at hnw
      push Not at hnw
      obtain ⟨v₁, hv₁, hn1, hn2⟩ := hnw
      rw [conc_eq_of_mem_ins hM hT h3 hcn hl2 hvY hv₁]
      by_cases hc : cn v₁ ∈ T₁.cycV δ
      · exact Or.inr ⟨hvY, hc, hn2 hc⟩
      · left
        simp only [SpTree.outC, mem_filter, mem_univ, true_and]
        exact ⟨hc, hn1⟩
    · left
      obtain ⟨hS, hcc, hvc⟩ := hconcS v hvY hvf
      obtain ⟨e, he, heY⟩ := hoff v hvY
      have hvin : v ∉ T₁.inC δ := fun h =>
        hnoZ e he ((hK1f _ heY).2 ((SpTree.mem_inC_iff hM hvc he).1 h))
      simp only [SpTree.outC, mem_filter, mem_univ, true_and]
      exact ⟨hcc, fun h => hvin (hS.2 h)⟩
  -- the weights
  have hsplit := T₁.sum_inC_add_sum_outC (wcf cn w) δ
  have htot : ∑ v, wcf cn w v ≤ 1 := by rw [sum_wcf]; exact h1
  have hcyc0 : ∀ u ∈ T₁.cycV δ, wcf cn w u ≤ ∑ v ∈ T₁.cycV δ, wcf cn w v := fun u hu =>
    single_le_sum (fun v _ => wcf_nonneg hw v) hu
  have hflexsum : ∀ (S : Finset P) (u : P), u ∈ T₁.cycV δ → (S = T₁.inC δ ∨ S = T₁.outC δ) →
      ∑ v ∈ S ∪ {u}, wcf cn w v = ∑ v ∈ S, wcf cn w v + wcf cn w u := by
    intro S u hu hS
    rw [sum_union (disjoint_singleton_right.2 fun h => ?_), sum_singleton]
    rcases hS with rfl | rfl
    · exact SpTree.notMem_cycV_of_mem_inC h hu
    · exact (mem_filter.1 h).2.1 hu
  refine ⟨Cf, Zf, ?_, isCycleSep_of_bd bdf, ?_, ?_⟩
  · rw [← Cf.card_verts]
    have hsub : Cf.verts ⊆ C.verts ∪ K₀ ∪ bandF T T₁ H l₀ l₂ a ∪ bandF T T₁ H l₀ l₂ b := by
      intro v hv
      rcases hCfv v hv with h | h | h | h <;> simp [h]
    have e1 := card_le_card hsub
    have e2 := card_union_le (C.verts ∪ K₀ ∪ bandF T T₁ H l₀ l₂ a) (bandF T T₁ H l₀ l₂ b)
    have e3 := card_union_le (C.verts ∪ K₀) (bandF T T₁ H l₀ l₂ a)
    have e4 := card_union_le C.verts K₀
    have e5 : #C.verts ≤ #(T.lvl l₂) :=
      card_le_card fun v hv => SpTree.mem_lvl.2 (hlevC v hv)
    have e6 := card_bandF (l₂ := l₂) hT hI a
    have e7 := card_bandF (l₂ := l₂) hT hI b
    omega
  · by_cases hflex : ∃ v₀ ∈ ins Y, cn v₀ ∈ T₁.cycV δ ∧ lighter
    · obtain ⟨v₀, hv₀, hc₀, hlt⟩ := hflex
      have hsub : ∀ v ∈ sideIn Cf Zf, cn v ∈ T₁.inC δ ∪ {cn v₀} := by
        intro v hv
        rcases hInA v hv with h | ⟨hvY, -, -⟩
        · exact mem_union_left _ h
        · exact mem_union_right _ (mem_singleton.2 (conc_eq_of_mem_ins hM hT h3 hcn hl2 hvY hv₀))
      have e1 := sum_le_sum_wcf hw hsub
      rw [hflexsum _ _ hc₀ (Or.inl rfl)] at e1
      have e3 := wc_le hM hT h3 hw hcn hl2 hv₀
      have e4 := hcyc0 _ hc₀
      rw [hlighter] at hlt
      rcases le_or_gt (1 / 3) (∑ v ∈ T₁.outC δ, wcf cn w v) with h | h <;> linarith
    · push Not at hflex
      have hsub : ∀ v ∈ sideIn Cf Zf, cn v ∈ T₁.inC δ := by
        intro v hv
        rcases hInA v hv with h | ⟨hvY, hc, hlt⟩
        · exact h
        · exact absurd hlt (hflex v hvY hc)
      exact (sum_le_sum_wcf hw hsub).trans hA
  · by_cases hflex : ∃ v₀ ∈ ins Y, cn v₀ ∈ T₁.cycV δ ∧ ¬ lighter
    · obtain ⟨v₀, hv₀, hc₀, hlt⟩ := hflex
      have hsub : ∀ v ∈ sideOut Cf Zf, cn v ∈ T₁.outC δ ∪ {cn v₀} := by
        intro v hv
        rcases hInB v hv with h | ⟨hvY, -, -⟩
        · exact mem_union_left _ h
        · exact mem_union_right _ (mem_singleton.2 (conc_eq_of_mem_ins hM hT h3 hcn hl2 hvY hv₀))
      have e1 := sum_le_sum_wcf hw hsub
      rw [hflexsum _ _ hc₀ (Or.inr rfl)] at e1
      have e3 := wc_le hM hT h3 hw hcn hl2 hv₀
      have e4 := hcyc0 _ hc₀
      rw [hlighter, not_le] at hlt
      rcases le_or_gt (1 / 3) (∑ v ∈ T₁.inC δ, wcf cn w v) with h | h <;> linarith
    · push Not at hflex
      have hsub : ∀ v ∈ sideOut Cf Zf, cn v ∈ T₁.outC δ := by
        intro v hv
        rcases hInB v hv with h | ⟨hvY, hc, hlt⟩
        · exact h
        · exact absurd (hflex v hvY hc) hlt
      exact (sum_le_sum_wcf hw hsub).trans hB

include hM htri hT hw h1 hI hl in
/-- **The deep case**: a dart both of whose faces avoid the levels `< l₂`. -/
theorem deep_case {cn : P → P} (hcn : IsConc T l₂ cn) {δ : D} (hδ : ¬ T₁.IsTree δ)
    (hδH : M.face δ ∈ H ∧ M.face (M.α δ) ∈ H)
    (hz1 : M.face δ ∉ M.zone (T.low l₂)) (hz2 : M.face (M.α δ) ∉ M.zone (T.low l₂))
    (hA : ∑ v ∈ T₁.inC δ, wcf cn w v ≤ 2 / 3) (hB : ∑ v ∈ T₁.outC δ, wcf cn w v ≤ 2 / 3)
    (hlight : ∀ f, f ∉ M.zone (T.low l₂) → ∑ v ∈ ins (M.comp (T.low l₂) f), w v ≤ 2 / 3) :
    ∃ (C : M.SCycle) (Z : Finset M.Face), C.k ≤ 2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂) ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      ∑ v ∈ sideIn C Z, w v ≤ 2 / 3 ∧ ∑ v ∈ sideOut C Z, w v ≤ 2 / 3 := by
  have hl2 : 1 ≤ l₂ := by omega
  obtain ⟨C, hCp, hC, -⟩ := hM.exists_scycle_comp T (root_mem_low hT hl2)
    (fun v hv => parent_mem_low hT hv) hz1
  exact deep_case_of_scycle hM htri hT hw h1 hI hl hcn hδ hδH hz1 hz2 hA hB hlight C hCp hC

end DeepCase

/-! ### The band theorem -/

section Band

variable (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ) {T : M.SpTree} (hT : IsBFS T)
  {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) (h1 : ∑ v, w v ≤ 1) {l₀ l₂ : ℕ} {H : Finset M.Face}
  {K₀ : Finset P} {c₀ : P} {T₁ : M.SpTree} (hI : Inner T w l₀ H K₀ c₀ T₁) (hl : l₀ < l₂)

include hM htri hT hw h1 hI hl in
/-- **The band theorem from a balanced dart.** For any concentration map `cn` at level `l₂`
(`PlanarSeparator.Map.IsConc`) and any dart `δ` off `T₁` whose fundamental cycle has strict
inside and strict outside of moved weight at most `2/3` each, there is a simple cycle separator
with at most `2 (l₂ - l₀) + #K₀ + #L` darts, `L` being the set of vertices of level `l₂`. -/
theorem band_separator_of_dart {cn : P → P} (hcn : IsConc T l₂ cn) {δ : D}
    (hδ : ¬ T₁.IsTree δ) (hA : ∑ v ∈ T₁.inC δ, wcf cn w v ≤ 2 / 3)
    (hB : ∑ v ∈ T₁.outC δ, wcf cn w v ≤ 2 / 3)
    (hlight : ∀ f, f ∉ M.zone (T.low l₂) → ∑ v ∈ ins (M.comp (T.low l₂) f), w v ≤ 2 / 3) :
    ∃ (C : M.SCycle) (Z : Finset M.Face), C.k ≤ 2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂) ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      ∑ v ∈ sideIn C Z, w v ≤ 2 / 3 ∧ ∑ v ∈ sideOut C Z, w v ≤ 2 / 3 := by
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (htri d).φ_three
  by_cases hbad : M.face δ ∉ H ∨ M.face (M.α δ) ∉ H
  · exfalso
    obtain ⟨hv, hf⟩ := hI.bad δ hδ hbad
    obtain ⟨v₀, hv₀⟩ : (ins H).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      have := hI.heavy
      rw [h, sum_empty] at this
      norm_num at this
    obtain ⟨e₀, he₀⟩ := hM.exists_dart v₀
    have hf₀ := mem_ins.1 hv₀ e₀ he₀
    -- the representatives of the strict inside of `H` lie in it
    have hconcH : ∀ v ∈ ins H, cn v ∈ ins H := by
      intro v hvH
      by_cases hvl : l₂ < T.height v
      · obtain ⟨e, he⟩ := hM.exists_dart v
        have hY := Yof_eq hT h3 hvl he
        have := cn_mem_ins hT h3 hcn hvl hM
        rw [hY] at this
        exact ins_mono (comp_subset_H hI hl (mem_ins.1 hvH e he)) this
      · rwa [hcn.of_le _ (not_lt.1 hvl)]
    have hside : ∀ v ∈ ins H, (v ∈ T₁.inC δ ↔ M.face e₀ ∈ T₁.inside δ) := by
      intro v hvH
      obtain ⟨e, he⟩ := hM.exists_dart v
      rw [SpTree.mem_inC_iff hM (hv v hvH) he]
      exact hf _ (mem_ins.1 hvH e he) _ hf₀
    by_cases hin : M.face e₀ ∈ T₁.inside δ
    · have := (sum_le_sum_wcf hw fun v hvH => (hside _ (hconcH v hvH)).2 hin).trans hA
      linarith [hI.heavy]
    · have hsub : ∀ v ∈ ins H, cn v ∈ T₁.outC δ := by
        intro v hvH
        simp only [SpTree.outC, mem_filter, mem_univ, true_and]
        exact ⟨hv _ (hconcH v hvH), fun h => hin ((hside _ (hconcH v hvH)).1 h)⟩
      have := (sum_le_sum_wcf hw hsub).trans hB
      linarith [hI.heavy]
  push Not at hbad
  by_cases hdeep : M.face δ ∉ M.zone (T.low l₂) ∧ M.face (M.α δ) ∉ M.zone (T.low l₂)
  · exact deep_case hM htri hT hw h1 hI hl hcn hδ hbad hdeep.1 hdeep.2 hA hB hlight
  · have hz : M.face δ ∈ M.zone (T.low l₂) ∨ M.face (M.α δ) ∈ M.zone (T.low l₂) := by
      by_contra h
      push Not at h
      exact hdeep h
    obtain ⟨C, Z, hk, rest⟩ := band_case hM htri hT hw hI hl hcn hδ hbad hz hA hB
    exact ⟨C, Z, by omega, rest⟩

include hM htri hT hw h1 hI hl in
/-- **The band theorem for any concentration map** `cn`
(`PlanarSeparator.Map.IsConc`): the balanced simple fundamental cycle of `T₁` for the weights
moved by `cn` (`PlanarSeparator.Map.SpTree.exists_simple_balanced`) gives a simple cycle
separator with at most `2 (l₂ - l₀) + #K₀ + #L` darts (`band_separator_of_dart`). -/
theorem exists_band_separator_of {cn : P → P} (hcn : IsConc T l₂ cn)
    (hlight : ∀ f, f ∉ M.zone (T.low l₂) → ∑ v ∈ ins (M.comp (T.low l₂) f), w v ≤ 2 / 3) :
    ∃ (C : M.SCycle) (Z : Finset M.Face), C.k ≤ 2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂) ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      ∑ v ∈ sideIn C Z, w v ≤ 2 / 3 ∧ ∑ v ∈ sideOut C Z, w v ≤ 2 / 3 := by
  obtain ⟨d₀, -⟩ := hM.exists_dart T.root
  obtain ⟨δ, hδ, hA, hB⟩ := T₁.exists_simple_balanced hM htri (wcf_nonneg (cn := cn) hw)
    (by rw [sum_wcf]; exact h1) d₀
  exact band_separator_of_dart hM htri hT hw h1 hI hl hcn hδ hA hB hlight

include hM htri hT hw h1 hI hl in
/-- **The band theorem.** Given an inner region at level `l₀` and a level `l₂ > l₀` at which
every component weighs at most `2/3`, there is a simple cycle separator with at most
`2 (l₂ - l₀) + #K₀ + #L` darts, `L` being the set of vertices of level `l₂`. -/
theorem exists_band_separator
    (hlight : ∀ f, f ∉ M.zone (T.low l₂) → ∑ v ∈ ins (M.comp (T.low l₂) f), w v ≤ 2 / 3) :
    ∃ (C : M.SCycle) (Z : Finset M.Face), C.k ≤ 2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂) ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      ∑ v ∈ sideIn C Z, w v ≤ 2 / 3 ∧ ∑ v ∈ sideOut C Z, w v ≤ 2 / 3 :=
  exists_band_separator_of hM htri hT hw h1 hI hl (isConc_conc T l₂) hlight

end Band

end Map

end PlanarSeparator
