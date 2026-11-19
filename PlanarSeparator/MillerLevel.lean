module

public import PlanarSeparator.MillerTree
public import PlanarSeparator.Levels

/-!
# Breadth-first levels of a plane map and the regions they bound

A *breadth-first tree* of a map (`PlanarSeparator.Map.IsBFS`) is a spanning tree whose height is
the distance from the root: the heights of the two ends of an edge differ by at most one and the
parent of a vertex is one level lower. Every plane map has one from any root
(`PlanarSeparator.Map.exists_bfs`).

In a map whose faces are triangles, the faces avoiding the vertices of level `< l` fall into
components (`PlanarSeparator.Map.comp`). The boundary of a component is a simple cycle all of whose
vertices have level `l` (`PlanarSeparator.Map.level_eq_of_mem_verts`); the vertices all of whose
faces lie in a component (its strict inside, `PlanarSeparator.Map.ins`) have level `> l`, and a
vertex of level `> l` lies in the strict inside of the component of any of its faces.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

open Finset

namespace Map

variable {D P : Type*} {M : Map D P}

/-! ### Breadth-first trees -/

/-- A spanning tree is *breadth-first* if its height is the distance from the root. -/
structure IsBFS [DecidableEq P] (T : M.SpTree) : Prop where
  step : ∀ d, T.height (M.vert (M.α d)) ≤ T.height (M.vert d) + 1
  parent : ∀ v (h : v ≠ T.root), T.height (M.vert (M.α (T.par v h))) + 1 = T.height v
  root : T.height T.root = 0

variable (M) in
/-- The graph of a map, without its loops. -/
def graph : SimpleGraph P where
  Adj u v := u ≠ v ∧ ∃ d, M.vert d = u ∧ M.vert (M.α d) = v
  symm := ⟨fun u v h => ⟨h.1.symm, by
    obtain ⟨d, rfl, rfl⟩ := h.2
    exact ⟨M.α d, rfl, by rw [M.α_α]⟩⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

section BFS

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

open Classical in
/-- **Every plane map has a breadth-first tree** from any root. -/
theorem exists_bfs (hM : M.IsPlane) (r : P) : ∃ T : M.SpTree, T.root = r ∧ IsBFS T := by
  classical
  have hreach : Reaches M.graph {r} univ := by
    refine ⟨subset_univ _, fun y hy => ⟨r, mem_singleton_self r, ?_⟩⟩
    obtain ⟨d₀, hd₀⟩ := hM.exists_dart r
    obtain ⟨d, hd⟩ := hM.exists_dart y
    have := hM.connected.reach_vert d₀ d
    rw [hd₀, hd] at this
    clear hd hy
    induction this with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b _ hab ih =>
      obtain ⟨e, rfl, rfl⟩ := hab
      by_cases he : M.vert e = M.vert (M.α e)
      · rwa [← he]
      · exact ih.tail ⟨⟨he, e, rfl, rfl⟩, mem_univ _⟩
  set lv := lev M.graph {r} univ
  have hpar : ∀ v, v ≠ r → ∃ d, M.vert d = v ∧ lv (M.vert (M.α d)) + 1 = lv v := by
    intro v hv
    obtain ⟨u, -, ⟨-, d, hd, hdu⟩, hu⟩ :=
      hreach.exists_parent (mem_univ v) (by simpa using hv)
    exact ⟨d, hd, by rw [hdu]; exact hu⟩
  let T : M.SpTree :=
    { root := r
      par := fun v h => (hpar v h).choose
      height := lv
      vert_par := fun v h => (hpar v h).choose_spec.1
      height_lt := fun v h => by
        have := (hpar v h).choose_spec.2
        omega }
  refine ⟨T, rfl, ?_, ?_, ?_⟩
  · intro d
    by_cases he : M.vert d = M.vert (M.α d)
    · rw [← he]; omega
    · exact hreach.lev_le_lev_add_one (mem_univ _) (mem_univ _) ⟨he, d, rfl, rfl⟩
  · intro v h
    exact (hpar v h).choose_spec.2
  · exact (hreach.lev_eq_zero_iff (mem_univ _)).2 (mem_singleton_self r)

end BFS

namespace IsBFS

variable [Fintype D] [DecidableEq D] [DecidableEq P] {T : M.SpTree} (hT : IsBFS T)
include hT

lemma step' (d : D) : T.height (M.vert d) ≤ T.height (M.vert (M.α d)) + 1 := by
  have := hT.step (M.α d)
  rwa [M.α_α] at this

lemma height_parent {v : P} (h : v ≠ T.root) : T.height (T.parent v) + 1 = T.height v := by
  rw [T.parent_of_ne h]
  exact hT.parent v h

lemma eq_root_of_height {v : P} (h : T.height v = 0) : v = T.root := by
  by_contra hv
  have := hT.height_parent hv
  omega

/-- The level of the ancestor `n` steps up. -/
lemma height_iterate {v : P} {n : ℕ} (hn : n ≤ T.height v) :
    T.height (T.parent^[n] v) + n = T.height v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h1 := ih (by omega)
    have hne : T.parent^[n] v ≠ T.root := fun h => by
      rw [h, hT.root] at h1
      omega
    have := hT.height_parent hne
    omega

/-- The corners of a triangle are at most one level apart. -/
lemma corner {d d' : D} (h3 : M.φ (M.φ (M.φ d)) = d) (hf : M.face d' = M.face d) :
    T.height (M.vert d') ≤ T.height (M.vert d) + 1 := by
  rcases M.eq_of_face_eq_of_φ_three h3 hf with rfl | rfl | rfl
  · omega
  · rw [M.vert_φ]
    exact hT.step d
  · have := hT.step' (M.φ (M.φ d))
    rwa [show M.vert (M.α (M.φ (M.φ d))) = M.vert d by rw [← M.vert_φ, h3]] at this

end IsBFS

/-! ### Regions -/

section Regions

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

open Classical in
/-- The vertices all of whose faces lie in `W`: the strict inside of `W`. -/
noncomputable def ins (W : Finset M.Face) : Finset P := {v | ∀ d, M.vert d = v → M.face d ∈ W}

lemma mem_ins {W : Finset M.Face} {v : P} : v ∈ ins W ↔ ∀ d, M.vert d = v → M.face d ∈ W := by
  classical
  simp [ins]

lemma ins_mono {W W' : Finset M.Face} (h : W ⊆ W') : ins W ⊆ ins W' := fun _ hv =>
  mem_ins.2 fun d hd => h (mem_ins.1 hv d hd)

variable (T : M.SpTree)

open Classical in
/-- The vertices of level `< l`. -/
noncomputable def SpTree.low (l : ℕ) : Finset P := {v | T.height v < l}

lemma mem_low {l : ℕ} {v : P} : v ∈ T.low l ↔ T.height v < l := by
  classical
  simp [SpTree.low]

lemma notMem_zone_iff {B : Finset P} {f : M.Face} :
    f ∉ M.zone B ↔ ∀ d, M.face d = f → M.vert d ∉ B := by
  rw [mem_zone]
  unfold Touch
  push Not
  rfl

variable {T}

lemma root_mem_low (hT : IsBFS T) {l : ℕ} (hl : 1 ≤ l) : T.root ∈ T.low l := by
  rw [mem_low, hT.root]
  omega

lemma parent_mem_low (hT : IsBFS T) {l : ℕ} {v : P} (hv : v ∈ T.low l) :
    T.parent v ∈ T.low l := by
  rw [mem_low] at *
  by_cases h : v = T.root
  · subst h
    simpa [SpTree.parent] using hv
  · have := hT.height_parent h
    omega

/-- The components get smaller as the level grows. -/
lemma comp_mono {l l' : ℕ} (hll : l ≤ l') {f g : M.Face} (hg : g ∈ M.comp (T.low l') f) :
    g ∈ M.comp (T.low l) f := by
  have hsub : M.zone (T.low l) ⊆ M.zone (T.low l') := fun x hx => by
    obtain ⟨d, rfl, hd⟩ := mem_zone.1 hx
    exact face_mem_zone (by rw [mem_low] at *; omega)
  obtain ⟨h1, h2⟩ := mem_comp.1 hg
  refine mem_comp.2 ⟨fun h => h1 (hsub h), Relation.ReflTransGen.mono (fun x y hxy => ?_) _ _ h2⟩
  exact ⟨mem_compl.2 fun h => mem_compl.1 hxy.1 (hsub h),
    mem_compl.2 fun h => mem_compl.1 hxy.2.1 (hsub h), hxy.2.2⟩

/-- **All faces at a vertex of level `> l` lie in one component.** -/
lemma mem_comp_of_lt (hT : IsBFS T) (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d) {l : ℕ} {v : P}
    (hv : l < T.height v) {f : M.Face} {d d' : D} (hd : M.vert d = v) (hd' : M.vert d' = v)
    (hdf : M.face d ∈ M.comp (T.low l) f) : M.face d' ∈ M.comp (T.low l) f := by
  have havoid : ∀ e, M.vert e = v → M.face e ∉ M.zone (T.low l) := by
    intro e he
    rw [notMem_zone_iff]
    intro e' he'
    have h2 : T.height (M.vert e) ≤ T.height (M.vert e') + 1 := hT.corner (h3 e') he'.symm
    rw [mem_low]
    rw [he] at h2
    omega
  obtain ⟨n, rfl⟩ := M.exists_σ_pow_eq (hd.trans hd'.symm)
  have hr := rtg_face_σ_pow (W := (M.zone (T.low l))ᶜ) (fun e he => mem_compl.2 (havoid e he))
    hd n
  obtain ⟨-, h2⟩ := mem_comp.1 hdf
  exact mem_comp.2 ⟨havoid _ (by rw [M.vert_σ_pow, hd]), h2.trans hr⟩

/-- A vertex of level `> l` with a face in a component lies in its strict inside. -/
lemma mem_ins_of_lt (hT : IsBFS T) (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d) {l : ℕ} {v : P}
    (hv : l < T.height v) {f : M.Face} {d : D} (hd : M.vert d = v)
    (hdf : M.face d ∈ M.comp (T.low l) f) : v ∈ ins (M.comp (T.low l) f) :=
  mem_ins.2 fun _ hd' => mem_comp_of_lt hT h3 hv hd hd' hdf

/-- The strict inside of a component (at a level `l ≥ 1`) lies above level `l`. -/
lemma lt_of_mem_ins (hM : M.IsPlane) (hT : IsBFS T) {l : ℕ} (hl : 1 ≤ l) {f : M.Face} {v : P}
    (hv : v ∈ ins (M.comp (T.low l) f)) : l < T.height v := by
  obtain ⟨d, hd⟩ := hM.exists_dart v
  have h1 := (mem_comp.1 (mem_ins.1 hv d hd)).1
  rw [notMem_zone_iff] at h1
  have h2 := h1 d rfl
  rw [mem_low, hd] at h2
  by_contra hle
  have hvr : v ≠ T.root := fun h => by rw [h, hT.root] at h2; omega
  have he := (mem_comp.1 (mem_ins.1 hv _ (T.vert_par v hvr))).1
  rw [notMem_zone_iff] at he
  have := he (M.φ (T.par v hvr)) (M.face_φ _)
  rw [mem_low, M.vert_φ] at this
  have := hT.parent v hvr
  omega

/-- A vertex touching a set of faces and its complement lies on the boundary cycle. -/
lemma mem_verts_of_touch {C : M.SCycle} {W : Finset M.Face}
    (hC : ∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) ↔ ¬ C.Mem d) {d d' : D}
    (hdd : M.vert d = M.vert d') (h1 : M.face d ∈ W) (h2 : M.face d' ∉ W) :
    M.vert d ∈ C.verts := by
  by_contra hv
  exact h2 ((face_iff_of_notMem_verts hC hv rfl hdd.symm).1 h1)

/-- Components of faces containing a common face are equal. -/
lemma comp_eq_of_mem {B : Finset P} {f g : M.Face} (hg : g ∈ M.comp B f) :
    M.comp B g = M.comp B f := by
  obtain ⟨-, hfg⟩ := mem_comp.1 hg
  ext x
  rw [mem_comp, mem_comp]
  constructor
  · rintro ⟨hx, hgx⟩
    exact ⟨hx, hfg.trans hgx⟩
  · rintro ⟨hx, hfx⟩
    exact ⟨hx, (rtg_symm (fun _ _ h => FAdj.symm h) hfg).trans hfx⟩

/-- **Both ends of an edge leaving a component lie at its level.** -/
lemma level_of_bd (hT : IsBFS T) (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d) {l : ℕ} {f : M.Face}
    {d : D} (h1 : M.face d ∈ M.comp (T.low l) f) (h2 : M.face (M.α d) ∉ M.comp (T.low l) f) :
    T.height (M.vert d) = l ∧ T.height (M.vert (M.α d)) = l := by
  have hz : M.face (M.α d) ∈ M.zone (T.low l) := by
    by_contra hz
    exact h2 (mem_comp_of_adj h1 hz)
  obtain ⟨hd, hαd, hy⟩ := bd_comp_triangle (h3 (M.α d)) h1 hz
  rw [mem_low] at hd hαd hy
  have e1 := hT.corner (d := M.φ (M.φ (M.α d))) (d' := M.α d) (h3 _)
    (by rw [M.face_φ, M.face_φ])
  have e2 := hT.corner (d := M.φ (M.φ (M.α d))) (d' := M.φ (M.α d)) (h3 _)
    (by rw [M.face_φ, M.face_φ, M.face_φ])
  rw [M.vert_φ, M.α_α] at e2
  omega

/-- **The boundary cycle of a component lies at its level.** -/
lemma level_of_mem_verts (hT : IsBFS T) (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d) {l : ℕ}
    {f : M.Face} {C : M.SCycle}
    (hC : ∀ d, (M.face d ∈ M.comp (T.low l) f ↔ M.face (M.α d) ∈ M.comp (T.low l) f) ↔
      ¬ C.Mem d) {v : P} (hv : v ∈ C.verts) : T.height v = l := by
  obtain ⟨i, hi, rfl⟩ := C.mem_verts.1 hv
  have hb := (hC (C.d i)).not.2 (not_not.2 (C.mem_d hi))
  by_cases h1 : M.face (C.d i) ∈ M.comp (T.low l) f
  · exact (level_of_bd hT h3 h1 fun h2 => hb (iff_of_true h1 h2)).1
  · have h2 : M.face (M.α (C.d i)) ∈ M.comp (T.low l) f := by tauto
    have := (level_of_bd hT h3 h2 (by rwa [M.α_α])).2
    rwa [M.α_α] at this

end Regions

end Map

end PlanarSeparator
