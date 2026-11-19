module

public import PlanarFlow.BKMNW.FixPath
public import PlanarFlow.BKMNW.Pendant
public import PlanarFlow.BKMNW.MongeBridge

/-!
# FixConservationOnPath with frozen vertices

Line 9 of CycleToSingleSinkLimitedMaxFlow (Algorithm 5 of Borradaile, Klein, Mozes, Nussbaum and
Wulff-Nilsen, SIAM J. Comput. 46(4), 2017) runs FixConservationOnPath on the graph from which the
vertices `C - C⁺` of the cycle have been deleted (line 2), along a path of artificial arcs through
the vertices of `C⁺`. The fixed map `CombMap` cannot add arcs, and FixConservationOnPath along the
separator path itself may move flow at the deleted vertices, which lie on it.

**The modelling.** The vertices of a set `Del` are *frozen*: the darts touching them
(`incSet M Del`) keep their flow. The procedure runs along the separator path on the **map with a
pendant edge at every vertex** (`CombMap.pendant`, plane by `CombMap.pendant_isPlane`):

* the darts touching `Del` get capacity `0` (deleted, as in the article);
* the flow they carried out of a vertex `v` is carried, with exactly that capacity, by the pendant
  edge of `v`, whose other end is not on the path: FixConservationOnPath does not change the net
  outflow there, so the flow on the pendant edge, the net outflow of the frozen vertices, and the
  part of the net outflow of every vertex due to the frozen darts all stay as they are.

So the net outflows seen by the procedure are those of the whole flow (`div_pendant_eq`), it
changes them only at the vertices of the path that are not frozen, and no residual path leads from
a vertex of the path with positive inflow to one with negative inflow without using a frozen dart
(`fixFrozen_spec`).

The subroutines on the map with pendant edges come from those on the map (`msspP`, `negP`): its
dual graph is the dual graph of the map with a loop at a face for every pendant edge, and loops of
nonnegative length change no distance (`isDist_of_loops`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

/-! ### Loops of nonnegative length -/

section Loops

variable {X A B : Type*} {G : Digraph X A} {G' : Digraph X B}

/-- Every arc of `G'` is a copy of an arc of `G`, or a loop of nonnegative length. -/
def ArcsInOrLoop (G' : Digraph X B) (G : Digraph X A) : Prop :=
  ∀ b, (∃ a, G.src a = G'.src b ∧ G.dst a = G'.dst b ∧ G.len a = G'.len b) ∨
    (G'.src b = G'.dst b ∧ 0 ≤ G'.len b)

lemma ArcsInOrLoop.walk (h : ArcsInOrLoop G' G) {x y : X} {l : List B} (hl : IsWalk G' x l y) :
    ∃ l', IsWalk G x l' y ∧ wlen G l' ≤ wlen G' l := by
  induction l generalizing x with
  | nil => exact ⟨[], hl, by simp⟩
  | cons b l ih =>
    obtain ⟨h1, h2⟩ := hl
    obtain ⟨l', hl', hle⟩ := ih h2
    rcases h b with ⟨a, ha1, ha2, ha3⟩ | ⟨hb1, hb2⟩
    · exact ⟨a :: l', ⟨ha1.trans h1, by rw [ha2]; exact hl'⟩, by
        simp only [wlen_cons, ha3]; omega⟩
    · refine ⟨l', ?_, by simp only [wlen_cons]; omega⟩
      rw [← h1, hb1]; exact hl'

/-- **Loops of nonnegative length change no distance.** -/
theorem isDist_of_loops (h₁ : ArcsIn G G') (h₂ : ArcsInOrLoop G' G) {r : X}
    {δ : X → Option ℤ} (h : IsDist G r δ) : IsDist G' r δ where
  some_walk y ℓ hy := by
    obtain ⟨l, hl, he⟩ := h.some_walk y ℓ hy
    obtain ⟨l', hl', he'⟩ := h₁.walk hl
    exact ⟨l', hl', he'.trans he⟩
  some_le y ℓ hy l hl := by
    obtain ⟨l', hl', hle⟩ := h₂.walk hl
    exact (h.some_le y ℓ hy l' hl').trans hle
  none y hy l hl := by
    obtain ⟨l', hl', -⟩ := h₂.walk hl
    exact h.none y hy l' hl'

end Loops

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F} (e : V → D) (he : ∀ v, M.tail (e v) = v)

/-! ### Paths and subroutines on the map with pendant edges -/

/-- A simple path of the map, in the map with pendant edges. -/
def SPath.lift (π : SPath M) : SPath (M.pendant e he) where
  k := π.k
  d j := .inl (π.d j)
  p j := .inl (π.p j)
  tail_d j hj := by simp [π.tail_d j hj]
  head_d j hj := by simp [π.head_d j hj]
  inj i hi j hj h := π.inj i hi j hj (Sum.inl.inj h)

omit [Fintype F] [DecidableEq F] in
lemma SPath.lift_darts (π : SPath M) : (π.lift e he).darts = π.darts.map .inl := by
  simp only [SPath.darts, SPath.lift, List.map_flatMap, List.map_cons, List.map_nil]
  rfl

lemma SPath.lift_faces (π : SPath M) : (π.lift e he).faces = π.faces := by
  simp only [SPath.faces, SPath.lift_darts, List.map_map]
  rfl

omit [Fintype F] [DecidableEq F] in
lemma SPath.lift_verts (π : SPath M) : (π.lift e he).verts = π.verts.image .inl := by
  simp only [SPath.verts, SPath.init, Finset.image_image]
  rfl

variable {e he}

/-- MSSP on the map with pendant edges, from MSSP on the map. -/
def msspP (mssp : List D → (D → ℤ) → F → F → Option ℤ) :
    List (D ⊕ (V × Bool)) → (D ⊕ (V × Bool) → ℤ) → F → F → Option ℤ :=
  fun L ℓ => mssp (L.filterMap Sum.getLeft?) fun d => ℓ (.inl d)

/-- Shortest paths with negative lengths on the map with pendant edges, from those on the map: a
pendant edge of negative length is a negative closed walk. -/
def negP (neg : (D → ℤ) → Option (F → ℤ)) : (D ⊕ (V × Bool) → ℤ) → Option (F → ℤ) := by
  classical
  exact fun ℓ => if ∀ x : V × Bool, 0 ≤ ℓ (.inr x) then neg fun d => ℓ (.inl d) else none

theorem msspP_spec {mssp : List D → (D → ℤ) → F → F → Option ℤ} {π : SPath M}
    (h : MSSPSpecAt M mssp π) : MSSPSpecAt (M.pendant e he) (msspP mssp) (π.lift e he) := by
  intro ℓ hℓ x hx
  rw [SPath.lift_faces] at hx
  have hfm : (π.lift e he).darts.filterMap Sum.getLeft? = π.darts := by
    rw [SPath.lift_darts]; simp [List.filterMap_map, Function.comp_def]
  simp only [msspP, hfm]
  have hδ := h (fun d => ℓ (.inl d)) (fun d hd => hℓ _ (by
    rw [SPath.lift_darts]; simpa using hd)) x hx
  refine isDist_of_loops (fun a => ?_) (fun b => ?_) hδ
  · exact ⟨⟨.inl a.1, by rw [SPath.lift_darts]; simpa using a.2⟩, rfl, rfl, rfl⟩
  · obtain ⟨b, hb⟩ := b
    rcases b with d | ⟨v, t⟩
    · exact Or.inl ⟨⟨d, by rw [SPath.lift_darts] at hb; simpa using hb⟩, rfl, rfl, rfl⟩
    · exact Or.inr ⟨rfl, hℓ _ hb⟩

theorem negP_spec {neg : (D → ℤ) → Option (F → ℤ)} (h : NegSSSPSpec M neg) :
    NegSSSPSpec (M.pendant e he) (negP neg) := by
  intro ℓ
  by_cases hn : ∀ x : V × Bool, 0 ≤ ℓ (.inr x)
  · simp only [negP, hn, implies_true, ite_true]
    have := h fun d => ℓ (.inl d)
    cases hc : neg fun d => ℓ (.inl d) with
    | none =>
      rw [hc] at this
      obtain ⟨m, c, hcw, hlt⟩ := this
      exact ⟨m, fun t => .inl (c t), hcw, hlt⟩
    | some p =>
      rw [hc] at this
      rintro (d | x)
      · exact this d
      · show p _ ≤ p _ + ℓ (.inr x)
        have := hn x
        rcases x with ⟨v, t⟩
        show p (M.face (e v)) ≤ p (M.face (e v)) + _
        omega
  · push Not at hn
    obtain ⟨x, hx⟩ := hn
    simp only [negP, show ¬ ∀ x : V × Bool, 0 ≤ ℓ (.inr x) from fun h' => by
      have := h' x; omega, ite_false]
    rcases x with ⟨v, t⟩
    refine ⟨1, fun _ => .inr (v, t), ⟨by omega, fun t ht => by omega, rfl⟩, ?_⟩
    simp [Digraph.walkLen, dualGraph, hx]

/-! ### Net outflows on the map with pendant edges -/

omit [Fintype F] [DecidableEq F] in
lemma div_pendant_inl (hp : D ⊕ (V × Bool) → ℤ) (v : V) :
    (M.pendant e he).div hp (.inl v) = (∑ d with M.tail d = v, hp (.inl d)) + hp (.inr (v, true)) := by
  rw [CombMap.div, Finset.sum_filter, Fintype.sum_sum_type, Finset.sum_filter]
  congr 1 <;> simp [Fintype.sum_prod_type]

omit [Fintype F] [DecidableEq F] in
lemma div_pendant_inr (hp : D ⊕ (V × Bool) → ℤ) (v : V) :
    (M.pendant e he).div hp (.inr v) = hp (.inr (v, false)) := by
  rw [CombMap.div, Finset.sum_filter, Fintype.sum_sum_type]
  simp [Fintype.sum_prod_type]

/-! ### The procedure -/

variable (M) in
/-- The darts touching the frozen vertices. -/
def incSet (Del : Finset V) : Finset D := univ.filter fun d => M.tail d ∈ Del ∨ M.head d ∈ Del

lemma rev_mem_incSet {Del : Finset V} {d : D} : M.rev d ∈ incSet M Del ↔ d ∈ incSet M Del := by
  simp [incSet, or_comm]

variable (M) in
/-- The net outflow due to the frozen darts. -/
def frozenOut (f₁ : D → ℤ) (Del : Finset V) (v : V) : ℤ :=
  ∑ d with M.tail d = v ∧ d ∈ incSet M Del, f₁ d

variable (M) in
/-- The capacities on the map with pendant edges. -/
def frCap (U f₁ : D → ℤ) (Del : Finset V) : D ⊕ (V × Bool) → ℤ
  | .inl d => if d ∈ incSet M Del then 0 else U d
  | .inr (v, true) => max (frozenOut M f₁ Del v) 0
  | .inr (v, false) => max (- frozenOut M f₁ Del v) 0

variable (M) in
/-- The initial flow on the map with pendant edges. -/
def frFlow (f₁ : D → ℤ) (Del : Finset V) : D ⊕ (V × Bool) → ℤ
  | .inl d => if d ∈ incSet M Del then 0 else f₁ d
  | .inr (v, true) => frozenOut M f₁ Del v
  | .inr (v, false) => - frozenOut M f₁ Del v

variable (M e he) in
/-- **FixConservationOnPath along `π` with the vertices of `Del` frozen**, run on the map with
pendant edges. -/
noncomputable def fixFrozen (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F)
    (neg : (D → ℤ) → Option (F → ℤ)) (U f₁ : D → ℤ) (π : SPath M) (Del : Finset V) : D → ℤ :=
  fun d => if d ∈ incSet M Del then f₁ d else
    fixPath (M.pendant e he) (frCap M U f₁ Del) (frFlow M f₁ Del) (π.lift e he) (msspP mssp) fr
      (negP neg) (.inl d)

/-- The net outflow on the map with pendant edges, for a flow vanishing on the frozen darts and
carrying the frozen outflow on the pendant edges, is that of the whole flow. -/
lemma div_pendant_eq {Del : Finset V} {f₁ : D → ℤ} {hp : D ⊕ (V × Bool) → ℤ}
    (hz : ∀ d ∈ incSet M Del, hp (.inl d) = 0)
    (hpe : ∀ v, hp (.inr (v, true)) = frozenOut M f₁ Del v) (v : V) :
    (M.pendant e he).div hp (.inl v) =
      M.div (fun d => if d ∈ incSet M Del then f₁ d else hp (.inl d)) v := by
  rw [div_pendant_inl, hpe, frozenOut, CombMap.div, Finset.sum_ite, Finset.filter_filter,
    Finset.filter_filter, add_comm]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun d => d ∈ incSet M Del), Finset.filter_filter,
    Finset.filter_filter, Finset.sum_eq_zero (fun d hd => hz d (by simp at hd; exact hd.2)),
    zero_add]

/-- **The specification of FixConservationOnPath with frozen vertices.** -/
theorem fixFrozen_spec (hM : M.IsPlane) {U f₁ : D → ℤ} (hU : ∀ d, 0 ≤ U d)
    (hf₁ : IsPseudo M U f₁) {π : SPath M} {mssp : List D → (D → ℤ) → F → F → Option ℤ}
    (hmssp : MSSPSpecAt M mssp π) {fr : FRFun F} (hfr : FRSpec fr)
    {neg : (D → ℤ) → Option (F → ℤ)} (hneg : NegSSSPSpec M neg) (Del : Finset V) :
    IsPseudo M U (fixFrozen M e he mssp fr neg U f₁ π Del) ∧
      (∀ d ∈ incSet M Del, fixFrozen M e he mssp fr neg U f₁ π Del d = f₁ d) ∧
      (∀ v, (v ∉ π.verts ∨ v ∈ Del) →
        M.div (fixFrozen M e he mssp fr neg U f₁ π Del) v = M.div f₁ v) ∧
      ∃ Z, π.verts.filter (fun v => M.div (fixFrozen M e he mssp fr neg U f₁ π Del) v < 0) ⊆ Z ∧
        Disjoint Z (π.verts.filter fun v => 0 < M.div (fixFrozen M e he mssp fr neg U f₁ π Del) v) ∧
        ∀ d, d ∉ incSet M Del → M.tail d ∈ Z → M.head d ∉ Z →
          fixFrozen M e he mssp fr neg U f₁ π Del d = U d := by
  classical
  have hcap : ∀ x, 0 ≤ frCap M U f₁ Del x := by
    rintro (d | ⟨v, _ | _⟩)
    · simp only [frCap]; split_ifs
      · exact le_rfl
      · exact hU d
    · exact le_max_right _ _
    · exact le_max_right _ _
  have hp₀ : IsPseudo (M.pendant e he) (frCap M U f₁ Del) (frFlow M f₁ Del) := by
    refine ⟨?_, ?_⟩
    · rintro (d | ⟨v, _ | _⟩)
      · show frFlow M f₁ Del (.inl (M.rev d)) = _
        simp only [frFlow, rev_mem_incSet, hf₁.antisymm d]
        split_ifs <;> simp
      · show frFlow M f₁ Del (.inr (v, true)) = _
        simp [frFlow]
      · show frFlow M f₁ Del (.inr (v, false)) = _
        simp [frFlow]
    · rintro (d | ⟨v, _ | _⟩)
      · simp only [frFlow, frCap]; split_ifs
        · exact le_rfl
        · exact hf₁.le_cap d
      · exact le_max_left _ _
      · exact le_max_left _ _
  have hfix := fixPath_spec (pendant_isPlane he hM) hcap hp₀ (π.lift e he) (msspP_spec hmssp) hfr
    (negP_spec hneg)
  unfold fixFrozen
  generalize fixPath (M.pendant e he) (frCap M U f₁ Del) (frFlow M f₁ Del) (π.lift e he)
    (msspP mssp) fr (negP neg) = hp at hfix
  obtain ⟨hps, heq, hnp⟩ := hfix
  have hz : ∀ d ∈ incSet M Del, hp (.inl d) = 0 := by
    intro d hd
    have h1 := hps.le_cap (.inl d)
    have h2 := hps.le_cap (.inl (M.rev d))
    have h3 := hps.antisymm (.inl d)
    simp only [frCap, hd, rev_mem_incSet, ite_true] at h1 h2
    change hp (.inl (M.rev d)) = _ at h3
    omega
  have hinr : ∀ v, Sum.inr v ∉ (π.lift e he).verts := by
    intro v; rw [SPath.lift_verts]; simp
  have hpe : ∀ v, hp (.inr (v, true)) = frozenOut M f₁ Del v := by
    intro v
    have h1 := heq (.inr v) (hinr v)
    rw [div_pendant_inr, div_pendant_inr] at h1
    have h2 := hps.antisymm (.inr (v, true))
    change hp (.inr (v, false)) = _ at h2
    simp only [frFlow] at h1
    omega
  have hz₀ : ∀ d ∈ incSet M Del, frFlow M f₁ Del (.inl d) = 0 := fun d hd => by
    simp [frFlow, hd]
  have hpe₀ : ∀ v, frFlow M f₁ Del (.inr (v, true)) = frozenOut M f₁ Del v := fun v => rfl
  have hd₀ : ∀ v, (M.pendant e he).div (frFlow M f₁ Del) (.inl v) = M.div f₁ v := by
    intro v
    rw [div_pendant_eq hz₀ hpe₀]
    congr 1; funext d; simp only [frFlow]; split_ifs <;> rfl
  have hd₂ : ∀ v, (M.pendant e he).div hp (.inl v) =
      M.div (fun d => if d ∈ incSet M Del then f₁ d else hp (.inl d)) v :=
    div_pendant_eq hz hpe
  have hmem : ∀ v, Sum.inl v ∈ (π.lift e he).verts ↔ v ∈ π.verts := by
    intro v; rw [SPath.lift_verts]; simp
  refine ⟨⟨fun d => ?_, fun d => ?_⟩, fun d hd => by simp [hd], fun v hv => ?_, ?_⟩
  · simp only [rev_mem_incSet]
    split_ifs with h
    · exact hf₁.antisymm d
    · exact hps.antisymm (.inl d)
  · split_ifs with h
    · exact hf₁.le_cap d
    · have := hps.le_cap (.inl d); simpa [frCap, h] using this
  · rcases hv with hv | hv
    · rw [← hd₂, heq (.inl v) (by rwa [hmem]), hd₀]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [mem_filter, mem_univ, true_and] at hd
      have : d ∈ incSet M Del := by simp [incSet, hd, hv]
      simp [this]
  · obtain ⟨Z', hZ1, hZ2, hZ3⟩ := hnp
    refine ⟨univ.filter fun v => Sum.inl v ∈ Z', fun v hv => ?_, ?_, fun d hd h1 h2 => ?_⟩
    · simp only [mem_filter] at hv
      simp only [mem_filter, mem_univ, true_and]
      exact hZ1 (mem_filter.2 ⟨(hmem v).2 hv.1, by rw [hd₂]; exact hv.2⟩)
    · rw [disjoint_left]
      intro v hv hv'
      simp only [mem_filter, mem_univ, true_and] at hv hv'
      exact disjoint_left.1 hZ2 hv (mem_filter.2 ⟨(hmem v).2 hv'.1, by rw [hd₂]; exact hv'.2⟩)
    · simp only [mem_filter, mem_univ, true_and] at h1 h2
      have := hZ3 (.inl d) h1 h2
      simp only [hd, ite_false]
      simpa [frCap, hd] using this

end BKMNW

end PlanarFlow
