module

public import PlanarSeparator.MillerInner

/-!
# The band theorem with explicit choices

The band theorem of Miller's argument (`PlanarSeparator.Map.exists_band_separator`,
`PlanarSeparator.Map.band_separator_of_dart`) is a case analysis on a balanced dart `δ` of the
tree `T₁` of an inner region, whose choices are existential. This file makes every choice
explicit, as a function `PlanarSeparator.Map.bandSep` of computable data, and proves that its
value is a simple cycle separator with the bound of the band theorem
(`PlanarSeparator.Map.band_separator_explicit`).

* **The boundary cycle** of a set of faces `W` from a dart `x₀` leaving it
  (`PlanarSeparator.Map.Out`): the darts `bdD W x₀ i = turnOutⁱ x₀`, where `turnOut W x` is the
  first dart `σʲ (α x)` (`j ≥ 0`) around the head of `x` leaving `W`, and `bdK W` of them, the
  number of darts leaving `W` (`PlanarSeparator.Map.bdCycle`, `PlanarSeparator.Map.bdCycle_spec`:
  whenever some proper simple cycle bounds `W`, these darts form one).
* **The ancestor at level `l₂`** of a vertex `u` in `T₁`: the first iterated parent of level
  `≤ l₂` (`PlanarSeparator.Map.topA`, `PlanarSeparator.Map.topA_eq`).
* **The rerouting options** (`PlanarSeparator.Map.arcOpt`): the fundamental cycle of the last
  dart of an arc of the boundary cycle in the tree redirected along the arc
  (`PlanarSeparator.Map.SpTree.arcTree`), with its inside or the complement, whichever agrees
  with the inside of `δ` at a given face `g₀` off the component.
* **The case analysis** (`PlanarSeparator.Map.bandSep`): if a face of `δ` touches the levels
  `< l₂`, the fundamental cycle of `δ` in `T₁` with its inside; otherwise, with `Y` the
  component of `δ` at level `l₂`, `C` its boundary cycle from `x₀` and `a`, `b` the ancestors at
  level `l₂` of the tail and the head of `δ` (`PlanarSeparator.Map.deepSep`): `C` with `Y` if
  `a = b` or `Y` weighs at least `1/3`; otherwise the arc option from `b` to `a`, if it puts the
  face of `δ` on the wanted side (`PlanarSeparator.Map.deepWant`: the side of the representative
  of `Y`, or the lighter side if the representative lies on the cycle of `δ`), and the arc option
  from `a` to `b` otherwise (`PlanarSeparator.Map.deepPick`).

The function takes, besides the data of the earlier steps (the trees `T` and `T₁`, the level
`l₂`, the concentration map `cn`, the weights `w`) and the dart `δ`, a dart `x₀` leaving the
component of `δ` (needed in the deep case only) and a face `g₀` touching the levels `< l₂`
(for instance the face of a dart at the root); the theorem holds for any such choices.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

open Finset

namespace Map

variable {D P : Type*} {M : Map D P} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-! ### Copying a simple cycle onto given data -/

/-- A simple cycle with given darts, equal to those of `C` at the indices `< C.k`. -/
def SCycle.copy (C : M.SCycle) (k : ℕ) (d : ℕ → D) (hk : C.k = k)
    (hd : ∀ i < C.k, C.d i = d i) : M.SCycle where
  k := k
  d := d
  pos := hk ▸ C.pos
  vert_α i hi := by
    subst hk
    rw [← hd i hi, ← hd _ (Nat.mod_lt _ C.pos)]
    exact C.vert_α i hi
  inj i hi j hj h := by
    subst hk
    rw [← hd i hi, ← hd j hj] at h
    exact C.inj i hi j hj h

lemma SCycle.mem_copy (C : M.SCycle) {k : ℕ} {d : ℕ → D} {hk : C.k = k}
    {hd : ∀ i < C.k, C.d i = d i} {x : D} : (C.copy k d hk hd).Mem x ↔ C.Mem x := by
  subst hk
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, by rw [hd i hi]; exact h⟩
  · rintro ⟨i, hi, h⟩
    refine ⟨i, hi, ?_⟩
    show x = d i ∨ x = M.α (d i)
    rw [← hd i hi]
    exact h

lemma SCycle.copy_proper (C : M.SCycle) {k : ℕ} {d : ℕ → D} {hk : C.k = k}
    {hd : ∀ i < C.k, C.d i = d i} (hC : C.Proper) : (C.copy k d hk hd).Proper := by
  subst hk
  intro h2
  have h2' : C.k = 2 := h2
  show d 0 ≠ M.α (d 1)
  rw [← hd 0 (by omega), ← hd 1 (by omega)]
  exact hC h2'

/-! ### The boundary cycle of a set of faces, explicitly -/

/-- A dart leaving a set of faces `W`: its face lies in `W`, that of its reversal does not. -/
def Out (W : Finset M.Face) (x : D) : Prop := M.face x ∈ W ∧ M.face (M.α x) ∉ W

open Classical in
/-- **Turning to the next dart leaving `W`**: the first dart `σʲ (α x)` (`j ≥ 0`) around the head
of `x` which leaves `W` (`x` itself if there is none). -/
noncomputable def turnOut (W : Finset M.Face) (x : D) : D :=
  if h : ∃ j, Out W ((M.σ ^ j) (M.α x)) then (M.σ ^ Nat.find h) (M.α x) else x

lemma turnOut_spec {W : Finset M.Face} {x y : D} (hy : Out W y)
    (hyv : M.vert y = M.vert (M.α x)) :
    Out W (turnOut W x) ∧ M.vert (turnOut W x) = M.vert (M.α x) := by
  classical
  obtain ⟨n, hn⟩ := M.exists_σ_pow_eq hyv.symm
  have h : ∃ j, Out W ((M.σ ^ j) (M.α x)) := ⟨n, hn ▸ hy⟩
  rw [turnOut, dite_eq_left_of_eq_true (eq_true h)]
  exact ⟨Nat.find_spec h, M.vert_σ_pow _ _⟩

/-- The darts of the boundary cycle of `W` from `x₀`: `x₀` and the darts reached by turning. -/
noncomputable def bdD (W : Finset M.Face) (x₀ : D) (i : ℕ) : D := (turnOut W)^[i] x₀

open Classical in
/-- The number of darts of the boundary cycle: the number of darts leaving `W`. -/
noncomputable def bdK (W : Finset M.Face) : ℕ := #{x | Out W x}

/-- **The boundary cycle by turning.** If some proper simple cycle bounds `W` and `x₀` leaves
`W`, then the darts `bdD W x₀ i`, `i < bdK W`, are the darts of a proper simple cycle bounding
`W`. -/
theorem exists_bdCycle {W : Finset M.Face} {x₀ : D}
    (hex : ∃ C : M.SCycle, C.Proper ∧ ∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) ↔ ¬ C.Mem d)
    (hx₀ : Out W x₀) :
    ∃ C : M.SCycle, C.Proper ∧ C.k = bdK W ∧ (∀ i < C.k, C.d i = bdD W x₀ i) ∧
      (∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) ↔ ¬ C.Mem d) := by
  classical
  obtain ⟨C, hCp, hC⟩ := hex
  obtain ⟨C', hCp', h0, -, hC', hS⟩ := exists_oriented C hCp hC hx₀.1 hx₀.2
  have huniq : ∀ y y', Out W y → Out W y' → M.vert y = M.vert y' → y = y' := by
    intro y y' hy hy' hv
    obtain ⟨i, hi, rfl⟩ := (hS y).1 hy
    obtain ⟨j, hj, rfl⟩ := (hS y').1 hy'
    rw [C'.inj i hi j hj hv]
  have hd : ∀ i < C'.k, C'.d i = bdD W x₀ i := by
    intro i hi
    induction i with
    | zero => exact h0
    | succ i ih =>
      have hi' : i < C'.k := by omega
      have hv : M.vert (M.α (C'.d i)) = M.vert (C'.d (i + 1)) := by
        rw [C'.vert_α i hi', Nat.mod_eq_of_lt hi]
      have hO : Out W (C'.d (i + 1)) := (hS _).2 ⟨i + 1, hi, rfl⟩
      obtain ⟨t1, t2⟩ := turnOut_spec hO hv.symm
      have e : bdD W x₀ (i + 1) = turnOut W (bdD W x₀ i) := Function.iterate_succ_apply' _ _ _
      rw [e, ← ih hi']
      exact (huniq _ _ t1 hO (t2.trans hv)).symm
  refine ⟨C', hCp', ?_, hd, hC'⟩
  rw [bdK]
  have : ({x | Out W x} : Finset D) = (range C'.k).image C'.d := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_range]
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := (hS x).1 hx
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact (hS _).2 ⟨i, hi, rfl⟩
  rw [this, card_image_of_injOn, card_range]
  intro i hi j hj h
  exact C'.inj i (by simpa using hi) j (by simpa using hj) (congrArg M.vert h)

/-- The hypotheses of the boundary cycle by turning: some proper simple cycle bounds `W`, and
`x₀` leaves `W`. -/
def BdOK (W : Finset M.Face) (x₀ : D) : Prop :=
  (∃ C : M.SCycle, C.Proper ∧ ∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) ↔ ¬ C.Mem d) ∧ Out W x₀

/-- **The boundary cycle of `W` from `x₀`**, with `bdK W` darts `bdD W x₀ i` (only the proofs
of its fields use the hypotheses). -/
noncomputable def bdCycle (W : Finset M.Face) (x₀ : D) (h : BdOK W x₀) : M.SCycle :=
  (exists_bdCycle h.1 h.2).choose.copy (bdK W) (bdD W x₀)
    (exists_bdCycle h.1 h.2).choose_spec.2.1 (exists_bdCycle h.1 h.2).choose_spec.2.2.1

@[simp] lemma bdCycle_k {W : Finset M.Face} {x₀ : D} (h : BdOK W x₀) :
    (bdCycle W x₀ h).k = bdK W := rfl

@[simp] lemma bdCycle_d {W : Finset M.Face} {x₀ : D} (h : BdOK W x₀) :
    (bdCycle W x₀ h).d = bdD W x₀ := rfl

theorem bdCycle_spec {W : Finset M.Face} {x₀ : D} (h : BdOK W x₀) :
    (bdCycle W x₀ h).Proper ∧
      ∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) ↔ ¬ (bdCycle W x₀ h).Mem d := by
  obtain ⟨hp, -, -, hb⟩ := (exists_bdCycle h.1 h.2).choose_spec
  refine ⟨SCycle.copy_proper _ hp, fun d => ?_⟩
  rw [bdCycle, SCycle.mem_copy]
  exact hb d

/-- **The boundary cycle by any choice of outgoing darts.** If `nx v` is a dart leaving `W` at
`v` for every vertex `v` at which a dart leaves `W` (as a pass over the darts stores them), then
the darts of the boundary cycle are those of the walk `x ↦ nx (vert (α x))` from `x₀`: at every
vertex of a boundary cycle exactly one dart leaves `W`. -/
theorem bdD_eq_iterate {W : Finset M.Face} {x₀ : D} (h : BdOK W x₀) (nx : P → D)
    (hnx : ∀ y, Out W y → Out W (nx (M.vert y)) ∧ M.vert (nx (M.vert y)) = M.vert y) (i : ℕ) :
    bdD W x₀ i = (fun x => nx (M.vert (M.α x)))^[i] x₀ := by
  classical
  obtain ⟨⟨C, hCp, hC⟩, hx₀⟩ := h
  obtain ⟨C', -, -, -, -, hS⟩ := exists_oriented C hCp hC hx₀.1 hx₀.2
  have huniq : ∀ y y', Out W y → Out W y' → M.vert y = M.vert y' → y = y' := by
    intro y y' hy hy' hv
    obtain ⟨i, hi, rfl⟩ := (hS y).1 hy
    obtain ⟨j, hj, rfl⟩ := (hS y').1 hy'
    rw [C'.inj i hi j hj hv]
  have hhead : ∀ x, Out W x → ∃ y, Out W y ∧ M.vert y = M.vert (M.α x) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := (hS x).1 hx
    exact ⟨_, (hS _).2 ⟨_, Nat.mod_lt _ C'.pos, rfl⟩, (C'.vert_α j hj).symm⟩
  have key : ∀ i, Out W (bdD W x₀ i) ∧ bdD W x₀ i = (fun x => nx (M.vert (M.α x)))^[i] x₀ := by
    intro i
    induction i with
    | zero => exact ⟨hx₀, rfl⟩
    | succ i ih =>
      obtain ⟨y, hy, hyv⟩ := hhead _ ih.1
      obtain ⟨t1, t2⟩ := turnOut_spec hy hyv
      have e : bdD W x₀ (i + 1) = turnOut W (bdD W x₀ i) := Function.iterate_succ_apply' _ _ _
      obtain ⟨n1, n2⟩ := hnx y hy
      rw [hyv] at n1 n2
      refine ⟨by rw [e]; exact t1, ?_⟩
      rw [e, Function.iterate_succ_apply', ← ih.2]
      exact huniq _ _ t1 n1 (t2.trans n2.symm)
  exact (key i).2

/-! ### The ancestor at a level -/

open Classical in
/-- **The ancestor at level `l`** of `u` in `T₁`: the first iterated parent in `T₁` whose level
in `T` is at most `l`. -/
noncomputable def topA (T T₁ : M.SpTree) (l : ℕ) (u : P) : P :=
  if h : ∃ j, T.height (T₁.parent^[j] u) ≤ l then T₁.parent^[Nat.find h] u else u

/-- An ancestor `a` of `u` of level `≤ l`, below which the root path of `u` runs above `l`, is
`topA`. -/
lemma topA_eq {T T₁ : M.SpTree} {l : ℕ} {u a : P} (ha : a ∈ T₁.anc u) (hal : T.height a ≤ l)
    (hrest : ∀ v ∈ T₁.anc u, v ∉ T₁.anc a → l < T.height v) : topA T T₁ l u = a := by
  classical
  obtain ⟨n, rfl⟩ := (T₁.mem_anc_iff).1 ha
  have h : ∃ j, T.height (T₁.parent^[j] u) ≤ l := ⟨n, hal⟩
  rw [topA, dite_eq_left_of_eq_true (eq_true h)]
  have hle : Nat.find h ≤ n := Nat.find_min' h hal
  have hspec := Nat.find_spec h
  by_cases hm : T₁.parent^[Nat.find h] u ∈ T₁.anc (T₁.parent^[n] u)
  · refine T₁.eq_of_mem_anc_of_mem_anc hm ?_
    rw [show n = (n - Nat.find h) + Nat.find h by omega, Function.iterate_add_apply]
    exact T₁.iterate_parent_mem_anc _ _
  · exact absurd hspec (not_le.2 (hrest _ (T₁.iterate_parent_mem_anc _ _) hm))

/-- **The ancestor at a level by guarded parent steps.** If the root of `T₁` has level `≤ l`,
then `N ≥ #P` steps of "the parent if the level is `> l`" from `u` reach `topA T T₁ l u`. -/
theorem topA_eq_iterate {T T₁ : M.SpTree} {l : ℕ} (hr : T.height T₁.root ≤ l) (u : P) {N : ℕ}
    (hN : Fintype.card P ≤ N) :
    topA T T₁ l u = (fun v => if l < T.height v then T₁.parent v else v)^[N] u := by
  classical
  set g := fun v => if l < T.height v then T₁.parent v else v with hg
  obtain ⟨n₀, hn₀⟩ := T₁.exists_iterate_eq_root u
  have h : ∃ j, T.height (T₁.parent^[j] u) ≤ l := ⟨n₀, by rw [hn₀]; exact hr⟩
  rw [topA, dite_eq_left_of_eq_true (eq_true h)]
  set m := Nat.find h with hm
  have hmin : ∀ j < m, l < T.height (T₁.parent^[j] u) := fun j hj =>
    not_le.1 (Nat.find_min h hj)
  have hspec : T.height (T₁.parent^[m] u) ≤ l := Nat.find_spec h
  have h1 : ∀ j ≤ m, g^[j] u = T₁.parent^[j] u := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega), hg]
      simp only [hmin j (by omega), ↓reduceIte]
  have h2 : ∀ j, g^[m + j] u = T₁.parent^[m] u := by
    intro j
    induction j with
    | zero => exact h1 m le_rfl
    | succ j ih =>
      rw [← add_assoc, Function.iterate_succ_apply', ih, hg]
      simp only [not_lt.2 hspec, ↓reduceIte]
  have hmN : m ≤ N := by
    have : m ≤ #(T₁.anc u) := T₁.lt_card_anc fun i hi e => by
      have := hmin i hi
      rw [e] at this
      omega
    exact this.trans ((card_le_univ _).trans hN)
  rw [show N = m + (N - m) by omega, h2]

/-! ### Separators -/

/-- **A separator** `(C, Z)` with at most `N` darts: `C` bounds `Z`, and both sides weigh at most
`2/3`. -/
abbrev SepOK (w : P → ℝ) (N : ℕ) (r : M.SCycle × Finset M.Face) : Prop :=
  r.1.k ≤ N ∧ IsCycleSep r.1 r.2 (sideIn r.1 r.2) (sideOut r.1 r.2) ∧
    ∑ v ∈ sideIn r.1 r.2, w v ≤ 2 / 3 ∧ ∑ v ∈ sideOut r.1 r.2, w v ≤ 2 / 3

section Fallback

variable {T : M.SpTree} (hM : M.IsPlane) (hT : IsBFS T) (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d)
include hM hT h3

/-- **The boundary cycle of a component separates** (`PlanarSeparator.Map.fallback`, with the
separator named): the cycle `C` itself with the component. -/
lemma fallback_self {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) {l₂ : ℕ} (hl : 1 ≤ l₂) {f : M.Face}
    {C : M.SCycle}
    (hC : ∀ d, (M.face d ∈ M.comp (T.low l₂) f ↔ M.face (M.α d) ∈ M.comp (T.low l₂) f) ↔
      ¬ C.Mem d)
    (hY1 : ∑ v ∈ ins (M.comp (T.low l₂) f), w v ≤ 2 / 3)
    (hY2 : ∑ v, w v - ∑ v ∈ ins (M.comp (T.low l₂) f), w v - ∑ v ∈ C.verts, w v ≤ 2 / 3) :
    C.k ≤ #(T.lvl l₂) ∧
      IsCycleSep C (M.comp (T.low l₂) f) (sideIn C (M.comp (T.low l₂) f))
        (sideOut C (M.comp (T.low l₂) f)) ∧
      ∑ v ∈ sideIn C (M.comp (T.low l₂) f), w v ≤ 2 / 3 ∧
      ∑ v ∈ sideOut C (M.comp (T.low l₂) f), w v ≤ 2 / 3 := by
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
  refine ⟨?_, isCycleSep_of_bd hC, ?_, ?_⟩
  · rw [← C.card_verts]
    exact card_le_card fun v hv => SpTree.mem_lvl.2 (hlev v hv)
  · exact (sum_le_sum_of_subset_of_nonneg hin fun v _ _ => hw v).trans hY1
  · have := sum_le_sum_of_subset_of_nonneg (subset_univ (sideOut C Y ∪ (ins Y ∪ C.verts)))
      fun v _ _ => hw v
    rw [sum_union hout, sum_union hinsC] at this
    linarith

end Fallback

/-! ### The rerouting options -/

open Classical in
/-- The fundamental cycle of `e` in `T₂` with its inside, or with the complement if the inside
disagrees with `Z₀` at the face `g₀`. -/
noncomputable def arcOptOf (T₂ : M.SpTree) (e : D) (Z₀ : Finset M.Face) (g₀ : M.Face) :
    M.SCycle × Finset M.Face :=
  (T₂.fcycle e, if (g₀ ∈ T₂.inside e ↔ g₀ ∈ Z₀) then T₂.inside e else (T₂.inside e)ᶜ)

open Classical in
/-- **A rerouting option**: for the arc of `L` steps of `C` from the index `s`, the fundamental
cycle of its last dart in the tree `T₁` redirected along it (`PlanarSeparator.Map.SpTree.arcTree`,
over the first `L - 1` steps), oriented to agree with `Z₀` at `g₀` (`junk` if the arc tree is
not defined). -/
noncomputable def arcOpt (T₁ : M.SpTree) (C : M.SCycle) (s L : ℕ) (Z₀ : Finset M.Face)
    (g₀ : M.Face) (junk : M.SCycle) : M.SCycle × Finset M.Face :=
  if h : s < C.k ∧ T₁.root ∉ C.verts ∧
      ∀ i < C.k, T₁.height (M.vert (C.d i)) = T₁.height (M.vert (C.d s)) then
    arcOptOf (T₁.arcTree C s (L - 1) h.1 h.2.1 h.2.2) (C.d (C.idxAt s (L - 1))) Z₀ g₀
  else (junk, ∅)

/-- **The rerouting option, explicitly** (`PlanarSeparator.Map.reroute_option`, with the cycle
and the set named): its cycle bounds its set of faces, whose boundary cochain is the arc plus the
tree path `Pc` between the ends of the arc, and its set agrees with `Z₀` at `g₀`. -/
lemma arcOpt_spec (hM : M.IsPlane) {T₁ : M.SpTree} {C : M.SCycle} {s' L' : ℕ} (hs' : s' < C.k)
    (hL1 : 1 ≤ L') (hLk : L' < C.k) (hr : T₁.root ∉ C.verts)
    (hC : ∀ i < C.k, T₁.height (M.vert (C.d i)) = T₁.height (M.vert (C.d s')))
    (hnt : ∀ i < C.k, ¬ T₁.IsTree (C.d i)) (hCp : C.Proper) (Pc : D → ZMod 2)
    (hP : T₁.pathC (M.vert (C.d s')) + T₁.pathC (M.vert (C.d (C.idxAt s' L'))) = Pc)
    (Z₀ : Finset M.Face) (g₀ : M.Face) (junk : M.SCycle) (o : M.SCycle × Finset M.Face)
    (ho : o = arcOpt T₁ C s' L' Z₀ g₀ junk) :
    (∀ d, (M.face d ∈ o.2 ↔ M.face (M.α d) ∈ o.2) ↔ ¬ o.1.Mem d) ∧
      (∀ d, (M.face d ∈ o.2 ↔ M.face (M.α d) ∈ o.2) ↔ C.arcS s' L' d + Pc d = 0) ∧
      (∀ v, v ∈ o.1.verts ↔ ∃ d, M.vert d = v ∧ C.arcS s' L' d + Pc d ≠ 0) ∧
      (g₀ ∈ o.2 ↔ g₀ ∈ Z₀) := by
  subst ho
  rw [arcOpt, dite_eq_left_of_eq_true (eq_true ⟨hs', hr, hC⟩)]
  set T₂ := T₁.arcTree C s' (L' - 1) hs' hr hC
  set e := C.d (C.idxAt s' (L' - 1))
  have he : ¬ T₂.IsTree e := T₁.not_isTree_arcTree C hCp hnt hL1 hLk
  have hfund : T₂.fund e = C.arcS s' L' + Pc := by
    rw [T₁.fund_arcTree C hL1 hLk, ← hP, add_assoc]
  have hbd := T₂.bd_inside hM he
  have hbd' : ∀ d, (M.face d ∈ T₂.inside e ↔ M.face (M.α d) ∈ T₂.inside e) ↔
      C.arcS s' L' d + Pc d = 0 := fun d => by
    rw [SpTree.inside_iff hM, hfund, Pi.add_apply]
  have hverts : ∀ v, v ∈ (T₂.fcycle e).verts ↔
      ∃ d, M.vert d = v ∧ C.arcS s' L' d + Pc d ≠ 0 := fun v => by
    rw [SpTree.fcycle_verts he, SpTree.mem_cycV, hfund]
    rfl
  by_cases hg : g₀ ∈ T₂.inside e ↔ g₀ ∈ Z₀
  · rw [arcOptOf, ite_eq_left_of_eq_true _ _ (eq_true hg)]
    exact ⟨hbd, hbd', hverts, hg⟩
  · rw [arcOptOf, ite_eq_right_of_eq_false _ _ (eq_false hg)]
    refine ⟨bd_compl hbd, fun d => ?_, hverts, ?_⟩
    · show (M.face d ∈ (T₂.inside e)ᶜ ↔ M.face (M.α d) ∈ (T₂.inside e)ᶜ) ↔ _
      rw [mem_compl, mem_compl, ← hbd' d]
      tauto
    · show g₀ ∈ (T₂.inside e)ᶜ ↔ _
      rw [mem_compl]
      tauto

/-! ### The deep case, explicitly -/

/-- **The wanted side** for the component `Y` in the deep case: the representatives of the
vertices of the strict inside of `Y` lie strictly inside the cycle of `δ`, or on it while the
strict inside is the lighter side. -/
def deepWant (T₁ : M.SpTree) (cn : P → P) (w : P → ℝ) (Y : Finset M.Face) (δ : D) : Prop :=
  ∀ v ∈ ins Y, cn v ∈ T₁.inC δ ∨
    (cn v ∈ T₁.cycV δ ∧ ∑ u ∈ T₁.inC δ, wcf cn w u ≤ ∑ u ∈ T₁.outC δ, wcf cn w u)

open Classical in
/-- **The choice of the arc**: the option along the arc from `b` to `a` if it puts the face of
`δ` on the wanted side, the option along the arc from `a` to `b` otherwise. -/
noncomputable def deepPick (T₁ : M.SpTree) (C : M.SCycle) (δ : D) (a b : P) (want : Prop)
    (g₀ : M.Face) : M.SCycle × Finset M.Face :=
  if (M.face δ ∈
      (arcOpt T₁ C (C.idx b) (C.off (C.idx b) (C.idx a)) (T₁.inside δ) g₀ (T₁.fcycle δ)).2 ↔
      want) then
    arcOpt T₁ C (C.idx b) (C.off (C.idx b) (C.idx a)) (T₁.inside δ) g₀ (T₁.fcycle δ)
  else arcOpt T₁ C (C.idx a) (C.k - C.off (C.idx b) (C.idx a)) (T₁.inside δ) g₀ (T₁.fcycle δ)

open Classical in
/-- **The deep case**: for a dart `δ` both of whose faces avoid the levels `< l₂`, with `C` a
boundary cycle of its component `Y` at level `l₂`: `C` with `Y` if the ancestors at level `l₂`
of the ends of `δ` coincide or `Y` weighs at least `1/3`, the chosen rerouting otherwise. -/
noncomputable def deepSep (T T₁ : M.SpTree) (l₂ : ℕ) (cn : P → P) (w : P → ℝ) (δ : D)
    (C : M.SCycle) (g₀ : M.Face) : M.SCycle × Finset M.Face :=
  if topA T T₁ l₂ (M.vert δ) = topA T T₁ l₂ (M.vert (M.α δ)) ∨
      1 / 3 ≤ ∑ v ∈ ins (M.comp (T.low l₂) (M.face δ)), w v then
    (C, M.comp (T.low l₂) (M.face δ))
  else deepPick T₁ C δ (topA T T₁ l₂ (M.vert δ)) (topA T T₁ l₂ (M.vert (M.α δ)))
    (deepWant T₁ cn w (M.comp (T.low l₂) (M.face δ)) δ) g₀

section DeepCase

variable (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ) {T : M.SpTree} (hT : IsBFS T)
  {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) (h1 : ∑ v, w v ≤ 1) {l₀ l₂ : ℕ} {H : Finset M.Face}
  {K₀ : Finset P} {c₀ : P} {T₁ : M.SpTree} (hI : Inner T w l₀ H K₀ c₀ T₁) (hl : l₀ < l₂)

include hM htri hT hw h1 hI hl in
/-- **The deep case, explicitly** (`PlanarSeparator.Map.deep_case_of_scycle`, with the
separator named): for a dart both of whose faces avoid the levels `< l₂`, a proper simple cycle
`C` bounding the component `Y` of the dart at level `l₂` and a face `g₀` off `Y`,
`deepSep T T₁ l₂ cn w δ C g₀` is a separator with at most `2 (l₂ - l₀) + #K₀ + #L` darts. -/
theorem deep_explicit {cn : P → P} (hcn : IsConc T l₂ cn) {δ : D} (hδ : ¬ T₁.IsTree δ)
    (hδH : M.face δ ∈ H ∧ M.face (M.α δ) ∈ H)
    (hz1 : M.face δ ∉ M.zone (T.low l₂)) (hz2 : M.face (M.α δ) ∉ M.zone (T.low l₂))
    (hA : ∑ v ∈ T₁.inC δ, wcf cn w v ≤ 2 / 3) (hB : ∑ v ∈ T₁.outC δ, wcf cn w v ≤ 2 / 3)
    (hlight : ∀ f, f ∉ M.zone (T.low l₂) → ∑ v ∈ ins (M.comp (T.low l₂) f), w v ≤ 2 / 3)
    (C : M.SCycle) (hCp : C.Proper)
    (hC : ∀ d, (M.face d ∈ M.comp (T.low l₂) (M.face δ) ↔
      M.face (M.α d) ∈ M.comp (T.low l₂) (M.face δ)) ↔ ¬ C.Mem d)
    {g₀ : M.Face} (hg₀ : g₀ ∉ M.comp (T.low l₂) (M.face δ)) :
    SepOK w (2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂)) (deepSep T T₁ l₂ cn w δ C g₀) := by
  classical
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (htri d).φ_three
  have hl2 : 1 ≤ l₂ := by omega
  rw [deepSep]
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
  -- the complement of `Y` is connected
  obtain ⟨d₀, hd₀⟩ := hM.exists_dart T.root
  have hYc : FConn Yᶜ := compl_comp_fConn hM (zone_fConn hM T hr2
    (fun v hv => parent_mem_low hT hv)) (hd₀ ▸ hr2) (M.face δ)
  -- the fallback
  have hfb : ∑ v, w v - ∑ v ∈ ins Y, w v - ∑ v ∈ C.verts, w v ≤ 2 / 3 →
      SepOK w (2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂)) (C, Y) := fun h => by
    obtain ⟨hk, rest⟩ := fallback_self hM hT h3 hw hl2 hC (hlight _ hz1) h
    refine ⟨?_, rest⟩
    show C.k ≤ _
    omega
  -- the ends of `δ` and their ancestors at level `l₂`
  obtain ⟨a, hax, haC, hxa⟩ := exists_top hM hT hI hl hC _ (touch_comp hC hδY)
  obtain ⟨b, hbz, hbC, hzb⟩ := exists_top hM hT hI hl hC _ (touch_comp hC hαY)
  have hta : topA T T₁ l₂ (M.vert δ) = a :=
    topA_eq hax (hlevC a haC).le fun v hv hva => hinsl v (hxa v hv hva)
  have htb : topA T T₁ l₂ (M.vert (M.α δ)) = b :=
    topA_eq hbz (hlevC b hbC).le fun v hv hvb => hinsl v (hzb v hv hvb)
  rw [hta, htb]
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
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inl hab))]
    subst hab
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
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inr hω))]
    apply hfb
    have := sum_nonneg fun v (_ : v ∈ C.verts) => hw v
    linarith
  rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => h.elim hab hω), deepPick]
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
  set o₁ := arcOpt T₁ C s L (T₁.inside δ) g₀ (T₁.fcycle δ) with ho₁
  set o₂ := arcOpt T₁ C t₀ (C.k - L) (T₁.inside δ) g₀ (T₁.fcycle δ) with ho₂
  obtain ⟨bd₁, bdΓ₁, verts₁, g₁⟩ := arcOpt_spec hM hsk hL1 hLk hr
    (fun i hi => hflat i hi s hsk) hnt hCp Pc (by rw [hsb, hat, hta, hPdef, add_comm])
    (T₁.inside δ) g₀ (T₁.fcycle δ) o₁ ho₁
  obtain ⟨bd₂, bdΓ₂, verts₂, g₂⟩ := arcOpt_spec hM htk (by omega : 1 ≤ C.k - L)
    (by omega) hr (fun i hi => hflat i hi t₀ htk) hnt hCp Pc (by rw [hta, hbt, hsb])
    (T₁.inside δ) g₀ (T₁.fcycle δ) o₂ ho₂
  set Z₁ := o₁.2
  set Z₂ := o₂.2
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
  have hwantdef : deepWant T₁ cn w Y δ ↔
      ∀ v ∈ ins Y, cn v ∈ T₁.inC δ ∨ (cn v ∈ T₁.cycV δ ∧ lighter) := by
    rw [hlighter]
    rfl
  suffices key : ∀ (Cf : M.SCycle) (Zf : Finset M.Face) (s' L' : ℕ), s' < C.k → 1 ≤ L' →
      L' < C.k →
      (∀ d, (M.face d ∈ Zf ↔ M.face (M.α d) ∈ Zf) ↔ ¬ Cf.Mem d) →
      (∀ d, (M.face d ∈ Zf ↔ M.face (M.α d) ∈ Zf) ↔ C.arcS s' L' d + Pc d = 0) →
      (∀ v, v ∈ Cf.verts ↔ ∃ d, M.vert d = v ∧ C.arcS s' L' d + Pc d ≠ 0) →
      (g₀ ∈ Zf ↔ g₀ ∈ T₁.inside δ) →
      ((M.vert (C.d s') = a ∧ M.vert (C.d (C.idxAt s' L')) = b) ∨
        (M.vert (C.d s') = b ∧ M.vert (C.d (C.idxAt s' L')) = a)) →
      (M.face δ ∈ Zf ↔ deepWant T₁ cn w Y δ) →
      Cf.k ≤ 2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂) ∧
        IsCycleSep Cf Zf (sideIn Cf Zf) (sideOut Cf Zf) ∧
        ∑ v ∈ sideIn Cf Zf, w v ≤ 2 / 3 ∧ ∑ v ∈ sideOut Cf Zf, w v ≤ 2 / 3 by
    by_cases h : M.face δ ∈ Z₁ ↔ deepWant T₁ cn w Y δ
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
      exact key o₁.1 o₁.2 s L hsk hL1 hLk bd₁ bdΓ₁ verts₁ g₁
        (Or.inr ⟨hsb, by rw [hat, hta]⟩) h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
      exact key o₂.1 o₂.2 t₀ (C.k - L) htk (by omega) (by omega) bd₂ bdΓ₂ verts₂ g₂
        (Or.inl ⟨hta, by rw [hbt, hsb]⟩) (iff_of_not_iff_of_iff_not h (hK3 _ hδY))
  intro Cf Zf s' L' hs' hL1' hLk' bdf bdΓf vertsf hgf hendsab hwant
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
      have hnw : ¬ deepWant T₁ cn w Y δ := fun h => hδZ (hwant.2 h)
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
  refine ⟨?_, isCycleSep_of_bd bdf, ?_, ?_⟩
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

end DeepCase

/-! ### The band theorem, explicitly -/

open Classical in
/-- **The separator of the band theorem, explicitly.** From the balanced dart `δ` of `T₁`: if
both faces of `δ` avoid the levels `< l₂` (the deep case), `deepSep` with the boundary cycle of
the component `Y` of `δ` at level `l₂` obtained by turning from `x₀` (`bdCycle`); otherwise (the
band case) the fundamental cycle of `δ` in `T₁` with its inside. -/
noncomputable def bandSep (T T₁ : M.SpTree) (l₂ : ℕ) (cn : P → P) (w : P → ℝ) (δ x₀ : D)
    (g₀ : M.Face) : M.SCycle × Finset M.Face :=
  if M.face δ ∉ M.zone (T.low l₂) ∧ M.face (M.α δ) ∉ M.zone (T.low l₂) then
    deepSep T T₁ l₂ cn w δ
      (if h : BdOK (M.comp (T.low l₂) (M.face δ)) x₀ then bdCycle _ x₀ h else T₁.fcycle δ) g₀
  else (T₁.fcycle δ, T₁.inside δ)

lemma bandSep_of_band {T T₁ : M.SpTree} {l₂ : ℕ} {cn : P → P} {w : P → ℝ} {δ x₀ : D}
    {g₀ : M.Face}
    (h : M.face δ ∈ M.zone (T.low l₂) ∨ M.face (M.α δ) ∈ M.zone (T.low l₂)) :
    bandSep T T₁ l₂ cn w δ x₀ g₀ = (T₁.fcycle δ, T₁.inside δ) := by
  rw [bandSep, ite_eq_right_of_eq_false _ _ (eq_false fun h' => h.elim h'.1 h'.2)]

lemma bandSep_of_deep {T T₁ : M.SpTree} {l₂ : ℕ} {cn : P → P} {w : P → ℝ} {δ x₀ : D}
    {g₀ : M.Face} (hz1 : M.face δ ∉ M.zone (T.low l₂)) (hz2 : M.face (M.α δ) ∉ M.zone (T.low l₂))
    (h : BdOK (M.comp (T.low l₂) (M.face δ)) x₀) :
    bandSep T T₁ l₂ cn w δ x₀ g₀ = deepSep T T₁ l₂ cn w δ (bdCycle _ x₀ h) g₀ := by
  rw [bandSep, ite_eq_left_of_eq_true _ _ (eq_true ⟨hz1, hz2⟩),
    dite_eq_left_of_eq_true (eq_true h)]

section Band

variable (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ) {T : M.SpTree} (hT : IsBFS T)
  {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) (h1 : ∑ v, w v ≤ 1) {l₀ l₂ : ℕ} {H : Finset M.Face}
  {K₀ : Finset P} {c₀ : P} {T₁ : M.SpTree} (hI : Inner T w l₀ H K₀ c₀ T₁) (hl : l₀ < l₂)

include hM htri hT hw hI hl in
/-- **A balanced dart has both faces in `H`**: otherwise its cycle leaves the strict inside of
`H`, of weight `> 2/3`, on one side. -/
lemma faces_mem_H {cn : P → P} (hcn : IsConc T l₂ cn) {δ : D} (hδ : ¬ T₁.IsTree δ)
    (hA : ∑ v ∈ T₁.inC δ, wcf cn w v ≤ 2 / 3) (hB : ∑ v ∈ T₁.outC δ, wcf cn w v ≤ 2 / 3) :
    M.face δ ∈ H ∧ M.face (M.α δ) ∈ H := by
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (htri d).φ_three
  by_contra hbad'
  have hbad : M.face δ ∉ H ∨ M.face (M.α δ) ∉ H := by tauto
  obtain ⟨hv, hf⟩ := hI.bad δ hδ hbad
  obtain ⟨v₀, hv₀⟩ : (ins H).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have := hI.heavy
    rw [h, sum_empty] at this
    norm_num at this
  obtain ⟨e₀, he₀⟩ := hM.exists_dart v₀
  have hf₀ := mem_ins.1 hv₀ e₀ he₀
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

include hM htri hT hw h1 hI hl in
/-- **The band theorem, explicitly.** For any concentration map `cn` at level `l₂`, any dart `δ`
off `T₁` whose fundamental cycle has strict inside and strict outside of moved weight at most
`2/3` each (step 8), any face `g₀` touching the levels `< l₂`, and any dart `x₀` leaving the
component of `δ` at level `l₂` when both faces of `δ` avoid the levels `< l₂`, the explicit
separator `bandSep T T₁ l₂ cn w δ x₀ g₀` has at most `2 (l₂ - l₀) + #K₀ + #L` darts, `L` being
the set of vertices of level `l₂`, bounds its set of faces, and both of its sides weigh at most
`2/3`: the conclusion of `PlanarSeparator.Map.band_separator_of_dart`, for a named separator. -/
theorem band_separator_explicit {cn : P → P} (hcn : IsConc T l₂ cn) {δ : D}
    (hδ : ¬ T₁.IsTree δ) (hA : ∑ v ∈ T₁.inC δ, wcf cn w v ≤ 2 / 3)
    (hB : ∑ v ∈ T₁.outC δ, wcf cn w v ≤ 2 / 3)
    (hlight : ∀ f, f ∉ M.zone (T.low l₂) → ∑ v ∈ ins (M.comp (T.low l₂) f), w v ≤ 2 / 3)
    {x₀ : D} (hx₀ : M.face δ ∉ M.zone (T.low l₂) → M.face (M.α δ) ∉ M.zone (T.low l₂) →
      Out (M.comp (T.low l₂) (M.face δ)) x₀)
    {g₀ : M.Face} (hg₀ : g₀ ∈ M.zone (T.low l₂)) :
    SepOK w (2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂)) (bandSep T T₁ l₂ cn w δ x₀ g₀) := by
  have hl2 : 1 ≤ l₂ := by omega
  have hH := faces_mem_H hM htri hT hw hI hl hcn hδ hA hB
  by_cases hdeep : M.face δ ∉ M.zone (T.low l₂) ∧ M.face (M.α δ) ∉ M.zone (T.low l₂)
  · obtain ⟨C, hCp, hC, -⟩ := hM.exists_scycle_comp T (root_mem_low hT hl2)
      (fun v hv => parent_mem_low hT hv) hdeep.1
    have hok : BdOK (M.comp (T.low l₂) (M.face δ)) x₀ := ⟨⟨C, hCp, hC⟩, hx₀ hdeep.1 hdeep.2⟩
    rw [bandSep_of_deep hdeep.1 hdeep.2 hok]
    obtain ⟨hp, hb⟩ := bdCycle_spec hok
    exact deep_explicit hM htri hT hw h1 hI hl hcn hδ hH hdeep.1 hdeep.2 hA hB hlight _ hp hb
      fun h => (mem_comp.1 h).1 hg₀
  · have hz : M.face δ ∈ M.zone (T.low l₂) ∨ M.face (M.α δ) ∈ M.zone (T.low l₂) := by
      by_contra h
      push Not at h
      exact hdeep h
    rw [bandSep_of_band hz]
    obtain ⟨hk, rest⟩ := band_case_fcycle hM htri hT hw hI hl hcn hδ hH hz hA hB
    refine ⟨?_, rest⟩
    show (T₁.fcycle δ).k ≤ _
    omega

include hM htri hT hw h1 hI hl in
/-- The explicit band theorem in the form of `PlanarSeparator.Map.band_separator_of_dart`, with
the face `g₀` of a dart at the root. -/
theorem band_separator_explicit' {cn : P → P} (hcn : IsConc T l₂ cn) {δ : D}
    (hδ : ¬ T₁.IsTree δ) (hA : ∑ v ∈ T₁.inC δ, wcf cn w v ≤ 2 / 3)
    (hB : ∑ v ∈ T₁.outC δ, wcf cn w v ≤ 2 / 3)
    (hlight : ∀ f, f ∉ M.zone (T.low l₂) → ∑ v ∈ ins (M.comp (T.low l₂) f), w v ≤ 2 / 3)
    {x₀ : D} (hx₀ : M.face δ ∉ M.zone (T.low l₂) → M.face (M.α δ) ∉ M.zone (T.low l₂) →
      Out (M.comp (T.low l₂) (M.face δ)) x₀)
    {d₀ : D} (hd₀ : M.vert d₀ = T.root) :
    ∃ (C : M.SCycle) (Z : Finset M.Face), (C, Z) = bandSep T T₁ l₂ cn w δ x₀ (M.face d₀) ∧
      C.k ≤ 2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂) ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      ∑ v ∈ sideIn C Z, w v ≤ 2 / 3 ∧ ∑ v ∈ sideOut C Z, w v ≤ 2 / 3 :=
  ⟨_, _, rfl, band_separator_explicit hM htri hT hw h1 hI hl hcn hδ hA hB hlight hx₀
    (face_mem_zone (by rw [hd₀]; exact root_mem_low hT (by omega)))⟩

end Band

end Map

end PlanarSeparator
