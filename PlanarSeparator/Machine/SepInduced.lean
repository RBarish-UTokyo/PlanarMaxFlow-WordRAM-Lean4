module

public import PlanarSeparator.InducedRot
public import PlanarSeparator.SepTreeExplicit
public import PlanarSeparator.Machine.Encode

/-!
# A separator routine computed by the separator program on induced rotation systems

The separator tree of `PlanarSeparator/SepTreeExplicit.lean` is built from a separator routine
(`PlanarSeparator.SepRoutine G c`): for every vertex set `U` and natural weights `w`, a
separation `(S, A, B)` of `U` with `#S ≤ c √#U` and parts of weight at most `2/3`. Here such a
routine is obtained from the machine separator program of Lipton and Tarjan
(`SepProg.sepProg`, `PlanarSeparator.separator_machine`), run on the input `sepInput` of the
**induced rotation system** of a connected piece (`PlanarSeparator.InducedRot.indRot`, first
return of the rotation; plane by `PlanarSeparator.InducedRot.indRot_isPlane`).

* `runsWithin_out_unique`: the output of a run of the (deterministic) machine is unique; so
  `ltOut P`, the output of the compiled separator program `ltProg` on the input `P`, is the
  output of every run of it.
* `ltProg_spec`: the separator program on `sepInput R w di` (the statement of
  `SeparatorMachine`, for the explicit program `ltProg`).
* `dartNum`: a numbering of the darts of a graph on `Fin k` with the darts of lower tails first
  (by the key `fst * k + snd`).
* **`PlanarSeparator.CompSep`**, **`PlanarSeparator.SepRoutine.ofComp`**: a separator routine
  from a separator of the connected pieces, explicitly (as `planar_separator_induce`): if a
  connected component `C` of `U` (in the order of a list `ord` of the vertices) weighs more than
  `2/3`, separate it and add the rest of `U` to the lighter part; otherwise the separator is
  empty and the first part is the first component of weight at least `1/3`, or the union of the
  components of the shortest prefix of `ord` of weight at least `1/3`.
* **`PlanarSeparator.ltComp`**: the separator of a connected piece `C` by the separator
  program: list `C` in the order of `ord`, take the induced rotation system on `Fin #C`, the dart
  numbering `dartNum`, run `ltProg` on `sepInput` and read back the words `0`, `1`, `2`
  (a single vertex is its own separator). Constant `9` (`6 √k + 3 ≤ 9 √k`).
* **`PlanarSeparator.ltRoutine`** `: SepRoutine G 9` for a plane rotation system, and
  **`PlanarSeparator.buildTree_ltRoutine_square_spec`**: the explicit separator tree of the
  square built with `(ltRoutine …).square` is good for `T ≥ sepTreeConst (9 (Δ + 1)²)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

open Finset WordRAM WordRAM.Machine Relation

/-! ### The output of a run is unique -/

theorem runsWithin_out_unique {prog : Program} {P : Input} {W W' s s' : ℕ} {out out' : List ℕ}
    (h : RunsWithin prog P W s out) (h' : RunsWithin prog P W' s' out') : out = out' := by
  obtain ⟨k, -, hall, c, hc, hh, rfl⟩ := h
  obtain ⟨k', -, hall', c', hc', hh', rfl⟩ := h'
  have none_after : ∀ {k : ℕ} {c : Config}, run prog P k initConfig = some c → AtHalt prog c →
      run prog P (k + 1) initConfig = none := fun {k c} hc hh => by
    rw [run_succ_right, hc, Option.bind_some]; exact step_halt hh
  rcases lt_trichotomy k k' with hlt | rfl | hlt
  · obtain ⟨d, hd, -⟩ := hall' (k + 1) hlt
    rw [none_after hc hh] at hd; cases hd
  · rw [hc] at hc'; cases hc'; rfl
  · obtain ⟨d, hd, -⟩ := hall (k' + 1) hlt
    rw [none_after hc' hh'] at hd; cases hd

/-- The compiled separator program of Lipton and Tarjan. -/
def ltProg : Program := Stmt.compile SepProg.sepProg 0 ++ [Instr.halt]

open Classical in
/-- The output of the separator program on the input `P` (empty if it does not halt). -/
noncomputable def ltOut (P : Input) : List ℕ :=
  if h : ∃ out W s, RunsWithin ltProg P W s out then h.choose else []

theorem ltOut_eq {P : Input} {W s : ℕ} {out : List ℕ} (h : RunsWithin ltProg P W s out) :
    ltOut P = out := by
  have hex : ∃ out W s, RunsWithin ltProg P W s out := ⟨out, W, s, h⟩
  unfold ltOut
  split
  · rename_i h'
    obtain ⟨W', s', h''⟩ := h'.choose_spec
    exact runsWithin_out_unique h'' h
  · exact absurd hex ‹_›

/-- **The separator program on `sepInput`** (the statement of `SeparatorMachine` for the
explicit program `ltProg`). -/
theorem ltProg_spec {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G) (hR : R.IsPlane) (w : Fin n → ℕ) (di : G.Dart ≃ Fin m)
    (hdi : ∀ d d' : G.Dart, d.fst < d'.fst → di d < di d') (W : ℕ)
    (hW : 16 * m + 12 * n + 3 * ∑ v, w v + 22 ≤ W) :
    ∃ out : List ℕ, RunsWithin ltProg (sepInput R w di) W (320 * m + 191 * n + 403) out ∧
      IsSeparation G univ {v : Fin n | out.getD v 0 = 0} {v : Fin n | out.getD v 0 = 1}
        {v : Fin n | out.getD v 0 = 2} ∧
      (#{v : Fin n | out.getD v 0 = 0} : ℝ) ≤ 6 * √(n : ℝ) + 3 ∧
      3 * ∑ v ∈ univ.filter (fun v : Fin n => out.getD v 0 = 1), w v ≤ 2 * ∑ v, w v ∧
      3 * ∑ v ∈ univ.filter (fun v : Fin n => out.getD v 0 = 2), w v ≤ 2 * ∑ v, w v := by
  have hE := SepProg.enc_sepInput R w di hdi
  have hIn := SepProg.inHolds_sepInput R w di
  have hsum : ∑ v ∈ range n, SepProg.wI w v = ∑ v, w v := by
    rw [← Fin.sum_univ_eq_sum_range]; simp [SepProg.wI]
  have hW' : SepProg.memTop n m + 3 * ∑ v ∈ range n, SepProg.wI w v + 2 * n + 3 * m + 10 ≤ W := by
    rw [hsum]; unfold SepProg.memTop; omega
  obtain ⟨out, h1, h2⟩ := SepProg.sepProg_sepOut hR w hE hIn hW' (SepProg.sepInput_le R w di hW)
  exact ⟨out, h1, h2⟩

/-! ### A numbering of the darts, lower tails first -/

section DartNum

variable {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]

/-- The key of a dart: `fst * k + snd`. -/
def dkey (d : H.Dart) : ℕ := d.fst * k + d.snd

lemma dkey_injective : Function.Injective (dkey H) := by
  intro d d' h
  simp only [dkey] at h
  have h1 := d.snd.2
  have h2 := d'.snd.2
  have e1 : (d.fst : ℕ) = d'.fst := by
    rcases lt_trichotomy (d.fst : ℕ) d'.fst with hl | he | hl
    · exfalso
      have : (d.fst : ℕ) * k + d.snd < d'.fst * k + d'.snd := by nlinarith
      omega
    · exact he
    · exfalso
      have : (d'.fst : ℕ) * k + d'.snd < d.fst * k + d.snd := by nlinarith
      omega
  have e2 : (d.snd : ℕ) = d'.snd := by rw [e1] at h; omega
  exact (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext (Fin.ext e1) (Fin.ext e2))

/-- The keys of the darts. -/
def dkeys : Finset ℕ := univ.image (dkey H)

/-- **The numbering of the darts** by their keys. -/
noncomputable def dartNum : H.Dart ≃ Fin (dkeys H).card :=
  (Equiv.ofBijective (fun d => (⟨dkey H d, mem_image_of_mem _ (mem_univ d)⟩ : {x // x ∈ dkeys H}))
    ⟨fun d d' h => dkey_injective H (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
      obtain ⟨d, -, rfl⟩ := mem_image.1 hx; exact ⟨d, rfl⟩⟩).trans
    ((dkeys H).orderIsoOfFin rfl).symm.toEquiv

lemma dartNum_lt {d d' : H.Dart} (h : d.fst < d'.fst) : dartNum H d < dartNum H d' := by
  have hk : dkey H d < dkey H d' := by
    simp only [dkey]
    have := d.snd.2
    have h' : (d.fst : ℕ) + 1 ≤ d'.fst := h
    nlinarith
  show ((dkeys H).orderIsoOfFin rfl).symm _ < ((dkeys H).orderIsoOfFin rfl).symm _
  exact ((dkeys H).orderIsoOfFin rfl).symm.strictMono (Subtype.mk_lt_mk.2 hk)

end DartNum

/-! ### A separator routine from a separator of the connected pieces -/

section Comp

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- `C` is connected inside itself. -/
def InConn (C : Finset V) : Prop := ∀ x ∈ C, ∀ y ∈ C, ReflTransGen (AdjIn G C) x y

variable (G) in
/-- A **separator of the connected pieces** with constant `c`: for every nonempty vertex set `C`
connected inside itself and natural weights `w`, a separation of `C` with `#S ≤ c √#C` and parts
of weight at most `2/3` of the weight of `C`. -/
structure CompSep (c : ℝ) where
  /-- The separator, the first part and the second part. -/
  sep : Finset V → (V → ℕ) → Finset V × Finset V × Finset V
  spec : ∀ C w, InConn G C → C.Nonempty →
    IsSeparation G C (sep C w).1 (sep C w).2.1 (sep C w).2.2 ∧
    ((sep C w).1.card : ℝ) ≤ c * √(#C : ℝ) ∧
    3 * ∑ v ∈ (sep C w).2.1, w v ≤ 2 * ∑ v ∈ C, w v ∧
    3 * ∑ v ∈ (sep C w).2.2, w v ≤ 2 * ∑ v ∈ C, w v

omit [Fintype V] [DecidableRel G.Adj] in
theorem inConn_comp {U : Finset V} {v : V} : InConn G (comp G U v) := by
  have key : ∀ x, ReflTransGen (AdjIn G U) v x → ReflTransGen (AdjIn G (comp G U v)) v x := by
    intro x h
    induction h with
    | refl => exact .refl
    | @tail a b hva hab ih =>
      have ha : a ∈ comp G U v := mem_comp.2 ⟨hab.2.1, hva⟩
      have hb : b ∈ comp G U v := mem_comp.2 ⟨hab.2.2, hva.tail hab⟩
      exact ih.tail ⟨hab.1, ha, hb⟩
  have hsymm : ∀ a b, ReflTransGen (AdjIn G (comp G U v)) a b →
      ReflTransGen (AdjIn G (comp G U v)) b a := fun a b h => by
    induction h with
    | refl => exact .refl
    | tail _ hbc ih => exact (ReflTransGen.single (adjIn_symm hbc)).trans ih
  intro x hx y hy
  exact (hsymm _ _ (key x (mem_comp.1 hx).2)).trans (key y (mem_comp.1 hy).2)

omit [Fintype V] [DecidableRel G.Adj] in
/-- A separation of a vertex set `C` closed under the edges inside `U ⊇ C` gives separations of
`U`, with the rest of `U` added to either part. -/
theorem sep_add_rest {U C S A B : Finset V} (hCU : C ⊆ U)
    (hcl : ∀ a ∈ C, ∀ b ∈ U, G.Adj a b → b ∈ C) (h : IsSeparation G C S A B) :
    IsSeparation G U S (A ∪ (U \ C)) B ∧ IsSeparation G U S A (B ∪ (U \ C)) := by
  have hC : ∀ x, x ∈ C ↔ x ∈ S ∨ x ∈ A ∨ x ∈ B := by
    intro x; rw [← h.union_eq]; simp
  have hS : S ⊆ C := fun x hx => (hC x).2 (Or.inl hx)
  have hA : A ⊆ C := fun x hx => (hC x).2 (Or.inr (Or.inl hx))
  have hB : B ⊆ C := fun x hx => (hC x).2 (Or.inr (Or.inr hx))
  have hU : ∀ x, x ∈ U ↔ x ∈ S ∨ x ∈ A ∨ x ∈ B ∨ (x ∈ U ∧ x ∉ C) := by
    intro x
    have := hC x
    have := @hCU x
    tauto
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · ext x; have := hU x; simp only [mem_union, mem_sdiff]; tauto
  · exact disjoint_union_right.2 ⟨h.disjoint_sep_left, disjoint_of_subset_left hS disjoint_sdiff⟩
  · exact h.disjoint_sep_right
  · exact disjoint_union_left.2 ⟨h.disjoint,
      disjoint_of_subset_right hB (disjoint_sdiff.symm.mono_left le_rfl)⟩
  · intro a ha b hb hab
    rcases mem_union.1 ha with ha | ha
    · exact h.not_adj a ha b hb hab
    · exact (mem_sdiff.1 ha).2 (hcl b (hB hb) a (mem_sdiff.1 ha).1 hab.symm)
  · ext x; have := hU x; simp only [mem_union, mem_sdiff]; tauto
  · exact h.disjoint_sep_left
  · exact disjoint_union_right.2 ⟨h.disjoint_sep_right, disjoint_of_subset_left hS disjoint_sdiff⟩
  · exact disjoint_union_right.2 ⟨h.disjoint, disjoint_of_subset_left hA disjoint_sdiff⟩
  · intro a ha b hb hab
    rcases mem_union.1 hb with hb | hb
    · exact h.not_adj a ha b hb hab
    · exact (mem_sdiff.1 hb).2 (hcl a (hA ha) b (mem_sdiff.1 hb).1 hab)

omit [Fintype V] [DecidableRel G.Adj] in
/-- A part closed under the edges inside `U` gives a separation with empty separator. -/
theorem sep_of_closed {U A : Finset V} (hAU : A ⊆ U)
    (hcl : ∀ a ∈ A, ∀ b ∈ U, G.Adj a b → b ∈ A) : IsSeparation G U ∅ A (U \ A) where
  union_eq := by rw [empty_union, union_sdiff_of_subset hAU]
  disjoint_sep_left := disjoint_empty_left _
  disjoint_sep_right := disjoint_empty_left _
  disjoint := disjoint_sdiff
  not_adj a ha b hb hab := (mem_sdiff.1 hb).2 (hcl a ha b (mem_sdiff.1 hb).1 hab)

variable (G) in
/-- The heavy component of `U`: the component of the first vertex of `ord` in `U` whose
component weighs more than `2/3` of `U`, if any. -/
noncomputable def heavyC (ord : List V) (U : Finset V) (w : V → ℕ) : Option V :=
  (ord.filter fun v => v ∈ U ∧ 2 * ∑ u ∈ U, w u < 3 * ∑ u ∈ comp G U v, w u).head?

variable (G) in
/-- The union of the components of `U` meeting the first `k` vertices of `ord`. -/
noncomputable def pre (ord : List V) (U : Finset V) (k : ℕ) : Finset V :=
  ((ord.take k).toFinset.filter (· ∈ U)).biUnion (comp G U)

variable (G) in
/-- The shortest prefix of `ord` whose components weigh at least `1/3` of `U`. -/
noncomputable def kstar (ord : List V) (U : Finset V) (w : V → ℕ) : ℕ := by
  classical exact Nat.find (p := fun k => ∑ u ∈ U, w u ≤ 3 * ∑ u ∈ pre G ord U k, w u ∨
    ord.length < k) ⟨ord.length + 1, Or.inr (Nat.lt_succ_self _)⟩

variable (G) in
/-- The first part when no component is heavy: the component of the last vertex of the
shortest prefix if it weighs at least `1/3`, otherwise the components of the prefix. -/
noncomputable def lightA (ord : List V) (U : Finset V) (w : V → ℕ) : Finset V :=
  match ord[kstar G ord U w - 1]? with
  | some v => if kstar G ord U w ≠ 0 ∧ v ∈ U ∧ ∑ u ∈ U, w u ≤ 3 * ∑ u ∈ comp G U v, w u then
      comp G U v else pre G ord U (kstar G ord U w)
  | none => pre G ord U (kstar G ord U w)

variable (G) in
/-- **The separator from a separator of the connected pieces.** -/
noncomputable def compSep (cs : Finset V → (V → ℕ) → Finset V × Finset V × Finset V)
    (ord : List V) (U : Finset V) (w : V → ℕ) : Finset V × Finset V × Finset V :=
  match heavyC G ord U w with
  | some v =>
    if ∑ u ∈ (cs (comp G U v) w).2.1, w u ≤ ∑ u ∈ (cs (comp G U v) w).2.2, w u then
      ((cs (comp G U v) w).1, (cs (comp G U v) w).2.1 ∪ (U \ comp G U v),
        (cs (comp G U v) w).2.2)
    else ((cs (comp G U v) w).1, (cs (comp G U v) w).2.1,
        (cs (comp G U v) w).2.2 ∪ (U \ comp G U v))
  | none => (∅, lightA G ord U w, U \ lightA G ord U w)

omit [Fintype V] [DecidableRel G.Adj] in
theorem heavyC_some {ord : List V} {U : Finset V} {w : V → ℕ} {v : V}
    (h : heavyC G ord U w = some v) :
    v ∈ U ∧ 2 * ∑ u ∈ U, w u < 3 * ∑ u ∈ comp G U v, w u := by
  have := List.mem_of_mem_head? h
  simpa using (List.mem_filter.1 this).2

omit [Fintype V] [DecidableRel G.Adj] in
theorem heavyC_none {ord : List V} (hord : ∀ v, v ∈ ord) {U : Finset V} {w : V → ℕ}
    (h : heavyC G ord U w = none) :
    ∀ v ∈ U, 3 * ∑ u ∈ comp G U v, w u ≤ 2 * ∑ u ∈ U, w u := by
  intro v hv
  have h' := List.head?_eq_none_iff.1 h
  have := List.filter_eq_nil_iff.1 h' v (hord v)
  simp only [decide_eq_true_eq, not_and, not_lt] at this
  exact this hv

omit [Fintype V] [DecidableRel G.Adj] in
theorem pre_subset (ord : List V) (U : Finset V) (k : ℕ) : pre G ord U k ⊆ U :=
  biUnion_subset.2 fun y _ => comp_subset U y

omit [Fintype V] [DecidableRel G.Adj] in
theorem pre_closed (ord : List V) (U : Finset V) (k : ℕ) :
    ∀ a ∈ pre G ord U k, ∀ b ∈ U, G.Adj a b → b ∈ pre G ord U k := by
  intro a ha b hb hab
  obtain ⟨y, hy, hay⟩ := mem_biUnion.1 ha
  exact mem_biUnion.2 ⟨y, hy, mem_comp_of_adj hay hb hab⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem pre_length {ord : List V} (hord : ∀ v, v ∈ ord) (U : Finset V) :
    pre G ord U ord.length = U :=
  (pre_subset ord U _).antisymm fun u hu =>
    mem_biUnion.2 ⟨u, mem_filter.2 ⟨by simp [hord u], hu⟩, mem_comp_self hu⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem lightA_subset (ord : List V) (U : Finset V) (w : V → ℕ) : lightA G ord U w ⊆ U := by
  unfold lightA
  split
  · split_ifs
    · exact comp_subset U _
    · exact pre_subset ord U _
  · exact pre_subset ord U _

omit [Fintype V] [DecidableRel G.Adj] in
theorem lightA_closed (ord : List V) (U : Finset V) (w : V → ℕ) :
    ∀ a ∈ lightA G ord U w, ∀ b ∈ U, G.Adj a b → b ∈ lightA G ord U w := by
  unfold lightA
  split
  · split_ifs
    · exact fun a ha b hb hab => mem_comp_of_adj ha hb hab
    · exact pre_closed ord U _
  · exact pre_closed ord U _

omit [Fintype V] [DecidableRel G.Adj] in
/-- **The weight of the first part** when no component is heavy: between `1/3` and `2/3`. -/
theorem lightA_weight {ord : List V} (hord : ∀ v, v ∈ ord) {U : Finset V} {w : V → ℕ}
    (hnh : ∀ v ∈ U, 3 * ∑ u ∈ comp G U v, w u ≤ 2 * ∑ u ∈ U, w u) :
    3 * ∑ u ∈ lightA G ord U w, w u ≤ 2 * ∑ u ∈ U, w u ∧
      ∑ u ∈ U, w u ≤ 3 * ∑ u ∈ lightA G ord U w, w u := by
  classical
  have hlen := pre_length (G := G) hord U
  have hspec : ∑ u ∈ U, w u ≤ 3 * ∑ u ∈ pre G ord U (kstar G ord U w), w u ∨
      ord.length < kstar G ord U w := by
    unfold kstar; exact Nat.find_spec (p := fun k => ∑ u ∈ U, w u ≤ 3 * ∑ u ∈ pre G ord U k, w u ∨ ord.length < k) _
  have hKle : kstar G ord U w ≤ ord.length := by
    unfold kstar; exact Nat.find_min' (p := fun k => ∑ u ∈ U, w u ≤ 3 * ∑ u ∈ pre G ord U k, w u ∨ ord.length < k) _ (Or.inl (by rw [hlen]; omega))
  have hmin : ∀ j < kstar G ord U w, 3 * ∑ u ∈ pre G ord U j, w u < ∑ u ∈ U, w u := by
    intro j hj
    have : ¬ (∑ u ∈ U, w u ≤ 3 * ∑ u ∈ pre G ord U j, w u ∨ ord.length < j) := by
      unfold kstar at hj; exact Nat.find_min (p := fun k => ∑ u ∈ U, w u ≤ 3 * ∑ u ∈ pre G ord U k, w u ∨ ord.length < k) _ hj
    omega
  obtain ⟨K, hK⟩ : ∃ K, kstar G ord U w = K := ⟨_, rfl⟩
  rw [hK] at hspec hKle hmin
  have hW : ∑ u ∈ U, w u ≤ 3 * ∑ u ∈ pre G ord U K, w u := hspec.resolve_right (by omega)
  rcases Nat.eq_zero_or_pos K with h0 | hpos
  · subst h0
    have hpre0 : pre G ord U 0 = ∅ := by simp [pre]
    have hA : lightA G ord U w = ∅ := by
      unfold lightA
      rw [hK]
      split
      · simp only [show ¬ (0 ≠ 0) from fun h => h rfl, false_and, ↓reduceIte, hpre0]
      · exact hpre0
    rw [hpre0, sum_empty] at hW
    rw [hA, sum_empty]
    omega
  · have hKl : K - 1 < ord.length := by omega
    have hv : ord[K - 1]? = some ord[K - 1] := List.getElem?_eq_getElem hKl
    set v := ord[K - 1]
    have hsub : pre G ord U K ⊆ pre G ord U (K - 1) ∪ (if v ∈ U then comp G U v else ∅) := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := mem_biUnion.1 hx
      obtain ⟨hyt, hyU⟩ := mem_filter.1 hy
      have ht : ord.take K = ord.take (K - 1) ++ [v] := by
        conv_lhs => rw [show K = (K - 1) + 1 by omega]
        exact List.take_succ_eq_append_getElem hKl
      rw [List.mem_toFinset, ht, List.mem_append, List.mem_singleton] at hyt
      rcases hyt with hyt | rfl
      · exact mem_union_left _ (mem_biUnion.2 ⟨y, mem_filter.2 ⟨List.mem_toFinset.2 hyt, hyU⟩, hxy⟩)
      · exact mem_union_right _ (by simp only [hyU, ↓reduceIte]; exact hxy)
    have hle : ∑ u ∈ pre G ord U K, w u ≤ ∑ u ∈ pre G ord U (K - 1), w u +
        ∑ u ∈ (if v ∈ U then comp G U v else ∅), w u := by
      refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _).trans ?_
      have := sum_union_inter (s₁ := pre G ord U (K - 1))
        (s₂ := if v ∈ U then comp G U v else ∅) (f := w)
      omega
    have hm := hmin (K - 1) (by omega)
    have hA : lightA G ord U w = if K ≠ 0 ∧ v ∈ U ∧ ∑ u ∈ U, w u ≤ 3 * ∑ u ∈ comp G U v, w u
        then comp G U v else pre G ord U K := by
      unfold lightA; rw [hK, hv]
    rw [hA]
    split_ifs with hc
    · exact ⟨hnh v hc.2.1, hc.2.2⟩
    · refine ⟨?_, hW⟩
      by_cases hvU : v ∈ U
      · simp only [hvU, ↓reduceIte] at hle
        have : 3 * ∑ u ∈ comp G U v, w u < ∑ u ∈ U, w u := by
          by_contra hh; exact hc ⟨by omega, hvU, by omega⟩
        omega
      · simp only [hvU, ↓reduceIte, sum_empty] at hle
        omega

omit [Fintype V] [DecidableRel G.Adj] in
/-- **The separator from a separator of the connected pieces meets the specification of
separator routines.** -/
theorem compSep_spec {c : ℝ} (hc : 0 ≤ c) (cs : CompSep G c) {ord : List V}
    (hord : ∀ v, v ∈ ord) (U : Finset V) (w : V → ℕ) :
    IsSeparation G U (compSep G cs.sep ord U w).1 (compSep G cs.sep ord U w).2.1
        (compSep G cs.sep ord U w).2.2 ∧
      ((compSep G cs.sep ord U w).1.card : ℝ) ≤ c * √(#U : ℝ) ∧
      3 * ∑ v ∈ (compSep G cs.sep ord U w).2.1, w v ≤ 2 * ∑ v ∈ U, w v ∧
      3 * ∑ v ∈ (compSep G cs.sep ord U w).2.2, w v ≤ 2 * ∑ v ∈ U, w v := by
  unfold compSep
  split
  · rename_i v hh
    obtain ⟨hvU, hheavy⟩ := heavyC_some hh
    have hCU := comp_subset (G := G) U v
    obtain ⟨hsep, hcard, hA, hB⟩ := cs.spec (comp G U v) w inConn_comp
      ⟨v, mem_comp_self hvU⟩
    have hcl : ∀ a ∈ comp G U v, ∀ b ∈ U, G.Adj a b → b ∈ comp G U v :=
      fun a ha b hb hab => mem_comp_of_adj ha hb hab
    have hext := sep_add_rest hCU hcl hsep
    set r := cs.sep (comp G U v) w
    have hAC : r.2.1 ⊆ comp G U v := fun x hx => by
      rw [← hsep.union_eq]; exact mem_union_left _ (mem_union_right _ hx)
    have hBC : r.2.2 ⊆ comp G U v := fun x hx => by
      rw [← hsep.union_eq]; exact mem_union_right _ hx
    have hAB : ∑ u ∈ r.2.1, w u + ∑ u ∈ r.2.2, w u ≤ ∑ u ∈ comp G U v, w u := by
      rw [← sum_union hsep.disjoint]
      exact sum_le_sum_of_subset_of_nonneg (union_subset hAC hBC) fun _ _ _ => Nat.zero_le _
    have hrest := sum_sdiff hCU (f := w)
    have hAZ := sum_union (disjoint_of_subset_left hAC
      (disjoint_sdiff : Disjoint (comp G U v) (U \ comp G U v))) (f := w)
    have hBZ := sum_union (disjoint_of_subset_left hBC
      (disjoint_sdiff : Disjoint (comp G U v) (U \ comp G U v))) (f := w)
    have hcardU : (r.1.card : ℝ) ≤ c * √(#U : ℝ) :=
      hcard.trans (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (by exact_mod_cast card_le_card hCU)) hc)
    split_ifs with hle
    · exact ⟨hext.1, hcardU, by simp only; omega, by simp only; omega⟩
    · exact ⟨hext.2, hcardU, by simp only; omega, by simp only; omega⟩
  · rename_i hh
    have hnh := heavyC_none hord hh
    obtain ⟨h1, h2⟩ := lightA_weight (G := G) hord (w := w) hnh
    have hrest := sum_sdiff (lightA_subset (G := G) ord U w) (f := w)
    refine ⟨sep_of_closed (lightA_subset ord U w) (lightA_closed ord U w), ?_, h1, ?_⟩
    · simp only [card_empty, Nat.cast_zero]; positivity
    · simp only; omega

variable (G) in
/-- **The separator routine of a separator of the connected pieces** (for a list `ord` of all
the vertices). -/
noncomputable def SepRoutine.ofComp {c : ℝ} (hc : 0 ≤ c) (cs : CompSep G c) (ord : List V)
    (hord : ∀ v, v ∈ ord) : SepRoutine G c where
  sep := compSep G cs.sep ord
  isSeparation U w := (compSep_spec hc cs hord U w).1
  card_le U w := (compSep_spec hc cs hord U w).2.1
  weight_left U w := (compSep_spec hc cs hord U w).2.2.1
  weight_right U w := (compSep_spec hc cs hord U w).2.2.2

end Comp

/-! ### The separator of a connected piece by the separator program -/

section LT

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A separation of the pulled back graph on the whole of `V'` maps to a separation of the range
of the embedding. -/
theorem sep_map {V' : Type*} [Fintype V'] [DecidableEq V'] [DecidableEq V] (e : V' ↪ V)
    {S A B : Finset V'} (h : IsSeparation (G.comap e) univ S A B) :
    IsSeparation G (univ.map e) (S.map e) (A.map e) (B.map e) where
  union_eq := by rw [← map_union, ← map_union, h.union_eq]
  disjoint_sep_left := (disjoint_map e).2 h.disjoint_sep_left
  disjoint_sep_right := (disjoint_map e).2 h.disjoint_sep_right
  disjoint := (disjoint_map e).2 h.disjoint
  not_adj a ha b hb hab := by
    obtain ⟨a', ha', rfl⟩ := mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := mem_map.1 hb
    exact h.not_adj a' ha' b' hb' hab

omit [Fintype V] [DecidableRel G.Adj] in
/-- The pulled back graph of a set connected inside itself is connected. -/
theorem connected_comap {V' : Type*} [Fintype V'] {C : Finset V} (e : V' ↪ V)
    (hr : univ.map e = C) (hC : InConn G C) (hne : C.Nonempty) : (G.comap e).Connected := by
  have hmem : ∀ x, x ∈ C ↔ ∃ a, e a = x := fun x => by
    rw [← hr]; simp
  rw [SimpleGraph.connected_iff]
  refine ⟨fun a b => ?_, ?_⟩
  · have key : ∀ y, ReflTransGen (AdjIn G C) (e a) y → ∀ b, e b = y → (G.comap e).Reachable a b := by
      intro y h
      induction h with
      | refl => intro b hb; rw [e.injective hb]
      | @tail x y _ hxy ih =>
        intro b hb
        obtain ⟨c, rfl⟩ := (hmem x).1 hxy.2.1
        refine (ih c rfl).trans (SimpleGraph.Adj.reachable ?_)
        show G.Adj (e c) (e b)
        rw [hb]; exact hxy.1
    exact key (e b) (hC _ ((hmem _).2 ⟨a, rfl⟩) _ ((hmem _).2 ⟨b, rfl⟩)) b rfl
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨a, -⟩ := (hmem x).1 hx
    exact ⟨a⟩

/-- The vertices of `C` in the order of `ord`. -/
def clist (ord : List V) (C : Finset V) : List V := (ord.filter (· ∈ C)).dedup

/-- The numbering of the vertices of `C` by their positions in `clist`. -/
def cemb (ord : List V) (C : Finset V) : Fin (clist ord C).length ↪ V :=
  ⟨fun i => (clist ord C).get i, List.nodup_iff_injective_get.1 (List.nodup_dedup _)⟩

omit [Fintype V] in
theorem mem_clist {ord : List V} (hord : ∀ v, v ∈ ord) {C : Finset V} {v : V} :
    v ∈ clist ord C ↔ v ∈ C := by
  simp [clist, hord v]

omit [Fintype V] in
theorem map_cemb {ord : List V} (hord : ∀ v, v ∈ ord) (C : Finset V) :
    univ.map (cemb ord C) = C := by
  ext v
  rw [mem_map, ← mem_clist hord (C := C) (v := v)]
  constructor
  · rintro ⟨i, -, rfl⟩; simp [cemb]
  · intro h
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 h
    exact ⟨i, mem_univ _, hi⟩

omit [Fintype V] in
theorem length_clist {ord : List V} (hord : ∀ v, v ∈ ord) (C : Finset V) :
    (clist ord C).length = #C := by
  have := card_map (s := (univ : Finset (Fin (clist ord C).length))) (cemb ord C)
  rw [map_cemb hord, card_univ, Fintype.card_fin] at this
  exact this.symm

variable (R : Kasteleyn.RotationSystem G)

/-- **The input of the separator program for the piece `C`**: the induced rotation system on
the vertices of `C` numbered by `clist`, the weights, the darts numbered by `dartNum`. -/
noncomputable def ltIn (ord : List V) (C : Finset V) (w : V → ℕ) : Input :=
  sepInput (InducedRot.indRot R (cemb ord C)) (fun i => w (cemb ord C i))
    (dartNum (G.comap (cemb ord C)))

/-- **The separator of a connected piece by the separator program**: the vertices of `C`
printed `0`, `1`, `2` by `ltProg` on `ltIn R ord C w` (a single vertex is its own separator). -/
noncomputable def ltComp (ord : List V) (C : Finset V) (w : V → ℕ) :
    Finset V × Finset V × Finset V :=
  if (clist ord C).length ≤ 1 then (C, ∅, ∅) else
    ((univ.filter fun i : Fin (clist ord C).length => (ltOut (ltIn R ord C w)).getD i 0 = 0).map
        (cemb ord C),
      (univ.filter fun i : Fin (clist ord C).length => (ltOut (ltIn R ord C w)).getD i 0 = 1).map
        (cemb ord C),
      (univ.filter fun i : Fin (clist ord C).length => (ltOut (ltIn R ord C w)).getD i 0 = 2).map
        (cemb ord C))

/-- **The separator program separates the connected pieces**, with `#S ≤ 9 √#C`. -/
theorem ltComp_spec (hR : R.IsPlane) {ord : List V} (hord : ∀ v, v ∈ ord) (C : Finset V)
    (w : V → ℕ) (hC : InConn G C) (hne : C.Nonempty) :
    IsSeparation G C (ltComp R ord C w).1 (ltComp R ord C w).2.1 (ltComp R ord C w).2.2 ∧
      ((ltComp R ord C w).1.card : ℝ) ≤ 9 * √(#C : ℝ) ∧
      3 * ∑ v ∈ (ltComp R ord C w).2.1, w v ≤ 2 * ∑ v ∈ C, w v ∧
      3 * ∑ v ∈ (ltComp R ord C w).2.2, w v ≤ 2 * ∑ v ∈ C, w v := by
  have hlen := length_clist hord C
  unfold ltComp
  split_ifs with h1
  · have hC1 : #C = 1 := by have := card_pos.2 hne; omega
    refine ⟨⟨by simp, disjoint_empty_right _, disjoint_empty_right _, disjoint_empty_left _,
      fun a ha => by simp at ha⟩, ?_, by simp, by simp⟩
    rw [hC1]; norm_num
  · have hr : univ.map (cemb ord C) = C := map_cemb hord C
    have hplane := InducedRot.indRot_isPlane R (cemb ord C) hR
      (connected_comap (cemb ord C) hr hC hne) (by rw [Fintype.card_fin]; omega)
    obtain ⟨out, hrun, hsep, hcard, hA, hB⟩ := ltProg_spec (G.comap (cemb ord C))
      (InducedRot.indRot R (cemb ord C)) hplane (fun i => w (cemb ord C i))
      (dartNum (G.comap (cemb ord C))) (fun d d' h => dartNum_lt _ h) _ le_rfl
    have hout : ltOut (ltIn R ord C w) = out := ltOut_eq (P := ltIn R ord C w) hrun
    rw [hout]
    have hsum : ∑ v ∈ C, w v = ∑ i, w (cemb ord C i) := by
      conv_lhs => rw [← hr]
      rw [sum_map]
    have hsep' := sep_map (cemb ord C) hsep
    rw [hr] at hsep'
    refine ⟨hsep', ?_, ?_, ?_⟩
    · rw [card_map]
      have hk : ((clist ord C).length : ℝ) = #C := by exact_mod_cast hlen
      have h1k : (1 : ℝ) ≤ √((clist ord C).length : ℝ) := by
        rw [Real.one_le_sqrt]; exact_mod_cast (show 1 ≤ (clist ord C).length by omega)
      rw [← hk]
      linarith
    · rw [sum_map, hsum]; exact hA
    · rw [sum_map, hsum]; exact hB

/-- **The separator program as a separator of the connected pieces.** -/
noncomputable def ltCompSep (hR : R.IsPlane) (ord : List V) (hord : ∀ v, v ∈ ord) :
    CompSep G 9 where
  sep := ltComp R ord
  spec C w hC hne := ltComp_spec R hR hord C w hC hne

/-- **The separator routine of the separator program** for a plane rotation system `R` and a
list `ord` of all the vertices (`#S ≤ 9 √#U`): the separator of the heavy component, or the
grouping of the components (`SepRoutine.ofComp`), with the connected pieces separated by
`ltProg` on their induced rotation systems. -/
noncomputable def ltRoutine (hR : R.IsPlane) (ord : List V) (hord : ∀ v, v ∈ ord) :
    SepRoutine G 9 :=
  SepRoutine.ofComp G (by norm_num) (ltCompSep R hR ord hord) ord hord

/-- **The explicit separator tree of the square with the separator program**: for a plane
rotation system of `G` of maximum degree at most `Δ`, a list `ord` of all the vertices and
`T ≥ 40 (177 · 9 (Δ + 1)² + 1)`, the tree built from `(ltRoutine R hR ord hord).square hΔ` is a
good tree of the square of `G`. -/
theorem buildTree_ltRoutine_square_spec (hR : R.IsPlane) {ord : List V} (hord : ∀ v, v ∈ ord)
    {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) {T : ℕ} (hT : sepTreeConst (9 * ((Δ : ℝ) + 1) ^ 2) ≤ T) :
    GoodTree (PlanarSeparator.square G) T (SepRoutine.buildTree (PlanarSeparator.square G)
      ((ltRoutine R hR ord hord).square hΔ).sep ord T) :=
  (ltRoutine R hR ord hord).buildTree_square_spec (by norm_num) hΔ hT hord

/-- The same for `G` itself. -/
theorem buildTree_ltRoutine_spec (hR : R.IsPlane) {ord : List V} (hord : ∀ v, v ∈ ord)
    {T : ℕ} (hT : sepTreeConst 9 ≤ T) :
    GoodTree G T (SepRoutine.buildTree G (ltRoutine R hR ord hord).sep ord T) :=
  (ltRoutine R hR ord hord).buildTree_spec (by norm_num) hT hord

end LT

end PlanarSeparator
