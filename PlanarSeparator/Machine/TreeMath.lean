module

public import PlanarSeparator.Machine.SquareProg

/-!
# The separator tree on the machine: the functional models

Pure models of the worklist programs of `PlanarSeparator/Machine/TreeProg.lean`, related to
`PlanarSeparator.SepRoutine.divide`, `splitW` and `buildAux`.

* `dv`: the division with the machine's state, the separator flags and the piece of every
  vertex named by its least vertex (`dv_spec`: the flags are those of the separator of `divide`,
  the name of a vertex outside the separator is the least vertex of its piece).
* `dFold`: the worklist of frames processed in order (`dFold_step_leaf`, `dFold_step_split`:
  one round of the worklist loop keeps `dFold`).
* `bsplit_map_congr`, `bsplit_mem`, `dedup_map_of_injOn`: the balanced split along a map.
* `splitW_eq_sp`: `splitW` with the machine's names (`spSt`, `spList`, `spCnt`): the separator
  is the set of flags `1`, the parts are given by `bsplit` of the list of names of the pieces
  (each piece named by its least vertex) with the counts of names.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset

variable {N : ℕ}

/-! ### The division with the machine's state -/

/-- The state of the division: separator flags `sf` and piece names `pid`. -/
structure DSt where
  /-- The separator flags. -/
  sf : ℕ → ℕ
  /-- The piece names. -/
  pid : ℕ → ℕ

/-- A leaf: every vertex of `U` named by the least vertex of `U`. -/
def dLeaf (U : Finset (Fin N)) (s : DSt) : DSt :=
  ⟨s.sf, fun x => if x ∈ UN U then lv U 0 else s.pid x⟩

/-- The flags `1` on `S`. -/
def dMark (S : Finset (Fin N)) (s : DSt) : DSt :=
  ⟨fun x => if x ∈ UN S then 1 else s.sf x, s.pid⟩

/-- **The division with the machine's state**, as `SepRoutine.divide`. -/
def dv (sep : Finset (Fin N) → (Fin N → ℕ) → Finset (Fin N) × Finset (Fin N) × Finset (Fin N))
    (μ : Fin N → ℕ) (L : ℕ) : ℕ → Finset (Fin N) → DSt → DSt
  | 0, U, s => dLeaf U s
  | k + 1, U, s =>
    if ∑ v ∈ U, μ v ≤ L then dLeaf U s
    else dv sep μ L k (sep U μ).2.2 (dv sep μ L k (sep U μ).2.1 (dMark (sep U μ).1 s))

theorem mk_mk (A B : Finset (Fin N)) (f : ℕ → ℕ) :
    (fun x => if x ∈ UN A then 1 else (fun x => if x ∈ UN B then 1 else f x) x) =
      (fun x => if x ∈ UN (B ∪ A) then 1 else f x) := by
  funext x
  simp only [UN, map_union, mem_union]
  by_cases h1 : x ∈ A.map Fin.valEmbedding
  · simp [h1]
  · by_cases h2 : x ∈ B.map Fin.valEmbedding <;> simp [h1, h2]

theorem lv_zero_mem {U : Finset (Fin N)} {v : Fin N} (hv : v ∈ U) : lv U 0 ∈ UN U :=
  lv_mem_UN U (card_pos.2 ⟨v, hv⟩)

/-- **The division with the machine's state** (fuel `k`, any `U`): the flags of the separator
`S` of `divide`, the names kept outside `U`, and every vertex `v ∈ U \ S` named by the least
vertex of its piece `κ v`, a class of `U \ S`. -/
theorem dv_spec {H : SimpleGraph (Fin N)}
    {sep : Finset (Fin N) → (Fin N → ℕ) → Finset (Fin N) × Finset (Fin N) × Finset (Fin N)}
    (hsep : ∀ U w, IsSeparation H U (sep U w).1 (sep U w).2.1 (sep U w).2.2) (μ : Fin N → ℕ)
    (L : ℕ) : ∀ (k : ℕ) (U : Finset (Fin N)) (s : DSt),
      let d := SepRoutine.divide sep μ L k U
      (dv sep μ L k U s).sf = (fun x => if x ∈ UN d.1 then 1 else s.sf x) ∧
      (∀ x, x ∉ UN U → (dv sep μ L k U s).pid x = s.pid x) ∧
      d.1 ⊆ U ∧
      (∀ v ∈ U \ d.1, (dv sep μ L k U s).pid v = lv (d.2 v) 0 ∧ v ∈ d.2 v ∧
        ∀ y ∈ d.2 v, y ∈ U \ d.1 ∧ d.2 y = d.2 v) := by
  have hleaf : ∀ (U : Finset (Fin N)) (s : DSt),
      (dLeaf U s).sf = (fun x => if x ∈ UN (∅ : Finset (Fin N)) then 1 else s.sf x) ∧
      (∀ x, x ∉ UN U → (dLeaf U s).pid x = s.pid x) ∧ (∅ : Finset (Fin N)) ⊆ U ∧
      (∀ v ∈ U \ ∅, (dLeaf U s).pid v = lv ((fun _ => U) v) 0 ∧ v ∈ (fun _ => U) v ∧
        ∀ y ∈ (fun _ : Fin N => U) v, y ∈ U \ ∅ ∧ (fun _ : Fin N => U) y = (fun _ => U) v) := by
    intro U s
    refine ⟨?_, fun x hx => ?_, empty_subset _, fun v hv => ?_⟩
    · funext x; simp [dLeaf, UN]
    · simp only [dLeaf, hx, ite_false]
    · rw [sdiff_empty] at hv
      refine ⟨?_, hv, fun y hy => ⟨by rwa [sdiff_empty], rfl⟩⟩
      simp only [dLeaf, val_mem_UN.2 hv, ite_true]
  intro k
  induction k with
  | zero => intro U s; exact hleaf U s
  | succ k ih =>
  intro U s
  by_cases hL : ∑ v ∈ U, μ v ≤ L
  · have e1 : dv sep μ L (k + 1) U s = dLeaf U s := by simp only [dv, hL, ite_true]
    have e2 : SepRoutine.divide sep μ L (k + 1) U = (∅, fun _ => U) := by
      simp only [SepRoutine.divide, hL, ite_true]
    rw [e1, e2]; exact hleaf U s
  have e1 : dv sep μ L (k + 1) U s =
      dv sep μ L k (sep U μ).2.2 (dv sep μ L k (sep U μ).2.1 (dMark (sep U μ).1 s)) := by
    simp only [dv, hL, ite_false]
  have e2 : SepRoutine.divide sep μ L (k + 1) U =
      ((sep U μ).1 ∪ (SepRoutine.divide sep μ L k (sep U μ).2.1).1 ∪
        (SepRoutine.divide sep μ L k (sep U μ).2.2).1, fun v => if v ∈ (sep U μ).2.1 then
        (SepRoutine.divide sep μ L k (sep U μ).2.1).2 v else
        (SepRoutine.divide sep μ L k (sep U μ).2.2).2 v) := by
    simp only [SepRoutine.divide, hL, ite_false]
  rw [e1, e2]
  have hs := hsep U μ
  set S := (sep U μ).1
  set A := (sep U μ).2.1
  set B := (sep U μ).2.2
  set d₁ := SepRoutine.divide sep μ L k A
  set d₂ := SepRoutine.divide sep μ L k B
  set s₁ := dv sep μ L k A (dMark S s)
  obtain ⟨f1, p1, sub1, c1⟩ := ih A (dMark S s)
  obtain ⟨f2, p2, sub2, c2⟩ := ih B s₁
  have hAU : A ⊆ U := fun x hx => hs.union_eq ▸ mem_union_left _ (mem_union_right _ hx)
  have hBU : B ⊆ U := fun x hx => hs.union_eq ▸ mem_union_right _ hx
  have hSU : S ⊆ U := fun x hx => hs.union_eq ▸ mem_union_left _ (mem_union_left _ hx)
  have hAB := hs.disjoint
  have hSA := hs.disjoint_sep_left
  have hSB := hs.disjoint_sep_right
  refine ⟨?_, fun x hx => ?_, ?_, fun v hv => ?_⟩
  · rw [f2, show s₁.sf = _ from f1]
    simp only [dMark]
    rw [mk_mk, mk_mk, ← union_assoc]
  · rw [p2 x (fun h => hx (by
      obtain ⟨hxN, hm⟩ := mem_UN.1 h; exact mem_UN.2 ⟨hxN, hBU hm⟩)),
      p1 x (fun h => hx (by
      obtain ⟨hxN, hm⟩ := mem_UN.1 h; exact mem_UN.2 ⟨hxN, hAU hm⟩))]
    rfl
  · exact union_subset (union_subset hSU (sub1.trans hAU)) (sub2.trans hBU)
  · obtain ⟨hvU, hvS⟩ := mem_sdiff.1 hv
    simp only [mem_union, not_or] at hvS
    obtain ⟨⟨hvS0, hvS1⟩, hvS2⟩ := hvS
    have hAB' : ∀ y, y ∈ A → y ∉ B := fun y h1 h2 => disjoint_left.1 hAB h1 h2
    by_cases hvA : v ∈ A
    · simp only [hvA, ite_true]
      have hvB : v ∉ B := hAB' v hvA
      obtain ⟨q1, q2, q3⟩ := c1 v (mem_sdiff.2 ⟨hvA, hvS1⟩)
      refine ⟨?_, q2, fun y hy => ?_⟩
      · rw [p2 v (fun h => hvB (val_mem_UN.1 h)), q1]
      · obtain ⟨hyA, hyD⟩ := mem_sdiff.1 (q3 y hy).1
        refine ⟨mem_sdiff.2 ⟨hAU hyA, ?_⟩, by simp only [hyA, ite_true]; exact (q3 y hy).2⟩
        simp only [mem_union, not_or]
        exact ⟨⟨fun h => disjoint_left.1 hSA h hyA, hyD⟩,
          fun h => hAB' y hyA (sub2 h)⟩
    · simp only [hvA, ite_false]
      have hvB : v ∈ B := by
        have := hs.union_eq ▸ hvU
        simp only [mem_union] at this
        rcases this with (h | h) | h
        · exact absurd h hvS0
        · exact absurd h hvA
        · exact h
      obtain ⟨q1, q2, q3⟩ := c2 v (mem_sdiff.2 ⟨hvB, hvS2⟩)
      refine ⟨q1, q2, fun y hy => ?_⟩
      obtain ⟨hyB, hyD⟩ := mem_sdiff.1 (q3 y hy).1
      have hyA : y ∉ A := fun h => hAB' y h hyB
      refine ⟨mem_sdiff.2 ⟨hBU hyB, ?_⟩, by simp only [hyA, ite_false]; exact (q3 y hy).2⟩
      simp only [mem_union, not_or]
      exact ⟨⟨fun h => disjoint_left.1 hSB h hyB, fun h => hyA (sub1 h)⟩, hyD⟩

/-! ### The worklist -/

/-- The frames `(U, fuel)` of the worklist processed in order. -/
def dFold (sep : Finset (Fin N) → (Fin N → ℕ) → Finset (Fin N) × Finset (Fin N) × Finset (Fin N))
    (μ : Fin N → ℕ) (L : ℕ) : List (Finset (Fin N) × ℕ) → DSt → DSt
  | [], s => s
  | f :: l, s => dFold sep μ L l (dv sep μ L f.2 f.1 s)

/-- A leaf round of the worklist (fuel `0`, or weight at most `L`). -/
theorem dFold_step_leaf
    (sep : Finset (Fin N) → (Fin N → ℕ) → Finset (Fin N) × Finset (Fin N) × Finset (Fin N))
    (μ : Fin N → ℕ) (L : ℕ) {U : Finset (Fin N)} {k : ℕ} (h : k = 0 ∨ ∑ v ∈ U, μ v ≤ L)
    (l : List (Finset (Fin N) × ℕ)) (s : DSt) :
    dFold sep μ L ((U, k) :: l) s = dFold sep μ L l (dLeaf U s) := by
  simp only [dFold]
  congr 1
  rcases k with _ | k
  · rfl
  · simp only [dv, h.resolve_left (by omega), ite_true]

/-- A splitting round of the worklist: the frame `(U, k + 1)` of weight above `L` replaced by
the frames of the two parts. -/
theorem dFold_step_split
    (sep : Finset (Fin N) → (Fin N → ℕ) → Finset (Fin N) × Finset (Fin N) × Finset (Fin N))
    (μ : Fin N → ℕ) (L : ℕ) {U : Finset (Fin N)} {k : ℕ} (h : ¬ ∑ v ∈ U, μ v ≤ L)
    (l : List (Finset (Fin N) × ℕ)) (s : DSt) :
    dFold sep μ L ((U, k + 1) :: l) s =
      dFold sep μ L (((sep U μ).2.1, k) :: ((sep U μ).2.2, k) :: l) (dMark (sep U μ).1 s) := by
  simp only [dFold, dv, h, ite_false]

/-! ### The balanced split along a map -/

section bsplitMap

variable {ι κ : Type*}

theorem lsum_map_congr {x : ι → ℕ} {x' : κ → ℕ} {f : ι → κ} {l : List ι}
    (h : ∀ i ∈ l, x' (f i) = x i) : lsum x' (l.map f) = lsum x l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, lsum_cons, h i List.mem_cons_self,
      ih fun j hj => h j (List.mem_cons_of_mem _ hj)]

theorem gpre_map_congr {x : ι → ℕ} {x' : κ → ℕ} {f : ι → κ} (X : ℕ) :
    ∀ (l : List ι) (s : ℕ), (∀ i ∈ l, x' (f i) = x i) →
      gpre x' X s (l.map f) = (gpre x X s l).map f
  | [], _, _ => rfl
  | i :: l, s, h => by
    simp only [List.map_cons, gpre, h i List.mem_cons_self]
    split_ifs
    · rw [gpre_map_congr X l _ fun j hj => h j (List.mem_cons_of_mem _ hj), List.map_cons]
    · rfl

theorem bwalk_map_congr {x y : ι → ℕ} {x' y' : κ → ℕ} {f : ι → κ} (X p q : ℕ) :
    ∀ (k : ℕ) (r a acc : List ι), (∀ i ∈ r ++ a ++ acc, x' (f i) = x i ∧ y' (f i) = y i) →
      bwalk x' y' X p q k (r.map f) (a.map f) (acc.map f) = (bwalk x y X p q k r a acc).map f
  | 0, r, a, acc, _ => by simp [bwalk]
  | k + 1, r, a, acc, h => by
    have hx : ∀ l : List ι, (∀ i ∈ l, i ∈ r ++ a ++ acc) → lsum x' (l.map f) = lsum x l :=
      fun l hl => lsum_map_congr fun i hi => (h i (hl i hi)).1
    have hy : ∀ l : List ι, (∀ i ∈ l, i ∈ r ++ a ++ acc) → lsum y' (l.map f) = lsum y l :=
      fun l hl => lsum_map_congr fun i hi => (h i (hl i hi)).2
    rcases a with _ | ⟨j, a'⟩
    · rcases r with _ | ⟨i, r'⟩
      · simp [bwalk]
      · simp only [List.map_cons, List.map_nil, bwalk]
        rw [← List.map_append, hy (r' ++ acc) (fun i hi => by simp at hi ⊢; tauto)]
        split_ifs
        · simp
        · exact bwalk_map_congr X p q k r' [] acc (fun i hi => h i (by simp at hi ⊢; tauto))
    · simp only [List.map_cons, bwalk]
      rw [← List.map_append, hx (r ++ acc) (fun i hi => by simp at hi ⊢; tauto)]
      split_ifs with h1
      · rw [← List.map_cons]
        exact bwalk_map_congr X p q k r a' (j :: acc) (fun i hi => h i (by simp at hi ⊢; tauto))
      · rcases r with _ | ⟨i, r'⟩
        · rfl
        · simp only [List.map_cons]
          rw [← List.map_append, hy (r' ++ acc) (fun i hi => by simp at hi ⊢; tauto)]
          split_ifs
          · simp
          · rw [← List.map_cons]
            exact bwalk_map_congr X p q k r' (j :: a') acc
              (fun i hi => h i (by simp at hi ⊢; tauto))

/-- **The balanced split along a map** whose measures agree on the list. -/
theorem bsplit_map_congr {x y : ι → ℕ} {x' y' : κ → ℕ} {f : ι → κ} (p q : ℕ) {l : List ι}
    (h : ∀ i ∈ l, x' (f i) = x i ∧ y' (f i) = y i) :
    bsplit x' y' p q (l.map f) = (bsplit x y p q l).map f := by
  have hx := lsum_map_congr (l := l) fun i hi => (h i hi).1
  have hg := gpre_map_congr (x := x) (x' := x') (f := f) (lsum x l) l 0 fun i hi => (h i hi).1
  have hd : ∀ m : List ι, m <+: l ∨ m <:+ l → ∀ i ∈ m, i ∈ l := fun m hm i hi => by
    rcases hm with hm | hm
    · exact hm.subset hi
    · exact hm.subset hi
  have hJ1 : gpre x (lsum x l) 0 l <+: l := by
    have := (gpre_spec x (lsum x l) l 0 (Nat.zero_le _)).1
    exact ⟨_, this⟩
  have hJ2 : l.drop (gpre x (lsum x l) 0 l).length <:+ l := List.drop_suffix _ _
  have hyJ1 : lsum y' ((gpre x (lsum x l) 0 l).map f) = lsum y (gpre x (lsum x l) 0 l) :=
    lsum_map_congr fun i hi => (h i (hd _ (Or.inl hJ1) i hi)).2
  have hyJ2 : lsum y' ((l.drop (gpre x (lsum x l) 0 l).length).map f) =
      lsum y (l.drop (gpre x (lsum x l) 0 l).length) :=
    lsum_map_congr fun i hi => (h i (hd _ (Or.inr hJ2) i hi)).2
  simp only [bsplit]
  rw [hx, hg, List.length_map, ← List.map_drop, hyJ1, hyJ2, List.length_map]
  split_ifs
  · rw [← List.map_nil (f := f)]
    exact bwalk_map_congr _ p q _ _ _ [] fun i hi => by
      simp only [List.append_nil, List.mem_append] at hi
      rcases hi with hi | hi
      · exact h i (hd _ (Or.inl hJ1) i hi)
      · exact h i (hd _ (Or.inr hJ2) i hi)
  · rw [← List.map_nil (f := f)]
    exact bwalk_map_congr _ p q _ _ _ [] fun i hi => by
      simp only [List.append_nil, List.mem_append] at hi
      rcases hi with hi | hi
      · exact h i (hd _ (Or.inr hJ2) i hi)
      · exact h i (hd _ (Or.inl hJ1) i hi)
  · rfl

theorem bwalk_mem {x y : ι → ℕ} (X p q : ℕ) :
    ∀ (k : ℕ) (r a acc : List ι), ∀ i ∈ bwalk x y X p q k r a acc, i ∈ r ++ a ++ acc
  | 0, r, a, acc, i, hi => by simp only [bwalk, List.mem_append] at hi ⊢; tauto
  | k + 1, r, a, acc, i, hi => by
    rcases a with _ | ⟨j, a'⟩
    · rcases r with _ | ⟨i', r'⟩
      · simp only [bwalk] at hi; simp [hi]
      · simp only [bwalk] at hi
        split_ifs at hi
        · simp only [List.mem_append] at hi ⊢; simp; tauto
        · have := bwalk_mem X p q k r' [] acc i hi
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff] at this ⊢; tauto
    · simp only [bwalk] at hi
      split_ifs at hi
      · have := bwalk_mem X p q k r a' (j :: acc) i hi
        simp only [List.mem_append, List.mem_cons] at this ⊢; tauto
      · rcases r with _ | ⟨i', r'⟩
        · simp only at hi; simp [hi]
        · simp only at hi
          split_ifs at hi
          · simp only [List.mem_append, List.mem_cons] at hi ⊢; tauto
          · have := bwalk_mem X p q k r' (j :: a') acc i hi
            simp only [List.mem_append, List.mem_cons] at this ⊢; tauto

theorem bsplit_mem {x y : ι → ℕ} (p q : ℕ) {l : List ι} {i : ι} (hi : i ∈ bsplit x y p q l) :
    i ∈ l := by
  have hJ1 : gpre x (lsum x l) 0 l <+: l := ⟨_, (gpre_spec x (lsum x l) l 0 (Nat.zero_le _)).1⟩
  have hJ2 : l.drop (gpre x (lsum x l) 0 l).length <:+ l := List.drop_suffix _ _
  simp only [bsplit] at hi
  split_ifs at hi
  · have := bwalk_mem _ p q _ _ _ [] i hi
    simp only [List.append_nil, List.mem_append] at this
    rcases this with h | h
    · exact hJ1.subset h
    · exact hJ2.subset h
  · have := bwalk_mem _ p q _ _ _ [] i hi
    simp only [List.append_nil, List.mem_append] at this
    rcases this with h | h
    · exact hJ2.subset h
    · exact hJ1.subset h
  · exact hJ1.subset hi

theorem dedup_map_of_injOn [DecidableEq ι] [DecidableEq κ] {f : ι → κ} :
    ∀ {l : List ι}, (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).dedup = l.dedup.map f
  | [], _ => rfl
  | i :: l, h => by
    have ih := dedup_map_of_injOn (l := l) fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b
      (List.mem_cons_of_mem _ hb)
    rw [List.map_cons]
    by_cases hi : i ∈ l
    · have hfi : f i ∈ l.map f := List.mem_map_of_mem hi
      rw [List.dedup_cons_of_mem hfi, List.dedup_cons_of_mem hi, ih]
    · have hfi : f i ∉ l.map f := by
        intro hm
        obtain ⟨j, hj, he⟩ := List.mem_map.1 hm
        exact hi (h j (List.mem_cons_of_mem _ hj) i List.mem_cons_self he ▸ hj)
      rw [List.dedup_cons_of_notMem hfi, List.dedup_cons_of_notMem hi, ih, List.map_cons]

end bsplitMap

/-! ### The split of a node with the machine's names -/

section spW

open NestedDissection

variable {H : SimpleGraph (Fin N)} [DecidableRel H.Adj]

/-- The weights of `splitW`. -/
def spMu (H : SimpleGraph (Fin N)) [DecidableRel H.Adj] (W : Finset (Fin N)) : Fin N → ℕ :=
  fun v => if v ∈ W then 20 * max #(bdry H W) 1 else if v ∈ bdry H W then 20 * #W else 0

/-- The bound of the pieces of `splitW`. -/
def spL (H : SimpleGraph (Fin N)) [DecidableRel H.Adj] (W : Finset (Fin N)) : ℕ :=
  #W * max #(bdry H W) 1

/-- The machine's division state of `splitW`. -/
def spSt (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (sep : Finset (Fin N) → (Fin N → ℕ) → Finset (Fin N) × Finset (Fin N) × Finset (Fin N))
    (W : Finset (Fin N)) (s0 : DSt) : DSt :=
  dv sep (spMu H W) (spL H W) #(W ∪ bdry H W) (W ∪ bdry H W) s0

/-- The names of the pieces, by the last vertex of each piece in increasing order. -/
def spList (pid : ℕ → ℕ) (D : Finset (Fin N)) : List ℕ :=
  (((List.range N).filter (· ∈ UN D)).map pid).dedup

/-- The number of vertices of `X` named `i`. -/
def spCnt (pid : ℕ → ℕ) (X : Finset (Fin N)) (i : ℕ) : ℕ := #(X.filter fun v : Fin N => pid v = i)

theorem range_filter_UN (D : Finset (Fin N)) :
    (List.range N).filter (· ∈ UN D) = ((ord N).filter (· ∈ D)).map Fin.val := by
  rw [← List.map_coe_finRange_eq_range, List.filter_map]
  congr 1
  refine List.filter_congr fun v _ => ?_
  simp only [Function.comp, val_mem_UN]

/-- **`splitW` with the machine's names**: with the separator flags `sf` and the names `pid` of
`spSt` (from flags `0`), the separator is the set of flags `1`, and the parts are given by the
balanced split of the list of names with the counts of names. -/
theorem splitW_eq_sp
    {sep : Finset (Fin N) → (Fin N → ℕ) → Finset (Fin N) × Finset (Fin N) × Finset (Fin N)}
    (hsep : ∀ U w, IsSeparation H U (sep U w).1 (sep U w).2.1 (sep U w).2.2) (W : Finset (Fin N))
    (s0 : DSt) (h0 : ∀ x, s0.sf x = 0) :
    let st := spSt H sep W s0
    let Sm := univ.filter fun v : Fin N => st.sf v = 1
    let B := bdry H W
    let J := bsplit (spCnt st.pid (W \ Sm)) (spCnt st.pid (B \ Sm)) 5 (3 * #B)
      (spList st.pid ((W ∪ B) \ Sm))
    SepRoutine.splitW H sep (ord N) W =
      (W ∩ Sm, (W \ Sm).filter (fun v : Fin N => st.pid v ∈ J),
        (W \ Sm).filter (fun v : Fin N => st.pid v ∉ J)) := by
  intro st Sm B J
  obtain ⟨hf, -, -, hc⟩ := dv_spec hsep (spMu H W) (spL H W) #(W ∪ B) (W ∪ B) s0
  set d := SepRoutine.divide sep (spMu H W) (spL H W) #(W ∪ B) (W ∪ B) with hd
  have hS : Sm = d.1 := by
    ext v
    simp only [Sm, mem_filter, mem_univ, true_and, st, spSt]
    rw [hf]
    simp only [val_mem_UN, h0]
    split_ifs with h <;> simp [h]
  set κ := d.2
  set D := (W ∪ B) \ d.1
  have hpid : ∀ v ∈ D, st.pid v = lv (κ v) 0 := fun v hv => (hc v hv).1
  have hinj : ∀ u ∈ D, ∀ v ∈ D, lv (κ u) 0 = lv (κ v) 0 → κ u = κ v := by
    intro u hu v hv he
    have h1 := lv_zero_mem (hc u hu).2.1
    obtain ⟨hyN, hy⟩ := mem_UN.1 h1
    have hy' : (⟨lv (κ u) 0, hyN⟩ : Fin N) ∈ κ v := by
      have h2 := lv_zero_mem (hc v hv).2.1
      rw [← he] at h2
      obtain ⟨_, h2'⟩ := mem_UN.1 h2
      exact h2'
    rw [← ((hc u hu).2.2 _ hy).2, ((hc v hv).2.2 _ hy').2]
  have hl : spList st.pid ((W ∪ B) \ Sm) =
      (((ord N).filter (· ∈ D)).map κ).dedup.map (fun P => lv P 0) := by
    rw [spList, hS, range_filter_UN, List.map_map, ← dedup_map_of_injOn, List.map_map]
    · congr 1
      refine List.map_congr_left fun v hv => ?_
      simp only [Function.comp]
      exact hpid v (by simpa [D] using (List.mem_filter.1 hv).2)
    · intro P hP Q hQ he
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hP
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hQ
      exact hinj u (by simpa [D] using (List.mem_filter.1 hu).2) v
        (by simpa [D] using (List.mem_filter.1 hv).2) he
  have hpc : ∀ (X : Finset (Fin N)), X ⊆ D → ∀ u ∈ D,
      spCnt st.pid X (lv (κ u) 0) = #(X.filter fun v => κ v = κ u) := by
    intro X hX u hu
    unfold spCnt
    congr 1
    refine filter_congr fun v hv => ?_
    rw [hpid v (hX hv)]
    exact ⟨hinj v (hX hv) u hu, fun h => by rw [h]⟩
  have hmemL : ∀ P ∈ ((ord N).filter (· ∈ D)).map κ, ∃ u ∈ D, P = κ u := by
    intro P hP
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hP
    exact ⟨u, by simpa [D] using (List.mem_filter.1 hu).2, rfl⟩
  have hJ : J = (bsplit (fun i => #((W \ d.1).filter fun v => κ v = i))
      (fun i => #((B \ d.1).filter fun v => κ v = i)) 5 (3 * #B)
      (((ord N).filter (· ∈ D)).map κ).dedup).map (fun P => lv P 0) := by
    simp only [J]
    rw [hl, hS]
    refine bsplit_map_congr 5 (3 * #B) fun P hP => ?_
    obtain ⟨u, hu, rfl⟩ := hmemL P (List.mem_dedup.1 hP)
    exact ⟨hpc _ (sdiff_subset_sdiff subset_union_left le_rfl) u hu,
      hpc _ (sdiff_subset_sdiff subset_union_right le_rfl) u hu⟩
  have hmem : ∀ v ∈ W \ d.1, st.pid v ∈ J ↔ κ v ∈ (bsplit (fun i => #((W \ d.1).filter
      fun v => κ v = i)) (fun i => #((B \ d.1).filter fun v => κ v = i)) 5 (3 * #B)
      (((ord N).filter (· ∈ D)).map κ).dedup).toFinset := by
    intro v hv
    have hvD : v ∈ D := sdiff_subset_sdiff subset_union_left le_rfl hv
    rw [hJ, hpid v hvD, List.mem_map, List.mem_toFinset]
    constructor
    · rintro ⟨P, hP, he⟩
      obtain ⟨u, hu, rfl⟩ := hmemL P (List.mem_dedup.1 (bsplit_mem _ _ hP))
      rwa [← hinj u hu v hvD he]
    · intro h; exact ⟨κ v, h, rfl⟩
  rw [hS]
  simp only [SepRoutine.splitW]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · exact filter_congr fun v hv => (hmem v hv).symm
  · exact filter_congr fun v hv => not_congr (hmem v hv).symm

end spW

end Piece

end PlanarSeparator
