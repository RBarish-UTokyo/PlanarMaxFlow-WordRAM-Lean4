module

public import PlanarFlow.STFlow.Cost
public import PlanarFlow.Plane.Pivot
public import PlanarFlow.BKMNW.Matching

/-!
# Counting the pivots of the single-source single-sink algorithm

The cost of the algorithm (`PlanarFlow/STFlow/Cost.lean`) is `O(n log n)` under `PivotBound`:
at most `m + 1` steps on `m` darts. This file reduces `PivotBound` to the pivot lemma
(`PlanarFlow/Plane/Pivot.lean`) and isolates the statement that remains.

## The trees of a run

Along a run (`traj`), every step but the last is a pivot (`run_pivot`), and a pivot adds its
dart `e` (the bottleneck, crossed forward by the path of the cotree) to the set of parent darts
(`parSet`) of the dual tree (`pivot_enter`). So the number of steps is at most one more than the
number of darts entering the sequence of trees, and by double counting
(`PlanarFlow.Pivot.sum_card_sdiff_le`) at most `m + 1` **if every dart enters at most once**.

## The remaining hypothesis

The levels of Erickson (the sums `psum P` of a unit flow `P` along the paths of the tree) give the
path of the cotree: `chi d = psum (face d) + P d - psum (face (rev d))` (`chi_eq_psum`). A dart
that enters twice is crossed forward by the path of the cotree at both entries. The hypothesis
`NoReentry M` excludes this: along a run of pivots, **a dart that pivots into the dual tree is
never again crossed forward by the path of the cotree**. This is the statement that each dart
pivots into the tree at most once (Borradaile and Klein, J. ACM 56(2), 2009; Erickson, SODA
2010), **not proved here**: its proof is the planar topology of the leftmost paths (they move
monotonically in the universal cover of the plane minus `s` and `t`), which this development does
not have. The count only needs the weaker `EnterOnce M` (**each dart enters the set of parent darts
at most once** along a run of pivots; `enterOnce_of_noReentry`). Under it:

* `steps_le_of_enterOnce`, `steps_le_of_noReentry`: every run takes at most `m + 1` steps;
* `pivotBound_of_enterOnce`, `pivotBound_of_noReentry`: **`PivotBound M`**;
* `stflowCost_le_of_enterOnce`, `stflowCost_le_of_noReentry`: the cost is at most `36 K m lg m`.

The capacities play no role: `NoReentry` follows
from the same statement for any sequence of *free pivots* (any dart crossed forward whose head
face is not above its tail face; `noReentry_of_freeNoReentry`), which follows from a sharper
statement, *no ancestor overtakes a face whose parent dart pivoted in*
(`freeNoReentry_of_noOvertake`); it also records the routes considered for a proof.

`NoReentry` holds on every plane map with at most two faces (`noReentry_of_card_face_le_two`:
there, the level of the face other than the root rises at a pivot, after which no dart can be
crossed forward into it, so two pivots never follow each other), for instance on the map of a
single edge (`noReentry_edge`): the hypothesis is satisfiable.

## The darts of the initial tree are not covered

`NoReentry` speaks only of darts that enter the tree **by a pivot**; its analogue for the darts of
the initial tree is false, so a proof must use the crossing at the pivot. Take the plane graph on
the vertices `0, …, 3` with the edges `03`, `12`, `13`, two edges `01` (`a`, `a'`) and two edges
`02` (`b`, `b'`), and the faces (boundary walks) `0 1 3` (through `a`), `1 0 2` (through `a` and
`b`), `1 2 0` (through `b'` and `a'`), `0 3 1` (through `a'`) and the face `o` between `b` and
`b'`; `s = 3`, `t = 2`, the root `o` (incident to `t`). Capacities: `4` on `0 → 2` (`b`),
`0 → 1` (`a'`) and `3 → 0`; `2` on `2 → 0` (`b'`) and `0 → 3`; `1` on `0 → 2` (`b'`), `1 → 2`,
`2 → 1` and `3 → 1`; `0` on the other darts. Flow `0`; tree: `0 1 3` hangs from `1 0 2` by
`1 → 0` (`a`), `1 0 2` from `o` by `2 → 0` (`b`), `0 3 1` from `0 1 3` by `1 → 3`, and `1 2 0`
from `0 3 1` by `1 → 0` (`a'`), all of capacity `0`. The run pivots three times with unique
bottlenecks (`0 → 2` (`b'`) into `1 2 0`, `1 → 2` into `1 0 2`, `3 → 0` into `0 3 1`), after
which the path of the cotree crosses `1 → 0` (`a'`), the initial parent dart of `1 2 0`, forward
(`chi = 1`). (Found by a computer search, like the evidence below; not used in the proofs.)

**Computer experiments** (exhaustive on small plane maps for every sequence of allowed pivots,
random on larger ones; not part of this development) support `NoReentry` and the following
sharper form, false again for the initial tree: if a face `b` changes its parent from a dart `e`
that entered by a pivot to a dart `e'`, then from then on `chi e ≤ chi e'` (by induction along the
parents of `b`, this gives `NoReentry`). They also show that, along a sequence of pivots chosen
freely among the darts crossed forward whose head face is not above their tail face, a face can be
the root of three pivots, so a bound of two pivots per face (which would also give `m + 1` steps)
does not hold in that generality.

## A stronger monotonicity is false

A dart that pivots out is crossed backward right after the pivot (`pivot_exit`: `chi d = -1`).
It is tempting to strengthen `NoReentry` to: along a run of pivots, no dart is crossed by the path
of the cotree backward and later forward. **This is false**, already from an initial state of the
algorithm (a circulation and a tree of tight darts rooted at a face incident to `t`). Take the
plane graph on the vertices `0, …, 4` with the edges `01, 02, 03, 04, 13, 14, 23` and the faces
(boundary walks) `1 4 0 2 3` (outer), `4 1 0` (the root `o`, the face of the dart `4 → 1`),
`0 1 3` and `0 3 2`; `s = 2`, `t = 4`. Capacities: `4` on `1 → 4`, `0 → 3`, `3 → 0`, `0 → 4`;
`3` on `0 → 1`, `2 → 0`; `2` on `1 → 0`, `1 → 3`, `3 → 1`, `2 → 3`, `3 → 2`; `1` on `0 → 2`; `0` on
`4 → 1`, `4 → 0`. Flow: one unit around `0 → 2 → 3 → 1 → 0` and one around `0 → 3 → 1 → 0`.
Tree: the outer face hangs from `o` by `4 → 1`, the face `0 1 3` from `o` by `1 → 0`, the face
`0 3 2` from the outer face by `0 → 2` (all saturated). The run: the path
`2 3 0 4` (residual capacities `1, 5, 4`), pivot `2 → 3`; the path `2 0 4` (`4, 3`), pivot
`0 → 4`; the path `2 0 3 1 4` (`1, 4, 0, 4`), pivot `3 → 1`; then the path `2 0 1 4`, whose
bottleneck `2 → 0` stops the run. The bottlenecks are unique, the first path crosses the edge
`03` as `3 → 0` and the third as `0 → 3`, and the steps `0, 1, 2` are pivots.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-! ### Trees -/

namespace DTree

/-- The parent darts of a tree. -/
noncomputable def parSet (T : DTree M) : Finset D :=
  (univ.filter fun x => x ≠ T.root).image T.par

lemma mem_parSet {T : DTree M} {d : D} : d ∈ T.parSet ↔ ∃ x, x ≠ T.root ∧ T.par x = d := by
  simp [parSet]

lemma inT_of_mem_parSet {T : DTree M} {d : D} (h : d ∈ T.parSet) : T.InT d := by
  obtain ⟨x, hx, rfl⟩ := mem_parSet.1 h
  exact T.inT_par hx

/-- The parent of a face other than the root is not below it. -/
lemma not_anc_up (T : DTree M) {b : F} (hb : b ≠ T.root) : ¬ T.Anc b (T.up b) := by
  rintro ⟨n, hn⟩
  have hp : Function.IsPeriodicPt T.up (n + 1) b := by
    show T.up^[n + 1] b = b
    rw [Function.iterate_succ_apply, hn]
  have h := (hp.mul_const (T.depth b)).eq
  rw [T.iterate_of_le (by nlinarith)] at h
  exact hb h.symm

end DTree

/-! ### The path of the cotree from the levels -/

/-- **The path of the cotree from the levels**: for any unit flow `P` from `s` to `t`,
`chi d = psum P (face d) + P d - psum P (face (rev d))`. -/
lemma chi_eq_psum (hM : M.IsPlane) {s t : V} (T : DTree M) {P : D → ℤ}
    (hPa : M.IsAntisymm P)
    (hPd : ∀ v, M.div P v = (if s = v then 1 else 0) - (if t = v then 1 else 0)) (d : D) :
    T.chi s t d = T.psum P (M.face d) + P d - T.psum P (M.face (M.rev d)) := by
  obtain ⟨hχa, hχdiv, hχoff, -⟩ := T.chi_spec hM s t
  have hcirc : M.IsCirc (P - T.chi s t) := ⟨fun d => by
    simp only [Pi.sub_apply, hPa d, hχa d]; ring, fun v => by
      rw [div_sub, hPd, hχdiv]; ring⟩
  obtain ⟨ψ, hψ⟩ := exists_int_potential hM hcirc
  have hP : ∀ d, P d = T.chi s t d + M.cob ψ d := fun d => by
    have := hψ d; simp only [Pi.sub_apply] at this; omega
  have hps : ∀ x, T.psum P x = ψ x - ψ T.root := fun x => by
    have : P = T.chi s t + M.cob ψ := funext hP
    rw [this, DTree.psum_add, T.psum_eq_zero (fun y hy => hχoff _ (T.inT_par hy)),
      DTree.psum_cob, zero_add]
  rw [hps, hps, hP d]; simp only [cob]; ring

/-! ### Pivots -/

variable {c : D → ℤ} {s t : V}

open Classical in
/-- **A pivot**: when a step does not stop, it gives the face `b = face (rev e)` the parent dart
`e`, crossed forward by the path of the cotree, from a face not below `b`. -/
lemma pivot_facts {st : St M} (h : (step M c s t st).2 = false) :
    ∃ e b, st.T.chi s t e = 1 ∧ M.face (M.rev e) = b ∧ b ≠ st.T.root ∧
      ¬ st.T.Anc b (M.face e) ∧ (step M c s t st).1.T.root = st.T.root ∧
      (∀ x, (step M c s t st).1.T.par x = if x = b then e else st.T.par x) ∧
      ∀ φ x, (step M c s t st).1.T.psum φ x = st.T.psum φ x +
        if st.T.Anc b x then st.T.psum φ (M.face e) + φ e - st.T.psum φ b else 0 := by
  classical
  have hne : (pathSet s t st.T).Nonempty := by
    by_contra hne
    unfold step at h
    simp [hne] at h
  unfold step at h ⊢
  simp only [hne, ↓reduceDIte] at h ⊢
  obtain ⟨hb, ha, hroot, hpar, hps⟩ := stepE_facts h
  exact ⟨_, _, bott_mem c s t st.g st.T hne, rfl, hb, ha, hroot, hpar, hps⟩

/-- **A pivot adds its dart to the tree**: the dart `e` of the pivot is a parent dart after the
pivot and not before, and every new parent dart is `e`. -/
lemma pivot_enter (hM : M.IsPlane) {st : St M} (h : (step M c s t st).2 = false) :
    ∃ e, st.T.chi s t e = 1 ∧ e ∉ st.T.parSet ∧ e ∈ (step M c s t st).1.T.parSet ∧
      ∀ d, d ∈ (step M c s t st).1.T.parSet → d ∉ st.T.parSet → d = e := by
  obtain ⟨e, b, he, -, hb, -, hroot, hpar, -⟩ := pivot_facts h
  obtain ⟨-, -, hoff, -⟩ := st.T.chi_spec hM s t
  refine ⟨e, he, fun hm => ?_, DTree.mem_parSet.2 ⟨b, hroot ▸ hb, by simp [hpar]⟩,
    fun d hd hn => ?_⟩
  · rw [hoff _ (DTree.inT_of_mem_parSet hm)] at he; exact absurd he (by norm_num)
  · obtain ⟨x, hx, rfl⟩ := DTree.mem_parSet.1 hd
    rw [hpar]
    split_ifs with hxb
    · rfl
    · rw [hpar] at hn
      simp only [hxb, ↓reduceIte] at hn
      exact absurd (DTree.mem_parSet.2 ⟨x, hroot ▸ hx, rfl⟩) hn

/-- **A dart that pivots out is crossed backward**: right after the pivot, the new path of the
cotree crosses the old parent dart of `b` backward. -/
lemma pivot_exit (hM : M.IsPlane) {st : St M} (h : (step M c s t st).2 = false) {d : D}
    (hd : d ∈ st.T.parSet) (hd' : d ∉ (step M c s t st).1.T.parSet) :
    (step M c s t st).1.T.chi s t d = -1 := by
  classical
  obtain ⟨e, b, he, -, hb, -, hroot, hpar, hpsum⟩ := pivot_facts h
  obtain ⟨hχa, hχdiv, hoff, -⟩ := st.T.chi_spec hM s t
  obtain ⟨x, hx, rfl⟩ := DTree.mem_parSet.1 hd
  have hxb : x = b := by
    by_contra hxb
    exact hd' (DTree.mem_parSet.2 ⟨x, hroot ▸ hx, by rw [hpar]; simp [hxb]⟩)
  subst hxb
  rw [chi_eq_psum hM _ hχa hχdiv, hpsum, hpsum, st.T.head_par x hx, ← st.T.up_of_ne hx]
  have h0 : ∀ y, st.T.psum (st.T.chi s t) y = 0 :=
    st.T.psum_eq_zero fun y hy => hoff _ (st.T.inT_par hy)
  simp only [h0, st.T.not_anc_up hx, st.T.anc_self, ↓reduceIte, he,
    hoff _ (st.T.inT_par hx)]
  norm_num

/-! ### Runs -/

variable (M c s t) in
/-- **The states of a run**: `traj st i` after `i` steps (the run itself stops earlier). -/
noncomputable def traj (st : St M) : ℕ → St M
  | 0 => st
  | i + 1 => (step M c s t (traj st i)).1

lemma traj_succ' (st : St M) (i : ℕ) :
    traj M c s t st (i + 1) = traj M c s t (step M c s t st).1 i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [traj, ih, traj]

lemma traj_inv (hM : M.IsPlane) {st : St M} (hI : Inv c s t st) (i : ℕ) :
    Inv c s t (traj M c s t st i) := by
  induction i with
  | zero => exact hI
  | succ i ih => exact step_inv hM ih

/-- **Every step of a run but the last is a pivot.** -/
lemma run_pivot : ∀ (n : ℕ) (st : St M) (i : ℕ), i + 1 < (run M c s t n st).2.1 →
    (step M c s t (traj M c s t st i)).2 = false
  | 0, st, i, h => by simp [run] at h
  | n + 1, st, i, h => by
    unfold run at h
    split_ifs at h with hd
    · simp at h
    · simp only at h
      rcases i with _ | i
      · simpa [traj] using hd
      · rw [traj_succ']
        exact run_pivot n _ i (by omega)

/-- **The remaining hypothesis**: along a run of pivots, a dart that pivots into the dual tree at
step `i` is never again crossed forward by the path of the cotree (each dart pivots into the tree
at most once: Borradaile and Klein; Erickson). -/
def NoReentry (M : CombMap D V F) : Prop :=
  ∀ (c : D → ℤ) (s t : V) (st : St M), Inv c s t st → ∀ i j (d : D), i < j →
    (∀ l ≤ j, (step M c s t (traj M c s t st l)).2 = false) →
    d ∉ (traj M c s t st i).T.parSet → d ∈ (traj M c s t st (i + 1)).T.parSet →
    (traj M c s t st j).T.chi s t d ≠ 1

/-- **Each dart enters the dual tree at most once** along a run of pivots: a dart that enters the
set of parent darts at step `i` does not enter it again at a later step `j`. This is exactly what
the count of the steps needs; it follows from `NoReentry` (`enterOnce_of_noReentry`). -/
def EnterOnce (M : CombMap D V F) : Prop :=
  ∀ (c : D → ℤ) (s t : V) (st : St M), Inv c s t st → ∀ i j (d : D), i < j →
    (∀ l ≤ j, (step M c s t (traj M c s t st l)).2 = false) →
    d ∉ (traj M c s t st i).T.parSet → d ∈ (traj M c s t st (i + 1)).T.parSet →
    d ∉ (traj M c s t st j).T.parSet → d ∉ (traj M c s t st (j + 1)).T.parSet

/-- **`NoReentry` implies `EnterOnce`**: a dart entering at a pivot is crossed forward by the path
of the cotree just before (`pivot_enter`). -/
theorem enterOnce_of_noReentry (hM : M.IsPlane) (hnr : NoReentry M) : EnterOnce M := by
  intro c s t st hI i j d hij hpiv h1 h2 h3 h4
  obtain ⟨e, he, -, -, hd⟩ := pivot_enter (c := c) hM (hpiv j le_rfl)
  rw [traj] at h4
  exact hnr c s t st hI i j d hij hpiv h1 h2 (hd d h4 h3 ▸ he)

/-- **Under `EnterOnce`, every run takes at most `m + 1` steps.** -/
theorem steps_le_of_enterOnce (hM : M.IsPlane) (heo : EnterOnce M) {st : St M}
    (hI : Inv c s t st) (n : ℕ) : (run M c s t n st).2.1 ≤ Fintype.card D + 1 := by
  generalize hk : (run M c s t n st).2.1 = k
  have hpiv : ∀ i, i + 1 < k → (step M c s t (traj M c s t st i)).2 = false := fun i hi =>
    run_pivot n st i (hk ▸ hi)
  generalize hT : (fun i => (traj M c s t st i).T.parSet) = T
  have hT' : ∀ i, T i = (traj M c s t st i).T.parSet := fun i => by rw [← hT]
  -- every pivot adds a dart
  have h1 : ∀ i, i + 1 < k → 1 ≤ (T (i + 1) \ T i).card := fun i hi => by
    obtain ⟨e, -, h1, h2, -⟩ := pivot_enter (c := c) hM (hpiv i hi)
    rw [Nat.one_le_iff_ne_zero, ne_eq, card_eq_zero, ← ne_eq, ← nonempty_iff_ne_empty]
    exact ⟨e, mem_sdiff.2 ⟨by rw [hT']; exact h2, by rw [hT']; exact h1⟩⟩
  -- every dart enters at most once
  have honce : ∀ d, (Pivot.entries T (k - 1) d).card ≤ 1 := by
    intro d
    rw [card_le_one]
    intro i hi i' hi'
    simp only [Pivot.entries, mem_filter, mem_range] at hi hi'
    by_contra hne
    wlog hlt : i < i' generalizing i i'
    · exact this i' i hi' hi (Ne.symm hne) (by omega)
    refine heo c s t st hI i i' d hlt (fun l hl => hpiv l (by omega)) ?_ ?_ ?_ ?_
    · rw [← hT']; exact hi.2.2
    · rw [← hT']; exact hi.2.1
    · rw [← hT']; exact hi'.2.2
    · rw [← hT']; exact hi'.2.1
  have hsum := Pivot.sum_card_sdiff_le honce
  have hge : k - 1 ≤ ∑ i ∈ range (k - 1), (T (i + 1) \ T i).card := by
    calc k - 1 = ∑ _i ∈ range (k - 1), 1 := by simp
      _ ≤ _ := sum_le_sum fun i hi => h1 i (by simp at hi; omega)
  omega

/-- **Under `NoReentry`, every run takes at most `m + 1` steps.** -/
theorem steps_le_of_noReentry (hM : M.IsPlane) (hnr : NoReentry M) {st : St M}
    (hI : Inv c s t st) (n : ℕ) : (run M c s t n st).2.1 ≤ Fintype.card D + 1 :=
  steps_le_of_enterOnce hM (enterOnce_of_noReentry hM hnr) hI n

lemma init_inv {o : F} {st : St M} (h : init M c s t o = some st) : Inv c s t st := by
  unfold init at h
  split_ifs at h with hex
  obtain rfl := Option.some.inj h
  exact hex.choose_spec.2.1

/-- **`PivotBound` from `EnterOnce`.** -/
theorem pivotBound_of_enterOnce (hM : M.IsPlane) (heo : EnterOnce M) : PivotBound M := by
  intro c X Y
  unfold stflowSteps coreRun
  split_ifs with h
  · cases hi : init M (capR M c X Y) h.1.choose (M.tail h.2.choose) (M.face h.2.choose) with
    | none => simp
    | some st =>
      simpa using steps_le_of_enterOnce hM heo (init_inv hi) _
  · exact Nat.zero_le _

/-- **`PivotBound` from `NoReentry`.** -/
theorem pivotBound_of_noReentry (hM : M.IsPlane) (hnr : NoReentry M) : PivotBound M :=
  pivotBound_of_enterOnce hM (enterOnce_of_noReentry hM hnr)

/-- **The cost is `O(n log n)` under `EnterOnce`**: at most `36 K m lg m` on a plane map with
`m ≥ 1` darts. -/
theorem stflowCost_le_of_enterOnce {cc : STCosts} {K : ℕ} (hc : cc.Bounds K) (hM : M.IsPlane)
    (hD : 1 ≤ Fintype.card D) (heo : EnterOnce M) (c : D → ℤ) (X Y : Finset V) :
    stflowCost M cc c X Y ≤ 36 * K * Fintype.card D * lg (Fintype.card D) :=
  stflowCost_le_of_pivotBound hc hM hD (pivotBound_of_enterOnce hM heo) c X Y

/-- **The cost is `O(n log n)` under `NoReentry`**: at most `36 K m lg m` on a plane map with
`m ≥ 1` darts. -/
theorem stflowCost_le_of_noReentry {cc : STCosts} {K : ℕ} (hc : cc.Bounds K) (hM : M.IsPlane)
    (hD : 1 ≤ Fintype.card D) (hnr : NoReentry M) (c : D → ℤ) (X Y : Finset V) :
    stflowCost M cc c X Y ≤ 36 * K * Fintype.card D * lg (Fintype.card D) :=
  stflowCost_le_of_enterOnce hc hM hD (enterOnce_of_noReentry hM hnr) c X Y

/-! ### Satisfiability -/

/-- In a type with at most two elements, two elements different from a third are equal. -/
lemma eq_of_card_le_two {α : Type*} [Fintype α] (h : Fintype.card α ≤ 2) {r x y : α}
    (hx : x ≠ r) (hy : y ≠ r) : x = y := by
  classical
  by_contra hxy
  have : ({r, x, y} : Finset α).card = 3 := by
    rw [card_insert_of_notMem (by simp [Ne.symm hx, Ne.symm hy]),
      card_pair hxy]
  have := card_le_univ ({r, x, y} : Finset α)
  omega

/-- **On a plane map with at most two faces, two pivots never follow each other**: the first
pivot gives the face `b` other than the root the parent dart `e` with `chi e = 1`, which raises
the level of `b` by one, so the path of the new cotree crosses no dart forward into `b`. Hence
`NoReentry` holds. -/
theorem noReentry_of_card_face_le_two (hM : M.IsPlane) (hF : Fintype.card F ≤ 2) :
    NoReentry M := by
  intro c s t st _ i j d hij hpiv _ _
  exfalso
  have h0 : (step M c s t st).2 = false := hpiv 0 (Nat.zero_le _)
  have h1 : (step M c s t (step M c s t st).1).2 = false := hpiv 1 (by omega)
  obtain ⟨e, b, he, -, hbr, hna, hroot, hpar, -⟩ := pivot_facts h0
  obtain ⟨e', b', he', hb', hbr', hna', -⟩ := pivot_facts h1
  generalize hT1 : (step M c s t st).1.T = T1 at hroot hpar he' hbr' hna'
  have hbr1 : b ≠ T1.root := by rw [hroot]; exact hbr
  -- the faces: the root, `b`, and nothing else
  have hbb : b' = b := eq_of_card_le_two hF hbr' hbr1
  subst hbb
  have hfe : M.face e = T1.root := by
    by_contra h
    exact hna (eq_of_card_le_two hF (hroot ▸ h) hbr ▸ st.T.anc_self _)
  have hfe' : M.face e' = T1.root := by
    by_contra h
    exact hna' (eq_of_card_le_two hF h hbr1 ▸ T1.anc_self _)
  -- the level of `b'` in the new tree, for the first path of the cotree
  obtain ⟨hχa, hχdiv, -, hχle⟩ := st.T.chi_spec hM s t
  have hps : T1.psum (st.T.chi s t) b' = 1 := by
    rw [T1.psum_of_ne _ hbr1, T1.up_of_ne hbr1, hpar]
    simp only [↓reduceIte, hfe, T1.psum_root, he, zero_add]
  have := chi_eq_psum hM T1 hχa hχdiv e'
  rw [hfe', T1.psum_root, hb', hps] at this
  have := hχle e'
  omega

/-- **`NoReentry` is satisfiable**: the map of a single edge (one face) is plane and meets it. -/
theorem noReentry_edge : (CombMap.ofRotation edgeRot).IsPlane ∧
    NoReentry (CombMap.ofRotation edgeRot) := by
  have hpl := CombMap.ofRotation_isPlane edgeRot_isPlane
  refine ⟨hpl, noReentry_of_card_face_le_two hpl (Fintype.card_le_one_iff_subsingleton.2 ?_ |>.trans
    (by norm_num))⟩
  refine ⟨fun y y' => ?_⟩
  suffices h : ∀ y, y = edgeRot.face ⟨(0, 1), by decide⟩ by rw [h y, h y']
  intro y
  obtain ⟨⟨⟨a, b⟩, hab⟩, rfl⟩ := edgeRot.face_surjective y
  refine edgeRot.face_eq_face_iff.2 ?_
  fin_cases a <;> fin_cases b
  · exact absurd hab (by decide)
  · exact Equiv.Perm.SameCycle.refl _ _
  · exact ⟨-1, rfl⟩
  · exact absurd hab (by decide)

end STFlow

end PlanarFlow
