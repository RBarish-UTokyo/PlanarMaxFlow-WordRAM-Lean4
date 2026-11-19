module

public import PlanarFlow.STFlow.LexCount

/-!
# The pivot bound and the cost of the perturbed algorithm

From `lenterOnce` (each dart enters the dual tree at most once along the perturbed run) the count
of `PlanarFlow/STFlow/PivotCount.lean` gives **at most `m + 1` steps** on `m` darts
(`lsteps_le`), hence for the perturbed implementation `pstflow` of SingleSourceSingleSinkMaxFlow:

* `lsteps_le_of`: the bound for every perturbation whose parent darts are tight in the cut of the
  cyclic cover (`TightLev`); `lsteps_le` for `lexEps`;
* `pstflowSteps_le`: at most `m + 1` steps, on every plane map with transitive rotations and
  faces and nonnegative capacities;
* `pstflowCost_le`: **its cost is at most `36 K m lg m`** (`O(n log n)`), with the costs of its
  subroutines bounded as in `STCosts.Bounds`; the cost counts the initial shortest-path tree, the
  bookkeeping, the two dynamic forests, and a constant number of dynamic-tree operations per step
  actually performed (`costOf`, as for the unperturbed algorithm).

The genericity is enforced as in Cabello, Chambers and Erickson (Section 6): the capacities are
compared lexicographically with the perturbation `ε d = (4 F + 5) ^ (index of d)`; the
second coordinate only breaks ties, so the flow computed is a maximum flow for the given
capacities (`pstflow_spec`).

**On the cost model.** `pstflowCost` charges, as for the unperturbed algorithm, a constant number
of dynamic-tree operations per step, each at the cost `cc.dt` assumed `O(log n)`. The values in
the trees are now pairs, and the second coordinates are integers of `O(m log F)` bits (this
deterministic choice is what the proof uses); charging one operation on such pairs as `O(log n)`
is an assumption of the model (`STCosts.Bounds`), not a consequence. Cabello, Chambers and Erickson
use perturbations of `O(log n)` bits chosen at random (unique shortest paths with high
probability), or a deterministic lexicographic scheme at an extra factor `O(log n)`. A machine
implementation of the perturbation may thus spend `O(m lg² m)`; the maximum-flow algorithm
budgets `K m lg² m` for this subroutine (`PlanarFlow.BKMNW.SubCosts.Bounds.stflow`), which
absorbs that factor without changing its bound `O(n log³ n)`.

**On the machine.** `PlanarFlow.STFlow.pstflow_exec` (`PlanarFlow/STFlow/ProgExec.lean`) runs
`pstflow` on the machine of `WordRAM`, whose real registers are exact at unit cost: one key per
dart, `N (c - g) + (ε - h)` (`PlanarFlow/STFlow/ProgKey.lean`, an integer of `O(m log m)` bits
for `lexEps`), on the evertable dynamic trees, within `O(m log m)` steps (`pst_steps_le_m`). The
program works for every perturbation with the properties `PertOK` (`pstflowE_exec`). The
maximum-flow algorithm uses instead the perturbation of polynomial size `isoEps`
(`PlanarFlow.STFlow.pstflowW`, `PlanarFlow/STFlow/IsoCost.lean`: the same pivot bound,
`lsteps_le_of` with `PlanarFlow.STFlow.tight_parW`), whose keys are integers of polynomial size
(`PlanarFlow.STFlow.isoKeys_bounded`, `PlanarFlow.STFlow.pstflowW_exec_exists`). The lemmas
`lenterOnce_of` and `lsteps_le_of` state the pivot bound for every perturbation whose parent
darts are tight in the cut of the cover (`TightLev`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {c ε : D → ℤ} {s t : V}

/-- **Every step of a perturbed run but the last is a pivot.** -/
lemma lrun_pivot : ∀ (n : ℕ) (st : LSt M) (i : ℕ), i + 1 < (lrun M c ε s t n st).2.1 →
    (lstep M c ε s t (ltraj M c ε s t st i)).2 = false
  | 0, st, i, h => by simp [lrun] at h
  | n + 1, st, i, h => by
    unfold lrun at h
    split_ifs at h with hd
    · simp at h
    · simp only at h
      rcases i with _ | i
      · simpa [ltraj] using hd
      · rw [ltraj_succ']
        exact lrun_pivot n _ i (by omega)

/-- **A pivot of the perturbed run adds its dart to the tree.** -/
lemma lpivot_enter (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M}
    (h : (lstep M c ε s t st).2 = false) :
    ∃ e, e ∉ st.T.parSet ∧ e ∈ (lstep M c ε s t st).1.T.parSet := by
  obtain ⟨e, he, hb, hroot, hpar, -⟩ := lpivot_facts hM hst h
  obtain ⟨-, -, hoff, -⟩ := st.T.chi_spec hM s t
  refine ⟨e, fun hm => ?_, DTree.mem_parSet.2 ⟨_, hroot ▸ hb, by simp [hpar]⟩⟩
  rw [hoff _ (DTree.inT_of_mem_parSet hm)] at he
  exact absurd he (by norm_num)

/-- **Every perturbed run takes at most `m + 1` steps**, for any perturbation whose parent darts are
tight in the cut of the cover (`TightLev`), on a plane map with transitive rotations
and faces, from a state satisfying `LInv` rooted at the face of a dart leaving `t`. -/
theorem lsteps_le_of (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (hc : ∀ d, 0 ≤ c d) (hst : s ≠ t)
    (hTL : ∀ (π : SPath M) (hk : 0 < π.k), π.p 0 = s → π.p π.k = t →
      ∃ ℓ, (∀ e, 0 ≤ ℓ e) ∧ TightLev c ε hrot π hk ℓ)
    {d₀ : D} (hd₀ : M.tail d₀ = t) {st : LSt M}
    (hI : LInv c ε s t st) (hroot : st.T.root = M.face d₀) (n : ℕ) :
    (lrun M c ε s t n st).2.1 ≤ Fintype.card D + 1 := by
  generalize hk : (lrun M c (ε) s t n st).2.1 = k
  have hpiv : ∀ i, i + 1 < k →
      (lstep M c (ε) s t (ltraj M c (ε) s t st i)).2 = false :=
    fun i hi => lrun_pivot n st i (hk ▸ hi)
  generalize hT : (fun i => (ltraj M c (ε) s t st i).T.parSet) = T
  have hT' : ∀ i, T i = (ltraj M c (ε) s t st i).T.parSet := fun i => by rw [← hT]
  have h1 : ∀ i, i + 1 < k → 1 ≤ (T (i + 1) \ T i).card := fun i hi => by
    obtain ⟨e, h1, h2⟩ := lpivot_enter hM hst (hpiv i hi)
    rw [Nat.one_le_iff_ne_zero, ne_eq, card_eq_zero, ← ne_eq, ← nonempty_iff_ne_empty]
    exact ⟨e, mem_sdiff.2 ⟨by rw [hT']; exact h2, by rw [hT']; exact h1⟩⟩
  have honce : ∀ d, (Pivot.entries T (k - 1) d).card ≤ 1 := by
    intro d
    rw [card_le_one]
    intro i hi i' hi'
    simp only [Pivot.entries, mem_filter, mem_range] at hi hi'
    by_contra hne
    wlog hlt : i < i' generalizing i i'
    · exact this i' i hi' hi (Ne.symm hne) (by omega)
    refine lenterOnce_of hM hrot hface hc hst hTL hd₀ hI hroot i i' d hlt
      (fun l hl => hpiv l (by omega)) ?_ ?_ ?_ ?_
    · rw [← hT']; exact hi.2.2
    · rw [← hT']; exact hi.2.1
    · rw [← hT']; exact hi'.2.2
    · rw [← hT']; exact hi'.2.1
  have hsum := Pivot.sum_card_sdiff_le honce
  have hge : k - 1 ≤ ∑ i ∈ range (k - 1), (T (i + 1) \ T i).card := by
    calc k - 1 = ∑ _i ∈ range (k - 1), 1 := by simp
      _ ≤ _ := sum_le_sum fun i hi => h1 i (by simp at hi; omega)
  omega

/-- **Every perturbed run takes at most `m + 1` steps**, on a plane map with transitive rotations
and faces, from a state satisfying `LInv` rooted at the face of a dart leaving `t`. -/
theorem lsteps_le (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (hc : ∀ d, 0 ≤ c d) (hst : s ≠ t) {d₀ : D} (hd₀ : M.tail d₀ = t) {st : LSt M}
    (hI : LInv c (lexEps D F) s t st) (hroot : st.T.root = M.face d₀) (n : ℕ) :
    (lrun M c (lexEps D F) s t n st).2.1 ≤ Fintype.card D + 1 :=
  lsteps_le_of hM hrot hface hc hst (fun π hk _ _ => ⟨_, fun e => covLen_nonneg _ hc
    (fun d => lexEps_nonneg d) e, tightLev_lex hrot π hk hM hface hc⟩) hd₀ hI hroot n

/-! ### The perturbed implementation -/

variable (M) in
open Classical in
/-- **The number of steps** (augmentations) performed by `pstflow M c X Y`. -/
noncomputable def pstflowSteps (c : D → ℤ) (X Y : Finset V) : ℕ :=
  if h : X.Nonempty ∧ ∃ d, M.tail d ∈ Y then
    ((pcoreRun M (capR M c X Y) h.1.choose (M.tail h.2.choose) (M.face h.2.choose)).map
      fun r => r.2.1).getD 0
  else 0

variable (M) in
/-- **The cost** of `pstflow M c X Y`: as for the unperturbed algorithm (`costOf`), for the
number of steps performed (the perturbation adds a second coordinate to the values in the dynamic
trees, a constant factor). -/
noncomputable def pstflowCost (cc : STCosts) (c : D → ℤ) (X Y : Finset V) : ℕ :=
  costOf D V F cc (pstflowSteps M c X Y)

/-- **The perturbed implementation takes at most `m + 1` steps** on every plane map with
transitive rotations and faces, for nonnegative capacities. -/
theorem pstflowSteps_le (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) (X Y : Finset V) :
    pstflowSteps M c X Y ≤ Fintype.card D + 1 := by
  classical
  unfold pstflowSteps pcoreRun
  split_ifs with h
  · set t := M.tail h.2.choose
    cases hi : linit M (capR M c X Y) (lexEps D F) h.1.choose t (M.face h.2.choose) with
    | none => simp
    | some st =>
      simp only [Option.map_some, Option.getD_some]
      obtain ⟨hroot, hI⟩ := linit_inv _ _ hi
      by_cases hst : h.1.choose = t
      · -- the source is the sink: the path of the cotree is empty, the run stops at once
        have hz : ∀ d, st.T.chi h.1.choose t d = 0 := by
          obtain ⟨ha, hdiv, hoff, -⟩ := st.T.chi_spec hM h.1.choose t
          refine st.T.circ_eq_zero hM ⟨ha, fun v => ?_⟩ hoff
          rw [hdiv]; simp [hst]
        have hne : ¬ (pathSet h.1.choose t st.T).Nonempty := by
          rintro ⟨d, hd⟩; simp [pathSet, hz d] at hd
        have h1 : (lstep M (capR M c X Y) (lexEps D F) h.1.choose t st).2 = true := by
          simp [lstep, hne]
        cases fuel F with
        | zero => simp [lrun]
        | succ n => simp [lrun, h1]
      · exact lsteps_le hM hrot hface (capR_nonneg hc X Y) hst rfl hI hroot _
  · exact Nat.zero_le _

/-- **The cost of the perturbed implementation is `O(n log n)`**: at most `36 K m lg m` on every
plane map with transitive rotations and faces with `m ≥ 1` darts, for nonnegative capacities.
No hypothesis on the pivots remains. -/
theorem pstflowCost_le {cc : STCosts} {K : ℕ} (hcc : cc.Bounds K) (hM : M.IsPlane)
    (hrot : M.RotTrans) (hface : M.FaceTrans) (hD : 1 ≤ Fintype.card D) {c : D → ℤ}
    (hc : ∀ d, 0 ≤ c d) (X Y : Finset V) :
    pstflowCost M cc c X Y ≤ 36 * K * Fintype.card D * lg (Fintype.card D) :=
  costOf_le_of_le hcc hM hD (pstflowSteps_le hM hrot hface hc X Y)

/-- **The perturbed single-source single-sink algorithm on a plane map with transitive rotations
and faces**: it meets `STFlowSpec`, and its cost is at most `36 K m lg m`. -/
theorem pstflow_plane (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {cc : STCosts}
    {K : ℕ} (hcc : cc.Bounds K) (hD : 1 ≤ Fintype.card D) :
    STFlowSpec M (pstflow M) ∧ ∀ c : D → ℤ, (∀ d, 0 ≤ c d) → ∀ X Y : Finset V,
      pstflowCost M cc c X Y ≤ 36 * K * Fintype.card D * lg (Fintype.card D) :=
  ⟨pstflow_spec hM, fun _ hc X Y => pstflowCost_le hcc hM hrot hface hD hc X Y⟩

/-- **The same for the maps of plane rotation systems** (which have transitive rotations and
faces): the hypotheses of `pstflow_plane` are met by every plane rotation system. -/
theorem pstflow_ofRotation {W : Type*} [Fintype W] [DecidableEq W] {Γ : SimpleGraph W}
    [DecidableRel Γ.Adj] {R : Kasteleyn.RotationSystem Γ} (hR : R.IsPlane) {cc : STCosts}
    {K : ℕ} (hcc : cc.Bounds K) (hD : 1 ≤ Fintype.card Γ.Dart) :
    STFlowSpec (CombMap.ofRotation R) (pstflow (CombMap.ofRotation R)) ∧
      ∀ c : Γ.Dart → ℤ, (∀ d, 0 ≤ c d) → ∀ X Y : Finset W,
        pstflowCost (CombMap.ofRotation R) cc c X Y ≤
          36 * K * Fintype.card Γ.Dart * lg (Fintype.card Γ.Dart) :=
  pstflow_plane (CombMap.ofRotation_isPlane hR) (MSSP.ofRotation_rotTrans R)
    (ofRotation_faceTrans R) hcc hD

end STFlow

end PlanarFlow
