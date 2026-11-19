module

public import PlanarFlow.STFlow.Init
public import PlanarFlow.BKMNW.CycleSink

/-!
# Single-source single-sink maximum flow: the implementation meets `STFlowSpec`

The maximum-flow algorithm of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen calls
SingleSourceSingleSinkMaxFlow with the source and the sink the vertex sets `X`, `Y` of two
disjoint simple paths, each contracted into one vertex (`PlanarFlow.BKMNW.STFlowSpec`).

**Contraction.** Contracting the edges of a simple path keeps a plane map plane; here it is done
without building a new map, by capacities: every dart with both ends in `X`, or both ends in `Y`,
gets the capacity `H = 1 + Σ c` (more than any cut separating `X` from `Y`), and the darts leaving
`Y` otherwise get the capacity `0`, so that no flow leaves the sink (`capR`). A maximum flow from
one vertex `s ∈ X` to one vertex `t ∈ Y` then has a minimum cut of capacity `< H`, which cannot cut
a dart of the two paths: it contains all of `X` and none of `Y`. Setting the flow to `0` on the
darts inside `X` and inside `Y` (`restrictR`) gives the output `STOut`: a pseudoflow conserved off
`X ∪ Y`, no vertex of `Y` sending flow out, and a closed set containing `X` and no vertex of `Y`.

**The algorithm** (`coreFlow`): the initial shortest-path tree of the dual (`init`), rooted at
the face `o` of a dart leaving `t`, and the run of augmentations and pivots (`run`), with `2 F² + 1`
steps allowed (it stops before, `run_done`).

* `coreFlow_spec`: on a plane map with nonnegative capacities and `s ≠ t`, `coreFlow` is a
  pseudoflow conserved off `s` and `t` with no residual path from `s` to `t`.
* `stflow_spec`: **the implementation `stflow M` meets `STFlowSpec M` on every plane map `M`.**
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-- The number of steps allowed: `2 F² + 1`. -/
def fuel (F : Type*) [Fintype F] : ℕ := 2 * Fintype.card F * Fintype.card F + 1

variable (M) in
/-- **The single-source single-sink algorithm**: the run from the initial shortest-path tree of
the dual rooted at `o`. -/
noncomputable def coreRun (c : D → ℤ) (s t : V) (o : F) : Option (St M × ℕ × Bool) :=
  (init M c s t o).map (run M c s t (fuel F))

variable (M) in
/-- The flow computed by `coreRun`. -/
noncomputable def coreFlow (c : D → ℤ) (s t : V) (o : F) : D → ℤ :=
  match coreRun M c s t o with
  | some r => r.1.g
  | none => 0

/-- **Correctness of the single-source single-sink algorithm.** -/
theorem coreFlow_spec (hM : M.IsPlane) [Nonempty D] {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) {s t : V}
    (hst : s ≠ t) (o : F) :
    IsPseudo M c (coreFlow M c s t o) ∧
      (∀ v, v ≠ s → v ≠ t → M.div (coreFlow M c s t o) v = 0) ∧
      NoPath M c (coreFlow M c s t o) {s} {t} := by
  obtain ⟨st, hst0, -, hI, -⟩ := init_spec hM hc s t o
  obtain ⟨h1, h2, -, h4⟩ := st.T.chi_spec hM s t
  have hP : IsUnit (M := M) (s := s) (t := t) (st.T.chi s t) := ⟨h1, h2, h4⟩
  have := run_spec hM hst hP hI (n := fuel F) (by unfold fuel; omega)
  simpa [coreFlow, coreRun, hst0] using this

/-! ### The contraction by capacities -/

/-- A dart with both ends in `X` or both ends in `Y`. -/
def Inside (M : CombMap D V F) (X Y : Finset V) (d : D) : Prop :=
  (M.tail d ∈ X ∧ M.head d ∈ X) ∨ (M.tail d ∈ Y ∧ M.head d ∈ Y)

instance (X Y : Finset V) (d : D) : Decidable (Inside M X Y d) := by
  unfold Inside; infer_instance

lemma inside_rev {X Y : Finset V} {d : D} : Inside M X Y (M.rev d) ↔ Inside M X Y d := by
  simp only [Inside, CombMap.tail_rev, CombMap.head_rev]; tauto

variable (M) in
/-- The capacities of the contraction: `H = 1 + Σ c` inside `X` and inside `Y`, `0` on the other
darts leaving `Y`. -/
def capR (c : D → ℤ) (X Y : Finset V) (d : D) : ℤ :=
  if Inside M X Y d then ∑ e, c e + 1 else if M.tail d ∈ Y then 0 else c d

variable (M) in
/-- The flow set to `0` inside `X` and inside `Y`. -/
def restrictR (X Y : Finset V) (g : D → ℤ) (d : D) : ℤ := if Inside M X Y d then 0 else g d

variable (M) in
open Classical in
/-- **SingleSourceSingleSinkMaxFlow**, from the vertex set `X` to the vertex set `Y`: a vertex
`s ∈ X`, a dart leaving a vertex `t ∈ Y` (whose face is the root of the dual tree), the algorithm
on the contracted capacities, and the flow restricted. -/
noncomputable def stflow (c : D → ℤ) (X Y : Finset V) : D → ℤ :=
  if h : X.Nonempty ∧ ∃ d, M.tail d ∈ Y then
    restrictR M X Y (coreFlow M (capR M c X Y) h.1.choose (M.tail h.2.choose) (M.face h.2.choose))
  else 0

lemma capR_nonneg {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) (X Y : Finset V) (d : D) :
    0 ≤ capR M c X Y d := by
  have : 0 ≤ ∑ e, c e := sum_nonneg fun e _ => hc e
  unfold capR; split_ifs <;> first | omega | exact hc d

/-- The net outflow of a set containing `s` and not `t`, for a flow conserved off `s` and `t`. -/
lemma sum_div_of_cons {g : D → ℤ} {s t : V} (hcons : ∀ v, v ≠ s → v ≠ t → M.div g v = 0)
    {U : Finset V} (hs : s ∈ U) (ht : t ∉ U) : ∑ v ∈ U, M.div g v = M.div g s := by
  rw [← sum_erase_add _ _ hs, sum_eq_zero fun v hv => hcons v (ne_of_mem_erase hv)
    (fun h => ht (h ▸ mem_of_mem_erase hv)), zero_add]

/-- Along a simple path, two vertices joined by a dart of capacity `H` are on the same side of a
closed set of capacity `< H`: all the vertices of the path are on the side of any one of them. -/
lemma path_side {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {W : Finset V} {H : ℤ} (hW : cutCap M u W < H)
    (P : SPath M) (hP : ∀ j < P.k, u (P.d j) = H ∧ u (M.rev (P.d j)) = H) {v w : V}
    (hv : v ∈ P.verts) (hw : w ∈ P.verts) (hvW : v ∈ W) : w ∈ W := by
  have hle : ∀ d, M.tail d ∈ W → M.head d ∉ W → u d ≤ cutCap M u W := fun d h1 h2 =>
    single_le_sum (f := u) (fun e _ => hu e) (by simp [h1, h2])
  have hstep : ∀ j < P.k, (P.p j ∈ W ↔ P.p (j + 1) ∈ W) := by
    intro j hj
    constructor
    · intro h; by_contra h'
      have := hle (P.d j) (by rw [P.tail_d j hj]; exact h) (by rw [P.head_d j hj]; exact h')
      have := (hP j hj).1; omega
    · intro h; by_contra h'
      have := hle (M.rev (P.d j)) (by rw [M.tail_rev, P.head_d j hj]; exact h)
        (by rw [M.head_rev, P.tail_d j hj]; exact h')
      have := (hP j hj).2; omega
  have hall : ∀ j ≤ P.k, (P.p j ∈ W ↔ P.p 0 ∈ W) := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih => rw [← hstep j (by omega), ih (by omega)]
  obtain ⟨i, hi, rfl⟩ := P.mem_init.1 hv
  obtain ⟨j, hj, rfl⟩ := P.mem_init.1 hw
  exact (hall j hj).2 ((hall i hi).1 hvW)

/-- **The contraction**: from a flow from `s ∈ X` to `t ∈ Y` with the capacities `capR`, the
restricted flow meets `STOut`. -/
theorem stOut_restrictR {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) (πs πt : SPath M)
    (hXY : Disjoint πs.verts πt.verts) {s t : V} (hs : s ∈ πs.verts) (ht : t ∈ πt.verts)
    {g : D → ℤ} (hg : IsPseudo M (capR M c πs.verts πt.verts) g)
    (hcons : ∀ v, v ≠ s → v ≠ t → M.div g v = 0)
    (hcut : NoPath M (capR M c πs.verts πt.verts) g {s} {t}) :
    STOut M c πs.verts πt.verts (restrictR M πs.verts πt.verts g) := by
  generalize hX : πs.verts = X at *
  generalize hY : πt.verts = Y at *
  have hst : s ≠ t := fun h => disjoint_left.1 hXY hs (h ▸ ht)
  have hcR := capR_nonneg (M := M) hc X Y
  have hsumc : 0 ≤ ∑ e, c e := sum_nonneg fun e _ => hc e
  have hnotX : ∀ v ∈ Y, v ∉ X := fun v hv h => disjoint_left.1 hXY h hv
  -- the capacity of `X`
  have hcapX : cutCap M (capR M c X Y) X ≤ ∑ e, c e := by
    unfold cutCap
    calc ∑ d with M.tail d ∈ X ∧ M.head d ∉ X, capR M c X Y d
        = ∑ d with M.tail d ∈ X ∧ M.head d ∉ X, c d := sum_congr rfl fun d hd => by
          simp only [mem_filter, mem_univ, true_and] at hd
          have h1 : ¬ Inside M X Y d := by
            rintro (h | h)
            · exact hd.2 h.2
            · exact hnotX _ h.1 hd.1
          have h2 : M.tail d ∉ Y := fun h => hnotX _ h hd.1
          simp [capR, h1, h2]
      _ ≤ ∑ e, c e := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun e _ _ => hc e
  obtain ⟨W, hsW, hWt, hW⟩ := hcut
  have hsW' : s ∈ W := hsW (mem_singleton_self s)
  have htW : t ∉ W := fun h => disjoint_left.1 hWt h (mem_singleton_self t)
  have hcapW : cutCap M (capR M c X Y) W < ∑ e, c e + 1 := by
    rw [← (tight_iff_closed hg W).2 hW, sum_div_of_cons hcons hsW' htW,
      ← sum_div_of_cons hcons hs (hnotX t ht)]
    have := sum_div_le_cutCap hg X
    omega
  have hin : ∀ (P : SPath M), (P.verts = X ∨ P.verts = Y) → ∀ j < P.k,
      capR M c X Y (P.d j) = ∑ e, c e + 1 ∧ capR M c X Y (M.rev (P.d j)) = ∑ e, c e + 1 := by
    intro P hP j hj
    have hm1 : M.tail (P.d j) ∈ P.verts := by rw [P.tail_d j hj]; exact P.p_mem_init hj.le
    have hm2 : M.head (P.d j) ∈ P.verts := by rw [P.head_d j hj]; exact P.p_mem_init hj
    have hI : Inside M X Y (P.d j) := by
      rcases hP with h | h <;> rw [h] at hm1 hm2
      · exact Or.inl ⟨hm1, hm2⟩
      · exact Or.inr ⟨hm1, hm2⟩
    have hI' : Inside M X Y (M.rev (P.d j)) := inside_rev.2 hI
    simp [capR, hI, hI']
  have hXW : X ⊆ W := fun x hx => by
    subst hX
    exact path_side hcR hcapW πs (hin πs (Or.inl rfl)) hs hx hsW'
  have hYW : ∀ y ∈ Y, y ∉ W := fun y hy hyW => by
    subst hY
    exact htW (path_side hcR hcapW πt (hin πt (Or.inr rfl)) hy ht hyW)
  refine ⟨⟨fun d => ?_, fun d => ?_⟩, fun v hvX hvY => ?_, fun v hv => ?_, ⟨W, hXW, ?_, ?_⟩⟩
  · simp only [restrictR, inside_rev, hg.antisymm d]; split_ifs <;> simp
  · have hle := hg.le_cap d
    have := hc d
    unfold restrictR; unfold capR at hle
    split_ifs at hle ⊢ <;> omega
  · -- conservation off `X ∪ Y`
    have hsv : v ≠ s := fun h => hvX (h ▸ hs)
    have htv : v ≠ t := fun h => hvY (h ▸ ht)
    rw [← hcons v hsv htv]
    refine sum_congr rfl fun d hd => ?_
    simp only [mem_filter, mem_univ, true_and] at hd
    have : ¬ Inside M X Y d := by
      rintro (h | h)
      · exact hvX (hd ▸ h.1)
      · exact hvY (hd ▸ h.1)
    simp [restrictR, this]
  · -- no vertex of `Y` sends flow out
    refine sum_nonpos fun d hd => ?_
    simp only [mem_filter, mem_univ, true_and] at hd
    unfold restrictR
    split_ifs with hI
    · exact le_rfl
    · have := hg.le_cap d
      have h1 : M.tail d ∈ Y := hd ▸ hv
      simp only [capR, hI, h1, ite_false, ite_true] at this
      exact this
  · rw [disjoint_left]; exact fun w hw hwY => hYW w hwY hw
  · intro d hd1 hd2
    have h1 : ¬ Inside M X Y d := by
      rintro (h | h)
      · exact hd2 (hXW h.2)
      · exact hYW _ h.1 hd1
    have h2 : M.tail d ∉ Y := fun h => hYW _ h hd1
    have := hW d hd1 hd2
    simp only [restrictR, h1, ite_false]
    simpa [capR, h1, h2] using this

/-- On a connected map, a vertex `t` with another vertex `s ≠ t` has a dart leaving it. -/
lemma exists_dart_tail (hM : M.IsPlane) {s t : V} (hst : s ≠ t) : ∃ d, M.tail d = t := by
  rcases Relation.ReflTransGen.cases_head (hM.conn t s) with h | ⟨w, ⟨d, h1, -⟩, -⟩
  · exact absurd h.symm hst
  · exact ⟨d, h1⟩

/-- **The implementation meets `STFlowSpec`** on every plane map. -/
theorem stflow_spec (hM : M.IsPlane) : STFlowSpec M (stflow M) := by
  classical
  intro c πs πt hc hXY
  have hXne : πs.verts.Nonempty := ⟨_, πs.p_mem_init (Nat.zero_le _)⟩
  have hY : (πt.p 0) ∈ πt.verts := πt.p_mem_init (Nat.zero_le _)
  have hne : πs.p 0 ≠ πt.p 0 := fun h => disjoint_left.1 hXY (πs.p_mem_init (Nat.zero_le _))
    (h ▸ hY)
  obtain ⟨d₀, hd₀⟩ := exists_dart_tail hM hne
  have hex : πs.verts.Nonempty ∧ ∃ d, M.tail d ∈ πt.verts := ⟨hXne, d₀, hd₀ ▸ hY⟩
  have : Nonempty D := ⟨d₀⟩
  unfold stflow
  simp only [hex, and_self, ↓reduceDIte]
  have hs := hex.1.choose_spec
  have ht := hex.2.choose_spec
  have hst : hex.1.choose ≠ M.tail hex.2.choose := fun h => disjoint_left.1 hXY hs (h ▸ ht)
  obtain ⟨h1, h2, h3⟩ := coreFlow_spec hM (capR_nonneg (M := M) hc πs.verts πt.verts) hst
    (M.face hex.2.choose)
  exact stOut_restrictR hc πs πt hXY hs ht h1 h2 h3

end STFlow

end PlanarFlow
