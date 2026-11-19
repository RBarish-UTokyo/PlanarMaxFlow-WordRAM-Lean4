module

public import PlanarFlow.BKMNW.TwoGroupsProg

/-!
# Connected components of a graph in CSR form on the machine (breadth-first search)

A generic labelling program: the graph on the nodes `0, …, N-1` is given in compressed sparse
row form, `OFF[u] = nmem (OFFb + u)` (`u ≤ N`, nondecreasing) and the neighbours of `u` are
`ADJ[i] = nmem (ADJb + i)` for `OFF[u] ≤ i < OFF[u+1]` (relation `bfAdj`, assumed symmetric).
The program labels every node with the number of its component: `LAB[u] = nmem (LABb + u)`
(initially zero), using a queue `Q[j] = nmem (Qb + j)`; one scan over the nodes, a
breadth-first search from every unlabelled node. Cost `O(N + E)`.

Registers: `4400 = N`, `4401 = OFFb`, `4402 = ADJb`, `4403 = LABb`, `4404 = Qb`; written:
constants `4405 = 1`, `4406 = 0`; `4407 = s` (scan), `4408 = L` (labels used), `4409 = h`,
`4410 = t` (queue head/tail), `4411 = i`, `4412` (end of the neighbour interval), `4413 = u`
(the popped node), `4414` (a label read), `4415 = v` (a node pushed), `4416` (an address).

* pure: `bfAdj`, `bfDeg`, `bfSum`, the invariant `BfCore` and its steps (`bfCore_push`,
  `bfCore_lab_of_marked`, `bfCore_pop`, `bfCore_close`, `bfCore_new`, `bfCore_final`),
  `bfSum_le` (the scanned degrees are at most `E`);
* programs `bfPush`, `bfEdge`, `bfPop`, `bfNew`, `bfOuter`, **`bfProg`**;
* **`bfProg_exec`**: within `27 N + 14 E + 8` steps (`E = OFF[N] - OFF[0]`), for all `u v < N`,
  `LAB[u] = LAB[v] ↔ ReflTransGen (bfAdj …) u v`, `0 < LAB[u] ≤ N`; memory outside the label and
  queue arrays, registers outside `4405 … 4416`, reals and output kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine

/-! ### The pure part -/

/-- The adjacency of the CSR graph: `v` is listed among the neighbours of `u < N`. -/
def bfAdj (m : ℕ → ℕ) (N OFFb ADJb u v : ℕ) : Prop :=
  u < N ∧ ∃ i, m (OFFb + u) ≤ i ∧ i < m (OFFb + u + 1) ∧ m (ADJb + i) = v

/-- The degree of `u`. -/
def bfDeg (m : ℕ → ℕ) (OFFb u : ℕ) : ℕ := m (OFFb + u + 1) - m (OFFb + u)

/-- The degrees of the first `h` queue entries. -/
def bfSum (m₀ m : ℕ → ℕ) (OFFb Qb h : ℕ) : ℕ := ∑ j ∈ range h, bfDeg m₀ OFFb (m (Qb + j))

/-- The state of the search: queue `Q[0 … t)` of distinct nodes, the marked nodes are those of
the queue, labels at most `L`, equal labels only in a component, the neighbours of the first
`hc` queue entries labelled like them, the entries from `h` on labelled `L`, memory outside the
two arrays unchanged. -/
structure BfCore (m₀ m : ℕ → ℕ) (N OFFb ADJb LABb Qb L hc h t : ℕ) : Prop where
  ht : h ≤ t
  tN : t ≤ N
  qlt : ∀ j < t, m (Qb + j) < N
  qnd : ∀ i < t, ∀ j < t, m (Qb + i) = m (Qb + j) → i = j
  mark : ∀ u < N, (0 < m (LABb + u) ↔ ∃ j < t, m (Qb + j) = u)
  labL : ∀ u < N, m (LABb + u) ≤ L
  reach : ∀ u < N, ∀ v < N, 0 < m (LABb + u) → m (LABb + u) = m (LABb + v) →
    ReflTransGen (bfAdj m₀ N OFFb ADJb) u v
  clos : ∀ j < hc, ∀ v, bfAdj m₀ N OFFb ADJb (m (Qb + j)) v →
    0 < m (LABb + v) ∧ m (LABb + v) = m (LABb + m (Qb + j))
  cur : ∀ j, h ≤ j → j < t → m (LABb + m (Qb + j)) = L
  frame : ∀ a, ¬ (LABb ≤ a ∧ a < LABb + N) → ¬ (Qb ≤ a ∧ a < Qb + N) → m a = m₀ a

section Pure

variable {m₀ m : ℕ → ℕ} {N OFFb ADJb LABb Qb L hc h t : ℕ}

lemma bfAdj_lt {u v : ℕ} (hval : ∀ u < N, ∀ i, m₀ (OFFb + u) ≤ i → i < m₀ (OFFb + u + 1) →
    m₀ (ADJb + i) < N) (h : bfAdj m₀ N OFFb ADJb u v) : v < N := by
  obtain ⟨hu, i, h1, h2, rfl⟩ := h
  exact hval u hu i h1 h2

lemma rtg_symm_of_symm {r : ℕ → ℕ → Prop} (hs : ∀ u v, r u v → r v u) {u v : ℕ}
    (h : ReflTransGen r u v) : ReflTransGen r v u := by
  induction h with
  | refl => exact .refl
  | tail _ h2 ih => exact ReflTransGen.head (hs _ _ h2) ih

/-- `t` distinct nodes `< N` none equal to `v < N`: `t < N`. -/
lemma bf_t_lt {f : ℕ → ℕ} {t v : ℕ} (hlt : ∀ j < t, f j < N)
    (hnd : ∀ i < t, ∀ j < t, f i = f j → i = j) (hv : v < N) (hne : ∀ j < t, f j ≠ v) :
    t < N := by
  have hsub : (range t).image f ⊆ (range N).erase v := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hx
    rw [mem_range] at hj
    exact mem_erase.2 ⟨hne j hj, mem_range.2 (hlt j hj)⟩
  have hc := card_le_card hsub
  rw [card_image_of_injOn (fun i hi j hj h => hnd i (mem_range.1 hi) j (mem_range.1 hj) h),
    card_range, card_erase_of_mem (mem_range.2 hv), card_range] at hc
  omega

/-- The sum of the degrees over all nodes. -/
lemma bf_sum_deg (m₀ : ℕ → ℕ) (OFFb : ℕ) (hmono : ∀ u < N, m₀ (OFFb + u) ≤ m₀ (OFFb + u + 1)) :
    ∑ u ∈ range N, bfDeg m₀ OFFb u = m₀ (OFFb + N) - m₀ (OFFb + 0) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih (fun u hu => hmono u (by omega))]
    have h1 := hmono n (by omega)
    have h2 : m₀ (OFFb + 0) ≤ m₀ (OFFb + n) := by
      clear ih h1
      induction n with
      | zero => exact le_refl _
      | succ k ihk =>
        exact le_trans (ihk (fun u hu => hmono u (by omega))) (hmono k (by omega))
    unfold bfDeg
    rw [show OFFb + (n + 1) = OFFb + n + 1 by omega]
    omega

/-- The degrees of distinct queue entries sum to at most `E`. -/
lemma bfSum_le (hmono : ∀ u < N, m₀ (OFFb + u) ≤ m₀ (OFFb + u + 1)) {h : ℕ}
    (hlt : ∀ j < h, m (Qb + j) < N) (hnd : ∀ i < h, ∀ j < h, m (Qb + i) = m (Qb + j) → i = j) :
    bfSum m₀ m OFFb Qb h ≤ m₀ (OFFb + N) - m₀ (OFFb + 0) := by
  rw [← bf_sum_deg m₀ OFFb hmono]
  unfold bfSum
  rw [← sum_image (f := fun u => bfDeg m₀ OFFb u) (g := fun j => m (Qb + j))
    (fun i hi j hj h => hnd i (mem_range.1 hi) j (mem_range.1 hj) h)]
  apply sum_le_sum_of_subset
  intro x hx
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hx
  exact mem_range.2 (hlt j (mem_range.1 hj))

lemma bfSum_congr {m₀ m m' : ℕ → ℕ} {OFFb Qb h : ℕ} (hq : ∀ j < h, m' (Qb + j) = m (Qb + j)) :
    bfSum m₀ m' OFFb Qb h = bfSum m₀ m OFFb Qb h := by
  unfold bfSum
  exact sum_congr rfl fun j hj => by rw [hq j (mem_range.1 hj)]

lemma bfSum_succ {m₀ m : ℕ → ℕ} {OFFb Qb h : ℕ} :
    bfSum m₀ m OFFb Qb (h + 1) = bfSum m₀ m OFFb Qb h + bfDeg m₀ OFFb (m (Qb + h)) := by
  unfold bfSum; rw [sum_range_succ]

/-- The memory after a push of `v` with the label `L` at the queue position `t`. -/
def bfW (m : ℕ → ℕ) (LABb Qb L t v : ℕ) : ℕ → ℕ :=
  upd (upd m (LABb + v) L) (Qb + t) v

/-- **A push**: an unmarked node `v < N` reachable from every node labelled `L`, labelled `L`
and appended to the queue. -/
lemma bfCore_push (hs : ∀ u v, bfAdj m₀ N OFFb ADJb u v → bfAdj m₀ N OFFb ADJb v u)
    (hval : ∀ u v, bfAdj m₀ N OFFb ADJb u v → v < N)
    (hL : BfCore m₀ m N OFFb ADJb LABb Qb L hc h t) (hlay : LABb + N ≤ Qb) (hcl : hc ≤ t)
    {v : ℕ} (hv : v < N) (h0 : m (LABb + v) = 0) (hL0 : 0 < L)
    (hR : ∀ w < N, 0 < m (LABb + w) → m (LABb + w) = L →
      ReflTransGen (bfAdj m₀ N OFFb ADJb) w v) :
    t < N ∧ BfCore m₀ (bfW m LABb Qb L t v) N OFFb ADJb LABb Qb L hc h (t + 1) := by
  obtain ⟨ht, tN, qlt, qnd, mark, labL, reach, clos, cur, frame⟩ := hL
  have hne : ∀ j < t, m (Qb + j) ≠ v := fun j hj he => by
    have := (mark v hv).2 ⟨j, hj, he⟩; omega
  have htN : t < N := bf_t_lt qlt qnd hv hne
  -- reading the new memory
  have rQ : ∀ j, bfW m LABb Qb L t v (Qb + j) = if j = t then v else m (Qb + j) := by
    intro j; unfold bfW
    by_cases hj : j = t
    · subst hj; rw [upd_apply, tgIteT rfl, tgIteT rfl]
    · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), tgIteF hj]
  have rL : ∀ u < N, bfW m LABb Qb L t v (LABb + u) = if u = v then L else m (LABb + u) := by
    intro u hu; unfold bfW
    rw [upd_other _ _ _ (by omega)]
    by_cases huv : u = v
    · subst huv; rw [upd_apply, tgIteT rfl, tgIteT rfl]
    · rw [upd_other _ _ _ (by omega), tgIteF huv]
  have qlt' : ∀ j < t + 1, bfW m LABb Qb L t v (Qb + j) < N := fun j hj => by
    rw [rQ]; split_ifs with h1
    · exact hv
    · exact qlt j (by omega)
  -- labels of marked nodes are unchanged
  have rLm : ∀ u < N, 0 < m (LABb + u) → bfW m LABb Qb L t v (LABb + u) = m (LABb + u) :=
    fun u hu hp => by rw [rL u hu, tgIteF (fun h => by subst h; omega)]
  refine ⟨htN, ⟨by omega, by omega, qlt', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i hi j hj he
    rw [rQ, rQ] at he
    by_cases hit : i = t <;> by_cases hjt : j = t
    · omega
    · rw [tgIteT hit, tgIteF hjt] at he; exact absurd he.symm (hne j (by omega))
    · rw [tgIteF hit, tgIteT hjt] at he; exact absurd he (hne i (by omega))
    · rw [tgIteF hit, tgIteF hjt] at he; exact qnd i (by omega) j (by omega) he
  · intro u hu
    rw [rL u hu]
    by_cases huv : u = v
    · subst huv; rw [tgIteT rfl]
      exact ⟨fun _ => ⟨t, by omega, by rw [rQ, tgIteT rfl]⟩, fun _ => hL0⟩
    · rw [tgIteF huv, mark u hu]
      constructor
      · rintro ⟨j, hj, he⟩; exact ⟨j, by omega, by rw [rQ, tgIteF (by omega)]; exact he⟩
      · rintro ⟨j, hj, he⟩
        rw [rQ] at he
        by_cases hjt : j = t
        · rw [tgIteT hjt] at he; exact absurd he.symm huv
        · rw [tgIteF hjt] at he; exact ⟨j, by omega, he⟩
  · intro u hu
    rw [rL u hu]; split_ifs
    · exact le_refl _
    · exact labL u hu
  · intro u hu w hw hp he
    rw [rL u hu, rL w hw] at he
    rw [rL u hu] at hp
    by_cases huv : u = v <;> by_cases hwv : w = v
    · subst huv; subst hwv; exact .refl
    · rw [tgIteT huv, tgIteF hwv] at he
      subst huv
      have hwp : 0 < m (LABb + w) := by omega
      exact rtg_symm_of_symm hs (hR w hw hwp he.symm)
    · rw [tgIteF huv, tgIteT hwv] at he
      rw [tgIteF huv] at hp
      subst hwv
      exact hR u hu hp he
    · rw [tgIteF huv, tgIteF hwv] at he
      rw [tgIteF huv] at hp
      exact reach u hu w hw hp he
  · intro j hj w hw
    rw [rQ, tgIteF (by omega)] at hw ⊢
    obtain ⟨h1, h2⟩ := clos j hj w hw
    have hwN : w < N := hval _ _ hw
    have hpj := (mark _ (qlt j (by omega))).2 ⟨j, by omega, rfl⟩
    rw [rLm w hwN h1, rLm _ (qlt j (by omega)) hpj]
    exact ⟨h1, h2⟩
  · intro j hj1 hj2
    rw [rQ]
    by_cases hjt : j = t
    · rw [tgIteT hjt, rL v hv, tgIteT rfl]
    · rw [tgIteF hjt]
      have hp := (mark _ (qlt j (by omega))).2 ⟨j, by omega, rfl⟩
      rw [rLm _ (qlt j (by omega)) hp]
      exact cur j hj1 (by omega)
  · intro a ha1 ha2
    unfold bfW
    rw [upd_other _ _ _ (fun h => ha2 ⟨by omega, by omega⟩),
      upd_other _ _ _ (fun h => ha1 ⟨by omega, by omega⟩)]
    exact frame a ha1 ha2

/-- Positive labels and the queue entries below `t` are kept. -/
def BfMono (N LABb Qb t : ℕ) (m m' : ℕ → ℕ) : Prop :=
  (∀ u < N, 0 < m (LABb + u) → m' (LABb + u) = m (LABb + u)) ∧
    ∀ j < t, m' (Qb + j) = m (Qb + j)

lemma bfMono_refl (N LABb Qb t : ℕ) (m : ℕ → ℕ) : BfMono N LABb Qb t m m :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩

lemma bfMono_trans {N LABb Qb t t' : ℕ} {m m' m'' : ℕ → ℕ} (h1 : BfMono N LABb Qb t m m')
    (h2 : BfMono N LABb Qb t' m' m'') (htt : t ≤ t') : BfMono N LABb Qb t m m'' := by
  refine ⟨fun u hu hp => ?_, fun j hj => ?_⟩
  · rw [h2.1 u hu (by rw [h1.1 u hu hp]; exact hp), h1.1 u hu hp]
  · rw [h2.2 j (by omega), h1.2 j hj]

lemma bfMono_push {N LABb Qb L t v : ℕ} {m : ℕ → ℕ} (hlay : LABb + N ≤ Qb) (hv : v < N)
    (h0 : m (LABb + v) = 0) : BfMono N LABb Qb t m (bfW m LABb Qb L t v) := by
  refine ⟨fun u hu hp => ?_, fun j hj => ?_⟩
  · have huv : u ≠ v := fun h => by subst h; omega
    unfold bfW
    rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
  · unfold bfW
    rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]

/-- **A neighbour already marked has the current label.** -/
lemma bfCore_lab_of_marked (hs : ∀ u v, bfAdj m₀ N OFFb ADJb u v → bfAdj m₀ N OFFb ADJb v u)
    (hL : BfCore m₀ m N OFFb ADJb LABb Qb L hc (hc + 1) t) (hu : m (LABb + m (Qb + hc)) = L)
    {v : ℕ} (hv : v < N) (hadj : bfAdj m₀ N OFFb ADJb (m (Qb + hc)) v)
    (hp : 0 < m (LABb + v)) : m (LABb + v) = L := by
  obtain ⟨j, hj, rfl⟩ := (hL.mark v hv).1 hp
  by_cases h1 : hc + 1 ≤ j
  · exact hL.cur j h1 hj
  · by_cases h2 : j = hc
    · subst h2; exact hu
    · have := (hL.clos j (by omega) _ (hs _ _ hadj)).2
      rw [← hu, this]

/-- **A pop**: the head of the queue is labelled `L`. -/
lemma bfCore_pop (hL : BfCore m₀ m N OFFb ADJb LABb Qb L h h t) (hht : h < t) :
    BfCore m₀ m N OFFb ADJb LABb Qb L h (h + 1) t ∧ m (LABb + m (Qb + h)) = L := by
  refine ⟨⟨by omega, hL.tN, hL.qlt, hL.qnd, hL.mark, hL.labL, hL.reach, hL.clos,
    fun j h1 h2 => hL.cur j (by omega) h2, hL.frame⟩, hL.cur h le_rfl hht⟩

/-- **The end of a scan of neighbours**: the popped entry is closed. -/
lemma bfCore_close (hL : BfCore m₀ m N OFFb ADJb LABb Qb L hc (hc + 1) t)
    (hu : m (LABb + m (Qb + hc)) = L)
    (hn : ∀ v, bfAdj m₀ N OFFb ADJb (m (Qb + hc)) v → 0 < m (LABb + v) ∧ m (LABb + v) = L) :
    BfCore m₀ m N OFFb ADJb LABb Qb L (hc + 1) (hc + 1) t := by
  refine ⟨hL.ht, hL.tN, hL.qlt, hL.qnd, hL.mark, hL.labL, hL.reach, fun j hj v hv => ?_,
    hL.cur, hL.frame⟩
  by_cases h1 : j = hc
  · subst h1; rw [hu]; exact hn v hv
  · exact hL.clos j (by omega) v hv

/-- **A new component** from the unmarked node `s`, queue empty: label `L + 1`. -/
lemma bfCore_new (hs : ∀ u v, bfAdj m₀ N OFFb ADJb u v → bfAdj m₀ N OFFb ADJb v u)
    (hval : ∀ u v, bfAdj m₀ N OFFb ADJb u v → v < N)
    (hL : BfCore m₀ m N OFFb ADJb LABb Qb L h h h) (hlay : LABb + N ≤ Qb) {s : ℕ} (hsN : s < N)
    (h0 : m (LABb + s) = 0) :
    h < N ∧ BfCore m₀ (bfW m LABb Qb (L + 1) h s) N OFFb ADJb LABb Qb (L + 1) h h (h + 1) := by
  have hL' : BfCore m₀ m N OFFb ADJb LABb Qb (L + 1) h h h :=
    ⟨hL.ht, hL.tN, hL.qlt, hL.qnd, hL.mark, fun u hu => le_trans (hL.labL u hu) (by omega),
      hL.reach, hL.clos, fun j h1 h2 => absurd h2 (by omega), hL.frame⟩
  exact bfCore_push hs hval hL' hlay le_rfl hsN h0 (by omega)
    (fun w hw _ he => absurd he (by have := hL.labL w hw; omega))

/-- **The end**: every node marked, every entry closed: equal labels exactly on components. -/
lemma bfCore_final (hval : ∀ u v, bfAdj m₀ N OFFb ADJb u v → v < N)
    (hL : BfCore m₀ m N OFFb ADJb LABb Qb L t t t) (hall : ∀ u < N, 0 < m (LABb + u)) :
    ∀ u < N, ∀ v < N,
      (m (LABb + u) = m (LABb + v) ↔ ReflTransGen (bfAdj m₀ N OFFb ADJb) u v) := by
  intro u hu v hv
  refine ⟨fun he => hL.reach u hu v hv (hall u hu) he, fun hr => ?_⟩
  have key : ∀ b, ReflTransGen (bfAdj m₀ N OFFb ADJb) u b → b < N ∧ m (LABb + b) = m (LABb + u) := by
    intro b hb
    induction hb with
    | refl => exact ⟨hu, rfl⟩
    | tail _ hst ih =>
      obtain ⟨hbN, hbl⟩ := ih
      obtain ⟨j, hj, hjb⟩ := (hL.mark _ hbN).1 (hall _ hbN)
      have hst' := hst
      rw [← hjb] at hst'
      have := (hL.clos j hj _ hst').2
      rw [hjb] at this
      exact ⟨hval _ _ hst, by rw [this, hbl]⟩
  exact (key v hr).2.symm

lemma bfW_lab_self {m : ℕ → ℕ} {N LABb Qb L t v : ℕ} (hlay : LABb + N ≤ Qb) (hv : v < N) :
    bfW m LABb Qb L t v (LABb + v) = L := by
  unfold bfW; rw [upd_other _ _ _ (by omega), upd_same]

/-- The layout: `OFF (N + 1) | ADJ (E) | LAB (N) | Q (N + 1)` below `W`. -/
structure BfLay (N E OFFb ADJb LABb Qb W : ℕ) : Prop where
  l1 : OFFb + N + 1 ≤ ADJb
  l2 : ADJb + E ≤ LABb
  l3 : LABb + N ≤ Qb
  l4 : Qb + N + 1 ≤ W

/-- The input graph: nondecreasing offsets ending at `E`, neighbours `< N`, symmetric. -/
structure BfIn (m₀ : ℕ → ℕ) (N OFFb ADJb E : ℕ) : Prop where
  mono : ∀ u < N, m₀ (OFFb + u) ≤ m₀ (OFFb + u + 1)
  last : m₀ (OFFb + N) = E
  val : ∀ u v, bfAdj m₀ N OFFb ADJb u v → v < N
  sym : ∀ u v, bfAdj m₀ N OFFb ADJb u v → bfAdj m₀ N OFFb ADJb v u

lemma bf_off_le {m₀ : ℕ → ℕ} {N OFFb : ℕ} (hmono : ∀ u < N, m₀ (OFFb + u) ≤ m₀ (OFFb + u + 1)) :
    ∀ k u, u + k = N → m₀ (OFFb + u) ≤ m₀ (OFFb + N) := by
  intro k
  induction k with
  | zero => intro u hu; rw [show u = N by omega]
  | succ k ih =>
    intro u hu
    exact le_trans (hmono u (by omega)) (by
      have := ih (u + 1) (by omega); rwa [show OFFb + (u + 1) = OFFb + u + 1 by omega] at this)

end Pure

/-! ### The program -/

open WordRAM.Machine.Stmt WordRAM.Programs

/-- Push `v = r4415` with the label `L = r4408` at the tail `t = r4410`. -/
def bfPush : Stmt :=
  block [.addN 4416 4403 4415, .storeN 4416 4408, .addN 4416 4404 4410, .storeN 4416 4415,
    .addN 4410 4410 4405]

/-- One neighbour `v = ADJ[i]`: push it if unlabelled. -/
def bfEdge : Stmt :=
  .seq (block [.addN 4416 4402 4411, .loadN 4415 4416, .addN 4416 4403 4415, .loadN 4414 4416])
    (.seq (.ifLtN 4406 4414 .skip bfPush) (block [.addN 4411 4411 4405]))

/-- Pop `u = Q[h]` and scan its neighbours. -/
def bfPop : Stmt :=
  .seq (block [.addN 4416 4404 4409, .loadN 4413 4416, .addN 4409 4409 4405, .addN 4416 4401 4413,
    .loadN 4411 4416, .addN 4416 4416 4405, .loadN 4412 4416]) (.whileLtN 4411 4412 bfEdge)

/-- A new component from `s = r4407`: the next label, push `s`, search. -/
def bfNew : Stmt :=
  .seq (block [.addN 4408 4408 4405, .copyN 4415 4407]) (.seq bfPush (.whileLtN 4409 4410 bfPop))

/-- One node of the scan. -/
def bfOuter : Stmt :=
  .seq (block [.addN 4416 4403 4407, .loadN 4414 4416])
    (.seq (.ifLtN 4406 4414 .skip bfNew) (block [.addN 4407 4407 4405]))

/-- **Connected components by breadth-first search.** -/
def bfProg : Stmt :=
  .seq (block [.constN 4405 1, .constN 4406 0, .constN 4407 0, .constN 4408 0, .constN 4409 0,
    .constN 4410 0]) (.whileLtN 4407 4400 bfOuter)

section Exec

variable {P : Input} {W : ℕ}

/-- A loop with a potential, keeping the final potential in the bound. -/
theorem bfWhilePot {a b : ℕ} {body : Stmt} (I : Config → Prop)
    (Φ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k + Φ c' ≤ Φ c + 2 := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨c₁, k₁, hb, hI₁, hΦ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hk₂⟩ := ih (Φ c₁) (by omega) hI₁ rfl
      exact ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', by omega⟩
    · exact ⟨c, 2, .whileLtN_false ht (hI c hc), hc, ht, by omega⟩

theorem bfPush_exec (c : Config) (hc : WordsBounded W c) {LABb Qb L t v : ℕ}
    (r3 : c.nreg 4403 = LABb) (r4 : c.nreg 4404 = Qb) (r5 : c.nreg 4405 = 1)
    (r8 : c.nreg 4408 = L) (r10 : c.nreg 4410 = t) (r15 : c.nreg 4415 = v)
    (w1 : LABb + v ≤ W) (w2 : Qb + t ≤ W) (w3 : t + 1 ≤ W) :
    ∃ c' k, Exec P W bfPush c c' k ∧ k = 5 ∧ c'.nreg 4410 = t + 1 ∧
      c'.nmem = bfW c.nmem LABb Qb L t v ∧
      (∀ x, x ≠ 4410 → x ≠ 4416 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bfPush
  exec_block
  all_goals try (config_simp; simp only [r3, r4, r5, r8, r10, r15]; omega)
  refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r5, r10]
  · config_simp; simp only [r3, r4, r8, r10, r15, bfW]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **One neighbour.** -/
theorem bfEdge_exec (c : Config) (hc : WordsBounded W c) {ADJb LABb Qb L t i : ℕ}
    (r2 : c.nreg 4402 = ADJb) (r3 : c.nreg 4403 = LABb) (r4 : c.nreg 4404 = Qb)
    (r5 : c.nreg 4405 = 1) (r6 : c.nreg 4406 = 0) (r8 : c.nreg 4408 = L)
    (r10 : c.nreg 4410 = t) (r11 : c.nreg 4411 = i)
    (w0 : ADJb + i ≤ W) (w1 : LABb + c.nmem (ADJb + i) ≤ W) (w2 : Qb + t ≤ W) (w3 : t + 1 ≤ W)
    (w4 : i + 1 ≤ W) :
    ∃ c' k, Exec P W bfEdge c c' k ∧ k ≤ 12 ∧ c'.nreg 4411 = i + 1 ∧
      (0 < c.nmem (LABb + c.nmem (ADJb + i)) → c'.nmem = c.nmem ∧ c'.nreg 4410 = t) ∧
      (c.nmem (LABb + c.nmem (ADJb + i)) = 0 →
        c'.nmem = bfW c.nmem LABb Qb L t (c.nmem (ADJb + i)) ∧ c'.nreg 4410 = t + 1) ∧
      (∀ x, x ≠ 4410 → x ≠ 4411 → x ≠ 4414 → x ≠ 4415 → x ≠ 4416 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bfEdge
  set v := c.nmem (ADJb + i) with hv
  obtain ⟨c₁, k₁, e₁, hk₁, g14, g15, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 4416 4402 4411, .loadN 4415 4416, .addN 4416 4403 4415,
        .loadN 4414 4416]) c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 4414 = c.nmem (LABb + v) ∧
      c₁.nreg 4415 = v ∧
      (∀ x, x ≠ 4414 → x ≠ 4415 → x ≠ 4416 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; simp only [r2, r3, r11]; omega)
    refine ⟨rfl, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r2, r3, r11, hv]
    · config_simp; simp only [r2, r11, hv]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 4414 → x ≠ 4415 → x ≠ 4416 → c₁.nreg x = c.nreg x := gn₁
  obtain ⟨c₂, k₂, e₂, hk₂, H1, H2, gn₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (.ifLtN 4406 4414 .skip bfPush) c₁ c₂ k₂ ∧ k₂ ≤ 7 ∧
      (0 < c.nmem (LABb + v) → c₂.nmem = c.nmem ∧ c₂.nreg 4410 = t) ∧
      (c.nmem (LABb + v) = 0 → c₂.nmem = bfW c.nmem LABb Qb L t v ∧ c₂.nreg 4410 = t + 1) ∧
      (∀ x, x ≠ 4410 → x ≠ 4414 → x ≠ 4415 → x ≠ 4416 → c₂.nreg x = c.nreg x) ∧
      c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    by_cases hh : c₁.nreg 4406 < c₁.nreg 4414
    · have hp : 0 < c.nmem (LABb + v) := by
        rw [q _ (by omega) (by omega) (by omega), r6, g14] at hh; exact hh
      refine ⟨c₁, 1, .ifLtN_true hh (.skip hw₁), by omega, fun _ => ⟨gm₁, ?_⟩,
        fun h => absurd h (by omega), fun x a b d e => q x b d e, gr₁, grm₁, go₁⟩
      rw [q _ (by omega) (by omega) (by omega), r10]
    · have h0 : c.nmem (LABb + v) = 0 := by
        rw [q _ (by omega) (by omega) (by omega), r6, g14] at hh; omega
      obtain ⟨c₂, k₂, e₂, hk₂, h10, hm₂, hn₂, hr₂, hrm₂, ho₂⟩ := bfPush_exec (P := P) c₁ hw₁
        (by rw [q _ (by omega) (by omega) (by omega), r3])
        (by rw [q _ (by omega) (by omega) (by omega), r4])
        (by rw [q _ (by omega) (by omega) (by omega), r5])
        (by rw [q _ (by omega) (by omega) (by omega), r8])
        (by rw [q _ (by omega) (by omega) (by omega), r10]) g15 w1 w2 w3
      rw [gm₁] at hm₂
      refine ⟨c₂, k₂ + 2, .ifLtN_false hh e₂, by omega, fun h => absurd h0 (by omega),
        fun _ => ⟨hm₂, h10⟩, fun x a b d e => ?_, by rw [hr₂, gr₁], by rw [hrm₂, grm₁],
        by rw [ho₂, go₁]⟩
      rw [hn₂ x a e, q x b d e]
  have hw₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, h11, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.addN 4411 4411 4405]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 4411 = i + 1 ∧
      (∀ x, x ≠ 4411 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have p5 : c₂.nreg 4405 = 1 := by rw [gn₂ _ (by omega) (by omega) (by omega) (by omega), r5]
    have p11 : c₂.nreg 4411 = i := by
      rw [gn₂ _ (by omega) (by omega) (by omega) (by omega), r11]
    exec_block
    all_goals try ((try config_simp); (try simp only [p5, p11]); omega)
    refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [p5, p11]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, h11, fun h => ?_, fun h => ?_,
    fun x a b d e f => by rw [hn₃ x b, gn₂ x a d e f], by rw [hr₃, gr₂], by rw [hrm₃, grm₂],
    by rw [ho₃, go₂]⟩
  · obtain ⟨x, y⟩ := H1 h
    exact ⟨by rw [hm₃, x], by rw [hn₃ _ (by omega), y]⟩
  · obtain ⟨x, y⟩ := H2 h
    exact ⟨by rw [hm₃, x], by rw [hn₃ _ (by omega), y]⟩

/-- **The scan of the neighbours of the popped node** `u = Q[j₀]`. -/
theorem bfScan_exec (c : Config) (hc : WordsBounded W c) {m₀ : ℕ → ℕ}
    {N E OFFb ADJb LABb Qb L j₀ t u : ℕ}
    (hL : BfLay N E OFFb ADJb LABb Qb W) (hG : BfIn m₀ N OFFb ADJb E)
    (r2 : c.nreg 4402 = ADJb) (r3 : c.nreg 4403 = LABb) (r4 : c.nreg 4404 = Qb)
    (r5 : c.nreg 4405 = 1) (r6 : c.nreg 4406 = 0) (r8 : c.nreg 4408 = L)
    (r10 : c.nreg 4410 = t) (r11 : c.nreg 4411 = m₀ (OFFb + u))
    (r12 : c.nreg 4412 = m₀ (OFFb + u + 1))
    (hB : BfCore m₀ c.nmem N OFFb ADJb LABb Qb L j₀ (j₀ + 1) t) (hu : c.nmem (Qb + j₀) = u)
    (huL : c.nmem (LABb + u) = L) :
    ∃ c' k, Exec P W (.whileLtN 4411 4412 bfEdge) c c' k ∧ k ≤ 14 * bfDeg m₀ OFFb u + 2 ∧
      t ≤ c'.nreg 4410 ∧
      BfCore m₀ c'.nmem N OFFb ADJb LABb Qb L (j₀ + 1) (j₀ + 1) (c'.nreg 4410) ∧
      BfMono N LABb Qb t c.nmem c'.nmem ∧
      (∀ x, x ≠ 4410 → x ≠ 4411 → x ≠ 4414 → x ≠ 4415 → x ≠ 4416 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4⟩ := hL
  have huN : u < N := by rw [← hu]; exact hB.qlt j₀ (by have := hB.ht; omega)
  have hupos : 0 < c.nmem (LABb + u) := (hB.mark u huN).2 ⟨j₀, by have := hB.ht; omega, hu⟩
  have hL0 : 0 < L := by omega
  have hmono := hG.mono
  have hoffE : m₀ (OFFb + u + 1) ≤ E := by
    rw [← hG.last]
    have := bf_off_le hmono (N - (u + 1)) (u + 1) (by omega)
    rwa [show OFFb + (u + 1) = OFFb + u + 1 by omega] at this
  have hlohi : m₀ (OFFb + u) ≤ m₀ (OFFb + u + 1) := hmono u huN
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, x ≠ 4410 → x ≠ 4411 → x ≠ 4414 → x ≠ 4415 → x ≠ 4416 → c'.nreg x = c.nreg x) ∧
    t ≤ c'.nreg 4410 ∧ BfCore m₀ c'.nmem N OFFb ADJb LABb Qb L j₀ (j₀ + 1) (c'.nreg 4410) ∧
    BfMono N LABb Qb t c.nmem c'.nmem ∧
    (∀ i', m₀ (OFFb + u) ≤ i' → i' < i → 0 < c'.nmem (LABb + m₀ (ADJb + i')) ∧
      c'.nmem (LABb + m₀ (ADJb + i')) = L) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', k, e, hk, hw', h11', j1, j2, j3, j4, j5, j6, j7, j8⟩ := tgRange (P := P)
    (a := 4411) (b := 4412) (body := bfEdge) J (B := 12) c hc r11 r12 hlohi
    ⟨fun _ _ _ _ _ _ => rfl, by rw [r10], by rw [r10]; exact hB, bfMono_refl _ _ _ _ _,
      fun i' h1 h2 => absurd h2 (by omega), rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h11 h12 ⟨j1, j2, j3, j4, j5, j6, j7, j8⟩ => by
      have f : ∀ x, x ≠ 4410 → x ≠ 4411 → x ≠ 4414 → x ≠ 4415 → x ≠ 4416 →
          c'.nreg x = c.nreg x := j1
      set t' := c'.nreg 4410 with ht'
      have htN : t' ≤ N := j3.tN
      have hiE : i < E := by omega
      have hadj : c'.nmem (ADJb + i) = m₀ (ADJb + i) := j3.frame _ (by omega) (by omega)
      set v := m₀ (ADJb + i) with hv
      have hAuv : bfAdj m₀ N OFFb ADJb u v := ⟨huN, i, hlo, hhi, rfl⟩
      have hvN : v < N := hG.val _ _ hAuv
      have hu' : c'.nmem (Qb + j₀) = u := by rw [j4.2 j₀ (by have := hB.ht; omega), hu]
      have huL' : c'.nmem (LABb + u) = L := by rw [j4.1 u huN hupos, huL]
      obtain ⟨c'', k', e', hk', h11'', H1, H2, hn'', hr'', hrm'', ho''⟩ := bfEdge_exec (P := P)
        c' hw (by rw [f _ (by omega) (by omega) (by omega) (by omega) (by omega), r2])
        (by rw [f _ (by omega) (by omega) (by omega) (by omega) (by omega), r3])
        (by rw [f _ (by omega) (by omega) (by omega) (by omega) (by omega), r4])
        (by rw [f _ (by omega) (by omega) (by omega) (by omega) (by omega), r5])
        (by rw [f _ (by omega) (by omega) (by omega) (by omega) (by omega), r6])
        (by rw [f _ (by omega) (by omega) (by omega) (by omega) (by omega), r8])
        ht'.symm h11 (by omega) (by rw [hadj]; omega) (by omega) (by omega) (by omega)
      rw [hadj] at H1 H2
      have fr'' : ∀ x, x ≠ 4410 → x ≠ 4411 → x ≠ 4414 → x ≠ 4415 → x ≠ 4416 →
          c''.nreg x = c.nreg x := fun x a b d e g => by rw [hn'' x a b d e g, f x a b d e g]
      have h12'' : c''.nreg 4412 = m₀ (OFFb + u + 1) := by
        rw [fr'' _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r12
      refine ⟨c'', k', e', hk', h11'', h12'', ?_⟩
      by_cases hp : 0 < c'.nmem (LABb + v)
      · obtain ⟨hm'', h10''⟩ := H1 hp
        have hvL : c'.nmem (LABb + v) = L := by
          rw [← hu'] at hAuv
          exact bfCore_lab_of_marked hG.sym j3 (by rw [hu']; exact huL') hvN hAuv hp
        refine ⟨fr'', by rw [h10'']; exact j2, by rw [hm'', h10'']; exact j3,
          by rw [hm'']; exact j4, fun i' h1 h2 => ?_, by rw [hr'', j6], by rw [hrm'', j7],
          by rw [ho'', j8]⟩
        rw [hm'']
        rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | h2
        · exact j5 i' h1 h2
        · subst h2; exact ⟨hp, hvL⟩
      · have h0 : c'.nmem (LABb + v) = 0 := by omega
        obtain ⟨hm'', h10''⟩ := H2 h0
        have hR : ∀ w < N, 0 < c'.nmem (LABb + w) → c'.nmem (LABb + w) = L →
            ReflTransGen (bfAdj m₀ N OFFb ADJb) w v := fun w hw hpw hwl =>
          (j3.reach w hw u huN hpw (by rw [hwl, huL'])).tail hAuv
        obtain ⟨htN', hB'⟩ := bfCore_push hG.sym hG.val j3 l3 (by have := j3.ht; omega) hvN h0
          hL0 hR
        have hmo := bfMono_push (L := L) (t := t') l3 hvN h0
        refine ⟨fr'', by rw [h10'']; omega, by rw [hm'', h10'']; exact hB',
          by rw [hm'']; exact bfMono_trans j4 hmo j2, fun i' h1 h2 => ?_, by rw [hr'', j6],
          by rw [hrm'', j7], by rw [ho'', j8]⟩
        rw [hm'']
        rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | h2
        · obtain ⟨a, b⟩ := j5 i' h1 h2
          have hwN : m₀ (ADJb + i') < N := hG.val u _ ⟨huN, i', h1, by omega, rfl⟩
          rw [hmo.1 _ hwN a]; exact ⟨a, b⟩
        · subst h2; rw [bfW_lab_self l3 hvN]; exact ⟨hL0, rfl⟩)
  refine ⟨c', k, e, by unfold bfDeg; omega, j2, ?_, j4, j1, j6, j7, j8⟩
  have hu' : c'.nmem (Qb + j₀) = u := by rw [j4.2 j₀ (by have := hB.ht; omega), hu]
  have huL' : c'.nmem (LABb + u) = L := by rw [j4.1 u huN hupos, huL]
  refine bfCore_close j3 (by rw [hu']; exact huL') fun v hv => ?_
  rw [hu'] at hv
  obtain ⟨_, i, h1, h2, rfl⟩ := hv
  exact j5 i h1 h2

/-- **A pop** of `u = Q[h]` and the scan of its neighbours. -/
theorem bfPop_exec (c : Config) (hc : WordsBounded W c) {m₀ : ℕ → ℕ}
    {N E OFFb ADJb LABb Qb L h t : ℕ}
    (hL : BfLay N E OFFb ADJb LABb Qb W) (hG : BfIn m₀ N OFFb ADJb E)
    (r1 : c.nreg 4401 = OFFb) (r2 : c.nreg 4402 = ADJb) (r3 : c.nreg 4403 = LABb)
    (r4 : c.nreg 4404 = Qb) (r5 : c.nreg 4405 = 1) (r6 : c.nreg 4406 = 0)
    (r8 : c.nreg 4408 = L) (r9 : c.nreg 4409 = h) (r10 : c.nreg 4410 = t) (hht : h < t)
    (hB : BfCore m₀ c.nmem N OFFb ADJb LABb Qb L h h t) :
    ∃ c' k, Exec P W bfPop c c' k ∧ k ≤ 9 + 14 * bfDeg m₀ OFFb (c.nmem (Qb + h)) ∧
      c'.nreg 4409 = h + 1 ∧ t ≤ c'.nreg 4410 ∧
      BfCore m₀ c'.nmem N OFFb ADJb LABb Qb L (h + 1) (h + 1) (c'.nreg 4410) ∧
      BfMono N LABb Qb t c.nmem c'.nmem ∧
      (∀ x, (x < 4409 ∨ 4416 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hLay := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL
  unfold bfPop
  set u := c.nmem (Qb + h) with hu
  have huN : u < N := hB.qlt h hht
  have hNt : t ≤ N := hB.tN
  have o1 : c.nmem (OFFb + u) = m₀ (OFFb + u) := hB.frame _ (by omega) (by omega)
  have o2 : c.nmem (OFFb + u + 1) = m₀ (OFFb + u + 1) := hB.frame _ (by omega) (by omega)
  obtain ⟨c₁, k₁, e₁, hk₁, g9, g11, g12, g13, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 4416 4404 4409, .loadN 4413 4416, .addN 4409 4409 4405,
        .addN 4416 4401 4413, .loadN 4411 4416, .addN 4416 4416 4405, .loadN 4412 4416])
        c c₁ k₁ ∧ k₁ = 7 ∧ c₁.nreg 4409 = h + 1 ∧ c₁.nreg 4411 = m₀ (OFFb + u) ∧
      c₁.nreg 4412 = m₀ (OFFb + u + 1) ∧ c₁.nreg 4413 = u ∧
      (∀ x, x ≠ 4409 → x ≠ 4411 → x ≠ 4412 → x ≠ 4413 → x ≠ 4416 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; simp only [r1, r4, r5, r9, ← hu]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x a b d e g => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r5, r9]
    · config_simp; simp only [r1, r4, r9, ← hu, o1]
    · config_simp; simp only [r1, r4, r5, r9, ← hu, o2]
    · config_simp; simp only [r4, r9, ← hu]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 4409 → x ≠ 4411 → x ≠ 4412 → x ≠ 4413 → x ≠ 4416 → c₁.nreg x = c.nreg x :=
    gn₁
  obtain ⟨hB1, huL⟩ := bfCore_pop hB hht
  rw [← gm₁] at hB1
  have hu' : c₁.nmem (Qb + h) = u := by rw [gm₁]
  have huL' : c₁.nmem (LABb + u) = L := by rw [gm₁]; exact huL
  obtain ⟨c₂, k₂, e₂, hk₂, h10₂, hB₂, hmo₂, hn₂, hr₂, hrm₂, ho₂⟩ := bfScan_exec (P := P) c₁ hw₁
    hLay hG (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega), r2])
    (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega), r3])
    (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega), r4])
    (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega), r5])
    (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega), r6])
    (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega), r8])
    (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega), r10]) g11 g12 hB1
    hu' huL'
  rw [gm₁] at hmo₂
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, ?_, h10₂, hB₂, hmo₂, fun x hx => ?_,
    by rw [hr₂, gr₁], by rw [hrm₂, grm₁], by rw [ho₂, go₁]⟩
  · rw [hn₂ _ (by omega) (by omega) (by omega) (by omega) (by omega), g9]
  · rw [hn₂ _ (by omega) (by omega) (by omega) (by omega) (by omega),
      q _ (by omega) (by omega) (by omega) (by omega) (by omega)]

/-- The potential of the search: `11 (N - h) + 14 (E - Σ_{j<h} deg Q[j])`. -/
def bfPhi (m₀ : ℕ → ℕ) (N E OFFb Qb : ℕ) (c : Config) : ℕ :=
  11 * (N - c.nreg 4409) + 14 * (E - bfSum m₀ c.nmem OFFb Qb (c.nreg 4409))

/-- **The search until the queue is empty.** -/
theorem bfSearch_exec (c : Config) (hc : WordsBounded W c) {m₀ : ℕ → ℕ}
    {N E OFFb ADJb LABb Qb L h t : ℕ}
    (hL : BfLay N E OFFb ADJb LABb Qb W) (hG : BfIn m₀ N OFFb ADJb E)
    (r1 : c.nreg 4401 = OFFb) (r2 : c.nreg 4402 = ADJb) (r3 : c.nreg 4403 = LABb)
    (r4 : c.nreg 4404 = Qb) (r5 : c.nreg 4405 = 1) (r6 : c.nreg 4406 = 0)
    (r8 : c.nreg 4408 = L) (r9 : c.nreg 4409 = h) (r10 : c.nreg 4410 = t)
    (hB : BfCore m₀ c.nmem N OFFb ADJb LABb Qb L h h t) :
    ∃ c' k, Exec P W (.whileLtN 4409 4410 bfPop) c c' k ∧
      k + bfPhi m₀ N E OFFb Qb c' ≤ bfPhi m₀ N E OFFb Qb c + 2 ∧
      c'.nreg 4409 = c'.nreg 4410 ∧ t ≤ c'.nreg 4410 ∧
      BfCore m₀ c'.nmem N OFFb ADJb LABb Qb L (c'.nreg 4409) (c'.nreg 4409) (c'.nreg 4410) ∧
      BfMono N LABb Qb t c.nmem c'.nmem ∧
      (∀ x, (x < 4409 ∨ 4416 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hLay := hL
  let I : Config → Prop := fun c' => WordsBounded W c' ∧
    (∀ x, (x < 4409 ∨ 4416 < x) → c'.nreg x = c.nreg x) ∧ t ≤ c'.nreg 4410 ∧
    BfCore m₀ c'.nmem N OFFb ADJb LABb Qb L (c'.nreg 4409) (c'.nreg 4409) (c'.nreg 4410) ∧
    BfMono N LABb Qb t c.nmem c'.nmem ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', k, e, ⟨hw', i1, i2, i3, i4, i5, i6, i7⟩, hn, hk⟩ := bfWhilePot (P := P) (W := W)
    (a := 4409) (b := 4410) (body := bfPop) I (bfPhi m₀ N E OFFb Qb) (fun c h => h.1)
    (fun c' ⟨hw, i1, i2, i3, i4, i5, i6, i7⟩ hlt => by
      have f : ∀ x, (x < 4409 ∨ 4416 < x) → c'.nreg x = c.nreg x := i1
      obtain ⟨c'', k', e', hk', h9'', h10'', hB'', hmo'', hn'', hr'', hrm'', ho''⟩ :=
        bfPop_exec (P := P) c' hw hLay hG (by rw [f _ (by omega), r1]) (by rw [f _ (by omega), r2])
          (by rw [f _ (by omega), r3]) (by rw [f _ (by omega), r4]) (by rw [f _ (by omega), r5])
          (by rw [f _ (by omega), r6]) (by rw [f _ (by omega), r8]) rfl rfl hlt i3
      refine ⟨c'', k', e', ⟨e'.wb_right, fun x hx => by rw [hn'' x hx, f x hx], by omega,
        by rw [h9'']; exact hB'', bfMono_trans i4 hmo'' i2, by rw [hr'', i5], by rw [hrm'', i6],
        by rw [ho'', i7]⟩, ?_⟩
      unfold bfPhi
      rw [h9'']
      have hS : bfSum m₀ c''.nmem OFFb Qb (c'.nreg 4409 + 1) =
          bfSum m₀ c'.nmem OFFb Qb (c'.nreg 4409) +
            bfDeg m₀ OFFb (c'.nmem (Qb + c'.nreg 4409)) := by
        rw [bfSum_congr (fun j hj => hmo''.2 j (by omega)), bfSum_succ]
      have hle := bfSum_le (m := c''.nmem) (Qb := Qb) hG.mono (h := c'.nreg 4409 + 1)
        (fun j hj => hB''.qlt j (by have := hB''.ht; omega))
        (fun i hi j hj => hB''.qnd i (by have := hB''.ht; omega) j (by have := hB''.ht; omega))
      rw [hG.last] at hle
      have hN := i3.tN
      omega) ⟨hc, fun _ _ => rfl, by rw [r10], by rw [r9, r10]; exact hB, bfMono_refl _ _ _ _ _,
        rfl, rfl, rfl⟩
  have := i3.ht
  exact ⟨c', k, e, hk, by omega, i2, i3, i4, i1, i5, i6, i7⟩

/-- **A new component** from the unmarked node `s`. -/
theorem bfNew_exec (c : Config) (hc : WordsBounded W c) {m₀ : ℕ → ℕ}
    {N E OFFb ADJb LABb Qb L h s : ℕ}
    (hL : BfLay N E OFFb ADJb LABb Qb W) (hG : BfIn m₀ N OFFb ADJb E)
    (r1 : c.nreg 4401 = OFFb) (r2 : c.nreg 4402 = ADJb) (r3 : c.nreg 4403 = LABb)
    (r4 : c.nreg 4404 = Qb) (r5 : c.nreg 4405 = 1) (r6 : c.nreg 4406 = 0) (r7 : c.nreg 4407 = s)
    (r8 : c.nreg 4408 = L) (r9 : c.nreg 4409 = h) (r10 : c.nreg 4410 = h)
    (hB : BfCore m₀ c.nmem N OFFb ADJb LABb Qb L h h h) (hLh : L ≤ h) (hsN : s < N)
    (h0 : c.nmem (LABb + s) = 0) :
    ∃ c' k, Exec P W bfNew c c' k ∧
      k + bfPhi m₀ N E OFFb Qb c' ≤ bfPhi m₀ N E OFFb Qb c + 9 ∧
      c'.nreg 4409 = c'.nreg 4410 ∧ c'.nreg 4408 = L + 1 ∧ h + 1 ≤ c'.nreg 4410 ∧
      BfCore m₀ c'.nmem N OFFb ADJb LABb Qb (L + 1) (c'.nreg 4409) (c'.nreg 4409)
        (c'.nreg 4410) ∧
      BfMono N LABb Qb h c.nmem c'.nmem ∧ 0 < c'.nmem (LABb + s) ∧
      (∀ x, (x < 4408 ∨ 4416 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hLay := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL
  obtain ⟨hhN, hB'⟩ := bfCore_new hG.sym hG.val hB l3 hsN h0
  unfold bfNew
  obtain ⟨c₁, k₁, e₁, hk₁, g8, g15, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 4408 4408 4405, .copyN 4415 4407]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 4408 = L + 1 ∧ c₁.nreg 4415 = s ∧
      (∀ x, x ≠ 4408 → x ≠ 4415 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; simp only [r5, r8]; omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r5, r8]
    · config_simp; simp only [r7]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 4408 → x ≠ 4415 → c₁.nreg x = c.nreg x := gn₁
  obtain ⟨c₂, k₂, e₂, hk₂, h10₂, hm₂, hn₂, hr₂, hrm₂, ho₂⟩ := bfPush_exec (P := P) c₁ hw₁
    (by rw [q _ (by omega) (by omega), r3]) (by rw [q _ (by omega) (by omega), r4])
    (by rw [q _ (by omega) (by omega), r5]) g8 (by rw [q _ (by omega) (by omega), r10]) g15
    (by omega) (by omega) (by omega)
  rw [gm₁] at hm₂
  have hw₂ := e₂.wb_right
  have q2 : ∀ x, x ≠ 4408 → x ≠ 4410 → x ≠ 4415 → x ≠ 4416 → c₂.nreg x = c.nreg x :=
    fun x a b d e => by rw [hn₂ x b e, q x a d]
  have hB₂ : BfCore m₀ c₂.nmem N OFFb ADJb LABb Qb (L + 1) h h (h + 1) := by rw [hm₂]; exact hB'
  have hmo₂ : BfMono N LABb Qb h c.nmem c₂.nmem := by
    rw [hm₂]; exact bfMono_push l3 hsN h0
  obtain ⟨c₃, k₃, e₃, hk₃, h9₃, h10₃, hB₃, hmo₃, hn₃, hr₃, hrm₃, ho₃⟩ := bfSearch_exec (P := P)
    c₂ hw₂ hLay hG (by rw [q2 _ (by omega) (by omega) (by omega) (by omega), r1])
    (by rw [q2 _ (by omega) (by omega) (by omega) (by omega), r2])
    (by rw [q2 _ (by omega) (by omega) (by omega) (by omega), r3])
    (by rw [q2 _ (by omega) (by omega) (by omega) (by omega), r4])
    (by rw [q2 _ (by omega) (by omega) (by omega) (by omega), r5])
    (by rw [q2 _ (by omega) (by omega) (by omega) (by omega), r6])
    (by rw [hn₂ _ (by omega) (by omega), g8])
    (by rw [q2 _ (by omega) (by omega) (by omega) (by omega), r9]) h10₂ hB₂
  have hΦ : bfPhi m₀ N E OFFb Qb c₂ = bfPhi m₀ N E OFFb Qb c := by
    unfold bfPhi
    rw [q2 _ (by omega) (by omega) (by omega) (by omega), r9,
      bfSum_congr (fun j hj => hmo₂.2 j hj)]
  have hs₂ : 0 < c₂.nmem (LABb + s) := by rw [hm₂, bfW_lab_self l3 hsN]; omega
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, h9₃, ?_, h10₃, hB₃,
    bfMono_trans hmo₂ hmo₃ (by omega), by rw [hmo₃.1 s hsN hs₂]; exact hs₂, fun x hx => ?_,
    by rw [hr₃, hr₂, gr₁], by rw [hrm₃, hrm₂, grm₁], by rw [ho₃, ho₂, go₁]⟩
  · rw [hn₃ _ (by omega), hn₂ _ (by omega) (by omega), g8]
  · rw [hn₃ _ (by omega), q2 _ (by omega) (by omega) (by omega) (by omega)]

/-- **One node of the scan.** -/
theorem bfOuter_exec (c : Config) (hc : WordsBounded W c) {m₀ : ℕ → ℕ}
    {N E OFFb ADJb LABb Qb L h s : ℕ}
    (hL : BfLay N E OFFb ADJb LABb Qb W) (hG : BfIn m₀ N OFFb ADJb E)
    (r1 : c.nreg 4401 = OFFb) (r2 : c.nreg 4402 = ADJb) (r3 : c.nreg 4403 = LABb)
    (r4 : c.nreg 4404 = Qb) (r5 : c.nreg 4405 = 1) (r6 : c.nreg 4406 = 0) (r7 : c.nreg 4407 = s)
    (r8 : c.nreg 4408 = L) (r9 : c.nreg 4409 = h) (r10 : c.nreg 4410 = h)
    (hB : BfCore m₀ c.nmem N OFFb ADJb LABb Qb L h h h) (hLh : L ≤ h) (hsN : s < N) :
    ∃ c' k, Exec P W bfOuter c c' k ∧
      k + bfPhi m₀ N E OFFb Qb c' ≤ bfPhi m₀ N E OFFb Qb c + 14 ∧
      c'.nreg 4407 = s + 1 ∧ c'.nreg 4409 = c'.nreg 4410 ∧ c'.nreg 4408 ≤ c'.nreg 4409 ∧
      BfCore m₀ c'.nmem N OFFb ADJb LABb Qb (c'.nreg 4408) (c'.nreg 4409) (c'.nreg 4409)
        (c'.nreg 4410) ∧
      BfMono N LABb Qb h c.nmem c'.nmem ∧ 0 < c'.nmem (LABb + s) ∧
      (∀ x, (x < 4407 ∨ 4416 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hLay := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL
  unfold bfOuter
  obtain ⟨c₁, k₁, e₁, hk₁, g14, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 4416 4403 4407, .loadN 4414 4416]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 4414 = c.nmem (LABb + s) ∧
      (∀ x, x ≠ 4414 → x ≠ 4416 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; simp only [r3, r7]; omega)
    refine ⟨rfl, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r3, r7]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 4414 → x ≠ 4416 → c₁.nreg x = c.nreg x := gn₁
  have hB₁ : BfCore m₀ c₁.nmem N OFFb ADJb LABb Qb L h h h := by rw [gm₁]; exact hB
  have hΦ₁ : bfPhi m₀ N E OFFb Qb c₁ = bfPhi m₀ N E OFFb Qb c := by
    unfold bfPhi; rw [gm₁, q _ (by omega) (by omega)]
  obtain ⟨c₂, k₂, e₂, hk₂, h9₂, h89₂, hB₂, hmo₂, hs₂, gn₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (.ifLtN 4406 4414 .skip bfNew) c₁ c₂ k₂ ∧
      k₂ + bfPhi m₀ N E OFFb Qb c₂ ≤ bfPhi m₀ N E OFFb Qb c + 11 ∧
      c₂.nreg 4409 = c₂.nreg 4410 ∧ c₂.nreg 4408 ≤ c₂.nreg 4409 ∧
      BfCore m₀ c₂.nmem N OFFb ADJb LABb Qb (c₂.nreg 4408) (c₂.nreg 4409) (c₂.nreg 4409)
        (c₂.nreg 4410) ∧
      BfMono N LABb Qb h c.nmem c₂.nmem ∧ 0 < c₂.nmem (LABb + s) ∧
      (∀ x, (x < 4407 ∨ 4416 < x ∨ x = 4407) → c₂.nreg x = c.nreg x) ∧
      c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    by_cases hh : c₁.nreg 4406 < c₁.nreg 4414
    · have hp : 0 < c.nmem (LABb + s) := by
        rw [q _ (by omega) (by omega), r6, g14] at hh; exact hh
      have hm1 : BfMono N LABb Qb h c.nmem c₁.nmem := by rw [gm₁]; exact bfMono_refl _ _ _ _ _
      have hp1 : 0 < c₁.nmem (LABb + s) := by rw [gm₁]; exact hp
      refine ⟨c₁, 1, .ifLtN_true hh (.skip hw₁), by omega, ?_, ?_, ?_, hm1, hp1,
        fun x hx => q x (by omega) (by omega), gr₁, grm₁, go₁⟩
      · rw [q _ (by omega) (by omega), q _ (by omega) (by omega), r9, r10]
      · rw [q _ (by omega) (by omega), q _ (by omega) (by omega), r9, r8]; exact hLh
      · rw [q _ (by omega) (by omega), q _ (by omega) (by omega), q _ (by omega) (by omega),
          r9, r10, r8]; exact hB₁
    · have h0 : c.nmem (LABb + s) = 0 := by
        rw [q _ (by omega) (by omega), r6, g14] at hh; omega
      obtain ⟨c₂, k₂, e₂, hk₂, h9₂, h8₂, h10₂, hB₂, hmo₂, hs₂, hn₂, hr₂, hrm₂, ho₂⟩ :=
        bfNew_exec (P := P) c₁ hw₁ hLay hG (by rw [q _ (by omega) (by omega), r1])
          (by rw [q _ (by omega) (by omega), r2]) (by rw [q _ (by omega) (by omega), r3])
          (by rw [q _ (by omega) (by omega), r4]) (by rw [q _ (by omega) (by omega), r5])
          (by rw [q _ (by omega) (by omega), r6]) (by rw [q _ (by omega) (by omega), r7])
          (by rw [q _ (by omega) (by omega), r8]) (by rw [q _ (by omega) (by omega), r9])
          (by rw [q _ (by omega) (by omega), r10]) hB₁ hLh hsN (by rw [gm₁]; exact h0)
      rw [gm₁] at hmo₂
      refine ⟨c₂, k₂ + 2, .ifLtN_false hh e₂, by omega, h9₂, by rw [h8₂, h9₂]; omega,
        by rw [h8₂]; exact hB₂, hmo₂, hs₂, fun x hx => ?_, by rw [hr₂, gr₁],
        by rw [hrm₂, grm₁], by rw [ho₂, go₁]⟩
      rw [hn₂ x (by omega), q x (by omega) (by omega)]
  have hw₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, h7₃, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.addN 4407 4407 4405]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 4407 = s + 1 ∧
      (∀ x, x ≠ 4407 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have p5 : c₂.nreg 4405 = 1 := by rw [gn₂ _ (by omega), r5]
    have p7 : c₂.nreg 4407 = s := by rw [gn₂ _ (by omega), r7]
    exec_block
    all_goals try ((try config_simp); (try simp only [p5, p7]); omega)
    refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [p5, p7]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hΦ₃ : bfPhi m₀ N E OFFb Qb c₃ = bfPhi m₀ N E OFFb Qb c₂ := by
    unfold bfPhi; rw [hm₃, hn₃ _ (by omega)]
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, h7₃, ?_, ?_, ?_,
    by rw [hm₃]; exact hmo₂, by rw [hm₃]; exact hs₂, fun x hx => ?_, by rw [hr₃, gr₂],
    by rw [hrm₃, grm₂], by rw [ho₃, go₂]⟩
  · rw [hn₃ _ (by omega), hn₃ _ (by omega), h9₂]
  · rw [hn₃ _ (by omega), hn₃ _ (by omega)]; exact h89₂
  · rw [hn₃ _ (by omega), hn₃ _ (by omega), hn₃ _ (by omega), hm₃]; exact hB₂
  · rw [hn₃ _ (by omega), gn₂ x (by omega)]

/-- **Connected components on the machine**: under the layout `BfLay` and the input graph
conditions `BfIn` (nondecreasing offsets ending at `E`, neighbours `< N`, symmetric adjacency),
with the label array zero, within `27 N + 14 E + 8` steps every node `u < N` gets a label
`0 < LAB[u] ≤ N` with `LAB[u] = LAB[v] ↔ ReflTransGen (bfAdj …) u v`; memory outside the label and
queue arrays, registers outside `4405 … 4416`, reals and output kept. -/
theorem bfProg_exec (c : Config) (hc : WordsBounded W c) {N E OFFb ADJb LABb Qb : ℕ}
    (hL : BfLay N E OFFb ADJb LABb Qb W) (hG : BfIn c.nmem N OFFb ADJb E)
    (r0 : c.nreg 4400 = N) (r1 : c.nreg 4401 = OFFb) (r2 : c.nreg 4402 = ADJb)
    (r3 : c.nreg 4403 = LABb) (r4 : c.nreg 4404 = Qb)
    (hLAB : ∀ u < N, c.nmem (LABb + u) = 0) :
    ∃ c' k, Exec P W bfProg c c' k ∧ k ≤ 27 * N + 14 * E + 8 ∧
      (∀ u < N, ∀ v < N, (c'.nmem (LABb + u) = c'.nmem (LABb + v) ↔
        ReflTransGen (bfAdj c.nmem N OFFb ADJb) u v)) ∧
      (∀ u < N, 0 < c'.nmem (LABb + u) ∧ c'.nmem (LABb + u) ≤ N) ∧
      (∀ a, ¬ (LABb ≤ a ∧ a < LABb + N) → ¬ (Qb ≤ a ∧ a < Qb + N) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4405 ∨ 4416 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hLay := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL
  unfold bfProg
  obtain ⟨c₁, k₁, e₁, hk₁, g5, g6, g7, g8, g9, g10, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4405 1, .constN 4406 0, .constN 4407 0, .constN 4408 0,
        .constN 4409 0, .constN 4410 0]) c c₁ k₁ ∧ k₁ = 6 ∧ c₁.nreg 4405 = 1 ∧
      c₁.nreg 4406 = 0 ∧ c₁.nreg 4407 = 0 ∧ c₁.nreg 4408 = 0 ∧ c₁.nreg 4409 = 0 ∧
      c₁.nreg 4410 = 0 ∧ (∀ x, (x < 4405 ∨ 4410 < x) → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have hB₁ : BfCore c.nmem c₁.nmem N OFFb ADJb LABb Qb 0 0 0 0 := by
    rw [gm₁]
    refine ⟨le_rfl, Nat.zero_le _, fun j hj => absurd hj (by omega),
      fun i hi => absurd hi (by omega), fun u hu => ?_, fun u hu => by rw [hLAB u hu],
      fun u hu v hv hp => absurd hp (by rw [hLAB u hu]; omega),
      fun j hj => absurd hj (by omega), fun j h1 h2 => absurd h2 (by omega),
      fun _ _ _ => rfl⟩
    rw [hLAB u hu]
    exact ⟨fun h => absurd h (by omega), fun ⟨j, hj, _⟩ => absurd hj (by omega)⟩
  let I : Config → Prop := fun c' => WordsBounded W c' ∧
    (∀ x, (x < 4407 ∨ 4416 < x) → c'.nreg x = c₁.nreg x) ∧ c'.nreg 4407 ≤ N ∧
    c'.nreg 4409 = c'.nreg 4410 ∧ c'.nreg 4408 ≤ c'.nreg 4409 ∧
    BfCore c.nmem c'.nmem N OFFb ADJb LABb Qb (c'.nreg 4408) (c'.nreg 4409) (c'.nreg 4409)
      (c'.nreg 4410) ∧
    (∀ u < c'.nreg 4407, 0 < c'.nmem (LABb + u)) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c', k, e, ⟨hw', i1, i2, i3, i4, i5, i6, i7, i8, i9⟩, hn, hk⟩ := bfWhilePot (P := P)
    (W := W) (a := 4407) (b := 4400) (body := bfOuter) I
    (fun c' => 16 * (N - c'.nreg 4407) + bfPhi c.nmem N E OFFb Qb c') (fun c h => h.1)
    (fun c' ⟨hw, i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ hlt => by
      have f : ∀ x, (x < 4407 ∨ 4416 < x) → c'.nreg x = c₁.nreg x := i1
      have f0 : c'.nreg 4400 = N := by rw [f _ (by omega), gn₁ _ (by omega), r0]
      rw [f0] at hlt
      obtain ⟨c'', k', e', hk', h7'', h9'', h89'', hB'', hmo'', hs'', hn'', hr'', hrm'',
        ho''⟩ := bfOuter_exec (P := P) c' hw hLay hG
          (by rw [f _ (by omega), gn₁ _ (by omega), r1])
          (by rw [f _ (by omega), gn₁ _ (by omega), r2])
          (by rw [f _ (by omega), gn₁ _ (by omega), r3])
          (by rw [f _ (by omega), gn₁ _ (by omega), r4]) (by rw [f _ (by omega), g5])
          (by rw [f _ (by omega), g6]) rfl rfl rfl i3.symm (by rw [i3] at i5 ⊢; exact i5) i4 hlt
      refine ⟨c'', k', e', ⟨e'.wb_right, fun x hx => by rw [hn'' x hx, f x hx], by omega,
        h9'', h89'', hB'', fun u hu => ?_, by rw [hr'', i7], by rw [hrm'', i8],
        by rw [ho'', i9]⟩, by omega⟩
      rw [h7''] at hu
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · have huN : u < N := by omega
        rw [hmo''.1 u huN (i6 u hu)]; exact i6 u hu
      · exact hs'')
    ⟨hw₁, fun _ _ => rfl, by rw [g7]; omega, by rw [g9, g10], by rw [g8, g9],
      by rw [g8, g9, g10]; exact hB₁, fun u hu => absurd hu (by rw [g7]; omega), rfl, rfl, rfl⟩
  have f0 : c'.nreg 4400 = N := by rw [i1 _ (by omega), gn₁ _ (by omega), r0]
  rw [f0] at hn
  have hsN : c'.nreg 4407 = N := by omega
  have hall : ∀ u < N, 0 < c'.nmem (LABb + u) := fun u hu => i6 u (by omega)
  have hΦ₁ : bfPhi c.nmem N E OFFb Qb c₁ = 11 * N + 14 * E := by
    unfold bfPhi; rw [g9]; simp [bfSum]
  rw [i3] at i5
  refine ⟨c', k₁ + k, .seq e₁ e, by rw [g7, hΦ₁] at hk; omega, ?_, fun u hu => ⟨hall u hu, ?_⟩,
    fun a h1 h2 => i5.frame a h1 h2, fun x hx => ?_, by rw [i7, gr₁], by rw [i8, grm₁],
    by rw [i9, go₁]⟩
  · exact bfCore_final hG.val i5 hall
  · have := i5.labL u hu; have := i5.tN; omega
  · by_cases hx' : x < 4407 ∨ 4416 < x
    · rw [i1 x hx', gn₁ x (by omega)]
    · omega

end Exec

end BKMNW

end PlanarFlow
