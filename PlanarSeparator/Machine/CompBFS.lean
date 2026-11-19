module

public import PlanarSeparator.Machine.CompMath

/-!
# The components of a vertex set by breadth-first search: the invariants

The labelling of the components of `G[U]` by the program of
`PlanarSeparator/Machine/CompProg.lean`, abstractly: a label array `lab` (`0` off `U`, `1` on
the vertices of `U` not reached yet, `j + 1` on the `j`-th component found) and a component weight
array `cw`, scanned along the sorted list of `U` (`BInv`); one search from a seed `s` with the
queue `Q` (`BCore`, `Proc`, `Part`).

Everything is stated on natural numbers (vertex numbers), as the cells of the machine:
`UN U`, `cN U x` (the component of `x`), `adjN`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]

/-! ### Vertex sets on numbers -/

/-- The numbers of the vertices of `U`. -/
def UN (U : Finset (Fin N)) : Finset ℕ := U.map Fin.valEmbedding

variable (G) in
/-- The numbers of the vertices of the component of `x` in `U`. -/
noncomputable def cN (U : Finset (Fin N)) (x : ℕ) : Finset ℕ :=
  if h : x < N then (comp G U ⟨x, h⟩).map Fin.valEmbedding else ∅

variable (G) in
/-- Adjacency on numbers. -/
def adjN (x y : ℕ) : Prop := ∃ hx : x < N, ∃ hy : y < N, G.Adj ⟨x, hx⟩ ⟨y, hy⟩

theorem mem_UN {U : Finset (Fin N)} {x : ℕ} : x ∈ UN U ↔ ∃ h : x < N, (⟨x, h⟩ : Fin N) ∈ U := by
  simp only [UN, mem_map, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨v.2, hv⟩
  · rintro ⟨h, hx⟩; exact ⟨_, hx, rfl⟩

theorem lt_of_mem_UN {U : Finset (Fin N)} {x : ℕ} (h : x ∈ UN U) : x < N := (mem_UN.1 h).1

theorem val_mem_UN {U : Finset (Fin N)} {v : Fin N} : (v : ℕ) ∈ UN U ↔ v ∈ U := by
  rw [mem_UN]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨v.2, h⟩⟩

theorem card_UN (U : Finset (Fin N)) : #(UN U) = #U := card_map _

theorem mem_cN {U : Finset (Fin N)} {x y : ℕ} :
    y ∈ cN G U x ↔ ∃ hx : x < N, ∃ hy : y < N, (⟨y, hy⟩ : Fin N) ∈ comp G U ⟨x, hx⟩ := by
  unfold cN
  split
  · rename_i hx
    simp only [mem_map, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨hx, v.2, hv⟩
    · rintro ⟨_, hy, h⟩; exact ⟨_, h, rfl⟩
  · rename_i hx
    simp only [notMem_empty, false_iff]
    rintro ⟨h, _⟩; exact hx h

theorem cN_val {U : Finset (Fin N)} {v u : Fin N} : (u : ℕ) ∈ cN G U v ↔ u ∈ comp G U v := by
  rw [mem_cN]; exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨v.2, u.2, h⟩⟩

theorem cN_subset {U : Finset (Fin N)} {x : ℕ} : cN G U x ⊆ UN U := fun y hy => by
  obtain ⟨hx, hy, h⟩ := mem_cN.1 hy
  exact mem_UN.2 ⟨hy, comp_subset _ _ h⟩

theorem self_mem_cN {U : Finset (Fin N)} {x : ℕ} (hx : x ∈ UN U) : x ∈ cN G U x := by
  obtain ⟨h, hx⟩ := mem_UN.1 hx
  exact mem_cN.2 ⟨h, h, mem_comp_self hx⟩

theorem cN_symm {U : Finset (Fin N)} {x y : ℕ} (hx : x ∈ UN U) (hy : y ∈ cN G U x) :
    x ∈ cN G U y := by
  obtain ⟨h1, h2, h⟩ := mem_cN.1 hy
  obtain ⟨_, hxU⟩ := mem_UN.1 hx
  exact mem_cN.2 ⟨h2, h1, comp_symm hxU h⟩

theorem cN_eq {U : Finset (Fin N)} {x y : ℕ} (hy : y ∈ cN G U x) : cN G U y = cN G U x := by
  obtain ⟨h1, h2, h⟩ := mem_cN.1 hy
  unfold cN
  simp only [h1, h2, ↓reduceDIte, comp_eq_comp h]

theorem cN_adj {U : Finset (Fin N)} {s x y : ℕ} (hx : x ∈ cN G U s) (hy : y ∈ UN U)
    (h : adjN G x y) : y ∈ cN G U s := by
  obtain ⟨h1, h2, hc⟩ := mem_cN.1 hx
  obtain ⟨hy', hyU⟩ := mem_UN.1 hy
  obtain ⟨_, _, ha⟩ := h
  exact mem_cN.2 ⟨h1, hy', mem_comp_of_adj hc hyU ha⟩

theorem sum_cN (U : Finset (Fin N)) (w : Fin N → ℕ) (v : Fin N) :
    ∑ y ∈ cN G U v, SepProg.wI w y = ∑ y ∈ comp G U v, w y := by
  unfold cN
  simp only [v.2, ↓reduceDIte]
  rw [sum_map]
  refine sum_congr rfl fun y _ => ?_
  simp [SepProg.wI]

/-! ### The darts of a vertex -/

/-- The head of the dart `g` is adjacent to its tail. -/
theorem adjN_head {x g : ℕ} (hx : x < N) (h1 : gofs G x ≤ g) (h2 : g < gofs G (x + 1)) :
    tlG G (rvG G g) < N ∧ adjN G x (tlG G (rvG G g)) := by
  have hg : g < nD G := lt_of_lt_of_le h2 (gofs_le G _)
  obtain ⟨d, rfl⟩ := exists_dart_of_lt G hg
  have e1 := (ofs_le_iff G d _).1 h1
  have e2 := (ofs_lt_iff G d _).1 h2
  have hf : (d.fst : ℕ) = x := by omega
  rw [rvG_dartNum, tlG_dartNum]
  refine ⟨d.snd.2, hx, d.snd.2, ?_⟩
  have : d.fst = ⟨x, hx⟩ := Fin.ext hf
  rw [← this]
  exact d.adj

/-- Every neighbour is the head of a dart of the vertex. -/
theorem exists_dart_adjN {x y : ℕ} (h : adjN G x y) :
    ∃ g, gofs G x ≤ g ∧ g < gofs G (x + 1) ∧ tlG G (rvG G g) = y := by
  obtain ⟨hx, hy, ha⟩ := h
  let d : G.Dart := ⟨(⟨x, hx⟩, ⟨y, hy⟩), ha⟩
  refine ⟨dartNum G d, (ofs_le_iff G d _).2 le_rfl, (ofs_lt_iff G d _).2 (Nat.lt_succ_self _), ?_⟩
  rw [rvG_dartNum, tlG_dartNum]
  rfl

theorem lv_mem_UN (U : Finset (Fin N)) {l : ℕ} (hl : l < #U) : lv U l ∈ UN U := by
  rw [← ul_length] at hl
  rw [lv_ul U hl, val_mem_UN]
  exact ul_mem U hl

omit [DecidableRel G.Adj] in
/-- A sum over an injective enumeration of a set of numbers. -/
theorem sum_range_eqN {t : ℕ} (Q : ℕ → ℕ) (S : Finset ℕ) (hin : ∀ j < t, Q j ∈ S)
    (hinj : ∀ i < t, ∀ j < t, Q i = Q j → i = j) (hsurj : ∀ x ∈ S, ∃ j < t, Q j = x)
    (f : ℕ → ℕ) : ∑ j ∈ range t, f (Q j) = ∑ x ∈ S, f x := by
  rw [← sum_image (fun i hi j hj h => hinj i (mem_range.1 hi) j (mem_range.1 hj) h)]
  congr 1
  ext a
  simp only [mem_image, mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact hin j hj
  · intro ha; exact hsurj a ha

omit [DecidableRel G.Adj] in
theorem sum_range_leN {t : ℕ} (Q : ℕ → ℕ) (S : Finset ℕ) (hin : ∀ j < t, Q j ∈ S)
    (hinj : ∀ i < t, ∀ j < t, Q i = Q j → i = j) (f : ℕ → ℕ) :
    ∑ j ∈ range t, f (Q j) ≤ ∑ x ∈ S, f x := by
  rw [← sum_image (fun i hi j hj h => hinj i (mem_range.1 hi) j (mem_range.1 hj) h)]
  refine sum_le_sum_of_subset_of_nonneg (fun a ha => ?_) fun _ _ _ => Nat.zero_le _
  obtain ⟨j, hj, rfl⟩ := mem_image.1 ha
  exact hin j (mem_range.1 hj)

/-! ### The labelling along the list of `U` -/

variable (G) in
/-- **The labels after the first `i` vertices of the list of `U`**: `0` off `U`; `1` on the
vertices whose component contains none of the first `i` vertices; otherwise a label in
`[2, nc + 1]`, the same exactly on a component, with the weight of the component in `cw`. -/
structure BInv (U : Finset (Fin N)) (w : Fin N → ℕ) (i nc : ℕ) (lab cw : ℕ → ℕ) : Prop where
  out : ∀ x < N, x ∉ UN U → lab x = 0
  one : ∀ x ∈ UN U, lab x = 1 ↔ ∀ l < i, l < #U → lv U l ∉ cN G U x
  rng : ∀ x ∈ UN U, lab x ≠ 1 → 2 ≤ lab x ∧ lab x ≤ nc + 1
  same : ∀ x ∈ UN U, ∀ y ∈ UN U, 2 ≤ lab x → (lab y = lab x ↔ y ∈ cN G U x)
  wt : ∀ x ∈ UN U, 2 ≤ lab x → cw (lab x - 1) = ∑ y ∈ cN G U x, SepProg.wI w y
  cz : ∀ j ≤ N, (j = 0 ∨ nc < j) → cw j = 0
  surj : ∀ j, 1 ≤ j → j ≤ nc → ∃ x ∈ UN U, lab x = j + 1
  ncle : nc ≤ i

theorem BInv.init (U : Finset (Fin N)) (w : Fin N → ℕ) {lab cw : ℕ → ℕ}
    (hl1 : ∀ x ∈ UN U, lab x = 1) (hl0 : ∀ x < N, x ∉ UN U → lab x = 0)
    (hc : ∀ j ≤ N, cw j = 0) : BInv G U w 0 0 lab cw where
  out := hl0
  one x hx := by rw [hl1 x hx]; simp
  rng x hx h := absurd (hl1 x hx) h
  same x hx y hy h := by rw [hl1 x hx] at h; omega
  wt x hx h := by rw [hl1 x hx] at h; omega
  cz j hj _ := hc j hj
  surj j h1 h2 := by omega
  ncle := le_rfl

variable {U : Finset (Fin N)} {w : Fin N → ℕ} {i nc : ℕ} {lab cw : ℕ → ℕ}

theorem BInv.skip (hB : BInv G U w i nc lab cw) (hi : i < #U) (h : lab (lv U i) ≠ 1) :
    BInv G U w (i + 1) nc lab cw where
  out := hB.out
  one x hx := by
    rw [hB.one x hx]
    constructor
    · intro H l hl hlU hmem
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact H l hl hlU hmem
      · have hs := lv_mem_UN U hi
        have h2 := (hB.rng _ hs h).1
        have hxs : x ∈ cN G U (lv U l) := cN_symm hx hmem
        have := (hB.same _ hs x hx h2).2 hxs
        have hx1 := (hB.one x hx).2 H
        omega
    · intro H l hl hlU
      exact H l (by omega) hlU
  rng := hB.rng
  same := hB.same
  wt := hB.wt
  cz := hB.cz
  surj := hB.surj
  ncle := by have := hB.ncle; omega

theorem BInv.congr (hB : BInv G U w i nc lab cw) {lab' cw' : ℕ → ℕ}
    (hl : ∀ x < N, lab' x = lab x) (hc : ∀ j, cw' j = cw j) : BInv G U w i nc lab' cw' where
  out x hx h := by rw [hl x hx]; exact hB.out x hx h
  one x hx := by rw [hl x (lt_of_mem_UN hx)]; exact hB.one x hx
  rng x hx := by rw [hl x (lt_of_mem_UN hx)]; exact hB.rng x hx
  same x hx y hy := by
    rw [hl x (lt_of_mem_UN hx), hl y (lt_of_mem_UN hy)]; exact hB.same x hx y hy
  wt x hx := by rw [hl x (lt_of_mem_UN hx), hc]; exact hB.wt x hx
  cz j hj h := by rw [hc]; exact hB.cz j hj h
  surj j h1 h2 := by
    obtain ⟨x, hx, e⟩ := hB.surj j h1 h2
    exact ⟨x, hx, by rw [hl x (lt_of_mem_UN hx)]; exact e⟩
  ncle := hB.ncle

theorem BInv.final (hB : BInv G U w #U nc lab cw) {x : ℕ} (hx : x ∈ UN U) : 2 ≤ lab x := by
  have h : lab x ≠ 1 := by
    intro h1
    obtain ⟨hxN, hxU⟩ := mem_UN.1 hx
    obtain ⟨l, hl, he⟩ := exists_ul U hxU
    have hl' : l < #U := by rw [← ul_length]; exact hl
    refine (hB.one x hx).1 h1 l hl' hl' ?_
    rw [lv_ul U hl, he]
    exact self_mem_cN hx
  exact (hB.rng x hx h).1

/-! ### One search -/

variable (G) in
/-- **The search from the seed `s` with the label `c`**: only labels `1` changed, to `c`; the
queue `Q 0, …, Q (t - 1)` (starting at `s`, injective) lists the vertices labelled `c`, which
lie in the component of `s`. -/
structure BCore (U : Finset (Fin N)) (s c : ℕ) (lab₀ lab Q : ℕ → ℕ) (t : ℕ) : Prop where
  seed : 0 < t ∧ Q 0 = s
  chg : ∀ x < N, lab x ≠ lab₀ x → lab₀ x = 1 ∧ lab x = c
  qin : ∀ j < t, Q j ∈ cN G U s ∧ lab (Q j) = c
  qall : ∀ x < N, lab x = c → ∃ j < t, Q j = x
  inj : ∀ i < t, ∀ j < t, Q i = Q j → i = j

variable (G) in
/-- The first `h` vertices of the queue have all their neighbours in `U` labelled `c`. -/
def Proc (U : Finset (Fin N)) (c h : ℕ) (lab Q : ℕ → ℕ) : Prop :=
  ∀ j < h, ∀ y ∈ UN U, adjN G (Q j) y → lab y = c

variable (G) in
/-- The heads in `U` of the darts of `x` below `g` are labelled `c`. -/
def Part (U : Finset (Fin N)) (c x g : ℕ) (lab : ℕ → ℕ) : Prop :=
  ∀ g', gofs G x ≤ g' → g' < g → tlG G (rvG G g') ∈ UN U → lab (tlG G (rvG G g')) = c

variable {s c t h : ℕ} {lab₀ Q : ℕ → ℕ}

theorem BCore.lt_N (hC : BCore G U s c lab₀ lab Q t) {j : ℕ} (hj : j < t) : Q j < N :=
  lt_of_mem_UN (cN_subset (hC.qin j hj).1)

theorem BCore.t_le (hC : BCore G U s c lab₀ lab Q t) : t ≤ #(cN G U s) := by
  have := sum_range_leN Q (cN G U s) (fun j hj => (hC.qin j hj).1) hC.inj (fun _ => 1)
  simpa using this

theorem BCore.sum_le (hC : BCore G U s c lab₀ lab Q t) {h : ℕ} (hh : h ≤ t) (f : ℕ → ℕ) :
    ∑ j ∈ range h, f (Q j) ≤ ∑ x ∈ cN G U s, f x :=
  sum_range_leN Q (cN G U s) (fun j hj => (hC.qin j (by omega)).1)
    (fun i hi j hj => hC.inj i (by omega) j (by omega)) f

theorem BCore.start (hs : s ∈ UN U) {lab : ℕ → ℕ} (hls : lab s = c)
    (hlo : ∀ x < N, x ≠ s → lab x = lab₀ x) (hs1 : lab₀ s = 1) (hQ : Q 0 = s)
    (hc : ∀ x < N, lab₀ x ≠ c) :
    BCore G U s c lab₀ lab Q 1 where
  seed := ⟨Nat.one_pos, hQ⟩
  chg x _ hx := by
    by_cases e : x = s
    · subst e; exact ⟨hs1, hls⟩
    · exact absurd (hlo x ‹_› e) hx
  qin j hj := by
    obtain rfl : j = 0 := by omega
    rw [hQ]; exact ⟨self_mem_cN hs, hls⟩
  qall x _ hx := by
    by_cases e : x = s
    · exact ⟨0, Nat.one_pos, by rw [hQ, e]⟩
    · exact absurd (by rw [← hlo x ‹_› e]; exact hx) (hc x ‹_›)
  inj i hi j hj _ := by omega

theorem BInv.ne_c (hB : BInv G U w i nc lab₀ cw) {x : ℕ} (hx : x < N) : lab₀ x ≠ nc + 2 := by
  by_cases hxU : x ∈ UN U
  · by_cases h1 : lab₀ x = 1
    · omega
    · have := (hB.rng x hxU h1).2; omega
  · rw [hB.out x hx hxU]; omega

theorem BInv.mem_of_one (hB : BInv G U w i nc lab₀ cw) {x : ℕ} (hx : x < N) (h : lab₀ x = 1) :
    x ∈ UN U := by
  by_contra hxU
  rw [hB.out x hx hxU] at h
  omega

/-- A vertex labelled `1` at the start of the search from `s`, in the component of `s`. -/
theorem BInv.one_of_cN (hB : BInv G U w i nc lab₀ cw) (hs : s ∈ UN U) (hs1 : lab₀ s = 1)
    {y : ℕ} (hy : y ∈ cN G U s) : lab₀ y = 1 := by
  have hyU := cN_subset hy
  by_contra h1
  have h2 := (hB.rng y hyU h1).1
  have := (hB.same y hyU s hs h2).2 (cN_symm hs hy)
  omega

omit [DecidableRel G.Adj] in
theorem lab_c_upd {lab' : ℕ → ℕ} {z : ℕ}
    (hz : lab' z = c) (ho : ∀ y < N, y ≠ z → lab' y = lab y) {y : ℕ} (hyN : y < N)
    (hy : lab y = c) : lab' y = c := by
  by_cases e : y = z
  · rw [e, hz]
  · rw [ho y hyN e, hy]

/-- **A new vertex**: the head `z` of a dart of the current vertex `Q h`, labelled `1`, gets the
label `c` and goes to the end of the queue. -/
theorem BCore.visit_new (hB : BInv G U w i nc lab₀ cw) (hcdef : c = nc + 2)
    (hC : BCore G U s c lab₀ lab Q t) (hP : Proc G U c h lab Q) (hht : h < t)
    {g : ℕ} (hpart : Part G U c (Q h) g lab) (hg1 : gofs G (Q h) ≤ g)
    (hg2 : g < gofs G (Q h + 1)) (hz1 : lab (tlG G (rvG G g)) = 1)
    {lab' Q' : ℕ → ℕ} (hz : lab' (tlG G (rvG G g)) = c)
    (ho : ∀ y < N, y ≠ tlG G (rvG G g) → lab' y = lab y) (hQt : Q' t = tlG G (rvG G g))
    (hQo : ∀ j < t, Q' j = Q j) :
    BCore G U s c lab₀ lab' Q' (t + 1) ∧ Proc G U c h lab' Q' ∧
      Part G U c (Q' h) (g + 1) lab' ∧ t < #(cN G U s) := by
  set z := tlG G (rvG G g)
  have hxN := hC.lt_N hht
  obtain ⟨hzN, hadj⟩ := adjN_head (G := G) hxN hg1 hg2
  have hc1 : c ≠ 1 := by omega
  have hz0 : lab₀ z = 1 := by
    by_contra hne
    have := (hC.chg z hzN (by rw [hz1]; exact Ne.symm hne)).2
    omega
  have hzU := hB.mem_of_one hzN hz0
  have hzs : z ∈ cN G U s := cN_adj (hC.qin h hht).1 hzU hadj
  have hQz : ∀ j < t, Q j ≠ z := fun j hj e => by
    have := (hC.qin j hj).2; rw [e, hz1] at this; omega
  have hC' : BCore G U s c lab₀ lab' Q' (t + 1) := {
    seed := ⟨Nat.succ_pos _, by rw [hQo 0 hC.seed.1]; exact hC.seed.2⟩
    chg := fun x hx hne => by
      by_cases e : x = z
      · rw [e]; exact ⟨hz0, hz⟩
      · rw [ho x hx e] at hne ⊢; exact hC.chg x hx hne
    qin := fun j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hQo j hj]; exact ⟨(hC.qin j hj).1, lab_c_upd hz ho (hC.lt_N hj) (hC.qin j hj).2⟩
      · rw [hQt]; exact ⟨hzs, hz⟩
    qall := fun x hx hl => by
      by_cases e : x = z
      · exact ⟨t, Nat.lt_succ_self _, by rw [hQt, e]⟩
      · rw [ho x hx e] at hl
        obtain ⟨j, hj, hjx⟩ := hC.qall x hx hl
        exact ⟨j, by omega, by rw [hQo j hj, hjx]⟩
    inj := fun a ha b hb e => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
      · rw [hQo a ha, hQo b hb] at e; exact hC.inj a ha b hb e
      · rw [hQo a ha, hQt] at e; exact absurd e (hQz a ha)
      · rw [hQo b hb, hQt] at e; exact absurd e.symm (hQz b hb)
      · rfl }
  refine ⟨hC', fun j hj y hy ha => ?_, fun g' h1 h2 hU => ?_, ?_⟩
  · rw [hQo j (by omega)] at ha
    exact lab_c_upd hz ho (lt_of_mem_UN hy) (hP j hj y hy ha)
  · rw [hQo h hht] at h1
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
    · exact lab_c_upd hz ho (lt_of_mem_UN hU) (hpart g' h1 h2 hU)
    · exact hz
  · have := hC'.t_le; omega

/-- **A vertex already labelled** (not `1`): nothing changes. -/
theorem BCore.visit_old (hB : BInv G U w i nc lab₀ cw) (hs : s ∈ UN U)
    (hs1 : lab₀ s = 1) (hC : BCore G U s c lab₀ lab Q t) (hht : h < t)
    {g : ℕ} (hpart : Part G U c (Q h) g lab) (hg1 : gofs G (Q h) ≤ g)
    (hg2 : g < gofs G (Q h + 1)) (hz1 : lab (tlG G (rvG G g)) ≠ 1) :
    Part G U c (Q h) (g + 1) lab := by
  intro g' h1 h2 hU
  rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
  · exact hpart g' h1 h2 hU
  set z := tlG G (rvG G g')
  obtain ⟨hzN, hadj⟩ := adjN_head (G := G) (hC.lt_N hht) hg1 hg2
  by_contra hne
  have he : lab z = lab₀ z := by
    by_contra e; exact hne (hC.chg z hzN e).2
  have hzs : z ∈ cN G U s := cN_adj (hC.qin h hht).1 hU hadj
  have := hB.one_of_cN hs hs1 hzs
  rw [← he] at this
  exact hz1 this

/-- **The end of the darts of the current vertex.** -/
theorem Proc.succ (hP : Proc G U c h lab Q) (hpart : Part G U c (Q h) (gofs G (Q h + 1)) lab) :
    Proc G U c (h + 1) lab Q := by
  intro j hj y hy ha
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · exact hP j hj y hy ha
  obtain ⟨g, h1, h2, rfl⟩ := exists_dart_adjN ha
  exact hpart g h1 h2 hy

/-- **The end of the search**: the vertices labelled `c` are the component of `s`. -/
theorem BCore.lab_iff (hC : BCore G U s c lab₀ lab Q t) (hP : Proc G U c t lab Q) {y : ℕ}
    (hy : y < N) : lab y = c ↔ y ∈ cN G U s := by
  constructor
  · intro hl
    obtain ⟨j, hj, rfl⟩ := hC.qall y hy hl
    exact (hC.qin j hj).1
  · intro hys
    obtain ⟨hsN, hyN, hc⟩ := mem_cN.1 hys
    have key : ∀ v : Fin N, Relation.ReflTransGen (AdjIn G U) ⟨s, hsN⟩ v → lab v = c := by
      intro v hv
      induction hv with
      | refl =>
        have := (hC.qin 0 hC.seed.1).2; rw [hC.seed.2] at this; exact this
      | @tail a b _ hab ih =>
        obtain ⟨j, hj, hja⟩ := hC.qall a a.2 ih
        exact hP j hj b (val_mem_UN.2 hab.2.2) ⟨by rw [hja]; exact a.2, b.2, by
          simp only [hja]; exact hab.1⟩
    exact key _ (mem_comp.1 hc).2

/-- **The labelling after the search** from the `i`-th vertex of `U`, labelled `nc + 2`. -/
theorem BCore.finish (hB : BInv G U w i nc lab₀ cw) (hcdef : c = nc + 2) (hi : i < #U)
    (hsdef : s = lv U i) (hC : BCore G U s c lab₀ lab Q t)
    (hP : Proc G U c t lab Q) {cw' : ℕ → ℕ}
    (hcw : cw' (nc + 1) = ∑ j ∈ range t, SepProg.wI w (Q j))
    (hco : ∀ j, j ≠ nc + 1 → cw' j = cw j) : BInv G U w (i + 1) (nc + 1) lab cw' := by
  have hs : s ∈ UN U := hsdef ▸ lv_mem_UN U hi
  have hc1 : c ≠ 1 := by omega
  have hiff := fun y hy => hC.lab_iff hP (y := y) hy
  have unch : ∀ x < N, lab x ≠ c → lab x = lab₀ x := fun x hx h => by
    by_contra e; exact h (hC.chg x hx e).2
  exact {
    out := fun x hx hxU => by
      rw [unch x hx (fun h => hxU (cN_subset ((hiff x hx).1 h)))]; exact hB.out x hx hxU
    one := fun x hx => by
      have hxN := lt_of_mem_UN hx
      constructor
      · intro h1 l hl hlU hmem
        have e := unch x hxN (by omega)
        rw [h1] at e
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
        · exact (hB.one x hx).1 e.symm l hl hlU hmem
        · rw [← hsdef] at hmem
          have := (hiff x hxN).2 (cN_symm hx hmem)
          omega
      · intro H
        have h0 : lab₀ x = 1 := (hB.one x hx).2 fun l hl hlU => H l (by omega) hlU
        have hns : x ∉ cN G U s := fun hm => H i (Nat.lt_succ_self _) hi
          (by rw [← hsdef]; exact cN_symm hs hm)
        rw [unch x hxN (fun h => hns ((hiff x hxN).1 h)), h0]
    rng := fun x hx h1 => by
      have hxN := lt_of_mem_UN hx
      by_cases e : lab x = c
      · omega
      · rw [unch x hxN e] at h1 ⊢
        have := hB.rng x hx h1; omega
    same := fun x hx y hy h2 => by
      have hxN := lt_of_mem_UN hx
      have hyN := lt_of_mem_UN hy
      by_cases e : lab x = c
      · have hxs := (hiff x hxN).1 e
        rw [e, hiff y hyN, cN_eq hxs]
      · have ex := unch x hxN e
        rw [ex] at h2 ⊢
        constructor
        · intro hl
          have ey : lab y ≠ c := fun h => e (by rw [← h, hl, ex])
          rw [unch y hyN ey] at hl
          exact (hB.same x hx y hy h2).1 hl
        · intro hm
          have h0 := (hB.same x hx y hy h2).2 hm
          by_cases ey : lab y = c
          · have := (hC.chg y hyN (by rw [ey, h0, ← ex]; exact Ne.symm e)).1
            omega
          · rw [unch y hyN ey, h0]
    wt := fun x hx h2 => by
      have hxN := lt_of_mem_UN hx
      by_cases e : lab x = c
      · have hxs := (hiff x hxN).1 e
        rw [e, hcdef, show nc + 2 - 1 = nc + 1 by omega, hcw, cN_eq hxs]
        exact sum_range_eqN Q (cN G U s) (fun j hj => (hC.qin j hj).1) hC.inj
          (fun y hy => hC.qall y (lt_of_mem_UN (cN_subset hy)) ((hiff y (lt_of_mem_UN (cN_subset hy))).2 hy)) _
      · rw [unch x hxN e] at h2 ⊢
        have := (hB.rng x hx (by omega)).2
        rw [hco _ (by omega)]
        exact hB.wt x hx h2
    cz := fun j hj h => by
      rw [hco j (by omega)]; exact hB.cz j hj (by omega)
    surj := fun j h1 h2 => by
      by_cases hj : j ≤ nc
      · obtain ⟨x, hx, hl⟩ := hB.surj j h1 hj
        have hxN := lt_of_mem_UN hx
        refine ⟨x, hx, ?_⟩
        have hne : lab x ≠ c := fun h => by
          have := (hC.chg x hxN (by rw [h, hl]; omega)).1; omega
        rw [unch x hxN hne, hl]
      · obtain rfl : j = nc + 1 := by omega
        exact ⟨s, hs, by rw [(hiff s (lt_of_mem_UN hs)).2 (self_mem_cN hs)]; omega⟩
    ncle := by have := hB.ncle; omega }

/-- The vertices still labelled `1` after the search lose exactly the component of `s`. -/
theorem BCore.sum_one (hB : BInv G U w i nc lab₀ cw) (hcdef : c = nc + 2) (hs : s ∈ UN U)
    (hs1 : lab₀ s = 1) (hC : BCore G U s c lab₀ lab Q t) (hP : Proc G U c t lab Q)
    (f : ℕ → ℕ) :
    ∑ x ∈ (UN U).filter (fun x => lab₀ x = 1), f x =
      ∑ x ∈ (UN U).filter (fun x => lab x = 1), f x + ∑ x ∈ cN G U s, f x := by
  have hc1 : c ≠ 1 := by omega
  have hsub : cN G U s ⊆ (UN U).filter (fun x => lab₀ x = 1) := fun y hy =>
    mem_filter.2 ⟨cN_subset hy, hB.one_of_cN hs hs1 hy⟩
  have heq : (UN U).filter (fun x => lab x = 1) =
      (UN U).filter (fun x => lab₀ x = 1) \ cN G U s := by
    ext x
    simp only [mem_filter, mem_sdiff]
    constructor
    · rintro ⟨hx, h1⟩
      have hxN := lt_of_mem_UN hx
      have e : lab x = lab₀ x := by
        by_contra e; have := (hC.chg x hxN e).2; omega
      refine ⟨⟨hx, by rw [← e, h1]⟩, fun hm => ?_⟩
      have := (hC.lab_iff hP hxN).2 hm; omega
    · rintro ⟨⟨hx, h1⟩, hm⟩
      have hxN := lt_of_mem_UN hx
      refine ⟨hx, ?_⟩
      have hlc : lab x ≠ c := fun h => hm ((hC.lab_iff hP hxN).1 h)
      by_contra e
      exact hlc (hC.chg x hxN (by rw [h1]; exact e)).2
  rw [heq, sum_sdiff hsub]

end Piece

end PlanarSeparator
