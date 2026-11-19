module

public import PlanarFlow.NegSSSP.SepGlue
public import PlanarFlow.BKMNW.MachCost

/-!
# The decomposition by simple cycles from an explicit split function

The decomposition `PlanarFlow.NegSSSP.negDecF` used by the recursion for negative lengths is
chosen by `Classical.choose` among the decompositions meeting `NTree.FDec`. Here the
decomposition is built from an explicit split function, the choices of the machine, so that a
realization of the split of a piece is a realization at a node of the decomposition used.

* `CutOK N K A₀`: the conclusion of `exists_cycle_cut` for the cut `A₀`, `K \ A₀` of a component
  `K`; `CutsOK N cut`: `cut K` meets it on every connected piece of kept darts. Miller's program
  gives such a cut (`sep_run_cutOK`: the darts of `K` marked `1` by `sepRun prog`), and so does
  the existence proof (`cutC`, `cutsOK_cutC`).
* `grp`: **the grouping of the components** by one scan of the darts in a given order: the
  components are added to the first group while it has at most a quarter of the darts; the first
  component that makes it larger ends the scan, the group with it if it then has at most three
  quarters, that component alone otherwise (`grp_spec`, `splitF_grp`).
* `splitM N ord cut P`: **the split of the machine**: if a component (`pcomp`) of the piece has
  more than three quarters of the darts (the first such dart in the list `ord P`, the order of
  the darts of the piece on the machine), it is cut by `cut`, the rest of the piece joined to the
  smaller part (`cutPair`, `splitF_cutPair`); otherwise the components are grouped by `grp` in
  the order `ord P`. `splitM_splitF`: it meets `SplitF` on every
  piece of more than `10⁶` kept darts, for a cut function meeting `CutsOK` (on a plane map with
  transitive rotations and faces, `cutC` does, and so do the marks of Miller's program);
  `splitM_big`: in the large case the split does not depend on the dart found.
* `decM split n P`, `negDecM N ord cut`: **the decomposition of the split function** (`n` rounds,
  a node only where the split covers the piece); `negDecM_fDec`: it meets `NTree.FDec`;
  `piece_negDecM`: its piece is the set of kept darts on every map.
* `negSSSPDecM`, `negSSSPDecM_potOut`, `negSSSPDecM_spec_dual`: the recursion on it, correct on
  every map; `negDecMCost_le`: its counted cost is `O(n log² n)` (from `negCost_le_fsq`, which
  holds for every tree meeting `NTree.FDec`: `fdecCost_le`); `negDecMCost_mach`: with the machine
  costs `cNegMach C` it is at most `cMach.negsssp n`, as for `negDecF`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap Relation BKMNW

section Split

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {N : CombMap D V F}

/-! ### Cuts of a component -/

variable (N) in
/-- **A cut of a component meeting the conclusion of `exists_cycle_cut`**: `A₀ ⊆ K` and `K \ A₀`
have at most `(2 #K + 12 c) / 3` darts each for some `c ≤ 6 √(12 #K) + 4`, at most `c` shared
vertices, which for each part, with any rest sharing no vertex with `K`, lie on one face of `c`
darts of a plane map of at most `18 #K` vertices, faces and darts (`OneFace`). -/
def CutOK (K A₀ : Finset D) : Prop :=
  A₀ ⊆ K ∧ ∃ c, c ≤ 6 * Nat.sqrt (12 * K.card) + 4 ∧
    3 * A₀.card ≤ 2 * K.card + 12 * c ∧ 3 * (K \ A₀).card ≤ 2 * K.card + 12 * c ∧
    (bdry N A₀ (K \ A₀)).card ≤ c ∧
    ∀ R : Finset D, Disjoint (verts N R) (verts N K) →
      OneFace N (A₀ ∪ R) (bdry N A₀ (K \ A₀)) (18 * K.card) c ∧
      OneFace N ((K \ A₀) ∪ R) (bdry N A₀ (K \ A₀)) (18 * K.card) c

variable (N) in
/-- **A cut function meeting `CutOK` on every connected piece of kept darts.** -/
def CutsOK (cut : Finset D → Finset D) : Prop :=
  ∀ K ⊆ reps N, K.Nonempty → DConn N K → CutOK N K (cut K)

lemma eq_sdiff_of_union {K A₀ A₁ : Finset D} (hu : A₀ ∪ A₁ = K) (hd : Disjoint A₀ A₁) :
    A₁ = K \ A₀ := by
  rw [← hu, union_sdiff_left, sdiff_eq_self_of_disjoint hd.symm]

/-- The conclusion of `exists_cycle_cut` for two parts is `CutOK` for the first. -/
lemma cutOK_of {K A₀ A₁ : Finset D} {c : ℕ} (hu : A₀ ∪ A₁ = K) (hd : Disjoint A₀ A₁)
    (hc : c ≤ 6 * Nat.sqrt (12 * K.card) + 4)
    (h0 : 3 * A₀.card ≤ 2 * K.card + 12 * c) (h1 : 3 * A₁.card ≤ 2 * K.card + 12 * c)
    (hb : (bdry N A₀ A₁).card ≤ c)
    (hw : ∀ R : Finset D, Disjoint (verts N R) (verts N K) →
      OneFace N (A₀ ∪ R) (bdry N A₀ A₁) (18 * K.card) c ∧
      OneFace N (A₁ ∪ R) (bdry N A₀ A₁) (18 * K.card) c) : CutOK N K A₀ := by
  obtain rfl := eq_sdiff_of_union hu hd
  exact ⟨hu ▸ subset_union_left, c, hc, h0, h1, hb, hw⟩

variable (N) in
/-- **A cut by the existence proof** (`exists_cycle_cut`), `∅` where there is none. -/
noncomputable def cutC (K : Finset D) : Finset D := by
  classical exact if h : ∃ A₀, CutOK N K A₀ then h.choose else ∅

theorem cutsOK_cutC (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) :
    CutsOK N (cutC N) := by
  classical
  intro K hKr hK0 hK
  have hex : ∃ A₀, CutOK N K A₀ := by
    obtain ⟨A₀, A₁, c, hu, hd, hc, h0, h1, hb, hw⟩ := exists_cycle_cut hM hrot hface hKr hK0 hK
    exact ⟨A₀, cutOK_of hu hd hc h0 h1 hb hw⟩
  unfold cutC
  simp only [hex, ↓reduceDIte]
  exact hex.choose_spec

/-! ### The large component -/

/-- **The split by a cut `A₀` of a component `K` of `P`**: the rest `P \ K` joined to the smaller
of `A₀` and `K \ A₀`. -/
def cutPair (P K A₀ : Finset D) : Finset D × Finset D :=
  if A₀.card ≤ (K \ A₀).card then (A₀ ∪ (P \ K), K \ A₀) else (A₀, (K \ A₀) ∪ (P \ K))

/-- **The split of a piece by a cut of a large component meets `SplitF`.** -/
lemma splitF_cutPair {P K A₀ : Finset D} (hs : 1000000 < P.card) (hKP : K ⊆ P)
    (hRd : Disjoint (verts N (P \ K)) (verts N K)) (hbig : 3 * P.card / 4 < K.card)
    (hcut : CutOK N K A₀) : SplitF N P (cutPair P K A₀).1 (cutPair P K A₀).2 := by
  unfold cutPair
  obtain ⟨hA₀K, c, hc, h0, h1, hb, hw⟩ := hcut
  have hu : A₀ ∪ (K \ A₀) = K := union_sdiff_of_subset hA₀K
  have hd : Disjoint A₀ (K \ A₀) := disjoint_sdiff
  have hA₁K : K \ A₀ ⊆ K := sdiff_subset
  have hKR : K ∪ (P \ K) = P := union_sdiff_of_subset hKP
  have hRc : (P \ K).card + K.card = P.card := card_sdiff_add_card_eq_card hKP
  have hRK : Disjoint (P \ K) K := sdiff_disjoint
  generalize K \ A₀ = A₁ at *
  generalize P \ K = R at *
  have hK : K.card ≤ P.card := card_le_card hKP
  have hc' : c ≤ 6 * Nat.sqrt (12 * P.card) + 4 :=
    hc.trans (by have := Nat.sqrt_le_sqrt (Nat.mul_le_mul_left 12 hK); omega)
  have h48 := sqrt_cut_le hs
  have hsq := succ_sq_cut_le (by omega) hc'
  have hcard : A₀.card + A₁.card = K.card := by rw [← card_union_of_disjoint hd, hu]
  have hRA₀ : Disjoint R A₀ := hRK.mono_right (hu ▸ subset_union_left)
  have hRA₁ : Disjoint R A₁ := hRK.mono_right hA₁K
  have hv₀ : Disjoint (verts N R) (verts N A₀) :=
    hRd.mono_right (verts_mono (hu ▸ subset_union_left))
  have hv₁ : Disjoint (verts N R) (verts N A₁) := hRd.mono_right (verts_mono hA₁K)
  have hbP : (bdry N A₀ A₁).card ≤ P.card := by omega
  have hsq' : ((bdry N A₀ A₁).card + 1) ^ 2 ≤ 1200 * P.card :=
    (Nat.pow_le_pow_left (by omega) 2).trans hsq
  have hcsq : c ^ 2 ≤ 1200 * P.card := (Nat.pow_le_pow_left (by omega) 2).trans hsq
  obtain ⟨w₀, w₁⟩ := hw R hRd
  obtain ⟨w₀', w₁'⟩ := hw ∅ (by simp [verts])
  rw [union_empty] at w₀' w₁'
  split_ifs with hle <;> dsimp only
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [union_right_comm, hu, hKR]
    · exact disjoint_union_left.2 ⟨hd, hRA₁⟩
    · rw [card_union_of_disjoint hRA₀.symm]; omega
    · omega
    · rw [card_union_of_disjoint hRA₀.symm]; omega
    · omega
    · rwa [bdry_union_right hv₁]
    · rwa [bdry_union_right hv₁]
    · intro _
      rw [bdry_union_right hv₁]
      exact ⟨c, hcsq, w₀.mono (by omega), w₁'.mono (by omega)⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← union_assoc, hu, hKR]
    · exact disjoint_union_right.2 ⟨hd, hRA₀.symm⟩
    · omega
    · rw [card_union_of_disjoint hRA₁.symm]; omega
    · omega
    · rw [card_union_of_disjoint hRA₁.symm]; omega
    · rwa [bdry_comm, bdry_union_right hv₀, bdry_comm]
    · rwa [bdry_comm, bdry_union_right hv₀, bdry_comm]
    · intro _
      rw [bdry_comm, bdry_union_right hv₀, bdry_comm]
      exact ⟨c, hcsq, w₀'.mono (by omega), w₁.mono (by omega)⟩

/-! ### Grouping the components -/

variable (N) in
/-- **The grouping of the components of `P`** by a scan of the darts `ds`, from the group `acc`:
the component of the next dart is added while the group has at most a quarter of the darts of
`P`; the first component that makes it larger ends the scan, with the group if it then has at
most three quarters of the darts, alone otherwise. -/
noncomputable def grp (P : Finset D) (acc : Finset D) : List D → Finset D
  | [] => acc
  | d :: ds =>
    if 4 * (acc ∪ pcomp N P d).card ≤ P.card then grp P (acc ∪ pcomp N P d) ds
    else if 4 * (acc ∪ pcomp N P d).card ≤ 3 * P.card then acc ∪ pcomp N P d
    else pcomp N P d

variable (N) in
/-- A set of darts of `P` closed under the components of `P`. -/
def Closed (P G : Finset D) : Prop := ∀ d ∈ G, pcomp N P d ⊆ G

lemma closed_pcomp {P : Finset D} (x : D) : Closed N P (pcomp N P x) := fun _ hd =>
  (pcomp_eq hd).le

lemma Closed.union {P G H : Finset D} (hG : Closed N P G) (hH : Closed N P H) :
    Closed N P (G ∪ H) := fun d hd => by
  rcases mem_union.1 hd with h | h
  · exact (hG d h).trans subset_union_left
  · exact (hH d h).trans subset_union_right

/-- **A closed set of darts shares no vertex with the rest of the piece.** -/
lemma bdry_closed {P G : Finset D} (hGP : G ⊆ P) (hG : Closed N P G) :
    bdry N G (P \ G) = ∅ := by
  refine eq_empty_of_forall_notMem fun v hv => ?_
  obtain ⟨h0, h1⟩ := mem_inter.1 hv
  obtain ⟨d₀, hd₀, e₀⟩ := mem_verts_iff'.1 h0
  obtain ⟨d₁, hd₁, e₁⟩ := mem_verts_iff'.1 h1
  have := mem_pcomp_of_share (self_mem_pcomp (hGP hd₀)) (mem_sdiff.1 hd₁).1 (share_of e₀ e₁)
  exact (mem_sdiff.1 hd₁).2 (hG d₀ hd₀ this)

/-- **The grouping**: from a closed group of at most a quarter of the darts, scanning darts of
`P` covering the rest, with components of at most three quarters of the darts each, the group
found is closed and nonempty, and it and the rest have at most three quarters of the darts. -/
lemma grp_spec {P : Finset D} (hP : 0 < P.card)
    (hsmall : ∀ x ∈ P, (pcomp N P x).card ≤ 3 * P.card / 4) :
    ∀ (ds : List D) (acc : Finset D), acc ⊆ P → Closed N P acc → 4 * acc.card ≤ P.card →
      (∀ d ∈ ds, d ∈ P) → (∀ d ∈ P, d ∈ acc ∨ d ∈ ds) →
      grp N P acc ds ⊆ P ∧ Closed N P (grp N P acc ds) ∧ (grp N P acc ds).Nonempty ∧
        4 * (grp N P acc ds).card ≤ 3 * P.card ∧ 4 * (P \ grp N P acc ds).card ≤ 3 * P.card
  | [], acc, hacc, _, h4, _, hcov => by
    have : P ⊆ acc := fun d hd => by simpa using hcov d hd
    have := card_le_card this
    omega
  | d :: ds, acc, hacc, hcl, h4, hds, hcov => by
    have hdP : d ∈ P := hds d (List.mem_cons_self ..)
    simp only [grp]
    set X := pcomp N P d with hX
    have hXP : X ⊆ P := pcomp_subset P d
    have hXc : X.card ≤ 3 * P.card / 4 := hsmall d hdP
    have hdX : d ∈ X := self_mem_pcomp hdP
    have hU : acc ∪ X ⊆ P := union_subset hacc hXP
    have hUc : Closed N P (acc ∪ X) := hcl.union (closed_pcomp d)
    have hUle : (acc ∪ X).card ≤ acc.card + X.card := card_union_le _ _
    split_ifs with h1 h2
    · refine grp_spec hP hsmall ds (acc ∪ X) hU hUc h1
        (fun e he => hds e (List.mem_cons_of_mem _ he))
        fun e he => ?_
      rcases hcov e he with h | h
      · exact Or.inl (mem_union_left _ h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inl (mem_union_right _ hdX)
        · exact Or.inr h
    · have := card_sdiff_of_subset hU
      refine ⟨hU, hUc, ⟨d, mem_union_right _ hdX⟩, h2, ?_⟩
      omega
    · have := card_sdiff_of_subset hXP
      refine ⟨hXP, closed_pcomp d, ⟨d, hdX⟩, by omega, ?_⟩
      omega

/-- **The grouping of the components of a large piece meets `SplitF`**, when each component has
at most three quarters of the darts. -/
lemma splitF_grp {P : Finset D} (hs : 1000000 < P.card)
    (hsmall : ∀ x ∈ P, (pcomp N P x).card ≤ 3 * P.card / 4) {L : List D}
    (hL : ∀ d ∈ P, d ∈ L) :
    SplitF N P (grp N P ∅ (L.filter (· ∈ P))) (P \ grp N P ∅ (L.filter (· ∈ P))) := by
  obtain ⟨hGP, hGc, hG0, hG4, hR4⟩ := grp_spec (by omega) hsmall (L.filter (· ∈ P)) ∅
    (empty_subset _) (fun _ h => absurd h (notMem_empty _)) (by simp)
    (fun d hd => by simpa using (List.mem_filter.1 hd).2)
    (fun d hd => Or.inr (List.mem_filter.2 ⟨hL d hd, by simpa using hd⟩))
  set G := grp N P ∅ (L.filter (· ∈ P))
  have hbd := bdry_closed hGP hGc
  have hcs := card_sdiff_of_subset hGP
  refine ⟨union_sdiff_of_subset hGP, disjoint_sdiff, card_pos.2 hG0, ?_, by omega, hR4, ?_, ?_,
    ?_⟩
  · omega
  · rw [hbd, card_empty]; omega
  · rw [hbd, card_empty]; omega
  · rw [hbd]; exact fun h => absurd h not_nonempty_empty

/-! ### The split of the machine -/

/-- **An order of the darts of every piece**: `ord P` lists every dart of `P`. -/
def OrdOK (ord : Finset D → List D) : Prop := ∀ P : Finset D, ∀ d ∈ P, d ∈ ord P

variable (N) in
/-- The test for a dart of a component of more than three quarters of the darts of `P`. -/
noncomputable def bigP (P : Finset D) (x : D) : Bool := by
  classical exact decide (x ∈ P ∧ 3 * P.card / 4 < (pcomp N P x).card)

lemma bigP_iff {P : Finset D} {x : D} :
    bigP N P x = true ↔ x ∈ P ∧ 3 * P.card / 4 < (pcomp N P x).card := by
  classical
  unfold bigP; exact decide_eq_true_iff

variable (N) in
/-- **The split of the machine** of a piece `P`, scanning the darts in the order `ord P` (the
order of the darts of the piece on the machine): the first dart of a component of more than three
quarters of the darts, if there is one, and its component cut by `cut`, the rest joined to the
smaller part (`cutPair`); otherwise the components grouped by `grp` in the order `ord P`. -/
noncomputable def splitM (ord : Finset D → List D) (cut : Finset D → Finset D) (P : Finset D) :
    Finset D × Finset D :=
  match (ord P).find? (bigP N P) with
  | some x => cutPair P (pcomp N P x) (cut (pcomp N P x))
  | none => (grp N P ∅ ((ord P).filter (· ∈ P)), P \ grp N P ∅ ((ord P).filter (· ∈ P)))

/-- **The split of the machine meets `SplitF`** on every piece of more than `10⁶` kept darts, for
an order of the darts of every piece and a cut function meeting `CutsOK` (the plane hypotheses
enter only through the cuts). -/
theorem splitM_splitF {ord : Finset D → List D} (hL : OrdOK ord) {cut : Finset D → Finset D}
    (hcut : CutsOK N cut) {P : Finset D} (hPr : P ⊆ reps N) (hs : 1000000 < P.card) :
    SplitF N P (splitM N ord cut P).1 (splitM N ord cut P).2 := by
  unfold splitM
  rcases hf : (ord P).find? (bigP N P) with _ | x
  · simp only
    refine splitF_grp hs (fun x hx => ?_) (hL P)
    have := List.find?_eq_none.1 hf x (hL P x hx)
    rw [bigP_iff] at this
    push Not at this
    exact this hx
  · simp only
    obtain ⟨hx, hb⟩ := bigP_iff.1 (List.find?_some hf)
    have hKP := pcomp_subset (N := N) P x
    exact splitF_cutPair hs hKP (disjoint_verts_pcomp P x) hb
      (hcut _ (hKP.trans hPr) ⟨x, self_mem_pcomp hx⟩ pcomp_dconn)

/-- Two components of more than three quarters of the darts each are the same. -/
lemma pcomp_eq_of_big {P : Finset D} {x y : D} (hx : 3 * P.card / 4 < (pcomp N P x).card)
    (hy : 3 * P.card / 4 < (pcomp N P y).card) : pcomp N P x = pcomp N P y := by
  by_contra hne
  have hd : Disjoint (pcomp N P x) (pcomp N P y) := by
    refine disjoint_left.2 fun z hz hz' => hne ?_
    rw [← pcomp_eq hz, pcomp_eq hz']
  have := card_le_card (union_subset (pcomp_subset (N := N) P x) (pcomp_subset (N := N) P y))
  rw [card_union_of_disjoint hd] at this
  omega

/-- **In the large case the split of the machine does not depend on the dart found**: it is the
cut of the large component, for any dart of it. -/
theorem splitM_big {ord : Finset D → List D} (hL : OrdOK ord) (cut : Finset D → Finset D)
    {P : Finset D}
    {x : D} (hx : x ∈ P) (hb : 3 * P.card / 4 < (pcomp N P x).card) :
    splitM N ord cut P = cutPair P (pcomp N P x) (cut (pcomp N P x)) := by
  unfold splitM
  rcases hf : (ord P).find? (bigP N P) with _ | y
  · exact absurd (bigP_iff.2 ⟨hx, hb⟩) (by simpa using List.find?_eq_none.1 hf x (hL P x hx))
  · simp only
    rw [pcomp_eq_of_big (bigP_iff.1 (List.find?_some hf)).2 hb]

/-- **Without a large component the split of the machine is the grouping** in the order of
`ord P`. -/
theorem splitM_small {ord : Finset D → List D} (cut : Finset D → Finset D) {P : Finset D}
    (hsmall : ∀ x ∈ P, (pcomp N P x).card ≤ 3 * P.card / 4) :
    splitM N ord cut P =
      (grp N P ∅ ((ord P).filter (· ∈ P)), P \ grp N P ∅ ((ord P).filter (· ∈ P))) := by
  unfold splitM
  rcases hf : (ord P).find? (bigP N P) with _ | y
  · rfl
  · obtain ⟨hy, hb⟩ := bigP_iff.1 (List.find?_some hf)
    exact absurd (hsmall y hy) (by omega)

end Split

/-! ### The decomposition of a split function -/

section Dec

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {N : CombMap D V F}

/-- **The decomposition of a split function** in `n` rounds: a piece of more than `10⁶` darts
whose split covers it is a node over the decompositions of the two parts, every other piece a
leaf. -/
def decM (split : Finset D → Finset D × Finset D) : ℕ → Finset D → NTree D
  | 0, P => .leaf P
  | n + 1, P =>
    if 1000000 < P.card ∧ (split P).1 ∪ (split P).2 = P then
      .node (decM split n (split P).1) (decM split n (split P).2)
    else .leaf P

/-- **The piece of the decomposition of a split function** is the piece decomposed. -/
theorem piece_decM (split : Finset D → Finset D × Finset D) :
    ∀ (n : ℕ) (P : Finset D), (decM split n P).piece = P
  | 0, P => rfl
  | n + 1, P => by
    simp only [decM]
    split_ifs with h
    · simp only [NTree.piece, piece_decM split n, h.2]
    · rfl

/-- **The decomposition of a split function meeting `SplitF` on the large pieces of kept darts
meets `NTree.FDec`**, in `n ≥ #P` rounds. -/
theorem decM_fDec {split : Finset D → Finset D × Finset D}
    (hsplit : ∀ P ⊆ reps N, 1000000 < P.card → SplitF N P (split P).1 (split P).2) :
    ∀ (n : ℕ) (P : Finset D), P.card ≤ n → P ⊆ reps N → (decM split n P).FDec N
  | 0, P, hP, _ => by simp only [decM, NTree.FDec]; omega
  | n + 1, P, hP, hPr => by
    simp only [decM]
    split_ifs with h
    · have hs := hsplit P hPr h.1
      obtain ⟨hu, -, h0, h1, hc0, hc1, -⟩ := hs
      have hP₀ : (split P).1 ⊆ P := fun x hx => hu ▸ mem_union_left _ hx
      have hP₁ : (split P).2 ⊆ P := fun x hx => hu ▸ mem_union_right _ hx
      refine ⟨decM_fDec hsplit n _ (by omega) (hP₀.trans hPr),
        decM_fDec hsplit n _ (by omega) (hP₁.trans hPr), ?_⟩
      rw [piece_decM, piece_decM, hu]
      exact hsplit P hPr h.1
    · simp only [NTree.FDec]
      by_contra hc
      exact h ⟨by omega, (hsplit P hPr (by omega)).1⟩

variable (N) in
/-- **The decomposition of the machine**: the decomposition of the kept darts by the split of
the machine `splitM N ord cut` (darts of each piece `P` scanned in the order `ord P`, the large
components cut by
`cut`). -/
noncomputable def negDecM (ord : Finset D → List D) (cut : Finset D → Finset D) : NTree D :=
  decM (splitM N ord cut) (Fintype.card D) (reps N)

lemma piece_negDecM (ord : Finset D → List D) (cut : Finset D → Finset D) :
    (negDecM N ord cut).piece = reps N :=
  piece_decM _ _ _

/-- **The decomposition of the machine is by simple cycles, with the boundary on one face** at
every node (`NTree.FDec`), for an order of the darts of every piece and a cut function meeting
`CutsOK` (on a
plane map with transitive rotations and faces, `cutsOK_cutC`, `sep_run_cutOK`). -/
theorem negDecM_fDec {ord : Finset D → List D} (hL : OrdOK ord) {cut : Finset D → Finset D}
    (hcut : CutsOK N cut) :
    (negDecM N ord cut).FDec N :=
  decM_fDec (fun _ hPr hs => splitM_splitF hL hcut hPr hs) _ _ (card_le_univ _) subset_rfl

/-- **The nodes of the decomposition of the machine are splits of the machine**: every node of
`decM split n P` splits its piece by `split`. -/
theorem decM_node {split : Finset D → Finset D × Finset D} :
    ∀ {n : ℕ} {P : Finset D} {l r : NTree D}, decM split n P = .node l r →
      l = decM split (n - 1) (split P).1 ∧ r = decM split (n - 1) (split P).2 ∧
        1000000 < P.card ∧ (split P).1 ∪ (split P).2 = P
  | 0, P, l, r, h => by simp [decM] at h
  | n + 1, P, l, r, h => by
    simp only [decM] at h
    split_ifs at h with hc
    · cases h
      exact ⟨rfl, rfl, hc⟩

variable (N) in
/-- **Shortest paths with negative lengths** in the graph of `N`: the recursion through the
simple graph on the decomposition of the machine `negDecM N ord cut`. -/
noncomputable def negSSSPDecM (ord : Finset D → List D) (cut : Finset D → Finset D)
    (mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ)
    (bf : DDG V → DDG V → Option (V → ℤ))
    (fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V → (Option V → ℤ) →
      Option V → Option ℤ) (ℓ : D → ℤ) : Option (V → ℤ) :=
  negSSSPS N mssp bf fr (negDecM N ord cut) ℓ

/-- **Correctness of `negSSSPDecM`**, on every map, for every list and cut function. -/
theorem negSSSPDecM_potOut (ord : Finset D → List D) (cut : Finset D → Finset D)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}
    (hmssp : PieceMSSPSpec N mssp) {bf : DDG V → DDG V → Option (V → ℤ)} (hbf : BFDDGSpec bf)
    {fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V → (Option V → ℤ) →
      Option V → Option ℤ} (hfr : FRSpec fr) (ℓ : D → ℤ) :
    PotOut (N.graph ℓ) (negSSSPDecM N ord cut mssp bf fr ℓ) :=
  negSSSPS_potOut hmssp hbf hfr (piece_negDecM ord cut) ℓ

/-- **The recursion `negSSSPDecM` on the dual map meets `NegSSSPSpec`**, on every map. -/
theorem negSSSPDecM_spec_dual (M : CombMap D V F) (ord : Finset D → List D)
    (cut : Finset D → Finset D)
    {mssp : Finset D → (D → ℤ) → Finset F → F → F → Option ℤ}
    (hmssp : PieceMSSPSpec M.dual mssp) {bf : DDG F → DDG F → Option (F → ℤ)}
    (hbf : BFDDGSpec bf)
    {fr : DDG (Option F) → List (Option F × Option F × ℤ) → Option F → (Option F → ℤ) →
      Option F → Option ℤ} (hfr : FRSpec fr) :
    NegSSSPSpec M (negSSSPDecM M.dual ord cut mssp bf fr) := fun ℓ => by
  rw [← dual_graph]
  exact negSSSPOut_of_potOut (negSSSPDecM_potOut ord cut hmssp hbf hfr ℓ)

/-- **The cost of the recursion on any decomposition of the kept darts by simple cycles**: with
the linear bookkeeping of the simple graph, at most `10920 K n lg² n + (10⁶ + 1) K n`. -/
theorem fdecCost_le {c : NegCosts} {K : ℕ} (hc : c.Bounds K) {τ : NTree D}
    (hτ : τ.piece = reps N) (h : τ.FDec N) :
    c.lin (Fintype.card D) + negCost N c τ ≤
      10920 * K * Fintype.card D * lg (Fintype.card D) ^ 2 + 1000001 * K * Fintype.card D := by
  have h1 := hc.lin (Fintype.card D)
  have h2 := negCost_le_fsq hc h
  rw [hτ] at h2
  have hr : (reps N).card ≤ Fintype.card D := card_le_univ _
  have hl := lg_mono hr
  have h3 : 10920 * K * (reps N).card * lg (reps N).card ^ 2 ≤
      10920 * K * Fintype.card D * lg (Fintype.card D) ^ 2 := by gcongr
  have h4 : 1000000 * K * (reps N).card ≤ 1000000 * K * Fintype.card D := by gcongr
  nlinarith

variable (N) in
/-- **The counted cost of `negSSSPDecM`**: the simple graph and the recursion on
`negDecM N ord cut`. -/
noncomputable def negDecMCost (ord : Finset D → List D) (cut : Finset D → Finset D) (c : NegCosts) :
    ℕ :=
  c.lin (Fintype.card D) + negCost N c (negDecM N ord cut)

/-- **The cost of `negSSSPDecM` is `O(n log² n)`**, as for `negDecF`. -/
theorem negDecMCost_le {ord : Finset D → List D} (hL : OrdOK ord) {cut : Finset D → Finset D}
    (hcut : CutsOK N cut) {c : NegCosts} {K : ℕ}
    (hc : c.Bounds K) :
    negDecMCost N ord cut c ≤ 10920 * K * Fintype.card D * lg (Fintype.card D) ^ 2 +
      1000001 * K * Fintype.card D :=
  fdecCost_le hc (piece_negDecM ord cut) (negDecM_fDec hL hcut)

end Dec

section Mach

universe w

/-- **The counted cost of the recursion on the decomposition of the machine with the machine
costs**: on `n` darts, for an order of the darts of every piece and a cut function meeting
`CutsOK` on the dual,
at most `cMach.negsssp n` (as `negSSSPImpl_cost_mach` for `negDecF`). -/
theorem negDecMCost_mach (C C₀ : ℕ) {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] {M : CombMap D V F} {ord : Finset D → List D}
    (hL : OrdOK ord)
    {cut : Finset D → Finset D} (hcut : CutsOK M.dual cut) :
    negDecMCost M.dual ord cut (cNegMach C) ≤ (cMach C C₀).negsssp (Fintype.card D) :=
  negDecMCost_le hL hcut (cNegMach_bounds C)

end Mach

/-! ### The cut of Miller's program -/

section MillerCut

open PlanarSeparator PlanarSeparator.MillerProg WordRAM WordRAM.Machine

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {N : CombMap D V F}

variable (N) in
/-- **The darts of `K` marked `1`** by marks `f (c d)` on the darts of the piece map numbered
by `c`. -/
noncomputable def markSet (K : Finset D) {m : ℕ} (c : SDart (rcl N K) ≃ Fin m) (f : ℕ → ℕ) :
    Finset D := by
  classical exact K.filter fun d => ∃ h : d ∈ rcl N K, f (c ⟨d, h⟩) = 1

lemma mem_markSet {K : Finset D} {m : ℕ} {c : SDart (rcl N K) ≃ Fin m} {f : ℕ → ℕ} {d : D} :
    d ∈ markSet N K c f ↔ d ∈ K ∧ ∃ h : d ∈ rcl N K, f (c ⟨d, h⟩) = 1 := by
  classical
  unfold markSet; rw [mem_filter]

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The cut of Miller's program meets `CutOK`**: in the setting of `sep_run_split` (the plain
encoding of the piece map of a connected piece `K` of kept darts, any program `prog` of steps
1–10 meeting `Spec10`), the run of `sepRun prog` ends within the bound of `sep_run_split`, and the
darts of `K` it marks `1` at `B₀ + 22 m` form a cut of `K` meeting `CutOK`. A cut function giving
on each connected piece the marks of the run is therefore a cut function meeting `CutsOK`, and
the decomposition of the machine on it meets `NTree.FDec` (`negDecM_fDec`). -/
theorem sep_run_cutOK (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {K : Finset D} (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K)
    {m nV nF : ℕ} (c : SDart (rcl N K) ≃ Fin m) (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF) (hm1 : 1 ≤ m)
    {W : ℕ} {P : Input} {B₀ T : ℕ} {prog : WordRAM.Machine.Stmt} {c₀ : Config}
    (hE : Enc (kmap N K) c vn fn c₀.nmem B₀ (B₀ + m) (B₀ + 2 * m) (B₀ + 3 * m) (B₀ + 4 * m))
    (hfl : ∀ d, c₀.nmem (B₀ + 5 * m + c d) = flK N K d)
    (hB : aEnd (3 * m) (nV + nF + m) ≤ B₀) (hW : B₀ + 23 * m + nV + nF + 2 ≤ W)
    (hc : WordsBounded W c₀) (h390 : c₀.nreg 390 = m) (h391 : c₀.nreg 391 = nV)
    (h392 : c₀.nreg 392 = nF) (h393 : c₀.nreg 393 = B₀)
    (hX : Spec10 (kmap N K) c vn fn (flK N K) B₀ T prog P W) :
    ∃ c' t, Exec P W (sepRun prog) c₀ c' t ∧
      t ≤ 221 * m + 5 * (nV + nF) + 4 * Nat.log 2 (nV + nF + m) + 110 + T + 9 +
        (105 * m + 30) ∧
      CutOK N K (markSet N K c fun i => c'.nmem (B₀ + 22 * m + i)) := by
  obtain ⟨c', t, e, ht, Z, hmk, hu, hd, ℓ, hℓ, h0, h1, hb, hw⟩ :=
    sep_run_split hM hrot hface hKr hK0 hK c vn fn hm1 hE hfl hB hW hc h390 h391 h392 h393 hX
  refine ⟨c', t, e, ht, ?_⟩
  have hs : markSet N K c (fun i => c'.nmem (B₀ + 22 * m + i)) = side N K Z := by
    ext d
    rw [mem_markSet]
    constructor
    · rintro ⟨hdK, h, h1⟩
      exact (hmk d h hdK).2 h1
    · intro hd'
      have hdK := side_subset Z hd'
      have h := subset_rcl (N := N) K hdK
      exact ⟨hdK, h, (hmk d h hdK).1 hd'⟩
  rw [hs]
  exact cutOK_of hu hd hℓ h0 h1 hb hw

end MillerCut

end NegSSSP

end PlanarFlow
