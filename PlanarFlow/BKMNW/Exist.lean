module

public import PlanarFlow.BKMNW.MaxFlow

/-!
# Decompositions meeting `BalDecA`: the recursion

The cost theorems (`PlanarFlow.BKMNW.runL_isMax_costA`, `PlanarFlow.BKMNW.maxflow_tri_cost`)
assume a decomposition meeting `PlanarFlow.BKMNW.BalDecA`. This file reduces its existence to
the existence of **one split of a large piece** (`exists_balDecA_of_split`): everything else
(the recursion, the alternation of the article between splits balanced in size and splits
balanced in the number of holes, the bound `η = 6` on the holes touching a piece, the small
pieces and the leaves) is done here.

## The plan

Following Algorithm 1 of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J. Comput.
46(4), 2017) and Fakcharoenphol and Rao:

1. **The recursion** (`exists_decOK_of_split`, proved here). A piece is a set `P` of darts with
   holes `Hs`, meeting `PcOK` (closed under reversal, connected after contracting its holes, the
   holes pairwise disjoint and free of terminals) and a property `Inv` of the pieces (the
   invariant that the geometric splits need). A large piece (more than `s` darts) is split by
   `hsize` (each child at most three quarters of the darts) or, when six holes touch it and the
   previous split was balanced in size, by `hhole` (each child touched by at most five holes).
   The holes touching a child of a split balanced in size are at most one more than those touching
   the parent (`nTouch_childHoles_le`), so at most six holes touch every piece: five after a split
   balanced in the number of holes, six after one balanced in size. This is the alternation of
   line 2 of Algorithm 1, and `ADec.BalA` allows exactly it.
2. **Small pieces** (`exists_decOK_small`, proved here). A piece of at most `s` darts is
   decomposed down to leaves solved by the leaf solver (`ADec.LeafOK`): its vertices off the
   terminals and the holes are merged into the holes one at a time, along a dart to a hole, the
   edge of this dart split off as a leaf of two darts (`splitOK_peel`). This needs the terminals to
   have degree at most one (the pendant terminals of footnote 4 of the article: no separator can
   pass through them, and a vertex all of whose neighbours are terminals is merged directly,
   `splitOK_pendant`) and no loops. These splits are not balanced, which `ADec.BalA` allows below
   `s` darts (`ADec.SizeBal`); they add `s` to the depth.
3. **The split of a large piece** (`hsize`, `hhole`; proved in the files after this one, for
   the invariant `CInv` of `PlanarFlow/BKMNW/ExistSplit.lean`). On the preprocessed map
   (`PlanarFlow.CombMap.preMap`: a triangulation, the terminals replaced by pendant vertices), the
   piece map of the core of a piece (the darts with no end at a pendant vertex, its holes
   contracted, `PlanarFlow.BKMNW.PieceInv`) has faces of at most three darts or with every dart at
   one hole (`ExistFace`). The holes that are cut vertices are pruned, the weight of the light
   components moved to an anchor dart (`ExistCert`); then no face goes around a hole
   (`ExistJordan`, `ExistComp`), and Miller's theorem on the stellar subdivision gives a short
   cycle (`ExistMiller`), a passage through the centre of a face replaced by darts of the face: a
   simple path through the holes (`PlanarFlow.BKMNW.HPath.Simple`) of at most `6 √(2 m) + 4`
   darts, cut into at most seven parts off the holes (`ExistSegs`). The pendant edges and the
   darts inside the holes are attached (`ExistSplit`, `ExistOracle`), and the parts are grouped
   into two children (`ExistGroup`), with weight on the darts (`split_size`) or on the holes
   (`split_hole`).

`exists_balDecA_of_split` takes the splits of the large pieces as hypotheses; with
`split_size` and `split_hole` they give `PlanarFlow.BKMNW.exists_balDecA_of_cinv`, and on the
preprocessed map `PlanarFlow.BKMNW.exists_balDecA_pre` (`κ = 9`, `η = 6`, `s = 100000`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Relation

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-! ### Coarser holes -/

/-- `Hs'` is **coarser** than `Hs`: every hole of `Hs` lies in a hole of `Hs'`. -/
def Coarse (Hs Hs' : List (Finset V)) : Prop := ∀ H ∈ Hs, ∃ H' ∈ Hs', H ⊆ H'

lemma Coarse.hRel {Hs Hs' : List (Finset V)} (h : Coarse Hs Hs') {a b : V} (hab : HRel Hs a b) :
    HRel Hs' a b := by
  rcases hab with e | ⟨H, hH, ha, hb⟩
  · exact Or.inl e
  · obtain ⟨H', hH', hs⟩ := h H hH
    exact Or.inr ⟨H', hH', hs ha, hs hb⟩

lemma Coarse.inner {Hs Hs' : List (Finset V)} (h : Coarse Hs Hs') {d : D} (hd : Inner M Hs d) :
    Inner M Hs' d := by
  obtain ⟨H, hH, h1, h2⟩ := hd
  obtain ⟨H', hH', hs⟩ := h H hH
  exact ⟨H', hH', hs h1, hs h2⟩

lemma Coarse.pdarts_subset {Hs Hs' : List (Finset V)} (h : Coarse Hs Hs') (P : Finset D) :
    pdarts M P Hs' ⊆ pdarts M P Hs := fun d hd => by
  rw [mem_pdarts] at hd ⊢; exact ⟨hd.1, fun h' => hd.2 (h.inner h')⟩

/-- In coarser pairwise disjoint holes, a vertex related (in the finer holes) to a vertex of a
hole lies in this hole. -/
lemma Coarse.mem_of_hRel {Hs Hs' : List (Finset V)} (h : Coarse Hs Hs')
    (hd : Hs'.Pairwise Disjoint) {H' : Finset V} (hH' : H' ∈ Hs') {a b : V} (hb : b ∈ H')
    (hab : HRel Hs a b) : a ∈ H' := by
  rcases hab with e | ⟨H, hH, ha, hb'⟩
  · exact e ▸ hb
  · obtain ⟨H₁, hH₁, hs⟩ := h H hH
    by_cases e : H₁ = H'
    · exact e ▸ hs ha
    · exact absurd hb (disjoint_left.1 (disjoint_of_pairwise hd hH₁ hH' e) (hs hb'))

lemma coarse_childHoles (Hs : List (Finset V)) (C : Finset V) : Coarse Hs (childHoles Hs C) :=
  fun _ hH => exists_childHoles hH

/-- **Coarser holes keep a piece connected**: the darts left out of the piece map lie inside a
hole, and a step through them is a step between two vertices of this hole. -/
theorem HConn.coarse {P : Finset D} {Hs Hs' : List (Finset V)} (h : HConn M P Hs)
    (hco : Coarse Hs Hs') (hd : Hs'.Pairwise Disjoint) : HConn M P Hs' := by
  intro x hx y hy
  have hsub := hco.pdarts_subset (M := M) P
  have hout : ∀ z, z ∈ pdarts M P Hs → z ∉ pdarts M P Hs' →
      ∃ H' ∈ Hs', M.tail z ∈ H' ∧ M.head z ∈ H' := fun z h1 h2 => by
    rw [mem_pdarts] at h1 h2
    push Not at h2
    exact h2 h1.1
  have key : ∀ z, ReflTransGen (fun a b => b ∈ pdarts M P Hs ∧
      (b = M.rev a ∨ HRel Hs (M.tail a) (M.tail b))) x z →
      z ∈ pdarts M P Hs ∧
      (z ∈ pdarts M P Hs' → ReflTransGen (fun a b => b ∈ pdarts M P Hs' ∧
        (b = M.rev a ∨ HRel Hs' (M.tail a) (M.tail b))) x z) ∧
      (z ∉ pdarts M P Hs' → ∃ w H', ReflTransGen (fun a b => b ∈ pdarts M P Hs' ∧
        (b = M.rev a ∨ HRel Hs' (M.tail a) (M.tail b))) x w ∧ H' ∈ Hs' ∧ M.tail w ∈ H' ∧
          M.tail z ∈ H' ∧ M.head z ∈ H') := by
    intro z hz
    induction hz with
    | refl => exact ⟨hsub hx, fun _ => .refl, fun h' => absurd hx h'⟩
    | tail _ hst ih =>
      rename_i b c _
      obtain ⟨hb0, ihin, ihout⟩ := ih
      obtain ⟨hc0, hbc⟩ := hst
      refine ⟨hc0, fun hc => ?_, fun hc => ?_⟩
      · by_cases hb : b ∈ pdarts M P Hs'
        · refine (ihin hb).tail ⟨hc, ?_⟩
          rcases hbc with e | e
          · exact Or.inl e
          · exact Or.inr (hco.hRel e)
        · obtain ⟨w, H', hw, hH', hwH, hbt, hbh⟩ := ihout hb
          rcases hbc with e | e
          · exfalso
            rw [mem_pdarts] at hc
            exact hc.2 ⟨H', hH', by rw [e, CombMap.tail_rev]; exact hbh,
              by rw [e, CombMap.head_rev]; exact hbt⟩
          · have : M.tail c ∈ H' := hco.mem_of_hRel hd hH' hbt (hRel_symm e)
            exact hw.tail ⟨hc, Or.inr (Or.inr ⟨H', hH', hwH, this⟩)⟩
      · obtain ⟨H', hH', hct, hch⟩ := hout c hc0 hc
        by_cases hb : b ∈ pdarts M P Hs'
        · rcases hbc with e | e
          · exfalso
            rw [mem_pdarts] at hb
            exact hb.2 ⟨H', hH', by rw [← CombMap.head_rev, ← e]; exact hch,
              by rw [← CombMap.tail_rev, ← e]; exact hct⟩
          · exact ⟨b, H', ihin hb, hH', hco.mem_of_hRel hd hH' hct e, hct, hch⟩
        · obtain ⟨w, H₁, hw, hH₁, hwH, hbt, hbh⟩ := ihout hb
          rcases hbc with e | e
          · refine ⟨w, H₁, hw, hH₁, hwH, ?_, ?_⟩
            · rw [e, CombMap.tail_rev]; exact hbh
            · rw [e, CombMap.head_rev]; exact hbt
          · have htc : M.tail c ∈ H₁ := hco.mem_of_hRel hd hH₁ hbt (hRel_symm e)
            refine ⟨w, H₁, hw, hH₁, hwH, htc, ?_⟩
            by_cases eH : H₁ = H'
            · exact eH ▸ hch
            · exact absurd hct (disjoint_left.1 (disjoint_of_pairwise hd hH₁ hH' eH) htc)
  exact (key y (h x (hsub hx) y (hsub hy))).2.1 hy

/-- A piece is connected after contracting its holes as soon as its piece map is that of a
connected piece. -/
lemma HConn.of_pdarts_eq {P Q : Finset D} {Hs : List (Finset V)} (h : HConn M P Hs)
    (e : pdarts M Q Hs = pdarts M P Hs) : HConn M Q Hs := by
  unfold HConn; rw [e]; exact h

/-! ### The holes touching a piece -/

open Classical in
lemma nTouch_childHoles_le {P P' : Finset D} (hP : P' ⊆ P) (Hs : List (Finset V))
    (C : Finset V) : nTouch M P' (childHoles Hs C) ≤ nTouch M P Hs + 1 := by
  unfold nTouch childHoles
  rw [List.filter_append, List.length_append, List.filter_filter]
  have h1 : ((Hs.filter fun H => (decide (∃ v ∈ H, Touch M P' v) && decide (Disjoint H C)))).length
      ≤ (Hs.filter fun H => decide (∃ v ∈ H, Touch M P v)).length := by
    refine (List.monotone_filter_right _ fun H hH => ?_).length_le
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hH ⊢
    obtain ⟨⟨v, hv, d, hd, e⟩, -⟩ := hH
    exact ⟨v, hv, d, hP hd, e⟩
  have h2 : ([newHole Hs C].filter fun H => decide (∃ v ∈ H, Touch M P' v)).length ≤ 1 := by
    have := List.length_filter_le (fun H => decide (∃ v ∈ H, Touch M P' v)) [newHole Hs C]
    simpa using this
  omega

open Classical in
/-- When the separator meets a hole touching the piece, no hole is added. -/
lemma nTouch_childHoles_le_of_meet {P P' : Finset D} (hP : P' ⊆ P) {Hs : List (Finset V)}
    {C : Finset V} {H₀ : Finset V} (hH₀ : H₀ ∈ Hs) (ht : ∃ v ∈ H₀, Touch M P v)
    (hm : ¬ Disjoint H₀ C) : nTouch M P' (childHoles Hs C) ≤ nTouch M P Hs := by
  unfold nTouch childHoles
  rw [List.filter_append, List.length_append, List.filter_filter]
  set L := Hs.filter fun H => decide (∃ v ∈ H, Touch M P v)
  have h1 : ((Hs.filter fun H => (decide (∃ v ∈ H, Touch M P' v) && decide (Disjoint H C)))).length
      ≤ L.countP (fun H => decide (Disjoint H C)) := by
    rw [List.countP_eq_length_filter, List.filter_filter]
    refine (List.monotone_filter_right _ fun H hH => ?_).length_le
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hH ⊢
    obtain ⟨⟨v, hv, d, hd, e⟩, h'⟩ := hH
    exact ⟨h', v, hv, d, hP hd, e⟩
  have h3 : 0 < L.countP (fun H => !decide (Disjoint H C)) :=
    List.countP_pos_iff.2 ⟨H₀, List.mem_filter.2 ⟨hH₀, by simpa using ht⟩, by simpa using hm⟩
  have h4 := List.length_eq_countP_add_countP (fun H => decide (Disjoint H C)) (l := L)
  have h2 : ([newHole Hs C].filter fun H => decide (∃ v ∈ H, Touch M P' v)).length ≤ 1 := by
    have := List.length_filter_le (fun H => decide (∃ v ∈ H, Touch M P' v)) [newHole Hs C]
    simpa using this
  have h5 : L.countP (fun H => !decide (Disjoint H C)) =
      L.countP (fun H => decide ¬ (decide (Disjoint H C) = true)) := by
    congr 1
  omega

/-! ### Splits and the recursion -/

variable (M) in
/-- **The invariant of a piece in the construction**: closed under reversal, connected after
contracting its holes, its holes pairwise disjoint and free of terminals. -/
structure PcOK (S T : Finset V) (P : Finset D) (Hs : List (Finset V)) : Prop where
  rev : RevClosed M P
  conn : HConn M P Hs
  disj : Hs.Pairwise Disjoint
  term : Disjoint (hunion Hs) (S ∪ T)

variable (M) in
/-- **A split of a piece** `P` with holes `Hs` into the children `l` and `r` by the separator `π`:
the conditions of `ADec.Good`, `ADec.PGood` and `ADec.Core` at the node (with `κ`, `η`), the
children closed under reversal and connected after contracting their holes. -/
structure SplitOK (S T : Finset V) (κ η : ℕ) (P : Finset D) (Hs : List (Finset V))
    (l r : Finset D) (π : HSep M) : Prop where
  union : l ∪ r = P
  disj : Disjoint l r
  lpos : 0 < l.card
  rpos : 0 < r.card
  bd : bd M l r ⊆ S ∪ T ∪ (hunion Hs ∪ π.path.mverts)
  sepT : Disjoint π.path.mverts (S ∪ T)
  seg : π.SegOK Hs
  simple : π.path.Simple Hs
  darts : ∀ e ∈ π.path.darts, e ∈ pdarts M P Hs
  segs : ∀ σ ∈ π.segs, (∀ e ∈ σ.darts, e ∈ P) ∧ ∃ x ∈ P, M.tail x = σ.p σ.k
  short : π.Short κ η P.card
  lrev : RevClosed M l
  rrev : RevClosed M r
  lconn : HConn M l (childHoles Hs π.path.mverts)
  rconn : HConn M r (childHoles Hs π.path.mverts)

namespace SplitOK

variable {S T : Finset V} {κ η : ℕ} {P l r : Finset D} {Hs : List (Finset V)} {π : HSep M}

lemma pcOK_l (h : SplitOK M S T κ η P Hs l r π) (hP : PcOK M S T P Hs) :
    PcOK M S T l (childHoles Hs π.path.mverts) :=
  ⟨h.lrev, h.lconn, pairwise_childHoles hP.disj, by
    rw [hunion_childHoles]; exact disjoint_union_left.2 ⟨hP.term, h.sepT⟩⟩

lemma pcOK_r (h : SplitOK M S T κ η P Hs l r π) (hP : PcOK M S T P Hs) :
    PcOK M S T r (childHoles Hs π.path.mverts) :=
  ⟨h.rrev, h.rconn, pairwise_childHoles hP.disj, by
    rw [hunion_childHoles]; exact disjoint_union_left.2 ⟨hP.term, h.sepT⟩⟩

lemma card_l_lt (h : SplitOK M S T κ η P Hs l r π) : l.card < P.card := by
  rw [← h.union, card_union_of_disjoint h.disj]; have := h.rpos; omega

lemma card_r_lt (h : SplitOK M S T κ η P Hs l r π) : r.card < P.card := by
  rw [← h.union, card_union_of_disjoint h.disj]; have := h.lpos; omega

/-- **A node from a split**: the conditions of correctness hold at the node when they hold at the
children. -/
lemma node (h : SplitOK M S T κ η P Hs l r π) (hP : HConn M P Hs) {τl τr : ADec M}
    (hl : τl.piece = l)
    (hr : τr.piece = r) (gl : τl.Good M S T (childHoles Hs π.path.mverts))
    (gr : τr.Good M S T (childHoles Hs π.path.mverts))
    (pl : τl.PGood M (childHoles Hs π.path.mverts)) (pr : τr.PGood M (childHoles Hs π.path.mverts))
    (ol : τl.LeafOK M S T (childHoles Hs π.path.mverts))
    (or : τr.LeafOK M S T (childHoles Hs π.path.mverts)) :
    (ADec.node τl τr π).piece = P ∧ (ADec.node τl τr π).Good M S T Hs ∧
      (ADec.node τl τr π).PGood M Hs ∧ (ADec.node τl τr π).LeafOK M S T Hs := by
  have e : τl.piece ∪ τr.piece = P := by rw [hl, hr, h.union]
  refine ⟨e, ⟨gl, gr, by rw [hl, hr]; exact h.disj, by rw [hl, hr]; exact h.bd, h.sepT, h.seg⟩,
    ⟨by rw [e]; exact hP, h.simple, by rw [e]; exact h.darts, pl, pr, by rw [e]; exact h.segs⟩,
    ol, or⟩

end SplitOK

variable (M) in
/-- **The decompositions of a piece built here**: covering the piece `P` with holes `Hs`, good,
with pieces as in the article and leaves solved by the leaf solver, and balanced as in the
article (`ADec.BalA`, with the flag `b`). -/
def DecOK (S T : Finset V) (κ η s : ℕ) (P : Finset D) (Hs : List (Finset V)) (b : Bool)
    (τ : ADec M) : Prop :=
  τ.piece = P ∧ τ.Good M S T Hs ∧ τ.PGood M Hs ∧ τ.LeafOK M S T Hs ∧ τ.BalA M κ η s b Hs

/-- **The recursion with the alternation of the article**, from splits of the large pieces. Let
`Inv` be a property of the pieces. Assume that every piece meeting `PcOK` with at most `s` darts and
at most six holes touching it has a decomposition (`hsmall`), and that every piece meeting `PcOK`
and `Inv` with more than `s` darts has a split into children meeting `Inv` with at most three
quarters of its darts each when at most five holes touch it (`hsize`), and a split whose children
touch at most five holes each when six holes touch it (`hhole`). Then every piece meeting `PcOK`
and `Inv` has a decomposition meeting `BalA` with `η = 6`: a split balanced in the number of holes
is done only when six holes touch the piece and the previous split was balanced in size, so that
at most six holes touch every piece (at most five after a split balanced in the number of
holes). -/
theorem exists_decOK_of_split {S T : Finset V} {κ s : ℕ}
    (Inv : Finset D → List (Finset V) → Prop)
    (hsmall : ∀ P Hs, PcOK M S T P Hs → P.card ≤ s → nTouch M P Hs ≤ 6 →
      ∃ τ : ADec M, ∀ b, DecOK M S T κ 6 s P Hs b τ)
    (hsize : ∀ P Hs, PcOK M S T P Hs → Inv P Hs → s < P.card → nTouch M P Hs ≤ 5 →
      ∃ l r π, SplitOK M S T κ 6 P Hs l r π ∧ Inv l (childHoles Hs π.path.mverts) ∧
        Inv r (childHoles Hs π.path.mverts) ∧ 4 * l.card ≤ 3 * P.card ∧ 4 * r.card ≤ 3 * P.card)
    (hhole : ∀ P Hs, PcOK M S T P Hs → Inv P Hs → s < P.card → nTouch M P Hs = 6 →
      ∃ l r π, SplitOK M S T κ 6 P Hs l r π ∧ Inv l (childHoles Hs π.path.mverts) ∧
        Inv r (childHoles Hs π.path.mverts) ∧ nTouch M l (childHoles Hs π.path.mverts) ≤ 5 ∧
          nTouch M r (childHoles Hs π.path.mverts) ≤ 5) :
    ∀ (n : ℕ) (P : Finset D) (Hs : List (Finset V)) (b : Bool), P.card = n → PcOK M S T P Hs →
      Inv P Hs → nTouch M P Hs ≤ (if b then 6 else 5) →
        ∃ τ : ADec M, DecOK M S T κ 6 s P Hs b τ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Hs b hn hP hI ht
  by_cases hs : P.card ≤ s
  · obtain ⟨τ, hτ⟩ := hsmall P Hs hP hs (by split_ifs at ht <;> omega)
    exact ⟨τ, hτ b⟩
  push Not at hs
  by_cases hh : b = true ∧ nTouch M P Hs = 6
  · -- a split balanced in the number of holes
    obtain ⟨hb, h6⟩ := hh
    obtain ⟨l, r, π, h, il, ir, tl, tr⟩ := hhole P Hs hP hI hs h6
    obtain ⟨τl, pl, gl, ql, ol, bl⟩ := ih _ (hn ▸ h.card_l_lt) l _ false rfl (h.pcOK_l hP) il
      (by simpa using tl)
    obtain ⟨τr, pr, gr, qr, or, br⟩ := ih _ (hn ▸ h.card_r_lt) r _ false rfl (h.pcOK_r hP) ir
      (by simpa using tr)
    obtain ⟨e, g, q, o⟩ := h.node hP.conn pl pr gl gr ql qr ol or
    refine ⟨.node τl τr π, e, g, q, o, ?_⟩
    refine ⟨by rw [pl, pr]; exact h.disj, by rw [pl]; exact h.lpos, by rw [pr]; exact h.rpos,
      by rw [pl, pr, h.union]; exact h.short, by rw [pl, pr, h.union]; omega,
      Or.inr ⟨hb, bl, br⟩⟩
  · -- a split balanced in size
    have h5 : nTouch M P Hs ≤ 5 := by
      cases b
      · simpa using ht
      · simp only [ite_true] at ht; simp only [true_and] at hh; omega
    obtain ⟨l, r, π, h, il, ir, sl, sr⟩ := hsize P Hs hP hI hs h5
    have tl := nTouch_childHoles_le (M := M) (h.union ▸ subset_union_left) Hs π.path.mverts
    have tr := nTouch_childHoles_le (M := M) (h.union ▸ subset_union_right) Hs π.path.mverts
    obtain ⟨τl, pl, gl, ql, ol, bl⟩ := ih _ (hn ▸ h.card_l_lt) l _ true rfl (h.pcOK_l hP) il
      (by simp only [ite_true]; omega)
    obtain ⟨τr, pr, gr, qr, or, br⟩ := ih _ (hn ▸ h.card_r_lt) r _ true rfl (h.pcOK_r hP) ir
      (by simp only [ite_true]; omega)
    obtain ⟨e, g, q, o⟩ := h.node hP.conn pl pr gl gr ql qr ol or
    refine ⟨.node τl τr π, e, g, q, o, ?_⟩
    refine ⟨by rw [pl, pr]; exact h.disj, by rw [pl]; exact h.lpos, by rw [pr]; exact h.rpos,
      by rw [pl, pr, h.union]; exact h.short, by rw [pl, pr, h.union]; omega,
      Or.inl ⟨Or.inr ⟨by rw [pl, pr, h.union]; exact sl, by rw [pl, pr, h.union]; exact sr⟩,
        bl, br⟩⟩

/-! ### Small pieces: merging the vertices into the holes one at a time -/

/-- The simple path of one dart (not a loop). -/
def SPath.ofDart (x : D) (hx : M.head x ≠ M.tail x) : SPath M where
  k := 1
  d _ := x
  p j := if j = 0 then M.tail x else M.head x
  tail_d j hj := by obtain rfl : j = 0 := by omega
                    simp
  head_d j hj := by obtain rfl : j = 0 := by omega
                    simp
  inj i hi j hj e := by
    interval_cases i <;> interval_cases j <;> simp_all [eq_comm]

lemma SPath.ofDart_verts (x : D) (hx : M.head x ≠ M.tail x) :
    (SPath.ofDart x hx).verts = {M.tail x, M.head x} := by
  ext v
  simp only [SPath.verts, SPath.mem_init, SPath.ofDart, mem_insert, mem_singleton]
  constructor
  · rintro ⟨t, ht, rfl⟩
    interval_cases t <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by omega, by simp⟩
    · exact ⟨1, le_rfl, by simp⟩

lemma SPath.ofDart_darts (x : D) (hx : M.head x ≠ M.tail x) :
    (SPath.ofDart x hx).darts = [x, M.rev x] := by
  simp [SPath.darts, SPath.ofDart]

lemma SPath.point_darts' (x : D) (v : V) : (SPath.point (M' := M) x v).darts = [] := by
  simp [SPath.darts, SPath.point]

lemma HPath.toH_point_mverts (x : D) (v : V) : (SPath.point (M' := M) x v).toH.mverts = {v} := by
  rw [SPath.toH_mverts, SPath.point_verts]

lemma HPath.toH_ofDart_mverts (x : D) (hx : M.head x ≠ M.tail x) :
    (SPath.ofDart x hx).toH.mverts = {M.tail x, M.head x} := by
  rw [SPath.toH_mverts, SPath.ofDart_verts]

lemma hConn_of_pdarts_eq_empty {P : Finset D} {Hs : List (Finset V)}
    (h : pdarts M P Hs = ∅) : HConn M P Hs := fun x hx => by rw [h] at hx; simp at hx

lemma revClosed_pair (x : D) : RevClosed M {x, M.rev x} := fun d hd => by
  simp only [mem_insert, mem_singleton] at hd ⊢
  rcases hd with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (M.rev_rev _)

lemma revClosed_sdiff_pair {P : Finset D} (hP : RevClosed M P) (x : D) :
    RevClosed M (P \ {x, M.rev x}) := fun d hd => by
  simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hd ⊢
  refine ⟨hP d hd.1, fun e => hd.2.2 (by rw [← e, M.rev_rev]), fun e => hd.2.1 ?_⟩
  have := congrArg M.rev e; rwa [M.rev_rev, M.rev_rev] at this

lemma bd_subset_pair (l : Finset D) (x : D) :
    bd M l {x, M.rev x} ⊆ {M.tail x, M.head x} := fun v hv => by
  obtain ⟨-, d, hd, rfl⟩ := mem_bd.1 hv
  simp only [mem_insert, mem_singleton] at hd ⊢
  rcases hd with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (by rw [CombMap.tail_rev])

lemma inner_childHoles_of_mem {Hs : List (Finset V)} {C : Finset V} {x : D} (h1 : M.tail x ∈ C)
    (h2 : M.head x ∈ C) : Inner M (childHoles Hs C) x :=
  ⟨newHole Hs C, List.mem_append_right _ (List.mem_singleton_self _), subset_newHole h1,
    subset_newHole h2⟩

lemma pdarts_sdiff_pair {P : Finset D} {Hs : List (Finset V)} {x : D} (hx : Inner M Hs x) :
    pdarts M (P \ {x, M.rev x}) Hs = pdarts M P Hs := by
  ext d
  simp only [mem_pdarts, mem_sdiff, mem_insert, mem_singleton]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · refine fun h => ⟨⟨h.1, fun e => h.2 ?_⟩, h.2⟩
    rcases e with rfl | rfl
    · exact hx
    · exact inner_rev.2 hx

lemma pdarts_pair_eq_empty {Hs : List (Finset V)} {x : D} (hx : Inner M Hs x) :
    pdarts M {x, M.rev x} Hs = ∅ := by
  ext d
  simp only [mem_pdarts, mem_insert, mem_singleton, Finset.notMem_empty, iff_false, not_and,
    not_not]
  rintro (rfl | rfl)
  · exact hx
  · exact inner_rev.2 hx

lemma card_sdiff_pair_pos {P : Finset D} {x : D} (hx : x ∈ P) (hP : RevClosed M P)
    (h : 2 < P.card) : 0 < (P \ {x, M.rev x}).card := by
  have : ({x, M.rev x} : Finset D) ⊆ P := by
    intro d hd; simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact hx
    · exact hP _ hx
  rw [card_sdiff_of_subset this]
  have := card_le_two (a := x) (b := M.rev x)
  omega

lemma union_sdiff_pair {P : Finset D} {x : D} (hx : x ∈ P) (hP : RevClosed M P) :
    P \ {x, M.rev x} ∪ {x, M.rev x} = P := by
  refine sdiff_union_of_subset fun d hd => ?_
  simp only [mem_insert, mem_singleton] at hd
  rcases hd with rfl | rfl
  · exact hx
  · exact hP _ hx

lemma card_pair_pos (x : D) : 0 < ({x, M.rev x} : Finset D).card := card_pos.2 ⟨x, by simp⟩

/-- A leaf solved by the leaf solver meets everything. -/
lemma decOK_leaf {S T : Finset V} {κ η s : ℕ} {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs)
    (hL : P.card ≤ 2 ∨ ∀ d ∈ pdarts M P Hs, M.tail d ∈ S ∪ T ∪ hunion Hs) (b : Bool) :
    DecOK M S T κ η s P Hs b (.leaf P) :=
  ⟨rfl, hP.rev, hP.conn, hL, trivial⟩

/-- A node of a small piece whose second child is a leaf. -/
lemma decOK_node_leaf {S T : Finset V} {κ η s : ℕ} {P l r : Finset D} {Hs : List (Finset V)}
    {π : HSep M} (h : SplitOK M S T κ η P Hs l r π) (hP : PcOK M S T P Hs) (hs : P.card ≤ s)
    (ht : nTouch M P Hs ≤ η)
    (hr : r.card ≤ 2 ∨ ∀ d ∈ pdarts M r (childHoles Hs π.path.mverts),
      M.tail d ∈ S ∪ T ∪ hunion (childHoles Hs π.path.mverts))
    {τl : ADec M} (hl : ∀ b, DecOK M S T κ η s l (childHoles Hs π.path.mverts) b τl) (b : Bool) :
    DecOK M S T κ η s P Hs b (.node τl (.leaf r) π) := by
  obtain ⟨pl, gl, ql, ol, bl⟩ := hl true
  obtain ⟨e, g, q, o⟩ := h.node (τr := .leaf r) hP.conn pl rfl gl h.rrev ql h.rconn ol hr
  refine ⟨e, g, q, o, by rw [pl]; exact h.disj, by rw [pl]; exact h.lpos, h.rpos,
    by rw [pl, ADec.piece, h.union]; exact h.short, by rw [pl, ADec.piece, h.union]; exact ht,
    Or.inl ⟨Or.inl (by rw [pl, ADec.piece, h.union]; exact hs), bl, trivial⟩⟩

lemma hunion_singleton' (A : Finset V) : hunion [A] = A := by simp [hunion]

lemma hunion_nil' : hunion ([] : List (Finset V)) = ∅ := rfl

lemma hConn_pair (x : D) (Hs : List (Finset V)) : HConn M {x, M.rev x} Hs := by
  intro a ha b hb
  have ha' := pdarts_subset _ _ ha
  have hb' := pdarts_subset _ _ hb
  simp only [mem_insert, mem_singleton] at ha' hb'
  by_cases e : a = b
  · exact e ▸ .refl
  refine .single ⟨hb, Or.inl ?_⟩
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact absurd rfl e
  · rfl
  · rw [M.rev_rev]
  · exact absurd rfl e

/-- **Removing a pendant edge keeps a piece connected**: a dart `x` whose head is a vertex off
the holes with no other dart of the piece leaving it. -/
lemma HConn.sdiff_pendant {P : Finset D} {Hs : List (Finset V)} (h : HConn M P Hs) {x : D}
    (hx : x ∈ P) (hw : M.head x ∉ hunion Hs) (hv : M.tail x ∉ hunion Hs)
    (hdeg : ∀ d ∈ P, M.tail d = M.head x → d = M.rev x) : HConn M (P \ {x, M.rev x}) Hs := by
  intro a ha b hb
  have hsub : pdarts M (P \ {x, M.rev x}) Hs ⊆ pdarts M P Hs :=
    fun d hd => by rw [mem_pdarts] at hd ⊢; exact ⟨(mem_sdiff.1 hd.1).1, hd.2⟩
  have hmem : ∀ d, d ∈ pdarts M P Hs → d ∉ ({x, M.rev x} : Finset D) →
      d ∈ pdarts M (P \ {x, M.rev x}) Hs := fun d hd hn => by
    rw [mem_pdarts] at hd ⊢; exact ⟨mem_sdiff.2 ⟨hd.1, hn⟩, hd.2⟩
  have ha0 : a ∉ ({x, M.rev x} : Finset D) := (mem_sdiff.1 (pdarts_subset _ _ ha)).2
  set R' := fun a b => b ∈ pdarts M (P \ {x, M.rev x}) Hs ∧
    (b = M.rev a ∨ HRel Hs (M.tail a) (M.tail b))
  have hpr : ∀ y, y ∈ ({x, M.rev x} : Finset D) ↔ y = x ∨ y = M.rev x := fun y => by simp
  have hrx : ∀ d ∈ P, HRel Hs (M.tail (M.rev x)) (M.tail d) → d = M.rev x := fun d hd e => by
    rw [CombMap.tail_rev] at e
    exact hdeg d hd (hRel_eq_of_not_mem hw (hRel_symm e))
  have key : ∀ z, ReflTransGen (fun a b => b ∈ pdarts M P Hs ∧
      (b = M.rev a ∨ HRel Hs (M.tail a) (M.tail b))) a z →
      z ∈ pdarts M P Hs ∧ (z ∉ ({x, M.rev x} : Finset D) → ReflTransGen R' a z) ∧
      (z ∈ ({x, M.rev x} : Finset D) → ∃ w, ReflTransGen R' a w ∧ M.tail w = M.tail x) := by
    intro z hz
    induction hz with
    | refl => exact ⟨hsub ha, fun _ => .refl, fun h' => absurd h' ha0⟩
    | tail _ hst ih =>
      rename_i c d _
      obtain ⟨hc0, ihn, ihm⟩ := ih
      obtain ⟨hd0, hcd⟩ := hst
      have hdP := pdarts_subset _ _ hd0
      refine ⟨hd0, fun hdn => ?_, fun hdm => ?_⟩
      · by_cases hc : c ∈ ({x, M.rev x} : Finset D)
        · obtain ⟨w, hw', ew⟩ := ihm hc
          rcases (hpr c).1 hc with rfl | rfl
          · rcases hcd with e | e
            · exact absurd ((hpr d).2 (Or.inr e)) hdn
            · have e' := hRel_eq_of_not_mem hv (hRel_symm e)
              exact hw'.tail ⟨hmem d hd0 hdn, Or.inr (Or.inl (ew.trans e'.symm))⟩
          · rcases hcd with e | e
            · exact absurd ((hpr d).2 (Or.inl (by rw [e, M.rev_rev]))) hdn
            · exact absurd ((hpr d).2 (Or.inr (hrx d hdP e))) hdn
        · exact (ihn hc).tail ⟨hmem d hd0 hdn, hcd⟩
      · by_cases hc : c ∈ ({x, M.rev x} : Finset D)
        · exact ihm hc
        · rcases (hpr d).1 hdm with rfl | rfl
          · rcases hcd with e | e
            · exact absurd ((hpr c).2 (Or.inr (by rw [e, M.rev_rev]))) hc
            · exact ⟨c, ihn hc, hRel_eq_of_not_mem hv e⟩
          · rcases hcd with e | e
            · exact absurd ((hpr c).2 (Or.inl (M.rev_injective e).symm)) hc
            · exfalso
              have e' : M.tail c = M.head x := by
                rw [CombMap.tail_rev] at e; exact hRel_eq_of_not_mem hw e
              exact hc ((hpr c).2 (Or.inr (hdeg c (pdarts_subset _ _ hc0) e')))
  exact (key b (h a (hsub ha) b (hsub hb))).2.1 (mem_sdiff.1 (pdarts_subset _ _ hb)).2

/-- **The vertices next to the holes**: if no dart of the piece map goes from a vertex off the
terminals and the holes into a hole, and the terminals have degree at most one, then all the
darts of a piece map with a dart leaving a hole leave terminals or holes. -/
lemma tail_mem_of_no_peel {S T : Finset V}
    (hdeg : ∀ t ∈ S ∪ T, ∀ d d', M.tail d = t → M.tail d' = t → d = d') {P : Finset D}
    {Hs : List (Finset V)} (hP : PcOK M S T P Hs)
    (hno : ∀ x ∈ pdarts M P Hs, M.tail x ∉ S ∪ T ∪ hunion Hs → M.head x ∉ hunion Hs)
    {y₀ : D} (hy₀ : y₀ ∈ pdarts M P Hs) (hy : M.tail y₀ ∈ hunion Hs) :
    ∀ d ∈ pdarts M P Hs, M.tail d ∈ S ∪ T ∪ hunion Hs := by
  have hst := stable_pdarts hP.rev Hs
  have hhead : ∀ z ∈ pdarts M P Hs, M.tail z ∈ hunion Hs → M.head z ∈ S ∪ T ∪ hunion Hs := by
    intro z hz ht
    by_contra hh
    have hrz : M.rev z ∈ pdarts M P Hs := hst z hz
    exact hno _ hrz (by rwa [CombMap.tail_rev]) (by rw [CombMap.head_rev]; exact ht)
  intro d hd
  have key : ∀ z, ReflTransGen (fun a b => b ∈ pdarts M P Hs ∧
      (b = M.rev a ∨ HRel Hs (M.tail a) (M.tail b))) y₀ z →
      z ∈ pdarts M P Hs ∧ M.tail z ∈ S ∪ T ∪ hunion Hs ∧ M.head z ∈ S ∪ T ∪ hunion Hs := by
    intro z hz
    induction hz with
    | refl => exact ⟨hy₀, mem_union_right _ hy, hhead _ hy₀ hy⟩
    | tail _ hst' ih =>
      rename_i b c _
      obtain ⟨hb0, hbt, hbh⟩ := ih
      obtain ⟨hc0, hbc⟩ := hst'
      rcases hbc with e | e
      · subst e; exact ⟨hc0, by rwa [CombMap.tail_rev], by rwa [CombMap.head_rev]⟩
      · by_cases hb : M.tail b ∈ hunion Hs
        · have hc : M.tail c ∈ hunion Hs := by
            rcases e with e | ⟨H, hH, -, h2⟩
            · exact e ▸ hb
            · exact subset_hunion hH h2
          exact ⟨hc0, mem_union_right _ hc, hhead _ hc0 hc⟩
        · have e' : M.tail c = M.tail b := hRel_eq_of_not_mem hb (hRel_symm e)
          have hbST : M.tail b ∈ S ∪ T := by
            rcases mem_union.1 hbt with h | h
            · exact h
            · exact absurd h hb
          have : c = b := hdeg _ hbST c b e' rfl
          subst this; exact ⟨hc0, hbt, hbh⟩
  exact (key d (hP.conn y₀ hy₀ d hd)).2.1

/-- The separator merging a vertex into a hole: the dart `x` from the vertex to the hole, its
only part off the holes the vertex. -/
def peelSep (x : D) (hx : M.head x ≠ M.tail x) : HSep M :=
  ⟨(SPath.ofDart x hx).toH, [SPath.point x (M.tail x)]⟩

/-- **Merging a vertex next to a hole into the hole**: the vertex `v` off the terminals and the
holes, joined to a hole by a dart `x` of the piece map; the edge of `x` is split off as a leaf. -/
lemma splitOK_peel {S T : Finset V} {κ η : ℕ} {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) {x : D} (hx : x ∈ pdarts M P Hs) (hv : M.tail x ∉ S ∪ T ∪ hunion Hs)
    (ha : M.head x ∈ hunion Hs) (hcard : 2 < P.card) (hne : M.head x ≠ M.tail x) :
    SplitOK M S T κ η P Hs (P \ {x, M.rev x}) {x, M.rev x} (peelSep x hne) := by
  have hxP : x ∈ P := (mem_pdarts.1 hx).1
  have hm : (peelSep x hne).path.mverts = {M.tail x, M.head x} := HPath.toH_ofDart_mverts x hne
  have hvH : M.tail x ∉ hunion Hs := fun h => hv (mem_union_right _ h)
  have hvST : M.tail x ∉ S ∪ T := fun h => hv (mem_union_left _ h)
  have hin : Inner M (childHoles Hs (peelSep x hne).path.mverts) x :=
    inner_childHoles_of_mem (by rw [hm]; simp) (by rw [hm]; simp)
  have hco := hP.conn.coarse (coarse_childHoles Hs (peelSep x hne).path.mverts)
    (pairwise_childHoles hP.disj)
  refine ⟨union_sdiff_pair hxP hP.rev, disjoint_sdiff_self_left,
    card_sdiff_pair_pos hxP hP.rev hcard, card_pair_pos x, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    revClosed_sdiff_pair hP.rev x, revClosed_pair x,
    hco.of_pdarts_eq (pdarts_sdiff_pair hin), hConn_of_pdarts_eq_empty (pdarts_pair_eq_empty hin)⟩
  · refine (bd_subset_pair _ x).trans fun v hv' => ?_
    rw [hm]; exact mem_union_right _ (mem_union_right _ hv')
  · rw [hm]
    refine disjoint_left.2 fun v hv' hvS => ?_
    simp only [mem_insert, mem_singleton] at hv'
    rcases hv' with rfl | rfl
    · exact hvST hvS
    · exact disjoint_left.1 hP.term ha hvS
  · refine ⟨fun σ hσ => ?_, List.pairwise_singleton _ _, ?_⟩
    · rw [List.mem_singleton.1 hσ, SPath.point_verts]
      exact disjoint_singleton_left.2 hvH
    · rw [hm]; simp only [peelSep, List.map_cons, List.map_nil, hunion_singleton',
        SPath.point_verts]
      ext v; simp only [mem_union, mem_insert, mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inl (h ▸ ha)
  · refine ⟨fun j hj => ?_, fun i hi j hj e => ?_⟩
    · obtain rfl : j = 0 := by simpa [peelSep, SPath.toH, SPath.ofDart] using hj
      exact Or.inl (by simp [peelSep, SPath.toH, SPath.ofDart])
    · simp only [peelSep, SPath.toH, SPath.ofDart] at hi hj e
      interval_cases i <;> interval_cases j
      · rfl
      · rcases e with e | ⟨H, hH, h1, -⟩
        · simp at e; exact absurd e.symm hne
        · simp at h1; exact absurd (subset_hunion hH h1) hvH
      · rcases e with e | ⟨H, hH, -, h2⟩
        · simp at e; exact absurd e hne
        · simp at h2; exact absurd (subset_hunion hH h2) hvH
      · rfl
  · intro e he
    rw [show (peelSep x hne).path.darts = [x, M.rev x] by
      rw [peelSep, SPath.toH_darts, SPath.ofDart_darts]] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hx
    · exact stable_pdarts hP.rev Hs _ hx
  · intro σ hσ
    rw [List.mem_singleton.1 hσ]
    exact ⟨fun e he => by simp [SPath.point_darts'] at he, x, hxP, rfl⟩
  · refine ⟨by simp [peelSep], fun σ hσ => ?_⟩
    rw [List.mem_singleton.1 hσ]; simp [SPath.point]

lemma SPath.toSep_darts (π : SPath M) : π.toSep.path.darts = π.darts := rfl

/-- **The first hole, on an edge off the terminals**: the edge of `x` is the separator. -/
lemma splitOK_edge {S T : Finset V} {κ η : ℕ} (hκ : 1 ≤ κ) {P : Finset D}
    {Hs : List (Finset V)} (hP : PcOK M S T P Hs) {x : D} (hx : x ∈ pdarts M P Hs)
    (hv : M.tail x ∉ S ∪ T ∪ hunion Hs) (hw : M.head x ∉ S ∪ T ∪ hunion Hs) (hcard : 2 < P.card)
    (hne : M.head x ≠ M.tail x) :
    SplitOK M S T κ η P Hs (P \ {x, M.rev x}) {x, M.rev x} (SPath.ofDart x hne).toSep := by
  have hxP : x ∈ P := (mem_pdarts.1 hx).1
  have hm : (SPath.ofDart x hne).toSep.path.mverts = {M.tail x, M.head x} :=
    HPath.toH_ofDart_mverts x hne
  have hdisj : Disjoint (SPath.ofDart x hne).verts (hunion Hs) := by
    rw [SPath.ofDart_verts]
    refine disjoint_left.2 fun v hv' hvH => ?_
    simp only [mem_insert, mem_singleton] at hv'
    rcases hv' with rfl | rfl
    · exact hv (mem_union_right _ hvH)
    · exact hw (mem_union_right _ hvH)
  have hin : Inner M (childHoles Hs (SPath.ofDart x hne).toSep.path.mverts) x :=
    inner_childHoles_of_mem (by rw [hm]; simp) (by rw [hm]; simp)
  have hco := hP.conn.coarse (coarse_childHoles Hs (SPath.ofDart x hne).toSep.path.mverts)
    (pairwise_childHoles hP.disj)
  refine ⟨union_sdiff_pair hxP hP.rev, disjoint_sdiff_self_left,
    card_sdiff_pair_pos hxP hP.rev hcard, card_pair_pos x, ?_, ?_, SPath.toSep_segOK _ hdisj,
    SPath.toH_simple _ hdisj, ?_, ?_, ?_, revClosed_sdiff_pair hP.rev x, revClosed_pair x,
    hco.of_pdarts_eq (pdarts_sdiff_pair hin), hConn_of_pdarts_eq_empty (pdarts_pair_eq_empty hin)⟩
  · refine (bd_subset_pair _ x).trans fun v hv' => ?_
    rw [hm]; exact mem_union_right _ (mem_union_right _ hv')
  · rw [hm]
    refine disjoint_left.2 fun v hv' hvS => ?_
    simp only [mem_insert, mem_singleton] at hv'
    rcases hv' with rfl | rfl
    · exact hv (mem_union_left _ hvS)
    · exact hw (mem_union_left _ hvS)
  · intro e he
    rw [SPath.toSep_darts, SPath.ofDart_darts] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hx
    · exact stable_pdarts hP.rev Hs _ hx
  · intro σ hσ
    rw [show σ = SPath.ofDart x hne by simpa [SPath.toSep] using hσ]
    refine ⟨fun e he => ?_, M.rev x, hP.rev _ hxP, by simp [SPath.ofDart]⟩
    rw [SPath.ofDart_darts] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hxP
    · exact hP.rev _ hxP
  · refine ⟨by simp [SPath.toSep], fun σ hσ => ?_⟩
    rw [show σ = SPath.ofDart x hne by simpa [SPath.toSep] using hσ]
    simp only [SPath.ofDart, one_pow, mul_one]
    constructor
    · have : 1 ≤ κ ^ 2 := Nat.one_le_pow _ _ hκ
      calc 1 ≤ κ ^ 2 := this
        _ ≤ κ ^ 2 * P.card := Nat.le_mul_of_pos_right _ (by omega)
    · omega

/-- **The first hole, at a vertex all of whose neighbours are terminals**: the vertex is the
separator, and the pendant edge of `x` to a terminal of degree one is split off. -/
lemma splitOK_pendant {S T : Finset V} {κ η : ℕ} {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) {x : D} (hx : x ∈ pdarts M P Hs) (hv : M.tail x ∉ S ∪ T ∪ hunion Hs)
    (hw : M.head x ∈ S ∪ T) (hwH : M.head x ∉ hunion Hs)
    (hdeg : ∀ d ∈ P, M.tail d = M.head x → d = M.rev x) (hcard : 2 < P.card) :
    SplitOK M S T κ η P Hs (P \ {x, M.rev x}) {x, M.rev x}
      (SPath.point (M' := M) x (M.tail x)).toSep := by
  have hxP : x ∈ P := (mem_pdarts.1 hx).1
  have hm : (SPath.point (M' := M) x (M.tail x)).toSep.path.mverts = {M.tail x} :=
    HPath.toH_point_mverts x _
  have hvH : M.tail x ∉ hunion Hs := fun h => hv (mem_union_right _ h)
  have hdisj : Disjoint (SPath.point (M' := M) x (M.tail x)).verts (hunion Hs) := by
    rw [SPath.point_verts]; exact disjoint_singleton_left.2 hvH
  refine ⟨union_sdiff_pair hxP hP.rev, disjoint_sdiff_self_left,
    card_sdiff_pair_pos hxP hP.rev hcard, card_pair_pos x, ?_, ?_, SPath.toSep_segOK _ hdisj,
    SPath.toH_simple _ hdisj, ?_, ?_, ?_, revClosed_sdiff_pair hP.rev x, revClosed_pair x,
    (hP.conn.sdiff_pendant hxP hwH hvH hdeg).coarse (coarse_childHoles _ _)
      (pairwise_childHoles hP.disj), hConn_pair x _⟩
  · refine (bd_subset_pair _ x).trans fun v hv' => ?_
    simp only [mem_insert, mem_singleton] at hv'
    rcases hv' with rfl | rfl
    · rw [hm]; exact mem_union_right _ (mem_union_right _ (mem_singleton_self _))
    · exact mem_union_left _ hw
  · rw [hm]; exact disjoint_singleton_left.2 fun h => hv (mem_union_left _ h)
  · intro e he; rw [SPath.toSep_darts, SPath.point_darts'] at he; simp at he
  · intro σ hσ
    rw [show σ = SPath.point (M' := M) x (M.tail x) by simpa [SPath.toSep] using hσ]
    exact ⟨fun e he => by simp [SPath.point_darts'] at he, x, hxP, rfl⟩
  · refine ⟨by simp [SPath.toSep], fun σ hσ => ?_⟩
    rw [show σ = SPath.point (M' := M) x (M.tail x) by simpa [SPath.toSep] using hσ]
    simp [SPath.point]

/-- The separator of no dart at a hole vertex, with no part off the holes. -/
def holeSep (y : D) (a : V) : HSep M := ⟨(SPath.point y a).toH, []⟩

/-- **Splitting off the darts inside the holes** when no dart of the piece map leaves a hole: the
separator is a vertex of a hole. -/
lemma splitOK_dump {S T : Finset V} {κ η : ℕ} {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) {y : D} (hyP : y ∈ P) (hy : M.tail y ∈ hunion Hs)
    (hyn : y ∉ pdarts M P Hs) {x : D} (hx : x ∈ pdarts M P Hs) :
    SplitOK M S T κ η P Hs (pdarts M P Hs) (P \ pdarts M P Hs) (holeSep y (M.tail y)) := by
  have hm : (holeSep (M := M) y (M.tail y)).path.mverts = {M.tail y} :=
    HPath.toH_point_mverts y _
  have hinner : ∀ d ∈ P \ pdarts M P Hs, Inner M Hs d := fun d hd => by
    rw [mem_sdiff, mem_pdarts] at hd; push Not at hd; exact hd.2 hd.1
  have hco := hP.conn.coarse (coarse_childHoles Hs (holeSep (M := M) y (M.tail y)).path.mverts)
    (pairwise_childHoles hP.disj)
  set ch := childHoles Hs (holeSep (M := M) y (M.tail y)).path.mverts
  have hcoar := coarse_childHoles Hs (holeSep (M := M) y (M.tail y)).path.mverts
  refine ⟨union_sdiff_of_subset (pdarts_subset _ _), disjoint_sdiff, card_pos.2 ⟨x, hx⟩,
    card_pos.2 ⟨y, mem_sdiff.2 ⟨hyP, hyn⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun d hd => stable_pdarts hP.rev Hs d hd, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨-, d, hd, rfl⟩ := mem_bd.1 hv
    obtain ⟨H, hH, h1, -⟩ := hinner d hd
    exact mem_union_right _ (mem_union_left _ (subset_hunion hH h1))
  · rw [hm]; exact disjoint_singleton_left.2 fun h => disjoint_left.1 hP.term hy h
  · refine ⟨fun σ hσ => by simp [holeSep] at hσ, List.Pairwise.nil, ?_⟩
    rw [hm]; simp only [holeSep, List.map_nil, hunion_nil', union_empty]
    exact (union_eq_left.2 (singleton_subset_iff.2 hy)).symm
  · exact ⟨fun j hj => by simp [holeSep, SPath.toH, SPath.point] at hj,
      fun i hi j hj _ => by simp [holeSep, SPath.toH, SPath.point] at hi hj; omega⟩
  · intro e he
    simp [holeSep, SPath.toH_darts, SPath.point_darts'] at he
  · intro σ hσ; simp [holeSep] at hσ
  · exact ⟨by simp [holeSep], fun σ hσ => by simp [holeSep] at hσ⟩
  · intro d hd
    have h1 := hinner d hd
    rw [mem_sdiff, mem_pdarts] at hd ⊢
    exact ⟨hP.rev d hd.1, fun h => h.2 (inner_rev.2 h1)⟩
  · refine hco.of_pdarts_eq ?_
    ext d
    simp only [mem_pdarts]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, fun h' => h.2 (hcoar.inner h')⟩, h.2⟩⟩
  · refine hConn_of_pdarts_eq_empty ?_
    ext d
    simp only [mem_pdarts, Finset.notMem_empty, iff_false, not_and, not_not]
    exact fun hd => hcoar.inner (hinner d hd)

lemma nTouch_eq_zero {P : Finset D} {Hs : List (Finset V)}
    (h : ∀ d ∈ P, M.tail d ∉ hunion Hs) : nTouch M P Hs = 0 := by
  unfold nTouch
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro H hH
  simp only [decide_eq_true_eq, not_exists, not_and]
  rintro v hv ⟨d, hd, rfl⟩
  exact h d hd (subset_hunion hH hv)

/-- **Small pieces**: every piece meeting `PcOK` (with at most `η ≥ 1` holes touching it) has a
decomposition meeting `BalA` for every flag, on a map without loops whose terminals have degree at
most one: the vertices off the terminals and the holes are merged into the holes one at a time
(`splitOK_peel`), each step splitting off one edge as a leaf; the first hole is an edge or a
vertex (`splitOK_edge`, `splitOK_pendant`); the darts inside the holes are split off when no dart
of the piece map leaves a hole (`splitOK_dump`). All the splits are of pieces of at most `s`
darts, so they are balanced in size in the sense of `ADec.SizeBal`. -/
theorem exists_decOK_small {S T : Finset V} {κ η s : ℕ} (hκ : 1 ≤ κ) (hη : 1 ≤ η)
    (hloop : ∀ d, M.head d ≠ M.tail d)
    (hdeg : ∀ t ∈ S ∪ T, ∀ d d', M.tail d = t → M.tail d' = t → d = d') :
    ∀ (n : ℕ) (P : Finset D) (Hs : List (Finset V)), P.card = n → PcOK M S T P Hs →
      P.card ≤ s → nTouch M P Hs ≤ η → ∃ τ : ADec M, ∀ b, DecOK M S T κ η s P Hs b τ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Hs hn hP hs ht
  by_cases hL : P.card ≤ 2 ∨ ∀ d ∈ pdarts M P Hs, M.tail d ∈ S ∪ T ∪ hunion Hs
  · exact ⟨_, decOK_leaf hP hL⟩
  push Not at hL
  obtain ⟨hcard, d₀, hd₀, hbad⟩ := hL
  by_cases hB1 : ∃ x ∈ pdarts M P Hs, M.tail x ∉ S ∪ T ∪ hunion Hs ∧ M.head x ∈ hunion Hs
  · -- merge a vertex next to a hole into the hole
    obtain ⟨x, hx, hv, ha⟩ := hB1
    have hne : M.head x ≠ M.tail x := fun e => hv (mem_union_right _ (e ▸ ha))
    have h := splitOK_peel (κ := κ) (η := η) hP hx hv ha hcard hne
    have hm : (peelSep x hne).path.mverts = {M.tail x, M.head x} :=
      HPath.toH_ofDart_mverts x hne
    obtain ⟨H, hH, haH⟩ := mem_hunion.1 ha
    have htl : nTouch M (P \ {x, M.rev x}) (childHoles Hs (peelSep x hne).path.mverts) ≤ η :=
      (nTouch_childHoles_le_of_meet sdiff_subset hH
        ⟨M.head x, haH, M.rev x, hP.rev _ (mem_pdarts.1 hx).1, by rw [CombMap.tail_rev]⟩
        (by rw [hm]; exact not_disjoint_iff.2 ⟨M.head x, haH, by simp⟩)).trans ht
    obtain ⟨τl, hτl⟩ := ih _ (hn ▸ h.card_l_lt) _ _ rfl (h.pcOK_l hP)
      ((card_le_card sdiff_subset).trans hs) htl
    exact ⟨_, decOK_node_leaf h hP hs ht (Or.inl card_le_two) hτl⟩
  push Not at hB1
  by_cases hB2 : ∃ y ∈ pdarts M P Hs, M.tail y ∈ hunion Hs
  · obtain ⟨y, hy, hyH⟩ := hB2
    exact absurd (tail_mem_of_no_peel hdeg hP hB1 hy hyH d₀ hd₀) hbad
  push Not at hB2
  by_cases hB3 : ∃ y ∈ P, M.tail y ∈ hunion Hs
  · -- split off the darts inside the holes
    obtain ⟨y, hyP, hyH⟩ := hB3
    have hyn : y ∉ pdarts M P Hs := fun h => hB2 y h hyH
    have h := splitOK_dump (κ := κ) (η := η) hP hyP hyH hyn hd₀
    obtain ⟨H, hH, hyH'⟩ := mem_hunion.1 hyH
    have hm : (holeSep (M := M) y (M.tail y)).path.mverts = {M.tail y} :=
      HPath.toH_point_mverts y _
    have htl : nTouch M (pdarts M P Hs)
        (childHoles Hs (holeSep (M := M) y (M.tail y)).path.mverts) ≤ η :=
      (nTouch_childHoles_le_of_meet (pdarts_subset _ _) hH ⟨_, hyH', y, hyP, rfl⟩
        (by rw [hm]; exact not_disjoint_iff.2 ⟨_, hyH', mem_singleton_self _⟩)).trans ht
    obtain ⟨τl, hτl⟩ := ih _ (hn ▸ h.card_l_lt) _ _ rfl (h.pcOK_l hP)
      ((card_le_card (pdarts_subset _ _)).trans hs) htl
    refine ⟨_, decOK_node_leaf h hP hs ht (Or.inr fun d hd => ?_) hτl⟩
    exfalso
    rw [mem_pdarts, mem_sdiff, mem_pdarts] at hd
    obtain ⟨⟨hdP, hdn⟩, hdi⟩ := hd
    push Not at hdn
    exact hdi ((coarse_childHoles _ _).inner (hdn hdP))
  push Not at hB3
  -- no dart touches a hole: the first hole
  have hnt : nTouch M P Hs = 0 := nTouch_eq_zero hB3
  have hwH : M.head d₀ ∉ hunion Hs := by
    rw [← CombMap.tail_rev]; exact hB3 _ (hP.rev _ (mem_pdarts.1 hd₀).1)
  by_cases hw : M.head d₀ ∈ S ∪ T
  · have hdegw : ∀ d ∈ P, M.tail d = M.head d₀ → d = M.rev d₀ := fun d _ e =>
      hdeg _ hw d (M.rev d₀) e (by rw [CombMap.tail_rev])
    have h := splitOK_pendant (κ := κ) (η := η) hP hd₀ hbad hw hwH hdegw hcard
    have htl := nTouch_childHoles_le (M := M) (sdiff_subset (s := P) (t := {d₀, M.rev d₀})) Hs
      (SPath.point (M' := M) d₀ (M.tail d₀)).toSep.path.mverts
    obtain ⟨τl, hτl⟩ := ih _ (hn ▸ h.card_l_lt) _ _ rfl (h.pcOK_l hP)
      ((card_le_card sdiff_subset).trans hs) (by omega)
    exact ⟨_, decOK_node_leaf h hP hs ht (Or.inl card_le_two) hτl⟩
  · have hwbad : M.head d₀ ∉ S ∪ T ∪ hunion Hs := by
      rw [mem_union, not_or]; exact ⟨hw, hwH⟩
    have h := splitOK_edge (κ := κ) (η := η) hκ hP hd₀ hbad hwbad hcard (hloop d₀)
    have htl := nTouch_childHoles_le (M := M) (sdiff_subset (s := P) (t := {d₀, M.rev d₀})) Hs
      (SPath.ofDart d₀ (hloop d₀)).toSep.path.mverts
    obtain ⟨τl, hτl⟩ := ih _ (hn ▸ h.card_l_lt) _ _ rfl (h.pcOK_l hP)
      ((card_le_card sdiff_subset).trans hs) (by omega)
    exact ⟨_, decOK_node_leaf h hP hs ht (Or.inl card_le_two) hτl⟩

/-- The whole map is a piece meeting `PcOK`. -/
lemma pcOK_univ (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) (S T : Finset V) :
    PcOK M S T univ [] := by
  refine ⟨fun _ _ => mem_univ _, ?_, List.Pairwise.nil, by simp [hunion_nil']⟩
  by_cases hD : Nonempty D
  · exact ADec.hConn_univ hM hrot hface hD
  · intro x; exact absurd ⟨x⟩ hD

/-- **`BalDecA` from splits of the large pieces**: on a plane map without loops with transitive
rotations and faces whose terminals have degree at most one, if every large piece meeting `PcOK`
and a property `Inv` of the pieces (holding for the whole map) has the splits `hsize` and `hhole`
of `exists_decOK_of_split`, then a decomposition meeting `BalDecA` with `η = 6` exists. The
pieces of at most `s` darts are decomposed by `exists_decOK_small`. -/
theorem exists_balDecA_of_split (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (hloop : ∀ d, M.head d ≠ M.tail d) {S T : Finset V}
    (hdeg : ∀ t ∈ S ∪ T, ∀ d d', M.tail d = t → M.tail d' = t → d = d') {κ s : ℕ} (hκ : 1 ≤ κ)
    (Inv : Finset D → List (Finset V) → Prop) (hroot : Inv univ [])
    (hsize : ∀ P Hs, PcOK M S T P Hs → Inv P Hs → s < P.card → nTouch M P Hs ≤ 5 →
      ∃ l r π, SplitOK M S T κ 6 P Hs l r π ∧ Inv l (childHoles Hs π.path.mverts) ∧
        Inv r (childHoles Hs π.path.mverts) ∧ 4 * l.card ≤ 3 * P.card ∧ 4 * r.card ≤ 3 * P.card)
    (hhole : ∀ P Hs, PcOK M S T P Hs → Inv P Hs → s < P.card → nTouch M P Hs = 6 →
      ∃ l r π, SplitOK M S T κ 6 P Hs l r π ∧ Inv l (childHoles Hs π.path.mverts) ∧
        Inv r (childHoles Hs π.path.mverts) ∧ nTouch M l (childHoles Hs π.path.mverts) ≤ 5 ∧
          nTouch M r (childHoles Hs π.path.mverts) ≤ 5) :
    ∃ τ : ADec M, BalDecA M S T κ 6 s τ := by
  have h := exists_decOK_of_split (M := M) (S := S) (T := T) (κ := κ) (s := s) Inv
    (fun P Hs hP hs ht => exists_decOK_small hκ (by norm_num) hloop hdeg _ P Hs rfl hP hs ht)
    hsize hhole _ univ [] true rfl (pcOK_univ hM hrot hface S T) hroot (by simp [nTouch])
  exact h

end BKMNW

end PlanarFlow
