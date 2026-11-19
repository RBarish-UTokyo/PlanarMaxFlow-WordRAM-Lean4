module

public import PlanarFlow.BKMNW.Exist

/-!
# The decomposition of split functions: a deterministic `BalDecA`

The existence proof of a decomposition meeting `PlanarFlow.BKMNW.BalDecA`
(`PlanarFlow.BKMNW.exists_decOK_of_split`) picks the split of every large piece by an existence
statement. Here the decomposition is **a function of three subroutines**: a split balanced in
size `spS`, a split balanced in the number of holes `spH` (each answering `none` or a split
`(l, r, π)` of a piece `P` with holes `Hs`) and a decomposition `sm` of the small pieces. The
recursion `decA spS spH sm s` follows the alternation of the article (line 2 of Algorithm 1): a
piece of at most `s` darts is decomposed by `sm`; a larger piece is split by `spH` if six holes
touch it and the previous split was balanced in size (flag `b`), by `spS` otherwise, and the two
children recursed with the flag of the split.

The specification `SplitFns` asks the subroutines for their answers **only on the pieces of the
recursion**: pieces meeting `PcOK` and an invariant `Inv` (for the preprocessed map, `CInv` of
`PlanarFlow/BKMNW/ExistSplit.lean`). This is a restriction of the separator specification that is
necessary (`SepSpec`, which asks for a split of
every piece, cannot be met), and it is exactly the hypothesis of `exists_decOK_of_split`, for given
functions instead of an existence.

* `decA`, `piece_decA`;
* **`decA_decOK`**: for subroutines meeting `SplitFns`, `decA` meets `DecOK` on every piece of the
  recursion; **`decA_balDecA`**: from the root, `BalDecA` with `η = 6`;
* `splitFns_choose` (`exists_splitFns`): subroutines meeting `SplitFns` exist as soon as the
  splits exist (`Classical.choose`), so the specification is satisfiable whenever
  `exists_decOK_of_split` applies.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-- The answer type of a split subroutine: `none`, or the two children and the separator. -/
abbrev SplitAns (M : CombMap D V F) := Option (Finset D × Finset D × HSep M)

variable (M) in
/-- The test of the alternation: the split is balanced in the number of holes iff the previous
split was balanced in size (`b`) and six holes touch the piece. -/
noncomputable def holeStep (P : Finset D) (Hs : List (Finset V)) (b : Bool) : Bool :=
  b && decide (nTouch M P Hs = 6)

variable (M) in
/-- **The decomposition of split functions**: a piece of at most `s` darts decomposed by `sm`;
a larger piece split by `spH` (if `holeStep`) or `spS` (otherwise), the children recursed with
the flag `!holeStep` (a split balanced in size frees the next one); a leaf when the subroutine
answers `none` or a child that is not smaller. -/
noncomputable def decA (spS spH : Finset D → List (Finset V) → SplitAns M)
    (sm : Finset D → List (Finset V) → ADec M) (s : ℕ) (P : Finset D) (Hs : List (Finset V))
    (b : Bool) : ADec M :=
  if P.card ≤ s then sm P Hs else
    match (if holeStep M P Hs b then spH P Hs else spS P Hs) with
    | none => .leaf P
    | some (l, r, π) =>
      if _h : l.card < P.card ∧ r.card < P.card then
        .node (decA spS spH sm s l (childHoles Hs π.path.mverts) (!holeStep M P Hs b))
          (decA spS spH sm s r (childHoles Hs π.path.mverts) (!holeStep M P Hs b)) π
      else .leaf P
termination_by P.card
decreasing_by
  · exact _h.1
  · exact _h.2

/-- The unfolding of `decA` at a large piece whose subroutine answers a smaller split. -/
lemma decA_split {spS spH : Finset D → List (Finset V) → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M} {s : ℕ} {P : Finset D} {Hs : List (Finset V)}
    {b : Bool} (hs : s < P.card) {l r : Finset D} {π : HSep M}
    (he : (if holeStep M P Hs b then spH P Hs else spS P Hs) = some (l, r, π))
    (hl : l.card < P.card) (hr : r.card < P.card) :
    decA M spS spH sm s P Hs b =
      .node (decA M spS spH sm s l (childHoles Hs π.path.mverts) (!holeStep M P Hs b))
        (decA M spS spH sm s r (childHoles Hs π.path.mverts) (!holeStep M P Hs b)) π := by
  rw [decA]
  have hs' : ¬ P.card ≤ s := by omega
  simp only [hs', ↓reduceIte]
  split
  · rename_i h; rw [he] at h; cases h
  · rename_i l' r' π' h
    rw [he] at h
    cases h
    simp only [hl, hr, and_self, ↓reduceDIte]

/-- The unfolding of `decA` at a small piece. -/
lemma decA_small {spS spH : Finset D → List (Finset V) → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M} {s : ℕ} {P : Finset D} {Hs : List (Finset V)}
    {b : Bool} (hs : P.card ≤ s) : decA M spS spH sm s P Hs b = sm P Hs := by
  rw [decA]; simp only [hs, ↓reduceIte]

variable (M) in
/-- **The specification of the subroutines of `decA`**, on the pieces of the recursion only
(`PcOK` and the invariant `Inv`): `sm` decomposes every small piece touching at most six holes
(for every flag), `spS` splits every large piece touching at most five holes into children of at
most three quarters of its darts, and `spH` every large piece touching six holes into children
touching at most five holes each, the children meeting `Inv`. -/
structure SplitFns (S T : Finset V) (κ s : ℕ) (Inv : Finset D → List (Finset V) → Prop)
    (spS spH : Finset D → List (Finset V) → SplitAns M)
    (sm : Finset D → List (Finset V) → ADec M) : Prop where
  small : ∀ P Hs, PcOK M S T P Hs → P.card ≤ s → nTouch M P Hs ≤ 6 →
    ∀ b, DecOK M S T κ 6 s P Hs b (sm P Hs)
  size : ∀ P Hs, PcOK M S T P Hs → Inv P Hs → s < P.card → nTouch M P Hs ≤ 5 →
    ∃ l r π, spS P Hs = some (l, r, π) ∧ SplitOK M S T κ 6 P Hs l r π ∧
      Inv l (childHoles Hs π.path.mverts) ∧ Inv r (childHoles Hs π.path.mverts) ∧
      4 * l.card ≤ 3 * P.card ∧ 4 * r.card ≤ 3 * P.card
  hole : ∀ P Hs, PcOK M S T P Hs → Inv P Hs → s < P.card → nTouch M P Hs = 6 →
    ∃ l r π, spH P Hs = some (l, r, π) ∧ SplitOK M S T κ 6 P Hs l r π ∧
      Inv l (childHoles Hs π.path.mverts) ∧ Inv r (childHoles Hs π.path.mverts) ∧
      nTouch M l (childHoles Hs π.path.mverts) ≤ 5 ∧ nTouch M r (childHoles Hs π.path.mverts) ≤ 5

/-- **The decomposition of split functions meeting `SplitFns` meets `DecOK`** on every piece of
the recursion (the deterministic form of `exists_decOK_of_split`). -/
theorem decA_decOK {S T : Finset V} {κ s : ℕ} {Inv : Finset D → List (Finset V) → Prop}
    {spS spH : Finset D → List (Finset V) → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M} (hF : SplitFns M S T κ s Inv spS spH sm) :
    ∀ (n : ℕ) (P : Finset D) (Hs : List (Finset V)) (b : Bool), P.card = n → PcOK M S T P Hs →
      Inv P Hs → nTouch M P Hs ≤ (if b then 6 else 5) →
        DecOK M S T κ 6 s P Hs b (decA M spS spH sm s P Hs b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Hs b hn hP hI ht
  by_cases hs : P.card ≤ s
  · rw [decA_small hs]
    exact hF.small P Hs hP hs (by split_ifs at ht <;> omega) b
  push Not at hs
  by_cases hh : b = true ∧ nTouch M P Hs = 6
  · -- a split balanced in the number of holes
    obtain ⟨hb, h6⟩ := hh
    have hst : holeStep M P Hs b = true := by simp [holeStep, hb, h6]
    obtain ⟨l, r, π, he, h, il, ir, tl, tr⟩ := hF.hole P Hs hP hI hs h6
    have he' : (if holeStep M P Hs b then spH P Hs else spS P Hs) = some (l, r, π) := by
      rw [hst]; exact he
    rw [decA_split hs he' h.card_l_lt h.card_r_lt, hst, Bool.not_true]
    obtain ⟨pl, gl, ql, ol, bl⟩ := ih _ (hn ▸ h.card_l_lt) l _ false rfl (h.pcOK_l hP) il
      (by simpa using tl)
    obtain ⟨pr, gr, qr, or, br⟩ := ih _ (hn ▸ h.card_r_lt) r _ false rfl (h.pcOK_r hP) ir
      (by simpa using tr)
    obtain ⟨e, g, q, o⟩ := h.node hP.conn pl pr gl gr ql qr ol or
    refine ⟨e, g, q, o, ?_⟩
    refine ⟨by rw [pl, pr]; exact h.disj, by rw [pl]; exact h.lpos, by rw [pr]; exact h.rpos,
      by rw [pl, pr, h.union]; exact h.short, by rw [pl, pr, h.union]; omega,
      Or.inr ⟨hb, bl, br⟩⟩
  · -- a split balanced in size
    have h5 : nTouch M P Hs ≤ 5 := by
      cases b
      · simpa using ht
      · simp only [ite_true] at ht; simp only [true_and] at hh; omega
    have hst : holeStep M P Hs b = false := by
      simp only [holeStep, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      cases b
      · exact Or.inl rfl
      · exact Or.inr (by omega)
    obtain ⟨l, r, π, he, h, il, ir, sl, sr⟩ := hF.size P Hs hP hI hs h5
    have he' : (if holeStep M P Hs b then spH P Hs else spS P Hs) = some (l, r, π) := by
      rw [hst]; exact he
    rw [decA_split hs he' h.card_l_lt h.card_r_lt, hst, Bool.not_false]
    have tl := nTouch_childHoles_le (M := M) (h.union ▸ subset_union_left) Hs π.path.mverts
    have tr := nTouch_childHoles_le (M := M) (h.union ▸ subset_union_right) Hs π.path.mverts
    obtain ⟨pl, gl, ql, ol, bl⟩ := ih _ (hn ▸ h.card_l_lt) l _ true rfl (h.pcOK_l hP) il
      (by simp only [ite_true]; omega)
    obtain ⟨pr, gr, qr, or, br⟩ := ih _ (hn ▸ h.card_r_lt) r _ true rfl (h.pcOK_r hP) ir
      (by simp only [ite_true]; omega)
    obtain ⟨e, g, q, o⟩ := h.node hP.conn pl pr gl gr ql qr ol or
    refine ⟨e, g, q, o, ?_⟩
    refine ⟨by rw [pl, pr]; exact h.disj, by rw [pl]; exact h.lpos, by rw [pr]; exact h.rpos,
      by rw [pl, pr, h.union]; exact h.short, by rw [pl, pr, h.union]; omega,
      Or.inl ⟨Or.inr ⟨by rw [pl, pr, h.union]; exact sl, by rw [pl, pr, h.union]; exact sr⟩,
        bl, br⟩⟩

/-- **The piece of the decomposition of split functions** is the piece decomposed, on every
piece of the recursion. -/
theorem piece_decA {S T : Finset V} {κ s : ℕ} {Inv : Finset D → List (Finset V) → Prop}
    {spS spH : Finset D → List (Finset V) → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M} (hF : SplitFns M S T κ s Inv spS spH sm)
    {P : Finset D} {Hs : List (Finset V)} {b : Bool} (hP : PcOK M S T P Hs) (hI : Inv P Hs)
    (ht : nTouch M P Hs ≤ (if b then 6 else 5)) :
    (decA M spS spH sm s P Hs b).piece = P :=
  (decA_decOK hF _ P Hs b rfl hP hI ht).1

/-- The whole map is a piece meeting `PcOK` when it has no dart (no hypothesis on the map). -/
lemma pcOK_univ_of_isEmpty [IsEmpty D] (S T : Finset V) : PcOK M S T univ [] :=
  ⟨fun _ _ => mem_univ _, fun x => isEmptyElim x, List.Pairwise.nil, by simp [hunion_nil']⟩

/-- **`BalDecA` for the decomposition of split functions**: on a plane map with transitive
rotations and faces, for subroutines meeting `SplitFns` and an invariant holding at the whole map,
`decA` from the whole map (no hole, flag `true`) meets `BalDecA` with `η = 6`. -/
theorem decA_balDecA (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {S T : Finset V} {κ s : ℕ} {Inv : Finset D → List (Finset V) → Prop}
    {spS spH : Finset D → List (Finset V) → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M} (hF : SplitFns M S T κ s Inv spS spH sm)
    (hroot : Inv univ []) :
    BalDecA M S T κ 6 s (decA M spS spH sm s univ [] true) :=
  decA_decOK hF _ univ [] true rfl (pcOK_univ hM hrot hface S T) hroot (by simp [nTouch])

/-- **`BalDecA` for the decomposition of split functions on a map without darts**, with no
hypothesis on the map or the invariant (the whole map is small, decomposed by `sm`). -/
theorem decA_balDecA_of_isEmpty [IsEmpty D] {S T : Finset V} {κ s : ℕ}
    {Inv : Finset D → List (Finset V) → Prop}
    {spS spH : Finset D → List (Finset V) → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M} (hF : SplitFns M S T κ s Inv spS spH sm) :
    BalDecA M S T κ 6 s (decA M spS spH sm s univ [] true) := by
  have h0 : (univ : Finset D).card ≤ s := by simp
  rw [decA_small h0]
  exact hF.small univ [] (pcOK_univ_of_isEmpty S T) h0 (by simp [nTouch]) true

/-! ### Subroutines meeting the specification exist -/

section Choose

open Classical

variable (M) in
/-- The split balanced in size chosen by the existence statement (`none` where there is none). -/
noncomputable def spSC (S T : Finset V) (κ : ℕ) (Inv : Finset D → List (Finset V) → Prop)
    (P : Finset D) (Hs : List (Finset V)) : SplitAns M :=
  if h : ∃ x : Finset D × Finset D × HSep M, SplitOK M S T κ 6 P Hs x.1 x.2.1 x.2.2 ∧
      Inv x.1 (childHoles Hs x.2.2.path.mverts) ∧ Inv x.2.1 (childHoles Hs x.2.2.path.mverts) ∧
      4 * x.1.card ≤ 3 * P.card ∧ 4 * x.2.1.card ≤ 3 * P.card then some h.choose else none

variable (M) in
/-- The split balanced in the number of holes chosen by the existence statement. -/
noncomputable def spHC (S T : Finset V) (κ : ℕ) (Inv : Finset D → List (Finset V) → Prop)
    (P : Finset D) (Hs : List (Finset V)) : SplitAns M :=
  if h : ∃ x : Finset D × Finset D × HSep M, SplitOK M S T κ 6 P Hs x.1 x.2.1 x.2.2 ∧
      Inv x.1 (childHoles Hs x.2.2.path.mverts) ∧ Inv x.2.1 (childHoles Hs x.2.2.path.mverts) ∧
      nTouch M x.1 (childHoles Hs x.2.2.path.mverts) ≤ 5 ∧
      nTouch M x.2.1 (childHoles Hs x.2.2.path.mverts) ≤ 5 then some h.choose else none

variable (M) in
/-- The decomposition of a small piece chosen by the existence statement (a leaf where there is
none). -/
noncomputable def smC (S T : Finset V) (κ s : ℕ) (P : Finset D) (Hs : List (Finset V)) : ADec M :=
  if h : ∃ τ : ADec M, ∀ b, DecOK M S T κ 6 s P Hs b τ then h.choose else .leaf P

/-- **Subroutines meeting `SplitFns` exist** as soon as the splits and the decompositions of the
small pieces exist (the hypotheses of `exists_decOK_of_split`): the choices `spSC`, `spHC`, `smC`.
-/
theorem splitFns_choose {S T : Finset V} {κ s : ℕ} (Inv : Finset D → List (Finset V) → Prop)
    (hsmall : ∀ P Hs, PcOK M S T P Hs → P.card ≤ s → nTouch M P Hs ≤ 6 →
      ∃ τ : ADec M, ∀ b, DecOK M S T κ 6 s P Hs b τ)
    (hsize : ∀ P Hs, PcOK M S T P Hs → Inv P Hs → s < P.card → nTouch M P Hs ≤ 5 →
      ∃ l r π, SplitOK M S T κ 6 P Hs l r π ∧ Inv l (childHoles Hs π.path.mverts) ∧
        Inv r (childHoles Hs π.path.mverts) ∧ 4 * l.card ≤ 3 * P.card ∧ 4 * r.card ≤ 3 * P.card)
    (hhole : ∀ P Hs, PcOK M S T P Hs → Inv P Hs → s < P.card → nTouch M P Hs = 6 →
      ∃ l r π, SplitOK M S T κ 6 P Hs l r π ∧ Inv l (childHoles Hs π.path.mverts) ∧
        Inv r (childHoles Hs π.path.mverts) ∧ nTouch M l (childHoles Hs π.path.mverts) ≤ 5 ∧
          nTouch M r (childHoles Hs π.path.mverts) ≤ 5) :
    SplitFns M S T κ s Inv (spSC M S T κ Inv) (spHC M S T κ Inv) (smC M S T κ s) := by
  refine ⟨fun P Hs hP hs ht b => ?_, fun P Hs hP hI hs ht => ?_, fun P Hs hP hI hs ht => ?_⟩
  · have h := hsmall P Hs hP hs ht
    unfold smC
    rw [dite_eq_left_of_eq_true (eq_true h)]
    exact h.choose_spec b
  · obtain ⟨l, r, π, hx⟩ := hsize P Hs hP hI hs ht
    have h : ∃ x : Finset D × Finset D × HSep M, SplitOK M S T κ 6 P Hs x.1 x.2.1 x.2.2 ∧
        Inv x.1 (childHoles Hs x.2.2.path.mverts) ∧ Inv x.2.1 (childHoles Hs x.2.2.path.mverts) ∧
        4 * x.1.card ≤ 3 * P.card ∧ 4 * x.2.1.card ≤ 3 * P.card := ⟨(l, r, π), hx⟩
    refine ⟨h.choose.1, h.choose.2.1, h.choose.2.2, ?_, h.choose_spec⟩
    unfold spSC
    rw [dite_eq_left_of_eq_true (eq_true h)]
  · obtain ⟨l, r, π, hx⟩ := hhole P Hs hP hI hs ht
    have h : ∃ x : Finset D × Finset D × HSep M, SplitOK M S T κ 6 P Hs x.1 x.2.1 x.2.2 ∧
        Inv x.1 (childHoles Hs x.2.2.path.mverts) ∧ Inv x.2.1 (childHoles Hs x.2.2.path.mverts) ∧
        nTouch M x.1 (childHoles Hs x.2.2.path.mverts) ≤ 5 ∧
        nTouch M x.2.1 (childHoles Hs x.2.2.path.mverts) ≤ 5 := ⟨(l, r, π), hx⟩
    refine ⟨h.choose.1, h.choose.2.1, h.choose.2.2, ?_, h.choose_spec⟩
    unfold spHC
    rw [dite_eq_left_of_eq_true (eq_true h)]

end Choose

end BKMNW

end PlanarFlow
