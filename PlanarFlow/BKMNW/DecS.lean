module

public import PlanarFlow.BKMNW.DecA

/-!
# The decomposition of split functions with a state carried down the recursion

`PlanarFlow.BKMNW.decA` passes only the piece and its holes `(P, Hs)` to the split subroutines.
The split chain of `PlanarFlow.BKMNW.SplitD` also needs the rotation of the piece map of the core,
which is not a function of `(P, Hs)` (see `PlanarFlow/BKMNW/SplitRot.lean`): a program carries it
down the recursion. Here `decS` is `decA` with a state `σ : St` passed to the subroutines and a
function `chS` computing the state of each child from the parent's state, the separator and the
child's darts; the specification `SplitFnsS` asks the children's invariant for these states.

* `decS`, `decS_split`, `decS_small`;
* **`decS_decOK`**, **`decS_balDecA`** (from an initial state meeting the invariant at the whole
  map), `decS_balDecA_of_isEmpty`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F} {St : Type*}

variable (M) in
/-- **The decomposition of split functions with a state**: `decA` where the subroutines also
read a state `σ`, the children's states given by `chS P Hs σ π X`. -/
noncomputable def decS (spS spH : Finset D → List (Finset V) → St → SplitAns M)
    (sm : Finset D → List (Finset V) → ADec M)
    (chS : Finset D → List (Finset V) → St → HSep M → Finset D → St) (s : ℕ) (P : Finset D)
    (Hs : List (Finset V)) (σ : St) (b : Bool) : ADec M :=
  if P.card ≤ s then sm P Hs else
    match (if holeStep M P Hs b then spH P Hs σ else spS P Hs σ) with
    | none => .leaf P
    | some (l, r, π) =>
      if _h : l.card < P.card ∧ r.card < P.card then
        .node (decS spS spH sm chS s l (childHoles Hs π.path.mverts) (chS P Hs σ π l)
            (!holeStep M P Hs b))
          (decS spS spH sm chS s r (childHoles Hs π.path.mverts) (chS P Hs σ π r)
            (!holeStep M P Hs b)) π
      else .leaf P
termination_by P.card
decreasing_by
  · exact _h.1
  · exact _h.2

/-- The unfolding of `decS` at a large piece whose subroutine answers a smaller split. -/
lemma decS_split {spS spH : Finset D → List (Finset V) → St → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M}
    {chS : Finset D → List (Finset V) → St → HSep M → Finset D → St} {s : ℕ} {P : Finset D}
    {Hs : List (Finset V)} {σ : St} {b : Bool} (hs : s < P.card) {l r : Finset D} {π : HSep M}
    (he : (if holeStep M P Hs b then spH P Hs σ else spS P Hs σ) = some (l, r, π))
    (hl : l.card < P.card) (hr : r.card < P.card) :
    decS M spS spH sm chS s P Hs σ b =
      .node (decS M spS spH sm chS s l (childHoles Hs π.path.mverts) (chS P Hs σ π l)
          (!holeStep M P Hs b))
        (decS M spS spH sm chS s r (childHoles Hs π.path.mverts) (chS P Hs σ π r)
          (!holeStep M P Hs b)) π := by
  rw [decS]
  have hs' : ¬ P.card ≤ s := by omega
  simp only [hs', ↓reduceIte]
  split
  · rename_i h; rw [he] at h; cases h
  · rename_i l' r' π' h
    rw [he] at h
    cases h
    simp only [hl, hr, and_self, ↓reduceDIte]

/-- The unfolding of `decS` at a small piece. -/
lemma decS_small {spS spH : Finset D → List (Finset V) → St → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M}
    {chS : Finset D → List (Finset V) → St → HSep M → Finset D → St} {s : ℕ} {P : Finset D}
    {Hs : List (Finset V)} {σ : St} {b : Bool} (hs : P.card ≤ s) :
    decS M spS spH sm chS s P Hs σ b = sm P Hs := by
  rw [decS]; simp only [hs, ↓reduceIte]

variable (M) in
/-- **The specification of the subroutines of `decS`**: `SplitFns` with an invariant of the
pieces and their states, the children's invariant holding for the states `chS`. -/
structure SplitFnsS (S T : Finset V) (κ s : ℕ) (Inv : Finset D → List (Finset V) → St → Prop)
    (spS spH : Finset D → List (Finset V) → St → SplitAns M)
    (sm : Finset D → List (Finset V) → ADec M)
    (chS : Finset D → List (Finset V) → St → HSep M → Finset D → St) : Prop where
  small : ∀ P Hs, PcOK M S T P Hs → P.card ≤ s → nTouch M P Hs ≤ 6 →
    ∀ b, DecOK M S T κ 6 s P Hs b (sm P Hs)
  size : ∀ P Hs σ, PcOK M S T P Hs → Inv P Hs σ → s < P.card → nTouch M P Hs ≤ 5 →
    ∃ l r π, spS P Hs σ = some (l, r, π) ∧ SplitOK M S T κ 6 P Hs l r π ∧
      Inv l (childHoles Hs π.path.mverts) (chS P Hs σ π l) ∧
      Inv r (childHoles Hs π.path.mverts) (chS P Hs σ π r) ∧
      4 * l.card ≤ 3 * P.card ∧ 4 * r.card ≤ 3 * P.card
  hole : ∀ P Hs σ, PcOK M S T P Hs → Inv P Hs σ → s < P.card → nTouch M P Hs = 6 →
    ∃ l r π, spH P Hs σ = some (l, r, π) ∧ SplitOK M S T κ 6 P Hs l r π ∧
      Inv l (childHoles Hs π.path.mverts) (chS P Hs σ π l) ∧
      Inv r (childHoles Hs π.path.mverts) (chS P Hs σ π r) ∧
      nTouch M l (childHoles Hs π.path.mverts) ≤ 5 ∧ nTouch M r (childHoles Hs π.path.mverts) ≤ 5

/-- **The decomposition with a state meets `DecOK`** on every piece of the recursion whose state
meets the invariant. -/
theorem decS_decOK {S T : Finset V} {κ s : ℕ} {Inv : Finset D → List (Finset V) → St → Prop}
    {spS spH : Finset D → List (Finset V) → St → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M}
    {chS : Finset D → List (Finset V) → St → HSep M → Finset D → St}
    (hF : SplitFnsS M S T κ s Inv spS spH sm chS) :
    ∀ (n : ℕ) (P : Finset D) (Hs : List (Finset V)) (σ : St) (b : Bool), P.card = n →
      PcOK M S T P Hs → Inv P Hs σ → nTouch M P Hs ≤ (if b then 6 else 5) →
        DecOK M S T κ 6 s P Hs b (decS M spS spH sm chS s P Hs σ b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Hs σ b hn hP hI ht
  by_cases hs : P.card ≤ s
  · rw [decS_small hs]
    exact hF.small P Hs hP hs (by split_ifs at ht <;> omega) b
  push Not at hs
  by_cases hh : b = true ∧ nTouch M P Hs = 6
  · obtain ⟨hb, h6⟩ := hh
    have hst : holeStep M P Hs b = true := by simp [holeStep, hb, h6]
    obtain ⟨l, r, π, he, h, il, ir, tl, tr⟩ := hF.hole P Hs σ hP hI hs h6
    have he' : (if holeStep M P Hs b then spH P Hs σ else spS P Hs σ) = some (l, r, π) := by
      rw [hst]; exact he
    rw [decS_split hs he' h.card_l_lt h.card_r_lt, hst, Bool.not_true]
    obtain ⟨pl, gl, ql, ol, bl⟩ := ih _ (hn ▸ h.card_l_lt) l _ _ false rfl (h.pcOK_l hP) il
      (by simpa using tl)
    obtain ⟨pr, gr, qr, or, br⟩ := ih _ (hn ▸ h.card_r_lt) r _ _ false rfl (h.pcOK_r hP) ir
      (by simpa using tr)
    obtain ⟨e, g, q, o⟩ := h.node hP.conn pl pr gl gr ql qr ol or
    refine ⟨e, g, q, o, ?_⟩
    refine ⟨by rw [pl, pr]; exact h.disj, by rw [pl]; exact h.lpos, by rw [pr]; exact h.rpos,
      by rw [pl, pr, h.union]; exact h.short, by rw [pl, pr, h.union]; omega,
      Or.inr ⟨hb, bl, br⟩⟩
  · have h5 : nTouch M P Hs ≤ 5 := by
      cases b
      · simpa using ht
      · simp only [ite_true] at ht; simp only [true_and] at hh; omega
    have hst : holeStep M P Hs b = false := by
      simp only [holeStep, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      cases b
      · exact Or.inl rfl
      · exact Or.inr (by omega)
    obtain ⟨l, r, π, he, h, il, ir, sl, sr⟩ := hF.size P Hs σ hP hI hs h5
    have he' : (if holeStep M P Hs b then spH P Hs σ else spS P Hs σ) = some (l, r, π) := by
      rw [hst]; exact he
    rw [decS_split hs he' h.card_l_lt h.card_r_lt, hst, Bool.not_false]
    have tl := nTouch_childHoles_le (M := M) (h.union ▸ subset_union_left) Hs π.path.mverts
    have tr := nTouch_childHoles_le (M := M) (h.union ▸ subset_union_right) Hs π.path.mverts
    obtain ⟨pl, gl, ql, ol, bl⟩ := ih _ (hn ▸ h.card_l_lt) l _ _ true rfl (h.pcOK_l hP) il
      (by simp only [ite_true]; omega)
    obtain ⟨pr, gr, qr, or, br⟩ := ih _ (hn ▸ h.card_r_lt) r _ _ true rfl (h.pcOK_r hP) ir
      (by simp only [ite_true]; omega)
    obtain ⟨e, g, q, o⟩ := h.node hP.conn pl pr gl gr ql qr ol or
    refine ⟨e, g, q, o, ?_⟩
    refine ⟨by rw [pl, pr]; exact h.disj, by rw [pl]; exact h.lpos, by rw [pr]; exact h.rpos,
      by rw [pl, pr, h.union]; exact h.short, by rw [pl, pr, h.union]; omega,
      Or.inl ⟨Or.inr ⟨by rw [pl, pr, h.union]; exact sl, by rw [pl, pr, h.union]; exact sr⟩,
        bl, br⟩⟩

/-- **`BalDecA` for the decomposition with a state**: on a plane map with transitive rotations
and faces, for subroutines meeting `SplitFnsS` and an initial state meeting the invariant at the
whole map, `decS` from the whole map (no hole, flag `true`) meets `BalDecA` with `η = 6`. -/
theorem decS_balDecA (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {S T : Finset V} {κ s : ℕ} {Inv : Finset D → List (Finset V) → St → Prop}
    {spS spH : Finset D → List (Finset V) → St → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M}
    {chS : Finset D → List (Finset V) → St → HSep M → Finset D → St}
    (hF : SplitFnsS M S T κ s Inv spS spH sm chS) {σ₀ : St} (hroot : Inv univ [] σ₀) :
    BalDecA M S T κ 6 s (decS M spS spH sm chS s univ [] σ₀ true) :=
  decS_decOK hF _ univ [] σ₀ true rfl (pcOK_univ hM hrot hface S T) hroot (by simp [nTouch])

/-- **`BalDecA` for the decomposition with a state on a map without darts** (no hypothesis on
the map, the invariant or the state). -/
theorem decS_balDecA_of_isEmpty [IsEmpty D] {S T : Finset V} {κ s : ℕ}
    {Inv : Finset D → List (Finset V) → St → Prop}
    {spS spH : Finset D → List (Finset V) → St → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M}
    {chS : Finset D → List (Finset V) → St → HSep M → Finset D → St}
    (hF : SplitFnsS M S T κ s Inv spS spH sm chS) (σ₀ : St) :
    BalDecA M S T κ 6 s (decS M spS spH sm chS s univ [] σ₀ true) := by
  have h0 : (univ : Finset D).card ≤ s := by simp
  rw [decS_small h0]
  exact hF.small univ [] (pcOK_univ_of_isEmpty S T) h0 (by simp [nTouch]) true

end BKMNW

end PlanarFlow
