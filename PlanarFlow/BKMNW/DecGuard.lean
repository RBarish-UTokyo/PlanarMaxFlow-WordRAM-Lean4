module

public import PlanarFlow.BKMNW.DecS

/-!
# Guarded split functions: the record of a call determines a valid state

A call `x` of the extended frame (`PlanarFlow/BKMNW/MfX.lean`) knows its state only through
`PhOk`: `x.1 = decS … x.1.piece Hs st b` for **some** `st`. With the plain split functions
(`spSR`, `spHR`) nothing forces that `st` to be a valid rotation (`CInvS`), and the programs of
the split chain (`scProg_exec_sepC`, …) need it (`PMap`). Here the split functions are
**guarded**: `guardS G sp P Hs σ = if G P Hs σ then sp P Hs σ else none`, with `G` the hypotheses
of the fields `size`/`hole` of `SplitFnsS` (`PcOK`, the invariant, `s < #P`, `nTouch`). Then

* **`splitFnsS_guard`**: the guarded functions meet `SplitFnsS` whenever the plain ones do (the
  guard holds wherever `SplitFnsS` asks for an answer), so the headline theorems apply to the
  guarded decomposition unchanged;
* `decS_cases` (the three shapes of one unfolding of `decS`), `guardS_some`;
* **`decS_piece_guard`**: `(decS (guardS …) (guardS …) sm chS s P Hs σ b).piece = P` for every
  reversal-closed `P` and **every** state `σ` (the piece of a child call is
  the dart set computed by its split);
* **`decS_node_guard`**: at a node of the guarded decomposition of a large piece, for any state
  `σ` producing it, the guard holds (`PcOK`, `Inv P Hs σ`, the `nTouch` bound), the plain split
  answers `(l, r, π)` with `SplitOK`, the children are the guarded decompositions of `l`, `r` with
  the states `chS P Hs σ π l`, `chS P Hs σ π r` and the flag `!holeStep`, and their pieces are
  `l`, `r`.
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
open Classical in
/-- **A guarded split function**: the answer of `sp` where `G` holds, `none` elsewhere. -/
noncomputable def guardS (G : Finset D → List (Finset V) → St → Prop)
    (sp : Finset D → List (Finset V) → St → SplitAns M) (P : Finset D) (Hs : List (Finset V))
    (σ : St) : SplitAns M :=
  if G P Hs σ then sp P Hs σ else none

variable (M) in
/-- The guard of the split by size: the hypotheses of the field `size` of `SplitFnsS`. -/
def gSz (S T : Finset V) (s : ℕ) (Inv : Finset D → List (Finset V) → St → Prop) (P : Finset D)
    (Hs : List (Finset V)) (σ : St) : Prop :=
  PcOK M S T P Hs ∧ Inv P Hs σ ∧ s < P.card ∧ nTouch M P Hs ≤ 5

variable (M) in
/-- The guard of the split by holes: the hypotheses of the field `hole` of `SplitFnsS`. -/
def gHl (S T : Finset V) (s : ℕ) (Inv : Finset D → List (Finset V) → St → Prop) (P : Finset D)
    (Hs : List (Finset V)) (σ : St) : Prop :=
  PcOK M S T P Hs ∧ Inv P Hs σ ∧ s < P.card ∧ nTouch M P Hs = 6

lemma guardS_pos {G : Finset D → List (Finset V) → St → Prop}
    {sp : Finset D → List (Finset V) → St → SplitAns M} {P : Finset D} {Hs : List (Finset V)}
    {σ : St} (h : G P Hs σ) : guardS M G sp P Hs σ = sp P Hs σ := by
  classical
  unfold guardS; simp only [h, ↓reduceIte]

lemma guardS_some {G : Finset D → List (Finset V) → St → Prop}
    {sp : Finset D → List (Finset V) → St → SplitAns M} {P : Finset D} {Hs : List (Finset V)}
    {σ : St} {x : Finset D × Finset D × HSep M} (h : guardS M G sp P Hs σ = some x) :
    G P Hs σ ∧ sp P Hs σ = some x := by
  classical
  unfold guardS at h
  by_cases hG : G P Hs σ
  · simp only [hG, ↓reduceIte] at h; exact ⟨hG, h⟩
  · simp only [hG, ↓reduceIte, reduceCtorEq] at h

/-- **The guarded functions meet `SplitFnsS`** whenever the plain ones do. -/
theorem splitFnsS_guard {S T : Finset V} {κ s : ℕ} {Inv : Finset D → List (Finset V) → St → Prop}
    {spS spH : Finset D → List (Finset V) → St → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M}
    {chS : Finset D → List (Finset V) → St → HSep M → Finset D → St}
    (hF : SplitFnsS M S T κ s Inv spS spH sm chS) :
    SplitFnsS M S T κ s Inv (guardS M (gSz M S T s Inv) spS) (guardS M (gHl M S T s Inv) spH)
      sm chS :=
  ⟨hF.small,
   fun P Hs σ hP hI hs ht => by
    rw [guardS_pos (sp := spS) ⟨hP, hI, hs, ht⟩]; exact hF.size P Hs σ hP hI hs ht,
   fun P Hs σ hP hI hs ht => by
    rw [guardS_pos (sp := spH) ⟨hP, hI, hs, ht⟩]; exact hF.hole P Hs σ hP hI hs ht⟩

/-- **The three shapes of one unfolding of `decS`**: a small piece (`sm`), a leaf, or a node from
a split answer with smaller parts. -/
lemma decS_cases (spS spH : Finset D → List (Finset V) → St → SplitAns M)
    (sm : Finset D → List (Finset V) → ADec M)
    (chS : Finset D → List (Finset V) → St → HSep M → Finset D → St) (s : ℕ) (P : Finset D)
    (Hs : List (Finset V)) (σ : St) (b : Bool) :
    (P.card ≤ s ∧ decS M spS spH sm chS s P Hs σ b = sm P Hs) ∨
    (s < P.card ∧ decS M spS spH sm chS s P Hs σ b = .leaf P) ∨
    ∃ l r π, s < P.card ∧
      (if holeStep M P Hs b then spH P Hs σ else spS P Hs σ) = some (l, r, π) ∧
      l.card < P.card ∧ r.card < P.card ∧
      decS M spS spH sm chS s P Hs σ b =
        .node (decS M spS spH sm chS s l (childHoles Hs π.path.mverts) (chS P Hs σ π l)
            (!holeStep M P Hs b))
          (decS M spS spH sm chS s r (childHoles Hs π.path.mverts) (chS P Hs σ π r)
            (!holeStep M P Hs b)) π := by
  by_cases hs : P.card ≤ s
  · exact Or.inl ⟨hs, decS_small hs⟩
  push Not at hs
  rcases he : (if holeStep M P Hs b then spH P Hs σ else spS P Hs σ) with _ | ⟨l, r, π⟩
  · refine Or.inr (Or.inl ⟨hs, ?_⟩)
    rw [decS]
    have hs' : ¬ P.card ≤ s := by omega
    simp only [hs', ↓reduceIte]
    split
    · rfl
    · rename_i l' r' π' h; rw [he] at h; cases h
  · by_cases hlr : l.card < P.card ∧ r.card < P.card
    · exact Or.inr (Or.inr ⟨l, r, π, hs, rfl, hlr.1, hlr.2, decS_split hs he hlr.1 hlr.2⟩)
    · refine Or.inr (Or.inl ⟨hs, ?_⟩)
      rw [decS]
      have hs' : ¬ P.card ≤ s := by omega
      simp only [hs', ↓reduceIte]
      split
      · rename_i h; rw [he] at h; try cases h
      · rename_i l' r' π' h
        rw [he] at h
        cases h
        simp only [hlr, ↓reduceDIte] at *

/-- One answer of the guarded functions: the guard holds and the plain function answers the
same, with `SplitOK`. -/
lemma guard_answer {S T : Finset V} {κ s : ℕ} {Inv : Finset D → List (Finset V) → St → Prop}
    {spS spH : Finset D → List (Finset V) → St → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M}
    {chS : Finset D → List (Finset V) → St → HSep M → Finset D → St}
    (hF : SplitFnsS M S T κ s Inv spS spH sm chS) {P : Finset D} {Hs : List (Finset V)}
    {σ : St} {b : Bool} {l r : Finset D} {π : HSep M}
    (he : (if holeStep M P Hs b then guardS M (gHl M S T s Inv) spH P Hs σ
      else guardS M (gSz M S T s Inv) spS P Hs σ) = some (l, r, π)) :
    PcOK M S T P Hs ∧ Inv P Hs σ ∧ s < P.card ∧
      (if holeStep M P Hs b then spH P Hs σ else spS P Hs σ) = some (l, r, π) ∧
      SplitOK M S T κ 6 P Hs l r π ∧ Inv l (childHoles Hs π.path.mverts) (chS P Hs σ π l) ∧
      Inv r (childHoles Hs π.path.mverts) (chS P Hs σ π r) ∧
      (holeStep M P Hs b = true → nTouch M P Hs = 6) ∧
      (holeStep M P Hs b = false → nTouch M P Hs ≤ 5) := by
  cases hst : holeStep M P Hs b
  · rw [hst] at he
    simp only [Bool.false_eq_true, ↓reduceIte] at he ⊢
    obtain ⟨⟨hP, hI, hs, ht⟩, h⟩ := guardS_some he
    obtain ⟨l', r', π', he', hok, il, ir, -, -⟩ := hF.size P Hs σ hP hI hs ht
    rw [h] at he'
    cases he'
    exact ⟨hP, hI, hs, h, hok, il, ir, fun h => absurd h (by simp), fun _ => ht⟩
  · rw [hst] at he
    simp only [↓reduceIte] at he ⊢
    obtain ⟨⟨hP, hI, hs, ht⟩, h⟩ := guardS_some he
    obtain ⟨l', r', π', he', hok, il, ir, -, -⟩ := hF.hole P Hs σ hP hI hs ht
    rw [h] at he'
    cases he'
    exact ⟨hP, hI, hs, h, hok, il, ir, fun _ => ht, fun h => absurd h (by simp)⟩

/-- **The piece of the guarded decomposition** of a reversal-closed set is the set itself, for
every state. -/
theorem decS_piece_guard {S T : Finset V} {κ s : ℕ}
    {Inv : Finset D → List (Finset V) → St → Prop}
    {spS spH : Finset D → List (Finset V) → St → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M}
    {chS : Finset D → List (Finset V) → St → HSep M → Finset D → St}
    (hF : SplitFnsS M S T κ s Inv spS spH sm chS)
    (hsm : ∀ P Hs, RevClosed M P → (sm P Hs).piece = P) :
    ∀ (n : ℕ) (P : Finset D) (Hs : List (Finset V)) (σ : St) (b : Bool), P.card = n →
      RevClosed M P →
      (decS M (guardS M (gSz M S T s Inv) spS) (guardS M (gHl M S T s Inv) spH) sm chS s P Hs σ
        b).piece = P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Hs σ b hn hP
  rcases decS_cases (guardS M (gSz M S T s Inv) spS) (guardS M (gHl M S T s Inv) spH) sm chS s P
    Hs σ b with ⟨-, h⟩ | ⟨-, h⟩ | ⟨l, r, π, hs, he, hl, hr, h⟩
  · rw [h]; exact hsm P Hs hP
  · rw [h]; rfl
  · rw [h]
    obtain ⟨hPc, -, -, -, hok, -, -, -, -⟩ := guard_answer hF he
    have pl := ih _ (hn ▸ hl) l (childHoles Hs π.path.mverts) (chS P Hs σ π l)
      (!holeStep M P Hs b) rfl (hok.pcOK_l hPc).rev
    have pr := ih _ (hn ▸ hr) r (childHoles Hs π.path.mverts) (chS P Hs σ π r)
      (!holeStep M P Hs b) rfl (hok.pcOK_r hPc).rev
    simp only [ADec.piece, pl, pr, hok.union]

/-- **A node of the guarded decomposition of a large piece**, for any state producing it: the
guard holds, the plain split answers `(l, r, π)` with `SplitOK`, the children are the guarded
decompositions of `l` and `r` (pieces `l`, `r`) with the states `chS P Hs σ π ·` and the flag
`!holeStep`. -/
theorem decS_node_guard {S T : Finset V} {κ s : ℕ}
    {Inv : Finset D → List (Finset V) → St → Prop}
    {spS spH : Finset D → List (Finset V) → St → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M}
    {chS : Finset D → List (Finset V) → St → HSep M → Finset D → St}
    (hF : SplitFnsS M S T κ s Inv spS spH sm chS)
    (hsm : ∀ P Hs, RevClosed M P → (sm P Hs).piece = P) {P : Finset D} {Hs : List (Finset V)}
    {σ : St} {b : Bool} (hs : s < P.card) {lt rt : ADec M} {π : HSep M}
    (h : decS M (guardS M (gSz M S T s Inv) spS) (guardS M (gHl M S T s Inv) spH) sm chS s P Hs
      σ b = .node lt rt π) :
    PcOK M S T P Hs ∧ Inv P Hs σ ∧
      (holeStep M P Hs b = true → nTouch M P Hs = 6) ∧
      (holeStep M P Hs b = false → nTouch M P Hs ≤ 5) ∧
      (if holeStep M P Hs b then spH P Hs σ else spS P Hs σ) = some (lt.piece, rt.piece, π) ∧
      SplitOK M S T κ 6 P Hs lt.piece rt.piece π ∧
      lt = decS M (guardS M (gSz M S T s Inv) spS) (guardS M (gHl M S T s Inv) spH) sm chS s
        lt.piece (childHoles Hs π.path.mverts) (chS P Hs σ π lt.piece) (!holeStep M P Hs b) ∧
      rt = decS M (guardS M (gSz M S T s Inv) spS) (guardS M (gHl M S T s Inv) spH) sm chS s
        rt.piece (childHoles Hs π.path.mverts) (chS P Hs σ π rt.piece) (!holeStep M P Hs b) ∧
      Inv lt.piece (childHoles Hs π.path.mverts) (chS P Hs σ π lt.piece) ∧
      Inv rt.piece (childHoles Hs π.path.mverts) (chS P Hs σ π rt.piece) := by
  rcases decS_cases (guardS M (gSz M S T s Inv) spS) (guardS M (gHl M S T s Inv) spH) sm chS s P
    Hs σ b with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨l, r, π', -, he, hl, hr, h3⟩
  · omega
  · rw [h2] at h; cases h
  · rw [h3] at h
    injection h with el er eπ
    subst eπ
    obtain ⟨hPc, hI, -, hsp, hok, il, ir, t1, t2⟩ := guard_answer hF he
    have pl := decS_piece_guard hF hsm _ l (childHoles Hs π'.path.mverts) (chS P Hs σ π' l)
      (!holeStep M P Hs b) rfl (hok.pcOK_l hPc).rev
    have pr := decS_piece_guard hF hsm _ r (childHoles Hs π'.path.mverts) (chS P Hs σ π' r)
      (!holeStep M P Hs b) rfl (hok.pcOK_r hPc).rev
    subst el er
    rw [pl, pr]
    exact ⟨hPc, hI, t1, t2, hsp, hok, rfl, rfl, il, ir⟩


/-- **A large piece meeting the invariant is a node** of the guarded decomposition. -/
theorem decS_guard_isNode {S T : Finset V} {κ s : ℕ}
    {Inv : Finset D → List (Finset V) → St → Prop}
    {spS spH : Finset D → List (Finset V) → St → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M}
    {chS : Finset D → List (Finset V) → St → HSep M → Finset D → St}
    (hF : SplitFnsS M S T κ s Inv spS spH sm chS) {P : Finset D} {Hs : List (Finset V)}
    {σ : St} {b : Bool} (hP : PcOK M S T P Hs) (hI : Inv P Hs σ) (hs : s < P.card)
    (ht : nTouch M P Hs ≤ (if b then 6 else 5)) :
    ∃ lt rt π, decS M (guardS M (gSz M S T s Inv) spS) (guardS M (gHl M S T s Inv) spH) sm chS s
      P Hs σ b = .node lt rt π := by
  by_cases hh : b = true ∧ nTouch M P Hs = 6
  · obtain ⟨hb, h6⟩ := hh
    have hst : holeStep M P Hs b = true := by simp [holeStep, hb, h6]
    obtain ⟨l, r, π, he, h, -, -, -, -⟩ := hF.hole P Hs σ hP hI hs h6
    have he' : (if holeStep M P Hs b then guardS M (gHl M S T s Inv) spH P Hs σ
        else guardS M (gSz M S T s Inv) spS P Hs σ) = some (l, r, π) := by
      rw [hst]; simp only [↓reduceIte]; rw [guardS_pos ⟨hP, hI, hs, h6⟩]; exact he
    exact ⟨_, _, _, decS_split hs he' h.card_l_lt h.card_r_lt⟩
  · have h5 : nTouch M P Hs ≤ 5 := by
      cases b
      · simpa using ht
      · simp only [ite_true] at ht; simp only [true_and] at hh; omega
    have hst : holeStep M P Hs b = false := by
      simp only [holeStep, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      cases b
      · exact Or.inl rfl
      · exact Or.inr (by omega)
    obtain ⟨l, r, π, he, h, -, -, -, -⟩ := hF.size P Hs σ hP hI hs h5
    have he' : (if holeStep M P Hs b then guardS M (gHl M S T s Inv) spH P Hs σ
        else guardS M (gSz M S T s Inv) spS P Hs σ) = some (l, r, π) := by
      rw [hst]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [guardS_pos ⟨hP, hI, hs, h5⟩]
      exact he
    exact ⟨_, _, _, decS_split hs he' h.card_l_lt h.card_r_lt⟩

/-- **The children of a node of the guarded decomposition meet the invariant of the recursion**
(`PcOK`, `Inv`, the `nTouch` bound of their flag); in particular a large child is a node
(`decS_guard_isNode`). -/
theorem decS_node_guard_kids {S T : Finset V} {κ s : ℕ}
    {Inv : Finset D → List (Finset V) → St → Prop}
    {spS spH : Finset D → List (Finset V) → St → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M}
    {chS : Finset D → List (Finset V) → St → HSep M → Finset D → St}
    (hF : SplitFnsS M S T κ s Inv spS spH sm chS)
    (hsm : ∀ P Hs, RevClosed M P → (sm P Hs).piece = P) {P : Finset D} {Hs : List (Finset V)}
    {σ : St} {b : Bool} (hs : s < P.card) {lt rt : ADec M} {π : HSep M}
    (h : decS M (guardS M (gSz M S T s Inv) spS) (guardS M (gHl M S T s Inv) spH) sm chS s P Hs
      σ b = .node lt rt π) :
    ∀ X ∈ [lt.piece, rt.piece], PcOK M S T X (childHoles Hs π.path.mverts) ∧
      Inv X (childHoles Hs π.path.mverts) (chS P Hs σ π X) ∧
      nTouch M X (childHoles Hs π.path.mverts) ≤ (if !holeStep M P Hs b then 6 else 5) := by
  obtain ⟨hP, hI, t1, t2, hsp, hok, el, er, il, ir⟩ := decS_node_guard hF hsm hs h
  have key : ∀ X, X ⊆ P → (X = lt.piece ∨ X = rt.piece) →
      nTouch M X (childHoles Hs π.path.mverts) ≤ (if !holeStep M P Hs b then 6 else 5) := by
    intro X hX hXe
    cases hst : holeStep M P Hs b
    · have := nTouch_childHoles_le (M := M) hX Hs π.path.mverts
      have := t2 hst
      simp only [Bool.not_false, ↓reduceIte]; omega
    · have h6 := t1 hst
      rw [hst] at hsp
      simp only [↓reduceIte] at hsp
      obtain ⟨l', r', π', he', -, -, -, tl, tr⟩ := hF.hole P Hs σ hP hI hs h6
      rw [hsp] at he'
      injection he' with he''
      injection he'' with e1 e2
      injection e2 with e2 e3
      subst e3
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rcases hXe with rfl | rfl
      · rw [e1]; exact tl
      · rw [e2]; exact tr
  intro X hX
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl
  · exact ⟨hok.pcOK_l hP, il, key _ (hok.union ▸ subset_union_left) (Or.inl rfl)⟩
  · exact ⟨hok.pcOK_r hP, ir, key _ (hok.union ▸ subset_union_right) (Or.inr rfl)⟩

end BKMNW

end PlanarFlow
