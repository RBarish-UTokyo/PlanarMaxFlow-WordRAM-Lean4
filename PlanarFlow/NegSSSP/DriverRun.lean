module

public import PlanarFlow.NegSSSP.Driver
public import PlanarFlow.NegSSSP.DecM
public import PlanarFlow.BKMNW.MachCost

/-!
# The driver on the decomposition of the machine

The driver of `PlanarFlow/NegSSSP/Driver.lean` instantiated with the recursion for negative
lengths on a decomposition `decM split n P` of a split function (`PlanarFlow.NegSSSP.decM`): the
frames of the subprograms are given by two predicates, `InP n P d e c` (the frame `[d, e)` holds
the piece `P` with `n` rounds left) and `Res P o d e c` (the frame holds the outcome
`o : Option (V → ℤ)` of the piece `P`), and the specifications of the subprograms
(`NSpec`) are stated with the rounds and the split: the test decides `Cnd split n P` (the
condition of a node of `decM`), the leaf solver and the combination give outcomes that are
`PotOut` (a feasible potential of the piece, or `none` and none exists), the split writes the
pieces `(split P).1`, `(split P).2` with one round less.

* `nspec_dspec`: the specifications `NSpec` give those of the driver, `DSpec`, for the inputs
  `NIn` (a decomposition `decM split n P` with `InP n P`) and the outputs `NOut` (a `PotOut`
  outcome of the piece with `Res`).
* `drive_dec`: **the driver computes a `PotOut` outcome of the piece of the root**, within
  `dcost … (decM split n P) + 2` steps.
* `dcost_le_negCost`: on a decomposition by simple cycles (`NTree.FDec`), with the costs of the
  subprograms bounded by `A · c.leaf m + B` at a leaf of `m ≤ 10⁶` darts and by
  `A · c.node … + B` at a node (test, split and combination), and `c.leaf m ≥ 1`,
  `c.lin m ≥ 1` for `m ≥ 1`, the cost of the driver is at most
  `(A + B + 80) · negCost N c τ + B + 20`.
* `drive_negDecM`: **the whole recursion for negative lengths as one run of the driver**, on the
  decomposition of the machine `negDecM N ord cut` with the least lengths `minLen N ℓ` (and no
  loop of negative length): the outcome in the root frame is a `PotOut` outcome of the graph
  `N.graph ℓ` (what `negSSSPDecM_potOut` asserts of `negSSSPDecM`), within
  `(A + B + 80) · negDecMCost N ord cut c + B + 22` steps.
* `drive_negDecM_mach`: the same on the dual map with the machine costs `cNegMach C`, within
  `(A + B + 80) · (cMach C C₀).negsssp n + B + 22` steps (`negDecMCost_mach`).

The subprograms themselves (`testS`, `leafS`, `splitS`, `nodeS` meeting `NSpec`) are inputs: on
the machine they are the split program (`splitProg_splitM`), the leaf solver
(`BFList.prog_exec`) and the node program (`node_exec_valBy`), each with its glue to the frames
(copy of the frame data to the work area below `Hb`, the run lifted by `Exec.lift_trunc`, the
copy of the results back).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Driver

open Finset WordRAM WordRAM.Machine BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {N : CombMap D V F}

/-- **The condition of a node of `decM split n P`**: a round left, more than `10⁶` darts, the
split covering the piece. -/
def Cnd (split : Finset D → Finset D × Finset D) (n : ℕ) (P : Finset D) : Prop :=
  0 < n ∧ 1000000 < P.card ∧ (split P).1 ∪ (split P).2 = P

lemma decM_leaf {split : Finset D → Finset D × Finset D} {n : ℕ} {P : Finset D}
    (h : ¬ Cnd split n P) : decM split n P = .leaf P := by
  rcases n with _ | n
  · rfl
  · simp only [decM]
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun hc => h ⟨Nat.succ_pos n, hc⟩)]

lemma decM_node' {split : Finset D → Finset D × Finset D} {n : ℕ} {P : Finset D}
    (h : Cnd split (n + 1) P) :
    decM split (n + 1) P = .node (decM split n (split P).1) (decM split n (split P).2) := by
  simp only [decM]
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h.2.1, h.2.2⟩)]

lemma decM_isLeaf_iff {split : Finset D → Finset D × Finset D} {n : ℕ} {P : Finset D} :
    (∃ Q, decM split n P = .leaf Q) ↔ ¬ Cnd split n P := by
  refine ⟨fun ⟨Q, hQ⟩ hc => ?_, fun h => ⟨P, decM_leaf h⟩⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := hc.1; omega⟩
  rw [decM_node' hc] at hQ
  cases hQ

/-- The inputs of the driver: a decomposition `decM split n P` with the piece `P` and the rounds
`n` in the frame. -/
def NIn (split : Finset D → Finset D × Finset D) (InP : ℕ → Finset D → ℕ → ℕ → Config → Prop)
    (τ : NTree D) (d e : ℕ) (c : Config) : Prop :=
  ∃ n P, τ = decM split n P ∧ InP n P d e c

variable (N) in
/-- The outputs of the driver: an outcome of the piece in the frame, `PotOut`. -/
def NOut (ℓ : D → ℤ) (Res : Finset D → Option (V → ℤ) → ℕ → ℕ → Config → Prop)
    (τ : NTree D) (d e : ℕ) (c : Config) : Prop :=
  ∃ o, PotOut (pg N τ.piece ℓ) o ∧ Res τ.piece o d e c

/-- The cost of the combination at a node. -/
def ncT (ncP : Finset D → Finset D → ℕ) : NTree D → ℕ
  | .leaf _ => 0
  | .node l r => ncP l.piece r.piece

variable (N) in
/-- **The specifications of the subprograms on the decomposition `decM split`** (see the module
docstring). -/
structure NSpec (ℓ : D → ℤ) (split : Finset D → Finset D × Finset D) (I : Input) (W Hb : ℕ)
    (testS leafS splitS nodeS : Stmt) (G : Config → Prop)
    (InP : ℕ → Finset D → ℕ → ℕ → Config → Prop)
    (Res : Finset D → Option (V → ℤ) → ℕ → ℕ → Config → Prop)
    (tcP lcP scP : Finset D → ℕ) (ncP : Finset D → Finset D → ℕ) : Prop where
  g_stab : ∀ c c', G c → (∀ r < 3000, c'.nreg r = c.nreg r) → c'.rreg = c.rreg →
    MemEq c c' 0 Hb → G c'
  in_stab : ∀ n P d e c c', InP n P d e c → MemEq c c' d e → InP n P d e c'
  res_stab : ∀ P o d e c c', Res P o d e c → MemEq c c' d e → Res P o d e c'
  test : ∀ n P d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → InP n P d e c →
    ∃ c' t, Exec I W testS c c' t ∧ t ≤ tcP P ∧ G c' ∧ RegKeep c c' ∧ HeapKeep Hb h h h c c' ∧
      c'.output = c.output ∧ (c'.nreg 2997 < 1 ↔ ¬ Cnd split n P)
  leaf : ∀ n P d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → InP n P d e c → ¬ Cnd split n P →
    ∃ c' t o, Exec I W leafS c c' t ∧ t ≤ lcP P ∧ G c' ∧ RegKeep c c' ∧
      HeapKeep Hb h d e c c' ∧ c'.output = c.output ∧ PotOut (pg N P ℓ) o ∧ Res P o d e c'
  spl : ∀ n P d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → InP (n + 1) P d e c →
    Cnd split (n + 1) P →
    ∃ c' t el er, Exec I W splitS c c' t ∧ t ≤ scP P ∧ G c' ∧ RegKeep c c' ∧
      HeapKeep Hb h h h c c' ∧ c'.output = c.output ∧ c'.nreg 2998 = el ∧ c'.nreg 2999 = er ∧
      h + 5 ≤ el ∧ el + 5 ≤ er ∧ InP n (split P).1 (h + 5) el c' ∧
      InP n (split P).2 (el + 5) er c'
  node : ∀ n P d e bl el er c o₀ o₁, G c → WordsBounded W c → c.nreg 3004 = d →
    c.nreg 3005 = e → c.nreg 3006 = bl + 5 → c.nreg 3007 = el → c.nreg 3008 = el + 5 →
    c.nreg 3009 = er → c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e → e ≤ bl → bl + 5 ≤ el →
    el + 5 ≤ er → InP (n + 1) P d e c → Cnd split (n + 1) P →
    PotOut (pg N (split P).1 ℓ) o₀ → PotOut (pg N (split P).2 ℓ) o₁ →
    Res (split P).1 o₀ (bl + 5) el c → Res (split P).2 o₁ (el + 5) er c →
    ∃ c' t o, Exec I W nodeS c c' t ∧ t ≤ ncP (split P).1 (split P).2 ∧ G c' ∧
      RegKeep c c' ∧ HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧ PotOut (pg N P ℓ) o ∧
      Res P o d e c'

variable {ℓ : D → ℤ} {split : Finset D → Finset D × Finset D} {I : Input} {W Hb : ℕ}
  {testS leafS splitS nodeS : Stmt} {G : Config → Prop}
  {InP : ℕ → Finset D → ℕ → ℕ → Config → Prop}
  {Res : Finset D → Option (V → ℤ) → ℕ → ℕ → Config → Prop}
  {tcP lcP scP : Finset D → ℕ} {ncP : Finset D → Finset D → ℕ}

/-- **The specifications on the decomposition give those of the driver.** -/
theorem nspec_dspec
    (hS : NSpec N ℓ split I W Hb testS leafS splitS nodeS G InP Res tcP lcP scP ncP) :
    DSpec I W Hb testS leafS splitS nodeS G (NIn split InP) (NOut N ℓ Res)
      (fun τ => tcP τ.piece) (fun τ => lcP τ.piece) (fun τ => scP τ.piece) (ncT ncP) where
  g_stab := hS.g_stab
  in_stab τ d e c c' := fun ⟨n, P, hτ, hi⟩ hm => ⟨n, P, hτ, hS.in_stab n P d e c c' hi hm⟩
  out_stab τ d e c c' := fun ⟨o, hp, hr⟩ hm => ⟨o, hp, hS.res_stab _ o d e c c' hr hm⟩
  test τ d e h c hg hw h4 h5 h3 b1 b2 b3 := fun ⟨n, P, hτ, hi⟩ => by
    obtain ⟨c', t, ex, ht, g, rk, hk, ho, hf⟩ := hS.test n P d e h c hg hw h4 h5 h3 b1 b2 b3 hi
    refine ⟨c', t, ex, ?_, g, rk, hk, ho, ?_⟩
    · rw [hτ, piece_decM]; exact ht
    · rw [hf, hτ, decM_isLeaf_iff]
  leaf Q d e h c hg hw h4 h5 h3 b1 b2 b3 := fun ⟨n, P, hτ, hi⟩ => by
    have hc : ¬ Cnd split n P := decM_isLeaf_iff.1 ⟨Q, hτ.symm⟩
    have hQ : Q = P := by rw [decM_leaf hc] at hτ; cases hτ; rfl
    subst hQ
    obtain ⟨c', t, o, ex, ht, g, rk, hk, ho, hp, hr⟩ :=
      hS.leaf n Q d e h c hg hw h4 h5 h3 b1 b2 b3 hi hc
    exact ⟨c', t, ex, ht, g, rk, hk, ho, o, hp, hr⟩
  split l r d e h c hg hw h4 h5 h3 b1 b2 b3 := fun ⟨n, P, hτ, hi⟩ => by
    obtain ⟨hl, hr, hcard, hu⟩ := decM_node hτ.symm
    have hn : n = (n - 1) + 1 := by
      rcases n with _ | n
      · simp [decM] at hτ
      · rfl
    rw [hn] at hi
    have hc : Cnd split (n - 1 + 1) P := ⟨Nat.succ_pos _, hcard, hu⟩
    obtain ⟨c', t, el, er, ex, ht, g, rk, hk, ho, s1, s2, b4, b5, il, ir⟩ :=
      hS.spl (n - 1) P d e h c hg hw h4 h5 h3 b1 b2 b3 hi hc
    refine ⟨c', t, el, er, ex, ?_, g, rk, hk, ho, s1, s2, b4, b5, ⟨n - 1, _, hl, il⟩,
      ⟨n - 1, _, hr, ir⟩⟩
    rw [hτ, piece_decM]; exact ht
  node l r d e bl el er c hg hw h4 h5 h6 h7 h8 h9 h3 b1 b2 b3 b4 b5 :=
    fun ⟨n, P, hτ, hi⟩ ⟨o₀, p₀, r₀⟩ ⟨o₁, p₁, r₁⟩ => by
    obtain ⟨hl, hr, hcard, hu⟩ := decM_node hτ.symm
    have hn : n = (n - 1) + 1 := by
      rcases n with _ | n
      · simp [decM] at hτ
      · rfl
    rw [hn] at hi
    have hc : Cnd split (n - 1 + 1) P := ⟨Nat.succ_pos _, hcard, hu⟩
    have el' : l.piece = (split P).1 := by rw [hl, piece_decM]
    have er' : r.piece = (split P).2 := by rw [hr, piece_decM]
    rw [el'] at p₀ r₀
    rw [er'] at p₁ r₁
    obtain ⟨c', t, o, ex, ht, g, rk, hk, ho, hp, hres⟩ := hS.node (n - 1) P d e bl el er c o₀ o₁
      hg hw h4 h5 h6 h7 h8 h9 h3 b1 b2 b3 b4 b5 hi hc p₀ p₁ r₀ r₁
    have ep : (NTree.node l r).piece = P := by rw [hτ, piece_decM]
    refine ⟨c', t, ex, ?_, g, rk, hk, ho, o, ?_, ?_⟩
    · show t ≤ ncP l.piece r.piece
      rw [el', er']; exact ht
    · rw [ep]; exact hp
    · rw [ep]; exact hres

/-- **The driver on a decomposition `decM split n P`**: from the root frame holding the piece
`P` with `n` rounds, a `PotOut` outcome of `P` in the root frame. -/
theorem drive_dec
    (hS : NSpec N ℓ split I W Hb testS leafS splitS nodeS G InP Res tcP lcP scP ncP)
    (hHb : 0 < Hb) (n : ℕ) (P : Finset D) {e h : ℕ} (c : Config) (hc : WordsBounded W c)
    (hg : G c) (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1) (r2 : c.nreg 3002 = Hb)
    (r3 : c.nreg 3003 = h) (m0 : c.nmem Hb = 0) (m1 : c.nmem (Hb + 1) = 0)
    (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h) (hin : InP n P (Hb + 5) e c) :
    ∃ c' t o, Exec I W (driver testS leafS splitS nodeS) c c' t ∧
      t ≤ dcost (fun τ => tcP τ.piece) (fun τ => lcP τ.piece) (fun τ => scP τ.piece) (ncT ncP)
        (decM split n P) + 2 ∧
      PotOut (pg N P ℓ) o ∧ Res P o (Hb + 5) e c' ∧ G c' ∧ c'.nreg 3003 = h ∧
      HeapKeep Hb h Hb e c c' ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, g, ⟨o, hp, hr⟩, -, h3, hk, ho⟩ :=
    drive (nspec_dspec hS) hHb (decM split n P) c hc hg r0 r1 r2 r3 m0 m1 m2 he hh
      ⟨n, P, rfl, hin⟩
  rw [piece_decM] at hp hr
  exact ⟨c', t, o, ex, ht, hp, hr, g, h3, hk, ho⟩

/-! ### The cost -/

/-- **The cost of the driver on a decomposition by simple cycles with nonempty pieces**. -/
theorem dcost_le_negCost {c : NegCosts} {A B : ℕ}
    (hl : ∀ P : Finset D, P.card ≤ 1000000 → tcP P + lcP P ≤ A * c.leaf P.card + B)
    (hn : ∀ P₀ P₁ : Finset D, SplitF N (P₀ ∪ P₁) P₀ P₁ →
      tcP (P₀ ∪ P₁) + scP (P₀ ∪ P₁) + ncP P₀ P₁ ≤ A * c.node (P₀ ∪ P₁).card
        (bdry N P₀ P₁).card P₀.card (verts N P₀).card P₁.card (verts N P₁).card + B)
    (h1l : ∀ m, 1 ≤ m → 1 ≤ c.leaf m) (h1n : ∀ m, 1 ≤ m → 1 ≤ c.lin m) :
    ∀ τ : NTree D, τ.FDec N → 0 < τ.piece.card →
      dcost (fun τ => tcP τ.piece) (fun τ => lcP τ.piece) (fun τ => scP τ.piece) (ncT ncP) τ ≤
        (A + B + 80) * negCost N c τ
  | .leaf P, hf, hp => by
    simp only [dcost, negCost, NTree.piece, NTree.FDec] at *
    have h1 := hl P hf
    have h2 := h1l _ hp
    have h3 : (B + 80) * 1 ≤ (B + 80) * c.leaf P.card := Nat.mul_le_mul_left _ h2
    nlinarith
  | .node l r, hf, hp => by
    obtain ⟨fl, fr, hs⟩ := hf
    have il := dcost_le_negCost hl hn h1l h1n l fl hs.2.2.1
    have ir := dcost_le_negCost hl hn h1l h1n r fr hs.2.2.2.1
    have hnode := hn l.piece r.piece hs
    have hlp : 1 ≤ (l.piece ∪ r.piece).card :=
      le_trans hs.2.2.1 (card_le_card subset_union_left)
    set X := c.node (l.piece ∪ r.piece).card (bdry N l.piece r.piece).card l.piece.card
      (verts N l.piece).card r.piece.card (verts N r.piece).card with hX
    have h1 : 1 ≤ X := le_trans (h1n _ hlp) (by rw [hX]; unfold NegCosts.node; omega)
    have h3 : (B + 80) * 1 ≤ (B + 80) * X := Nat.mul_le_mul_left _ h1
    simp only [dcost, negCost, ncT, NTree.piece]
    rw [← hX]
    nlinarith

/-- **The cost of the driver on a decomposition by simple cycles.** -/
theorem dcost_le_negCost' {c : NegCosts} {A B : ℕ}
    (hl : ∀ P : Finset D, P.card ≤ 1000000 → tcP P + lcP P ≤ A * c.leaf P.card + B)
    (hn : ∀ P₀ P₁ : Finset D, SplitF N (P₀ ∪ P₁) P₀ P₁ →
      tcP (P₀ ∪ P₁) + scP (P₀ ∪ P₁) + ncP P₀ P₁ ≤ A * c.node (P₀ ∪ P₁).card
        (bdry N P₀ P₁).card P₀.card (verts N P₀).card P₁.card (verts N P₁).card + B)
    (h1l : ∀ m, 1 ≤ m → 1 ≤ c.leaf m) (h1n : ∀ m, 1 ≤ m → 1 ≤ c.lin m) (τ : NTree D)
    (hf : τ.FDec N) :
    dcost (fun τ => tcP τ.piece) (fun τ => lcP τ.piece) (fun τ => scP τ.piece) (ncT ncP) τ ≤
      (A + B + 80) * negCost N c τ + B + 20 := by
  rcases Nat.eq_zero_or_pos τ.piece.card with h0 | hp
  · cases τ with
    | leaf P =>
      simp only [dcost, negCost, NTree.piece, NTree.FDec] at *
      have := hl P hf
      nlinarith
    | node l r =>
      obtain ⟨-, -, hs⟩ := hf
      have := card_le_card (subset_union_left (s₁ := l.piece) (s₂ := r.piece))
      simp only [NTree.piece] at h0
      have := hs.2.2.1
      omega
  · have := dcost_le_negCost hl hn h1l h1n τ hf hp
    omega

/-! ### The whole recursion -/

/-- **The outcome on the kept darts with the least lengths is an outcome of the graph**, when
no loop has a negative length (as in `negSSSPS_potOut`). -/
theorem potOut_graph_of_reps {ℓ : D → ℤ} (hneg : ∀ d, N.tail d = N.head d → 0 ≤ ℓ d)
    {o : Option (V → ℤ)} (h : PotOut (pg N (reps N) (minLen N ℓ)) o) :
    PotOut (N.graph ℓ) o := by
  rcases o with _ | p
  · rintro ⟨p, hp⟩
    refine h ⟨p, fun a => ?_⟩
    obtain ⟨x, h1, h2, e⟩ := exists_minLen (N := N) ℓ a.1
    have := hp x
    simp only [CombMap.graph] at this
    show p (N.head a.1) ≤ p (N.tail a.1) + minLen N ℓ a.1
    rw [e, ← h1, ← h2]; exact this
  · intro d
    show p (N.head d) ≤ p (N.tail d) + ℓ d
    by_cases hl : N.tail d = N.head d
    · rw [hl]; have := hneg d hl; omega
    · obtain ⟨d', hd', h1, h2⟩ := exists_reps hl
      have := h ⟨d', hd'⟩
      have hm := minLen_le (N := N) ℓ h1.symm h2.symm
      simp only [MSSP.pieceGraph] at this
      rw [h1, h2] at this
      omega

/-- **The whole recursion for negative lengths as one run of the driver** (see the module
docstring): on the decomposition of the machine `negDecM N ord cut`, from the root frame holding
the kept darts with `Fintype.card D` rounds, with the least lengths `minLen N ℓ` and no loop of
negative length. -/
theorem drive_negDecM {ord : Finset D → List D} (hL : OrdOK ord) {cut : Finset D → Finset D}
    (hcut : CutsOK N cut) {ℓ₀ : D → ℤ} (hneg : ∀ d, N.tail d = N.head d → 0 ≤ ℓ₀ d)
    (hS : NSpec N (minLen N ℓ₀) (splitM N ord cut) I W Hb testS leafS splitS nodeS G InP Res
      tcP lcP scP ncP) (hHb : 0 < Hb) {c₀ : NegCosts} {A B : ℕ}
    (hl : ∀ P : Finset D, P.card ≤ 1000000 → tcP P + lcP P ≤ A * c₀.leaf P.card + B)
    (hn : ∀ P₀ P₁ : Finset D, SplitF N (P₀ ∪ P₁) P₀ P₁ →
      tcP (P₀ ∪ P₁) + scP (P₀ ∪ P₁) + ncP P₀ P₁ ≤ A * c₀.node (P₀ ∪ P₁).card
        (bdry N P₀ P₁).card P₀.card (verts N P₀).card P₁.card (verts N P₁).card + B)
    (h1l : ∀ m, 1 ≤ m → 1 ≤ c₀.leaf m) (h1n : ∀ m, 1 ≤ m → 1 ≤ c₀.lin m)
    {e h : ℕ} (c : Config) (hc : WordsBounded W c) (hg : G c) (r0 : c.nreg 3000 = 0)
    (r1 : c.nreg 3001 = 1) (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h)
    (m0 : c.nmem Hb = 0) (m1 : c.nmem (Hb + 1) = 0) (m2 : c.nmem (Hb + 2) = e)
    (he : Hb + 5 ≤ e) (hh : e ≤ h) (hin : InP (Fintype.card D) (reps N) (Hb + 5) e c) :
    ∃ c' t o, Exec I W (driver testS leafS splitS nodeS) c c' t ∧
      t ≤ (A + B + 80) * negDecMCost N ord cut c₀ + B + 22 ∧ PotOut (N.graph ℓ₀) o ∧
      Res (reps N) o (Hb + 5) e c' ∧ G c' ∧ c'.output = c.output := by
  obtain ⟨c', t, o, ex, ht, hp, hr, g, -, -, ho⟩ :=
    drive_dec hS hHb (Fintype.card D) (reps N) c hc hg r0 r1 r2 r3 m0 m1 m2 he hh hin
  have hcost := dcost_le_negCost' (N := N) (tcP := tcP) (lcP := lcP) (scP := scP) (ncP := ncP)
    hl hn h1l h1n _ (negDecM_fDec hL hcut)
  have hk : (A + B + 80) * negCost N c₀ (negDecM N ord cut) ≤
      (A + B + 80) * negDecMCost N ord cut c₀ :=
    Nat.mul_le_mul_left _ (by unfold negDecMCost; omega)
  refine ⟨c', t, o, ex, ?_, potOut_graph_of_reps hneg hp, hr, g, ho⟩
  unfold negDecM at hcost hk
  omega

universe w

/-- **The whole recursion on the dual map with the machine costs**: within
`(A + B + 80) · (cMach C C₀).negsssp n + B + 22` steps, `n` the darts, when the subprograms cost
at most `A · (cNegMach C).leaf m + B` at a leaf and `A · (cNegMach C).node … + B` at a node. -/
theorem drive_negDecM_mach (C C₀ : ℕ) {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] {M : CombMap D V F} {ord : Finset D → List D}
    (hL : OrdOK ord) {cut : Finset D → Finset D} (hcut : CutsOK M.dual cut) {ℓ₀ : D → ℤ}
    (hneg : ∀ d, M.dual.tail d = M.dual.head d → 0 ≤ ℓ₀ d)
    {InP : ℕ → Finset D → ℕ → ℕ → Config → Prop}
    {Res : Finset D → Option (F → ℤ) → ℕ → ℕ → Config → Prop}
    {tcP lcP scP : Finset D → ℕ} {ncP : Finset D → Finset D → ℕ}
    (hS : NSpec M.dual (minLen M.dual ℓ₀) (splitM M.dual ord cut) I W Hb testS leafS splitS
      nodeS G InP Res tcP lcP scP ncP) (hHb : 0 < Hb) {A B : ℕ}
    (hl : ∀ P : Finset D, P.card ≤ 1000000 → tcP P + lcP P ≤ A * (cNegMach C).leaf P.card + B)
    (hn : ∀ P₀ P₁ : Finset D, SplitF M.dual (P₀ ∪ P₁) P₀ P₁ →
      tcP (P₀ ∪ P₁) + scP (P₀ ∪ P₁) + ncP P₀ P₁ ≤ A * (cNegMach C).node (P₀ ∪ P₁).card
        (bdry M.dual P₀ P₁).card P₀.card (verts M.dual P₀).card P₁.card
        (verts M.dual P₁).card + B)
    {e h : ℕ} (c : Config) (hc : WordsBounded W c) (hg : G c) (r0 : c.nreg 3000 = 0)
    (r1 : c.nreg 3001 = 1) (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h)
    (m0 : c.nmem Hb = 0) (m1 : c.nmem (Hb + 1) = 0) (m2 : c.nmem (Hb + 2) = e)
    (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hin : InP (Fintype.card D) (reps M.dual) (Hb + 5) e c) :
    ∃ c' t o, Exec I W (driver testS leafS splitS nodeS) c c' t ∧
      t ≤ (A + B + 80) * (cMach C C₀).negsssp (Fintype.card D) + B + 22 ∧
      PotOut (M.dual.graph ℓ₀) o ∧ Res (reps M.dual) o (Hb + 5) e c' ∧ G c' ∧
      c'.output = c.output := by
  obtain ⟨c', t, o, ex, ht, hp, hr, g, ho⟩ := drive_negDecM hL hcut hneg hS hHb hl hn
    (fun m hm => by show 1 ≤ 96 * m ^ 2; nlinarith) (fun m hm => by show 1 ≤ 1000 * m; omega)
    c hc hg r0 r1 r2 r3 m0 m1 m2 he hh hin
  have hk := Nat.mul_le_mul_left (A + B + 80) (negDecMCost_mach C C₀ (M := M) hL hcut)
  exact ⟨c', t, o, ex, by omega, hp, hr, g, ho⟩

end Driver

end NegSSSP

end PlanarFlow
