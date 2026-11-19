module

public import PlanarFlow.NegSSSP.DriverRoom
public import PlanarFlow.NegSSSP.SplitStage

/-!
# The driver on the decomposition of the machine, with room for the heap

`NSpec` (`DriverRun.lean`) with a room invariant (`DSpecR`, `DriverRoom.lean`): **`NSpecR`**
takes three room functions of the piece, `rL` (the leaf), `rS` (the split: the frames of the
children are written in `[h, h + rS P)`) and `rN` (the combination, above its heap top before the
split), and its fields assume `h + rL P ≤ W`, `h + rS P ≤ W`, `bl + rN P ≤ W` (and the split
gives `er ≤ h + rS P`). The room of a subtree is `roomT rL rS rN`: `rL P` at a leaf,
`rS P + rN P + max (room l) (room r)` at a node of piece `P`.

* `nspecR_dspecR`: `NSpecR` gives `DSpecR` with `room = roomT rL rS rN`.
* `roomT_decM_le`: `roomT (decM split n P) ≤ (n + 1) · R` when `rL ≤ R` and `rS + rN ≤ R`.
* `drive_decR`, `drive_split_machR`, **`drive_msplit_machR`**: `drive_dec`, `drive_split_mach`,
  `drive_msplit_mach` for `NSpecR`, with the extra hypothesis `h + (#D + 1) · R ≤ W` at the root
  (the bounds unchanged).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Driver

open Finset WordRAM WordRAM.Machine BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {N : CombMap D V F}

/-- **The room of a subtree**: `rL P` at a leaf, `rS P + rN P + max (room l) (room r)` at a node
of piece `P`. -/
def roomT (rL rS rN : Finset D → ℕ) : NTree D → ℕ
  | .leaf P => rL P
  | .node l r => rS (l.piece ∪ r.piece) + rN (l.piece ∪ r.piece) +
      max (roomT rL rS rN l) (roomT rL rS rN r)

/-- **The room of the decomposition of a split function** in `n` rounds. -/
theorem roomT_decM_le {rL rS rN : Finset D → ℕ} {R : ℕ} (hL : ∀ Q, rL Q ≤ R)
    (hSN : ∀ Q, rS Q + rN Q ≤ R) (split : Finset D → Finset D × Finset D) :
    ∀ (n : ℕ) (P : Finset D), roomT rL rS rN (decM split n P) ≤ (n + 1) * R
  | 0, P => by simp only [decM, roomT]; have := hL P; omega
  | n + 1, P => by
    simp only [decM]
    split_ifs with h
    · have i1 := roomT_decM_le hL hSN split n (split P).1
      have i2 := roomT_decM_le hL hSN split n (split P).2
      have := hSN ((decM split n (split P).1).piece ∪ (decM split n (split P).2).piece)
      simp only [roomT]
      rw [Nat.add_mul, Nat.one_mul]
      have : max (roomT rL rS rN (decM split n (split P).1))
        (roomT rL rS rN (decM split n (split P).2)) ≤ (n + 1) * R := max_le i1 i2
      have : (n + 1) * R ≤ (n + 1 + 1) * R := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul (n + 1) 1 R] at this
      omega
    · simp only [roomT]; have := hL P
      have : R ≤ (n + 1 + 1) * R := Nat.le_mul_of_pos_left _ (by omega)
      omega

variable (N) in
/-- **The specifications of the subprograms on the decomposition `decM split`, with room** (see
the module docstring). -/
structure NSpecR (ℓ : D → ℤ) (split : Finset D → Finset D × Finset D) (I : Input) (W Hb : ℕ)
    (testS leafS splitS nodeS : Stmt) (G : Config → Prop)
    (InP : ℕ → Finset D → ℕ → ℕ → Config → Prop)
    (Res : Finset D → Option (V → ℤ) → ℕ → ℕ → Config → Prop)
    (tcP lcP scP : Finset D → ℕ) (ncP : Finset D → Finset D → ℕ) (rL rS rN : Finset D → ℕ) :
    Prop where
  g_stab : ∀ c c', G c → (∀ r < 3000, c'.nreg r = c.nreg r) → c'.rreg = c.rreg →
    MemEq c c' 0 Hb → G c'
  in_stab : ∀ n P d e c c', InP n P d e c → MemEq c c' d e → InP n P d e c'
  res_stab : ∀ P o d e c c', Res P o d e c → MemEq c c' d e → Res P o d e c'
  test : ∀ n P d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → InP n P d e c →
    ∃ c' t, Exec I W testS c c' t ∧ t ≤ tcP P ∧ G c' ∧ RegKeep c c' ∧ HeapKeep Hb h h h c c' ∧
      c'.output = c.output ∧ (c'.nreg 2997 < 1 ↔ ¬ Cnd split n P)
  leaf : ∀ n P d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → h + rL P ≤ W → InP n P d e c →
    ¬ Cnd split n P →
    ∃ c' t o, Exec I W leafS c c' t ∧ t ≤ lcP P ∧ G c' ∧ RegKeep c c' ∧
      HeapKeep Hb h d e c c' ∧ c'.output = c.output ∧ PotOut (pg N P ℓ) o ∧ Res P o d e c'
  spl : ∀ n P d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → h + rS P ≤ W → InP (n + 1) P d e c →
    Cnd split (n + 1) P →
    ∃ c' t el er, Exec I W splitS c c' t ∧ t ≤ scP P ∧ G c' ∧ RegKeep c c' ∧
      HeapKeep Hb h h h c c' ∧ c'.output = c.output ∧ c'.nreg 2998 = el ∧ c'.nreg 2999 = er ∧
      h + 5 ≤ el ∧ el + 5 ≤ er ∧ er ≤ h + rS P ∧ InP n (split P).1 (h + 5) el c' ∧
      InP n (split P).2 (el + 5) er c'
  node : ∀ n P d e bl el er c o₀ o₁, G c → WordsBounded W c → c.nreg 3004 = d →
    c.nreg 3005 = e → c.nreg 3006 = bl + 5 → c.nreg 3007 = el → c.nreg 3008 = el + 5 →
    c.nreg 3009 = er → c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e → e ≤ bl → bl + 5 ≤ el →
    el + 5 ≤ er → bl + rN P ≤ W → InP (n + 1) P d e c → Cnd split (n + 1) P →
    PotOut (pg N (split P).1 ℓ) o₀ → PotOut (pg N (split P).2 ℓ) o₁ →
    Res (split P).1 o₀ (bl + 5) el c → Res (split P).2 o₁ (el + 5) er c →
    ∃ c' t o, Exec I W nodeS c c' t ∧ t ≤ ncP (split P).1 (split P).2 ∧ G c' ∧
      RegKeep c c' ∧ HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧ PotOut (pg N P ℓ) o ∧
      Res P o d e c'

variable {ℓ : D → ℤ} {split : Finset D → Finset D × Finset D} {I : Input} {W Hb : ℕ}
  {testS leafS splitS nodeS : Stmt} {G : Config → Prop}
  {InP : ℕ → Finset D → ℕ → ℕ → Config → Prop}
  {Res : Finset D → Option (V → ℤ) → ℕ → ℕ → Config → Prop}
  {tcP lcP scP : Finset D → ℕ} {ncP : Finset D → Finset D → ℕ} {rL rS rN : Finset D → ℕ}

/-- **The specifications with room on the decomposition give those of the driver with room.** -/
theorem nspecR_dspecR
    (hS : NSpecR N ℓ split I W Hb testS leafS splitS nodeS G InP Res tcP lcP scP ncP rL rS rN) :
    DSpecR I W Hb testS leafS splitS nodeS G (NIn split InP) (NOut N ℓ Res)
      (fun τ => tcP τ.piece) (fun τ => lcP τ.piece) (fun τ => scP τ.piece) (ncT ncP)
      (roomT rL rS rN) where
  g_stab := hS.g_stab
  in_stab τ d e c c' := fun ⟨n, P, hτ, hi⟩ hm => ⟨n, P, hτ, hS.in_stab n P d e c c' hi hm⟩
  out_stab τ d e c c' := fun ⟨o, hp, hr⟩ hm => ⟨o, hp, hS.res_stab _ o d e c c' hr hm⟩
  test τ d e h c hg hw h4 h5 h3 b1 b2 b3 _ := fun ⟨n, P, hτ, hi⟩ => by
    obtain ⟨c', t, ex, ht, g, rk, hk, ho, hf⟩ := hS.test n P d e h c hg hw h4 h5 h3 b1 b2 b3 hi
    refine ⟨c', t, ex, ?_, g, rk, hk, ho, ?_⟩
    · rw [hτ, piece_decM]; exact ht
    · rw [hf, hτ, decM_isLeaf_iff]
  leaf Q d e h c hg hw h4 h5 h3 b1 b2 b3 hroom := fun ⟨n, P, hτ, hi⟩ => by
    have hc : ¬ Cnd split n P := decM_isLeaf_iff.1 ⟨Q, hτ.symm⟩
    have hQ : Q = P := by rw [decM_leaf hc] at hτ; cases hτ; rfl
    subst hQ
    obtain ⟨c', t, o, ex, ht, g, rk, hk, ho, hp, hr⟩ :=
      hS.leaf n Q d e h c hg hw h4 h5 h3 b1 b2 b3 hroom hi hc
    exact ⟨c', t, ex, ht, g, rk, hk, ho, o, hp, hr⟩
  split l r d e h c hg hw h4 h5 h3 b1 b2 b3 hroom := fun ⟨n, P, hτ, hi⟩ => by
    obtain ⟨hl, hr, hcard, hu⟩ := decM_node hτ.symm
    have hn : n = (n - 1) + 1 := by
      rcases n with _ | n
      · simp [decM] at hτ
      · rfl
    rw [hn] at hi
    have hc : Cnd split (n - 1 + 1) P := ⟨Nat.succ_pos _, hcard, hu⟩
    have ep : l.piece ∪ r.piece = P := by
      have := congrArg NTree.piece hτ
      rw [piece_decM] at this; exact this
    have hR : roomT rL rS rN (.node l r) = rS P + rN P +
        max (roomT rL rS rN l) (roomT rL rS rN r) := by simp only [roomT, ep]
    have ml := le_max_left (roomT rL rS rN l) (roomT rL rS rN r)
    have mr := le_max_right (roomT rL rS rN l) (roomT rL rS rN r)
    obtain ⟨c', t, el, er, ex, ht, g, rk, hk, ho, s1, s2, b4, b5, b6, il, ir⟩ :=
      hS.spl (n - 1) P d e h c hg hw h4 h5 h3 b1 b2 b3 (by omega) hi hc
    refine ⟨c', t, el, er, ex, ?_, g, rk, hk, ho, s1, s2, b4, b5, by omega, by omega,
      ⟨n - 1, _, hl, il⟩, ⟨n - 1, _, hr, ir⟩⟩
    rw [hτ, piece_decM]; exact ht
  node l r d e bl el er c hg hw h4 h5 h6 h7 h8 h9 h3 b1 b2 b3 b4 b5 hroom :=
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
    have ep : (NTree.node l r).piece = P := by rw [hτ, piece_decM]
    have hR : roomT rL rS rN (.node l r) = rS P + rN P +
        max (roomT rL rS rN l) (roomT rL rS rN r) := by
      simp only [roomT]; simp only [NTree.piece] at ep; rw [ep]
    rw [el'] at p₀ r₀
    rw [er'] at p₁ r₁
    obtain ⟨c', t, o, ex, ht, g, rk, hk, ho, hp, hres⟩ := hS.node (n - 1) P d e bl el er c o₀ o₁
      hg hw h4 h5 h6 h7 h8 h9 h3 b1 b2 b3 b4 b5 (by omega) hi hc p₀ p₁ r₀ r₁
    refine ⟨c', t, ex, ?_, g, rk, hk, ho, o, ?_, ?_⟩
    · show t ≤ ncP l.piece r.piece
      rw [el', er']; exact ht
    · rw [ep]; exact hp
    · rw [ep]; exact hres

/-- **The driver on a decomposition `decM split n P`, with room.** -/
theorem drive_decR
    (hS : NSpecR N ℓ split I W Hb testS leafS splitS nodeS G InP Res tcP lcP scP ncP rL rS rN)
    (hHb : 0 < Hb) (n : ℕ) (P : Finset D) {e h : ℕ} (c : Config) (hc : WordsBounded W c)
    (hg : G c) (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1) (r2 : c.nreg 3002 = Hb)
    (r3 : c.nreg 3003 = h) (m0 : c.nmem Hb = 0) (m1 : c.nmem (Hb + 1) = 0)
    (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hroom : h + roomT rL rS rN (decM split n P) ≤ W) (hin : InP n P (Hb + 5) e c) :
    ∃ c' t o, Exec I W (driver testS leafS splitS nodeS) c c' t ∧
      t ≤ dcost (fun τ => tcP τ.piece) (fun τ => lcP τ.piece) (fun τ => scP τ.piece) (ncT ncP)
        (decM split n P) + 2 ∧
      PotOut (pg N P ℓ) o ∧ Res P o (Hb + 5) e c' ∧ G c' ∧ c'.nreg 3003 = h ∧
      HeapKeep Hb h Hb e c c' ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, g, ⟨o, hp, hr⟩, -, h3, hk, ho⟩ :=
    driveR (nspecR_dspecR hS) hHb (decM split n P) c hc hg r0 r1 r2 r3 m0 m1 m2 he hh hroom
      ⟨n, P, rfl, hin⟩
  rw [piece_decM] at hp hr
  exact ⟨c', t, o, ex, ht, hp, hr, g, h3, hk, ho⟩

universe w

/-- **`drive_split_mach` with room**: the same bound, with `h + (#D + 1) · R ≤ W` at the root
for room functions with `rL ≤ R`, `rS + rN ≤ R`. -/
theorem drive_split_machR (C C₀ : ℕ) {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] {M : CombMap D V F}
    {split : Finset D → Finset D × Finset D}
    (hsplit : ∀ P ⊆ reps M.dual, 1000000 < P.card →
      SplitF M.dual P (split P).1 (split P).2) {ℓ₀ : D → ℤ}
    (hneg : ∀ d, M.dual.tail d = M.dual.head d → 0 ≤ ℓ₀ d)
    {InP : ℕ → Finset D → ℕ → ℕ → Config → Prop}
    {Res : Finset D → Option (F → ℤ) → ℕ → ℕ → Config → Prop}
    {tcP lcP scP : Finset D → ℕ} {ncP : Finset D → Finset D → ℕ} {rL rS rN : Finset D → ℕ}
    {R : ℕ} (hRL : ∀ Q, rL Q ≤ R) (hRSN : ∀ Q, rS Q + rN Q ≤ R)
    (hS : NSpecR M.dual (minLen M.dual ℓ₀) split I W Hb testS leafS splitS nodeS G InP Res
      tcP lcP scP ncP rL rS rN) (hHb : 0 < Hb) {A B : ℕ}
    (hl : ∀ P : Finset D, P.card ≤ 1000000 → tcP P + lcP P ≤ A * (cNegMach C).leaf P.card + B)
    (hn : ∀ P₀ P₁ : Finset D, SplitF M.dual (P₀ ∪ P₁) P₀ P₁ →
      tcP (P₀ ∪ P₁) + scP (P₀ ∪ P₁) + ncP P₀ P₁ ≤ A * (cNegMach C).node (P₀ ∪ P₁).card
        (bdry M.dual P₀ P₁).card P₀.card (verts M.dual P₀).card P₁.card
        (verts M.dual P₁).card + B)
    {e h : ℕ} (c : Config) (hc : WordsBounded W c) (hg : G c) (r0 : c.nreg 3000 = 0)
    (r1 : c.nreg 3001 = 1) (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h)
    (m0 : c.nmem Hb = 0) (m1 : c.nmem (Hb + 1) = 0) (m2 : c.nmem (Hb + 2) = e)
    (he : Hb + 5 ≤ e) (hh : e ≤ h) (hroom : h + (Fintype.card D + 1) * R ≤ W)
    (hin : InP (Fintype.card D) (reps M.dual) (Hb + 5) e c) :
    ∃ c' t o, Exec I W (driver testS leafS splitS nodeS) c c' t ∧
      t ≤ (A + B + 80) * (cMach C C₀).negsssp (Fintype.card D) + B + 22 ∧
      PotOut (M.dual.graph ℓ₀) o ∧ Res (reps M.dual) o (Hb + 5) e c' ∧ G c' ∧
      c'.output = c.output := by
  have hR := roomT_decM_le hRL hRSN split (Fintype.card D) (reps M.dual)
  obtain ⟨c', t, o, ex, ht, hp, hr, g, -, -, ho⟩ :=
    drive_decR hS hHb (Fintype.card D) (reps M.dual) c hc hg r0 r1 r2 r3 m0 m1 m2 he hh
      (by omega) hin
  have hf : (decM split (Fintype.card D) (reps M.dual)).FDec M.dual :=
    decM_fDec hsplit _ _ (card_le_univ _) subset_rfl
  have hcost := dcost_le_negCost' (N := M.dual) (tcP := tcP) (lcP := lcP) (scP := scP)
    (ncP := ncP) hl hn (fun m hm => by show 1 ≤ 96 * m ^ 2; nlinarith)
    (fun m hm => by show 1 ≤ 1000 * m; omega) _ hf
  have hfd := fdecCost_le (cNegMach_bounds C) (piece_decM split _ _) hf
  have hk : (A + B + 80) * negCost M.dual (cNegMach C) (decM split (Fintype.card D)
      (reps M.dual)) ≤ (A + B + 80) * (cMach C C₀).negsssp (Fintype.card D) :=
    Nat.mul_le_mul_left _ (by show _ ≤ 10920 * negK C * _ * lg _ ^ 2 + 1000001 * negK C * _
                              omega)
  exact ⟨c', t, o, ex, by omega, potOut_graph_of_reps hneg hp, hr, g, ho⟩

/-- **`drive_msplit_mach` with room**: the whole recursion for negative lengths on the dual map,
on the machine's own split `msplit`, with the room invariant. -/
theorem drive_msplit_machR (C C₀ : ℕ) {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] {M : CombMap D V F} (g : Frame.GIds D F)
    (hM : M.dual.IsPlane) (hrot : M.dual.RotTrans) (hface : M.dual.FaceTrans)
    {ℓ₀ : D → ℤ} (hneg : ∀ d, M.dual.tail d = M.dual.head d → 0 ≤ ℓ₀ d)
    {InP : ℕ → Finset D → ℕ → ℕ → Config → Prop}
    {Res : Finset D → Option (F → ℤ) → ℕ → ℕ → Config → Prop}
    {tcP lcP scP : Finset D → ℕ} {ncP : Finset D → Finset D → ℕ} {rL rS rN : Finset D → ℕ}
    {R : ℕ} (hRL : ∀ Q, rL Q ≤ R) (hRSN : ∀ Q, rS Q + rN Q ≤ R)
    (hS : NSpecR M.dual (minLen M.dual ℓ₀) (Frame.msplit g M.dual) I W Hb testS leafS splitS
      nodeS G InP Res tcP lcP scP ncP rL rS rN) (hHb : 0 < Hb) {A B : ℕ}
    (hl : ∀ P : Finset D, P.card ≤ 1000000 → tcP P + lcP P ≤ A * (cNegMach C).leaf P.card + B)
    (hn : ∀ P₀ P₁ : Finset D, SplitF M.dual (P₀ ∪ P₁) P₀ P₁ →
      tcP (P₀ ∪ P₁) + scP (P₀ ∪ P₁) + ncP P₀ P₁ ≤ A * (cNegMach C).node (P₀ ∪ P₁).card
        (bdry M.dual P₀ P₁).card P₀.card (verts M.dual P₀).card P₁.card
        (verts M.dual P₁).card + B)
    {e h : ℕ} (c : Config) (hc : WordsBounded W c) (hg : G c) (r0 : c.nreg 3000 = 0)
    (r1 : c.nreg 3001 = 1) (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h)
    (m0 : c.nmem Hb = 0) (m1 : c.nmem (Hb + 1) = 0) (m2 : c.nmem (Hb + 2) = e)
    (he : Hb + 5 ≤ e) (hh : e ≤ h) (hroom : h + (Fintype.card D + 1) * R ≤ W)
    (hin : InP (Fintype.card D) (reps M.dual) (Hb + 5) e c) :
    ∃ c' t o, Exec I W (driver testS leafS splitS nodeS) c c' t ∧
      t ≤ (A + B + 80) * (cMach C C₀).negsssp (Fintype.card D) + B + 22 ∧
      PotOut (M.dual.graph ℓ₀) o ∧ Res (reps M.dual) o (Hb + 5) e c' ∧ G c' ∧
      c'.output = c.output :=
  drive_split_machR C C₀ (fun _ hP hs => Frame.msplit_splitF (g := g) hM hrot hface hP hs) hneg hRL hRSN
    hS hHb hl hn c hc hg r0 r1 r2 r3 m0 m1 m2 he hh hroom hin

end Driver

end NegSSSP

end PlanarFlow
