module

public import PlanarFlow.NegSSSP.NdDrive
public import PlanarFlow.NegSSSP.LeafCost

/-!
# The cost of the node step without its full branch: `O(m log m)`

* `heapLg_le_log`: `Heap.lg j ≤ ⌊log₂ j⌋ + 1`.
* **`nd_cost_le`**: for a piece of `m ≥ 1` darts with `k ≤ 2m` half-edges and `w ≤ 2m`
  vertices, `11 + splitSCost m k + wsCost k + ndCost m k w ≤ 60000 · m · lg m` (the test, the
  split with the clearing of its work area, the node step but its full branch).
* **`nd_hn`**: the hypothesis `hn` of `drive_msplit_nodeS` follows from the bound of the full
  branch alone, `ncF P₀ P₁ ≤ A · node + B`, once the separator constant `C` of `cNegMach C`
  is at least `60000` (with `A + 1` in place of `A`): the overhead of the node step is charged
  to the separator term `C · m · lg m` of the node.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset BKMNW

theorem heapLg_le_log (j : ℕ) : Heap.lg j ≤ Nat.log 2 j + 1 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [Heap.lg_zero]; omega
    · rw [Heap.lg_pos hj]
      by_cases h2 : j < 2
      · have : j / 2 = 0 := by omega
        rw [this, Heap.lg_zero]; omega
      · have e : Nat.log 2 j = Nat.log 2 (j / 2) + 1 := Nat.log_of_one_lt_of_le (by norm_num)
          (by omega)
        have := ih (j / 2) (by omega)
        omega

theorem log_two_mul_le {m : ℕ} (hm : 1 ≤ m) (a : ℕ) (ha : a ≤ 8 * m) :
    Nat.log 2 a ≤ Nat.log 2 m + 3 := by
  calc Nat.log 2 a ≤ Nat.log 2 (m * 2 * 2 * 2) := Nat.log_mono_right (by omega)
    _ = Nat.log 2 m + 3 := by
      rw [Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega),
        Nat.log_mul_base (by norm_num) (by omega)]

theorem log_two_le {m : ℕ} (hm : 1 ≤ m) (a : ℕ) (ha : a ≤ 2 * m) :
    Nat.log 2 a ≤ Nat.log 2 m + 1 := by
  calc Nat.log 2 a ≤ Nat.log 2 (m * 2) := Nat.log_mono_right (by omega)
    _ = Nat.log 2 m + 1 := Nat.log_mul_base (by norm_num) (by omega)

/-- The logarithmic facts at a piece of `m ≥ 1` darts. -/
theorem spWs_le {m k : ℕ} (hm : 1 ≤ m) (hk : k ≤ 2 * m) :
    spWs k ≤ 700 * (m * (Nat.log 2 m + 1)) := by
  have l2 : Nat.log 2 (3 * k) ≤ Nat.log 2 m + 3 := log_two_mul_le hm _ (by omega)
  have p2 : (Nat.log 2 (3 * k) + 2) * (3 * k) ≤ 30 * (m * (Nat.log 2 m + 1)) := by
    have : (Nat.log 2 (3 * k) + 2) * (3 * k) ≤ (5 * (Nat.log 2 m + 1)) * (6 * m) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (5 * (Nat.log 2 m + 1)) * (6 * m) = 30 * (m * (Nat.log 2 m + 1)) := by ring
    omega
  have hmX : m ≤ m * (Nat.log 2 m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold spWs
  rw [spB0_eq]
  generalize (Nat.log 2 (3 * k) + 2) * (3 * k) = A2 at p2 ⊢
  generalize m * (Nat.log 2 m + 1) = X at *
  omega

theorem splitT_le {m k : ℕ} (hm : 1 ≤ m) (hk : k ≤ 2 * m) :
    splitT k ≤ 60000 * (m * (Nat.log 2 m + 1)) := by
  have l1 : Nat.log 2 k ≤ Nat.log 2 m + 1 := log_two_le hm k hk
  have hsq : Nat.sqrt (12 * k) ≤ 12 * k := Nat.sqrt_le_self _
  have p1 : (1746 * k + 156) * (Nat.log 2 k + 3) ≤ 14592 * (m * (Nat.log 2 m + 1)) := by
    have : (1746 * k + 156) * (Nat.log 2 k + 3) ≤ (3648 * m) * (4 * (Nat.log 2 m + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (3648 * m) * (4 * (Nat.log 2 m + 1)) = 14592 * (m * (Nat.log 2 m + 1)) := by ring
    omega
  have hmX : m ≤ m * (Nat.log 2 m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold splitT bigT
  generalize (1746 * k + 156) * (Nat.log 2 k + 3) = A1 at p1 ⊢
  generalize Nat.sqrt (12 * k) = A5 at hsq ⊢
  generalize m * (Nat.log 2 m + 1) = X at *
  omega

theorem rnCost_le {m w : ℕ} (hm : 1 ≤ m) (hw : w ≤ 2 * m) :
    rnCost m w ≤ 1500 * (m * (Nat.log 2 m + 1)) := by
  have l3 : Heap.lg (2 * (w + 1)) ≤ Nat.log 2 m + 4 := by
    have := heapLg_le_log (2 * (w + 1))
    have := log_two_mul_le hm (2 * (w + 1)) (by omega)
    omega
  have p3 : (w + 1) * (23 * Heap.lg (2 * (w + 1)) + 21) ≤ 339 * (m * (Nat.log 2 m + 1)) := by
    have : (w + 1) * (23 * Heap.lg (2 * (w + 1)) + 21) ≤ (3 * m) * (113 * (Nat.log 2 m + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (3 * m) * (113 * (Nat.log 2 m + 1)) = 339 * (m * (Nat.log 2 m + 1)) := by ring
    omega
  have p4 : (13 * Heap.lg (2 * (w + 1)) + 20) * (m + w) ≤ 216 * (m * (Nat.log 2 m + 1)) := by
    have : (13 * Heap.lg (2 * (w + 1)) + 20) * (m + w) ≤ (72 * (Nat.log 2 m + 1)) * (3 * m) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (72 * (Nat.log 2 m + 1)) * (3 * m) = 216 * (m * (Nat.log 2 m + 1)) := by ring
    omega
  have p5 : Nat.log 2 m + 1 ≤ m * (Nat.log 2 m + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hmX : m ≤ m * (Nat.log 2 m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold rnCost osCost dkC
  generalize (w + 1) * (23 * Heap.lg (2 * (w + 1)) + 21) = A3 at p3 ⊢
  generalize (13 * Heap.lg (2 * (w + 1)) + 20) * (m + w) = A4 at p4 ⊢
  generalize Heap.lg (2 * (w + 1)) = H at l3 ⊢
  generalize m * (Nat.log 2 m + 1) = X at *
  omega

/-- **The node step without its full branch costs `O(m log m)`.** -/
theorem nd_cost_le {m k w : ℕ} (hm : 1 ≤ m) (hk : k ≤ 2 * m) (hw : w ≤ 2 * m) :
    11 + splitSCost m k + wsCost k + ndCost m k w ≤ 200000 * (m * lg m) := by
  have h1 := spWs_le hm hk
  have h2 := splitT_le hm hk
  have h3 := rnCost_le hm hw
  have hmX : m ≤ m * (Nat.log 2 m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  show _ ≤ 200000 * (m * (Nat.log 2 m + 1))
  unfold splitSCost ndCost ndBCost prepCost
  unfold wsCost
  generalize spWs k = S at h1 ⊢
  generalize splitT k = T at h2 ⊢
  generalize rnCost m w = R at h3 ⊢
  generalize m * (Nat.log 2 m + 1) = X at *
  omega

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {N : CombMap D V F}

/-- **The hypothesis `hn` of `drive_msplit_nodeS` from the bound of the full branch alone**:
the overhead of the node step (`nd_cost_le`) is charged to the separator term `C · m · lg m`
of the node cost, for `C ≥ 200000`. -/
theorem nd_hn {C A B : ℕ} (hC : 200000 ≤ C) {ncF : Finset D → Finset D → ℕ}
    (hF : ∀ P₀ P₁ : Finset D, SplitF N (P₀ ∪ P₁) P₀ P₁ →
      ncF P₀ P₁ ≤ A * (cNegMach C).node (P₀ ∪ P₁).card (bdry N P₀ P₁).card P₀.card
        (verts N P₀).card P₁.card (verts N P₁).card + B) :
    ∀ P₀ P₁ : Finset D, SplitF N (P₀ ∪ P₁) P₀ P₁ →
      11 + (splitSCost (P₀ ∪ P₁).card (ck N (P₀ ∪ P₁)) + wsCost (ck N (P₀ ∪ P₁))) +
        (ndCost (P₀ ∪ P₁).card (ck N (P₀ ∪ P₁)) (verts N (P₀ ∪ P₁)).card + ncF P₀ P₁) ≤
        (A + 1) * (cNegMach C).node (P₀ ∪ P₁).card (bdry N P₀ P₁).card P₀.card
          (verts N P₀).card P₁.card (verts N P₁).card + B := by
  intro P₀ P₁ hS
  have h0 : 0 < P₀.card := hS.2.2.1
  have hm : 1 ≤ (P₀ ∪ P₁).card := by
    have := card_le_card (subset_union_left : P₀ ⊆ P₀ ∪ P₁); omega
  have hc : 11 + splitSCost (P₀ ∪ P₁).card (ck N (P₀ ∪ P₁)) + wsCost (ck N (P₀ ∪ P₁)) +
      ndCost (P₀ ∪ P₁).card (ck N (P₀ ∪ P₁)) (verts N (P₀ ∪ P₁)).card ≤
      200000 * ((P₀ ∪ P₁).card * lg (P₀ ∪ P₁).card) :=
    nd_cost_le hm (card_rcl_le (N := N) (P₀ ∪ P₁)) (NTree.card_verts_le (N := N) (P₀ ∪ P₁))
  have hF' := hF P₀ P₁ hS
  have hsep : (cNegMach C).sep (P₀ ∪ P₁).card ≤ (cNegMach C).node (P₀ ∪ P₁).card
      (bdry N P₀ P₁).card P₀.card (verts N P₀).card P₁.card (verts N P₁).card := by
    unfold NegCosts.node; omega
  have hC' : 200000 * ((P₀ ∪ P₁).card * lg (P₀ ∪ P₁).card) ≤
      (cNegMach C).sep (P₀ ∪ P₁).card := by
    show _ ≤ C * (P₀ ∪ P₁).card * lg (P₀ ∪ P₁).card
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hC
  generalize (cNegMach C).node (P₀ ∪ P₁).card (bdry N P₀ P₁).card P₀.card (verts N P₀).card
    P₁.card (verts N P₁).card = nd at hF' hsep ⊢
  rw [Nat.add_mul, Nat.one_mul]
  omega

end Frame

namespace Driver

open Finset WordRAM WordRAM.Machine BKMNW Frame

universe w

variable {I : Input} {W : ℕ}

/-- **The whole negative-length recursion, `O(n log² n)`, given the full branch of the node
step**: `drive_msplit_nodeS` with the leaf cost (`leaf_cost_le`) and the overhead of the node
step (`nd_hn`) discharged, for a separator constant `C ≥ 200000`; the remaining hypotheses are
the full branch `Fs` (`hF`) and its cost `ncF ≤ A · node + B` (`hncF`). Bound
`(A + 1 + B + 80) · (cMach C C₀).negsssp (#D) + B + 22`, `cMach.negsssp n =
10920 · negK C · n · lg² n + 1000001 · negK C · n`. -/
theorem drive_msplit_nodeS_cost (C C₀ : ℕ) (hC : 200000 ≤ C) {D V F : Type w} [Fintype D]
    [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    {M : CombMap D V F} (g : GIds D F) (hM : M.dual.IsPlane) (hrot : M.dual.RotTrans)
    (hface : M.dual.FaceTrans)
    {ℓ₀ : D → ℤ} (hneg : ∀ d, M.dual.tail d = M.dual.head d → 0 ≤ ℓ₀ d)
    {L Hb Gt : ℕ} (hGt : spWs (Fintype.card D) < Gt) (hGH : Gt + g.G ≤ Hb)
    (hℓ : ∀ x, |minLen M.dual ℓ₀ x| ≤ L) (hsumL : ∑ x, |minLen M.dual ℓ₀ x| ≤ L)
    (hWL : 8 * Fintype.card D * Fintype.card D * (L + 1) + 3 * L + 2 ≤ W)
    (hWL7 : 7 * L + 2 ≤ W) (hW6 : 1000000 ≤ W) {Fs : Stmt}
    {ncF : Finset D → Finset D → ℕ} {rF : Finset D → ℕ} {RF : ℕ} (hRF : ∀ Q, rF Q ≤ RF)
    (hF : ∀ n P d e bl el er c f₀ f₁, GZ0 Hb c → WordsBounded W c →
      c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = bl + 5 → c.nreg 3007 = el →
      c.nreg 3008 = el + 5 → c.nreg 3009 = er → c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e →
      e ≤ bl → bl + 5 ≤ el → el + 5 ≤ er → bl + rF P ≤ W →
      InPR g M.dual (minLen M.dual ℓ₀) L (n + 1) P d e c →
      Cnd (msplit g M.dual) (n + 1) P →
      PotOut (pg M.dual (msplit g M.dual P).1 (minLen M.dual ℓ₀)) (some f₀) →
      PotOut (pg M.dual (msplit g M.dual P).2 (minLen M.dual ℓ₀)) (some f₁) →
      Res g M.dual L (msplit g M.dual P).1 (some f₀) (bl + 5) el c →
      Res g M.dual L (msplit g M.dual P).2 (some f₁) (el + 5) er c →
      (bdry M.dual (msplit g M.dual P).1 (msplit g M.dual P).2).Nonempty →
      ∃ c' t o, Exec I W Fs c c' t ∧ t ≤ ncF (msplit g M.dual P).1 (msplit g M.dual P).2 ∧
        GZ0 Hb c' ∧ RegKeep c c' ∧ HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧
        PotOut (pg M.dual P (minLen M.dual ℓ₀)) o ∧ Res g M.dual L P o d e c')
    (hHb : 0 < Hb) {A B : ℕ} (hA : 20 ≤ A) (hB : 400 ≤ B)
    (hncF : ∀ P₀ P₁ : Finset D, SplitF M.dual (P₀ ∪ P₁) P₀ P₁ →
      ncF P₀ P₁ ≤ A * (cNegMach C).node (P₀ ∪ P₁).card (bdry M.dual P₀ P₁).card P₀.card
        (verts M.dual P₀).card P₁.card (verts M.dual P₁).card + B)
    {e h : ℕ} (c : Config) (hc : WordsBounded W c) (hg : GZ0 Hb c)
    (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1) (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h)
    (m0 : c.nmem Hb = 0) (m1 : c.nmem (Hb + 1) = 0)
    (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hroom : h + (Fintype.card D + 1) *
      roomB (Fintype.card D) (66 * Fintype.card D + 31 + RF) ≤ W)
    (hin : InPR g M.dual (minLen M.dual ℓ₀) L (Fintype.card D) (reps M.dual) (Hb + 5) e c) :
    ∃ c' t o, Exec I W (driver testS (leafS Gt) splitS0 (nodeS Gt Fs)) c c' t ∧
      t ≤ (A + 1 + B + 80) * (cMach C C₀).negsssp (Fintype.card D) + B + 22 ∧
      PotOut (M.dual.graph ℓ₀) o ∧ Res g M.dual L (reps M.dual) o (Hb + 5) e c' ∧
      GZ0 Hb c' ∧ c'.output = c.output :=
  drive_msplit_nodeS C C₀ g hM hrot hface hneg hGt hGH hℓ hsumL hWL hWL7 hW6 hRF hF hHb
    (fun P _ => leaf_cost_le C (by omega) hB P) (nd_hn hC hncF) c hc hg r0 r1 r2 r3 m0 m1 m2
    he hh hroom hin

end Driver

namespace Frame

end Frame

end NegSSSP

end PlanarFlow
