module

public import PlanarFlow.NegSSSP.BFExecAny
public import PlanarFlow.NegSSSP.NodeRunA

/-!
# Bellman–Ford of a node from the matrices in slots, as one run

After the two parts of a node (`PlanarFlow/NegSSSP/NodeRunD.lean`), the flags and the lengths of
the two dense distance graphs (row-major, `b²` entries each) and the order `π` lie in regions
above the work space of Bellman–Ford. `bfStage` runs Bellman–Ford on them in **one run**:

1. `zeroRegs (List.range 85)`, `bfSet`: the registers of `bfStartP` computed from `b` (`r802`),
   the registers below `85` bounded by `bfWP b`;
2. `clrProg`: the natural memory `≤ bfWP b` cleared;
3. three copies (`cpyProg`): `π` to `5 b + 2`, the flags and the lengths of the two matrices to
   their places in `bfStartP` (`BFMem`);
4. `bfFull` inside the configuration (`bfFull_exec_emb`);
5. `bfOut ; cpyProg`: the flag of the outcome saved in `r990`, the values `E` copied to a slot
   (`r810`), and a list of `b` natural cells (`r973`, the vertex numbers of the order of the
   first part) copied to a slot (`r809`).

* `bfStage_exec`: within `bfCostP b + 4 bfWP b + 22 b² + 22 b + 200` steps, the values `E` at
  the slot, `r990 = 0` with `Feas2O … E`, or `r990 = 1` and no feasible potential; the registers
  `800 … 899` and `≥ 919` (but `990`), the natural memory above `bfWP b` outside the slot of the
  list, the real memory above `bfWP b` outside the slot of the values and a scratch region, and
  the output are kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge

variable {I : Input} {W : ℕ}

/-- The registers of `bfStartP` from `b = r802` (scratch `r50 … r58`), `r86 = 5 b + 2` (kept by
`bfFull`), and `r900 = bfWP b + 1` (the bound of the clearing). -/
def bfSet : Stmt :=
  block [.copyN 1 802, .constN 10 1, .constN 4 0, .mulN 50 1 1, .constN 51 2,
    .addN 52 1 1, .addN 53 52 52, .addN 54 53 1, .addN 9 54 51, .copyN 3 9, .addN 8 9 1,
    .addN 42 8 1, .addN 81 42 50, .addN 55 50 50, .addN 43 42 55, .addN 56 54 54, .addN 57 56 51,
    .addN 41 57 55, .addN 80 41 50, .addN 40 80 50, .copyN 2 40, .addN 7 40 55, .copyN 86 9,
    .constN 58 11, .addN 900 7 55, .addN 900 900 53, .addN 900 900 58]

lemma upd_bnd {f : ℕ → ℕ} {B r₀ v : ℕ} (hf : ∀ r < 85, f r ≤ B) (hv : r₀ < 85 → v ≤ B) :
    ∀ r < 85, upd f r₀ v r ≤ B := fun r hr => by
  rw [upd_apply]; split_ifs with h
  · exact hv (h ▸ hr)
  · exact hf r hr

theorem bfSet_exec {b : ℕ} (c : Config) (hc : WordsBounded W c) (hb : c.nreg 802 = b)
    (hW : bfWP b + 1 ≤ W) (hz : ∀ r < 85, c.nreg r ≤ bfWP b) :
    ∃ c' k, Exec I W bfSet c c' k ∧ k = 27 ∧ BFRegs b c' ∧ c'.nreg 50 = b * b ∧
      c'.nreg 86 = 5 * b + 2 ∧ c'.nreg 900 = bfWP b + 1 ∧ (∀ r < 85, c'.nreg r ≤ bfWP b) ∧
      (∀ r, 85 ≤ r → r ≠ 86 → r ≠ 900 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hWb : bfWP b = 8 * (b * b) + 14 * b + 12 := rfl
  unfold bfSet
  exec_block
  all_goals try (config_simp; (try simp only [hb]); omega)
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals (try config_simp); (try simp only [hb]); (try omega)
  · repeat refine upd_bnd ?_ (fun _ => by omega)
    exact hz
  · simp (disch := omega) only [upd_other]

/-- Before a copy: the registers of `cpyProg` from five registers. -/
def cpS (rn rDn rSn rDr rSr : ℕ) : Stmt :=
  block [.copyN 910 rn, .copyN 911 rDn, .copyN 912 rSn, .copyN 913 rDr, .copyN 914 rSr]

theorem cpS_exec {rn rDn rSn rDr rSr : ℕ} (h : (rn < 910 ∨ 914 < rn) ∧ (rDn < 910 ∨ 914 < rDn) ∧
    (rSn < 910 ∨ 914 < rSn) ∧ (rDr < 910 ∨ 914 < rDr) ∧ (rSr < 910 ∨ 914 < rSr)) (c : Config)
    (hc : WordsBounded W c) :
    ∃ c' k, Exec I W (cpS rn rDn rSn rDr rSr) c c' k ∧ k = 5 ∧ c'.nreg 910 = c.nreg rn ∧
      c'.nreg 911 = c.nreg rDn ∧ c'.nreg 912 = c.nreg rSn ∧ c'.nreg 913 = c.nreg rDr ∧
      c'.nreg 914 = c.nreg rSr ∧ (∀ r, (r < 910 ∨ 914 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cpS
  exec_block
  config_simp
  simp only [upd_apply]
  and_intros
  all_goals (try intro r hr)
  all_goals split_ifs <;> first | omega | rfl

/-- After `bfFull`: the flag saved in `r990`. -/
def bfOut : Stmt := block [.copyN 990 30]

theorem bfOut_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec I W bfOut c c' k ∧ k = 1 ∧ c'.nreg 990 = c.nreg 30 ∧
      (∀ r, r ≠ 990 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bfOut
  exec_block
  config_simp
  intro r hr; simp (disch := omega) only [upd_other]

lemma rmLt {b s t : ℕ} (hs : s < b) (ht : t < b) : s * b + t < b * b := by nlinarith

/-- A row-major index. -/
lemma rowmaj {b e : ℕ} (he : e < b * b) : ∃ s < b, ∃ t < b, e = s * b + t := by
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | h
    · simp at he
    · exact h
  refine ⟨e / b, ?_, e % b, Nat.mod_lt _ hb, (Nat.div_add_mod' e b).symm⟩
  exact (Nat.div_lt_iff_lt_mul hb).2 he

/-- **Bellman–Ford of a node from the slots.** -/
def bfStage : Stmt :=
  .seq (zeroRegs (List.range 85)) <| .seq bfSet <| .seq clrProg <|
  .seq (cpS 1 9 970 974 4) <| .seq cpyProg <| .seq (cpS 50 42 971 41 971) <| .seq cpyProg <|
  .seq (cpS 50 81 972 80 972) <| .seq cpyProg <| .seq bfFull <| .seq bfOut <|
  .seq (cpS 802 809 973 810 86) cpyProg

/-- The layout of `bfStage`: `π` at `πb`, the matrices at `F0`, `F1` (natural flags and real
lengths), the list at `Ob`, the real scratch `R` of the copy of `π`, the slots `Z6`, `Z7` of the
list and of the values, all above `bfWP b` and below `W'`. -/
structure BLay (b πb F0 F1 Ob R Z6 Z7 W' : ℕ) : Prop where
  wp : bfWP b + 2 ≤ W'
  pi : bfWP b < πb
  piW : πb + b ≤ W'
  f0 : bfWP b < F0
  f0W : F0 + b * b ≤ W'
  f1 : bfWP b < F1
  f1W : F1 + b * b ≤ W'
  ob : bfWP b < Ob
  obW : Ob + b ≤ W'
  r : bfWP b < R
  rW : R + b ≤ W'
  rF0 : R + b ≤ F0 ∨ F0 + b * b ≤ R
  rF1 : R + b ≤ F1 ∨ F1 + b * b ≤ R
  z6 : bfWP b < Z6
  z6W : Z6 + b ≤ W'
  z6O : Z6 + b ≤ Ob ∨ Ob + b ≤ Z6
  z7 : bfWP b < Z7
  z7W : Z7 + b ≤ W'

set_option maxHeartbeats 4000000 in
/-- **Bellman–Ford of a node from the slots, as one run** (see the module docstring). -/
theorem bfStage_exec {b : ℕ} {X₁ X₂ : ℕ → ℕ → Prop} {D₁ D₂ : ℕ → ℕ → ℤ} {π : ℕ → ℕ}
    (hπ : IsPermB b π) (hD₁ : CrossingX b X₁ D₁) (hD₂ : CrossingX b X₂ D₂)
    {πb F0 F1 Ob R Z6 Z7 W' : ℕ} (hL : BLay b πb F0 F1 Ob R Z6 Z7 W') (c : Config)
    (hc : WordsBounded W' c) (h802 : c.nreg 802 = b) (h809 : c.nreg 809 = Z6)
    (h810 : c.nreg 810 = Z7) (h970 : c.nreg 970 = πb) (h971 : c.nreg 971 = F0)
    (h972 : c.nreg 972 = F1) (h973 : c.nreg 973 = Ob) (h974 : c.nreg 974 = R)
    (hπm : ∀ i < b, c.nmem (πb + i) = π i)
    (hF0 : ∀ s < b, ∀ t < b, c.nmem (F0 + (s * b + t)) = finB X₁ s t ∧
      c.rmem (F0 + (s * b + t)) = (D₁ s t : ℝ))
    (hF1 : ∀ s < b, ∀ t < b, c.nmem (F1 + (s * b + t)) = finB X₂ s t ∧
      c.rmem (F1 + (s * b + t)) = (D₂ s t : ℝ)) :
    ∃ c' k, ∃ E : ℕ → ℤ, Exec I W' bfStage c c' k ∧
      k ≤ bfCostP b + 4 * bfWP b + 22 * (b * b) + 22 * b + 200 ∧
      (∀ v < b, c'.rmem (Z7 + v) = E v) ∧
      ((c'.nreg 990 = 0 ∧ Feas2O b X₁ D₁ X₂ D₂ π E) ∨
        (c'.nreg 990 = 1 ∧ ¬ ∃ E', Feas2O b X₁ D₁ X₂ D₂ π E')) ∧
      (∀ i < b, c'.nmem (Z6 + i) = c.nmem (Ob + i)) ∧
      (∀ r, (800 ≤ r ∧ r < 900) ∨ (919 ≤ r ∧ r ≠ 990) → c'.nreg r = c.nreg r) ∧
      (∀ a, bfWP b < a → (a < Z6 ∨ Z6 + b ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, bfWP b < a → (a < R ∨ R + b ≤ a) → (a < Z7 ∨ Z7 + b ≤ a) →
        c'.rmem a = c.rmem a) ∧
      c'.output = c.output := by
  obtain ⟨wp, pi, piW, f0, f0W, f1, f1W, ob, obW, r, rW, rF0, rF1, z6, z6W, z6O, z7, z7W⟩ := hL
  have hWb : bfWP b = 8 * (b * b) + 14 * b + 12 := rfl
  -- 0., 1. the registers
  obtain ⟨c₁, k₁, e₁, hk₁, hz₁, -, hnm₁, hrm₁, ho₁⟩ :=
    zeroRegs_exec (P := I) (List.range 85) c hc
  have hn₁ : ∀ r, 85 ≤ r → c₁.nreg r = c.nreg r := fun r hr => by
    rw [hz₁ r, ite_eq_right_of_eq_false _ _ (eq_false (by simp; omega))]
  obtain ⟨c₂, k₂, e₂, hk₂, hR₂, r50, r86, r900, hb₂, hn₂, -, hnm₂, hrm₂, ho₂⟩ :=
    bfSet_exec (I := I) (b := b) c₁ e₁.wb_right (by rw [hn₁ 802 (by omega), h802])
      (by omega) (fun r hr => by
        rw [hz₁ r, ite_eq_left_of_eq_true _ _ (eq_true (by simp; omega))]; exact Nat.zero_le _)
  have hn₂' : ∀ r, 85 ≤ r → r ≠ 86 → r ≠ 900 → c₂.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [hn₂ r h1 h2 h3, hn₁ r h1]
  -- 2. the clearing
  obtain ⟨c₃, k₃, e₃, hk₃, z₃, hm₃, hn₃, hrr₃, hrm₃, ho₃⟩ :=
    clrProg_exec (P := I) (L := bfWP b + 1) (by omega) c₂ e₂.wb_right r900
  -- 3., 4. `π`
  obtain ⟨c₄, k₄, e₄, hk₄, p910, p911, p912, p913, p914, hn₄, hrr₄, hnm₄, hrm₄, ho₄⟩ :=
    cpS_exec (I := I) (rn := 1) (rDn := 9) (rSn := 970) (rDr := 974) (rSr := 4) (by omega) c₃
      e₃.wb_right
  have g : ∀ r, r < 85 → c₄.nreg r = c₂.nreg r := fun r hr => by
    rw [hn₄ r (by omega), hn₃ r (by omega)]
  have hL₄ : CpyLay b (5 * b + 2) πb R 0 W' :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨c₅, k₅, e₅, hk₅, hcp₅, hm₅, hr₅, hn₅, hrr₅, ho₅⟩ := cpyProg_exec (P := I) hL₄ c₄
    e₄.wb_right (by rw [p910, hn₃ 1 (by omega), hR₂.r1])
    (by rw [p911, hn₃ 9 (by omega), hR₂.r9])
    (by rw [p912, hn₃ 970 (by omega), hn₂' 970 (by omega) (by omega) (by omega), h970])
    (by rw [p913, hn₃ 974 (by omega), hn₂' 974 (by omega) (by omega) (by omega), h974])
    (by rw [p914, hn₃ 4 (by omega), hR₂.r4])
  -- 5., 6. the first matrix
  obtain ⟨c₆, k₆, e₆, hk₆, q910, q911, q912, q913, q914, hn₆, hrr₆, hnm₆, hrm₆, ho₆⟩ :=
    cpS_exec (I := I) (rn := 50) (rDn := 42) (rSn := 971) (rDr := 41) (rSr := 971) (by omega) c₅
      e₅.wb_right
  have hL₆ : CpyLay (b * b) (7 * b + 2) F0 (10 * b + 2 + 2 * (b * b)) F0 W' :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have g₅ : ∀ r, r < 85 ∨ (900 ≤ r ∧ r < 910) ∨ 970 ≤ r → c₅.nreg r = c₃.nreg r := fun r hr => by
    rw [hn₅ r (by omega), hn₄ r (by omega)]
  have g₃ : ∀ r, 970 ≤ r → c₃.nreg r = c.nreg r := fun r hr => by
    rw [hn₃ r (by omega), hn₂' r (by omega) (by omega) (by omega)]
  obtain ⟨c₇, k₇, e₇, hk₇, hcp₇, hm₇, hr₇, hn₇, hrr₇, ho₇⟩ := cpyProg_exec (P := I) hL₆ c₆
    e₆.wb_right (by rw [q910, g₅ 50 (by omega), hn₃ 50 (by omega), r50])
    (by rw [q911, g₅ 42 (by omega), hn₃ 42 (by omega), hR₂.r42])
    (by rw [q912, g₅ 971 (by omega), g₃ 971 (by omega), h971])
    (by rw [q913, g₅ 41 (by omega), hn₃ 41 (by omega), hR₂.r41])
    (by rw [q914, g₅ 971 (by omega), g₃ 971 (by omega), h971])
  -- 7., 8. the second matrix
  obtain ⟨c₈, k₈, e₈, hk₈, u910, u911, u912, u913, u914, hn₈, hrr₈, hnm₈, hrm₈, ho₈⟩ :=
    cpS_exec (I := I) (rn := 50) (rDn := 81) (rSn := 972) (rDr := 80) (rSr := 972) (by omega) c₇
      e₇.wb_right
  have hL₈ : CpyLay (b * b) (7 * b + 2 + b * b) F1 (10 * b + 2 + 3 * (b * b)) F1 W' :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have g₇ : ∀ r, r < 85 ∨ (900 ≤ r ∧ r < 910) ∨ 970 ≤ r → c₇.nreg r = c₃.nreg r := fun r hr => by
    rw [hn₇ r (by omega), hn₆ r (by omega), g₅ r hr]
  obtain ⟨c₉, k₉, e₉, hk₉, hcp₉, hm₉, hr₉, hn₉, hrr₉, ho₉⟩ := cpyProg_exec (P := I) hL₈ c₈
    e₈.wb_right (by rw [u910, g₇ 50 (by omega), hn₃ 50 (by omega), r50])
    (by rw [u911, g₇ 81 (by omega), hn₃ 81 (by omega), hR₂.r81])
    (by rw [u912, g₇ 972 (by omega), g₃ 972 (by omega), h972])
    (by rw [u913, g₇ 80 (by omega), hn₃ 80 (by omega), hR₂.r80])
    (by rw [u914, g₇ 972 (by omega), g₃ 972 (by omega), h972])
  have g₉ : ∀ r, r < 85 ∨ (900 ≤ r ∧ r < 910) ∨ 970 ≤ r → c₉.nreg r = c₃.nreg r := fun r hr => by
    rw [hn₉ r (by omega), hn₈ r (by omega), g₇ r hr]
  -- the memory before Bellman–Ford
  have hmc : ∀ a, bfWP b < a → c₉.nmem a = c.nmem a := fun a ha => by
    rw [hm₉ a (Or.inr (by omega)), hnm₈, hm₇ a (Or.inr (by omega)), hnm₆,
      hm₅ a (Or.inr (by omega)), hnm₄, hm₃ a (by omega), hnm₂, hnm₁]
  have hrc : ∀ a, bfWP b < a → (a < R ∨ R + b ≤ a) → c₉.rmem a = c.rmem a := fun a ha ha' => by
    rw [hr₉ a (Or.inr (by omega)), hrm₈, hr₇ a (Or.inr (by omega)), hrm₆, hr₅ a ha', hrm₄,
      hrm₃, hrm₂, hrm₁]
  have hF0' : ∀ e < b * b, c₉.nmem (7 * b + 2 + e) = c.nmem (F0 + e) ∧
      c₉.rmem (10 * b + 2 + 2 * (b * b) + e) = c.rmem (F0 + e) := fun e he => by
    refine ⟨?_, ?_⟩
    · rw [hm₉ _ (Or.inl (by omega)), hnm₈, (hcp₇ e he).1, hnm₆, ← hmc _ (by omega),
        hm₉ _ (Or.inr (by omega)), hnm₈, hm₇ _ (Or.inr (by omega)), hnm₆]
    · rw [hr₉ _ (Or.inl (by omega)), hrm₈, (hcp₇ e he).2, hrm₆,
        ← hrc _ (by omega) (by omega), hr₉ _ (Or.inr (by omega)), hrm₈,
        hr₇ _ (Or.inr (by omega)), hrm₆]
  have hF1' : ∀ e < b * b, c₉.nmem (7 * b + 2 + b * b + e) = c.nmem (F1 + e) ∧
      c₉.rmem (10 * b + 2 + 3 * (b * b) + e) = c.rmem (F1 + e) := fun e he => by
    refine ⟨?_, ?_⟩
    · rw [(hcp₉ e he).1, hnm₈, ← hmc _ (by omega), hm₉ _ (Or.inr (by omega)), hnm₈]
    · rw [(hcp₉ e he).2, hrm₈, ← hrc _ (by omega) (by omega), hr₉ _ (Or.inr (by omega)), hrm₈]
  have hπ' : ∀ i < b, c₉.nmem (5 * b + 2 + i) = π i := fun i hi => by
    rw [hm₉ _ (Or.inl (by omega)), hnm₈, hm₇ _ (Or.inl (by omega)), hnm₆, (hcp₅ i hi).1, hnm₄,
      hm₃ _ (by omega), hnm₂, hnm₁, hπm i hi]
  have hBM : BFMem b X₁ D₁ X₂ D₂ π c₉ := by
    refine ⟨hπ', fun s t hs ht => ?_, fun s t hs ht => ?_, fun s t hs ht => ?_,
      fun s t hs ht => ?_⟩
    · have := (hF0' _ (rmLt hs ht)).1
      rw [← Nat.add_assoc] at this; rw [this]; exact (hF0 s hs t ht).1
    · have := (hF1' _ (rmLt hs ht)).1
      rw [← Nat.add_assoc] at this; rw [this]; exact (hF1 s hs t ht).1
    · have := (hF0' _ (rmLt hs ht)).2
      rw [← Nat.add_assoc] at this; rw [this]; exact (hF0 s hs t ht).2
    · have := (hF1' _ (rmLt hs ht)).2
      rw [← Nat.add_assoc] at this; rw [this]; exact (hF1 s hs t ht).2
  have hBR : BFRegs b c₉ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [g₉ _ (by omega), hn₃ _ (by omega)]
    exacts [hR₂.r1, hR₂.r2, hR₂.r3, hR₂.r4, hR₂.r7, hR₂.r8, hR₂.r9, hR₂.r10, hR₂.r40, hR₂.r41,
      hR₂.r42, hR₂.r43, hR₂.r80, hR₂.r81]
  have hmb : ∀ a ≤ bfWP b, c₉.nmem a ≤ bfWP b := by
    intro a ha
    by_cases h1 : 7 * b + 2 + b * b ≤ a ∧ a < 7 * b + 2 + b * b + b * b
    · obtain ⟨e, rfl⟩ : ∃ e, a = 7 * b + 2 + b * b + e := ⟨a - (7 * b + 2 + b * b), by omega⟩
      obtain ⟨s, hs, t, ht, rfl⟩ := rowmaj (show e < b * b by omega)
      rw [(hF1' _ (by omega)).1, (hF1 s hs t ht).1]
      have := finB_le (X := X₂) s t; omega
    by_cases h2 : 7 * b + 2 ≤ a ∧ a < 7 * b + 2 + b * b
    · obtain ⟨e, rfl⟩ : ∃ e, a = 7 * b + 2 + e := ⟨a - (7 * b + 2), by omega⟩
      obtain ⟨s, hs, t, ht, rfl⟩ := rowmaj (show e < b * b by omega)
      rw [(hF0' _ (by omega)).1, (hF0 s hs t ht).1]
      have := finB_le (X := X₁) s t; omega
    rw [hm₉ a (by omega), hnm₈, hm₇ a (by omega), hnm₆]
    by_cases h3 : 5 * b + 2 ≤ a ∧ a < 5 * b + 2 + b
    · obtain ⟨i, rfl⟩ : ∃ i, a = 5 * b + 2 + i := ⟨a - (5 * b + 2), by omega⟩
      rw [(hcp₅ i (by omega)).1, hnm₄, hm₃ _ (by omega), hnm₂, hnm₁, hπm i (by omega)]
      have := hπ.lt i (by omega); omega
    rw [hm₅ a (by omega), hnm₄, z₃ a (by omega)]; exact Nat.zero_le _
  -- 9. Bellman–Ford
  obtain ⟨d, k₁₀, e₁₀, hk₁₀, ⟨E, hE, hout, -⟩, ho₁₀, hn₁₀, -, hm₁₀, hr₁₀⟩ :=
    bfFull_exec_emb (P := I) hπ hD₁ hD₂ (W' := W') (by omega) c₉ e₉.wb_right hBR hBM
      (fun r hr => by rw [g₉ r (by omega), hn₃ r (by omega)]; exact hb₂ r hr) hmb
  -- 10. the flag
  obtain ⟨c₁₁, k₁₁, e₁₁, hk₁₁, f990, hn₁₁, -, hnm₁₁, hrm₁₁, ho₁₁⟩ :=
    bfOut_exec (I := I) d e₁₀.wb_right
  have gd : ∀ r, (800 ≤ r ∧ r < 900) ∨ (919 ≤ r ∧ r ≠ 990) ∨ r = 86 → c₁₁.nreg r =
      c₉.nreg r := fun r hr => by rw [hn₁₁ r (by omega), hn₁₀ r (by omega)]
  -- 11., 12. the outputs
  obtain ⟨c₁₂, k₁₂, e₁₂, hk₁₂, v910, v911, v912, v913, v914, hn₁₂, hrr₁₂, hnm₁₂, hrm₁₂, ho₁₂⟩ :=
    cpS_exec (I := I) (rn := 802) (rDn := 809) (rSn := 973) (rDr := 810) (rSr := 86) (by omega)
      c₁₁ e₁₁.wb_right
  have g₉' : ∀ r, (800 ≤ r ∧ r < 900) ∨ (919 ≤ r ∧ r ≠ 990) → c₉.nreg r = c.nreg r :=
    fun r hr => by
      rw [hn₉ r (by omega), hn₈ r (by omega), hn₇ r (by omega), hn₆ r (by omega),
        hn₅ r (by omega), hn₄ r (by omega), hn₃ r (by omega),
        hn₂' r (by omega) (by omega) (by omega)]
  have hL₁₂ : CpyLay b Z6 Ob Z7 (5 * b + 2) W' :=
    ⟨z6O, Or.inr (by omega), by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨c₁₃, k₁₃, e₁₃, hk₁₃, hcp₁₃, hm₁₃, hr₁₃, hn₁₃, hrr₁₃, ho₁₃⟩ := cpyProg_exec (P := I)
    hL₁₂ c₁₂ e₁₂.wb_right (by rw [v910, gd 802 (by omega), g₉' 802 (by omega), h802])
    (by rw [v911, gd 809 (by omega), g₉' 809 (by omega), h809])
    (by rw [v912, gd 973 (by omega), g₉' 973 (by omega), h973])
    (by rw [v913, gd 810 (by omega), g₉' 810 (by omega), h810])
    (by rw [v914, gd 86 (by omega), hn₉ 86 (by omega), hn₈ 86 (by omega), hn₇ 86 (by omega),
      hn₆ 86 (by omega), hn₅ 86 (by omega), hn₄ 86 (by omega), hn₃ 86 (by omega), r86])
  refine ⟨c₁₃, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + (k₈ + (k₉ + (k₁₀ + (k₁₁ + (k₁₂ +
    k₁₃))))))))))), E, Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅
      (Exec.seq e₆ (Exec.seq e₇ (Exec.seq e₈ (Exec.seq e₉ (Exec.seq e₁₀ (Exec.seq e₁₁
        (Exec.seq e₁₂ e₁₃))))))))))), ?_, fun v hv => ?_, ?_, fun i hi => ?_,
    fun r hr => ?_, fun a ha ha' => ?_, fun a ha ha' ha'' => ?_, ?_⟩
  · simp only [List.length_range] at hk₁
    omega
  · rw [(hcp₁₃ v hv).2, hrm₁₂, hrm₁₁, hE v hv]
  · rw [hn₁₃ 990 (by omega), hn₁₂ 990 (by omega), f990]; exact hout
  · rw [(hcp₁₃ i hi).1, hnm₁₂, hnm₁₁, hm₁₀ _ (by omega), hmc _ (by omega)]
  · rw [hn₁₃ r (by omega), hn₁₂ r (by omega), gd r (by omega), g₉' r hr]
  · rw [hm₁₃ a ha', hnm₁₂, hnm₁₁, hm₁₀ a ha, hmc a ha]
  · rw [hr₁₃ a ha'', hrm₁₂, hrm₁₁, hr₁₀ a ha, hrc a ha ha']
  · rw [ho₁₃, ho₁₂, ho₁₁, ho₁₀, ho₉, ho₈, ho₇, ho₆, ho₅, ho₄, ho₃, ho₂, ho₁]

end NegSSSP

end PlanarFlow
