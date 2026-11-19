module

public import PlanarFlow.BKMNW.PpOut
public import PlanarFlow.BKMNW.PpHyp
public import PlanarFlow.BKMNW.NoEmit

/-!
# The print of the flow, and the frame of the max-flow program

* `prB`: from the input, the frame base `Hb + 5 = 128 n + 2 K + 8` of the root call (`n = nd`,
  `K = nv`); prints `Z = mem[Hb + 8]`, then the `N = mem[Hb + 5]` cells of the root's flow array
  `FL` from `Hb + 9 + 6 N`. **`prB_exec`** (`≤ 7 N + 30` steps).
* `mfProg sepL stepP`: the max-flow program of `mfMain_cMachXGE`;
  **`noEmit_mfProg`**: it prints nothing when `sepL` and `stepP` print nothing.
* `capS_le_bigN`: the capacities on slots are at most `Z = bigN`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv Feas
  NegSSSP.Driver

variable {P : Input} {W : ℕ}

/-- The setup of the print of the flow: `8750 = Hb + 5` (the frame), `8741 = N`, print `Z`,
`8775 = Hb + 9 + 6 N` (the flow array), stride `1`. -/
def prBS : Stmt :=
  block [.constN 8778 2, .readIn 8700 8778, .constN 8778 0, .readIn 8707 8778,
    .constN 8778 128, .mulN 8750 8700 8778, .constN 8778 2, .mulN 8751 8707 8778,
    .addN 8750 8750 8751, .constN 8778 8, .addN 8750 8750 8778, .loadN 8741 8750,
    .constN 8778 3, .addN 8752 8750 8778, .loadN 8753 8752, .outN 8753,
    .constN 8778 6, .mulN 8775 8741 8778, .addN 8775 8775 8750, .constN 8778 4,
    .addN 8775 8775 8778, .constN 8776 1, .constN 8704 1]

/-- **The print of the flow** of the root call. -/
def prB : Stmt := .seq prBS prL

/-- The frame base of the root call: `Hb + 5`, `Hb = 128 n + 2 K + 3`. -/
def frB (d : List ℕ) : ℕ := 128 * nd d + 2 * nv d + 8

theorem prBS_exec {d : List ℕ} (hP : P.data = d) (hwd : ∀ i, word d i ≤ W) (c : Config)
    (hc : WordsBounded W c) {N Z : ℕ} (hN : c.nmem (frB d) = N) (hZ : c.nmem (frB d + 3) = Z)
    (hW : frB d + 8 * N + 200 ≤ W) :
    ∃ c' t, Exec P W prBS c c' t ∧ t = 23 ∧ c'.nreg 8741 = N ∧
      c'.nreg 8775 = frB d + 4 + 6 * N ∧ c'.nreg 8776 = 1 ∧ c'.nreg 8704 = 1 ∧
      c'.nmem = c.nmem ∧ c'.output = c.output ++ [Z] := by
  have e2 : d.getD 2 0 = nd d := rfl
  have e0 : d.getD 0 0 = nv d := rfl
  unfold frB at hN hZ hW
  have k1 : nd d * 128 + nv d * 2 + 8 = 128 * nd d + 2 * nv d + 8 := by ring
  have hN' : c.nmem (nd d * 128 + nv d * 2 + 8) = N := by rw [k1]; exact hN
  have hZ' : c.nmem (nd d * 128 + nv d * 2 + 8 + 3) = Z := by rw [k1]; exact hZ
  unfold prBS
  exec_block
  all_goals try omega
  all_goals try (config_simp; rw [hP]; first | exact hwd 2 | exact hwd 0)
  all_goals try (config_simp; rw [hP, e2]; omega)
  all_goals try (config_simp; rw [hP, e0]; omega)
  all_goals try (config_simp; rw [hP, e2, e0]; omega)
  all_goals try (config_simp; rw [hP, e2, e0, hN']; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, ?_⟩
  all_goals config_simp
  all_goals try (rw [hP, e2, e0, hN'])
  all_goals try (rw [hP, e2, e0, hZ'])
  all_goals try (rw [hP, e2, e0, hN']; unfold frB; ring)
  all_goals try (unfold frB; ring)

/-- **The print of the flow**: `Z`, then the `N` cells from `Hb + 9 + 6 N`. -/
theorem prB_exec {d : List ℕ} (hP : P.data = d) (hwd : ∀ i, word d i ≤ W) (c : Config)
    (hc : WordsBounded W c) {N Z : ℕ} (hN : c.nmem (frB d) = N) (hZ : c.nmem (frB d + 3) = Z)
    (hW : frB d + 8 * N + 200 ≤ W) :
    ∃ c' t, Exec P W prB c c' t ∧ t ≤ 7 * N + 30 ∧
      c'.output = c.output ++ Z :: (List.range N).map (fun i => c.nmem (frB d + 4 + 6 * N + i)) := by
  obtain ⟨c₁, t₁, e₁, ht₁, r41, r75, r76, r04, m1, o1⟩ := prBS_exec hP hwd c hc hN hZ hW
  obtain ⟨c₂, t₂, e₂, ht₂, o2, -, -, -, -⟩ := prL_exec (P := P) c₁ e₁.wb_right r41 r04 r75 r76
    (by omega)
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, ?_⟩
  rw [o2, o1, m1, List.append_assoc]
  simp only [List.singleton_append, one_mul]

/-- **The max-flow program** of `mfMain_cMachXGE`. -/
def mfProg (sepL stepP : Stmt) : Stmt :=
  .seq (.seq rfProg rxProg) (driver mtProg mlProg (splitSX (sepPX 100000 sepL)) (nodeSF stepP))

/-- **The max-flow program prints nothing** when the separator and the node step print nothing. -/
theorem noEmit_mfProg {sepL stepP : Stmt} (h1 : Stmt.noEmit sepL = true)
    (h2 : Stmt.noEmit stepP = true) : Stmt.noEmit (mfProg sepL stepP) = true := by
  have a1 : Stmt.noEmit rfProg = true := by decide +kernel
  have a2 : Stmt.noEmit rxProg = true := by decide +kernel
  have a3 : Stmt.noEmit mtProg = true := by decide +kernel
  have a4 : Stmt.noEmit mlProg = true := by decide +kernel
  have a5 : Stmt.noEmit spPre = true := by decide +kernel
  have a6 : Stmt.noEmit spSet = true := by decide +kernel
  have b1 : Stmt.noEmit spFlags = true := by decide +kernel
  have a7 : Stmt.noEmit spChL = true := by decide +kernel
  have b2 : Stmt.noEmit spGlR = true := by decide +kernel
  have b3 : Stmt.noEmit sfChild = true := by decide +kernel
  have b4 : Stmt.noEmit spRec = true := by decide +kernel
  have a8 : Stmt.noEmit (sepD0 100000) = true := by decide +kernel
  have a9 : Stmt.noEmit sepSm = true := by decide +kernel
  have a10 : Stmt.noEmit njProg = true := by decide +kernel
  have a11 : Stmt.noEmit peekB = true := by decide +kernel
  have a12 : Stmt.noEmit popB = true := by decide +kernel
  have a13 : Stmt.noEmit pushB = true := by decide +kernel
  have a14 : Stmt.noEmit coB = true := by decide +kernel
  have a15 : Stmt.noEmit coPost = true := by decide +kernel
  simp only [mfProg, Stmt.noEmit, driver, body, splitSX, spFront, sepPX, nodeSF, a1, a2, a3, a4,
    a5, a6, b1, a7, b2, b3, b4, a8, a9, a10, a11, a12, a13, a14, a15, h1, h2, Bool.and_self]

/-- **The capacities on slots are at most `Z = bigN`** (no loops). -/
lemma capS_le_bigN {d : List ℕ} (wf : Wf d) (hl : ∀ i < nd d, tl d (rv d i) ≠ tl d i) (s : ℕ) :
    capS (map wf) (fun i => cp d i) (srcF d) (snkF d) s ≤ bigN (map wf) (fun i => cp d i) := by
  unfold capS
  split_ifs with h1 h2 h3 h4
  · unfold xt
    split_ifs with h5
    · rw [bigN_map wf hl]
      have e : cp d (s / 3) = fl (tl d (rv d (s / 3)) ≠ tl d (s / 3)) * cp d (s / 3) := by
        unfold fl; rw [ppIteT (hl _ h5), one_mul]
      show cp d (s / 3) ≤ _
      rw [e]
      exact Finset.single_le_sum (f := fun x => fl (tl d (rv d x) ≠ tl d x) * cp d x)
        (fun _ _ => Nat.zero_le _) (mem_range.2 h5)
    · exact Nat.zero_le _
  all_goals first | exact Nat.zero_le _ | exact le_rfl

end Pp

end BKMNW

end PlanarFlow
