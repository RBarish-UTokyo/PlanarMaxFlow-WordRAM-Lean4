module

public import PlanarFlow.BKMNW.PrPP
public import PlanarFlow.BKMNW.PqTop

/-!
# The print of the flow when the input has loops

A loop `x` carries no flow; its slot `3 x` is invalid, so its position `POS[3 x]` lies in
`[N, 7 n)` (`ppBL_execB`). The print `prBBL a p = zP a p ; prBSB ; prL ; prZ` prints `Z`, the `N`
flow cells, and then `7 n - N` copies of `Z` (`prZ`), so that `q[POS[3 x]] - Z = 0` on a loop.

* `capS_le_bigNL`: the capacity of a valid slot is at most `Z = bigN` (loops allowed);
* `prBSBL_exec` (`prBSB_exec` with the registers `8700 = n`, `8753 = Z`), `prZ_exec`,
  **`prBBL_exec`**.
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

lemma capS_le_bigNL {d : List ℕ} (wf : Wf d) {s : ℕ} (hv : ValidS (map wf) s) :
    capS (map wf) (fun i => cp d i) (srcF d) (snkF d) s ≤ bigN (map wf) (fun i => cp d i) := by
  unfold capS
  split_ifs with h1 h2 h3 h4
  · unfold xt
    split_ifs with h5
    · rw [bigN_eq_sumL wf]
      have hn : NlP d (s / 3) := by
        rcases hv with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact ((isNl_map_iff wf).1 h).2
        · omega
        · omega
      have e : cp d (s / 3) = fl (tl d (rv d (s / 3)) ≠ tl d (s / 3)) * cp d (s / 3) := by
        unfold fl; rw [ppIteT (show tl d (rv d (s / 3)) ≠ tl d (s / 3) from hn), one_mul]
      show cp d (s / 3) ≤ _
      rw [e]
      exact Finset.single_le_sum (f := fun x => fl (tl d (rv d x) ≠ tl d x) * cp d x)
        (fun _ _ => Nat.zero_le _) (mem_range.2 h5)
    · exact Nat.zero_le _
  all_goals first | exact Nat.zero_le _ | exact le_rfl

theorem prBSBL_exec {d : List ℕ} (hP : P.data = d) (hwd : ∀ i, word d i ≤ W) (c : Config)
    (hc : WordsBounded W c) {B N Z : ℕ} (r30 : c.nreg 8730 = B)
    (hN : c.nmem (B + frB d) = N) (hZ : c.nmem (B + frB d + 3) = Z)
    (hW : B + frB d + 8 * N + 200 ≤ W) :
    ∃ c' t, Exec P W prBSB c c' t ∧ t = 24 ∧ c'.nreg 8741 = N ∧
      c'.nreg 8775 = B + frB d + 4 + 6 * N ∧ c'.nreg 8776 = 1 ∧ c'.nreg 8704 = 1 ∧
      c'.nreg 8700 = nd d ∧ c'.nreg 8753 = Z ∧
      c'.nmem = c.nmem ∧ c'.output = c.output ++ [Z] := by
  have e2 : d.getD 2 0 = nd d := rfl
  have e0 : d.getD 0 0 = nv d := rfl
  unfold frB at hN hZ hW
  have k1 : nd d * 128 + nv d * 2 + 8 + B = B + (128 * nd d + 2 * nv d + 8) := by ring
  have hN' : c.nmem (nd d * 128 + nv d * 2 + 8 + B) = N := by rw [k1]; exact hN
  have hZ' : c.nmem (nd d * 128 + nv d * 2 + 8 + B + 3) = Z := by rw [k1]; exact hZ
  unfold prBSB
  exec_block
  all_goals try omega
  all_goals try (config_simp; rw [hP]; first | exact hwd 2 | exact hwd 0)
  all_goals try (config_simp; rw [hP, e2]; omega)
  all_goals try (config_simp; rw [hP, e0]; omega)
  all_goals try (config_simp; rw [hP, e2, e0]; omega)
  all_goals try (config_simp; rw [hP, e2, e0, r30]; omega)
  all_goals try (config_simp; rw [hP, e2, e0, r30, hN']; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  all_goals config_simp
  all_goals try (rw [hP, e2, e0, r30, hN'])
  all_goals try (rw [hP, e2, e0, r30, hZ'])
  all_goals try (rw [hP, e2, e0, r30, hN']; unfold frB; ring)
  all_goals try (unfold frB; ring)
  all_goals try (rw [hP]; rfl)

/-- Print `Z` (`r8753`) for `i = N … 7 n - 1` (`N = r8741`, `n = r8700`). -/
def prZ : Stmt := .seq (block [.constN 8778 7, .mulN 8779 8700 8778, .copyN 8740 8741])
  (.whileLtN 8740 8779 (block [.outN 8753, .addN 8740 8740 8704]))

theorem prZ_exec (c : Config) (hc : WordsBounded W c) {n N Z : ℕ} (r00 : c.nreg 8700 = n)
    (r41 : c.nreg 8741 = N) (r53 : c.nreg 8753 = Z) (r04 : c.nreg 8704 = 1) (hN : N ≤ 7 * n)
    (hW : 7 * n + 8 ≤ W) :
    ∃ c' t, Exec P W prZ c c' t ∧ t ≤ 4 * (7 * n - N) + 6 ∧
      c'.output = c.output ++ List.replicate (7 * n - N) Z := by
  obtain ⟨c₁, t₁, e₁, ht₁, v79, v40, f1, m1, o1⟩ : ∃ c₁ t₁,
      Exec P W (block [.constN 8778 7, .mulN 8779 8700 8778, .copyN 8740 8741]) c c₁ t₁ ∧
      t₁ = 3 ∧ c₁.nreg 8779 = 7 * n ∧ c₁.nreg 8740 = N ∧
      (∀ x, x ≠ 8778 → x ≠ 8779 → x ≠ 8740 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (config_simp; rw [r00]; omega)
    refine ⟨rfl, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl⟩
    · config_simp; rw [r00]; ring
    · config_simp; rw [r41]
    · config_simp; simp (disch := omega) only [upd_other]
  let J : ℕ → Config → Prop := fun i e =>
    e.output = c.output ++ List.replicate (i - N) Z ∧ e.nreg 8753 = Z ∧ e.nreg 8704 = 1
  obtain ⟨c₂, t₂, e₂, ht₂, -, -, j1, -, -⟩ := lnRange (P := P) (a := 8740) (b := 8779)
    (body := block [.outN 8753, .addN 8740 8740 8704]) J (lo := N) (hi := 7 * n) (B := 2) c₁
    e₁.wb_right v40 v79 hN
    ⟨by rw [o1]; simp, by rw [f1 _ (by omega) (by omega) (by omega)]; exact r53,
      by rw [f1 _ (by omega) (by omega) (by omega)]; exact r04⟩
    (fun i e hlo hhi hw hci hbn ⟨j1, j2, j3⟩ => by
      exec_block
      all_goals try (config_simp; rw [hci, j3]; omega)
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
      · config_simp; rw [hci, j3]
      · config_simp; exact hbn
      · config_simp; rw [j1, j2, List.append_assoc, show i + 1 - N = (i - N) + 1 by omega,
          List.replicate_succ']
      · config_simp; exact j2
      · config_simp; exact j3)
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, j1⟩

/-- **The print of the flow at the base, loops allowed.** -/
def prBBL (a p : ℕ) : Stmt := .seq (zP a p) (.seq prBSB (.seq prL prZ))

theorem prBBL_exec {d : List ℕ} (hP : P.data = d) (hwd : ∀ i, word d i ≤ W) (a p : ℕ)
    (c : Config) (hc : WordsBounded W c) {N Z : ℕ} (hN : c.nmem (zB a p d + frB d) = N)
    (hZ : c.nmem (zB a p d + frB d + 3) = Z) (hN7 : N ≤ 7 * nd d) (hW1 : 7 * nd d + zb d + 20 ≤ W)
    (hW3 : (7 * nd d + zb d + 1) ^ p ≤ W)
    (hW : zB a p d + frB d + 8 * N + 200 ≤ W) :
    ∃ c' t, Exec P W (prBBL a p) c c' t ∧ t ≤ 9 * nd d + p + 7 * N + 4 * (7 * nd d - N) + 70 ∧
      c'.output = c.output ++ Z :: ((List.range N).map
        (fun i => c.nmem (zB a p d + frB d + 4 + 6 * N + i)) ++
        List.replicate (7 * nd d - N) Z) := by
  obtain ⟨c₀, t₀, e₀, ht₀, r30, m0, -, -, o0⟩ := zP_exec hP hwd a p c hc hW1
    (by unfold frB at hW; omega) (by omega) hW3
  rw [← m0] at hN hZ
  obtain ⟨c₁, t₁, e₁, ht₁, r41, r75, r76, r04, r00, r53, m1, o1⟩ := prBSBL_exec hP hwd c₀
    e₀.wb_right r30 hN hZ hW
  obtain ⟨c₂, t₂, e₂, ht₂, o2, -, f2, -, -⟩ := prL_exec (P := P) c₁ e₁.wb_right r41 r04 r75 r76
    (by omega)
  obtain ⟨c₃, t₃, e₃, ht₃, o3⟩ := prZ_exec (P := P) c₂ e₂.wb_right (n := nd d) (N := N) (Z := Z)
    (by rw [f2 _ (by omega) (by omega) (by omega)]; exact r00)
    (by rw [f2 _ (by omega) (by omega) (by omega)]; exact r41)
    (by rw [f2 _ (by omega) (by omega) (by omega)]; exact r53)
    (by rw [f2 _ (by omega) (by omega) (by omega)]; exact r04) hN7 (by unfold frB at hW; omega)
  refine ⟨c₃, t₀ + (t₁ + (t₂ + t₃)), .seq e₀ (.seq e₁ (.seq e₂ e₃)), by omega, ?_⟩
  rw [o3, o2, o1, m1, o0, m0, List.append_assoc, List.append_assoc]
  simp only [List.singleton_append, one_mul, List.cons_append, List.nil_append]

end Pp

end BKMNW

end PlanarFlow
