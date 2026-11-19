module

public import PlanarFlow.BKMNW.Nf7aMk

/-!
# The arrays of the prologue of `fixP`

Natural-word loops of the prologue (layout in `Nf7aP1.lean`):

* **`clProg`** (`clProg_exec`, `11 m + 4` steps): `CL[i] = CP[i] + Z − FLW[i]` (the lengths
  `c − f₀` of the MSSP call) and `r9420 = Σ_{i < m} CP[i]` (`absSum c`);
* **`kBlk`** (`kBlk_exec`, `16` steps): `r9373 = Mb = 4 AS + 1`, `r9422 = L = 8 · fpB AS m k`,
  `r9310 = K = 16 · fpB AS m k` with `fpB AS m k = (k + 2) · 2 (AS + m (4 AS + 1)) + 12 AS + 4`;
* **`fsaProg`** (`fsaProg_exec`, `40 k + 3` steps): for `l < k`, `t = PD[l]`, `r = RV[t]`:
  `CW[l] = CP[t]`, `CR[l] = CP[r]`, `FW[l] = F0[l] = FLW[t] + K − Z`,
  `DV[l] = DVS[LAB[t] − 1] + K − Z · DG[LAB[t] − 1]`;
* **`fsbProg`** (`fsbProg_exec`, `24 k + 3` steps): `ET[2l] = EH[2l+1] = MK[FL[t]] − 2`,
  `ET[2l+1] = EH[2l] = MK[FL[r]] − 2`;
* **`fscProg`** (`fscProg_exec`, `10 n + 3` steps): `PW[x] = 0`, `PR[x] = EL[x] = K` (`x < n`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### The lengths of the MSSP call and the sum of the capacities -/

/-- `CL[i] := CP[i] + Z − FLW[i]`, `AS += CP[i]`. -/
def clBody : Stmt :=
  block [.addN 9457 9434 9456, .loadN 9457 9457, .addN 9458 9435 9456, .loadN 9458 9458,
    .addN 9459 9457 9421, .subN 9459 9459 9458, .addN 9460 9409 9456, .storeN 9460 9459,
    .addN 9420 9420 9457, .addN 9456 9456 9436]

/-- **The lengths and the sum of the capacities.** -/
def clProg : Stmt := .seq (block [.constN 9456 0, .constN 9420 0]) (.whileLtN 9456 9400 clBody)

theorem clBody_exec (c : Config) (hc : WordsBounded W c) {CPb FLWb CLb Z AS i : ℕ}
    (r34 : c.nreg 9434 = CPb) (r35 : c.nreg 9435 = FLWb) (r09 : c.nreg 9409 = CLb)
    (r21 : c.nreg 9421 = Z) (r20 : c.nreg 9420 = AS) (r36 : c.nreg 9436 = 1)
    (r56 : c.nreg 9456 = i) (h1 : CPb + i ≤ W) (h2 : FLWb + i ≤ W)
    (h3 : c.nmem (CPb + i) + Z ≤ W) (h4 : CLb + i ≤ W) (h5 : AS + c.nmem (CPb + i) ≤ W)
    (h6 : i + 1 ≤ W) :
    ∃ c' k, Exec P W clBody c c' k ∧ k = 10 ∧ c'.nreg 9456 = i + 1 ∧
      c'.nreg 9420 = AS + c.nmem (CPb + i) ∧
      c'.nmem = upd c.nmem (CLb + i) (c.nmem (CPb + i) + Z - c.nmem (FLWb + i)) ∧
      (∀ r, r ≠ 9420 → (r < 9456 ∨ 9460 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold clBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r34, r35, r09, r21, r20, r36, r56]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r34, r35, r09, r21, r20, r36, r56])
  all_goals first | (simp only [upd_apply]; split_ifs <;> omega) | rfl

/-- **The lengths of the MSSP call and the sum of the capacities on the machine.** -/
theorem clProg_exec (c : Config) (hc : WordsBounded W c) {m CPb FLWb CLb Z : ℕ}
    (r00 : c.nreg 9400 = m) (r34 : c.nreg 9434 = CPb) (r35 : c.nreg 9435 = FLWb)
    (r09 : c.nreg 9409 = CLb) (r21 : c.nreg 9421 = Z) (r36 : c.nreg 9436 = 1)
    (hrd : CPb + m ≤ CLb ∧ FLWb + m ≤ CLb) (hS : ∑ i ∈ range m, c.nmem (CPb + i) + Z ≤ W)
    (hW : CLb + m + 1 ≤ W) :
    ∃ c' t, Exec P W clProg c c' t ∧ t ≤ 12 * m + 4 ∧
      (∀ i < m, c'.nmem (CLb + i) = c.nmem (CPb + i) + Z - c.nmem (FLWb + i)) ∧
      c'.nreg 9420 = ∑ i ∈ range m, c.nmem (CPb + i) ∧
      (∀ a, ¬ (CLb ≤ a ∧ a < CLb + m) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 9420 → (r < 9456 ∨ 9460 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a56, a20, ak, am, ar, arm, ao⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 9456 0, .constN 9420 0]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 9456 = 0 ∧
      c₁.nreg 9420 = 0 ∧ (∀ r, r ≠ 9456 → r ≠ 9420 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  have hsum : ∀ i ≤ m, ∑ j ∈ range i, c.nmem (CPb + j) ≤ ∑ j ∈ range m, c.nmem (CPb + j) :=
    fun i hi => sum_le_sum_of_subset (range_subset_range.2 hi)
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ i' < i, c'.nmem (CLb + i') = c.nmem (CPb + i') + Z - c.nmem (FLWb + i')) ∧
    c'.nreg 9420 = ∑ j ∈ range i, c.nmem (CPb + j) ∧
    (∀ a, ¬ (CLb ≤ a ∧ a < CLb + i) → c'.nmem a = c.nmem a) ∧
    (∀ r, r ≠ 9420 → (r < 9456 ∨ 9460 < r) → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h56, j1, j2, j3, j4, j5, j6, j7⟩ := tgRange (P := P)
    (a := 9456) (b := 9400) (body := clBody) J (lo := 0) (hi := m) (B := 10) c₁ e₁.wb_right a56
    (by rw [ak _ (by omega) (by omega), r00]) (Nat.zero_le _)
    ⟨fun i hi => absurd hi (by omega), by rw [a20]; simp, fun a _ => by rw [am],
      fun r h1 h2 => ak r (by omega) h1, ar, arm, ao⟩
    (fun i c' _ hi hw h56 h00 ⟨j1, j2, j3, j4, j5, j6, j7⟩ => by
      have eCP : c'.nmem (CPb + i) = c.nmem (CPb + i) := j3 _ (by omega)
      have eFL : c'.nmem (FLWb + i) = c.nmem (FLWb + i) := j3 _ (by omega)
      have hs1 := hsum (i + 1) (by omega)
      rw [sum_range_succ] at hs1
      obtain ⟨c'', t, ex, ht, b56, b20, bm, bk, br, brm, bo⟩ :=
        clBody_exec (P := P) c' hw (CPb := CPb) (FLWb := FLWb) (CLb := CLb) (Z := Z) (i := i)
          (by rw [j4 _ (by omega) (by omega), r34]) (by rw [j4 _ (by omega) (by omega), r35])
          (by rw [j4 _ (by omega) (by omega), r09]) (by rw [j4 _ (by omega) (by omega), r21])
          j2 (by rw [j4 _ (by omega) (by omega), r36]) h56 (by omega) (by omega)
          (by rw [eCP]; omega) (by omega) (by rw [eCP]; omega) (by omega)
      rw [eCP, eFL] at bm
      refine ⟨c'', t, ex, ht.le, b56, by rw [bk _ (by omega) (by omega)]; exact h00,
        fun i' hi' => ?_, by rw [b20, eCP, sum_range_succ], fun a ha => ?_,
        fun r h1 h2 => by rw [bk r h1 h2, j4 r h1 h2], by rw [br, j5], by rw [brm, j6],
        by rw [bo, j7]⟩
      · rw [bm, upd_apply]
        split_ifs with h
        · have : i' = i := by omega
          subst this; rfl
        · exact j1 i' (by omega)
      · rw [bm, upd_other _ _ _ (by omega)]; exact j3 a (by omega))
  refine ⟨c₂, _, e₁.seq e₂, by rw [hk₁]; simp only [Nat.sub_zero] at hk₂; omega, j1, j2, j3,
    j4, j5, j6, j7⟩

/-! ### The offsets -/

/-- **The bound of the signed words** of `fixP` (flows, prices, lengths, capacities): from the sum
`AS` of the capacities, the number `m` of darts and the length `k` of the path. -/
def fpB (AS m k : ℕ) : ℕ := (k + 2) * (2 * (AS + m * (4 * AS + 1))) + 12 * AS + 4

/-- `Mb = 4 AS + 1`, `L = fpB`, `K = 16 fpB`. -/
def kBlk : Stmt :=
  block [.constN 9490 4, .mulN 9491 9490 9420, .addN 9491 9491 9436, .copyN 9373 9491,
    .mulN 9492 9400 9491, .addN 9492 9492 9420, .addN 9492 9492 9492, .addN 9493 9401 9436,
    .addN 9493 9493 9436, .mulN 9494 9493 9492, .constN 9495 12, .mulN 9495 9495 9420,
    .addN 9494 9494 9495, .addN 9494 9494 9490, .constN 9497 8, .mulN 9422 9497 9494,
    .constN 9496 16, .mulN 9310 9496 9494]

theorem kBlk_exec (c : Config) (hc : WordsBounded W c) {AS m k : ℕ}
    (r20 : c.nreg 9420 = AS) (r00 : c.nreg 9400 = m) (r01 : c.nreg 9401 = k)
    (r36 : c.nreg 9436 = 1) (hW : 16 * fpB AS m k + k + 16 ≤ W) :
    ∃ c' t, Exec P W kBlk c c' t ∧ t = 18 ∧ c'.nreg 9373 = 4 * AS + 1 ∧
      c'.nreg 9422 = 8 * fpB AS m k ∧ c'.nreg 9310 = 16 * fpB AS m k ∧
      (∀ r, r ≠ 9373 → r ≠ 9422 → r ≠ 9310 → (r < 9490 ∨ 9497 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set X := m * (4 * AS + 1) with hX
  have e3 : (k + 1 + 1) * (X + AS + (X + AS)) + 12 * AS + 4 = fpB AS m k := by
    unfold fpB; rw [hX]; ring
  have e4 : X + AS + (X + AS) ≤ (k + 1 + 1) * (X + AS + (X + AS)) := by nlinarith
  have e5 : 4 * AS + 1 ≤ X + 4 * AS + 1 := by omega
  have e6 : 4 * AS + 1 ≤ X ∨ m = 0 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact Or.inr h
    · left; rw [hX]; nlinarith
  have e7 : 4 * AS + 1 ≤ fpB AS m k := by
    rcases e6 with h | h
    · omega
    · unfold fpB; omega
  unfold kBlk
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r00, r01, r36]); (try rw [← hX]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r20, r00, r01, r36])
  all_goals first | (simp only [upd_apply]; split_ifs <;> omega) | omega | (unfold fpB; ring)

end BKMNW

end PlanarFlow
