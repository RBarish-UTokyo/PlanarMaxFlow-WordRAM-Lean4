module

public import PlanarFlow.BKMNW.FrFixed

/-!
# The natural image of an FR-Dijkstra input and the reference run of `frNF`

An input `P : Prm` of FR-Dijkstra (with `Lay P`, the inputs bounded by `L`) is held, on natural
words, by the **image**: the natural cells `frNM P a` (offsets and heads of the explicit arcs) at
`a < P.sb`, and the residues `frRS P L a` modulo `M = frM P L` of the integer cells `frRZ P a`
(dense distance graph, prices, lengths of the explicit arcs) at `β + a`, `β = P.W + 1`; every other
cell `≤ frWN P L` zero.

* `frRegs`, `frNM`, `frRZ`, `frRS`; the real start **`frCfg P`** (`frCfg_inp`, `frCfg_data`,
  `frCfg_wb`, `frCfg_memB`) and its natural image **`frCfgN P L`** (`natOf` with the constants
  `M`, `H`, `β` in `r760 … r762`; `frCfgN_sim`, `frCfgN_wb`, `frCfgN_nreg`, `frCfgN_nmem`);
* **`FResN P L K v dd nm Fb Rb`**: the result of FR-Dijkstra on natural words (a run of Dijkstra's
  algorithm `MRun`, closed under the arcs; the flag `1` at `Fb + y` iff `y` is reached; the
  distance `dd i` decoded from the residue at `Rb + v i`);
* **`frNF_ref`**: the fixed natural program `frNF` runs from `frCfgN P L` within
  `4 frCost P + 3` steps (word bound `frWN P L`) to a configuration with `FResN … sb (β + db)`,
  output empty.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace FrFix

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Machine.ModNat WordRAM.Programs
  Monge Monge.FR Monge.CmpAbs

/-! ### The image -/

/-- The input registers of FR-Dijkstra (`Inp`), zero elsewhere. -/
def frRegs (P : Prm) (r : ℕ) : ℕ :=
  if r = 100 then P.N else if r = 101 then P.b else if r = 102 then P.Db else if r = 103 then P.pb
  else if r = 104 then P.ob else if r = 105 then P.lb else if r = 106 then P.r
  else if r = 107 then P.sb else if r = 108 then P.db else if r = 109 then P.wb else 0

/-- The natural cells of the input: the offsets and the heads of the explicit arcs. -/
def frNM (P : Prm) (a : ℕ) : ℕ :=
  if P.ob ≤ a ∧ a ≤ P.ob + P.N then P.off (a - P.ob)
  else if P.ob + P.N + 1 ≤ a ∧ a < P.ob + P.N + 1 + P.m then P.dst (a - (P.ob + P.N + 1)) else 0

/-- The integer cells of the input: the dense distance graph, the prices, the lengths. -/
def frRZ (P : Prm) (a : ℕ) : ℤ :=
  if P.Db ≤ a ∧ a < P.Db + P.b * P.b then P.D ((a - P.Db) / P.b) ((a - P.Db) % P.b)
  else if P.pb ≤ a ∧ a < P.pb + P.N then P.p (a - P.pb)
  else if P.lb ≤ a ∧ a < P.lb + P.m then P.len (a - P.lb) else 0

/-- The residues of the integer cells modulo `frM P L`. -/
def frRS (P : Prm) (L a : ℕ) : ℕ := (frRZ P a % (frM P L : ℤ)).toNat

/-- **The real start of FR-Dijkstra** on the input `P`. -/
noncomputable def frCfg (P : Prm) : Config where
  pc := 0
  nreg := frRegs P
  rreg := fun _ => 0
  nmem := fun a => if a < P.sb then frNM P a else 0
  rmem := fun a => if a < P.sb then ((frRZ P a : ℤ) : ℝ) else 0
  output := []

variable {P : Prm} {L : ℕ}

theorem frCfg_inp : Inp P (frCfg P) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [frCfg, frRegs]

lemma mul_lt_sq {i j b : ℕ} (hi : i < b) (hj : j < b) : i * b + j < b * b := by
  have h := Nat.mul_le_mul_right b (show i + 1 ≤ b by omega)
  rw [Nat.succ_mul] at h
  omega

lemma div_mod_ij {i j b : ℕ} (hj : j < b) : (i * b + j) / b = i ∧ (i * b + j) % b = j := by
  have hb : 0 < b := by omega
  refine ⟨div_eq_of_mul hj, ?_⟩
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

theorem frCfg_data (hL : Lay P) : Data P (frCfg P) := by
  have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4
  refine ⟨fun i j hi hj => ?_, fun x hx => ?_, fun x hx => ?_, fun e he => ?_, fun e he => ?_⟩
  · have h1 := mul_lt_sq hi hj
    obtain ⟨d1, d2⟩ := div_mod_ij (i := i) hj
    have e1 : P.Db + i * P.b + j - P.Db = i * P.b + j := by omega
    simp only [frCfg, frRZ, show P.Db + i * P.b + j < P.sb by omega, ↓reduceIte, e1, d1, d2,
      show P.Db ≤ P.Db + i * P.b + j ∧ P.Db + i * P.b + j < P.Db + P.b * P.b from
        ⟨by omega, by omega⟩, and_self]
  · simp only [frCfg, frRZ, show P.pb + x < P.sb by omega, ↓reduceIte,
      show ¬ (P.Db ≤ P.pb + x ∧ P.pb + x < P.Db + P.b * P.b) by omega,
      show P.pb ≤ P.pb + x ∧ P.pb + x < P.pb + P.N from ⟨by omega, by omega⟩, and_self,
      Nat.add_sub_cancel_left]
  · simp only [frCfg, frNM, show P.ob + x < P.sb by omega, ↓reduceIte,
      show P.ob ≤ P.ob + x ∧ P.ob + x ≤ P.ob + P.N from ⟨by omega, by omega⟩, and_self,
      Nat.add_sub_cancel_left]
  · simp only [frCfg, frNM, show P.ob + P.N + 1 + e < P.sb by omega, ↓reduceIte,
      show ¬ (P.ob ≤ P.ob + P.N + 1 + e ∧ P.ob + P.N + 1 + e ≤ P.ob + P.N) by omega,
      show P.ob + P.N + 1 ≤ P.ob + P.N + 1 + e ∧ P.ob + P.N + 1 + e < P.ob + P.N + 1 + P.m from
        ⟨by omega, by omega⟩, and_self, Nat.add_sub_cancel_left]
  · simp only [frCfg, frRZ, show P.lb + e < P.sb by omega, ↓reduceIte,
      show ¬ (P.Db ≤ P.lb + e ∧ P.lb + e < P.Db + P.b * P.b) by omega,
      show ¬ (P.pb ≤ P.lb + e ∧ P.lb + e < P.pb + P.N) by omega,
      show P.lb ≤ P.lb + e ∧ P.lb + e < P.lb + P.m from ⟨by omega, by omega⟩, and_self,
      Nat.add_sub_cancel_left]

/-- The offsets are at most the number of arcs. -/
lemma off_le (hL : Lay P) {x : ℕ} (hx : x ≤ P.N) : P.off x ≤ P.m := by
  have key : ∀ k, x + k ≤ P.N → P.off x ≤ P.off (x + k) := by
    intro k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih =>
      intro hk
      exact (ih (by omega)).trans (hL.off_mono (x + k) (by omega))
  have := key (P.N - x) (by omega)
  rw [show x + (P.N - x) = P.N by omega, hL.off_last] at this
  exact this

lemma frNM_le (hL : Lay P) (a : ℕ) : frNM P a ≤ P.W := by
  have hw := lay_w hL
  have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  unfold frNM
  split_ifs with h1 h2
  · have := off_le hL (x := a - P.ob) (by omega); omega
  · have := hL.dst_lt (a - (P.ob + P.N + 1)) (by omega); omega
  · omega

lemma frRegs_le (hL : Lay P) (r : ℕ) : frRegs P r ≤ P.W := by
  have hw := lay_w hL
  have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  have := hL.r_lt
  unfold frRegs
  split_ifs <;> omega

theorem frCfg_wb (hL : Lay P) : WordsBounded P.W (frCfg P) := by
  refine ⟨fun r => frRegs_le hL r, fun a => ?_⟩
  simp only [frCfg]
  split_ifs
  · exact frNM_le hL a
  · exact Nat.zero_le _

lemma frRZ_abs (hL : Lay P) (hX : XB P L) (a : ℕ) : |frRZ P a| ≤ (L : ℤ) := by
  have hb := hL.b_pos
  unfold frRZ
  split_ifs with h1 h2 h3
  · have hi : (a - P.Db) / P.b < P.b := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    exact hX.D _ _ hi (Nat.mod_lt _ (by omega))
  · exact hX.p _ (by omega)
  · exact hX.len _ (by omega)
  · simp

theorem frCfg_memB (hL : Lay P) (hX : XB P L) : MemB P.W (BB P L) (frCfg P) := by
  intro a ha
  simp only [frCfg]
  have hB : (L : ℝ) ≤ (BB P L : ℝ) := by
    unfold BB; push_cast
    have : (0 : ℝ) ≤ P.N := by positivity
    nlinarith [show (0 : ℝ) ≤ L by positivity]
  split_ifs
  · have h := frRZ_abs hL hX a
    have h' : |((frRZ P a : ℤ) : ℝ)| ≤ (L : ℝ) := by exact_mod_cast h
    exact h'.trans hB
  · simp only [abs_zero]; positivity

/-- **The natural image of the start**: `natOf` of `frCfg P`, the constants `M`, `H`, `β` of the
simulation in `r760 … r762` (as `frNF` reads them). -/
noncomputable def frCfgN (P : Prm) (L : ℕ) : Config :=
  { natOf 372 P.W (frM P L) (P.W + 1) (frCfg P) with
    nreg := upd (upd (upd (natOf 372 P.W (frM P L) (P.W + 1) (frCfg P)).nreg 760 (frM P L))
      761 (frH P L)) 762 (P.W + 1) }

lemma frM_pos : 0 < frM P L := by unfold frM; omega

theorem frCfgN_sim : Sim 372 P.W (frM P L) (P.W + 1) (frCfg P) (frCfgN P L) := by
  have hS := sim_natOf (R := 372) (W := P.W) (M := frM P L) (β := P.W + 1) (c := frCfg P)
    (by omega) frM_pos (fun r _ => ⟨0, by simp [frCfg]⟩)
    (fun a _ => by
      simp only [frCfg]
      split_ifs
      · exact ⟨_, rfl⟩
      · exact ⟨0, by simp⟩)
  refine ⟨fun r hr => ?_, fun r hr => ?_, hS.nmem, hS.rmem, hS.output⟩
  · simp only [frCfgN]
    rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
    exact hS.nreg r hr
  · simp only [frCfgN]
    rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
    exact hS.rreg r hr

theorem frCfgN_wb (hL : Lay P) : WordsBounded (frWN P L) (frCfgN P L) := by
  have hw := natOf_wb (R := 372) (M := frM P L) (β := P.W + 1) (frCfg_wb hL)
    (W' := frWN P L) (by unfold frWN; omega) (by unfold frWN; omega) frM_pos
  refine ⟨fun r => ?_, hw.2⟩
  simp only [frCfgN, upd_apply]
  split_ifs
  · unfold frWN; omega
  · unfold frWN frM; omega
  · unfold frWN; omega
  · exact hw.1 r

/-- The registers of the image. -/
theorem frCfgN_nreg (r : ℕ) (hr : r < 763) :
    (frCfgN P L).nreg r = if r < 372 then frRegs P r else if r = 760 then frM P L
      else if r = 761 then frH P L else if r = 762 then P.W + 1 else 0 := by
  simp only [frCfgN, natOf, frCfg, upd_apply]
  by_cases h1 : r < 372
  · simp only [h1, ↓reduceIte, show r ≠ 760 by omega, show r ≠ 761 by omega,
      show r ≠ 762 by omega]
  · by_cases h2 : r < 2 * 372
    · simp only [h1, h2, ↓reduceIte, show r ≠ 760 by omega, show r ≠ 761 by omega,
        show r ≠ 762 by omega]
      unfold resOf
      split
      · rename_i h
        have h0 := Classical.choose_spec h
        have : Classical.choose h = 0 := by exact_mod_cast h0.symm
        rw [this]; rfl
      · rfl
    · simp only [h1, h2, ↓reduceIte]
      split_ifs <;> first | rfl | omega

lemma resOf_int {M : ℕ} (z : ℤ) : resOf M (z : ℝ) = (z % (M : ℤ)).toNat := by
  unfold resOf
  rw [dite_eq_left_of_eq_true (eq_true ⟨z, rfl⟩)]
  have h := Classical.choose_spec (⟨z, rfl⟩ : ∃ z' : ℤ, (z : ℝ) = z')
  have : Classical.choose (⟨z, rfl⟩ : ∃ z' : ℤ, (z : ℝ) = z') = z := by exact_mod_cast h.symm
  rw [this]

/-- **The memory of the image**: `frNM` below `sb`, the residues `frRS` at `β + a`, `a < sb`,
zero elsewhere. -/
theorem frCfgN_nmem (hL : Lay P) (a : ℕ) :
    (frCfgN P L).nmem a = if a < P.sb then frNM P a
      else if P.W + 1 ≤ a ∧ a < P.W + 1 + P.sb then frRS P L (a - (P.W + 1)) else 0 := by
  have hw := lay_w hL
  have := hL.m5; have := hL.m6
  simp only [frCfgN, natOf, frCfg]
  by_cases h1 : a < P.sb
  · simp only [show a ≤ P.W by omega, h1, ↓reduceIte]
  · by_cases h2 : a ≤ P.W
    · simp only [h1, h2, ↓reduceIte, show ¬ (P.W + 1 ≤ a ∧ a < P.W + 1 + P.sb) by omega]
    · by_cases h3 : P.W + 1 ≤ a ∧ a ≤ P.W + 1 + P.W
      · simp only [h1, h2, h3, and_self, ↓reduceIte]
        by_cases h4 : a - (P.W + 1) < P.sb
        · simp only [h4, ↓reduceIte, show P.W + 1 ≤ a ∧ a < P.W + 1 + P.sb from
            ⟨by omega, by omega⟩, and_self, frRS]
          exact resOf_int _
        · have e0 := resOf_int (M := frM P L) 0
          simp only [Int.cast_zero, Int.zero_emod, Int.toNat_zero] at e0
          simp only [h4, ↓reduceIte, e0]
          split_ifs <;> first | rfl | omega
      · simp only [h1, h2, h3, ↓reduceIte, show ¬ (P.W + 1 ≤ a ∧ a < P.W + 1 + P.sb) by omega]

/-! ### The result on natural words -/

/-- **The result of FR-Dijkstra on natural words**: a run of Dijkstra's algorithm with the price
function (`MRun`), closed under the arcs, the flag `1` at `Fb + y` iff `y` is reached, the
distance `dd i` decoded from the residue at `Rb + v i` (`≤ H` nonnegative, else minus `M`). -/
def FResN (P : Prm) (L K : ℕ) (v : ℕ → ℕ) (dd : ℕ → ℤ) (nm : ℕ → ℕ) (Fb Rb : ℕ) : Prop :=
  MRun P K v dd ∧ 0 < K ∧ (∀ i < K, v i < P.N) ∧
    (∀ i < K, ∀ y ℓ, IsArc P (v i) y ℓ → ∃ j < K, y = v j) ∧
    (∀ y < P.N, nm (Fb + y) = 1 ↔ ∃ i < K, v i = y) ∧
    (∀ i < K, dd i = if nm (Rb + v i) ≤ frH P L then (nm (Rb + v i) : ℤ)
      else (nm (Rb + v i) : ℤ) - frM P L)

/-- `FResN` depends only on the flag and residue cells. -/
theorem FResN.congr {K : ℕ} {v : ℕ → ℕ} {dd : ℕ → ℤ} {nm nm' : ℕ → ℕ} {Fb Rb Fb' Rb' : ℕ}
    (h : FResN P L K v dd nm Fb Rb) (hf : ∀ y < P.N, nm' (Fb' + y) = nm (Fb + y))
    (hr : ∀ y < P.N, nm' (Rb' + y) = nm (Rb + y)) : FResN P L K v dd nm' Fb' Rb' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, h4, fun y hy => by rw [hf y hy]; exact h5 y hy, fun i hi => ?_⟩
  rw [hr _ (h3 i hi)]; exact h6 i hi

/-- **The reference run of the fixed natural FR-Dijkstra** on the image of the input. -/
theorem frNF_ref (hL : Lay P) (hXB : XB P L) (hDc : Crossing P.b P.D) (hF : Feas P) (I : Input) :
    ∃ dN' k', Exec I (frWN P L) frNF (frCfgN P L) dN' k' ∧ k' ≤ 4 * frCost P + 3 ∧
      dN'.output = [] ∧ ∃ K v dd, FResN P L K v dd dN'.nmem P.sb (P.W + 1 + P.db) := by
  obtain ⟨c', k, e, hk, hDa', ho, -, -, ⟨K, v, dd, hres⟩, d', k', e', hk', hS', -, -⟩ :=
    frProg_exec_nat (I := I) hL hXB hDc hF (frCfg P) (frCfg_wb hL) frCfg_inp (frCfg_data hL)
      (frCfg_memB hL hXB) frCfgN_sim (frCfgN_wb hL)
  have r60 : (frCfgN P L).nreg 760 = frM P L := by simp [frCfgN]
  have r61 : (frCfgN P L).nreg 761 = frH P L := by simp [frCfgN]
  have r62 : (frCfgN P L).nreg 762 = P.W + 1 := by simp [frCfgN]
  refine ⟨d', k', frNF_exec e' r60 r61 r62, hk', by rw [hS'.output, ho]; rfl, K, v, dd, ?_⟩
  have hw := lay_w hL
  have := hL.m5; have := hL.m6
  obtain ⟨hR, hK, hv, hcl, hfl, hdd⟩ := hres
  refine ⟨hR, hK, hv, hcl, fun y hy => ?_, fun i hi => ?_⟩
  · rw [hS'.nmem _ (by omega)]; exact hfl y hy
  · have h := frRes_dist_nat hL hXB ⟨hR, hK, hv, hcl, hfl, hdd⟩ hS' hi
    rw [show P.W + 1 + (P.db + v i) = P.W + 1 + P.db + v i by omega] at h
    split_ifs at h ⊢ <;> exact_mod_cast h

end FrFix

end BKMNW

end PlanarFlow
