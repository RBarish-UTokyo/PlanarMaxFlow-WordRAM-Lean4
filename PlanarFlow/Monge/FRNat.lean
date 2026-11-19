module

public import PlanarFlow.Monge.FRCmpLoop
public import PlanarFlow.Monge.FRReloc

/-!
# FR-Dijkstra on natural words

`frProg_exec_nat`: the run of `PlanarFlow.Monge.FR.frProg_exec` is simulated by the program on
natural words `constsS; toNat 372 M frProg` (`WordRAM/Machine/RealsModNat.lean`), which keeps every
real value modulo `M = frM P L = 12 (N + 2) L + 1` in natural words, with the word bound
`frWN P L = 2 W + 1 + M² + M` (`W = P.W`) and at most `4 frCost P + 3` steps. Hypotheses beyond
those of `frProg_exec`: the inputs bounded by `L` (`XB`), every real memory cell at an address
`≤ W` bounded by `BB P L = (N + 2) L` (`MemB`), and a natural configuration `d` holding the
residues of the (integer) reals of the start (`ModNat.Sim`; the reals at addresses `≤ W` and in
the registers `< 372` are integers). At the end `d'` holds the residues of the reals of the final
configuration; the distances, of absolute value at most `N L < M / 2`, are read back from their
residues by `ModNat.Res.signed`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Machine.ModNat CmpAbs

variable {P : Prm} {I : Input} {L : ℕ}

/-- The bound of the compared differences. -/
def frH (P : Prm) (L : ℕ) : ℕ := 6 * BB P L

/-- The modulus. -/
def frM (P : Prm) (L : ℕ) : ℕ := 2 * frH P L + 1

/-- The word bound of the program on natural words. -/
def frWN (P : Prm) (L : ℕ) : ℕ := 2 * P.W + 1 + frM P L * frM P L + frM P L

/-- **FR-Dijkstra on natural words.** From the inputs of `frProg_exec` bounded by `L`, the real
memory bounded by `BB P L`, and a natural configuration `d` holding the residues modulo
`frM P L` of the reals (`Sim`, registers `< 372`, real memory at `β + a` for `β = P.W + 1`),
bounded by `frWN P L`: the run of `frProg` (the result `FRes` of `frProg_exec`) is simulated by
the natural program `constsS 372 M H β; toNat 372 M frProg` within `4 frCost P + 3` steps and the
word bound `frWN P L`, ending in a configuration holding the residues of the final reals, with
the natural registers `≥ 748` and the natural memory outside `[0, W] ∪ [β, β + W]` kept. -/
theorem frProg_exec_nat (hL : Lay P) (hXB : XB P L) (hDc : Crossing P.b P.D) (hF : Feas P)
    (c : Config) (hc : WordsBounded P.W c) (hin : Inp P c) (hDa : Data P c)
    (hMB : MemB P.W (BB P L) c) {d : Config} (hS : Sim 372 P.W (frM P L) (P.W + 1) c d)
    (hd : WordsBounded (frWN P L) d) :
    ∃ c' k, Exec I P.W frProg c c' k ∧ k ≤ frCost P ∧ Data P c' ∧ c'.output = c.output ∧
      (∀ r < 100, c'.nreg r = c.nreg r) ∧ (∀ r < 100, c'.rreg r = c.rreg r) ∧
      (∃ K v dd, FRes P K v dd c'.nmem c'.rmem) ∧
      ∃ d' k', Exec I (frWN P L) (.seq (constsS 372 (frM P L) (frH P L) (P.W + 1))
          (ModNat.toNat 372 (frM P L) frProg)) d d' k' ∧ k' ≤ 4 * frCost P + 3 ∧
        Sim 372 P.W (frM P L) (P.W + 1) c' d' ∧ (∀ r, 2 * 372 + 4 ≤ r → d'.nreg r = d.nreg r) ∧
        (∀ a, P.W < a → (a < P.W + 1 ∨ P.W + 1 + P.W < a) → d'.nmem a = d.nmem a) := by
  obtain ⟨c', k, e, hk, hDa', ho, hr1, hr2, hres⟩ := frProg_exec (I := I) hL hDc hF c hc hin hDa
  have hcmp := (frProg_good (I := I) hL hXB hDc hF c hc hin hDa).toCmp hMB
  obtain ⟨d', k', e', hk', hS', -, hK, hN, -, -⟩ := (hcmp.exec e).toNat_consts frProg_regsOK
    (by decide) (show 2 * frH P L < frM P L by unfold frM; omega) (by omega)
    (by unfold frWN; omega) (by unfold frWN; omega) (by unfold frWN; omega) hS hd
  exact ⟨c', k, e, hk, hDa', ho, hr1, hr2, hres, d', k', e', by omega, hS', hK, hN⟩

/-- **Reading a bounded integer back from its residue**: if `|x| ≤ H` and `2 H < M`, then `x` is
the residue `v` when `v ≤ H`, and `v - M` otherwise. -/
theorem _root_.WordRAM.Machine.ModNat.Res.signed {M H : ℕ} {x : ℝ} {v : ℕ} (h : Res M x v)
    (hx : |x| ≤ H) (hM : 2 * H < M) : x = if v ≤ H then (v : ℝ) else (v : ℝ) - M := by
  obtain ⟨z, rfl, hv⟩ := h
  have hz : |z| ≤ (H : ℤ) := by exact_mod_cast hx
  rw [abs_le] at hz
  have hM0 : (0 : ℤ) < M := by omega
  rcases le_or_gt 0 z with h0 | h0
  · have e : z % (M : ℤ) = z := Int.emod_eq_of_lt h0 (by omega)
    have hvz : (v : ℤ) = z := hv.trans e
    have hvH : v ≤ H := by omega
    rw [iteT hvH]; exact_mod_cast hvz.symm
  · have e : z % (M : ℤ) = z + M := by
      rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
    have hvz : (v : ℤ) = z + M := hv.trans e
    have hvH : ¬ v ≤ H := by omega
    rw [iteF hvH]
    have : (z : ℝ) = ((v : ℤ) : ℝ) - M := by rw [hvz]; push_cast; ring
    rw [this]; push_cast; ring

/-- **The distances on natural words**: in the final natural configuration of
`frProg_exec_nat`, the residue at `β + (db + v i)` gives back the distance `dd i` of the run. -/
theorem frRes_dist_nat (hL : Lay P) (hX : XB P L) {K : ℕ} {v : ℕ → ℕ} {dd : ℕ → ℤ} {c' d' : Config}
    (hres : FRes P K v dd c'.nmem c'.rmem) (hS' : Sim 372 P.W (frM P L) (P.W + 1) c' d')
    {i : ℕ} (hi : i < K) :
    ((dd i : ℤ) : ℝ) = if d'.nmem (P.W + 1 + (P.db + v i)) ≤ frH P L then
      (d'.nmem (P.W + 1 + (P.db + v i)) : ℝ) else (d'.nmem (P.W + 1 + (P.db + v i)) : ℝ) - frM P L := by
  obtain ⟨hR, -, hv, -, -, hd⟩ := hres
  have hvi := hv i hi
  have hw := lay_w hL
  have := hL.m6
  have hres := hS'.rmem (P.db + v i) (by omega)
  rw [hd i hi] at hres
  refine hres.signed ?_ (by unfold frM; omega)
  have h1 := hR.dist_le_real hL hX hv i hi
  refine h1.trans ?_
  unfold frH BB; push_cast; nlinarith

/-! ### A natural configuration simulating an integer one -/

/-- The residue modulo `M` of an integer real (`0` for a real that is not an integer). -/
noncomputable def _root_.WordRAM.Machine.ModNat.resOf (M : ℕ) (x : ℝ) : ℕ := by
  classical
  exact if h : ∃ z : ℤ, x = z then (Classical.choose h % (M : ℤ)).toNat else 0

/-- The natural configuration holding the residues modulo `M` of the reals of `c` (registers
`< R` at `R + r`, memory `≤ W` at `β + a`), the natural registers `< R` and the natural memory
`≤ W` of `c`, and zero elsewhere. -/
noncomputable def _root_.WordRAM.Machine.ModNat.natOf (R W M β : ℕ) (c : Config) : Config where
  pc := c.pc
  nreg := fun r => if r < R then c.nreg r
    else if r < 2 * R then resOf M (c.rreg (r - R)) else 0
  rreg := fun _ => 0
  nmem := fun a => if a ≤ W then c.nmem a
    else if β ≤ a ∧ a ≤ β + W then resOf M (c.rmem (a - β)) else 0
  rmem := fun _ => 0
  output := c.output

theorem _root_.WordRAM.Machine.ModNat.res_resOf {M : ℕ} (hM : 0 < M) {x : ℝ}
    (hx : ∃ z : ℤ, x = z) : Res M x (resOf M x) := by
  unfold resOf
  rw [dite_eq_left_of_eq_true (eq_true hx)]
  exact ⟨_, Classical.choose_spec hx,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hM.ne'))⟩

/-- **The simulation of an integer configuration**: if the real registers `< R` and the real
memory `≤ W` of `c` are integers, `natOf` simulates `c`. -/
theorem _root_.WordRAM.Machine.ModNat.sim_natOf {R W M β : ℕ} (hβ : W < β) (hM : 0 < M)
    {c : Config} (hr : ∀ r < R, ∃ z : ℤ, c.rreg r = z) (hm : ∀ a ≤ W, ∃ z : ℤ, c.rmem a = z) :
    Sim R W M β c (natOf R W M β c) := by
  refine ⟨fun r hr' => ?_, fun r hr' => ?_, fun a ha => ?_, fun a ha => ?_, rfl⟩
  · simp [natOf, hr']
  · have h1 : ¬ R + r < R := by omega
    have h2 : R + r < 2 * R := by omega
    simp only [natOf, h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
    exact res_resOf hM (hr r hr')
  · simp [natOf, ha]
  · have h1 : ¬ β + a ≤ W := by omega
    have h2 : β ≤ β + a ∧ β + a ≤ β + W := ⟨by omega, by omega⟩
    simp only [natOf, h1, h2, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
    exact res_resOf hM (hm a ha)

theorem _root_.WordRAM.Machine.ModNat.natOf_wb {R W M β W' : ℕ} {c : Config}
    (hc : WordsBounded W c) (hW : W ≤ W') (hM : M ≤ W' + 1) (hM0 : 0 < M) :
    WordsBounded W' (natOf R W M β c) := by
  have hlt : ∀ x : ℝ, resOf M x ≤ W' := fun x => by
    unfold resOf
    split
    · rename_i h
      have h1 := Int.emod_lt_of_pos (Classical.choose h) (show (0 : ℤ) < M by exact_mod_cast hM0)
      have h2 := Int.emod_nonneg (Classical.choose h) (show (M : ℤ) ≠ 0 by exact_mod_cast hM0.ne')
      omega
    · exact Nat.zero_le _
  refine ⟨fun r => ?_, fun a => ?_⟩
  · simp only [natOf]; split_ifs
    · exact (hc.1 r).trans hW
    · exact hlt _
    · exact Nat.zero_le _
  · simp only [natOf]; split_ifs
    · exact (hc.2 a).trans hW
    · exact hlt _
    · exact Nat.zero_le _

/-- **FR-Dijkstra on natural words from an integer start**: if the real registers `< 372` and
the real memory `≤ P.W` of the start of `frProg_exec` are integers bounded by `BB P L` (the
memory), the natural program runs from `natOf 372 P.W (frM P L) (P.W + 1) c` as in
`frProg_exec_nat`. -/
theorem frProg_exec_nat_of_int (hL : Lay P) (hXB : XB P L) (hDc : Crossing P.b P.D)
    (hF : Feas P) (c : Config) (hc : WordsBounded P.W c) (hin : Inp P c) (hDa : Data P c)
    (hMB : MemB P.W (BB P L) c) (hri : ∀ r < 372, ∃ z : ℤ, c.rreg r = z)
    (hmi : ∀ a ≤ P.W, ∃ z : ℤ, c.rmem a = z) :
    ∃ c' k, Exec I P.W frProg c c' k ∧ k ≤ frCost P ∧ Data P c' ∧ c'.output = c.output ∧
      (∀ r < 100, c'.nreg r = c.nreg r) ∧ (∀ r < 100, c'.rreg r = c.rreg r) ∧
      (∃ K v dd, FRes P K v dd c'.nmem c'.rmem) ∧
      ∃ d' k', Exec I (frWN P L) (.seq (constsS 372 (frM P L) (frH P L) (P.W + 1))
          (ModNat.toNat 372 (frM P L) frProg)) (natOf 372 P.W (frM P L) (P.W + 1) c) d' k' ∧
        k' ≤ 4 * frCost P + 3 ∧ Sim 372 P.W (frM P L) (P.W + 1) c' d' := by
  have hM0 : 0 < frM P L := by unfold frM; omega
  obtain ⟨c', k, e, hk, a1, a2, a3, a4, a5, d', k', e', hk', hS', -⟩ :=
    frProg_exec_nat (I := I) hL hXB hDc hF c hc hin hDa hMB (sim_natOf (by omega) hM0 hri hmi)
      (natOf_wb hc (by unfold frWN; omega) (by unfold frWN; omega) hM0)
  exact ⟨c', k, e, hk, a1, a2, a3, a4, a5, d', k', e', hk', hS'⟩

/-! ### Inside a larger configuration -/

theorem _root_.WordRAM.Machine.ModNat.trI_ok {R M : ℕ} {i : Instr}
    (hr : i.regsOK (fun r => decide (r < R)) = true) (hn : i.notInp = true)
    (hd : i.noRand = true) :
    (trI R M i).regsOK (fun r => decide (r < 2 * R + 4)) = true ∧ (trI R M i).noInp = true ∧
      (trI R M i).noRand = true := by
  cases i <;> simp_all [trI, Instr.regsOK, Instr.regs, Stmt.regsOK, Stmt.noInp, Stmt.noRand,
    Instr.notInp, Instr.noRand, block] <;> omega

theorem _root_.WordRAM.Machine.ModNat.cmpS_ok {R a b : ℕ} (ha : a < R) (hb : b < R) :
    (cmpS R a b).regsOK (fun r => decide (r < 2 * R + 4)) = true ∧ (cmpS R a b).noInp = true ∧
      (cmpS R a b).noRand = true := by
  simp [cmpS, Instr.regsOK, Instr.regs, Stmt.regsOK, Stmt.noInp, Stmt.noRand,
    Instr.notInp, Instr.noRand, block]; omega

/-- The statement on natural words names only registers `< 2R + 4`, reads no input and draws
no random word, when `s` names only registers `< R` and does neither. -/
theorem _root_.WordRAM.Machine.ModNat.toNat_ok {R M : ℕ} {s : Stmt}
    (hr : s.regsOK (fun r => decide (r < R)) = true) (hn : s.noInp = true)
    (hd : s.noRand = true) :
    (ModNat.toNat R M s).regsOK (fun r => decide (r < 2 * R + 4)) = true ∧
      (ModNat.toNat R M s).noInp = true ∧ (ModNat.toNat R M s).noRand = true := by
  induction s with
  | skip => simp [ModNat.toNat, Stmt.regsOK, Stmt.noInp, Stmt.noRand]
  | instr i =>
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand] at hr hn hd
    exact trI_ok hr hn hd
  | seq s t ihs iht =>
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true] at hr hn hd
    obtain ⟨a1, a2, a3⟩ := ihs hr.1 hn.1 hd.1
    obtain ⟨b1, b2, b3⟩ := iht hr.2 hn.2 hd.2
    simp [ModNat.toNat, Stmt.regsOK, Stmt.noInp, Stmt.noRand, a1, a2, a3, b1, b2, b3]
  | ifLtN a b t e iht ihe =>
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true, decide_eq_true_eq] at hr hn hd
    obtain ⟨a1, a2, a3⟩ := iht hr.1.2 hn.1 hd.1
    obtain ⟨b1, b2, b3⟩ := ihe hr.2 hn.2 hd.2
    simp only [ModNat.toNat, Stmt.regsOK, Stmt.noInp, Stmt.noRand, a1, a2, a3, b1, b2, b3,
      Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    simp only [and_true, true_and]
    first | omega | (constructor <;> omega)
  | ifLtR a b t e iht ihe =>
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true, decide_eq_true_eq] at hr hn hd
    obtain ⟨a1, a2, a3⟩ := iht hr.1.2 hn.1 hd.1
    obtain ⟨b1, b2, b3⟩ := ihe hr.2 hn.2 hd.2
    obtain ⟨c1, c2, c3⟩ := cmpS_ok hr.1.1.1 hr.1.1.2
    simp only [ModNat.toNat, Stmt.regsOK, Stmt.noInp, Stmt.noRand, a1, a2, a3, b1, b2, b3, c1, c2,
      c3, Bool.and_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    simp only [and_true, true_and]
    first | omega | (constructor <;> omega)
  | whileLtN a b body ih =>
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true, decide_eq_true_eq] at hr hn hd
    obtain ⟨a1, a2, a3⟩ := ih hr.2 hn hd
    simp only [ModNat.toNat, Stmt.regsOK, Stmt.noInp, Stmt.noRand, a1, a2, a3, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq]
    simp only [and_true, true_and]
    first | omega | (constructor <;> omega)
  | whileLtR a b body ih =>
    simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true, decide_eq_true_eq] at hr hn hd
    obtain ⟨a1, a2, a3⟩ := ih hr.2 hn hd
    obtain ⟨c1, c2, c3⟩ := cmpS_ok hr.1.1 hr.1.2
    simp only [ModNat.toNat, Stmt.regsOK, Stmt.noInp, Stmt.noRand, a1, a2, a3, c1, c2, c3,
      Bool.and_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    simp only [and_true, true_and]
    first | omega | (constructor <;> omega)

theorem frNat_ok : (Stmt.seq (constsS 372 (frM P L) (frH P L) (P.W + 1))
      (ModNat.toNat 372 (frM P L) frProg)).regsOK (fun r => decide (r < 748)) = true ∧
    (Stmt.seq (constsS 372 (frM P L) (frH P L) (P.W + 1))
      (ModNat.toNat 372 (frM P L) frProg)).noInp = true ∧
    (Stmt.seq (constsS 372 (frM P L) (frH P L) (P.W + 1))
      (ModNat.toNat 372 (frM P L) frProg)).noRand = true := by
  obtain ⟨a1, a2, a3⟩ := toNat_ok (M := frM P L) frProg_regsOK frProg_noInp frProg_noRand
  simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true]
  refine ⟨⟨by simp [constsS, block, Stmt.regsOK, Instr.regsOK, Instr.regs], a1⟩,
    ⟨by simp [constsS, block, Stmt.noInp, Instr.notInp], a2⟩,
    ⟨by simp [constsS, block, Stmt.noRand, Instr.noRand], a3⟩⟩

/-- **FR-Dijkstra on natural words, inside a larger configuration.** The real configuration `d`
is that of `frProg_exec_emb`, its real memory `≤ P.W` bounded by `BB P L`; the natural
configuration `dN`, with any word bound `WN ≥ frWN P L`, holds the residues of the reals of `d`
(`Sim`) and has its registers `< 748` and its memory `≤ frWN P L` bounded by `frWN P L`. Then
`frProg` runs from `d` as in `frProg_exec_emb` (to `d'`, with a run of Dijkstra's algorithm in
the memory), and the natural program runs from `dN` within `4 frCost P + 3` steps to a
configuration holding the residues of the reals of `d'`, keeping the registers `≥ 748` and the
memory above `frWN P L`. -/
theorem frProg_exec_emb_nat (hL : Lay P) (hXB : XB P L) (hDc : Crossing P.b P.D) (hF : Feas P)
    {W' : ℕ} (hW : P.W ≤ W') (d : Config) (hd : WordsBounded W' d) (hin : Inp P d)
    (hDa : Data P d) (hrb : ∀ r < 372, d.nreg r ≤ P.W) (hmb : ∀ a ≤ P.W, d.nmem a ≤ P.W)
    (hMB : MemB P.W (BB P L) d) {WN : ℕ} (hWN : frWN P L ≤ WN) {dN : Config}
    (hS : Sim 372 P.W (frM P L) (P.W + 1) d dN) (hdN : WordsBounded WN dN)
    (hdNr : ∀ r < 748, dN.nreg r ≤ frWN P L) (hdNm : ∀ a ≤ frWN P L, dN.nmem a ≤ frWN P L) :
    ∃ d' k, Exec I W' frProg d d' k ∧ k ≤ frCost P ∧ Data P d' ∧ d'.output = d.output ∧
      (∀ r < 100, d'.nreg r = d.nreg r) ∧ (∀ r < 100, d'.rreg r = d.rreg r) ∧
      (∃ K v dd, FRes P K v dd d'.nmem d'.rmem) ∧
      (∀ r, 372 ≤ r → d'.nreg r = d.nreg r) ∧ (∀ r, 372 ≤ r → d'.rreg r = d.rreg r) ∧
      (∀ a, P.W < a → d'.nmem a = d.nmem a) ∧ (∀ a, P.W < a → d'.rmem a = d.rmem a) ∧
      ∃ dN' k', Exec I WN (.seq (constsS 372 (frM P L) (frH P L) (P.W + 1))
          (ModNat.toNat 372 (frM P L) frProg)) dN dN' k' ∧ k' ≤ 4 * frCost P + 3 ∧
        Sim 372 P.W (frM P L) (P.W + 1) d' dN' ∧
        (∀ r, 748 ≤ r → dN'.nreg r = dN.nreg r) ∧ (∀ a, frWN P L < a → dN'.nmem a = dN.nmem a) := by
  -- the real run, on the truncation
  set c := trunc frU P.W d with hcdef
  have hA := agree_trunc frU P.W d
  have hn : ∀ r < 372, c.nreg r = d.nreg r := fun r hr => (hA.nreg r (by simp [frU, hr])).symm
  have hnr : ∀ r < 372, c.rreg r = d.rreg r := fun r hr => (hA.rreg r (by simp [frU, hr])).symm
  have hm : ∀ a ≤ P.W, c.nmem a = d.nmem a := fun a ha => (hA.nmem a ha).symm
  have hrm : ∀ a ≤ P.W, c.rmem a = d.rmem a := fun a ha => (hA.rmem a ha).symm
  have hw : WordsBounded P.W c :=
    wordsBounded_trunc (fun r hr => hrb r (by simpa [frU] using hr)) hmb
  have hinc : Inp P c := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hn _ (by omega)]
    exacts [hin.r100, hin.r101, hin.r102, hin.r103, hin.r104, hin.r105, hin.r106, hin.r107,
      hin.r108, hin.r109]
  have hDac : Data P c := hDa.congr hL (fun a ha => (hA.nmem a ha).symm)
    (fun a ha => (hA.rmem a ha).symm)
  obtain ⟨c', k, e, hk, hDa', ho, hr1, hr2, K, v, dd, hres⟩ :=
    frProg_exec (I := I) hL hDc hF c hw hinc hDac
  obtain ⟨d', e', hA', hK, ho'⟩ :=
    Exec.lift_trunc (P' := I) e frProg_regsOK frProg_noInp frProg_noRand hW hd
  -- the natural run, on the truncation of `dN`
  have hMBc : MemB P.W (BB P L) c := fun a ha => by rw [hrm a ha]; exact hMB a ha
  have hSc : Sim 372 P.W (frM P L) (P.W + 1) c dN :=
    ⟨fun r hr => by rw [hS.nreg r hr, hn r hr], fun r hr => by rw [hnr r hr]; exact hS.rreg r hr,
      fun a ha => by rw [hS.nmem a ha, hm a ha], fun a ha => by rw [hrm a ha]; exact hS.rmem a ha,
      hS.output⟩
  set U : ℕ → Bool := fun r => decide (r < 748) with hU
  set dNt := trunc U (frWN P L) dN with hdNt
  have hB := agree_trunc U (frWN P L) dN
  have hWf : 2 * P.W + 1 ≤ frWN P L := by unfold frWN; omega
  have hSt : Sim 372 P.W (frM P L) (P.W + 1) c dNt :=
    ⟨fun r hr => by rw [← hB.nreg r (by simp [hU]; omega)]; exact hSc.nreg r hr,
      fun r hr => by rw [← hB.nreg _ (by simp [hU]; omega)]; exact hSc.rreg r hr,
      fun a ha => by rw [← hB.nmem a (by omega)]; exact hSc.nmem a ha,
      fun a ha => by rw [← hB.nmem _ (by omega)]; exact hSc.rmem a ha, hSc.output⟩
  have hwt : WordsBounded (frWN P L) dNt :=
    wordsBounded_trunc (fun r hr => hdNr r (by simpa [hU] using hr)) hdNm
  have hcmp := (frProg_good (I := I) hL hXB hDc hF c hw hinc hDac).toCmp hMBc
  obtain ⟨dt', kt, et, hkt, hSt', -, -, -, -, -⟩ := (hcmp.exec e).toNat_consts frProg_regsOK
    (by decide) (show 2 * frH P L < frM P L by unfold frM; omega) (by omega)
    (by unfold frWN; omega) (by unfold frWN; omega) (by unfold frWN; omega) hSt hwt
  obtain ⟨ok1, ok2, ok3⟩ := frNat_ok (P := P) (L := L)
  obtain ⟨dN', eN, hAN, hKN, hoN⟩ := Exec.lift_trunc (P' := I) et ok1 ok2 ok3 hWN hdN
  refine ⟨d', k, e', hk, hDa'.congr hL hA'.nmem hA'.rmem, by rw [ho', ho]; rfl,
    fun r hr => ?_, fun r hr => ?_, ⟨K, v, dd, hres.congr hL hA'.nmem hA'.rmem⟩,
    fun r hr => hK.nreg r (by simp [frU]; omega), fun r hr => hK.rreg r (by simp [frU]; omega),
    hK.nmem, hK.rmem, dN', kt, eN, by omega, ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_,
      fun a ha => ?_, ?_⟩, fun r hr => hKN.nreg r (by simp [hU]; omega), hKN.nmem⟩
  · rw [hA'.nreg r (by simp [frU]; omega), hr1 r hr, hn r (by omega)]
  · rw [hA'.rreg r (by simp [frU]; omega), hr2 r hr, hnr r (by omega)]
  · rw [hAN.nreg r (by simp [hU]; omega), hSt'.nreg r hr, hA'.nreg r (by simp [frU, hr])]
  · rw [hAN.nreg _ (by simp [hU]; omega), hA'.rreg r (by simp [frU, hr])]; exact hSt'.rreg r hr
  · rw [hAN.nmem a (by omega), hSt'.nmem a ha, hA'.nmem a ha]
  · rw [hAN.nmem _ (by omega), hA'.rmem a ha]; exact hSt'.rmem a ha
  · rw [hoN, hSt'.output, ho']

end FR

end Monge

end PlanarFlow
