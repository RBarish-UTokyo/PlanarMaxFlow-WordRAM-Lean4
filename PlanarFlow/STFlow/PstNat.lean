module

public import PlanarFlow.STFlow.PstCmp
public import PlanarFlow.Monge.FRNat
public import WordRAM.Machine.KernelRfl

/-!
# The s-t flow oracle on natural words

The program `pstProg` keeps its integers (lengths, keys, capacities, flows) in the exact real
registers of the machine. This file runs it **on natural words**: the program
`constsS 201 M H β; toNat 201 M pstProg` (`WordRAM/Machine/RealsModNat.lean`) keeps every real
value modulo `M = 2 H + 1` in natural words.

* `pstProg_regsOK`, `pstProg_noDivR`: the syntactic conditions of the simulation (registers
  `< 201`, no `divR`; checked by the kernel);
* `pstflowW_abs_le`: the flow values are at most `Σ capR` in absolute value;
* **`pstflowW_exec_nat`**: for every plane map with transitive rotations and faces, nonnegative
  capacities, `X` nonempty, a dart whose tail is in `Y` and `X`, `Y` disjoint, the run of
  `pstflowW_exec_exists_cmp` (within `504 000 000 · m lg m` steps, `OUT[d] = pstflowW M c X Y d`)
  is simulated from the natural configuration `natOf 201 W M (W + 1) c₀` holding the residues of
  the start, within `4 · 504 000 000 · m lg m + 3` steps and the word bound
  `pstWN W H = 2 W + 1 + M² + M` (`W = B + 16 (n + 1)`, `H = pstH n m #F #V isoW_bound`,
  `M = 2 H + 1`): at the end the natural memory cell `W + 1 + OUT + σ d` holds `v` with
  `pstflowW M c X Y d = v` if `v ≤ H` and `v - M` otherwise (the flow, of absolute value at most
  `H`, read back from its residue; negative flows are the residues above `H`).

The bound `H = 2 pstVb n m #F #V K` with `K = isoW_bound = (m + 4) (2 R + 1) (Σ capR + 1)`,
`pstVb = n · 4 (#F + #V) K + (m + 2) (2 n K + n + 4 K) + n · 8 #F K + n + K + 1`, `n = 2 (#F + #V + m)`:
`H = O(m² K) = O(m⁷ max c)`, so `M² + M = O(m¹⁴ (max c)²)`.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Machine.ModNat

/-- `pstProg` names only the registers `< 201` (checked by the kernel). -/
theorem pstProg_regsOK (B nD n : ℕ) :
    (pstProg B nD n).regsOK (fun r => decide (r < 201)) = true := by
  kernel_rfl

/-- `pstProg` uses no `divR` (checked by the kernel). -/
theorem pstProg_noDivR (B nD n : ℕ) : (pstProg B nD n).noDivR = true := by
  kernel_rfl

/-- The modulus. -/
def pstM (H : ℕ) : ℕ := 2 * H + 1

/-- The word bound of the program on natural words. -/
def pstWN (W H : ℕ) : ℕ := 2 * W + 1 + pstM H * pstM H + pstM H

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-- **The flow values are at most the total capacity** `Σ capR` in absolute value. -/
theorem pstflowW_abs_le (hM : M.IsPlane) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) {X Y : Finset V}
    (hXY : Disjoint X Y) (d : D) : |pstflowW M c X Y d| ≤ ∑ e, capR M c X Y e := by
  classical
  have hc' : ∀ e, 0 ≤ capR M c X Y e := capR_nonneg hc X Y
  have hS : 0 ≤ ∑ e, capR M c X Y e := sum_nonneg fun e _ => hc' e
  have hle : ∀ e, capR M c X Y e ≤ ∑ e, capR M c X Y e := fun e =>
    single_le_sum (fun e _ => hc' e) (mem_univ e)
  unfold pstflowW
  split_ifs with h
  · have : Nonempty D := ⟨h.2.choose⟩
    have hst : h.1.choose ≠ M.tail h.2.choose := fun e =>
      disjoint_left.1 hXY h.1.choose_spec (e ▸ h.2.choose_spec)
    obtain ⟨hP, -, -⟩ := pcoreFlowW_spec hM hc' hst (M.face h.2.choose)
    unfold restrictR
    split_ifs
    · simpa using hS
    · have h1 := hP.le_cap d
      have h2 := hP.le_cap (M.rev d)
      have h3 := hP.antisymm d
      rw [abs_le]
      constructor
      · have := hle (M.rev d); linarith
      · exact h1.trans (hle d)
  · simpa using hS

lemma sum_capR_le_iso (hM : M.IsPlane) [Nonempty D] {c : D → ℤ} (hc : ∀ d, 0 ≤ c d)
    (X Y : Finset V) : ∑ e, capR M c X Y e ≤ isoW_bound D V F (capR M c X Y) := by
  have hc' : ∀ e, 0 ≤ capR M c X Y e := capR_nonneg hc X Y
  have hS : 0 ≤ ∑ e, capR M c X Y e := sum_nonneg fun e _ => hc' e
  have hR : 0 ≤ isoR D V F := by unfold isoR; positivity
  unfold isoW_bound
  have h1 : (1 : ℤ) ≤ (Fintype.card D + 4) * (2 * isoR D V F + 1) := by nlinarith
  nlinarith

/-- **The s-t flow oracle on natural words.** For every plane map with transitive rotations and
faces, nonnegative capacities, `X` nonempty, a dart whose tail is in `Y`, `X`, `Y` disjoint:
there are an input `P`, sizes `n`, `B` and a starting configuration `c₀` (its reals integers,
`W = B + 16 (n + 1)`) from which `pstProg` runs within `504 000 000 · m lg m` steps to
`OUT[d] = pstflowW M c X Y d`; and the program on natural words
`constsS 201 M H (W + 1); toNat 201 M pstProg` (`H = pstH n m #F #V isoW_bound`, `M = 2 H + 1`)
runs from `natOf 201 W M (W + 1) c₀` (the residues of `c₀`, natural words only) within
`4 · 504 000 000 · m lg m + 3` steps and the word bound `pstWN W H = 2 W + 1 + M² + M`, printing
what `pstProg` prints (nothing), and ends with the flow `pstflowW M c X Y d` read from its residue
in the natural memory cell `W + 1 + OUT + σ d`: the residue `v` if `v ≤ H`, `v - M` otherwise. -/
theorem pstflowW_exec_nat (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) {X Y : Finset V} (hX : X.Nonempty)
    (hY : ∃ d, M.tail d ∈ Y) (hXY : Disjoint X Y) :
    ∃ (n B : ℕ) (P : Input) (c₀ c' : Config) (steps : ℕ),
      n = 2 * (Fintype.card F + Fintype.card V + Fintype.card D) ∧
      Exec P (B + 16 * (n + 1)) (pstProg B (Fintype.card D) n) c₀ c' steps ∧
      steps ≤ 504000000 * (Fintype.card D * lg (Fintype.card D)) ∧
      (∀ d, c'.rmem (aOT (Fintype.card D) + Fintype.equivFin D d) = pstflowW M c X Y d) ∧
      c'.output = c₀.output ∧
      ∃ d' k', Exec P (pstWN (B + 16 * (n + 1))
          (pstH n (Fintype.card D) (Fintype.card F) (Fintype.card V)
            (isoW_bound D V F (capR M c X Y)).toNat))
        (.seq (constsS 201 (pstM (pstH n (Fintype.card D) (Fintype.card F) (Fintype.card V)
            (isoW_bound D V F (capR M c X Y)).toNat))
          (pstH n (Fintype.card D) (Fintype.card F) (Fintype.card V)
            (isoW_bound D V F (capR M c X Y)).toNat) (B + 16 * (n + 1) + 1))
          (ModNat.toNat 201 (pstM (pstH n (Fintype.card D) (Fintype.card F) (Fintype.card V)
            (isoW_bound D V F (capR M c X Y)).toNat)) (pstProg B (Fintype.card D) n)))
        (natOf 201 (B + 16 * (n + 1)) (pstM (pstH n (Fintype.card D) (Fintype.card F)
            (Fintype.card V) (isoW_bound D V F (capR M c X Y)).toNat)) (B + 16 * (n + 1) + 1) c₀)
        d' k' ∧
      k' ≤ 4 * (504000000 * (Fintype.card D * lg (Fintype.card D))) + 3 ∧
      d'.output = c₀.output ∧
      ∀ d, pstflowW M c X Y d =
        if d'.nmem (B + 16 * (n + 1) + 1 + (aOT (Fintype.card D) + Fintype.equivFin D d)) ≤
            pstH n (Fintype.card D) (Fintype.card F) (Fintype.card V)
              (isoW_bound D V F (capR M c X Y)).toNat
        then (d'.nmem (B + 16 * (n + 1) + 1 + (aOT (Fintype.card D) + Fintype.equivFin D d)) : ℤ)
        else (d'.nmem (B + 16 * (n + 1) + 1 + (aOT (Fintype.card D) + Fintype.equivFin D d)) : ℤ) -
          pstM (pstH n (Fintype.card D) (Fintype.card F) (Fintype.card V)
            (isoW_bound D V F (capR M c X Y)).toNat) := by
  have : Nonempty D := ⟨hY.choose⟩
  obtain ⟨n, B, P, c₀, c', steps, h1, hB7, e, hst, hOUT, hout, hmem, hreg, hcmp⟩ :=
    pstflowW_exec_exists_cmp hM hrot hface hc hX hY hXY
  set W := B + 16 * (n + 1) with hW
  set H := pstH n (Fintype.card D) (Fintype.card F) (Fintype.card V)
    (isoW_bound D V F (capR M c X Y)).toNat with hH
  set Mm := pstM H with hMm
  have hM0 : 0 < Mm := by rw [hMm]; unfold pstM; omega
  have hSim : Sim 201 W Mm (W + 1) c₀ (natOf 201 W Mm (W + 1) c₀) :=
    sim_natOf (by omega) hM0 (fun r _ => ⟨0, by rw [hreg r]; simp⟩)
      (fun a _ => by obtain ⟨z, hz, -⟩ := hmem a; exact ⟨z, hz⟩)
  have hwb : WordsBounded (pstWN W H) (natOf 201 W Mm (W + 1) c₀) :=
    natOf_wb e.wb_left (by unfold pstWN; omega) (by rw [hMm]; unfold pstWN; omega) hM0
  obtain ⟨d', k', e', hk', hS', -, -, -, -, -⟩ := (hcmp.exec e).toNat_consts (pstProg_regsOK _ _ _)
    (pstProg_noDivR _ _ _) (show 2 * H < Mm by rw [hMm]; unfold pstM; omega) (show W < W + 1 by omega)
    (by unfold pstWN; omega) (by unfold pstWN; omega) (by rw [hMm]; unfold pstWN; omega) hSim hwb
  refine ⟨n, B, P, c₀, c', steps, h1, e, hst, hOUT, hout, d', k', e', by omega,
    hS'.output.trans hout, fun d => ?_⟩
  -- the flow read back from its residue
  have hσ := (Fintype.equivFin D d).2
  have hres := hS'.rmem (aOT (Fintype.card D) + Fintype.equivFin D d)
    (by unfold aOT; omega)
  rw [hOUT d] at hres
  have hb : |((pstflowW M c X Y d : ℤ) : ℝ)| ≤ H := by
    have h1 := (pstflowW_abs_le hM hc hXY d).trans (sum_capR_le_iso hM hc X Y)
    have h2 : isoW_bound D V F (capR M c X Y) ≤ ((isoW_bound D V F (capR M c X Y)).toNat : ℤ) :=
      Int.self_le_toNat _
    have h3 : (isoW_bound D V F (capR M c X Y)).toNat ≤ H := by
      rw [hH]; unfold pstH pstVb; omega
    have h4 : |pstflowW M c X Y d| ≤ (H : ℤ) := by
      have : ((isoW_bound D V F (capR M c X Y)).toNat : ℤ) ≤ (H : ℤ) := by exact_mod_cast h3
      linarith
    exact_mod_cast h4
  have hdec := hres.signed hb (show 2 * H < Mm by rw [hMm]; unfold pstM; omega)
  split_ifs at hdec ⊢ with hv
  · exact_mod_cast hdec
  · exact_mod_cast hdec

end STFlow

end PlanarFlow
