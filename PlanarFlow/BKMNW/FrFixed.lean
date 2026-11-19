module

public import PlanarFlow.Monge.FRNat
public import PlanarFlow.Klein.ExecNat
public import WordRAM.Machine.Iter
public import PlanarFlow.BKMNW.LgNat

/-!
# FR-Dijkstra on natural words as one fixed program

`frProg_exec_emb_nat` runs the natural-word program `constsS 372 M H β ; toNat 372 M frProg`,
whose text depends on the instance (the constants `M = frM P L`, `H = frH P L`, `β = P.W + 1`).
Here the constants are hoisted (as `drvT` did for `negFix`):

* `cR0` (every real constant of a statement is `0`), **`toNat_cR0`** (then `toNat R M s` does not
  depend on `M`), `frProg_cR0` (kernel-checked);
* **`frNF`** `= (r744 := r760 ; r745 := r761 ; r746 := r762) ; toNat 372 0 frProg`, one fixed
  program; `frNF_natOnly`, `frNF_noInp`, `frNF_noRand`, `frNF_regsOK` (registers `< 763`);
* **`frNF_lgRun`**: the logged run `lgS LP ONE frNF` in place, from any configuration agreeing with
  the start on the registers `< 763` and the memory `≤ WN` (reals arbitrary and kept), within
  three times the steps: the same registers and memory `≤ WN` as the run of `frNF`, the log of
  the stores (`LgKeep`) above `WN` (for `lgClr` to restore a zero memory afterwards);
* **`frNF_exec`**: whenever `constsS 372 M H β ; toNat 372 M frProg` runs from `dN` (e.g. by
  `frProg_exec_emb_nat`) and `r760 = M`, `r761 = H`, `r762 = β`, the fixed program `frNF` runs from
  `dN` to the same configuration in the same number of steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace FrFix

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Machine.ModNat WordRAM.Programs

/-- Every real constant of the statement is `0`. -/
def cR0 : Stmt → Bool
  | .skip => true
  | .instr (.constR _ z) => decide (z = 0)
  | .instr _ => true
  | .seq s t => cR0 s && cR0 t
  | .ifLtN _ _ t e => cR0 t && cR0 e
  | .ifLtR _ _ t e => cR0 t && cR0 e
  | .whileLtN _ _ b => cR0 b
  | .whileLtR _ _ b => cR0 b

theorem trI_cR0 (R M M' : ℕ) (i : Instr) (h : cR0 (.instr i) = true) :
    trI R M i = trI R M' i := by
  cases i with
  | constR r z =>
    simp only [cR0, decide_eq_true_eq] at h
    subst h
    simp [trI]
  | _ => rfl

/-- **Without real constants other than `0`, the translation does not depend on the modulus.** -/
theorem toNat_cR0 (R M M' : ℕ) : ∀ s : Stmt, cR0 s = true → toNat R M s = toNat R M' s
  | .skip, _ => rfl
  | .instr i, h => by simp only [toNat]; exact trI_cR0 R M M' i h
  | .seq s t, h => by
    simp only [cR0, Bool.and_eq_true] at h
    simp only [toNat, toNat_cR0 R M M' s h.1, toNat_cR0 R M M' t h.2]
  | .ifLtN a b t e, h => by
    simp only [cR0, Bool.and_eq_true] at h
    simp only [toNat, toNat_cR0 R M M' t h.1, toNat_cR0 R M M' e h.2]
  | .ifLtR a b t e, h => by
    simp only [cR0, Bool.and_eq_true] at h
    simp only [toNat, toNat_cR0 R M M' t h.1, toNat_cR0 R M M' e h.2]
  | .whileLtN a b body, h => by
    simp only [cR0] at h
    simp only [toNat, toNat_cR0 R M M' body h]
  | .whileLtR a b body, h => by
    simp only [cR0] at h
    simp only [toNat, toNat_cR0 R M M' body h]

theorem frProg_cR0 : cR0 Monge.FR.frProg = true := by decide +kernel

/-- **The fixed natural-word FR-Dijkstra**: the constants from `r760 … r762`. -/
def frNF : Stmt :=
  .seq (block [.copyN 744 760, .copyN 745 761, .copyN 746 762]) (toNat 372 0 Monge.FR.frProg)

theorem frNF_natOnly : Klein.natOnly frNF = true := by decide +kernel

theorem frNF_noInp : frNF.noInp = true := by decide +kernel

theorem frNF_noRand : frNF.noRand = true := by decide +kernel

theorem frNF_regsOK : frNF.regsOK (fun r => decide (r < 763)) = true := by decide +kernel

variable {P : Input} {W : ℕ}

lemma cfg_eq {c d : Config} (h0 : c.pc = d.pc) (h1 : c.nreg = d.nreg) (h2 : c.rreg = d.rreg)
    (h3 : c.nmem = d.nmem) (h4 : c.rmem = d.rmem) (h5 : c.output = d.output) : c = d := by
  cases c; cases d; simp_all

/-- **The fixed program runs as the instance program.** -/
theorem frNF_exec {M H β : ℕ} {dN dN' : Config} {k : ℕ}
    (h : Exec P W (.seq (constsS 372 M H β) (toNat 372 M Monge.FR.frProg)) dN dN' k)
    (r60 : dN.nreg 760 = M) (r61 : dN.nreg 761 = H) (r62 : dN.nreg 762 = β) :
    Exec P W frNF dN dN' k := by
  obtain ⟨c₁, k₁, k₂, e₁, e₂, rfl⟩ := Exec.seq_inv h
  have hw : WordsBounded W dN := e₁.wb_left
  obtain ⟨d₁, t₁, f₁, ht₁, fn, fm, fr, frm, fo⟩ : ∃ d₁ t₁,
      Exec P W (block [.copyN 744 760, .copyN 745 761, .copyN 746 762]) dN d₁ t₁ ∧ t₁ = 3 ∧
      d₁.nreg = upd (upd (upd dN.nreg 744 M) 745 H) 746 β ∧ d₁.nmem = dN.nmem ∧
      d₁.rreg = dN.rreg ∧ d₁.rmem = dN.rmem ∧ d₁.output = dN.output := by
    exec_block
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
    config_simp
    simp only [r60, r61, r62]
  have hM : M ≤ W := r60 ▸ hw.1 760
  have hH : H ≤ W := r61 ▸ hw.1 761
  have hβ : β ≤ W := r62 ▸ hw.1 762
  obtain ⟨g₁, u₁, h₁, hu₁, gn, gm, gr, grm, go⟩ : ∃ g₁ u₁,
      Exec P W (constsS 372 M H β) dN g₁ u₁ ∧ u₁ = 3 ∧
      g₁.nreg = upd (upd (upd dN.nreg 744 M) 745 H) 746 β ∧ g₁.nmem = dN.nmem ∧
      g₁.rreg = dN.rreg ∧ g₁.rmem = dN.rmem ∧ g₁.output = dN.output := by
    unfold constsS
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
    config_simp
  obtain ⟨rfl, rfl⟩ := Exec.det e₁ h₁
  have he : d₁ = c₁ := cfg_eq (by rw [f₁.pc_eq, h₁.pc_eq]) (by rw [fn, gn]) (by rw [fr, gr])
    (by rw [fm, gm]) (by rw [frm, grm]) (by rw [fo, go])
  rw [← he] at e₂
  rw [toNat_cR0 372 M 0 _ frProg_cR0] at e₂
  rw [hu₁, ← ht₁]
  exact .seq f₁ e₂

/-- **The logged in-place run of the fixed natural-word FR-Dijkstra.** -/
theorem frNF_lgRun {P' : Input} {WN : ℕ} {dN dN' : Config} {k : ℕ} (h : Exec P WN frNF dN dN' k)
    {LP ONE : ℕ} (hLP : 763 ≤ LP) (hONE : 763 ≤ ONE) (hne : LP ≠ ONE) (hWs : WN ≤ W)
    (d : Config) (hA : ∀ r < 763, d.nreg r = dN.nreg r) (hm : ∀ a ≤ WN, d.nmem a = dN.nmem a)
    (hd : WordsBounded W d) (h1 : d.nreg ONE = 1) (hp : WN < d.nreg LP)
    (hpW : d.nreg LP + k ≤ W) :
    ∃ d' k' j, Exec P' W (NegSSSP.lgS LP ONE frNF) d d' k' ∧ k' ≤ 3 * k ∧ j ≤ k ∧
      (∀ r < 763, d'.nreg r = dN'.nreg r) ∧ (∀ a ≤ WN, d'.nmem a = dN'.nmem a) ∧
      NegSSSP.LgKeep (fun r => decide (r < 763)) WN LP (d.nreg LP) j d d' ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧
      ∃ L, dN'.output = dN.output ++ L ∧ d'.output = d.output ++ L := by
  obtain ⟨d', k', j, ex, hk, hj, hA', hm', hK, hr, hrm, L, o1, o2⟩ :=
    MfDrv.lg_liftNat (P' := P') h frNF_regsOK frNF_noInp frNF_noRand frNF_natOnly
      (by simp; omega) (by simp; omega) hne hWs d (fun r hr => hA r (by simpa using hr)) hm hd h1
      hp hpW
  exact ⟨d', k', j, ex, hk, hj, fun r hr => hA' r (by simpa using hr), hm', hK, hr, hrm, L, o1, o2⟩

end FrFix

end BKMNW

end PlanarFlow
