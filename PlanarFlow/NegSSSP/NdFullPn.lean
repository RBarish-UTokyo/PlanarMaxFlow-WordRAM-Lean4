module

public import PlanarFlow.NegSSSP.NdFullJ

/-!
# The full branch: the node's primary values before the node

The residues of the node's real data sit at `W' + 1 + …` with `W' = pnW p₀ p₁`, a word bound
computed by the node's own parameter program `pnProg` from the plain arrays of the two
instances; the full branch runs `pnProg` once before the node (renamed: `pnπ` exchanges its
registers `[10530, 10700)` with `[1000, 1170)`, so registers `≥ 3000` are untouched and the
node's zero registers `1000 … 1999` are zeroed again afterwards).

* `pnπ` (an involution, `rbF_inv_of`), `pnπ_lo`, `pnπ_hi`, `pnπ_out`;
* **`fbPn_exec`**: `rnS pnπ pnProg` from the sizes `PnIn` at `1080 … 1093`: within
  `pnCost` steps, `HnPrim` at `1000 + j` (`W'` in `r1022`, `M` in `r1023`, `H` in `r1024`);
  registers outside `[1000, 1170)`, memory, reals, output kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The block table of the renaming of `pnProg`. -/
def pnTbl : List (ℕ × ℕ × ℕ) := [(10530, 1000, 170)]

theorem pnTbl_disj : rbDisj pnTbl = true := by decide

/-- **The renaming of `pnProg`**: `[10530, 10700) ↔ [1000, 1170)`. -/
def pnπ : Equiv.Perm ℕ := Function.Involutive.toPerm _ (rbF_inv_of pnTbl_disj)

theorem pnπ_apply (r : ℕ) : pnπ r = rbF pnTbl r := rfl

theorem pnπ_symm : pnπ.symm = pnπ := Function.Involutive.toPerm_symm _

theorem pnπ_hi (j : ℕ) (hj : j < 170) : pnπ (10530 + j) = 1000 + j := by
  rw [pnπ_apply]; simp only [pnTbl, rbF]
  split_ifs <;> omega

theorem pnπ_lo (j : ℕ) (hj : j < 170) : pnπ (1000 + j) = 10530 + j := by
  rw [pnπ_apply]; simp only [pnTbl, rbF]
  split_ifs <;> omega

theorem pnπ_out (r : ℕ) (h1 : r < 1000 ∨ 1170 ≤ r) (h2 : r < 10530 ∨ 10700 ≤ r) : pnπ r = r := by
  rw [pnπ_apply]; simp only [pnTbl, rbF]
  split_ifs <;> omega

/-- The renamed parameter program. -/
def fbPn : Stmt := rnS pnπ pnProg

/-- **The node's primary values before the node** (see the module docstring). -/
theorem fbPn_exec {p₀ p₁ : FeP} {m w b B Y S : ℕ} (d : Config) (hd : WordsBounded W d)
    (hin : PnIn (fun r => d.nreg (pnπ r)) p₀ p₁ m w b B Y S)
    (hI0₀ : p₀.I0 = Y + 16 * S + 2 * w) (hI0₁ : p₁.I0 = p₀.END)
    (hL₀ : p₀.Lmax = feIsoB p₀.A p₀.N p₀.FN
      (1 + pwS d.nmem (p₀.I0 + 3 * p₀.nD) (p₀.I0 + 4 * p₀.nD) p₀.nD))
    (hL₁ : p₁.Lmax = feIsoB p₁.A p₁.N p₁.FN
      (1 + pwS d.nmem (p₁.I0 + 3 * p₁.nD) (p₁.I0 + 4 * p₁.nD) p₁.nD))
    (hb : 1 ≤ b) (hW1 : pnW p₀ p₁ ≤ W) (hW2 : 2 * nodeHN m b w B + 1 ≤ W)
    (hW3 : MSSP.isoN1 p₀.A p₀.N p₀.FN ≤ W) (hW4 : MSSP.isoN1 p₁.A p₁.N p₁.FN ≤ W)
    (h9600 : 9600 ≤ W) :
    ∃ d' t, Exec P W fbPn d d' t ∧ t ≤ pnCost p₀.nD p₁.nD ∧
      HnPrim (fun r => d'.nreg (pnπ r)) p₀ p₁ (Y + 16 * S) (Y + 16 * S + w) (pnW p₀ p₁)
        (2 * nodeHN m b w B + 1) (nodeHN m b w B) (MSSP.isoN1 p₀.A p₀.N p₀.FN)
        (MSSP.isoN1 p₁.A p₁.N p₁.FN)
        (1 + pwS d.nmem (p₀.I0 + 3 * p₀.nD) (p₀.I0 + 4 * p₀.nD) p₀.nD)
        (1 + pwS d.nmem (p₁.I0 + 3 * p₁.nD) (p₁.I0 + 4 * p₁.nD) p₁.nD) ∧
      (∀ r, (r < 1000 ∨ 1170 ≤ r) → d'.nreg r = d.nreg r) ∧
      d'.nmem = d.nmem ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  set e₀ := rnC pnπ d with he₀
  have hn₀ : ∀ r, e₀.nreg r = d.nreg (pnπ r) := fun r => by
    simp only [he₀, rnC, pnπ_symm]
  have hw₀ : WordsBounded W e₀ := ⟨fun r => by rw [hn₀]; exact hd.1 _, fun a => hd.2 a⟩
  have hin₀ : PnIn e₀.nreg p₀ p₁ m w b B Y S := by
    have : e₀.nreg = fun r => d.nreg (pnπ r) := funext hn₀
    rw [this]; exact hin
  obtain ⟨e', t, ex, ht, hprim, hk, hm, hr, hrm, ho⟩ :=
    pnProg_exec (P := P) e₀ hw₀ hin₀ hI0₀ hI0₁ hL₀ hL₁ hb hW1 hW2 hW3 hW4 h9600
  have ex' := rn_exec pnπ ex
  have hback : rnC pnπ e₀ = d := by
    rw [he₀]; have := nb_rnC_back pnπ d; rwa [pnπ_symm] at this
  rw [hback] at ex'
  have hn' : ∀ r, (rnC pnπ e').nreg (pnπ r) = e'.nreg r := fun r => rnC_nreg pnπ e' r
  refine ⟨rnC pnπ e', t, ex', ht, ?_, fun r hr => ?_, by simp [rnC, hm, he₀],
    by simp [rnC, hr, he₀], by simp [rnC, hrm, he₀], by simp [rnC, ho, he₀]⟩
  · have : (fun r => (rnC pnπ e').nreg (pnπ r)) = e'.nreg := funext hn'
    rw [this]; exact hprim
  · have hπ : pnπ (pnπ r) = r := rbF_inv_of pnTbl_disj r
    have hq : (rnC pnπ e').nreg r = e'.nreg (pnπ r) := by
      have := hn' (pnπ r); rwa [hπ] at this
    rw [hq, hk _ ?_, hn₀, hπ]
    by_cases h1 : 10530 ≤ r ∧ r < 10700
    · obtain ⟨j, rfl⟩ : ∃ j, r = 10530 + j := ⟨r - 10530, by omega⟩
      rw [pnπ_hi j (by omega)]; omega
    · rw [pnπ_out r hr (by omega)]; omega

end NegSSSP

end PlanarFlow
