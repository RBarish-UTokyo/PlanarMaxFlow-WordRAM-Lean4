module

public import PlanarFlow.BKMNW.NcRb

/-!
# The bits of `rbP` and the set `C⁺` of `c2sG`

* **`rbRes_eq`**: with `FL[i] = Z + g (en i)` and `CP[i] = U (en i)`, the residual bit of `rbP`
  is `[g (en i) < U (en i)]`;
* **`rbSrc_eq`**: with `CF[i] = [tail (en i) ∈ C]`, `LAB[i] = l + 1` and
  `DV[l] - Z · DG[l] = div g (tail (en i))` (what `MfDrv.dvP_exec`/`dvP_div` give), the source bit
  is `[tail (en i) ∈ posSet g C]`;
* **`rb_fwdReach`**: hence the reach bit of the dart `i` (`rbP_exec`) is `1` iff its tail is reached
  from `posSet g C` by residual paths; with `CF[i]`, iff the tail is in
  `fwdReach U g (posSet g C) C` (the set `C⁺` of `c2sBeta`, `delSet`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Relation CombMap NsStep NegSSSP

universe w

lemma bit_eq {a b : ℕ} : (a - b) / (a - b) = if b < a then 1 else 0 := by
  split_ifs with h
  · exact Nat.div_self (by omega)
  · rw [show a - b = 0 by omega]

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

/-- The residual bit. -/
theorem rbRes_eq {mem : ℕ → ℕ} {FLb CPb Z i : ℕ} {U g : D → ℤ} {d : D}
    (hfl : (mem (FLb + i) : ℤ) = Z + g d) (hcp : (mem (CPb + i) : ℤ) = U d) :
    rbRes mem FLb CPb Z i = if g d < U d then 1 else 0 := by
  unfold rbRes
  rw [bit_eq]
  by_cases h : g d < U d
  · rw [iteT h, iteT (by omega)]
  · rw [iteF h, iteF (by omega)]

/-- The source bit. -/
theorem rbSrc_eq {mem : ℕ → ℕ} {Z CFb LABb DVb DGb i l : ℕ} {g : D → ℤ} {C : Finset V} {v : V}
    (hcf : mem (CFb + i) = if v ∈ C then 1 else 0) (hl : mem (LABb + i) = l + 1)
    (hdv : (mem (DVb + l) : ℤ) - Z * mem (DGb + l) = M.div g v) :
    rbSrc mem Z CFb LABb DVb DGb i = if v ∈ posSet M g C then 1 else 0 := by
  unfold rbSrc
  rw [hl, Nat.add_sub_cancel, bit_eq, hcf]
  have e : ((mem (DGb + l) * Z : ℕ) : ℤ) = (Z : ℤ) * mem (DGb + l) := by push_cast; ring
  have key : mem (DVb + l) < mem (DGb + l) * Z ↔ M.div g v < 0 := by
    constructor
    · intro h
      have h' : ((mem (DVb + l) : ℕ) : ℤ) < ((mem (DGb + l) * Z : ℕ) : ℤ) := by exact_mod_cast h
      rw [e] at h'; linarith
    · intro h
      have h' : ((mem (DVb + l) : ℕ) : ℤ) < ((mem (DGb + l) * Z : ℕ) : ℤ) := by rw [e]; linarith
      exact_mod_cast h'
  by_cases hC : v ∈ C
  · have hp : v ∈ posSet M g C ↔ M.div g v < 0 := by simp [posSet, hC]
    by_cases hn : M.div g v < 0
    · rw [iteT hC, iteT (key.2 hn), iteT (hp.2 hn)]
    · rw [iteT hC, iteF (fun h => hn (key.1 h)), iteF (fun h => hn (hp.1 h))]
  · rw [iteF hC, zero_mul, iteF (fun h => hC (by simp only [posSet, mem_filter] at h; exact h.1))]

open Classical in
/-- **The reach bits of `rbP` are the residual reachability from `posSet g C`.** -/
theorem rb_fwdReach (h : EnumOK M en m) (hrot : M.RotTrans) (hV : ∀ v, ∃ d, M.tail d = v)
    {U g : D → ℤ} {C : Finset V} {res src : ℕ → ℕ}
    (hres : ∀ i < m, res i = if g (en i) < U (en i) then 1 else 0)
    (hsrc : ∀ i < m, src i = if M.tail (en i) ∈ posSet M g C then 1 else 0) {i : ℕ}
    (hi : i < m) :
    (ReflTransGen (BfsAdj (rbOb m) (rbOe m res) id (rbHd m (sgI M en m) (rvI M en m) src)) m i ∧
        M.tail (en i) ∈ C) ↔ M.tail (en i) ∈ fwdReach M U g (posSet M g C) C := by
  rw [rb_reach h hrot hV hres hsrc hi]
  simp only [fwdReach, mem_filter]
  tauto

end NcStep

end BKMNW

end PlanarFlow
