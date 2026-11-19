module

public import PlanarFlow.NegSSSP.Enc.HoistFe

/-!
# The node program with its moduli out of the program text

Preparation of the constant hoisting of `nodeProgNN` (`HoistNode.lean`). The only places where
the node program is not "one template with the instance in `constN`" are

* the residues `(z mod M)` of the real constants of the simulated real programs
  (`ModNat.toNat 202 (2 Hc + 1) (kleinProgMem …)` inside `kPartN`, `ModNat.toNat 1000 M restProg`):
  all these constants are `0` or `1` (`hn_cr_klein`, `hn_cr_rest`, `hn_cr_bdry`, kernel-checked),
  so the modulus can be replaced by `2` (`hs_toNat`) when `Hc ≥ 1` and `M ≥ 2`;
* the meta-level choice `if p₀.Kw ≤ p₁.Kw then kPairN 0 807 p₀ 1 808 p₁ else kPairN 1 808 p₁ 0 807 p₀`.

`kPartN2`, `kPairN2`, `hnNodeA` (the first branch), `hnNodeB` (the second) are the programs with
modulus `2`; **`kPartN_eq2`**, **`nodeProgNN_eqA`**, **`nodeProgNN_eqB`** are the equations.
-/

@[expose] public section

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-- Klein's part on natural words with the residues of its real constants taken modulo `2`. -/
def hnKMem2 (p : KPN) : Stmt :=
  .seq (.seq (ModNat.constsS 202 (2 * p.Hc + 1) p.Hc p.βK)
      (ModNat.toNat 202 2 (Klein.kleinProgMem p.Bw p.nD p.n p.k p.k (p.Kw + 1) p.len)))
    (Klein.divCutLoop (p.βK + Klein.aOUT p.nD) (Klein.aRB p.n) (p.k * p.k) p.N1 p.Wc)

/-- `kPartN` with the residues of Klein's real constants modulo `2` (equal to `kPartN` when
`Hc ≥ 1`, `kPartN_eq2`). -/
def kPartN2 (p : KPN) : Stmt :=
  .seq (kpC p.k p.Pb) <| .seq cornerProg <|
  .seq (cpyNProg (p.Kw + 1) p.β (p.Kw + 1)) <| .seq (fillNProg p.βK (2 * p.Kw + 2)) <|
  .seq (cpyNProg p.βK p.RkN (3 * p.nD + 3)) <| .seq (zeroRegs (List.range 404)) <|
  .seq (hnKMem2 p) <|
  .seq (kpRN p.k p.n (p.βK + Klein.aOUT p.nD) p.βN p.M) <| .seq rdProgN
    (zeroRegs (List.range 408 ++ List.range' 910 9))

/-- The pair of parts with `kPartN2`. -/
def kPairN2 (zf δrf : ℕ) (pf : KPN) (zs δrs : ℕ) (ps : KPN) : Stmt :=
  .seq (partSet zf δrf) <| .seq (kPartN2 pf) <| .seq (partSet zs δrs) (kPartN2 ps)

/-- The node program, first branch (`p₀.Kw ≤ p₁.Kw`), the moduli of the residues of the real
constants replaced by `2`. -/
def hnNodeA (p₀ p₁ : KPN) (M H βN : ℕ) : Stmt :=
  .seq (.seq (ModNat.constsS 1000 M H βN) (ModNat.toNat 1000 2 (.seq bdSet bdryProg))) <|
  .seq (kPairN2 0 807 p₀ 1 808 p₁) (ModNat.toNat 1000 2 restProg)

/-- The node program, second branch (`p₁.Kw < p₀.Kw`). -/
def hnNodeB (p₀ p₁ : KPN) (M H βN : ℕ) : Stmt :=
  .seq (.seq (ModNat.constsS 1000 M H βN) (ModNat.toNat 1000 2 (.seq bdSet bdryProg))) <|
  .seq (kPairN2 1 808 p₁ 0 807 p₀) (ModNat.toNat 1000 2 restProg)

/-- The real constants of Klein's program are `0` or `1` (kernel-checked, for all parameters). -/
theorem hn_cr_klein (B nD n k t β len : ℕ) :
    hsCR 2 (Klein.kleinProgMem B nD n k t β len) = true := by
  kernel_rfl

theorem hn_cr_rest : hsCR 2 restProg = true := by kernel_rfl

theorem hn_cr_bdry : hsCR 0 (.seq bdSet bdryProg) = true := by kernel_rfl

/-- **`kPartN` with the modulus of the residues of Klein's constants replaced by `2`.** -/
theorem kPartN_eq2 (p : KPN) (hH : 1 ≤ p.Hc) : kPartN p = kPartN2 p := by
  have h := hs_toNat (R := 202) (M := 2 * p.Hc + 1) (M' := 2) _
    (hn_cr_klein p.Bw p.nD p.n p.k p.k (p.Kw + 1) p.len) (by omega) le_rfl
  simp only [kPartN, kPartN2, hnKMem2, Klein.kleinMemNDC, Klein.kleinMemN, h]

theorem kPairN_eq2 (zf δrf : ℕ) (pf : KPN) (zs δrs : ℕ) (ps : KPN) (hf : 1 ≤ pf.Hc)
    (hs : 1 ≤ ps.Hc) : kPairN zf δrf pf zs δrs ps = kPairN2 zf δrf pf zs δrs ps := by
  simp only [kPairN, kPairN2, kPartN_eq2 pf hf, kPartN_eq2 ps hs]

theorem hn_toNat_rest {M : ℕ} (hM : 2 ≤ M) :
    ModNat.toNat 1000 M restProg = ModNat.toNat 1000 2 restProg :=
  hs_toNat _ hn_cr_rest hM le_rfl

theorem hn_toNat_bdry (M : ℕ) :
    ModNat.toNat 1000 M (.seq bdSet bdryProg) = ModNat.toNat 1000 2 (.seq bdSet bdryProg) :=
  hs_toNat _ hn_cr_bdry (Nat.zero_le _) (Nat.zero_le _)

/-- **The node program, first branch.** -/
theorem nodeProgNN_eqA (p₀ p₁ : KPN) (M H βN : ℕ) (hK : p₀.Kw ≤ p₁.Kw) (h₀ : 1 ≤ p₀.Hc)
    (h₁ : 1 ≤ p₁.Hc) (hM : 2 ≤ M) : nodeProgNN p₀ p₁ M H βN = hnNodeA p₀ p₁ M H βN := by
  simp only [nodeProgNN, hnNodeA, hK, ↓reduceIte, kPairN_eq2 _ _ _ _ _ _ h₀ h₁,
    hn_toNat_rest hM, hn_toNat_bdry M]

/-- **The node program, second branch.** -/
theorem nodeProgNN_eqB (p₀ p₁ : KPN) (M H βN : ℕ) (hK : p₁.Kw < p₀.Kw) (h₀ : 1 ≤ p₀.Hc)
    (h₁ : 1 ≤ p₁.Hc) (hM : 2 ≤ M) : nodeProgNN p₀ p₁ M H βN = hnNodeB p₀ p₁ M H βN := by
  simp only [nodeProgNN, hnNodeB, show ¬ p₀.Kw ≤ p₁.Kw by omega, ↓reduceIte,
    kPairN_eq2 _ _ _ _ _ _ h₁ h₀, hn_toNat_rest hM, hn_toNat_bdry M]

end NegSSSP

end PlanarFlow
