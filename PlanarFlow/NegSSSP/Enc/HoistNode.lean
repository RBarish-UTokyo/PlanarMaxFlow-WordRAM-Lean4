module

public import PlanarFlow.NegSSSP.Enc.HoistNodeA

/-!
# The node program as one fixed program

Constant hoisting (`HoistGen.lean`) applied to the node program `nodeProgNN p₀ p₁ M H βN`
(after `HoistNodeA.lean`: moduli of the residues of the real constants replaced by `2`, the two
branches of the meta-level test `p₀.Kw ≤ p₁.Kw` as `hnNodeA`, `hnNodeB`):

* `kpVL p`: **the 55 parameters of a part** `p : KPN` (`p.k`, `p.Pb`, `p.Kw + 1`, `p.β`,
  `2 p.Kw + 2`, `p.βK`, `3 p.nD + 3`, `p.RkN`, `2 p.Hc + 1`, `p.Hc`, `p.n`, `p.Bw + j`
  (`j < 16`), Klein's input offsets `iHD`, `iIV`, …, `p.k * p.k`, `p.N1`, `p.βK + aOUT p.nD`,
  `p.Wc`, `p.βN`, `p.M`);
* `hnVL p₀ p₁ M H βN = [M, H, βN] ++ kpVL p₀ ++ kpVL p₁ ++ [p₀.Kw, p₁.Kw]`: **the 115 parameters
  of the node**, in the registers `10400 + j`;
* `hnM0`, `hnM1` (marker parts), `hnTbl` (the 113 marker values and their parameter numbers);
* the pieces `hnX` (`constsS`), `hnY`, `hnPA`, `hnPB` (the two pairs of parts), `hnZ`, and
  **`nodeFixT = (hnX ; hnY) ; (ifLtN 10514 10513 hnPB hnPA ; hnZ)`**: one statement, independent
  of the instance; the meta-level test became the machine test `p₁.Kw < p₀.Kw` on the registers
  `10514`, `10513`;
* kernel-checked equations `hnX_eq`, `hnPA_eq`, `hnPB_eq`, `hnY_eq`, `hnZ_eq`
  (`hsUn 10400 (hnV …) piece = piece of the instance`, for **all** parameters) and register
  conditions `hnX_ok`, …;
* **`nodeFix_exec`**: every run of `nodeProgNN p₀ p₁ M H βN` (with `Hcᵢ ≥ 1`, `M ≥ 2`) from a
  configuration holding `hnVL p₀ p₁ M H βN` at `10400` is a run of `nodeFixT` between the same
  configurations, within **one or two more steps** (the machine test); the registers `≥ 10400`
  are kept.
-/

@[expose] public section

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-- **The 55 parameters of a part** (the constants of `kPartN2 p`, in the order of `hnTbl`). -/
def kpVL (p : KPN) : List ℕ :=
  [p.k,
    p.Pb,
    p.Kw + 1,
    p.β,
    2 * p.Kw + 2,
    p.βK,
    3 * p.nD + 3,
    p.RkN,
    2 * p.Hc + 1,
    p.Hc,
    p.n,
    p.Bw + 0,
    p.Bw + 1,
    p.Bw + 2,
    p.Bw + 3,
    p.Bw + 4,
    p.Bw + 5,
    p.Bw + 6,
    p.Bw + 7,
    p.Bw + 8,
    p.Bw + 9,
    p.Bw + 10,
    p.Bw + 11,
    p.Bw + 12,
    p.Bw + 13,
    p.Bw + 14,
    p.Bw + 15,
    Klein.iHD p.nD p.n p.k,
    Klein.iIV p.nD p.n p.k,
    Klein.iHD p.nD p.n p.k + 1,
    Klein.iIT p.nD p.n p.k,
    Klein.iNG p.nD,
    Klein.aPH p.nD,
    Klein.iNT p.nD,
    Klein.iNH p.nD,
    Klein.aVL p.nD,
    Klein.aH0 p.nD,
    Klein.iHD p.nD p.n p.k + 2,
    Klein.iIF p.nD p.n p.k,
    Klein.iHD p.nD p.n p.k + 3,
    Klein.iIC p.nD p.n p.k,
    Klein.iGB p.nD p.n,
    Klein.iXT p.nD p.n p.k,
    Klein.iXT p.nD p.n p.k + p.k,
    Klein.aTH p.nD,
    Klein.iED p.nD,
    Klein.iOB p.nD p.n p.k,
    Klein.iOE p.nD p.n p.k,
    Klein.iOL p.nD p.n p.k,
    p.k * p.k,
    p.N1,
    p.βK + Klein.aOUT p.nD,
    p.Wc,
    p.βN,
    p.M]

theorem kpVL_length (p : KPN) : (kpVL p).length = 55 := rfl

/-- **The 115 parameters of the node.** -/
def hnVL (p₀ p₁ : KPN) (M H βN : ℕ) : List ℕ :=
  [M, H, βN] ++ kpVL p₀ ++ kpVL p₁ ++ [p₀.Kw, p₁.Kw]

/-- The `j`-th parameter of the node. -/
def hnV (p₀ p₁ : KPN) (M H βN : ℕ) (j : ℕ) : ℕ := (hnVL p₀ p₁ M H βN).getD j 0

theorem hnVL_length (p₀ p₁ : KPN) (M H βN : ℕ) : (hnVL p₀ p₁ M H βN).length = 115 := rfl

/-- The marker of the first part. -/
def hnM0 : KPN := ⟨1000000007, 1000000009, 1000000021, 1000000033, 1000000087, 1000000093,
  1000000097, 1000000103, 1000000123, 1000000181, 1000000207, 1000000223, 1000000241, 1000000271⟩

/-- The marker of the second part. -/
def hnM1 : KPN := ⟨1000000000039, 1000000000061, 1000000000063, 1000000000091, 1000000000121,
  1000000000163, 1000000000169, 1000000000177, 1000000000189, 1000000000193, 1000000000211,
  1000000000271, 1000000000303, 1000000000329⟩

/-- The markers of `M`, `H`, `βN`. -/
def hnMM : ℕ := 7000000000000001
def hnMH : ℕ := 7000000000000013
def hnMB : ℕ := 7000000000000019

/-- The marker values of the node's constants and their parameter numbers. -/
def hnTbl : List (ℕ × ℕ) :=
  [(7000000000000001, 0),
    (7000000000000013, 1),
    (7000000000000019, 2),
    (1000000007, 3),
    (1000000103, 4),
    (17000000386, 5),
    (1000000093, 6),
    (34000000772, 7),
    (1000000223, 8),
    (3000000030, 9),
    (1000000097, 10),
    (2000000247, 11),
    (1000000123, 12),
    (1000000021, 13),
    (1000000033, 14),
    (1000000034, 15),
    (1000000035, 16),
    (1000000036, 17),
    (1000000037, 18),
    (1000000038, 19),
    (1000000039, 20),
    (1000000040, 21),
    (1000000041, 22),
    (1000000042, 23),
    (1000000043, 24),
    (1000000044, 25),
    (1000000045, 26),
    (1000000046, 27),
    (1000000047, 28),
    (1000000048, 29),
    (17000000235, 30),
    (13000000151, 31),
    (17000000236, 32),
    (14000000172, 33),
    (3000000027, 34),
    (1000000009, 35),
    (4000000036, 36),
    (5000000045, 37),
    (2000000018, 38),
    (3000000029, 39),
    (17000000237, 40),
    (15000000193, 41),
    (17000000238, 42),
    (16000000214, 43),
    (9000000093, 44),
    (17000000239, 45),
    (18000000246, 46),
    (3000000028, 47),
    (8000000072, 48),
    (10000000100, 49),
    (11000000121, 50),
    (12000000142, 51),
    (1000000014000000049, 52),
    (1000000181, 53),
    (4000000253, 54),
    (1000000207, 55),
    (1000000241, 56),
    (1000000271, 57),
    (1000000000039, 58),
    (1000000000177, 59),
    (17000000001116, 60),
    (1000000000163, 61),
    (34000000002232, 62),
    (1000000000271, 63),
    (3000000000186, 64),
    (1000000000169, 65),
    (2000000000379, 66),
    (1000000000189, 67),
    (1000000000063, 68),
    (1000000000091, 69),
    (1000000000092, 70),
    (1000000000093, 71),
    (1000000000094, 72),
    (1000000000095, 73),
    (1000000000096, 74),
    (1000000000097, 75),
    (1000000000098, 76),
    (1000000000099, 77),
    (1000000000100, 78),
    (1000000000101, 79),
    (1000000000102, 80),
    (1000000000103, 81),
    (1000000000104, 82),
    (1000000000105, 83),
    (1000000000106, 84),
    (17000000001029, 85),
    (13000000000777, 86),
    (17000000001030, 87),
    (14000000000840, 88),
    (3000000000183, 89),
    (1000000000061, 90),
    (4000000000244, 91),
    (5000000000305, 92),
    (2000000000122, 93),
    (3000000000185, 94),
    (17000000001031, 95),
    (15000000000903, 96),
    (17000000001032, 97),
    (16000000000966, 98),
    (9000000000551, 99),
    (17000000001033, 100),
    (18000000001072, 101),
    (3000000000184, 102),
    (8000000000488, 103),
    (10000000000590, 104),
    (11000000000653, 105),
    (12000000000716, 106),
    (1000000000078000000001521, 107),
    (1000000000193, 108),
    (4000000000457, 109),
    (1000000000211, 110),
    (1000000000303, 111),
    (1000000000329, 112)]

/-- The fixed `constsS`. -/
def hnX : Stmt := hsHoist 10400 hnTbl (ModNat.constsS 1000 hnMM hnMH hnMB)
/-- The boundary part (no instance constant). -/
def hnY : Stmt := ModNat.toNat 1000 2 (.seq bdSet bdryProg)
/-- The fixed pair of parts, first branch. -/
def hnPA : Stmt := hsHoist 10400 hnTbl (kPairN2 0 807 hnM0 1 808 hnM1)
/-- The fixed pair of parts, second branch. -/
def hnPB : Stmt := hsHoist 10400 hnTbl (kPairN2 1 808 hnM1 0 807 hnM0)
/-- The rest (no instance constant). -/
def hnZ : Stmt := ModNat.toNat 1000 2 restProg

/-- **The node as one fixed statement.** -/
def nodeFixT : Stmt := .seq (.seq hnX hnY) (.seq (.ifLtN 10514 10513 hnPB hnPA) hnZ)

theorem hnX_eq (p₀ p₁ : KPN) (M H βN : ℕ) :
    hsUn 10400 (hnV p₀ p₁ M H βN) hnX = ModNat.constsS 1000 M H βN := by kernel_rfl

theorem hnY_eq (p₀ p₁ : KPN) (M H βN : ℕ) :
    hsUn 10400 (hnV p₀ p₁ M H βN) hnY = ModNat.toNat 1000 2 (.seq bdSet bdryProg) := by
  kernel_rfl

theorem hnZ_eq (p₀ p₁ : KPN) (M H βN : ℕ) :
    hsUn 10400 (hnV p₀ p₁ M H βN) hnZ = ModNat.toNat 1000 2 restProg := by kernel_rfl

set_option maxRecDepth 100000 in
/-- **The fixed pair is the pair of parts of every instance** (first branch, kernel-checked). -/
theorem hnPA_eq (p₀ p₁ : KPN) (M H βN : ℕ) :
    hsUn 10400 (hnV p₀ p₁ M H βN) hnPA = kPairN2 0 807 p₀ 1 808 p₁ := by kernel_rfl

set_option maxRecDepth 100000 in
/-- **The fixed pair is the pair of parts of every instance** (second branch, kernel-checked). -/
theorem hnPB_eq (p₀ p₁ : KPN) (M H βN : ℕ) :
    hsUn 10400 (hnV p₀ p₁ M H βN) hnPB = kPairN2 1 808 p₁ 0 807 p₀ := by kernel_rfl

theorem hnX_ok : hsOK 10400 115 hnX = true := by kernel_rfl
set_option maxRecDepth 100000 in
theorem hnY_ok : hsOK 10400 115 hnY = true := by kernel_rfl
set_option maxRecDepth 100000 in
theorem hnZ_ok : hsOK 10400 115 hnZ = true := by kernel_rfl
set_option maxRecDepth 100000 in
theorem hnPA_ok : hsOK 10400 115 hnPA = true := by kernel_rfl
set_option maxRecDepth 100000 in
theorem hnPB_ok : hsOK 10400 115 hnPB = true := by kernel_rfl

theorem hnV_kw0 (p₀ p₁ : KPN) (M H βN : ℕ) : hnV p₀ p₁ M H βN 113 = p₀.Kw := rfl
theorem hnV_kw1 (p₀ p₁ : KPN) (M H βN : ℕ) : hnV p₀ p₁ M H βN 114 = p₁.Kw := rfl

theorem hn_seq_inv {I : Input} {W : ℕ} {s t : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec I W (.seq s t) c c' k) :
    ∃ c₁ k₁ k₂, Exec I W s c c₁ k₁ ∧ Exec I W t c₁ c' k₂ ∧ k = k₁ + k₂ := by
  cases h with
  | seq e₁ e₂ => exact ⟨_, _, _, e₁, e₂, rfl⟩

/-- **The fixed node runs as the node of the instance** whose parameters it holds (see the
module docstring). -/
theorem nodeFix_exec {{I : Input}} {{W : ℕ}} {{p₀ p₁ : KPN}} {{M H βN : ℕ}} (h₀ : 1 ≤ p₀.Hc)
    (h₁ : 1 ≤ p₁.Hc) (hM : 2 ≤ M) {{c c' : Config}} {{t : ℕ}}
    (h : Exec I W (nodeProgNN p₀ p₁ M H βN) c c' t)
    (hv : ∀ j < 115, c.nreg (10400 + j) = hnV p₀ p₁ M H βN j) :
    ∃ t', Exec I W nodeFixT c c' t' ∧ t' ≤ t + 2 ∧ ∀ a, 10400 ≤ a → c'.nreg a = c.nreg a := by
  have pre : ∀ {{c₁ c₂ : Config}} {{k : ℕ}},
      Exec I W (.seq (ModNat.constsS 1000 M H βN) (ModNat.toNat 1000 2 (.seq bdSet bdryProg)))
        c₁ c₂ k → (∀ j < 115, c₁.nreg (10400 + j) = hnV p₀ p₁ M H βN j) →
      Exec I W (.seq hnX hnY) c₁ c₂ k ∧ ∀ a, 10400 ≤ a → c₂.nreg a = c₁.nreg a := by
    intro c₁ c₂ k e hv₁
    obtain ⟨c₃, k₁, k₂, e₁, e₂, rfl⟩ := hn_seq_inv e
    obtain ⟨f₁, k₁⟩ := hs_exec' (hnX_eq p₀ p₁ M H βN) e₁ hnX_ok hv₁
    obtain ⟨f₂, k₂⟩ := hs_exec' (hnY_eq p₀ p₁ M H βN) e₂ hnY_ok
      (fun j hj => by rw [k₁ _ (by omega)]; exact hv₁ j hj)
    exact ⟨.seq f₁ f₂, fun a ha => (k₂ a ha).trans (k₁ a ha)⟩
  by_cases hK : p₀.Kw ≤ p₁.Kw
  · rw [nodeProgNN_eqA p₀ p₁ M H βN hK h₀ h₁ hM] at h
    obtain ⟨c₁, t₁, t₂, e₁, e₂, rfl⟩ := hn_seq_inv h
    obtain ⟨c₂, t₃, t₄, e₃, e₄, rfl⟩ := hn_seq_inv e₂
    obtain ⟨f₁, k₁⟩ := pre e₁ hv
    have hv₁ := fun j (hj : j < 115) => (k₁ (10400 + j) (by omega)).trans (hv j hj)
    have a0 : c₁.nreg 10513 = p₀.Kw := hv₁ 113 (by omega)
    have a1 : c₁.nreg 10514 = p₁.Kw := hv₁ 114 (by omega)
    obtain ⟨f₃, k₃⟩ := hs_exec' (hnPA_eq p₀ p₁ M H βN) e₃ hnPA_ok hv₁
    obtain ⟨f₄, k₄⟩ := hs_exec' (hnZ_eq p₀ p₁ M H βN) e₄ hnZ_ok
      (fun j hj => by rw [k₃ _ (by omega)]; exact hv₁ j hj)
    have ht : ¬ c₁.nreg 10514 < c₁.nreg 10513 := by rw [a0, a1]; omega
    exact ⟨_, .seq f₁ (.seq (.ifLtN_false ht f₃) f₄), by omega,
      fun a ha => ((k₄ a ha).trans (k₃ a ha)).trans (k₁ a ha)⟩
  · rw [nodeProgNN_eqB p₀ p₁ M H βN (by omega) h₀ h₁ hM] at h
    obtain ⟨c₁, t₁, t₂, e₁, e₂, rfl⟩ := hn_seq_inv h
    obtain ⟨c₂, t₃, t₄, e₃, e₄, rfl⟩ := hn_seq_inv e₂
    obtain ⟨f₁, k₁⟩ := pre e₁ hv
    have hv₁ := fun j (hj : j < 115) => (k₁ (10400 + j) (by omega)).trans (hv j hj)
    have a0 : c₁.nreg 10513 = p₀.Kw := hv₁ 113 (by omega)
    have a1 : c₁.nreg 10514 = p₁.Kw := hv₁ 114 (by omega)
    obtain ⟨f₃, k₃⟩ := hs_exec' (hnPB_eq p₀ p₁ M H βN) e₃ hnPB_ok hv₁
    obtain ⟨f₄, k₄⟩ := hs_exec' (hnZ_eq p₀ p₁ M H βN) e₄ hnZ_ok
      (fun j hj => by rw [k₃ _ (by omega)]; exact hv₁ j hj)
    have ht : c₁.nreg 10514 < c₁.nreg 10513 := by rw [a0, a1]; omega
    exact ⟨_, .seq f₁ (.seq (.ifLtN_true ht f₃) f₄), by omega,
      fun a ha => ((k₄ a ha).trans (k₃ a ha)).trans (k₁ a ha)⟩

end NegSSSP

end PlanarFlow
