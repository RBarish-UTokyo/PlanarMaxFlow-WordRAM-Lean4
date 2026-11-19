module

public import PlanarFlow.NegSSSP.Enc.PrmWc
public import PlanarFlow.NegSSSP.Enc.HoistPrmN

/-!
# The primary values of the fixed node computed on the machine

`node_exec_fixedP` reads 21 primary values in the registers `10530 … 10558` (`HnPrim`). Here a
program computes them from **14 sizes of the node** in the registers `10610 … 10623` (`PnIn`):
the sizes `nD k nV nF` of the maps of the two one-face instances, the node's `m w b B`, and its
layout values `Y S`, and from the plain arrays of the two instances in memory:

* the layout: `Pb₀ = Y + 16 S`, `Pb₁ = Pb₀ + w`, `p₀.I0 = Pb₀ + 2 w`, `p₁.I0 = p₀.END`;
* `N₁ᵢ = isoN1 Aᵢ Nᵢ FNᵢ` (a chain of products);
* `Wcᵢ = 1 + Σ IS · LN` over the plain arrays at `pᵢ.I0` (`pwWc`, a loop; `pw_srcW`: this is
  `(srcW …).toNat`);
* `pᵢ.Lmax = feIsoB Aᵢ Nᵢ FNᵢ Wcᵢ` (the bound of the isolating lengths);
* `W' = pnW p₀ p₁ = p₁.END + Σᵢ (Lmaxᵢ + Infᵢ + 2 kcnHc … + 1)` (so that every word bound of the
  encoders, `Lmax ≤ W'`, `Inf + Lmax ≤ W'`, `2 kcnHc … + 1 ≤ W'`, `p₁.END ≤ W'`, holds);
* `H = nodeHN m b w B`, `M = 2 H + 1`.

**`pnProg_exec`**: within `pnCost p₀.nD p₁.nD = 9 (p₀.nD + p₁.nD) + 701` steps, `HnPrim` for those
values; registers outside `[10530, 10700)`, the memory, reals and output kept. Word bound:
`pnW p₀ p₁ ≤ W`, `2 nodeHN m b w B + 1 ≤ W`, `isoN1 … ≤ W`, `9600 ≤ W`; `1 ≤ b`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### The values -/

/-- The constants of an encoder from its sizes, its base and its weight bound. -/
def pnP (nD k nV nF I0 Wc : ℕ) : FeP :=
  ⟨nD, k, nV, nF, I0, feIsoB (nV + 2 * k) (nD + 8 * k) (nF + 2 * k) Wc⟩

/-- The word bound `W'` of the two encoders. -/
def pnW (p₀ p₁ : FeP) : ℕ :=
  p₁.END + p₀.Lmax + p₁.Lmax + p₀.Inf + p₁.Inf +
    (2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1) +
    (2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1)

/-- The 14 sizes in the registers. -/
structure PnIn (f : ℕ → ℕ) (p₀ p₁ : FeP) (m w b B Y S : ℕ) : Prop where
  a0 : f 10610 = p₀.nD
  a1 : f 10611 = p₀.k
  a2 : f 10612 = p₀.nV
  a3 : f 10613 = p₀.nF
  b0 : f 10614 = p₁.nD
  b1 : f 10615 = p₁.k
  b2 : f 10616 = p₁.nV
  b3 : f 10617 = p₁.nF
  m : f 10618 = m
  w : f 10619 = w
  b : f 10620 = b
  B : f 10621 = B
  Y : f 10622 = Y
  S : f 10623 = S

lemma pn_end (p : FeP) :
    p.END = 37 + 85 * p.nD + 944 * p.k + 69 * p.nV + 81 * p.nF + p.I0 + p.k * p.k := by
  simp only [FeP.END, FeP.OS, FeP.ZT, FeP.ZS, FeP.DB, FeP.RK, FeP.ISO, FeP.MK, FeP.RD, FeP.ZI,
    FeP.WW, FeP.ZC, FeP.O1, FeP.ZV, FeP.ONE, FeP.SL, FeP.Kw, FeP.Bw, FeP.β, FeP.NN, FeP.AE,
    FeP.A, FeP.N, FeP.FN, Klein.kBL, Klein.aOUT]
  omega

/-! ### The two chains -/

/-- **Chain 1**: copies of the sizes, the layout, `Nᵢ Aᵢ FNᵢ`, `N₁ᵢ`, `H`, `M`. -/
def pnL1 : List PcStep :=
  [(10530, [(1, .v 10610)], 0), (10531, [(1, .v 10611)], 0), (10532, [(1, .v 10612)], 0),
    (10533, [(1, .v 10613)], 0),
    (10540, [(1, .v 10614)], 0), (10541, [(1, .v 10615)], 0), (10542, [(1, .v 10616)], 0),
    (10543, [(1, .v 10617)], 0),
    (10550, [(1, .v 10622), (16, .v 10623)], 0),
    (10551, [(1, .v 10622), (16, .v 10623), (1, .v 10619)], 0),
    (10534, [(1, .v 10622), (16, .v 10623), (2, .v 10619)], 0),
    (10544, [(37, .one), (85, .v 10610), (944, .v 10611), (69, .v 10612), (81, .v 10613),
      (1, .v 10534), (1, .vv 10611 10611)], 0),
    (10560, [(3, .v 10610), (1, .v 10534)], 0), (10561, [(4, .v 10610), (1, .v 10534)], 0),
    (10562, [(3, .v 10614), (1, .v 10544)], 0), (10563, [(4, .v 10614), (1, .v 10544)], 0),
    (10630, [(1, .v 10610), (8, .v 10611)], 0), (10631, [(1, .v 10612), (2, .v 10611)], 0),
    (10632, [(1, .v 10613), (2, .v 10611)], 0),
    (10633, [(1, .vv 10631 10630), (1, .one)], 0), (10634, [(2, .vv 10632 10631), (1, .one)], 0),
    (10635, [(1, .vv 10633 10634)], 0), (10555, [(1, .vv 10635 10631), (1, .v 10635)], 0),
    (10640, [(1, .v 10614), (8, .v 10615)], 0), (10641, [(1, .v 10616), (2, .v 10615)], 0),
    (10642, [(1, .v 10617), (2, .v 10615)], 0),
    (10643, [(1, .vv 10641 10640), (1, .one)], 0), (10644, [(2, .vv 10642 10641), (1, .one)], 0),
    (10645, [(1, .vv 10643 10644)], 0), (10556, [(1, .vv 10645 10641), (1, .v 10645)], 0),
    (10650, [(3, .vv 10618 10621), (2, .v 10621)], 0),
    (10651, [(1, .vv 10620 10650)], 0),
    (10652, [(2, .vv 10651 10620), (1, .v 10651)], 0),
    (10653, [(4, .vv 10652 10620), (4, .v 10652)], 0),
    (10654, [(1, .v 10653), (1, .vv 10620 10651), (8, .vv 10620 10620), (16, .v 10620),
      (13, .one)], 0),
    (10655, [(4, .vv 10620 10654), (2, .v 10654)], 0),
    (10656, [(1, .vv 10620 10655), (1, .v 10655)], 0),
    (10657, [(2, .vv 10620 10656), (3, .v 10656)], 0),
    (10658, [(1, .vv 10619 10657), (3, .v 10657)], 0),
    (10659, [(1, .vv 10620 10658), (1, .v 10658)], 0),
    (10660, [(2, .vv 10620 10659), (3, .v 10659)], 0),
    (10661, [(1, .vv 10619 10660), (3, .v 10660)], 0),
    (10554, [(2, .v 10621), (512, .v 10661)], 0),
    (10553, [(2, .v 10554), (1, .one)], 0)]

/-- **Chain 2**: `Lmaxᵢ`, the factors of `kcnHc`, `W'`. -/
def pnL2 : List PcStep :=
  [(10535, [(1, .vv 10555 10557), (1, .v 10635), (2, .vv 10633 10632), (1, .v 10630)], 0),
    (10545, [(1, .vv 10556 10558), (1, .v 10645), (2, .vv 10643 10642), (1, .v 10640)], 0),
    (10670, [(1, .vv 10630 10535), (1, .one)], 0),
    (10671, [(1, .vv 10632 10670), (1, .v 10670)], 0),
    (10672, [(1, .vv 10631 10671), (1, .v 10671)], 0),
    (10673, [(1, .vv 10631 10672), (1, .v 10672)], 0),
    (10674, [(1, .vv 10611 10673), (1, .v 10673)], 0),
    (10680, [(1, .vv 10640 10545), (1, .one)], 0),
    (10681, [(1, .vv 10642 10680), (1, .v 10680)], 0),
    (10682, [(1, .vv 10641 10681), (1, .v 10681)], 0),
    (10683, [(1, .vv 10641 10682), (1, .v 10682)], 0),
    (10684, [(1, .vv 10615 10683), (1, .v 10683)], 0),
    (10552, [(41, .one), (85, .v 10614), (944, .v 10615), (69, .v 10616), (81, .v 10617),
      (1, .v 10544), (1, .vv 10615 10615), (1, .v 10535), (1, .v 10545),
      (1, .vv 10631 10535), (1, .vv 10641 10545), (9600, .v 10674), (9600, .v 10684)], 0)]

set_option maxRecDepth 100000 in
theorem pnL1_wf : pcWF 10600 9600 pnL1 = true := by kernel_rfl

set_option maxRecDepth 100000 in
theorem pnL2_wf : pcWF 10600 9600 pnL2 = true := by kernel_rfl

/-- **The program of the primary values.** -/
def pnProg : Stmt :=
  .seq (pcProg 10600 pnL1) <| .seq (pwWc 10557 10560 10561 10530) <|
    .seq (pwWc 10558 10562 10563 10540) (pcProg 10600 pnL2)

theorem pnProg_natOnly : Klein.natOnly pnProg = true := by kernel_rfl

/-- Its number of steps. -/
def pnCost (n₀ n₁ : ℕ) : ℕ := pcCost pnL1 + (9 * n₀ + 9) + (9 * n₁ + 9) + pcCost pnL2

theorem pnCost_eq (n₀ n₁ : ℕ) : pnCost n₀ n₁ = 9 * (n₀ + n₁) + 701 := by
  have h1 : pcCost pnL1 = 480 := by kernel_rfl
  have h2 : pcCost pnL2 = 203 := by kernel_rfl
  unfold pnCost; rw [h1, h2]; ring

/-- With all constants `0`, a solution has `g dst = Σ c · m (g)`. -/
theorem pcSol_d0 {l : List PcStep} (hd : l.all (fun s => s.2.2 == 0) = true) {g : ℕ → ℕ}
    (h : PcSol l g) : ∀ s ∈ l, hpSum g s.2.1 = g s.1 := by
  intro s hs
  have h0 : s.2.2 = 0 := by
    simp only [List.all_eq_true, beq_iff_eq] at hd; exact hd s hs
  rw [h s hs, h0, Nat.sub_zero]

/-! ### Chain 1 -/

set_option maxHeartbeats 1000000 in
/-- The equations of chain 1. -/
theorem pnL1_eqs {g : ℕ → ℕ} (h : PcSol pnL1 g) :
    g 10530 = g 10610 ∧ g 10531 = g 10611 ∧ g 10532 = g 10612 ∧ g 10533 = g 10613 ∧
    g 10540 = g 10614 ∧ g 10541 = g 10615 ∧ g 10542 = g 10616 ∧ g 10543 = g 10617 ∧
    g 10550 = g 10622 + 16 * g 10623 ∧ g 10551 = g 10622 + 16 * g 10623 + g 10619 ∧
    g 10534 = g 10622 + 16 * g 10623 + 2 * g 10619 ∧
    g 10544 = 37 + 85 * g 10610 + 944 * g 10611 + 69 * g 10612 + 81 * g 10613 + g 10534 +
      g 10611 * g 10611 ∧
    g 10560 = 3 * g 10610 + g 10534 ∧ g 10561 = 4 * g 10610 + g 10534 ∧
    g 10562 = 3 * g 10614 + g 10544 ∧ g 10563 = 4 * g 10614 + g 10544 ∧
    g 10630 = g 10610 + 8 * g 10611 ∧ g 10631 = g 10612 + 2 * g 10611 ∧
    g 10632 = g 10613 + 2 * g 10611 ∧
    g 10633 = g 10631 * g 10630 + 1 ∧ g 10634 = 2 * (g 10632 * g 10631) + 1 ∧
    g 10635 = g 10633 * g 10634 ∧ g 10555 = g 10635 * g 10631 + g 10635 ∧
    g 10640 = g 10614 + 8 * g 10615 ∧ g 10641 = g 10616 + 2 * g 10615 ∧
    g 10642 = g 10617 + 2 * g 10615 ∧
    g 10643 = g 10641 * g 10640 + 1 ∧ g 10644 = 2 * (g 10642 * g 10641) + 1 ∧
    g 10645 = g 10643 * g 10644 ∧ g 10556 = g 10645 * g 10641 + g 10645 ∧
    g 10650 = 3 * (g 10618 * g 10621) + 2 * g 10621 ∧ g 10651 = g 10620 * g 10650 ∧
    g 10652 = 2 * (g 10651 * g 10620) + g 10651 ∧
    g 10653 = 4 * (g 10652 * g 10620) + 4 * g 10652 ∧
    g 10654 = g 10653 + g 10620 * g 10651 + 8 * (g 10620 * g 10620) + 16 * g 10620 + 13 ∧
    g 10655 = 4 * (g 10620 * g 10654) + 2 * g 10654 ∧
    g 10656 = g 10620 * g 10655 + g 10655 ∧ g 10657 = 2 * (g 10620 * g 10656) + 3 * g 10656 ∧
    g 10658 = g 10619 * g 10657 + 3 * g 10657 ∧ g 10659 = g 10620 * g 10658 + g 10658 ∧
    g 10660 = 2 * (g 10620 * g 10659) + 3 * g 10659 ∧
    g 10661 = g 10619 * g 10660 + 3 * g 10660 ∧
    g 10554 = 2 * g 10621 + 512 * g 10661 ∧ g 10553 = 2 * g 10554 + 1 := by
  simp only [PcSol, pnL1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.sub_zero, one_mul, add_zero] at h
  omega

/-- The values of chain 1. -/
structure Pn1V (g : ℕ → ℕ) (p₀ p₁ : FeP) (m w b B Y S : ℕ) : Prop where
  nD₀ : g 10530 = p₀.nD
  k₀ : g 10531 = p₀.k
  nV₀ : g 10532 = p₀.nV
  nF₀ : g 10533 = p₀.nF
  nD₁ : g 10540 = p₁.nD
  k₁ : g 10541 = p₁.k
  nV₁ : g 10542 = p₁.nV
  nF₁ : g 10543 = p₁.nF
  Pb₀ : g 10550 = Y + 16 * S
  Pb₁ : g 10551 = Y + 16 * S + w
  I0₀ : g 10534 = Y + 16 * S + 2 * w
  I0₁ : g 10544 = 37 + 85 * p₀.nD + 944 * p₀.k + 69 * p₀.nV + 81 * p₀.nF +
    (Y + 16 * S + 2 * w) + p₀.k * p₀.k
  IS₀ : g 10560 = Y + 16 * S + 2 * w + 3 * p₀.nD
  LN₀ : g 10561 = Y + 16 * S + 2 * w + 4 * p₀.nD
  IS₁ : g 10562 = g 10544 + 3 * p₁.nD
  LN₁ : g 10563 = g 10544 + 4 * p₁.nD
  N₀ : g 10630 = p₀.N
  A₀ : g 10631 = p₀.A
  FN₀ : g 10632 = p₀.FN
  t1₀ : g 10633 = MSSP.isoN3 p₀.A p₀.N
  t3₀ : g 10635 = MSSP.isoN2 p₀.A p₀.N p₀.FN
  N1₀ : g 10555 = MSSP.isoN1 p₀.A p₀.N p₀.FN
  N₁ : g 10640 = p₁.N
  A₁ : g 10641 = p₁.A
  FN₁ : g 10642 = p₁.FN
  t1₁ : g 10643 = MSSP.isoN3 p₁.A p₁.N
  t3₁ : g 10645 = MSSP.isoN2 p₁.A p₁.N p₁.FN
  N1₁ : g 10556 = MSSP.isoN1 p₁.A p₁.N p₁.FN
  H : g 10554 = nodeHN m b w B
  M : g 10553 = 2 * nodeHN m b w B + 1

theorem pn_bfB {b L x1 x2 x3 x4 : ℕ} (h1 : x1 = b * L) (h2 : x2 = 2 * (x1 * b) + x1)
    (h3 : x3 = 4 * (x2 * b) + 4 * x2) (h4 : x4 = x3 + b * x1 + 8 * (b * b) + 16 * b + 13) :
    x4 = bfB b L := by
  subst h1 h2 h3 h4
  unfold bfB Monge.bfXm Monge.bfΔ bfWP; ring

theorem pn_partB {b w X y1 y2 y3 : ℕ} (h1 : y1 = b * X + X) (h2 : y2 = 2 * (b * y1) + 3 * y1)
    (h3 : y3 = w * y2 + 3 * y2) : y3 = partB b w X := by
  subst h1 h2 h3
  unfold partB; ring

/-- **The values of chain 1.** -/
theorem pn1_val {g : ℕ → ℕ} {p₀ p₁ : FeP} {m w b B Y S : ℕ} (hin : PnIn g p₀ p₁ m w b B Y S)
    (h : PcSol pnL1 g) : Pn1V g p₀ p₁ m w b B Y S := by
  obtain ⟨e30, e31, e32, e33, e40, e41, e42, e43, e50, e51, e34, e44, e60, e61, e62, e63,
    f30, f31, f32, f33, f34, f35, f55, f40, f41, f42, f43, f44, f45, f56,
    h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h54', h53'⟩ := pnL1_eqs h
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, hm, hw, hb, hB, hY, hS⟩ := hin
  have hR := pn_bfB h51 h52 h53 h54
  have hX1 := pn_partB h56 h57 h58
  have hX2 := pn_partB h59 h60 h61
  refine ⟨by rw [e30, a0], by rw [e31, a1], by rw [e32, a2], by rw [e33, a3], by rw [e40, b0],
    by rw [e41, b1], by rw [e42, b2], by rw [e43, b3], by rw [e50, hY, hS],
    by rw [e51, hY, hS, hw], by rw [e34, hY, hS, hw], ?_, ?_, ?_, by rw [e62, b0]; omega,
    by rw [e63, b0]; omega, by rw [f30, a0, a1]; rfl, by rw [f31, a2, a1]; rfl,
    by rw [f32, a3, a1]; rfl, ?_, ?_, ?_, by rw [f40, b0, b1]; rfl, by rw [f41, b2, b1]; rfl,
    by rw [f42, b3, b1]; rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e44, e34, a0, a1, a2, a3, hY, hS, hw]
  · rw [e60, e34, a0, hY, hS, hw]; omega
  · rw [e61, e34, a0, hY, hS, hw]; omega
  · rw [f33, f31, f30, a0, a1, a2]; simp only [MSSP.isoN3, FeP.A, FeP.N]
  · rw [f35, f33, f34, f31, f30, f32, a0, a1, a2, a3]
    simp only [MSSP.isoN2, MSSP.isoN3, FeP.A, FeP.N, FeP.FN]; ring_nf
  · rw [f55, f35, f33, f34, f31, f30, f32, a0, a1, a2, a3]
    simp only [MSSP.isoN1, MSSP.isoN2, MSSP.isoN3, FeP.A, FeP.N, FeP.FN]; ring
  · rw [f43, f41, f40, b0, b1, b2]; simp only [MSSP.isoN3, FeP.A, FeP.N]
  · rw [f45, f43, f44, f41, f40, f42, b0, b1, b2, b3]
    simp only [MSSP.isoN2, MSSP.isoN3, FeP.A, FeP.N, FeP.FN]; ring_nf
  · rw [f56, f45, f43, f44, f41, f40, f42, b0, b1, b2, b3]
    simp only [MSSP.isoN1, MSSP.isoN2, MSSP.isoN3, FeP.A, FeP.N, FeP.FN]; ring
  · rw [h54', hX2, hX1, h55, hR, h50, hb, hw, hm, hB]
    unfold nodeHN restB dijB; ring_nf
  · rw [h53', h54', hX2, hX1, h55, hR, h50, hb, hw, hm, hB]
    unfold nodeHN restB dijB; ring_nf

/-- `Wc ≤ feIsoB … Wc`. -/
theorem pn_wc_le (n m B Wc : ℕ) : Wc ≤ feIsoB n m B Wc := by
  have h : 0 < MSSP.isoN1 n m B := by
    simp only [MSSP.isoN1, MSSP.isoN2, MSSP.isoN3]; positivity
  unfold feIsoB
  have := Nat.le_mul_of_pos_left Wc h
  omega

theorem pnL1_dsts : ∀ r ∈ pcDsts pnL1, 10530 ≤ r ∧ r < 10690 ∧ r ≠ 10557 ∧ r ≠ 10558 ∧
    (r < 10610 ∨ 10623 < r) ∧ r ≠ 10600 ∧ r ≠ 10601 := by
  intro r hr
  simp only [pcDsts, pnL1, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  omega

theorem pnL2_dsts : ∀ r ∈ pcDsts pnL2, r = 10535 ∨ r = 10545 ∨ r = 10552 ∨
    (10670 ≤ r ∧ r ≤ 10684) := by
  intro r hr
  simp only [pcDsts, pnL2, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  omega

theorem pnL1_d0 : pnL1.all (fun s => s.2.2 == 0) = true := by kernel_rfl
theorem pnL2_d0 : pnL2.all (fun s => s.2.2 == 0) = true := by kernel_rfl

set_option maxHeartbeats 4000000 in
/-- **The words of chain 1 are bounded.** -/
theorem pn1_le {g : ℕ → ℕ} {p₀ p₁ : FeP} {m w b B Y S : ℕ} (hin : PnIn g p₀ p₁ m w b B Y S)
    (h : PcSol pnL1 g) (hI0₀ : p₀.I0 = Y + 16 * S + 2 * w) (hI0₁ : p₁.I0 = p₀.END)
    (hb : 1 ≤ b) (hW1 : pnW p₀ p₁ ≤ W) (hW2 : 2 * nodeHN m b w B + 1 ≤ W)
    (hW3 : MSSP.isoN1 p₀.A p₀.N p₀.FN ≤ W) (hW4 : MSSP.isoN1 p₁.A p₁.N p₁.FN ≤ W) :
    ∀ s ∈ pnL1, hpSum g s.2.1 ≤ W := by
  have hv := pn1_val hin h
  have hd := pcSol_d0 pnL1_d0 h
  obtain ⟨e30, e31, e32, e33, e40, e41, e42, e43, e50, e51, e34, e44, e60, e61, e62, e63,
    f30, f31, f32, f33, f34, f35, f55, f40, f41, f42, f43, f44, f45, f56,
    h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h54', h53'⟩ := pnL1_eqs h
  have E₀ := pn_end p₀
  have E₁ := pn_end p₁
  have hEW : p₁.END ≤ W := by unfold pnW at hW1; omega
  have hEI : g 10544 = p₁.I0 := by rw [hI0₁, hv.I0₁, E₀, hI0₀]
  -- the products
  have t1 : g 10633 ≤ g 10635 := by
    rw [f35]; exact Nat.le_mul_of_pos_right _ (by rw [f34]; omega)
  have t2 : g 10634 ≤ g 10635 := by
    rw [f35]; exact Nat.le_mul_of_pos_left _ (by rw [f33]; omega)
  have t3 : g 10643 ≤ g 10645 := by
    rw [f45]; exact Nat.le_mul_of_pos_right _ (by rw [f44]; omega)
  have t4 : g 10644 ≤ g 10645 := by
    rw [f45]; exact Nat.le_mul_of_pos_left _ (by rw [f43]; omega)
  have t5 : g 10650 ≤ g 10651 := by
    rw [h51]; exact Nat.le_mul_of_pos_left _ (by rw [hin.b]; omega)
  have hH : g 10553 ≤ W := by rw [hv.M]; exact hW2
  have hN1₀ : g 10555 ≤ W := by rw [hv.N1₀]; exact hW3
  have hN1₁ : g 10556 ≤ W := by rw [hv.N1₁]; exact hW4
  have hA : g 10631 ≤ W ∧ g 10630 ≤ W ∧ g 10632 ≤ W ∧ g 10641 ≤ W ∧ g 10640 ≤ W ∧
      g 10642 ≤ W := by
    rw [hv.A₀, hv.N₀, hv.FN₀, hv.A₁, hv.N₁, hv.FN₁]
    simp only [FeP.A, FeP.N, FeP.FN]
    omega
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, hm', hw', hb', hB', hY, hS⟩ := hin
  clear hv
  intro s hs
  rw [hd s hs]
  simp only [pnL1, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals dsimp only
  all_goals omega

/-! ### Chain 2 -/

set_option maxHeartbeats 1000000 in
/-- The equations of chain 2. -/
theorem pnL2_eqs {g : ℕ → ℕ} (h : PcSol pnL2 g) :
    g 10535 = g 10555 * g 10557 + g 10635 + 2 * (g 10633 * g 10632) + g 10630 ∧
    g 10545 = g 10556 * g 10558 + g 10645 + 2 * (g 10643 * g 10642) + g 10640 ∧
    g 10670 = g 10630 * g 10535 + 1 ∧ g 10671 = g 10632 * g 10670 + g 10670 ∧
    g 10672 = g 10631 * g 10671 + g 10671 ∧ g 10673 = g 10631 * g 10672 + g 10672 ∧
    g 10674 = g 10611 * g 10673 + g 10673 ∧
    g 10680 = g 10640 * g 10545 + 1 ∧ g 10681 = g 10642 * g 10680 + g 10680 ∧
    g 10682 = g 10641 * g 10681 + g 10681 ∧ g 10683 = g 10641 * g 10682 + g 10682 ∧
    g 10684 = g 10615 * g 10683 + g 10683 ∧
    g 10552 = 41 + 85 * g 10614 + 944 * g 10615 + 69 * g 10616 + 81 * g 10617 + g 10544 +
      g 10615 * g 10615 + g 10535 + g 10545 + g 10631 * g 10535 + g 10641 * g 10545 +
      9600 * g 10674 + 9600 * g 10684 := by
  simp only [PcSol, pnL2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.sub_zero, one_mul, mul_one, add_zero] at h
  omega

/-- What chain 2 reads from chain 1 and the two loops. -/
structure Pn2In (g : ℕ → ℕ) (p₀ p₁ : FeP) (Wc₀ Wc₁ : ℕ) : Prop where
  N₀ : g 10630 = p₀.N
  A₀ : g 10631 = p₀.A
  FN₀ : g 10632 = p₀.FN
  t1₀ : g 10633 = MSSP.isoN3 p₀.A p₀.N
  t3₀ : g 10635 = MSSP.isoN2 p₀.A p₀.N p₀.FN
  N1₀ : g 10555 = MSSP.isoN1 p₀.A p₀.N p₀.FN
  Wc₀ : g 10557 = Wc₀
  k₀ : g 10611 = p₀.k
  N₁ : g 10640 = p₁.N
  A₁ : g 10641 = p₁.A
  FN₁ : g 10642 = p₁.FN
  t1₁ : g 10643 = MSSP.isoN3 p₁.A p₁.N
  t3₁ : g 10645 = MSSP.isoN2 p₁.A p₁.N p₁.FN
  N1₁ : g 10556 = MSSP.isoN1 p₁.A p₁.N p₁.FN
  Wc₁ : g 10558 = Wc₁
  k₁ : g 10615 = p₁.k
  nD₁ : g 10614 = p₁.nD
  nV₁ : g 10616 = p₁.nV
  nF₁ : g 10617 = p₁.nF
  I0₁ : g 10544 = p₁.I0

theorem pn_kcn {N L FN A k q1 q2 q3 q4 q5 : ℕ} (h1 : q1 = N * L + 1) (h2 : q2 = FN * q1 + q1)
    (h3 : q3 = A * q2 + q2) (h4 : q4 = A * q3 + q3) (h5 : q5 = k * q4 + q4) :
    4800 * q5 = kcnHc A FN (N * L) k := by
  subst h1 h2 h3 h4 h5; unfold kcnHc; ring

theorem pn_lmax {A N FN Wc t1 t3 N1 x : ℕ} (h1 : t1 = MSSP.isoN3 A N)
    (h3 : t3 = MSSP.isoN2 A N FN) (hN : N1 = MSSP.isoN1 A N FN)
    (hx : x = N1 * Wc + t3 + 2 * (t1 * FN) + N) : x = feIsoB A N FN Wc := by
  subst h1 h3 hN hx; unfold feIsoB; ring

set_option maxHeartbeats 4000000 in
/-- **The values and the word bounds of chain 2.** -/
theorem pn2_val {g : ℕ → ℕ} {p₀ p₁ : FeP} {Wc₀ Wc₁ : ℕ} (hin : Pn2In g p₀ p₁ Wc₀ Wc₁)
    (h : PcSol pnL2 g) (hL₀ : p₀.Lmax = feIsoB p₀.A p₀.N p₀.FN Wc₀)
    (hL₁ : p₁.Lmax = feIsoB p₁.A p₁.N p₁.FN Wc₁) (hW1 : pnW p₀ p₁ ≤ W) :
    g 10535 = p₀.Lmax ∧ g 10545 = p₁.Lmax ∧ g 10552 = pnW p₀ p₁ ∧
      ∀ s ∈ pnL2, hpSum g s.2.1 ≤ W := by
  obtain ⟨e35, e45, q1, q2, q3, q4, q5, r1, r2, r3, r4, r5, e52⟩ := pnL2_eqs h
  have L₀ : g 10535 = p₀.Lmax := by
    rw [hL₀]; exact pn_lmax hin.t1₀ hin.t3₀ hin.N1₀ (by rw [e35, hin.Wc₀, hin.FN₀, hin.N₀])
  have L₁ : g 10545 = p₁.Lmax := by
    rw [hL₁]; exact pn_lmax hin.t1₁ hin.t3₁ hin.N1₁ (by rw [e45, hin.Wc₁, hin.FN₁, hin.N₁])
  have K₀ := pn_kcn q1 q2 q3 q4 q5
  have K₁ := pn_kcn r1 r2 r3 r4 r5
  rw [hin.N₀, L₀, hin.FN₀, hin.A₀, hin.k₀] at K₀
  rw [hin.N₁, L₁, hin.FN₁, hin.A₁, hin.k₁] at K₁
  have E₁ := pn_end p₁
  have hP : g 10552 = pnW p₀ p₁ := by
    rw [e52, L₀, L₁, hin.nD₁, hin.k₁, hin.nV₁, hin.nF₁, hin.I0₁, hin.A₀, hin.A₁]
    unfold pnW FeP.Inf
    omega
  refine ⟨L₀, L₁, hP, ?_⟩
  have hd := pcSol_d0 pnL2_d0 h
  have hPW : g 10552 ≤ W := by rw [hP]; exact hW1
  have hW' : p₀.Lmax + p₁.Lmax + 2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k +
      2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k ≤ W := by
    unfold pnW at hW1; omega
  clear hP E₁ hin hL₀ hL₁
  intro s hs
  rw [hd s hs]
  simp only [pnL2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only
  all_goals omega

/-! ### The program -/

set_option maxHeartbeats 4000000 in
/-- **The primary values of the fixed node on the machine** (see the module docstring). -/
theorem pnProg_exec {p₀ p₁ : FeP} {m w b B Y S : ℕ} (c : Config) (hc : WordsBounded W c)
    (hin : PnIn c.nreg p₀ p₁ m w b B Y S) (hI0₀ : p₀.I0 = Y + 16 * S + 2 * w)
    (hI0₁ : p₁.I0 = p₀.END)
    (hL₀ : p₀.Lmax = feIsoB p₀.A p₀.N p₀.FN
      (1 + pwS c.nmem (p₀.I0 + 3 * p₀.nD) (p₀.I0 + 4 * p₀.nD) p₀.nD))
    (hL₁ : p₁.Lmax = feIsoB p₁.A p₁.N p₁.FN
      (1 + pwS c.nmem (p₁.I0 + 3 * p₁.nD) (p₁.I0 + 4 * p₁.nD) p₁.nD))
    (hb : 1 ≤ b) (hW1 : pnW p₀ p₁ ≤ W) (hW2 : 2 * nodeHN m b w B + 1 ≤ W)
    (hW3 : MSSP.isoN1 p₀.A p₀.N p₀.FN ≤ W) (hW4 : MSSP.isoN1 p₁.A p₁.N p₁.FN ≤ W)
    (h9600 : 9600 ≤ W) :
    ∃ c' t, Exec P W pnProg c c' t ∧ t ≤ pnCost p₀.nD p₁.nD ∧
      HnPrim c'.nreg p₀ p₁ (Y + 16 * S) (Y + 16 * S + w) (pnW p₀ p₁) (2 * nodeHN m b w B + 1)
        (nodeHN m b w B) (MSSP.isoN1 p₀.A p₀.N p₀.FN) (MSSP.isoN1 p₁.A p₁.N p₁.FN)
        (1 + pwS c.nmem (p₀.I0 + 3 * p₀.nD) (p₀.I0 + 4 * p₀.nD) p₀.nD)
        (1 + pwS c.nmem (p₁.I0 + 3 * p₁.nD) (p₁.I0 + 4 * p₁.nD) p₁.nD) ∧
      (∀ r, (r < 10530 ∨ 10700 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set Wc₀ := 1 + pwS c.nmem (p₀.I0 + 3 * p₀.nD) (p₀.I0 + 4 * p₀.nD) p₀.nD with hWc₀
  set Wc₁ := 1 + pwS c.nmem (p₁.I0 + 3 * p₁.nD) (p₁.I0 + 4 * p₁.nD) p₁.nD with hWc₁
  have E₀ := pn_end p₀
  have E₁ := pn_end p₁
  have hEW : p₁.END ≤ W := by unfold pnW at hW1; omega
  have hLW : p₀.Lmax ≤ W ∧ p₁.Lmax ≤ W := by unfold pnW at hW1; omega
  have hWc : Wc₀ ≤ W ∧ Wc₁ ≤ W := by
    have := pn_wc_le p₀.A p₀.N p₀.FN Wc₀
    have := pn_wc_le p₁.A p₁.N p₁.FN Wc₁
    omega
  -- chain 1
  have hin1 : ∀ g : ℕ → ℕ, (∀ r, r ∉ pcDsts pnL1 → r ≠ 10600 → r ≠ 10600 + 1 →
      g r = c.nreg r) → PnIn g p₀ p₁ m w b B Y S := fun g hg => by
    have k : ∀ r, 10610 ≤ r → r ≤ 10623 → g r = c.nreg r := fun r h1 h2 =>
      hg r (fun hr => by have := pnL1_dsts r hr; omega) (by omega) (by omega)
    obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, hm, hw, hb', hB, hY, hS⟩ := hin
    exact ⟨(k _ (by omega) (by omega)).trans a0, (k _ (by omega) (by omega)).trans a1,
      (k _ (by omega) (by omega)).trans a2, (k _ (by omega) (by omega)).trans a3,
      (k _ (by omega) (by omega)).trans b0, (k _ (by omega) (by omega)).trans b1,
      (k _ (by omega) (by omega)).trans b2, (k _ (by omega) (by omega)).trans b3,
      (k _ (by omega) (by omega)).trans hm, (k _ (by omega) (by omega)).trans hw,
      (k _ (by omega) (by omega)).trans hb', (k _ (by omega) (by omega)).trans hB,
      (k _ (by omega) (by omega)).trans hY, (k _ (by omega) (by omega)).trans hS⟩
  obtain ⟨c₁, e₁, s₁, f₁, m₁, r₁, rm₁, o₁⟩ := pcProg_exec (I := P) pnL1 pnL1_wf h9600 c hc
    (fun g hg hs => pn1_le (hin1 g hg) hs hI0₀ hI0₁ hb hW1 hW2 hW3 hW4)
  have v₁ := pn1_val (hin1 c₁.nreg f₁) s₁
  have hEI : c₁.nreg 10544 = p₁.I0 := by rw [hI0₁, v₁.I0₁, E₀, hI0₀]
  -- the two loops
  obtain ⟨c₂, k₂, e₂, hk₂, w₂, f₂, m₂, r₂, rm₂, o₂⟩ := pwWc_exec (P := P) (dst := 10557) (rIS := 10560) (rLN := 10561) (rN := 10530)
    (a := p₀.I0 + 3 * p₀.nD) (b := p₀.I0 + 4 * p₀.nD) (n := p₀.nD)
    (by omega) (by omega) (by omega) c₁ e₁.wb_right
    (by rw [v₁.IS₀, hI0₀]) (by rw [v₁.LN₀, hI0₀]) v₁.nD₀ (by omega) (by omega)
    (by rw [m₁]; exact hWc.1)
  obtain ⟨c₃, k₃, e₃, hk₃, w₃, f₃, m₃, r₃, rm₃, o₃⟩ := pwWc_exec (P := P) (dst := 10558) (rIS := 10562) (rLN := 10563) (rN := 10540)
    (a := p₁.I0 + 3 * p₁.nD) (b := p₁.I0 + 4 * p₁.nD) (n := p₁.nD)
    (by omega) (by omega) (by omega) c₂ e₂.wb_right
    (by rw [f₂ _ (by omega) (by omega), v₁.IS₁, hEI])
    (by rw [f₂ _ (by omega) (by omega), v₁.LN₁, hEI])
    (by rw [f₂ _ (by omega) (by omega), v₁.nD₁]) (by omega) (by omega)
    (by rw [m₂, m₁]; exact hWc.2)
  have k₃ : ∀ r, r ≠ 10557 → r ≠ 10558 → (r < 10690 ∨ 10697 < r) → c₃.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => by rw [f₃ r h2 h3, f₂ r h1 h3]
  have hW₂ : c₃.nreg 10557 = Wc₀ := by rw [f₃ _ (by omega) (by omega), w₂, m₁]
  have hW₃ : c₃.nreg 10558 = Wc₁ := by rw [w₃, m₂, m₁]
  -- chain 2
  have hin2 : ∀ g : ℕ → ℕ, (∀ r, r ∉ pcDsts pnL2 → r ≠ 10600 → r ≠ 10600 + 1 →
      g r = c₃.nreg r) → Pn2In g p₀ p₁ Wc₀ Wc₁ := fun g hg => by
    have k : ∀ r, r ≠ 10535 → r ≠ 10545 → r ≠ 10552 → (r < 10670 ∨ 10684 < r) →
        r ≠ 10600 → r ≠ 10601 → g r = c₃.nreg r := fun r h1 h2 h3 h4 h5 h6 =>
      hg r (fun hr => by have := pnL2_dsts r hr; omega) h5 h6
    have kk : ∀ r, r ≠ 10535 → r ≠ 10545 → r ≠ 10552 → (r < 10670 ∨ 10684 < r) →
        r ≠ 10600 → r ≠ 10601 → r ≠ 10557 → r ≠ 10558 → (r < 10690 ∨ 10697 < r) →
        g r = c₁.nreg r := fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
      (k r h1 h2 h3 h4 h5 h6).trans (k₃ r h7 h8 h9)
    have hi := hin1 c₁.nreg f₁
    exact ⟨(kk 10630 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans v₁.N₀,
      (kk 10631 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans v₁.A₀,
      (kk 10632 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans v₁.FN₀,
      (kk 10633 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans v₁.t1₀,
      (kk 10635 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans v₁.t3₀,
      (kk 10555 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans v₁.N1₀,
      (k 10557 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hW₂,
      (kk 10611 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans hi.a1,
      (kk 10640 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans v₁.N₁,
      (kk 10641 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans v₁.A₁,
      (kk 10642 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans v₁.FN₁,
      (kk 10643 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans v₁.t1₁,
      (kk 10645 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans v₁.t3₁,
      (kk 10556 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans v₁.N1₁,
      (k 10558 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hW₃,
      (kk 10615 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans hi.b1,
      (kk 10614 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans hi.b0,
      (kk 10616 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans hi.b2,
      (kk 10617 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans hi.b3,
      (kk 10544 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).trans hEI⟩
  have hL₀' : p₀.Lmax = feIsoB p₀.A p₀.N p₀.FN Wc₀ := hL₀
  have hL₁' : p₁.Lmax = feIsoB p₁.A p₁.N p₁.FN Wc₁ := hL₁
  obtain ⟨c₄, e₄, s₄, f₄, m₄, r₄, rm₄, o₄⟩ := pcProg_exec (I := P) pnL2 pnL2_wf h9600 c₃
    e₃.wb_right (fun g hg hs => (pn2_val (hin2 g hg) hs hL₀' hL₁' hW1).2.2.2)
  obtain ⟨L₀, L₁, PW, -⟩ := pn2_val (hin2 c₄.nreg f₄) s₄ hL₀' hL₁' hW1
  -- the final registers
  have k₄ : ∀ r, r ≠ 10535 → r ≠ 10545 → r ≠ 10552 → (r < 10670 ∨ 10684 < r) →
      r ≠ 10600 → r ≠ 10601 → c₄.nreg r = c₃.nreg r := fun r h1 h2 h3 h4 h5 h6 =>
    f₄ r (fun hr => by have := pnL2_dsts r hr; omega) h5 h6
  have kk : ∀ r, r ≠ 10535 → r ≠ 10545 → r ≠ 10552 → (r < 10670 ∨ 10684 < r) →
      r ≠ 10600 → r ≠ 10601 → r ≠ 10557 → r ≠ 10558 → (r < 10690 ∨ 10697 < r) →
      c₄.nreg r = c₁.nreg r := fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    (k₄ r h1 h2 h3 h4 h5 h6).trans (k₃ r h7 h8 h9)
  have T : ∀ r, 10530 ≤ r → r ≤ 10556 → r ≠ 10535 → r ≠ 10545 → r ≠ 10552 →
      c₄.nreg r = c₁.nreg r := fun r a b' c' d' e' =>
    kk r c' d' e' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨c₄, _, Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ e₄)), by unfold pnCost; omega, ⟨?_, ?_, ?_, ?_, ?_, L₀, ?_, ?_, ?_, ?_, ?_, L₁, ?_, ?_, PW,
      ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_, by rw [m₄, m₃, m₂, m₁], by rw [r₄, r₃, r₂, r₁],
    by rw [rm₄, rm₃, rm₂, rm₁], by rw [o₄, o₃, o₂, o₁]⟩
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact v₁.nD₀
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact v₁.k₀
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact v₁.nV₀
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact v₁.nF₀
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; rw [v₁.I0₀, hI0₀]
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact v₁.nD₁
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact v₁.k₁
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact v₁.nV₁
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact v₁.nF₁
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hEI
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact v₁.Pb₀
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact v₁.Pb₁
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact v₁.M
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact v₁.H
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact v₁.N1₀
  · rw [T _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact v₁.N1₁
  · rw [k₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hW₂
  · rw [k₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hW₃
  · rw [kk r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]
    exact f₁ r (fun h => by have := pnL1_dsts r h; omega) (by omega) (by omega)

end NegSSSP

end PlanarFlow
