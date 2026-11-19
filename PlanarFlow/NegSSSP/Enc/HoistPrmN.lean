module

public import PlanarFlow.NegSSSP.Enc.HoistPrmFe

/-!
# The parameters of the fixed node on the machine

`hnRec p Pb N1 Wc W' M`: the constants of a part (`KPN`) from the constants `p : FeP` of its
encoder, the position base `Pb`, `N₁ = srcN1 …`, `Wc = (srcW …).toNat`, the word bound `W'` and
the modulus `M` (with `Hc = 0`: the two entries `2 Hc + 1`, `Hc` are written later by `hfSave`).
`hnPrmL`: the 115 parameters `hnVL (hnRec p₀ …) (hnRec p₁ …) M H (W' + 1)` as polynomials
(linear, plus `kᵢ²`) in the 21 primary registers: `p₀` at `10530 … 10535`, `p₁` at
`10540 … 10545`, `Pb₀ Pb₁ W' M H N1₀ N1₁ Wc₀ Wc₁` at `10550 … 10558`.
**`hnPrm_val`**, **`hnPrm_le`**, **`hnPrm_exec`** (as for the encoder).
-/

@[expose] public section

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-- The constants of a part from the constants of its encoder (with `Hc = 0`). -/
def hnRec (p : FeP) (Pb N1 Wc W' M : ℕ) : KPN :=
  ⟨p.k, p.N, p.NN, p.Bw, p.Kw + 1, p.β, p.RK, Pb, 0, N1, Wc, 2 * W' + 2, W' + 1, M⟩

set_option maxHeartbeats 4000000 in
/-- **The 115 parameters of the fixed node as polynomials in the primary registers.** -/
def hnPrmL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v (10550 + 3))], 0),
    ([(1, hpM.v (10550 + 4))], 0),
    ([(1, hpM.one), (1, hpM.v (10550 + 2))], 0),
    ([(1, hpM.v (10530 + 1))], 0),
    ([(1, hpM.v (10550 + 0))], 0),
    ([(24, hpM.one), (62, hpM.v (10530 + 0)), (691, hpM.v (10530 + 1)), (48, hpM.v (10530 + 2)), (48, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(5, hpM.v (10530 + 0)), (1, hpM.v (10530 + 1)), (1, hpM.v (10530 + 4))], 0),
    ([(48, hpM.one), (124, hpM.v (10530 + 0)), (1382, hpM.v (10530 + 1)), (96, hpM.v (10530 + 2)), (96, hpM.v (10530 + 3)), (2, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(2, hpM.one), (2, hpM.v (10550 + 2))], 0),
    ([(3, hpM.one), (3, hpM.v (10530 + 0)), (24, hpM.v (10530 + 1))], 0),
    ([(30, hpM.one), (78, hpM.v (10530 + 0)), (836, hpM.v (10530 + 1)), (58, hpM.v (10530 + 2)), (66, hpM.v (10530 + 3)), (1, hpM.v (10530 + 4)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(1, hpM.one)], 0),
    ([], 0),
    ([(2, hpM.v (10530 + 0)), (24, hpM.v (10530 + 1)), (2, hpM.v (10530 + 2)), (2, hpM.v (10530 + 3))], 0),
    ([(7, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(8, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(9, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(10, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(11, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(12, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(13, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(14, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(15, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(16, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(17, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(18, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(19, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(20, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(21, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(22, hpM.one), (30, hpM.v (10530 + 0)), (307, hpM.v (10530 + 1)), (16, hpM.v (10530 + 2)), (16, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(23, hpM.v (10530 + 0)), (241, hpM.v (10530 + 1)), (14, hpM.v (10530 + 2)), (14, hpM.v (10530 + 3))], 0),
    ([(15, hpM.v (10530 + 0)), (145, hpM.v (10530 + 1)), (6, hpM.v (10530 + 2)), (6, hpM.v (10530 + 3))], 0),
    ([(1, hpM.one), (23, hpM.v (10530 + 0)), (241, hpM.v (10530 + 1)), (14, hpM.v (10530 + 2)), (14, hpM.v (10530 + 3))], 0),
    ([(17, hpM.v (10530 + 0)), (169, hpM.v (10530 + 1)), (8, hpM.v (10530 + 2)), (8, hpM.v (10530 + 3))], 0),
    ([(3, hpM.v (10530 + 0)), (24, hpM.v (10530 + 1))], 0),
    ([(1, hpM.v (10530 + 0)), (8, hpM.v (10530 + 1))], 0),
    ([(4, hpM.v (10530 + 0)), (32, hpM.v (10530 + 1))], 0),
    ([(5, hpM.v (10530 + 0)), (40, hpM.v (10530 + 1))], 0),
    ([(2, hpM.v (10530 + 0)), (16, hpM.v (10530 + 1))], 0),
    ([(2, hpM.one), (3, hpM.v (10530 + 0)), (24, hpM.v (10530 + 1))], 0),
    ([(2, hpM.one), (23, hpM.v (10530 + 0)), (241, hpM.v (10530 + 1)), (14, hpM.v (10530 + 2)), (14, hpM.v (10530 + 3))], 0),
    ([(19, hpM.v (10530 + 0)), (193, hpM.v (10530 + 1)), (10, hpM.v (10530 + 2)), (10, hpM.v (10530 + 3))], 0),
    ([(3, hpM.one), (23, hpM.v (10530 + 0)), (241, hpM.v (10530 + 1)), (14, hpM.v (10530 + 2)), (14, hpM.v (10530 + 3))], 0),
    ([(21, hpM.v (10530 + 0)), (217, hpM.v (10530 + 1)), (12, hpM.v (10530 + 2)), (12, hpM.v (10530 + 3))], 0),
    ([(10, hpM.v (10530 + 0)), (88, hpM.v (10530 + 1)), (2, hpM.v (10530 + 2)), (2, hpM.v (10530 + 3))], 0),
    ([(4, hpM.one), (23, hpM.v (10530 + 0)), (241, hpM.v (10530 + 1)), (14, hpM.v (10530 + 2)), (14, hpM.v (10530 + 3))], 0),
    ([(4, hpM.one), (23, hpM.v (10530 + 0)), (242, hpM.v (10530 + 1)), (14, hpM.v (10530 + 2)), (14, hpM.v (10530 + 3))], 0),
    ([(1, hpM.one), (3, hpM.v (10530 + 0)), (24, hpM.v (10530 + 1))], 0),
    ([(8, hpM.v (10530 + 0)), (64, hpM.v (10530 + 1))], 0),
    ([(10, hpM.v (10530 + 0)), (89, hpM.v (10530 + 1)), (2, hpM.v (10530 + 2)), (2, hpM.v (10530 + 3))], 0),
    ([(12, hpM.v (10530 + 0)), (113, hpM.v (10530 + 1)), (4, hpM.v (10530 + 2)), (4, hpM.v (10530 + 3))], 0),
    ([(14, hpM.v (10530 + 0)), (137, hpM.v (10530 + 1)), (6, hpM.v (10530 + 2)), (6, hpM.v (10530 + 3))], 0),
    ([(1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(1, hpM.v (10550 + 5))], 0),
    ([(5, hpM.one), (3, hpM.v (10530 + 0)), (24, hpM.v (10530 + 1)), (2, hpM.v (10550 + 2))], 0),
    ([(1, hpM.v (10550 + 7))], 0),
    ([(1, hpM.one), (1, hpM.v (10550 + 2))], 0),
    ([(1, hpM.v (10550 + 3))], 0),
    ([(1, hpM.v (10540 + 1))], 0),
    ([(1, hpM.v (10550 + 1))], 0),
    ([(24, hpM.one), (62, hpM.v (10540 + 0)), (691, hpM.v (10540 + 1)), (48, hpM.v (10540 + 2)), (48, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(5, hpM.v (10540 + 0)), (1, hpM.v (10540 + 1)), (1, hpM.v (10540 + 4))], 0),
    ([(48, hpM.one), (124, hpM.v (10540 + 0)), (1382, hpM.v (10540 + 1)), (96, hpM.v (10540 + 2)), (96, hpM.v (10540 + 3)), (2, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(2, hpM.one), (2, hpM.v (10550 + 2))], 0),
    ([(3, hpM.one), (3, hpM.v (10540 + 0)), (24, hpM.v (10540 + 1))], 0),
    ([(30, hpM.one), (78, hpM.v (10540 + 0)), (836, hpM.v (10540 + 1)), (58, hpM.v (10540 + 2)), (66, hpM.v (10540 + 3)), (1, hpM.v (10540 + 4)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(1, hpM.one)], 0),
    ([], 0),
    ([(2, hpM.v (10540 + 0)), (24, hpM.v (10540 + 1)), (2, hpM.v (10540 + 2)), (2, hpM.v (10540 + 3))], 0),
    ([(7, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(8, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(9, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(10, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(11, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(12, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(13, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(14, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(15, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(16, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(17, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(18, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(19, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(20, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(21, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(22, hpM.one), (30, hpM.v (10540 + 0)), (307, hpM.v (10540 + 1)), (16, hpM.v (10540 + 2)), (16, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(23, hpM.v (10540 + 0)), (241, hpM.v (10540 + 1)), (14, hpM.v (10540 + 2)), (14, hpM.v (10540 + 3))], 0),
    ([(15, hpM.v (10540 + 0)), (145, hpM.v (10540 + 1)), (6, hpM.v (10540 + 2)), (6, hpM.v (10540 + 3))], 0),
    ([(1, hpM.one), (23, hpM.v (10540 + 0)), (241, hpM.v (10540 + 1)), (14, hpM.v (10540 + 2)), (14, hpM.v (10540 + 3))], 0),
    ([(17, hpM.v (10540 + 0)), (169, hpM.v (10540 + 1)), (8, hpM.v (10540 + 2)), (8, hpM.v (10540 + 3))], 0),
    ([(3, hpM.v (10540 + 0)), (24, hpM.v (10540 + 1))], 0),
    ([(1, hpM.v (10540 + 0)), (8, hpM.v (10540 + 1))], 0),
    ([(4, hpM.v (10540 + 0)), (32, hpM.v (10540 + 1))], 0),
    ([(5, hpM.v (10540 + 0)), (40, hpM.v (10540 + 1))], 0),
    ([(2, hpM.v (10540 + 0)), (16, hpM.v (10540 + 1))], 0),
    ([(2, hpM.one), (3, hpM.v (10540 + 0)), (24, hpM.v (10540 + 1))], 0),
    ([(2, hpM.one), (23, hpM.v (10540 + 0)), (241, hpM.v (10540 + 1)), (14, hpM.v (10540 + 2)), (14, hpM.v (10540 + 3))], 0),
    ([(19, hpM.v (10540 + 0)), (193, hpM.v (10540 + 1)), (10, hpM.v (10540 + 2)), (10, hpM.v (10540 + 3))], 0),
    ([(3, hpM.one), (23, hpM.v (10540 + 0)), (241, hpM.v (10540 + 1)), (14, hpM.v (10540 + 2)), (14, hpM.v (10540 + 3))], 0),
    ([(21, hpM.v (10540 + 0)), (217, hpM.v (10540 + 1)), (12, hpM.v (10540 + 2)), (12, hpM.v (10540 + 3))], 0),
    ([(10, hpM.v (10540 + 0)), (88, hpM.v (10540 + 1)), (2, hpM.v (10540 + 2)), (2, hpM.v (10540 + 3))], 0),
    ([(4, hpM.one), (23, hpM.v (10540 + 0)), (241, hpM.v (10540 + 1)), (14, hpM.v (10540 + 2)), (14, hpM.v (10540 + 3))], 0),
    ([(4, hpM.one), (23, hpM.v (10540 + 0)), (242, hpM.v (10540 + 1)), (14, hpM.v (10540 + 2)), (14, hpM.v (10540 + 3))], 0),
    ([(1, hpM.one), (3, hpM.v (10540 + 0)), (24, hpM.v (10540 + 1))], 0),
    ([(8, hpM.v (10540 + 0)), (64, hpM.v (10540 + 1))], 0),
    ([(10, hpM.v (10540 + 0)), (89, hpM.v (10540 + 1)), (2, hpM.v (10540 + 2)), (2, hpM.v (10540 + 3))], 0),
    ([(12, hpM.v (10540 + 0)), (113, hpM.v (10540 + 1)), (4, hpM.v (10540 + 2)), (4, hpM.v (10540 + 3))], 0),
    ([(14, hpM.v (10540 + 0)), (137, hpM.v (10540 + 1)), (6, hpM.v (10540 + 2)), (6, hpM.v (10540 + 3))], 0),
    ([(1, hpM.vv (10540 + 1) (10540 + 1))], 0),
    ([(1, hpM.v (10550 + 6))], 0),
    ([(5, hpM.one), (3, hpM.v (10540 + 0)), (24, hpM.v (10540 + 1)), (2, hpM.v (10550 + 2))], 0),
    ([(1, hpM.v (10550 + 8))], 0),
    ([(1, hpM.one), (1, hpM.v (10550 + 2))], 0),
    ([(1, hpM.v (10550 + 3))], 0),
    ([(23, hpM.one), (62, hpM.v (10530 + 0)), (691, hpM.v (10530 + 1)), (48, hpM.v (10530 + 2)), (48, hpM.v (10530 + 3)), (1, hpM.vv (10530 + 1) (10530 + 1))], 0),
    ([(23, hpM.one), (62, hpM.v (10540 + 0)), (691, hpM.v (10540 + 1)), (48, hpM.v (10540 + 2)), (48, hpM.v (10540 + 3)), (1, hpM.vv (10540 + 1) (10540 + 1))], 0)]

theorem hnPrmL_length : hnPrmL.length = 115 := rfl

/-- The primary values in the registers. -/
structure HnPrim (f : ℕ → ℕ) (p₀ p₁ : FeP) (Pb₀ Pb₁ W' M H N1₀ N1₁ Wc₀ Wc₁ : ℕ) : Prop where
  a0 : f (10530 + 0) = p₀.nD
  a1 : f (10530 + 1) = p₀.k
  a2 : f (10530 + 2) = p₀.nV
  a3 : f (10530 + 3) = p₀.nF
  a4 : f (10530 + 4) = p₀.I0
  a5 : f (10530 + 5) = p₀.Lmax
  b0 : f (10540 + 0) = p₁.nD
  b1 : f (10540 + 1) = p₁.k
  b2 : f (10540 + 2) = p₁.nV
  b3 : f (10540 + 3) = p₁.nF
  b4 : f (10540 + 4) = p₁.I0
  b5 : f (10540 + 5) = p₁.Lmax
  c0 : f (10550 + 0) = Pb₀
  c1 : f (10550 + 1) = Pb₁
  c2 : f (10550 + 2) = W'
  c3 : f (10550 + 3) = M
  c4 : f (10550 + 4) = H
  c5 : f (10550 + 5) = N1₀
  c6 : f (10550 + 6) = N1₁
  c7 : f (10550 + 7) = Wc₀
  c8 : f (10550 + 8) = Wc₁

set_option maxHeartbeats 16000000 in
/-- **The values of the node's parameter polynomials.** -/
theorem hnPrm_val {f : ℕ → ℕ} {p₀ p₁ : FeP} {Pb₀ Pb₁ W' M H N1₀ N1₁ Wc₀ Wc₁ : ℕ}
    (h : HnPrim f p₀ p₁ Pb₀ Pb₁ W' M H N1₀ N1₁ Wc₀ Wc₁) :
    hnPrmL.map (fun e => hpSum f e.1 - e.2) =
      hnVL (hnRec p₀ Pb₀ N1₀ Wc₀ W' M) (hnRec p₁ Pb₁ N1₁ Wc₁ W' M) M H (W' + 1) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, b0, b1, b2, b3, b4, b5, c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := h
  simp only [hnPrmL, List.map_cons, List.map_nil, hpSum, hpM.ev, List.sum_cons, List.sum_nil,
    a0, a1, a2, a3, a4, a5, b0, b1, b2, b3, b4, b5, c0, c1, c2, c3, c4, c5, c6, c7, c8,
    hnVL, kpVL, hnRec, KPN.Kw, List.cons_append, List.nil_append, FeP.N, FeP.A, FeP.FN, FeP.AE,
    FeP.NN, FeP.β, FeP.Bw, FeP.Kw, FeP.SL, FeP.ONE, FeP.ZV, FeP.PA, FeP.O1, FeP.ZC, FeP.WW,
    FeP.ZI, FeP.RD, FeP.MK, FeP.ISO, FeP.RK, Klein.kBL, Klein.aOUT, Klein.iOB, Klein.iOE,
    Klein.iOL, Klein.iXT, Klein.iIV, Klein.iIT, Klein.iHD, Klein.iIF, Klein.iIC, Klein.iGB,
    Klein.iNG, Klein.iNT, Klein.iNH, Klein.iED, Klein.aPH, Klein.aVL, Klein.aH0, Klein.aTH,
    List.cons.injEq, and_true, Nat.sub_zero]
  repeat' apply And.intro
  all_goals first | trivial | rfl | omega | ring

/-- The bound of the node's parameter sums. -/
def hnB (p₀ p₁ : FeP) (Pb₀ Pb₁ W' M H N1₀ N1₁ Wc₀ Wc₁ : ℕ) : ℕ :=
  3 * (p₀.END + p₁.END + W' + M + H + N1₀ + N1₁ + Wc₀ + Wc₁ + Pb₀ + Pb₁) + 3

set_option maxRecDepth 100000 in
theorem hnPrm_shape : hpShape 10530 10559 1382 0 hnPrmL = true := by kernel_rfl

set_option maxHeartbeats 4000000 in
/-- The parameters of a part are at most `2 p.END + 2 W' + M + N1 + Wc + Pb + 2`. -/
theorem kp_le (p : FeP) (Pb N1 Wc W' M : ℕ) :
    ∀ x ∈ kpVL (hnRec p Pb N1 Wc W' M), x ≤ 2 * p.END + 2 * W' + M + N1 + Wc + Pb + 2 := by
  rw [← List.forall_iff_forall_mem]
  simp only [kpVL, hnRec, KPN.Kw, List.Forall, FeP.N, FeP.A, FeP.FN, FeP.AE, FeP.NN, FeP.β, FeP.Bw,
    FeP.Kw, FeP.SL, FeP.ONE, FeP.ZV, FeP.PA, FeP.O1, FeP.ZC, FeP.WW, FeP.ZI, FeP.RD, FeP.MK,
    FeP.ISO, FeP.RK, FeP.DB, FeP.ZS, FeP.ZT, FeP.OS, FeP.END, Klein.kBL, Klein.aOUT, Klein.iOB,
    Klein.iOE, Klein.iOL, Klein.iXT, Klein.iIV, Klein.iIT, Klein.iHD, Klein.iIF, Klein.iIC,
    Klein.iGB, Klein.iNG, Klein.iNT, Klein.iNH, Klein.iED, Klein.aPH, Klein.aVL, Klein.aH0,
    Klein.aTH]
  repeat' apply And.intro
  all_goals omega

/-- **The sums of the node's parameter polynomials are at most `hnB …`.** -/
theorem hnPrm_le {{f : ℕ → ℕ}} {{p₀ p₁ : FeP}} {{Pb₀ Pb₁ W' M H N1₀ N1₁ Wc₀ Wc₁ : ℕ}}
    (h : HnPrim f p₀ p₁ Pb₀ Pb₁ W' M H N1₀ N1₁ Wc₀ Wc₁) :
    ∀ e ∈ hnPrmL, hpSum f e.1 ≤ hnB p₀ p₁ Pb₀ Pb₁ W' M H N1₀ N1₁ Wc₀ Wc₁ := by
  intro e he
  have hsh := hnPrm_shape
  simp only [hpShape, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hsh
  have hd0 : e.2 = 0 := by have := (hsh e he).1; omega
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  have hval := congrArg (fun l => l[j]?) (hnPrm_val h)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some] at hval
  have hj115 : j < 115 := by rw [← hnPrmL_length]; exact hj
  rw [hd0, Nat.sub_zero] at hval
  have hv : hpSum f hnPrmL[j].1 ∈ hnVL (hnRec p₀ Pb₀ N1₀ Wc₀ W' M) (hnRec p₁ Pb₁ N1₁ Wc₁ W' M)
      M H (W' + 1) := by
    have := List.getElem?_eq_some_iff.1 hval.symm
    obtain ⟨h1, h2⟩ := this
    exact h2 ▸ List.getElem_mem h1
  have k0 := kp_le p₀ Pb₀ N1₀ Wc₀ W' M
  have k1 := kp_le p₁ Pb₁ N1₁ Wc₁ W' M
  simp only [hnVL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
  unfold hnB
  have e0 : p₀.Bw + 16 * (p₀.NN + 1) ≤ p₀.END := by
    simp only [FeP.Kw, FeP.END, FeP.OS, FeP.ZT, FeP.ZS, FeP.DB, FeP.RK, FeP.ISO, FeP.MK, FeP.RD, FeP.ZI,
      FeP.WW, FeP.ZC, FeP.O1, FeP.ZV, FeP.ONE, FeP.SL]; omega
  have e1 : p₁.Bw + 16 * (p₁.NN + 1) ≤ p₁.END := by
    simp only [FeP.Kw, FeP.END, FeP.OS, FeP.ZT, FeP.ZS, FeP.DB, FeP.RK, FeP.ISO, FeP.MK, FeP.RD, FeP.ZI,
      FeP.WW, FeP.ZC, FeP.O1, FeP.ZV, FeP.ONE, FeP.SL]; omega
  generalize hpSum f hnPrmL[j].1 = S at hv ⊢
  rcases hv with (((h | h | h) | h) | h) | h | h
  · rw [h]; omega
  · rw [h]; omega
  · rw [h]; omega
  · have := k0 _ h; omega
  · have := k1 _ h; omega
  · rw [h]; simp only [KPN.Kw, hnRec]; omega
  · rw [h]; simp only [KPN.Kw, hnRec]; omega

/-- **The parameters of the fixed node computed on the machine** from the 21 primary registers
(scratch `10600`, `10601`), within `hpCost hnPrmL` steps. -/
theorem hnPrm_exec {I : Input} {W : ℕ} {p₀ p₁ : FeP} {Pb₀ Pb₁ W' M H N1₀ N1₁ Wc₀ Wc₁ : ℕ}
    (c : Config) (hc : WordsBounded W c) (hP : HnPrim c.nreg p₀ p₁ Pb₀ Pb₁ W' M H N1₀ N1₁ Wc₀ Wc₁)
    (hW : hnB p₀ p₁ Pb₀ Pb₁ W' M H N1₀ N1₁ Wc₀ Wc₁ ≤ W) (h1382 : 1382 ≤ W) :
    ∃ c', Exec I W (hpProg 10400 10600 hnPrmL) c c' (hpCost hnPrmL) ∧
      (∀ j < 115, c'.nreg (10400 + j) =
        hnV (hnRec p₀ Pb₀ N1₀ Wc₀ W' M) (hnRec p₁ Pb₁ N1₁ Wc₁ W' M) M H (W' + 1) j) ∧
      (∀ r, (r < 10400 ∨ 10515 ≤ r) → r ≠ 10600 → r ≠ 10601 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 10400 10600 hnPrmL :=
    hpShape_ok hnPrm_shape h1382 (Nat.zero_le _) (by simp [hnPrmL_length]) (by omega)
      (by simp [hnPrmL_length])
  obtain ⟨c', e, v, f, m, r, rm, o⟩ := hpProg_exec (I := I) hnPrmL 10400 hok c hc
    (fun e he => (hnPrm_le hP e he).trans hW)
  refine ⟨c', e, fun j hj => ?_, fun r h1 h2 h3 => f r (by
    rw [hnPrmL_length]; omega) h2 h3, m, r, rm, o⟩
  have hj' : j < hnPrmL.length := by rw [hnPrmL_length]; exact hj
  rw [v j hj']
  have hval := hnPrm_val hP
  unfold hnV
  rw [← hval, List.getD_eq_getElem _ _ hj',
    List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj'), List.getElem_map]

end NegSSSP

end PlanarFlow
