module

public import PlanarFlow.NegSSSP.Enc.HoistPrm

/-!
# The parameters of the fixed encoder on the machine

`hfPrmL Q`: the 110 parameters `feVL p` of the fixed encoder as polynomials (sums of terms
`c · m` minus a constant) in the six primary values of `p : FeP` held in the registers
`Q + 0 … Q + 5` (`p.nD`, `p.k`, `p.nV`, `p.nF`, `p.I0`, `p.Lmax`): linear, except
`p.k * p.k` (in `Bw`) and `p.A * p.Lmax` (in `Inf`). **`hfPrm_val`**: their values are
`feVL p`; **`hfPrm_le`**: each sum is `≤ p.END + p.Inf` (so all words of the parameter program
are `≤ W` when `p.END + p.Inf ≤ W` and `942 ≤ W`, the largest coefficient).
-/

@[expose] public section

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt

set_option maxHeartbeats 4000000 in
/-- **The 110 parameters of the fixed encoder as polynomials in the primaries at `Q`.** -/
def hfPrmL (Q : ℕ) : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v (Q + 0))], 0),
    ([(1, hpM.v (Q + 1))], 0),
    ([(1, hpM.v (Q + 2))], 0),
    ([(1, hpM.v (Q + 3))], 0),
    ([(5, hpM.v (Q + 0)), (1, hpM.v (Q + 1)), (1, hpM.v (Q + 4))], 0),
    ([(24, hpM.one), (67, hpM.v (Q + 0)), (692, hpM.v (Q + 1)), (48, hpM.v (Q + 2)), (48, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(1, hpM.v (Q + 4))], 0),
    ([(1, hpM.v (Q + 0)), (1, hpM.v (Q + 4))], 0),
    ([(2, hpM.v (Q + 0)), (1, hpM.v (Q + 4))], 0),
    ([(3, hpM.v (Q + 0)), (1, hpM.v (Q + 4))], 0),
    ([(4, hpM.v (Q + 0)), (1, hpM.v (Q + 4))], 0),
    ([(5, hpM.v (Q + 0)), (1, hpM.v (Q + 4))], 0),
    ([(1, hpM.v (Q + 0)), (8, hpM.v (Q + 1))], 0),
    ([(24, hpM.one), (68, hpM.v (Q + 0)), (700, hpM.v (Q + 1)), (48, hpM.v (Q + 2)), (48, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(2, hpM.v (Q + 1)), (1, hpM.v (Q + 2))], 0),
    ([(9, hpM.v (Q + 0)), (33, hpM.v (Q + 1)), (1, hpM.v (Q + 4))], 0),
    ([(24, hpM.one), (69, hpM.v (Q + 0)), (708, hpM.v (Q + 1)), (48, hpM.v (Q + 2)), (48, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(25, hpM.one), (69, hpM.v (Q + 0)), (710, hpM.v (Q + 1)), (49, hpM.v (Q + 2)), (48, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(25, hpM.one), (69, hpM.v (Q + 0)), (712, hpM.v (Q + 1)), (50, hpM.v (Q + 2)), (48, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(25, hpM.one), (69, hpM.v (Q + 0)), (714, hpM.v (Q + 1)), (51, hpM.v (Q + 2)), (48, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(25, hpM.one), (69, hpM.v (Q + 0)), (716, hpM.v (Q + 1)), (52, hpM.v (Q + 2)), (48, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(10, hpM.v (Q + 0)), (41, hpM.v (Q + 1)), (1, hpM.v (Q + 4))], 0),
    ([(25, hpM.one), (70, hpM.v (Q + 0)), (724, hpM.v (Q + 1)), (52, hpM.v (Q + 2)), (48, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(25, hpM.one), (70, hpM.v (Q + 0)), (726, hpM.v (Q + 1)), (53, hpM.v (Q + 2)), (48, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(25, hpM.one), (70, hpM.v (Q + 0)), (728, hpM.v (Q + 1)), (54, hpM.v (Q + 2)), (48, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(27, hpM.one), (70, hpM.v (Q + 0)), (728, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (48, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(25, hpM.one), (70, hpM.v (Q + 0)), (728, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (48, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(6, hpM.v (Q + 0)), (9, hpM.v (Q + 1)), (1, hpM.v (Q + 4))], 0),
    ([(1, hpM.v (Q + 0)), (10, hpM.v (Q + 1)), (1, hpM.v (Q + 2))], 0),
    ([(27, hpM.one), (70, hpM.v (Q + 0)), (734, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (50, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(2, hpM.v (Q + 1)), (1, hpM.v (Q + 3))], 0),
    ([(27, hpM.one), (71, hpM.v (Q + 0)), (742, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (50, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(27, hpM.one), (73, hpM.v (Q + 0)), (758, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (50, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(28, hpM.one), (73, hpM.v (Q + 0)), (760, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (51, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(28, hpM.one), (73, hpM.v (Q + 0)), (762, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (52, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(28, hpM.one), (73, hpM.v (Q + 0)), (764, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (53, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(28, hpM.one), (73, hpM.v (Q + 0)), (766, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (54, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(27, hpM.one), (72, hpM.v (Q + 0)), (750, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (50, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(28, hpM.one), (74, hpM.v (Q + 0)), (774, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (54, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(28, hpM.one), (74, hpM.v (Q + 0)), (776, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (55, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(28, hpM.one), (74, hpM.v (Q + 0)), (778, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (56, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(28, hpM.one), (74, hpM.v (Q + 0)), (780, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (57, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(28, hpM.one), (74, hpM.v (Q + 0)), (782, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (58, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(28, hpM.one), (74, hpM.v (Q + 0)), (784, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (59, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(29, hpM.one), (74, hpM.v (Q + 0)), (786, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (60, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(29, hpM.one), (74, hpM.v (Q + 0)), (788, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (61, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(29, hpM.one), (74, hpM.v (Q + 0)), (790, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (62, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(29, hpM.one), (74, hpM.v (Q + 0)), (792, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (63, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(29, hpM.one), (74, hpM.v (Q + 0)), (794, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (64, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(25, hpM.one), (70, hpM.v (Q + 0)), (730, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (48, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(25, hpM.one), (70, hpM.v (Q + 0)), (732, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (49, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(25, hpM.one), (70, hpM.v (Q + 0)), (734, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (50, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(7, hpM.v (Q + 0)), (9, hpM.v (Q + 1)), (1, hpM.v (Q + 4))], 0),
    ([(1, hpM.v (Q + 0)), (12, hpM.v (Q + 1)), (1, hpM.v (Q + 2)), (1, hpM.v (Q + 3))], 0),
    ([(2, hpM.v (Q + 1)), (1, hpM.v (Q + 3))], 1),
    ([(29, hpM.one), (75, hpM.v (Q + 0)), (804, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (65, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(29, hpM.one), (74, hpM.v (Q + 0)), (796, hpM.v (Q + 1)), (55, hpM.v (Q + 2)), (65, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(11, hpM.v (Q + 0)), (49, hpM.v (Q + 1)), (1, hpM.v (Q + 4))], 0),
    ([(36, hpM.one), (85, hpM.v (Q + 0)), (940, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (81, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(37, hpM.one), (85, hpM.v (Q + 0)), (942, hpM.v (Q + 1)), (68, hpM.v (Q + 2)), (81, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(15, hpM.v (Q + 0)), (90, hpM.v (Q + 1)), (2, hpM.v (Q + 2)), (2, hpM.v (Q + 3)), (1, hpM.v (Q + 4))], 0),
    ([(17, hpM.v (Q + 0)), (114, hpM.v (Q + 1)), (4, hpM.v (Q + 2)), (4, hpM.v (Q + 3)), (1, hpM.v (Q + 4))], 0),
    ([(19, hpM.v (Q + 0)), (138, hpM.v (Q + 1)), (6, hpM.v (Q + 2)), (6, hpM.v (Q + 3)), (1, hpM.v (Q + 4))], 0),
    ([(2, hpM.one), (1, hpM.v (Q + 2))], 0),
    ([(29, hpM.one), (77, hpM.v (Q + 0)), (824, hpM.v (Q + 1)), (56, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(29, hpM.one), (77, hpM.v (Q + 0)), (826, hpM.v (Q + 1)), (57, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(29, hpM.one), (76, hpM.v (Q + 0)), (816, hpM.v (Q + 1)), (56, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(30, hpM.one), (77, hpM.v (Q + 0)), (828, hpM.v (Q + 1)), (58, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(30, hpM.one), (78, hpM.v (Q + 0)), (836, hpM.v (Q + 1)), (58, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(4, hpM.one), (28, hpM.v (Q + 0)), (243, hpM.v (Q + 1)), (14, hpM.v (Q + 2)), (14, hpM.v (Q + 3)), (1, hpM.v (Q + 4))], 0),
    ([(4, hpM.one), (28, hpM.v (Q + 0)), (242, hpM.v (Q + 1)), (14, hpM.v (Q + 2)), (14, hpM.v (Q + 3)), (1, hpM.v (Q + 4))], 0),
    ([(33, hpM.one), (81, hpM.v (Q + 0)), (860, hpM.v (Q + 1)), (58, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(33, hpM.one), (81, hpM.v (Q + 0)), (862, hpM.v (Q + 1)), (59, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(1, hpM.one), (2, hpM.vv (Q + 1) (Q + 5)), (1, hpM.vv (Q + 2) (Q + 5))], 0),
    ([(33, hpM.one), (81, hpM.v (Q + 0)), (864, hpM.v (Q + 1)), (60, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(33, hpM.one), (81, hpM.v (Q + 0)), (866, hpM.v (Q + 1)), (61, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(34, hpM.one), (81, hpM.v (Q + 0)), (868, hpM.v (Q + 1)), (62, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(34, hpM.one), (81, hpM.v (Q + 0)), (870, hpM.v (Q + 1)), (63, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(34, hpM.one), (81, hpM.v (Q + 0)), (872, hpM.v (Q + 1)), (64, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(34, hpM.one), (81, hpM.v (Q + 0)), (874, hpM.v (Q + 1)), (65, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(34, hpM.one), (81, hpM.v (Q + 0)), (876, hpM.v (Q + 1)), (66, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(20, hpM.v (Q + 0)), (146, hpM.v (Q + 1)), (6, hpM.v (Q + 2)), (6, hpM.v (Q + 3)), (1, hpM.v (Q + 4))], 0),
    ([(22, hpM.v (Q + 0)), (170, hpM.v (Q + 1)), (8, hpM.v (Q + 2)), (8, hpM.v (Q + 3)), (1, hpM.v (Q + 4))], 0),
    ([(28, hpM.v (Q + 0)), (242, hpM.v (Q + 1)), (14, hpM.v (Q + 2)), (14, hpM.v (Q + 3)), (1, hpM.v (Q + 4))], 0),
    ([(2, hpM.v (Q + 1)), (1, hpM.v (Q + 2))], 1),
    ([(34, hpM.one), (81, hpM.v (Q + 0)), (878, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(34, hpM.one), (82, hpM.v (Q + 0)), (886, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(34, hpM.one), (84, hpM.v (Q + 0)), (902, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(35, hpM.one), (84, hpM.v (Q + 0)), (904, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (67, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(35, hpM.one), (84, hpM.v (Q + 0)), (906, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (68, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(35, hpM.one), (84, hpM.v (Q + 0)), (908, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (69, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(35, hpM.one), (84, hpM.v (Q + 0)), (910, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (70, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(34, hpM.one), (83, hpM.v (Q + 0)), (894, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (66, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(35, hpM.one), (85, hpM.v (Q + 0)), (918, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (70, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(35, hpM.one), (85, hpM.v (Q + 0)), (920, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (71, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(35, hpM.one), (85, hpM.v (Q + 0)), (922, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (72, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(35, hpM.one), (85, hpM.v (Q + 0)), (924, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (73, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(35, hpM.one), (85, hpM.v (Q + 0)), (926, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (74, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(35, hpM.one), (85, hpM.v (Q + 0)), (928, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (75, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(36, hpM.one), (85, hpM.v (Q + 0)), (930, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (76, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(36, hpM.one), (85, hpM.v (Q + 0)), (932, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (77, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(36, hpM.one), (85, hpM.v (Q + 0)), (934, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (78, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(36, hpM.one), (85, hpM.v (Q + 0)), (936, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (79, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(36, hpM.one), (85, hpM.v (Q + 0)), (938, hpM.v (Q + 1)), (67, hpM.v (Q + 2)), (80, hpM.v (Q + 3)), (1, hpM.v (Q + 4)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(24, hpM.v (Q + 0)), (194, hpM.v (Q + 1)), (10, hpM.v (Q + 2)), (10, hpM.v (Q + 3)), (1, hpM.v (Q + 4))], 0),
    ([(26, hpM.v (Q + 0)), (218, hpM.v (Q + 1)), (12, hpM.v (Q + 2)), (12, hpM.v (Q + 3)), (1, hpM.v (Q + 4))], 0),
    ([(2, hpM.one), (28, hpM.v (Q + 0)), (242, hpM.v (Q + 1)), (14, hpM.v (Q + 2)), (14, hpM.v (Q + 3)), (1, hpM.v (Q + 4))], 0),
    ([(1, hpM.one), (28, hpM.v (Q + 0)), (242, hpM.v (Q + 1)), (14, hpM.v (Q + 2)), (14, hpM.v (Q + 3)), (1, hpM.v (Q + 4))], 0),
    ([(24, hpM.one), (62, hpM.v (Q + 0)), (691, hpM.v (Q + 1)), (48, hpM.v (Q + 2)), (48, hpM.v (Q + 3)), (1, hpM.vv (Q + 1) (Q + 1))], 0),
    ([(23, hpM.one), (62, hpM.v (Q + 0)), (691, hpM.v (Q + 1)), (48, hpM.v (Q + 2)), (48, hpM.v (Q + 3)), (1, hpM.vv (Q + 1) (Q + 1))], 0)]

theorem hfPrmL_length (Q : ℕ) : (hfPrmL Q).length = 110 := rfl

set_option maxHeartbeats 8000000 in
/-- **The values of the parameter polynomials are the parameters of the encoder.** -/
theorem hfPrm_val (Q : ℕ) (p : FeP) (f : ℕ → ℕ) (h0 : f (Q + 0) = p.nD) (h1 : f (Q + 1) = p.k)
    (h2 : f (Q + 2) = p.nV) (h3 : f (Q + 3) = p.nF) (h4 : f (Q + 4) = p.I0)
    (h5 : f (Q + 5) = p.Lmax) :
    (hfPrmL Q).map (fun e => hpSum f e.1 - e.2) = feVL p := by
  simp only [hfPrmL, List.map_cons, List.map_nil, hpSum, hpM.ev, List.sum_cons, List.sum_nil,
    h0, h1, h2, h3, h4, h5, feVL, FeP.N, FeP.A, FeP.FN, FeP.AE, FeP.NN, FeP.β, FeP.Bw, FeP.Kw,
    FeP.SL, FeP.ONE, FeP.ZV, FeP.PA, FeP.O1, FeP.ZC, FeP.WW, FeP.ZI, FeP.RD, FeP.MK, FeP.ISO,
    FeP.RK, FeP.DB, FeP.ZS, FeP.ZT, FeP.OS, FeP.END, FeP.Inf, Klein.kBL, Klein.aOUT, Klein.iOB,
    Klein.iOE, Klein.iOL, Klein.iXT, Klein.iIV, Klein.iIT, Klein.iHD, Klein.iIF, Klein.iIC,
    List.cons.injEq, and_true, Nat.sub_zero]
  repeat' apply And.intro
  all_goals first | omega | ring

set_option maxHeartbeats 8000000 in
/-- **The sums of the parameter polynomials are at most `p.END + p.Inf`.** -/
theorem hfPrm_le (Q : ℕ) (p : FeP) (f : ℕ → ℕ) (h0 : f (Q + 0) = p.nD) (h1 : f (Q + 1) = p.k)
    (h2 : f (Q + 2) = p.nV) (h3 : f (Q + 3) = p.nF) (h4 : f (Q + 4) = p.I0)
    (h5 : f (Q + 5) = p.Lmax) : ∀ e ∈ hfPrmL Q, hpSum f e.1 ≤ p.END + p.Inf := by
  rw [← List.forall_iff_forall_mem]
  simp only [hfPrmL, List.forall_cons, List.Forall, hpSum, List.map_cons, List.map_nil, hpM.ev,
    List.sum_cons, List.sum_nil, h0, h1, h2, h3, h4, h5, FeP.N, FeP.A, FeP.FN, FeP.AE, FeP.NN,
    FeP.β, FeP.Bw, FeP.Kw, FeP.SL, FeP.ONE, FeP.ZV, FeP.PA, FeP.O1, FeP.ZC, FeP.WW, FeP.ZI,
    FeP.RD, FeP.MK, FeP.ISO, FeP.RK, FeP.DB, FeP.ZS, FeP.ZT, FeP.OS, FeP.END, FeP.Inf, Klein.kBL,
    Klein.aOUT, and_true]
  repeat' apply And.intro
  all_goals first | omega | (ring_nf; omega) | nlinarith

/-- The registers of a monomial lie in `[lo, hi)`. -/
def hpM.inB (lo hi : ℕ) : hpM → Bool
  | .one => true
  | .v r => decide (lo ≤ r ∧ r < hi)
  | .vv r s => decide (lo ≤ r ∧ r < hi ∧ lo ≤ s ∧ s < hi)

/-- The shape of a parameter list: constants `≤ dmax`, coefficients in `[1, cmax]`, registers in
`[lo, hi)` (decidable). -/
def hpShape (lo hi cmax dmax : ℕ) (es : List (List (ℕ × hpM) × ℕ)) : Bool :=
  es.all fun e => decide (e.2 ≤ dmax) &&
    e.1.all fun x => decide (1 ≤ x.1 ∧ x.1 ≤ cmax) && x.2.inB lo hi

theorem hpM_avoid_of_inB {lo hi y : ℕ} {m : hpM} (h : m.inB lo hi = true) (hy : y < lo ∨ hi ≤ y) :
    m.avoid y := by
  cases m <;> simp_all [hpM.inB, hpM.avoid] <;> omega

/-- The shape gives the conditions of `hpProg_exec`. -/
theorem hpShape_ok {W PB t lo hi cmax dmax : ℕ} {es : List (List (ℕ × hpM) × ℕ)}
    (h : hpShape lo hi cmax dmax es = true) (hc : cmax ≤ W) (hd : dmax ≤ W)
    (hP : hi ≤ PB ∨ PB + es.length ≤ lo) (ht : hi ≤ t ∨ t + 1 < lo)
    (htP : t + 1 < PB ∨ PB + es.length ≤ t) : hpProgOK W PB t es := by
  refine ⟨htP, fun e he => ?_⟩
  simp only [hpShape, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h e he
  refine ⟨by omega, fun x hx => ?_⟩
  obtain ⟨⟨a, b⟩, c⟩ := h2 x hx
  exact ⟨a, by omega, fun y y1 y2 => hpM_avoid_of_inB c (by omega),
    hpM_avoid_of_inB c (by omega), hpM_avoid_of_inB c (by omega)⟩

set_option maxRecDepth 100000 in
theorem hfPrm_shape0 : hpShape 10530 10536 942 1 (hfPrmL 10530) = true := by kernel_rfl
set_option maxRecDepth 100000 in
theorem hfPrm_shape1 : hpShape 10540 10546 942 1 (hfPrmL 10540) = true := by kernel_rfl

set_option maxRecDepth 100000 in
theorem hfPrm_cost (Q : ℕ) : hpCost (hfPrmL Q) = hpCost (hfPrmL 0) := by kernel_rfl

/-- **The parameters of the fixed encoder computed on the machine** from the six primary values
of `p` at `Q` (`(PB, Q) = (10000, 10530)` or `(10200, 10540)`, scratch `10600`, `10601`), within
`hpCost (hfPrmL 0)` steps. -/
theorem hfPrm_exec {I : Input} {W : ℕ} (PB Q : ℕ)
    (hQ : (PB = 10000 ∧ Q = 10530) ∨ (PB = 10200 ∧ Q = 10540)) (p : FeP) (c : Config)
    (hc : WordsBounded W c) (hW : p.END + p.Inf ≤ W) (h942 : 942 ≤ W)
    (h0 : c.nreg (Q + 0) = p.nD) (h1 : c.nreg (Q + 1) = p.k) (h2 : c.nreg (Q + 2) = p.nV)
    (h3 : c.nreg (Q + 3) = p.nF) (h4 : c.nreg (Q + 4) = p.I0) (h5 : c.nreg (Q + 5) = p.Lmax) :
    ∃ c', Exec I W (hpProg PB 10600 (hfPrmL Q)) c c' (hpCost (hfPrmL 0)) ∧
      (∀ j < 110, c'.nreg (PB + j) = feV p j) ∧
      (∀ r, (r < PB ∨ PB + 110 ≤ r) → r ≠ 10600 → r ≠ 10601 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W PB 10600 (hfPrmL Q) := by
    rcases hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hpShape_ok hfPrm_shape0 h942 (by omega) (by simp [hfPrmL_length])
        (by omega) (by simp [hfPrmL_length])
    · exact hpShape_ok hfPrm_shape1 h942 (by omega) (by simp [hfPrmL_length])
        (by omega) (by simp [hfPrmL_length])
  obtain ⟨c', e, v, f, m, r, rm, o⟩ := hpProg_exec (I := I) (hfPrmL Q) PB hok c hc
    (fun e he => (hfPrm_le Q p c.nreg h0 h1 h2 h3 h4 h5 e he).trans hW)
  refine ⟨c', e.cast (hfPrm_cost Q), fun j hj => ?_, fun r h1 h2 h3 => f r (by
    rw [hfPrmL_length]; exact h1) h2 h3, m, r, rm, o⟩
  have hj' : j < (hfPrmL Q).length := by rw [hfPrmL_length]; exact hj
  rw [v j hj']
  have hval := hfPrm_val Q p c.nreg h0 h1 h2 h3 h4 h5
  unfold feV
  rw [← hval, List.getD_eq_getElem _ _ hj',
    List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj'), List.getElem_map]

end NegSSSP

end PlanarFlow
