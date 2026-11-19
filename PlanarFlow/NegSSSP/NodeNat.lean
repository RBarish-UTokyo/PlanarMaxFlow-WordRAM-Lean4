module

public import PlanarFlow.NegSSSP.NodeNatC

/-!
# The node run on natural words: the transformed node program

**One modulus for the whole node.** The node program `nodeProg p₀ p₁` is put on natural words
as one statement, `constsS R M H (W' + 1); ModNat.toNat R M (nodeProg p₀ p₁)`, with `R` above all
the registers of the node and one modulus `M > 2 H`, `H` the largest comparison bound of the
pieces (each piece is compare-bounded with its own bound, raised by `ExecCmp.mono_H`):

* the glue (`glue_cmp`, `nat_cmp`; `*_glueOK`, `*_natOnly`, `PlanarFlow/NegSSSP/NodeNatA.lean`):
  `2 B` from the invariant `NInv W' B`, kept;
* `cProg`, `pProg` (`cProg_cmp`, `pProg_cmp`): `512 (4 b + 2) B`, `64 (2 b + 3)(b + 1) B`, the
  invariant raised to `(4 b + 2) B`, `(2 b + 3)(b + 1) B`;
* Bellman–Ford (`bfStage_cmp`, `PlanarFlow/NegSSSP/NodeNatB.lean`): `2 bfB b B`, raised to
  `bfB b B`;
* FR-Dijkstra of a part (`dijk_cmp_emb`, `PlanarFlow/NegSSSP/NodeNatC.lean`): `6 (w + 3) B`,
  raised to `(w + 3) B`;
* Klein's part (`kPart`): a hypothesis (`KCmp`), to be discharged by the conversion of Klein's
  program.

`NodeCmp I W' H Bf p₀ p₁ c`: every run of the node from `c` is compare-bounded by `H` and ends with
its real memory `≤ W'` bounded by `Bf`. `node_exec_nat`: from such a start `c` with integer reals
(the natural encoding `natOf R W' M (W' + 1) c`, the residues modulo `M`), the transformed node
program runs within `4 t + 3` steps (`t` the steps of the real run) with words bounded by any
`WN ≥ 2 W' + 1 + M² + M`, ends simulating the end of the real run (`Sim`), and every real memory
cell of the end is read back from its residue by `ModNat.Res.signed` (`Bf ≤ H`). With the run of
`node_exec` (the values `f x` of `NegSSSP.step` at `Z + 20 M₀ + ν x`), this is the node on natural
words; the composition `NodeCmp` of the pieces along the run of `node_exec` is
`node_exec_cmp` (`PlanarFlow/NegSSSP/NodeCmpD.lean`, assuming `KCmp`), combined with this theorem
in `node_exec_nat'` (`PlanarFlow/NegSSSP/NodeCmpE.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine Monge CmpAbs ModNat

/-- Every run of the node from `c` is compare-bounded by `H` and ends with its real memory
`≤ W'` bounded by `Bf`. -/
def NodeCmp (I : Input) (W' H Bf : ℕ) (p₀ p₁ : KP) (c : Config) : Prop :=
  ∀ c' t, Exec I W' (nodeProg p₀ p₁) c c' t →
    ExecCmp I W' H (nodeProg p₀ p₁) c c' t ∧ MemB W' Bf c'

/-- The hypothesis on Klein's part of a node: every run of the two parts (`kPairOf`) from a
configuration with the invariant `NInv W' B` compares within `HK` and ends with `NInv W' BK`
(to be discharged by the conversion of Klein's program). -/
def KCmp (I : Input) (W' B HK BK : ℕ) (s : Stmt) : Prop :=
  ∀ c c' t, NInv W' B c → IntAll c → Exec I W' s c c' t →
    ExecCmp I W' HK s c c' t ∧ NInv W' BK c'

/-- **The node on natural words** (see the module docstring). -/
theorem node_exec_nat {I : Input} {W' H Bf R M WN : ℕ} {p₀ p₁ : KP} {c c' : Config} {t : ℕ}
    (hN : NodeCmp I W' H Bf p₀ p₁ c) (e : Exec I W' (nodeProg p₀ p₁) c c' t)
    (hR : (nodeProg p₀ p₁).regsOK (fun r => decide (r < R)) = true)
    (hD : (nodeProg p₀ p₁).noDivR = true) (hZ : IntAll c) (hM : 2 * H < M) (hBf : Bf ≤ H)
    (hWN : 2 * W' + 1 + M * M + M ≤ WN) :
    ∃ d' t', Exec I WN (.seq (constsS R M H (W' + 1)) (ModNat.toNat R M (nodeProg p₀ p₁)))
        (natOf R W' M (W' + 1) c) d' t' ∧ t' ≤ 4 * t + 3 ∧ Sim R W' M (W' + 1) c' d' ∧
      Consts R M H (W' + 1) d' ∧
      ∀ a ≤ W', c'.rmem a = if d'.nmem (W' + 1 + a) ≤ H then (d'.nmem (W' + 1 + a) : ℝ)
        else (d'.nmem (W' + 1 + a) : ℝ) - M := by
  obtain ⟨hC, hMB⟩ := hN c' t e
  have hM0 : 0 < M := by omega
  have hS := sim_natOf (R := R) (W := W') (M := M) (β := W' + 1) (by omega) hM0
    (fun r _ => hZ.1 r) (fun a _ => hZ.2 a)
  have hd : WordsBounded WN (natOf R W' M (W' + 1) c) :=
    natOf_wb e.wb_left (by omega) (by nlinarith) hM0
  obtain ⟨d', t', e', ht', hS', hK', -⟩ := hC.toNat_consts hR hD hM (by omega) (by omega)
    (by omega) (by omega) hS hd
  refine ⟨d', t', e', ht', hS', hK', fun a ha => ?_⟩
  exact (hS'.rmem a ha).signed ((hMB a ha).trans (by exact_mod_cast hBf)) hM

end NegSSSP

end PlanarFlow
