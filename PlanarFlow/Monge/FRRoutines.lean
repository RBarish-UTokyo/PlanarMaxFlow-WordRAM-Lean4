module

public import WordRAM
public import PlanarFlow.Monge.FRTree
public import PlanarFlow.Monge.RowMin

/-!
# FR-Dijkstra on the machine: the input and the basic routines

The input is one dense distance graph on the vertices `0, …, b - 1` (the corners of a face, in
their cyclic order) with explicit arcs, on the vertices `0, …, N - 1` (`b ≤ N`), and a price
function `p`:

* the lengths `D i j` in the real memory at `Db + i b + j`;
* the prices `p x` in the real memory at `pb + x`;
* the explicit arcs grouped by their tail: the arcs leaving `x` are `off x ≤ e < off (x + 1)`,
  `off x` in the natural memory at `ob + x`, the head of `e` at `ob + N + 1 + e`, its length in
  the real memory at `lb + e`;
* the root `r`.

The output: the settled flags (natural memory at `sb + x`) and the distances (real memory at
`db + x`).

**The heap of the vertices.** The keys of Dijkstra are reduced by the price function. A
tournament tree of winners over the vertices (`PlanarFlow.Monge.FR.WinOK`) holds the tentative
keys of the vertices not yet settled (present flags at `wb + x`, keys in the real memory at
`wb + x`, the winners at `wb + N + i`, `1 ≤ i < 2N`, the leaf `N + x` holding `x`). The
structures of the half blocks come after it (`PlanarFlow.Monge.FR.Prm.tb`).

**The routines** of this file (the whole program is `PlanarFlow.Monge.FR.frProg`):

* `evF`, `evE`: an entry of the matrix of the current half block (`F ρ σ`, and `d + F`);
* `hpFix`, `hpUp`, `decKey`: the heap of the vertices (recompute the winner of a node, the
  winners up to the root, decrease a key);
* `ctxW`: the registers of a half block of a level;
* `arcBody`: relax one explicit arc of the vertex `r180`;
* `setup`, `initBody`, `initWinBody`: the constants, the initialization of one vertex, of one
  internal node of the heap of the vertices.

Registers: `r100 … r109` the inputs (`N, b, Db, pb, ob, lb, r, sb, db, wb`), `r110 = 1`,
`r111 = 2`, `r112 = wb + 3N`, `r113 = 16 b`, `r114 = wb + N`, `r115 = b - 1`, `r116 = 4`,
`r117 = 0`, `r118 = 8` (`PlanarFlow.Monge.FR.Glob`); `r120 … r125` the current half block
(`B, s, ts = k s, ss = sib k * s, nc, nr`, `PlanarFlow.Monge.FR.HCtx`); the other registers
are used by the routines.
-/

@[expose] public section

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-! ### The entries of a half block -/

/-- `F ρ σ` in the real `r130`, for `ρ = r130`, `σ = r131`: the length from the source
`ss + σ` to the target `cl b (ts + ρ)`, minus the price of the target. -/
def evF : Stmt :=
  .seq (.instr (.addN 132 122 130)) <|
  .seq (.ifLtN 115 132 (.instr (.copyN 132 115)) .skip) <|
  block [.addN 133 123 131, .mulN 133 133 101, .addN 133 133 132, .addN 133 133 102, .loadR 130 133,
    .addN 133 103 132, .loadR 131 133, .subR 130 130 131]

/-- `d (ss + σ) + F ρ σ` in the real `r130`. -/
def evE : Stmt :=
  .seq evF (block [.addN 133 123 131, .addN 133 133 108, .loadR 131 133, .addR 130 131 130])

/-! ### The heap of the vertices -/

/-- Recompute the winner at the node `r170`. -/
def hpFix : Stmt :=
  .seq (block [.mulN 173 170 111, .addN 173 173 114, .loadN 171 173, .addN 173 173 110,
    .loadN 172 173, .addN 173 109 171, .loadN 174 173]) <|
  .seq (.ifLtN 174 110 (.instr (.copyN 174 172))
    (.seq (block [.addN 173 109 172, .loadN 174 173])
      (.ifLtN 174 110 (.instr (.copyN 174 171))
        (.seq (block [.addN 173 109 171, .loadR 170 173, .addN 173 109 172, .loadR 171 173])
          (.ifLtR 170 171 (.instr (.copyN 174 171)) (.instr (.copyN 174 172))))))) <|
  block [.addN 173 114 170, .storeN 173 174]

/-- Recompute the winners from the node `r170` up to the root. -/
def hpUp : Stmt := .whileLtN 117 170 (.seq hpFix (.instr (.divN 170 170 111)))

/-- **Decrease the key** of the vertex `r175` to the real `r175`, unless it is settled or its
key is not larger. -/
def decKey : Stmt :=
  .seq (block [.addN 176 107 175, .loadN 177 176, .constN 176 0]) <|
  .seq (.ifLtN 177 110
    (.seq (block [.addN 177 109 175, .loadN 177 177])
      (.ifLtN 177 110 (.instr (.copyN 176 110))
        (.seq (block [.addN 177 109 175, .loadR 176 177])
          (.ifLtR 175 176 (.instr (.copyN 176 110)) .skip)))) .skip) <|
  .ifLtN 117 176
    (.seq (block [.addN 177 109 175, .storeN 177 110, .storeR 177 175, .addN 170 100 175,
      .divN 170 170 111]) hpUp) .skip

/-! ### A half block and an explicit arc -/

/-- The registers of the half block `r183` of the level `s = r182` (level base `r181`, stride
`r w` per row). -/
def ctxW (w : ℕ) : Stmt :=
  .seq (block [.copyN 121 182, .mulN 122 183 182, .mulN 120 122 w, .addN 120 120 181,
    .modN 189 183 111]) <|
  .seq (.ifLtN 189 110 (.instr (.addN 189 183 110)) (.instr (.subN 189 183 110))) <|
  .seq (block [.mulN 123 189 182, .subN 124 101 123, .subN 125 101 122]) <|
  .seq (.ifLtN 121 124 (.instr (.copyN 124 121)) .skip)
    (.ifLtN 121 125 (.instr (.copyN 125 121)) .skip)

/-- One explicit arc `r185` of `r180`. -/
def arcBody : Stmt :=
  block [.addN 187 104 100, .addN 187 187 110, .addN 187 187 185, .loadN 175 187,
    .addN 187 108 180, .loadR 175 187, .addN 187 105 185, .loadR 180 187, .addR 175 175 180,
    .addN 187 103 175, .loadR 180 187, .subR 175 175 180] |>.seq
  (.seq decKey (.instr (.addN 185 185 110)))

/-! ### The initialization -/

/-- The constants. -/
def setup : Stmt :=
  block [.constN 110 1, .constN 111 2, .constN 116 4, .constN 117 0, .constN 118 8,
    .constN 191 3, .mulN 112 100 191, .addN 112 112 109, .constN 191 16, .mulN 113 101 191,
    .addN 114 109 100, .subN 115 101 110]

/-- One vertex of the initialization. -/
def initBody : Stmt :=
  block [.addN 191 107 192, .storeN 191 117, .addN 191 109 192, .storeN 191 117,
    .addN 191 114 100, .addN 191 191 192, .storeN 191 192, .addN 192 192 110]

/-- One internal node of the initialization of the heap. -/
def initWinBody : Stmt := .seq (.instr (.subN 170 170 110)) hpFix

end FR

end Monge

end PlanarFlow
