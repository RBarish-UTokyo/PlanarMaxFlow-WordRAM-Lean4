module

public import WordRAM
public import PlanarFlow.Plane.Feasible
public import PlanarFlow.ShortestPath.BellmanFord

/-!
# Feasible flows in plane graphs on the machine: the input and the program

The program `PlanarFlow.Feas.prog` decides whether a plane graph with capacities on the darts
admits a flow meeting given supplies and demands at the vertices (Miller–Naor). It runs on the
random-access machine of `WordRAM/Spec.lean`.

## The input

A list of natural numbers
`[V, F, S, tl 0, rv 0, fc 0, nx 0, cp 0, …, tl (S-1), …, cp (S-1), bp 0, bn 0, …, bp (V-1), bn (V-1)]`:
`V` vertices, `F` faces, `S` darts; for every dart `i` its tail `tl i`, its reverse `rv i`, its
face `fc i`, the next dart `nx i` along the boundary walk of its face, and its capacity `cp i`;
for every vertex `v` its supply `bp v` and its demand `bn v` (the net flow out of `v` must be
`bp v - bn v`). The input describes the combinatorial map `PlanarFlow.Feas.map`, which is
required to be plane (`PlanarFlow.Feas.Enc`). The successor `nx` is part of the description of
the embedding; the program never reads it.

## The program

1. Constants; the total `B` of the supplies and demands; the offset `Z = (F S + 1)(B + 1)`.
   Signed values `x` are stored as `x + Z`.
2. A spanning tree of the graph, by `V` passes over the darts from the vertex `0`: a dart from a
   marked vertex to an unmarked one marks its head, records itself as the parent dart of the
   head, and appends the head to the order of discovery.
3. A *base flow* `g` with net flow `bp - bn` out of every vertex, along the tree: the vertices are
   processed in the reverse order of discovery, each sending its excess to its parent.
   The supplies and demands balance exactly when the excess left at the root is `0`.
4. `F` rounds of Bellman–Ford over the dual graph, whose arcs go from `fc i` to `fc (rv i)` with
   length `cp i - g i`, from `0` at every face.
5. A check that the values form a feasible potential. The output is `1` if the supplies and
   demands balance and the check passes, `0` otherwise.

By `PlanarFlow.CombMap.bflow_iff_potential` and `PlanarFlow.Digraph.isPot_bf_card` the output is
`1` exactly when the flow exists; the cost is `O((V + F) S)` steps.

## Memory

`g` at `0 … S-1`; marks at `S + v`; parent darts at `S + V + v`; the order of discovery at
`S + 2V + k`; excesses at `S + 3V + v`; the Bellman–Ford values at `S + 4V + f`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Feas

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The input -/

/-- The head of a dart. -/
def hd (d : List ℕ) (i : ℕ) : ℕ := tl d (rv d i)
/-! ### The program -/

/-- Constants: `r1 = 1`, `r2 = V`, `r3 = F`, `r4 = S`, `r5 = 5`, `r7 = S + V`, `r8 = S + 2V`,
`r9 = S + 3V`, `r10 = S + 4V`, `r11 = 5S + 3`, `r12 = 2`, `r13 = 3`. -/
def setup : Stmt := block [.constN 1 1, .readIn 2 0, .readIn 3 1, .constN 12 2, .readIn 4 12,
  .constN 5 5, .constN 13 3, .addN 7 4 2, .addN 8 7 2, .addN 9 8 2, .addN 10 9 2,
  .mulN 11 4 5, .addN 11 11 13, .copyN 20 0, .copyN 21 0]

/-- One vertex `r20` of the sum `r21` of the supplies and demands. -/
def bsumStep : Stmt := block [.mulN 22 20 12, .addN 22 22 11, .readIn 23 22, .addN 21 21 23,
  .addN 22 22 1, .readIn 23 22, .addN 21 21 23, .addN 20 20 1]

/-- The offset `r6 = Z = (F S + 1)(B + 1)`. -/
def zset : Stmt := block [.mulN 22 3 4, .addN 22 22 1, .addN 23 21 1, .mulN 6 22 23]

/-- The start of the search: mark the vertex `0`; `r25 = 1` vertex found, `r26 = 0` passes. -/
def reachStart : Stmt := block [.storeN 4 1, .storeN 8 0, .copyN 25 1, .copyN 26 0]

/-- One dart `r20` of a pass: if its tail is marked and its head is not, mark the head. -/
def scan : Stmt :=
  .seq (block [.mulN 22 20 5, .addN 22 22 13, .readIn 23 22, .addN 22 22 1, .readIn 24 22,
      .mulN 22 24 5, .addN 22 22 13, .readIn 24 22, .addN 22 4 23, .loadN 27 22, .addN 22 4 24,
      .loadN 28 22])
    (.seq (.ifLtN 28 27 (block [.storeN 22 1, .addN 22 7 24, .storeN 22 20, .addN 22 8 25,
        .storeN 22 24, .addN 25 25 1]) .skip)
      (.instr (.addN 20 20 1)))

/-- One pass over the darts. -/
def pass : Stmt :=
  .seq (.instr (.copyN 20 0)) (.seq (.whileLtN 20 4 scan) (.instr (.addN 26 26 1)))

/-- One dart `r20` of the initialization of the base flow to `0`. -/
def gStep : Stmt := block [.storeN 20 6, .addN 20 20 1]

/-- One vertex `r20` of the initialization of the excesses to the supply minus the demand. -/
def exStep : Stmt := block [.mulN 22 20 12, .addN 22 22 11, .readIn 23 22, .addN 22 22 1,
  .readIn 24 22, .addN 23 23 6, .subN 23 23 24, .addN 22 9 20, .storeN 22 23, .addN 20 20 1]

/-- One vertex of the tree, in the reverse order of discovery: it sends its excess to its
parent along its parent dart. -/
def treeStep : Stmt := block [.subN 29 29 1, .addN 22 8 29, .loadN 23 22, .addN 22 7 23,
  .loadN 24 22, .addN 22 9 23, .loadN 27 22, .mulN 22 24 5, .addN 22 22 13, .readIn 28 22,
  .addN 22 22 1, .readIn 30 22, .storeN 30 27, .addN 31 6 6, .subN 31 31 27, .storeN 24 31,
  .addN 22 9 28, .loadN 31 22, .addN 31 31 27, .subN 31 31 6, .storeN 22 31]

/-- `r32 = 1` if the excess at the root is `0`, else `0`. -/
def rootCheck : Stmt :=
  .seq (block [.copyN 32 1, .loadN 23 9])
    (.seq (.ifLtN 23 6 (.instr (.copyN 32 0)) .skip) (.ifLtN 6 23 (.instr (.copyN 32 0)) .skip))

/-- One face `r20` of the initialization of the Bellman–Ford values to `0`. -/
def eStep : Stmt := block [.addN 22 10 20, .storeN 22 6, .addN 20 20 1]

/-- For the dart `r20`: `r30` is the value at its face plus its length, `r31` the value at the
face of its reverse, `r22` the address of the latter. -/
def cand : Stmt := block [.mulN 22 20 5, .addN 22 22 13, .addN 22 22 1, .readIn 24 22,
  .addN 22 22 1, .readIn 23 22, .addN 22 22 12, .readIn 27 22, .mulN 22 24 5, .addN 22 22 13,
  .addN 22 22 1, .addN 22 22 1, .readIn 28 22, .addN 22 10 23, .loadN 30 22, .addN 30 30 27,
  .addN 30 30 6, .loadN 31 20, .subN 30 30 31, .addN 22 10 28, .loadN 31 22]

/-- Relax the dart `r20`. -/
def relaxStep : Stmt :=
  .seq cand (.seq (.ifLtN 30 31 (.instr (.storeN 22 30)) .skip) (.instr (.addN 20 20 1)))

/-- One round of Bellman–Ford. -/
def round : Stmt :=
  .seq (.instr (.copyN 20 0)) (.seq (.whileLtN 20 4 relaxStep) (.instr (.addN 26 26 1)))

/-- Check the dart `r20`: clear `r32` if it is violated. -/
def checkStep : Stmt :=
  .seq cand (.seq (.ifLtN 30 31 (.instr (.copyN 32 0)) .skip) (.instr (.addN 20 20 1)))

/-- **The feasibility test.** -/
def prog : Stmt :=
  .seq setup <| .seq (.whileLtN 20 2 bsumStep) <| .seq zset <|
  .seq reachStart <| .seq (.whileLtN 26 2 pass) <|
  .seq (.instr (.copyN 20 0)) <| .seq (.whileLtN 20 4 gStep) <|
  .seq (.instr (.copyN 20 0)) <| .seq (.whileLtN 20 2 exStep) <|
  .seq (.instr (.copyN 29 2)) <| .seq (.whileLtN 1 29 treeStep) <|
  .seq rootCheck <|
  .seq (.instr (.copyN 20 0)) <| .seq (.whileLtN 20 3 eStep) <|
  .seq (.instr (.copyN 26 0)) <| .seq (.whileLtN 26 3 round) <|
  .seq (.instr (.copyN 20 0)) <| .seq (.whileLtN 20 4 checkStep) (.instr (.outN 32))

/-! ### Registers and memory -/

/-- The constant registers, except the offset. -/
def Regs0 (d : List ℕ) (c : Config) : Prop :=
  c.nreg 0 = 0 ∧ c.nreg 1 = 1 ∧ c.nreg 2 = nv d ∧ c.nreg 3 = nf d ∧ c.nreg 4 = nd d ∧
    c.nreg 5 = 5 ∧ c.nreg 7 = nd d + nv d ∧ c.nreg 8 = nd d + 2 * nv d ∧
    c.nreg 9 = nd d + 3 * nv d ∧ c.nreg 10 = nd d + 4 * nv d ∧ c.nreg 11 = nd d * 5 + 3 ∧
    c.nreg 12 = 2 ∧ c.nreg 13 = 3

/-- The constant registers. -/
def Regs (d : List ℕ) (c : Config) : Prop := Regs0 d c ∧ c.nreg 6 = zz d

/-- The registers below `20` are unchanged. -/
def Keeps (c c' : Config) : Prop := ∀ r < 20, c'.nreg r = c.nreg r

theorem Keeps.refl (c : Config) : Keeps c c := fun _ _ => rfl

theorem Keeps.trans {c c' c'' : Config} (h : Keeps c c') (h' : Keeps c' c'') : Keeps c c'' :=
  fun r hr => (h' r hr).trans (h r hr)

theorem regs0_of {d : List ℕ} {c c' : Config} (hR : Regs0 d c)
    (h : ∀ r < 20, r ≠ 6 → c'.nreg r = c.nreg r) : Regs0 d c' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩ := hR
  exact ⟨(h 0 (by omega) (by omega)).trans h0, (h 1 (by omega) (by omega)).trans h1, (h 2 (by omega) (by omega)).trans h2,
    (h 3 (by omega) (by omega)).trans h3, (h 4 (by omega) (by omega)).trans h4, (h 5 (by omega) (by omega)).trans h5,
    (h 7 (by omega) (by omega)).trans h7, (h 8 (by omega) (by omega)).trans h8, (h 9 (by omega) (by omega)).trans h9,
    (h 10 (by omega) (by omega)).trans h10, (h 11 (by omega) (by omega)).trans h11, (h 12 (by omega) (by omega)).trans h12,
    (h 13 (by omega) (by omega)).trans h13⟩

theorem regs_of {d : List ℕ} {c c' : Config} (hR : Regs d c) (h : Keeps c c') : Regs d c' :=
  ⟨regs0_of hR.1 fun r hr _ => h r hr, (h 6 (by omega)).trans hR.2⟩

/-- The signed value stored at an address. -/
def sv (d : List ℕ) (m : ℕ → ℕ) (a : ℕ) : ℤ := (m a : ℤ) - zz d

/-- The mark of a vertex. -/
def mark (d : List ℕ) (m : ℕ → ℕ) (v : ℕ) : ℕ := m (nd d + v)
/-- The parent dart of a vertex. -/
def pr (d : List ℕ) (m : ℕ → ℕ) (v : ℕ) : ℕ := m (nd d + nv d + v)
/-- The vertex discovered `k`-th. -/
def od (d : List ℕ) (m : ℕ → ℕ) (k : ℕ) : ℕ := m (nd d + 2 * nv d + k)
/-- The excess of a vertex. -/
def exv (d : List ℕ) (m : ℕ → ℕ) (v : ℕ) : ℤ := sv d m (nd d + 3 * nv d + v)
/-- The Bellman–Ford value of a face. -/
def ev (d : List ℕ) (m : ℕ → ℕ) (f : ℕ) : ℤ := sv d m (nd d + 4 * nv d + f)

/-- The net flow out of `v` of a function on the darts. -/
def dv (d : List ℕ) (g : ℕ → ℤ) (v : ℕ) : ℤ := ∑ j ∈ (range (nd d)).filter (fun j => tl d j = v), g j

/-- The supply minus the demand of a vertex. -/
def bb (d : List ℕ) (v : ℕ) : ℤ := (bp d v : ℤ) - bn d v

lemma word_inp (d : List ℕ) (i : ℕ) : (inp d).data.getD i 0 = word d i := rfl

end Feas

end PlanarFlow
