# Flows in plane graphs and the BKMNW maximum flow on a word RAM, in Lean 4

A Lean 4 and Mathlib formalization of flows and shortest paths in plane graphs: max-flow min-cut,
the theorem of Miller and Naor, programs for an explicit word RAM for feasible flows, Dijkstra's
algorithm and bipartite matching, and the maximum-flow algorithm of Borradaile, Klein, Mozes,
Nussbaum and Wulff-Nilsen on the machine in `O(n log^3 n)` steps. All proofs use only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

Author and maintainer: Robert D. Barish ([rbarish@ims.u-tokyo.ac.jp](mailto:rbarish@ims.u-tokyo.ac.jp)).

## Submission

| Challenge | Solution | comparator config | metadata | Theorems |
|---|---|---|---|---|
| `PlanarFlowChallenge.lean` | `PlanarFlowSolution.lean` | `comparator.json` | `formalization.yaml` | 6 |

The Challenge module is the statement to audit: it is self-contained, imports only Mathlib and ends
with the compared theorems proved by `sorry`. The Solution module imports the libraries of this
repository, never the Challenge. The configuration permits exactly the axioms `propext`,
`Quot.sound` and `Classical.choice`, compares no definitions separately (`definition_names` is
empty) and enables nanoda. The definitions in the Challenge are copies of the specification modules
of the libraries (`Kasteleyn/Spec.lean`, `NestedDissection/DetModSpec.lean`,
`NestedDissection/Spec.lean`, `PlanarFlow/Matching/Spec.lean`, `PlanarFlow/NegSSSP/Spec.lean`,
`PlanarFlow/STFlow/Spec.lean`, `PlanarFlow/Spec.lean`, `PlanarSeparator/Spec.lean`,
`WordRAM/AlgebraicSpec.lean`, `WordRAM/Spec.lean`); the comparator checks that every constant used
by the compared statements is the same kernel constant in the Solution's environment.

## Statement

### Common definitions

**The machine (`WordRAM`).** A program is a finite list of instructions, addressed by list
position. A configuration has a program counter, natural registers and natural memory cells
(`ℕ → ℕ`), real registers and real memory cells (`ℕ → ℝ`), and an output list. The instructions
are: `halt`; reading the number of input words and the input word at a register address (`0` past
the end); natural constants, copy, `+`, truncated `-`, `*`, `/` (`0` on division by zero) and `%`
(`a % 0 = a`); natural load and store at a register address; the same for reals with real division
(division by zero is a fault); reading a word of the random tape; jumps; branches on `<` for
naturals and for reals; and appending a natural register to the output. Every instruction costs
one step. `WordRAM.RunsWithin prog P W T out` says: started on input `P` from the all-zero
configuration, `prog` executes some number `k` of instructions without fault and then stands at a
`halt` instruction, `k + 1 ≤ T` (the final `halt` is charged one step), every configuration along
the run (the last one included) has all natural registers and all natural memory cells at most
`W`, and the output at the end is `out`. Real registers are not bounded. All inputs in the
statements below have the random tape constantly `0`; randomized algorithms receive their random
values as input words, and the statements bound the fraction of the possible values for which the
output is wrong.

**Plane maps (`PlanarFlow.CombMap`).** The flow part uses combinatorial maps with darts `D`,
vertices `V` and faces `F`: a fixed-point-free involution `rev` on darts, a tail vertex and a face
for each dart, and an injective `next` (the next dart along the boundary of its face) with
`face (next d) = face d` and `tail (next d) = tail (rev d)`; loops and multiple darts are allowed.
A map is plane if `V` is nonempty, the graph and the dual graph (faces adjacent across a dart) are
connected, and `|V| + |F| = |D| / 2 + 2`.

### Flows, including BKMNW maximum flow (`PlanarFlowChallenge.lean`)

Definitions: a `Network V E` has arcs with tail, head and integer capacity; a flow from `S` to `T`
is nonnegative, within capacities and conserved (net outflow `0`) off `S ∪ T`; its value is the
net outflow of `S`; a cut is a vertex set containing `S` and disjoint from `T`, with capacity the
total capacity of the arcs leaving it. On a combinatorial map, a `b`-flow within capacities `u` is
an antisymmetric `f` (`f (rev d) = -f d`) with net outflow `b v` at every vertex and `f ≤ u`; a
feasible potential for lengths `ℓ` is `φ` on faces with `φ (face (rev d)) - φ (face d) ≤ ℓ d`.
The machine inputs are lists of naturals: `Feas` encodes a map (numbers of vertices, faces and
darts, then five words per dart: tail, reverse, face, next, capacity, then supply and demand per
vertex), `Dijk` a digraph with arcs grouped by tail (with a source and a cap `INF` on the
printed distances), `BM` a bipartite graph (colours, arcs from white to black vertices grouped by
tail); the predicates `Feas.Enc`, `Dijk.DEnc`, `BM.Enc` state well-formedness and lower bounds on
the word bound `W`.

* `PlanarFlow.maxflow_mincut`: for a finite network with nonnegative capacities and disjoint
  `S, T`, there are a flow `f` and a cut `X` with `value f = cutCap X`, such that every flow has
  value at most `value f` and every cut has capacity at least `cutCap X`.
* `PlanarFlow.miller_naor`: for a plane map, `b : V → ℤ` and `u, g : D → ℤ` with `g`
  antisymmetric and of net outflow `b` at every vertex: a `b`-flow within `u` exists iff there is
  a feasible potential for the lengths `u - g`.
* `PlanarFlow.feasible_flow_machine`: there is one program such that for every `d`, `W` with
  `Feas.Enc d W` (a plane map with `V` vertices, `F` faces, `S` darts) it halts within
  `26 (S + 2)(V + F + 2)` steps with natural words at most `W` and prints one word, `1` if a flow
  meeting the supplies minus demands within the capacities exists and `0` otherwise.
* `PlanarFlow.dijkstra_machine`: there is one program such that for every `d`, `W` with
  `Dijk.DEnc d W` (`n ≥ 1` vertices, `m` arcs, natural lengths, `INF + length ≤ W` for every arc)
  it halts within `(n + m + 1)(36 ⌊log₂ n⌋ + 143)` steps with natural words at most `W` and prints
  `n` words: for each vertex `v` its distance from the source capped at `INF`, that is, a value at
  most `INF` which is at most the length of every walk from the source to `v` and, if below `INF`,
  the length of such a walk (so `INF` when there is no walk).
* `PlanarFlow.bipartite_matching_machine`: there is one program such that for every `d`, `W` with
  `BM.Enc d W` (`n` vertices, `m` arcs) it halts within `80 (n + 1)(n + m + 1)` steps with natural
  words at most `W` and prints the maximum size of a matching (a set of arcs, no two sharing a
  vertex).
* `PlanarFlow.maxflow_machine`: there are a program and constants `c`, `k` such that for every
  `d`, `W` with `Feas.MEnc' d W` (a plane map with `n` darts and `K` vertices, loops allowed, whose
  rotation `nx ∘ rv` and face walk `nx` are transitive on the darts of each vertex and of each
  face, sources `{v : supply ≠ 0}` and sinks `{v : demand ≠ 0}` disjoint, every input word at most
  `W`) and `W ≥ c (7 s)^k` with `s = n + K + Σ capacities + 2`, the program halts within
  `c (n + K + 1)(⌊log₂ n⌋ + 1)^3` steps with natural words at most `W` and prints `p ++ Z :: q`
  with `|p| = n` and `p[x] < |q|` for every dart `x < n` (every printed index lies in `q`),
  such that `x ↦ q[p[x]] - Z` (in Lean, `q.getD (p.getD x 0) 0 - Z`, with both lookups in range)
  is a flow from the sources to the sinks (antisymmetric, within capacities, conserved off sources
  and sinks) whose value (net outflow of the sources) is at least that of every such flow. The
  constants `c` and `k` are existentially quantified. The statement is `MaxFlowMachine`
  (`PlanarFlow/SpecMaxFlow.lean`).

## Libraries

Each library root module (`WordRAM.lean`, …) imports the modules of the library present here.
The libraries contain exactly the modules needed by the Solution (1323 modules).

| Library | Modules | Content |
|---|---|---|
| `WordRAM` | 12 | the modules used here, from: the machine, structured programs and their compilation, the counted-operation model |
| `Kasteleyn` | 3 | the modules used here, from: Pfaffians, rotation systems, Kasteleyn orientations, the orientation program |
| `NestedDissection` | 17 | the modules used here, from: separator trees, fill, sparse elimination, determinants modulo a prime on the machine |
| `PlanarSeparator` | 114 | the modules used here, from: the planar separator theorem, separator trees, the separator program |
| `PlanarFlow` | 1177 | flows and shortest paths in plane maps, the BKMNW maximum flow (multiple-source shortest paths, FR-Dijkstra, Monge searches, link-cut trees, negative-length shortest paths) |

`Audit.lean` prints the axioms of the 6 compared theorems and of 2753 further theorems of
the libraries.

## Checking

Toolchain `leanprover/lean4:v4.35.0-rc2`; Mathlib as pinned in `lakefile.toml` and
`lake-manifest.json`.

```bash
lake exe cache get && lake build
lake env lean Audit.lean    # every report names only propext, Classical.choice, Quot.sound
lake comparator --config comparator.json --paranoid
```

`lake comparator` needs `bwrap` and the toolchain's `bin` directory on `PATH`. Building the
libraries from scratch takes hours on a small machine, the largest modules need about 5.5 GB of
memory, and the comparator's kernels replay an export of several GB.

## License

Apache-2.0 (`LICENSE`).
