module

public import PlanarFlow.BKMNW.Headline
public import PlanarFlow.BKMNW.FRMachine
public import PlanarFlow.STFlow.ProgExec
public import PlanarFlow.STFlow.IsoExec

/-!
# The subroutine costs of the machine programs

The cost bound of the maximum-flow algorithm (`PlanarFlow.BKMNW.maxflow_plane_cost`) holds for
every family of subroutine costs meeting `SubCosts.Bounds K K₀`, and the bound of the recursion
for negative lengths (`PlanarFlow.NegSSSP.negDecFCost_le`) for every family meeting
`NegSSSP.NegCosts.Bounds K'`. This file fixes concrete families from the step bounds of the
machine programs that exist (`cMach`, `NegSSSP.cNegMach`), proves the bounds with explicit
constants (`cMach_bounds`, `NegSSSP.cNegMach_bounds`), and, for each field whose machine program
is ready, proves that **every call of the subroutine is realized by a run of that program within
the step count of the field**.

The fields without a program are parameters of the families, at the form of the budget:
`C m lg m` for the separator, `C m` for the linear bookkeeping of the maximum-flow recursion and
`C₀ m` for its leaf solver (the linear bookkeeping of the negative-length recursion is `1000 m`,
realized in part). Every bound below holds for all `C` and `C₀`; they are placeholders
for the step counts of programs still to be written, not proved costs.

## Status of the fields

The family `cMach C C₀ : SubCosts` (maximum flow, `K = machK C = 1010921 · negK C`, `K₀ = C₀`):

| field     | value                                    | realization                           |
|-----------|------------------------------------------|---------------------------------------|
| `stflow`  | `504000000 m lg m`                       | **proved**: `cMach_stflow_exec`,      |
|           |                                          | `cMach_stflow_exec_piece`             |
| `fr`      | `6300 (x lg² x + p lg x)`                | **proved for every call**: those of   |
|           |                                          | FixConservationOnPath,                |
|           |                                          | `cMach_fr_exec_fixPath_faces`         |
|           |                                          | (`PlanarFlow/BKMNW/FRFixPath.lean`);  |
|           |                                          | those of the push-back,               |
|           |                                          | `cMach_fr_exec_dual`                  |
|           |                                          | (`PlanarFlow/BKMNW/FRDij.lean`)       |
| `negsssp` | `10920 K' m lg² m + 1000001 K' m`,       | counted cost only:                    |
|           | `K' = negK C`                            | `negSSSPImpl_cost_mach`               |
| `mssp`    | `24637500000 (m lg m + k² lg m)`         | **proved for every call** (every      |
|           |                                          | vertex and face with a dart):         |
|           |                                          | `cMach_mssp_exec`                     |
|           |                                          |                                       |
| `sep`     | `C m lg m` (parameter)                   | blocked                               |
| `leaf`    | `C₀ m` (parameter)                       | **proved for every call when          |
|           |                                          | `C₀ ≥ 30`**: `cMach_leaf_exec`        |
|           |                                          |                                       |
| `lin`     | `C m` (parameter)                        | blocked                               |

The family `NegSSSP.cNegMach C : NegCosts` (negative lengths, `K' = negK C`):

| field  | value                                       | realization                            |
|--------|---------------------------------------------|----------------------------------------|
| `mssp` | `32886 · 2372500000 (m lg m + b² lg m)`     | **proved at the size of the node**:    |
|        |                                             | `NegSSSP.cNegMach_mssp_exec`; with the |
|        |                                             | reading of the answers (polynomially   |
|        |                                             | bounded lengths):                      |
|        |                                             | `NegSSSP.cNegMach_mssp_read_exec`      |
|        |                                             | (`PlanarFlow/BKMNW/ReadMach.lean`)     |
| `dij`  | `6300 (x + p) lg x`                         | **proved for every call**:             |
|        |                                             | `NegSSSP.cNegMach_dijk_exec`           |
|        |                                             | (`PlanarFlow/BKMNW/FRDij.lean`)        |
| `bf`   | `7900 (b + 1)² lg b`                        | **proved for every call**:             |
|        |                                             | `NegSSSP.cNegMach_bf_exec`             |
|        |                                             |                                        |
| `sep`  | `C m lg m` (parameter)                      | partly: `NegSSSP.sep_run_split_full`   |
|        |                                             | (large component, whole program)       |
| `lin`  | `1000 m`                                    | **proved in part** (boundary, reduced  |
|        |                                             | lengths, `π`, minima, `C`, initial     |
|        |                                             | lengths, prices, layout of the arcs):  |
|        |                                             | `NegSSSP.cNegMach_lin_exec_all`,       |
|        |                                             | `NegSSSP.cNegMach_lin_glue_cost`       |
|        |                                             |                                        |
| `leaf` | `96 m²`                                     | **proved for every call** (`m ≥ 1`):   |
|        |                                             | `NegSSSP.cNegMach_leaf_exec`           |
|        |                                             |                                        |

* `stflow`: every call of the s-t flow oracle of `planeOracles` (the perturbed algorithm
  `PlanarFlow.STFlow.pstflowW`, with the word-size perturbation `isoEps`) on a plane map with
  transitive rotations and faces, in particular on a piece map (`pmap`) of the recursion, with
  nonnegative capacities, a nonempty source set and a sink set reached by a dart, disjoint, is
  the output of a run of the machine program `PlanarFlow.STFlow.pstProg` within
  `cMach.stflow m` steps (`PlanarFlow.STFlow.pstflowW_exec_exists`,
  `PlanarFlow.STFlow.pst_steps_le_m`). **Word size**: the perturbation is
  `isoEps M t d = isoL + isoW M t d`, between `1` and `(4 F + 6) #V` (an isolating perturbation
  in the sense of Bourke, Tewari and Vinodchandran: the curl of `isoW` is `1` at every vertex but
  `t`, so the sum of `isoW` along a simple dual cycle counts the vertices on one side,
  `PlanarFlow/STFlow/IsoCycle.lean`); shortest walks in the cut of the cyclic cover are unique
  (`PlanarFlow.STFlow.curl_unique`, `PlanarFlow.STFlow.tight_parW`), so the pivot bound of
  Erickson holds (`PlanarFlow.STFlow.lstepsW_le`), and the darts of the path of the cotree have
  distinct perturbed reduced lengths (`PlanarFlow.STFlow.lred_isoEps_inj`). Every number of the
  run (the keys `N (c - g) + (ε - h)`, the lengths `N c + ε`, the bottleneck amounts and the
  constants, `PlanarFlow.STFlow.isoKeys_bounded`) and every real memory cell of the starting
  configuration (`cMach_stflow_exec`) is an integer of absolute value at most
  `isoW_bound = (m + 4) (2 R + 1) (Σ c + 1)`, `R = (F + 1) m (4 F + 6) #V`: polynomial in the size
  of the map times the capacities. The program holds these integers in the machine's real
  registers; **on natural words** (`cMach_stflow_exec_nat`):
  every run of `pstProg` from the start compares reals at distance at most
  `H = PlanarFlow.STFlow.pstH n m #F #V isoW_bound` (`O(m² isoW_bound)`,
  `PlanarFlow.STFlow.pstflowW_exec_exists_cmp`; the values of the dynamic trees are bounded by
  their potential, `PlanarFlow/DynTree/CmpPot.lean`), so the program on natural words
  `constsS; ModNat.toNat 201 M pstProg` (`M = 2 H + 1`) runs within `4 · cMach.stflow m + 3`
  steps and the word bound `2 W + 1 + M² + M`, the flows read back from their residues
  (`PlanarFlow.STFlow.pstflowW_exec_nat`). In the other cases (no source, or no dart into the
  sinks) `pstflowW` is the zero flow.
* `fr`: the program `PlanarFlow.Monge.FR.frProg` computes the distances in one dense distance
  graph with explicit arcs within `cMach.fr N m` steps, **provided the lengths of the dense
  distance graph meet the crossing inequality** (`PlanarFlow.Monge.Crossing`). For the calls of
  FixConservationOnPath the input is laid out (`PlanarFlow.Monge.FR.mkPrm`), the crossing
  inequality is `crossing_fixPath`, and every call is realized within `cMach.fr (2k) (2k)` steps
  (`PlanarFlow.BKMNW.cMach_fr_exec_fixPath`, `PlanarFlow/BKMNW/FRFixPath.lean`), and within
  `cMach.fr x (2k)`, `x` the faces along the path, the charge of `SubCosts.fixRun`
  (`cMach_fr_exec_fixPath_faces`). The other calls charged to `fr` are the two runs of Dijkstra in
  the dual of the push-back (`dualDijkstra`, no dense distance graph), each realized within
  `cMach.fr nf n` steps, the charge of `SubCosts.pushRun` (`cMach_fr_exec_dual`). Inside the
  recursion for negative lengths the calls with dense distance graphs are those of Bellman–Ford
  (`NegCosts.bf`), on the union of the two dense distance graphs of the children; these have
  missing arcs (`NegSSSP.crossingO_childDDG`: only the weaker crossing inequality `CrossingO`),
  and they are realized by their own program (`NegCosts.bf` below).
* `negsssp`: the oracle `negSSSPImpl` has counted cost at most `cMach.negsssp m` in the model
  `NegCosts` with the costs `cNegMach C` (`negSSSPImpl_cost_mach`); any family meeting
  `NegCosts.Bounds K'` gives a field meeting `SubCosts.Bounds.negsssp` with `K ≥ 1010921 K'`
  (`negsssp_field_le`). A machine run of the whole recursion needs the blocked fields of
  `cNegMach` and the composition of the programs. **The composition**: the driver
  `NegSSSP.Driver.driver` (`PlanarFlow/NegSSSP/Driver.lean`), one loop with an explicit stack of
  frames in memory following `decM` in post-order, parametric in a test, a leaf solver, a split
  and a combination given by `Exec` specifications (`NegSSSP.Driver.DSpec`); `Driver.drive`: the
  run within the sum of the costs of the subprograms plus `20` per leaf and `80` per node.
  `PlanarFlow/NegSSSP/DriverRun.lean`: with the subprograms specified on the frames of the
  decomposition of the machine (`NegSSSP.Driver.NSpec`: outcomes `PotOut`, the split writing
  `splitM` with one round less), `Driver.drive_negDecM_mach`: the outcome in the root frame is
  a `PotOut` outcome of the graph (as `negSSSPDecM_potOut`), within
  `(A + B + 80) · cMach.negsssp n + B + 22` steps when the subprograms cost at most
  `A · cNegMach.leaf m + B` at a leaf and `A · cNegMach.node … + B` at a node. Not yet
  supplied: the four subprograms meeting `NSpec` (the frame glue around `splitProg_splitM`,
  `BFList.prog_exec` and `node_exec_valBy`: the encodings of the children pieces, of the node
  and of the leaf, the one-face encodings, the positions of the boundary vertices) and the
  setup of the root frame (the least lengths, the loops).
* `NegCosts.mssp`: at a node of `m` darts of the decomposition by simple cycles, each of the two
  calls is realized by Klein's program on a one-face instance (`PlanarFlow.NegSSSP.splitF_exec`)
  within `cNegMach.mssp m b` steps — **at the size `m` of the node**, not at the size `mᵢ` of the
  part at which `NegCosts.node` charges the call: the instance of a part is bounded by the size
  of its parent (`OneFace` with `q ≤ 18 m`). The two charges agree up to the constants in the
  bound of a node (`NegCosts.node_le`: `O(m lg m)`), but the realization is not a per-field
  inequality. The reading of the `b²` answers off the trees is part of the program.
* `NegCosts.dij`: Dijkstra with a price function on explicit arcs is FR-Dijkstra with one corner
  (`b = 1`): the dense distance graph on one corner has no arcs (`faceDDG_one_len`), the
  crossing inequality is vacuous, and the layout `Lay` asks only `1 ≤ N` of the corners
  (`NegSSSP.lay_one_exists`); starting configurations exist for every layout
  (`NegSSSP.exists_frConfig`), and all the hypotheses together can be met
  (`NegSSSP.cNegMach_dij_exec_hyps`). `frProg` then computes the distances in
  `emptyDDG.union arcs`, the graph of the calls of the recursion (`PlanarFlow.NegSSSP.dijk`),
  within `6300 (N + m) lg N` steps (`PlanarFlow.Monge.FR.frCost_le` with `b = 1`). Every call
  `fr emptyDDG E r φ` with a feasible price function is laid out (the vertices of a set `S`
  holding the root and the ends of the arcs numbered by `Finset.equivFin`, the arcs sorted by tail
  by `PlanarFlow.Monge.FR.mkPrm`) and realized within `cNegMach.dij |S| |E|` steps
  (`NegSSSP.cNegMach_dij_exec_list`); for the calls `dijk` of a step on a nonempty piece of `m`
  darts and `w` vertices this is `cNegMach.dij (w + 1) (m + w)`, the charge of `NegCosts.node`
  (`NegSSSP.cNegMach_dijk_exec`).
* `mssp`: Klein's program with masked queries (`PlanarFlow.Klein.kleinProgM`) on the cut of the
  dual graph along the path, one flagged move per face along the path and those faces as
  targets, holds `msspPlaneK` at every pair of faces along the path within
  `1642500000 (N lg N + p² lg N)` steps, `N = #V + #F + #D` (`Klein.msspPlaneK_masked`). When
  every vertex and every face has a dart, `N ≤ 3 #D`, so this is within `cMach.mssp #D p`
  (`cMach_mssp_exec`), the charge of `SubCosts.fixRun`. The unmasked program would answer all
  roots of the cut, one per dart leaving the path. Computing the flags (one pass over the roots)
  is a precondition, as are the other preconditions of `klein_exec`.
* `NegCosts.bf`: Bellman–Ford over the union of the two dense distance graphs of the children,
  which have missing arcs and meet only the crossing inequality `CrossingO` in their
  enumerations (`NegSSSP.crossing_step_parts`), is the program `NegSSSP.bfFull`
  (`PlanarFlow/NegSSSP/BFExecP.lean`): from the plain encoding of the two `Option`-matrices
  (arc flags and lengths in row-major order, `NegSSSP.bfStartP`) the pass
  `PlanarFlow.Monge.prepO` computes the static tables of each matrix (the bound `Hb`, then per
  level of the half blocks the first arc column, the genuine flag and the standing row of each
  row, and the entries; `prepCost b ≤ 139 (b + 1)² lg b`), then `PlanarFlow.Monge.bfDDG2O` runs
  `b + 1` rounds of Bellman–Ford over the union with SMAWK on the extended Monge matrices of the
  half blocks (`bf2CostO b ≤ 7600 (b + 1)² lg b`); in all `bfCostP b ≤ 7900 (b + 1)² lg b`
  (`NegSSSP.bfCostP_le`). Every call of the recursion is realized within `cNegMach.bf b` steps,
  `b = |B|`, with a `PotOut` output of `DDG.join` (`NegSSSP.cNegMach_bf_exec`). The function
  `NegSSSP.bfMach I` read off the run (the outcome of the unique run on the pairs meeting the
  hypotheses of the program, `bfRef` elsewhere) meets `BFDDGSpec` (`NegSSSP.bfMach_spec`), and
  at every call of the recursion its value is the outcome of such a run
  (`NegSSSP.bfMach_step`).
* `NegCosts.lin` (`1000 m`): the bookkeeping of a node of `m` darts between the calls of
  `PlanarFlow.NegSSSP.step` is (1) the boundary `B = bdry N P₀ P₁` and its enumerations, (2) the
  reduced lengths `redLen N ℓ δᵢ` passed to the two calls of `mssp`, (3) the orders `β₀`, `β₁`
  of `B` of the one-face instances (`crossing_step_parts`) and `π = permOf b β₀ β₁`, (4) the
  reading of the `b²` answers of each call of `mssp` into the row-major layout of
  `NegSSSP.bfStartP`, (5) the lowering `E - C` (`C = Σ_B |E - δ₀| + |E - δ₁|`), the initial
  lengths `initLen`, the prices and the arcs `dijArcs` of the two calls of Dijkstra in the layout
  `PlanarFlow.Monge.FR.mkPrm` of `frProg`, (6) the minima `omin` of the two runs. On the plain
  encoding of a node (`NegSSSP.NodeEnc`: darts enumerated, vertices numbered below `w ≤ 2m`)
  these are realized: (1) `NegSSSP.bdryProg` (`61 m + 12` steps, `B` listed by vertex number),
  (2) `NegSSSP.redProg` (`17 m + 3` per part), `π` of (3) from the vertex numbers of `β₀`, `β₁`
  at given bases (`NegSSSP.permProg_node`, `16 b + 6 ≤ 32 m + 6`), (6) from the flags and values
  of the two runs at the vertex numbers (`NegSSSP.minProg_node`, `21 w + 3 ≤ 42 m + 3`), together
  within `196 m` (`NegSSSP.cNegMach_lin_exec_all`); (5) by `NegSSSP.cProg` (`C`, by real
  comparisons with `0`, `21 b + 6` steps), `NegSSSP.pProg` per part (the initial lengths and the
  prices at the vertex numbers, the price of the root, `10 w + 17 b + 11`; read as `C`, `initLen`,
  `price` by `NegSSSP.arith_node`) and `NegSSSP.csProg` per part (the arcs in the layout of
  `mkPrm` by a stable counting sort proved against `FR.pre`/`FR.arcList`, `35 M + 21 N + 23` for
  `M = m + w` candidate arcs with keep flags and `N = w + 1` vertices, `NegSSSP.csProg_mkPrm`),
  the candidate arcs themselves by `NegSSSP.aProg` per part (`34 m + 16 w + 8`; read as the arcs
  `dijArcs` numbered by `NegSSSP.csList_dijArcs`), and the settled flags of each run normalized
  to `0`/`1` by `NegSSSP.nrmProg` (`17 w + 4`; `NegSSSP.minIn_of_run`, `NegSSSP.minProg_node_num`:
  the data of `minProg` and the values of `NegSSSP.step` at the vertex numbers); all of it within
  `1000 m` (`NegSSSP.cNegMach_lin_glue_cost`). The calls of Dijkstra are realized at the
  vertex numbers of the node (root `0`, vertex `x` at `ν x + 1`) for any list of the arcs with the
  same members (`NegSSSP.dijk_exec_num`, `PlanarFlow/BKMNW/FRDijNum.lean`), so that (6) reads the
  runs where (5) laid them out. (4) is not in `lin`: the answers are perturbed (`Klein.outNN`:
  the integer part of a real divided by `2 ^ M`, then the cut `Klein.cutW`), the machine has no
  real-to-integer rounding, and `NegSSSP.rdProg` recovers the integer part by a binary search on
  the real side, `O(b² log Wc)` comparisons (`Wc` the cut of the instance); for polynomially
  bounded reduced lengths it is charged to the term `b² lg m` of `mssp`, which Klein's run does
  not use (`NegSSSP.cNegMach_mssp_read_exec`). **Word-sized perturbation (math done, machine
  not yet)**: `PlanarFlow/MSSP/Isolate.lean` replaces the exponential perturbation by a
  deterministic one with polynomially bounded integers, `MSSP.isoLen ℓ d = N₁ ℓ d + N₂ +
  N₃ (w d + B) + ι d` (`N₁ = (n m + 1)(2 B n + 1)(n + 1)`, `ι` the dart numbers, `w` an
  isolating weight of the plane map: antisymmetric, positive curl at every face but one,
  `|w| ≤ #F`, `MSSP.exists_isoW`; Green's theorem on simple cycles, `MSSP.circ_ne_zero`):
  `MSSP.HypNN.hypIso` (the hypotheses of the article), `MSSP.odist_isoLen` (answers divided by
  `N₁`), `MSSP.isoLen_lt` (`isoLen ℓ d < N₁ (ℓ d + 1)`). With these lengths the values of the
  forest of Klein's dynamic tree (`val d = wt d + label (tail d) - label (head d)`,
  `PlanarFlow/Klein/Values.lean`) and the answers are below `poly(n) (max ℓ + 1)`, and the
  reading is one `divN` per answer. **Reals on natural words** (`WordRAM/Machine/RealsModNat.lean`,
  `WordRAM.Machine.ModNat.ExecCmp.toNat`): a statement without `divR` whose reals are integers
  runs on natural words holding its reals modulo `M` (`ModNat.toNat`, at most `4 ×` the steps,
  word bound `max (W, β + W, M² + M)`), provided only that at every executed real test the
  compared difference is at most `H`, `2 H < M` (`ModNat.ExecCmp`; compositional proof rules
  `ModNat.CmpOK.seq`, `…whileLtN`, … from the existing realization lemmas, `Machine.Exec.det`);
  the values themselves may grow between comparisons, only their residues are kept. Klein's
  programs meet the syntactic conditions (`Klein.kleinProgM_regsOK`, `Klein.kleinProgM_noDivR`,
  `Klein.kleinProgMem_regsOK`, `Klein.kleinProgMem_noDivR`). What remains is the bound of the
  compared differences along Klein's run (`ModNat.CmpOK` for `kleinProgM` / `kleinProgMem`):
  its real tests are the conditional moves of the minima in `DynTree.recompS` (`cmov1`,
  `cmov2`, inside every rotation of a splay, the switch of `access` and `cut`), which compare the
  stored value of a node with the minima of its children as it reads them — numbers relative to
  the pending tags above it, so their *differences* are differences of true values of the forest
  (the stored values and tags are not bounded by the invariant `DynTree.LCTE`, only these
  differences are) — and the bit `DynTree.bitS` of `min2` (the minimum against the threshold
  `L - 2B`); then the computation of `w` on the machine (a spanning tree of the dual and subtree
  sizes, `O(m)`), and the re-wiring of `NegSSSP.KEncPert` / `ReadMach` to them, after which the
  polynomial bound on the reduced lengths of `cNegMach_mssp_read_exec` is no longer needed. **Done
  since** (no change of the statements above): the maximum-flow call on the isolating lengths
  (`Klein.msspPlaneK_maskedIso`, `BKMNW.cMach_mssp_execIso`:
  lengths `len'` of the cut with `0 < len' < N₁ (C.len + 1)`, answers read by `Klein.outNI N₁`);
  the bounds of the forest values along the operations (`PlanarFlow/DynTree/VBndOps.lean`,
  `Klein.pivot_vbnd`, `Klein.dart_vbnd`); the replay with `DynTree.ORunC` of the pivot
  (`Klein.piv_orunC`), the pivot loop with the bit `bitS` of `min2` against `L - 2B`
  (`Klein.mv_orunAC`), the queries (`Klein.qMask_orunC`), the step to the next move
  (`Klein.nx_orunC`) and **the whole masked loop over the moves** (`Klein.tLoopM_orunC`,
  `PlanarFlow/Klein/ProgTripMaskC.lean`: compare-bounded from a start whose forest values are at
  most `A - Lo₀`); the explicit bounds `Klein.kleinV` (values) and `Klein.kleinH` (compared
  differences), at most `3000 (k + 1) (#V + 1)² (tripW + 1)` (`Klein.kleinV_kleinH_le`).
  Not yet: the initialisation `inS` (`in_orun`) as an `ORunC`, hence `CmpOK` for the whole
  `kleinProgM`; the unmasked `kleinProg`/`kleinProgMem`; the natural-word realization
  (`ExecCmp.toNat`) and the reading by `divN`. The orders `β₀`, `β₁` of (3) and the source indices
  of (4) are computed by `NegSSSP.cornerProg` from the positions of the boundary vertices on the
  face of the instance, which are an input (tied to the separator glue). The infrastructure of
  the composition of the runs of a node into one run: `WordRAM.Machine.Exec.mono_W` (word bound), `Exec.embed`/`Exec.lift`
  (`WordRAM/Machine/WordMono.lean`: a run in the memory `≤ W` on the registers of the program
  runs inside any larger configuration, keeping the other registers and the memory above `W`;
  `Stmt.toMem` reads the input words from memory instead), Bellman–Ford from any configuration
  holding the content of `bfStartP` and inside a larger one (`NegSSSP.bfFull_exec_any`,
  `NegSSSP.bfFull_exec_emb`), FR-Dijkstra at any base (`Monge.FR.mkPrmAt`) and inside a larger
  configuration (`Monge.FR.frProg_exec_emb`), Klein's program reading the one-face encoding from
  memory (`Klein.klein_exec_of_enc`, `Klein.klein_exec_enc_exists`), and a two-call example
  (`NegSSSP.fr_nrm_exec`: `frProg ; nrmProg`). **The Dijkstra half of a node is one run**
  (`NegSSSP.node_dij_exec`, `PlanarFlow/NegSSSP/NodeRun.lean`): on the plain encoding of the
  node held above the work space of FR-Dijkstra (above `NegSSSP.loB m w = 4 m + 18 w + 175`, in
  slots `Z + k (m + w + 1)`; the registers of the context `NegSSSP.NCtx` and the values `E` of
  Bellman–Ford on the boundary are inputs), `cProg` ; per part `NegSSSP.partProg` (the natural
  work space cleared, `pProg`, `aProg`, `csProg`, the arcs copied into the layout of `mkPrm`,
  the registers of `frProg` set, `frProg` by `NegSSSP.dijk_exec_emb`, `nrmProg`:
  `NegSSSP.part_exec`) ; `minProg`, within `2 cNegMach.dij (w + 1) (m + w) + 200 m + 450 w +
  70 b + 2700 ≤ 2 cNegMach.dij (w + 1) (m + w) + 1240 m + 2700` steps (the calls of Dijkstra at
  the `w + 1` vertex numbers of the node, not at the size of the part), writing the potential
  of `NegSSSP.step` at the vertex numbers when Bellman–Ford answers `some E`
  (`NegSSSP.node_dij_step`). Klein's calls start from the encoding of the one-face instance in
  memory: `NegSSSP.splitF_exec_enc` (`PlanarFlow/NegSSSP/FaceKleinEnc.lean`, `kleinProgMem`
  within three times the bound of `splitF_exec`; the encoding `KleinEnc` of the instance chosen
  by `SplitF` is an input, not computed from the node). **The whole node is one run**
  (`NegSSSP.node_exec`, `PlanarFlow/NegSSSP/NodeExec.lean`): `NegSSSP.nodeProg` = the boundary
  (`bdryProg`, listed by vertex number) ; the two parts (`NegSSSP.kPart`,
  `PlanarFlow/NegSSSP/NodeRunD.lean`: `cornerProg` from the positions of the boundary vertices on
  the face, the real constants of the encoding copied down, `kleinProgMem` from the encoding of
  the one-face instance in a slot (`NegSSSP.KSlot`), `rdProg` into the matrices of `bfStartP`;
  the part with the smaller work space of Klein's program first, `NegSSSP.kpair_exec`) ;
  `permProg` ; Bellman–Ford from the matrices (`NegSSSP.bfStage`,
  `PlanarFlow/NegSSSP/NodeRunE.lean`) ; `nodeDij`, in one configuration: there is an outcome
  `o`, a `PotOut` output of the union of the two dense distance graphs, such that for every `bf`
  answering `o` the run leaves the output of `NegSSSP.step` (`none`, or `f x` at the output slot
  for every vertex `x` of the node), within `1000 · cNegMach.node + 10000` steps for
  polynomially bounded reduced lengths (`NegSSSP.node_exec_cost_le`). Inputs of the run (not
  computed): the encodings of the one-face instances and the positions of the boundary vertices
  on their faces; the reduced lengths (`redProg`) are not needed by the run (the encodings carry
  the weights). The encodings by their properties (`PlanarFlow/NegSSSP/KEncVal.lean`,
  `PlanarFlow/NegSSSP/KEncPert.lean`): `NegSSSP.node_exec_val` is `node_exec` for **any**
  one-face instances of the two parts (`fd.q ≤ 18 m`, `fd.k² ≤ 1200 m`) and **any** encodings
  meeting `NegSSSP.FEncVal` (`Klein.KVal`: the hypotheses of `klein_exec_of_enc` on the words);
  `Klein.kval_kInputT` gives the explicit words (`Klein.kInputT`, word bound `Klein.kB`) for any
  layout, numbering and initial trees with orders. The lengths of the encoding there are
  `MSSP.pert`, perturbed by `Fintype.equivFin` (not computable); `NegSSSP.node_exec_valBy` is
  the same run with the perturbation by the numbering `σ` of the encoding (`MSSP.pertBy σ`,
  `NegSSSP.FEncValBy`, met by the explicit words: `NegSSSP.fencValBy_exists`). **On the concrete
  instances of the split** (`PlanarFlow/NegSSSP/KEncConcrete.lean`): the one-face instance of a
  side is a definition, `NegSSSP.sideFD` (the disc `discMap (kst N K) Z` of the side in the
  stellar subdivision of the piece map, its face `NegSSSP.discFace` the darts of the cycle
  oriented with the side inside, `NegSSSP.discCyc`, from the start `i₀` of the walk; explicit
  embeddings `sideE`, `sideJ`; `NegSSSP.sideFD_inst`); `NegSSSP.faceWalk_side`: `faceWalk`, from
  the plain encoding of the piece map and the marks of the side, writes for every source a
  position `t` whose dart of the walk leaves it (`NegSSSP.sideFD_pos`: a position on the face of
  `sideFD`); `NegSSSP.node_exec_side`: `node_exec_valBy` with `fd₀`, `fd₁` the instances
  `sideFD` of the two sides (`fd.q ≤ 18 m`, `fd.k² ≤ 1200 m` from `K ⊆ P` and the length of the
  cycle), the positions in the form `faceWalk_side` writes them. Pieces of the encoding on the
  machine: the real part of `KSlot` (`PlanarFlow/NegSSSP/KEncProg.lean`: `NegSSSP.kcProg`,
  within `36 |D| + 4 |V| + 4 k + 56` steps from the lengths (reals), the flags of the piece and
  the reach bits by dart number: the weights `tripWt`, labels `tripφ` and `tripL`, `tripTh`,
  `tripH0`, `NegSSSP.kcProg_kslot`; the perturbed lengths `pertBy σ`, of size `2^|D|`, stay
  reals); the reach bits (`PlanarFlow/NegSSSP/KEncReach.lean`: breadth-first search
  `NegSSSP.bfsProg`, within `35 nV + 17 m + 12` steps on out-lists, `NegSSSP.bfsProg_exec`, and
  on the out-lists of a piece the bits `Reach (pieceGraph M S ℓ) x y`,
  `NegSSSP.bfsProg_reach`). Not done: the input words of `kInputT` for `srcMap` of `sideFD`
  (the dart arrays, out-lists, the cotree, the orders; the region `ln` of `KInput` holds the
  perturbed lengths as words, `2^|D| ℓ + 2^(σ d)`, while the node has the reduced lengths as
  reals only, and the machine has no conversion from reals to words), and the initial tree (the
  shortest-path tree `tpar` of the perturbed lengths).
* `sep` (partly): the split of a connected piece by a short simple cycle
  (`NegSSSP.exists_cycle_cut`) is realized by `PlanarSeparator.MillerProg.sepRun prog`
  (`NegSSSP.sep_run_split`, `PlanarFlow/NegSSSP/SepGlue.lean`) from the plain encoding of the
  piece map `kmap N K` (`PlanarSeparator.MillerProg.Enc`) and the flags of `K`, for any program
  `prog` of steps 1–10 meeting `PlanarSeparator.MillerProg.Spec10`, within
  `326 m + 5 (nV + nF) + 4 log₂ n + T + 149` steps plus the `T` of `prog`, with the parts
  `side N K Z`, `side N K Zᶜ` meeting the conclusion of `exists_cycle_cut`
  (`exists_cycle_cut_of`). Miller's whole program meets `Spec10`
  (`PlanarSeparator.MillerProg.prog10_spec10`, `PlanarSeparator/Machine/SepProg10.lean`:
  `prog10 = setup10 ; millerFull ; marks01` within
  `T10 m n = (693 m + 60 n + 152) log₂ n + 5500 m + 850 n + 1700`, `n = nV + nF + m`, for
  `B₀ ≥ aEnd10 (3 m) n`), so the large-component split runs entirely on the machine:
  `NegSSSP.sep_run_split_full` (`PlanarFlow/NegSSSP/SepFull.lean`), within
  `(1746 |K| + 156) (log₂ |K| + 3) + 16772 |K| + 1849` steps. The plain encoding of the piece map
  of a component is computed from the plain encoding of the piece carrying its own rotation and
  the flags of the component (`NegSSSP.encProg_enc`, `PlanarFlow/NegSSSP/PieceEnc.lean`, within
  `116 k + 47` steps on `k` half-edges: compaction by ranks, the face permutation and its inverse,
  vertex and face numbers by orbit labelling `NegSSSP.orbProg_exec`), with the index of each
  half-edge of the component for `joinProg`. The positions on the face of the boundary vertices
  for `cornerProg` are computed by `NegSSSP.faceWalk` (`PlanarFlow/NegSSSP/FaceWalk.lean`, within
  `72 m + 13 k + 18` steps for a cycle of `k` darts): from the plain encoding of the piece map and
  the marks of `sepRun` (`NegSSSP.sep_run_cyc`, the run with its cycle exposed), it walks the
  darts of the stellar subdivision on the boundary of a side and writes the position of each
  vertex, which meets the hypothesis of `cornerProg_face` for the one-face instance of the side
  started at the first dart of the walk (`NegSSSP.faceWalk_faceInst`). The whole split of a piece
  is one program, `NegSSSP.splitProg` (`PlanarFlow/NegSSSP/SplitRun.lean`: `compProg`, then
  `grpProg`, or `encProg`, a copy of the encoding above the separator's word bound, `sepRun prog10`
  lifted into the configuration by `Exec.lift_trunc` (`NegSSSP.sep_run_lift`, keeping the memory
  above `B₀ + 25 k + 2` and the registers from `700` on), `joinProg` and `faceWalk` on both sides):
  `NegSSSP.splitProg_splitM`, its sides are those of `splitM N ord cut P` for the order of the
  darts on the machine and, in the large case, the cut read off the marks (meeting `CutOK`), with
  the positions on the face of both parts (`NegSSSP.PosInst`, the hypothesis of
  `cornerProg_face`), within `splitT k = (1746 k + 156) (log₂ k + 3) + 17237 k + 156 √(12 k) + 2964`
  steps on `k` half-edges. Not done: the one-face encoding (`KleinEnc` of the `srcMap` instance)
  computed from the part, and the decomposition used:
  `negDecF` is chosen by `Classical.choose`, not computed, so the realization is per split of a
  piece, not per node of `negDecF`.
* `leaf` of the maximum-flow recursion: the leaf solver `leafSolve` (a decision per dart from the
  ranks of its ends) is realized by `PlanarFlow.LeafFlow.prog` (`PlanarFlow/Machine/LeafFlow.lean`,
  within `25 n + 5` steps on `n` darts) on the darts and vertices numbered by `Fintype.equivFin`,
  hence within `C₀ n` steps when `C₀ ≥ 30` (`cMach_leaf_exec`).
* `NegCosts.leaf`: the leaf solver `leafBF` (Bellman–Ford with a final check on the piece) is
  realized by the program `PlanarFlow.BFList.prog` (Bellman–Ford
  on a list of arcs, values in the real memory, within `16 (N + 1)(m + 1)` steps; the flag is `1`
  exactly when a feasible potential exists, and the values are then `bf N`). The vertices and the
  darts of the piece are numbered, the arcs laid out by `BFList.start`, and the machine's digraph
  is isomorphic to `leafGraph` (`Digraph.Iso.bf`, `Digraph.Iso.isPot_iff`); with `N ≤ 2m` this is
  within `96 m²` steps (`NegSSSP.cNegMach_leaf_exec`).

## Main results

* `cMach_bounds`: `(cMach C C₀).Bounds (machK C) C₀`; `maxflow_plane_cost_mach`: the headline
  bound with these costs.
* `NegSSSP.cNegMach_bounds`: `(cNegMach C).Bounds (negK C)`.
* the realizations listed above.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

open Finset BKMNW

namespace NegSSSP

/-! ### The costs in the model of the negative-length shortest paths -/

/-- The constant of `cNegMach C`: Klein's program at a node (`32886 · 2372500000`, the largest
constant of a program) plus the parameter `C`. -/
def negK (C : ℕ) : ℕ := 32886 * 2372500000 + C

/-- **The costs of the recursion for negative lengths from the machine programs**: Klein's
program at a node (`splitF_exec`), FR-Dijkstra with one corner for Dijkstra (`frCost_le`),
Bellman–Ford over two dense distance graphs with missing arcs from their plain encoding
(`NegSSSP.bfFull`, `NegSSSP.bfCostP_le`), the bookkeeping programs of a node
(`NegSSSP.bdryProg`, `NegSSSP.redProg`, `NegSSSP.cProg`, `NegSSSP.pProg`, `NegSSSP.csProg`),
Bellman–Ford on a list of arcs for the leaf solver (`PlanarFlow.BFList.prog_exec`,
`16 (2m + 1)(m + 1) ≤ 96 m²` on a piece of `m ≥ 1` darts); the bookkeeping of a node is charged
`1000 m` (the part with a program, `NegSSSP.cNegMach_lin_exec_all`,
`NegSSSP.cNegMach_lin_glue_cost`); the separator has no program yet, with the constant `C` as a
parameter. -/
def cNegMach (C : ℕ) : NegCosts where
  sep m := C * m * lg m
  mssp m b := 32886 * 2372500000 * (m * lg m + b ^ 2 * lg m)
  bf b := 7900 * (b + 1) ^ 2 * lg b
  dij x p := 6300 * (x + p) * lg x
  lin m := 1000 * m
  leaf m := 96 * m ^ 2

lemma le_negK (C : ℕ) : C ≤ negK C ∧ 32886 * 2372500000 ≤ negK C := by
  unfold negK; omega

/-- **The machine costs meet `NegCosts.Bounds`** with `K' = negK C`. -/
theorem cNegMach_bounds (C : ℕ) : (cNegMach C).Bounds (negK C) where
  sep m := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_negK C).1)
  mssp m b := Nat.mul_le_mul_right _ (le_negK C).2
  bf b := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ((by norm_num : 7900 ≤ 32886 *
    2372500000).trans (le_negK C).2))
  dij x p := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ((by norm_num : 6300 ≤ 32886 *
    2372500000).trans (le_negK C).2))
  lin m := Nat.mul_le_mul_right _ ((by norm_num : 1000 ≤ 32886 * 2372500000).trans
    (le_negK C).2)
  leaf m := Nat.mul_le_mul_right _ ((by norm_num : 96 ≤ 32886 * 2372500000).trans (le_negK C).2)

/-! ### Multiple-source shortest paths at a node: Klein's program -/

section Mssp

open WordRAM WordRAM.Machine

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- **The two calls of multiple-source shortest paths at a node are realized by Klein's
program** within `cNegMach.mssp m b` steps each, `m` the darts of the node and `b` its shared
vertices (`splitF_exec`): at a node meeting `SplitF` with shared vertices, for each part `X`
there are a one-face instance and a run of `kleinProg` on it ending with the distances in the
part between the shared vertices in its output. The bound is at the size of the node, not of the
part (see the module docstring). -/
theorem cNegMach_mssp_exec (C : ℕ) {P P₀ P₁ : Finset D} (h : SplitF N P P₀ P₁)
    (hB : (bdry N P₀ P₁).Nonempty) {ℓ : D → ℤ} {X : Finset D} (hX : X = P₀ ∨ X = P₁)
    (hnn : ∀ d ∈ X, 0 ≤ ℓ d) :
    ∃ fd : FaceData N X (bdry N P₀ P₁), ∃ (n Bw : ℕ) (I : Input) (c₀ c' : Config) (steps : ℕ),
      Exec I (Bw + 16 * (n + 1))
        (Klein.kleinProg Bw (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k fd.k) c₀ c' steps ∧
      steps ≤ (cNegMach C).mssp P.card (bdry N P₀ P₁).card ∧
      (∀ b ∈ bdry N P₀ P₁, ∃ i < fd.k, fd.Q.tail (fd.g i) = fd.j b ∧
        ∀ b' ∈ bdry N P₀ P₁, ∃ i' < fd.k, fd.Q.tail (fd.g i') = fd.j b' ∧
          Klein.srcOut (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ))
            (Fintype.card (Klein.SrcD fd.DQ fd.k))
            (Klein.kOut (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k c' i i') =
          MSSP.odist (MSSP.pieceGraph N X ℓ) b b') ∧
      c'.output = c₀.output := by
  obtain ⟨fd, n, Bw, I, c₀, c', steps, hE, hs, hR, hout⟩ := splitF_exec h hB hX hnn
  refine ⟨fd, n, Bw, I, c₀, c', steps, hE, hs.trans ?_, hR, hout⟩
  show _ ≤ 32886 * 2372500000 * (P.card * lg P.card + (bdry N P₀ P₁).card ^ 2 * lg P.card)
  rw [mul_add, ← mul_assoc]
  exact Nat.le_add_right _ _

end Mssp

end NegSSSP

namespace BKMNW

/-! ### Dijkstra on explicit arcs: FR-Dijkstra with one corner -/

section Dij

variable {X : Type*} [DecidableEq X]

/-- The dense distance graph on one corner has no arcs. -/
lemma faceDDG_one_len (β : ℕ → X) (D : ℕ → ℕ → ℤ) (x y : X) :
    (faceDDG β 1 D).len x y = none := by
  have : ¬ ∃ p : Monge.Arc 1, β p.1.1 = x ∧ β p.1.2 = y := fun ⟨p, _⟩ =>
    p.2 (Subsingleton.elim _ _)
  simp only [faceDDG, this, ↓reduceDIte]

lemma arcsIn_empty_one (β : ℕ → X) (D : ℕ → ℕ → ℤ) (E : List (X × X × ℤ)) :
    ArcsIn ((emptyDDG (F := X)).union E) ((faceDDG β 1 D).union E) := by
  rintro (⟨_, h, -⟩ | e)
  · simp [emptyDDG] at h
  · exact ⟨.inr e, rfl, rfl, rfl⟩

lemma arcsIn_one_empty (β : ℕ → X) (D : ℕ → ℕ → ℤ) (E : List (X × X × ℤ)) :
    ArcsIn ((faceDDG β 1 D).union E) ((emptyDDG (F := X)).union E) := by
  rintro (⟨⟨x, y⟩, -, -, h⟩ | e)
  · rw [faceDDG_one_len] at h; exact absurd h (by decide)
  · exact ⟨.inr e, rfl, rfl, rfl⟩

end Dij

/-- The logarithm of the heaps (`0` at `0`) is at most `lg`. -/
lemma heap_lg_le (n : ℕ) : Heap.lg n ≤ lg n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp [Heap.lg, lg]
  · rw [Heap.lg_eq_log h]; rfl

end BKMNW

namespace NegSSSP

section Dij

open WordRAM WordRAM.Machine Monge.FR

variable {P : Prm} {I : Input}

/-- **Dijkstra with a price function on explicit arcs on the machine** (the calls charged
`NegCosts.dij`): `frProg` with one corner (`b = 1`) computes the distances from the root in
`emptyDDG.union arcs`, the explicit arcs of the input, within `cNegMach.dij N m` steps
(`6300 (N + m) lg N`), for a price function feasible on the arcs. The crossing inequality is
vacuous with one corner. -/
theorem cNegMach_dij_exec (C : ℕ) (hL : Lay P) (hb : P.b = 1) (h0 : P.off 0 = 0)
    (hm : 0 < P.m) (hp : ((emptyDDG (F := Fin P.N)).union (exArcs P hL.N_pos)).IsPot
      (fun y => P.p y))
    (c : Config) (hc : WordsBounded P.W c) (hin : Inp P c) (hDa : Data P c) :
    ∃ c' k, Exec I P.W frProg c c' k ∧ k ≤ (cNegMach C).dij P.N P.m ∧ Data P c' ∧
      c'.output = c.output ∧
      ∃ δ : Fin P.N → Option ℤ,
        IsDist ((emptyDDG (F := Fin P.N)).union (exArcs P hL.N_pos)) (fv P hL.N_pos P.r) δ ∧
        ∀ y : Fin P.N, (c'.nmem (P.sb + y) = 1 ↔ δ y ≠ none) ∧
          ∀ ℓ, δ y = some ℓ → c'.rmem (P.db + y) = ℓ := by
  have hDc : Monge.Crossing P.b P.D := by
    intro i i' j j' hi _ hi' _ _; omega
  have hlen : (exArcs P hL.N_pos).length = P.m := by simp [exArcs]
  have hA : Nonempty (Monge.Arc P.b ⊕ Fin (exArcs P hL.N_pos).length) :=
    ⟨.inr ⟨0, by omega⟩⟩
  have hb' := hb
  have hp' : ((faceDDG (fv P hL.N_pos) P.b P.D).union (exArcs P hL.N_pos)).IsPot
      (fun y => P.p y) := by
    rw [hb]; exact isPot_of_arcsIn (arcsIn_one_empty _ _ _) hp
  obtain ⟨c', k, e, hk, hDa', hO, δ, hδ, hmem⟩ :=
    frProg_isDist (I := I) hL h0 hDc hA hp' c hc hin hDa
  refine ⟨c', k, e, hk.trans ?_, hDa', hO, δ, ?_, hmem⟩
  · have h1 := frCost_le hL
    have hLv : P.Lv = 1 := by simp [Prm.Lv, hb]
    rw [hb, hLv] at h1
    have hN := hL.N_pos
    have hG : 1 ≤ lg P.N := one_le_lg _
    show _ ≤ 6300 * (P.N + P.m) * lg P.N
    have h2 : 150 * (P.N + P.m) * Heap.lg P.N ≤ 150 * (P.N + P.m) * lg P.N :=
      Nat.mul_le_mul_left _ (heap_lg_le _)
    have : 1 ≤ (P.N + P.m) * lg P.N := Nat.one_le_iff_ne_zero.2 (by positivity)
    have e : 6300 * (P.N + P.m) * lg P.N = 150 * (P.N + P.m) * lg P.N +
        6150 * ((P.N + P.m) * lg P.N) := by ring
    omega
  · rw [hb] at hδ
    exact isDist_of_arcsIn (arcsIn_one_empty _ _ _) (arcsIn_empty_one _ _ _) hδ

/-- **The layout of FR-Dijkstra with one corner can be met**: for every `N ≥ 1` vertices and
`m` explicit arcs, there is an input with `b = 1` meeting `Lay` (here with zero prices and
lengths). -/
theorem lay_one_exists {N m : ℕ} (hN : 1 ≤ N) (dst : ℕ → ℕ) (hdst : ∀ e < m, dst e < N) :
    ∃ P : Prm, Lay P ∧ P.b = 1 ∧ P.N = N ∧ P.m = m ∧ P.off 0 = 0 ∧ (∀ y, P.p y = 0) ∧
      ∀ e, P.len e = 0 := by
  refine ⟨Prm.mk N 1 m 0 1 (1 + N) (2 + 2 * N + m) (2 + 2 * N + 2 * m) (2 + 3 * N + 2 * m)
    (2 + 4 * N + 2 * m) (200 + 7 * N + 2 * m) (fun _ _ => 0) (fun _ => 0)
    (fun x => if x < N then 0 else m) dst (fun _ => 0) 0,
    ⟨le_rfl, hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdst⟩, rfl, rfl, rfl, ?_,
    fun _ => rfl, fun _ => rfl⟩
  all_goals try (simp <;> omega)
  · simp [Prm.Lv]; omega
  · simp [Prm.rb, Prm.bh, Prm.tb, Prm.hb, Prm.Lv, Prm.TB]; omega
  · intro x hx
    simp only
    split_ifs <;> omega


/-- **The starting configurations of `frProg` exist for every layout**: the registers of `Inp`,
the dense distance graph, the prices and the explicit arcs in the memory (`Data`), the words
bounded by `W`. -/
theorem exists_frConfig (hL : Lay P) : ∃ c : Config, WordsBounded P.W c ∧ Inp P c ∧ Data P c := by
  have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  have hw := hL.w
  have hb := hL.b_pos
  have hbN := hL.bN
  have hr := hL.r_lt
  have hoff : ∀ k x, x + k = P.N → P.off x ≤ P.m := by
    intro k
    induction k with
    | zero => intro x hx; rw [add_zero] at hx; rw [hx, hL.off_last]
    | succ k ih => intro x hx; exact (hL.off_mono x (by omega)).trans (ih (x + 1) (by omega))
  have hdst := hL.dst_lt
  refine ⟨Config.mk 0
    (fun r => if r = 100 then P.N else if r = 101 then P.b else if r = 102 then P.Db
      else if r = 103 then P.pb else if r = 104 then P.ob else if r = 105 then P.lb
      else if r = 106 then P.r else if r = 107 then P.sb else if r = 108 then P.db
      else if r = 109 then P.wb else 0)
    (fun _ => 0)
    (fun a => if P.ob ≤ a ∧ a ≤ P.ob + P.N then P.off (a - P.ob)
      else if P.ob + P.N + 1 ≤ a ∧ a < P.ob + P.N + 1 + P.m then P.dst (a - (P.ob + P.N + 1))
      else 0)
    (fun a => if P.Db ≤ a ∧ a < P.Db + P.b * P.b then
        ((P.D ((a - P.Db) / P.b) ((a - P.Db) % P.b) : ℤ) : ℝ)
      else if P.pb ≤ a ∧ a < P.pb + P.N then ((P.p (a - P.pb) : ℤ) : ℝ)
      else if P.lb ≤ a ∧ a < P.lb + P.m then ((P.len (a - P.lb) : ℤ) : ℝ) else 0)
    [], ⟨fun r => ?_, fun a => ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨fun i j hi hj => ?_, fun x hx => ?_, fun x hx => ?_, fun e he => ?_, fun e he => ?_⟩⟩
  all_goals dsimp only
  · split_ifs <;> omega
  · split_ifs with h1 h2
    · have := hoff (P.N - (a - P.ob)) (a - P.ob) (by omega); omega
    · have := hdst (a - (P.ob + P.N + 1)) (by omega); omega
    · omega
  all_goals try (simp; done)
  · have h1 : i * P.b + j < P.b * P.b := by nlinarith
    have e1 : (i * P.b + j) / P.b = i := by
      rw [add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hj, zero_add]
    have e2 : (i * P.b + j) % P.b = j := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    rw [ite_eq_left ⟨by omega, by omega⟩, show P.Db + i * P.b + j - P.Db = i * P.b + j by omega, e1,
      e2]
  · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
  · rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
  · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩,
      Nat.add_sub_cancel_left]

/-- **The hypotheses of `cNegMach_dij_exec` can be met**: a layout with one corner, an explicit
arc, a feasible price function and a starting configuration. -/
theorem cNegMach_dij_exec_hyps :
    ∃ (P : Prm) (hL : Lay P) (c : Config), P.b = 1 ∧ P.off 0 = 0 ∧ 0 < P.m ∧
      ((emptyDDG (F := Fin P.N)).union (exArcs P hL.N_pos)).IsPot (fun y => P.p y) ∧
      WordsBounded P.W c ∧ Inp P c ∧ Data P c := by
  obtain ⟨P, hL, hb, -, hm, h0, hp, hl⟩ := lay_one_exists (N := 1) (m := 1) le_rfl (fun _ => 0)
    (fun _ _ => Nat.one_pos)
  obtain ⟨c, h1, h2, h3⟩ := exists_frConfig hL
  refine ⟨P, hL, c, hb, h0, by omega, ?_, h1, h2, h3⟩
  rintro (⟨_, h, -⟩ | e)
  · simp [emptyDDG] at h
  · simp [DDG.union, exArcs, hp, hl, Sum.elim]

end Dij

end NegSSSP

namespace BKMNW

/-! ### The costs of the maximum-flow recursion -/

/-- The constant of `cMach C C₀`: `1010921 · negK C`. -/
def machK (C : ℕ) : ℕ := 1010921 * NegSSSP.negK C

/-- **The counted cost of negative-length shortest paths fits the budget of `SubCosts`**: for
`K ≥ 1010921 K'`, `10920 K' m lg² m + 1000001 K' m ≤ K m lg² m` (the form of
`PlanarFlow.BKMNW.negSSSPImpl_cost` under `NegCosts.Bounds K'`). -/
theorem negsssp_field_le {K K' : ℕ} (hK : 1010921 * K' ≤ K) (m : ℕ) :
    10920 * K' * m * lg m ^ 2 + 1000001 * K' * m ≤ K * m * lg m ^ 2 := by
  have h1 : K' * m ≤ K' * m * lg m ^ 2 :=
    Nat.le_mul_of_pos_right _ (by have := one_le_lg m; positivity)
  have h2 : 1010921 * K' * m * lg m ^ 2 ≤ K * m * lg m ^ 2 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hK)
  nlinarith

/-- **The subroutine costs of the machine programs** (see the module docstring for the status of
each field): the perturbed s-t flow program (`504000000 m lg m`), FR-Dijkstra
(`6300 (x lg² x + p lg x)`), the counted cost of the recursion for negative lengths with the
costs `cNegMach C`, Klein's program with masked queries for MSSP (`cMach_mssp_exec`); the separator
(`C m lg m`), the bookkeeping (`C m`) and the leaf solver (`C₀ m`) as parameters. -/
def cMach (C C₀ : ℕ) : SubCosts where
  leaf m := C₀ * m
  sep m := C * m * lg m
  mssp m k := 24637500000 * (m * lg m + k ^ 2 * lg m)
  fr x p := 6300 * (x * lg x ^ 2 + p * lg x)
  negsssp m := 10920 * NegSSSP.negK C * m * lg m ^ 2 + 1000001 * NegSSSP.negK C * m
  stflow m := 504000000 * (m * lg m)
  lin m := C * m

lemma le_machK (C : ℕ) : C ≤ machK C ∧ 504000000 ≤ machK C := by
  have := NegSSSP.le_negK C
  unfold machK; omega

/-- **The machine costs meet `SubCosts.Bounds`** with `K = machK C = 1010921 · negK C` and
`K₀ = C₀`. -/
theorem cMach_bounds (C C₀ : ℕ) : (cMach C C₀).Bounds (machK C) C₀ where
  leaf m := le_rfl
  sep m := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_machK C).1)
  mssp m k := Nat.mul_le_mul_right _ (by
    have := (NegSSSP.le_negK C).2
    unfold machK; omega)
  fr x p := Nat.mul_le_mul_right _ ((by norm_num : 6300 ≤ 504000000).trans (le_machK C).2)
  negsssp m := negsssp_field_le le_rfl m
  stflow m := by
    show 504000000 * (m * lg m) ≤ machK C * m * lg m ^ 2
    have h1 : m * lg m ≤ m * lg m ^ 2 := Nat.mul_le_mul_left _ (SubCosts.lg_le_sq m)
    calc 504000000 * (m * lg m) ≤ machK C * (m * lg m ^ 2) :=
          Nat.mul_le_mul (le_machK C).2 h1
      _ = machK C * m * lg m ^ 2 := by ring
  lin m := Nat.mul_le_mul_right _ (le_machK C).1

universe w

/-- **The counted cost of `negSSSPImpl` with the machine costs**: on every plane map with
transitive rotations and faces and `n` darts, the counted cost of the recursion for negative
lengths with the costs `cNegMach C` is at most `cMach.negsssp n`. -/
theorem negSSSPImpl_cost_mach (fr : (X : Type w) → [Fintype X] → [DecidableEq X] → FRFun X)
    (C C₀ : ℕ) {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) :
    NegSSSP.negDecFCost M.dual (NegSSSP.cNegMach C) ≤ (cMach C C₀).negsssp (Fintype.card D) :=
  (negSSSPImpl_cost fr hM hrot hface (NegSSSP.cNegMach_bounds C)).2.2

section Main

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The headline with the machine costs**: `maxflow_plane_cost` for the costs `cMach C C₀`,
with `K = machK C`. The bound holds for all `C` and `C₀`, the constants of the separator, the
bookkeeping and the leaf solver, which have no machine program yet. -/
theorem maxflow_plane_cost_mach (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) (C C₀ : ℕ) :
    ∃ τ : ADec (lpreMap M),
      BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) ∧
      runLCost (lpreMap M) (cMach C C₀) τ ≤
        (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) :=
  maxflow_plane_cost hM hrot hface hu hST (cMach_bounds C C₀)

end Main

/-! ### The s-t flow oracle on the machine -/

section STFlow

open WordRAM WordRAM.Machine Orbit

open Classical in
/-- **Every call of the s-t flow oracle is realized on the machine within `cMach.stflow m`
steps, with numbers of polynomial size**: on a plane map with transitive rotations and faces and
`m` darts, with nonnegative capacities, a nonempty source set and a sink set reached by a dart,
disjoint, there are an input, a word bound and a starting configuration from which
`PlanarFlow.STFlow.pstProg` runs within `cMach.stflow m = 504000000 m lg m` steps and ends with
the flow of the oracle of `planeOracles` (`PlanarFlow.STFlow.pstflowW`, the word-size
perturbation) in its output region; every real memory cell of the starting configuration is an
integer of absolute value at most `isoW_bound = (m + 4) (2 R + 1) (Σ c + 1)` (`c` the capacities
the oracle runs on, `capR`), and so are the numbers of the run
(`PlanarFlow.STFlow.isoKeys_bounded`). -/
theorem cMach_stflow_exec (fr : (X : Type w) → [Fintype X] → [DecidableEq X] → FRFun X)
    (C C₀ : ℕ) {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) {X Y : Finset V} (hX : X.Nonempty)
    (hY : ∃ d, M.tail d ∈ Y) (hXY : Disjoint X Y) :
    ∃ (n B : ℕ) (P : Input) (c₀ c' : Config) (steps : ℕ),
      n = 2 * (Fintype.card F + Fintype.card V + Fintype.card D) ∧
      Exec P (B + 16 * (n + 1)) (STFlow.pstProg B (Fintype.card D) n) c₀ c' steps ∧
      steps ≤ (cMach C C₀).stflow (Fintype.card D) ∧
      (∀ d, c'.rmem (STFlow.aOT (Fintype.card D) + Fintype.equivFin D d) =
        (planeOracles fr).stflow M c X Y d) ∧
      c'.output = c₀.output ∧
      ∀ a, ∃ z : ℤ, c₀.rmem a = z ∧ |z| ≤ STFlow.isoW_bound D V F (STFlow.capR M c X Y) :=
  STFlow.pstflowW_exec_exists hM hrot hface hc hX hY hXY

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

open Classical in
/-- **The calls of the s-t flow oracle on the piece maps**: on the piece map `pmap h` of a piece
`P` with holes `Hs` (connected after contracting the holes, `HConn`, with a dart), the call of
the oracle in `PlanarFlow.BKMNW.c2sImpl` (nonnegative capacities, a nonempty source set, a sink
set reached by a dart, disjoint) is realized by a run of `pstProg` within `cMach.stflow n` steps,
`n` the darts of the piece map, the size at which `arunLCost` charges it. -/
theorem cMach_stflow_exec_piece (fr : (X : Type w) → [Fintype X] → [DecidableEq X] → FRFun X)
    (C C₀ : ℕ) {P : Finset D} {Hs : List (Finset V)} {σ : Equiv.Perm D} (h : PieceInv M P Hs σ)
    (hcon : HConn M P Hs) {x₀ : D} (hx₀ : x₀ ∈ pdarts M P Hs)
    {c : SDart (pdarts M P Hs) → ℤ} (hc : ∀ d, 0 ≤ c d)
    {X Y : Finset (SVert σ (pdarts M P Hs))} (hX : X.Nonempty) (hY : ∃ d, (pmap h).tail d ∈ Y)
    (hXY : Disjoint X Y) :
    ∃ (n B : ℕ) (I : Input) (c₀ c' : Config) (steps : ℕ),
      n = 2 * (Fintype.card (SFace σ (pdarts M P Hs) (revPerm M)) +
        Fintype.card (SVert σ (pdarts M P Hs)) + Fintype.card (SDart (pdarts M P Hs))) ∧
      Exec I (B + 16 * (n + 1))
        (STFlow.pstProg B (Fintype.card (SDart (pdarts M P Hs))) n) c₀ c' steps ∧
      steps ≤ (cMach C C₀).stflow (pdarts M P Hs).card ∧
      (∀ d, c'.rmem (STFlow.aOT (Fintype.card (SDart (pdarts M P Hs))) +
          Fintype.equivFin (SDart (pdarts M P Hs)) d) =
        (planeOracles fr).stflow (pmap h) c X Y d) ∧
      c'.output = c₀.output ∧
      ∀ a, ∃ z : ℤ, c₀.rmem a = z ∧ |z| ≤ STFlow.isoW_bound (SDart (pdarts M P Hs))
        (SVert σ (pdarts M P Hs)) (SFace σ (pdarts M P Hs) (revPerm M))
        (STFlow.capR (pmap h) c X Y) := by
  obtain ⟨hpl, hrot, hface⟩ := h.isPlane hcon hx₀
  obtain ⟨n, B, I, c₀, c', steps, hn, e, hs, hout, ho, hw⟩ :=
    cMach_stflow_exec fr C C₀ (M := pmap h) hpl hrot hface hc hX hY hXY
  exact ⟨n, B, I, c₀, c', steps, hn, e, by rwa [Fintype.card_coe] at hs, hout, ho, hw⟩

end STFlow

/-! ### FR-Dijkstra, given the crossing inequality -/

section FR

open WordRAM WordRAM.Machine Monge.FR

variable {P : Prm} {I : Input}

/-- **FR-Dijkstra on the machine within `cMach.fr N m` steps, given the crossing inequality**:
`frProg` computes the distances in the union of one dense distance graph and the explicit arcs
within `6300 (N lg² N + m lg N)` steps (`frProg_isDist`, `PlanarFlow.Monge.FR.frCost_le_fr`).
The crossing (Monge) inequality of the lengths is a hypothesis, not yet proved for the dense
distance graphs of the algorithm: the calls of the algorithm are not yet realized. -/
theorem cMach_fr_exec (C C₀ : ℕ) (hL : Lay P) (h0 : P.off 0 = 0)
    (hDc : Monge.Crossing P.b P.D)
    (hA : Nonempty (Monge.Arc P.b ⊕ Fin (exArcs P hL.N_pos).length))
    (hp : ((faceDDG (fv P hL.N_pos) P.b P.D).union (exArcs P hL.N_pos)).IsPot (fun y => P.p y))
    (c : Config) (hc : WordsBounded P.W c) (hin : Inp P c) (hDa : Data P c) :
    ∃ c' k, Exec I P.W frProg c c' k ∧ k ≤ (cMach C C₀).fr P.N P.m ∧ Data P c' ∧
      c'.output = c.output ∧
      ∃ δ : Fin P.N → Option ℤ,
        IsDist ((faceDDG (fv P hL.N_pos) P.b P.D).union (exArcs P hL.N_pos)) (fv P hL.N_pos P.r) δ ∧
        ∀ y : Fin P.N, (c'.nmem (P.sb + y) = 1 ↔ δ y ≠ none) ∧
          ∀ ℓ, δ y = some ℓ → c'.rmem (P.db + y) = ℓ := by
  obtain ⟨c', k, e, hk, hDa', hO, hδ⟩ := frProg_isDist (I := I) hL h0 hDc hA hp c hc hin hDa
  refine ⟨c', k, e, (hk.trans (frCost_le_fr hL)).trans ?_, hDa', hO, hδ⟩
  have := heap_lg_le P.N
  show _ ≤ 6300 * (P.N * lg P.N ^ 2 + P.m * lg P.N)
  gcongr

end FR

end BKMNW

end PlanarFlow
