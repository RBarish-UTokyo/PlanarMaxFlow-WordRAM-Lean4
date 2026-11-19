module

public import PlanarSeparator.Machine.MillerComp
public import PlanarSeparator.Machine.MillerHeavy
public import PlanarSeparator.Machine.MillerTest
public import PlanarSeparator.Machine.MillerLast
public import PlanarSeparator.Machine.MillerConc
public import PlanarSeparator.Machine.MillerThin
public import PlanarSeparator.Machine.MillerDart
public import PlanarSeparator.Machine.MillerBFS
public import PlanarSeparator.Machine.MillerInner
public import PlanarSeparator.Machine.MillerInC
public import PlanarSeparator.Machine.MillerJump
public import PlanarSeparator.Machine.MillerS8Run

/-!
# Miller's simple cycle separator on the machine: the plan

This file records the route by which Miller's theorem for triangulations
(`PlanarSeparator.Map.exists_short_cycle_separator`: a simple cycle of at most `6 √n + 4` darts
bounding a set of faces `Z` whose strict inside and strict outside weigh at most `2/3` each) is
to be computed by a program for the machine `WordRAM`, and which parts are proved so far. Each
step names the proved lemma whose hypotheses it establishes or whose construction it follows.

## The data

A plane map all of whose faces are triangles, with `n` vertices and `k` faces, is held *coded*
as in `PlanarSeparator/Machine/Search.lean` and `PlanarSeparator.CycleSearch.Coded`: the darts
are `0, …, 3 k - 1`, the darts of face `f` are `3 f, 3 f + 1, 3 f + 2` (the face permutation is
`CycleSearch.phi3`), and the arrays are the reversal `A x` and the vertex `V x` of each dart, with
natural vertex weights `w v`. The rotation at a vertex is `x ↦ phi3 (A x)`. In this format the
fundamental cycle search of Lipton and Tarjan (`CycleSearch.cycleSep`), the dual tree and the
marks of the faces inside a fundamental cycle (`PlanarSeparator/Machine/InMark.lean`) already
run without change.

## The steps

1. **Breadth-first search** from vertex `0` along the darts at each vertex: levels `L v` and
   parent darts, giving a spanning tree `T` with `IsBFS T` (the conditions `IsBFS.step`,
   `IsBFS.parent`, `IsBFS.root`; compare `PlanarSeparator.Map.exists_bfs`). The existing search
   (`PlanarSeparator/Machine/BFS.lean`) reads darts grouped by vertex; on the coded format the
   darts at every vertex are first linked into lists. **Proved**: `MillerProg.bprog_exec` and
   `MillerProg.bprog_tree` (`PlanarSeparator/Machine/MillerBFS.lean`, within `19 n + 90 k + 14`
   steps the levels at `bLv` are the heights of a breadth-first tree `T` rooted at the vertex
   numbered `0`, and its parent darts are at `bPr`); and a dart at every vertex,
   `MillerProg.dpass_exec` (`PlanarSeparator/Machine/MillerDart.lean`, within `21 k + 4` steps,
   read as darts `fdD v` at the vertices `v` by `MillerProg.dpass_dart`).
2. **Level counts and `t = ⌊√n⌋`**, as `lstat` and `sqrtL` of
   `PlanarSeparator/Machine/LevelStat.lean`: the programs `lcnt` and `msqrt` of
   `PlanarSeparator/Machine/MillerThin.lean` (proved with step 5).
3. **The heavy test at a level `l`** (`PlanarSeparator.Map.Heavy`): the faces avoiding the
   levels `< l` (the faces off `zone (T.low l)`: all three corners of level `≥ l`) are flagged,
   and their components (`PlanarSeparator.Map.comp`) are labelled by the program `clab`
   (`PlanarSeparator/Machine/MillerComp.lean`, **proved**: `MillerProg.clab_exec`, within
   `68 k + 4` steps, the labels are exactly the classes of adjacency through flagged faces).
   The strict inside of a component at level `l ≥ 1` consists of the vertices of level `> l`
   whose faces lie in it (`PlanarSeparator.Map.lt_of_mem_ins`,
   `PlanarSeparator.Map.mem_ins_of_lt`), so one pass over the vertices adds each weight of a
   vertex of level `> l` to the label of the face of any of its darts; the level is heavy if
   some label weighs more than `2/3` of the total. **Proved**: the labels of `clab` are the
   components `comp` through the coding (`MillerProg.label_eq_iff`), and the heavy test in
   these terms (`MillerProg.heavy_iff`, for the weights `w v / Σ w`), and the program `hvy`
   (`PlanarSeparator/Machine/MillerTest.lean`: flags, `clab`, weights of the labels; proved:
   `MillerProg.hvy_exec`, within `101 k + 21 n + 11` steps the flag is the numeric test), and
   together: **`MillerProg.hvy_heavy`**, the flag of `hvy` is `1` if and only if the level is
   `Heavy`, for a coded triangulation whose levels, first darts and weights are in memory.
4. **The last heavy level `ls`**: heavy levels form an initial segment
   (`PlanarSeparator.Map.heavy_mono`) below `n` (`PlanarSeparator.Map.heavy_lt`), so a binary
   search over `[1, n)` finds `ls` with `O(log n)` heavy tests. This is the only step that is not
   linear: the program runs in `O(n log n)` steps. **Proved**: `MillerProg.bsearch_exec`
   (`PlanarSeparator/Machine/MillerLast.lean`), within `(106 k + 21 n + 30) ⌈log₂ n⌉ + 5` steps
   a level `ls < n` that is `0` or heavy, with no heavy level above it.
5. **Thin levels**: `l₂ = ls + 1 + j₂` and, if `ls > t`, `l₀ = ls - t + j₀`, with
   `(t + 1) #(level) ≤ n` (`PlanarSeparator.Map.exists_small_level`), found as by `findJ` and
   `findJ'` of `PlanarSeparator/Machine/LevelStat.lean`. **Proved**: `MillerProg.thin_exec`
   (`PlanarSeparator/Machine/MillerThin.lean`), within `24 n + 16 ⌊√n⌋ + 43` steps
   `t = ⌊√n⌋`, and `j₂, j₀ ≤ t` with `(t + 1) #(T.lvl l) ≤ n` at both levels.
6. **The inner region** (`PlanarSeparator.Map.Inner`): if `ls ≤ t`, all faces with the tree `T`
   (`PlanarSeparator.Map.inner_univ`); otherwise the heaviest component `H` at level `l₀`
   (labels of step 3 at `l₀`), its boundary cycle `C` (the darts with exactly one side in `H`,
   chained by turning around their heads; `PlanarSeparator.Map.IsPlane.exists_scycle_comp`) and
   the tree `T₁` redirected along `C` (`PlanarSeparator.Map.SpTree.arcTree`,
   `PlanarSeparator.Map.exists_inner_comp`). The construction is made explicit in
   `PlanarSeparator/MillerInner.lean` (**proved**: `PlanarSeparator.Map.inner_explicit`): for any
   dart `x₀` leaving `H`, the inner region has `c₀` the vertex of `x₀`, `K₀` the vertices of the
   darts leaving `H`, and `T₁` the tree whose parent dart at the head of every dart `x` leaving
   `H` (other than the vertex of `x₀`) is `α x`, and that of `T` elsewhere; so one pass over the
   darts computes `T₁` from the labels of step 3 at `l₀`. **Proved**: `MillerProg.iprog_inner`
   (`PlanarSeparator/Machine/MillerInner.lean`, at a heavy level `l₀ ≥ 1`, within
   `247 k + 39 n + 33` steps the parent darts of `T₁` of an inner region are at `bPr` and the
   number of `c₀` in `r240`). The case `l₀ = 0` keeps `T` (`PlanarSeparator.Map.inner_univ`).
7. **Concentrated weights** at `l₂` (`PlanarSeparator.Map.wc`): the components at `l₂` by
   `clab`, a representative vertex of level `> l₂` for each label, and the weights of each
   component moved to it. The band theorem holds for any representatives: for any concentration
   map (`PlanarSeparator.Map.IsConc`) and the weights it moves (`PlanarSeparator.Map.wcf`),
   **proved**: `PlanarSeparator.Map.exists_band_separator_of`, and from any balanced dart,
   `PlanarSeparator.Map.band_separator_of_dart`. The program `cprog`
   (`PlanarSeparator/Machine/MillerConc.lean`: the heavy test at `l₂` for the labels and their
   weights, a representative per label, then the image and the moved weight of every vertex);
   **proved**: `MillerProg.conc_exec`, within `106 k + 59 n + 26` steps the images at `bCN` are
   a concentration map and the numbers at `bWC` its moved weights.
8. **A balanced simple fundamental cycle** of `T₁` for the concentrated weights
   (`PlanarSeparator.Map.SpTree.exists_simple_balanced`): the descent of
   `PlanarSeparator.Map.SpTree.exists_simple_balanced_of_lt` from a dart, passing to the heavier
   of `α φ δ`, `α φ² δ` for the weights of the *strict* insides `inC`. Unlike the face weights of
   the descent of Lipton and Tarjan (`PlanarSeparator/Machine/Walk.lean`), the strict inside
   weights need, for each dart, the weight of the tree path from the apex of its triangle up to
   the cycle (`bset`), that is root path sums and lowest common ancestors. **Proved (the
   mathematics)**: the recursion is exact, `inC δ = inC a₁ ⊔ inC a₂ ⊔ bset δ`
   (`PlanarSeparator.Map.SpTree.inC_eq_union`, `sum_inC`, `PlanarSeparator/CycleWeight.lean`, from
   the disjointness of the insides of the two children, `disjoint_inside`), and
   `bset δ` is the set of the vertices of the two child cycles and the apex off the cycle of `δ`
   (`bset_eq`); the weight of a fundamental cycle is `rs x + rs z - 2 rs l + w l` from the root
   sums `rs` and the lowest common ancestor `l` (`sum_cycV`, with `anc_inter_anc`, `cycV_eq_anc`).
   The weight of `bset δ` from root sums and the three lowest common ancestors of the corners is
   `sum_bset` (two of them coincide, `tripod`; `bset δ` is the path from `y` up to the third, the
   center, and, when the center is the ancestor `p` of `x` and `z`, also the segment above `p`):
   the mathematics of the computation is complete. **Proved (the programs)**:
   * root sums and depths (`PlanarSeparator/Machine/MillerRoot.lean`): given an order of the
     vertices with parents first (`MillerProg.IsOrd`), one pass `rspass` stores the parent, the
     depth and the root sum of every vertex within `28 n + 3` steps (`MillerProg.rspass_exec`;
     for a spanning tree read through the coding, `MillerProg.rspass_tree`: `vi (T.parent v)`,
     `#(T.anc v) - 1` and `∑ u ∈ T.anc v, w u`). The order is a hypothesis: the queue of the
     breadth-first search of step 1 is such an order, but `MillerProg.bprog_exec` does not export
     it yet;
   * lowest common ancestors by binary lifting (`PlanarSeparator/Machine/MillerLCA.lean`):
     `L ≥ 1` with `n ≤ 2 ^ L`, `L ≤ log₂ n + 1` (`MillerProg.lgprog_exec`, `4 log₂ n + 4` steps), the table of
     the `2 ^ j`-th ancestors (`MillerProg.tbuild_exec`, `(9 n + 8) L + 5` steps) and the query
     (`MillerProg.lcaq_exec`, `25 L + 26` steps, the lowest common ancestor in the numeric sense
     `MillerProg.IsLCA`); for a spanning tree it is the deepest common ancestor
     (`MillerProg.isLCA_tree`), and for the ends of a dart `lca T δ` (`MillerProg.isLCA_lca`,
     `MillerProg.lcaq_lca`);
   * the strict inside weights (`PlanarSeparator/Machine/MillerInC.lean`): after the search of
     the dual tree of `PlanarSeparator/Machine/Search.lean`, `bpass` stores the weight of
     `bset (pd F)` (three queries per face; `MillerProg.bform_eq`) in place of the face weights,
     within `(75 L + 125) k + 3` steps (`MillerProg.bpass_exec`), and the pass of Lipton and Tarjan
     (`PlanarSeparator/Machine/Pass.lean`) then computes `W (inC (pd F))` for every face `F ≠ 0`
     (`MillerProg.inC_exec`, numeric; `MillerProg.recHoldsC`, the recurrence from `sum_inC`;
     **`MillerProg.inC_tree`**, for a coded plane triangulation, within `(75 L + 187) k + 6`
     steps). Every dart off the tree is `pd F` or the reverse of one
     (`PlanarSeparator.CycleSearch.Coded.pdor`), and `inC (α δ) = outC δ`, whose weight is
     `W − W (inC δ) − W (cycV δ)` (`sum_inC_add_sum_outC`, `sum_cycV`).
   * the walk (`PlanarSeparator/Machine/MillerWalk.lean`): the strict inside weight of any dart off
     the tree (`MillerProg.IvM`: `J` of its face, or the complement `tot − J − W (cycV)` with one
     query), and the descent of `exists_simple_balanced_of_lt` (`MillerProg.mwalk_exec`, within
     `(50 L + 160) (k + 1) + 50 L + 142` steps, for the rules `MillerProg.MWH`);
   * **step 8 on the machine** (`PlanarSeparator/Machine/MillerStep8.lean`): the program
     `MillerProg.step8` (`bpass`, the pass, the total weight `wsum`, the walk) and
     **`MillerProg.step8_tree`**: after the search of the dual tree, within
     `(125 L + 347) k + 6 n + 100 L + 312` steps, `r353` is a dart `δ` off the tree with
     `3 W (inC δ) ≤ 2 W` and `3 W (outC δ) ≤ 2 W`, the conclusion of `exists_simple_balanced`;
   * the inputs: the tree marks at `3 k + x` and clear face marks from the parent darts
     (`PlanarSeparator/Machine/MillerMarks.lean`, `MillerProg.tmpass_exec`, `20 k + 13 n + 9`
     steps, and `MillerProg.coded_of_tmark`: the coding is `CycleSearch.Coded`; the reversals are
     those of the Miller programs with `bR = 0`, and the Miller arrays lie above `11 k`); the
     parents at `bU` and the depths and root sums of any tree without an order, by pointer
     jumping along the table (`PlanarSeparator/Machine/MillerJump.lean`, `MillerProg.upass_exec`,
     `MillerProg.jpass_exec`, `(30 n + 10) L + 22 n + 10` steps, `MillerProg.jpass_tree`). The
     breadth-first order of step 1 would serve `rspass` for the tree `T`, but not for the
     redirected tree `T₁` of step 6, hence the order-free pass.
   * **one program for step 8** (`PlanarSeparator/Machine/MillerS8Run.lean`):
     `MillerProg.step8run = tmpass ; search ; upass ; lgprog ; tbuild ; jpass ; step8` from the
     parent darts of any spanning tree and natural weights; **`MillerProg.step8run_tree`**: within
     `(125 log₂ n + 564) k + (39 n + 122) log₂ n + 94 n + 468` steps, a dart off the tree whose
     strict inside and outside weigh at most `2/3` of the total; and with the redirected tree
     `T₁` of `iprog_inner` and the moved weights at `bWC` of `conc_exec`
     (**`MillerProg.step8run_conc`**), the hypotheses `hA`, `hB` of
     `PlanarSeparator.Map.band_separator_of_dart` for the normalized moved weights `wcf cn (wR wP)`.
   * **steps 1–8 as one program** (`PlanarSeparator/Machine/MillerA.lean`):
     `MillerProg.millerA = bprog ; dpass ; wsum ; bsearch ; thin ; innerStep ; concStep ;
     step8run` (with the register moves between them), the layout `MillerProg.ALay` (the
     reversals at `0`, the cycle search below `11 k`, the Miller arrays above) and the starting
     registers `MillerProg.ARegs`. `MillerProg.innerStep` runs `iprog` at
     `l₀ = ls - ⌊√n⌋ + j₀` if `⌊√n⌋ < ls` (the level `l₀` is heavy by `heavy_mono`) and keeps
     `T₁ = T`, `l₀ = 0` otherwise (`MillerProg.innerStep_exec`); `MillerProg.concStep` runs
     `cprog` at `l₂ = ls + 1 + j₂` if `l₂ < n` and copies the weights otherwise (the identity is
     a concentration map there; `MillerProg.concStep_exec`). **`MillerProg.millerA_spec`**: within
     `(231 log₂ n + 1134) k + (60 n + 152) log₂ n + 278 n + 637` steps, the breadth-first tree
     `T`, the levels `l₀ ≤ ls < l₂` with their bounds, the inner region and the parent darts of
     `T₁` at `bPr`, the concentration map `cn` and its moved weights at `bWC`, and the dart `δ`
     in `r353` with the hypotheses `hδ`, `hA`, `hB`, `hlight` of
     `PlanarSeparator.Map.band_separator_of_dart`; **`MillerProg.millerA_band`** applies it.
9. **The case analysis of the band theorem** (`PlanarSeparator.Map.exists_band_separator`).
   **Proved (the mathematics, with every choice explicit)**: `PlanarSeparator/BandExplicit.lean`
   defines the separator `PlanarSeparator.Map.bandSep T T₁ l₂ cn w δ x₀ g₀` from the balanced
   dart `δ` of step 8 (with `x₀` a dart leaving the component of `δ` at `l₂` and `g₀` a face
   touching the levels `< l₂`, e.g. at a dart of the root), and
   **`PlanarSeparator.Map.band_separator_explicit`** proves for it the conclusion of
   `PlanarSeparator.Map.band_separator_of_dart`. A dart with a face off `H` is impossible
   (`PlanarSeparator.Map.faces_mem_H`); in the band case the separator is the fundamental cycle
   of `δ` in `T₁` with its inside; in the deep case (`PlanarSeparator.Map.deepSep`,
   `PlanarSeparator.Map.deep_explicit`) the boundary cycle of the component `Y` is obtained by
   turning from `x₀` (`PlanarSeparator.Map.bdCycle`, darts `bdD`, length `bdK`), the ancestors
   at level `l₂` of the ends are the first iterated parents of level `≤ l₂`
   (`PlanarSeparator.Map.topA`), the separator is `C` with `Y` if they coincide or `Y` weighs
   at least `1/3`, and otherwise the rerouting option (`PlanarSeparator.Map.arcOpt`: the
   fundamental cycle of the last dart of an arc in the tree redirected along it, with its inside
   or the complement, as it agrees with the inside of `δ` at `g₀`) along the arc from `b` to `a`
   if it puts the face of `δ` on the wanted side (`PlanarSeparator.Map.deepWant`), along the arc
   from `a` to `b` otherwise (`PlanarSeparator.Map.deepPick`). **Proved (the programs, partly)**
   (`PlanarSeparator/Machine/MillerBand.lean`, registers `r430 …`): the darts leaving `Y` by
   their vertices and their number (`MillerProg.bdPass_exec`, `72 k + 4` steps,
   `MillerProg.nOut_eq_bdK`), the walk writing the boundary cycle and the positions of its
   vertices (`MillerProg.cyWalk_exec`, `16 K + 4` steps; the darts of `bdCycle` through the
   coding, `MillerProg.cyNext_iter_bdD`, `MillerProg.cyNext_inj`), the ancestor at level `≤ l`
   (`MillerProg.taPass_exec`, `12 n + 4` steps; `MillerProg.taNext_topA`), and the parent darts
   of the tree redirected along an arc (`MillerProg.cpPass_exec`, `MillerProg.arPass_exec`,
   `7 n + 19 ℓ + 7` steps; `MillerProg.arcTree_par_code`). The darts of the
   fundamental cycle of a dart in a tree given by its parent darts
   (`PlanarSeparator/Machine/MillerFcyc.lean`, registers `r500 …`: `MillerProg.fcProg_exec`,
   `77 n + 26` steps; `MillerProg.fcProg_fcycle`, the darts of `fcycle` through the coding), and
   the inside marks of a dart off a tree after the search of its dual tree
   (`PlanarSeparator/Machine/MillerInside.lean`, registers `r530 …`: `MillerProg.imLoop_exec`,
   `MillerProg.imLoop_inside`, `21 k + 21` steps; for a redirected tree the tree marks and the
   search are to be rerun on its parent darts), and for the tests
   (`PlanarSeparator/Machine/MillerWeigh.lean`, registers `r551 …`): the zone test of a face
   (`MillerProg.ztest_exec`, `MillerProg.ztest_zone`), the weights of the strict inside and outside
   of a fundamental cycle in `O(n)` (`MillerProg.cvMark_exec`, `MillerProg.wPass_exec`,
   `MillerProg.weigh_sides`) and the numeric forms of the heavy test, of the comparison of the
   sides and of `deepWant` (`MillerProg.third_le_iff`, `MillerProg.lighter_iff`,
   `MillerProg.deepWant_iff`). **The band case after steps 1–8**
   (`PlanarSeparator/Machine/MillerS910.lean`): `MillerProg.s9band` (the constants of the cycle
   search restored, `fcProg` on the parent darts of `T₁`, `tmpass ; search` on them, `fsel ;
   imLoop`, and the zone tests of both faces of `δ`, `MillerProg.s9zt`) and
   **`MillerProg.s9band_spec`**: within `113 k + 90 n + 145` steps, the darts of `T₁.fcycle δ`
   at `bFc` (number in `r514`), marks at `bIm` differing from `r539` exactly on `T₁.inside δ`,
   and flags `r580`, `r581` positive iff the face of `δ`, of `α δ`, avoids the levels `< l₂`;
   for the deep case, the two ancestors at level `l₂` of the ends of `δ`
   (`MillerProg.s9top`, two runs of `taPass`; `MillerProg.s9top_topA`, `24 n + 18` steps).
   **Steps 1–9 in the band case as one program** (`PlanarSeparator/Machine/MillerFull.lean`):
   `MillerProg.millerB = millerA ; s9band` and **`MillerProg.millerB_spec`**: within
   `(231 log₂ n + 1134) k + (60 n + 152) log₂ n + 278 n + 637 + (113 k + 90 n + 145)` steps,
   `r580, r581 > 0` iff the deep case of `bandSep`, and otherwise `bandSep` (for any `x₀`, `g₀`)
   is `(T₁.fcycle δ, T₁.inside δ)`, held on the machine as above, and satisfies
   `PlanarSeparator.Map.SepOK` with `2 (l₂ - l₀) + #K₀ + #(T.lvl l₂)` darts; it also exports the
   whole state needed by a deep-case continuation (the hypotheses of
   `band_separator_explicit`, the arrays of `millerA`, the memory above `bFc + 2 n + 1`, the
   registers `≥ 590`). **Deep-case pieces** (`PlanarSeparator/Machine/MillerDeep.lean`):
   `MillerProg.s10hvy` reruns `hvy` at `l₂` in a fresh region (`MillerProg.s10hvy_spec`,
   `101 k + 27 n + 36` steps: the label `r597` of `Y` marks exactly the faces of `Y`,
   `r599 = ∑ v ∈ ins Y, wP v`, `r168 = ∑ wP`; the heavy test is `r168 ≤ 3 r599`);
   `MillerProg.s10cyc` (`xfind`, a dart `x₀` leaving `Y`, `MillerProg.xfind_exec` and
   `MillerProg.exists_out_comp`; then `bdPass ; cyWalk`) and **`MillerProg.s10cyc_spec`**
   (`180 k + 12` steps: `BdOK Y x₀`, the darts of `bdCycle Y x₀` at `bCy`, their number in
   `r451`, the positions of its vertices at `bPos`); and **`MillerProg.deep_fallback_sep`**: if
   the ancestors coincide or `Y` is heavy, `bandSep` is `(bdCycle Y x₀, Y)` and is a separator.
   **The band case and the deep fallback as one program**
   (`PlanarSeparator/Machine/MillerFull0.lean`): `MillerProg.millerC = millerB ; if r580, r581 > 0
   then s10hvy ; s9top ; s10cyc` and **`MillerProg.millerC_spec`** (the bound of `millerB_spec`
   plus `281 k + 51 n + 69`): in the band case `bandSep` on the machine with `SepOK`; in the deep
   case the tests `r584 = r585` and `r168 ≤ 3 r599` of `deepSep`, the faces of `Y`, the darts of
   `bdCycle Y x₀` at `bCy`, and in the fallback branch `bandSep = (bdCycle Y x₀, Y)` with `SepOK`.
   For this, `millerA_spec` (with `step8run_tree`, `step8run_conc`,
   `step8_tree`) now also exports the reversals at `0`, the vertices at `bV`, the weights at
   `bw`, the darts `fdD` at `bF` and the memory above `bS₂ + n`; `concStep_exec`,
   `millerA_spec` and `millerB_spec` also export the concentration map itself at `bCN`
   (`bCN + vi v ↦ vi (cn v)`, if `l₂ < n`, which holds in the deep case).
   **The rerouting branch** (`PlanarSeparator/Machine/MillerReroute.lean`, registers `r600 …`):
   one option (`MillerProg.ropt = cpPass ; arPass ; (dart e into r353) ; (registers) ; s9band ;
   (orientation bits)`, bases of a fresh region in `r600 … r604`; **`MillerProg.ropt_spec`**,
   `113 k + 97 n + 19 ℓ + 230` steps: the darts of the cycle of `e = C.d (C.idxAt s ℓ)` in the arc
   tree `T₁.arcTree C s ℓ` with its inside marks, `r653 = 1` iff the insides of `e` and of `δ`
   agree at `g₀`, `r655 = 1` iff the face of `δ` lies on the oriented side); the guards of
   `arcOpt` in the deep case (`MillerProg.reroute_guards`); the test `deepWant`
   (`MillerProg.s10want = (registers) ; cvMark ; wPass ; rpPass ; wDec`, the representative of
   `ins Y` found by `rpPass` among the vertices of level `> l₂` with a face labelled `Y`, read in
   the array of `cn`; **`MillerProg.s10want_spec`**, `9 K + 44 n + 60` steps: `r624 = 1` iff
   `deepWant`); and **`MillerProg.s10rr_spec`** for `s10rr` (the indices `C.idx b`, `C.idx a` from
   the positions, `L = C.off`, `s10want`, the first option, the comparison with the wanted side,
   the second option if needed): within `9 K + 44 n + 2 (113 k + 97 n + 19 C.k + 230) + 120`
   steps the output registers (darts at `r640`, number `r641`, marks at `r642`, flag `r643`,
   polarity `r644`: `G ∈ Z ↔ (mark ≠ flag ↔ r644 = 1)`) hold
   `deepPick T₁ C δ a b (deepWant …) g₀` for any proper simple cycle `C` bounding `Y` held at
   `bCy` with its positions at `bPos`. **The whole program**
   (`PlanarSeparator/Machine/MillerFullAll.lean`): `MillerProg.millerFull = millerB ; if r580,
   r581 > 0 then (s10fb ; (the two test bits) ; if a test holds then fbO else s10rr) else bandO`
   and **`MillerProg.millerFull_spec`**: within the bound of `millerC_spec` plus
   `226 k + 291 n + 620`, the output registers `r640 … r644` hold
   `bandSep T T₁ l₂ cn (wR wP) δ x₀ g₀` (for the dart `x₀` of `xfind` in the deep case and the face
   `g₀` of the dart `fdD` at the root) and it satisfies `SepOK` with
   `2 (l₂ - l₀) + #K₀ + #(T.lvl l₂)` darts, in the band case, the deep fallback and the rerouting
   branch.
10. **Output**: the darts of the cycle and the marks of the faces of `Z`: in the band case and
   for the rerouting options the darts `fd` of a fundamental cycle and the inside marks (or
   their complement), in the fallback the array `bCy` of `cyWalk` and the labels of `Y`. Written
   for the band case (`MillerProg.millerB_spec`: the darts at `bFc`, the marks at `bIm` with the
   flag `r539`), for the rerouting branch (`MillerProg.s10rr_spec`) and in all cases in the
   output registers `r640 … r644` (`MillerProg.millerFull_spec`: `bandO`, `fbO` with the
   boundary cycle at `bCy` and the labels of `Y` at `bL'`, `optOut`).

## Status

Proved: step 3's component labelling (`MillerProg.clab_exec`), its identification with the
components of the map (`MillerProg.label_eq_iff`), the numeric form of the heavy test
(`MillerProg.heavy_iff`), the program of the heavy test (`MillerProg.hvy_exec`) and its
correctness for `PlanarSeparator.Map.Heavy` (`MillerProg.hvy_heavy`); step 4, the last heavy
level by bisection (`MillerProg.bsearch_exec`); steps 2 and 5, the level counts, `⌊√n⌋` and
the thin levels (`MillerProg.thin_exec`); step 1, the breadth-first search on the coded map
(`MillerProg.bprog_exec`, `MillerProg.bprog_tree`) and a dart at every vertex
(`MillerProg.dpass_exec`, `MillerProg.dpass_dart`); step 6 at a level `l₀ ≥ 1`, the inner
region and the redirected tree (`MillerProg.iprog_inner`, with
`PlanarSeparator.Map.inner_explicit`); step 7, the concentrated weights
(`MillerProg.conc_exec`, with the band theorem for any concentration map,
`PlanarSeparator.Map.exists_band_separator_of`); in step 8, root sums and depths
(`MillerProg.rspass_tree`), lowest common ancestors by binary lifting (`MillerProg.tbuild_exec`,
`MillerProg.lcaq_lca`) and the weights of the strict insides of the darts `pd F`
(`MillerProg.inC_tree`), the walk and step 8 (`MillerProg.step8_tree`, from the parent darts `MillerProg.step8run_tree`,
and for `T₁` and the concentrated weights `MillerProg.step8run_conc`), and its inputs
(`MillerProg.tmpass_exec`, `MillerProg.jpass_tree`). Steps 1–8 are composed into one program
with one `O((k + n) log n)` bound (`MillerProg.millerA_spec`), ending with the hypotheses of
`PlanarSeparator.Map.band_separator_of_dart` for the dart of step 8 (`MillerProg.millerA_band`).
Steps 9–10 in the band case are composed with steps 1–8 (`MillerProg.millerB_spec`: the case
test, and in the band case the explicit separator `bandSep` on the machine with `SepOK`), the deep
fallback too (`MillerProg.millerC_spec`), and the rerouting branch of the deep case is proved as
a program on the state after `s10cyc` (`MillerProg.s10rr_spec`, with `ropt_spec`,
`s10want_spec`, `reroute_guards`); **the whole program** `MillerProg.millerFull` is proved by
`MillerProg.millerFull_spec`: from the coded triangulation (with the starting registers `ARegs`,
`S9Regs`, `S10Regs`, `S11Regs` and clear scratch regions), within one explicit
`O((k + n) log n)` bound, the separator in the output registers is the explicit
`bandSep T T₁ l₂ cn (wR wP) δ x₀ g₀` and satisfies `SepOK` in all cases (the theorem starts, as
`millerA_spec`, from the coded map in memory and ends with the separator in memory).
-/
