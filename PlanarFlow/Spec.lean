module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Log
public import Mathlib.Logic.Relation
public import WordRAM.Spec

/-!
# Planar flows: the specification

The definitions the statements of the `PlanarFlow` targets use, and the targets. The library
`PlanarFlow` is built on these definitions (they are its own, not copies), so that a statement
read here is the statement proved.

* **Combinatorial maps** (`PlanarFlow.CombMap`): darts `D` with a reversal `rev` (an involution
  without fixed points), a tail, a face, and the next dart `next` along the boundary walk of its
  face (injective, on the same face, starting at the head of the dart). A map is **plane**
  (`CombMap.IsPlane`) if the graph and its dual are connected and Euler's formula
  `#V + #F = #D / 2 + 2` holds. Flows are antisymmetric integer functions on the darts
  (`IsAntisymm`), with net flow `div f v` out of a vertex; a `b`-flow within capacities `u` is
  `IsBFlow b u f`; a feasible potential of the dual graph with lengths `ℓ` on the dual arcs
  `face d → face (rev d)` is `IsPotential ℓ φ` (`cob φ d ≤ ℓ d`).
* **Networks** (`PlanarFlow.Network`): arcs with a tail, a head and an integer capacity; flows
  from sources `S` to sinks `T` (`IsFlow`), their value, cuts and their capacities.
* **Inputs of the machine programs**, lists of natural numbers for the word RAM of
  `WordRAM/Spec.lean`:
  - `Feas`: a plane map with capacities, supplies and demands
    (`[V, F, S, tl 0, rv 0, fc 0, nx 0, cp 0, …, bp 0, bn 0, …]`, `Feas.Enc`), the question being
    whether a flow meeting the supplies and demands within the capacities exists
    (`Feas.Feasible`);
  - `Dijk`: a digraph with nonnegative lengths in compressed form, a source and a word `INF`
    capping the distances (`Dijk.DEnc`), with the lengths of the walks from the source (`Dijk.Reach`);
  - `BM`: a bipartite graph in compressed form (`BM.Enc`) and its matchings (`BM.IsMatching`).
* **The targets**: `MaxFlowMinCut`, `MillerNaor`, `FeasibleFlowMachine`, `DijkstraMachine`,
  `BipartiteMatchingMachine`, and `MaxFlowMachine'` (the maximum-flow algorithm of Borradaile,
  Klein, Mozes, Nussbaum and Wulff-Nilsen on the machine, at the end of this file).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

open Finset

/-! ### Combinatorial maps and flows on darts -/

/-- A combinatorial map with darts `D`, vertices `V` and faces `F`. -/
structure CombMap (D V F : Type*) where
  /-- The reverse of a dart. -/
  rev : D → D
  rev_rev : ∀ d, rev (rev d) = d
  rev_ne : ∀ d, rev d ≠ d
  /-- The vertex at which a dart starts. -/
  tail : D → V
  /-- The face whose boundary walk traverses the dart. -/
  face : D → F
  /-- The next dart along the boundary walk of the face of a dart. -/
  next : D → D
  next_injective : Function.Injective next
  face_next : ∀ d, face (next d) = face d
  tail_next : ∀ d, tail (next d) = tail (rev d)

namespace CombMap

variable {D V F : Type*} (M : CombMap D V F)

/-- The vertex at which a dart ends. -/
def head (d : D) : V := M.tail (M.rev d)

variable [Fintype D] [DecidableEq V]

/-- The net flow of `f` out of the vertex `v`. -/
def div (f : D → ℤ) (v : V) : ℤ := ∑ d with M.tail d = v, f d

/-- `f` is antisymmetric: the flow along the reverse of a dart is the opposite. -/
def IsAntisymm {R : Type*} [Neg R] (f : D → R) : Prop := ∀ d, f (M.rev d) = - f d

/-- The coboundary of a function on the faces: the difference of its values on the two sides
of each dart. -/
def cob {R : Type*} [Sub R] (φ : F → R) (d : D) : R := φ (M.face (M.rev d)) - φ (M.face d)

/-- The dual relation: the face of a dart is adjacent to the face of its reverse. -/
def DualAdj (x y : F) : Prop := ∃ d, M.face d = x ∧ M.face (M.rev d) = y

/-- The primal relation: the tail of a dart is adjacent to its head. -/
def Adj (a b : V) : Prop := ∃ d, M.tail d = a ∧ M.head d = b

/-- A *plane* map: the graph and its dual are connected and Euler's formula holds. -/
structure IsPlane [Fintype V] [Fintype F] : Prop where
  nonempty : Nonempty V
  conn : ∀ a b, Relation.ReflTransGen M.Adj a b
  dualConn : ∀ x y, Relation.ReflTransGen M.DualAdj x y
  euler : Fintype.card V + Fintype.card F = Fintype.card D / 2 + 2

end CombMap

namespace CombMap

section Flows

variable {D V F : Type*} {M : CombMap D V F}
variable [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]

/-- A feasible potential for lengths `ℓ` on the dual arcs `face d → face (rev d)`. -/
def IsPotential (M : CombMap D V F) (ℓ : D → ℤ) (φ : F → ℤ) : Prop :=
  ∀ d, M.cob φ d ≤ ℓ d

/-- A `b`-flow respecting the capacities `u`. -/
structure IsBFlow (M : CombMap D V F) (b : V → ℤ) (u : D → ℤ) (f : D → ℤ) : Prop where
  antisymm : M.IsAntisymm f
  div_eq : ∀ v, M.div f v = b v
  le_cap : ∀ d, f d ≤ u d

end Flows

end CombMap

/-! ### Networks -/

/-- A network: arcs `E` between vertices `V`, each with a tail, a head and an integer
capacity. -/
structure Network (V : Type*) (E : Type*) where
  /-- The tail of an arc. -/
  tail : E → V
  /-- The head of an arc. -/
  head : E → V
  /-- The capacity of an arc. -/
  cap : E → ℤ

namespace Network

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (N : Network V E)

/-- The net flow leaving a vertex: the flow on the arcs leaving it minus the flow on the arcs
entering it. -/
def netOut (f : E → ℤ) (v : V) : ℤ :=
  ∑ e with N.tail e = v, f e - ∑ e with N.head e = v, f e

/-- A flow from the sources `S` to the sinks `T`. -/
structure IsFlow (S T : Finset V) (f : E → ℤ) : Prop where
  nonneg : ∀ e, 0 ≤ f e
  le_cap : ∀ e, f e ≤ N.cap e
  conserve : ∀ v, v ∉ S → v ∉ T → N.netOut f v = 0

/-- The value of a flow: the net flow leaving the sources. -/
def value (S : Finset V) (f : E → ℤ) : ℤ := ∑ v ∈ S, N.netOut f v

/-- A cut: a set of vertices containing every source and no sink. -/
def IsCut (S T X : Finset V) : Prop := S ⊆ X ∧ Disjoint X T

/-- The capacity of a set of vertices: the total capacity of the arcs leaving it. -/
def cutCap (X : Finset V) : ℤ := ∑ e with N.tail e ∈ X ∧ N.head e ∉ X, N.cap e

end Network

/-! ### The input of the feasibility test -/

namespace Feas

open WordRAM

/-- The input of a run. -/
def inp (d : List ℕ) : Input := ⟨d, fun _ => 0⟩

/-- The words of the input. -/
def word (d : List ℕ) (i : ℕ) : ℕ := d.getD i 0
/-- The number of vertices. -/
def nv (d : List ℕ) : ℕ := word d 0
/-- The number of faces. -/
def nf (d : List ℕ) : ℕ := word d 1
/-- The number of darts. -/
def nd (d : List ℕ) : ℕ := word d 2
/-- The tail of a dart. -/
def tl (d : List ℕ) (i : ℕ) : ℕ := word d (i * 5 + 3)
/-- The reverse of a dart. -/
def rv (d : List ℕ) (i : ℕ) : ℕ := word d (i * 5 + 3 + 1)
/-- The face of a dart. -/
def fc (d : List ℕ) (i : ℕ) : ℕ := word d (i * 5 + 3 + 1 + 1)
/-- The next dart along the boundary walk of the face. -/
def nx (d : List ℕ) (i : ℕ) : ℕ := word d (i * 5 + 6)
/-- The capacity of a dart. -/
def cp (d : List ℕ) (i : ℕ) : ℕ := word d (i * 5 + 3 + 1 + 1 + 2)

/-- The supply of a vertex. -/
def bp (d : List ℕ) (v : ℕ) : ℕ := word d (v * 2 + (nd d * 5 + 3))
/-- The demand of a vertex. -/
def bn (d : List ℕ) (v : ℕ) : ℕ := word d (v * 2 + (nd d * 5 + 3) + 1)
/-- The total of the supplies and demands. -/
def bsum (d : List ℕ) : ℕ := ∑ v ∈ range (nv d), (bp d v + bn d v)
/-- The offset of signed values. -/
def zz (d : List ℕ) : ℕ := (nf d * nd d + 1) * (bsum d + 1)

/-- The input describes a combinatorial map. -/
structure Wf (d : List ℕ) : Prop where
  tl_lt : ∀ i < nd d, tl d i < nv d
  rv_lt : ∀ i < nd d, rv d i < nd d
  rv_rv : ∀ i < nd d, rv d (rv d i) = i
  rv_ne : ∀ i < nd d, rv d i ≠ i
  fc_lt : ∀ i < nd d, fc d i < nf d
  nx_lt : ∀ i < nd d, nx d i < nd d
  nx_inj : ∀ i < nd d, ∀ j < nd d, nx d i = nx d j → i = j
  fc_nx : ∀ i < nd d, fc d (nx d i) = fc d i
  tl_nx : ∀ i < nd d, tl d (nx d i) = tl d (rv d i)

/-- The combinatorial map described by the input. -/
def map {d : List ℕ} (h : Wf d) : CombMap (Fin (nd d)) (Fin (nv d)) (Fin (nf d)) where
  rev i := ⟨rv d i, h.rv_lt i i.2⟩
  rev_rev i := Fin.ext (h.rv_rv i i.2)
  rev_ne i := fun e => h.rv_ne i i.2 (congrArg Fin.val e)
  tail i := ⟨tl d i, h.tl_lt i i.2⟩
  face i := ⟨fc d i, h.fc_lt i i.2⟩
  next i := ⟨nx d i, h.nx_lt i i.2⟩
  next_injective a b e := Fin.ext (h.nx_inj a a.2 b b.2 (congrArg Fin.val e))
  face_next i := Fin.ext (h.fc_nx i i.2)
  tail_next i := Fin.ext (h.tl_nx i i.2)

/-- The supplies minus the demands. -/
def bvec (d : List ℕ) (v : Fin (nv d)) : ℤ := (bp d v : ℤ) - bn d v

/-- The capacities. -/
def ucap (d : List ℕ) (i : Fin (nd d)) : ℤ := cp d i

/-- A flow meeting the supplies and demands within the capacities exists. -/
def Feasible {d : List ℕ} (h : Wf d) : Prop := ∃ f, (map h).IsBFlow (bvec d) (ucap d) f

/-- Well-formed inputs for the word bound `W`: a plane map, and words large enough. -/
structure Enc (d : List ℕ) (W : ℕ) : Prop where
  wf : Wf d
  plane : (map wf).IsPlane
  word_le : ∀ i, word d i ≤ W
  size : nd d * 5 + 2 * nv d + 4 * nv d + nf d + 8 ≤ W
  big : 2 * zz d + 2 * bsum d + 2 ≤ W
  cap_le : ∀ i < nd d, 2 * zz d + cp d i ≤ W

end Feas

/-! ### The input of Dijkstra's algorithm -/

namespace Dijk

open WordRAM

/-- The input of a run. -/
def inp (d : List ℕ) : Input := ⟨d, fun _ => 0⟩
/-- The words of the input. -/
def word (d : List ℕ) (i : ℕ) : ℕ := d.getD i 0
/-- The number of vertices. -/
def nn (d : List ℕ) : ℕ := word d 0
/-- The number of arcs. -/
def mm (d : List ℕ) : ℕ := word d 1
/-- The source. -/
def src (d : List ℕ) : ℕ := word d 2
/-- The cap `INF` on the printed distances. -/
def inf (d : List ℕ) : ℕ := word d 3
/-- The first arc leaving `u`. -/
def off (d : List ℕ) (u : ℕ) : ℕ := word d (u + 4)
/-- The head of an arc. -/
def dst (d : List ℕ) (j : ℕ) : ℕ := word d (j * 2 + (nn d + 5))
/-- The length of an arc. -/
def len (d : List ℕ) (j : ℕ) : ℕ := word d (j * 2 + (nn d + 5) + 1)

/-- Well-formed inputs for the word bound `W`. -/
structure DEnc (d : List ℕ) (W : ℕ) : Prop where
  n_pos : 1 ≤ nn d
  src_lt : src d < nn d
  off_zero : off d 0 = 0
  off_last : off d (nn d) = mm d
  off_mono : ∀ u < nn d, off d u ≤ off d (u + 1)
  dst_lt : ∀ j < mm d, dst d j < nn d
  word_le : ∀ i, word d i ≤ W
  size : 4 * nn d + 2 * mm d + 8 ≤ W
  inf_le : ∀ j < mm d, inf d + len d j ≤ W

/-- The walks from the source: `Reach v ℓ` if some walk from the source to `v` has length `ℓ`. -/
inductive Reach (d : List ℕ) : ℕ → ℕ → Prop
  | src : Reach d (src d) 0
  | step {u ℓ j : ℕ} : Reach d u ℓ → u < nn d → off d u ≤ j → j < off d (u + 1) →
      Reach d (dst d j) (ℓ + len d j)

end Dijk

/-! ### The input of maximum bipartite matching -/

namespace BM

open WordRAM

/-- The words of the input. -/
def word (d : List ℕ) (i : ℕ) : ℕ := d.getD i 0
/-- The number of vertices. -/
def nn (d : List ℕ) : ℕ := word d 0
/-- The number of arcs. -/
def mm (d : List ℕ) : ℕ := word d 1
/-- The colour of a vertex (`1` white, `0` black). -/
def col (d : List ℕ) (v : ℕ) : ℕ := word d (v + 2)
/-- The first arc of a vertex. -/
def off (d : List ℕ) (u : ℕ) : ℕ := word d (u + (nn d + 2))
/-- The head of an arc. -/
def dst (d : List ℕ) (j : ℕ) : ℕ := word d (j + (2 * nn d + 3))

/-- An arc from `w` to `b`. -/
def Arc (d : List ℕ) (w b : ℕ) : Prop :=
  w < nn d ∧ ∃ j, off d w ≤ j ∧ j < off d (w + 1) ∧ dst d j = b

/-- A matching: pairs along arcs from white vertices, no two sharing a vertex. -/
def IsMatching (d : List ℕ) (M : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ M, Arc d p.1 p.2 ∧ col d p.1 = 1) ∧ (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q) ∧
    (∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q)

/-- The input describes a bipartite graph. -/
structure Wf (d : List ℕ) : Prop where
  col_le : ∀ v < nn d, col d v ≤ 1
  arc_lt : ∀ w b, Arc d w b → b < nn d
  arc_col : ∀ w b, Arc d w b → col d w = 1 ∧ col d b = 0

/-- The input of a run. -/
def inp (d : List ℕ) : Input := ⟨d, fun _ => 0⟩

/-- Well-formed inputs for the word bound `W`. -/
structure Enc (d : List ℕ) (W : ℕ) : Prop extends Wf d where
  off_zero : off d 0 = 0
  off_last : off d (nn d) = mm d
  off_mono : ∀ u < nn d, off d u ≤ off d (u + 1)
  word_le : ∀ i, word d i ≤ W
  size : 6 * nn d + mm d + 8 ≤ W

end BM

/-! ### The targets -/

universe u

/-- **The max-flow min-cut theorem** for multiple sources and sinks: in a network with
nonnegative capacities and disjoint sets of sources `S` and sinks `T`, some flow from `S` to `T`
has the value of the capacity of some cut; that flow is a maximum flow and that cut a minimum
cut. -/
def MaxFlowMinCut : Prop :=
  ∀ {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (N : Network V E)
    (S T : Finset V), Disjoint S T → (∀ e, 0 ≤ N.cap e) →
    ∃ f X, N.IsFlow S T f ∧ Network.IsCut S T X ∧ N.value S f = N.cutCap X ∧
      (∀ g, N.IsFlow S T g → N.value S g ≤ N.value S f) ∧
      (∀ Y, Network.IsCut S T Y → N.cutCap X ≤ N.cutCap Y)

/-- **Supplies and demands in plane graphs (Miller and Naor).** On a plane map, if `g` is an
antisymmetric function on the darts with net flow `b` out of every vertex, a `b`-flow within the
capacities `u` exists if and only if the dual graph with the lengths `u - g` on the dual arcs has a
feasible potential. -/
def MillerNaor : Prop :=
  ∀ {D V F : Type u} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
    [DecidableEq F] (M : CombMap D V F), M.IsPlane → ∀ (b : V → ℤ) (u g : D → ℤ),
    M.IsAntisymm g → (∀ v, M.div g v = b v) →
    ((∃ f, M.IsBFlow b u f) ↔ ∃ φ, M.IsPotential (u - g) φ)

/-- **Feasible flows in plane graphs on the machine.** One word program for the word RAM (no real
instruction, `WordRAM.Program.IsWord`) decides, for every well-formed input describing a plane map
with `V` vertices, `F` faces and `S` darts, capacities on the darts and supplies and demands at the
vertices, whether a flow meeting the supplies and demands within the capacities exists: it halts
within `26 (S + 2)(V + F + 2)` steps (`O(n²)` for plane graphs) and prints `1` if such a flow exists
and `0` otherwise. -/
def FeasibleFlowMachine : Prop :=
  ∃ prog : WordRAM.Program, WordRAM.Program.IsWord prog ∧
    ∀ (d : List ℕ) (W : ℕ) (he : Feas.Enc d W),
    ∃ ans : ℕ, ans ≤ 1 ∧ (ans = 1 ↔ Feas.Feasible he.wf) ∧
      WordRAM.RunsWithin prog (Feas.inp d) W
        (26 * (Feas.nd d + 2) * (Feas.nv d + Feas.nf d + 2)) [ans]

/-- **Dijkstra's algorithm on the machine.** One word program for the word RAM (no real instruction,
`WordRAM.Program.IsWord`) computes, for every well-formed input (a digraph with `n` vertices, `m`
arcs grouped by their tails, natural lengths, a source and a word `INF`), within
`(n + m + 1)(36 ⌊log₂ n⌋ + 143)` steps, the distance from the source to every vertex capped at
`INF`: the printed value of `v` is at most `INF` and at most the length of every walk from the
source to `v`, and if it is below `INF` it is the length of such a walk (so it is `INF` when there
is no walk). -/
def DijkstraMachine : Prop :=
  ∃ prog : WordRAM.Program, WordRAM.Program.IsWord prog ∧ ∀ (d : List ℕ) (W : ℕ), Dijk.DEnc d W →
    ∃ Dv : ℕ → ℕ, (∀ v < Dijk.nn d, Dv v ≤ Dijk.inf d ∧
        (Dv v < Dijk.inf d → Dijk.Reach d v (Dv v)) ∧ ∀ ℓ, Dijk.Reach d v ℓ → Dv v ≤ ℓ) ∧
      WordRAM.RunsWithin prog (Dijk.inp d) W
        ((Dijk.nn d + Dijk.mm d + 1) * (36 * Nat.log 2 (Dijk.nn d) + 143))
        ((List.range (Dijk.nn d)).map Dv)

/-- **Maximum bipartite matching on the machine.** One word program for the word RAM (no real
instruction, `WordRAM.Program.IsWord`) prints, for every well-formed bipartite graph with `n`
vertices and `m` arcs, the size of a maximum matching, within `80 (n + 1)(n + m + 1)` steps. -/
def BipartiteMatchingMachine : Prop :=
  ∃ prog : WordRAM.Program, WordRAM.Program.IsWord prog ∧ ∀ (d : List ℕ) (W : ℕ), BM.Enc d W →
    ∃ k : ℕ, (∃ M, BM.IsMatching d M ∧ M.card = k) ∧ (∀ M, BM.IsMatching d M → M.card ≤ k) ∧
      WordRAM.RunsWithin prog (BM.inp d) W (80 * (BM.nn d + 1) * (BM.nn d + BM.mm d + 1)) [k]

end PlanarFlow

end

/-! ### The maximum-flow target: maximum flow on the machine

The maximum-flow algorithm of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen on the
machine.

* `Feas.MEnc' d W`: the input `d` (in the format of `Feas.Enc`) describes a plane map, loops
  allowed, whose rotations (`nx ∘ rv`) and face walks (`nx`) are transitive on the darts of each
  vertex and of each face, with disjoint sources (`bp ≠ 0`) and sinks (`bn ≠ 0`), and every word at
  most `W`; `Feas.size' d` is the number of darts and vertices plus the total capacity, plus `2`.
* `Feas.IsSTFlow'`: antisymmetric, within the capacities, conserved off the sources and sinks;
  `Feas.stValue'`: the net flow out of the sources.
* `MaxFlowMachine'`: one program computes a maximum flow within `c (n + K + 1)(⌊log₂ n⌋ + 1)³`
  steps (`n` darts, `K` vertices) whenever the word bound is at least `c (7 · size)^k`.
-/

@[expose] public section

namespace PlanarFlow

open Finset

namespace Feas

/-- The sources: the vertices with `bp ≠ 0`. -/
def srcs' (d : List ℕ) : Finset (Fin (nv d)) := univ.filter fun v => bp d v ≠ 0

/-- The sinks: the vertices with `bn ≠ 0`. -/
def snks' (d : List ℕ) : Finset (Fin (nv d)) := univ.filter fun v => bn d v ≠ 0

/-- A flow from the sources to the sinks on the darts of the map: antisymmetric, within the
capacities, conserved off the sources and the sinks. -/
structure IsSTFlow' {d : List ℕ} (h : Wf d) (f : Fin (nd d) → ℤ) : Prop where
  antisymm : (map h).IsAntisymm f
  le_cap : ∀ i, f i ≤ ucap d i
  conserve : ∀ v, v ∉ srcs' d → v ∉ snks' d → (map h).div f v = 0

/-- The value of a flow: the net flow out of the sources. -/
def stValue' {d : List ℕ} (h : Wf d) (f : Fin (nd d) → ℤ) : ℤ := ∑ v ∈ srcs' d, (map h).div f v

/-- Well-formed maximum-flow inputs for the word bound `W`: a plane map (loops allowed), the
rotation (`nx ∘ rv`) and the face walk (`nx`) transitive on the darts of a vertex / of a face,
disjoint sources and sinks, every word at most `W`. -/
structure MEnc' (d : List ℕ) (W : ℕ) : Prop where
  wf : Wf d
  plane : (map wf).IsPlane
  rotT : ∀ i < nd d, ∀ j < nd d, tl d i = tl d j → ∃ k, (fun x => nx d (rv d x))^[k] i = j
  faceT : ∀ i < nd d, ∀ j < nd d, fc d i = fc d j → ∃ k, (nx d)^[k] i = j
  disj : ∀ v < nv d, bp d v = 0 ∨ bn d v = 0
  word_le : ∀ i, word d i ≤ W

/-- The size of an input: darts, vertices and the total capacity. -/
def size' (d : List ℕ) : ℕ := nd d + nv d + ∑ i ∈ Finset.range (nd d), cp d i + 2

end Feas

/-- **Maximum flow in plane graphs on the machine** (Borradaile, Klein, Mozes, Nussbaum,
Wulff-Nilsen). One program for the word RAM computes, for every well-formed input describing a
plane map with `n` darts and `K` vertices (loops allowed), capacities on the darts and sets of
sources and sinks, a maximum flow from the sources to the sinks within
`c (n + K + 1)(⌊log₂ n⌋ + 1)³` steps, whenever the word size is at least `c (7 · size)^k`: it
prints `p ++ Z :: q` with `|p| = n`, the flow on dart `x` being `q[p[x]] - Z`, where a lookup
outside a list reads as `0` (in Lean, `q.getD (p.getD x 0) 0 - Z`; the indices `p[x]` are not
required to lie in `q`). `MaxFlowMachine` (`PlanarFlow/SpecMaxFlow.lean`) strengthens this
statement: there the program is a word program (`WordRAM.Program.IsWord`) and every index `p[x]`
lies in `q`. -/
def MaxFlowMachine' : Prop :=
  ∃ (prog : WordRAM.Program) (c k : ℕ), ∀ (d : List ℕ) (W : ℕ) (he : Feas.MEnc' d W),
    c * (7 * Feas.size' d) ^ k ≤ W →
    ∃ (p : List ℕ) (Z : ℕ) (q : List ℕ), p.length = Feas.nd d ∧
      Feas.IsSTFlow' he.wf (fun x => ((q.getD (p.getD x 0) 0 : ℕ) : ℤ) - Z) ∧
      (∀ g, Feas.IsSTFlow' he.wf g →
        Feas.stValue' he.wf g ≤
          Feas.stValue' he.wf (fun x => ((q.getD (p.getD x 0) 0 : ℕ) : ℤ) - Z)) ∧
      WordRAM.RunsWithin prog (Feas.inp d) W
        (c * (Feas.nd d + Feas.nv d + 1) * (Nat.log 2 (Feas.nd d) + 1) ^ 3) (p ++ Z :: q)

end PlanarFlow

end
