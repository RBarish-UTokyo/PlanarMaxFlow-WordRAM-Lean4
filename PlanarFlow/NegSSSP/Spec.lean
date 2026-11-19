module

public import PlanarFlow.BKMNW.Specs
public import PlanarFlow.BKMNW.DKPW
public import PlanarFlow.BKMNW.Cancel
public import PlanarFlow.Monge.DDGBF

/-!
# Shortest paths with negative lengths in plane graphs: the setting and the subroutines

The recursion of Klein, Mozes and Weimann (ACM Trans. Algorithms 6 (2010), 30) and of Mozes and
Wulff-Nilsen (ESA 2010, the article) computes shortest paths with negative lengths in the graph of
a plane map. Here it is stated for the graph `N.graph ℓ` of a map `N` (an arc from the tail to the
head of every dart, of length `ℓ d`), and applied to the dual graph of a map `M` through the dual
map `M.dual`, whose graph is `M.dualGraph ℓ` (`CombMap.dual_graph`).

* `CombMap.dual`: **the dual map** (the faces of `M` as vertices, the vertices of `M` as faces,
  the rotation of `M` as the boundary walk of its faces); `CombMap.IsPlane.dual`: the dual of a
  plane map is plane.
* `PotOut G o`: `o` is a feasible potential of `G`, or `none` and `G` has no feasible potential
  (equivalently, `negSSSPOut_of_potOut`, a closed walk of negative length).
* `PieceMSSPSpec`: **multiple-source shortest paths in a piece** (Klein): for a set `P` of darts
  with nonnegative lengths and sources `B`, the distances in the piece from every vertex of `B`.
  In the recursion the sources are the boundary vertices of the piece, which the cycle separators
  of the article put on one face of the piece, where Klein's algorithm applies; this condition is
  not part of the specification (a face of a piece needs the map of the piece).
  `msspRef`: the distances meet it.
* `DDG.join`: the union of two dense distance graphs, as a digraph; `BFDDGSpec`: **Bellman–Ford
  over the union of two dense distance graphs** returns a feasible potential of the union, or
  `none` when there is none. `potOut_bf`: the Bellman–Ford values after `|X|` rounds from `0`,
  checked for feasibility, meet it (`bfRef`); `potOut_bfDDG`: the outcome of the program
  `PlanarFlow.Monge.bfDDG` on one dense distance graph (`PlanarFlow.Monge.bfDDG_exec`) is such
  an output.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

open Finset

/-! ### The dual map -/

namespace CombMap

variable {D V F : Type*}

/-- **The dual map**: the faces as vertices, the vertices as faces, the rotation as the boundary
walk of the faces. The tail of a dart is its face, its head the face of its reverse. -/
def dual (M : CombMap D V F) : CombMap D F V where
  rev := M.rev
  rev_rev := M.rev_rev
  rev_ne := M.rev_ne
  tail := M.face
  face := M.tail
  next := M.rot
  next_injective := M.rot_injective
  face_next d := M.tail_rot d
  tail_next d := M.face_rot d

/-- The graph of a map with lengths on the darts: an arc from the tail to the head of every
dart. -/
def graph (M : CombMap D V F) (ℓ : D → ℤ) : Digraph V D where
  src := M.tail
  dst := M.head
  len := ℓ

variable [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]

/-- **The graph of the dual map is the dual graph.** -/
theorem dual_graph (M : CombMap D V F) (ℓ : D → ℤ) : M.dual.graph ℓ = M.dualGraph ℓ := rfl

/-- **The dual of a plane map is plane.** -/
theorem IsPlane.dual {M : CombMap D V F} (hM : M.IsPlane) : M.dual.IsPlane where
  nonempty := by
    by_contra hF
    rw [not_nonempty_iff] at hF
    have hD : IsEmpty D := ⟨fun d => hF.false (M.face d)⟩
    have h2 := hM.euler
    rw [Fintype.card_eq_zero (α := F), Fintype.card_eq_zero (α := D)] at h2
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := V) (by omega)
    rcases (hM.conn a b).cases_head with e | ⟨c, ⟨d, -⟩, -⟩
    · exact hab e
    · exact hD.false d
  conn := hM.dualConn
  dualConn := hM.conn
  euler := by have := hM.euler; change Fintype.card F + Fintype.card V = _; omega

end CombMap

namespace NegSSSP

open BKMNW CombMap

/-! ### Outputs -/

section Out

variable {X A : Type*}

/-- **A feasible potential, or none**: `some p` with `p` a feasible potential of `G`, or `none`
when `G` has no feasible potential. -/
def PotOut (G : Digraph X A) : Option (X → ℤ) → Prop
  | some p => G.IsPot p
  | none => ¬ ∃ p, G.IsPot p

/-- Without a feasible potential there is a closed walk of negative length. -/
theorem negSSSPOut_of_potOut [Fintype X] [DecidableEq X] [Fintype A] {G : Digraph X A}
    {o : Option (X → ℤ)} (h : PotOut G o) : NegSSSPOut G o := by
  cases o with
  | some p => exact h
  | none =>
    by_contra hn
    simp only [NegSSSPOut, not_exists, not_and, not_lt] at hn
    exact h (G.exists_pot_iff.2 hn)

/-- **Bellman–Ford with a final check**: the values after `|X|` rounds from `0` if they are
feasible, `none` otherwise. -/
noncomputable def bfCheck [Fintype X] [DecidableEq X] [Fintype A] (G : Digraph X A) :
    Option (X → ℤ) := by
  classical exact if G.IsPot (G.bf (Fintype.card X)) then some (G.bf (Fintype.card X)) else none

/-- **Bellman–Ford with a final check meets `PotOut`** (`PlanarFlow.Digraph.isPot_bf_card`). -/
theorem potOut_bf [Fintype X] [DecidableEq X] [Fintype A] (G : Digraph X A) :
    PotOut G (bfCheck G) := by
  classical
  unfold bfCheck
  split_ifs with h
  · exact h
  · exact fun ⟨p, hp⟩ => h (G.isPot_bf_card hp)

end Out

/-! ### Multiple-source shortest paths in a piece -/

section MSSP

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- **The specification of multiple-source shortest paths in a piece** (Klein): for a set `P` of
darts with nonnegative lengths and sources `B`, the distances in the piece from every vertex
of `B`. -/
def PieceMSSPSpec (N : CombMap D V F)
    (mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ) : Prop :=
  ∀ P ℓ B, (∀ d ∈ P, 0 ≤ ℓ d) → ∀ b ∈ B, IsDist (MSSP.pieceGraph N P ℓ) b (mssp P ℓ B b)

/-- The distances in a piece (a witness that `PieceMSSPSpec` can be met, not an implementation). -/
noncomputable def msspRef (N : CombMap D V F) (P : Finset D) (ℓ : D → ℤ) (_B : Finset V)
    (b v : V) : Option ℤ :=
  MSSP.odist (MSSP.pieceGraph N P ℓ) b v

theorem msspRef_spec (N : CombMap D V F) : PieceMSSPSpec N (msspRef N) :=
  fun P ℓ _ hnn b _ => isDist_odist (G := MSSP.pieceGraph N P ℓ) (fun a => hnn a.1 a.2) b

end MSSP

/-! ### Bellman–Ford over the union of two dense distance graphs -/

section BF

variable {X : Type*}

/-- **The union of two dense distance graphs**, as a digraph. -/
def _root_.PlanarFlow.BKMNW.DDG.join (H₁ H₂ : DDG X) : Digraph X (H₁.Arc ⊕ H₂.Arc) where
  src := Sum.elim (fun p => p.1.1) fun p => p.1.1
  dst := Sum.elim (fun p => p.1.2) fun p => p.1.2
  len := Sum.elim (fun p => (H₁.len p.1.1 p.1.2).getD 0) fun p => (H₂.len p.1.1 p.1.2).getD 0

/-- **The specification of Bellman–Ford over the union of two dense distance graphs**: a feasible
potential of the union, or `none` when there is none. -/
def BFDDGSpec (bf : DDG X → DDG X → Option (X → ℤ)) : Prop :=
  ∀ H₁ H₂, PotOut (H₁.join H₂) (bf H₁ H₂)

instance [Fintype X] [DecidableEq X] (H : DDG X) : Fintype H.Arc := by
  unfold DDG.Arc; infer_instance

/-- Bellman–Ford with a final check over the union (a witness that `BFDDGSpec` can be met). -/
noncomputable def bfRef [Fintype X] [DecidableEq X] (H₁ H₂ : DDG X) : Option (X → ℤ) :=
  bfCheck (H₁.join H₂)

theorem bfRef_spec [Fintype X] [DecidableEq X] : BFDDGSpec (bfRef (X := X)) :=
  fun H₁ H₂ => potOut_bf (H₁.join H₂)

/-- **The outcome of the program `bfDDG` on one dense distance graph is a `PotOut` output**: the
flag `r30 = 0` with a feasible potential, or `r30 = 1` with none
(`PlanarFlow.Monge.bfDDG_exec`). -/
theorem potOut_bfDDG {b : ℕ} {D : ℕ → ℕ → ℤ} {E : ℕ → ℤ} {flag : ℕ}
    (h : (flag = 0 ∧ (Monge.ddg b D).IsPot (fun v => E v)) ∨ (flag = 1 ∧ ¬ Monge.HasPot b D)) :
    PotOut (Monge.ddg b D) (if flag = 0 then some (fun v => E v) else none) := by
  rcases h with ⟨h0, hp⟩ | ⟨h1, hn⟩
  · simp only [h0, ↓reduceIte]; exact hp
  · simp only [h1, one_ne_zero, ↓reduceIte]; exact hn

end BF

end NegSSSP

end PlanarFlow
