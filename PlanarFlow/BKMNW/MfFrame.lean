module

public import PlanarFlow.BKMNW.MfDrvRoom

/-!
# A concrete frame layout for the max-flow driver

The driver (`mfDrive`, `mfDriveR`) runs the recursion `arunL` call by call, each call `x =
(τ, Hs, σ)` in a frame `[d, e)` of memory described by two predicates `FIn x d e c` (the input
of the call) and `FOut x f d e c` (its output flow `f`). This file fixes **one concrete layout**
of these frames on natural words.

The darts of the piece map, `B = pdarts M τ.piece Hs` (`m` of them), are numbered `0 … m-1` by
the **increasing order of a global numbering** `gid : D → ℕ` of the darts (`en i` the dart of
number `i`; `en_mono`): the numbering of a frame is determined by its set of darts, and the
compaction of a parent numbering by a flag (`lkProg`) is the numbering of the child. The frame
holds:

* header: `d ↦ m`, `d + 1 ↦ #Hs`, `d + 2 ↦ ntag τ` (`0` at a leaf call, `1` at a node call),
  `d + 3 ↦ Z` (the offset of the flows);
* seven arrays of length `m` from `d + 4`: `GID` (the global numbers), `RV` (the index of the
  reverse, as `encProg` reads `REV`), `SG` (the index of the image by the rotation `σ`, `SIG`),
  `CP` (the capacities, at most `Z`), `KR` (the rank `lrk S T (hunion Hs)` of the tail: `0`
  source, `1` hole, `2` sink, `3` other), `HL` (the hole label of the tail, `hlab`: `j + 1` for
  the hole `Hs[j]`, `0` off the holes), and `FL` (the flow, `Z + f`, written by the leaf solver
  and the combination). The frame has `fsz m = 4 + 7 m` cells.

* `ntag`, `hlab`, `fext` (a flow on `SDart B`, extended by `0`), **`Lay`** (the layout of the
  input arrays), `Lay.congr` (it depends only on `[d, d + 4 + 6 m)`), **`CallOk`** (the
  invariants of a call along a good decomposition: `PMOk`, `Good`, `PGood`, `LeafOK`, the
  terminals off the holes, the holes pairwise disjoint), **`CallOk.chL`**, **`CallOk.chR`** (they
  pass to the child calls).
* **`FInL Reach`**, **`FOutL`** (the frame predicates; `Reach` a set of calls closed under the
  children, e.g. the calls of one decomposition, so that a separator program has to compute the
  separator only of those), `FInL.stab`, `FOutL.stab` (the stability fields of `MfSpec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The tag of a call: `0` at a leaf, `1` at a node. -/
def ntag : ADec M → ℕ
  | .leaf _ => 0
  | .node _ _ _ => 1

lemma ntag_lt_one_iff (τ : ADec M) : ntag τ < 1 ↔ ∃ Q, τ = .leaf Q := by
  cases τ with
  | leaf Q => exact ⟨fun _ => ⟨Q, rfl⟩, fun _ => by simp [ntag]⟩
  | node l r π => exact ⟨fun h => by simp [ntag] at h, fun ⟨Q, h⟩ => by cases h⟩

/-- **The hole label** of a vertex: `j + 1` for the first hole `Hs[j]` containing it, `0` off the
holes. -/
def hlab (Hs : List (Finset V)) (v : V) : ℕ :=
  if v ∈ hunion Hs then Hs.findIdx (fun H => decide (v ∈ H)) + 1 else 0

/-- A flow on the darts of a piece map, extended by `0`. -/
def fext {B : Finset D} (f : SDart B → ℤ) (y : D) : ℤ := if h : y ∈ B then f ⟨y, h⟩ else 0

lemma fext_mem {B : Finset D} (f : SDart B → ℤ) {y : D} (h : y ∈ B) : fext f y = f ⟨y, h⟩ := by
  simp [fext, h]

/-- The number of cells of a frame of `m` darts. -/
def fsz (m : ℕ) : ℕ := 4 + 7 * m

variable (M) in
/-- **The layout of the input of a call** `x = (τ, Hs, σ)` in the memory `mem` from `d` (see the
module docstring): `m` darts of the piece map numbered by `en` in the increasing order of `gid`,
and the header and the six input arrays `GID`, `RV`, `SG`, `CP`, `KR`, `HL`. -/
structure Lay (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ) (x : MCall M) (m : ℕ)
    (en : ℕ → D) (d : ℕ) (mem : ℕ → ℕ) : Prop where
  hm : mem d = m
  hk : mem (d + 1) = x.2.1.length
  tag : mem (d + 2) = ntag x.1
  hz : mem (d + 3) = Z
  en_mem : ∀ i < m, en i ∈ pdarts M x.1.piece x.2.1
  en_surj : ∀ y ∈ pdarts M x.1.piece x.2.1, ∃ i < m, en i = y
  en_mono : ∀ i j, i < j → j < m → gid (en i) < gid (en j)
  gd : ∀ i < m, mem (d + 4 + i) = gid (en i)
  rv : ∀ i < m, mem (d + 4 + m + i) < m ∧ en (mem (d + 4 + m + i)) = M.rev (en i)
  sg : ∀ i < m, mem (d + 4 + 2 * m + i) < m ∧ en (mem (d + 4 + 2 * m + i)) = x.2.2 (en i)
  cp : ∀ i < m, (mem (d + 4 + 3 * m + i) : ℤ) = u (en i) ∧ mem (d + 4 + 3 * m + i) ≤ Z
  kr : ∀ i < m, mem (d + 4 + 4 * m + i) = lrk S T (hunion x.2.1) (M.tail (en i))
  hl : ∀ i < m, mem (d + 4 + 5 * m + i) = hlab x.2.1 (M.tail (en i))

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- **The layout depends only on `[d, d + 4 + 6 m)`.** -/
lemma Lay.congr {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem mem' : ℕ → ℕ}
    (h : Lay M gid u S T Z x m en d mem)
    (he : ∀ a, d ≤ a → a < d + 4 + 6 * m → mem' a = mem a) : Lay M gid u S T Z x m en d mem' where
  hm := by rw [he _ le_rfl (by omega)]; exact h.hm
  hk := by rw [he _ (by omega) (by omega)]; exact h.hk
  tag := by rw [he _ (by omega) (by omega)]; exact h.tag
  hz := by rw [he _ (by omega) (by omega)]; exact h.hz
  en_mem := h.en_mem
  en_surj := h.en_surj
  en_mono := h.en_mono
  gd i hi := by rw [he _ (by omega) (by omega)]; exact h.gd i hi
  rv i hi := by rw [he _ (by omega) (by omega)]; exact h.rv i hi
  sg i hi := by rw [he _ (by omega) (by omega)]; exact h.sg i hi
  cp i hi := by rw [he _ (by omega) (by omega)]; exact h.cp i hi
  kr i hi := by rw [he _ (by omega) (by omega)]; exact h.kr i hi
  hl i hi := by rw [he _ (by omega) (by omega)]; exact h.hl i hi

/-- The numbering is injective. -/
lemma Lay.en_inj {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (h : Lay M gid u S T Z x m en d mem) {i j : ℕ} (hi : i < m) (hj : j < m)
    (e : en i = en j) : i = j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · have := h.en_mono i j hij hj; rw [e] at this; omega
  · rfl
  · have := h.en_mono j i hij hi; rw [e] at this; omega

/-! ### The invariants of the calls -/

variable (M) in
/-- **The invariants of a call along a good decomposition**: the piece maps (`PMOk`), the
decomposition (`Good`, `PGood`, `LeafOK`), the sources and the sinks off the holes, the holes
pairwise disjoint. -/
def CallOk (S T : Finset V) (x : MCall M) : Prop :=
  x.1.PMOk M x.2.1 x.2.2 ∧ x.1.Good M S T x.2.1 ∧ x.1.PGood M x.2.1 ∧ x.1.LeafOK M S T x.2.1 ∧
    Disjoint S (hunion x.2.1) ∧ Disjoint T (hunion x.2.1) ∧ x.2.1.Pairwise Disjoint

lemma CallOk.pieceInv {x : MCall M} (h : CallOk M S T x) :
    PieceInv M x.1.piece x.2.1 x.2.2 := h.1.pieceInv

lemma callOk_child_holes {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    (h : CallOk M S T (.node l r π, Hs, σ)) :
    Disjoint S (hunion (childHoles Hs π.path.mverts)) ∧
      Disjoint T (hunion (childHoles Hs π.path.mverts)) ∧
      (childHoles Hs π.path.mverts).Pairwise Disjoint := by
  obtain ⟨-, ⟨-, -, -, -, hC, -⟩, -, -, hSA, hTA, hd⟩ := h
  rw [hunion_childHoles]
  refine ⟨disjoint_union_right.2 ⟨hSA, ?_⟩, disjoint_union_right.2 ⟨hTA, ?_⟩,
    pairwise_childHoles hd⟩
  · exact (disjoint_of_subset_right subset_union_left hC).symm
  · exact (disjoint_of_subset_right subset_union_right hC).symm

/-- **The invariants pass to the left child call.** -/
lemma CallOk.chL {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    (h : CallOk M S T (.node l r π, Hs, σ)) : CallOk M S T (chL M l r π Hs σ) := by
  obtain ⟨hS, hT, hd⟩ := callOk_child_holes h
  obtain ⟨⟨-, hpl, -⟩, ⟨gl, -⟩, ⟨-, -, -, pgl, -⟩, ⟨hl, -⟩, -⟩ := h
  exact ⟨hpl, gl, pgl, hl, hS, hT, hd⟩

/-- **The invariants pass to the right child call.** -/
lemma CallOk.chR {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    (h : CallOk M S T (.node l r π, Hs, σ)) : CallOk M S T (chR M l r π Hs σ) := by
  obtain ⟨hS, hT, hd⟩ := callOk_child_holes h
  obtain ⟨⟨-, -, hpr⟩, ⟨-, gr, -⟩, ⟨-, -, -, -, pgr, -⟩, ⟨-, hr⟩, -⟩ := h
  exact ⟨hpr, gr, pgr, hr, hS, hT, hd⟩

/-! ### The frame predicates -/

variable (M) in
/-- **The input of a call in the frame `[d, e)`**: a call of `Reach` with the invariants
`CallOk`, laid out by `Lay` with room for the flow array (`d + fsz m ≤ e`). -/
def FInL (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ)
    (x : MCall M) (d e : ℕ) (c : Config) : Prop :=
  Reach x ∧ CallOk M S T x ∧ ∃ m en, Lay M gid u S T Z x m en d c.nmem ∧ d + fsz m ≤ e

variable (M) in
/-- **The output flow `f` of a call in the frame `[d, e)`**: the layout `Lay`, and the flow array
`FL[i] = Z + f (en i)` from `d + 4 + 6 m`. -/
def FOutL (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ) : FOutT M :=
  fun x f d e c => ∃ m en, Lay M gid u S T Z x m en d c.nmem ∧ d + fsz m ≤ e ∧
    ∀ i < m, (c.nmem (d + 4 + 6 * m + i) : ℤ) = Z + fext f (en i)

lemma FInL.stab {Reach : MCall M → Prop} {x : MCall M} {d e : ℕ} {c c' : Config}
    (h : FInL M Reach gid u S T Z x d e c) (hm : MemEq c c' d e) :
    FInL M Reach gid u S T Z x d e c' := by
  obtain ⟨hr, ho, m, en, hl, he⟩ := h
  refine ⟨hr, ho, m, en, hl.congr fun a h1 h2 => (hm a h1 (by unfold fsz at he; omega)).1, he⟩

lemma FOutL.stab {x : MCall M} {f : SDart (pdarts M x.1.piece x.2.1) → ℤ} {d e : ℕ}
    {c c' : Config} (h : FOutL M gid u S T Z x f d e c) (hm : MemEq c c' d e) :
    FOutL M gid u S T Z x f d e c' := by
  obtain ⟨m, en, hl, he, hf⟩ := h
  unfold fsz at he
  refine ⟨m, en, hl.congr fun a h1 h2 => (hm a h1 (by omega)).1, by unfold fsz; omega,
    fun i hi => ?_⟩
  rw [(hm _ (by omega) (by omega)).1]; exact hf i hi

end MfDrv

end BKMNW

end PlanarFlow
