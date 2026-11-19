module

public import WordRAM
public import PlanarFlow.DynTree.Ghost

/-!
# Dynamic trees: the memory layout and the representation invariant

The structure for the nodes `0, …, n-1` lives at a base address `B`: node `u` (and the nil node
`n`) has a record of 16 words at `adr B u j = 16u + (B + j)`. Natural fields: `par` (0, the
splay parent or the path-parent, `n` for none), `lc` (1), `rc` (2) (the children in the
auxiliary tree, `n` for none), `am` (3, the leftmost argmin of the first values of the subtree),
`fpar` (4, the parent in the forest), `lm` (5, the leftmost node), `rtm` (6, the rightmost node),
`amr` (7, the rightmost argmin of the first values), `am2`, `am2r` (8, 9, the same for the second
values), `rvw` (10, the reversal bit). Real fields: `vl` (0, the first value), `tg` (1, a pending
addition to the first values), `mn` (2), `sm` (3), `cnt` (4) (the minimum, the sum and the number
of nodes of the subtree), `vl2`, `tg2`, `mn2`, `sm2` (5–8, the same for the second values).

**Values.** The true value of `u` is its stored value plus the tags of `u` and of its ancestors
in its auxiliary tree: adding `δ` to a whole auxiliary tree is adding `δ` to the tag of its
root, and a rotation moves tags as in the delta representation of Sleator and Tarjan.

**Reversal.** The ghost virtual tree `VT` is the *true* tree (its in-order is the path). The
reversal bit of `x` means that the children of `x` are stored swapped, and that the records
below `x` (not `x` itself) are stored mirrored: their two values, tags and aggregates swapped,
their left and right aggregates swapped. A stored subtree thus carries a *parity* `π`, the
exclusive or of the reversal bits strictly above it in its auxiliary tree (`Enc M t p π`), and its
records hold the aggregates of `mirT^π t` (the mirror image if `π` is set), the first and second
values exchanged. The parent of a root of an auxiliary tree reads it with parity `false`.

**Aggregates.** `own M u`: the aggregates of the subtree of `u` *without* the tags of `u`; `rd M u`
adds them (what the parent reads). `AggOK`: `own` is the combination `comb` of the children and
of `u`, read in mirror image when the bit of `u` is set.

**Encoding.** `Enc M t p π`: the virtual tree `t` is stored in `M` with parity `π` and `p` the
parent pointer of its root; `EncC M ctx r p` is the same for a zipper (`cpar` the parity at the
hole). `Inv M G`: the list `G` of virtual trees (one per tree of the forest) is stored, its labels
are exactly `0, …, n-1`, and the nil record has `lc = rc = n`, `cnt = sm = sm2 = 0`.
`RepE M G F`: `G` represents the forest `F` (its edges and both values); `Rep` adds that `fpar` is
the parent function (which `evert` does not keep).
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine VT

/-- The address of field `j` of node `u` of the structure at base `B`. -/
def adr (B u j : ℕ) : ℕ := u * 16 + (B + j)

lemma adr_eq_iff {B u j u' j' : ℕ} (hj : j < 16) (hj' : j' < 16) :
    adr B u j = adr B u' j' ↔ u = u' ∧ j = j' := by
  unfold adr
  constructor
  · intro h
    have : u = u' := by omega
    subst this
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The memory: natural and real. -/
structure Mem where
  /-- Natural memory. -/
  nm : ℕ → ℕ
  /-- Real memory. -/
  rm : ℕ → ℝ

section fields
variable (B : ℕ) (M : Mem)

/-- The parent pointer (splay parent or path-parent). -/
def par (u : ℕ) : ℕ := M.nm (adr B u 0)
/-- The left child. -/
def lc (u : ℕ) : ℕ := M.nm (adr B u 1)
/-- The right child. -/
def rc (u : ℕ) : ℕ := M.nm (adr B u 2)
/-- The leftmost argmin of the first values of the subtree. -/
def am (u : ℕ) : ℕ := M.nm (adr B u 3)
/-- The forest parent. -/
def fpar (u : ℕ) : ℕ := M.nm (adr B u 4)
/-- The leftmost node of the subtree. -/
def lm (u : ℕ) : ℕ := M.nm (adr B u 5)
/-- The rightmost node of the subtree. -/
def rtm (u : ℕ) : ℕ := M.nm (adr B u 6)
/-- The rightmost argmin of the first values. -/
def amr (u : ℕ) : ℕ := M.nm (adr B u 7)
/-- The leftmost argmin of the second values. -/
def am2 (u : ℕ) : ℕ := M.nm (adr B u 8)
/-- The rightmost argmin of the second values. -/
def am2r (u : ℕ) : ℕ := M.nm (adr B u 9)
/-- The word of the reversal bit. -/
def rvw (u : ℕ) : ℕ := M.nm (adr B u 10)
/-- The reversal bit. -/
def rv (u : ℕ) : Bool := rvw B M u != 0
/-- The stored value. -/
def vl (u : ℕ) : ℝ := M.rm (adr B u 0)
/-- The tag. -/
def tg (u : ℕ) : ℝ := M.rm (adr B u 1)
/-- The minimum of the subtree, without the tag of `u`. -/
def mn (u : ℕ) : ℝ := M.rm (adr B u 2)
/-- The sum of the subtree, without the tag of `u`. -/
def sm (u : ℕ) : ℝ := M.rm (adr B u 3)
/-- The number of nodes of the subtree. -/
def cnt (u : ℕ) : ℝ := M.rm (adr B u 4)
/-- The stored second value. -/
def vl2 (u : ℕ) : ℝ := M.rm (adr B u 5)
/-- The tag of the second values. -/
def tg2 (u : ℕ) : ℝ := M.rm (adr B u 6)
/-- The minimum of the second values, without the tag. -/
def mn2 (u : ℕ) : ℝ := M.rm (adr B u 7)
/-- The sum of the second values, without the tag. -/
def sm2 (u : ℕ) : ℝ := M.rm (adr B u 8)
/-- The sum of the subtree as the parent sees it. -/
def sumA (u : ℕ) : ℝ := sm B M u + tg B M u * cnt B M u
/-- The minimum of the subtree as the parent sees it. -/
def minA (u : ℕ) : ℝ := mn B M u + tg B M u
/-- The sum of the second values as the parent sees it. -/
def sumA2 (u : ℕ) : ℝ := sm2 B M u + tg2 B M u * cnt B M u
/-- The minimum of the second values as the parent sees it. -/
def minA2 (u : ℕ) : ℝ := mn2 B M u + tg2 B M u
/-- The value of channel `k` (`false`: first, `true`: second). -/
def vlc (k : Bool) (u : ℕ) : ℝ := if k then vl2 B M u else vl B M u
/-- The tag of channel `k`. -/
def tgc (k : Bool) (u : ℕ) : ℝ := if k then tg2 B M u else tg B M u
/-- The true left child of `u` when its children are read with parity `σ`. -/
def lcS (σ : Bool) (u : ℕ) : ℕ := if σ then rc B M u else lc B M u

end fields

/-! ### Aggregates -/

/-- The aggregates of a subtree: the count, the sums and minima of both values, the leftmost and
rightmost argmins of both values, the leftmost and rightmost nodes. -/
@[ext] structure Ag where
  /-- The number of nodes. -/
  c : ℝ
  /-- The sum of the first values. -/
  s1 : ℝ
  /-- The sum of the second values. -/
  s2 : ℝ
  /-- The minimum of the first values. -/
  m1 : ℝ
  /-- The minimum of the second values. -/
  m2 : ℝ
  /-- The leftmost argmin of the first values. -/
  a1 : ℕ
  /-- The rightmost argmin of the first values. -/
  b1 : ℕ
  /-- The leftmost argmin of the second values. -/
  a2 : ℕ
  /-- The rightmost argmin of the second values. -/
  b2 : ℕ
  /-- The leftmost node. -/
  lm : ℕ
  /-- The rightmost node. -/
  rm : ℕ

namespace Ag

/-- The aggregates of the mirror image with the two values exchanged. -/
def mir (g : Ag) : Ag := ⟨g.c, g.s2, g.s1, g.m2, g.m1, g.b2, g.a2, g.b1, g.a1, g.rm, g.lm⟩

/-- `mir` if `π` is set. -/
def mirIf (π : Bool) (g : Ag) : Ag := if π then g.mir else g

/-- Add the tags `c0`, `c1` to the values. -/
def addTags (c0 c1 : ℝ) (g : Ag) : Ag :=
  ⟨g.c, g.s1 + c0 * g.c, g.s2 + c1 * g.c, g.m1 + c0, g.m2 + c1, g.a1, g.b1, g.a2, g.b2, g.lm,
    g.rm⟩

@[simp] lemma mir_mir (g : Ag) : g.mir.mir = g := rfl
@[simp] lemma mir_c (g : Ag) : g.mir.c = g.c := rfl
@[simp] lemma mirIf_false (g : Ag) : mirIf false g = g := rfl
@[simp] lemma mirIf_true (g : Ag) : mirIf true g = g.mir := rfl
@[simp] lemma mirIf_mirIf (π : Bool) (g : Ag) : mirIf π (mirIf π g) = g := by
  cases π <;> rfl
lemma mirIf_xor (π σ : Bool) (g : Ag) : mirIf (π ^^ σ) g = mirIf π (mirIf σ g) := by
  cases π <;> cases σ <;> rfl
lemma mir_addTags (c0 c1 : ℝ) (g : Ag) : (addTags c0 c1 g).mir = addTags c1 c0 g.mir := rfl
lemma mirIf_addTags (π : Bool) (c0 c1 : ℝ) (g : Ag) :
    mirIf π (addTags c0 c1 g) = addTags (if π then c1 else c0) (if π then c0 else c1) (mirIf π g) := by
  cases π <;> rfl

end Ag

open Ag

section combs
variable (n : ℕ)

/-- The leftmost minimum of `[A (if a < n), (v, u), Bq (if b < n)]`. -/
def lmn (a : ℕ) (A : ℝ × ℕ) (v : ℝ) (u : ℕ) (b : ℕ) (Bq : ℝ × ℕ) : ℝ × ℕ :=
  if b < n ∧ Bq.1 < (if a < n ∧ ¬ v < A.1 then A else (v, u)).1 then Bq
  else if a < n ∧ ¬ v < A.1 then A else (v, u)

/-- Combine the aggregates of the left child `a`, of the node `u` with values `v1`, `v2` and of
the right child `b` (a child `≥ n` is absent; its count and sums are still added). -/
def comb (a : ℕ) (A : Ag) (u : ℕ) (v1 v2 : ℝ) (b : ℕ) (Bg : Ag) : Ag :=
  ⟨A.c + Bg.c + 1, A.s1 + v1 + Bg.s1, A.s2 + v2 + Bg.s2,
    (lmn n a (A.m1, A.a1) v1 u b (Bg.m1, Bg.a1)).1, (lmn n a (A.m2, A.a2) v2 u b (Bg.m2, Bg.a2)).1,
    (lmn n a (A.m1, A.a1) v1 u b (Bg.m1, Bg.a1)).2, (lmn n b (Bg.m1, Bg.b1) v1 u a (A.m1, A.b1)).2,
    (lmn n a (A.m2, A.a2) v2 u b (Bg.m2, Bg.a2)).2, (lmn n b (Bg.m2, Bg.b2) v2 u a (A.m2, A.b2)).2,
    if a < n then A.lm else u, if b < n then Bg.rm else u⟩

lemma lmn_fst_symm (a : ℕ) (m m' : ℝ) (i j i' j' : ℕ) (v : ℝ) (u : ℕ) (b : ℕ) :
    (lmn n a (m, i) v u b (m', i')).1 = (lmn n b (m', j') v u a (m, j)).1 := by
  unfold lmn
  by_cases ha : a < n <;> by_cases hb : b < n <;> simp only [ha, hb, true_and, false_and,
    ite_false] <;> split_ifs <;> simp_all <;> linarith

/-- **Mirror image of a combination.** -/
lemma mir_comb (a : ℕ) (A : Ag) (u : ℕ) (v1 v2 : ℝ) (b : ℕ) (Bg : Ag) :
    (comb n a A u v1 v2 b Bg).mir = comb n b Bg.mir u v2 v1 a A.mir := by
  ext <;> simp only [mir, comb]
  · ring
  · ring
  · ring
  · exact lmn_fst_symm n _ _ _ _ _ _ _ _ _ _
  · exact lmn_fst_symm n _ _ _ _ _ _ _ _ _ _

/-- A child read as `A` in place of `A'`: the same count and sums, and the same aggregates if
present. -/
def ChildOK (a : ℕ) (A A' : Ag) : Prop :=
  (A.c = A'.c ∧ A.s1 = A'.s1 ∧ A.s2 = A'.s2) ∧ (a < n → A = A')

lemma ChildOK.mir {a : ℕ} {A A' : Ag} (h : ChildOK n a A A') : ChildOK n a A.mir A'.mir :=
  ⟨⟨h.1.1, h.1.2.2, h.1.2.1⟩, fun ha => by rw [h.2 ha]⟩

lemma ChildOK.mirI {a : ℕ} {A A' : Ag} (π : Bool) (h : ChildOK n a A A') :
    ChildOK n a (Ag.mirIf π A) (Ag.mirIf π A') := by
  cases π
  · exact h
  · exact h.mir n

lemma ChildOK.of_mirI {a : ℕ} {A A' : Ag} (π : Bool) (h : ChildOK n a (Ag.mirIf π A) A') :
    ChildOK n a A (Ag.mirIf π A') := by
  have := h.mirI n π
  rwa [mirIf_mirIf] at this

lemma comb_congr {a a' b b' u : ℕ} {A A' Bg Bg' : Ag} {v1 v2 : ℝ} (ha : a < n ↔ a' < n)
    (hA : ChildOK n a A A') (hb : b < n ↔ b' < n) (hB : ChildOK n b Bg Bg') :
    comb n a A u v1 v2 b Bg = comb n a' A' u v1 v2 b' Bg' := by
  obtain ⟨⟨c1, s1, t1⟩, e1⟩ := hA
  obtain ⟨⟨c2, s2, t2⟩, e2⟩ := hB
  have k1 : ∀ (f : Ag → ℝ × ℕ) (g : ℝ × ℕ), (if a < n ∧ ¬ v1 < (f A).1 then f A else g) =
      (if a' < n ∧ ¬ v1 < (f A').1 then f A' else g) := by
    intro f g; by_cases h : a < n
    · rw [e1 h]; simp [h, ha.mp h]
    · simp [h, mt ha.mpr h]
  have k2 : ∀ (f : Ag → ℝ × ℕ) (g : ℝ × ℕ), (if a < n ∧ ¬ v2 < (f A).1 then f A else g) =
      (if a' < n ∧ ¬ v2 < (f A').1 then f A' else g) := by
    intro f g; by_cases h : a < n
    · rw [e1 h]; simp [h, ha.mp h]
    · simp [h, mt ha.mpr h]
  have k3 : ∀ (f : Ag → ℝ × ℕ) (g : ℝ × ℕ) (w : ℝ), (if b < n ∧ (f Bg).1 < w then f Bg else g) =
      (if b' < n ∧ (f Bg').1 < w then f Bg' else g) := by
    intro f g w; by_cases h : b < n
    · rw [e2 h]; simp [h, hb.mp h]
    · simp [h, mt hb.mpr h]
  have k4 : ∀ (f : Ag → ℝ × ℕ) (g : ℝ × ℕ) (v : ℝ), (if b < n ∧ ¬ v < (f Bg).1 then f Bg else g) =
      (if b' < n ∧ ¬ v < (f Bg').1 then f Bg' else g) := by
    intro f g v; by_cases h : b < n
    · rw [e2 h]; simp [h, hb.mp h]
    · simp [h, mt hb.mpr h]
  have k5 : ∀ (f : Ag → ℝ × ℕ) (g : ℝ × ℕ) (w : ℝ), (if a < n ∧ (f A).1 < w then f A else g) =
      (if a' < n ∧ (f A').1 < w then f A' else g) := by
    intro f g w; by_cases h : a < n
    · rw [e1 h]; simp [h, ha.mp h]
    · simp [h, mt ha.mpr h]
  have kl : (if a < n then A.lm else u) = (if a' < n then A'.lm else u) := by
    by_cases h : a < n
    · rw [e1 h]; simp [h, ha.mp h]
    · simp [h, mt ha.mpr h]
  have kr : (if b < n then Bg.rm else u) = (if b' < n then Bg'.rm else u) := by
    by_cases h : b < n
    · rw [e2 h]; simp [h, hb.mp h]
    · simp [h, mt hb.mpr h]
  simp only [comb, lmn]
  rw [k1 (fun A => (A.m1, A.a1)), k2 (fun A => (A.m2, A.a2)), k4 (fun B => (B.m1, B.b1)),
    k4 (fun B => (B.m2, B.b2)), kl, kr, c1, c2, s1, s2, t1, t2]
  simp only []
  rw [k3 (fun B => (B.m1, B.a1)), k3 (fun B => (B.m2, B.a2)), k5 (fun A => (A.m1, A.b1)),
    k5 (fun A => (A.m2, A.b2))]

end combs

/-! ### What is stored at a node -/

section stored
variable (B n : ℕ)

/-- The aggregates stored at `u` (without its tags). -/
def own (M : Mem) (u : ℕ) : Ag :=
  ⟨cnt B M u, sm B M u, sm2 B M u, mn B M u, mn2 B M u, am B M u, amr B M u, am2 B M u,
    am2r B M u, lm B M u, rtm B M u⟩

/-- The aggregates of `u` as its parent reads them. -/
def rd (M : Mem) (u : ℕ) : Ag := addTags (tg B M u) (tg2 B M u) (own B M u)

/-- The aggregates of `u` are computed from its children. -/
def AggOK (M : Mem) (u : ℕ) : Prop :=
  own B M u = if rv B M u then
      comb n (rc B M u) (rd B M (rc B M u)).mir u (vl B M u) (vl2 B M u) (lc B M u)
        (rd B M (lc B M u)).mir
    else comb n (lc B M u) (rd B M (lc B M u)) u (vl B M u) (vl2 B M u) (rc B M u)
        (rd B M (rc B M u))

lemma aggOK_iff {M : Mem} {u : ℕ} : AggOK B n M u ↔ own B M u = mirIf (rv B M u)
    (comb n (lc B M u) (rd B M (lc B M u)) u (vlc B M (rv B M u) u) (vlc B M (!rv B M u) u)
      (rc B M u) (rd B M (rc B M u))) := by
  unfold AggOK
  cases rv B M u
  · simp [vlc]
  · simp [vlc, mir_comb]

/-- The parity of the children of a node with parity `π`. -/
abbrev cσ (M : Mem) (π : Bool) (x : ℕ) : Bool := π ^^ rv B M x

/-- The virtual tree `t` is stored in `M` with parity `π`, its root pointing to `p`. -/
inductive Enc (M : Mem) : VT → ℕ → Bool → Prop
  | leaf (p : ℕ) (π : Bool) : Enc M leaf p π
  | node {l r : VT} {x p : ℕ} {ds : List VT} {π : Bool} :
      par B M x = p → lcS B M (cσ B M π x) x = rt n l → lcS B M (!cσ B M π x) x = rt n r →
      AggOK B n M x → Enc M l x (cσ B M π x) → Enc M r x (cσ B M π x) →
      (∀ d ∈ ds, Enc M d x false) → Enc M (node l x r ds) p π

/-- The node above the hole of a zipper (`p` above the whole). -/
def hp (p : ℕ) : List Frame → ℕ
  | [] => p
  | f :: _ => f.y

/-- A frame is stored with parity `π` at its node, the hole having root `r`. -/
def EncF (M : Mem) : Frame → ℕ → Bool → Prop
  | .L y c dy, r, π => lcS B M (cσ B M π y) y = r ∧ lcS B M (!cσ B M π y) y = rt n c ∧
      AggOK B n M y ∧ Enc B n M c y (cσ B M π y) ∧ ∀ d ∈ dy, Enc B n M d y false
  | .R c y dy, r, π => lcS B M (cσ B M π y) y = rt n c ∧ lcS B M (!cσ B M π y) y = r ∧
      AggOK B n M y ∧ Enc B n M c y (cσ B M π y) ∧ ∀ d ∈ dy, Enc B n M d y false
  | .D l y r bef aft, _, π => lcS B M (cσ B M π y) y = rt n l ∧
      lcS B M (!cσ B M π y) y = rt n r ∧ AggOK B n M y ∧
      Enc B n M l y (cσ B M π y) ∧ Enc B n M r y (cσ B M π y) ∧
      ∀ d ∈ bef ++ aft, Enc B n M d y false

/-- The parity of the hole of a frame whose node has parity `π`. -/
def hpar (M : Mem) : Frame → Bool → Bool
  | .D _ _ _ _ _, _ => false
  | f, π => cσ B M π f.y

/-- The parity at the hole of a zipper. -/
def cpar (M : Mem) : List Frame → Bool
  | [] => false
  | f :: fs => hpar B M f (cpar M fs)

/-- A zipper is stored, the hole having root `r` and the whole tree parent `p`. -/
def EncC (M : Mem) : List Frame → ℕ → ℕ → Prop
  | [], _, _ => True
  | f :: fs, r, p => EncF B n M f r (cpar B M fs) ∧ par B M f.y = hp p fs ∧ EncC M fs f.y p

/-- The nil record. -/
structure NilOK (M : Mem) : Prop where
  lc : lc B M n = n
  rc : rc B M n = n
  cnt : cnt B M n = 0
  sm : sm B M n = 0
  sm2 : sm2 B M n = 0

/-- Shift the values of a list. -/
def shift (c : ℝ) (L : List (ℕ × ℝ)) : List (ℕ × ℝ) := L.map fun q => (q.1, q.2 + c)

/-- The values of channel `k` of an auxiliary tree stored with parity `π`, in order, relative to
the tags above its root. -/
def rs (M : Mem) : VT → Bool → Bool → List (ℕ × ℝ)
  | leaf, _, _ => []
  | node l x r _, π, k => shift (tgc B M (k ^^ π) x)
      (rs M l (cσ B M π x) k ++ (x, vlc B M (k ^^ π) x) :: rs M r (cσ B M π x) k)

mutual
/-- The values of channel `k` of the hanging trees. -/
def dV (M : Mem) : VT → Bool → List (ℕ × ℝ)
  | leaf, _ => []
  | node l _ r ds, k => dV M l k ++ dV M r k ++ dVL M ds k
/-- The values of channel `k` of a list of virtual trees. -/
def dVL (M : Mem) : List VT → Bool → List (ℕ × ℝ)
  | [], _ => []
  | d :: ds, k => rs B M d false k ++ dV M d k ++ dVL M ds k
end

/-- The global invariant: `G` is stored at base `B`, its labels are `0, …, n-1`. -/
structure Inv (M : Mem) (G : List VT) : Prop where
  enc : ∀ T ∈ G, Enc B n M T n false
  nodup : (nodesL G).Nodup
  cover : ∀ u, u ∈ nodesL G ↔ u < n
  nil : NilOK B n M

/-- `G`, stored in `M`, represents the forest `F`: its edges and both values. -/
structure RepE (M : Mem) (G : List VT) (F : Forest) : Prop where
  par : ∀ u p, (u, p) ∈ dEL n G → F.par u = p
  val : ∀ u w, (u, w) ∈ dVL B M G false → F.val u = w
  val2 : ∀ u w, (u, w) ∈ dVL B M G true → F.val2 u = w

/-- `G` represents `F`, and `fpar` is the parent function. -/
structure Rep (M : Mem) (G : List VT) (F : Forest) : Prop extends RepE B n M G F where
  fpar : ∀ u < n, fpar B M u = F.par u

end stored

/-! ### Basic lemmas -/

lemma ite_of_pos {α : Type*} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

lemma ite_of_neg {α : Type*} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]

section lemmas
variable {B n : ℕ}

@[simp] lemma rs_leaf (M : Mem) (π k : Bool) : rs B M leaf π k = [] := rfl
lemma rs_node (M : Mem) (l r : VT) (x : ℕ) (ds : List VT) (π k : Bool) :
    rs B M (node l x r ds) π k = shift (tgc B M (k ^^ π) x)
      (rs B M l (cσ B M π x) k ++ (x, vlc B M (k ^^ π) x) :: rs B M r (cσ B M π x) k) := rfl
@[simp] lemma dV_leaf (M : Mem) (k : Bool) : dV B M leaf k = [] := rfl
@[simp] lemma dV_node (M : Mem) (l r : VT) (x : ℕ) (ds : List VT) (k : Bool) :
    dV B M (node l x r ds) k = dV B M l k ++ dV B M r k ++ dVL B M ds k := rfl
@[simp] lemma dVL_nil (M : Mem) (k : Bool) : dVL B M [] k = [] := rfl
@[simp] lemma dVL_cons (M : Mem) (d : VT) (ds : List VT) (k : Bool) :
    dVL B M (d :: ds) k = rs B M d false k ++ dV B M d k ++ dVL B M ds k := rfl
@[simp] lemma dVL_append (M : Mem) (a b : List VT) (k : Bool) :
    dVL B M (a ++ b) k = dVL B M a k ++ dVL B M b k := by
  induction a with
  | nil => simp
  | cons t a ih => simp [ih]

@[simp] lemma shift_append (c : ℝ) (L L' : List (ℕ × ℝ)) :
    shift c (L ++ L') = shift c L ++ shift c L' := by simp [shift]
@[simp] lemma shift_cons (c : ℝ) (q : ℕ × ℝ) (L : List (ℕ × ℝ)) :
    shift c (q :: L) = (q.1, q.2 + c) :: shift c L := by simp [shift]
@[simp] lemma shift_nil (c : ℝ) : shift c [] = [] := rfl
lemma shift_shift (c d : ℝ) (L : List (ℕ × ℝ)) : shift d (shift c L) = shift (c + d) L := by
  simp [shift, Function.comp_def, add_assoc]
@[simp] lemma length_shift (c : ℝ) (L : List (ℕ × ℝ)) : (shift c L).length = L.length := by
  simp [shift]
lemma map_fst_shift (c : ℝ) (L : List (ℕ × ℝ)) : (shift c L).map Prod.fst = L.map Prod.fst := by
  simp [shift, Function.comp_def]
lemma reverse_shift (c : ℝ) (L : List (ℕ × ℝ)) : (shift c L).reverse = shift c L.reverse := by
  simp [shift, List.map_reverse]
lemma sum_shift (c : ℝ) (L : List (ℕ × ℝ)) :
    ((shift c L).map Prod.snd).sum = (L.map Prod.snd).sum + c * L.length := by
  induction L with
  | nil => simp
  | cons q L ih => simp only [shift_cons, List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

lemma lmin_shift (c : ℝ) {L : List (ℕ × ℝ)} (h : L ≠ []) :
    lmin (shift c L) = ((lmin L).1 + c, (lmin L).2) := by
  induction L with
  | nil => exact absurd rfl h
  | cons p L ih =>
    rcases L with _ | ⟨q, L⟩
    · rfl
    · have ih' := ih (by simp)
      simp only [shift_cons] at ih' ⊢
      rw [lmin_cons, ih', lmin_cons]
      split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; linarith)

lemma lmin_snoc_cons {A C : List (ℕ × ℝ)} (q : ℕ × ℝ) :
    lmin (A ++ q :: C) =
      let p1 := if A ≠ [] ∧ ¬ q.2 < (lmin A).1 then lmin A else (q.2, q.1)
      if C ≠ [] ∧ (lmin C).1 < p1.1 then lmin C else p1 := by
  have e1 : ∀ D : List (ℕ × ℝ), lmin (q :: D) =
      if D ≠ [] ∧ (lmin D).1 < q.2 then lmin D else (q.2, q.1) := by
    intro D; rcases D with _ | ⟨r, D⟩
    · simp [lmin]
    · simp [lmin_cons]
  have hq : lmin [q] = (q.2, q.1) := rfl
  rcases A with _ | ⟨a, A⟩
  · simp [e1]
  · rw [show (a :: A) ++ q :: C = ((a :: A) ++ [q]) ++ C by simp]
    rcases C with _ | ⟨c, C⟩
    · rw [List.append_nil, lmin_append (by simp) (by simp), hq]
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and, not_true_eq_false, false_and,
        ite_false]
      split_ifs <;> rfl
    · rw [lmin_append (by simp) (by simp), lmin_append (by simp) (by simp), hq]
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and]
      split_ifs <;> rfl

/-- The least value of a nonempty list is a value of the list and below all of them. -/
lemma lmin_spec : ∀ {L : List (ℕ × ℝ)}, L ≠ [] →
    (lmin L).1 ∈ L.map Prod.snd ∧ ∀ q ∈ L, (lmin L).1 ≤ q.2
  | [], h => absurd rfl h
  | [p], _ => ⟨by simp [lmin], by simp [lmin]⟩
  | p :: q :: L, _ => by
    obtain ⟨h1, h2⟩ := lmin_spec (L := q :: L) (by simp)
    rw [lmin_cons]
    split_ifs with h
    · refine ⟨List.mem_cons_of_mem _ h1, fun r hr => ?_⟩
      rcases List.mem_cons.mp hr with rfl | hr
      · exact h.le
      · exact h2 r hr
    · refine ⟨by simp, fun r hr => ?_⟩
      rcases List.mem_cons.mp hr with rfl | hr
      · exact le_refl _
      · exact le_trans (not_lt.mp h) (h2 r hr)

lemma lmin_fst_eq {L L' : List (ℕ × ℝ)} (hL : L ≠ []) (hL' : L' ≠ [])
    (h : ∀ x, x ∈ L.map Prod.snd ↔ x ∈ L'.map Prod.snd) : (lmin L).1 = (lmin L').1 := by
  obtain ⟨a1, a2⟩ := lmin_spec hL
  obtain ⟨b1, b2⟩ := lmin_spec hL'
  obtain ⟨q, hq, eq⟩ := List.mem_map.mp ((h _).mpr b1)
  obtain ⟨q', hq', eq'⟩ := List.mem_map.mp ((h _).mp a1)
  have := a2 q hq
  have := b2 q' hq'
  linarith

/-- The rightmost minimum. -/
def rmin (L : List (ℕ × ℝ)) : ℝ × ℕ := lmin L.reverse

lemma rmin_fst {L : List (ℕ × ℝ)} (h : L ≠ []) : (rmin L).1 = (lmin L).1 :=
  lmin_fst_eq (by simpa using h) h (fun x => by simp [List.map_reverse])

/-- The true aggregates of the values `L0`, `L1` of the two channels along the path `S`. -/
def tAg (n : ℕ) (L0 L1 : List (ℕ × ℝ)) (S : List ℕ) : Ag :=
  ⟨L0.length, (L0.map Prod.snd).sum, (L1.map Prod.snd).sum, (lmin L0).1, (lmin L1).1,
    (lmin L0).2, (rmin L0).2, (lmin L1).2, (rmin L1).2, S.headD n, S.getLastD n⟩

lemma lmn_eq_lmin {a b u : ℕ} {L R : List (ℕ × ℝ)} (v : ℝ) (ha : a < n ↔ L ≠ [])
    (hb : b < n ↔ R ≠ []) :
    lmn n a ((lmin L).1, (lmin L).2) v u b ((lmin R).1, (lmin R).2) = lmin (L ++ (u, v) :: R) := by
  rw [lmin_snoc_cons, lmn]
  simp only [ha, hb]

/-- **The aggregates of a node from those of its children.** -/
lemma tAg_join {a b u : ℕ} {L0 L1 R0 R1 : List (ℕ × ℝ)} {sl sr : List ℕ} (v0 v1 c0 c1 : ℝ)
    (hl0 : L0.map Prod.fst = sl) (hl1 : L1.map Prod.fst = sl) (hr0 : R0.map Prod.fst = sr)
    (hr1 : R1.map Prod.fst = sr) (ha : a < n ↔ sl ≠ []) (hb : b < n ↔ sr ≠ []) :
    tAg n (shift c0 (L0 ++ (u, v0) :: R0)) (shift c1 (L1 ++ (u, v1) :: R1)) (sl ++ u :: sr) =
      addTags c0 c1 (comb n a (tAg n L0 L1 sl) u v0 v1 b (tAg n R0 R1 sr)) := by
  have nl : ∀ {L : List (ℕ × ℝ)} {s : List ℕ}, L.map Prod.fst = s → (L ≠ [] ↔ s ≠ []) := by
    intro L s h; subst h; simp
  have ha0 := ha.trans (nl hl0).symm
  have ha1 := ha.trans (nl hl1).symm
  have hb0 := hb.trans (nl hr0).symm
  have hb1 := hb.trans (nl hr1).symm
  have hne : ∀ (L : List (ℕ × ℝ)) (q : ℕ × ℝ) (R : List (ℕ × ℝ)), L ++ q :: R ≠ [] := by simp
  have rv : ∀ (L R : List (ℕ × ℝ)) (q : ℕ × ℝ), (L ++ q :: R).reverse = R.reverse ++ q :: L.reverse := by
    simp
  have hra : ∀ {L : List (ℕ × ℝ)}, (a < n ↔ L ≠ []) → (a < n ↔ L.reverse ≠ []) := by
    intro L h; simpa using h
  have hrb : ∀ {L : List (ℕ × ℝ)}, (b < n ↔ L ≠ []) → (b < n ↔ L.reverse ≠ []) := by
    intro L h; simpa using h
  have len : ∀ {L : List (ℕ × ℝ)} {s : List ℕ}, L.map Prod.fst = s → L.length = s.length := by
    intro L s h; subst h; simp
  ext
  · simp [tAg, addTags, comb]; ring
  · simp only [tAg, addTags, comb, sum_shift]; simp; ring
  · simp only [tAg, addTags, comb, sum_shift]; simp
    rw [len hl0, len hl1, len hr0, len hr1]; push_cast; ring
  · simp only [tAg, addTags, comb, lmin_shift _ (hne _ _ _)]
    rw [lmn_eq_lmin v0 ha0 hb0]
  · simp only [tAg, addTags, comb, lmin_shift _ (hne _ _ _)]
    rw [lmn_eq_lmin v1 ha1 hb1]
  · simp only [tAg, addTags, comb, lmin_shift _ (hne _ _ _)]
    rw [lmn_eq_lmin v0 ha0 hb0]
  · simp only [tAg, addTags, comb, rmin, reverse_shift, rv, lmin_shift _ (hne _ _ _)]
    have e1 : ((lmin R0).1, (lmin R0.reverse).2) = ((lmin R0.reverse).1, (lmin R0.reverse).2) := by
      by_cases h : R0 = []
      · subst h; rfl
      · rw [← rmin_fst h]; rfl
    have e2 : ((lmin L0).1, (lmin L0.reverse).2) = ((lmin L0.reverse).1, (lmin L0.reverse).2) := by
      by_cases h : L0 = []
      · subst h; rfl
      · rw [← rmin_fst h]; rfl
    rw [e1, e2, lmn_eq_lmin v0 (hrb hb0) (hra ha0)]
  · simp only [tAg, addTags, comb, lmin_shift _ (hne _ _ _)]
    rw [lmn_eq_lmin v1 ha1 hb1]
  · simp only [tAg, addTags, comb, rmin, reverse_shift, rv, lmin_shift _ (hne _ _ _)]
    have e1 : ((lmin R1).1, (lmin R1.reverse).2) = ((lmin R1.reverse).1, (lmin R1.reverse).2) := by
      by_cases h : R1 = []
      · subst h; rfl
      · rw [← rmin_fst h]; rfl
    have e2 : ((lmin L1).1, (lmin L1.reverse).2) = ((lmin L1.reverse).1, (lmin L1.reverse).2) := by
      by_cases h : L1 = []
      · subst h; rfl
      · rw [← rmin_fst h]; rfl
    rw [e1, e2, lmn_eq_lmin v1 (hrb hb1) (hra ha1)]
  · simp only [tAg, addTags, comb]
    by_cases h : a < n
    · obtain ⟨s, ss, rfl⟩ := List.exists_cons_of_ne_nil (ha.mp h); simp [h]
    · have : sl = [] := by by_contra h'; exact h (ha.mpr h')
      subst this; simp [h]
  · simp only [tAg, addTags, comb]
    by_cases h : b < n
    · simp only [h, ite_true]
      obtain ⟨s, ss, e⟩ := List.exists_cons_of_ne_nil (hb.mp h)
      rw [e, List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_append]
      simp [List.getLast?_cons]
    · have : sr = [] := by by_contra h'; exact h (hb.mpr h')
      subst this; simp [h, List.getLastD_eq_getLast?]

lemma rs_fst (M : Mem) : ∀ (t : VT) (π k : Bool), (rs B M t π k).map Prod.fst = seq t
  | leaf, _, _ => rfl
  | node l x r ds, π, k => by
    simp only [rs_node, map_fst_shift, List.map_append, List.map_cons, rs_fst M l, rs_fst M r,
      seq_node]

lemma rs_length (M : Mem) (t : VT) (π k : Bool) : (rs B M t π k).length = (seq t).length := by
  rw [← rs_fst M t π k, List.length_map]

lemma rs_ne_nil (M : Mem) {t : VT} (π k : Bool) : rs B M t π k ≠ [] ↔ t ≠ leaf := by
  rw [← List.length_pos_iff, rs_length, List.length_pos_iff, Ne, Ne, seq_eq_nil]

end lemmas

/-! ### Agreement of memories -/

section agree
variable (B n : ℕ)

/-- `M'` agrees with `M` on the fields of `u`. -/
def Agr (M M' : Mem) (u : ℕ) : Prop :=
  ∀ j < 16, M'.nm (adr B u j) = M.nm (adr B u j) ∧ M'.rm (adr B u j) = M.rm (adr B u j)

/-- `M'` agrees with `M` on the fields of `u` except `par` and the two tags. -/
def AgrC (M M' : Mem) (u : ℕ) : Prop :=
  ∀ j < 16, (j ≠ 0 → M'.nm (adr B u j) = M.nm (adr B u j)) ∧
    (j ≠ 1 → j ≠ 6 → M'.rm (adr B u j) = M.rm (adr B u j))

lemma Agr.agrC {M M' : Mem} {u : ℕ} (h : Agr B M M' u) : AgrC B M M' u :=
  fun j hj => ⟨fun _ => (h j hj).1, fun _ _ => (h j hj).2⟩

lemma Agr.rdEq {M M' : Mem} {u : ℕ} (h : Agr B M M' u) : rd B M' u = rd B M u := by
  simp only [rd, own, addTags, cnt, sm, sm2, mn, mn2, am, amr, am2, am2r, lm, rtm, tg, tg2]
  rw [(h 1 (by omega)).2, (h 2 (by omega)).2, (h 3 (by omega)).2, (h 4 (by omega)).2,
    (h 6 (by omega)).2, (h 7 (by omega)).2, (h 8 (by omega)).2, (h 3 (by omega)).1,
    (h 5 (by omega)).1, (h 6 (by omega)).1, (h 7 (by omega)).1, (h 8 (by omega)).1,
    (h 9 (by omega)).1]

lemma AgrC.ownEq {M M' : Mem} {u : ℕ} (h : AgrC B M M' u) : own B M' u = own B M u := by
  simp only [own, cnt, sm, sm2, mn, mn2, am, amr, am2, am2r, lm, rtm]
  rw [(h 2 (by omega)).2 (by omega) (by omega), (h 3 (by omega)).2 (by omega) (by omega),
    (h 4 (by omega)).2 (by omega) (by omega), (h 7 (by omega)).2 (by omega) (by omega),
    (h 8 (by omega)).2 (by omega) (by omega), (h 3 (by omega)).1 (by omega),
    (h 5 (by omega)).1 (by omega), (h 6 (by omega)).1 (by omega), (h 7 (by omega)).1 (by omega),
    (h 8 (by omega)).1 (by omega), (h 9 (by omega)).1 (by omega)]

lemma AgrC.rvEq {M M' : Mem} {u : ℕ} (h : AgrC B M M' u) : rv B M' u = rv B M u := by
  simp only [DynTree.rv, rvw]; rw [(h 10 (by omega)).1 (by omega)]

/-- What a parent reads of a child `a` in `M`, and of `a'` in `M'`, is the same. -/
structure Look (M M' : Mem) (a a' : ℕ) : Prop where
  lt : a < n ↔ a' < n
  cnt : cnt B M' a' = cnt B M a
  sumA : sumA B M' a' = sumA B M a
  sumA2 : sumA2 B M' a' = sumA2 B M a
  rd : a < n → rd B M' a' = rd B M a

lemma Look.childOK {M M' : Mem} {a a' : ℕ} (h : Look B n M M' a a') :
    ChildOK n a (DynTree.rd B M' a') (DynTree.rd B M a) :=
  ⟨⟨h.cnt, h.sumA, h.sumA2⟩, h.rd⟩

lemma look_of_agr {M M' : Mem} {a : ℕ} (h : Agr B M M' a) : Look B n M M' a a := by
  have e := h.rdEq B
  refine ⟨Iff.rfl, ?_, ?_, ?_, fun _ => e⟩
  · exact congrArg Ag.c e
  · exact congrArg Ag.s1 e
  · exact congrArg Ag.s2 e

lemma look_nil {M M' : Mem} (hN : NilOK B n M) (hN' : NilOK B n M') : Look B n M M' n n :=
  ⟨Iff.rfl, by rw [hN.cnt, hN'.cnt], by simp only [sumA]; rw [hN.cnt, hN'.cnt, hN.sm, hN'.sm]; ring,
    by simp only [sumA2]; rw [hN.cnt, hN'.cnt, hN.sm2, hN'.sm2]; ring,
    fun h => absurd h (lt_irrefl n)⟩

/-- The combination at `u` read in `M'` is the one read in `M`. -/
lemma comb_eq {M M' : Mem} {u : ℕ} (hv : vl B M' u = vl B M u) (hv2 : vl2 B M' u = vl2 B M u)
    (hl : Look B n M M' (lc B M u) (lc B M' u)) (hr : Look B n M M' (rc B M u) (rc B M' u)) :
    comb n (lc B M' u) (rd B M' (lc B M' u)) u (vl B M' u) (vl2 B M' u) (rc B M' u)
        (rd B M' (rc B M' u)) =
      comb n (lc B M u) (rd B M (lc B M u)) u (vl B M u) (vl2 B M u) (rc B M u)
        (rd B M (rc B M u)) ∧
    comb n (rc B M' u) (rd B M' (rc B M' u)).mir u (vl B M' u) (vl2 B M' u) (lc B M' u)
        (rd B M' (lc B M' u)).mir =
      comb n (rc B M u) (rd B M (rc B M u)).mir u (vl B M u) (vl2 B M u) (lc B M u)
        (rd B M (lc B M u)).mir := by
  rw [hv, hv2]
  have l1 := (hl.childOK B n)
  have r1 := (hr.childOK B n)
  have hlt : lc B M' u < n ↔ lc B M u < n := hl.lt.symm
  have hrt : rc B M' u < n ↔ rc B M u < n := hr.lt.symm
  refine ⟨comb_congr n hlt ?_ hrt ?_, comb_congr n hrt ?_ hlt ?_⟩
  · exact ⟨l1.1, fun h => l1.2 (hlt.mp h)⟩
  · exact ⟨r1.1, fun h => r1.2 (hrt.mp h)⟩
  · exact ⟨(r1.mir n).1, fun h => (r1.mir n).2 (hrt.mp h)⟩
  · exact ⟨(l1.mir n).1, fun h => (l1.mir n).2 (hlt.mp h)⟩

lemma AggOK.transfer {M M' : Mem} {u : ℕ} (h : AggOK B n M u) (ho : own B M' u = own B M u)
    (hv : vl B M' u = vl B M u) (hv2 : vl2 B M' u = vl2 B M u) (hrv : rv B M' u = rv B M u)
    (hl : Look B n M M' (lc B M u) (lc B M' u)) (hr : Look B n M M' (rc B M u) (rc B M' u)) :
    AggOK B n M' u := by
  obtain ⟨e1, e2⟩ := comb_eq B n hv hv2 hl hr
  unfold AggOK at h ⊢
  rw [ho, h, hrv, e1, e2]

lemma AggOK.of_agrC {M M' : Mem} {u : ℕ} (h : AggOK B n M u) (hu : AgrC B M M' u)
    (hl : Look B n M M' (lc B M u) (lc B M u)) (hr : Look B n M M' (rc B M u) (rc B M u)) :
    AggOK B n M' u := by
  have e1 : lc B M' u = lc B M u := (hu 1 (by omega)).1 (by omega)
  have e2 : rc B M' u = rc B M u := (hu 2 (by omega)).1 (by omega)
  exact h.transfer B n (hu.ownEq B) ((hu 0 (by omega)).2 (by omega) (by omega))
    ((hu 5 (by omega)).2 (by omega) (by omega)) (hu.rvEq B) (e1 ▸ hl) (e2 ▸ hr)

/-! ### Encoding: basic facts and the frame lemma -/

lemma Enc.par_rt {M : Mem} {t : VT} {p : ℕ} {π : Bool} (h : Enc B n M t p π)
    (ht : t ≠ VT.leaf) : par B M (rt n t) = p := by
  cases h with
  | leaf => exact absurd rfl ht
  | node hp => exact hp

lemma enc_node_iff {M : Mem} {l r : VT} {x p : ℕ} {ds : List VT} {π : Bool} :
    Enc B n M (node l x r ds) p π ↔ par B M x = p ∧ lcS B M (cσ B M π x) x = rt n l ∧
      lcS B M (!cσ B M π x) x = rt n r ∧ AggOK B n M x ∧ Enc B n M l x (cσ B M π x) ∧
      Enc B n M r x (cσ B M π x) ∧ ∀ d ∈ ds, Enc B n M d x false := by
  constructor
  · intro h; cases h with
    | node h1 h2 h3 h4 h5 h6 h7 => exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩; exact .node h1 h2 h3 h4 h5 h6 h7

/-- A node that is not reversed, read with parity `false`, stores its children in order. -/
lemma enc_node_iff_clean {M : Mem} {l r : VT} {x p : ℕ} {ds : List VT}
    (hx : rv B M x = false) :
    Enc B n M (node l x r ds) p false ↔ par B M x = p ∧ lc B M x = rt n l ∧
      rc B M x = rt n r ∧ AggOK B n M x ∧ Enc B n M l x false ∧
      Enc B n M r x false ∧ ∀ d ∈ ds, Enc B n M d x false := by
  rw [enc_node_iff]
  simp [cσ, hx, lcS]

/-- **Mirror image.** A tree stored with parity `π` is its mirror image stored with parity
`!π`. -/
theorem enc_mirror {M : Mem} : ∀ {t : VT} {p : ℕ} {π : Bool},
    Enc B n M t p π → Enc B n M (mirT t) p (!π)
  | _, _, _, .leaf p π => .leaf p _
  | _, _, π, .node (l := l) (r := r) (x := x) h1 h2 h3 h4 h5 h6 h7 => by
    have e : cσ B M (!π) x = !cσ B M π x := by simp [cσ]
    refine .node h1 ?_ ?_ h4 ?_ ?_ h7
    · rw [e, rt_mirT]; exact h3
    · rw [e, Bool.not_not, rt_mirT]; exact h2
    · rw [e]; exact enc_mirror h6
    · rw [e]; exact enc_mirror h5

lemma enc_mirror_iff {M : Mem} {t : VT} {p : ℕ} {π : Bool} :
    Enc B n M (mirT t) p π ↔ Enc B n M t p (!π) := by
  constructor
  · intro h; have := enc_mirror B n h; rwa [mirT_mirT] at this
  · intro h; have := enc_mirror B n h; rwa [Bool.not_not] at this

lemma mem_nodesL_of {ds : List VT} {d : VT} (hd : d ∈ ds) {u : ℕ} (hu : u ∈ nodes d) :
    u ∈ nodesL ds := by
  induction ds with
  | nil => simp at hd
  | cons d' ds ih =>
    simp only [List.mem_cons] at hd
    simp only [nodesL_cons, List.mem_append]
    rcases hd with rfl | hd
    · exact Or.inl hu
    · exact Or.inr (ih hd)

lemma nodup_of_mem_nodesL {ds : List VT} (h : (nodesL ds).Nodup) {d : VT} (hd : d ∈ ds) :
    (nodes d).Nodup := by
  induction ds with
  | nil => simp at hd
  | cons d' ds ih =>
    simp only [nodesL_cons, List.nodup_append] at h
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact h.1
    · exact ih h.2.1 hd

lemma rt_mem_nodes {s : VT} (hs : s ≠ VT.leaf) (n : ℕ) : rt n s ∈ nodes s := by
  cases s with
  | leaf => exact absurd rfl hs
  | node a y b dy => simp

/-- **Frame lemma.** An encoding survives any change of memory outside its nodes, and of the
`par` and tag fields of its root. -/
theorem Enc.frame {M M' : Mem} (hN : NilOK B n M) (hN' : NilOK B n M') {t : VT} {p : ℕ}
    {π : Bool} (h : Enc B n M t p π) : (nodes t).Nodup →
    ∀ p', (∀ u ∈ nodes t, u ≠ rt n t → Agr B M M' u) → (t ≠ VT.leaf → AgrC B M M' (rt n t)) →
    (t ≠ VT.leaf → par B M' (rt n t) = p') → Enc B n M' t p' π := by
  induction h with
  | leaf p π => intros; exact .leaf _ _
  | @node l r x p ds π h1 h2 h3 h4 h5 h6 h7 ih5 ih6 ih7 =>
    intro hnd p' hin hrt hp
    simp only [nodes_node] at hnd
    have hnd' := hnd
    rw [List.nodup_append, List.nodup_append, List.nodup_cons] at hnd'
    obtain ⟨⟨hl, ⟨hxr, hr⟩, hlr⟩, hds, hrest⟩ := hnd'
    have hx := hrt (by simp)
    simp only [rt_node] at hx
    have hσ : cσ B M' π x = cσ B M π x := by simp only [cσ, hx.rvEq B]
    have sub : ∀ (s : VT), (s = l ∨ s = r ∨ s ∈ ds) → ∀ u ∈ nodes s,
        u ∈ nodes (VT.node l x r ds) ∧ u ≠ x := by
      rintro s hs u hu
      rcases hs with rfl | rfl | hs
      · exact ⟨by simp [hu], fun e => hlr u hu x (by simp) e⟩
      · exact ⟨by simp [hu], fun e => hxr (e ▸ hu)⟩
      · have hu' := mem_nodesL_of hs hu
        exact ⟨by simp [hu'], fun e => hrest x (by simp) u hu' e.symm⟩
    have agrS : ∀ (s : VT), (s = l ∨ s = r ∨ s ∈ ds) → ∀ u ∈ nodes s, Agr B M M' u :=
      fun s hs u hu => hin u (sub s hs u hu).1 (by simpa using (sub s hs u hu).2)
    have child : ∀ (s : VT) (σ : Bool), (s = l ∨ s = r ∨ s ∈ ds) → Enc B n M s x σ →
        (nodes s).Nodup →
        ((nodes s).Nodup → ∀ p', (∀ u ∈ nodes s, u ≠ rt n s → Agr B M M' u) →
          (s ≠ VT.leaf → AgrC B M M' (rt n s)) → (s ≠ VT.leaf → par B M' (rt n s) = p') →
          Enc B n M' s p' σ) → Enc B n M' s x σ := fun s σ hs hse hnds ih =>
      ih hnds x (fun u hu _ => agrS s hs u hu)
        (fun hne => (agrS s hs (rt n s) (rt_mem_nodes hne n)).agrC)
        (fun hne => by
          rw [show par B M' (rt n s) = par B M (rt n s) from
            ((agrS s hs (rt n s) (rt_mem_nodes hne n)) 0 (by omega)).1]
          exact hse.par_rt B n hne)
    have lookc : ∀ (s : VT), (s = l ∨ s = r ∨ s ∈ ds) →
        Look B n M M' (rt n s) (rt n s) := fun s hs => by
      cases s with
      | leaf => exact look_nil B n hN hN'
      | node a y b dy => exact look_of_agr B n (agrS _ hs y (by simp))
    have elc : lc B M' x = lc B M x := (hx 1 (by omega)).1 (by omega)
    have erc : rc B M' x = rc B M x := (hx 2 (by omega)).1 (by omega)
    have hS : ∀ σ, lcS B M' σ x = lcS B M σ x := by intro σ; simp only [lcS, elc, erc]
    refine .node (hp (by simp)) ?_ ?_ ?_ ?_ ?_
      (fun d hd => child d false (Or.inr (Or.inr hd)) (h7 d hd) (nodup_of_mem_nodesL hds hd)
        (ih7 d hd))
    · rw [hσ, hS]; exact h2
    · rw [hσ, hS]; exact h3
    · refine h4.of_agrC B n hx ?_ ?_
      · cases e : cσ B M π x
        · have : lc B M x = rt n l := by simpa [lcS, e] using h2
          rw [this]; exact lookc l (Or.inl rfl)
        · have : lc B M x = rt n r := by simpa [lcS, e] using h3
          rw [this]; exact lookc r (Or.inr (Or.inl rfl))
      · cases e : cσ B M π x
        · have : rc B M x = rt n r := by simpa [lcS, e] using h3
          rw [this]; exact lookc r (Or.inr (Or.inl rfl))
        · have : rc B M x = rt n l := by simpa [lcS, e] using h2
          rw [this]; exact lookc l (Or.inl rfl)
    · rw [hσ]; exact child l _ (Or.inl rfl) h5 hl ih5
    · rw [hσ]; exact child r _ (Or.inr (Or.inl rfl)) h6 hr ih6

/-! ### The aggregates -/

/-- The combination at a node of parity `π`, in the true order. -/
lemma own_mirIf {M : Mem} {x : ℕ} {l r : VT} {π : Bool} (hA : AggOK B n M x)
    (hl : lcS B M (cσ B M π x) x = rt n l) (hr : lcS B M (!cσ B M π x) x = rt n r) :
    mirIf π (own B M x) = comb n (rt n l) (mirIf (cσ B M π x) (rd B M (rt n l))) x
      (vlc B M π x) (vlc B M (!π) x) (rt n r) (mirIf (cσ B M π x) (rd B M (rt n r))) := by
  rw [aggOK_iff] at hA
  rw [hA, ← mirIf_xor]
  generalize hR : rv B M x = R at hl hr
  simp only [cσ, hR] at hl hr ⊢
  cases π <;> cases R <;> simp [lcS] at hl hr ⊢ <;>
    simp only [mir_comb, hl, hr]

/-- **The aggregates are correct.** What the parent reads of the root of a tree stored with
parity `π` is, up to the mirror image, the count, sums, minima, argmins and end nodes of the true
values along its path. -/
theorem Enc.agg {M : Mem} (hN : NilOK B n M) {t : VT} {p : ℕ} {π : Bool}
    (h : Enc B n M t p π) (hlt : ∀ u ∈ nodes t, u < n) :
    ChildOK n (rt n t) (mirIf π (rd B M (rt n t))) (tAg n (rs B M t π false) (rs B M t π true)
      (seq t)) := by
  induction h with
  | leaf p π =>
    refine ⟨?_, fun h => absurd h (lt_irrefl n)⟩
    cases π <;> simp [rd, own, addTags, tAg, mir, hN.cnt, hN.sm, hN.sm2]
  | @node l r x p ds π h1 h2 h3 h4 h5 h6 h7 ih5 ih6 _ =>
    have il := ih5 (fun u hu => hlt u (by simp [hu]))
    have ir := ih6 (fun u hu => hlt u (by simp [hu]))
    have hx : x < n := hlt x (by simp)
    have key := own_mirIf B n h4 h2 h3
    have e : mirIf π (rd B M x) = addTags (tgc B M π x) (tgc B M (!π) x) (mirIf π (own B M x)) := by
      simp only [rd]; rw [mirIf_addTags]; cases π <;> rfl
    have hrl : ∀ s : VT, (∀ u ∈ nodes s, u < n) → (rt n s < n ↔ seq s ≠ []) := by
      intro s hs; cases s with
      | leaf => simp
      | node a y b dy => simp [hs y (by simp)]
    refine ⟨?_, fun _ => ?_⟩ <;>
    · simp only [rt_node]
      rw [e, key, comb_congr n Iff.rfl il Iff.rfl ir, rs_node, rs_node]
      simp only [Bool.false_xor, Bool.true_xor]
      rw [seq_node, tAg_join (vlc B M π x) (vlc B M (!π) x) (tgc B M π x) (tgc B M (!π) x)
        (rs_fst M l _ _) (rs_fst M l _ _) (rs_fst M r _ _) (rs_fst M r _ _)
        (hrl l (fun u hu => hlt u (by simp [hu]))) (hrl r (fun u hu => hlt u (by simp [hu])))]
      try exact ⟨rfl, rfl, rfl⟩

/-! ### Zippers -/

@[simp] lemma rt_plugF (f : Frame) (t : VT) : rt n (f.plug t) = f.y := by
  cases f <;> rfl

lemma enc_plugF {M : Mem} (f : Frame) (t : VT) (q : ℕ) (π : Bool) :
    Enc B n M (f.plug t) q π ↔ Enc B n M t f.y (hpar B M f π) ∧ EncF B n M f (rt n t) π ∧
      par B M f.y = q := by
  cases f with
  | L y c dy => simp only [Frame.plug, enc_node_iff, EncF, Frame.y, hpar]; tauto
  | R c y dy => simp only [Frame.plug, enc_node_iff, EncF, Frame.y, hpar]; tauto
  | D l y r bef aft =>
    simp only [Frame.plug, enc_node_iff, EncF, Frame.y, hpar, List.forall_mem_append,
      List.forall_mem_cons]
    tauto

lemma enc_plugZ {M : Mem} (t : VT) (ctx : List Frame) (p : ℕ) :
    Enc B n M (plug t ctx) p false ↔ Enc B n M t (hp p ctx) (cpar B M ctx) ∧
      EncC B n M ctx (rt n t) p := by
  induction ctx generalizing t with
  | nil => simp [hp, EncC, cpar]
  | cons f fs ih =>
    rw [plug_cons, ih, enc_plugF, rt_plugF]
    simp only [hp, EncC, cpar]
    tauto

/-! ### Values -/

/-- `M'` agrees with `M` on the values, the tags and the reversal bit of `u`. -/
def AgrV (M M' : Mem) (u : ℕ) : Prop :=
  vl B M' u = vl B M u ∧ tg B M' u = tg B M u ∧ vl2 B M' u = vl2 B M u ∧
    tg2 B M' u = tg2 B M u ∧ rv B M' u = rv B M u

lemma AgrV.vlc {M M' : Mem} {u : ℕ} (h : AgrV B M M' u) (k : Bool) :
    vlc B M' k u = vlc B M k u := by cases k <;> simp [DynTree.vlc, h.1, h.2.2.1]

lemma AgrV.tgc {M M' : Mem} {u : ℕ} (h : AgrV B M M' u) (k : Bool) :
    tgc B M' k u = tgc B M k u := by cases k <;> simp [DynTree.tgc, h.2.1, h.2.2.2.1]

lemma rs_frame {M M' : Mem} : ∀ (t : VT), (∀ u ∈ nodes t, AgrV B M M' u) →
    ∀ π k, rs B M' t π k = rs B M t π k
  | VT.leaf, _, _, _ => rfl
  | VT.node l x r ds, h, π, k => by
    have hx := h x (by simp)
    simp only [rs_node, cσ, hx.2.2.2.2, hx.vlc, hx.tgc]
    rw [rs_frame l (fun u hu => h u (by simp [hu])), rs_frame r (fun u hu => h u (by simp [hu]))]

mutual
lemma dV_frame {M M' : Mem} : ∀ (t : VT), (∀ u ∈ nodes t, AgrV B M M' u) →
    ∀ k, dV B M' t k = dV B M t k
  | VT.leaf, _, _ => rfl
  | VT.node l x r ds, h, k => by
    simp only [dV_node]
    rw [dV_frame l (fun u hu => h u (by simp [hu])), dV_frame r (fun u hu => h u (by simp [hu])),
      dVL_frame ds (fun u hu => h u (by simp [hu]))]
lemma dVL_frame {M M' : Mem} : ∀ (ts : List VT), (∀ u ∈ nodesL ts, AgrV B M M' u) →
    ∀ k, dVL B M' ts k = dVL B M ts k
  | [], _, _ => rfl
  | t :: ts, h, k => by
    simp only [dVL_cons]
    rw [rs_frame B t (fun u hu => h u (by simp [hu])), dV_frame t (fun u hu => h u (by simp [hu])),
      dVL_frame ts (fun u hu => h u (by simp [hu]))]
end

/-- The values of the mirror image: reversed, the two channels exchanged. -/
lemma rs_mirT (M : Mem) : ∀ (t : VT) (π k : Bool),
    rs B M (mirT t) π k = (rs B M t (!π) (!k)).reverse
  | VT.leaf, _, _ => rfl
  | VT.node l x r ds, π, k => by
    have e1 : (k ^^ π) = (!k ^^ !π) := by cases k <;> cases π <;> rfl
    have e2 : cσ B M π x = !cσ B M (!π) x := by simp [cσ]
    simp only [mirT_node, rs_node, rs_mirT M l, rs_mirT M r, reverse_shift, List.reverse_append,
      List.reverse_cons, List.append_assoc, List.singleton_append, e1, e2, Bool.not_not]

end agree

end DynTree

end PlanarFlow
