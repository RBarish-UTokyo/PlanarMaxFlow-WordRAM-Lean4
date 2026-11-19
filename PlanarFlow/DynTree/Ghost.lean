module

public import PlanarFlow.DynTree.Forest

/-!
# Dynamic trees: virtual trees, zippers and the rank potential

The link-cut tree of Sleator and Tarjan splits each tree of the forest into vertex-disjoint
*preferred paths*; each path is kept as a splay tree (its *auxiliary tree*) whose in-order is the
path from top to bottom, and the root of each auxiliary tree points to the parent of the top of
its path (the *path-parent*). The auxiliary trees with these pointers form the *virtual tree*.

`VT` is a virtual tree: a binary node `node l x r ds` has the auxiliary subtrees `l`, `r` and the
list `ds` of virtual trees hanging from `x` by path-parent pointers. It is ghost data: the
machine only stores the pointers, and `PlanarFlow.DynTree.Enc` relates the two.

* `seq t`: the in-order of the auxiliary tree of `t` (the path it represents);
* `edges p t`: the forest edges `(child, parent)` that `t` represents when the top of its path has
  parent `p`;
* `size t`: the number of nodes of `t` (with the hanging trees); `pot t = ∑ ⌊log₂ size⌋` over the
  nodes, the integer rank potential;
* zippers: `Frame`, `plug`; a rotation `rotUp` and the splay steps (zig, zig-zig, zig-zag).

**Integer access lemma.** With ranks `⌊log₂ s⌋`, a zig-zig or zig-zag step at `x` satisfies
`Φ' + 3 r(x) + 1 ≤ Φ + 3 r'(x)` (`pot_zigzig`, `pot_zigzag`) and a zig step `Φ' + r(x) ≤ Φ + r'(x)`
(`pot_zig`); the only fact about logarithms used is `log₂_add`: if `a + b ≤ c` then
`⌊log₂ a⌋ + ⌊log₂ b⌋ + 1 ≤ 2⌊log₂ c⌋`. This is the rank argument of D. D. Sleator and R. E. Tarjan,
*Self-adjusting binary search trees*, J. ACM 32 (1985), 652–686, in its integer form.
-/

@[expose] public section

namespace PlanarFlow

namespace DynTree

/-- A virtual tree: an auxiliary binary tree whose nodes carry lists of hanging virtual trees. -/
inductive VT where
  | leaf : VT
  | node (l : VT) (x : ℕ) (r : VT) (ds : List VT) : VT

namespace VT

/-- The label of the root, `n` (nil) for a leaf. -/
def rt (n : ℕ) : VT → ℕ
  | leaf => n
  | node _ x _ _ => x

/-- The in-order of the auxiliary tree. -/
def seq : VT → List ℕ
  | leaf => []
  | node l x r _ => seq l ++ x :: seq r

mutual
/-- The number of nodes. -/
def size : VT → ℕ
  | leaf => 0
  | node l _ r ds => size l + size r + 1 + sizeL ds
/-- The number of nodes of a list of virtual trees. -/
def sizeL : List VT → ℕ
  | [] => 0
  | t :: ts => size t + sizeL ts
end

mutual
/-- The rank potential: `∑ ⌊log₂ size⌋` over the nodes. -/
def pot : VT → ℕ
  | leaf => 0
  | node l x r ds => pot l + pot r + potL ds + Nat.log 2 (size (node l x r ds))
/-- The rank potential of a list of virtual trees. -/
def potL : List VT → ℕ
  | [] => 0
  | t :: ts => pot t + potL ts
end

mutual
/-- All labels. -/
def nodes : VT → List ℕ
  | leaf => []
  | node l x r ds => nodes l ++ x :: nodes r ++ nodesL ds
/-- All labels of a list of virtual trees. -/
def nodesL : List VT → List ℕ
  | [] => []
  | t :: ts => nodes t ++ nodesL ts
end

/-- The edges `(child, parent)` along a path `xs` whose first node has parent `p`. -/
def chain : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | p, x :: xs => (x, p) :: chain x xs

mutual
/-- The edges represented by the hanging trees. -/
def dE : VT → List (ℕ × ℕ)
  | leaf => []
  | node l x r ds => dE l ++ dE r ++ dEL x ds
/-- The edges represented by a list of trees hanging from `y`. -/
def dEL (y : ℕ) : List VT → List (ℕ × ℕ)
  | [] => []
  | d :: ds => chain y (seq d) ++ dE d ++ dEL y ds
end

/-- The edges represented by `t` when the top of its path has parent `p`. -/
def edges (p : ℕ) (t : VT) : List (ℕ × ℕ) := chain p (seq t) ++ dE t

@[simp] lemma size_leaf : size leaf = 0 := rfl
@[simp] lemma size_node (l r : VT) (x : ℕ) (ds : List VT) :
    size (node l x r ds) = size l + size r + 1 + sizeL ds := rfl
@[simp] lemma sizeL_nil : sizeL [] = 0 := rfl
@[simp] lemma sizeL_cons (t : VT) (ts : List VT) : sizeL (t :: ts) = size t + sizeL ts := rfl
@[simp] lemma pot_leaf : pot leaf = 0 := rfl
lemma pot_node (l r : VT) (x : ℕ) (ds : List VT) :
    pot (node l x r ds) = pot l + pot r + potL ds + Nat.log 2 (size l + size r + 1 + sizeL ds) :=
  rfl
lemma pot_node' (l r : VT) (x : ℕ) (ds : List VT) :
    pot (node l x r ds) = pot l + pot r + potL ds + Nat.log 2 (size (node l x r ds)) := rfl
@[simp] lemma potL_nil : potL [] = 0 := rfl
@[simp] lemma potL_cons (t : VT) (ts : List VT) : potL (t :: ts) = pot t + potL ts := rfl
@[simp] lemma nodes_leaf : nodes leaf = [] := rfl
@[simp] lemma nodes_node (l r : VT) (x : ℕ) (ds : List VT) :
    nodes (node l x r ds) = nodes l ++ x :: nodes r ++ nodesL ds := rfl
@[simp] lemma nodesL_nil : nodesL [] = [] := rfl
@[simp] lemma nodesL_cons (t : VT) (ts : List VT) : nodesL (t :: ts) = nodes t ++ nodesL ts := rfl
@[simp] lemma seq_leaf : seq leaf = [] := rfl
@[simp] lemma seq_node (l r : VT) (x : ℕ) (ds : List VT) :
    seq (node l x r ds) = seq l ++ x :: seq r := rfl
@[simp] lemma rt_leaf (n : ℕ) : rt n leaf = n := rfl
@[simp] lemma rt_node (n : ℕ) (l r : VT) (x : ℕ) (ds : List VT) : rt n (node l x r ds) = x := rfl
@[simp] lemma dE_leaf : dE leaf = [] := rfl
@[simp] lemma dE_node (l r : VT) (x : ℕ) (ds : List VT) :
    dE (node l x r ds) = dE l ++ dE r ++ dEL x ds := rfl
@[simp] lemma dEL_nil (y : ℕ) : dEL y [] = [] := rfl
@[simp] lemma dEL_cons (y : ℕ) (d : VT) (ds : List VT) :
    dEL y (d :: ds) = chain y (seq d) ++ dE d ++ dEL y ds := rfl
@[simp] lemma chain_nil (p : ℕ) : chain p [] = [] := rfl
@[simp] lemma chain_cons (p x : ℕ) (xs : List ℕ) : chain p (x :: xs) = (x, p) :: chain x xs := rfl

@[simp] lemma sizeL_append (a b : List VT) : sizeL (a ++ b) = sizeL a + sizeL b := by
  induction a with
  | nil => simp
  | cons t a ih => simp [ih]; omega

@[simp] lemma potL_append (a b : List VT) : potL (a ++ b) = potL a + potL b := by
  induction a with
  | nil => simp
  | cons t a ih => simp [ih]; omega

@[simp] lemma nodesL_append (a b : List VT) : nodesL (a ++ b) = nodesL a ++ nodesL b := by
  induction a with
  | nil => simp
  | cons t a ih => simp [ih]

@[simp] lemma dEL_append (y : ℕ) (a b : List VT) : dEL y (a ++ b) = dEL y a ++ dEL y b := by
  induction a with
  | nil => simp
  | cons t a ih => simp [ih]

lemma chain_append (p : ℕ) (xs ys : List ℕ) :
    chain p (xs ++ ys) = chain p xs ++ chain (xs.getLastD p) ys := by
  induction xs generalizing p with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, chain_cons, ih, List.getLastD_cons]

lemma size_eq_length : ∀ t : VT, size t = (nodes t).length
  | leaf => rfl
  | node l x r ds => by
    simp only [size_node, nodes_node, List.length_append, List.length_cons, size_eq_length l,
      size_eq_length r, sizeL_eq_length ds]
    omega
where sizeL_eq_length : ∀ ts : List VT, sizeL ts = (nodesL ts).length
  | [] => rfl
  | t :: ts => by simp [size_eq_length t, sizeL_eq_length ts]

lemma size_pos_of_ne_leaf {t : VT} (h : t ≠ leaf) : 1 ≤ size t := by
  cases t with
  | leaf => exact absurd rfl h
  | node l x r ds => simp only [size_node]; omega

lemma seq_eq_nil {t : VT} : seq t = [] ↔ t = leaf := by
  cases t <;> simp

/-! ### Logarithms -/

/-- The integer form of the concavity of the logarithm used in the access lemma. -/
lemma log2_add {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a + b ≤ c) :
    Nat.log 2 a + Nat.log 2 b + 1 ≤ 2 * Nat.log 2 c := by
  have hac : Nat.log 2 a ≤ Nat.log 2 c := Nat.log_mono_right (by omega)
  have hbc : Nat.log 2 b ≤ Nat.log 2 c := Nat.log_mono_right (by omega)
  by_contra hcon
  have e1 : Nat.log 2 a = Nat.log 2 c := by omega
  have e2 : Nat.log 2 b = Nat.log 2 c := by omega
  have p1 : 2 ^ Nat.log 2 a ≤ a := Nat.pow_log_le_self 2 (by omega)
  have p2 : 2 ^ Nat.log 2 b ≤ b := Nat.pow_log_le_self 2 (by omega)
  have p3 : c < 2 ^ (Nat.log 2 c + 1) := Nat.lt_pow_succ_log_self (by norm_num) c
  rw [e1] at p1; rw [e2] at p2; rw [pow_succ] at p3
  omega

lemma log_mono {a b : ℕ} (h : a ≤ b) : Nat.log 2 a ≤ Nat.log 2 b := Nat.log_mono_right h

/-! ### Zippers -/

/-- A frame of a zipper: the hole is the left child of `y` (`L`), its right child (`R`), or one
of the trees hanging from `y` (`D`, between `bef` and `aft`). -/
inductive Frame where
  | L (y : ℕ) (r : VT) (ds : List VT)
  | R (l : VT) (y : ℕ) (ds : List VT)
  | D (l : VT) (y : ℕ) (r : VT) (bef aft : List VT)

namespace Frame

/-- Fill the hole. -/
def plug : Frame → VT → VT
  | L y r ds, t => node t y r ds
  | R l y ds, t => node l y t ds
  | D l y r bef aft, t => node l y r (bef ++ t :: aft)

/-- The node of the frame. -/
def y : Frame → ℕ
  | L y _ _ => y
  | R _ y _ => y
  | D _ y _ _ _ => y

/-- The hole is a child in the auxiliary tree. -/
def Solid : Frame → Prop
  | D _ _ _ _ _ => False
  | _ => True

/-- The hole is a left child. -/
def IsL : Frame → Prop
  | L _ _ _ => True
  | _ => False

/-- The number of nodes outside the hole. -/
def fsize : Frame → ℕ
  | L _ r ds => size r + 1 + sizeL ds
  | R l _ ds => size l + 1 + sizeL ds
  | D l _ r bef aft => size l + size r + 1 + sizeL bef + sizeL aft

/-- The potential outside the hole, except at `y`. -/
def fpot : Frame → ℕ
  | L _ r ds => pot r + potL ds
  | R l _ ds => pot l + potL ds
  | D l _ r bef aft => pot l + pot r + potL bef + potL aft

/-- The labels outside the hole. -/
def fnodes : Frame → List ℕ
  | L y r ds => y :: nodes r ++ nodesL ds
  | R l y ds => y :: nodes l ++ nodesL ds
  | D l y r bef aft => y :: nodes l ++ nodes r ++ nodesL bef ++ nodesL aft

lemma size_plug (f : Frame) (t : VT) : size (f.plug t) = size t + f.fsize := by
  cases f <;> simp [plug, fsize] <;> omega

lemma pot_plug (f : Frame) (t : VT) :
    pot (f.plug t) = pot t + f.fpot + Nat.log 2 (size t + f.fsize) := by
  rw [← size_plug]
  cases f <;> simp only [plug, pot_node', fpot, potL_append, potL_cons] <;> ring

lemma nodes_plug (f : Frame) (t : VT) : (nodes (f.plug t)).Perm (nodes t ++ f.fnodes) := by
  rw [List.perm_iff_count]; intro a
  cases f <;> simp [plug, fnodes, List.count_append, List.count_cons] <;> omega

end Frame

open Frame

/-- Plug a tree into a zipper (innermost frame first). -/
def plug : VT → List Frame → VT
  | t, [] => t
  | t, f :: fs => plug (f.plug t) fs

/-- The number of nodes of a zipper. -/
def csize : List Frame → ℕ
  | [] => 0
  | f :: fs => f.fsize + csize fs

/-- The potential of a zipper whose hole holds `s` nodes. -/
def cpot : List Frame → ℕ → ℕ
  | [], _ => 0
  | f :: fs, s => f.fpot + Nat.log 2 (s + f.fsize) + cpot fs (s + f.fsize)

/-- The labels of a zipper. -/
def cnodes : List Frame → List ℕ
  | [] => []
  | f :: fs => f.fnodes ++ cnodes fs

@[simp] lemma plug_nil (t : VT) : plug t [] = t := rfl
@[simp] lemma plug_cons (t : VT) (f : Frame) (fs : List Frame) :
    plug t (f :: fs) = plug (f.plug t) fs := rfl

lemma size_plugZ (t : VT) (ctx : List Frame) : size (plug t ctx) = size t + csize ctx := by
  induction ctx generalizing t with
  | nil => simp [csize]
  | cons f fs ih => simp only [plug_cons, ih, size_plug, csize]; omega

lemma pot_plugZ (t : VT) (ctx : List Frame) : pot (plug t ctx) = pot t + cpot ctx (size t) := by
  induction ctx generalizing t with
  | nil => simp [cpot]
  | cons f fs ih => simp only [plug_cons, ih, pot_plug, size_plug, cpot]; omega

lemma nodes_plugZ (t : VT) (ctx : List Frame) :
    (nodes (plug t ctx)).Perm (nodes t ++ cnodes ctx) := by
  induction ctx generalizing t with
  | nil => simp [cnodes]
  | cons f fs ih =>
    simp only [plug_cons, cnodes]
    refine (ih _).trans ?_
    rw [← List.append_assoc]
    exact (nodes_plug f t).append_right _

/-! ### Rotations and splay steps -/

/-- Rotate the root of `t` above the node of the frame `f` (a zig). -/
def rotUp : VT → Frame → VT
  | node a x b dx, .L y c dy => node a x (node b y c dy) dx
  | node a x b dx, .R c y dy => node (node c y a dy) x b dx
  | t, f => f.plug t

/-- The frame of `x` after the rotation of its parent `y` above its grandparent `z`, in a
zig-zig step. -/
def zz : Frame → Frame → Frame
  | .L y c dy, .L z d dz => .L y (node c z d dz) dy
  | .R c y dy, .R d z dz => .R (node d z c dz) y dy
  | f, _ => f

/-- Two solid frames on the same side. -/
def SameSide (f₁ f₂ : Frame) : Prop := f₁.Solid ∧ f₂.Solid ∧ (f₁.IsL ↔ f₂.IsL)

/-- Two solid frames on opposite sides. -/
def OppSide (f₁ f₂ : Frame) : Prop := f₁.Solid ∧ f₂.Solid ∧ ¬ (f₁.IsL ↔ f₂.IsL)

lemma rotUp_plug_zz {f₁ f₂ : Frame} (h : SameSide f₁ f₂) (t : VT) :
    rotUp (f₁.plug t) f₂ = (zz f₁ f₂).plug t := by
  obtain ⟨h1, h2, h3⟩ := h
  cases f₁ <;> cases f₂ <;> simp_all [Solid, IsL, rotUp, zz, Frame.plug]

lemma zz_solid {f₁ f₂ : Frame} (h : SameSide f₁ f₂) : (zz f₁ f₂).Solid := by
  obtain ⟨h1, h2, h3⟩ := h
  cases f₁ <;> cases f₂ <;> simp_all [Solid, IsL, zz]

lemma zz_y {f₁ f₂ : Frame} (h : SameSide f₁ f₂) : (zz f₁ f₂).y = f₁.y := by
  obtain ⟨h1, h2, h3⟩ := h
  cases f₁ <;> cases f₂ <;> simp_all [Solid, IsL, zz, Frame.y]

lemma size_rotUp (t : VT) (f : Frame) : size (rotUp t f) = size (f.plug t) := by
  cases t with
  | leaf => rfl
  | node a x b dx => cases f <;> simp [rotUp, Frame.plug] <;> omega

lemma seq_rotUp {t : VT} {f : Frame} (hf : f.Solid) : seq (rotUp t f) = seq (f.plug t) := by
  cases t with
  | leaf => rfl
  | node a x b dx => cases f <;> simp_all [rotUp, Frame.plug, Solid]

lemma nodes_rotUp (t : VT) (f : Frame) : (nodes (rotUp t f)).Perm (nodes (f.plug t)) := by
  cases t with
  | leaf => exact List.Perm.refl _
  | node a x b dx =>
    rw [List.perm_iff_count]; intro e
    cases f <;> simp [rotUp, Frame.plug, List.count_append, List.count_cons] <;> omega

lemma dE_rotUp (t : VT) (f : Frame) (e : ℕ × ℕ) : e ∈ dE (rotUp t f) ↔ e ∈ dE (f.plug t) := by
  cases t with
  | leaf => exact Iff.rfl
  | node a x b dx => cases f <;> simp [rotUp, Frame.plug] <;> tauto

lemma rt_rotUp {t : VT} (ht : t ≠ leaf) {f : Frame} (hf : f.Solid) (n : ℕ) :
    rt n (rotUp t f) = rt n t := by
  cases t with
  | leaf => exact absurd rfl ht
  | node a x b dx => cases f <;> simp_all [rotUp, Solid]

/-- The integer rank bound of a zig. -/
lemma pot_zig {t : VT} (ht : t ≠ leaf) {f : Frame} (hf : f.Solid) :
    pot (rotUp t f) + Nat.log 2 (size t) ≤ pot (f.plug t) + Nat.log 2 (size (f.plug t)) := by
  obtain ⟨a, x, b, dx, rfl⟩ : ∃ a x b dx, t = node a x b dx := by
    cases t with
    | leaf => exact absurd rfl ht
    | node a x b dx => exact ⟨a, x, b, dx, rfl⟩
  cases f with
  | L y c dy =>
    simp only [rotUp, Frame.plug, pot_node, size_node]
    generalize size a = A, size b = Bs, size c = C, sizeL dx = X, sizeL dy = Y
    have := log_mono (show Bs + C + 1 + Y ≤ A + Bs + 1 + X + C + 1 + Y by omega)
    rw [show A + (Bs + C + 1 + Y) + 1 + X = A + Bs + 1 + X + C + 1 + Y by omega]
    omega
  | R c y dy =>
    simp only [rotUp, Frame.plug, pot_node, size_node]
    generalize size a = A, size b = Bs, size c = C, sizeL dx = X, sizeL dy = Y
    have := log_mono (show C + A + 1 + Y ≤ C + (A + Bs + 1 + X) + 1 + Y by omega)
    rw [show C + A + 1 + Y + Bs + 1 + X = C + (A + Bs + 1 + X) + 1 + Y by omega]
    omega
  | D l y r bef aft => simp [Solid] at hf

/-- The integer rank bound of a zig-zig. -/
lemma pot_zigzig {t : VT} (ht : t ≠ leaf) {f₁ f₂ : Frame} (h : SameSide f₁ f₂) :
    pot (rotUp t (zz f₁ f₂)) + 3 * Nat.log 2 (size t) + 1 ≤
      pot (f₂.plug (f₁.plug t)) + 3 * Nat.log 2 (size (f₂.plug (f₁.plug t))) := by
  obtain ⟨a, x, b, dx, rfl⟩ : ∃ a x b dx, t = node a x b dx := by
    cases t with
    | leaf => exact absurd rfl ht
    | node a x b dx => exact ⟨a, x, b, dx, rfl⟩
  obtain ⟨h1, h2, h3⟩ := h
  cases f₁ <;> cases f₂ <;> simp [Solid, IsL] at h1 h2 h3
  · rename_i y c dy z d dz
    simp only [zz, rotUp, Frame.plug, pot_node, size_node]
    generalize size a = A, size b = Bs, size c = C, size d = D', sizeL dx = X, sizeL dy = Y,
      sizeL dz = Z
    have k := log2_add (a := A + Bs + 1 + X) (b := C + D' + 1 + Z)
      (c := A + Bs + 1 + X + C + 1 + Y + D' + 1 + Z) (by omega) (by omega) (by omega)
    have := log_mono (show Bs + (C + D' + 1 + Z) + 1 + Y ≤
      A + Bs + 1 + X + C + 1 + Y + D' + 1 + Z by omega)
    have := log_mono (show A + Bs + 1 + X ≤ A + Bs + 1 + X + C + 1 + Y by omega)
    have e : A + (Bs + (C + D' + 1 + Z) + 1 + Y) + 1 + X =
      A + Bs + 1 + X + C + 1 + Y + D' + 1 + Z := by omega
    rw [e]
    omega
  · rename_i c y dy d z dz
    simp only [zz, rotUp, Frame.plug, pot_node, size_node]
    generalize size a = A, size b = Bs, size c = C, size d = D', sizeL dx = X, sizeL dy = Y,
      sizeL dz = Z
    have k := log2_add (a := A + Bs + 1 + X) (b := D' + C + 1 + Z)
      (c := D' + (C + (A + Bs + 1 + X) + 1 + Y) + 1 + Z) (by omega) (by omega) (by omega)
    have := log_mono (show D' + C + 1 + Z + A + 1 + Y ≤
      D' + (C + (A + Bs + 1 + X) + 1 + Y) + 1 + Z by omega)
    have := log_mono (show A + Bs + 1 + X ≤ C + (A + Bs + 1 + X) + 1 + Y by omega)
    have e : D' + C + 1 + Z + A + 1 + Y + Bs + 1 + X =
      D' + (C + (A + Bs + 1 + X) + 1 + Y) + 1 + Z := by omega
    have e2 : D' + C + 1 + Z + A + 1 + Y = D' + C + 1 + Z + A + 1 + Y := rfl
    rw [e]
    omega

/-- The integer rank bound of a zig-zag. -/
lemma pot_zigzag {t : VT} (ht : t ≠ leaf) {f₁ f₂ : Frame} (h : OppSide f₁ f₂) :
    pot (rotUp (rotUp t f₁) f₂) + 3 * Nat.log 2 (size t) + 1 ≤
      pot (f₂.plug (f₁.plug t)) + 3 * Nat.log 2 (size (f₂.plug (f₁.plug t))) := by
  obtain ⟨a, x, b, dx, rfl⟩ : ∃ a x b dx, t = node a x b dx := by
    cases t with
    | leaf => exact absurd rfl ht
    | node a x b dx => exact ⟨a, x, b, dx, rfl⟩
  obtain ⟨h1, h2, h3⟩ := h
  cases f₁ <;> cases f₂ <;> simp [Solid, IsL] at h1 h2 h3
  · rename_i y c dy d z dz
    simp only [rotUp, Frame.plug, pot_node, size_node]
    generalize size a = A, size b = Bs, size c = C, size d = D', sizeL dx = X, sizeL dy = Y,
      sizeL dz = Z
    have k := log2_add (a := D' + A + 1 + Z) (b := Bs + C + 1 + Y)
      (c := D' + (A + Bs + 1 + X + C + 1 + Y) + 1 + Z) (by omega) (by omega) (by omega)
    have := log_mono (show A + Bs + 1 + X ≤ A + Bs + 1 + X + C + 1 + Y by omega)
    have := log_mono (show A + Bs + 1 + X + C + 1 + Y ≤ D' + (A + Bs + 1 + X + C + 1 + Y) + 1 + Z
      by omega)
    have e : D' + A + 1 + Z + (Bs + C + 1 + Y) + 1 + X =
      D' + (A + Bs + 1 + X + C + 1 + Y) + 1 + Z := by omega
    rw [e]
    omega
  · rename_i c y dy z d dz
    simp only [rotUp, Frame.plug, pot_node, size_node]
    generalize size a = A, size b = Bs, size c = C, size d = D', sizeL dx = X, sizeL dy = Y,
      sizeL dz = Z
    have k := log2_add (a := C + A + 1 + Y) (b := Bs + D' + 1 + Z)
      (c := C + (A + Bs + 1 + X) + 1 + Y + D' + 1 + Z) (by omega) (by omega) (by omega)
    have := log_mono (show A + Bs + 1 + X ≤ C + (A + Bs + 1 + X) + 1 + Y by omega)
    have := log_mono (show C + (A + Bs + 1 + X) + 1 + Y ≤ C + (A + Bs + 1 + X) + 1 + Y + D' + 1 + Z
      by omega)
    have e : C + A + 1 + Y + (Bs + D' + 1 + Z) + 1 + X =
      C + (A + Bs + 1 + X) + 1 + Y + D' + 1 + Z := by omega
    rw [e]
    omega

/-! ### Trees representing the same paths -/

/-- `t` and `t'` represent the same path with the same hanging trees. -/
structure Same (t t' : VT) : Prop where
  seq : seq t = seq t'
  dE : ∀ e, e ∈ dE t ↔ e ∈ dE t'
  nodes : (nodes t).Perm (nodes t')
  size : size t = size t'

lemma Same.refl (t : VT) : Same t t := ⟨rfl, fun _ => Iff.rfl, List.Perm.refl _, rfl⟩

lemma Same.symm {t t' : VT} (h : Same t t') : Same t' t :=
  ⟨h.seq.symm, fun e => (h.dE e).symm, h.nodes.symm, h.size.symm⟩

lemma Same.plugF {t t' : VT} (h : Same t t') (f : Frame) : Same (f.plug t) (f.plug t') := by
  refine ⟨?_, fun e => ?_, ?_, by rw [size_plug, size_plug, h.size]⟩
  · cases f <;> simp [Frame.plug, h.seq]
  · cases f <;> simp [Frame.plug, h.seq, h.dE e]
  · exact (nodes_plug f t).trans (((h.nodes).append_right _).trans (nodes_plug f t').symm)

lemma Same.plugZ {t t' : VT} (h : Same t t') (ctx : List Frame) :
    Same (VT.plug t ctx) (VT.plug t' ctx) := by
  induction ctx generalizing t t' with
  | nil => exact h
  | cons f fs ih => exact ih (h.plugF f)

lemma same_rotUp {t : VT} {f : Frame} (hf : f.Solid) :
    Same (rotUp t f) (f.plug t) :=
  ⟨seq_rotUp hf, dE_rotUp t f, nodes_rotUp t f, size_rotUp t f⟩


/-! ### Mirror images -/

/-- The mirror image of the auxiliary tree (the hanging trees are kept): its in-order is
reversed. -/
def mirT : VT → VT
  | leaf => leaf
  | node l x r ds => node (mirT r) x (mirT l) ds

@[simp] lemma mirT_leaf : mirT leaf = leaf := rfl
@[simp] lemma mirT_node (l r : VT) (x : ℕ) (ds : List VT) :
    mirT (node l x r ds) = node (mirT r) x (mirT l) ds := rfl

@[simp] lemma mirT_mirT : ∀ t : VT, mirT (mirT t) = t
  | leaf => rfl
  | node l x r ds => by simp [mirT_mirT l, mirT_mirT r]

@[simp] lemma rt_mirT (n : ℕ) (t : VT) : rt n (mirT t) = rt n t := by cases t <;> rfl

lemma mirT_eq_leaf {t : VT} : mirT t = leaf ↔ t = leaf := by cases t <;> simp

lemma seq_mirT : ∀ t : VT, seq (mirT t) = (seq t).reverse
  | leaf => rfl
  | node l x r ds => by simp [seq_mirT l, seq_mirT r]

lemma size_mirT : ∀ t : VT, size (mirT t) = size t
  | leaf => rfl
  | node l x r ds => by simp [size_mirT l, size_mirT r]; omega

lemma pot_mirT : ∀ t : VT, pot (mirT t) = pot t
  | leaf => rfl
  | node l x r ds => by
    simp only [mirT_node, pot_node, pot_mirT l, pot_mirT r, size_mirT]; ring_nf

lemma nodes_mirT : ∀ t : VT, (nodes (mirT t)).Perm (nodes t)
  | leaf => List.Perm.refl _
  | node l x r ds => by
    rw [List.perm_iff_count]; intro a
    have h1 := (nodes_mirT l).count_eq a
    have h2 := (nodes_mirT r).count_eq a
    simp only [mirT_node, nodes_node, List.count_append, List.count_cons] at h1 h2 ⊢
    omega

lemma dE_mirT : ∀ (t : VT) (e : ℕ × ℕ), e ∈ dE (mirT t) ↔ e ∈ dE t
  | leaf, _ => Iff.rfl
  | node l x r ds, e => by
    simp only [mirT_node, dE_node, List.mem_append, dE_mirT l e, dE_mirT r e]; tauto

lemma same_mirT_seq {t t' : VT} (h : Same t t') : Same (mirT t) (mirT t') :=
  ⟨by rw [seq_mirT, seq_mirT, h.seq], fun e => by rw [dE_mirT, dE_mirT]; exact h.dE e,
    (nodes_mirT t).trans (h.nodes.trans (nodes_mirT t').symm),
    by rw [size_mirT, size_mirT, h.size]⟩

/-- The mirror image of a frame. -/
def mirF : Frame → Frame
  | .L y c dy => .R (mirT c) y dy
  | .R c y dy => .L y (mirT c) dy
  | .D l y r bef aft => .D (mirT r) y (mirT l) bef aft

lemma mirT_plugF {f : Frame} (hf : f.Solid) (t : VT) :
    mirT (f.plug t) = (mirF f).plug (mirT t) := by
  cases f <;> simp_all [mirF, Frame.plug, Frame.Solid]

lemma mirF_solid {f : Frame} : (mirF f).Solid ↔ f.Solid := by
  cases f <;> simp [mirF, Frame.Solid]

@[simp] lemma mirF_y (f : Frame) : (mirF f).y = f.y := by cases f <;> rfl

lemma mirT_rotUp (t : VT) {f : Frame} (hf : f.Solid) :
    mirT (rotUp t f) = rotUp (mirT t) (mirF f) := by
  cases t with
  | leaf => cases f <;> simp_all [Frame.Solid, rotUp, mirF, Frame.plug]
  | node a x b dx => cases f <;> simp_all [Frame.Solid, rotUp, mirF]

end VT

end DynTree

end PlanarFlow
