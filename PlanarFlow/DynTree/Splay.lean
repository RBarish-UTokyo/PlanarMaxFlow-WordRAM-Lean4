module

public import PlanarFlow.DynTree.Push

/-!
# Dynamic trees: splaying

**Ghost.** `splay1 t ctx` is one splay step at the root `x` of `t` in the zipper `ctx`: a zig
(the parent of `x` is the root of its auxiliary tree), a zig-zig or a zig-zag; `splayG` repeats it
until `x` is the root of its auxiliary tree (the zipper no longer starts with a solid frame).
`splayG_spec`: the result is `(t', rest)` with `ctx = sf ++ rest` (`sf` the solid frames),
`t'` represents the same paths as `plug t sf`, has root `x` with the same hanging trees, and the
rank potential satisfies the access lemma
`pot (plug t' rest) + 3 r(t) + |sf| / 2 ≤ pot (plug t ctx) + 3 r(t')` (`r = ⌊log₂ size⌋`).

**Memory.** `splayStepM x` is the step on the memory: it pushes the reversal bits of the
grandparent (in a zig-zig or zig-zag), of the parent and of `x`, top down, and then makes one or
two rotations, chosen by reading the pointers; `splayStep_ok`: it realises `splay1` on a stored
virtual forest. The test "`x` is a child of its parent" read in the memory is `HeadSolid ctx`.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine VT

namespace VT

instance (f : Frame) : Decidable f.Solid := by cases f <;> unfold Frame.Solid <;> infer_instance
instance (f : Frame) : Decidable f.IsL := by cases f <;> unfold Frame.IsL <;> infer_instance

/-- One splay step at the root of `t`, with the zipper `ctx` above it. -/
def splay1 : VT → List Frame → VT × List Frame
  | t, f1 :: f2 :: fs =>
    if f1.Solid then
      if f2.Solid then
        if (f1.IsL ↔ f2.IsL) then (rotUp t (zz f1 f2), fs) else (rotUp (rotUp t f1) f2, fs)
      else (rotUp t f1, f2 :: fs)
    else (t, f1 :: f2 :: fs)
  | t, [f1] => if f1.Solid then (rotUp t f1, []) else (t, [f1])
  | t, [] => (t, [])

/-- The zipper starts with a solid frame: the root of the hole is not the root of its auxiliary
tree. -/
def HeadSolid : List Frame → Prop
  | f :: _ => f.Solid
  | [] => False

instance (ctx : List Frame) : Decidable (HeadSolid ctx) := by
  cases ctx <;> unfold HeadSolid <;> infer_instance

/-- The hanging trees of the root. -/
def dsOf : VT → List VT
  | leaf => []
  | node _ _ _ ds => ds

lemma rotUp_shape {a b : VT} {x : ℕ} {dx : List VT} {f : Frame} (hf : f.Solid) :
    ∃ a' b', rotUp (node a x b dx) f = node a' x b' dx := by
  cases f with
  | L y c dy => exact ⟨_, _, rfl⟩
  | R c y dy => exact ⟨_, _, rfl⟩
  | D l y r bef aft => exact absurd hf (by simp [Frame.Solid])

lemma Same.trans {t t' t'' : VT} (h : Same t t') (h' : Same t' t'') : Same t t'' :=
  ⟨h.seq.trans h'.seq, fun e => (h.dE e).trans (h'.dE e), h.nodes.trans h'.nodes,
    h.size.trans h'.size⟩

lemma zz_IsL {f₁ f₂ : Frame} (h : SameSide f₁ f₂) : (zz f₁ f₂).IsL ↔ f₁.IsL := by
  obtain ⟨h1, h2, h3⟩ := h
  cases f₁ <;> cases f₂ <;> simp_all [Frame.Solid, Frame.IsL, zz]

lemma zz_fsize {f₁ f₂ : Frame} (h : SameSide f₁ f₂) : (zz f₁ f₂).fsize = f₁.fsize + f₂.fsize := by
  obtain ⟨h1, h2, h3⟩ := h
  cases f₁ <;> cases f₂ <;> simp_all [Frame.Solid, Frame.IsL, zz, Frame.fsize] <;> omega

lemma pot_plugZ_cons (t : VT) (f : Frame) (fs : List Frame) :
    pot (plug t (f :: fs)) = pot (f.plug t) + cpot fs (size (f.plug t)) := by
  rw [plug_cons, pot_plugZ]

/-- **One splay step.** -/
lemma splay1_spec {t : VT} (ht : t ≠ leaf) {ctx : List Frame} (hc : HeadSolid ctx) :
    ∃ pre, ctx = pre ++ (splay1 t ctx).2 ∧ (∀ f ∈ pre, f.Solid) ∧
      Same (splay1 t ctx).1 (plug t pre) ∧ (splay1 t ctx).1 ≠ leaf ∧
      (∀ m, rt m (splay1 t ctx).1 = rt m t) ∧ dsOf (splay1 t ctx).1 = dsOf t ∧
      ((pre.length = 1 ∧ ¬ HeadSolid (splay1 t ctx).2 ∧
          pot (plug (splay1 t ctx).1 (splay1 t ctx).2) + 3 * Nat.log 2 (size t) ≤
          pot (plug t ctx) + 3 * Nat.log 2 (size (splay1 t ctx).1)) ∨
       (pre.length = 2 ∧ pot (plug (splay1 t ctx).1 (splay1 t ctx).2) + 3 * Nat.log 2 (size t) + 1 ≤
          pot (plug t ctx) + 3 * Nat.log 2 (size (splay1 t ctx).1))) := by
  obtain ⟨a, x, b, dx, rfl⟩ : ∃ a x b dx, t = node a x b dx := by
    cases t with
    | leaf => exact absurd rfl ht
    | node a x b dx => exact ⟨a, x, b, dx, rfl⟩
  -- the zig case, shared by two branches
  have zig : ∀ (f1 : Frame) (rest : List Frame), f1.Solid → ¬ HeadSolid rest →
      ∃ pre, f1 :: rest = pre ++ rest ∧ (∀ f ∈ pre, f.Solid) ∧
      Same (rotUp (node a x b dx) f1) (plug (node a x b dx) pre) ∧
      rotUp (node a x b dx) f1 ≠ leaf ∧
      (∀ m, rt m (rotUp (node a x b dx) f1) = rt m (node a x b dx)) ∧
      dsOf (rotUp (node a x b dx) f1) = dsOf (node a x b dx) ∧
      ((pre.length = 1 ∧ ¬ HeadSolid rest ∧ pot (plug (rotUp (node a x b dx) f1) rest) +
          3 * Nat.log 2 (size (node a x b dx)) ≤ pot (plug (node a x b dx) (f1 :: rest)) +
          3 * Nat.log 2 (size (rotUp (node a x b dx) f1))) ∨
       (pre.length = 2 ∧ pot (plug (rotUp (node a x b dx) f1) rest) +
          3 * Nat.log 2 (size (node a x b dx)) + 1 ≤ pot (plug (node a x b dx) (f1 :: rest)) +
          3 * Nat.log 2 (size (rotUp (node a x b dx) f1)))) := by
    intro f1 rest hf1 hrest
    obtain ⟨a', b', e⟩ := rotUp_shape (a := a) (b := b) (x := x) (dx := dx) hf1
    refine ⟨[f1], rfl, by simpa using hf1, same_rotUp hf1, by rw [e]; simp, fun m => by rw [e]; rfl,
      by rw [e]; rfl, Or.inl ⟨rfl, hrest, ?_⟩⟩
    have k := pot_zig (t := node a x b dx) (by simp) hf1
    rw [pot_plugZ, pot_plugZ_cons, size_rotUp]
    have hm := log_mono (show size (node a x b dx) ≤ size (f1.plug (node a x b dx)) by
      rw [Frame.size_plug]; omega)
    omega
  rcases ctx with _ | ⟨f1, _ | ⟨f2, fs⟩⟩
  · exact absurd hc (by simp [HeadSolid])
  · have hf1 : f1.Solid := hc
    simp only [splay1, hf1, ite_true]
    simpa using zig f1 [] hf1 (by simp [HeadSolid])
  · have hf1 : f1.Solid := hc
    by_cases hf2 : f2.Solid
    · by_cases hs : (f1.IsL ↔ f2.IsL)
      · simp only [splay1, hf1, hf2, hs, ite_true]
        have hss : SameSide f1 f2 := ⟨hf1, hf2, hs⟩
        obtain ⟨a', b', e⟩ := rotUp_shape (a := a) (b := b) (x := x) (dx := dx) (zz_solid hss)
        refine ⟨[f1, f2], rfl, by simp [hf1, hf2], ?_, by rw [e]; simp, fun m => by rw [e]; rfl,
          by rw [e]; rfl, Or.inr ⟨rfl, ?_⟩⟩
        · refine (same_rotUp (zz_solid hss)).trans ?_
          rw [← rotUp_plug_zz hss]
          exact same_rotUp hf2
        · have k := pot_zigzig (t := node a x b dx) (by simp) hss
          rw [pot_plugZ, plug_cons, pot_plugZ_cons]
          simp only [size_rotUp, Frame.size_plug, zz_fsize hss, Nat.add_assoc] at k ⊢
          omega
      · simp only [splay1, hf1, hf2, hs, ite_true, ite_false]
        have hos : OppSide f1 f2 := ⟨hf1, hf2, hs⟩
        obtain ⟨a', b', e1⟩ := rotUp_shape (a := a) (b := b) (x := x) (dx := dx) hf1
        obtain ⟨a'', b'', e2⟩ := rotUp_shape (a := a') (b := b') (x := x) (dx := dx) hf2
        refine ⟨[f1, f2], rfl, by simp [hf1, hf2], ?_, by rw [e1, e2]; simp,
          fun m => by rw [e1, e2]; rfl, by rw [e1, e2]; rfl, Or.inr ⟨rfl, ?_⟩⟩
        · exact (same_rotUp hf2).trans ((same_rotUp hf1).plugF f2)
        · have k := pot_zigzag (t := node a x b dx) (by simp) hos
          rw [pot_plugZ, plug_cons, pot_plugZ_cons]
          simp only [size_rotUp, Frame.size_plug, Nat.add_assoc] at k ⊢
          omega
    · simp only [splay1, hf1, hf2, ite_true, ite_false]
      exact zig f1 (f2 :: fs) hf1 hf2

lemma splay1_length {t : VT} (ht : t ≠ leaf) {ctx : List Frame} (hc : HeadSolid ctx) :
    (splay1 t ctx).2.length < ctx.length := by
  obtain ⟨pre, e, -, -, -, -, -, h⟩ := splay1_spec ht hc
  have : pre ≠ [] := by
    rintro rfl
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> simp at h
  conv_rhs => rw [e]
  rw [List.length_append]
  have := List.length_pos_iff.mpr this
  omega

lemma plug_append (t : VT) (a b : List Frame) : plug t (a ++ b) = plug (plug t a) b := by
  induction a generalizing t with
  | nil => rfl
  | cons f a ih => exact ih _

/-- `t` is not a leaf. -/
def isNode : VT → Bool
  | leaf => false
  | node _ _ _ _ => true

lemma isNode_iff {t : VT} : t.isNode = true ↔ t ≠ leaf := by
  cases t <;> simp [isNode]

/-- Splay the root of `t` to the root of its auxiliary tree. -/
def splayG (t : VT) (ctx : List Frame) : VT × List Frame :=
  if h : HeadSolid ctx ∧ t.isNode = true then splayG (splay1 t ctx).1 (splay1 t ctx).2
  else (t, ctx)
termination_by ctx.length
decreasing_by exact splay1_length (isNode_iff.mp h.2) h.1

/-- **Splaying.** The solid frames `sf` above the root of `t` are consumed; the result represents
the same paths as `plug t sf`, has the same root and hanging trees, and satisfies the access
lemma. -/
theorem splayG_spec {t : VT} (ht : t ≠ leaf) (ctx : List Frame) :
    ∃ sf, ctx = sf ++ (splayG t ctx).2 ∧ (∀ f ∈ sf, f.Solid) ∧ ¬ HeadSolid (splayG t ctx).2 ∧
      Same (splayG t ctx).1 (plug t sf) ∧ (splayG t ctx).1 ≠ leaf ∧
      (∀ m, rt m (splayG t ctx).1 = rt m t) ∧ dsOf (splayG t ctx).1 = dsOf t ∧
      pot (plug (splayG t ctx).1 (splayG t ctx).2) + 3 * Nat.log 2 (size t) + sf.length / 2 ≤
        pot (plug t ctx) + 3 * Nat.log 2 (size (splayG t ctx).1) := by
  induction hn : ctx.length using Nat.strong_induction_on generalizing t ctx with
  | _ N ih =>
    by_cases hc : HeadSolid ctx
    · rw [splayG, dite_cond_eq_true (eq_true ⟨hc, isNode_iff.mpr ht⟩)]
      obtain ⟨pre, e, hpre, hsame, hne, hrt, hds, hpot⟩ := splay1_spec ht hc
      generalize hr1 : splay1 t ctx = r1 at e hsame hne hrt hds hpot
      obtain ⟨t1, ctx1⟩ := r1
      simp only at e hsame hne hrt hds hpot ⊢
      have hlen : ctx1.length < N := by
        rw [← hn, e, List.length_append]
        have : pre ≠ [] := by
          rintro rfl
          rcases hpot with ⟨h, -⟩ | ⟨h, -⟩ <;> simp at h
        have := List.length_pos_iff.mpr this
        omega
      obtain ⟨sf1, e1, hsf1, hns, hs1, hne1, hrt1, hds1, hpot1⟩ := ih _ hlen hne ctx1 rfl
      refine ⟨pre ++ sf1, ?_, ?_, hns, ?_, hne1, fun m => (hrt1 m).trans (hrt m), hds1.trans hds,
        ?_⟩
      · rw [List.append_assoc, ← e1, e]
      · intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact hpre f hf
        · exact hsf1 f hf
      · rw [plug_append]
        exact hs1.trans (hsame.plugZ sf1)
      · rw [List.length_append]
        rcases hpot with ⟨h1, h2, h3⟩ | ⟨h1, h3⟩
        · have : sf1 = [] := by
            rcases sf1 with _ | ⟨f, sf1⟩
            · rfl
            · exact absurd (by rw [e1]; exact hsf1 f (by simp)) h2
          subst this
          rw [h1]; simp only [List.length_nil] at hpot1 ⊢
          omega
        · rw [h1]
          have : (2 + sf1.length) / 2 = sf1.length / 2 + 1 := by omega
          rw [this]
          omega
    · rw [splayG, dite_cond_eq_false (eq_false (fun h => hc h.1))]
      exact ⟨[], rfl, by simp, hc, Same.refl _, ht, fun _ => rfl, rfl, by simp⟩

/-- The number of solid frames at the start of a zipper (the depth of the hole in its auxiliary
tree). -/
def sp : List Frame → ℕ
  | [] => 0
  | f :: fs => if f.Solid then sp fs + 1 else 0

lemma sp_of_not {ctx : List Frame} (h : ¬ HeadSolid ctx) : sp ctx = 0 := by
  cases ctx with
  | nil => rfl
  | cons f fs => simp only [sp]; exact ite_of_neg h _ _

lemma sp_append {sf rest : List Frame} (hsf : ∀ f ∈ sf, f.Solid) (hr : ¬ HeadSolid rest) :
    sp (sf ++ rest) = sf.length := by
  induction sf with
  | nil => exact sp_of_not hr
  | cons f sf ih =>
    simp only [List.cons_append, sp, List.length_cons]
    rw [ite_of_pos (hsf f (by simp)), ih (fun g hg => hsf g (by simp [hg]))]

lemma sp_cons_solid {f : Frame} {fs : List Frame} (h : f.Solid) : sp (f :: fs) = sp fs + 1 := by
  simp only [sp]; exact ite_of_pos h _ _

/-- One splay step lowers `⌈sp / 2⌉` by one. -/
lemma splay1_sp {t : VT} (ht : t ≠ leaf) {ctx : List Frame} (hc : HeadSolid ctx) :
    (sp (splay1 t ctx).2 + 1) / 2 + 1 ≤ (sp ctx + 1) / 2 := by
  obtain ⟨pre, e, hpre, -, -, -, -, hpot⟩ := splay1_spec ht hc
  generalize (splay1 t ctx).2 = ctx' at e hpot
  subst e
  rcases hpot with ⟨h1, h2, -⟩ | ⟨h1, -⟩
  · rw [sp_of_not h2]
    obtain ⟨f, rfl⟩ : ∃ f, pre = [f] := List.length_eq_one_iff.mp h1
    rw [List.singleton_append, sp_cons_solid (hpre f (by simp)), sp_of_not h2]
  · obtain ⟨f, g, rfl⟩ : ∃ f g, pre = [f, g] := List.length_eq_two.mp h1
    simp only [List.cons_append, List.nil_append]
    rw [sp_cons_solid (hpre f (by simp)), sp_cons_solid (hpre g (by simp))]
    omega

lemma splayG_step {t : VT} (ht : t ≠ leaf) {ctx : List Frame} (hc : HeadSolid ctx) :
    splayG (splay1 t ctx).1 (splay1 t ctx).2 = splayG t ctx := by
  conv_rhs => rw [splayG, dite_cond_eq_true (eq_true ⟨hc, isNode_iff.mpr ht⟩)]

lemma splayG_stop (t : VT) {ctx : List Frame} (hc : ¬ HeadSolid ctx) : splayG t ctx = (t, ctx) := by
  rw [splayG, dite_cond_eq_false (eq_false (fun h => hc h.1))]

lemma splay1_node {t : VT} (ht : t ≠ leaf) {ctx : List Frame} (hc : HeadSolid ctx) (m : ℕ) :
    (splay1 t ctx).1 ≠ leaf ∧ rt m (splay1 t ctx).1 = rt m t := by
  obtain ⟨-, -, -, -, h1, h2, -⟩ := splay1_spec ht hc
  exact ⟨h1, h2 m⟩

end VT

/-! ### The splay step on the memory -/

variable (B n : ℕ)

/-- `x` is a child of its parent in the auxiliary tree (it is not the root of its auxiliary
tree). -/
def IsChild (M : Mem) (x : ℕ) : Prop := lc B M (par B M x) = x ∨ rc B M (par B M x) = x

instance (M : Mem) (x : ℕ) : Decidable (IsChild B M x) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- One splay step at `x` on the memory: push the bits of the nodes to be rotated, top down,
then a zig, a zig-zig (rotate the parent first) or a zig-zag (rotate `x` twice), read from the
pointers. -/
def splayStepM (x : ℕ) (M : Mem) : Mem :=
  if IsChild B M (par B M x) then
    if (lc B (pushM B x (pushM B (par B M x) (pushM B (par B M (par B M x)) M))) (par B M x) = x ↔
        lc B (pushM B x (pushM B (par B M x) (pushM B (par B M (par B M x)) M)))
          (par B M (par B M x)) = par B M x) then
      rotMem B n x (rotMem B n (par B M x)
        (pushM B x (pushM B (par B M x) (pushM B (par B M (par B M x)) M))))
    else rotMem B n x (rotMem B n x
        (pushM B x (pushM B (par B M x) (pushM B (par B M (par B M x)) M))))
  else rotMem B n x (pushM B x (pushM B (par B M x) M))

/-- The pointers of the node of a stored frame to the root `r` of the hole. -/
lemma frame_ptr {M : Mem} {f : Frame} {r : ℕ} {π : Bool} (hF : EncF B n M f r π) (hr : r < n)
    (hnot : r ∉ f.fnodes) :
    ((lc B M f.y = r ∨ rc B M f.y = r) ↔ f.Solid) ∧
      (f.Solid → (lc B M f.y = r ↔ (f.IsL ↔ cσ B M π f.y = false))) := by
  have hrt : ∀ c : VT, (∀ u ∈ nodes c, u ∈ f.fnodes) → rt n c ≠ r := by
    intro c hc e
    rcases rt_or_nil n c with ⟨-, h⟩ | h
    · rw [h] at e; omega
    · exact hnot (e ▸ hc _ h)
  cases f with
  | L y c dy =>
    obtain ⟨e1, e2, -⟩ := hF
    have := hrt c (fun u hu => by simp [Frame.fnodes, hu])
    simp only [Frame.y, Frame.Solid, Frame.IsL]
    cases e : cσ B M π y <;> simp only [lcS, e, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at e1 e2 <;> simp [e1, e2, this, Ne.symm this]
  | R c y dy =>
    obtain ⟨e1, e2, -⟩ := hF
    have := hrt c (fun u hu => by simp [Frame.fnodes, hu])
    simp only [Frame.y, Frame.Solid, Frame.IsL]
    cases e : cσ B M π y <;> simp only [lcS, e, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at e1 e2 <;> simp [e1, e2, this, Ne.symm this]
  | D l y rr bef aft =>
    obtain ⟨e1, e2, -⟩ := hF
    have h1 := hrt l (fun u hu => by simp [Frame.fnodes, hu])
    have h2 := hrt rr (fun u hu => by simp [Frame.fnodes, hu])
    simp only [Frame.y, Frame.Solid, Frame.IsL]
    cases e : cσ B M π y <;> simp only [lcS, e, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at e1 e2 <;> simp [e1, e2, h1, h2]

/-- The facts about the root `x` of `t` in a stored zipper. -/
lemma root_facts {M : Mem} {G : List VT} (hI : Inv B n M G) {gb ga : List VT} {t : VT}
    {ctx : List Frame} (hG : G = gb ++ plug t ctx :: ga) (ht : t ≠ leaf) :
    par B M (rt n t) = hp n ctx ∧ (IsChild B M (rt n t) ↔ HeadSolid ctx) ∧
    (∀ f fs, ctx = f :: fs → f.Solid →
      (lc B M f.y = rt n t ↔ (f.IsL ↔ cσ B M (cpar B M fs) f.y = false))) := by
  have hX := rotCtx B n hI hG
  have hx : rt n t ∈ nodes t := rt_mem_nodes ht n
  have hxn := hX.lts _ hx
  have hpar := hX.enc.par_rt B n ht
  refine ⟨hpar, ?_, ?_⟩
  · unfold IsChild
    rw [hpar]
    rcases ctx with _ | ⟨f, fs⟩
    · simp only [hp, HeadSolid, iff_false]
      rw [hI.nil.lc, hI.nil.rc]; omega
    · have hF := hX.encC.1
      have hnot : rt n t ∉ f.fnodes := fun hm => ne_of_count (fun w => by
        have := hX.count w; simp only [cnodes_cons, List.count_append] at this; omega) hx hm rfl
      exact (frame_ptr B n hF hxn hnot).1
  · rintro f fs rfl hf
    have hF := hX.encC.1
    have hnot : rt n t ∉ f.fnodes := fun hm => ne_of_count (fun w => by
      have := hX.count w; simp only [cnodes_cons, List.count_append] at this; omega) hx hm rfl
    exact (frame_ptr B n hF hxn hnot).2 hf

/-- Pushes keep the reversal bits outside the pushed subtree, and the ghost. -/
lemma push_okE' {M : Mem} {G : List VT} {F : Forest} (hI : Inv B n M G) (hR : RepE B n M G F)
    {gb ga : List VT} {t : VT} {ctx : List Frame} (hG : G = gb ++ plug t ctx :: ga)
    (ht : t ≠ VT.leaf) :
    Inv B n (pushM B (rt n t) M) G ∧ RepE B n (pushM B (rt n t) M) G F ∧
      MemFrame B n M (pushM B (rt n t) M) ∧ (∀ u, fpar B (pushM B (rt n t) M) u = fpar B M u) ∧
      rv B (pushM B (rt n t) M) (rt n t) = false ∧
      (∀ u ∈ cnodes ctx, rv B (pushM B (rt n t) M) u = rv B M u) ∧
      (∀ u, par B (pushM B (rt n t) M) u = par B M u) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := push_okE B n hI hR hG ht
  refine ⟨h1, h2, h3, h4, h5, fun u hu => ?_, fun u => pushM_keep (by omega) (by omega)⟩
  have hX := rotCtx B n hI hG
  obtain ⟨l, x, r, ds, rfl⟩ : ∃ l x r ds, t = node l x r ds := by
    cases t with
    | leaf => exact absurd rfl ht
    | node l x r ds => exact ⟨l, x, r, ds, rfl⟩
  have hnd : (nodes (node l x r ds)).Nodup :=
    List.nodup_iff_count_le_one.mpr fun w => by have := hX.count w; omega
  have hout := hX.out
  have := (pushLocal B n hI.nil hX.enc hnd hX.lts hX.z_out).2.2.2.1 u (hX.ltc u hu)
    (fun h => hout u (List.mem_append_left _ hu) u h rfl)
  exact this.rv B

/-- **The splay step on the memory realises `splay1`.** -/
theorem splayStep_okE {M : Mem} {G : List VT} {F : Forest} (hI : Inv B n M G)
    (hR : RepE B n M G F) {gb ga : List VT} {t : VT} {ctx : List Frame}
    (hG : G = gb ++ plug t ctx :: ga) (ht : t ≠ leaf) (hc : HeadSolid ctx) :
    Inv B n (splayStepM B n (rt n t) M) (gb ++ plug (splay1 t ctx).1 (splay1 t ctx).2 :: ga) ∧
    RepE B n (splayStepM B n (rt n t) M) (gb ++ plug (splay1 t ctx).1 (splay1 t ctx).2 :: ga) F ∧
    MemFrame B n M (splayStepM B n (rt n t) M) ∧
    (∀ u, fpar B (splayStepM B n (rt n t) M) u = fpar B M u) := by
  obtain ⟨hpar, -, -⟩ := root_facts B n hI hG ht
  rcases ctx with _ | ⟨f1, rest⟩
  · exact absurd hc (by simp [HeadSolid])
  have hf1 : f1.Solid := hc
  simp only [hp] at hpar
  -- the parent `y = f1.y` and its facts
  have hG1 : G = gb ++ plug (f1.plug t) rest :: ga := hG
  have hy1 : f1.plug t ≠ leaf := by cases f1 <;> simp [Frame.plug]
  obtain ⟨hpar1, hch1, -⟩ := root_facts B n hI hG1 hy1
  simp only [rt_plugF, hp] at hpar1 hch1
  have fp2 : ∀ {M1 M2 M3 : Mem}, (∀ u, fpar B M2 u = fpar B M1 u) →
      (∀ u, fpar B M3 u = fpar B M2 u) → ∀ u, fpar B M3 u = fpar B M1 u :=
    fun h1 h2 u => (h2 u).trans (h1 u)
  -- the zig: push `y`, push `x`, rotate
  have zig : ¬ HeadSolid rest →
      splayStepM B n (rt n t) M = rotMem B n (rt n t) (pushM B (rt n t) (pushM B f1.y M)) := by
    intro h
    unfold splayStepM
    rw [hpar, ite_of_neg (fun h' => h (hch1.mp h'))]
  have zigOK : ¬ HeadSolid rest →
      Inv B n (splayStepM B n (rt n t) M) (gb ++ plug (rotUp t f1) rest :: ga) ∧
      RepE B n (splayStepM B n (rt n t) M) (gb ++ plug (rotUp t f1) rest :: ga) F ∧
      MemFrame B n M (splayStepM B n (rt n t) M) ∧
      (∀ u, fpar B (splayStepM B n (rt n t) M) u = fpar B M u) := by
    intro h
    rw [zig h]
    obtain ⟨Ia, Ra, Fa, Pa, ya, -, -⟩ := push_okE' B n hI hR hG1 hy1
    simp only [rt_plugF] at Ia Ra Fa Pa ya
    obtain ⟨Ib, Rb, Fb, Pb, xb, yb, -⟩ := push_okE' B n Ia Ra hG ht
    obtain ⟨Ic, Rc, Fc⟩ := rotate_okE B n Ib Rb hG hf1 ht xb
      (by rw [yb _ (by simp [cnodes_cons, y_mem_fnodes])]; exact ya)
    exact ⟨Ic, Rc, (Fa.trans B n Fb).trans B n Fc, fp2 (fp2 Pa Pb) (fun u => rotMem_fpar u)⟩
  rcases rest with _ | ⟨f2, fs⟩
  · simp only [splay1, hf1, ite_true]
    exact zigOK (by simp [HeadSolid])
  by_cases hf2 : f2.Solid
  · have hch : IsChild B M f1.y := hch1.mpr hf2
    -- push `z`, `y`, `x`
    have hG2 : G = gb ++ plug (f2.plug (f1.plug t)) fs :: ga := hG
    have hz2 : f2.plug (f1.plug t) ≠ leaf := by cases f2 <;> simp [Frame.plug]
    obtain ⟨Ia, Ra, Fa, Pa, za, -, qa⟩ := push_okE' B n hI hR hG2 hz2
    simp only [rt_plugF] at Ia Ra Fa Pa za qa
    obtain ⟨Ib, Rb, Fb, Pb, yb, zb, qb⟩ := push_okE' B n Ia Ra hG1 hy1
    simp only [rt_plugF] at Ib Rb Fb Pb yb zb qb
    obtain ⟨Ic, Rc, Fc, Pc, xc, yc, qc⟩ := push_okE' B n Ib Rb hG ht
    generalize hM3 : pushM B (rt n t) (pushM B f1.y (pushM B f2.y M)) = M3 at Ic Rc Fc Pc xc yc qc
    have hyc : rv B M3 f1.y = false := by
      rw [yc _ (by simp [cnodes_cons, y_mem_fnodes])]; exact yb
    have hzc : rv B M3 f2.y = false := by
      rw [yc _ (by simp [cnodes_cons, y_mem_fnodes]), zb _ (by simp [cnodes_cons, y_mem_fnodes])]
      exact za
    have hpz : par B M f1.y = f2.y := hpar1
    obtain ⟨-, -, hL⟩ := root_facts B n Ic hG ht
    obtain ⟨-, -, hL1⟩ := root_facts B n Ic hG1 hy1
    simp only [rt_plugF] at hL1
    have e1 := hL f1 _ rfl hf1
    have e2 := hL1 f2 fs rfl hf2
    have hσ : cσ B M3 (cpar B M3 (f2 :: fs)) f1.y = cσ B M3 (cpar B M3 fs) f2.y := by
      rcases frame_solid_cases hf2 with ⟨y, c, dy, rfl⟩ | ⟨c, y, dy, rfl⟩ <;>
        simp only [cpar, DynTree.hpar, cσ, hyc, Bool.xor_false]
    have hσ2 : cσ B M3 (cpar B M3 fs) f2.y = cpar B M3 fs := by simp [cσ, hzc]
    rw [hσ, hσ2] at e1
    rw [hσ2] at e2
    have hstepM : splayStepM B n (rt n t) M = (if (lc B M3 f1.y = rt n t ↔ lc B M3 f2.y = f1.y)
        then rotMem B n (rt n t) (rotMem B n f1.y M3)
        else rotMem B n (rt n t) (rotMem B n (rt n t) M3)) := by
      unfold splayStepM
      rw [hpar, ite_of_pos hch, hpz, hM3]
    have key : (lc B M3 f1.y = rt n t ↔ lc B M3 f2.y = f1.y) ↔ (f1.IsL ↔ f2.IsL) := by
      rw [e1, e2]
      by_cases a : f1.IsL <;> by_cases b : f2.IsL <;> cases cpar B M3 fs <;> simp [a, b]
    by_cases hs : (f1.IsL ↔ f2.IsL)
    · simp only [splay1, hf1, hf2, hs, ite_true]
      have hss : SameSide f1 f2 := ⟨hf1, hf2, hs⟩
      rw [hstepM, ite_of_pos (key.mpr hs)]
      obtain ⟨I1, R1, F1⟩ := rotate_okE B n Ic Rc hG1 hf2 hy1 (by rw [rt_plugF]; exact hyc) hzc
      simp only [rt_plugF] at I1 R1 F1
      rw [rotUp_plug_zz hss] at I1 R1
      obtain ⟨I2, R2, F2⟩ := rotate_okE B n I1 R1 (t := t) (f := zz f1 f2) (fs := fs) rfl
        (zz_solid hss) ht (by rw [rotMem_rv]; exact xc) (by rw [zz_y hss, rotMem_rv]; exact hyc)
      refine ⟨I2, R2, (((Fa.trans B n Fb).trans B n Fc).trans B n F1).trans B n F2, ?_⟩
      intro u; rw [rotMem_fpar, rotMem_fpar, Pc, Pb, Pa]
    · simp only [splay1, hf1, hf2, hs, ite_true, ite_false]
      rw [hstepM, ite_of_neg (fun h => hs (key.mp h))]
      obtain ⟨I1, R1, F1⟩ := rotate_okE B n Ic Rc hG hf1 ht xc hyc
      obtain ⟨a, x, b, dx, rfl⟩ : ∃ a x b dx, t = node a x b dx := by
        cases t with
        | leaf => exact absurd rfl ht
        | node a x b dx => exact ⟨a, x, b, dx, rfl⟩
      obtain ⟨a', b', e⟩ := rotUp_shape (a := a) (b := b) (x := x) (dx := dx) hf1
      rw [e] at I1 R1 ⊢
      obtain ⟨I2, R2, F2⟩ := rotate_okE B n I1 R1 (t := node a' x b' dx) (f := f2) (fs := fs) rfl
        hf2 (by simp) (by rw [rt_node, rotMem_rv]; exact xc) (by rw [rotMem_rv]; exact hzc)
      refine ⟨I2, R2, (((Fa.trans B n Fb).trans B n Fc).trans B n F1).trans B n F2, ?_⟩
      intro u; simp only [rt_node] at *
      rw [rotMem_fpar, rotMem_fpar, Pc, Pb, Pa]
  · simp only [splay1, hf1, hf2, ite_true, ite_false]
    exact zigOK hf2

theorem splayStep_ok {M : Mem} {G : List VT} {F : Forest} (hI : Inv B n M G)
    (hR : Rep B n M G F) {gb ga : List VT} {t : VT} {ctx : List Frame}
    (hG : G = gb ++ plug t ctx :: ga) (ht : t ≠ leaf) (hc : HeadSolid ctx) :
    Inv B n (splayStepM B n (rt n t) M) (gb ++ plug (splay1 t ctx).1 (splay1 t ctx).2 :: ga) ∧
    Rep B n (splayStepM B n (rt n t) M) (gb ++ plug (splay1 t ctx).1 (splay1 t ctx).2 :: ga) F ∧
    MemFrame B n M (splayStepM B n (rt n t) M) := by
  obtain ⟨h1, h2, h3, h4⟩ := splayStep_okE B n hI hR.toRepE hG ht hc
  exact ⟨h1, ⟨h2, fun u hu => by rw [h4]; exact hR.fpar u hu⟩, h3⟩

end DynTree

end PlanarFlow
