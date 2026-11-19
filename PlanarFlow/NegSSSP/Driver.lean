module

public import PlanarFlow.NegSSSP.Rec
public import WordRAM.Programs.Tactics
public import WordRAM.Machine.WordMono

/-!
# A post-order traversal of a decomposition with an explicit stack, on the machine

A **driver** for the recursion on a decomposition (`NTree`): one loop with an explicit stack of
frames in memory, parametric in four subprograms given by `Exec` specifications (`DSpec`):

* `testS`: decides whether the piece of the current frame is a leaf (`r2997 < 1`) or a node;
* `leafS`: the leaf solver, on the current frame (output in the frame itself);
* `splitS`: the split, writing the inputs of the two children in two new frames above the heap
  top (their ends in `r2998`, `r2999`);
* `nodeS`: the combination at a node, from the inputs of the node and the outputs of its two
  children (output in the frame of the node).

**The frames.** A frame is a segment `[b, e)` of the natural and real memory: a header of five
words (`b`: the tag, `0` to expand, `1` to combine; `b + 1`: the next frame of the stack, `0` at
the bottom; `b + 2`: the end `e`; `b + 3`, `b + 4`: the bases of the frames of the two children,
set when the frame is expanded) and the data `[b + 5, e)`. The frames are allocated on a heap
from `Hb` upwards with a bump pointer (`r3003`, the heap top); the stack of tasks is the linked
list of frames from `r3002` (the top). Expanding a node allocates its two children at the heap
top, right after the other (the left frame `[h, el)`, the right frame `[el, er)`), and pushes
them; combining a node frees them (the heap top back to `h`). So the stack is always the list of
frames of a post-order traversal still to do, and the heap a stack too.

**The registers of the driver** (`≥ 3000`, kept by the subprograms): `r3000 = 0`, `r3001 = 1`,
`r3002` the top, `r3003` the heap top, the arguments of the subprograms `r3004 = d` (the data of
the current frame), `r3005 = e` (its end), and for `nodeS` `r3006 = bl + 5`, `r3007 = el`,
`r3008 = el + 5`, `r3009 = er` (the data and ends of the children); `r3010 … r3012` scratch.

**The subprograms** may write anything below `Hb` (a work area), the registers `< 3000`, the
real registers, and the memory above the heap top; in the heap they write only their own frame
(`leafS`, `nodeS`; `nodeS` also the frames of the children, freed afterwards). Their
specifications are stated with abstract predicates `In τ d e c`, `Out τ d e c` on the data
`[d, e)` of a frame of the subtree `τ` (stable under any change outside `[d, e)`, `MemEq`) and an
invariant `G` (stable under changes of the registers `≥ 3000` and of the memory from `Hb` on).

## Main results

* `regKeep_of_keep`, `heapKeep_of_keep`: a run lifted below the heap (`Exec.lift_trunc`, word
  bound `< Hb`, registers `< 3000`) meets the frame conditions of the subprograms.
* `drive`: from the root frame at `Hb` holding `In τ`, the driver runs to a configuration with
  `Out τ` in the root frame, within `dcost τ + 2` steps: the sum over the leaves of the test and
  the leaf solver, over the nodes of the test, the split and the combination, plus `20` per leaf
  and `80` per node (`dcost`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace PlanarFlow

namespace NegSSSP

namespace Driver

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {I : Input} {W : ℕ}

/-! ### The blocks of the driver -/

/-- Reading the header of the top frame `b = r3002`: `r3010` the tag, `r3004 = b + 5`,
`r3005` the end. -/
def peekB : Stmt := block [.loadN 3010 3002, .constN 3011 5, .addN 3004 3002 3011,
  .constN 3011 2, .addN 3012 3002 3011, .loadN 3005 3012]

/-- Popping the top frame: `r3002 := nmem (b + 1)`. -/
def popB : Stmt := block [.constN 3011 1, .addN 3012 3002 3011, .loadN 3002 3012]

/-- After the split of the top frame `b` (heap top `h = r3003`, the ends `el = r2998`,
`er = r2999` of the children): the tag of `b` set to `1`, the bases `h`, `el` of the children in
its header, the headers of the children (`h`: next `el`, end `el`; `el`: next `b`, end `er`),
the top `h`, the heap top `er`. -/
def pushB : Stmt := block [.constN 3011 1, .storeN 3002 3011,
  .constN 3011 3, .addN 3012 3002 3011, .storeN 3012 3003,
  .constN 3011 4, .addN 3012 3002 3011, .storeN 3012 2998,
  .constN 3011 0, .storeN 3003 3011,
  .constN 3011 1, .addN 3012 3003 3011, .storeN 3012 2998,
  .constN 3011 2, .addN 3012 3003 3011, .storeN 3012 2998,
  .constN 3011 0, .storeN 2998 3011,
  .constN 3011 1, .addN 3012 2998 3011, .storeN 3012 3002,
  .constN 3011 2, .addN 3012 2998 3011, .storeN 3012 2999,
  .copyN 3002 3003, .copyN 3003 2999]

/-- The arguments of `nodeS` at the top frame `b`: `r3006 = bl + 5`, `r3007 = el`,
`r3008 = el + 5`, `r3009 = er` (the heap top). -/
def coB : Stmt := block [.constN 3011 3, .addN 3012 3002 3011, .loadN 3011 3012,
  .constN 3012 5, .addN 3006 3011 3012, .constN 3011 4, .addN 3012 3002 3011,
  .loadN 3007 3012, .constN 3012 5, .addN 3008 3007 3012, .copyN 3009 3003]

/-- After `nodeS` at the top frame `b`: the heap top back to `bl`, the frame popped. -/
def coPost : Stmt := block [.constN 3011 3, .addN 3012 3002 3011, .loadN 3003 3012,
  .constN 3011 1, .addN 3012 3002 3011, .loadN 3002 3012]

/-- One step of the driver: expand (test; leaf and pop, or split and push) or combine. -/
def body (testS leafS splitS nodeS : Stmt) : Stmt :=
  .seq peekB (.ifLtN 3010 3001
    (.seq testS (.ifLtN 2997 3001 (.seq leafS popB) (.seq splitS pushB)))
    (.seq coB (.seq nodeS coPost)))

/-- **The driver**: the steps while the stack is not empty (`r3000 = 0 < r3002`). -/
def driver (testS leafS splitS nodeS : Stmt) : Stmt :=
  .whileLtN 3000 3002 (body testS leafS splitS nodeS)

/-- The memory written by `pushB`. -/
def pushMem (f : ℕ → ℕ) (b h el er : ℕ) : ℕ → ℕ :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd f b 1) (b + 3) h) (b + 4) el) h 0) (h + 1) el)
    (h + 2) el) el 0) (el + 1) b) (el + 2) er

/-! ### The specifications of the blocks -/

theorem peekB_exec {b : ℕ} (c : Config) (hc : WordsBounded W c) (r3002 : c.nreg 3002 = b)
    (hW : b + 5 ≤ W) :
    ∃ c' t, Exec I W peekB c c' t ∧ t = 6 ∧ c'.nreg 3010 = c.nmem b ∧
      c'.nreg 3004 = b + 5 ∧ c'.nreg 3005 = c.nmem (b + 2) ∧
      (∀ r, r ≠ 3004 → r ≠ 3005 → r ≠ 3010 → r ≠ 3011 → r ≠ 3012 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold peekB
  exec_block
  all_goals try ((try config_simp); (try simp only [r3002]) <;> omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r3002])
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem popB_exec {b : ℕ} (c : Config) (hc : WordsBounded W c) (r3002 : c.nreg 3002 = b)
    (hW : b + 1 ≤ W) :
    ∃ c' t, Exec I W popB c c' t ∧ t = 3 ∧ c'.nreg 3002 = c.nmem (b + 1) ∧
      (∀ r, r ≠ 3002 → r ≠ 3011 → r ≠ 3012 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold popB
  exec_block
  all_goals try ((try config_simp); (try simp only [r3002]) <;> omega)
  refine ⟨rfl, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r3002])
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem coPost_exec {b : ℕ} (c : Config) (hc : WordsBounded W c) (r3002 : c.nreg 3002 = b)
    (hW : b + 3 ≤ W) :
    ∃ c' t, Exec I W coPost c c' t ∧ t = 6 ∧ c'.nreg 3003 = c.nmem (b + 3) ∧
      c'.nreg 3002 = c.nmem (b + 1) ∧
      (∀ r, r ≠ 3002 → r ≠ 3003 → r ≠ 3011 → r ≠ 3012 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold coPost
  exec_block
  all_goals try ((try config_simp); (try simp only [r3002]) <;> omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r3002])
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem coB_exec {b bl el : ℕ} (c : Config) (hc : WordsBounded W c) (r3002 : c.nreg 3002 = b)
    (m3 : c.nmem (b + 3) = bl) (m4 : c.nmem (b + 4) = el) (hW : b + 5 ≤ W) (hl : bl + 5 ≤ W)
    (hr : el + 5 ≤ W) :
    ∃ c' t, Exec I W coB c c' t ∧ t = 11 ∧ c'.nreg 3006 = bl + 5 ∧ c'.nreg 3007 = el ∧
      c'.nreg 3008 = el + 5 ∧ c'.nreg 3009 = c.nreg 3003 ∧
      (∀ r, (r < 3006 ∨ 3012 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold coB
  exec_block
  all_goals try ((try config_simp); (try simp only [r3002, m3, m4]) <;> omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r3002, m3, m4])
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem pushB_exec {b h el er : ℕ} (c : Config) (hc : WordsBounded W c)
    (r3002 : c.nreg 3002 = b) (r3003 : c.nreg 3003 = h) (r2998 : c.nreg 2998 = el)
    (r2999 : c.nreg 2999 = er) (hW : b + 4 ≤ W) (hh : h + 2 ≤ W) (he : el + 2 ≤ W)
    (h4 : 4 ≤ W) :
    ∃ c' t, Exec I W pushB c c' t ∧ t = 26 ∧ c'.nreg 3002 = h ∧ c'.nreg 3003 = er ∧
      (∀ r, r ≠ 3002 → r ≠ 3003 → r ≠ 3011 → r ≠ 3012 → c'.nreg r = c.nreg r) ∧
      c'.nmem = pushMem c.nmem b h el er ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pushB
  exec_block
  all_goals try ((try config_simp); (try simp only [r3002, r3003, r2998, r2999]) <;> omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r3002, r3003, r2998, r2999, pushMem])
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

section PushMem

variable {f : ℕ → ℕ} {b h el er : ℕ}

lemma pushMem_keep {a : ℕ} (ha : a ≠ b ∧ a ≠ b + 3 ∧
    a ≠ b + 4 ∧ a ≠ h ∧ a ≠ h + 1 ∧ a ≠ h + 2 ∧ a ≠ el ∧ a ≠ el + 1 ∧ a ≠ el + 2) :
    pushMem f b h el er a = f a := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ha
  simp [pushMem, a1, a2, a3, a4, a5, a6, a7, a8, a9]

lemma pushMem_vals (h1 : b + 4 < h) (h2 : h + 2 < el) :
    pushMem f b h el er b = 1 ∧ pushMem f b h el er (b + 3) = h ∧
      pushMem f b h el er (b + 4) = el ∧ pushMem f b h el er h = 0 ∧
      pushMem f b h el er (h + 1) = el ∧ pushMem f b h el er (h + 2) = el ∧
      pushMem f b h el er el = 0 ∧ pushMem f b h el er (el + 1) = b ∧
      pushMem f b h el er (el + 2) = er := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [pushMem, upd_apply]; split_ifs <;> omega)

end PushMem

/-! ### The specifications of the subprograms -/

/-- The natural and real memory of `c'` agree with those of `c` on `[lo, hi)`. -/
def MemEq (c c' : Config) (lo hi : ℕ) : Prop :=
  ∀ a, lo ≤ a → a < hi → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a

/-- The heap `[Hb, h)` of `c` is kept in `c'`, except `[lo, hi)`. -/
def HeapKeep (Hb h lo hi : ℕ) (c c' : Config) : Prop :=
  ∀ a, Hb ≤ a → a < h → (a < lo ∨ hi ≤ a) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a

/-- The registers of the driver (`≥ 3000`) are kept. -/
def RegKeep (c c' : Config) : Prop := ∀ r, 3000 ≤ r → c'.nreg r = c.nreg r

lemma MemEq.trans {c c₁ c₂ : Config} {lo hi : ℕ} (h₁ : MemEq c c₁ lo hi)
    (h₂ : MemEq c₁ c₂ lo hi) : MemEq c c₂ lo hi := fun a h1 h2 =>
  ⟨(h₂ a h1 h2).1.trans (h₁ a h1 h2).1, (h₂ a h1 h2).2.trans (h₁ a h1 h2).2⟩

lemma memEq_of_eq {c c' : Config} (hn : c'.nmem = c.nmem) (hr : c'.rmem = c.rmem)
    (lo hi : ℕ) : MemEq c c' lo hi := fun a _ _ => ⟨by rw [hn], by rw [hr]⟩

lemma HeapKeep.memEq {Hb h lo hi : ℕ} {c c' : Config} (hk : HeapKeep Hb h lo hi c c')
    {x y : ℕ} (hx : Hb ≤ x) (hy : y ≤ h) (hd : y ≤ lo ∨ hi ≤ x) : MemEq c c' x y :=
  fun a _ _ => hk a (by omega) (by omega) (by omega)

lemma HeapKeep.trans {Hb h lo hi : ℕ} {c c₁ c₂ : Config} (h₁ : HeapKeep Hb h lo hi c c₁)
    (h₂ : HeapKeep Hb h lo hi c₁ c₂) : HeapKeep Hb h lo hi c c₂ := fun a h1 h2 h3 =>
  ⟨(h₂ a h1 h2 h3).1.trans (h₁ a h1 h2 h3).1, (h₂ a h1 h2 h3).2.trans (h₁ a h1 h2 h3).2⟩

lemma heapKeep_of_eq {c c' : Config} (hn : c'.nmem = c.nmem) (hr : c'.rmem = c.rmem)
    (Hb h lo hi : ℕ) : HeapKeep Hb h lo hi c c' := fun a _ _ _ => ⟨by rw [hn], by rw [hr]⟩

/-- **A run lifted below the heap meets the frame conditions of the subprograms**: the frame
`Keep U Ws` of `Exec.lift`/`Exec.lift_trunc` (registers outside `U`, memory above `Ws` kept) with
`U` below `3000` and `Ws < Hb` keeps the registers of the driver and the whole heap. -/
lemma regKeep_of_keep {U : ℕ → Bool} {Ws : ℕ} {d d' : Config} (hk : Keep U Ws d d')
    (hU : ∀ r, 3000 ≤ r → U r = false) : RegKeep d d' := fun r hr => hk.nreg r (hU r hr)

lemma heapKeep_of_keep {U : ℕ → Bool} {Ws Hb : ℕ} {d d' : Config} (hk : Keep U Ws d d')
    (hW : Ws < Hb) (h lo hi : ℕ) : HeapKeep Hb h lo hi d d' := fun a h1 _ _ =>
  ⟨hk.nmem a (by omega), hk.rmem a (by omega)⟩

variable {D : Type*}

/-- **The specifications of the subprograms of the driver** (see the module docstring), with
the heap from `Hb`, the invariant `G`, the inputs `In` and outputs `Out` of the frames of the
subtrees, and the costs `tc` (test), `lc` (leaf), `sc` (split), `nc` (combination). -/
structure DSpec (I : Input) (W Hb : ℕ) (testS leafS splitS nodeS : Stmt) (G : Config → Prop)
    (In Out : NTree D → ℕ → ℕ → Config → Prop) (tc lc sc nc : NTree D → ℕ) : Prop where
  /-- `G` depends only on the registers `< 3000`, the real registers and the memory below
  `Hb`. -/
  g_stab : ∀ c c', G c → (∀ r < 3000, c'.nreg r = c.nreg r) → c'.rreg = c.rreg →
    MemEq c c' 0 Hb → G c'
  /-- `In τ d e` depends only on the memory `[d, e)`. -/
  in_stab : ∀ τ d e c c', In τ d e c → MemEq c c' d e → In τ d e c'
  /-- `Out τ d e` depends only on the memory `[d, e)`. -/
  out_stab : ∀ τ d e c c', Out τ d e c → MemEq c c' d e → Out τ d e c'
  /-- The test: `r2997 < 1` exactly at a leaf; nothing of the heap written. -/
  test : ∀ τ d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → In τ d e c →
    ∃ c' t, Exec I W testS c c' t ∧ t ≤ tc τ ∧ G c' ∧ RegKeep c c' ∧ HeapKeep Hb h h h c c' ∧
      c'.output = c.output ∧ (c'.nreg 2997 < 1 ↔ ∃ P, τ = .leaf P)
  /-- The leaf solver: the output in the frame, nothing else of the heap written. -/
  leaf : ∀ P d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → In (.leaf P) d e c →
    ∃ c' t, Exec I W leafS c c' t ∧ t ≤ lc (.leaf P) ∧ G c' ∧ RegKeep c c' ∧
      HeapKeep Hb h d e c c' ∧ c'.output = c.output ∧ Out (.leaf P) d e c'
  /-- The split: the inputs of the children at `[h + 5, el)` and `[el + 5, er)` above the heap
  top `h`, the ends in `r2998`, `r2999`; nothing of the heap written. -/
  split : ∀ l r d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → In (.node l r) d e c →
    ∃ c' t el er, Exec I W splitS c c' t ∧ t ≤ sc (.node l r) ∧ G c' ∧ RegKeep c c' ∧
      HeapKeep Hb h h h c c' ∧ c'.output = c.output ∧ c'.nreg 2998 = el ∧ c'.nreg 2999 = er ∧
      h + 5 ≤ el ∧ el + 5 ≤ er ∧ In l (h + 5) el c' ∧ In r (el + 5) er c'
  /-- The combination: from the input of the node and the outputs of the children (above the
  frame of the node, from `bl` on), the output in the frame of the node; nothing of the heap
  below `bl` written but the frame. -/
  node : ∀ l r d e bl el er c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3006 = bl + 5 → c.nreg 3007 = el → c.nreg 3008 = el + 5 → c.nreg 3009 = er →
    c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e → e ≤ bl → bl + 5 ≤ el → el + 5 ≤ er →
    In (.node l r) d e c → Out l (bl + 5) el c → Out r (el + 5) er c →
    ∃ c' t, Exec I W nodeS c c' t ∧ t ≤ nc (.node l r) ∧ G c' ∧ RegKeep c c' ∧
      HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧ Out (.node l r) d e c'

/-- **The cost of the driver**: the subprograms, plus `20` per leaf and `80` per node. -/
def dcost (tc lc sc nc : NTree D → ℕ) : NTree D → ℕ
  | .leaf P => tc (.leaf P) + lc (.leaf P) + 20
  | .node l r => tc (.node l r) + sc (.node l r) + nc (.node l r) + dcost tc lc sc nc l +
      dcost tc lc sc nc r + 80

variable {Hb : ℕ} {testS leafS splitS nodeS : Stmt} {G : Config → Prop}
  {In Out : NTree D → ℕ → ℕ → Config → Prop} {tc lc sc nc : NTree D → ℕ}

/-- The state before the traversal of a subtree `τ` in the frame `[b, e)` (next frame `nx`,
heap top `h`). -/
structure Pre (W Hb : ℕ) (G : Config → Prop) (In : NTree D → ℕ → ℕ → Config → Prop)
    (τ : NTree D) (b e nx h : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  g : G c
  r0 : c.nreg 3000 = 0
  r1 : c.nreg 3001 = 1
  top : c.nreg 3002 = b
  hp : c.nreg 3003 = h
  tag : c.nmem b = 0
  nxt : c.nmem (b + 1) = nx
  en : c.nmem (b + 2) = e
  lb : Hb ≤ b
  le1 : b + 5 ≤ e
  le2 : e ≤ h
  inp : In τ (b + 5) e c

/-- The state after the traversal of a subtree `τ` in the frame `[b, e)`. -/
structure Post (W Hb : ℕ) (G : Config → Prop) (Out : NTree D → ℕ → ℕ → Config → Prop)
    (τ : NTree D) (b e nx h : ℕ) (c c₁ : Config) : Prop where
  wb : WordsBounded W c₁
  g : G c₁
  r0 : c₁.nreg 3000 = 0
  r1 : c₁.nreg 3001 = 1
  top : c₁.nreg 3002 = nx
  hp : c₁.nreg 3003 = h
  keep : HeapKeep Hb h b e c c₁
  out : c₁.output = c.output
  res : Out τ (b + 5) e c₁

/-- `c₁` is reached from `c` by iterations of the loop `s` in `t₁` steps. -/
def Cont (I : Input) (W : ℕ) (s : Stmt) (c c₁ : Config) (t₁ : ℕ) : Prop :=
  ∀ c' t, Exec I W s c₁ c' t → Exec I W s c c' (t₁ + t)

/-- One iteration of the driver. -/
lemma cont_step {c c₁ : Config} {k : ℕ} (hc : 0 < c.nreg 3002) (h0 : c.nreg 3000 = 0)
    (e : Exec I W (body testS leafS splitS nodeS) c c₁ k) :
    Cont I W (driver testS leafS splitS nodeS) c c₁ (k + 2) := fun c' t et => by
  have := Exec.whileLtN_true (by rw [h0]; exact hc) e et
  unfold driver
  rwa [show k + 2 + t = k + 2 + t from rfl]

lemma Cont.trans {s : Stmt} {c c₁ c₂ : Config} {t₁ t₂ : ℕ} (h₁ : Cont I W s c c₁ t₁)
    (h₂ : Cont I W s c₁ c₂ t₂) : Cont I W s c c₂ (t₁ + t₂) := fun c' t et => by
  have := h₁ c' (t₂ + t) (h₂ c' t et)
  rwa [← Nat.add_assoc] at this

/-- The result of the traversal of a subtree. -/
def Trav (I : Input) (W Hb : ℕ) (testS leafS splitS nodeS : Stmt) (G : Config → Prop)
    (In Out : NTree D → ℕ → ℕ → Config → Prop) (tc lc sc nc : NTree D → ℕ) (τ : NTree D) :
    Prop :=
  ∀ b e nx h c, Pre W Hb G In τ b e nx h c →
    ∃ c₁ t₁, Cont I W (driver testS leafS splitS nodeS) c c₁ t₁ ∧
      t₁ ≤ dcost tc lc sc nc τ ∧ Post W Hb G Out τ b e nx h c c₁

/-- **The traversal of a leaf**: one iteration (the test, the leaf solver, the pop). -/
theorem trav_leaf (hS : DSpec I W Hb testS leafS splitS nodeS G In Out tc lc sc nc)
    (hHb : 0 < Hb) (P : Finset D) :
    Trav I W Hb testS leafS splitS nodeS G In Out tc lc sc nc (.leaf P) := by
  intro b e nx h c hp
  have hW : h ≤ W := hp.hp ▸ WordsBounded.nreg hp.wb 3003
  have lb := hp.lb; have le1 := hp.le1; have le2 := hp.le2
  obtain ⟨c1, t1, e1, ht1, p3010, p3004, p3005, pr1, pn1, prr1, prm1, po1⟩ :=
    peekB_exec (I := I) c hp.wb hp.top (by omega)
  rw [hp.tag] at p3010
  rw [hp.en] at p3005
  have R1 : ∀ r, (r < 3004 ∨ 3012 < r) → c1.nreg r = c.nreg r := fun r hr =>
    pr1 r (by omega) (by omega) (by omega) (by omega) (by omega)
  have g1 : G c1 := hS.g_stab c c1 hp.g (fun r hr => R1 r (by omega)) prr1
    (memEq_of_eq pn1 prm1 _ _)
  have i1 : In (.leaf P) (b + 5) e c1 := hS.in_stab _ _ _ c c1 hp.inp (memEq_of_eq pn1 prm1 _ _)
  have q3003 : c1.nreg 3003 = h := (R1 3003 (by omega)).trans hp.hp
  obtain ⟨c2, t2, e2, ht2, g2, rk2, hk2, po2, hf2⟩ :=
    hS.test _ (b + 5) e h c1 g1 e1.wb_right p3004 p3005 q3003 (by omega) le1 le2 i1
  have f2 : c2.nreg 2997 < c2.nreg 3001 := by
    rw [rk2 3001 (by omega), R1 3001 (by omega), hp.r1]; exact hf2.2 ⟨P, rfl⟩
  have i2 := hS.in_stab _ _ _ c1 c2 i1 (hk2.memEq (by omega) le2 (Or.inl le2))
  obtain ⟨c3, t3, e3, ht3, g3, rk3, hk3, po3, o3⟩ := hS.leaf P (b + 5) e h c2 g2 e2.wb_right
    (by rw [rk2 _ (by omega)]; exact p3004) (by rw [rk2 _ (by omega)]; exact p3005)
    (by rw [rk2 _ (by omega)]; exact q3003) (by omega) le1 le2 i2
  have t3002 : c3.nreg 3002 = b := by
    rw [rk3 _ (by omega), rk2 _ (by omega), R1 3002 (by omega), hp.top]
  obtain ⟨c4, t4, e4, ht4, p3002, pr4, pn4, prr4, prm4, po4⟩ :=
    popB_exec (I := I) c3 e3.wb_right t3002 (by omega)
  have eb : Exec I W (body testS leafS splitS nodeS) c c4 (t1 + (t2 + (t3 + t4 + 1) + 1)) :=
    Exec.seq e1 (Exec.ifLtN_true (by rw [p3010, R1 3001 (by omega), hp.r1]; omega)
      (Exec.seq e2 (Exec.ifLtN_true f2 (Exec.seq e3 e4))))
  have R : ∀ r, (r = 3000 ∨ r = 3001 ∨ r = 3003) → c4.nreg r = c.nreg r := fun r hr => by
    rw [pr4 r (by omega) (by omega) (by omega), rk3 r (by omega), rk2 r (by omega),
      R1 r (by omega)]
  have K : HeapKeep Hb h b e c c4 := fun a h1 h2 h3 => by
    have k3 := hk3 a h1 h2 (by omega)
    have k2 := hk2 a h1 h2 (Or.inl h2)
    rw [pn4, prm4, k3.1, k3.2, k2.1, k2.2, pn1, prm1]; exact ⟨rfl, rfl⟩
  refine ⟨c4, _, cont_step (by rw [hp.top]; omega) hp.r0 eb, ?_, ?_⟩
  · simp only [dcost]; omega
  refine ⟨e4.wb_right, hS.g_stab c3 c4 g3 (fun r hr => pr4 r (by omega) (by omega) (by omega))
    prr4 (memEq_of_eq pn4 prm4 _ _), (R 3000 (by omega)).trans hp.r0,
    (R 3001 (by omega)).trans hp.r1, ?_, (R 3003 (by omega)).trans hp.hp, K, ?_,
    hS.out_stab _ _ _ c3 c4 o3 (memEq_of_eq pn4 prm4 _ _)⟩
  · rw [p3002, (hk3 (b + 1) (by omega) (by omega) (by omega)).1,
      (hk2 (b + 1) (by omega) (by omega) (by omega)).1, pn1, hp.nxt]
  · rw [po4, po3, po2, po1]

/-- **The traversal of a node**: the expansion (the test, the split, the push), the traversals of
the two children, the combination. -/
theorem trav_node (hS : DSpec I W Hb testS leafS splitS nodeS G In Out tc lc sc nc)
    (hHb : 0 < Hb) (l r : NTree D) (ihl : Trav I W Hb testS leafS splitS nodeS G In Out tc lc sc nc l)
    (ihr : Trav I W Hb testS leafS splitS nodeS G In Out tc lc sc nc r) :
    Trav I W Hb testS leafS splitS nodeS G In Out tc lc sc nc (.node l r) := by
  intro b e nx h c hp
  have hW : h ≤ W := hp.hp ▸ WordsBounded.nreg hp.wb 3003
  have lb := hp.lb; have le1 := hp.le1; have le2 := hp.le2
  -- the expansion
  obtain ⟨c1, t1, e1, ht1, p3010, p3004, p3005, pr1, pn1, prr1, prm1, po1⟩ :=
    peekB_exec (I := I) c hp.wb hp.top (by omega)
  rw [hp.tag] at p3010
  rw [hp.en] at p3005
  have R1 : ∀ r, (r < 3004 ∨ 3012 < r) → c1.nreg r = c.nreg r := fun r hr =>
    pr1 r (by omega) (by omega) (by omega) (by omega) (by omega)
  have g1 : G c1 := hS.g_stab c c1 hp.g (fun r hr => R1 r (by omega)) prr1
    (memEq_of_eq pn1 prm1 _ _)
  have i1 : In (.node l r) (b + 5) e c1 :=
    hS.in_stab _ _ _ c c1 hp.inp (memEq_of_eq pn1 prm1 _ _)
  have q3003 : c1.nreg 3003 = h := (R1 3003 (by omega)).trans hp.hp
  obtain ⟨c2, t2, e2, ht2, g2, rk2, hk2, po2, hf2⟩ :=
    hS.test _ (b + 5) e h c1 g1 e1.wb_right p3004 p3005 q3003 (by omega) le1 le2 i1
  have f2 : ¬ c2.nreg 2997 < c2.nreg 3001 := by
    rw [rk2 3001 (by omega), R1 3001 (by omega), hp.r1]
    intro hlt
    obtain ⟨P, hP⟩ := hf2.1 hlt
    cases hP
  have i2 := hS.in_stab _ _ _ c1 c2 i1 (hk2.memEq (by omega) le2 (Or.inl le2))
  obtain ⟨c3, t3, el, er, e3, ht3, g3, rk3, hk3, po3, s2998, s2999, hel, her, il3, ir3⟩ :=
    hS.split l r (b + 5) e h c2 g2 e2.wb_right
      (by rw [rk2 _ (by omega)]; exact p3004) (by rw [rk2 _ (by omega)]; exact p3005)
      (by rw [rk2 _ (by omega)]; exact q3003) (by omega) le1 le2 i2
  have hW3 : er ≤ W := s2999 ▸ WordsBounded.nreg e3.wb_right 2999
  have t3002 : c3.nreg 3002 = b := by
    rw [rk3 _ (by omega), rk2 _ (by omega), R1 3002 (by omega), hp.top]
  have t3003 : c3.nreg 3003 = h := by rw [rk3 _ (by omega), rk2 _ (by omega)]; exact q3003
  obtain ⟨c4, t4, e4, ht4, p3002, p3003, pr4, pn4, prr4, prm4, po4⟩ :=
    pushB_exec (I := I) c3 e3.wb_right t3002 t3003 s2998 s2999 (by omega) (by omega)
      (by omega) (by omega)
  have eb1 : Exec I W (body testS leafS splitS nodeS) c c4 (t1 + (t2 + (t3 + t4 + 2) + 1)) :=
    Exec.seq e1 (Exec.ifLtN_true (by rw [p3010, R1 3001 (by omega), hp.r1]; omega)
      (Exec.seq e2 (Exec.ifLtN_false f2 (Exec.seq e3 e4))))
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ :=
    pushMem_vals (f := c3.nmem) (b := b) (h := h) (el := el) (er := er) (by omega) (by omega)
  rw [← pn4] at v1 v2 v3 v4 v5 v6 v7 v8 v9
  have M4 : ∀ a, (a < b ∨ a = b + 1 ∨ a = b + 2 ∨ (b + 4 < a ∧ a < h) ∨ (h + 2 < a ∧ a < el) ∨
      el + 2 < a) →
      c4.nmem a = c3.nmem a ∧ c4.rmem a = c3.rmem a := fun a ha =>
    ⟨by rw [pn4]; exact pushMem_keep ⟨by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega⟩, by rw [prm4]⟩
  have R4 : ∀ r, (r = 3000 ∨ r = 3001) → c4.nreg r = c.nreg r := fun r hr => by
    rw [pr4 r (by omega) (by omega) (by omega) (by omega), rk3 r (by omega), rk2 r (by omega),
      R1 r (by omega)]
  have g4 : G c4 := hS.g_stab c3 c4 g3
    (fun r hr => pr4 r (by omega) (by omega) (by omega) (by omega)) prr4
    (fun a _ ha => M4 a (by omega))
  -- the left child
  have il4 : In l (h + 5) el c4 := hS.in_stab _ _ _ c3 c4 il3 (fun a h1 h2 => M4 a (by omega))
  have pl : Pre W Hb G In l h el el er c4 := ⟨e4.wb_right, g4, (R4 3000 (by omega)).trans hp.r0,
    (R4 3001 (by omega)).trans hp.r1, p3002, p3003, v4, v5, v6, by omega, hel, by omega, il4⟩
  obtain ⟨c5, t5, C5, ht5, P5⟩ := ihl h el el er c4 pl
  -- the right child
  have ir5 : In r (el + 5) er c5 := hS.in_stab _ _ _ c4 c5
    (hS.in_stab _ _ _ c3 c4 ir3 (fun a h1 h2 => M4 a (by omega)))
    (P5.keep.memEq (by omega) le_rfl (Or.inr (by omega)))
  have pr : Pre W Hb G In r el er b er c5 := ⟨P5.wb, P5.g, P5.r0, P5.r1, P5.top, P5.hp,
    by rw [(P5.keep el (by omega) (by omega) (by omega)).1]; exact v7,
    by rw [(P5.keep (el + 1) (by omega) (by omega) (by omega)).1]; exact v8,
    by rw [(P5.keep (el + 2) (by omega) (by omega) (by omega)).1]; exact v9,
    by omega, her, le_rfl, ir5⟩
  obtain ⟨c6, t6, C6, ht6, P6⟩ := ihr el er b er c5 pr
  have M6 : ∀ a, Hb ≤ a → a < h → c6.nmem a = c4.nmem a ∧ c6.rmem a = c4.rmem a :=
    fun a h1 h2 => by
      have k6 := P6.keep a h1 (by omega) (Or.inl (by omega))
      have k5 := P5.keep a h1 (by omega) (Or.inl h2)
      rw [k6.1, k6.2, k5.1, k5.2]; exact ⟨rfl, rfl⟩
  -- the combination
  obtain ⟨c7, t7, e7, ht7, q3010, q3004, q3005, qr7, qn7, qrr7, qrm7, qo7⟩ :=
    peekB_exec (I := I) c6 P6.wb P6.top (by omega)
  have tag6 : c6.nmem b = 1 := by rw [(M6 b lb (by omega)).1]; exact v1
  have en6 : c6.nmem (b + 2) = e := by
    rw [(M6 (b + 2) (by omega) (by omega)).1, (M4 (b + 2) (by omega)).1,
      (hk3 (b + 2) (by omega) (by omega) (by omega)).1,
      (hk2 (b + 2) (by omega) (by omega) (by omega)).1, pn1, hp.en]
  rw [tag6] at q3010
  rw [en6] at q3005
  have R7 : ∀ r, (r < 3004 ∨ 3012 < r) → c7.nreg r = c6.nreg r := fun r hr =>
    qr7 r (by omega) (by omega) (by omega) (by omega) (by omega)
  have m73 : c7.nmem (b + 3) = h := by rw [qn7, (M6 (b + 3) (by omega) (by omega)).1]; exact v2
  have m74 : c7.nmem (b + 4) = el := by
    rw [qn7, (M6 (b + 4) (by omega) (by omega)).1]; exact v3
  obtain ⟨c8, t8, e8, ht8, s3006, s3007, s3008, s3009, sr8, sn8, srr8, srm8, so8⟩ :=
    coB_exec (I := I) c7 e7.wb_right ((R7 3002 (by omega)).trans P6.top) m73 m74 (by omega)
      (by omega) (by omega)
  have R8 : ∀ r, (r < 3004 ∨ 3012 < r) → c8.nreg r = c6.nreg r := fun r hr =>
    (sr8 r (by omega)).trans (R7 r hr)
  have g8 : G c8 := hS.g_stab c6 c8 P6.g (fun r hr => R8 r (by omega)) (srr8.trans qrr7)
    (memEq_of_eq (sn8.trans qn7) (srm8.trans qrm7) _ _)
  have inX : In (.node l r) (b + 5) e c8 := hS.in_stab _ _ _ c c8 hp.inp (fun a h1 h2 => by
    have m6 := M6 a (by omega) (by omega)
    have m4 := M4 a (by omega)
    have k3 := hk3 a (by omega) (by omega) (by omega)
    have k2 := hk2 a (by omega) (by omega) (by omega)
    rw [sn8, qn7, srm8, qrm7, m6.1, m6.2, m4.1, m4.2, k3.1, k3.2, k2.1, k2.2, pn1, prm1]
    exact ⟨rfl, rfl⟩)
  have outL : Out l (h + 5) el c8 := hS.out_stab _ _ _ c5 c8 P5.res (fun a h1 h2 => by
    have k6 := P6.keep a (by omega) (by omega) (Or.inl (by omega))
    rw [sn8, qn7, srm8, qrm7, k6.1, k6.2]; exact ⟨rfl, rfl⟩)
  have outR : Out r (el + 5) er c8 := hS.out_stab _ _ _ c6 c8 P6.res
    (memEq_of_eq (sn8.trans qn7) (srm8.trans qrm7) _ _)
  obtain ⟨c9, t9, e9, ht9, g9, rk9, hk9, po9, o9⟩ := hS.node l r (b + 5) e h el er c8 g8
    e8.wb_right (by rw [sr8 _ (by omega)]; exact q3004) (by rw [sr8 _ (by omega)]; exact q3005)
    s3006 s3007 s3008 (by rw [s3009, R7 _ (by omega)]; exact P6.hp)
    (by rw [R8 _ (by omega)]; exact P6.hp) (by omega) le1 le2 hel her inX outL outR
  obtain ⟨c10, t10, e10, ht10, u3003, u3002, ur10, un10, urr10, urm10, uo10⟩ :=
    coPost_exec (I := I) (b := b) c9 e9.wb_right (by rw [rk9 _ (by omega), R8 _ (by omega)]; exact P6.top)
      (by omega)
  have eb2 : Exec I W (body testS leafS splitS nodeS) c6 c10 (t7 + (t8 + (t9 + t10) + 2)) :=
    Exec.seq e7 (Exec.ifLtN_false (by rw [q3010, R7 3001 (by omega), P6.r1]; omega)
      (Exec.seq e8 (Exec.seq e9 e10)))
  have hb9 : ∀ a, Hb ≤ a → a < b + 5 → c9.nmem a = c8.nmem a := fun a h1 h2 =>
    (hk9 a h1 (by omega) (Or.inl h2)).1
  have R10 : ∀ r, (r = 3000 ∨ r = 3001) → c10.nreg r = c6.nreg r := fun r hr => by
    rw [ur10 r (by omega) (by omega) (by omega) (by omega), rk9 r (by omega), R8 r (by omega)]
  refine ⟨c10, _, (cont_step (by rw [hp.top]; omega) hp.r0 eb1).trans
    (C5.trans (C6.trans (cont_step (by rw [P6.top]; omega) P6.r0 eb2))), ?_, ?_⟩
  · simp only [dcost]; omega
  refine ⟨e10.wb_right, hS.g_stab c9 c10 g9
    (fun r hr => ur10 r (by omega) (by omega) (by omega) (by omega)) urr10
    (memEq_of_eq un10 urm10 _ _), (R10 3000 (by omega)).trans P6.r0,
    (R10 3001 (by omega)).trans P6.r1, ?_, ?_, ?_, ?_,
    hS.out_stab _ _ _ c9 c10 o9 (memEq_of_eq un10 urm10 _ _)⟩
  · rw [u3002, hb9 (b + 1) (by omega) (by omega), sn8, qn7,
      (M6 (b + 1) (by omega) (by omega)).1, (M4 (b + 1) (by omega)).1,
      (hk3 (b + 1) (by omega) (by omega) (by omega)).1,
      (hk2 (b + 1) (by omega) (by omega) (by omega)).1, pn1, hp.nxt]
  · rw [u3003, hb9 (b + 3) (by omega) (by omega), sn8]; exact m73
  · intro a h1 h2 h3
    have k9 := hk9 a h1 h2 (by omega)
    have m6 := M6 a h1 h2
    have m4 := M4 a (by omega)
    have k3 := hk3 a h1 h2 (Or.inl h2)
    have k2 := hk2 a h1 h2 (Or.inl h2)
    rw [un10, urm10, k9.1, k9.2, sn8, qn7, srm8, qrm7, m6.1, m6.2, m4.1, m4.2, k3.1, k3.2,
      k2.1, k2.2, pn1, prm1]
    exact ⟨rfl, rfl⟩
  · rw [uo10, po9, so8, qo7, P6.out, P5.out, po4, po3, po2, po1]

/-- **The traversal of every subtree.** -/
theorem trav (hS : DSpec I W Hb testS leafS splitS nodeS G In Out tc lc sc nc) (hHb : 0 < Hb) :
    ∀ τ : NTree D, Trav I W Hb testS leafS splitS nodeS G In Out tc lc sc nc τ
  | .leaf P => trav_leaf hS hHb P
  | .node l r => trav_node hS hHb l r (trav hS hHb l) (trav hS hHb r)

/-- **The driver** (see the module docstring): from the root frame `[Hb, e)` (tag `0`, next `0`,
end `e`) holding `In τ`, the heap top `h ≥ e`, `r3000 = 0`, `r3001 = 1`, the top `Hb > 0`, the
driver runs to `Out τ` in the root frame within `dcost τ + 2` steps, keeping `G`, the output,
the heap top and the heap outside the root frame. -/
theorem drive (hS : DSpec I W Hb testS leafS splitS nodeS G In Out tc lc sc nc) (hHb : 0 < Hb)
    (τ : NTree D) {e h : ℕ} (c : Config) (hc : WordsBounded W c) (hg : G c)
    (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1) (r2 : c.nreg 3002 = Hb)
    (r3 : c.nreg 3003 = h) (m0 : c.nmem Hb = 0) (m1 : c.nmem (Hb + 1) = 0)
    (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h) (hin : In τ (Hb + 5) e c) :
    ∃ c' t, Exec I W (driver testS leafS splitS nodeS) c c' t ∧ t ≤ dcost tc lc sc nc τ + 2 ∧
      G c' ∧ Out τ (Hb + 5) e c' ∧ c'.nreg 3002 = 0 ∧ c'.nreg 3003 = h ∧
      HeapKeep Hb h Hb e c c' ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, C, ht, P⟩ :=
    trav hS hHb τ Hb e 0 h c ⟨hc, hg, r0, r1, r2, r3, m0, m1, m2, le_rfl, he, hh, hin⟩
  have ef : Exec I W (driver testS leafS splitS nodeS) c₁ c₁ 2 :=
    Exec.whileLtN_false (by rw [P.r0, P.top]; omega) P.wb
  exact ⟨c₁, t₁ + 2, C c₁ 2 ef, by omega, P.g, P.res, P.top, P.hp, P.keep, P.out⟩

end Driver

end NegSSSP

end PlanarFlow
