module

public import PlanarFlow.NegSSSP.Driver

/-!
# The explicit-stack driver over labelled binary trees

`PlanarFlow.NegSSSP.Driver.driver testS leafS splitS nodeS` (one loop over a stack of frames in
memory) traverses a decomposition in post-order; `PlanarFlow.NegSSSP.Driver.drive` proves it
for the trees `NTree D` of the negative-length recursion, whose nodes carry no data. The
max-flow recursion runs on `ADec M`, whose nodes carry a separator, with holes and a rotation
along the calls. This file proves **the same driver program** on trees with labels on the leaves
and on the nodes (`LTree A B`), so that the frame predicates `In`, `Out` can depend on the label
of every node.

The subprograms may now also write the registers above `3012` (`DRegKeep`: only the registers
`3000 … 3012` of the driver must be kept), so that programs with registers in other bands (e.g.
the `lin` programs, registers `62xx`) run inside them unchanged.

* `LTree`, `DSpecL` (the specifications of the four subprograms, as `DSpec` with labels),
  `dcostL` (the subprograms plus `20` per leaf and `80` per node).
* **`driveL`**: from the root frame `[Hb, e)` holding `In τ`, the driver runs to `Out τ` in the
  root frame within `dcostL τ + 2` steps (same statement as `Driver.drive`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace PlanarFlow

namespace BKMNW

/-- **A binary tree with labels** on the leaves (`A`) and on the nodes (`B`). -/
inductive LTree (A B : Type*) where
  | leaf (a : A)
  | node (l r : LTree A B) (b : B)

namespace MfDrv

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP.Driver

variable {I : Input} {W : ℕ}

/-- The registers `3000 … 3012` of the driver are kept. -/
def DRegKeep (c c' : Config) : Prop := ∀ r, 3000 ≤ r → r ≤ 3012 → c'.nreg r = c.nreg r

variable {A B : Type*}

/-- **The specifications of the subprograms of the driver on labelled trees** (as
`NegSSSP.Driver.DSpec`; the registers above `3012` free). -/
structure DSpecL (I : Input) (W Hb : ℕ) (testS leafS splitS nodeS : Stmt) (G : Config → Prop)
    (In Out : LTree A B → ℕ → ℕ → Config → Prop) (tc lc sc nc : LTree A B → ℕ) : Prop where
  g_stab : ∀ c c', G c → (∀ r < 3000, c'.nreg r = c.nreg r) → c'.rreg = c.rreg →
    MemEq c c' 0 Hb → G c'
  in_stab : ∀ τ d e c c', In τ d e c → MemEq c c' d e → In τ d e c'
  out_stab : ∀ τ d e c c', Out τ d e c → MemEq c c' d e → Out τ d e c'
  test : ∀ τ d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → In τ d e c →
    ∃ c' t, Exec I W testS c c' t ∧ t ≤ tc τ ∧ G c' ∧ DRegKeep c c' ∧ HeapKeep Hb h h h c c' ∧
      c'.output = c.output ∧ (c'.nreg 2997 < 1 ↔ ∃ a, τ = .leaf a)
  leaf : ∀ a d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → In (.leaf a) d e c →
    ∃ c' t, Exec I W leafS c c' t ∧ t ≤ lc (.leaf a) ∧ G c' ∧ DRegKeep c c' ∧
      HeapKeep Hb h d e c c' ∧ c'.output = c.output ∧ Out (.leaf a) d e c'
  split : ∀ l r b d e h c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → In (.node l r b) d e c →
    ∃ c' t el er, Exec I W splitS c c' t ∧ t ≤ sc (.node l r b) ∧ G c' ∧ DRegKeep c c' ∧
      HeapKeep Hb h h h c c' ∧ c'.output = c.output ∧ c'.nreg 2998 = el ∧ c'.nreg 2999 = er ∧
      h + 5 ≤ el ∧ el + 5 ≤ er ∧ In l (h + 5) el c' ∧ In r (el + 5) er c'
  node : ∀ l r b d e bl el er c, G c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3006 = bl + 5 → c.nreg 3007 = el → c.nreg 3008 = el + 5 → c.nreg 3009 = er →
    c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e → e ≤ bl → bl + 5 ≤ el → el + 5 ≤ er →
    In (.node l r b) d e c → Out l (bl + 5) el c → Out r (el + 5) er c →
    ∃ c' t, Exec I W nodeS c c' t ∧ t ≤ nc (.node l r b) ∧ G c' ∧ DRegKeep c c' ∧
      HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧ Out (.node l r b) d e c'

/-- **The cost of the driver**: the subprograms, plus `20` per leaf and `80` per node. -/
def dcostL (tc lc sc nc : LTree A B → ℕ) : LTree A B → ℕ
  | .leaf a => tc (.leaf a) + lc (.leaf a) + 20
  | .node l r b => tc (.node l r b) + sc (.node l r b) + nc (.node l r b) +
      dcostL tc lc sc nc l + dcostL tc lc sc nc r + 80

variable {Hb : ℕ} {testS leafS splitS nodeS : Stmt} {G : Config → Prop}
  {In Out : LTree A B → ℕ → ℕ → Config → Prop} {tc lc sc nc : LTree A B → ℕ}

/-- The state before the traversal of a subtree. -/
structure PreL (W Hb : ℕ) (G : Config → Prop) (In : LTree A B → ℕ → ℕ → Config → Prop)
    (τ : LTree A B) (b e nx h : ℕ) (c : Config) : Prop where
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

/-- The state after the traversal of a subtree. -/
structure PostL (W Hb : ℕ) (G : Config → Prop) (Out : LTree A B → ℕ → ℕ → Config → Prop)
    (τ : LTree A B) (b e nx h : ℕ) (c c₁ : Config) : Prop where
  wb : WordsBounded W c₁
  g : G c₁
  r0 : c₁.nreg 3000 = 0
  r1 : c₁.nreg 3001 = 1
  top : c₁.nreg 3002 = nx
  hp : c₁.nreg 3003 = h
  keep : HeapKeep Hb h b e c c₁
  out : c₁.output = c.output
  res : Out τ (b + 5) e c₁

/-- The result of the traversal of a subtree. -/
def TravL (I : Input) (W Hb : ℕ) (testS leafS splitS nodeS : Stmt) (G : Config → Prop)
    (In Out : LTree A B → ℕ → ℕ → Config → Prop) (tc lc sc nc : LTree A B → ℕ)
    (τ : LTree A B) : Prop :=
  ∀ b e nx h c, PreL W Hb G In τ b e nx h c →
    ∃ c₁ t₁, Cont I W (driver testS leafS splitS nodeS) c c₁ t₁ ∧
      t₁ ≤ dcostL tc lc sc nc τ ∧ PostL W Hb G Out τ b e nx h c c₁

/-- **The traversal of a leaf.** -/
theorem travL_leaf (hS : DSpecL I W Hb testS leafS splitS nodeS G In Out tc lc sc nc)
    (hHb : 0 < Hb) (a : A) :
    TravL I W Hb testS leafS splitS nodeS G In Out tc lc sc nc (.leaf a) := by
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
  have i1 : In (.leaf a) (b + 5) e c1 := hS.in_stab _ _ _ c c1 hp.inp (memEq_of_eq pn1 prm1 _ _)
  have q3003 : c1.nreg 3003 = h := (R1 3003 (by omega)).trans hp.hp
  obtain ⟨c2, t2, e2, ht2, g2, rk2, hk2, po2, hf2⟩ :=
    hS.test _ (b + 5) e h c1 g1 e1.wb_right p3004 p3005 q3003 (by omega) le1 le2 i1
  have f2 : c2.nreg 2997 < c2.nreg 3001 := by
    rw [rk2 3001 (by omega) (by omega), R1 3001 (by omega), hp.r1]; exact hf2.2 ⟨a, rfl⟩
  have i2 := hS.in_stab _ _ _ c1 c2 i1 (hk2.memEq (by omega) le2 (Or.inl le2))
  obtain ⟨c3, t3, e3, ht3, g3, rk3, hk3, po3, o3⟩ := hS.leaf a (b + 5) e h c2 g2 e2.wb_right
    (by rw [rk2 _ (by omega) (by omega)]; exact p3004)
    (by rw [rk2 _ (by omega) (by omega)]; exact p3005)
    (by rw [rk2 _ (by omega) (by omega)]; exact q3003) (by omega) le1 le2 i2
  have t3002 : c3.nreg 3002 = b := by
    rw [rk3 _ (by omega) (by omega), rk2 _ (by omega) (by omega), R1 3002 (by omega), hp.top]
  obtain ⟨c4, t4, e4, ht4, p3002, pr4, pn4, prr4, prm4, po4⟩ :=
    popB_exec (I := I) c3 e3.wb_right t3002 (by omega)
  have eb : Exec I W (body testS leafS splitS nodeS) c c4 (t1 + (t2 + (t3 + t4 + 1) + 1)) :=
    Exec.seq e1 (Exec.ifLtN_true (by rw [p3010, R1 3001 (by omega), hp.r1]; omega)
      (Exec.seq e2 (Exec.ifLtN_true f2 (Exec.seq e3 e4))))
  have R : ∀ r, (r = 3000 ∨ r = 3001 ∨ r = 3003) → c4.nreg r = c.nreg r := fun r hr => by
    rw [pr4 r (by omega) (by omega) (by omega), rk3 r (by omega) (by omega),
      rk2 r (by omega) (by omega), R1 r (by omega)]
  have K : HeapKeep Hb h b e c c4 := fun a' h1 h2 h3 => by
    have k3 := hk3 a' h1 h2 (by omega)
    have k2 := hk2 a' h1 h2 (Or.inl h2)
    rw [pn4, prm4, k3.1, k3.2, k2.1, k2.2, pn1, prm1]; exact ⟨rfl, rfl⟩
  refine ⟨c4, _, cont_step (by rw [hp.top]; omega) hp.r0 eb, ?_, ?_⟩
  · simp only [dcostL]; omega
  refine ⟨e4.wb_right, hS.g_stab c3 c4 g3 (fun r hr => pr4 r (by omega) (by omega) (by omega))
    prr4 (memEq_of_eq pn4 prm4 _ _), (R 3000 (by omega)).trans hp.r0,
    (R 3001 (by omega)).trans hp.r1, ?_, (R 3003 (by omega)).trans hp.hp, K, ?_,
    hS.out_stab _ _ _ c3 c4 o3 (memEq_of_eq pn4 prm4 _ _)⟩
  · rw [p3002, (hk3 (b + 1) (by omega) (by omega) (by omega)).1,
      (hk2 (b + 1) (by omega) (by omega) (by omega)).1, pn1, hp.nxt]
  · rw [po4, po3, po2, po1]

/-- **The traversal of a node.** -/
theorem travL_node (hS : DSpecL I W Hb testS leafS splitS nodeS G In Out tc lc sc nc)
    (hHb : 0 < Hb) (l r : LTree A B) (bb : B)
    (ihl : TravL I W Hb testS leafS splitS nodeS G In Out tc lc sc nc l)
    (ihr : TravL I W Hb testS leafS splitS nodeS G In Out tc lc sc nc r) :
    TravL I W Hb testS leafS splitS nodeS G In Out tc lc sc nc (.node l r bb) := by
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
  have i1 : In (.node l r bb) (b + 5) e c1 :=
    hS.in_stab _ _ _ c c1 hp.inp (memEq_of_eq pn1 prm1 _ _)
  have q3003 : c1.nreg 3003 = h := (R1 3003 (by omega)).trans hp.hp
  obtain ⟨c2, t2, e2, ht2, g2, rk2, hk2, po2, hf2⟩ :=
    hS.test _ (b + 5) e h c1 g1 e1.wb_right p3004 p3005 q3003 (by omega) le1 le2 i1
  have f2 : ¬ c2.nreg 2997 < c2.nreg 3001 := by
    rw [rk2 3001 (by omega) (by omega), R1 3001 (by omega), hp.r1]
    intro hlt
    obtain ⟨a, hP⟩ := hf2.1 hlt
    cases hP
  have i2 := hS.in_stab _ _ _ c1 c2 i1 (hk2.memEq (by omega) le2 (Or.inl le2))
  obtain ⟨c3, t3, el, er, e3, ht3, g3, rk3, hk3, po3, s2998, s2999, hel, her, il3, ir3⟩ :=
    hS.split l r bb (b + 5) e h c2 g2 e2.wb_right
      (by rw [rk2 _ (by omega) (by omega)]; exact p3004)
      (by rw [rk2 _ (by omega) (by omega)]; exact p3005)
      (by rw [rk2 _ (by omega) (by omega)]; exact q3003) (by omega) le1 le2 i2
  have hW3 : er ≤ W := s2999 ▸ WordsBounded.nreg e3.wb_right 2999
  have t3002 : c3.nreg 3002 = b := by
    rw [rk3 _ (by omega) (by omega), rk2 _ (by omega) (by omega), R1 3002 (by omega), hp.top]
  have t3003 : c3.nreg 3003 = h := by
    rw [rk3 _ (by omega) (by omega), rk2 _ (by omega) (by omega)]; exact q3003
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
    rw [pr4 r (by omega) (by omega) (by omega) (by omega), rk3 r (by omega) (by omega),
      rk2 r (by omega) (by omega), R1 r (by omega)]
  have g4 : G c4 := hS.g_stab c3 c4 g3
    (fun r hr => pr4 r (by omega) (by omega) (by omega) (by omega)) prr4
    (fun a _ ha => M4 a (by omega))
  have il4 : In l (h + 5) el c4 := hS.in_stab _ _ _ c3 c4 il3 (fun a h1 h2 => M4 a (by omega))
  have pl : PreL W Hb G In l h el el er c4 := ⟨e4.wb_right, g4, (R4 3000 (by omega)).trans hp.r0,
    (R4 3001 (by omega)).trans hp.r1, p3002, p3003, v4, v5, v6, by omega, hel, by omega, il4⟩
  obtain ⟨c5, t5, C5, ht5, P5⟩ := ihl h el el er c4 pl
  have ir5 : In r (el + 5) er c5 := hS.in_stab _ _ _ c4 c5
    (hS.in_stab _ _ _ c3 c4 ir3 (fun a h1 h2 => M4 a (by omega)))
    (P5.keep.memEq (by omega) le_rfl (Or.inr (by omega)))
  have pr : PreL W Hb G In r el er b er c5 := ⟨P5.wb, P5.g, P5.r0, P5.r1, P5.top, P5.hp,
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
  have inX : In (.node l r bb) (b + 5) e c8 := hS.in_stab _ _ _ c c8 hp.inp (fun a h1 h2 => by
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
  obtain ⟨c9, t9, e9, ht9, g9, rk9, hk9, po9, o9⟩ := hS.node l r bb (b + 5) e h el er c8 g8
    e8.wb_right (by rw [sr8 _ (by omega)]; exact q3004) (by rw [sr8 _ (by omega)]; exact q3005)
    s3006 s3007 s3008 (by rw [s3009, R7 _ (by omega)]; exact P6.hp)
    (by rw [R8 _ (by omega)]; exact P6.hp) (by omega) le1 le2 hel her inX outL outR
  obtain ⟨c10, t10, e10, ht10, u3003, u3002, ur10, un10, urr10, urm10, uo10⟩ :=
    coPost_exec (I := I) (b := b) c9 e9.wb_right
      (by rw [rk9 _ (by omega) (by omega), R8 _ (by omega)]; exact P6.top) (by omega)
  have eb2 : Exec I W (body testS leafS splitS nodeS) c6 c10 (t7 + (t8 + (t9 + t10) + 2)) :=
    Exec.seq e7 (Exec.ifLtN_false (by rw [q3010, R7 3001 (by omega), P6.r1]; omega)
      (Exec.seq e8 (Exec.seq e9 e10)))
  have hb9 : ∀ a, Hb ≤ a → a < b + 5 → c9.nmem a = c8.nmem a := fun a h1 h2 =>
    (hk9 a h1 (by omega) (Or.inl h2)).1
  have R10 : ∀ r, (r = 3000 ∨ r = 3001) → c10.nreg r = c6.nreg r := fun r hr => by
    rw [ur10 r (by omega) (by omega) (by omega) (by omega), rk9 r (by omega) (by omega),
      R8 r (by omega)]
  refine ⟨c10, _, (cont_step (by rw [hp.top]; omega) hp.r0 eb1).trans
    (C5.trans (C6.trans (cont_step (by rw [P6.top]; omega) P6.r0 eb2))), ?_, ?_⟩
  · simp only [dcostL]; omega
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
theorem travL (hS : DSpecL I W Hb testS leafS splitS nodeS G In Out tc lc sc nc)
    (hHb : 0 < Hb) : ∀ τ : LTree A B, TravL I W Hb testS leafS splitS nodeS G In Out tc lc sc nc τ
  | .leaf a => travL_leaf hS hHb a
  | .node l r b => travL_node hS hHb l r b (travL hS hHb l) (travL hS hHb r)

/-- **The driver on labelled trees**: from the root frame `[Hb, e)` (tag `0`, next `0`, end
`e`) holding `In τ`, the heap top `h ≥ e`, `r3000 = 0`, `r3001 = 1`, the top `Hb > 0`, the
driver runs to `Out τ` in the root frame within `dcostL τ + 2` steps, keeping `G`, the output,
the heap top and the heap outside the root frame. -/
theorem driveL (hS : DSpecL I W Hb testS leafS splitS nodeS G In Out tc lc sc nc)
    (hHb : 0 < Hb) (τ : LTree A B) {e h : ℕ} (c : Config) (hc : WordsBounded W c) (hg : G c)
    (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1) (r2 : c.nreg 3002 = Hb)
    (r3 : c.nreg 3003 = h) (m0 : c.nmem Hb = 0) (m1 : c.nmem (Hb + 1) = 0)
    (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h) (hin : In τ (Hb + 5) e c) :
    ∃ c' t, Exec I W (driver testS leafS splitS nodeS) c c' t ∧ t ≤ dcostL tc lc sc nc τ + 2 ∧
      G c' ∧ Out τ (Hb + 5) e c' ∧ c'.nreg 3002 = 0 ∧ c'.nreg 3003 = h ∧
      HeapKeep Hb h Hb e c c' ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, C, ht, P⟩ :=
    travL hS hHb τ Hb e 0 h c ⟨hc, hg, r0, r1, r2, r3, m0, m1, m2, le_rfl, he, hh, hin⟩
  have ef : Exec I W (driver testS leafS splitS nodeS) c₁ c₁ 2 :=
    Exec.whileLtN_false (by rw [P.r0, P.top]; omega) P.wb
  exact ⟨c₁, t₁ + 2, C c₁ 2 ef, by omega, P.g, P.res, P.top, P.hp, P.keep, P.out⟩

end MfDrv

end BKMNW

end PlanarFlow
