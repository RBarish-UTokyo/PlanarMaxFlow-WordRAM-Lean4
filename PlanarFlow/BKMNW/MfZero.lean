module

public import PlanarFlow.BKMNW.MfDrvO

/-!
# The zero-memory invariant through the max-flow driver

The in-place call `negCallZ` of the machine's negative-length shortest paths
(`PlanarFlow/BKMNW/NegCallZ.lean`) needs the natural memory `≤ Wz` to be zero when it starts, and
restores it. Here this invariant **`MemZ Wz`** is threaded through the driver, as its invariant
`G` of `MfSpecRC`:

* the test `mtProg`, the leaf solver `mlProg` and the split `splitS sepP` keep the memory below
  the heap top (their specifications hold with `Hb = 0`; `SepPSpec` already keeps the memory below
  the scratch base `Sb > h`, so **no extra clause is needed for `sepP`**), hence keep `MemZ Wz`
  when `Wz < Hb`;
* **`NodeSpecFC'`** (the combination's field with `MemZ Wz` in and out), **`StepPSpecC'`**
  (`StepPSpecC` with the extra hypotheses `Wz < d` and `MemZ Wz c`), **`nodeSF_specC'`**;
* **`mfSpecR_frameO'`**, **`mfDriveFrameO'`**: the driver for `arunLO` from a start with
  `MemZ Wz` and `Wz < Hb`, ending with `MemZ Wz` again.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs NegSSSP.Driver

universe w

/-- **The zero-memory invariant**: the natural memory `≤ Wz` is zero. -/
def MemZ (Wz : ℕ) (c : Config) : Prop := ∀ a ≤ Wz, c.nmem a = 0

lemma MemZ.of_eq {Wz : ℕ} {c c' : Config} (h : MemZ Wz c)
    (hk : ∀ a ≤ Wz, c'.nmem a = c.nmem a) : MemZ Wz c' := fun a ha => by rw [hk a ha, h a ha]

/-- A heap kept from `0` keeps the zero memory below the kept part. -/
lemma MemZ.of_heapKeep {Wz h lo hi : ℕ} {c c' : Config} (hz : MemZ Wz c)
    (hk : HeapKeep 0 h lo hi c c') (h1 : Wz < h) (h2 : Wz < lo) : MemZ Wz c' :=
  hz.of_eq fun a ha => (hk a (Nat.zero_le a) (by omega) (Or.inl (by omega))).1

lemma HeapKeep.of_zero {Hb h lo hi : ℕ} {c c' : Config} (hk : HeapKeep 0 h lo hi c c') :
    HeapKeep Hb h lo hi c c' := fun a _ h2 h3 => hk a (Nat.zero_le a) h2 h3

section Gen

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

section Generic

variable (M) in
/-- **The combination's field with the zero-memory invariant, for any frame predicates**
(`MfSpecRC.node` with `G = MemZ Wz`). -/
def NodeFieldZ (cf : CFlow M) (I : Input) (W Hb Wz : ℕ) (nodeS : Stmt)
    (FIn : MCall M → ℕ → ℕ → Config → Prop) (FOut : FOutT M) (nc rS rN : MCall M → ℕ) : Prop :=
  ∀ l r π Hs σ d e bl el er c, MemZ Wz c → WordsBounded W c → c.nreg 3004 = d →
    c.nreg 3005 = e → c.nreg 3006 = bl + 5 → c.nreg 3007 = el → c.nreg 3008 = el + 5 →
    c.nreg 3009 = er → c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e → e ≤ bl → bl + 5 ≤ el →
    el + 5 ≤ er → bl + rS (.node l r π, Hs, σ) + rN (.node l r π, Hs, σ) ≤ W →
    FIn (.node l r π, Hs, σ) d e c →
    FOut (chL M l r π Hs σ) (cf (chL M l r π Hs σ)) (bl + 5) el c →
    FOut (chR M l r π Hs σ) (cf (chR M l r π Hs σ)) (el + 5) er c →
    ∃ c' t, Exec I W nodeS c c' t ∧ t ≤ nc (.node l r π, Hs, σ) ∧ MemZ Wz c' ∧
      DRegKeep c c' ∧ HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧
      FOut (.node l r π, Hs, σ) (cf (.node l r π, Hs, σ)) d e c'

/-- **The zero-memory invariant for any frame predicates** (`FInL`, or a later `FInLX` with a
decomposition record): if the test, the leaf solver and the split meet their fields of `MfSpecRC`
with heap base `0` and `G = True` (they keep all the memory below the heap top), and the
combination meets `NodeFieldZ`, then the four programs meet `MfSpecRC` with `G = MemZ Wz` for
any heap base `Hb > Wz`. The fields of `h0` other than `test`, `leaf`, `split` (and the stability
of `FIn`, `FOut`) are not used: its combination program `nodeS₀` is arbitrary. -/
theorem mfSpecRC_memZ {cf : CFlow M} {I : Input} {W Hb Wz : ℕ}
    {testS leafS splitS nodeS nodeS₀ : Stmt} {FIn : MCall M → ℕ → ℕ → Config → Prop}
    {FOut : FOutT M} {tc lc sc nc nc₀ rL rS rN rN₀ : MCall M → ℕ}
    (h0 : MfSpecRC M cf I W 0 testS leafS splitS nodeS₀ (fun _ => True) FIn FOut tc lc sc nc₀ rL
      rS rN₀) (hWz : Wz < Hb)
    (hnode : NodeFieldZ M cf I W Hb Wz nodeS FIn FOut nc rS rN) :
    MfSpecRC M cf I W Hb testS leafS splitS nodeS (MemZ Wz) FIn FOut tc lc sc nc rL rS rN where
  g_stab c c' hg _ _ hm := hg.of_eq fun a ha => (hm a (Nat.zero_le a) (by omega)).1
  in_stab := h0.in_stab
  out_stab := h0.out_stab
  test x d e h c hg hc r4 r5 r3 h1 h2 h3 hin := by
    obtain ⟨c', t, ex, ht, -, dk, hk, ho, hf⟩ :=
      h0.test x d e h c trivial hc r4 r5 r3 (by omega) h2 h3 hin
    exact ⟨c', t, ex, ht, hg.of_heapKeep hk (by omega) (by omega), dk, HeapKeep.of_zero hk,
      ho, hf⟩
  leaf Q Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hrm hin := by
    obtain ⟨c', t, ex, ht, -, dk, hk, ho, hf⟩ :=
      h0.leaf Q Hs σ d e h c trivial hc r4 r5 r3 (by omega) h2 h3 hrm hin
    exact ⟨c', t, ex, ht, hg.of_heapKeep hk (by omega) (by omega), dk, HeapKeep.of_zero hk,
      ho, hf⟩
  split l r π Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hrm hin := by
    obtain ⟨c', t, el, er, ex, ht, -, dk, hk, ho, s8, s9, e1, e2, e3, il, ir⟩ :=
      h0.split l r π Hs σ d e h c trivial hc r4 r5 r3 (by omega) h2 h3 hrm hin
    exact ⟨c', t, el, er, ex, ht, hg.of_heapKeep hk (by omega) (by omega), dk,
      HeapKeep.of_zero hk, ho, s8, s9, e1, e2, e3, il, ir⟩
  node := hnode

end Generic

section FrameZ

variable (M) in
/-- **The specification of the combination with the zero-memory invariant** (`NodeSpecFC` with
`MemZ Wz` before and after). -/
def NodeSpecFC' (cf : CFlow M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Hb Wz : ℕ) (nodeS : Stmt) (nc rS rN : MCall M → ℕ) :
    Prop :=
  ∀ l r π Hs σ d e bl el er c, MemZ Wz c → WordsBounded W c → c.nreg 3004 = d →
    c.nreg 3005 = e → c.nreg 3006 = bl + 5 → c.nreg 3007 = el → c.nreg 3008 = el + 5 →
    c.nreg 3009 = er → c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e → e ≤ bl → bl + 5 ≤ el →
    el + 5 ≤ er → bl + rS (.node l r π, Hs, σ) + rN (.node l r π, Hs, σ) ≤ W →
    FInL M Reach gid u S T Z (.node l r π, Hs, σ) d e c →
    FOutL M gid u S T Z (chL M l r π Hs σ) (cf (chL M l r π Hs σ)) (bl + 5) el c →
    FOutL M gid u S T Z (chR M l r π Hs σ) (cf (chR M l r π Hs σ)) (el + 5) er c →
    ∃ c' t, Exec I W nodeS c c' t ∧ t ≤ nc (.node l r π, Hs, σ) ∧ MemZ Wz c' ∧
      DRegKeep c c' ∧ HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧
      FOutL M gid u S T Z (.node l r π, Hs, σ) (cf (.node l r π, Hs, σ)) d e c'

variable {NO : MOFam M} {cf : CFlow M} {Reach : MCall M → Prop} {gid : D → ℕ} {u : D → ℤ}
  {S T : Finset V} {Z : ℕ} {I : Input} {W Hb Wz : ℕ} {sepP nodeS : Stmt} {sT : ℕ → ℕ}
  {sR : ℕ → ℕ → ℕ} {nc rN : MCall M → ℕ}

/-- **`mfSpecR_frameO` with the zero-memory invariant** `G = MemZ Wz` (`Wz < Hb`): the test, the
leaf solver and the split keep the memory below the heap top, so they keep `MemZ Wz`; the
combination is the hypothesis `NodeSpecFC'`. -/
theorem mfSpecR_frameO' (hsep : SepPSpec M Reach gid u S T Z I W sepP sT sR)
    (hReach : ∀ l r π Hs σ, Reach ((.node l r π, Hs, σ) : MCall M) →
      Reach (chL M l r π Hs σ) ∧ Reach (chR M l r π Hs σ)) (hZ : 2 * Z ≤ W) (hWz : Wz < Hb)
    (hnode : NodeSpecFC' M (cflowO M NO u S T) Reach gid u S T Z I W Hb Wz nodeS nc (rSp M sR)
      rN) :
    MfSpecRC M (cflowO M NO u S T) I W Hb mtProg mlProg (splitS sepP) nodeS (MemZ Wz)
      (FInL M Reach gid u S T Z) (FOutL M gid u S T Z) (fun _ => 3)
      (fun x => 20 * (pdarts M x.1.piece x.2.1).card + 17) (scp M sT) nc (fun _ => 0)
      (rSp M sR) rN where
  g_stab c c' hg _ _ hm := hg.of_eq fun a ha => (hm a (Nat.zero_le a) (by omega)).1
  in_stab _ _ _ _ _ h hm := h.stab hm
  out_stab _ _ _ _ _ _ h hm := h.stab hm
  test x d e h c hg hc r4 r5 r3 h1 h2 h3 hin := by
    obtain ⟨c', t, ex, ht, -, dk, hk, ho, hf⟩ :=
      mtProg_spec (Hb := 0) x d e h c trivial hc r4 r5 r3 (by omega) h2 h3 hin
    exact ⟨c', t, ex, ht, hg.of_heapKeep hk (by omega) (by omega), dk, HeapKeep.of_zero hk,
      ho, hf⟩
  leaf Q Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 _ hin := by
    rw [cflowO_leaf (planeOracles fun X => frRef X)]
    obtain ⟨c', t, ex, ht, -, dk, hk, ho, hf⟩ :=
      mlProg_spec (Hb := 0) _ hZ Q Hs σ d e h c trivial hc r4 r5 r3 (by omega) h2 h3 hin
    exact ⟨c', t, ex, ht, hg.of_heapKeep hk (by omega) (by omega), dk, HeapKeep.of_zero hk,
      ho, hf⟩
  split l r π Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hrm hin := by
    obtain ⟨c', t, el, er, ex, ht, -, dk, hk, ho, s8, s9, e1, e2, e3, il, ir⟩ :=
      mfSplit_spec (Hb := 0) hsep hReach l r π Hs σ d e h c trivial hc r4 r5 r3 (by omega) h2
        h3 hrm hin
    exact ⟨c', t, el, er, ex, ht, hg.of_heapKeep hk (by omega) (by omega), dk,
      HeapKeep.of_zero hk, ho,
      s8, s9, e1, e2, e3, il, ir⟩
  node := hnode

/-- **`mfDriveFrameO` with the zero-memory invariant**: from a start with `MemZ Wz` (`Wz < Hb`),
the driver ends with `FOutL` of `arunLO` and `MemZ Wz` again, within `mcost + 2` steps. -/
theorem mfDriveFrameO' (hsep : SepPSpec M Reach gid u S T Z I W sepP sT sR)
    (hReach : ∀ l r π Hs σ, Reach ((.node l r π, Hs, σ) : MCall M) →
      Reach (chL M l r π Hs σ) ∧ Reach (chR M l r π Hs σ)) (hZ : 2 * Z ≤ W) (hWz : Wz < Hb)
    (hnode : NodeSpecFC' M (cflowO M NO u S T) Reach gid u S T Z I W Hb Wz nodeS nc (rSp M sR)
      rN)
    (hHb : 0 < Hb) (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D) {e h : ℕ} (c : Config)
    (hc : WordsBounded W c) (hz : MemZ Wz c) (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1)
    (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h) (m0 : c.nmem Hb = 0)
    (m1 : c.nmem (Hb + 1) = 0) (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hr : h + roomC M (fun _ => 0) (rSp M sR) rN τ Hs σ ≤ W)
    (hin : FInL M Reach gid u S T Z (τ, Hs, σ) (Hb + 5) e c) :
    ∃ c' t, Exec I W (driver mtProg mlProg (splitS sepP) nodeS) c c' t ∧
      t ≤ mcost M (fun _ => 3) (fun x => 20 * (pdarts M x.1.piece x.2.1).card + 17) (scp M sT) nc
        τ Hs σ + 2 ∧ MemZ Wz c' ∧
      FOutL M gid u S T Z (τ, Hs, σ) (arunLO M NO u S T τ Hs σ) (Hb + 5) e c' ∧
      HeapKeep Hb h Hb e c c' ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, g', hout, -, -, hk, ho⟩ :=
    mfDriveRC (mfSpecR_frameO' hsep hReach hZ hWz hnode) hHb τ Hs σ c hc hz r0 r1 r2 r3 m0 m1
      m2 he hh hr hin
  exact ⟨c', t, ex, ht, g', hout, hk, ho⟩

end FrameZ

section StepZ

variable (M) in
/-- **The specification of the step with the zero-memory invariant**: `StepPSpecC` with the extra
hypotheses `Wz < d` (the frame above the zero part) and `MemZ Wz c`. The conclusion is that of
`StepPSpecC` (it keeps the memory below `b` outside the flow array, hence `MemZ Wz`). -/
def StepPSpecC' (cf : CFlow M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (stepP : Stmt) (stT rT : MCall M → ℕ) :
    Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e b m : ℕ)
    (en : ℕ → D) (c : Config),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem → d + fsz m ≤ e →
    (∀ i < m, (c.nmem (d + 4 + 6 * m + i) : ℤ) =
      Z + fext (joinFlow (B := pdarts M (l.piece ∪ r.piece) Hs)
        (cf (chL M l r π Hs σ)) (cf (chR M l r π Hs σ))) (en i)) →
    WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = b + 5 → e ≤ b →
    b + rT (.node l r π, Hs, σ) ≤ W → Wz < d → MemZ Wz c →
    ∃ c' t, Exec I W stepP c c' t ∧ t ≤ stT (.node l r π, Hs, σ) ∧ DRegKeep c c' ∧
      (∀ a, a < b → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      ∀ i < m, (c'.nmem (d + 4 + 6 * m + i) : ℤ) =
        Z + fext (cf (.node l r π, Hs, σ)) (en i)

/-- `StepPSpecC` (no hypothesis on the memory) gives `StepPSpecC'`. -/
lemma StepPSpecC.toZ {cf : CFlow M} {Reach : MCall M → Prop} {gid : D → ℕ} {u : D → ℤ}
    {S T : Finset V} {Z : ℕ} {I : Input} {W Wz : ℕ} {stepP : Stmt} {stT rT : MCall M → ℕ}
    (h : StepPSpecC M cf Reach gid u S T Z I W stepP stT rT) :
    StepPSpecC' M cf Reach gid u S T Z I W Wz stepP stT rT :=
  fun l r π Hs σ d e b m en c hR hok hL hde hfl hc r4 r5 r6 heb hroom _ _ =>
    h l r π Hs σ d e b m en c hR hok hL hde hfl hc r4 r5 r6 heb hroom

variable {cf : CFlow M} {Reach : MCall M → Prop} {gid : D → ℕ} {u : D → ℤ}
  {S T : Finset V} {Z : ℕ} {I : Input} {W Hb Wz : ℕ} {stepP : Stmt} {stT rT rS : MCall M → ℕ}

/-- **`nodeSF_specC` with the zero-memory invariant** (`Wz < Hb`): the join keeps the memory below
the parent's heap top outside the flow array, so the step starts with `MemZ Wz`, and keeps it. -/
theorem nodeSF_specC' (hst : StepPSpecC' M cf Reach gid u S T Z I W Wz stepP stT rT)
    (hWz : Wz < Hb) :
    NodeSpecFC' M cf Reach gid u S T Z I W Hb Wz (nodeSF stepP) (ncF M stT) rS rT := by
  intro l r π Hs σ d e bl el er c hz hc r4 r5 r6 r7 r8 r9 r3 hd1 hde hebl hbl hel hroom hin hl hr
  have hR := hin.1
  have hok := hin.2.1
  obtain ⟨c₁, t₁, m, en, e₁, ht₁, hL₁, hfs, hfl₁, hm₁, hr₁, hrr₁, hrm₁, ho₁⟩ :=
    njProg_join (I := I) l r π Hs σ c hc r4 r6 r8 r9 hebl hbl hel hin hl hr
  have hw₁ := e₁.wb_right
  have hz₁ : MemZ Wz c₁ := hz.of_eq fun a ha => hm₁ a (by omega) (fun h => by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, dk₂, hm₂, ho₂, hfl₂⟩ := hst l r π Hs σ d e bl m en c₁ hR hok hL₁ hfs
    hfl₁ hw₁ (by rw [hr₁ _ (by omega), r4]) (by rw [hr₁ _ (by omega), r5])
    (by rw [hr₁ _ (by omega), r6]) hebl (by omega) (by omega) hz₁
  have hm : m = (pdarts M (l.piece ∪ r.piece) Hs).card := hL₁.card
  unfold fsz at hfs
  have hz₂ : MemZ Wz c₂ := hz₁.of_eq fun a ha => (hm₂ a (by omega) (fun h => by omega)).1
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, ?_, hz₂, fun x hx1 hx2 => ?_, fun a ha1 ha2 ha3 => ?_,
    by rw [ho₂, ho₁], m, en, hL₁.congr fun a h1 h2 => (hm₂ a (by omega) (by omega)).1,
    by unfold fsz; omega, hfl₂⟩
  · unfold ncF; simp only [ADec.piece]; rw [← hm]; omega
  · rw [dk₂ x hx1 hx2, hr₁ x (by omega)]
  · have hnot : ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) := fun h => by omega
    obtain ⟨a1, a2⟩ := hm₂ a ha2 hnot
    exact ⟨by rw [a1, hm₁ a (by omega) hnot], by rw [a2, hrm₁]⟩

end StepZ

end Gen

end MfDrv

end BKMNW

end PlanarFlow
