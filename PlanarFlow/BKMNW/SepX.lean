module

public import PlanarFlow.BKMNW.MfX

/-!
# The specification `SepPSpecX` of the separator program on the extended frame

`SepPSpec` (`MfSplitProg.lean`) is not satisfiable for the decomposition of the headline theorem.
**`SepPSpecX`** gives the separator program the extended frame `FInLX` (the
frame with the decomposition record, `MfX.lean`) and asks it, besides the outputs of `SepPSpec`
(the flags of the left piece, of the path's darts and vertices on the frame's darts, of the holes
meeting the path, the two tags), for **the records of the two children**: from a base `Xb`
returned in `r6501` (above the scratch of the rest of the split, `Sb + 21 m + 4 k + 2 ≤ Xb`), the
sizes `zl`, `zr` at `Xb`, `Xb + 1`, the left child's record at `Xb + 2` and the right child's at
`Xb + 2 + zl` (`RecAt`), all below `Sb + sR n m k` (`n` the darts of the piece, `m` of the piece
map, `k` the holes); within `sT n k` steps; keeping the memory below `Sb` (in particular any memory
below the frame base, e.g. a zero area `≤ Wz < Hb`), the registers `3000 … 3012` and the output.

* `SepPSpecX`, `RecsOut` (the children's records from `Xb`), `RecsOut.congr`;
* `spFlags_hi` (the flags of the split keep the memory from `Wb + 7 m + 3 k` on);
* **`spFront_execX`**: `spFront sepP` on the extended frame: `SpFront` and the children's records.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **The children's records written by the separator program** from `Xb`: sizes `zl = mem Xb`,
`zr = mem (Xb + 1)`, the left child's record at `Xb + 2`, the right child's at `Xb + 2 + zl`,
between `lo` and `hi`. -/
def RecsOut (ds : DSys M) (gid : D → ℕ) (ν : V → ℕ) (S T : Finset V) (l r : ADec M) (π : HSep M)
    (Hs : List (Finset V)) (σ : Perm D) (lo hi Xb : ℕ) (mem : ℕ → ℕ) : Prop :=
  lo ≤ Xb ∧ Xb + 2 + mem Xb + mem (Xb + 1) ≤ hi ∧
    RecAt M ds gid ν S T (chL M l r π Hs σ) (Xb + 2) (mem Xb) mem ∧
    RecAt M ds gid ν S T (chR M l r π Hs σ) (Xb + 2 + mem Xb) (mem (Xb + 1)) mem

variable (M) in
/-- **The specification of the separator program on the extended frame** (see the module
docstring). -/
def SepPSpecX (ds : DSys M) (Reach : MCall M → Prop) (gid : D → ℕ) (ν : V → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (sepP : Stmt) (sT : ℕ → ℕ → ℕ)
    (sR : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e h Sb m : ℕ)
    (en : ℕ → D) (c : Config),
    FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem → WordsBounded W c →
    c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3003 = h → c.nreg 6500 = Sb → e ≤ h → h < Sb →
    Sb + sR (l.piece ∪ r.piece).card m Hs.length ≤ W →
    ∃ c' t, Exec I W sepP c c' t ∧ t ≤ sT (l.piece ∪ r.piece).card Hs.length ∧ DRegKeep c c' ∧
      (∀ a < Sb, c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ i < m, c'.nmem (Sb + i) = bf (en i ∈ l.piece)) ∧
      (∀ i < m, c'.nmem (Sb + m + i) = bf (en i ∈ π.path.darts.toFinset)) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = bf (M.tail (en i) ∈ π.path.mverts)) ∧
      (∀ j < Hs.length, c'.nmem (Sb + 3 * m + j) =
        bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
      c'.nmem (Sb + 3 * m + Hs.length) = ntag l ∧ c'.nmem (Sb + 3 * m + Hs.length + 1) = ntag r ∧
      RecsOut M ds gid ν S T l r π Hs σ (Sb + 21 * m + 4 * Hs.length + 2)
        (Sb + sR (l.piece ∪ r.piece).card m Hs.length) (c'.nreg 6501) c'.nmem

variable {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {ds : DSys M}

/-- `RecsOut` depends only on the memory in `[Xb, hi)`. -/
lemma RecsOut.congr {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    {lo hi Xb : ℕ} {mem mem' : ℕ → ℕ} (h : RecsOut M ds gid ν S T l r π Hs σ lo hi Xb mem)
    (he : ∀ a, Xb ≤ a → a < hi → mem' a = mem a) :
    RecsOut M ds gid ν S T l r π Hs σ lo hi Xb mem' := by
  obtain ⟨h1, h2, hl, hr⟩ := h
  have e0 : mem' Xb = mem Xb := he _ le_rfl (by omega)
  have e1 : mem' (Xb + 1) = mem (Xb + 1) := he _ (by omega) (by omega)
  refine ⟨h1, by rw [e0, e1]; exact h2, ?_, ?_⟩
  · rw [e0]; exact hl.congr fun a a1 a2 => he a (by omega) (by omega)
  · rw [e0, e1]; exact hr.congr fun a a1 a2 => he a (by omega) (by omega)

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **The flags of the split keep the memory from `Wb + 7 m + 3 k` on** (the hypotheses of
`spFlags_exec`). -/
theorem spFlags_hi (c : Config) (hc : WordsBounded W c) {d m k Sb Wb : ℕ}
    (hR : SpRegs c d m k Sb Wb) (o1 : d + 4 + 6 * m ≤ Sb) (o2 : Sb + 3 * m + k + 2 ≤ Wb)
    (w : Wb + 7 * m + 3 * k ≤ W) (w' : m + k + 2 ≤ W)
    (hrv : ∀ i < m, c.nmem (d + 4 + m + i) < m) (hHL : ∀ i < m, c.nmem (d + 4 + 5 * m + i) ≤ k) :
    ∃ c' t, Exec I W spFlags c c' t ∧
      ∀ a, Wb + 7 * m + 3 * k ≤ a → c'.nmem a = c.nmem a := by
  obtain ⟨c₃, t₃, e₃, ht₃, f1, f2, f3, f4, m3, n3, rr3, rm3, o3⟩ := sfFlagsA_exec (P := I) c hc
    (m := m) (k := k) (Wb := Wb) (CVb := Sb + 2 * m) (HLb := d + 4 + 5 * m) (HMb := Sb + 3 * m)
    hR.r10 hR.r11 hR.r21 hR.r39 hR.r40 hR.r41 hR.r42 hR.r44 hR.r36 hR.r47 hR.r37 (by omega)
    (by omega) (by omega) w w' hHL
  have q3 : ∀ x, (x < 6300 ∨ (6309 < x ∧ x < 6520) ∨ x = 6521 ∨ (6529 < x ∧ x ≠ 6548)) →
      c₃.nreg x = c.nreg x := n3
  have m3' : ∀ a, a < Wb → c₃.nmem a = c.nmem a := fun a ha => m3 a (by omega)
  have hR3 : SpRegs c₃ d m k Sb Wb := hR.congr fun x hx => q3 x (by unfold spReg at hx; omega)
  have NH : ∀ i < m, c₃.nmem (Wb + i) = nhv c.nmem Sb d m i := f1
  have hl3 : ∀ i < m, c₃.nmem (d + 4 + 5 * m + i) = c.nmem (d + 4 + 5 * m + i) := fun i hi =>
    m3' _ (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, g1, g2, g3, g4, g5, m4, n4, rr4, rm4, o4⟩ := sfFlagsB_exec (P := I) c₃
    e₃.wb_right (m := m) (k := k) (Wb := Wb) (HLb := d + 4 + 5 * m) (LPb := Sb)
    (RVb := d + 4 + m) (KRb := d + 4 + 4 * m) (nd1 := cnt (hfv c.nmem Sb m) k + 1)
    hR3.r10 hR3.r21 hR3.r39 hR3.r41 hR3.r43 hR3.r44 hR3.r45 hR3.r46 hR3.r47 f3 hR3.r31 hR3.r32
    hR3.r33 hR3.r34 hR3.r35 (by omega) (by omega) (by omega) (by omega) w (by omega)
    (fun i hi => by rw [m3' _ (by omega)]; exact hrv i hi)
    (fun i hi => by rw [hl3 i hi]; exact hHL i hi)
    (fun i hi h1 h2 => by
      rw [NH i hi] at h1
      rw [hl3 i hi] at h2 ⊢
      have hl := hHL i hi
      have hz : hfv c.nmem Sb m (c.nmem (d + 4 + 5 * m + i) - 1) = 1 := by
        unfold nhv nhF at h1; unfold hfv hfF; split_ifs at h1 <;> simp_all
      rw [f4 _ (by omega) (by unfold hfv at hz; omega)]
      have := cnt_le (fun j => hfF (c.nmem (Sb + 3 * m + j))) (c.nmem (d + 4 + 5 * m + i) - 1)
      omega)
  refine ⟨c₄, _, .seq e₃ e₄, fun a ha => ?_⟩
  rw [m4 a (by omega), m3 a (by omega)]

set_option maxHeartbeats 4000000 in
/-- **The front of the split on the extended frame**: `spFront_exec` with `SepPSpecX`, and the
children's records `RecsOut` from `r6501` at the end. -/
theorem spFront_execX {Reach : MCall M → Prop} {sepP : Stmt} {sT : ℕ → ℕ → ℕ}
    {sR : ℕ → ℕ → ℕ → ℕ} (hsep : SepPSpecX M ds Reach gid ν u S T Z I W sepP sT sR)
    {l r : ADec M} {π : HSep M}
    {Hs : List (Finset V)} {σ : Perm D} {d e h : ℕ} (c : Config) (hc : WordsBounded W c)
    (r4 : c.nreg 3004 = d) (r5 : c.nreg 3005 = e) (r3 : c.nreg 3003 = h) (heh : e ≤ h)
    (hin : FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c) {m : ℕ} {en : ℕ → D}
    (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem) (hfs : d + fsz m ≤ e)
    (hroom : h + 18 + 14 * m + sR (l.piece ∪ r.piece).card m Hs.length + 21 * m +
      4 * Hs.length + 2 ≤ W) :
    ∃ c' t, Exec I W (spFront sepP) c c' t ∧
      t ≤ sT (l.piece ∪ r.piece).card Hs.length + 91 * m + 21 * Hs.length + 72 ∧
      SpFront M gid u S T Z c' l r π Hs σ m en d h (h + 18 + 14 * m)
        (h + 18 + 14 * m + 3 * m + Hs.length + 2) ∧ DRegKeep c c' ∧
      (∀ a < h + 18 + 14 * m, c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      c'.output = c.output ∧
      RecsOut M ds gid ν S T l r π Hs σ (h + 18 + 14 * m + 21 * m + 4 * Hs.length + 2)
        (h + 18 + 14 * m + sR (l.piece ∪ r.piece).card m Hs.length) (c'.nreg 6501) c'.nmem := by
  have hW : h ≤ W := r3 ▸ hc.1 3003
  unfold fsz at hfs
  have hk0 : Hs.length = c.nmem (d + 1) := hL.hk.symm
  -- `r6500 := Sb`
  obtain ⟨c₁, t₁, e₁, ht₁, p00, n1, m1, rr1, rm1, o1⟩ := spPre_exec (P := I) c hc r4 r3 hL.hm
    (by omega)
  have hin1 : FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c₁ :=
    hin.stab (memEq_of_eq m1 rm1 d e)
  have hL1 : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₁.nmem := by rw [m1]; exact hL
  -- the separator program
  obtain ⟨c₂, t₂, e₂, ht₂, dk2, mk2, o2, s1, s2, s3, s4, s5, s6, hRO⟩ := hsep l r π Hs σ d e h
    (h + 18 + 14 * m) m en c₁ hin1 hL1 e₁.wb_right (by rw [n1 _ (by omega), r4])
    (by rw [n1 _ (by omega), r5]) (by rw [n1 _ (by omega), r3]) p00 heh (by omega) (by omega)
  have hL2 : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₂.nmem :=
    hL1.congr fun a h1 h2 => (mk2 a (by omega)).1
  have hk2 : c₂.nmem (d + 1) = Hs.length := hL2.hk
  have hlL : ∀ i < m, c₂.nmem (d + 4 + 5 * m + i) = hlab Hs (M.tail (en i)) := hL2.hl
  have krL : ∀ i < m, c₂.nmem (d + 4 + 4 * m + i) = lrk S T (hunion Hs) (M.tail (en i)) :=
    hL2.kr
  have emL : ∀ i < m, en i ∈ pdarts M (l.piece ∪ r.piece) Hs := hL2.en_mem
  have d4 : c₂.nreg 3004 = d := by rw [dk2 _ (by omega) (by omega), n1 _ (by omega), r4]
  have d3 : c₂.nreg 3003 = h := by rw [dk2 _ (by omega) (by omega), n1 _ (by omega), r3]
  -- the bases
  obtain ⟨c₃, t₃, e₃, ht₃, hR3, n3, m3, rr3, rm3, o3⟩ := spSet_exec (P := I) c₂ e₂.wb_right d4
    d3 hL2.hm hk2 rfl rfl (by omega) (by omega)
  have hL3 : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₃.nmem := by rw [m3]; exact hL2
  -- the flags
  obtain ⟨c₄, t₄, e₄, ht₄, g1, g2, g3, g4, g5, g6, m4, hR4, n4, rr4, rm4, o4⟩ := spFlags_exec
    (P := I) c₃ e₃.wb_right hR3 (by omega) le_rfl (by omega) (by omega)
    (fun i hi => (hL3.rv i hi).1) (fun i hi => by rw [m3, hlL i hi]; exact hlab_le _ _)
  obtain ⟨c₄', t₄', e₄', hi4⟩ := spFlags_hi (I := I) c₃ e₃.wb_right hR3 (by omega) le_rfl
    (by omega) (by omega) (fun i hi => (hL3.rv i hi).1)
    (fun i hi => by rw [m3, hlL i hi]; exact hlab_le _ _)
  obtain ⟨rfl, rfl⟩ := Exec.det e₄' e₄
  -- the records
  have hRO4 : RecsOut M ds gid ν S T l r π Hs σ (h + 18 + 14 * m + 21 * m + 4 * Hs.length + 2)
      (h + 18 + 14 * m + sR (l.piece ∪ r.piece).card m Hs.length) (c₄'.nreg 6501) c₄'.nmem := by
    have r01 : c₄'.nreg 6501 = c₂.nreg 6501 := by rw [n4 _ (by omega), n3 _ (by omega)]
    rw [r01]
    exact hRO.congr fun a a1 a2 => by
      have := hRO.1
      rw [hi4 a (by omega), m3]
  -- the invariants of the call
  obtain ⟨-, hok, -⟩ := hin
  obtain ⟨⟨hPI, -, -⟩, ⟨-, -, hlr, -, hC, -⟩, -, -, hSA, hTA, hd⟩ := hok
  have hSC : Disjoint S π.path.mverts :=
    (disjoint_of_subset_right subset_union_left hC).symm
  have hTC : Disjoint T π.path.mverts :=
    (disjoint_of_subset_right subset_union_right hC).symm
  rw [m3] at g1 g2 g3 g4 g6
  -- the machine's flag of the new hole
  have NH : ∀ i < m, nhv c₂.nmem (h + 18 + 14 * m) d m i =
      bf (M.tail (en i) ∈ newHole Hs π.path.mverts) := fun i hi =>
    nhv_sem (x := (.node l r π, Hs, σ)) hL2 hd s3 s4 hi
  have NHr : ∀ i < m, nhv c₂.nmem (h + 18 + 14 * m) d m (c₂.nmem (d + 4 + m + i)) =
      bf (M.tail (M.rev (en i)) ∈ newHole Hs π.path.mverts) := fun i hi => by
    obtain ⟨hj, ej⟩ := hL2.rv i hi
    rw [NH _ hj, ej]
  have hcnt : ∀ j ≤ Hs.length, cnt (hfv c₂.nmem (h + 18 + 14 * m) m) j =
      hcnt Hs π.path.mverts j := fun j hj => cnt_hfv s4 hj
  have M4 : ∀ a < h + 18 + 14 * m + 3 * m + Hs.length + 2, c₄'.nmem a = c₂.nmem a :=
    fun a ha => by rw [m4 a ha, m3]
  refine ⟨c₄', _, .seq e₁ (.seq e₂ (.seq e₃ e₄')), by omega, ⟨hR4, ?_, ?_, ?_,
    hL2.congr fun a h1 h2 => M4 a (by omega), fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, g5, ?_, ?_, rfl, rfl⟩, fun x h1 h2 => ?_, fun a ha => ?_,
    by rw [o4, o3, o2, o1], hRO4⟩
  · rw [g6, hcnt _ le_rfl, hcnt_length, length_childHoles_eq]
  · rw [n4 _ (by omega), n3 _ (by omega), d4]
  · rw [n4 _ (by omega), n3 _ (by omega), d3]
  · rw [M4 _ (by omega)]; exact s2 i hi
  · have hyB := emL i hi
    rw [g1 i hi, s1 i hi, NH i hi, NHr i hi, flL_eq]
    exact bf_congr (mem_pdarts_child hyB).symm
  · have hyB := emL i hi
    have hlr' : en i ∈ r.piece ↔ ¬ en i ∈ l.piece := by
      have h1 := (mem_pdarts.1 hyB).1
      simp only [ADec.piece, mem_union] at h1
      constructor
      · intro hr hl; exact disjoint_left.1 hlr hl hr
      · intro hl; rcases h1 with h1 | h1
        · exact absurd h1 hl
        · exact h1
    rw [g2 i hi, s1 i hi, NH i hi, NHr i hi, flR_eq]
    refine bf_congr ?_
    rw [mem_pdarts_child hyB, hlr']
  · rw [g3 i hi, NH i hi, krL i hi]
    exact kcF_eq hSC hTC hSA _
  · have hl := hlab_le Hs (M.tail (en i))
    rw [g4 i hi, NH i hi, hlL i hi, hcnt _ le_rfl, hcnt _ (by omega)]
    exact hcF_eq hd _ (fun _ _ => rfl)
  · rw [M4 _ (by omega)]; exact s5
  · rw [M4 _ (by omega)]; exact s6
  · rw [n4 _ (by omega), n3 _ (by omega), dk2 _ h1 h2, n1 _ (by omega)]
  · have := mk2 a ha
    rw [M4 a (by omega), rr4] at *
    rw [rm4, rm3, this.1, this.2, m1, rm1]
    exact ⟨rfl, rfl⟩

end Exec

end MfDrv

end BKMNW

end PlanarFlow
