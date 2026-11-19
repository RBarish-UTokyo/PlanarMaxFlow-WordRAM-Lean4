module

public import PlanarFlow.BKMNW.MfSplitProg

/-!
# The front of the split: the separator and the per-dart data of the children

`spPre ; sepP ; spSet ; spFlags` at a node call `x = (.node l r π, Hs, σ)` (frame `[d, e)`, `m`
darts `en i`, `k = #Hs` holes, heap top `h`, `Sb = h + 18 + 14 m`, `Wb = Sb + 3 m + k + 2`): with
`sepP` meeting `SepPSpec`, it ends in a state **`SpFront`**: the registers `SpRegs`,
`r6548 = #(childHoles Hs C)`, the parent's layout, and from `Sb`, `Wb` the arrays
`PF = bf (en i ∈ π.path.darts)`, `FLl = bf (en i ∈ Bl)`, `FLr = bf (en i ∈ Br)` (the children's
darts), `KC` (the children's ranks), `HC` (the children's hole labels), `ID`, the tags `ntag l`,
`ntag r`.

* `bf_congr`, `hlab_le`, **`nhv_sem`**, `cnt_hfv`, `SpFront`, `SpFront.congr`.
* **`spFront_exec`**: within `sT m + 91 m + 21 k + 72` steps, `SpFront` at the end, the memory
  and the reals below `Sb`, the registers `3000 … 3012` and the output kept.
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

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

lemma bf_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : bf p = bf q := by
  unfold bf; by_cases hp : p
  · rw [iteT hp, iteT (h.1 hp)]
  · rw [iteF hp, iteF (fun hq => hp (h.2 hq))]

lemma hlab_le (Hs : List (Finset V)) (v : V) : hlab Hs v ≤ Hs.length := by
  by_cases h : 0 < hlab Hs v
  · have := (hlab_mem h).1; omega
  · omega

/-- **The machine's flag of the new hole.** -/
lemma nhv_sem {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (hd : x.2.1.Pairwise Disjoint) {C : Finset V}
    {Sb : ℕ} (hcv : ∀ i < m, mem (Sb + 2 * m + i) = bf (M.tail (en i) ∈ C))
    (hhm : ∀ j < x.2.1.length, mem (Sb + 3 * m + j) = bf (¬ Disjoint (x.2.1.getD j ∅) C))
    {i : ℕ} (hi : i < m) : nhv mem Sb d m i = bf (M.tail (en i) ∈ newHole x.2.1 C) := by
  rw [← nhF_eq hd]
  unfold nhv
  rw [hcv i hi, hL.hl i hi]
  unfold nhF
  by_cases h1 : 0 < bf (M.tail (en i) ∈ C)
  · rw [iteT h1, iteT h1]
  · rw [iteF h1, iteF h1]
    by_cases h2 : 0 < hlab x.2.1 (M.tail (en i))
    · rw [iteT h2, iteT h2, hhm _ (hlab_mem h2).1]
    · rw [iteF h2, iteF h2]

/-- The count of the kept holes on the machine. -/
lemma cnt_hfv {mem : ℕ → ℕ} {Sb m : ℕ} {Hs : List (Finset V)} {C : Finset V}
    (hhm : ∀ j < Hs.length, mem (Sb + 3 * m + j) = bf (¬ Disjoint (Hs.getD j ∅) C))
    {j : ℕ} (hj : j ≤ Hs.length) : cnt (hfv mem Sb m) j = hcnt Hs C j := by
  rw [← cnt_hfF Hs C hj]
  exact cnt_ext fun i hi => by unfold hfv; rw [hhm i (by omega)]

variable (M) in
/-- **The state after the front of the split** (see the module docstring). -/
structure SpFront (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ) (c : Config)
    (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (m : ℕ) (en : ℕ → D)
    (d h Sb Wb : ℕ) : Prop where
  regs : SpRegs c d m Hs.length Sb Wb
  r48 : c.nreg 6548 = (childHoles Hs π.path.mverts).length
  r04 : c.nreg 3004 = d
  r03 : c.nreg 3003 = h
  lay : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem
  pf : ∀ i < m, c.nmem (Sb + m + i) = bf (en i ∈ π.path.darts.toFinset)
  fl : ∀ i < m, c.nmem (Wb + m + i) = bf (en i ∈ pdarts M l.piece (childHoles Hs π.path.mverts))
  fr : ∀ i < m, c.nmem (Wb + 2 * m + i) =
    bf (en i ∈ pdarts M r.piece (childHoles Hs π.path.mverts))
  kc : ∀ i < m, c.nmem (Wb + 3 * m + i) =
    lrk S T (hunion (childHoles Hs π.path.mverts)) (M.tail (en i))
  hc : ∀ i < m, c.nmem (Wb + 4 * m + i) = hlab (childHoles Hs π.path.mverts) (M.tail (en i))
  id : ∀ i < m, c.nmem (Wb + 5 * m + i) = i
  tl : c.nmem (Sb + 3 * m + Hs.length) = ntag l
  tr : c.nmem (Sb + 3 * m + Hs.length + 1) = ntag r
  hSb : Sb = h + 18 + 14 * m
  hWb : Wb = Sb + 3 * m + Hs.length + 2

/-- `SpFront` depends on the registers of `SpRegs`, `6548`, `3003`, `3004` and on the memory in
`[d, d + 4 + 6 m)` and `[Sb, Wb + 6 m)`. -/
lemma SpFront.congr {c c' : Config} {l r : ADec M} {π : HSep M} {Hs : List (Finset V)}
    {σ : Perm D} {m : ℕ} {en : ℕ → D} {d h Sb Wb : ℕ}
    (hF : SpFront M gid u S T Z c l r π Hs σ m en d h Sb Wb)
    (hr : ∀ x, (spReg x ∨ x = 6548 ∨ x = 3003 ∨ x = 3004) → c'.nreg x = c.nreg x)
    (hm : ∀ a, ((d ≤ a ∧ a < d + 4 + 6 * m) ∨ (Sb ≤ a ∧ a < Wb + 6 * m)) →
      c'.nmem a = c.nmem a) :
    SpFront M gid u S T Z c' l r π Hs σ m en d h Sb Wb where
  regs := hF.regs.congr fun x hx => hr x (Or.inl hx)
  r48 := by rw [hr _ (by omega)]; exact hF.r48
  r04 := by rw [hr _ (by omega)]; exact hF.r04
  r03 := by rw [hr _ (by omega)]; exact hF.r03
  lay := hF.lay.congr fun a h1 h2 => hm a (Or.inl ⟨h1, h2⟩)
  pf i hi := by have := hF.hWb; rw [hm _ (by omega)]; exact hF.pf i hi
  fl i hi := by have := hF.hWb; rw [hm _ (by omega)]; exact hF.fl i hi
  fr i hi := by have := hF.hWb; rw [hm _ (by omega)]; exact hF.fr i hi
  kc i hi := by have := hF.hWb; rw [hm _ (by omega)]; exact hF.kc i hi
  hc i hi := by have := hF.hWb; rw [hm _ (by omega)]; exact hF.hc i hi
  id i hi := by have := hF.hWb; rw [hm _ (by omega)]; exact hF.id i hi
  tl := by have := hF.hWb; rw [hm _ (by omega)]; exact hF.tl
  tr := by have := hF.hWb; rw [hm _ (by omega)]; exact hF.tr
  hSb := hF.hSb
  hWb := hF.hWb

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **The front of the split** (see the module docstring). -/
theorem spFront_exec {Reach : MCall M → Prop} {sepP : Stmt} {sT : ℕ → ℕ} {sR : ℕ → ℕ → ℕ}
    (hsep : SepPSpec M Reach gid u S T Z I W sepP sT sR) {l r : ADec M} {π : HSep M}
    {Hs : List (Finset V)} {σ : Perm D} {d e h : ℕ} (c : Config) (hc : WordsBounded W c)
    (r4 : c.nreg 3004 = d) (r5 : c.nreg 3005 = e) (r3 : c.nreg 3003 = h) (heh : e ≤ h)
    (hin : FInL M Reach gid u S T Z (.node l r π, Hs, σ) d e c) {m : ℕ} {en : ℕ → D}
    (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem) (hfs : d + fsz m ≤ e)
    (hroom : h + 18 + 14 * m + sR m Hs.length + 21 * m + 4 * Hs.length + 2 ≤ W) :
    ∃ c' t, Exec I W (spFront sepP) c c' t ∧
      t ≤ sT m + 91 * m + 21 * Hs.length + 72 ∧
      SpFront M gid u S T Z c' l r π Hs σ m en d h (h + 18 + 14 * m)
        (h + 18 + 14 * m + 3 * m + Hs.length + 2) ∧ DRegKeep c c' ∧
      (∀ a < h + 18 + 14 * m, c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      c'.output = c.output := by
  have hW : h ≤ W := r3 ▸ hc.1 3003
  unfold fsz at hfs
  have hk0 : Hs.length = c.nmem (d + 1) := hL.hk.symm
  -- `r6500 := Sb`
  obtain ⟨c₁, t₁, e₁, ht₁, p00, n1, m1, rr1, rm1, o1⟩ := spPre_exec (P := I) c hc r4 r3 hL.hm
    (by omega)
  have hin1 : FInL M Reach gid u S T Z (.node l r π, Hs, σ) d e c₁ :=
    hin.stab (memEq_of_eq m1 rm1 d e)
  have hL1 : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₁.nmem := by rw [m1]; exact hL
  -- the separator program
  obtain ⟨c₂, t₂, e₂, ht₂, dk2, mk2, o2, s1, s2, s3, s4, s5, s6⟩ := hsep l r π Hs σ d e h
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
  have M4 : ∀ a < h + 18 + 14 * m + 3 * m + Hs.length + 2, c₄.nmem a = c₂.nmem a := fun a ha =>
    by rw [m4 a ha, m3]
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, ⟨hR4, ?_, ?_, ?_,
    hL2.congr fun a h1 h2 => M4 a (by omega), fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, g5, ?_, ?_, rfl, rfl⟩, fun x h1 h2 => ?_, fun a ha => ?_,
    by rw [o4, o3, o2, o1]⟩
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
