module

public import PlanarFlow.BKMNW.LinMerge
public import PlanarFlow.BKMNW.LinFlow

/-!
# The sum of the children's flows into the parent's frame, on the machine

At a node call the driver holds the parent's frame at `d` (`m` darts, the arrays `GID` from
`d + 4` and `FL` from `d + 4 + 6 m`) and the two children's output frames at `dl`, `dr` (`ml`,
`mr` darts; `GID` from `dl + 4`, `FL` from `dl + 4 + 6 ml`; the same at `dr`); the layout is
`PlanarFlow/BKMNW/MfFrame.lean`. The program `njProg`:

* reads `m`, `ml`, `mr`, `Z = mem (d + 3)` and the bases (`njA`, `njB`);
* two merges (`lxProg`) give the parent indices `IL[k]` of the left child's darts, written over the
  left child's array `RV` (at `dl + 4 + ml`), and `IR[k]` of the right child's (at `dr + 4 + mr`);
* fills the parent's `FL` with `Z` (`lzProg`) and copies the children's `FL` entries to their
  parent indices (`lcsProg` twice).

**`njProg_exec`**: within `35 m + 9 (ml + mr) + 60` steps the parent's `FL[i]` is the right
child's `FL[k]` if `GID_r[k] = GID[i]`, else the left child's `FL[k]` if `GID_l[k] = GID[i]`, else
`Z`; memory below `dl` outside the parent's `FL`, registers below `6260`, reals and output kept.
Registers written: `6260 … 6265`, `6600 … 6644`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Exec

variable {P : Input} {W : ℕ}

/-- The sizes, `Z`, and the bases of the merges. -/
def njA : Stmt := block [.loadN 6630 3004, .loadN 6631 3006, .loadN 6632 3008, .constN 6633 4,
  .addN 6634 3004 6633, .addN 6635 3006 6633, .addN 6636 3008 6633, .addN 6637 6635 6631,
  .addN 6638 6636 6632, .constN 6633 3, .addN 6643 3004 6633, .loadN 6644 6643]

/-- The bases of the flow arrays. -/
def njB : Stmt := block [.constN 6633 6, .mulN 6639 6633 6631, .addN 6640 6635 6639,
  .mulN 6639 6633 6632, .addN 6641 6636 6639, .mulN 6639 6633 6630, .addN 6642 6634 6639]

/-- The registers of the left merge. -/
def njS1 : Stmt :=
  block [.copyN 6600 6630, .copyN 6601 6634, .copyN 6602 6631, .copyN 6603 6635, .copyN 6604 6637]

/-- The registers of the right merge. -/
def njS2 : Stmt := block [.copyN 6602 6632, .copyN 6603 6636, .copyN 6604 6638]

/-- The registers of the fill. -/
def njS3 : Stmt := block [.copyN 6260 6630, .copyN 6261 6642, .copyN 6262 6644]

/-- The registers of the left copy. -/
def njS4 : Stmt := block [.copyN 6620 6631, .copyN 6621 6637, .copyN 6622 6640, .copyN 6623 6642]

/-- The registers of the right copy. -/
def njS5 : Stmt := block [.copyN 6620 6632, .copyN 6621 6638, .copyN 6622 6641]

/-- The bases and the two merges. -/
def njFront : Stmt := .seq njA (.seq njB (.seq njS1 (.seq lxProg (.seq njS2 lxProg))))

/-- The fill and the two copies. -/
def njBack : Stmt := .seq njS3 (.seq lzProg (.seq njS4 (.seq lcsProg (.seq njS5 lcsProg))))

/-- **The sum of the children's flows into the parent's frame.** -/
def njProg : Stmt := .seq njFront njBack

theorem njA_exec (c : Config) (hc : WordsBounded W c) {d dl dr m ml mr Z : ℕ}
    (r4 : c.nreg 3004 = d) (r6 : c.nreg 3006 = dl) (r8 : c.nreg 3008 = dr)
    (hm : c.nmem d = m) (hml : c.nmem dl = ml) (hmr : c.nmem dr = mr) (hz : c.nmem (d + 3) = Z)
    (w1 : d + 4 ≤ W) (w2 : dl + 4 + ml ≤ W) (w3 : dr + 4 + mr ≤ W) :
    ∃ c' t, Exec P W njA c c' t ∧ t = 12 ∧ c'.nreg 6630 = m ∧ c'.nreg 6631 = ml ∧
      c'.nreg 6632 = mr ∧ c'.nreg 6634 = d + 4 ∧ c'.nreg 6635 = dl + 4 ∧
      c'.nreg 6636 = dr + 4 ∧ c'.nreg 6637 = dl + 4 + ml ∧ c'.nreg 6638 = dr + 4 + mr ∧
      c'.nreg 6644 = Z ∧ (∀ x, x < 6630 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold njA
  exec_block
  all_goals try omega
  all_goals
    try (config_simp; simp (disch := omega) only [upd_other, upd_same, r4, r6, r8, hm, hml, hmr,
      hz] <;> omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r4, r6, r8, hm, hml, hmr, hz])
    try omega

theorem njB_exec (c : Config) (hc : WordsBounded W c) {d dl dr m ml mr : ℕ}
    (r0 : c.nreg 6630 = m) (r1 : c.nreg 6631 = ml) (r2 : c.nreg 6632 = mr)
    (r4 : c.nreg 6634 = d + 4) (r5 : c.nreg 6635 = dl + 4) (r6 : c.nreg 6636 = dr + 4)
    (w0 : 6 ≤ W) (w1 : d + 4 + 6 * m ≤ W) (w2 : dl + 4 + 6 * ml ≤ W) (w3 : dr + 4 + 6 * mr ≤ W) :
    ∃ c' t, Exec P W njB c c' t ∧ t = 7 ∧ c'.nreg 6640 = dl + 4 + 6 * ml ∧
      c'.nreg 6641 = dr + 4 + 6 * mr ∧ c'.nreg 6642 = d + 4 + 6 * m ∧
      (∀ x, x ≠ 6633 → x ≠ 6639 → x ≠ 6640 → x ≠ 6641 → x ≠ 6642 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold njB
  exec_block
  all_goals try omega
  all_goals
    try (config_simp; simp (disch := omega) only [upd_other, upd_same, r0, r1, r2, r4, r5, r6]
         <;> omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x a1 a2 a3 a4 a5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r0, r1, r2, r4, r5, r6])
    try omega


/-- **The bases and the two merges.** -/
theorem njFront_exec (c : Config) (hc : WordsBounded W c) {d dl dr m ml mr Z : ℕ}
    (r4 : c.nreg 3004 = d) (r6 : c.nreg 3006 = dl) (r8 : c.nreg 3008 = dr)
    (hm : c.nmem d = m) (hml : c.nmem dl = ml) (hmr : c.nmem dr = mr) (hz : c.nmem (d + 3) = Z)
    (l1 : d + 4 + 7 * m ≤ dl) (l2 : dl + 4 + 7 * ml ≤ dr) (l3 : dr + 4 + 7 * mr ≤ W)
    (hp : ∀ i j, i < j → j < m → c.nmem (d + 4 + i) < c.nmem (d + 4 + j))
    (hql : ∀ k k', k < k' → k' < ml → c.nmem (dl + 4 + k) < c.nmem (dl + 4 + k'))
    (hqr : ∀ k k', k < k' → k' < mr → c.nmem (dr + 4 + k) < c.nmem (dr + 4 + k'))
    (hexl : ∀ k < ml, ∃ i < m, c.nmem (d + 4 + i) = c.nmem (dl + 4 + k))
    (hexr : ∀ k < mr, ∃ i < m, c.nmem (d + 4 + i) = c.nmem (dr + 4 + k)) :
    ∃ c' t, Exec P W njFront c c' t ∧ t ≤ 30 * m + 37 ∧ c'.nreg 6630 = m ∧
      c'.nreg 6631 = ml ∧ c'.nreg 6632 = mr ∧ c'.nreg 6637 = dl + 4 + ml ∧
      c'.nreg 6638 = dr + 4 + mr ∧ c'.nreg 6640 = dl + 4 + 6 * ml ∧
      c'.nreg 6641 = dr + 4 + 6 * mr ∧ c'.nreg 6642 = d + 4 + 6 * m ∧ c'.nreg 6644 = Z ∧
      (∀ k < ml, c'.nmem (dl + 4 + ml + k) < m ∧
        c.nmem (d + 4 + c'.nmem (dl + 4 + ml + k)) = c.nmem (dl + 4 + k)) ∧
      (∀ k < mr, c'.nmem (dr + 4 + mr + k) < m ∧
        c.nmem (d + 4 + c'.nmem (dr + 4 + mr + k)) = c.nmem (dr + 4 + k)) ∧
      (∀ a, ¬ (dl + 4 + ml ≤ a ∧ a < dl + 4 + ml + ml) →
        ¬ (dr + 4 + mr ≤ a ∧ a < dr + 4 + mr + mr) → c'.nmem a = c.nmem a) ∧
      (∀ x, x < 6600 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold njFront
  obtain ⟨c₁, k₁, e₁, hk₁, a30, a31, a32, a34, a35, a36, a37, a38, a44, gn₁, gm₁, gr₁, grm₁,
    go₁⟩ := njA_exec (P := P) c hc r4 r6 r8 hm hml hmr hz (by omega) (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, a40, a41, a42, gn₂, gm₂, gr₂, grm₂, go₂⟩ := njB_exec (P := P) c₁
    e₁.wb_right a30 a31 a32 a34 a35 a36 (by omega) (by omega) (by omega) (by omega)
  have q2 : ∀ x, (x < 6633 ∨ (x ≠ 6633 ∧ x ≠ 6639 ∧ x ≠ 6640 ∧ x ≠ 6641 ∧ x ≠ 6642)) →
      c₂.nreg x = c₁.nreg x := fun x hx => by
    rcases hx with hx | ⟨b1, b2, b3, b4, b5⟩
    · exact gn₂ x (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact gn₂ x b1 b2 b3 b4 b5
  obtain ⟨c₃, k₃, e₃, hk₃, s0, s1, s2, s3, s4, gn₃, gm₃, gr₃, grm₃, go₃⟩ : ∃ c₃ k₃,
      Exec P W njS1 c₂ c₃ k₃ ∧ k₃ = 5 ∧ c₃.nreg 6600 = m ∧ c₃.nreg 6601 = d + 4 ∧
      c₃.nreg 6602 = ml ∧ c₃.nreg 6603 = dl + 4 ∧ c₃.nreg 6604 = dl + 4 + ml ∧
      (∀ x, (x < 6600 ∨ 6604 < x) → c₃.nreg x = c₂.nreg x) ∧
      c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have hw₂ := e₂.wb_right
    have b0 : c₂.nreg 6630 = m := by rw [q2 _ (by omega), a30]
    have b4 : c₂.nreg 6634 = d + 4 := by rw [q2 _ (by omega), a34]
    have b1 : c₂.nreg 6631 = ml := by rw [q2 _ (by omega), a31]
    have b5 : c₂.nreg 6635 = dl + 4 := by rw [q2 _ (by omega), a35]
    have b7 : c₂.nreg 6637 = dl + 4 + ml := by rw [q2 _ (by omega), a37]
    unfold njS1
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [b0, b1, b4, b5, b7])
    simp only [upd_apply]; split_ifs <;> omega
  have hw₃ := e₃.wb_right
  -- the left merge
  have em3 : ∀ a, c₃.nmem a = c.nmem a := fun a => by rw [gm₃, gm₂, gm₁]
  obtain ⟨c₄, k₄, e₄, hk₄, il, ml4, gn₄, gr₄, grm₄, go₄⟩ := lxProg_exec (P := P) c₃ hw₃ s0 s1 s2
    s3 s4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun i j h1 h2 => by rw [em3, em3]; exact hp i j h1 h2)
    (fun k k' h1 h2 => by rw [em3, em3]; exact hql k k' h1 h2)
    (fun k hk => by simp only [em3]; exact hexl k hk)
  simp only [em3] at il
  have q4 : ∀ x, (x < 6605 ∨ 6610 < x) → c₄.nreg x = c₃.nreg x := gn₄
  obtain ⟨c₅, k₅, e₅, hk₅, t2, t3, t4, gn₅, gm₅, gr₅, grm₅, go₅⟩ : ∃ c₅ k₅,
      Exec P W njS2 c₄ c₅ k₅ ∧ k₅ = 3 ∧ c₅.nreg 6602 = mr ∧ c₅.nreg 6603 = dr + 4 ∧
      c₅.nreg 6604 = dr + 4 + mr ∧ (∀ x, (x < 6602 ∨ 6604 < x) → c₅.nreg x = c₄.nreg x) ∧
      c₅.nmem = c₄.nmem ∧ c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    have hw₄ := e₄.wb_right
    have b2 : c₄.nreg 6632 = mr := by
      rw [q4 _ (by omega), gn₃ _ (by omega), q2 _ (by omega), a32]
    have b6 : c₄.nreg 6636 = dr + 4 := by
      rw [q4 _ (by omega), gn₃ _ (by omega), q2 _ (by omega), a36]
    have b8 : c₄.nreg 6638 = dr + 4 + mr := by
      rw [q4 _ (by omega), gn₃ _ (by omega), q2 _ (by omega), a38]
    unfold njS2
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [b2, b6, b8])
    simp only [upd_apply]; split_ifs <;> omega
  have hw₅ := e₅.wb_right
  have em5 : ∀ a, ¬ (dl + 4 + ml ≤ a ∧ a < dl + 4 + ml + ml) → c₅.nmem a = c.nmem a :=
    fun a ha => by rw [gm₅, ml4 a ha, em3]
  have u0 : c₅.nreg 6600 = m := by rw [gn₅ _ (by omega), q4 _ (by omega), s0]
  have u1 : c₅.nreg 6601 = d + 4 := by rw [gn₅ _ (by omega), q4 _ (by omega), s1]
  -- the right merge
  obtain ⟨c₆, k₆, e₆, hk₆, ir, mr6, gn₆, gr₆, grm₆, go₆⟩ := lxProg_exec (P := P) c₅ hw₅ u0 u1 t2
    t3 t4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun i j h1 h2 => by rw [em5 _ (by omega), em5 _ (by omega)]; exact hp i j h1 h2)
    (fun k k' h1 h2 => by rw [em5 _ (by omega), em5 _ (by omega)]; exact hqr k k' h1 h2)
    (fun k hk => by
      obtain ⟨i, hi, he⟩ := hexr k hk
      exact ⟨i, hi, by rw [em5 _ (by omega), em5 _ (by omega)]; exact he⟩)
  have q6 : ∀ x, (x < 6605 ∨ 6610 < x) → c₆.nreg x = c₅.nreg x := gn₆
  have back : ∀ x, 6610 < x → x ≠ 6633 → x ≠ 6639 → x ≠ 6640 → x ≠ 6641 → x ≠ 6642 →
      c₆.nreg x = c₁.nreg x := fun x h1 h2 h3 h4 h5 h6 => by
    rw [q6 _ (by omega), gn₅ _ (by omega), q4 _ (by omega), gn₃ _ (by omega),
      q2 _ (Or.inr ⟨h2, h3, h4, h5, h6⟩)]
  have back2 : ∀ x, 6610 < x → c₆.nreg x = c₂.nreg x := fun x h1 => by
    rw [q6 _ (by omega), gn₅ _ (by omega), q4 _ (by omega), gn₃ _ (by omega)]
  refine ⟨c₆, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆)))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄
    (.seq e₅ e₆)))), by omega, by rw [back _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), a30], by rw [back _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), a31], by rw [back _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), a32], by rw [back _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), a37], by rw [back _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), a38], by rw [back2 _ (by omega), a40],
    by rw [back2 _ (by omega), a41], by rw [back2 _ (by omega), a42],
    by rw [back _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a44],
    fun k hk => ?_, fun k hk => ?_, fun a ha hb => ?_, fun x hx => ?_,
    by rw [gr₆, gr₅, gr₄, gr₃, gr₂, gr₁], by rw [grm₆, grm₅, grm₄, grm₃, grm₂, grm₁],
    by rw [go₆, go₅, go₄, go₃, go₂, go₁]⟩
  · rw [mr6 _ (by omega), gm₅]
    exact il k hk
  · obtain ⟨b1, b2⟩ := ir k hk
    refine ⟨b1, ?_⟩
    rw [← em5 _ (by omega), ← em5 (dr + 4 + k) (by omega)]
    exact b2
  · rw [mr6 a hb, em5 a ha]
  · rw [q6 _ (by omega), gn₅ _ (by omega), q4 _ (by omega), gn₃ _ (by omega), q2 _ (by omega),
      gn₁ x (by omega)]

/-- **The fill and the two copies.** -/
theorem njBack_exec (c : Config) (hc : WordsBounded W c) {m ml mr ILb IRb VLb VRb OUTb Z : ℕ}
    (r0 : c.nreg 6630 = m) (r1 : c.nreg 6631 = ml) (r2 : c.nreg 6632 = mr)
    (r7 : c.nreg 6637 = ILb) (r8 : c.nreg 6638 = IRb) (r40 : c.nreg 6640 = VLb)
    (r41 : c.nreg 6641 = VRb) (r42 : c.nreg 6642 = OUTb) (r44 : c.nreg 6644 = Z)
    (l0 : 0 < OUTb) (l1 : OUTb + m ≤ ILb) (l2 : ILb + ml ≤ VLb) (l3 : VLb + ml ≤ IRb) (l4 : IRb + mr ≤ VRb)
    (l5 : VRb + mr ≤ W)
    (hIL : ∀ k < ml, c.nmem (ILb + k) < m) (hIR : ∀ k < mr, c.nmem (IRb + k) < m)
    (iL : ∀ k < ml, ∀ k' < ml, c.nmem (ILb + k) = c.nmem (ILb + k') → k = k')
    (iR : ∀ k < mr, ∀ k' < mr, c.nmem (IRb + k) = c.nmem (IRb + k') → k = k') :
    ∃ c' t, Exec P W njBack c c' t ∧ t ≤ 5 * m + 9 * (ml + mr) + 22 ∧
      (∀ k < mr, c'.nmem (OUTb + c.nmem (IRb + k)) = c.nmem (VRb + k)) ∧
      (∀ k < ml, (∀ k' < mr, c.nmem (IRb + k') ≠ c.nmem (ILb + k)) →
        c'.nmem (OUTb + c.nmem (ILb + k)) = c.nmem (VLb + k)) ∧
      (∀ i < m, (∀ k < ml, c.nmem (ILb + k) ≠ i) → (∀ k < mr, c.nmem (IRb + k) ≠ i) →
        c'.nmem (OUTb + i) = Z) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, x < 6260 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold njBack
  obtain ⟨c₁, k₁, e₁, hk₁, s0, s1, s2, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W njS3 c c₁ k₁ ∧ k₁ = 3 ∧ c₁.nreg 6260 = m ∧ c₁.nreg 6261 = OUTb ∧
      c₁.nreg 6262 = Z ∧ (∀ x, (x < 6260 ∨ 6262 < x) → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold njS3
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r0, r42, r44])
    simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c₂, k₂, e₂, hk₂, o1, o2, o3, o4, o5, o6⟩ := lzProg_exec (P := P) c₁ e₁.wb_right s0 s1
    s2 (by omega) (by omega)
  have q2 : ∀ x, (x < 6260 ∨ 6265 < x) → c₂.nreg x = c.nreg x := fun x hx => by
    rw [o3 x (by omega), gn₁ x (by omega)]
  have m2 : ∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [o2 a ha, gm₁]
  obtain ⟨c₃, k₃, e₃, hk₃, t0, t1, t2, t3, gn₃, gm₃, gr₃, grm₃, go₃⟩ : ∃ c₃ k₃,
      Exec P W njS4 c₂ c₃ k₃ ∧ k₃ = 4 ∧ c₃.nreg 6620 = ml ∧ c₃.nreg 6621 = ILb ∧
      c₃.nreg 6622 = VLb ∧ c₃.nreg 6623 = OUTb ∧
      (∀ x, (x < 6620 ∨ 6623 < x) → c₃.nreg x = c₂.nreg x) ∧
      c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have hw₂ := e₂.wb_right
    unfold njS4
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (rw [q2 _ (by omega)]; simp only [r1, r7, r40, r42])
    simp only [upd_apply]; split_ifs <;> omega
  have em3 : ∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c₃.nmem a = c.nmem a := fun a ha => by
    rw [gm₃, m2 a ha]
  obtain ⟨c₄, k₄, e₄, hk₄, p1, p3, p4, p5, p6, p7⟩ := lcsProg_exec (P := P) c₃ e₃.wb_right t0 t1
    t2 t3 (by omega) (by omega) (by omega)
    (fun j hj => by rw [em3 _ (by omega)]; have := hIL j hj; omega)
    (fun i hi j hj h => iL i hi j hj (by rwa [em3 _ (by omega), em3 _ (by omega)] at h))
    (fun i hi j hj => by rw [em3 _ (by omega)]; have := hIL i hi; omega)
    (fun i hi j hj => by rw [em3 _ (by omega)]; have := hIL i hi; omega)
  have q4 : ∀ x, (x < 6624 ∨ 6627 < x) → c₄.nreg x = c₃.nreg x := p4
  obtain ⟨c₅, k₅, e₅, hk₅, u0, u1, u2, gn₅, gm₅, gr₅, grm₅, go₅⟩ : ∃ c₅ k₅,
      Exec P W njS5 c₄ c₅ k₅ ∧ k₅ = 3 ∧ c₅.nreg 6620 = mr ∧ c₅.nreg 6621 = IRb ∧
      c₅.nreg 6622 = VRb ∧ (∀ x, (x < 6620 ∨ 6622 < x) → c₅.nreg x = c₄.nreg x) ∧
      c₅.nmem = c₄.nmem ∧ c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    have hw₄ := e₄.wb_right
    unfold njS5
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (rw [q4 _ (by omega), gn₃ _ (by omega), q2 _ (by omega)]; simp only [r2, r8, r41])
    simp only [upd_apply]; split_ifs <;> omega
  have u3 : c₅.nreg 6623 = OUTb := by rw [gn₅ _ (by omega), q4 _ (by omega), t3]
  -- the memory of `c₄` off the targets of the left copy
  have em4 : ∀ a, (∀ j < ml, a ≠ OUTb + c.nmem (ILb + j)) → ¬ (OUTb ≤ a ∧ a < OUTb + m) →
      c₄.nmem a = c.nmem a := fun a h1 h2 => by
    rw [p3 a (fun j hj => by rw [em3 _ (by omega)]; exact h1 j hj), em3 a h2]
  have em5 : ∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c₅.nmem a = c.nmem a := fun a ha => by
    rw [gm₅]; exact em4 a (fun j hj h => ha ⟨by omega, by have := hIL j hj; omega⟩) ha
  obtain ⟨c₆, k₆, e₆, hk₆, v1, v3, v4, v5, v6, v7⟩ := lcsProg_exec (P := P) c₅ e₅.wb_right u0 u1
    u2 u3 (by omega) (by omega) (by omega)
    (fun j hj => by rw [em5 _ (by omega)]; have := hIR j hj; omega)
    (fun i hi j hj h => iR i hi j hj (by rwa [em5 _ (by omega), em5 _ (by omega)] at h))
    (fun i hi j hj => by rw [em5 _ (by omega)]; have := hIR i hi; omega)
    (fun i hi j hj => by rw [em5 _ (by omega)]; have := hIR i hi; omega)
  have eIR : ∀ k < mr, c₅.nmem (IRb + k) = c.nmem (IRb + k) := fun k hk => em5 _ (by omega)
  refine ⟨c₆, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆)))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄
    (.seq e₅ e₆)))), by omega, fun k hk => ?_, fun k hk hne => ?_, fun i hi h1 h2 => ?_,
    fun a ha => ?_, fun x hx => ?_, by rw [v5, gr₅, p5, gr₃, o4, gr₁],
    by rw [v6, grm₅, p6, grm₃, o5, grm₁], by rw [v7, go₅, p7, go₃, o6, go₁]⟩
  · rw [← eIR k hk, v1 k hk, em5 _ (by omega)]
  · rw [v3 _ (fun j hj => by rw [eIR j hj]; have := hne j hj; omega), gm₅]
    have := p1 k hk
    rwa [em3 _ (by have := hIL k hk; omega), em3 _ (by omega)] at this
  · rw [v3 _ (fun j hj => by rw [eIR j hj]; have := h2 j hj; omega), gm₅,
      p3 _ (fun j hj => by rw [em3 _ (by omega)]; have := h1 j hj; omega), gm₃]
    exact o1 i hi
  · rw [v3 _ (fun j hj h => ha ⟨by omega, by rw [eIR j hj] at h; have := hIR j hj; omega⟩),
      em5 a ha]
  · rw [v4 _ (by omega), gn₅ _ (by omega), q4 _ (by omega), gn₃ _ (by omega), q2 _ (by omega)]

/-- A strictly increasing array is injective. -/
lemma sinc_inj {f : ℕ → ℕ} {m : ℕ} (hf : ∀ i j, i < j → j < m → f i < f j) {i j : ℕ}
    (hi : i < m) (hj : j < m) (h : f i = f j) : i = j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · have := hf i j hij hj; omega
  · rfl
  · have := hf j i hij hi; omega

/-- **The sum of the children's flows into the parent's frame** (see the module docstring). -/
theorem njProg_exec (c : Config) (hc : WordsBounded W c) {d dl dr m ml mr Z : ℕ}
    (r4 : c.nreg 3004 = d) (r6 : c.nreg 3006 = dl) (r8 : c.nreg 3008 = dr)
    (hm : c.nmem d = m) (hml : c.nmem dl = ml) (hmr : c.nmem dr = mr) (hz : c.nmem (d + 3) = Z)
    (l1 : d + 4 + 7 * m ≤ dl) (l2 : dl + 4 + 7 * ml ≤ dr) (l3 : dr + 4 + 7 * mr ≤ W)
    (hp : ∀ i j, i < j → j < m → c.nmem (d + 4 + i) < c.nmem (d + 4 + j))
    (hql : ∀ k k', k < k' → k' < ml → c.nmem (dl + 4 + k) < c.nmem (dl + 4 + k'))
    (hqr : ∀ k k', k < k' → k' < mr → c.nmem (dr + 4 + k) < c.nmem (dr + 4 + k'))
    (hexl : ∀ k < ml, ∃ i < m, c.nmem (d + 4 + i) = c.nmem (dl + 4 + k))
    (hexr : ∀ k < mr, ∃ i < m, c.nmem (d + 4 + i) = c.nmem (dr + 4 + k)) :
    ∃ c' t, Exec P W njProg c c' t ∧ t ≤ 35 * m + 9 * (ml + mr) + 59 ∧
      (∀ i < m, ∀ k < mr, c.nmem (dr + 4 + k) = c.nmem (d + 4 + i) →
        c'.nmem (d + 4 + 6 * m + i) = c.nmem (dr + 4 + 6 * mr + k)) ∧
      (∀ i < m, ∀ k < ml, c.nmem (dl + 4 + k) = c.nmem (d + 4 + i) →
        (∀ k' < mr, c.nmem (dr + 4 + k') ≠ c.nmem (d + 4 + i)) →
        c'.nmem (d + 4 + 6 * m + i) = c.nmem (dl + 4 + 6 * ml + k)) ∧
      (∀ i < m, (∀ k < ml, c.nmem (dl + 4 + k) ≠ c.nmem (d + 4 + i)) →
        (∀ k < mr, c.nmem (dr + 4 + k) ≠ c.nmem (d + 4 + i)) →
        c'.nmem (d + 4 + 6 * m + i) = Z) ∧
      (∀ a, a < dl → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, x < 6260 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold njProg
  obtain ⟨c₁, k₁, e₁, hk₁, a30, a31, a32, a37, a38, a40, a41, a42, a44, il, ir, km, kr, gr₁,
    grm₁, go₁⟩ := njFront_exec (P := P) c hc r4 r6 r8 hm hml hmr hz l1 l2 l3 hp hql hqr hexl hexr
  have iL : ∀ k < ml, ∀ k' < ml, c₁.nmem (dl + 4 + ml + k) = c₁.nmem (dl + 4 + ml + k') →
      k = k' := fun k hk k' hk' h => by
    have h1 := (il k hk).2; have h2 := (il k' hk').2
    rw [h] at h1; rw [h1] at h2
    exact sinc_inj hql hk hk' h2
  have iR : ∀ k < mr, ∀ k' < mr, c₁.nmem (dr + 4 + mr + k) = c₁.nmem (dr + 4 + mr + k') →
      k = k' := fun k hk k' hk' h => by
    have h1 := (ir k hk).2; have h2 := (ir k' hk').2
    rw [h] at h1; rw [h1] at h2
    exact sinc_inj hqr hk hk' h2
  obtain ⟨c₂, k₂, e₂, hk₂, b1, b2, b3, b4, b5, b6, b7, b8⟩ := njBack_exec (P := P) c₁
    e₁.wb_right a30 a31 a32 a37 a38 a40 a41 a42 a44 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (fun k hk => (il k hk).1) (fun k hk => (ir k hk).1) iL iR
  have eVL : ∀ k < ml, c₁.nmem (dl + 4 + 6 * ml + k) = c.nmem (dl + 4 + 6 * ml + k) :=
    fun k hk => km _ (by omega) (by omega)
  have eVR : ∀ k < mr, c₁.nmem (dr + 4 + 6 * mr + k) = c.nmem (dr + 4 + 6 * mr + k) :=
    fun k hk => km _ (by omega) (by omega)
  -- the parent index of a child entry equal to `GP[i]` is `i`
  have pL : ∀ i < m, ∀ k < ml, c.nmem (dl + 4 + k) = c.nmem (d + 4 + i) →
      c₁.nmem (dl + 4 + ml + k) = i := fun i hi k hk h => by
    obtain ⟨a1, a2⟩ := il k hk
    exact sinc_inj hp a1 hi (by rw [a2, h])
  have pR : ∀ i < m, ∀ k < mr, c.nmem (dr + 4 + k) = c.nmem (d + 4 + i) →
      c₁.nmem (dr + 4 + mr + k) = i := fun i hi k hk h => by
    obtain ⟨a1, a2⟩ := ir k hk
    exact sinc_inj hp a1 hi (by rw [a2, h])
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fun i hi k hk h => ?_, fun i hi k hk h hn => ?_,
    fun i hi h1 h2 => ?_, fun a ha hb => ?_, fun x hx => ?_, by rw [b6, gr₁], by rw [b7, grm₁],
    by rw [b8, go₁]⟩
  · have := b1 k hk
    rw [pR i hi k hk h, eVR k hk] at this
    exact this
  · have := b2 k hk (fun k' hk' he => by
      rw [pL i hi k hk h] at he
      apply hn k' hk'
      have := (ir k' hk').2
      rw [he] at this; exact this.symm)
    rw [pL i hi k hk h, eVL k hk] at this
    exact this
  · refine b3 i hi (fun k hk he => h1 k hk ?_) (fun k hk he => h2 k hk ?_)
    · have := (il k hk).2; rw [he] at this; exact this.symm
    · have := (ir k hk).2; rw [he] at this; exact this.symm
  · rw [b4 a hb, km a (by omega) (by omega)]
  · rw [b5 x hx, kr x (by omega)]

end Exec

end BKMNW

end PlanarFlow
