module

public import PlanarFlow.BKMNW.MfFrameChild
public import PlanarFlow.BKMNW.MfFrameSem
public import PlanarFlow.BKMNW.MfLeaf

/-!
# The split of the max-flow driver around a separator program `sepP`

**The separator program is a parameter** `sepP` with the explicit specification **`SepPSpec`**:
at a node call `x = (.node l r π, Hs, σ)` of `Reach` in the frame `[d, e)` (the layout `Lay`,
`m` darts `en i`, `k = #Hs` holes), with the heap top `h = r3003` and a scratch base
`Sb = r6500 > h`, it writes from `Sb`, within `sT m` steps and using memory below `Sb + sR m k`
only:

* `LP[i] = bf (en i ∈ l.piece)` at `Sb + i`, `PF[i] = bf (en i ∈ π.path.darts)` at `Sb + m + i`,
  `CV[i] = bf (tail (en i) ∈ π.path.mverts)` at `Sb + 2 m + i` (`i < m`);
* `HM[j] = bf (¬ Disjoint Hs[j] π.path.mverts)` at `Sb + 3 m + j` (`j < k`);
* the tags `ntag l`, `ntag r` at `Sb + 3 m + k`, `Sb + 3 m + k + 1`;

keeping the memory below `Sb`, the registers `3000 … 3012` and the output. (A program computing
Miller's separator of the piece map from the frame arrays `GID`, `RV`, `SG`, `KR`, `HL`, and the
decomposition's choices, meets it; its cost `sT m = O(m log m)` is the charge `c.sep`.)

The rest of the split is fixed: `spPre` (`r6500 := Sb = h + 18 + 14 m`), `sepP`, `spSetA`,
`spSetB` (the bases), `sfFlagsA`, `sfFlagsB` (the per-dart data of the children), `spGlL`,
`sfChild` (the left child's frame at `h + 5`), `spGlR`, `sfChild` (the right child's frame at
`el + 5`), `spFin` (`r2998 := el`, `r2999 := er`): **`splitS sepP`**.

This file: `SepPSpec`, the programs, `spPre_exec`, `spSetA_exec`, `spSetB_exec`, **`lay_child`**
(the child's layout from the output of `sfChild` and the child's data).
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
/-- **The specification of the separator program** (see the module docstring). -/
def SepPSpec (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ)
    (I : Input) (W : ℕ) (sepP : Stmt) (sT : ℕ → ℕ) (sR : ℕ → ℕ → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e h Sb m : ℕ)
    (en : ℕ → D) (c : Config),
    FInL M Reach gid u S T Z (.node l r π, Hs, σ) d e c →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem → WordsBounded W c →
    c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3003 = h → c.nreg 6500 = Sb → e ≤ h → h < Sb →
    Sb + sR m Hs.length ≤ W →
    ∃ c' t, Exec I W sepP c c' t ∧ t ≤ sT m ∧ DRegKeep c c' ∧
      (∀ a < Sb, c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ i < m, c'.nmem (Sb + i) = bf (en i ∈ l.piece)) ∧
      (∀ i < m, c'.nmem (Sb + m + i) = bf (en i ∈ π.path.darts.toFinset)) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = bf (M.tail (en i) ∈ π.path.mverts)) ∧
      (∀ j < Hs.length, c'.nmem (Sb + 3 * m + j) =
        bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
      c'.nmem (Sb + 3 * m + Hs.length) = ntag l ∧ c'.nmem (Sb + 3 * m + Hs.length + 1) = ntag r

/-! ### The programs -/

/-- `r6500 := Sb = h + 18 + 14 m`. -/
def spPre : Stmt := block [.loadN 6510 3004, .constN 6550 14, .mulN 6551 6550 6510,
  .constN 6550 18, .addN 6552 3003 6550, .addN 6500 6552 6551]

/-- The bases, first part. -/
def spSetA : Stmt := block [.loadN 6510 3004, .constN 6550 1, .addN 6552 3004 6550,
  .loadN 6511 6552, .constN 6521 1, .constN 6539 0, .constN 6550 14, .mulN 6551 6550 6510,
  .constN 6550 18, .addN 6552 3003 6550, .addN 6543 6552 6551, .addN 6564 6543 6510,
  .addN 6540 6564 6510, .addN 6542 6540 6510, .addN 6554 6542 6511, .constN 6550 2,
  .addN 6544 6554 6550]

/-- The bases, second part. -/
def spSetB : Stmt := block [.constN 6550 4, .addN 6555 3004 6550, .addN 6545 6555 6510,
  .addN 6552 6545 6510, .addN 6552 6552 6510, .addN 6546 6552 6510, .addN 6541 6546 6510,
  .addN 6531 6544 6510, .addN 6532 6531 6510, .addN 6533 6532 6510, .addN 6534 6533 6510,
  .addN 6535 6534 6510, .addN 6566 6535 6510, .addN 6536 6566 6510, .addN 6547 6536 6511,
  .addN 6537 6547 6511, .addN 6562 6537 6511]

/-- The registers of `sfChild` for the left child. -/
def spGlL : Stmt := block [.copyN 6560 6510, .copyN 6561 3004, .copyN 6563 6535, .copyN 6565 6531,
  .copyN 6567 6533, .copyN 6568 6534, .constN 6550 5, .addN 6569 3003 6550, .copyN 6570 6548,
  .loadN 6571 6554, .constN 6550 3, .addN 6552 3004 6550, .loadN 6572 6552]

/-- The registers of `sfChild` for the right child. -/
def spGlR : Stmt := block [.copyN 6553 6597, .copyN 6565 6532, .constN 6550 5,
  .addN 6569 6597 6550, .constN 6550 1, .addN 6552 6554 6550, .loadN 6571 6552]

/-- `r2998 := el`, `r2999 := er`. -/
def spFin : Stmt := block [.copyN 2998 6553, .copyN 2999 6597]

/-- The bases. -/
def spSet : Stmt := .seq spSetA spSetB

/-- The per-dart data of the children. -/
def spFlags : Stmt := .seq sfFlagsA sfFlagsB

/-- The left child's frame. -/
def spChL : Stmt := .seq spGlL sfChild

/-- The right child's frame, and the bounds for the driver. -/
def spChR : Stmt := .seq spGlR (.seq sfChild spFin)

/-- The front of the split: the separator and the per-dart data of the children. -/
def spFront (sepP : Stmt) : Stmt := .seq spPre (.seq sepP (.seq spSet spFlags))

/-- **The split around the separator program `sepP`.** -/
def splitS (sepP : Stmt) : Stmt := .seq (spFront sepP) (.seq spChL spChR)



/-- The machine's flag of the tail of the dart `i` in the new hole. -/
def nhv (mem : ℕ → ℕ) (Sb d m i : ℕ) : ℕ :=
  nhF (mem (Sb + 2 * m + i)) (mem (d + 4 + 5 * m + i)) (mem (Sb + 3 * m + (mem (d + 4 + 5 * m + i) - 1)))

/-- The machine's flag of the hole `j` kept. -/
def hfv (mem : ℕ → ℕ) (Sb m j : ℕ) : ℕ := hfF (mem (Sb + 3 * m + j))

/-- **The registers of the split after `spSet`.** -/
structure SpRegs (c : Config) (d m k Sb Wb : ℕ) : Prop where
  r10 : c.nreg 6510 = m
  r11 : c.nreg 6511 = k
  r21 : c.nreg 6521 = 1
  r39 : c.nreg 6539 = 0
  r43 : c.nreg 6543 = Sb
  r64 : c.nreg 6564 = Sb + m
  r40 : c.nreg 6540 = Sb + 2 * m
  r42 : c.nreg 6542 = Sb + 3 * m
  r54 : c.nreg 6554 = Sb + 3 * m + k
  r44 : c.nreg 6544 = Wb
  r45 : c.nreg 6545 = d + 4 + m
  r46 : c.nreg 6546 = d + 4 + 4 * m
  r41 : c.nreg 6541 = d + 4 + 5 * m
  r31 : c.nreg 6531 = Wb + m
  r32 : c.nreg 6532 = Wb + 2 * m
  r33 : c.nreg 6533 = Wb + 3 * m
  r34 : c.nreg 6534 = Wb + 4 * m
  r35 : c.nreg 6535 = Wb + 5 * m
  r66 : c.nreg 6566 = Wb + 6 * m
  r36 : c.nreg 6536 = Wb + 7 * m
  r47 : c.nreg 6547 = Wb + 7 * m + k
  r37 : c.nreg 6537 = Wb + 7 * m + 2 * k
  r62 : c.nreg 6562 = Wb + 7 * m + 3 * k

/-- The registers of `SpRegs`. -/
def spReg (x : ℕ) : Prop :=
  x = 6510 ∨ x = 6511 ∨ x = 6521 ∨ x = 6539 ∨ x = 6543 ∨ x = 6564 ∨ x = 6540 ∨ x = 6542 ∨
    x = 6554 ∨ x = 6544 ∨ x = 6545 ∨ x = 6546 ∨ x = 6541 ∨ x = 6531 ∨ x = 6532 ∨ x = 6533 ∨
    x = 6534 ∨ x = 6535 ∨ x = 6566 ∨ x = 6536 ∨ x = 6547 ∨ x = 6537 ∨ x = 6562

/-- The registers of `SpRegs` are kept when the registers of `spReg` are. -/
lemma SpRegs.congr {c c' : Config} {d m k Sb Wb : ℕ} (h : SpRegs c d m k Sb Wb)
    (hr : ∀ x, spReg x → c'.nreg x = c.nreg x) : SpRegs c' d m k Sb Wb where
  r10 := by rw [hr _ (by unfold spReg; omega)]; exact h.r10
  r11 := by rw [hr _ (by unfold spReg; omega)]; exact h.r11
  r21 := by rw [hr _ (by unfold spReg; omega)]; exact h.r21
  r39 := by rw [hr _ (by unfold spReg; omega)]; exact h.r39
  r43 := by rw [hr _ (by unfold spReg; omega)]; exact h.r43
  r64 := by rw [hr _ (by unfold spReg; omega)]; exact h.r64
  r40 := by rw [hr _ (by unfold spReg; omega)]; exact h.r40
  r42 := by rw [hr _ (by unfold spReg; omega)]; exact h.r42
  r54 := by rw [hr _ (by unfold spReg; omega)]; exact h.r54
  r44 := by rw [hr _ (by unfold spReg; omega)]; exact h.r44
  r45 := by rw [hr _ (by unfold spReg; omega)]; exact h.r45
  r46 := by rw [hr _ (by unfold spReg; omega)]; exact h.r46
  r41 := by rw [hr _ (by unfold spReg; omega)]; exact h.r41
  r31 := by rw [hr _ (by unfold spReg; omega)]; exact h.r31
  r32 := by rw [hr _ (by unfold spReg; omega)]; exact h.r32
  r33 := by rw [hr _ (by unfold spReg; omega)]; exact h.r33
  r34 := by rw [hr _ (by unfold spReg; omega)]; exact h.r34
  r35 := by rw [hr _ (by unfold spReg; omega)]; exact h.r35
  r66 := by rw [hr _ (by unfold spReg; omega)]; exact h.r66
  r36 := by rw [hr _ (by unfold spReg; omega)]; exact h.r36
  r47 := by rw [hr _ (by unfold spReg; omega)]; exact h.r47
  r37 := by rw [hr _ (by unfold spReg; omega)]; exact h.r37
  r62 := by rw [hr _ (by unfold spReg; omega)]; exact h.r62

/-! ### The set-up blocks -/

section Exec

variable {P : Input} {W : ℕ}

theorem spPre_exec (c : Config) (hc : WordsBounded W c) {d h m : ℕ} (r4 : c.nreg 3004 = d)
    (r3 : c.nreg 3003 = h) (hm : c.nmem d = m) (w : h + 18 + 14 * m ≤ W) :
    ∃ c' k, Exec P W spPre c c' k ∧ k = 6 ∧ c'.nreg 6500 = h + 18 + 14 * m ∧
      (∀ x, (x < 6500 ∨ 6500 < x ∧ x < 6510 ∨ 6552 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold spPre
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r4, r3, hm]; omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r4, r3, hm])
    try omega

theorem spSetA_exec (c : Config) (hc : WordsBounded W c) {d h m k : ℕ} (r4 : c.nreg 3004 = d)
    (r3 : c.nreg 3003 = h) (hm : c.nmem d = m) (hk : c.nmem (d + 1) = k)
    (w : h + 18 + 14 * m + 3 * m + k + 2 ≤ W) (wd : d + 1 ≤ W) :
    ∃ c' t, Exec P W spSetA c c' t ∧ t = 17 ∧ c'.nreg 6510 = m ∧ c'.nreg 6511 = k ∧
      c'.nreg 6521 = 1 ∧ c'.nreg 6539 = 0 ∧ c'.nreg 6543 = h + 18 + 14 * m ∧
      c'.nreg 6564 = h + 18 + 14 * m + m ∧ c'.nreg 6540 = h + 18 + 14 * m + 2 * m ∧
      c'.nreg 6542 = h + 18 + 14 * m + 3 * m ∧ c'.nreg 6554 = h + 18 + 14 * m + 3 * m + k ∧
      c'.nreg 6544 = h + 18 + 14 * m + 3 * m + k + 2 ∧
      (∀ x, (x < 6510 ∨ (6555 < x ∧ x ≠ 6564)) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold spSetA
  exec_block
  all_goals try omega
  all_goals
    try (config_simp; simp (disch := omega) only [upd_other, upd_same, r4, r3, hm, hk]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r4, r3, hm, hk])
    try omega

theorem spSetB_exec (c : Config) (hc : WordsBounded W c) {d m k Wb : ℕ} (r4 : c.nreg 3004 = d)
    (r10 : c.nreg 6510 = m) (r11 : c.nreg 6511 = k) (r44 : c.nreg 6544 = Wb)
    (w1 : d + 4 + 5 * m ≤ W) (w2 : Wb + 7 * m + 3 * k ≤ W) :
    ∃ c' t, Exec P W spSetB c c' t ∧ t = 17 ∧ c'.nreg 6545 = d + 4 + m ∧
      c'.nreg 6546 = d + 4 + 4 * m ∧ c'.nreg 6541 = d + 4 + 5 * m ∧ c'.nreg 6531 = Wb + m ∧
      c'.nreg 6532 = Wb + 2 * m ∧ c'.nreg 6533 = Wb + 3 * m ∧ c'.nreg 6534 = Wb + 4 * m ∧
      c'.nreg 6535 = Wb + 5 * m ∧ c'.nreg 6566 = Wb + 6 * m ∧ c'.nreg 6536 = Wb + 7 * m ∧
      c'.nreg 6547 = Wb + 7 * m + k ∧ c'.nreg 6537 = Wb + 7 * m + 2 * k ∧
      c'.nreg 6562 = Wb + 7 * m + 3 * k ∧
      (∀ x, x ≠ 6550 → x ≠ 6555 → x ≠ 6545 → x ≠ 6552 → x ≠ 6546 → x ≠ 6541 → x ≠ 6531 →
        x ≠ 6532 → x ≠ 6533 → x ≠ 6534 → x ≠ 6535 → x ≠ 6566 → x ≠ 6536 → x ≠ 6547 →
        x ≠ 6537 → x ≠ 6562 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold spSetB
  exec_block
  all_goals try omega
  all_goals
    try (config_simp; simp (disch := omega) only [upd_other, upd_same, r4, r10, r11, r44]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r4, r10, r11, r44])
    try omega


/-- **The bases**: `spSetA ; spSetB` sets `SpRegs` (`34` steps). -/
theorem spSet_exec (c : Config) (hc : WordsBounded W c) {d h m k Sb Wb : ℕ}
    (r4 : c.nreg 3004 = d) (r3 : c.nreg 3003 = h) (hm : c.nmem d = m) (hk : c.nmem (d + 1) = k)
    (hSb : Sb = h + 18 + 14 * m) (hWb : Wb = Sb + 3 * m + k + 2) (w : Wb + 7 * m + 3 * k ≤ W)
    (wd : d + 4 + 5 * m ≤ W) :
    ∃ c' t, Exec P W spSet c c' t ∧ t = 34 ∧ SpRegs c' d m k Sb Wb ∧
      (∀ x, (x < 6510 ∨ 6566 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  subst hSb hWb
  obtain ⟨c₁, t₁, e₁, ht₁, a10, a11, a21, a39, a43, a64, a40, a42, a54, a44, n1, m1, rr1, rm1,
    o1⟩ := spSetA_exec (P := P) c hc r4 r3 hm hk (by omega) (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, b45, b46, b41, b31, b32, b33, b34, b35, b66, b36, b47, b37, b62, n2, m2,
    rr2, rm2, o2⟩ := spSetB_exec (P := P) c₁ e₁.wb_right (by rw [n1 _ (by omega), r4]) a10 a11
    a44 (by omega) w
  have G : ∀ x, (6510 ≤ x ∧ x ≤ 6544 ∧ x ≠ 6531 ∧ x ≠ 6532 ∧ x ≠ 6533 ∧ x ≠ 6534 ∧ x ≠ 6535 ∧
      x ≠ 6536 ∧ x ≠ 6537 ∧ x ≠ 6541) ∨ x = 6554 ∨ x = 6564 → c₂.nreg x = c₁.nreg x :=
    fun x hx => n2 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  refine ⟨c₂, _, .seq e₁ e₂, by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, b45, b46, b41, b31,
    b32, b33, b34, b35, b66, b36, b47, b37, b62⟩, fun x hx => ?_, by rw [m2, m1],
    by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
  · rw [G _ (by omega), a10]
  · rw [G _ (by omega), a11]
  · rw [G _ (by omega), a21]
  · rw [G _ (by omega), a39]
  · rw [G _ (by omega), a43]
  · rw [G _ (by omega), a64]
  · rw [G _ (by omega), a40]
  · rw [G _ (by omega), a42]
  · rw [G _ (by omega), a54]
  · rw [G _ (by omega), a44]
  · rw [n2 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), n1 x (by omega)]

set_option maxHeartbeats 2000000 in
/-- **The per-dart data of the children on the machine**: `sfFlagsA ; sfFlagsB`. -/
theorem spFlags_exec (c : Config) (hc : WordsBounded W c) {d m k Sb Wb : ℕ}
    (hR : SpRegs c d m k Sb Wb) (o1 : d + 4 + 6 * m ≤ Sb) (o2 : Sb + 3 * m + k + 2 ≤ Wb)
    (w : Wb + 7 * m + 3 * k ≤ W) (w' : m + k + 2 ≤ W)
    (hrv : ∀ i < m, c.nmem (d + 4 + m + i) < m) (hHL : ∀ i < m, c.nmem (d + 4 + 5 * m + i) ≤ k) :
    ∃ c' t, Exec P W spFlags c c' t ∧ t ≤ 91 * m + 21 * k + 32 ∧
      (∀ i < m, c'.nmem (Wb + m + i) = flL (c.nmem (Sb + i)) (nhv c.nmem Sb d m i)
        (nhv c.nmem Sb d m (c.nmem (d + 4 + m + i)))) ∧
      (∀ i < m, c'.nmem (Wb + 2 * m + i) = flR (c.nmem (Sb + i)) (nhv c.nmem Sb d m i)
        (nhv c.nmem Sb d m (c.nmem (d + 4 + m + i)))) ∧
      (∀ i < m, c'.nmem (Wb + 3 * m + i) =
        kcF (nhv c.nmem Sb d m i) (c.nmem (d + 4 + 4 * m + i))) ∧
      (∀ i < m, c'.nmem (Wb + 4 * m + i) = hcF (nhv c.nmem Sb d m i) (c.nmem (d + 4 + 5 * m + i))
        (cnt (hfv c.nmem Sb m) (c.nmem (d + 4 + 5 * m + i) - 1)) (cnt (hfv c.nmem Sb m) k + 1)) ∧
      (∀ i < m, c'.nmem (Wb + 5 * m + i) = i) ∧
      c'.nreg 6548 = cnt (hfv c.nmem Sb m) k + 1 ∧
      (∀ a, a < Wb → c'.nmem a = c.nmem a) ∧
      SpRegs c' d m k Sb Wb ∧
      (∀ x, (x < 6300 ∨ (6309 < x ∧ x < 6510) ∨ 6566 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₃, t₃, e₃, ht₃, f1, f2, f3, f4, m3, n3, rr3, rm3, o3⟩ := sfFlagsA_exec (P := P) c hc
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
  obtain ⟨c₄, t₄, e₄, ht₄, g1, g2, g3, g4, g5, m4, n4, rr4, rm4, o4⟩ := sfFlagsB_exec (P := P) c₃
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
  have q4 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₄.nreg x = c₃.nreg x := n4
  have RV3 : ∀ i < m, c₃.nmem (d + 4 + m + i) = c.nmem (d + 4 + m + i) := fun i hi =>
    m3' _ (by omega)
  refine ⟨c₄, _, .seq e₃ e₄, by omega, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, g5, ?_, fun a ha => ?_, hR3.congr fun x hx => ?_, fun x hx => ?_,
    by rw [rr4, rr3], by rw [rm4, rm3], by rw [o4, o3]⟩
  · have hr := hrv i hi
    rw [g2 i hi, m3' _ (by omega), NH i hi, RV3 i hi, NH _ hr]
  · have hr := hrv i hi
    rw [g3 i hi, m3' _ (by omega), NH i hi, RV3 i hi, NH _ hr]
  · rw [g4 i hi, NH i hi, m3' _ (by omega)]
  · have hl := hHL i hi
    rw [g1 i hi, NH i hi, hl3 i hi]
    unfold hcF
    split_ifs with h1 h2
    · rfl
    · have hz : hfv c.nmem Sb m (c.nmem (d + 4 + 5 * m + i) - 1) = 1 := by
        unfold nhv nhF at h1; unfold hfv hfF; split_ifs at h1 <;> simp_all
      rw [f4 _ (by omega) (by unfold hfv at hz; omega)]
      rfl
    · rfl
  · rw [q4 _ (by unfold vscr; omega) (by omega) (by omega), f3]; rfl
  · rw [m4 _ (by omega), m3' _ ha]
  · rw [q4 _ (by unfold vscr; unfold spReg at hx; omega) (by unfold spReg at hx; omega)
      (by unfold spReg at hx; omega)]
  · rw [q4 _ (by unfold vscr; omega) (by omega) (by omega), q3 _ (by omega)]

end Exec

/-! ### The layout of a child frame -/

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- **The layout of a child frame** from the output of `sfChild` and the child's data. -/
lemma lay_child {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem mem' : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (τc : ADec M) (Hc : List (Finset V)) (σc : Perm D)
    {mc dc : ℕ} {ix : ℕ → ℕ}
    (hix : ∀ k < mc, ix k < m ∧ en (ix k) ∈ pdarts M τc.piece Hc)
    (hsurj : ∀ y ∈ pdarts M τc.piece Hc, ∃ k < mc, en (ix k) = y)
    (hmono : ∀ k k', k < k' → k' < mc → ix k < ix k')
    (h0 : mem' dc = mc) (h1 : mem' (dc + 1) = Hc.length) (h2 : mem' (dc + 2) = ntag τc)
    (h3 : mem' (dc + 3) = Z)
    (hg : ∀ k < mc, mem' (dc + 4 + k) = mem (d + 4 + ix k))
    (hr : ∀ k < mc, mem' (dc + 4 + mc + k) < mc ∧
      en (ix (mem' (dc + 4 + mc + k))) = M.rev (en (ix k)))
    (hs : ∀ k < mc, mem' (dc + 4 + 2 * mc + k) < mc ∧
      en (ix (mem' (dc + 4 + 2 * mc + k))) = σc (en (ix k)))
    (hcp : ∀ k < mc, mem' (dc + 4 + 3 * mc + k) = mem (d + 4 + 3 * m + ix k))
    (hkr : ∀ k < mc, mem' (dc + 4 + 4 * mc + k) = lrk S T (hunion Hc) (M.tail (en (ix k))))
    (hhl : ∀ k < mc, mem' (dc + 4 + 5 * mc + k) = hlab Hc (M.tail (en (ix k)))) :
    Lay M gid u S T Z (τc, Hc, σc) mc (fun k => en (ix k)) dc mem' where
  hm := h0
  hk := h1
  tag := h2
  hz := h3
  en_mem k hk := (hix k hk).2
  en_surj := hsurj
  en_mono k k' hkk hk' := hL.en_mono _ _ (hmono k k' hkk hk') (hix k' hk').1
  gd k hk := by rw [hg k hk]; exact hL.gd _ (hix k hk).1
  rv k hk := hr k hk
  sg k hk := hs k hk
  cp k hk := by rw [hcp k hk]; exact hL.cp _ (hix k hk).1
  kr k hk := hkr k hk
  hl k hk := hhl k hk

end MfDrv

end BKMNW

end PlanarFlow
