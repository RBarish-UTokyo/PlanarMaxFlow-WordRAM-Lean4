module

public import PlanarFlow.BKMNW.S7Od5

/-!
# Stage 7 of `sepL` composed (I): hole flags, new hole, keys, classes

**`s7a = s7S1 ; s7S2 ; hfProg ; ytProg ; s7Cl`**: from a scratch base `Z = r7199` (above the
record and the other inputs) and the record's arrays as functions (`S7In`: the enumeration `g` of
the piece `P`, reverses `RP`, hole labels `HP`, vertex keys `VK`, the path's vertex flags `VF`,
the flags `NF` of `Nf`), within `300 n + 20 k + 200` steps:

* `HT[j + 1] = bf (¬ Disjoint Hs[j] C)` (`j < k`), `HT[0] = 0` at `HTb = Z + n`;
* `ID[i] = ID[j] ↔ g j ∈ clsF M P Nf Hs K ρ (g i)` and `ID[i] < nI = 3 (2 n + nk)` at
  `IDb = Cb + 12 n + nk + 2` (`Cb = Z + 2 n + k + 1`, `nk = n + k + 1`), given `HClosed` of the new
  hole and `IsCls` of `clsF` (from `exists_cls'`);
* the bases of stage 7 (III) in registers (`S7Regs`): `7150 = IDb`, `7151 = nI`,
  `7152 = Ob = IDb + n`, the gathers' `7133 = Sb + m`, `7134 = Sb + 2 m`, `7135 = k`,
  `7136 = HTb + 1`, `7137 = Sb + 3 m`.

Inputs: `7100 = n`, `7105 = k + 1`, `7101 = HPb`, `7102 = VFb`, `7106 = RPb`, `7109 = VKb`,
`7142 = NFb`, `7143 = K`, `7199 = Z`, `7193 = Sb`, `7130 = m`, `6521 = 1`.
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

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The bases of stage 7 (first half). -/
def s7S1 : Stmt :=
  block [.copyN 7103 7199, .addN 7104 7199 7100, .addN 7140 7104 7105, .addN 7140 7140 7100,
    .copyN 7107 7140, .addN 7108 7140 7100, .addN 7110 7108 7100, .addN 7110 7110 7100,
    .addN 7110 7110 7100, .addN 7141 7100 7105, .subN 7135 7105 6521, .addN 7136 7104 6521]

/-- The bases of stage 7 (second half). -/
def s7S2 : Stmt :=
  block [.addN 7151 7100 7100, .addN 7151 7151 7141, .addN 7194 7151 7151,
    .addN 7151 7194 7151, .addN 7196 7100 7100, .addN 7196 7196 7196, .addN 7197 7196 7196,
    .addN 7196 7197 7196, .addN 7150 7140 7196,
    .addN 7150 7150 7141, .addN 7150 7150 6521, .addN 7150 7150 6521, .addN 7152 7150 7100,
    .addN 7133 7193 7130, .addN 7134 7133 7130, .addN 7137 7134 7130]

/-- **Stage 7 (I)**: hole flags, new hole, keys, classes. -/
def s7a : Stmt := .seq (.seq s7S1 s7S2) (.seq (.seq hfProg ytProg) s7Cl)

/-- The bases of stage 7 after the set-up. -/
structure S7Regs (c : Config) (n k Z Sb m : ℕ) : Prop where
  r00 : c.nreg 7100 = n
  r05 : c.nreg 7105 = k + 1
  r99 : c.nreg 7199 = Z
  r93 : c.nreg 7193 = Sb
  r30 : c.nreg 7130 = m
  r21 : c.nreg 6521 = 1
  r03 : c.nreg 7103 = Z
  r04 : c.nreg 7104 = Z + n
  r40 : c.nreg 7140 = Z + 2 * n + k + 1
  r07 : c.nreg 7107 = Z + 2 * n + k + 1
  r08 : c.nreg 7108 = Z + 3 * n + k + 1
  r10 : c.nreg 7110 = Z + 6 * n + k + 1
  r41 : c.nreg 7141 = n + k + 1
  r35 : c.nreg 7135 = k
  r36 : c.nreg 7136 = Z + n + 1
  r51 : c.nreg 7151 = 3 * (2 * n + (n + k + 1))
  r50 : c.nreg 7150 = Z + 15 * n + 2 * k + 4
  r52 : c.nreg 7152 = Z + 16 * n + 2 * k + 4
  r33 : c.nreg 7133 = Sb + m
  r34 : c.nreg 7134 = Sb + 2 * m
  r37 : c.nreg 7137 = Sb + 3 * m

/-- The registers `S7Regs` reads. -/
def s7Reg (x : ℕ) : Prop :=
  x = 7100 ∨ x = 7105 ∨ x = 7199 ∨ x = 7193 ∨ x = 7130 ∨ x = 6521 ∨ x = 7103 ∨ x = 7104 ∨
    x = 7140 ∨ x = 7107 ∨ x = 7108 ∨ x = 7110 ∨ x = 7141 ∨ x = 7135 ∨ x = 7136 ∨ x = 7151 ∨
    x = 7150 ∨ x = 7152 ∨ x = 7133 ∨ x = 7134 ∨ x = 7137

lemma S7Regs.congr {c c' : Config} {n k Z Sb m : ℕ} (h : S7Regs c n k Z Sb m)
    (e : ∀ x, s7Reg x → c'.nreg x = c.nreg x) : S7Regs c' n k Z Sb m := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rwa [e _ (by unfold s7Reg; omega)]

section Exec

variable {P : Input} {W : ℕ}

theorem s7S1_exec (c : Config) (hc : WordsBounded W c) {n k Z : ℕ}
    (r00 : c.nreg 7100 = n) (r05 : c.nreg 7105 = k + 1) (r99 : c.nreg 7199 = Z)
    (r21 : c.nreg 6521 = 1) (w : Z + 6 * n + k + 1 ≤ W) :
    ∃ c' t, Exec P W s7S1 c c' t ∧ t = 12 ∧ c'.nreg 7103 = Z ∧ c'.nreg 7104 = Z + n ∧
      c'.nreg 7140 = Z + 2 * n + k + 1 ∧ c'.nreg 7107 = Z + 2 * n + k + 1 ∧
      c'.nreg 7108 = Z + 3 * n + k + 1 ∧ c'.nreg 7110 = Z + 6 * n + k + 1 ∧
      c'.nreg 7141 = n + k + 1 ∧ c'.nreg 7135 = k ∧ c'.nreg 7136 = Z + n + 1 ∧
      c'.nmem = c.nmem ∧
      (∀ x, x ≠ 7103 → x ≠ 7104 → x ≠ 7140 → x ≠ 7107 → x ≠ 7108 → x ≠ 7110 → x ≠ 7141 →
        x ≠ 7135 → x ≠ 7136 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold s7S1
  exec_block
  all_goals try (config_simp; (try simp only [r00, r05, r99, r21]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, fun x h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_,
    rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r00, r05, r99, r21]); done)
  all_goals try (config_simp; (try simp only [r00, r05, r99, r21]); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other])

theorem s7S2_exec (c : Config) (hc : WordsBounded W c) {n k Z Sb m : ℕ}
    (r00 : c.nreg 7100 = n) (r40 : c.nreg 7140 = Z + 2 * n + k + 1)
    (r41 : c.nreg 7141 = n + k + 1) (r93 : c.nreg 7193 = Sb) (r30 : c.nreg 7130 = m)
    (r21 : c.nreg 6521 = 1) (w : Z + 16 * n + 2 * k + 4 ≤ W) (w' : 9 * n + 3 * k + 3 ≤ W)
    (w'' : Sb + 3 * m ≤ W) :
    ∃ c' t, Exec P W s7S2 c c' t ∧ t = 16 ∧ c'.nreg 7151 = 3 * (2 * n + (n + k + 1)) ∧
      c'.nreg 7150 = Z + 15 * n + 2 * k + 4 ∧ c'.nreg 7152 = Z + 16 * n + 2 * k + 4 ∧
      c'.nreg 7133 = Sb + m ∧ c'.nreg 7134 = Sb + 2 * m ∧ c'.nreg 7137 = Sb + 3 * m ∧
      c'.nmem = c.nmem ∧
      (∀ x, x ≠ 7151 → x ≠ 7150 → x ≠ 7152 → x ≠ 7133 → x ≠ 7134 → x ≠ 7137 →
        (x < 7194 ∨ 7197 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold s7S2
  exec_block
  all_goals try (config_simp; (try simp only [r00, r40, r41, r93, r30, r21]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, fun x h1 h2 h3 h4 h5 h6 h7 => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r00, r40, r41, r93, r30, r21]); done)
  all_goals try (config_simp; (try simp only [r00, r40, r41, r93, r30, r21]); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other])

end Exec

section Sem

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

variable (M : CombMap D V F) in
/-- **The record's arrays for stage 7**, as functions. -/
structure S7In (P : Finset D) (Hs : List (Finset V)) (C : Finset V) (Nf : Finset D)
    (g : ℕ → D) (n : ℕ) (rp hp vk vf nf : ℕ → ℕ) : Prop where
  mem : ∀ i < n, g i ∈ P
  surj : ∀ d ∈ P, ∃ i < n, g i = d
  inj : ∀ i < n, ∀ j < n, g i = g j → i = j
  rp : ∀ i < n, rp i < n ∧ g (rp i) = M.rev (g i)
  hp : ∀ i < n, hp i = hlab Hs (M.tail (g i))
  vk : ∀ i < n, vk i < n ∧ ∀ j < n, (vk i = vk j ↔ M.tail (g i) = M.tail (g j))
  vf : ∀ i < n, vf i = bf (M.tail (g i) ∈ C)
  nf : ∀ i < n, nf i = bf (g i ∈ Nf)
  tail : ∀ v ∈ C, ∃ i < n, M.tail (g i) = v
  hd : Hs.Pairwise Disjoint

lemma bf_le_one7 (p : Prop) [Decidable p] : bf p ≤ 1 := by unfold bf; split_ifs <;> omega

lemma bf_pos_iff' (p : Prop) [Decidable p] : 0 < bf p ↔ p := by
  unfold bf; split_ifs with h <;> simp [h]

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- The set-up of stage 7. -/
theorem s7S_exec (c : Config) (hc : WordsBounded W c) {n k Z Sb m : ℕ}
    (r00 : c.nreg 7100 = n) (r05 : c.nreg 7105 = k + 1) (r99 : c.nreg 7199 = Z)
    (r93 : c.nreg 7193 = Sb) (r30 : c.nreg 7130 = m) (r21 : c.nreg 6521 = 1)
    (w : Z + 16 * n + 2 * k + 4 ≤ W) (w' : 9 * n + 3 * k + 3 ≤ W) (w3 : Sb + 3 * m ≤ W) :
    ∃ c' t, Exec P W (.seq s7S1 s7S2) c c' t ∧ t = 28 ∧ S7Regs c' n k Z Sb m ∧
      c'.nmem = c.nmem ∧
      (∀ x, (x < 7103 ∨ x = 7105 ∨ x = 7106 ∨ x = 7109 ∨ (7110 < x ∧ x < 7133) ∨
        (7137 < x ∧ x < 7140) ∨ (7141 < x ∧ x < 7150) ∨ (7152 < x ∧ x < 7194) ∨ 7197 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a3, a4, a40, a7, a8, a10, a41, a35, a36, m1, n1, rr1, rm1, o1⟩ :=
    s7S1_exec (P := P) c hc r00 r05 r99 r21 (by omega)
  have q1 : ∀ x, (x < 7103 ∨ x = 7105 ∨ x = 7106 ∨ x = 7109 ∨ (7110 < x ∧ x < 7135) ∨
      (7136 < x ∧ x < 7140) ∨ 7141 < x) → c₁.nreg x = c.nreg x := fun x hx =>
    n1 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, b51, b50, b52, b33, b34, b37, m2, n2, rr2, rm2, o2⟩ :=
    s7S2_exec (P := P) c₁ e₁.wb_right (n := n) (k := k) (Z := Z) (Sb := Sb) (m := m)
      ((q1 _ (by omega)).trans r00) a40 a41 ((q1 _ (by omega)).trans r93)
      ((q1 _ (by omega)).trans r30) ((q1 _ (by omega)).trans r21) w w' w3
  have q2 : ∀ x, (x ≠ 7151 ∧ x ≠ 7150 ∧ x ≠ 7152 ∧ x ≠ 7133 ∧ x ≠ 7134 ∧ x ≠ 7137 ∧
      (x < 7194 ∨ 7197 < x)) → c₂.nreg x = c₁.nreg x := fun x hx =>
    n2 x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2
  refine ⟨c₂, _, .seq e₁ e₂, by omega,
    ⟨by rw [q2 _ (by omega), q1 _ (by omega)]; exact r00,
      by rw [q2 _ (by omega), q1 _ (by omega)]; exact r05,
      by rw [q2 _ (by omega), q1 _ (by omega)]; exact r99,
      by rw [q2 _ (by omega), q1 _ (by omega)]; exact r93,
      by rw [q2 _ (by omega), q1 _ (by omega)]; exact r30,
      by rw [q2 _ (by omega), q1 _ (by omega)]; exact r21,
      by rw [q2 _ (by omega)]; exact a3, by rw [q2 _ (by omega)]; exact a4,
      by rw [q2 _ (by omega)]; exact a40, by rw [q2 _ (by omega)]; exact a7,
      by rw [q2 _ (by omega)]; exact a8, by rw [q2 _ (by omega)]; exact a10,
      by rw [q2 _ (by omega)]; exact a41, by rw [q2 _ (by omega)]; exact a35,
      by rw [q2 _ (by omega)]; exact a36, b51, b50, b52, b33, b34, b37⟩,
    by rw [m2, m1], fun x hx => by rw [q2 _ (by omega), q1 _ (by omega)],
    by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩

/-- The new hole and the keys of the record's darts, as the classes program reads them. -/
structure S7H {M : CombMap D V F} (Ps Nf : Finset D) (Hs : List (Finset V)) (ρ : HPath M)
    (g : ℕ → D) (n k Z RPb NFb : ℕ) (mem : ℕ → ℕ) : Prop where
  ht0 : mem (Z + n) = 0
  htj : ∀ j < k, mem (Z + n + 1 + j) = bf (¬ Disjoint (Hs.getD j ∅) ρ.mverts)
  cls : ClsEnum M Ps Nf Hs (newHole Hs ρ.mverts) n g (fun i => mem (RPb + i))
      (fun i => mem (Z + 2 * n + k + 1 + 4 * n + i)) (fun i => mem (Z + 2 * n + k + 1 + i))
      (fun i => mem (Z + 2 * n + k + 1 + n + i)) (fun i => mem (NFb + i))
  tk : ∀ i < n, mem (Z + 2 * n + k + 1 + 4 * n + i) < n + k + 1

set_option maxHeartbeats 4000000 in
/-- **The hole flags, the new hole and the keys** (`hfProg ; ytProg` from `S7Regs`). -/
theorem s7H_exec {M : CombMap D V F} {Ps Nf : Finset D} {Hs : List (Finset V)}
    {ρ : HPath M} {g : ℕ → D} (c : Config) (hc : WordsBounded W c)
    {n k Z Sb m HPb VFb RPb VKb NFb : ℕ} {rp hp vk vf nf : ℕ → ℕ}
    (hI : S7In M Ps Hs ρ.mverts Nf g n rp hp vk vf nf) (hk : Hs.length = k)
    (R : S7Regs c n k Z Sb m)
    (r01 : c.nreg 7101 = HPb) (r02 : c.nreg 7102 = VFb) (r06 : c.nreg 7106 = RPb)
    (r09 : c.nreg 7109 = VKb)
    (mHP : ∀ i < n, c.nmem (HPb + i) = hp i) (mVF : ∀ i < n, c.nmem (VFb + i) = vf i)
    (mRP : ∀ i < n, c.nmem (RPb + i) = rp i) (mVK : ∀ i < n, c.nmem (VKb + i) = vk i)
    (mNF : ∀ i < n, c.nmem (NFb + i) = nf i)
    (lay : HPb + n ≤ Z ∧ VFb + n ≤ Z ∧ RPb + n ≤ Z ∧ VKb + n ≤ Z ∧ NFb + n ≤ Z ∧
      Z + 17 * n + 2 * k + 4 ≤ W) (hW : 9 * n + 3 * k + 6 ≤ W) :
    ∃ c' t, Exec P W (.seq hfProg ytProg) c c' t ∧ t ≤ 53 * n + 6 * k + 40 ∧
      S7Regs c' n k Z Sb m ∧ S7H Ps Nf Hs ρ g n k Z RPb NFb c'.nmem ∧
      (∀ a, (a < Z ∨ Z + 7 * n + k + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → (x < 6030 ∨ 6035 < x) → x ≠ 7120 →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lay
  have hd := hI.hd
  have hHf : HfRegs c n k HPb VFb Z (Z + n) RPb (Z + 2 * n + k + 1) (Z + 3 * n + k + 1) VKb
      (Z + 6 * n + k + 1) :=
    ⟨R.r00, r01, r02, R.r03, R.r04, R.r05, r06, R.r07, R.r08, r09, R.r10, R.r21⟩
  have hp_le : ∀ i < n, hp i ≤ k := fun i hi => by rw [hI.hp i hi, ← hk]; exact hlab_le _ _
  have vf_le : ∀ i < n, vf i ≤ 1 := fun i hi => by rw [hI.vf i hi]; exact bf_le_one7 _
  obtain ⟨c₃, t₃, e₃, ht₃, h0, hT, fm3, fn3, fr3, frm3, fo3⟩ := hfProg_exec (P := P) c hc hHf
    (hp := hp) (vf := vf) mHP mVF vf_le hp_le ⟨l1, l2, by omega, by omega⟩ (by omega) (by omega)
  have R3 : S7Regs c₃ n k Z Sb m := R.congr fun x hx =>
    fn3 x (by unfold vscr; unfold s7Reg at hx; omega) (by unfold s7Reg at hx; omega)
      (by unfold s7Reg at hx; omega) (by unfold s7Reg at hx; omega)
      (by unfold s7Reg at hx; omega)
  have hHf3 : HfRegs c₃ n k HPb VFb Z (Z + n) RPb (Z + 2 * n + k + 1) (Z + 3 * n + k + 1) VKb
      (Z + 6 * n + k + 1) := hHf.congr fun x hx =>
    fn3 x (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
  set ht : ℕ → ℕ := fun h => c₃.nmem (Z + n + h) with hht
  have ht0 : ht 0 = 0 := by simp only [hht, add_zero]; exact h0
  have htj : ∀ j < k, ht (j + 1) = bf (¬ Disjoint (Hs.getD j ∅) ρ.mverts) := by
    intro j hj
    simp only [hht]
    rw [hT (j + 1) (by omega) (by omega)]
    have := hf_sem (M := M) hd (C := ρ.mverts) (g := g) (n := n) (hp := hp) (vf := vf) hI.hp
      hI.vf hI.tail (j := j) (by omega)
    unfold bf
    by_cases hx : ∃ i < n, hp i * vf i = j + 1
    · rw [iteT hx, iteT (this.1 hx)]
    · rw [iteF hx, iteF (fun h => hx (this.2 h))]
  have ht1 : ∀ h ≤ k, ht h ≤ 1 := by
    intro h hh
    rcases Nat.eq_zero_or_pos h with rfl | hp'
    · rw [ht0]; omega
    · obtain ⟨j, rfl⟩ : ∃ j, h = j + 1 := ⟨h - 1, by omega⟩
      rw [htj j (by omega)]; exact bf_le_one7 _
  have hhtpos : ∀ j < Hs.length, (0 < ht (j + 1) ↔ ¬ Disjoint (Hs.getD j ∅) ρ.mverts) :=
    fun j hj => by rw [htj j (by omega), bf_pos_iff']
  have M3 : ∀ a, a < Z → c₃.nmem a = c.nmem a := fun a ha => fm3 a (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, Y1, Y2, Y3, fm4, fn4, fr4, frm4, fo4⟩ := ytProg_exec (P := P) c₃
    e₃.wb_right hHf3 (hp := hp) (vf := vf) (rp := rp) (vk := vk) (ht := ht)
    (fun i hi => by rw [M3 _ (by omega)]; exact mHP i hi)
    (fun i hi => by rw [M3 _ (by omega)]; exact mVF i hi)
    (fun i hi => by rw [M3 _ (by omega)]; exact mRP i hi)
    (fun i hi => by rw [M3 _ (by omega)]; exact mVK i hi)
    (fun h hh => rfl) vf_le hp_le ht1 (fun i hi => (hI.rp i hi).1) (fun i hi => (hI.vk i hi).1)
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩ (by omega)
  have R4 : S7Regs c₄ n k Z Sb m := R3.congr fun x hx =>
    fn4 x (by unfold vscr; unfold s7Reg at hx; omega) (by unfold s7Reg at hx; omega)
      (by unfold s7Reg at hx; omega)
  have M4 : ∀ a, a < Z → c₄.nmem a = c.nmem a := fun a ha => by
    rw [fm4 a (by omega)]; exact M3 a ha
  have hnh : ∀ i < n, (0 < vf i + ht (hp i) ↔ M.tail (g i) ∈ newHole Hs ρ.mverts) := by
    intro i hi
    rw [hI.vf i hi, hI.hp i hi]
    exact yt_sem hd ht0 hhtpos
  refine ⟨c₄, _, .seq e₃ e₄, by omega, R4, ⟨?_, fun j hj => ?_, ?_, fun i hi => ?_⟩,
    fun a ha => ?_, fun x a1 a2 a3 a4 a5 => ?_, by rw [fr4, fr3], by rw [frm4, frm3],
    by rw [fo4, fo3]⟩
  · rw [fm4 _ (by omega)]; exact h0
  · rw [fm4 _ (by omega), show Z + n + 1 + j = Z + n + (j + 1) by omega]
    exact htj j hj
  · refine ⟨hI.mem, hI.surj, hI.inj, fun i hi => ?_, fun i hi => ?_, fun i hi j hj => ?_,
      fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [M4 _ (by omega), mRP i hi]; exact (hI.rp i hi).1
    · rw [M4 _ (by omega), mRP i hi]; exact (hI.rp i hi).2
    · rw [show Z + 2 * n + k + 1 + 4 * n + i = Z + 6 * n + k + 1 + i by omega,
        show Z + 2 * n + k + 1 + 4 * n + j = Z + 6 * n + k + 1 + j by omega, Y3 i hi, Y3 j hj,
        hI.hp i hi, hI.hp j hj]
      exact tk_sem hd (hI.vk i hi).1 (hI.vk j hj).1 ((hI.vk i hi).2 j hj)
    · rw [Y1 i hi]; exact hnh i hi
    · rw [show Z + 2 * n + k + 1 + n + i = Z + 3 * n + k + 1 + i by omega, Y2 i hi]
      have h1 := hnh _ (hI.rp i hi).1
      rw [(hI.rp i hi).2, CombMap.tail_rev] at h1
      exact h1
    · rw [M4 _ (by omega), mNF i hi, hI.nf i hi]
      exact bf_pos_iff' _
  · rw [show Z + 2 * n + k + 1 + 4 * n + i = Z + 6 * n + k + 1 + i by omega, Y3 i hi, tkV_eq]
    have := (hI.vk i hi).1; have := hp_le i hi
    split_ifs <;> omega
  · rw [fm4 a (by omega), fm3 a (by omega)]
  · rw [fn4 x a1 a2 a3, fn3 x a1 a2 a3 a4 a5]

set_option maxHeartbeats 4000000 in
/-- **Stage 7 (I) composed** (see the module docstring). -/
theorem s7a_exec {M : CombMap D V F} {Ps Nf : Finset D} {Hs : List (Finset V)} {K : ℕ}
    {ρ : HPath M} {g : ℕ → D} (c : Config) (hc : WordsBounded W c)
    {n k Z Sb m HPb VFb RPb VKb NFb : ℕ} {rp hp vk vf nf : ℕ → ℕ}
    (hI : S7In M Ps Hs ρ.mverts Nf g n rp hp vk vf nf) (hk : Hs.length = k)
    (hY : HClosed Hs (newHole Hs ρ.mverts)) (hC : IsCls Ps (clsF M Ps Nf Hs K ρ))
    (hNf : Nf ⊆ Ps)
    (r00 : c.nreg 7100 = n) (r05 : c.nreg 7105 = k + 1) (r99 : c.nreg 7199 = Z)
    (r93 : c.nreg 7193 = Sb) (r30 : c.nreg 7130 = m) (r21 : c.nreg 6521 = 1)
    (r01 : c.nreg 7101 = HPb) (r02 : c.nreg 7102 = VFb) (r06 : c.nreg 7106 = RPb)
    (r09 : c.nreg 7109 = VKb) (r42 : c.nreg 7142 = NFb) (r43 : c.nreg 7143 = K)
    (mHP : ∀ i < n, c.nmem (HPb + i) = hp i) (mVF : ∀ i < n, c.nmem (VFb + i) = vf i)
    (mRP : ∀ i < n, c.nmem (RPb + i) = rp i) (mVK : ∀ i < n, c.nmem (VKb + i) = vk i)
    (mNF : ∀ i < n, c.nmem (NFb + i) = nf i)
    (lay : HPb + n ≤ Z ∧ VFb + n ≤ Z ∧ RPb + n ≤ Z ∧ VKb + n ≤ Z ∧ NFb + n ≤ Z ∧
      Z + 17 * n + 2 * k + 4 ≤ W) (hW : 9 * n + 3 * k + 6 ≤ W) (w3 : Sb + 3 * m ≤ W) :
    ∃ c' t, Exec P W s7a c c' t ∧ t ≤ 300 * n + 20 * k + 200 ∧ S7Regs c' n k Z Sb m ∧
      c'.nmem (Z + n) = 0 ∧
      (∀ j < k, c'.nmem (Z + n + 1 + j) = bf (¬ Disjoint (Hs.getD j ∅) ρ.mverts)) ∧
      (∀ i < n, ∀ j < n, (c'.nmem (Z + 15 * n + 2 * k + 4 + i) =
        c'.nmem (Z + 15 * n + 2 * k + 4 + j) ↔ g j ∈ clsF M Ps Nf Hs K ρ (g i))) ∧
      (∀ i < n, c'.nmem (Z + 15 * n + 2 * k + 4 + i) < 3 * (2 * n + (n + k + 1))) ∧
      (∀ a, (a < Z ∨ Z + 16 * n + 2 * k + 4 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4400 ∨ (4467 < x ∧ x < 4910) ∨ (4916 < x ∧ x < 6030) ∨
        (6035 < x ∧ x < 6520) ∨ x = 6521 ∨ (6529 < x ∧ x < 7103) ∨ x = 7105 ∨ x = 7106 ∨
        x = 7109 ∨ (7110 < x ∧ x < 7120) ∨ (7120 < x ∧ x < 7133) ∨ (7137 < x ∧ x < 7140) ∨
        (7141 < x ∧ x < 7150) ∨ (7152 < x ∧ x < 7194) ∨ (7197 < x)) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lay
  unfold s7a
  obtain ⟨c₂, t₂, e₂, ht₂, R2, m2, n2, rr2, rm2, o2⟩ := s7S_exec (P := P) c hc r00 r05 r99 r93
    r30 r21 (by omega) (by omega) w3
  have q : ∀ x, (x = 7101 ∨ x = 7102 ∨ x = 7106 ∨ x = 7109 ∨ x = 7142 ∨ x = 7143) →
      c₂.nreg x = c.nreg x := fun x hx => n2 x (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, R4, H4, fm4, fn4, fr4, frm4, fo4⟩ := s7H_exec (P := P) c₂ e₂.wb_right
    hI hk R2 ((q _ (by omega)).trans r01) ((q _ (by omega)).trans r02)
    ((q _ (by omega)).trans r06) ((q _ (by omega)).trans r09)
    (by rw [m2]; exact mHP) (by rw [m2]; exact mVF) (by rw [m2]; exact mRP)
    (by rw [m2]; exact mVK) (by rw [m2]; exact mNF) ⟨l1, l2, l3, l4, l5, l6⟩ hW
  have q4 : ∀ x, (x = 7106 ∨ x = 7142 ∨ x = 7143) → c₄.nreg x = c.nreg x := fun x hx => by
    rw [fn4 x (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega),
      q _ (by omega)]
  obtain ⟨c₅, t₅, e₅, ht₅, C1, C2, fm5, fn5, fr5, frm5, fo5⟩ := s7Cl_exec (P := P) c₄
    e₄.wb_right (n := n) (nk := n + k + 1) (RPb := RPb) (Cb := Z + 2 * n + k + 1) (NFs := NFb)
    (K := K) R4.r00 ((q4 _ (by omega)).trans r06) R4.r40 R4.r41 ((q4 _ (by omega)).trans r42)
    ((q4 _ (by omega)).trans r43) R4.r21 H4.cls hNf hY hC H4.tk
    ⟨by omega, by omega, by omega⟩ (by omega)
  have R5 : S7Regs c₅ n k Z Sb m := R4.congr fun x hx =>
    fn5 x (by unfold s7Reg at hx; omega)
  refine ⟨c₅, _, .seq e₂ (.seq e₄ e₅), by omega, R5, ?_, fun j hj => ?_,
    fun i hi j hj => ?_, fun i hi => ?_, fun a ha => ?_, fun x hx => ?_,
    by rw [fr5, fr4, rr2], by rw [frm5, frm4, rm2], by rw [fo5, fo4, o2]⟩
  · rw [fm5 _ (by omega)]; exact H4.ht0
  · rw [fm5 _ (by omega)]; exact H4.htj j hj
  · rw [show Z + 15 * n + 2 * k + 4 + i = Z + 2 * n + k + 1 + 12 * n + (n + k + 1) + 2 + i by
      omega, show Z + 15 * n + 2 * k + 4 + j = Z + 2 * n + k + 1 + 12 * n + (n + k + 1) + 2 + j
      by omega]
    exact C1 i hi j hj
  · rw [show Z + 15 * n + 2 * k + 4 + i = Z + 2 * n + k + 1 + 12 * n + (n + k + 1) + 2 + i by
      omega]
    exact C2 i hi
  · rw [fm5 a (by omega), fm4 a (by omega), m2]
  · rw [fn5 x (by omega), fn4 x (by unfold vscr; omega) (by omega) (by omega) (by omega)
      (by omega), n2 x (by omega)]

end Sem

end MfDrv

end BKMNW

end PlanarFlow
