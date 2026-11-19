module

public import PlanarFlow.BKMNW.LgWtP

/-!
# The large-piece separator, stage 4: the weights program `lgWt`

`lgWt = lgWtA ; lgWtB ; lgWtC` writes the weights `EX[j]` (`j < n'`) of the certificate of a
large piece on the enumeration of the piece map of the core (stage 2), at `b + 3 n'` (the field
`ex` of `LvIn`). Scratch from `Yb` (`n` darts of the record, `kk` holes):

| array | base | size |
| --- | --- | --- |
| `CF2` (flags of the core) | `Yb` | `n` |
| `VK` (run keys) | `Yb + n` | `n` |
| `CK` (class keys of the tails) | `Yb + 2n` | `n` |
| `AK` (class keys of the anchor vertices) | `Yb + 3n` | `n` |
| `KT` (keys of the core's darts) | `Yb + 4n` | `n'` |
| `T2` (first core index of a key) | `Yb + 5n` | `kk + n + 1` |
| junk output of `fiProg` | `Yb + 6n + kk + 1` | `n'` |
| `SF` (representatives) | `Yb + 7n + kk + 1` | `n` |
| `AV` (their anchors) | `Yb + 8n + kk + 1` | `n` |
| `T1` (first core index of a hole) | `Yb + 9n + kk + 1` | `kk + 1` |
| `EXK` (`pcExf`) | `Yb + 9n + 2kk + 2` | `n'` |
| `EXM` (scatter-add of `2`) | `Yb + 10n + 2kk + 2` | `n' + 1` |
| the word `2` | `Yb + 11n + 2kk + 3` | `1` |

* `WtR0` (input registers), `WtRegs` (all bases), `wtW` (registers written after the set-up),
  `WtRegs.congr`;
* `lw0` (set-up), **`lgWtA`** (`lw0 ; cfScan ; vkLoop ; ckScan ; akScan`), **`lgWtA_exec`**.
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

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

/-- The input registers of the weights program. -/
structure WtR0 (c : Config) (n RPb HPb VPb IXb b n' kk K Yb : ℕ) : Prop where
  r00 : c.nreg 5800 = n
  r01 : c.nreg 5801 = RPb
  r02 : c.nreg 5802 = HPb
  r03 : c.nreg 5803 = VPb
  r06 : c.nreg 5806 = 1
  r07 : c.nreg 5807 = 2
  r09 : c.nreg 5809 = IXb
  r10 : c.nreg 5810 = b
  r11 : c.nreg 5811 = n'
  r70 : c.nreg 5870 = kk
  r71 : c.nreg 5871 = K
  r72 : c.nreg 5872 = Yb
  r21 : c.nreg 6521 = 1

/-- **All the registers of the weights program** after the set-up. -/
structure WtRegs (c : Config) (n RPb HPb VPb IXb b n' kk K Yb : ℕ) : Prop where
  r00 : c.nreg 5800 = n
  r01 : c.nreg 5801 = RPb
  r02 : c.nreg 5802 = HPb
  r03 : c.nreg 5803 = VPb
  r04 : c.nreg 5804 = Yb
  r06 : c.nreg 5806 = 1
  r07 : c.nreg 5807 = 2
  r09 : c.nreg 5809 = IXb
  r10 : c.nreg 5810 = b
  r11 : c.nreg 5811 = n'
  r70 : c.nreg 5870 = kk
  r71 : c.nreg 5871 = K
  r72 : c.nreg 5872 = Yb
  r73 : c.nreg 5873 = Yb + n
  r74 : c.nreg 5874 = Yb + 2 * n
  r75 : c.nreg 5875 = Yb + 3 * n
  r76 : c.nreg 5876 = Yb + 7 * n + kk + 1
  r77 : c.nreg 5877 = Yb + 8 * n + kk + 1
  r78 : c.nreg 5878 = Yb + 4 * n
  r79 : c.nreg 5879 = Yb + 5 * n
  r80 : c.nreg 5880 = Yb + 6 * n + kk + 1
  r81 : c.nreg 5881 = Yb + 9 * n + kk + 1
  r82 : c.nreg 5882 = Yb + 9 * n + 2 * kk + 2
  r83 : c.nreg 5883 = Yb + 10 * n + 2 * kk + 2
  r84 : c.nreg 5884 = Yb + 11 * n + 2 * kk + 3
  r85 : c.nreg 5885 = kk + n + 1
  r86 : c.nreg 5886 = kk + 1
  r87 : c.nreg 5887 = n' + 1
  r88 : c.nreg 5888 = b + n'
  r89 : c.nreg 5889 = b + 3 * n'
  r21 : c.nreg 6521 = 1

/-- The registers written by the loops of the weights program. -/
def wtW (x : ℕ) : Prop :=
  (5890 ≤ x ∧ x ≤ 5896) ∨ x = 6520 ∨ (6522 ≤ x ∧ x ≤ 6529) ∨ (6210 ≤ x ∧ x ≤ 6217) ∨
    (4480 ≤ x ∧ x ≤ 4492) ∨ (4630 ≤ x ∧ x ≤ 4639)

lemma WtRegs.congr {c c' : Config} {n RPb HPb VPb IXb b n' kk K Yb : ℕ}
    (h : WtRegs c n RPb HPb VPb IXb b n' kk K Yb) (he : ∀ x, ¬ wtW x → c'.nreg x = c.nreg x) :
    WtRegs c' n RPb HPb VPb IXb b n' kk K Yb := by
  have q : ∀ x, (5800 ≤ x ∧ x ≤ 5889) ∨ x = 6521 → c'.nreg x = c.nreg x := fun x hx =>
    he x (by unfold wtW; omega)
  exact ⟨by rw [q _ (by omega)]; exact h.r00, by rw [q _ (by omega)]; exact h.r01,
    by rw [q _ (by omega)]; exact h.r02, by rw [q _ (by omega)]; exact h.r03,
    by rw [q _ (by omega)]; exact h.r04, by rw [q _ (by omega)]; exact h.r06,
    by rw [q _ (by omega)]; exact h.r07, by rw [q _ (by omega)]; exact h.r09,
    by rw [q _ (by omega)]; exact h.r10, by rw [q _ (by omega)]; exact h.r11,
    by rw [q _ (by omega)]; exact h.r70, by rw [q _ (by omega)]; exact h.r71,
    by rw [q _ (by omega)]; exact h.r72, by rw [q _ (by omega)]; exact h.r73,
    by rw [q _ (by omega)]; exact h.r74, by rw [q _ (by omega)]; exact h.r75,
    by rw [q _ (by omega)]; exact h.r76, by rw [q _ (by omega)]; exact h.r77,
    by rw [q _ (by omega)]; exact h.r78, by rw [q _ (by omega)]; exact h.r79,
    by rw [q _ (by omega)]; exact h.r80, by rw [q _ (by omega)]; exact h.r81,
    by rw [q _ (by omega)]; exact h.r82, by rw [q _ (by omega)]; exact h.r83,
    by rw [q _ (by omega)]; exact h.r84, by rw [q _ (by omega)]; exact h.r85,
    by rw [q _ (by omega)]; exact h.r86, by rw [q _ (by omega)]; exact h.r87,
    by rw [q _ (by omega)]; exact h.r88, by rw [q _ (by omega)]; exact h.r89,
    by rw [q _ (by omega)]; exact h.r21⟩

/-- **The set-up**: the bases from `Yb`, `n`, `kk`, `b`, `n'`, and the word `2`. -/
def lw0 : Stmt :=
  block [.copyN 5804 5872, .addN 5873 5872 5800, .addN 5874 5873 5800, .addN 5875 5874 5800,
    .addN 5878 5875 5800, .addN 5879 5878 5800, .addN 5885 5870 5800, .addN 5885 5885 5806,
    .addN 5880 5879 5885, .addN 5876 5880 5800, .addN 5877 5876 5800, .addN 5881 5877 5800,
    .addN 5886 5870 5806, .addN 5882 5881 5886, .addN 5883 5882 5800, .addN 5884 5883 5800,
    .addN 5884 5884 5806, .addN 5887 5811 5806, .addN 5888 5810 5811, .addN 5889 5888 5811,
    .addN 5889 5889 5811, .constN 5899 2, .storeN 5884 5899]

/-- **Part A of the weights program**: the set-up, the flags of the core, the run keys, the class
keys of the tails and of the anchor vertices. -/
def lgWtA : Stmt := .seq lw0 (.seq cfScan (.seq vkLoop (.seq ckScan akScan)))

lemma vkF_congr {vp vp' : ℕ → ℕ} {i : ℕ} (h : ∀ j ≤ i, vp j = vp' j) : vkF vp i = vkF vp' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [vkF]
    rw [h (i + 1) le_rfl, h i (by omega), ih fun j hj => h j (by omega)]

/-- The keys of the core's darts: `KT[j] = CK[IX[j]]`. -/
def lwKT : Stmt := ggProg 5811 5809 5874 5878

/-- The registers of the first `fiProg` (keys `KT`, flags `NF`, table `T2`, junk marks). -/
def lwF2s : Stmt :=
  block [.copyN 4480 5811, .copyN 4481 5878, .copyN 4482 5810, .copyN 4483 5879, .copyN 4484 5880,
    .constN 4485 0]

/-- **Part B of the weights program**: the keys of the core's darts, the table `T2` of the first
core index of every key, the flags of the representatives and their anchors. -/
def lgWtB : Stmt :=
  .seq lwKT (.seq (zfill 5885 5879) (.seq (.seq lwF2s fiProg) (.seq sfScan avScan)))

lemma fiF_congrW {fl fl' key key' : ℕ → ℕ} {n : ℕ} (hf : ∀ j < n, fl j = fl' j)
    (hk : ∀ j < n, key j = key' j) (k : ℕ) : fiF fl key n k = fiF fl' key' n k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fiF_succ, fiF_succ, ih (fun j hj => hf j (by omega)) (fun j hj => hk j (by omega)),
      hf n (by omega), hk n (by omega)]

/-- The registers of the second `fiProg` (keys `TH`, flags `NF`, table `T1`, marks `EXK`). -/
def lwF1s : Stmt :=
  block [.copyN 4480 5811, .copyN 4481 5888, .copyN 4482 5810, .copyN 4483 5881, .copyN 4484 5882,
    .copyN 4485 5871]

/-- The registers of the scatter-add (keys `AV`, the word `2` with stride `0`, table `EXM`). -/
def lwSAs : Stmt :=
  block [.copyN 4630 5800, .copyN 4631 5877, .copyN 4632 5884, .constN 4633 0, .copyN 4634 5883]

/-- **Part C of the weights program**: the marks `K` of the holes' anchors, the scatter-add of `2`
at the anchors of the pairs, the sum. -/
def lgWtC : Stmt :=
  .seq (zfill 5886 5881) (.seq (.seq lwF1s fiProg) (.seq (zfill 5887 5883) (.seq (.seq lwSAs saProg)
    exScan)))

/-- **The weights program** (stage 4 of the large-piece separator). -/
def lgWt : Stmt := .seq lgWtA (.seq lgWtB lgWtC)

lemma fiF_leW (fl key : ℕ → ℕ) (n k : ℕ) : fiF fl key n k ≤ n := by
  induction n with
  | zero => simp [fiF]
  | succ n ih => rw [fiF_succ]; split_ifs <;> omega

lemma fiO_congrW {V : ℕ} {fl fl' key key' : ℕ → ℕ} {i : ℕ} (hf : ∀ j ≤ i, fl j = fl' j)
    (hk : ∀ j ≤ i, key j = key' j) : fiO V fl key i = fiO V fl' key' i := by
  unfold fiO
  rw [hf i le_rfl, hk i le_rfl,
    fiF_congrW (fun j hj => hf j (by omega)) (fun j hj => hk j (by omega))]

lemma fiO_leW (V : ℕ) (fl key : ℕ → ℕ) (i : ℕ) : fiO V fl key i ≤ V := by
  unfold fiO; split_ifs <;> omega

lemma saF_le_two (key : ℕ → ℕ) (n k : ℕ) : saF key (fun _ => 2) n k ≤ 2 * n := by
  unfold saF
  rw [sum_const, smul_eq_mul]
  have := card_le_card (filter_subset (fun j => key j = k) (range n))
  rw [card_range] at this
  omega

section Exec

variable {P : Input} {W : ℕ}

theorem lw0_exec (c : Config) (hc : WordsBounded W c) {n RPb HPb VPb IXb b n' kk K Yb : ℕ}
    (hR : WtR0 c n RPb HPb VPb IXb b n' kk K Yb) (w : Yb + 11 * n + 2 * kk + 4 ≤ W)
    (wb : b + 3 * n' ≤ W) (h2 : 2 ≤ W) :
    ∃ c' t, Exec P W lw0 c c' t ∧ t = 23 ∧ WtRegs c' n RPb HPb VPb IXb b n' kk K Yb ∧
      c'.nmem = upd c.nmem (Yb + 11 * n + 2 * kk + 3) 2 ∧
      (∀ x, x ≠ 5804 → (x < 5873 ∨ 5889 < x) → x ≠ 5899 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨r00, r01, r02, r03, r06, r07, r09, r10, r11, r70, r71, r72, r21⟩ := hR
  unfold lw0
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r00, r01, r02, r03,
    r06, r07, r09, r10, r11, r70, r71, r72, r21]; omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun x a1 a2 a3 => ?_, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r00, r01, r02, r03, r06, r07, r09, r10,
      r11, r70, r71, r72, r21])
    try omega
    try (congr 1; omega)

/-- **Part A on the machine**: the bases (`WtRegs`), `CF2[i] = cfv …`, `VK[i] = vkF VP i`,
`CK[i] = ckA kk HP VP i`, `AK[i] = akA kk RP HP VP i` (`i < n`) and the word `2`; memory outside
`[Yb, Yb + 4n)` and the word `2` kept. -/
theorem lgWtA_exec (c : Config) (hc : WordsBounded W c) {n RPb HPb VPb IXb b n' kk K Yb : ℕ}
    (hR : WtR0 c n RPb HPb VPb IXb b n' kk K Yb) (w : Yb + 11 * n + 2 * kk + 4 ≤ W)
    (wb : b + 3 * n' ≤ W) (h2 : 2 ≤ W) (hn : n + 1 ≤ W)
    (l1 : RPb + n ≤ Yb) (l2 : HPb + n ≤ Yb) (l3 : VPb + n ≤ Yb)
    (hrp : ∀ i < n, c.nmem (RPb + i) < n) (hhp : ∀ i < n, c.nmem (HPb + i) ≤ kk) :
    ∃ c' t, Exec P W lgWtA c c' t ∧ t ≤ 100 * n + 60 ∧
      WtRegs c' n RPb HPb VPb IXb b n' kk K Yb ∧
      (∀ i < n, c'.nmem (Yb + i) = cfv (c.nmem (VPb + i)) (c.nmem (VPb + c.nmem (RPb + i)))
        (c.nmem (HPb + i)) (c.nmem (HPb + c.nmem (RPb + i)))) ∧
      (∀ i < n, c'.nmem (Yb + 2 * n + i) =
        ckA kk (fun j => c.nmem (HPb + j)) (fun j => c.nmem (VPb + j)) i) ∧
      (∀ i < n, c'.nmem (Yb + 3 * n + i) = akA kk (fun j => c.nmem (RPb + j))
        (fun j => c.nmem (HPb + j)) (fun j => c.nmem (VPb + j)) i) ∧
      c'.nmem (Yb + 11 * n + 2 * kk + 3) = 2 ∧
      (∀ a, ¬ (Yb ≤ a ∧ a < Yb + 4 * n) → a ≠ Yb + 11 * n + 2 * kk + 3 →
        c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ wtW x → x ≠ 5804 → (x < 5873 ∨ 5889 < x) → x ≠ 5899 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set m₀ := c.nmem with hm₀
  set TW := Yb + 11 * n + 2 * kk + 3 with hTW
  obtain ⟨c₀, t₀, e₀, ht₀, R0, m0, n0, rr0, rm0, o0⟩ := lw0_exec (P := P) c hc hR w wb h2
  have M0 : ∀ a, a ≠ TW → c₀.nmem a = m₀ a := fun a ha => by rw [m0, upd_other _ _ _ ha]
  -- the flags of the core
  obtain ⟨c₁, t₁, e₁, ht₁, f1, m1, n1, rr1, rm1, o1⟩ := cfScan_exec (P := P) c₀ e₀.wb_right
    R0.r00 R0.r01 R0.r02 R0.r03 R0.r04 R0.r06 R0.r07 R0.r21 (by omega) (by omega) (by omega)
    (by omega) (by omega) (fun i hi => by rw [M0 _ (by omega)]; exact hrp i hi)
    (fun i hi => by omega) (fun i hi => by omega) (fun i hi => by omega)
  have R1 : WtRegs c₁ n RPb HPb VPb IXb b n' kk K Yb :=
    R0.congr fun x hx => n1 x (by unfold vscr; unfold wtW at hx; omega)
      (by unfold wtW at hx; omega) (by unfold wtW at hx; omega)
  have M1 : ∀ a, ¬ (Yb ≤ a ∧ a < Yb + n) → a ≠ TW → c₁.nmem a = m₀ a := fun a h1 h2 => by
    rw [m1 a h1, M0 a h2]
  have F1 : ∀ i < n, c₁.nmem (Yb + i) = cfv (m₀ (VPb + i)) (m₀ (VPb + m₀ (RPb + i)))
      (m₀ (HPb + i)) (m₀ (HPb + m₀ (RPb + i))) := fun i hi => by
    have := hrp i hi
    have e1 : c₀.nmem (RPb + i) = m₀ (RPb + i) := M0 _ (by omega)
    rw [f1 i hi, e1, M0 (VPb + i) (by omega), M0 (VPb + m₀ (RPb + i)) (by omega),
      M0 (HPb + i) (by omega), M0 (HPb + m₀ (RPb + i)) (by omega)]
  -- the run keys
  obtain ⟨c₂, t₂, e₂, ht₂, f2, m2, n2, rr2, rm2, o2⟩ := vkLoop_exec (P := P) c₁ e₁.wb_right
    R1.r00 R1.r03 R1.r73 R1.r06 (by omega) (by omega) (by omega) (by omega)
    (fun i hi => by omega)
  have R2 : WtRegs c₂ n RPb HPb VPb IXb b n' kk K Yb :=
    R1.congr fun x hx => n2 x (by unfold wtW at hx; omega)
  have M2 : ∀ a, ¬ (Yb ≤ a ∧ a < Yb + 2 * n) → a ≠ TW → c₂.nmem a = m₀ a := fun a h1 h2 => by
    rw [m2 a (by omega), M1 a (by omega) h2]
  have F2 : ∀ i < n, c₂.nmem (Yb + n + i) = vkF (fun j => m₀ (VPb + j)) i := fun i hi => by
    rw [f2 i hi]
    exact vkF_congr fun j hj => M1 _ (by omega) (by omega)
  have F1' : ∀ i < n, c₂.nmem (Yb + i) = c₁.nmem (Yb + i) := fun i hi => m2 _ (by omega)
  -- the class keys
  obtain ⟨c₃, t₃, e₃, ht₃, f3, m3, n3, rr3, rm3, o3⟩ := ckScan_exec (P := P) c₂ e₂.wb_right
    R2.r00 R2.r02 R2.r73 R2.r74 R2.r70 R2.r06 R2.r21 (by omega) (by omega) (by omega) (by omega)
    (fun i hi => by
      rw [M2 _ (by omega) (by omega), F2 i hi]
      have := hhp i hi
      have := vkF_le (fun j => m₀ (VPb + j)) i
      omega)
    (fun i hi => by omega) (fun i hi => by omega)
  have R3 : WtRegs c₃ n RPb HPb VPb IXb b n' kk K Yb :=
    R2.congr fun x hx => n3 x (by unfold vscr; unfold wtW at hx; omega)
      (by unfold wtW at hx; omega) (by unfold wtW at hx; omega)
  have F3 : ∀ i < n, c₃.nmem (Yb + 2 * n + i) =
      ckA kk (fun j => m₀ (HPb + j)) (fun j => m₀ (VPb + j)) i := fun i hi => by
    rw [f3 i hi, M2 _ (by omega) (by omega), F2 i hi, ckM_eq]; rfl
  have M3 : ∀ a, ¬ (Yb ≤ a ∧ a < Yb + 3 * n) → a ≠ TW → c₃.nmem a = m₀ a := fun a h1 h2 => by
    rw [m3 a (by omega), M2 a (by omega) h2]
  -- the anchor keys
  have hak : ∀ i < n, akM i (c₃.nmem (VPb + i)) (c₃.nmem (RPb + i)) < n := fun i hi => by
    rw [akM_eq]; split_ifs
    · rw [M3 _ (by omega) (by omega)]; exact hrp i hi
    · exact hi
  obtain ⟨c₄, t₄, e₄, ht₄, f4, m4, n4, rr4, rm4, o4⟩ := akScan_exec (P := P) c₃ e₃.wb_right
    R3.r00 R3.r03 R3.r01 R3.r74 R3.r75 R3.r06 R3.r07 R3.r21 (by omega) (by omega) (by omega)
    (by omega) hak (by omega) (fun i hi => by omega) (fun i hi => by omega) (fun i hi => by omega)
  have R4 : WtRegs c₄ n RPb HPb VPb IXb b n' kk K Yb :=
    R3.congr fun x hx => n4 x (by unfold vscr; unfold wtW at hx; omega)
      (by unfold wtW at hx; omega) (by unfold wtW at hx; omega)
  have F4 : ∀ i < n, c₄.nmem (Yb + 3 * n + i) = akA kk (fun j => m₀ (RPb + j))
      (fun j => m₀ (HPb + j)) (fun j => m₀ (VPb + j)) i := fun i hi => by
    have ev : c₃.nmem (VPb + i) = m₀ (VPb + i) := M3 _ (by omega) (by omega)
    have er : c₃.nmem (RPb + i) = m₀ (RPb + i) := M3 _ (by omega) (by omega)
    have hlt := hak i hi
    rw [ev, er] at hlt
    rw [f4 i hi, ev, er, F3 _ hlt, akM_eq]
    unfold akA akI
    rfl
  refine ⟨c₄, t₀ + (t₁ + (t₂ + (t₃ + t₄))), .seq e₀ (.seq e₁ (.seq e₂ (.seq e₃ e₄))), by omega, R4,
    fun i hi => ?_, fun i hi => ?_, F4, ?_, fun a h1 h2 => ?_, fun x hx a1 a2 a3 => ?_,
    by rw [rr4, rr3, rr2, rr1, rr0], by rw [rm4, rm3, rm2, rm1, rm0],
    by rw [o4, o3, o2, o1, o0]⟩
  · rw [m4 _ (by omega), m3 _ (by omega), F1' i hi, F1 i hi]
  · rw [m4 _ (by omega), F3 i hi]
  · rw [m4 _ (by omega), m3 _ (by omega), m2 _ (by omega), m1 _ (by omega), m0, upd_same]
  · rw [m4 a (by omega), M3 a (by omega) h2]
  · rw [n4 x (by unfold vscr; unfold wtW at hx; omega) (by unfold wtW at hx; omega)
      (by unfold wtW at hx; omega), n3 x (by unfold vscr; unfold wtW at hx; omega)
      (by unfold wtW at hx; omega) (by unfold wtW at hx; omega),
      n2 x (by unfold wtW at hx; omega), n1 x (by unfold vscr; unfold wtW at hx; omega)
      (by unfold wtW at hx; omega) (by unfold wtW at hx; omega), n0 x a1 a2 a3]

theorem lwF2s_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W lwF2s c c' t ∧ t = 6 ∧ c'.nreg 4480 = c.nreg 5811 ∧
      c'.nreg 4481 = c.nreg 5878 ∧ c'.nreg 4482 = c.nreg 5810 ∧ c'.nreg 4483 = c.nreg 5879 ∧
      c'.nreg 4484 = c.nreg 5880 ∧ c'.nreg 4485 = 0 ∧
      (∀ x, (x < 4480 ∨ 4485 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lwF2s
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])

/-- **Part B on the machine.** From the class keys `CK[i] = ck i` and `AK[i] = ak i`
(`0 < · < kk + n + 1`), the flags `CF2`, the indices `IX[j] < n` and the flags `NF` at `b`
(`j < n'`): the table `T2[k] = fiF NF (ck ∘ IX) n' k` (`0 < k < kk + n + 1`) and
`AV[i] = sfM CF2[i] HP[i] HP[RP[i]] T2[ck i] i RP[i] · T2[ak i]`; memory outside
`[Yb + 4n, Yb + 9n + kk + 1)` kept. -/
theorem lgWtB_exec (c : Config) (hc : WordsBounded W c) {n RPb HPb VPb IXb b n' kk K Yb : ℕ}
    (hR : WtRegs c n RPb HPb VPb IXb b n' kk K Yb) {ck ak : ℕ → ℕ}
    (w : Yb + 11 * n + 2 * kk + 4 ≤ W) (hn : n + 1 ≤ W) (hn' : n' ≤ n)
    (l1 : RPb + n ≤ Yb) (l2 : HPb + n ≤ Yb) (l4 : IXb + n' ≤ Yb) (l5 : b + n' ≤ Yb)
    (hrp : ∀ i < n, c.nmem (RPb + i) < n) (hix : ∀ j < n', c.nmem (IXb + j) < n)
    (hck : ∀ i < n, c.nmem (Yb + 2 * n + i) = ck i) (hak : ∀ i < n, c.nmem (Yb + 3 * n + i) = ak i)
    (bck : ∀ i < n, ck i < kk + n + 1) (bak : ∀ i < n, ak i < kk + n + 1) :
    ∃ c' t, Exec P W lgWtB c c' t ∧ t ≤ 90 * n + 6 * kk + 40 ∧
      WtRegs c' n RPb HPb VPb IXb b n' kk K Yb ∧
      (∀ i < n, c'.nmem (Yb + 8 * n + kk + 1 + i) =
        sfM (c.nmem (Yb + i)) (c.nmem (HPb + i)) (c.nmem (HPb + c.nmem (RPb + i)))
          (fiF (fun j => c.nmem (b + j)) (fun j => ck (c.nmem (IXb + j))) n' (ck i)) i
          (c.nmem (RPb + i)) *
        fiF (fun j => c.nmem (b + j)) (fun j => ck (c.nmem (IXb + j))) n' (ak i)) ∧
      (∀ a, ¬ (Yb + 4 * n ≤ a ∧ a < Yb + 9 * n + kk + 1) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ wtW x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set fl : ℕ → ℕ := fun j => c.nmem (b + j) with hfl
  set kt : ℕ → ℕ := fun j => ck (c.nmem (IXb + j)) with hkt
  -- the keys of the core's darts
  obtain ⟨c₁, t₁, e₁, ht₁, f1, m1, n1, rr1, rm1, o1⟩ := ggProg_exec (P := P) c hc
    (a := 5811) (b := 5809) (cc := 5874) (dd := 5878) (by omega) (by omega) (by omega) (by omega)
    hR.r11 hR.r09 hR.r74 hR.r78 (by omega) (by omega) (by omega)
    (fun j hj => by have := hix j hj; omega) (fun j hj => by omega)
    (fun j hj => by have := hix j hj; omega)
  have R1 := hR.congr fun x hx => n1 x (by unfold wtW at hx; omega)
  have K1 : ∀ j < n', c₁.nmem (Yb + 4 * n + j) = kt j := fun j hj => by
    rw [f1 j hj, hck _ (hix j hj)]
  have M1 : ∀ a, ¬ (Yb + 4 * n ≤ a ∧ a < Yb + 4 * n + n') → c₁.nmem a = c.nmem a := m1
  -- the zero table
  obtain ⟨c₂, t₂, e₂, ht₂, f2, m2, n2, rr2, rm2, o2⟩ := zfill_exec (P := P) c₁ e₁.wb_right
    (bnd := 5885) (ob := 5879) R1.r85 R1.r21 R1.r79 (by omega) (by omega) (by unfold vscr; omega)
    (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
  have R2 := R1.congr fun x hx => n2 x (by unfold vscr; unfold wtW at hx; omega)
    (by unfold wtW at hx; omega) (by unfold wtW at hx; omega)
  -- the table of first indices
  obtain ⟨c₃, t₃, e₃, ht₃, s0, s1, s2, s3, s4, s5, n3, m3, rr3, rm3, o3⟩ := lwF2s_exec (P := P) c₂
    e₂.wb_right
  obtain ⟨c₄, t₄, e₄, ht₄, f4, -, m4, n4, rr4, rm4, o4⟩ := fiProg_exec (P := P) c₃ e₃.wb_right
    (n := n') (KEYb := Yb + 4 * n) (FLb := b) (Tb := Yb + 5 * n) (OUTb := Yb + 6 * n + kk + 1)
    (V := 0) (nk := kk + n + 1) (by rw [s0, R2.r11]) (by rw [s1, R2.r78]) (by rw [s2, R2.r10])
    (by rw [s3, R2.r79]) (by rw [s4, R2.r80]) s5
    (fun i hi => by
      rw [m3, m2 _ (by omega), K1 i hi]
      exact bck _ (hix i hi))
    ⟨by omega, by omega, by omega, by omega, by omega⟩
    (fun k hk1 hk2 => by rw [m3]; exact f2 k hk2)
  have R4 := R2.congr fun x hx => by
    rw [n4 x (by unfold wtW at hx; omega), n3 x (by unfold wtW at hx; omega)]
  have T4 : ∀ k, 0 < k → k < kk + n + 1 → c₄.nmem (Yb + 5 * n + k) = fiF fl kt n' k :=
    fun k hk1 hk2 => by
      rw [f4 k hk1 hk2]
      refine fiF_congrW (fun j hj => ?_) (fun j hj => ?_) k
      · rw [m3, m2 _ (by omega), M1 _ (by omega)]
      · rw [m3, m2 _ (by omega), K1 j hj]
  have M4 : ∀ a, ¬ (Yb + 4 * n ≤ a ∧ a < Yb + 7 * n + kk + 1) → c₄.nmem a = c.nmem a := fun a ha => by
    rw [m4 a (by omega), m3, m2 a (by omega), M1 a (by omega)]
  have T4' : ∀ k < kk + n + 1, c₄.nmem (Yb + 5 * n + k) = fiF fl kt n' k := fun k hk => by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [m4 _ (by omega), m3, f2 0 (by omega)]
      exact ((fiF_zero_iff _ _).2 (Or.inl rfl)).symm
    · exact T4 k hk0 hk
  -- the representatives
  obtain ⟨c₅, t₅, e₅, ht₅, f5, m5, n5, rr5, rm5, o5⟩ := sfScan_exec (P := P) c₄ e₄.wb_right
    (nk := kk + n + 1) R4.r00 R4.r72 R4.r02 R4.r01 R4.r74 R4.r79 R4.r76 R4.r06 R4.r21 (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi => by rw [M4 _ (by omega)]; exact hrp i hi)
    (fun i hi => by rw [M4 _ (by omega), hck i hi]; exact bck i hi)
    (fun i hi => by omega) (fun i hi => by omega) (fun i hi => by omega) (fun i hi => by omega)
    (fun k hk => by omega)
  have R5 := R4.congr fun x hx => n5 x (by unfold vscr; unfold wtW at hx; omega)
    (by unfold wtW at hx; omega) (by unfold wtW at hx; omega)
  have S5 : ∀ i < n, c₅.nmem (Yb + 7 * n + kk + 1 + i) =
      sfM (c.nmem (Yb + i)) (c.nmem (HPb + i)) (c.nmem (HPb + c.nmem (RPb + i))) (fiF fl kt n' (ck i)) i
        (c.nmem (RPb + i)) := fun i hi => by
    have er : c₄.nmem (RPb + i) = c.nmem (RPb + i) := M4 _ (by omega)
    have ec : c₄.nmem (Yb + 2 * n + i) = ck i := by rw [M4 _ (by omega), hck i hi]
    have := hrp i hi
    rw [f5 i hi, er, ec, M4 (Yb + i) (by omega), M4 (HPb + i) (by omega),
      M4 (HPb + c.nmem (RPb + i)) (by omega), T4' _ (bck i hi)]
  -- the anchors
  obtain ⟨c₆, t₆, e₆, ht₆, f6, m6, n6, rr6, rm6, o6⟩ := avScan_exec (P := P) c₅ e₅.wb_right
    (nk := kk + n + 1) R5.r00 R5.r76 R5.r75 R5.r79 R5.r77 R5.r21 (by omega) (by omega) (by omega)
    (by omega) (by omega) (fun i hi => by rw [S5 i hi]; exact sfM_le _ _ _ _ _ _)
    (fun i hi => by rw [m5 _ (by omega), M4 _ (by omega), hak i hi]; exact bak i hi)
    (fun i hi => by omega) (fun i hi => by omega) (fun k hk => by omega)
  have R6 := R5.congr fun x hx => n6 x (by unfold vscr; unfold wtW at hx; omega)
    (by unfold wtW at hx; omega) (by unfold wtW at hx; omega)
  refine ⟨c₆, t₁ + (t₂ + ((t₃ + t₄) + (t₅ + t₆))),
    .seq e₁ (.seq e₂ (.seq (.seq e₃ e₄) (.seq e₅ e₆))), by omega, R6, fun i hi => ?_,
    fun a ha => ?_, fun x hx => ?_, by rw [rr6, rr5, rr4, rr3, rr2, rr1],
    by rw [rm6, rm5, rm4, rm3, rm2, rm1], by rw [o6, o5, o4, o3, o2, o1]⟩
  · have ea : c₅.nmem (Yb + 3 * n + i) = ak i := by
      rw [m5 _ (by omega), M4 _ (by omega), hak i hi]
    have := bak i hi
    rw [f6 i hi, S5 i hi, ea, m5 _ (by omega), T4' _ (bak i hi)]
  · rw [m6 a (by omega), m5 a (by omega), M4 a (by omega)]
  · rw [n6 x (by unfold vscr; unfold wtW at hx; omega) (by unfold wtW at hx; omega)
      (by unfold wtW at hx; omega), n5 x (by unfold vscr; unfold wtW at hx; omega)
      (by unfold wtW at hx; omega) (by unfold wtW at hx; omega),
      n4 x (by unfold wtW at hx; omega), n3 x (by unfold wtW at hx; omega),
      n2 x (by unfold vscr; unfold wtW at hx; omega) (by unfold wtW at hx; omega)
      (by unfold wtW at hx; omega), n1 x (by unfold wtW at hx; omega)]

theorem lwF1s_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W lwF1s c c' t ∧ t = 6 ∧ c'.nreg 4480 = c.nreg 5811 ∧
      c'.nreg 4481 = c.nreg 5888 ∧ c'.nreg 4482 = c.nreg 5810 ∧ c'.nreg 4483 = c.nreg 5881 ∧
      c'.nreg 4484 = c.nreg 5882 ∧ c'.nreg 4485 = c.nreg 5871 ∧
      (∀ x, (x < 4480 ∨ 4485 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lwF1s
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])

theorem lwSAs_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W lwSAs c c' t ∧ t = 5 ∧ c'.nreg 4630 = c.nreg 5800 ∧
      c'.nreg 4631 = c.nreg 5877 ∧ c'.nreg 4632 = c.nreg 5884 ∧ c'.nreg 4633 = 0 ∧
      c'.nreg 4634 = c.nreg 5883 ∧
      (∀ x, (x < 4630 ∨ 4634 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lwSAs
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])

/-- **Part C on the machine.** From the anchors `AV[i] ≤ n'` (`i < n`), the flags `NF` and hole
labels `TH ≤ kk` at `b`, `b + n'` and the word `2`: `EX[j] = fiO K NF TH j + saF AV 2 n (j + 1)`
at `b + 3 n'` (`j < n'`); memory outside `[Yb + 9n + kk + 1, Yb + 11n + 2kk + 3)` and
`[b + 3n', b + 4n')` kept. -/
theorem lgWtC_exec (c : Config) (hc : WordsBounded W c) {n RPb HPb VPb IXb b n' kk K Yb : ℕ}
    (hR : WtRegs c n RPb HPb VPb IXb b n' kk K Yb)
    (w : Yb + 11 * n + 2 * kk + 4 ≤ W) (hn : n + 1 ≤ W) (hn' : n' ≤ n) (hK : K + 2 * n ≤ W)
    (l5 : b + 4 * n' ≤ Yb)
    (hav : ∀ i < n, c.nmem (Yb + 8 * n + kk + 1 + i) ≤ n')
    (hth : ∀ j < n', c.nmem (b + n' + j) ≤ kk)
    (htwo : c.nmem (Yb + 11 * n + 2 * kk + 3) = 2) :
    ∃ c' t, Exec P W lgWtC c c' t ∧ t ≤ 60 * n + 6 * kk + 60 ∧
      WtRegs c' n RPb HPb VPb IXb b n' kk K Yb ∧
      (∀ j < n', c'.nmem (b + 3 * n' + j) =
        fiO K (fun j => c.nmem (b + j)) (fun j => c.nmem (b + n' + j)) j +
          saF (fun i => c.nmem (Yb + 8 * n + kk + 1 + i)) (fun _ => 2) n (j + 1)) ∧
      (∀ a, ¬ (Yb + 9 * n + kk + 1 ≤ a ∧ a < Yb + 11 * n + 2 * kk + 3) →
        ¬ (b + 3 * n' ≤ a ∧ a < b + 4 * n') → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ wtW x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- the zero table `T1`
  obtain ⟨c₁, t₁, e₁, ht₁, f1, m1, n1, rr1, rm1, o1⟩ := zfill_exec (P := P) c hc
    (bnd := 5886) (ob := 5881) hR.r86 hR.r21 hR.r81 (by omega) (by omega) (by unfold vscr; omega)
    (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
  have R1 := hR.congr fun x hx => n1 x (by unfold vscr; unfold wtW at hx; omega)
    (by unfold wtW at hx; omega) (by unfold wtW at hx; omega)
  -- the marks of the holes' anchors
  obtain ⟨c₂, t₂, e₂, ht₂, s0, s1, s2, s3, s4, s5, n2, m2, rr2, rm2, o2⟩ := lwF1s_exec (P := P) c₁
    e₁.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, -, f3, m3, n3, rr3, rm3, o3⟩ := fiProg_exec (P := P) c₂ e₂.wb_right
    (n := n') (KEYb := b + n') (FLb := b) (Tb := Yb + 9 * n + kk + 1)
    (OUTb := Yb + 9 * n + 2 * kk + 2) (V := K) (nk := kk + 1) (by rw [s0, R1.r11])
    (by rw [s1, R1.r88]) (by rw [s2, R1.r10]) (by rw [s3, R1.r81]) (by rw [s4, R1.r82])
    (by rw [s5, R1.r71])
    (fun i hi => by rw [m2, m1 _ (by omega)]; have := hth i hi; omega)
    ⟨by omega, by omega, by omega, by omega, by omega⟩
    (fun k hk1 hk2 => by rw [m2]; exact f1 k hk2)
  have R3 := R1.congr fun x hx => by
    rw [n3 x (by unfold wtW at hx; omega), n2 x (by unfold wtW at hx; omega)]
  have X3 : ∀ j < n', c₃.nmem (Yb + 9 * n + 2 * kk + 2 + j) =
      fiO K (fun j => c.nmem (b + j)) (fun j => c.nmem (b + n' + j)) j := fun j hj => by
    rw [f3 j hj, m2]
    exact fiO_congrW (fun j' hj' => m1 _ (by omega)) (fun j' hj' => m1 _ (by omega))
  have M3 : ∀ a, ¬ (Yb + 9 * n + kk + 1 ≤ a ∧ a < Yb + 10 * n + 2 * kk + 2) →
      c₃.nmem a = c.nmem a := fun a ha => by
    rw [m3 a (by omega), m2, m1 a (by omega)]
  -- the zero table `EXM`
  obtain ⟨c₄, t₄, e₄, ht₄, f4, m4, n4, rr4, rm4, o4⟩ := zfill_exec (P := P) c₃ e₃.wb_right
    (bnd := 5887) (ob := 5883) R3.r87 R3.r21 R3.r83 (by omega) (by omega) (by unfold vscr; omega)
    (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
  have R4 := R3.congr fun x hx => n4 x (by unfold vscr; unfold wtW at hx; omega)
    (by unfold wtW at hx; omega) (by unfold wtW at hx; omega)
  -- the scatter-add
  obtain ⟨c₅, t₅, e₅, ht₅, a0, a1, a2, a3, a4, n5, m5, rr5, rm5, o5⟩ := lwSAs_exec (P := P) c₄
    e₄.wb_right
  have hAV : ∀ i < n, c₅.nmem (Yb + 8 * n + kk + 1 + i) = c.nmem (Yb + 8 * n + kk + 1 + i) :=
    fun i hi => by rw [m5, m4 _ (by omega), M3 _ (by omega)]
  have hTW : c₅.nmem (Yb + 11 * n + 2 * kk + 3) = 2 := by
    rw [m5, m4 _ (by omega), M3 _ (by omega), htwo]
  obtain ⟨c₆, t₆, e₆, ht₆, f6, m6, n6, rr6, rm6, o6⟩ := saProg_exec (P := P) c₅ e₅.wb_right
    (m := n) (nk := n' + 1) (KEYb := Yb + 8 * n + kk + 1) (VALb := Yb + 11 * n + 2 * kk + 3)
    (st := 0) (Wb := Yb + 10 * n + 2 * kk + 2) (by rw [a0, R4.r00]) (by rw [a1, R4.r77])
    (by rw [a2, R4.r84]) a3 (by rw [a4, R4.r83])
    (fun j hj => by rw [hAV j hj]; have := hav j hj; omega)
    (fun k hk => by rw [m5]; exact f4 k hk) (fun j hj => by omega) (fun j hj => by omega)
    (by omega) (by omega) (fun j hj => by omega) (by omega)
    (by
      rw [sum_congr rfl fun j hj => by rw [Nat.zero_mul, Nat.add_zero, hTW], sum_const,
        card_range, smul_eq_mul]
      omega)
  have R6 := R4.congr fun x hx => by
    rw [n6 x (by unfold wtW at hx; omega), n5 x (by unfold wtW at hx; omega)]
  have S6 : ∀ k < n' + 1, c₆.nmem (Yb + 10 * n + 2 * kk + 2 + k) =
      saF (fun i => c.nmem (Yb + 8 * n + kk + 1 + i)) (fun _ => 2) n k := fun k hk => by
    rw [f6 k hk]
    exact saF_congr (fun j hj => hAV j hj) (fun j hj => by rw [Nat.zero_mul, Nat.add_zero, hTW]) k
  have X6 : ∀ j < n', c₆.nmem (Yb + 9 * n + 2 * kk + 2 + j) =
      fiO K (fun j => c.nmem (b + j)) (fun j => c.nmem (b + n' + j)) j := fun j hj => by
    rw [m6 _ (by omega), m5, m4 _ (by omega), X3 j hj]
  -- the sum
  obtain ⟨c₇, t₇, e₇, ht₇, f7, m7, n7, rr7, rm7, o7⟩ := exScan_exec (P := P) c₆ e₆.wb_right
    R6.r11 R6.r82 R6.r83 R6.r89 R6.r06 R6.r21 (by omega) (by omega) (by omega) (by omega)
    (fun j hj => by
      rw [X6 j hj, S6 (j + 1) (by omega)]
      have := fiO_leW K (fun j => c.nmem (b + j)) (fun j => c.nmem (b + n' + j)) j
      have := saF_le_two (fun i => c.nmem (Yb + 8 * n + kk + 1 + i)) n (j + 1)
      omega)
    (fun j hj => by omega) (fun j hj => by omega)
  have R7 := R6.congr fun x hx => n7 x (by unfold vscr; unfold wtW at hx; omega)
    (by unfold wtW at hx; omega) (by unfold wtW at hx; omega)
  refine ⟨c₇, t₁ + ((t₂ + t₃) + (t₄ + ((t₅ + t₆) + t₇))),
    .seq e₁ (.seq (.seq e₂ e₃) (.seq e₄ (.seq (.seq e₅ e₆) e₇))), by omega, R7,
    fun j hj => by rw [f7 j hj, X6 j hj, S6 (j + 1) (by omega)], fun a h1 h2 => ?_,
    fun x hx => ?_, by rw [rr7, rr6, rr5, rr4, rr3, rr2, rr1],
    by rw [rm7, rm6, rm5, rm4, rm3, rm2, rm1], by rw [o7, o6, o5, o4, o3, o2, o1]⟩
  · rw [m7 a (by omega), m6 a (by omega), m5, m4 a (by omega), M3 a (by omega)]
  · rw [n7 x (by unfold vscr; unfold wtW at hx; omega) (by unfold wtW at hx; omega)
      (by unfold wtW at hx; omega), n6 x (by unfold wtW at hx; omega),
      n5 x (by unfold wtW at hx; omega), n4 x (by unfold vscr; unfold wtW at hx; omega)
      (by unfold wtW at hx; omega) (by unfold wtW at hx; omega),
      n3 x (by unfold wtW at hx; omega), n2 x (by unfold wtW at hx; omega),
      n1 x (by unfold vscr; unfold wtW at hx; omega) (by unfold wtW at hx; omega)
      (by unfold wtW at hx; omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
