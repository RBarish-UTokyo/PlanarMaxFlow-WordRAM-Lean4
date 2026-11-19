module

public import PlanarFlow.BKMNW.PfP

/-!
# Stage 7 of `sepL` (I): the hole flags, the new hole, the keys of the classes

From the path's vertex flags `VF` on the record (`lgPF`) and the record's hole labels `HP`,
reverses `RP` and vertex keys `VK`:

* **`hfProg`** (`KH[i] = HP[i] · VF[i]`, a zero table `HT` of `k + 1` cells, the marks of the keys
  (`pfMk`), `HT[0] := 0`), **`hfProg_exec`** (`13 n + 6 k + 30` steps): `HT[h] = 1` iff some dart
  has `HP[i] · VF[i] = h` (`1 ≤ h ≤ k`), `HT[0] = 0`;
* **`hf_sem`** (pure): with `HP = hlab ∘ tail`, `VF = bf (tail ∈ C)` and every vertex of `C` a tail
  of the record (`pf_mverts_tail`), `(∃ i, HP[i] · VF[i] = j + 1) ↔ ¬ Disjoint Hs[j] C`;
* **`ytProg`** (`YT[i] = VF[i] + HT[HP[i]]`, `YH[i] = YT[RP[i]]`, `TK[i] = HP[i] > 0 ? n + HP[i] :
  VK[i]`), **`ytProg_exec`** (`42 n + 9` steps), **`yt_sem`** (`0 < YT[i] ↔ tail ∈ newHole Hs C`),
  **`tk_sem`** (`TK[i] = TK[j] ↔ HRel Hs` of the tails);
* **`s7G`** (the gathers of the outputs 2–4 of `SepPSpecX` through `FX`: `DF ∘ FX` at `Sb + m`,
  `VF ∘ FX` at `Sb + 2 m`, `HT[1 ..]` at `Sb + 3 m`), **`s7G_exec`** (`25 m + 7 k + 40` steps).

Registers `7100 = n`, `7101 = HPb`, `7102 = VFb`, `7103 = KHb`, `7104 = HTb`, `7105 = k + 1`,
`7106 = RPb`, `7107 = YTb`, `7108 = YHb`, `7109 = VKb`, `7110 = TKb`, written `7120`; for `s7G`
`7130 = m`, `7131 = FXb`, `7132 = DFb`, `7133 = Sb + m`, `7134 = Sb + 2 m`, `7135 = k`,
`7136 = HTb + 1`, `7137 = Sb + 3 m`; `6521 = 1`.
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

/-- `KH[i] = HP[i] · VF[i]`. -/
def vbKH : Stmt :=
  block [.addN 6524 7101 6520, .loadN 6524 6524, .addN 6525 7102 6520, .loadN 6525 6525,
    .mulN 6523 6524 6525]

/-- The registers of the mark loop of the hole flags. -/
def hfS : Stmt := block [.copyN 6030 7100, .copyN 6031 7103, .copyN 6032 7104]

/-- `HT[0] := 0`. -/
def hfZ : Stmt := block [.constN 7120 0, .storeN 7104 7120]

/-- **The hole flags** `HT[h] = [∃ i, HP[i] · VF[i] = h]` (`h ≥ 1`), `HT[0] = 0`. -/
def hfProg : Stmt :=
  .seq (mapRunS vbKH 7100 7103) (.seq (zfill 7105 7104) (.seq (.seq hfS pfMk) hfZ))

/-- `YT[i] = VF[i] + HT[HP[i]]`. -/
def vbYT : Stmt :=
  block [.addN 6524 7102 6520, .loadN 6524 6524, .addN 6525 7101 6520, .loadN 6525 6525,
    .addN 6525 7104 6525, .loadN 6525 6525, .addN 6523 6524 6525]

/-- `YH[i] = YT[RP[i]]`. -/
def vbYH : Stmt :=
  block [.addN 6524 7106 6520, .loadN 6524 6524, .addN 6524 7107 6524, .loadN 6523 6524]

/-- `TK[i] = s (n + HP[i]) + (1 - s) VK[i]`, `s = HP[i] / HP[i]`. -/
def vbTK : Stmt :=
  block [.addN 6524 7101 6520, .loadN 6524 6524, .divN 6525 6524 6524, .addN 6526 7100 6524,
    .mulN 6526 6525 6526, .subN 6527 6521 6525, .addN 6528 7109 6520, .loadN 6528 6528,
    .mulN 6528 6527 6528, .addN 6523 6526 6528]

/-- **The flags of the new hole and the keys of the classes.** -/
def ytProg : Stmt :=
  .seq (mapRunS vbYT 7100 7107) (.seq (mapRunS vbYH 7100 7108) (mapRunS vbTK 7100 7110))

/-- The value of `vbTK`. -/
def tkV (n h vk : ℕ) : ℕ := pdSel (h / h) (n + h) vk

lemma tkV_eq (n h vk : ℕ) : tkV n h vk = if h = 0 then vk else n + h := by
  unfold tkV
  rw [pdSel_eq (dself_le h), dself_eq]
  split_ifs <;> simp_all

/-- The registers of the gathers. -/
def s7G1 : Stmt := ggProg 7130 7131 7132 7133
/-- The second gather. -/
def s7G2 : Stmt := ggProg 7130 7131 7102 7134
/-- The copy of the hole flags. -/
def s7G3 : Stmt := .seq (block [.copyN 4910 7135, .copyN 4911 7136, .copyN 4912 7137]) cpArr

/-- **The outputs 2–4 of `SepPSpecX`** through `FX`. -/
def s7G : Stmt := .seq s7G1 (.seq s7G2 s7G3)

section Exec

variable {P : Input} {W : ℕ}

theorem vbKH_exec (c : Config) (hc : WordsBounded W c) {i HPb VFb h v : ℕ}
    (r20 : c.nreg 6520 = i) (r01 : c.nreg 7101 = HPb) (r02 : c.nreg 7102 = VFb)
    (hh : c.nmem (HPb + i) = h) (hv : c.nmem (VFb + i) = v) (hv1 : v ≤ 1)
    (w1 : HPb + i ≤ W) (w2 : VFb + i ≤ W) :
    ∃ c' k, Exec P W vbKH c c' k ∧ k ≤ 5 ∧ c'.nreg 6523 = h * v ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have bh : h ≤ W := hh ▸ hc.2 _
  have m1 : h * v ≤ W := by rw [mul_comm]; exact fmul_le hv1 bh
  unfold vbKH
  exec_block
  all_goals try (config_simp; (try simp only [r20, r01, r02, hh, hv]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r01, r02, hh, hv]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbYT_exec (c : Config) (hc : WordsBounded W c) {i HPb VFb HTb h v t : ℕ}
    (r20 : c.nreg 6520 = i) (r01 : c.nreg 7101 = HPb) (r02 : c.nreg 7102 = VFb)
    (r04 : c.nreg 7104 = HTb)
    (hh : c.nmem (HPb + i) = h) (hv : c.nmem (VFb + i) = v) (ht : c.nmem (HTb + h) = t)
    (w1 : HPb + i ≤ W) (w2 : VFb + i ≤ W) (w3 : HTb + h ≤ W) (w4 : v + t ≤ W) :
    ∃ c' k, Exec P W vbYT c c' k ∧ k ≤ 7 ∧ c'.nreg 6523 = v + t ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold vbYT
  exec_block
  all_goals try (config_simp; (try simp only [r20, r01, r02, r04, hh, hv, ht]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r01, r02, r04, hh, hv, ht]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbYH_exec (c : Config) (hc : WordsBounded W c) {i RPb YTb r y : ℕ}
    (r20 : c.nreg 6520 = i) (r06 : c.nreg 7106 = RPb) (r07 : c.nreg 7107 = YTb)
    (hr : c.nmem (RPb + i) = r) (hy : c.nmem (YTb + r) = y) (w1 : RPb + i ≤ W)
    (w2 : YTb + r ≤ W) :
    ∃ c' k, Exec P W vbYH c c' k ∧ k ≤ 4 ∧ c'.nreg 6523 = y ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold vbYH
  exec_block
  all_goals try (config_simp; (try simp only [r20, r06, r07, hr, hy]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r06, r07, hr, hy]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbTK_exec (c : Config) (hc : WordsBounded W c) {i n HPb VKb h vk : ℕ}
    (r20 : c.nreg 6520 = i) (r00 : c.nreg 7100 = n) (r01 : c.nreg 7101 = HPb)
    (r09 : c.nreg 7109 = VKb) (r21 : c.nreg 6521 = 1)
    (hh : c.nmem (HPb + i) = h) (hv : c.nmem (VKb + i) = vk)
    (w1 : HPb + i ≤ W) (w2 : VKb + i ≤ W) (w3 : n + h + vk ≤ W) :
    ∃ c' k, Exec P W vbTK c c' k ∧ k ≤ 10 ∧ c'.nreg 6523 = tkV n h vk ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hd := dself_le h
  have m1 : h / h * (n + h) ≤ W := fmul_le hd (by omega)
  have m2 : (1 - h / h) * vk ≤ W := fmul_le (Nat.sub_le _ _) (by omega)
  have m3 : tkV n h vk ≤ W := pdSel_le hd (by omega) (by omega)
  unfold tkV pdSel at m3
  unfold vbTK
  exec_block
  all_goals try (config_simp; (try simp only [r20, r00, r01, r09, r21, hh, hv]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r00, r01, r09, r21, hh, hv, tkV, pdSel]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

/-- The registers of stage 7 (I). -/
structure HfRegs (c : Config) (n k HPb VFb KHb HTb RPb YTb YHb VKb TKb : ℕ) : Prop where
  r00 : c.nreg 7100 = n
  r01 : c.nreg 7101 = HPb
  r02 : c.nreg 7102 = VFb
  r03 : c.nreg 7103 = KHb
  r04 : c.nreg 7104 = HTb
  r05 : c.nreg 7105 = k + 1
  r06 : c.nreg 7106 = RPb
  r07 : c.nreg 7107 = YTb
  r08 : c.nreg 7108 = YHb
  r09 : c.nreg 7109 = VKb
  r10 : c.nreg 7110 = TKb
  r21 : c.nreg 6521 = 1

lemma HfRegs.congr {c c' : Config} {n k HPb VFb KHb HTb RPb YTb YHb VKb TKb : ℕ}
    (h : HfRegs c n k HPb VFb KHb HTb RPb YTb YHb VKb TKb)
    (e : ∀ x, (7100 ≤ x ∧ x ≤ 7110) ∨ x = 6521 → c'.nreg x = c.nreg x) :
    HfRegs c' n k HPb VFb KHb HTb RPb YTb YHb VKb TKb :=
  ⟨by rw [e _ (by omega)]; exact h.r00, by rw [e _ (by omega)]; exact h.r01,
    by rw [e _ (by omega)]; exact h.r02, by rw [e _ (by omega)]; exact h.r03,
    by rw [e _ (by omega)]; exact h.r04, by rw [e _ (by omega)]; exact h.r05,
    by rw [e _ (by omega)]; exact h.r06, by rw [e _ (by omega)]; exact h.r07,
    by rw [e _ (by omega)]; exact h.r08, by rw [e _ (by omega)]; exact h.r09,
    by rw [e _ (by omega)]; exact h.r10, by rw [e _ (by omega)]; exact h.r21⟩

set_option maxHeartbeats 1000000 in
/-- The keys `KH[i] = HP[i] · VF[i]` (`mapRunS vbKH`). -/
theorem hfKH_exec (c : Config) (hc : WordsBounded W c)
    {n k HPb VFb KHb HTb RPb YTb YHb VKb TKb : ℕ} {hp vf : ℕ → ℕ}
    (hR : HfRegs c n k HPb VFb KHb HTb RPb YTb YHb VKb TKb)
    (hhp : ∀ i < n, c.nmem (HPb + i) = hp i) (hvf : ∀ i < n, c.nmem (VFb + i) = vf i)
    (hvf1 : ∀ i < n, vf i ≤ 1)
    (lay : HPb + n ≤ KHb ∧ VFb + n ≤ KHb ∧ KHb + n ≤ W) (hn : n + 1 ≤ W) :
    ∃ c' t, Exec P W (mapRunS vbKH 7100 7103) c c' t ∧ t ≤ 10 * n + 3 ∧
      (∀ i < n, c'.nmem (KHb + i) = hp i * vf i) ∧
      (∀ a, ¬ (KHb ≤ a ∧ a < KHb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3⟩ := lay
  obtain ⟨c', t, e, ht, f, fm, fn, fr, frm, fo⟩ := mapRun_exec (P := P) c hc
    (vb := vbKH) (bnd := 7100) (ob := 7103) (m := n) (Ob := KHb) (B := 5)
    (fun i => hp i * vf i) hR.r00 hR.r21 hR.r03
    (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega)
    (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      have g : ∀ x, ((7100 ≤ x ∧ x ≤ 7110) ∨ x = 6521) → c'.nreg x = c.nreg x := fun x hx =>
        hr x (by unfold vscr; omega) (by omega) (by omega)
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbKH_exec (P := P) c' hw
        (HPb := HPb) (VFb := VFb) (h := hp i) (v := vf i) h20 (by rw [g _ (by omega)]; exact hR.r01)
        (by rw [g _ (by omega)]; exact hR.r02) (by rw [hm _ (by omega)]; exact hhp i hi)
        (by rw [hm _ (by omega)]; exact hvf i hi) (hvf1 i hi) (by omega) (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  exact ⟨c', t, e, by omega, f, fm, fn, fr, frm, fo⟩

theorem hfZ_exec (c : Config) (hc : WordsBounded W c) {HTb : ℕ} (r04 : c.nreg 7104 = HTb)
    (w : HTb ≤ W) :
    ∃ c' t, Exec P W hfZ c c' t ∧ t = 2 ∧ c'.nmem = upd c.nmem HTb 0 ∧
      (∀ x, x ≠ 7120 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hfZ
  exec_block
  all_goals try (config_simp; (try simp only [r04]); omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp (disch := omega) only [upd_same, upd_other, r04]
  · config_simp; simp (disch := omega) only [upd_other]

set_option maxHeartbeats 2000000 in
/-- **The hole flags** (see the module docstring). -/
theorem hfProg_exec (c : Config) (hc : WordsBounded W c)
    {n k HPb VFb KHb HTb RPb YTb YHb VKb TKb : ℕ} {hp vf : ℕ → ℕ}
    (hR : HfRegs c n k HPb VFb KHb HTb RPb YTb YHb VKb TKb)
    (hhp : ∀ i < n, c.nmem (HPb + i) = hp i) (hvf : ∀ i < n, c.nmem (VFb + i) = vf i)
    (hvf1 : ∀ i < n, vf i ≤ 1) (hpk : ∀ i < n, hp i ≤ k)
    (lay : HPb + n ≤ KHb ∧ VFb + n ≤ KHb ∧ KHb + n ≤ HTb ∧ HTb + k + 1 ≤ W) (hn : n + 1 ≤ W)
    (hk : k + 2 ≤ W) :
    ∃ c' t, Exec P W hfProg c c' t ∧ t ≤ 17 * n + 6 * k + 30 ∧
      c'.nmem HTb = 0 ∧
      (∀ h, 1 ≤ h → h ≤ k → c'.nmem (HTb + h) = if ∃ i < n, hp i * vf i = h then 1 else 0) ∧
      (∀ a, ¬ (KHb ≤ a ∧ a < HTb + k + 1) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → (x < 6030 ∨ 6035 < x) → x ≠ 7120 →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4⟩ := lay
  unfold hfProg
  obtain ⟨c₁, t₁, e₁, ht₁, f1, fm1, fn1, fr1, frm1, fo1⟩ := hfKH_exec (P := P) c hc hR hhp hvf
    hvf1 ⟨l1, l2, by omega⟩ hn
  have hR1 := hR.congr (c' := c₁) fun x hx => fn1 x (by unfold vscr; omega) (by omega) (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, f2, fm2, fn2, fr2, frm2, fo2⟩ := zfill_exec (P := P) c₁ e₁.wb_right
    (bnd := 7105) (ob := 7104) (m := k + 1) (Ob := HTb) hR1.r05 hR1.r21 hR1.r04 (by omega)
    (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega)
    (by omega)
  have hR2 := hR1.congr (c' := c₂) fun x hx => fn2 x (by unfold vscr; omega) (by omega) (by omega)
  have K2 : ∀ i < n, c₂.nmem (KHb + i) = hp i * vf i := fun i hi => by
    rw [fm2 _ (by omega)]; exact f1 i hi
  obtain ⟨c₃, t₃, e₃, ht₃, g3, gm3, gn3, gr3, grm3, go3⟩ := pfMark_exec (P := P) c₂ e₂.wb_right
    (a := 7100) (b := 7103) (d := 7104) (m := n) (n := k) (KEYb := KHb) (Tb := HTb)
    (by omega) (by omega) (by omega) hR2.r00 hR2.r03 hR2.r04 (key := fun i => hp i * vf i) K2
    (fun j hj => by
      have := hvf1 j hj; have := hpk j hj
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hvf1 j hj) with h | h <;> rw [h] <;> omega)
    (Or.inl (by omega)) (by omega) (by omega) hn
  have hR3 := hR2.congr (c' := c₃) fun x hx => gn3 x (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, m4, n4, r4, rm4, o4⟩ := hfZ_exec (P := P) c₃ e₃.wb_right hR3.r04
    (by omega)
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, ?_,
    fun h h1 h2 => ?_, fun a ha => ?_, fun x a1 a2 a3 a4 a5 => ?_, by rw [r4, gr3, fr2, fr1],
    by rw [rm4, grm3, frm2, frm1], by rw [o4, go3, fo2, fo1]⟩
  · rw [m4, upd_same]
  · rw [m4, upd_other _ _ _ (by omega), g3 h (by omega), f2 h (by omega)]
  · rw [m4, upd_other _ _ _ (by omega), gm3 a (by omega), fm2 a (by omega), fm1 a (by omega)]
  · rw [n4 x a5, gn3 x a4, fn2 x a1 a2 a3, fn1 x a1 a2 a3]

set_option maxHeartbeats 2000000 in
/-- **The flags of the new hole and the keys** (see the module docstring). -/
theorem ytProg_exec (c : Config) (hc : WordsBounded W c)
    {n k HPb VFb KHb HTb RPb YTb YHb VKb TKb : ℕ} {hp vf rp vk ht : ℕ → ℕ}
    (hR : HfRegs c n k HPb VFb KHb HTb RPb YTb YHb VKb TKb)
    (hhp : ∀ i < n, c.nmem (HPb + i) = hp i) (hvf : ∀ i < n, c.nmem (VFb + i) = vf i)
    (hrp : ∀ i < n, c.nmem (RPb + i) = rp i) (hvk : ∀ i < n, c.nmem (VKb + i) = vk i)
    (hht : ∀ h ≤ k, c.nmem (HTb + h) = ht h)
    (hvf1 : ∀ i < n, vf i ≤ 1) (hpk : ∀ i < n, hp i ≤ k) (hht1 : ∀ h ≤ k, ht h ≤ 1)
    (hrpn : ∀ i < n, rp i < n) (hvkn : ∀ i < n, vk i < n)
    (lay : HPb + n ≤ YTb ∧ VFb + n ≤ YTb ∧ HTb + k + 1 ≤ YTb ∧ RPb + n ≤ YTb ∧ VKb + n ≤ YTb ∧
      YTb + n ≤ YHb ∧ YHb + n ≤ TKb ∧ TKb + n ≤ W) (hW : 2 * n + k + 2 ≤ W) :
    ∃ c' t, Exec P W ytProg c c' t ∧ t ≤ 36 * n + 9 ∧
      (∀ i < n, c'.nmem (YTb + i) = vf i + ht (hp i)) ∧
      (∀ i < n, c'.nmem (YHb + i) = vf (rp i) + ht (hp (rp i))) ∧
      (∀ i < n, c'.nmem (TKb + i) = tkV n (hp i) (vk i)) ∧
      (∀ a, ¬ (YTb ≤ a ∧ a < TKb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := lay
  unfold ytProg
  have gR : ∀ c' : Config, (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) →
      ∀ x, ((7100 ≤ x ∧ x ≤ 7110) ∨ x = 6521) → c'.nreg x = c.nreg x := fun c' hr x hx =>
    hr x (by unfold vscr; omega) (by omega) (by omega)
  obtain ⟨c₁, t₁, e₁, ht₁, f1, fm1, fn1, fr1, frm1, fo1⟩ := mapRun_exec (P := P) c hc
    (vb := vbYT) (bnd := 7100) (ob := 7107) (m := n) (Ob := YTb) (B := 7)
    (fun i => vf i + ht (hp i)) hR.r00 hR.r21 hR.r07
    (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega)
    (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      have g := gR c' hr
      have hp1 := hpk i hi
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbYT_exec (P := P) c' hw
        (HPb := HPb) (VFb := VFb) (HTb := HTb) (h := hp i) (v := vf i) (t := ht (hp i)) h20 (by rw [g _ (by omega)]; exact hR.r01)
        (by rw [g _ (by omega)]; exact hR.r02) (by rw [g _ (by omega)]; exact hR.r04)
        (by rw [hm _ (by omega)]; exact hhp i hi) (by rw [hm _ (by omega)]; exact hvf i hi)
        (by rw [hm _ (by omega)]; exact hht _ hp1) (by omega) (by omega) (by omega)
        (by have := hvf1 i hi; have := hht1 _ hp1; omega)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  have hR1 := hR.congr (c' := c₁) (gR c₁ fn1)
  obtain ⟨c₂, t₂, e₂, ht₂, f2, fm2, fn2, fr2, frm2, fo2⟩ := mapRun_exec (P := P) c₁ e₁.wb_right
    (vb := vbYH) (bnd := 7100) (ob := 7108) (m := n) (Ob := YHb) (B := 4)
    (fun i => vf (rp i) + ht (hp (rp i))) hR1.r00 hR1.r21 hR1.r08
    (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega)
    (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      have g := gR c' (fun x a b d => by rw [hr x a b d, fn1 x a b d])
      have hr1 := hrpn i hi
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbYH_exec (P := P) c' hw
        (RPb := RPb) (YTb := YTb) (r := rp i) (y := vf (rp i) + ht (hp (rp i))) h20 (by rw [g _ (by omega)]; exact hR.r06)
        (by rw [g _ (by omega)]; exact hR.r07)
        (by rw [hm _ (by omega), fm1 _ (by omega)]; exact hrp i hi)
        (by rw [hm _ (by omega)]; exact f1 _ hr1) (by omega) (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  have hR2 := hR.congr (c' := c₂) (gR c₂ (fun x a b d => by rw [fn2 x a b d, fn1 x a b d]))
  obtain ⟨c₃, t₃, e₃, ht₃, f3, fm3, fn3, fr3, frm3, fo3⟩ := mapRun_exec (P := P) c₂ e₂.wb_right
    (vb := vbTK) (bnd := 7100) (ob := 7110) (m := n) (Ob := TKb) (B := 10)
    (fun i => tkV n (hp i) (vk i)) hR2.r00 hR2.r21 hR2.r10
    (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega)
    (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      have g := gR c' (fun x a b d => by rw [hr x a b d, fn2 x a b d, fn1 x a b d])
      have hp1 := hpk i hi
      have hv1 := hvkn i hi
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbTK_exec (P := P) c' hw
        (n := n) (HPb := HPb) (VKb := VKb) (h := hp i) (vk := vk i) h20 (by rw [g _ (by omega)]; exact hR.r00)
        (by rw [g _ (by omega)]; exact hR.r01) (by rw [g _ (by omega)]; exact hR.r09)
        (by rw [g _ (by omega)]; exact hR.r21)
        (by rw [hm _ (by omega), fm2 _ (by omega), fm1 _ (by omega)]; exact hhp i hi)
        (by rw [hm _ (by omega), fm2 _ (by omega), fm1 _ (by omega)]; exact hvk i hi)
        (by omega) (by omega) (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, fun i hi => ?_, fun i hi => ?_,
    f3, fun a ha => ?_, fun x a b d => ?_, by rw [fr3, fr2, fr1], by rw [frm3, frm2, frm1],
    by rw [fo3, fo2, fo1]⟩
  · rw [fm3 _ (by omega), fm2 _ (by omega)]; exact f1 i hi
  · rw [fm3 _ (by omega)]; exact f2 i hi
  · rw [fm3 a (by omega), fm2 a (by omega), fm1 a (by omega)]
  · rw [fn3 x a b d, fn2 x a b d, fn1 x a b d]

theorem s7G3a_exec (c : Config) (hc : WordsBounded W c) {k a b : ℕ}
    (q35 : c.nreg 7135 = k) (q36 : c.nreg 7136 = a) (q37 : c.nreg 7137 = b) :
    ∃ c' t, Exec P W (block [.copyN 4910 7135, .copyN 4911 7136, .copyN 4912 7137]) c c' t ∧
      t = 3 ∧ c'.nreg 4910 = k ∧ c'.nreg 4911 = a ∧ c'.nreg 4912 = b ∧
      c'.nmem = c.nmem ∧ (∀ x, (x < 4910 ∨ 4912 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp (disch := omega) only [upd_other, upd_same, q35, q36, q37]

set_option maxHeartbeats 2000000 in
/-- **The gathers of the outputs 2–4** (see the module docstring). -/
theorem s7G_exec (c : Config) (hc : WordsBounded W c) {m k FXb DFb VFb HTb Sb n : ℕ}
    (r30 : c.nreg 7130 = m) (r31 : c.nreg 7131 = FXb) (r32 : c.nreg 7132 = DFb)
    (r02 : c.nreg 7102 = VFb) (r33 : c.nreg 7133 = Sb + m) (r34 : c.nreg 7134 = Sb + 2 * m)
    (r35 : c.nreg 7135 = k) (r36 : c.nreg 7136 = HTb + 1) (r37 : c.nreg 7137 = Sb + 3 * m)
    (hfx : ∀ i < m, c.nmem (FXb + i) < n)
    (lay : FXb + m ≤ Sb ∧ DFb + n ≤ Sb ∧ VFb + n ≤ Sb ∧ HTb + k + 1 ≤ Sb ∧
      Sb + 3 * m + k ≤ W) (hW : m + k + 1 ≤ W) :
    ∃ c' t, Exec P W s7G c c' t ∧ t ≤ 18 * m + 7 * k + 30 ∧
      (∀ i < m, c'.nmem (Sb + m + i) = c.nmem (DFb + c.nmem (FXb + i))) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = c.nmem (VFb + c.nmem (FXb + i))) ∧
      (∀ j < k, c'.nmem (Sb + 3 * m + j) = c.nmem (HTb + 1 + j)) ∧
      (∀ a, ¬ (Sb + m ≤ a ∧ a < Sb + 3 * m + k) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4910 ∨ (4916 < x ∧ x < 6210) ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := lay
  unfold s7G s7G1 s7G2 s7G3
  obtain ⟨c₁, t₁, e₁, ht₁, f1, fm1, fn1, fr1, frm1, fo1⟩ := ggProg_exec (P := P) c hc
    (a := 7130) (b := 7131) (cc := 7132) (dd := 7133) (m := m) (IXb := FXb) (Ab := DFb)
    (OUTb := Sb + m) (by omega) (by omega) (by omega) (by omega) r30 r31 r32 r33 (by omega)
    (by omega) (by omega) (fun j hj => by have := hfx j hj; omega) (fun j hj => by omega)
    (fun j hj => by have := hfx j hj; omega)
  obtain ⟨c₂, t₂, e₂, ht₂, f2, fm2, fn2, fr2, frm2, fo2⟩ := ggProg_exec (P := P) c₁ e₁.wb_right
    (a := 7130) (b := 7131) (cc := 7102) (dd := 7134) (m := m) (IXb := FXb) (Ab := VFb)
    (OUTb := Sb + 2 * m) (by omega) (by omega) (by omega) (by omega)
    (by rw [fn1 _ (by omega)]; exact r30) (by rw [fn1 _ (by omega)]; exact r31)
    (by rw [fn1 _ (by omega)]; exact r02) (by rw [fn1 _ (by omega)]; exact r34) (by omega)
    (by omega) (by omega)
    (fun j hj => by rw [fm1 _ (by omega)]; have := hfx j hj; omega) (fun j hj => by omega)
    (fun j hj => by rw [fm1 _ (by omega)]; have := hfx j hj; omega)
  have q35 : c₂.nreg 7135 = k := by rw [fn2 _ (by omega), fn1 _ (by omega)]; exact r35
  have q36 : c₂.nreg 7136 = HTb + 1 := by rw [fn2 _ (by omega), fn1 _ (by omega)]; exact r36
  have q37 : c₂.nreg 7137 = Sb + 3 * m := by rw [fn2 _ (by omega), fn1 _ (by omega)]; exact r37
  obtain ⟨c₃, t₃, e₃, ht₃, s0, s1, s2, sm3, sn3, sr3, srm3, so3⟩ := s7G3a_exec (P := P) c₂
    e₂.wb_right q35 q36 q37
  obtain ⟨c₄, t₄, e₄, ht₄, f4, fm4, fn4, fr4, frm4, fo4⟩ := cpArr_exec (P := P) c₃ e₃.wb_right
    s0 s1 s2 ⟨Or.inl (by omega), by omega, by omega, by omega⟩
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega,
    fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, fun a ha => ?_, fun x hx => ?_,
    by rw [fr4, sr3, fr2, fr1], by rw [frm4, srm3, frm2, frm1], by rw [fo4, so3, fo2, fo1]⟩
  · have hx := hfx i hi
    rw [fm4 _ (by omega), sm3, fm2 _ (by omega), f1 i hi]
  · have hx := hfx i hi
    rw [fm4 _ (by omega), sm3, f2 i hi, fm1 (FXb + i) (by omega), fm1 _ (by omega)]
  · rw [f4 j hj, sm3, fm2 _ (by omega), fm1 _ (by omega)]
  · rw [fm4 a (by omega), sm3, fm2 a (by omega), fm1 a (by omega)]
  · rw [fn4 x (by omega), sn3 x (by omega), fn2 x (by omega), fn1 x (by omega)]

end Exec

/-! ### The meaning -/

section Sem

variable {D : Type*} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The hole flags**: with the hole labels of the tails, the flags of the path's vertices and
every vertex of `C` a tail of the record, the hole `Hs[j]` meets `C` iff some dart has
`HP[i] · VF[i] = j + 1`. -/
theorem hf_sem {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {C : Finset V} {g : ℕ → D}
    {n : ℕ} {hp vf : ℕ → ℕ} (hhp : ∀ i < n, hp i = hlab Hs (M.tail (g i)))
    (hvf : ∀ i < n, vf i = bf (M.tail (g i) ∈ C))
    (htail : ∀ v ∈ C, ∃ i < n, M.tail (g i) = v) {j : ℕ} (hj : j < Hs.length) :
    (∃ i < n, hp i * vf i = j + 1) ↔ ¬ Disjoint (Hs.getD j ∅) C := by
  constructor
  · rintro ⟨i, hi, e⟩ hdis
    rw [hhp i hi, hvf i hi] at e
    unfold bf at e
    split_ifs at e with hC
    · rw [mul_one, hlab_eq_succ_iff hd hj] at e
      exact disjoint_left.1 hdis e hC
  · intro hm
    obtain ⟨v, hvH, hvC⟩ := not_disjoint_iff.1 hm
    obtain ⟨i, hi, rfl⟩ := htail v hvC
    refine ⟨i, hi, ?_⟩
    rw [hhp i hi, hvf i hi, (hlab_eq_succ_iff hd hj).2 hvH]
    unfold bf; rw [iteT hvC, mul_one]

/-- **The flags of the new hole**: `0 < VF[i] + HT[HP[i]] ↔ tail ∈ newHole Hs C`. -/
theorem yt_sem {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {C : Finset V} {v : V}
    {ht : ℕ → ℕ} (ht0 : ht 0 = 0)
    (hht : ∀ j < Hs.length, (0 < ht (j + 1) ↔ ¬ Disjoint (Hs.getD j ∅) C)) :
    0 < bf (v ∈ C) + ht (hlab Hs v) ↔ v ∈ newHole Hs C := by
  rw [mem_newHole_iff' hd]
  have e1 : 0 < bf (v ∈ C) ↔ v ∈ C := by unfold bf; split_ifs with h <;> simp [h]
  have e2 : 0 < ht (hlab Hs v) ↔ 0 < hlab Hs v ∧ ¬ Disjoint (Hs.getD (hlab Hs v - 1) ∅) C := by
    rcases Nat.eq_zero_or_pos (hlab Hs v) with h0 | hp
    · rw [h0, ht0]; simp
    · obtain ⟨hlt, -⟩ := hlab_mem hp
      have := hht _ hlt
      rw [Nat.sub_add_cancel hp] at this
      rw [this]; exact ⟨fun h => ⟨hp, h⟩, fun h => h.2⟩
  constructor
  · intro h
    by_cases hc : v ∈ C
    · exact Or.inl hc
    · right; apply e2.1
      have : bf (v ∈ C) = 0 := by unfold bf; simp [hc]
      omega
  · rintro (h | h)
    · have := e1.2 h; omega
    · have := e2.2 h; omega

/-- **The keys of the classes of the tails**: with vertex keys `vk < n` (equal iff the tails are
equal), `tkV n (hlab tail) vk` is equal for two darts iff their tails are `HRel`. -/
theorem tk_sem {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {n : ℕ} {u w : V}
    {a b : ℕ} (ha : a < n) (hb : b < n) (hab : a = b ↔ u = w) :
    tkV n (hlab Hs u) a = tkV n (hlab Hs w) b ↔ HRel Hs u w := by
  rw [tkV_eq, tkV_eq]
  have hlab_eq_of : ∀ x y : V, HRel Hs x y → hlab Hs x = hlab Hs y := by
    rintro x y (rfl | ⟨H, hH, hx, hy⟩)
    · rfl
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hH
      have hj' : Hs.getD j ∅ = Hs[j] := getD_eq_get hj
      rw [(hlab_eq_succ_iff hd hj).2 (by rw [hj']; exact hx),
        (hlab_eq_succ_iff hd hj).2 (by rw [hj']; exact hy)]
  constructor
  · intro h
    split_ifs at h with h1 h2 h2
    · exact Or.inl (hab.1 h)
    · omega
    · omega
    · have e : hlab Hs u = hlab Hs w := by omega
      have hp : 0 < hlab Hs u := Nat.pos_of_ne_zero h1
      obtain ⟨hlt, hm⟩ := hlab_mem hp
      have hm' : w ∈ Hs.getD (hlab Hs u - 1) ∅ := by
        rw [e]; exact (hlab_mem (by omega)).2
      exact Or.inr ⟨_, sm_getD_mem hlt, hm, hm'⟩
  · intro h
    have e := hlab_eq_of u w h
    split_ifs with h1 h2 h2
    · rcases h with rfl | ⟨H, hH, hx, hy⟩
      · exact hab.2 rfl
      · exact absurd (hlab_pos_iff.2 (mem_hunion.2 ⟨H, hH, hx⟩)) (by omega)
    · omega
    · omega
    · omega

end Sem

end MfDrv

end BKMNW

end PlanarFlow
