module

public import PlanarFlow.BKMNW.PfS

/-!
# The path's flags on the record, the program `lgPF`

From the path's darts as `1 +` core indices at `PD` (`PathPD`, written by `mbD`), the core's
enumeration `IX` (core index → record index), the record's reverses `RP` and tail numbers `VP`:

`lgPF = pf0 ; vkLoop ; zfill ; (KA, KB, KC, KD by mapRunS) ; 4 × (pfSx ; pfMk) ; (VF by mapRunS)`

* `VK = vkF VP` (vertex keys; `TailSorted`) at `Yb`, the tables `VM` (`n + 1`) at `Yb + n` and
  `DF` (`n + 1`) at `Yb + 2n + 1`, `VF` at `Yb + 3n + 2`, the keys `KA … KD` at
  `Yb + 4n + 2 … Yb + 7n + 2` (scratch `[Yb, Yb + 8n + 2)`);
* **`lgPF_exec`**: within `150 n + 100` steps, `DF[i] = 1` iff `i` is a key `pfKB`/`pfKC`
  (else `0`) and `VF[i] = 1` iff `VK[i]` is a key `pfKA`/`pfKD` (else `0`), `i < n`; memory
  outside the scratch kept. With `pf_darts_keys` / `pf_mverts_keys` (`PfS.lean`): `DF[i] = 1` iff
  `g i ∈ ρ.darts`, `VF[i] = 1` iff `tail (g i) ∈ ρ.mverts`.

Inputs: `6000 = n`, `6001 = RPb`, `6002 = IXb`, `6003 = PDb`, `6011 = Yb`, `6012 = VPb`.
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

/-- The registers of `lgPF`. -/
def pf0 : Stmt :=
  block [.constN 6010 1, .constN 6521 1, .copyN 6004 6011, .addN 6005 6011 6000,
    .addN 6006 6005 6000, .addN 6006 6006 6010, .addN 6007 6006 6000, .addN 6007 6007 6010,
    .addN 6008 6007 6000, .addN 6009 6008 6000, .addN 6013 6009 6000, .addN 6014 6013 6000,
    .subN 6015 6000 6010, .subN 6018 6017 6010, .addN 6016 6000 6000, .addN 6016 6016 6010, .addN 6016 6016 6010,
    .copyN 5800 6000, .copyN 5803 6012, .copyN 5873 6011, .constN 5806 1]

/-- The marks of the tails. -/
def pfS1 : Stmt := block [.copyN 6030 6017, .copyN 6031 6008, .copyN 6032 6005]
/-- The marks of the heads. -/
def pfS2 : Stmt := block [.copyN 6030 6018, .copyN 6031 6014, .copyN 6032 6005]
/-- The marks of the darts. -/
def pfS3 : Stmt := block [.copyN 6030 6018, .copyN 6031 6009, .copyN 6032 6006]
/-- The marks of the reverses. -/
def pfS4 : Stmt := block [.copyN 6030 6018, .copyN 6031 6013, .copyN 6032 6006]

/-- The keys. -/
def pfKeys : Stmt :=
  .seq (mapRunS vbPA 6017 6008) (.seq (mapRunS vbPB 6018 6009)
    (.seq (mapRunS vbPC 6018 6013) (mapRunS vbPD 6018 6014)))

/-- The marks. -/
def pfMarks : Stmt :=
  .seq (.seq pfS1 pfMk) (.seq (.seq pfS2 pfMk) (.seq (.seq pfS3 pfMk) (.seq pfS4 pfMk)))

/-- **The path's flags on the record.** -/
def lgPF : Stmt :=
  .seq (.seq pf0 (.seq vkLoop (zfill 6016 6005)))
    (.seq pfKeys (.seq pfMarks (mapRunS vbPV 6000 6007)))

section Exec

variable {P : Input} {W : ℕ}

theorem pf0_exec (c : Config) (hc : WordsBounded W c) {n np Yb VPb : ℕ}
    (r00 : c.nreg 6000 = n) (r17 : c.nreg 6017 = np) (r11 : c.nreg 6011 = Yb)
    (r12 : c.nreg 6012 = VPb)
    (w : Yb + 8 * n + 2 ≤ W) (w1 : 1 ≤ n) :
    ∃ c' t, Exec P W pf0 c c' t ∧ t = 21 ∧ c'.nreg 6010 = 1 ∧ c'.nreg 6521 = 1 ∧
      c'.nreg 6018 = np - 1 ∧
      c'.nreg 6004 = Yb ∧ c'.nreg 6005 = Yb + n ∧ c'.nreg 6006 = Yb + 2 * n + 1 ∧
      c'.nreg 6007 = Yb + 3 * n + 2 ∧ c'.nreg 6008 = Yb + 4 * n + 2 ∧
      c'.nreg 6009 = Yb + 5 * n + 2 ∧ c'.nreg 6013 = Yb + 6 * n + 2 ∧
      c'.nreg 6014 = Yb + 7 * n + 2 ∧ c'.nreg 6015 = n - 1 ∧ c'.nreg 6016 = 2 * n + 2 ∧
      c'.nreg 5800 = n ∧ c'.nreg 5803 = VPb ∧ c'.nreg 5873 = Yb ∧ c'.nreg 5806 = 1 ∧
      c'.nmem = c.nmem ∧
      (∀ x, x ≠ 6010 → x ≠ 6521 → x ≠ 6018 → (x < 6004 ∨ (6009 < x ∧ x < 6013) ∨ 6016 < x) →
        x ≠ 5800 → x ≠ 5803 → x ≠ 5873 → x ≠ 5806 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pf0
  exec_block
  all_goals try (config_simp; (try simp only [r00, r11, r12, r17]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl,
    fun x h1 h2 h8 h3 h4 h5 h6 h7 => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r00, r11, r12, r17]); done)
  all_goals try (config_simp; (try simp only [r00, r11, r12, r17]); omega)
  · config_simp; simp (disch := omega) only [upd_other]

theorem pfS_exec (c : Config) (hc : WordsBounded W c) {a b d : ℕ} (ha : a < 6030 ∨ 6032 < a)
    (hb : b < 6030 ∨ 6032 < b) (hd : d < 6030 ∨ 6032 < d) :
    ∃ c' t, Exec P W (block [.copyN 6030 a, .copyN 6031 b, .copyN 6032 d]) c c' t ∧ t = 3 ∧
      c'.nreg 6030 = c.nreg a ∧ c'.nreg 6031 = c.nreg b ∧ c'.nreg 6032 = c.nreg d ∧
      c'.nmem = c.nmem ∧ (∀ x, (x < 6030 ∨ 6032 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp (disch := omega) only [upd_other, upd_same]

/-- The registers `lgPF` keeps. -/
def pfKeepR (x : ℕ) : Prop :=
  x < 5800 ∨ (5806 < x ∧ x < 5873) ∨ (5873 < x ∧ x < 5890) ∨ (5896 < x ∧ x < 6004) ∨
    x = 6011 ∨ x = 6012 ∨ x = 6017 ∨ (6018 < x ∧ x < 6030) ∨ (6035 < x ∧ x < 6520) ∨ 6529 < x

/-- The registers of `lgPF` after the set-up. -/
structure PfRegs (c : Config) (n np Yb : ℕ) : Prop where
  r00 : c.nreg 6000 = n
  r17 : c.nreg 6017 = np
  r18 : c.nreg 6018 = np - 1
  r04 : c.nreg 6004 = Yb
  r05 : c.nreg 6005 = Yb + n
  r06 : c.nreg 6006 = Yb + 2 * n + 1
  r07 : c.nreg 6007 = Yb + 3 * n + 2
  r08 : c.nreg 6008 = Yb + 4 * n + 2
  r09 : c.nreg 6009 = Yb + 5 * n + 2
  r13 : c.nreg 6013 = Yb + 6 * n + 2
  r14 : c.nreg 6014 = Yb + 7 * n + 2
  r15 : c.nreg 6015 = n - 1
  r10 : c.nreg 6010 = 1
  r21 : c.nreg 6521 = 1

lemma PfRegs.congr {c c' : Config} {n np Yb : ℕ} (h : PfRegs c n np Yb)
    (e : ∀ x, (6000 ≤ x ∧ x ≤ 6018) ∨ x = 6521 → c'.nreg x = c.nreg x) : PfRegs c' n np Yb :=
  ⟨by rw [e _ (by omega)]; exact h.r00, by rw [e _ (by omega)]; exact h.r17,
    by rw [e _ (by omega)]; exact h.r18, by rw [e _ (by omega)]; exact h.r04,
    by rw [e _ (by omega)]; exact h.r05, by rw [e _ (by omega)]; exact h.r06,
    by rw [e _ (by omega)]; exact h.r07, by rw [e _ (by omega)]; exact h.r08,
    by rw [e _ (by omega)]; exact h.r09, by rw [e _ (by omega)]; exact h.r13,
    by rw [e _ (by omega)]; exact h.r14, by rw [e _ (by omega)]; exact h.r15,
    by rw [e _ (by omega)]; exact h.r10, by rw [e _ (by omega)]; exact h.r21⟩

set_option maxHeartbeats 1000000 in
/-- The keys of the tails (`mapRunS vbPA`). -/
theorem pfKA_exec (c : Config) (hc : WordsBounded W c) {n np n' IXb PDb Yb : ℕ}
    {pd ix vk : ℕ → ℕ} (hR : PfRegs c n np Yb) (r02 : c.nreg 6002 = IXb) (r03 : c.nreg 6003 = PDb)
    (hpd : ∀ j < np, c.nmem (PDb + j) = pd j) (hix : ∀ q < n', c.nmem (IXb + q) = ix q)
    (hvk : ∀ i < n, c.nmem (Yb + i) = vk i)
    (hPD : ∀ j < np, pd j ≤ n') (hIX : ∀ q < n', ix q < n) (hn' : 1 ≤ n') (hnp : np ≤ n)
    (lay : IXb + n' ≤ Yb ∧ PDb + np ≤ Yb ∧ Yb + 8 * n + 2 ≤ W) :
    ∃ c' t, Exec P W (mapRunS vbPA 6017 6008) c c' t ∧ t ≤ 17 * n + 3 ∧
      (∀ j < np, c'.nmem (Yb + 4 * n + 2 + j) = pfKA pd ix vk n j) ∧
      (∀ a, ¬ (Yb + 4 * n + 2 ≤ a ∧ a < Yb + 4 * n + 2 + np) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3⟩ := lay
  obtain ⟨c', t, e, ht, f, fm, fn, fr, frm, fo⟩ := mapRun_exec (P := P) c hc
    (vb := vbPA) (bnd := 6017) (ob := 6008) (m := np) (Ob := Yb + 4 * n + 2) (B := 12)
    (pfKA pd ix vk n) hR.r17 hR.r21 hR.r08
    (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega)
    (by omega) (by omega)
    (fun j hj c' hw h20 hr hm => by
      have hq : pd j - 1 < n' := by have := hPD j hj; omega
      have hi := hIX _ hq
      have e1 : c'.nmem (PDb + j) = pd j := by rw [hm _ (by omega), hpd j hj]
      have e2 : c'.nmem (IXb + (pd j - 1)) = ix (pd j - 1) := by
        rw [hm _ (by omega), hix _ hq]
      have e3 : c'.nmem (Yb + ix (pd j - 1)) = vk (ix (pd j - 1)) := by
        rw [hm _ (by omega), hvk _ hi]
      have g : ∀ x, ((6000 ≤ x ∧ x ≤ 6018) ∨ x = 6521) → c'.nreg x = c.nreg x := fun x hx =>
        hr x (by unfold vscr; omega) (by omega) (by omega)
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbPA_exec (P := P) c' hw (n := n)
        (PDb := PDb) (IXb := IXb) (VKb := Yb) h20 (by rw [g _ (by omega)]; exact hR.r00)
        (by rw [g _ (by omega)]; exact r02) (by rw [g _ (by omega)]; exact r03)
        (by rw [g _ (by omega)]; exact hR.r04) (by rw [g _ (by omega)]; exact hR.r10)
        e1 e2 e3 (by omega) (by omega) (by omega) (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  exact ⟨c', t, e, by omega, f, fm, fn, fr, frm, fo⟩

set_option maxHeartbeats 1000000 in
/-- The keys of the first darts (`mapRunS vbPB`). -/
theorem pfKB_exec (c : Config) (hc : WordsBounded W c) {n np n' IXb PDb Yb : ℕ}
    {pd ix : ℕ → ℕ} (hR : PfRegs c n np Yb) (r02 : c.nreg 6002 = IXb) (r03 : c.nreg 6003 = PDb)
    (hpd : ∀ j < np, c.nmem (PDb + j) = pd j) (hix : ∀ q < n', c.nmem (IXb + q) = ix q)
    (hPD : ∀ j < np, pd j ≤ n') (hnp : np ≤ n) (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (lay : IXb + n' ≤ Yb ∧ PDb + np ≤ Yb ∧ Yb + 8 * n + 2 ≤ W) :
    ∃ c' t, Exec P W (mapRunS vbPB 6018 6009) c c' t ∧ t ≤ 17 * n + 3 ∧
      (∀ j < np - 1, c'.nmem (Yb + 5 * n + 2 + j) = pfKB pd ix n j) ∧
      (∀ a, ¬ (Yb + 5 * n + 2 ≤ a ∧ a < Yb + 5 * n + 2 + (np - 1)) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3⟩ := lay
  obtain ⟨c', t, e, ht, f, fm, fn, fr, frm, fo⟩ := mapRun_exec (P := P) c hc
    (vb := vbPB) (bnd := 6018) (ob := 6009) (m := np - 1) (Ob := Yb + 5 * n + 2) (B := 12)
    (pfKB pd ix n) hR.r18 hR.r21 hR.r09
    (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega)
    (by omega) (by omega)
    (fun j hj c' hw h20 hr hm => by
      have hq : pd j - 1 < n' := by have := hPD j (by omega); omega
      have e1 : c'.nmem (PDb + j) = pd j := by rw [hm _ (by omega), hpd j (by omega)]
      have e1' : c'.nmem (PDb + j + 1) = pd (j + 1) := by
        rw [hm _ (by omega), show PDb + j + 1 = PDb + (j + 1) by omega, hpd _ (by omega)]
      have e2 : c'.nmem (IXb + (pd j - 1)) = ix (pd j - 1) := by
        rw [hm _ (by omega), hix _ hq]
      have g : ∀ x, ((6000 ≤ x ∧ x ≤ 6018) ∨ x = 6521) → c'.nreg x = c.nreg x := fun x hx =>
        hr x (by unfold vscr; omega) (by omega) (by omega)
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbPB_exec (P := P) c' hw (n := n)
        (PDb := PDb) (IXb := IXb) h20 (by rw [g _ (by omega)]; exact hR.r00)
        (by rw [g _ (by omega)]; exact r02) (by rw [g _ (by omega)]; exact r03)
        (by rw [g _ (by omega)]; exact hR.r10)
        e1 e1' e2 (by omega) (by omega) (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  exact ⟨c', t, e, by have : np - 1 ≤ np := Nat.sub_le np 1; omega, f, fm, fn, fr, frm, fo⟩

set_option maxHeartbeats 1000000 in
/-- The keys of the reverses (`mapRunS vbPC`). -/
theorem pfKC_exec (c : Config) (hc : WordsBounded W c) {n np n' RPb IXb PDb Yb : ℕ}
    {pd ix rp : ℕ → ℕ} (hR : PfRegs c n np Yb) (r01 : c.nreg 6001 = RPb)
    (r02 : c.nreg 6002 = IXb) (r03 : c.nreg 6003 = PDb)
    (hpd : ∀ j < np, c.nmem (PDb + j) = pd j) (hix : ∀ q < n', c.nmem (IXb + q) = ix q)
    (hrp : ∀ i < n, c.nmem (RPb + i) = rp i)
    (hPD : ∀ j < np, pd j ≤ n') (hnp : np ≤ n) (hIX : ∀ q < n', ix q < n) (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (lay : RPb + n ≤ Yb ∧ IXb + n' ≤ Yb ∧ PDb + np ≤ Yb ∧ Yb + 8 * n + 2 ≤ W) :
    ∃ c' t, Exec P W (mapRunS vbPC 6018 6013) c c' t ∧ t ≤ 19 * n + 3 ∧
      (∀ j < np - 1, c'.nmem (Yb + 6 * n + 2 + j) = pfKC pd ix rp n j) ∧
      (∀ a, ¬ (Yb + 6 * n + 2 ≤ a ∧ a < Yb + 6 * n + 2 + (np - 1)) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l0, l1, l2, l3⟩ := lay
  obtain ⟨c', t, e, ht, f, fm, fn, fr, frm, fo⟩ := mapRun_exec (P := P) c hc
    (vb := vbPC) (bnd := 6018) (ob := 6013) (m := np - 1) (Ob := Yb + 6 * n + 2) (B := 14)
    (pfKC pd ix rp n) hR.r18 hR.r21 hR.r13
    (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega)
    (by omega) (by omega)
    (fun j hj c' hw h20 hr hm => by
      have hq : pd j - 1 < n' := by have := hPD j (by omega); omega
      have hi := hIX _ hq
      have e1 : c'.nmem (PDb + j) = pd j := by rw [hm _ (by omega), hpd j (by omega)]
      have e1' : c'.nmem (PDb + j + 1) = pd (j + 1) := by
        rw [hm _ (by omega), show PDb + j + 1 = PDb + (j + 1) by omega, hpd _ (by omega)]
      have e2 : c'.nmem (IXb + (pd j - 1)) = ix (pd j - 1) := by
        rw [hm _ (by omega), hix _ hq]
      have e3 : c'.nmem (RPb + ix (pd j - 1)) = rp (ix (pd j - 1)) := by
        rw [hm _ (by omega), hrp _ hi]
      have g : ∀ x, ((6000 ≤ x ∧ x ≤ 6018) ∨ x = 6521) → c'.nreg x = c.nreg x := fun x hx =>
        hr x (by unfold vscr; omega) (by omega) (by omega)
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbPC_exec (P := P) c' hw (n := n)
        (PDb := PDb) (IXb := IXb) (RPb := RPb) h20 (by rw [g _ (by omega)]; exact hR.r00)
        (by rw [g _ (by omega)]; exact r01) (by rw [g _ (by omega)]; exact r02)
        (by rw [g _ (by omega)]; exact r03) (by rw [g _ (by omega)]; exact hR.r10)
        e1 e1' e2 e3 (by omega) (by omega) (by omega) (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  exact ⟨c', t, e, by have : np - 1 ≤ np := Nat.sub_le np 1; omega, f, fm, fn, fr, frm, fo⟩

set_option maxHeartbeats 1000000 in
/-- The keys of the heads (`mapRunS vbPD`). -/
theorem pfKD_exec (c : Config) (hc : WordsBounded W c) {n np n' RPb IXb PDb Yb : ℕ}
    {pd ix rp vk : ℕ → ℕ} (hR : PfRegs c n np Yb) (r01 : c.nreg 6001 = RPb)
    (r02 : c.nreg 6002 = IXb) (r03 : c.nreg 6003 = PDb)
    (hpd : ∀ j < np, c.nmem (PDb + j) = pd j) (hix : ∀ q < n', c.nmem (IXb + q) = ix q)
    (hrp : ∀ i < n, c.nmem (RPb + i) = rp i) (hvk : ∀ i < n, c.nmem (Yb + i) = vk i)
    (hPD : ∀ j < np, pd j ≤ n') (hnp : np ≤ n) (hIX : ∀ q < n', ix q < n) (hRP : ∀ i < n, rp i < n)
    (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (lay : RPb + n ≤ Yb ∧ IXb + n' ≤ Yb ∧ PDb + np ≤ Yb ∧ Yb + 8 * n + 2 ≤ W) :
    ∃ c' t, Exec P W (mapRunS vbPD 6018 6014) c c' t ∧ t ≤ 21 * n + 3 ∧
      (∀ j < np - 1, c'.nmem (Yb + 7 * n + 2 + j) = pfKD pd ix rp vk n j) ∧
      (∀ a, ¬ (Yb + 7 * n + 2 ≤ a ∧ a < Yb + 7 * n + 2 + (np - 1)) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l0, l1, l2, l3⟩ := lay
  obtain ⟨c', t, e, ht, f, fm, fn, fr, frm, fo⟩ := mapRun_exec (P := P) c hc
    (vb := vbPD) (bnd := 6018) (ob := 6014) (m := np - 1) (Ob := Yb + 7 * n + 2) (B := 16)
    (pfKD pd ix rp vk n) hR.r18 hR.r21 hR.r14
    (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega)
    (by omega) (by omega)
    (fun j hj c' hw h20 hr hm => by
      have hq : pd j - 1 < n' := by have := hPD j (by omega); omega
      have hi := hIX _ hq
      have hr2 := hRP _ hi
      have e1 : c'.nmem (PDb + j) = pd j := by rw [hm _ (by omega), hpd j (by omega)]
      have e1' : c'.nmem (PDb + j + 1) = pd (j + 1) := by
        rw [hm _ (by omega), show PDb + j + 1 = PDb + (j + 1) by omega, hpd _ (by omega)]
      have e2 : c'.nmem (IXb + (pd j - 1)) = ix (pd j - 1) := by
        rw [hm _ (by omega), hix _ hq]
      have e3 : c'.nmem (RPb + ix (pd j - 1)) = rp (ix (pd j - 1)) := by
        rw [hm _ (by omega), hrp _ hi]
      have e4 : c'.nmem (Yb + rp (ix (pd j - 1))) = vk (rp (ix (pd j - 1))) := by
        rw [hm _ (by omega), hvk _ hr2]
      have g : ∀ x, ((6000 ≤ x ∧ x ≤ 6018) ∨ x = 6521) → c'.nreg x = c.nreg x := fun x hx =>
        hr x (by unfold vscr; omega) (by omega) (by omega)
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbPD_exec (P := P) c' hw (n := n)
        (PDb := PDb) (IXb := IXb) (RPb := RPb) (VKb := Yb) h20
        (by rw [g _ (by omega)]; exact hR.r00)
        (by rw [g _ (by omega)]; exact r01) (by rw [g _ (by omega)]; exact r02)
        (by rw [g _ (by omega)]; exact r03) (by rw [g _ (by omega)]; exact hR.r04)
        (by rw [g _ (by omega)]; exact hR.r10)
        e1 e1' e2 e3 e4 (by omega) (by omega) (by omega) (by omega) (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  exact ⟨c', t, e, by have : np - 1 ≤ np := Nat.sub_le np 1; omega, f, fm, fn, fr, frm, fo⟩

set_option maxHeartbeats 1000000 in
/-- **`lgPF`, the set-up**: `pf0 ; vkLoop ; zfill` (the vertex keys `VK`, the tables zeroed). -/
theorem pfA1_exec (c : Config) (hc : WordsBounded W c) {n np Yb VPb : ℕ}
    (r00 : c.nreg 6000 = n) (r17 : c.nreg 6017 = np) (r11 : c.nreg 6011 = Yb) (r12 : c.nreg 6012 = VPb) (hn : 1 ≤ n)
    (lay : VPb + n ≤ Yb ∧ Yb + 8 * n + 2 ≤ W) :
    ∃ c' t, Exec P W (.seq pf0 (.seq vkLoop (zfill 6016 6005))) c c' t ∧ t ≤ 30 * n + 40 ∧
      PfRegs c' n np Yb ∧
      (∀ i < n, c'.nmem (Yb + i) = vkF (fun j => c.nmem (VPb + j)) i) ∧
      (∀ j < 2 * n + 2, c'.nmem (Yb + n + j) = 0) ∧
      (∀ a, (a < Yb ∨ Yb + 3 * n + 2 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5800 ∨ (5806 < x ∧ x < 5873) ∨ (5873 < x ∧ x < 5890) ∨ (5896 < x ∧ x < 6004) ∨
        (6010 < x ∧ x < 6013) ∨ x = 6017 ∨ (6018 < x ∧ x < 6520) ∨ 6529 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2⟩ := lay
  obtain ⟨c₁, t₁, e₁, ht₁, a10, a21, a18, a04, a05, a06, a07, a08, a09, a13, a14, a15, a16, a5800,
    a5803, a5873, a5806, am₁, an₁, ar₁, arm₁, ao₁⟩ := pf0_exec (P := P) c hc r00 r17 r11 r12
      (by omega) hn
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, t₂, e₂, ht₂, v1, vm₂, vn₂, vr₂, vrm₂, vo₂⟩ := vkLoop_exec (P := P) c₁ hw₁ a5800
    a5803 a5873 a5806 (by omega) (by omega) (by omega) (by omega) (fun i hi h => by omega)
  have hw₂ := e₂.wb_right
  rw [am₁] at v1
  obtain ⟨c₃, t₃, e₃, ht₃, z1, zm₃, zn₃, zr₃, zrm₃, zo₃⟩ := zfill_exec (P := P) c₂ hw₂
    (bnd := 6016) (ob := 6005) (m := 2 * n + 2) (Ob := Yb + n)
    (by rw [vn₂ _ (by omega)]; exact a16) (by rw [vn₂ _ (by omega)]; exact a21)
    (by rw [vn₂ _ (by omega)]; exact a05) (by omega) (by omega) (by unfold vscr; omega)
    (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
  have k : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → (x < 5890 ∨ 5896 < x) →
      c₃.nreg x = c₁.nreg x := fun x h1 h2 h3 h4 => by rw [zn₃ x h1 h2 h3, vn₂ x h4]
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega,
    PfRegs.congr (n := n) (np := np) (Yb := Yb) (c := c₁)
      ⟨by rw [an₁ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), r00],
        by rw [an₁ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), r17], a18, a04, a05, a06, a07, a08, a09, a13, a14, a15, a10, a21⟩
      (fun x hx => k x (by unfold vscr; omega) (by omega) (by omega) (by omega)),
    fun i hi => by rw [zm₃ _ (by omega)]; exact v1 i hi, z1,
    fun a ha => by rw [zm₃ a (by omega), vm₂ a (by omega), am₁], fun x hx => ?_,
    by rw [zr₃, vr₂, ar₁], by rw [zrm₃, vrm₂, arm₁], by rw [zo₃, vo₂, ao₁]⟩
  rw [k x (by unfold vscr; omega) (by omega) (by omega) (by omega),
    an₁ x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]

set_option maxHeartbeats 1000000 in
/-- One table of marks: `pfSx ; pfMk` with the keys at `KEYb` (`m` of them, `≤ n`) into the
table at `Tb` (`n + 1` cells). -/
theorem pfMark_exec (c : Config) (hc : WordsBounded W c) {a b d m n KEYb Tb : ℕ}
    (ha : a < 6030 ∨ 6032 < a) (hb : b < 6030 ∨ 6032 < b) (hd : d < 6030 ∨ 6032 < d)
    (ra : c.nreg a = m) (rb : c.nreg b = KEYb) (rd : c.nreg d = Tb) {key : ℕ → ℕ}
    (hkey : ∀ j < m, c.nmem (KEYb + j) = key j) (hkn : ∀ j < m, key j ≤ n)
    (d1 : KEYb + m ≤ Tb ∨ Tb + n + 1 ≤ KEYb) (w1 : KEYb + m ≤ W) (w2 : Tb + n + 1 ≤ W)
    (w3 : m + 1 ≤ W) :
    ∃ c' t, Exec P W (.seq (block [.copyN 6030 a, .copyN 6031 b, .copyN 6032 d]) pfMk) c c' t ∧
      t ≤ 7 * m + 7 ∧
      (∀ x < n + 1, c'.nmem (Tb + x) =
        if ∃ j < m, key j = x then 1 else c.nmem (Tb + x)) ∧
      (∀ a, ¬ (Tb ≤ a ∧ a < Tb + (n + 1)) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6030 ∨ 6035 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, s0, s1, s2, sm₁, sn₁, sr₁, srm₁, so₁⟩ := pfS_exec (P := P) c hc ha hb hd
  obtain ⟨c₂, t₂, e₂, ht₂, g, gm₂, gn₂, gr₂, grm₂, go₂⟩ := pfMk_exec (P := P) c₁ e₁.wb_right
    (m := m) (nk := n + 1) (KEYb := KEYb) (Tb := Tb) (by rw [s0, ra]) (by rw [s1, rb])
    (by rw [s2, rd]) (fun j hj => by rw [sm₁, hkey j hj]; have := hkn j hj; omega)
    (fun j hj => by omega) w1 (by omega) w3
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, fun x hx => ?_, fun a ha => ?_, fun x hx => ?_,
    by rw [gr₂, sr₁], by rw [grm₂, srm₁], by rw [go₂, so₁]⟩
  · rw [g x hx, sm₁]
    congr 1
    apply propext
    constructor
    · rintro ⟨j, hj, h⟩; exact ⟨j, hj, by rw [← hkey j hj]; exact h⟩
    · rintro ⟨j, hj, h⟩; exact ⟨j, hj, by rw [hkey j hj]; exact h⟩
  · rw [gm₂ a ha, sm₁]
  · rw [gn₂ x (by omega), sn₁ x (by omega)]

set_option maxHeartbeats 1000000 in
/-- The vertex flags `VF[i] = VM[VK[i]]` (`mapRunS vbPV`). -/
theorem pfVF_exec (c : Config) (hc : WordsBounded W c) {n np Yb : ℕ} {vk : ℕ → ℕ}
    (hR : PfRegs c n np Yb) (hvk : ∀ i < n, c.nmem (Yb + i) = vk i) (hvkn : ∀ i < n, vk i < n)
    (lay : Yb + 8 * n + 2 ≤ W) :
    ∃ c' t, Exec P W (mapRunS vbPV 6000 6007) c c' t ∧ t ≤ 9 * n + 3 ∧
      (∀ i < n, c'.nmem (Yb + 3 * n + 2 + i) = c.nmem (Yb + n + vk i)) ∧
      (∀ a, ¬ (Yb + 3 * n + 2 ≤ a ∧ a < Yb + 3 * n + 2 + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, e, ht, f, fm, fn, fr, frm, fo⟩ := mapRun_exec (P := P) c hc
    (vb := vbPV) (bnd := 6000) (ob := 6007) (m := n) (Ob := Yb + 3 * n + 2) (B := 4)
    (fun i => c.nmem (Yb + n + vk i)) hR.r00 hR.r21 hR.r07
    (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega)
    (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      have hv := hvkn i hi
      have e1 : c'.nmem (Yb + i) = vk i := by rw [hm _ (by omega), hvk i hi]
      have g : ∀ x, ((6000 ≤ x ∧ x ≤ 6018) ∨ x = 6521) → c'.nreg x = c.nreg x := fun x hx =>
        hr x (by unfold vscr; omega) (by omega) (by omega)
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbPV_exec (P := P) c' hw
        (VKb := Yb) (VMb := Yb + n) h20 (by rw [g _ (by omega)]; exact hR.r04)
        (by rw [g _ (by omega)]; exact hR.r05) e1 (by omega) (by omega)
      rw [hm _ (by omega)] at v
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  exact ⟨c', t, e, by omega, f, fm, fn, fr, frm, fo⟩

lemma pf_key_le {f x n : ℕ} (hf : f ≤ 1) (hx : x < n) : pdSel f x n ≤ n :=
  pdSel_le hf hx.le le_rfl

lemma pf_if_or {p q : Prop} [Decidable p] [Decidable q] :
    (if q then 1 else if p then 1 else 0) = (if p ∨ q then 1 else 0 : ℕ) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

lemma pf_if_or2 {m : ℕ} {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] :
    (if ∃ j < m, q j then 1 else if ∃ j < m, p j then 1 else 0) =
      (if ∃ j < m, p j ∨ q j then 1 else 0 : ℕ) := by
  by_cases hp : ∃ j < m, p j <;> by_cases hq : ∃ j < m, q j
  · rw [iteT hq, iteT (by obtain ⟨j, hj, h⟩ := hp; exact ⟨j, hj, Or.inl h⟩)]
  · rw [iteF hq, iteT hp, iteT (by obtain ⟨j, hj, h⟩ := hp; exact ⟨j, hj, Or.inl h⟩)]
  · rw [iteT hq, iteT (by obtain ⟨j, hj, h⟩ := hq; exact ⟨j, hj, Or.inr h⟩)]
  · rw [iteF hq, iteF hp, iteF]
    rintro ⟨j, hj, h | h⟩
    · exact hp ⟨j, hj, h⟩
    · exact hq ⟨j, hj, h⟩

set_option maxHeartbeats 2000000 in
/-- **The path's flags on the record** (see the module docstring). -/
theorem lgPF_exec (c : Config) (hc : WordsBounded W c) {n np n' RPb IXb PDb Yb VPb : ℕ}
    (r00 : c.nreg 6000 = n) (r17 : c.nreg 6017 = np) (r01 : c.nreg 6001 = RPb) (r02 : c.nreg 6002 = IXb)
    (r03 : c.nreg 6003 = PDb) (r11 : c.nreg 6011 = Yb) (r12 : c.nreg 6012 = VPb)
    (hn : 1 ≤ n) (hn' : 1 ≤ n') (hnp1 : 1 ≤ np) (hnp : np ≤ n)
    (hRP : ∀ i < n, c.nmem (RPb + i) < n) (hIX : ∀ q < n', c.nmem (IXb + q) < n)
    (hPD : ∀ j < np, c.nmem (PDb + j) ≤ n')
    (lay : RPb + n ≤ Yb ∧ IXb + n' ≤ Yb ∧ PDb + np ≤ Yb ∧ VPb + n ≤ Yb ∧ Yb + 8 * n + 2 ≤ W) :
    ∃ c' t, Exec P W lgPF c c' t ∧ t ≤ 150 * n + 100 ∧
      (∀ i < n, c'.nmem (Yb + 2 * n + 1 + i) =
        if ∃ j < np - 1, pfKB (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q)) n j = i ∨
          pfKC (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q))
            (fun i => c.nmem (RPb + i)) n j = i then 1 else 0) ∧
      (∀ i < n, c'.nmem (Yb + 3 * n + 2 + i) =
        if (∃ j < np, pfKA (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q))
            (vkF (fun j => c.nmem (VPb + j))) n j = vkF (fun j => c.nmem (VPb + j)) i) ∨
          (∃ j < np - 1, pfKD (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q))
            (fun i => c.nmem (RPb + i)) (vkF (fun j => c.nmem (VPb + j))) n j =
              vkF (fun j => c.nmem (VPb + j)) i) then 1 else 0) ∧
      (∀ a, ¬ (Yb ≤ a ∧ a < Yb + 8 * n + 2) → c'.nmem a = c.nmem a) ∧
      (∀ x, pfKeepR x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l0, l1, l2, l3, l4⟩ := lay
  have hvkn : ∀ i < n, vkF (fun j => c.nmem (VPb + j)) i < n := fun i hi =>
    lt_of_le_of_lt (vkF_le _ i) hi
  -- the set-up
  obtain ⟨c₁, t₁, e₁, ht₁, hR₁, vk₁, z₁, m₁, k₁, rr₁, rm₁, o₁⟩ := pfA1_exec (P := P) c hc r00 r17 r11
    r12 hn ⟨l3, l4⟩
  have hw₁ := e₁.wb_right
  have hpd₁ : ∀ j < np, c₁.nmem (PDb + j) = c.nmem (PDb + j) := fun j hj => m₁ _ (by omega)
  have hix₁ : ∀ q < n', c₁.nmem (IXb + q) = c.nmem (IXb + q) := fun q hq => m₁ _ (by omega)
  have hrp₁ : ∀ i < n, c₁.nmem (RPb + i) = c.nmem (RPb + i) := fun i hi => m₁ _ (by omega)
  have r01₁ : c₁.nreg 6001 = RPb := by rw [k₁ _ (by omega), r01]
  have r02₁ : c₁.nreg 6002 = IXb := by rw [k₁ _ (by omega), r02]
  have r03₁ : c₁.nreg 6003 = PDb := by rw [k₁ _ (by omega), r03]
  -- the keys
  obtain ⟨c₂, t₂, e₂, ht₂, KA, m₂, k₂, rr₂, rm₂, o₂⟩ := pfKA_exec (P := P) c₁ hw₁ (n' := n')
    hR₁ r02₁ r03₁ hpd₁ hix₁ vk₁ hPD hIX hn' hnp ⟨by omega, by omega, l4⟩
  have hw₂ := e₂.wb_right
  have g2 : ∀ x, ((6000 ≤ x ∧ x ≤ 6018) ∨ x = 6521) → c₂.nreg x = c₁.nreg x := fun x hx =>
    k₂ x (by unfold vscr; omega) (by omega) (by omega)
  obtain ⟨c₃, t₃, e₃, ht₃, KB, m₃, k₃, rr₃, rm₃, o₃⟩ := pfKB_exec (P := P) c₂ hw₂ (n' := n')
    (hR₁.congr g2) (by rw [g2 _ (by omega), r02₁]) (by rw [g2 _ (by omega), r03₁])
    (fun j hj => by rw [m₂ _ (by omega), hpd₁ j hj])
    (fun q hq => by rw [m₂ _ (by omega), hix₁ q hq]) hPD hnp hn hn' ⟨by omega, by omega, l4⟩
  have hw₃ := e₃.wb_right
  have g3 : ∀ x, ((6000 ≤ x ∧ x ≤ 6018) ∨ x = 6521) → c₃.nreg x = c₁.nreg x := fun x hx => by
    rw [k₃ x (by unfold vscr; omega) (by omega) (by omega), g2 x hx]
  have hm3 : ∀ a, (a < Yb ∨ (Yb ≤ a ∧ a < Yb + 4 * n + 2)) → c₃.nmem a = c₁.nmem a :=
    fun a ha => by rw [m₃ a (by omega), m₂ a (by omega)]
  obtain ⟨c₄, t₄, e₄, ht₄, KC, m₄, k₄, rr₄, rm₄, o₄⟩ := pfKC_exec (P := P) c₃ hw₃ (n' := n')
    (hR₁.congr g3) (by rw [g3 _ (by omega), r01₁]) (by rw [g3 _ (by omega), r02₁])
    (by rw [g3 _ (by omega), r03₁])
    (fun j hj => by rw [hm3 _ (by omega), hpd₁ j hj])
    (fun q hq => by rw [hm3 _ (by omega), hix₁ q hq])
    (fun i hi => by rw [hm3 _ (by omega), hrp₁ i hi]) hPD hnp hIX hn hn'
    ⟨by omega, by omega, by omega, l4⟩
  have hw₄ := e₄.wb_right
  have g4 : ∀ x, ((6000 ≤ x ∧ x ≤ 6018) ∨ x = 6521) → c₄.nreg x = c₁.nreg x := fun x hx => by
    rw [k₄ x (by unfold vscr; omega) (by omega) (by omega), g3 x hx]
  have hm4 : ∀ a, (a < Yb ∨ (Yb ≤ a ∧ a < Yb + 4 * n + 2)) → c₄.nmem a = c₁.nmem a :=
    fun a ha => by rw [m₄ a (by omega), hm3 a ha]
  obtain ⟨c₅, t₅, e₅, ht₅, KD, m₅, k₅, rr₅, rm₅, o₅⟩ := pfKD_exec (P := P) c₄ hw₄ (n' := n')
    (hR₁.congr g4) (by rw [g4 _ (by omega), r01₁]) (by rw [g4 _ (by omega), r02₁])
    (by rw [g4 _ (by omega), r03₁])
    (fun j hj => by rw [hm4 _ (by omega), hpd₁ j hj])
    (fun q hq => by rw [hm4 _ (by omega), hix₁ q hq])
    (fun i hi => by rw [hm4 _ (by omega), hrp₁ i hi])
    (fun i hi => by rw [hm4 _ (by omega), vk₁ i hi]) hPD hnp hIX hRP hn hn'
    ⟨by omega, by omega, by omega, l4⟩
  have hw₅ := e₅.wb_right
  have g5 : ∀ x, ((6000 ≤ x ∧ x ≤ 6018) ∨ x = 6521) → c₅.nreg x = c₁.nreg x := fun x hx => by
    rw [k₅ x (by unfold vscr; omega) (by omega) (by omega), g4 x hx]
  have hR₅ : PfRegs c₅ n np Yb := hR₁.congr g5
  -- the memory after the keys
  have hk5 : ∀ a, (a < Yb + 4 * n + 2 ∨ Yb + 8 * n + 2 ≤ a) → c₅.nmem a = c₁.nmem a :=
    fun a ha => by rw [m₅ a (by omega), m₄ a (by omega), m₃ a (by omega), m₂ a (by omega)]
  have hKA5 : ∀ j < np, c₅.nmem (Yb + 4 * n + 2 + j) = pfKA (fun j => c.nmem (PDb + j))
      (fun q => c.nmem (IXb + q)) (vkF (fun j => c.nmem (VPb + j))) n j := fun j hj => by
    rw [m₅ _ (by omega), m₄ _ (by omega), m₃ _ (by omega)]; exact KA j hj
  have hKB5 : ∀ j < np - 1, c₅.nmem (Yb + 5 * n + 2 + j) = pfKB (fun j => c.nmem (PDb + j))
      (fun q => c.nmem (IXb + q)) n j := fun j hj => by
    rw [m₅ _ (by omega), m₄ _ (by omega)]; exact KB j hj
  have hKC5 : ∀ j < np - 1, c₅.nmem (Yb + 6 * n + 2 + j) = pfKC (fun j => c.nmem (PDb + j))
      (fun q => c.nmem (IXb + q)) (fun i => c.nmem (RPb + i)) n j := fun j hj => by
    rw [m₅ _ (by omega)]; exact KC j hj
  -- the bounds of the keys
  have bA : ∀ j < np, pfKA (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q))
      (vkF (fun j => c.nmem (VPb + j))) n j ≤ n := fun j hj => by
    have := hPD j hj
    exact pf_key_le (dself_le _) (hvkn _ (hIX (c.nmem (PDb + j) - 1) (by omega)))
  have bB : ∀ j < np - 1, pfKB (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q)) n j ≤ n :=
    fun j hj => by
      have := hPD j (by omega)
      exact pf_key_le (dself_le _) (hIX (c.nmem (PDb + j) - 1) (by omega))
  have bC : ∀ j < np - 1, pfKC (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q))
      (fun i => c.nmem (RPb + i)) n j ≤ n := fun j hj => by
    have := hPD j (by omega)
    exact pf_key_le (dself_le _) (hRP _ (hIX (c.nmem (PDb + j) - 1) (by omega)))
  have bD : ∀ j < np - 1, pfKD (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q))
      (fun i => c.nmem (RPb + i)) (vkF (fun j => c.nmem (VPb + j))) n j ≤ n := fun j hj => by
    have := hPD j (by omega)
    exact pf_key_le (dself_le _) (hvkn _ (hRP _ (hIX (c.nmem (PDb + j) - 1) (by omega))))
  -- the marks
  obtain ⟨c₆, t₆, e₆, ht₆, T6, mm₆, n6, rr₆, rm₆, o₆⟩ := pfMark_exec (P := P) c₅ hw₅
    (a := 6017) (b := 6008) (d := 6005) (n := n) (by omega) (by omega) (by omega) hR₅.r17
    hR₅.r08 hR₅.r05 hKA5 bA (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have hw₆ := e₆.wb_right
  have hR₆ : PfRegs c₆ n np Yb := hR₅.congr fun x hx => n6 x (by omega)
  obtain ⟨c₇, t₇, e₇, ht₇, T7, mm₇, n7, rr₇, rm₇, o₇⟩ := pfMark_exec (P := P) c₆ hw₆
    (a := 6018) (b := 6014) (d := 6005) (n := n) (key := pfKD (fun j => c.nmem (PDb + j))
      (fun q => c.nmem (IXb + q)) (fun i => c.nmem (RPb + i)) (vkF (fun j => c.nmem (VPb + j))) n)
    (by omega) (by omega) (by omega) hR₆.r18 hR₆.r14 hR₆.r05
    (fun j hj => by rw [mm₆ _ (by omega)]; exact KD j hj) bD
    (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have hw₇ := e₇.wb_right
  have hR₇ : PfRegs c₇ n np Yb := hR₆.congr fun x hx => n7 x (by omega)
  obtain ⟨c₈, t₈, e₈, ht₈, T8, mm₈, n8, rr₈, rm₈, o₈⟩ := pfMark_exec (P := P) c₇ hw₇
    (a := 6018) (b := 6009) (d := 6006) (n := n) (by omega) (by omega) (by omega) hR₇.r18
    hR₇.r09 hR₇.r06 (fun j hj => by rw [mm₇ _ (by omega), mm₆ _ (by omega)]; exact hKB5 j hj) bB
    (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have hw₈ := e₈.wb_right
  have hR₈ : PfRegs c₈ n np Yb := hR₇.congr fun x hx => n8 x (by omega)
  obtain ⟨c₉, t₉, e₉, ht₉, T9, mm₉, n9, rr₉, rm₉, o₉⟩ := pfMark_exec (P := P) c₈ hw₈
    (a := 6018) (b := 6013) (d := 6006) (n := n) (by omega) (by omega) (by omega) hR₈.r18
    hR₈.r13 hR₈.r06
    (fun j hj => by rw [mm₈ _ (by omega), mm₇ _ (by omega), mm₆ _ (by omega)]; exact hKC5 j hj) bC
    (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have hw₉ := e₉.wb_right
  have hR₉ : PfRegs c₉ n np Yb := hR₈.congr fun x hx => n9 x (by omega)
  -- the vertex flags
  have hvk₉ : ∀ i < n, c₉.nmem (Yb + i) = vkF (fun j => c.nmem (VPb + j)) i := fun i hi => by
    rw [mm₉ _ (by omega), mm₈ _ (by omega), mm₇ _ (by omega), mm₆ _ (by omega),
      hk5 _ (by omega)]
    exact vk₁ i hi
  obtain ⟨c₁₀, t₁₀, e₁₀, ht₁₀, VF, mm₁₀, n10, rr₁₀, rm₁₀, o₁₀⟩ := pfVF_exec (P := P) c₉ hw₉ hR₉
    hvk₉ hvkn l4
  refine ⟨c₁₀, t₁ + ((t₂ + (t₃ + (t₄ + t₅))) + ((t₆ + (t₇ + (t₈ + t₉))) + t₁₀)),
    .seq e₁ (.seq (.seq e₂ (.seq e₃ (.seq e₄ e₅))) (.seq (.seq e₆ (.seq e₇ (.seq e₈ e₉))) e₁₀)),
    ?_, fun i hi => ?_, fun i hi => ?_, fun a ha => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · have : np - 1 ≤ np := Nat.sub_le np 1
    omega
  · have hz : c₁.nmem (Yb + 2 * n + 1 + i) = 0 := by
      have := z₁ (n + 1 + i) (by omega)
      rwa [show Yb + n + (n + 1 + i) = Yb + 2 * n + 1 + i by omega] at this
    rw [mm₁₀ _ (by omega), T9 i (by omega), T8 i (by omega), mm₇ _ (by omega), mm₆ _ (by omega),
      hk5 _ (by omega), hz]
    exact pf_if_or2
  · have hv := hvkn i hi
    rw [VF i hi, mm₉ _ (by omega), mm₈ _ (by omega), T7 _ (by omega), T6 _ (by omega),
      hk5 _ (by omega), show Yb + n + vkF (fun j => c.nmem (VPb + j)) i =
        Yb + n + vkF (fun j => c.nmem (VPb + j)) i from rfl, z₁ _ (by omega)]
    exact pf_if_or
  · rw [mm₁₀ a (by omega), mm₉ a (by omega), mm₈ a (by omega), mm₇ a (by omega),
      mm₆ a (by omega), hk5 a (by omega), m₁ a (by omega)]
  · unfold pfKeepR at hx
    rw [n10 x (by unfold vscr; omega) (by omega) (by omega), n9 x (by omega), n8 x (by omega),
      n7 x (by omega), n6 x (by omega), k₅ x (by unfold vscr; omega) (by omega) (by omega),
      k₄ x (by unfold vscr; omega) (by omega) (by omega),
      k₃ x (by unfold vscr; omega) (by omega) (by omega),
      k₂ x (by unfold vscr; omega) (by omega) (by omega), k₁ x (by omega)]
  · rw [rr₁₀, rr₉, rr₈, rr₇, rr₆, rr₅, rr₄, rr₃, rr₂, rr₁]
  · rw [rm₁₀, rm₉, rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁]
  · rw [o₁₀, o₉, o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]

end Exec

/-- **The flags of `lgPF` are those of the path**: under `PfIn` (the path on the record by the
indices `IX[PD[j] - 1]`) and the shape of `PD` (`PathPD`), the dart flag of `i` is
`bf (g i ∈ ρ.darts)` and the vertex flag `bf (tail (g i) ∈ ρ.mverts)`. -/
theorem lgPF_flags {D : Type*} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] {M : CombMap D V F} {g : ℕ → D} {n np : ℕ}
    {rp vk pd ix : ℕ → ℕ} {ρ : HPath M} (h : PfIn M g n rp vk (pfI pd ix) ρ)
    (hs : PdShape pd np ρ.k) (hk' : ρ.k < np) {i : ℕ} (hi : i < n) (hvk : vk i < n) :
    (if ∃ j < np - 1, pfKB pd ix n j = i ∨ pfKC pd ix rp n j = i then 1 else 0) =
        bf (g i ∈ ρ.darts.toFinset) ∧
      (if (∃ j < np, pfKA pd ix vk n j = vk i) ∨ (∃ j < np - 1, pfKD pd ix rp vk n j = vk i)
        then 1 else 0) = bf (M.tail (g i) ∈ ρ.mverts) := by
  unfold bf
  constructor
  · exact if_congr ((pf_darts_keys h hs hk' hi).trans List.mem_toFinset.symm) rfl rfl
  · exact if_congr (pf_mverts_keys h hs hk' hi hvk) rfl rfl

/-- **The hypotheses of `lgPF_flags` from the record and `PathPD`**: `g` injective on `[0, n)`,
the reverses `rp`, tail numbers `vp` sorted (`TailSorted`) with `ν` injective, the core's
enumeration `e' q = g (ix q)` (`q < n'`) and the path's darts `PathPD M e' n' PDb c ρ` give
`PfIn` for the keys `vkF vp`, the shape of `PD`, `ρ.k < n'` and `PD[j] ≤ n'`. -/
theorem pfIn_of {D : Type*} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] {M : CombMap D V F} {g e' : ℕ → D}
    {ν : V → ℕ} {n n' PDb : ℕ} {rp vp ix : ℕ → ℕ} {c : Config} {ρ : HPath M}
    (hinj : ∀ i < n, ∀ i' < n, g i = g i' → i = i')
    (hrp : ∀ i < n, rp i < n ∧ g (rp i) = M.rev (g i))
    (hvp : ∀ i < n, vp i = ν (M.tail (g i))) (hmono : ∀ i j, i < j → j < n → vp i ≤ vp j)
    (hν : Function.Injective ν) (hix : ∀ q < n', ix q < n ∧ e' q = g (ix q))
    (hn'n : n' ≤ n) (hP : PathPD M e' n' PDb c ρ) :
    PfIn M g n rp (vkF vp) (pfI (fun j => c.nmem (PDb + j)) ix) ρ ∧
      PdShape (fun j => c.nmem (PDb + j)) n' ρ.k ∧ ρ.k < n' ∧ (∀ j < n', c.nmem (PDb + j) ≤ n') := by
  obtain ⟨hk, hd, hz⟩ := hP
  refine ⟨⟨hinj, hrp, fun i hi i' hi' => ?_, ?_, fun j hj => ?_⟩, ⟨fun j hj => ?_, hz⟩, hk,
    fun j hj => ?_⟩
  · rw [vkF_eq_iff hmono hi hi', hvp i hi, hvp i' hi']
    exact hν.eq_iff
  · omega
  · obtain ⟨i, hi, h1, h2, h3⟩ := hd j hj
    have e1 : pfI (fun j => c.nmem (PDb + j)) ix j = ix i := by
      show ix (c.nmem (PDb + j) - 1) = ix i
      rw [h1, Nat.add_sub_cancel]
    obtain ⟨h4, h5⟩ := hix i hi
    exact ⟨by rw [e1]; exact h4, by rw [e1, ← h5, h2], h3⟩
  · obtain ⟨i, hi, h1, -, -⟩ := hd j hj
    show c.nmem (PDb + j) ≠ 0
    omega
  · by_cases h : j ≤ ρ.k
    · obtain ⟨i, hi, h1, -, -⟩ := hd j h
      omega
    · have := hz j hj (by omega)
      omega

end MfDrv

end BKMNW

end PlanarFlow
