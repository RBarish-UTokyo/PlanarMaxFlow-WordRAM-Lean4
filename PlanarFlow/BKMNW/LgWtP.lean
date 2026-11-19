module

public import PlanarFlow.BKMNW.LgWtS

/-!
# The large-piece separator, stage 4: the scans of the weights program

The loops of the weights program `lgWt` (`LgWtE.lean`), each with its exec lemma. Every value is
computed branch-free on natural words (`x / x` is the flag `x ≠ 0`).

* `vkM` (one step of the run keys), `vkM_eq`; `vkBody`, `vkInit`, **`vkLoop`** (registers
  `5890 … 5896`; `VK[i] = vkF VP i`), **`vkLoop_exec`** (`15 n + 5` steps);
* `ckM = ckv` (`ckM_eq`), `vbCK`, **`ckScan`** (`CK[i] = ckv kk HP[i] VK[i]`);
* `vbAK`, **`akScan`** (`AK[i] = CK[akI RP VP i]`);
* `sfM` (`sfM_eq`: the flag of `selP`), `vbSF`, **`sfScan`**;
* `vbAV`, **`avScan`** (`AV[j] = SF[j] · T2[AK[j]]`);
* `vbEX`, **`exScan`** (`EX[j] = EXK[j] + EXM[j + 1]`);
* `zfill` (a zero fill), **`zfill_exec`**.

Registers: `5800 = n`, `5801 = RPb`, `5802 = HPb`, `5803 = VPb`, `5806 = 1`, `5807 = 2`,
`5811 = n'`, `5870 = kk`, `5872 = CF2b`, `5873 = VKb`, `5874 = CKb`, `5875 = AKb`, `5876 = SFb`,
`5877 = AVb`, `5879 = T2b`, `5882 = EXKb`, `5883 = EXMb`, `5889 = EXb`; the map loops' `6520 … 6529`.
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

/-! ### Machine forms of the values -/

/-- One step of the run keys: the new key from the index `i`, the previous value `p`, the current
key `u` and the value `v`. -/
def vkM (i p u v : ℕ) : ℕ := u + ((v - p) + (p - v)) / ((v - p) + (p - v)) * (i - u)

lemma vkM_eq {i p u v : ℕ} (hu : u ≤ i) : vkM i p u v = if v = p then u else i := by
  unfold vkM
  split_ifs with h
  · subst h; simp
  · have : 0 < (v - p) + (p - v) := by omega
    rw [Nat.div_self this]; omega

/-- The class key as computed: `h + (1 - h / h) · (kk + 1 + vk)`. -/
def ckM (kk h vk : ℕ) : ℕ := h + (1 - h / h) * (kk + 1 + vk)

lemma ckM_eq (kk h vk : ℕ) : ckM kk h vk = ckv kk h vk := by
  unfold ckM ckv
  split_ifs with h0
  · rw [Nat.div_self h0]; simp
  · have : h = 0 := by omega
    subst this; simp

/-- The anchor index as computed: `(1 - b) · i + b · r`, `b = v % 2`. -/
def akM (i v r : ℕ) : ℕ := (1 - v % 2) * i + v % 2 * r

lemma akM_eq (i v r : ℕ) : akM i v r = if v % 2 = 1 then r else i := by
  unfold akM
  have := Nat.mod_lt v (show 0 < 2 by norm_num)
  split_ifs with h
  · rw [h]; simp
  · have h0 : v % 2 = 0 := by omega
    rw [h0]; simp

/-- The flag of a representative as computed, from `cf`, the labels `hp`, `hpr` of the tail and
head, the table entry `tbv` of the tail's key, the index `i` and the reverse index `rp`. -/
def sfM (cf hp hpr tbv i rp : ℕ) : ℕ :=
  (1 - cf / cf) *
      (1 - (1 - ((hp - hpr) + (hpr - hp)) / ((hp - hpr) + (hpr - hp))) * (hp / hp) *
        (1 - tbv / tbv)) *
    ((rp - i) / (rp - i))

lemma div_self_flag (x : ℕ) : x / x = if x = 0 then 0 else 1 := by
  split_ifs with h
  · subst h; simp
  · exact Nat.div_self (by omega)

lemma dself_le (x : ℕ) : x / x ≤ 1 := by
  rw [div_self_flag]; split_ifs <;> omega

lemma sfM_eq (cf hp hpr tbv i rp : ℕ) :
    sfM cf hp hpr tbv i rp = bf (cf = 0 ∧ ¬ (0 < hp ∧ hp = hpr ∧ tbv = 0) ∧ i < rp) := by
  unfold sfM bf
  have k1 : ((hp - hpr) + (hpr - hp) = 0) ↔ hp = hpr := by omega
  have k2 : (rp - i = 0) ↔ ¬ i < rp := by omega
  have k3 : (hp = 0) ↔ ¬ 0 < hp := by omega
  rw [div_self_flag cf, div_self_flag ((hp - hpr) + (hpr - hp)), div_self_flag hp,
    div_self_flag tbv, div_self_flag (rp - i)]
  simp only [k1, k2, k3]
  by_cases a : cf = 0 <;> by_cases b : 0 < hp <;> by_cases c : hp = hpr <;>
    by_cases d : tbv = 0 <;> by_cases e : i < rp <;> simp [a, b, c, d, e] <;>
    (split_ifs <;> omega)

lemma sfM_le (cf hp hpr tbv i rp : ℕ) : sfM cf hp hpr tbv i rp ≤ 1 := by
  rw [sfM_eq]; unfold bf; split_ifs <;> omega

/-! ### The programs -/

/-- The body of the run keys: `v := VP[i]`, `cur := vkM i prev cur v`, `VK[i] := cur`,
`prev := v`, `i := i + 1`. -/
def vkBody : Stmt :=
  block [.addN 5893 5803 5890, .loadN 5894 5893, .subN 5895 5894 5891, .subN 5896 5891 5894,
    .addN 5895 5895 5896, .divN 5895 5895 5895, .subN 5896 5890 5892, .mulN 5896 5895 5896,
    .addN 5892 5892 5896, .addN 5893 5873 5890, .storeN 5893 5892, .copyN 5891 5894,
    .addN 5890 5890 5806]

/-- The start of the run keys: `i := 0`, `prev := VP[0]`, `cur := 0`. -/
def vkInit : Stmt := block [.constN 5890 0, .loadN 5891 5803, .constN 5892 0]

/-- **The run keys** `VK[i] = vkF VP i` (`i < n`). -/
def vkLoop : Stmt := .seq vkInit (.whileLtN 5890 5800 vkBody)

/-- The value block of the class keys: `ckM kk HP[i] VK[i]`. -/
def vbCK : Stmt :=
  block [.addN 6524 5802 6520, .loadN 6524 6524, .addN 6525 5873 6520, .loadN 6525 6525,
    .divN 6526 6524 6524, .subN 6527 5806 6526, .addN 6528 5870 5806, .addN 6528 6528 6525,
    .mulN 6527 6527 6528, .addN 6523 6524 6527]

/-- **The class keys** of the tails. -/
def ckScan : Stmt := mapRunS vbCK 5800 5874

/-- The value block of the anchor keys: `CK[akM i VP[i] RP[i]]`. -/
def vbAK : Stmt :=
  block [.addN 6524 5803 6520, .loadN 6524 6524, .modN 6524 6524 5807, .addN 6525 5801 6520,
    .loadN 6525 6525, .subN 6526 5806 6524, .mulN 6526 6526 6520, .mulN 6527 6524 6525,
    .addN 6526 6526 6527, .addN 6527 5874 6526, .loadN 6523 6527]

/-- **The anchor keys.** -/
def akScan : Stmt := mapRunS vbAK 5800 5875

/-- The value block of the representatives' flags:
`sfM CF2[i] HP[i] HP[RP[i]] T2[CK[i]] i RP[i]`. -/
def vbSF : Stmt :=
  block [.addN 6524 5872 6520, .loadN 6524 6524, .addN 6525 5802 6520, .loadN 6525 6525,
    .addN 6526 5801 6520, .loadN 6526 6526, .addN 6527 5802 6526, .loadN 6527 6527,
    .subN 6528 6525 6527, .subN 6529 6527 6525, .addN 6528 6528 6529, .divN 6528 6528 6528,
    .subN 6528 5806 6528, .divN 6529 6525 6525, .mulN 6528 6528 6529,
    .addN 6525 5874 6520, .loadN 6525 6525, .addN 6525 5879 6525, .loadN 6525 6525,
    .divN 6525 6525 6525, .subN 6525 5806 6525, .mulN 6528 6528 6525,
    .subN 6526 6526 6520, .divN 6526 6526 6526,
    .divN 6524 6524 6524, .subN 6524 5806 6524, .subN 6528 5806 6528, .mulN 6524 6524 6528,
    .mulN 6523 6524 6526]

/-- **The flags of the representatives of the attached pairs.** -/
def sfScan : Stmt := mapRunS vbSF 5800 5876

/-- The value block of the anchors: `SF[i] · T2[AK[i]]`. -/
def vbAV : Stmt :=
  block [.addN 6524 5876 6520, .loadN 6524 6524, .addN 6525 5875 6520, .loadN 6525 6525,
    .addN 6525 5879 6525, .loadN 6525 6525, .mulN 6523 6524 6525]

/-- **The anchors of the representatives** (`1 +` a core index, or `0`). -/
def avScan : Stmt := mapRunS vbAV 5800 5877

/-- The value block of the weights: `EXK[j] + EXM[j + 1]`. -/
def vbEX : Stmt :=
  block [.addN 6524 5882 6520, .loadN 6524 6524, .addN 6525 6520 5806, .addN 6525 5883 6525,
    .loadN 6525 6525, .addN 6523 6524 6525]

/-- **The weights** on the core's enumeration. -/
def exScan : Stmt := mapRunS vbEX 5811 5889

/-- **A zero fill** of `r[bnd]` words from `r[ob]`. -/
def zfill (bnd ob : ℕ) : Stmt := mapRunS (block [.constN 6523 0]) bnd ob

section Exec

variable {P : Input} {W : ℕ}

theorem zfill_exec (c : Config) (hc : WordsBounded W c) {bnd ob m Ob : ℕ}
    (r1 : c.nreg bnd = m) (r2 : c.nreg 6521 = 1) (r3 : c.nreg ob = Ob)
    (w1 : Ob + m ≤ W) (w2 : m + 1 ≤ W) (s2 : ¬ vscr bnd) (s4 : ¬ vscr ob) (h6 : 6522 ≠ bnd)
    (h7 : 6520 ≠ bnd) (h8 : ob ≠ 6520) (h3 : 6522 ≠ ob) :
    ∃ c' t, Exec P W (zfill bnd ob) c c' t ∧ t ≤ 6 * m + 3 ∧
      (∀ j < m, c'.nmem (Ob + j) = 0) ∧
      (∀ a, ¬ (Ob ≤ a ∧ a < Ob + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, f1, m1, n1, rr1, rm1, o1⟩ := mapRun_exec (P := P) c hc
    (vb := block [.constN 6523 0]) (bnd := bnd) (ob := ob) (m := m) (Ob := Ob) (B := 1)
    (fun _ => 0) r1 r2 r3 w1 w2 s2 s4 h6 h7 h8 h3
    (fun i hi c' hw h20 hr hm => by
      obtain ⟨c'', k', e', hk'', v, nn, mm, rr, rm, oo⟩ := cst_exec (P := P) (r := 6523) (v := 0)
        c' hw (Nat.zero_le _)
      exact ⟨c'', k', e', by omega, v, fun x hx => nn x (by unfold vscr at hx; omega), mm, rr,
        rm, oo⟩)
  exact ⟨c₁, t₁, e₁, by omega, f1, m1, n1, rr1, rm1, o1⟩

theorem vkBody_exec (c : Config) (hc : WordsBounded W c) {VPb VKb i p u v : ℕ}
    (r03 : c.nreg 5803 = VPb) (r73 : c.nreg 5873 = VKb) (r06 : c.nreg 5806 = 1)
    (r90 : c.nreg 5890 = i) (r91 : c.nreg 5891 = p) (r92 : c.nreg 5892 = u)
    (hv : c.nmem (VPb + i) = v) (hu : u ≤ i) (w1 : VPb + i ≤ W) (w2 : VKb + i ≤ W)
    (w3 : i + 1 ≤ W) :
    ∃ c' t, Exec P W vkBody c c' t ∧ t = 13 ∧ c'.nreg 5890 = i + 1 ∧ c'.nreg 5891 = v ∧
      c'.nreg 5892 = vkM i p u v ∧ c'.nmem = upd c.nmem (VKb + i) (vkM i p u v) ∧
      (∀ x, (x < 5890 ∨ 5896 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b1 : v ≤ W := hv ▸ hc.2 _
  have b2 : p ≤ W := r91 ▸ hc.1 _
  have hm : ((v - p) + (p - v)) / ((v - p) + (p - v)) * (i - u) ≤ i - u := cs_mul_le (dself_le _)
  have hd : ((v - p) + (p - v)) / ((v - p) + (p - v)) ≤ 1 := dself_le _
  have hk : vkM i p u v ≤ i := by unfold vkM; omega
  unfold vkBody
  exec_block
  all_goals try (config_simp; simp only [r03, r73, r06, r90, r91, r92, hv]; omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r03, r73, r06,
    r90, r91, r92, hv]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r03, r73, r06, r90, r91, r92, hv])
    try rfl
    try omega

theorem vkInit_exec (c : Config) (hc : WordsBounded W c) {VPb : ℕ} (r03 : c.nreg 5803 = VPb) :
    ∃ c' t, Exec P W vkInit c c' t ∧ t = 3 ∧ c'.nreg 5890 = 0 ∧ c'.nreg 5891 = c.nmem VPb ∧
      c'.nreg 5892 = 0 ∧ (∀ x, (x < 5890 ∨ 5896 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b1 : c.nmem VPb ≤ W := hc.2 _
  unfold vkInit
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp only [r03]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r03])

/-- **The run keys on the machine**: `VK[i] = vkF VP i` for `i < n`, within `15 n + 5` steps;
memory outside `[VKb, VKb + n)` and registers outside `5890 … 5896` kept. -/
theorem vkLoop_exec (c : Config) (hc : WordsBounded W c) {n VPb VKb : ℕ}
    (r00 : c.nreg 5800 = n) (r03 : c.nreg 5803 = VPb) (r73 : c.nreg 5873 = VKb)
    (r06 : c.nreg 5806 = 1) (w1 : VPb + n ≤ W) (w2 : VKb + n ≤ W) (w3 : n + 1 ≤ W)
    (hVP : VPb ≤ W) (hd : ∀ i < n, ¬ (VKb ≤ VPb + i ∧ VPb + i < VKb + n)) :
    ∃ c' t, Exec P W vkLoop c c' t ∧ t ≤ 15 * n + 5 ∧
      (∀ i < n, c'.nmem (VKb + i) = vkF (fun j => c.nmem (VPb + j)) i) ∧
      (∀ a, ¬ (VKb ≤ a ∧ a < VKb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5890 ∨ 5896 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, gn₁, gm₁, gr₁, grm₁, go₁⟩ := vkInit_exec (P := P) c hc r03
  have hw₁ := e₁.wb_right
  set m₀ := c.nmem with hm₀
  set vp : ℕ → ℕ := fun j => m₀ (VPb + j) with hvp
  have hv0 : c₁.nreg 5891 = vp (0 - 1) := by rw [g1]; simp [hvp]
  let J : ℕ → Config → Prop := fun i c' =>
    c'.nreg 5891 = vp (i - 1) ∧ c'.nreg 5892 = vkF vp (i - 1) ∧
    (∀ x, (x < 5890 ∨ 5896 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (VKb + j) = vkF vp j) ∧
    (∀ a, ¬ (VKb ≤ a ∧ a < VKb + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h90, j1, j2, j3, j4, j5, j6, j7, j8⟩ := tgRange (P := P)
    (a := 5890) (b := 5800) (body := vkBody) J (B := 13) c₁ hw₁ g0
    (by rw [gn₁ _ (by omega), r00]) (Nat.zero_le n)
    ⟨hv0, by rw [g2]; simp [vkF], fun _ _ => rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h90 h00 ⟨j1, j2, j3, j4, j5, j6, j7, j8⟩ => by
      have f : ∀ x, (x < 5890 ∨ 5896 < x) → c'.nreg x = c₁.nreg x := j3
      have e1 : c'.nmem (VPb + i) = vp i := j5 _ (fun h => hd i hhi ⟨h.1, by omega⟩)
      have hu : vkF vp (i - 1) ≤ i := (vkF_le vp (i - 1)).trans (by omega)
      obtain ⟨c'', t, ex, ht, h90', h91', h92', hm', hn', hr', hrm', ho'⟩ := vkBody_exec (P := P)
        c' hw (by rw [f _ (by omega), gn₁ _ (by omega), r03])
        (by rw [f _ (by omega), gn₁ _ (by omega), r73])
        (by rw [f _ (by omega), gn₁ _ (by omega), r06]) h90 j1 j2 e1 hu (by omega) (by omega)
        (by omega)
      have hstep : vkM i (vp (i - 1)) (vkF vp (i - 1)) (vp i) = vkF vp i := by
        rw [vkM_eq hu, vkF_step vp i]
      rw [hstep] at h92' hm'
      refine ⟨c'', t, ex, ht.le, h90', by rw [hn' _ (by omega)]; exact h00,
        by rw [h91']; simp, by rw [h92']; simp,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j6], by rw [hrm', j7], by rw [ho', j8]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j4 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (by omega)]
        exact j5 a (by omega))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j4, fun a ha => j5 a (by omega), fun x hx => ?_,
    by rw [j6, gr₁], by rw [j7, grm₁], by rw [j8, go₁]⟩
  rw [j3 x hx, gn₁ x hx]

/-! ### The value blocks -/

/-- A frame of the value blocks: only the scratch `vscr` written. -/
theorem vb_frame_aux {x : ℕ} (hx : ¬ vscr x) : x < 6523 ∨ 6529 < x := by unfold vscr at hx; omega

theorem vbCK_exec (c : Config) (hc : WordsBounded W c) {i HPb VKb kk h vk : ℕ}
    (r20 : c.nreg 6520 = i) (r02 : c.nreg 5802 = HPb) (r73 : c.nreg 5873 = VKb)
    (r70 : c.nreg 5870 = kk) (r06 : c.nreg 5806 = 1)
    (hh : c.nmem (HPb + i) = h) (hv : c.nmem (VKb + i) = vk)
    (w1 : HPb + i ≤ W) (w2 : VKb + i ≤ W) (w3 : h + kk + 1 + vk ≤ W) :
    ∃ c' k, Exec P W vbCK c c' k ∧ k ≤ 10 ∧ c'.nreg 6523 = ckM kk h vk ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hm : (1 - h / h) * (kk + 1 + vk) ≤ kk + 1 + vk := cs_mul_le (Nat.sub_le _ _)
  have hd := dself_le h
  unfold vbCK
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r20, r02, r73,
    r70, r06, hh, hv]; omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
    simp (disch := omega) only [upd_other, upd_same, r20, r02, r73, r70, r06, hh, hv]
    rfl
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbAK_exec (c : Config) (hc : WordsBounded W c) {i VPb RPb CKb v r y : ℕ}
    (r20 : c.nreg 6520 = i) (r03 : c.nreg 5803 = VPb) (r01 : c.nreg 5801 = RPb)
    (r74 : c.nreg 5874 = CKb) (r06 : c.nreg 5806 = 1) (r07 : c.nreg 5807 = 2)
    (hv : c.nmem (VPb + i) = v) (hr : c.nmem (RPb + i) = r) (hy : c.nmem (CKb + akM i v r) = y)
    (w1 : VPb + i ≤ W) (w2 : RPb + i ≤ W) (w3 : CKb + akM i v r ≤ W) :
    ∃ c' k, Exec P W vbAK c c' k ∧ k ≤ 11 ∧ c'.nreg 6523 = y ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b0 : i ≤ W := r20 ▸ hc.1 _
  have b1 : r ≤ W := hr ▸ hc.2 _
  have b2 : y ≤ W := hy ▸ hc.2 _
  have hmod : v % 2 ≤ 1 := by have := Nat.mod_lt v (show 0 < 2 by norm_num); omega
  have h1 : (1 - v % 2) * i ≤ i := cs_mul_le (Nat.sub_le _ _)
  have h2 : v % 2 * r ≤ r := cs_mul_le hmod
  have hak : (1 - v % 2) * i + v % 2 * r = akM i v r := rfl
  unfold vbAK
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r20, r03, r01,
    r74, r06, r07, hv, hr, hak, hy]; omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
    simp (disch := omega) only [upd_other, upd_same, r20, r03, r01, r74, r06, r07, hv, hr, hak, hy]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

lemma mul_le_one'' {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := by
  calc a * b ≤ 1 * 1 := Nat.mul_le_mul ha hb
    _ = 1 := rfl

theorem vbSF_exec (c : Config) (hc : WordsBounded W c) {i CFb HPb RPb CKb T2b cf hp r hpr ck tb : ℕ}
    (r20 : c.nreg 6520 = i) (r72 : c.nreg 5872 = CFb) (r02 : c.nreg 5802 = HPb)
    (r01 : c.nreg 5801 = RPb) (r74 : c.nreg 5874 = CKb) (r79 : c.nreg 5879 = T2b)
    (r06 : c.nreg 5806 = 1)
    (h1 : c.nmem (CFb + i) = cf) (h2 : c.nmem (HPb + i) = hp) (h3 : c.nmem (RPb + i) = r)
    (h4 : c.nmem (HPb + r) = hpr) (h5 : c.nmem (CKb + i) = ck) (h6 : c.nmem (T2b + ck) = tb)
    (w1 : CFb + i ≤ W) (w2 : HPb + i ≤ W) (w3 : RPb + i ≤ W) (w4 : HPb + r ≤ W)
    (w5 : CKb + i ≤ W) (w6 : T2b + ck ≤ W) :
    ∃ c' k, Exec P W vbSF c c' k ∧ k ≤ 29 ∧ c'.nreg 6523 = sfM cf hp hpr tb i r ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b0 : i ≤ W := r20 ▸ hc.1 _
  have b1 : r ≤ W := h3 ▸ hc.2 _
  have b2 : hp ≤ W := h2 ▸ hc.2 _
  have b3 : hpr ≤ W := h4 ▸ hc.2 _
  have b4 : cf ≤ W := h1 ▸ hc.2 _
  have b5 : tb ≤ W := h6 ▸ hc.2 _
  have b6 : ck ≤ W := h5 ▸ hc.2 _
  have b06 : 1 ≤ W := r06 ▸ hc.1 _
  have f1 := dself_le ((hp - hpr) + (hpr - hp))
  have f2 := dself_le hp
  have f3 : (1 - ((hp - hpr) + (hpr - hp)) / ((hp - hpr) + (hpr - hp))) * (hp / hp) ≤ 1 :=
    mul_le_one'' (Nat.sub_le _ _) f2
  have f5 := dself_le tb
  have f4 : (1 - ((hp - hpr) + (hpr - hp)) / ((hp - hpr) + (hpr - hp))) * (hp / hp) *
      (1 - tb / tb) ≤ 1 := mul_le_one'' f3 (Nat.sub_le _ _)
  have f6 := dself_le (r - i)
  have f7 := dself_le cf
  have f8 : (1 - cf / cf) * (1 - (1 - ((hp - hpr) + (hpr - hp)) / ((hp - hpr) + (hpr - hp))) *
      (hp / hp) * (1 - tb / tb)) ≤ 1 := mul_le_one'' (Nat.sub_le _ _) (Nat.sub_le _ _)
  have f9 := sfM_le cf hp hpr tb i r
  have hsf : (1 - cf / cf) * (1 - (1 - ((hp - hpr) + (hpr - hp)) / ((hp - hpr) + (hpr - hp))) *
      (hp / hp) * (1 - tb / tb)) * ((r - i) / (r - i)) = sfM cf hp hpr tb i r := rfl
  unfold vbSF
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r20, r72, r02,
    r01, r74, r79, r06, h1, h2, h3, h4, h5, h6]; omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r20, r72, r02,
    r01, r74, r79, r06, h1, h2, h3, h4, h5, h6, hsf]; omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
    simp (disch := omega) only [upd_other, upd_same, r20, r72, r02, r01, r74, r79, r06, h1, h2,
      h3, h4, h5, h6]
    rfl
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbAV_exec (c : Config) (hc : WordsBounded W c) {i SFb AKb T2b s k t : ℕ}
    (r20 : c.nreg 6520 = i) (r76 : c.nreg 5876 = SFb) (r75 : c.nreg 5875 = AKb)
    (r79 : c.nreg 5879 = T2b) (h1 : c.nmem (SFb + i) = s) (h2 : c.nmem (AKb + i) = k)
    (h3 : c.nmem (T2b + k) = t) (hs : s ≤ 1) (w1 : SFb + i ≤ W) (w2 : AKb + i ≤ W)
    (w3 : T2b + k ≤ W) :
    ∃ c' k', Exec P W vbAV c c' k' ∧ k' ≤ 7 ∧ c'.nreg 6523 = s * t ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b5 : t ≤ W := h3 ▸ hc.2 _
  have hm : s * t ≤ t := cs_mul_le hs
  unfold vbAV
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r20, r76, r75,
    r79, h1, h2, h3]; omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
    simp (disch := omega) only [upd_other, upd_same, r20, r76, r75, r79, h1, h2, h3]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbEX_exec (c : Config) (hc : WordsBounded W c) {j EXKb EXMb a b : ℕ}
    (r20 : c.nreg 6520 = j) (r82 : c.nreg 5882 = EXKb) (r83 : c.nreg 5883 = EXMb)
    (r06 : c.nreg 5806 = 1) (h1 : c.nmem (EXKb + j) = a) (h2 : c.nmem (EXMb + (j + 1)) = b)
    (w1 : EXKb + j ≤ W) (w2 : EXMb + (j + 1) ≤ W) (w3 : a + b ≤ W) :
    ∃ c' k, Exec P W vbEX c c' k ∧ k ≤ 6 ∧ c'.nreg 6523 = a + b ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold vbEX
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r20, r82, r83,
    r06, h1, h2]; omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
    simp (disch := omega) only [upd_other, upd_same, r20, r82, r83, r06, h1, h2]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

/-! ### The scans -/

lemma vreg_ok {c c₁ : Config} {x : ℕ}
    (hr : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₁.nreg x = c.nreg x) (h : x < 6520 ∨ 6529 < x) :
    c₁.nreg x = c.nreg x := hr x (by unfold vscr; omega) (by omega) (by omega)

theorem ckScan_exec (c : Config) (hc : WordsBounded W c) {n HPb VKb CKb kk : ℕ}
    (r00 : c.nreg 5800 = n) (r02 : c.nreg 5802 = HPb) (r73 : c.nreg 5873 = VKb)
    (r74 : c.nreg 5874 = CKb) (r70 : c.nreg 5870 = kk) (r06 : c.nreg 5806 = 1)
    (r21 : c.nreg 6521 = 1) (w0 : CKb + n ≤ W) (w0' : n + 1 ≤ W) (w1 : HPb + n ≤ W)
    (w2 : VKb + n ≤ W) (hb : ∀ i < n, c.nmem (HPb + i) + kk + 1 + c.nmem (VKb + i) ≤ W)
    (d1 : ∀ i < n, ¬ (CKb ≤ HPb + i ∧ HPb + i < CKb + n))
    (d2 : ∀ i < n, ¬ (CKb ≤ VKb + i ∧ VKb + i < CKb + n)) :
    ∃ c' t, Exec P W ckScan c c' t ∧ t ≤ 15 * n + 3 ∧
      (∀ i < n, c'.nmem (CKb + i) = ckM kk (c.nmem (HPb + i)) (c.nmem (VKb + i))) ∧
      (∀ a, ¬ (CKb ≤ a ∧ a < CKb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, h1, h2, h3, h4, h5, h6⟩ := mapRun_exec (P := P) c hc (vb := vbCK)
    (bnd := 5800) (ob := 5874) (m := n) (Ob := CKb) (B := 10)
    (fun i => ckM kk (c.nmem (HPb + i)) (c.nmem (VKb + i))) r00 r21 r74 w0 w0'
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c₁ hw h20 hr hm => vbCK_exec (P := P) c₁ hw h20
      (by rw [vreg_ok hr (by omega), r02]) (by rw [vreg_ok hr (by omega), r73])
      (by rw [vreg_ok hr (by omega), r70]) (by rw [vreg_ok hr (by omega), r06])
      (hm _ (d1 i hi)) (hm _ (d2 i hi)) (by omega) (by omega) (hb i hi))
  exact ⟨c', t, ex, by omega, h1, h2, h3, h4, h5, h6⟩

theorem akScan_exec (c : Config) (hc : WordsBounded W c) {n VPb RPb CKb AKb : ℕ}
    (r00 : c.nreg 5800 = n) (r03 : c.nreg 5803 = VPb) (r01 : c.nreg 5801 = RPb)
    (r74 : c.nreg 5874 = CKb) (r75 : c.nreg 5875 = AKb) (r06 : c.nreg 5806 = 1)
    (r07 : c.nreg 5807 = 2) (r21 : c.nreg 6521 = 1) (w0 : AKb + n ≤ W) (w0' : n + 1 ≤ W)
    (w1 : VPb + n ≤ W) (w2 : RPb + n ≤ W)
    (hak : ∀ i < n, akM i (c.nmem (VPb + i)) (c.nmem (RPb + i)) < n) (w3 : CKb + n ≤ W)
    (d1 : ∀ i < n, ¬ (AKb ≤ VPb + i ∧ VPb + i < AKb + n))
    (d2 : ∀ i < n, ¬ (AKb ≤ RPb + i ∧ RPb + i < AKb + n))
    (d3 : ∀ i < n, ¬ (AKb ≤ CKb + i ∧ CKb + i < AKb + n)) :
    ∃ c' t, Exec P W akScan c c' t ∧ t ≤ 16 * n + 3 ∧
      (∀ i < n, c'.nmem (AKb + i) =
        c.nmem (CKb + akM i (c.nmem (VPb + i)) (c.nmem (RPb + i)))) ∧
      (∀ a, ¬ (AKb ≤ a ∧ a < AKb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, h1, h2, h3, h4, h5, h6⟩ := mapRun_exec (P := P) c hc (vb := vbAK)
    (bnd := 5800) (ob := 5875) (m := n) (Ob := AKb) (B := 11)
    (fun i => c.nmem (CKb + akM i (c.nmem (VPb + i)) (c.nmem (RPb + i)))) r00 r21 r75 w0 w0'
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c₁ hw h20 hr hm => by
      have e1 := hm _ (d1 i hi)
      have e2 := hm _ (d2 i hi)
      have ha := hak i hi
      have e3 := hm _ (d3 _ ha)
      exact vbAK_exec (P := P) c₁ hw h20
        (by rw [vreg_ok hr (by omega), r03]) (by rw [vreg_ok hr (by omega), r01])
        (by rw [vreg_ok hr (by omega), r74]) (by rw [vreg_ok hr (by omega), r06])
        (by rw [vreg_ok hr (by omega), r07]) e1 e2 e3 (by omega) (by omega) (by omega))
  exact ⟨c', t, ex, by omega, h1, h2, h3, h4, h5, h6⟩

theorem sfScan_exec (c : Config) (hc : WordsBounded W c) {n CFb HPb RPb CKb T2b SFb nk : ℕ}
    (r00 : c.nreg 5800 = n) (r72 : c.nreg 5872 = CFb) (r02 : c.nreg 5802 = HPb)
    (r01 : c.nreg 5801 = RPb) (r74 : c.nreg 5874 = CKb) (r79 : c.nreg 5879 = T2b)
    (r76 : c.nreg 5876 = SFb) (r06 : c.nreg 5806 = 1) (r21 : c.nreg 6521 = 1)
    (w0 : SFb + n ≤ W) (w0' : n + 1 ≤ W) (w1 : CFb + n ≤ W) (w2 : HPb + n ≤ W)
    (w3 : RPb + n ≤ W) (w4 : CKb + n ≤ W) (w5 : T2b + nk ≤ W)
    (hrp : ∀ i < n, c.nmem (RPb + i) < n) (hck : ∀ i < n, c.nmem (CKb + i) < nk)
    (d1 : ∀ i < n, ¬ (SFb ≤ CFb + i ∧ CFb + i < SFb + n))
    (d2 : ∀ i < n, ¬ (SFb ≤ HPb + i ∧ HPb + i < SFb + n))
    (d3 : ∀ i < n, ¬ (SFb ≤ RPb + i ∧ RPb + i < SFb + n))
    (d4 : ∀ i < n, ¬ (SFb ≤ CKb + i ∧ CKb + i < SFb + n))
    (d5 : ∀ k < nk, ¬ (SFb ≤ T2b + k ∧ T2b + k < SFb + n)) :
    ∃ c' t, Exec P W sfScan c c' t ∧ t ≤ 34 * n + 3 ∧
      (∀ i < n, c'.nmem (SFb + i) = sfM (c.nmem (CFb + i)) (c.nmem (HPb + i))
        (c.nmem (HPb + c.nmem (RPb + i))) (c.nmem (T2b + c.nmem (CKb + i))) i
        (c.nmem (RPb + i))) ∧
      (∀ a, ¬ (SFb ≤ a ∧ a < SFb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, h1, h2, h3, h4, h5, h6⟩ := mapRun_exec (P := P) c hc (vb := vbSF)
    (bnd := 5800) (ob := 5876) (m := n) (Ob := SFb) (B := 29)
    (fun i => sfM (c.nmem (CFb + i)) (c.nmem (HPb + i))
        (c.nmem (HPb + c.nmem (RPb + i))) (c.nmem (T2b + c.nmem (CKb + i))) i
        (c.nmem (RPb + i))) r00 r21 r76 w0 w0'
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c₁ hw h20 hr hm => by
      have e1 := hm _ (d1 i hi)
      have e2 := hm _ (d2 i hi)
      have e3 := hm _ (d3 i hi)
      have hr' := hrp i hi
      have e4 := hm _ (d2 _ hr')
      have e5 := hm _ (d4 i hi)
      have hk := hck i hi
      have e6 := hm _ (d5 _ hk)
      exact vbSF_exec (P := P) c₁ hw h20
        (by rw [vreg_ok hr (by omega), r72]) (by rw [vreg_ok hr (by omega), r02])
        (by rw [vreg_ok hr (by omega), r01]) (by rw [vreg_ok hr (by omega), r74])
        (by rw [vreg_ok hr (by omega), r79]) (by rw [vreg_ok hr (by omega), r06])
        e1 e2 e3 e4 e5 e6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  exact ⟨c', t, ex, by omega, h1, h2, h3, h4, h5, h6⟩

theorem avScan_exec (c : Config) (hc : WordsBounded W c) {n SFb AKb T2b AVb nk : ℕ}
    (r00 : c.nreg 5800 = n) (r76 : c.nreg 5876 = SFb) (r75 : c.nreg 5875 = AKb)
    (r79 : c.nreg 5879 = T2b) (r77 : c.nreg 5877 = AVb) (r21 : c.nreg 6521 = 1)
    (w0 : AVb + n ≤ W) (w0' : n + 1 ≤ W) (w1 : SFb + n ≤ W) (w2 : AKb + n ≤ W)
    (w5 : T2b + nk ≤ W) (hsf : ∀ i < n, c.nmem (SFb + i) ≤ 1)
    (hak : ∀ i < n, c.nmem (AKb + i) < nk)
    (d1 : ∀ i < n, ¬ (AVb ≤ SFb + i ∧ SFb + i < AVb + n))
    (d2 : ∀ i < n, ¬ (AVb ≤ AKb + i ∧ AKb + i < AVb + n))
    (d3 : ∀ k < nk, ¬ (AVb ≤ T2b + k ∧ T2b + k < AVb + n)) :
    ∃ c' t, Exec P W avScan c c' t ∧ t ≤ 12 * n + 3 ∧
      (∀ i < n, c'.nmem (AVb + i) = c.nmem (SFb + i) * c.nmem (T2b + c.nmem (AKb + i))) ∧
      (∀ a, ¬ (AVb ≤ a ∧ a < AVb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, h1, h2, h3, h4, h5, h6⟩ := mapRun_exec (P := P) c hc (vb := vbAV)
    (bnd := 5800) (ob := 5877) (m := n) (Ob := AVb) (B := 7)
    (fun i => c.nmem (SFb + i) * c.nmem (T2b + c.nmem (AKb + i))) r00 r21 r77 w0 w0'
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c₁ hw h20 hr hm => by
      have e1 := hm _ (d1 i hi)
      have e2 := hm _ (d2 i hi)
      have hk := hak i hi
      have e3 := hm _ (d3 _ hk)
      exact vbAV_exec (P := P) c₁ hw h20
        (by rw [vreg_ok hr (by omega), r76]) (by rw [vreg_ok hr (by omega), r75])
        (by rw [vreg_ok hr (by omega), r79]) e1 e2 e3 (hsf i hi) (by omega) (by omega)
        (by omega))
  exact ⟨c', t, ex, by omega, h1, h2, h3, h4, h5, h6⟩

theorem exScan_exec (c : Config) (hc : WordsBounded W c) {n' EXKb EXMb EXb : ℕ}
    (r11 : c.nreg 5811 = n') (r82 : c.nreg 5882 = EXKb) (r83 : c.nreg 5883 = EXMb)
    (r89 : c.nreg 5889 = EXb) (r06 : c.nreg 5806 = 1) (r21 : c.nreg 6521 = 1)
    (w0 : EXb + n' ≤ W) (w0' : n' + 1 ≤ W) (w1 : EXKb + n' ≤ W) (w2 : EXMb + n' + 1 ≤ W)
    (hb : ∀ j < n', c.nmem (EXKb + j) + c.nmem (EXMb + (j + 1)) ≤ W)
    (d1 : ∀ j < n', ¬ (EXb ≤ EXKb + j ∧ EXKb + j < EXb + n'))
    (d2 : ∀ j < n', ¬ (EXb ≤ EXMb + (j + 1) ∧ EXMb + (j + 1) < EXb + n')) :
    ∃ c' t, Exec P W exScan c c' t ∧ t ≤ 11 * n' + 3 ∧
      (∀ j < n', c'.nmem (EXb + j) = c.nmem (EXKb + j) + c.nmem (EXMb + (j + 1))) ∧
      (∀ a, ¬ (EXb ≤ a ∧ a < EXb + n') → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, h1, h2, h3, h4, h5, h6⟩ := mapRun_exec (P := P) c hc (vb := vbEX)
    (bnd := 5811) (ob := 5889) (m := n') (Ob := EXb) (B := 6)
    (fun j => c.nmem (EXKb + j) + c.nmem (EXMb + (j + 1))) r11 r21 r89 w0 w0'
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun j hj c₁ hw h20 hr hm => vbEX_exec (P := P) c₁ hw h20
      (by rw [vreg_ok hr (by omega), r82]) (by rw [vreg_ok hr (by omega), r83])
      (by rw [vreg_ok hr (by omega), r06]) (hm _ (d1 j hj)) (hm _ (d2 j hj)) (by omega)
      (by omega) (hb j hj))
  exact ⟨c', t, ex, by omega, h1, h2, h3, h4, h5, h6⟩

end Exec

end MfDrv

end BKMNW

end PlanarFlow
