module

public import PlanarFlow.BKMNW.MfX

/-!
# The large-piece separator, stage 1: the darts of the piece map of the core, from the record

At a call of the decomposition `decS` with a large piece (record of phase `0`), the split chain
(`spSR`/`spHR` via `splitD`/`pcertF`) works on the piece map of the **core**
`pdarts M (core M Q P) Hs` (`Q` the pendant vertices). The record (`MfX.lean`) has no flag of the
pendant vertices; they are read off the global vertex numbering `ν` (the array `VP`) under the
convention **`v ∈ Q ↔ ν v` odd** (`QPar`). A dart `d = g i` of the piece is a dart of the piece map
of the core iff both ends have even numbers and it is not inside a hole (the two ends' hole labels
are not the same positive label, `inner_iff_hlab`):

* `cfv v vr h hr` (the flag as a natural expression), **`cfv_eq`**;
* `QPar`, **`mem_pdarts_core_iff`** (the flag of a dart from the numbers and labels of its ends);
* `vbCCa` (five loads), `vbCCb` (the arithmetic), `vbCC`, **`vbCC_exec`** (a value block of
  `mapRunS`, `≤ 26` steps), `cfScan := mapRunS vbCC 5800 5804`, **`cfScan_exec`** (`31 n + 3`
  steps): `OUT[i] = cfv …` over the record's arrays;
* **`cfScan_rec`**: on a record (`RArr`), `OUT[i] = bf (g i ∈ pdarts M (core M Q P) Hs)` for
  `i < n`.

Registers: inputs `5800 = n`, `5801 = RPb`, `5802 = HPb`, `5803 = VPb`, `5804 = OUTb`,
`5806 = 1`, `5807 = 2`, `6521 = 1`; written `6520`, `6522`, `6523 … 6529` (`mapRunS`).
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

/-! ### The flag as a natural expression -/

/-- The flag of a dart of the piece map of the core from the numbers `v`, `vr` of its ends and
their hole labels `h`, `hr`, as computed by `vbCCb`. -/
def cfv (v vr h hr : ℕ) : ℕ :=
  (1 - (v % 2 + vr % 2)) * (1 - (1 - ((1 - (1 - ((h - hr) + (hr - h)))) + (1 - h))))

lemma cfv_eq (v vr h hr : ℕ) :
    cfv v vr h hr = bf (v % 2 = 0 ∧ vr % 2 = 0 ∧ ¬ (0 < h ∧ h = hr)) := by
  unfold cfv bf
  have h1 : v % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h2 : vr % 2 < 2 := Nat.mod_lt _ (by norm_num)
  by_cases a : v % 2 = 0 ∧ vr % 2 = 0 ∧ ¬ (0 < h ∧ h = hr)
  · simp only [a, and_self, not_false_eq_true, ↓reduceIte]
    obtain ⟨a1, a2, a3⟩ := a
    by_cases hh : h = 0
    · subst hh; simp
    · have : h ≠ hr := fun e => a3 ⟨by omega, e⟩
      have e1 : 1 - (1 - ((h - hr) + (hr - h))) = 1 := by omega
      rw [e1]; omega
  · simp only [a, ↓reduceIte]
    by_cases b : v % 2 = 0 ∧ vr % 2 = 0
    · have c : 0 < h ∧ h = hr := by
        by_contra hc; exact a ⟨b.1, b.2, hc⟩
      obtain ⟨c1, c2⟩ := c
      subst c2
      have e1 : 1 - h = 0 := by omega
      simp [e1]
    · have : 1 - (v % 2 + vr % 2) = 0 := by omega
      rw [this, zero_mul]

/-- **The pendant vertices are the odd numbers**: the convention on the global vertex numbering
under which the record determines the core. -/
def QPar (Q : Finset V) (ν : V → ℕ) : Prop := ∀ v, v ∈ Q ↔ ν v % 2 = 1

lemma notMem_of_QPar {Q : Finset V} {ν : V → ℕ} (h : QPar Q ν) (v : V) :
    v ∉ Q ↔ ν v % 2 = 0 := by
  rw [h v]; omega

/-- **The darts of the piece map of the core** from the numbers and hole labels of their ends. -/
lemma mem_pdarts_core_iff {Q : Finset V} {ν : V → ℕ} (hQ : QPar Q ν) {P : Finset D}
    {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {d : D} (hdP : d ∈ P) :
    d ∈ pdarts M (core M Q P) Hs ↔
      ν (M.tail d) % 2 = 0 ∧ ν (M.head d) % 2 = 0 ∧
        ¬ (0 < hlab Hs (M.tail d) ∧ hlab Hs (M.tail d) = hlab Hs (M.head d)) := by
  rw [mem_pdarts, mem_core, inner_iff_hlab hd, notMem_of_QPar hQ, notMem_of_QPar hQ]
  constructor
  · rintro ⟨⟨-, a, b⟩, c⟩; exact ⟨a, b, c⟩
  · rintro ⟨a, b, c⟩; exact ⟨⟨hdP, a, b⟩, c⟩

/-! ### The value block -/

/-- The loads: `r6524 = RP[i]`, `r6525 = VP[i]`, `r6526 = VP[RP[i]]`, `r6527 = HP[i]`,
`r6528 = HP[RP[i]]`. -/
def vbCCa : Stmt :=
  .seq (block [.addN 6524 5801 6520, .loadN 6524 6524])
    (.seq (block [.addN 6525 5803 6520, .loadN 6525 6525])
      (.seq (block [.addN 6526 5803 6524, .loadN 6526 6526])
        (.seq (block [.addN 6527 5802 6520, .loadN 6527 6527])
          (block [.addN 6528 5802 6524, .loadN 6528 6528]))))

/-- The arithmetic: `r6523 := cfv r6525 r6526 r6527 r6528`. -/
def vbCCb : Stmt :=
  block [.modN 6525 6525 5807, .modN 6526 6526 5807, .addN 6525 6525 6526, .subN 6525 5806 6525,
    .subN 6526 6527 6528, .subN 6529 6528 6527, .addN 6526 6526 6529, .subN 6526 5806 6526,
    .subN 6526 5806 6526, .subN 6529 5806 6527, .addN 6526 6526 6529, .subN 6526 5806 6526,
    .subN 6526 5806 6526, .mulN 6523 6525 6526]

/-- **The value block of the flags of the piece map of the core.** -/
def vbCC : Stmt := .seq vbCCa vbCCb

/-- **The scan of the flags of the piece map of the core** over the record. -/
def cfScan : Stmt := mapRunS vbCC 5800 5804

section Exec

variable {P : Input} {W : ℕ}

/-- A two-instruction load `r := mem (B + mem a)`-style, with the counter in any register. -/
theorem ld2r_exec (c : Config) (hc : WordsBounded W c) {t r b ctr i B : ℕ}
    (rb : c.nreg b = B) (rc : c.nreg ctr = i) (w : B + i ≤ W) (h1 : t ≠ b) (h2 : t ≠ ctr) :
    ∃ c' k, Exec P W (block [.addN t b ctr, .loadN r t]) c c' k ∧ k = 2 ∧
      c'.nreg r = c.nmem (B + i) ∧ (∀ x, x ≠ t → x ≠ r → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  ld2_exec c hc rb rc w h1 h2

theorem vbCCa_exec (c : Config) (hc : WordsBounded W c) {i RPb HPb VPb : ℕ}
    (r20 : c.nreg 6520 = i) (r01 : c.nreg 5801 = RPb) (r02 : c.nreg 5802 = HPb)
    (r03 : c.nreg 5803 = VPb) (w1 : RPb + i ≤ W) (w2 : VPb + i ≤ W)
    (w3 : VPb + c.nmem (RPb + i) ≤ W) (w4 : HPb + i ≤ W) (w5 : HPb + c.nmem (RPb + i) ≤ W) :
    ∃ c' k, Exec P W vbCCa c c' k ∧ k ≤ 10 ∧ c'.nreg 6525 = c.nmem (VPb + i) ∧
      c'.nreg 6526 = c.nmem (VPb + c.nmem (RPb + i)) ∧ c'.nreg 6527 = c.nmem (HPb + i) ∧
      c'.nreg 6528 = c.nmem (HPb + c.nmem (RPb + i)) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v1, n1, m1, rr1, rm1, o1⟩ := ld2_exec (P := P) (t := 6524) (r := 6524)
    (b := 5801) (ctr := 6520) c hc r01 r20 w1 (by omega) (by omega)
  have q1 : ∀ x, ¬ vscr x → c₁.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; exact n1 x (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := ld2_exec (P := P) (t := 6525) (r := 6525)
    (b := 5803) (ctr := 6520) c₁ e₁.wb_right (by rw [q1 _ (by unfold vscr; omega), r03])
    (by rw [q1 _ (by unfold vscr; omega), r20]) w2 (by omega) (by omega)
  have q2 : ∀ x, ¬ vscr x → c₂.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; rw [n2 x (by omega) (by omega), q1 x (by unfold vscr; omega)]
  have v1' : c₂.nreg 6524 = c.nmem (RPb + i) := by rw [n2 _ (by omega) (by omega), v1]
  rw [m1] at v2
  obtain ⟨c₃, k₃, e₃, hk₃, v3, n3, m3, rr3, rm3, o3⟩ := ld2_exec (P := P) (t := 6526) (r := 6526)
    (b := 5803) (ctr := 6524) c₂ e₂.wb_right (by rw [q2 _ (by unfold vscr; omega), r03]) v1'
    w3 (by omega) (by omega)
  have q3 : ∀ x, ¬ vscr x → c₃.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; rw [n3 x (by omega) (by omega), q2 x (by unfold vscr; omega)]
  have v1'' : c₃.nreg 6524 = c.nmem (RPb + i) := by rw [n3 _ (by omega) (by omega), v1']
  rw [m2, m1] at v3
  obtain ⟨c₄, k₄, e₄, hk₄, v4, n4, m4, rr4, rm4, o4⟩ := ld2_exec (P := P) (t := 6527) (r := 6527)
    (b := 5802) (ctr := 6520) c₃ e₃.wb_right (by rw [q3 _ (by unfold vscr; omega), r02])
    (by rw [q3 _ (by unfold vscr; omega), r20]) w4 (by omega) (by omega)
  have q4 : ∀ x, ¬ vscr x → c₄.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; rw [n4 x (by omega) (by omega), q3 x (by unfold vscr; omega)]
  have v1''' : c₄.nreg 6524 = c.nmem (RPb + i) := by rw [n4 _ (by omega) (by omega), v1'']
  rw [m3, m2, m1] at v4
  obtain ⟨c₅, k₅, e₅, hk₅, v5, n5, m5, rr5, rm5, o5⟩ := ld2_exec (P := P) (t := 6528) (r := 6528)
    (b := 5802) (ctr := 6524) c₄ e₄.wb_right (by rw [q4 _ (by unfold vscr; omega), r02]) v1'''
    w5 (by omega) (by omega)
  rw [m4, m3, m2, m1] at v5
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega, ?_, ?_, ?_, v5,
    fun x hx => ?_, by rw [m5, m4, m3, m2, m1], by rw [rr5, rr4, rr3, rr2, rr1],
    by rw [rm5, rm4, rm3, rm2, rm1], by rw [o5, o4, o3, o2, o1]⟩
  · rw [n5 _ (by omega) (by omega), n4 _ (by omega) (by omega), n3 _ (by omega) (by omega), v2]
  · rw [n5 _ (by omega) (by omega), n4 _ (by omega) (by omega), v3]
  · rw [n5 _ (by omega) (by omega), v4]
  · unfold vscr at hx; rw [n5 x (by omega) (by omega), q4 x (by unfold vscr; omega)]

theorem vbCCb_exec (c : Config) (hc : WordsBounded W c) {v vr h hr : ℕ}
    (r06 : c.nreg 5806 = 1) (r07 : c.nreg 5807 = 2) (r25 : c.nreg 6525 = v)
    (r26 : c.nreg 6526 = vr) (r27 : c.nreg 6527 = h) (r28 : c.nreg 6528 = hr) :
    ∃ c' k, Exec P W vbCCb c c' k ∧ k = 14 ∧ c'.nreg 6523 = cfv v vr h hr ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b27 : h ≤ W := r27 ▸ hc.1 6527
  have b28 : hr ≤ W := r28 ▸ hc.1 6528
  have b06 : 1 ≤ W := r06 ▸ hc.1 5806
  have b07 : 2 ≤ W := r07 ▸ hc.1 5807
  have m1 : v % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have m2 : vr % 2 < 2 := Nat.mod_lt _ (by norm_num)
  unfold vbCCb
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r06, r07, r25,
    r26, r27, r28]; omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r06, r07, r25,
    r26, r27, r28]; exact le_trans (Nat.mul_le_mul (Nat.sub_le 1 _) (Nat.sub_le 1 _)) (by omega))
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
    simp (disch := omega) only [upd_other, upd_same, r06, r07, r25, r26, r27, r28]
    rfl
  · unfold vscr at hx
    config_simp
    simp (disch := omega) only [upd_other, upd_same]

/-- **The value block of the flags**: `r6523 = cfv VP[i] VP[RP[i]] HP[i] HP[RP[i]]`, scratch
registers only, memory kept. -/
theorem vbCC_exec (c : Config) (hc : WordsBounded W c) {i RPb HPb VPb : ℕ}
    (r20 : c.nreg 6520 = i) (r01 : c.nreg 5801 = RPb) (r02 : c.nreg 5802 = HPb)
    (r03 : c.nreg 5803 = VPb) (r06 : c.nreg 5806 = 1) (r07 : c.nreg 5807 = 2)
    (w1 : RPb + i ≤ W) (w2 : VPb + i ≤ W)
    (w3 : VPb + c.nmem (RPb + i) ≤ W) (w4 : HPb + i ≤ W) (w5 : HPb + c.nmem (RPb + i) ≤ W) :
    ∃ c' k, Exec P W vbCC c c' k ∧ k ≤ 26 ∧
      c'.nreg 6523 = cfv (c.nmem (VPb + i)) (c.nmem (VPb + c.nmem (RPb + i)))
        (c.nmem (HPb + i)) (c.nmem (HPb + c.nmem (RPb + i))) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a5, a6, a7, a8, n1, m1, rr1, rm1, o1⟩ := vbCCa_exec (P := P) c hc r20
    r01 r02 r03 w1 w2 w3 w4 w5
  obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := vbCCb_exec (P := P) c₁ e₁.wb_right
    (by rw [n1 _ (by unfold vscr; omega), r06]) (by rw [n1 _ (by unfold vscr; omega), r07])
    a5 a6 a7 a8
  exact ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, v2, fun x hx => by rw [n2 x hx, n1 x hx],
    by rw [m2, m1], by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩

/-- **The scan of the flags**: `OUT[i] = cfv VP[i] VP[RP[i]] HP[i] HP[RP[i]]` for `i < n`, within
`31 n + 3` steps; memory outside `[OUTb, OUTb + n)` and registers outside `6520`, `6522`,
`6523 … 6529` kept. -/
theorem cfScan_exec (c : Config) (hc : WordsBounded W c) {n RPb HPb VPb OUTb : ℕ}
    (r00 : c.nreg 5800 = n) (r01 : c.nreg 5801 = RPb) (r02 : c.nreg 5802 = HPb)
    (r03 : c.nreg 5803 = VPb) (r04 : c.nreg 5804 = OUTb) (r06 : c.nreg 5806 = 1)
    (r07 : c.nreg 5807 = 2) (r21 : c.nreg 6521 = 1)
    (w0 : OUTb + n ≤ W) (w0' : n + 1 ≤ W) (w1 : RPb + n ≤ W) (w2 : VPb + n ≤ W)
    (w4 : HPb + n ≤ W) (hrp : ∀ i < n, c.nmem (RPb + i) < n)
    (d1 : ∀ i < n, ¬ (OUTb ≤ RPb + i ∧ RPb + i < OUTb + n))
    (d2 : ∀ i < n, ¬ (OUTb ≤ VPb + i ∧ VPb + i < OUTb + n))
    (d3 : ∀ i < n, ¬ (OUTb ≤ HPb + i ∧ HPb + i < OUTb + n)) :
    ∃ c' t, Exec P W cfScan c c' t ∧ t ≤ 31 * n + 3 ∧
      (∀ i < n, c'.nmem (OUTb + i) = cfv (c.nmem (VPb + i)) (c.nmem (VPb + c.nmem (RPb + i)))
        (c.nmem (HPb + i)) (c.nmem (HPb + c.nmem (RPb + i)))) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, h1, h2, h3, h4, h5, h6⟩ := mapRun_exec (P := P) c hc (vb := vbCC)
    (bnd := 5800) (ob := 5804) (m := n) (Ob := OUTb) (B := 26)
    (fun i => cfv (c.nmem (VPb + i)) (c.nmem (VPb + c.nmem (RPb + i)))
      (c.nmem (HPb + i)) (c.nmem (HPb + c.nmem (RPb + i)))) r00 r21 r04 w0 w0'
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c₁ hw h20 hr hm => by
      have e1 : c₁.nmem (RPb + i) = c.nmem (RPb + i) := hm _ (d1 i hi)
      have hj := hrp i hi
      have e2 : c₁.nmem (VPb + i) = c.nmem (VPb + i) := hm _ (d2 i hi)
      have e3 : c₁.nmem (VPb + c.nmem (RPb + i)) = c.nmem (VPb + c.nmem (RPb + i)) :=
        hm _ (d2 _ hj)
      have e4 : c₁.nmem (HPb + i) = c.nmem (HPb + i) := hm _ (d3 i hi)
      have e5 : c₁.nmem (HPb + c.nmem (RPb + i)) = c.nmem (HPb + c.nmem (RPb + i)) :=
        hm _ (d3 _ hj)
      obtain ⟨c₂, k, e, hk, v, n2, m2, rr2, rm2, o2⟩ := vbCC_exec (P := P) c₁ hw h20
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega), r01])
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega), r02])
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega), r03])
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega), r06])
        (by rw [hr _ (by unfold vscr; omega) (by omega) (by omega), r07])
        (by omega) (by omega) (by rw [e1]; omega) (by omega) (by rw [e1]; omega)
      rw [e1, e2, e3, e4, e5] at v
      exact ⟨c₂, k, e, hk, v, n2, m2, rr2, rm2, o2⟩)
  exact ⟨c', t, ex, by omega, h1, h2, h3, h4, h5, h6⟩

/-- **The scan on a record**: with `QPar Q ν`, pairwise disjoint holes and the record's arrays
`RP`, `HP`, `VP` (`RArr`), `OUT[i] = bf (g i ∈ pdarts M (core M Q P) Hs)` for `i < n`. -/
theorem cfScan_rec {gid : D → ℕ} {ν : V → ℕ} {S T Q : Finset V} {x : MCall M} {m n R : ℕ}
    {g : ℕ → D} (hQ : QPar Q ν) (hd : x.2.1.Pairwise Disjoint) (c : Config)
    (hA : RArr M gid ν S T x m n R g c.nmem) (hc : WordsBounded W c) {OUTb : ℕ}
    (r00 : c.nreg 5800 = n) (r01 : c.nreg 5801 = R + 3 + n) (r02 : c.nreg 5802 = R + 3 + 2 * n)
    (r03 : c.nreg 5803 = R + 3 + 4 * n) (r04 : c.nreg 5804 = OUTb) (r06 : c.nreg 5806 = 1)
    (r07 : c.nreg 5807 = 2) (r21 : c.nreg 6521 = 1)
    (w0 : OUTb + n ≤ W) (w1 : R + 3 + 5 * n ≤ W) (hO : R + 3 + 6 * n + m ≤ OUTb) :
    ∃ c' t, Exec P W cfScan c c' t ∧ t ≤ 31 * n + 3 ∧
      (∀ i < n, c'.nmem (OUTb + i) = bf (g i ∈ pdarts M (core M Q x.1.piece) x.2.1)) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, h1, h2, h3, h4, h5, h6⟩ := cfScan_exec (P := P) c hc r00 r01 r02 r03 r04
    r06 r07 r21 w0 (by omega) (by omega) (by omega) (by omega) (fun i hi => (hA.rp i hi).1)
    (fun i hi => by omega) (fun i hi => by omega) (fun i hi => by omega)
  refine ⟨c', t, ex, ht, fun i hi => ?_, h2, h3, h4, h5, h6⟩
  rw [h1 i hi, cfv_eq]
  obtain ⟨hj, hgj⟩ := hA.rp i hi
  have hv1 : c.nmem (R + 3 + 4 * n + i) = ν (M.tail (g i)) := hA.vp i hi
  have hv2 : c.nmem (R + 3 + 4 * n + c.nmem (R + 3 + n + i)) = ν (M.head (g i)) := by
    rw [hA.vp _ hj, hgj, CombMap.tail_rev]
  have hh1 : c.nmem (R + 3 + 2 * n + i) = hlab x.2.1 (M.tail (g i)) := hA.hp i hi
  have hh2 : c.nmem (R + 3 + 2 * n + c.nmem (R + 3 + n + i)) = hlab x.2.1 (M.head (g i)) := by
    rw [hA.hp _ hj, hgj, CombMap.tail_rev]
  rw [hv1, hv2, hh1, hh2]
  unfold bf
  congr 1
  exact propext (mem_pdarts_core_iff hQ hd (hA.g_mem i hi)).symm

end Exec

end MfDrv

end BKMNW

end PlanarFlow
