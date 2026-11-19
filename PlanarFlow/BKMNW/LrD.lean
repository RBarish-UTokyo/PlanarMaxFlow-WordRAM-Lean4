module

public import PlanarFlow.BKMNW.LrC

/-!
# The children's records of the large split: one child, second half

After `lrOneA` (`LP` at `A + n`, its compaction `CI`/`IX`, the compaction `IX2` of `CF`, `KC`,
`HC`, the flags `Bc` of the child's core piece map at `Y + 3 n`):

* **`lrCr`** (`crProg` over the parent record at `Y`: the child's rotation, in the parent's
  numbering, `CN` at `Y + 6 n`), `lrCr_exec`;
* `lrB4b` (the bases of the record at `R' = r8509 + 2`, as `smB4b`), `smB6` (`RP'`), **`lrSP`**
  (`lrProg`: `SP'[CI[i]] := CI[CN[i]]` for the flagged `i` of `Bc`), `smB5` (`GP'`, `HP'`, `KP'`,
  `VP'`, `FX'`), **`lrHd`** (the header `n_X | 0 | 1 - hb` and the size `6 n_X + m_X + 3` in
  `8510`);
* **`lrOneB = lrB4b ; smB6 ; lrSP ; smB5 ; lrHd`**, **`lrOneB_exec`** (within `64 n + 120` steps).
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

/-- The registers of `crProg`. -/
def lrCrR : Stmt := block [.copyN 6200 5504, .copyN 6201 8506]

/-- The child's rotation over the parent record. -/
def lrCr : Stmt := .seq lrCrR crProg

/-- The bases of the child's record (as `smB4b`, from `r8509`). -/
def lrB4b : Stmt := block [.constN 5519 2, .addN 5542 8509 5519, .constN 5519 3,
  .addN 5554 5542 5519, .addN 5555 5554 5540, .addN 5556 5555 5540, .addN 5557 5556 5540,
  .addN 5558 5557 5540, .addN 5559 5558 5540, .addN 5560 5559 5540]

/-- The registers of the state array's remap. -/
def lrSPR : Stmt := block [.copyN 6310 5504, .copyN 6311 8516, .copyN 6312 5509,
  .copyN 6313 8517, .copyN 6314 5559]

/-- **The child's state array**: `SP'[CI[i]] := CI[CN[i]]` for the flagged `i` of `Bc`. -/
def lrSP : Stmt := .seq lrSPR lrProg

/-- **The header of the child's record** and its size in `8510`. -/
def lrHd : Stmt := block [.storeN 5542 5540, .constN 5519 1, .addN 5546 5542 5519,
  .constN 5547 0, .storeN 5546 5547, .constN 5519 2, .addN 5548 5542 5519, .subN 5549 6521 8505,
  .storeN 5548 5549, .constN 5519 6, .mulN 8510 5519 5540, .addN 8510 8510 5541,
  .constN 5519 3, .addN 8510 8510 5519]

/-- **One child's record, second half.** -/
def lrOneB : Stmt := .seq lrB4b (.seq smB6 (.seq lrSP (.seq smB5 lrHd)))

section Exec

variable {I : Input} {W : ℕ}

theorem lrCrR_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec I W lrCrR c c' t ∧ t = 2 ∧ c'.nreg 6200 = c.nreg 5504 ∧
      c'.nreg 6201 = c.nreg 8506 ∧ (∀ x, (x < 6200 ∨ 6201 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hc.1 5504; have := hc.1 8506
  unfold lrCrR
  exec_block
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])
    try omega

set_option maxHeartbeats 1000000 in
/-- **The child's rotation over the parent record** (`crProg_childRot` with `m = n`, `A = Y`). -/
theorem lrCr_exec {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] (M : CombMap D V F)
    (σ : Perm D) (B : Finset D) (L : List D) (Bc : Finset D)
    (c : Config) (hc : WordsBounded W c) {n Y : ℕ} (r04 : c.nreg 5504 = n)
    (r06 : c.nreg 8506 = Y) (hW : Y + 8 * n ≤ W) (hm : n + 2 ≤ W)
    {e : ℕ → D} (he : ∀ i < n, ∀ j < n, e i = e j → i = j) (heB : ∀ i < n, e i ∈ B)
    (hBe : ∀ x ∈ B, ∃ i < n, e i = x)
    (hσ : Stable σ B) (hrB : ∀ x ∈ B, M.rev x ∈ B) (hrL : ∀ x ∈ L, M.rev x ∈ L)
    (hBc : Bc ⊆ B \ L.toFinset)
    (hSG : ∀ i < n, c.nmem (Y + i) < n ∧ e (c.nmem (Y + i)) = σ (e i))
    (hRV : ∀ i < n, c.nmem (Y + n + i) < n ∧ e (c.nmem (Y + n + i)) = M.rev (e i))
    (hLF : ∀ i < n, c.nmem (Y + 2 * n + i) = if e i ∈ L.toFinset then 1 else 0)
    (hCF : ∀ i < n, c.nmem (Y + 3 * n + i) = if e i ∈ Bc then 1 else 0) :
    ∃ c' k, Exec I W lrCr c c' k ∧ k ≤ 79 * n + 72 ∧
      (∀ i < n, e i ∈ Bc → c'.nmem (Y + 6 * n + i) < n ∧
        e (c'.nmem (Y + 6 * n + i)) = childRot M σ B L Bc (e i)) ∧
      (∀ a, ¬ (Y + 4 * n ≤ a ∧ a < Y + 8 * n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6200 ∨ 6250 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a0, a1, n1, m1, rr1, rm1, o1⟩ := lrCrR_exec (I := I) c hc
  rw [r04] at a0; rw [r06] at a1
  obtain ⟨c₂, t₂, e₂, ht₂, cn, mm, nn, rr2, rm2, o2⟩ := crProg_childRot (P := I) M σ B L Bc c₁
    e₁.wb_right a0 a1 hW hm he heB hBe hσ hrB hrL hBc (by rw [m1]; exact hSG)
    (by rw [m1]; exact hRV) (by rw [m1]; exact hLF) (by rw [m1]; exact hCF)
  refine ⟨c₂, _, .seq e₁ e₂, by clear * - ht₁ ht₂; omega, cn, fun a ha => by rw [mm a ha, m1],
    fun x hx => ?_, by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
  rw [nn x (by clear * - hx; omega), n1 x (by clear * - hx; omega)]

theorem lrB4b_exec (c : Config) (hc : WordsBounded W c) {XX nl : ℕ}
    (r09 : c.nreg 8509 = XX) (r40 : c.nreg 5540 = nl) (w : XX + 5 + 6 * nl ≤ W) :
    ∃ c' t, Exec I W lrB4b c c' t ∧ t = 10 ∧ c'.nreg 5542 = XX + 2 ∧
      c'.nreg 5554 = XX + 2 + 3 ∧ c'.nreg 5555 = XX + 2 + 3 + nl ∧
      c'.nreg 5556 = XX + 2 + 3 + 2 * nl ∧ c'.nreg 5557 = XX + 2 + 3 + 3 * nl ∧
      c'.nreg 5558 = XX + 2 + 3 + 4 * nl ∧ c'.nreg 5559 = XX + 2 + 3 + 5 * nl ∧
      c'.nreg 5560 = XX + 2 + 3 + 6 * nl ∧
      (∀ x, (x < 5519 ∨ (5519 < x ∧ x < 5542) ∨ (5542 < x ∧ x < 5554) ∨ 5560 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lrB4b
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r09, r40]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r09, r40])
    try omega

theorem lrSPR_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec I W lrSPR c c' t ∧ t = 5 ∧ c'.nreg 6310 = c.nreg 5504 ∧
      c'.nreg 6311 = c.nreg 8516 ∧ c'.nreg 6312 = c.nreg 5509 ∧ c'.nreg 6313 = c.nreg 8517 ∧
      c'.nreg 6314 = c.nreg 5559 ∧ (∀ x, (x < 6310 ∨ 6314 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hc.1 5504; have := hc.1 8516; have := hc.1 5509; have := hc.1 8517; have := hc.1 5559
  unfold lrSPR
  exec_block
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])
    try omega

/-- **The child's state array on the machine** (`lrProg`). -/
theorem lrSP_exec (c : Config) (hc : WordsBounded W c) {n Fb CIb Ab OUTb : ℕ}
    (r04 : c.nreg 5504 = n) (r16 : c.nreg 8516 = Fb) (r09 : c.nreg 5509 = CIb)
    (r17 : c.nreg 8517 = Ab) (r59 : c.nreg 5559 = OUTb)
    (l1 : Fb + n ≤ OUTb) (l2 : CIb + n ≤ OUTb) (l3 : Ab + n ≤ OUTb) (l4 : OUTb + n ≤ W)
    (w4 : n + 1 ≤ W)
    (hA : ∀ i < n, 0 < c.nmem (Fb + i) → c.nmem (Ab + i) < n)
    (hCI : ∀ i < n, 0 < c.nmem (Fb + i) → c.nmem (CIb + i) < n)
    (hinj : ∀ i < n, ∀ j < n, 0 < c.nmem (Fb + i) → 0 < c.nmem (Fb + j) →
      c.nmem (CIb + i) = c.nmem (CIb + j) → i = j) :
    ∃ c' t, Exec I W lrSP c c' t ∧ t ≤ 14 * n + 10 ∧
      (∀ i < n, 0 < c.nmem (Fb + i) →
        c'.nmem (OUTb + c.nmem (CIb + i)) = c.nmem (CIb + c.nmem (Ab + i))) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6310 ∨ 6319 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a0, a1, a2, a3, a4, n1, m1, rr1, rm1, o1⟩ := lrSPR_exec (I := I) c hc
  rw [r04] at a0; rw [r16] at a1; rw [r09] at a2; rw [r17] at a3; rw [r59] at a4
  obtain ⟨c₂, t₂, e₂, ht₂, g2, mm2, nn2, rr2, rm2, o2⟩ := lrProg_exec (P := I) c₁ e₁.wb_right
    a0 a1 a2 a3 a4 l1 l2 l3 l4 w4
    (fun i hi hf => by rw [m1] at hf ⊢; exact hA i hi hf)
    (fun i hi hf => by rw [m1] at hf ⊢; exact hCI i hi hf)
    (fun i hi j hj hfi hfj e => by rw [m1] at hfi hfj e; exact hinj i hi j hj hfi hfj e)
  rw [m1] at g2 mm2
  refine ⟨c₂, _, .seq e₁ e₂, by clear * - ht₁ ht₂; omega, g2, mm2, fun x hx => ?_,
    by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
  rw [nn2 x (by clear * - hx; omega), n1 x (by clear * - hx; omega)]

theorem lrHd_exec (c : Config) (hc : WordsBounded W c) {XX nl ml hb : ℕ}
    (r42 : c.nreg 5542 = XX + 2) (r40 : c.nreg 5540 = nl) (r41 : c.nreg 5541 = ml)
    (r21 : c.nreg 6521 = 1) (r05 : c.nreg 8505 = hb)
    (w : XX + 2 + (6 * nl + ml + 3) + 3 ≤ W) :
    ∃ c' t, Exec I W lrHd c c' t ∧ t = 14 ∧ c'.nreg 8510 = 6 * nl + ml + 3 ∧
      c'.nmem (XX + 2) = nl ∧ c'.nmem (XX + 2 + 1) = 0 ∧ c'.nmem (XX + 2 + 2) = 1 - hb ∧
      (∀ a, (a < XX + 2 ∨ XX + 4 < a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5519 ∨ (5519 < x ∧ x < 5546) ∨ (5549 < x ∧ x ≠ 8510)) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hh := hc.1 8505
  unfold lrHd
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r42, r40, r41, r21, r05]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun a ha => ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r42, r40, r41, r21, r05])
    try omega

end Exec

end MfDrv

end BKMNW

end PlanarFlow
