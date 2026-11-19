module

public import PlanarFlow.BKMNW.NpDivM
public import PlanarFlow.BKMNW.LinLoops

/-!
# `dvP`: the vertex labels and the net outflow of the flow array at every vertex

A building block of the push-backs (`retP`, `frmP`: the bounds `β` and the excesses), of
FixConservationOnPath (the inflow at `p i`) and of `c2sP` (`c2sBeta`). From the frame of a call at
`d` (`r3004`) and a scratch base `A` (`r8430`), registers `8431 … 8447`:

* `dvA`: the bases (`SG = d + 4 + 2m`, `FL = d + 4 + 6m`, `LAB = A`, `DV = A + m`, `DG = A + 2m`)
  and the arguments of `OrbLab.olProg`; loop `dvZ`: `[A, A + 3m)` zeroed;
* `olProg`: `LAB[i] = olab SG i + 1` (the vertex label of `en i`);
* loop `dvB`: `DV[olab i] += FL[i]`, `DG[olab i] += 1`.

**`dvP_exec`** (`48 m + 30` steps) and **`dvP_div`**: for every `i < m`,
`(DV[olab i] : ℤ) - Z · DG[olab i] = (pmap h).div g (tail (en i))` when `FL` holds `Z + g`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs OrbLab

universe w

/-! ### The program -/

/-- The bases and the arguments of `olProg`, part 1. -/
def dvA1 : Stmt :=
  block [.copyN 8431 3004, .loadN 8432 8431, .constN 8433 2, .mulN 8434 8432 8433,
    .addN 8434 8431 8434, .constN 8435 4, .addN 7350 8434 8435, .copyN 7351 8430,
    .copyN 7352 8432]

/-- The bases, part 2. -/
def dvA2 : Stmt :=
  block [.constN 8433 6, .mulN 8434 8432 8433, .addN 8434 8431 8434,
    .addN 8436 8434 8435, .addN 8437 8430 8432, .addN 8438 8437 8432, .addN 8439 8438 8432,
    .copyN 8440 8430, .constN 8441 1, .constN 8442 0]

/-- The bases and the arguments of `olProg`. -/
def dvA : Stmt := .seq dvA1 dvA2

/-- `mem[j] := 0`; `j := j + 1`. -/
def dvZ : Stmt := block [.storeN 8440 8442, .addN 8440 8440 8441]

/-- `i := 0`. -/
def dvI : Stmt := block [.constN 8443 0]

/-- `v := LAB[i] - 1`; `DV[v] += FL[i]`; `DG[v] += 1`; `i := i + 1`. -/
def dvB : Stmt :=
  block [.addN 8444 8430 8443, .loadN 8444 8444, .subN 8444 8444 8441, .addN 8445 8436 8443,
    .loadN 8445 8445, .addN 8446 8437 8444, .loadN 8447 8446, .addN 8447 8447 8445,
    .storeN 8446 8447, .addN 8446 8438 8444, .loadN 8447 8446, .addN 8447 8447 8441,
    .storeN 8446 8447, .addN 8443 8443 8441]

/-- **The vertex labels and the net outflows.** -/
def dvP : Stmt :=
  .seq dvA (.seq (.whileLtN 8440 8439 dvZ) (.seq olProg (.seq dvI (.whileLtN 8443 8432 dvB))))

/-! ### The blocks -/

section Blocks

variable {P : Input} {W : ℕ}

theorem dvA1_exec (c : Config) (hc : WordsBounded W c) {d A m : ℕ} (r4 : c.nreg 3004 = d)
    (r30 : c.nreg 8430 = A) (hm : c.nmem d = m) (w1 : d + 6 * m + 4 ≤ W) (w3 : 6 ≤ W) :
    ∃ c' t, Exec P W dvA1 c c' t ∧ t = 9 ∧ c'.nreg 8431 = d ∧ c'.nreg 8432 = m ∧
      c'.nreg 7350 = d + 2 * m + 4 ∧ c'.nreg 7351 = A ∧ c'.nreg 7352 = m ∧
      c'.nreg 8435 = 4 ∧ c'.nreg 8430 = A ∧
      (∀ x, (x < 7350 ∨ 7352 < x) → (x < 8431 ∨ 8447 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dvA1
  exec_block
  all_goals try (clear * - r4 r30 hm w1 w3; config_simp; (try simp only [r4, r30, hm]); omega)
  all_goals try (clear * - w1 w3; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r4, r30, hm]
  all_goals try omega
  simp only [upd_apply]; split_ifs <;> omega

theorem dvA2_exec (c : Config) (hc : WordsBounded W c) {d A m : ℕ} (r31 : c.nreg 8431 = d)
    (r32 : c.nreg 8432 = m) (r35 : c.nreg 8435 = 4) (r30 : c.nreg 8430 = A)
    (w1 : d + 6 * m + 4 ≤ W) (w2 : A + 3 * m ≤ W) (w3 : 6 ≤ W) :
    ∃ c' t, Exec P W dvA2 c c' t ∧ t = 10 ∧
      c'.nreg 8436 = d + 6 * m + 4 ∧ c'.nreg 8437 = A + m ∧ c'.nreg 8438 = A + m + m ∧
      c'.nreg 8439 = A + m + m + m ∧ c'.nreg 8440 = A ∧ c'.nreg 8441 = 1 ∧
      c'.nreg 8442 = 0 ∧
      (∀ x, (x < 8433 ∨ 8447 < x) → x ≠ 8435 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dvA2
  exec_block
  all_goals try (clear * - r31 r32 r35 r30 w1 w2 w3; config_simp; (try simp only [r31, r32, r35, r30]); omega)
  all_goals try (clear * - w1 w2 w3; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r31, r32, r35, r30]
  all_goals try omega
  simp only [upd_apply]; split_ifs <;> omega

theorem dvZ_exec (c : Config) (hc : WordsBounded W c) {j : ℕ} (r40 : c.nreg 8440 = j)
    (r41 : c.nreg 8441 = 1) (r42 : c.nreg 8442 = 0) (w : j + 1 ≤ W) :
    ∃ c' t, Exec P W dvZ c c' t ∧ t = 2 ∧ c'.nreg 8440 = j + 1 ∧ c'.nmem = upd c.nmem j 0 ∧
      (∀ x, x ≠ 8440 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dvZ
  exec_block
  all_goals try (config_simp; simp only [r40, r41, r42]; omega)
  refine ⟨rfl, ?_, ?_, fun x h1 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r40, r41]
  · config_simp; simp only [r40, r42]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem dvI_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W dvI c c' t ∧ t = 1 ∧ c'.nreg 8443 = 0 ∧
      (∀ x, x ≠ 8443 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dvI
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem dvB_exec (c : Config) (hc : WordsBounded W c) {A FLb DVb DGb i v : ℕ}
    (r30 : c.nreg 8430 = A) (r36 : c.nreg 8436 = FLb) (r37 : c.nreg 8437 = DVb)
    (r38 : c.nreg 8438 = DGb) (r41 : c.nreg 8441 = 1) (r43 : c.nreg 8443 = i)
    (hv : c.nmem (A + i) = v + 1) (hne : DVb < DGb) (w1 : A + i ≤ W) (w2 : FLb + i ≤ W)
    (w3 : DVb + v ≤ W) (w4 : DGb + v ≤ W) (w5 : c.nmem (DVb + v) + c.nmem (FLb + i) ≤ W)
    (w6 : c.nmem (DGb + v) + 1 ≤ W) (w7 : i + 1 ≤ W) :
    ∃ c' t, Exec P W dvB c c' t ∧ t = 14 ∧ c'.nreg 8443 = i + 1 ∧
      c'.nmem = upd (upd c.nmem (DVb + v) (c.nmem (DVb + v) + c.nmem (FLb + i))) (DGb + v)
        (c.nmem (DGb + v) + 1) ∧
      (∀ x, (x < 8443 ∨ 8447 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hne' : DGb + v ≠ DVb + v := by omega
  unfold dvB
  exec_block
  all_goals try (config_simp; simp only [r30, r36, r37, r38, r41, r43, hv,
    show v + 1 - 1 = v by omega]; (try rw [upd_other _ _ _ hne']); omega)
  refine ⟨rfl, ?_, ?_, fun x h1 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r41, r43]
  · config_simp; simp only [r30, r36, r37, r38, r41, r43, hv, show v + 1 - 1 = v by omega]
    rw [upd_other _ _ _ hne']
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

end Blocks

/-! ### The loops and the whole program -/

section Run

variable {P : Input} {W : ℕ}

/-- **The zeroing loop** over `[A, A + 3m)`. -/
theorem dvZL_exec (c : Config) (hc : WordsBounded W c) {A n : ℕ} (r40 : c.nreg 8440 = A)
    (r39 : c.nreg 8439 = A + n) (r41 : c.nreg 8441 = 1) (r42 : c.nreg 8442 = 0)
    (w : A + n + 1 ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 8440 8439 dvZ) c c' t ∧ t ≤ 4 * n + 2 ∧
      (∀ a, A ≤ a → a < A + n → c'.nmem a = 0) ∧
      (∀ a, (a < A ∨ A + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 8440 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun j c' =>
    (∀ x, x ≠ 8440 → c'.nreg x = c.nreg x) ∧ (∀ a, A ≤ a → a < j → c'.nmem a = 0) ∧
    (∀ a, (a < A ∨ j ≤ a) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', t, ex, ht, -, -, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 8440) (b := 8439)
    (body := dvZ) J (B := 2) c hc r40 r39 (by omega)
    ⟨fun _ _ => rfl, fun a h1 h2 => absurd h2 (by omega), fun _ _ => rfl, rfl, rfl, rfl⟩
    (fun j c₁ hlo hi hw h40 h39 ⟨f₁, z₁, o₁, q1, q2, q3⟩ => by
      obtain ⟨c₂, t₂, e₂, ht₂, g40, gm, gn, gr, grm, go⟩ := dvZ_exec (P := P) c₁ hw h40
        (by rw [f₁ _ (by omega), r41]) (by rw [f₁ _ (by omega), r42]) (by omega)
      refine ⟨c₂, t₂, e₂, ht₂.le, g40, by rw [gn _ (by omega)]; exact h39,
        fun x h1 => by rw [gn x h1, f₁ x h1], fun a h1 h2 => ?_, fun a ha => ?_,
        by rw [gr, q1], by rw [grm, q2], by rw [go, q3]⟩
      · rw [gm]
        by_cases e : a = j
        · rw [e, upd_same]
        · rw [upd_other _ _ _ e]; exact z₁ a h1 (by omega)
      · rw [gm, upd_other _ _ _ (by omega)]; exact o₁ a (by omega))
  refine ⟨c', t, ex, by omega, fun a h1 h2 => j2 a h1 h2, fun a ha => j3 a (by omega), j1, j4,
    j5, j6⟩

/-- The sums and the counts over the first `i` labels. -/
def dvS (lab fl : ℕ → ℕ) (i v : ℕ) : ℕ := ∑ j ∈ (range i).filter (fun j => lab j = v), fl j

/-- The counts. -/
def dvC (lab : ℕ → ℕ) (i v : ℕ) : ℕ := ((range i).filter (fun j => lab j = v)).card

lemma dvS_succ (lab fl : ℕ → ℕ) (i v : ℕ) :
    dvS lab fl (i + 1) v = dvS lab fl i v + if lab i = v then fl i else 0 := by
  unfold dvS; rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [sum_insert (by simp), add_comm]
  · rw [add_zero]

lemma dvC_succ (lab : ℕ → ℕ) (i v : ℕ) :
    dvC lab (i + 1) v = dvC lab i v + if lab i = v then 1 else 0 := by
  unfold dvC; rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rw [add_zero]

lemma dvS_le (lab fl : ℕ → ℕ) (i v : ℕ) : dvS lab fl i v ≤ ∑ j ∈ range i, fl j :=
  sum_le_sum_of_subset (filter_subset _ _)

lemma dvC_le (lab : ℕ → ℕ) (i v : ℕ) : dvC lab i v ≤ i :=
  (card_le_card (filter_subset _ _)).trans (by simp)

/-- **The accumulation loop** `DV[lab i] += FL[i]`, `DG[lab i] += 1`. -/
theorem dvBL_exec (c : Config) (hc : WordsBounded W c) {A FLb m : ℕ} (lab : ℕ → ℕ)
    (r30 : c.nreg 8430 = A) (r36 : c.nreg 8436 = FLb) (r37 : c.nreg 8437 = A + m)
    (r38 : c.nreg 8438 = A + m + m) (r41 : c.nreg 8441 = 1) (r43 : c.nreg 8443 = 0)
    (r32 : c.nreg 8432 = m) (hlab : ∀ i < m, c.nmem (A + i) = lab i + 1 ∧ lab i < m)
    (hz : ∀ v < m, c.nmem (A + m + v) = 0 ∧ c.nmem (A + m + m + v) = 0)
    (hFL : FLb + m ≤ A) (w1 : A + 3 * m ≤ W)
    (wS : ∑ j ∈ range m, c.nmem (FLb + j) ≤ W) (wm : m + 1 ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 8443 8432 dvB) c c' t ∧ t ≤ 16 * m + 2 ∧
      (∀ v < m, c'.nmem (A + m + v) = dvS lab (fun j => c.nmem (FLb + j)) m v ∧
        c'.nmem (A + m + m + v) = dvC lab m v) ∧
      (∀ a, (a < A + m ∨ A + m + m + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 8443 ∨ 8447 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨fl, hfl⟩ : ∃ fl : ℕ → ℕ, fl = fun j => c.nmem (FLb + j) := ⟨_, rfl⟩
  have wS' : ∑ j ∈ range m, fl j ≤ W := by rw [hfl]; exact wS
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 8443 ∨ 8447 < x) → c'.nreg x = c.nreg x) ∧
    (∀ v < m, c'.nmem (A + m + v) = dvS lab fl i v ∧ c'.nmem (A + m + m + v) = dvC lab i v) ∧
    (∀ a, (a < A + m ∨ A + m + m + m ≤ a) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', t, ex, ht, -, -, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 8443) (b := 8432)
    (body := dvB) J (B := 14) c hc r43 r32 (Nat.zero_le _)
    ⟨fun _ _ => rfl, fun v hv => ⟨by rw [(hz v hv).1]; simp [dvS],
      by rw [(hz v hv).2]; simp [dvC]⟩, fun _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c₁ _ hi hw h43 h32 ⟨f₁, s₁, o₁, q1, q2, q3⟩ => by
      obtain ⟨hl1, hl2⟩ := hlab i hi
      have hv : c₁.nmem (A + i) = lab i + 1 := by rw [o₁ _ (by omega)]; exact hl1
      have hf : c₁.nmem (FLb + i) = fl i := by rw [hfl]; exact o₁ _ (by omega)
      obtain ⟨sv, cv⟩ := s₁ (lab i) hl2
      have b1 := dvS_le lab fl i (lab i)
      have b2 := dvC_le lab i (lab i)
      have b3 : ∑ j ∈ range i, fl j + fl i ≤ ∑ j ∈ range m, fl j := by
        rw [← sum_range_succ]; exact sum_le_sum_of_subset (range_subset_range.2 hi)
      obtain ⟨c₂, t₂, e₂, ht₂, g43, gm, gn, gr, grm, go⟩ := dvB_exec (P := P) c₁ hw
        (v := lab i) (by rw [f₁ _ (by omega), r30]) (by rw [f₁ _ (by omega), r36])
        (by rw [f₁ _ (by omega), r37]) (by rw [f₁ _ (by omega), r38])
        (by rw [f₁ _ (by omega), r41]) h43 hv (by omega) (by omega) (by omega) (by omega)
        (by omega) (by rw [sv, hf]; omega) (by rw [cv]; omega) (by omega)
      refine ⟨c₂, t₂, e₂, ht₂.le, g43, by rw [gn _ (by omega)]; exact h32,
        fun x hx => by rw [gn x hx, f₁ x hx], fun v hv' => ?_, fun a ha => ?_,
        by rw [gr, q1], by rw [grm, q2], by rw [go, q3]⟩
      · obtain ⟨sv', cv'⟩ := s₁ v hv'
        rw [gm, dvS_succ, dvC_succ]
        by_cases e : lab i = v
        · subst e
          simp only [↓reduceIte]
          refine ⟨?_, ?_⟩
          · rw [upd_other _ _ _ (by omega), upd_same, sv, hf]
          · rw [upd_same, cv]
        · simp only [e, ↓reduceIte, add_zero]
          refine ⟨?_, ?_⟩
          · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact sv'
          · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact cv'
      · rw [gm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact o₁ a ha)
  subst hfl
  exact ⟨c', t, ex, by omega, j2, j3, j1, j4, j5, j6⟩

/-- **The vertex labels and the net outflows**, from the frame at `d` (`r3004`) and the scratch
base `A` (`r8430`): `LAB[i] = olab SG i + 1`, `DV[v] = Σ_{olab j = v} FL[j]`, `DG[v] = #{j : olab j =
v}` for `v < m`, within `48 m + 30` steps; memory outside `[A, A + 3m)` kept. -/
theorem dvP_exec (c : Config) (hc : WordsBounded W c) {d A m : ℕ} (r4 : c.nreg 3004 = d)
    (r30 : c.nreg 8430 = A) (hm : c.nmem d = m) (hp : PermOn (sgF d m c.nmem) m)
    (hA : d + 4 + 7 * m ≤ A) (w2 : A + 3 * m + 1 ≤ W) (w3 : 6 ≤ W)
    (wS : ∑ j ∈ range m, c.nmem (d + 6 * m + 4 + j) ≤ W) :
    ∃ c' t, Exec P W dvP c c' t ∧ t ≤ 48 * m + 30 ∧
      (∀ i < m, c'.nmem (A + i) = olab (sgF d m c.nmem) i + 1) ∧
      (∀ v < m, c'.nmem (A + m + v) =
          dvS (olab (sgF d m c.nmem)) (fun j => c.nmem (d + 6 * m + 4 + j)) m v ∧
        c'.nmem (A + m + m + v) = dvC (olab (sgF d m c.nmem)) m v) ∧
      (∀ a, (a < A ∨ A + 3 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 7350 ∨ 7352 < x) → (x < 7400 ∨ 7405 < x) → (x < 8431 ∨ 8447 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a31, a32, a50, a51, a52, a35, a30, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    dvA1_exec (P := P) c hc r4 r30 hm (by omega) w3
  obtain ⟨c₂, t₂, e₂, ht₂, b36, b37, b38, b39, b40, b41, b42, f₂, m₂, rr₂, rm₂, o₂⟩ :=
    dvA2_exec (P := P) c₁ e₁.wb_right a31 a32 a35 a30 (by omega) (by omega) w3
  obtain ⟨c₃, t₃, e₃, ht₃, z₃, k₃, f₃, rr₃, rm₃, o₃⟩ := dvZL_exec (P := P) c₂ e₂.wb_right
    (n := 3 * m) b40 (by rw [b39]; ring) b41 b42 (by omega)
  have mem₃ : ∀ a, a < A → c₃.nmem a = c.nmem a := fun a ha => by
    rw [k₃ a (Or.inl ha), m₂, m₁]
  obtain ⟨c₄, t₄, e₄, ht₄, l₄, k₄, f₄, rr₄, rm₄, o₄⟩ := olProg_exec (P := P) (W := W)
    (f := sgF d m c.nmem) hp (Pb := d + 2 * m + 4) (Lb := A) (by omega) (by omega) (by omega)
    c₃ e₃.wb_right (by rw [f₃ _ (by omega), f₂ _ (by omega) (by omega)]; exact a50)
    (by rw [f₃ _ (by omega), f₂ _ (by omega) (by omega)]; exact a51)
    (by rw [f₃ _ (by omega), f₂ _ (by omega) (by omega)]; exact a52)
    (fun x hx => by rw [mem₃ _ (by omega)]; unfold sgF; congr 1; omega)
    (fun x hx => z₃ _ (by omega) (by omega))
  obtain ⟨c₅, t₅, e₅, ht₅, i43, f₅, m₅, rr₅, rm₅, o₅⟩ := dvI_exec (P := P) c₄ e₄.wb_right
  have g : ∀ x, (x < 7400 ∨ 7405 < x) → x ≠ 8443 → x ≠ 8440 → c₅.nreg x = c₂.nreg x :=
    fun x h1 h2 h3 => by rw [f₅ x h2, f₄ x h1, f₃ x h3]
  obtain ⟨c₆, t₆, e₆, ht₆, d₆, k₆, f₆, rr₆, rm₆, o₆⟩ := dvBL_exec (P := P) c₅ e₅.wb_right
    (A := A) (FLb := d + 6 * m + 4) (m := m) (olab (sgF d m c.nmem))
    (by rw [g _ (by omega) (by omega) (by omega), f₂ _ (by omega) (by omega)]; exact a30)
    (by rw [g _ (by omega) (by omega) (by omega)]; exact b36)
    (by rw [g _ (by omega) (by omega) (by omega)]; exact b37)
    (by rw [g _ (by omega) (by omega) (by omega)]; exact b38)
    (by rw [g _ (by omega) (by omega) (by omega)]; exact b41) i43
    (by rw [g _ (by omega) (by omega) (by omega), f₂ _ (by omega) (by omega)]; exact a32)
    (fun i hi => ⟨by rw [m₅]; exact l₄ i hi, olab_lt hp hi⟩)
    (fun v hv => ⟨by rw [m₅, k₄ _ (Or.inr (by omega))]; exact z₃ _ (by omega) (by omega),
      by rw [m₅, k₄ _ (Or.inr (by omega))]; exact z₃ _ (by omega) (by omega)⟩)
    (by omega) (by omega)
    (by
      have : ∀ j ∈ range m, c₅.nmem (d + 6 * m + 4 + j) = c.nmem (d + 6 * m + 4 + j) :=
        fun j hj => by
          rw [mem_range] at hj
          rw [m₅, k₄ _ (Or.inl (by omega)), mem₃ _ (by omega)]
      rw [sum_congr rfl this]; exact wS)
    (by omega)
  have hFL₅ : ∀ j < m, c₅.nmem (d + 6 * m + 4 + j) = c.nmem (d + 6 * m + 4 + j) := fun j hj => by
    rw [m₅, k₄ _ (Or.inl (by omega)), mem₃ _ (by omega)]
  have hS : ∀ v, dvS (olab (sgF d m c.nmem)) (fun j => c₅.nmem (d + 6 * m + 4 + j)) m v =
      dvS (olab (sgF d m c.nmem)) (fun j => c.nmem (d + 6 * m + 4 + j)) m v := fun v =>
    sum_congr rfl fun j hj => hFL₅ j (mem_range.1 (mem_filter.1 hj).1)
  refine ⟨c₆, t₁ + t₂ + (t₃ + (t₄ + (t₅ + t₆))), .seq (.seq e₁ e₂) (.seq e₃ (.seq e₄ (.seq e₅ e₆))),
    by omega, fun i hi => ?_, fun v hv => ?_, fun a ha => ?_, fun x h1 h2 h3 => ?_, ?_, ?_, ?_⟩
  · rw [k₆ _ (Or.inl (by omega)), m₅]; exact l₄ i hi
  · obtain ⟨u1, u2⟩ := d₆ v hv
    exact ⟨by rw [u1, hS], u2⟩
  · rcases ha with ha | ha
    · rw [k₆ _ (Or.inl (by omega)), m₅, k₄ _ (Or.inl ha), mem₃ a ha]
    · rw [k₆ _ (Or.inr (by omega)), m₅, k₄ _ (Or.inr (by omega)), k₃ a (Or.inr ha), m₂, m₁]
  · rw [f₆ x (by omega), g x h2 (by omega) (by omega), f₂ x (by omega) (by omega), f₁ x h1 h3]
  · rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁]
  · rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁]
  · rw [o₆, o₅, o₄, o₃, o₂, o₁]

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- **The net outflow from the machine's sums**: when the flow array holds `Z + g`,
`DV[olab i] - Z · DG[olab i]` is the net outflow of `g` at the vertex of `en i`. -/
theorem dvP_div {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    {g : SDart (pdarts M x.1.piece x.2.1) → ℤ} (hfl : FLHas Z m d en mem g) {i : ℕ}
    (hi : i < m) :
    ((dvS (olab (sgF d m mem)) (fun j => mem (d + 6 * m + 4 + j)) m (olab (sgF d m mem) i) : ℕ)
        : ℤ) - Z * (dvC (olab (sgF d m mem)) m (olab (sgF d m mem) i) : ℕ) =
      (pmap h).div g ((pmap h).tail (vDart hL hi)) := by
  rw [hL.div_eq_sum h g hi]
  unfold dvS dvC
  rw [Nat.cast_sum, card_eq_sum_ones, Nat.cast_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 (mem_filter.1 hj).1
  have := hfl j hj'
  rw [show d + 4 + 6 * m + j = d + 6 * m + 4 + j by omega] at this
  simp only [Nat.cast_one, mul_one]
  omega

end Run

end MfDrv

end BKMNW

end PlanarFlow
