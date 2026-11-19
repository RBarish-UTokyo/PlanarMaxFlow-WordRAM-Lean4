module

public import PlanarSeparator.Machine.SepIn
public import PlanarSeparator.MillerFaceOf

/-!
# The output of Miller's program: from the faces of the twice subdivided map to a side per dart

Steps 9–10 give a simple cycle separator `C'`, `Z'` of `M.stellar.stellar` (marks `0`/`1` of its
triangles). The proof of `exists_short_cycle_separator_face` turns it into faces `Z` of
`M.stellar` (`PlanarSeparator.Map.faceSepZ`: the majority faces, two of whose three triangles
are in `Z'`, if some dart leaves them, otherwise the face of a triangle in `Z'` or off it), and
the split of the recursion takes the darts of the piece by the side of their triangle.

* `MillerProg.sepOut` (`MillerProg.sepOut_exec`, `105 m + 30` steps): the majority marks
  (`mjLoop`), the number of darts leaving them and a triangle marked `1` and one marked `0`
  (`scLoop`), and the marks of `Z` (`cpyN` or `indLoop`).
* `MillerProg.zfv_faceSepZ`: these marks are those of `faceSepZ Z' t₁ t₂`
  (`MillerProg.mjv_maj` for the majority faces); `MillerProg.wR_wSt`: the weights of Miller's
  program are the dart weights of the recursion (`wF (wS S)`, `S` the old flagged darts).
* **`MillerProg.sepOut_sep`**: from the separator of steps 9–10, the marks of `Z` and a cycle
  `C` with the conclusion of `exists_short_cycle_separator_card` (`card_sep_of`).
* **`MillerProg.sepRun_exec`**: the whole program `sepRun prog = sepIn ; prog ; soIn ; sepOut`
  for any `prog` meeting `MillerProg.Spec10` (steps 1–10 from the input written by `sepIn`, with
  the marks of a separator of the twice subdivided map).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

variable {W : ℕ} {P : Input}

/-! ### The programs -/

/-- One face of the first subdivision: `mj[u] = (zm[3u] + zm[3u+1] + zm[3u+2]) / 2` (two of
its three triangles marked; `r368 = u`, `r371`, `r372` the bases of `zm` and `mj`, `r375 = 1`,
`r376 = 2`, `r377 = 3`). -/
def mjbody : Stmt :=
  block [.mulN 380 377 368, .addN 380 371 380, .loadN 381 380, .addN 380 380 375,
    .loadN 382 380, .addN 380 380 375, .loadN 383 380, .addN 381 381 382, .addN 381 381 383,
    .divN 381 381 376, .addN 380 372 368, .storeN 380 381, .addN 368 368 375]

/-- **The majority faces** (`r370 = m` faces). -/
def mjLoop : Stmt := .seq (.instr (.constN 368 0)) (.whileLtN 368 370 mjbody)

/-- The marks of the majority faces: two of the three triangles of the face `u` marked. -/
def mjv (zm : ℕ → ℕ) (u : ℕ) : ℕ := (zm (3 * u) + zm (3 * u + 1) + zm (3 * u + 2)) / 2

theorem mjLoop_exec {m bZ bMj : ℕ} (hd : bMj + m ≤ bZ ∨ bZ + 3 * m ≤ bMj)
    (hW : bZ + 3 * m ≤ W ∧ bMj + m ≤ W) (c : Config) (hc : WordsBounded W c)
    (h370 : c.nreg 370 = m) (h371 : c.nreg 371 = bZ) (h372 : c.nreg 372 = bMj)
    (h375 : c.nreg 375 = 1) (h376 : c.nreg 376 = 2) (h377 : c.nreg 377 = 3)
    (hz : ∀ y < 3 * m, c.nmem (bZ + y) ≤ 1) :
    ∃ c' t, Exec P W mjLoop c c' t ∧ t ≤ 15 * m + 3 ∧
      (∀ u < m, c'.nmem (bMj + u) = mjv (fun y => c.nmem (bZ + y)) u) ∧
      (∀ r, r ≠ 368 → (r < 380 ∨ 383 < r) → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bMj ∨ bMj + m ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 368 = i ∧ i ≤ m ∧
    (∀ r, r ≠ 368 → (r < 380 ∨ 383 < r) → c'.nreg r = c.nreg r) ∧
    (∀ u < i, c'.nmem (bMj + u) = mjv (fun y => c.nmem (bZ + y)) u) ∧
    (∀ a, ¬ (bMj ≤ a ∧ a < bMj + i) → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  have e₁ := Exec.constN (P := P) hc 368 0 (by omega)
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 368) (rN := 370) (N := m)
    (lo := 0) (B := 13) (body := mjbody) I
    (fun i c' h => ⟨h.1, h.2.1, (h.2.2.2.1 370 (by omega) (by omega)).trans h370⟩)
    (fun i c₁ ⟨hw, h368, hi, hr, hd', hm, ho⟩ hlt => by
      have hc := hw
      have g371 := (hr 371 (by omega) (by omega)).trans h371
      have g372 := (hr 372 (by omega) (by omega)).trans h372
      have g375 := (hr 375 (by omega) (by omega)).trans h375
      have g376 := (hr 376 (by omega) (by omega)).trans h376
      have g377 := (hr 377 (by omega) (by omega)).trans h377
      have m0 : c₁.nmem (bZ + 3 * i) = c.nmem (bZ + 3 * i) := hm _ (by omega)
      have m1 : c₁.nmem (bZ + 3 * i + 1) = c.nmem (bZ + (3 * i + 1)) := hm _ (by omega)
      have m2 : c₁.nmem (bZ + 3 * i + 1 + 1) = c.nmem (bZ + (3 * i + 2)) := hm _ (by omega)
      have z0 := hz (3 * i) (by omega)
      have z1 := hz (3 * i + 1) (by omega)
      have z2 := hz (3 * i + 2) (by omega)
      have k1 := g371; have k5 := g375; have k7 := g377
      unfold mjbody
      exec_block
      all_goals try (show _ ≤ _; config_simp; (try simp only [g371, g375, g377, h368]); omega)
      all_goals try (show _ ≤ _; config_simp; (try simp only [k1, k5, k7, h368, m0, m1, m2]); omega)
      refine ⟨⟨‹_›, ?_, by omega, fun r a b => ?_, fun u hu => ?_, fun a ha => ?_, ho⟩, le_rfl⟩
      all_goals config_simp
      · rw [h368, g375]
      · simp only [upd_apply]; split_ifs <;> first | omega | exact hr r a b
      · simp only [g371, g372, g375, g376, g377, h368, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · have := hd' u hu
          split_ifs <;> first | omega | exact this
        · rw [ite_eq_left rfl]
          simp only [mjv, m0, m1, m2]
      · simp only [g372, h368, upd_apply]
        split_ifs <;> first | omega | exact hm a (by omega))
    (by omega) ⟨e₁.wb_right, by config_simp, by omega,
      fun r a _ => by config_simp; rw [upd_other _ _ _ a],
      fun u hu => absurd hu (by omega), fun a _ => rfl, rfl⟩
  obtain ⟨-, -, -, hr, hd', hm, ho⟩ := hI
  exact ⟨c', 1 + t, .seq e₁ e, by omega, hd', hr, fun a ha => hm a (by omega), ho⟩

/-- One dart `x = r368` of the first subdivision: add `mj[x/3] - mj[α x / 3]` (`1` iff `x`
leaves the majority faces) to `r387`, and keep in `r388` (`r389`) the last triangle `x` of the
second subdivision with `zm[x] = 1` (`= 0`); `r373` the base of the reversals `A₁`. -/
def scbody : Stmt :=
  block [.addN 380 371 368, .loadN 381 380, .divN 382 368 377, .addN 380 372 382,
    .loadN 383 380, .addN 380 373 368, .loadN 384 380, .divN 384 384 377, .addN 380 372 384,
    .loadN 384 380, .subN 383 383 384, .addN 387 387 383, .subN 385 368 388,
    .mulN 385 385 381, .addN 388 388 385, .subN 386 375 381, .subN 385 368 389,
    .mulN 385 385 386, .addN 389 389 385, .addN 368 368 375]

/-- **The scan of the darts** (`r378 = 3 m` darts). -/
def scLoop : Stmt :=
  .seq (block [.constN 368 0, .constN 387 0, .constN 388 0, .constN 389 0])
    (.whileLtN 368 378 scbody)

set_option maxHeartbeats 4000000 in
/-- **The scan**: the number of darts leaving the majority faces (`r387`), and a triangle marked
`1` (`r388`) and one marked `0` (`r389`) if there are. -/
theorem scLoop_exec {m bZ bMj bA : ℕ} (hW : bZ + 3 * m ≤ W ∧ bMj + m ≤ W ∧ bA + 3 * m ≤ W)
    (c : Config) (hc : WordsBounded W c)
    (h371 : c.nreg 371 = bZ) (h372 : c.nreg 372 = bMj) (h373 : c.nreg 373 = bA)
    (h375 : c.nreg 375 = 1) (h377 : c.nreg 377 = 3) (h378 : c.nreg 378 = 3 * m)
    (hz : ∀ y < 3 * m, c.nmem (bZ + y) ≤ 1) (hmj : ∀ u < m, c.nmem (bMj + u) ≤ 1)
    (hA : ∀ x < 3 * m, c.nmem (bA + x) < 3 * m) :
    ∃ c' t, Exec P W scLoop c c' t ∧ t ≤ 22 * (3 * m) + 6 ∧
      c'.nreg 387 = ∑ x ∈ range (3 * m),
        (c.nmem (bMj + x / 3) - c.nmem (bMj + c.nmem (bA + x) / 3)) ∧
      (c'.nreg 388 + 1 ≤ 3 * m ∨ m = 0) ∧
      ((∃ x < 3 * m, c.nmem (bZ + x) = 1) → c.nmem (bZ + c'.nreg 388) = 1) ∧
      (c'.nreg 389 + 1 ≤ 3 * m ∨ m = 0) ∧
      ((∃ x < 3 * m, c.nmem (bZ + x) = 0) → c.nmem (bZ + c'.nreg 389) = 0) ∧
      (∀ r, r ≠ 368 → (r < 380 ∨ 389 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.output = c.output := by
  set f : ℕ → ℕ := fun x => c.nmem (bMj + x / 3) - c.nmem (bMj + c.nmem (bA + x) / 3) with hf
  have hf1 : ∀ x < 3 * m, f x ≤ 1 := fun x hx => by
    have := hmj (x / 3) (by omega); simp only [hf]; omega
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 368 = i ∧ i ≤ 3 * m ∧
    (∀ r, r ≠ 368 → (r < 380 ∨ 389 < r) → c'.nreg r = c.nreg r) ∧
    c'.nreg 387 = ∑ x ∈ range i, f x ∧ c'.nreg 387 ≤ i ∧
    (c'.nreg 388 + 1 ≤ i ∨ (i = 0 ∧ c'.nreg 388 = 0)) ∧
    ((∃ x < i, c.nmem (bZ + x) = 1) → c.nmem (bZ + c'.nreg 388) = 1) ∧
    (c'.nreg 389 + 1 ≤ i ∨ (i = 0 ∧ c'.nreg 389 = 0)) ∧
    ((∃ x < i, c.nmem (bZ + x) = 0) → c.nmem (bZ + c'.nreg 389) = 0) ∧
    c'.nmem = c.nmem ∧ c'.output = c.output
  have e₁ := Exec.constN (P := P) hc 368 0 (by omega)
  have e₂ := Exec.constN (P := P) e₁.wb_right 387 0 (by omega)
  have e₃ := Exec.constN (P := P) e₂.wb_right 388 0 (by omega)
  have e₄ := Exec.constN (P := P) e₃.wb_right 389 0 (by omega)
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 368) (rN := 378)
    (N := 3 * m) (lo := 0) (B := 20) (body := scbody) I
    (fun i c' h => ⟨h.1, h.2.1, (h.2.2.2.1 378 (by omega) (by omega)).trans h378⟩)
    (fun i c₁ ⟨hw, h368, hi, hr, hacc, hacc', hy1, hy1', hy2, hy2', hm, ho⟩ hlt => by
      have hc := hw
      have k1 := (hr 371 (by omega) (by omega)).trans h371
      have k2 := (hr 372 (by omega) (by omega)).trans h372
      have k3 := (hr 373 (by omega) (by omega)).trans h373
      have k5 := (hr 375 (by omega) (by omega)).trans h375
      have k7 := (hr 377 (by omega) (by omega)).trans h377
      have hAi := hA i hlt
      have hmj1 := hmj (i / 3) (by omega)
      have hmj2 := hmj (c.nmem (bA + i) / 3) (by omega)
      have hfi : c.nmem (bMj + i / 3) - c.nmem (bMj + c.nmem (bA + i) / 3) ≤ 1 := by omega
      have hzi := hz i hlt
      obtain hz0 | hz0 : c.nmem (bZ + i) = 0 ∨ c.nmem (bZ + i) = 1 := by omega
      all_goals
        unfold scbody
        exec_block
        all_goals try (show _ ≤ _; config_simp; (try simp only [k1, k2, k3, k5, k7, h368, hm]); omega)
        all_goals try (show _ ≤ _; config_simp; (try simp only [k1, k5, h368, hm, hz0]); omega)
        refine ⟨⟨‹_›, ?_, by omega, fun r a b => ?_, ?_, ?_, ?_, fun h => ?_, ?_, fun h => ?_,
          by config_simp; exact hm, ho⟩, le_rfl⟩
        all_goals config_simp
        all_goals try (simp only [k1, k2, k3, k5, k7, h368, hm, hz0, Nat.sub_self, mul_zero,
          mul_one, add_zero, Nat.sub_zero])
        all_goals first
          | omega
          | (simp only [upd_apply]; split_ifs <;> first | omega | exact hr r a b)
          | (rw [Finset.sum_range_succ, ← hacc])
          | (obtain ⟨x, hx, hzx⟩ := h
             rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
             · exact hy1' ⟨x, hx, hzx⟩
             · omega)
          | (obtain ⟨x, hx, hzx⟩ := h
             rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
             · exact hy2' ⟨x, hx, hzx⟩
             · omega)
          | (rw [show c₁.nreg 388 + (i - c₁.nreg 388) = i by omega]; exact hz0)
          | (rw [show c₁.nreg 389 + (i - c₁.nreg 389) = i by omega]; exact hz0))
    (by omega) ⟨e₄.wb_right, by config_simp, by omega,
      fun r a b => by
        config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl,
      by config_simp; simp, by config_simp; omega, Or.inr ⟨rfl, by config_simp⟩,
      fun ⟨x, hx, _⟩ => absurd hx (by omega), Or.inr ⟨rfl, by config_simp⟩,
      fun ⟨x, hx, _⟩ => absurd hx (by omega), rfl, rfl⟩
  obtain ⟨-, -, -, hr, hacc, -, hy1, hy1', hy2, hy2', hm, ho⟩ := hI
  exact ⟨c', 1 + (1 + (1 + (1 + 0))) + t,
    .seq (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.skip e₄.wb_right))))) e, by omega, hacc,
    by omega, fun h => hy1' (by obtain ⟨x, hx, h⟩ := h; exact ⟨x, hx, h⟩), by omega,
    fun h => hy2' (by obtain ⟨x, hx, h⟩ := h; exact ⟨x, hx, h⟩), hr, hm, ho⟩

/-- One face `u = r368`: `Zf[u] = 1` iff `u = r369` (`r374` the base of `Zf`). -/
def indbody : Stmt :=
  block [.subN 380 368 369, .subN 381 369 368, .addN 380 380 381, .subN 380 375 380,
    .addN 381 374 368, .storeN 381 380, .addN 368 368 375]

/-- **The marks of one face** (`r370 = m` faces). -/
def indLoop : Stmt := .seq (.instr (.constN 368 0)) (.whileLtN 368 370 indbody)

theorem indLoop_exec {m bZf t : ℕ} (hW : bZf + m ≤ W) (htm : t < m) (c : Config)
    (hc : WordsBounded W c)
    (h369 : c.nreg 369 = t) (h370 : c.nreg 370 = m) (h374 : c.nreg 374 = bZf)
    (h375 : c.nreg 375 = 1) :
    ∃ c' t', Exec P W indLoop c c' t' ∧ t' ≤ 9 * m + 3 ∧
      (∀ u < m, c'.nmem (bZf + u) = if u = t then 1 else 0) ∧
      (∀ r, r ≠ 368 → r ≠ 380 → r ≠ 381 → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bZf ∨ bZf + m ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 368 = i ∧ i ≤ m ∧
    (∀ r, r ≠ 368 → r ≠ 380 → r ≠ 381 → c'.nreg r = c.nreg r) ∧
    (∀ u < i, c'.nmem (bZf + u) = if u = t then 1 else 0) ∧
    (∀ a, ¬ (bZf ≤ a ∧ a < bZf + i) → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  have e₁ := Exec.constN (P := P) hc 368 0 (by omega)
  obtain ⟨c', t', e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 368) (rN := 370) (N := m)
    (lo := 0) (B := 7) (body := indbody) I
    (fun i c' h => ⟨h.1, h.2.1, (h.2.2.2.1 370 (by omega) (by omega) (by omega)).trans h370⟩)
    (fun i c₁ ⟨hw, h368, hi, hr, hd', hm, ho⟩ hlt => by
      have hc := hw
      have k9 := (hr 369 (by omega) (by omega) (by omega)).trans h369
      have k4 := (hr 374 (by omega) (by omega) (by omega)).trans h374
      have k5 := (hr 375 (by omega) (by omega) (by omega)).trans h375
      unfold indbody
      exec_block
      all_goals try (show _ ≤ _; config_simp; (try simp only [k9, k4, k5, h368]); omega)
      refine ⟨⟨‹_›, ?_, by omega, fun r a b d => ?_, fun u hu => ?_, fun a ha => ?_, ho⟩, le_rfl⟩
      all_goals config_simp
      · rw [h368, k5]
      · simp only [upd_apply]; split_ifs <;> first | omega | exact hr r a b d
      · simp only [k9, k4, k5, h368, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · have := hd' u hu
          split_ifs at this ⊢ <;> first | omega | exact this
        · split_ifs <;> omega
      · simp only [k4, h368, upd_apply]
        split_ifs <;> first | omega | exact hm a (by omega))
    (by omega) ⟨e₁.wb_right, by config_simp, by omega,
      fun r a _ _ => by config_simp; rw [upd_other _ _ _ a],
      fun u hu => absurd hu (by omega), fun a _ => rfl, rfl⟩
  obtain ⟨-, -, -, hr, hd', hm, ho⟩ := hI
  exact ⟨c', 1 + t', .seq e₁ e, by omega, hd', hr, fun a ha => hm a (by omega), ho⟩

/-- The constants and the bases of the copy (`r370 = m`, `r372 = bMj`, `r374 = bZf`). -/
def soB1 : Stmt := block [.constN 375 1, .constN 376 2, .constN 377 3, .mulN 378 377 370,
  .constN 307 1, .copyN 338 370, .copyN 339 372, .copyN 340 374]

/-- **The faces of the separator in the first subdivision** (a mark per face at `bZf`): the
majority faces if some dart leaves them, otherwise the face of the last triangle marked `1`
(no majority face) or of the last triangle marked `0` (every face a majority face). -/
def sepOut : Stmt :=
  .seq soB1 <| .seq mjLoop <| .seq scLoop <| .seq (.instr (.constN 380 0)) <|
    .ifLtN 380 387 cpyN <| .seq (.instr (.loadN 381 372)) <|
      .seq (.ifLtN 380 381 (.instr (.divN 369 389 377)) (.instr (.divN 369 388 377))) indLoop

/-- The faces chosen by `sepOut`, in numbers: `mjv` if `0 < s`, else the face of `y₁` if
`mjv 0 = 0`, else that of `y₂`. -/
def zfv (zm : ℕ → ℕ) (s y₁ y₂ u : ℕ) : ℕ :=
  if 0 < s then mjv zm u else if mjv zm 0 = 0 then (if u = y₁ / 3 then 1 else 0)
    else (if u = y₂ / 3 then 1 else 0)

set_option maxHeartbeats 4000000 in
/-- **`sepOut` on the machine**, within `105 m + 30` steps. -/
theorem sepOut_exec {m bZ bMj bA bZf : ℕ} (hm1 : 1 ≤ m)
    (hd : (bMj + m ≤ bZ ∨ bZ + 3 * m ≤ bMj) ∧ (bMj + m ≤ bA ∨ bA + 3 * m ≤ bMj) ∧
      (bMj + m ≤ bZf ∨ bZf + m ≤ bMj) ∧ (bZf + m ≤ bZ ∨ bZ + 3 * m ≤ bZf) ∧
      (bZf + m ≤ bA ∨ bA + 3 * m ≤ bZf))
    (hW : bZ + 3 * m ≤ W ∧ bMj + m ≤ W ∧ bA + 3 * m ≤ W ∧ bZf + m ≤ W)
    (c : Config) (hc : WordsBounded W c)
    (h370 : c.nreg 370 = m) (h371 : c.nreg 371 = bZ) (h372 : c.nreg 372 = bMj)
    (h373 : c.nreg 373 = bA) (h374 : c.nreg 374 = bZf)
    (hz : ∀ y < 3 * m, c.nmem (bZ + y) ≤ 1) (hA : ∀ x < 3 * m, c.nmem (bA + x) < 3 * m) :
    ∃ (c' : Config) (t y₁ y₂ : ℕ), Exec P W sepOut c c' t ∧ t ≤ 105 * m + 30 ∧
      y₁ < 3 * m ∧ ((∃ x < 3 * m, c.nmem (bZ + x) = 1) → c.nmem (bZ + y₁) = 1) ∧
      y₂ < 3 * m ∧ ((∃ x < 3 * m, c.nmem (bZ + x) = 0) → c.nmem (bZ + y₂) = 0) ∧
      (∀ u < m, c'.nmem (bZf + u) = zfv (fun y => c.nmem (bZ + y))
        (∑ x ∈ range (3 * m), (mjv (fun y => c.nmem (bZ + y)) (x / 3) -
          mjv (fun y => c.nmem (bZ + y)) (c.nmem (bA + x) / 3))) y₁ y₂ u) ∧
      (∀ a, (a < bMj ∨ bMj + m ≤ a) → (a < bZf ∨ bZf + m ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.output = c.output := by
  obtain ⟨d1, d2, d3, d4, d5⟩ := hd
  set zm : ℕ → ℕ := fun y => c.nmem (bZ + y) with hzm
  -- the constants
  obtain ⟨c₁, t₁, e₁, ht₁, g5, g6, g7, g8, g307, g338, g339, g340, hm₁, ho₁⟩ :
      ∃ c₁ t₁, Exec P W soB1 c c₁ t₁ ∧ t₁ ≤ 8 ∧ c₁.nreg 375 = 1 ∧ c₁.nreg 376 = 2 ∧
        c₁.nreg 377 = 3 ∧ c₁.nreg 378 = 3 * m ∧ c₁.nreg 307 = 1 ∧ c₁.nreg 338 = m ∧
        c₁.nreg 339 = bMj ∧ c₁.nreg 340 = bZf ∧ c₁.nmem = c.nmem ∧ c₁.output = c.output := by
    unfold soB1
    exec_block
    all_goals try (show _ ≤ _; config_simp; (try simp only [h370]); omega)
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
    all_goals (config_simp <;> (try simp only [h370, h372, h374]) <;> omega)
  have i₁ : ∀ r, r ≠ 375 → r ≠ 376 → r ≠ 377 → r ≠ 378 → r ≠ 307 → r ≠ 338 → r ≠ 339 →
      r ≠ 340 → c₁.nreg r = c.nreg r := fun r a1 a2 a3 a4 a5 a6 a7 a8 => e₁.nreg_of_wr (by
    simp only [soB1, block, Stmt.wr, Instr.wr, Bool.or_false, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne, ne_eq]; omega)
  have j : ∀ r, 368 < r → r < 375 → c₁.nreg r = c.nreg r := fun r a b =>
    i₁ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  -- the majority faces
  obtain ⟨c₂, t₂, e₂, ht₂, hmj, hr₂, hm₂, ho₂⟩ := mjLoop_exec (P := P) (W := W) (m := m)
    (bZ := bZ) (bMj := bMj) d1 ⟨hW.1, hW.2.1⟩ c₁ e₁.wb_right ((j 370 (by omega) (by omega)).trans
      h370) ((j 371 (by omega) (by omega)).trans h371) ((j 372 (by omega) (by omega)).trans h372)
    g5 g6 g7 (by rw [hm₁]; exact hz)
  rw [hm₁] at hmj
  have hmjl : ∀ u < m, c₂.nmem (bMj + u) ≤ 1 := fun u hu => by
    rw [hmj u hu]; unfold mjv; beta_reduce
    have := hz (3 * u) (by omega); have := hz (3 * u + 1) (by omega)
    have := hz (3 * u + 2) (by omega); omega
  have k₂ : ∀ r, r ≠ 368 → (r < 380 ∨ 383 < r) → c₂.nreg r = c₁.nreg r := hr₂
  -- the scan
  obtain ⟨c₃, t₃, e₃, ht₃, hacc, hy1, hy1', hy2, hy2', hr₃, hm₃, ho₃⟩ := scLoop_exec (P := P)
    (W := W) (m := m) (bZ := bZ) (bMj := bMj) (bA := bA) ⟨hW.1, hW.2.1, hW.2.2.1⟩ c₂ e₂.wb_right
    ((k₂ 371 (by omega) (by omega)).trans ((j 371 (by omega) (by omega)).trans h371))
    ((k₂ 372 (by omega) (by omega)).trans ((j 372 (by omega) (by omega)).trans h372))
    ((k₂ 373 (by omega) (by omega)).trans ((j 373 (by omega) (by omega)).trans h373))
    ((k₂ 375 (by omega) (by omega)).trans g5) ((k₂ 377 (by omega) (by omega)).trans g7)
    ((k₂ 378 (by omega) (by omega)).trans g8)
    (fun y hy => by rw [hm₂ _ (by omega), hm₁]; exact hz y hy) hmjl
    (fun x hx => by rw [hm₂ _ (by omega), hm₁]; exact hA x hx)
  have M₂ : ∀ a, a < bMj ∨ bMj + m ≤ a → c₂.nmem a = c.nmem a := fun a h => by
    rw [hm₂ a h, hm₁]
  have hzc : ∀ x < 3 * m, c₂.nmem (bZ + x) = zm x := fun x hx => M₂ _ (by omega)
  set s := ∑ x ∈ range (3 * m), (mjv zm (x / 3) - mjv zm (c.nmem (bA + x) / 3)) with hs
  have hacc' : c₃.nreg 387 = s := by
    rw [hacc, hs]
    refine sum_congr rfl fun x hx => ?_
    have hx := mem_range.1 hx
    have := hA x hx
    rw [M₂ (bA + x) (by omega), hmj _ (by omega), hmj _ (by omega)]
  have k₃ : ∀ r, r ≠ 368 → (r < 380 ∨ 389 < r) → c₃.nreg r = c₁.nreg r := fun r a b =>
    (hr₃ r a b).trans (k₂ r a (by omega))
  have Y1 : (∃ x < 3 * m, zm x = 1) → zm (c₃.nreg 388) = 1 := fun ⟨x, hx, h⟩ => by
    rw [← hzc _ (by omega)]; exact hy1' ⟨x, hx, by rw [hzc x hx]; exact h⟩
  have Y2 : (∃ x < 3 * m, zm x = 0) → zm (c₃.nreg 389) = 0 := fun ⟨x, hx, h⟩ => by
    rw [← hzc _ (by omega)]; exact hy2' ⟨x, hx, by rw [hzc x hx]; exact h⟩
  have e₄ := Exec.constN (P := P) e₃.wb_right 380 0 (by omega)
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg 380 0 }
  have hw₄ := e₄.wb_right
  have k₄ : ∀ r, r ≠ 380 → c₄.nreg r = c₃.nreg r := fun r h => upd_other _ _ _ h
  have q380 : c₄.nreg 380 = 0 := by show upd c₃.nreg 380 0 380 = 0; rw [upd_same]
  have q387 : c₄.nreg 387 = s := (k₄ 387 (by omega)).trans hacc'
  by_cases hs0 : 0 < s
  · obtain ⟨c₅, t₅, e₅, ht₅, hd₅, -, hm₅, ho₅⟩ := cpyN_exec (P := P) (W := W) (N := m)
      (bs := bMj) (bd := bZf) d3 ⟨hW.2.1, hW.2.2.2⟩ c₄ hw₄
      ((k₄ 307 (by omega)).trans ((k₃ 307 (by omega) (by omega)).trans g307))
      ((k₄ 338 (by omega)).trans ((k₃ 338 (by omega) (by omega)).trans g338))
      ((k₄ 339 (by omega)).trans ((k₃ 339 (by omega) (by omega)).trans g339))
      ((k₄ 340 (by omega)).trans ((k₃ 340 (by omega) (by omega)).trans g340))
    refine ⟨c₅, t₁ + (t₂ + (t₃ + (1 + (t₅ + 1)))), c₃.nreg 388, c₃.nreg 389,
      .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.ifLtN_true (by rw [q380, q387]; exact hs0)
        e₅)))), by omega, by omega, Y1, by omega, Y2,
      fun u hu => ?_, fun a h1 h2 => ?_, by rw [ho₅]; exact ho₃.trans (ho₂.trans ho₁)⟩
    · rw [hd₅ u hu, show c₄.nmem = c₃.nmem from rfl, hm₃, hmj u hu]
      unfold zfv; rw [ite_eq_left hs0]
    · rw [hm₅ a h2, show c₄.nmem = c₃.nmem from rfl, hm₃, M₂ a h1]
  · have e₅ := Exec.loadN (P := P) hw₄ 381 372
    set c₅ : Config := { c₄ with nreg := upd c₄.nreg 381 (c₄.nmem (c₄.nreg 372)) }
    have hw₅ := e₅.wb_right
    have k₅ : ∀ r, r ≠ 381 → c₅.nreg r = c₄.nreg r := fun r h => upd_other _ _ _ h
    have g372 : c₄.nreg 372 = bMj := (k₄ 372 (by omega)).trans ((k₃ 372 (by omega)
      (by omega)).trans ((j 372 (by omega) (by omega)).trans h372))
    have q381 : c₅.nreg 381 = mjv zm 0 := by
      show upd c₄.nreg 381 (c₄.nmem (c₄.nreg 372)) 381 = _
      rw [upd_same, g372, show c₄.nmem = c₃.nmem from rfl, hm₃, ← hmj 0 (by omega), add_zero]
    have hm5 : c₅.nmem = c₃.nmem := rfl
    have r377 : c₅.nreg 377 = 3 := (k₅ 377 (by omega)).trans ((k₄ 377 (by omega)).trans
      ((k₃ 377 (by omega) (by omega)).trans g7))
    -- the face of the chosen triangle
    obtain ⟨y, hy, hyc, c₆, t₆, e₆, ht₆, h369, k₆, hm₆, ho₆⟩ : ∃ y, y < 3 * m ∧
        (y = c₃.nreg 388 ∧ mjv zm 0 = 0 ∨ y = c₃.nreg 389 ∧ mjv zm 0 ≠ 0) ∧ ∃ c₆ t₆,
        Exec P W (.ifLtN 380 381 (.instr (.divN 369 389 377)) (.instr (.divN 369 388 377)))
          c₅ c₆ t₆ ∧ t₆ ≤ 3 ∧ c₆.nreg 369 = y / 3 ∧ (∀ r, r ≠ 369 → c₆.nreg r = c₅.nreg r) ∧
          c₆.nmem = c₅.nmem ∧ c₆.output = c₅.output := by
      by_cases h0 : mjv zm 0 = 0
      · have e₆ := Exec.divN (P := P) hw₅ 369 388 377
        have hn : ¬ c₅.nreg 380 < c₅.nreg 381 := by rw [k₅ 380 (by omega), q380, q381, h0]; omega
        refine ⟨c₃.nreg 388, by omega, Or.inl ⟨rfl, h0⟩, _, _, .ifLtN_false hn e₆, le_rfl, ?_,
          fun r h => upd_other _ _ _ h, rfl, rfl⟩
        show upd c₅.nreg 369 (c₅.nreg 388 / c₅.nreg 377) 369 = _
        rw [upd_same, r377, k₅ 388 (by omega), k₄ 388 (by omega)]
      · have e₆ := Exec.divN (P := P) hw₅ 369 389 377
        have hn : c₅.nreg 380 < c₅.nreg 381 := by rw [k₅ 380 (by omega), q380, q381]; omega
        refine ⟨c₃.nreg 389, by omega, Or.inr ⟨rfl, h0⟩, _, _, .ifLtN_true hn e₆, by omega, ?_,
          fun r h => upd_other _ _ _ h, rfl, rfl⟩
        show upd c₅.nreg 369 (c₅.nreg 389 / c₅.nreg 377) 369 = _
        rw [upd_same, r377, k₅ 389 (by omega), k₄ 389 (by omega)]
    have rr : ∀ r, r ≠ 369 → r ≠ 380 → r ≠ 381 → r ≠ 368 → (r < 380 ∨ 389 < r) →
        c₆.nreg r = c₁.nreg r := fun r a b d f g =>
      (k₆ r a).trans ((k₅ r d).trans ((k₄ r b).trans (k₃ r f g)))
    obtain ⟨c₇, t₇, e₇, ht₇, hd₇, -, hm₇, ho₇⟩ := indLoop_exec (P := P) (W := W) (m := m)
      (bZf := bZf) (t := y / 3) hW.2.2.2 (by omega) c₆ e₆.wb_right h369
      ((rr 370 (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        ((j 370 (by omega) (by omega)).trans h370))
      ((rr 374 (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        ((j 374 (by omega) (by omega)).trans h374))
      ((rr 375 (by omega) (by omega) (by omega) (by omega) (by omega)).trans g5)
    refine ⟨c₇, t₁ + (t₂ + (t₃ + (1 + ((1 + (t₆ + t₇)) + 2)))), c₃.nreg 388, c₃.nreg 389,
      .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.ifLtN_false (by rw [q380, q387]; exact hs0)
        (.seq e₅ (.seq e₆ e₇)))))), by omega, by omega, Y1, by omega, Y2,
      fun u hu => ?_, fun a h1 h2 => ?_, ?_⟩
    · rw [hd₇ u hu]
      unfold zfv
      rw [ite_eq_right hs0]
      rcases hyc with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
      · rw [ite_eq_left h0]
      · rw [ite_eq_right h0]
    · rw [hm₇ a h2, hm₆, hm5, hm₃, M₂ a h1]
    · rw [ho₇, ho₆]; exact ho₃.trans (ho₂.trans ho₁)

/-! ### The marks and the faces of the separator -/

section Link

open Map StDart

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]

lemma zm_val (M : Map D Q) {m : ℕ} (c : D ≃ Fin m) {zm : ℕ → ℕ}
    {Z' : Finset M.stellar.stellar.Face}
    (hzm : ∀ F, zm (M.stellar.stFn (M.stCode c) F) = if F ∈ Z' then 1 else 0)
    (x : StDart D) : zm (M.stCode c x) = if M.stellar.stTri x ∈ Z' then 1 else 0 := by
  rw [← hzm, Map.stFn_stTri]

/-- **The majority marks**: `mjv zm` at the number of a face of the first subdivision is `1`
exactly for the majority faces of the marked triangles `Z'` of the second. -/
theorem mjv_maj (M : Map D Q) {m : ℕ} (c : D ≃ Fin m) {zm : ℕ → ℕ}
    {Z' : Finset M.stellar.stellar.Face}
    (hzm : ∀ F, zm (M.stellar.stFn (M.stCode c) F) = if F ∈ Z' then 1 else 0)
    (f : M.stellar.Face) : mjv zm (M.stFn c f) = if f ∈ maj Z' then 1 else 0 := by
  classical
  obtain ⟨d, rfl⟩ := stTri_surjective f
  rw [stFn_stTri]
  have e0 := zm_val M c hzm (old d)
  have e1 := zm_val M c hzm (up (M.φ d))
  have e2 := zm_val M c hzm (down d)
  simp only [stCode_val, stNum, Equiv.symm_apply_apply] at e0 e1 e2
  have hmaj := face_mem_maj_iff (M := M.stellar) M.stellar_φ_three (Z' := Z') (d := old d)
  rw [stellar_face_old, stellar_φ_old, stellar_φ_up, Equiv.symm_apply_apply] at hmaj
  unfold mjv
  rw [e0, e1, e2]
  by_cases h0 : M.stellar.stTri (old d) ∈ Z' <;> by_cases h1 : M.stellar.stTri (up (M.φ d)) ∈ Z' <;>
    by_cases h2 : M.stellar.stTri (down d) ∈ Z' <;> simp only [h0, h1, h2, ↓reduceIte] <;>
    simp only [h0, h1, h2, and_self, and_true, true_and, or_self, or_true, true_or,
      and_false, false_and, false_or, or_false, iff_true, iff_false] at hmaj <;>
    simp only [hmaj, ↓reduceIte]

/-- **The faces chosen by `sepOut` are `faceSepZ`**: for the marks `zm` of a set `Z'` of
triangles of the second subdivision, the reversals `A₁` of the first, and triangles `y₁` marked
`1` and `y₂` marked `0`, the mark `zfv` of a face of the first subdivision is `1` exactly for the
faces of `faceSepZ Z' t₁ t₂`, `t₁`, `t₂` the darts numbered `y₁`, `y₂`. -/
theorem zfv_faceSepZ (M : Map D Q) (hM : M.IsPlane) {m : ℕ} (c : D ≃ Fin m) (hm : 1 ≤ m)
    {zm A₁ : ℕ → ℕ} {Z' : Finset M.stellar.stellar.Face}
    (hzm : ∀ F, zm (M.stellar.stFn (M.stCode c) F) = if F ∈ Z' then 1 else 0)
    (hA : ∀ x, A₁ (M.stCode c x) = M.stCode c (M.stellar.α x))
    {y₁ y₂ : ℕ} (hy₁ : y₁ < 3 * m) (hy₂ : y₂ < 3 * m) (f : M.stellar.Face) :
    zfv zm (∑ x ∈ range (3 * m), (mjv zm (x / 3) - mjv zm (A₁ x / 3))) y₁ y₂ (M.stFn c f) =
      if f ∈ faceSepZ Z' ((M.stCode c).symm ⟨y₁, hy₁⟩) ((M.stCode c).symm ⟨y₂, hy₂⟩)
      then 1 else 0 := by
  classical
  set c₁ := M.stCode c with hc₁
  have L1 := mjv_maj M c hzm
  -- the faces of the darts by their numbers
  have hface : ∀ x : StDart D, (c₁ x : ℕ) / 3 = M.stFn c (M.stellar.face x) := fun x =>
    (stFn_face M c x).symm
  have hterm : ∀ x : StDart D, mjv zm ((c₁ x : ℕ) / 3) - mjv zm (A₁ (c₁ x) / 3) =
      (if M.stellar.face x ∈ maj Z' then 1 else 0) -
        (if M.stellar.face (M.stellar.α x) ∈ maj Z' then 1 else 0) := fun x => by
    rw [hface, hA, hface, L1, L1]
  have hsum : (0 < ∑ x ∈ range (3 * m), (mjv zm (x / 3) - mjv zm (A₁ x / 3))) ↔
      ∃ d₀, M.stellar.face d₀ ∈ maj Z' ∧ M.stellar.face (M.stellar.α d₀) ∉ maj Z' := by
    rw [Finset.sum_pos_iff]
    constructor
    · rintro ⟨x, hx, hpos⟩
      have hx := mem_range.1 hx
      have e : x = c₁ (c₁.symm ⟨x, hx⟩) := by simp
      rw [e, hterm] at hpos
      refine ⟨c₁.symm ⟨x, hx⟩, ?_⟩
      by_cases h1 : M.stellar.face (c₁.symm ⟨x, hx⟩) ∈ maj Z'
      · by_cases h2 : M.stellar.face (M.stellar.α (c₁.symm ⟨x, hx⟩)) ∈ maj Z'
        · rw [ite_eq_left h1, ite_eq_left h2] at hpos; omega
        · exact ⟨h1, h2⟩
      · rw [ite_eq_right h1] at hpos; omega
    · rintro ⟨d₀, h1, h2⟩
      refine ⟨c₁ d₀, mem_range.2 (c₁ d₀).2, ?_⟩
      rw [hterm, ite_eq_left h1, ite_eq_right h2]; omega
  have hy₁' : (c₁ (c₁.symm ⟨y₁, hy₁⟩) : ℕ) = y₁ := by simp
  have hy₂' : (c₁ (c₁.symm ⟨y₂, hy₂⟩) : ℕ) = y₂ := by simp
  have hsing : ∀ (y : ℕ) (hy : y < 3 * m), ((if M.stFn c f = y / 3 then 1 else 0) : ℕ) =
      if f ∈ ({M.stellar.face (c₁.symm ⟨y, hy⟩)} : Finset _) then 1 else 0 := fun y hy => by
    have := hface (c₁.symm ⟨y, hy⟩)
    simp only [Equiv.apply_symm_apply] at this
    have key : (M.stFn c f : ℕ) = y / 3 ↔ f = M.stellar.face (c₁.symm ⟨y, hy⟩) := by
      rw [this]; exact ⟨fun h' => (M.stFn c).injective (Fin.ext h'), fun h' => by rw [h']⟩
    simp only [mem_singleton]
    exact if_congr key rfl rfl
  unfold zfv faceSepZ
  by_cases hs : ∃ d₀, M.stellar.face d₀ ∈ maj Z' ∧ M.stellar.face (M.stellar.α d₀) ∉ maj Z'
  · rw [ite_eq_left (hsum.2 hs), ite_eq_left hs, L1]
  · rw [ite_eq_right (fun h => hs (hsum.1 h)), ite_eq_right hs]
    push Not at hs
    have hb : ∀ d, bdc (maj Z') d = 0 := fun d => by
      rw [bdc_eq_zero_iff]
      exact ⟨hs d, fun h => by have := hs (M.stellar.α d) h; rwa [M.stellar.α_α] at this⟩
    have h0 : ∀ g : M.stellar.Face, (M.stFn c g : ℕ) = 0 → (mjv zm 0 = 0 ↔ g ∉ maj Z') :=
      fun g hg => by
        have := L1 g; rw [hg] at this; rw [this]; split_ifs with h <;> simp [h]
    obtain ⟨g, hg⟩ : ∃ g : M.stellar.Face, (M.stFn c g : ℕ) = 0 :=
      ⟨(M.stFn c).symm ⟨0, by omega⟩, by simp⟩
    rcases eq_empty_or_univ_of_bdc (isPlane_stellar hM).connected hb with h | h
    · have hm0 : mjv zm 0 = 0 := (h0 g hg).2 (by rw [h]; exact notMem_empty _)
      rw [ite_eq_left hm0, ite_eq_left h, hsing]
    · have hm0 : mjv zm 0 ≠ 0 := fun h' => (h0 g hg).1 h' (by rw [h]; exact mem_univ _)
      have hne : maj Z' ≠ ∅ := by rw [h]; exact (univ_nonempty_iff.2 ⟨g⟩).ne_empty
      rw [ite_eq_right hm0, ite_eq_right hne, hsing]

/-- The darts of the first subdivision weighed by Miller's program: the old darts of the
flagged darts. -/
def flagS (fl : D → ℕ) : Finset (StDart D) := (univ.filter fun d => fl d = 1).image old

lemma sum_wSt (M : Map D Q) {m : ℕ} (c : D ≃ Fin m) (fl : D → ℕ) :
    ∑ x, wSt M c fl x = ∑ d, fl d := by
  rw [Fintype.sum_sum_type]
  simp only [wSt, Sum.elim_inl, sum_const_zero, Sum.elim_inr, zero_add]
  exact Equiv.sum_comp ((M.stFn c).trans c.symm) fl

lemma card_flagS {fl : D → ℕ} (hfl : ∀ d, fl d ≤ 1) : #(flagS fl) = ∑ d, fl d := by
  rw [flagS, card_image_of_injective _ (fun a b h => StDart.old.inj h), card_filter]
  exact sum_congr rfl fun d _ => by have := hfl d; split_ifs <;> omega

/-- **The weights of Miller's program are the dart weights of the recursion**: the normalized
weights `wSt c fl / Σ` on the vertices of the twice subdivided map are the face weights
`wF (wS S)` of the first subdivision for the set `S` of the old darts of the flagged darts. -/
theorem wR_wSt (M : Map D Q) {m : ℕ} (c : D ≃ Fin m) {fl : D → ℕ} (hfl : ∀ d, fl d ≤ 1) :
    wR (wSt M c fl) = wF M.stellar (wS (flagS fl)) := by
  classical
  funext x
  rcases x with v | F
  · simp [wR, wSt, wF]
  · obtain ⟨d, rfl⟩ := stTri_surjective F
    have hS : (∑ u, ((wSt M c fl u : ℕ) : ℝ)) = (#(flagS fl) : ℝ) := by
      rw [card_flagS hfl, ← sum_wSt M c fl]; push_cast; rfl
    simp only [wR, hS, wF, Sum.elim_inr]
    have hset : (({y | M.stellar.face y = M.stTri d} : Finset (StDart D))) =
        {old d, up (M.φ d), down d} := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · exact eq_of_stellar_face
      · rintro (rfl | rfl | rfl)
        · rfl
        · rw [stellar_face_up', Equiv.symm_apply_apply]
        · exact stellar_face_down' d
    rw [show (∑ y with M.stellar.face y = M.stTri d, wS (flagS fl) y) =
        ∑ y ∈ ({old d, up (M.φ d), down d} : Finset (StDart D)), wS (flagS fl) y by
      rw [← hset]]
    rw [sum_insert (by simp), sum_insert (by simp), sum_singleton]
    have hu : up (M.φ d) ∉ flagS fl := by simp [flagS]
    have hd : down d ∉ flagS fl := by simp [flagS]
    have ho : old d ∈ flagS fl ↔ fl d = 1 := by simp [flagS]
    simp only [wS, hu, hd, ↓reduceIte, add_zero, wSt, Sum.elim_inr, stFn_stTri,
      Equiv.symm_apply_apply]
    have := hfl d
    by_cases h : fl d = 1
    · rw [ite_eq_left (ho.2 h), h]; simp
    · rw [ite_eq_right (fun h' => h (ho.1 h')), show fl d = 0 by omega]; simp

end Link

/-! ### The side of every dart from the separator of steps 9–10 -/

section Sep

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]

open Map StDart

set_option maxHeartbeats 4000000 in
open Classical in
/-- **From the separator of the twice subdivided map to the separator of the first
subdivision, on the machine.** Let `C'`, `Z'` be a simple cycle separator of
`M.stellar.stellar` for the weights `wSt c fl` of Miller's program (as steps 9–10 output it, with
at most `6 ⌊√n⌋ + 4` darts), its triangles marked `1` at `bZ` (by their numbers `stFn`), and the
reversals of `M.stellar` at `bA`. Then `sepOut` ends within `105 m + 30` steps with a mark per
face of `M.stellar` at `bZf`, the faces of a set `Z` (`faceSepZ`) bounded by a simple cycle `C`
of `M.stellar` of at most `6 √(3 (nV + nF)) + 4` darts such that, among the flagged darts off
`C`, those inside and those outside number at most `2/3` of them plus `2 C.k` each: the
conclusion of `PlanarSeparator.Map.exists_short_cycle_separator_card` (`card_sep_of`), which is
what the split of the recursion consumes (`PlanarFlow.NegSSSP.exists_cycle_cut`). -/
theorem sepOut_sep (M : Map D Q) {m nV nF : ℕ} (c : D ≃ Fin m) (vn : Q ≃ Fin nV)
    (fn : M.Face ≃ Fin nF) (hm1 : 1 ≤ m) (hM : M.IsPlane) (hl : ∀ d, M.vert (M.α d) ≠ M.vert d)
    {fl : D → ℕ} (hfl : ∀ d, fl d ≤ 1)
    {C' : M.stellar.stellar.SCycle} {Z' : Finset M.stellar.stellar.Face}
    (hk' : C'.k ≤ 6 * Nat.sqrt (nV + nF + m) + 4)
    (hsep' : IsCycleSep C' Z' (sideIn C' Z') (sideOut C' Z'))
    (hin' : ∑ x ∈ sideIn C' Z', wR (wSt M c fl) x ≤ 2 / 3)
    (hout' : ∑ x ∈ sideOut C' Z', wR (wSt M c fl) x ≤ 2 / 3)
    {bZ bMj bA bZf : ℕ}
    (hd : (bMj + m ≤ bZ ∨ bZ + 3 * m ≤ bMj) ∧ (bMj + m ≤ bA ∨ bA + 3 * m ≤ bMj) ∧
      (bMj + m ≤ bZf ∨ bZf + m ≤ bMj) ∧ (bZf + m ≤ bZ ∨ bZ + 3 * m ≤ bZf) ∧
      (bZf + m ≤ bA ∨ bA + 3 * m ≤ bZf))
    (hW : bZ + 3 * m ≤ W ∧ bMj + m ≤ W ∧ bA + 3 * m ≤ W ∧ bZf + m ≤ W)
    (c₀ : Config) (hc : WordsBounded W c₀)
    (h370 : c₀.nreg 370 = m) (h371 : c₀.nreg 371 = bZ) (h372 : c₀.nreg 372 = bMj)
    (h373 : c₀.nreg 373 = bA) (h374 : c₀.nreg 374 = bZf)
    (hzm : ∀ F, c₀.nmem (bZ + M.stellar.stFn (M.stCode c) F) = if F ∈ Z' then 1 else 0)
    (hA₁ : ∀ x, c₀.nmem (bA + M.stCode c x) = M.stCode c (M.stellar.α x)) :
    ∃ c' t, Exec P W sepOut c₀ c' t ∧ t ≤ 105 * m + 30 ∧
      ∃ (C : M.stellar.SCycle) (Z : Finset M.stellar.Face),
        (∀ f, c'.nmem (bZf + M.stFn c f) = if f ∈ Z then 1 else 0) ∧
        C.k ≤ 6 * Nat.sqrt (3 * (nV + nF)) + 4 ∧ IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
        3 * #{d ∈ flagS fl | M.stellar.face d ∈ Z ∧ ¬ C.Mem d} ≤ 2 * #(flagS fl) + 6 * C.k ∧
        3 * #{d ∈ flagS fl | M.stellar.face d ∉ Z ∧ ¬ C.Mem d} ≤ 2 * #(flagS fl) + 6 * C.k ∧
        (∀ a, (a < bMj ∨ bMj + m ≤ a) → (a < bZf ∨ bZf + m ≤ a) → c'.nmem a = c₀.nmem a) ∧
        c'.output = c₀.output := by
  set c₁ := M.stCode c with hc₁
  set zm : ℕ → ℕ := fun y => c₀.nmem (bZ + y) with hzmdef
  have hzm' : ∀ F, zm (M.stellar.stFn c₁ F) = if F ∈ Z' then 1 else 0 := hzm
  have hF : ∀ y (hy : y < 3 * m), ∃ F, (M.stellar.stFn c₁ F : ℕ) = y := fun y hy =>
    ⟨(M.stellar.stFn c₁).symm ⟨y, hy⟩, by simp⟩
  have hz : ∀ y < 3 * m, c₀.nmem (bZ + y) ≤ 1 := fun y hy => by
    obtain ⟨F, rfl⟩ := hF y hy
    rw [hzm]; split_ifs <;> omega
  have hA : ∀ x < 3 * m, c₀.nmem (bA + x) < 3 * m := fun x hx => by
    have e : x = c₁ (c₁.symm ⟨x, hx⟩) := by simp
    rw [e, hA₁]; exact Fin.isLt _
  obtain ⟨c', t, y₁, y₂, e, ht, hy₁, hy₁', hy₂, hy₂', hZf, hm', ho'⟩ :=
    sepOut_exec (P := P) (W := W) hm1 hd hW c₀ hc h370 h371 h372 h373 h374 hz hA
  -- some triangle in `Z'` and some off it
  have hex : (∃ F, F ∈ Z') ∧ ∃ F, F ∉ Z' := by
    have := (hsep'.bd (C'.d 0)).not.2 (not_not.2 (C'.mem_d C'.pos))
    by_cases h : M.stellar.stellar.face (C'.d 0) ∈ Z'
    · exact ⟨⟨_, h⟩, _, fun h' => this (iff_of_true h h')⟩
    · exact ⟨⟨_, by by_contra h'; exact this (iff_of_false h h')⟩, _, h⟩
  obtain ⟨⟨F₁, hF₁⟩, ⟨F₂, hF₂⟩⟩ := hex
  have hz₁ : zm y₁ = 1 := hy₁' ⟨_, (M.stellar.stFn c₁ F₁).2, by
    show zm _ = 1; rw [hzm', ite_eq_left hF₁]⟩
  have hz₂ : zm y₂ = 0 := hy₂' ⟨_, (M.stellar.stFn c₁ F₂).2, by
    show zm _ = 0; rw [hzm', ite_eq_right hF₂]⟩
  set t₁ := c₁.symm ⟨y₁, hy₁⟩
  set t₂ := c₁.symm ⟨y₂, hy₂⟩
  have ht₁ : M.stellar.stTri t₁ ∈ Z' := by
    have := zm_val M c hzm' t₁
    rw [show (c₁ t₁ : ℕ) = y₁ by simp [t₁], hz₁] at this
    by_contra h; rw [ite_eq_right h] at this; omega
  have ht₂ : M.stellar.stTri t₂ ∉ Z' := by
    have := zm_val M c hzm' t₂
    rw [show (c₁ t₂ : ℕ) = y₂ by simp [t₂], hz₂] at this
    intro h; rw [ite_eq_left h] at this; omega
  have hcardP : Fintype.card (Q ⊕ M.Face) = nV + nF := by
    rw [Fintype.card_sum, Fintype.card_congr vn, Fintype.card_congr fn, Fintype.card_fin,
      Fintype.card_fin]
  have hcardF : Fintype.card M.stellar.Face = m := by
    rw [card_stellar_face, Fintype.card_congr c, Fintype.card_fin]
  rw [wR_wSt M c hfl] at hin' hout'
  obtain ⟨C, hk, hsepC, hin, hout⟩ := card_sep_of (isPlane_stellar hM)
    (M.isTriangle_stellar hl) (stellar_loopless hl) (flagS fl) (C' := C') (Z' := Z')
    (by rw [hcardP, hcardF]; exact hk') hsep' hin' hout' ht₁ ht₂
  refine ⟨c', t, e, ht, C, faceSepZ Z' t₁ t₂, fun f => ?_, by rw [hcardP] at hk; exact hk,
    hsepC, hin, hout, hm', ho'⟩
  rw [hZf _ (M.stFn c f).2]
  exact zfv_faceSepZ M hM c hm1 hzm' (A₁ := fun x => c₀.nmem (bA + x)) hA₁ hy₁ hy₂ f

/-- The registers of `sepOut` after steps 1–10: `r370 = m`, the marks at `r394`, the reversals of
the first subdivision at `B₀ + 6 m`, the majority marks at `B₀ + 21 m`, the output at
`B₀ + 22 m` (`r390 = m`, `r393 = B₀` as set for `sepIn`). -/
def soIn : Stmt := block [.copyN 370 390, .copyN 371 394, .constN 380 6, .mulN 381 390 380,
  .addN 373 393 381, .constN 380 21, .mulN 381 390 380, .addN 372 393 381, .addN 374 372 390]

/-- **The separator program with steps 1–10 as a parameter**: the input (`sepIn`), steps 1–10
(`prog`, e.g. `millerA` and steps 9–10 with the marks of the faces of the separator), and the
side of every dart (`sepOut`). -/
def sepRun (prog : Stmt) : Stmt := .seq sepIn (.seq prog (.seq soIn sepOut))

/-- **The specification of steps 1–10 used by `sepRun`**: from any state with the input of
`millerA` written by `sepIn` (`ARegs`, the coded twice subdivided map, the weights `wSt c fl`,
for the `L` of `lgprog`: `log₂ n ≤ L ≤ log₂ n + 1`), `prog` ends within `T` steps, keeps `r390`,
`r393` and the memory from `B₀` on, and leaves at `r394` (below `B₀`) the marks `0`/`1` of the triangles (numbered by `stFn`) of a simple cycle
separator `C'`, `Z'` of the twice subdivided map with at most `6 ⌊√n⌋ + 4` darts and both strict
sides of weight at most `2/3` (the separator of `bandSep`, `SepOK`, with its bound
`2 (l₂ - l₀) + #K₀ + #(T.lvl l₂) ≤ 6 ⌊√n⌋ + 2`). -/
def Spec10 {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]
    (M : Map D Q) {m nV nF : ℕ} (c : D ≃ Fin m) (vn : Q ≃ Fin nV) (fn : M.Face ≃ Fin nF)
    (fl : D → ℕ) (B₀ T : ℕ) (prog : Stmt) (P : Input) (W : ℕ) : Prop :=
  ∀ (c₁ : Config) (L : ℕ), WordsBounded W c₁ →
    Nat.log 2 (nV + nF + m) ≤ L → L ≤ Nat.log 2 (nV + nF + m) + 1 →
    ARegs (aBase (3 * m) (nV + nF + m) L) (3 * m) (nV + nF + m) c₁ →
    (∀ y, c₁.nmem (M.stellar.stCode (M.stCode c) y) =
      M.stellar.stCode (M.stCode c) (M.stellar.stellar.α y)) →
    (∀ y, c₁.nmem (11 * (3 * m) + M.stellar.stCode (M.stCode c) y) =
      M.stellar.stVi (M.stVi vn fn) (M.stFn c) (M.stellar.stellar.vert y)) →
    (∀ x, c₁.nmem ((aBase (3 * m) (nV + nF + m) L).bw +
      M.stellar.stVi (M.stVi vn fn) (M.stFn c) x) = wSt M c fl x) →
    ∃ c₂ t, Exec P W prog c₁ c₂ t ∧ t ≤ T ∧ c₂.nreg 390 = c₁.nreg 390 ∧
      c₂.nreg 393 = c₁.nreg 393 ∧ c₂.nreg 394 + 3 * m ≤ B₀ ∧
      (∀ a, B₀ ≤ a → c₂.nmem a = c₁.nmem a) ∧
      ∃ (C' : M.stellar.stellar.SCycle) (Z' : Finset M.stellar.stellar.Face),
        C'.k ≤ 6 * Nat.sqrt (nV + nF + m) + 4 ∧ IsCycleSep C' Z' (sideIn C' Z') (sideOut C' Z') ∧
        ∑ x ∈ sideIn C' Z', wR (wSt M c fl) x ≤ 2 / 3 ∧
        ∑ x ∈ sideOut C' Z', wR (wSt M c fl) x ≤ 2 / 3 ∧
        ∀ G, c₂.nmem (c₂.nreg 394 + M.stellar.stFn (M.stCode c) G) = if G ∈ Z' then 1 else 0

set_option maxHeartbeats 8000000 in
open Classical in
/-- **The separator of the recursion on the machine, with steps 1–10 as a parameter.** From the
plain encoding of a plane map `M` without loops (`m ≥ 1` darts, `0/1` flags `fl`) at `B₀`, for
any `prog` meeting `Spec10` within `T` steps, `sepRun prog` ends within
`221 m + 5 (nV + nF) + 4 log₂ n + 110 + T + 9 + 105 m + 30` steps with a mark per face of the
first subdivision `M.stellar` at `B₀ + 22 m`, the faces of a set `Z` bounded by a simple cycle
of `M.stellar` with the conclusion of `exists_short_cycle_separator_card` for the old darts of
the flagged darts. -/
theorem sepRun_exec (M : Map D Q) {m nV nF : ℕ} (c : D ≃ Fin m) (vn : Q ≃ Fin nV)
    (fn : M.Face ≃ Fin nF) (fl : D → ℕ) {B₀ T : ℕ} {prog : Stmt} {c₀ : Config} (hm1 : 1 ≤ m)
    (hM : M.IsPlane) (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) (hfl1 : ∀ d, fl d ≤ 1)
    (hE : Enc M c vn fn c₀.nmem B₀ (B₀ + m) (B₀ + 2 * m) (B₀ + 3 * m) (B₀ + 4 * m))
    (hfl : ∀ d, c₀.nmem (B₀ + 5 * m + c d) = fl d)
    (hB : aEnd (3 * m) (nV + nF + m) ≤ B₀) (hW : B₀ + 23 * m + nV + nF + 2 ≤ W)
    (hc : WordsBounded W c₀) (h390 : c₀.nreg 390 = m) (h391 : c₀.nreg 391 = nV)
    (h392 : c₀.nreg 392 = nF) (h393 : c₀.nreg 393 = B₀)
    (hX : Spec10 M c vn fn fl B₀ T prog P W) :
    ∃ c' t, Exec P W (sepRun prog) c₀ c' t ∧
      t ≤ 221 * m + 5 * (nV + nF) + 4 * Nat.log 2 (nV + nF + m) + 110 + T + 9 +
        (105 * m + 30) ∧
      ∃ (C : M.stellar.SCycle) (Z : Finset M.stellar.Face),
        (∀ f, c'.nmem (B₀ + 22 * m + M.stFn c f) = if f ∈ Z then 1 else 0) ∧
        C.k ≤ 6 * Nat.sqrt (3 * (nV + nF)) + 4 ∧ IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
        3 * #{d ∈ flagS fl | M.stellar.face d ∈ Z ∧ ¬ C.Mem d} ≤ 2 * #(flagS fl) + 6 * C.k ∧
        3 * #{d ∈ flagS fl | M.stellar.face d ∉ Z ∧ ¬ C.Mem d} ≤ 2 * #(flagS fl) + 6 * C.k := by
  obtain ⟨c₁, t₁, L, e₁, ht₁, hL1, hL2, hAR, hA, -, hV, hw, hA₁, hr₁, -⟩ :=
    sepIn_exec (P := P) (W := W) M c vn fn fl hm1 hE hfl hB (by omega) hc h390 h391 h392 h393
  obtain ⟨c₂, t₂, e₂, ht₂, g390, g393, hbZ, hm₂, C', Z', hk', hsep', hin', hout', hzm⟩ :=
    hX c₁ L e₁.wb_right hL1 hL2 hAR hA hV hw
  have k390 : c₂.nreg 390 = m := g390.trans ((hr₁ 390 le_rfl (by omega)).trans h390)
  have k393 : c₂.nreg 393 = B₀ := g393.trans ((hr₁ 393 (by omega) (by omega)).trans h393)
  set bZ := c₂.nreg 394 with hbZdef
  have hc₂ := e₂.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, q370, q371, q372, q373, q374, hm₃⟩ : ∃ c₃ t₃,
      Exec P W soIn c₂ c₃ t₃ ∧ t₃ ≤ 9 ∧ c₃.nreg 370 = m ∧ c₃.nreg 371 = bZ ∧
      c₃.nreg 372 = B₀ + 21 * m ∧ c₃.nreg 373 = B₀ + 6 * m ∧ c₃.nreg 374 = B₀ + 22 * m ∧
      c₃.nmem = c₂.nmem := by
    unfold soIn
    exec_block
    all_goals try (show _ ≤ _; config_simp; (try simp only [k390, k393]); omega)
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals (config_simp <;> (try simp only [k390, k393, ← hbZdef]) <;> omega)
  obtain ⟨c', t₄, e₄, ht₄, C, Z, hmk, hk, hsep, hin, hout, -, -⟩ :=
    sepOut_sep (P := P) (W := W) M c vn fn hm1 hM hl hfl1 hk' hsep' hin' hout'
      (bZ := bZ) (bMj := B₀ + 21 * m) (bA := B₀ + 6 * m) (bZf := B₀ + 22 * m) (by omega)
      (by omega) c₃ e₃.wb_right q370 q371 q372 q373 q374 (by rw [hm₃]; exact hzm)
      (fun x => by
        rw [hm₃, hm₂ _ (by have := (M.stCode c x).2; omega)]; exact hA₁ x)
  exact ⟨c', t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, C, Z, hmk, hk,
    hsep, hin, hout⟩

end Sep

end MillerProg

end PlanarSeparator
