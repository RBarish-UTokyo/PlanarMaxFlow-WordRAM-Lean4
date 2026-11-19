module

public import PlanarSeparator.Machine.MillerBand
public import PlanarSeparator.Machine.MillerRoot

/-!
# Miller's separator on the machine: the darts of a fundamental cycle

For the outputs of steps 9 and 10 (`PlanarSeparator.Map.bandSep`: in the band case the fundamental
cycle of the dart `δ` of step 8 in `T₁`, for a rerouting option the fundamental cycle of the last
dart of an arc in the redirected tree), the darts `fd T δ i`, `i < ck T δ`, of the fundamental
cycle `PlanarSeparator.Map.SpTree.fcycle` of a dart `δ` in a tree given by its parent darts `Pr`
(the parent of `v` is `upN A V Pr r₀ v`). The program `fcProg` has four passes, each with `n`
(or `ct`) iterations:

* `fmark`: the ancestors of the tail `x = V δ` get the stamp `s` in the marks at `bMk`;
* `fwalkZ`: from the head `z = V (A δ)` up to the first marked vertex (the lowest common
  ancestor), writing `δ` and the parent darts at `bFc`, and their number `cs` (`r512`);
* `fwalkX`: from `x` up to the lowest common ancestor, writing the parent darts at `bTmp`, and
  their number `ct` (`r513`);
* `frev`: the reversals of these darts, in the reverse order, after the first `1 + cs` darts,
  and `ck = 1 + cs + ct` (`r514`).

`fcProg_exec`: within `77 n + 26` steps; `fcProg_fcycle`: through the coding, the darts at `bFc + i`,
`i < ck`, are the codes of `fd T δ i` and `r514 = ck T δ`.

Registers: inputs `r500 = δ`, `r501 = bA`, `r502 = bV`, `r503 = bPr`, `r504 = r₀`, `r505 = n`,
`r506 = bMk`, `r507 = s`, `r508 = bFc`, `r509 = bTmp`, `r510 = 0`, `r511 = 1` (`FR`); the passes
write `r512 … r520`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The programs -/

/-- The parent `V (A (Pr v))` of `r516 = v`, in `r516` (scratch `r517`). -/
def fup : List Instr :=
  [.addN 517 503 516, .loadN 517 517, .addN 517 501 517, .loadN 517 517, .addN 517 502 517,
    .loadN 516 517]

/-- **One step of the marks**: stamp `r516 = v`, then move to its parent unless it is the root. -/
def fmBody : Stmt :=
  .seq (block [.subN 519 516 504, .subN 518 504 516, .addN 519 519 518, .copyN 518 516])
    (.seq (.ifLtN 519 511 .skip (block fup))
      (block [.addN 517 506 518, .storeN 517 507, .addN 515 515 511]))

/-- **The marks of the ancestors of the tail of `δ`.** -/
def fmark : Stmt :=
  .seq (block [.addN 517 502 500, .loadN 516 517, .copyN 515 510]) (.whileLtN 515 505 fmBody)

/-- **One step from the head**: unless `r516` is marked, record its parent dart and move up. -/
def fzBody : Stmt :=
  .seq (block [.addN 517 506 516, .loadN 518 517, .subN 519 518 507, .subN 517 507 518,
      .addN 519 519 517])
    (.seq (.ifLtN 519 511 .skip (block ([.addN 518 503 516, .loadN 518 518] ++ fup ++
        [.addN 517 508 512, .addN 517 517 511, .storeN 517 518, .addN 512 512 511])))
      (.instr (.addN 515 515 511)))

/-- **From the head to the lowest common ancestor.** -/
def fwalkZ : Stmt :=
  .seq (block [.addN 517 501 500, .loadN 517 517, .addN 517 502 517, .loadN 516 517,
      .storeN 508 500, .copyN 512 510, .copyN 515 510])
    (.whileLtN 515 505 fzBody)

/-- **One step from the tail**: unless `r516` is the ancestor `r520`, record its parent dart. -/
def fxBody : Stmt :=
  .seq (block [.subN 519 516 520, .subN 517 520 516, .addN 519 519 517])
    (.seq (.ifLtN 519 511 .skip (block ([.addN 518 503 516, .loadN 518 518] ++ fup ++
        [.addN 517 509 513, .storeN 517 518, .addN 513 513 511])))
      (.instr (.addN 515 515 511)))

/-- **From the tail to the lowest common ancestor.** -/
def fwalkX : Stmt :=
  .seq (block [.copyN 520 516, .addN 517 502 500, .loadN 516 517, .copyN 513 510,
      .copyN 515 510])
    (.whileLtN 515 505 fxBody)

/-- **One reversed dart** `r515 = j`: `bFc + 1 + cs + j := A (bTmp + ct - 1 - j)`. -/
def frBody : List Instr :=
  [.subN 517 513 515, .subN 517 517 511, .addN 517 509 517, .loadN 518 517, .addN 518 501 518,
    .loadN 518 518, .addN 517 508 512, .addN 517 517 511, .addN 517 517 515, .storeN 517 518,
    .addN 515 515 511]

/-- **The darts from the lowest common ancestor down to the tail**, and `ck` in `r514`. -/
def frev : Stmt :=
  .seq (block [.copyN 515 510, .addN 514 512 513, .addN 514 514 511])
    (.whileLtN 515 513 (block frBody))

/-- **The darts of the fundamental cycle of `δ`.** -/
def fcProg : Stmt := .seq fmark (.seq fwalkZ (.seq fwalkX frev))

/-- The input registers of `fcProg`. -/
structure FR (δ bA bV bPr r₀ n bMk s bFc bTmp : ℕ) (c : Config) : Prop where
  r500 : c.nreg 500 = δ
  r501 : c.nreg 501 = bA
  r502 : c.nreg 502 = bV
  r503 : c.nreg 503 = bPr
  r504 : c.nreg 504 = r₀
  r505 : c.nreg 505 = n
  r506 : c.nreg 506 = bMk
  r507 : c.nreg 507 = s
  r508 : c.nreg 508 = bFc
  r509 : c.nreg 509 = bTmp
  r510 : c.nreg 510 = 0
  r511 : c.nreg 511 = 1

theorem FR.of {δ bA bV bPr r₀ n bMk s bFc bTmp : ℕ} {c c' : Config}
    (h : FR δ bA bV bPr r₀ n bMk s bFc bTmp c)
    (e : ∀ r, 500 ≤ r → r < 512 → c'.nreg r = c.nreg r) : FR δ bA bV bPr r₀ n bMk s bFc bTmp c' :=
  ⟨(e _ (by omega) (by omega)).trans h.r500, (e _ (by omega) (by omega)).trans h.r501,
    (e _ (by omega) (by omega)).trans h.r502, (e _ (by omega) (by omega)).trans h.r503,
    (e _ (by omega) (by omega)).trans h.r504, (e _ (by omega) (by omega)).trans h.r505,
    (e _ (by omega) (by omega)).trans h.r506, (e _ (by omega) (by omega)).trans h.r507,
    (e _ (by omega) (by omega)).trans h.r508, (e _ (by omega) (by omega)).trans h.r509,
    (e _ (by omega) (by omega)).trans h.r510, (e _ (by omega) (by omega)).trans h.r511⟩

/-- The layout of `fcProg`: the arrays read lie below the marks, then the temporary array and
the output. -/
def FLay (k n bA bV bPr bMk bTmp bFc W : ℕ) : Prop :=
  bA + 3 * k ≤ bMk ∧ bV + 3 * k ≤ bMk ∧ bPr + n ≤ bMk ∧ bMk + n ≤ bTmp ∧ bTmp + n ≤ bFc ∧
    bFc + 2 * n + 1 ≤ W

lemma iter_up_lt {k n r₀ : ℕ} {A V Pr : ℕ → ℕ} (hin : RootIn k n r₀ A V Pr) {x : ℕ}
    (hx : x < n) (i : ℕ) : (upN A V Pr r₀)^[i] x < n := by
  induction i with
  | zero => exact hx
  | succ i ih => rw [Function.iterate_succ_apply']; exact hin.up_lt ih

section proofs

variable {k : ℕ} {W : ℕ} {P : Input} {δ bA bV bPr r₀ n bMk s bFc bTmp : ℕ} {A V Pr : ℕ → ℕ}


set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- The parent of `r516`. -/
theorem fup_exec {v p a b : ℕ} (c : Config) (hc : WordsBounded W c) (h501 : c.nreg 501 = bA)
    (h502 : c.nreg 502 = bV) (h503 : c.nreg 503 = bPr) (h516 : c.nreg 516 = v)
    (m1 : c.nmem (bPr + v) = p) (m2 : c.nmem (bA + p) = a) (m3 : c.nmem (bV + a) = b)
    (hb : bPr + v ≤ W ∧ bA + p ≤ W ∧ bV + a ≤ W) :
    ∃ c' t, Exec P W (block fup) c c' t ∧ t ≤ 6 ∧
      (c'.nreg 516 = b ∧ (∀ r, r ≠ 516 → r ≠ 517 → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.output = c.output) := by
  unfold fup
  exec_block
  all_goals try (config_simp; (try simp only [h503, h516, m1, h501, m2, h502, m3]); omega)
  rename_i hwb
  simp only [h503, h516, m1, h501, m2, h502, m3] at hwb ⊢
  refine ⟨by omega, by config_simp, fun r h1 h2 => ?_, by config_simp, by config_simp⟩
  config_simp; simp only [upd_apply]; split_ifs <;> omega

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The marks of the ancestors of the tail.** -/
theorem fmark_exec (hlay : FLay k n bA bV bPr bMk bTmp bFc W) (c : Config)
    (hc : WordsBounded W c) (hF : FR δ bA bV bPr r₀ n bMk s bFc bTmp c)
    (hin : RootIn k n r₀ A V Pr) (hδ : δ < 3 * k)
    (mA : ∀ x < 3 * k, c.nmem (bA + x) = A x) (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x)
    (mP : ∀ v < n, v ≠ r₀ → c.nmem (bPr + v) = Pr v) :
    ∃ c' t, Exec P W fmark c c' t ∧ t ≤ 18 * n + 5 ∧
      (∀ v < n, (∃ i < n, (upN A V Pr r₀)^[i] (V δ) = v) → c'.nmem (bMk + v) = s) ∧
      (∀ v < n, (¬ ∃ i < n, (upN A V Pr r₀)^[i] (V δ) = v) →
        c'.nmem (bMk + v) = c.nmem (bMk + v)) ∧
      (∀ a, a < bMk ∨ bMk + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 515 ∨ 520 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hlay
  obtain ⟨r500, r501, r502, r503, r504, r505, r506, r507, -, -, r510, r511⟩ := hF
  set f := upN A V Pr r₀ with hf
  set x := V δ with hx
  have hxn : x < n := hin.V_lt _ hδ
  have hlt : ∀ i, f^[i] x < n := iter_up_lt hin hxn
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 515 = i ∧
    c'.nreg 505 = n ∧ i ≤ n ∧ c'.nreg 516 = f^[i] x ∧
    (∀ v < n, (∃ j < i, f^[j] x = v) → c'.nmem (bMk + v) = s) ∧
    (∀ v < n, (¬ ∃ j < i, f^[j] x = v) → c'.nmem (bMk + v) = c.nmem (bMk + v)) ∧
    (∀ a, a < bMk ∨ bMk + n ≤ a → c'.nmem a = c.nmem a) ∧
    (∀ r, r < 515 ∨ 520 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.addN 517 502 500, .loadN 516 517,
      .copyN 515 510]) c c₁ k₁ ∧ I 0 c₁ ∧ k₁ = 3 := by
    exec_block
    · rw [r502, r500]; omega
    refine ⟨⟨‹_›, by config_simp; exact r510, by config_simp; exact r505, by omega,
      by config_simp; rw [r502, r500, mV _ hδ]; rfl,
      fun v _ ⟨j, hj, _⟩ => absurd hj (by omega), fun v _ _ => rfl, fun a _ => rfl,
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl⟩, rfl⟩
  obtain ⟨c₂, t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 515) (rN := 505)
    (N := n) (lo := 0) (B := 16) (body := fmBody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h515, h505, hin', h516, hM1, hM2, hf₁, hr, ho⟩ hi => by
      have g : ∀ r, r < 515 → c₁.nreg r = c.nreg r := fun r hr' => hr r (Or.inl hr')
      have g501 : c₁.nreg 501 = bA := by rw [g 501 (by omega)]; exact r501
      have g502 : c₁.nreg 502 = bV := by rw [g 502 (by omega)]; exact r502
      have g503 : c₁.nreg 503 = bPr := by rw [g 503 (by omega)]; exact r503
      have g504 : c₁.nreg 504 = r₀ := by rw [g 504 (by omega)]; exact r504
      have g506 : c₁.nreg 506 = bMk := by rw [g 506 (by omega)]; exact r506
      have g507 : c₁.nreg 507 = s := by rw [g 507 (by omega)]; exact r507
      have g511 : c₁.nreg 511 = 1 := by rw [g 511 (by omega)]; exact r511
      set v := f^[i] x with hv
      have hvn : v < n := hlt i
      have hnext : f^[i + 1] x = f v := Function.iterate_succ_apply' _ _ _
      have hb1 := hw₁.1 516
      have hb2 := hw₁.1 504
      -- the last block, from the state after the move
      have hfin : ∀ c₃ : Config, WordsBounded W c₃ → c₃.nreg 518 = v → c₃.nreg 516 = f v →
          c₃.nreg 515 = i → (∀ r, r < 515 ∨ 520 ≤ r → c₃.nreg r = c₁.nreg r) →
          c₃.nmem = c₁.nmem → c₃.output = c₁.output →
          ∃ c' k, Exec P W (block [.addN 517 506 518, .storeN 517 507, .addN 515 515 511]) c₃
            c' k ∧ I (i + 1) c' ∧ k ≤ 3 := by
        intro c₃ hw₃ f518 f516 f515 fr fm fo
        have f506 : c₃.nreg 506 = bMk := (fr 506 (by omega)).trans g506
        have f507 : c₃.nreg 507 = s := (fr 507 (by omega)).trans g507
        have f511 : c₃.nreg 511 = 1 := (fr 511 (by omega)).trans g511
        have f505 : c₃.nreg 505 = n := (fr 505 (by omega)).trans h505
        exec_block
        all_goals try (config_simp; (try simp only [f506, f518, f515, f511]); omega)
        rename_i hwb
        simp only [f506, f518, f507, f515, f511] at hwb ⊢
        refine ⟨⟨hwb, by config_simp, by config_simp; exact f505, by omega,
          by config_simp; rw [f516, hnext], fun u hu hex => ?_, fun u hu hn => ?_,
          fun a ha => ?_, fun r hr' => ?_, by config_simp; rw [fo, ho]⟩, by omega⟩
        · config_simp
          by_cases hvu : u = v
          · rw [hvu, upd_same]
          · rw [upd_other _ _ _ (by omega), fm]
            obtain ⟨j, hj, hju⟩ := hex
            refine hM1 u hu ⟨j, ?_, hju⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
            · exact hj
            · exact absurd hju.symm hvu
        · config_simp
          have hvu : u ≠ v := fun e => hn ⟨i, by omega, e.symm⟩
          rw [upd_other _ _ _ (by omega), fm]
          exact hM2 u hu fun ⟨j, hj, e⟩ => hn ⟨j, by omega, e⟩
        · config_simp
          rw [upd_other _ _ _ (by omega), fm]; exact hf₁ a ha
        · config_simp; simp only [upd_apply]
          split_ifs <;> first | omega | (rw [fr r hr']; exact hr r hr')
      unfold fmBody
      refine spec_seq ?_
      exec_block
      · config_simp; rw [h516, g504]; omega
      rename_i hwa
      simp only [h516, g504] at hwa ⊢
      refine spec_seq ?_
      by_cases hroot : v = r₀
      · have hfv : f v = v := by
          rw [hf, upN, ite_eq_left_of_eq_true _ _ (eq_true hroot)]; exact hroot.symm
        refine spec_ifLtN_true (by config_simp; rw [g511]; omega) ?_
        refine spec_skip hwa ?_
        obtain ⟨c', k', e', hI', hk'⟩ := hfin _ hwa (by config_simp <;> exact h516)
          (by config_simp; rw [hfv]; exact h516) (by config_simp <;> exact h515)
          (fun r hr' => by config_simp; simp only [upd_apply]; split_ifs <;> omega)
          (by config_simp) (by config_simp)
        exact ⟨c', k', e', hI', by omega⟩
      · have hpv := hin.Pr_lt v hvn hroot
        have hav := hin.A_lt _ hpv
        have m1 : c₁.nmem (bPr + v) = Pr v := by rw [hf₁ _ (Or.inl (by omega))]; exact mP v hvn hroot
        have m2 : c₁.nmem (bA + Pr v) = A (Pr v) := by rw [hf₁ _ (Or.inl (by omega))]; exact mA _ hpv
        have m3 : c₁.nmem (bV + A (Pr v)) = V (A (Pr v)) := by
          rw [hf₁ _ (Or.inl (by omega))]; exact mV _ hav
        have hfv : f v = V (A (Pr v)) := by
          rw [hf, upN, ite_eq_right_of_eq_false _ _ (eq_false hroot)]; rfl
        refine spec_ifLtN_false (by config_simp; rw [g511]; omega) ?_
        refine spec_use (fup_exec _ hwa (by config_simp <;> exact g501)
          (by config_simp <;> exact g502) (by config_simp <;> exact g503)
          (by config_simp <;> exact h516) (by config_simp <;> exact m1) (by config_simp <;> exact m2)
          (by config_simp <;> exact m3) ⟨by omega, by omega, by omega⟩) ?_
        intro c₃ k₃ hk₃ hw₃ ⟨f516, fr, fm, fo⟩
        obtain ⟨c', k', e', hI', hk'⟩ := hfin c₃ hw₃
          (by rw [fr 518 (by omega) (by omega)]; config_simp <;> exact h516)
          (by rw [f516]; exact hfv.symm)
          (by rw [fr 515 (by omega) (by omega)]; config_simp <;> exact h515)
          (fun r hr' => by
            by_cases h1 : r = 516
            · omega
            by_cases h2 : r = 517
            · omega
            rw [fr r h1 h2]; config_simp; simp only [upd_apply]; split_ifs <;> omega)
          (by rw [fm]) (by rw [fo])
        exact ⟨c', k', e', hI', by omega⟩)
    (by omega) hI₁
  obtain ⟨-, -, -, -, -, hM1', hM2', hf', hr', ho'⟩ := hI
  exact ⟨c₂, 3 + t, .seq e₁ e, by omega, hM1', hM2', hf', hr', ho'⟩

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **From the head to the first marked vertex.** If the first `c₀` vertices of the root path of
`z = V (A δ)` are unmarked (and not the root) and the next one is marked, then `fwalkZ` writes
`δ` and their parent darts at `bFc`, and `r512 = c₀`, `r516` is that marked vertex. -/
theorem fwalkZ_exec (hlay : FLay k n bA bV bPr bMk bTmp bFc W) (c : Config)
    (hc : WordsBounded W c) (hF : FR δ bA bV bPr r₀ n bMk s bFc bTmp c)
    (hin : RootIn k n r₀ A V Pr) (hδ : δ < 3 * k)
    (mA : ∀ x < 3 * k, c.nmem (bA + x) = A x) (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x)
    (mP : ∀ v < n, v ≠ r₀ → c.nmem (bPr + v) = Pr v) {c₀ : ℕ} (hc₀ : c₀ ≤ n)
    (hz : ∀ j < c₀, c.nmem (bMk + (upN A V Pr r₀)^[j] (V (A δ))) ≠ s ∧
      (upN A V Pr r₀)^[j] (V (A δ)) ≠ r₀)
    (hz' : c.nmem (bMk + (upN A V Pr r₀)^[c₀] (V (A δ))) = s) :
    ∃ c' t, Exec P W fwalkZ c c' t ∧ t ≤ 25 * n + 9 ∧ c'.nreg 512 = c₀ ∧
      c'.nreg 516 = (upN A V Pr r₀)^[c₀] (V (A δ)) ∧ c'.nmem bFc = δ ∧
      (∀ j < c₀, c'.nmem (bFc + 1 + j) = Pr ((upN A V Pr r₀)^[j] (V (A δ)))) ∧
      (∀ a, a < bFc ∨ bFc + 2 * n + 1 ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 512 → r < 515 ∨ 520 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hlay
  obtain ⟨r500, r501, r502, r503, r504, r505, r506, r507, r508, -, r510, r511⟩ := hF
  set f := upN A V Pr r₀ with hf
  set z := V (A δ) with hzdef
  have hAδ := hin.A_lt _ hδ
  have hzn : z < n := hin.V_lt _ hAδ
  have hlt : ∀ i, f^[i] z < n := iter_up_lt hin hzn
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 515 = i ∧
    c'.nreg 505 = n ∧ i ≤ n ∧ c'.nreg 512 = min i c₀ ∧ c'.nreg 516 = f^[min i c₀] z ∧
    c'.nmem bFc = δ ∧ (∀ j < min i c₀, c'.nmem (bFc + 1 + j) = Pr (f^[j] z)) ∧
    (∀ a, a < bFc ∨ bFc + 2 * n + 1 ≤ a → c'.nmem a = c.nmem a) ∧
    (∀ r, r ≠ 512 → r < 515 ∨ 520 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.addN 517 501 500, .loadN 517 517,
      .addN 517 502 517, .loadN 516 517, .storeN 508 500, .copyN 512 510, .copyN 515 510])
      c c₁ k₁ ∧ I 0 c₁ ∧ k₁ = 7 := by
    have m1 : c.nmem (bA + δ) = A δ := mA δ hδ
    have m2 : c.nmem (bV + A δ) = V (A δ) := mV _ hAδ
    exec_block
    all_goals try (config_simp; (try simp only [r501, r500, m1, r502, m2]); omega)
    rename_i hwb
    simp only [r501, r500, m1, r502, m2, r508, r510] at hwb ⊢
    refine ⟨⟨hwb, by config_simp, by config_simp; exact r505, by omega, by config_simp; omega,
      by config_simp; rw [Nat.zero_min]; rfl, by config_simp, fun j hj => absurd hj (by omega),
      fun a ha => by config_simp; rw [upd_other _ _ _ (by omega)],
      fun r h1 h2 => by config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl⟩,
      by first | rfl | trivial⟩
  obtain ⟨c₂, t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 515) (rN := 505)
    (N := n) (lo := 0) (B := 23) (body := fzBody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h515, h505, hin', h512, h516, h0, hout, hf₁, hr, ho⟩ hi => by
      have g : ∀ r, r < 512 → c₁.nreg r = c.nreg r := fun r hr' => hr r (by omega) (by omega)
      have g501 : c₁.nreg 501 = bA := by rw [g 501 (by omega)]; exact r501
      have g502 : c₁.nreg 502 = bV := by rw [g 502 (by omega)]; exact r502
      have g503 : c₁.nreg 503 = bPr := by rw [g 503 (by omega)]; exact r503
      have g506 : c₁.nreg 506 = bMk := by rw [g 506 (by omega)]; exact r506
      have g507 : c₁.nreg 507 = s := by rw [g 507 (by omega)]; exact r507
      have g508 : c₁.nreg 508 = bFc := by rw [g 508 (by omega)]; exact r508
      have g511 : c₁.nreg 511 = 1 := by rw [g 511 (by omega)]; exact r511
      set m := min i c₀ with hm
      set v := f^[m] z with hv
      have hvn : v < n := hlt m
      have mk : c₁.nmem (bMk + v) = c.nmem (bMk + v) := hf₁ _ (Or.inl (by omega))
      have hbm := hw₁.2 (bMk + v)
      have hbs := hw₁.1 507
      have hstep : ∀ c₃ : Config, WordsBounded W c₃ → c₃.nreg 515 = i →
          (∀ r, r ≠ 512 → r < 515 ∨ 520 ≤ r → c₃.nreg r = c.nreg r) →
          c₃.nreg 512 = min (i + 1) c₀ → c₃.nreg 516 = f^[min (i + 1) c₀] z →
          c₃.nmem bFc = δ → (∀ j < min (i + 1) c₀, c₃.nmem (bFc + 1 + j) = Pr (f^[j] z)) →
          (∀ a, a < bFc ∨ bFc + 2 * n + 1 ≤ a → c₃.nmem a = c.nmem a) →
          c₃.output = c.output →
          ∃ c' k, Exec P W (.instr (.addN 515 515 511)) c₃ c' k ∧ I (i + 1) c' ∧ k ≤ 1 := by
        intro c₃ hw₃ e515 er e512 e516 e0 eout ef eo
        have e511 : c₃.nreg 511 = 1 := (er 511 (by omega) (by omega)).trans r511
        have e505 : c₃.nreg 505 = n := (er 505 (by omega) (by omega)).trans r505
        have ea := Exec.addN (P := P) hw₃ 515 515 511 (by rw [e515, e511]; omega)
        refine ⟨_, 1, ea, ⟨ea.wb_right, by config_simp; rw [e515, e511],
          by config_simp; exact e505, by omega, by config_simp; exact e512,
          by config_simp; exact e516, by config_simp; exact e0, by config_simp; exact eout,
          by config_simp; exact ef, fun r h1 h2 => ?_, by config_simp; exact eo⟩, le_rfl⟩
        config_simp; simp only [upd_apply]
        split_ifs with h'
        · omega
        · exact er r h1 h2
      unfold fzBody
      refine spec_seq ?_
      exec_block
      · config_simp; rw [g506, h516]; omega
      · config_simp; simp only [g506, h516, mk, g507]
        have := hw₁.2 (bMk + v); rw [mk] at this; omega
      rename_i hwa
      simp only [g506, h516, mk, g507] at hwa ⊢
      refine spec_seq ?_
      by_cases hic : i < c₀
      · have e1 : m = i := by omega
        have e2 : min (i + 1) c₀ = i + 1 := by omega
        obtain ⟨hnm, hnr⟩ := hz i hic
        rw [e1] at hv
        have hvr : v ≠ r₀ := by rw [hv]; exact hnr
        have hpv := hin.Pr_lt v hvn hvr
        have hav := hin.A_lt _ hpv
        have m1 : c₁.nmem (bPr + v) = Pr v := by rw [hf₁ _ (Or.inl (by omega))]; exact mP v hvn hvr
        have m2 : c₁.nmem (bA + Pr v) = A (Pr v) := by
          rw [hf₁ _ (Or.inl (by omega))]; exact mA _ hpv
        have m3 : c₁.nmem (bV + A (Pr v)) = V (A (Pr v)) := by
          rw [hf₁ _ (Or.inl (by omega))]; exact mV _ hav
        have hfv : f v = V (A (Pr v)) := by
          rw [hf, upN, ite_eq_right_of_eq_false _ _ (eq_false hvr)]; rfl
        have hnext : f^[i + 1] z = f v := by rw [Function.iterate_succ_apply', ← hv]
        refine spec_ifLtN_false (by
          config_simp; rw [g511]
          have : c.nmem (bMk + v) ≠ s := by rw [hv]; exact hnm
          omega) ?_
        unfold fup
        simp only [List.cons_append, List.nil_append]
        exec_block
        all_goals try (config_simp; (try simp only [g503, h516, m1, g501, m2, g502, m3, g508,
          h512, g511]); omega)
        rename_i hwd
        simp only [g503, h516, m1, g501, m2, g502, m3, g508, h512, g511] at hwd ⊢
        obtain ⟨c', k', e', hI', hk'⟩ := hstep _ hwd (by config_simp; exact h515)
          (fun r h1 h2 => by
            config_simp; simp only [upd_apply]
            split_ifs <;> first | omega | exact hr r h1 h2)
          (by config_simp; rw [e1, e2])
          (by config_simp; rw [e2, hnext, hfv])
          (by config_simp; rw [upd_other _ _ _ (by omega)]; exact h0)
          (fun j hj => by
            config_simp
            rcases Nat.lt_or_ge j i with hj' | hj'
            · rw [upd_other _ _ _ (by omega)]; exact hout j (by omega)
            · obtain rfl : j = i := by omega
              rw [show bFc + 1 + j = bFc + j + 1 by omega, e1, upd_same, hv])
          (fun a ha => by config_simp; rw [upd_other _ _ _ (by omega)]; exact hf₁ a ha)
          (by config_simp; exact ho)
        exact ⟨c', k', e', hI', by omega⟩
      · have e1 : m = c₀ := by omega
        have e2 : min (i + 1) c₀ = c₀ := by omega
        rw [e1] at hv
        refine spec_ifLtN_true (by
          config_simp; rw [g511]
          have : c.nmem (bMk + v) = s := by rw [hv]; exact hz'
          omega) ?_
        refine spec_skip hwa ?_
        obtain ⟨c', k', e', hI', hk'⟩ := hstep _ hwa (by config_simp <;> exact h515)
          (fun r h1 h2 => by
            config_simp; simp only [upd_apply]
            split_ifs <;> first | omega | exact hr r h1 h2)
          (by config_simp; rw [h512, e1, e2])
          (by config_simp; rw [h516, e2, ← e1])
          (by config_simp <;> exact h0)
          (fun j hj => by config_simp; exact hout j (by omega))
          (fun a ha => by config_simp; exact hf₁ a ha) (by config_simp <;> exact ho)
        exact ⟨c', k', e', hI', by omega⟩)
    (by omega) hI₁
  obtain ⟨-, -, -, -, h512', h516', h0', hout', hf', hr', ho'⟩ := hI
  have hmn : min n c₀ = c₀ := by omega
  rw [hmn] at h512' h516' hout'
  exact ⟨c₂, 7 + t, .seq e₁ e, by omega, h512', h516', h0', hout', hf', hr', ho'⟩

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **From the tail to the lowest common ancestor** `r516 = lca`: if the first `d₀` vertices of the
root path of `x = V δ` are not `lca` (nor the root) and the next one is, then `fwalkX` writes their
parent darts at `bTmp`, and `r513 = d₀`. -/
theorem fwalkX_exec (hlay : FLay k n bA bV bPr bMk bTmp bFc W) (c : Config)
    (hc : WordsBounded W c) (hF : FR δ bA bV bPr r₀ n bMk s bFc bTmp c)
    (hin : RootIn k n r₀ A V Pr) (hδ : δ < 3 * k) {lca : ℕ} (h516 : c.nreg 516 = lca)
    (mA : ∀ x < 3 * k, c.nmem (bA + x) = A x) (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x)
    (mP : ∀ v < n, v ≠ r₀ → c.nmem (bPr + v) = Pr v) {d₀ : ℕ} (hd₀ : d₀ ≤ n)
    (hx : ∀ j < d₀, (upN A V Pr r₀)^[j] (V δ) ≠ lca ∧ (upN A V Pr r₀)^[j] (V δ) ≠ r₀)
    (hx' : (upN A V Pr r₀)^[d₀] (V δ) = lca) :
    ∃ c' t, Exec P W fwalkX c c' t ∧ t ≤ 21 * n + 7 ∧ c'.nreg 513 = d₀ ∧
      (∀ j < d₀, c'.nmem (bTmp + j) = Pr ((upN A V Pr r₀)^[j] (V δ))) ∧
      (∀ a, a < bTmp ∨ bTmp + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 513 → r < 515 ∨ 521 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hlay
  obtain ⟨r500, r501, r502, r503, r504, r505, r506, r507, r508, r509, r510, r511⟩ := hF
  set f := upN A V Pr r₀ with hf
  set x := V δ with hxdef
  have hxn : x < n := hin.V_lt _ hδ
  have hlt : ∀ i, f^[i] x < n := iter_up_lt hin hxn
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 515 = i ∧
    c'.nreg 505 = n ∧ i ≤ n ∧ c'.nreg 513 = min i d₀ ∧ c'.nreg 516 = f^[min i d₀] x ∧
    c'.nreg 520 = lca ∧ (∀ j < min i d₀, c'.nmem (bTmp + j) = Pr (f^[j] x)) ∧
    (∀ a, a < bTmp ∨ bTmp + n ≤ a → c'.nmem a = c.nmem a) ∧
    (∀ r, r ≠ 513 → r < 515 ∨ 521 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 520 516, .addN 517 502 500,
      .loadN 516 517, .copyN 513 510, .copyN 515 510]) c c₁ k₁ ∧ I 0 c₁ ∧ k₁ = 5 := by
    have m1 : c.nmem (bV + δ) = V δ := mV δ hδ
    exec_block
    all_goals try (config_simp; (try simp only [r502, r500, m1]); omega)
    rename_i hwb
    simp only [r502, r500, m1, r510, h516] at hwb ⊢
    refine ⟨⟨hwb, by config_simp, by config_simp; exact r505, by omega, by config_simp; omega,
      by config_simp; rw [Nat.zero_min]; rfl, by config_simp, fun j hj => absurd hj (by omega),
      fun a ha => rfl,
      fun r h1 h2 => by config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl⟩,
      by first | rfl | trivial⟩
  obtain ⟨c₂, t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 515) (rN := 505)
    (N := n) (lo := 0) (B := 19) (body := fxBody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h515, h505, hin', h513, h516', h520, hout, hf₁, hr, ho⟩ hi => by
      have g : ∀ r, r < 513 → c₁.nreg r = c.nreg r := fun r hr' => hr r (by omega) (by omega)
      have g501 : c₁.nreg 501 = bA := by rw [g 501 (by omega)]; exact r501
      have g502 : c₁.nreg 502 = bV := by rw [g 502 (by omega)]; exact r502
      have g503 : c₁.nreg 503 = bPr := by rw [g 503 (by omega)]; exact r503
      have g509 : c₁.nreg 509 = bTmp := by rw [g 509 (by omega)]; exact r509
      have g511 : c₁.nreg 511 = 1 := by rw [g 511 (by omega)]; exact r511
      set m := min i d₀ with hm
      set v := f^[m] x with hv
      have hvn : v < n := hlt m
      have hstep : ∀ c₃ : Config, WordsBounded W c₃ → c₃.nreg 515 = i →
          (∀ r, r ≠ 513 → r < 515 ∨ 521 ≤ r → c₃.nreg r = c.nreg r) →
          c₃.nreg 513 = min (i + 1) d₀ → c₃.nreg 516 = f^[min (i + 1) d₀] x →
          c₃.nreg 520 = lca → (∀ j < min (i + 1) d₀, c₃.nmem (bTmp + j) = Pr (f^[j] x)) →
          (∀ a, a < bTmp ∨ bTmp + n ≤ a → c₃.nmem a = c.nmem a) →
          c₃.output = c.output →
          ∃ c' k, Exec P W (.instr (.addN 515 515 511)) c₃ c' k ∧ I (i + 1) c' ∧ k ≤ 1 := by
        intro c₃ hw₃ e515 er e513 e516 e520 eout ef eo
        have e511 : c₃.nreg 511 = 1 := (er 511 (by omega) (by omega)).trans r511
        have e505 : c₃.nreg 505 = n := (er 505 (by omega) (by omega)).trans r505
        have ea := Exec.addN (P := P) hw₃ 515 515 511 (by rw [e515, e511]; omega)
        refine ⟨_, 1, ea, ⟨ea.wb_right, by config_simp; rw [e515, e511],
          by config_simp; exact e505, by omega, by config_simp; exact e513,
          by config_simp; exact e516, by config_simp; exact e520, by config_simp; exact eout,
          by config_simp; exact ef, fun r h1 h2 => ?_, by config_simp; exact eo⟩, le_rfl⟩
        config_simp; simp only [upd_apply]
        split_ifs with h'
        · omega
        · exact er r h1 h2
      unfold fxBody
      refine spec_seq ?_
      exec_block
      · config_simp; rw [h516', h520]; have := hw₁.1 516; have := hw₁.1 520; omega
      rename_i hwa
      simp only [h516', h520] at hwa ⊢
      refine spec_seq ?_
      by_cases hid : i < d₀
      · have e1 : m = i := by omega
        have e2 : min (i + 1) d₀ = i + 1 := by omega
        obtain ⟨hnl, hnr⟩ := hx i hid
        rw [e1] at hv
        have hvr : v ≠ r₀ := by rw [hv]; exact hnr
        have hvl : v ≠ lca := by rw [hv]; exact hnl
        have hpv := hin.Pr_lt v hvn hvr
        have hav := hin.A_lt _ hpv
        have m1 : c₁.nmem (bPr + v) = Pr v := by rw [hf₁ _ (Or.inl (by omega))]; exact mP v hvn hvr
        have m2 : c₁.nmem (bA + Pr v) = A (Pr v) := by
          rw [hf₁ _ (Or.inl (by omega))]; exact mA _ hpv
        have m3 : c₁.nmem (bV + A (Pr v)) = V (A (Pr v)) := by
          rw [hf₁ _ (Or.inl (by omega))]; exact mV _ hav
        have hfv : f v = V (A (Pr v)) := by
          rw [hf, upN, ite_eq_right_of_eq_false _ _ (eq_false hvr)]; rfl
        have hnext : f^[i + 1] x = f v := by rw [Function.iterate_succ_apply', ← hv]
        refine spec_ifLtN_false (by config_simp; rw [g511]; omega) ?_
        unfold fup
        simp only [List.cons_append, List.nil_append]
        exec_block
        all_goals try (config_simp; (try simp only [g503, h516', m1, g501, m2, g502, m3, g509,
          h513, g511]); omega)
        rename_i hwd
        simp only [g503, h516', m1, g501, m2, g502, m3, g509, h513, g511] at hwd ⊢
        obtain ⟨c', k', e', hI', hk'⟩ := hstep _ hwd (by config_simp; exact h515)
          (fun r h1 h2 => by
            config_simp; simp only [upd_apply]
            split_ifs <;> first | omega | exact hr r h1 h2)
          (by config_simp; rw [e1, e2])
          (by config_simp; rw [e2, hnext, hfv])
          (by config_simp; exact h520)
          (fun j hj => by
            config_simp
            rcases Nat.lt_or_ge j i with hj' | hj'
            · rw [upd_other _ _ _ (by omega)]; exact hout j (by omega)
            · obtain rfl : j = i := by omega
              rw [e1, upd_same, hv])
          (fun a ha => by config_simp; rw [upd_other _ _ _ (by omega)]; exact hf₁ a ha)
          (by config_simp; exact ho)
        exact ⟨c', k', e', hI', by omega⟩
      · have e1 : m = d₀ := by omega
        have e2 : min (i + 1) d₀ = d₀ := by omega
        rw [e1] at hv
        have hvl : v = lca := by rw [hv]; exact hx'
        refine spec_ifLtN_true (by config_simp; rw [g511]; omega) ?_
        refine spec_skip hwa ?_
        obtain ⟨c', k', e', hI', hk'⟩ := hstep _ hwa (by config_simp <;> exact h515)
          (fun r h1 h2 => by
            config_simp; simp only [upd_apply]
            split_ifs <;> first | omega | exact hr r h1 h2)
          (by config_simp; rw [h513, e1, e2])
          (by config_simp; rw [h516', e2, ← e1])
          (by config_simp <;> exact h520)
          (fun j hj => by config_simp; exact hout j (by omega))
          (fun a ha => by config_simp; exact hf₁ a ha) (by config_simp <;> exact ho)
        exact ⟨c', k', e', hI', by omega⟩)
    (by omega) hI₁
  obtain ⟨-, -, -, -, h513', -, -, hout', hf', hr', ho'⟩ := hI
  have hmn : min n d₀ = d₀ := by omega
  rw [hmn] at h513' hout'
  exact ⟨c₂, 5 + t, .seq e₁ e, by omega, h513', hout', hf', hr', ho'⟩

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The reversed darts.** -/
theorem frev_exec (hlay : FLay k n bA bV bPr bMk bTmp bFc W) (c : Config)
    (hc : WordsBounded W c) (hF : FR δ bA bV bPr r₀ n bMk s bFc bTmp c) {cs ct : ℕ}
    {Tv : ℕ → ℕ} (h512 : c.nreg 512 = cs) (h513 : c.nreg 513 = ct) (hcs : cs ≤ n) (hct : ct ≤ n)
    (hT : ∀ j < ct, c.nmem (bTmp + j) = Tv j ∧ Tv j < 3 * k)
    (mA : ∀ x < 3 * k, c.nmem (bA + x) = A x) :
    ∃ c' t, Exec P W frev c c' t ∧ t ≤ 13 * n + 5 ∧ c'.nreg 514 = 1 + cs + ct ∧
      (∀ j < ct, c'.nmem (bFc + 1 + cs + j) = A (Tv (ct - 1 - j))) ∧
      (∀ a, ¬ (bFc + 1 + cs ≤ a ∧ a < bFc + 1 + cs + ct) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 514 → r ≠ 515 → r ≠ 517 → r ≠ 518 → c'.nreg r = c.nreg r) ∧
      c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hlay
  obtain ⟨-, r501, -, -, -, -, -, -, r508, r509, r510, r511⟩ := hF
  let I : ℕ → Config → Prop := fun j c' => WordsBounded W c' ∧ c'.nreg 515 = j ∧
    c'.nreg 513 = ct ∧ j ≤ ct ∧ c'.nreg 514 = 1 + cs + ct ∧
    (∀ j' < j, c'.nmem (bFc + 1 + cs + j') = A (Tv (ct - 1 - j'))) ∧
    (∀ a, ¬ (bFc + 1 + cs ≤ a ∧ a < bFc + 1 + cs + j) → c'.nmem a = c.nmem a) ∧
    (∀ r, r ≠ 514 → r ≠ 515 → r ≠ 517 → r ≠ 518 → c'.nreg r = c.nreg r) ∧
    c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 515 510, .addN 514 512 513,
      .addN 514 514 511]) c c₁ k₁ ∧ I 0 c₁ ∧ k₁ = 3 := by
    exec_block
    all_goals try (config_simp; (try simp only [h512, h513, r511]); omega)
    rename_i hwb
    simp only [h512, h513, r511, r510] at hwb ⊢
    refine ⟨⟨hwb, by config_simp, by config_simp; exact h513, by omega, by config_simp; omega,
      fun j hj => absurd hj (by omega), fun a _ => rfl,
      fun r h1 h2 h3 h4 => by config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl⟩,
      by first | rfl | trivial⟩
  obtain ⟨c₂, t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 515) (rN := 513)
    (N := ct) (lo := 0) (B := 11) (body := block frBody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c₁ ⟨hw₁, h515, h513', hj', h514, hout, hf₁, hr, ho⟩ hj => by
      have g501 : c₁.nreg 501 = bA := by rw [hr 501 (by omega) (by omega) (by omega) (by omega)]; exact r501
      have g508 : c₁.nreg 508 = bFc := by rw [hr 508 (by omega) (by omega) (by omega) (by omega)]; exact r508
      have g509 : c₁.nreg 509 = bTmp := by rw [hr 509 (by omega) (by omega) (by omega) (by omega)]; exact r509
      have g511 : c₁.nreg 511 = 1 := by rw [hr 511 (by omega) (by omega) (by omega) (by omega)]; exact r511
      have g512 : c₁.nreg 512 = cs := by rw [hr 512 (by omega) (by omega) (by omega) (by omega)]; exact h512
      obtain ⟨mT, hTk⟩ := hT (ct - 1 - j) (by omega)
      have m1 : c₁.nmem (bTmp + (ct - j - 1)) = Tv (ct - 1 - j) := by
        rw [hf₁ _ (by omega), show ct - j - 1 = ct - 1 - j by omega]; exact mT
      have m2 : c₁.nmem (bA + Tv (ct - 1 - j)) = A (Tv (ct - 1 - j)) := by
        rw [hf₁ _ (by omega)]; exact mA _ hTk
      unfold frBody
      exec_block
      all_goals try (config_simp; (try simp only [h513', h515, g511, g509, m1, g501, m2, g508, g512]); omega)
      rename_i hwb
      simp only [h513', h515, g511, g509, m1, g501, m2, g508, g512] at hwb ⊢
      refine ⟨⟨hwb, by config_simp, by config_simp; exact h513', by omega,
        by config_simp; exact h514, fun j' hj'' => ?_, fun a ha => ?_, fun r h1 h2 h3 h4 => ?_,
        by config_simp; exact ho⟩, by omega⟩
      · config_simp
        rcases Nat.lt_or_ge j' j with h | h
        · rw [upd_other _ _ _ (by omega)]; exact hout j' h
        · obtain rfl : j' = j := by omega
          rw [show bFc + 1 + cs + j' = bFc + cs + 1 + j' by omega, upd_same]
      · config_simp
        rw [upd_other _ _ _ (by omega)]; exact hf₁ a (by omega)
      · config_simp; simp only [upd_apply]
        split_ifs <;> first | omega | exact hr r h1 h2 h3 h4)
    (by omega) hI₁
  obtain ⟨-, -, -, -, h514', hout', hf', hr', ho'⟩ := hI
  have : (11 + 2) * (ct - 0) ≤ 13 * n := by rw [Nat.sub_zero]; exact Nat.mul_le_mul_left _ hct
  exact ⟨c₂, 3 + t, .seq e₁ e, by omega, h514', hout', hf', hr', ho'⟩

set_option maxHeartbeats 2000000 in
/-- **The darts of a fundamental cycle, numerically.** With the marks at `bMk` free of the stamp,
the lengths `c₀` (from the head `z` to the first ancestor of the tail `x`) and `d₀` (from `x` to
it), `fcProg` writes `δ`, the `c₀` parent darts from `z` and the reversals of the `d₀` parent darts
from `x` in the reverse order, and `r514 = 1 + c₀ + d₀`. -/
theorem fcProg_exec (hlay : FLay k n bA bV bPr bMk bTmp bFc W) (c : Config)
    (hc : WordsBounded W c) (hF : FR δ bA bV bPr r₀ n bMk s bFc bTmp c)
    (hin : RootIn k n r₀ A V Pr) (hδ : δ < 3 * k)
    (mA : ∀ x < 3 * k, c.nmem (bA + x) = A x) (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x)
    (mP : ∀ v < n, v ≠ r₀ → c.nmem (bPr + v) = Pr v) (hs0 : ∀ v < n, c.nmem (bMk + v) ≠ s)
    {c₀ d₀ : ℕ} (hc₀ : c₀ ≤ n)
    (hz : ∀ j < c₀, (¬ ∃ i < n, (upN A V Pr r₀)^[i] (V δ) = (upN A V Pr r₀)^[j] (V (A δ))) ∧
      (upN A V Pr r₀)^[j] (V (A δ)) ≠ r₀)
    (hz' : ∃ i < n, (upN A V Pr r₀)^[i] (V δ) = (upN A V Pr r₀)^[c₀] (V (A δ)))
    (hd₀ : d₀ ≤ n)
    (hx : ∀ j < d₀, (upN A V Pr r₀)^[j] (V δ) ≠ (upN A V Pr r₀)^[c₀] (V (A δ)) ∧
      (upN A V Pr r₀)^[j] (V δ) ≠ r₀)
    (hx' : (upN A V Pr r₀)^[d₀] (V δ) = (upN A V Pr r₀)^[c₀] (V (A δ))) :
    ∃ c' t, Exec P W fcProg c c' t ∧ t ≤ 77 * n + 26 ∧ c'.nreg 514 = 1 + c₀ + d₀ ∧
      c'.nmem bFc = δ ∧
      (∀ j < c₀, c'.nmem (bFc + 1 + j) = Pr ((upN A V Pr r₀)^[j] (V (A δ)))) ∧
      (∀ j < d₀, c'.nmem (bFc + 1 + c₀ + j) = A (Pr ((upN A V Pr r₀)^[d₀ - 1 - j] (V δ)))) ∧
      (∀ a, a < bMk ∨ bFc + 2 * n + 1 ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 512 ∨ 521 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  have hl := hlay
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hl
  set f := upN A V Pr r₀ with hf
  have hxn : V δ < n := hin.V_lt _ hδ
  have hzn : V (A δ) < n := hin.V_lt _ (hin.A_lt _ hδ)
  -- 1. the marks
  obtain ⟨c₁, t₁, e₁, ht₁, hM1, hM2, hf₁, hr₁, ho₁⟩ :=
    fmark_exec (P := P) hlay c hc hF hin hδ mA mV mP
  have hF₁ := hF.of fun r h1 h2 => hr₁ r (Or.inl (by omega))
  have mA₁ : ∀ x < 3 * k, c₁.nmem (bA + x) = A x := fun x hx => by
    rw [hf₁ _ (Or.inl (by omega))]; exact mA x hx
  have mV₁ : ∀ x < 3 * k, c₁.nmem (bV + x) = V x := fun x hx => by
    rw [hf₁ _ (Or.inl (by omega))]; exact mV x hx
  have mP₁ : ∀ v < n, v ≠ r₀ → c₁.nmem (bPr + v) = Pr v := fun v hv hr => by
    rw [hf₁ _ (Or.inl (by omega))]; exact mP v hv hr
  -- 2. from the head
  obtain ⟨c₂, t₂, e₂, ht₂, h512, h516, h0, hout, hf₂, hr₂, ho₂⟩ :=
    fwalkZ_exec (P := P) hlay c₁ e₁.wb_right hF₁ hin hδ mA₁ mV₁ mP₁ hc₀
      (fun j hj => ⟨by
        rw [hM2 _ (iter_up_lt hin hzn j) (hz j hj).1]; exact hs0 _ (iter_up_lt hin hzn j),
        (hz j hj).2⟩)
      (hM1 _ (iter_up_lt hin hzn c₀) hz')
  have hF₂ := hF₁.of fun r h1 h2 => hr₂ r (by omega) (Or.inl (by omega))
  have mA₂ : ∀ x < 3 * k, c₂.nmem (bA + x) = A x := fun x hx => by
    rw [hf₂ _ (Or.inl (by omega))]; exact mA₁ x hx
  have mV₂ : ∀ x < 3 * k, c₂.nmem (bV + x) = V x := fun x hx => by
    rw [hf₂ _ (Or.inl (by omega))]; exact mV₁ x hx
  have mP₂ : ∀ v < n, v ≠ r₀ → c₂.nmem (bPr + v) = Pr v := fun v hv hr => by
    rw [hf₂ _ (Or.inl (by omega))]; exact mP₁ v hv hr
  -- 3. from the tail
  obtain ⟨c₃, t₃, e₃, ht₃, h513, htmp, hf₃, hr₃, ho₃⟩ :=
    fwalkX_exec (P := P) hlay c₂ e₂.wb_right hF₂ hin hδ h516 mA₂ mV₂ mP₂ hd₀ hx hx'
  have hF₃ := hF₂.of fun r h1 h2 => hr₃ r (by omega) (Or.inl (by omega))
  have mA₃ : ∀ x < 3 * k, c₃.nmem (bA + x) = A x := fun x hx => by
    rw [hf₃ _ (Or.inl (by omega))]; exact mA₂ x hx
  have h512₃ : c₃.nreg 512 = c₀ := by rw [hr₃ 512 (by omega) (Or.inl (by omega))]; exact h512
  -- 4. the reversed darts
  obtain ⟨c₄, t₄, e₄, ht₄, h514, hrev, hf₄, hr₄, ho₄⟩ :=
    frev_exec (P := P) (Tv := fun j => Pr (f^[j] (V δ))) hlay c₃ e₃.wb_right hF₃ h512₃ h513 hc₀
      hd₀ (fun j hj => ⟨htmp j hj, hin.Pr_lt _ (iter_up_lt hin hxn j) (hx j hj).2⟩) mA₃
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, h514, ?_, ?_,
    ?_, fun a ha => ?_, fun r hr => ?_, by rw [ho₄, ho₃, ho₂, ho₁]⟩
  · rw [hf₄ _ (by omega), hf₃ _ (Or.inr (by omega))]; exact h0
  · intro j hj
    rw [hf₄ _ (by omega), hf₃ _ (Or.inr (by omega))]; exact hout j hj
  · intro j hj
    rw [hrev j hj]
  · rw [hf₄ _ (by omega), hf₃ _ (by omega), hf₂ _ (by omega), hf₁ _ (by omega)]
  · rw [hr₄ r (by omega) (by omega) (by omega) (by omega), hr₃ r (by omega) (by omega),
      hr₂ r (by omega) (by omega), hr₁ r (by omega)]

end proofs

/-! ### Through the coding -/

section Bridge

open Map

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

/-- An ancestor is reached in fewer than `#Q` parent steps. -/
theorem SpTree.exists_iter_lt (T : M.SpTree) {u v : Q} (hu : u ∈ T.anc v) :
    ∃ i < Fintype.card Q, T.parent^[i] v = u := by
  classical
  have hex := (T.mem_anc_iff).1 hu
  obtain ⟨i, hiu, hmin⟩ : ∃ i, T.parent^[i] v = u ∧ ∀ j < i, T.parent^[j] v ≠ u :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  refine ⟨i, ?_, hiu⟩
  have hnr : ∀ j < i, T.parent^[j] v ≠ T.root := by
    intro j hj e
    apply hmin j hj
    rw [e, ← hiu, show i = (i - j) + j by omega, Function.iterate_add_apply, e,
      T.iterate_parent_root]
  have hinj : Set.InjOn (fun j => T.parent^[j] v) (range (i + 1) : Set ℕ) := by
    intro a ha b hb e
    simp only [coe_range, Set.mem_Iio] at ha hb
    by_cases hab : a = b
    · exact hab
    exact T.iterate_inj e (hnr _ (by omega))
  have := card_le_card (subset_univ ((range (i + 1)).image fun j => T.parent^[j] v))
  rw [card_image_of_injOn hinj, card_range, card_univ] at this
  omega

set_option maxHeartbeats 2000000 in
/-- **The darts of a fundamental cycle on the machine.** For a spanning tree `T` whose parent
darts are coded by `Pr` (`Pr (vi v) = cd (T.par v)`), and a dart `δ`, `fcProg` writes at
`bFc + i` the codes of the darts `(T.fcycle δ).d i` of the fundamental cycle of `δ`, `i` below its
length `(T.fcycle δ).k` (in `r514`), within `77 n + 26` steps. -/
theorem fcProg_fcycle {T : M.SpTree} {k n : ℕ} (cd : D ≃ Fin (3 * k)) (vi : Q ≃ Fin n)
    {A V Pr : ℕ → ℕ} (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hV : ∀ x, V (cd x) = vi (M.vert x))
    (hPr : ∀ v (h : v ≠ T.root), Pr (vi v) = cd (T.par v h)) (δ : D)
    {W bA bV bPr bMk s bFc bTmp : ℕ} {P : Input} (hlay : FLay k n bA bV bPr bMk bTmp bFc W)
    (c : Config) (hc : WordsBounded W c)
    (hF : FR (cd δ) bA bV bPr (vi T.root) n bMk s bFc bTmp c)
    (mA : ∀ x < 3 * k, c.nmem (bA + x) = A x) (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x)
    (mP : ∀ v < n, v ≠ (vi T.root : ℕ) → c.nmem (bPr + v) = Pr v)
    (hs0 : ∀ v < n, c.nmem (bMk + v) ≠ s) :
    ∃ c' t, Exec P W fcProg c c' t ∧ t ≤ 77 * n + 26 ∧ c'.nreg 514 = (T.fcycle δ).k ∧
      (∀ i < (T.fcycle δ).k, c'.nmem (bFc + i) = cd ((T.fcycle δ).d i)) ∧
      (∀ a, a < bMk ∨ bFc + 2 * n + 1 ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 512 ∨ 521 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  classical
  have hin := rootIn_tree cd vi T hAcd hV hPr
  have hit : ∀ j u, (upN A V Pr (vi T.root))^[j] (vi u) = vi (T.parent^[j] u) := by
    intro j
    induction j with
    | zero => intro u; rfl
    | succ j ih =>
      intro u
      rw [Function.iterate_succ_apply', ih, upN_tree cd vi T hAcd hV hPr,
        ← Function.iterate_succ_apply' T.parent]
  have hcard : Fintype.card Q = n := by rw [Fintype.card_congr vi, Fintype.card_fin]
  set x' := M.vert δ
  set z' := M.vert (M.α δ)
  have ex : V (cd δ) = vi x' := hV δ
  have ez : V (A (cd δ)) = vi z' := by rw [hAcd, hV]
  have hS : ∀ u, (∃ i < n, (upN A V Pr (vi T.root))^[i] (vi x') = vi u) ↔ u ∈ T.anc x' := by
    intro u
    constructor
    · rintro ⟨i, -, e⟩
      rw [hit] at e
      rw [← Fin.ext e |> vi.injective]
      exact T.iterate_parent_mem_anc i x'
    · intro hu
      obtain ⟨i, hi, e⟩ := SpTree.exists_iter_lt T hu
      exact ⟨i, by omega, by rw [hit, e]⟩
  have hnrz : ∀ j < SpTree.cs T δ, T.parent^[j] z' ≠ T.root := fun j hj =>
    SpTree.iterate_ne_root_of_lt_cs hj
  have hnrx : ∀ j < SpTree.ct T δ, T.parent^[j] x' ≠ T.root := fun j hj =>
    SpTree.iterate_ne_root_of_lt_ct hj
  have hcs : SpTree.cs T δ ≤ n :=
    (T.lt_card_anc hnrz).trans ((card_le_univ _).trans hcard.le)
  have hct : SpTree.ct T δ ≤ n :=
    (T.lt_card_anc hnrx).trans ((card_le_univ _).trans hcard.le)
  have hlca : T.parent^[SpTree.cs T δ] z' = SpTree.lca T δ := rfl
  obtain ⟨c', t, e, ht, h514, h0, hout, hrev, hfm, hfr, ho⟩ := fcProg_exec (P := P)
    (c₀ := SpTree.cs T δ) (d₀ := SpTree.ct T δ) hlay c hc hF hin (cd δ).2 mA mV mP hs0 hcs
    (fun j hj => by
      rw [ex, ez, hit]
      exact ⟨fun ⟨i, hi, e⟩ => SpTree.iterate_notMem_of_lt_cs hj ((hS _).1 ⟨i, hi, e⟩),
        fun e => hnrz j hj (vi.injective (Fin.ext e))⟩)
    (by rw [ex, ez, hit, hlca]; exact (hS _).2 (SpTree.lca_mem_anc δ))
    hct
    (fun j hj => by
      rw [ex, ez, hit, hit, hlca]
      exact ⟨fun e => SpTree.iterate_ne_of_lt_ct hj (vi.injective (Fin.ext e)),
        fun e => hnrx j hj (vi.injective (Fin.ext e))⟩)
    (by rw [ex, ez, hit, hit, hlca, SpTree.iterate_ct])
  refine ⟨c', t, e, ht, h514, fun i hi => ?_, hfm, hfr, ho⟩
  rw [SpTree.fcycle_k] at hi
  rw [SpTree.fcycle_d]
  unfold SpTree.fd
  unfold SpTree.ck at hi
  split_ifs with h1 h2
  · subst h1; simpa using h0
  · have hj : i - 1 < SpTree.cs T δ := by omega
    rw [SpTree.pdt_of_ne (hnrz _ hj), ← hPr, ← hit, ← ez, show bFc + i = bFc + 1 + (i - 1) by omega]
    exact hout _ hj
  · have hj : i - 1 - SpTree.cs T δ < SpTree.ct T δ := by omega
    have e2 : SpTree.ck T δ - 1 - i = SpTree.ct T δ - 1 - (i - 1 - SpTree.cs T δ) := by
      unfold SpTree.ck; omega
    rw [e2, SpTree.pdt_of_ne (hnrx _ (by omega)), ← hAcd, ← hPr, ← hit, ← ex,
      show bFc + i = bFc + 1 + SpTree.cs T δ + (i - 1 - SpTree.cs T δ) by omega]
    exact hrev _ hj

end Bridge

end MillerProg

end PlanarSeparator
