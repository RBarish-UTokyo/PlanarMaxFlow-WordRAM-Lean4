module

public import PlanarSeparator.Machine.MillerInner
public import PlanarSeparator.BandExplicit

/-!
# Miller's separator on the machine: the band case analysis (step 9), first passes

Step 9 of the plan in `PlanarSeparator/Machine/Miller.lean` computes the separator
`PlanarSeparator.Map.bandSep` of `PlanarSeparator/BandExplicit.lean` from the balanced dart of
step 8. In the deep case it needs the boundary cycle of the component `Y` of the dart at level
`l₂`, the ancestors at level `l₂` of the ends of the dart, and the trees redirected along the
arcs of the cycle. This file has the passes computing them on the coded map (darts `x < 3 k`,
reversal `A x` at `bA + x`, vertex `V x` at `bV + x`, the label `lb f` of the face `f` at
`bL + f`, the label `h` of `Y`), each with an explicit linear step bound, and their reading
through the coding (`cd : D ≃ Fin (3 k)`, `vi : P ≃ Fin n`):

* `bdPass`, one pass over the darts: for every dart `x` leaving `Y` (`Lv lb A h x`), the cell
  `bNx + V x` receives such a dart, and `r351` counts them (`bdPass_exec`, within `72 k + 4`
  steps; the count is `bdK Y`, `nOut_eq_bdK`).
* `cyWalk`: from a dart `x₀` leaving `Y`, `K = r351` steps of `x ↦ nx (V (A x))`, writing the
  `i`-th dart at `bCy + i` and the index `i` of its vertex at `bPos + V x` (`cyWalk_exec`, within
  `16 K + 4` steps). Through the coding these are the darts `bdD Y x₀ i` of the boundary cycle
  `PlanarSeparator.Map.bdCycle` (`cyNext_iter_bdD`, from `PlanarSeparator.Map.bdD_eq_iterate`),
  with distinct vertices (`cyNext_inj`).
* `taPass`: the ancestor at level `≤ l` of a vertex `u` in the tree of the parent darts at
  `bPr`: `n` guarded parent steps (`taPass_exec`, within `12 n + 4` steps); through the coding
  this is `PlanarSeparator.Map.topA` (`taNext_topA`, from
  `PlanarSeparator.Map.topA_eq_iterate`).
* `cpPass` and `arPass`: a copy of the parent darts at `bPr2` (`cpPass_exec`, `7 n + 3` steps),
  then the redirection along the arc of `ℓ` steps of the cycle from the index `s`
  (`arPass_exec`, `19 ℓ + 4` steps); through the coding these are the parent darts of
  `PlanarSeparator.Map.SpTree.arcTree` (`arcTree_par_code`), the tree of a rerouting option
  (`PlanarSeparator.Map.arcOpt`).

Registers: inputs `r330 = 0`, `r331 = 1`, `r332 = 3`, `r333 = bA`, `r334 = bV`, `r335 = bL`,
`r336 = 3 k`, `r337 = h`, `r338 = bNx`, `r339 = bCy`, `r340 = bPos`, `r341 = n`, `r342 = bLv`
(levels), `r343 = bPr` (parent darts), `r344 = l`, `r345 = x₀`, `r346 = u` (`BR`), and
`r347 = s`, `r348 = ℓ`, `r349 = bPr2`; the passes write `r350 … r358` (`bdPass`, with the count
in `r351`), `r360 … r365` (`cyWalk`), `r370 … r373` (`taPass`), `r380 … r386` (`arPass`),
`r390 … r392` (`cpPass`), all at `r430` and above, disjoint from the registers of steps 1–8.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The programs -/

/-- The test of the dart `r350 = x`: `r355 = A x`, `r357 = |lb (x / 3) - h|`,
`r358 = |lb (A x / 3) - h|`. -/
def bdTest : List Instr :=
  [.divN 452 450 432, .addN 453 435 452, .loadN 454 453, .addN 453 433 450, .loadN 455 453,
    .divN 452 455 432, .addN 453 435 452, .loadN 456 453, .subN 457 454 437, .subN 458 437 454,
    .addN 457 457 458, .subN 458 456 437, .subN 452 437 456, .addN 458 458 452]

/-- A dart leaving `Y`: store it at its vertex, count it. -/
def bdStore : List Instr :=
  [.addN 453 434 450, .loadN 452 453, .addN 453 438 452, .storeN 453 450, .addN 451 451 431]

/-- **One dart** `r350 = x`. -/
def bdBody : Stmt :=
  .seq (block bdTest)
    (.seq (.ifLtN 457 431 (.ifLtN 430 458 (block bdStore) .skip) .skip)
      (.instr (.addN 450 450 431)))

/-- **The darts leaving `Y`, by their vertices**, and their number in `r351`. -/
def bdPass : Stmt := .seq (block [.copyN 450 430, .copyN 451 430]) (.whileLtN 450 436 bdBody)

/-- **One step of the walk** `r360 = i`, `r361 = x`: record `x` at `bCy + i` and `i` at
`bPos + V x`, then move to `nx (V (A x))`. -/
def cyBody : List Instr :=
  [.addN 462 434 461, .loadN 463 462, .addN 462 433 461, .loadN 464 462, .addN 462 434 464,
    .loadN 464 462, .addN 462 438 464, .loadN 464 462, .addN 462 439 460, .storeN 462 461,
    .addN 462 440 463, .storeN 462 460, .copyN 461 464, .addN 460 460 431]

/-- **The boundary cycle**: `K = r351` steps from `x₀ = r345`. -/
def cyWalk : Stmt := .seq (block [.copyN 460 430, .copyN 461 445]) (.whileLtN 460 451 (block cyBody))

/-- The parent of `r371 = v` if its level is `> l`. -/
def taStep : List Instr :=
  [.addN 472 443 471, .loadN 473 472, .addN 472 433 473, .loadN 473 472, .addN 472 434 473,
    .loadN 471 472]

/-- **One guarded parent step.** -/
def taBody : Stmt :=
  .seq (block [.addN 472 442 471, .loadN 473 472])
    (.seq (.ifLtN 444 473 (block taStep) .skip) (.instr (.addN 470 470 431)))

/-- **The ancestor at level `≤ l`** of `u = r346`, in `r371`: `n` guarded parent steps. -/
def taPass : Stmt := .seq (block [.copyN 470 430, .copyN 471 446]) (.whileLtN 470 441 taBody)

/-- The input registers of the passes of step 9. -/
structure BR (bA bV bL k h bNx bCy bPos n bLv bPr l x₀ u : ℕ) (c : Config) : Prop where
  r330 : c.nreg 430 = 0
  r331 : c.nreg 431 = 1
  r332 : c.nreg 432 = 3
  r333 : c.nreg 433 = bA
  r334 : c.nreg 434 = bV
  r335 : c.nreg 435 = bL
  r336 : c.nreg 436 = 3 * k
  r337 : c.nreg 437 = h
  r338 : c.nreg 438 = bNx
  r339 : c.nreg 439 = bCy
  r340 : c.nreg 440 = bPos
  r341 : c.nreg 441 = n
  r342 : c.nreg 442 = bLv
  r343 : c.nreg 443 = bPr
  r344 : c.nreg 444 = l
  r345 : c.nreg 445 = x₀
  r346 : c.nreg 446 = u

theorem BR.of {bA bV bL k h bNx bCy bPos n bLv bPr l x₀ u : ℕ} {c c' : Config}
    (hB : BR bA bV bL k h bNx bCy bPos n bLv bPr l x₀ u c)
    (e : ∀ r, 430 ≤ r → r < 447 → c'.nreg r = c.nreg r) :
    BR bA bV bL k h bNx bCy bPos n bLv bPr l x₀ u c' :=
  ⟨(e _ (by omega) (by omega)).trans hB.r330, (e _ (by omega) (by omega)).trans hB.r331,
    (e _ (by omega) (by omega)).trans hB.r332, (e _ (by omega) (by omega)).trans hB.r333,
    (e _ (by omega) (by omega)).trans hB.r334, (e _ (by omega) (by omega)).trans hB.r335,
    (e _ (by omega) (by omega)).trans hB.r336, (e _ (by omega) (by omega)).trans hB.r337,
    (e _ (by omega) (by omega)).trans hB.r338, (e _ (by omega) (by omega)).trans hB.r339,
    (e _ (by omega) (by omega)).trans hB.r340, (e _ (by omega) (by omega)).trans hB.r341,
    (e _ (by omega) (by omega)).trans hB.r342, (e _ (by omega) (by omega)).trans hB.r343,
    (e _ (by omega) (by omega)).trans hB.r344, (e _ (by omega) (by omega)).trans hB.r345,
    (e _ (by omega) (by omega)).trans hB.r346⟩

/-- The number of darts `< i` leaving the component of label `h`. -/
def nOut (lb A : ℕ → ℕ) (h i : ℕ) : ℕ :=
  #((range i).filter fun x => lb (x / 3) = h ∧ lb (A x / 3) ≠ h)

lemma nOut_succ (lb A : ℕ → ℕ) (h i : ℕ) :
    nOut lb A h (i + 1) =
      nOut lb A h i + if lb (i / 3) = h ∧ lb (A i / 3) ≠ h then 1 else 0 := by
  unfold nOut
  rw [range_add_one, filter_insert]
  split_ifs with hi
  · rw [card_insert_of_notMem (by simp)]
  · rw [add_zero]

section proofs

variable {k : ℕ} {W : ℕ} {P : Input}
  {bA bV bL h bNx bCy bPos n bLv bPr l x₀ u : ℕ}

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- The test of a dart. -/
theorem bdTest_exec {A lb : ℕ → ℕ} {x : ℕ} (hW : bL + k ≤ W ∧ bA + 3 * k ≤ W) (c : Config)
    (hc : WordsBounded W c) (h332 : c.nreg 432 = 3) (h335 : c.nreg 435 = bL)
    (h333 : c.nreg 433 = bA) (h337 : c.nreg 437 = h) (h350 : c.nreg 450 = x) (hx : x < 3 * k)
    (mA : c.nmem (bA + x) = A x) (hAx : A x < 3 * k) (m1 : c.nmem (bL + x / 3) = lb (x / 3))
    (m2 : c.nmem (bL + A x / 3) = lb (A x / 3)) :
    ∃ c' t, Exec P W (block bdTest) c c' t ∧ t = 14 ∧ c'.nreg 455 = A x ∧
      (c'.nreg 457 < 1 ↔ lb (x / 3) = h) ∧ (0 < c'.nreg 458 ↔ lb (A x / 3) ≠ h) ∧
      (∀ r, r < 452 ∨ 459 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.output = c.output := by
  have hb1 := hc.2 (bL + x / 3)
  have hb2 := hc.2 (bL + A x / 3)
  have hh := hc.1 437
  rw [m1] at hb1; rw [m2] at hb2; rw [h337] at hh
  unfold bdTest
  exec_block
  all_goals try (config_simp; (try simp only [h332, h335, h333, h350, mA, m1, m2, h337]); omega)
  rename_i hwb
  simp only [h332, h335, h333, h350, mA, m1, m2, h337] at hwb ⊢
  refine ⟨trivial, by config_simp, by config_simp; omega, by config_simp; omega, fun r hr => ?_,
    by config_simp, by config_simp⟩
  config_simp; simp only [upd_apply]; split_ifs <;> omega

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The darts leaving `Y`, by their vertices.** After `bdPass`, for every vertex `v < n` at
which a dart leaves the component of label `h`, the cell `bNx + v` holds such a dart
(`PlanarSeparator.MillerProg.PInv` with the identity), the other cells of `[bNx, bNx + n)` are
unchanged, and `r351` is the number of these darts. -/
theorem bdPass_exec {A lb V : ℕ → ℕ}
    (hlay : bA + 3 * k ≤ bNx ∧ bV + 3 * k ≤ bNx ∧ bNx + n ≤ bL) (hW : bL + k ≤ W)
    (c : Config) (hc : WordsBounded W c) (hB : BR bA bV bL k h bNx bCy bPos n bLv bPr l x₀ u c)
    (hA : ∀ x < 3 * k, c.nmem (bA + x) = A x ∧ A x < 3 * k)
    (hlb : ∀ g < k, c.nmem (bL + g) = lb g) (hV : ∀ x < 3 * k, c.nmem (bV + x) = V x ∧ V x < n) :
    ∃ c' t, Exec P W bdPass c c' t ∧ t ≤ 72 * k + 4 ∧
      PInv n bNx (Lv lb A h) V id c.nmem (3 * k) c'.nmem ∧
      c'.nreg 451 = nOut lb A h (3 * k) ∧
      (∀ a, a < bNx ∨ bNx + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 450 ∨ 459 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  obtain ⟨r330, r331, r332, r333, r334, r335, r336, r337, r338, -, -, -, -, -, -, -, -⟩ := hB
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 450 = i ∧
    c'.nreg 436 = 3 * k ∧ i ≤ 3 * k ∧ c'.nreg 451 = nOut lb A h i ∧
    PInv n bNx (Lv lb A h) V id c.nmem i c'.nmem ∧
    (∀ a, a < bNx ∨ bNx + n ≤ a → c'.nmem a = c.nmem a) ∧
    (∀ r, r < 450 ∨ 459 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 450 430, .copyN 451 430])
      c c₁ k₁ ∧ I 0 c₁ ∧ k₁ = 2 := by
    exec_block
    refine ⟨⟨‹_›, by config_simp; exact r330, by config_simp; exact r336, by omega,
      by config_simp; rw [r330]; rfl,
      fun v hv => ⟨fun ⟨x, hx, _⟩ => absurd hx (by omega), fun _ => rfl⟩, fun a _ => rfl,
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl⟩, rfl⟩
  obtain ⟨c₂, t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 450) (rN := 436)
    (N := 3 * k) (lo := 0) (B := 22) (body := bdBody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h350, h336, hin, h351, hP, hf, hr, ho⟩ hi => by
      have g : ∀ r, r < 450 → c₁.nreg r = c.nreg r := fun r hr' => hr r (Or.inl hr')
      have g330 : c₁.nreg 430 = 0 := by rw [g 430 (by omega)]; exact r330
      have g331 : c₁.nreg 431 = 1 := by rw [g 431 (by omega)]; exact r331
      have g332 : c₁.nreg 432 = 3 := by rw [g 432 (by omega)]; exact r332
      have g333 : c₁.nreg 433 = bA := by rw [g 433 (by omega)]; exact r333
      have g334 : c₁.nreg 434 = bV := by rw [g 434 (by omega)]; exact r334
      have g335 : c₁.nreg 435 = bL := by rw [g 435 (by omega)]; exact r335
      have g337 : c₁.nreg 437 = h := by rw [g 437 (by omega)]; exact r337
      have g338 : c₁.nreg 438 = bNx := by rw [g 438 (by omega)]; exact r338
      obtain ⟨mA, hAi⟩ := hA i hi
      obtain ⟨c₂, t₂, e₂, rfl, f355, f357, f358, fr, fm, fo⟩ := bdTest_exec (P := P) (lb := lb)
        ⟨hW, by omega⟩ c₁ hw₁ g332 g335 g333 g337 h350 hi
        (by rw [hf _ (Or.inl (by omega))]; exact mA) hAi
        (by rw [hf _ (Or.inr (by omega))]; exact hlb _ (by omega))
        (by rw [hf _ (Or.inr (by omega))]; exact hlb _ (by omega))
      have hw₂ := e₂.wb_right
      have f350 : c₂.nreg 450 = i := (fr 450 (by omega)).trans h350
      have f330 : c₂.nreg 430 = 0 := (fr 430 (by omega)).trans g330
      have f331 : c₂.nreg 431 = 1 := (fr 431 (by omega)).trans g331
      have f351 : c₂.nreg 451 = nOut lb A h i := (fr 451 (by omega)).trans h351
      have hstep : ∀ c₃ : Config, WordsBounded W c₃ → c₃.nreg 450 = i →
          (∀ r, r < 450 ∨ 459 ≤ r → c₃.nreg r = c₂.nreg r) →
          c₃.nreg 451 = nOut lb A h (i + 1) →
          PInv n bNx (Lv lb A h) V id c.nmem (i + 1) c₃.nmem →
          (∀ a, a < bNx ∨ bNx + n ≤ a → c₃.nmem a = c.nmem a) → c₃.output = c.output →
          ∃ c' k, Exec P W (.instr (.addN 450 450 431)) c₃ c' k ∧ I (i + 1) c' ∧ k ≤ 1 := by
        intro c₃ hw₃ e350 er e351 eP ef eo
        have e331 : c₃.nreg 431 = 1 := (er 431 (by omega)).trans f331
        have ea := Exec.addN (P := P) hw₃ 450 450 431 (by rw [e350, e331]; omega)
        refine ⟨_, 1, ea, ⟨ea.wb_right, by config_simp; rw [e350, e331], ?_, by omega,
          by config_simp; exact e351, by config_simp; exact eP, by config_simp; exact ef,
          fun r hr' => ?_, by config_simp; exact eo⟩, le_rfl⟩
        · config_simp; rw [er 436 (by omega), fr 436 (by omega), h336]
        · config_simp; simp only [upd_apply]
          split_ifs with h'
          · omega
          · rw [er r (by omega), fr r (by omega)]; exact hr r hr'
      have hcnt : nOut lb A h i < 3 * k := by
        have := card_le_card (filter_subset (fun x => lb (x / 3) = h ∧ lb (A x / 3) ≠ h)
          (range i))
        rw [card_range] at this
        unfold nOut; omega
      unfold bdBody
      refine spec_seq ⟨c₂, 14, e₂, ?_⟩
      refine spec_seq ?_
      by_cases hl : Lv lb A h i
      · refine spec_ifLtN_true (by rw [f331]; exact f357.2 hl.1) ?_
        refine spec_ifLtN_true (by rw [f330]; exact f358.2 hl.2) ?_
        obtain ⟨mV, hVn⟩ := hV _ hi
        have mV' : c₂.nmem (bV + i) = V i := by
          rw [fm, hf _ (Or.inl (by omega))]; exact mV
        have f334 : c₂.nreg 434 = bV := (fr 434 (by omega)).trans g334
        have f338 : c₂.nreg 438 = bNx := (fr 438 (by omega)).trans g338
        unfold bdStore
        exec_block
        · rw [f334, f350]; omega
        · config_simp; simp only [f334, f350, mV', f338]; omega
        · config_simp; rw [f351, f331]; omega
        rename_i hwd
        simp only [f334, f350, mV', f338, f351, f331] at hwd ⊢
        obtain ⟨c', k', e', hI', hk'⟩ := hstep _ hwd (by config_simp; exact f350)
          (fun r hr' => by config_simp; simp only [upd_apply]; split_ifs <;> omega)
          (by
            config_simp
            rw [nOut_succ, ite_eq_left_of_eq_true _ _
              (eq_true (show lb (i / 3) = h ∧ lb (A i / 3) ≠ h from hl))])
          (by config_simp; rw [fm]; exact hP.store (A := id) hl hVn)
          (fun a ha => by
            config_simp; rw [upd_other _ _ _ (by omega), fm]; exact hf a ha)
          (by config_simp; rw [fo, ho])
        exact ⟨c', k', e', hI', by omega⟩
      · have e351 : c₂.nreg 451 = nOut lb A h (i + 1) := by
          rw [f351, nOut_succ, ite_eq_right_of_eq_false _ _
            (eq_false (show ¬ (lb (i / 3) = h ∧ lb (A i / 3) ≠ h) from hl)), add_zero]
        by_cases hl1 : lb (i / 3) = h
        · refine spec_ifLtN_true (by rw [f331]; exact f357.2 hl1) ?_
          have hl2 : ¬ lb (A i / 3) ≠ h := fun h2 => hl ⟨hl1, h2⟩
          refine spec_ifLtN_false (by rw [f330]; exact fun h' => hl2 (f358.1 h')) ?_
          refine spec_skip hw₂ ?_
          obtain ⟨c', k', e', hI', hk'⟩ := hstep _ hw₂ f350 (fun r _ => rfl) e351
            (by rw [fm]; exact hP.skip hl) (fun a ha => by rw [fm]; exact hf a ha)
            (by rw [fo, ho])
          exact ⟨c', k', e', hI', by omega⟩
        · refine spec_ifLtN_false (by rw [f331]; exact fun h' => hl1 (f357.1 h')) ?_
          refine spec_skip hw₂ ?_
          obtain ⟨c', k', e', hI', hk'⟩ := hstep _ hw₂ f350 (fun r _ => rfl) e351
            (by rw [fm]; exact hP.skip hl) (fun a ha => by rw [fm]; exact hf a ha)
            (by rw [fo, ho])
          exact ⟨c', k', e', hI', by omega⟩)
    (by omega) hI₁
  obtain ⟨-, -, -, -, h351', hP', hf', hr', ho'⟩ := hI
  exact ⟨c₂, 2 + t, .seq e₁ e, by omega, hP', h351', hf', hr', ho'⟩

end proofs

/-- The next dart of the walk: `nx (V (A x))`. -/
def cyNext (A V NX : ℕ → ℕ) (x : ℕ) : ℕ := NX (V (A x))

/-- The guarded parent step: the parent `V (A (Pr v))` if the level of `v` is `> l`. -/
def taNext (L Pr A V : ℕ → ℕ) (l v : ℕ) : ℕ := if l < L v then V (A (Pr v)) else v

lemma cyNext_iter_lt {A V NX : ℕ → ℕ} {k n x₀ : ℕ} (hx₀ : x₀ < 3 * k)
    (hA : ∀ x < 3 * k, A x < 3 * k) (hV : ∀ x < 3 * k, V x < n) (hN : ∀ v < n, NX v < 3 * k)
    (i : ℕ) : (cyNext A V NX)^[i] x₀ < 3 * k := by
  induction i with
  | zero => exact hx₀
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact hN _ (hV _ (hA _ ih))

lemma taNext_iter_lt {L Pr A V : ℕ → ℕ} {k n l u : ℕ} (hu : u < n)
    (hPr : ∀ v < n, l < L v → Pr v < 3 * k) (hA : ∀ x < 3 * k, A x < 3 * k)
    (hV : ∀ x < 3 * k, V x < n) (i : ℕ) : (taNext L Pr A V l)^[i] u < n := by
  induction i with
  | zero => exact hu
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    unfold taNext
    split_ifs with h
    · exact hV _ (hA _ (hPr _ ih h))
    · exact ih

section proofs2

variable {k : ℕ} {W : ℕ} {P : Input}
  {bA bV bL h bNx bCy bPos n bLv bPr l x₀ u : ℕ}

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The boundary cycle, by a walk.** From `x₀`, `K = r351` steps of `cyNext` (the dart stored
at the vertex `V (A x)`): the `i`-th dart is written at `bCy + i`, and, if the vertices of the
walk are distinct, the index `i` at `bPos + V x`. -/
theorem cyWalk_exec {A V NX : ℕ → ℕ} {K : ℕ}
    (hlay : bA + 3 * k ≤ bCy ∧ bV + 3 * k ≤ bCy ∧ bNx + n ≤ bCy ∧ bCy + K ≤ bPos)
    (hW : bPos + n ≤ W) (c : Config) (hc : WordsBounded W c)
    (hB : BR bA bV bL k h bNx bCy bPos n bLv bPr l x₀ u c) (h351 : c.nreg 451 = K)
    (hx₀ : x₀ < 3 * k) (hA : ∀ x < 3 * k, c.nmem (bA + x) = A x ∧ A x < 3 * k)
    (hV : ∀ x < 3 * k, c.nmem (bV + x) = V x ∧ V x < n)
    (hN : ∀ v < n, c.nmem (bNx + v) = NX v ∧ NX v < 3 * k)
    (hinj : ∀ i < K, ∀ j < K, V ((cyNext A V NX)^[i] x₀) = V ((cyNext A V NX)^[j] x₀) →
      i = j) :
    ∃ c' t, Exec P W cyWalk c c' t ∧ t ≤ 16 * K + 4 ∧
      (∀ i < K, c'.nmem (bCy + i) = (cyNext A V NX)^[i] x₀) ∧
      (∀ i < K, c'.nmem (bPos + V ((cyNext A V NX)^[i] x₀)) = i) ∧
      c'.nreg 461 = (cyNext A V NX)^[K] x₀ ∧
      (∀ a, ¬ (bCy ≤ a ∧ a < bCy + K) → ¬ (bPos ≤ a ∧ a < bPos + n) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 460 ∨ 466 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  obtain ⟨r330, r331, r332, r333, r334, r335, r336, r337, r338, r339, r340, -, -, -, -, r345,
    -⟩ := hB
  set g := cyNext A V NX with hg
  have hlt : ∀ i, g^[i] x₀ < 3 * k := cyNext_iter_lt hx₀ (fun x hx => (hA x hx).2)
    (fun x hx => (hV x hx).2) (fun v hv => (hN v hv).2)
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 460 = i ∧
    c'.nreg 451 = K ∧ i ≤ K ∧ c'.nreg 461 = g^[i] x₀ ∧
    (∀ j < i, c'.nmem (bCy + j) = g^[j] x₀) ∧
    (∀ j < i, c'.nmem (bPos + V (g^[j] x₀)) = j) ∧
    (∀ a, ¬ (bCy ≤ a ∧ a < bCy + K) → ¬ (bPos ≤ a ∧ a < bPos + n) → c'.nmem a = c.nmem a) ∧
    (∀ r, r < 460 ∨ 466 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 460 430, .copyN 461 445])
      c c₁ k₁ ∧ I 0 c₁ ∧ k₁ = 2 := by
    exec_block
    refine ⟨⟨‹_›, by config_simp; exact r330, by config_simp; exact h351, by omega,
      by config_simp; exact r345, fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega), fun a _ _ => rfl,
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl⟩, rfl⟩
  obtain ⟨c₂, t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 460) (rN := 451)
    (N := K) (lo := 0) (B := 14) (body := block cyBody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h360, h351', hin, h361, hCy, hPos, hf, hr, ho⟩ hi => by
      have g' : ∀ r, r < 460 → c₁.nreg r = c.nreg r := fun r hr' => hr r (Or.inl hr')
      have g331 : c₁.nreg 431 = 1 := by rw [g' 431 (by omega)]; exact r331
      have g333 : c₁.nreg 433 = bA := by rw [g' 433 (by omega)]; exact r333
      have g334 : c₁.nreg 434 = bV := by rw [g' 434 (by omega)]; exact r334
      have g338 : c₁.nreg 438 = bNx := by rw [g' 438 (by omega)]; exact r338
      have g339 : c₁.nreg 439 = bCy := by rw [g' 439 (by omega)]; exact r339
      have g340 : c₁.nreg 440 = bPos := by rw [g' 440 (by omega)]; exact r340
      set d := g^[i] x₀ with hd
      have hdk : d < 3 * k := hlt i
      obtain ⟨mV, hVd⟩ := hV _ hdk
      obtain ⟨mA, hAd⟩ := hA _ hdk
      obtain ⟨mV2, hV2⟩ := hV _ hAd
      obtain ⟨mN, hNn⟩ := hN _ hV2
      have m1 : c₁.nmem (bV + d) = V d := by rw [hf _ (by omega) (by omega)]; exact mV
      have m2 : c₁.nmem (bA + d) = A d := by rw [hf _ (by omega) (by omega)]; exact mA
      have m3 : c₁.nmem (bV + A d) = V (A d) := by rw [hf _ (by omega) (by omega)]; exact mV2
      have m4 : c₁.nmem (bNx + V (A d)) = NX (V (A d)) := by
        rw [hf _ (by omega) (by omega)]; exact mN
      have hnext : g^[i + 1] x₀ = NX (V (A d)) := by
        rw [Function.iterate_succ_apply', hg, cyNext]
      unfold cyBody
      exec_block
      all_goals try (config_simp; (try simp only [g334, h361, m1, g333, m2, m3, m4, g338,
        g339, h360, g340, g331]); omega)
      rename_i hwb
      simp only [g334, h361, m1, g333, m2, m3, m4, g338, g339, h360, g340, g331] at hwb ⊢
      refine ⟨⟨hwb, by config_simp, by config_simp; exact h351', by omega,
        by config_simp; exact hnext.symm, fun j hj => ?_, fun j hj => ?_, fun a ha1 ha2 => ?_,
        fun r hr' => ?_, by config_simp; exact ho⟩, by omega⟩
      · config_simp
        rw [upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact hCy j hj
        · rw [upd_same]
      · config_simp
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · have hne : V (g^[j] x₀) ≠ V d := fun e => by
            have := hinj j (by omega) i hi e; omega
          rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
          exact hPos j hj
        · rw [upd_same]
      · config_simp
        rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        exact hf a ha1 ha2
      · config_simp; simp only [upd_apply]
        split_ifs <;> first | omega | exact hr r hr')
    (by omega) hI₁
  obtain ⟨-, -, -, -, h361', hCy', hPos', hf', hr', ho'⟩ := hI
  exact ⟨c₂, 2 + t, .seq e₁ e, by omega, hCy', hPos', h361', hf', hr', ho'⟩

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The ancestor at level `≤ l`.** `n` guarded parent steps from `u` in the tree whose parent
darts are at `bPr` (read at the vertices of level `> l` only). -/
theorem taPass_exec {A V L Pr : ℕ → ℕ}
    (hW : bLv + n ≤ W ∧ bPr + n ≤ W ∧ bA + 3 * k ≤ W ∧ bV + 3 * k ≤ W) (c : Config)
    (hc : WordsBounded W c) (hB : BR bA bV bL k h bNx bCy bPos n bLv bPr l x₀ u c)
    (hu : u < n) (hL : ∀ v < n, c.nmem (bLv + v) = L v)
    (hPr : ∀ v < n, l < L v → c.nmem (bPr + v) = Pr v ∧ Pr v < 3 * k)
    (hA : ∀ x < 3 * k, c.nmem (bA + x) = A x ∧ A x < 3 * k)
    (hV : ∀ x < 3 * k, c.nmem (bV + x) = V x ∧ V x < n) :
    ∃ c' t, Exec P W taPass c c' t ∧ t ≤ 12 * n + 4 ∧
      c'.nreg 471 = (taNext L Pr A V l)^[n] u ∧ c'.nmem = c.nmem ∧
      (∀ r, r < 470 ∨ 474 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  obtain ⟨r330, r331, r332, r333, r334, r335, r336, r337, r338, r339, r340, r341, r342, r343,
    r344, r345, r346⟩ := hB
  set g := taNext L Pr A V l with hg
  have hlt : ∀ i, g^[i] u < n := taNext_iter_lt hu (fun v hv h => (hPr v hv h).2)
    (fun x hx => (hA x hx).2) (fun x hx => (hV x hx).2)
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 470 = i ∧
    c'.nreg 441 = n ∧ i ≤ n ∧ c'.nreg 471 = g^[i] u ∧ c'.nmem = c.nmem ∧
    (∀ r, r < 470 ∨ 474 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 470 430, .copyN 471 446])
      c c₁ k₁ ∧ I 0 c₁ ∧ k₁ = 2 := by
    exec_block
    refine ⟨⟨‹_›, by config_simp; exact r330, by config_simp; exact r341, by omega,
      by config_simp; exact r346, rfl,
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl⟩, rfl⟩
  obtain ⟨c₂, t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 470) (rN := 441)
    (N := n) (lo := 0) (B := 10) (body := taBody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h370, h341, hin, h371, hm, hr, ho⟩ hi => by
      have g' : ∀ r, r < 470 → c₁.nreg r = c.nreg r := fun r hr' => hr r (Or.inl hr')
      have g331 : c₁.nreg 431 = 1 := by rw [g' 431 (by omega)]; exact r331
      have g333 : c₁.nreg 433 = bA := by rw [g' 433 (by omega)]; exact r333
      have g334 : c₁.nreg 434 = bV := by rw [g' 434 (by omega)]; exact r334
      have g342 : c₁.nreg 442 = bLv := by rw [g' 442 (by omega)]; exact r342
      have g343 : c₁.nreg 443 = bPr := by rw [g' 443 (by omega)]; exact r343
      have g344 : c₁.nreg 444 = l := by rw [g' 444 (by omega)]; exact r344
      set v := g^[i] u with hv
      have hvn : v < n := hlt i
      have mL : c₁.nmem (bLv + v) = L v := by rw [hm]; exact hL v hvn
      have hnext : g^[i + 1] u = g v := Function.iterate_succ_apply' _ _ _
      unfold taBody
      refine spec_seq ?_
      exec_block
      · config_simp; rw [g342, h371]; omega
      rename_i hwb
      simp only [g342, h371, mL] at hwb ⊢
      refine spec_seq ?_
      have hstep : ∀ c₃ : Config, WordsBounded W c₃ → c₃.nreg 470 = i →
          (∀ r, r < 470 ∨ 474 ≤ r → c₃.nreg r = c.nreg r) → c₃.nmem = c.nmem →
          c₃.output = c.output → c₃.nreg 471 = g^[i + 1] u →
          ∃ c' k, Exec P W (.instr (.addN 470 470 431)) c₃ c' k ∧ I (i + 1) c' ∧ k ≤ 1 := by
        intro c₃ hw₃ e370 er em eo e371
        have e331 : c₃.nreg 431 = 1 := (er 431 (Or.inl (by omega))).trans r331
        have e341 : c₃.nreg 441 = n := (er 441 (Or.inl (by omega))).trans r341
        have ea := Exec.addN (P := P) hw₃ 470 470 431 (by rw [e370, e331]; omega)
        refine ⟨_, 1, ea, ⟨ea.wb_right, by config_simp; rw [e370, e331],
          by config_simp; exact e341, by omega, by config_simp; exact e371,
          by config_simp; exact em, fun r hr' => ?_, by config_simp; exact eo⟩, le_rfl⟩
        config_simp; simp only [upd_apply]
        split_ifs with h'
        · omega
        · exact er r hr'
      by_cases hlv : l < L v
      · refine spec_ifLtN_true (by config_simp; rw [g344]; exact hlv) ?_
        obtain ⟨mP, hPv⟩ := hPr v hvn hlv
        obtain ⟨mA, hAv⟩ := hA _ hPv
        obtain ⟨mV, hVv⟩ := hV _ hAv
        have m1 : c₁.nmem (bPr + v) = Pr v := by rw [hm]; exact mP
        have m2 : c₁.nmem (bA + Pr v) = A (Pr v) := by rw [hm]; exact mA
        have m3 : c₁.nmem (bV + A (Pr v)) = V (A (Pr v)) := by rw [hm]; exact mV
        unfold taStep
        exec_block
        all_goals try (config_simp; (try simp only [g343, h371, m1, g333, m2, g334, m3]); omega)
        rename_i hwd
        simp only [g343, h371, m1, g333, m2, g334, m3] at hwd ⊢
        obtain ⟨c', k', e', hI', hk'⟩ := hstep _ hwd (by config_simp; exact h370)
          (fun r hr' => by
            config_simp; simp only [upd_apply]
            split_ifs <;> first | omega | exact hr r hr')
          (by config_simp; exact hm) (by config_simp; exact ho)
          (by
            config_simp
            rw [hnext, hg, taNext, ite_eq_left_of_eq_true _ _ (eq_true hlv)])
        exact ⟨c', k', e', hI', by omega⟩
      · refine spec_ifLtN_false (by config_simp; rw [g344]; exact hlv) ?_
        refine spec_skip ‹_› ?_
        obtain ⟨c', k', e', hI', hk'⟩ := hstep _ ‹_› (by config_simp; exact h370)
          (fun r hr' => by
            config_simp; simp only [upd_apply]
            split_ifs <;> first | omega | exact hr r hr')
          (by config_simp; exact hm) (by config_simp; exact ho)
          (by
            config_simp
            rw [hnext, hg, taNext, ite_eq_right_of_eq_false _ _ (eq_false hlv)]
            exact h371)
        exact ⟨c', k', e', hI', by omega⟩)
    (by omega) hI₁
  obtain ⟨-, -, -, -, h371', hm', hr', ho'⟩ := hI
  exact ⟨c₂, 2 + t, .seq e₁ e, by omega, h371', hm', hr', ho'⟩

end proofs2

/-! ### The parent darts of the tree redirected along an arc -/

/-- **One copied parent dart** `r390 = v`: `bPr2 + v := bPr + v`. -/
def cpBody : List Instr :=
  [.addN 491 443 490, .loadN 492 491, .addN 491 449 490, .storeN 491 492, .addN 490 490 431]

/-- **A copy of the parent darts** at `bPr2 = r349`. -/
def cpPass : Stmt := .seq (.instr (.copyN 490 430)) (.whileLtN 490 441 (block cpBody))

/-- The index `m` steps after `s` on a cycle of length `K` (as `PlanarSeparator.Map.SCycle.idxAt`). -/
def idxN (K s m : ℕ) : ℕ := if s + m < K then s + m else s + m - K

/-- **One step of the arc** `r380 = j`, `r381 = idxN K s j`: the next index `r382`, and the
parent dart of the vertex of the cycle there becomes the reversal of the dart of the cycle at
`r381`. -/
def arBody : Stmt :=
  .seq (block [.addN 482 481 431])
    (.seq (.ifLtN 482 451 .skip (.instr (.copyN 482 430)))
      (block [.addN 483 439 482, .loadN 484 483, .addN 483 434 484, .loadN 485 483,
        .addN 483 439 481, .loadN 484 483, .addN 483 433 484, .loadN 486 483,
        .addN 483 449 485, .storeN 483 486, .copyN 481 482, .addN 480 480 431]))

/-- **The redirection along the arc** of `ℓ = r348` steps from the index `s = r347` of the cycle
at `bCy` (of length `K = r351`), into the parent darts at `bPr2 = r349`. -/
def arPass : Stmt := .seq (block [.copyN 480 430, .copyN 481 447]) (.whileLtN 480 448 arBody)

lemma idxN_succ {K s m : ℕ} (hs : s < K) (hm : m + 1 < K) :
    (if idxN K s m + 1 < K then idxN K s m + 1 else 0) = idxN K s (m + 1) := by
  unfold idxN; split_ifs <;> omega

lemma idxN_lt {K s m : ℕ} (hs : s < K) (hm : m < K) : idxN K s m < K := by
  unfold idxN; split_ifs <;> omega

lemma idxN_inj {K s m m' : ℕ} (hm : m < K) (hm' : m' < K)
    (h : idxN K s m = idxN K s m') : m = m' := by
  unfold idxN at h; split_ifs at h <;> omega

section proofs3

variable {k : ℕ} {W : ℕ} {P : Input}
  {bA bV bL h bNx bCy bPos n bLv bPr l x₀ u : ℕ}

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The copy of the parent darts.** -/
theorem cpPass_exec {bPr2 : ℕ} (hlay : bPr + n ≤ bPr2) (hW : bPr2 + n ≤ W) (c : Config)
    (hc : WordsBounded W c) (hB : BR bA bV bL k h bNx bCy bPos n bLv bPr l x₀ u c)
    (h349 : c.nreg 449 = bPr2) :
    ∃ c' t, Exec P W cpPass c c' t ∧ t ≤ 7 * n + 3 ∧
      (∀ v < n, c'.nmem (bPr2 + v) = c.nmem (bPr + v)) ∧
      (∀ a, a < bPr2 ∨ bPr2 + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 490 ∨ 493 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  obtain ⟨r330, r331, -, -, -, -, -, -, -, -, -, r341, -, r343, -, -, -⟩ := hB
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 490 = i ∧
    c'.nreg 441 = n ∧ i ≤ n ∧ (∀ v < i, c'.nmem (bPr2 + v) = c.nmem (bPr + v)) ∧
    (∀ a, a < bPr2 ∨ bPr2 + i ≤ a → c'.nmem a = c.nmem a) ∧
    (∀ r, r < 490 ∨ 493 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output
  have e₁ := Exec.copyN (P := P) hc 490 430
  obtain ⟨c₂, t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 490) (rN := 441)
    (N := n) (lo := 0) (B := 5) (body := block cpBody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h390, h341, hin, hcp, hf, hr, ho⟩ hi => by
      have g' : ∀ r, r < 490 → c₁.nreg r = c.nreg r := fun r hr' => hr r (Or.inl hr')
      have g331 : c₁.nreg 431 = 1 := by rw [g' 431 (by omega)]; exact r331
      have g343 : c₁.nreg 443 = bPr := by rw [g' 443 (by omega)]; exact r343
      have g349 : c₁.nreg 449 = bPr2 := by rw [g' 449 (by omega)]; exact h349
      have m1 : c₁.nmem (bPr + i) = c.nmem (bPr + i) := hf _ (Or.inl (by omega))
      unfold cpBody
      exec_block
      all_goals try (config_simp; (try simp only [g343, h390, g349, g331, m1]); omega)
      rename_i hwb
      simp only [g343, h390, g349, g331, m1] at hwb ⊢
      refine ⟨⟨hwb, by config_simp, by config_simp; exact h341, by omega, fun v hv => ?_,
        fun a ha => ?_, fun r hr' => ?_, by config_simp; exact ho⟩, by omega⟩
      · config_simp
        rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
        · rw [upd_other _ _ _ (by omega)]; exact hcp v hv
        · rw [upd_same]
      · config_simp
        rw [upd_other _ _ _ (by omega)]; exact hf a (by omega)
      · config_simp; simp only [upd_apply]
        split_ifs <;> first | omega | exact hr r hr')
    (by omega) ⟨e₁.wb_right, by config_simp; exact r330, by config_simp; exact r341, by omega,
      fun v hv => absurd hv (by omega), fun a _ => rfl, fun r hr => by
        show upd c.nreg 490 (c.nreg 430) r = c.nreg r
        simp only [upd_apply]; split_ifs <;> omega, rfl⟩
  obtain ⟨-, -, -, -, hcp', hf', hr', ho'⟩ := hI
  exact ⟨c₂, 1 + t, .seq e₁ e, by omega, hcp', hf', hr', ho'⟩

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The redirection along an arc.** For the cycle of the darts `cy i`, `i < K`, at `bCy`, with
distinct vertices: after `arPass`, for `1 ≤ j ≤ ℓ` the cell of the vertex of the cycle `j` steps
after `s` holds the reversal `A` of the dart of the cycle `j - 1` steps after `s`, and the other
cells of `[bPr2, bPr2 + n)` are unchanged. -/
theorem arPass_exec {A V cy : ℕ → ℕ} {K s ℓ bPr2 : ℕ}
    (hlay : bA + 3 * k ≤ bPr2 ∧ bV + 3 * k ≤ bPr2 ∧ bCy + K ≤ bPr2) (hW : bPr2 + n ≤ W)
    (c : Config) (hc : WordsBounded W c) (hB : BR bA bV bL k h bNx bCy bPos n bLv bPr l x₀ u c)
    (h351 : c.nreg 451 = K) (h347 : c.nreg 447 = s) (h348 : c.nreg 448 = ℓ)
    (h349 : c.nreg 449 = bPr2) (hs : s < K) (hℓ : ℓ < K)
    (hcy : ∀ i < K, c.nmem (bCy + i) = cy i ∧ cy i < 3 * k)
    (hA : ∀ x < 3 * k, c.nmem (bA + x) = A x ∧ A x < 3 * k)
    (hV : ∀ x < 3 * k, c.nmem (bV + x) = V x ∧ V x < n)
    (hinj : ∀ i < K, ∀ j < K, V (cy i) = V (cy j) → i = j) :
    ∃ c' t, Exec P W arPass c c' t ∧ t ≤ 19 * ℓ + 4 ∧
      (∀ j, 1 ≤ j → j ≤ ℓ →
        c'.nmem (bPr2 + V (cy (idxN K s j))) = A (cy (idxN K s (j - 1)))) ∧
      (∀ v < n, (∀ j, 1 ≤ j → j ≤ ℓ → v ≠ V (cy (idxN K s j))) →
        c'.nmem (bPr2 + v) = c.nmem (bPr2 + v)) ∧
      (∀ a, a < bPr2 ∨ bPr2 + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 480 ∨ 487 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  obtain ⟨r330, r331, -, r333, r334, -, -, -, -, r339, -, -, -, -, -, -, -⟩ := hB
  let I : ℕ → Config → Prop := fun j c' => WordsBounded W c' ∧ c'.nreg 480 = j ∧
    c'.nreg 448 = ℓ ∧ j ≤ ℓ ∧ c'.nreg 481 = idxN K s j ∧
    (∀ j', 1 ≤ j' → j' ≤ j →
      c'.nmem (bPr2 + V (cy (idxN K s j'))) = A (cy (idxN K s (j' - 1)))) ∧
    (∀ v < n, (∀ j', 1 ≤ j' → j' ≤ j → v ≠ V (cy (idxN K s j'))) →
      c'.nmem (bPr2 + v) = c.nmem (bPr2 + v)) ∧
    (∀ a, a < bPr2 ∨ bPr2 + n ≤ a → c'.nmem a = c.nmem a) ∧
    (∀ r, r < 480 ∨ 487 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 480 430, .copyN 481 447])
      c c₁ k₁ ∧ I 0 c₁ ∧ k₁ = 2 := by
    exec_block
    refine ⟨⟨‹_›, by config_simp; exact r330, by config_simp; exact h348, by omega,
      by config_simp; rw [h347]; unfold idxN; simp [hs], fun j' h1 h2 => absurd h2 (by omega),
      fun v _ _ => rfl, fun a _ => rfl,
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl⟩, rfl⟩
  obtain ⟨c₂, t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 480) (rN := 448)
    (N := ℓ) (lo := 0) (B := 17) (body := arBody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c₁ ⟨hw₁, h380, h348', hin, h381, hw, hu, hf, hr, ho⟩ hj => by
      have g' : ∀ r, r < 480 → c₁.nreg r = c.nreg r := fun r hr' => hr r (Or.inl hr')
      have g330 : c₁.nreg 430 = 0 := by rw [g' 430 (by omega)]; exact r330
      have g331 : c₁.nreg 431 = 1 := by rw [g' 431 (by omega)]; exact r331
      have g333 : c₁.nreg 433 = bA := by rw [g' 433 (by omega)]; exact r333
      have g334 : c₁.nreg 434 = bV := by rw [g' 434 (by omega)]; exact r334
      have g339 : c₁.nreg 439 = bCy := by rw [g' 439 (by omega)]; exact r339
      have g349 : c₁.nreg 449 = bPr2 := by rw [g' 449 (by omega)]; exact h349
      have g351 : c₁.nreg 451 = K := by rw [g' 451 (by omega)]; exact h351
      set i := idxN K s j with hi
      set i' := idxN K s (j + 1) with hi'
      have hik : i < K := idxN_lt hs (by omega)
      have hik' : i' < K := idxN_lt hs (by omega)
      obtain ⟨mc, hck⟩ := hcy i hik
      obtain ⟨mc', hck'⟩ := hcy i' hik'
      obtain ⟨mA, hAc⟩ := hA _ hck
      obtain ⟨mV, hVc⟩ := hV _ hck'
      have m1 : c₁.nmem (bCy + i') = cy i' := by rw [hf _ (Or.inl (by omega))]; exact mc'
      have m2 : c₁.nmem (bV + cy i') = V (cy i') := by rw [hf _ (Or.inl (by omega))]; exact mV
      have m3 : c₁.nmem (bCy + i) = cy i := by rw [hf _ (Or.inl (by omega))]; exact mc
      have m4 : c₁.nmem (bA + cy i) = A (cy i) := by rw [hf _ (Or.inl (by omega))]; exact mA
      have hdist : ∀ j', 1 ≤ j' → j' ≤ j → V (cy (idxN K s j')) ≠ V (cy i') := by
        intro j' h1 h2 e
        have := idxN_inj (by omega) (by omega)
          (hinj _ (idxN_lt hs (by omega)) _ hik' e)
        omega
      have hfin : ∀ c₂ : Config, WordsBounded W c₂ → c₂.nreg 482 = i' → c₂.nreg 481 = i →
          c₂.nreg 480 = j → (∀ r, r < 480 ∨ 483 ≤ r → c₂.nreg r = c₁.nreg r) →
          c₂.nmem = c₁.nmem → c₂.output = c₁.output →
          ∃ c' k, Exec P W (block [.addN 483 439 482, .loadN 484 483, .addN 483 434 484,
            .loadN 485 483, .addN 483 439 481, .loadN 484 483, .addN 483 433 484,
            .loadN 486 483, .addN 483 449 485, .storeN 483 486, .copyN 481 482,
            .addN 480 480 431]) c₂ c' k ∧ I (j + 1) c' ∧ k ≤ 12 := by
        intro c₂ hw₂ f382 f381 f380 fr fm fo
        have f339 : c₂.nreg 439 = bCy := (fr 439 (by omega)).trans g339
        have f334 : c₂.nreg 434 = bV := (fr 434 (by omega)).trans g334
        have f333 : c₂.nreg 433 = bA := (fr 433 (by omega)).trans g333
        have f349 : c₂.nreg 449 = bPr2 := (fr 449 (by omega)).trans g349
        have f331 : c₂.nreg 431 = 1 := (fr 431 (by omega)).trans g331
        have f348 : c₂.nreg 448 = ℓ := (fr 448 (by omega)).trans h348'
        rw [← fm] at m1 m2 m3 m4
        exec_block
        all_goals try (config_simp; (try simp only [f339, f382, m1, f334, m2, f381, m3, f333,
          m4, f349, f380, f331]); omega)
        rename_i hwb
        simp only [f339, f382, m1, f334, m2, f381, m3, f333, m4, f349, f380, f331] at hwb ⊢
        refine ⟨⟨hwb, by config_simp, by config_simp; exact f348, by omega,
          by config_simp; exact hi', fun j' h1 h2 => ?_, fun v hv hne => ?_, fun a ha => ?_, fun r hr' => ?_,
          by config_simp; rw [fo, ho]⟩, by omega⟩
        · config_simp
          rcases Nat.lt_or_ge j' (j + 1) with h2 | h2
          · rw [upd_other _ _ _ (by have := hdist j' h1 (by omega); omega), fm]
            exact hw j' h1 (by omega)
          · obtain rfl : j' = j + 1 := by omega
            rw [← hi', upd_same, show j + 1 - 1 = j by omega]
        · config_simp
          rw [upd_other _ _ _ (by
            have := hne (j + 1) (by omega) le_rfl
            rw [← hi'] at this
            omega), fm]
          exact hu v hv fun j' h1 h2 => hne j' h1 (by omega)
        · config_simp
          rw [upd_other _ _ _ (by have := hVc; omega), fm]; exact hf a ha
        · config_simp; simp only [upd_apply]
          split_ifs <;> first | omega | (rw [fr r (by omega)]; exact hr r hr')
      unfold arBody
      refine spec_seq ?_
      exec_block
      · config_simp; rw [h381, g331]; have := hw₁.1 481; omega
      rename_i hwa
      simp only [h381, g331] at hwa ⊢
      refine spec_seq ?_
      have hsucc := idxN_succ (K := K) (s := s) (m := j) hs (by omega)
      rw [← hi] at hsucc
      by_cases hlt : i + 1 < K
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hlt)] at hsucc
        refine spec_ifLtN_true (by config_simp; rw [g351]; exact hlt) ?_
        refine spec_skip ‹_› ?_
        obtain ⟨c', k', e', hI', hk'⟩ := hfin _ ‹_› (by config_simp; exact hsucc)
          (by config_simp; exact h381) (by config_simp; exact h380)
          (fun r hr' => by config_simp; simp only [upd_apply]; split_ifs <;> omega)
          (by config_simp) (by config_simp)
        exact ⟨c', k', e', hI', by omega⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hlt)] at hsucc
        refine spec_ifLtN_false (by config_simp; rw [g351]; exact hlt) ?_
        refine spec_instr (Exec.copyN ‹_› 482 430) fun hw₃ => ?_
        obtain ⟨c', k', e', hI', hk'⟩ := hfin _ hw₃ (by config_simp; rw [g330]; exact hsucc)
          (by config_simp; exact h381) (by config_simp; exact h380)
          (fun r hr' => by config_simp; simp only [upd_apply]; split_ifs <;> omega)
          (by config_simp) (by config_simp)
        exact ⟨c', k', e', hI', by omega⟩)
    (by omega) hI₁
  obtain ⟨-, -, -, -, -, hw', hu', hf', hr', ho'⟩ := hI
  exact ⟨c₂, 2 + t, .seq e₁ e, by omega, hw', hu', hf', hr', ho'⟩

end proofs3

/-! ### Through the coding -/

section Bridge

open Map

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] {M : Map D P}
  {k n : ℕ} (cd : D ≃ Fin (3 * k)) (vi : P ≃ Fin n) {A V : ℕ → ℕ}
  (hA : ∀ x, A (cd x) = cd (M.α x)) (hV : ∀ x, V (cd x) = vi (M.vert x))

include hA in
/-- The numeric test of a dart leaving the component is `PlanarSeparator.Map.Out`, if the faces
with the label `h` are those of `Y` (as `PlanarSeparator.MillerProg.lab_iff_comp` gives). -/
theorem lv_iff_out {lb : ℕ → ℕ} {h : ℕ} {Y : Finset M.Face}
    (hlab : ∀ y : D, lb ((cd y : ℕ) / 3) = h ↔ M.face y ∈ Y) (y : D) :
    Lv lb A h (cd y) ↔ Out Y y := by
  unfold Lv Out
  rw [hA, hlab, ne_eq, hlab]

omit [Fintype P] in
/-- **The count of `bdPass` is the length of the boundary cycle.** -/
theorem nOut_eq_bdK {lb : ℕ → ℕ} {h : ℕ} {Y : Finset M.Face}
    (hlv : ∀ y : D, Lv lb A h (cd y) ↔ Out Y y) : nOut lb A h (3 * k) = bdK Y := by
  classical
  rw [bdK, ← card_image_of_injective _ (fun x y e => cd.injective (Fin.ext e) :
    Function.Injective fun x : D => (cd x : ℕ))]
  unfold nOut
  congr 1
  ext x
  simp only [mem_filter, mem_range, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨hx, hl⟩
    refine ⟨cd.symm ⟨x, hx⟩, ?_, by simp⟩
    rw [← hlv, Equiv.apply_symm_apply]
    exact hl
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(cd y).2, (hlv y).2 hy⟩

include hA hV in
/-- **The walk of `cyWalk` is the boundary cycle.** If the cell of every vertex at which a dart
leaves `Y` holds such a dart (as after `bdPass`), the walk `cyNext` from the dart `cd x₀` runs
through the codes of the darts `bdD Y x₀ i` of `PlanarSeparator.Map.bdCycle`. -/
theorem cyNext_iter_bdD {NX lb : ℕ → ℕ} {h : ℕ} {Y : Finset M.Face}
    (hlv : ∀ y : D, Lv lb A h (cd y) ↔ Out Y y) (hN : ∀ v < n, NX v < 3 * k)
    (hP : ∀ v < n, (∃ x < 3 * k, Lv lb A h x ∧ V x = v) →
      ∃ x < 3 * k, Lv lb A h x ∧ V x = v ∧ NX v = x)
    {x₀ : D} (hok : BdOK Y x₀) (i : ℕ) :
    (cyNext A V NX)^[i] (cd x₀) = cd (bdD Y x₀ i) := by
  set nxM : P → D := fun p => cd.symm ⟨NX (vi p), hN _ (vi p).2⟩ with hnxM
  have hcd : ∀ p, (cd (nxM p) : ℕ) = NX (vi p) := fun p => by simp [hnxM]
  have hnx : ∀ y, Out Y y → Out Y (nxM (M.vert y)) ∧ M.vert (nxM (M.vert y)) = M.vert y := by
    intro y hy
    obtain ⟨x, hx, hl, hxv, hNx⟩ := hP _ (vi (M.vert y)).2
      ⟨cd y, (cd y).2, (hlv y).2 hy, hV y⟩
    have e : (cd (nxM (M.vert y)) : ℕ) = x := by rw [hcd, hNx]
    refine ⟨?_, ?_⟩
    · rw [← hlv, e]; exact hl
    · apply vi.injective
      apply Fin.ext
      rw [← hV, e, hxv]
  rw [bdD_eq_iterate hok nxM hnx i]
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, cyNext, hA, hV, hcd]

include hA hV in
/-- The vertices of the walk are distinct over the length of the boundary cycle (the hypothesis
of the positions in `cyWalk_exec`). -/
theorem cyNext_inj {NX lb : ℕ → ℕ} {h : ℕ} {Y : Finset M.Face}
    (hlv : ∀ y : D, Lv lb A h (cd y) ↔ Out Y y) (hN : ∀ v < n, NX v < 3 * k)
    (hP : ∀ v < n, (∃ x < 3 * k, Lv lb A h x ∧ V x = v) →
      ∃ x < 3 * k, Lv lb A h x ∧ V x = v ∧ NX v = x)
    {x₀ : D} (hok : BdOK Y x₀) :
    ∀ i < bdK Y, ∀ j < bdK Y, V ((cyNext A V NX)^[i] (cd x₀)) =
      V ((cyNext A V NX)^[j] (cd x₀)) → i = j := by
  intro i hi j hj e
  rw [cyNext_iter_bdD cd vi hA hV hlv hN hP hok, cyNext_iter_bdD cd vi hA hV hlv hN hP hok,
    hV, hV] at e
  have := (bdCycle Y x₀ hok).inj i hi j hj (vi.injective (Fin.ext e))
  exact this

include hA hV in
/-- **The guarded parent steps of `taPass` through the coding**: with the levels `L` of `T` and
the parent darts `Pr` of `T₁`, `taNext` follows the guarded parent steps of
`PlanarSeparator.Map.topA_eq_iterate`. -/
theorem taNext_iter_eq {T T₁ : M.SpTree} {l : ℕ} {L Pr : ℕ → ℕ}
    (hL : ∀ v, L (vi v) = T.height v)
    (hPr : ∀ v (hv : v ≠ T₁.root), Pr (vi v) = cd (T₁.par v hv))
    (hr : T.height T₁.root ≤ l) (N : ℕ) (u : P) :
    (taNext L Pr A V l)^[N] (vi u) =
      vi ((fun v => if l < T.height v then T₁.parent v else v)^[N] u) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    set v := (fun v => if l < T.height v then T₁.parent v else v)^[N] u
    unfold taNext
    rw [hL]
    by_cases hv : l < T.height v
    · have hne : v ≠ T₁.root := fun e => by rw [e] at hv; omega
      simp only [hv, ↓reduceIte]
      rw [hPr v hne, hA, hV, T₁.parent_of_ne hne]
    · simp only [hv, ↓reduceIte]

include hA hV in
/-- **The ancestor at level `l` on the machine**: `n` guarded steps of `taPass` from `vi u` give
`vi (topA T T₁ l u)`. -/
theorem taNext_topA {T T₁ : M.SpTree} {l : ℕ} {L Pr : ℕ → ℕ}
    (hL : ∀ v, L (vi v) = T.height v)
    (hPr : ∀ v (hv : v ≠ T₁.root), Pr (vi v) = cd (T₁.par v hv))
    (hr : T.height T₁.root ≤ l) (u : P) :
    (taNext L Pr A V l)^[n] (vi u) = vi (topA T T₁ l u) := by
  rw [taNext_iter_eq cd vi hA hV hL hPr hr, topA_eq_iterate hr u
    (by rw [Fintype.card_congr vi, Fintype.card_fin])]

include hA hV in
/-- **The parent darts of `arPass` are those of the arc tree.** If `Pr` codes the parent darts
of `T₁`, the cycle array `cy` codes the darts of `C`, and `Pr2` is `Pr` changed as by `cpPass`
and `arPass` (the arc of `ℓ` steps from `s`), then `Pr2` codes the parent darts of
`T₁.arcTree C s ℓ` (`PlanarSeparator.Map.SpTree.arcTree`). -/
theorem arcTree_par_code {T₁ : M.SpTree} (C : M.SCycle) {s ℓ : ℕ} (hs : s < C.k)
    (hr : T₁.root ∉ C.verts)
    (hC : ∀ i < C.k, T₁.height (M.vert (C.d i)) = T₁.height (M.vert (C.d s))) (hℓ : ℓ < C.k)
    {cy Pr Pr2 : ℕ → ℕ} (hcy : ∀ i < C.k, cy i = cd (C.d i))
    (hPr : ∀ v (hv : v ≠ T₁.root), Pr (vi v) = cd (T₁.par v hv))
    (h1 : ∀ j, 1 ≤ j → j ≤ ℓ → Pr2 (V (cy (idxN C.k s j))) = A (cy (idxN C.k s (j - 1))))
    (h2 : ∀ v < n, (∀ j, 1 ≤ j → j ≤ ℓ → v ≠ V (cy (idxN C.k s j))) → Pr2 v = Pr v)
    (v : P) (hv : v ≠ (T₁.arcTree C s ℓ hs hr hC).root) :
    Pr2 (vi v) = cd ((T₁.arcTree C s ℓ hs hr hC).par v hv) := by
  have hv' : v ≠ T₁.root := hv
  have hidx : ∀ m, idxN C.k s m = C.idxAt s m := fun m => rfl
  by_cases hR : v ∈ C.arcR s ℓ
  · obtain ⟨hvC, hj1, hj2⟩ := C.mem_arcR.1 hR
    obtain ⟨hik, hiv⟩ := C.idx_spec hvC
    have hjk : C.off s (C.idx v) < C.k := C.off_lt hs hik
    have hat : C.idxAt s (C.off s (C.idx v)) = C.idx v := C.idxAt_off hs hik
    have e1 : V (cy (idxN C.k s (C.off s (C.idx v)))) = vi v := by
      rw [hidx, hat, hcy _ hik, hV, hiv]
    show Pr2 (vi v) = cd ((T₁.redirect _ _ _ _ _ _ _ _ _).par v hv)
    rw [SpTree.redirect_par_of_mem T₁ hv' hR, ← e1, h1 _ hj1 hj2, SCycle.arcNxt]
    have hpre : C.pre (C.idx v) = C.idxAt s (C.off s (C.idx v) - 1) := by
      have := C.pre_idxAt hs (m := C.off s (C.idx v) - 1) (by omega)
      rwa [Nat.sub_add_cancel hj1, hat] at this
    rw [hpre, hidx, hcy _ (C.idxAt_lt hs (by omega)), hA]
  · show Pr2 (vi v) = cd ((T₁.redirect _ _ _ _ _ _ _ _ _).par v hv)
    rw [SpTree.redirect_par_of_notMem T₁ hv' hR, h2 _ (vi v).2 ?_, hPr v hv']
    intro j hj1 hj2 e
    apply hR
    have hjk : j < C.k := by omega
    have hik := C.idxAt_lt hs hjk
    rw [hidx, hcy _ hik, hV] at e
    have hvv : v = M.vert (C.d (C.idxAt s j)) := vi.injective (Fin.ext e)
    rw [C.mem_arcR, hvv, C.idx_vert hik, C.off_idxAt hs hjk]
    exact ⟨C.mem_verts.2 ⟨_, hik, rfl⟩, hj1, hj2⟩

end Bridge

end MillerProg

end PlanarSeparator
