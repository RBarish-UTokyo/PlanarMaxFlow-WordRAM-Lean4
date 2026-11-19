module

public import PlanarSeparator.Machine.MillerInside

/-!
# Miller's separator on the machine: the weights of the two sides of a fundamental cycle

For the choice of the side in the deep case of step 9 (`PlanarSeparator.Map.deepWant`: the
comparison of the moved weights of `inC δ` and `outC δ`), the weights of the strict inside and of
the strict outside of the fundamental cycle of `δ` are recomputed in `O(n)` steps from the darts of
the cycle (`fcProg`, at `bFc`, `K = r514` of them) and the inside marks (`imLoop`, at `bIm`, flag
`r539`):

* `cvMark`: the vertices of the darts of the cycle get the stamp `s₂` at `bCv` (`cvMark_exec`,
  `9 K + 3` steps);
* `ztest`: the zone test of the face of a dart, `flagF` from the levels of its three corners
  (`ztest_exec`, `30` steps; `ztest_zone`: the face avoids the levels `< l` iff it is positive);
* `wPass`: one pass over the vertices: a vertex off the cycle is inside if the mark of the face of
  its dart `fd v` (at `bF + v`) differs from the flag; its weight (at `bw + v`) is added to `r562`
  (inside) or `r563` (outside) (`wPass_exec`, `25 n + 5` steps).

**`weigh_sides`**: through the coding, `r562 = ∑ v ∈ T.inC δ, w v` and `r563 = ∑ v ∈ T.outC δ, w v`.

For the decisions of `PlanarSeparator.Map.deepSep`: `third_le_iff` (the heavy test `1/3 ≤`
as `tot ≤ 3 S` in natural numbers), `lighter_iff` (the comparison of the moved weights of the two
sides as one of natural numbers) and `deepWant_iff` (the wanted side as the test at the
representative of `Y`).

Registers: inputs those of `FR` (`fcProg`) and `IR` (`imLoop`), `r551 = bCv`, `r552 = s₂`,
`r553 = bF`, `r554 = bw`; written `r556 … r563`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-- **The vertex of the `r556`-th dart of the cycle** gets the stamp. -/
def cvBody : List Instr :=
  [.addN 557 508 556, .loadN 557 557, .addN 557 502 557, .loadN 557 557, .addN 557 551 557,
    .storeN 557 552, .addN 556 556 511]

/-- **The marks of the vertices of the cycle.** -/
def cvMark : Stmt := .seq (.instr (.copyN 556 510)) (.whileLtN 556 514 (block cvBody))

/-- The face of the dart of `r559 = v` and the comparison of its mark with the flag. -/
def wFace : List Instr :=
  [.addN 557 553 559, .loadN 557 557, .divN 557 557 535, .addN 557 531 557, .loadN 557 557,
    .subN 558 557 539, .subN 557 539 557, .addN 558 558 557]

/-- **One vertex** `r559 = v`. -/
def wBody : Stmt :=
  .seq (block [.addN 557 551 559, .loadN 558 557, .subN 560 558 552, .subN 557 552 558,
      .addN 560 560 557, .addN 557 554 559, .loadN 561 557])
    (.seq (.ifLtN 560 511 .skip
        (.seq (block wFace) (.ifLtN 558 511 (.instr (.addN 563 563 561))
          (.instr (.addN 562 562 561)))))
      (.instr (.addN 559 559 511)))

/-- **The weights of the two sides.** -/
def wPass : Stmt := .seq (block [.copyN 559 510, .copyN 562 510, .copyN 563 510])
  (.whileLtN 559 505 wBody)


/-- The level of the corner `r571 + j` of the face, compared with `l = r566`: `r570 := 0` if it is
below. -/
def zCorner (j : ℕ) : Stmt :=
  .seq (block [.constN 572 j, .addN 572 571 572, .addN 569 502 572, .loadN 569 569,
      .addN 569 567 569, .loadN 569 569])
    (.ifLtN 569 566 (.instr (.copyN 570 510)) .skip)

/-- **The zone test of the face of the dart `r565`**: `r570 = flagF l V L (r565 / 3)` (`1` if all
three corners have level `≥ l`). -/
def ztest : Stmt :=
  .seq (block [.divN 571 565 535, .mulN 571 571 535, .copyN 570 511])
    (.seq (zCorner 0) (.seq (zCorner 1) (zCorner 2)))

/-- The numeric test of a vertex inside: off the cycle, with a face marked differently from the
flag. -/
def InN (cv fdN im : ℕ → ℕ) (s₂ fl v : ℕ) : Prop := cv v ≠ s₂ ∧ im (fdN v / 3) ≠ fl

/-- Outside: off the cycle, with a face marked as the flag. -/
def OutN (cv fdN im : ℕ → ℕ) (s₂ fl v : ℕ) : Prop := cv v ≠ s₂ ∧ im (fdN v / 3) = fl

section proofs

variable {k : ℕ} {W : ℕ} {P : Input} {δ bA bV bPr r₀ n bMk s bFc bTmp : ℕ}

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The marks of the vertices of the cycle.** -/
theorem cvMark_exec {V cy : ℕ → ℕ} {K bCv s₂ : ℕ} (hlay : bV + 3 * k ≤ bCv ∧ bFc + K ≤ bCv)
    (hW : bCv + n ≤ W) (c : Config) (hc : WordsBounded W c)
    (hF : FR δ bA bV bPr r₀ n bMk s bFc bTmp c) (h514 : c.nreg 514 = K)
    (h551 : c.nreg 551 = bCv) (h552 : c.nreg 552 = s₂)
    (hcy : ∀ j < K, c.nmem (bFc + j) = cy j ∧ cy j < 3 * k)
    (hV : ∀ x < 3 * k, c.nmem (bV + x) = V x ∧ V x < n) :
    ∃ c' t, Exec P W cvMark c c' t ∧ t ≤ 9 * K + 3 ∧
      (∀ v < n, (∃ j < K, V (cy j) = v) → c'.nmem (bCv + v) = s₂) ∧
      (∀ v < n, (¬ ∃ j < K, V (cy j) = v) → c'.nmem (bCv + v) = c.nmem (bCv + v)) ∧
      (∀ a, a < bCv ∨ bCv + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 556 → r ≠ 557 → c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  obtain ⟨-, -, r502, -, -, -, -, -, r508, -, r510, r511⟩ := hF
  let I : ℕ → Config → Prop := fun j c' => WordsBounded W c' ∧ c'.nreg 556 = j ∧
    c'.nreg 514 = K ∧ j ≤ K ∧
    (∀ v < n, (∃ j' < j, V (cy j') = v) → c'.nmem (bCv + v) = s₂) ∧
    (∀ v < n, (¬ ∃ j' < j, V (cy j') = v) → c'.nmem (bCv + v) = c.nmem (bCv + v)) ∧
    (∀ a, a < bCv ∨ bCv + n ≤ a → c'.nmem a = c.nmem a) ∧
    (∀ r, r ≠ 556 → r ≠ 557 → c'.nreg r = c.nreg r) ∧ c'.output = c.output
  have e₁ := Exec.copyN (P := P) hc 556 510
  obtain ⟨c₂, t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 556) (rN := 514)
    (N := K) (lo := 0) (B := 7) (body := block cvBody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c₁ ⟨hw₁, h556, h514', hj', hM1, hM2, hf, hr, ho⟩ hj => by
      have g502 : c₁.nreg 502 = bV := by rw [hr 502 (by omega) (by omega)]; exact r502
      have g508 : c₁.nreg 508 = bFc := by rw [hr 508 (by omega) (by omega)]; exact r508
      have g511 : c₁.nreg 511 = 1 := by rw [hr 511 (by omega) (by omega)]; exact r511
      have g551 : c₁.nreg 551 = bCv := by rw [hr 551 (by omega) (by omega)]; exact h551
      have g552 : c₁.nreg 552 = s₂ := by rw [hr 552 (by omega) (by omega)]; exact h552
      obtain ⟨mc, hck⟩ := hcy j hj
      obtain ⟨mV, hVn⟩ := hV _ hck
      have m1 : c₁.nmem (bFc + j) = cy j := by rw [hf _ (Or.inl (by omega))]; exact mc
      have m2 : c₁.nmem (bV + cy j) = V (cy j) := by rw [hf _ (Or.inl (by omega))]; exact mV
      unfold cvBody
      exec_block
      all_goals try (config_simp; (try simp only [g508, h556, m1, g502, m2, g551, g511]); omega)
      rename_i hwb
      simp only [g508, h556, m1, g502, m2, g551, g552, g511] at hwb ⊢
      refine ⟨⟨hwb, by config_simp, by config_simp; exact h514', by omega, fun v hv hex => ?_,
        fun v hv hn => ?_, fun a ha => ?_, fun r h1 h2 => ?_, by config_simp; exact ho⟩, by omega⟩
      · config_simp
        by_cases hvj : v = V (cy j)
        · rw [hvj, upd_same]
        · rw [upd_other _ _ _ (by omega)]
          obtain ⟨j', hj'', e'⟩ := hex
          refine hM1 v hv ⟨j', ?_, e'⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj'' with h | rfl
          · exact h
          · exact absurd e'.symm hvj
      · config_simp
        have hvj : v ≠ V (cy j) := fun e' => hn ⟨j, by omega, e'.symm⟩
        rw [upd_other _ _ _ (by omega)]
        exact hM2 v hv fun ⟨j', h1, h2⟩ => hn ⟨j', by omega, h2⟩
      · config_simp; rw [upd_other _ _ _ (by omega)]; exact hf a ha
      · config_simp; simp only [upd_apply]
        split_ifs <;> first | omega | exact hr r h1 h2)
    (by omega) ⟨e₁.wb_right, by config_simp; exact r510, by config_simp; exact h514, by omega,
      fun v _ ⟨j, hj, _⟩ => absurd hj (by omega), fun v _ _ => rfl, fun a _ => rfl,
      fun r h1 h2 => by
        show upd c.nreg 556 (c.nreg 510) r = c.nreg r
        simp only [upd_apply]; split_ifs <;> omega, rfl⟩
  obtain ⟨-, -, -, -, hM1', hM2', hf', hr', ho'⟩ := hI
  exact ⟨c₂, 1 + t, .seq e₁ e, by omega, hM1', hM2', hf', hr', ho'⟩

lemma sum_ite_le {w : ℕ → ℕ} {p : ℕ → Prop} [DecidablePred p] {i n : ℕ} (hi : i < n) :
    (∑ v ∈ range i, if p v then w v else 0) + w i ≤ ∑ v ∈ range n, w v := by
  have h1 : (∑ v ∈ range i, if p v then w v else 0) ≤ ∑ v ∈ range i, w v :=
    sum_le_sum fun v _ => by split_ifs <;> omega
  have h2 : ∑ v ∈ range (i + 1), w v ≤ ∑ v ∈ range n, w v :=
    sum_le_sum_of_subset (range_subset_range.2 (by omega))
  rw [sum_range_succ] at h2
  omega

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The weights of the two sides.** With the stamps `cv` of the vertices of the cycle at `bCv`,
the darts `fdN v` at the vertices at `bF`, the face marks `im` at `bIm` and the flag `fl`, and
natural weights `w` at `bw` of total at most `W`: `r562` is the weight of the vertices off the
cycle whose face is marked differently from the flag, `r563` that of the others off the cycle. -/
theorem wPass_exec {cv fdN im w : ℕ → ℕ} {bCv s₂ bF bw bIm bA a fl : ℕ}
    (hW : bCv + n ≤ W ∧ bF + n ≤ W ∧ bw + n ≤ W ∧ bIm + k ≤ W) (c : Config)
    (hc : WordsBounded W c) (hF : FR δ bA bV bPr r₀ n bMk s bFc bTmp c) (hI : IR k bIm bA a c)
    (h539 : c.nreg 539 = fl) (h551 : c.nreg 551 = bCv) (h552 : c.nreg 552 = s₂)
    (h553 : c.nreg 553 = bF) (h554 : c.nreg 554 = bw)
    (mcv : ∀ v < n, c.nmem (bCv + v) = cv v) (mfd : ∀ v < n, c.nmem (bF + v) = fdN v ∧ fdN v < 3 * k)
    (mim : ∀ f < k, c.nmem (bIm + f) = im f) (mw : ∀ v < n, c.nmem (bw + v) = w v)
    (htot : ∑ v ∈ range n, w v ≤ W) :
    ∃ c' t, Exec P W wPass c c' t ∧ t ≤ 25 * n + 5 ∧
      c'.nreg 562 = ∑ v ∈ range n, (if cv v ≠ s₂ ∧ im (fdN v / 3) ≠ fl then w v else 0) ∧
      c'.nreg 563 = ∑ v ∈ range n, (if cv v ≠ s₂ ∧ im (fdN v / 3) = fl then w v else 0) ∧
      c'.nmem = c.nmem ∧ (∀ r, r < 557 ∨ 564 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.output = c.output := by
  obtain ⟨-, -, -, -, -, r505, -, -, -, -, r510, r511⟩ := hF
  obtain ⟨-, r531, -, -, r535, -, -, -, -⟩ := hI
  let Si : ℕ → ℕ := fun i => ∑ v ∈ range i, (if cv v ≠ s₂ ∧ im (fdN v / 3) ≠ fl then w v else 0)
  let So : ℕ → ℕ := fun i => ∑ v ∈ range i, (if cv v ≠ s₂ ∧ im (fdN v / 3) = fl then w v else 0)
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 559 = i ∧
    c'.nreg 505 = n ∧ i ≤ n ∧ c'.nreg 562 = Si i ∧ c'.nreg 563 = So i ∧ c'.nmem = c.nmem ∧
    (∀ r, r < 557 ∨ 564 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 559 510, .copyN 562 510,
      .copyN 563 510]) c c₁ k₁ ∧ I 0 c₁ ∧ k₁ = 3 := by
    exec_block
    refine ⟨⟨‹_›, by config_simp; exact r510, by config_simp; exact r505, by omega,
      by config_simp; rw [r510]; rfl, by config_simp; rw [r510]; rfl, rfl,
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl⟩, rfl⟩
  obtain ⟨c₂, t, e, hI', ht⟩ := Exec.forN (P := P) (W := W) (ri := 559) (rN := 505)
    (N := n) (lo := 0) (B := 23) (body := wBody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h559, h505, hin, h562, h563, hm, hr, ho⟩ hi => by
      have g : ∀ r, r < 557 → c₁.nreg r = c.nreg r := fun r hr' => hr r (Or.inl hr')
      have g511 : c₁.nreg 511 = 1 := by rw [g 511 (by omega)]; exact r511
      have g531 : c₁.nreg 531 = bIm := by rw [g 531 (by omega)]; exact r531
      have g535 : c₁.nreg 535 = 3 := by rw [g 535 (by omega)]; exact r535
      have g539 : c₁.nreg 539 = fl := by rw [g 539 (by omega)]; exact h539
      have g551 : c₁.nreg 551 = bCv := by rw [g 551 (by omega)]; exact h551
      have g552 : c₁.nreg 552 = s₂ := by rw [g 552 (by omega)]; exact h552
      have g553 : c₁.nreg 553 = bF := by rw [g 553 (by omega)]; exact h553
      have g554 : c₁.nreg 554 = bw := by rw [g 554 (by omega)]; exact h554
      have m1 : c₁.nmem (bCv + i) = cv i := by rw [hm]; exact mcv i hi
      have m2 : c₁.nmem (bw + i) = w i := by rw [hm]; exact mw i hi
      obtain ⟨m3', hfdk⟩ := mfd i hi
      have m3 : c₁.nmem (bF + i) = fdN i := by rw [hm]; exact m3'
      have m4 : c₁.nmem (bIm + fdN i / 3) = im (fdN i / 3) := by rw [hm]; exact mim _ (by omega)
      have hb1 := hw₁.2 (bCv + i)
      have hb2 := hw₁.1 552
      have hb3 := hw₁.2 (bIm + fdN i / 3)
      have hb4 := hw₁.1 539
      rw [m1] at hb1; rw [g552] at hb2; rw [m4] at hb3; rw [g539] at hb4
      have hsi : Si i + w i ≤ ∑ v ∈ range n, w v :=
        sum_ite_le (w := w) (p := fun v => cv v ≠ s₂ ∧ im (fdN v / 3) ≠ fl) hi
      have hso : So i + w i ≤ ∑ v ∈ range n, w v :=
        sum_ite_le (w := w) (p := fun v => cv v ≠ s₂ ∧ im (fdN v / 3) = fl) hi
      have hSi : Si (i + 1) = Si i + if cv i ≠ s₂ ∧ im (fdN i / 3) ≠ fl then w i else 0 :=
        sum_range_succ _ _
      have hSo : So (i + 1) = So i + if cv i ≠ s₂ ∧ im (fdN i / 3) = fl then w i else 0 :=
        sum_range_succ _ _
      have hstep : ∀ c₃ : Config, WordsBounded W c₃ → c₃.nreg 559 = i →
          (∀ r, r < 557 ∨ 564 ≤ r → c₃.nreg r = c.nreg r) → c₃.nreg 562 = Si (i + 1) →
          c₃.nreg 563 = So (i + 1) → c₃.nmem = c.nmem → c₃.output = c.output →
          ∃ c' k, Exec P W (.instr (.addN 559 559 511)) c₃ c' k ∧ I (i + 1) c' ∧ k ≤ 1 := by
        intro c₃ hw₃ e559 er e562 e563 em eo
        have e511 : c₃.nreg 511 = 1 := (er 511 (Or.inl (by omega))).trans r511
        have e505 : c₃.nreg 505 = n := (er 505 (Or.inl (by omega))).trans r505
        have ea := Exec.addN (P := P) hw₃ 559 559 511 (by rw [e559, e511]; omega)
        refine ⟨_, 1, ea, ⟨ea.wb_right, by config_simp; rw [e559, e511],
          by config_simp; exact e505, by omega, by config_simp; exact e562,
          by config_simp; exact e563, by config_simp; exact em, fun r hr' => ?_,
          by config_simp; exact eo⟩, le_rfl⟩
        config_simp; simp only [upd_apply]
        split_ifs with h'
        · omega
        · exact er r hr'
      unfold wBody
      refine spec_seq ?_
      exec_block
      all_goals try (config_simp; (try simp only [g551, h559, m1, g552, g554, m2]); omega)
      rename_i hwa
      simp only [g551, h559, m1, g552, g554, m2] at hwa ⊢
      refine spec_seq ?_
      by_cases hcy : cv i = s₂
      · refine spec_ifLtN_true (by config_simp; rw [g511]; omega) ?_
        refine spec_skip hwa ?_
        have n1 : ¬ (cv i ≠ s₂ ∧ im (fdN i / 3) ≠ fl) := fun h => h.1 hcy
        have n2 : ¬ (cv i ≠ s₂ ∧ im (fdN i / 3) = fl) := fun h => h.1 hcy
        obtain ⟨c', k', e', hI'', hk'⟩ := hstep _ hwa (by config_simp <;> exact h559)
          (fun r hr' => by
            config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr')
          (by config_simp; rw [h562, hSi, ite_eq_right_of_eq_false _ _ (eq_false n1), add_zero])
          (by config_simp; rw [h563, hSo, ite_eq_right_of_eq_false _ _ (eq_false n2), add_zero])
          (by config_simp <;> exact hm) (by config_simp <;> exact ho)
        exact ⟨c', k', e', hI'', by omega⟩
      · refine spec_ifLtN_false (by config_simp; rw [g511]; omega) ?_
        refine spec_seq ?_
        unfold wFace
        exec_block
        all_goals try (config_simp; (try simp only [g553, h559, m3, g535, g531, m4, g539]); omega)
        rename_i hwb
        simp only [g553, h559, m3, g535, g531, m4, g539] at hwb ⊢
        by_cases him : im (fdN i / 3) = fl
        · refine spec_ifLtN_true (by config_simp; rw [g511]; omega) ?_
          have n1 : ¬ (cv i ≠ s₂ ∧ im (fdN i / 3) ≠ fl) := fun h => h.2 him
          have p2 : cv i ≠ s₂ ∧ im (fdN i / 3) = fl := ⟨hcy, him⟩
          have hadd : c₁.nreg 563 + w i ≤ W := by
            rw [h563]; omega
          refine spec_instr (Exec.addN hwb 563 563 561 (by config_simp; omega)) fun hw₃ => ?_
          obtain ⟨c', k', e', hI'', hk'⟩ := hstep _ hw₃ (by config_simp <;> exact h559)
            (fun r hr' => by
              config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr')
            (by config_simp; rw [h562, hSi, ite_eq_right_of_eq_false _ _ (eq_false n1), add_zero])
            (by config_simp; rw [h563, hSo, ite_eq_left_of_eq_true _ _ (eq_true p2)])
            (by config_simp <;> exact hm) (by config_simp <;> exact ho)
          exact ⟨c', k', e', hI'', by omega⟩
        · refine spec_ifLtN_false (by config_simp; rw [g511]; omega) ?_
          have p1 : cv i ≠ s₂ ∧ im (fdN i / 3) ≠ fl := ⟨hcy, him⟩
          have n2 : ¬ (cv i ≠ s₂ ∧ im (fdN i / 3) = fl) := fun h => him h.2
          have hadd : c₁.nreg 562 + w i ≤ W := by
            rw [h562]; omega
          refine spec_instr (Exec.addN hwb 562 562 561 (by config_simp; omega)) fun hw₃ => ?_
          obtain ⟨c', k', e', hI'', hk'⟩ := hstep _ hw₃ (by config_simp <;> exact h559)
            (fun r hr' => by
              config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr')
            (by config_simp; rw [h562, hSi, ite_eq_left_of_eq_true _ _ (eq_true p1)])
            (by config_simp; rw [h563, hSo, ite_eq_right_of_eq_false _ _ (eq_false n2), add_zero])
            (by config_simp <;> exact hm) (by config_simp <;> exact ho)
          exact ⟨c', k', e', hI'', by omega⟩)
    (by omega) hI₁
  obtain ⟨-, -, -, -, h562', h563', hm', hr', ho'⟩ := hI'
  exact ⟨c₂, 3 + t, .seq e₁ e, by omega, h562', h563', hm', hr', ho'⟩

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem zCorner_exec {V L : ℕ → ℕ} {bLv l f₃ j : ℕ} (hj : j < 3) (hW : bV + 3 * k ≤ W ∧ bLv + n ≤ W)
    (c : Config) (hc : WordsBounded W c) (h502 : c.nreg 502 = bV) (h510 : c.nreg 510 = 0)
    (h566 : c.nreg 566 = l) (h567 : c.nreg 567 = bLv) (h571 : c.nreg 571 = f₃)
    (hf₃ : f₃ + 3 ≤ 3 * k) (mV : c.nmem (bV + (f₃ + j)) = V (f₃ + j)) (hVn : V (f₃ + j) < n)
    (mL : c.nmem (bLv + V (f₃ + j)) = L (V (f₃ + j))) :
    ∃ c' t, Exec P W (zCorner j) c c' t ∧ t ≤ 8 ∧
      c'.nreg 570 = (if L (V (f₃ + j)) < l then 0 else c.nreg 570) ∧
      (∀ r, r ≠ 569 → r ≠ 570 → r ≠ 572 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.output = c.output := by
  unfold zCorner
  refine spec_seq ?_
  exec_block
  all_goals try (config_simp; (try simp only [h571, h502, mV, h567]); omega)
  rename_i hwa
  simp only [h571, h502, mV, h567, mL] at hwa ⊢
  by_cases hlt : L (V (f₃ + j)) < l
  · refine spec_ifLtN_true (by config_simp; rw [h566]; exact hlt) ?_
    refine spec_instr (Exec.copyN hwa 570 510) fun _ => ⟨by omega, ?_, fun r h1 h2 h3 => ?_,
      by config_simp, by config_simp⟩
    · config_simp; rw [ite_eq_left_of_eq_true _ _ (eq_true hlt), h510]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  · refine spec_ifLtN_false (by config_simp; rw [h566]; exact hlt) ?_
    refine spec_skip hwa ⟨by omega, ?_, fun r h1 h2 h3 => ?_, by config_simp, by config_simp⟩
    · config_simp; rw [ite_eq_right_of_eq_false _ _ (eq_false hlt)]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The zone test of a face**: `r570 = flagF l V L (y / 3)`. -/
theorem ztest_exec {V L : ℕ → ℕ} {bLv l y bIm a : ℕ} (hW : bV + 3 * k ≤ W ∧ bLv + n ≤ W)
    (c : Config) (hc : WordsBounded W c) (hF : FR δ bA bV bPr r₀ n bMk s bFc bTmp c)
    (hI : IR k bIm bA a c) (h565 : c.nreg 565 = y) (h566 : c.nreg 566 = l)
    (h567 : c.nreg 567 = bLv) (hy : y < 3 * k)
    (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x ∧ V x < n)
    (mL : ∀ v < n, c.nmem (bLv + v) = L v) :
    ∃ c' t, Exec P W ztest c c' t ∧ t ≤ 30 ∧ c'.nreg 570 = flagF l V L (y / 3) ∧
      (∀ r, r ≠ 569 → r ≠ 570 → r ≠ 571 → r ≠ 572 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.output = c.output := by
  obtain ⟨-, -, r502, -, -, -, -, -, -, -, r510, r511⟩ := hF
  obtain ⟨-, -, -, -, r535, -, -, -, -⟩ := hI
  have hb := hc.1 565
  rw [h565] at hb
  obtain ⟨c₁, k₁, e₁, h571, h570, hr₁, hm₁, ho₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.divN 571 565 535,
      .mulN 571 571 535, .copyN 570 511]) c c₁ k₁ ∧ c₁.nreg 571 = 3 * (y / 3) ∧ c₁.nreg 570 = 1 ∧
      (∀ r, r ≠ 570 → r ≠ 571 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.output = c.output ∧ k₁ = 3 := by
    exec_block
    all_goals try (config_simp; (try simp only [h565, r535]); omega)
    rename_i hwb
    simp only [h565, r535, r511] at hwb ⊢
    refine ⟨by config_simp; ring, by config_simp, fun r h1 h2 => ?_, by first | rfl | trivial,
      by first | rfl | trivial, by first | rfl | trivial⟩
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hf₃ : 3 * (y / 3) + 3 ≤ 3 * k := by omega
  have step : ∀ (j : ℕ) (hj : j < 3) (c₀ : Config), WordsBounded W c₀ →
      (∀ r, r ≠ 569 → r ≠ 570 → r ≠ 571 → r ≠ 572 → c₀.nreg r = c.nreg r) →
      c₀.nreg 571 = 3 * (y / 3) → c₀.nmem = c.nmem →
      ∃ c' t, Exec P W (zCorner j) c₀ c' t ∧ t ≤ 8 ∧
        c'.nreg 570 = (if L (V (3 * (y / 3) + j)) < l then 0 else c₀.nreg 570) ∧
        (∀ r, r ≠ 569 → r ≠ 570 → r ≠ 571 → r ≠ 572 → c'.nreg r = c.nreg r) ∧
        c'.nreg 571 = 3 * (y / 3) ∧ c'.nmem = c.nmem ∧ c'.output = c₀.output := by
    intro j hj c₀ hw₀ fr f571 fm
    obtain ⟨mVj, hVj⟩ := mV (3 * (y / 3) + j) (by omega)
    obtain ⟨c', t, e, ht, h1, h2, h3, h4⟩ := zCorner_exec (P := P) (V := V) (L := L) hj hW c₀ hw₀
      ((fr 502 (by omega) (by omega) (by omega) (by omega)).trans r502)
      ((fr 510 (by omega) (by omega) (by omega) (by omega)).trans r510)
      ((fr 566 (by omega) (by omega) (by omega) (by omega)).trans h566)
      ((fr 567 (by omega) (by omega) (by omega) (by omega)).trans h567) f571 hf₃
      (by rw [fm]; exact mVj) hVj (by rw [fm]; exact mL _ hVj)
    exact ⟨c', t, e, ht, h1, fun r a1 a2 a3 a4 => by rw [h2 r a1 a2 a4]; exact fr r a1 a2 a3 a4,
      by rw [h2 571 (by omega) (by omega) (by omega)]; exact f571, by rw [h3, fm], h4⟩
  obtain ⟨c₂, t₂, e₂, ht₂, g1, g2, g3, g4, g5⟩ := step 0 (by omega) c₁ e₁.wb_right
    (fun r a1 a2 a3 a4 => hr₁ r a2 a3) h571 hm₁
  obtain ⟨c₃, t₃, e₃, ht₃, g1', g2', g3', g4', g5'⟩ := step 1 (by omega) c₂ e₂.wb_right g2 g3 g4
  obtain ⟨c₄, t₄, e₄, ht₄, g1'', g2'', g3'', g4'', g5''⟩ := step 2 (by omega) c₃ e₃.wb_right
    g2' g3' g4'
  refine ⟨c₄, 3 + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, ?_, g2'', g4'',
    by rw [g5'', g5', g5, ho₁]⟩
  rw [g1'', g1', g1, h570]
  unfold flagF
  simp only [Nat.add_zero]
  split_ifs <;> omega

end proofs

/-! ### Through the coding -/

section Bridge

open Map CycleSearch

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

/-- **The weights of `wPass` are those of the strict inside and outside.** If the stamps `cv`
mark exactly the vertices of the cycle of `δ` (as `cvMark` after `fcProg`), the darts `fdN` code a
dart at every vertex, and the face marks `im` differ from the flag exactly on `T.inside δ` (as
`imLoop_inside`), the two sums of `wPass` are `∑ v ∈ T.inC δ, wP v` and `∑ v ∈ T.outC δ, wP v`. -/
theorem weigh_sides (hM : M.IsPlane) {T : M.SpTree} {δ : D} (hδ : ¬ T.IsTree δ) {k n : ℕ}
    (cd : D ≃ Fin (3 * k)) (vi : Q ≃ Fin n) (hfi : ∀ x : D, fi cd (M.face x) = (cd x : ℕ) / 3)
    {V cv fdN im w : ℕ → ℕ} {s₂ fl : ℕ} (hV : ∀ x, V (cd x) = vi (M.vert x))
    (hcv1 : ∀ v < n, (∃ j < (T.fcycle δ).k, V (cd ((T.fcycle δ).d j)) = v) → cv v = s₂)
    (hcv2 : ∀ v < n, (¬ ∃ j < (T.fcycle δ).k, V (cd ((T.fcycle δ).d j)) = v) → cv v ≠ s₂)
    (fdD : Q → D) (hfdD : ∀ u, M.vert (fdD u) = u) (hfd : ∀ u, fdN (vi u) = cd (fdD u))
    (him : ∀ G, im (fi cd G) ≠ fl ↔ G ∈ T.inside δ) (wP : Q → ℕ) (hw : ∀ u, w (vi u) = wP u) :
    ∑ v ∈ range n, (if cv v ≠ s₂ ∧ im (fdN v / 3) ≠ fl then w v else 0) =
        ∑ u ∈ T.inC δ, wP u ∧
      ∑ v ∈ range n, (if cv v ≠ s₂ ∧ im (fdN v / 3) = fl then w v else 0) =
        ∑ u ∈ T.outC δ, wP u := by
  classical
  have hcyc : ∀ u, cv (vi u) = s₂ ↔ u ∈ T.cycV δ := by
    intro u
    rw [← SpTree.fcycle_verts hδ, SCycle.mem_verts]
    constructor
    · intro h
      by_contra hn
      refine hcv2 _ (vi u).2 (fun ⟨j, hj, e⟩ => hn ⟨j, hj, ?_⟩) h
      rw [hV] at e
      exact vi.injective (Fin.ext e)
    · rintro ⟨j, hj, e⟩
      exact hcv1 _ (vi u).2 ⟨j, hj, by rw [hV, e]⟩
  have hin : ∀ u, (cv (vi u) ≠ s₂ ∧ im (fdN (vi u) / 3) ≠ fl) ↔ u ∈ T.inC δ := by
    intro u
    rw [hfd, ← hfi, him, Ne, hcyc]
    constructor
    · rintro ⟨h1, h2⟩; exact (SpTree.mem_inC_iff hM h1 (hfdD u)).2 h2
    · intro h
      have h1 : u ∉ T.cycV δ := SpTree.notMem_cycV_of_mem_inC h
      exact ⟨h1, (SpTree.mem_inC_iff hM h1 (hfdD u)).1 h⟩
  have hout : ∀ u, (cv (vi u) ≠ s₂ ∧ im (fdN (vi u) / 3) = fl) ↔ u ∈ T.outC δ := by
    intro u
    have e1 : im (fdN (vi u) / 3) = fl ↔ M.face (fdD u) ∉ T.inside δ := by
      rw [hfd, ← hfi, ← him, not_not]
    rw [e1, Ne, hcyc]
    simp only [SpTree.outC, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ((SpTree.mem_inC_iff hM h1 (hfdD u)).1 h)⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ((SpTree.mem_inC_iff hM h1 (hfdD u)).2 h)⟩
  refine ⟨?_, ?_⟩
  · rw [sum_range_vi vi, ← sum_filter]
    refine sum_congr ?_ fun u _ => hw u
    ext u; simp only [mem_filter, mem_univ, true_and]; exact hin u
  · rw [sum_range_vi vi, ← sum_filter]
    refine sum_congr ?_ fun u _ => hw u
    ext u; simp only [mem_filter, mem_univ, true_and]; exact hout u

/-- **The zone test through the coding**: the face of `y` avoids the levels `< l` if and only if
`flagF l V L (cd y / 3)` is positive. -/
theorem ztest_zone {T₀ T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {A Tm V L : ℕ → ℕ}
    (hC : Coded M T₀ k cd A Tm) (vi : Q ≃ Fin n) (hV : ∀ x, V (cd x) = vi (M.vert x))
    (hL : ∀ v, L (vi v) = T.height v) (l : ℕ) (y : D) :
    0 < flagF l V L ((cd y : ℕ) / 3) ↔ M.face y ∉ M.zone (T.low l) := by
  rw [← hC.fi_face]
  exact flagF_pos_iff hC vi hV hL l (M.face y)

/-- **The heavy test, numerically**: for the normalized weights, a set weighs at least `1/3` if
and only if three times its natural weight is at least the total. -/
theorem third_le_iff {wP : Q → ℕ} (hpos : 0 < ∑ v, wP v) (X : Finset Q) :
    1 / 3 ≤ ∑ v ∈ X, wR wP v ↔ ∑ v, wP v ≤ 3 * ∑ v ∈ X, wP v := by
  have hS : (0 : ℝ) < ∑ v, (wP v : ℝ) := by exact_mod_cast hpos
  unfold wR
  rw [← sum_div, le_div_iff₀ hS]
  constructor
  · intro h
    have : ((∑ v, wP v : ℕ) : ℝ) ≤ ((3 * ∑ v ∈ X, wP v : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · intro h
    have : ((∑ v, wP v : ℕ) : ℝ) ≤ ((3 * ∑ v ∈ X, wP v : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith

/-- **The comparison of the two sides, numerically**: if the moved weights are natural numbers
`wv` divided by the total of `wP` (as `conc_exec` gives), the strict inside is the lighter side
exactly when its natural weight is at most that of the strict outside. -/
theorem lighter_iff {cn : Q → Q} {wP wv : Q → ℕ} (hpos : 0 < ∑ v, wP v)
    (h : ∀ u, wcf cn (wR wP) u = (wv u : ℝ) / ∑ v, (wP v : ℝ)) (X X' : Finset Q) :
    ∑ v ∈ X, wcf cn (wR wP) v ≤ ∑ v ∈ X', wcf cn (wR wP) v ↔
      ∑ v ∈ X, wv v ≤ ∑ v ∈ X', wv v := by
  have hS : (0 : ℝ) < ∑ v, (wP v : ℝ) := by exact_mod_cast hpos
  simp only [h, ← sum_div]
  rw [div_le_div_iff_of_pos_right hS]
  exact_mod_cast Iff.rfl

/-- **The wanted side through the representative**: if the concentration sends the strict inside
of `Y` to one vertex `r`, `deepWant` is the test at `r` (or holds vacuously). -/
theorem deepWant_iff {T₁ : M.SpTree} {cn : Q → Q} {w : Q → ℝ} {Y : Finset M.Face} {δ : D}
    {r : Q} (hr : ∀ v ∈ ins Y, cn v = r) :
    deepWant T₁ cn w Y δ ↔ (ins Y = ∅ ∨ (r ∈ T₁.inC δ ∨ (r ∈ T₁.cycV δ ∧
      ∑ u ∈ T₁.inC δ, wcf cn w u ≤ ∑ u ∈ T₁.outC δ, wcf cn w u))) := by
  unfold deepWant
  constructor
  · intro h
    by_cases he : ins Y = ∅
    · exact Or.inl he
    · obtain ⟨v₀, hv₀⟩ := nonempty_iff_ne_empty.2 he
      have := h v₀ hv₀
      rw [hr v₀ hv₀] at this
      exact Or.inr this
  · rintro (he | h) v hv
    · rw [he] at hv; exact absurd hv (notMem_empty v)
    · rw [hr v hv]; exact h

end Bridge

end MillerProg

end PlanarSeparator
