module

public import PlanarSeparator.Machine.MillerFull0

/-!
# Miller's separator on the machine: one rerouting option of the deep case

In the rerouting branch of `PlanarSeparator.Map.deepSep` the separator is one of the two options
`PlanarSeparator.Map.arcOpt` along the boundary cycle `C` of the component `Y`: the fundamental
cycle of the last dart `e = C.d (C.idxAt s ℓ)` of an arc in the tree `T₂` redirected along the
arc (`PlanarSeparator.Map.SpTree.arcTree`, over `ℓ` steps from the index `s`), with its inside or
the complement, as the inside agrees with that of `δ` at the face `g₀`.

`ropt` (bases of a fresh region in `r600 … r604`, the arc in `r447 = s`, `r448 = ℓ`):
`cpPass ; arPass` (the parent darts of `T₂` at `bPr2`, `MillerProg.arcTree_par_code`), the dart
`e` into `r353` (`roptE`), the registers of `s9band` for the fresh region (`roptR`), `s9band` on
`T₂` (the darts of `T₂.fcycle e` at `bFc2`, its inside marks at `bIm2` with the flag `r539`), and
the orientation bits (`roptO`): `r653 = 1` iff the insides of `e` in `T₂` and of `δ` in `T₁`
agree at `g₀`, `r655 = 1` iff the face of `δ` lies on the chosen side.

**`MillerProg.ropt_spec`**: within `113 k + 97 n + 19 ℓ + 220` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset Map CycleSearch

/-! ### Bits -/

/-- `r := 1` if `x ≠ y`, else `0`. -/
def nqb (r x y : ℕ) : Stmt :=
  .ifLtN x y (.instr (.constN r 1)) (.ifLtN y x (.instr (.constN r 1)) (.instr (.constN r 0)))

/-- `r := 1` if `x = y`, else `0`. -/
def eqb (r x y : ℕ) : Stmt :=
  .ifLtN x y (.instr (.constN r 0)) (.ifLtN y x (.instr (.constN r 0)) (.instr (.constN r 1)))

section Bits

variable {W : ℕ} {P : Input}

theorem nqb_exec (hW : 1 ≤ W) (r x y : ℕ) (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (nqb r x y) c c' t ∧ t ≤ 5 ∧ c'.nreg r ≤ 1 ∧
      (c'.nreg r = 1 ↔ c.nreg x ≠ c.nreg y) ∧ (∀ r', r' ≠ r → c'.nreg r' = c.nreg r') ∧
      c'.nmem = c.nmem ∧ c'.output = c.output := by
  by_cases h1 : c.nreg x < c.nreg y
  · exact ⟨_, _, .ifLtN_true h1 (Exec.constN hc r 1 hW), by omega, by simp,
      by simp; omega, fun r' h => by simp [upd_other _ _ _ h], rfl, rfl⟩
  · by_cases h2 : c.nreg y < c.nreg x
    · exact ⟨_, _, .ifLtN_false h1 (.ifLtN_true h2 (Exec.constN hc r 1 hW)), by omega,
        by simp, by simp; omega, fun r' h => by simp [upd_other _ _ _ h], rfl, rfl⟩
    · exact ⟨_, _, .ifLtN_false h1 (.ifLtN_false h2 (Exec.constN hc r 0 (by omega))), by omega,
        by simp, by simp; omega, fun r' h => by simp [upd_other _ _ _ h], rfl, rfl⟩

theorem eqb_exec (hW : 1 ≤ W) (r x y : ℕ) (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (eqb r x y) c c' t ∧ t ≤ 5 ∧ c'.nreg r ≤ 1 ∧
      (c'.nreg r = 1 ↔ c.nreg x = c.nreg y) ∧ (∀ r', r' ≠ r → c'.nreg r' = c.nreg r') ∧
      c'.nmem = c.nmem ∧ c'.output = c.output := by
  by_cases h1 : c.nreg x < c.nreg y
  · exact ⟨_, _, .ifLtN_true h1 (Exec.constN hc r 0 (by omega)), by omega, by simp,
      by simp; omega, fun r' h => by simp [upd_other _ _ _ h], rfl, rfl⟩
  · by_cases h2 : c.nreg y < c.nreg x
    · exact ⟨_, _, .ifLtN_false h1 (.ifLtN_true h2 (Exec.constN hc r 0 (by omega))), by omega,
        by simp, by simp; omega, fun r' h => by simp [upd_other _ _ _ h], rfl, rfl⟩
    · exact ⟨_, _, .ifLtN_false h1 (.ifLtN_false h2 (Exec.constN hc r 1 hW)), by omega,
        by simp, by simp; omega, fun r' h => by simp [upd_other _ _ _ h], rfl, rfl⟩

end Bits

/-! ### One option -/

/-- The dart `e = C.d (idxN K s ℓ)` of the cycle at `bCy` into `r353`. -/
def roptE : Stmt :=
  .seq (.instr (.addN 487 447 448)) <| .seq (.ifLtN 487 451 .skip (.instr (.subN 487 487 451)))
    (block [.addN 487 439 487, .loadN 353 487])

/-- The registers `S9Regs` of `s9band` for the region of `r600 … r604`. -/
def roptR : List Instr :=
  [.constN 501 0, .copyN 502 434, .copyN 503 449, .constN 504 0, .copyN 505 441, .copyN 506 604,
    .constN 507 1, .copyN 508 603, .copyN 509 602, .constN 510 0, .constN 511 1, .copyN 530 605,
    .copyN 531 601, .constN 533 1, .constN 534 0, .constN 535 3, .copyN 536 606, .copyN 537 607,
    .constN 538 0, .copyN 567 442]

/-- **The orientation bits**: the marks at the face `g₀` of the dart at `bF = r595` in the new
region (`bIm2 = r601`, flag `r539`) and in the old one (`bIm = r608`, flag `r609`), their agreement
`r653`, and whether the face of `δ = r610` lies on the chosen side (`r655`). -/
def roptO : Stmt :=
  .seq (block [.loadN 650 595, .divN 650 650 432, .addN 651 601 650, .loadN 651 651,
    .addN 652 608 650, .loadN 652 652, .divN 654 610 432, .addN 654 601 654, .loadN 654 654]) <|
  .seq (nqb 656 651 539) <| .seq (nqb 657 652 609) <| .seq (eqb 653 656 657) <|
  .seq (nqb 658 654 539) (eqb 655 658 653)

/-- **One rerouting option**: the arc tree, the cycle of its last dart with the inside marks, and
the orientation bits. -/
def ropt : Stmt :=
  .seq (.instr (.copyN 449 600)) <| .seq cpPass <| .seq arPass <| .seq roptE <|
  .seq (block roptR) <| .seq s9band roptO

section Opt

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

set_option maxHeartbeats 16000000 in
/-- **One rerouting option on the machine.** -/
theorem ropt_spec {T T₁ : M.SpTree} {C : M.SCycle} {k n : ℕ} {cd : D ≃ Fin (3 * k)}
    {vi : Q ≃ Fin n} {A V : ℕ → ℕ} {W : ℕ} {P : Input} {c : Config}
    {bV bL h bNx bCy bPos bLv bPr l x₀ u bPr2 bIm2 bMk2 bTmp2 bFc2 bF bIm fl₁ s ℓ : ℕ}
    {δ xg : D} (hM : M.IsPlane) (hk : 0 < k)
    (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hφ : ∀ x, (cd (M.φ x) : ℕ) = phi3 (cd x))
    (hV : ∀ x, V (cd x) = vi (M.vert x)) (hfi : ∀ x : D, fi cd (M.face x) = (cd x : ℕ) / 3)
    (hr : (vi T₁.root : ℕ) = 0) (hs : s < C.k) (hℓ : ℓ + 1 < C.k) (hro : T₁.root ∉ C.verts)
    (hC : ∀ i < C.k, T₁.height (M.vert (C.d i)) = T₁.height (M.vert (C.d s)))
    (hnt : ∀ i < C.k, ¬ T₁.IsTree (C.d i)) (hCp : C.Proper)
    (hlay : S9Lay k n bV bPr2 bLv bIm2 bMk2 bTmp2 bFc2 W)
    (hlay' : bPr + n ≤ bPr2 ∧ bV + 3 * k ≤ bPr2 ∧ bLv + n ≤ bPr2 ∧ bCy + C.k ≤ bPr2 ∧ 11 * k ≤ bF ∧ bF + 1 ≤ bPr2 ∧ 11 * k ≤ bIm ∧
      bIm + k ≤ bPr2 ∧ 2 * C.k ≤ W)
    (hc : WordsBounded W c) (hB : BR 0 bV bL k h bNx bCy bPos n bLv bPr l x₀ u c)
    (h451 : c.nreg 451 = C.k) (h447 : c.nreg 447 = s) (h448 : c.nreg 448 = ℓ)
    (h600 : c.nreg 600 = bPr2) (h601 : c.nreg 601 = bIm2) (h602 : c.nreg 602 = bTmp2)
    (h603 : c.nreg 603 = bFc2) (h604 : c.nreg 604 = bMk2) (h605 : c.nreg 605 = k)
    (h606 : c.nreg 606 = 9 * k) (h607 : c.nreg 607 = 8 * k) (h595 : c.nreg 595 = bF)
    (h608 : c.nreg 608 = bIm) (h609 : c.nreg 609 = fl₁) (h610 : c.nreg 610 = cd δ)
    (mA : ∀ x < 3 * k, c.nmem x = A x) (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x)
    (mL : ∀ v, c.nmem (bLv + vi v) = T.height v)
    (hPr : ∀ v (h : v ≠ T₁.root), c.nmem (bPr + vi v) = cd (T₁.par v h))
    (mCy : ∀ i < C.k, c.nmem (bCy + i) = cd (C.d i)) (mF : c.nmem bF = cd xg)
    (mIm : ∀ G : M.Face, c.nmem (bIm + fi cd G) ≠ fl₁ ↔ G ∈ T₁.inside δ)
    (hMk : ∀ v < n, c.nmem (bMk2 + v) = 0) :
    ∃ c' t, Exec P W ropt c c' t ∧ t ≤ 113 * k + 97 * n + 19 * ℓ + 230 ∧
      c'.nreg 514 = ((T₁.arcTree C s ℓ hs hro hC).fcycle (C.d (C.idxAt s ℓ))).k ∧
      (∀ i < ((T₁.arcTree C s ℓ hs hro hC).fcycle (C.d (C.idxAt s ℓ))).k,
        c'.nmem (bFc2 + i) = cd (((T₁.arcTree C s ℓ hs hro hC).fcycle (C.d (C.idxAt s ℓ))).d i)) ∧
      (∀ G : M.Face, c'.nmem (bIm2 + fi cd G) ≠ c'.nreg 539 ↔
        G ∈ (T₁.arcTree C s ℓ hs hro hC).inside (C.d (C.idxAt s ℓ))) ∧
      c'.nreg 653 ≤ 1 ∧
      (c'.nreg 653 = 1 ↔ (M.face xg ∈ (T₁.arcTree C s ℓ hs hro hC).inside (C.d (C.idxAt s ℓ)) ↔
        M.face xg ∈ T₁.inside δ)) ∧
      c'.nreg 655 ≤ 1 ∧
      (c'.nreg 655 = 1 ↔ (M.face δ ∈ (T₁.arcTree C s ℓ hs hro hC).inside (C.d (C.idxAt s ℓ)) ↔
        c'.nreg 653 = 1)) ∧
      (∀ x < 3 * k, c'.nmem x = A x) ∧
      (∀ a, 11 * k ≤ a → (a < bPr2 ∨ bFc2 + 2 * n + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (430 ≤ r ∧ r < 447) ∨ r = 451 ∨ (590 ≤ r ∧ (r < 650 ∨ 659 ≤ r)) →
        c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  classical
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hlay
  obtain ⟨d1, d0, d8, d2, d3, d4, d5, d6, d7⟩ := hlay'
  set T₂ := T₁.arcTree C s ℓ hs hro hC
  set e := C.d (C.idxAt s ℓ)
  have hW1 : 1 ≤ W := by omega
  -- 0. `r449 := bPr2`
  have e₀ := Exec.copyN (P := P) hc 449 600
  set c₀ : Config := { c with nreg := upd c.nreg 449 (c.nreg 600) }
  have hw₀ := e₀.wb_right
  have k₀ : ∀ r, r ≠ 449 → c₀.nreg r = c.nreg r := fun r hr => upd_other _ _ _ hr
  have q449 : c₀.nreg 449 = bPr2 := by
    show upd c.nreg 449 (c.nreg 600) 449 = _; rw [upd_same, h600]
  have hB₀ : BR 0 bV bL k h bNx bCy bPos n bLv bPr l x₀ u c₀ :=
    hB.of fun r a b => k₀ r (by omega)
  -- 1. the copy of the parent darts
  obtain ⟨c₁, t₁, e₁, ht₁, hcp₁, hm₁, hr₁, ho₁⟩ :=
    cpPass_exec (P := P) (bPr2 := bPr2) d1 (by omega) c₀ hw₀ hB₀ q449
  have hw₁ := e₁.wb_right
  have hB₁ := hB₀.of fun r a b => hr₁ r (Or.inl (by omega))
  -- 2. the redirection along the arc
  have hA' : ∀ x < 3 * k, c₁.nmem (0 + x) = A x ∧ A x < 3 * k := fun x hx => by
    refine ⟨by rw [zero_add, hm₁ x (Or.inl (by omega))]; exact mA x hx, ?_⟩
    have e' : x = cd (cd.symm ⟨x, hx⟩) := by simp
    rw [e', hAcd]; exact (cd _).2
  have hV' : ∀ x < 3 * k, c₁.nmem (bV + x) = V x ∧ V x < n := fun x hx => by
    refine ⟨by rw [hm₁ _ (Or.inl (by omega))]; exact mV x hx, ?_⟩
    have e' : x = cd (cd.symm ⟨x, hx⟩) := by simp
    rw [e', hV]; exact (vi _).2
  obtain ⟨c₂, t₂, e₂, ht₂, hp1, hp2, hm₂, hr₂, ho₂⟩ :=
    arPass_exec (P := P) (A := A) (V := V) (cy := fun i => cd (C.d i)) (K := C.k) (s := s)
      (ℓ := ℓ) (bPr2 := bPr2) ⟨by omega, by omega, d2⟩ (by omega) c₁ hw₁ hB₁
      (by rw [hr₁ 451 (Or.inl (by omega)), k₀ 451 (by omega)]; exact h451)
      (by rw [hr₁ 447 (Or.inl (by omega)), k₀ 447 (by omega)]; exact h447)
      (by rw [hr₁ 448 (Or.inl (by omega)), k₀ 448 (by omega)]; exact h448)
      (by rw [hr₁ 449 (Or.inl (by omega))]; exact q449) hs (by omega)
      (fun i hi => ⟨by rw [hm₁ _ (Or.inl (by omega))]; exact mCy i hi, (cd _).2⟩) hA' hV'
      (fun i hi j hj e' => by
        rw [hV, hV] at e'
        exact C.inj _ hi _ hj (vi.injective (Fin.ext e')))
  have hw₂ := e₂.wb_right
  have hPr₂ : ∀ v (hv : v ≠ T₂.root), c₂.nmem (bPr2 + vi v) = cd (T₂.par v hv) :=
    fun v hv => arcTree_par_code cd vi hAcd hV C hs hro hC (by omega)
      (cy := fun i => cd (C.d i)) (Pr := fun u => c.nmem (bPr + u))
      (Pr2 := fun u => c₂.nmem (bPr2 + u)) (fun i _ => rfl) hPr hp1
      (fun v hv h' => by rw [hp2 v hv h', hcp₁ v hv]) v hv
  -- 3. the dart `e`
  have R₂ : ∀ r, r < 480 → r ≠ 449 → c₂.nreg r = c.nreg r := fun r a b =>
    (hr₂ r (Or.inl a)).trans ((hr₁ r (Or.inl (by omega))).trans (k₀ r b))
  have g447 := R₂ 447 (by omega) (by omega)
  have g448 := R₂ 448 (by omega) (by omega)
  have g451 := R₂ 451 (by omega) (by omega)
  have g439 := (R₂ 439 (by omega) (by omega)).trans hB.r339
  have hik : C.idxAt s ℓ < C.k := C.idxAt_lt hs (by omega)
  have ea := Exec.addN (P := P) hw₂ 487 447 448 (by rw [g447, g448, h447, h448]; omega)
  set ca : Config := { c₂ with nreg := upd c₂.nreg 487 (c₂.nreg 447 + c₂.nreg 448) }
  have qa : ca.nreg 487 = s + ℓ := by
    show upd c₂.nreg 487 (c₂.nreg 447 + c₂.nreg 448) 487 = _
    rw [upd_same, g447, g448, h447, h448]
  have ka : ∀ r, r ≠ 487 → ca.nreg r = c₂.nreg r := fun r hr => upd_other _ _ _ hr
  obtain ⟨cb, tb, eb, htb, qb, kb, mb, ob⟩ : ∃ cb tb, Exec P W
      (.ifLtN 487 451 .skip (.instr (.subN 487 487 451))) ca cb tb ∧ tb ≤ 3 ∧
      cb.nreg 487 = C.idxAt s ℓ ∧ (∀ r, r ≠ 487 → cb.nreg r = c₂.nreg r) ∧
      cb.nmem = c₂.nmem ∧ cb.output = c₂.output := by
    have q451 : ca.nreg 451 = C.k := by rw [ka 451 (by omega), g451, h451]
    by_cases hlt : s + ℓ < C.k
    · refine ⟨ca, _, .ifLtN_true (by rw [qa, q451]; exact hlt) (.skip ea.wb_right), by omega,
        ?_, ka, rfl, rfl⟩
      rw [qa]; simp only [SCycle.idxAt, hlt, ↓reduceIte]
    · refine ⟨_, _, .ifLtN_false (by rw [qa, q451]; exact hlt)
        (Exec.subN ea.wb_right 487 487 451), by omega, ?_, fun r hr => ?_, rfl, rfl⟩
      · show upd ca.nreg 487 _ 487 = _
        rw [qa, q451]; simp only [SCycle.idxAt, hlt, ↓reduceIte, upd_same]
      · show upd ca.nreg 487 _ r = _
        rw [upd_other _ _ _ hr, ka r hr]
  obtain ⟨c₃, t₃, e₃', ht₃, q353, kc, mc, oc⟩ : ∃ c₃ t₃, Exec P W
      (block [.addN 487 439 487, .loadN 353 487]) cb c₃ t₃ ∧ t₃ = 2 ∧
      c₃.nreg 353 = cb.nmem (bCy + C.idxAt s ℓ) ∧
      (∀ r, r ≠ 487 → r ≠ 353 → c₃.nreg r = cb.nreg r) ∧ c₃.nmem = cb.nmem ∧
      c₃.output = cb.output := by
    have hwb := eb.wb_right
    have q439 : cb.nreg 439 = bCy := by rw [kb 439 (by omega), g439]
    exec_block
    · rw [q439, qb]; omega
    · refine ⟨rfl, ?_, fun r a b => ?_, rfl, rfl⟩
      · config_simp; rw [q439, qb]
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have e₃ : Exec P W roptE c₂ c₃ (1 + (tb + t₃)) := .seq ea (.seq eb e₃')
  have hw₃ := e₃.wb_right
  have q353' : c₃.nreg 353 = cd e := by
    rw [q353, mb, hm₂ _ (Or.inl (by omega)), hm₁ _ (Or.inl (by omega))]; exact mCy _ hik
  have R₃ : ∀ r, r ≠ 487 → r ≠ 353 → c₃.nreg r = c₂.nreg r := fun r a b => by
    rw [kc r a b, kb r a]
  have M₃ : c₃.nmem = c₂.nmem := by rw [mc, mb]
  have G₃ : ∀ r, (r < 480 ∨ 493 ≤ r) → r ≠ 449 → r ≠ 487 → r ≠ 353 → c₃.nreg r = c.nreg r :=
    fun r a b d f => by
      rw [R₃ r d f, hr₂ r (by omega), hr₁ r (by omega), k₀ r b]
  -- 4. the registers of `s9band`
  obtain ⟨c₄, t₄, e₄, ht₄, hR₄, md, od⟩ : ∃ c₄ t₄, Exec P W (block roptR) c₃ c₄ t₄ ∧
      t₄ = 20 ∧ S9Regs k n bV bPr2 bLv bIm2 bMk2 bTmp2 bFc2 c₄ ∧ c₄.nmem = c₃.nmem ∧
      c₄.output = c₃.output := by
    have v434 : c₃.nreg 434 = bV := (G₃ 434 (by omega) (by omega) (by omega) (by omega)).trans
      hB.r334
    have v449 : c₃.nreg 449 = bPr2 := by
      rw [R₃ 449 (by omega) (by omega), hr₂ 449 (by omega), hr₁ 449 (by omega)]; exact q449
    have v441 : c₃.nreg 441 = n := (G₃ 441 (by omega) (by omega) (by omega) (by omega)).trans
      hB.r341
    have v442 : c₃.nreg 442 = bLv := (G₃ 442 (by omega) (by omega) (by omega) (by omega)).trans
      hB.r342
    have v601 := (G₃ 601 (by omega) (by omega) (by omega) (by omega)).trans h601
    have v602 := (G₃ 602 (by omega) (by omega) (by omega) (by omega)).trans h602
    have v603 := (G₃ 603 (by omega) (by omega) (by omega) (by omega)).trans h603
    have v604 := (G₃ 604 (by omega) (by omega) (by omega) (by omega)).trans h604
    have v605 := (G₃ 605 (by omega) (by omega) (by omega) (by omega)).trans h605
    have v606 := (G₃ 606 (by omega) (by omega) (by omega) (by omega)).trans h606
    have v607 := (G₃ 607 (by omega) (by omega) (by omega) (by omega)).trans h607
    unfold roptR
    exec_block
    all_goals try omega
    refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      rfl, rfl⟩
    all_goals config_simp
    all_goals first | rfl | assumption
  have hw₄ := e₄.wb_right
  have kd : ∀ r, (r < 501 ∨ 568 ≤ r) → c₄.nreg r = c₃.nreg r := fun r hr =>
    e₄.nreg_of_wr (by simp [roptR, block, Stmt.wr, Instr.wr]; omega)
  -- 5. `s9band` on the arc tree
  have hδ : ¬ T₂.IsTree e := by
    have := T₁.not_isTree_arcTree C (hs := hs) (hr := hro) (hC := hC) hCp hnt (L := ℓ + 1)
      (by omega) hℓ
    simpa only [Nat.add_sub_cancel] using this
  have M₄ : ∀ a, (a < bPr2 ∨ bPr2 + n ≤ a) → c₄.nmem a = c.nmem a := fun a ha => by
    rw [md, M₃, hm₂ a ha, hm₁ a ha]
  obtain ⟨c₅, t₅, e₅, ht₅, h514, hd₅, him₅, -, -, mA₅, hm₅, hr₅, -, -, ho₅⟩ :=
    s9band_spec (T := T) (T₁ := T₂) (cd := cd) (vi := vi) (A := A) (V := V) (P := P) (c := c₄)
      (l₂ := c₄.nreg 160) (δ := e) hM hk hAcd hφ hV hr ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10,
        l11⟩ hw₄ hR₄
      (by rw [kd 353 (by omega)]; exact q353') rfl hδ
      (fun x hx => by rw [M₄ x (Or.inl (by omega))]; exact mA x hx)
      (fun x hx => by rw [M₄ _ (Or.inl (by omega))]; exact mV x hx)
      (fun v => by have := (vi v).2; rw [M₄ _ (Or.inl (by omega))]; exact mL v)
      (fun v hv => by rw [md, M₃]; exact hPr₂ v hv)
      (fun v hv => by rw [M₄ _ (Or.inr (by omega))]; exact hMk v hv)
  have hw₅ := e₅.wb_right
  have S5 : ∀ r, ((430 ≤ r ∧ r < 447) ∨ r = 451) → c₅.nreg r = c₄.nreg r := fun r hr =>
    e₅.nreg_of_wr (by
      rcases hr with ⟨a, b⟩ | rfl
      · interval_cases r <;> decide
      · decide)
  have G₅ : ∀ r, 590 ≤ r → r ≠ 449 → c₅.nreg r = c.nreg r := fun r a b => by
    rw [hr₅ r a, kd r (by omega), G₃ r (by omega) b (by omega) (by omega)]
  have B₅ : ∀ r, ((430 ≤ r ∧ r < 447) ∨ r = 451) → c₅.nreg r = c.nreg r := fun r hr => by
    rw [S5 r hr, kd r (by omega)]
    rcases hr with ⟨a, b⟩ | rfl
    · exact G₃ r (by omega) (by omega) (by omega) (by omega)
    · exact G₃ 451 (by omega) (by omega) (by omega) (by omega)
  have M₅ : ∀ a, 11 * k ≤ a → a < bPr2 → c₅.nmem a = c.nmem a := fun a h1 h2 => by
    rw [hm₅ a h1 (Or.inl (by omega)), M₄ a (Or.inl h2)]
  -- 6. the orientation bits
  have v595 := (G₅ 595 (by omega) (by omega)).trans h595
  have v601 := (G₅ 601 (by omega) (by omega)).trans h601
  have v608 := (G₅ 608 (by omega) (by omega)).trans h608
  have v609 := (G₅ 609 (by omega) (by omega)).trans h609
  have v610 := (G₅ 610 (by omega) (by omega)).trans h610
  have v432 := (B₅ 432 (Or.inl ⟨by omega, by omega⟩)).trans hB.r332
  have mF₅ : c₅.nmem bF = cd xg := (M₅ bF d3 (by omega)).trans mF
  have hxg := (cd xg).2
  have hδk := (cd δ).2
  obtain ⟨c₆, t₆, e₆', ht₆, q651, q652, q654, k₆, m₆, o₆⟩ : ∃ c₆ t₆, Exec P W
      (block [.loadN 650 595, .divN 650 650 432, .addN 651 601 650, .loadN 651 651,
        .addN 652 608 650, .loadN 652 652, .divN 654 610 432, .addN 654 601 654,
        .loadN 654 654]) c₅ c₆ t₆ ∧ t₆ = 9 ∧
      c₆.nreg 651 = c₅.nmem (bIm2 + (cd xg : ℕ) / 3) ∧
      c₆.nreg 652 = c₅.nmem (bIm + (cd xg : ℕ) / 3) ∧
      c₆.nreg 654 = c₅.nmem (bIm2 + (cd δ : ℕ) / 3) ∧
      (∀ r, r ≠ 650 → r ≠ 651 → r ≠ 652 → r ≠ 654 → c₆.nreg r = c₅.nreg r) ∧
      c₆.nmem = c₅.nmem ∧ c₆.output = c₅.output := by
    exec_block
    all_goals try (config_simp; simp only [v595, v432, v601, v608, v610, mF₅]; omega)
    refine ⟨rfl, ?_, ?_, ?_, fun r a b d f => ?_, rfl, rfl⟩
    all_goals config_simp
    · simp only [v595, v432, v601, mF₅]
    · simp only [v595, v432, v608, mF₅]
    · simp only [v432, v601, v610]
    · simp only [upd_apply]; split_ifs <;> omega
  have e₆ := e₆'
  have hw₆ := e₆.wb_right
  obtain ⟨c₇, t₇, e₇, ht₇, b₇, i₇, k₇, m₇, o₇⟩ := nqb_exec (P := P) hW1 656 651 539 c₆ hw₆
  obtain ⟨c₈, t₈, e₈, ht₈, b₈, i₈, k₈, m₈, o₈⟩ :=
    nqb_exec (P := P) hW1 657 652 609 c₇ e₇.wb_right
  obtain ⟨c₉, t₉, e₉, ht₉, b₉, i₉, k₉, m₉, o₉⟩ :=
    eqb_exec (P := P) hW1 653 656 657 c₈ e₈.wb_right
  obtain ⟨c₁₀, t₁₀, e₁₀, ht₁₀, b₁₀, i₁₀, k₁₀, m₁₀, o₁₀⟩ :=
    nqb_exec (P := P) hW1 658 654 539 c₉ e₉.wb_right
  obtain ⟨c₁₁, t₁₁, e₁₁, ht₁₁, b₁₁, i₁₁, k₁₁, m₁₁, o₁₁⟩ :=
    eqb_exec (P := P) hW1 655 658 653 c₁₀ e₁₀.wb_right
  have eO : Exec P W roptO c₅ c₁₁ (t₆ + (t₇ + (t₈ + (t₉ + (t₁₀ + t₁₁))))) :=
    .seq e₆ (.seq e₇ (.seq e₈ (.seq e₉ (.seq e₁₀ e₁₁))))
  have eR : Exec P W ropt c c₁₁ _ :=
    .seq e₀ (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ eO)))))
  -- the registers through the bits
  have K11 : ∀ r, r < 650 ∨ 659 ≤ r → c₁₁.nreg r = c₆.nreg r := fun r hr => by
    rw [k₁₁ r (by omega), k₁₀ r (by omega), k₉ r (by omega), k₈ r (by omega), k₇ r (by omega)]
  have M11 : c₁₁.nmem = c₅.nmem := by rw [m₁₁, m₁₀, m₉, m₈, m₇, m₆]
  have f539 : c₁₁.nreg 539 = c₅.nreg 539 := by rw [K11 539 (by omega), k₆ 539 (by omega)
    (by omega) (by omega) (by omega)]
  have hfk : ∀ G : M.Face, fi cd G < k := fun G => by
    unfold fi; have := (cd (M.face_surjective G).choose).2; omega
  have c656 : c₈.nreg 656 = 1 ↔ M.face xg ∈ T₂.inside e := by
    rw [k₈ 656 (by omega), i₇, q651, k₆ 539 (by omega) (by omega) (by omega) (by omega),
      ← hfi, him₅]
  have c657 : c₈.nreg 657 = 1 ↔ M.face xg ∈ T₁.inside δ := by
    rw [i₈, k₇ 652 (by omega), k₇ 609 (by omega), q652,
      k₆ 609 (by omega) (by omega) (by omega) (by omega), v609, ← hfi,
      M₅ _ (by omega) (by have := hfk (M.face xg); omega)]
    exact mIm _
  have k656 : c₈.nreg 656 ≤ 1 := by rw [k₈ 656 (by omega)]; exact b₇
  have c653 : c₉.nreg 653 = 1 ↔ (M.face xg ∈ T₂.inside e ↔ M.face xg ∈ T₁.inside δ) := by
    rw [i₉, ← c656, ← c657]
    constructor
    · intro h; rw [h]
    · intro h; omega
  have c658 : c₁₀.nreg 658 = 1 ↔ M.face δ ∈ T₂.inside e := by
    rw [i₁₀, k₉ 654 (by omega), k₉ 539 (by omega), k₈ 654 (by omega), k₈ 539 (by omega),
      k₇ 654 (by omega), k₇ 539 (by omega), q654,
      k₆ 539 (by omega) (by omega) (by omega) (by omega), ← hfi, him₅]
  refine ⟨c₁₁, _, eR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [K11 514 (by omega), k₆ 514 (by omega) (by omega) (by omega) (by omega)]; exact h514
  · intro i hi; rw [M11]; exact hd₅ i hi
  · intro G; rw [M11, f539]; exact him₅ G
  · rw [k₁₁ 653 (by omega), k₁₀ 653 (by omega)]; exact b₉
  · rw [k₁₁ 653 (by omega), k₁₀ 653 (by omega)]; exact c653
  · exact b₁₁
  · have e653 : c₁₁.nreg 653 = c₉.nreg 653 := by rw [k₁₁ 653 (by omega), k₁₀ 653 (by omega)]
    rw [i₁₁, k₁₀ 653 (by omega), e653, ← c658]
    constructor
    · intro h; rw [h]
    · intro h; omega
  · intro x hx; rw [M11]; exact mA₅ x hx
  · intro a h1 h2
    rw [M11, hm₅ a h1 (by omega), M₄ a (by omega)]
  · intro r hr
    have : r < 650 ∨ 659 ≤ r := by omega
    rw [K11 r this, k₆ r (by omega) (by omega) (by omega) (by omega)]
    rcases hr with hr | hr | ⟨a, b⟩
    · exact B₅ r (Or.inl hr)
    · exact B₅ r (Or.inr hr)
    · exact G₅ r a (by omega)
  · rw [o₁₁, o₁₀, o₉, o₈, o₇, o₆, ho₅, od, oc, ob, ho₂, ho₁]

end Opt

/-! ### The guards of the options -/

section Guards

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

/-- **The guards of `arcOpt` in the deep case** (as in `PlanarSeparator.Map.deep_explicit`): for
a proper simple cycle `C` bounding the component `Y` of `δ` at level `l₂`, the two ancestors at
level `l₂` of the ends of `δ` lie on `C`, the root does not, `T₁` is flat on `C`, and the darts
of `C` are not tree darts of `T₁`. -/
theorem reroute_guards (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ) {T : M.SpTree}
    (hT : IsBFS T) {w : Q → ℝ} {l₀ l₂ : ℕ} {H : Finset M.Face} {K₀ : Finset Q} {c₀ : Q}
    {T₁ : M.SpTree} (hI : Inner T w l₀ H K₀ c₀ T₁) (hl : l₀ < l₂) {δ : D}
    (hz1 : M.face δ ∉ M.zone (T.low l₂)) (hz2 : M.face (M.α δ) ∉ M.zone (T.low l₂))
    (C : M.SCycle)
    (hC : ∀ d, (M.face d ∈ M.comp (T.low l₂) (M.face δ) ↔
      M.face (M.α d) ∈ M.comp (T.low l₂) (M.face δ)) ↔ ¬ C.Mem d) :
    topA T T₁ l₂ (M.vert δ) ∈ C.verts ∧ topA T T₁ l₂ (M.vert (M.α δ)) ∈ C.verts ∧
      T₁.root ∉ C.verts ∧
      (∀ i < C.k, ∀ j < C.k, T₁.height (M.vert (C.d i)) = T₁.height (M.vert (C.d j))) ∧
      (∀ i < C.k, ¬ T₁.IsTree (C.d i)) := by
  classical
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (htri d).φ_three
  have hl2 : 1 ≤ l₂ := by omega
  have hδY : M.face δ ∈ M.comp (T.low l₂) (M.face δ) := Map.mem_comp_self hz1
  have hαY : M.face (M.α δ) ∈ M.comp (T.low l₂) (M.face δ) := Map.mem_comp_of_adj hδY hz2
  have hlevC : ∀ v ∈ C.verts, T.height v = l₂ := fun v hv => Map.level_of_mem_verts hT h3 hC hv
  have hinsl : ∀ v ∈ ins (M.comp (T.low l₂) (M.face δ)), l₂ < T.height v := fun v hv => Map.lt_of_mem_ins hM hT hl2 hv
  obtain ⟨a, hax, haC, hxa⟩ := Map.exists_top hM hT hI hl hC _ (Map.touch_comp hC hδY)
  obtain ⟨b, hbz, hbC, hzb⟩ := Map.exists_top hM hT hI hl hC _ (Map.touch_comp hC hαY)
  have hta : topA T T₁ l₂ (M.vert δ) = a :=
    Map.topA_eq hax (hlevC a haC).le fun v hv hva => hinsl v (hxa v hv hva)
  have htb : topA T T₁ l₂ (M.vert (M.α δ)) = b :=
    Map.topA_eq hbz (hlevC b hbC).le fun v hv hvb => hinsl v (hzb v hv hvb)
  rw [hta, htb]
  obtain ⟨N, hN⟩ := hI.height₁
  refine ⟨haC, hbC, fun h => ?_, fun i hi j hj => ?_, ?_⟩
  · have := hlevC _ h
    rw [hI.root₁, hT.root] at this
    omega
  · have e1 := hlevC _ (C.mem_verts.2 ⟨i, hi, rfl⟩)
    have e2 := hlevC _ (C.mem_verts.2 ⟨j, hj, rfl⟩)
    rw [hN _ (by rw [e1]; exact hl), hN _ (by rw [e2]; exact hl), e1, e2]
  · rintro i hi ⟨v, hv, h⟩
    have e1 : T.height (M.vert (C.d i)) = l₂ := hlevC _ (C.mem_verts.2 ⟨i, hi, rfl⟩)
    have e2 : T.height (M.vert (M.α (C.d i))) = l₂ := by
      rw [C.vert_α_d_suc hi]
      exact hlevC _ (C.mem_verts.2 ⟨_, C.suc_lt hi, rfl⟩)
    rcases h with h | h
    · have hv' : M.vert (C.d i) = v := by rw [h, T₁.vert_par]
      have := hI.bfs₁ v hv (by rw [← hv', e1]; exact hl)
      rw [← h, e2, ← hv', e1] at this
      omega
    · have hv' : M.vert (M.α (C.d i)) = v := by rw [h, M.α_α, T₁.vert_par]
      have := hI.bfs₁ v hv (by rw [← hv', e2]; exact hl)
      rw [← h, e1, ← hv', e2] at this
      omega

end Guards

/-! ### The representative of the strict inside of `Y` -/

/-- One vertex `v = r628`: if its level `L v = r629` exceeds `l = r566` and the label of the face
of its dart `F v` is `h = r597`, then `r626 := 1` and `r627 := CN v`. -/
def rpBody : Stmt :=
  .seq (block [.addN 629 442 628, .loadN 629 629]) <|
  .seq (.ifLtN 566 629
    (.seq (block [.addN 629 595 628, .loadN 629 629, .divN 629 629 432, .addN 629 435 629,
        .loadN 629 629])
      (.ifLtN 629 597 .skip (.ifLtN 597 629 .skip
        (block [.constN 626 1, .addN 627 634 628, .loadN 627 627]))))
    .skip)
  (.instr (.addN 628 628 431))

/-- **The representative pass** over the vertices. -/
def rpPass : Stmt := .seq (block [.copyN 628 430, .copyN 626 430]) (.whileLtN 628 441 rpBody)

section RP

variable {W : ℕ} {P : Input}

set_option maxHeartbeats 4000000 in
/-- **The representative pass**: `r626 = 1` iff some vertex `v < n` has level `> l` and a dart
`F v` whose face has the label `h`, and then `r627 = CN v` for such a vertex. -/
theorem rpPass_exec {Lf Ff lb CNf : ℕ → ℕ} {k n bLv bF bL bCN l h : ℕ}
    (hW : bLv + n ≤ W ∧ bF + n ≤ W ∧ bL + k ≤ W ∧ bCN + n ≤ W) (c : Config)
    (hc : WordsBounded W c) (h430 : c.nreg 430 = 0) (h431 : c.nreg 431 = 1)
    (h432 : c.nreg 432 = 3) (h441 : c.nreg 441 = n) (h442 : c.nreg 442 = bLv)
    (h595 : c.nreg 595 = bF) (h435 : c.nreg 435 = bL) (h597 : c.nreg 597 = h)
    (h566 : c.nreg 566 = l) (h634 : c.nreg 634 = bCN)
    (mL : ∀ v < n, c.nmem (bLv + v) = Lf v) (mF : ∀ v < n, c.nmem (bF + v) = Ff v ∧ Ff v < 3 * k)
    (mlb : ∀ g < k, c.nmem (bL + g) = lb g) (mCN : ∀ v < n, c.nmem (bCN + v) = CNf v) :
    ∃ c' t, Exec P W rpPass c c' t ∧ t ≤ 19 * n + 4 ∧
      (c'.nreg 626 = 1 ↔ ∃ v < n, l < Lf v ∧ lb (Ff v / 3) = h) ∧
      (c'.nreg 626 = 1 → ∃ v < n, l < Lf v ∧ lb (Ff v / 3) = h ∧ c'.nreg 627 = CNf v) ∧
      (∀ r, r < 626 ∨ 630 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.output = c.output ∧ c'.nreg 626 ≤ 1 := by
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 628 = i ∧
    c'.nreg 441 = n ∧ i ≤ n ∧ (c'.nreg 626 = 1 ↔ ∃ v < i, l < Lf v ∧ lb (Ff v / 3) = h) ∧
    (c'.nreg 626 = 1 → ∃ v < i, l < Lf v ∧ lb (Ff v / 3) = h ∧ c'.nreg 627 = CNf v) ∧
    (∀ r, r < 626 ∨ 630 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.output = c.output ∧
    c'.nreg 626 ≤ 1
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 628 430, .copyN 626 430])
      c c₁ k₁ ∧ I 0 c₁ ∧ k₁ = 2 := by
    exec_block
    refine ⟨⟨‹_›, by config_simp; exact h430, by config_simp; exact h441, Nat.zero_le _,
      by config_simp; rw [h430]; simp, fun h' => by config_simp at h'; rw [h430] at h'; omega,
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl, rfl,
      by config_simp; rw [h430]; omega⟩, rfl⟩
  obtain ⟨c₂, t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 628) (rN := 441) (N := n)
    (lo := 0) (B := 17) (body := rpBody) I (fun i c' h' => ⟨h'.1, h'.2.1, h'.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h628, h441', hin, hf1, hf2, hr, hm, ho, hle⟩ hi => by
      have g : ∀ r, r < 626 ∨ 630 ≤ r → c₁.nreg r = c.nreg r := hr
      have v442 := (g 442 (by omega)).trans h442
      have v595 := (g 595 (by omega)).trans h595
      have v432 := (g 432 (by omega)).trans h432
      have v435 := (g 435 (by omega)).trans h435
      have v597 := (g 597 (by omega)).trans h597
      have v566 := (g 566 (by omega)).trans h566
      have v634 := (g 634 (by omega)).trans h634
      have v431 := (g 431 (by omega)).trans h431
      have hFi := mF i hi
      -- the level
      obtain ⟨ca, ka, ea, hka, qa, ra, ma, oa⟩ : ∃ ca ka, Exec P W
          (block [.addN 629 442 628, .loadN 629 629]) c₁ ca ka ∧ ka = 2 ∧ ca.nreg 629 = Lf i ∧
          (∀ r, r ≠ 629 → ca.nreg r = c₁.nreg r) ∧ ca.nmem = c₁.nmem ∧
          ca.output = c₁.output := by
        exec_block
        · rw [v442, h628]; omega
        · refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl⟩
          · config_simp; rw [v442, h628, hm]; exact mL i hi
          · config_simp; simp only [upd_apply]; split_ifs <;> omega
      have hwa := ea.wb_right
      -- the test and the update
      obtain ⟨cb, kb, eb, hkb, hb1, hb2, rb, mb, ob, hbl⟩ : ∃ cb kb, Exec P W
          (.ifLtN 566 629
            (.seq (block [.addN 629 595 628, .loadN 629 629, .divN 629 629 432,
                .addN 629 435 629, .loadN 629 629])
              (.ifLtN 629 597 .skip (.ifLtN 597 629 .skip
                (block [.constN 626 1, .addN 627 634 628, .loadN 627 627]))))
            .skip) ca cb kb ∧ kb ≤ 13 ∧
          (cb.nreg 626 = 1 ↔ ∃ v < i + 1, l < Lf v ∧ lb (Ff v / 3) = h) ∧
          (cb.nreg 626 = 1 → ∃ v < i + 1, l < Lf v ∧ lb (Ff v / 3) = h ∧ cb.nreg 627 = CNf v) ∧
          (∀ r, r ≠ 626 → r ≠ 627 → r ≠ 629 → cb.nreg r = c₁.nreg r) ∧ cb.nmem = c₁.nmem ∧
          cb.output = c₁.output ∧ cb.nreg 626 ≤ 1 := by
        have lt_succ : ∀ v, v < i + 1 ↔ v < i ∨ v = i := fun v => by omega
        by_cases hl : l < Lf i
        · obtain ⟨cc, kc, ec, hkc, qc, rc, mc, oc⟩ : ∃ cc kc, Exec P W
              (block [.addN 629 595 628, .loadN 629 629, .divN 629 629 432,
                .addN 629 435 629, .loadN 629 629]) ca cc kc ∧ kc = 5 ∧
              cc.nreg 629 = lb (Ff i / 3) ∧
              (∀ r, r ≠ 629 → cc.nreg r = c₁.nreg r) ∧ cc.nmem = c₁.nmem ∧
              cc.output = c₁.output := by
            have u595 : ca.nreg 595 = bF := (ra 595 (by omega)).trans v595
            have u628 : ca.nreg 628 = i := (ra 628 (by omega)).trans h628
            have u432 : ca.nreg 432 = 3 := (ra 432 (by omega)).trans v432
            have u435 : ca.nreg 435 = bL := (ra 435 (by omega)).trans v435
            have mF' : ca.nmem (bF + i) = Ff i := by rw [ma, hm]; exact hFi.1
            exec_block
            · rw [u595, u628]; omega
            · config_simp; rw [u595, u628, mF', u432, u435]; omega
            · refine ⟨rfl, ?_, fun r hr => ?_, by rw [ma], by rw [oa]⟩
              · config_simp; rw [u595, u628, mF', u432, u435, ma, hm]
                exact mlb _ (by omega)
              · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact ra r hr
          have hwc := ec.wb_right
          have t566 : ca.nreg 566 < ca.nreg 629 := by rw [qa, ra 566 (by omega), v566]; exact hl
          by_cases ha : cc.nreg 629 < cc.nreg 597
          · refine ⟨cc, _, .ifLtN_true t566 (.seq ec (.ifLtN_true ha (.skip hwc))), by omega,
              ?_, ?_, fun r _ _ d => rc r d, mc, oc, by rw [rc 626 (by omega)]; exact hle⟩
            · rw [rc 626 (by omega), hf1]
              constructor
              · rintro ⟨v, hv, h1⟩; exact ⟨v, by omega, h1⟩
              · rintro ⟨v, hv, h1, h2⟩
                rcases (lt_succ v).1 hv with hv | rfl
                · exact ⟨v, hv, h1, h2⟩
                · rw [qc, rc 597 (by omega), v597] at ha; omega
            · intro h'; rw [rc 626 (by omega)] at h'
              obtain ⟨v, hv, h1, h2, h3⟩ := hf2 h'
              exact ⟨v, by omega, h1, h2, by rw [rc 627 (by omega)]; exact h3⟩
          · by_cases hb : cc.nreg 597 < cc.nreg 629
            · refine ⟨cc, _, .ifLtN_true t566 (.seq ec (.ifLtN_false ha
                (.ifLtN_true hb (.skip hwc)))), by omega, ?_, ?_, fun r _ _ d => rc r d,
                mc, oc, by rw [rc 626 (by omega)]; exact hle⟩
              · rw [rc 626 (by omega), hf1]
                constructor
                · rintro ⟨v, hv, h1⟩; exact ⟨v, by omega, h1⟩
                · rintro ⟨v, hv, h1, h2⟩
                  rcases (lt_succ v).1 hv with hv | rfl
                  · exact ⟨v, hv, h1, h2⟩
                  · rw [qc, rc 597 (by omega), v597] at hb; omega
              · intro h'; rw [rc 626 (by omega)] at h'
                obtain ⟨v, hv, h1, h2, h3⟩ := hf2 h'
                exact ⟨v, by omega, h1, h2, by rw [rc 627 (by omega)]; exact h3⟩
            · have heq : lb (Ff i / 3) = h := by
                rw [qc, rc 597 (by omega), v597] at ha hb; omega
              obtain ⟨cd', kd, ed, hkd, q626, q627, rd, md, od⟩ : ∃ cd' kd, Exec P W
                  (block [.constN 626 1, .addN 627 634 628, .loadN 627 627]) cc cd' kd ∧
                  kd = 3 ∧ cd'.nreg 626 = 1 ∧ cd'.nreg 627 = CNf i ∧
                  (∀ r, r ≠ 626 → r ≠ 627 → cd'.nreg r = cc.nreg r) ∧ cd'.nmem = cc.nmem ∧
                  cd'.output = cc.output := by
                have u634 : cc.nreg 634 = bCN := (rc 634 (by omega)).trans v634
                have u628 : cc.nreg 628 = i := (rc 628 (by omega)).trans h628
                exec_block
                · omega
                · config_simp; rw [u634, u628]; omega
                · refine ⟨rfl, by config_simp, ?_, fun r a b => ?_, rfl, rfl⟩
                  · config_simp; rw [u634, u628, mc, hm]; exact mCN i hi
                  · config_simp; simp only [upd_apply]; split_ifs <;> omega
              refine ⟨cd', _, .ifLtN_true t566 (.seq ec (.ifLtN_false ha (.ifLtN_false hb ed))),
                by omega, ?_, fun _ => ⟨i, by omega, hl, heq, q627⟩,
                fun r a b d => by rw [rd r a b]; exact rc r d,
                by rw [md, mc], by rw [od, oc], by rw [q626]⟩
              rw [q626]; exact ⟨fun _ => ⟨i, by omega, hl, heq⟩, fun _ => rfl⟩
        · have t566 : ¬ ca.nreg 566 < ca.nreg 629 := by
            rw [qa, ra 566 (by omega), v566]; exact hl
          refine ⟨ca, _, .ifLtN_false t566 (.skip hwa), by omega, ?_, ?_,
            fun r _ _ d => ra r d, ma, oa, by rw [ra 626 (by omega)]; exact hle⟩
          · rw [ra 626 (by omega), hf1]
            constructor
            · rintro ⟨v, hv, h1⟩; exact ⟨v, by omega, h1⟩
            · rintro ⟨v, hv, h1, h2⟩
              rcases (lt_succ v).1 hv with hv | rfl
              · exact ⟨v, hv, h1, h2⟩
              · exact absurd h1 hl
          · intro h'; rw [ra 626 (by omega)] at h'
            obtain ⟨v, hv, h1, h2, h3⟩ := hf2 h'
            exact ⟨v, by omega, h1, h2, by rw [ra 627 (by omega)]; exact h3⟩
      have hwb := eb.wb_right
      have u628 : cb.nreg 628 = i := (rb 628 (by omega) (by omega) (by omega)).trans h628
      have u431 : cb.nreg 431 = 1 := (rb 431 (by omega) (by omega) (by omega)).trans v431
      have ec := Exec.addN (P := P) hwb 628 628 431 (by rw [u628, u431]; omega)
      refine ⟨_, _, .seq ea (.seq eb ec), ⟨ec.wb_right, ?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        by omega⟩
      · config_simp; rw [u628, u431]
      · config_simp; rw [rb 441 (by omega) (by omega) (by omega), h441']
      · config_simp; exact hb1
      · intro h'
        config_simp at h'
        obtain ⟨v, hv, h1, h2, h3⟩ := hb2 h'
        exact ⟨v, hv, h1, h2, by config_simp; exact h3⟩
      · intro r hr
        config_simp
        simp only [upd_apply]
        split_ifs with hh
        · omega
        · rw [rb r (by omega) (by omega) (by omega)]; exact g r hr
      · show cb.nmem = _; rw [mb, hm]
      · show cb.output = _; rw [ob, ho]
      · config_simp; exact hbl) (Nat.zero_le _) hI₁
  obtain ⟨-, -, -, -, hf1, hf2, hr, hm, ho, hle⟩ := hI
  exact ⟨c₂, 2 + t, .seq e₁ e, by omega, hf1, hf2, hr, hm, ho, hle⟩

end RP

/-! ### The wanted side -/

/-- **The decision of `deepWant`** from the representative `r627` (found iff `r626 = 1`), the
cycle marks at `bCv = r632` (stamp `r552`), the inside marks at `bIm = r608` (flag `r539`) read at
the dart `F` at `bF = r595`, and the two side weights `r562`, `r563`: `r624 = 1` iff nothing was
found, or the representative lies strictly inside, or on the cycle with the inside lighter. -/
def wDec : Stmt :=
  .ifLtN 430 626
    (.seq (block [.addN 645 632 627, .loadN 645 645, .addN 646 595 627, .loadN 646 646,
      .divN 646 646 432, .addN 646 608 646, .loadN 646 646]) <|
      .seq (nqb 647 645 552)
        (.ifLtN 430 647 (nqb 624 646 539)
          (.ifLtN 563 562 (.instr (.constN 624 0)) (.instr (.constN 624 1)))))
    (.instr (.constN 624 1))

section WDec

variable {W : ℕ} {P : Input}

set_option maxHeartbeats 4000000 in
theorem wDec_exec {bCv bF bIm rep fd s₂ fl Si So : ℕ} (c : Config) (hc : WordsBounded W c)
    (hW1 : 1 ≤ W) (h430 : c.nreg 430 = 0) (h432 : c.nreg 432 = 3) (h632 : c.nreg 632 = bCv)
    (h595 : c.nreg 595 = bF) (h608 : c.nreg 608 = bIm) (h627 : c.nreg 627 = rep)
    (h626 : c.nreg 626 = fd) (hfd : fd ≤ 1) (h552 : c.nreg 552 = s₂) (h539 : c.nreg 539 = fl)
    (h562 : c.nreg 562 = Si) (h563 : c.nreg 563 = So)
    (hb : fd = 1 → bCv + rep ≤ W ∧ bF + rep ≤ W ∧ bIm + c.nmem (bF + rep) / 3 ≤ W) :
    ∃ c' t, Exec P W wDec c c' t ∧ t ≤ 25 ∧ c'.nreg 624 ≤ 1 ∧
      (c'.nreg 624 = 1 ↔ (fd = 0 ∨ (c.nmem (bCv + rep) ≠ s₂ ∧
        c.nmem (bIm + c.nmem (bF + rep) / 3) ≠ fl) ∨
        (c.nmem (bCv + rep) = s₂ ∧ Si ≤ So))) ∧
      (∀ r, r ≠ 624 → r ≠ 645 → r ≠ 646 → r ≠ 647 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.output = c.output := by
  by_cases hf : c.nreg 430 < c.nreg 626
  swap
  · have hf0 : fd = 0 := by rw [h430, h626] at hf; omega
    refine ⟨_, _, .ifLtN_false hf (Exec.constN hc 624 1 hW1), by omega, by simp,
      by simp [hf0], fun r a b d _ => by simp [upd_other _ _ _ a], rfl, rfl⟩
  have hf1 : fd = 1 := by rw [h430, h626] at hf; omega
  obtain ⟨hb1, hb2, hb3⟩ := hb hf1
  obtain ⟨c₁, t₁, e₁, ht₁, q645, q646, r₁, m₁, o₁⟩ : ∃ c₁ t₁, Exec P W
      (block [.addN 645 632 627, .loadN 645 645, .addN 646 595 627, .loadN 646 646,
        .divN 646 646 432, .addN 646 608 646, .loadN 646 646]) c c₁ t₁ ∧ t₁ = 7 ∧
      c₁.nreg 645 = c.nmem (bCv + rep) ∧ c₁.nreg 646 = c.nmem (bIm + c.nmem (bF + rep) / 3) ∧
      (∀ r, r ≠ 645 → r ≠ 646 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; simp only [h632, h627, h595, h432, h608]; omega)
    refine ⟨rfl, ?_, ?_, fun r a b => ?_, rfl, rfl⟩
    all_goals config_simp
    · simp only [h632, h627]
    · simp only [h595, h627, h432, h608]
    · simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have g : ∀ r, r ≠ 645 → r ≠ 646 → c₁.nreg r = c.nreg r := r₁
  · obtain ⟨c₂, t₂, e₂, ht₂, b₂, i₂, k₂, m₂, o₂⟩ := nqb_exec (P := P) hW1 647 645 552 c₁ hw₁
    have hw₂ := e₂.wb_right
    have i₂' : c₂.nreg 647 = 1 ↔ c.nmem (bCv + rep) ≠ s₂ := by
      rw [i₂, q645, g 552 (by omega) (by omega), h552]
    by_cases hx : c₂.nreg 430 < c₂.nreg 647
    · have hx1 : c₂.nreg 647 = 1 := by
        rw [k₂ 430 (by omega), g 430 (by omega) (by omega), h430] at hx; omega
      obtain ⟨c₃, t₃, e₃, ht₃, b₃, i₃, k₃, m₃, o₃⟩ := nqb_exec (P := P) hW1 624 646 539 c₂ hw₂
      refine ⟨c₃, _, .ifLtN_true hf (.seq e₁ (.seq e₂ (.ifLtN_true hx e₃))), by omega, b₃, ?_,
        fun r a b d f => by rw [k₃ r a, k₂ r f, g r b d], by rw [m₃, m₂, m₁],
        by rw [o₃, o₂, o₁]⟩
      rw [i₃, k₂ 646 (by omega), k₂ 539 (by omega), q646, g 539 (by omega) (by omega), h539]
      have hne := i₂'.1 hx1
      constructor
      · intro h; exact Or.inr (Or.inl ⟨hne, h⟩)
      · rintro (h | ⟨-, h⟩ | ⟨h, -⟩)
        · omega
        · exact h
        · exact absurd h hne
    · have hx0 : ¬ c.nmem (bCv + rep) ≠ s₂ := fun h => by
        have := i₂'.2 h
        rw [k₂ 430 (by omega), g 430 (by omega) (by omega), h430] at hx; omega
      have v562 : c₂.nreg 562 = Si := by rw [k₂ 562 (by omega), g 562 (by omega) (by omega), h562]
      have v563 : c₂.nreg 563 = So := by rw [k₂ 563 (by omega), g 563 (by omega) (by omega), h563]
      by_cases hs : c₂.nreg 563 < c₂.nreg 562
      · refine ⟨_, _, .ifLtN_true hf (.seq e₁ (.seq e₂ (.ifLtN_false hx (.ifLtN_true hs
          (Exec.constN hw₂ 624 0 (by omega)))))), by omega, by simp, ?_,
          fun r a b d f => by simp [upd_other _ _ _ a, k₂ r f, g r b d], by simp [m₂, m₁],
          by simp [o₂, o₁]⟩
        simp only [Config.nreg_mk, upd_same]
        rw [v562, v563] at hs
        constructor
        · intro h; omega
        · rintro (h | ⟨h, -⟩ | ⟨-, h⟩)
          · omega
          · exact absurd h hx0
          · omega
      · refine ⟨_, _, .ifLtN_true hf (.seq e₁ (.seq e₂ (.ifLtN_false hx (.ifLtN_false hs
          (Exec.constN hw₂ 624 1 hW1))))), by omega, by simp, ?_,
          fun r a b d f => by simp [upd_other _ _ _ a, k₂ r f, g r b d], by simp [m₂, m₁],
          by simp [o₂, o₁]⟩
        simp only [Config.nreg_mk, upd_same]
        rw [v562, v563] at hs
        refine ⟨fun _ => Or.inr (Or.inr ⟨not_not.1 hx0, by omega⟩), fun _ => trivial⟩

end WDec

/-- The registers of `cvMark ; wPass` for the cycle of `δ` in `T₁` (at `bFc = r630`) and of the
fresh cycle marks (`bCv = r632`, stamp `1`), the moved weights (`bWC = r633`). -/
def wReg : List Instr :=
  [.constN 501 0, .copyN 502 434, .copyN 503 443, .constN 504 0, .copyN 505 441, .constN 506 0,
    .constN 507 0, .copyN 508 630, .constN 509 0, .constN 510 0, .constN 511 1,
    .copyN 530 605, .copyN 531 608, .constN 533 1, .constN 534 0, .constN 535 3, .copyN 536 606,
    .copyN 537 607, .constN 538 0, .copyN 551 632, .constN 552 1, .copyN 553 595, .copyN 554 633]

/-- **The test `deepWant`**: the cycle marks and the side weights of the cycle of `δ` in `T₁` for
the moved weights, the representative of the strict inside of `Y`, the decision (into `r624`). -/
def s10want : Stmt := .seq (block wReg) (.seq cvMark (.seq wPass (.seq rpPass wDec)))

section Want

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

set_option maxHeartbeats 16000000 in
/-- **The test `deepWant` on the machine.** -/
theorem s10want_spec {T T₁ : M.SpTree} {cn : Q → Q} {k n : ℕ} {cd : D ≃ Fin (3 * k)}
    {vi : Q ≃ Fin n} {V : ℕ → ℕ} {W : ℕ} {P : Input} {c : Config}
    {bV bL h bNx bCy bPos bLv bPr l x₀ u bFc bIm bF bCv bWC bCN l₂ fl hY : ℕ} {δ : D}
    {wP : Q → ℕ} {fdD : Q → D} (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ)
    (hT : IsBFS T) (hl2 : 1 ≤ l₂) (hδ : ¬ T₁.IsTree δ) (hcn : IsConc T l₂ cn)
    (hpos : 0 < ∑ v, wP v) (hV : ∀ x, V (cd x) = vi (M.vert x))
    (hfi : ∀ x : D, fi cd (M.face x) = (cd x : ℕ) / 3) (hfdD : ∀ u, M.vert (fdD u) = u)
    (hlay : bV + 3 * k ≤ bCv ∧ bFc + (T₁.fcycle δ).k ≤ bCv ∧ bF + n ≤ bCv ∧ bIm + k ≤ bCv ∧
      bLv + n ≤ bCv ∧ bL + k ≤ bCv ∧ bCN + n ≤ bCv ∧ bWC + n ≤ bCv ∧ bCv + n ≤ W)
    (hc : WordsBounded W c) (hB : BR 0 bV bL k h bNx bCy bPos n bLv bPr l x₀ u c)
    (h514 : c.nreg 514 = (T₁.fcycle δ).k) (h539 : c.nreg 539 = fl) (h566 : c.nreg 566 = l₂)
    (h597 : c.nreg 597 = hY) (h595 : c.nreg 595 = bF) (h605 : c.nreg 605 = k)
    (h606 : c.nreg 606 = 9 * k) (h607 : c.nreg 607 = 8 * k) (h608 : c.nreg 608 = bIm)
    (h630 : c.nreg 630 = bFc) (h632 : c.nreg 632 = bCv) (h633 : c.nreg 633 = bWC)
    (h634 : c.nreg 634 = bCN)
    (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x)
    (mFc : ∀ i < (T₁.fcycle δ).k, c.nmem (bFc + i) = cd ((T₁.fcycle δ).d i))
    (mIm : ∀ G : M.Face, c.nmem (bIm + fi cd G) ≠ fl ↔ G ∈ T₁.inside δ)
    (mF : ∀ u, c.nmem (bF + vi u) = cd (fdD u)) (mL : ∀ v, c.nmem (bLv + vi v) = T.height v)
    (mlab : ∀ y : D, c.nmem (bL + (cd y : ℕ) / 3) = hY ↔
      M.face y ∈ M.comp (T.low l₂) (M.face δ))
    (mWC : ∀ u, wcf cn (wR wP) u = (c.nmem (bWC + vi u) : ℝ) / ∑ v, (wP v : ℝ))
    (mCN : ∀ v, c.nmem (bCN + vi v) = vi (cn v)) (hCv : ∀ v < n, c.nmem (bCv + v) = 0)
    (htot : ∑ v ∈ range n, c.nmem (bWC + v) ≤ W) :
    ∃ c' t, Exec P W s10want c c' t ∧ t ≤ 9 * (T₁.fcycle δ).k + 44 * n + 60 ∧
      c'.nreg 624 ≤ 1 ∧
      (c'.nreg 624 = 1 ↔ deepWant T₁ cn (wR wP) (M.comp (T.low l₂) (M.face δ)) δ) ∧
      (∀ a, a < bCv ∨ bCv + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, (430 ≤ r ∧ r < 500) ∨ r = 514 ∨ r = 539 ∨ r = 566 ∨
        (590 ≤ r ∧ r ≠ 624 ∧ (r < 626 ∨ 630 ≤ r) ∧ (r < 645 ∨ 648 ≤ r)) →
        c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  classical
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := hlay
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (htri d).φ_three
  set K := (T₁.fcycle δ).k
  set Y := M.comp (T.low l₂) (M.face δ)
  have hk0 := (cd δ).2
  have hW1 : 1 ≤ W := by omega
  have hW3 : 3 ≤ W := by omega
  -- 0. the registers
  obtain ⟨c₁, t₁, e₁, ht₁, hF₁, hI₁, q551, q552, q553, q554, md, od⟩ : ∃ c₁ t₁,
      Exec P W (block wReg) c c₁ t₁ ∧ t₁ = 23 ∧ FR (c.nreg 500) 0 bV bPr 0 n 0 0 bFc 0 c₁ ∧
      IR k bIm 0 (c.nreg 547) c₁ ∧ c₁.nreg 551 = bCv ∧ c₁.nreg 552 = 1 ∧ c₁.nreg 553 = bF ∧
      c₁.nreg 554 = bWC ∧ c₁.nmem = c.nmem ∧ c₁.output = c.output := by
    have v434 := hB.r334
    have v443 := hB.r343
    have v441 := hB.r341
    unfold wReg
    exec_block
    all_goals try omega
    refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, rfl, rfl⟩
    all_goals config_simp
    all_goals first | rfl | assumption
  have hw₁ := e₁.wb_right
  have kd : ∀ r, (r < 501 ∨ (511 < r ∧ r < 530) ∨ (538 < r ∧ r < 551) ∨ 554 < r) →
      c₁.nreg r = c.nreg r := fun r hr =>
    e₁.nreg_of_wr (by simp [wReg, block, Stmt.wr, Instr.wr]; omega)
  have hV' : ∀ x < 3 * k, c₁.nmem (bV + x) = V x ∧ V x < n := fun x hx => by
    refine ⟨by rw [md]; exact mV x hx, ?_⟩
    have e' : x = cd (cd.symm ⟨x, hx⟩) := by simp
    rw [e', hV]; exact (vi _).2
  -- 1. the cycle marks
  obtain ⟨c₂, t₂, e₂, ht₂, hcv1, hcv2, hm₂, hr₂, ho₂⟩ :=
    cvMark_exec (P := P) (V := V) (cy := fun j => cd ((T₁.fcycle δ).d j)) (K := K) (bCv := bCv)
      (s₂ := 1) ⟨l1, l2⟩ l9 c₁ hw₁ hF₁ (by rw [kd 514 (by omega)]; exact h514) q551 q552
      (fun j hj => ⟨by rw [md]; exact mFc j hj, (cd _).2⟩) hV'
  have hw₂ := e₂.wb_right
  set cv : ℕ → ℕ := fun v => c₂.nmem (bCv + v)
  have M₂ : ∀ a, a < bCv → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hm₂ a (Or.inl ha), md]
  -- 2. the side weights for the moved weights
  have hF₂ := hF₁.of fun r a b => hr₂ r (by omega) (by omega)
  have hI₂ : IR k bIm 0 (c.nreg 547) c₂ :=
    ⟨(hr₂ 530 (by omega) (by omega)).trans hI₁.r530, (hr₂ 531 (by omega) (by omega)).trans hI₁.r531,
      (hr₂ 533 (by omega) (by omega)).trans hI₁.r533, (hr₂ 534 (by omega) (by omega)).trans hI₁.r534,
      (hr₂ 535 (by omega) (by omega)).trans hI₁.r535, (hr₂ 536 (by omega) (by omega)).trans hI₁.r536,
      (hr₂ 537 (by omega) (by omega)).trans hI₁.r537, (hr₂ 538 (by omega) (by omega)).trans hI₁.r538,
      (hr₂ 547 (by omega) (by omega)).trans hI₁.r547⟩
  have hfk : ∀ G : M.Face, fi cd G < k := fun G => by
    unfold fi; have := (cd (M.face_surjective G).choose).2; omega
  obtain ⟨c₃, t₃, e₃, ht₃, hSi, hSo, hm₃, hr₃, ho₃⟩ :=
    wPass_exec (P := P) (cv := cv) (fdN := fun v => c.nmem (bF + v))
      (im := fun f => c.nmem (bIm + f)) (w := fun v => c.nmem (bWC + v)) (fl := fl)
      ⟨l9, by omega, by omega, by omega⟩ c₂ hw₂ hF₂ hI₂
      (by rw [hr₂ 539 (by omega) (by omega), kd 539 (by omega)]; exact h539)
      (by rw [hr₂ 551 (by omega) (by omega)]; exact q551)
      (by rw [hr₂ 552 (by omega) (by omega), q552])
      (by rw [hr₂ 553 (by omega) (by omega)]; exact q553)
      (by rw [hr₂ 554 (by omega) (by omega)]; exact q554)
      (fun v _ => rfl)
      (fun v hv => ⟨M₂ _ (by omega), by
        rw [show v = vi (vi.symm ⟨v, hv⟩) by simp, mF]; exact (cd _).2⟩)
      (fun f hf => M₂ _ (by omega)) (fun v hv => M₂ _ (by omega)) htot
  have hw₃ := e₃.wb_right
  -- the sides through the coding
  have hcyc : ∀ u, cv (vi u) = 1 ↔ u ∈ T₁.cycV δ := by
    intro u
    rw [← SpTree.fcycle_verts hδ, SCycle.mem_verts]
    constructor
    · intro h'
      by_contra hn
      have := hcv2 _ (vi u).2 (fun ⟨j, hj, e⟩ => hn ⟨j, hj, by
        rw [hV] at e; exact vi.injective (Fin.ext e)⟩)
      simp only [cv] at h'
      rw [this, md, hCv _ (vi u).2] at h'; omega
    · rintro ⟨j, hj, e⟩
      exact hcv1 _ (vi u).2 ⟨j, hj, by rw [hV, e]⟩
  have hin : ∀ u, (cv (vi u) ≠ 1 ∧ c.nmem (bIm + c.nmem (bF + vi u) / 3) ≠ fl) ↔
      u ∈ T₁.inC δ := by
    intro u
    rw [mF, ← hfi, mIm, Ne, hcyc]
    constructor
    · rintro ⟨h1, h2⟩; exact (SpTree.mem_inC_iff hM h1 (hfdD u)).2 h2
    · intro h'
      have h1 : u ∉ T₁.cycV δ := SpTree.notMem_cycV_of_mem_inC h'
      exact ⟨h1, (SpTree.mem_inC_iff hM h1 (hfdD u)).1 h'⟩
  obtain ⟨wsi, wso⟩ := weigh_sides hM hδ cd vi hfi hV (cv := cv) (s₂ := 1)
    (w := fun v => c.nmem (bWC + v))
    (fun v hv hx => hcv1 v hv hx)
    (fun v hv hx => by simp only [cv]; rw [hcv2 v hv hx, md, hCv v hv]; omega)
    fdD hfdD (fdN := fun v => c.nmem (bF + v)) (fun u => mF u)
    (im := fun f => c.nmem (bIm + f)) mIm (fun u => c.nmem (bWC + vi u)) (fun u => rfl)
  -- 3. the representative
  have R₃ : ∀ r, (r < 556 ∨ 564 ≤ r) → c₃.nreg r = c₁.nreg r := fun r hr => by
    rw [hr₃ r (by omega), hr₂ r (by omega) (by omega)]
  have Rc : ∀ r, (430 ≤ r ∧ r < 501) ∨ 564 ≤ r → c₃.nreg r = c.nreg r := fun r hr => by
    rw [R₃ r (by omega), kd r (by omega)]
  have M₃ : ∀ a, a < bCv → c₃.nmem a = c.nmem a := fun a ha => by rw [hm₃]; exact M₂ a ha
  obtain ⟨c₄, t₄, e₄, ht₄, f₄, g₄, hr₄, hm₄, ho₄, hle₄⟩ :=
    rpPass_exec (P := P) (Lf := fun v => c.nmem (bLv + v)) (Ff := fun v => c.nmem (bF + v))
      (lb := fun g => c.nmem (bL + g)) (CNf := fun v => c.nmem (bCN + v)) (k := k) (n := n)
      (bLv := bLv) (bF := bF) (bL := bL) (bCN := bCN) (l := l₂) (h := hY)
      ⟨by omega, by omega, by omega, by omega⟩ c₃ hw₃
      ((Rc 430 (by omega)).trans hB.r330) ((Rc 431 (by omega)).trans hB.r331)
      ((Rc 432 (by omega)).trans hB.r332) ((Rc 441 (by omega)).trans hB.r341)
      ((Rc 442 (by omega)).trans hB.r342) ((Rc 595 (by omega)).trans h595)
      ((Rc 435 (by omega)).trans hB.r335) ((Rc 597 (by omega)).trans h597)
      ((Rc 566 (by omega)).trans h566) ((Rc 634 (by omega)).trans h634)
      (fun v hv => M₃ _ (by omega))
      (fun v hv => ⟨M₃ _ (by omega), by
        rw [show v = vi (vi.symm ⟨v, hv⟩) by simp, mF]; exact (cd _).2⟩)
      (fun g hg => M₃ _ (by omega)) (fun v hv => M₃ _ (by omega))
  have hw₄ := e₄.wb_right
  -- the condition of the pass is the strict inside of `Y`
  have hcond : ∀ w : Q, (l₂ < c.nmem (bLv + vi w) ∧ c.nmem (bL + c.nmem (bF + vi w) / 3) = hY) ↔
      w ∈ ins Y := fun w => by
    rw [mL, mF, mlab, mem_ins_comp_iff hM hT h3 hl2 (hfdD w)]
  -- 4. the decision
  have R₄ : ∀ r, r < 626 ∨ 630 ≤ r → c₄.nreg r = c₃.nreg r := hr₄
  have rep_lt : c₄.nreg 626 = 1 → c₄.nreg 627 < n := fun h' => by
    obtain ⟨v, hv, -, -, e⟩ := g₄ h'
    rw [e, show v = vi (vi.symm ⟨v, hv⟩) by simp, mCN]; exact (vi _).2
  obtain ⟨c₅, t₅, e₅, ht₅, b₅, i₅, hr₅, hm₅, ho₅⟩ :=
    wDec_exec (P := P) (bCv := bCv) (bF := bF) (bIm := bIm) (rep := c₄.nreg 627)
      (fd := c₄.nreg 626) (s₂ := 1) (fl := fl) (Si := c₃.nreg 562) (So := c₃.nreg 563) c₄ hw₄ hW1
      ((R₄ 430 (by omega)).trans ((Rc 430 (by omega)).trans hB.r330))
      ((R₄ 432 (by omega)).trans ((Rc 432 (by omega)).trans hB.r332))
      ((R₄ 632 (by omega)).trans ((Rc 632 (by omega)).trans h632))
      ((R₄ 595 (by omega)).trans ((Rc 595 (by omega)).trans h595))
      ((R₄ 608 (by omega)).trans ((Rc 608 (by omega)).trans h608)) rfl rfl hle₄
      ((R₄ 552 (by omega)).trans (by rw [hr₃ 552 (by omega), hr₂ 552 (by omega) (by omega), q552]))
      ((R₄ 539 (by omega)).trans
        (by rw [hr₃ 539 (by omega), hr₂ 539 (by omega) (by omega), kd 539 (by omega), h539]))
      (R₄ 562 (by omega)) (R₄ 563 (by omega)) (fun h' => by
        have hlt := rep_lt h'
        refine ⟨by omega, by omega, ?_⟩
        rw [hm₄, M₃ _ (by omega), show c₄.nreg 627 = vi (vi.symm ⟨_, hlt⟩) by simp, mF]
        have := (cd (fdD (vi.symm ⟨_, hlt⟩))).2
        omega)
  have hw₅ := e₅.wb_right
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega, b₅, ?_,
    fun a ha => by rw [hm₅, hm₄, hm₃, hm₂ a ha, md], fun r hr => ?_,
    by rw [ho₅, ho₄, ho₃, ho₂, od]⟩
  · rw [i₅]
    by_cases hY0 : ∃ w, w ∈ ins Y
    · obtain ⟨w₀, hw₀⟩ := hY0
      have e626 : c₄.nreg 626 = 1 := f₄.2 ⟨vi w₀, (vi w₀).2, (hcond w₀).2 hw₀⟩
      obtain ⟨v, hv, hc1, hc2, hrep⟩ := g₄ e626
      have hvu : v = vi (vi.symm ⟨v, hv⟩) := by simp
      set u₁ := vi.symm ⟨v, hv⟩
      have hu₁ : u₁ ∈ ins Y := (hcond u₁).1 (by rw [← hvu]; exact ⟨hc1, hc2⟩)
      have hrep' : c₄.nreg 627 = vi (cn u₁) := by rw [hrep, hvu, mCN]
      have hr : ∀ v ∈ ins Y, cn v = cn u₁ := fun v hv' =>
        Map.conc_eq_of_mem_ins hM hT h3 hcn hl2 hv' hu₁
      have hne : ins Y ≠ ∅ := fun h' => by rw [h'] at hu₁; simp at hu₁
      set r := cn u₁
      have him' : c₂.nmem (bIm + c₂.nmem (bF + vi r) / 3) =
          c.nmem (bIm + c.nmem (bF + vi r) / 3) := by
        have := (vi r).2
        rw [M₂ (bF + vi r) (by omega)]
        exact M₂ _ (by rw [mF]; have := (cd (fdD r)).2; omega)
      have A1 := hin r
      have A2 := hcyc r
      have L1 := lighter_iff hpos mWC (T₁.inC δ) (T₁.outC δ)
      have S1 : c₃.nreg 562 = ∑ u ∈ T₁.inC δ, c.nmem (bWC + vi u) := hSi.trans wsi
      have S2 : c₃.nreg 563 = ∑ u ∈ T₁.outC δ, c.nmem (bWC + vi u) := hSo.trans wso
      rw [deepWant_iff hr, hrep', hm₄, hm₃]
      constructor
      · rintro (h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · omega
        · exact Or.inr (Or.inl (A1.1 ⟨h1, by rwa [him'] at h2⟩))
        · exact Or.inr (Or.inr ⟨A2.1 h1, L1.2 (by rw [← S1, ← S2]; exact h2)⟩)
      · rintro (h0 | h1 | ⟨h1, h2⟩)
        · exact absurd h0 hne
        · obtain ⟨a1, a2⟩ := A1.2 h1
          exact Or.inr (Or.inl ⟨a1, by rw [him']; exact a2⟩)
        · exact Or.inr (Or.inr ⟨A2.2 h1, by rw [S1, S2]; exact L1.1 h2⟩)
    · have e626 : c₄.nreg 626 = 0 := by
        have : c₄.nreg 626 ≠ 1 := fun h' => by
          obtain ⟨v, hv, hc⟩ := f₄.1 h'
          refine hY0 ⟨vi.symm ⟨v, hv⟩, (hcond _).1 ?_⟩
          simpa using hc
        omega
      exact iff_of_true (Or.inl e626) fun v hv => absurd ⟨v, hv⟩ hY0
  · rw [hr₅ r (by omega) (by omega) (by omega) (by omega), hr₄ r (by omega), hr₃ r (by omega),
      hr₂ r (by omega) (by omega), kd r (by omega)]

end Want

/-! ### The rerouting branch -/

/-- The saved flag and dart of `δ` (`r609`, `r610`), and the indices `r621 = C.idx b`,
`r622 = C.idx a` of the two ancestors `b = r585`, `a = r584` by the positions at `bPos = r440`. -/
def rrA : List Instr :=
  [.copyN 609 539, .copyN 610 500, .addN 621 440 585, .loadN 621 621, .addN 622 440 584,
    .loadN 622 622]

/-- `r623 = C.off (C.idx b) (C.idx a)`. -/
def rrL : Stmt :=
  .ifLtN 622 621 (block [.addN 623 622 451, .subN 623 623 621]) (.instr (.subN 623 622 621))

/-- The first option: from `C.idx b`, `ℓ = L - 1`, in the region of `r611 … r615`. -/
def opt1Set : List Instr :=
  [.copyN 447 621, .subN 448 623 431, .copyN 600 611, .copyN 601 612, .copyN 602 613,
    .copyN 603 614, .copyN 604 615]

/-- The second option: from `C.idx a`, `ℓ = K - L - 1`, in the region of `r616 … r620`. -/
def opt2Set : List Instr :=
  [.copyN 447 622, .subN 448 451 623, .subN 448 448 431, .copyN 600 616, .copyN 601 617,
    .copyN 602 618, .copyN 603 619, .copyN 604 620]

/-- **The output registers** of an option: the darts at `r640` (number `r641`), the marks at
`r642` with the flag `r643` and the polarity `r644`. -/
def optOut : List Instr :=
  [.copyN 640 603, .copyN 641 514, .copyN 642 601, .copyN 643 539, .copyN 644 653]

/-- **The rerouting branch of `deepSep`**: the indices, `deepWant`, the first option, and the
second if the first does not put the face of `δ` on the wanted side. -/
def s10rr : Stmt :=
  .seq (block rrA) <| .seq rrL <| .seq s10want <| .seq (block opt1Set) <| .seq ropt <|
  .seq (eqb 659 655 624) <|
  .ifLtN 430 659 (block optOut) (.seq (block opt2Set) (.seq ropt (block optOut)))

section RR

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

omit [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] in
lemma fi_lt' {k : ℕ} (cd : D ≃ Fin (3 * k)) (G : M.Face) : fi cd G < k := by
  unfold fi; have := (cd (M.face_surjective G).choose).2; omega

/-- An option with its orientation, through the polarity. -/
lemma mem_orient {F : Type*} [Fintype F] [DecidableEq F] {X Z₀ : Finset F} {g G : F} {p : Prop}
    {_ : Decidable (g ∈ X ↔ g ∈ Z₀)} (hp : p ↔ (g ∈ X ↔ g ∈ Z₀)) :
    G ∈ (if (g ∈ X ↔ g ∈ Z₀) then X else Xᶜ) ↔ (G ∈ X ↔ p) := by
  by_cases h : (g ∈ X ↔ g ∈ Z₀)
  · simp only [h, ↓reduceIte]; tauto
  · simp only [h, ↓reduceIte, mem_compl]; tauto

set_option maxHeartbeats 32000000 in
/-- **The rerouting branch on the machine**: the output registers hold
`deepPick T₁ C δ a b (deepWant …) g₀` for the two ancestors `a`, `b` and the face `g₀` of the dart
at the root, with the face marks at `bI1` or `bI2`; the memory from `bF2 + 2 n + 1` on is kept. -/
theorem s10rr_spec {T T₁ : M.SpTree} {C : M.SCycle} {cn : Q → Q} {k n : ℕ}
    {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n} {A V : ℕ → ℕ} {W : ℕ} {P : Input} {c : Config}
    {bV bL h bNx bCy bPos bLv bPr l x₀ u bFc bIm bF bCv bWC bCN l₀ l₂ fl hY : ℕ}
    {bP1 bI1 bM1 bT1 bF1 bP2 bI2 bM2 bT2 bF2 : ℕ} {H : Finset M.Face} {K₀ : Finset Q} {c₀ : Q}
    {δ : D} {wP : Q → ℕ} {fdD : Q → D} (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ)
    (hT : IsBFS T) (hI : Inner T (wR wP) l₀ H K₀ c₀ T₁) (hl : l₀ < l₂) (hδ : ¬ T₁.IsTree δ)
    (hcn : IsConc T l₂ cn) (hpos : 0 < ∑ v, wP v)
    (hz1 : M.face δ ∉ M.zone (T.low l₂)) (hz2 : M.face (M.α δ) ∉ M.zone (T.low l₂))
    (hCp : C.Proper)
    (hC : ∀ d, (M.face d ∈ M.comp (T.low l₂) (M.face δ) ↔
      M.face (M.α d) ∈ M.comp (T.low l₂) (M.face δ)) ↔ ¬ C.Mem d)
    (hab : topA T T₁ l₂ (M.vert δ) ≠ topA T T₁ l₂ (M.vert (M.α δ)))
    (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hφ : ∀ x, (cd (M.φ x) : ℕ) = phi3 (cd x))
    (hV : ∀ x, V (cd x) = vi (M.vert x)) (hfi : ∀ x : D, fi cd (M.face x) = (cd x : ℕ) / 3)
    (hfdD : ∀ u, M.vert (fdD u) = u) (hr : (vi T₁.root : ℕ) = 0)
    (hlay : bV + 3 * k ≤ bCv ∧ bFc + (T₁.fcycle δ).k ≤ bCv ∧ bF + n ≤ bCv ∧ bIm + k ≤ bCv ∧
      bLv + n ≤ bCv ∧ bL + k ≤ bCv ∧ bCN + n ≤ bCv ∧ bWC + n ≤ bCv ∧ bPr + n ≤ bCv ∧
      bCy + C.k ≤ bCv ∧ bPos + n ≤ bCv ∧ bCv + n ≤ bP1 ∧ 11 * k ≤ bF ∧ 11 * k ≤ bIm ∧
      2 * C.k ≤ W ∧ bF1 + 2 * n + 1 ≤ bP2 ∧ 11 * k ≤ bPr ∧ 11 * k ≤ bCy)
    (hl1 : S9Lay k n bV bP1 bLv bI1 bM1 bT1 bF1 W) (hl2 : S9Lay k n bV bP2 bLv bI2 bM2 bT2 bF2 W)
    (hc : WordsBounded W c) (hB : BR 0 bV bL k h bNx bCy bPos n bLv bPr l x₀ u c)
    (h451 : c.nreg 451 = C.k) (h584 : c.nreg 584 = vi (topA T T₁ l₂ (M.vert δ)))
    (h585 : c.nreg 585 = vi (topA T T₁ l₂ (M.vert (M.α δ)))) (h500 : c.nreg 500 = cd δ)
    (h514 : c.nreg 514 = (T₁.fcycle δ).k) (h539 : c.nreg 539 = fl) (h566 : c.nreg 566 = l₂)
    (h597 : c.nreg 597 = hY) (h595 : c.nreg 595 = bF) (h605 : c.nreg 605 = k)
    (h606 : c.nreg 606 = 9 * k) (h607 : c.nreg 607 = 8 * k) (h608 : c.nreg 608 = bIm)
    (h630 : c.nreg 630 = bFc) (h632 : c.nreg 632 = bCv) (h633 : c.nreg 633 = bWC)
    (h634 : c.nreg 634 = bCN)
    (h611 : c.nreg 611 = bP1) (h612 : c.nreg 612 = bI1) (h613 : c.nreg 613 = bT1)
    (h614 : c.nreg 614 = bF1) (h615 : c.nreg 615 = bM1)
    (h616 : c.nreg 616 = bP2) (h617 : c.nreg 617 = bI2) (h618 : c.nreg 618 = bT2)
    (h619 : c.nreg 619 = bF2) (h620 : c.nreg 620 = bM2)
    (mA : ∀ x < 3 * k, c.nmem x = A x) (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x)
    (mL : ∀ v, c.nmem (bLv + vi v) = T.height v)
    (hPr : ∀ v (h : v ≠ T₁.root), c.nmem (bPr + vi v) = cd (T₁.par v h))
    (mCy : ∀ i < C.k, c.nmem (bCy + i) = cd (C.d i))
    (mPos : ∀ i < C.k, c.nmem (bPos + vi (M.vert (C.d i))) = i)
    (mFc : ∀ i < (T₁.fcycle δ).k, c.nmem (bFc + i) = cd ((T₁.fcycle δ).d i))
    (mIm : ∀ G : M.Face, c.nmem (bIm + fi cd G) ≠ fl ↔ G ∈ T₁.inside δ)
    (mF : ∀ u, c.nmem (bF + vi u) = cd (fdD u))
    (mlab : ∀ y : D, c.nmem (bL + (cd y : ℕ) / 3) = hY ↔
      M.face y ∈ M.comp (T.low l₂) (M.face δ))
    (mWC : ∀ u, wcf cn (wR wP) u = (c.nmem (bWC + vi u) : ℝ) / ∑ v, (wP v : ℝ))
    (mCN : ∀ v, c.nmem (bCN + vi v) = vi (cn v)) (hCv : ∀ v < n, c.nmem (bCv + v) = 0)
    (htot : ∑ v ∈ range n, c.nmem (bWC + v) ≤ W)
    (hM1 : ∀ v < n, c.nmem (bM1 + v) = 0) (hM2 : ∀ v < n, c.nmem (bM2 + v) = 0) :
    ∃ c' t, Exec P W s10rr c c' t ∧
      t ≤ 9 * (T₁.fcycle δ).k + 44 * n + 2 * (113 * k + 97 * n + 19 * C.k + 230) + 120 ∧
      c'.nreg 641 = (deepPick T₁ C δ (topA T T₁ l₂ (M.vert δ)) (topA T T₁ l₂ (M.vert (M.α δ)))
        (deepWant T₁ cn (wR wP) (M.comp (T.low l₂) (M.face δ)) δ) (M.face (fdD T₁.root))).1.k ∧
      (∀ i < (deepPick T₁ C δ (topA T T₁ l₂ (M.vert δ)) (topA T T₁ l₂ (M.vert (M.α δ)))
          (deepWant T₁ cn (wR wP) (M.comp (T.low l₂) (M.face δ)) δ) (M.face (fdD T₁.root))).1.k,
        c'.nmem (c'.nreg 640 + i) = cd ((deepPick T₁ C δ (topA T T₁ l₂ (M.vert δ))
          (topA T T₁ l₂ (M.vert (M.α δ))) (deepWant T₁ cn (wR wP) (M.comp (T.low l₂) (M.face δ)) δ)
          (M.face (fdD T₁.root))).1.d i)) ∧
      (∀ G : M.Face, G ∈ (deepPick T₁ C δ (topA T T₁ l₂ (M.vert δ))
          (topA T T₁ l₂ (M.vert (M.α δ))) (deepWant T₁ cn (wR wP) (M.comp (T.low l₂) (M.face δ)) δ)
          (M.face (fdD T₁.root))).2 ↔
        (c'.nmem (c'.nreg 642 + fi cd G) ≠ c'.nreg 643 ↔ c'.nreg 644 = 1)) ∧
      (c'.nreg 642 = bI1 ∨ c'.nreg 642 = bI2) ∧
      (∀ a, bF2 + 2 * n + 1 ≤ a → c'.nmem a = c.nmem a) ∧
      c'.output = c.output := by
  classical
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18⟩ :=
    hlay
  have hk0 := (cd δ).2
  have hk : 0 < k := by omega
  have hW1 : 1 ≤ W := by have := hl1.l11; omega
  have hl1' := hl1
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := hl1'
  have hl2' := hl2
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11⟩ := hl2'
  set a := topA T T₁ l₂ (M.vert δ)
  set b := topA T T₁ l₂ (M.vert (M.α δ))
  set want := deepWant T₁ cn (wR wP) (M.comp (T.low l₂) (M.face δ)) δ
  set g₀ := M.face (fdD T₁.root)
  obtain ⟨haC, hbC, hro, hflat, hnt⟩ :=
    reroute_guards hM htri hT hI hl hz1 hz2 C hC
  obtain ⟨hsk, hsb⟩ := C.idx_spec hbC
  obtain ⟨htk, hta⟩ := C.idx_spec haC
  set sb := C.idx b
  set sa := C.idx a
  have hst : sb ≠ sa := fun e =>
    hab ((hta.symm.trans (congrArg (fun i => M.vert (C.d i)) e.symm)).trans hsb)
  set L := C.off sb sa
  have hL1 : 1 ≤ L := by simp only [L, SCycle.off]; split_ifs <;> omega
  have hLk : L < C.k := C.off_lt hsk htk
  -- 1. the indices
  have mPb : c.nmem (bPos + vi b) = sb := by
    have := mPos sb hsk; rwa [hsb] at this
  have mPa : c.nmem (bPos + vi a) = sa := by
    have := mPos sa htk; rwa [hta] at this
  obtain ⟨c₁, t₁, e₁, ht₁, q609, q610, q621, q622, k₁, m₁, o₁⟩ : ∃ c₁ t₁,
      Exec P W (block rrA) c c₁ t₁ ∧ t₁ = 6 ∧ c₁.nreg 609 = fl ∧ c₁.nreg 610 = cd δ ∧
      c₁.nreg 621 = sb ∧ c₁.nreg 622 = sa ∧
      (∀ r, r ≠ 609 → r ≠ 610 → r ≠ 621 → r ≠ 622 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.output = c.output := by
    have v440 := hB.r340
    have hvb := (vi b).2
    have hva := (vi a).2
    unfold rrA
    exec_block
    all_goals try (config_simp; simp only [v440, h585, h584]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 => ?_, rfl, rfl⟩
    all_goals config_simp
    · exact h539
    · exact h500
    · simp only [v440, h585]; exact mPb
    · simp only [v440, h584]; exact mPa
    · simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, t₂, e₂, ht₂, q623, k₂, m₂, o₂⟩ : ∃ c₂ t₂, Exec P W rrL c₁ c₂ t₂ ∧ t₂ ≤ 4 ∧
      c₂.nreg 623 = L ∧ (∀ r, r ≠ 623 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
      c₂.output = c₁.output := by
    have v451 : c₁.nreg 451 = C.k := by rw [k₁ 451 (by omega) (by omega) (by omega) (by omega)]
                                        exact h451
    by_cases hlt : c₁.nreg 622 < c₁.nreg 621
    · obtain ⟨c₂, t₂, e₂, ht₂, q, kk, mm, oo⟩ : ∃ c₂ t₂, Exec P W
          (block [.addN 623 622 451, .subN 623 623 621]) c₁ c₂ t₂ ∧ t₂ = 2 ∧
          c₂.nreg 623 = sa + C.k - sb ∧ (∀ r, r ≠ 623 → c₂.nreg r = c₁.nreg r) ∧
          c₂.nmem = c₁.nmem ∧ c₂.output = c₁.output := by
        exec_block
        · rw [q622, v451]; omega
        · refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl⟩
          · config_simp; rw [q622, v451, q621]
          · config_simp; simp only [upd_apply]; split_ifs <;> omega
      refine ⟨c₂, _, .ifLtN_true hlt e₂, by omega, ?_, kk, mm, oo⟩
      rw [q]; rw [q621, q622] at hlt
      simp only [L, SCycle.off]; split_ifs <;> omega
    · refine ⟨_, _, .ifLtN_false hlt (Exec.subN hw₁ 623 622 621), by omega, ?_,
        fun r hr => by simp [upd_other _ _ _ hr], rfl, rfl⟩
      simp only [Config.nreg_mk, upd_same]
      rw [q621, q622] at hlt ⊢
      simp only [L, SCycle.off]; split_ifs <;> omega
  have hw₂ := e₂.wb_right
  have K₂ : ∀ r, r ≠ 609 → r ≠ 610 → r ≠ 621 → r ≠ 622 → r ≠ 623 → c₂.nreg r = c.nreg r :=
    fun r a1 a2 a3 a4 a5 => by rw [k₂ r a5, k₁ r a1 a2 a3 a4]
  have M₂ : c₂.nmem = c.nmem := by rw [m₂, m₁]
  have KK : ∀ r, 590 ≤ r → r ≠ 609 → r ≠ 610 → (r < 621 ∨ 623 < r) → c₂.nreg r = c.nreg r :=
    fun r a b d f => K₂ r b d (by omega) (by omega) (by omega)
  -- 2. the wanted side
  obtain ⟨c₃, t₃, e₃, ht₃, b₃, i₃, hm₃, hr₃, ho₃⟩ :=
    s10want_spec (T := T) (T₁ := T₁) (cn := cn) (V := V) (P := P) (c := c₂) (wP := wP)
      (fdD := fdD) (bV := bV) (bL := bL) (h := h) (bNx := bNx) (bCy := bCy) (bPos := bPos)
      (bLv := bLv) (bPr := bPr) (l := l) (x₀ := x₀) (u := u) (fl := fl) (hY := hY) (l₂ := l₂)
      hM htri hT (by omega) hδ hcn hpos
      hV hfi hfdD ⟨y1, y2, y3, y4, y5, y6, y7, y8, by omega⟩ hw₂
      (hB.of fun r a b => K₂ r (by omega) (by omega) (by omega) (by omega) (by omega))
      (by rw [K₂ 514 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h514)
      (by rw [K₂ 539 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h539)
      (by rw [K₂ 566 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h566)
      (by rw [K₂ 597 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h597)
      ((KK 595 (by omega) (by omega) (by omega) (by omega)).trans h595)
      ((KK 605 (by omega) (by omega) (by omega) (by omega)).trans h605)
      ((KK 606 (by omega) (by omega) (by omega) (by omega)).trans h606)
      ((KK 607 (by omega) (by omega) (by omega) (by omega)).trans h607)
      ((KK 608 (by omega) (by omega) (by omega) (by omega)).trans h608)
      ((KK 630 (by omega) (by omega) (by omega) (by omega)).trans h630)
      ((KK 632 (by omega) (by omega) (by omega) (by omega)).trans h632)
      ((KK 633 (by omega) (by omega) (by omega) (by omega)).trans h633)
      ((KK 634 (by omega) (by omega) (by omega) (by omega)).trans h634)
      (by rw [M₂]; exact mV) (by rw [M₂]; exact mFc) (by rw [M₂]; exact mIm)
      (by rw [M₂]; exact mF) (by rw [M₂]; exact mL) (by rw [M₂]; exact mlab)
      (by rw [M₂]; exact mWC) (by rw [M₂]; exact mCN) (by rw [M₂]; exact hCv)
      (by rw [M₂]; exact htot)
  have hw₃ := e₃.wb_right
  have K₃ : ∀ r, (430 ≤ r ∧ r < 500) ∨ (590 ≤ r ∧ r ≠ 624 ∧ (r < 626 ∨ 630 ≤ r) ∧
      (r < 645 ∨ 648 ≤ r)) → c₃.nreg r = c₂.nreg r := fun r hr => hr₃ r (by omega)
  have M₃ : ∀ a, a < bCv → c₃.nmem a = c.nmem a := fun a ha => by
    rw [hm₃ a (Or.inl ha), M₂]
  -- 3. the first option
  have hC₁ : ∀ i < C.k, T₁.height (M.vert (C.d i)) = T₁.height (M.vert (C.d sb)) :=
    fun i hi => hflat i hi sb hsk
  have hC₂ : ∀ i < C.k, T₁.height (M.vert (C.d i)) = T₁.height (M.vert (C.d sa)) :=
    fun i hi => hflat i hi sa htk
  obtain ⟨c₄, t₄, e₄, ht₄, q447, q448, q600, q601, q602, q603, q604, m₄, o₄⟩ : ∃ c₄ t₄,
      Exec P W (block opt1Set) c₃ c₄ t₄ ∧ t₄ = 7 ∧ c₄.nreg 447 = sb ∧ c₄.nreg 448 = L - 1 ∧
      c₄.nreg 600 = bP1 ∧ c₄.nreg 601 = bI1 ∧ c₄.nreg 602 = bT1 ∧ c₄.nreg 603 = bF1 ∧
      c₄.nreg 604 = bM1 ∧ c₄.nmem = c₃.nmem ∧ c₄.output = c₃.output := by
    have v621 : c₃.nreg 621 = sb := by rw [K₃ 621 (by omega), k₂ 621 (by omega)]; exact q621
    have v623 : c₃.nreg 623 = L := by rw [K₃ 623 (by omega)]; exact q623
    have v431 : c₃.nreg 431 = 1 := by
      rw [K₃ 431 (by omega), K₂ 431 (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hB.r331
    have v611 : c₃.nreg 611 = bP1 := by
      rw [K₃ 611 (by omega), KK 611 (by omega) (by omega) (by omega) (by omega), h611]
    have v612 : c₃.nreg 612 = bI1 := by
      rw [K₃ 612 (by omega), KK 612 (by omega) (by omega) (by omega) (by omega), h612]
    have v613 : c₃.nreg 613 = bT1 := by
      rw [K₃ 613 (by omega), KK 613 (by omega) (by omega) (by omega) (by omega), h613]
    have v614 : c₃.nreg 614 = bF1 := by
      rw [K₃ 614 (by omega), KK 614 (by omega) (by omega) (by omega) (by omega), h614]
    have v615 : c₃.nreg 615 = bM1 := by
      rw [K₃ 615 (by omega), KK 615 (by omega) (by omega) (by omega) (by omega), h615]
    unfold opt1Set
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
    all_goals config_simp
    all_goals try assumption
    rw [v623, v431]
  have hw₄ := e₄.wb_right
  have k₄ : ∀ r, (r < 447 ∨ 448 < r) → (r < 600 ∨ 604 < r) → c₄.nreg r = c₃.nreg r :=
    fun r a b => e₄.nreg_of_wr (by simp [opt1Set, block, Stmt.wr, Instr.wr]; omega)
  have G₄ : ∀ r, (430 ≤ r ∧ r < 447) ∨ r = 451 ∨ (590 ≤ r ∧ r < 600) ∨ (604 < r ∧ r ≠ 609 ∧
      r ≠ 610 ∧ (r < 621 ∨ 623 < r) ∧ r ≠ 624 ∧ (r < 626 ∨ 630 ≤ r) ∧ (r < 645 ∨ 648 ≤ r)) →
      c₄.nreg r = c.nreg r := fun r hr => by
    rw [k₄ r (by omega) (by omega), K₃ r (by omega),
      K₂ r (by omega) (by omega) (by omega) (by omega) (by omega)]
  have M₄ : ∀ a, a < bCv → c₄.nmem a = c.nmem a := fun a ha => by rw [m₄]; exact M₃ a ha
  have mF0 : c.nmem bF = cd (fdD T₁.root) := by have := mF T₁.root; rwa [hr, add_zero] at this
  obtain ⟨c₅, t₅, e₅, ht₅, h514₅, hd₅, him₅, b653, i653, b655, i655, mA₅, hm₅, hr₅, ho₅⟩ :=
    ropt_spec (T := T) (T₁ := T₁) (C := C) (A := A) (V := V) (P := P) (c := c₄) (bV := bV)
      (bL := bL) (h := h) (bNx := bNx) (bCy := bCy) (bPos := bPos) (bLv := bLv) (bPr := bPr)
      (l := l) (x₀ := x₀) (u := u) (bF := bF) (bIm := bIm) (fl₁ := fl) (δ := δ)
      (xg := fdD T₁.root) hM hk hAcd hφ hV hfi hr hsk (by omega) hro hC₁ hnt hCp hl1
      ⟨by omega, by omega, by omega, by omega, y13, by omega, y14, by omega, y15⟩ hw₄
      (hB.of fun r a b => G₄ r (by omega))
      ((G₄ 451 (by omega)).trans h451) q447 q448 q600 q601 q602 q603 q604
      ((G₄ 605 (by omega)).trans h605) ((G₄ 606 (by omega)).trans h606)
      ((G₄ 607 (by omega)).trans h607) ((G₄ 595 (by omega)).trans h595)
      ((G₄ 608 (by omega)).trans h608)
      (by rw [k₄ 609 (by omega) (by omega), K₃ 609 (by omega), k₂ 609 (by omega)]; exact q609)
      (by rw [k₄ 610 (by omega) (by omega), K₃ 610 (by omega), k₂ 610 (by omega)]; exact q610)
      (fun x hx => by rw [M₄ x (by omega)]; exact mA x hx)
      (fun x hx => by rw [M₄ _ (by omega)]; exact mV x hx)
      (fun v => by have := (vi v).2; rw [M₄ _ (by omega)]; exact mL v)
      (fun v hv => by have := (vi v).2; rw [M₄ _ (by omega)]; exact hPr v hv)
      (fun i hi => by rw [M₄ _ (by omega)]; exact mCy i hi)
      (by rw [M₄ _ (by omega)]; exact mF0)
      (fun G => by have := fi_lt' cd G; rw [M₄ _ (by omega)]; exact mIm G)
      (fun v hv => by rw [m₄, hm₃ _ (Or.inr (by omega)), M₂]; exact hM1 v hv)
  have hw₅ := e₅.wb_right
  have hkL : C.k - L - 1 + 1 < C.k := by omega
  -- the first option, explicitly
  have ho₁ : arcOpt T₁ C sb L (T₁.inside δ) g₀ (T₁.fcycle δ) =
      arcOptOf (T₁.arcTree C sb (L - 1) hsk hro hC₁) (C.d (C.idxAt sb (L - 1))) (T₁.inside δ)
        g₀ := by
    rw [arcOpt, dite_eq_left_of_eq_true (eq_true ⟨hsk, hro, hC₁⟩)]
  have mem₁ : ∀ G, G ∈ (arcOpt T₁ C sb L (T₁.inside δ) g₀ (T₁.fcycle δ)).2 ↔
      (G ∈ (T₁.arcTree C sb (L - 1) hsk hro hC₁).inside (C.d (C.idxAt sb (L - 1))) ↔
        c₅.nreg 653 = 1) := fun G => by
    rw [ho₁, arcOptOf]; exact mem_orient i653
  have face₁ : M.face δ ∈ (arcOpt T₁ C sb L (T₁.inside δ) g₀ (T₁.fcycle δ)).2 ↔
      c₅.nreg 655 = 1 := (mem₁ (M.face δ)).trans i655.symm
  obtain ⟨c₆, t₆, e₆, ht₆, b₆, i₆, k₆, m₆, o₆⟩ := eqb_exec (P := P) hW1 659 655 624 c₅ hw₅
  have hw₆ := e₆.wb_right
  have v624 : c₅.nreg 624 = c₃.nreg 624 := by
    rw [hr₅ 624 (by omega), k₄ 624 (by omega) (by omega)]
  have test : c₆.nreg 659 = 1 ↔
      (M.face δ ∈ (arcOpt T₁ C sb L (T₁.inside δ) g₀ (T₁.fcycle δ)).2 ↔ want) := by
    rw [i₆, face₁, v624]
    have := b655; have := b₃
    constructor
    · intro h'; rw [h']; exact i₃
    · intro h'
      by_cases q : c₅.nreg 655 = 1
      · have := i₃.2 (h'.1 q); omega
      · have : ¬ c₃.nreg 624 = 1 := fun z => q (h'.2 (i₃.1 z))
        omega
  have v430 : c₆.nreg 430 = 0 := by
    rw [k₆ 430 (by omega), hr₅ 430 (by omega), G₄ 430 (by omega)]; exact hB.r330
  have hdp : deepPick T₁ C δ a b want g₀ =
      if (M.face δ ∈ (arcOpt T₁ C sb L (T₁.inside δ) g₀ (T₁.fcycle δ)).2 ↔ want) then
        arcOpt T₁ C sb L (T₁.inside δ) g₀ (T₁.fcycle δ)
      else arcOpt T₁ C sa (C.k - L) (T₁.inside δ) g₀ (T₁.fcycle δ) := rfl
  by_cases hx : c₆.nreg 430 < c₆.nreg 659
  · have h659 : c₆.nreg 659 = 1 := by rw [v430] at hx; omega
    have hpick : deepPick T₁ C δ a b want g₀ = arcOpt T₁ C sb L (T₁.inside δ) g₀ (T₁.fcycle δ) :=
      by rw [hdp]; exact ite_eq_left_of_eq_true _ _ (eq_true (test.1 h659))
    obtain ⟨c₇, t₇, e₇, ht₇, q640, q641, q642, q643, q644, m₇, o₇⟩ : ∃ c₇ t₇,
        Exec P W (block optOut) c₆ c₇ t₇ ∧ t₇ = 5 ∧ c₇.nreg 640 = bF1 ∧
        c₇.nreg 641 = c₅.nreg 514 ∧ c₇.nreg 642 = bI1 ∧ c₇.nreg 643 = c₅.nreg 539 ∧
        c₇.nreg 644 = c₅.nreg 653 ∧ c₇.nmem = c₆.nmem ∧ c₇.output = c₆.output := by
      have v603 : c₆.nreg 603 = bF1 := by rw [k₆ 603 (by omega), hr₅ 603 (by omega), q603]
      have v601 : c₆.nreg 601 = bI1 := by rw [k₆ 601 (by omega), hr₅ 601 (by omega), q601]
      have v514 := k₆ 514 (by omega)
      have v539 := k₆ 539 (by omega)
      have v653 := k₆ 653 (by omega)
      unfold optOut
      exec_block
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
      all_goals config_simp
      all_goals assumption
    refine ⟨c₇, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.ifLtN_true hx e₇)))))),
      by omega, ?_, ?_, ?_, Or.inl q642, fun a ha => ?_, ?_⟩
    · rw [hpick, ho₁, q641]; exact h514₅
    · intro i hi; rw [hpick, ho₁] at hi ⊢; rw [q640, m₇, m₆]; exact hd₅ i hi
    · intro G
      rw [hpick, mem₁, q642, q643, q644, m₇, m₆, him₅]
    · rw [m₇, m₆, hm₅ a (by omega) (Or.inr (by omega)), m₄, hm₃ _ (Or.inr (by omega)), M₂]
    · rw [o₇, o₆, ho₅, o₄, ho₃, o₂, o₁]
  · have hsel : ¬ (M.face δ ∈ (arcOpt T₁ C sb L (T₁.inside δ) g₀ (T₁.fcycle δ)).2 ↔ want) :=
      fun h' => hx (by rw [v430, test.2 h']; omega)
    have hpick : deepPick T₁ C δ a b want g₀ =
        arcOpt T₁ C sa (C.k - L) (T₁.inside δ) g₀ (T₁.fcycle δ) := by
      rw [hdp]; exact ite_eq_right_of_eq_false _ _ (eq_false hsel)
    have G₆ : ∀ r, (430 ≤ r ∧ r < 447) ∨ r = 451 ∨ (590 ≤ r ∧ r < 600) ∨ (604 < r ∧ r ≠ 609 ∧
        r ≠ 610 ∧ (r < 621 ∨ 623 < r) ∧ r ≠ 624 ∧ (r < 626 ∨ 630 ≤ r) ∧ (r < 645 ∨ 648 ≤ r) ∧
        (r < 650 ∨ 659 < r)) → c₆.nreg r = c.nreg r := fun r hr => by
      rw [k₆ r (by omega), hr₅ r (by omega), G₄ r (by omega)]
    have Q6 : ∀ r, 604 < r → r < 650 → c₆.nreg r = c₃.nreg r := fun r a b' => by
      rw [k₆ r (by omega), hr₅ r (by omega), k₄ r (by omega) (by omega)]
    obtain ⟨c₇, t₇, e₇, ht₇, p447, p448, p600, p601, p602, p603, p604, m₇, o₇⟩ : ∃ c₇ t₇,
        Exec P W (block opt2Set) c₆ c₇ t₇ ∧ t₇ = 8 ∧ c₇.nreg 447 = sa ∧
        c₇.nreg 448 = C.k - L - 1 ∧ c₇.nreg 600 = bP2 ∧ c₇.nreg 601 = bI2 ∧
        c₇.nreg 602 = bT2 ∧ c₇.nreg 603 = bF2 ∧ c₇.nreg 604 = bM2 ∧ c₇.nmem = c₆.nmem ∧
        c₇.output = c₆.output := by
      have v622 : c₆.nreg 622 = sa := by
        rw [Q6 622 (by omega) (by omega), K₃ 622 (by omega), k₂ 622 (by omega)]; exact q622
      have v623 : c₆.nreg 623 = L := by
        rw [Q6 623 (by omega) (by omega), K₃ 623 (by omega)]; exact q623
      have v451 : c₆.nreg 451 = C.k := (G₆ 451 (by omega)).trans h451
      have v431 : c₆.nreg 431 = 1 := (G₆ 431 (by omega)).trans hB.r331
      have v616 := (G₆ 616 (by omega)).trans h616
      have v617 := (G₆ 617 (by omega)).trans h617
      have v618 := (G₆ 618 (by omega)).trans h618
      have v619 := (G₆ 619 (by omega)).trans h619
      have v620 := (G₆ 620 (by omega)).trans h620
      unfold opt2Set
      exec_block
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
      all_goals config_simp
      all_goals try assumption
      rw [v451, v623, v431]
    have hw₇ := e₇.wb_right
    have k₇ : ∀ r, (r < 447 ∨ 448 < r) → (r < 600 ∨ 604 < r) → c₇.nreg r = c₆.nreg r :=
      fun r a b => e₇.nreg_of_wr (by simp [opt2Set, block, Stmt.wr, Instr.wr]; omega)
    have G₇ : ∀ r, (430 ≤ r ∧ r < 447) ∨ r = 451 ∨ (590 ≤ r ∧ r < 600) ∨ (604 < r ∧ r ≠ 609 ∧
        r ≠ 610 ∧ (r < 621 ∨ 623 < r) ∧ r ≠ 624 ∧ (r < 626 ∨ 630 ≤ r) ∧ (r < 645 ∨ 648 ≤ r) ∧
        (r < 650 ∨ 659 < r)) → c₇.nreg r = c.nreg r := fun r hr => by
      rw [k₇ r (by omega) (by omega)]; exact G₆ r hr
    have M₇ : ∀ a, 11 * k ≤ a → a < bCv → c₇.nmem a = c.nmem a := fun a h1 h2 => by
      rw [m₇, m₆, hm₅ a h1 (Or.inl (by omega))]; exact M₄ a h2
    obtain ⟨c₈, t₈, e₈, ht₈, h514₈, hd₈, him₈, -, i653₈, -, -, -, hm₈, hr₈, ho₈⟩ :=
      ropt_spec (T := T) (T₁ := T₁) (C := C) (A := A) (V := V) (P := P) (c := c₇) (bV := bV)
        (bL := bL) (h := h) (bNx := bNx) (bCy := bCy) (bPos := bPos) (bLv := bLv) (bPr := bPr)
        (l := l) (x₀ := x₀) (u := u) (bF := bF) (bIm := bIm) (fl₁ := fl) (δ := δ)
        (xg := fdD T₁.root) hM hk hAcd hφ hV hfi hr htk hkL hro hC₂ hnt hCp hl2
        ⟨by omega, by omega, by omega, by omega, y13, by omega, y14, by omega, y15⟩ hw₇
        (hB.of fun r a b => G₇ r (by omega))
        ((G₇ 451 (by omega)).trans h451) p447 p448 p600 p601 p602 p603 p604
        ((G₇ 605 (by omega)).trans h605) ((G₇ 606 (by omega)).trans h606)
        ((G₇ 607 (by omega)).trans h607) ((G₇ 595 (by omega)).trans h595)
        ((G₇ 608 (by omega)).trans h608)
        (by rw [k₇ 609 (by omega) (by omega), Q6 609 (by omega) (by omega), K₃ 609 (by omega),
          k₂ 609 (by omega)]; exact q609)
        (by rw [k₇ 610 (by omega) (by omega), Q6 610 (by omega) (by omega), K₃ 610 (by omega),
          k₂ 610 (by omega)]; exact q610)
        (fun x hx => by rw [m₇, m₆]; exact mA₅ x hx)
        (fun x hx => by rw [M₇ _ (by omega) (by omega)]; exact mV x hx)
        (fun v => by have := (vi v).2; rw [M₇ _ (by omega) (by omega)]; exact mL v)
        (fun v hv => by have := (vi v).2; rw [M₇ _ (by omega) (by omega)]; exact hPr v hv)
        (fun i hi => by rw [M₇ _ (by omega) (by omega)]; exact mCy i hi)
        (by rw [M₇ _ (by omega) (by omega)]; exact mF0)
        (fun G => by have := fi_lt' cd G; rw [M₇ _ (by omega) (by omega)]; exact mIm G)
        (fun v hv => by
          rw [m₇, m₆, hm₅ _ (by omega) (Or.inr (by omega)), m₄, hm₃ _ (Or.inr (by omega)), M₂]
          exact hM2 v hv)
    have hw₈ := e₈.wb_right
    have ho₂ : arcOpt T₁ C sa (C.k - L) (T₁.inside δ) g₀ (T₁.fcycle δ) =
        arcOptOf (T₁.arcTree C sa (C.k - L - 1) htk hro hC₂) (C.d (C.idxAt sa (C.k - L - 1)))
          (T₁.inside δ) g₀ := by
      rw [arcOpt, dite_eq_left_of_eq_true (eq_true ⟨htk, hro, hC₂⟩)]
    obtain ⟨c₉, t₉, e₉, ht₉, q640, q641, q642, q643, q644, m₉, o₉⟩ : ∃ c₉ t₉,
        Exec P W (block optOut) c₈ c₉ t₉ ∧ t₉ = 5 ∧ c₉.nreg 640 = bF2 ∧
        c₉.nreg 641 = c₈.nreg 514 ∧ c₉.nreg 642 = bI2 ∧ c₉.nreg 643 = c₈.nreg 539 ∧
        c₉.nreg 644 = c₈.nreg 653 ∧ c₉.nmem = c₈.nmem ∧ c₉.output = c₈.output := by
      have v603 : c₈.nreg 603 = bF2 := by rw [hr₈ 603 (by omega), p603]
      have v601 : c₈.nreg 601 = bI2 := by rw [hr₈ 601 (by omega), p601]
      unfold optOut
      exec_block
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
      all_goals config_simp
      all_goals first | rfl | assumption
    refine ⟨c₉, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.ifLtN_false hx
      (.seq e₇ (.seq e₈ e₉)))))))), by omega, ?_, ?_, ?_, Or.inr q642, fun a ha => ?_, ?_⟩
    · rw [hpick, ho₂, q641]; exact h514₈
    · intro i hi; rw [hpick, ho₂] at hi ⊢; rw [q640, m₉]; exact hd₈ i hi
    · intro G
      rw [hpick, ho₂, arcOptOf, mem_orient i653₈, q642, q643, q644, m₉, him₈]
    · rw [m₉, hm₈ a (by omega) (Or.inr (by omega)), m₇, m₆, hm₅ a (by omega) (Or.inr (by omega)),
        m₄, hm₃ _ (Or.inr (by omega)), M₂]
    · rw [o₉, ho₈, o₇, o₆, ho₅, o₄, ho₃, o₂, o₁]

end RR

end MillerProg

end PlanarSeparator
