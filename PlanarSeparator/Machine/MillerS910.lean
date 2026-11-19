module

public import PlanarSeparator.Machine.MillerA
public import PlanarSeparator.Machine.MillerWeigh

/-!
# Miller's separator on the machine: the band case of step 9 after steps 1–8

After `millerA` (steps 1–8, `MillerProg.millerA_spec`: the breadth-first tree `T` with its levels
at `bLv`, the tree `T₁` of the inner region with its parent darts at `bPr`, the thin level `l₂` in
`r160` and the balanced dart `δ` off `T₁` in `r353`), the program `s9band` computes the data of
the separator of the band case of `PlanarSeparator.Map.bandSep` and the zone tests choosing the
case:

* `crSet`: the constants `r0 … r10` of the cycle search (`CycleSearch.CRegs`) from `k = r530`
  (the search of step 8 has overwritten them);
* `s9copy`: `δ` into `r500` (for `fcProg`) and `r547` (for `imLoop`), `l₂` into `r566`, and the
  registers `r161 = n`, `r215 = bPr`, `r255 = r₀` of `tmpass`;
* `fcProg`: the darts of the fundamental cycle of `δ` in `T₁` at `bFc`, their number in `r514`
  (`MillerProg.fcProg_fcycle`);
* `tmpass ; search`: the tree marks of `T₁` and the search of its dual tree (the state `SB`);
* `fsel ; imLoop`: the inside marks of `δ` at `bIm`, the flag in `r539`
  (`MillerProg.imLoop_inside`);
* `s9zt`: the zone tests of the faces of `δ` and `α δ` (`MillerProg.ztest_zone`), in `r580` and
  `r581`.

**`s9band_spec`**: within `113 k + 90 n + 145` steps, the darts at `bFc` are those of
`T₁.fcycle δ`, the marks at `bIm` differ from `r539` exactly on `T₁.inside δ`, and `r580`
(`r581`) is positive iff the face of `δ` (of `α δ`) avoids the levels `< l₂`; both positive is
the deep case of `bandSep`, otherwise `bandSep` is `(T₁.fcycle δ, T₁.inside δ)`
(`PlanarSeparator.Map.bandSep_of_band`).

Registers: the inputs `S9Regs` (above `500`, untouched by `millerA`), the layout `S9Lay` (the new
arrays above those of `millerA`: inside marks, cycle marks, a temporary array, the cycle).
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

/-! ### The programs -/

/-- **The constants of the cycle search** from `k = r530`. -/
def crSet : List Instr :=
  [.constN 0 0, .constN 1 1, .constN 2 2, .constN 3 3, .copyN 4 530, .addN 5 4 4, .addN 5 5 4,
    .addN 6 5 5, .addN 7 6 4, .addN 8 7 4, .addN 9 8 4, .addN 10 9 4]

/-- The dart `δ` and the level `l₂` for the passes, and the registers of `tmpass`. -/
def s9copy : List Instr :=
  [.copyN 500 353, .copyN 547 353, .copyN 566 160, .copyN 161 505, .copyN 215 503,
    .copyN 255 504]

/-- **The zone tests** of the faces of `y = r500` (into `r580`) and of `A y` (into `r581`). -/
def s9zt : Stmt :=
  .seq (.instr (.copyN 565 500)) <| .seq ztest <|
  .seq (block [.copyN 580 570, .loadN 565 500]) <| .seq ztest (.instr (.copyN 581 570))

/-- **Step 9, the band case**: the darts of the fundamental cycle of `δ` in `T₁`, its inside
marks, and the zone tests of the two faces of `δ`. -/
def s9band : Stmt :=
  .seq (block crSet) <| .seq (block s9copy) <| .seq fcProg <| .seq tmpass <| .seq search <|
  .seq (.seq fsel imLoop) s9zt

/-- The input registers of `s9band`. -/
structure S9Regs (k n bV bPr bLv bIm bMk bTmp bFc : ℕ) (c : Config) : Prop where
  r501 : c.nreg 501 = 0
  r502 : c.nreg 502 = bV
  r503 : c.nreg 503 = bPr
  r504 : c.nreg 504 = 0
  r505 : c.nreg 505 = n
  r506 : c.nreg 506 = bMk
  r507 : c.nreg 507 = 1
  r508 : c.nreg 508 = bFc
  r509 : c.nreg 509 = bTmp
  r510 : c.nreg 510 = 0
  r511 : c.nreg 511 = 1
  r530 : c.nreg 530 = k
  r531 : c.nreg 531 = bIm
  r533 : c.nreg 533 = 1
  r534 : c.nreg 534 = 0
  r535 : c.nreg 535 = 3
  r536 : c.nreg 536 = 9 * k
  r537 : c.nreg 537 = 8 * k
  r538 : c.nreg 538 = 0
  r567 : c.nreg 567 = bLv

/-- The layout of `s9band`: the arrays read (the vertices of the darts, the levels, the parent
darts) above the cycle search, then the inside marks, the cycle marks, the temporary array and
the darts of the cycle. -/
structure S9Lay (k n bV bPr bLv bIm bMk bTmp bFc W : ℕ) : Prop where
  l1 : 11 * k ≤ bV
  l2 : 11 * k ≤ bLv
  l3 : 11 * k ≤ bPr
  l4 : bV + 3 * k ≤ bIm
  l5 : bLv + n ≤ bIm
  l6 : bPr + n ≤ bIm
  l7 : bIm + k ≤ bMk
  l8 : bMk + n ≤ bTmp
  l9 : bTmp + n ≤ bFc
  l10 : bFc + 2 * n + 1 ≤ W
  l11 : 11 * k + 4 ≤ W

section proofs

variable {W : ℕ} {P : Input}

/-- `IR` survives programs keeping the registers `r530 … r547`. -/
theorem IR.of' {k bIm bA a : ℕ} {c c' : Config} (h : IR k bIm bA a c)
    (e : ∀ r, 530 ≤ r → r < 548 → c'.nreg r = c.nreg r) : IR k bIm bA a c' :=
  ⟨(e 530 (by omega) (by omega)).trans h.r530, (e 531 (by omega) (by omega)).trans h.r531,
    (e 533 (by omega) (by omega)).trans h.r533, (e 534 (by omega) (by omega)).trans h.r534,
    (e 535 (by omega) (by omega)).trans h.r535, (e 536 (by omega) (by omega)).trans h.r536,
    (e 537 (by omega) (by omega)).trans h.r537, (e 538 (by omega) (by omega)).trans h.r538,
    (e 547 (by omega) (by omega)).trans h.r547⟩

set_option maxHeartbeats 2000000 in
/-- **The constants of the cycle search.** -/
theorem crSet_exec {k : ℕ} (hW : 10 * k + 3 ≤ W) (c : Config) (hc : WordsBounded W c)
    (h530 : c.nreg 530 = k) :
    ∃ c' t, Exec P W (block crSet) c c' t ∧ t = 12 ∧ CRegs k c' ∧
      (∀ r, 11 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.output = c.output := by
  unfold crSet
  exec_block
  all_goals try (config_simp; (try simp only [h530]); omega)
  refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl⟩
  · unfold CRegs; config_simp; omega
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

set_option maxHeartbeats 2000000 in
/-- **The zone tests of the two faces of a dart.** -/
theorem s9zt_exec {k n δ' bA bV bPr r₀ bMk s bFc bTmp bIm a : ℕ} {V L A : ℕ → ℕ} {bLv l y : ℕ}
    (hW : bV + 3 * k ≤ W ∧ bLv + n ≤ W) (c : Config) (hc : WordsBounded W c)
    (hF : FR δ' bA bV bPr r₀ n bMk s bFc bTmp c) (hI : IR k bIm bA a c) (h500 : c.nreg 500 = y)
    (h566 : c.nreg 566 = l) (h567 : c.nreg 567 = bLv) (hy : y < 3 * k) (hAy : A y < 3 * k)
    (mAy : c.nmem y = A y)
    (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x ∧ V x < n)
    (mL : ∀ v < n, c.nmem (bLv + v) = L v) :
    ∃ c' t, Exec P W s9zt c c' t ∧ t ≤ 64 ∧ c'.nreg 580 = flagF l V L (y / 3) ∧
      c'.nreg 581 = flagF l V L (A y / 3) ∧
      (∀ r, r ≠ 565 → r ≠ 569 → r ≠ 570 → r ≠ 571 → r ≠ 572 → r ≠ 580 → r ≠ 581 →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.output = c.output := by
  -- `r565 := y`
  have e₁ := Exec.copyN (P := P) hc 565 500
  set c₁ : Config := { c with nreg := upd c.nreg 565 (c.nreg 500) }
  have k₁ : ∀ r, r ≠ 565 → c₁.nreg r = c.nreg r := fun r hr => upd_other _ _ _ hr
  have hw₁ := e₁.wb_right
  have hF₁ : FR δ' bA bV bPr r₀ n bMk s bFc bTmp c₁ := hF.of fun r h1 h2 => k₁ r (by omega)
  have hI₁ : IR k bIm bA a c₁ := IR.of' hI fun r h1 h2 => k₁ r (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, f₂, hr₂, hm₂, ho₂⟩ := ztest_exec (P := P) (V := V) (L := L) hW c₁ hw₁
    hF₁ hI₁ (by show upd c.nreg 565 (c.nreg 500) 565 = y; rw [upd_same, h500])
    ((k₁ 566 (by omega)).trans h566) ((k₁ 567 (by omega)).trans h567) hy mV mL
  have hw₂ := e₂.wb_right
  -- `r580 := r570`, `r565 := A y`
  obtain ⟨c₃, t₃, e₃, ht₃, q580, q565, hr₃, hm₃, ho₃⟩ : ∃ c₃ t₃,
      Exec P W (block [.copyN 580 570, .loadN 565 500]) c₂ c₃ t₃ ∧ t₃ = 2 ∧
      c₃.nreg 580 = c₂.nreg 570 ∧ c₃.nreg 565 = c₂.nmem (c₂.nreg 500) ∧
      (∀ r, r ≠ 565 → r ≠ 580 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧
      c₃.output = c₂.output := by
    exec_block
    refine ⟨rfl, by config_simp, by config_simp, fun r h1 h2 => ?_, rfl, rfl⟩
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₃ := e₃.wb_right
  have g500 : c₂.nreg 500 = y := by
    rw [hr₂ 500 (by omega) (by omega) (by omega) (by omega), k₁ 500 (by omega), h500]
  have hF₃ : FR δ' bA bV bPr r₀ n bMk s bFc bTmp c₃ := hF₁.of fun r h1 h2 => by
    rw [hr₃ r (by omega) (by omega), hr₂ r (by omega) (by omega) (by omega) (by omega)]
  have hI₃ : IR k bIm bA a c₃ := IR.of' hI₁ fun r h1 h2 => by
    rw [hr₃ r (by omega) (by omega), hr₂ r (by omega) (by omega) (by omega) (by omega)]
  have fm₃ : c₃.nmem = c.nmem := by rw [hm₃, hm₂]
  obtain ⟨c₄, t₄, e₄, ht₄, f₄, hr₄, hm₄, ho₄⟩ := ztest_exec (P := P) (V := V) (L := L) (l := l) (bLv := bLv) hW c₃ hw₃
    hF₃ hI₃ (by rw [q565, g500, hm₂]; exact mAy)
    (by rw [hr₃ 566 (by omega) (by omega), hr₂ 566 (by omega) (by omega) (by omega) (by omega)]
        exact (k₁ 566 (by omega)).trans h566)
    (by rw [hr₃ 567 (by omega) (by omega), hr₂ 567 (by omega) (by omega) (by omega) (by omega)]
        exact (k₁ 567 (by omega)).trans h567) hAy (by rw [fm₃]; exact mV)
    (by rw [fm₃]; exact mL)
  have hw₄ := e₄.wb_right
  have e₅ := Exec.copyN (P := P) hw₄ 581 570
  set c₅ : Config := { c₄ with nreg := upd c₄.nreg 581 (c₄.nreg 570) }
  have k₅ : ∀ r, r ≠ 581 → c₅.nreg r = c₄.nreg r := fun r hr => upd_other _ _ _ hr
  refine ⟨c₅, 1 + (t₂ + (t₃ + (t₄ + 1))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega,
    ?_, ?_, fun r a1 a2 a3 a4 a5 a6 a7 => ?_, by rw [show c₅.nmem = c₄.nmem from rfl, hm₄, fm₃],
    by rw [show c₅.output = c₄.output from rfl, ho₄, ho₃, ho₂]⟩
  · rw [k₅ 580 (by omega), hr₄ 580 (by omega) (by omega) (by omega) (by omega), q580, f₂]
  · show upd c₄.nreg 581 (c₄.nreg 570) 581 = _
    rw [upd_same, f₄]
  · rw [k₅ r a7, hr₄ r a2 a3 a4 a5, hr₃ r a1 a6, hr₂ r a2 a3 a4 a5, k₁ r a1]

end proofs

/-! ### The band case through the coding -/

section Band

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

set_option maxHeartbeats 8000000 in
/-- **Step 9 on the machine, the band case.** From the coded triangulation (reversals at `0`,
vertices at `bV`), the levels of a tree `T` at `bLv`, the parent darts of a spanning tree `T₁` at
`bPr` (root `0`), a level `l₂` in `r160`, a dart `δ` off `T₁` in `r353` and clear marks at `bMk`,
the program `s9band` writes within `113 k + 90 n + 145` steps the darts of the fundamental cycle
of `δ` in `T₁` at `bFc` (their number in `r514`), marks at `bIm` differing from `r539` exactly on
the faces inside `δ`, and in `r580`, `r581` flags positive iff the face of `δ`, of `α δ`, avoids
the levels `< l₂`. -/
theorem s9band_spec {T T₁ : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n}
    {A V : ℕ → ℕ} {W : ℕ} {P : Input} {c : Config} {bV bPr bLv bIm bMk bTmp bFc l₂ : ℕ} {δ : D}
    (hM : M.IsPlane) (hk : 0 < k)
    (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hφ : ∀ x, (cd (M.φ x) : ℕ) = phi3 (cd x))
    (hV : ∀ x, V (cd x) = vi (M.vert x)) (hr : (vi T₁.root : ℕ) = 0)
    (hlay : S9Lay k n bV bPr bLv bIm bMk bTmp bFc W) (hc : WordsBounded W c)
    (hR : S9Regs k n bV bPr bLv bIm bMk bTmp bFc c) (h353 : c.nreg 353 = cd δ)
    (h160 : c.nreg 160 = l₂) (hδ : ¬ T₁.IsTree δ)
    (mA : ∀ x < 3 * k, c.nmem x = A x) (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x)
    (mL : ∀ v, c.nmem (bLv + vi v) = T.height v)
    (hPr : ∀ v (h : v ≠ T₁.root), c.nmem (bPr + vi v) = cd (T₁.par v h))
    (hMk : ∀ v < n, c.nmem (bMk + v) = 0) :
    ∃ c' t, Exec P W s9band c c' t ∧ t ≤ 113 * k + 90 * n + 145 ∧
      c'.nreg 514 = (T₁.fcycle δ).k ∧
      (∀ i < (T₁.fcycle δ).k, c'.nmem (bFc + i) = cd ((T₁.fcycle δ).d i)) ∧
      (∀ G : M.Face, c'.nmem (bIm + fi cd G) ≠ c'.nreg 539 ↔ G ∈ T₁.inside δ) ∧
      (0 < c'.nreg 580 ↔ M.face δ ∉ M.zone (T.low l₂)) ∧
      (0 < c'.nreg 581 ↔ M.face (M.α δ) ∉ M.zone (T.low l₂)) ∧
      (∀ x < 3 * k, c'.nmem x = A x) ∧
      (∀ a, 11 * k ≤ a → (a < bIm ∨ bFc + 2 * n + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, 590 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nreg 500 = cd δ ∧ c'.nreg 566 = l₂ ∧
      c'.output = c.output := by
  classical
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hlay
  set Pr : ℕ → ℕ := fun u => c.nmem (bPr + u) with hPrd
  have hPr' : ∀ v (h : v ≠ T₁.root), Pr (vi v) = cd (T₁.par v h) := hPr
  have hin := rootIn_tree cd vi T₁ hAcd hV hPr'
  set L : ℕ → ℕ := fun u => c.nmem (bLv + u) with hLd
  -- 0. the constants
  obtain ⟨c₁, t₁, e₁, ht₁, hCR₁, hr₁, hm₁, ho₁⟩ := crSet_exec (P := P) (by omega) c hc hR.r530
  have hw₁ := e₁.wb_right
  -- 1. the copies
  obtain ⟨c₂, t₂, e₂, ht₂, q500, q547, q566, q161, q215, q255, hr₂, hm₂, ho₂⟩ : ∃ c₂ t₂,
      Exec P W (block s9copy) c₁ c₂ t₂ ∧ t₂ = 6 ∧ c₂.nreg 500 = c₁.nreg 353 ∧
      c₂.nreg 547 = c₁.nreg 353 ∧ c₂.nreg 566 = c₁.nreg 160 ∧ c₂.nreg 161 = c₁.nreg 505 ∧
      c₂.nreg 215 = c₁.nreg 503 ∧ c₂.nreg 255 = c₁.nreg 504 ∧
      (∀ r, r ≠ 500 → r ≠ 547 → r ≠ 566 → r ≠ 161 → r ≠ 215 → r ≠ 255 →
        c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧ c₂.output = c₁.output := by
    unfold s9copy
    exec_block
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
      by config_simp, fun r a1 a2 a3 a4 a5 a6 => ?_, rfl, rfl⟩
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₂ := e₂.wb_right
  have G : ∀ r, 400 ≤ r → r ≠ 500 → r ≠ 547 → r ≠ 566 → c₂.nreg r = c.nreg r :=
    fun r a b d e => by rw [hr₂ r b d e (by omega) (by omega) (by omega), hr₁ r (by omega)]
  have p353 : c₁.nreg 353 = cd δ := (hr₁ 353 (by omega)).trans h353
  have fm₂ : c₂.nmem = c.nmem := by rw [hm₂, hm₁]
  -- 2. the darts of the cycle
  have hF₂ : FR (cd δ) 0 bV bPr (vi T₁.root) n bMk 1 bFc bTmp c₂ :=
    ⟨q500.trans p353, (G 501 (by omega) (by omega) (by omega) (by omega)).trans hR.r501,
      (G 502 (by omega) (by omega) (by omega) (by omega)).trans hR.r502,
      (G 503 (by omega) (by omega) (by omega) (by omega)).trans hR.r503,
      (G 504 (by omega) (by omega) (by omega) (by omega)).trans (hR.r504.trans hr.symm),
      (G 505 (by omega) (by omega) (by omega) (by omega)).trans hR.r505,
      (G 506 (by omega) (by omega) (by omega) (by omega)).trans hR.r506,
      (G 507 (by omega) (by omega) (by omega) (by omega)).trans hR.r507,
      (G 508 (by omega) (by omega) (by omega) (by omega)).trans hR.r508,
      (G 509 (by omega) (by omega) (by omega) (by omega)).trans hR.r509,
      (G 510 (by omega) (by omega) (by omega) (by omega)).trans hR.r510,
      (G 511 (by omega) (by omega) (by omega) (by omega)).trans hR.r511⟩
  obtain ⟨c₃, t₃, e₃, ht₃, h514, hd₃, hm₃, hr₃, ho₃⟩ := fcProg_fcycle cd vi (A := A) (V := V)
    (Pr := Pr) hAcd hV hPr' δ (W := W) (bA := 0) (bV := bV) (bPr := bPr) (bMk := bMk) (s := 1)
    (bFc := bFc) (bTmp := bTmp) (P := P)
    ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ c₂ hw₂ hF₂
    (fun x hx => by rw [zero_add, fm₂]; exact mA x hx) (fun x hx => by rw [fm₂]; exact mV x hx)
    (fun v hv _ => by rw [fm₂]) (fun v hv => by rw [fm₂, hMk v hv]; omega)
  have hw₃ := e₃.wb_right
  have fm₃ : ∀ a, a < bMk → c₃.nmem a = c.nmem a := fun a ha => by rw [hm₃ a (Or.inl ha), fm₂]
  -- 3. the tree marks and the search
  have hTF : TFix k n (vi T₁.root) bPr W A Pr c₃ :=
    ⟨cregs_of hCR₁ fun r hr' => by
        rw [hr₃ r (Or.inl (by omega)),
          hr₂ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)],
      by rw [hr₃ 161 (Or.inl (by omega)), q161, hr₁ 505 (by omega), hR.r505],
      by rw [hr₃ 215 (Or.inl (by omega)), q215, hr₁ 503 (by omega), hR.r503],
      by rw [hr₃ 255 (Or.inl (by omega)), q255, hr₁ 504 (by omega), hR.r504, hr],
      fun x hx => by rw [fm₃ x (by omega)]; exact mA x hx, hin.A_lt,
      fun v hv _ => fm₃ _ (by omega), hin.Pr_lt, by omega, by omega, by omega⟩
  obtain ⟨c₄, t₄, e₄, ht₄, hT₄, hz₄, hm₄, hr₄, ho₄⟩ := tmpass_exec (P := P) hTF hw₃
  have hC := coded_of_tmark (k := k) (cd := cd) (vi := vi) (A := A) (Pr := Pr) hAcd hφ hPr'
  set Tm := tmark A Pr (vi T₁.root) n
  have hw₄ := e₄.wb_right
  have mm₄ : ∀ a, a < 3 * k ∨ 8 * k ≤ a → c₄.nmem a = c₃.nmem a := fun a ha =>
    hm₄ a (by unfold TOut; omega)
  have hH₄ : Holds k A Tm (fun f => c₄.nmem (6 * k + f)) c₄.nmem :=
    ⟨fun x hx => by rw [mm₄ x (by omega), fm₃ x (by omega)]; exact mA x hx,
      fun x hx => hT₄ x hx, fun _ _ => rfl⟩
  obtain ⟨c₅, t₅, e₅, hI₅, hend₅, ht₅, hm₅⟩ := search_exec (P := P) (o := c₄.output) hC.tri
    (by omega) hk c₄ hw₄ (cregs_of hTF.regs fun r hr' => hr₄ r (by omega) (by omega) (by omega)
      (by omega)) hH₄ rfl hz₄
  have hall₅ := hC.search_all hM hk hI₅ hend₅
  have hw₅ := e₅.wb_right
  have fr₅ : ∀ r, 25 ≤ r → c₅.nreg r = c₄.nreg r := fun r hr' =>
    e₅.nreg_of_wr (Stmt.wr_of_wmax (by have hs : search.wmax < 25 := (by decide); omega))
  have K₅ : ∀ r, 400 ≤ r → (r < 512 ∨ 521 ≤ r) → c₅.nreg r = c₂.nreg r := fun r a b => by
    rw [fr₅ r (by omega), hr₄ r (by omega) (by omega) (by omega) (by omega), hr₃ r b]
  -- 4. the inside marks
  have hI₅' : IR k bIm 0 (cd δ) c₅ :=
    ⟨by rw [K₅ 530 (by omega) (by omega), G 530 (by omega) (by omega) (by omega) (by omega)]
        exact hR.r530,
      by rw [K₅ 531 (by omega) (by omega), G 531 (by omega) (by omega) (by omega) (by omega)]
         exact hR.r531,
      by rw [K₅ 533 (by omega) (by omega), G 533 (by omega) (by omega) (by omega) (by omega)]
         exact hR.r533,
      by rw [K₅ 534 (by omega) (by omega), G 534 (by omega) (by omega) (by omega) (by omega)]
         exact hR.r534,
      by rw [K₅ 535 (by omega) (by omega), G 535 (by omega) (by omega) (by omega) (by omega)]
         exact hR.r535,
      by rw [K₅ 536 (by omega) (by omega), G 536 (by omega) (by omega) (by omega) (by omega)]
         exact hR.r536,
      by rw [K₅ 537 (by omega) (by omega), G 537 (by omega) (by omega) (by omega) (by omega)]
         exact hR.r537,
      by rw [K₅ 538 (by omega) (by omega), G 538 (by omega) (by omega) (by omega) (by omega)]
         exact hR.r538,
      by rw [K₅ 547 (by omega) (by omega), q547, p353]⟩
  obtain ⟨c₆, t₆, e₆, ht₆, him₆, hm₆, hr₆, ho₆⟩ := imLoop_inside (P := P) hC hM hk hI₅.toSB
    hall₅ δ ((hC.T_cd δ).2 hδ) (bIm := bIm) (bA := 0) ⟨by omega, by omega⟩ (by omega) hI₅'
    (fun x hx => by rw [zero_add]; exact hI₅.hold.1 x hx)
  have hw₆ := e₆.wb_right
  have MF : ∀ a, 11 * k ≤ a → a < bIm → c₆.nmem a = c.nmem a := fun a h1 h2 => by
    rw [hm₆ a (by omega), hm₅ a h1, mm₄ a (by omega), fm₃ a (by omega)]
  -- 5. the zone tests
  have K₆ : ∀ r, 400 ≤ r → r < 512 → c₆.nreg r = c₂.nreg r := fun r a b => by
    rw [hr₆ r (by omega) (by omega) (Or.inl (by omega)), K₅ r a (Or.inl b)]
  have hF₆ : FR (cd δ) 0 bV bPr (vi T₁.root) n bMk 1 bFc bTmp c₆ :=
    hF₂.of fun r h1 h2 => K₆ r (by omega) h2
  have hI₆ : IR k bIm 0 (c₆.nreg 547) c₆ :=
    ⟨by rw [hr₆ 530 (by omega) (by omega) (Or.inl (by omega))]; exact hI₅'.r530,
      by rw [hr₆ 531 (by omega) (by omega) (Or.inl (by omega))]; exact hI₅'.r531,
      by rw [hr₆ 533 (by omega) (by omega) (Or.inl (by omega))]; exact hI₅'.r533,
      by rw [hr₆ 534 (by omega) (by omega) (Or.inl (by omega))]; exact hI₅'.r534,
      by rw [hr₆ 535 (by omega) (by omega) (Or.inl (by omega))]; exact hI₅'.r535,
      by rw [hr₆ 536 (by omega) (by omega) (Or.inl (by omega))]; exact hI₅'.r536,
      by rw [hr₆ 537 (by omega) (by omega) (Or.inl (by omega))]; exact hI₅'.r537,
      by rw [hr₆ 538 (by omega) (by omega) (Or.inl (by omega))]; exact hI₅'.r538, rfl⟩
  have h566 : c₆.nreg 566 = l₂ := by
    rw [hr₆ 566 (by omega) (by omega) (Or.inr (by omega)), K₅ 566 (by omega) (Or.inr (by omega)),
      q566, hr₁ 160 (by omega), h160]
  have h567 : c₆.nreg 567 = bLv := by
    rw [hr₆ 567 (by omega) (by omega) (Or.inr (by omega)), K₅ 567 (by omega) (Or.inr (by omega)),
      G 567 (by omega) (by omega) (by omega) (by omega)]
    exact hR.r567
  obtain ⟨c₇, t₇, e₇, ht₇, f580, f581, hr₇, hm₇, ho₇⟩ := s9zt_exec (P := P) (V := V) (L := L)
    (A := A) (l := l₂) (bLv := bLv) ⟨by omega, by omega⟩ c₆ hw₆ hF₆ hI₆ hF₆.r500 h566 h567
    (cd δ).2 (hin.A_lt _ (cd δ).2)
    (by rw [hm₆ _ (by omega)]; exact hI₅.hold.1 _ (cd δ).2)
    (fun x hx => ⟨by rw [MF _ (by omega) (by omega)]; exact mV x hx, hin.V_lt x hx⟩)
    (fun v hv => MF _ (by omega) (by omega))
  have hL : ∀ v, L (vi v) = T.height v := mL
  have e₀ : Exec P W s9band c c₇ (t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + t₇)))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇)))))
  refine ⟨c₇, _, e₀, by omega, ?_, fun i hi => ?_, fun G' => ?_, ?_, ?_, fun x hx => ?_,
    fun a h1 h2 => ?_, fun r hr' => ?_, ?_, ?_, ?_⟩
  · rw [hr₇ 514 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      hr₆ 514 (by omega) (by omega) (Or.inl (by omega)), fr₅ 514 (by omega),
      hr₄ 514 (by omega) (by omega) (by omega) (by omega), h514]
  · rw [hm₇, hm₆ _ (by omega), hm₅ _ (by omega), mm₄ _ (by omega)]
    exact hd₃ i hi
  · rw [hm₇, hr₇ 539 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]
    exact him₆ G'
  · rw [f580]; exact ztest_zone hC vi hV hL l₂ δ
  · rw [f581, hAcd]; exact ztest_zone hC vi hV hL l₂ (M.α δ)
  · rw [hm₇, hm₆ x (by omega)]; exact hI₅.hold.1 x hx
  · rw [hm₇, hm₆ a (by omega), hm₅ a h1, mm₄ a (by omega), hm₃ a (by omega), fm₂]
  · exact e₀.nreg_of_wr (Stmt.wr_of_wmax (by have hs : s9band.wmax < 590 := (by decide); omega))
  · rw [hr₇ 500 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hF₆.r500
  · rw [hr₇ 566 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact h566
  · rw [ho₇, ho₆, show c₅.output = c₄.output from hI₅.out, ho₄, ho₃, ho₂, ho₁]

end Band

/-! ### The deep case: the ancestors at level `l₂` of the ends of `δ` -/

/-- **The ancestors at level `≤ l = r566` of the ends of the dart `y = r500`** (the test
`topA T T₁ l₂ (vert δ) = topA T T₁ l₂ (vert (α δ))` of `PlanarSeparator.Map.deepSep`), by two runs
of `taPass`: into `r584` and `r585`. -/
def s9top : Stmt :=
  .seq (block [.copyN 444 566, .addN 586 434 500, .loadN 446 586]) <| .seq taPass <|
  .seq (block [.copyN 584 471, .loadN 586 500, .addN 586 434 586, .loadN 446 586]) <|
  .seq taPass (.instr (.copyN 585 471))

section Top

variable {W : ℕ} {P : Input}

set_option maxHeartbeats 4000000 in
/-- **The two ancestors on the machine**: `r584` and `r585` are the ends of `n` guarded parent
steps from the vertices `V y` and `V (A y)`, within `24 n + 18` steps. -/
theorem s9top_exec {k n bV bL h bNx bCy bPos bLv bPr l' x₀ u l y : ℕ} {A V L Pr : ℕ → ℕ}
    (hW : bLv + n ≤ W ∧ bPr + n ≤ W ∧ 3 * k ≤ W ∧ bV + 3 * k ≤ W) (c : Config)
    (hc : WordsBounded W c) (hB : BR 0 bV bL k h bNx bCy bPos n bLv bPr l' x₀ u c)
    (h500 : c.nreg 500 = y) (h566 : c.nreg 566 = l) (hy : y < 3 * k)
    (hL : ∀ v < n, c.nmem (bLv + v) = L v)
    (hPr : ∀ v < n, l < L v → c.nmem (bPr + v) = Pr v ∧ Pr v < 3 * k)
    (hA : ∀ x < 3 * k, c.nmem x = A x ∧ A x < 3 * k)
    (hV : ∀ x < 3 * k, c.nmem (bV + x) = V x ∧ V x < n) :
    ∃ c' t, Exec P W s9top c c' t ∧ t ≤ 24 * n + 18 ∧
      c'.nreg 584 = (taNext L Pr A V l)^[n] (V y) ∧
      c'.nreg 585 = (taNext L Pr A V l)^[n] (V (A y)) ∧ c'.nmem = c.nmem ∧
      (∀ r, r ≠ 444 → r ≠ 446 → (r < 470 ∨ 474 ≤ r) → r ≠ 584 → r ≠ 585 → r ≠ 586 →
        c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  have hA' : ∀ x < 3 * k, c.nmem (0 + x) = A x ∧ A x < 3 * k := fun x hx => by
    rw [zero_add]; exact hA x hx
  have m₀y := (hV y hy).1
  -- 1. `l`, and the vertex of `y`
  obtain ⟨c₁, t₁, e₁, ht₁, q444, q446, hr₁, hm₁, ho₁⟩ : ∃ c₁ t₁,
      Exec P W (block [.copyN 444 566, .addN 586 434 500, .loadN 446 586]) c c₁ t₁ ∧ t₁ = 3 ∧
      c₁.nreg 444 = l ∧ c₁.nreg 446 = V y ∧
      (∀ r, r ≠ 444 → r ≠ 446 → r ≠ 586 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.output = c.output := by
    have hb := hc.1 434
    rw [hB.r334] at hb
    exec_block
    · config_simp; rw [hB.r334, h500]; omega
    refine ⟨rfl, by config_simp; exact h566, ?_, fun r a1 a2 a3 => ?_, rfl, rfl⟩
    · config_simp; rw [hB.r334, h500]; exact m₀y
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have hB₁ : BR 0 bV bL k h bNx bCy bPos n bLv bPr l x₀ (V y) c₁ :=
    ⟨(hr₁ 430 (by omega) (by omega) (by omega)).trans hB.r330,
      (hr₁ 431 (by omega) (by omega) (by omega)).trans hB.r331,
      (hr₁ 432 (by omega) (by omega) (by omega)).trans hB.r332,
      (hr₁ 433 (by omega) (by omega) (by omega)).trans hB.r333,
      (hr₁ 434 (by omega) (by omega) (by omega)).trans hB.r334,
      (hr₁ 435 (by omega) (by omega) (by omega)).trans hB.r335,
      (hr₁ 436 (by omega) (by omega) (by omega)).trans hB.r336,
      (hr₁ 437 (by omega) (by omega) (by omega)).trans hB.r337,
      (hr₁ 438 (by omega) (by omega) (by omega)).trans hB.r338,
      (hr₁ 439 (by omega) (by omega) (by omega)).trans hB.r339,
      (hr₁ 440 (by omega) (by omega) (by omega)).trans hB.r340,
      (hr₁ 441 (by omega) (by omega) (by omega)).trans hB.r341,
      (hr₁ 442 (by omega) (by omega) (by omega)).trans hB.r342,
      (hr₁ 443 (by omega) (by omega) (by omega)).trans hB.r343, q444,
      (hr₁ 445 (by omega) (by omega) (by omega)).trans hB.r345, q446⟩
  obtain ⟨c₂, t₂, e₂, ht₂, f₂, hm₂, hr₂, ho₂⟩ := taPass_exec (P := P) (A := A) (V := V) (L := L)
    (Pr := Pr) ⟨hW.1, hW.2.1, by omega, hW.2.2.2⟩ c₁ hw₁ hB₁ (hV y hy).2 (by rw [hm₁]; exact hL) (by rw [hm₁]; exact hPr)
    (by rw [hm₁]; exact hA') (by rw [hm₁]; exact hV)
  have hw₂ := e₂.wb_right
  have fm₂ : c₂.nmem = c.nmem := by rw [hm₂, hm₁]
  -- 2. the vertex of `A y`
  have hAy := hA y hy
  obtain ⟨c₃, t₃, e₃, ht₃, q584, q446', hr₃, hm₃, ho₃⟩ : ∃ c₃ t₃,
      Exec P W (block [.copyN 584 471, .loadN 586 500, .addN 586 434 586, .loadN 446 586]) c₂ c₃
        t₃ ∧ t₃ = 4 ∧ c₃.nreg 584 = c₂.nreg 471 ∧ c₃.nreg 446 = V (A y) ∧
      (∀ r, r ≠ 446 → r ≠ 584 → r ≠ 586 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧
      c₃.output = c₂.output := by
    have g434 : c₂.nreg 434 = bV := by
      rw [hr₂ 434 (Or.inl (by omega)), hr₁ 434 (by omega) (by omega) (by omega)]; exact hB.r334
    have g500 : c₂.nreg 500 = y := by
      rw [hr₂ 500 (Or.inr (by omega)), hr₁ 500 (by omega) (by omega) (by omega)]; exact h500
    have hb := hc.1 434
    rw [hB.r334] at hb
    exec_block
    · config_simp; rw [g434, g500, fm₂, hAy.1]; omega
    refine ⟨rfl, by config_simp, ?_, fun r a1 a2 a3 => ?_, rfl, rfl⟩
    · config_simp; rw [g434, g500, fm₂, hAy.1]; exact (hV _ hAy.2).1
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₃ := e₃.wb_right
  have F₃ : ∀ r, 430 ≤ r → r < 446 → c₃.nreg r = c₁.nreg r := fun r a b => by
    rw [hr₃ r (by omega) (by omega) (by omega), hr₂ r (Or.inl (by omega))]
  have hB₃ : BR 0 bV bL k h bNx bCy bPos n bLv bPr l x₀ (V (A y)) c₃ :=
    ⟨(F₃ 430 (by omega) (by omega)).trans hB₁.r330, (F₃ 431 (by omega) (by omega)).trans hB₁.r331,
      (F₃ 432 (by omega) (by omega)).trans hB₁.r332, (F₃ 433 (by omega) (by omega)).trans hB₁.r333,
      (F₃ 434 (by omega) (by omega)).trans hB₁.r334, (F₃ 435 (by omega) (by omega)).trans hB₁.r335,
      (F₃ 436 (by omega) (by omega)).trans hB₁.r336, (F₃ 437 (by omega) (by omega)).trans hB₁.r337,
      (F₃ 438 (by omega) (by omega)).trans hB₁.r338, (F₃ 439 (by omega) (by omega)).trans hB₁.r339,
      (F₃ 440 (by omega) (by omega)).trans hB₁.r340, (F₃ 441 (by omega) (by omega)).trans hB₁.r341,
      (F₃ 442 (by omega) (by omega)).trans hB₁.r342, (F₃ 443 (by omega) (by omega)).trans hB₁.r343,
      (F₃ 444 (by omega) (by omega)).trans hB₁.r344, (F₃ 445 (by omega) (by omega)).trans hB₁.r345,
      q446'⟩
  have fm₃ : c₃.nmem = c.nmem := by rw [hm₃, fm₂]
  obtain ⟨c₄, t₄, e₄, ht₄, f₄, hm₄, hr₄, ho₄⟩ := taPass_exec (P := P) (A := A) (V := V) (L := L)
    (Pr := Pr) ⟨hW.1, hW.2.1, by omega, hW.2.2.2⟩ c₃ hw₃ hB₃ (hV _ hAy.2).2
    (by rw [fm₃]; exact hL) (by rw [fm₃]; exact hPr) (by rw [fm₃]; exact hA') (by rw [fm₃]; exact hV)
  have hw₄ := e₄.wb_right
  have e₅ := Exec.copyN (P := P) hw₄ 585 471
  set c₅ : Config := { c₄ with nreg := upd c₄.nreg 585 (c₄.nreg 471) }
  have k₅ : ∀ r, r ≠ 585 → c₅.nreg r = c₄.nreg r := fun r hr => upd_other _ _ _ hr
  refine ⟨c₅, t₁ + (t₂ + (t₃ + (t₄ + 1))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega,
    ?_, ?_, by rw [show c₅.nmem = c₄.nmem from rfl, hm₄, fm₃], fun r a1 a2 a3 a4 a5 a6 => ?_,
    by rw [show c₅.output = c₄.output from rfl, ho₄, ho₃, ho₂, ho₁]⟩
  · rw [k₅ 584 (by omega), hr₄ 584 (Or.inr (by omega)), q584, f₂]
  · show upd c₄.nreg 585 (c₄.nreg 471) 585 = _
    rw [upd_same, f₄]
  · rw [k₅ r a5, hr₄ r a3, hr₃ r a2 a4 a6, hr₂ r a3, hr₁ r a1 a2 a6]

/-- **The ancestors through the coding**: if `bLv` holds the levels of `T` and `bPr` the parent
darts of `T₁`, whose root has level `≤ l`, the two results of `s9top` from `y = cd δ` are
`vi (topA T T₁ l (vert δ))` and `vi (topA T T₁ l (vert (α δ)))`; in particular they agree iff
the ancestors do (`PlanarSeparator.Map.deepSep`). -/
theorem s9top_topA {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]
    {M : Map D Q} {T T₁ : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n}
    {A V : ℕ → ℕ} {bV bL h bNx bCy bPos bLv bPr l' x₀ u l : ℕ} {δ : D}
    (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hV : ∀ x, V (cd x) = vi (M.vert x))
    (hW : bLv + n ≤ W ∧ bPr + n ≤ W ∧ 3 * k ≤ W ∧ bV + 3 * k ≤ W) (c : Config)
    (hc : WordsBounded W c) (hB : BR 0 bV bL k h bNx bCy bPos n bLv bPr l' x₀ u c)
    (h500 : c.nreg 500 = cd δ) (h566 : c.nreg 566 = l) (hl : T.height T₁.root ≤ l)
    (mL : ∀ v, c.nmem (bLv + vi v) = T.height v)
    (hPr : ∀ v (h : v ≠ T₁.root), c.nmem (bPr + vi v) = cd (T₁.par v h))
    (mA : ∀ x < 3 * k, c.nmem x = A x) (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x) :
    ∃ c' t, Exec P W s9top c c' t ∧ t ≤ 24 * n + 18 ∧
      c'.nreg 584 = vi (topA T T₁ l (M.vert δ)) ∧
      c'.nreg 585 = vi (topA T T₁ l (M.vert (M.α δ))) ∧
      (c'.nreg 584 = c'.nreg 585 ↔ topA T T₁ l (M.vert δ) = topA T T₁ l (M.vert (M.α δ))) ∧
      c'.nmem = c.nmem ∧
      (∀ r, r ≠ 444 → r ≠ 446 → (r < 470 ∨ 474 ≤ r) → r ≠ 584 → r ≠ 585 → r ≠ 586 →
        c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  classical
  set L : ℕ → ℕ := fun v => c.nmem (bLv + v)
  set Pr : ℕ → ℕ := fun v => c.nmem (bPr + v)
  have hPr' : ∀ v (hv : v ≠ T₁.root), Pr (vi v) = cd (T₁.par v hv) := hPr
  have hin := rootIn_tree cd vi T₁ hAcd hV hPr'
  have hlt : ∀ v < n, l < L v → c.nmem (bPr + v) = Pr v ∧ Pr v < 3 * k := fun v hv hlv => by
    refine ⟨rfl, hin.Pr_lt v hv fun e => ?_⟩
    have : L v = T.height T₁.root := by rw [e]; exact mL _
    omega
  obtain ⟨c', t, e, ht, f1, f2, hm, hr, ho⟩ := s9top_exec (P := P) (A := A) (V := V) (L := L)
    (Pr := Pr) (l := l) hW c hc hB h500 h566 (cd δ).2 (fun v _ => rfl) hlt
    (fun x hx => ⟨mA x hx, hin.A_lt x hx⟩) (fun x hx => ⟨mV x hx, hin.V_lt x hx⟩)
  have g1 : c'.nreg 584 = vi (topA T T₁ l (M.vert δ)) := by
    rw [f1, hV]; exact taNext_topA cd vi hAcd hV mL hPr' hl _
  have g2 : c'.nreg 585 = vi (topA T T₁ l (M.vert (M.α δ))) := by
    rw [f2, hAcd, hV]; exact taNext_topA cd vi hAcd hV mL hPr' hl _
  refine ⟨c', t, e, ht, g1, g2, ?_, hm, hr, ho⟩
  rw [g1, g2, Fin.val_inj, vi.apply_eq_iff_eq]

end Top

end MillerProg

end PlanarSeparator
