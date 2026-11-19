module

public import PlanarSeparator.Machine.MillerInC

/-!
# Miller's separator on the machine: the walk to a balanced fundamental cycle

Part of step 8 of the plan in `PlanarSeparator/Machine/Miller.lean`. With the weights `J F` of
the strict insides of the darts `pd F` stored at `10 k + F` (`PlanarSeparator/Machine/MillerInC.lean`),
the weight of the strict inside of every dart `y` off the tree is `IvM y`:

* `J (y / 3)` if `y` is the dart `pd` of its face;
* otherwise `A y` is the dart `pd` of its face, the strict inside of `y` is the strict outside of
  `A y`, and its weight is `tot - J (A y / 3) - cwN (A y)`, where `cwN d` is the weight of the
  fundamental cycle of `d` from the root sums and one lowest-common-ancestor query
  (`PlanarSeparator.Map.SpTree.sum_cycV`).

The walk (`mwalk`) follows `PlanarSeparator.Map.SpTree.exists_simple_balanced_of_lt`: it starts from
the dart `δ₀ = pd` of the second face found; if neither side of `δ₀` is heavier than `2/3` of the
total, `δ₀` is the answer; otherwise it starts from the heavier side and moves from `δ` to the
heavier of `a₁ = A (φ δ)`, `a₂ = A (φ² δ)` (a dart off the tree) as long as that is heavier than
`2/3`, and answers the first one that is not. The answer `d` (in `r353`) is a dart off the tree
with `3 IvM d ≤ 2 tot` and `3 IvM (A d) ≤ 2 tot` (`mwalk_exec`, numeric, within
`(50 L + 160) (k + 1) + 50 L + 142` steps, from the recurrence of the strict insides and the
complement rule `MWH`). For a coded plane triangulation (`PlanarSeparator/Machine/MillerStep8.lean`:
`mwh_tree`, and with the pass of the strict insides and the total weight, **`step8_tree`**) the
answer is a dart `δ` off the tree with
`3 W (inC δ) ≤ 2 W` and `3 W (outC δ) ≤ 2 W`: the conclusion of
`PlanarSeparator.Map.SpTree.exists_simple_balanced`.

Registers: those of the search (`r0 … r10`), of `lcaq`, `r162 = bV`, `r250 = bW`, `r252 = bS`,
`r320 = tot`; the helpers write `r330 … r346`, the walk `r321` and `r350 … r364`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset CycleSearch

/-! ### The numbers -/

/-- The data of the walk: the coded map (`A`, the tree marks `Tm`), the search (`pdf`), the
stored weights `J`, the vertices `V` of the darts, the root sums `R`, the weights `w`, the lowest
common ancestors `Lc`, and the total `tot`. -/
structure WD where
  k : ℕ
  A : ℕ → ℕ
  Tm : ℕ → ℕ
  pdf : ℕ → ℕ
  J : ℕ → ℕ
  V : ℕ → ℕ
  R : ℕ → ℕ
  w : ℕ → ℕ
  Lc : ℕ → ℕ → ℕ
  tot : ℕ

/-- The weight of the fundamental cycle of the dart `y`: `R x + R z - 2 R l + w l`. -/
def cwN (d : WD) (y : ℕ) : ℕ :=
  (d.R (d.V y) - d.R (d.Lc (d.V y) (d.V (d.A y)))) +
    (d.R (d.V (d.A y)) - d.R (d.Lc (d.V y) (d.V (d.A y)))) + d.w (d.Lc (d.V y) (d.V (d.A y)))

/-- The weight of the strict inside of a dart off the tree. -/
def IvM (d : WD) (y : ℕ) : ℕ :=
  if y / 3 ≠ 0 ∧ d.pdf (y / 3) = y then d.J (y / 3) else d.tot - d.J (d.A y / 3) - cwN d (d.A y)

/-- The weight of the strict inside of any dart (`0` for a tree dart). -/
def cvM (d : WD) (z : ℕ) : ℕ := if d.Tm z = 0 then IvM d z else 0

/-! ### The programs -/

/-- `r331 := J (r330 / 3)`. -/
def ivS : Stmt := block [.addN 334 10 332, .loadN 331 334]

/-- `r331 := tot - J (A y / 3) - cwN (A y)` for `y = r330`. -/
def ivO : Stmt :=
  .seq (block [.loadN 334 330, .divN 335 334 3, .addN 336 10 335, .loadN 336 336,
      .addN 337 162 334, .loadN 337 337, .addN 338 162 330, .loadN 338 338])
    (.seq (qcall 337 338 339)
      (block [.addN 340 252 337, .loadN 340 340, .addN 341 252 339, .loadN 341 341,
        .subN 342 340 341, .addN 340 252 338, .loadN 340 340, .subN 343 340 341,
        .addN 342 342 343, .addN 340 250 339, .loadN 340 340, .addN 342 342 340,
        .subN 331 320 336, .subN 331 331 342]))

/-- **`r331 := IvM r330`** for a dart off the tree. -/
def ivm : Stmt :=
  .seq (block [.divN 332 330 3, .addN 333 8 332, .loadN 333 333])
    (.ifLtN 0 332 (.ifLtN 333 330 ivO (.ifLtN 330 333 ivO ivS)) ivO)

/-- **`r331 := cvM r330`**. -/
def cvm : Stmt :=
  .seq (block [.addN 334 5 330, .loadN 344 334]) (.ifLtN 344 1 ivm (.instr (.copyN 331 0)))

/-- `rOut := phi3 rIn`. -/
def phiM (rIn rOut : ℕ) : Stmt :=
  .seq (.instr (.modN 345 rIn 3)) (.ifLtN 345 2 (.instr (.addN rOut rIn 1)) (.instr (.subN rOut rIn 2)))

/-- The choice of the heavier child: `a₂` if `a₁` is a tree dart or lighter. -/
def wchoose : Stmt :=
  .seq (block [.addN 334 5 355, .loadN 344 334])
    (.ifLtN 344 1 (.ifLtN 358 359 (block [.copyN 360 357, .copyN 361 359])
        (block [.copyN 360 355, .copyN 361 358]))
      (block [.copyN 360 357, .copyN 361 359]))

/-- **One step of the walk** from `δ = r350` with weight `r351`. -/
def mwbody : Stmt :=
  .seq (phiM 350 354) <| .seq (.instr (.loadN 355 354)) <| .seq (phiM 354 356) <|
  .seq (.instr (.loadN 357 356)) <|
  .seq (.instr (.copyN 330 355)) <| .seq cvm <| .seq (.instr (.copyN 358 331)) <|
  .seq (.instr (.copyN 330 357)) <| .seq cvm <| .seq (.instr (.copyN 359 331)) <|
  .seq wchoose <| .seq (.instr (.mulN 362 361 3)) <|
  .ifLtN 321 362 (block [.copyN 350 360, .copyN 351 361]) (block [.copyN 353 360, .copyN 352 1])

/-- The start of the walk from `δ₀ = pd (qu 1)`. -/
def mwstart : Stmt :=
  .seq (block [.addN 321 320 320, .addN 334 9 1, .loadN 345 334, .addN 334 8 345,
      .loadN 363 334, .copyN 330 363]) <|
  .seq ivm <| .seq (.instr (.mulN 362 331 3)) <|
  .ifLtN 321 362 (block [.copyN 350 363, .copyN 351 331, .copyN 352 0])
    (.seq (block [.loadN 330 363, .copyN 364 330]) <| .seq ivm <|
      .seq (.instr (.mulN 362 331 3)) <|
      .ifLtN 321 362 (block [.copyN 350 364, .copyN 351 331, .copyN 352 0])
        (block [.copyN 353 363, .copyN 352 1]))

/-- **The walk.** -/
def mwalk : Stmt := .seq mwstart (.whileLtN 352 1 mwbody)

/-! ### The state -/

/-- The data of the lowest-common-ancestor queries and the vertex arrays. -/
structure WL where
  n : ℕ
  r₀ : ℕ
  bD : ℕ
  bU : ℕ
  L : ℕ
  bV : ℕ
  bS : ℕ
  bW : ℕ
  f : ℕ → ℕ
  dep : ℕ → ℕ

/-- The memory and the registers the walk reads. -/
structure WSm (d : WD) (e : WL) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : CRegs d.k c
  A_m : ∀ x < 3 * d.k, c.nmem x = d.A x
  T_m : ∀ x < 3 * d.k, c.nmem (3 * d.k + x) = d.Tm x
  pd_m : ∀ f < d.k, c.nmem (8 * d.k + f) = d.pdf f
  J_m : ∀ f < d.k, f ≠ 0 → c.nmem (10 * d.k + f) = d.J f
  V_m : ∀ x < 3 * d.k, c.nmem (e.bV + x) = d.V x
  S_m : ∀ u < e.n, c.nmem (e.bS + u) = d.R u
  W_m : ∀ u < e.n, c.nmem (e.bW + u) = d.w u
  r162 : c.nreg 162 = e.bV
  r250 : c.nreg 250 = e.bW
  r252 : c.nreg 252 = e.bS
  r320 : c.nreg 320 = d.tot
  qfix : QFix e.n e.r₀ e.bD e.bU e.L W e.f e.dep c

/-- The numeric assumptions of the helpers. -/
structure WAm (d : WD) (e : WL) (W : ℕ) : Prop where
  tri : Tri d.k d.A d.Tm
  pdor : ∀ y < 3 * d.k, d.Tm y = 0 →
    (y / 3 ≠ 0 ∧ d.pdf (y / 3) = y) ∨ (d.A y / 3 ≠ 0 ∧ d.pdf (d.A y / 3) = d.A y)
  J_le : ∀ f < d.k, f ≠ 0 → d.J f ≤ d.tot
  V_lt : ∀ x < 3 * d.k, d.V x < e.n
  lc : ∀ u v, u < e.n → v < e.n → IsLCA e.f u v (d.Lc u v)
  cw_le : ∀ y < 3 * d.k, d.Tm y = 0 → cwN d y ≤ d.tot
  hV : e.bV + 3 * d.k ≤ W
  hS : e.bS + e.n ≤ W
  hW : e.bW + e.n ≤ W
  hk : 11 * d.k + 3 * d.tot + 4 ≤ W

section helpers

variable {d : WD} {e : WL} {W : ℕ} {P : Input}

theorem WSm.keep {c c' : Config} (h : WSm d e W c) (hw : WordsBounded W c')
    (hr : ∀ r, r < 280 ∨ r = 320 → c'.nreg r = c.nreg r) (hm : c'.nmem = c.nmem) :
    WSm d e W c' :=
  ⟨hw, cregs_of h.regs fun r hr' => hr r (Or.inl (by omega)), fun x hx => hm ▸ h.A_m x hx,
    fun x hx => hm ▸ h.T_m x hx, fun f hf => hm ▸ h.pd_m f hf, fun f hf h0 => hm ▸ h.J_m f hf h0,
    fun x hx => hm ▸ h.V_m x hx, fun u hu => hm ▸ h.S_m u hu, fun u hu => hm ▸ h.W_m u hu,
    (hr 162 (by omega)).trans h.r162, (hr 250 (by omega)).trans h.r250,
    (hr 252 (by omega)).trans h.r252, (hr 320 (by omega)).trans h.r320,
    h.qfix.of (fun r h' => hr r (Or.inl h')) (fun a _ => by rw [hm])⟩

/-- The frame of the helpers. -/
def FrM (c c' : Config) : Prop := ∀ r, r < 280 ∨ (292 ≤ r ∧ r ≤ 330) ∨ 346 < r → c'.nreg r = c.nreg r

theorem lc_lt (hA : WAm d e W) (hT : PTree e.n e.r₀ e.f e.dep) {u v : ℕ} (hu : u < e.n)
    (hv : v < e.n) : d.Lc u v < e.n := by
  obtain ⟨m, hm⟩ := (hA.lc u v hu hv).1; rw [← hm]; exact hT.iter_lt m hu

set_option maxHeartbeats 2000000 in
theorem ivO_exec (hA : WAm d e W) (c : Config) (hS : WSm d e W c) (hy : c.nreg 330 < 3 * d.k)
    (hT : d.Tm (c.nreg 330) = 0) (hno : ¬ (c.nreg 330 / 3 ≠ 0 ∧ d.pdf (c.nreg 330 / 3) = c.nreg 330)) :
    ∃ c' t, Exec P W ivO c c' t ∧ t ≤ 25 * e.L + 51 ∧ (WSm d e W c' ∧ FrM c c' ∧
      c'.nreg 331 = IvM d (c.nreg 330) ∧ c'.output = c.output) := by
  have hc := hS.wb
  have hTr := hS.qfix.tree
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hS.regs
  generalize hgy : c.nreg 330 = y at hy hT hno
  have hAy := hA.tri.A_lt y hy
  have hAA := hA.tri.A_A y hy
  have hor := hA.pdor y hy hT
  have hc0 : d.A y / 3 ≠ 0 := by tauto
  have hJ := hS.J_m (d.A y / 3) (by omega) hc0
  have hAm := hS.A_m y hy
  have hVa := hS.V_m _ hAy
  have hVy := hS.V_m _ hy
  have hxa := hA.V_lt _ hAy
  have hxy := hA.V_lt _ hy
  have hbV := hA.hV
  have hk := hA.hk
  obtain ⟨c₁, t₁, e₁, hw₁, g334, g336, g337, g338, fr₁, hm₁, ho₁, rfl⟩ : ∃ c₁ t₁, Exec P W
      (block [.loadN 334 330, .divN 335 334 3, .addN 336 10 335, .loadN 336 336,
        .addN 337 162 334, .loadN 337 337, .addN 338 162 330, .loadN 338 338]) c c₁ t₁ ∧
      WordsBounded W c₁ ∧ c₁.nreg 334 = d.A y ∧ c₁.nreg 336 = d.J (d.A y / 3) ∧
      c₁.nreg 337 = d.V (d.A y) ∧ c₁.nreg 338 = d.V y ∧
      (∀ r, r < 334 ∨ 338 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.output = c.output ∧ t₁ = 8 := by
    exec_block
    all_goals try (config_simp; simp only [hgy, hAm, h3, h10, hS.r162, hJ, hVa]; omega)
    refine ⟨‹_›, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals simp only [hgy, hAm, h3, h10, hS.r162, hJ, hVa, hVy]
    simp only [upd_apply]; split_ifs <;> first | omega | rfl
  have hS₁ : WSm d e W c₁ := hS.keep hw₁ (fun r hr => fr₁ r (by omega)) hm₁
  obtain ⟨c₂, t₂, e₂, ht₂, hl₂, -, fr₂, hm₂, ho₂⟩ := qcall_exec (P := P) c₁ hS₁.qfix hw₁
    (ra := 337) (rb := 338) (rd := 339) (by omega) (by omega) (by rw [g337]; exact hxa)
    (by rw [g338]; exact hxy)
  rw [g337, g338] at hl₂
  have hl : c₂.nreg 339 = d.Lc (d.V y) (d.V (d.A y)) := by
    have := IsLCA.unique hTr hxa hl₂ (hA.lc _ _ hxa hxy)
    rw [this]
    exact IsLCA.unique hTr hxa (hA.lc _ _ hxa hxy) (hA.lc _ _ hxy hxa).symm
  have hw₂ := e₂.wb_right
  have hS₂ : WSm d e W c₂ := hS₁.keep hw₂ (fun r hr => fr₂ r (by omega) (by omega)) hm₂
  have hlt := lc_lt hA hTr hxy hxa
  -- the cycle weight of `A y`
  set l := d.Lc (d.V y) (d.V (d.A y))
  have hcw : cwN d (d.A y) = (d.R (d.V (d.A y)) - d.R l) + (d.R (d.V y) - d.R l) + d.w l := by
    unfold cwN; rw [hAA]
    have : d.Lc (d.V (d.A y)) (d.V y) = l :=
      IsLCA.unique hTr hxa (hA.lc _ _ hxa hxy) (hA.lc _ _ hxy hxa).symm
    rw [this]
  have hcwle := hA.cw_le _ hAy (by rw [hA.tri.T_A y hy]; exact hT)
  have k337 : c₂.nreg 337 = d.V (d.A y) := by rw [fr₂ 337 (by omega) (by omega)]; exact g337
  have k338 : c₂.nreg 338 = d.V y := by rw [fr₂ 338 (by omega) (by omega)]; exact g338
  have k336 : c₂.nreg 336 = d.J (d.A y / 3) := by rw [fr₂ 336 (by omega) (by omega)]; exact g336
  have hc := hw₂
  have mS1 := hS₂.S_m _ hxa
  have mS2 := hS₂.S_m _ hlt
  have mS3 := hS₂.S_m _ hxy
  have mW := hS₂.W_m _ hlt
  have hbS := hA.hS
  have hbW := hA.hW
  obtain ⟨c₃, t₃, e₃, h₃, rfl⟩ : ∃ c₃ t₃, Exec P W
      (block [.addN 340 252 337, .loadN 340 340, .addN 341 252 339, .loadN 341 341,
        .subN 342 340 341, .addN 340 252 338, .loadN 340 340, .subN 343 340 341,
        .addN 342 342 343, .addN 340 250 339, .loadN 340 340, .addN 342 342 340,
        .subN 331 320 336, .subN 331 331 342]) c₂ c₃ t₃ ∧
      (WSm d e W c₃ ∧ (∀ r, r < 331 ∨ 343 < r → c₃.nreg r = c₂.nreg r) ∧
        c₃.nreg 331 = d.tot - d.J (d.A y / 3) - cwN d (d.A y) ∧ c₃.output = c₂.output) ∧
      t₃ = 14 := by
    exec_block
    all_goals try (config_simp; simp only [hS₂.r252, hS₂.r250, k337, k338, hl, mS1, mS2, mS3, mW]; omega)
    refine ⟨⟨hS₂.keep ‹_› (fun r hr => ?_) rfl, fun r hr => ?_, ?_, rfl⟩, rfl⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
    · simp only [hS₂.r252, hS₂.r250, hS₂.r320, k336, k337, k338, hl, mS1, mS2, mS3, mW, hcw]
  refine ⟨c₃, 8 + (t₂ + 14), .seq e₁ (.seq e₂ e₃), by omega, h₃.1, fun r hr => ?_, ?_,
    by rw [h₃.2.2.2, ho₂, ho₁]⟩
  · rw [h₃.2.1 r (by omega), fr₂ r (by omega) (by omega), fr₁ r (by omega)]
  · rw [h₃.2.2.1]; unfold IvM; rw [ite_eq_right_iff.2 (fun h => absurd h hno)]

theorem FrM.trans {c c₁ c₂ : Config} (h₁ : FrM c c₁) (h₂ : FrM c₁ c₂) : FrM c c₂ :=
  fun r hr => (h₂ r hr).trans (h₁ r hr)

set_option maxHeartbeats 1000000 in
/-- **`IvM` on the machine.** -/
theorem ivm_exec (hA : WAm d e W) (c : Config) (hS : WSm d e W c) (hy : c.nreg 330 < 3 * d.k)
    (hT : d.Tm (c.nreg 330) = 0) :
    ∃ c' t, Exec P W ivm c c' t ∧ t ≤ 25 * e.L + 60 ∧ (WSm d e W c' ∧ FrM c c' ∧
      c'.nreg 331 = IvM d (c.nreg 330) ∧ c'.output = c.output) := by
  have hc := hS.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hS.regs
  have hk := hA.hk
  have hpdm : c.nmem (8 * d.k + c.nreg 330 / 3) = d.pdf (c.nreg 330 / 3) :=
    hS.pd_m _ (by omega)
  obtain ⟨c₁, t₁, e₁, hw₁, g332, g333, fr₁, hm₁, ho₁, rfl⟩ : ∃ c₁ t₁, Exec P W
      (block [.divN 332 330 3, .addN 333 8 332, .loadN 333 333]) c c₁ t₁ ∧
      WordsBounded W c₁ ∧ c₁.nreg 332 = c.nreg 330 / 3 ∧ c₁.nreg 333 = d.pdf (c.nreg 330 / 3) ∧
      (∀ r, r < 332 ∨ 333 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.output = c.output ∧ t₁ = 3 := by
    exec_block
    · config_simp; rw [h8, h3]; omega
    refine ⟨‹_›, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    · rw [h3]
    · rw [h8, h3, hpdm]
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
  have hS₁ : WSm d e W c₁ := hS.keep hw₁ (fun r hr => fr₁ r (by omega)) hm₁
  have g330 : c₁.nreg 330 = c.nreg 330 := fr₁ 330 (by omega)
  have gfr : FrM c c₁ := fun r hr => fr₁ r (by omega)
  have g0 : c₁.nreg 0 = 0 := (fr₁ 0 (by omega)).trans h0
  have other : ¬ (c.nreg 330 / 3 ≠ 0 ∧ d.pdf (c.nreg 330 / 3) = c.nreg 330) →
      ∃ c' t, Exec P W ivO c₁ c' t ∧ t ≤ 25 * e.L + 51 ∧ (WSm d e W c' ∧ FrM c c' ∧
        c'.nreg 331 = IvM d (c.nreg 330) ∧ c'.output = c.output) := fun hno => by
    obtain ⟨c', t, ex, ht, hS', hfr, h331, ho⟩ := ivO_exec (P := P) hA c₁ hS₁
      (by rw [g330]; exact hy) (by rw [g330]; exact hT) (by rw [g330]; exact hno)
    exact ⟨c', t, ex, ht, hS', gfr.trans hfr, by rw [h331, g330], by rw [ho, ho₁]⟩
  unfold ivm
  refine spec_seq ⟨c₁, 3, e₁, ?_⟩
  by_cases hcond : c.nreg 330 / 3 ≠ 0 ∧ d.pdf (c.nreg 330 / 3) = c.nreg 330
  · refine spec_ifLtN_true (by rw [g0, g332]; omega) ?_
    refine spec_ifLtN_false (by rw [g333, g330, hcond.2]; omega) ?_
    refine spec_ifLtN_false (by rw [g333, g330, hcond.2]; omega) ?_
    have hJm := hS.J_m (c.nreg 330 / 3) (by omega) hcond.1
    have hc := hw₁
    have g10 : c₁.nreg 10 = 10 * d.k := (fr₁ 10 (by omega)).trans h10
    unfold ivS
    exec_block
    · config_simp; rw [g10, g332]; omega
    refine ⟨by omega, hS₁.keep ‹_› (fun r hr => by
      config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl) rfl,
      gfr.trans fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl,
      ?_, by rw [ho₁]⟩
    config_simp; rw [g10, g332, hm₁, hJm]; unfold IvM; rw [ite_eq_left_of_eq_true _ _ (eq_true hcond)]
  · obtain ⟨c', t, ex, ht, post⟩ := other hcond
    by_cases h332 : 0 < c₁.nreg 332
    · have hne : d.pdf (c.nreg 330 / 3) ≠ c.nreg 330 := fun h => hcond ⟨by omega, h⟩
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨c', t + 1 + 1, .ifLtN_true (by rw [g0]; exact h332)
          (.ifLtN_true (by rw [g333, g330]; exact hlt) ex), by omega, post⟩
      · exact ⟨c', t + 1 + 2 + 1, .ifLtN_true (by rw [g0]; exact h332)
          (.ifLtN_false (by rw [g333, g330]; omega) (.ifLtN_true (by rw [g333, g330]; exact hgt) ex)),
          by omega, post⟩
    · exact ⟨c', t + 2, .ifLtN_false (by rw [g0]; exact h332) ex, by omega, post⟩

theorem IvM_le (hA : WAm d e W) {y : ℕ} (hy : y < 3 * d.k) : IvM d y ≤ d.tot := by
  unfold IvM; split_ifs with h
  · exact hA.J_le _ (by have := hA.tri.A_lt y hy; omega) h.1
  · omega

theorem cvM_le (hA : WAm d e W) {y : ℕ} (hy : y < 3 * d.k) : cvM d y ≤ d.tot := by
  unfold cvM; split_ifs
  · exact IvM_le hA hy
  · omega

/-- **`cvM` on the machine.** -/
theorem cvm_exec (hA : WAm d e W) (c : Config) (hS : WSm d e W c) (hy : c.nreg 330 < 3 * d.k) :
    ∃ c' t, Exec P W cvm c c' t ∧ t ≤ 25 * e.L + 63 ∧ (WSm d e W c' ∧ FrM c c' ∧
      c'.nreg 331 = cvM d (c.nreg 330) ∧ c'.output = c.output) := by
  have hc := hS.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hS.regs
  have hk := hA.hk
  have hTm := hS.T_m _ hy
  have hTle := hA.tri.T_le _ hy
  obtain ⟨c₁, t₁, e₁, hw₁, g344, fr₁, hm₁, ho₁, rfl⟩ : ∃ c₁ t₁, Exec P W
      (block [.addN 334 5 330, .loadN 344 334]) c c₁ t₁ ∧ WordsBounded W c₁ ∧
      c₁.nreg 344 = d.Tm (c.nreg 330) ∧ (∀ r, r ≠ 334 → r ≠ 344 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.output = c.output ∧ t₁ = 2 := by
    exec_block
    · config_simp; rw [h5]; omega
    refine ⟨‹_›, ?_, fun r a b => ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    · rw [h5, hTm]
    · rw [upd_other _ _ _ b, upd_other _ _ _ a]
  have hS₁ : WSm d e W c₁ := hS.keep hw₁ (fun r hr => fr₁ r (by omega) (by omega)) hm₁
  have gfr : FrM c c₁ := fun r hr => fr₁ r (by omega) (by omega)
  have g330 : c₁.nreg 330 = c.nreg 330 := fr₁ 330 (by omega) (by omega)
  have g141 : c₁.nreg 1 = 1 := (fr₁ 1 (by omega) (by omega)).trans h1
  by_cases hT : d.Tm (c.nreg 330) = 0
  · obtain ⟨c', t, ex, ht, hS', hfr, h331, ho⟩ := ivm_exec (P := P) hA c₁ hS₁
      (by rw [g330]; exact hy) (by rw [g330]; exact hT)
    refine ⟨c', 2 + (t + 1), .seq e₁ (.ifLtN_true (by rw [g344, g141, hT]; omega) ex), by omega,
      hS', gfr.trans hfr, ?_, by rw [ho, ho₁]⟩
    rw [h331, g330]; unfold cvM; rw [ite_eq_left_of_eq_true _ _ (eq_true hT)]
  · have e₂ := Exec.copyN (P := P) hw₁ 331 0
    refine ⟨_, 2 + (1 + 2), .seq e₁ (.ifLtN_false (by rw [g344, g141]; omega) e₂), by omega,
      hS₁.keep e₂.wb_right (fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]) rfl,
      gfr.trans fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)], ?_, by rw [ho₁]⟩
    config_simp
    rw [(fr₁ 0 (by omega) (by omega)).trans h0]; unfold cvM; rw [ite_eq_right_iff.2 (fun h => absurd h hT)]

/-- **`phi3` on the machine.** -/
theorem phiM_exec {rIn rOut : ℕ} (hIn : rIn ≠ 345) (_hOut : rOut ≠ 345) (c : Config)
    (hS : WSm d e W c) (hy : c.nreg rIn < 3 * d.k) (hk : 3 * d.k ≤ W) :
    ∃ c' t, Exec P W (phiM rIn rOut) c c' t ∧ t ≤ 4 ∧
      c'.nreg rOut = phi3 (c.nreg rIn) ∧ (∀ r, r ≠ 345 → r ≠ rOut → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.output = c.output ∧ WordsBounded W c' := by
  have hc := hS.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hS.regs
  have e₁ := Exec.modN (P := P) hc 345 rIn 3
  have hw₁ := e₁.wb_right
  have gi : ∀ r, r ≠ 345 → upd c.nreg 345 (c.nreg rIn % c.nreg 3) r = c.nreg r :=
    fun r hr => upd_other _ _ _ hr
  by_cases hm : c.nreg rIn % 3 < 2
  · have e₂ := Exec.addN (P := P) hw₁ rOut rIn 1 (by simp only [Config.nreg_mk]; rw [gi _ hIn, gi _ (by omega), h1]; omega)
    refine ⟨_, 1 + (1 + 1), .seq e₁ (.ifLtN_true (by simp only [Config.nreg_mk, upd_same]; rw [gi 2 (by omega), h2, h3]; exact hm) e₂),
      by omega, ?_, fun r a b => ?_, rfl, rfl, e₂.wb_right⟩
    · simp only [Config.nreg_mk, upd_same]; rw [gi _ hIn, gi _ (by omega), h1]
      unfold phi3; rw [ite_eq_left_of_eq_true _ _ (eq_true hm)]
    · simp only [Config.nreg_mk]; rw [upd_other _ _ _ b, gi _ a]
  · have e₂ := Exec.subN (P := P) hw₁ rOut rIn 2
    refine ⟨_, 1 + (1 + 2), .seq e₁ (.ifLtN_false (by simp only [Config.nreg_mk, upd_same]; rw [gi 2 (by omega), h2, h3]; omega) e₂),
      by omega, ?_, fun r a b => ?_, rfl, rfl, e₂.wb_right⟩
    · simp only [Config.nreg_mk, upd_same]; rw [gi _ hIn, gi _ (by omega), h2]
      unfold phi3; rw [ite_eq_right_iff.2 (fun h => absurd h hm)]
    · simp only [Config.nreg_mk]; rw [upd_other _ _ _ b, gi _ a]

end helpers

/-! ### The walk -/

/-- The child chosen from `a₁`, `a₂` with weights `I₁`, `I₂`: `a₂` if `a₁` is a tree dart or
lighter. -/
def choice (d : WD) (a₁ a₂ I₁ I₂ : ℕ) : ℕ × ℕ :=
  if d.Tm a₁ = 0 then (if I₁ < I₂ then (a₂, I₂) else (a₁, I₁)) else (a₂, I₂)

/-- The outcome of the walk: a dart `r353` off the tree whose two sides weigh at most `2/3`. -/
def MGood (d : WD) (c : Config) : Prop :=
  c.nreg 352 = 1 ∧ c.nreg 353 < 3 * d.k ∧ d.Tm (c.nreg 353) = 0 ∧
    3 * IvM d (c.nreg 353) ≤ 2 * d.tot ∧ 3 * IvM d (d.A (c.nreg 353)) ≤ 2 * d.tot

/-- The walk is running from `δ = r350`, heavier than `2/3`. -/
def MRun (d : WD) (c : Config) : Prop :=
  c.nreg 352 = 0 ∧ c.nreg 350 < 3 * d.k ∧ d.Tm (c.nreg 350) = 0 ∧
    c.nreg 351 = IvM d (c.nreg 350) ∧ 2 * d.tot < 3 * c.nreg 351

/-- The state of the walk. -/
structure MWI (d : WD) (e : WL) (W : ℕ) (o : List ℕ) (c : Config) : Prop where
  ws : WSm d e W c
  r321 : c.nreg 321 = 2 * d.tot
  out : c.output = o
  st : MRun d c ∨ MGood d c

/-- The facts on the strict inside weights which the walk uses: the recurrence with the weight
`Bs y` of `bset y`, which lies on the cycle of each child off the tree and vanishes if both are
tree darts, the complement rule, and a size decreasing along the walk. -/
structure MWH (d : WD) (sz Bs : ℕ → ℕ) : Prop where
  recI : ∀ y < 3 * d.k, d.Tm y = 0 →
    IvM d y = cvM d (d.A (phi3 y)) + cvM d (d.A (phi3 (phi3 y))) + Bs y
  sub₁ : ∀ y < 3 * d.k, d.Tm y = 0 → d.Tm (d.A (phi3 y)) = 0 → Bs y ≤ cwN d (d.A (phi3 y))
  sub₂ : ∀ y < 3 * d.k, d.Tm y = 0 → d.Tm (d.A (phi3 (phi3 y))) = 0 →
    Bs y ≤ cwN d (d.A (phi3 (phi3 y)))
  empty : ∀ y < 3 * d.k, d.Tm y = 0 → d.Tm (d.A (phi3 y)) ≠ 0 →
    d.Tm (d.A (phi3 (phi3 y))) ≠ 0 → Bs y = 0
  comp : ∀ y < 3 * d.k, d.Tm y = 0 → IvM d y + IvM d (d.A y) + cwN d y = d.tot
  dec₁ : ∀ y < 3 * d.k, d.Tm y = 0 → d.Tm (d.A (phi3 y)) = 0 → sz (d.A (phi3 y)) < sz y
  dec₂ : ∀ y < 3 * d.k, d.Tm y = 0 → d.Tm (d.A (phi3 (phi3 y))) = 0 →
    sz (d.A (phi3 (phi3 y))) < sz y
  sz_le : ∀ y < 3 * d.k, sz y ≤ d.k

section walk

variable {d : WD} {e : WL} {W : ℕ} {P : Input} {o : List ℕ} {sz Bs : ℕ → ℕ}

/-- **The choice is a heavier child off the tree, and `bset` lies on its cycle.** -/
theorem choice_spec (hA : WAm d e W) (hH : MWH d sz Bs) {δ : ℕ} (hδ : δ < 3 * d.k)
    (hT : d.Tm δ = 0) (heavy : 2 * d.tot < 3 * IvM d δ) :
    let a := (choice d (d.A (phi3 δ)) (d.A (phi3 (phi3 δ))) (cvM d (d.A (phi3 δ)))
      (cvM d (d.A (phi3 (phi3 δ))))).1
    let I := (choice d (d.A (phi3 δ)) (d.A (phi3 (phi3 δ))) (cvM d (d.A (phi3 δ)))
      (cvM d (d.A (phi3 (phi3 δ))))).2
    a < 3 * d.k ∧ d.Tm a = 0 ∧ I = IvM d a ∧ sz a < sz δ ∧
      IvM d δ ≤ 2 * I + cwN d a := by
  intro a I
  have h1 := phi3_lt hδ
  have h2 := phi3_lt h1
  have hA₁ := hA.tri.A_lt _ h1
  have hA₂ := hA.tri.A_lt _ h2
  have hrec := hH.recI δ hδ hT
  have hcv : ∀ z, d.Tm z ≠ 0 → cvM d z = 0 := fun z h => by
    unfold cvM; rw [ite_eq_right_iff.2 (fun h' => absurd h' h)]
  have hcv' : ∀ z, d.Tm z = 0 → cvM d z = IvM d z := fun z h => by
    unfold cvM; rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  simp only [a, I, choice]
  by_cases t₁ : d.Tm (d.A (phi3 δ)) = 0
  · simp only [t₁, ↓reduceIte]
    by_cases hlt : cvM d (d.A (phi3 δ)) < cvM d (d.A (phi3 (phi3 δ)))
    · simp only [hlt, ↓reduceIte]
      have t₂ : d.Tm (d.A (phi3 (phi3 δ))) = 0 := by
        by_contra h; rw [hcv _ h] at hlt; omega
      have := hH.sub₂ δ hδ hT t₂
      exact ⟨hA₂, t₂, hcv' _ t₂, hH.dec₂ δ hδ hT t₂, by omega⟩
    · simp only [hlt, ↓reduceIte]
      have := hH.sub₁ δ hδ hT t₁
      exact ⟨hA₁, t₁, hcv' _ t₁, hH.dec₁ δ hδ hT t₁, by omega⟩
  · simp only [t₁, ↓reduceIte]
    have t₂ : d.Tm (d.A (phi3 (phi3 δ))) = 0 := by
      by_contra h
      have := hH.empty δ hδ hT t₁ h
      rw [hcv _ t₁, hcv _ h] at hrec
      omega
    have := hH.sub₂ δ hδ hT t₂
    rw [hcv _ t₁] at hrec
    exact ⟨hA₂, t₂, hcv' _ t₂, hH.dec₂ δ hδ hT t₂, by omega⟩

theorem wchoose_exec (hA : WAm d e W) (c : Config) (hS : WSm d e W c) {a₁ a₂ I₁ I₂ : ℕ}
    (h355 : c.nreg 355 = a₁) (h357 : c.nreg 357 = a₂) (h358 : c.nreg 358 = I₁)
    (h359 : c.nreg 359 = I₂) (ha₁ : a₁ < 3 * d.k) :
    ∃ c' t, Exec P W wchoose c c' t ∧ t ≤ 7 ∧ (WSm d e W c' ∧
      c'.nreg 360 = (choice d a₁ a₂ I₁ I₂).1 ∧ c'.nreg 361 = (choice d a₁ a₂ I₁ I₂).2 ∧
      (∀ r, r ≠ 334 → r ≠ 344 → r ≠ 360 → r ≠ 361 → c'.nreg r = c.nreg r) ∧
      c'.output = c.output) := by
  have hc := hS.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hS.regs
  have hk := hA.hk
  have hTm := hS.T_m _ ha₁
  have hTle := hA.tri.T_le _ ha₁
  unfold wchoose
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h5, h355]; omega
  config_simp
  rw [h5, h355, hTm]
  rename_i hw₁
  config_simp at hw₁
  rw [h5, h355, hTm] at hw₁
  have keep : ∀ c', WordsBounded W c' → (∀ r, r ≠ 334 → r ≠ 344 → r ≠ 360 → r ≠ 361 →
      c'.nreg r = c.nreg r) → c'.nmem = c.nmem → WSm d e W c' := fun c' hw hr hm =>
    hS.keep hw (fun r hr' => hr r (by omega) (by omega) (by omega) (by omega)) hm
  by_cases t₁ : d.Tm a₁ = 0
  · refine spec_ifLtN_true (by config_simp; rw [h1, t₁]; omega) ?_
    by_cases hlt : I₁ < I₂
    · refine spec_ifLtN_true (by config_simp; rw [h358, h359]; exact hlt) ?_
      exec_block
      refine ⟨by omega, keep _ ‹_› (fun r a b c' d' => ?_) rfl, ?_, ?_, fun r a b c' d' => ?_, rfl⟩
      all_goals config_simp
      all_goals first
        | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)
        | simp only [choice, t₁, hlt, ↓reduceIte, h357, h359]
    · refine spec_ifLtN_false (by config_simp; rw [h358, h359]; exact hlt) ?_
      exec_block
      refine ⟨by omega, keep _ ‹_› (fun r a b c' d' => ?_) rfl, ?_, ?_, fun r a b c' d' => ?_, rfl⟩
      all_goals config_simp
      all_goals first
        | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)
        | simp only [choice, t₁, hlt, ↓reduceIte, h355, h358]
  · refine spec_ifLtN_false (by config_simp; rw [h1]; omega) ?_
    exec_block
    refine ⟨by omega, keep _ ‹_› (fun r a b c' d' => ?_) rfl, ?_, ?_, fun r a b c' d' => ?_, rfl⟩
    all_goals config_simp
    all_goals first
      | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)
      | simp only [choice, t₁, ↓reduceIte, h357, h359]

/-! ### One step of the walk -/

theorem step_load (c : Config) (hw : WordsBounded W c) (r a : ℕ) :
    ∃ c', Exec P W (.instr (.loadN r a)) c c' 1 ∧ c'.nreg r = c.nmem (c.nreg a) ∧
      (∀ q, q ≠ r → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem ∧ c'.output = c.output ∧
      WordsBounded W c' :=
  ⟨_, Exec.loadN hw r a, by config_simp, fun q hq => by config_simp; rw [upd_other _ _ _ hq],
    rfl, rfl, (Exec.loadN (P := P) hw r a).wb_right⟩

theorem step_copy (c : Config) (hw : WordsBounded W c) (r a : ℕ) :
    ∃ c', Exec P W (.instr (.copyN r a)) c c' 1 ∧ c'.nreg r = c.nreg a ∧
      (∀ q, q ≠ r → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem ∧ c'.output = c.output ∧
      WordsBounded W c' :=
  ⟨_, Exec.copyN hw r a, by config_simp, fun q hq => by config_simp; rw [upd_other _ _ _ hq],
    rfl, rfl, (Exec.copyN (P := P) hw r a).wb_right⟩

theorem step_mul (c : Config) (hw : WordsBounded W c) (r a b : ℕ) (hb : c.nreg a * c.nreg b ≤ W) :
    ∃ c', Exec P W (.instr (.mulN r a b)) c c' 1 ∧ c'.nreg r = c.nreg a * c.nreg b ∧
      (∀ q, q ≠ r → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem ∧ c'.output = c.output ∧
      WordsBounded W c' :=
  ⟨_, Exec.mulN hw r a b hb, by config_simp, fun q hq => by config_simp; rw [upd_other _ _ _ hq],
    rfl, rfl, (Exec.mulN (P := P) hw r a b hb).wb_right⟩

set_option maxHeartbeats 4000000 in
/-- **One step of the walk.** -/
theorem mwbody_exec (hA : WAm d e W) (hH : MWH d sz Bs) (c : Config) (hI : MWI d e W o c)
    (hrun : MRun d c) :
    ∃ c' t, Exec P W mwbody c c' t ∧ MWI d e W o c' ∧
      (if c'.nreg 352 = 0 then (50 * e.L + 160) * (sz (c'.nreg 350) + 1) else 0) + t + 2 ≤
        (50 * e.L + 160) * (sz (c.nreg 350) + 1) := by
  obtain ⟨r352, hδ, hTδ, r351, heavy⟩ := hrun
  have hS := hI.ws
  have hk := hA.hk
  have h3 := hS.regs.2.2.2.1
  have h1 := hS.regs.2.1
  generalize hgδ : c.nreg 350 = δ at hδ hTδ r351
  rw [r351] at heavy
  have hp1 := phi3_lt hδ
  have hp2 := phi3_lt hp1
  have ha1 := hA.tri.A_lt _ hp1
  have ha2 := hA.tri.A_lt _ hp2
  obtain ⟨hca, hcT, hcI, hcsz, hcw⟩ := choice_spec hA hH hδ hTδ heavy
  set a := (choice d (d.A (phi3 δ)) (d.A (phi3 (phi3 δ))) (cvM d (d.A (phi3 δ)))
      (cvM d (d.A (phi3 (phi3 δ))))).1 with ha_def
  set I := (choice d (d.A (phi3 δ)) (d.A (phi3 (phi3 δ))) (cvM d (d.A (phi3 δ)))
      (cvM d (d.A (phi3 (phi3 δ))))).2 with hI_def
  have hIle : I ≤ d.tot := by rw [hcI]; exact IvM_le hA hca
  -- φ δ, a₁
  obtain ⟨c₁, t₁, e₁, ht₁, g354, fr₁, hm₁, ho₁, hw₁⟩ := phiM_exec (P := P) (rIn := 350)
    (rOut := 354) (by omega) (by omega) c hS (by rw [hgδ]; exact hδ) (by omega)
  rw [hgδ] at g354
  have hS₁ := hS.keep hw₁ (fun r hr => fr₁ r (by omega) (by omega)) hm₁
  obtain ⟨c₂, e₂, g355, fr₂, hm₂, ho₂, hw₂⟩ := step_load (P := P) c₁ hw₁ 355 354
  rw [g354, hS₁.A_m _ hp1] at g355
  have hS₂ := hS₁.keep hw₂ (fun r hr => fr₂ r (by omega)) hm₂
  -- φ² δ, a₂
  obtain ⟨c₃, t₃, e₃, ht₃, g356, fr₃, hm₃, ho₃, hw₃⟩ := phiM_exec (P := P) (rIn := 354)
    (rOut := 356) (by omega) (by omega) c₂ hS₂ (by rw [fr₂ 354 (by omega), g354]; exact hp1)
    (by omega)
  rw [fr₂ 354 (by omega), g354] at g356
  have hS₃ := hS₂.keep hw₃ (fun r hr => fr₃ r (by omega) (by omega)) hm₃
  obtain ⟨c₄, e₄, g357, fr₄, hm₄, ho₄, hw₄⟩ := step_load (P := P) c₃ hw₃ 357 356
  rw [g356, hS₃.A_m _ hp2] at g357
  have hS₄ := hS₃.keep hw₄ (fun r hr => fr₄ r (by omega)) hm₄
  have k355 : c₄.nreg 355 = d.A (phi3 δ) := by
    rw [fr₄ 355 (by omega), fr₃ 355 (by omega) (by omega), g355]
  -- the two weights
  obtain ⟨c₅, e₅, g330, fr₅, hm₅, ho₅, hw₅⟩ := step_copy (P := P) c₄ hw₄ 330 355
  rw [k355] at g330
  have hS₅ := hS₄.keep hw₅ (fun r hr => fr₅ r (by omega)) hm₅
  obtain ⟨c₆, t₆, e₆, ht₆, hS₆, fr₆, g331, ho₆⟩ := cvm_exec (P := P) hA c₅ hS₅
    (by rw [g330]; exact ha1)
  rw [g330] at g331
  obtain ⟨c₇, e₇, g358, fr₇, hm₇, ho₇, hw₇⟩ := step_copy (P := P) c₆ (hS₆.wb) 358 331
  rw [g331] at g358
  have hS₇ := hS₆.keep hw₇ (fun r hr => fr₇ r (by omega)) hm₇
  have k357 : c₇.nreg 357 = d.A (phi3 (phi3 δ)) := by
    rw [fr₇ 357 (by omega), fr₆ 357 (by omega), fr₅ 357 (by omega), g357]
  obtain ⟨c₈, e₈, g330', fr₈, hm₈, ho₈, hw₈⟩ := step_copy (P := P) c₇ hw₇ 330 357
  rw [k357] at g330'
  have hS₈ := hS₇.keep hw₈ (fun r hr => fr₈ r (by omega)) hm₈
  obtain ⟨c₉, t₉, e₉, ht₉, hS₉, fr₉, g331', ho₉⟩ := cvm_exec (P := P) hA c₈ hS₈
    (by rw [g330']; exact ha2)
  rw [g330'] at g331'
  obtain ⟨c₁₀, e₁₀, g359, fr₁₀, hm₁₀, ho₁₀, hw₁₀⟩ := step_copy (P := P) c₉ (hS₉.wb) 359 331
  rw [g331'] at g359
  have hS₁₀ := hS₉.keep hw₁₀ (fun r hr => fr₁₀ r (by omega)) hm₁₀
  -- the choice
  have k355' : c₁₀.nreg 355 = d.A (phi3 δ) := by
    rw [fr₁₀ 355 (by omega), fr₉ 355 (by omega), fr₈ 355 (by omega), fr₇ 355 (by omega),
      fr₆ 355 (by omega), fr₅ 355 (by omega), k355]
  have k357' : c₁₀.nreg 357 = d.A (phi3 (phi3 δ)) := by
    rw [fr₁₀ 357 (by omega), fr₉ 357 (by omega), fr₈ 357 (by omega), k357]
  have k358 : c₁₀.nreg 358 = cvM d (d.A (phi3 δ)) := by
    rw [fr₁₀ 358 (by omega), fr₉ 358 (by omega), fr₈ 358 (by omega), g358]
  obtain ⟨c₁₁, t₁₁, e₁₁, ht₁₁, hS₁₁, g360, g361, fr₁₁, ho₁₁⟩ := wchoose_exec (P := P) hA c₁₀
    hS₁₀ k355' k357' k358 g359 ha1
  have hw₁₁ := hS₁₁.wb
  have g3 : c₁₁.nreg 3 = 3 := (fr₁₁ 3 (by omega) (by omega) (by omega) (by omega)).trans
    hS₁₀.regs.2.2.2.1
  obtain ⟨c₁₂, e₁₂, g362, fr₁₂, hm₁₂, ho₁₂, hw₁₂⟩ := step_mul (P := P) c₁₁ hw₁₁ 362 361 3
    (by rw [g361, g3]; omega)
  rw [g361, g3] at g362
  have hS₁₂ := hS₁₁.keep hw₁₂ (fun r hr => fr₁₂ r (by omega)) hm₁₂
  -- the registers kept from the start
  have keep : ∀ r, r < 280 ∨ (292 ≤ r ∧ r ≤ 329) ∨ 363 ≤ r ∨ r = 352 → c₁₂.nreg r = c.nreg r :=
    fun r hr => by
      rw [fr₁₂ r (by omega), fr₁₁ r (by omega) (by omega) (by omega) (by omega),
        fr₁₀ r (by omega), fr₉ r (by omega), fr₈ r (by omega), fr₇ r (by omega),
        fr₆ r (by omega), fr₅ r (by omega), fr₄ r (by omega), fr₃ r (by omega) (by omega),
        fr₂ r (by omega), fr₁ r (by omega) (by omega)]
  have k321 : c₁₂.nreg 321 = 2 * d.tot := (keep 321 (by omega)).trans hI.r321
  have k360 : c₁₂.nreg 360 = a := by rw [fr₁₂ 360 (by omega), g360]
  have k361 : c₁₂.nreg 361 = I := by rw [fr₁₂ 361 (by omega), g361]
  have ho12 : c₁₂.output = o := by
    rw [ho₁₂, ho₁₁, ho₁₀, ho₉, ho₈, ho₇, ho₆, ho₅, ho₄, ho₃, ho₂, ho₁, hI.out]
  have hpre : Exec P W (.seq (phiM 350 354) <| .seq (.instr (.loadN 355 354)) <|
      .seq (phiM 354 356) <| .seq (.instr (.loadN 357 356)) <|
      .seq (.instr (.copyN 330 355)) <| .seq cvm <| .seq (.instr (.copyN 358 331)) <|
      .seq (.instr (.copyN 330 357)) <| .seq cvm <| .seq (.instr (.copyN 359 331)) <|
      .seq wchoose (.instr (.mulN 362 361 3))) c c₁₂
      (t₁ + (1 + (t₃ + (1 + (1 + (t₆ + (1 + (1 + (t₉ + (1 + (t₁₁ + 1))))))))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉
      (.seq e₁₀ (.seq e₁₁ e₁₂))))))))))
  have hcost : t₁ + (1 + (t₃ + (1 + (1 + (t₆ + (1 + (1 + (t₉ + (1 + (t₁₁ + 1)))))))))) ≤
      50 * e.L + 154 := by omega
  -- the comparison
  have hseq : ∀ s c' t', Exec P W s c₁₂ c' t' → Exec P W (.seq (phiM 350 354) <|
      .seq (.instr (.loadN 355 354)) <| .seq (phiM 354 356) <| .seq (.instr (.loadN 357 356)) <|
      .seq (.instr (.copyN 330 355)) <| .seq cvm <| .seq (.instr (.copyN 358 331)) <|
      .seq (.instr (.copyN 330 357)) <| .seq cvm <| .seq (.instr (.copyN 359 331)) <|
      .seq wchoose <| .seq (.instr (.mulN 362 361 3)) s) c c'
      (t₁ + (1 + (t₃ + (1 + (1 + (t₆ + (1 + (1 + (t₉ + (1 + (t₁₁ + (1 + t')))))))))))) := by
    intro s c' t' ex
    exact .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉
      (.seq e₁₀ (.seq e₁₁ (.seq e₁₂ ex)))))))))))
  have hcomp := hH.comp a hca hcT
  have hB := hA.cw_le a hca hcT
  have hc12 := hw₁₂
  by_cases hgo : 2 * d.tot < 3 * I
  · -- continue from `a`
    obtain ⟨c₁₃, t₁₃, e₁₃, hI₁₃, rfl⟩ : ∃ c₁₃ t₁₃, Exec P W (block [.copyN 350 360, .copyN 351 361])
        c₁₂ c₁₃ t₁₃ ∧ (MWI d e W o c₁₃ ∧ c₁₃.nreg 352 = 0 ∧ c₁₃.nreg 350 = a) ∧ t₁₃ = 2 := by
      have hc := hc12
      exec_block
      refine ⟨⟨⟨hS₁₂.keep ‹_› (fun r hr => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl) rfl, ?_, ho12,
        Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩⟩, ?_, ?_⟩, rfl⟩
      all_goals config_simp
      all_goals try simp only [k321, k360, k361]
      all_goals first | exact hca | exact hcT | exact hcI | exact hgo | skip
      all_goals (rw [keep 352 (by omega)]; exact r352)
    refine ⟨c₁₃, _, hseq _ _ _ (.ifLtN_true (by rw [k321, g362]; omega) e₁₃), hI₁₃.1, ?_⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true hI₁₃.2.1), hI₁₃.2.2]
    have : (50 * e.L + 160) * (sz a + 1) + (50 * e.L + 160) ≤
        (50 * e.L + 160) * (sz δ + 1) := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  · -- stop at `a`
    obtain ⟨c₁₃, t₁₃, e₁₃, hI₁₃, rfl⟩ : ∃ c₁₃ t₁₃, Exec P W (block [.copyN 353 360, .copyN 352 1])
        c₁₂ c₁₃ t₁₃ ∧ (MWI d e W o c₁₃ ∧ c₁₃.nreg 352 = 1) ∧ t₁₃ = 2 := by
      have hc := hc12
      have k1 : c₁₂.nreg 1 = 1 := (keep 1 (by omega)).trans h1
      exec_block
      refine ⟨⟨⟨hS₁₂.keep ‹_› (fun r hr => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl) rfl, ?_, ho12,
        Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩⟩, ?_⟩, rfl⟩
      all_goals config_simp
      all_goals try simp only [k321, k360, k1]
      all_goals first | exact hca | exact hcT | skip
      · rw [← hcI]; omega
      · omega
    refine ⟨c₁₃, _, hseq _ _ _ (.ifLtN_false (by rw [k321, g362]; omega) e₁₃), hI₁₃.1, ?_⟩
    rw [ite_eq_right_iff.2 (fun h => absurd (hI₁₃.2.symm.trans h) (by omega))]
    have : 50 * e.L + 160 ≤ (50 * e.L + 160) * (sz δ + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega

set_option maxHeartbeats 4000000 in
/-- **The start of the walk.** -/
theorem mwstart_exec (hA : WAm d e W) (c : Config) (hS : WSm d e W c) (ho : c.output = o)
    (hq1 : c.nmem (9 * d.k + 1) < d.k) (hd0 : d.pdf (c.nmem (9 * d.k + 1)) < 3 * d.k)
    (hT0 : d.Tm (d.pdf (c.nmem (9 * d.k + 1))) = 0) :
    ∃ c' t, Exec P W mwstart c c' t ∧ MWI d e W o c' ∧ t ≤ 50 * e.L + 140 := by
  have hc := hS.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hS.regs
  have hk := hA.hk
  generalize hgq : c.nmem (9 * d.k + 1) = q at hq1 hd0 hT0
  generalize hgδ : d.pdf q = δ₀ at hd0 hT0
  have hpd : c.nmem (8 * d.k + q) = δ₀ := by rw [hS.pd_m q hq1, hgδ]
  have hAδ := hA.tri.A_lt _ hd0
  have hTA : d.Tm (d.A δ₀) = 0 := by rw [hA.tri.T_A _ hd0]; exact hT0
  obtain ⟨c₁, t₁, e₁, hw₁, g321, g363, g330, fr₁, hm₁, ho₁, rfl⟩ : ∃ c₁ t₁, Exec P W
      (block [.addN 321 320 320, .addN 334 9 1, .loadN 345 334, .addN 334 8 345,
        .loadN 363 334, .copyN 330 363]) c c₁ t₁ ∧ WordsBounded W c₁ ∧
      c₁.nreg 321 = 2 * d.tot ∧ c₁.nreg 363 = δ₀ ∧ c₁.nreg 330 = δ₀ ∧
      (∀ r, r < 321 ∨ (321 < r ∧ r < 330) ∨ (330 < r ∧ r < 334) ∨ (334 < r ∧ r < 345) ∨
        (345 < r ∧ r < 363) ∨ 363 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.output = c.output ∧ t₁ = 6 := by
    exec_block
    all_goals try (config_simp; simp only [hS.r320, h9, h1, h8, hgq, hpd]; omega)
    refine ⟨‹_›, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try simp only [hS.r320, h9, h1, h8, hgq, hpd]
    · omega
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
  have hS₁ := hS.keep hw₁ (fun r hr => fr₁ r (by omega)) hm₁
  obtain ⟨c₂, t₂, e₂, ht₂, hS₂, fr₂, g331, ho₂⟩ := ivm_exec (P := P) hA c₁ hS₁
    (by rw [g330]; exact hd0) (by rw [g330]; exact hT0)
  rw [g330] at g331
  have hIle := IvM_le hA hd0
  have g3 : c₂.nreg 3 = 3 := (fr₂ 3 (by omega)).trans ((fr₁ 3 (by omega)).trans h3)
  obtain ⟨c₃, e₃, g362, fr₃, hm₃, ho₃, hw₃⟩ := step_mul (P := P) c₂ hS₂.wb 362 331 3
    (by rw [g331, g3]; omega)
  rw [g331, g3] at g362
  have hS₃ := hS₂.keep hw₃ (fun r hr => fr₃ r (by omega)) hm₃
  have keep₃ : ∀ r, r < 280 ∨ (292 ≤ r ∧ r ≤ 330) ∨ (346 < r ∧ r ≠ 362) → c₃.nreg r = c₁.nreg r :=
    fun r hr => by rw [fr₃ r (by omega), fr₂ r (by omega)]
  have k321 : c₃.nreg 321 = 2 * d.tot := (keep₃ 321 (by omega)).trans g321
  have k363 : c₃.nreg 363 = δ₀ := (keep₃ 363 (by omega)).trans g363
  have k331 : c₃.nreg 331 = IvM d δ₀ := by rw [fr₃ 331 (by omega), g331]
  have k1 : c₃.nreg 1 = 1 := (keep₃ 1 (by omega)).trans ((fr₁ 1 (by omega)).trans h1)
  have k0 : c₃.nreg 0 = 0 := (keep₃ 0 (by omega)).trans ((fr₁ 0 (by omega)).trans h0)
  have ho3 : c₃.output = o := by rw [ho₃, ho₂, ho₁, ho]
  have hpre : ∀ s c' t', Exec P W s c₃ c' t' → Exec P W (.seq (block [.addN 321 320 320,
      .addN 334 9 1, .loadN 345 334, .addN 334 8 345, .loadN 363 334, .copyN 330 363]) <|
      .seq ivm <| .seq (.instr (.mulN 362 331 3)) s) c c' (6 + (t₂ + (1 + t'))) :=
    fun s c' t' ex => .seq e₁ (.seq e₂ (.seq e₃ ex))
  have hc3 := hw₃
  unfold mwstart
  by_cases h1st : 2 * d.tot < 3 * IvM d δ₀
  · obtain ⟨c₄, t₄, e₄, hI₄, rfl⟩ : ∃ c₄ t₄, Exec P W
        (block [.copyN 350 363, .copyN 351 331, .copyN 352 0]) c₃ c₄ t₄ ∧ MWI d e W o c₄ ∧
        t₄ = 3 := by
      have hc := hc3
      exec_block
      refine ⟨⟨hS₃.keep ‹_› (fun r hr => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl) rfl, ?_, ho3,
        Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩⟩, rfl⟩
      all_goals config_simp
      all_goals try simp only [k321, k363, k331, k0]
      all_goals first | exact hd0 | exact hT0 | exact h1st | skip
    exact ⟨c₄, _, hpre _ _ _ (.ifLtN_true (by rw [k321, g362]; omega) e₄), hI₄, by omega⟩
  · -- the other side
    obtain ⟨c₄, e₄, g330', fr₄, hm₄, ho₄, hw₄⟩ := step_load (P := P) c₃ hw₃ 330 363
    rw [k363, hm₃, hS₂.A_m _ hd0] at g330'
    have hS₄ := hS₃.keep hw₄ (fun r hr => fr₄ r (by omega)) hm₄
    obtain ⟨c₅, e₅, g364, fr₅, hm₅, ho₅, hw₅⟩ := step_copy (P := P) c₄ hw₄ 364 330
    rw [g330'] at g364
    have hS₅ := hS₄.keep hw₅ (fun r hr => fr₅ r (by omega)) hm₅
    obtain ⟨c₆, t₆, e₆, ht₆, hS₆, fr₆, g331', ho₆⟩ := ivm_exec (P := P) hA c₅ hS₅
      (by rw [fr₅ 330 (by omega), g330']; exact hAδ)
      (by rw [fr₅ 330 (by omega), g330']; exact hTA)
    rw [fr₅ 330 (by omega), g330'] at g331'
    have hOle := IvM_le hA hAδ
    have g3' : c₆.nreg 3 = 3 := by
      rw [fr₆ 3 (by omega), fr₅ 3 (by omega), fr₄ 3 (by omega), keep₃ 3 (by omega), fr₁ 3 (by omega), h3]
    obtain ⟨c₇, e₇, g362', fr₇, hm₇, ho₇, hw₇⟩ := step_mul (P := P) c₆ hS₆.wb 362 331 3
      (by rw [g331', g3']; omega)
    rw [g331', g3'] at g362'
    have hS₇ := hS₆.keep hw₇ (fun r hr => fr₇ r (by omega)) hm₇
    have keep₇ : ∀ r, r < 280 ∨ (292 ≤ r ∧ r < 330) ∨ (346 < r ∧ r ≠ 362 ∧ r ≠ 364) →
        c₇.nreg r = c₃.nreg r := fun r hr => by
      rw [fr₇ r (by omega), fr₆ r (by omega), fr₅ r (by omega), fr₄ r (by omega)]
    have j321 : c₇.nreg 321 = 2 * d.tot := (keep₇ 321 (by omega)).trans k321
    have j363 : c₇.nreg 363 = δ₀ := (keep₇ 363 (by omega)).trans k363
    have j364 : c₇.nreg 364 = d.A δ₀ := by rw [fr₇ 364 (by omega), fr₆ 364 (by omega), g364]
    have j331 : c₇.nreg 331 = IvM d (d.A δ₀) := by rw [fr₇ 331 (by omega), g331']
    have j1 : c₇.nreg 1 = 1 := (keep₇ 1 (by omega)).trans k1
    have j0 : c₇.nreg 0 = 0 := (keep₇ 0 (by omega)).trans k0
    have ho7 : c₇.output = o := by rw [ho₇, ho₆, ho₅, ho₄, ho3]
    have hc7 := hw₇
    have hrest : ∀ s c' t', Exec P W s c₇ c' t' → Exec P W (.seq (block [.loadN 330 363,
        .copyN 364 330]) <| .seq ivm <| .seq (.instr (.mulN 362 331 3)) s) c₃ c'
        ((1 + (1 + 0)) + (t₆ + (1 + t'))) :=
      fun s c' t' ex => .seq (Exec.block_cons e₄ (Exec.block_cons e₅ (Exec.block_nil hw₅)))
        (.seq e₆ (.seq e₇ ex))
    by_cases h2nd : 2 * d.tot < 3 * IvM d (d.A δ₀)
    · obtain ⟨c₈, t₈, e₈, hI₈, rfl⟩ : ∃ c₈ t₈, Exec P W
          (block [.copyN 350 364, .copyN 351 331, .copyN 352 0]) c₇ c₈ t₈ ∧ MWI d e W o c₈ ∧
          t₈ = 3 := by
        have hc := hc7
        exec_block
        refine ⟨⟨hS₇.keep ‹_› (fun r hr => by
            config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl) rfl, ?_, ho7,
          Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩⟩, rfl⟩
        all_goals config_simp
        all_goals try simp only [j321, j364, j331, j0]
        all_goals first | exact hAδ | exact hTA | exact h2nd | skip
      exact ⟨c₈, _, hpre _ _ _ (.ifLtN_false (by rw [k321, g362]; omega)
        (hrest _ _ _ (.ifLtN_true (by rw [j321, g362']; omega) e₈))), hI₈, by omega⟩
    · obtain ⟨c₈, t₈, e₈, hI₈, rfl⟩ : ∃ c₈ t₈, Exec P W
          (block [.copyN 353 363, .copyN 352 1]) c₇ c₈ t₈ ∧ MWI d e W o c₈ ∧ t₈ = 2 := by
        have hc := hc7
        exec_block
        refine ⟨⟨hS₇.keep ‹_› (fun r hr => by
            config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl) rfl, ?_, ho7,
          Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩⟩, rfl⟩
        all_goals config_simp
        all_goals try simp only [j321, j363, j1]
        all_goals first | exact hd0 | exact hT0 | omega | skip
      exact ⟨c₈, _, hpre _ _ _ (.ifLtN_false (by rw [k321, g362]; omega)
        (hrest _ _ _ (.ifLtN_false (by rw [j321, g362']; omega) e₈))), hI₈, by omega⟩

/-- **The walk.** From the state holding the coded map, the search, the strict inside weights
`J`, the vertex arrays and the total `tot` (`WSm`), with the assumptions `WAm` and the rules
`MWH`, the walk ends within `(50 L + 160) (k + 1) + 50 L + 142` steps with a dart `r353` off the
tree whose strict inside and strict outside weigh at most `2/3` of `tot` (`MGood`). -/
theorem mwalk_exec (hA : WAm d e W) (hH : MWH d sz Bs) (c : Config) (hS : WSm d e W c)
    (ho : c.output = o) (hq1 : c.nmem (9 * d.k + 1) < d.k)
    (hd0 : d.pdf (c.nmem (9 * d.k + 1)) < 3 * d.k)
    (hT0 : d.Tm (d.pdf (c.nmem (9 * d.k + 1))) = 0) :
    ∃ c' t, Exec P W mwalk c c' t ∧ t ≤ (50 * e.L + 160) * (d.k + 1) + 50 * e.L + 142 ∧
      WSm d e W c' ∧ c'.output = o ∧ MGood d c' := by
  obtain ⟨c₁, t₁, e₁, hI₁, ht₁⟩ := mwstart_exec (P := P) hA c hS ho hq1 hd0 hT0
  obtain ⟨c', t, ex, hI', hn, ht⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 352) (b := 1)
    (body := mwbody) (MWI d e W o)
    (fun c => if c.nreg 352 = 0 then (50 * e.L + 160) * (sz (c.nreg 350) + 1) else 0)
    (fun c h => h.ws.wb)
    (fun c hc hlt => by
      have hrun : MRun d c := by
        rcases hc.st with h | h
        · exact h
        · rw [h.1, hc.ws.regs.2.1] at hlt; omega
      obtain ⟨c₂, t₂, e₂, hI₂, hΦ⟩ := mwbody_exec (P := P) hA hH c hc hrun
      exact ⟨c₂, t₂, e₂, hI₂, by rw [ite_eq_left_of_eq_true _ _ (eq_true hrun.1)]; exact hΦ⟩) hI₁
  have hgood : MGood d c' := by
    rcases hI'.st with h | h
    · rw [h.1, hI'.ws.regs.2.1] at hn; omega
    · exact h
  refine ⟨c', t₁ + t, .seq e₁ ex, ?_, hI'.ws, hI'.out, hgood⟩
  have : (if c₁.nreg 352 = 0 then (50 * e.L + 160) * (sz (c₁.nreg 350) + 1) else 0) ≤
      (50 * e.L + 160) * (d.k + 1) := by
    split_ifs with h
    · rcases hI₁.st with h' | h'
      · exact Nat.mul_le_mul_left _ (by have := hH.sz_le _ h'.2.1; omega)
      · rw [h'.1] at h; omega
    · omega
  omega

end walk

end MillerProg

end PlanarSeparator
