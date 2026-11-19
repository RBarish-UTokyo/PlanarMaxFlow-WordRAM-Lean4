module

public import PlanarSeparator.Machine.SplitPass

/-!
# The split of a node on the machine: the front

The first part of the machine form of `PlanarSeparator.SepRoutine.splitW` for the square of
`G`: from the state between splits `SWB` and the sorted list of a vertex set `U`, the worklist
state `DCore` of the division of `U ∪ B` (`B` the boundary of `U` in the square) with the weights
`spMu` and the bound `spL`, ready for `divLoop`.

* `Stmt.wok`, `wr_of_wok`: the registers written by a statement, checked by `decide`.
* `SWB`: the state between splits (`SBase` with the weights `0`, the arrays of the split).
* **`swFront_exec`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace WordRAM.Machine.Stmt

/-! ### The registers written by a statement -/

/-- Every register written by the statement satisfies `p`. -/
def wok (p : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => (i.wr i.wreg == false) || p i.wreg
  | .seq s t => wok p s && wok p t
  | .ifLtN _ _ s t | .ifLtR _ _ s t => wok p s && wok p t
  | .whileLtN _ _ s | .whileLtR _ _ s => wok p s

theorem wreg_of_wr' {i : Instr} {r : ℕ} (h : i.wr r = true) : i.wreg = r := by
  cases i <;> simp_all [Instr.wr, Instr.wreg]

theorem wr_of_wok {p : ℕ → Bool} {s : Stmt} (hs : s.wok p = true) {r : ℕ} (hr : p r = false) :
    s.wr r = false := by
  induction s with
  | skip => rfl
  | instr i =>
    simp only [wok, Bool.or_eq_true, beq_iff_eq] at hs
    simp only [Stmt.wr]
    by_contra h
    have h' : i.wr r = true := by simpa using h
    have e := wreg_of_wr' h'
    rcases hs with hs | hs
    · rw [e] at hs; rw [hs] at h'; exact Bool.false_ne_true h'
    · rw [e] at hs; rw [hs] at hr; exact absurd hr (by simp)
  | seq s t ihs iht =>
    simp only [wok, Bool.and_eq_true] at hs; simp [Stmt.wr, ihs hs.1, iht hs.2]
  | ifLtN _ _ s t ihs iht =>
    simp only [wok, Bool.and_eq_true] at hs; simp [Stmt.wr, ihs hs.1, iht hs.2]
  | ifLtR _ _ s t ihs iht =>
    simp only [wok, Bool.and_eq_true] at hs; simp [Stmt.wr, ihs hs.1, iht hs.2]
  | whileLtN _ _ s ih => exact ih hs
  | whileLtR _ _ s ih => exact ih hs

end WordRAM.Machine.Stmt

namespace PlanarSeparator.Piece

open WordRAM WordRAM.Machine

theorem Exec.nreg_of_wok {P : Input} {W : ℕ} {p : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (e : Exec P W s c c' k) (hs : s.wok p = true) {r : ℕ} (hr : p r = false) :
    c'.nreg r = c.nreg r := Exec.nreg_of_wr e (Stmt.wr_of_wok hs hr)

end PlanarSeparator.Piece

namespace PlanarSeparator

namespace Piece

open Finset NestedDissection WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {W : ℕ} {P : Input}

/-! ### The state between splits -/

variable (G) in
/-- **The state between splits**: `SBase` with the weights `0` and the bound `M ≥ 40 (N² + 1)`;
the flag array `aS`, the name array `aP`, the list area `aV`, the frame stack `aF` of the
division; the zones `aZ`, the counts `aCW`, `aCB`, the seen names `aSn` and the marks `aJ` of
the balanced split, all zero. -/
structure SWB (R : Kasteleyn.RotationSystem G) (Z W M aS aP aV aF aZ aCW aCB aSn aJ : ℕ)
    (c : Config) : Prop where
  base : SBase G R (fun _ => 0) Z W M c
  rS : c.nreg 1310 = aS
  rP : c.nreg 1311 = aP
  rV : c.nreg 1312 = aV
  rF : c.nreg 1313 = aF
  rZ : c.nreg 1390 = aZ
  rCW : c.nreg 1391 = aCW
  rCB : c.nreg 1392 = aCB
  rSn : c.nreg 1393 = aSn
  rJ : c.nreg 1394 = aJ
  lay1 : c.nreg 1203 + N ≤ aS
  lay2 : aS + N ≤ aP
  lay3 : aP + N ≤ aV
  lay4 : aV + N ≤ aF
  lay5 : aF + 3 * (N + 1) ≤ aZ
  lay6 : aZ + N ≤ aCW
  lay7 : aCW + N ≤ aCB
  lay8 : aCB + N ≤ aSn
  lay9 : aSn + N ≤ aJ
  lay10 : aJ + N ≤ W
  hMN : M + N ≤ W
  hM : 40 * (N * N + 1) ≤ M
  zZ : ∀ x < N, c.nmem (aZ + x) = 0
  zCW : ∀ x < N, c.nmem (aCW + x) = 0
  zCB : ∀ x < N, c.nmem (aCB + x) = 0
  zSn : ∀ x < N, c.nmem (aSn + x) = 0
  zJ : ∀ x < N, c.nmem (aJ + x) = 0

/-! ### The front -/

/-- The registers written by the front. -/
def pA (r : ℕ) : Bool :=
  r == 1201 || (1205 ≤ r && r ≤ 1216) || (1314 ≤ r && r ≤ 1326) || r == 1389 ||
    (1395 ≤ r && r ≤ 1415)

/-- The constants of the weights and the bound. -/
def swConst : Stmt := .seq (.ifLtN 1404 1001 (.instr (.copyN 1407 1001)) (.instr (.copyN 1407 1404)))
  (block [.constN 1405 20, .mulN 1405 1405 1407, .constN 1406 20, .mulN 1406 1406 1421,
    .mulN 1314 1421 1407, .constN 1389 2])

/-- The first frame of the division. -/
def swFrame : Stmt := block [.storeN 1313 1312, .addN 1411 1313 1001, .storeN 1411 1403,
  .addN 1411 1411 1001, .storeN 1411 1403, .copyN 1315 1001]

/-- **The front** of the split of the node `U` (list at `nreg 1420`, size `nreg 1421`). -/
def swFront : Stmt :=
  .seq (block [.copyN 1321 1420, .copyN 1322 1421]) (.seq dCopy (.seq sqP1 (.seq sqP2
    (.seq spN1 (.seq (.instr (.copyN 1201 1396)) (.seq sqP2 (.seq spN2 (.seq (spClr 1310)
    (.seq (spClr 1311) (.seq swConst (.seq spWt swFrame)))))))))))

/-- The worklist of the division of `D` (one frame, list at `aV`). -/
def swFr (D : Finset (Fin N)) (aV : ℕ) : DFr N :=
  ⟨1, fun _ => D, fun _ => #D, fun _ => aV, ⟨fun _ => 0, fun _ => 0⟩⟩

theorem swFront_wok : swFront.wok pA = true := by decide

set_option maxHeartbeats 4000000 in
/-- **The front of the split**: from the state between splits and the sorted list of `U` at
`aW` (`nreg 1420`, size in `1421`), the worklist state of the division of
`D = N[N[U]] = U ∪ B` (`B` the boundary of `U` in the square) with the weights `spMu` and the
bound `spL`; the zones `1` on `U`, `2` on `D \ U`; `#B` in `1404`. -/
theorem swFront_exec {R : Kasteleyn.RotationSystem G} {Z M aS aP aV aF aZ aCW aCB aSn aJ aW : ℕ}
    {c : Config} (hc : SWB G R Z W M aS aP aV aF aZ aCW aCB aSn aJ c) {U : Finset (Fin N)}
    (h00 : c.nreg 1420 = aW) (h01 : c.nreg 1421 = #U)
    (hl : ∀ l < #U, c.nmem (aW + l) = lv U l) (l1 : aJ + N ≤ aW) (l2 : aW + N ≤ W) :
    ∃ c' k, Exec P W swFront c c' k ∧ k ≤ 130 * N + 60 + 22 * ∑ v ∈ closedNbhd G U, G.degree v ∧
      DCore G R (spMu (square G) U) Z W M aS aP aV aF (spL (square G) U)
        #(closedNbhd G (closedNbhd G U)) c' (swFr (closedNbhd G (closedNbhd G U)) aV) c' ∧
      c'.nreg 1315 = 1 ∧
      (∀ x < N, c'.nmem (aZ + x) =
        if x ∈ UN U then 1 else if x ∈ UN (closedNbhd G (closedNbhd G U)) then 2 else 0) ∧
      c'.nreg 1404 = #(bdry (square G) U) ∧ c'.nreg 1389 = 2 ∧
      (∀ r, pA r = false → c'.nreg r = c.nreg r) ∧
      (∀ a, aZ + N ≤ a → c'.nmem a = c.nmem a) ∧
      c'.output = c.output ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem := by
  have hb := hc.base
  have hw := hb.wb
  have := hb.lU; have := hb.lC; have := hb.lQ; have := hb.lW; have := hb.lS; have := hb.l0
  have := hb.l1; have := hb.l2; have := hb.l3; have := hb.l4; have := hb.l5; have := hb.l6
  have := hb.l7; have := hb.lA; have := hb.lB; have := hb.lF; have := hb.lV
  have := hc.lay1; have := hc.lay2; have := hc.lay3; have := hc.lay4; have := hc.lay5
  have := hc.lay6; have := hc.lay7; have := hc.lay8; have := hc.lay9; have := hc.lay10
  have := hc.hMN; have := hc.hM; have := hb.sw
  have hUN := card_le_N U
  set C := closedNbhd G U with hCdef
  set D := closedNbhd G C with hDdef
  have hUC : U ⊆ C := subset_closedNbhd U
  have hCD : C ⊆ D := subset_closedNbhd C
  have hCN := card_le_N C
  have hDN := card_le_N D
  set a0 := c.nreg 1200 with ha0
  set aFl := c.nreg 1202 with haFl
  have hNN : N ≤ N * N + 1 := Nat.le_succ_of_le (Nat.le_mul_self N)
  have hW40 : 40 * (N * N + 1) ≤ W := by omega
  -- the copy of the list
  obtain ⟨c₀, k₀, e₀, hk₀, hw₀, g21, g22, gm₀⟩ : ∃ c₀ k₀, Exec P W
      (block [.copyN 1321 1420, .copyN 1322 1421]) c c₀ k₀ ∧ k₀ = 2 ∧ WordsBounded W c₀ ∧
      c₀.nreg 1321 = aW ∧ c₀.nreg 1322 = #U ∧ c₀.nmem = c.nmem := by
    exec_block
    exact ⟨rfl, ‹_›, by config_simp; exact h00, by config_simp; exact h01, rfl⟩
  have K₀ : ∀ r, pA r = false → c₀.nreg r = c.nreg r := fun r hr =>
    Exec.nreg_of_wok e₀ (by decide) hr
  obtain ⟨c₁, k₁, e₁, hw₁, g01₁, gl₁, gm₁, -, hk₁⟩ := dCopy_exec (P := P) (U := U) (a0 := a0) hw₀
    (by rw [K₀ 1001 (by decide)]; exact hb.one) g21 g22 (K₀ 1200 (by decide))
    (fun j hj => by rw [gm₀]; exact hl j hj) (Or.inr (by omega)) (by omega) (by omega)
  have K₁ : ∀ r, pA r = false → c₁.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₁ (by decide) hr, K₀ r hr]
  have M₁ : ∀ a, (a < a0 ∨ a0 + N ≤ a) → c₁.nmem a = c.nmem a := fun a ha => by
    rw [gm₁ a ha, gm₀]
  -- the flags `2` on `U`
  obtain ⟨c₂, k₂, e₂, hw₂, -, hf₂, gm₂, -, hk₂⟩ := sqP1_exec (P := P) (U := U) (a0 := a0) (aF := aFl) hw₁ (by omega)
    (by rw [K₁ 1001 (by decide)]; exact hb.one) (K₁ 1200 (by decide)) (K₁ 1202 (by decide))
    g01₁ gl₁ (by omega) (by omega)
  have K₂ : ∀ r, pA r = false → c₂.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₂ (by decide) hr, K₁ r hr]
  have M₂ : ∀ a, (a < a0 ∨ a0 + N ≤ a) → (a < aFl ∨ aFl + N ≤ a) → c₂.nmem a = c.nmem a :=
    fun a h1 h2 => by rw [gm₂ a h2, M₁ a h1]
  have g01₂ : c₂.nreg 1201 = #U := by rw [Exec.nreg_of_wr e₂ (by decide)]; exact g01₁
  have gl₂ : ∀ l < #U, c₂.nmem (a0 + l) = lv U l := fun l hl' => by
    rw [gm₂ _ (Or.inl (by omega))]; exact gl₁ l hl'
  have hF₂ : ∀ x < N, c₂.nmem (aFl + x) = if x ∈ UN U then 2 else 0 := fun x hx => by
    rw [hf₂ x hx, M₁ _ (Or.inr (by omega)), hb.fz x hx]
  have FL : ∀ c' : Config, WordsBounded W c' → (∀ r, pA r = false → c'.nreg r = c.nreg r) →
      (∀ a, a < a0 → c'.nmem a = c.nmem a) → FLay G W c' a0 aFl := fun c' hw' K M => by
    have e10 := K 1010 (by decide); have e11 := K 1011 (by decide)
    have e12 := K 1012 (by decide)
    have g := gofs_le G
    exact { wb := hw', one := by rw [K 1001 (by decide)]; exact hb.one
            h00 := K 1200 (by decide), h02 := K 1202 (by decide)
            l0 := by rw [e10, e11]; exact hb.l0
            l1 := by rw [e11, e12]; exact hb.l1
            l2 := by rw [e12]; omega
            lB := by omega, lF := by omega
            ofs := fun v hv => by
              rw [e10, M _ (by have := g v; omega)]; exact hb.ofs v hv
            tl := fun g' hg => by rw [e11, M _ (by omega)]; exact hb.tl g' hg
            rv := fun g' hg => by rw [e12, M _ (by omega)]; exact hb.rv g' hg }
  -- the flags `1` on `C \ U`
  obtain ⟨c₃, k₃, e₃, hw₃, -, hf₃, gm₃, hk₃⟩ := sqP2_exec (P := P) (U := U)
    (FL c₂ hw₂ K₂ (fun a ha => M₂ a (Or.inl ha) (Or.inl (by omega)))) (by omega) g01₂ gl₂ hF₂
  have K₃ : ∀ r, pA r = false → c₃.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₃ (by decide) hr, K₂ r hr]
  have M₃ : ∀ a, (a < a0 ∨ a0 + N ≤ a) → (a < aFl ∨ aFl + N ≤ a) → c₃.nmem a = c.nmem a :=
    fun a h1 h2 => by rw [gm₃ a h2, M₂ a h1 h2]
  -- the closed neighbourhood
  obtain ⟨c₄, k₄, e₄, hw₄, g96₄, gl₄, hf₄, hz₄, gm₄, -, hk₄⟩ := spN1_exec (P := P) (a0 := a0) (aF := aFl) (aZ := aZ) hw₃ hUC
    (by rw [K₃ 1001 (by decide)]; exact hb.one) (by rw [K₃ 0 (by decide)]; exact hb.r0)
    (by rw [K₃ 1204 (by decide)]; exact hb.nN) (K₃ 1200 (by decide)) (K₃ 1202 (by decide))
    (by rw [K₃ 1390 (by decide)]; exact hc.rZ) hf₃
    (fun x hx => by rw [M₃ _ (Or.inr (by omega)) (Or.inr (by omega))]; exact hc.zZ x hx)
    (by omega) (by omega) (by omega) (by omega)
  have K₄ : ∀ r, pA r = false → c₄.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₄ (by decide) hr, K₃ r hr]
  have M₄ : ∀ a, (a < a0 ∨ aZ + N ≤ a) → c₄.nmem a = c.nmem a := fun a ha => by
    rw [gm₄ a ha]; rcases ha with ha | ha
    · exact M₃ a (Or.inl ha) (Or.inl (by omega))
    · exact M₃ a (Or.inr (by omega)) (Or.inr (by omega))
  -- the flags of the second neighbourhood
  obtain ⟨c₅, k₅, e₅, hk₅, hw₅, g01₅, gm₅⟩ : ∃ c₅ k₅, Exec P W (.instr (.copyN 1201 1396)) c₄ c₅ k₅ ∧
      k₅ = 1 ∧ WordsBounded W c₅ ∧ c₅.nreg 1201 = #C ∧ c₅.nmem = c₄.nmem := by
    refine spec_instr (Exec.copyN hw₄ _ _) fun hw' => ?_
    exact ⟨rfl, hw', by config_simp; exact g96₄, rfl⟩
  have K₅ : ∀ r, pA r = false → c₅.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₅ (by decide) hr, K₄ r hr]
  obtain ⟨c₆, k₆, e₆, hw₆, -, hf₆, gm₆, hk₆⟩ := sqP2_exec (P := P) (U := C)
    (FL c₅ hw₅ K₅ (fun a ha => by rw [gm₅, M₄ a (Or.inl ha)])) (by omega) g01₅
    (fun l hl' => by rw [gm₅]; exact gl₄ l hl') (fun x hx => by rw [gm₅]; exact hf₄ x hx)
  have K₆ : ∀ r, pA r = false → c₆.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₆ (by decide) hr, K₅ r hr]
  -- the list of `D`, the zones
  obtain ⟨c₇, k₇, e₇, hw₇, g03₇, g04₇, gl₇, hf₇, hz₇, gm₇, -, hk₇⟩ := spN2_exec (P := P) (aF := aFl) (aV := aV) (aZ := aZ) hw₆
    hUC hCD (by rw [K₆ 1001 (by decide)]; exact hb.one) (by rw [K₆ 0 (by decide)]; exact hb.r0)
    (by rw [K₆ 1204 (by decide)]; exact hb.nN) (K₆ 1202 (by decide))
    (by rw [K₆ 1312 (by decide)]; exact hc.rV) (by rw [K₆ 1390 (by decide)]; exact hc.rZ) hf₆
    (fun x hx => by rw [gm₆ _ (Or.inr (by omega)), gm₅]; exact hz₄ x hx)
    (by omega) (by omega) (by omega) (by omega)
  have K₇ : ∀ r, pA r = false → c₇.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₇ (by decide) hr, K₆ r hr]
  have M₇ : ∀ a, (a < a0 ∨ aZ + N ≤ a) → c₇.nmem a = c.nmem a := fun a ha => by
    rw [gm₇ a (by omega) (by omega) (by omega), gm₆ a (by omega), gm₅, M₄ a ha]
  -- the zeros on the flag and name arrays
  obtain ⟨c₈, k₈, e₈, hw₈, hz₈, gm₈, -, hk₈⟩ := spClr_exec (P := P) (N := N) (r := 1310) (b := aS) hw₇ (by decide)
    (by decide) (by rw [K₇ 1001 (by decide)]; exact hb.one)
    (by rw [K₇ 0 (by decide)]; exact hb.r0) (by rw [K₇ 1204 (by decide)]; exact hb.nN)
    (by rw [K₇ 1310 (by decide)]; exact hc.rS) (by omega)
  have K₈ : ∀ r, pA r = false → c₈.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₈ (by decide) hr, K₇ r hr]
  obtain ⟨c₉, k₉, e₉, hw₉, hz₉, gm₉, -, hk₉⟩ := spClr_exec (P := P) (N := N) (r := 1311) (b := aP) hw₈ (by decide)
    (by decide) (by rw [K₈ 1001 (by decide)]; exact hb.one)
    (by rw [K₈ 0 (by decide)]; exact hb.r0) (by rw [K₈ 1204 (by decide)]; exact hb.nN)
    (by rw [K₈ 1311 (by decide)]; exact hc.rP) (by omega)
  have K₉ : ∀ r, pA r = false → c₉.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₉ (by decide) hr, K₈ r hr]
  have M₉ : ∀ a, (a < aS ∨ aP + N ≤ a) → c₉.nmem a = c₇.nmem a := fun a ha => by
    rw [gm₉ a (by omega), gm₈ a (by omega)]
  have g04₉ : c₉.nreg 1404 = #(D \ U) := by
    rw [Exec.nreg_of_wr e₉ (by decide), Exec.nreg_of_wr e₈ (by decide)]; exact g04₇
  have g03₉ : c₉.nreg 1403 = #D := by
    rw [Exec.nreg_of_wr e₉ (by decide), Exec.nreg_of_wr e₈ (by decide)]; exact g03₇
  -- the constants
  have hbd : bdry (square G) U = D \ U := bdry_square_eq U
  have hbN : #(D \ U) ≤ N := card_le_N _
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, hw₁₀, g05, g06, g14, g89, gm₁₀⟩ : ∃ c₁₀ k₁₀,
      Exec P W swConst c₉ c₁₀ k₁₀ ∧ k₁₀ ≤ 9 ∧ WordsBounded W c₁₀ ∧
      c₁₀.nreg 1405 = 20 * max #(D \ U) 1 ∧ c₁₀.nreg 1406 = 20 * #U ∧
      c₁₀.nreg 1314 = #U * max #(D \ U) 1 ∧ c₁₀.nreg 1389 = 2 ∧ c₁₀.nmem = c₉.nmem := by
    have r1 : c₉.nreg 1001 = 1 := by rw [K₉ 1001 (by decide)]; exact hb.one
    have r01 : c₉.nreg 1421 = #U := by rw [K₉ 1421 (by decide)]; exact h01
    have hmx : max #(D \ U) 1 ≤ N + 1 := max_le (by omega) (by omega)
    have h20 : 20 * (N + 1) ≤ W := by omega
    have hmm : #U * max #(D \ U) 1 ≤ N * (N + 1) := Nat.mul_le_mul hUN hmx
    unfold swConst
    refine spec_seq ?_
    by_cases hb0 : #(D \ U) < 1
    · refine spec_ifLtN_true (by rw [g04₉, r1]; exact hb0) ?_
      refine spec_instr (Exec.copyN hw₉ _ _) fun hw' => ?_
      have hm1 : max #(D \ U) 1 = 1 := by omega
      exec_block
      · omega
      · config_simp; rw [r1]; omega
      · omega
      · config_simp; rw [r01]; omega
      · config_simp; rw [r01, r1, Nat.mul_one]; omega
      · omega
      · refine ⟨by omega, ‹_›, by config_simp; rw [r1, hm1], by config_simp; rw [r01],
          by config_simp; rw [r01, r1, hm1], by config_simp, rfl⟩
    · refine spec_ifLtN_false (by rw [g04₉, r1]; exact hb0) ?_
      refine spec_instr (Exec.copyN hw₉ _ _) fun hw' => ?_
      have hm1 : max #(D \ U) 1 = #(D \ U) := by omega
      exec_block
      · omega
      · config_simp; rw [g04₉]; omega
      · omega
      · config_simp; rw [r01]; omega
      · config_simp; rw [r01, g04₉]; exact (Nat.mul_le_mul hUN hbN).trans (by omega)
      · omega
      · refine ⟨by omega, ‹_›, by config_simp; rw [g04₉, hm1], by config_simp; rw [r01],
          by config_simp; rw [r01, g04₉, hm1], by config_simp, rfl⟩
  have K₁₀ : ∀ r, pA r = false → c₁₀.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₁₀ (by decide) hr, K₉ r hr]
  have g04₁₀ : c₁₀.nreg 1404 = #(D \ U) := by rw [Exec.nreg_of_wr e₁₀ (by decide)]; exact g04₉
  have g03₁₀ : c₁₀.nreg 1403 = #D := by rw [Exec.nreg_of_wr e₁₀ (by decide)]; exact g03₉
  -- the weights
  have hz₁₀ : ∀ x < N, c₁₀.nmem (aZ + x) =
      if x ∈ UN U then 1 else if x ∈ UN D then 2 else 0 := fun x hx => by
    rw [gm₁₀, M₉ _ (Or.inr (by omega))]; exact hz₇ x hx
  obtain ⟨c₁₁, k₁₁, e₁₁, hw₁₁, hwt₁₁, gm₁₁, -, hk₁₁⟩ := spWt_exec (P := P) (aw := c.nreg 1014) (aZ := aZ) hw₁₀ (X := U) (Y := D)
    (by rw [K₁₀ 1001 (by decide)]; exact hb.one) (by rw [K₁₀ 0 (by decide)]; exact hb.r0)
    (by rw [K₁₀ 1204 (by decide)]; exact hb.nN) (K₁₀ 1014 (by decide))
    (by rw [K₁₀ 1390 (by decide)]; exact hc.rZ) g05 g06 hz₁₀ (by omega) (by omega)
  have K₁₁ : ∀ r, pA r = false → c₁₁.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₁₁ (by decide) hr, K₁₀ r hr]
  have g04₁₁ : c₁₁.nreg 1404 = #(D \ U) := by rw [Exec.nreg_of_wr e₁₁ (by decide)]; exact g04₁₀
  have g03₁₁ : c₁₁.nreg 1403 = #D := by rw [Exec.nreg_of_wr e₁₁ (by decide)]; exact g03₁₀
  have g14₁₁ : c₁₁.nreg 1314 = #U * max #(D \ U) 1 := by
    rw [Exec.nreg_of_wr e₁₁ (by decide)]; exact g14
  have g89₁₁ : c₁₁.nreg 1389 = 2 := by rw [Exec.nreg_of_wr e₁₁ (by decide)]; exact g89
  -- the first frame
  obtain ⟨c', k₁₂, e₁₂, hk₁₂, hw', f0, f1, f2, g15, g04', g14', g89', gm'⟩ : ∃ c' k₁₂,
      Exec P W swFrame c₁₁ c' k₁₂ ∧ k₁₂ = 6 ∧ WordsBounded W c' ∧
      c'.nmem aF = aV ∧ c'.nmem (aF + 1) = #D ∧ c'.nmem (aF + 2) = #D ∧ c'.nreg 1315 = 1 ∧
      c'.nreg 1404 = #(D \ U) ∧ c'.nreg 1314 = #U * max #(D \ U) 1 ∧ c'.nreg 1389 = 2 ∧
      (∀ a, (a < aF ∨ aF + 3 ≤ a) → c'.nmem a = c₁₁.nmem a) := by
    have r1 : c₁₁.nreg 1001 = 1 := by rw [K₁₁ 1001 (by decide)]; exact hb.one
    have r13 : c₁₁.nreg 1313 = aF := by rw [K₁₁ 1313 (by decide)]; exact hc.rF
    have r12 : c₁₁.nreg 1312 = aV := by rw [K₁₁ 1312 (by decide)]; exact hc.rV
    unfold swFrame
    exec_block
    · rw [r13, r1]; omega
    · config_simp; rw [r13, r1]; omega
    · refine ⟨rfl, ‹_›, ?_, ?_, ?_, by config_simp; exact r1, by config_simp; exact g04₁₁,
        by config_simp; exact g14₁₁, by config_simp; exact g89₁₁, fun a ha => ?_⟩
      · config_simp; rw [r13, r12, r1, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
          upd_same]
      · config_simp; rw [r13, r1, g03₁₁, upd_other _ _ _ (by omega), upd_same]
      · config_simp; rw [r13, r1, g03₁₁, show aF + 1 + 1 = aF + 2 by omega, upd_same]
      · config_simp; rw [r13, r1, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
          upd_other _ _ _ (by omega)]
  have e : Exec P W swFront c c' (k₀ + (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + (k₈ + (k₉ +
      (k₁₀ + (k₁₁ + k₁₂)))))))))))) :=
    .seq e₀ (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉
      (.seq e₁₀ (.seq e₁₁ e₁₂)))))))))))
  have K' : ∀ r, pA r = false → c'.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e swFront_wok hr]
  have rr : c'.rreg = c.rreg ∧ c'.rmem = c.rmem := Exec.real_of_noReal e (by decide)
  have ou : c'.output = c.output := Exec.output_of_ou e (by decide)
  have aw := c.nreg 1014
  have M' : ∀ a, (a < c.nreg 1014 ∨ c.nreg 1014 + N ≤ a) → (a < a0 ∨ aZ + N ≤ a) →
      a < aF ∨ aF + 3 ≤ a → c'.nmem a = c.nmem a := fun a h1 h2 h3 => by
    rw [gm' a h3, gm₁₁ a h1, gm₁₀, M₉ a (by omega), M₇ a h2]
  have hwI : ∀ v (hv : v < N), SepProg.wI (spMu (square G) U) v =
      if v ∈ UN U then 20 * max #(D \ U) 1 else if v ∈ UN D then 20 * #U else 0 := by
    intro v hv
    have e1 : v ∈ UN U ↔ (⟨v, hv⟩ : Fin N) ∈ U := by
      rw [mem_UN]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩
    have e2 : v ∈ UN D ↔ (⟨v, hv⟩ : Fin N) ∈ D := by
      rw [mem_UN]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩
    simp only [SepProg.wI, hv, dite_true, spMu, hbd, mem_sdiff, e1, e2]
    split_ifs <;> simp_all
  have hbase : SBase G R (spMu (square G) U) Z W M c' := hb.congr' hw'
    (fun r hr h1 => K' r (by unfold KeptS at hr; simp only [pA]; simp; omega))
    (fun a ha => by
      have := hb.lZ
      rcases ha with ha | ha | ha | ha | ha | ha
      · exact M' a (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      · exact M' a (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      · exact M' a (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      · exact M' a (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      · exact M' a (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      · obtain ⟨x, hx, rfl⟩ : ∃ x, x < N ∧ a = aFl + x := ⟨a - aFl, by omega, by omega⟩
        rw [gm' _ (Or.inl (by omega)), gm₁₁ _ (Or.inr (by omega)), gm₁₀,
          M₉ _ (Or.inl (by omega)), hf₇ x hx, hb.fz x hx])
    (fun v hv => by
      rw [gm' _ (Or.inl (by omega)), hwt₁₁ v hv, gm₁₀, M₉ _ (Or.inl (by omega)),
        M₇ _ (Or.inl (by omega)), hb.wt v hv, hwI v hv]
      simp [SepProg.wI])
    ((sum_spMu_le (square G) U).trans (by rw [Nat.mul_assoc]; have := hc.hM; omega)) rr.1 rr.2
  have hsum : ∑ v ∈ U, G.degree v ≤ ∑ v ∈ C, G.degree v := sum_le_sum_of_subset hUC
  refine ⟨c', _, e, by omega, ⟨hbase, by rw [K' 1310 (by decide)]; exact hc.rS,
    by rw [K' 1311 (by decide)]; exact hc.rP, by rw [K' 1312 (by decide)]; exact hc.rV,
    by rw [K' 1313 (by decide)]; exact hc.rF, by rw [g14']; simp [spL, hbd],
    by rw [K' 1203 (by decide)]; exact hc.lay1, hc.lay2, hc.lay3, hc.lay4, by omega, by omega,
    fun i hi => ?_, fun i j hij hj => by simp [swFr] at hj; omega, fun x hx => ?_,
    fun r _ => rfl, fun a _ => rfl, rfl⟩, g15, fun x hx => ?_, by rw [g04', hbd], g89', K',
    fun a ha => M' a (Or.inr (by omega)) (Or.inr ha) (Or.inr (by omega)), ou, rr.1, rr.2⟩
  · have hi0 : i = 0 := by simp [swFr] at hi; omega
    subst hi0
    simp only [swFr, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    refine ⟨f0, f1, f2, fun j hj => ?_, le_rfl, by omega, by omega⟩
    rw [gm' _ (Or.inl (by omega)), gm₁₁ _ (Or.inr (by omega)), gm₁₀,
      M₉ _ (Or.inr (by omega))]
    exact gl₇ j hj
  · simp only [swFr]
    refine ⟨?_, ?_⟩
    · rw [gm' _ (Or.inl (by omega)), gm₁₁ _ (Or.inr (by omega)), gm₁₀,
        gm₉ _ (Or.inl (by omega))]
      exact hz₈ x hx
    · rw [gm' _ (Or.inl (by omega)), gm₁₁ _ (Or.inr (by omega)), gm₁₀]
      exact hz₉ x hx
  · rw [gm' _ (Or.inr (by omega)), gm₁₁ _ (Or.inr (by omega))]
    exact hz₁₀ x hx

end Piece

end PlanarSeparator
