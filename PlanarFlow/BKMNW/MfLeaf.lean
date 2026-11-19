module

public import PlanarFlow.BKMNW.MfFrame
public import PlanarFlow.Machine.LeafFlow
public import PlanarFlow.BKMNW.LinLoops

/-!
# The test and the leaf solver of the max-flow driver on the concrete frames

On the frames of `MfFrame.lean`:

* **`mtProg`** (the test): `r2997 := mem (d + 2)`, the tag of the call (`0` at a leaf call);
  `mtProg_exec` (`3` steps).
* **`mlProg`** (the leaf solver, natural words): for every dart `i < m` of the piece map,
  `FL[i] := fvalN KR[i] KR[RV[i]] Z CP[i] CP[RV[i]]` (the decision of `leafSolve` from the ranks
  of the two ends: `Z + CP[i]` up in rank, `Z - CP[RV[i]]` down, `Z` otherwise); registers
  `6400 … 6414`; `mlProg_exec` (`25 m + 19` steps).
* `lrk_vimg` (the rank of a vertex of the piece map is the rank of the tail, the sources and the
  sinks off the holes), **`arunL_leaf_eq`** (the flow of a leaf call: `LeafFlow.fval` of the ranks
  of the ends and the capacities), `fvalN_eq`.
* **`mtProg_spec`**, **`mlProg_spec`**: the fields `test` and `leaf` of `MfSpecR` for the frame
  predicates `FInL`, `FOutL` (with `G = True`, `2 Z ≤ W`).

`LeafFlow.prog` (`cMach_leaf_exec`) computes the same decision with real-valued capacities and
flows in its own layout; `mlProg` is its natural-word version on the frame (flows with the offset
`Z`), so no real register is used.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-! ### The flow of a leaf call -/

/-- **The ranks on a piece map** are the ranks of the tails, the sources and the sinks being off
the holes. -/
lemma lrk_vimg {P : Finset D} {Hs : List (Finset V)} {σ : Perm D} (h : PieceInv M P Hs σ)
    {S T : Finset V} (hS : Disjoint S (hunion Hs)) (hT : Disjoint T (hunion Hs))
    {inst : DecidableEq (SVert σ (pdarts M P Hs))} (x : SDart (pdarts M P Hs)) :
    @lrk _ inst (vimg M σ _ S) (vimg M σ _ T) (vimg M σ _ (hunion Hs)) ((pmap h).tail x) =
      lrk S T (hunion Hs) (M.tail x.1) := by
  have e1 := mk_mem_vimg_iff h hS (x := x)
  have e2 := mk_mem_vimg_iff h hT (x := x)
  have e3 := mk_mem_vimg_hunion h (Hs' := Hs) (fun H hH => subset_hunion hH) (x := x)
  rw [pmap_tail]
  unfold lrk
  by_cases a1 : M.tail x.1 ∈ S
  · simp [e1.2 a1, a1]
  · have b1 : Quotient.mk _ x ∉ vimg M σ _ S := fun h => a1 (e1.1 h)
    by_cases a3 : M.tail x.1 ∈ hunion Hs
    · simp [b1, a1, e3.2 a3, a3]
    · have b3 : Quotient.mk _ x ∉ vimg M σ _ (hunion Hs) := fun h => a3 (e3.1 h)
      by_cases a2 : M.tail x.1 ∈ T
      · simp [b1, a1, b3, a3, e2.2 a2, a2]
      · have b2 : Quotient.mk _ x ∉ vimg M σ _ T := fun h => a2 (e2.1 h)
        simp [b1, a1, b3, a3, b2, a2]

/-- **The flow of a leaf call**, dart by dart: the decision `LeafFlow.fval` of the ranks of the
two ends and the capacities of the dart and of its reverse. -/
theorem arunL_leaf_eq (O : PlaneOracles.{w}) (u : D → ℤ) {S T : Finset V} {Q : Finset D}
    {Hs : List (Finset V)} {σ : Perm D} (h : CallOk M S T (.leaf Q, Hs, σ))
    (x : SDart (pdarts M Q Hs)) :
    arunL M O u S T (.leaf Q) Hs σ x =
      LeafFlow.fval (lrk S T (hunion Hs) (M.tail x.1))
        (lrk S T (hunion Hs) (M.tail (M.rev x.1))) (u x.1) (u (M.rev x.1)) := by
  have hp : PieceInv M Q Hs σ := h.pieceInv
  obtain ⟨-, -, -, -, hS, hT, -⟩ := h
  rw [arunL]
  dsimp only [ADec.piece]
  simp only [hp, ↓reduceDIte]
  unfold leafSolve LeafFlow.fval
  simp only [CombMap.head]
  erw [lrk_vimg hp hS hT x, lrk_vimg hp hS hT ((pmap hp).rev x)]
  rfl

/-- The decision on natural words, with the offset `z`. -/
def fvalN (a b z p q : ℕ) : ℕ :=
  if a < 3 ∧ b < 3 then (if a < b then z + p else if b < a then z - q else z) else z

lemma fvalN_eq {a b z p q : ℕ} {U U' : ℤ} (hp : (p : ℤ) = U) (hq : (q : ℤ) = U') (hqz : q ≤ z) :
    (fvalN a b z p q : ℤ) = z + LeafFlow.fval a b U U' := by
  unfold fvalN LeafFlow.fval
  split_ifs <;> push_cast <;> omega

lemma fvalN_le {a b z p q : ℕ} (hp : p ≤ z) : fvalN a b z p q ≤ 2 * z := by
  unfold fvalN; split_ifs <;> omega

/-! ### The test -/

/-- **The test**: `r2997 := mem (r3004 + 2)`. -/
def mtProg : Stmt := block [.constN 6400 2, .addN 6401 3004 6400, .loadN 2997 6401]

theorem mtProg_exec {P : Input} {W : ℕ} (c : Config) (hc : WordsBounded W c) {d : ℕ}
    (r4 : c.nreg 3004 = d) (hd : d + 2 ≤ W) :
    ∃ c' k, Exec P W mtProg c c' k ∧ k = 3 ∧ c'.nreg 2997 = c.nmem (d + 2) ∧
      (∀ x, x ≠ 2997 → x ≠ 6400 → x ≠ 6401 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mtProg
  exec_block
  all_goals try (first | omega | (config_simp; simp only [r4]; omega))
  refine ⟨rfl, ?_, fun x a b e => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r4]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega


/-! ### The leaf solver -/

/-- The set-up, first part: `r6407 = 1`, `r6406 = 3`, `r6400 = m`, `r6405 = Z`. -/
def mlSetA : Stmt := block [.constN 6407 1, .constN 6406 3, .loadN 6400 3004,
  .constN 6409 3, .addN 6410 3004 6409, .loadN 6405 6410]

/-- The set-up, second part: the bases `r6402 = RV`, `r6403 = CP`, `r6401 = KR`, `r6404 = FL`,
`r6408 = 0`. -/
def mlSetB : Stmt := block [.constN 6409 4, .addN 6411 3004 6409,
  .addN 6402 6411 6400, .addN 6412 6402 6400, .addN 6403 6412 6400, .addN 6401 6403 6400,
  .addN 6412 6401 6400, .addN 6404 6412 6400, .constN 6408 0]

/-- The set-up: `r6400 = m`, `r6405 = Z`, `r6402 = RV`, `r6403 = CP`, `r6401 = KR`, `r6404 = FL`
(the bases of the arrays of the frame at `r3004`), `r6406 = 3`, `r6407 = 1`, `r6408 = 0`. -/
def mlSet : Stmt := .seq mlSetA mlSetB

/-- The ranks of the two ends of the dart `i = r6408`: `r6410 = KR[i]`, `r6411 = RV[i]`,
`r6412 = KR[RV[i]]`; `r6413 := Z`. -/
def mlRk : Stmt := block [.addN 6409 6401 6408, .loadN 6410 6409, .addN 6409 6402 6408,
  .loadN 6411 6409, .addN 6409 6401 6411, .loadN 6412 6409, .copyN 6413 6405]

/-- Up in rank: `r6413 := Z + CP[i]`. -/
def mlUp : Stmt := block [.addN 6409 6403 6408, .loadN 6414 6409, .addN 6413 6405 6414]

/-- Down in rank: `r6413 := Z - CP[RV[i]]`. -/
def mlDown : Stmt := block [.addN 6409 6403 6411, .loadN 6414 6409, .subN 6413 6405 6414]

/-- The decision. -/
def mlDec : Stmt :=
  .ifLtN 6410 6406 (.ifLtN 6412 6406 (.ifLtN 6410 6412 mlUp (.ifLtN 6412 6410 mlDown .skip)) .skip)
    .skip

/-- `FL[i] := r6413`, `i := i + 1`. -/
def mlWr : Stmt := block [.addN 6409 6404 6408, .storeN 6409 6413, .addN 6408 6408 6407]

/-- One dart. -/
def mlBody : Stmt := .seq mlRk (.seq mlDec mlWr)

/-- **The leaf solver** on the frame at `r3004`. -/
def mlProg : Stmt := .seq mlSet (.whileLtN 6408 6400 mlBody)

section Leaf

variable {P : Input} {W : ℕ}

theorem mlDec_exec (c : Config) (hc : WordsBounded W c) {a b z p q Cb i j : ℕ}
    (r10 : c.nreg 6410 = a) (r12 : c.nreg 6412 = b) (r6 : c.nreg 6406 = 3)
    (r13 : c.nreg 6413 = z) (r5 : c.nreg 6405 = z) (r3 : c.nreg 6403 = Cb)
    (r8 : c.nreg 6408 = i) (r11 : c.nreg 6411 = j) (mp : c.nmem (Cb + i) = p)
    (mq : c.nmem (Cb + j) = q) (w1 : Cb + i ≤ W) (w2 : Cb + j ≤ W) (w3 : z + p ≤ W) :
    ∃ c' k, Exec P W mlDec c c' k ∧ k ≤ 8 ∧ c'.nreg 6413 = fvalN a b z p q ∧
      (∀ x, x ≠ 6409 → x ≠ 6413 → x ≠ 6414 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mlDec
  by_cases ha : a < 3
  · refine spec_ifLtN_true (by rw [r10, r6]; exact ha) ?_
    by_cases hb : b < 3
    · refine spec_ifLtN_true (by rw [r12, r6]; exact hb) ?_
      by_cases hab : a < b
      · refine spec_ifLtN_true (by rw [r10, r12]; exact hab) ?_
        unfold mlUp
        exec_block
        all_goals try (first | omega | (config_simp; simp only [r3, r8, r5, mp]; omega))
        refine ⟨by omega, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; simp only [r3, r8, r5, mp, fvalN, ha, hb, hab, and_self, ↓reduceIte]
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      · refine spec_ifLtN_false (by rw [r10, r12]; exact hab) ?_
        by_cases hba : b < a
        · refine spec_ifLtN_true (by rw [r10, r12]; exact hba) ?_
          unfold mlDown
          exec_block
          all_goals try (first | omega | (config_simp; simp only [r3, r11, r5, mq]; omega))
          refine ⟨by omega, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
          · config_simp
            simp only [r3, r11, r5, mq, fvalN, ha, hb, hab, hba, and_self, ↓reduceIte]
          · config_simp; simp only [upd_apply]; split_ifs <;> omega
        · refine spec_ifLtN_false (by rw [r10, r12]; exact hba) ?_
          refine spec_skip hc ⟨by omega, ?_, fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
          rw [r13]; simp only [fvalN, ha, hb, hab, hba, and_self, ↓reduceIte]
    · refine spec_ifLtN_false (by rw [r12, r6]; exact hb) ?_
      refine spec_skip hc ⟨by omega, ?_, fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
      rw [r13]; simp only [fvalN, hb, and_false, ↓reduceIte]
  · refine spec_ifLtN_false (by rw [r10, r6]; exact ha) ?_
    refine spec_skip hc ⟨by omega, ?_, fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
    rw [r13]; simp only [fvalN, ha, false_and, ↓reduceIte]

theorem mlBody_exec (c : Config) (hc : WordsBounded W c) {Kb Rb Cb Fb Z i : ℕ}
    (r1 : c.nreg 6401 = Kb) (r2 : c.nreg 6402 = Rb) (r3 : c.nreg 6403 = Cb)
    (r4 : c.nreg 6404 = Fb) (r5 : c.nreg 6405 = Z) (r6 : c.nreg 6406 = 3)
    (r7 : c.nreg 6407 = 1) (r8 : c.nreg 6408 = i)
    (w1 : Kb + i ≤ W) (w2 : Rb + i ≤ W) (w3 : Kb + c.nmem (Rb + i) ≤ W) (w4 : Cb + i ≤ W)
    (w5 : Cb + c.nmem (Rb + i) ≤ W) (w6 : Fb + i ≤ W) (w7 : i + 1 ≤ W)
    (w8 : Z + c.nmem (Cb + i) ≤ W) :
    ∃ c' k, Exec P W mlBody c c' k ∧ k ≤ 18 ∧ c'.nreg 6408 = i + 1 ∧
      c'.nmem = upd c.nmem (Fb + i) (fvalN (c.nmem (Kb + i)) (c.nmem (Kb + c.nmem (Rb + i))) Z
        (c.nmem (Cb + i)) (c.nmem (Cb + c.nmem (Rb + i)))) ∧
      (∀ x, (x < 6408 ∨ 6414 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, g10, g11, g12, g13, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W mlRk c c₁ k₁ ∧ k₁ = 7 ∧ c₁.nreg 6410 = c.nmem (Kb + i) ∧
      c₁.nreg 6411 = c.nmem (Rb + i) ∧ c₁.nreg 6412 = c.nmem (Kb + c.nmem (Rb + i)) ∧
      c₁.nreg 6413 = Z ∧
      (∀ x, x ≠ 6409 → x ≠ 6410 → x ≠ 6411 → x ≠ 6412 → x ≠ 6413 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold mlRk
    exec_block
    all_goals try (first | omega | (config_simp; simp only [r1, r2, r8]; omega))
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x a b c d e => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r1, r8]
    · config_simp; simp only [r2, r8]
    · config_simp; simp only [r1, r2, r8]
    · config_simp; simp only [r5]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have q1 : ∀ x, x ≠ 6409 → x ≠ 6410 → x ≠ 6411 → x ≠ 6412 → x ≠ 6413 → c₁.nreg x = c.nreg x :=
    gn₁
  obtain ⟨c₂, k₂, e₂, hk₂, g13', gn₂, gm₂, gr₂, grm₂, go₂⟩ := mlDec_exec (P := P) c₁ e₁.wb_right
    g10 g12 (by rw [q1 _ (by omega) (by omega) (by omega) (by omega) (by omega), r6]) g13
    (by rw [q1 _ (by omega) (by omega) (by omega) (by omega) (by omega), r5])
    (by rw [q1 _ (by omega) (by omega) (by omega) (by omega) (by omega), r3])
    (by rw [q1 _ (by omega) (by omega) (by omega) (by omega) (by omega), r8]) g11
    (by rw [gm₁]) (by rw [gm₁]) w4 w5 w8
  have q2 : ∀ x, x ≠ 6409 → x ≠ 6413 → x ≠ 6414 → c₂.nreg x = c₁.nreg x := gn₂
  obtain ⟨c₃, k₃, e₃, hk₃, g8, gm₃, gn₃, gr₃, grm₃, go₃⟩ : ∃ c₃ k₃,
      Exec P W mlWr c₂ c₃ k₃ ∧ k₃ = 3 ∧ c₃.nreg 6408 = i + 1 ∧
      c₃.nmem = upd c₂.nmem (Fb + i) (c₂.nreg 6413) ∧
      (∀ x, x ≠ 6408 → x ≠ 6409 → c₃.nreg x = c₂.nreg x) ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have s4 : c₂.nreg 6404 = Fb := by
      rw [q2 _ (by omega) (by omega) (by omega),
        q1 _ (by omega) (by omega) (by omega) (by omega) (by omega), r4]
    have s8 : c₂.nreg 6408 = i := by
      rw [q2 _ (by omega) (by omega) (by omega),
        q1 _ (by omega) (by omega) (by omega) (by omega) (by omega), r8]
    have s7 : c₂.nreg 6407 = 1 := by
      rw [q2 _ (by omega) (by omega) (by omega),
        q1 _ (by omega) (by omega) (by omega) (by omega) (by omega), r7]
    have hw₂ := e₂.wb_right
    unfold mlWr
    exec_block
    all_goals try (first | omega | (config_simp; simp only [s4, s8, s7]; omega))
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [s8, s7]
    · config_simp; simp only [s4, s8]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, g8, ?_, fun x hx => ?_,
    by rw [gr₃, gr₂, gr₁], by rw [grm₃, grm₂, grm₁], by rw [go₃, go₂, go₁]⟩
  · rw [gm₃, gm₂, gm₁, g13']
  · rw [gn₃ x (by omega) (by omega), q2 x (by omega) (by omega) (by omega),
      q1 x (by omega) (by omega) (by omega) (by omega) (by omega)]

theorem mlSet_exec (c : Config) (hc : WordsBounded W c) {d m : ℕ} (r4 : c.nreg 3004 = d)
    (hm : c.nmem d = m) (hW : d + 4 + 6 * m ≤ W) :
    ∃ c' k, Exec P W mlSet c c' k ∧ k = 15 ∧ c'.nreg 6400 = m ∧ c'.nreg 6405 = c.nmem (d + 3) ∧
      c'.nreg 6402 = d + 4 + m ∧ c'.nreg 6403 = d + 4 + 3 * m ∧ c'.nreg 6401 = d + 4 + 4 * m ∧
      c'.nreg 6404 = d + 4 + 6 * m ∧ c'.nreg 6406 = 3 ∧ c'.nreg 6407 = 1 ∧ c'.nreg 6408 = 0 ∧
      (∀ x, (x < 6400 ∨ 6414 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a7, a6, a0, a5, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W mlSetA c c₁ k₁ ∧ k₁ = 6 ∧ c₁.nreg 6407 = 1 ∧ c₁.nreg 6406 = 3 ∧
      c₁.nreg 6400 = m ∧ c₁.nreg 6405 = c.nmem (d + 3) ∧
      (∀ x, (x < 6400 ∨ 6414 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold mlSetA
    exec_block
    all_goals try (first | omega | (config_simp; simp only [r4, hm]; omega))
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      config_simp
      try (simp (disch := omega) only [upd_other, upd_same, r4, hm])
      try omega
  have b4 : c₁.nreg 3004 = d := by rw [gn₁ _ (by omega), r4]
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, b2, b3, b1, b5, b8, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W mlSetB c₁ c₂ k₂ ∧ k₂ = 9 ∧ c₂.nreg 6402 = d + 4 + m ∧
      c₂.nreg 6403 = d + 4 + 3 * m ∧ c₂.nreg 6401 = d + 4 + 4 * m ∧
      c₂.nreg 6404 = d + 4 + 6 * m ∧ c₂.nreg 6408 = 0 ∧
      (∀ x, x ≠ 6401 → x ≠ 6402 → x ≠ 6403 → x ≠ 6404 → x ≠ 6408 → x ≠ 6409 → x ≠ 6411 →
        x ≠ 6412 → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    unfold mlSetB
    exec_block
    all_goals try (first | omega | (config_simp; simp only [b4, a0]; omega))
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 h3 h4 h5 h6 h7 h8 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      config_simp
      try (simp (disch := omega) only [upd_other, upd_same, b4, a0])
      try omega
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, ?_, ?_, b2, b3, b1, b5, ?_, ?_, b8, fun x hx => ?_,
    by rw [gm₂, gm₁], by rw [gr₂, gr₁], by rw [grm₂, grm₁], by rw [go₂, go₁]⟩
  · rw [gn₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), a0]
  · rw [gn₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), a5]
  · rw [gn₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), a6]
  · rw [gn₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), a7]
  · rw [gn₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), gn₁ x hx]

/-- **The leaf solver on the machine**: from the frame at `d = r3004` (`m = mem d`, `Z =
mem (d + 3)`, the reverse indices `RV[i] < m`, the capacities `CP[i] ≤ Z`, `2 Z ≤ W`), within
`20 m + 17` steps `FL[i] = fvalN KR[i] KR[RV[i]] Z CP[i] CP[RV[i]]` for `i < m`; memory outside
`[d + 4 + 6 m, d + 4 + 7 m)`, registers outside `6400 … 6414`, reals and output kept. -/
theorem mlProg_exec (c : Config) (hc : WordsBounded W c) {d m Z : ℕ} (r4 : c.nreg 3004 = d)
    (hm : c.nmem d = m) (hz : c.nmem (d + 3) = Z) (hW : d + 4 + 7 * m ≤ W) (hZ : 2 * Z ≤ W)
    (hrv : ∀ i < m, c.nmem (d + 4 + m + i) < m) (hcp : ∀ i < m, c.nmem (d + 4 + 3 * m + i) ≤ Z) :
    ∃ c' k, Exec P W mlProg c c' k ∧ k ≤ 20 * m + 17 ∧
      (∀ i < m, c'.nmem (d + 4 + 6 * m + i) = fvalN (c.nmem (d + 4 + 4 * m + i))
        (c.nmem (d + 4 + 4 * m + c.nmem (d + 4 + m + i))) Z (c.nmem (d + 4 + 3 * m + i))
        (c.nmem (d + 4 + 3 * m + c.nmem (d + 4 + m + i)))) ∧
      (∀ a, ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 7 * m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6400 ∨ 6414 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, s0, s5, s2, s3, s1, s4, s6, s7, s8, gn₁, gm₁, gr₁, grm₁, go₁⟩ :=
    mlSet_exec (P := P) c hc r4 hm (by omega)
  rw [hz] at s5
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 6408 ∨ 6414 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (d + 4 + 6 * m + j) = fvalN (m₀ (d + 4 + 4 * m + j))
        (m₀ (d + 4 + 4 * m + m₀ (d + 4 + m + j))) Z (m₀ (d + 4 + 3 * m + j))
        (m₀ (d + 4 + 3 * m + m₀ (d + 4 + m + j)))) ∧
    (∀ a, ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h8, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 6408)
    (b := 6400) (body := mlBody) J (B := 18) c₁ e₁.wb_right s8 s0 (Nat.zero_le m)
    ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega), fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h8 h0 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 6408 ∨ 6414 < x) → c'.nreg x = c₁.nreg x := j1
      have hr := hrv i hhi
      have e1 : ∀ a, a < d + 4 + 6 * m → c'.nmem a = m₀ a := fun a ha => j3 a (by omega)
      have a2 : c'.nmem (d + 4 + m + i) = m₀ (d + 4 + m + i) := e1 _ (by omega)
      have a1 : c'.nmem (d + 4 + 4 * m + i) = m₀ (d + 4 + 4 * m + i) := e1 _ (by omega)
      have a3 : c'.nmem (d + 4 + 3 * m + i) = m₀ (d + 4 + 3 * m + i) := e1 _ (by omega)
      have a4 : c'.nmem (d + 4 + 4 * m + m₀ (d + 4 + m + i)) =
          m₀ (d + 4 + 4 * m + m₀ (d + 4 + m + i)) := e1 _ (by omega)
      have a5 : c'.nmem (d + 4 + 3 * m + m₀ (d + 4 + m + i)) =
          m₀ (d + 4 + 3 * m + m₀ (d + 4 + m + i)) := e1 _ (by omega)
      have hc' := hcp i hhi
      obtain ⟨c'', t, ex, ht, h8', hm', hn', hr', hrm', ho'⟩ := mlBody_exec (P := P) c' hw
        (Kb := d + 4 + 4 * m) (Rb := d + 4 + m) (Cb := d + 4 + 3 * m) (Fb := d + 4 + 6 * m)
        (Z := Z)
        (by rw [f _ (by omega), s1]) (by rw [f _ (by omega), s2]) (by rw [f _ (by omega), s3])
        (by rw [f _ (by omega), s4]) (by rw [f _ (by omega), s5]) (by rw [f _ (by omega), s6])
        (by rw [f _ (by omega), s7]) h8 (by omega) (by omega)
        (by rw [a2]; omega) (by omega) (by rw [a2]; omega) (by omega)
        (by omega) (by rw [a3]; omega)
      rw [a2] at hm'
      rw [a1, a3, a4, a5] at hm'
      refine ⟨c'', t, ex, ht, h8', by rw [hn' _ (by omega)]; exact h0,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
        exact j3 a (fun h => ha ⟨h.1, by omega⟩))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, fun a ha => j3 a (by omega), fun x hx => ?_,
    by rw [j4, gr₁], by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), gn₁ x (by omega)]

/-! ### The fields of `MfSpecR` -/

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- The number of darts of a frame is the number of darts of its piece map. -/
lemma Lay.card {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (h : Lay M gid u S T Z x m en d mem) : m = (pdarts M x.1.piece x.2.1).card := by
  have e : pdarts M x.1.piece x.2.1 = (range m).image en := by
    ext y
    simp only [mem_image, mem_range]
    constructor
    · intro hy; obtain ⟨i, hi, rfl⟩ := h.en_surj y hy; exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact h.en_mem i hi
  rw [e, card_image_of_injOn (fun i hi j hj e => h.en_inj (mem_range.1 hi) (mem_range.1 hj) e),
    card_range]

/-- **The test meets the field `test` of `MfSpecR`** (with `G = True`), in `3` steps. -/
theorem mtProg_spec {Reach : MCall M → Prop} {I : Input} {W Hb : ℕ} :
    ∀ (x : MCall M) d e h c, True → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → FInL M Reach gid u S T Z x d e c →
    ∃ c' t, Exec I W mtProg c c' t ∧ t ≤ 3 ∧ True ∧ DRegKeep c c' ∧ HeapKeep Hb h h h c c' ∧
      c'.output = c.output ∧ (c'.nreg 2997 < 1 ↔ ∃ Q, x.1 = .leaf Q) := by
  intro x d e h c _ hc r4 _ r3 _ _ h3 ⟨_, _, m, en, hl, he⟩
  have hW : h ≤ W := r3 ▸ hc.1 3003
  unfold fsz at he
  obtain ⟨c', k, ex, hk, g97, gn, gm, gr, grm, go⟩ := mtProg_exec (P := I) c hc r4 (by omega)
  refine ⟨c', k, ex, by omega, trivial, fun r h1 h2 => gn r (by omega) (by omega) (by omega),
    fun a _ _ _ => ⟨by rw [gm], by rw [grm]⟩, go, ?_⟩
  rw [g97, hl.tag]
  exact ntag_lt_one_iff x.1

/-- **The leaf solver meets the field `leaf` of `MfSpecR`** (with `G = True`, `2 Z ≤ W`, no room
needed): within `20 m + 17` steps (`m` the darts of the piece map) the flow array of the frame
holds `Z + arunL` of the leaf call. -/
theorem mlProg_spec (O : PlaneOracles.{w}) {Reach : MCall M → Prop} {I : Input} {W Hb : ℕ}
    (hZ : 2 * Z ≤ W) :
    ∀ Q Hs σ d e h c, True → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h →
    FInL M Reach gid u S T Z (.leaf Q, Hs, σ) d e c →
    ∃ c' t, Exec I W mlProg c c' t ∧ t ≤ 20 * (pdarts M Q Hs).card + 17 ∧ True ∧
      DRegKeep c c' ∧ HeapKeep Hb h d e c c' ∧ c'.output = c.output ∧
      FOutL M gid u S T Z (.leaf Q, Hs, σ) (cflow M O u S T (.leaf Q, Hs, σ)) d e c' := by
  intro Q Hs σ d e h c _ hc r4 _ r3 _ _ h3 ⟨_, hok, m, en, hl, he⟩
  have hW : h ≤ W := r3 ▸ hc.1 3003
  have hm := hl.card
  unfold fsz at he
  obtain ⟨c', k, ex, hk, hf, hkeep, gn, gr, grm, go⟩ := mlProg_exec (P := I) c hc r4 hl.hm hl.hz
    (by omega) hZ (fun i hi => (hl.rv i hi).1) (fun i hi => (hl.cp i hi).2)
  refine ⟨c', k, ex, by have : m = (pdarts M Q Hs).card := hm; omega, trivial,
    fun r h1 h2 => gn r (by omega), fun a _ _ ha => ⟨hkeep a (by omega), by rw [grm]⟩, go,
    m, en, hl.congr fun a h1 h2 => hkeep a (by omega), by unfold fsz; omega, fun i hi => ?_⟩
  rw [hf i hi]
  obtain ⟨hj, ej⟩ := hl.rv i hi
  set j := c.nmem (d + 4 + m + i)
  obtain ⟨cpi, -⟩ := hl.cp i hi
  obtain ⟨cpj, cpjZ⟩ := hl.cp j hj
  rw [ej] at cpj
  rw [fvalN_eq cpi cpj cpjZ, hl.kr i hi, hl.kr j hj, ej, fext_mem _ (hl.en_mem i hi)]
  exact congrArg _ (arunL_leaf_eq O u hok ⟨en i, hl.en_mem i hi⟩).symm

end Leaf

end MfDrv

end BKMNW

end PlanarFlow
