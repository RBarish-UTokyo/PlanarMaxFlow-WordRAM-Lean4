module

public import PlanarFlow.Monge.RangeMinBuild

/-!
# Range minima in an anti-Monge matrix on the machine: the merge of a node

The node of height `j + 1` at the offset `o` (registers `NCtx`, threshold `θ` in `r327` after
`thrS`) is built by merging the sorted thresholds of its two children (`2 ^ j - 1` each) and its
own threshold. The registers of the merge: the pointers `il = r354`, `ir = r355` into the
children, the head `r356` of the third array (`θ`, or the sentinel `nc + 1` once `θ` is merged),
the output index `g = r357` and its bound `2 ^ (j + 1) - 1` in `r358`.

* `recS`: the record of the gap `g`: `GL[g] := il`, `GR[g] := ir`, and `ROW[g] :=` the row of the
  gap `il` of the left child once `θ` is merged, else the row of the gap `ir` of the right child.
* `emitS`: the least of the three heads is written to `A[g]` (`MS.emitX`).
* `merge_exec`: the loop over the gaps, the last record and the sentinel; the node is correct
  (`node_ok`), within `25 · 2 ^ (j + 1) + 20` steps, writing only the cells of the level `j + 1`
  at the indices `[o, o + 2 ^ (j + 1))` (`InLev`).
* `leaves_exec`: the leaves: `A₀[o] := nc + 1`, `ROW₀[o] := o`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace RM

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs FR Heap

variable {p : RMP} {I : Input}

/-! ### Cells -/

lemma cell_inj {j j' f f' i i' : ℕ} (hf : f < 4) (hf' : f' < 4) (hi : i < p.s) (hi' : i' < p.s)
    (h : cell p j f i = cell p j' f' i') : j = j' ∧ f = f' ∧ i = i' := by
  unfold cell at h
  have h' : (4 * j + f) * p.s + i = (4 * j' + f') * p.s + i' := by omega
  have hs : 0 < p.s := Nat.one_le_two_pow
  have e1 := congrArg (· % p.s) h'
  have e2 := congrArg (· / p.s) h'
  simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at e1
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.add_comm _ i',
    Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hi'] at e2
  omega

/-- The cell `a` is an entry of one of the four arrays of the level `j`, at an index in
`[lo, hi)`. -/
def InLev (p : RMP) (j lo hi a : ℕ) : Prop := ∃ f < 4, ∃ i, lo ≤ i ∧ i < hi ∧ a = cell p j f i

lemma not_inLev {J lo hi j f i : ℕ} (hf : f < 4) (his : i < p.s) (hhi : hi ≤ p.s)
    (h : j ≠ J ∨ i < lo ∨ hi ≤ i) : ¬ InLev p J lo hi (cell p j f i) := by
  rintro ⟨f', hf', i', h1, h2, e⟩
  obtain ⟨a, b, c⟩ := cell_inj hf hf' his (by omega) e
  omega

lemma InLev.mono {J lo hi hi' a : ℕ} (h : InLev p J lo hi a) (hh : hi ≤ hi') :
    InLev p J lo hi' a := by
  obtain ⟨f, hf, i, h1, h2, e⟩ := h
  exact ⟨f, hf, i, h1, by omega, e⟩

lemma InLev.bound {J lo hi a : ℕ} (h : InLev p J lo hi a) (hJ : J ≤ p.T) (hhi : hi ≤ p.s) :
    p.B ≤ a ∧ a < p.B + 4 * (p.T + 1) * p.s := by
  obtain ⟨f, hf, i, h1, h2, rfl⟩ := h
  have := cell_bound (p := p) hJ
  have := cell_eq (p := p) J f i
  have : f * p.s ≤ 3 * p.s := Nat.mul_le_mul_right _ (by omega)
  unfold cell at *; constructor <;> omega

/-- Equal arrays from equal cells. -/
lemma arr_congr {nm nm' : ℕ → ℕ} {j f o e : ℕ}
    (h : nm' (cell p j f (o + e)) = nm (cell p j f (o + e))) :
    Arr nm' p j f o e = Arr nm p j f o e :=
  h

lemma gapAt_congr {nm nm' : ℕ → ℕ} {j o σ : ℕ}
    (h : ∀ e < 2 ^ j, nm' (cell p j 0 (o + e)) = nm (cell p j 0 (o + e))) :
    gapAt nm' p j o σ = gapAt nm p j o σ :=
  cntP_congr fun e he => h e (by omega)

/-- **A node depends only on its cells** (and those of its children). -/
lemma NodeOK.congr {F : ℕ → ℕ → ℝ} {nm nm' : ℕ → ℕ} {j o : ℕ}
    (hS : ∀ j', (j' = j ∨ j = j' + 1) → ∀ f < 4, ∀ e < 2 ^ j,
      nm' (cell p j' f (o + e)) = nm (cell p j' f (o + e)))
    (hok : NodeOK F p nm j o) : NodeOK F p nm' j o := by
  have h0 := hS j (Or.inl rfl)
  have hg : ∀ σ, gapAt nm' p j o σ = gapAt nm p j o σ := fun σ =>
    gapAt_congr fun e he => h0 0 (by omega) e he
  have hgl := gapAt_lt nm (p := p) j o
  obtain ⟨⟨a1, a2, a3⟩, hσ⟩ := hok
  have hpos := Nat.one_le_two_pow (n := j)
  refine ⟨⟨fun e he => ?_, ?_, fun e he => ?_⟩, fun σ hσ' => ?_⟩
  · rw [arr_congr (h0 0 (by omega) e (by omega)), arr_congr (h0 0 (by omega) (e + 1) (by omega))]
    exact a1 e he
  · rw [arr_congr (h0 0 (by omega) _ (by omega))]; exact a2
  · rw [arr_congr (h0 0 (by omega) e (by omega))]; exact a3 e he
  obtain ⟨b1, b2⟩ := hσ σ hσ'
  rw [hg σ, arr_congr (h0 3 (by omega) _ (hgl σ))]
  refine ⟨b1, fun j' hj => ?_⟩
  obtain ⟨c1, c2⟩ := b2 j' hj
  have h1 := hS j' (Or.inr hj)
  have hp : 2 ^ j = 2 * 2 ^ j' := by rw [hj, pow_succ]; ring
  rw [arr_congr (h0 1 (by omega) _ (hgl σ)), arr_congr (h0 2 (by omega) _ (hgl σ)), c1, c2]
  refine ⟨gapAt_congr fun e he => (h1 0 (by omega) e (by omega)).symm,
    gapAt_congr fun e he => ?_⟩
  have := h1 0 (by omega) (2 ^ j' + e) (by omega)
  rw [← Nat.add_assoc] at this; exact this.symm

/-- A node is kept by a write to the cells of a level at indices outside it. -/
lemma NodeOK.frame {F : ℕ → ℕ → ℝ} {nm nm' : ℕ → ℕ} {J lo hi j o : ℕ} (hos : o + 2 ^ j ≤ p.s)
    (hhi : hi ≤ p.s) (hfr : ∀ a, ¬ InLev p J lo hi a → nm' a = nm a)
    (hd : J ≠ j ∧ J ≠ j - 1 ∨ o + 2 ^ j ≤ lo ∨ hi ≤ o) (hok : NodeOK F p nm j o) :
    NodeOK F p nm' j o :=
  hok.congr fun j' hj' f hf e he =>
    hfr _ (not_inLev (j := j') (i := o + e) hf (by omega) hhi (by omega))

/-! ### The records of the gaps -/

/-- **The record of the gap `g`** of the node of height `j + 1` at `o` (memory `nm`; the children
in `nm₀`): its gaps `GL[g]`, `GR[g]` at the children and whether `θ` was merged (`iz`) count its
sources, and `ROW[g]` is the row of the child chosen by `θ`; as in `node_ok`. -/
def GapRec (p : RMP) (nm nm₀ : ℕ → ℕ) (j o θ g : ℕ) : Prop :=
  ∃ iz ≤ 1, Arr nm p (j + 1) 1 o g ≤ 2 ^ j - 1 ∧ Arr nm p (j + 1) 2 o g ≤ 2 ^ j - 1 ∧
    Arr nm p (j + 1) 1 o g + Arr nm p (j + 1) 2 o g + iz = g ∧
    (∀ σ, cntP (Arr nm p (j + 1) 0 o) g σ = cntP (Arr nm₀ p j 0 o) (Arr nm p (j + 1) 1 o g) σ +
      cntP (Arr nm₀ p j 0 (o + 2 ^ j)) (Arr nm p (j + 1) 2 o g) σ + cntP (Ac θ p.nc) iz σ) ∧
    Arr nm p (j + 1) 3 o g = if iz = 1 then Arr nm₀ p j 3 o (Arr nm p (j + 1) 1 o g) else
      Arr nm₀ p j 3 (o + 2 ^ j) (Arr nm p (j + 1) 2 o g)

lemma GapRec.congr {nm nm' nm₀ : ℕ → ℕ} {j o θ g : ℕ}
    (h0 : ∀ e < g, nm' (cell p (j + 1) 0 (o + e)) = nm (cell p (j + 1) 0 (o + e)))
    (h123 : ∀ f, 1 ≤ f → f < 4 → nm' (cell p (j + 1) f (o + g)) = nm (cell p (j + 1) f (o + g)))
    (h : GapRec p nm nm₀ j o θ g) : GapRec p nm' nm₀ j o θ g := by
  obtain ⟨iz, hiz, a1, a2, a3, a4, a5⟩ := h
  have e1 : Arr nm' p (j + 1) 1 o g = Arr nm p (j + 1) 1 o g := h123 1 le_rfl (by omega)
  have e2 : Arr nm' p (j + 1) 2 o g = Arr nm p (j + 1) 2 o g := h123 2 (by omega) (by omega)
  have e3 : Arr nm' p (j + 1) 3 o g = Arr nm p (j + 1) 3 o g := h123 3 (by omega) (by omega)
  refine ⟨iz, hiz, by rw [e1]; exact a1, by rw [e2]; exact a2, by rw [e1, e2]; exact a3,
    fun σ => ?_, by rw [e1, e2, e3]; exact a5⟩
  rw [cntP_congr (f := Arr nm' p (j + 1) 0 o) (g := Arr nm p (j + 1) 0 o) (fun e he => h0 e he),
    e1, e2]
  exact a4 σ

/-! ### The programs -/

/-- The record of the gap `g = r357`: `ROW[g]` (the row of the right child at the gap `ir` while
`θ` is not merged, `r356 < nc + 1`, else of the left child at `il`), `GL[g] := il`,
`GR[g] := ir`. -/
def recS : Stmt :=
  .seq (.ifLtN 356 310 (block [.addN 361 337 355, .loadN 361 361])
    (block [.addN 361 336 354, .loadN 361 361])) <|
  block [.addN 360 338 357, .addN 360 360 301, .storeN 360 354, .addN 360 360 301,
    .storeN 360 355, .addN 360 360 301, .storeN 360 361]

/-- The head of the left child is written. -/
def emX : Stmt := block [.storeN 360 362, .addN 354 354 308]

/-- The head of the right child is written. -/
def emY : Stmt := block [.storeN 360 363, .addN 355 355 308]

/-- The threshold `θ` of the node is written; the third head becomes the sentinel. -/
def emZ : Stmt := block [.storeN 360 356, .copyN 356 310]

/-- The least of the three heads is written to `A[g]`, and `g := g + 1`. -/
def emitS : Stmt :=
  .seq (block [.addN 362 334 354, .loadN 362 362, .addN 363 335 355, .loadN 363 363,
    .addN 360 338 357]) <|
  .seq (.ifLtN 363 362 (.ifLtN 356 363 emZ emY) (.ifLtN 356 362 emZ emX))
    (.instr (.addN 357 357 308))

/-- One gap of the merge. -/
def mergeBody : Stmt := .seq recS emitS

/-- **The merge** of the node: the gaps `g < 2 ^ (j + 1) - 1`, then the record of the last gap
and the sentinel. -/
def merge : Stmt :=
  .seq (block [.constN 354 0, .constN 355 0, .copyN 356 327, .constN 357 0, .addN 358 331 331,
    .subN 358 358 308]) <|
  .seq (.whileLtN 357 358 mergeBody) <|
  .seq recS (block [.addN 360 338 357, .storeN 360 310])

lemma cell_lt {j f i : ℕ} (hj : j ≤ p.T) (hf : f < 4) (hi : i < p.s) :
    cell p j f i < p.B + 4 * (p.T + 1) * p.s := by
  have := cell_bound (p := p) hj
  have := cell_eq (p := p) j f i
  have : f * p.s ≤ 3 * p.s := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The record of a gap on the machine. -/
theorem recS_exec (hL : RMLay p) {j o : ℕ} (c : Config) (hc : WordsBounded p.W c)
    (hR : RCtx p c) (hN : NCtx p j o c) (hj : j + 1 ≤ p.T) (ho : 2 ^ (j + 1) ∣ o)
    (hos : o < p.s) (hil : c.nreg 354 ≤ 2 ^ j - 1) (hir : c.nreg 355 ≤ 2 ^ j - 1)
    (hg : c.nreg 357 < 2 ^ (j + 1)) :
    ∃ c' k, Exec I p.W recS c c' k ∧ k ≤ 11 ∧
      (c'.nmem = upd (upd (upd c.nmem (cell p (j + 1) 1 (o + c.nreg 357)) (c.nreg 354))
        (cell p (j + 1) 2 (o + c.nreg 357)) (c.nreg 355)) (cell p (j + 1) 3 (o + c.nreg 357))
        (if c.nreg 356 < p.nc + 1 then c.nmem (cell p j 3 (o + 2 ^ j + c.nreg 355)) else
          c.nmem (cell p j 3 (o + c.nreg 354))) ∧
        (∀ r, r ≠ 360 → r ≠ 361 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hW := W_bound hL
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have hds := off_le ho (pow_dvd_s hj) hos
  have b1 := cell_lt (p := p) (j := j) (f := 3) (i := o + 2 ^ j + c.nreg 355) (by omega)
    (by omega) (by omega)
  have b2 := cell_lt (p := p) (j := j + 1) (f := 3) (i := o + c.nreg 357) hj
    (by omega) (by omega)
  have a1 := cell_eq (p := p) (j + 1) 1 (o + c.nreg 357)
  have a2 := cell_eq (p := p) (j + 1) 2 (o + c.nreg 357)
  have a3 := cell_eq (p := p) (j + 1) 3 (o + c.nreg 357)
  have a0 := cell_eq (p := p) (j + 1) 0 o
  have r3 := cell_eq (p := p) j 3 (o + 2 ^ j)
  have r3' := cell_eq (p := p) j 3 (o + 2 ^ j + c.nreg 355)
  have l3 := cell_eq (p := p) j 3 o
  have l3' := cell_eq (p := p) j 3 (o + c.nreg 354)
  have hrow : ∃ c₁ k₁, Exec I p.W (.ifLtN 356 310 (block [.addN 361 337 355, .loadN 361 361])
      (block [.addN 361 336 354, .loadN 361 361])) c c₁ k₁ ∧ k₁ ≤ 4 ∧
      c₁ = { c with nreg := upd c.nreg 361 (if c.nreg 356 < p.nc + 1 then
        c.nmem (cell p j 3 (o + 2 ^ j + c.nreg 355)) else c.nmem (cell p j 3 (o + c.nreg 354))) }
      := by
    by_cases ht : c.nreg 356 < p.nc + 1
    · refine spec_ifLtN_true (by rw [hR.r310]; exact ht) ?_
      exec_block
      · rw [hN.r337]; omega
      refine ⟨by omega, ?_⟩
      simp only [ht, ↓reduceIte]
      rw [hN.r337, show cell p j 3 (o + 2 ^ j) + c.nreg 355 = cell p j 3 (o + 2 ^ j + c.nreg 355)
        by omega]
    · refine spec_ifLtN_false (by rw [hR.r310]; exact ht) ?_
      exec_block
      · rw [hN.r336]; omega
      refine ⟨by omega, ?_⟩
      simp only [ht, ↓reduceIte]
      rw [hN.r336, show cell p j 3 o + c.nreg 354 = cell p j 3 (o + c.nreg 354) by omega]
  obtain ⟨c₁, k₁, e₁, hk₁, rfl⟩ := hrow
  unfold recS
  refine spec_seq ⟨_, k₁, e₁, ?_⟩
  have hw₁ := e₁.wb_right
  generalize hrw : (if c.nreg 356 < p.nc + 1 then c.nmem (cell p j 3 (o + 2 ^ j + c.nreg 355))
    else c.nmem (cell p j 3 (o + c.nreg 354))) = row at hw₁ ⊢
  exec_block
  · config_simp; rw [hN.r338]; omega
  · config_simp; rw [hN.r338, hR.r301]; omega
  · config_simp; rw [hN.r338, hR.r301]; omega
  · config_simp; rw [hN.r338, hR.r301]; omega
  refine ⟨by omega, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp
    rw [hN.r338, hR.r301,
      show cell p (j + 1) 0 o + c.nreg 357 + p.s + p.s + p.s = cell p (j + 1) 3 (o + c.nreg 357)
        by omega,
      show cell p (j + 1) 0 o + c.nreg 357 + p.s + p.s = cell p (j + 1) 2 (o + c.nreg 357)
        by omega,
      show cell p (j + 1) 0 o + c.nreg 357 + p.s = cell p (j + 1) 1 (o + c.nreg 357) by omega]
  · config_simp; upd_tac

/-- The emission of the least head on the machine: the head `x` of the left child, `y` of the
right child, `z = r356`; ties go to the left child, then to the right child. -/
theorem emitS_exec (hL : RMLay p) {j o : ℕ} (c : Config) (hc : WordsBounded p.W c)
    (hR : RCtx p c) (hN : NCtx p j o c) (hj : j + 1 ≤ p.T) (ho : 2 ^ (j + 1) ∣ o)
    (hos : o < p.s) (hil : c.nreg 354 ≤ 2 ^ j - 1) (hir : c.nreg 355 ≤ 2 ^ j - 1)
    (hg : c.nreg 357 < 2 ^ (j + 1)) :
    ∃ c' k, Exec I p.W emitS c c' k ∧ k ≤ 12 ∧
      (c'.nreg 357 = c.nreg 357 + 1 ∧
        (∀ r, r ≠ 354 → r ≠ 355 → r ≠ 356 → r ≠ 357 → r ≠ 360 → r ≠ 362 → r ≠ 363 →
          c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
        c'.output = c.output ∧
        ((c.nmem (cell p j 0 (o + c.nreg 354)) ≤ c.nmem (cell p j 0 (o + 2 ^ j + c.nreg 355)) ∧
          c.nmem (cell p j 0 (o + c.nreg 354)) ≤ c.nreg 356 ∧
          c'.nmem = upd c.nmem (cell p (j + 1) 0 (o + c.nreg 357))
            (c.nmem (cell p j 0 (o + c.nreg 354))) ∧
          c'.nreg 354 = c.nreg 354 + 1 ∧ c'.nreg 355 = c.nreg 355 ∧ c'.nreg 356 = c.nreg 356) ∨
        (c.nmem (cell p j 0 (o + 2 ^ j + c.nreg 355)) ≤ c.nmem (cell p j 0 (o + c.nreg 354)) ∧
          c.nmem (cell p j 0 (o + 2 ^ j + c.nreg 355)) ≤ c.nreg 356 ∧
          c'.nmem = upd c.nmem (cell p (j + 1) 0 (o + c.nreg 357))
            (c.nmem (cell p j 0 (o + 2 ^ j + c.nreg 355))) ∧
          c'.nreg 354 = c.nreg 354 ∧ c'.nreg 355 = c.nreg 355 + 1 ∧ c'.nreg 356 = c.nreg 356) ∨
        (c.nreg 356 ≤ c.nmem (cell p j 0 (o + c.nreg 354)) ∧
          c.nreg 356 ≤ c.nmem (cell p j 0 (o + 2 ^ j + c.nreg 355)) ∧
          c'.nmem = upd c.nmem (cell p (j + 1) 0 (o + c.nreg 357)) (c.nreg 356) ∧
          c'.nreg 354 = c.nreg 354 ∧ c'.nreg 355 = c.nreg 355 ∧ c'.nreg 356 = p.nc + 1))) := by
  have hW := W_bound hL
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have hds := off_le ho (pow_dvd_s hj) hos
  have hs : p.s ≤ p.W := by have := hL.wB; nlinarith
  have b1 := cell_lt (p := p) (j := j) (f := 0) (i := o + 2 ^ j + c.nreg 355) (by omega)
    (by omega) (by omega)
  have b2 := cell_lt (p := p) (j := j + 1) (f := 0) (i := o + c.nreg 357) hj
    (by omega) (by omega)
  have b0 := cell_lt (p := p) (j := j) (f := 0) (i := o + c.nreg 354) (by omega)
    (by omega) (by omega)
  have ex : c.nreg 334 + c.nreg 354 = cell p j 0 (o + c.nreg 354) := by
    rw [hN.r334, cell_add]
  have ey : c.nreg 335 + c.nreg 355 = cell p j 0 (o + 2 ^ j + c.nreg 355) := by
    rw [hN.r335, cell_add]
  have ez : c.nreg 338 + c.nreg 357 = cell p (j + 1) 0 (o + c.nreg 357) := by
    rw [hN.r338, cell_add]
  generalize hx : c.nmem (cell p j 0 (o + c.nreg 354)) = x
  generalize hy : c.nmem (cell p j 0 (o + 2 ^ j + c.nreg 355)) = y
  generalize hA : cell p (j + 1) 0 (o + c.nreg 357) = A at ez b2
  unfold emitS
  refine spec_seq ?_
  exec_block
  · omega
  · config_simp; omega
  · config_simp; omega
  refine spec_seq ?_
  by_cases hyx : y < x
  · refine spec_ifLtN_true (by config_simp; rw [ex, ey, hx, hy]; exact hyx) ?_
    by_cases hzy : c.nreg 356 < y
    · refine spec_ifLtN_true (by config_simp; rw [ey, hy]; exact hzy) ?_
      unfold emZ
      exec_block
      refine spec_instr (Exec.addN ‹_› 357 357 308 (by config_simp; rw [hR.r308]; omega))
        fun _ => ?_
      refine ⟨by omega, by config_simp; rw [hR.r308], fun r h1 h2 h3 h4 h5 h6 h7 => ?_, rfl, rfl,
        rfl, Or.inr (Or.inr ⟨by omega, by omega, by config_simp; simp only [ez], by config_simp,
          by config_simp, by config_simp; rw [hR.r310]⟩)⟩
      config_simp; upd_tac
    · refine spec_ifLtN_false (by config_simp; rw [ey, hy]; exact hzy) ?_
      unfold emY
      exec_block
      · config_simp; rw [hR.r308]; omega
      refine spec_instr (Exec.addN ‹_› 357 357 308 (by config_simp; rw [hR.r308]; omega))
        fun _ => ?_
      refine ⟨by omega, by config_simp; rw [hR.r308], fun r h1 h2 h3 h4 h5 h6 h7 => ?_, rfl, rfl,
        rfl, Or.inr (Or.inl ⟨by omega, by omega, by config_simp; simp only [ez, ey, hy],
          by config_simp,
          by config_simp; rw [hR.r308], by config_simp⟩)⟩
      config_simp; upd_tac
  · refine spec_ifLtN_false (by config_simp; rw [ex, ey, hx, hy]; exact hyx) ?_
    by_cases hzx : c.nreg 356 < x
    · refine spec_ifLtN_true (by config_simp; rw [ex, hx]; exact hzx) ?_
      unfold emZ
      exec_block
      refine spec_instr (Exec.addN ‹_› 357 357 308 (by config_simp; rw [hR.r308]; omega))
        fun _ => ?_
      refine ⟨by omega, by config_simp; rw [hR.r308], fun r h1 h2 h3 h4 h5 h6 h7 => ?_, rfl, rfl,
        rfl, Or.inr (Or.inr ⟨by omega, by omega, by config_simp; simp only [ez], by config_simp,
          by config_simp, by config_simp; rw [hR.r310]⟩)⟩
      config_simp; upd_tac
    · refine spec_ifLtN_false (by config_simp; rw [ex, hx]; exact hzx) ?_
      unfold emX
      exec_block
      · config_simp; rw [hR.r308]; omega
      refine spec_instr (Exec.addN ‹_› 357 357 308 (by config_simp; rw [hR.r308]; omega))
        fun _ => ?_
      refine ⟨by omega, by config_simp; rw [hR.r308], fun r h1 h2 h3 h4 h5 h6 h7 => ?_, rfl, rfl,
        rfl, Or.inl ⟨by omega, by omega, by config_simp; simp only [ez, ex, hx],
          by config_simp; rw [hR.r308], by config_simp, by config_simp⟩⟩
      config_simp; upd_tac

lemma cell_ne {j j' f f' i i' : ℕ} (hf : f < 4) (hf' : f' < 4) (hi : i < p.s) (hi' : i' < p.s)
    (h : j ≠ j' ∨ f ≠ f' ∨ i ≠ i') : cell p j f i ≠ cell p j' f' i' := fun e => by
  have := cell_inj hf hf' hi hi' e; omega

/-- **The state of the merge loop** of the node of height `j + 1` at `o` with the threshold `θ`,
from the configuration `c₀` before the merge: the merge state `MS` of the output array (the
pointers `il = r354`, `ir = r355`, `g = r357`; `θ` merged when `g - il - ir = 1`), the head
`r356` of the third array, the records of the gaps `< g`, and the frame. -/
structure IM (p : RMP) (j o θ : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded p.W c
  keep : ∀ r, (r < 354 ∨ 364 ≤ r) → c.nreg r = c₀.nreg r
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
  r358 : c.nreg 358 = 2 * (2 ^ j - 1) + 1
  ms : MS (Arr c.nmem p (j + 1) 0 o) (Arr c₀.nmem p j 0 o) (Arr c₀.nmem p j 0 (o + 2 ^ j))
    (Ac θ p.nc) (2 ^ j - 1) (2 ^ j - 1) 1 p.nc (c.nreg 357) (c.nreg 354) (c.nreg 355)
    (c.nreg 357 - c.nreg 354 - c.nreg 355)
  zc : c.nreg 356 = Ac θ p.nc (c.nreg 357 - c.nreg 354 - c.nreg 355)
  recs : ∀ g < c.nreg 357, GapRec p c.nmem c₀.nmem j o θ g
  fr : ∀ a, ¬ InLev p (j + 1) o (o + c.nreg 357) a → c.nmem a = c₀.nmem a

lemma MS.congr {Av Av' X Y Z : ℕ → ℕ} {mx my mz nc g ix iy iz : ℕ}
    (h : MS Av X Y Z mx my mz nc g ix iy iz) (he : ∀ e < g, Av' e = Av e) :
    MS Av' X Y Z mx my mz nc g ix iy iz :=
  ⟨h.ix_le, h.iy_le, h.iz_le, h.g_eq, fun σ => by rw [cntP_congr he]; exact h.cnt σ,
    fun e he' => by rw [he e (by omega), he (e + 1) he']; exact h.sorted e he',
    fun e he' => by rw [he e he']; exact h.le e he',
    fun hg => by rw [he (g - 1) (by omega)]; exact h.last hg⟩

set_option maxHeartbeats 1000000 in
/-- **One gap of the merge**: its record, then the least head is emitted. -/
theorem mergeBody_exec (hL : RMLay p) {j o θ : ℕ} {c₀ : Config} (hR₀ : RCtx p c₀)
    (hN₀ : NCtx p j o c₀) (hj : j + 1 ≤ p.T) (ho : 2 ^ (j + 1) ∣ o) (hos : o < p.s)
    (hθ : θ ≤ p.nc) (hl : LOK (Arr c₀.nmem p j 0 o) (2 ^ j - 1) p.nc)
    (hr : LOK (Arr c₀.nmem p j 0 (o + 2 ^ j)) (2 ^ j - 1) p.nc)
    (c : Config) (hI : IM p j o θ c₀ c) (hlt : c.nreg 357 < c.nreg 358) :
    ∃ c' k, Exec I p.W mergeBody c c' k ∧ IM p j o θ c₀ c' ∧
      25 * (c'.nreg 358 - c'.nreg 357) + k + 2 ≤ 25 * (c.nreg 358 - c.nreg 357) := by
  have hc := hI.wb
  have hR : RCtx p c := hR₀.of fun r h1 h2 => hI.keep r (by omega)
  have hN : NCtx p j o c := hN₀.of fun r h1 h2 => hI.keep r (by omega)
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have hpos := Nat.one_le_two_pow (n := j)
  have hds := off_le ho (pow_dvd_s hj) hos
  have hms := hI.ms
  have h358 := hI.r358
  have hzc := hI.zc
  have hrec := hI.recs
  have hfr := hI.fr
  generalize hil : c.nreg 354 = il at hms hzc
  generalize hir : c.nreg 355 = ir at hms hzc
  generalize hg : c.nreg 357 = g at hms hzc hrec hfr hlt
  generalize hiz : g - il - ir = iz at hms hzc
  have hil' := hms.ix_le; have hir' := hms.iy_le; have hiz' := hms.iz_le; have hge := hms.g_eq
  rw [h358] at hlt
  -- the cells of the children are those of `c₀`
  have hch : ∀ f < 4, ∀ i < p.s, c.nmem (cell p j f i) = c₀.nmem (cell p j f i) := fun f hf i hi =>
    hfr _ (not_inLev hf hi (by omega) (Or.inl (by omega)))
  unfold mergeBody
  refine spec_seq ?_
  refine spec_use (recS_exec (I := I) hL c hc hR hN hj ho hos (by omega) (by omega)
    (by omega)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨e1, hK1, hrr1, hrm1, ho1⟩
  rw [hil, hir, hg] at e1
  have hR1 : RCtx p c₁ := hR.of fun r h1 h2 => hK1 r (by omega) (by omega)
  have hN1 : NCtx p j o c₁ := hN.of fun r h1 h2 => hK1 r (by omega) (by omega)
  refine spec_use (emitS_exec (I := I) hL c₁ hw₁ hR1 hN1 hj ho hos
    (by rw [hK1 354 (by omega) (by omega)]; omega) (by rw [hK1 355 (by omega) (by omega)]; omega)
    (by rw [hK1 357 (by omega) (by omega)]; omega)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨f357, hK2, hrr2, hrm2, ho2, hcase⟩
  rw [hK1 354 (by omega) (by omega), hK1 355 (by omega) (by omega),
    hK1 356 (by omega) (by omega), hK1 357 (by omega) (by omega), hil, hir, hg, hzc] at hcase
  rw [hK1 357 (by omega) (by omega), hg] at f357
  rw [hzc] at e1
  have hgs : o + g < p.s := by omega
  -- the cells written by the record
  have n12 : cell p (j + 1) 1 (o + g) ≠ cell p (j + 1) 2 (o + g) :=
    cell_ne (by omega) (by omega) hgs hgs (by omega)
  have n13 : cell p (j + 1) 1 (o + g) ≠ cell p (j + 1) 3 (o + g) :=
    cell_ne (by omega) (by omega) hgs hgs (by omega)
  have n23 : cell p (j + 1) 2 (o + g) ≠ cell p (j + 1) 3 (o + g) :=
    cell_ne (by omega) (by omega) hgs hgs (by omega)
  have hm1 : ∀ b, b ≠ cell p (j + 1) 1 (o + g) → b ≠ cell p (j + 1) 2 (o + g) →
      b ≠ cell p (j + 1) 3 (o + g) → c₁.nmem b = c.nmem b := fun b h1 h2 h3 => by
    rw [e1, upd_other _ _ _ h3, upd_other _ _ _ h2, upd_other _ _ _ h1]
  have v1 : c₁.nmem (cell p (j + 1) 1 (o + g)) = il := by
    rw [e1, upd_other _ _ _ n13, upd_other _ _ _ n12, upd_same]
  have v2 : c₁.nmem (cell p (j + 1) 2 (o + g)) = ir := by
    rw [e1, upd_other _ _ _ n23, upd_same]
  have v3 : c₁.nmem (cell p (j + 1) 3 (o + g)) = if iz = 1 then c₀.nmem (cell p j 3 (o + il))
      else c₀.nmem (cell p j 3 (o + 2 ^ j + ir)) := by
    rw [e1, upd_same]
    rcases Nat.eq_or_lt_of_le hiz' with rfl | h0
    · simp only [Ac, one_ne_zero, ↓reduceIte, lt_irrefl]
      exact hch 3 (by omega) _ (by omega)
    · have : iz = 0 := by omega
      subst this
      simp only [Ac, ↓reduceIte, show θ < p.nc + 1 by omega, zero_ne_one]
      exact hch 3 (by omega) _ (by omega)
  have hlev : ∀ f < 4, ∀ i < p.s, c₁.nmem (cell p j f i) = c₀.nmem (cell p j f i) :=
    fun f hf i hi => by
      rw [hm1 _ (cell_ne hf (by omega) hi hgs (by omega))
        (cell_ne hf (by omega) hi hgs (by omega)) (cell_ne hf (by omega) hi hgs (by omega))]
      exact hch f hf i hi
  rw [hlev 0 (by omega) _ (by omega), hlev 0 (by omega) _ (by omega)] at hcase
  -- the record of the gap `g`
  have hrec1 : GapRec p c₁.nmem c₀.nmem j o θ g := by
    refine ⟨iz, hiz', ?_, ?_, ?_, fun σ => ?_, ?_⟩
    · show c₁.nmem _ ≤ _; rw [v1]; exact hil'
    · show c₁.nmem _ ≤ _; rw [v2]; exact hir'
    · show c₁.nmem _ + c₁.nmem _ + _ = _; rw [v1, v2]; omega
    · show _ = cntP _ (c₁.nmem _) σ + cntP _ (c₁.nmem _) σ + _
      rw [v1, v2, ← hms.cnt σ]
      refine cntP_congr fun e he => ?_
      show c₁.nmem _ = c.nmem _
      have hes : o + e < p.s := by omega
      exact hm1 _ (cell_ne (by omega) (by omega) hes hgs (by omega))
        (cell_ne (by omega) (by omega) hes hgs (by omega))
        (cell_ne (by omega) (by omega) hes hgs (by omega))
    · show c₁.nmem _ = if iz = 1 then c₀.nmem _ else c₀.nmem _
      rw [v3]; unfold Arr; rw [v1, v2]
  have fin : ∀ v il' ir', c₂.nmem = upd c₁.nmem (cell p (j + 1) 0 (o + g)) v →
      c₂.nreg 354 = il' → c₂.nreg 355 = ir' →
      MS (Arr c₂.nmem p (j + 1) 0 o) (Arr c₀.nmem p j 0 o) (Arr c₀.nmem p j 0 (o + 2 ^ j))
        (Ac θ p.nc) (2 ^ j - 1) (2 ^ j - 1) 1 p.nc (g + 1) il' ir' (g + 1 - il' - ir') →
      c₂.nreg 356 = Ac θ p.nc (g + 1 - il' - ir') →
      IM p j o θ c₀ c₂ ∧
        25 * (c₂.nreg 358 - c₂.nreg 357) + (k₁ + k₂) + 2 ≤ 25 * (c.nreg 358 - c.nreg 357) := by
    intro v il' ir' hm2 h354 h355 hms' hzc'
    have n0 : ∀ f, 1 ≤ f → f < 4 → cell p (j + 1) f (o + g) ≠ cell p (j + 1) 0 (o + g) :=
      fun f h1 h2 => cell_ne (by omega) (by omega) hgs hgs (by omega)
    have k2 : ∀ r, (r < 354 ∨ 364 ≤ r) → c₂.nreg r = c.nreg r := fun r hr => by
      rw [hK2 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        hK1 r (by omega) (by omega)]
    have v358 : c₂.nreg 358 = 2 * (2 ^ j - 1) + 1 := by
      rw [hK2 358 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        hK1 358 (by omega) (by omega), h358]
    refine ⟨⟨hw₂, fun r hr => (k2 r hr).trans (hI.keep r hr), hrr2.trans (hrr1.trans hI.rr),
      hrm2.trans (hrm1.trans hI.rm), ho2.trans (ho1.trans hI.out), v358,
      by rw [f357, h354, h355]; exact hms', by rw [f357, h354, h355]; exact hzc',
      fun g' hg' => ?_, fun a ha => ?_⟩, ?_⟩
    · rw [f357] at hg'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hg' with hg' | rfl
      · have hg's : o + g' < p.s := by omega
        refine (hrec g' hg').congr (fun e he => ?_) (fun f h1 h2 => ?_)
        · have hes : o + e < p.s := by omega
          rw [hm2, upd_other _ _ _ (cell_ne (by omega) (by omega) hes hgs (by omega)),
            hm1 _ (cell_ne (by omega) (by omega) hes hgs (by omega))
              (cell_ne (by omega) (by omega) hes hgs (by omega))
              (cell_ne (by omega) (by omega) hes hgs (by omega))]
        · rw [hm2, upd_other _ _ _ (cell_ne (by omega) (by omega) hg's hgs (by omega)),
            hm1 _ (cell_ne (by omega) (by omega) hg's hgs (by omega))
              (cell_ne (by omega) (by omega) hg's hgs (by omega))
              (cell_ne (by omega) (by omega) hg's hgs (by omega))]
      · refine hrec1.congr (fun e he => ?_) (fun f h1 h2 => ?_)
        · have hes : o + e < p.s := by omega
          rw [hm2, upd_other _ _ _ (cell_ne (by omega) (by omega) hes hgs (by omega))]
        · rw [hm2, upd_other _ _ _ (n0 f h1 h2)]
    · rw [f357] at ha
      have hw : ∀ f < 4, a ≠ cell p (j + 1) f (o + g) := fun f hf e =>
        ha ⟨f, hf, o + g, by omega, by omega, e⟩
      rw [hm2, upd_other _ _ _ (hw 0 (by omega)), hm1 a (hw 1 (by omega)) (hw 2 (by omega))
        (hw 3 (by omega))]
      exact hfr a fun h => ha (h.mono (by omega))
    · rw [v358, f357, h358, hg]; omega
  have hAv : ∀ v, ∀ e < g, Arr (upd c₁.nmem (cell p (j + 1) 0 (o + g)) v) p (j + 1) 0 o e =
      Arr c.nmem p (j + 1) 0 o e := fun v e he => by
    have hes : o + e < p.s := by omega
    show upd _ _ _ _ = c.nmem _
    rw [upd_other _ _ _ (cell_ne (by omega) (by omega) hes hgs (by omega)),
      hm1 _ (cell_ne (by omega) (by omega) hes hgs (by omega))
        (cell_ne (by omega) (by omega) hes hgs (by omega))
        (cell_ne (by omega) (by omega) hes hgs (by omega))]
  have hnew : ∀ v, Arr (upd c₁.nmem (cell p (j + 1) 0 (o + g)) v) p (j + 1) 0 o g = v :=
    fun v => upd_same _ _ _
  have hlt' : g < 2 ^ j - 1 + (2 ^ j - 1) + 1 := by omega
  have hZ := lok_ac hθ
  rcases hcase with ⟨hxy, hxz, hm2, h354, h355, h356⟩ | ⟨hxy, hxz, hm2, h354, h355, h356⟩ |
    ⟨hxy, hxz, hm2, h354, h355, h356⟩
  · have := MS.emitX hl hr hZ hms hlt' (hAv (c₀.nmem (cell p j 0 (o + il))))
      (hnew (c₀.nmem (cell p j 0 (o + il)))) hxy hxz
    rw [← hm2] at this
    obtain ⟨hI', hk⟩ := fin _ _ _ hm2 h354 h355
      (by rw [show g + 1 - (il + 1) - ir = iz by omega]; exact this)
      (by rw [h356, show g + 1 - (il + 1) - ir = iz by omega])
    exact ⟨hI', by omega⟩
  · have := (MS.emitX hr hl hZ hms.swap12 (by omega)
      (hAv (c₀.nmem (cell p j 0 (o + 2 ^ j + ir))))
      (hnew (c₀.nmem (cell p j 0 (o + 2 ^ j + ir)))) hxy hxz).swap12
    rw [← hm2] at this
    obtain ⟨hI', hk⟩ := fin _ _ _ hm2 h354 h355
      (by rw [show g + 1 - il - (ir + 1) = iz by omega]; exact this)
      (by rw [h356, show g + 1 - il - (ir + 1) = iz by omega])
    exact ⟨hI', by omega⟩
  · have := (MS.emitX hZ hr hl hms.swap13 (by omega) (hAv (Ac θ p.nc iz))
      (hnew (Ac θ p.nc iz)) hxz hxy).swap13
    rw [← hm2] at this
    have hiz0 : iz = 0 := by have := this.iz_le; omega
    obtain ⟨hI', hk⟩ := fin _ _ _ hm2 h354 h355
      (by rw [show g + 1 - il - ir = iz + 1 by omega]; exact this)
      (by rw [h356, show g + 1 - il - ir = 1 by omega]; rfl)
    exact ⟨hI', by omega⟩

/-- Name the starting configuration of a spec goal. -/
theorem spec_named {W : ℕ} {s : Stmt} {c : Config} {Q : Config → ℕ → Prop}
    (h : ∀ c₁, c₁ = c → WordsBounded W c → ∃ c' k, Exec I W s c₁ c' k ∧ Q c' k)
    (hw : WordsBounded W c) : ∃ c' k, Exec I W s c c' k ∧ Q c' k := h c rfl hw

/-- The record written by `recS` is the record of the gap. -/
lemma recS_gap {j o θ g il ir iz : ℕ} {nm nm₀ nm₁ : ℕ → ℕ} (hos : o + 2 * 2 ^ j ≤ p.s)
    (hg : g < 2 * 2 ^ j)
    (hms : MS (Arr nm p (j + 1) 0 o) (Arr nm₀ p j 0 o) (Arr nm₀ p j 0 (o + 2 ^ j)) (Ac θ p.nc)
      (2 ^ j - 1) (2 ^ j - 1) 1 p.nc g il ir iz) (hθ : θ ≤ p.nc)
    (hch : ∀ f < 4, ∀ i < p.s, nm (cell p j f i) = nm₀ (cell p j f i))
    (e1 : nm₁ = upd (upd (upd nm (cell p (j + 1) 1 (o + g)) il) (cell p (j + 1) 2 (o + g)) ir)
      (cell p (j + 1) 3 (o + g)) (if Ac θ p.nc iz < p.nc + 1 then
        nm (cell p j 3 (o + 2 ^ j + ir)) else nm (cell p j 3 (o + il)))) :
    GapRec p nm₁ nm₀ j o θ g := by
  have hil' := hms.ix_le; have hir' := hms.iy_le; have hiz' := hms.iz_le; have hge := hms.g_eq
  have hgs : o + g < p.s := by omega
  have n12 : cell p (j + 1) 1 (o + g) ≠ cell p (j + 1) 2 (o + g) :=
    cell_ne (by omega) (by omega) hgs hgs (by omega)
  have n13 : cell p (j + 1) 1 (o + g) ≠ cell p (j + 1) 3 (o + g) :=
    cell_ne (by omega) (by omega) hgs hgs (by omega)
  have n23 : cell p (j + 1) 2 (o + g) ≠ cell p (j + 1) 3 (o + g) :=
    cell_ne (by omega) (by omega) hgs hgs (by omega)
  have hm1 : ∀ b, b ≠ cell p (j + 1) 1 (o + g) → b ≠ cell p (j + 1) 2 (o + g) →
      b ≠ cell p (j + 1) 3 (o + g) → nm₁ b = nm b := fun b h1 h2 h3 => by
    rw [e1, upd_other _ _ _ h3, upd_other _ _ _ h2, upd_other _ _ _ h1]
  have v1 : nm₁ (cell p (j + 1) 1 (o + g)) = il := by
    rw [e1, upd_other _ _ _ n13, upd_other _ _ _ n12, upd_same]
  have v2 : nm₁ (cell p (j + 1) 2 (o + g)) = ir := by
    rw [e1, upd_other _ _ _ n23, upd_same]
  have v3 : nm₁ (cell p (j + 1) 3 (o + g)) = if iz = 1 then nm₀ (cell p j 3 (o + il))
      else nm₀ (cell p j 3 (o + 2 ^ j + ir)) := by
    rw [e1, upd_same]
    rcases Nat.eq_or_lt_of_le hiz' with rfl | h0
    · simp only [Ac, one_ne_zero, ↓reduceIte, lt_irrefl]
      exact hch 3 (by omega) _ (by omega)
    · have : iz = 0 := by omega
      subst this
      simp only [Ac, ↓reduceIte, show θ < p.nc + 1 by omega, zero_ne_one]
      exact hch 3 (by omega) _ (by omega)
  refine ⟨iz, hiz', ?_, ?_, ?_, fun σ => ?_, ?_⟩
  · show nm₁ _ ≤ _; rw [v1]; exact hil'
  · show nm₁ _ ≤ _; rw [v2]; exact hir'
  · show nm₁ _ + nm₁ _ + _ = _; rw [v1, v2]; omega
  · show _ = cntP _ (nm₁ _) σ + cntP _ (nm₁ _) σ + _
    rw [v1, v2, ← hms.cnt σ]
    refine cntP_congr fun e he => ?_
    show nm₁ _ = nm _
    have hes : o + e < p.s := by omega
    exact hm1 _ (cell_ne (by omega) (by omega) hes hgs (by omega))
      (cell_ne (by omega) (by omega) hes hgs (by omega))
      (cell_ne (by omega) (by omega) hes hgs (by omega))
  · show nm₁ _ = if iz = 1 then nm₀ _ else nm₀ _
    rw [v3]; unfold Arr; rw [v1, v2]

set_option maxHeartbeats 1000000 in
/-- **The merge of a node**: after `thrS` (the threshold `θ = r327`), the node of height `j + 1`
at `o` is correct, within `50 · 2 ^ j + 20` steps; only the cells of the level `j + 1` at the
indices `[o, o + 2 ^ (j + 1))` and the registers `r354 … r363` are written. -/
theorem merge_exec (hL : RMLay p) {j o : ℕ} (c : Config) (hc : WordsBounded p.W c)
    (hR : RCtx p c) (hN : NCtx p j o c) (hj : j + 1 ≤ p.T) (ho : 2 ^ (j + 1) ∣ o)
    (hos : o < p.s) (hC : ChildOK (rmF c.rmem p) p c.nmem j o) (hθ : c.nreg 327 ≤ p.nc)
    (hlo : ∀ σ < c.nreg 327, Pw (rmF c.rmem p) c.nmem p j o σ)
    (hhi : ∀ σ, c.nreg 327 ≤ σ → σ < p.nc → ¬ Pw (rmF c.rmem p) c.nmem p j o σ) :
    ∃ c' k, Exec I p.W merge c c' k ∧ k ≤ 50 * 2 ^ j + 20 ∧
      (NodeOK (rmF c.rmem p) p c'.nmem (j + 1) o ∧
        (∀ a, ¬ InLev p (j + 1) o (o + 2 ^ (j + 1)) a → c'.nmem a = c.nmem a) ∧
        (∀ r, (r < 354 ∨ 364 ≤ r) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hW := W_bound hL
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have hpos := Nat.one_le_two_pow (n := j)
  have hds := off_le ho (pow_dvd_s hj) hos
  have hs : p.s ≤ p.W := by have := hL.wB; nlinarith
  obtain ⟨hl, hr⟩ := hC
  generalize hθd : c.nreg 327 = θ at hθ hlo hhi
  unfold merge
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  · omega
  · config_simp; rw [hN.r331]; omega
  refine spec_named (fun c₁ hc₁ hw₁ => ?_) ‹_›
  rw [← hc₁] at hw₁
  have hI₀ : IM p j o θ c c₁ := ⟨hw₁, fun r hr => by rw [hc₁]; config_simp; upd_tac,
    by rw [hc₁], by rw [hc₁], by rw [hc₁],
    by rw [hc₁]; config_simp; rw [hN.r331, hR.r308]; omega,
    by rw [hc₁]; config_simp; exact MS.init,
    by rw [hc₁]; config_simp; rw [hθd]; rfl,
    fun g hg => by rw [hc₁] at hg; config_simp at hg; omega,
    fun a _ => by rw [hc₁]⟩
  have h357 : c₁.nreg 357 = 0 := by rw [hc₁]; config_simp
  have h358 := hI₀.r358
  clear hc₁
  refine spec_seq ?_
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := I) (W := p.W) (a := 357)
    (b := 358) (body := mergeBody) (fun c' => IM p j o θ c c')
    (fun c' => 25 * (c'.nreg 358 - c'.nreg 357)) (fun _ h => h.wb)
    (fun c' hI' hlt => mergeBody_exec hL hR hN hj ho hos hθ hl.1 hr.1 c' hI' hlt) hI₀
  refine ⟨c₂, k₂, e₂, ?_⟩
  have hw₂ := hI₂.wb
  have hR2 : RCtx p c₂ := hR.of fun r h1 h2 => hI₂.keep r (by omega)
  have hN2 : NCtx p j o c₂ := hN.of fun r h1 h2 => hI₂.keep r (by omega)
  have hms := hI₂.ms
  have hzc := hI₂.zc
  rw [hI₂.r358] at hn₂
  generalize hil : c₂.nreg 354 = il at hms hzc
  generalize hir : c₂.nreg 355 = ir at hms hzc
  generalize hg : c₂.nreg 357 = g at hms hzc hn₂
  generalize hiz : g - il - ir = iz at hms hzc
  have hil' := hms.ix_le; have hir' := hms.iy_le; have hiz' := hms.iz_le; have hge := hms.g_eq
  have hgm : g = 2 * (2 ^ j - 1) + 1 := by omega
  have hch : ∀ f < 4, ∀ i < p.s, c₂.nmem (cell p j f i) = c.nmem (cell p j f i) :=
    fun f hf i hi => hI₂.fr _ (not_inLev hf hi (by omega) (Or.inl (by omega)))
  refine spec_seq ?_
  refine spec_use (recS_exec (I := I) hL c₂ hw₂ hR2 hN2 hj ho hos (by omega) (by omega)
    (by omega)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨e3, hK3, hrr3, hrm3, ho3⟩
  rw [hil, hir, hg, hzc] at e3
  have hgap := recS_gap (by omega) (by omega) hms hθ hch e3
  have hgs : o + g < p.s := by omega
  have hR3 : RCtx p c₃ := hR2.of fun r h1 h2 => hK3 r (by omega) (by omega)
  have hN3 : NCtx p j o c₃ := hN2.of fun r h1 h2 => hK3 r (by omega) (by omega)
  have v357 : c₃.nreg 357 = g := by rw [hK3 357 (by omega) (by omega), hg]
  have bA := cell_lt (p := p) (j := j + 1) (f := 0) (i := o + g) hj (by omega) hgs
  have eA : c₃.nreg 338 + c₃.nreg 357 = cell p (j + 1) 0 (o + g) := by
    rw [hN3.r338, v357, cell_add]
  -- the memory at the end
  have key : ∀ nm₄ : ℕ → ℕ, nm₄ = upd c₃.nmem (cell p (j + 1) 0 (o + g)) (p.nc + 1) →
      NodeOK (rmF c.rmem p) p nm₄ (j + 1) o ∧
        ∀ a, ¬ InLev p (j + 1) o (o + 2 ^ (j + 1)) a → nm₄ a = c.nmem a := by
    intro nm₄ hm4
    have hrd : ∀ b, (∀ f < 4, b ≠ cell p (j + 1) f (o + g)) → nm₄ b = c₂.nmem b :=
      fun b hb => by
        rw [hm4, upd_other _ _ _ (hb 0 (by omega)), e3, upd_other _ _ _ (hb 3 (by omega)),
          upd_other _ _ _ (hb 2 (by omega)), upd_other _ _ _ (hb 1 (by omega))]
    have h0 : ∀ e < g, nm₄ (cell p (j + 1) 0 (o + e)) = c₂.nmem (cell p (j + 1) 0 (o + e)) :=
      fun e he => hrd _ fun f hf => cell_ne (by omega) hf (by omega) hgs (by omega)
    have hlev : ∀ f < 4, ∀ i < p.s, nm₄ (cell p j f i) = c.nmem (cell p j f i) :=
      fun f hf i hi => by
        rw [hrd _ fun f' hf' => cell_ne hf hf' hi hgs (by omega)]; exact hch f hf i hi
    have hil0 : il = 2 ^ j - 1 := by omega
    have hir0 : ir = 2 ^ j - 1 := by omega
    have hiz0 : iz = 1 := by omega
    subst hil0 hir0 hiz0
    have hM := hms.congr (Av' := Arr nm₄ p (j + 1) 0 o) h0
    rw [hgm] at hM
    have hgap' : ∀ g' ≤ 2 * (2 ^ j - 1) + 1, GapRec p nm₄ c.nmem j o θ g' := by
      intro g' hg'
      rcases Nat.lt_or_ge g' g with hlt | hge'
      · have hg's : o + g' < p.s := by omega
        refine (hI₂.recs g' (by rw [hg]; exact hlt)).congr (fun e he => ?_) (fun f h1 h2 => ?_)
        · exact h0 e (by omega)
        · exact hrd _ fun f' hf' => cell_ne (by omega) hf' hg's hgs (by omega)
      · have : g' = g := by omega
        subst this
        refine hgap.congr (fun e he => ?_) (fun f h1 h2 => ?_)
        · rw [hm4, upd_other _ _ _ (cell_ne (by omega) (by omega) (by omega) hgs (by omega))]
        · rw [hm4, upd_other _ _ _ (cell_ne (by omega) (by omega) hgs hgs (by omega))]
    have hsent : Arr nm₄ p (j + 1) 0 o (2 * (2 ^ j - 1) + 1) = p.nc + 1 := by
      show nm₄ _ = _; rw [hm4, ← hgm, upd_same]
    obtain ⟨hlok, hσ⟩ := node_ok (F := rmF c.rmem p) (GL := Arr nm₄ p (j + 1) 1 o)
      (GR := Arr nm₄ p (j + 1) 2 o) (RV := Arr nm₄ p (j + 1) 3 o) (RL := Arr c.nmem p j 3 o)
      (RR := Arr c.nmem p j 3 (o + 2 ^ j))
      (fun σ hσ => by
        rw [show o + (2 ^ j - 1 + 1) = o + 2 ^ j by omega]; exact (hl.2 σ hσ).1)
      (fun σ hσ => by
        rw [show o + (2 ^ j - 1 + 1) = o + 2 ^ j by omega,
          show o + 2 * (2 ^ j - 1 + 1) = o + 2 ^ j + 2 ^ j by omega]
        exact (hr.2 σ hσ).1)
      (fun σ hσ => hlo σ hσ) (fun σ h1 h2 => hhi σ h1 h2) hM hsent hgap'
    have e2 : 2 ^ (j + 1) - 1 = 2 * (2 ^ j - 1) + 1 := by omega
    refine ⟨⟨by rw [e2]; exact hlok, fun σ hσ' => ?_⟩, fun a ha => ?_⟩
    · obtain ⟨b1, b2, b3⟩ := hσ σ hσ'
      unfold gapAt
      rw [e2]
      refine ⟨by rw [show o + 2 ^ (j + 1) = o + 2 * (2 ^ j - 1 + 1) by omega]; exact b1,
        fun j' hj' => ?_⟩
      have : j' = j := by omega
      subst this
      rw [b2, b3]
      exact ⟨(gapAt_congr fun e he => hlev 0 (by omega) _ (by omega)).symm,
        (gapAt_congr fun e he => hlev 0 (by omega) _ (by omega)).symm⟩
    · rw [hrd a fun f hf e => ha ⟨f, hf, o + g, by omega, by omega, e⟩]
      exact hI₂.fr a fun h => ha (h.mono (by omega))
  exec_block
  · omega
  obtain ⟨hok, hfr4⟩ := key _ rfl
  have hm : upd c₃.nmem (c₃.nreg 338 + c₃.nreg 357) (c₃.nreg 310) =
      upd c₃.nmem (cell p (j + 1) 0 (o + g)) (p.nc + 1) := by rw [eA, hR3.r310]
  rw [h357, h358] at hk₂
  refine ⟨by omega, by config_simp; rw [hm]; exact hok, by config_simp; rw [hm]; exact hfr4,
    fun r hr => ?_, ?_, ?_, ?_⟩
  · config_simp
    rw [upd_other _ _ _ (by omega), hK3 r (by omega) (by omega)]; exact hI₂.keep r hr
  · config_simp; rw [hrr3, hI₂.rr]
  · config_simp; rw [hrm3, hI₂.rm]
  · config_simp; rw [ho3, hI₂.out]

/-! ### The leaves -/

/-- One leaf `o = r350`: `A₀[o] := nc + 1`, `ROW₀[o] := o`. -/
def leafBody : Stmt :=
  block [.addN 351 300 350, .storeN 351 310, .addN 351 351 301, .addN 351 351 301,
    .addN 351 351 301, .storeN 351 350, .addN 350 350 308]

/-- **The leaves.** -/
def leaves : Stmt := .seq (.instr (.constN 350 0)) (.whileLtN 350 301 leafBody)

/-- A leaf is a correct node. -/
lemma leaf_ok {F : ℕ → ℕ → ℝ} {nm : ℕ → ℕ} {o : ℕ} (h0 : nm (cell p 0 0 o) = p.nc + 1)
    (h3 : nm (cell p 0 3 o) = o) : NodeOK F p nm 0 o := by
  refine ⟨⟨fun e he => by simp at he, by simpa [Arr] using h0, fun e he => by simp at he⟩,
    fun σ _ => ⟨?_, fun j' hj => by omega⟩⟩
  have : Arr nm p 0 3 o (gapAt nm p 0 o σ) = o := by
    simp only [gapAt, pow_zero, Nat.sub_self, cntP, Arr, Nat.add_zero]; exact h3
  rw [this]
  exact ⟨le_rfl, by simp, fun ρ' h1 h2 => by rw [show ρ' = o by simp at h2; omega]⟩

/-- The state of the loop of the leaves. -/
structure ILf (p : RMP) (c₀ c : Config) : Prop where
  wb : WordsBounded p.W c
  keep : ∀ r, r ≠ 350 → r ≠ 351 → c.nreg r = c₀.nreg r
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
  le : c.nreg 350 ≤ p.s
  ok : ∀ o < c.nreg 350, c.nmem (cell p 0 0 o) = p.nc + 1 ∧ c.nmem (cell p 0 3 o) = o
  fr : ∀ a, ¬ InLev p 0 0 (c.nreg 350) a → c.nmem a = c₀.nmem a

theorem leafBody_exec (hL : RMLay p) {c₀ : Config} (hR₀ : RCtx p c₀) (c : Config)
    (hI : ILf p c₀ c) (hlt : c.nreg 350 < c.nreg 301) :
    ∃ c' k, Exec I p.W leafBody c c' k ∧ ILf p c₀ c' ∧
      9 * (p.s - c'.nreg 350) + k + 2 ≤ 9 * (p.s - c.nreg 350) := by
  have hc := hI.wb
  have hR : RCtx p c := hR₀.of fun r h1 h2 => hI.keep r (by omega) (by omega)
  have hW := W_bound hL
  have hs : p.s ≤ p.W := by have := hL.wB; nlinarith
  rw [hR.r301] at hlt
  generalize ho : c.nreg 350 = o at hlt
  have b3 := cell_lt (p := p) (j := 0) (f := 3) (i := o) (by omega) (by omega) hlt
  have e0 : cell p 0 0 o = p.B + o := by unfold cell; ring
  have e3 : cell p 0 3 o = cell p 0 0 o + p.s + p.s + p.s := by unfold cell; ring
  have n03 : cell p 0 3 o ≠ cell p 0 0 o := cell_ne (by omega) (by omega) hlt hlt (by omega)
  unfold leafBody
  exec_block
  · rw [hR.r300, ho]; omega
  · config_simp; rw [hR.r300, ho, hR.r301]; omega
  · config_simp; rw [hR.r300, ho, hR.r301]; omega
  · config_simp; rw [hR.r300, ho, hR.r301]; omega
  · config_simp; rw [hR.r308, ho]; omega
  have hok := hI.ok; have hfr := hI.fr
  rw [ho] at hok hfr
  have ea : c.nreg 300 + c.nreg 350 = cell p 0 0 o := by rw [hR.r300, ho, e0]
  have eb : cell p 0 0 o + c.nreg 301 + c.nreg 301 + c.nreg 301 = cell p 0 3 o := by
    rw [hR.r301, e3]
  refine ⟨⟨‹_›, fun r h1 h2 => ?_, hI.rr, hI.rm, hI.out,
    by config_simp; rw [hR.r308, ho]; omega, fun o' ho' => ?_, fun a ha => ?_⟩,
    by config_simp; rw [hR.r308, ho]; omega⟩
  · config_simp; simp only [upd_apply, h1, h2, ite_false]; exact hI.keep r h1 h2
  · config_simp at ho'
    rw [hR.r308, ho] at ho'
    config_simp
    rw [ea, eb, hR.r310, ho]
    rcases Nat.lt_succ_iff_lt_or_eq.1 ho' with h | rfl
    · have h's : o' < p.s := by omega
      rw [upd_other _ _ _ (cell_ne (by omega) (by omega) h's hlt (by omega)),
        upd_other _ _ _ (cell_ne (by omega) (by omega) h's hlt (by omega)),
        upd_other _ _ _ (cell_ne (by omega) (by omega) h's hlt (by omega)),
        upd_other _ _ _ (cell_ne (by omega) (by omega) h's hlt (by omega))]
      exact hok o' h
    · rw [upd_other _ _ _ n03.symm, upd_same, upd_same]; exact ⟨rfl, rfl⟩
  · config_simp at ha
    rw [hR.r308, ho] at ha
    have h0 : a ≠ cell p 0 0 o := fun e => ha ⟨0, by omega, o, by omega, by omega, e⟩
    have h3 : a ≠ cell p 0 3 o := fun e => ha ⟨3, by omega, o, by omega, by omega, e⟩
    config_simp
    rw [ea, eb, upd_other _ _ _ h3, upd_other _ _ _ h0]
    exact hfr a fun h => ha (h.mono (by omega))

/-- **The leaves**: within `9 s + 3` steps, `A₀[o] = nc + 1` and `ROW₀[o] = o` for all `o < s`;
only the cells of the level `0` and the registers `r350`, `r351` are written. -/
theorem leaves_exec (hL : RMLay p) (c : Config) (hc : WordsBounded p.W c) (hR : RCtx p c) :
    ∃ c' k, Exec I p.W leaves c c' k ∧ k ≤ 9 * p.s + 3 ∧
      ((∀ o < p.s, c'.nmem (cell p 0 0 o) = p.nc + 1 ∧ c'.nmem (cell p 0 3 o) = o) ∧
        (∀ a, ¬ InLev p 0 0 p.s a → c'.nmem a = c.nmem a) ∧
        (∀ r, r ≠ 350 → r ≠ 351 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold leaves
  refine spec_seq ?_
  refine spec_instr (Exec.constN hc 350 0 (by omega)) fun hw₁ => ?_
  have hI₀ : ILf p c { c with nreg := upd c.nreg 350 0 } :=
    ⟨hw₁, fun r h1 h2 => by config_simp; upd_tac, rfl, rfl, rfl, by config_simp; omega,
      fun o ho => by config_simp at ho; omega, fun a _ => rfl⟩
  obtain ⟨c', k, e, hI, hn, hk⟩ := Exec.whileLtN_potential (P := I) (W := p.W) (a := 350)
    (b := 301) (body := leafBody) (fun c' => ILf p c c')
    (fun c' => 9 * (p.s - c'.nreg 350)) (fun _ h => h.wb)
    (fun c' hI' hlt => leafBody_exec hL hR c' hI' hlt) hI₀
  have h301 : c'.nreg 301 = p.s := (hI.keep 301 (by omega) (by omega)).trans hR.r301
  have hle := hI.le
  have hs : c'.nreg 350 = p.s := by omega
  refine ⟨c', k, e, by config_simp at hk; omega, fun o ho => hI.ok o (by omega),
    fun a ha => hI.fr a (by rw [hs]; exact ha), hI.keep, hI.rr, hI.rm, hI.out⟩

end RM

end Monge

end PlanarFlow
