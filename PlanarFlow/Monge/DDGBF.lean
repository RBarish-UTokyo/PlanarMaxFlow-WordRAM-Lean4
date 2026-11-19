module

public import PlanarFlow.Monge.SmawkRun
public import PlanarFlow.Monge.Round

/-!
# Bellman–Ford over a dense distance graph on the machine

The input is a dense distance graph on the vertices `0, …, b - 1` of a face, its lengths
`D i j` stored in the real memory at `Db + i b + j` and satisfying the crossing inequality
(`PlanarFlow.Monge.Crossing`). The program `bfDDG` runs `b + 1` rounds of Bellman–Ford from the
values `0` (a virtual source joined to every vertex), keeping the values `e v` in the real memory
at `eb + v`. A round processes the dyadic blocks level by level (`PlanarFlow.Monge.InBlock`); a
block is two *half blocks*, the relaxation of all the arcs from one half to the other, and a half
block is one call of the row-minima program `PlanarFlow.Monge.smawk` (SMAWK) on its Monge matrix
`e i + D i t` (entry oracle `entBF`), followed by the update of its targets. The flag `r30`
records whether a value changed during the round.

**`PlanarFlow.Monge.bfDDG_exec`.** After the run, `r30 = 0` and the values form a feasible
potential of the dense distance graph, or `r30 = 1` and the dense distance graph has no feasible
potential (equivalently a closed walk of negative length,
`PlanarFlow.Digraph.exists_pot_iff`); if a feasible potential exists, the values are the
Bellman–Ford values `bf b` (the distances from the virtual source). A round costs
`O(b log b)` steps (each level `O(b)`), the whole run `O(b² log b)`.

Memory: the row-minima cells at `pb + 1 … pb + 5b + 1` (natural and real), the values at
`eb … eb + b - 1`, the lengths at `Db … Db + b² - 1` (real), with `pb + b < eb`, `eb + b ≤ Db`.
Registers: `r1 = b`, `r2 = Db`, `r3 = eb`, `r4 = pb` (inputs, kept), `r10 = 1` and the real
`r10 = 0`, `r12, r13` (initialization), `r14` the round, `r15 = b + 1`, `r20 = s` the level,
`r21` the start of the block, `r22 = r21 + s`, `r23` its end, `r24` the first target and `r25`
one past the last source of a half block, `r26 … r29` and the reals `r20, r21` (update), `r30`
the flag; `r60 …` belong to `smawk` and `r80 …` to the oracle. The row minima use the scratch
cells `pb + 1 … pb + 4 nr + nc + 1` (`nr, nc ≤ b`), below `eb`.

## References

* P. N. Klein, S. Mozes, O. Weimann, *Shortest paths in directed planar graphs with negative
  lengths: a linear-space `O(n log² n)`-time algorithm*, ACM Trans. Algorithms 6 (2010), 30.
* J. Fakcharoenphol, S. Rao, *Planar graphs, negative weight edges, shortest paths, and near
  linear time*, J. Comput. Syst. Sci. 72 (2006), 868–889.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The program -/

/-- The entry oracle of a half block: for the row `r70` and the column `r71` it leaves
`e i + D i t` in the real `r70`, for the source `i = r25 - 1 - r71` and the target
`t = r24 + r70`. -/
def entBF : Stmt := block [.subN 80 25 10, .subN 80 80 71, .addN 81 24 70, .addN 82 3 80,
  .loadR 80 82, .mulN 83 80 1, .addN 83 83 81, .addN 83 83 2, .loadR 81 83, .addR 70 80 81]

/-- One step of the update of a half block: lower the target `r24 + r26` to the minimum of the
row `r26`. -/
def updBody : Stmt :=
  .seq (block [.addN 27 24 26, .addN 28 3 27, .addN 29 4 26, .addN 29 29 10, .loadR 20 29,
      .loadR 21 28])
    (.seq (.ifLtR 20 21 (block [.storeR 28 20, .constN 30 1]) .skip) (.instr (.addN 26 26 10)))

/-- A half block: the row minima of the block matrix (targets from `r24`, `r60` of them; sources
below `r25`, `r61` of them), then the update of the targets. -/
def half : Stmt :=
  .seq (.instr (.copyN 62 4)) <| .seq (smawk entBF) <| .seq (.instr (.constN 26 0))
    (.whileLtN 26 60 updBody)

/-- A block `[r21, r21 + 2s)`: both halves. -/
def blockBody : Stmt :=
  .seq (.instr (.addN 23 22 20)) <| .seq (.ifLtN 1 23 (.instr (.copyN 23 1)) .skip) <|
  .seq (block [.copyN 24 22, .copyN 25 22, .subN 60 23 22, .copyN 61 20]) <| .seq half <|
  .seq (block [.copyN 24 21, .copyN 25 23, .copyN 60 20, .subN 61 23 22]) <| .seq half <|
  block [.addN 21 21 20, .addN 21 21 20, .addN 22 21 20]

/-- A level `s = r20`: all its blocks, then `s := 2s`. -/
def levelBF : Stmt :=
  .seq (block [.constN 21 0, .copyN 22 20]) (.seq (.whileLtN 22 1 blockBody) (.instr (.addN 20 20 20)))

/-- A round: all the levels. -/
def roundBF : Stmt :=
  .seq (block [.constN 20 1, .constN 30 0]) (.seq (.whileLtN 20 1 levelBF) (.instr (.addN 14 14 10)))

/-- One value set to `0`. -/
def initBody : Stmt := block [.addN 13 3 12, .storeR 13 10, .addN 12 12 10]

/-- **Bellman–Ford over a dense distance graph.** -/
def bfDDG : Stmt :=
  .seq (block [.constN 10 1, .constR 10 0, .constN 12 0, .addN 15 1 10, .constN 14 0,
    .constN 30 0]) <|
  .seq (.whileLtN 12 1 initBody) (.whileLtN 14 15 roundBF)

/-! ### The fixed data -/

/-- The fixed registers and the stored lengths. -/
structure Env (b Db eb pb : ℕ) (D : ℕ → ℕ → ℤ) (c : Config) : Prop where
  r1 : c.nreg 1 = b
  r2 : c.nreg 2 = Db
  r3 : c.nreg 3 = eb
  r4 : c.nreg 4 = pb
  r10 : c.nreg 10 = 1
  z10 : c.rreg 10 = 0
  dmem : ∀ i j, i < b → j < b → c.rmem (Db + i * b + j) = D i j

/-- The layout of the memory and the word bound. -/
structure Lay (b Db eb pb W : ℕ) : Prop where
  pe : pb + 5 * b + 1 < eb
  ed : eb + b ≤ Db
  w : Db + b * b + 4 * b + 10 ≤ W

/-- The values `E` are stored at `eb`. -/
def Vals (b eb : ℕ) (E : ℕ → ℤ) (c : Config) : Prop := ∀ v < b, c.rmem (eb + v) = E v

theorem Env.of {b Db eb pb : ℕ} {D : ℕ → ℕ → ℤ} {c c' : Config} (h : Env b Db eb pb D c)
    (hn : ∀ r, r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 10 → c'.nreg r = c.nreg r)
    (hr : c'.rreg 10 = c.rreg 10) (hm : ∀ a, Db ≤ a → c'.rmem a = c.rmem a) :
    Env b Db eb pb D c' :=
  ⟨(hn 1 (by omega)).trans h.r1, (hn 2 (by omega)).trans h.r2, (hn 3 (by omega)).trans h.r3,
    (hn 4 (by omega)).trans h.r4, (hn 10 (by omega)).trans h.r10, hr.trans h.z10,
    fun i j hi hj => (hm _ (by omega)).trans (h.dmem i j hi hj)⟩

/-- The matrix of a half block, in `ℝ`. -/
def blkR (D : ℕ → ℕ → ℤ) (E : ℕ → ℤ) (r0 c1 : ℕ) (ρ κ : ℕ) : ℝ := (blk D E r0 c1 ρ κ : ℤ)

variable {P : Input} {W : ℕ} {b Db eb pb : ℕ} {D : ℕ → ℕ → ℤ}

/-- **The entry oracle.** -/
theorem entBF_exec (hL : Lay b Db eb pb W) {E : ℕ → ℤ} {r0 nr c1 nc : ℕ} {c₀ : Config}
    (hE : Env b Db eb pb D c₀) (hV : Vals b eb E c₀) (h24 : c₀.nreg 24 = r0)
    (h25 : c₀.nreg 25 = c1) (hnc : nc ≤ c1) (hc1 : c1 ≤ b) (hr : r0 + nr ≤ b) :
    EntSpecK P W entBF (blkR D E r0 c1) 10 nr nc pb (4 * nr + nc + 1) c₀ := by
  intro c hc hA h70 h71
  obtain ⟨a1, a2, a3, a4, a5⟩ := hA
  have g1 : c.nreg 1 = b := (a1 1 (by omega)).trans hE.r1
  have g2 : c.nreg 2 = Db := (a1 2 (by omega)).trans hE.r2
  have g3 : c.nreg 3 = eb := (a1 3 (by omega)).trans hE.r3
  have g10 : c.nreg 10 = 1 := (a1 10 (by omega)).trans hE.r10
  have g24 : c.nreg 24 = r0 := (a1 24 (by omega)).trans h24
  have g25 : c.nreg 25 = c1 := (a1 25 (by omega)).trans h25
  have hLw := hL.w
  have hLe := hL.ed
  generalize hρ : c.nreg 70 = ρ at h70
  generalize hκ : c.nreg 71 = κ at h71
  have hsrc : c1 - 1 - κ < b := by omega
  have hsb : (c1 - 1 - κ) * b + b ≤ b * b := by
    have := Nat.mul_le_mul_right b (show c1 - 1 - κ + 1 ≤ b by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  unfold entBF
  exec_block
  · config_simp; rw [g24, hρ]; omega
  · config_simp; rw [g3, g25, g10, hκ]; omega
  · config_simp; rw [g25, g10, hκ, g1]; omega
  · config_simp; rw [g25, g10, hκ, g1, g24, hρ]; omega
  · config_simp; rw [g25, g10, hκ, g1, g24, hρ, g2]; omega
  refine ⟨le_refl _, ?_, fun r hr => ?_, fun r hr h => ?_, rfl, rfl, rfl⟩
  · config_simp
    rw [g25, g10, hκ, g1, g24, hρ, g2, g3]
    have e1 : c.rmem (eb + (c1 - 1 - κ)) = E (c1 - 1 - κ) := by
      rw [a4 _ (Or.inr (by have := hL.pe; omega))]; exact hV _ hsrc
    have e2 : c.rmem ((c1 - 1 - κ) * b + (r0 + ρ) + Db) = D (c1 - 1 - κ) (r0 + ρ) := by
      rw [a4 _ (Or.inr (by have := hL.pe; omega)),
        show (c1 - 1 - κ) * b + (r0 + ρ) + Db = Db + (c1 - 1 - κ) * b + (r0 + ρ) by ring]
      exact hE.dmem _ _ hsrc (by omega)
    simp only [blkR, blk, Int.cast_add]
    rw [← e1, ← e2]
  · config_simp; upd_tac
  · config_simp; upd_tac

/-! ### The update of a half block -/

/-- The row minimum of the row `ρ` of a half block, in `ℤ`. -/
noncomputable def Vrow (D : ℕ → ℕ → ℤ) (E : ℕ → ℤ) (r0 c1 nc ρ : ℕ) : ℤ :=
  blk D E r0 c1 ρ (lmin nc (blkR D E r0 c1) ρ)

/-- The arcs of a half block processed so far: from the sources `c1 - nc ≤ i < c1` to the
targets `r0 ≤ j < r0 + ρ`. -/
def HalfArcs (r0 c1 nc ρ : ℕ) (i j : ℕ) : Prop := c1 - nc ≤ i ∧ i < c1 ∧ r0 ≤ j ∧ j < r0 + ρ

/-- The state of the update of a half block, started from `c₁` with the values `E₁`. -/
structure IUp (b eb : ℕ) (D : ℕ → ℕ → ℤ) (W k : ℕ) (C : ℕ → ℕ → Prop) (E₀ E₁ : ℕ → ℤ)
    (r0 nr c1 nc : ℕ) (c₁ c : Config) : Prop where
  wb : WordsBounded W c
  nreg : ∀ r, r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → c.nreg r = c₁.nreg r
  rreg : ∀ r, r ≠ 20 → r ≠ 21 → c.rreg r = c₁.rreg r
  nmem : c.nmem = c₁.nmem
  rmem : ∀ a, (a < eb + r0 ∨ eb + r0 + nr ≤ a) → c.rmem a = c₁.rmem a
  out : c.output = c₁.output
  ρ : c.nreg 26 ≤ nr
  vals : ∃ E, Vals b eb E c ∧
    RoundOK b D k (fun i j => C i j ∨ HalfArcs r0 c1 nc (c.nreg 26) i j) E₀ E (c.nreg 30) ∧
    ∀ v < b, (v < r0 ∨ r0 + c.nreg 26 ≤ v) → E v = E₁ v

theorem updBody_exec (hL : Lay b Db eb pb W) {k : ℕ} {C : ℕ → ℕ → Prop} {E₀ E₁ : ℕ → ℤ}
    {r0 nr c1 nc : ℕ} {c₁ : Config} (hE₁ : Env b Db eb pb D c₁) (h24 : c₁.nreg 24 = r0)
    (h60 : c₁.nreg 60 = nr) (hnc : 1 ≤ nc) (hnc' : nc ≤ c1) (hc1 : c1 ≤ b) (hr : r0 + nr ≤ b)
    (hsep : r0 + nr ≤ c1 - nc ∨ c1 ≤ r0)
    (hrow : ∀ ρ < nr, c₁.rmem (pb + ρ + 1) = Vrow D E₁ r0 c1 nc ρ)
    (c : Config) (hI : IUp b eb D W k C E₀ E₁ r0 nr c1 nc c₁ c) (hlt : c.nreg 26 < c.nreg 60) :
    ∃ c' k', Exec P W updBody c c' k' ∧ IUp b eb D W k C E₀ E₁ r0 nr c1 nc c₁ c' ∧
      12 * (nr - c'.nreg 26) + k' + 2 ≤ 12 * (nr - c.nreg 26) := by
  have hc := hI.wb
  have hLw := hL.w
  have hpe := hL.pe
  have hed := hL.ed
  have g : ∀ r, r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → c.nreg r = c₁.nreg r := hI.nreg
  have g3 : c.nreg 3 = eb := (g 3 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hE₁.r3
  have g4 : c.nreg 4 = pb := (g 4 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hE₁.r4
  have g10 : c.nreg 10 = 1 :=
    (g 10 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hE₁.r10
  have g24 : c.nreg 24 = r0 := (g 24 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h24
  rw [g 60 (by omega) (by omega) (by omega) (by omega) (by omega), h60] at hlt
  generalize hρ : c.nreg 26 = ρ at hlt
  have hρI := hI.ρ
  rw [hρ] at hρI
  obtain ⟨E, hV, hR, hE⟩ := hI.vals
  rw [hρ] at hR hE
  -- the row minimum and the current value of the target
  have hrowc : c.rmem (pb + ρ + 1) = Vrow D E₁ r0 c1 nc ρ := by
    rw [hI.rmem _ (Or.inl (by omega))]; exact hrow ρ hlt
  have htc : c.rmem (eb + (r0 + ρ)) = E (r0 + ρ) := hV _ (by omega)
  -- the sources keep their values
  have hsrc : ∀ i, c1 - nc ≤ i → i < c1 → E i = E₁ i := fun i h1 h2 => hE i (by omega) (by omega)
  have hS : ∀ i, (c1 - nc ≤ i ∧ i < c1) → i < b ∧ i ≠ r0 + ρ := fun i hi => ⟨by omega, by omega⟩
  have hn0 : 0 < nc := hnc
  have hV1 : ∀ i, (c1 - nc ≤ i ∧ i < c1) → Vrow D E₁ r0 c1 nc ρ ≤ E i + D i (r0 + ρ) := by
    intro i hi
    have hle := lmin_le (blkR D E₁ r0 c1) ρ (j := c1 - 1 - i) (n := nc) (by omega)
    simp only [blkR] at hle
    have hle' := Int.cast_le.1 hle
    simp only [Vrow]
    rw [hsrc i hi.1 hi.2]
    simp only [blk] at hle' ⊢
    rw [show c1 - 1 - (c1 - 1 - i) = i by omega] at hle'
    exact hle'
  have hV2 : ∃ i, (c1 - nc ≤ i ∧ i < c1) ∧ Vrow D E₁ r0 c1 nc ρ = E i + D i (r0 + ρ) := by
    have hl := lmin_lt (blkR D E₁ r0 c1) ρ hn0
    refine ⟨c1 - 1 - lmin nc (blkR D E₁ r0 c1) ρ, ⟨by omega, by omega⟩, ?_⟩
    rw [hsrc _ (by omega) (by omega)]; rfl
  have hU := hR.update (S := fun i => c1 - nc ≤ i ∧ i < c1) (t := r0 + ρ) (by omega) hS hV1 hV2
  -- the new state
  have hfin : ∀ c' : Config, WordsBounded W c' →
      (∀ r, r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → c'.nreg r = c.nreg r) →
      (∀ r, r ≠ 20 → r ≠ 21 → c'.rreg r = c.rreg r) → c'.nmem = c.nmem →
      c'.output = c.output → c'.nreg 26 = ρ + 1 →
      c'.nreg 30 = (if Vrow D E₁ r0 c1 nc ρ < E (r0 + ρ) then 1 else c.nreg 30) →
      (∀ a, c'.rmem a = if a = eb + (r0 + ρ) ∧ Vrow D E₁ r0 c1 nc ρ < E (r0 + ρ) then
        ((Vrow D E₁ r0 c1 nc ρ : ℤ) : ℝ) else c.rmem a) →
      IUp b eb D W k C E₀ E₁ r0 nr c1 nc c₁ c' := by
    intro c' hw hn' hr' hnm ho h26 h30 hrm
    refine ⟨hw, fun r a1 a2 a3 a4 a5 => (hn' r a1 a2 a3 a4 a5).trans (g r a1 a2 a3 a4 a5),
      fun r a1 a2 => (hr' r a1 a2).trans (hI.rreg r a1 a2), hnm.trans hI.nmem, fun a ha => ?_,
      ho.trans hI.out, by omega, ?_⟩
    · rw [hrm a]; split_ifs with h
      · omega
      · exact hI.rmem a ha
    · refine ⟨fun v => if v = r0 + ρ ∧ Vrow D E₁ r0 c1 nc ρ < E (r0 + ρ) then
        Vrow D E₁ r0 c1 nc ρ else E v, fun v hv => ?_, ?_, fun v hv hv' => ?_⟩
      · rw [hrm]
        by_cases h : v = r0 + ρ ∧ Vrow D E₁ r0 c1 nc ρ < E (r0 + ρ)
        · have h' : eb + v = eb + (r0 + ρ) ∧ Vrow D E₁ r0 c1 nc ρ < E (r0 + ρ) :=
            ⟨by rw [h.1], h.2⟩
          rw [ite_eq_left h']; beta_reduce; rw [ite_eq_left h]
        · have h' : ¬ (eb + v = eb + (r0 + ρ) ∧ Vrow D E₁ r0 c1 nc ρ < E (r0 + ρ)) :=
            fun h'' => h ⟨by omega, h''.2⟩
          rw [ite_eq_right h']; beta_reduce; rw [ite_eq_right h]; exact hV v hv
      · rw [h30, h26]
        refine hU.mono fun i j hi hj hij hc => ?_
        rcases hc with hc | ⟨h1, h2, h3, h4⟩
        · exact Or.inl (Or.inl hc)
        · by_cases hj' : j = r0 + ρ
          · exact Or.inr ⟨⟨h1, h2⟩, hj'⟩
          · exact Or.inl (Or.inr ⟨h1, h2, h3, by omega⟩)
      · rw [h26] at hv'
        simp only
        split_ifs with h
        · omega
        · exact hE v hv (by omega)
  unfold updBody
  refine spec_seq ?_
  exec_block
  · rw [g24, hρ]; omega
  · config_simp; rw [g3, g24, hρ]; omega
  · config_simp; rw [g4, hρ]; omega
  · config_simp; rw [g4, hρ, g10]; omega
  have hcfg : ∀ x : ℝ, (x < c.rmem (c.nreg 3 + (c.nreg 24 + c.nreg 26)) ↔
      x < (E (r0 + ρ) : ℝ)) ∧ c.rmem (c.nreg 4 + c.nreg 26 + c.nreg 10) =
        (Vrow D E₁ r0 c1 nc ρ : ℝ) := fun x => by
    rw [g4, hρ, g10, g3, g24, hrowc, htc]; exact ⟨Iff.rfl, rfl⟩
  refine spec_seq ?_
  by_cases hcmp : Vrow D E₁ r0 c1 nc ρ < E (r0 + ρ)
  · refine spec_ifLtR_true (by
      config_simp; rw [(hcfg 0).2, (hcfg _).1]; exact_mod_cast hcmp) ?_
    exec_block
    · omega
    refine spec_instr (Exec.addN ‹_› _ _ _ ?_) fun hw => ?_
    · config_simp; rw [hρ, g10]; omega
    refine ⟨hfin _ hw (fun r a1 a2 a3 a4 a5 => ?_) (fun r a1 a2 => ?_) rfl rfl ?_ ?_ ?_, ?_⟩
    · config_simp; upd_tac
    · config_simp; upd_tac
    · config_simp; rw [hρ, g10]
    · config_simp; simp only [hcmp, ite_true]
    · intro a; config_simp; rw [upd_apply, (hcfg 0).2, g3, g24, hρ]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd ⟨h1, hcmp⟩ h2
      · exact absurd h2.1 h1
      · rfl
    · config_simp; rw [hρ, g10]
      omega
  · refine spec_ifLtR_false (by
      config_simp; rw [(hcfg 0).2, (hcfg _).1]; exact_mod_cast hcmp) ?_
    refine spec_skip ‹_› ?_
    refine spec_instr (Exec.addN ‹_› _ _ _ ?_) fun hw => ?_
    · config_simp; rw [hρ, g10]; omega
    refine ⟨hfin _ hw (fun r a1 a2 a3 a4 a5 => ?_) (fun r a1 a2 => ?_) rfl rfl ?_ ?_ ?_, ?_⟩
    · config_simp; upd_tac
    · config_simp; upd_tac
    · config_simp; rw [hρ, g10]
    · config_simp; simp only [hcmp, ite_false]
    · intro a; config_simp
      split_ifs with h1
      · exact absurd h1.2 hcmp
      · rfl
    · config_simp; rw [hρ, g10]
      omega

/-! ### A half block -/

/-- **A half block**: the relaxation of all the arcs from the sources `c1 - nc ≤ i < c1` to the
targets `r0 ≤ t < r0 + nr` (separated), by the row minima of the block matrix, within
`532 (nr + nc + 1)` steps. -/
theorem half_exec (hD : Crossing b D) (hL : Lay b Db eb pb W) {k : ℕ} {C : ℕ → ℕ → Prop}
    {E₀ E : ℕ → ℤ} {r0 nr c1 nc : ℕ} (c : Config) (hc : WordsBounded W c)
    (hE : Env b Db eb pb D c) (hV : Vals b eb E c) (hR : RoundOK b D k C E₀ E (c.nreg 30))
    (h24 : c.nreg 24 = r0) (h25 : c.nreg 25 = c1) (h60 : c.nreg 60 = nr) (h61 : c.nreg 61 = nc)
    (hnr : 1 ≤ nr) (hnc : 1 ≤ nc) (hnc' : nc ≤ c1) (hc1 : c1 ≤ b) (hr : r0 + nr ≤ b)
    (hsep : r0 + nr ≤ c1 - nc ∨ c1 ≤ r0) :
    ∃ c' k', Exec P W half c c' k' ∧ k' ≤ 532 * (nr + nc + 1) ∧
      (Env b Db eb pb D c' ∧
        (∃ E', Vals b eb E' c' ∧
          RoundOK b D k (fun i j => C i j ∨ HalfArcs r0 c1 nc nr i j) E₀ E' (c'.nreg 30)) ∧
        (∀ r < 60, r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → c'.nreg r = c.nreg r) ∧
        (∀ r < 60, r ≠ 20 → r ≠ 21 → c'.rreg r = c.rreg r) ∧ c'.output = c.output) := by
  have hLw := hL.w
  have hpe := hL.pe
  have hed := hL.ed
  unfold half
  refine spec_seq ?_
  refine spec_instr (Exec.copyN hc 62 4) fun hw₁ => ?_
  refine spec_seq ?_
  have hEa : Env b Db eb pb D { c with nreg := upd c.nreg 62 (c.nreg 4) } :=
    hE.of (fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]) rfl (fun _ _ => rfl)
  have hTM : IsTotMono nr nc (blkR D E r0 c1) := (isMonge_blk hD E hnc' hc1 hr hsep).cast.totMono
  refine spec_use (smawk_exec (entBF_exec (P := P) hL hEa hV (by config_simp; exact h24)
    (by config_simp; exact h25) hnc' hc1 hr) hTM (by omega) (by omega) (by omega) hw₁
    (by config_simp; exact h60) (by config_simp; exact h61)
    (by config_simp; exact hE.r4)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨⟨a1, a2, a3, a4, a5⟩, g60, g61, g62, hres⟩
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₂ 26 0 (by omega)) fun hw₃ => ?_
  -- the configuration `c₁` after the row minima
  have n₁ : ∀ r < 60, r ≠ 26 → ({ c₂ with nreg := upd c₂.nreg 26 0 } : Config).nreg r = c.nreg r :=
    fun r hr h => by
      config_simp; rw [upd_other _ _ _ h, a1 r hr]; config_simp; rw [upd_other _ _ _ (by omega)]
  have hE₁ : Env b Db eb pb D ({ c₂ with nreg := upd c₂.nreg 26 0 } : Config) :=
    hE.of (fun r hr => n₁ r (by omega) (by omega)) (a2 10 (by omega))
      (fun a ha => a4 a (Or.inr (by omega)))
  have hV₁ : Vals b eb E ({ c₂ with nreg := upd c₂.nreg 26 0 } : Config) :=
    fun v hv => (a4 _ (Or.inr (by omega))).trans (hV v hv)
  refine spec_while (IUp b eb D W k C E₀ E r0 nr c1 nc { c₂ with nreg := upd c₂.nreg 26 0 })
    (fun c => 12 * (nr - c.nreg 26)) (fun c h => h.wb)
    (fun c' hc' hlt' => updBody_exec hL hE₁ (by rw [n₁ 24 (by omega) (by omega), h24])
      (by config_simp; rw [g60]) hnc hnc' hc1 hr hsep (fun ρ hρ => by
        config_simp; rw [show pb + ρ + 1 = pb + ρ + 1 from rfl, (hres ρ hρ).2]; rfl) c' hc' hlt')
    ⟨hw₃, fun _ _ _ _ _ _ => rfl, fun _ _ _ => rfl, rfl, fun _ _ => rfl, rfl,
      by config_simp; omega, E, hV₁, ?_, fun _ _ _ => rfl⟩ ?_
  · rw [n₁ 30 (by omega) (by omega)]
    refine hR.mono fun i j _ _ _ hc => ?_
    rcases hc with hc | ⟨-, -, h3, h4⟩
    · exact hc
    · config_simp at h4; omega
  intro c₃ k₃ hI hn hk₃
  have h26 : c₃.nreg 26 = nr := by
    have := hI.ρ
    rw [hI.nreg 60 (by omega) (by omega) (by omega) (by omega) (by omega)] at hn
    config_simp at hn; rw [g60] at hn; omega
  obtain ⟨E', hV', hR', -⟩ := hI.vals
  rw [h26] at hR'
  refine ⟨?_, hE₁.of (fun r hr => hI.nreg r (by omega) (by omega) (by omega) (by omega) (by omega))
    (hI.rreg 10 (by omega) (by omega)) (fun a ha => hI.rmem a (Or.inr (by omega))),
    ⟨E', hV', hR'⟩, fun r hr a b' d e f => ?_, fun r hr h1 h2 => ?_, ?_⟩
  · beta_reduce at hk₃
    config_simp at hk₃
    omega
  · rw [hI.nreg r a b' d e f]; exact n₁ r hr a
  · rw [hI.rreg r h1 h2]; config_simp; rw [a2 r hr]
  · rw [hI.out]; config_simp; rw [a5]

/-! ### A block -/

/-- `r23 := min r23 r1`. -/
theorem minS_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k', Exec P W (.ifLtN 1 23 (.instr (.copyN 23 1)) .skip) c c' k' ∧ k' ≤ 2 ∧
      (c'.nreg 23 = min (c.nreg 23) (c.nreg 1) ∧ (∀ r, r ≠ 23 → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  by_cases h : c.nreg 1 < c.nreg 23
  · refine spec_ifLtN_true h ?_
    refine spec_instr (Exec.copyN hc 23 1) fun _ => ?_
    refine ⟨le_refl _, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; omega
    · config_simp; rw [upd_other _ _ _ hr]
  · refine spec_ifLtN_false h ?_
    refine spec_skip hc ?_
    exact ⟨by omega, by omega, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-- The state between the blocks of the level `s` of round `k`. -/
structure IB (b Db eb pb : ℕ) (D : ℕ → ℕ → ℤ) (W k : ℕ) (E₀ : ℕ → ℤ) (s : ℕ) (c₀ c : Config) :
    Prop where
  wb : WordsBounded W c
  env : Env b Db eb pb D c
  r14 : c.nreg 14 = c₀.nreg 14
  r15 : c.nreg 15 = c₀.nreg 15
  r20 : c.nreg 20 = s
  base : ∃ q, c.nreg 21 = 2 * s * q
  r22 : c.nreg 22 = c.nreg 21 + s
  basele : c.nreg 21 ≤ b + s
  vals : ∃ E, Vals b eb E c ∧ RoundOK b D k (Cov s (c.nreg 21)) E₀ E (c.nreg 30)
  out : c.output = c₀.output

/-- The cost bound of a block of the level `s`. -/
def blockCost (_b s : ℕ) : ℕ := 2 * (532 * (2 * s + 1)) + 14

lemma halfCost_le {b s nr nc : ℕ} (h1 : nr ≤ s) (h2 : nc ≤ s) (_h3 : s ≤ b) (_hnr : 1 ≤ nr) :
    532 * (nr + nc + 1) ≤ 532 * (2 * s + 1) := by
  omega

theorem blockBody_exec (hD : Crossing b D) (hL : Lay b Db eb pb W) {k : ℕ} {E₀ : ℕ → ℤ} {s : ℕ}
    {c₀ : Config} (hs : 1 ≤ s) (hsb : s < b) (c : Config) (hI : IB b Db eb pb D W k E₀ s c₀ c)
    (hlt : c.nreg 22 < c.nreg 1) :
    ∃ c' k', Exec P W blockBody c c' k' ∧ IB b Db eb pb D W k E₀ s c₀ c' ∧
      (blockCost b s + 2) * ((b + s - c'.nreg 21) / (2 * s)) + k' + 2 ≤
        (blockCost b s + 2) * ((b + s - c.nreg 21) / (2 * s)) := by
  have hc := hI.wb
  have hE := hI.env
  have hLw := hL.w
  have hpe := hL.pe
  have hed := hL.ed
  rw [hI.r22, hE.r1] at hlt
  obtain ⟨q, hq⟩ := hI.base
  generalize hbase : c.nreg 21 = base at hq hlt
  obtain ⟨E, hV, hR⟩ := hI.vals
  rw [hbase] at hR
  have g20 := hI.r20
  have g22 : c.nreg 22 = base + s := by rw [hI.r22, hbase]
  unfold blockBody
  -- `r23 := min (base + 2s) b`
  refine spec_seq ?_
  refine spec_instr (Exec.addN hc 23 22 20 (by rw [g22, g20]; omega)) fun hw₁ => ?_
  refine spec_seq ?_
  refine spec_use (minS_exec _ hw₁) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨h23, hn₂, hr₂, hnm₂, hrm₂, ho₂⟩
  config_simp at h23
  rw [g22, g20, hE.r1] at h23
  generalize hrend : min (base + s + s) b = rend at h23
  have hrend1 : base + s < rend := by rw [← hrend]; omega
  have hrend2 : rend ≤ b := by rw [← hrend]; omega
  have hrend3 : rend ≤ base + 2 * s := by rw [← hrend]; omega
  have e₂ : ∀ r, r ≠ 23 → c₂.nreg r = c.nreg r := fun r hr => by
    rw [hn₂ r hr]; config_simp; rw [upd_other _ _ _ hr]
  have hE₂ : Env b Db eb pb D c₂ :=
    hE.of (fun r hr => e₂ r (by omega)) (by rw [hr₂]) (fun a _ => by rw [hrm₂])
  -- the first half: from `[base, base + s)` to `[base + s, rend)`
  refine spec_seq ?_
  exec_block
  refine spec_seq ?_
  refine spec_use (half_exec (P := P) hD hL (C := Cov s base) (r0 := base + s) (c1 := base + s)
    (nr := rend - (base + s)) (nc := s) _ ‹_›
    (hE₂.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl))
    (fun v hv => by config_simp; rw [hrm₂]; exact hV v hv)
    (by config_simp; rw [e₂ 30 (by omega)]; exact hR)
    (by config_simp; rw [e₂ 22 (by omega), g22])
    (by config_simp; rw [e₂ 22 (by omega), g22])
    (by config_simp; rw [h23, e₂ 22 (by omega), g22])
    (by config_simp; rw [e₂ 20 (by omega), g20])
    (by omega) hs (by omega) (by omega) (by omega) (Or.inr le_rfl)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hE₃, ⟨E₃, hV₃, hR₃⟩, hn₃, hr₃, ho₃⟩
  have e₃ : ∀ r < 60, r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 →
      c₃.nreg r = c.nreg r := fun r hr a1 a2 a3 a4 a5 a6 a7 a8 => by
    rw [hn₃ r hr a4 a5 a6 a7 a8]; config_simp
    simp only [upd_apply]; split_ifs <;> first | omega | exact e₂ r a1
  have g23₃ : c₃.nreg 23 = rend := by
    rw [hn₃ 23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    config_simp; exact h23
  -- the second half: from `[base + s, rend)` to `[base, base + s)`
  refine spec_seq ?_
  exec_block
  refine spec_seq ?_
  refine spec_use (half_exec (P := P) hD hL (r0 := base) (c1 := rend) (nr := s)
    (nc := rend - (base + s)) _ ‹_›
    (hE₃.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl))
    (fun v hv => by config_simp; exact hV₃ v hv)
    (by config_simp; exact hR₃)
    (by config_simp; rw [e₃ 21 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hbase])
    (by config_simp; exact g23₃)
    (by config_simp; rw [e₃ 20 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), g20])
    (by config_simp; rw [g23₃, e₃ 22 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), g22])
    hs (by omega) (by omega) hrend2 (by omega) (Or.inl (by omega))) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨hE₄, ⟨E₄, hV₄, hR₄⟩, hn₄, hr₄, ho₄⟩
  have e₄ : ∀ r < 60, r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 →
      r ≠ 60 → r ≠ 61 → c₄.nreg r = c.nreg r := fun r hr a1 a2 a3 a4 a5 a6 a7 a8 _ _ => by
    rw [hn₄ r hr a4 a5 a6 a7 a8]; config_simp
    simp only [upd_apply]; split_ifs <;> first | omega | exact e₃ r hr a1 a2 a3 a4 a5 a6 a7 a8
  have g20₄ : c₄.nreg 20 = s := by
    rw [e₄ 20 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), g20]
  have g21₄ : c₄.nreg 21 = base := by
    rw [e₄ 21 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), hbase]
  -- the next block
  exec_block
  · rw [g21₄, g20₄]; omega
  · config_simp; rw [g21₄, g20₄]; omega
  · config_simp; rw [g21₄, g20₄]; omega
  refine ⟨⟨‹_›, hE₄.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl), ?_, ?_, ?_,
    ⟨q + 1, ?_⟩, ?_, ?_, ⟨E₄, fun v hv => by config_simp; exact hV₄ v hv, ?_⟩, ?_⟩, ?_⟩
  · config_simp; rw [e₄ 14 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega), hI.r14]
  · config_simp; rw [e₄ 15 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega), hI.r15]
  · config_simp; exact g20₄
  · config_simp; rw [g21₄, g20₄, hq]; ring
  · config_simp; rw [g20₄]
  · config_simp; rw [g21₄, g20₄]; omega
  · config_simp; rw [g21₄, g20₄]
    refine hR₄.mono fun i j hi hj hij hc => ?_
    rw [show base + s + s = 2 * s * q + 2 * s by rw [hq]; ring] at hc
    rcases cov_step (by omega) hc with hc | hc
    · rw [← hq] at hc; exact Or.inl (Or.inl hc)
    · rw [← hq] at hc
      rcases hc with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · exact Or.inl (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
  · config_simp; rw [ho₄]; config_simp; rw [ho₃]; config_simp; rw [ho₂, hI.out]
  · -- the cost
    config_simp; rw [g21₄, g20₄]
    have hb1 := halfCost_le (b := b) (s := s) (nr := rend - (base + s)) (nc := s) (by omega) le_rfl
      hsb.le (by omega)
    have hb2 := halfCost_le (b := b) (s := s) (nr := s) (nc := rend - (base + s)) le_rfl (by omega)
      hsb.le hs
    have hμ : (b + s - base) / (2 * s) = (b + s - (base + s + s)) / (2 * s) + 1 := by
      rw [show b + s - base = b + s - (base + s + s) + 2 * s by omega,
        Nat.add_div_right _ (by omega)]
    rw [hμ, Nat.mul_add, Nat.mul_one]
    generalize (blockCost b s + 2) * ((b + s - (base + s + s)) / (2 * s)) = Y
    have hB : blockCost b s = 2 * (532 * (2 * s + 1)) + 14 := rfl
    rw [hB]
    generalize hx : rend - (base + s) = x at hb1 hb2 ⊢
    omega

/-! ### A level -/

/-- The state between the levels of round `k`. -/
structure IL (b Db eb pb : ℕ) (D : ℕ → ℕ → ℤ) (W k : ℕ) (E₀ : ℕ → ℤ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  env : Env b Db eb pb D c
  r14 : c.nreg 14 = c₀.nreg 14
  r15 : c.nreg 15 = c₀.nreg 15
  pow : ∃ t, c.nreg 20 = 2 ^ t
  sle : c.nreg 20 ≤ 2 * b + 1
  vals : ∃ E, Vals b eb E c ∧ RoundOK b D k (Cov (c.nreg 20) 0) E₀ E (c.nreg 30)
  out : c.output = c₀.output

/-- The cost bound of a level. -/
def levelCost (b : ℕ) : ℕ := 3208 * b + 5

lemma blocks_le {b s : ℕ} (hs : 1 ≤ s) (hsb : s < b) :
    (blockCost b s + 2) * ((b + s) / (2 * s)) + 5 ≤ levelCost b := by
  unfold blockCost levelCost
  have h2 : s * ((b + s) / (2 * s)) ≤ b := by
    have := Nat.div_mul_le_self (b + s) (2 * s)
    have e : (b + s) / (2 * s) * (2 * s) = 2 * (s * ((b + s) / (2 * s))) := by ring
    omega
  have h1 : 2 * (532 * (2 * s + 1)) + 14 + 2 ≤ 3208 * s := by omega
  calc (2 * (532 * (2 * s + 1)) + 14 + 2) * ((b + s) / (2 * s)) + 5
      ≤ 3208 * s * ((b + s) / (2 * s)) + 5 := by
        have := Nat.mul_le_mul_right ((b + s) / (2 * s)) h1; omega
    _ = 3208 * (s * ((b + s) / (2 * s))) + 5 := by ring
    _ ≤ 3208 * b + 5 := by have := Nat.mul_le_mul_left 3208 h2; omega

theorem levelBF_exec (hD : Crossing b D) (hL : Lay b Db eb pb W) {k : ℕ} {E₀ : ℕ → ℤ}
    {c₀ : Config} (c : Config) (hI : IL b Db eb pb D W k E₀ c₀ c) (hlt : c.nreg 20 < c.nreg 1) :
    ∃ c' k', Exec P W levelBF c c' k' ∧ IL b Db eb pb D W k E₀ c₀ c' ∧
      (levelCost b + 2) * (Nat.log 2 b + 1 - Nat.log 2 (c'.nreg 20)) + k' + 2 ≤
        (levelCost b + 2) * (Nat.log 2 b + 1 - Nat.log 2 (c.nreg 20)) := by
  have hc := hI.wb
  have hE := hI.env
  have hLw := hL.w
  rw [hE.r1] at hlt
  obtain ⟨t, ht⟩ := hI.pow
  generalize hs : c.nreg 20 = s at ht hlt
  have hs1 : 1 ≤ s := by rw [ht]; exact Nat.one_le_two_pow
  obtain ⟨E, hV, hR⟩ := hI.vals
  rw [hs] at hR
  unfold levelBF
  refine spec_seq ?_
  exec_block
  · omega
  refine spec_seq ?_
  refine spec_while (IB b Db eb pb D W k E₀ s c₀)
    (fun c => (blockCost b s + 2) * ((b + s - c.nreg 21) / (2 * s))) (fun c h => h.wb)
    (fun c' hc' hlt' => blockBody_exec hD hL hs1 hlt c' hc' hlt')
    ⟨‹_›, hE.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl),
      by config_simp; exact hI.r14, by config_simp; exact hI.r15, by config_simp; exact hs,
      ⟨0, by config_simp; ring⟩, by config_simp; rw [hs], by config_simp; omega,
      ⟨E, hV, by config_simp; exact hR⟩, by config_simp; exact hI.out⟩ ?_
  intro c₂ k₂ hI₂ hn₂ hk₂
  have hw₂ := hI₂.wb
  have g20 := hI₂.r20
  have hend : b ≤ c₂.nreg 21 + s := by
    rw [hI₂.r22, hI₂.env.r1] at hn₂; omega
  refine spec_instr (Exec.addN hw₂ 20 20 20 (by rw [g20]; omega)) fun hw₃ => ?_
  obtain ⟨E₂, hV₂, hR₂⟩ := hI₂.vals
  refine ⟨⟨hw₃, hI₂.env.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl),
    by config_simp; exact hI₂.r14, by config_simp; exact hI₂.r15,
    ⟨t + 1, by config_simp; rw [g20, ht, pow_succ]; ring⟩, by config_simp; rw [g20]; omega,
    ⟨E₂, hV₂, ?_⟩, hI₂.out⟩, ?_⟩
  · config_simp; rw [g20]
    refine hR₂.mono fun i j hi hj hij hc => ?_
    exact cov_level ht hend hi hj (by rw [show s + s = 2 * s by ring] at hc; exact hc)
  · config_simp; rw [g20]
    beta_reduce at hk₂
    config_simp at hk₂
    rw [Nat.sub_zero] at hk₂
    have hl1 : Nat.log 2 (s + s) = Nat.log 2 s + 1 := by
      rw [show s + s = s * 2 by ring, Nat.log_mul_base (by norm_num) (by omega)]
    have hl2 : Nat.log 2 s ≤ Nat.log 2 b := Nat.log_mono_right hlt.le
    rw [hl1]
    have hb := blocks_le hs1 hlt
    have := mul_pred_add (a := levelCost b + 2) (x := Nat.log 2 b + 1 - Nat.log 2 s) (by omega)
    rw [show Nat.log 2 b + 1 - Nat.log 2 s - 1 = Nat.log 2 b + 1 - (Nat.log 2 s + 1) by omega]
      at this
    omega

/-! ### A round -/

/-- The state between the rounds. -/
structure IK (b Db eb pb : ℕ) (D : ℕ → ℕ → ℤ) (W : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  env : Env b Db eb pb D c
  r15 : c.nreg 15 = b + 1
  r14 : c.nreg 14 ≤ b + 1
  flag : c.nreg 30 ≤ 1
  vals : ∃ E, Vals b eb E c ∧
    (HasPot b D → ∀ v < b, bfv b D b v ≤ E v ∧ E v ≤ bfv b D (c.nreg 14) v) ∧
    (1 ≤ c.nreg 14 → c.nreg 30 = 0 → ∀ i j, i < b → j < b → i ≠ j → E j ≤ E i + D i j) ∧
    (1 ≤ c.nreg 14 → c.nreg 30 = 1 → HasPot b D →
      ∃ v < b, bfv b D b v < bfv b D (c.nreg 14 - 1) v)
  out : c.output = c₀.output

/-- The cost bound of a round. -/
def roundCost (b : ℕ) : ℕ := (levelCost b + 2) * (Nat.log 2 b + 1) + 5

theorem roundBF_exec (hD : Crossing b D) (hL : Lay b Db eb pb W) {c₀ : Config} (c : Config)
    (hI : IK b Db eb pb D W c₀ c) (hlt : c.nreg 14 < c.nreg 15) :
    ∃ c' k', Exec P W roundBF c c' k' ∧ IK b Db eb pb D W c₀ c' ∧
      (roundCost b + 2) * (b + 1 - c'.nreg 14) + k' + 2 ≤ (roundCost b + 2) * (b + 1 - c.nreg 14) := by
  have hc := hI.wb
  have hE := hI.env
  have hLw := hL.w
  rw [hI.r15] at hlt
  generalize hk : c.nreg 14 = k at hlt
  obtain ⟨E, hV, hB, -, -⟩ := hI.vals
  rw [hk] at hB
  unfold roundBF
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  refine spec_seq ?_
  refine spec_while (IL b Db eb pb D W k E { c with nreg := upd (upd c.nreg 20 1) 30 0 })
    (fun c => (levelCost b + 2) * (Nat.log 2 b + 1 - Nat.log 2 (c.nreg 20))) (fun c h => h.wb)
    (fun c' hc' hlt' => levelBF_exec hD hL c' hc' hlt')
    ⟨‹_›, hE.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl), rfl, rfl,
      ⟨0, by config_simp; rfl⟩, by config_simp; omega,
      ⟨E, hV, by
        config_simp
        exact (RoundOK.start hB).mono fun i j _ _ _ hc => not_cov_one_zero hc⟩, rfl⟩ ?_
  intro c₂ k₂ hI₂ hn₂ hk₂
  have hw₂ := hI₂.wb
  have g14 : c₂.nreg 14 = k := by rw [hI₂.r14]; config_simp; exact hk
  rw [hI₂.env.r1] at hn₂
  refine spec_instr (Exec.addN hw₂ 14 14 10 (by rw [g14, hI₂.env.r10]; omega)) fun hw₃ => ?_
  obtain ⟨E₂, hV₂, hR₂⟩ := hI₂.vals
  have hall := (hR₂.mono (C' := fun _ _ => True) fun i j hi hj hij _ =>
    cov_all (by omega) hij hi hj).finish
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hall
  refine ⟨⟨hw₃, hI₂.env.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl),
    by config_simp; rw [hI₂.r15]; config_simp; exact hI.r15, by config_simp; rw [g14, hI₂.env.r10]; omega,
    by config_simp; exact hf1, ⟨E₂, hV₂, fun hP v hv => ?_, fun _ h0 => ?_, fun _ h1 hP => ?_⟩,
    by config_simp; rw [hI₂.out]; config_simp; exact hI.out⟩, ?_⟩
  · config_simp; rw [g14, hI₂.env.r10]; exact hf2 hP v hv
  · config_simp at h0; exact hf3 h0
  · config_simp at h1; config_simp; rw [g14, hI₂.env.r10, Nat.add_sub_cancel]; exact hf4 h1 hP
  · config_simp; rw [g14, hI₂.env.r10]
    beta_reduce at hk₂
    config_simp at hk₂
    rw [show Nat.log 2 1 = 0 from Nat.log_one_right 2, Nat.sub_zero] at hk₂
    have := mul_pred_add (a := roundCost b + 2) (x := b + 1 - k) (by omega)
    rw [show b + 1 - k - 1 = b + 1 - (k + 1) by omega] at this
    unfold roundCost at this ⊢
    omega

/-! ### The whole run -/

/-- The state of the initialization of the values. -/
structure II (b Db eb pb : ℕ) (D : ℕ → ℕ → ℤ) (W : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  env : Env b Db eb pb D c
  r12 : c.nreg 12 ≤ b
  r14 : c.nreg 14 = 0
  r15 : c.nreg 15 = b + 1
  r30 : c.nreg 30 = 0
  zero : ∀ v < c.nreg 12, c.rmem (eb + v) = 0
  out : c.output = c₀.output

theorem initBody_exec (hL : Lay b Db eb pb W) {c₀ : Config} (c : Config)
    (hI : II b Db eb pb D W c₀ c) (hlt : c.nreg 12 < c.nreg 1) :
    ∃ c' k', Exec P W initBody c c' k' ∧ II b Db eb pb D W c₀ c' ∧
      5 * (b - c'.nreg 12) + k' + 2 ≤ 5 * (b - c.nreg 12) := by
  have hc := hI.wb
  have hE := hI.env
  have hLw := hL.w
  have hed := hL.ed
  rw [hE.r1] at hlt
  unfold initBody
  exec_block
  · rw [hE.r3]; omega
  · config_simp; rw [hE.r10]; omega
  refine ⟨⟨‹_›, hE.of (fun r hr => by config_simp; upd_tac) rfl (fun a ha => ?_), ?_, ?_, ?_, ?_,
    fun v hv => ?_, hI.out⟩, ?_⟩
  · config_simp; rw [upd_other _ _ _ (by rw [hE.r3]; omega)]
  · config_simp; rw [hE.r10]; omega
  · config_simp; exact hI.r14
  · config_simp; exact hI.r15
  · config_simp; exact hI.r30
  · config_simp at hv; config_simp
    rw [hE.r10] at hv
    rw [upd_apply, hE.r3, hE.z10]
    split_ifs with h
    · rfl
    · exact hI.zero v (by omega)
  · config_simp; rw [hE.r10]; omega

/-- The cost bound of the whole run. -/
def bfCost (b : ℕ) : ℕ := 5 * b + 10 + (roundCost b + 2) * (b + 1)

/-- **Bellman–Ford over a dense distance graph on the machine.** On the dense distance graph of
the vertices `0, …, b - 1` of a face (lengths `D` at `Db` in the real memory, satisfying the
crossing inequality), `bfDDG` runs `b + 1` rounds of Bellman–Ford from the values `0` within
`bfCost b = O(b² log b)` steps (`bfCost_le`). At the end the values `E v` are stored at `eb + v`,
and either `r30 = 0` and `E` is a feasible potential, or `r30 = 1` and there is no feasible
potential. If a feasible potential exists, `E` is `bf b`: the distances from a virtual source
joined to every vertex by an arc of length `0`. -/
theorem bfDDG_exec (hD : Crossing b D) (hL : Lay b Db eb pb W) (c : Config) (hc : WordsBounded W c)
    (h1 : c.nreg 1 = b) (h2 : c.nreg 2 = Db) (h3 : c.nreg 3 = eb) (h4 : c.nreg 4 = pb)
    (hDm : ∀ i j, i < b → j < b → c.rmem (Db + i * b + j) = D i j) :
    ∃ c' k, Exec P W bfDDG c c' k ∧ k ≤ bfCost b ∧
      ∃ E : ℕ → ℤ, (∀ v < b, c'.rmem (eb + v) = E v) ∧
        ((c'.nreg 30 = 0 ∧ (ddg b D).IsPot (fun v => E v)) ∨ (c'.nreg 30 = 1 ∧ ¬ HasPot b D)) ∧
        (HasPot b D → ∀ v < b, E v = bfv b D b v) ∧ c'.output = c.output ∧
        (∀ i j, i < b → j < b → c'.rmem (Db + i * b + j) = D i j) := by
  have hLw := hL.w
  unfold bfDDG
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  · config_simp; rw [h1]; omega
  · omega
  · omega
  refine spec_seq ?_
  refine spec_while (II b Db eb pb D W c) (fun c => 5 * (b - c.nreg 12)) (fun c h => h.wb)
    (fun c' hc' hlt' => initBody_exec hL c' hc' hlt')
    ⟨‹_›, ⟨by config_simp; exact h1, by config_simp; exact h2,
      by config_simp; exact h3, by config_simp; exact h4, by config_simp, by config_simp; simp,
      fun i j hi hj => by config_simp; exact hDm i j hi hj⟩, by config_simp; omega, by config_simp,
      by config_simp; rw [h1], by config_simp,
      fun v hv => by config_simp at hv; omega, rfl⟩ ?_
  intro c₁ k₁ hI₁ hn₁ hk₁
  have h12 : c₁.nreg 12 = b := by have := hI₁.r12; rw [hI₁.env.r1] at hn₁; omega
  refine spec_while (IK b Db eb pb D W c) (fun c => (roundCost b + 2) * (b + 1 - c.nreg 14))
    (fun c h => h.wb) (fun c' hc' hlt' => roundBF_exec hD hL c' hc' hlt')
    ⟨hI₁.wb, hI₁.env, hI₁.r15, by rw [hI₁.r14]; omega, by rw [hI₁.r30]; omega,
      ⟨fun _ => 0, fun v hv => by rw [hI₁.zero v (by omega)]; simp, fun hP v hv => ?_,
        fun h => by rw [hI₁.r14] at h; omega, fun h => by rw [hI₁.r14] at h; omega⟩,
      hI₁.out⟩ ?_
  · rw [hI₁.r14, bfv_zero]
    exact ⟨by have := bfv_card_le hP 0 hv; rwa [bfv_zero] at this, le_rfl⟩
  intro c₂ k₂ hI₂ hn₂ hk₂
  have h14 : c₂.nreg 14 = b + 1 := by have := hI₂.r14; rw [hI₂.r15] at hn₂; omega
  obtain ⟨E, hV, hB, hF, hN⟩ := hI₂.vals
  rw [h14] at hB hF hN
  refine ⟨?_, E, hV, ?_, fun hP v hv => ?_, by rw [hI₂.out],
    fun i j hi hj => hI₂.env.dmem i j hi hj⟩
  · beta_reduce at hk₁ hk₂
    config_simp at hk₁
    rw [hI₁.r14, Nat.sub_zero] at hk₂
    unfold bfCost
    omega
  · have hfl := hI₂.flag
    rcases Nat.lt_or_ge (c₂.nreg 30) 1 with h | h
    · exact Or.inl ⟨by omega, pot_of_feas (hF (by omega) (by omega))⟩
    · refine Or.inr ⟨by omega, fun hP => ?_⟩
      obtain ⟨v, hv, hlt⟩ := hN (by omega) (by omega) hP
      rw [Nat.add_sub_cancel] at hlt
      exact lt_irrefl _ hlt
  · have := hB hP v hv
    rw [show bfv b D (b + 1) v = bfv b D b v from ?_] at this
    · omega
    · obtain ⟨p, hp⟩ := hP
      rw [bfv_of_lt hv, bfv_of_lt hv]
      have := (ddg b D).bf_succ_card hp ⟨v, hv⟩
      rwa [Fintype.card_fin] at this

/-- The cost of the whole run is `O(b² log b)`. -/
theorem bfCost_le (b : ℕ) : bfCost b ≤ 3300 * (b + 1) ^ 2 * (Nat.log 2 b + 1) := by
  unfold bfCost roundCost levelCost
  have hL : 1 ≤ Nat.log 2 b + 1 := by omega
  generalize Nat.log 2 b + 1 = L at hL ⊢
  nlinarith [Nat.mul_le_mul (le_refl (b + 1)) hL, Nat.mul_le_mul (le_refl ((b + 1) * (b + 1))) hL]

/-- **A negative cycle when the flag is set.** If `bfDDG` ends with `r30 = 1`, the dense distance
graph has a closed walk of negative length (`PlanarFlow.Digraph.exists_pot_iff`). -/
theorem negWalk_of_not_hasPot {b : ℕ} {D : ℕ → ℕ → ℤ} (h : ¬ HasPot b D) :
    ∃ m c, (ddg b D).IsClosedWalk m c ∧ (ddg b D).walkLen m c < 0 := by
  by_contra hcon
  push Not at hcon
  exact h ((ddg b D).exists_pot_iff.2 hcon)

end Monge

end PlanarFlow
