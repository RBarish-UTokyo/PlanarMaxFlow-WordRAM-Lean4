module

public import PlanarFlow.NegSSSP.NodeN
public import PlanarFlow.NegSSSP.NodeCmpE

/-!
# The whole node on natural words, with Klein's part on natural words

`node_exec_nat'` (`PlanarFlow/NegSSSP/NodeCmpE.lean`) puts the node on natural words assuming
that Klein's part of the *real-register* node program is compare-bounded (`KCmp`), and assumes
`nodeProg` free of `divR` (it is not: `rdProg` divides reals). Here the node is put on natural
words **without these hypotheses**:

* `nodeProgNN`: the constants of the simulation, the glue before Klein's part on natural words
  (`ModNat.toNat 1000 M (bdSet; bdryProg)`), **the two parts on natural words** (`kPairN`:
  Klein's program on natural words with the isolating lengths, the read-back by `divN`, the
  matrices written as residues modulo `M` into the cells simulating the node's real memory),
  then the end of the node on natural words (`ModNat.toNat 1000 M restProg`).
  `nodeProgNN_natOnly`: **no real instruction** (checked by the kernel).
* `decodeN`: the real configuration read back from a natural one (`sgnD`: a residue `v ≤ H` is
  `v`, otherwise `v - M`); `sim_decodeN`: the natural configuration simulates it.
* `abs_matOf_le`: the lengths of the dense distance graph of a part are bounded by `(3 m + 2) B`
  when the lengths and the potentials are bounded by `B`.
* `node_exec_natN`: the run of the node on natural words (see its docstring).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge Monge.FR
  CmpAbs ModNat

/-! ### Reading a real configuration back from a natural one -/

/-- The integer read back from a residue `v` modulo `M`: `v` if `v ≤ H`, else `v - M`. -/
noncomputable def sgnD (H M v : ℕ) : ℝ := if v ≤ H then (v : ℝ) else (v : ℝ) - M

lemma res_sgnD {H M v : ℕ} (hv : v < M) : Res M (sgnD H M v) v := by
  unfold sgnD
  split_ifs with h
  · exact_mod_cast res_nat hv
  · refine ⟨(v : ℤ) - M, by push_cast; ring, ?_⟩
    have : ((v : ℤ) - M) % (M : ℤ) = v := by
      rw [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod_of_dvd _ (dvd_refl _)]
      exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast hv)
    exact this.symm

lemma sgnD_eq {H M v : ℕ} {x : ℝ} (h : Res M x v) (hx : |x| ≤ H) (hM : 2 * H < M) :
    sgnD H M v = x := (h.signed hx hM).symm

lemma sgnD_int (H M v : ℕ) : ∃ z : ℤ, sgnD H M v = z := by
  unfold sgnD
  split_ifs
  · exact ⟨v, by push_cast; ring⟩
  · exact ⟨(v : ℤ) - M, by push_cast; ring⟩

/-- **The real configuration read back from `d`**: below `R` (registers) and `W` (memory) the
natural words of `d` and the integers read back from its residues; elsewhere those of `c`. -/
noncomputable def decodeN (R W M H β : ℕ) (c d : Config) : Config where
  pc := c.pc
  nreg r := if r < R then d.nreg r else c.nreg r
  rreg r := if r < R then sgnD H M (d.nreg (R + r)) else c.rreg r
  nmem a := if a ≤ W then d.nmem a else c.nmem a
  rmem a := if a ≤ W then sgnD H M (d.nmem (β + a)) else c.rmem a
  output := d.output

theorem sim_decodeN {R W M H β : ℕ} {c d : Config} (hr : ∀ r < R, d.nreg (R + r) < M)
    (hm : ∀ a ≤ W, d.nmem (β + a) < M) : Sim R W M β (decodeN R W M H β c d) d where
  nreg r hr' := by simp [decodeN, hr']
  rreg r hr' := by simp only [decodeN, hr', ↓reduceIte]; exact res_sgnD (hr r hr')
  nmem a ha := by simp [decodeN, ha]
  rmem a ha := by simp only [decodeN, ha, ↓reduceIte]; exact res_sgnD (hm a ha)
  output := rfl

theorem intAll_decodeN {R W M H β : ℕ} {c d : Config} (hc : IntAll c) :
    IntAll (decodeN R W M H β c d) := by
  refine ⟨fun r => ?_, fun a => ?_⟩
  · simp only [decodeN]; split_ifs
    · exact sgnD_int H M _
    · exact hc.1 r
  · simp only [decodeN]; split_ifs
    · exact sgnD_int H M _
    · exact hc.2 a

theorem wb_decodeN {R W M H β : ℕ} {c d : Config} (hc : WordsBounded W c)
    (hr : ∀ r < R, d.nreg r ≤ W) (hm : ∀ a ≤ W, d.nmem a ≤ W) :
    WordsBounded W (decodeN R W M H β c d) := by
  refine ⟨fun r => ?_, fun a => ?_⟩
  · simp only [decodeN]; split_ifs with h
    · exact hr r h
    · exact hc.1 r
  · simp only [decodeN]; split_ifs with h
    · exact hm a h
    · exact hc.2 a

/-! ### The bound of the lengths of a dense distance graph -/

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

theorem abs_matOf_le {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}
    (hmssp : PieceMSSPSpec N mssp) {X : Finset D} {ℓ : D → ℤ} {δ : V → ℤ} {Bd : Finset V}
    (hnn : ∀ d ∈ X, 0 ≤ redLen N ℓ δ d) {B m : ℕ} (hXm : X.card ≤ m)
    (hℓ : ∀ d ∈ X, |ℓ d| ≤ B) (hδ : ∀ x ∈ verts N X, |δ x| ≤ B) (hBd : Bd ⊆ verts N X)
    (β' : ℕ → V) (s t : ℕ) (hs : β' s ∈ Bd) (ht : β' t ∈ Bd) :
    |(matOf (childDDG N mssp X ℓ δ Bd) β' s t : ℝ)| ≤ ((3 * m + 2) * B : ℕ) := by
  classical
  have hnn' : ∀ a, 0 ≤ (MSSP.pieceGraph N X (redLen N ℓ δ)).len a := fun a => hnn a.1 a.2
  have hms : mssp X (redLen N ℓ δ) Bd (β' s) (β' t) =
      MSSP.odist (MSSP.pieceGraph N X (redLen N ℓ δ)) (β' s) (β' t) := by
    have := odist_eq_of_isDist hnn' (hmssp X (redLen N ℓ δ) Bd hnn (β' s) hs)
    exact congrFun this (β' t)
  have hδs := hδ _ (hBd hs)
  have hδt := hδ _ (hBd ht)
  have hred : ∀ d ∈ X, redLen N ℓ δ d ≤ 3 * B := fun d hd => by
    have h1 := hℓ d hd
    have h2 := hδ (N.tail d) (by unfold verts; simp; exact Or.inl ⟨d, hd, rfl⟩)
    have h3 := hδ (N.head d) (by unfold verts; simp; exact Or.inr ⟨d, hd, rfl⟩)
    unfold redLen
    rw [abs_le] at h1 h2 h3
    omega
  have hsum : ∑ a, (MSSP.pieceGraph N X (redLen N ℓ δ)).len a ≤ (3 * m * B : ℤ) := by
    show ∑ a : {d // d ∈ X}, redLen N ℓ δ a.1 ≤ _
    rw [Finset.sum_coe_sort X (redLen N ℓ δ)]
    calc ∑ d ∈ X, redLen N ℓ δ d ≤ ∑ _d ∈ X, (3 * B : ℤ) := Finset.sum_le_sum hred
      _ = X.card * (3 * B : ℤ) := by simp
      _ ≤ m * (3 * B : ℤ) := by
          have : (X.card : ℤ) ≤ m := by exact_mod_cast hXm
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = 3 * m * B := by ring
  unfold matOf childDDG
  dsimp only
  rw [hms]
  unfold MSSP.odist
  split_ifs with hr
  · simp only [Option.map_some, Option.getD_some]
    have h0 := MSSP.dist_nonneg hnn' hr
    have h1 := (Klein.dist_le_sum_len hnn' hr).trans hsum
    rw [abs_le] at hδs hδt
    have : |MSSP.dist (MSSP.pieceGraph N X (redLen N ℓ δ)) (β' s) (β' t) +
        (δ (β' t) - δ (β' s))| ≤ ((3 * m + 2) * B : ℤ) := by
      rw [abs_le]; constructor <;> nlinarith
    exact_mod_cast this
  · simp only [Option.map_none, Option.getD_none, Int.cast_zero, abs_zero]
    positivity

/-! ### The program -/

/-- The comparison bound of the node on natural words: `2 B` for the glue before Klein's part,
`512 restB b w ((3 m + 2) B)` for the end of the node. -/
def nodeHN (m b w B : ℕ) : ℕ := 2 * B + 512 * restB b w ((3 * m + 2) * B)

/-- **The whole node on natural words** (see the module docstring): the constants of the
simulation (`R = 1000`, modulus `M`, bound `H`, the node's real memory at `βN + a`), the glue
before Klein's part simulated, the two parts on natural words, the end of the node simulated. -/
def nodeProgNN (p₀ p₁ : KPN) (M H βN : ℕ) : Stmt :=
  .seq (.seq (ModNat.constsS 1000 M H βN) (ModNat.toNat 1000 M (.seq bdSet bdryProg))) <|
  .seq (if p₀.Kw ≤ p₁.Kw then kPairN 0 807 p₀ 1 808 p₁ else kPairN 1 808 p₁ 0 807 p₀)
    (ModNat.toNat 1000 M restProg)

/-- **`nodeProgNN` has no real instruction and no real test** (checked by the kernel). -/
theorem nodeProgNN_natOnly (p₀ p₁ : KPN) (M H βN : ℕ) :
    Klein.natOnly (nodeProgNN p₀ p₁ M H βN) = true := by
  have h1 : Klein.natOnly (ModNat.constsS 1000 M H βN) = true := by kernel_rfl
  have h2 : Klein.natOnly (ModNat.toNat 1000 M (.seq bdSet bdryProg)) = true := by kernel_rfl
  have h3 : Klein.natOnly (ModNat.toNat 1000 M restProg) = true := by kernel_rfl
  have h4 : Klein.natOnly
      (if p₀.Kw ≤ p₁.Kw then kPairN 0 807 p₀ 1 808 p₁ else kPairN 1 808 p₁ 0 807 p₀) = true := by
    split_ifs <;> exact kPairN_natOnly _ _ _ _ _ _
  simp only [nodeProgNN, Klein.natOnly, h1, h2, h3, h4, Bool.and_self]

theorem prefix_regsOK : (Stmt.seq bdSet bdryProg).regsOK (fun r => decide (r < 1000)) = true := by
  decide +kernel

theorem prefix_noDivR : (Stmt.seq bdSet bdryProg).noDivR = true := by decide +kernel

theorem restProg_regs1000 : restProg.regsOK (fun r => decide (r < 1000)) = true := by
  decide +kernel

theorem restProg_noDivR : restProg.noDivR = true := by decide +kernel

/-- The layout of a part on natural words in the zone `z`, from the layout of the node. -/
theorem klayN_of {b w k nD n Kw Pb δb β Rk Z Y S W' z : ℕ} (hz : z ≤ 1) (h1 : b ≤ S)
    (h2 : b * b ≤ S) (h3 : k ≤ S) (h5 : 2 * Kw + 1 < Z) (h6 : n + k * k ≤ Z)
    (h8 : Z ≤ δb) (h9 : δb + w ≤ Y) (h10 : Y + 16 * S ≤ Pb) (h11 : Y + 16 * S ≤ β)
    (h12 : Y + 16 * S ≤ Rk) (h13 : Y + 16 * S ≤ W') (h14 : Pb + w ≤ W')
    (h15 : Rk + (3 * nD + 3) ≤ W') (h16 : β + Kw ≤ W') (h17 : w + 1 ≤ W') (h18 : Z ≤ Y) :
    KLayN b w k nD n Kw (Y + 2 * S) Pb δb (Y + (3 + 5 * z) * S) S β Rk (2 * W' + 2) (W' + 1)
      W' := by
  obtain ⟨A, hA, hA'⟩ : ∃ A, Y + (3 + 5 * z) * S = Y + 3 * S + A ∧ A ≤ 5 * S := by
    rcases (by omega : z = 0 ∨ z = 1) with rfl | rfl
    · exact ⟨0, by ring, by omega⟩
    · exact ⟨5 * S, by ring, le_rfl⟩
  rw [hA]
  exact ⟨h3, h1, h2, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega⟩

end NegSSSP

end PlanarFlow
