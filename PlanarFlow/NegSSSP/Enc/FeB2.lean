module

public import PlanarFlow.NegSSSP.Enc.FeB

/-!
# The composed encoder, phase B (continued): a cotree `C₁` of `C₀` and the isolating weights

* `feTs τ u v`: the vertices by their numbers, the root `u` replaced by `v`: the list whose
  parent darts are the parent array of `feB1_exec` (`feTs_mem`, `feTs_get`).
* `feB2Prog`, **`feB2_exec`**: `cotProg` on the tree `C₀` (the face of `g' 0` read from `NF`):
  **a tree `C₁ : DTree M'` of the faces rooted at the face of `g' 0`** with an order `cs`
  (`Klein.Orders`) and its parent darts `IC` at `O1 + FN`.
* `feB3Prog`, **`feB3_exec`**: `iwProg` on `C₁`: the words `FN + treeW C₁ d` at `WW + σ d`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

section Ts

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The vertices by their numbers, `u` replaced by `v`. -/
def feTs (τ : X ≃ Fin (Fintype.card X)) (u v : X) : List X :=
  (List.finRange (Fintype.card X)).map fun j => if τ.symm j = u then v else τ.symm j

lemma feTs_length (τ : X ≃ Fin (Fintype.card X)) (u v : X) :
    (feTs τ u v).length = Fintype.card X := by simp [feTs]

lemma feTs_mem (τ : X ≃ Fin (Fintype.card X)) {u v : X} (huv : u ≠ v) (y : X) :
    y ∈ feTs τ u v ↔ y ≠ u := by
  simp only [feTs, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, hj⟩
    split_ifs at hj with h
    · rw [← hj]; exact huv.symm
    · rw [← hj]; exact h
  · intro hy
    exact ⟨τ y, by simp [hy]⟩

lemma feTs_get (τ : X ≃ Fin (Fintype.card X)) (u v : X) {j : ℕ}
    (hj : j < (feTs τ u v).length) :
    (feTs τ u v)[j] = if τ.symm ⟨j, by rw [feTs_length] at hj; exact hj⟩ = u then v
      else τ.symm ⟨j, by rw [feTs_length] at hj; exact hj⟩ := by
  simp [feTs]

end Ts

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {σ₀ : D ≃ Fin (Fintype.card D)} {νv₀ : V ≃ Fin (Fintype.card V)}
  {τ₀ : F ≃ Fin (Fintype.card F)}

/-- The registers of `cotProg` on the tree `C₀` (all but `1401`, `1601`). -/
def feCotRegs (N FN A ITb RVb NFb of Z IVb ITc HDc : ℕ) : List (ℕ × ℕ) :=
  [(1700, N), (1701, A), (1702, ITb), (1703, RVb), (1704, NFb), (1705, of), (1706, Z),
    (1500, N), (1501, FN), (1502, Z + N), (1504, Z), (1505, Z + 3 * N),
    (1506, Z + 3 * N + FN + 1), (1507, Z + 3 * N + 2 * FN + 1), (1508, Z + 3 * N + 3 * FN + 1),
    (1509, Z + 3 * N + 4 * FN + 1), (1400, FN), (1402, Z + 3 * N + 2 * FN + 1),
    (1403, Z + 3 * N + 3 * FN + 1), (1404, Z + 3 * N + 4 * FN + 1), (1405, Z + 2 * N),
    (1406, Z + 4 * N + 4 * FN + 1), (1407, Z + 4 * N + 5 * FN + 1),
    (1408, Z + 4 * N + 6 * FN + 1), (1600, FN), (1602, Z + 4 * N + 6 * FN + 1), (1603, NFb),
    (1604, of), (1605, Z + 4 * N + 7 * FN + 1), (1606, Z + 4 * N + 7 * FN + 1 + FN),
    (1607, Z + 4 * N + 7 * FN + 1 + 2 * FN), (1608, Z + 4 * N + 7 * FN + 1 + 3 * FN + 1),
    (1609, Z + 4 * N + 7 * FN + 1 + 4 * FN + 1), (1610, Z + 4 * N + 7 * FN + 1 + 5 * FN + 1),
    (1611, Z + 4 * N + 7 * FN + 1 + 6 * FN + 1), (1612, Z + 4 * N + 7 * FN + 1 + 7 * FN + 1),
    (1613, IVb), (1614, ITc), (1615, HDc)]

/-- **`cotProg` with its registers** (the number of the root face loaded from `NF[a0]`). -/
def feCot (N FN A ITb RVb NFb of Z IVb ITc HDc a0 : ℕ) : Stmt :=
  .seq (feSet (feCotRegs N FN A ITb RVb NFb of Z IVb ITc HDc))
    (.seq (feLd2 1401 1601 (NFb + a0) of) cotProg)

theorem feCot_natOnly (N FN A ITb RVb NFb of Z IVb ITc HDc a0 : ℕ) :
    natOnly (feCot N FN A ITb RVb NFb of Z IVb ITc HDc a0) = true := by
  have h : natOnly cotProg = true := by kernel_rfl
  simp only [feCot, natOnly, feSet_natOnly, feLd2_natOnly, h, Bool.and_self]

set_option maxHeartbeats 4000000 in
/-- **`cotProg` with its registers on the machine**, for the map with the sources copied: any
tree `T` of the vertices given by the parent darts of a list `ts` (all the vertices but the root),
the root face `fe = face (g' 0)` read from `NF`. -/
theorem feCot_exec (hf : MSSP.FaceCycle M k g) (hM : M.IsPlane)
    (T : STFlow.DTree (srcMap hf).dual) {ts : List (SrcV V k)} (hts : ∀ y, y ∈ ts ↔ y ≠ T.root)
    {N FN A A' ITb RVb NFb Z IVb ITc HDc : ℕ}
    (cD : Fintype.card (SrcD D k) = N) (cF : Fintype.card (SrcF F k) = FN)
    (hA : ts.length = A) (c : Config) (hc : WordsBounded W c)
    (hIT : ∀ j (h : j < ts.length), c.nmem (ITb + j) = srcNum σ₀ (T.par ts[j]))
    (hRV : ∀ d, c.nmem (RVb + srcNum σ₀ d) = srcNum σ₀ ((srcMap hf).rev d))
    (hNF : ∀ d, c.nmem (NFb + srcNum σ₀ d) = (A' + N) + srcFNum τ₀ ((srcMap hf).face d))
    (lI : ITb + A ≤ Z) (lR : RVb + N ≤ Z) (lN : NFb + N ≤ Z) (lO : HDc + 2 ≤ Z)
    (liv : IVb + FN ≤ ITc) (lit : ITc + FN ≤ HDc) (wZ : Z + 4 * N + 15 * FN + 2 ≤ W)
    (wo : A' + N + FN ≤ W) :
    ∃ c' t, Exec P W (feCot N FN A ITb RVb NFb (A' + N) Z IVb ITc HDc
        (Fintype.card D)) c c' t ∧
      t ≤ 44 + cotCost N FN A ∧
      ∃ (C : STFlow.DTree (srcMap hf)) (cs : List (SrcF F k)),
        C.root = (srcMap hf).face (srcG hf 0) ∧
        (∀ x, x ≠ C.root → ¬ T.InT (C.par x)) ∧
        Orders C ((List.finRange (Fintype.card (SrcF F k))).map (srcFNum τ₀).symm) cs ∧
        (∀ i (h : i < ((List.finRange (Fintype.card (SrcF F k))).map (srcFNum τ₀).symm).length),
          c'.nmem (IVb + i) = (A' + N) +
            srcFNum τ₀ ((List.finRange (Fintype.card (SrcF F k))).map (srcFNum τ₀).symm)[i]) ∧
        (∀ i (h : i < cs.length), c'.nmem (ITc + i) = srcNum σ₀ (C.par cs[i])) ∧
        c'.nmem HDc = Fintype.card (SrcF F k) ∧ c'.nmem (HDc + 1) = cs.length ∧
        (∀ a, a < Z ∨ Z + 4 * N + 15 * FN + 2 ≤ a → a < IVb ∨ HDc + 2 ≤ a →
          c'.nmem a = c.nmem a) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  haveI : Nonempty (SrcD D k) := ⟨srcG hf 0⟩
  obtain ⟨-, -, -, g0⟩ := fe_roots (σ₀ := σ₀) (νv₀ := Fintype.equivFin V) hf
  have hN1 : 1 ≤ N := by rw [← cD]; exact Fintype.card_pos
  obtain ⟨c₁, k₁, e₁, hk₁, hn₁, hr₁, hm₁, hrm₁, ho₁⟩ :=
    feSet_exec (P := P) (feCotRegs N FN A ITb RVb NFb (A' + N) Z IVb ITc HDc) (by
      intro q hq; simp only [feCotRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only <;> clear * - lI lR lN lO liv lit wZ wo hN1 <;> omega) c hc
  have hgN : (srcNum σ₀ (srcG hf 0) : ℕ) < N := by rw [← cD]; exact (srcNum σ₀ _).2
  obtain ⟨c₂, k₂, e₂, hk₂, hm₂, h1401, h1601, hn₂, hr₂, hrm₂, ho₂⟩ :=
    feLd2_exec (P := P) (r₁ := 1401) (r₂ := 1601) (a := NFb + Fintype.card D) (o := A' + N)
      (by decide) (by decide) (by decide) (by rw [← g0]; clear * - lN wZ hgN; omega)
      (by clear * - wo; omega) c₁ e₁.wb_right
  have hfe : c₁.nmem (NFb + Fintype.card D) - (A' + N) =
      srcFNum τ₀ ((srcMap hf).face (srcG hf 0)) := by
    rw [hm₁, ← g0, hNF]; omega
  rw [hfe] at h1401 h1601
  have G : ∀ r, r ≠ 1401 → r ≠ 1601 → (r < 2450 ∨ 2459 < r) → c₂.nreg r =
      feSetV (feCotRegs N FN A ITb RVb NFb (A' + N) Z IVb ITc HDc) r (c.nreg r) :=
    fun r h1 h2 h3 => (hn₂ r h1 h2 h3).trans (hn₁ r)
  have hIT₂ : ∀ j (h : j < ts.length), c₂.nmem (ITb + j) = srcNum σ₀ (T.par ts[j]) :=
    fun j h => by rw [hm₂, hm₁]; exact hIT j h
  have hRV₂ : ∀ d, c₂.nmem (RVb + srcNum σ₀ d) = srcNum σ₀ ((srcMap hf).rev d) :=
    fun d => by rw [hm₂, hm₁]; exact hRV d
  have hNF₂ : ∀ d, c₂.nmem (NFb + srcNum σ₀ d) = (A' + N) + srcFNum τ₀ ((srcMap hf).face d) :=
    fun d => by rw [hm₂, hm₁]; exact hNF d
  subst cD cF hA
  obtain ⟨c₃, k₃, e₃, hk₃, C, cs, hCr, hoff, hOr, hIV, hIC, hH0, hH1, hm₃, -, hr₃, hrm₃, ho₃⟩ :=
    cotProg_exec (P := P) (srcMap_isPlane hf hM) T (srcNum σ₀) (srcFNum τ₀)
      ((srcMap hf).face (srcG hf 0)) hts c₂ e₂.wb_right
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV])) h1401
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ((G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]))
      ⟨(G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]), h1601,
        (G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]),
        (G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]),
        (G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]),
        (G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]),
        (G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]),
        (G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]),
        (G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]),
        (G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]),
        (G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]),
        (G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]),
        (G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]),
        (G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]),
        (G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV]),
        (G _ (by decide) (by decide) (by decide)).trans (by simp [feCotRegs, feSetV])⟩
      hIT₂ hRV₂ hNF₂ lI lR lN lO liv lit wZ (by clear * - wZ; omega) wo
  refine ⟨c₃, k₁ + (k₂ + k₃), Exec.seq e₁ (Exec.seq e₂ e₃), ?_, C, cs, hCr, hoff, hOr, hIV, hIC,
    by rw [hH0]; simp, hH1, fun a h1 h2 => ?_, by rw [hr₃, hr₂, hr₁], by rw [hrm₃, hrm₂, hrm₁],
    by rw [ho₃, ho₂, ho₁]⟩
  · simp [feCotRegs] at hk₁; clear * - hk₁ hk₂ hk₃; omega
  · rw [hm₃ a h1 h2, hm₂, hm₁]

end NegSSSP

end PlanarFlow
