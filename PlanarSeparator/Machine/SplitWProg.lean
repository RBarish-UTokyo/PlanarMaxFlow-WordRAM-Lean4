module

public import PlanarSeparator.Machine.SplitWBack

/-!
# The split of a node on the machine

**`PlanarSeparator.Piece.splitWProg`** computes `PlanarSeparator.SepRoutine.splitW` of the square
of `G` with the separator `sqSep` of the square (`squareProg`), for a vertex set `U` given as a
sorted list: the front `swFront` (the closed neighbourhoods, the list of `U ∪ B`, the weights
`spMu`, the first frame), the division `divLoop`, the back `swBack` (the names of the pieces,
the balanced split, the three parts, the zeros).

Main result: **`splitWProg_spec`**: from the state between splits `SWB` and the sorted list of
`U` at `aW` (`nreg 1420`, size in `1421`), the separator `(splitW …).1` is written as a sorted
list at the output buffer `aO` (`nreg 1422`, size in `1423`), the two parts in place of the list
of `U` (sizes in `1424`, `1425`), the state between splits holds again, within
`430 N + 362 + 22 ∑_{N[U]} deg` steps plus the cost `dcost` of the division.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset NestedDissection WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {W : ℕ} {P : Input}

/-- **The split of a node** on the machine. -/
def splitWProg : Stmt := .seq swFront (.seq divLoop swBack)

set_option maxHeartbeats 4000000 in
/-- **The split of a node on the machine**: the three parts of `splitW` of the square. -/
theorem splitWProg_spec {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) {Z M aS aP aV aF aZ aCW aCB aSn aJ aW aO : ℕ} {c : Config}
    (hc : SWB G R Z W M aS aP aV aF aZ aCW aCB aSn aJ c) {U : Finset (Fin N)}
    (h20 : c.nreg 1420 = aW) (h21 : c.nreg 1421 = #U) (h22 : c.nreg 1422 = aO)
    (hl : ∀ l < #U, c.nmem (aW + l) = lv U l) (lW : aJ + N ≤ aW) (lW' : aW + N ≤ W)
    (lO : aJ + N ≤ aO) (lO' : aO + N ≤ W) (ldisj : aO + #U ≤ aW ∨ aW + #U ≤ aO) :
    ∃ c' k, Exec P W splitWProg c c' k ∧
      k ≤ 430 * N + 362 + 22 * ∑ v ∈ closedNbhd G U, G.degree v +
        dcost (sqSep hR hΔ) (spMu (square G) U) (spL (square G) U) Δ
          #(closedNbhd G (closedNbhd G U)) (closedNbhd G (closedNbhd G U)) ∧
      SWB G R Z W M aS aP aV aF aZ aCW aCB aSn aJ c' ∧
      c'.nreg 1423 = #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).1 ∧
      (∀ t < #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).1,
        c'.nmem (aO + t) = lv (SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).1 t) ∧
      c'.nreg 1424 = #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.1 ∧
      (∀ t < #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.1,
        c'.nmem (aW + t) = lv (SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.1 t) ∧
      c'.nreg 1425 = #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.2 ∧
      (∀ t < #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.2,
        c'.nmem (aW + #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.1 + t) =
          lv (SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.2 t) ∧
      (∀ r, (KeptS r ∧ r ≠ 1201) ∨ 1426 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, aJ + N ≤ a → (a < aO ∨ aO + #U ≤ a) → (a < aW ∨ aW + #U ≤ a) →
        c'.nmem a = c.nmem a) ∧
      c'.output = c.output := by
  have hb := hc.base
  have := hb.lU; have := hb.lC; have := hb.lQ; have := hb.lW; have := hb.lS; have := hb.l0
  have := hb.l1; have := hb.l2; have := hb.l3; have := hb.l4; have := hb.l5; have := hb.l6
  have := hb.l7; have := hb.lA; have := hb.lB; have := hb.lF; have := hb.lV
  have := hc.lay1; have := hc.lay2; have := hc.lay3; have := hc.lay4; have := hc.lay5
  have := hc.lay6; have := hc.lay7; have := hc.lay8; have := hc.lay9; have := hc.lay10
  set D := closedNbhd G (closedNbhd G U) with hD
  have hDN := card_le_N D
  obtain ⟨c₁, k₁, e₁, hk₁, hD₁, h15, hz₁, h04, h89, K1, M1, ou1, -, -⟩ :=
    swFront_exec (P := P) hc h20 h21 hl lW lW'
  obtain ⟨a', c₂, k₂, e₂, hD₂, -, -, hst, hk₂⟩ := divLoop_exec (P := P) hR hΔ hD₁ h15
  have hDN' : #(closedNbhd G (closedNbhd G U)) ≤ N := card_le_N _
  have hUD : U ⊆ D := (subset_closedNbhd U).trans (subset_closedNbhd _)
  have hDUB : U ∪ bdry (square G) U = D := by
    rw [bdry_square_eq U, union_sdiff_of_subset hUD]
  have hst' : a'.st = swSt hR hΔ U := by
    rw [hst]
    simp [DFr.flist, swFr, dFold, swSt, spSt, hDUB]
    rfl
  have kp : ∀ r, pA r = false → DKept r → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [hD₂.keep r h2, K1 r h1]
  have q : ∀ r, pA r = false → 1333 ≤ r → c₂.nreg r = c.nreg r := fun r h1 h2 =>
    kp r h1 (Or.inr (Or.inr h2))
  have e1100 := K1 1100 (by decide); have e1015 := K1 1015 (by decide)
  have e1103 := K1 1103 (by decide); have e1019 := K1 1019 (by decide)
  have e1200 := K1 1200 (by decide); have e1203 := K1 1203 (by decide)
  have O2 : ∀ a, aZ ≤ a → c₂.nmem a = c₁.nmem a := fun a ha => hD₂.mem a
    ⟨Or.inr (by rw [e1100]; omega), Or.inr (by rw [e1015]; omega),
      Or.inr (by rw [e1103]; omega), Or.inr (by rw [e1019]; omega),
      Or.inr (by rw [e1200]; omega), Or.inr (by omega)⟩
  have r1203 : c₂.nreg 1203 = c.nreg 1203 :=
    kp 1203 (by decide) (Or.inl ⟨by unfold KeptS; omega, by omega⟩)
  obtain ⟨c₃, k₃, e₃, hk₃, hsw, g23, gS, g24, gA, g25, gA', K3, M3, ou3⟩ :=
    swBack_exec (P := P) hR hΔ (U := U) (aV := aV) (aF := aF) (aCW := aCW) (aCB := aCB)
      (aSn := aSn) hD₂.base hD₂.rS hD₂.rP hD₂.rV hD₂.rF
      (by rw [hD₂.keep 1389 (Or.inr (Or.inr (by omega)))]; exact h89)
      (by rw [q 1390 (by decide) (by omega)]; exact hc.rZ)
      (by rw [q 1391 (by decide) (by omega)]; exact hc.rCW)
      (by rw [q 1392 (by decide) (by omega)]; exact hc.rCB)
      (by rw [q 1393 (by decide) (by omega)]; exact hc.rSn)
      (by rw [q 1394 (by decide) (by omega)]; exact hc.rJ)
      (by rw [q 1420 (by decide) (by omega)]; exact h20)
      (by rw [q 1421 (by decide) (by omega)]; exact h21)
      (by rw [q 1422 (by decide) (by omega)]; exact h22)
      (by rw [hD₂.keep 1404 (Or.inr (Or.inr (by omega)))]; exact h04)
      (by rw [r1203]; exact hc.lay1) hc.lay2 hc.lay3 hc.lay4 hc.lay5 hc.lay6 hc.lay7 hc.lay8
      hc.lay9 hc.lay10 lW lW' lO lO' ldisj hc.hMN hc.hM
      (fun x hx => by rw [(hD₂.arr x hx).1, hst'])
      (fun x hx => by rw [(hD₂.arr x hx).2, hst'])
      (fun x hx => by rw [O2 _ (by omega)]; exact hz₁ x hx)
      (fun x hx => by rw [O2 _ (by omega), M1 _ (by omega)]; exact hc.zCW x hx)
      (fun x hx => by rw [O2 _ (by omega), M1 _ (by omega)]; exact hc.zCB x hx)
      (fun x hx => by rw [O2 _ (by omega), M1 _ (by omega)]; exact hc.zSn x hx)
      (fun x hx => by rw [O2 _ (by omega), M1 _ (by omega)]; exact hc.zJ x hx)
      (fun j hj => by rw [O2 _ (by omega), M1 _ (by omega)]; exact hl j hj)
  have hcost : (swFr D aV).cost (sqSep hR hΔ) (spMu (square G) U) (spL (square G) U) Δ =
      dcost (sqSep hR hΔ) (spMu (square G) U) (spL (square G) U) Δ #D D := by
    simp [DFr.cost, swFr]
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by rw [hcost] at hk₂; omega, hsw, g23, gS, g24, gA, g25,
    gA', fun r hr => ?_, fun a h1 h2 h3 => ?_, by rw [ou3, hD₂.out, ou1]⟩
  · have hA : pA r = false := by
      rcases hr with ⟨hr, h1⟩ | hr
      · unfold KeptS at hr; simp only [pA]; simp; omega
      · simp only [pA]; simp; omega
    have hB : pB r = false := by
      rcases hr with ⟨hr, h1⟩ | hr
      · unfold KeptS at hr; simp only [pB]; simp; omega
      · simp only [pB]; simp; omega
    have hK : DKept r := by
      rcases hr with ⟨hr, h1⟩ | hr
      · exact Or.inl ⟨hr, h1⟩
      · exact Or.inr (Or.inr (by omega))
    rw [K3 r hB, kp r hA hK]
  · rw [M3 a h1 h2 h3, O2 a (by omega), M1 a (by omega)]

end Piece

end PlanarSeparator
