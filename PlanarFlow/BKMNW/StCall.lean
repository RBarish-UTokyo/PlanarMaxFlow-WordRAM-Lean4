module

public import PlanarFlow.BKMNW.StCallH
public import PlanarFlow.BKMNW.MfZero

/-!
# One in-place call of the s-t flow program, from zero memory to zero memory

**`stCall_exec`**: at a map `M` numbered by `en` (`EnumOK` for `M` and its dual, plane,
transitive rotations), with capacities `c ≥ 0`, disjoint terminal sets `X`, `Y` (each the tail of
some dart), the frame arrays in memory above `Wz` (the reverses `rvI`, the rotation indices, the
capacities `(c (en i)).toNat`, the flags `[tail (en i) ∈ X]`, `[tail (en i) ∈ Y]`), the memory
`≤ Wz` zero (`MemZ`), the low image base `ib` with room for the natural run
(`pstWN W₀ (stHb M c X Y m) < ib`, `ib + pstWN W₀ (stHb …) ≤ Wz`, `W₀ = 101m + 45`), a scratch
`[Sb, Sb + stSz m)` above the arrays, an output `[Ob, Ob + m)` and a log
`[p, p + 3 (4 · pcoreB + 3))` above `Wz`, the fixed program **`stCall`** runs within
**`stCost m (4 · pcoreB V F m (4m+1) + 3)`** steps, ends with the memory `≤ Wz` **zero again**,
and writes at `Ob + i` (`i < m`) the word `max 0 (Z + g (en i))`, where

  `g = pstflowT M (isoEpsG (treeW C)) c X Y (tail d₁) d₀ T₀`

is the s-t flow of the explicit choices made by the machine: `d₁`, `d₀` the darts of greatest
index whose tails are in `X`, `Y` (`(enEq h d₁ : ℕ) = lastF XT m 0`, …), `C : DTree M.dual`
the search tree of the isolating weight (rooted at `tail d₀`), `T₀ : DTree M` the initial dual
tree from Dijkstra's tight parents (rooted at `face d₀`, meeting `LInv` for all terminals). The
memory above `Wz` outside the scratch, the output and the log is kept; registers outside `StScr`
kept; reals and output kept.

`stCost m K = hpCost stLayL + costA m + costB m + costC m + costD1 m + 27 K + 222 m + 112`:
linear in `m` plus the s-t flow program's own bound `K = 4 · pcoreB + 3` (and the
`O(m log m)` of Dijkstra in `costC`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace StCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP StEnc
  NsStep STFlow CombMap Klein MfDrv

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

variable {P : Input} {W : ℕ}

/-- **The step bound of one call** (`K` the bound `4 · pcoreB + 3` of the s-t flow program). -/
def stCost (m K : ℕ) : ℕ :=
  hpCost stLayL + costA m + costB m + costC m + costD1 m + 27 * K + 222 * m + 112

/-- The flags of a vertex set by dart index. -/
def flagX (M : CombMap D V F) (en : ℕ → D) (X : Finset V) (i : ℕ) : ℕ :=
  if M.tail (en i) ∈ X then 1 else 0

set_option maxHeartbeats 4000000 in
/-- **One in-place call of the s-t flow program** (see the module docstring). -/
theorem stCall_exec (hM : M.IsPlane) (hrot : M.RotTrans) (h : EnumOK M en m)
    (h' : EnumOK M.dual en m) (hm : 0 < m) {cp : D → ℤ} (hcp : ∀ d, 0 ≤ cp d) {X Y : Finset V}
    (hXY : Disjoint X Y) (hXn : ∃ d, M.tail d ∈ X) (hYn : ∃ d, M.tail d ∈ Y)
    (c : Config) (hc : WordsBounded W c) {RVb RTb Cb Xb Yb Sb ib Ob Z p Wz : ℕ}
    (r00 : c.nreg 9100 = m) (r01 : c.nreg 9101 = RVb) (r02 : c.nreg 9102 = RTb)
    (r03 : c.nreg 9103 = Cb) (r04 : c.nreg 9104 = Xb) (r05 : c.nreg 9105 = Yb)
    (r06 : c.nreg 9106 = Sb) (r07 : c.nreg 9107 = ib) (r08 : c.nreg 9108 = Ob)
    (r09 : c.nreg 9109 = Z) (r10 : c.nreg 9110 = p)
    (hRV : ∀ i < m, c.nmem (RVb + i) = rvI M en m i)
    (hRT : ∀ i < m, c.nmem (RTb + i) = ixOf en m (M.rot (en i)))
    (hC : ∀ i < m, c.nmem (Cb + i) = (cp (en i)).toNat)
    (hX : ∀ i < m, c.nmem (Xb + i) = flagX M en X i)
    (hY : ∀ i < m, c.nmem (Yb + i) = flagX M en Y i)
    (hz : MemZ Wz c)
    (oR : Wz < RVb) (oT : Wz < RTb) (oC : Wz < Cb) (oX : Wz < Xb) (oY : Wz < Yb)
    (lR : RVb + m ≤ Sb) (lT : RTb + m ≤ Sb) (lC : Cb + m ≤ Sb) (lX : Xb + m ≤ Sb)
    (lY : Yb + m ≤ Sb) (hSW : Sb + stSz m ≤ W)
    (hib : pstWN (101 * m + 45) (stHb M cp X Y m) < ib)
    (hibz : ib + pstWN (101 * m + 45) (stHb M cp X Y m) ≤ Wz)
    (hO : Wz < Ob) (hOp : Ob + m ≤ p)
    (hpW : p + 3 * (4 * pcoreB V F m (4 * m + 1) + 3) ≤ W) (hZW : Z + Wz ≤ W)
    (hWq : (4 * m + 5) * m + 2 * m + 1 ≤ W) (hWS : ∑ d, cp d + 1 ≤ (W : ℤ)) :
    ∃ c' t, Exec P W stCall c c' t ∧ t ≤ stCost m (4 * pcoreB V F m (4 * m + 1) + 3) ∧
      MemZ Wz c' ∧
      (∃ (d₀ d₁ : D) (C : DTree M.dual) (T₀ : DTree M),
        M.tail d₁ ∈ X ∧ (enEq h d₁ : ℕ) = StEnc.lastF (flagX M en X) m 0 ∧
        M.tail d₀ ∈ Y ∧ (enEq h d₀ : ℕ) = StEnc.lastF (flagX M en Y) m 0 ∧
        C.root = M.tail d₀ ∧ T₀.root = M.face d₀ ∧
        (∀ s t', LInv (capR M cp X Y) (isoEpsG V F (MSSP.treeW C)) s t'
          (tSt M (capR M cp X Y) (isoEpsG V F (MSSP.treeW C)) T₀)) ∧
        ∀ i < m, (c'.nmem (Ob + i) : ℤ) =
          max 0 ((Z : ℤ) + pstflowT M (isoEpsG V F (MSSP.treeW C)) cp X Y (M.tail d₁) d₀ T₀
            (en i))) ∧
      (∀ a, Wz < a → (a < Sb ∨ Sb + stSz m ≤ a) → (a < Ob ∨ Ob + m ≤ a) →
        (a < p ∨ p + 3 * (4 * pcoreB V F m (4 * m + 1) + 3) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ StScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hSz : stSz m = 132 * m + 36 := rfl
  rw [hSz] at hSW
  have hWN : 2 * (101 * m + 45) + 1 + pstM (stHb M cp X Y m) * pstM (stHb M cp X Y m) +
      pstM (stHb M cp X Y m) = pstWN (101 * m + 45) (stHb M cp X Y m) := rfl
  have hMb : pstM (stHb M cp X Y m) ≤ pstM (stHb M cp X Y m) * pstM (stHb M cp X Y m) :=
    Nat.le_mul_of_pos_left _ (by unfold pstM; omega)
  have hWz1 : 202 * m + 91 ≤ Wz := by omega
  have hWzW : Wz < W := by
    have := WordsBounded.nreg hc 9108; omega
  -- the flags
  have hXT : ∀ d, flagX M en X (enEq h d) = if M.tail d ∈ X then 1 else 0 := fun d => by
    simp only [flagX, enEq_val, en_ixOf h]
  have hYT : ∀ d, flagX M en Y (enEq h d) = if M.tail d ∈ Y then 1 else 0 := fun d => by
    simp only [flagX, enEq_val, en_ixOf h]
  obtain ⟨d₁, hd₁, hσ₁⟩ := lastF_map (enEq h) hXT hXn
  obtain ⟨d₀, hd₀, hσ₀⟩ := lastF_map (enEq h) hYT hYn
  -- 0. the layout
  obtain ⟨c₁, eP, hL₁, kP, mP, rP, rmP, oP⟩ := stPro_exec (P := P) c hc r00 r06 (by omega)
    (by omega)
  have g1 : ∀ r, 9100 ≤ r → r ≤ 9110 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    kP r (by omega) (by omega) (by omega)
  -- 1. the map stage
  obtain ⟨c₂, tA, eA, htA, nF, nV, τv, τf, a83, a84, hK₂, hG0₂, hG1₂, mA, kA, rA, rmA, oA⟩ :=
    stA_exec (P := P) h h' hm c₁ eP.wb_right (Sb := Sb) (RVb := RVb) (RTb := RTb) (Xb := Xb)
      (Yb := Yb) (XT := flagX M en X) (YT := flagX M en Y) hL₁
      ((g1 _ (by omega) (by omega)).trans r00) ((g1 _ (by omega) (by omega)).trans r01)
      ((g1 _ (by omega) (by omega)).trans r02) ((g1 _ (by omega) (by omega)).trans r04)
      ((g1 _ (by omega) (by omega)).trans r05) ((g1 _ (by omega) (by omega)).trans r06)
      (fun i hi => by rw [mP]; exact hRV i hi) (fun i hi => by rw [mP]; exact hRT i hi)
      (fun i hi => by rw [mP]; exact hX i hi) (fun i hi => by rw [mP]; exact hY i hi)
      lR lT lX lY (by rw [hSz]; omega)
  have hcF : Fintype.card F = nF := by rw [Fintype.card_congr τv, Fintype.card_fin]
  have hcV : Fintype.card V = nV := by rw [Fintype.card_congr τf, Fintype.card_fin]
  have hFm : nF ≤ m := hcF ▸ card_F_le h
  have hVm : nV ≤ m := hcV ▸ card_V_le h'
  have g2 : ∀ r, 9100 ≤ r → r ≤ 9182 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    kA r (by unfold EncScr; omega) (by omega) (by omega)
  have hL₂ : StL c₂.nreg m Sb := hL₁.frame (fun r h1 h2 => g2 r (by omega) h2)
  -- 2. the weight stage
  obtain ⟨c₃, tB, eB, htB, C, hCr, b45, b46, bWT, bPH, bCP, bRS, bTH, bH0, bGap, mB, kB, rB,
      rmB, oB⟩ :=
    stB_exec (P := P) hM h h' hm hcp (X := X) (Y := Y) (d₀ := d₀) c₂ eA.wb_right (Sb := Sb)
      (Cb := Cb) (Xb := Xb) (Yb := Yb) τv τf hL₂
      ((g2 _ (by omega) (by omega)).trans ((g1 _ (by omega) (by omega)).trans r00))
      ((g2 _ (by omega) (by omega)).trans ((g1 _ (by omega) (by omega)).trans r03))
      ((g2 _ (by omega) (by omega)).trans ((g1 _ (by omega) (by omega)).trans r04))
      ((g2 _ (by omega) (by omega)).trans ((g1 _ (by omega) (by omega)).trans r05)) a83 a84 hK₂
      (by rw [hG1₂, hσ₀])
      (fun i hi => by rw [mA _ (Or.inl (by omega)), mP]; exact hC i hi)
      (fun i hi => by rw [mA _ (Or.inl (by omega)), mP]; exact hX i hi)
      (fun i hi => by rw [mA _ (Or.inl (by omega)), mP]; exact hY i hi)
      lC lX lY (by omega) (by omega) (by omega) (by rw [hSz]; omega) hWq hWS (by omega)
  have hw : IsIsoW M (M.tail d₀) (MSSP.treeW C) := by rw [← hCr]; exact isIsoW_treeW C
  have hHb' := stH_le hM hw (capR_nonneg (M := M) hcp X Y) (4 * m + 1)
  have hHn := pcoreH_ge (V := V) (F := F) (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
    (capR M cp X Y) (isoEpsG V F (MSSP.treeW C))
  generalize hHdef : pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
    (capR M cp X Y) (isoEpsG V F (MSSP.treeW C)) = H at b45 b46 bWT bPH bCP bRS bTH bH0 hHb' hHn
  have hHb2 : H ≤ stHb M cp X Y m := hHb'
  have hMo : pstM H ≤ pstM (stHb M cp X Y m) := by unfold pstM; omega
  have hWNH : pstWN (101 * m + 45) H ≤ pstWN (101 * m + 45) (stHb M cp X Y m) :=
    pstWN_mono hHb2
  have hMoWN : pstM H ≤ pstWN (101 * m + 45) H := by unfold pstWN; omega
  have g3 : ∀ r, 9100 ≤ r → r ≤ 9184 → r ≠ 9145 → r ≠ 9146 → c₃.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 h4 => kB r (by unfold EncScr; omega) h3 h4
  have hL₃ : StL c₃.nreg m Sb :=
    hL₂.frame (fun r h1 h2 => g3 r (by omega) (by omega) (by omega) (by omega))
  -- the image after the weight stage
  have hK₃ : KInM M.dual (enEq h) (fun x => 1 + (τv x : ℕ)) (ιG M h)
      (fun y => 2 * m + 1 + (τf y : ℕ)) (ιE M h) c₃.nmem (Sb + 3 * m) :=
    hK₂.move (E := 4 * m + 1) (ιE_lt h) (fun i hi => mB _ (Or.inl (by omega)) (Or.inr (by omega)))
  -- 3. the tree stage
  obtain ⟨c₄, tC, eC, htC, T₀, ts, C₀, cs, hroot, hLI, hC₀, hoff, hOT, hOC, hIV, hIT, hIF, hIC,
      hH0, hH1, hH2, hH3, mC, kC, rC, rmC, oC⟩ :=
    stC_exec (P := P) hM h h' hm hcp X Y (d₀ := d₀) (d₁ := d₁) hw c₃ eB.wb_right τv τf hL₃
      ((g3 _ (by omega) (by omega) (by omega) (by omega)).trans ((g2 _ (by omega) (by omega)).trans
        ((g1 _ (by omega) (by omega)).trans r00)))
      ((g3 _ (by omega) (by omega) (by omega) (by omega)).trans a83)
      ((g3 _ (by omega) (by omega) (by omega) (by omega)).trans a84) (by rw [hHdef]; exact b46) hK₃
      (by rw [mB _ (Or.inl (by omega)) (Or.inr (by omega)), hG0₂, hσ₁])
      (by rw [mB _ (Or.inl (by omega)) (Or.inr (by omega)), hG1₂, hσ₀]) (by rw [hHdef]; exact bWT)
      (by omega) (by rw [hSz]; omega) (by omega)
  have g4 : ∀ r, 9100 ≤ r → r < 9200 → c₄.nreg r = c₃.nreg r := fun r h1 h2 =>
    kC r (by unfold EncScr; omega)
  have hL₄ : StL c₄.nreg m Sb := hL₃.frame (fun r h1 h2 => g4 r (by omega) (by omega))
  have q : ∀ r, 9100 ≤ r → r ≤ 9110 → c₄.nreg r = c.nreg r := fun r h1 h2 => by
    rw [g4 r h1 (by omega), g3 r h1 (by omega) (by omega) (by omega), g2 r h1 (by omega),
      g1 r h1 h2]
  have q45 : c₄.nreg 9145 = H := (g4 _ (by omega) (by omega)).trans b45
  have q46 : c₄.nreg 9146 = pstM H := (g4 _ (by omega) (by omega)).trans b46
  -- the low memory before the run stage
  have lowB : ∀ a, a ≤ Wz → (a < 101 * m + 46 ∨ 106 * m + 49 ≤ a) → c₄.nmem a = 0 :=
    fun a h1 h2 => by
      rw [mC a (Or.inl (by omega)) (Or.inl (by omega)), mB a (Or.inl (by omega)) h2,
        mA a (Or.inl (by omega)), mP, hz a h1]
  have resC : ∀ a, 101 * m + 46 ≤ a → a < 106 * m + 49 → c₄.nmem a = c₃.nmem a :=
    fun a h1 h2 => mC a (Or.inl (by omega)) (Or.inl (by omega))
  -- 4. the image at `ib`, the parameters
  have hVz := wz_bound (ib := ib) (show 4 * m + 2 ≤ H by omega)
  obtain ⟨c₅, tD1, eD1, htD1, z1, zv, z50, z51, hcl, mD1, kD1, rD1, rmD1, oD1⟩ :=
    stD1_exec (P := P) c₄ eC.wb_right hL₄ ((q _ (by omega) (by omega)).trans r00)
      ((q _ (by omega) (by omega)).trans r07) ((q _ (by omega) (by omega)).trans r10) q45 q46
      (Or.inl (by omega)) (by rw [hSz]; omega) (by omega)
  have hKi := img_ib h τv τf hFm hVm (hts := by have := hOT.ylen; rw [hcF] at this; omega)
    (hcs := by have := hOC.ylen; rw [hcV] at this; omega) (d₀ := d₀) (d₁ := d₁) (mem := c₄.nmem)
    (mem' := c₅.nmem) (Sb := Sb) (ib := ib)
    (hK₃.move (E := 4 * m + 1) (ιE_lt h)
      (fun i hi => mC _ (Or.inl (by omega)) (Or.inl (by omega))))
    (by rw [mC _ (Or.inl (by omega)) (Or.inl (by omega)),
      mB _ (Or.inl (by omega)) (Or.inr (by omega)), hG0₂, hσ₁])
    (by rw [mC _ (Or.inl (by omega)) (Or.inl (by omega)),
      mB _ (Or.inl (by omega)) (Or.inr (by omega)), hG1₂, hσ₀])
    hIV hIT hIF hIC hH0 hH1 hH2 hH3 hcl
  obtain ⟨iK, iG0, iG1, iIV, iIT, iIF, iIC, iH0, iH1, iH2, iH3, ibd⟩ := hKi
  -- the low memory of the run
  have mlow : ∀ a, a < ib → c₅.nmem a = c₄.nmem a := fun a ha => mD1 a (Or.inl ha)
  have res5 : ∀ a < 5 * m + 3, c₅.nmem (101 * m + 46 + a) < pstM H := by
    have := res_lt h (mem := c₅.nmem) (Mo := pstM H) (by unfold pstM; omega)
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aWT; omega),
          resC _ (by omega) (by have := (enEq h e).2; unfold aWT; omega)]; exact bWT e)
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aPH; omega),
          resC _ (by omega) (by have := (enEq h e).2; unfold aPH; omega)]; exact bPH e)
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aCP; omega),
          resC _ (by omega) (by have := (enEq h e).2; unfold aCP; omega)]; exact bCP e)
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aRS; omega),
          resC _ (by omega) (by have := (enEq h e).2; unfold aRS; omega)]; exact bRS e)
      (by rw [mlow _ (by unfold aTH; omega), resC _ (by omega) (by unfold aTH; omega)]; exact bTH)
      (by rw [mlow _ (by unfold aH0; omega), resC _ (by omega) (by unfold aH0; omega)]; exact bH0)
      (fun i hi => by
        rw [mlow _ (by omega), resC _ (by omega) (by omega)]; exact bGap i hi)
    exact this
  have low5 : ∀ a, a ≤ Wz → (a < 101 * m + 46 ∨ 106 * m + 49 ≤ a) →
      (a < ib ∨ ib + (37 * m + 13) ≤ a) → c₅.nmem a = 0 := fun a h1 h2 h3 => by
    rw [mD1 a h3, lowB a h1 h2]
  have res5' : ∀ a ≤ 101 * m + 45, c₅.nmem (101 * m + 46 + a) < pstM H := fun a ha => by
    by_cases h1 : a < 5 * m + 3
    · exact res5 a h1
    · rw [low5 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))]; unfold pstM; omega
  -- 5. the logged run
  obtain ⟨c₆, tD2, j, eD2, htD2, hj, hOUT, hLK, hb6, rD2, rmD2, oD2⟩ :=
    stD2_exec (P := P) hM hrot h h' hm hcp hXY hd₁ hd₀ hCr hroot (hLI _ _) τv τf hOT hOC hoff hC₀
      c₅ eD1.wb_right (ib := ib) (p := p) (Wz := Wz) (H := H) hHdef.symm z1 zv z50 z51 iK iG0 iG1 iIV
      iIT iIF iIC iH0 iH1 iH2 iH3 ibd
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aWT; omega),
          resC _ (by omega) (by have := (enEq h e).2; unfold aWT; omega)]; exact bWT e)
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aPH; omega),
          resC _ (by omega) (by have := (enEq h e).2; unfold aPH; omega)]; exact bPH e)
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aCP; omega),
          resC _ (by omega) (by have := (enEq h e).2; unfold aCP; omega)]; exact bCP e)
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aRS; omega),
          resC _ (by omega) (by have := (enEq h e).2; unfold aRS; omega)]; exact bRS e)
      (by rw [mlow _ (by unfold aTH; omega), resC _ (by omega) (by unfold aTH; omega)]; exact bTH)
      (by rw [mlow _ (by unfold aH0; omega), resC _ (by omega) (by unfold aH0; omega)]; exact bH0)
      (fun a ha => low5 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
      (fun a ha => res5' a ha)
      (fun a ha => by
        by_cases h1 : 101 * m + 46 ≤ a ∧ a < 106 * m + 49
        · have := res5 (a - (101 * m + 46)) (by omega)
          rw [show 101 * m + 46 + (a - (101 * m + 46)) = a by omega] at this; omega
        · rw [low5 a (by omega) (by omega) (Or.inl (by omega))]; exact Nat.zero_le _)
      (fun a ha => by
        by_cases h1 : 101 * m + 46 ≤ a ∧ a < 106 * m + 49
        · have := res5 (a - (101 * m + 46)) (by omega)
          rw [show 101 * m + 46 + (a - (101 * m + 46)) = a by omega] at this; omega
        · by_cases h2 : ib ≤ a ∧ a < ib + (37 * m + 13)
          · have := ibd (a - ib) (by omega)
            rw [show ib + (a - ib) = a by omega] at this; omega
          · rw [low5 a ha (by omega) (by omega)]; exact Nat.zero_le _)
      (fun i h1 h2 => low5 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  -- 6. the read-back and the clearing
  have g6 : ∀ r, 9100 ≤ r → r < 9200 → (r < 9120 ∨ 9128 < r) → r ≠ 9150 → r ≠ 9151 →
      c₆.nreg r = c₄.nreg r := fun r h1 h2 h3 h4 h5 => by
    rw [hLK.nreg r (by simp; omega) h4, kD1 r (by omega) (by omega) h3 h4 h5]
  have hL₆ : StL c₆.nreg m Sb :=
    hL₄.frame (fun r h1 h2 => g6 r (by omega) (by omega) (by omega) (by omega) (by omega))
  have q6 : ∀ r, 9100 ≤ r → r ≤ 9110 → c₆.nreg r = c.nreg r := fun r h1 h2 => by
    rw [g6 r h1 (by omega) (by omega) (by omega) (by omega), q r h1 h2]
  obtain ⟨c₇, tD3, eD3, htD3, O7, Z7, K7, R7, rD3, rmD3, oD3⟩ :=
    stD3_exec (P := P) c₆ eD2.wb_right (j := j) (Wz := Wz) hL₆
      ((q6 _ (by omega) (by omega)).trans r00) ((q6 _ (by omega) (by omega)).trans r07)
      ((q6 _ (by omega) (by omega)).trans r08) ((q6 _ (by omega) (by omega)).trans r09)
      ((q6 _ (by omega) (by omega)).trans r10)
      ((g6 _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans q45)
      ((g6 _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans q46) hLK.lp
      hLK.logle (by omega) hO hOp
      (fun i hi => by have := hb6 (107 * m + 49 + i) (by omega); omega) (by omega) (by omega)
      (by omega)
  refine ⟨c₇, _, eP.seq (eA.seq (eB.seq (eC.seq (eD1.seq (eD2.seq eD3))))), ?_,
    fun a ha => ?_, ⟨d₀, d₁, C, T₀, hd₁, hσ₁, hd₀, hσ₀, hCr, hroot, hLI, fun i hi => ?_⟩,
    fun a h1 h2 h3 h4 => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have h3 := htD3
    unfold costD3 at h3
    unfold stCost
    omega
  · by_cases hl : (∃ i < j, c₆.nmem (p + i) = a) ∨ (101 * m + 46 ≤ a ∧ a < 106 * m + 49) ∨
        (ib ≤ a ∧ a < ib + (37 * m + 13))
    · exact Z7 a hl
    · simp only [not_or, not_exists, not_and, not_le, not_lt] at hl
      obtain ⟨hl1, hl2, hl3⟩ := hl
      rw [K7 a (fun i hi e => hl1 i hi e) (by omega) (by omega) (Or.inl (by omega)),
        hLK.dirty a ha (fun i hi e => hl1 i hi e),
        low5 a ha (by omega) (by omega)]
  · rw [O7 i hi, rdv_eq, hOUT i hi]
  · have hnl : ∀ i < j, c₆.nmem (p + i) ≠ a := fun i hi e => by
      have := hLK.logle i hi; omega
    rw [K7 a hnl (by omega) (by omega) h3, hLK.nmem a h1 (by omega), mD1 a (by omega),
      mC a (by omega) (by omega), mB a (by omega) (by omega), mA a (by omega), mP]
  · unfold StScr EncScr at hr
    rw [R7 r (by omega) (by omega) (by omega), hLK.nreg r (by simp; omega) (by omega),
      kD1 r (by omega) (by omega) (by omega) (by omega) (by omega),
      kC r (by unfold EncScr; omega), kB r (by unfold EncScr; omega) (by omega) (by omega),
      kA r (by unfold EncScr; omega) (by omega) (by omega), kP r (by omega) (by omega) (by omega)]
  · rw [rD3, rD2, rD1, rC, rB, rA, rP]
  · rw [rmD3, rmD2, rmD1, rmC, rmB, rmA, rmP]
  · rw [oD3, oD2, oD1, oC, oB, oA, oP]

end StCall

end BKMNW

end PlanarFlow
