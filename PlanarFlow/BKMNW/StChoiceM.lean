module

public import PlanarFlow.BKMNW.StCallZB

/-!
# The choices of the machine's s-t flow, and the flow it computes

* `StGood M h I c X Y`: the canonical run of the encoders (from `stCan m (stArr …)`, word bound
  `stWc`, input `I`) ends in a configuration meeting `EncFacts` for some trees `C`, `T₀`;
* **`stChoiceOf h I : STFlow.StChoice M`** (for a map numbered by `en`, `[Nonempty (DTree M)]` for
  the inputs where nothing is chosen): the source `tail (stDart X)`, the sink dart `stDart Y`
  (the darts of greatest index with tail in `X`, `Y`), the perturbation `isoEpsG (treeW C)` and
  the tree `T₀` of the canonical run — **functions of the capacities and the terminals only**
  (the machine's choices, read off the canonical run);
* **`stChoiceOf_OK`**: on a plane map with transitive rotations and `EnumOK` for the map and its
  dual, the choices are valid (`StChoice.OK`), so `STFlow.StChoice.spec` applies;
* **`stCallZ_exec`**: the fixed program `stCallZ` at any configuration holding the frame arrays
  (any addresses above `Wz`, `MemZ Wz`, the room conditions) ends with `MemZ Wz` again and writes
  at `Ob + i` the word **`max 0 (Z + (stChoiceOf h I).flow c X Y (en i))`** — the s-t flow of the
  explicit choices `stChoiceOf h I`, by the locality lemma `stE_lift` (the run of the encoders at
  the call agrees with the canonical run on every word they write).

With `chs x h' := stChoiceOf (EnumOK of the frame order of the call) I`, this is the s-t flow of
`NsStep.machMOS gid I chs` at the call (`machMOS_stflow`).
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

variable (M) in
/-- **The canonical run of the encoders succeeds** (for some trees `C`, `T₀`). -/
def StGood (h : EnumOK M en m) (I : Input) (cp : D → ℤ) (X Y : Finset V) : Prop :=
  ∃ (C : DTree M.dual) (T₀ : DTree M) (c' : Config) (t : ℕ),
    Exec I (stWc M cp X Y m) stE (stCan m (stArr M en m cp X Y)) c' t ∧ t ≤ costE m ∧
      EncFacts h cp X Y c' C T₀

/-- **The choices of the machine's s-t flow** (see the module docstring). -/
noncomputable def stChoiceOf (h : EnumOK M en m) (I : Input) [Nonempty (DTree M)] :
    StChoice M := by
  classical
  exact
  { src := fun _ X _ => M.tail (stDart M en m X)
    snk := fun _ _ Y => stDart M en m Y
    eps := fun cp X Y => if hg : StGood M h I cp X Y then isoEpsG V F (MSSP.treeW hg.choose)
      else fun _ => 0
    tree := fun cp X Y => if hg : StGood M h I cp X Y then hg.choose_spec.choose
      else Classical.arbitrary _ }

lemma stChoiceOf_flow (h : EnumOK M en m) (I : Input) [Nonempty (DTree M)] {cp : D → ℤ}
    {X Y : Finset V} (hg : StGood M h I cp X Y) :
    (stChoiceOf h I).flow cp X Y = pstflowT M (isoEpsG V F (MSSP.treeW hg.choose)) cp X Y
      (M.tail (stDart M en m X)) (stDart M en m Y) hg.choose_spec.choose := by
  classical
  simp only [StChoice.flow, stChoiceOf, dif_pos hg]

lemma stDart_mem (h : EnumOK M en m) {X : Finset V} (hX : ∃ d, M.tail d ∈ X) :
    M.tail (stDart M en m X) ∈ X ∧ (enEq h (stDart M en m X) : ℕ) = StEnc.lastF (flagX M en X) m 0 := by
  have hXT : ∀ d, flagX M en X (enEq h d) = if M.tail d ∈ X then 1 else 0 := fun d => by
    simp only [flagX, enEq_val, en_ixOf h]
  obtain ⟨d₁, hd₁, hσ₁⟩ := lastF_map (enEq h) hXT hX
  have e : stDart M en m X = d₁ := by unfold stDart; rw [← hσ₁]; exact en_ixOf h d₁
  rw [e]; exact ⟨hd₁, hσ₁⟩

/-- **The choices are valid.** -/
theorem stChoiceOf_OK (hM : M.IsPlane) (h : EnumOK M en m) (h' : EnumOK M.dual en m)
    (hm : 0 < m) (I : Input) [Nonempty (DTree M)] : (stChoiceOf h I).OK := by
  classical
  intro cp X Y hcp hXY hXn hYn
  have hX : ∃ d, M.tail d ∈ X := by
    obtain ⟨v, hv⟩ := hXn; obtain ⟨d, hd⟩ := h'.fsurj v; exact ⟨d, by rw [← hd] at hv; exact hv⟩
  have hg : StGood M h I cp X Y := stE_can (P := I) hM h h' hm hcp hX hYn |>.elim
    fun C hC => hC.elim fun T₀ hT => hT.elim fun c' hc' => hc'.elim fun t ⟨ex, ht, hEF⟩ =>
      ⟨C, T₀, c', t, ex, ht, hEF⟩
  obtain ⟨c', t, ex, -, hEF⟩ := hg.choose_spec.choose_spec
  obtain ⟨nF, nV, τv, τf, ts, C₀, cs, hCr, hroot, hLI, -⟩ := hEF
  refine ⟨(stDart_mem h hX).1, (stDart_mem h hYn).1, ?_⟩
  simp only [stChoiceOf, dif_pos hg]
  exact hLI _ _

/-- The step bound of `stCallZ`. -/
def stCostZ (m K : ℕ) : ℕ :=
  costIn m + costE m + costD1 m + hpCost stClrL + 5 * (137 * m + 36) + 5 + 27 * K + 222 * m + 112

set_option maxHeartbeats 6000000 in
/-- **The s-t flow call computes the flow of the machine's choices** (see the module
docstring). -/
theorem stCallZ_exec (hM : M.IsPlane) (hrot : M.RotTrans) (h : EnumOK M en m)
    (h' : EnumOK M.dual en m) (hm : 0 < m) [Nonempty (DTree M)] {cp : D → ℤ}
    (hcp : ∀ d, 0 ≤ cp d) {X Y : Finset V} (hXY : Disjoint X Y) (hXn : ∃ d, M.tail d ∈ X)
    (hYn : ∃ d, M.tail d ∈ Y) (c : Config) (hc : WordsBounded W c)
    {RVb RTb Cb Xb Yb ib Ob Z p Wz : ℕ}
    (r00 : c.nreg 9100 = m) (r01 : c.nreg 9101 = RVb) (r02 : c.nreg 9102 = RTb)
    (r03 : c.nreg 9103 = Cb) (r04 : c.nreg 9104 = Xb) (r05 : c.nreg 9105 = Yb)
    (r07 : c.nreg 9107 = ib) (r08 : c.nreg 9108 = Ob) (r09 : c.nreg 9109 = Z)
    (r10 : c.nreg 9110 = p)
    (hRV : ∀ i < m, c.nmem (RVb + i) = rvI M en m i)
    (hRT : ∀ i < m, c.nmem (RTb + i) = ixOf en m (M.rot (en i)))
    (hC : ∀ i < m, c.nmem (Cb + i) = (cp (en i)).toNat)
    (hX : ∀ i < m, c.nmem (Xb + i) = flagX M en X i)
    (hY : ∀ i < m, c.nmem (Yb + i) = flagX M en Y i)
    (hz : MemZ Wz c)
    (oR : Wz < RVb) (oT : Wz < RTb) (oC : Wz < Cb) (oX : Wz < Xb) (oY : Wz < Yb)
    (wR : RVb + m ≤ W) (wT : RTb + m ≤ W) (wC : Cb + m ≤ W) (wX : Xb + m ≤ W) (wY : Yb + m ≤ W)
    (hWc : stWc M cp X Y m ≤ Wz)
    (hib : pstWN (101 * m + 45) (stHb M cp X Y m) < ib) (hib0 : 339 * m + 128 ≤ ib)
    (hibz : ib + pstWN (101 * m + 45) (stHb M cp X Y m) ≤ Wz)
    (hO : Wz < Ob) (hOp : Ob + m ≤ p)
    (hpW : p + 3 * (4 * pcoreB V F m (4 * m + 1) + 3) ≤ W) (hZW : Z + Wz ≤ W) :
    ∃ c' t, Exec P W stCallZ c c' t ∧ t ≤ stCostZ m (4 * pcoreB V F m (4 * m + 1) + 3) ∧
      MemZ Wz c' ∧
      (∀ i < m, (c'.nmem (Ob + i) : ℤ) = max 0 ((Z : ℤ) + (stChoiceOf h P).flow cp X Y (en i))) ∧
      (∀ a, Wz < a → (a < Ob ∨ Ob + m ≤ a) →
        (a < p ∨ p + 3 * (4 * pcoreB V F m (4 * m + 1) + 3) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ StScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  have hWN : 2 * (101 * m + 45) + 1 + pstM (stHb M cp X Y m) * pstM (stHb M cp X Y m) +
      pstM (stHb M cp X Y m) = pstWN (101 * m + 45) (stHb M cp X Y m) := rfl
  have hWcv : stWc M cp X Y m = pstWN (101 * m + 45) (stHb M cp X Y m) + 339 * m + 128 +
      (4 * m + 5) * m + 2 * m + (∑ d, cp d).toNat + 1 := rfl
  have hWzW : Wz < W := by have := WordsBounded.nreg hc 9108; omega
  obtain ⟨hd₁, hσ₁⟩ := stDart_mem h hXn
  obtain ⟨hd₀, hσ₀⟩ := stDart_mem h hYn
  -- 0. the arrays at the fixed low addresses
  obtain ⟨c₁, t₁, eI, htI, nI, mI, kI, KI, rI, rmI, oI⟩ :=
    stIn_exec (P := P) c hc (arr := stArr M en m cp X Y) r00 r01 r02 r03 r04 r05
      (fun i hi => by rw [hRV i hi]; simp only [stArr]; rw [if_pos hi])
      (fun i hi => by
        rw [hRT i hi]; simp only [stArr]; rw [if_neg (by omega), if_pos (by omega)]
        congr 3; omega)
      (fun i hi => by
        rw [hC i hi]; simp only [stArr]
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; congr 3; omega)
      (fun i hi => by
        rw [hX i hi]; simp only [stArr]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
          show 3 * m + i - 3 * m = i by omega])
      (fun i hi => by
        rw [hY i hi]; simp only [stArr]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          show 4 * m + i - 4 * m = i by omega])
      hz oR oT oC oX oY wR wT wC wX wY (by omega) (by omega) hm
  -- 1. the canonical run and its choices
  have hg : StGood M h P cp X Y := stE_can (P := P) hM h h' hm hcp hXn hYn |>.elim
    fun C hC => hC.elim fun T₀ hT => hT.elim fun c' hc' => hc'.elim fun t ⟨ex, ht, hEF⟩ =>
      ⟨C, T₀, c', t, ex, ht, hEF⟩
  have hflow := stChoiceOf_flow h P hg
  obtain ⟨cE, tE, exE, htE, hEF⟩ := hg.choose_spec.choose_spec
  generalize hg.choose_spec.choose = T₀ at hEF hflow
  generalize hg.choose = C at hEF hflow
  obtain ⟨nF, nV, τv, τf, ts, C₀, cs, hCr, hroot, hLI, hC₀, hoff, hOT, hOC, hLE, e00, e45, e46,
    hKE, hG0E, hG1E, hIV, hIT, hIF, hIC, hH0, hH1, hH2, hH3, bWT, bPH, bCP, bRS, bTH, bH0, bGap,
    lowE, oE⟩ := hEF
  have hcF : Fintype.card F = nF := by rw [Fintype.card_congr τv, Fintype.card_fin]
  have hcV : Fintype.card V = nV := by rw [Fintype.card_congr τf, Fintype.card_fin]
  have hFm : nF ≤ m := hcF ▸ card_F_le h
  have hVm : nV ≤ m := hcV ▸ card_V_le h'
  -- 2. the run of the encoders at the call, by locality
  obtain ⟨cL, exL, LA, LM, LK, LKm, rL, rmL, L, oL1, oL2⟩ := stE_lift (P := P) exE
    (show stWc M cp X Y m ≤ W by omega) c₁ eI.wb_right (fun r hr => nI r hr)
    (fun a ha => mI a (by omega))
  have hL0 : L = [] := by
    have e : (stCan m (stArr M en m cp X Y)).output = [] := rfl
    rw [oE, e] at oL1; simpa using oL1.symm
  have uY : ∀ r, ((9100 ≤ r ∧ r < 9107) ∨ (9111 ≤ r ∧ r < 9200)) → uE r = true := fun r hr => by
    rw [uE_iff]; omega
  have uN : ∀ r, (9107 ≤ r ∧ r ≤ 9110) → uE r = false := fun r hr => by
    cases hu : uE r
    · rfl
    · rw [uE_iff] at hu; omega
  have hL₂ : StL cL.nreg m (207 * m + 92) :=
    hLE.frame (fun r h1 h2 => LA r (uY r (by omega)))
  have q : ∀ r, 9107 ≤ r → r ≤ 9110 → cL.nreg r = c.nreg r := fun r h1 h2 => by
    rw [LK r (uN r ⟨h1, h2⟩), kI r (uN r ⟨h1, h2⟩)]
  have q00 : cL.nreg 9100 = m := (LA _ (uY _ (by omega))).trans e00
  have hw : IsIsoW M (M.tail (stDart M en m Y)) (MSSP.treeW C) := by
    rw [← hCr]; exact isIsoW_treeW C
  have hHb' := stH_le hM hw (capR_nonneg (M := M) hcp X Y) (4 * m + 1)
  have hHn := pcoreH_ge (V := V) (F := F) (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
    (capR M cp X Y) (isoEpsG V F (MSSP.treeW C))
  have q45 : cL.nreg 9145 = pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
      (capR M cp X Y) (isoEpsG V F (MSSP.treeW C)) := (LA _ (uY _ (by omega))).trans e45
  have q46 := (LA 9146 (uY _ (by omega))).trans e46
  generalize hHdef : pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
    (capR M cp X Y) (isoEpsG V F (MSSP.treeW C)) = H at q45 q46 bWT bPH bCP bRS bTH bH0 hHb' hHn
  have hHb2 : H ≤ stHb M cp X Y m := hHb'
  have hMo : pstM H ≤ pstM (stHb M cp X Y m) := by unfold pstM; omega
  have hWNH : pstWN (101 * m + 45) H ≤ pstWN (101 * m + 45) (stHb M cp X Y m) :=
    pstWN_mono hHb2
  have hMoWN : pstM H ≤ pstWN (101 * m + 45) H := by unfold pstWN; omega
  -- 3. the image at `ib`, the parameters
  have hVz := wz_bound (ib := ib) (show 4 * m + 2 ≤ H by omega)
  obtain ⟨cD, tD1, eD1, htD1, z1, zv, z50, z51, hcl, mD1, kD1, rD1, rmD1, oD1⟩ :=
    stD1_exec (P := P) cL exL.wb_right hL₂ q00 ((q _ (by omega) (by omega)).trans r07)
      ((q _ (by omega) (by omega)).trans r10) q45 q46
      (Or.inr (by omega)) (by rw [show stSz m = 132 * m + 36 from rfl]; omega) (by omega)
  -- 4. the arrays and the scratch zeroed
  obtain ⟨cK, tK, eK, htK, ZK, MK, RK, rK, rmK, oK⟩ := stClr_exec (P := P) cD eD1.wb_right
    (by rw [kD1 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact q00)
    (by omega) hm
  have hts : ts.length ≤ m := by have := hOT.ylen; rw [hcF] at this; exact this.trans hFm
  have hcs : cs.length ≤ m := by have := hOC.ylen; rw [hcV] at this; exact this.trans hVm
  have hKi := img_ib h τv τf hFm hVm hts hcs (d₀ := stDart M en m Y)
    (d₁ := stDart M en m X) (mem := cL.nmem) (mem' := cK.nmem) (Sb := 207 * m + 92) (ib := ib)
    (hKE.move (E := 4 * m + 1) (ιE_lt h) (fun i hi => LM _ (by omega)))
    (by rw [LM _ (by omega)]; exact hG0E) (by rw [LM _ (by omega)]; exact hG1E)
    (fun i hi => by
      have : i < m := by simp at hi; omega
      rw [LM _ (by omega)]; exact hIV i hi)
    (fun i hi => by
      have := hOT.ylen; rw [hcF] at this
      rw [LM _ (by omega)]; exact hIT i hi)
    (fun i hi => by
      have : i < m := by simp at hi; omega
      rw [LM _ (by omega)]; exact hIF i hi)
    (fun i hi => by
      have := hOC.ylen; rw [hcV] at this
      rw [LM _ (by omega)]; exact hIC i hi)
    (by rw [LM _ (by omega)]; exact hH0) (by rw [LM _ (by omega)]; exact hH1)
    (by rw [LM _ (by omega)]; exact hH2) (by rw [LM _ (by omega)]; exact hH3)
    (fun i hi => by rw [MK _ (by omega)]; exact hcl i hi)
  obtain ⟨iK, iG0, iG1, iIV, iIT, iIF, iIC, iH0, iH1, iH2, iH3, ibd⟩ := hKi
  -- the low memory of the run
  have mlow : ∀ a, a < 202 * m + 92 → cK.nmem a = cL.nmem a := fun a ha => by
    rw [MK a (Or.inl ha), mD1 a (Or.inl (by omega))]
  have low5 : ∀ a, a ≤ Wz → (a < 101 * m + 46 ∨ 106 * m + 49 ≤ a) →
      (a < ib ∨ ib + (37 * m + 13) ≤ a) → cK.nmem a = 0 := fun a h1 h2 h3 => by
    by_cases hs : 202 * m + 92 ≤ a ∧ a < 339 * m + 128
    · have := ZK (a - (202 * m + 92)) (by omega)
      rwa [show 202 * m + 92 + (a - (202 * m + 92)) = a by omega] at this
    · rw [MK a (by omega), mD1 a h3]
      by_cases hc' : a ≤ stWc M cp X Y m
      · rw [LM a hc', lowE a h2 (by omega)]
      · rw [LKm a (by omega), mI a h1, stCan_zero m _ (by omega)]
  have res5 : ∀ a < 5 * m + 3, cK.nmem (101 * m + 46 + a) < pstM H := by
    have := res_lt h (mem := cK.nmem) (Mo := pstM H) (by unfold pstM; omega)
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aWT; omega),
          LM _ (by have := (enEq h e).2; unfold aWT; omega)]; exact bWT e)
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aPH; omega),
          LM _ (by have := (enEq h e).2; unfold aPH; omega)]; exact bPH e)
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aCP; omega),
          LM _ (by have := (enEq h e).2; unfold aCP; omega)]; exact bCP e)
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aRS; omega),
          LM _ (by have := (enEq h e).2; unfold aRS; omega)]; exact bRS e)
      (by rw [mlow _ (by unfold aTH; omega), LM _ (by unfold aTH; omega)]; exact bTH)
      (by rw [mlow _ (by unfold aH0; omega), LM _ (by unfold aH0; omega)]; exact bH0)
      (fun i hi => by rw [mlow _ (by omega), LM _ (by omega)]; exact bGap i hi)
    exact this
  have res5' : ∀ a ≤ 101 * m + 45, cK.nmem (101 * m + 46 + a) < pstM H := fun a ha => by
    by_cases h1 : a < 5 * m + 3
    · exact res5 a h1
    · rw [low5 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))]; unfold pstM; omega
  have kK : ∀ r, (r < 5030 ∨ 5035 < r) → r ≠ 9198 → r ≠ 9199 → cK.nreg r = cD.nreg r := RK
  -- 5. the logged run
  obtain ⟨c₆, tD2, j, eD2, htD2, hj, hOUT, hLK, hb6, rD2, rmD2, oD2⟩ :=
    stD2_exec (P := P) hM hrot h h' hm hcp hXY hd₁ hd₀ hCr hroot (hLI _ _) τv τf hOT hOC hoff hC₀
      cK eK.wb_right (ib := ib) (p := p) (Wz := Wz) (H := H) hHdef.symm
      (fun r hr => by rw [kK r (by omega) (by omega) (by omega)]; exact z1 r hr)
      (fun j hj => by rw [kK _ (by omega) (by omega) (by omega)]; exact zv j hj)
      (by rw [kK _ (by omega) (by omega) (by omega)]; exact z50)
      (by rw [kK _ (by omega) (by omega) (by omega)]; exact z51)
      iK iG0 iG1 iIV iIT iIF iIC iH0 iH1 iH2 iH3 ibd
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aWT; omega),
          LM _ (by have := (enEq h e).2; unfold aWT; omega)]; exact bWT e)
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aPH; omega),
          LM _ (by have := (enEq h e).2; unfold aPH; omega)]; exact bPH e)
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aCP; omega),
          LM _ (by have := (enEq h e).2; unfold aCP; omega)]; exact bCP e)
      (fun e => by
        rw [mlow _ (by have := (enEq h e).2; unfold aRS; omega),
          LM _ (by have := (enEq h e).2; unfold aRS; omega)]; exact bRS e)
      (by rw [mlow _ (by unfold aTH; omega), LM _ (by unfold aTH; omega)]; exact bTH)
      (by rw [mlow _ (by unfold aH0; omega), LM _ (by unfold aH0; omega)]; exact bH0)
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
  have g6 : ∀ r, 9100 ≤ r → r < 9198 → (r < 9120 ∨ 9128 < r) → r ≠ 9150 → r ≠ 9151 →
      c₆.nreg r = cL.nreg r := fun r h1 h2 h3 h4 h5 => by
    rw [hLK.nreg r (by simp; omega) h4, kK r (by omega) (by omega) (by omega),
      kD1 r (by omega) (by omega) h3 h4 h5]
  have hL₆ : StL c₆.nreg m (207 * m + 92) :=
    hL₂.frame (fun r h1 h2 => g6 r (by omega) (by omega) (by omega) (by omega) (by omega))
  have q6 : ∀ r, 9107 ≤ r → r ≤ 9110 → c₆.nreg r = c.nreg r := fun r h1 h2 => by
    rw [g6 r (by omega) (by omega) (by omega) (by omega) (by omega), q r h1 h2]
  obtain ⟨c₇, tD3, eD3, htD3, O7, Z7, K7, R7, rD3, rmD3, oD3⟩ :=
    stD3_exec (P := P) c₆ eD2.wb_right (j := j) (Wz := Wz) hL₆
      ((g6 _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans q00)
      ((q6 _ (by omega) (by omega)).trans r07)
      ((q6 _ (by omega) (by omega)).trans r08) ((q6 _ (by omega) (by omega)).trans r09)
      ((q6 _ (by omega) (by omega)).trans r10)
      ((g6 _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans q45)
      ((g6 _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans q46) hLK.lp
      hLK.logle (by omega) hO hOp
      (fun i hi => by have := hb6 (107 * m + 49 + i) (by omega); omega) (by omega) (by omega)
      (by omega)
  refine ⟨c₇, _, eI.seq (exL.seq (eD1.seq (eK.seq (eD2.seq eD3)))), ?_, fun a ha => ?_,
    fun i hi => ?_, fun a h1 h3 h4 => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have h3 := htD3
    unfold costD3 at h3
    unfold stCostZ
    omega
  · by_cases hl : (∃ i < j, c₆.nmem (p + i) = a) ∨ (101 * m + 46 ≤ a ∧ a < 106 * m + 49) ∨
        (ib ≤ a ∧ a < ib + (37 * m + 13))
    · exact Z7 a hl
    · simp only [not_or, not_exists, not_and, not_le, not_lt] at hl
      obtain ⟨hl1, hl2, hl3⟩ := hl
      rw [K7 a (fun i hi e => hl1 i hi e) (by omega) (by omega) (Or.inl (by omega)),
        hLK.dirty a ha (fun i hi e => hl1 i hi e),
        low5 a ha (by omega) (by omega)]
  · rw [O7 i hi, rdv_eq, hOUT i hi, hflow]
  · have hnl : ∀ i < j, c₆.nmem (p + i) ≠ a := fun i hi e => by
      have := hLK.logle i hi; omega
    rw [K7 a hnl (by omega) (by omega) h3, hLK.nmem a h1 (by omega), MK a (by omega),
      mD1 a (by omega), LKm a (by omega), KI a h1]
  · have hu : uE r = false := by
      cases hu : uE r
      · rfl
      · rw [uE_iff] at hu; unfold StScr EncScr at hr; omega
    unfold StScr EncScr at hr
    rw [R7 r (by omega) (by omega) (by omega), hLK.nreg r (by simp; omega) (by omega),
      kK r (by omega) (by omega) (by omega),
      kD1 r (by omega) (by omega) (by omega) (by omega) (by omega), LK r hu, kI r hu]
  · rw [rD3, rD2, rK, rD1, rL, rI]
  · rw [rmD3, rmD2, rmK, rmD1, rmL, rmI]
  · rw [oD3, oD2, oK, oD1, oL2, hL0, List.append_nil, oI]

end StCall

end BKMNW

end PlanarFlow
