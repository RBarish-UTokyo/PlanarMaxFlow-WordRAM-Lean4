module

public import PlanarFlow.BKMNW.StCallZA
public import WordRAM.Machine.Iter

/-!
# The canonical run of the encoders and its locality

* `stArr M en m c X Y` (the five frame arrays as one word function), `stDart` (the dart of greatest
  index whose tail is in a set), `stWc` (the word bound of the canonical run);
* `EncFacts h c X Y c' C T₀`: the words of `c'` are those the encoders write for the trees `C`
  (isolating weight) and `T₀` (initial dual tree) — the map words, the terminal darts, the `KInit`
  words, the residues, `H`, `Mo`, the layout, the rest of the low memory zero — and `C`, `T₀` are
  rooted at the sink dart and meet `LInv`;
* **`stE_can`**: the canonical run of the encoders from `stCan m (stArr …)` with the word bound
  `stWc` exists and ends in a configuration meeting `EncFacts` for some `C`, `T₀`;
* **`stE_lift`** (the locality lemma): any run of the encoders from `stCan` lifts to a run from any
  configuration agreeing with `stCan` on the registers `uE` and the memory `≤ Wc` (the reals are
  irrelevant: natural words only), ending in a configuration agreeing with the canonical end on
  `uE` and the memory `≤ Wc`, all other registers and the memory above `Wc` kept.
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
/-- The five frame arrays as one word function. -/
noncomputable def stArr (en : ℕ → D) (m : ℕ) (cp : D → ℤ) (X Y : Finset V) (k : ℕ) : ℕ :=
  if k < m then rvI M en m k
  else if k < 2 * m then ixOf en m (M.rot (en (k - m)))
  else if k < 3 * m then (cp (en (k - 2 * m))).toNat
  else if k < 4 * m then flagX M en X (k - 3 * m)
  else flagX M en Y (k - 4 * m)

variable (M) in
/-- The dart of greatest index whose tail is in `X`. -/
def stDart (en : ℕ → D) (m : ℕ) (X : Finset V) : D := en (StEnc.lastF (flagX M en X) m 0)

variable (M) in
/-- The word bound of the canonical run. -/
noncomputable def stWc (cp : D → ℤ) (X Y : Finset V) (m : ℕ) : ℕ :=
  pstWN (101 * m + 45) (stHb M cp X Y m) + 339 * m + 128 + (4 * m + 5) * m + 2 * m +
    (∑ d, cp d).toNat + 1

/-- **The words the encoders write**, for the trees `C` and `T₀` (see the module docstring). -/
def EncFacts (h : EnumOK M en m) (cp : D → ℤ) (X Y : Finset V) (c' : Config)
    (C : DTree M.dual) (T₀ : DTree M) : Prop :=
  ∃ (nF nV : ℕ) (τv : F ≃ Fin nF) (τf : V ≃ Fin nV) (ts : List F) (C₀ : DTree M.dual)
    (cs : List V),
    C.root = M.tail (stDart M en m Y) ∧ T₀.root = M.face (stDart M en m Y) ∧
    (∀ s t', LInv (capR M cp X Y) (isoEpsG V F (MSSP.treeW C)) s t'
      (tSt M (capR M cp X Y) (isoEpsG V F (MSSP.treeW C)) T₀)) ∧
    C₀.root = M.tail (stDart M en m X) ∧ (∀ x, x ≠ C₀.root → ¬ (toDD T₀).InT (C₀.par x)) ∧
    Klein.Orders (toDD T₀) ((List.finRange nF).map τv.symm) ts ∧
    Klein.Orders C₀ ((List.finRange nV).map τf.symm) cs ∧
    StL c'.nreg m (207 * m + 92) ∧ c'.nreg 9100 = m ∧
    c'.nreg 9145 = pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
      (capR M cp X Y) (isoEpsG V F (MSSP.treeW C)) ∧
    c'.nreg 9146 = pstM (pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
      (capR M cp X Y) (isoEpsG V F (MSSP.treeW C))) ∧
    KInM M.dual (enEq h) (fun x => 1 + (τv x : ℕ)) (ιG M h) (fun y => 2 * m + 1 + (τf y : ℕ))
      (ιE M h) c'.nmem (207 * m + 92 + 3 * m) ∧
    c'.nmem (207 * m + 92 + 15 * m + 1) = enEq h (stDart M en m X) ∧
    c'.nmem (207 * m + 92 + 15 * m + 2) = enEq h (stDart M en m Y) ∧
    (∀ i (hi : i < ((List.finRange nF).map τv.symm).length),
      c'.nmem (207 * m + 92 + 24 * m + 5 + i) = 1 + τv ((List.finRange nF).map τv.symm)[i]) ∧
    (∀ i (hi : i < ts.length),
      c'.nmem (207 * m + 92 + 24 * m + 5 + (4 * m + 1) + i) = enEq h (T₀.par ts[i])) ∧
    (∀ i (hi : i < ((List.finRange nV).map τf.symm).length),
      c'.nmem (207 * m + 92 + 24 * m + 5 + 2 * (4 * m + 1) + i) =
        2 * m + 1 + τf ((List.finRange nV).map τf.symm)[i]) ∧
    (∀ i (hi : i < cs.length),
      c'.nmem (207 * m + 92 + 24 * m + 5 + 3 * (4 * m + 1) + i) = enEq h (C₀.par cs[i])) ∧
    c'.nmem (207 * m + 92 + 24 * m + 5 + 4 * (4 * m + 1)) =
      ((List.finRange nF).map τv.symm).length ∧
    c'.nmem (207 * m + 92 + 24 * m + 5 + 4 * (4 * m + 1) + 1) = ts.length ∧
    c'.nmem (207 * m + 92 + 24 * m + 5 + 4 * (4 * m + 1) + 2) =
      ((List.finRange nV).map τf.symm).length ∧
    c'.nmem (207 * m + 92 + 24 * m + 5 + 4 * (4 * m + 1) + 3) = cs.length ∧
    (∀ e, c'.nmem (101 * m + 46 + (aWT + enEq h e)) =
      zres (pstM (pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
        (capR M cp X Y) (isoEpsG V F (MSSP.treeW C))))
        (STFlow.wlen (stN (V := V) (F := F) (MSSP.treeW C)) (capR M cp X Y)
          (isoEpsG V F (MSSP.treeW C)) e)) ∧
    (∀ e, c'.nmem (101 * m + 46 + (aPH m + enEq h e)) =
      zres (pstM (pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
        (capR M cp X Y) (isoEpsG V F (MSSP.treeW C))))
        (STFlow.wlen (stN (V := V) (F := F) (MSSP.treeW C)) (capR M cp X Y)
          (isoEpsG V F (MSSP.treeW C)) e)) ∧
    (∀ e, c'.nmem (101 * m + 46 + (aCP m + enEq h e)) =
      zres (pstM (pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
        (capR M cp X Y) (isoEpsG V F (MSSP.treeW C)))) (capR M cp X Y e)) ∧
    (∀ e, c'.nmem (101 * m + 46 + (aRS m + enEq h e)) =
      zres (pstM (pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
        (capR M cp X Y) (isoEpsG V F (MSSP.treeW C)))) (rsIn M X Y e)) ∧
    c'.nmem (101 * m + 46 + aTH m) =
      zres (pstM (pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
        (capR M cp X Y) (isoEpsG V F (MSSP.treeW C))))
        (STFlow.kTh D F (stN (V := V) (F := F) (MSSP.treeW C)) (capR M cp X Y)
          (isoEpsG V F (MSSP.treeW C))) ∧
    c'.nmem (101 * m + 46 + aH0 m) =
      zres (pstM (pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
        (capR M cp X Y) (isoEpsG V F (MSSP.treeW C))))
        (STFlow.kH0 D F (stN (V := V) (F := F) (MSSP.treeW C)) (capR M cp X Y)
          (isoEpsG V F (MSSP.treeW C))) ∧
    (∀ i < m + 1, c'.nmem (103 * m + 46 + i) = 0) ∧
    (∀ a, (a < 101 * m + 46 ∨ 106 * m + 49 ≤ a) → (a < 202 * m + 92 ∨ 339 * m + 128 ≤ a) →
      c'.nmem a = 0) ∧
    c'.output = []

/-- The cost of the encoders. -/
def costE (m : ℕ) : ℕ := hpCost stLayL + costA m + costB m + costC m

lemma stCan_nreg (m : ℕ) (arr : ℕ → ℕ) :
    (stCan m arr).nreg 9100 = m ∧ (stCan m arr).nreg 9101 = 202 * m + 92 ∧
    (stCan m arr).nreg 9102 = 203 * m + 92 ∧ (stCan m arr).nreg 9103 = 204 * m + 92 ∧
    (stCan m arr).nreg 9104 = 205 * m + 92 ∧ (stCan m arr).nreg 9105 = 206 * m + 92 ∧
    (stCan m arr).nreg 9106 = 207 * m + 92 := by
  simp [stCan]

lemma stCan_arr (m : ℕ) (arr : ℕ → ℕ) {k : ℕ} (hk : k < 5 * m) :
    (stCan m arr).nmem (202 * m + 92 + k) = arr k := by
  simp only [stCan]
  rw [ite_cond_eq_true _ _ (eq_true (by omega))]; congr 1; omega

lemma stCan_zero (m : ℕ) (arr : ℕ → ℕ) {a : ℕ} (ha : a < 202 * m + 92 ∨ 207 * m + 92 ≤ a) :
    (stCan m arr).nmem a = 0 := by
  simp only [stCan]
  rw [ite_cond_eq_false _ _ (eq_false (by omega))]

set_option maxHeartbeats 4000000 in
/-- **The canonical run of the encoders** (see the module docstring). -/
theorem stE_can (hM : M.IsPlane) (h : EnumOK M en m) (h' : EnumOK M.dual en m) (hm : 0 < m)
    {cp : D → ℤ} (hcp : ∀ d, 0 ≤ cp d) {X Y : Finset V}
    (hXn : ∃ d, M.tail d ∈ X) (hYn : ∃ d, M.tail d ∈ Y) :
    ∃ (C : DTree M.dual) (T₀ : DTree M) (c' : Config) (t : ℕ),
      Exec P (stWc M cp X Y m) stE (stCan m (stArr M en m cp X Y)) c' t ∧ t ≤ costE m ∧
      EncFacts h cp X Y c' C T₀ := by
  set Wc := stWc M cp X Y m with hWcd
  set arr := stArr M en m cp X Y with harr
  set c := stCan m arr with hcd
  obtain ⟨r00, r01, r02, r03, r04, r05, r06⟩ := stCan_nreg m arr
  have hSnn : 0 ≤ ∑ d, cp d := Finset.sum_nonneg fun d _ => hcp d
  have hWN : 2 * (101 * m + 45) + 1 + pstM (stHb M cp X Y m) * pstM (stHb M cp X Y m) +
      pstM (stHb M cp X Y m) = pstWN (101 * m + 45) (stHb M cp X Y m) := rfl
  have hWcv : Wc = pstWN (101 * m + 45) (stHb M cp X Y m) + 339 * m + 128 + (4 * m + 5) * m +
      2 * m + (∑ d, cp d).toNat + 1 := rfl
  have hScp : (∑ d, cp d) = ((∑ d, cp d).toNat : ℤ) := (Int.toNat_of_nonneg hSnn).symm
  have hcpl : ∀ d, (cp d).toNat ≤ (∑ d, cp d).toNat := fun d => by
    have := Finset.single_le_sum (f := cp) (fun d _ => hcp d) (Finset.mem_univ d)
    omega
  -- the canonical configuration is bounded
  have hc : WordsBounded Wc c := by
    refine ⟨fun r => ?_, fun a => ?_⟩
    · simp only [hcd, stCan]; split_ifs <;> omega
    · simp only [hcd, stCan]
      split_ifs with ha
      · simp only [harr, stArr]
        split_ifs
        · have := rvI_lt h (a - (202 * m + 92)); omega
        · have := ixOf_lt h (M.rot (en (a - (202 * m + 92) - m))); omega
        · have := hcpl (en (a - (202 * m + 92) - 2 * m)); omega
        · simp only [flagX]; split_ifs <;> omega
        · simp only [flagX]; split_ifs <;> omega
      · omega
  have aK : ∀ k < 5 * m, c.nmem (202 * m + 92 + k) = arr k := fun k hk => stCan_arr m arr hk
  have hXT : ∀ d, flagX M en X (enEq h d) = if M.tail d ∈ X then 1 else 0 := fun d => by
    simp only [flagX, enEq_val, en_ixOf h]
  have hYT : ∀ d, flagX M en Y (enEq h d) = if M.tail d ∈ Y then 1 else 0 := fun d => by
    simp only [flagX, enEq_val, en_ixOf h]
  obtain ⟨d₁, hd₁, hσ₁⟩ := lastF_map (enEq h) hXT hXn
  obtain ⟨d₀, hd₀, hσ₀⟩ := lastF_map (enEq h) hYT hYn
  have e₁d : stDart M en m X = d₁ := by
    unfold stDart; rw [← hσ₁]; exact en_ixOf h d₁
  have e₀d : stDart M en m Y = d₀ := by
    unfold stDart; rw [← hσ₀]; exact en_ixOf h d₀
  unfold EncFacts
  rw [e₁d, e₀d]
  -- 0. the layout
  obtain ⟨c₁, eP, hL₁, kP, mP, rP, rmP, oP⟩ := stPro_exec (P := P) c hc r00 r06 (by omega)
    (by omega)
  have g1 : ∀ r, 9100 ≤ r → r ≤ 9110 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    kP r (by omega) (by omega) (by omega)
  -- 1. the map stage
  obtain ⟨c₂, tA, eA, htA, nF, nV, τv, τf, a83, a84, hK₂, hG0₂, hG1₂, mA, kA, rA, rmA, oA⟩ :=
    stA_exec (P := P) h h' hm c₁ eP.wb_right (Sb := 207 * m + 92) (RVb := 202 * m + 92)
      (RTb := 203 * m + 92) (Xb := 205 * m + 92) (Yb := 206 * m + 92) (XT := flagX M en X)
      (YT := flagX M en Y) hL₁
      ((g1 _ (by omega) (by omega)).trans r00) ((g1 _ (by omega) (by omega)).trans r01)
      ((g1 _ (by omega) (by omega)).trans r02) ((g1 _ (by omega) (by omega)).trans r04)
      ((g1 _ (by omega) (by omega)).trans r05) ((g1 _ (by omega) (by omega)).trans r06)
      (fun i hi => by rw [mP, aK i (by omega)]; simp only [harr, stArr]; rw [if_pos hi])
      (fun i hi => by
        rw [mP, show 203 * m + 92 + i = 202 * m + 92 + (m + i) by omega, aK _ (by omega)]
        simp only [harr, stArr]; rw [if_neg (by omega), if_pos (by omega)]; congr 3; omega)
      (fun i hi => by
        rw [mP, show 205 * m + 92 + i = 202 * m + 92 + (3 * m + i) by omega, aK _ (by omega)]
        simp only [harr, stArr]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        congr 1; omega)
      (fun i hi => by
        rw [mP, show 206 * m + 92 + i = 202 * m + 92 + (4 * m + i) by omega, aK _ (by omega)]
        simp only [harr, stArr]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        congr 1; omega)
      (by omega) (by omega) (by omega) (by omega) (by rw [show stSz m = 132 * m + 36 from rfl]; omega)
  have hcF : Fintype.card F = nF := by rw [Fintype.card_congr τv, Fintype.card_fin]
  have hcV : Fintype.card V = nV := by rw [Fintype.card_congr τf, Fintype.card_fin]
  have g2 : ∀ r, 9100 ≤ r → r ≤ 9182 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    kA r (by unfold EncScr; omega) (by omega) (by omega)
  have hL₂ : StL c₂.nreg m (207 * m + 92) := hL₁.frame (fun r h1 h2 => g2 r (by omega) h2)
  -- 2. the weight stage
  obtain ⟨c₃, tB, eB, htB, C, hCr, b45, b46, bWT, bPH, bCP, bRS, bTH, bH0, bGap, mB, kB, rB,
      rmB, oB⟩ :=
    stB_exec (P := P) hM h h' hm hcp (X := X) (Y := Y) (d₀ := d₀) c₂ eA.wb_right
      (Sb := 207 * m + 92) (Cb := 204 * m + 92) (Xb := 205 * m + 92) (Yb := 206 * m + 92) τv τf
      hL₂
      ((g2 _ (by omega) (by omega)).trans ((g1 _ (by omega) (by omega)).trans r00))
      ((g2 _ (by omega) (by omega)).trans ((g1 _ (by omega) (by omega)).trans r03))
      ((g2 _ (by omega) (by omega)).trans ((g1 _ (by omega) (by omega)).trans r04))
      ((g2 _ (by omega) (by omega)).trans ((g1 _ (by omega) (by omega)).trans r05)) a83 a84 hK₂
      (by rw [hG1₂, hσ₀])
      (fun i hi => by
        rw [mA _ (Or.inl (by omega)), mP,
          show 204 * m + 92 + i = 202 * m + 92 + (2 * m + i) by omega, aK _ (by omega)]
        simp only [harr, stArr]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        congr 3; omega)
      (fun i hi => by
        rw [mA _ (Or.inl (by omega)), mP,
          show 205 * m + 92 + i = 202 * m + 92 + (3 * m + i) by omega, aK _ (by omega)]
        simp only [harr, stArr]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
          show 3 * m + i - 3 * m = i by omega]
        rfl)
      (fun i hi => by
        rw [mA _ (Or.inl (by omega)), mP,
          show 206 * m + 92 + i = 202 * m + 92 + (4 * m + i) by omega, aK _ (by omega)]
        simp only [harr, stArr]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          show 4 * m + i - 4 * m = i by omega]
        rfl)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [show stSz m = 132 * m + 36 from rfl]; omega) (by omega) (by omega) (by omega)
  have hw : IsIsoW M (M.tail d₀) (MSSP.treeW C) := by rw [← hCr]; exact isIsoW_treeW C
  have g3 : ∀ r, 9100 ≤ r → r ≤ 9184 → r ≠ 9145 → r ≠ 9146 → c₃.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 h4 => kB r (by unfold EncScr; omega) h3 h4
  have hL₃ : StL c₃.nreg m (207 * m + 92) :=
    hL₂.frame (fun r h1 h2 => g3 r (by omega) (by omega) (by omega) (by omega))
  have hK₃ : KInM M.dual (enEq h) (fun x => 1 + (τv x : ℕ)) (ιG M h)
      (fun y => 2 * m + 1 + (τf y : ℕ)) (ιE M h) c₃.nmem (207 * m + 92 + 3 * m) :=
    hK₂.move (E := 4 * m + 1) (ιE_lt h) (fun i hi => mB _ (Or.inl (by omega)) (Or.inr (by omega)))
  -- 3. the tree stage
  obtain ⟨c₄, tC, eC, htC, T₀, ts, C₀, cs, hroot, hLI, hC₀, hoff, hOT, hOC, hIV, hIT, hIF, hIC,
      hH0, hH1, hH2, hH3, mC, kC, rC, rmC, oC⟩ :=
    stC_exec (P := P) hM h h' hm hcp X Y (d₀ := d₀) (d₁ := d₁) hw c₃ eB.wb_right τv τf hL₃
      ((g3 _ (by omega) (by omega) (by omega) (by omega)).trans ((g2 _ (by omega) (by omega)).trans
        ((g1 _ (by omega) (by omega)).trans r00)))
      ((g3 _ (by omega) (by omega) (by omega) (by omega)).trans a83)
      ((g3 _ (by omega) (by omega) (by omega) (by omega)).trans a84) b46 hK₃
      (by rw [mB _ (Or.inl (by omega)) (Or.inr (by omega)), hG0₂, hσ₁])
      (by rw [mB _ (Or.inl (by omega)) (Or.inr (by omega)), hG1₂, hσ₀]) bWT
      (by omega) (by rw [show stSz m = 132 * m + 36 from rfl]; omega) (by omega)
  have g4 : ∀ r, 9100 ≤ r → r < 9200 → c₄.nreg r = c₃.nreg r := fun r h1 h2 =>
    kC r (by unfold EncScr; omega)
  have resC : ∀ a, 101 * m + 46 ≤ a → a < 106 * m + 49 → c₄.nmem a = c₃.nmem a :=
    fun a h1 h2 => mC a (Or.inl (by omega)) (Or.inl (by omega))
  refine ⟨C, T₀, c₄, _, eP.seq (eA.seq (eB.seq eC)), by unfold costE; omega,
    nF, nV, τv, τf, ts, C₀, cs, hCr, hroot, hLI, hC₀, hoff, hOT, hOC,
    hL₃.frame (fun r h1 h2 => g4 r (by omega) (by omega)),
    (g4 _ (by omega) (by omega)).trans ((g3 _ (by omega) (by omega) (by omega) (by omega)).trans
      ((g2 _ (by omega) (by omega)).trans ((g1 _ (by omega) (by omega)).trans r00))),
    (g4 _ (by omega) (by omega)).trans b45, (g4 _ (by omega) (by omega)).trans b46,
    hK₃.move (E := 4 * m + 1) (ιE_lt h)
      (fun i hi => mC _ (Or.inl (by omega)) (Or.inl (by omega))),
    by rw [mC _ (Or.inl (by omega)) (Or.inl (by omega)),
      mB _ (Or.inl (by omega)) (Or.inr (by omega)), hG0₂, hσ₁],
    by rw [mC _ (Or.inl (by omega)) (Or.inl (by omega)),
      mB _ (Or.inl (by omega)) (Or.inr (by omega)), hG1₂, hσ₀],
    hIV, hIT, hIF, hIC, hH0, hH1, hH2, hH3,
    fun e => by
      rw [resC _ (by omega) (by have := (enEq h e).2; unfold aWT; omega)]; exact bWT e,
    fun e => by
      rw [resC _ (by omega) (by have := (enEq h e).2; unfold aPH; omega)]; exact bPH e,
    fun e => by
      rw [resC _ (by omega) (by have := (enEq h e).2; unfold aCP; omega)]; exact bCP e,
    fun e => by
      rw [resC _ (by omega) (by have := (enEq h e).2; unfold aRS; omega)]; exact bRS e,
    by rw [resC _ (by omega) (by unfold aTH; omega)]; exact bTH,
    by rw [resC _ (by omega) (by unfold aH0; omega)]; exact bH0,
    fun i hi => by rw [resC _ (by omega) (by omega)]; exact bGap i hi,
    fun a h1 h2 => ?_, by rw [oC, oB, oA, oP]; rfl⟩
  rw [mC a (by omega) (by omega), mB a (by omega) h1, mA a (by omega), mP,
    stCan_zero m arr (by omega)]

/-- **The locality of the encoders**: a run from the canonical configuration lifts to every
configuration agreeing with it on the registers `uE` and the memory `≤ Wc`. -/
theorem stE_lift {Wc : ℕ} {c₀ c₀' : Config} {t : ℕ} (ex : Exec P Wc stE c₀ c₀' t)
    (hWc : Wc ≤ W) (c : Config) (hc : WordsBounded W c)
    (hA : ∀ r, uE r = true → c.nreg r = c₀.nreg r) (hm : ∀ a ≤ Wc, c.nmem a = c₀.nmem a) :
    ∃ c', Exec P W stE c c' t ∧ (∀ r, uE r = true → c'.nreg r = c₀'.nreg r) ∧
      (∀ a ≤ Wc, c'.nmem a = c₀'.nmem a) ∧ (∀ r, uE r = false → c'.nreg r = c.nreg r) ∧
      (∀ a, Wc < a → c'.nmem a = c.nmem a) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      ∃ L, c₀'.output = c₀.output ++ L ∧ c'.output = c.output ++ L := by
  have ex' := Exec.mbReals ex (mbNatS_of_natOnly _ stE_natOnly) c.rreg c.rmem
  have hAg : Agree uE Wc (setR c₀ c.rreg c.rmem) c :=
    ⟨fun r hr => hA r hr, fun r _ => rfl, fun a ha => hm a ha, fun a _ => rfl⟩
  obtain ⟨c', ex'', hA', hK, L, o1, o2⟩ := Exec.liftSame ex' stE_regsOK stE_noRand hWc hAg hc
  refine ⟨c', ex'', fun r hr => hA'.nreg r hr, fun a ha => hA'.nmem a ha, fun r hr => hK.nreg r hr,
    fun a ha => hK.nmem a ha, ?_, ?_, L, by simpa using o1, o2⟩
  · funext r
    cases hr : uE r
    · exact hK.rreg r hr
    · exact hA'.rreg r hr
  · funext a
    by_cases ha : a ≤ Wc
    · exact hA'.rmem a ha
    · exact hK.rmem a (by omega)

end StCall

end BKMNW

end PlanarFlow
