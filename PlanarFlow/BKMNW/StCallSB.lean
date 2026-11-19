module

public import PlanarFlow.BKMNW.StCallSA

/-!
# The weight stage of the s-t flow call

**`stB_exec`**: after the map stage (compact `KInM` at `IMb = Sb + 3m`, `σ d₀` at
`Gb + 1 = Sb + 15m + 2`), from the capacities `(c (en i)).toNat` and the flags of `X`, `Y` in
the frame, the weight stage computes (within `costB m = 360 m + 300` steps) a tree
`C : DTree M.dual` rooted at `tail d₀` (the isolating weight `w = treeW C`), the residue words
of `STFlow.st_sNFM` at `β₀ = 101 m + 46` (`WT`, `PH`, `CP`, `RS`, `kTh`, `kH0` of
`wlen (stN w) (capR c X Y) (isoEpsG w)`), the words `[β₀ + 2m, β₀ + 3m + 1)` zero, and
`H = pcoreH …`, `Mo = pstM H` in `r9145`, `r9146`; the memory changes only in the scratch
`[Sb + 41 m + 15, Sb + 64 m + 21)` and in `[β₀, β₀ + 5m + 3)`.

`stHb M c X Y m` is the bound `pstH (4m + 1) #D #F #V (isoW_bound (capR c X Y))` of `H`
(`STFlow.stH_le`), independent of the weight.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace StCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP StEnc
  NsStep STFlow CombMap

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

variable {P : Input} {W : ℕ}

variable (M) in
/-- **The bound of `H`** at a call, independent of the isolating weight. -/
noncomputable def stHb (c : D → ℤ) (X Y : Finset V) (m : ℕ) : ℕ :=
  pstH (4 * m + 1) (Fintype.card D) (Fintype.card F) (Fintype.card V)
    (isoW_bound D V F (capR M c X Y)).toNat

/-- The cost of the weight stage. -/
def costB (m : ℕ) : ℕ := 360 * m + 300

lemma card_V_le (h' : EnumOK M.dual en m) : Fintype.card V ≤ m := by
  have := card_F_le h'
  exact this

lemma card_D_eq (h : EnumOK M en m) : Fintype.card D = m := card_eq h

set_option maxHeartbeats 1000000 in
/-- **The weight stage** (see the module docstring). -/
theorem stB_exec (hM : M.IsPlane) (h : EnumOK M en m) (h' : EnumOK M.dual en m) (hm : 0 < m)
    {cp : D → ℤ} (hcp : ∀ d, 0 ≤ cp d) {X Y : Finset V} {d₀ : D}
    (c : Config) (hc : WordsBounded W c) {Sb Cb Xb Yb nF nV : ℕ} (τv : F ≃ Fin nF)
    (τf : V ≃ Fin nV) (hL : StL c.nreg m Sb)
    (r00 : c.nreg 9100 = m) (r03 : c.nreg 9103 = Cb) (r04 : c.nreg 9104 = Xb)
    (r05 : c.nreg 9105 = Yb) (r83 : c.nreg 9183 = nF) (r84 : c.nreg 9184 = nV)
    (hK : KInM M.dual (enEq h) (fun x => 1 + (τv x : ℕ)) (ιG M h)
      (fun y => 2 * m + 1 + (τf y : ℕ)) (ιE M h) c.nmem (Sb + 3 * m))
    (hG1 : c.nmem (Sb + 15 * m + 2) = enEq h d₀)
    (hC : ∀ i < m, c.nmem (Cb + i) = (cp (en i)).toNat)
    (hX : ∀ i < m, c.nmem (Xb + i) = if M.tail (en i) ∈ X then 1 else 0)
    (hY : ∀ i < m, c.nmem (Yb + i) = if M.tail (en i) ∈ Y then 1 else 0)
    (lC : Cb + m ≤ Sb) (lX : Xb + m ≤ Sb) (lY : Yb + m ≤ Sb)
    (oC : 106 * m + 49 ≤ Cb) (oX : 106 * m + 49 ≤ Xb) (oY : 106 * m + 49 ≤ Yb)
    (hW : Sb + stSz m ≤ W) (hWq : (4 * m + 5) * m + 2 * m + 1 ≤ W)
    (hWS : ∑ d, cp d + 1 ≤ (W : ℤ)) (hWM : pstM (stHb M cp X Y m) ≤ W) :
    ∃ c' t, Exec P W stB c c' t ∧ t ≤ costB m ∧
      ∃ C : DTree M.dual, C.root = M.tail d₀ ∧
        c'.nreg 9145 = pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
          (capR M cp X Y) (isoEpsG V F (MSSP.treeW C)) ∧
        c'.nreg 9146 = pstM (pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
          (capR M cp X Y) (isoEpsG V F (MSSP.treeW C))) ∧
        (∀ e, c'.nmem (101 * m + 46 + (Klein.aWT + enEq h e)) =
          zres (pstM (pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
            (capR M cp X Y) (isoEpsG V F (MSSP.treeW C))))
            (STFlow.wlen (stN (V := V) (F := F) (MSSP.treeW C)) (capR M cp X Y)
              (isoEpsG V F (MSSP.treeW C)) e)) ∧
        (∀ e, c'.nmem (101 * m + 46 + (Klein.aPH m + enEq h e)) =
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
        c'.nmem (101 * m + 46 + Klein.aTH m) =
          zres (pstM (pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
            (capR M cp X Y) (isoEpsG V F (MSSP.treeW C))))
            (STFlow.kTh D F (stN (V := V) (F := F) (MSSP.treeW C)) (capR M cp X Y)
              (isoEpsG V F (MSSP.treeW C))) ∧
        c'.nmem (101 * m + 46 + Klein.aH0 m) =
          zres (pstM (pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C))
            (capR M cp X Y) (isoEpsG V F (MSSP.treeW C))))
            (STFlow.kH0 D F (stN (V := V) (F := F) (MSSP.treeW C)) (capR M cp X Y)
              (isoEpsG V F (MSSP.treeW C))) ∧
        (∀ i < m + 1, c'.nmem (103 * m + 46 + i) = 0) ∧
        (∀ a, (a < Sb + 41 * m + 15 ∨ Sb + 64 * m + 21 ≤ a) →
          (a < 101 * m + 46 ∨ 106 * m + 49 ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, ¬ EncScr r → r ≠ 9145 → r ≠ 9146 → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hSz : stSz m = 132 * m + 36 := rfl
  have : Nonempty D := ⟨en 0⟩
  have hcV : Fintype.card V = nV := by rw [Fintype.card_congr τf, Fintype.card_fin]
  have hcF : Fintype.card F = nF := by rw [Fintype.card_congr τv, Fintype.card_fin]
  have hVm : nV ≤ m := hcV ▸ card_V_le h'
  have hFm : nF ≤ m := hcF ▸ card_F_le h
  have hV1 : 1 ≤ nV := by rw [← hcV]; exact Fintype.card_pos_iff.2 ⟨M.tail (en 0)⟩
  -- 1. the registers of `ivProg`
  obtain ⟨c₁, e₁, v₁, f₁, m₁, r₁, rm₁, o₁⟩ := cpL_exec (P := P) stSB1 (by decide) (by decide) c hc
  have a60 : c₁.nreg 7960 = m := (v₁ (7960, 9100) (by simp [stSB1])).trans r00
  have a61 : c₁.nreg 7961 = Sb + 4 * m := (v₁ (7961, 9165) (by simp [stSB1])).trans hL.nf
  have a62 : c₁.nreg 7962 = Sb + 3 * m := (v₁ (7962, 9164) (by simp [stSB1])).trans hL.im
  have a63 : c₁.nreg 7963 = 2 * m + 1 := (v₁ (7963, 9177) (by simp [stSB1])).trans hL.of
  have a64 : c₁.nreg 7964 = nV := (v₁ (7964, 9184) (by simp [stSB1])).trans r84
  have a65 : c₁.nreg 7965 = Sb + 15 * m + 2 := (v₁ (7965, 9169) (by simp [stSB1])).trans hL.gp
  have a66 : c₁.nreg 7966 = Sb + 41 * m + 15 :=
    (v₁ (7966, 9172) (by simp [stSB1])).trans hL.zi
  have a67 : c₁.nreg 7967 = Sb + 63 * m + 21 :=
    (v₁ (7967, 9173) (by simp [stSB1])).trans hL.wb
  have a68 : c₁.nreg 7968 = m := (v₁ (7968, 9100) (by simp [stSB1])).trans r00
  have k₁ : ∀ r, ¬ EncScr r → c₁.nreg r = c.nreg r := fun r hr =>
    f₁ r (by simp only [stSB1, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false]; unfold EncScr at hr; omega)
  -- 2. `ivProg`
  have hNF : ∀ d, c₁.nmem (Sb + 4 * m + enEq h d) = 2 * m + 1 + τf (M.tail d) := fun d => by
    rw [m₁]; have := hK.nf d; simp only [Klein.iNF] at this
    rw [show Sb + 4 * m = Sb + 3 * m + m by omega]; exact this
  have hRV : ∀ d, c₁.nmem (Sb + 3 * m + enEq h d) = enEq h (M.rev d) := fun d => by
    rw [m₁]; have := hK.rv d; simp only [Klein.iRV, add_zero] at this; exact this
  obtain ⟨c₂, t₂, e₂, ht₂, C, hCr, hWw, M₂, R₂, rr₂, rm₂, o₂⟩ :=
    ivProg_exec (P := P) hM (enEq h) τf d₀ c₁ e₁.wb_right a60 a61 a62 a63 a64 a65 a66 a67 a68
      hNF hRV (by rw [m₁]; exact hG1) (by omega) (by omega) (by omega) (Or.inr (by omega))
      (Or.inr (by omega)) (by rw [hcV]; exact hVm) (by rw [hSz] at hW; rw [hcV]; omega)
      (by rw [hSz] at hW; omega) (by rw [hSz] at hW; omega) (by rw [hSz] at hW; omega)
  have k₂ : ∀ r, ¬ EncScr r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [R₂ r (by unfold EncScr at hr; omega), k₁ r hr]
  have g2 : ∀ r, 9100 ≤ r → r < 9200 → c₂.nreg r = c.nreg r := fun r h1 h2 =>
    k₂ r (by unfold EncScr; omega)
  -- 3. the registers of `srProg`
  obtain ⟨c₃, e₃, v₃, f₃, m₃, r₃, rm₃, o₃⟩ := cpL_exec (P := P) stSB2 (by decide) (by decide) c₂
    e₂.wb_right
  set w := MSSP.treeW C with hw
  -- the index data of `srProg`
  set p : SrD := ⟨m, 4 * m + 1, nF, nV, m, fun i => c₃.nmem (Cb + i), fun i => c₃.nmem (Xb + i),
    fun i => c₃.nmem (Yb + i), fun i => c₃.nmem (Sb + 3 * m + i),
    fun i => c₃.nmem (Sb + 63 * m + 21 + i)⟩ with hp
  have hpD : p.nD = m := rfl
  have mlo : ∀ a, a < Sb → c₃.nmem a = c.nmem a := fun a ha => by
    rw [m₃, M₂ a (Or.inl (by omega)) (Or.inl (by omega)), m₁]
  have mim : ∀ a, Sb ≤ a → a < Sb + 41 * m + 15 → c₃.nmem a = c.nmem a := fun a h1 h2 => by
    rw [m₃, M₂ a (Or.inl (by omega)) (Or.inl (by omega)), m₁]
  have hwV : ∀ d, |w d| ≤ Fintype.card V := fun d => MSSP.abs_treeW_le C d
  have hOf : p.OfMap M (enEq h) cp X Y w := by
    refine ⟨hcF.symm, hcV.symm, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_,
      fun d => ?_, hwV, hcp⟩
    · have := ixOf_lt h d
      show c₃.nmem (Cb + ixOf en m d) = _
      rw [mlo _ (by omega), hC _ this, en_ixOf h]
    · have := ixOf_lt h d
      show c₃.nmem (Xb + ixOf en m d) = _
      rw [mlo _ (by omega), hX _ this, en_ixOf h]
    · have := ixOf_lt h d
      show c₃.nmem (Yb + ixOf en m d) = _
      rw [mlo _ (by omega), hY _ this, en_ixOf h]
    · have := ixOf_lt h d
      show c₃.nmem (Sb + 3 * m + ixOf en m d) = _
      rw [mim _ (by omega) (by omega)]
      have := hK.rv d; simp only [Klein.iRV, add_zero] at this; exact this
    · show c₃.nmem (Sb + 63 * m + 21 + enEq h d) = _
      rw [m₃]
      have := hWw d
      have hb := hwV d
      rw [← hcV] at hVm
      have hb' : -(m : ℤ) ≤ w d := by
        have := neg_abs_le (w d); omega
      show _ = (((m : ℕ) : ℤ) + w d).toNat
      omega
    · have := hwV d; rw [← hcV] at hVm; show |w d| ≤ (m : ℤ); omega
  have b00 : c₃.nreg 7800 = p.nD := by
    rw [v₃ (7800, 9100) (by simp [stSB2]), g2 _ (by omega) (by omega), r00]
  have hIn : SrIn p Cb Xb Yb (Sb + 3 * m) (Sb + 63 * m + 21) (101 * m + 46) c₃ := by
    refine ⟨b00, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i _ => rfl, fun i _ => rfl,
      fun i _ => rfl, fun i _ => rfl, fun i _ => rfl⟩
    · rw [v₃ (7801, 9103) (by simp [stSB2]), g2 _ (by omega) (by omega), r03]
    · rw [v₃ (7802, 9104) (by simp [stSB2]), g2 _ (by omega) (by omega), r04]
    · rw [v₃ (7803, 9105) (by simp [stSB2]), g2 _ (by omega) (by omega), r05]
    · rw [v₃ (7804, 9164) (by simp [stSB2]), g2 _ (by omega) (by omega), hL.im]
    · rw [v₃ (7805, 9173) (by simp [stSB2]), g2 _ (by omega) (by omega), hL.wb]
    · rw [v₃ (7806, 9100) (by simp [stSB2]), g2 _ (by omega) (by omega), r00]
    · rw [v₃ (7807, 9183) (by simp [stSB2]), g2 _ (by omega) (by omega), r83]
    · rw [v₃ (7808, 9184) (by simp [stSB2]), g2 _ (by omega) (by omega), r84]
    · rw [v₃ (7809, 9160) (by simp [stSB2]), g2 _ (by omega) (by omega), hL.n]
    · rw [v₃ (7810, 9163) (by simp [stSB2]), g2 _ (by omega) (by omega), hL.b0]
  have hLay : SrLay m Cb Xb Yb (Sb + 3 * m) (Sb + 63 * m + 21) (101 * m + 46) W := by
    rw [hSz] at hW
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, Or.inr (by omega),
      Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
  -- the bounds of `srProg`
  have hIso : IsIsoW M (M.tail d₀) w := by rw [← hCr]; exact isIsoW_treeW C
  have hHle := stH_le hM hIso (capR_nonneg (M := M) hcp X Y) (4 * m + 1)
  have eH := hOf.H_eq
  have hpn : p.n = 4 * m + 1 := rfl
  rw [hpn] at eH
  have hMo : p.Mo ≤ W := by
    have e1 : p.Mo = 2 * p.H + 1 := rfl
    have e2 : pstM (stHb M cp X Y m) = 2 * stHb M cp X Y m + 1 := rfl
    have e3 : p.H ≤ stHb M cp X Y m := by rw [eH]; exact hHle
    omega
  have hS : p.S + 1 ≤ W := by
    have := hOf.S_eq; omega
  have hL0 : p.L0 ≤ W := by
    have : p.L0 = (4 * nF + 5) * nV := rfl
    have h1 : (4 * nF + 5) * nV ≤ (4 * m + 5) * m := Nat.mul_le_mul (by omega) hVm
    omega
  have hLW : ∀ i < p.nD, p.L0 + p.WW i ≤ W := fun i hi => by
    have e0 : p.L0 = (4 * nF + 5) * nV := rfl
    have h1 : (4 * nF + 5) * nV ≤ (4 * m + 5) * m := Nat.mul_le_mul (by omega) hVm
    have hi' : i < m := hi
    have e1 : p.WW i = p.WW (enEq h (en i)) := by
      show _ = c₃.nmem (Sb + 63 * m + 21 + ixOf en m (en i)); rw [ixOf_en h hi']
    have e2 := hOf.WW (en i)
    have hb := hwV (en i)
    rw [← hcV] at hVm
    have : p.WW i ≤ 2 * m := by
      rw [e1, e2]; show (((m : ℕ) : ℤ) + w (en i)).toNat ≤ 2 * m
      have := le_abs_self (w (en i)); omega
    omega
  -- 4. `srProg`
  obtain ⟨c₄, t₄, e₄, ht₄, W4, P4, C4, S4, T4, H4, h33, h34, M₄, R₄, rr₄, rm₄, o₄⟩ :=
    srProg_map (P := P) hOf hLay hMo hS hLW hL0 (by show 1 ≤ 4 * m + 1; omega)
      (by show Fintype.card F + Fintype.card V ≤ 4 * m + 1; omega)
      (by rw [hcV]; exact hV1) c₃ e₃.wb_right hIn
  have g3 : ∀ r, 9100 ≤ r → r < 9200 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    rw [f₃ r (by simp only [stSB2, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false]; omega), g2 r h1 h2]
  -- 5. save `H`, `Mo`; the registers of the gap
  obtain ⟨c₅, e₅, v₅, f₅, m₅, r₅, rm₅, o₅⟩ := cpL_exec (P := P) stSB3 (by decide) (by decide) c₄
    e₄.wb_right
  have d45 : c₅.nreg 9145 = c₄.nreg 7833 := v₅ (9145, 7833) (by simp [stSB3])
  have d46 : c₅.nreg 9146 = c₄.nreg 7834 := v₅ (9146, 7834) (by simp [stSB3])
  have d30 : c₅.nreg 5030 = m + 1 := by
    rw [v₅ (5030, 9179) (by simp [stSB3]), R₄ _ (by omega), g3 _ (by omega) (by omega), hL.gl]
  have d31 : c₅.nreg 5031 = 103 * m + 46 := by
    rw [v₅ (5031, 9178) (by simp [stSB3]), R₄ _ (by omega), g3 _ (by omega) (by omega), hL.gap]
  -- 6. the gap
  obtain ⟨c₆, t₆, e₆, ht₆, Z₆, M₆, R₆, rr₆, rm₆, o₆⟩ := mzFill_exec (P := P) c₅ e₅.wb_right d30 d31
    (by rw [hSz] at hW; omega) (by rw [hSz] at hW; omega)
  have m64 : ∀ a, (a < 103 * m + 46 ∨ 103 * m + 46 + (m + 1) ≤ a) → c₆.nmem a = c₄.nmem a :=
    fun a ha => by rw [M₆ a ha, m₅]
  refine ⟨c₆, _, (e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq e₆))))), ?_, C, hCr, ?_, ?_,
    fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, ?_, ?_, Z₆, fun a h1 h2 => ?_,
    fun r hr a1 a2 => ?_, by rw [rr₆, r₅, rr₄, r₃, rr₂, r₁], by rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · have h2 := ht₂
    unfold ivCost at h2
    simp only [stSB1, stSB2, stSB3, List.length_cons, List.length_nil, costB]
    have : 220 * nV ≤ 220 * m := by omega
    omega
  · rw [R₆ _ (by omega), d45, h33]
  · rw [R₆ _ (by omega), d46, h34]
  · rw [m64 _ (by have := (enEq h e).2; unfold Klein.aWT; omega)]; exact W4 e
  · rw [m64 _ (by have := (enEq h e).2; unfold Klein.aPH; omega)]; exact P4 e
  · rw [m64 _ (by have := (enEq h e).2; unfold aCP; omega)]; exact C4 e
  · rw [m64 _ (by have := (enEq h e).2; unfold aRS; omega)]; exact S4 e
  · rw [m64 _ (by unfold Klein.aTH; omega)]; exact T4
  · rw [m64 _ (by unfold Klein.aH0; omega)]; exact H4
  · rw [m64 a (by omega), M₄ a (by omega), m₃,
      M₂ a (by rcases h1 with h1 | h1 <;> omega) (by rcases h1 with h1 | h1 <;> omega), m₁]
  · unfold EncScr at hr
    rw [R₆ r (by omega), f₅ r (by simp only [stSB3, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false]; omega), R₄ r (by omega), f₃ r (by simp only [stSB2,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]; omega),
      k₂ r (by unfold EncScr; omega)]

end StCall

end BKMNW

end PlanarFlow
