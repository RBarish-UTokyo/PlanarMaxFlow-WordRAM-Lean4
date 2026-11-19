module

public import PlanarFlow.BKMNW.StCallA

/-!
# The map stage of the s-t flow call

* `KInM.move`: Klein's map words move with any copy of their `8 nD + E` words;
* **`stA_exec`**: from the frame arrays `RV = rvI`, `RT = ixOf ∘ rot` of a map numbered by `en`
  (`EnumOK` for the map and its dual) and the flags `XT`, `YT`, the map stage writes, within
  `230 m + 233` steps, at `IMb = Sb + 3m` Klein's encoding of the dual with **compact** node
  numbers (`KInM M.dual (enEq h) (1 + τv) (ιG M h) (2m + 1 + τf) (ιE M h)` for bijections
  `τv : F ≃ Fin nF`, `τf : V ≃ Fin nV`, `nF`, `nV` saved in `r9183`, `r9184`) and the terminal
  darts `StEnc.lastF XT m 0`, `StEnc.lastF YT m 0` at `Gb = Sb + 15m + 1`, `Gb + 1`; the memory changes only
  in the scratch `[Sb, Sb + 41m + 15)`; registers outside `EncScr`, `9183`, `9184` kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

variable {D' X Y : Type*} [Fintype D'] [DecidableEq D'] [Fintype X] [DecidableEq X]

/-- **Klein's map words move with a copy of their words.** -/
theorem KInM.move {Q : CombMap D' X Y} {nD : ℕ} {σ : D' ≃ Fin nD} {ιv : X → ℕ}
    {ιg : D' → ℕ} {ιf : Y → ℕ} {ιe : D' → ℕ} {mem mem' : ℕ → ℕ} {β β' E : ℕ}
    (h : KInM Q σ ιv ιg ιf ιe mem β) (hE : ∀ d, ιe d < E)
    (hm : ∀ i < 8 * nD + E, mem' (β' + i) = mem (β + i)) : KInM Q σ ιv ιg ιf ιe mem' β' where
  rv d := by
    have := (σ d).2; rw [add_assoc, hm _ (by unfold Klein.iRV; omega), ← add_assoc]; exact h.rv d
  nf d := by
    have := (σ d).2; rw [add_assoc, hm _ (by unfold Klein.iNF; omega), ← add_assoc]; exact h.nf d
  ne d := by
    have := (σ d).2; rw [add_assoc, hm _ (by unfold Klein.iNE; omega), ← add_assoc]; exact h.ne d
  ng d := by
    have := (σ d).2; rw [add_assoc, hm _ (by unfold Klein.iNG; omega), ← add_assoc]; exact h.ng d
  nt d := by
    have := (σ d).2; rw [add_assoc, hm _ (by unfold Klein.iNT; omega), ← add_assoc]; exact h.nt d
  nh d := by
    have := (σ d).2; rw [add_assoc, hm _ (by unfold Klein.iNH; omega), ← add_assoc]; exact h.nh d
  is d := by
    have := (σ d).2; rw [add_assoc, hm _ (by unfold Klein.iIS; omega), ← add_assoc]; exact h.is d
  ed d := by
    have := hE d; rw [add_assoc, hm _ (by unfold Klein.iED; omega), ← add_assoc]; exact h.ed d

end StEnc

namespace StCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP StEnc
  NsStep

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

variable {P : Input} {W : ℕ}

/-- The cost of the map stage. -/
def costA (m : ℕ) : ℕ := 230 * m + 233

set_option maxHeartbeats 800000 in
/-- **The map stage** (see the module docstring). -/
theorem stA_exec (h : EnumOK M en m) (h' : EnumOK M.dual en m) (hm : 0 < m) (c : Config)
    (hc : WordsBounded W c) {Sb RVb RTb Xb Yb : ℕ} {XT YT : ℕ → ℕ} (hL : StL c.nreg m Sb)
    (r00 : c.nreg 9100 = m) (r01 : c.nreg 9101 = RVb) (r02 : c.nreg 9102 = RTb)
    (r04 : c.nreg 9104 = Xb) (r05 : c.nreg 9105 = Yb) (r06 : c.nreg 9106 = Sb)
    (hRV : ∀ i < m, c.nmem (RVb + i) = rvI M en m i)
    (hRT : ∀ i < m, c.nmem (RTb + i) = ixOf en m (M.rot (en i)))
    (hX : ∀ i < m, c.nmem (Xb + i) = XT i) (hY : ∀ i < m, c.nmem (Yb + i) = YT i)
    (lR : RVb + m ≤ Sb) (lT : RTb + m ≤ Sb) (lX : Xb + m ≤ Sb) (lY : Yb + m ≤ Sb)
    (hW : Sb + stSz m ≤ W) :
    ∃ c' t, Exec P W stA c c' t ∧ t ≤ costA m ∧
      ∃ (nF nV : ℕ) (τv : F ≃ Fin nF) (τf : V ≃ Fin nV), c'.nreg 9183 = nF ∧
        c'.nreg 9184 = nV ∧
        KInM M.dual (enEq h) (fun x => 1 + (τv x : ℕ)) (ιG M h) (fun y => 2 * m + 1 + (τf y : ℕ))
          (ιE M h) c'.nmem (Sb + 3 * m) ∧
        c'.nmem (Sb + 15 * m + 1) = StEnc.lastF XT m 0 ∧ c'.nmem (Sb + 15 * m + 2) = StEnc.lastF YT m 0 ∧
        (∀ a, (a < Sb ∨ Sb + 41 * m + 15 ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, ¬ EncScr r → r ≠ 9183 → r ≠ 9184 → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hSz : stSz m = 132 * m + 36 := rfl
  -- 1. the registers of `smP`
  obtain ⟨c₁, e₁, v₁, f₁, m₁, r₁, rm₁, o₁⟩ := cpL_exec (P := P) stSA1 (by decide) (by decide) c hc
  have a00 : c₁.nreg 7700 = m := (v₁ (7700, 9100) (by simp [stSA1])).trans r00
  have a01 : c₁.nreg 7701 = RVb := (v₁ (7701, 9101) (by simp [stSA1])).trans r01
  have a02 : c₁.nreg 7702 = RTb := (v₁ (7702, 9102) (by simp [stSA1])).trans r02
  have a03 : c₁.nreg 7703 = Sb := (v₁ (7703, 9106) (by simp [stSA1])).trans r06
  have a04 : c₁.nreg 7704 = Sb + 3 * m := (v₁ (7704, 9164) (by simp [stSA1])).trans hL.im
  have k₁ : ∀ r, (r < 7700 ∨ 7704 < r) → c₁.nreg r = c.nreg r := fun r hr =>
    f₁ r (by simp only [stSA1, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false]; omega)
  -- 2. `smP`
  obtain ⟨c₂, t₂, e₂, ht₂, K₂, Z₂, M₂, R₂, rr₂, rm₂, o₂⟩ := smP_kin (P := P) h h' c₁ e₁.wb_right
    a00 a01 a02 a03 a04 (fun i hi => by rw [m₁]; exact hRV i hi)
    (fun i hi => by rw [m₁]; exact hRT i hi) lR lT le_rfl (by rw [hSz] at hW; omega)
  have k₂ : ∀ r, ¬ EncScr r → c₂.nreg r = c.nreg r := fun r hr => by
    unfold EncScr at hr
    rw [R₂ r (by unfold SmScr; omega), k₁ r (by omega)]
  -- 3. the registers of `cmProg`
  obtain ⟨c₃, e₃, v₃, f₃, m₃, r₃, rm₃, o₃⟩ := cpL_exec (P := P) stSA2 (by decide) (by decide) c₂
    e₂.wb_right
  have g : ∀ r, 9100 ≤ r → r < 9200 → c₂.nreg r = c.nreg r := fun r h1 h2 =>
    k₂ r (by unfold EncScr; omega)
  have b50 : c₃.nreg 7950 = m := by
    rw [v₃ (7950, 9100) (by simp [stSA2]), g _ (by omega) (by omega), r00]
  have b51 : c₃.nreg 7951 = (Sb + 3 * m) + Klein.iNT m := by
    rw [v₃ (7951, 9166) (by simp [stSA2]), g _ (by omega) (by omega), hL.nt]
    unfold Klein.iNT; omega
  have b52 : c₃.nreg 7952 = (Sb + 3 * m) + Klein.iNH m := by
    rw [v₃ (7952, 9167) (by simp [stSA2]), g _ (by omega) (by omega), hL.nh]
    unfold Klein.iNH; omega
  have b53 : c₃.nreg 7953 = (Sb + 3 * m) + Klein.iNF m := by
    rw [v₃ (7953, 9165) (by simp [stSA2]), g _ (by omega) (by omega), hL.nf]
    unfold Klein.iNF; omega
  have b54 : c₃.nreg 7954 = m := by
    rw [v₃ (7954, 9100) (by simp [stSA2]), g _ (by omega) (by omega), r00]
  have b55 : c₃.nreg 7955 = Sb + 40 * m + 15 := by
    rw [v₃ (7955, 9171) (by simp [stSA2]), g _ (by omega) (by omega), hL.rb]
  have k₃ : ∀ r, ¬ EncScr r → c₃.nreg r = c.nreg r := fun r hr => by
    rw [f₃ r (by simp only [stSA2, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false]; unfold EncScr at hr; omega), k₂ r hr]
  -- 4. `cmProg`
  have hFl := fLab_lt h
  have hVl := fLab_lt h'
  obtain ⟨c₄, t₄, e₄, ht₄, τv, τf, K₄, M₄, R₄, rr₄, rm₄, o₄⟩ :=
    cmProg_kin (P := P) (Q := M.dual) (enEq h) (ιv := ιF M h) (ιf := ιV M h')
      (β := Sb + 3 * m) (Rb := Sb + 40 * m + 15) (E := 4 * m + 1) c₃ e₃.wb_right
      (by rw [m₃]; exact K₂) (fun x y e => fLab_inj h (by unfold ιF at e; omega))
      (fun x => by unfold ιF; omega) (fun x => by unfold ιF; have := hFl x; omega)
      (fun x y e => fLab_inj h' (by unfold ιV at e; omega)) (fun y => by unfold ιV; omega)
      (fun y => by unfold ιV; have := hVl y; omega) (fun y => h.fsurj y)
      (fun v => h'.fsurj v) (ιE_lt h) (by omega) (by rw [hSz] at hW; omega)
      (by rw [hSz] at hW; omega) b50 b51 b52 b53 b54 b55
  have k₄ : ∀ r, ¬ EncScr r → c₄.nreg r = c.nreg r := fun r hr => by
    rw [R₄ r (by unfold EncScr at hr; omega), k₃ r hr]
  -- 5. the registers of `gbProg`
  obtain ⟨c₅, e₅, v₅, f₅, m₅, r₅, rm₅, o₅⟩ := cpL_exec (P := P) stSA3 (by decide) (by decide) c₄
    e₄.wb_right
  have g4 : ∀ r, 9100 ≤ r → r < 9200 → c₄.nreg r = c.nreg r := fun r h1 h2 =>
    k₄ r (by unfold EncScr; omega)
  have d50 : c₅.nreg 7850 = m := by
    rw [v₅ (7850, 9100) (by simp [stSA3]), g4 _ (by omega) (by omega), r00]
  have d51 : c₅.nreg 7851 = Xb := by
    rw [v₅ (7851, 9104) (by simp [stSA3]), g4 _ (by omega) (by omega), r04]
  have d52 : c₅.nreg 7852 = Yb := by
    rw [v₅ (7852, 9105) (by simp [stSA3]), g4 _ (by omega) (by omega), r05]
  have d53 : c₅.nreg 7853 = Sb + 15 * m + 1 := by
    rw [v₅ (7853, 9168) (by simp [stSA3]), g4 _ (by omega) (by omega), hL.gb]
  -- the memory below the scratch is the start's
  have mlo : ∀ a, a < Sb → c₅.nmem a = c.nmem a := fun a ha => by
    rw [m₅, M₄ a (by omega) (by omega) (by omega), m₃, M₂ a (by omega) (by omega), m₁]
  -- 6. `gbProg`
  obtain ⟨c₆, t₆, e₆, ht₆, M₆, R₆, rr₆, rm₆, o₆⟩ := gbProg_exec (P := P) (XT := XT) (YT := YT)
    (by omega) (by omega) (by rw [hSz] at hW; omega) (by rw [hSz] at hW; omega) c₅ e₅.wb_right
    d50 d51 d52 d53 (fun i hi => by rw [mlo _ (by omega)]; exact hX i hi)
    (fun i hi => by rw [mlo _ (by omega)]; exact hY i hi)
  -- 7. save `nF`, `nV`
  obtain ⟨c₇, e₇, v₇, f₇, m₇, r₇, rm₇, o₇⟩ := cpL_exec (P := P) stSA4 (by decide) (by decide) c₆
    e₆.wb_right
  have s83 : c₇.nreg 9183 = c₄.nreg 7957 := by
    rw [v₇ (9183, 7957) (by simp [stSA4]), R₆ _ (by omega),
      f₅ _ (by simp [stSA3])]
  have s84 : c₇.nreg 9184 = c₄.nreg 7959 := by
    rw [v₇ (9184, 7959) (by simp [stSA4]), R₆ _ (by omega),
      f₅ _ (by simp [stSA3])]
  have mfin : c₇.nmem = upd (upd c₅.nmem (Sb + 15 * m + 1) (StEnc.lastF XT m 0)) (Sb + 15 * m + 1 + 1)
      (StEnc.lastF YT m 0) := by rw [m₇, M₆]
  refine ⟨c₇, _, (e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq (e₆.seq e₇)))))), ?_,
    c₄.nreg 7957, c₄.nreg 7959, τv, τf, s83, s84, ?_, ?_, ?_, fun a ha => ?_, fun r hr h1 h2 => ?_,
    by rw [r₇, rr₆, r₅, rr₄, r₃, rr₂, r₁], by rw [rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₇, o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · simp only [stSA1, stSA2, stSA3, stSA4, List.length_cons, List.length_nil, costA]
    omega
  · refine K₄.move (ιE_lt h) (fun i hi => ?_)
    rw [mfin, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), m₅]
  · rw [mfin, upd_other _ _ _ (by omega), upd_same]
  · rw [mfin, upd_same]
  · rw [mfin, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), m₅,
      M₄ a (by omega) (by omega) (by omega), m₃, M₂ a (by omega) (by omega), m₁]
  · rw [f₇ r (by simp [stSA4]; omega), R₆ r (by unfold EncScr at hr; omega),
      f₅ r (by simp only [stSA3, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false]; unfold EncScr at hr; omega), k₄ r hr]

end StCall

end BKMNW

end PlanarFlow
