module

public import PlanarFlow.BKMNW.StCallSB

/-!
# The tree stage of the s-t flow call

* `wlen_bds`: the perturbed lengths `wlen (stN w) (capR c X Y) (isoEpsG w)` are positive and below
  `pstM (pcoreH …)`; `pcoreH_ge`: `n + 1 ≤ pcoreH n …`;
* `stSC1_exec` (the registers of Dijkstra's run, `Inf = Mo² + 1`, the root word `NT[G[1]]`);
* **`stC_exec`**: after the weight stage, within `costC m` steps, Dijkstra's run on the dual with
  the lengths read from the residues at `β₀` (`stdP_exec`) and its parent words give the initial
  dual tree `T₀` (`STFlow.t0_of_par`: rooted at `face d₀`, `LInv` for all terminals), and
  `kiProg` writes Klein's `KInit` words (the orders of `T₀` and of a cotree `C₀` rooted at
  `tail d₁` off `T₀`) at `IVb = Sb + 24m + 5`; the memory changes only in
  `[Sb + 24m + 5, Sb + 40m + 15)` and `[Sb + 64m + 21, Sb + 132m + 36)`.
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

lemma pcoreH_ge (n : ℕ) (N : ℤ) (c ε : D → ℤ) : n + 1 ≤ pcoreH D V F n N c ε := by
  unfold pcoreH pstH pstVb; omega

/-- The perturbed lengths are positive and below the modulus. -/
lemma wlen_bds (hM : M.IsPlane) {w : D → ℤ} {t : V} (hw : IsIsoW M t w) {c : D → ℤ}
    (hc : ∀ d, 0 ≤ c d) (n : ℕ) (d : D) :
    0 < STFlow.wlen (stN (V := V) (F := F) w) c (isoEpsG V F w) d ∧
      STFlow.wlen (stN (V := V) (F := F) w) c (isoEpsG V F w) d <
        pstM (pcoreH D V F n (stN (V := V) (F := F) w) c (isoEpsG V F w)) := by
  have hε : ∀ d, 1 ≤ isoEpsG V F w d := fun d => (isoEpsG_bounds hM hw d).1
  have hS : 0 ≤ ∑ d, isoEpsG V F w d := Finset.sum_nonneg fun d _ => zero_le_one.trans (hε d)
  have hL : 0 ≤ lexR F (isoEpsG V F w) := by unfold lexR; positivity
  have hN : 1 ≤ stN (V := V) (F := F) w := by unfold stN; omega
  obtain ⟨h1, -, -, -, -⟩ := start_abs_le (D := D) (F := F) hN hc (fun d => zero_le_one.trans (hε d))
  have h2 := kH0_le_pcoreH (D := D) (V := V) (F := F) n (stN (V := V) (F := F) w) c (isoEpsG V F w)
  have h3 := h1 d
  have hpos : 0 < STFlow.wlen (stN (V := V) (F := F) w) c (isoEpsG V F w) d := by
    unfold STFlow.wlen
    have := hε d; have := hc d
    have : 0 ≤ stN (V := V) (F := F) w * c d := mul_nonneg (by omega) this
    omega
  refine ⟨hpos, ?_⟩
  have := le_abs_self (STFlow.wlen (stN (V := V) (F := F) w) c (isoEpsG V F w) d)
  unfold pstM; push_cast; omega

/-- The registers of Dijkstra's run. -/
theorem stSC1_exec (c : Config) (hc : WordsBounded W c)
    (h1 : c.nreg 9146 * c.nreg 9146 + c.nreg 9182 ≤ W)
    (h2 : c.nreg 9166 + c.nmem (c.nreg 9169) ≤ W) :
    ∃ c' t, Exec P W stSC1 c c' t ∧ t = 11 ∧
      c'.nreg 7860 = c.nreg 9100 ∧ c'.nreg 7861 = c.nreg 9160 ∧ c'.nreg 7862 = c.nreg 9166 ∧
      c'.nreg 7863 = c.nreg 9167 ∧ c'.nreg 7864 = c.nreg 9163 ∧ c'.nreg 7865 = c.nreg 9174 ∧
      c'.nreg 7870 = c.nreg 9146 * c.nreg 9146 + c.nreg 9182 ∧
      c'.nreg 7871 = c.nmem (c.nreg 9166 + c.nmem (c.nreg 9169)) ∧
      (∀ r, (r < 7860 ∨ 7871 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h1' : c.nreg 9146 * c.nreg 9146 ≤ W := by omega
  unfold stSC1
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

/-- The cost of the tree stage. -/
def costC (m : ℕ) : ℕ := stdCost (4 * m + 1) m + 365 * m + 300

set_option maxHeartbeats 1600000 in
/-- **The tree stage** (see the module docstring). -/
theorem stC_exec (hM : M.IsPlane) (h : EnumOK M en m) (h' : EnumOK M.dual en m) (hm : 0 < m)
    {cp : D → ℤ} (hcp : ∀ d, 0 ≤ cp d) (X Y : Finset V) {d₀ d₁ : D} {wt : D → ℤ}
    (hw : IsIsoW M (M.tail d₀) wt)
    (c : Config) (hc : WordsBounded W c) {Sb nF nV : ℕ} (τv : F ≃ Fin nF)
    (τf : V ≃ Fin nV) (hL : StL c.nreg m Sb)
    (r00 : c.nreg 9100 = m) (r83 : c.nreg 9183 = nF) (r84 : c.nreg 9184 = nV)
    (r46 : c.nreg 9146 = pstM (pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) wt)
      (capR M cp X Y) (isoEpsG V F wt)))
    (hK : KInM M.dual (enEq h) (fun x => 1 + (τv x : ℕ)) (ιG M h)
      (fun y => 2 * m + 1 + (τf y : ℕ)) (ιE M h) c.nmem (Sb + 3 * m))
    (hG0 : c.nmem (Sb + 15 * m + 1) = enEq h d₁) (hG1 : c.nmem (Sb + 15 * m + 2) = enEq h d₀)
    (hwt : ∀ e, c.nmem (101 * m + 46 + (Klein.aWT + enEq h e)) =
      zres (pstM (pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) wt)
        (capR M cp X Y) (isoEpsG V F wt)))
        (STFlow.wlen (stN (V := V) (F := F) wt) (capR M cp X Y) (isoEpsG V F wt) e))
    (lS : 106 * m + 49 ≤ Sb) (hW : Sb + stSz m ≤ W)
    (hWM : pstM (stHb M cp X Y m) * pstM (stHb M cp X Y m) + pstM (stHb M cp X Y m) + 1 ≤ W) :
    ∃ c' t, Exec P W stC c c' t ∧ t ≤ costC m ∧
      ∃ (T₀ : DTree M) (ts : List F) (C₀ : DTree M.dual) (cs : List V),
        T₀.root = M.face d₀ ∧
        (∀ s t', LInv (capR M cp X Y) (isoEpsG V F wt) s t'
          (tSt M (capR M cp X Y) (isoEpsG V F wt) T₀)) ∧
        C₀.root = M.tail d₁ ∧ (∀ x, x ≠ C₀.root → ¬ (toDD T₀).InT (C₀.par x)) ∧
        Klein.Orders (toDD T₀) ((List.finRange nF).map τv.symm) ts ∧
        Klein.Orders C₀ ((List.finRange nV).map τf.symm) cs ∧
        (∀ i (hi : i < ((List.finRange nF).map τv.symm).length),
          c'.nmem (Sb + 24 * m + 5 + i) = 1 + τv ((List.finRange nF).map τv.symm)[i]) ∧
        (∀ i (hi : i < ts.length),
          c'.nmem (Sb + 24 * m + 5 + (4 * m + 1) + i) = enEq h (T₀.par ts[i])) ∧
        (∀ i (hi : i < ((List.finRange nV).map τf.symm).length),
          c'.nmem (Sb + 24 * m + 5 + 2 * (4 * m + 1) + i) =
            2 * m + 1 + τf ((List.finRange nV).map τf.symm)[i]) ∧
        (∀ i (hi : i < cs.length),
          c'.nmem (Sb + 24 * m + 5 + 3 * (4 * m + 1) + i) = enEq h (C₀.par cs[i])) ∧
        c'.nmem (Sb + 24 * m + 5 + 4 * (4 * m + 1)) = ((List.finRange nF).map τv.symm).length ∧
        c'.nmem (Sb + 24 * m + 5 + 4 * (4 * m + 1) + 1) = ts.length ∧
        c'.nmem (Sb + 24 * m + 5 + 4 * (4 * m + 1) + 2) =
          ((List.finRange nV).map τf.symm).length ∧
        c'.nmem (Sb + 24 * m + 5 + 4 * (4 * m + 1) + 3) = cs.length ∧
        (∀ a, (a < Sb + 24 * m + 5 ∨ Sb + 40 * m + 15 ≤ a) →
          (a < Sb + 64 * m + 21 ∨ Sb + 132 * m + 36 ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, ¬ EncScr r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hSz : stSz m = 132 * m + 36 := rfl
  rw [hSz] at hW
  have : Nonempty D := ⟨en 0⟩
  have hcV : Fintype.card V = nV := by rw [Fintype.card_congr τf, Fintype.card_fin]
  have hcF : Fintype.card F = nF := by rw [Fintype.card_congr τv, Fintype.card_fin]
  have hVm : nV ≤ m := hcV ▸ card_V_le h'
  have hFm : nF ≤ m := hcF ▸ card_F_le h
  have hc' : ∀ d, 0 ≤ capR M cp X Y d := capR_nonneg hcp X Y
  have hbd := fun d => wlen_bds (n := 4 * m + 1) hM hw hc' d
  have hHb := stH_le hM hw hc' (4 * m + 1)
  have hHn := pcoreH_ge (V := V) (F := F) (4 * m + 1) (stN (V := V) (F := F) wt)
    (capR M cp X Y) (isoEpsG V F wt)
  set H := pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) wt) (capR M cp X Y)
    (isoEpsG V F wt) with hH
  set ℓ := STFlow.wlen (stN (V := V) (F := F) wt) (capR M cp X Y) (isoEpsG V F wt) with hℓ
  have hHb' : H ≤ stHb M cp X Y m := hHb
  have hMo : pstM H ≤ pstM (stHb M cp X Y m) := by unfold pstM; omega
  have hMM : pstM H * pstM H ≤ pstM (stHb M cp X Y m) * pstM (stHb M cp X Y m) :=
    Nat.mul_le_mul hMo hMo
  have eMo : pstM H = 2 * H + 1 := rfl
  -- 1. the registers of Dijkstra's run
  have hσ0 := (enEq h d₀).2
  obtain ⟨c₁, t₁, e₁, ht₁, a60, a61, a62, a63, a64, a65, a70, a71, k₁, m₁, r₁, rm₁, o₁⟩ :=
    stSC1_exec (P := P) c hc (by rw [r46, hL.one]; omega)
      (by rw [hL.nt, hL.gp, hG1]; omega)
  have hNT : ∀ d, c.nmem (Sb + 7 * m + enEq h d) = 1 + τv (M.face d) := fun d => by
    have := hK.nt d; simp only [Klein.iNT] at this
    rw [show Sb + 7 * m = Sb + 3 * m + 4 * m by omega]; exact this
  have hNH : ∀ d, c.nmem (Sb + 8 * m + enEq h d) = 1 + τv (M.face (M.rev d)) := fun d => by
    have := hK.nh d; simp only [Klein.iNH] at this
    rw [show Sb + 8 * m = Sb + 3 * m + 5 * m by omega]; exact this
  have hLv : ∀ d, c.nmem (101 * m + 46 + enEq h d) = (ℓ d).toNat := fun d => by
    have := hwt d; simp only [Klein.aWT, zero_add] at this
    rw [this]
    exact zres_nat (Int.toNat_of_nonneg (hbd d).1.le) (by
      have := (hbd d).2; have := (hbd d).1; omega)
  -- 2. Dijkstra's run on the dual
  obtain ⟨c₂, t₂, e₂, ht₂, hD₂, hP₂, M₂, R₂, rr₂, rm₂, o₂⟩ :=
    stdP_exec (P := P) (M := M.dual) (enEq h) (n := 4 * m + 1) (ιv := fun x => 1 + (τv x : ℕ))
      (fun x y e => τv.injective (Fin.ext (by simpa using e)))
      (fun x => by have := (τv x).2; omega) (by omega) (by omega) (ℓ := ℓ) (fun d => (hbd d).1)
      (Lmax := pstM H) (Inf := pstM H * pstM H + 1) (fun d => by
        have := (hbd d).2; have := (hbd d).1; omega)
      (by
        have h1 : Fintype.card F * pstM H ≤ pstM H * pstM H :=
          Nat.mul_le_mul_right _ (by rw [eMo]; omega)
        omega)
      (by omega) (u := M.face d₀) (fun x => reach_dual hM ℓ (M.face d₀) x)
      (NTb := Sb + 7 * m) (NHb := Sb + 8 * m) (Lb := 101 * m + 46) (Ab := Sb + 64 * m + 21)
      (by omega) (by omega) (by omega) (by omega) c₁ e₁.wb_right
      (fun d => by rw [m₁]; exact hNT d) (fun d => by rw [m₁]; exact hNH d)
      (fun d => by rw [m₁]; exact hLv d)
      (by rw [a60, r00]) (by rw [a61, hL.n]) (by rw [a62, hL.nt]) (by rw [a63, hL.nh])
      (by rw [a64, hL.b0]) (by rw [a65, hL.ab]) (by rw [a70, r46, hL.one])
      (by rw [a71, hL.nt, hL.gp, hG1]; exact hNT d₀)
  have k₂ : ∀ r, ¬ EncScr r → c₂.nreg r = c.nreg r := fun r hr => by
    unfold EncScr at hr
    rw [R₂ r (by omega), k₁ r (by omega)]
  have g2 : ∀ r, 9100 ≤ r → r < 9200 → c₂.nreg r = c.nreg r := fun r h1 h2 =>
    k₂ r (by unfold EncScr; omega)
  -- 3. the initial dual tree
  obtain ⟨T₀, hroot, hPAR, hLI⟩ := t0_of_par (ιF := fun x => 1 + (τv x : ℕ)) hM hcp X Y hw d₀
    (mem := c₂.nmem) (Pb := Sb + 64 * m + 21 + 9 * (4 * m + 1) + 1 + m) (σ := enEq h)
    (fun x hx => hP₂ x hx)
  -- 4. the registers of `kiProg`
  obtain ⟨c₃, e₃, v₃, f₃, m₃, r₃, rm₃, o₃⟩ := cpL_exec (P := P) stSC2 (by decide) (by decide) c₂
    e₂.wb_right
  have b : ∀ x y, (x, y) ∈ stSC2 → ∀ v, c.nreg y = v → c₃.nreg x = v := fun x y hxy v hv => by
    rw [v₃ (x, y) hxy, g2 y (by simp [stSC2] at hxy; omega) (by simp [stSC2] at hxy; omega), hv]
  have mlo : ∀ a, a < Sb + 64 * m + 21 → c₃.nmem a = c.nmem a := fun a ha => by
    rw [m₃, M₂ a (Or.inl ha), m₁]
  -- 5. `kiProg`
  obtain ⟨c₄, t₄, e₄, ht₄, ts, C₀, cs, hC₀, hoff, hOT, hOC, hIV, hIT, hIF, hIC, hH0, hH1, hH2,
      hH3, M₄, R₄, rr₄, rm₄, o₄⟩ :=
    kiProg_exec (P := P) hM (enEq h) τv τf d₀ d₁ hroot (NTb := Sb + 7 * m) (NFb := Sb + 4 * m)
      (RVb := Sb + 3 * m) (IVb := Sb + 24 * m + 5) (ofF := 2 * m + 1)
      (PRb := Sb + 101 * m + 31) (Z := Sb + 105 * m + 33) (Gb := Sb + 15 * m + 1) c₃ e₃.wb_right
      (b _ _ (by simp [stSC2]) _ r00) (b _ _ (by simp [stSC2]) _ hL.nt)
      (b _ _ (by simp [stSC2]) _ hL.nf) (b _ _ (by simp [stSC2]) _ hL.im)
      (b _ _ (by simp [stSC2]) _ hL.iv) (b _ _ (by simp [stSC2]) _ hL.n)
      (b _ _ (by simp [stSC2]) _ hL.of) (b _ _ (by simp [stSC2]) _ r83)
      (b _ _ (by simp [stSC2]) _ r84) (b _ _ (by simp [stSC2]) _ hL.pr)
      (b _ _ (by simp [stSC2]) _ hL.zk) (b _ _ (by simp [stSC2]) _ hL.gb)
      (fun d => by rw [mlo _ (by have := (enEq h d).2; omega)]; exact hNT d)
      (fun d => by
        rw [mlo _ (by have := (enEq h d).2; omega)]
        have := hK.nf d; simp only [Klein.iNF] at this
        rw [show Sb + 4 * m = Sb + 3 * m + m by omega]; exact this)
      (fun d => by
        rw [mlo _ (by have := (enEq h d).2; omega)]
        have := hK.rv d; simp only [Klein.iRV, add_zero] at this; exact this)
      (fun x hx => by
        rw [m₃, show Sb + 101 * m + 31 + 1 + (τv x : ℕ) =
          Sb + 64 * m + 21 + 9 * (4 * m + 1) + 1 + m + (1 + (τv x : ℕ)) by omega]
        exact hPAR x (hroot ▸ hx))
      (by rw [mlo _ (by omega)]; exact hG0) (by rw [mlo _ (by omega)]; exact hG1)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  refine ⟨c₄, _, (e₁.seq (e₂.seq (e₃.seq e₄))), ?_, T₀, ts, C₀, cs, hroot,
    fun s t' => hLI s t', hC₀, hoff, hOT, hOC, hIV, hIT, hIF, hIC, hH0, hH1, hH2, hH3,
    fun a h1 h2 => ?_, fun r hr => ?_, by rw [rr₄, r₃, rr₂, r₁], by rw [rm₄, rm₃, rm₂, rm₁],
    by rw [o₄, o₃, o₂, o₁]⟩
  · have h4 := ht₄
    unfold kiCost at h4
    simp only [stSC2, List.length_cons, List.length_nil, costC]
    have : 122 * nF ≤ 122 * m := by omega
    have : 178 * nV ≤ 178 * m := by omega
    omega
  · rw [M₄ a (by omega) (by omega) (by omega), m₃, M₂ a (by omega), m₁]
  · unfold EncScr at hr
    rw [R₄ r (by omega), f₃ r (by simp only [stSC2, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false]; omega), k₂ r (by unfold EncScr; omega)]

end StCall

end BKMNW

end PlanarFlow
