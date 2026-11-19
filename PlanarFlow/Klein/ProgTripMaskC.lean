module

public import PlanarFlow.Klein.ProgTripMask
public import PlanarFlow.Klein.ProgMoveC
public import PlanarFlow.Klein.ProgWeightC

/-!
# Klein's masked loop over the moves on the machine, with bounded comparisons

`tBodyM_orunC`, `tLoopM_orunC`: the proofs of `PlanarFlow/Klein/ProgTripMask.lean` replayed as
runs whose real comparisons are bounded (`DynTree.ORunC`). Besides `TInvM`, the loop keeps **the
bound `A - Lo` of the values of the forest** (`Lo` the bound at the nodes of the faces of
`Stored`, between `tripTh + (#V + 1) tripK` and `tripH0`). With `|tripWt| ≤ Wt`,
`|tripL| ≤ Wt`, `Wt + tripW + 2 #V tripW + |tripTh| ≤ A - tripH0` and
`30 (A - tripTh) + 12 tripK + 8 (Wt + tripW) ≤ H`, the queries (`qMask_orunC`), the pivot loop
(`mv_orunAC`) and the step to the next move (`nx_orunC`) are compare-bounded and leave the bound
`A - (Lo₄ - tripK)` for the next move.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ} {nD : ℕ}
  {σ : D ≃ Fin nD} {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} {t : ℕ}
  {X : ℕ → V} {fl : ℕ → Bool}

local notation "𝒢" => pieceGraph M S ℓ

section
variable {P : Input} {W B Hc : ℕ}

set_option maxHeartbeats 800000 in
theorem tBodyM_orunC (hW : B + 16 * (n + 1) ≤ W) (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ W)
    (hB : n + 2 * nD ≤ B) (hOUT : aOUT nD + kRank fl k * t ≤ B)
    (hRB : aRBM n k + kRank fl k * t ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W)
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    (hX : KTgt M k g S ℓ nD n ιv t X P) {F₀ : Forest} {c₀ : Config}
    (y : ℕ × (ℕ → MoveData M S) × ℝ) (hs : List EOp) (G : List VT) (c : Config)
    (h : TInvM M k g S ℓ σ n ιv ιg ιf ιe t X fl B W F₀ c₀ y hs G c) (ht : y.1 < k) {A Wt : ℝ}
    (hwtb : ∀ j' d, |(tripWt M k g S ℓ j' d : ℝ)| ≤ Wt) (hTLb : |(tripL V S ℓ : ℝ)| ≤ Wt)
    (hA1 : Wt + tripW S ℓ + 2 * (Fintype.card V * tripW S ℓ) + |(tripTh V S ℓ : ℝ)| ≤
      A - tripH0 V S ℓ k)
    (hA2 : 30 * (A - tripTh V S ℓ) + 12 * tripK V S ℓ + 8 * (Wt + tripW S ℓ) ≤ Hc)
    (hVy : VBnd (A - y.2.2) n (runOpsE n F₀ hs).1) (hLoy : y.2.2 ≤ tripH0 V S ℓ k) :
    ∃ (y' : ℕ × (ℕ → MoveData M S) × ℝ) (c' : Config) (os : List EOp) (G' : List VT),
      ORunC P W Hc B n (tBodyMS B nD n k t) c (runOpsE n F₀ hs).1 G c' os G'
        (tCntM t (fl y.1) (y'.2.1 y.1) (tripΔ M k g S y.1).card)
        (14 * (if fl y.1 then t else 0) + 182 + 30 * (tripΔ M k g S y.1).card) ∧
      TInvM M k g S ℓ σ n ιv ιg ιf ιe t X fl B W F₀ c₀ y' (hs ++ os) G' c' ∧ y'.1 = y.1 + 1 ∧
      (∀ j < y.1, y'.2.1 j = y.2.1 j) ∧ VBnd (A - y'.2.2) n (runOpsE n F₀ (hs ++ os)).1 ∧
      y'.2.2 ≤ tripH0 V S ℓ k := by
  classical
  obtain ⟨J, R, Lo⟩ := y
  simp only at h ht hVy hLoy ⊢
  have hK0r : (0 : ℝ) ≤ tripK V S ℓ := by exact_mod_cast tripK_nonneg
  have hW0r : (0 : ℝ) ≤ tripW S ℓ := by exact_mod_cast tripW_nonneg
  have hWt0 : 0 ≤ Wt := (abs_nonneg _).trans hTLb
  have hVr : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ Fintype.card V * tripW S ℓ := mul_nonneg hVr hW0r
  have hH0e : (tripH0 V S ℓ k : ℝ) = tripTh V S ℓ + (k + 1) * ((Fintype.card V + 1) *
      tripK V S ℓ) := by simp [tripH0]
  have hThLo : (tripTh V S ℓ : ℝ) + (Fintype.card V + 1) * tripK V S ℓ ≤ Lo := by
    have h1 := h.lo
    have hJk : (J : ℝ) + 1 ≤ k := by exact_mod_cast ht
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ k - (J + 1))
      (mul_nonneg (by linarith : (0 : ℝ) ≤ Fintype.card V + 1) hK0r)]
  set F := (runOpsE n F₀ hs).1 with hF
  set f := kRank fl k with hf
  set q := kRank fl J with hq
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hk := H.two_le_k
  have hqf : q ≤ f := kRank_mono fl ht.le
  have hqt : q * t ≤ f * t := Nat.mul_le_mul_right _ hqf
  have hqf' : fl J = true → q * t + t ≤ f * t := fun hb => by
    have := Nat.mul_le_mul_right t (kRank_succ_le fl ht hb)
    rw [Nat.add_mul, one_mul, ← hq, ← hf] at this
    exact this
  have hc := h.wb
  have hBW : B ≤ W := by omega
  have h80 : c.nreg 80 = J := h.r80
  have h82 : c.nreg 82 = q := h.r82
  -- the registers of the move and its flag
  obtain ⟨c₁, k₁, e₁, hk₁, p90, p91, p104, p105, p106, p109, p107, p108, n₁, r₁, mm₁, rm₁,
      out₁⟩ : ∃ c' k',
      Exec P W (block [.modN 90 80 81, .constN 92 1, .addN 91 80 92, .modN 91 91 81,
        .constN 105 t, .mulN 93 82 105, .constN 106 (aOUT nD), .addN 106 106 93,
        .constN 109 (aRBM n k), .addN 109 109 93, .constN 104 0, .constN 107 (aMK n),
        .addN 107 107 80, .loadN 108 107, .constN 107 0]) c c' k' ∧ k' = 15 ∧
      c'.nreg 90 = J % k ∧ c'.nreg 91 = (J + 1) % k ∧
      c'.nreg 104 = 0 ∧ c'.nreg 105 = t ∧ c'.nreg 106 = aOUT nD + q * t ∧
      c'.nreg 109 = aRBM n k + q * t ∧ c'.nreg 107 = 0 ∧ c'.nreg 108 = c.nmem (aMK n + J) ∧
      (∀ r, (r < 90 ∨ (94 ≤ r ∧ r < 104) ∨ 110 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    all_goals try (first
      | omega
      | (unfold aOUT aRBM aMK at *; omega)
      | (config_simp; rw [h80]; omega)
      | (config_simp; rw [h80]; unfold aMK; omega)
      | (config_simp; rw [h82]; unfold aOUT at *; omega)
      | (config_simp; rw [h82]; unfold aRBM at *; omega))
    refine ⟨rfl, ?_, ?_, by config_simp, by config_simp, ?_, ?_, by config_simp, ?_,
      fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [h80, h.r81]
    · config_simp; rw [h80, h.r81]
    · config_simp; rw [h82]
    · config_simp; rw [h82]
    · config_simp; rw [h80]
    · config_simp
      simp only [upd_other _ _ _ (show r ≠ 105 by omega), upd_other _ _ _ (show r ≠ 104 by omega),
        upd_other _ _ _ (show r ≠ 106 by omega), upd_other _ _ _ (show r ≠ 93 by omega),
        upd_other _ _ _ (show r ≠ 91 by omega), upd_other _ _ _ (show r ≠ 92 by omega),
        upd_other _ _ _ (show r ≠ 90 by omega), upd_other _ _ _ (show r ≠ 109 by omega),
        upd_other _ _ _ (show r ≠ 107 by omega), upd_other _ _ _ (show r ≠ 108 by omega)]
  have o₁ : ORunC P W Hc B n _ c F G c₁ [] G 0 k₁ := ORunC.glue (H := Hc) e₁ h.lcte
    (fun a _ _ => by rw [mm₁, rm₁]; exact ⟨rfl, rfl⟩) (n₁ 151 (by omega)) (by rfl)
  have p108' : c₁.nreg 108 = if fl J then 1 else 0 := by rw [p108]; exact h.flags J ht
  have p82 : c₁.nreg 82 = q := by rw [n₁ 82 (Or.inl (by omega)), h82]
  -- the answers at the targets, when the move is flagged
  obtain ⟨c₂, G₂, o₂, q₂, s82, rg₂, out₂, nm₂, rm₂⟩ := qMask_orunC (P := P) (H := Hc) (k := k) (X := X)
    (xb := fun i => if Reach 𝒢 (M.tail (g 0)) (X i) then 1 else 0) hW
    (by unfold iXT; omega) hP hL hX.xn hX.xr (base := aOUT nD + q * t)
    (rbase := aRBM n k + q * t) (fl J)
    (fun hb => by have := hqf' hb; unfold aOUT at *; omega)
    (fun hb => by have := hqf' hb; unfold aRBM at *; omega)
    e₁.wb_right o₁.1.2.lcte hVy (by
      have := abs_nonneg (tripTh V S ℓ : ℝ)
      nlinarith) p104 p105 p106 p109 p107 p108' p82
    (by have := kRank_le fl J; omega)
  -- the threshold
  have hc₂ := o₂.1.2.wb
  have hth₂ : c₂.rmem (aTH nD) = tripTh V S ℓ := by
    rw [rm₂ _ (Or.inl (by unfold aTH; unfold aOUT at hOUT; omega))
      (fun _ => Or.inl (by unfold aTH aOUT; omega)), rm₁, h.th]
  obtain ⟨c₃, k₃, e₃, hk₃, s100, s102, s103, n₃, r₃, mm₃, rm₃, out₃⟩ : ∃ c' k', Exec P W
      (block [.constN 94 (aTH nD), .loadR 100 94, .constN 102 0, .constN 103 1]) c₂ c' k' ∧
      k' = 4 ∧ c'.rreg 100 = ((tripL V S ℓ - 2 * (Fintype.card V * tripW S ℓ) : ℤ) : ℝ) ∧
      c'.nreg 102 = 0 ∧ c'.nreg 103 = 1 ∧
      (∀ r, r ≠ 94 → r ≠ 102 → r ≠ 103 → c'.nreg r = c₂.nreg r) ∧
      (∀ r, r ≠ 100 → c'.rreg r = c₂.rreg r) ∧ c'.nmem = c₂.nmem ∧ c'.rmem = c₂.rmem ∧
      c'.output = c₂.output := by
    exec_block
    all_goals try (first | omega | (unfold aTH; omega))
    refine ⟨rfl, by config_simp; exact hth₂, by config_simp, by config_simp, fun r h1 h2 h3 => ?_,
      fun r hr => ?_, rfl, rfl, rfl⟩
    · config_simp
      simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3]
    · config_simp; simp only [upd_other _ _ _ hr]
  have o₃ : ORunC P W Hc B n _ c₂ _ G₂ c₃ [] G₂ 0 k₃ := ORunC.glue (H := Hc) e₃ o₂.1.2.lcte
    (fun a _ _ => by rw [mm₃, rm₃]; exact ⟨rfl, rfl⟩) (n₃ 151 (by omega) (by omega) (by omega)) (by rfl)
  -- the memory and the registers at the start of the pivot loop
  have hnm₃ : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aRBM n k ∨ aRBM n k + f * t ≤ a) →
      c₃.nmem a = c.nmem a := fun a ha ha' => by
    rw [mm₃, nm₂ a ha (fun hb => by have := hqf' hb; omega), mm₁]
  have hrm₃ : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aOUT nD ∨ aOUT nD + f * t ≤ a) →
      c₃.rmem a = c.rmem a := fun a ha ha' => by
    rw [rm₃, rm₂ a ha (fun hb => by have := hqf' hb; omega), rm₁]
  have hKM₃ : KMem M σ ιv ((R J).T 0) (tripWt M k g S ℓ J) (tripφ S ℓ) c₃ := by
    refine ⟨fun x hx => ?_, fun d => ?_, fun d => ?_⟩
    · have := hL.prim.f_lt x
      rw [hnm₃ _ (Or.inl (by unfold aTP; omega)) (Or.inl (by unfold aTP aRBM; omega))]
      exact h.kmem.tp x hx
    · have := hσ d
      rw [hrm₃ _ (Or.inl (by unfold aWT; omega)) (Or.inl (by unfold aWT aOUT; omega))]
      exact h.kmem.wt d
    · have := hσ d
      rw [hrm₃ _ (Or.inl (by unfold aPH; omega)) (Or.inl (by unfold aPH aOUT; omega))]
      exact h.kmem.ph d
  have hreg₃ : ∀ r, r < 90 → r ≠ 82 → c₃.nreg r = c.nreg r ∧ c₃.rreg r = c.rreg r :=
    fun r hr h82' => by
      rw [n₃ r (by omega) (by omega) (by omega), r₃ r (by omega), (rg₂ r (by omega) h82'
        (by omega)).1, (rg₂ r (by omega) h82' (by omega)).2, n₁ r (Or.inl hr), r₁]
      exact ⟨rfl, rfl⟩
  have u82 : c₃.nreg 82 = kRank fl (J + 1) := by
    rw [n₃ 82 (by omega) (by omega) (by omega), s82, kRank_succ]
  have u100 : c₃.nreg 100 = ιf (M.face (M.rev (g (J % k)))) := by
    rw [n₃ 100 (by omega) (by omega) (by omega), (rg₂ 100 (by omega) (by omega) (by omega)).1,
      n₁ 100 (Or.inr (Or.inl (by omega))), h.r100]
  have u101 : c₃.nreg 101 = ιf (M.face (g (J % k))) := by
    rw [n₃ 101 (by omega) (by omega) (by omega), (rg₂ 101 (by omega) (by omega) (by omega)).1,
      n₁ 101 (Or.inr (Or.inl (by omega))), h.r101]
  have hK0 : (0 : ℝ) ≤ tripK V S ℓ := by exact_mod_cast tripK_nonneg
  have hJk' : (J : ℝ) + 1 ≤ k := by exact_mod_cast ht
  have hLo : ((tripL V S ℓ - 2 * (Fintype.card V * tripW S ℓ) : ℤ) : ℝ) +
      Fintype.card V * (driftK (tripL V S ℓ) (tripW S ℓ) (Fintype.card V) : ℝ) ≤ Lo := by
    have h1 := h.lo
    have e : (tripH0 V S ℓ k : ℝ) = ((tripL V S ℓ - 2 * (Fintype.card V * tripW S ℓ) : ℤ) : ℝ) +
        (k + 1) * ((Fintype.card V + 1) * (tripK V S ℓ : ℝ)) := by
      unfold tripH0 tripTh; push_cast; ring
    have e2 : (driftK (tripL V S ℓ) (tripW S ℓ) (Fintype.card V) : ℝ) = tripK V S ℓ := rfl
    rw [e] at h1; rw [e2]
    have hV0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.2 hJk') (mul_nonneg (by linarith : (0 : ℝ) ≤
      Fintype.card V + 1) hK0)]
  -- the pivot loop
  have hTh' : ((tripL V S ℓ - 2 * (Fintype.card V * tripW S ℓ) : ℤ) : ℝ) = tripTh V S ℓ := rfl
  obtain ⟨T, val, d, m, os₄, c₄, G₄, Lo₄, o₄, hT0, hv0, hrun, hTs, hl₄, ho₄, hS₄, hLo₄, hKM₄, fr₄,
    v100, v101, -, -, hV₄, hLo₄'⟩ := mv_orunAC (P := P) (Hc := Hc) hW (by omega) hB hP H.plane
    (H.tripMoveHyp hR J) H.uniq
    (H.g_not_mem J) (H.rev_g_not_mem J) (fun d hd => tripφ_of_mem hd) (W := tripW S ℓ)
    abs_tripφ_le (fun d hd hr => tripWt_elig J hd hr) (fun d hd => tripWt_inelig J hd)
    (fun d hd => tripL_gt hd) hL hK (A := A) (Wt := Wt) (hwtb J)
    (by rw [hTh']; push_cast; linarith) (by rw [hTh']; push_cast; linarith)
    h.start.1 h.start.2 h.st hLo e₃.wb_right o₃.1.2.lcte hVy hKM₃
    u100 u101 s100 s102 s103
  set RJ : MoveData M S := ⟨T, val, selForest M S (tpar 𝒢 (tripSrc M k g J)) d, d, m⟩ with hRJ
  have hMJ : MoveSpec M k g S ℓ J RJ := ⟨hrun, hTs⟩
  -- the next move
  have hc₄ := o₄.1.2.wb
  have w90 : c₄.nreg 90 = J % k := by rw [(fr₄.1 90 (by omega)).1, n₃ 90 (by omega) (by omega)
    (by omega), (rg₂ 90 (by omega) (by omega) (by omega)).1, p90]
  have w91 : c₄.nreg 91 = (J + 1) % k := by rw [(fr₄.1 91 (by omega)).1, n₃ 91 (by omega)
    (by omega) (by omega), (rg₂ 91 (by omega) (by omega) (by omega)).1, p91]
  have wtl : c₄.rmem (aTL nD) = tripL V S ℓ := by
    rw [fr₄.2.2.1 _ (Or.inl (by unfold aTL; unfold aOUT at hOUT; omega)),
      hrm₃ _ (Or.inl (by unfold aTL; unfold aOUT at hOUT; omega))
        (Or.inl (by unfold aTL aOUT; omega)), h.tl]
  obtain ⟨c₅, G₅, os₅, T', val', o₅, hl₅, ho₅, hS₅, hstart, hr, hpw, hpu, hpx, hKM₅, x100, x101,
    rg₅, out₅, rm₅, nm₅, hV₅⟩ := nx_orunC (P := P) (Hc := Hc) hW (by omega) hB
    (by unfold aOUT at hOUT; omega) hP
    H hR hL hK hG hO hMJ hc₄ o₄.1.2.lcte hS₄ hKM₄ wtl w90 w91 (by rw [v101, u101]) hwtb hTLb
    (by push_cast at hA1 ⊢; linarith [abs_nonneg (tripTh V S ℓ : ℝ)])
    (by
      have e2 : (driftK (tripL V S ℓ) (tripW S ℓ) (Fintype.card V) : ℝ) = tripK V S ℓ := rfl
      have := hLo₄; rw [e2] at this; simp only at this
      have := abs_nonneg (tripTh V S ℓ : ℝ)
      push_cast at hA2 ⊢; nlinarith) hV₄
  -- the next index
  have hc₅ := o₅.1.2.wb
  have w80 : c₅.nreg 80 = J := by
    rw [(rg₅ 80 (by omega)).1, (fr₄.1 80 (by omega)).1, (hreg₃ 80 (by omega) (by omega)).1,
      h.r80]
  obtain ⟨c₆, k₆, e₆, hk₆, z80, n₆, r₆, mm₆, rm₆, out₆⟩ : ∃ c' k', Exec P W
      (block [.constN 92 1, .addN 80 80 92]) c₅ c' k' ∧ k' = 2 ∧ c'.nreg 80 = J + 1 ∧
      (∀ r, r ≠ 80 → r ≠ 92 → c'.nreg r = c₅.nreg r) ∧ c'.rreg = c₅.rreg ∧
      c'.nmem = c₅.nmem ∧ c'.rmem = c₅.rmem ∧ c'.output = c₅.output := by
    exec_block
    · omega
    · config_simp; rw [w80]; omega
    · refine ⟨rfl, by config_simp; rw [w80], fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      config_simp; simp only [upd_other _ _ _ h1, upd_other _ _ _ h2]
  have o₆ : ORunC P W Hc B n _ c₅ _ G₅ c₆ [] G₅ 0 k₆ := ORunC.glue (H := Hc) e₆ o₅.1.2.lcte
    (fun a _ _ => by rw [mm₆, rm₆]; exact ⟨rfl, rfl⟩) (n₆ 151 (by omega) (by omega)) (by rfl)
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq o₆))))
  simp only [List.nil_append, List.append_nil] at o
  -- the data of the next move
  set R' : ℕ → MoveData M S := fun i =>
    if i < J then R i else if i = J then RJ else startData T' val' (g 0) with hR'
  have hlt : ∀ i < J, R' i = R i := fun i hi => by simp [hR', hi]
  have hJ : R' J = RJ := by simp [hR']
  have hJ1 : R' (J + 1) = startData T' val' (g 0) := by simp [hR']
  have hT0' : ∀ i ≤ J, (R' i).T 0 = (R i).T 0 ∧ (R' i).val 0 = (R i).val 0 := by
    intro i hi
    rcases Nat.lt_or_ge i J with h' | h'
    · rw [hlt i h']; exact ⟨rfl, rfl⟩
    · obtain rfl : i = J := by omega
      rw [hJ]; exact ⟨hT0, hv0⟩
  have hrun : (runOpsE n F₀ (hs ++ (os₄ ++ os₅))).1 = (runOpsE n (runOpsE n F os₄).1 os₅).1 := by
    rw [runOpsE_fst_append, runOpsE_fst_append]
  have hrm₆ : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (∀ d : D, a ≠ aWT + σ d) →
      (a < aOUT nD + q * t ∨ aOUT nD + q * t + t ≤ a) → c₆.rmem a = c.rmem a := by
    intro a ha hne ha'
    rw [rm₆, rm₅ a ha hne, fr₄.2.2.1 a ha, rm₃, rm₂ a ha (fun _ => ha'), rm₁]
  have hnm₆ : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → n ≤ a →
      (a < aRBM n k + q * t ∨ aRBM n k + q * t + t ≤ a) → c₆.nmem a = c.nmem a := by
    intro a ha hn ha'
    rw [mm₆, nm₅ a ha hn, fr₄.2.2.2 a ha hn, mm₃, nm₂ a ha (fun _ => ha'), mm₁]
  have htrip : IsTripUpTo M k g S ℓ (J + 1) R' := by
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · rcases Nat.lt_or_ge j J with h' | h'
      · rw [hlt j h']; exact h.trip.move j h'
      · obtain rfl : j = J := by omega
        rw [hJ]; exact hMJ
    · rcases Nat.lt_or_ge j J with h' | h'
      · rw [(hT0' (j + 1) h').1]; exact h.trip.root j h'
      · obtain rfl : j = J := by omega
        rw [hJ1]; exact hr
    · rcases Nat.lt_or_ge j J with h' | h'
      · rw [(hT0' (j + 1) h').1]; exact h.trip.par_dst j h'
      · obtain rfl : j = J := by omega
        rw [hJ1]; exact hpw
    · rcases Nat.lt_or_ge j J with h' | h'
      · rw [(hT0' (j + 1) h').1]; exact h.trip.par_src j h'
      · obtain rfl : j = J := by omega
        rw [hJ1]; exact hpu
    · rcases Nat.lt_or_ge j J with h' | h'
      · intro x hx1 hx2
        rw [(hT0' (j + 1) h').1, hlt j h']; exact h.trip.par_other j h' x hx1 hx2
      · obtain rfl : j = J := by omega
        rw [hJ1, hJ]; exact hpx
  refine ⟨(J + 1, R', Lo₄ - tripK V S ℓ), c₆, os₄ ++ os₅, G₅, o.mono (by
    show _ ≤ tCntM t (fl J) (R' J) _; rw [hJ]; unfold tCntM
    show _ ≤ (if fl J then t else 0) + 2 * (27 * m + 1) + 29 + _; omega)
    (by omega), ⟨by simp only; omega, htrip, ?_, ?_, o₆.1.2.wb, ?_, ?_, ?_, ?_, ?_, z80, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, fun j hj => hlt j hj,
    by show VBnd (A - (Lo₄ - tripK V S ℓ)) n _; simp only [runOpsE_fst_append]; exact hV₅,
    by show Lo₄ - (tripK V S ℓ : ℝ) ≤ _; linarith⟩
  · show StartOK M k g S ℓ (J + 1) ((R' (J + 1)).T 0) ((R' (J + 1)).val 0)
    rw [hJ1]; exact hstart
  · rw [runOpsE_fst_append]; exact o.1.2.lcte
  · show Stored M n ιv ιg ιf ιe (tripφ S ℓ) (M.face (g ((J + 1) % k))) (Lo₄ - tripK V S ℓ)
      (runOpsE n F₀ (hs ++ (os₄ ++ os₅))).1 ((R' (J + 1)).T 0) ((R' (J + 1)).val 0)
    rw [hJ1, hrun]; exact hS₅
  · show (tripH0 V S ℓ k : ℝ) - ((J + 1 : ℕ) : ℝ) * _ ≤ Lo₄ - _
    have h1 := h.lo
    have e2 : (driftK (tripL V S ℓ) (tripW S ℓ) (Fintype.card V) : ℝ) = tripK V S ℓ := rfl
    rw [e2] at hLo₄
    push_cast
    nlinarith
  · rw [runOpsE_append, h.out, runOpsE_append, ho₄]; exact ho₅
  · show (hs ++ (os₄ ++ os₅)).length ≤ ∑ j ∈ range (J + 1),
      (16 * (R' j).m + 18 + 4 * (tripΔ M k g S j).card)
    rw [sum_range_succ, hJ, sum_congr rfl fun i hi => by rw [hlt i (mem_range.1 hi)]]
    have := h.len
    simp only at this
    have hm : RJ.m = m := rfl
    simp only [List.length_append, hl₄, hm]
    omega
  · show KMem M σ ιv ((R' (J + 1)).T 0) _ _ c₆
    rw [hJ1]
    exact ⟨fun x hx => by rw [mm₆]; exact hKM₅.tp x hx, fun d => by rw [rm₆]; exact hKM₅.wt d,
      fun d => by rw [rm₆]; exact hKM₅.ph d⟩
  · rw [n₆ 81 (by omega) (by omega), (rg₅ 81 (by omega)).1, (fr₄.1 81 (by omega)).1,
      (hreg₃ 81 (by omega) (by omega)).1, h.r81]
  · rw [n₆ 82 (by omega) (by omega), (rg₅ 82 (by omega)).1, (fr₄.1 82 (by omega)).1, u82]
  · rw [n₆ 100 (by omega) (by omega), x100]
  · rw [n₆ 101 (by omega) (by omega), x101]
  · rw [hrm₆ (aTL nD) (Or.inl (by unfold aTL; unfold aOUT at hOUT; omega))
      (fun d h' => by have := hσ d; unfold aTL aWT at h'; omega)
      (Or.inl (by unfold aTL aOUT; omega)), h.tl]
  · rw [hrm₆ (aTH nD) (Or.inl (by unfold aTH; unfold aOUT at hOUT; omega))
      (fun d h' => by have := hσ d; unfold aTH aWT at h'; omega)
      (Or.inl (by unfold aTH aOUT; omega)), h.th]
  · intro j hj
    rw [hnm₆ _ (Or.inl (by unfold aMK aRBM at *; omega)) (by unfold aMK; omega)
      (Or.inl (by unfold aMK aRBM; omega))]
    exact h.flags j hj
  · intro j hj hfj i hi
    simp only at hj
    have hjk : kRank fl j * t + t ≤ f * t := by
      have := Nat.mul_le_mul_right t (kRank_succ_le fl (show j < k by omega) hfj)
      rw [Nat.add_mul, one_mul] at this
      exact this
    have hout : aOUT nD + kRank fl j * t + i < B := by omega
    have hrb : aRBM n k + kRank fl j * t + i < B := by omega
    rcases Nat.lt_or_ge j J with h' | h'
    · have := Nat.mul_le_mul_right t (kRank_succ_le fl h' hfj)
      rw [Nat.add_mul, one_mul, ← hq] at this
      have e : kOutM nD n k t c₆ (kRank fl j) i = kOutM nD n k t c (kRank fl j) i := by
        unfold kOutM
        rw [hrm₆ _ (Or.inl hout) (fun d h'' => by have := hσ d; unfold aOUT aWT at h''; omega)
          (Or.inl (by omega)), hnm₆ _ (Or.inl hrb) (by unfold aRBM; omega) (Or.inl (by omega))]
      rw [e]
      exact h.dist j h' hfj i hi
    · obtain rfl : j = J := by omega
      have hS0 := h.st
      rw [← hT0] at hS0
      have hnr := hX.nr i hi
      have hb : c₆.nmem (aRBM n k + kRank fl j * t + i) =
          if Reach 𝒢 (M.tail (g 0)) (X i) then 1 else 0 := by
        rw [mm₆, nm₅ _ (Or.inl hrb) (by unfold aRBM; omega),
          fr₄.2.2.2 _ (Or.inl hrb) (by unfold aRBM; omega), mm₃, (q₂ hfj i hi).2]
      unfold kOutM odist
      rw [hb, rm₆, rm₅ _ (Or.inl hout)
        (fun d h'' => by have := hσ d; unfold aOUT aWT at h''; omega),
        fr₄.2.2.1 _ (Or.inl hout), rm₃, (q₂ hfj i hi).1]
      by_cases hr : Reach 𝒢 (M.tail (g 0)) (X i)
      · have hr' := (reach_tgt H hR hnr j).2 hr
        simp only [hr, hr', ↓reduceIte, Option.map_some]
        exact congrArg some (stored_label H hR hL hMJ hS0 hr')
      · have hr' : ¬ Reach 𝒢 (tripSrc M k g j) (X i) := fun h => hr ((reach_tgt H hR hnr j).1 h)
        simp [hr, hr']
  · rw [out₆, out₅, fr₄.2.1, out₃, out₂, out₁, h.output]
  · intro r hr
    rw [n₆ r (by omega) (by omega), r₆, (rg₅ r (by omega)).1, (rg₅ r (by omega)).2,
      (fr₄.1 r (by omega)).1, (fr₄.1 r (by omega)).2, (hreg₃ r (by omega) (by omega)).1,
      (hreg₃ r (by omega) (by omega)).2]
    exact h.regs r hr

theorem tLoopM_orunC (hW : B + 16 * (n + 1) ≤ W) (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ W)
    (hB : n + 2 * nD ≤ B) (hOUT : aOUT nD + kRank fl k * t ≤ B)
    (hRB : aRBM n k + kRank fl k * t ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W)
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    (hX : KTgt M k g S ℓ nD n ιv t X P) {F₀ : Forest} {c₀ : Config} {R₀ : ℕ → MoveData M S}
    {Lo₀ : ℝ} {G : List VT} {c : Config}
    (h : TInvM M k g S ℓ σ n ιv ιg ιf ιe t X fl B W F₀ c₀ (0, R₀, Lo₀) [] G c) {A Wt : ℝ}
    (hwtb : ∀ j' d, |(tripWt M k g S ℓ j' d : ℝ)| ≤ Wt) (hTLb : |(tripL V S ℓ : ℝ)| ≤ Wt)
    (hA1 : Wt + tripW S ℓ + 2 * (Fintype.card V * tripW S ℓ) + |(tripTh V S ℓ : ℝ)| ≤
      A - tripH0 V S ℓ k)
    (hA2 : 30 * (A - tripTh V S ℓ) + 12 * tripK V S ℓ + 8 * (Wt + tripW S ℓ) ≤ Hc)
    (hV₀ : VBnd (A - Lo₀) n F₀) (hLo₀ : Lo₀ ≤ tripH0 V S ℓ k) :
    ∃ (R : ℕ → MoveData M S) (Lo : ℝ) (os : List EOp) (c' : Config) (G' : List VT),
      ORunC P W Hc B n (tLoopMS B nD n k t) c F₀ G c' os G'
        (∑ j ∈ range k, tCntM t (fl j) (R j) (tripΔ M k g S j).card)
        (∑ j ∈ range k, (14 * (if fl j then t else 0) + 190 + 30 * (tripΔ M k g S j).card) +
          2) ∧
      TInvM M k g S ℓ σ n ιv ιg ιf ιe t X fl B W F₀ c₀ (k, R, Lo) os G' c' ∧
      VBnd (A - Lo) n (runOpsE n F₀ os).1 ∧ Lo ≤ tripH0 V S ℓ k := by
  classical
  set cnt : ℕ × (ℕ → MoveData M S) × ℝ → ℕ := fun y =>
    ∑ j ∈ range y.1, tCntM t (fl j) (y.2.1 j) (tripΔ M k g S j).card with hcnt
  set ext : ℕ × (ℕ → MoveData M S) × ℝ → ℕ := fun y =>
    ∑ j ∈ Ico y.1 k, (14 * (if fl j then t else 0) + 190 + 30 * (tripΔ M k g S j).card)
    with hext
  obtain ⟨y, os, c', G', hrun, hI, ht, -, -⟩ := ORunC.whileLtN (P := P) (W := W) (H := Hc) (B := B)
    (n := n) (a := 80) (b := 81) (body := tBodyMS B nD n k t) F₀
    (fun y hs G₁ c₁ => TInvM M k g S ℓ σ n ιv ιg ιf ιe t X fl B W F₀ c₀ y hs G₁ c₁ ∧
      VBnd (A - y.2.2) n (runOpsE n F₀ hs).1 ∧ y.2.2 ≤ tripH0 V S ℓ k) cnt ext
    (fun _ _ _ _ h' _ => ⟨h'.1.lcte, h'.1.wb⟩)
    (fun y hs G₁ c₁ hh _ ht => by
      obtain ⟨h', hVy, hLy⟩ := hh
      have hJ : y.1 < k := by rw [h'.r80, h'.r81] at ht; exact ht
      obtain ⟨y', c₂, os, G₂, o, hI', hy1, hagree, hVy', hLy'⟩ :=
        tBodyM_orunC hW hWa hB hOUT hRB hP H hR hL hK hG hO hX y hs G₁ c₁ h' hJ hwtb hTLb hA1 hA2
          hVy hLy
      refine ⟨y', c₂, os, G₂, _, _, o, ⟨hI', hVy', hLy'⟩, ?_, ?_⟩
      · simp only [hcnt, hy1, sum_range_succ]
        rw [sum_congr rfl fun j hj => by rw [hagree j (mem_range.1 hj)]]
      · simp only [hext, hy1]
        rw [sum_eq_sum_Ico_succ_bot hJ]
        omega)
    (x := (0, R₀, Lo₀)) (hs := []) ⟨h, hV₀, hLo₀⟩ trivial
  obtain ⟨hI, hVf, hLf⟩ := hI
  have hk : y.1 = k := by
    have := hI.jle; rw [hI.r80, hI.r81] at ht; omega
  obtain ⟨J, R, Lo⟩ := y
  simp only at hk
  subst hk
  refine ⟨R, Lo, os, c', G', hrun.mono (by simp [hcnt]) ?_, by simpa using hI,
    by simpa using hVf, by simpa using hLf⟩
  simp only [hext, Ico_self, sum_empty, Nat.sub_zero]
  rw [range_eq_Ico]

end

end Klein

end PlanarFlow
