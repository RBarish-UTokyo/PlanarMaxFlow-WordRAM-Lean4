module

public import PlanarFlow.Klein.ProgKleinMC
public import PlanarFlow.Klein.ModNat

/-!
# Klein's (unmasked) program: every real comparison of every run is bounded

`PlanarFlow/Klein/ProgTripMaskC.lean` and `PlanarFlow/Klein/ProgKleinMC.lean` prove that the runs
of the masked program `kleinProgM` are compare-bounded; this file does the same for the program
`kleinProg` of `PlanarFlow/Klein/ProgTrip.lean`, which answers the `t` queries at every move:

* `tBody_orunC`, `tLoop_orunC`: the proofs of `tBody_orun`, `tLoop_orun` replayed as runs whose
  real comparisons are bounded (`DynTree.ORunC`), keeping the bound `A - Lo` of the values of
  the forest (as `tBodyM_orunC`, `tLoopM_orunC`);
* `kleinS_cmpOK`: **every run of `kleinS` from the initialised structure is compare-bounded by
  `Hc`** when `kleinHI ≤ Hc` (the initialisation by `in_orunC`);
* `kleinProg_cmpOK`: **the same for the whole program `kleinProg`** from a configuration meeting
  the preconditions of `klein_exec`.
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
  {X : ℕ → V}

local notation "𝒢" => pieceGraph M S ℓ

section
variable {P : Input} {W B Hc : ℕ}

set_option maxHeartbeats 800000 in
theorem tBody_orunC (hW : B + 16 * (n + 1) ≤ W) (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ W)
    (hB : n + 2 * nD ≤ B) (hOUT : aOUT nD + k * t ≤ B) (hRB : aRB n + k * t ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ W)
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    (hX : KTgt M k g S ℓ nD n ιv t X P) {F₀ : Forest} {c₀ : Config}
    (y : ℕ × (ℕ → MoveData M S) × ℝ) (hs : List EOp) (G : List VT) (c : Config)
    (h : TInv M k g S ℓ σ n ιv ιg ιf ιe t X B W F₀ c₀ y hs G c) (ht : y.1 < k) {A Wt : ℝ}
    (hwtb : ∀ j' d, |(tripWt M k g S ℓ j' d : ℝ)| ≤ Wt) (hTLb : |(tripL V S ℓ : ℝ)| ≤ Wt)
    (hA1 : Wt + tripW S ℓ + 2 * (Fintype.card V * tripW S ℓ) + |(tripTh V S ℓ : ℝ)| ≤
      A - tripH0 V S ℓ k)
    (hA2 : 30 * (A - tripTh V S ℓ) + 12 * tripK V S ℓ + 8 * (Wt + tripW S ℓ) ≤ Hc)
    (hVy : VBnd (A - y.2.2) n (runOpsE n F₀ hs).1) (hLoy : y.2.2 ≤ tripH0 V S ℓ k) :
    ∃ (y' : ℕ × (ℕ → MoveData M S) × ℝ) (c' : Config) (os : List EOp) (G' : List VT),
      ORunC P W Hc B n (tBodyS B nD n k t) c (runOpsE n F₀ hs).1 G c' os G'
        (tCnt t (y'.2.1 y.1) (tripΔ M k g S y.1).card)
        (14 * t + 174 + 30 * (tripΔ M k g S y.1).card) ∧
      TInv M k g S ℓ σ n ιv ιg ιf ιe t X B W F₀ c₀ y' (hs ++ os) G' c' ∧ y'.1 = y.1 + 1 ∧
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
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hk := H.two_le_k
  have hJk : J * t ≤ k * t := Nat.mul_le_mul_right _ ht.le
  have hJk2 : J * t + t ≤ k * t := by
    have := Nat.mul_le_mul_right t (show J + 1 ≤ k by omega)
    rw [Nat.add_mul, one_mul] at this; exact this
  have hc := h.wb
  have hBW : B ≤ W := by omega
  have h80 : c.nreg 80 = J := h.r80
  -- the registers of the move
  obtain ⟨c₁, k₁, e₁, hk₁, p90, p91, p104, p105, p106, p109, n₁, r₁, mm₁, rm₁, out₁⟩ : ∃ c' k',
      Exec P W (block [.modN 90 80 81, .constN 92 1, .addN 91 80 92, .modN 91 91 81,
        .constN 105 t, .mulN 93 80 105, .constN 106 (aOUT nD), .addN 106 106 93,
        .constN 109 (aRB n), .addN 109 109 93, .constN 104 0]) c c' k' ∧ k' = 11 ∧
      c'.nreg 90 = J % k ∧ c'.nreg 91 = (J + 1) % k ∧
      c'.nreg 104 = 0 ∧ c'.nreg 105 = t ∧ c'.nreg 106 = aOUT nD + J * t ∧
      c'.nreg 109 = aRB n + J * t ∧
      (∀ r, (r < 90 ∨ (94 ≤ r ∧ r < 104) ∨ 110 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    all_goals try (first
      | omega
      | (config_simp; rw [h80]; omega))
    refine ⟨rfl, ?_, ?_, by config_simp, by config_simp, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl,
      rfl⟩
    · config_simp; rw [h80, h.r81]
    · config_simp; rw [h80, h.r81]
    · config_simp; rw [h80]
    · config_simp; rw [h80]
    · config_simp
      simp only [upd_other _ _ _ (show r ≠ 105 by omega), upd_other _ _ _ (show r ≠ 104 by omega),
        upd_other _ _ _ (show r ≠ 106 by omega), upd_other _ _ _ (show r ≠ 93 by omega),
        upd_other _ _ _ (show r ≠ 91 by omega), upd_other _ _ _ (show r ≠ 92 by omega),
        upd_other _ _ _ (show r ≠ 90 by omega), upd_other _ _ _ (show r ≠ 109 by omega)]
  have o₁ : ORunC P W Hc B n _ c F G c₁ [] G 0 k₁ := ORunC.glue (H := Hc) e₁ h.lcte
    (fun a _ _ => by rw [mm₁, rm₁]; exact ⟨rfl, rfl⟩) (n₁ 151 (by omega)) (by rfl)
  -- the answers at the targets
  obtain ⟨c₂, G₂, o₂, q₂, rg₂, out₂, nm₂, rm₂, -⟩ := qry_orunC (P := P) (H := Hc) (k := k) (X := X)
    (xb := fun i => if Reach 𝒢 (M.tail (g 0)) (X i) then 1 else 0) hW
    (by unfold iXT; omega) hP hL hX.xn hX.xr (base := aOUT nD + J * t)
    (rbase := aRB n + J * t) (by omega) (by omega) e₁.wb_right o₁.1.2.lcte p104 p105
    p106 p109 hVy (by have := abs_nonneg (tripTh V S ℓ : ℝ); nlinarith)
  -- the threshold
  have hc₂ := o₂.1.2.wb
  have hth₂ : c₂.rmem (aTH nD) = tripTh V S ℓ := by
    rw [rm₂ _ (Or.inl (by unfold aTH; unfold aOUT at hOUT; omega))
      (Or.inl (by unfold aTH aOUT; omega)), rm₁, h.th]
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
    (fun a _ _ => by rw [mm₃, rm₃]; exact ⟨rfl, rfl⟩) (n₃ 151 (by omega) (by omega) (by omega))
    (by rfl)
  -- the memory and the registers at the start of the pivot loop
  have hnm₃ : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aRB n ∨ aRB n + k * t ≤ a) →
      c₃.nmem a = c.nmem a := fun a ha ha' => by
    rw [mm₃, nm₂ a ha (by omega), mm₁]
  have hrm₃ : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aOUT nD ∨ aOUT nD + k * t ≤ a) →
      c₃.rmem a = c.rmem a := fun a ha ha' => by
    rw [rm₃, rm₂ a ha (by omega), rm₁]
  have hKM₃ : KMem M σ ιv ((R J).T 0) (tripWt M k g S ℓ J) (tripφ S ℓ) c₃ := by
    refine ⟨fun x hx => ?_, fun d => ?_, fun d => ?_⟩
    · have := hL.prim.f_lt x
      rw [hnm₃ _ (Or.inl (by unfold aTP; omega)) (Or.inl (by unfold aTP aRB; omega))]
      exact h.kmem.tp x hx
    · have := hσ d
      rw [hrm₃ _ (Or.inl (by unfold aWT; omega)) (Or.inl (by unfold aWT aOUT; omega))]
      exact h.kmem.wt d
    · have := hσ d
      rw [hrm₃ _ (Or.inl (by unfold aPH; omega)) (Or.inl (by unfold aPH aOUT; omega))]
      exact h.kmem.ph d
  have hreg₃ : ∀ r, r < 90 → c₃.nreg r = c.nreg r ∧ c₃.rreg r = c.rreg r := fun r hr => by
    rw [n₃ r (by omega) (by omega) (by omega), r₃ r (by omega), (rg₂ r (by omega)).1,
      (rg₂ r (by omega)).2, n₁ r (Or.inl hr), r₁]; exact ⟨rfl, rfl⟩
  have u100 : c₃.nreg 100 = ιf (M.face (M.rev (g (J % k)))) := by
    rw [n₃ 100 (by omega) (by omega) (by omega), (rg₂ 100 (by omega)).1,
      n₁ 100 (Or.inr (Or.inl (by omega))), h.r100]
  have u101 : c₃.nreg 101 = ιf (M.face (g (J % k))) := by
    rw [n₃ 101 (by omega) (by omega) (by omega), (rg₂ 101 (by omega)).1,
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
    (by omega), (rg₂ 90 (by omega)).1, p90]
  have w91 : c₄.nreg 91 = (J + 1) % k := by rw [(fr₄.1 91 (by omega)).1, n₃ 91 (by omega)
    (by omega) (by omega), (rg₂ 91 (by omega)).1, p91]
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
    rw [(rg₅ 80 (by omega)).1, (fr₄.1 80 (by omega)).1, (hreg₃ 80 (by omega)).1, h.r80]
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
  have hK0 : (0 : ℝ) ≤ tripK V S ℓ := by exact_mod_cast tripK_nonneg
  have hrun : (runOpsE n F₀ (hs ++ (os₄ ++ os₅))).1 = (runOpsE n (runOpsE n F os₄).1 os₅).1 := by
    rw [runOpsE_fst_append, runOpsE_fst_append]
  have hrm₆ : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (∀ d : D, a ≠ aWT + σ d) →
      (a < aOUT nD + J * t ∨ aOUT nD + J * t + t ≤ a) → c₆.rmem a = c.rmem a := by
    intro a ha hne ha'
    rw [rm₆, rm₅ a ha hne, fr₄.2.2.1 a ha, rm₃, rm₂ a ha ha', rm₁]
  have hnm₆ : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → n ≤ a →
      (a < aRB n + J * t ∨ aRB n + J * t + t ≤ a) → c₆.nmem a = c.nmem a := by
    intro a ha hn ha'
    rw [mm₆, nm₅ a ha hn, fr₄.2.2.2 a ha hn, mm₃, nm₂ a ha ha', mm₁]
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
    show _ ≤ tCnt t (R' J) _; rw [hJ]; unfold tCnt; show _ ≤ t + 2 * (27 * m + 1) + 29 + _; omega)
    (by omega), ⟨by simp only; omega, htrip, ?_, ?_, o₆.1.2.wb, ?_, ?_, ?_, ?_, ?_, z80, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩, rfl, fun j hj => hlt j hj,
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
      (hreg₃ 81 (by omega)).1, h.r81]
  · rw [n₆ 100 (by omega) (by omega), x100]
  · rw [n₆ 101 (by omega) (by omega), x101]
  · rw [hrm₆ (aTL nD) (Or.inl (by unfold aTL; unfold aOUT at hOUT; omega))
      (fun d h' => by have := hσ d; unfold aTL aWT at h'; omega)
      (Or.inl (by unfold aTL aOUT; omega)), h.tl]
  · rw [hrm₆ (aTH nD) (Or.inl (by unfold aTH; unfold aOUT at hOUT; omega))
      (fun d h' => by have := hσ d; unfold aTH aWT at h'; omega)
      (Or.inl (by unfold aTH aOUT; omega)), h.th]
  · intro j hj i hi
    simp only at hj
    have hjk : j * t + i < k * t := by
      have := Nat.mul_le_mul_right t (show j + 1 ≤ k by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
    have hout : aOUT nD + j * t + i < B := by omega
    have hrb : aRB n + j * t + i < B := by omega
    rcases Nat.lt_or_ge j J with h' | h'
    · have := Nat.mul_le_mul_right t (show j + 1 ≤ J by omega)
      rw [Nat.add_mul, one_mul] at this
      have e : kOut nD n t c₆ j i = kOut nD n t c j i := by
        unfold kOut
        rw [hrm₆ _ (Or.inl hout) (fun d h'' => by have := hσ d; unfold aOUT aWT at h''; omega)
          (Or.inl (by omega)), hnm₆ _ (Or.inl hrb) (by unfold aRB; omega) (Or.inl (by omega))]
      rw [e]
      exact h.dist j h' i hi
    · obtain rfl : j = J := by omega
      have hS0 := h.st
      rw [← hT0] at hS0
      have hnr := hX.nr i hi
      have hb : c₆.nmem (aRB n + j * t + i) =
          if Reach 𝒢 (M.tail (g 0)) (X i) then 1 else 0 := by
        rw [mm₆, nm₅ _ (Or.inl hrb) (by unfold aRB; omega),
          fr₄.2.2.2 _ (Or.inl hrb) (by unfold aRB; omega), mm₃, (q₂ i hi).2]
      unfold kOut odist
      rw [hb, rm₆, rm₅ _ (Or.inl hout)
        (fun d h'' => by have := hσ d; unfold aOUT aWT at h''; omega),
        fr₄.2.2.1 _ (Or.inl hout), rm₃, (q₂ i hi).1]
      by_cases hr : Reach 𝒢 (M.tail (g 0)) (X i)
      · have hr' := (reach_tgt H hR hnr j).2 hr
        simp only [hr, hr', ↓reduceIte, Option.map_some]
        exact congrArg some (stored_label H hR hL hMJ hS0 hr')
      · have hr' : ¬ Reach 𝒢 (tripSrc M k g j) (X i) := fun h => hr ((reach_tgt H hR hnr j).1 h)
        simp [hr, hr']
  · rw [out₆, out₅, fr₄.2.1, out₃, out₂, out₁, h.output]
  · intro r hr
    rw [n₆ r (by omega) (by omega), r₆, (rg₅ r (by omega)).1, (rg₅ r (by omega)).2,
      (fr₄.1 r (by omega)).1, (fr₄.1 r (by omega)).2, (hreg₃ r (by omega)).1,
      (hreg₃ r (by omega)).2]
    exact h.regs r hr

/-- `tLoop_orun` with bounded comparisons (as `tLoopM_orunC`). -/
theorem tLoop_orunC (hW : B + 16 * (n + 1) ≤ W) (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ W)
    (hB : n + 2 * nD ≤ B) (hOUT : aOUT nD + k * t ≤ B) (hRB : aRB n + k * t ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ W)
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    (hX : KTgt M k g S ℓ nD n ιv t X P) {F₀ : Forest} {c₀ : Config} {R₀ : ℕ → MoveData M S}
    {Lo₀ : ℝ} {G : List VT} {c : Config}
    (h : TInv M k g S ℓ σ n ιv ιg ιf ιe t X B W F₀ c₀ (0, R₀, Lo₀) [] G c) {A Wt : ℝ}
    (hwtb : ∀ j' d, |(tripWt M k g S ℓ j' d : ℝ)| ≤ Wt) (hTLb : |(tripL V S ℓ : ℝ)| ≤ Wt)
    (hA1 : Wt + tripW S ℓ + 2 * (Fintype.card V * tripW S ℓ) + |(tripTh V S ℓ : ℝ)| ≤
      A - tripH0 V S ℓ k)
    (hA2 : 30 * (A - tripTh V S ℓ) + 12 * tripK V S ℓ + 8 * (Wt + tripW S ℓ) ≤ Hc)
    (hV₀ : VBnd (A - Lo₀) n F₀) (hLo₀ : Lo₀ ≤ tripH0 V S ℓ k) :
    ∃ (R : ℕ → MoveData M S) (Lo : ℝ) (os : List EOp) (c' : Config) (G' : List VT),
      ORunC P W Hc B n (tLoopS B nD n k t) c F₀ G c' os G'
        (∑ j ∈ range k, tCnt t (R j) (tripΔ M k g S j).card)
        (k * (14 * t + 182) + 30 * ∑ j ∈ range k, (tripΔ M k g S j).card + 2) ∧
      TInv M k g S ℓ σ n ιv ιg ιf ιe t X B W F₀ c₀ (k, R, Lo) os G' c' := by
  classical
  set cnt : ℕ × (ℕ → MoveData M S) × ℝ → ℕ := fun y =>
    ∑ j ∈ range y.1, tCnt t (y.2.1 j) (tripΔ M k g S j).card with hcnt
  set ext : ℕ × (ℕ → MoveData M S) × ℝ → ℕ := fun y =>
    (k - y.1) * (14 * t + 182) + 30 * ∑ j ∈ Ico y.1 k, (tripΔ M k g S j).card with hext
  obtain ⟨y, os, c', G', hrun, hI, ht, -, -⟩ := ORunC.whileLtN (P := P) (W := W) (H := Hc)
    (B := B) (n := n) (a := 80) (b := 81) (body := tBodyS B nD n k t) F₀
    (fun y hs G₁ c₁ => TInv M k g S ℓ σ n ιv ιg ιf ιe t X B W F₀ c₀ y hs G₁ c₁ ∧
      VBnd (A - y.2.2) n (runOpsE n F₀ hs).1 ∧ y.2.2 ≤ tripH0 V S ℓ k) cnt ext
    (fun _ _ _ _ h' _ => ⟨h'.1.lcte, h'.1.wb⟩)
    (fun y hs G₁ c₁ hh _ ht => by
      obtain ⟨h', hVy, hLy⟩ := hh
      have hJ : y.1 < k := by rw [h'.r80, h'.r81] at ht; exact ht
      obtain ⟨y', c₂, os, G₂, o, hI', hy1, hagree, hVy', hLy'⟩ :=
        tBody_orunC hW hWa hB hOUT hRB hP H hR hL hK hG hO hX y hs G₁ c₁ h' hJ hwtb hTLb hA1 hA2
          hVy hLy
      refine ⟨y', c₂, os, G₂, _, _, o, ⟨hI', hVy', hLy'⟩, ?_, ?_⟩
      · simp only [hcnt, hy1, sum_range_succ]
        rw [sum_congr rfl fun j hj => by rw [hagree j (mem_range.1 hj)]]
      · simp only [hext, hy1]
        rw [sum_eq_sum_Ico_succ_bot hJ]
        have : k - y.1 = k - (y.1 + 1) + 1 := by omega
        rw [this]
        ring_nf
        omega)
    (x := (0, R₀, Lo₀)) (hs := []) ⟨h, hV₀, hLo₀⟩ trivial
  obtain ⟨hI, -, -⟩ := hI
  have hk : y.1 = k := by
    have := hI.jle; rw [hI.r80, hI.r81] at ht; omega
  obtain ⟨J, R, Lo⟩ := y
  simp only at hk
  subst hk
  refine ⟨R, Lo, os, c', G', hrun.mono (by simp [hcnt]) ?_, by simpa using hI⟩
  simp only [hext, Nat.sub_zero, Nat.sub_self, zero_mul, Ico_self, sum_empty, mul_zero,
    add_zero]
  rw [range_eq_Ico]

/-- **Every run of `kleinS` from the initialised structure is compare-bounded by `Hc`**, for
`kleinHI ≤ Hc`, under the preconditions of `kleinS_orun`. -/
theorem kleinS_cmpOK (hW : B + 16 * (n + 1) ≤ W) (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ W)
    (hB : n + 2 * nD ≤ B) (hOUT : aOUT nD + k * t ≤ B) (hRB : aRB n + k * t ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ W)
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    (hX : KTgt M k g S ℓ nD n ιv t X P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F}
    (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x))
    (hCr : C.root = M.face (g 0))
    (hT : Compat T (tripSrc M k g 0) (tripDst M k g 0) (g (0 % k)) (tpar 𝒢 (tripSrc M k g 0)))
    {c : Config} (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n (Forest.init n) G c)
    (hwt : ∀ d, c.rmem (aWT + σ d) = tripWt M k g S ℓ 0 d)
    (hph : ∀ d, c.rmem (aPH nD + σ d) = tripφ S ℓ d) (htl : c.rmem (aTL nD) = tripL V S ℓ)
    (hth : c.rmem (aTH nD) = tripTh V S ℓ) (hh0 : c.rmem (aH0 nD) = tripH0 V S ℓ k)
    (hHc : kleinHI V F S ℓ k ≤ Hc) :
    ModNat.CmpOK P W Hc (kleinS B nD n k t) c := by
  classical
  have hk := H.two_le_k
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hW0 : (0 : ℝ) ≤ tripW S ℓ := by exact_mod_cast tripW_nonneg
  have hL0 : (0 : ℝ) ≤ tripL V S ℓ := by exact_mod_cast tripL_nonneg
  have hK0 : (0 : ℝ) ≤ tripK V S ℓ := by exact_mod_cast tripK_nonneg
  have hv0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hvw : 0 ≤ (Fintype.card V : ℝ) * tripW S ℓ := by positivity
  have hZ0 := kleinZ_nonneg (V := V) (F := F) (S := S) (ℓ := ℓ) (k := k)
  have hAT := kleinA_sub_tripTh_nonneg (V := V) (S := S) (ℓ := ℓ) (k := k)
  have hHZ : 2 * kleinZ V F S ℓ k ≤ (Hc : ℝ) := by
    unfold kleinHI kleinAI at hHc; linarith
  have hZ : zsum (treeOpsL T ιv ιg (tripφ S ℓ) vs ts ++ cotOpsL C ιf ιe
      (fun d => tripWt M k g S ℓ 0 d + T.psum (tripφ S ℓ) (M.tail d) -
        T.psum (tripφ S ℓ) (M.head d)) (tripH0 V S ℓ k) fs cs) ≤ kleinZ V F S ℓ k := by
    refine zsum_init_le T C _ _ _ hI.oT hI.oC hW0 (by positivity) (fun d => ?_) (fun d => ?_)
    · exact_mod_cast abs_tripφ_le d
    · have h1 := abs_le.1 (abs_tripWt_le (M := M) (k := k) (g := g) (S := S) (ℓ := ℓ) 0 d)
      have h2 := abs_le.1 (abs_psum_le_mul T (abs_tripφ_le (S := S) (ℓ := ℓ)) (M.tail d))
      have h3 := abs_le.1 (abs_psum_le_mul T (abs_tripφ_le (S := S) (ℓ := ℓ)) (M.head d))
      have h : |tripWt M k g S ℓ 0 d + T.psum (tripφ S ℓ) (M.tail d) -
          T.psum (tripφ S ℓ) (M.head d)| ≤
          tripL V S ℓ + 2 * ((Fintype.card V : ℤ) * tripW S ℓ) :=
        abs_le.2 ⟨by linarith, by linarith⟩
      have h' := (Int.cast_le (R := ℝ)).2 h
      push_cast at h' ⊢
      exact h'
  -- the initial trees
  obtain ⟨c₁, G₁, os₁, o₁, -, ho₁, hS₁, hKM₁, -, out₁, -, rm₁, hV₁⟩ := in_orunC (H := Hc) hW
    (by omega) hB (by unfold aOUT at hOUT; omega) hP hL hK hI hoff hc hS hwt hph hh0 hHZ hZ
  set F₀ := (runOpsE n (Forest.init n) os₁).1 with hF₀
  -- the registers of the loop
  have hg0 : P.data.getD (iGB nD n) 0 = σ (g 0) := by simpa using hG 0 (by omega)
  have hc₁ := o₁.1.2.wb
  have h0 := hσ (g 0)
  have h0' := hσ (M.rev (g 0))
  obtain ⟨c₂, k₂, e₂, hk₂, p80, p81, p100, p101, n₂, r₂, mm₂, rm₂, out₂⟩ : ∃ c' k', Exec P W
      (block (setupI nD n k)) c₁ c' k' ∧ k' = 13 ∧ c'.nreg 80 = 0 ∧ c'.nreg 81 = k ∧
      c'.nreg 100 = ιf (M.face (M.rev (g 0))) ∧ c'.nreg 101 = ιf (M.face (g 0)) ∧
      (∀ r, r ≠ 80 → r ≠ 81 → r ≠ 85 → r ≠ 86 → r ≠ 100 → r ≠ 101 → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.nmem = c₁.nmem ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
    unfold setupI
    exec_block
    all_goals try (first
      | exact hP _
      | omega
      | (simp only [iGB, iNF, iRV]; omega)
      | (config_simp; rw [hg0]; simp only [iNF, iRV]; omega)
      | (config_simp; rw [hg0, hK.rv]; simp only [iNF]; omega))
    refine ⟨rfl, by config_simp, by config_simp, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => ?_, rfl, rfl,
      rfl, rfl⟩
    · config_simp; rw [hg0, hK.rv, hK.nf]
    · config_simp; rw [hg0, hK.nf]
    · config_simp
      simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3, upd_other _ _ _ h4,
        upd_other _ _ _ h5, upd_other _ _ _ h6]
  have o₂ : ORunC P W Hc B n _ c₁ F₀ G₁ c₂ [] G₁ 0 k₂ := ORunC.glue e₂ o₁.1.2.lcte
    (fun a _ _ => by rw [mm₂, rm₂]; exact ⟨rfl, rfl⟩)
    (n₂ 151 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) (by rfl)
  -- the invariant at the first move
  have hI₀ : TInv M k g S ℓ σ n ιv ιg ιf ιe t X B W F₀ c₂
      (0, fun _ => startData T (fun d => tripWt M k g S ℓ 0 d + T.psum (tripφ S ℓ) (M.tail d) -
        T.psum (tripφ S ℓ) (M.head d)) (g 0), (tripH0 V S ℓ k : ℝ)) [] G₁ c₂ := by
    refine ⟨Nat.zero_le _, ⟨fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega)⟩, ⟨hT, fun d _ => rfl⟩, o₂.1.2.lcte, e₂.wb_right, ?_,
      by simp, rfl, by simp, ?_, p80, p81, ?_, ?_, ?_, ?_,
      fun j hj => absurd hj (by omega), rfl, fun _ _ => ⟨rfl, rfl⟩⟩
    · simp only [Nat.zero_mod]; rw [← hCr]; exact hS₁
    · exact ⟨fun x hx => by rw [mm₂]; exact hKM₁.tp x hx, fun d => by rw [rm₂]; exact hKM₁.wt d,
        fun d => by rw [rm₂]; exact hKM₁.ph d⟩
    · simp only [Nat.zero_mod]; exact p100
    · simp only [Nat.zero_mod]; exact p101
    · rw [rm₂, rm₁ _ (Or.inl (by unfold aTL; unfold aOUT at hOUT; omega))
        (Or.inr (by unfold aTL aVL; omega)), htl]
    · rw [rm₂, rm₁ _ (Or.inl (by unfold aTH; unfold aOUT at hOUT; omega))
        (Or.inr (by unfold aTH aVL; omega)), hth]
  -- the moves
  obtain ⟨hwtb, hTLb, hA1, -⟩ := klein_bnd_hyps (M := M) (k := k) (g := g) (S := S) (ℓ := ℓ)
    (H := kleinH V S ℓ k) le_rfl
  have hA1' : (tripL V S ℓ : ℝ) + tripW S ℓ + 2 * (Fintype.card V * tripW S ℓ) +
      |(tripTh V S ℓ : ℝ)| ≤ kleinAI V F S ℓ k - tripH0 V S ℓ k := by
    unfold kleinAI; linarith
  have hA2 : 30 * (kleinAI V F S ℓ k - tripTh V S ℓ) + 12 * tripK V S ℓ +
      8 * ((tripL V S ℓ : ℝ) + tripW S ℓ) ≤ Hc := hHc
  have hV₀ : VBnd (kleinAI V F S ℓ k - (tripH0 V S ℓ k : ℝ)) n F₀ := hV₁.mono (by
    unfold kleinAI kleinA; linarith [abs_nonneg (tripTh V S ℓ : ℝ)])
  obtain ⟨R, Lo, os, c₃, G₃, o₃, -⟩ :=
    tLoop_orunC hW hWa hB hOUT hRB hP H hR hL hK hG hO hX hI₀ hwtb hTLb hA1' hA2 hV₀ le_rfl
  exact (o₁.seq (o₂.seq o₃)).2

end

section
variable {P : Input} {B : ℕ}

/-- **Every run of Klein's program `kleinProg` is compare-bounded by `Hc`** (`kleinHI ≤ Hc`),
from a configuration meeting the preconditions of `klein_exec`. -/
theorem kleinProg_cmpOK (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ B) (hB : n + 2 * nD ≤ B)
    (hOUT : aOUT nD + k * t ≤ B) (hRB : aRB n + k * t ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1))
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    (hX : KTgt M k g S ℓ nD n ιv t X P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F}
    (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x))
    (hCr : C.root = M.face (g 0))
    (hT : Compat T (tripSrc M k g 0) (tripDst M k g 0) (g (0 % k)) (tpar 𝒢 (tripSrc M k g 0)))
    {c₀ : Config} (hc₀ : WordsBounded (B + 16 * (n + 1)) c₀)
    (hwt : ∀ d, c₀.rmem (aWT + σ d) = tripWt M k g S ℓ 0 d)
    (hph : ∀ d, c₀.rmem (aPH nD + σ d) = tripφ S ℓ d) (htl : c₀.rmem (aTL nD) = tripL V S ℓ)
    (hth : c₀.rmem (aTH nD) = tripTh V S ℓ) (hh0 : c₀.rmem (aH0 nD) = tripH0 V S ℓ k) {Hc : ℕ}
    (hHc : kleinHI V F S ℓ k ≤ Hc) :
    ModNat.CmpOK P (B + 16 * (n + 1)) Hc (kleinProg B nD n k t) c₀ := by
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  unfold aOUT at hOUT
  refine ModNat.CmpOK.seq (ModNat.cmpOK_of_noTestR (by rfl) c₀) fun c₁ k₁ e₁ => ?_
  refine ModNat.CmpOK.seq (ModNat.cmpOK_of_noTestR (initS_noTestR B) c₁) fun c₂ k₂ e₂ => ?_
  have e1 := Exec.constN (P := P) hc₀ 151 n (by omega)
  obtain rfl := exec_post e1 e₁
  obtain ⟨c2, k2, e2, -, hS2, -, hmf, -⟩ := init_exec (P := P) B n e1.wb_right le_rfl (by simp)
  obtain rfl := exec_post e2 e₂
  have hm : ∀ a, a < B → c₂.rmem a = c₀.rmem a := fun a ha => (hmf a (Or.inl ha)).2
  exact kleinS_cmpOK le_rfl (by omega) hB (by unfold aOUT; omega) hRB hP H hR hL hK hG hO hX
    hI hoff hCr hT e2.wb_right hS2.toE
    (fun d => by rw [hm _ (by have := hσ d; unfold aWT; omega)]; exact hwt d)
    (fun d => by rw [hm _ (by have := hσ d; unfold aPH; omega)]; exact hph d)
    (by rw [hm _ (by unfold aTL; omega)]; exact htl)
    (by rw [hm _ (by unfold aTH; omega)]; exact hth)
    (by rw [hm _ (by unfold aH0; omega)]; exact hh0) hHc

end

end Klein

end PlanarFlow
