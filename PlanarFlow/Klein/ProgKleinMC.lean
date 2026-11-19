module

public import PlanarFlow.Klein.ProgInitC
public import PlanarFlow.Klein.TripBnd
public import WordRAM.Machine.KernelRfl

/-!
# Klein's masked program: every real comparison of every run is bounded

The initialisation (`in_orunC`) and the loop over the moves (`tLoopM_orunC`) are
compare-bounded; this file puts them together.

* `kleinZ`: the bound `2 #V tripW + 2 #F (tripH0 + tripL + 2 #V tripW)` of the total size of the
  additions of the initialisation (`zsum_init_le` with `|tripφ| ≤ tripW` and
  `|tripWt + psum - psum| ≤ tripL + 2 #V tripW`), hence of the values of the forest after it;
* `kleinAI = kleinA + kleinZ`, `kleinHI = 30 (kleinAI - tripTh) + 12 tripK + 8 (tripL + tripW)`:
  the constants `A`, `H` of `tLoopM_orunC` admitting the larger values of the forest after the
  initialisation;
* `kleinMS_cmpOK`: **every run of `kleinMS` from the initialised structure compares reals at
  distance at most `Hc`** when `kleinHI ≤ Hc`;
* `kleinProgM_cmpOK`: **the same for the whole masked program `kleinProgM`** from a
  configuration meeting the preconditions of `kleinM_exec`;
* `kleinHI_le`: `kleinHI ≤ 4800 (k + 1) (#V + 1)² (#F + 1) (tripW + 1)`, polynomial in the size
  of the map and the largest length.
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

/-! ### The constants -/

variable (V F S ℓ) in
/-- The bound of the total size of the additions of the initialisation. -/
def kleinZ (k : ℕ) : ℝ :=
  2 * (Fintype.card V * (tripW S ℓ : ℝ)) + 2 * (Fintype.card F * (|(tripH0 V S ℓ k : ℝ)| +
    ((tripL V S ℓ : ℝ) + 2 * ((Fintype.card V : ℝ) * (tripW S ℓ : ℝ)))))

variable (V F S ℓ) in
/-- The constant `A` of the bound `A - Lo` of the values of the forest along the whole program. -/
def kleinAI (k : ℕ) : ℝ := kleinA V S ℓ k + kleinZ V F S ℓ k

variable (V F S ℓ) in
/-- **The bound of the compared differences** along the whole masked program. -/
def kleinHI (k : ℕ) : ℝ :=
  30 * (kleinAI V F S ℓ k - tripTh V S ℓ) + 12 * tripK V S ℓ + 8 * (tripL V S ℓ + tripW S ℓ)

lemma kleinZ_nonneg : 0 ≤ kleinZ V F S ℓ k := by
  have hW : (0 : ℝ) ≤ tripW S ℓ := by exact_mod_cast tripW_nonneg
  have hL : (0 : ℝ) ≤ tripL V S ℓ := by exact_mod_cast tripL_nonneg
  unfold kleinZ
  positivity

lemma kleinA_sub_tripTh_nonneg : 0 ≤ kleinA V S ℓ k - tripTh V S ℓ := by
  have hW : (0 : ℝ) ≤ tripW S ℓ := by exact_mod_cast tripW_nonneg
  have hL : (0 : ℝ) ≤ tripL V S ℓ := by exact_mod_cast tripL_nonneg
  have hK : (0 : ℝ) ≤ tripK V S ℓ := by exact_mod_cast tripK_nonneg
  have hv : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have e : (tripH0 V S ℓ k : ℝ) = tripTh V S ℓ + (k + 1) * ((Fintype.card V + 1) *
      tripK V S ℓ) := by simp [tripH0]
  unfold kleinA
  rw [e]
  have : 0 ≤ ((k : ℝ) + 1) * ((Fintype.card V + 1) * tripK V S ℓ) := by positivity
  have : 0 ≤ (Fintype.card V : ℝ) * tripW S ℓ := by positivity
  linarith [abs_nonneg (tripTh V S ℓ : ℝ)]

/-- **The bound `kleinHI` is polynomial**: at most `4800 (k + 1) (#V + 1)² (#F + 1) (tripW + 1)`. -/
theorem kleinHI_le :
    kleinHI V F S ℓ k ≤ 4800 * (k + 1) * ((Fintype.card V : ℝ) + 1) ^ 2 *
      ((Fintype.card F : ℝ) + 1) * (tripW S ℓ + 1) := by
  obtain ⟨hV, hH⟩ := kleinV_kleinH_le (V := V) (S := S) (ℓ := ℓ) (k := k)
  have hW : (0 : ℝ) ≤ tripW S ℓ := by exact_mod_cast tripW_nonneg
  have hL : (0 : ℝ) ≤ tripL V S ℓ := by exact_mod_cast tripL_nonneg
  have hK : (0 : ℝ) ≤ tripK V S ℓ := by exact_mod_cast tripK_nonneg
  have hv : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hf : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have e : (tripH0 V S ℓ k : ℝ) = tripTh V S ℓ + (k + 1) * ((Fintype.card V + 1) *
      tripK V S ℓ) := by simp [tripH0]
  have hTh0 : (0 : ℝ) ≤ tripTh V S ℓ := by
    have eL : (tripL V S ℓ : ℝ) = 4 * (Fintype.card V * tripW S ℓ) + tripW S ℓ + 1 := by
      simp [tripL, tripB]
    have eTh : (tripTh V S ℓ : ℝ) = (tripL V S ℓ : ℝ) - 2 * (Fintype.card V * tripW S ℓ) := by
      simp [tripTh]
    have : 0 ≤ (Fintype.card V : ℝ) * tripW S ℓ := by positivity
    rw [eTh, eL]; linarith
  have hH0 : (0 : ℝ) ≤ tripH0 V S ℓ k := by
    rw [e]; have : 0 ≤ ((k : ℝ) + 1) * ((Fintype.card V + 1) * tripK V S ℓ) := by positivity
    linarith
  -- `kleinZ ≤ (2 #F + 1) kleinV`
  have hKV : kleinV V S ℓ k = tripH0 V S ℓ k + tripL V S ℓ + tripW S ℓ +
      2 * (Fintype.card V * tripW S ℓ) := by
    unfold kleinV kleinA; rw [abs_of_nonneg hTh0]; ring
  have hvw : 0 ≤ (Fintype.card V : ℝ) * tripW S ℓ := by positivity
  have hZ : kleinZ V F S ℓ k ≤ (2 * Fintype.card F + 1) * kleinV V S ℓ k := by
    unfold kleinZ; rw [abs_of_nonneg hH0, hKV]
    nlinarith [mul_nonneg hf hW, mul_nonneg hf hvw, mul_nonneg hf hL, mul_nonneg hf hH0]
  have hHI : kleinHI V F S ℓ k = kleinH V S ℓ k + 30 * kleinZ V F S ℓ k := by
    unfold kleinHI kleinAI kleinH; ring
  set P : ℝ := (k + 1) * ((Fintype.card V : ℝ) + 1) ^ 2 * (tripW S ℓ + 1) with hP
  have hP0 : 0 ≤ P := by positivity
  have h1 : kleinH V S ℓ k ≤ 3000 * P := by rw [hP]; linarith
  have h2 : kleinV V S ℓ k ≤ 60 * P := by rw [hP]; linarith
  have h3 : (2 * (Fintype.card F : ℝ) + 1) * kleinV V S ℓ k ≤
      (2 * Fintype.card F + 1) * (60 * P) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have e2 : 4800 * (k + 1) * ((Fintype.card V : ℝ) + 1) ^ 2 * ((Fintype.card F : ℝ) + 1) *
      (tripW S ℓ + 1) = 4800 * (Fintype.card F + 1) * P := by rw [hP]; ring
  rw [hHI, e2]
  nlinarith [mul_nonneg hf hP0]

/-! ### The whole masked program -/

section
variable {P : Input} {W B : ℕ}

/-- **Every run of `kleinMS` from the initialised structure is compare-bounded by `Hc`**, for
`kleinHI ≤ Hc`, under the preconditions of `kleinMS_orun`. -/
theorem kleinMS_cmpOK (hW : B + 16 * (n + 1) ≤ W) (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ W)
    (hB : n + 2 * nD ≤ B) (hOUT : aOUT nD + kRank fl k * t ≤ B)
    (hRB : aRBM n k + kRank fl k * t ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W)
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
    (hmk : ∀ j < k, c.nmem (aMK n + j) = if fl j then 1 else 0) {Hc : ℕ}
    (hHc : kleinHI V F S ℓ k ≤ Hc) :
    ModNat.CmpOK P W Hc (kleinMS B nD n k t) c := by
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
  -- the size of the additions of the initialisation
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
  obtain ⟨c₁, G₁, os₁, o₁, -, ho₁, hS₁, hKM₁, -, out₁, nm₁, rm₁, hV₁⟩ := in_orunC (H := Hc) hW
    (by omega) hB (by unfold aOUT at hOUT; omega) hP hL hK hI hoff hc hS hwt hph hh0 hHZ hZ
  set F₀ := (runOpsE n (Forest.init n) os₁).1 with hF₀
  -- the registers of the loop
  have hg0 : P.data.getD (iGB nD n) 0 = σ (g 0) := by simpa using hG 0 (by omega)
  have hc₁ := o₁.1.2.wb
  have h0 := hσ (g 0)
  have h0' := hσ (M.rev (g 0))
  obtain ⟨c₂, k₂, e₂, hk₂, p80, p81, p82, p100, p101, n₂, r₂, mm₂, rm₂, out₂⟩ : ∃ c' k', Exec P W
      (block (setupIM nD n k)) c₁ c' k' ∧ k' = 14 ∧ c'.nreg 80 = 0 ∧ c'.nreg 81 = k ∧
      c'.nreg 82 = 0 ∧
      c'.nreg 100 = ιf (M.face (M.rev (g 0))) ∧ c'.nreg 101 = ιf (M.face (g 0)) ∧
      (∀ r, r ≠ 80 → r ≠ 81 → r ≠ 82 → r ≠ 85 → r ≠ 86 → r ≠ 100 → r ≠ 101 →
        c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.nmem = c₁.nmem ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
    unfold setupIM
    exec_block
    all_goals try (first
      | exact hP _
      | omega
      | (simp only [iGB, iNF, iRV]; omega)
      | (config_simp; rw [hg0]; simp only [iNF, iRV]; omega)
      | (config_simp; rw [hg0, hK.rv]; simp only [iNF]; omega))
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, ?_, ?_,
      fun r h1 h2 h3 h4 h5 h6 h7 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [hg0, hK.rv, hK.nf]
    · config_simp; rw [hg0, hK.nf]
    · config_simp
      simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3, upd_other _ _ _ h4,
        upd_other _ _ _ h5, upd_other _ _ _ h6, upd_other _ _ _ h7]
  have o₂ : ORunC P W Hc B n _ c₁ F₀ G₁ c₂ [] G₁ 0 k₂ := ORunC.glue e₂ o₁.1.2.lcte
    (fun a _ _ => by rw [mm₂, rm₂]; exact ⟨rfl, rfl⟩)
    (n₂ 151 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    (by rfl)
  -- the invariant at the first move
  have hI₀ : TInvM M k g S ℓ σ n ιv ιg ιf ιe t X fl B W F₀ c₂
      (0, fun _ => startData T (fun d => tripWt M k g S ℓ 0 d + T.psum (tripφ S ℓ) (M.tail d) -
        T.psum (tripφ S ℓ) (M.head d)) (g 0), (tripH0 V S ℓ k : ℝ)) [] G₁ c₂ := by
    refine ⟨Nat.zero_le _, ⟨fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega)⟩, ⟨hT, fun d _ => rfl⟩, o₂.1.2.lcte, e₂.wb_right, ?_,
      by simp, rfl, by simp, ?_, p80, p81, by rw [p82]; rfl, ?_, ?_, ?_, ?_, fun j hj => ?_,
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
    · rw [mm₂, nm₁ (aMK n + j) (Or.inl (by unfold aMK; unfold aRBM at hRB; omega))
        (by unfold aMK; omega)]
      exact hmk j hj
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
    tLoopM_orunC hW hWa hB hOUT hRB hP H hR hL hK hG hO hX hI₀ hwtb hTLb hA1' hA2 hV₀ le_rfl
  exact (o₁.seq (o₂.seq o₃)).2

end

section
variable {P : Input} {B : ℕ}

/-- The initialisation of the structure has no real test. -/
lemma initS_noTestR (B : ℕ) : (DynTree.initS B).noTestR = true := by kernel_rfl

/-- **Every run of Klein's masked program is compare-bounded by `Hc`** (`kleinHI ≤ Hc`), from a
configuration meeting the preconditions of `kleinM_exec`. -/
theorem kleinProgM_cmpOK (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ B) (hB : n + 2 * nD ≤ B)
    (hOUT : aOUT nD + kRank fl k * t ≤ B) (hRB : aRBM n k + kRank fl k * t ≤ B)
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
    (hth : c₀.rmem (aTH nD) = tripTh V S ℓ) (hh0 : c₀.rmem (aH0 nD) = tripH0 V S ℓ k)
    (hmk : ∀ j < k, c₀.nmem (aMK n + j) = if fl j then 1 else 0) {Hc : ℕ}
    (hHc : kleinHI V F S ℓ k ≤ Hc) :
    ModNat.CmpOK P (B + 16 * (n + 1)) Hc (kleinProgM B nD n k t) c₀ := by
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  unfold aOUT at hOUT
  refine ModNat.CmpOK.seq (ModNat.cmpOK_of_noTestR (by rfl) c₀) fun c₁ k₁ e₁ => ?_
  refine ModNat.CmpOK.seq (ModNat.cmpOK_of_noTestR (initS_noTestR B) c₁) fun c₂ k₂ e₂ => ?_
  have e1 := Exec.constN (P := P) hc₀ 151 n (by omega)
  obtain rfl := exec_post e1 e₁
  obtain ⟨c2, k2, e2, -, hS2, -, hmf, -⟩ := init_exec (P := P) B n e1.wb_right le_rfl (by simp)
  obtain rfl := exec_post e2 e₂
  have hm : ∀ a, a < B → c₂.rmem a = c₀.rmem a := fun a ha => (hmf a (Or.inl ha)).2
  have hmn : ∀ a, a < B → c₂.nmem a = c₀.nmem a := fun a ha => (hmf a (Or.inl ha)).1
  exact kleinMS_cmpOK le_rfl (by omega) hB (by unfold aOUT; omega) hRB hP H hR hL hK hG hO hX
    hI hoff hCr hT e2.wb_right hS2.toE
    (fun d => by rw [hm _ (by have := hσ d; unfold aWT; omega)]; exact hwt d)
    (fun d => by rw [hm _ (by have := hσ d; unfold aPH; omega)]; exact hph d)
    (by rw [hm _ (by unfold aTL; omega)]; exact htl)
    (by rw [hm _ (by unfold aTH; omega)]; exact hth)
    (by rw [hm _ (by unfold aH0; omega)]; exact hh0)
    (fun j hj => by
      rw [hmn (aMK n + j) (by unfold aMK; unfold aRBM at hRB; omega)]; exact hmk j hj) hHc

end

end Klein

end PlanarFlow
