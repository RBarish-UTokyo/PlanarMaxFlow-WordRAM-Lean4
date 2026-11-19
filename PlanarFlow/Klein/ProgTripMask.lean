module

public import PlanarFlow.Klein.ProgTrip
public import PlanarFlow.Klein.ProgQueryMask

/-!
# Klein's algorithm on the machine: answers at the flagged moves only

`kleinProgM` is `kleinProg` (`PlanarFlow/Klein/ProgTrip.lean`) with the query phase of each move
masked: the caller flags some of the `k` moves (`fl : ℕ → Bool`, as the array `MK` of `k`
natural words at `aMK n = n` in the natural memory of the starting configuration, `1` for a
flagged move and `0` otherwise), and the `t` path-sum queries run only at the start of a flagged
move. The answers of the flagged move `j` go to the slot `kRank fl j` (the number of flagged
moves before `j`): the real word `OUT[kRank fl j · t + i]` at `aOUT nD + …` and the reach bit
`RBM[kRank fl j · t + i]` at `aRBM n k = n + k` (`kOutM`), so the output arrays hold `f t` words,
`f = kRank fl k` the number of flagged moves.

**Cost.** The unmasked program costs `k t` queries, `O(N log N + k t log N)` steps
(`klein_steps_le`); on the cuts of the maximum-flow algorithm `k` is the number of darts leaving
the path, which can be of the order of the size of the piece, so that bound is not within the
allowance `K (m lg m + p² lg m)` of `PlanarFlow.BKMNW.SubCosts.Bounds.mssp` for a path of `p`
darts. Here a move costs `t` queries only when it is flagged and a constant number of steps to
read its flag otherwise: `kleinOpsM` (`f t` queries) and `kleinExtM`, `O(N log N + f t log N)`
steps in all (`kleinM_steps_le`; the `O(k)` steps of the unflagged moves are within `N`, as
`k ≤ #V`). The pivots and the steps to the next move are unchanged (`O(N)` in total).

* `tBodyMS`: the move with the masked queries (`qMaskS`, `PlanarFlow/Klein/ProgQueryMask.lean`);
  `TInvM`, `tBodyM_orun`, `tLoopM_orun`: the invariant and the loop over the moves, as `TInv`,
  `tBody_orun`, `tLoop_orun`, with the slot counter `r82 = kRank fl J`, the mask kept, and the
  answers of the flagged moves only.
* `kleinMS_orun`, `kleinM_exec`: **the end-to-end theorem of the masked program**, with the
  preconditions of `klein_exec` and the mask in the natural memory: the answers `kOutM` of every
  flagged move `j < k` at every target are the distances (`odist`).
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs

/-! ### The program with the masked queries -/

/-- The natural array `MK` of the flags of the `k` moves (in the natural memory). -/
def aMK (n : ℕ) : ℕ := n

/-- The natural array `RBM` of the reach bits of the flagged moves, after `MK`:
`RBM[q t + i]` for the slot `q` and the target `X i`. -/
def aRBM (n k : ℕ) : ℕ := n + k

/-- **One move with the masked queries** (`r80 = j`, `r81 = k`, `r82` the slot counter): the
flag `MK[j]` read into `r108`; when it is set, the path sums at the `t` targets into
`OUT[r82 t …]` and their reach bits into `RBM[r82 t …]`, and `r82` advanced (`qMaskS`); then the
pivot loop and the step to the next move as in `tBodyS`. -/
def tBodyMS (B nD n k t : ℕ) : Stmt :=
  .seq (block [.modN 90 80 81, .constN 92 1, .addN 91 80 92, .modN 91 91 81, .constN 105 t,
    .mulN 93 82 105, .constN 106 (aOUT nD), .addN 106 106 93, .constN 109 (aRBM n k),
    .addN 109 109 93, .constN 104 0, .constN 107 (aMK n), .addN 107 107 80, .loadN 108 107,
    .constN 107 0]) <|
  .seq (qMaskS B nD n k t) <|
  .seq (block [.constN 94 (aTH nD), .loadR 100 94, .constN 102 0, .constN 103 1]) <|
  .seq (mvLoopS B nD) <|
  .seq (.seq (nxAS B nD n) (wtS B nD n k)) <|
  block [.constN 92 1, .addN 80 80 92]

/-- **The loop over the `k` moves**, with the masked queries. -/
def tLoopMS (B nD n k t : ℕ) : Stmt := .whileLtN 80 81 (tBodyMS B nD n k t)

/-- **The answer in the output for the slot `q`** and the target `X i`: the real word
`OUT[q t + i]` when the reach bit `RBM[q t + i]` is `1`, none otherwise. The answers of the
flagged move `j` are in the slot `kRank fl j`. -/
def kOutM (nD n k t : ℕ) (c : Config) (q i : ℕ) : Option ℝ :=
  if c.nmem (aRBM n k + q * t + i) = 1 then some (c.rmem (aOUT nD + q * t + i)) else none

/-- The operations counted for the move `j` of the masked loop (`t` queries when it is
flagged). -/
def tCntM (t : ℕ) (b : Bool) {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] {M : CombMap D V F} {S : Finset D}
    (Rj : MoveData M S) (Δ : ℕ) : ℕ :=
  (if b then t else 0) + 2 * (27 * Rj.m + 1) + 29 + 5 * Δ

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ} {nD : ℕ}
  {σ : D ≃ Fin nD} {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} {t : ℕ}
  {X : ℕ → V} {fl : ℕ → Bool}

local notation "𝒢" => pieceGraph M S ℓ

variable (M k g S ℓ σ n ιv ιg ιf ιe) in
/-- **The invariant of the masked loop over the moves**: as `TInv`, with the slot counter
`r82 = kRank fl J`, the mask `MK` kept, and the answers of the flagged moves `j < J` in their
slots. -/
structure TInvM (t : ℕ) (X : ℕ → V) (fl : ℕ → Bool) (B W : ℕ) (F₀ : Forest) (c₀ : Config)
    (y : ℕ × (ℕ → MoveData M S) × ℝ) (hs : List EOp) (G : List VT) (c : Config) : Prop where
  jle : y.1 ≤ k
  trip : IsTripUpTo M k g S ℓ y.1 y.2.1
  start : StartOK M k g S ℓ y.1 ((y.2.1 y.1).T 0) ((y.2.1 y.1).val 0)
  lcte : LCTE B n (runOpsE n F₀ hs).1 G c
  wb : WordsBounded W c
  st : Stored M n ιv ιg ιf ιe (tripφ S ℓ) (M.face (g (y.1 % k))) y.2.2 (runOpsE n F₀ hs).1
    ((y.2.1 y.1).T 0) ((y.2.1 y.1).val 0)
  lo : (tripH0 V S ℓ k : ℝ) - y.1 * ((Fintype.card V + 1) * (tripK V S ℓ : ℝ)) ≤ y.2.2
  out : (runOpsE n F₀ hs).2 = []
  len : hs.length ≤ ∑ j ∈ range y.1, (16 * (y.2.1 j).m + 18 + 4 * (tripΔ M k g S j).card)
  kmem : KMem M σ ιv ((y.2.1 y.1).T 0) (tripWt M k g S ℓ y.1) (tripφ S ℓ) c
  r80 : c.nreg 80 = y.1
  r81 : c.nreg 81 = k
  r82 : c.nreg 82 = kRank fl y.1
  r100 : c.nreg 100 = ιf (M.face (M.rev (g (y.1 % k))))
  r101 : c.nreg 101 = ιf (M.face (g (y.1 % k)))
  tl : c.rmem (aTL nD) = tripL V S ℓ
  th : c.rmem (aTH nD) = tripTh V S ℓ
  flags : ∀ j < k, c.nmem (aMK n + j) = if fl j then 1 else 0
  dist : ∀ j < y.1, fl j = true → ∀ i < t,
    kOutM nD n k t c (kRank fl j) i = (odist 𝒢 (tripSrc M k g j) (X i)).map ((↑) : ℤ → ℝ)
  output : c.output = c₀.output
  regs : ∀ r, r < 80 → c.nreg r = c₀.nreg r ∧ c.rreg r = c₀.rreg r

section
variable {P : Input} {W B : ℕ}

/-- **One iteration of the masked loop over the moves**: the move `J` and the step to the move
`J + 1`, counted `tCntM` operations (`t` queries when `J` is flagged) and
`14 t + 182 + 30 #(tripΔ J)` further steps when it is flagged, `182 + 30 #(tripΔ J)` otherwise. -/
theorem tBodyM_orun (hW : B + 16 * (n + 1) ≤ W) (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ W)
    (hB : n + 2 * nD ≤ B) (hOUT : aOUT nD + kRank fl k * t ≤ B)
    (hRB : aRBM n k + kRank fl k * t ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W)
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    (hX : KTgt M k g S ℓ nD n ιv t X P) {F₀ : Forest} {c₀ : Config}
    (y : ℕ × (ℕ → MoveData M S) × ℝ) (hs : List EOp) (G : List VT) (c : Config)
    (h : TInvM M k g S ℓ σ n ιv ιg ιf ιe t X fl B W F₀ c₀ y hs G c) (ht : y.1 < k) :
    ∃ (y' : ℕ × (ℕ → MoveData M S) × ℝ) (c' : Config) (os : List EOp) (G' : List VT),
      ORun P W B n (tBodyMS B nD n k t) c (runOpsE n F₀ hs).1 G c' os G'
        (tCntM t (fl y.1) (y'.2.1 y.1) (tripΔ M k g S y.1).card)
        (14 * (if fl y.1 then t else 0) + 182 + 30 * (tripΔ M k g S y.1).card) ∧
      TInvM M k g S ℓ σ n ιv ιg ιf ιe t X fl B W F₀ c₀ y' (hs ++ os) G' c' ∧ y'.1 = y.1 + 1 ∧
      ∀ j < y.1, y'.2.1 j = y.2.1 j := by
  classical
  obtain ⟨J, R, Lo⟩ := y
  simp only at h ht ⊢
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
  have o₁ : ORun P W B n _ c F G c₁ [] G 0 k₁ := ORun.glue e₁ h.lcte
    (fun a _ _ => by rw [mm₁, rm₁]; exact ⟨rfl, rfl⟩) (n₁ 151 (by omega))
  have p108' : c₁.nreg 108 = if fl J then 1 else 0 := by rw [p108]; exact h.flags J ht
  have p82 : c₁.nreg 82 = q := by rw [n₁ 82 (Or.inl (by omega)), h82]
  -- the answers at the targets, when the move is flagged
  obtain ⟨c₂, G₂, o₂, q₂, s82, rg₂, out₂, nm₂, rm₂⟩ := qMask_orun (P := P) (k := k) (X := X)
    (xb := fun i => if Reach 𝒢 (M.tail (g 0)) (X i) then 1 else 0) hW
    (by unfold iXT; omega) hP hL hX.xn hX.xr (base := aOUT nD + q * t)
    (rbase := aRBM n k + q * t) (fl J)
    (fun hb => by have := hqf' hb; unfold aOUT at *; omega)
    (fun hb => by have := hqf' hb; unfold aRBM at *; omega)
    e₁.wb_right o₁.2.lcte p104 p105 p106 p109 p107 p108' p82 (by have := kRank_le fl J; omega)
  -- the threshold
  have hc₂ := o₂.2.wb
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
  have o₃ : ORun P W B n _ c₂ _ G₂ c₃ [] G₂ 0 k₃ := ORun.glue e₃ o₂.2.lcte
    (fun a _ _ => by rw [mm₃, rm₃]; exact ⟨rfl, rfl⟩) (n₃ 151 (by omega) (by omega) (by omega))
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
  obtain ⟨T, val, d, m, os₄, c₄, G₄, Lo₄, o₄, hT0, hv0, hrun, hTs, hl₄, ho₄, hS₄, hLo₄, hKM₄, fr₄,
    v100, v101, -, -⟩ := mv_orunA (P := P) hW (by omega) hB hP H.plane (H.tripMoveHyp hR J) H.uniq
    (H.g_not_mem J) (H.rev_g_not_mem J) (fun d hd => tripφ_of_mem hd) (W := tripW S ℓ)
    abs_tripφ_le (fun d hd hr => tripWt_elig J hd hr) (fun d hd => tripWt_inelig J hd)
    (fun d hd => tripL_gt hd) hL hK h.start.1 h.start.2 h.st hLo e₃.wb_right o₃.2.lcte hKM₃
    u100 u101 s100 s102 s103
  set RJ : MoveData M S := ⟨T, val, selForest M S (tpar 𝒢 (tripSrc M k g J)) d, d, m⟩ with hRJ
  have hMJ : MoveSpec M k g S ℓ J RJ := ⟨hrun, hTs⟩
  -- the next move
  have hc₄ := o₄.2.wb
  have w90 : c₄.nreg 90 = J % k := by rw [(fr₄.1 90 (by omega)).1, n₃ 90 (by omega) (by omega)
    (by omega), (rg₂ 90 (by omega) (by omega) (by omega)).1, p90]
  have w91 : c₄.nreg 91 = (J + 1) % k := by rw [(fr₄.1 91 (by omega)).1, n₃ 91 (by omega)
    (by omega) (by omega), (rg₂ 91 (by omega) (by omega) (by omega)).1, p91]
  have wtl : c₄.rmem (aTL nD) = tripL V S ℓ := by
    rw [fr₄.2.2.1 _ (Or.inl (by unfold aTL; unfold aOUT at hOUT; omega)),
      hrm₃ _ (Or.inl (by unfold aTL; unfold aOUT at hOUT; omega))
        (Or.inl (by unfold aTL aOUT; omega)), h.tl]
  obtain ⟨c₅, G₅, os₅, T', val', o₅, hl₅, ho₅, hS₅, hstart, hr, hpw, hpu, hpx, hKM₅, x100, x101,
    rg₅, out₅, rm₅, nm₅⟩ := nx_orun (P := P) hW (by omega) hB (by unfold aOUT at hOUT; omega) hP
    H hR hL hK hG hO hMJ hc₄ o₄.2.lcte hS₄ hKM₄ wtl w90 w91 (by rw [v101, u101])
  -- the next index
  have hc₅ := o₅.2.wb
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
  have o₆ : ORun P W B n _ c₅ _ G₅ c₆ [] G₅ 0 k₆ := ORun.glue e₆ o₅.2.lcte
    (fun a _ _ => by rw [mm₆, rm₆]; exact ⟨rfl, rfl⟩) (n₆ 151 (by omega) (by omega))
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
    (by omega), ⟨by simp only; omega, htrip, ?_, ?_, o₆.2.wb, ?_, ?_, ?_, ?_, ?_, z80, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, fun j hj => hlt j hj⟩
  · show StartOK M k g S ℓ (J + 1) ((R' (J + 1)).T 0) ((R' (J + 1)).val 0)
    rw [hJ1]; exact hstart
  · rw [runOpsE_fst_append]; exact o.2.lcte
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

/-- **The masked loop over the moves**: from the invariant at the start of the first move, the
loop makes the `k` moves, counted `∑ j < k, tCntM` operations and
`∑ j < k, (14 t [j flagged] + 190 + 30 #(tripΔ j)) + 2` further steps, and ends with the
invariant at the move `k`. -/
theorem tLoopM_orun (hW : B + 16 * (n + 1) ≤ W) (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ W)
    (hB : n + 2 * nD ≤ B) (hOUT : aOUT nD + kRank fl k * t ≤ B)
    (hRB : aRBM n k + kRank fl k * t ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W)
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    (hX : KTgt M k g S ℓ nD n ιv t X P) {F₀ : Forest} {c₀ : Config} {R₀ : ℕ → MoveData M S}
    {Lo₀ : ℝ} {G : List VT} {c : Config}
    (h : TInvM M k g S ℓ σ n ιv ιg ιf ιe t X fl B W F₀ c₀ (0, R₀, Lo₀) [] G c) :
    ∃ (R : ℕ → MoveData M S) (Lo : ℝ) (os : List EOp) (c' : Config) (G' : List VT),
      ORun P W B n (tLoopMS B nD n k t) c F₀ G c' os G'
        (∑ j ∈ range k, tCntM t (fl j) (R j) (tripΔ M k g S j).card)
        (∑ j ∈ range k, (14 * (if fl j then t else 0) + 190 + 30 * (tripΔ M k g S j).card) +
          2) ∧
      TInvM M k g S ℓ σ n ιv ιg ιf ιe t X fl B W F₀ c₀ (k, R, Lo) os G' c' := by
  classical
  set cnt : ℕ × (ℕ → MoveData M S) × ℝ → ℕ := fun y =>
    ∑ j ∈ range y.1, tCntM t (fl j) (y.2.1 j) (tripΔ M k g S j).card with hcnt
  set ext : ℕ × (ℕ → MoveData M S) × ℝ → ℕ := fun y =>
    ∑ j ∈ Ico y.1 k, (14 * (if fl j then t else 0) + 190 + 30 * (tripΔ M k g S j).card)
    with hext
  obtain ⟨y, os, c', G', hrun, hI, ht, -, -⟩ := ORun.whileLtN (P := P) (W := W) (B := B)
    (n := n) (a := 80) (b := 81) (body := tBodyMS B nD n k t) F₀
    (fun y hs G₁ c₁ => TInvM M k g S ℓ σ n ιv ιg ιf ιe t X fl B W F₀ c₀ y hs G₁ c₁) cnt ext
    (fun _ _ _ _ h' _ => ⟨h'.lcte, h'.wb⟩)
    (fun y hs G₁ c₁ h' _ ht => by
      have hJ : y.1 < k := by rw [h'.r80, h'.r81] at ht; exact ht
      obtain ⟨y', c₂, os, G₂, o, hI', hy1, hagree⟩ :=
        tBodyM_orun hW hWa hB hOUT hRB hP H hR hL hK hG hO hX y hs G₁ c₁ h' hJ
      refine ⟨y', c₂, os, G₂, _, _, o, hI', ?_, ?_⟩
      · simp only [hcnt, hy1, sum_range_succ]
        rw [sum_congr rfl fun j hj => by rw [hagree j (mem_range.1 hj)]]
      · simp only [hext, hy1]
        rw [sum_eq_sum_Ico_succ_bot hJ]
        omega)
    (x := (0, R₀, Lo₀)) (hs := []) h trivial
  have hk : y.1 = k := by
    have := hI.jle; rw [hI.r80, hI.r81] at ht; omega
  obtain ⟨J, R, Lo⟩ := y
  simp only at hk
  subst hk
  refine ⟨R, Lo, os, c', G', hrun.mono (by simp [hcnt]) ?_, by simpa using hI⟩
  simp only [hext, Ico_self, sum_empty, Nat.sub_zero]
  rw [range_eq_Ico]

end

/-! ### The whole program -/

/-- The registers of the loop, the query nodes of the first move and the slot counter. -/
def setupIM (nD n k : ℕ) : List Instr :=
  [.constN 80 0, .constN 81 k, .constN 85 (iGB nD n), .readIn 85 85,
    .constN 101 (iNF nD), .addN 101 101 85, .readIn 101 101,
    .constN 86 (iRV nD), .addN 86 86 85, .readIn 86 86,
    .constN 100 (iNF nD), .addN 100 100 86, .readIn 100 100, .constN 82 0]

/-- **Klein's algorithm with the masked queries** (after `r151 := n` and the initialisation of
the structure): the initial trees (`inS`), then the `k` moves around the face (`tLoopMS`), with
the answers at the `t` targets at the start of the flagged moves only. -/
def kleinMS (B nD n k t : ℕ) : Stmt := .seq (inS B nD n k) (.seq (block (setupIM nD n k))
  (tLoopMS B nD n k t))

/-- **The program with the masked queries**: `r151 := n`, the initialisation of the structure,
`kleinMS`. -/
def kleinProgM (B nD n k t : ℕ) : Stmt :=
  .seq (.instr (.constN 151 n)) (.seq (initS B) (kleinMS B nD n k t))

/-- The bound of the counted operations of `kleinMS` (`f t` queries for `f` flagged moves). -/
def kleinOpsM (nV nF nD nS k f t : ℕ) : ℕ :=
  6 * (nV + nF) + 2 * nD + f * t + 64 * nS + 31 * k

/-- The bound of the further steps of `kleinMS`. -/
def kleinExtM (nV nF nD nS k f t : ℕ) : ℕ :=
  60 * (nV + nF) + 20 * nD + 60 + 14 * (f * t) + 190 * k + 60 * nS

section
variable {P : Input} {W B : ℕ}

lemma sum_tCntM_le (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) {R : ℕ → MoveData M S}
    (hT : IsTripUpTo M k g S ℓ k R) :
    ∑ j ∈ range k, tCntM t (fl j) (R j) (tripΔ M k g S j).card ≤
      kRank fl k * t + 64 * S.card + 31 * k := by
  have e : ∀ j, tCntM t (fl j) (R j) (tripΔ M k g S j).card =
      (if fl j = true then t else 0) + (31 + 54 * (R j).m + 5 * (tripΔ M k g S j).card) :=
    fun j => by unfold tCntM; ring
  rw [sum_congr rfl fun j _ => e j, sum_add_distrib, sum_flag, sum_add_distrib,
    sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, card_range, smul_eq_mul]
  have h1 := hT.pivots H hR le_rfl
  have h2 := sum_tripΔ_le H
  omega

lemma sum_extM_le (H : Hyp M k g S ℓ) :
    ∑ j ∈ range k, (14 * (if fl j then t else 0) + 190 + 30 * (tripΔ M k g S j).card) ≤
      14 * (kRank fl k * t) + 190 * k + 60 * S.card := by
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_flag, sum_const, card_range,
    smul_eq_mul]
  have h2 := sum_tripΔ_le H
  omega

/-- **Klein's algorithm with the masked queries, from the initialised structure**: as
`kleinS_orun`, with the flags `fl` of the `k` moves in the natural memory (`MK`), counted at
most `kleinOpsM` operations (`f t` queries, `f = kRank fl k`) and `kleinExtM` further steps;
at the end, for every flagged move `j < k` and target `X i`, the answer `kOutM` in the slot
`kRank fl j` is the distance from the source of the move `j` to `X i`, none when it is not
reached. -/
theorem kleinMS_orun (hW : B + 16 * (n + 1) ≤ W) (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ W)
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
    (hmk : ∀ j < k, c.nmem (aMK n + j) = if fl j then 1 else 0) :
    ∃ c' F' G' m', LRun P W B n (kleinMS B nD n k t) c G c' F' G' m'
        (kleinExtM (Fintype.card V) (Fintype.card F) nD S.card k (kRank fl k) t) ∧
      m' ≤ kleinOpsM (Fintype.card V) (Fintype.card F) nD S.card k (kRank fl k) t ∧
      (∃ R : ℕ → MoveData M S, IsTripUpTo M k g S ℓ k R) ∧
      (∀ j < k, fl j = true → ∀ i < t,
        kOutM nD n k t c' (kRank fl j) i =
          (odist 𝒢 (tripSrc M k g j) (X i)).map ((↑) : ℤ → ℝ)) ∧
      c'.output = c.output := by
  classical
  have hk := H.two_le_k
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  -- the initial trees
  obtain ⟨c₁, G₁, os₁, o₁, -, ho₁, hS₁, hKM₁, -, out₁, nm₁, rm₁⟩ := in_orun hW (by omega) hB
    (by unfold aOUT at hOUT; omega) hP hL hK hI hoff hc hS hwt hph hh0
  set F₀ := (runOpsE n (Forest.init n) os₁).1 with hF₀
  -- the registers of the loop
  have hg0 : P.data.getD (iGB nD n) 0 = σ (g 0) := by simpa using hG 0 (by omega)
  have hc₁ := o₁.2.wb
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
  have o₂ : ORun P W B n _ c₁ F₀ G₁ c₂ [] G₁ 0 k₂ := ORun.glue e₂ o₁.2.lcte
    (fun a _ _ => by rw [mm₂, rm₂]; exact ⟨rfl, rfl⟩)
    (n₂ 151 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  -- the invariant at the first move
  have hI₀ : TInvM M k g S ℓ σ n ιv ιg ιf ιe t X fl B W F₀ c₂
      (0, fun _ => startData T (fun d => tripWt M k g S ℓ 0 d + T.psum (tripφ S ℓ) (M.tail d) -
        T.psum (tripφ S ℓ) (M.head d)) (g 0), (tripH0 V S ℓ k : ℝ)) [] G₁ c₂ := by
    refine ⟨Nat.zero_le _, ⟨fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega)⟩, ⟨hT, fun d _ => rfl⟩, o₂.2.lcte, e₂.wb_right, ?_,
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
  obtain ⟨R, Lo, os, c₃, G₃, o₃, hI₃⟩ :=
    tLoopM_orun hW hWa hB hOUT hRB hP H hR hL hK hG hO hX hI₀
  have o := o₁.seq (o₂.seq o₃)
  have hTk : IsTripUpTo M k g S ℓ k R := hI₃.trip
  refine ⟨c₃, _, G₃, _, o.2.mono le_rfl ?_, ?_, ⟨R, hTk⟩, hI₃.dist, ?_⟩
  · have := sum_extM_le (fl := fl) (t := t) H
    unfold kleinExtM; omega
  · have := sum_tCntM_le (t := t) (fl := fl) (R := R) H hR hI₃.trip
    unfold kleinOpsM; omega
  · rw [hI₃.output, out₂, out₁]

end

/-! ### The end-to-end theorem -/

section
variable {P : Input} {B : ℕ}

/-- **Klein's algorithm on the machine with the masked queries**: the program `kleinProgM` runs
from a configuration `c₀` meeting the preconditions of `klein_exec` and holding, in its natural
memory, the flags of the `k` moves (`MK`: the word `aMK n + j` is `1` when the move `j` is
flagged, `0` otherwise), within `140 (n + 1) + 21 + kleinOpsM · opCostE n + kleinExtM` steps
(`f t` queries for the `f = kRank fl k` flagged moves, instead of the `k t` of `kleinProg`); it
makes the `k` moves of a trip, prints nothing, and ends with the answers of the flagged moves in
its output: for every flagged move `j < k` and target `X i`, the real word
`OUT[kRank fl j · t + i]` and the natural word `RBM[kRank fl j · t + i]` give (`kOutM`) the
distance in the piece from `tail (g j)` to `X i` when it is reached, `none` otherwise
(`odist`). -/
theorem kleinM_exec (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ B) (hB : n + 2 * nD ≤ B)
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
    (hmk : ∀ j < k, c₀.nmem (aMK n + j) = if fl j then 1 else 0) :
    ∃ c' steps, Exec P (B + 16 * (n + 1)) (kleinProgM B nD n k t) c₀ c' steps ∧
      steps ≤ 140 * (n + 1) + 21 +
        kleinOpsM (Fintype.card V) (Fintype.card F) nD S.card k (kRank fl k) t * opCostE n +
        kleinExtM (Fintype.card V) (Fintype.card F) nD S.card k (kRank fl k) t ∧
      (∃ R : ℕ → MoveData M S, IsTripUpTo M k g S ℓ k R) ∧
      (∀ j < k, fl j = true → ∀ i < t,
        kOutM nD n k t c' (kRank fl j) i =
          (odist 𝒢 (tripSrc M k g j) (X i)).map ((↑) : ℤ → ℝ)) ∧
      c'.output = c₀.output := by
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  unfold aOUT at hOUT
  exact lctE_adaptive_exec B n (kleinMS B nD n k t) P _ _ hc₀ _ fun c hc hS hout hmf _ => by
    have hm : ∀ a, a < B → c.rmem a = c₀.rmem a := fun a ha => (hmf a (Or.inl ha)).2
    have hmn : ∀ a, a < B → c.nmem a = c₀.nmem a := fun a ha => (hmf a (Or.inl ha)).1
    obtain ⟨c', F', G', m', hrun, hm', htrip, hd, hout'⟩ := kleinMS_orun le_rfl (by omega) hB
      (by unfold aOUT; omega) hRB hP H hR hL hK hG hO hX hI hoff hCr hT hc hS
      (fun d => by rw [hm _ (by have := hσ d; unfold aWT; omega)]; exact hwt d)
      (fun d => by rw [hm _ (by have := hσ d; unfold aPH; omega)]; exact hph d)
      (by rw [hm _ (by unfold aTL; omega)]; exact htl)
      (by rw [hm _ (by unfold aTH; omega)]; exact hth)
      (by rw [hm _ (by unfold aH0; omega)]; exact hh0)
      (fun j hj => by
        rw [hmn (aMK n + j) (by unfold aMK; unfold aRBM at hRB; omega)]; exact hmk j hj)
    exact ⟨c', F', G', m', hrun, hm', htrip, hd, hout'.trans hout⟩

end

/-- **The step bound of the masked program is `O(N log N + f t log N)`** on `n = 2 N` nodes,
`N = #V + #F + #D`, for `f` flagged moves and `t` targets (the `O(k)` steps of the unflagged
moves within `N`, as `k ≤ #V`). -/
theorem kleinM_steps_le {nV nF nD nS k f t : ℕ} (hN : 1 ≤ nV + nF + nD) (hS : nS ≤ nD)
    (hk : k ≤ nV) :
    140 * (2 * (nV + nF + nD) + 1) + 21 +
        kleinOpsM nV nF nD nS k f t * opCostE (2 * (nV + nF + nD)) +
        kleinExtM nV nF nD nS k f t ≤
      36500000 * ((nV + nF + nD) * BKMNW.lg (nV + nF + nD) +
        f * t * BKMNW.lg (nV + nF + nD)) := by
  set N := nV + nF + nD with hNdef
  set l := BKMNW.lg N with hldef
  have hl1 : 1 ≤ l := BKMNW.one_le_lg N
  have hlog2 : Nat.log 2 (2 * N) = l := by
    rw [hldef]; unfold BKMNW.lg
    rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
  have hops : kleinOpsM nV nF nD nS k f t ≤ 103 * N + f * t := by unfold kleinOpsM; omega
  have hcost : opCostE (2 * N) ≤ 353820 * l := by unfold opCostE; rw [hlog2]; omega
  have hext : kleinExtM nV nF nD nS k f t ≤ 390 * N + 14 * (f * t) := by
    unfold kleinExtM; omega
  have h1 : kleinOpsM nV nF nD nS k f t * opCostE (2 * N) ≤ (103 * N + f * t) * (353820 * l) :=
    Nat.mul_le_mul hops hcost
  have h2 : N ≤ N * l := Nat.le_mul_of_pos_right N hl1
  have h3 : f * t ≤ f * t * l := Nat.le_mul_of_pos_right _ hl1
  have e : (103 * N + f * t) * (353820 * l) = 36443460 * (N * l) + 353820 * (f * t * l) := by
    ring
  have e2 : 36500000 * (N * l + f * t * l) = 36500000 * (N * l) + 36500000 * (f * t * l) := by
    ring
  omega

end Klein

end PlanarFlow
