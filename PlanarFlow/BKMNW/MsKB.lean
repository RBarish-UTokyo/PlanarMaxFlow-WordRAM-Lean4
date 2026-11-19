module

public import PlanarFlow.BKMNW.MsKA

/-!
# The Klein start of an MSSP call, part B: the start from memory words (math)

What the encoder writes, as words in memory, and the properties of Klein's start they give:

* `KInMS` (Klein's encoding with the piece flags `IS` and the lengths `LN`), `KInMS.of` (from the
  map words `StEnc.KInM` and the new words), **`KInMS.kInput`** (`Klein.KInput`);
* **`kBnd_of`**, **`kTgt_of`**, **`kInit_ofK`** (`Klein.KBnd`, `Klein.KTgt`, `Klein.KInit` for any
  number `k` of roots, the words of `kiProg` at `ib + iIV nD n k`);
* the trip constants in natural numbers: `msL`, `msTh`, `msK`, `msH0`, `msZ`, **`msHI`** with
  `tripL_eq`, `tripTh_eq`, `tripH0_eq`, **`kleinHI_eq`** (`kleinHI = msHI` for lengths
  nonnegative on the piece, `w = tripW`); `resW_nat`;
* **`mkC0`**: the start configuration of Klein's real run (flags `MK`, the real words `WT`, `PH`,
  `tripL`, `tripTh`, `tripH0`, nothing else), `mkC0_wb`, `mkC0_rmem_*`, `mkC0_nmem`,
  **`kMem_mkC0`** (the low memory `kMem` of that start, cell by cell), `natCfg_mkC0_nreg`
  (all registers of `natCfg` zero).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset Function MSSP NsStep WordRAM WordRAM.Machine

/-! ### Klein's encoding with the piece -/

section Enc

variable {D' X Y : Type*} [Fintype D'] [DecidableEq D'] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

/-- **Klein's encoding of a map with a piece and lengths, in memory at `β`.** -/
structure KInMS (Q : CombMap D' X Y) (S : Finset D') (ℓ : D' → ℤ) {nD : ℕ} (σ : D' ≃ Fin nD)
    (ιv : X → ℕ) (ιg : D' → ℕ) (ιf : Y → ℕ) (ιe : D' → ℕ) (mem : ℕ → ℕ) (β : ℕ) : Prop where
  rv : ∀ d, mem (β + Klein.iRV nD + σ d) = σ (Q.rev d)
  nf : ∀ d, mem (β + Klein.iNF nD + σ d) = ιf (Q.face d)
  ne : ∀ d, mem (β + Klein.iNE nD + σ d) = ιe d
  ng : ∀ d, mem (β + Klein.iNG nD + σ d) = ιg d
  nt : ∀ d, mem (β + Klein.iNT nD + σ d) = ιv (Q.tail d)
  nh : ∀ d, mem (β + Klein.iNH nD + σ d) = ιv (Q.head d)
  is : ∀ d, mem (β + Klein.iIS nD + σ d) = if d ∈ S then 1 else 0
  ln : ∀ d ∈ S, mem (β + Klein.iLN nD + σ d) = (ℓ d).toNat
  ed : ∀ d, mem (β + Klein.iED nD + ιe d) = σ d ∨ mem (β + Klein.iED nD + ιe d) = σ (Q.rev d)

/-- The map words, kept, with the new words of the piece and the lengths. -/
theorem KInMS.of {Q : CombMap D' X Y} {S : Finset D'} {ℓ : D' → ℤ} {nD : ℕ} {σ : D' ≃ Fin nD}
    {ιv : X → ℕ} {ιg : D' → ℕ} {ιf : Y → ℕ} {ιe : D' → ℕ} {mem mem' : ℕ → ℕ} {β n : ℕ}
    (h : StEnc.KInM Q σ ιv ιg ιf ιe mem β) (hn : ∀ d, ιe d < n)
    (hagr : ∀ i, (i < 6 * nD ∨ (8 * nD ≤ i ∧ i < 8 * nD + n)) → mem' (β + i) = mem (β + i))
    (his : ∀ d, mem' (β + Klein.iIS nD + σ d) = if d ∈ S then 1 else 0)
    (hln : ∀ d ∈ S, mem' (β + Klein.iLN nD + σ d) = (ℓ d).toNat) :
    KInMS Q S ℓ σ ιv ιg ιf ιe mem' β := by
  have e : ∀ (o : ℕ) (d : D'), o + nD ≤ 6 * nD →
      mem' (β + o + σ d) = mem (β + o + σ d) := fun o d ho => by
    have := (σ d).2
    rw [add_assoc, hagr _ (Or.inl (by omega)), ← add_assoc]
  refine ⟨fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, his,
    hln, fun d => ?_⟩
  · rw [e _ d (by simp [Klein.iRV]; omega)]; exact h.rv d
  · rw [e _ d (by simp [Klein.iNF]; omega)]; exact h.nf d
  · rw [e _ d (by simp [Klein.iNE]; omega)]; exact h.ne d
  · rw [e _ d (by simp [Klein.iNG]; omega)]; exact h.ng d
  · rw [e _ d (by simp [Klein.iNT]; omega)]; exact h.nt d
  · rw [e _ d (by simp [Klein.iNH]; omega)]; exact h.nh d
  · have := hn d
    have e' : mem' (β + Klein.iED nD + ιe d) = mem (β + Klein.iED nD + ιe d) := by
      rw [add_assoc, hagr _ (Or.inr (by simp [Klein.iED]; omega)), ← add_assoc]
    rw [e']; exact h.ed d

/-- **An input holding the words of the memory is Klein's encoding with the piece.** -/
theorem KInMS.kInput {Q : CombMap D' X Y} {S : Finset D'} {ℓ : D' → ℤ} {nD : ℕ}
    {σ : D' ≃ Fin nD} {ιv : X → ℕ} {ιg : D' → ℕ} {ιf : Y → ℕ} {ιe : D' → ℕ} {mem : ℕ → ℕ}
    {β n : ℕ} (h : KInMS Q S ℓ σ ιv ιg ιf ιe mem β) (hn : ∀ d, ιe d < n) (P : Input)
    (hP : ∀ i, i < 8 * nD + n → P.data.getD i 0 = mem (β + i)) :
    Klein.KInput Q S ℓ σ ιv ιg ιf ιe P where
  rv d := by
    have := (σ d).2; rw [hP _ (by unfold Klein.iRV; omega), ← add_assoc]; exact h.rv d
  nf d := by
    have := (σ d).2; rw [hP _ (by unfold Klein.iNF; omega), ← add_assoc]; exact h.nf d
  ne d := by
    have := (σ d).2; rw [hP _ (by unfold Klein.iNE; omega), ← add_assoc]; exact h.ne d
  ng d := by
    have := (σ d).2; rw [hP _ (by unfold Klein.iNG; omega), ← add_assoc]; exact h.ng d
  nt d := by
    have := (σ d).2; rw [hP _ (by unfold Klein.iNT; omega), ← add_assoc]; exact h.nt d
  nh d := by
    have := (σ d).2; rw [hP _ (by unfold Klein.iNH; omega), ← add_assoc]; exact h.nh d
  is d := by
    have := (σ d).2; rw [hP _ (by unfold Klein.iIS; omega), ← add_assoc]; exact h.is d
  ln d hd := by
    have := (σ d).2; rw [hP _ (by unfold Klein.iLN; omega), ← add_assoc]; exact h.ln d hd
  ed d := by
    have := hn d
    rw [hP _ (by unfold Klein.iED; omega), ← add_assoc]; exact h.ed d

/-- **The boundary darts from the words.** -/
theorem kBnd_of {k : ℕ} {g : ℕ → D'} {nD : ℕ} {σ : D' ≃ Fin nD} {n : ℕ} {mem : ℕ → ℕ} {β : ℕ}
    (hG : ∀ i < k, mem (β + Klein.iGB nD n + i) = σ (g i)) (P : Input)
    (hP : ∀ i, i < Klein.iGB nD n + k → P.data.getD i 0 = mem (β + i)) :
    Klein.KBnd k g σ n P := fun i hi => by
  rw [hP _ (by omega), ← add_assoc]; exact hG i hi

open Classical in
/-- **The targets from the words.** -/
theorem kTgt_of {Q : CombMap D' X Y} {k : ℕ} {g : ℕ → D'} {S : Finset D'} {ℓ : D' → ℤ}
    {nD n : ℕ} {ιv : X → ℕ} {t : ℕ} {X' : ℕ → X} {mem : ℕ → ℕ} {β : ℕ}
    (hnr : ∀ i < t, ¬ IsRoot Q k g (X' i))
    (hxn : ∀ i < t, mem (β + Klein.iXT nD n k + i) = ιv (X' i))
    (hxr : ∀ i < t, mem (β + Klein.iXT nD n k + t + i) =
      if Reach (pieceGraph Q S ℓ) (Q.tail (g 0)) (X' i) then 1 else 0) (P : Input)
    (hP : ∀ i, i < Klein.iXT nD n k + 2 * t → P.data.getD i 0 = mem (β + i)) :
    Klein.KTgt Q k g S ℓ nD n ιv t X' P where
  nr := hnr
  xn i hi := by rw [hP _ (by omega), ← add_assoc]; exact hxn i hi
  xr i hi := by
    rw [hP _ (by omega), show β + (Klein.iXT nD n k + t + i) = β + Klein.iXT nD n k + t + i by
      ring]
    exact hxr i hi

end Enc

/-! ### `KInit` for any number of roots -/

section Init

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- **`KInit` from the words of `kiProg`** at `ib + iIV nD n k`. -/
theorem kInit_ofK {nD n k nF nV : ℕ} (σ : D ≃ Fin nD) (τv : F ≃ Fin nF) (τf : V ≃ Fin nV)
    {T₀ : STFlow.DTree M} {C₀ : STFlow.DTree M.dual} {ts : List F} {cs : List V}
    (hOT : Klein.Orders (STFlow.toDD T₀) ((List.finRange nF).map τv.symm) ts)
    (hOC : Klein.Orders C₀ ((List.finRange nV).map τf.symm) cs) {ofF ib : ℕ} {mem : ℕ → ℕ}
    (hIV : ∀ i (h : i < ((List.finRange nF).map τv.symm).length),
      mem (ib + Klein.iIV nD n k + i) = 1 + τv ((List.finRange nF).map τv.symm)[i])
    (hIT : ∀ i (h : i < ts.length), mem (ib + Klein.iIV nD n k + n + i) = σ (T₀.par ts[i]))
    (hIF : ∀ i (h : i < ((List.finRange nV).map τf.symm).length),
      mem (ib + Klein.iIV nD n k + 2 * n + i) = ofF + τf ((List.finRange nV).map τf.symm)[i])
    (hIC : ∀ i (h : i < cs.length), mem (ib + Klein.iIV nD n k + 3 * n + i) = σ (C₀.par cs[i]))
    (hH0 : mem (ib + Klein.iIV nD n k + 4 * n) = ((List.finRange nF).map τv.symm).length)
    (hH1 : mem (ib + Klein.iIV nD n k + 4 * n + 1) = ts.length)
    (hH2 : mem (ib + Klein.iIV nD n k + 4 * n + 2) = ((List.finRange nV).map τf.symm).length)
    (hH3 : mem (ib + Klein.iIV nD n k + 4 * n + 3) = cs.length)
    (P : Input) (hP : ∀ j, j < Klein.iHD nD n k + 4 → P.data.getD j 0 = mem (ib + j))
    (hnF : nF ≤ n) (hnV : nV ≤ n) :
    Klein.KInit M.dual σ (fun x => 1 + (τv x : ℕ)) (fun v => ofF + (τf v : ℕ)) n k
      (STFlow.toDD T₀) C₀ ((List.finRange nF).map τv.symm) ts ((List.finRange nV).map τf.symm)
      cs P := by
  have hts : ts.length ≤ nF := by
    have h1 := hOT.ylen; have h2 := Fintype.card_fin nF ▸ Fintype.card_congr τv; omega
  have hcs : cs.length ≤ nV := by
    have h1 := hOC.ylen; have h2 := Fintype.card_fin nV ▸ Fintype.card_congr τf; omega
  refine ⟨hOT, hOC, fun i h => ?_, fun i h => ?_, fun i h => ?_, fun i h => ?_, ?_, ?_, ?_, ?_⟩
  · have : i < nF := by simpa using h
    rw [hP _ (by simp only [Klein.iHD, Klein.iIT, Klein.iIF, Klein.iIC, Klein.iIV]; omega),
      ← add_assoc]
    exact hIV i h
  · rw [hP _ (by simp only [Klein.iHD, Klein.iIT, Klein.iIF, Klein.iIC, Klein.iIV]; omega)]
    unfold Klein.iIT; rw [← add_assoc, ← add_assoc]; exact hIT i h
  · have : i < nV := by simpa using h
    rw [hP _ (by simp only [Klein.iHD, Klein.iIT, Klein.iIF, Klein.iIC, Klein.iIV]; omega)]
    unfold Klein.iIF; rw [← add_assoc, ← add_assoc]; exact hIF i h
  · rw [hP _ (by simp only [Klein.iHD, Klein.iIT, Klein.iIF, Klein.iIC, Klein.iIV]; omega)]
    unfold Klein.iIC; rw [← add_assoc, ← add_assoc]; exact hIC i h
  · rw [hP _ (by unfold Klein.iHD; omega)]; unfold Klein.iHD; rw [← add_assoc]; exact hH0
  · rw [hP _ (by unfold Klein.iHD; omega)]; unfold Klein.iHD
    rw [show ib + (Klein.iIV nD n k + 4 * n + 1) = ib + Klein.iIV nD n k + 4 * n + 1 by ring]
    exact hH1
  · rw [hP _ (by unfold Klein.iHD; omega)]; unfold Klein.iHD
    rw [show ib + (Klein.iIV nD n k + 4 * n + 2) = ib + Klein.iIV nD n k + 4 * n + 2 by ring]
    exact hH2
  · rw [hP _ (by unfold Klein.iHD; omega)]; unfold Klein.iHD
    rw [show ib + (Klein.iIV nD n k + 4 * n + 3) = ib + Klein.iIV nD n k + 4 * n + 3 by ring]
    exact hH3

end Init

/-! ### The constants of the trip in natural numbers -/

/-- `tripL`. -/
def msL (w nV : ℕ) : ℕ := 4 * nV * w + w + 1
/-- `tripTh`. -/
def msTh (w nV : ℕ) : ℕ := 2 * nV * w + w + 1
/-- `tripK`. -/
def msK (w nV : ℕ) : ℕ := 6 * nV * w + 2 * w + 1
/-- `tripH0`. -/
def msH0 (w nV k : ℕ) : ℕ := msTh w nV + (k + 1) * ((nV + 1) * msK w nV)
/-- `kleinZ`. -/
def msZ (w nV nF k : ℕ) : ℕ := 2 * nV * w + 2 * nF * (msH0 w nV k + msL w nV + 2 * nV * w)
/-- **`kleinHI`**. -/
def msHI (w nV nF k : ℕ) : ℕ :=
  30 * (msH0 w nV k + msL w nV + w + 2 * nV * w + msZ w nV nF k) + 12 * msK w nV +
    8 * (msL w nV + w)

section Trip

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {S : Finset D} {ℓ : D → ℤ}

lemma tripW_eq (hnn : ∀ d ∈ S, 0 ≤ ℓ d) : Klein.tripW S ℓ = ∑ d ∈ S, ℓ d :=
  Finset.sum_congr rfl fun d hd => abs_of_nonneg (hnn d hd)

lemma tripW_toNat (hnn : ∀ d ∈ S, 0 ≤ ℓ d) :
    ((Klein.tripW S ℓ).toNat : ℤ) = Klein.tripW S ℓ :=
  Int.toNat_of_nonneg Klein.tripW_nonneg

lemma tripL_eq : Klein.tripL V S ℓ =
    (msL (Klein.tripW S ℓ).toNat (Fintype.card V) : ℤ) := by
  have h := Int.toNat_of_nonneg (Klein.tripW_nonneg (S := S) (ℓ := ℓ))
  simp only [Klein.tripL, Klein.tripB, msL]; push_cast; rw [h]; ring

lemma tripTh_eq : Klein.tripTh V S ℓ =
    (msTh (Klein.tripW S ℓ).toNat (Fintype.card V) : ℤ) := by
  have h := Int.toNat_of_nonneg (Klein.tripW_nonneg (S := S) (ℓ := ℓ))
  simp only [Klein.tripTh, Klein.tripL, Klein.tripB, msTh]; push_cast; rw [h]; ring

lemma tripK_eq : Klein.tripK V S ℓ =
    (msK (Klein.tripW S ℓ).toNat (Fintype.card V) : ℤ) := by
  have h := Int.toNat_of_nonneg (Klein.tripW_nonneg (S := S) (ℓ := ℓ))
  have hL := Klein.tripL_nonneg (V := V) (S := S) (ℓ := ℓ)
  have hW := Klein.tripW_nonneg (S := S) (ℓ := ℓ)
  simp only [Klein.tripK, Klein.driftK, msK]
  rw [abs_of_nonneg hL, abs_of_nonneg hW,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hW), tripL_eq]
  simp only [msL]; push_cast; rw [h]; ring

lemma tripH0_eq (k : ℕ) : Klein.tripH0 V S ℓ k =
    (msH0 (Klein.tripW S ℓ).toNat (Fintype.card V) k : ℤ) := by
  simp only [Klein.tripH0, msH0, tripTh_eq, tripK_eq]; push_cast; ring

/-- **The bound `kleinHI` in natural numbers.** -/
theorem kleinHI_eq (k : ℕ) : Klein.kleinHI V F S ℓ k =
    (msHI (Klein.tripW S ℓ).toNat (Fintype.card V) (Fintype.card F) k : ℝ) := by
  have h := Int.toNat_of_nonneg (Klein.tripW_nonneg (S := S) (ℓ := ℓ))
  have eW : (Klein.tripW S ℓ : ℝ) = ((Klein.tripW S ℓ).toNat : ℝ) := by
    rw [← h]; push_cast; rw [Int.toNat_natCast]
  have eL : (Klein.tripL V S ℓ : ℝ) = (msL (Klein.tripW S ℓ).toNat (Fintype.card V) : ℝ) := by
    rw [tripL_eq]; push_cast; rfl
  have eT : (Klein.tripTh V S ℓ : ℝ) = (msTh (Klein.tripW S ℓ).toNat (Fintype.card V) : ℝ) := by
    rw [tripTh_eq]; push_cast; rfl
  have eK : (Klein.tripK V S ℓ : ℝ) = (msK (Klein.tripW S ℓ).toNat (Fintype.card V) : ℝ) := by
    rw [tripK_eq]; push_cast; rfl
  have eH : (Klein.tripH0 V S ℓ k : ℝ) = (msH0 (Klein.tripW S ℓ).toNat (Fintype.card V) k : ℝ) :=
    by rw [tripH0_eq]; push_cast; rfl
  simp only [Klein.kleinHI, Klein.kleinAI, Klein.kleinA, Klein.kleinZ, eW, eL, eT, eK, eH]
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  simp only [msHI, msZ]
  push_cast
  ring

end Trip

/-- The residue of a natural value below the modulus is the value. -/
lemma resW_nat {Mo : ℕ} {z : ℤ} (h0 : 0 ≤ z) (h1 : z < Mo) : Klein.resW Mo (z : ℝ) = z.toNat := by
  unfold Klein.resW
  rw [Int.floor_intCast, Int.emod_eq_of_lt h0 h1]

/-! ### The start configuration of Klein's run -/

section C0

variable {D' : Type*}

/-- **The start configuration**: the flags `MK` at `aMK n + j`, the real words `WT`, `PH` of the
darts and `tripL`, `tripTh`, `tripH0`; everything else zero. -/
noncomputable def mkC0 (nD n k : ℕ) (fl : ℕ → Bool) (σ : D' ≃ Fin nD) (wt φ : D' → ℤ)
    (L Th H0 : ℤ) : Config where
  pc := 0
  nreg _ := 0
  rreg _ := 0
  nmem a := if n ≤ a ∧ a < n + k then (if fl (a - n) then 1 else 0) else 0
  rmem a := if h : a < nD then (wt (σ.symm ⟨a, h⟩) : ℝ)
    else if h2 : a < 2 * nD then (φ (σ.symm ⟨a - nD, by omega⟩) : ℝ)
    else if a = 3 * nD then (L : ℝ) else if a = 3 * nD + 1 then (Th : ℝ)
    else if a = 3 * nD + 2 then (H0 : ℝ) else 0
  output := []

variable {nD n k : ℕ} {fl : ℕ → Bool} {σ : D' ≃ Fin nD} {wt φ : D' → ℤ} {L Th H0 : ℤ}

lemma mkC0_wb {W : ℕ} (hW : 1 ≤ W) : WordsBounded W (mkC0 nD n k fl σ wt φ L Th H0) := by
  unfold WordsBounded
  refine ⟨fun r => by simp [mkC0], fun a => ?_⟩
  show (if n ≤ a ∧ a < n + k then (if fl (a - n) then 1 else 0) else 0) ≤ W
  split_ifs <;> omega

lemma mkC0_wt (d : D') : (mkC0 nD n k fl σ wt φ L Th H0).rmem (Klein.aWT + σ d) = wt d := by
  have := (σ d).2
  simp only [mkC0, Klein.aWT, zero_add, this, ↓reduceDIte]
  simp

lemma mkC0_ph (d : D') : (mkC0 nD n k fl σ wt φ L Th H0).rmem (Klein.aPH nD + σ d) = φ d := by
  have := (σ d).2
  simp only [mkC0, Klein.aPH, show ¬ nD + (σ d : ℕ) < nD by omega,
    show nD + (σ d : ℕ) < 2 * nD by omega, ↓reduceDIte]
  simp

lemma mkC0_tl : (mkC0 nD n k fl σ wt φ L Th H0).rmem (Klein.aTL nD) = L := by
  simp [mkC0, Klein.aTL]; split_ifs <;> first | omega | rfl

lemma mkC0_th : (mkC0 nD n k fl σ wt φ L Th H0).rmem (Klein.aTH nD) = Th := by
  simp [mkC0, Klein.aTH]; split_ifs <;> first | omega | rfl

lemma mkC0_h0 : (mkC0 nD n k fl σ wt φ L Th H0).rmem (Klein.aH0 nD) = H0 := by
  simp [mkC0, Klein.aH0]; split_ifs <;> first | omega | rfl

lemma mkC0_mk {j : ℕ} (hj : j < k) :
    (mkC0 nD n k fl σ wt φ L Th H0).nmem (Klein.aMK n + j) = if fl j then 1 else 0 := by
  simp only [mkC0, Klein.aMK, show n ≤ n + j ∧ n + j < n + k from ⟨by omega, by omega⟩,
    and_self, ↓reduceIte, Nat.add_sub_cancel_left]

lemma mkC0_rr (r : ℕ) : ∃ z : ℤ, (mkC0 nD n k fl σ wt φ L Th H0).rreg r = z := ⟨0, by simp [mkC0]⟩

lemma mkC0_rm (a : ℕ) : ∃ z : ℤ, (mkC0 nD n k fl σ wt φ L Th H0).rmem a = z := by
  simp only [mkC0]
  split_ifs
  exacts [⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨0, by simp⟩]

/-- The registers of the simulating configuration are all zero. -/
lemma natCfg_mkC0_nreg {W Mo β : ℕ} (r : ℕ) :
    (Klein.natCfg 201 W Mo β (mkC0 nD n k fl σ wt φ L Th H0)).nreg r = 0 := by
  simp only [Klein.natCfg, mkC0]
  split_ifs
  · rfl
  · simp [Klein.resW]
  · rfl

/-- **The low memory of the start, cell by cell** (`B + 16 (n + 1) = W`, `β = W + 1`). -/
lemma kMem_mkC0 {B Hc : ℕ} {Pin : Input} {a : ℕ} :
    MsCall.kMem B n Hc (mkC0 nD n k fl σ wt φ L Th H0) Pin a =
      if a ≤ Klein.kleinWN B n Hc then
        (if a ≤ B + 16 * (n + 1) then
          (if n ≤ a ∧ a < n + k then (if fl (a - n) then 1 else 0) else 0)
        else if B + 16 * (n + 1) + 1 ≤ a ∧ a ≤ B + 16 * (n + 1) + 1 + (B + 16 * (n + 1)) then
          Klein.resW (2 * Hc + 1) ((mkC0 nD n k fl σ wt φ L Th H0).rmem
            (a - (B + 16 * (n + 1) + 1)))
        else 0)
      else Pin.data.getD (a - (Klein.kleinWN B n Hc + 1)) 0 := by
  simp only [MsCall.kMem, Klein.natCfg, mkC0]

end C0

end MsEnc

end BKMNW

end PlanarFlow
