module

public import PlanarFlow.BKMNW.MsEncC3
public import PlanarFlow.BKMNW.MsKC
public import PlanarFlow.BKMNW.MsStB3
public import PlanarFlow.BKMNW.MsStW3

/-!
# The composed MSSP encoder, part B: stages A and B joined

* notation of the composed encoder: `mσ` (the numbering of the darts of the cut), `mnD`,
  `mN` (the map `(cutMap …).dual.dual` of the cut `ccut`), **`mkl`** (the isolating lengths
  `MsCall.kLen (ccut …) (treeW Ct) mσ` of the tree `Ct` of stage B1), `mLD` (Dijkstra's lengths of
  `ms_tree`: `mkl` on the piece, `H` on the first ring dart, `2H` elsewhere);
* `StA.regs` (stage A's facts survive a change of the registers `≥ 8297`);
* `sum_piece` (a sum over the numbers below `nP` is a sum over the piece);
* **`msA_exec`** (`msA1 ; msA2`), **`StB`** (what stages A and B leave), **`msB_exec`**
  (`svSet ; msB1 ; rsSet ; msB2 ; msB3 ; msB4`): Klein's encoding with the piece and the isolating
  lengths (`KInMS`), `w = (tripW piece mkl).toNat`, `H = w + 1`, `N₁`, Dijkstra's lengths.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-! ### Notation -/

/-- The number of darts of the cut. -/
noncomputable abbrev mnD (Pa : SPath M) (en : ℕ → D) (m : ℕ) : ℕ :=
  nEc Pa.darts en m + 4 * nTc M Pa.darts en m

/-- The numbering of the darts of the cut. -/
noncomputable abbrev mσ {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) :
    CutD M Pa.darts ≃ Fin (mnD Pa en m) :=
  StEnc.enEq (cQ h Pa hk)

/-- The map of the cut of the call. -/
noncomputable abbrev mN (Pa : SPath M) : CombMap (CutD M Pa.darts) (CutV M Pa.darts) (CutF M Pa.darts) :=
  (cutMap Pa.rev_mem_darts').dual.dual

/-- **The isolating lengths of the call** for the tree `Ct`. -/
noncomputable abbrev mkl (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) (ℓ : D → ℤ) (hnn : ∀ e, 0 ≤ ℓ e)
    (Ct : STFlow.DTree (mN Pa)) : CutD M Pa.darts → ℤ :=
  MsCall.kLen (ccut hM hrot Pa hk ℓ fun e _ => hnn e) (MSSP.treeW Ct) (mσ h Pa hk)

/-- Dijkstra's lengths of `ms_tree`. -/
def mLD {D' : Type*} [DecidableEq D'] (S : Finset D') (kl : D' → ℤ) (e₀ : D') (H : ℤ) (d : D') :
    ℤ :=
  if d ∈ S then kl d else if d = e₀ then H else 2 * H

/-! ### Small facts -/

variable {P : Input} {W : ℕ}

/-- Stage A's facts survive a change of the registers `≥ 8297`. -/
lemma StA.regs {hM : M.IsPlane} {hrot : M.RotTrans} {en : ℕ → D} {m : ℕ} {h : EnumOK M en m}
    {Pa : SPath M} {hk : 0 < Pa.k} {p q : ℕ} {c₀ c c' : Config} {nF nV : ℕ}
    {τv : CutV M Pa.darts ≃ Fin nF} {τf : CutF M Pa.darts ≃ Fin nV}
    (hA : StA hM hrot h Pa hk p q c₀ c τv τf) (hr : ∀ r < 8297, c'.nreg r = c.nreg r)
    (hm : c'.nmem = c.nmem) (hrr : c'.rreg = c.rreg) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) (hE : ∀ r, ¬ EScr r → c'.nreg r = c.nreg r) :
    StA hM hrot h Pa hk p q c₀ c' τv τf where
  lay j hj := by rw [hr _ (by omega)]; exact hA.lay j hj
  per := by rw [hr _ (by omega)]; exact hA.per
  ncl := by rw [hr _ (by omega)]; exact hA.ncl
  r28 := by rw [hr _ (by omega)]; exact hA.r28
  r30 := by rw [hr _ (by omega)]; exact hA.r30
  r50 := by rw [hr _ (by omega)]; exact hA.r50
  r57 := by rw [hr _ (by omega)]; exact hA.r57
  r59 := by rw [hr _ (by omega)]; exact hA.r59
  tr := by rw [hm]; exact hA.tr
  fl := by rw [hm]; exact hA.fl
  lf := by rw [hm]; exact hA.lf
  cs := by rw [hm]; exact hA.cs
  cn := by rw [hm]; exact hA.cn
  rk := by rw [hm]; exact hA.rk
  kin := by rw [hm]; exact hA.kin
  g := by rw [hm]; exact hA.g
  gg0 := by rw [hm]; exact hA.gg0
  gg1 := by rw [hm]; exact hA.gg1
  mem := by rw [hm]; exact hA.mem
  reg r hr' := (hE r hr').trans (hA.reg r hr')
  rr := hrr.trans hA.rr
  rm := hrm.trans hA.rm
  out := ho.trans hA.out

/-- A sum over the numbers below `nP` is a sum over the darts numbered below `nP`. -/
lemma sum_piece {D' : Type*} {S : Finset D'} {nP nD : ℕ} (σ : D' ≃ Fin nD)
    (hS : ∀ d, d ∈ S ↔ (σ d : ℕ) < nP) (hnP : nP ≤ nD) (f : ℕ → ℕ) :
    ∑ j ∈ range nP, f j = ∑ d ∈ S, f (σ d) := by
  symm
  refine Finset.sum_nbij (fun d => (σ d : ℕ)) (fun d hd => ?_) (fun d _ d' _ e => ?_)
    (fun j hj => ?_) (fun d _ => rfl)
  · exact mem_range.2 ((hS d).1 hd)
  · exact σ.injective (Fin.ext e)
  · have hj' : j < nP := mem_range.1 hj
    refine ⟨σ.symm ⟨j, by omega⟩, ?_, ?_⟩
    · show σ.symm ⟨j, _⟩ ∈ S
      rw [hS]; simp [hj']
    · simp

/-- **Stage A.** -/
def msA : Stmt := .seq msA1 msA2

/-- **Stage A on the machine** (`msA1_exec`, `msA2_exec`). -/
theorem msA_exec (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} {Lmax q : ℕ} {ts : ℕ → D}
    {RVb RTb Pb Lb Qb Ob p : ℕ} (c : Config) (hc : WordsBounded W c)
    (hI : MsCall.MsIn M en m Pa ℓ Lmax q ts RVb RTb Pb Lb Qb Ob p c)
    (hRV : RVb + m ≤ p) (hRT : RTb + m ≤ p) (hPb : Pb + Pa.k ≤ p)
    (hW : p + 860 * m + 100 + 2 * q ≤ W) (h860 : 860 ≤ W) :
    ∃ e t nF nV, ∃ (τv : CutV M Pa.darts ≃ Fin nF) (τf : CutF M Pa.darts ≃ Fin nV),
      Exec P W msA c e t ∧ t ≤ costA1 m Pa.k + costA2 m ∧ StA hM hrot h Pa hk p q c e τv τf := by
  obtain ⟨c₁, t₁, e₁, ht₁, hA⟩ := msA1_exec (P := P) hM hrot h Pa hk c hc hI hRV hRT hPb hW h860
  have hm : c₁.nreg 8000 = m := by rw [hA.reg _ (by simp only [EScr]; omega)]; exact hI.r00
  have hp : c₁.nreg 8009 = p := by rw [hA.reg _ (by simp only [EScr]; omega)]; exact hI.r09
  obtain ⟨c₂, t₂, nF, nV, τv, τf, e₂, ht₂, hA2⟩ :=
    msA2_exec (P := P) hM hrot h Pa hk c c₁ e₁.wb_right hA hm hp hW
  exact ⟨c₂, t₁ + t₂, nF, nV, τv, τf, e₁.seq e₂, by omega, hA2⟩

/-- `svSet` with the frame of all the other registers. -/
theorem svSet_exec' (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W svSet c c' t ∧ t = 3 ∧ c'.nreg 8297 = c.nreg 7950 ∧
      c'.nreg 8298 = c.nreg 7957 ∧ c'.nreg 8299 = c.nreg 7959 ∧
      (∀ r, r ≠ 8297 → r ≠ 8298 → r ≠ 8299 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold svSet
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, fun r a b d => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | rfl
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-- The lengths of the call are bounded by `Lmax`. -/
lemma len_le_of_in {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) {ℓ : D → ℤ} {Lmax Lb : ℕ}
    {mem : ℕ → ℕ} (hln : ∀ i < m, (mem (Lb + i) : ℤ) = ℓ (en i) ∧ mem (Lb + i) ≤ Lmax)
    (e : D) : ℓ e ≤ Lmax := by
  have := hln _ (ixOf_lt h e)
  rw [en_ixOf h e] at this
  have h2 : ((mem (Lb + ixOf en m e) : ℕ) : ℤ) ≤ (Lmax : ℤ) := by exact_mod_cast this.2
  rw [this.1] at h2; exact h2

/-- **The isolating lengths are positive and below `N₁ (Lmax + 1)`.** -/
lemma mkl_bound (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e) {Lmax : ℕ}
    (hL : ∀ e, ℓ e ≤ Lmax) (Ct : STFlow.DTree (mN Pa)) (d : CutD M Pa.darts) :
    0 < mkl hM hrot h Pa hk ℓ hnn Ct d ∧
      mkl hM hrot h Pa hk ℓ hnn Ct d < (MSSP.isoN1 (Fintype.card (CutV M Pa.darts))
        (Fintype.card (CutD M Pa.darts)) (Fintype.card (CutF M Pa.darts)) : ℤ) * (Lmax + 1) := by
  have hn1 : 1 ≤ Fintype.card (CutV M Pa.darts) :=
    Fintype.card_pos_iff.2 ⟨Sum.inl (M.face (Pa.d 0))⟩
  have hι : ∀ d : CutD M Pa.darts, ((mσ h Pa hk d : ℕ)) < Fintype.card (CutD M Pa.darts) :=
    fun d => by rw [card_cutD h]; exact (mσ h Pa hk d).2
  have hcl0 : 0 ≤ cutLen M Pa.darts ℓ d := by
    rcases d with e | t <;> simp only [cutLen]
    · exact hnn e.1
    · exact le_rfl
  have hclL : cutLen M Pa.darts ℓ d ≤ Lmax := by
    rcases d with e | t <;> simp only [cutLen]
    · exact hL e.1
    · exact_mod_cast Nat.zero_le _
  have := MSSP.isoLen_lt (D := CutD M Pa.darts) (w := MSSP.treeW Ct) (ℓ := cutLen M Pa.darts ℓ)
    (ι := fun d => (mσ h Pa hk d : ℕ)) (MSSP.abs_treeW_le Ct) hι hn1 (d := d) hcl0
  obtain ⟨h1, h2⟩ := this
  refine ⟨h1, lt_of_lt_of_le h2 ?_⟩
  have hN : (0 : ℤ) ≤ (MSSP.isoN1 (Fintype.card (CutV M Pa.darts))
        (Fintype.card (CutD M Pa.darts)) (Fintype.card (CutF M Pa.darts)) : ℤ) := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hN

/-- **What stages A and B leave.** -/
structure StB (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) (ℓ : D → ℤ) (hnn : ∀ e, 0 ≤ ℓ e) (p q : ℕ) (c₀ e : Config)
    {nF nV : ℕ} (τv : CutV M Pa.darts ≃ Fin nF) (τf : CutF M Pa.darts ≃ Fin nV)
    (Ct : STFlow.DTree (mN Pa)) : Prop where
  lay : ∀ j < 17, e.nreg (8280 + j) = (msLayV m p q).getD j 0
  per : e.nreg 8156 = fixPer M Pa
  ncl : e.nreg 8157 = (fixCornerL M Pa).length
  r28 : e.nreg 8228 = nEc Pa.darts en m
  r50 : e.nreg 7950 = mnD Pa en m
  r57 : e.nreg 7957 = nF
  r59 : e.nreg 7959 = nV
  r97 : e.nreg 8297 = mnD Pa en m
  r98 : e.nreg 8298 = nF
  r99 : e.nreg 8299 = nV
  rw : e.nreg 7342 = (Klein.tripW (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct)).toNat
  rH : e.nreg 7335 =
    (Klein.tripW (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct)).toNat + 1
  rN1 : e.nreg 7328 = MSSP.isoN1 nF (mnD Pa en m) nV
  tr : ∀ s < fixPer M Pa, e.nmem (p + 6 * m + s) = ixOf en m ((tour M Pa.darts)^[s] (Pa.d 0))
  fl : ∀ i < m, e.nmem (p + m + i) = labI M en m i + 1
  cs : ∀ r < (fixCornerL M Pa).length,
    e.nmem (p + 8 * m + r) = (fixCornerL M Pa).getD r 0 ∧
      e.nmem (p + 7 * m + r) =
        ixOf en m ((tour M Pa.darts)^[(fixCornerL M Pa).getD r 0] (Pa.d 0))
  cn : ∀ i < m, M.face (en i) ∈ Pa.faces → ∃ r < (fixCornerL M Pa).length,
    e.nmem (p + 9 * m - 1 + (labI M en m i + 1)) = r ∧
      fixCorner M Pa ((fixCornerL M Pa).getD r 0) = M.face (en i)
  rk : ∀ i < m, e.nmem (p + 13 * m + i) = cE Pa.darts en i ∧
    e.nmem (p + 14 * m + i) = cT M Pa.darts en i
  kin : KInMS (mN Pa) (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct) (mσ h Pa hk)
    (fun x => 1 + (τv x : ℕ)) (StEnc.ιG _ (cQ h Pa hk))
    (fun y => 2 * mnD Pa en m + 1 + (τf y : ℕ)) (StEnc.ιE _ (cQ h Pa hk)) e.nmem (aIM m p)
  g : ∀ i < fixPer M Pa, e.nmem (aIM m p + 12 * mnD Pa en m + 1 + i) =
    mσ h Pa hk (cutG Pa.rev_mem_darts' (fixT0 Pa hk) i)
  gg0 : e.nmem (aGG m p) = mσ h Pa hk (cD0 Pa hk)
  gg1 : e.nmem (aGG m p + 1) = mσ h Pa hk (cD0 Pa hk)
  ld : ∀ d, e.nmem (aLD m p + mσ h Pa hk d) =
    (mLD (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct) (cD0 Pa hk)
      (((Klein.tripW (cutPiece M Pa.darts) (mkl hM hrot h Pa hk ℓ hnn Ct)).toNat + 1 : ℕ) : ℤ)
      d).toNat
  ctr : Ct.root = (cutMap Pa.rev_mem_darts').dual.tail (cD0 Pa hk)
  mem : ∀ a, (a < p ∨ p + 860 * m + 100 + 2 * q ≤ a) → e.nmem a = c₀.nmem a
  reg : ∀ r, ¬ EScr r → e.nreg r = c₀.nreg r
  rr : e.rreg = c₀.rreg
  rm : e.rmem = c₀.rmem
  out : e.output = c₀.output

/-- The first part of stage B. -/
def msBa : Stmt := .seq svSet (.seq msB1 (.seq rsSet msB2))

/-- The second part of stage B. -/
def msBb : Stmt := .seq msB3 msB4

/-- **Stage B.** -/
def msB : Stmt := .seq msBa msBb

/-- The step bound of stage B. -/
def costB (m : ℕ) : ℕ :=
  3 + (11 + StEnc.ivCost (5 * m) (2 * m + 1)) + 3 + (12 + 5 * (5 * m) + 5 + (8 + 8) * m + 5) +
    (17 + (15 + 8) * (5 * m) + 5) + (4 + (6 * (5 * m) + 5) + 10 + (18 + 8) * (5 * m) + 5)

set_option maxHeartbeats 4000000 in
/-- **Stage B, first part** (`svSet ; msB1 ; rsSet ; msB2`): the tree `Ct` of the isolating
weight and the copy lengths. -/
theorem msBa_exec (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e)
    {p q Lb nF nV : ℕ} (τv : CutV M Pa.darts ≃ Fin nF) (τf : CutF M Pa.darts ≃ Fin nV)
    (c₀ c : Config) (hc : WordsBounded W c) (hA : StA hM hrot h Pa hk p q c₀ c τv τf)
    (r00' : c₀.nreg 8000 = m) (r05 : c₀.nreg 8005 = Lb) (r09' : c₀.nreg 8009 = p)
    (hln : ∀ i < m, (c₀.nmem (Lb + i) : ℤ) = ℓ (en i))
    (lLb : Lb + m ≤ p) (hW : p + 860 * m + 100 + 2 * q ≤ W) :
    ∃ e t, ∃ Ct : STFlow.DTree (mN Pa), Exec P W msBa c e t ∧
      t ≤ 3 + (11 + StEnc.ivCost (5 * m) (2 * m + 1)) + 3 +
        (12 + 5 * (5 * m) + 5 + (8 + 8) * m + 5) ∧
      Ct.root = (cutMap Pa.rev_mem_darts').dual.tail (cD0 Pa hk) ∧
      (∀ d, (e.nmem (aWM m p + mσ h Pa hk d) : ℤ) = nV + MSSP.treeW Ct d) ∧
      (∀ d, (e.nmem (aCL m p + mσ h Pa hk d) : ℤ) = cutLen M Pa.darts ℓ d) ∧
      e.nreg 7950 = mnD Pa en m ∧ e.nreg 7957 = nF ∧ e.nreg 7959 = nV ∧
      e.nreg 8297 = mnD Pa en m ∧ e.nreg 8298 = nF ∧ e.nreg 8299 = nV ∧
      (∀ r, (r < 1400 ∨ 8000 ≤ r) → r ≠ 8264 → r ≠ 8265 → (r < 8200 ∨ 8219 < r) →
        (r < 8297 ∨ 8299 < r) → e.nreg r = c.nreg r) ∧
      (∀ a, (a < aZi m p ∨ aZi m p + 60 * m + 30 ≤ a) →
        (a < aWM m p ∨ aWM m p + mnD Pa en m ≤ a) → (a < aCL m p ∨ aCL m p + mnD Pa en m ≤ a) →
        (a < aDU m p ∨ aDU m p + mnD Pa en m ≤ a) → e.nmem a = c.nmem a) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  have eD : mnD Pa en m = nEc Pa.darts en m + 4 * nTc M Pa.darts en m := rfl
  have lay := hA.lay
  have l7 : c.nreg 8287 = p + 311 * m + 52 := lay 7 (by omega)
  have l9 : c.nreg 8289 = p + 321 * m + 52 := lay 9 (by omega)
  have r00 : c.nreg 8000 = c₀.nreg 8000 := hA.reg _ (by simp only [EScr]; omega)
  have r05' : c.nreg 8005 = Lb := by rw [hA.reg _ (by simp only [EScr]; omega)]; exact r05
  have r09 : c.nreg 8009 = c₀.nreg 8009 := hA.reg _ (by simp only [EScr]; omega)
  -- save
  obtain ⟨c₁, t₁, e₁, ht₁, s97, s98, s99, sR, sm, sr, srm, so⟩ := svSet_exec' (P := P) c hc
  have hA1 : StA hM hrot h Pa hk p q c₀ c₁ τv τf :=
    StA.regs hA (fun r hr => sR r (by omega) (by omega) (by omega)) sm sr srm so
      (fun r hr => sR r (by simp only [EScr] at hr; omega) (by simp only [EScr] at hr; omega)
        (by simp only [EScr] at hr; omega))
  -- the isolating weight
  obtain ⟨c₂, t₂, Ct, e₂, ht₂, hCr, hWM, M₂, R₂, rr₂, rm₂, o₂⟩ :=
    msB1_exec (P := P) hM hrot h Pa hk τv τf c₀ c₁ e₁.wb_right hA1 hW
  -- restore
  obtain ⟨c₃, t₃, e₃, ht₃, q50, q57, q59, qR, qm, qr, qrm, qo⟩ := rsSet_exec (P := P) c₂ e₂.wb_right
  have k3 : ∀ r, (r < 1400 ∨ 8000 ≤ r) → r ≠ 8264 → r ≠ 8265 → (r < 8297 ∨ 8299 < r) →
      c₃.nreg r = c.nreg r := fun r h1 h2 h3 h4 => by
    rw [qR r (by omega) (by omega) (by omega), R₂ r h1 h2 h3, sR r (by omega) (by omega) (by omega)]
  have m3 : ∀ a, (a < aZi m p ∨ aZi m p + 60 * m + 30 ≤ a) →
      (a < aWM m p ∨ aWM m p + mnD Pa en m ≤ a) → c₃.nmem a = c.nmem a := fun a h1 h2 => by
    rw [qm, M₂ a h1 h2, sm]
  have q50' : c₃.nreg 7950 = mnD Pa en m := by
    rw [q50, R₂ _ (by omega) (by omega) (by omega), s97]; exact hA.r50
  have q57' : c₃.nreg 7957 = nF := by
    rw [q57, R₂ _ (by omega) (by omega) (by omega), s98]; exact hA.r57
  have q59' : c₃.nreg 7959 = nV := by
    rw [q59, R₂ _ (by omega) (by omega) (by omega), s99]; exact hA.r59
  -- the copy lengths
  obtain ⟨c₄, t₄, e₄, ht₄, hcp, hz, M₄, R₄, rr₄, rm₄, o₄⟩ :=
    msB2_exec (P := P) (en := en) (m := m) Pa (p := p) (Lb := Lb) (nD := mnD Pa en m)
      (CL := p + 311 * m + 52) (DU := p + 321 * m + 52) c₃ e₃.wb_right
      (by rw [k3 _ (by omega) (by omega) (by omega) (by omega), r00]; exact r00')
      (by rw [k3 _ (by omega) (by omega) (by omega) (by omega)]; exact r05')
      (by rw [k3 _ (by omega) (by omega) (by omega) (by omega), r09]; exact r09')
      q50' (by rw [k3 _ (by omega) (by omega) (by omega) (by omega)]; exact l7)
      (by rw [k3 _ (by omega) (by omega) (by omega) (by omega)]; exact l9) (by omega)
      (fun i hi => by
        rw [m3 _ (Or.inl (by unfold aZi; omega)) (Or.inl (by unfold aWM; omega))]
        exact hA.lf i hi)
      (fun i hi => by
        rw [m3 _ (Or.inl (by unfold aZi; omega)) (Or.inl (by unfold aWM; omega))]
        exact (hA.rk i hi).1)
      lLb (by omega) (by omega) (by omega) (by omega)
  have hln3 : ∀ i < m, (c₃.nmem (Lb + i) : ℤ) = ℓ (en i) := fun i hi => by
    rw [m3 _ (Or.inl (by unfold aZi; omega)) (Or.inl (by unfold aWM; omega)),
      hA.mem _ (Or.inl (by omega)) (Or.inl (by unfold aDU; omega))]
    exact hln i hi
  have k4 : ∀ r, (r < 1400 ∨ 8000 ≤ r) → r ≠ 8264 → r ≠ 8265 → (r < 8200 ∨ 8219 < r) →
      (r < 8297 ∨ 8299 < r) → c₄.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 => by
    rw [R₄ r (by omega) (by omega) h4 h2, k3 r h1 h2 h3 h5]
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), Ct, e₁.seq (e₂.seq (e₃.seq e₄)), ?_, hCr, fun d => ?_,
    fun d => ?_, ?_, ?_, ?_, ?_, ?_, ?_, k4, fun a h1 h2 h3 h4 => ?_, by rw [rr₄, qr, rr₂, sr],
    by rw [rm₄, qrm, rm₂, srm], by rw [o₄, qo, o₂, so]⟩
  · have : 5 * mnD Pa en m ≤ 5 * (5 * m) := by omega
    omega
  · have := (mσ h Pa hk d).2
    rw [M₄ _ (Or.inl (by unfold aWM; omega)) (Or.inl (by unfold aWM; omega)), qm]; exact hWM d
  · exact cl_cutLen h Pa hk hnn c₄.nmem c₃.nmem hln3 hcp hz d
  · rw [R₄ _ (by omega) (by omega) (by omega) (by omega)]; exact q50'
  · rw [R₄ _ (by omega) (by omega) (by omega) (by omega)]; exact q57'
  · rw [R₄ _ (by omega) (by omega) (by omega) (by omega)]; exact q59'
  · rw [R₄ _ (by omega) (by omega) (by omega) (by omega), qR _ (by omega) (by omega) (by omega),
      R₂ _ (by omega) (by omega) (by omega), s97]; exact hA.r50
  · rw [R₄ _ (by omega) (by omega) (by omega) (by omega), qR _ (by omega) (by omega) (by omega),
      R₂ _ (by omega) (by omega) (by omega), s98]; exact hA.r57
  · rw [R₄ _ (by omega) (by omega) (by omega) (by omega), qR _ (by omega) (by omega) (by omega),
      R₂ _ (by omega) (by omega) (by omega), s99]; exact hA.r59
  · rw [M₄ a (by unfold aCL at h3; omega) (by unfold aDU at h4; omega), m3 a h1 h2]

/-- The raw length word of stage B3. -/
def lnRaw (mem : ℕ → ℕ) (CL WM cV nD cF j : ℕ) : ℕ :=
  mem (CL + j) * MSSP.isoN1 cV nD cF + mem (WM + j) * MSSP.isoN3 cV nD + MSSP.isoN2 cV nD cF + j

set_option maxHeartbeats 4000000 in
/-- **Stage B, second part** (`msB3 ; msB4`), on the words. -/
theorem msBb_exec {nD cV cF IM nP CL WM LD DU GG VB : ℕ} (c : Config) (hc : WordsBounded W c)
    (r50 : c.nreg 7950 = nD) (r57 : c.nreg 7957 = cV) (r59 : c.nreg 7959 = cF)
    (r82 : c.nreg 8282 = IM) (r30 : c.nreg 8230 = nP) (r87 : c.nreg 8287 = CL)
    (r86 : c.nreg 8286 = WM) (r88 : c.nreg 8288 = LD) (r89 : c.nreg 8289 = DU)
    (r84 : c.nreg 8284 = GG) (hnP : nP ≤ nD) (l1 : IM + 8 * nD ≤ WM) (l2 : WM + nD ≤ CL)
    (l3 : CL + nD ≤ LD) (l4 : LD + nD ≤ DU) (l5 : GG < LD) (l6 : GG < IM ∨ IM + 8 * nD ≤ GG)
    (hval : ∀ j < nD, lnRaw c.nmem CL WM cV nD cF j ≤ VB) (hs : 2 * (nD * VB + 1) ≤ W)
    (hW3 : MSSP.isoN1 cV nD cF + cV + 2 * (cF * cV) + 8 ≤ W ∧ CL + nD + 8 ≤ W)
    (hW4 : DU + nD + 8 ≤ W) (hG : c.nmem GG ≤ W) :
    ∃ e t, Exec P W msBb c e t ∧ t ≤ (17 + (15 + 8) * nD + 5) +
        (4 + (6 * nP + 5) + 10 + (18 + 8) * nD + 5) ∧
      (∀ j < nD, e.nmem (IM + 6 * nD + j) = (if j < nP then 1 else 0) ∧
        e.nmem (IM + 7 * nD + j) = if j < nP then lnRaw c.nmem CL WM cV nD cF j else 0) ∧
      e.nreg 7328 = MSSP.isoN1 cV nD cF ∧
      e.nreg 7342 = ∑ j ∈ range nP, lnRaw c.nmem CL WM cV nD cF j ∧
      e.nreg 7335 = ∑ j ∈ range nP, lnRaw c.nmem CL WM cV nD cF j + 1 ∧
      (∀ j < nD, e.nmem (LD + j) =
        if j < nP then lnRaw c.nmem CL WM cV nD cF j
        else if j = c.nmem GG then ∑ i ∈ range nP, lnRaw c.nmem CL WM cV nD cF i + 1
        else 2 * (∑ i ∈ range nP, lnRaw c.nmem CL WM cV nD cF i + 1)) ∧
      (∀ a, (a < IM + 6 * nD ∨ IM + 8 * nD ≤ a) → (a < LD ∨ LD + nD ≤ a) →
        (a < DU ∨ DU + nD ≤ a) → e.nmem a = c.nmem a) ∧
      (∀ r, (r < 7326 ∨ 7345 < r) → (r < 8200 ∨ 8219 < r) → r ≠ 8264 → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, hw₁, m₁, n28, R₁, rr₁, rm₁, o₁⟩ :=
    msB3_execW' (P := P) c hc r50 r57 r59 r82 r30 r87 r86 l1 l2
      (fun j hj => (hval j hj).trans (by
        have : VB ≤ nD * VB := Nat.le_mul_of_pos_left _ (by omega)
        omega)) hW3
  have k1 : ∀ r, (r < 7326 ∨ 7331 < r) → (r < 8200 ∨ 8219 < r) → r ≠ 8264 →
      c₁.nreg r = c.nreg r := R₁
  have hsum : ∑ j ∈ range nP, c₁.nmem (IM + 7 * nD + j) =
      ∑ j ∈ range nP, lnRaw c.nmem CL WM cV nD cF j :=
    Finset.sum_congr rfl fun j hj => by
      have hj' := mem_range.1 hj
      rw [(hw₁ j (by omega)).2]; simp only [hj', ↓reduceIte]; rfl
  have hsle : ∑ j ∈ range nP, lnRaw c.nmem CL WM cV nD cF j ≤ nD * VB := by
    have := Finset.sum_le_card_nsmul (range nP) (lnRaw c.nmem CL WM cV nD cF) VB
      (fun j hj => hval j (by have := mem_range.1 hj; omega))
    simp only [card_range, smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ hnP)
  have hGG : c₁.nmem GG = c.nmem GG := m₁ GG (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, w42, w35, wLD, M₂, R₂, rr₂, rm₂, o₂⟩ :=
    msB4_execW (P := P) c₁ e₁.wb_right (nD := nD) (IM := IM) (nP := nP) (LD := LD) (DU := DU) (GG := GG)
      (by rw [k1 _ (by omega) (by omega) (by omega)]; exact r50)
      (by rw [k1 _ (by omega) (by omega) (by omega)]; exact r82)
      (by rw [k1 _ (by omega) (by omega) (by omega)]; exact r30)
      (by rw [k1 _ (by omega) (by omega) (by omega)]; exact r88)
      (by rw [k1 _ (by omega) (by omega) (by omega)]; exact r89)
      (by rw [k1 _ (by omega) (by omega) (by omega)]; exact r84) hnP
      (fun j hj => by rw [(hw₁ j hj).1]; split_ifs <;> omega) (by omega) l4 l5
      (by rw [hsum]; omega)
      (fun j hj => by
        rw [(hw₁ j hj).2]; split_ifs
        · have h1 := hval j hj
          unfold lnRaw at h1
          have h2 : VB ≤ nD * VB := Nat.le_mul_of_pos_left _ (by omega)
          omega
        · omega) hW4 (by rw [hGG]; exact hG)
  have n28' : c₂.nreg 7328 = MSSP.isoN1 cV nD cF := by
    rw [R₂ _ (by omega) (by omega) (by omega)]; exact n28
  refine ⟨c₂, t₁ + t₂, e₁.seq e₂, by omega, fun j hj => ?_, n28', by rw [w42, hsum],
    by rw [w35, hsum], fun j hj => ?_,
    fun a h1 h2 h3 => ?_, fun r h1 h2 h3 => ?_, by rw [rr₂, rr₁], by rw [rm₂, rm₁],
    by rw [o₂, o₁]⟩
  · rw [M₂ _ (Or.inl (by omega)) (Or.inl (by omega)), M₂ _ (Or.inl (by omega)) (Or.inl (by omega))]
    exact hw₁ j hj
  · rw [wLD j hj, (hw₁ j hj).1, (hw₁ j hj).2, hsum, hGG]
    by_cases hj' : j < nP <;> simp [hj', lnRaw]
  · rw [M₂ a h2 h3, m₁ a h1]
  · rw [R₂ r (by omega) h2 h3, k1 r (by omega) h2 h3]

/-- The piece is the darts numbered below `nE + nT`. -/
lemma mσ_piece {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k)
    (d : CutD M Pa.darts) :
    d ∈ cutPiece M Pa.darts ↔ (mσ h Pa hk d : ℕ) < nEc Pa.darts en m + nTc M Pa.darts en m := by
  rw [enEq_cut Pa.rev_mem_darts' h (cD0 Pa hk)]; exact cutIx_mem_piece h d

/-- `tripW` of nonnegative lengths as a sum of natural words. -/
lemma tripW_toNat_sum {D' : Type*} {S : Finset D'} {f : D' → ℤ} (hf : ∀ d ∈ S, 0 ≤ f d) :
    (Klein.tripW S f).toNat = ∑ d ∈ S, (f d).toNat := by
  have : Klein.tripW S f = ((∑ d ∈ S, (f d).toNat : ℕ) : ℤ) := by
    unfold Klein.tripW; push_cast
    exact Finset.sum_congr rfl fun d hd => by rw [abs_of_nonneg (hf d hd), Int.toNat_of_nonneg (hf d hd)]
  rw [this, Int.toNat_natCast]

set_option maxHeartbeats 8000000 in
/-- **Stage B on the machine**: from stage A's facts, `StB` (Klein's encoding with the piece and
the isolating lengths, `w`, `H`, `N₁`, Dijkstra's lengths). The sums of addresses in the
hypotheses of the stage lemmas are per-entry (`msB3_execW'`, `msB4_execW`). -/
theorem msB_exec (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e)
    {p q Lb Lmax nF nV : ℕ} (τv : CutV M Pa.darts ≃ Fin nF) (τf : CutF M Pa.darts ≃ Fin nV)
    (c₀ c : Config) (hc : WordsBounded W c) (hA : StA hM hrot h Pa hk p q c₀ c τv τf)
    (r00' : c₀.nreg 8000 = m) (r05 : c₀.nreg 8005 = Lb) (r09' : c₀.nreg 8009 = p)
    (hln : ∀ i < m, (c₀.nmem (Lb + i) : ℤ) = ℓ (en i) ∧ c₀.nmem (Lb + i) ≤ Lmax)
    (lLb : Lb + m ≤ p)
    (hV : 2 * (mnD Pa en m * (MSSP.isoN1 nF (mnD Pa en m) nV * (Lmax + 1)) + 1) +
      MSSP.isoN1 nF (mnD Pa en m) nV + nF + 2 * (nV * nF) ≤ p)
    (hWW : p + 860 * m + 100 + 2 * q ≤ W) :
    ∃ e t, ∃ Ct : STFlow.DTree (mN Pa), Exec P W msB c e t ∧ t ≤ costB m ∧
      StB hM hrot h Pa hk ℓ hnn p q c₀ e τv τf Ct := by
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  have eD : mnD Pa en m = nEc Pa.darts en m + 4 * nTc M Pa.darts en m := rfl
  have lay := hA.lay
  have hL : ∀ e, ℓ e ≤ Lmax := len_le_of_in h (fun i hi => hln i hi)
  have eV : Fintype.card (CutV M Pa.darts) = nF := by rw [Fintype.card_congr τv, Fintype.card_fin]
  have eF : Fintype.card (CutF M Pa.darts) = nV := by rw [Fintype.card_congr τf, Fintype.card_fin]
  have eDc : Fintype.card (CutD M Pa.darts) = mnD Pa en m := card_cutD h
  obtain ⟨c₁, t₁, Ct, e₁, ht₁, hCr, hWM, hCL, a50, a57, a59, a97, a98, a99, aR, aM, arr, arm, ao⟩ :=
    msBa_exec (P := P) hM hrot h Pa hk hnn τv τf c₀ c hc hA r00' r05 r09'
      (fun i hi => (hln i hi).1) lLb (by omega)
  set kl := mkl hM hrot h Pa hk ℓ hnn Ct with hkl
  have hS : ∀ d, d ∈ cutPiece M Pa.darts ↔
      (mσ h Pa hk d : ℕ) < nEc Pa.darts en m + nTc M Pa.darts en m := mσ_piece h Pa hk
  -- the raw length words are the isolating lengths
  have hLN : ∀ d, lnRaw c₁.nmem (aCL m p) (aWM m p) nF (mnD Pa en m) nV (mσ h Pa hk d) =
      (kl d).toNat := fun d =>
    ln_kLen hM hrot h Pa hk (fun e _ => hnn e) hnn τv τf Ct c₁.nmem hCL hWM d
  have hklb : ∀ d, 0 < kl d ∧ kl d < (MSSP.isoN1 nF (mnD Pa en m) nV : ℤ) * (Lmax + 1) := by
    intro d
    have := mkl_bound hM hrot h Pa hk hnn hL Ct d
    rwa [eV, eF, eDc] at this
  have hval : ∀ j < mnD Pa en m, lnRaw c₁.nmem (aCL m p) (aWM m p) nF (mnD Pa en m) nV j ≤
      MSSP.isoN1 nF (mnD Pa en m) nV * (Lmax + 1) := fun j hj => by
    obtain ⟨d, hd⟩ : ∃ d, (mσ h Pa hk d : ℕ) = j := ⟨(mσ h Pa hk).symm ⟨j, hj⟩, by simp⟩
    rw [← hd, hLN d]
    obtain ⟨h1, h2⟩ := hklb d
    have : ((kl d).toNat : ℤ) = kl d := Int.toNat_of_nonneg h1.le
    have h3 : (((kl d).toNat : ℕ) : ℤ) ≤ ((MSSP.isoN1 nF (mnD Pa en m) nV * (Lmax + 1) : ℕ) : ℤ) := by
      push_cast; omega
    exact_mod_cast h3
  have r82 : c₁.nreg 8282 = aIM m p := by
    rw [aR _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact lay 2 (by omega)
  have g1 : c₁.nmem (aGG m p) = mσ h Pa hk (cD0 Pa hk) := by
    rw [aM _ (Or.inl (by unfold aGG aZi; omega)) (Or.inl (by unfold aGG aWM; omega))
      (Or.inl (by unfold aGG aCL; omega)) (Or.inl (by unfold aGG aDU; omega))]; exact hA.gg0
  have hVle : MSSP.isoN1 nF (mnD Pa en m) nV * (Lmax + 1) ≤
      mnD Pa en m * (MSSP.isoN1 nF (mnD Pa en m) nV * (Lmax + 1)) + 1 := by
    rcases Nat.eq_zero_or_pos (mnD Pa en m) with h0 | h0
    · have := cutIx_lt (L := Pa.darts) h (M := M) (en := en) (m := m) (cD0 Pa hk)
      omega
    · have := Nat.le_mul_of_pos_left (MSSP.isoN1 nF (mnD Pa en m) nV * (Lmax + 1)) h0
      omega
  have hN1le : MSSP.isoN1 nF (mnD Pa en m) nV ≤ MSSP.isoN1 nF (mnD Pa en m) nV * (Lmax + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, hw₂, n28, w42, w35, wLD, M₂, R₂, rr₂, rm₂, o₂⟩ :=
    msBb_exec (P := P) c₁ e₁.wb_right (nD := mnD Pa en m) (cV := nF) (cF := nV) (IM := aIM m p)
      (nP := nEc Pa.darts en m + nTc M Pa.darts en m) (CL := aCL m p) (WM := aWM m p)
      (LD := aLD m p) (DU := aDU m p) (GG := aGG m p)
      (VB := MSSP.isoN1 nF (mnD Pa en m) nV * (Lmax + 1)) a50 a57 a59 r82
      (by rw [aR _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hA.r30)
      (by rw [aR _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact lay 7 (by omega))
      (by rw [aR _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact lay 6 (by omega))
      (by rw [aR _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact lay 8 (by omega))
      (by rw [aR _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact lay 9 (by omega))
      (by rw [aR _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact lay 4 (by omega))
      (by omega) (by unfold aIM aWM; omega) (by unfold aWM aCL; omega) (by unfold aCL aLD; omega)
      (by unfold aLD aDU; omega) (by unfold aGG aLD; omega) (Or.inr (by unfold aIM aGG; omega))
      hval (by omega) (by unfold aCL; omega) (by unfold aDU; omega)
      (by rw [g1]; have := (mσ h Pa hk (cD0 Pa hk)).2; omega)
  have hsumw : ∑ j ∈ range (nEc Pa.darts en m + nTc M Pa.darts en m),
      lnRaw c₁.nmem (aCL m p) (aWM m p) nF (mnD Pa en m) nV j =
      (Klein.tripW (cutPiece M Pa.darts) kl).toNat := by
    rw [sum_piece (mσ h Pa hk) hS (by omega), tripW_toNat_sum (fun d _ => (hklb d).1.le)]
    exact Finset.sum_congr rfl fun d _ => hLN d
  have k2 : ∀ r, (r < 1400 ∨ 8000 ≤ r) → r ≠ 8264 → r ≠ 8265 → (r < 8200 ∨ 8219 < r) →
      (r < 8297 ∨ 8299 < r) → c₂.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 => by
    rw [R₂ r (by omega) h4 h2, aR r h1 h2 h3 h4 h5]
  have m2 : ∀ a, (a < aIM m p + 6 * mnD Pa en m ∨ aIM m p + 8 * mnD Pa en m ≤ a) →
      (a < aZi m p ∨ aZi m p + 60 * m + 30 ≤ a) →
      (a < aWM m p ∨ aWM m p + mnD Pa en m ≤ a) → (a < aCL m p ∨ aCL m p + mnD Pa en m ≤ a) →
      (a < aLD m p ∨ aLD m p + mnD Pa en m ≤ a) →
      (a < aDU m p ∨ aDU m p + mnD Pa en m ≤ a) → c₂.nmem a = c.nmem a :=
    fun a h1 h2 h3 h4 h5 h6 => by rw [M₂ a h1 h5 h6, aM a h2 h3 h4 h6]
  have mlow : ∀ a, a < p + 16 * m → c₂.nmem a = c.nmem a := fun a ha => by
    apply m2 a <;> first | (left; unfold aIM; omega) | (left; unfold aZi; omega) |
      (left; unfold aWM; omega) | (left; unfold aCL; omega) | (left; unfold aLD; omega) |
      (left; unfold aDU; omega)
  have hE : ∀ r, ¬ EScr r → c₂.nreg r = c₀.nreg r := fun r hr => by
    simp only [EScr] at hr
    rw [k2 r (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hA.reg r (by simp only [EScr]; omega)
  refine ⟨c₂, t₁ + t₂, Ct, e₁.seq e₂, ?_, ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, fun s hs => ?_, fun i hi => ?_, fun r hr => ?_, fun i hi hf => ?_,
    fun i hi => ?_, ?_, fun i hi => ?_, ?_, ?_, fun d => ?_, hCr, fun a ha => ?_, hE,
    by rw [rr₂, arr]; exact hA.rr, by rw [rm₂, arm]; exact hA.rm, by rw [o₂, ao]; exact hA.out⟩⟩
  · unfold costB
    have : (15 + 8) * mnD Pa en m ≤ (15 + 8) * (5 * m) := by omega
    have : 6 * (nEc Pa.darts en m + nTc M Pa.darts en m) ≤ 6 * (5 * m) := by omega
    have : (18 + 8) * mnD Pa en m ≤ (18 + 8) * (5 * m) := by omega
    omega
  · rw [k2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact lay j hj
  · rw [k2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hA.per
  · rw [k2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hA.ncl
  · rw [k2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hA.r28
  · rw [R₂ _ (by omega) (by omega) (by omega)]; exact a50
  · rw [R₂ _ (by omega) (by omega) (by omega)]; exact a57
  · rw [R₂ _ (by omega) (by omega) (by omega)]; exact a59
  · rw [R₂ _ (by omega) (by omega) (by omega)]; exact a97
  · rw [R₂ _ (by omega) (by omega) (by omega)]; exact a98
  · rw [R₂ _ (by omega) (by omega) (by omega)]; exact a99
  · rw [w42, hsumw]
  · rw [w35, hsumw]
  · exact n28
  · have := fixPer_le h Pa
    rw [mlow _ (by omega)]; exact hA.tr s hs
  · rw [mlow _ (by omega)]; exact hA.fl i hi
  · have := fixCornerL_le h Pa
    rw [mlow _ (by omega), mlow _ (by omega)]; exact hA.cs r hr
  · obtain ⟨r, hr, e1, e2⟩ := hA.cn i hi hf
    have hl := NsStep.labI_lt (M := M) h hi
    exact ⟨r, hr, by rw [mlow _ (by omega)]; exact e1, e2⟩
  · rw [mlow _ (by omega), mlow _ (by omega)]; exact hA.rk i hi
  · refine KInMS.of hA.kin (n := 4 * mnD Pa en m + 1) (StEnc.ιE_lt (cQ h Pa hk))
      (fun i hi => ?_) (fun d => ?_) (fun d hd => ?_)
    · apply m2 <;> first | (rcases hi with hi | hi <;> [left; right] <;> omega) |
        (left; unfold aIM aZi; omega) | (left; unfold aIM aWM; omega) |
        (left; unfold aIM aCL; omega) | (left; unfold aIM aLD; omega) |
        (left; unfold aIM aDU; omega)
    · have hσ := (mσ h Pa hk d).2
      rw [show aIM m p + Klein.iIS (mnD Pa en m) + (mσ h Pa hk d : ℕ) =
        aIM m p + 6 * mnD Pa en m + (mσ h Pa hk d : ℕ) by simp [Klein.iIS], (hw₂ _ hσ).1]
      by_cases hd : d ∈ cutPiece M Pa.darts
      · simp only [hd, (hS d).1 hd, ↓reduceIte]
      · have : ¬ (mσ h Pa hk d : ℕ) < nEc Pa.darts en m + nTc M Pa.darts en m :=
          fun h' => hd ((hS d).2 h')
        simp only [hd, this, ↓reduceIte]
    · have hσ := (mσ h Pa hk d).2
      rw [show aIM m p + Klein.iLN (mnD Pa en m) + (mσ h Pa hk d : ℕ) =
        aIM m p + 7 * mnD Pa en m + (mσ h Pa hk d : ℕ) by simp [Klein.iLN], (hw₂ _ hσ).2]
      simp only [(hS d).1 hd, ↓reduceIte]
      exact hLN d
  · rw [m2 _ (Or.inr (by omega)) (Or.inl (by unfold aIM aZi; have := fixPer_le h Pa; omega))
      (Or.inl (by unfold aIM aWM; have := fixPer_le h Pa; omega))
      (Or.inl (by unfold aIM aCL; have := fixPer_le h Pa; omega))
      (Or.inl (by unfold aIM aLD; have := fixPer_le h Pa; omega))
      (Or.inl (by unfold aIM aDU; have := fixPer_le h Pa; omega))]
    exact hA.g i hi
  · rw [m2 _ (Or.inr (by unfold aIM aGG; omega)) (Or.inl (by unfold aGG aZi; omega))
      (Or.inl (by unfold aGG aWM; omega)) (Or.inl (by unfold aGG aCL; omega))
      (Or.inl (by unfold aGG aLD; omega)) (Or.inl (by unfold aGG aDU; omega))]
    exact hA.gg0
  · rw [m2 _ (Or.inr (by unfold aIM aGG; omega)) (Or.inl (by unfold aGG aZi; omega))
      (Or.inl (by unfold aGG aWM; omega)) (Or.inl (by unfold aGG aCL; omega))
      (Or.inl (by unfold aGG aLD; omega)) (Or.inl (by unfold aGG aDU; omega))]
    exact hA.gg1
  · have hσ := (mσ h Pa hk d).2
    rw [wLD _ hσ, g1, hsumw]
    unfold mLD
    by_cases hd : d ∈ cutPiece M Pa.darts
    · simp only [(hS d).1 hd, hd, ↓reduceIte]; exact hLN d
    · have h1 : ¬ (mσ h Pa hk d : ℕ) < nEc Pa.darts en m + nTc M Pa.darts en m :=
        fun h' => hd ((hS d).2 h')
      simp only [h1, hd, ↓reduceIte]
      by_cases h0 : d = cD0 Pa hk
      · have h2 : (mσ h Pa hk d : ℕ) = mσ h Pa hk (cD0 Pa hk) := by rw [h0]
        simp only [h2, h0, ↓reduceIte, Int.toNat_natCast]
        rfl
      · have h2 : (mσ h Pa hk d : ℕ) ≠ mσ h Pa hk (cD0 Pa hk) :=
          fun e => h0 ((mσ h Pa hk).injective (Fin.ext e))
        simp only [h2, h0, ↓reduceIte]
        rw [show (2 : ℤ) * (((Klein.tripW (cutPiece M Pa.darts) kl).toNat + 1 : ℕ) : ℤ) =
          ((2 * ((Klein.tripW (cutPiece M Pa.darts) kl).toNat + 1) : ℕ) : ℤ) by push_cast; ring,
          Int.toNat_natCast]
  · rw [m2 a (by unfold aIM at *; omega) (by unfold aZi at *; omega) (by unfold aWM at *; omega)
      (by unfold aCL at *; omega) (by unfold aLD at *; omega) (by unfold aDU at *; omega)]
    exact hA.mem a (by unfold aGG at *; omega) (by unfold aDU at *; omega)

end MsEnc

end BKMNW

end PlanarFlow
