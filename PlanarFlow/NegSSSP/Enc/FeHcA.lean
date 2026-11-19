module

public import PlanarFlow.NegSSSP.Enc.HoistNode

/-!
# The encoder exports its constant `Hc`

The bound `Hc` of the residues written by the encoder (`KSlotN` modulo `2 Hc + 1`) depends on the
data (`Hc = kcnHc A FN (tripW …) k`, `tripW` a sum of isolating lengths). The fixed node program
must read it from the machine: the encoder computes it in the register `2125` (`kcnProg_kslot`,
`encResProg_fd`), and no later phase of the encoder writes `2125` or `2126` (`fh_bfs_ok`,
`fh_gather_ok`, `fh_end_ok`, `fh_clamp_ok`, kernel-checked for all parameters).

* `fh_keep25`: a statement naming neither `2125` nor `2126` keeps them;
* **`fhEnc_exec`**, **`fhMid_exec`**: `feEnc_exec`, `feMid_exec` (same proofs) with the extra
  conclusion `c'.nreg 2125 = kcnHc p.A p.FN (tripW …).toNat fd.k`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The registers other than `2125`, `2126`. -/
abbrev fhU : ℕ → Bool := fun r => decide (r ≠ 2125 ∧ r ≠ 2126)

theorem fh_bfs_ok (p : FeP) (x : ℕ) : (feBfs p x).regsOK fhU = true ∧
    (feBfs p x).noInp = true ∧ (feBfs p x).noRand = true := by
  refine ⟨?_, ?_, ?_⟩ <;> kernel_rfl

theorem fh_gather_ok (a b c d : ℕ) : (feGather a b c d).regsOK fhU = true ∧
    (feGather a b c d).noInp = true ∧ (feGather a b c d).noRand = true := by
  refine ⟨?_, ?_, ?_⟩ <;> kernel_rfl

theorem fh_end_ok (p : FeP) : (feEndProgDk p).regsOK fhU = true ∧
    (feEndProgDk p).noInp = true ∧ (feEndProgDk p).noRand = true := by
  refine ⟨?_, ?_, ?_⟩ <;> kernel_rfl

theorem fh_clamp_ok (a b c : ℕ) : (feClamp a b c).regsOK fhU = true ∧
    (feClamp a b c).noInp = true ∧ (feClamp a b c).noRand = true := by
  refine ⟨?_, ?_, ?_⟩ <;> kernel_rfl

/-- A statement naming neither `2125` nor `2126` keeps them. -/
theorem fh_keep25 {s : Stmt} {c c' : Config} {k : ℕ} (e : Exec P W s c c' k)
    (h : s.regsOK fhU = true ∧ s.noInp = true ∧ s.noRand = true) :
    c'.nreg 2125 = c.nreg 2125 ∧ c'.nreg 2126 = c.nreg 2126 :=
  ⟨exec_nreg_keep e h.1 h.2.1 h.2.2 2125 (by decide),
    exec_nreg_keep e h.1 h.2.1 h.2.2 2126 (by decide)⟩

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

set_option maxHeartbeats 2000000 in
open Classical in
/-- `feEnc_exec` with the register `2125` holding `Hc`. -/
theorem fhEnc_exec {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
    (σ₀ : fd.DQ ≃ Fin (Fintype.card fd.DQ)) (p : FeP) (hD : p.nD = Fintype.card fd.DQ)
    (hk : p.k = fd.k) (hV : p.nV = Fintype.card fd.VQ) (hF : p.nF = Fintype.card fd.FQ)
    (hW : p.END ≤ W)
    (hLm : feIsoB p.A p.N p.FN (srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)).toNat ≤ p.Lmax)
    (hLW : p.Lmax ≤ W) (hH : 2 * kcnHc p.A p.FN (p.N * p.Lmax) p.k + 1 ≤ W)
    {w : SrcD fd.DQ fd.k → ℤ} (hwB : ∀ d, |w d| ≤ Fintype.card (SrcF fd.FQ fd.k))
    (c : Config) (hc : WordsBounded W c)
    (hSL : ∀ d : SrcD fd.DQ fd.k, c.nmem (p.SL + srcNum σ₀ d) = (srcLen (faceLen fd.P' fd.e ℓ)
      (srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)) d).toNat)
    (hWW : ∀ d, c.nmem (p.WW + srcNum σ₀ d) = (w d + Fintype.card (SrcF fd.FQ fd.k)).toNat)
    (hfl : ∀ d, c.nmem (p.β + 6 * p.N + srcNum σ₀ d) =
      if d ∈ srcPiece fd.k (fd.P'.image fd.e) then 1 else 0)
    (hrb : ∀ d, c.nmem (p.RD + srcNum σ₀ d) =
      if MSSP.Reach (MSSP.pieceGraph (srcMap fd.inst.cycle) (srcPiece fd.k (fd.P'.image fd.e))
        (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
          (srcNum σ₀))) (tripDst (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0)
        ((srcMap fd.inst.cycle).tail d) then 1 else 0) :
    ∃ c' t, Exec P W (feEnc p) c c' t ∧ t ≤ 15 + (47 * p.N + 58) ∧
      (∀ d, c'.nmem (p.ISO + srcNum σ₀ d) = (srcIso (V := fd.VQ) (F := fd.FQ) fd.k
        (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀) d).toNat) ∧
      (∀ a < 3 * p.N + 3, c'.nmem (p.RK + a) =
        resW (2 * kcnHc p.A p.FN (tripW (srcPiece fd.k (fd.P'.image fd.e))
          (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
            (srcNum σ₀))).toNat fd.k + 1)
          (kConst (SrcV fd.VQ fd.k) (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle)
            (srcPiece fd.k (fd.P'.image fd.e))
            (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
              (srcNum σ₀)) (srcNum σ₀) a : ℝ)) ∧
      fdHI fd ℓ (srcNum σ₀) w ≤ (kcnHc p.A p.FN (tripW (srcPiece fd.k (fd.P'.image fd.e))
          (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
            (srcNum σ₀))).toNat fd.k : ℝ) ∧
      kcnHc p.A p.FN (tripW (srcPiece fd.k (fd.P'.image fd.e))
          (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
            (srcNum σ₀))).toNat fd.k ≤ kcnHc p.A p.FN (p.N * p.Lmax) p.k ∧
      (∀ a, (a < p.ISO ∨ p.ISO + p.N ≤ a) → (a < p.RK ∨ p.RK + 3 * p.N + 3 ≤ a) →
        c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 2125 = kcnHc p.A p.FN (tripW (srcPiece fd.k (fd.P'.image fd.e))
          (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
            (srcNum σ₀))).toNat fd.k := by
  obtain ⟨cD, cV, cF⟩ := fe_cards (k := fd.k) (D := fd.DQ) (V := fd.VQ) (F := fd.FQ) p hD hk hV hF
  have hnnQ : ∀ y, 0 ≤ faceLen fd.P' fd.e ℓ y := fun y => faceLen_nonneg _ _ _ y
  have hIso : ∀ d, (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e)
      (faceLen fd.P' fd.e ℓ) w (srcNum σ₀) d).toNat ≤ p.Lmax := fun d => by
    have := srcIso_le (V := fd.VQ) (F := fd.FQ) (S := fd.P'.image fd.e) hnnQ
      (faceLen_le_srcW fd ℓ) hwB (srcNum σ₀) d
    rw [cD, cV, cF] at this; omega
  have hTW := tripW_srcIso_le (V := fd.VQ) (F := fd.FQ) (S := fd.P'.image fd.e) hnnQ hwB
    (srcNum σ₀) hIso (srcPiece fd.k (fd.P'.image fd.e))
  rw [cD] at hTW
  have hHle := kcnHc_mono (nV := p.A) (nF := p.FN) (k := p.k) hTW
  have hSW1 : 1 ≤ (srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)).toNat := by
    have := sum_nonneg fun z (_ : z ∈ fd.P'.image fd.e) => hnnQ z
    unfold srcW; omega
  have hN1 : MSSP.isoN1 p.A p.N p.FN ≤ W := by
    have : MSSP.isoN1 p.A p.N p.FN ≤ MSSP.isoN1 p.A p.N p.FN *
        (srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)).toNat := Nat.le_mul_of_pos_right _ hSW1
    unfold feIsoB at hLm; omega
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ : p.β + 6 * p.N + p.N ≤ p.SL ∧ p.SL + p.N ≤ p.WW ∧
      p.WW + p.N ≤ p.RD ∧ p.RD + p.N ≤ p.ISO ∧ p.ISO + p.N = p.RK ∧
      p.RK + 3 * p.N + 3 ≤ W := by
    have hE := p.eqs; have hsl := p.slot_le; clear * - hE hsl hW; omega
  obtain ⟨c₁, k₁, e₁, hk₁, hn₁, hr₁, hm₁, hrm₁, ho₁⟩ :=
    feSet_exec (P := P) (feEncRegs p) (by
      intro q hq; simp only [feEncRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      have hA : p.A ≤ p.RK := by have := p.eqs; clear * - this; omega
      have hF' : p.FN ≤ p.RK := by have := p.eqs; clear * - this; omega
      have hk' : p.k ≤ p.RK := by have := p.eqs; clear * - this; omega
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp only <;> clear * - l1 l2 l3 l4 l5 l6 hA hF' hk' <;> omega) c hc
  have hm' : ∀ a, c₁.nmem a = c.nmem a := fun a => by rw [hm₁]
  have hHW : 2 * kcnHc (Fintype.card (SrcV fd.VQ fd.k)) (Fintype.card (SrcF fd.FQ fd.k))
      (tripW (srcPiece fd.k (fd.P'.image fd.e)) (srcIso (V := fd.VQ) (F := fd.FQ) fd.k
        (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀))).toNat fd.k + 1 ≤ W := by
    rw [cV, cF]; rw [hk] at hH hHle; omega
  rw [← cD] at l1 l2 l3 l4 l5 l6
  obtain ⟨c₂, k₂, e₂, hk₂, hI, hR, h25, -, hHI, hm₂, -, hr₂, hrm₂, ho₂⟩ :=
    encResProg_fd (P := P) fd ℓ (srcNum σ₀) hwB (SLb := p.SL) (WWb := p.WW) (ISb := p.ISO)
      (Sb := p.β + 6 * p.N) (Rb := p.RD) (Ob := p.RK)
      ⟨by omega, by omega, by omega, by omega, by omega⟩
      ⟨by rw [← cD]; omega, by omega, by omega, by omega, by rw [← cD]; omega, by omega,
        by omega⟩
      (by rw [← cD]; omega) (by omega) (by rw [cV, cD, cF]; exact hN1)
      (fun d => le_trans (hIso d) hLW) hHW c₁ e₁.wb_right
      (by rw [hn₁, cD]; simp [feEncRegs, feSetV]) (by rw [hn₁]; simp [feEncRegs, feSetV])
      (by rw [hn₁]; simp [feEncRegs, feSetV]) (by rw [hn₁]; simp [feEncRegs, feSetV])
      (by rw [hn₁, cV]; simp [feEncRegs, feSetV]) (by rw [hn₁, cD]; simp [feEncRegs, feSetV])
      (by rw [hn₁, cF]; simp [feEncRegs, feSetV]) (by rw [hn₁, cD]; simp [feEncRegs, feSetV])
      (by rw [hn₁]; simp [feEncRegs, feSetV]) (by rw [hn₁]; simp [feEncRegs, feSetV])
      (by rw [hn₁]; simp [feEncRegs, feSetV]) (by rw [hn₁]; simp [feEncRegs, feSetV])
      (by rw [hn₁, cV]; simp [feEncRegs, feSetV]) (by rw [hn₁]; simp [feEncRegs, feSetV, hk])
      (by rw [hn₁, cF]; simp [feEncRegs, feSetV])
      (fun d => by rw [hm']; exact hSL d) (fun d => by rw [hm']; exact hWW d)
      (fun d => by
        rw [hm', hfl d]
        by_cases h : d ∈ srcPiece fd.k (fd.P'.image fd.e) <;> simp [h])
      (fun d _ => by
        rw [hm', hrb d]
        by_cases h : MSSP.Reach (MSSP.pieceGraph (srcMap fd.inst.cycle)
          (srcPiece fd.k (fd.P'.image fd.e)) (srcIso (V := fd.VQ) (F := fd.FQ) fd.k
            (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀)))
          (tripDst (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0)
          ((srcMap fd.inst.cycle).tail d) <;> simp [h])
  rw [cV, cF] at h25
  have h25' := h25
  rw [h25] at hR hHI
  have hHle' := hHle
  rw [hk] at hHle'
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by simp [feEncRegs] at hk₁; rw [cD] at hk₂; omega,
    hI, ?_, hHI, le_of_le_of_eq hHle' (by rw [hk]), fun a h1 h2 => ?_, by rw [hr₂, hr₁], by rw [hrm₂, hrm₁],
    by rw [ho₂, ho₁], h25'⟩
  · intro a ha; rw [← cD] at ha; exact hR a ha
  · rw [← cD] at h1 h2; rw [hm₂ a h1 h2, hm']


set_option maxHeartbeats 8000000 in
open Classical in
/-- `feMid_exec` with the register `2125` holding `Hc`. -/
theorem fhMid_exec {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
    (σ₀ : fd.DQ ≃ Fin (Fintype.card fd.DQ)) (νv₀ : fd.VQ ≃ Fin (Fintype.card fd.VQ))
    (τ₀ : fd.FQ ≃ Fin (Fintype.card fd.FQ)) (p : FeP) (hD : p.nD = Fintype.card fd.DQ)
    (hk : p.k = fd.k) (hV : p.nV = Fintype.card fd.VQ) (hF : p.nF = Fintype.card fd.FQ)
    (hW : p.END ≤ W)
    (hLm : feIsoB p.A p.N p.FN (srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)).toNat ≤ p.Lmax)
    (hLW : p.Lmax ≤ W) (hH : 2 * kcnHc p.A p.FN (p.N * p.Lmax) p.k + 1 ≤ W)
    (c : Config) (hc : WordsBounded W c)
    (hQRV : ∀ d, c.nmem (p.I0 + σ₀ d) = σ₀ (fd.Q.rev d))
    (hQNT : ∀ d, c.nmem (p.I0 + p.nD + σ₀ d) = νv₀ (fd.Q.tail d))
    (hQNF : ∀ d, c.nmem (p.I0 + 2 * p.nD + σ₀ d) = τ₀ (fd.Q.face d))
    (hQIS : ∀ d, c.nmem (p.I0 + 3 * p.nD + σ₀ d) = if d ∈ fd.P'.image fd.e then 1 else 0)
    (hQLN : ∀ d, c.nmem (p.I0 + 4 * p.nD + σ₀ d) = (faceLen fd.P' fd.e ℓ d).toNat)
    (hQG : ∀ i < fd.k, c.nmem (p.I0 + 5 * p.nD + i) = σ₀ (fd.g i)) :
    ∃ c' t, Exec P W (feMidProg p) c c' t ∧ t ≤ feMidCost p ∧
      ∃ (C₀ : STFlow.DTree (srcMap fd.inst.cycle).dual) (w : SrcD fd.DQ fd.k → ℤ),
        C₀.root = tripSrc (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0 ∧
        (∀ y, y ≠ C₀.root → c'.nmem (p.PA + srcVNum νv₀ y) = srcNum σ₀ (C₀.par y)) ∧
        MSSP.IsoW (srcMap fd.inst.cycle) ((srcMap fd.inst.cycle).face (srcG fd.inst.cycle 0)) w ∧
        (∀ d, |w d| ≤ Fintype.card (SrcF fd.FQ fd.k)) ∧
        SrcArrM fd.Q fd.k fd.g (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) σ₀ νv₀ τ₀ p.β p.SL p.N
          p.A p.AE c'.nmem ∧
        FeOut (fd.P'.image fd.e) σ₀ νv₀ fd.inst.cycle p c'.nmem ∧
        (∀ d, c'.nmem (p.ISO + srcNum σ₀ d) = (srcIso (V := fd.VQ) (F := fd.FQ) fd.k
          (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀) d).toNat) ∧
        (∀ a < 3 * p.N + 3, c'.nmem (p.RK + a) =
          resW (2 * kcnHc p.A p.FN (tripW (srcPiece fd.k (fd.P'.image fd.e))
            (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
              (srcNum σ₀))).toNat fd.k + 1)
            (kConst (SrcV fd.VQ fd.k) (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle)
              (srcPiece fd.k (fd.P'.image fd.e))
              (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
                (srcNum σ₀)) (srcNum σ₀) a : ℝ)) ∧
        fdHI fd ℓ (srcNum σ₀) w ≤ (kcnHc p.A p.FN (tripW (srcPiece fd.k (fd.P'.image fd.e))
            (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
              (srcNum σ₀))).toNat fd.k : ℝ) ∧
        kcnHc p.A p.FN (tripW (srcPiece fd.k (fd.P'.image fd.e))
            (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
              (srcNum σ₀))).toNat fd.k ≤ kcnHc p.A p.FN (p.N * p.Lmax) p.k ∧
        (∀ y, c'.nmem (p.MK + srcVNum νv₀ y) =
          if MSSP.Reach (MSSP.pieceGraph (srcMap fd.inst.cycle) (srcPiece fd.k (fd.P'.image fd.e))
            (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
              (srcNum σ₀))) (tripSrc (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0) y
          then 1 else 0) ∧
        (∀ i < fd.k, c'.nmem (p.β + iXT p.N p.NN p.k + p.k + i) =
          if MSSP.Reach (MSSP.pieceGraph (srcMap fd.inst.cycle) (srcPiece fd.k (fd.P'.image fd.e))
            (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
              (srcNum σ₀))) ((srcMap fd.inst.cycle).tail (srcG fd.inst.cycle 0))
              (.inl (fd.Q.tail (fd.g i))) then 1 else 0) ∧
        (∀ a, a < p.β ∨ p.END ≤ a → c'.nmem a = c.nmem a) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
        c'.nreg 2125 = kcnHc p.A p.FN (tripW (srcPiece fd.k (fd.P'.image fd.e))
          (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
            (srcNum σ₀))).toNat fd.k := by
  have hf := fd.inst.cycle
  have hnnQ : ∀ y, 0 ≤ faceLen fd.P' fd.e ℓ y := fun y => faceLen_nonneg _ _ _ y
  obtain ⟨cD, cV, cF⟩ := fe_cards (k := fd.k) (D := fd.DQ) (V := fd.VQ) (F := fd.FQ) p hD hk hV hF
  have ho := p.ord
  -- A
  obtain ⟨c₁, k₁, e₁, hk₁, hA₁, hone₁, hm₁, hr₁, hrm₁, ho₁⟩ :=
    feA_exec (P := P) (S := fd.P'.image fd.e) (ℓ := faceLen fd.P' fd.e ℓ) (σ₀ := σ₀) (νv₀ := νv₀)
      (τ₀ := τ₀) fd.inst.cycle (fun d _ => hnnQ d) p hD hk hV hF hW
      (by have := hLm; unfold feIsoB at this
          have h1 : (srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)).toNat ≤
              MSSP.isoN1 p.A p.N p.FN * (srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)).toNat :=
            Nat.le_mul_of_pos_left _ (MSSP.isoN1_pos _ _ _)
          omega) c hc hQRV hQNT hQNF hQIS hQLN hQG
  -- B
  obtain ⟨c₂, k₂, e₂, hk₂, ⟨C₀, hC₀r, hPA₂⟩, ⟨w, hw, hwB, hWW₂⟩, hm₂, hr₂, hrm₂, ho₂⟩ :=
    feB_exec (P := P) fd.inst.cycle fd.inst.plane p hD hk hV hF hW c₁ e₁.wb_right hA₁ hone₁
  have hA₂ : SrcArrM fd.Q fd.k fd.g (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) σ₀ νv₀ τ₀ p.β p.SL
      p.N p.A p.AE c₂.nmem :=
    hA₁.keep hD hk hV hF fun x hx => hm₂ x (by clear * - hx ho; omega)
  obtain ⟨ru, rv, -, -⟩ := fe_roots (σ₀ := σ₀) (νv₀ := νv₀) fd.inst.cycle
  have hσN : ∀ d : SrcD fd.DQ fd.k, (srcNum σ₀ d : ℕ) < p.N := fun d => by
    have := (srcNum σ₀ d).2; clear * - this cD; omega
  have hτA : ∀ y : SrcV fd.VQ fd.k, (srcVNum νv₀ y : ℕ) < p.A := fun y => by
    have := (srcVNum νv₀ y).2; clear * - this cV; omega
  have hσs : ∀ i < p.N, ∃ d : SrcD fd.DQ fd.k, (srcNum σ₀ d : ℕ) = i :=
    fun i hi => ⟨(srcNum σ₀).symm ⟨i, by clear * - hi cD; omega⟩, by simp⟩
  -- the out-lists
  obtain ⟨c₃, k₃, e₃, hk₃, hO₃, hm₃, hr₃, hrm₃, ho₃⟩ :=
    feOs_exec (P := P) fd.inst.cycle p hD hk hV hF hW c₂ e₂.wb_right hA₂
  have hA₃ := hA₂.keep hD hk hV hF fun x hx => hm₃ x
    (by clear * - hx ho; omega)
    (by clear * - hx ho; omega)
  -- the search from the second root, the reach bits of the tails
  obtain ⟨c₄, k₄, e₄, hk₄, hR₄, hm₄, hr₄, hrm₄, ho₄⟩ :=
    feBfs_exec (P := P) fd.inst.cycle p hD hk hV hF hW (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀))
      (tripDst (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0) c₃ e₃.wb_right hA₃ hO₃
  have hA₄ := hA₃.keep hD hk hV hF fun x hx => hm₄ x
    (by clear * - hx ho; omega)
  obtain ⟨c₅, k₅, e₅, hk₅, hG₅, hm₅, -, hr₅, hrm₅, ho₅⟩ :=
    feGather_exec (P := P) (Out := p.RD) (In := p.β + 4 * p.N) (Mk := p.MK) (len := p.N)
      (nMk := p.A) (by clear * - ho hW; omega) (by clear * - ho hW; omega)
      (by clear * - ho hW; omega) (by clear * - ho hW; omega)
      (by clear * - ho hW; omega) (by clear * - ho hW; omega) c₄ e₄.wb_right
      (fun i hi => by
        obtain ⟨d, rfl⟩ := hσs i hi
        rw [(hA₄.arrays fd.inst.cycle d).2.2.1]; exact hτA _)
  have hA₅ := hA₄.keep hD hk hV hF fun x hx => hm₅ x
    (by clear * - hx ho; omega)
  -- the weights, the lengths, the flags, the reach bits by darts
  have hWW₅ : ∀ d, c₅.nmem (p.WW + srcNum σ₀ d) = (w d + Fintype.card (SrcF fd.FQ fd.k)).toNat :=
    fun d => by
      have := hσN d
      rw [hm₅ _ (by clear * - this ho; omega), hm₄ _ (by clear * - this ho; omega),
        hm₃ _ (by clear * - this ho; omega) (by clear * - this ho; omega)]
      exact hWW₂ d
  have hRD₅ : ∀ d, c₅.nmem (p.RD + srcNum σ₀ d) =
      if MSSP.Reach (MSSP.pieceGraph (srcMap fd.inst.cycle) (srcPiece fd.k (fd.P'.image fd.e))
        (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀))) (tripDst (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0)
        ((srcMap fd.inst.cycle).tail d) then 1 else 0 := fun d => by
    rw [hG₅ _ (hσN d), (hA₄.arrays fd.inst.cycle d).2.2.1]; exact hR₄ _
  -- the isolating lengths and the residues
  obtain ⟨c₆, k₆, e₆, hk₆, hI₆, hRK₆, hHI, hHle, hm₆, hr₆, hrm₆, ho₆, h25₆⟩ :=
    fhEnc_exec (P := P) fd ℓ σ₀ p hD hk hV hF hW hLm hLW hH hwB c₅ e₅.wb_right
      (fun d => (hA₅.arrays fd.inst.cycle d).2.2.2.2.2)
      hWW₅ (fun d => (hA₅.arrays fd.inst.cycle d).2.2.2.2.1) hRD₅
  have hA₆ := hA₅.keep hD hk hV hF fun x hx => hm₆ x
    (by clear * - hx ho; omega)
    (by clear * - hx ho; omega)
  -- the search from the first root, the reach bits of the targets
  have hO₆ : FeOut (fd.P'.image fd.e) σ₀ νv₀ fd.inst.cycle p c₆.nmem :=
    FeOut.of fd.inst.cycle cV (Bd := p.N) le_rfl hO₃ fun x h1 h2 => ClampAg.of_eq (by
      rw [hm₆ x (by clear * - h1 h2 ho; omega)
          (by clear * - h1 h2 ho; omega),
        hm₅ x (by clear * - h1 h2 ho; omega),
        hm₄ x (by clear * - h1 h2 ho; omega)])
  obtain ⟨c₇, k₇, e₇, hk₇, hR₇, hm₇, hr₇, hrm₇, ho₇⟩ :=
    feBfs_exec (P := P) fd.inst.cycle p hD hk hV hF hW (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀))
      (tripSrc (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0) c₆ e₆.wb_right hA₆ hO₆
  have hA₇ := hA₆.keep hD hk hV hF fun x hx => hm₇ x
    (by clear * - hx ho; omega)
  have hXN : ∀ i < p.k, c₇.nmem (p.β + iXT p.N p.NN p.k + i) = νv₀ (fd.Q.tail (fd.g i)) :=
    fun i hi => by
      have := (hA₇.2 i (by omega)).2
      rw [← this]; congr 1; clear * - ho hk; omega
  obtain ⟨c₈, k₈, e₈, hk₈, hG₈, hm₈, -, hr₈, hrm₈, ho₈⟩ :=
    feGather_exec (P := P) (Out := p.β + iXT p.N p.NN p.k + p.k) (In := p.β + iXT p.N p.NN p.k)
      (Mk := p.MK) (len := p.k) (nMk := p.A) (by clear * - ho hW; omega)
      (by clear * - ho hW; omega) (by clear * - ho hW; omega)
      (by clear * - ho hW; omega) (by clear * - ho hW; omega)
      (by clear * - ho hW; omega) c₇ e₇.wb_right
      (fun i hi => by rw [hXN i hi]; have := (νv₀ (fd.Q.tail (fd.g i))).2; omega)
  have h25₈ : c₈.nreg 2125 = c₆.nreg 2125 :=
    ((fh_keep25 e₈ (fh_gather_ok _ _ _ _)).1).trans ((fh_keep25 e₇ (fh_bfs_ok _ _)).1)
  have eu : (srcVNum (k := fd.k) νv₀ (tripSrc (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0) :
      ℕ) = p.nV := by rw [ru, hV]
  have ev : (srcVNum (k := fd.k) νv₀ (tripDst (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0) :
      ℕ) = p.nV + 2 := by rw [rv, hV]
  rw [ev] at e₄
  rw [eu] at e₇
  have eS : tripSrc (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0 =
      (srcMap fd.inst.cycle).tail (srcG fd.inst.cycle 0) := by simp [tripSrc]
  refine ⟨c₈, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + k₈)))))),
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ e₈)))))), ?_, C₀, w, hC₀r, fun y hy => ?_, hw, hwB,
    hA₇.keep hD hk hV hF fun x hx => hm₈ x (by clear * - hx ho; omega),
    FeOut.of fd.inst.cycle cV (Bd := p.N) le_rfl hO₆ fun x h1 h2 => ClampAg.of_eq (by
      rw [hm₈ x (by clear * - h1 h2 ho; omega),
        hm₇ x (by clear * - h1 h2 ho; omega)]),
    fun d => ?_, fun a ha => ?_, hHI, hHle, fun y => ?_, fun i hi => ?_, fun a ha => ?_,
    by rw [hr₈, hr₇, hr₆, hr₅, hr₄, hr₃, hr₂, hr₁], by rw [hrm₈, hrm₇, hrm₆, hrm₅, hrm₄, hrm₃,
      hrm₂, hrm₁], by rw [ho₈, ho₇, ho₆, ho₅, ho₄, ho₃, ho₂, ho₁], h25₈.trans h25₆⟩
  · unfold feMidCost; clear * - hk₁ hk₂ hk₃ hk₄ hk₅ hk₆ hk₇ hk₈; omega
  · have := hτA y
    rw [hm₈ _ (by clear * - this ho; omega),
      hm₇ _ (by clear * - this ho; omega), hm₆ _ (by clear * - this ho; omega)
        (by clear * - this ho; omega), hm₅ _ (by clear * - this ho; omega),
      hm₄ _ (by clear * - this ho; omega), hm₃ _ (by clear * - this ho; omega)
        (by clear * - this ho; omega)]
    exact hPA₂ y hy
  · have := hσN d
    rw [hm₈ _ (by clear * - this ho; omega),
      hm₇ _ (by clear * - this ho; omega)]
    exact hI₆ d
  · rw [hm₈ _ (by clear * - ha ho; omega),
      hm₇ _ (by clear * - ha ho; omega)]
    exact hRK₆ a ha
  · have := hτA y
    rw [hm₈ _ (by clear * - this ho; omega)]
    exact hR₇ y
  · have hi' : i < p.k := by rw [hk]; exact hi
    rw [hG₈ i hi', hXN i hi']
    have := hR₇ (.inl (fd.Q.tail (fd.g i)))
    rw [srcVNum_inl] at this
    rw [this, eS]
  · rw [hm₈ _ (by clear * - ha ho; omega),
      hm₇ _ (by clear * - ha ho; omega), hm₆ _ (by clear * - ha ho; omega)
        (by clear * - ha ho; omega), hm₅ _ (by clear * - ha ho; omega),
      hm₄ _ (by clear * - ha ho; omega), hm₃ _ (by clear * - ha ho; omega)
        (by clear * - ha ho; omega), hm₂ _ (by clear * - ha ho; omega),
      hm₁ _ ha]

end NegSSSP

end PlanarFlow
