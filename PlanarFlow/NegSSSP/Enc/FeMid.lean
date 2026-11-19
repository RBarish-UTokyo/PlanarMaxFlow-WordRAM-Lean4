module

public import PlanarFlow.NegSSSP.Enc.FeD

/-!
# The composed encoder: phases A to C of a one-face instance

`feMidProg p`: phase A (the dart arrays of the map with the sources copied, the ones), phase B
(the search tree `C₀`, its cotree `C₁`, the isolating weights `treeW C₁`), the out-lists of the
piece, the search from the second root and the reach bits of the tails (`RD`), the isolating
lengths and the residues of the real constants (`feEnc`), the search from the first root and the
reach bits of the targets (`XR`, in the slot).

* `SrcArrM.keep`: the words of `srcArrProg` survive a change outside their regions.
* **`feMid_exec`**: from the plain arrays of `fd.Q` at `I0`, within `feMidCost p` steps: the trees
  `C₀`, the isolating weight `w`, the words of phase A (`SrcArrM`), the out-lists (`FeOut`), the
  isolating lengths, the residues (`KSlotN.res`) with `fdHI ≤ Hc ≤ kcnHc A FN (N Lmax) k`, the
  marks of the first root and the reach bits `XR`; the memory changes only in `[β, END)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

section Keep

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {σ₀ : D ≃ Fin (Fintype.card D)} {νv₀ : V ≃ Fin (Fintype.card V)}
  {τ₀ : F ≃ Fin (Fintype.card F)}

/-- **The words of `srcArrProg` survive a change outside their regions.** -/
theorem SrcArrM.keep {p : FeP} (hD : p.nD = Fintype.card D) (hk : p.k = k)
    (hV : p.nV = Fintype.card V) (hF : p.nF = Fintype.card F) {m m' : ℕ → ℕ}
    (h : SrcArrM M k g S ℓ σ₀ νv₀ τ₀ p.β p.SL p.N p.A p.AE m)
    (hm : ∀ x, x < p.β + iOB p.N p.NN p.k ∨
      (p.β + iXT p.N p.NN p.k ≤ x ∧ x < p.β + iXT p.N p.NN p.k + p.k) ∨
      (p.SL ≤ x ∧ x < p.SL + p.N) → m' x = m x) :
    SrcArrM M k g S ℓ σ₀ νv₀ τ₀ p.β p.SL p.N p.A p.AE m' := by
  have hE := p.eqs
  refine SrcArrM.of (Bd := 2 * p.AE) (by omega) (by omega) (by omega) le_rfl h (fun j hj => ClampAg.of_eq (hm _ (Or.inl ?_)))
    (fun i hi => ClampAg.of_eq (hm _ (Or.inr (Or.inl ?_))))
    (fun j hj => hm _ (Or.inr (Or.inr ⟨by omega, by omega⟩)))
  · unfold iOB; rw [← hk] at hj; omega
  · unfold iXT; rw [← hk] at hi; constructor <;> omega

end Keep

/-- **The order of the regions** (for `omega` in large contexts). -/
lemma FeP.ord (p : FeP) :
    p.β + iOB p.N p.NN p.k ≤ p.β + iOL p.N p.NN p.k ∧
    p.β + iOL p.N p.NN p.k + p.N ≤ p.β + iXT p.N p.NN p.k ∧
    p.β + iXT p.N p.NN p.k + 2 * p.k ≤ p.SL ∧ p.SL + p.N ≤ p.ONE ∧ p.ONE + p.N ≤ p.ZV ∧
    p.ZV ≤ p.PA ∧ p.PA + p.A ≤ p.O1 ∧ p.ZV + 7 * p.A + p.N + 1 ≤ p.O1 ∧ p.O1 ≤ p.ZC ∧
    p.ZC ≤ p.WW ∧ p.WW + p.N ≤ p.ZI ∧ p.ZI ≤ p.RD ∧ p.RD + p.N ≤ p.MK ∧
    p.MK + 2 * p.A + 1 ≤ p.ISO ∧ p.ISO + p.N ≤ p.RK ∧ p.RK + 3 * p.N + 3 ≤ p.DB ∧
    p.DB + p.A ≤ p.ZS ∧ p.ZS + 8 * p.A + 1 ≤ p.ZT ∧ p.ZT + 4 * p.N + 15 * p.FN + 2 ≤ p.OS ∧
    p.OS + 2 * p.A + 1 ≤ p.END ∧ p.β + 4 * p.N + p.N ≤ p.β + iOB p.N p.NN p.k ∧
    p.β + iHD p.N p.NN p.k + 4 = p.β + iXT p.N p.NN p.k ∧
    p.β + iOL p.N p.NN p.k + p.N ≤ p.β + iIV p.N p.NN p.k ∧
    p.β + 8 * p.N + 2 * p.AE + p.k = p.β + iOB p.N p.NN p.k ∧
    p.β + 9 * p.N + 14 * p.AE + p.k + 4 = p.β + iXT p.N p.NN p.k ∧ p.A ≤ p.N + p.A ∧
    p.ZI + p.AE = p.RD ∧ p.ZC + 4 * p.N + 15 * p.FN + 2 = p.WW := by
  simp only [FeP.N, FeP.A, FeP.FN, FeP.AE, FeP.NN, FeP.β, FeP.Bw, FeP.Kw, FeP.SL, FeP.ONE, FeP.ZV,
    FeP.PA, FeP.O1, FeP.ZC, FeP.WW, FeP.ZI, FeP.RD, FeP.MK, FeP.ISO, FeP.RK, FeP.DB, FeP.ZS,
    FeP.ZT, FeP.OS, FeP.END, iOB, iOL, iXT, iHD, iIV, kBL, aOUT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | omega | trivial

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- **Phases A to C.** -/
def feMidProg (p : FeP) : Stmt :=
  .seq (feAProg p) <| .seq (feBProg p) <| .seq (feOs p) <| .seq (feBfs p (p.nV + 2)) <|
  .seq (feGather p.RD (p.β + 4 * p.N) p.MK p.N) <| .seq (feEnc p) <| .seq (feBfs p p.nV)
    (feGather (p.β + iXT p.N p.NN p.k + p.k) (p.β + iXT p.N p.NN p.k) p.MK p.k)

theorem feMidProg_natOnly (p : FeP) : natOnly (feMidProg p) = true := by
  simp only [feMidProg, natOnly, feAProg_natOnly, feBProg_natOnly, feOs_natOnly, feBfs_natOnly,
    feGather_natOnly, feEnc_natOnly, Bool.and_self]

/-- The cost bound of phases A to C. -/
def feMidCost (p : FeP) : ℕ :=
  (43 * p.nD + 284 * p.k + 5 * p.N + 64) + feBCost p + (9 + osCost p.N p.A) +
    2 * (8 + (35 * p.A + 17 * p.N + 12)) + (9 * p.N + 8) + (15 + (47 * p.N + 58)) +
    (9 * p.k + 8)

set_option maxHeartbeats 8000000 in
open Classical in
/-- **Phases A to C on the machine** (see the module docstring). -/
theorem feMid_exec {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
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
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
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
  obtain ⟨c₆, k₆, e₆, hk₆, hI₆, hRK₆, hHI, hHle, hm₆, hr₆, hrm₆, ho₆⟩ :=
    feEnc_exec (P := P) fd ℓ σ₀ p hD hk hV hF hW hLm hLW hH hwB c₅ e₅.wb_right
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
      hrm₂, hrm₁], by rw [ho₈, ho₇, ho₆, ho₅, ho₄, ho₃, ho₂, ho₁]⟩
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
