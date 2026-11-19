module

public import PlanarFlow.NegSSSP.Enc.FeB2
public import PlanarFlow.NegSSSP.IsoWProg

/-!
# The composed encoder, phase B (end): the isolating weights; the whole phase B

* `feIw`, **`feIw_exec`**: `iwProg` with its registers, on a tree `C : DTree M'` of the faces with
  an order `cs` (`Klein.Orders`): the words `B + treeW C d` at `Wb + σ d` (`iwProg_treeW`).
* `feBProg`, **`feB_exec`**: phase B: the search tree `C₀` of the vertices (parent array at
  `PA`), a cotree `C₁` of it rooted at the face of `g' 0`, and **an isolating weight `w`**
  (`MSSP.IsoW` with that face, `|w| ≤ FN`) with the words `(w d + FN).toNat` at `WW + σ d`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {σ₀ : D ≃ Fin (Fintype.card D)} {νv₀ : V ≃ Fin (Fintype.card V)}
  {τ₀ : F ≃ Fin (Fintype.card F)}

/-- **`iwProg` with its registers.** -/
def feIw (nN nD lc Fb Rb Cb Zb Wb B : ℕ) : Stmt :=
  .seq (feSet [(1700, nN), (1701, nD), (1702, lc), (1703, Fb), (1704, Rb), (1705, Cb),
    (1706, Zb), (1707, Wb), (1708, B)]) iwProg

theorem feIw_natOnly (nN nD lc Fb Rb Cb Zb Wb B : ℕ) :
    natOnly (feIw nN nD lc Fb Rb Cb Zb Wb B) = true := by
  have h : natOnly iwProg = true := by kernel_rfl
  simp only [feIw, natOnly, feSet_natOnly, h, Bool.and_self]

set_option maxHeartbeats 2000000 in
/-- **The isolating weights of a tree of the faces on the machine.** -/
theorem feIw_exec (hf : MSSP.FaceCycle M k g) (C : STFlow.DTree (srcMap hf))
    {fs cs : List (SrcF F k)} (hO : Orders C fs cs) {N FN of Fb Rb Cb Zb Wb : ℕ}
    (cD : Fintype.card (SrcD D k) = N) (cF : Fintype.card (SrcF F k) = FN)
    (c : Config) (hc : WordsBounded W c)
    (hFC : ∀ d, c.nmem (Fb + srcNum σ₀ d) = of + srcFNum τ₀ ((srcMap hf).face d))
    (hRV : ∀ d, c.nmem (Rb + srcNum σ₀ d) = srcNum σ₀ ((srcMap hf).rev d))
    (hCS : ∀ i (h : i < cs.length), c.nmem (Cb + i) = srcNum σ₀ (C.par cs[i]))
    (zF : Zb + (of + FN) ≤ Fb ∨ Fb + N ≤ Zb) (zR : Zb + (of + FN) ≤ Rb ∨ Rb + N ≤ Zb)
    (zC : Zb + (of + FN) ≤ Cb ∨ Cb + FN ≤ Zb)
    (wF : Wb + N ≤ Fb ∨ Fb + N ≤ Wb) (wR : Wb + N ≤ Rb ∨ Rb + N ≤ Wb)
    (wC : Wb + N ≤ Cb ∨ Cb + FN ≤ Wb) (zW : Zb + (of + FN) ≤ Wb ∨ Wb + N ≤ Zb)
    (bF : Fb + N ≤ W) (bR : Rb + N ≤ W) (bC : Cb + FN ≤ W) (bZ : Zb + (of + FN) ≤ W)
    (bW : Wb + N ≤ W) (bN : of + FN + 1 ≤ W) (bB : FN + FN ≤ W) :
    ∃ c' t, Exec P W (feIw (of + FN) N (FN - 1) Fb Rb Cb Zb Wb FN) c c' t ∧
      t ≤ 9 + (5 * (of + FN) + 5 * N + 37 * (FN - 1) + 20) ∧
      (∀ d, c'.nmem (Wb + srcNum σ₀ d) = (MSSP.treeW C d + FN).toNat) ∧
      (∀ a, (a < Zb ∨ Zb + (of + FN) ≤ a) → (a < Wb ∨ Wb + N ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hlc : cs.length = FN - 1 := by rw [orders_ylen_eq hO, cF]
  have hlc' : cs.length ≤ FN := by omega
  obtain ⟨c₁, k₁, e₁, hk₁, hn₁, hr₁, hm₁, hrm₁, ho₁⟩ :=
    feSet_exec (P := P) [(1700, of + FN), (1701, N), (1702, FN - 1), (1703, Fb), (1704, Rb),
      (1705, Cb), (1706, Zb), (1707, Wb), (1708, FN)] (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only <;> omega) c hc
  have hφ : Function.Injective fun y : SrcF F k => of + (srcFNum τ₀ y : ℕ) := fun a b h =>
    (srcFNum τ₀).injective (Fin.ext (by simpa using h))
  have hφn : ∀ y : SrcF F k, of + (srcFNum τ₀ y : ℕ) < of + FN := fun y => by
    have := (srcFNum τ₀ y).2; omega
  subst cD
  have hσs : ∀ i < Fintype.card (SrcD D k), ∃ d, (srcNum σ₀ d : ℕ) = i :=
    fun i hi => ⟨(srcNum σ₀).symm ⟨i, hi⟩, by simp⟩
  have hL : IwLay (of + FN) (Fintype.card (SrcD D k)) cs.length Fb Rb Cb Zb Wb W
      (iwFC (srcMap hf) (srcNum σ₀) fun y => of + (srcFNum τ₀ y : ℕ))
      (iwRV (srcMap hf) (srcNum σ₀)) (iwCS C (srcNum σ₀) cs) := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, zF, zR, by omega, wF, wR, by omega,
      zW, bF, bR, by omega, bZ, bW, bN, by omega, by omega⟩
    · obtain ⟨d, rfl⟩ := hσs i hi; rw [iwFC_apply]; exact hφn _
    · obtain ⟨d, rfl⟩ := hσs i hi; rw [iwRV_apply]; exact (srcNum σ₀ _).2
    · rw [iwCS_apply C _ cs hi]; exact (srcNum σ₀ _).2
  have hI : IwIn (of + FN) (Fintype.card (SrcD D k)) cs.length Fb Rb Cb Zb Wb FN
      (iwFC (srcMap hf) (srcNum σ₀) fun y => of + (srcFNum τ₀ y : ℕ))
      (iwRV (srcMap hf) (srcNum σ₀)) (iwCS C (srcNum σ₀) cs) c₁ := by
    refine ⟨by rw [hn₁]; simp [feSetV], by rw [hn₁]; simp [feSetV],
      by rw [hn₁, hlc]; simp [feSetV], by rw [hn₁]; simp [feSetV], by rw [hn₁]; simp [feSetV],
      by rw [hn₁]; simp [feSetV], by rw [hn₁]; simp [feSetV], by rw [hn₁]; simp [feSetV],
      by rw [hn₁]; simp [feSetV], fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · obtain ⟨d, rfl⟩ := hσs i hi; rw [iwFC_apply, hm₁, hFC]
    · obtain ⟨d, rfl⟩ := hσs i hi; rw [iwRV_apply, hm₁, hRV]
    · rw [iwCS_apply C _ cs hi, hm₁, hCS i hi]
  obtain ⟨c₂, k₂, e₂, hk₂, hWW, hm₂, -, hr₂, hrm₂, ho₂⟩ :=
    iwProg_treeW (P := P) C cs (srcNum σ₀) (fun y => of + (srcFNum τ₀ y : ℕ)) hO.ynd hO.ymem
      hO.ypw hφ hφn (by rw [cF]) (by rw [cF]; exact bB) hL c₁ e₁.wb_right hI
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by simp at hk₁; rw [hlc] at hk₂; omega, fun d => ?_,
    fun a h1 h2 => by rw [hm₂ a h1 h2, hm₁], by rw [hr₂, hr₁], by rw [hrm₂, hrm₁],
    by rw [ho₂, ho₁]⟩
  have := hWW d
  omega

end NegSSSP

end PlanarFlow

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {σ₀ : D ≃ Fin (Fintype.card D)} {νv₀ : V ≃ Fin (Fintype.card V)}
  {τ₀ : F ≃ Fin (Fintype.card F)}

/-- **Phase B**: the search tree of the vertices, a cotree of it, the isolating weights. -/
def feBProg (p : FeP) : Stmt :=
  .seq (feB1Prog p) <|
  .seq (feCot p.N p.FN p.A p.PA p.β (p.β + p.N) (p.A + p.N) p.ZC p.O1 (p.O1 + p.FN)
    (p.O1 + 2 * p.FN) p.nD)
    (feIw (p.A + p.N + p.FN) p.N (p.FN - 1) (p.β + p.N) p.β (p.O1 + p.FN) p.ZI p.WW p.FN)

theorem feBProg_natOnly (p : FeP) : natOnly (feBProg p) = true := by
  simp only [feBProg, natOnly, feB1Prog_natOnly, feCot_natOnly, feIw_natOnly, Bool.and_self]

/-- The cost bound of phase B. -/
def feBCost (p : FeP) : ℕ :=
  osCost p.N p.A + 35 * p.A + 19 * p.N + 34 + (44 + cotCost p.N p.FN p.A) +
    (9 + (5 * (p.A + p.N + p.FN) + 5 * p.N + 37 * (p.FN - 1) + 20))

set_option maxHeartbeats 4000000 in
/-- **Phase B on the machine** (see the module docstring). -/
theorem feB_exec (hf : MSSP.FaceCycle M k g) (hM : M.IsPlane) (p : FeP)
    (hD : p.nD = Fintype.card D) (hk : p.k = k) (hV : p.nV = Fintype.card V)
    (hF : p.nF = Fintype.card F) (hW : p.END ≤ W) (c : Config) (hc : WordsBounded W c)
    (hA : SrcArrM M k g S ℓ σ₀ νv₀ τ₀ p.β p.SL p.N p.A p.AE c.nmem)
    (hone : ∀ j < p.N, c.nmem (p.ONE + j) = 1) :
    ∃ c' t, Exec P W (feBProg p) c c' t ∧ t ≤ feBCost p ∧
      (∃ C₀ : STFlow.DTree (srcMap hf).dual, C₀.root = tripSrc (srcMap hf) k (srcG hf) 0 ∧
        (∀ y, y ≠ C₀.root → c'.nmem (p.PA + srcVNum νv₀ y) = srcNum σ₀ (C₀.par y))) ∧
      (∃ w : SrcD D k → ℤ, MSSP.IsoW (srcMap hf) ((srcMap hf).face (srcG hf 0)) w ∧
        (∀ d, |w d| ≤ Fintype.card (SrcF F k)) ∧
        ∀ d, c'.nmem (p.WW + srcNum σ₀ d) = (w d + Fintype.card (SrcF F k)).toNat) ∧
      (∀ a, a < p.ZV ∨ p.RD ≤ a → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨cD, cV, cF⟩ := fe_cards p hD hk hV hF
  obtain ⟨ru, -, -, -⟩ := fe_roots (σ₀ := σ₀) (νv₀ := νv₀) hf
  have hne := fe_src_ne_dst hf
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ : p.β + 6 * p.N ≤ p.ZV ∧
      p.PA + p.A ≤ p.O1 ∧ p.O1 + 2 * p.FN + 2 = p.ZC ∧ p.ZC + 4 * p.N + 15 * p.FN + 2 = p.WW ∧
      p.WW + p.N = p.ZI ∧ p.ZI + p.AE = p.RD ∧ p.RD ≤ p.END ∧ p.AE = p.A + p.N + p.FN ∧
      p.ZV + 7 * p.A + p.N + 1 = p.O1 ∧ p.PA = p.ZV + 6 * p.A + 1 + p.N := by
    have hE := p.eqs; have hsl := p.slot_le
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18,
      e19, e20, e21, e22, e23⟩ := hE
    obtain ⟨s1, -, -⟩ := hsl
    refine ⟨by omega, by omega, e12.symm, e13.symm, e14.symm, e15.symm, by omega, e4, e11.symm,
      e10⟩
  -- B1
  obtain ⟨c₁, k₁, e₁, hk₁, ⟨C₀, hCr, hPA, hPAu⟩, hm₁, hr₁, hrm₁, ho₁⟩ :=
    feB1_exec (P := P) hf hM p hD hk hV hF hW c hc hA hone
  -- the parent darts as the list `feTs`
  have hlen := feTs_length (srcVNum (k := k) νv₀) (tripSrc (srcMap hf) k (srcG hf) 0)
    (tripDst (srcMap hf) k (srcG hf) 0)
  rw [cV] at hlen
  have hIT : ∀ j (h : j < (feTs (srcVNum (k := k) νv₀) (tripSrc (srcMap hf) k (srcG hf) 0)
      (tripDst (srcMap hf) k (srcG hf) 0)).length), c₁.nmem (p.PA + j) =
      srcNum σ₀ (C₀.par (feTs (srcVNum (k := k) νv₀) (tripSrc (srcMap hf) k (srcG hf) 0)
        (tripDst (srcMap hf) k (srcG hf) 0))[j]) := by
    intro j h
    rw [feTs_get]
    split_ifs with hj
    · have e : j = p.nV := by
        have := congrArg (fun y => (srcVNum (k := k) νv₀ y : ℕ)) hj
        simp only [Equiv.apply_symm_apply] at this
        rw [this, ru, hV]
      rw [e]; exact hPAu
    · have := hPA _ (by rw [hCr]; exact hj)
      simp only [Equiv.apply_symm_apply] at this
      exact this
  have hRV : ∀ d, c₁.nmem (p.β + srcNum σ₀ d) = srcNum σ₀ ((srcMap hf).rev d) := fun d => by
    have := (srcNum σ₀ d).2
    rw [hm₁ _ (by omega)]; exact (hA.arrays hf d).1
  have hNF : ∀ d, c₁.nmem (p.β + p.N + srcNum σ₀ d) =
      (p.A + p.N) + srcFNum τ₀ ((srcMap hf).face d) := fun d => by
    have := (srcNum σ₀ d).2
    rw [hm₁ _ (by omega)]; exact (hA.arrays hf d).2.1
  have hW' := hW
  have hE := p.eqs
  -- B2
  obtain ⟨c₂, k₂, e₂, hk₂, C₁, cs, hC₁r, -, hOr, -, hIC, -, -, hm₂, hr₂, hrm₂, ho₂⟩ :=
    feCot_exec (P := P) (σ₀ := σ₀) (τ₀ := τ₀) (A' := p.A) (N := p.N) (FN := p.FN) (A := p.A)
      (ITb := p.PA) (RVb := p.β) (NFb := p.β + p.N) (Z := p.ZC) (IVb := p.O1)
      (ITc := p.O1 + p.FN) (HDc := p.O1 + 2 * p.FN) hf hM C₀
      (ts := feTs (srcVNum (k := k) νv₀) (tripSrc (srcMap hf) k (srcG hf) 0)
        (tripDst (srcMap hf) k (srcG hf) 0))
      (fun y => by rw [hCr]; exact feTs_mem _ hne y) cD cF hlen c₁ e₁.wb_right hIT hRV hNF
      (by clear * - l2 l3; omega) (by clear * - l1 l2 l3 l10; omega)
      (by clear * - l1 l2 l3 l10; omega) (by clear * - l3; omega) (by omega) (by omega)
      (by clear * - l4 l5 l6 l7 hW'; omega) (by clear * - l4 l5 l6 l7 l8 hW'; omega)
  -- B3
  obtain ⟨c₃, k₃, e₃, hk₃, hWW, hm₃, hr₃, hrm₃, ho₃⟩ :=
    feIw_exec (P := P) hf C₁ hOr (of := p.A + p.N) (Fb := p.β + p.N) (Rb := p.β)
      (Cb := p.O1 + p.FN) (Zb := p.ZI) (Wb := p.WW) cD cF c₂ e₂.wb_right
      (fun d => by
        have := (srcNum σ₀ d).2
        rw [hm₂ _ (by clear * - this cD l1 l2 l3 l10; omega)
          (by clear * - this cD l1 l2 l3 l10; omega)]; exact hNF d)
      (fun d => by
        have := (srcNum σ₀ d).2
        rw [hm₂ _ (by clear * - this cD l1 l2 l3 l10; omega)
          (by clear * - this cD l1 l2 l3 l10; omega)]; exact hRV d) hIC
      (by clear * - l1 l2 l3 l4 l5 l10; omega) (by clear * - l1 l2 l3 l4 l5 l10; omega)
      (by clear * - l1 l2 l3 l4 l5 l10; omega) (by clear * - l1 l2 l3 l4 l5 l10; omega)
      (by clear * - l1 l2 l3 l4 l5 l10; omega) (by clear * - l1 l2 l3 l4 l5 l10; omega)
      (by clear * - l1 l2 l3 l4 l5 l10; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 hW'; omega)
      (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 hW'; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 hW'; omega)
      (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 hW'; omega)
      (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 hW'; omega)
      (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 hW'; omega)
      (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 hW'; omega)
  refine ⟨c₃, k₁ + (k₂ + k₃), Exec.seq e₁ (Exec.seq (by rw [hD]; exact e₂) e₃), ?_, ⟨C₀, hCr, fun y hy => ?_⟩,
    ⟨MSSP.treeW C₁, by rw [← hC₁r]; exact MSSP.treeW_isoW C₁, fun d => MSSP.abs_treeW_le C₁ d,
      fun d => by rw [cF]; exact hWW d⟩, fun a ha => ?_, by rw [hr₃, hr₂, hr₁],
    by rw [hrm₃, hrm₂, hrm₁], by rw [ho₃, ho₂, ho₁]⟩
  · unfold feBCost; clear * - hk₁ hk₂ hk₃; omega
  · have := (srcVNum νv₀ y).2
    rw [hm₃ _ (by clear * - this cV l1 l2 l3 l4 l5 l10; omega)
      (by clear * - this cV l1 l2 l3 l4 l5 l10; omega),
      hm₂ _ (by clear * - this cV l1 l2 l3 l4 l5 l10; omega)
        (by clear * - this cV l1 l2 l3 l4 l5 l10; omega)]
    exact hPA y hy
  · rw [hm₃ _ (by clear * - ha l1 l2 l3 l4 l5 l6 l7 l8 l9 l10; omega) (by clear * - ha l1 l2 l3 l4 l5 l6 l7 l8 l9 l10; omega),
      hm₂ _ (by clear * - ha l1 l2 l3 l4 l5 l6 l7 l8 l9 l10; omega) (by clear * - ha l1 l2 l3 l4 l5 l6 l7 l8 l9 l10; omega),
      hm₁ a (by clear * - ha l1 l2 l3 l4 l5 l6 l7 l8 l9 l10; omega)]

end NegSSSP

end PlanarFlow
