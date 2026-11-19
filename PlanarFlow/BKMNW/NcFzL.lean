module

public import PlanarFlow.BKMNW.NcFzK

/-!
# `fzP` at a node call: the inputs of `pfP` and of the frozen-fix program

* `pend_bound`: the pendant run is bounded by `Z` on the darts of the map (`fixPath_spec`);
* **`pfIn_of`**, **`pfMean_of`**: at a node call with the arguments (`FzPSpec'`), the
  hypotheses `PfIn` and `PfMean` of `pfP` (for the piece map and the frame's dart order).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcFz

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine MfDrv NsStep OrbLab

section Bound

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M₀ : CombMap D V F}

/-- **The pendant run is bounded by `Z` on the darts of the map.** -/
theorem pend_bound (hpl : M₀.IsPlane) (hrot : M₀.RotTrans) (hft : M₀.FaceTrans) (e : V → D)
    (he : ∀ v, M₀.tail (e v) = v) {U f₁ : D → ℤ} {Z : ℕ} (hU : ∀ d, 0 ≤ U d ∧ U d ≤ Z)
    (hf : IsPseudo M₀ U f₁) (Del : Finset V) (π : SPath M₀) (g : NegSSSP.Frame.GIds D F) (I : Input) (x : D) :
    -(Z : ℤ) ≤ fixPath (M₀.pendant e he) (frCap M₀ U f₁ Del) (frFlow M₀ f₁ Del) (π.lift e he)
        (msspP (Klein.msspPlaneK M₀)) (frRef F) (negP (negMach g M₀ I)) (.inl x) ∧
      fixPath (M₀.pendant e he) (frCap M₀ U f₁ Del) (frFlow M₀ f₁ Del) (π.lift e he)
        (msspP (Klein.msspPlaneK M₀)) (frRef F) (negP (negMach g M₀ I)) (.inl x) ≤ Z := by
  have hfix := fixPath_spec (pendant_isPlane he hpl) (frCap_nonneg (fun d => (hU d).1) Del)
    (frFlow_pseudo e he hf Del) (π.lift e he)
    (msspP_spec (e := e) (he := he) (fun ℓ hℓ y hy => Klein.msspPlaneK_spec hpl hrot hft π ℓ hℓ y hy))
    (frRef_spec _) (negP_spec (e := e) (he := he) (negMach_spec g M₀ I))
  have h1 := hfix.pseudo.le_cap (.inl x)
  have h2 := hfix.pseudo.le_cap (.inl (M₀.rev x))
  have h3 := hfix.pseudo.antisymm (.inl x)
  change _ = -_ at h3
  have c1 : frCap M₀ U f₁ Del (.inl x) ≤ Z := by
    simp only [frCap]; split_ifs
    · positivity
    · exact (hU x).2
  have c2 : frCap M₀ U f₁ Del (.inl (M₀.rev x)) ≤ Z := by
    simp only [frCap]; split_ifs
    · positivity
    · exact (hU _).2
  have : (M₀.pendant e he).rev (.inl x) = .inl (M₀.rev x) := rfl
  rw [this] at h3
  constructor <;> linarith

end Bound

section Call

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- **The hypotheses of `pfP` at a node call.** -/
theorem pfIn_of {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    (h : SCond M l r π Hs σ) {d e b m : ℕ} {en : ℕ → D} (hm : 0 < m) {W : ℕ}
    {U f₁ : SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ}
    {Del : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))} {F1b DFb CPb Sb : ℕ}
    {c : Config} (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem)
    (hde : d + fsz m ≤ e) (heb : e ≤ b) (hb1 : b ≤ F1b) (l1 : F1b + m ≤ Sb) (l2 : DFb + m ≤ Sb)
    (l3 : CPb + m ≤ Sb) (wS : Sb + 40 * m + 20 ≤ W) (wZ : 4 * (m * Z) + 4 * Z + 4 ≤ W)
    (r04 : c.nreg 3004 = d) (r00 : c.nreg 9800 = F1b) (r01 : c.nreg 9801 = DFb)
    (r02 : c.nreg 9802 = CPb) (r04' : c.nreg 9804 = Sb)
    (hU : ∀ y, 0 ≤ U y ∧ U y ≤ Z) (hps : IsPseudo (pmap h.1) U f₁)
    (hCP : ∀ i < m, (c.nmem (CPb + i) : ℤ) = U (layEn _ en m hL.en_mem hm i))
    (hF1 : ∀ i < m, (c.nmem (F1b + i) : ℤ) = Z + f₁ (layEn _ en m hL.en_mem hm i))
    (hDF : ∀ i < m, c.nmem (DFb + i) =
      if (pmap h.1).tail (layEn _ en m hL.en_mem hm i) ∈ Del then 1 else 0) :
    PfIn c W d m Z Sb F1b DFb CPb where
  hm := hL.hm
  hz := hL.hz
  m0 := hm
  r04 := r04
  r00 := r00
  r01 := r01
  r02 := r02
  r04' := r04'
  lF := l1
  lD := l2
  lC := l3
  lfr := by unfold fsz at hde; omega
  wS := wS
  wZ := wZ
  rv i hi := (hL.rv i hi).1
  sg i hi := by rw [show d + 4 + m + m + i = d + 4 + 2 * m + i by ring]; exact (hL.sg i hi).1
  df i hi := by rw [hDF i hi]; split_ifs <;> omega
  f1 i hi := by
    have := hF1 i hi
    have h1 := hps.le_cap (layEn _ en m hL.en_mem hm i)
    have h2 := (hU (layEn _ en m hL.en_mem hm i)).2
    omega
  cp i hi := by
    have := hCP i hi
    have h2 := (hU (layEn _ en m hL.en_mem hm i)).2
    omega
  sgp := hL.permOn_sg

/-- **The meaning of `pfP`'s input at a node call.** -/
theorem pfMean_of {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    (h : SCond M l r π Hs σ) {d m : ℕ} {en : ℕ → D} (hm : 0 < m)
    {U f₁ : SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ}
    {Del : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))} {F1b DFb CPb : ℕ}
    {c : Config} (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem)
    (hft : (pmap h.1).FaceTrans)
    (hU : ∀ y, 0 ≤ U y ∧ U y ≤ Z) (hps : IsPseudo (pmap h.1) U f₁)
    (hCP : ∀ i < m, (c.nmem (CPb + i) : ℤ) = U (layEn _ en m hL.en_mem hm i))
    (hF1 : ∀ i < m, (c.nmem (F1b + i) : ℤ) = Z + f₁ (layEn _ en m hL.en_mem hm i))
    (hDF : ∀ i < m, c.nmem (DFb + i) =
      if (pmap h.1).tail (layEn _ en m hL.en_mem hm i) ∈ Del then 1 else 0) :
    PfMean c (pmap h.1) (layEn _ en m hL.en_mem hm) d m Z F1b DFb CPb U f₁ Del where
  inj := (lay_enumOK h.1 hL hm hft).inj
  surj := (lay_enumOK h.1 hL hm hft).surj
  rv i hi := by
    obtain ⟨h1, h2⟩ := hL.rv i hi
    exact Subtype.ext ((layEn_val h1).trans (h2.trans (congrArg M.rev (layEn_val hi).symm)))
  sg i hi := by
    obtain ⟨h1, h2⟩ := hL.sg i hi
    have hr : ∀ y, ((pmap h.1).rot y).1 = σ y.1 := fun y => by unfold pmap; rw [subMap_rot]
    exact Subtype.ext ((layEn_val h1).trans (h2.trans ((congrArg σ (layEn_val hi).symm).trans
      (hr _).symm)))
  vert i hi j hj := by
    have := hL.vert_eq_iff h.1 hi hj
    have e1 : vDart hL hi = layEn _ en m hL.en_mem hm i := Subtype.ext (layEn_val hi).symm
    have e2 : vDart hL hj = layEn _ en m hL.en_mem hm j := Subtype.ext (layEn_val hj).symm
    rw [e1, e2] at this
    exact this
  vsurj v := Quotient.inductionOn v fun y => ⟨y, rfl⟩
  cp := hCP
  f1 := hF1
  df := hDF
  ub := hU
  fb y := by
    have h1 := hps.le_cap y
    have h2 := hps.le_cap ((pmap h.1).rev y)
    have h3 := hps.antisymm y
    have := (hU y).2
    have := (hU ((pmap h.1).rev y)).2
    constructor <;> linarith

end Call

end NcFz

end BKMNW

end PlanarFlow
