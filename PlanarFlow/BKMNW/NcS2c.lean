module

public import PlanarFlow.BKMNW.NcTail

/-!
# The tail of `s2cP`: negate, the tail of `c2sP` on the mirrored data, negate

`s2c U g π H = −(c2s (U ∘ rev) (−g) π H)` (`s2c_machNF`). **`s2tP fzP pbP = (tgN ; ngL) ;
c2tP fzP pbP ; (tgN ; ngL)`**: `FL := 2Z − FL` (so `FL = Z + (−g)`), the tail of `c2sP` with the
arrays of the mirrored problem (capacities `U ∘ rev`, flow `−g`), `FL := 2Z − FL`.
**`s2tP_exec`**: from `HoleS2C (pmap h.1) U g πj H` (mirrored by `HoleS2C.mirror`), `FL` ends as
`Z + (machine's s2c) U g πj H`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap MfDrv NsStep StCall STFlow WordRAM WordRAM.Machine
  WordRAM.Machine.Stmt WordRAM.Programs

universe w

/-- The registers of `ngL` for `FL := 2Z − FL` (in place). -/
def tgN : Stmt :=
  block [.constN 9820 4, .addN 9821 9819 9820, .constN 9822 6, .mulN 9822 9822 9818,
    .addN 9821 9821 9822, .copyN 9792 9821, .copyN 9793 9821, .copyN 9794 9821,
    .copyN 9795 9816, .copyN 9796 9818]

/-- **The tail of `s2cP`.** -/
def s2tP (fzP pbP : Stmt) : Stmt := .seq (.seq tgN ngL) (.seq (c2tP fzP pbP) (.seq tgN ngL))

theorem tgN_exec {P : Input} {W : ℕ} (c : Config) (hc : WordsBounded W c) {m d : ℕ}
    (r18 : c.nreg 9818 = m) (r19 : c.nreg 9819 = d) (w : d + 4 + 6 * m ≤ W) (hm : 0 < m) :
    ∃ c' k, Exec P W tgN c c' k ∧ k = 10 ∧ c'.nreg 9821 = d + 4 + 6 * m ∧
      c'.nreg 9792 = d + 4 + 6 * m ∧ c'.nreg 9793 = d + 4 + 6 * m ∧
      c'.nreg 9794 = d + 4 + 6 * m ∧ c'.nreg 9795 = c.nreg 9816 ∧ c'.nreg 9796 = m ∧
      (∀ r, ¬ (9792 ≤ r ∧ r ≤ 9796) → ¬ (9820 ≤ r ∧ r ≤ 9822) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tgN
  exec_block
  all_goals try ((try config_simp); (try simp only [r18, r19]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r18, r19, upd_apply]) <;> (try split_ifs) <;> omega

/-- `FL := 2Z − FL` at a frame. -/
theorem negFL_exec {P : Input} {W : ℕ} (c : Config) (hc : WordsBounded W c) {m d Z : ℕ}
    (r16 : c.nreg 9816 = 2 * Z) (r18 : c.nreg 9818 = m) (r19 : c.nreg 9819 = d)
    (w : d + 4 + 7 * m + 1 ≤ W) (hm : 0 < m) :
    ∃ c' k, Exec P W (.seq tgN ngL) c c' k ∧ k ≤ 10 + (11 * m + 4) ∧
      (∀ t < m, c'.nmem (d + 4 + 6 * m + t) = 2 * Z - c.nmem (d + 4 + 6 * m + t)) ∧
      (∀ a, (a < d + 4 + 6 * m ∨ d + 4 + 6 * m + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ (ArScr r ∨ (9792 ≤ r ∧ r ≤ 9796) ∨ (9820 ≤ r ∧ r ≤ 9822)) →
        c'.nreg r = c.nreg r) ∧
      c'.nreg 9821 = d + 4 + 6 * m ∧ c'.nreg 9796 = m ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a21, a92, a93, a94, a95, a96, g₁, m₁, rr₁, rm₁, o₁⟩ :=
    tgN_exec (P := P) c hc r18 r19 (by omega) hm
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂, g₂, rr₂, rm₂, o₂⟩ := ngL_exec (P := P) c₁ e₁.wb_right
    (m := m) (Xb := d + 4 + 6 * m) (Yb := d + 4 + 6 * m) (Ob := d + 4 + 6 * m) (K := 2 * Z)
    ⟨a92, a93, a94, by rw [a95, r16], a96, by omega, by omega, by omega, by omega,
      fun t ht j hj => by omega, fun t ht j hj => by omega⟩
  refine ⟨c₂, k₁ + k₂, e₁.seq e₂, by omega, fun t ht => by rw [v₂ t ht, m₁],
    fun a ha => by rw [f₂ a ha, m₁], fun r hr => ?_, ?_, ?_, by rw [rr₂, rr₁],
    by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
  · rw [g₂ r (fun h => hr (Or.inl h)), g₁ r (fun h => hr (Or.inr (Or.inl h)))
      (fun h => hr (Or.inr (Or.inr h)))]
  · rw [g₂ _ (by unfold ArScr; omega)]; exact a21
  · rw [g₂ _ (by unfold ArScr; omega)]; exact a96

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The tail of `s2cP` writes the machine's `s2c`.** -/
theorem s2tP_exec {I : Input} {W : ℕ}
    (fb : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → STFlow.StChoice (pmap h))
    {fzP pbP : Stmt} {fzT pbT : MCall M → ℕ → ℕ} {fzR pbR : ℕ → ℕ}
    (hfz : FzPSpec M gid u S T Z I W fzP fzT fzR) (hpb : PbPSpec M gid u S T Z I W pbP pbT pbR)
    {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D} (h : SCond M l r π Hs σ)
    (hok : CallOk M S T (.node l r π, Hs, σ))
    (hinj : ∀ a ∈ pdarts M (l.piece ∪ r.piece) Hs, ∀ b ∈ pdarts M (l.piece ∪ r.piece) Hs,
      gid a = gid b → a = b)
    {d e b m : ℕ} {en : ℕ → D} (hm : 0 < m) {j : ℕ} {πj : SPath (pmap h.1)}
    (hj : (segsP h.1 π.segs h.2)[j]? = some πj)
    {U g : SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ}
    {H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))}
    (hh : HoleS2C (pmap h.1) U g πj H) (hU : ∀ y, 0 ≤ U y ∧ U y ≤ Z)
    (hHn : ∃ y, (pmap h.1).tail y ∈ H)
    (c : Config) (hc : WordsBounded W c)
    (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem) (hSeg : SegsAt' M en m π e b c)
    (hde : d + fsz m ≤ e) (heb : e ≤ b)
    {F1b DFb CPb FFb SbF BTb Gb PBb SbP CAPb CFb HFb ib Ob p Wz : ℕ}
    (hR : TailRegs c d e b m j F1b DFb CPb FFb SbF BTb Gb PBb SbP CAPb CFb HFb ib Ob p)
    (r16 : c.nreg 9816 = 2 * Z) (r18 : c.nreg 9818 = m) (r19 : c.nreg 9819 = d)
    (hz : MemZ Wz c) (oD : Wz < d)
    (hFL : ∀ i < m, (c.nmem (d + 4 + 6 * m + i) : ℤ) =
      Z + g (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i))
    -- the arrays of the mirrored problem (`U ∘ rev`, `−g`)
    (hCAP : ∀ i < m, c.nmem (CAPb + i) = (c2sCap (pmap h.1) (fun y => U ((pmap h.1).rev y)) (-g)
      πj.verts (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i)).toNat)
    (hCF : ∀ i < m, c.nmem (CFb + i) =
      flagX (pmap h.1) (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm) πj.verts i)
    (hHF : ∀ i < m, c.nmem (HFb + i) =
      flagX (pmap h.1) (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm) H i)
    (hCP : ∀ i < m, (c.nmem (CPb + i) : ℤ) =
      U ((pmap h.1).rev (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i)))
    (hDF : ∀ i < m, c.nmem (DFb + i) =
      if (pmap h.1).tail (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i) ∈
        delSet (pmap h.1) (fun y => U ((pmap h.1).rev y)) (-g) πj.verts then 1 else 0)
    (hBT : ∀ i < m, (c.nmem (BTb + i) : ℤ) =
      c2sBeta (pmap h.1) (fun y => U ((pmap h.1).rev y)) (-g) πj.verts
        ((pmap h.1).tail (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i)))
    (hWc : stWc (pmap h.1) (c2sCap (pmap h.1) (fun y => U ((pmap h.1).rev y)) (-g) πj.verts)
      πj.verts H m ≤ Wz)
    (hib : pstWN (101 * m + 45) (stHb (pmap h.1)
      (c2sCap (pmap h.1) (fun y => U ((pmap h.1).rev y)) (-g) πj.verts) πj.verts H m) < ib)
    (hib0 : 339 * m + 128 ≤ ib)
    (hibz : ib + pstWN (101 * m + 45) (stHb (pmap h.1)
      (c2sCap (pmap h.1) (fun y => U ((pmap h.1).rev y)) (-g) πj.verts) πj.verts H m) ≤ Wz)
    (l1 : b ≤ CAPb) (l2 : b ≤ CFb) (l3 : b ≤ HFb) (l4 : b ≤ Ob) (l5 : b ≤ F1b) (l6 : b ≤ DFb)
    (l7 : b ≤ CPb ∨ CPb + m ≤ d + 4 + 6 * m) (l8 : b ≤ FFb) (l9 : b ≤ Gb) (l10 : b ≤ BTb)
    (l11 : b ≤ PBb)
    (hOp : Ob + m ≤ p) (hpF : p + stR (.node l r π, Hs, σ) m ≤ F1b)
    (eF : F1b + m ≤ FFb) (eFG : FFb + m ≤ Gb) (eGP : Gb + m ≤ PBb)
    (eP : PBb + m ≤ SbF) (eSS : SbF ≤ SbP)
    (aC : CAPb + m ≤ Ob) (aX : CFb + m ≤ Ob) (aY : HFb + m ≤ Ob) (aD : DFb + m ≤ Ob)
    (aB : BTb + m ≤ Ob) (aP : CPb + m ≤ Ob)
    (wF : SbF + fzR m ≤ W) (wP : SbP + pbR m ≤ W) (hZW : 2 * Z + Wz ≤ W) (wZ : 6 * Z ≤ W)
    (e' : SVert σ (pdarts M (l.piece ∪ r.piece) Hs) → SDart (pdarts M (l.piece ∪ r.piece) Hs))
    (he' : ∀ v, (pmap h.1).tail (e' v) = v) :
    ∃ c' t, Exec I W (s2tP fzP pbP) c c' t ∧
      t ≤ 10 + (11 * m + 4) + (12 + stCostZ m (4 * pcoreB (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))
        (SFace σ (pdarts M (l.piece ∪ r.piece) Hs) (revPerm M)) m (4 * m + 1) + 3) +
        10 + (11 * m + 4) + (fzT (.node l r π, Hs, σ) j + 4 + (11 * m + 4)) +
        (pbT (.node l r π, Hs, σ) j + 4 + (11 * m + 4))) + (10 + (11 * m + 4)) ∧
      (∀ i < m, (c'.nmem (d + 4 + 6 * m + i) : ℤ) =
        Z + (xCtxN M (machNF gid I (stChsG gid I fb) (pchCall gid)) u S T l r π Hs σ h).O.s2c
          U g πj H (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i)) ∧
      MemZ Wz c' ∧
      (∀ a, a < b → (a < d + 4 + 6 * m ∨ d + 4 + 6 * m + m ≤ a) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      (∀ r, (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) → c'.nreg r = c.nreg r) ∧
      c'.output = c.output := by
  obtain ⟨hpl, hrot, hft⟩ := lay_plane h.1 hok hL hm
  have hUZ : ∀ y, U y ≤ (Z : ℤ) := fun y => (hU y).2
  have hgb := pseudo_bound hh.pseudo hUZ
  have hstep : ∀ i < m, d + 4 + 6 * m + i < b := fun i hi => by unfold fsz at hde; omega
  -- `FL := 2Z − FL`
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁, g₁, a21, a96, rr₁, rm₁, o₁⟩ :=
    negFL_exec (P := I) c hc r16 r18 r19 (by unfold fsz at hde; omega) hm
  have kN : ∀ r, (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) ∨ (9800 ≤ r ∧ r ≤ 9819) →
      c₁.nreg r = c.nreg r := fun r hr => g₁ r (by unfold ArScr; omega)
  have mem₁ : ∀ a, a < d + 4 + 6 * m → c₁.nmem a = c.nmem a := fun a ha => f₁ a (Or.inl ha)
  have mem₁' : ∀ a, d + 4 + 7 * m ≤ a → c₁.nmem a = c.nmem a := fun a ha => f₁ a (Or.inr (by omega))
  have hL₁ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₁.nmem :=
    hL.congr fun a h1 h2 => mem₁ a (by omega)
  have hSeg₁ : SegsAt' M en m π e b c₁ := by
    unfold SegsAt' at hSeg ⊢
    rw [kN _ (by omega)]
    exact hSeg.congr fun a h1 h2 => mem₁' a (by have := hSeg.1.1; unfold fsz at hde; omega)
  have hR₁ : TailRegs c₁ d e b m j F1b DFb CPb FFb SbF BTb Gb PBb SbP CAPb CFb HFb ib Ob p :=
    ⟨by rw [kN _ (by omega)]; exact hR.r3004, by rw [kN _ (by omega)]; exact hR.r3005,
      by rw [kN _ (by omega)]; exact hR.r3006, by rw [kN _ (by omega)]; exact hR.r6800,
      by rw [kN _ (by omega)]; exact hR.r00, by rw [kN _ (by omega)]; exact hR.r01,
      by rw [kN _ (by omega)]; exact hR.r02, by rw [kN _ (by omega)]; exact hR.r03,
      by rw [kN _ (by omega)]; exact hR.r04, by rw [kN _ (by omega)]; exact hR.r05,
      by rw [kN _ (by omega)]; exact hR.r06, by rw [kN _ (by omega)]; exact hR.r07,
      by rw [kN _ (by omega)]; exact hR.r08, by rw [kN _ (by omega)]; exact hR.r10,
      by rw [kN _ (by omega)]; exact hR.r11, by rw [kN _ (by omega)]; exact hR.r12,
      by rw [kN _ (by omega)]; exact hR.r13, by rw [kN _ (by omega)]; exact hR.r14,
      by rw [kN _ (by omega)]; exact hR.r15⟩
  have hU' : ∀ y, 0 ≤ U ((pmap h.1).rev y) ∧ U ((pmap h.1).rev y) ≤ Z := fun y => hU _
  have hz₁ : MemZ Wz c₁ := fun a ha => by rw [mem₁ a (by omega)]; exact hz a ha
  -- the tail of `c2sP` on the mirrored problem
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, z₂, f₂, g₂, o₂⟩ := c2tP_exec fb hfz hpb h hok hinj hm hj
    (U := fun y => U ((pmap h.1).rev y)) (g := -g) (HoleS2C.mirror hh) hU' hHn c₁ e₁.wb_right hL₁ hSeg₁
    hde heb hR₁ (by rw [kN _ (by omega)]; exact r16) (by rw [kN _ (by omega)]; exact r18)
    (by rw [kN _ (by omega)]; exact r19) hz₁ oD
    (fun i hi => by
      rw [v₁ i hi]
      have := hFL i hi
      have := hgb (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i)
      simp only [Pi.neg_apply]; omega)
    (fun i hi => (mem₁' _ (by unfold fsz at hde; omega)).trans (hCAP i hi))
    (fun i hi => (mem₁' _ (by unfold fsz at hde; omega)).trans (hCF i hi))
    (fun i hi => (mem₁' _ (by unfold fsz at hde; omega)).trans (hHF i hi))
    (fun i hi => by
      rcases l7 with l7 | l7
      · rw [mem₁' _ (by unfold fsz at hde; omega)]; exact hCP i hi
      · rw [mem₁ _ (by omega)]; exact hCP i hi)
    (fun i hi => (mem₁' _ (by unfold fsz at hde; omega)).trans (hDF i hi))
    (fun i hi => by rw [mem₁' _ (by unfold fsz at hde; omega)]; exact hBT i hi)
    hWc hib hib0 hibz l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 hOp hpF eF eFG eGP eP eSS aC aX aY aD
    aB aP wF wP hZW wZ e' he'
  -- the bound of the mirrored `c2s`
  have hmssp : MSSPSpecAt (pmap h.1) (Klein.msspPlaneK (pmap h.1)) πj :=
    fun ℓ hℓ x hx => Klein.msspPlaneK_spec hpl hrot hft πj ℓ hℓ x hx
  have hparts := c2sParts hpl (pushSpec_pchCall gid (.node l r π, Hs, σ) h.1 hpl)
    (fun y => (hU' y).1) (fun y => (hU' y).2) (HoleS2C.mirror hh) hmssp (frRef_spec _)
    (negLay_spec gid I (.node l r π, Hs, σ) h.1)
    (STFlow.StChoice.spec hpl (stChsG_OK gid I fb (.node l r π, Hs, σ) h.1 hpl hrot hinj)) e' he'
  have hcb : ∀ y, -(Z : ℤ) ≤ (xCtxN M (machNF gid I (stChsG gid I fb) (pchCall gid)) u S T l r π
      Hs σ h).O.c2s (fun y => U ((pmap h.1).rev y)) (-g) πj H y ∧
      (xCtxN M (machNF gid I (stChsG gid I fb) (pchCall gid)) u S T l r π Hs σ h).O.c2s
        (fun y => U ((pmap h.1).rev y)) (-g) πj H y ≤ Z := fun y => (hparts y).2.2.2.2.2.2
  -- `FL := 2Z − FL`
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃, g₃, -, -, rr₃, rm₃, o₃⟩ := negFL_exec (P := I) c₂ e₂.wb_right (m := m) (d := d) (Z := Z)
    (by rw [g₂ _ (by omega), kN _ (by omega)]; exact r16)
    (by rw [g₂ _ (by omega), kN _ (by omega)]; exact r18)
    (by rw [g₂ _ (by omega), kN _ (by omega)]; exact r19) (by unfold fsz at hde; omega) hm
  have hk₂' : k₂ ≤ 12 + stCostZ m (4 * pcoreB (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))
        (SFace σ (pdarts M (l.piece ∪ r.piece) Hs) (revPerm M)) m (4 * m + 1) + 3) +
        10 + (11 * m + 4) + (fzT (.node l r π, Hs, σ) j + 4 + (11 * m + 4)) +
        (pbT (.node l r π, Hs, σ) j + 4 + (11 * m + 4)) := hk₂
  refine ⟨c₃, k₁ + (k₂ + k₃), e₁.seq (e₂.seq e₃), by omega, fun i hi => ?_, fun a ha => ?_,
    fun a h1 h2 => ?_, fun r hr => ?_, by rw [o₃, o₂, o₁]⟩
  · rw [v₃ i hi, s2c_machNF gid I (stChsG gid I fb) (pchCall gid) u S T h]
    have h1 := v₂ i hi
    have h2 := hcb (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i)
    simp only [Pi.neg_apply]
    omega
  · rw [f₃ a (Or.inl (by omega))]; exact z₂ a ha
  · obtain ⟨x1, x2⟩ := f₂ a h1 h2
    refine ⟨by rw [f₃ a h2, x1, f₁ a h2], by rw [rm₃, x2, rm₁]⟩
  · rw [g₃ r (by unfold ArScr; omega), g₂ r (by omega), kN r (by omega)]

end NcStep

end BKMNW

end PlanarFlow
