module

public import PlanarFlow.BKMNW.NcT2
public import PlanarFlow.BKMNW.NcScanM

/-!
# The tail of `c2sP` writes the machine's `c2s`

**`c2tP_exec`**: at a node call, from the frame holding the hole flow `g` (`FL = Z + g`), the
arrays `CAP = c2sCap`, `CF`, `HF` (flags of the part `πj` and of the hole `H`), `CP = U`,
`DF = [tail ∈ delSet]`, `BT = c2sBeta ∘ tail` and the registers of the tail, the program
**`c2tP fzP pbP`** (with the parameter programs meeting `FzPSpec`, `PbPSpec`) leaves in `FL`
**`Z + (machine's c2s) U g πj H`** — the `c2s` of `xCtxN … (machNF gid I (stChsG gid I fb)
(pchCall gid))` — within `12 + stCostZ … + 10 + (11 m + 4) + fzT x j + 4 + (11 m + 4) + pbT x j +
4 + (11 m + 4)` steps, keeping the memory below `b` off `FL`, the zero area (`MemZ`), the
driver's and the step's registers. The words are bounded through `c2sParts`
(`HoleC2S` at the hole and `0 ≤ U ≤ Z`).
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

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- The registers of the tail and the layout of its arrays (above `b`). -/
structure TailRegs (c : Config) (d e b m j : ℕ)
    (F1b DFb CPb FFb SbF BTb Gb PBb SbP CAPb CFb HFb ib Ob p : ℕ) : Prop where
  r3004 : c.nreg 3004 = d
  r3005 : c.nreg 3005 = e
  r3006 : c.nreg 3006 = b + 5
  r6800 : c.nreg 6800 = j
  r00 : c.nreg 9800 = F1b
  r01 : c.nreg 9801 = DFb
  r02 : c.nreg 9802 = CPb
  r03 : c.nreg 9803 = FFb
  r04 : c.nreg 9804 = SbF
  r05 : c.nreg 9805 = BTb
  r06 : c.nreg 9806 = Gb
  r07 : c.nreg 9807 = PBb
  r08 : c.nreg 9808 = SbP
  r10 : c.nreg 9810 = CAPb
  r11 : c.nreg 9811 = CFb
  r12 : c.nreg 9812 = HFb
  r13 : c.nreg 9813 = ib
  r14 : c.nreg 9814 = Ob
  r15 : c.nreg 9815 = p

set_option maxHeartbeats 4000000 in
/-- **The tail of `c2sP` writes the machine's `c2s`.** -/
theorem c2tP_exec {I : Input} {W : ℕ}
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
    (hh : HoleC2S (pmap h.1) U g πj H) (hU : ∀ y, 0 ≤ U y ∧ U y ≤ Z)
    (hHn : ∃ y, (pmap h.1).tail y ∈ H)
    (c : Config) (hc : WordsBounded W c)
    (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem) (hSeg : SegsAt' M en m π e b c)
    (hde : d + fsz m ≤ e) (heb : e ≤ b)
    {F1b DFb CPb FFb SbF BTb Gb PBb SbP CAPb CFb HFb ib Ob p Wz : ℕ}
    (hR : TailRegs c d e b m j F1b DFb CPb FFb SbF BTb Gb PBb SbP CAPb CFb HFb ib Ob p)
    (r16 : c.nreg 9816 = 2 * Z) (r18 : c.nreg 9818 = m) (r19 : c.nreg 9819 = d)
    (hz : MemZ Wz c) (oD : Wz < d)
    -- the arrays
    (hFL : ∀ i < m, (c.nmem (d + 4 + 6 * m + i) : ℤ) =
      Z + g (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i))
    (hCAP : ∀ i < m, c.nmem (CAPb + i) = (c2sCap (pmap h.1) U g πj.verts
      (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i)).toNat)
    (hCF : ∀ i < m, c.nmem (CFb + i) =
      flagX (pmap h.1) (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm) πj.verts i)
    (hHF : ∀ i < m, c.nmem (HFb + i) =
      flagX (pmap h.1) (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm) H i)
    (hCP : ∀ i < m, (c.nmem (CPb + i) : ℤ) =
      U (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i))
    (hDF : ∀ i < m, c.nmem (DFb + i) =
      if (pmap h.1).tail (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i) ∈
        delSet (pmap h.1) U g πj.verts then 1 else 0)
    (hBT : ∀ i < m, (c.nmem (BTb + i) : ℤ) = c2sBeta (pmap h.1) U g πj.verts
      ((pmap h.1).tail (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i)))
    -- the bounds of `stCallZ`
    (hWc : stWc (pmap h.1) (c2sCap (pmap h.1) U g πj.verts) πj.verts H m ≤ Wz)
    (hib : pstWN (101 * m + 45)
      (stHb (pmap h.1) (c2sCap (pmap h.1) U g πj.verts) πj.verts H m) < ib)
    (hib0 : 339 * m + 128 ≤ ib)
    (hibz : ib + pstWN (101 * m + 45)
      (stHb (pmap h.1) (c2sCap (pmap h.1) U g πj.verts) πj.verts H m) ≤ Wz)
    -- the layout: `[b, …)`: `CAP CF HF CP? DF BT | O | p-region | F1 FF G PB | SbF/SbP`
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
    ∃ c' t, Exec I W (c2tP fzP pbP) c c' t ∧
      t ≤ 12 + stCostZ m (4 * pcoreB (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))
        (SFace σ (pdarts M (l.piece ∪ r.piece) Hs) (revPerm M)) m (4 * m + 1) + 3) +
        10 + (11 * m + 4) + (fzT (.node l r π, Hs, σ) j + 4 + (11 * m + 4)) +
        (pbT (.node l r π, Hs, σ) j + 4 + (11 * m + 4)) ∧
      (∀ i < m, (c'.nmem (d + 4 + 6 * m + i) : ℤ) =
        Z + (xCtxN M (machNF gid I (stChsG gid I fb) (pchCall gid)) u S T l r π Hs σ h).O.c2s
          U g πj H (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i)) ∧
      MemZ Wz c' ∧
      (∀ a, a < b → (a < d + 4 + 6 * m ∨ d + 4 + 6 * m + m ≤ a) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      (∀ r, (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) ∨ (9800 ≤ r ∧ r ≤ 9819) →
        c'.nreg r = c.nreg r) ∧
      c'.output = c.output := by
  obtain ⟨hpl, hrot, hft⟩ := lay_plane h.1 hok hL hm
  have hU0 : ∀ y, 0 ≤ U y := fun y => (hU y).1
  have hUZ : ∀ y, U y ≤ (Z : ℤ) := fun y => (hU y).2
  have hS := stOut_hole (x := (.node l r π, Hs, σ)) gid I fb h.1 hpl hrot hinj hh
  have hf₁ := f1_pseudo hh.pseudo hS
  have hmssp : MSSPSpecAt (pmap h.1) (Klein.msspPlaneK (pmap h.1)) πj :=
    fun ℓ hℓ x hx => Klein.msspPlaneK_spec hpl hrot hft πj ℓ hℓ x hx
  have hparts := c2sParts hpl (pushSpec_pchCall gid (.node l r π, Hs, σ) h.1 hpl) hU0 hUZ hh
    hmssp (frRef_spec _) (negLay_spec gid I (.node l r π, Hs, σ) h.1)
    (STFlow.StChoice.spec hpl (stChsG_OK gid I fb (.node l r π, Hs, σ) h.1 hpl hrot hinj)) e' he'
  have hstep : ∀ i < m, d + 4 + 6 * m + i < b := fun i hi => by unfold fsz at hde; omega
  -- part 1
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, z₁, f₁, g₁, a21, a96, rr₁, rm₁, o₁⟩ := tailT1_exec (W := W) (x := (.node l r π, Hs, σ)) I fb
    h.1 hok hinj hm c hc hL hh hU hHn hR.r00 hR.r10 hR.r11 hR.r12 hR.r13 hR.r14 hR.r15 r16 r18 r19
    hFL hCAP hCF hHF hz oD (by unfold fsz at hde; omega) (by unfold fsz at hde; omega)
    (by unfold fsz at hde; omega) (by unfold fsz at hde; omega) (by unfold fsz at hde; omega)
    (by omega) (by omega) (by omega)
    hWc hib hib0 hibz hOp (by omega) hZW (Or.inr hpF)
    (by omega) wZ
  have nS : ∀ r, ¬ (StScr r ∨ (9790 ≤ r ∧ r ≤ 9798) ∨ (9820 ≤ r ∧ r ≤ 9822)) →
      c₁.nreg r = c.nreg r := g₁
  have kS : ∀ r, (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) ∨ (9800 ≤ r ∧ r ≤ 9819) →
      ¬ (StScr r ∨ (9790 ≤ r ∧ r ≤ 9798) ∨ (9820 ≤ r ∧ r ≤ 9822)) := fun r hr hh' => by
    unfold StScr EncScr at hh'; omega
  have mem₁ : ∀ a, a < Ob → c₁.nmem a = c.nmem a := fun a ha => by
    by_cases hw : Wz < a
    · exact f₁ a hw (Or.inl ha) (Or.inl (by omega)) (Or.inl (by omega))
    · rw [z₁ a (by omega), hz a (by omega)]
  have hL₁ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₁.nmem :=
    hL.congr fun a h1 h2 => mem₁ a (by unfold fsz at hde; omega)
  have hSeg₁ : SegsAt' M en m π e b c₁ := by
    unfold SegsAt' at hSeg ⊢
    rw [nS _ (kS _ (by omega))]
    exact hSeg.congr fun a h1 h2 => mem₁ a (by have := hSeg.1.2.2.1; omega)
  -- part 2
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂, g₂, o₂⟩ := tailT2_exec hfz h hok hm hj e' he' c₁ e₁.wb_right
    hL₁ hSeg₁ hde heb (F1b := F1b) (DFb := DFb) (CPb := CPb) (FFb := FFb) (Gb := Gb)
    (Sb := SbF) (Wz := Wz)
    (by rw [nS _ (kS _ (by omega)), hR.r3004]) (by rw [nS _ (kS _ (by omega)), hR.r3005])
    (by rw [nS _ (kS _ (by omega)), hR.r3006]) (by rw [nS _ (kS _ (by omega)), hR.r6800])
    (by rw [nS _ (kS _ (by omega)), hR.r00]) (by rw [nS _ (kS _ (by omega)), hR.r01])
    (by rw [nS _ (kS _ (by omega)), hR.r02]) (by rw [nS _ (kS _ (by omega)), hR.r03])
    (by rw [nS _ (kS _ (by omega)), hR.r04]) (by rw [nS _ (kS _ (by omega)), hR.r06])
    (by rw [nS _ (kS _ (by omega)), r16]) a21 a96
    l5 l6 l7 l8 l9 (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl eF)
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl eFG) wF oD z₁ (by omega) hU hf₁
    (fun i hi => (congrArg (fun z : ℕ => (z : ℤ)) (mem₁ _ (by omega))).trans (hCP i hi))
    (fun i hi => v₁ i hi)
    (fun i hi => (mem₁ _ (by omega)).trans (hDF i hi))
    (fun i hi => (congrArg (fun z : ℕ => (z : ℤ)) (mem₁ _ (by unfold fsz at hde; omega))).trans
      (hFL i hi))
    (fun y => (hparts y).2.2.2.1) (fun y => (hparts y).2.2.2.2.2.1)
  have mem₂ : ∀ a, a < FFb → c₂.nmem a = c₁.nmem a := fun a ha =>
    (f₂ a (by omega) (Or.inl ha) (Or.inl (by omega))).1
  have nS₂ : ∀ r, (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) ∨ (9800 ≤ r ∧ r ≤ 9821) →
      c₂.nreg r = c₁.nreg r := fun r hr =>
    g₂ r (by unfold PKeep; omega) (by unfold ArScr; omega)
  have hL₂ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₂.nmem :=
    hL₁.congr fun a h1 h2 => mem₂ a (by unfold fsz at hde; omega)
  have hSeg₂ : SegsAt' M en m π e b c₂ := by
    unfold SegsAt' at hSeg₁ ⊢
    rw [nS₂ _ (by omega)]
    exact hSeg₁.congr fun a h1 h2 => mem₂ a (by have := hSeg₁.1.2.2.1; omega)
  have hz₂ : MemZ Wz c₂ := fun a ha => by rw [mem₂ a (by omega)]; exact z₁ a ha
  have a96₂ : c₂.nreg 9796 = m := by
    rw [g₂ _ (by unfold PKeep; omega) (by unfold ArScr; omega)]; exact a96
  -- the push-back's data
  set ff := fixFrozen (pmap h.1) e' he' (Klein.msspPlaneK (pmap h.1)) (frRef _)
    (negLay gid I (.node l r π, Hs, σ) h.1) U
    (HAdd.hAdd (α := SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ)
      (β := SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ) g
      ((stChsG gid I fb (.node l r π, Hs, σ) h.1).flow (c2sCap (pmap h.1) U g πj.verts)
        πj.verts H)) πj (delSet (pmap h.1) U g πj.verts) with hffdef
  have eG := c2sG_eqE e' he' (pchCall gid (.node l r π, Hs, σ) h.1) (Klein.msspPlaneK (pmap h.1))
    (frRef _) (negLay gid I (.node l r π, Hs, σ) h.1) (stChsG gid I fb (.node l r π, Hs, σ) h.1).flow
    U g πj H
  have hres : ∀ y, pchCall gid (.node l r π, Hs, σ) h.1 (c2sBeta (pmap h.1) U g πj.verts) ∅
      (ff - g) y = c2sG (pmap h.1) (pchCall gid (.node l r π, Hs, σ) h.1)
        (Klein.msspPlaneK (pmap h.1)) (frRef _) (negLay gid I (.node l r π, Hs, σ) h.1)
        (stChsG gid I fb (.node l r π, Hs, σ) h.1).flow U g πj H y - g y := fun y => by
    rw [eG]; exact (add_sub_cancel_left _ _).symm
  have hffb : ∀ y, -(Z : ℤ) ≤ ff y ∧ ff y ≤ Z := fun y => (hparts y).2.2.2.2.2.1
  have hc2b : ∀ y, -(Z : ℤ) ≤ c2sG (pmap h.1) (pchCall gid (.node l r π, Hs, σ) h.1)
        (Klein.msspPlaneK (pmap h.1)) (frRef _) (negLay gid I (.node l r π, Hs, σ) h.1)
        (stChsG gid I fb (.node l r π, Hs, σ) h.1).flow U g πj H y ∧
      c2sG (pmap h.1) (pchCall gid (.node l r π, Hs, σ) h.1)
        (Klein.msspPlaneK (pmap h.1)) (frRef _) (negLay gid I (.node l r π, Hs, σ) h.1)
        (stChsG gid I fb (.node l r π, Hs, σ) h.1).flow U g πj H y ≤ Z :=
    fun y => (hparts y).2.2.2.2.2.2
  have hgb : ∀ y, -(Z : ℤ) ≤ g y ∧ g y ≤ Z := fun y => (hparts y).2.2.2.1
  have hg'b : ∀ y, -(2 * (Z : ℤ)) ≤ (ff - g) y ∧ (ff - g) y ≤ 2 * Z := fun y => by
    have h1 := hgb y; have h2 := hffb y
    simp only [Pi.sub_apply]; constructor <;> omega
  have hresb : ∀ y, -(2 * (Z : ℤ)) ≤ pchCall gid (.node l r π, Hs, σ) h.1
      (c2sBeta (pmap h.1) U g πj.verts) ∅ (ff - g) y ∧
      pchCall gid (.node l r π, Hs, σ) h.1 (c2sBeta (pmap h.1) U g πj.verts) ∅ (ff - g) y ≤
        2 * Z := fun y => by
    rw [hres y]; have h1 := hgb y; have h2 := hc2b y
    constructor <;> omega
  have hsumb : ∀ y, -(Z : ℤ) ≤ g y + pchCall gid (.node l r π, Hs, σ) h.1
      (c2sBeta (pmap h.1) U g πj.verts) ∅ (ff - g) y := fun y => by
    rw [hres y]; have := hc2b y; omega
  -- part 3
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃, g₃, o₃⟩ := tailT3_exec hpb h hok hm (j := j)
    (β := c2sBeta (pmap h.1) U g πj.verts) (g := g) (g' := ff - g) c₂ e₂.wb_right hL₂ hSeg₂
    hde heb (BTb := BTb) (Gb := Gb) (PBb := PBb) (Sb := SbP) (Wz := Wz)
    (by rw [nS₂ _ (by omega), nS _ (kS _ (by omega)), hR.r3004])
    (by rw [nS₂ _ (by omega), nS _ (kS _ (by omega)), hR.r3005])
    (by rw [nS₂ _ (by omega), nS _ (kS _ (by omega)), hR.r3006])
    (by rw [nS₂ _ (by omega), nS _ (kS _ (by omega)), hR.r6800])
    (by rw [nS₂ _ (by omega), nS _ (kS _ (by omega)), hR.r05])
    (by rw [nS₂ _ (by omega), nS _ (kS _ (by omega)), hR.r06])
    (by rw [nS₂ _ (by omega), nS _ (kS _ (by omega)), hR.r07])
    (by rw [nS₂ _ (by omega), nS _ (kS _ (by omega)), hR.r08])
    (by rw [nS₂ _ (by omega), nS _ (kS _ (by omega)), r16])
    (by rw [nS₂ _ (by omega)]; exact a21) a96₂
    l10 l9 l11 (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl eGP) wP oD hz₂ wZ
    (c2sBeta_nonneg hh.pre) hg'b hresb
    (fun i hi => (congrArg (fun z : ℕ => (z : ℤ)) ((mem₂ _ (by omega)).trans
      (mem₁ _ (by omega)))).trans (hBT i hi))
    (fun i hi => by rw [v₂ i hi]; rfl)
    (fun i hi => (congrArg (fun z : ℕ => (z : ℤ)) ((mem₂ _ (by unfold fsz at hde; omega)).trans
      (mem₁ _ (by unfold fsz at hde; omega)))).trans (hFL i hi))
    hgb hsumb
  refine ⟨c₃, k₁ + (k₂ + k₃), e₁.seq (e₂.seq e₃), ?_, fun i hi => ?_, fun a ha => ?_,
    fun a h1 h2 => ?_, fun r hr => ?_, by rw [o₃, o₂, o₁]⟩
  · have hk₁' : k₁ ≤ 12 + stCostZ m (4 * pcoreB (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))
        (SFace σ (pdarts M (l.piece ∪ r.piece) Hs) (revPerm M)) m (4 * m + 1) + 3) +
        10 + (11 * m + 4) := hk₁
    omega
  · rw [v₃ i hi, c2s_machNF gid I (stChsG gid I fb) (pchCall gid) u S T h e' he']
    rfl
  · rw [(f₃ a (by omega) (Or.inl (by omega)) (Or.inl (by omega))).1]; exact hz₂ a ha
  · obtain ⟨x1, x2⟩ := f₃ a (by omega) (Or.inl (by omega)) h2
    obtain ⟨y1, y2⟩ := f₂ a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    refine ⟨by rw [x1, y1, mem₁ a (by omega)], by rw [x2, y2, rm₁]⟩
  · rw [g₃ r (by unfold PKeep; omega) (by unfold ArScr; omega), nS₂ r (by omega),
      nS r (kS r (by omega))]

end NcStep

end BKMNW

end PlanarFlow
