module

public import PlanarFlow.BKMNW.NcPar

/-!
# The tail of `c2sP`, part 1: the maximum flow and `F1 = FL + O − 2Z`

**`tailT1_exec`**: from a frame (`Lay`) holding the hole flow `g` (`FL = Z + g`), the arrays
`CAP = c2sCap U g C` (`C` the vertices of the part), `CF = [tail ∈ C]`, `HF = [tail ∈ H]`, and a
base `ib` in the zero area meeting the bounds of `stCallZ`, the program `tgA ; stCallZ ; tgB ;
axL` writes `F1 = Z + (g + st)` with `st` the machine's s-t flow (`stChsG`) on `c2sCap` from `C`
to `H` (the flow `f₁` of `c2sG`), within `stCostZ … + 11 m + 26` steps; the bounds of the words
come from `STOut` (`|st| ≤ 2Z`) and `f1_pseudo` (`|g + st| ≤ Z`).
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

/-- The scratch words of `stCallZ` at a call. -/
noncomputable def stR (x : MCall M) (m : ℕ) : ℕ :=
  3 * (4 * pcoreB (SVert x.2.2 (pdarts M x.1.piece x.2.1))
    (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) m (4 * m + 1) + 3)

/-- The s-t flow of the machine at a hole. -/
lemma stOut_hole (gid : D → ℕ) (I : Input)
    (fb : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → STFlow.StChoice (pmap h))
    {x : MCall M} (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hpl : (pmap hP).IsPlane)
    (hrot : (pmap hP).RotTrans)
    (hinj : ∀ a ∈ pdarts M x.1.piece x.2.1, ∀ b ∈ pdarts M x.1.piece x.2.1, gid a = gid b → a = b)
    {U g : SDart (pdarts M x.1.piece x.2.1) → ℤ} {πj : SPath (pmap hP)}
    {H : Finset (SVert x.2.2 (pdarts M x.1.piece x.2.1))} (hh : HoleC2S (pmap hP) U g πj H) :
    STOut (pmap hP) (c2sCap (pmap hP) U g πj.verts) πj.verts H
      ((stChsG gid I fb x hP).flow (c2sCap (pmap hP) U g πj.verts) πj.verts H) := by
  obtain ⟨πH, hπH⟩ := hh.path
  have hst := STFlow.StChoice.spec hpl (stChsG_OK gid I fb x hP hpl hrot hinj)
  have := hst (c2sCap (pmap hP) U g πj.verts) πj πH (c2sCap_nonneg hh.pseudo πj.verts)
    (by rw [hπH]; exact hh.disj)
  rwa [hπH] at this

set_option maxHeartbeats 1600000 in
/-- **The maximum flow and `F1 = FL + O − 2Z`.** -/
theorem tailT1_exec (I : Input)
    (fb : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → STFlow.StChoice (pmap h))
    {x : MCall M} (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hok : CallOk M S T x)
    (hinj : ∀ a ∈ pdarts M x.1.piece x.2.1, ∀ b ∈ pdarts M x.1.piece x.2.1, gid a = gid b → a = b)
    {m : ℕ} {en : ℕ → D} {d : ℕ} (hm : 0 < m) {W : ℕ} (c : Config) (hc : WordsBounded W c)
    (hL : Lay M gid u S T Z x m en d c.nmem)
    {U g : SDart (pdarts M x.1.piece x.2.1) → ℤ} {πj : SPath (pmap hP)}
    {H : Finset (SVert x.2.2 (pdarts M x.1.piece x.2.1))}
    (hh : HoleC2S (pmap hP) U g πj H) (hU : ∀ y, 0 ≤ U y ∧ U y ≤ Z)
    (hHn : ∃ y, (pmap hP).tail y ∈ H)
    {CAPb CFb HFb ib Ob p F1b Wz : ℕ}
    (r00 : c.nreg 9800 = F1b) (r10 : c.nreg 9810 = CAPb) (r11 : c.nreg 9811 = CFb)
    (r12 : c.nreg 9812 = HFb) (r13 : c.nreg 9813 = ib) (r14 : c.nreg 9814 = Ob)
    (r15 : c.nreg 9815 = p) (r16 : c.nreg 9816 = 2 * Z) (r18 : c.nreg 9818 = m)
    (r19 : c.nreg 9819 = d)
    (hFL : ∀ i < m, (c.nmem (d + 4 + 6 * m + i) : ℤ) =
      Z + g (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i))
    (hCAP : ∀ i < m, c.nmem (CAPb + i) = (c2sCap (pmap hP) U g πj.verts
      (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i)).toNat)
    (hCF : ∀ i < m, c.nmem (CFb + i) =
      flagX (pmap hP) (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm) πj.verts i)
    (hHF : ∀ i < m, c.nmem (HFb + i) =
      flagX (pmap hP) (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm) H i)
    (hz : MemZ Wz c) (oD : Wz < d)
    (l1 : d + 4 + 7 * m ≤ CAPb) (l2 : d + 4 + 7 * m ≤ CFb) (l3 : d + 4 + 7 * m ≤ HFb)
    (l4 : d + 4 + 7 * m ≤ Ob) (l5 : d + 4 + 7 * m ≤ F1b)
    (wC : CAPb + m ≤ W) (wX : CFb + m ≤ W) (wY : HFb + m ≤ W)
    (hWc : stWc (pmap hP) (c2sCap (pmap hP) U g πj.verts) πj.verts H m ≤ Wz)
    (hib : pstWN (101 * m + 45) (stHb (pmap hP) (c2sCap (pmap hP) U g πj.verts) πj.verts H m) < ib)
    (hib0 : 339 * m + 128 ≤ ib)
    (hibz : ib + pstWN (101 * m + 45)
      (stHb (pmap hP) (c2sCap (pmap hP) U g πj.verts) πj.verts H m) ≤ Wz)
    (hOp : Ob + m ≤ p) (hpW : p + stR x m ≤ W) (hZW : 2 * Z + Wz ≤ W)
    (dF : F1b + m ≤ Ob ∨ p + stR x m ≤ F1b) (wF : F1b + m ≤ W) (wZ : 6 * Z ≤ W) :
    ∃ c' t, Exec I W (.seq tgA (.seq stCallZ (.seq tgB axL))) c c' t ∧
      t ≤ 12 + stCostZ m (4 * pcoreB (SVert x.2.2 (pdarts M x.1.piece x.2.1))
        (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) m (4 * m + 1) + 3) +
        10 + (11 * m + 4) ∧
      (∀ i < m, (c'.nmem (F1b + i) : ℤ) =
        Z + (g + (stChsG gid I fb x hP).flow (c2sCap (pmap hP) U g πj.verts) πj.verts H)
          (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i)) ∧
      MemZ Wz c' ∧
      (∀ a, Wz < a → (a < Ob ∨ Ob + m ≤ a) → (a < p ∨ p + stR x m ≤ a) →
        (a < F1b ∨ F1b + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ (StScr r ∨ (9790 ≤ r ∧ r ≤ 9798) ∨ (9820 ≤ r ∧ r ≤ 9822)) →
        c'.nreg r = c.nreg r) ∧
      c'.nreg 9821 = d + 4 + 6 * m ∧ c'.nreg 9796 = m ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hpl, hrot, hft⟩ := lay_plane hP hok hL hm
  -- the bounds of the words
  have hU0 : ∀ y, 0 ≤ U y := fun y => (hU y).1
  have hUZ : ∀ y, U y ≤ (Z : ℤ) := fun y => (hU y).2
  have hS := stOut_hole gid I fb hP hpl hrot hinj hh
  have hstb : ∀ y, -(2 * (Z : ℤ)) ≤
      (stChsG gid I fb x hP).flow (c2sCap (pmap hP) U g πj.verts) πj.verts H y ∧
      (stChsG gid I fb x hP).flow (c2sCap (pmap hP) U g πj.verts) πj.verts H y ≤ 2 * Z :=
    stOut_bound hS (c2sCap_le hh.pseudo hU0 hUZ πj.verts)
  have hf₁ := pseudo_bound (f1_pseudo hh.pseudo hS) hUZ
  have hgb := pseudo_bound hh.pseudo hUZ
  -- the registers of `stCallZ`
  obtain ⟨c₁, k₁, e₁, hk₁, a00, a01, a02, a03, a04, a05, a07, a08, a09, a10, g₁, m₁, rr₁,
    rm₁, o₁⟩ := tgA_exec (P := I) c hc r18 r19 (by omega)
  have hL₁ : Lay M gid u S T Z x m en d c₁.nmem := hL.congr fun a _ _ => by rw [m₁]
  obtain ⟨c₂, k₂, e₂, hk₂, z₂, O₂, f₂, g₂, rr₂, rm₂, o₂⟩ := stCallZ_lay (P := I) (W := W) fb hP
    hok hm (cp := c2sCap (pmap hP) U g πj.verts) (c2sCap_nonneg hh.pseudo πj.verts) hh.disj
    (by obtain ⟨y, hy⟩ := pmap_tail_surj hP (πj.p 0)
        exact ⟨y, by rw [hy]; exact πj.p_mem_init (Nat.zero_le _)⟩) hHn c₁ hL₁
    e₁.wb_right (Cb := CAPb) (Xb := CFb) (Yb := HFb) (ib := ib) (Ob := Ob) (Zo := 2 * Z) (p := p)
    (Wz := Wz) a00 a01 a02 (by rw [a03, r10]) (by rw [a04, r11]) (by rw [a05, r12])
    (by rw [a07, r13]) (by rw [a08, r14]) (by rw [a09, r16]) (by rw [a10, r15])
    (fun i hi => (congrFun m₁ _).trans (hCAP i hi)) (fun i hi => (congrFun m₁ _).trans (hCF i hi))
    (fun i hi => (congrFun m₁ _).trans (hHF i hi)) (by unfold MemZ at hz ⊢; rw [m₁]; exact hz) oD
    (by omega) (by omega) (by omega) (by omega) wC wX wY hWc hib hib0 hibz (by omega) hOp
    (by unfold stR at hpW; omega) hZW
  have q₂ : ∀ r, ¬ StScr r → r ≠ 9820 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [g₂ r h1, g₁ r (fun h => h1 (Or.inr (Or.inr h))) h2]
  have nS : ∀ r, 9757 ≤ r → r ≤ 9899 → ¬ StScr r := fun r h1 h2 h => by
    unfold StScr EncScr at h; omega
  -- the registers of `axL`
  obtain ⟨c₃, k₃, e₃, hk₃, b21, b92, b93, b94, b95, b96, g₃, m₃, rr₃, rm₃, o₃⟩ :=
    tgB_exec (P := I) c₂ e₂.wb_right (m := m) (d := d)
      (by rw [q₂ _ (nS _ (by omega) (by omega)) (by omega), r18])
      (by rw [q₂ _ (nS _ (by omega) (by omega)) (by omega), r19]) (by omega) hm
  have hm₂ : ∀ a, Wz < a → (a < Ob ∨ Ob + m ≤ a) → (a < p ∨ p + stR x m ≤ a) →
      c₂.nmem a = c.nmem a := fun a h1 h2 h3 => by
    rw [f₂ a h1 h2 (by unfold stR at h3; exact h3), m₁]
  have O₂' : ∀ i < m, (c₂.nmem (Ob + i) : ℤ) = max 0 (((2 * Z : ℕ) : ℤ) +
      (stChsG gid I fb x hP).flow (c2sCap (pmap hP) U g πj.verts) πj.verts H
        (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i)) := O₂
  have hO : ∀ i < m, (c₂.nmem (Ob + i) : ℤ) = 2 * Z +
      (stChsG gid I fb x hP).flow (c2sCap (pmap hP) U g πj.verts) πj.verts H
        (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i) := fun i hi => by
    rw [O₂' i hi]
    have := (hstb (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i)).1
    push_cast; omega
  have hFL₂ : ∀ i < m, c₂.nmem (d + 4 + 6 * m + i) = c.nmem (d + 4 + 6 * m + i) :=
    fun i hi => hm₂ _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄, g₄, rr₄, rm₄, o₄⟩ := axL_exec (P := I) c₃ e₃.wb_right
    (m := m) (Xb := d + 4 + 6 * m) (Yb := Ob) (Ob := F1b) (K := 2 * Z)
    ⟨b92, by rw [b93, q₂ _ (nS _ (by omega) (by omega)) (by omega), r14],
      by rw [b94, q₂ _ (nS _ (by omega) (by omega)) (by omega), r00],
      by rw [b95, q₂ _ (nS _ (by omega) (by omega)) (by omega), r16], b96,
      by omega, by omega, wF, by omega,
      fun t ht j hj => by omega, fun t ht j hj => by omega⟩
    (fun t ht => by
      rw [m₃, hFL₂ t ht]
      have h1 := hFL t ht
      have h2 := hO t ht
      have h3 := hstb (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm t)
      have h4 := hgb (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm t)
      omega)
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), e₁.seq (e₂.seq (e₃.seq e₄)), by omega, fun i hi => ?_,
    ?_, fun a h1 h2 h3 h4 => ?_, fun r hr => ?_, ?_, ?_, by rw [rr₄, rr₃, rr₂, rr₁],
    by rw [rm₄, rm₃, rm₂, rm₁], by rw [o₄, o₃, o₂, o₁]⟩
  · rw [v₄ i hi, m₃, hFL₂ i hi]
    have h1 := hFL i hi
    have h2 := hO i hi
    have h3 := hf₁ (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i)
    simp only [Pi.add_apply] at h3 ⊢
    omega
  · intro a ha
    rw [f₄ a (Or.inl (by omega)), m₃]; exact z₂ a ha
  · rw [f₄ a h4, m₃]; exact hm₂ a h1 h2 h3
  · rw [g₄ r (by unfold ArScr; omega), g₃ r (by omega) (by omega),
      q₂ r (fun h => hr (Or.inl h)) (by omega)]
  · rw [g₄ _ (by unfold ArScr; omega)]; exact b21
  · rw [g₄ _ (by unfold ArScr; omega)]; exact b96

end NcStep

end BKMNW

end PlanarFlow
