module

public import PlanarFlow.BKMNW.NcTail
public import PlanarFlow.BKMNW.ThChsE

/-!
# The tail of `c2sP` relative to the machine's family `machNFT`

The choice families `(x : MCall M) → (h : PieceInv …) → StChoice (pmap h)` do not
exist (`NsStep.chs_isEmpty`), so `c2tP_exec` (stated with `machNF … (stChsG gid I fb)`) cannot be
applied. Here the same statements relative to **`machNFT gid I (pchCall gid)`** (s-t flow
`stFlowT gid I x h`, ThChsE.lean), with the same proofs:

* `stFlowT_lay` (at a frame, `stFlowT` is the flow of `stChoiceOf` of the frame order),
  **`stCallZ_layT`**, `stOut_holeT`, **`tailT1_execT`**, `c2s_machNFT`, `s2c_machNFT`,
  **`c2tP_execT`** (the tail writes `Z + (machNFT's c2s) U g πj H`).
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

section Call

variable {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}

/-- **At a frame, `stFlowT` is the flow of the choices of the frame order.** -/
theorem stFlowT_lay (I : Input)
    (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem) (hm : 0 < m)
    (hft : (pmap hP).FaceTrans) [hT : Nonempty (STFlow.DTree (pmap hP))] :
    stFlowT gid I x hP = (stChoiceOf (lay_enumOK hP hl hm hft) I).flow := by
  have hc := lay_card hP hl hm hft
  have hg := lay_gOrd hP hl hm hft hc
  have hx : ∃ en', GOrd gid x hP en' := ⟨_, hg⟩
  unfold stFlowT
  simp only [hx, hT, ↓reduceDIte]
  rw [stChoiceOf_congr _ _ (gOrd_unique hx.choose_spec hg) hc.symm I]

set_option maxHeartbeats 1000000 in
/-- **`stCallZ` at a frame** writes the s-t flow `stFlowT` (input `P` of the run):
the reverse and rotation arrays are the frame's `RV = d + 4 + m`, `SG = d + 4 + 2 m`; the
capacity and the two flag arrays are given in the frame order. -/
theorem stCallZ_layT
    (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hok : CallOk M S T x) (hm : 0 < m)
    {P : Input} {W : ℕ} {cp : SDart (pdarts M x.1.piece x.2.1) → ℤ} (hcp : ∀ d, 0 ≤ cp d)
    {X Y : Finset (SVert x.2.2 (pdarts M x.1.piece x.2.1))} (hXY : Disjoint X Y)
    (hXn : ∃ d, (pmap hP).tail d ∈ X) (hYn : ∃ d, (pmap hP).tail d ∈ Y) (c : Config)
    (hl : Lay M gid u S T Z x m en d c.nmem)
    (hc : WordsBounded W c) {Cb Xb Yb ib Ob Zo p Wz : ℕ}
    (r00 : c.nreg 9100 = m) (r01 : c.nreg 9101 = d + 4 + m) (r02 : c.nreg 9102 = d + 4 + 2 * m)
    (r03 : c.nreg 9103 = Cb) (r04 : c.nreg 9104 = Xb) (r05 : c.nreg 9105 = Yb)
    (r07 : c.nreg 9107 = ib) (r08 : c.nreg 9108 = Ob) (r09 : c.nreg 9109 = Zo)
    (r10 : c.nreg 9110 = p)
    (hC : ∀ i < m, c.nmem (Cb + i) =
      (cp (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i)).toNat)
    (hX : ∀ i < m, c.nmem (Xb + i) =
      flagX (pmap hP) (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm) X i)
    (hY : ∀ i < m, c.nmem (Yb + i) =
      flagX (pmap hP) (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm) Y i)
    (hz : MemZ Wz c) (oD : Wz < d) (oC : Wz < Cb) (oX : Wz < Xb) (oY : Wz < Yb)
    (wD : d + 4 + 3 * m ≤ W) (wC : Cb + m ≤ W) (wX : Xb + m ≤ W) (wY : Yb + m ≤ W)
    (hWc : stWc (pmap hP) cp X Y m ≤ Wz)
    (hib : pstWN (101 * m + 45) (stHb (pmap hP) cp X Y m) < ib) (hib0 : 339 * m + 128 ≤ ib)
    (hibz : ib + pstWN (101 * m + 45) (stHb (pmap hP) cp X Y m) ≤ Wz)
    (hO : Wz < Ob) (hOp : Ob + m ≤ p)
    (hpW : p + 3 * (4 * pcoreB (SVert x.2.2 (pdarts M x.1.piece x.2.1))
      (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) m (4 * m + 1) + 3) ≤ W)
    (hZW : Zo + Wz ≤ W) :
    ∃ c' t, Exec P W stCallZ c c' t ∧
      t ≤ stCostZ m (4 * pcoreB (SVert x.2.2 (pdarts M x.1.piece x.2.1))
        (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) m (4 * m + 1) + 3) ∧
      MemZ Wz c' ∧
      (∀ i < m, (c'.nmem (Ob + i) : ℤ) = max 0 ((Zo : ℤ) + stFlowT gid P x hP cp X Y
        (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i))) ∧
      (∀ a, Wz < a → (a < Ob ∨ Ob + m ≤ a) →
        (a < p ∨ p + 3 * (4 * pcoreB (SVert x.2.2 (pdarts M x.1.piece x.2.1))
          (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) m (4 * m + 1) + 3) ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ StScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hpl, hrot, hft⟩ := lay_plane hP hok hl hm
  have he := lay_enumOK hP hl hm hft
  have hT := dtree_nonempty hpl hrot he hm (pmap_tail_surj hP)
  have hflow := stFlowT_lay (I := P) hP hl hm hft
  rw [hflow]
  exact stCallZ_exec hpl hrot he (enumOK_dual he hrot (pmap_tail_surj hP)) hm hcp hXY hXn hYn c
    hc r00 r01 r02 r03 r04 r05 r07 r08 r09 r10 (fun i hi => lay_rv hP hl hm hft hi)
    (fun i hi => lay_rt hP hl hm hft hi) hC hX hY hz (by omega) (by omega) oC oX oY
    (by omega) (by omega) wC wX wY hWc hib hib0 hibz hO hOp hpW hZW

end Call

/-- The s-t flow of the machine at a hole. -/
lemma stOut_holeT (gid : D → ℕ) (I : Input)
    {x : MCall M} (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hpl : (pmap hP).IsPlane)
    (hrot : (pmap hP).RotTrans)
    (hinj : ∀ a ∈ pdarts M x.1.piece x.2.1, ∀ b ∈ pdarts M x.1.piece x.2.1, gid a = gid b → a = b)
    {U g : SDart (pdarts M x.1.piece x.2.1) → ℤ} {πj : SPath (pmap hP)}
    {H : Finset (SVert x.2.2 (pdarts M x.1.piece x.2.1))} (hh : HoleC2S (pmap hP) U g πj H) :
    STOut (pmap hP) (c2sCap (pmap hP) U g πj.verts) πj.verts H
      (stFlowT gid I x hP (c2sCap (pmap hP) U g πj.verts) πj.verts H) := by
  obtain ⟨πH, hπH⟩ := hh.path
  obtain ⟨hx, hT, e, hok⟩ := stFlowT_eq gid I x hP hpl hrot hinj
  have hst := STFlow.StChoice.spec hpl hok
  rw [e]
  have := hst (c2sCap (pmap hP) U g πj.verts) πj πH (c2sCap_nonneg hh.pseudo πj.verts)
    (by rw [hπH]; exact hh.disj)
  rwa [hπH] at this

set_option maxHeartbeats 1600000 in
/-- **The maximum flow and `F1 = FL + O − 2Z`.** -/
theorem tailT1_execT (I : Input)
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
        Z + (g + stFlowT gid I x hP (c2sCap (pmap hP) U g πj.verts) πj.verts H)
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
  have hS := stOut_holeT gid I hP hpl hrot hinj hh
  have hstb : ∀ y, -(2 * (Z : ℤ)) ≤
      stFlowT gid I x hP (c2sCap (pmap hP) U g πj.verts) πj.verts H y ∧
      stFlowT gid I x hP (c2sCap (pmap hP) U g πj.verts) πj.verts H y ≤ 2 * Z :=
    stOut_bound hS (c2sCap_le hh.pseudo hU0 hUZ πj.verts)
  have hf₁ := pseudo_bound (f1_pseudo hh.pseudo hS) hUZ
  have hgb := pseudo_bound hh.pseudo hUZ
  -- the registers of `stCallZ`
  obtain ⟨c₁, k₁, e₁, hk₁, a00, a01, a02, a03, a04, a05, a07, a08, a09, a10, g₁, m₁, rr₁,
    rm₁, o₁⟩ := tgA_exec (P := I) c hc r18 r19 (by omega)
  have hL₁ : Lay M gid u S T Z x m en d c₁.nmem := hL.congr fun a _ _ => by rw [m₁]
  obtain ⟨c₂, k₂, e₂, hk₂, z₂, O₂, f₂, g₂, rr₂, rm₂, o₂⟩ := stCallZ_layT (P := I) (W := W) hP
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
      stFlowT gid I x hP (c2sCap (pmap hP) U g πj.verts) πj.verts H
        (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i)) := O₂
  have hO : ∀ i < m, (c₂.nmem (Ob + i) : ℤ) = 2 * Z +
      stFlowT gid I x hP (c2sCap (pmap hP) U g πj.verts) πj.verts H
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

/-- **The `c2s` of the machine's node subroutines** with any dart at each vertex. -/
theorem c2s_machNFT (gid : D → ℕ) (I : WordRAM.Input)
    (pch : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) →
      PushFn (SDart (pdarts M x.1.piece x.2.1)) (SVert x.2.2 (pdarts M x.1.piece x.2.1)))
    (u : D → ℤ) (S T : Finset V) {l r : ADec M} {π : HSep M} {Hs : List (Finset V)}
    {σ : Perm D} (h : SCond M l r π Hs σ)
    (e : SVert σ (pdarts M (l.piece ∪ r.piece) Hs) → SDart (pdarts M (l.piece ∪ r.piece) Hs))
    (he : ∀ v, (pmap h.1).tail (e v) = v) (U f : SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ)
    (πj : SPath (pmap h.1)) (H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))) :
    (xCtxN M (machNFT gid I pch) u S T l r π Hs σ h).O.c2s U f πj H =
      f + @id (SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ)
        (pch (.node l r π, Hs, σ) h.1 (c2sBeta (pmap h.1) U f πj.verts) ∅
        (fixFrozen (pmap h.1) e he (Klein.msspPlaneK (pmap h.1)) (frRef _)
          (negLay gid I (.node l r π, Hs, σ) h.1) U
          (f + @id (SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ)
            (stFlowT gid I (.node l r π, Hs, σ) h.1 (c2sCap (pmap h.1) U f πj.verts) πj.verts H))
          πj (delSet (pmap h.1) U f πj.verts) - f)) :=
  c2sG_eqE e he _ _ _ _ _ U f πj H

/-- **The `s2c` of the machine's node subroutines** is its `c2s` on the reversed capacities and
the opposite flow, negated. -/
theorem s2c_machNFT (gid : D → ℕ) (I : WordRAM.Input)
    (pch : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) →
      PushFn (SDart (pdarts M x.1.piece x.2.1)) (SVert x.2.2 (pdarts M x.1.piece x.2.1)))
    (u : D → ℤ) (S T : Finset V) {l r : ADec M} {π : HSep M} {Hs : List (Finset V)}
    {σ : Perm D} (h : SCond M l r π Hs σ) (U f : SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ)
    (πj : SPath (pmap h.1)) (H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))) :
    (xCtxN M (machNFT gid I pch) u S T l r π Hs σ h).O.s2c U f πj H =
      -((xCtxN M (machNFT gid I pch) u S T l r π Hs σ h).O.c2s
        (fun d => U ((pmap h.1).rev d)) (-f) πj H) := rfl

set_option maxHeartbeats 4000000 in
/-- **The tail of `c2sP` writes the machine's `c2s`.** -/
theorem c2tP_execT {I : Input} {W : ℕ}
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
        Z + (xCtxN M (machNFT gid I (pchCall gid)) u S T l r π Hs σ h).O.c2s
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
  obtain ⟨hxT, hTT, hstT, hokT⟩ := stFlowT_eq gid I (.node l r π, Hs, σ) h.1 hpl hrot hinj
  have hS := stOut_holeT (x := (.node l r π, Hs, σ)) gid I h.1 hpl hrot hinj hh
  have hf₁ := f1_pseudo hh.pseudo hS
  have hmssp : MSSPSpecAt (pmap h.1) (Klein.msspPlaneK (pmap h.1)) πj :=
    fun ℓ hℓ x hx => Klein.msspPlaneK_spec hpl hrot hft πj ℓ hℓ x hx
  have hparts := c2sParts hpl (pushSpec_pchCall gid (.node l r π, Hs, σ) h.1 hpl) hU0 hUZ hh
    hmssp (frRef_spec _) (negLay_spec gid I (.node l r π, Hs, σ) h.1)
    (hstT ▸ STFlow.StChoice.spec hpl hokT) e' he'
  have hstep : ∀ i < m, d + 4 + 6 * m + i < b := fun i hi => by unfold fsz at hde; omega
  -- part 1
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, z₁, f₁, g₁, a21, a96, rr₁, rm₁, o₁⟩ := tailT1_execT (W := W) (x := (.node l r π, Hs, σ)) I
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
      (stFlowT gid I (.node l r π, Hs, σ) h.1 (c2sCap (pmap h.1) U g πj.verts)
        πj.verts H)) πj (delSet (pmap h.1) U g πj.verts) with hffdef
  have eG := c2sG_eqE e' he' (pchCall gid (.node l r π, Hs, σ) h.1) (Klein.msspPlaneK (pmap h.1))
    (frRef _) (negLay gid I (.node l r π, Hs, σ) h.1) (stFlowT gid I (.node l r π, Hs, σ) h.1)
    U g πj H
  have hres : ∀ y, pchCall gid (.node l r π, Hs, σ) h.1 (c2sBeta (pmap h.1) U g πj.verts) ∅
      (ff - g) y = c2sG (pmap h.1) (pchCall gid (.node l r π, Hs, σ) h.1)
        (Klein.msspPlaneK (pmap h.1)) (frRef _) (negLay gid I (.node l r π, Hs, σ) h.1)
        (stFlowT gid I (.node l r π, Hs, σ) h.1) U g πj H y - g y := fun y => by
    rw [eG]; exact (add_sub_cancel_left _ _).symm
  have hffb : ∀ y, -(Z : ℤ) ≤ ff y ∧ ff y ≤ Z := fun y => (hparts y).2.2.2.2.2.1
  have hc2b : ∀ y, -(Z : ℤ) ≤ c2sG (pmap h.1) (pchCall gid (.node l r π, Hs, σ) h.1)
        (Klein.msspPlaneK (pmap h.1)) (frRef _) (negLay gid I (.node l r π, Hs, σ) h.1)
        (stFlowT gid I (.node l r π, Hs, σ) h.1) U g πj H y ∧
      c2sG (pmap h.1) (pchCall gid (.node l r π, Hs, σ) h.1)
        (Klein.msspPlaneK (pmap h.1)) (frRef _) (negLay gid I (.node l r π, Hs, σ) h.1)
        (stFlowT gid I (.node l r π, Hs, σ) h.1) U g πj H y ≤ Z :=
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
  · rw [v₃ i hi, c2s_machNFT gid I (pchCall gid) u S T h e' he']
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
