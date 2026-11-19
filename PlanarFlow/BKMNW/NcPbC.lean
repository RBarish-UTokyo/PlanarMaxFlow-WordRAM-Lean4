module

public import PlanarFlow.BKMNW.NcPbT
public import PlanarFlow.BKMNW.NcCore

/-!
# The core of `c2sP`/`s2cP` with `PbPSpec'`

**`c2cP_exec'`**: `c2cP_exec` (same statement) with the specifications
`FzPSpec'` (and `wzz m Z ≤ Wz`), `PbPSpec'` (`NcPb.lean`) in place of `FzPSpec`, `PbPSpec`; the
proof is the same, with `c2tP_execT'`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap MfDrv NsStep StCall STFlow OrbLab WordRAM WordRAM.Machine
  WordRAM.Machine.Stmt WordRAM.Programs

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 8000000 in
/-- **The core of `c2sP`/`s2cP` writes the machine's `c2s`.** -/
theorem c2cP_exec' {I : Input} {W : ℕ} {wzz : ℕ → ℕ → ℕ}
    {fzP pbP : Stmt} {fzT pbT : MCall M → ℕ → ℕ} {fzR pbR : ℕ → ℕ}
    (hfz : FzPSpec' M gid u S T Z I W wzz fzP fzT fzR) (hpb : PbPSpec' M gid u S T Z I W pbP pbT pbR)
    {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D} (h : SCond M l r π Hs σ)
    (hok : CallOk M S T (.node l r π, Hs, σ))
    (hinj : ∀ a ∈ pdarts M (l.piece ∪ r.piece) Hs, ∀ b ∈ pdarts M (l.piece ∪ r.piece) Hs,
      gid a = gid b → a = b)
    {d e b m : ℕ} {en : ℕ → D} (hm : 0 < m) {j i : ℕ} {πj : SPath (pmap h.1)}
    (hj : (segsP h.1 π.segs h.2)[j]? = some πj)
    {H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))}
    (hH : (sHoles (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs) (segsP h.1 π.segs h.2) j)[i]? =
      some H)
    {U g : SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ}
    (hh : HoleC2S (pmap h.1) U g πj H) (hU : ∀ y, 0 ≤ U y ∧ U y ≤ Z)
    (c : Config) (hc : WordsBounded W c)
    (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem) (hSeg : SegsAt' M en m π e b c)
    (hde : d + fsz m ≤ e) (heb : e ≤ b) {Wz CPb : ℕ} (hz : MemZ Wz c) (oD : Wz < d)
    (hWz : wzc m Z ≤ Wz)
    (hFL : ∀ i < m, (c.nmem (d + 4 + 6 * m + i) : ℤ) =
      Z + g (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i))
    (hCP : ∀ i < m, (c.nmem (CPb + i) : ℤ) =
      U (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i))
    (hR : HdRegs c d b m Z) (r30 : c.nreg 9830 = CPb) (r04 : c.nreg 3004 = d)
    (r05 : c.nreg 3005 = e) (r06 : c.nreg 3006 = b + 5) (r00 : c.nreg 6800 = j)
    (r02 : c.nreg 6802 = i) (hCPl : CPb + m ≤ b + m)
    (hCPo : b ≤ CPb ∨ CPb + m ≤ d + 4 + 6 * m)
    (wF : b + 28 * m + 10 + stRm m + fzR m ≤ W) (wP : b + 28 * m + 10 + stRm m + pbR m ≤ W)
    (wZ : 6 * Z ≤ W) (wZW : 2 * Z + Wz ≤ W)
    (e' : SVert σ (pdarts M (l.piece ∪ r.piece) Hs) → SDart (pdarts M (l.piece ∪ r.piece) Hs))
    (he' : ∀ v, (pmap h.1).tail (e' v) = v) (hwz : wzz m Z ≤ Wz) :
    ∃ c' t, Exec I W (c2cP fzP pbP) c c' t ∧
      t ≤ hdCost m + (12 + stCostZ m (4 * pcoreB (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))
        (SFace σ (pdarts M (l.piece ∪ r.piece) Hs) (revPerm M)) m (4 * m + 1) + 3) +
        10 + (11 * m + 4) + (fzT (.node l r π, Hs, σ) j + 4 + (11 * m + 4)) +
        (pbT (.node l r π, Hs, σ) j + 4 + (11 * m + 4))) ∧
      (∀ i < m, (c'.nmem (d + 4 + 6 * m + i) : ℤ) =
        Z + (xCtxN M (machNFT gid I (pchCall gid)) u S T l r π Hs σ h).O.c2s
          U g πj H (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i)) ∧
      MemZ Wz c' ∧
      (∀ a, a < b → (a < d + 4 + 6 * m ∨ d + 4 + 6 * m + m ≤ a) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      (∀ r, (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) ∨ (9816 ≤ r ∧ r ≤ 9819) →
        c'.nreg r = c.nreg r) ∧
      c'.output = c.output := by
  classical
  -- facts on the piece map
  obtain ⟨hpl, hrot, hft⟩ := lay_plane h.1 hok hL hm
  have hE := lay_enumOK h.1 hL hm hft
  have hcD : Fintype.card (SDart (pdarts M (l.piece ∪ r.piece) Hs)) = m := StEnc.card_eq hE
  have hcF : Fintype.card (SFace σ (pdarts M (l.piece ∪ r.piece) Hs) (revPerm M)) ≤ m :=
    StEnc.card_F_le hE
  have hcV : Fintype.card (SVert σ (pdarts M (l.piece ∪ r.piece) Hs)) ≤ m := by
    have := Fintype.card_le_of_surjective _ (pmap_tail_surj (x := (.node l r π, Hs, σ)) h.1)
    exact this.trans hcD.le
  have hU0 : ∀ y, 0 ≤ U y := fun y => (hU y).1
  have hUZ : ∀ y, U y ≤ (Z : ℤ) := fun y => (hU y).2
  have hgb := pseudo_bound hh.pseudo hUZ
  have hcap : ∀ y, 0 ≤ c2sCap (pmap h.1) U g πj.verts y ∧
      c2sCap (pmap h.1) U g πj.verts y ≤ 2 * Z := fun y =>
    ⟨c2sCap_nonneg hh.pseudo _ y, c2sCap_le hh.pseudo hU0 hUZ _ y⟩
  have hd : Hs.Pairwise Disjoint := hok.2.2.2.2.2.2
  have hHmem : H ∈ sHoles (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs)
      (segsP h.1 π.segs h.2) j := List.mem_of_getElem? hH
  have hHn := sHoles_nonempty h.1 (segsP h.1 π.segs h.2) j hHmem
  obtain ⟨ib1, ib2, ib3, ib4⟩ := wz_ib (M := pmap h.1) (by omega) hcD hcF hcV hcap πj.verts H hWz
  have hstR : stR (.node l r π, Hs, σ) m ≤ stRm m := stR_le_pR (by omega) hcV hcF
  -- arithmetic
  have hfr : d + 4 + 7 * m ≤ b := by unfold fsz at hde; omega
  have hQ : 2 * Z * m ≤ W := by
    have h1 : 2 * Z * m ≤ wzQ m Z := by
      have := stWc_le_wzQ (M := pmap h.1) (by omega) hcD hcF hcV hcap πj.verts H
      have e2 : 2 * Z * m ≤ wzq m Z * wzq m Z := by unfold wzq; nlinarith
      have e3 : wzq m Z * wzq m Z ≤ wzQ m Z := by
        unfold wzQ
        rw [← pow_two]; exact Nat.pow_le_pow_right (by unfold wzq; omega) (by omega)
      omega
    unfold wzc at hWz; omega
  have w6 : 6 ≤ W := by
    have : 1 ≤ wzQ m Z := Nat.one_le_pow _ _ (by unfold wzq; omega)
    unfold wzc at hWz; omega
  have wW : b + 28 * m + 10 + stRm m ≤ W := by omega
  have wZ2 : 2 * Z ≤ W := by omega
  have hCPZ : ∀ i < m, c.nmem (CPb + i) ≤ Z := fun i hi => by
    have := hCP i hi; have := hUZ (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i)
    omega
  -- stages A–C
  obtain ⟨c₁, k₁, e₁, hk₁, lab₁, dv₁, dg₁, cf₁, mk₁, mem₁, K₁, rr₁, rm₁, o₁⟩ :=
    hd1_exec (P := I) h hrot hm c hc hL hSeg hde heb hj hFL hCP hCPZ (fun y => (hgb y).2) hR r30 r04
      r00 hCPl wW wZ2 hQ w6
  have hR₁ : HdRegs c₁ d b m Z := hR.keep1 K₁
  have memb₁ : ∀ a, a < b + m → c₁.nmem a = c.nmem a := fun a ha => mem₁ a (Or.inl ha)
  have hL₁ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₁.nmem :=
    hL.congr fun a h1 h2 => memb₁ a (by omega)
  -- stage D
  have hIn : ScIn (pmap h.1) (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm) m
      c₁.nmem (b + 5 * m + 1) (b + 14 * m + 5) (d + 4 + m) CPb (d + 4 + 6 * m) (b + m)
      (b + 2 * m) (b + 3 * m) Z U g πj.verts :=
    { cf := fun i hi => cf₁ i hi
      rb := mk₁
      rv := fun i hi => by
        rw [memb₁ _ (by omega), lay_rv h.1 hL hm hft hi]
        exact ⟨rvI_lt hE i, en_rvI hE i⟩
      fl := fun i hi => by rw [memb₁ _ (by omega)]; exact hFL i hi
      cp := fun i hi => by rw [memb₁ _ (by omega)]; exact hCP i hi
      le := fun i hi => hh.pseudo.le_cap _
      dv := fun i hi => ⟨by rw [lab₁ i hi]; omega, dv₁ i hi⟩ }
  obtain ⟨c₂, k₂, e₂, hk₂, cap₂, bt₂, df₂, mem₂, K₂, rr₂, rm₂, o₂⟩ := hdSc_exec (P := I) c₁
    e₁.wb_right hIn (fun i hi => by rw [memb₁ _ (by omega)]; exact hCPZ i hi) dg₁
    (fun i hi => by rw [lab₁ i hi]; have := olab_lt hL.permOn_sg hi; omega)
    hR₁.r32 hR₁.r33 (by rw [K₁ 9830 (by unfold Keep1; omega)]; exact r30) hR₁.r39 hR₁.r41
    hR₁.r74 hR₁.r76 hR₁.r35 hR₁.r36 hR₁.r37 hR₁.r42 hR₁.r43 hR₁.r44 hfr (by omega) (by omega)
    wZ2 (by have : m * Z ≤ 2 * Z * m := by nlinarith
            omega)
  have K₂' : ∀ r, Keep1 r → ¬ (9790 ≤ r ∧ r ≤ 9798) → c₂.nreg r = c₁.nreg r := fun r hr h2 =>
    K₂ r (by unfold Keep1 at hr; omega) (by unfold Keep1 at hr; unfold ScScr; omega) (by omega)
      (by unfold ArScr; omega)
  have hR₂ : HdRegs c₂ d b m Z := hR₁.congr fun r hr =>
    K₂' r (by unfold Keep1; omega) (by omega)
  have memb₂ : ∀ a, (a < b + 16 * m + 9 ∨ b + 19 * m + 9 ≤ a) → c₂.nmem a = c₁.nmem a := mem₂
  -- stage E
  have hL₂ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₂.nmem :=
    hL.congr fun a h1 h2 => by rw [memb₂ a (by omega), memb₁ a (by omega)]
  have hSeg₂ : SegsAt' M en m π e b c₂ := by
    unfold SegsAt' at hSeg ⊢
    rw [K₂' 6807 (by unfold Keep1; omega) (by omega), K₁ 6807 (by unfold Keep1; omega)]
    exact hSeg.congr fun a h1 h2 => by
      rw [memb₂ a (by omega), memb₁ a (by have := hSeg.1.1; omega)]
  have lab₂ : ∀ i < m, c₂.nmem (b + m + i) = olab (sgF d m c₂.nmem) i + 1 := fun i hi => by
    rw [memb₂ _ (by omega), lab₁ i hi]
    rw [olab_congr hL.permOn_sg (g := sgF d m c₂.nmem) (fun t ht => by
      unfold sgF; rw [memb₂ _ (by omega), memb₁ _ (by omega)]) hi]
  obtain ⟨c₃, k₃, e₃, hk₃, hf₃, mem₃, K₃, rr₃, rm₃, o₃⟩ := hdHF_exec (P := I) h hm c₂ e₂.wb_right
    hL₂ hSeg₂ hde heb hd hH (by rw [K₂' 6800 (by unfold Keep1; omega) (by omega),
      K₁ 6800 (by unfold Keep1; omega)]; exact r00)
    (by rw [K₂' 6802 (by unfold Keep1; omega) (by omega),
      K₁ 6802 (by unfold Keep1; omega)]; exact r02)
    hR₂.r32 hR₂.r35 hR₂.r74 hR₂.r77 hR₂.r45 hR₂.r46 hR₂.r47 hR₂.r48 lab₂ (by omega)
  have hR₃ : HdRegs c₃ d b m Z := hR₂.congr fun r hr => K₃ r (by omega)
  -- the tail's registers
  obtain ⟨c₄, k₄, e₄, hk₄, t00, t01, t02, t03, t04, t05, t06, t07, t08, t10, t11, t12, t14, t15,
    f₄, f₄', m₄, rr₄, rm₄, o₄⟩ := tlGl_exec (P := I) c₃ e₃.wb_right
  have k₄r : ∀ r, ¬ (9800 ≤ r ∧ r ≤ 9815) → c₄.nreg r = c₃.nreg r := f₄
  have regs3 : ∀ r, (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) ∨ (9816 ≤ r ∧ r ≤ 9819) →
      c₃.nreg r = c.nreg r := fun r hr => by
    rw [K₃ r (by omega), K₂' r (by unfold Keep1; omega) (by omega), K₁ r (by unfold Keep1; omega)]
  have hR₄ : TailRegs c₄ d e b m j (b + 24 * m + 10 + stRm m) (b + 18 * m + 9) CPb
      (b + 24 * m + 10 + stRm m + m) (b + 24 * m + 10 + stRm m + 4 * m) (b + 17 * m + 9)
      (b + 24 * m + 10 + stRm m + 2 * m) (b + 24 * m + 10 + stRm m + 3 * m)
      (b + 24 * m + 10 + stRm m + 4 * m) (b + 16 * m + 9) (b + 5 * m + 1) (b + 22 * m + 10)
      (wzQ m Z + 339 * m + 128) (b + 23 * m + 10) (b + 24 * m + 10) :=
    { r3004 := by rw [k₄r 3004 (by omega), regs3 3004 (by omega)]; exact r04
      r3005 := by rw [k₄r 3005 (by omega), regs3 3005 (by omega)]; exact r05
      r3006 := by rw [k₄r 3006 (by omega), regs3 3006 (by omega)]; exact r06
      r6800 := by rw [k₄r 6800 (by omega), regs3 6800 (by omega)]; exact r00
      r00 := by rw [t00]; exact hR₃.r51
      r01 := by rw [t01]; exact hR₃.r44
      r02 := by rw [t02, K₃ 9830 (by omega), K₂' 9830 (by unfold Keep1; omega) (by omega),
        K₁ 9830 (by unfold Keep1; omega)]; exact r30
      r03 := by rw [t03]; exact hR₃.r52
      r04 := by rw [t04]; exact hR₃.r55
      r05 := by rw [t05]; exact hR₃.r43
      r06 := by rw [t06]; exact hR₃.r53
      r07 := by rw [t07]; exact hR₃.r54
      r08 := by rw [t08]; exact hR₃.r55
      r10 := by rw [t10]; exact hR₃.r42
      r11 := by rw [t11]; exact hR₃.r39
      r12 := by rw [t12]; exact hR₃.r48
      r13 := by rw [f₄' 9813 rfl]; exact hR₃.r13
      r14 := by rw [t14]; exact hR₃.r49
      r15 := by rw [t15]; exact hR₃.r50 }
  -- the memory at `c₄`
  have mem₄ : ∀ a, (a < b + 19 * m + 9 ∨ b + 23 * m + 10 ≤ a) → c₄.nmem a = c₂.nmem a :=
    fun a ha => by rw [m₄]; exact mem₃ a ha
  have memc₄ : ∀ a, a < b + m → c₄.nmem a = c.nmem a := fun a ha => by
    rw [mem₄ a (by omega), memb₂ a (by omega), memb₁ a ha]
  have hL₄ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₄.nmem :=
    hL.congr fun a h1 h2 => memc₄ a (by omega)
  have hSeg₄ : SegsAt' M en m π e b c₄ := by
    unfold SegsAt' at hSeg ⊢
    rw [k₄r 6807 (by omega), regs3 6807 (by omega)]
    exact hSeg.congr fun a h1 h2 => memc₄ a (by have := hSeg.1.1; omega)
  have hz₄ : MemZ Wz c₄ := fun a ha => by rw [memc₄ a (by omega)]; exact hz a ha
  -- the tail
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, z₅, f₅, g₅, o₅⟩ := c2tP_execT' hfz hpb h hok hinj hm hj hh hU hHn
    c₄ e₄.wb_right hL₄ hSeg₄ hde heb hR₄
    (by rw [k₄r 9816 (by omega)]; exact hR₃.r16) (by rw [k₄r 9818 (by omega)]; exact hR₃.r18)
    (by rw [k₄r 9819 (by omega)]; exact hR₃.r19) hz₄ oD
    (fun i hi => by rw [memc₄ _ (by omega)]; exact hFL i hi)
    (fun i hi => by rw [mem₄ _ (by omega)]; exact cap₂ i hi)
    (fun i hi => by rw [mem₄ _ (by omega), memb₂ _ (by omega)]; exact cf₁ i hi)
    (fun i hi => (congrFun m₄ _).trans (hf₃ i hi))
    (fun i hi => by
      rcases hCPo with ho | ho
      · rw [mem₄ _ (by omega), memb₂ _ (by omega), memb₁ _ (by omega)]; exact hCP i hi
      · rw [memc₄ _ (by omega)]; exact hCP i hi)
    (fun i hi => by rw [mem₄ _ (by omega)]; exact df₂ i hi)
    (fun i hi => by
      rw [mem₄ _ (by omega), bt₂ i hi]
      exact Int.toNat_of_nonneg (c2sBeta_nonneg hh.pre _))
    ib1 ib2 ib3 ib4
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rcases hCPo with ho | ho
        · exact Or.inl ho
        · exact Or.inr ho)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (le_refl _)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) wZW wZ e' he' hwz
  refine ⟨c₅, k₁ + (k₂ + (k₃ + (k₄ + k₅))), e₁.seq (e₂.seq (e₃.seq (e₄.seq e₅))), ?_, v₅, z₅,
    fun a h1 h2 => ?_, fun r hr => ?_, ?_⟩
  · unfold hdCost; omega
  · obtain ⟨x1, x2⟩ := f₅ a h1 h2
    refine ⟨by rw [x1, memc₄ a (by omega)], by rw [x2, rm₄, rm₃, rm₂, rm₁]⟩
  · rw [g₅ r (by omega), k₄r r (by omega), regs3 r hr]
  · rw [o₅, o₄, o₃, o₂, o₁]

end NcStep

end BKMNW

end PlanarFlow
