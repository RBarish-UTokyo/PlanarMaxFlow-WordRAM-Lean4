module

public import PlanarFlow.BKMNW.NcT1

/-!
# The tail of `c2sP`, parts 2 and 3: the parameter programs and the last passes

* **`tailT2_exec`**: `fzP ; tgC ; sxL` — the program of `fixFrozen` (`FzPSpec`) writes
  `FF = Z + ff`, then `G = FF + 2Z − FL = 2Z + (ff − g)` (`ff`, `g` bounded by `Z`);
* **`tailT3_exec`**: `pbP ; tgD ; axL` — the push-back program (`PbPSpec`) writes
  `PB = 2Z + pchCall … β ∅ g'`, then `FL := FL + PB − 2Z = Z + g + pchCall … β ∅ g'`.
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

set_option maxHeartbeats 1600000 in
/-- **The program of `fixFrozen` and `G = FF + 2Z − FL`.** -/
theorem tailT2_exec {I : Input} {W : ℕ} {fzP : Stmt} {fzT : MCall M → ℕ → ℕ} {fzR : ℕ → ℕ}
    (hfz : FzPSpec M gid u S T Z I W fzP fzT fzR)
    {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D} (h : SCond M l r π Hs σ)
    (hok : CallOk M S T (.node l r π, Hs, σ)) {d e b m : ℕ} {en : ℕ → D} (hm : 0 < m)
    {j : ℕ} {πj : SPath (pmap h.1)} (hj : (segsP h.1 π.segs h.2)[j]? = some πj)
    {U f₁ g : SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ}
    {Del : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))}
    (e' : SVert σ (pdarts M (l.piece ∪ r.piece) Hs) → SDart (pdarts M (l.piece ∪ r.piece) Hs))
    (he' : ∀ v, (pmap h.1).tail (e' v) = v)
    (c : Config) (hc : WordsBounded W c) (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem)
    (hSeg : SegsAt' M en m π e b c) (hde : d + fsz m ≤ e) (heb : e ≤ b)
    {F1b DFb CPb FFb Gb Sb Wz : ℕ}
    (r04 : c.nreg 3004 = d) (r05 : c.nreg 3005 = e) (r06 : c.nreg 3006 = b + 5)
    (r6800 : c.nreg 6800 = j) (r00 : c.nreg 9800 = F1b) (r01 : c.nreg 9801 = DFb)
    (r02 : c.nreg 9802 = CPb) (r03 : c.nreg 9803 = FFb) (r04' : c.nreg 9804 = Sb)
    (r06' : c.nreg 9806 = Gb) (r16 : c.nreg 9816 = 2 * Z) (r21 : c.nreg 9821 = d + 4 + 6 * m)
    (r96 : c.nreg 9796 = m)
    (l1 : b ≤ F1b) (l2 : b ≤ DFb) (l3 : b ≤ CPb ∨ CPb + m ≤ d + 4 + 6 * m) (l4 : b ≤ FFb)
    (l5 : b ≤ Gb) (s1 : F1b + m ≤ Sb) (s2 : DFb + m ≤ Sb) (s3 : CPb + m ≤ Sb) (s4 : FFb + m ≤ Sb)
    (s5 : Gb + m ≤ Sb) (d1 : F1b + m ≤ FFb ∨ FFb + m ≤ F1b) (d2 : DFb + m ≤ FFb ∨ FFb + m ≤ DFb)
    (d3 : CPb + m ≤ FFb ∨ FFb + m ≤ CPb) (d4 : FFb + m ≤ Gb ∨ Gb + m ≤ FFb)
    (wS : Sb + fzR m ≤ W) (oD : Wz < d) (hz : MemZ Wz c) (wZ : 4 * Z ≤ W)
    (hU : ∀ y, 0 ≤ U y ∧ U y ≤ Z) (hf₁ : IsPseudo (pmap h.1) U f₁)
    (hCP : ∀ i < m, (c.nmem (CPb + i) : ℤ) = U (layEn _ en m hL.en_mem hm i))
    (hF1 : ∀ i < m, (c.nmem (F1b + i) : ℤ) = Z + f₁ (layEn _ en m hL.en_mem hm i))
    (hDF : ∀ i < m, c.nmem (DFb + i) =
      if (pmap h.1).tail (layEn _ en m hL.en_mem hm i) ∈ Del then 1 else 0)
    (hFL : ∀ i < m, (c.nmem (d + 4 + 6 * m + i) : ℤ) = Z + g (layEn _ en m hL.en_mem hm i))
    (hg : ∀ y, -(Z : ℤ) ≤ g y ∧ g y ≤ Z)
    (hff : ∀ y, -(Z : ℤ) ≤ fixFrozen (pmap h.1) e' he' (Klein.msspPlaneK (pmap h.1)) (frRef _)
        (negLay gid I (.node l r π, Hs, σ) h.1) U f₁ πj Del y ∧
      fixFrozen (pmap h.1) e' he' (Klein.msspPlaneK (pmap h.1)) (frRef _)
        (negLay gid I (.node l r π, Hs, σ) h.1) U f₁ πj Del y ≤ Z) :
    ∃ c' t, Exec I W (.seq fzP (.seq tgC sxL)) c c' t ∧
      t ≤ fzT (.node l r π, Hs, σ) j + 4 + (11 * m + 4) ∧
      (∀ i < m, (c'.nmem (Gb + i) : ℤ) = 2 * Z +
        (fixFrozen (pmap h.1) e' he' (Klein.msspPlaneK (pmap h.1)) (frRef _)
          (negLay gid I (.node l r π, Hs, σ) h.1) U f₁ πj Del (layEn _ en m hL.en_mem hm i) -
          g (layEn _ en m hL.en_mem hm i))) ∧
      (∀ a, a < Sb → (a < FFb ∨ FFb + m ≤ a) → (a < Gb ∨ Gb + m ≤ a) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      (∀ r, PKeep r → ¬ (ArScr r ∨ (9792 ≤ r ∧ r ≤ 9795)) → c'.nreg r = c.nreg r) ∧
      c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁', g₁, o₁⟩ := hfz l r π Hs σ h d e b m en hm j πj U f₁ Del e' he'
    F1b DFb CPb FFb Sb Wz c hL hok hSeg hj hde heb l1 l2 l3 l4 s1 s2 s3 s4 d1 d2 d3 wS oD hz hc
    r04 r05 r06 r6800 r00 r01 r02 r03 r04' hU hf₁ hCP hF1 hDF
  have hk : ∀ r, PKeep r → c₁.nreg r = c.nreg r := g₁
  obtain ⟨c₂, k₂, e₂, hk₂, a92, a93, a94, a95, g₂, m₂, rr₂, rm₂, o₂⟩ :=
    tgC_exec (P := I) c₁ e₁.wb_right
  have hFL₁ : ∀ i < m, c₁.nmem (d + 4 + 6 * m + i) = c.nmem (d + 4 + 6 * m + i) := fun i hi =>
    (f₁' _ (by unfold fsz at hde; omega) (Or.inl (by unfold fsz at hde; omega))).1
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃, g₃, rr₃, rm₃, o₃⟩ := sxL_exec (P := I) c₂ e₂.wb_right
    (m := m) (Xb := FFb) (Yb := d + 4 + 6 * m) (Ob := Gb) (K := 2 * Z)
    ⟨by rw [a92, hk _ (by unfold PKeep; omega), r03],
      by rw [a93, hk _ (by unfold PKeep; omega), r21],
      by rw [a94, hk _ (by unfold PKeep; omega), r06'],
      by rw [a95, hk _ (by unfold PKeep; omega), r16],
      by rw [g₂ _ (by omega), hk _ (by unfold PKeep; omega), r96],
      by omega, by unfold fsz at hde; omega, by omega, by omega,
      fun t ht j' hj' => by omega, fun t ht j' hj' => by unfold fsz at hde; omega⟩
    (fun t ht => by
      rw [m₂]
      have := v₁ t ht
      have := hff (layEn _ en m hL.en_mem hm t)
      omega)
  refine ⟨c₃, k₁ + (k₂ + k₃), e₁.seq (e₂.seq e₃), by omega, fun i hi => ?_,
    fun a h1 h2 h3 => ?_, fun r hr1 hr2 => ?_, by rw [o₃, o₂, o₁]⟩
  · rw [v₃ i hi, m₂, hFL₁ i hi]
    have h1 := v₁ i hi
    have h2 := hFL i hi
    have h3 := hff (layEn _ en m hL.en_mem hm i)
    have h4 := hg (layEn _ en m hL.en_mem hm i)
    omega
  · rw [f₃ a h3, m₂, rm₃, rm₂]; exact f₁' a h1 h2
  · rw [g₃ r (fun h => hr2 (Or.inl h)), g₂ r (fun h => hr2 (Or.inr h)), hk r hr1]

set_option maxHeartbeats 1600000 in
/-- **The push-back program and `FL := FL + PB − 2Z`.** -/
theorem tailT3_exec {I : Input} {W : ℕ} {pbP : Stmt} {pbT : MCall M → ℕ → ℕ} {pbR : ℕ → ℕ}
    (hpb : PbPSpec M gid u S T Z I W pbP pbT pbR)
    {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D} (h : SCond M l r π Hs σ)
    (hok : CallOk M S T (.node l r π, Hs, σ)) {d e b m : ℕ} {en : ℕ → D} (hm : 0 < m) {j : ℕ}
    {β : SVert σ (pdarts M (l.piece ∪ r.piece) Hs) → ℤ}
    {g g' : SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ}
    (c : Config) (hc : WordsBounded W c) (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem)
    (hSeg : SegsAt' M en m π e b c) (hde : d + fsz m ≤ e) (heb : e ≤ b)
    {BTb Gb PBb Sb Wz : ℕ}
    (r04 : c.nreg 3004 = d) (r05 : c.nreg 3005 = e) (r06 : c.nreg 3006 = b + 5)
    (r6800 : c.nreg 6800 = j) (r05' : c.nreg 9805 = BTb) (r06' : c.nreg 9806 = Gb)
    (r07 : c.nreg 9807 = PBb) (r08 : c.nreg 9808 = Sb) (r16 : c.nreg 9816 = 2 * Z)
    (r21 : c.nreg 9821 = d + 4 + 6 * m) (r96 : c.nreg 9796 = m)
    (l1 : b ≤ BTb) (l2 : b ≤ Gb) (l3 : b ≤ PBb) (s1 : BTb + m ≤ Sb) (s2 : Gb + m ≤ Sb)
    (s3 : PBb + m ≤ Sb) (d1 : BTb + m ≤ PBb ∨ PBb + m ≤ BTb) (d2 : Gb + m ≤ PBb ∨ PBb + m ≤ Gb)
    (wS : Sb + pbR m ≤ W) (oD : Wz < d) (hz : MemZ Wz c) (wZ : 6 * Z ≤ W)
    (hβ : ∀ v, 0 ≤ β v) (hg' : ∀ y, -(2 * (Z : ℤ)) ≤ g' y ∧ g' y ≤ 2 * Z)
    (hres : ∀ y, -(2 * (Z : ℤ)) ≤ pchCall gid (.node l r π, Hs, σ) h.1 β ∅ g' y ∧
      pchCall gid (.node l r π, Hs, σ) h.1 β ∅ g' y ≤ 2 * Z)
    (hBT : ∀ i < m, (c.nmem (BTb + i) : ℤ) = β ((pmap h.1).tail (layEn _ en m hL.en_mem hm i)))
    (hG : ∀ i < m, (c.nmem (Gb + i) : ℤ) = 2 * Z + g' (layEn _ en m hL.en_mem hm i))
    (hFL : ∀ i < m, (c.nmem (d + 4 + 6 * m + i) : ℤ) = Z + g (layEn _ en m hL.en_mem hm i))
    (hg : ∀ y, -(Z : ℤ) ≤ g y ∧ g y ≤ Z)
    (hsum : ∀ y, -(Z : ℤ) ≤ g y + pchCall gid (.node l r π, Hs, σ) h.1 β ∅ g' y) :
    ∃ c' t, Exec I W (.seq pbP (.seq tgD axL)) c c' t ∧
      t ≤ pbT (.node l r π, Hs, σ) j + 4 + (11 * m + 4) ∧
      (∀ i < m, (c'.nmem (d + 4 + 6 * m + i) : ℤ) = Z + (g (layEn _ en m hL.en_mem hm i) +
        pchCall gid (.node l r π, Hs, σ) h.1 β ∅ g' (layEn _ en m hL.en_mem hm i))) ∧
      (∀ a, a < Sb → (a < PBb ∨ PBb + m ≤ a) →
        (a < d + 4 + 6 * m ∨ d + 4 + 6 * m + m ≤ a) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      (∀ r, PKeep r → ¬ (ArScr r ∨ (9792 ≤ r ∧ r ≤ 9795)) → c'.nreg r = c.nreg r) ∧
      c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁, g₁, o₁⟩ := hpb l r π Hs σ h d e b m en hm j β g' BTb Gb PBb Sb
    Wz c hL hok hSeg hde heb l1 l2 l3 s1 s2 s3 d1 d2 wS oD hz hc r04 r05 r06 r6800 r05' r06' r07
    r08 hβ hg' hres hBT hG
  have hk : ∀ r, PKeep r → c₁.nreg r = c.nreg r := g₁
  obtain ⟨c₂, k₂, e₂, hk₂, a92, a93, a94, a95, g₂, m₂, rr₂, rm₂, o₂⟩ :=
    tgD_exec (P := I) c₁ e₁.wb_right
  have hFL₁ : ∀ i < m, c₁.nmem (d + 4 + 6 * m + i) = c.nmem (d + 4 + 6 * m + i) := fun i hi =>
    (f₁ _ (by unfold fsz at hde; omega) (Or.inl (by unfold fsz at hde; omega))).1
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃, g₃, rr₃, rm₃, o₃⟩ := axL_exec (P := I) c₂ e₂.wb_right
    (m := m) (Xb := d + 4 + 6 * m) (Yb := PBb) (Ob := d + 4 + 6 * m) (K := 2 * Z)
    ⟨by rw [a92, hk _ (by unfold PKeep; omega), r21],
      by rw [a93, hk _ (by unfold PKeep; omega), r07],
      by rw [a94, hk _ (by unfold PKeep; omega), r21],
      by rw [a95, hk _ (by unfold PKeep; omega), r16],
      by rw [g₂ _ (by omega), hk _ (by unfold PKeep; omega), r96],
      by unfold fsz at hde; omega, by omega, by unfold fsz at hde; omega, by omega,
      fun t ht j' hj' => by omega, fun t ht j' hj' => by unfold fsz at hde; omega⟩
    (fun t ht => by
      rw [m₂, hFL₁ t ht]
      have := v₁ t ht
      have := hFL t ht
      have := hres (layEn _ en m hL.en_mem hm t)
      have := hg (layEn _ en m hL.en_mem hm t)
      omega)
  refine ⟨c₃, k₁ + (k₂ + k₃), e₁.seq (e₂.seq e₃), by omega, fun i hi => ?_,
    fun a h1 h2 h3 => ?_, fun r hr1 hr2 => ?_, by rw [o₃, o₂, o₁]⟩
  · rw [v₃ i hi, m₂, hFL₁ i hi]
    have h1 : (c₁.nmem (PBb + i) : ℤ) = 2 * Z +
        pchCall gid (.node l r π, Hs, σ) h.1 β ∅ g'
          (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i) := v₁ i hi
    have h2 : (c.nmem (d + 4 + 6 * m + i) : ℤ) =
        Z + g (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i) := hFL i hi
    have h3 := hres (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i)
    have h4 := hsum (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i)
    show _ = (Z : ℤ) + (g (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i) +
      pchCall gid (.node l r π, Hs, σ) h.1 β ∅ g'
        (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i))
    omega
  · rw [f₃ a h3, m₂, rm₃, rm₂]; exact f₁ a h1 h2
  · rw [g₃ r (fun h => hr2 (Or.inl h)), g₂ r (fun h => hr2 (Or.inr h)), hk r hr1]

end NcStep

end BKMNW

end PlanarFlow
