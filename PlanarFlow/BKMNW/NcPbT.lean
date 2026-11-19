module

public import PlanarFlow.BKMNW.NcTailT
public import PlanarFlow.BKMNW.NcPb
public import PlanarFlow.BKMNW.NfBound
public import PlanarFlow.BKMNW.NrSpec

/-!
# The tail of `c2sP` with the push-back specification `PbPSpec'`

`tailT3_exec` and `c2tP_execT` with `PbPSpec'` (`NcPb.lean`) in place of `PbPSpec`:

* `c2sBeta_le` (`c2sBeta U g C v ≤ #darts · Z` for a pseudoflow `g`, `0 ≤ U ≤ Z`);
* **`tailT3_exec'`** (same statement as `tailT3_exec`, with `β ≤ m Z` and `IsAntisymm g'`);
* **`tailT2_exec'`** (`tailT2_exec` with `FzPSpec'` and `wzz m Z ≤ Wz`);
* **`c2tP_execT'`** (same statement as `c2tP_execT`, with `FzPSpec'` (and `wzz m Z ≤ Wz`), `PbPSpec'`): the two extra facts hold at
  the tail: `g' = fixFrozen … − g` is antisymmetric (both are pseudoflows, `fixFrozen_spec`), and
  `β = c2sBeta ≤ m Z` (`abs_div_le_sum`).
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

/-- The excess `c2sBeta` of a pseudoflow is at most `#darts · Z`. -/
lemma c2sBeta_le {M' : CombMap D V F} {U g : D → ℤ} (hU : ∀ y, 0 ≤ U y) (hUZ : ∀ y, U y ≤ (Z : ℤ))
    (hg : IsPseudo M' U g) (C : Finset V) (v : V) :
    c2sBeta M' U g C v ≤ (Fintype.card D : ℤ) * Z := by
  have hsum : ∑ y, U y ≤ (Fintype.card D : ℤ) * Z := by
    calc ∑ y, U y ≤ ∑ _y : D, (Z : ℤ) := Finset.sum_le_sum fun y _ => hUZ y
      _ = (Fintype.card D : ℤ) * Z := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h0 : 0 ≤ (Fintype.card D : ℤ) * Z := by positivity
  unfold c2sBeta
  split_ifs
  · have := abs_div_le_sum hU hg v
    have := neg_abs_le (M'.div g v)
    linarith
  · exact h0

set_option maxHeartbeats 1600000 in
/-- **The program of `fixFrozen` and `G = FF + 2Z − FL`** (`FzPSpec'`). -/
theorem tailT2_exec' {I : Input} {W : ℕ} {wzz : ℕ → ℕ → ℕ} {fzP : Stmt} {fzT : MCall M → ℕ → ℕ} {fzR : ℕ → ℕ}
    (hfz : FzPSpec' M gid u S T Z I W wzz fzP fzT fzR)
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
        (negLay gid I (.node l r π, Hs, σ) h.1) U f₁ πj Del y ≤ Z) (hwz : wzz m Z ≤ Wz) :
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
    F1b DFb CPb FFb Sb Wz c hL hok hSeg hj hde heb l1 l2 l3 l4 s1 s2 s3 s4 d1 d2 d3 wS oD hwz hz hc
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
/-- **The push-back program and `FL := FL + PB − 2Z`** (`PbPSpec'`). -/
theorem tailT3_exec' {I : Input} {W : ℕ} {pbP : Stmt} {pbT : MCall M → ℕ → ℕ} {pbR : ℕ → ℕ}
    (hpb : PbPSpec' M gid u S T Z I W pbP pbT pbR)
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
    (hβ : ∀ v, 0 ≤ β v ∧ β v ≤ (m : ℤ) * Z) (hanti : (pmap h.1).IsAntisymm g')
    (hg' : ∀ y, -(2 * (Z : ℤ)) ≤ g' y ∧ g' y ≤ 2 * Z)
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
    r08 hβ hanti hg' hres hBT hG
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


set_option maxHeartbeats 4000000 in
/-- **The tail of `c2sP` writes the machine's `c2s`** (`PbPSpec'`). -/
theorem c2tP_execT' {I : Input} {W : ℕ} {wzz : ℕ → ℕ → ℕ}
    {fzP pbP : Stmt} {fzT pbT : MCall M → ℕ → ℕ} {fzR pbR : ℕ → ℕ}
    (hfz : FzPSpec' M gid u S T Z I W wzz fzP fzT fzR) (hpb : PbPSpec' M gid u S T Z I W pbP pbT pbR)
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
    (he' : ∀ v, (pmap h.1).tail (e' v) = v) (hwz : wzz m Z ≤ Wz) :
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
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂, g₂, o₂⟩ := tailT2_exec' hfz h hok hm hj e' he' c₁ e₁.wb_right
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
    (fun y => (hparts y).2.2.2.1) (fun y => (hparts y).2.2.2.2.2.1) hwz
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
  -- the extra facts of `PbPSpec'`
  have hffP : IsPseudo (pmap h.1) U ff :=
    (fixFrozen_spec (e := e') (he := he') hpl hU0 hf₁ hmssp (frRef_spec _)
      (negLay_spec gid I (.node l r π, Hs, σ) h.1) (delSet (pmap h.1) U g πj.verts)).1
  have hanti : (pmap h.1).IsAntisymm (ff - g) := fun y => by
    simp only [Pi.sub_apply]; rw [hffP.antisymm y, hh.pseudo.antisymm y]; ring
  have hcard : Fintype.card (SDart (pdarts M (l.piece ∪ r.piece) Hs)) = m := by
    rw [Fintype.card_coe]; exact hL.card_eq
  have hβ' : ∀ v, 0 ≤ c2sBeta (pmap h.1) U g πj.verts v ∧
      c2sBeta (pmap h.1) U g πj.verts v ≤ (m : ℤ) * Z := fun v =>
    ⟨c2sBeta_nonneg hh.pre v, by
      have := c2sBeta_le hU0 hUZ hh.pseudo πj.verts v; rw [hcard] at this; exact this⟩
  -- part 3
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃, g₃, o₃⟩ := tailT3_exec' hpb h hok hm (j := j)
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
    hβ' hanti hg'b hresb
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
