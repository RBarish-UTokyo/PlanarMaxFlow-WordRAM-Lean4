module

public import PlanarFlow.BKMNW.NcFzL

/-!
# `fzP` meets `FzPSpec'` given a frozen-fix program meeting `FixFrameSpec`

**`fzP_spec`**: `FixFrameSpec fixC msP Scr Rm wzm C C₀ fxT fxR wzf` and the MSSP call program's
specification on every map give, for every map `M` and every `gid u S T Z I W` with `1 ≤ W`,
`FzPSpec' M gid u S T Z I W (fzWz wzf) (fzP fixC) (fzTc fxT) (fzRc fxR Z)` with

* the zero area **`fzWz wzf m Z = Σ_{m' ≤ 3m} wzf m' (m Z)`** (the pendant frame has
  `m' = m + 2n ≤ 3m` darts and offset `m Z`);
* the room **`fzRc fxR Z m = 40 m + 20 + 4 (m Z) + 4 Z + 4 + Σ_{m' ≤ 3m} fxR m' (m Z)`**
  (`pfP`'s scratch `≤ 37 m + 16` above `Sb`, then `fixC`'s room above the pendant frame);
* the steps **`fzTc fxT x j = pfT m + 3 + fxT m #faces(πj) k(πj) + (24 m + 40)`** (`m` the
  darts of the piece, `πj` the part `j`, `partFK`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcFz

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine MfDrv NsStep OrbLab

/-- The zero area of `fzP`. -/
def fzWz (wzf : ℕ → ℕ → ℕ) (m Z : ℕ) : ℕ := ∑ i ∈ range (3 * m + 1), wzf i (m * Z)

/-- The room of `fzP`. -/
def fzRc (fxR : ℕ → ℕ → ℕ) (Z m : ℕ) : ℕ :=
  40 * m + 20 + 4 * (m * Z) + 4 * Z + 4 + ∑ i ∈ range (3 * m + 1), fxR i (m * Z)

section Defs

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

open Classical in
/-- The number of faces along the part `j` of a node call and its number of darts. -/
noncomputable def partFK : MCall M → ℕ → ℕ × ℕ
  | (.node l r π, Hs, σ), j =>
    if h : SCond M l r π Hs σ then
      ((segsP h.1 π.segs h.2)[j]?.map fun πj => (πj.faces.card, πj.k)).getD (0, 0)
    else (0, 0)
  | _, _ => (0, 0)

lemma partFK_node {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    (h : SCond M l r π Hs σ) {j : ℕ} {πj : SPath (pmap h.1)}
    (hπj : (segsP h.1 π.segs h.2)[j]? = some πj) :
    partFK (.node l r π, Hs, σ) j = (πj.faces.card, πj.k) := by
  simp only [partFK, dif_pos h, hπj, Option.map_some, Option.getD_some]

/-- The steps of `fzP`. -/
noncomputable def fzTc (fxT : ℕ → ℕ → ℕ → ℕ) (x : MCall M) (j : ℕ) : ℕ :=
  pfT (pdarts M x.1.piece x.2.1).card + 3 +
    fxT (pdarts M x.1.piece x.2.1).card (partFK x j).1 (partFK x j).2 +
    (24 * (pdarts M x.1.piece x.2.1).card + 40)

end Defs

/-- **The value of the copy-back.** -/
lemma fz_val {q F1 FL mZ Z : ℕ} {g f : ℤ} (inc : Prop) [Decidable inc]
    (hq : q = if inc then 1 else 0) (hF : (F1 : ℤ) = Z + f) (hFL : (FL : ℤ) = mZ + g)
    (hg : -(Z : ℤ) ≤ g) :
    ((q * F1 + (FL + Z - mZ) - q * (FL + Z - mZ) : ℕ) : ℤ) = Z + (if inc then f else g) := by
  split_ifs at hq ⊢ <;> subst hq <;> simp <;> omega

lemma sum_ge {f : ℕ → ℕ} {i N : ℕ} (h : i < N) : f i ≤ ∑ j ∈ range N, f j :=
  single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.2 h)

section Main

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

set_option maxHeartbeats 4000000 in
/-- **`fzP` meets `FzPSpec'`** (see the module docstring). -/
theorem fzP_spec {fixC msP : Stmt} {Scr : ℕ → Prop} {Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    {C C₀ : ℕ} {fxT : ℕ → ℕ → ℕ → ℕ} {fxR wzf : ℕ → ℕ → ℕ}
    (hFF : FixFrameSpec fixC msP Scr Rm wzm C C₀ fxT fxR wzf)
    (hMS : ∀ {D' V' F' : Type} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
      [Fintype F'] [DecidableEq F'] (M' : CombMap D' V' F'),
      MsCall.MsspCallSpec M' msP Scr (MsEnc.msCostS C C₀) Rm wzm)
    (M : CombMap D V F) (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) :
    NcStep.FzPSpec' M gid u S T Z I W (fzWz wzf) (fzP fixC) (fzTc fxT) (fzRc fxR Z) := by
  intro l r π Hs σ h d e b m en hm j πj U f₁ Del e' he' F1b DFb CPb FFb Sb Wz c hL hok hseg hπj
    hde heb hb1 hb2 hb3 hb4 l1 l2 l3 l4 dj1 dj2 dj3 hRm hWzd hwz hz hc r04 r05 r06 r00' ra rb rc
    rd re hU hps hCP hF1 hDF
  obtain ⟨hpl, hrot, hft⟩ := NcStep.lay_plane h.1 hok hL hm
  have hcard := lay_card h.1 hL hm hft
  have w1 : Sb + 40 * m + 20 ≤ W := by unfold fzRc at hRm; omega
  have w2 : 4 * (m * Z) + 4 * Z + 4 ≤ W := by unfold fzRc at hRm; omega
  have hW1 : 1 ≤ W := by omega
  have hI := pfIn_of h hm hL hde heb hb1 l1 l2 l3 w1 w2 r04 ra rb rc re hU hps hCP hF1 hDF
  have hMn := pfMean_of h hm hL hft hU hps hCP hF1 hDF
  set en₀ := layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm with hen₀
  obtain ⟨c₁, k₁, n, e₁, hk₁, hR⟩ := pfP_exec (P := I) c hc hW1 hI
  have hnm := hR.nm
  obtain ⟨e₀, he₀, hMF⟩ := pend_frame hI hR hMn
  obtain ⟨c₂, k₂, e₂, hk₂, g04, g98, g06, g₂, m₂, rr₂, rm₂, o₂⟩ := fxG_exec (P := I) c₁ e₁.wb_right
  -- the parts
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.1 hπj
  have hlow : ∀ a, a < Sb → c₂.nmem a = c.nmem a := fun a ha => by rw [m₂]; exact hR.st.low a ha
  have hL₂ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₂.nmem :=
    hL.congr fun a h1 h2 => hlow a (by unfold fsz at hde; omega)
  have hS₂ : SegsOut' M en m π e b (c.nreg 6807) c₂.nmem :=
    SegsOut'.congr hseg fun a h1 h2 => hlow a (by omega)
  have hSL := segsL_of h hL₂ hm hS₂
  -- the registers of `c₂`
  have q2 : ∀ r, ¬ ExtScr r → r ≠ 3004 → r ≠ 9998 → r ≠ 3006 → c₂.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => by rw [g₂ r h2 h3 h4, hR.st.reg r h1]
  have x04 : c₂.nreg 3004 = Sb + 12 + 16 * m := by rw [g04, hR.st.rg.r71]
  have x98 : c₂.nreg 9998 = d := by rw [g98, hR.st.rg.r50]
  have x06 : c₂.nreg 3006 = Sb + 12 + 16 * m + 4 + 7 * (m + 2 * n) := by rw [g06, hR.st.rg2.r79]
  have x07 : c₂.nreg 6807 = c.nreg 6807 :=
    q2 _ (by unfold ExtScr; omega) (by omega) (by omega) (by omega)
  have x00 : c₂.nreg 6800 = j := by
    rw [q2 _ (by unfold ExtScr; omega) (by omega) (by omega) (by omega), r00']
  -- the room
  have hm' : m + 2 * n ≤ 3 * m := by omega
  have hroom : Sb + 12 + 16 * m + 4 + 7 * (m + 2 * n) + fxR (m + 2 * n) (m * Z) ≤ W := by
    have := sum_ge (f := fun i => fxR i (m * Z)) (show m + 2 * n < 3 * m + 1 by omega)
    unfold fzRc at hRm; omega
  have hwzf : wzf (m + 2 * n) (m * Z) ≤ Wz := by
    have := sum_ge (f := fun i => wzf i (m * Z)) (show m + 2 * n < 3 * m + 1 by omega)
    unfold fzWz at hwz; omega
  -- the frozen-fix program
  have hen : NsStep.EnumOK (pmap h.1) en₀ m := lay_enumOK h.1 hL hm hft
  obtain ⟨c₃, k₃, e₃, hk₃, hFL, hmem3, hz3, hreg3, ho3⟩ := hFF hMS (pmap h.1) hpl hrot hft e₀ he₀
    I W Wz m (m + 2 * n) (m * Z) d (Sb + 12 + 16 * m) (Sb + 12 + 16 * m + 4 + 7 * (m + 2 * n)) e b
    (c.nreg 6807) j en₀ hen (pEn (pmap h.1) en₀ (fun t => c₁.nmem (Sb + 12 + 12 * m + t)) m n)
    (segsP h.1 π.segs h.2) hj (frCap (pmap h.1) U f₁ Del) (frFlow (pmap h.1) f₁ Del) c₂
    (by rw [hlow _ (by unfold fsz at hde; omega)]; exact hL.hm)
    (fun i hi => by
      rw [hlow _ (by unfold fsz at hde; omega)]
      exact ⟨hI.rv i hi, hMn.rv i hi⟩)
    (fun i hi => by
      rw [hlow _ (by unfold fsz at hde; omega)]
      exact ⟨(hL.sg i hi).1, hMn.sg i hi⟩)
    (by rw [m₂]; exact hMF) (fun i hi => pEn_inl hi) (by omega) hm' hm hSL
    (frFlow_pseudo e₀ he₀ hps Del) (frCap_nonneg (fun y => (hU y).1) Del) x04 x98 x06 x07 x00
    (by unfold fsz at hde; omega) (by omega) (by omega) hWzd (by unfold fsz at hde; omega)
    (by unfold fsz at hde; omega) hroom hwzf
    (fun a ha => by rw [hlow a (by unfold fsz at hde; omega)]; exact hz a ha) e₂.wb_right
  rw [hget] at hFL hk₃
  -- the copy-back
  have hS3 : ∀ a, a < Sb + 12 + 16 * m + 4 + 6 * (m + 2 * n) → c₃.nmem a = c₁.nmem a :=
    fun a ha => by rw [(hmem3 a (by omega) (Or.inl ha)).1, m₂]
  have y04 : c₃.nreg 9804 = Sb := by
    rw [hreg3 _ (by unfold NcStep.PKeep; omega), q2 _ (by unfold ExtScr; omega) (by omega) (by omega)
      (by omega), re]
  have y00 : c₃.nreg 9800 = F1b := by
    rw [hreg3 _ (by unfold NcStep.PKeep; omega), q2 _ (by unfold ExtScr; omega) (by omega) (by omega)
      (by omega), ra]
  have y03 : c₃.nreg 9803 = FFb := by
    rw [hreg3 _ (by unfold NcStep.PKeep; omega), q2 _ (by unfold ExtScr; omega) (by omega) (by omega)
      (by omega), rd]
  have hq3 : ∀ t < m, c₃.nmem (Sb + 12 + 13 * m + t) = qF c.nmem DFb (d + 4 + m) t := fun t ht => by
    rw [hS3 _ (by omega)]; exact hR.st.q t ht
  have hFL3 : ∀ t < m, ((c₃.nmem (Sb + 12 + 16 * m + 4 + 6 * (m + 2 * n) + t) : ℕ) : ℤ) =
      (m * Z : ℕ) + fixPath ((pmap h.1).pendant e₀ he₀) (frCap (pmap h.1) U f₁ Del)
        (frFlow (pmap h.1) f₁ Del) (πj.lift e₀ he₀) (msspP (Klein.msspPlaneK (pmap h.1)))
        (frRef _) (negP (negMach (NsStep.nsIds (pmap h.1) hen (en₀ 0)) (pmap h.1) I))
        (.inl (en₀ t)) := fun t ht => by
    have := hFL t (by omega)
    rw [pEn_inl ht] at this
    exact this
  have hb : ∀ t, -(Z : ℤ) ≤ fixPath ((pmap h.1).pendant e₀ he₀) (frCap (pmap h.1) U f₁ Del)
        (frFlow (pmap h.1) f₁ Del) (πj.lift e₀ he₀) (msspP (Klein.msspPlaneK (pmap h.1)))
        (frRef _) (negP (negMach (NsStep.nsIds (pmap h.1) hen (en₀ 0)) (pmap h.1) I))
        (.inl (en₀ t)) ∧
      fixPath ((pmap h.1).pendant e₀ he₀) (frCap (pmap h.1) U f₁ Del)
        (frFlow (pmap h.1) f₁ Del) (πj.lift e₀ he₀) (msspP (Klein.msspPlaneK (pmap h.1)))
        (frRef _) (negP (negMach (NsStep.nsIds (pmap h.1) hen (en₀ 0)) (pmap h.1) I))
        (.inl (en₀ t)) ≤ Z := fun t => pend_bound hpl hrot hft e₀ he₀ hU hps Del πj
    (NsStep.nsIds (pmap h.1) hen (en₀ 0)) I (en₀ t)
  obtain ⟨c₄, k₄, e₄, hk₄, hFF4, hmem4, z04, z06, hreg4, rr₄, rm₄, o₄⟩ := cbP_exec (P := I) c₃
    e₃.wb_right hW1 (S := Sb) (d := d) (A0 := c.nreg 3006) (m := m) (Z := Z)
    (Qb := Sb + 12 + 13 * m) (FLb := Sb + 12 + 16 * m + 4 + 6 * (m + 2 * n)) y04 y00 y03
    (by rw [hS3 _ (by omega)]; exact hR.st.sv0) (by rw [hS3 _ (by omega)]; exact hR.st.sv1)
    (by rw [hS3 _ (by omega)]; exact hR.st.sv2) (by rw [hS3 _ (by omega)]; exact hR.st.sv3)
    (by rw [hS3 _ (by omega)]; exact hR.st.sv4) (by rw [hS3 _ (by omega)]; exact hR.st.sv5)
    (by rw [hS3 _ (by omega)]; exact hR.st.sv6) l1 l4 dj1 (by omega) (by omega) (by omega)
    (by omega) (fun t ht => by rw [hq3 t ht]; exact qF_le_one _ _ _ _)
    (fun t ht => by rw [hS3 _ (by omega), hR.st.low _ (by omega)]; exact hI.f1 t ht)
    (fun t ht => by
      have h1 := hFL3 t ht
      have h2 := (hb t).2
      push_cast at h1
      have : (c₃.nmem (Sb + 12 + 16 * m + 4 + 6 * (m + 2 * n) + t) : ℤ) ≤ m * Z + Z := by
        linarith
      have : c₃.nmem (Sb + 12 + 16 * m + 4 + 6 * (m + 2 * n) + t) ≤ m * Z + Z := by exact_mod_cast this
      omega)
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), e₁.seq (e₂.seq (e₃.seq e₄)), ?_, fun i hi => ?_,
    fun a ha hFFa => ?_, fun r hr => ?_, by rw [o₄, ho3, o₂, hR.st.out]⟩
  · -- the steps
    have hpk := partFK_node h hπj
    unfold fzTc
    simp only [hpk]
    rw [← hcard]
    have := hk₁
    omega
  · -- the value
    rw [hFF4 i hi, hq3 i hi, hS3 _ (by omega), hR.st.low _ (by omega)]
    have E1 := fixFrozen_indep (M := pmap h.1) he' he₀ (Klein.msspPlaneK (pmap h.1)) (frRef _)
      (negLay gid I (.node l r π, Hs, σ) h.1) U f₁ πj Del
    have E2 : negLay gid I (.node l r π, Hs, σ) h.1 =
        negMach (NsStep.nsIds (pmap h.1) hen (en₀ 0)) (pmap h.1) I := negLay_lay I h.1 hL hm hft
    have key : ((Z : ℤ) + if en₀ i ∈ incSet (pmap h.1) Del then f₁ (en₀ i) else
        fixPath ((pmap h.1).pendant e₀ he₀) (frCap (pmap h.1) U f₁ Del) (frFlow (pmap h.1) f₁ Del)
          (πj.lift e₀ he₀) (msspP (Klein.msspPlaneK (pmap h.1))) (frRef _)
          (negP (negMach (NsStep.nsIds (pmap h.1) hen (en₀ 0)) (pmap h.1) I)) (.inl (en₀ i))) =
        (Z : ℤ) + fixFrozen (pmap h.1) e' he' (Klein.msspPlaneK (pmap h.1)) (frRef _)
          (negLay gid I (.node l r π, Hs, σ) h.1) U f₁ πj Del (en₀ i) :=
      (congrArg (fun g => (Z : ℤ) + fixFrozen (pmap h.1) e₀ he₀ (Klein.msspPlaneK (pmap h.1))
        (frRef _) g U f₁ πj Del (en₀ i)) E2.symm).trans
        (congrArg (fun G => (Z : ℤ) + G (en₀ i)) E1.symm)
    refine Eq.trans ?_ key
    exact fz_val _ (hMn.qF_eq hI hi) (hMn.f1 i hi) (by rw [hFL3 i hi]) (hb i).1
  · -- the memory
    have hFFa' : ¬ (FFb ≤ a ∧ a < FFb + m) := by omega
    rw [hmem4 a (by omega)]
    obtain ⟨u1, u2⟩ := hmem3 a (by omega) (Or.inl (by omega))
    refine ⟨by rw [u1, m₂, hR.st.low a ha], ?_⟩
    rw [rm₄, u2]
    show c₂.rmem a = c.rmem a
    rw [rm₂, hR.st.rm]
  · -- the registers
    unfold NcStep.PKeep at hr
    by_cases h34 : r = 3004
    · subst h34; rw [z04, r04]
    by_cases h36 : r = 3006
    · subst h36; rw [z06]
    rw [hreg4 r h34 h36 (by omega), hreg3 r (by unfold NcStep.PKeep; omega),
      q2 r (by unfold ExtScr; omega) h34 (by omega) h36]

end Main

end NcFz

end BKMNW

end PlanarFlow
