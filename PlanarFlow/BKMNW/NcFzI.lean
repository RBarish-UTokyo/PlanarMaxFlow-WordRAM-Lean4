module

public import PlanarFlow.BKMNW.NcFzH

/-!
# The meaning of `pfP`: `pend_frame`

**`pend_frame`**: `PfIn`, `PfRes` (the run of `pfP`) and `PfMean` (the meaning of its input for a
map `M₀` numbered by `en₀`) give a choice `e` of a dart at every vertex such that the memory at
`d' = S + 12 + 16 m` is a frame (`MFr`) of `M₀.pendant e he` with `m + 2n` darts, offset `m Z`,
capacities `frCap M₀ U f₁ Del` and flow `frFlow M₀ f₁ Del`, the numbering **`pEn`** (`inl (en₀ i)`
for `i < m`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcFz

open Finset WordRAM WordRAM.Machine OrbLab MfDrv CombMap

variable {D₀ V₀ F₀ : Type*} [Fintype D₀] [DecidableEq D₀] [Fintype V₀] [DecidableEq V₀]
  {M₀ : CombMap D₀ V₀ F₀}

/-- **The numbering of the pendant frame**: `inl (en₀ i)` (`i < m`), `inr (v_t, true)` at
`m + t`, `inr (v_t, false)` at `m + n + t`, `v_t` the vertex of the representative `IX[t]`. -/
def pEn (M₀ : CombMap D₀ V₀ F₀) (en₀ : ℕ → D₀) (ix : ℕ → ℕ) (m n i : ℕ) : D₀ ⊕ (V₀ × Bool) :=
  if i < m then .inl (en₀ i)
  else if i < m + n then .inr (M₀.tail (en₀ (ix (i - m))), true)
  else .inr (M₀.tail (en₀ (ix (i - m - n))), false)

lemma pEn_inl {en₀ : ℕ → D₀} {ix : ℕ → ℕ} {m n i : ℕ} (hi : i < m) :
    pEn M₀ en₀ ix m n i = .inl (en₀ i) := by simp [pEn, hi]

lemma pEn_t {en₀ : ℕ → D₀} {ix : ℕ → ℕ} {m n t : ℕ} (ht : t < n) :
    pEn M₀ en₀ ix m n (m + t) = .inr (M₀.tail (en₀ (ix t)), true) := by
  simp [pEn, show ¬ m + t < m by omega, show m + t < m + n by omega]

lemma pEn_f {en₀ : ℕ → D₀} {ix : ℕ → ℕ} {m n t : ℕ} :
    pEn M₀ en₀ ix m n (m + n + t) = .inr (M₀.tail (en₀ (ix t)), false) := by
  simp only [pEn, show ¬ m + n + t < m by omega, show ¬ m + n + t < m + n by omega, if_false,
    show m + n + t - m - n = t by omega]

lemma pEn_t' {en₀ : ℕ → D₀} {mem : ℕ → ℕ} {B m n t : ℕ} (ht : t < n) :
    pEn M₀ en₀ (fun t => mem (B + t)) m n (m + t) = .inr (M₀.tail (en₀ (mem (B + t))), true) :=
  pEn_t ht

lemma pEn_f' {en₀ : ℕ → D₀} {mem : ℕ → ℕ} {B m n t : ℕ} :
    pEn M₀ en₀ (fun t => mem (B + t)) m n (m + n + t) = .inr (M₀.tail (en₀ (mem (B + t))), false) :=
  pEn_f

lemma cast_add_sub {a K b : ℕ} (h : b ≤ a + K) : ((a + K - b : ℕ) : ℤ) = a + K - b := by omega

lemma cast_sub_max (a b : ℕ) : ((a + 0 - b : ℕ) : ℤ) = max ((a : ℤ) - b) 0 := by
  rcases le_total b a with h | h
  · rw [max_eq_left (by omega)]; omega
  · rw [max_eq_right (by omega)]; omega

section Main

variable {c c' : Config} {W d m Z S F1b DFb CPb n : ℕ} {en₀ : ℕ → D₀} {U f₁ : D₀ → ℤ}
  {Del : Finset V₀}

/-- The representatives: `0 < rfF i` iff `olab i = i`. -/
lemma rfF_pos_iff {sg : ℕ → ℕ} {i : ℕ} : 0 < rfF sg i ↔ olab sg i = i := by
  have := olab_le sg i; unfold rfF; omega

/-- **The vertex of the number `t`.** -/
lemma PfRes.vtx (hI : PfIn c W d m Z S F1b DFb CPb) (hR : PfRes c c' d m Z S F1b DFb CPb n)
    {t : ℕ} (ht : t < n) :
    c'.nmem (S + 12 + 12 * m + t) < m ∧
      olab (sgF d m c.nmem) (c'.nmem (S + 12 + 12 * m + t)) = c'.nmem (S + 12 + 12 * m + t) ∧
      cnt (rfF (sgF d m c.nmem)) (c'.nmem (S + 12 + 12 * m + t)) = t := by
  obtain ⟨i, hi, h1, h2, e⟩ := hR.st.ix ht
  rw [e]; exact ⟨hi, rfF_pos_iff.1 h1, h2⟩

/-- **The number of the vertex of `en₀ i`.** -/
lemma PfRes.num (hI : PfIn c W d m Z S F1b DFb CPb) (hR : PfRes c c' d m Z S F1b DFb CPb n)
    {i : ℕ} (hi : i < m) :
    cnt (rfF (sgF d m c.nmem)) (olab (sgF d m c.nmem) i) < n ∧
      c'.nmem (S + 12 + 12 * m + cnt (rfF (sgF d m c.nmem)) (olab (sgF d m c.nmem) i)) =
        olab (sgF d m c.nmem) i ∧
      c'.nmem (S + 12 + 11 * m + olab (sgF d m c.nmem) i) =
        cnt (rfF (sgF d m c.nmem)) (olab (sgF d m c.nmem) i) := by
  have hp := hI.sgp
  have hl := olab_lt hp hi
  have hf : 0 < rfF (sgF d m c.nmem) (olab (sgF d m c.nmem) i) := by rw [rfF_olab hp hi]; omega
  obtain ⟨u1, u2⟩ := hR.st.ci _ hl hf
  refine ⟨?_, u2, u1⟩
  rw [hR.st.nv]; exact cnt_lt_of _ hl hf

/-- The vertices of the numbers are distinct. -/
lemma PfRes.vtx_inj (hI : PfIn c W d m Z S F1b DFb CPb) (hR : PfRes c c' d m Z S F1b DFb CPb n)
    (hM : PfMean c M₀ en₀ d m Z F1b DFb CPb U f₁ Del) {t t' : ℕ} (ht : t < n) (ht' : t' < n)
    (e : M₀.tail (en₀ (c'.nmem (S + 12 + 12 * m + t))) =
      M₀.tail (en₀ (c'.nmem (S + 12 + 12 * m + t')))) : t = t' := by
  obtain ⟨a1, a2, a3⟩ := hR.vtx hI ht
  obtain ⟨b1, b2, b3⟩ := hR.vtx hI ht'
  have := (hM.vert _ a1 _ b1).1 e
  rw [a2, b2] at this
  rw [← a3, ← b3, this]

/-- **The choice of a dart at every vertex**: the representative of its orbit. -/
lemma PfMean.choice (hI : PfIn c W d m Z S F1b DFb CPb)
    (hM : PfMean c M₀ en₀ d m Z F1b DFb CPb U f₁ Del) :
    ∃ e : V₀ → D₀, (∀ v, M₀.tail (e v) = v) ∧
      ∀ i < m, e (M₀.tail (en₀ i)) = en₀ (olab (sgF d m c.nmem) i) := by
  have hp := hI.sgp
  have ex : ∀ v, ∃ i, i < m ∧ M₀.tail (en₀ i) = v := fun v => by
    obtain ⟨y, hy⟩ := hM.vsurj v
    obtain ⟨i, hi, rfl⟩ := hM.surj y
    exact ⟨i, hi, hy⟩
  choose iv hiv using ex
  refine ⟨fun v => en₀ (olab (sgF d m c.nmem) (iv v)), fun v => ?_, fun i hi => ?_⟩
  · have h1 := (hiv v).1
    rw [(hM.vert _ (olab_lt hp h1) _ h1).2 (olab_olab hp h1), (hiv v).2]
  · have h1 := (hiv (M₀.tail (en₀ i))).1
    have h2 := (hiv (M₀.tail (en₀ i))).2
    show en₀ (olab _ (iv _)) = _
    rw [(hM.vert _ h1 _ hi).1 h2]

/-- The value written by `bSg` at a dart of the map. -/
lemma sgV_eq {s r k m : ℕ} (hs : s < m) :
    sgV (r + 1) s m k = if s = r then k + m else s := by
  unfold sgV
  rw [Nat.add_sub_cancel]
  split_ifs with h
  · subst h; simp; omega
  · rw [show 1 - ((s - r) + (r - s)) = 0 by omega]; simp

set_option maxHeartbeats 800000 in
/-- **The frame of the map with pendant edges** (see the module docstring). -/
theorem pend_frame (hI : PfIn c W d m Z S F1b DFb CPb) (hR : PfRes c c' d m Z S F1b DFb CPb n)
    (hM : PfMean c M₀ en₀ d m Z F1b DFb CPb U f₁ Del) :
    ∃ (e : V₀ → D₀) (he : ∀ v, M₀.tail (e v) = v),
      MFr (M₀.pendant e he) (pEn M₀ en₀ (fun t => c'.nmem (S + 12 + 12 * m + t)) m n)
        (m + 2 * n) (m * Z) (frCap M₀ U f₁ Del) (frFlow M₀ f₁ Del) (S + 12 + 16 * m) c'.nmem := by
  obtain ⟨e, he, hek⟩ := hM.choice hI
  have hp := hI.sgp
  have m0 := hI.m0
  have hnm := hR.nm
  -- the vertex of the number `t` is the vertex of the dart `c'.nmem (S + 12 + 12 * m + t)`
  have vt : ∀ t < n, c'.nmem (S + 12 + 12 * m + t) < m ∧
      olab (sgF d m c.nmem) (c'.nmem (S + 12 + 12 * m + t)) = c'.nmem (S + 12 + 12 * m + t) ∧
      cnt (rfF (sgF d m c.nmem)) (c'.nmem (S + 12 + 12 * m + t)) = t :=
    fun t ht => hR.vtx hI ht
  have hZm : Z ≤ m * Z := Nat.le_mul_of_pos_left Z m0
  refine ⟨e, he, ⟨hR.st.hd0, hR.st.hd3, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- injective
    intro i hi j hj h
    rcases lt_or_ge i m with h1 | h1 <;> rcases lt_or_ge j m with h2 | h2
    · rw [pEn_inl h1, pEn_inl h2] at h; exact hM.inj i h1 j h2 (Sum.inl.inj h)
    · exfalso
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h2
      rw [pEn_inl h1] at h
      by_cases h3 : t < n
      · rw [pEn_t' h3] at h; exact Sum.inl_ne_inr h
      · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h3)
        rw [← Nat.add_assoc, pEn_f'] at h; exact Sum.inl_ne_inr h
    · exfalso
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h1
      rw [pEn_inl h2] at h
      by_cases h3 : t < n
      · rw [pEn_t' h3] at h; exact Sum.inr_ne_inl h
      · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h3)
        rw [← Nat.add_assoc, pEn_f'] at h; exact Sum.inr_ne_inl h
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h1
      obtain ⟨t', rfl⟩ := Nat.exists_eq_add_of_le h2
      skip
      by_cases h3 : t < n <;> by_cases h4 : t' < n
      · rw [pEn_t' h3, pEn_t' h4] at h
        have := hR.vtx_inj hI hM h3 h4 (Prod.mk.inj (Sum.inr.inj h)).1
        omega
      · obtain ⟨u', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h4)
        rw [pEn_t' h3, ← Nat.add_assoc, pEn_f'] at h
        simp at h
      · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h3)
        rw [pEn_t' h4, ← Nat.add_assoc, pEn_f'] at h
        simp at h
      · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h3)
        obtain ⟨u', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h4)
        rw [← Nat.add_assoc, pEn_f', ← Nat.add_assoc, pEn_f'] at h
        have := hR.vtx_inj hI hM (by omega) (by omega) (Prod.mk.inj (Sum.inr.inj h)).1
        omega
  · -- surjective
    rintro (y | ⟨v, b⟩)
    · obtain ⟨i, hi, rfl⟩ := hM.surj y
      exact ⟨i, by omega, by rw [pEn_inl hi]⟩
    · obtain ⟨y, hy⟩ := hM.vsurj v
      obtain ⟨i, hi, rfl⟩ := hM.surj y
      obtain ⟨n1, n2, -⟩ := hR.num hI hi
      have hv : M₀.tail (en₀ (c'.nmem (S + 12 + 12 * m + cnt (rfF (sgF d m c.nmem)) (olab (sgF d m c.nmem) i)))) = v := by
        rw [n2, ← hy]
        exact (hM.vert _ (olab_lt hp hi) _ hi).2 (olab_olab hp hi)
      cases b
      · exact ⟨m + n + cnt (rfF (sgF d m c.nmem)) (olab (sgF d m c.nmem) i), by omega, by rw [pEn_f', hv]⟩
      · exact ⟨m + cnt (rfF (sgF d m c.nmem)) (olab (sgF d m c.nmem) i), by omega, by rw [pEn_t' n1, hv]⟩
  · -- reverse
    intro i hi
    rcases lt_or_ge i m with h1 | h1
    · rw [hR.rv0 i h1]
      have := hI.rv i h1
      refine ⟨by omega, ?_⟩
      rw [pEn_inl this, pEn_inl h1, hM.rv i h1]; rfl
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h1
      by_cases h3 : t < n
      · rw [← Nat.add_assoc, hR.rv1 t h3]
        refine ⟨by omega, ?_⟩
        rw [show t + (m + n) = m + n + t by omega, pEn_f', pEn_t' h3]; rfl
      · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h3)
        rw [show S + 12 + 16 * m + 4 + (m + 2 * n) + (m + (n + u)) =
          S + 12 + 16 * m + 4 + (m + 2 * n) + (m + n) + u by omega, hR.rv2 u (by omega)]
        refine ⟨by omega, ?_⟩
        rw [show u + m = m + u by omega, pEn_t' (by omega), ← Nat.add_assoc, pEn_f']; rfl
  · -- rotation
    intro i hi
    rcases lt_or_ge i m with h1 | h1
    · obtain ⟨n1, n2, n3⟩ := hR.num hI h1
      have hs := hI.sg i h1
      rw [hR.sg0 i h1, hR.st.lab i h1, Nat.add_sub_cancel, n3]
      rw [sgV_eq hs]
      have hnx : M₀.next (M₀.rev (en₀ i)) = en₀ (sgF d m c.nmem i) := by
        rw [← hM.sg i h1]
      have hhd : M₀.head (M₀.rev (en₀ i)) = M₀.tail (en₀ i) := by
        unfold CombMap.head; rw [M₀.rev_rev]
      have hsg' : c.nmem (d + 4 + m + m + i) = sgF d m c.nmem i := by
        unfold sgF; congr 1; omega
      rw [hsg']
      split_ifs with h
      · refine ⟨by omega, ?_⟩
        rw [show cnt (rfF (sgF d m c.nmem)) (olab (sgF d m c.nmem) i) + m = m + cnt (rfF (sgF d m c.nmem)) (olab (sgF d m c.nmem) i) by omega,
          pEn_t' n1, pEn_inl h1]
        show _ = pNext M₀ e (M₀.pendant e he |>.rev (.inl (en₀ i)))
        simp only [pendant_rev_inl, pNext, hnx, hhd, hek i h1, h, ite_true]
        rw [n2, (hM.vert _ (olab_lt hp h1) _ h1).2 (olab_olab hp h1)]
      · have hs' : sgF d m c.nmem i < m := by rw [← hsg']; exact hs
        refine ⟨by omega, ?_⟩
        rw [pEn_inl hs', pEn_inl h1]
        show _ = pNext M₀ e (M₀.pendant e he |>.rev (.inl (en₀ i)))
        have hne : en₀ (sgF d m c.nmem i) ≠ en₀ (olab (sgF d m c.nmem) i) := fun e' =>
          h (hM.inj _ hs' _ (olab_lt hp h1) e')
        simp only [pendant_rev_inl, pNext, hnx, hhd, hek i h1, hne, ite_false]
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h1
      by_cases h3 : t < n
      · obtain ⟨v1, v2, v3⟩ := vt t h3
        rw [show S + 12 + 16 * m + 4 + 2 * (m + 2 * n) + (m + t) =
          S + 12 + 16 * m + 4 + 2 * (m + 2 * n) + m + t by omega, hR.sg1 t h3]
        refine ⟨by omega, ?_⟩
        rw [pEn_t' h3, pEn_inl v1]
        show _ = pNext M₀ e (M₀.pendant e he |>.rev (.inr (_, true)))
        simp only [pendant_rev_inr, Bool.not_true, pNext]
        rw [hek _ v1, v2]
      · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h3)
        rw [show S + 12 + 16 * m + 4 + 2 * (m + 2 * n) + (m + (n + u)) =
          S + 12 + 16 * m + 4 + 2 * (m + 2 * n) + (m + n) + u by omega, hR.sg2 u (by omega)]
        refine ⟨by omega, ?_⟩
        rw [show u + (m + n) = m + n + u by omega, ← Nat.add_assoc, pEn_f']
        show _ = pNext M₀ e (M₀.pendant e he |>.rev (.inr (_, false)))
        simp only [pendant_rev_inr, Bool.not_false, pNext]
  · -- capacities
    intro i hi
    rcases lt_or_ge i m with h1 | h1
    · rw [hR.cp0 i h1, hR.st.q i h1, hM.qF_eq hI h1, pEn_inl h1]
      have hc := hM.cp i h1
      have hcz := hI.cp i h1
      simp only [frCap]
      split_ifs with h
      · simp
      · simp only [Nat.mul_zero, Nat.sub_zero]; exact ⟨hc, by omega⟩
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h1
      by_cases h3 : t < n
      · obtain ⟨v1, v2, v3⟩ := vt t h3
        have hfo := hM.frozen_eq hI v1
        have hab := abs_le.1 (hM.frozen_abs (M₀.tail (en₀ (c'.nmem (S + 12 + 12 * m + t)))))
        rw [v2, ← hR.st.dv _ v1, ← hR.st.dg _ v1] at hfo
        rw [show S + 12 + 16 * m + 4 + 3 * (m + 2 * n) + (m + t) =
          S + 12 + 16 * m + 4 + 3 * (m + 2 * n) + m + t by omega, hR.cp1 t h3, hR.dvr t h3,
          hR.zg t h3, pEn_t' h3]
        simp only [frCap]
        rw [cast_sub_max, Nat.cast_mul, mul_comm (_ : ℤ) (Z : ℤ), hfo]
        refine ⟨rfl, ?_⟩
        have : ((c'.nmem (S + 12 + 8 * m + c'.nmem (S + 12 + 12 * m + t)) + 0 - c'.nmem (S + 12 + 9 * m + c'.nmem (S + 12 + 12 * m + t)) * Z : ℕ) : ℤ)
            ≤ m * Z := by
          rw [cast_sub_max, Nat.cast_mul, mul_comm (_ : ℤ) (Z : ℤ), hfo]
          exact max_le hab.2 (by positivity)
        exact_mod_cast this
      · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h3)
        have hu : u < n := by omega
        obtain ⟨v1, v2, v3⟩ := vt u hu
        have hfo := hM.frozen_eq hI v1
        have hab := abs_le.1 (hM.frozen_abs (M₀.tail (en₀ (c'.nmem (S + 12 + 12 * m + u)))))
        rw [v2, ← hR.st.dv _ v1, ← hR.st.dg _ v1] at hfo
        rw [show S + 12 + 16 * m + 4 + 3 * (m + 2 * n) + (m + (n + u)) =
          S + 12 + 16 * m + 4 + 3 * (m + 2 * n) + (m + n) + u by omega, hR.cp2 u hu, hR.dvr u hu,
          hR.zg u hu, ← Nat.add_assoc, pEn_f']
        simp only [frCap]
        have key : ((c'.nmem (S + 12 + 9 * m + c'.nmem (S + 12 + 12 * m + u)) * Z + 0 - c'.nmem (S + 12 + 8 * m + c'.nmem (S + 12 + 12 * m + u)) : ℕ)
            : ℤ) = max (-frozenOut M₀ f₁ Del (M₀.tail (en₀ (c'.nmem (S + 12 + 12 * m + u))))) 0 := by
          rw [cast_sub_max, Nat.cast_mul, ← hfo]; ring_nf
        refine ⟨key, ?_⟩
        have : ((c'.nmem (S + 12 + 9 * m + c'.nmem (S + 12 + 12 * m + u)) * Z + 0 - c'.nmem (S + 12 + 8 * m + c'.nmem (S + 12 + 12 * m + u)) : ℕ)
            : ℤ) ≤ m * Z := by
          rw [key]; exact max_le (by linarith) (by positivity)
        exact_mod_cast this
  · -- flow
    intro i hi
    rcases lt_or_ge i m with h1 | h1
    · have hx := hM.x0F_eq hI h1
      have hf := hM.f1 i h1
      have hfb := hM.fb (en₀ i)
      rw [hR.fl0 i h1, hR.st.x0 i h1, pEn_inl h1]
      simp only [frFlow]
      have hle : x0F c.nmem F1b DFb (d + 4 + m) Z i ≤ c.nmem (F1b + i) + m * Z := by
        have : ((x0F c.nmem F1b DFb (d + 4 + m) Z i : ℕ) : ℤ) ≤ c.nmem (F1b + i) + m * Z := by
          split_ifs at hx <;> push_cast <;> nlinarith
        exact_mod_cast this
      rw [cast_add_sub hle]
      push_cast
      split_ifs at hx ⊢ <;> linarith
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h1
      by_cases h3 : t < n
      · obtain ⟨v1, v2, v3⟩ := vt t h3
        have hfo := hM.frozen_eq hI v1
        have hab := abs_le.1 (hM.frozen_abs (M₀.tail (en₀ (c'.nmem (S + 12 + 12 * m + t)))))
        rw [v2, ← hR.st.dv _ v1, ← hR.st.dg _ v1] at hfo
        rw [show S + 12 + 16 * m + 4 + 6 * (m + 2 * n) + (m + t) =
          S + 12 + 16 * m + 4 + 6 * (m + 2 * n) + m + t by omega, hR.fl1 t h3, hR.dvr t h3,
          hR.zg t h3, pEn_t' h3]
        simp only [frFlow]
        have hle : c'.nmem (S + 12 + 9 * m + c'.nmem (S + 12 + 12 * m + t)) * Z ≤
            c'.nmem (S + 12 + 8 * m + c'.nmem (S + 12 + 12 * m + t)) + m * Z := by
          have : ((c'.nmem (S + 12 + 9 * m + c'.nmem (S + 12 + 12 * m + t)) * Z : ℕ) : ℤ) ≤
              c'.nmem (S + 12 + 8 * m + c'.nmem (S + 12 + 12 * m + t)) + m * Z := by
            push_cast; rw [mul_comm (_ : ℤ) (Z : ℤ)]; linarith
          exact_mod_cast this
        rw [cast_add_sub hle]
        push_cast; rw [mul_comm (_ : ℤ) (Z : ℤ)]; linarith
      · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h3)
        have hu : u < n := by omega
        obtain ⟨v1, v2, v3⟩ := vt u hu
        have hfo := hM.frozen_eq hI v1
        have hab := abs_le.1 (hM.frozen_abs (M₀.tail (en₀ (c'.nmem (S + 12 + 12 * m + u)))))
        rw [v2, ← hR.st.dv _ v1, ← hR.st.dg _ v1] at hfo
        rw [show S + 12 + 16 * m + 4 + 6 * (m + 2 * n) + (m + (n + u)) =
          S + 12 + 16 * m + 4 + 6 * (m + 2 * n) + (m + n) + u by omega, hR.fl2 u hu, hR.dvr u hu,
          hR.zg u hu, ← Nat.add_assoc, pEn_f']
        simp only [frFlow]
        have hle : c'.nmem (S + 12 + 8 * m + c'.nmem (S + 12 + 12 * m + u)) ≤
            c'.nmem (S + 12 + 9 * m + c'.nmem (S + 12 + 12 * m + u)) * Z + m * Z := by
          have : ((c'.nmem (S + 12 + 8 * m + c'.nmem (S + 12 + 12 * m + u)) : ℕ) : ℤ) ≤
              (c'.nmem (S + 12 + 9 * m + c'.nmem (S + 12 + 12 * m + u)) * Z : ℕ) + m * Z := by
            push_cast; rw [mul_comm (_ : ℤ) (Z : ℤ)]; linarith
          exact_mod_cast this
        rw [cast_add_sub hle]
        push_cast; rw [mul_comm (_ : ℤ) (Z : ℤ)]; linarith

end Main

end NcFz

end BKMNW

end PlanarFlow
