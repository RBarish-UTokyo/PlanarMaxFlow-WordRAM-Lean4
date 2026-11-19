module

public import PlanarFlow.BKMNW.Nf9bE

/-!
# The final negative-length call of the frozen fix, on the base map

* **`olab_sub`** (pure): if `f'` follows `f` on `[0, m)` either directly or through two points
  `≥ m`, the orbit labels of `f'` and `f` agree on `[0, m)`;
* **`pq_lab`**: the face labels of the pendant prologue (`olab` of the pendant `NX`) on the base
  indices are the face labels `labI M₀ en m` of the base map (the boundary walk of a face of the map
  with pendant edges is that of the base map with the two pendant darts of a vertex inserted);
* **`finAB9_exec`**, **`finP9_exec`**: the final step `finP` (`finAB_execW`, `finP_execW`)
  on an arbitrary map `M` with a numbering `EnumOK M en m`: the arrays `RV` (reverse), `RT`
  (rotation), `CP`, `FL`, `LAB` at any bases (here: the first `m` cells of the pendant `RV`, `CP`,
  `FL`, `LAB` and the base `SG`), the negative-length call `negStep_exec'` with the identifiers
  `nsIds M henum (en 0)`; the flow written is `g + cob χ` for
  `negMach (nsIds M henum (en 0)) M I (u − g) = some χ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace F9b

open Finset Function Equiv Orbit CombMap OrbLab NegSSSP NegSSSP.Frame MfDrv NsStep NcFz SPath
  WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### Orbit labels of a refined walk -/

/-- **Orbit labels of a walk with inserted points.** -/
theorem olab_sub {f f' : ℕ → ℕ} {m : ℕ} (hf : ∀ j < m, f j < m)
    (hstep : ∀ j < m, f' j = f j ∨ (m ≤ f' j ∧ m ≤ f' (f' j) ∧ f' (f' (f' j)) = f j))
    {i : ℕ} (hi : i < m) : olab f' i = olab f i := by
  have hfi : ∀ t, f^[t] i < m := by
    intro t
    induction t with
    | zero => exact hi
    | succ t ih => rw [Function.iterate_succ_apply']; exact hf _ ih
  -- every point of the `f`-orbit is on the `f'`-orbit
  have ha : ∀ t, ∃ s, f'^[s] i = f^[t] i := by
    intro t
    induction t with
    | zero => exact ⟨0, rfl⟩
    | succ t ih =>
      obtain ⟨s, hs⟩ := ih
      rcases hstep _ (hfi t) with h | ⟨-, -, h⟩
      · refine ⟨s + 1, ?_⟩
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hs, h]
      · refine ⟨s + 3, ?_⟩
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply', hs, h]
  -- every point of the `f'`-orbit below `m` is on the `f`-orbit
  have hb : ∀ s, ∃ t, f'^[s] i = f^[t] i ∨
      (m ≤ f'^[s] i ∧ m ≤ f' (f'^[s] i) ∧ f' (f' (f'^[s] i)) = f^[t + 1] i) ∨
      (m ≤ f'^[s] i ∧ f' (f'^[s] i) = f^[t + 1] i) := by
    intro s
    induction s with
    | zero => exact ⟨0, Or.inl rfl⟩
    | succ s ih =>
      obtain ⟨t, h | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩⟩ := ih
      · rcases hstep _ (hfi t) with h' | ⟨g1, g2, g3⟩
        · refine ⟨t + 1, Or.inl ?_⟩
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h, h']
        · refine ⟨t, Or.inr (Or.inl ⟨?_, ?_, ?_⟩)⟩
          · rw [Function.iterate_succ_apply', h]; exact g1
          · rw [Function.iterate_succ_apply', h]; exact g2
          · rw [Function.iterate_succ_apply', h, g3, Function.iterate_succ_apply']
      · refine ⟨t, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
        · rw [Function.iterate_succ_apply']; exact h2
        · rw [Function.iterate_succ_apply']; exact h3
      · refine ⟨t + 1, Or.inl ?_⟩
        rw [Function.iterate_succ_apply']; exact h2
  apply le_antisymm
  · obtain ⟨t, ht⟩ := olab_mem f i
    obtain ⟨s, hs⟩ := ha t
    rw [← ht, ← hs]
    exact olab_min f' i s
  · obtain ⟨s, hs⟩ := olab_mem f' i
    have hl : olab f' i < m := lt_of_le_of_lt (olab_le f' i) hi
    obtain ⟨t, h | ⟨h1, -⟩ | ⟨h1, -⟩⟩ := hb s
    · rw [← hs, h]; exact olab_min f i t
    · rw [hs] at h1; omega
    · rw [hs] at h1; omega

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

section Pend

variable {M₀ : CombMap D V F} {e : V → D} {he : ∀ v, M₀.tail (e v) = v}
variable {en : ℕ → D} {en' : ℕ → D ⊕ (V × Bool)} {m m' Z' d d' : ℕ}
  {cap f₀ : D ⊕ (V × Bool) → ℤ} {segs : List (SPath M₀)} {lo hi Gb j : ℕ} {mem : ℕ → ℕ}

lemma pnext_inl (y : D) : (M₀.pendant e he).next (.inl y) =
    if M₀.next y = e (M₀.head y) then .inr (M₀.head y, true) else .inl (M₀.next y) := rfl

lemma pnext_t (v : V) : (M₀.pendant e he).next (.inr (v, true)) = .inr (v, false) := rfl

lemma pnext_f (v : V) : (M₀.pendant e he).next (.inr (v, false)) = .inl (e v) := rfl

variable (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j mem)
include H

/-- An index whose dart is a pendant dart is not a base index. -/
lemma PCtx.ge_of_inr {i : ℕ} {x : V × Bool} (h : en' i = .inr x) : ¬ i < m := fun hi => by
  rw [H.hen i hi] at h; exact Sum.inl_ne_inr h

/-- **The face labels of the pendant prologue on the base indices.** -/
theorem pq_lab {i : ℕ} (hi : i < m) : olab (nxF d' m' mem) i = labI M₀ en m i := by
  have hmm := H.mm
  refine olab_sub (fun j hj => ixOf_lt H.enum _) (fun j hj => ?_) hi
  have hf := en_phiI H.enum j
  have hfl : phiI M₀ en m j < m := ixOf_lt H.enum _
  have hfl' : ixOf en m (M₀.next (en j)) < m := hfl
  have hf' : en (ixOf en m (M₀.next (en j))) = M₀.next (en j) := hf
  obtain ⟨a1, a2⟩ := H.fr.nx_iter 1 j (by omega)
  simp only [Function.iterate_one] at a1 a2
  rw [H.hen j hj, pnext_inl] at a2
  by_cases hc : M₀.next (en j) = e (M₀.head (en j))
  · rw [if_pos hc] at a2
    right
    have g1 : m ≤ nxF d' m' mem j := not_lt.1 (H.ge_of_inr a2)
    obtain ⟨b1, b2⟩ := H.fr.nx_iter 1 _ a1
    simp only [Function.iterate_one] at b1 b2
    rw [a2, pnext_t] at b2
    have g2 : m ≤ nxF d' m' mem (nxF d' m' mem j) := not_lt.1 (H.ge_of_inr b2)
    obtain ⟨c1, c2⟩ := H.fr.nx_iter 1 _ b1
    simp only [Function.iterate_one] at c1 c2
    rw [b2, pnext_f] at c2
    refine ⟨g1, g2, H.fr.en_inj c1 (by omega) ?_⟩
    rw [c2, H.hen _ hfl', hf', hc]
  · rw [if_neg hc] at a2
    left
    exact H.fr.en_inj a1 (by omega) (by rw [a2, H.hen _ hfl', hf'])

end Pend

/-! ### The final step on an arbitrary map -/

section Fin

variable {M : CombMap D V F} {en : ℕ → D} {m : ℕ}
variable {P : Input} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **Phases A and B of the final step on a map with a numbering.** -/
theorem finAB9_exec (C C₀ : ℕ) (hC : 200000 ≤ C) (henum : EnumOK M en m) (hm : 0 < m)
    (u g : D → ℤ) (hpre : NegPre M (u - g)) (I P' : Input) {W : ℕ}
    (c : Config) (hc : WordsBounded W c)
    {Tb k PDb CWb CRb FWb K Wz RVb RTb CPb FLb Z : ℕ}
    (r69 : c.nreg 9469 = Tb) (r00 : c.nreg 9400 = m) (r36 : c.nreg 9436 = 1)
    (r34 : c.nreg 9434 = CPb) (r35 : c.nreg 9435 = FLb)
    (r21 : c.nreg 9421 = Z) (r10 : c.nreg 9310 = K) (r01 : c.nreg 9401 = k)
    (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = RVb) (r31 : c.nreg 9431 = RTb)
    (r74 : c.nreg 9374 = CWb) (r75 : c.nreg 9375 = CRb) (r76 : c.nreg 9376 = FWb)
    (hRV : ∀ i < m, c.nmem (RVb + i) < m ∧ en (c.nmem (RVb + i)) = M.rev (en i))
    (hRT : ∀ i < m, c.nmem (RTb + i) < m ∧ en (c.nmem (RTb + i)) = M.rot (en i))
    (hCP : ∀ i < m, (c.nmem (CPb + i) : ℤ) = u (en i))
    (hPD : ∀ l < k, c.nmem (PDb + l) < m)
    (hdist : ∀ l < k, ∀ l' < k, c.nmem (PDb + l) ≠ c.nmem (RVb + c.nmem (PDb + l')) ∧
      (c.nmem (PDb + l) = c.nmem (PDb + l') → l = l') ∧
      (c.nmem (RVb + c.nmem (PDb + l)) = c.nmem (RVb + c.nmem (PDb + l')) → l = l'))
    (hFLo : ∀ i < m, (∀ l < k, c.nmem (PDb + l) ≠ i ∧ c.nmem (RVb + c.nmem (PDb + l)) ≠ i) →
      (c.nmem (FLb + i) : ℤ) = Z + g (en i))
    (hCW : ∀ l < k, (c.nmem (CWb + l) : ℤ) = u (en (c.nmem (PDb + l))))
    (hCR : ∀ l < k, (c.nmem (CRb + l) : ℤ) = u (en (c.nmem (RVb + c.nmem (PDb + l)))))
    (hFW : ∀ l < k, (c.nmem (FWb + l) : ℤ) = g (en (c.nmem (PDb + l))) + K)
    (hgr : ∀ l < k, g (en (c.nmem (RVb + c.nmem (PDb + l)))) = - g (en (c.nmem (PDb + l))))
    (hgK : ∀ i < m, |g (en i)| ≤ K) (hℓK : ∀ i < m, |u (en i) - g (en i)| ≤ K)
    (hz : ∀ a ≤ Wz, c.nmem a = 0) (hS : 9 * m + 1 + tsz m ≤ Wz + 1)
    (hWR : Wz < RVb ∧ Wz < RTb)
    (hlo : CPb + m ≤ Tb ∧ FLb + m ≤ Tb ∧ RVb + m ≤ Tb ∧ RTb + m ≤ Tb ∧ PDb + k ≤ Tb ∧
      CWb + k ≤ Tb ∧ CRb + k ≤ Tb ∧ FWb + k ≤ Tb)
    (hWz : rtW m (rtL M (u - g)) m ≤ Wz)
    (hW : Tb + 22 * m + 13 + negT C C₀ m ≤ W)
    (wL : 2 * K + rtL M (u - g) ≤ W) (hw2 : spWs m + 205 ≤ W)
    (hw3 : fxWB m (rtL M (u - g)) ≤ W)
    (hv : ∀ i < m, c.nmem (CPb + i) + Z + K ≤ W)
    (hx : ∀ l < k, c.nmem (CWb + l) + K + K ≤ W)
    (hy : ∀ l < k, c.nmem (CRb + l) + c.nmem (FWb + l) ≤ W) :
    ∃ c' t, Exec P' W (.seq finA finB) c c' t ∧ t ≤ 9 * negT C C₀ m + 486 * m + 21 * k + 8300 ∧
      c'.nreg 9477 = Tb ∧ c'.nreg 9479 = Tb + m ∧ c'.nreg 9480 = Tb + m + m + 1 ∧
      c'.nreg 9481 = Tb + m + m + 1 + (10 * m + 6) ∧
      (∀ r, KeepR r → (r < 9477 ∨ 9498 < r) → c'.nreg r = c.nreg r) ∧
      (∀ i < m, c'.nmem (Tb + i) = (u (en i) - g (en i) + K).toNat) ∧
      Res (nsIds M henum (en 0)) M.dual (rtL M (u - g))
        (repsN M.dual (nsIds M henum (en 0)).gd)
        (negMach (nsIds M henum (en 0)) M I (u - g)) (Tb + m + m + 1 + (10 * m + 6))
        (Tb + m + m + 1 + (10 * m + 6) +
          Frame.fsz (repsN M.dual (nsIds M henum (en 0)).gd).card
          (ck M.dual (repsN M.dual (nsIds M henum (en 0)).gd))) c' ∧
      c'.nmem (Tb + m + m + 1 + 1) = (repsN M.dual (nsIds M henum (en 0)).gd).card ∧
      c'.nmem (Tb + m + m + 1 + 1 + 1) = ck M.dual (repsN M.dual (nsIds M henum (en 0)).gd) ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      (∀ a, Wz < a → a < Tb → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := hlo
  have hcard := card_eq_m henum
  have hf1 : Frame.fsz (repsN M.dual (nsIds M henum (en 0)).gd).card
      (ck M.dual (repsN M.dual (nsIds M henum (en 0)).gd)) ≤ 6 + 10 * m ∧
      Frame.fin (repsN M.dual (nsIds M henum (en 0)).gd).card
      (ck M.dual (repsN M.dual (nsIds M henum (en 0)).gd)) ≤ 4 + 6 * m := by
    have h1 := card_le_n (repsN M.dual (nsIds M henum (en 0)).gd)
    have h2 := ck_le_n M.dual (repsN M.dual (nsIds M henum (en 0)).gd)
    rw [hcard] at h1 h2
    unfold Frame.fsz Frame.fin
    constructor <;> omega
  obtain ⟨hf1, hf2⟩ := hf1
  obtain ⟨c₁, t₁, e₁, ht₁, a77, a79, a80, a81, a82, A1, A2, A3, am, ak, ar, arm, ao⟩ :=
    finA_execW (P := P') c hc (T := Tb) (CWb := CWb) (CRb := CRb) (FWb := FWb) r69 r00 r36 r34 r35
      r21 r10 r01 r02 r30 r74 r75 r76 hPD (fun i hi => (hRV i hi).1) hdist
      ⟨l1, l2, l5, l3, l6, l7, l8⟩ (by omega) hv hx hy
  have hLN := ln_all (nm := c.nmem) (nm' := c₁.nmem) (Ui := fun i => u (en i))
    (gi := fun i => g (en i)) hPD hdist A1 A2 A3 hCP hFLo hCW hCR hFW hgr hgK hℓK
  obtain ⟨c₂, t₂, e₂, ht₂, b00, b01, b02, b03, b04, b05, b06, b22, b24, bk, bm, br, brm, bo⟩ :=
    fnN_exec (P := P') c₁ e₁.wb_right
  have k1 : ∀ r, KeepR r → (r < 9477 ∨ 9498 < r) → c₁.nreg r = c.nreg r := fun r hr h2 =>
    ak r (by omega) (by omega) (by omega)
  have k2 : ∀ r, KeepR r → c₂.nreg r = c₁.nreg r := fun r hr => bk r
    (by unfold KeepR at hr; omega) (by unfold KeepR at hr; omega) (by unfold KeepR at hr; omega)
  have m2 : ∀ a, (a < Tb ∨ Tb + m ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [bm, am a ha]
  obtain ⟨c₃, t₃, e₃, ht₃, cz, cRes, cIn', cK, ck1, ck2, cr, crm, co⟩ :=
    negStep_exec' C C₀ hC henum (en 0) (u - g) hpre I P' c₂ e₂.wb_right
      (RVb := RVb) (RTb := RTb) (LNb := Tb) (K := K) (S := 0) (A := Tb + m + m + 1) (Wz := Wz)
      (Ob := Tb + m + m + 1 + (10 * m + 6)) (p := Tb + m + m + 1 + (10 * m + 6) + (10 * m + 6))
      (by rw [b00, k1 _ (keepR_ge (by norm_num)) (by norm_num), r00])
      (by rw [b01, k1 _ (keepR_ge (by norm_num)) (by norm_num), r30])
      (by rw [b02, k1 _ (keepR_ge (by norm_num)) (by norm_num), r31]) (by rw [b03, a77])
      (by rw [b04, k1 _ (keepR_ge (by norm_num)) (by norm_num), r10]) b05 (by rw [b06, a80])
      (by rw [b22, a81]) (by rw [b24, a82])
      (fun i hi => by
        rw [m2 _ (Or.inl (by omega))]
        obtain ⟨h1, h2⟩ := hRV i hi
        rw [← ixOf_en henum h1, h2]; rfl)
      (fun i hi => by
        rw [m2 _ (Or.inl (by omega))]
        obtain ⟨h1, h2⟩ := hRT i hi
        rw [← ixOf_en henum h1, h2])
      (fun i hi => (congrFun bm (Tb + i)).trans (by rw [hLN i hi]; rfl))
      (fun i hi => hℓK i hi)
      (fun a ha => by rw [bm, am a (Or.inl (by omega))]; exact hz a ha)
      (by omega) hWR.1 hWR.2 (by omega) (by omega) (Or.inl (by omega)) (by omega) (by omega)
      (by omega) (by omega) wL hWz (by omega) (by omega) (by omega) hw2 hw3
  have k3 : ∀ r, KeepR r → c₃.nreg r = c₂.nreg r := fun r hr => by
    by_cases h3 : 3000 ≤ r ∧ r ≤ 3012
    · exact ck1 r h3.1 h3.2
    · unfold KeepR at hr
      exact ck2 r (by unfold ncScr; omega) (by unfold NsScr; omega)
  refine ⟨c₃, _, e₁.seq (e₂.seq e₃), ?_,
    by rw [k3 _ (keepR_ge (by norm_num)), k2 _ (keepR_ge (by norm_num)), a77],
    by rw [k3 _ (keepR_ge (by norm_num)), k2 _ (keepR_ge (by norm_num)), a79],
    by rw [k3 _ (keepR_ge (by norm_num)), k2 _ (keepR_ge (by norm_num)), a80],
    by rw [k3 _ (keepR_ge (by norm_num)), k2 _ (keepR_ge (by norm_num)), a81],
    fun r hr h2 => by rw [k3 r hr, k2 r hr, k1 r hr h2], fun i hi => ?_,
    cRes, ?_, ?_, cz, fun a h1 h2 => ?_, by rw [cr, br, ar], by rw [crm, brm, arm],
    by rw [co, bo, ao]⟩
  · clear * - ht₁ ht₂ ht₃ hf1 hf2
    omega
  · rw [cK _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)), bm]
    exact hLN i hi
  · exact cIn'.rm
  · rw [show Tb + m + m + 1 + 1 + 1 = Tb + m + m + 1 + 2 by omega]; exact cIn'.rk
  · rw [cK _ h1 (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)), bm,
      am a (Or.inl h2)]

set_option maxHeartbeats 4000000 in
/-- **The final step on a map with a numbering**: the flow `g + cob χ` in `FL`. -/
theorem finP9_exec (C C₀ : ℕ) (hC : 200000 ≤ C) (henum : EnumOK M en m) (hm : 0 < m)
    (u g : D → ℤ) (hpre : NegPre M (u - g)) (I P' : Input) {W : ℕ}
    (c : Config) (hc : WordsBounded W c)
    {Tb k PDb CWb CRb FWb K Wz RVb RTb CPb FLb LABb Z : ℕ} {χ : F → ℤ}
    (hχ : negMach (nsIds M henum (en 0)) M I (u - g) = some χ)
    (r69 : c.nreg 9469 = Tb) (r00 : c.nreg 9400 = m) (r36 : c.nreg 9436 = 1)
    (r34 : c.nreg 9434 = CPb) (r35 : c.nreg 9435 = FLb)
    (r21 : c.nreg 9421 = Z) (r10 : c.nreg 9310 = K) (r01 : c.nreg 9401 = k)
    (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = RVb) (r31 : c.nreg 9431 = RTb)
    (r74 : c.nreg 9374 = CWb) (r75 : c.nreg 9375 = CRb) (r76 : c.nreg 9376 = FWb)
    (r05 : c.nreg 9405 = LABb)
    (hRV : ∀ i < m, c.nmem (RVb + i) < m ∧ en (c.nmem (RVb + i)) = M.rev (en i))
    (hRT : ∀ i < m, c.nmem (RTb + i) < m ∧ en (c.nmem (RTb + i)) = M.rot (en i))
    (hCP : ∀ i < m, (c.nmem (CPb + i) : ℤ) = u (en i))
    (hLAB : ∀ i < m, c.nmem (LABb + i) = labI M en m i + 1)
    (hPD : ∀ l < k, c.nmem (PDb + l) < m)
    (hdist : ∀ l < k, ∀ l' < k, c.nmem (PDb + l) ≠ c.nmem (RVb + c.nmem (PDb + l')) ∧
      (c.nmem (PDb + l) = c.nmem (PDb + l') → l = l') ∧
      (c.nmem (RVb + c.nmem (PDb + l)) = c.nmem (RVb + c.nmem (PDb + l')) → l = l'))
    (hFLo : ∀ i < m, (∀ l < k, c.nmem (PDb + l) ≠ i ∧ c.nmem (RVb + c.nmem (PDb + l)) ≠ i) →
      (c.nmem (FLb + i) : ℤ) = Z + g (en i))
    (hCW : ∀ l < k, (c.nmem (CWb + l) : ℤ) = u (en (c.nmem (PDb + l))))
    (hCR : ∀ l < k, (c.nmem (CRb + l) : ℤ) = u (en (c.nmem (RVb + c.nmem (PDb + l)))))
    (hFW : ∀ l < k, (c.nmem (FWb + l) : ℤ) = g (en (c.nmem (PDb + l))) + K)
    (hgr : ∀ l < k, g (en (c.nmem (RVb + c.nmem (PDb + l)))) = - g (en (c.nmem (PDb + l))))
    (hgK : ∀ i < m, |g (en i)| ≤ K) (hℓK : ∀ i < m, |u (en i) - g (en i)| ≤ K)
    (hfin : ∀ i < m, 0 ≤ (Z : ℤ) + (g + M.cob χ) (en i))
    (hz : ∀ a ≤ Wz, c.nmem a = 0) (hS : 9 * m + 1 + tsz m ≤ Wz + 1)
    (hWR : Wz < RVb ∧ Wz < RTb)
    (hlo : RVb + m ≤ CPb ∧ CPb + m ≤ FLb ∧ FLb + m ≤ LABb ∧ LABb + m ≤ Tb ∧ RTb + m ≤ Tb ∧
      PDb + k ≤ Tb ∧ CWb + k ≤ Tb ∧ CRb + k ≤ Tb ∧ FWb + k ≤ Tb)
    (hWz : rtW m (rtL M (u - g)) m ≤ Wz)
    (hW : Tb + 60 * m + 60 + negT C C₀ m ≤ W)
    (wL : 2 * K + rtL M (u - g) ≤ W) (hw2 : spWs m + 205 ≤ W)
    (hw3 : fxWB m (rtL M (u - g)) ≤ W)
    (hv : ∀ i < m, c.nmem (CPb + i) + Z + K + K + 2 * rtL M (u - g) ≤ W)
    (hx : ∀ l < k, c.nmem (CWb + l) + K + K ≤ W)
    (hy : ∀ l < k, c.nmem (CRb + l) + c.nmem (FWb + l) ≤ W) :
    ∃ c' t, Exec P' W finP c c' t ∧ t ≤ finT C C₀ m k ∧
      (∀ i < m, (c'.nmem (FLb + i) : ℤ) = Z + (g + M.cob χ) (en i)) ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      (∀ a, Wz < a → a < Tb → (a < FLb ∨ FLb + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, KeepR r → (r < 9477 ∨ 9498 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := hlo
  set Ob := Tb + m + m + 1 + (10 * m + 6) with hOb
  have hcard := card_eq_m henum
  obtain ⟨c₂, t₂, e₂, ht₂, a77, a79, a80, a81, ak, aLN, aRes, aM, aK, az, am, ar, arm, ao⟩ :=
    finAB9_exec C C₀ hC henum hm u g hpre I P' c hc (Tb := Tb) (k := k) (PDb := PDb)
      (CWb := CWb) (CRb := CRb) (FWb := FWb) (K := K) (Wz := Wz) (RVb := RVb) (RTb := RTb)
      (CPb := CPb) (FLb := FLb) (Z := Z) r69 r00 r36 r34 r35 r21 r10 r01 r02 r30 r31
      r74 r75 r76 hRV hRT hCP hPD hdist hFLo hCW hCR hFW hgr hgK hℓK hz hS hWR
      ⟨by omega, by omega, by omega, l4, l5, l6, l7, l8⟩ hWz (by omega) wL hw2 hw3
      (fun i hi => by have := hv i hi; omega) hx hy
  -- the outcome
  rw [hχ] at aRes
  obtain ⟨-, a0, w, ι, hw2', hw1, hv', hcov⟩ := aRes
  set G := nsIds M henum (en 0) with hG
  set Pr := repsN M.dual G.gd with hPr
  set m' := Pr.card with hm'
  set k' := ck M.dual Pr with hk'
  have hfin' : Frame.fin m' k' = 4 + 5 * k' + m' := rfl
  rw [hfin'] at hw1 hv'
  have k2 : ∀ r, KeepR r → (r < 9477 ∨ 9498 < r) → c₂.nreg r = c.nreg r := ak
  have m2 : ∀ a, Wz < a → a < Tb → c₂.nmem a = c.nmem a := am
  have hk'm : k' ≤ m ∧ m' ≤ m := by
    have h1 := ck_le_n M.dual Pr
    have h2 := card_le_n Pr
    rw [hcard] at h1 h2
    exact ⟨h1, h2⟩
  have hid : ∀ v < w, c₂.nmem (Ob + (4 + 5 * k' + m') + 2 + v) < m := fun v hv => by
    rw [(hv' v hv).2.1]; exact G.gv_lt _
  have hRV2 : ∀ i < m, c₂.nmem (RVb + i) < m := fun i hi => by
    rw [m2 _ (by omega) (by omega)]; exact (hRV i hi).1
  have hLAB2 : ∀ i < m, c₂.nmem (LABb + i) ≤ m := fun i hi => by
    rw [m2 _ (by omega) (by omega), hLAB i hi]; have := labI_lt henum hi; omega
  have hVL : ∀ v < w, c₂.nmem (Ob + (4 + 5 * k' + m') + 2 + m' + m' + v) ≤
      2 * rtL M (u - g) := fun v hv => by
    obtain ⟨-, -, h3, h4⟩ := hv' v hv
    rw [show Ob + (4 + 5 * k' + m') + 2 + m' + m' + v = Ob + (4 + 5 * k' + m') + 2 + 2 * m' + v
      by omega, h3]
    exact Int.toNat_le.2 (by have := (abs_le.1 h4).2; push_cast; omega)
  have h4 : ∀ i < m, c₂.nmem (CPb + i) + Z + K + K + 2 * rtL M (u - g) ≤ W := fun i hi => by
    rw [m2 _ (by omega) (by omega)]; exact hv i hi
  have h5 : 2 * rtL M (u - g) + K ≤ W := by have := hv 0 hm; omega
  obtain ⟨c₃, t₃, e₃, ht₃, cFL, cK, cn, cr, crm, co⟩ :=
    finC_execW (P := P') c₂ e₂.wb_right (T := Tb) (m := m) (A := Tb + m + m + 1) (Ob := Ob)
      (m' := m') (k' := k') (w := w) (CPb := CPb) (RVb := RVb) (LABb := LABb)
      (FLb := FLb) (Z := Z) (K := K) (B := 2 * rtL M (u - g)) a77 a79 a80 a81
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r00])
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r36])
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r34])
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r30])
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r05])
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r35])
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r21])
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r10]) aM aK hw1 hw2' hid hRV2 hLAB2
      ⟨by omega, by omega, l0, l1, l2, l3⟩ (by omega) hVL h4 h5
  refine ⟨c₃, _, e₂.seq e₃, ?_, fun i hi => ?_, fun a ha => ?_, fun a h1 h2 h3 => ?_,
    fun r hr h2 => ?_, by rw [cr, ar], by rw [crm, arm], by rw [co, ao]⟩
  · unfold finT; omega
  · -- the flow array holds `g + cob χ`
    rw [cFL i hi]
    set IDb := Ob + (4 + 5 * k' + m') + 2 with hIDb
    set VLb := Ob + (4 + 5 * k' + m') + 2 + m' + m' with hVLb
    set nm0 := potZ c₂.nmem (Tb + m) m with hnm0
    have n0 : ∀ a, (a < Tb + m ∨ Tb + m + (m + 1) ≤ a) → nm0 a = c₂.nmem a := fun a ha => by
      rw [hnm0]; unfold potZ; split_ifs with h
      · omega
      · rfl
    have hidm : ∀ v < w, nm0 (IDb + v) < m := fun v hv => by
      rw [n0 _ (Or.inr (by omega))]; exact hid v hv
    set nm := potM nm0 IDb VLb (Tb + m) w with hnm
    have rd : ∀ a, a < Tb + m → nm a = c₂.nmem a := fun a ha => by
      rw [hnm, potM_out _ (G := m) hidm (Or.inl ha), n0 a (Or.inl ha)]
    have rd2 : ∀ a, Wz < a → a < Tb → nm a = c.nmem a := fun a h1 h2 => by
      rw [rd a (by omega), m2 a h1 h2]
    -- the potential cells
    have hcons : ∀ v' < w, ∀ v'' < w, nm0 (IDb + v') = nm0 (IDb + v'') →
        nm0 (VLb + v') = nm0 (VLb + v'') := fun v' h1 v'' h2 e => by
      rw [n0 _ (Or.inr (by omega)), n0 _ (Or.inr (by omega)), (hv' v' h1).2.1,
        (hv' v'' h2).2.1] at e
      have := G.gv_inj e
      rw [n0 _ (Or.inr (by omega)), n0 _ (Or.inr (by omega)),
        show VLb + v' = Ob + (4 + 5 * k' + m') + 2 + 2 * m' + v' by omega,
        show VLb + v'' = Ob + (4 + 5 * k' + m') + 2 + 2 * m' + v'' by omega,
        (hv' v' h1).2.2.1, (hv' v'' h2).2.2.1, this]
    have hPOT : ∀ j < m, M.face (en j) ∈ verts M.dual Pr →
        (nm (Tb + m + (labI M en m j + 1)) : ℤ) =
          χ (M.face (en j)) + rtL M (u - g) := fun j hj hmem => by
      obtain ⟨v, hv, hιv⟩ := hcov _ hmem
      have e1 : labI M en m j = G.gv (ι v) := by
        rw [← gv_face henum (en 0) hj, hιv]
      have e2 : nm0 (IDb + v) = G.gv (ι v) := by
        rw [n0 _ (Or.inr (by omega))]; exact (hv' v hv).2.1
      rw [show Tb + m + (labI M en m j + 1) = Tb + m + nm0 (IDb + v) + 1 by
        rw [e1, e2]; omega, hnm, potM_val nm0 hcons hv, n0 _ (Or.inr (by omega)),
        show VLb + v = Ob + (4 + 5 * k' + m') + 2 + 2 * m' + v by omega, (hv' v hv).2.2.1,
        ← hιv, Int.toNat_of_nonneg (by have := (abs_le.1 (hv' v hv).2.2.2).1; omega)]
    -- the reads of `flV`
    have hr := hRV i hi
    set r := c.nmem (RVb + i) with hr'
    have rCP : nm (CPb + i) = c.nmem (CPb + i) := rd2 _ (by omega) (by omega)
    have rRV : nm (RVb + i) = r := rd2 _ (by omega) (by omega)
    have rLr : nm (LABb + r) = labI M en m r + 1 := by
      rw [rd2 _ (by omega) (by omega), hLAB r hr.1]
    have rLi : nm (LABb + i) = labI M en m i + 1 := by
      rw [rd2 _ (by omega) (by omega), hLAB i hi]
    have rLN : nm (Tb + i) = (u (en i) - g (en i) + K).toNat := by
      rw [rd _ (by omega), aLN i hi]
    unfold flV
    rw [rCP, rRV, rLr, rLi, rLN]
    show _ = (Z : ℤ) + (g (en i) + (χ (M.face (M.rev (en i))) - χ (M.face (en i))))
    refine fl_dart (L := rtL M (u - g)) (hCP i hi) rfl (hgK i hi) (hℓK i hi) ?_
      (by have := hfin i hi; exact this)
    by_cases hlp : M.face (en i) = M.face (M.rev (en i))
    · left
      have : labI M en m r = labI M en m i := by
        have e1 := gv_face henum (en 0) hr.1
        have e2 := gv_face henum (en 0) hi
        rw [← e1, ← e2, hr.2, ← hlp]
      exact ⟨by rw [this], by rw [← hlp]⟩
    · right
      obtain ⟨v1, v2⟩ := face_mem_verts M G.gd (y := en i) hlp
      refine ⟨?_, hPOT i hi v1⟩
      have := hPOT r hr.1 (by rw [hr.2]; exact v2)
      rw [hr.2] at this
      exact this
  · rw [cK a (Or.inl (by omega)) (Or.inl (by omega)), az a ha]
  · rw [cK a (Or.inl (by omega)) h3, m2 a h1 h2]
  · unfold KeepR at hr
    rw [cn r (by omega) (by omega), k2 r (by unfold KeepR; omega) h2]

end Fin

end F9b

end BKMNW

end PlanarFlow
