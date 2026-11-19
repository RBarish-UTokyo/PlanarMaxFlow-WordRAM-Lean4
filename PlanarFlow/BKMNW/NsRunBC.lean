module

public import PlanarFlow.BKMNW.NsLink

/-!
# The negSSSP step of a call: stages B and C

From the state after stage A (`nsA_exec`): the grouping `tbProg` (kept darts, least lengths, the
offset `L = rtL`), the numbering `nmProg` (the closure list `fLi` and its inverse), the deletion
flags (`nsM`) and the first returns (`nsD`): **`nsBC_exec`**, within `150 m + 50` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace PlanarFlow

namespace BKMNW

namespace NsStep

open Finset Function Equiv Orbit CombMap NegSSSP NegSSSP.Frame OrbLab WordRAM WordRAM.Machine
  WordRAM.Machine.Stmt WordRAM.Programs

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

variable {P : Input} {W : ℕ}

theorem setM_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (block [.copyN 6230 7500, .copyN 6231 7516, .copyN 6232 7518,
      .copyN 6233 7513]) c c' t ∧ t = 4 ∧ c'.nreg 6230 = c.nreg 7500 ∧
      c'.nreg 6231 = c.nreg 7516 ∧ c'.nreg 6232 = c.nreg 7518 ∧ c'.nreg 6233 = c.nreg 7513 ∧
      (∀ r, (r < 6230 ∨ 6233 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

theorem setD_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (block [.copyN 6240 7500, .copyN 6241 7513, .copyN 6242 7510,
      .copyN 6243 7511]) c c' t ∧ t = 4 ∧ c'.nreg 6240 = c.nreg 7500 ∧
      c'.nreg 6241 = c.nreg 7513 ∧ c'.nreg 6242 = c.nreg 7510 ∧ c'.nreg 6243 = c.nreg 7511 ∧
      (∀ r, (r < 6240 ∨ 6243 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

/-- Stage B: the grouping, in the terms of the call. -/
theorem nsB_exec (h : EnumOK M en m) (d₀ : D) (ℓ : D → ℤ) (c : Config) (hc : WordsBounded W c)
    {RVb LNb K S : ℕ} (r00 : c.nreg 7500 = m) (r01 : c.nreg 7501 = RVb)
    (r03 : c.nreg 7503 = LNb) (r04 : c.nreg 7504 = K) (hL : LayRegs c m K S)
    (hLAB : ∀ i < m, c.nmem (S + 2 * m + i) = labI M en m i + 1)
    (hRV : ∀ i < m, c.nmem (RVb + i) = rvI M en m i)
    (hLN : ∀ i < m, c.nmem (LNb + i) = (ℓ (en i) + K).toNat) (hK : ∀ i < m, |ℓ (en i)| ≤ K)
    (hz : ∀ a, S + 9 * m + 1 ≤ a → a < S + 9 * m + 1 + tsz m → c.nmem a = 0)
    (sR : S + 9 * m + 1 + tsz m ≤ RVb) (sN : S + 9 * m + 1 + tsz m ≤ LNb) (wR : RVb + m ≤ W)
    (wN : LNb + m ≤ W) (wK : 2 * K ≤ W) (wL : rtL M ℓ ≤ W) :
    ∃ c' t, Exec P W tbProg c c' t ∧ t ≤ 81 * m + 14 ∧
      (∀ j < m, c'.nmem (S + 4 * m + j) = kpI M en m h d₀ j) ∧
      (∀ j < m, (c'.nmem (S + 5 * m + j) : ℤ) = minLen M.dual ℓ (en j) + K) ∧
      c'.nreg 7525 = rtL M ℓ ∧
      (∀ a, ¬ (S + 4 * m ≤ a ∧ a < S + 6 * m) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 7522 ∨ 7548 < r) → c'.nreg r = c.nreg r) ∧ c'.nreg 7522 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩ := hL
  have hR : TbRegs c m RVb LNb K (S + 2 * m) (S + 4 * m) (S + 5 * m) (S + 9 * m + 1) (2 * K) :=
    ⟨r00, r01, r03, r04, d2, d4, d5, d9, d10, d11⟩
  have hA : TbArr c.nmem m RVb (S + 2 * m) (S + 9 * m + 1) (labI M en m) (rvI M en m) :=
    ⟨hLAB, hRV, fun j _ => rvI_lt h j, fun j hj => labI_lt h hj, by omega, sR⟩
  have hsum : rtL M ℓ = ∑ j ∈ range m, lterm K (2 * K - (grpP (labI M en m) (rvI M en m)
      (m + 1) m j).sup (vL (fun j => (ℓ (en j) + K).toNat) (2 * K))) := by
    rw [rtL_eq h ℓ K _ (fun i hi => mln_eq h ℓ K hK hi)]
    rfl
  obtain ⟨c', t, ex, ht, k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ :=
    tbProg_exec (P := P) (ln := fun j => (ℓ (en j) + K).toNat) c hc hR hA hLN hz (by omega)
      (by omega) (by omega) sN wR wN (by omega) wK (by rw [← hsum]; exact wL)
  refine ⟨c', t, ex, ht, fun j hj => ?_, fun j hj => ?_, ?_, fun a ha => ?_, k6, k4, k7, k8, k9⟩
  · rw [(k1 j hj).1, kflag_eq_kpI h d₀ hj]
  · rw [(k1 j hj).2]; exact mln_eq h ℓ K hK hj
  · rw [k2, hsum]
  · apply k3 a
    · intro h'; apply ha; clear * - h'; constructor <;> omega
    · intro h'; apply ha; clear * - h'; constructor <;> omega

/-- The deletion flags `DF[j] = 1 - POS[j]` (generic). -/
theorem nsM_exec (c : Config) (hc : WordsBounded W c) {K S : ℕ} (r00 : c.nreg 7500 = m)
    (hL : LayRegs c m K S) (hZ0 : ∀ j < m, c.nmem (S + 8 * m + 1 + j) = 0)
    (w : S + 9 * m + 1 ≤ W) :
    ∃ c' t, Exec P W nsM c c' t ∧ t ≤ 11 * m + 8 ∧
      (∀ j < m, c'.nmem (S + 3 * m + j) = 1 - c.nmem (S + 6 * m + j)) ∧
      (∀ a, (a < S + 3 * m ∨ S + 4 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 6230 ∨ 6238 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have w1 : S + 6 * m + m ≤ W := by omega
  have w2 : S + 8 * m + 1 + m ≤ W := by omega
  have w3 : S + 3 * m + m ≤ W := by omega
  have w4 : m + 1 ≤ W := by omega
  have x1 : ∀ j < m, ¬ (S + 3 * m ≤ S + 6 * m + j ∧ S + 6 * m + j < S + 3 * m + m) :=
    fun j hj => by omega
  have x2 : ∀ j < m, ¬ (S + 3 * m ≤ S + 8 * m + 1 + j ∧ S + 8 * m + 1 + j < S + 3 * m + m) :=
    fun j hj => by omega
  obtain ⟨-, -, -, d3, -, -, d6, -, d8, -, -, -, -⟩ := hL
  unfold nsM
  obtain ⟨c₂, t₂, e₂, ht₂, b0, b1, b2, b3, bR, bm, br, brm, bo⟩ := setM_exec (P := P) c hc
  obtain ⟨c₃, t₃, e₃, ht₃, f1, f2, fR, fr, frm, fo⟩ := lmProg_exec (P := P) c₂ e₂.wb_right
    (m := m) (Xb := S + 6 * m) (Yb := S + 8 * m + 1) (OUTb := S + 3 * m)
    (by rw [b0, r00]) (by rw [b1, d6]) (by rw [b2, d8]) (by rw [b3, d3]) w1 w2 w3 w4 x1 x2
  refine ⟨c₃, t₂ + t₃, .seq e₂ e₃, by clear * - ht₂ ht₃; omega, fun j hj => ?_, fun a ha => ?_, fun r hr => ?_,
    by rw [fr, br], by rw [frm, brm], by rw [fo, bo]⟩
  · rw [f1 j hj, bm, hZ0 j hj, Nat.sub_zero]
  · rw [f2 a (by clear * - ha; omega), bm]
  · rw [fR r (by clear * - hr; omega), bR r (by clear * - hr; omega)]

/-- The first returns (generic). -/
theorem nsD_exec {α : Type*} [Fintype α] [DecidableEq α] (c : Config) (hc : WordsBounded W c)
    {K S : ℕ} (r00 : c.nreg 7500 = m) (hL : LayRegs c m K S) {e : ℕ → α} {G : Perm α}
    {R : Finset α} (he : ∀ i < m, ∀ j < m, e i = e j → i = j)
    (hdel : ∀ j < m, 0 < c.nmem (S + 3 * m + j) → e j ∈ R)
    (hrep : BKMNW.RetRep e m G R c.nmem S (S + m)) (w : S + 9 * m + 1 ≤ W) :
    ∃ c' t, Exec P W nsD c c' t ∧ t ≤ 14 * m + 9 ∧
      BKMNW.RetRep e m G (dset e (fun j => c.nmem (S + 3 * m + j)) R m) c'.nmem S (S + m) ∧
      (∀ a, (a < S ∨ S + 2 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 6240 ∨ 6250 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have w1 : S + 3 * m + m ≤ W := by omega
  have w2 : S + m ≤ W := by omega
  have w3 : S + m + m ≤ W := by omega
  have w4 : m + 1 ≤ W := by omega
  have x1 : ∀ j < m, ∀ k < m, S + 3 * m + j ≠ S + k := fun j hj k hk => by omega
  have x2 : ∀ j < m, ∀ k < m, S + 3 * m + j ≠ S + m + k := fun j hj k hk => by omega
  have x3 : ∀ j < m, ∀ k < m, S + j ≠ S + m + k := fun j hj k hk => by omega
  obtain ⟨d0, d1, -, d3, -, -, -, -, -, -, -, -, -⟩ := hL
  unfold nsD
  obtain ⟨c₄, t₄, e₄, ht₄, g0, g1, g2, g3, gR, gm, gr, grm, go⟩ := setD_exec (P := P) c hc
  obtain ⟨c₅, t₅, e₅, ht₅, k1, k2, kR, kr, krm, ko⟩ := ldProg_exec (P := P) c₄ e₄.wb_right
    (m := m) (DFb := S + 3 * m) (NXb := S) (PRb := S + m)
    (by rw [g0, r00]) (by rw [g1, d3]) (by rw [g2, d0]) (by rw [g3, d1]) w1 w2 w3 w4 x1 x2 x3 he (fun j hj hp => hdel j hj (by rw [gm] at hp; exact hp))
    (by rw [gm]; exact hrep)
  rw [gm] at k1
  refine ⟨c₅, t₄ + t₅, .seq e₄ e₅, by clear * - ht₄ ht₅; omega, k1, fun a ha => ?_, fun r hr => ?_,
    by rw [kr, gr], by rw [krm, grm], by rw [ko, go]⟩
  · rw [k2 a (by clear * - ha; omega) (by clear * - ha; omega), gm]
  · rw [kR r (by clear * - hr; omega), gR r (by clear * - hr; omega)]

/-- Stage C: the closure numbering, the deletion flags, the first returns. -/
theorem nsC_exec (h : EnumOK M en m) (d₀ : D) (c : Config) (hc : WordsBounded W c)
    {RVb K S : ℕ} (r00 : c.nreg 7500 = m) (r01 : c.nreg 7501 = RVb) (hL : LayRegs c m K S)
    (hNX : ∀ i < m, c.nmem (S + i) = phiI M en m i)
    (hPR : ∀ i < m, c.nmem (S + m + i) < m ∧
      en (c.nmem (S + m + i)) = (rotPerm M.dual).symm (en i))
    (hKP : ∀ j < m, c.nmem (S + 4 * m + j) = kpI M en m h d₀ j)
    (hRV : ∀ i < m, c.nmem (RVb + i) = rvI M en m i)
    (hP0 : ∀ j < m, c.nmem (S + 6 * m + j) = 0)
    (hZ0 : ∀ j < m, c.nmem (S + 8 * m + 1 + j) = 0)
    (sR : S + 9 * m + 1 ≤ RVb) (wR : RVb + m ≤ W) :
    ∃ c' t, Exec P W (.seq nmProg (.seq nsM nsD)) c c' t ∧ t ≤ 70 * m + 30 ∧
      LRep (fLi M en m h d₀) c'.nmem (S + 7 * m) (S + 6 * m) m ∧
      c'.nreg 7527 = (cLi M en m h d₀).length ∧ c'.nreg 7526 = (fLi M en m h d₀).length ∧
      (∀ i < m, en i ∈ rcl M.dual (repsN M.dual (nsIds M h d₀).gd) →
        c'.nmem (S + i) < m ∧ en (c'.nmem (S + i)) =
          ret (rotPerm M.dual) (rcl M.dual (repsN M.dual (nsIds M h d₀).gd)) (en i)) ∧
      (∀ a, (a < S ∨ (S + 2 * m ≤ a ∧ a < S + 3 * m) ∨ (S + 4 * m ≤ a ∧ a < S + 6 * m) ∨
        S + 8 * m + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      LayRegs c' m K S ∧ c'.nreg 7525 = c.nreg 7525 ∧
      (∀ r, ¬ NsScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hL₀ := hL
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩ := hL
  have w1 : S + 4 * m + m ≤ S + 6 * m := by omega
  have w2 : S + 6 * m + m ≤ S + 7 * m := by omega
  have w3 : S + 7 * m + m + 1 ≤ RVb := by omega
  have w4 : S + 9 * m + 1 ≤ W := by omega
  -- the numbering
  obtain ⟨c₁, t₁, e₁, ht₁, n27, n26, nL, nF, n22, n25, nR, nr, nrm, no⟩ :=
    nmProg_exec (P := P) (kp := kpI M en m h d₀) (rv := rvI M en m) c hc r00 r01 d4 d6 d7 hKP
      (fun j _ => kpI_le h d₀ j) hRV (fun j _ => rvI_lt h j) (fun j hj => rvI_rvI h hj) hP0
      w1 w2 w3 wR
  rw [fLG_eq h d₀] at n26 nL
  rw [cLG_kpI h d₀] at n27
  have hL₁ : LayRegs c₁ m K S := hL₀.of fun r h1 h2 => by
    by_cases e : r = 7522
    · subst e; rw [n22, d12]
    · exact nR r (by clear * - h1 h2 e; omega)
  have F₁ : ∀ a, (a < S + 6 * m ∨ S + 8 * m + 1 ≤ a) → c₁.nmem a = c.nmem a := fun a ha =>
    nF a (by clear * - ha; omega) (by clear * - ha; omega)
  have r00₁ : c₁.nreg 7500 = m := by rw [nR _ (by decide), r00]
  -- the flags
  obtain ⟨c₃, t₃, e₃, ht₃, f1, f2, fR, fr, frm, fo⟩ := nsM_exec (P := P) c₁ e₁.wb_right r00₁ hL₁
    (fun j hj => by rw [F₁ _ (by clear * - hj; omega)]; exact hZ0 j hj) w4
  have hDF : ∀ j < m, (0 < c₃.nmem (S + 3 * m + j) ↔ j ∉ fLi M en m h d₀) := fun j hj => by
    rw [f1 j hj, nL.2 j hj]
    by_cases hm : j ∈ fLi M en m h d₀
    · rw [iteT hm]; simp only [hm, not_true_eq_false, iff_false]; omega
    · rw [iteF hm]; simp only [hm, not_false_eq_true, iff_true]; omega
  have hL₃ : LayRegs c₃ m K S := hL₁.of fun r h1 h2 => fR r (by clear * - h1 h2; omega)
  -- the first returns
  have hrep := retRep_univ h c₃.nmem S (S + m)
    (fun i hi => by rw [f2 _ (by clear * - hi; omega), F₁ _ (by clear * - hi; omega)]; exact hNX i hi)
    (fun i hi => by rw [f2 _ (by clear * - hi; omega), F₁ _ (by clear * - hi; omega)]; exact hPR i hi)
  obtain ⟨c₅, t₅, e₅, ht₅, k1, k2, kR, kr, krm, ko⟩ := nsD_exec (P := P) c₃ e₃.wb_right
    (by rw [fR _ (by decide), r00₁]) hL₃ (e := en) (fun i hi j hj e => h.inj i hi j hj e)
    (fun _ _ _ => mem_univ _) hrep w4
  rw [dset_rcl h d₀ _ hDF] at k1
  unfold nsM nsD at *
  refine ⟨c₅, t₁ + (t₃ + t₅), .seq e₁ (.seq e₃ e₅), by clear * - ht₁ ht₃ ht₅; omega, ?_, ?_, ?_, fun i hi hr => ?_,
    fun a ha => ?_, ?_, ?_, fun r hr => ?_,
    by rw [kr, fr, nr], by rw [krm, frm, nrm], by rw [ko, fo, no]⟩
  · refine ⟨fun t ht => ?_, fun j hj => ?_⟩
    · have hk : (fLi M en m h d₀).length ≤ m := length_le_of_nodup (fLi_nodup h d₀)
        fun x hx => fLi_lt h d₀ hx
      rw [k2 _ (by clear * - hk ht; omega), f2 _ (by clear * - hk ht; omega)]; exact nL.1 t ht
    · rw [k2 _ (by clear * - hj; omega), f2 _ (by clear * - hj; omega)]; exact nL.2 j hj
  · rw [kR _ (by decide), fR _ (by decide), n27]
  · rw [kR _ (by decide), fR _ (by decide), n26]
  · obtain ⟨a1, -, a3, -⟩ := k1 i hi hr
    exact ⟨a1, a3⟩
  · rw [k2 a (by clear * - ha; omega), f2 a (by clear * - ha; omega),
      F₁ a (by clear * - ha; omega)]
  · exact hL₃.of fun r h1 h2 => kR r (by clear * - h1 h2; omega)
  · rw [kR _ (by decide), fR _ (by decide), n25]
  · obtain ⟨q1, -, -, -, q5, -, -⟩ := nsScr_out hr
    rw [kR r (by clear * - q1; omega), fR r (by clear * - q1; omega),
      nR r (by clear * - q5; omega)]

end NsStep

end BKMNW

end PlanarFlow
