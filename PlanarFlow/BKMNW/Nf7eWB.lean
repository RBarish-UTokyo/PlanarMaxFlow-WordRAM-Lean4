module

public import PlanarFlow.BKMNW.Nf7aP3

/-!
# Per-address word bounds for the prologue, part 2

Copies of `fsaBody_exec`, `fsaProg_exec`, `fsbBody_exec`, `fsbProg_exec`, `fscBody_exec`,
`fscProg_exec`, `proP3b_exec`, `proP3c_exec` (suffix `W`) whose word-bound hypotheses bound each
address separately (or the top address, given the layout hypotheses) instead of a sum of
addresses. The programs and conclusions are unchanged.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1600000 in
theorem fsaBody_execW (c : Config) (hc : WordsBounded W c)
    {m K Z PDb RVb CPb FLWb DVA CWb CRb FWb F0b DVb l : ℕ}
    (r00 : c.nreg 9400 = m) (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = RVb)
    (r34 : c.nreg 9434 = CPb) (r35 : c.nreg 9435 = FLWb) (r08 : c.nreg 9408 = DVA)
    (r10 : c.nreg 9310 = K) (r21 : c.nreg 9421 = Z) (r36 : c.nreg 9436 = 1)
    (r74 : c.nreg 9374 = CWb) (r75 : c.nreg 9375 = CRb) (r76 : c.nreg 9376 = FWb)
    (r12 : c.nreg 9412 = F0b) (r13 : c.nreg 9413 = DVb) (r61 : c.nreg 9461 = l)
    (ht : c.nmem (PDb + l) < m) (hr : c.nmem (RVb + c.nmem (PDb + l)) < m)
    (hv : c.nmem (DVA + c.nmem (PDb + l)) - 1 < m)
    (hb : PDb + l ≤ W ∧ RVb + m ≤ W ∧ CPb + m ≤ W ∧ FLWb + m ≤ W ∧ DVA + 3 * m ≤ W)
    (hfl : c.nmem (FLWb + c.nmem (PDb + l)) + K ≤ W)
    (hdv : c.nmem (DVA + m + (c.nmem (DVA + c.nmem (PDb + l)) - 1)) + K ≤ W)
    (hdg : c.nmem (DVA + m + m + (c.nmem (DVA + c.nmem (PDb + l)) - 1)) * Z ≤ W)
    (ho : CWb + l ≤ W ∧ CRb + l ≤ W ∧ FWb + l ≤ W ∧ F0b + l ≤ W ∧ DVb + l + 1 ≤ W) :
    ∃ c' k, Exec P W fsaBody c c' k ∧ k = 36 ∧ c'.nreg 9461 = l + 1 ∧
      c'.nmem = upd (upd (upd (upd (upd c.nmem (CWb + l) (c.nmem (CPb + c.nmem (PDb + l))))
        (CRb + l) (c.nmem (CPb + c.nmem (RVb + c.nmem (PDb + l)))))
        (FWb + l) (fsaFW c.nmem PDb FLWb K Z l)) (F0b + l) (fsaFW c.nmem PDb FLWb K Z l))
        (DVb + l) (fsaDV c.nmem PDb DVA m K Z l) ∧
      (∀ r, (r < 9461 ∨ 9470 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  obtain ⟨ho1, ho2, ho3, ho4, ho5⟩ := ho
  unfold fsaBody
  exec_block
  all_goals try ((try config_simp) <;>
    (try simp only [r00, r02, r30, r34, r35, r08, r10, r21, r36, r74, r75, r76, r12, r13, r61]) <;>
    omega)
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try
    (simp only [r00, r02, r30, r34, r35, r08, r10, r21, r36, r74, r75, r76, r12, r13, r61])
  all_goals first | (simp only [upd_apply]; split_ifs <;> omega) |
    (simp only [fsaFW, fsaDV]; rfl) | rfl

/-- **The words of the darts of the path on the machine.** -/
theorem fsaProg_execW (c : Config) (hc : WordsBounded W c)
    {k m K Z PDb RVb CPb FLWb DVA CWb CRb FWb F0b DVb : ℕ}
    (r01 : c.nreg 9401 = k)
    (r00 : c.nreg 9400 = m) (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = RVb)
    (r34 : c.nreg 9434 = CPb) (r35 : c.nreg 9435 = FLWb) (r08 : c.nreg 9408 = DVA)
    (r10 : c.nreg 9310 = K) (r21 : c.nreg 9421 = Z) (r36 : c.nreg 9436 = 1)
    (r74 : c.nreg 9374 = CWb) (r75 : c.nreg 9375 = CRb) (r76 : c.nreg 9376 = FWb)
    (r12 : c.nreg 9412 = F0b) (r13 : c.nreg 9413 = DVb)
    (hPD : ∀ l < k, c.nmem (PDb + l) < m) (hRV : ∀ i < m, c.nmem (RVb + i) < m)
    (hLAB : ∀ i < m, c.nmem (DVA + i) - 1 < m)
    (hFLW : ∀ i < m, c.nmem (FLWb + i) + K ≤ W)
    (hDVS : ∀ v < m, c.nmem (DVA + m + v) + K ≤ W)
    (hDG : ∀ v < m, c.nmem (DVA + m + m + v) * Z ≤ W)
    (hrd : PDb + k ≤ CWb ∧ RVb + m ≤ CWb ∧ CPb + m ≤ CWb ∧ FLWb + m ≤ CWb ∧
      DVA + 3 * m ≤ CWb)
    (hsp : CWb + k ≤ CRb ∧ CRb + k ≤ FWb ∧ FWb + k ≤ F0b ∧ F0b + k ≤ DVb)
    (hW : DVb + k + 1 ≤ W) :
    ∃ c' t, Exec P W fsaProg c c' t ∧ t ≤ 38 * k + 3 ∧
      (∀ l < k, c'.nmem (CWb + l) = c.nmem (CPb + c.nmem (PDb + l)) ∧
        c'.nmem (CRb + l) = c.nmem (CPb + c.nmem (RVb + c.nmem (PDb + l))) ∧
        c'.nmem (FWb + l) = fsaFW c.nmem PDb FLWb K Z l ∧
        c'.nmem (F0b + l) = fsaFW c.nmem PDb FLWb K Z l ∧
        c'.nmem (DVb + l) = fsaDV c.nmem PDb DVA m K Z l) ∧
      (∀ a, ¬ (CWb ≤ a ∧ a < CWb + k) → ¬ (CRb ≤ a ∧ a < CRb + k) →
        ¬ (FWb ≤ a ∧ a < FWb + k) → ¬ (F0b ≤ a ∧ a < F0b + k) → ¬ (DVb ≤ a ∧ a < DVb + k) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9461 ∨ 9470 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hrd
  obtain ⟨s1, s2, s3, s4⟩ := hsp
  obtain ⟨c₁, k₁, e₁, hk₁, a61, ak, am, ar, arm, ao⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 9461 0]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 9461 = 0 ∧
      (∀ r, r ≠ 9461 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun l c' =>
    (∀ l' < l, c'.nmem (CWb + l') = c.nmem (CPb + c.nmem (PDb + l')) ∧
        c'.nmem (CRb + l') = c.nmem (CPb + c.nmem (RVb + c.nmem (PDb + l'))) ∧
        c'.nmem (FWb + l') = fsaFW c.nmem PDb FLWb K Z l' ∧
        c'.nmem (F0b + l') = fsaFW c.nmem PDb FLWb K Z l' ∧
        c'.nmem (DVb + l') = fsaDV c.nmem PDb DVA m K Z l') ∧
    (∀ a, ¬ (CWb ≤ a ∧ a < CWb + l) → ¬ (CRb ≤ a ∧ a < CRb + l) →
        ¬ (FWb ≤ a ∧ a < FWb + l) → ¬ (F0b ≤ a ∧ a < F0b + l) → ¬ (DVb ≤ a ∧ a < DVb + l) →
        c'.nmem a = c.nmem a) ∧
    (∀ r, (r < 9461 ∨ 9470 < r) → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have lo : ∀ (c' : Config) l, l ≤ k → (∀ a, ¬ (CWb ≤ a ∧ a < CWb + l) →
      ¬ (CRb ≤ a ∧ a < CRb + l) → ¬ (FWb ≤ a ∧ a < FWb + l) → ¬ (F0b ≤ a ∧ a < F0b + l) →
      ¬ (DVb ≤ a ∧ a < DVb + l) → c'.nmem a = c.nmem a) →
      ∀ a, a < CWb → c'.nmem a = c.nmem a := fun c' l hl h a ha =>
    h a (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h61, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 9461) (b := 9401) (body := fsaBody) J (lo := 0) (hi := k) (B := 36) c₁ e₁.wb_right a61
    (by rw [ak _ (by omega), r01]) (Nat.zero_le _)
    ⟨fun l hl => absurd hl (by omega), fun a _ _ _ _ _ => by rw [am],
      fun r hr => ak r (by omega), ar, arm, ao⟩
    (fun l c' _ hl hw h61 h01 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have L := lo c' l hl.le j2
      have ht := hPD l hl
      have eT : c'.nmem (PDb + l) = c.nmem (PDb + l) := L _ (by omega)
      have hr := hRV _ ht
      have eR : c'.nmem (RVb + c.nmem (PDb + l)) = c.nmem (RVb + c.nmem (PDb + l)) :=
        L _ (by omega)
      have hv := hLAB _ ht
      have eV : c'.nmem (DVA + c.nmem (PDb + l)) = c.nmem (DVA + c.nmem (PDb + l)) :=
        L _ (by omega)
      have eCT : c'.nmem (CPb + c.nmem (PDb + l)) = c.nmem (CPb + c.nmem (PDb + l)) :=
        L _ (by omega)
      have eCR : c'.nmem (CPb + c.nmem (RVb + c.nmem (PDb + l))) =
          c.nmem (CPb + c.nmem (RVb + c.nmem (PDb + l))) := L _ (by omega)
      have eFT : c'.nmem (FLWb + c.nmem (PDb + l)) = c.nmem (FLWb + c.nmem (PDb + l)) :=
        L _ (by omega)
      have eDS : c'.nmem (DVA + m + (c.nmem (DVA + c.nmem (PDb + l)) - 1)) =
          c.nmem (DVA + m + (c.nmem (DVA + c.nmem (PDb + l)) - 1)) := L _ (by omega)
      have eDG : c'.nmem (DVA + m + m + (c.nmem (DVA + c.nmem (PDb + l)) - 1)) =
          c.nmem (DVA + m + m + (c.nmem (DVA + c.nmem (PDb + l)) - 1)) := L _ (by omega)
      have fW : fsaFW c'.nmem PDb FLWb K Z l = fsaFW c.nmem PDb FLWb K Z l := by
        simp only [fsaFW, eT, eFT]
      have fD : fsaDV c'.nmem PDb DVA m K Z l = fsaDV c.nmem PDb DVA m K Z l := by
        simp only [fsaDV, eT, eV, eDS, eDG]
      obtain ⟨c'', t, ex, htt, b61, bm, bk, br, brm, bo⟩ :=
        fsaBody_execW (P := P) c' hw (m := m) (K := K) (Z := Z) (PDb := PDb) (RVb := RVb)
          (CPb := CPb) (FLWb := FLWb) (DVA := DVA) (CWb := CWb) (CRb := CRb) (FWb := FWb)
          (F0b := F0b) (DVb := DVb) (l := l)
          (by rw [j3 _ (by omega), r00]) (by rw [j3 _ (by omega), r02])
          (by rw [j3 _ (by omega), r30]) (by rw [j3 _ (by omega), r34])
          (by rw [j3 _ (by omega), r35]) (by rw [j3 _ (by omega), r08])
          (by rw [j3 _ (by omega), r10]) (by rw [j3 _ (by omega), r21])
          (by rw [j3 _ (by omega), r36]) (by rw [j3 _ (by omega), r74])
          (by rw [j3 _ (by omega), r75]) (by rw [j3 _ (by omega), r76])
          (by rw [j3 _ (by omega), r12]) (by rw [j3 _ (by omega), r13]) h61
          (by rw [eT]; exact ht) (by rw [eT, eR]; exact hr) (by rw [eT, eV]; exact hv)
          (by omega) (by rw [eT, eFT]; exact hFLW _ ht) (by rw [eT, eV, eDS]; exact hDVS _ hv)
          (by rw [eT, eV, eDG]; exact hDG _ hv) (by omega)
      rw [eT, eR, eCT, eCR, fW, fD] at bm
      refine ⟨c'', t, ex, htt.le, b61, by rw [bk _ (by omega)]; exact h01,
        fun l' hl' => ?_, fun a g1 g2 g3 g4 g5 => ?_, fun r hr => by rw [bk r hr]; exact j3 r hr,
        by rw [br, j4], by rw [brm, j5], by rw [bo, j6]⟩
      · rw [bm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with h | rfl
        · obtain ⟨q1, q2, q3, q4, q5⟩ := j1 l' h
          simp only [upd_apply]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (split_ifs <;> first | omega | assumption)
        · simp only [upd_apply]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (split_ifs <;> first | omega | rfl)
      · rw [bm]
        simp only [upd_apply]
        split_ifs <;> first | omega |
          exact j2 a (by omega) (by omega) (by omega) (by omega) (by omega))
  refine ⟨c₂, _, e₁.seq e₂, by rw [hk₁]; simp only [Nat.sub_zero] at hk₂; omega, j1, j2, j3,
    j4, j5, j6⟩

theorem fsbBody_execW (c : Config) (hc : WordsBounded W c) {PDb RVb FLb MKb ETb EHb l : ℕ}
    (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = RVb) (r05 : c.nreg 9405 = FLb)
    (r07 : c.nreg 9407 = MKb) (r14 : c.nreg 9414 = ETb) (r15 : c.nreg 9415 = EHb)
    (r36 : c.nreg 9436 = 1) (r71 : c.nreg 9471 = l)
    (hb : PDb + l ≤ W ∧ RVb + c.nmem (PDb + l) ≤ W ∧ FLb + c.nmem (PDb + l) ≤ W ∧
      FLb + c.nmem (RVb + c.nmem (PDb + l)) ≤ W)
    (hf : MKb + c.nmem (FLb + c.nmem (PDb + l)) ≤ W ∧
      MKb + c.nmem (FLb + c.nmem (RVb + c.nmem (PDb + l))) ≤ W)
    (ho : ETb + 2 * l + 2 ≤ W ∧ EHb + 2 * l + 2 ≤ W) :
    ∃ c' k, Exec P W fsbBody c c' k ∧ k = 26 ∧ c'.nreg 9471 = l + 1 ∧
      c'.nmem = upd (upd (upd (upd c.nmem (ETb + (l + l)) (fsbI c.nmem FLb MKb (c.nmem (PDb + l))))
        (ETb + (l + l) + 1) (fsbI c.nmem FLb MKb (c.nmem (RVb + c.nmem (PDb + l)))))
        (EHb + (l + l)) (fsbI c.nmem FLb MKb (c.nmem (RVb + c.nmem (PDb + l)))))
        (EHb + (l + l) + 1) (fsbI c.nmem FLb MKb (c.nmem (PDb + l))) ∧
      (∀ r, (r < 9471 ∨ 9477 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨ho1, ho2⟩ := ho
  unfold fsbBody
  exec_block
  all_goals try ((try config_simp) <;>
    (try simp only [r02, r30, r05, r07, r14, r15, r36, r71]) <;> omega)
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r02, r30, r05, r07, r14, r15, r36, r71])
  all_goals first | (simp only [upd_apply]; split_ifs <;> omega) |
    (simp only [fsbI, Nat.sub_sub]; rfl) | rfl

/-- **The tails and heads of the explicit arcs on the machine.** -/
theorem fsbProg_execW (c : Config) (hc : WordsBounded W c) {k m PDb RVb FLb MKb ETb EHb : ℕ}
    (r01 : c.nreg 9401 = k) (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = RVb)
    (r05 : c.nreg 9405 = FLb) (r07 : c.nreg 9407 = MKb) (r14 : c.nreg 9414 = ETb)
    (r15 : c.nreg 9415 = EHb) (r36 : c.nreg 9436 = 1)
    (hPD : ∀ l < k, c.nmem (PDb + l) < m) (hRV : ∀ i < m, c.nmem (RVb + i) < m)
    (hFL : ∀ i < m, c.nmem (FLb + i) ≤ m)
    (hrd : PDb + k ≤ ETb ∧ RVb + m ≤ ETb ∧ FLb + m ≤ ETb ∧ MKb + m + 1 ≤ ETb)
    (hsp : ETb + 2 * k ≤ EHb) (hW : EHb + 2 * k + 2 ≤ W) :
    ∃ c' t, Exec P W fsbProg c c' t ∧ t ≤ 28 * k + 3 ∧
      (∀ l < k, c'.nmem (ETb + 2 * l) = fsbI c.nmem FLb MKb (c.nmem (PDb + l)) ∧
        c'.nmem (ETb + 2 * l + 1) = fsbI c.nmem FLb MKb (c.nmem (RVb + c.nmem (PDb + l))) ∧
        c'.nmem (EHb + 2 * l) = fsbI c.nmem FLb MKb (c.nmem (RVb + c.nmem (PDb + l))) ∧
        c'.nmem (EHb + 2 * l + 1) = fsbI c.nmem FLb MKb (c.nmem (PDb + l))) ∧
      (∀ a, ¬ (ETb ≤ a ∧ a < ETb + 2 * k) → ¬ (EHb ≤ a ∧ a < EHb + 2 * k) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9471 ∨ 9477 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h1, h2, h3, h4⟩ := hrd
  obtain ⟨c₁, k₁, e₁, hk₁, a71, ak, am, ar, arm, ao⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 9471 0]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 9471 = 0 ∧
      (∀ r, r ≠ 9471 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun l c' =>
    (∀ l' < l, c'.nmem (ETb + 2 * l') = fsbI c.nmem FLb MKb (c.nmem (PDb + l')) ∧
        c'.nmem (ETb + 2 * l' + 1) = fsbI c.nmem FLb MKb (c.nmem (RVb + c.nmem (PDb + l'))) ∧
        c'.nmem (EHb + 2 * l') = fsbI c.nmem FLb MKb (c.nmem (RVb + c.nmem (PDb + l'))) ∧
        c'.nmem (EHb + 2 * l' + 1) = fsbI c.nmem FLb MKb (c.nmem (PDb + l'))) ∧
    (∀ a, ¬ (ETb ≤ a ∧ a < ETb + 2 * l) → ¬ (EHb ≤ a ∧ a < EHb + 2 * l) →
        c'.nmem a = c.nmem a) ∧
    (∀ r, (r < 9471 ∨ 9477 < r) → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h71, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 9471) (b := 9401) (body := fsbBody) J (lo := 0) (hi := k) (B := 26) c₁ e₁.wb_right a71
    (by rw [ak _ (by omega), r01]) (Nat.zero_le _)
    ⟨fun l hl => absurd hl (by omega), fun a _ _ => by rw [am],
      fun r hr => ak r (by omega), ar, arm, ao⟩
    (fun l c' _ hl hw h71 h01 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have L : ∀ a, a < ETb → c'.nmem a = c.nmem a := fun a ha => j2 a (by omega) (by omega)
      have ht := hPD l hl
      have hr := hRV _ ht
      have eT : c'.nmem (PDb + l) = c.nmem (PDb + l) := L _ (by omega)
      have eR : c'.nmem (RVb + c.nmem (PDb + l)) = c.nmem (RVb + c.nmem (PDb + l)) :=
        L _ (by omega)
      have hft := hFL _ ht
      have hfr := hFL _ hr
      have eFT : c'.nmem (FLb + c.nmem (PDb + l)) = c.nmem (FLb + c.nmem (PDb + l)) :=
        L _ (by omega)
      have eFR : c'.nmem (FLb + c.nmem (RVb + c.nmem (PDb + l))) =
          c.nmem (FLb + c.nmem (RVb + c.nmem (PDb + l))) := L _ (by omega)
      have iT : fsbI c'.nmem FLb MKb (c.nmem (PDb + l)) = fsbI c.nmem FLb MKb (c.nmem (PDb + l)) := by
        simp only [fsbI, eFT]; rw [L _ (by omega)]
      have iR : fsbI c'.nmem FLb MKb (c.nmem (RVb + c.nmem (PDb + l))) =
          fsbI c.nmem FLb MKb (c.nmem (RVb + c.nmem (PDb + l))) := by
        simp only [fsbI, eFR]; rw [L _ (by omega)]
      obtain ⟨c'', t, ex, htt, b71, bm, bk, br, brm, bo⟩ :=
        fsbBody_execW (P := P) c' hw (PDb := PDb) (RVb := RVb) (FLb := FLb) (MKb := MKb)
          (ETb := ETb) (EHb := EHb) (l := l)
          (by rw [j3 _ (by omega), r02]) (by rw [j3 _ (by omega), r30])
          (by rw [j3 _ (by omega), r05]) (by rw [j3 _ (by omega), r07])
          (by rw [j3 _ (by omega), r14]) (by rw [j3 _ (by omega), r15])
          (by rw [j3 _ (by omega), r36]) h71
          (by rw [eT, eR]; omega) (by rw [eT, eR, eFT, eFR]; omega) ⟨by omega, by omega⟩
      rw [eT, eR, iT, iR] at bm
      refine ⟨c'', t, ex, htt.le, b71, by rw [bk _ (by omega)]; exact h01,
        fun l' hl' => ?_, fun a g1 g2 => ?_, fun r hr => by rw [bk r hr]; exact j3 r hr,
        by rw [br, j4], by rw [brm, j5], by rw [bo, j6]⟩
      · rw [bm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with h | rfl
        · obtain ⟨q1, q2, q3, q4⟩ := j1 l' h
          simp only [upd_apply]
          refine ⟨?_, ?_, ?_, ?_⟩ <;> (split_ifs <;> first | omega | assumption)
        · simp only [upd_apply]
          refine ⟨?_, ?_, ?_, ?_⟩ <;> (split_ifs <;> first | omega | rfl)
      · rw [bm]
        simp only [upd_apply]
        split_ifs <;> first | omega | exact j2 a (by omega) (by omega))
  refine ⟨c₂, _, e₁.seq e₂, by rw [hk₁]; simp only [Nat.sub_zero] at hk₂; omega, j1, j2, j3,
    j4, j5, j6⟩

theorem fscBody_execW (c : Config) (hc : WordsBounded W c) {PWb PRb ELb K x : ℕ}
    (r16 : c.nreg 9416 = PWb) (r17 : c.nreg 9417 = PRb) (r77 : c.nreg 9377 = ELb)
    (r10 : c.nreg 9310 = K) (r36 : c.nreg 9436 = 1) (r82 : c.nreg 9482 = 0)
    (r80 : c.nreg 9480 = x) (ho : PWb + x + 1 ≤ W ∧ PRb + x ≤ W ∧ ELb + x ≤ W) :
    ∃ c' k, Exec P W fscBody c c' k ∧ k = 7 ∧ c'.nreg 9480 = x + 1 ∧
      c'.nmem = upd (upd (upd c.nmem (PWb + x) 0) (PRb + x) K) (ELb + x) K ∧
      (∀ r, r ≠ 9480 → r ≠ 9483 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨ho1, ho2, ho3⟩ := ho
  unfold fscBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r16, r17, r77, r10, r36, r82, r80]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r16, r17, r77, r10, r36, r82, r80])
  all_goals first | (simp only [upd_apply]; split_ifs <;> omega) | rfl

/-- **The prices, offset prices and lengths at the start on the machine.** -/
theorem fscProg_execW (c : Config) (hc : WordsBounded W c) {k PWb PRb ELb K : ℕ}
    (r01 : c.nreg 9401 = k) (r16 : c.nreg 9416 = PWb) (r17 : c.nreg 9417 = PRb)
    (r77 : c.nreg 9377 = ELb) (r10 : c.nreg 9310 = K) (r36 : c.nreg 9436 = 1)
    (hsp : (PWb + 2 * k ≤ PRb ∨ PRb + 2 * k ≤ PWb) ∧ (PWb + 2 * k ≤ ELb ∨ ELb + 2 * k ≤ PWb) ∧
      (PRb + 2 * k ≤ ELb ∨ ELb + 2 * k ≤ PRb))
    (hW : PWb + 2 * k + 1 ≤ W ∧ PRb + 2 * k ≤ W ∧ ELb + 2 * k ≤ W) :
    ∃ c' t, Exec P W fscProg c c' t ∧ t ≤ 9 * (2 * k) + 5 ∧
      (∀ x < 2 * k, c'.nmem (PWb + x) = 0 ∧ c'.nmem (PRb + x) = K ∧ c'.nmem (ELb + x) = K) ∧
      (∀ a, ¬ (PWb ≤ a ∧ a < PWb + 2 * k) → ¬ (PRb ≤ a ∧ a < PRb + 2 * k) →
        ¬ (ELb ≤ a ∧ a < ELb + 2 * k) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9480 ∨ 9483 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hWa, hWb, hWc⟩ := hW
  obtain ⟨c₁, k₁, e₁, hk₁, a80, a82, a81, ak, am, ar, arm, ao⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 9480 0, .constN 9482 0, .addN 9481 9401 9401]) c c₁ k₁ ∧
      k₁ = 3 ∧ c₁.nreg 9480 = 0 ∧ c₁.nreg 9482 = 0 ∧ c₁.nreg 9481 = 2 * k ∧
      (∀ r, (r < 9480 ∨ 9482 < r) → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r01]); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r01]; omega)
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun x c' =>
    (∀ x' < x, c'.nmem (PWb + x') = 0 ∧ c'.nmem (PRb + x') = K ∧ c'.nmem (ELb + x') = K) ∧
    (∀ a, ¬ (PWb ≤ a ∧ a < PWb + x) → ¬ (PRb ≤ a ∧ a < PRb + x) →
        ¬ (ELb ≤ a ∧ a < ELb + x) → c'.nmem a = c.nmem a) ∧
    (∀ r, r ≠ 9480 → r ≠ 9483 → c'.nreg r = c₁.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨hs1, hs2, hs3⟩ := hsp
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h80, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 9480) (b := 9481) (body := fscBody) J (lo := 0) (hi := 2 * k) (B := 7) c₁ e₁.wb_right
    a80 a81 (Nat.zero_le _)
    ⟨fun x hx => absurd hx (by omega), fun a _ _ _ => by rw [am], fun _ _ _ => rfl, ar, arm, ao⟩
    (fun x c' _ hx hw h80 h81 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      obtain ⟨c'', t, ex, htt, b80, bm, bk, br, brm, bo⟩ :=
        fscBody_execW (P := P) c' hw (PWb := PWb) (PRb := PRb) (ELb := ELb) (K := K) (x := x)
          (by rw [j3 _ (by omega) (by omega), ak _ (by omega), r16])
          (by rw [j3 _ (by omega) (by omega), ak _ (by omega), r17])
          (by rw [j3 _ (by omega) (by omega), ak _ (by omega), r77])
          (by rw [j3 _ (by omega) (by omega), ak _ (by omega), r10])
          (by rw [j3 _ (by omega) (by omega), ak _ (by omega), r36]) (by rw [j3 _ (by omega) (by omega), a82]) h80
          (by omega)
      refine ⟨c'', t, ex, htt.le, b80, by rw [bk _ (by omega) (by omega)]; exact h81,
        fun x' hx' => ?_, fun a g1 g2 g3 => ?_,
        fun r h1 h2 => by rw [bk r h1 h2]; exact j3 r h1 h2,
        by rw [br, j4], by rw [brm, j5], by rw [bo, j6]⟩
      · rw [bm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hx' with h | rfl
        · obtain ⟨q1, q2, q3⟩ := j1 x' h
          simp only [upd_apply]
          refine ⟨?_, ?_, ?_⟩ <;> (split_ifs <;> first | omega | assumption)
        · simp only [upd_apply]
          refine ⟨?_, ?_, ?_⟩ <;> (split_ifs <;> first | omega | rfl)
      · rw [bm]
        simp only [upd_apply]
        split_ifs <;> first | omega | exact j2 a (by omega) (by omega) (by omega))
  refine ⟨c₂, _, e₁.seq e₂, by rw [hk₁]; simp only [Nat.sub_zero] at hk₂; omega, j1, j2,
    fun r hr => by rw [j3 r (by omega) (by omega), ak r (by omega)], j4, j5, j6⟩

set_option maxHeartbeats 1600000 in
theorem proP3b_execW (p : FpIn) (c : Config) (hc : WordsBounded W c) {A0 : ℕ}
    (hR : RegP1 p A0 c) (r10 : c.nreg 9310 = p.K)
    (hlo : ∀ a < A0, c.nmem a = p.mem a)
    (hLAB : ∀ i < p.m, c.nmem (A0 + p.m + p.m + p.m + p.m + 1 + i) = p.vl i + 1)
    (hDV : ∀ v < p.m, c.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + v) = dvS p.vl p.FLW p.m v ∧
        c.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + v) = dvC p.vl p.m v)
    (hRV : ∀ i < p.m, p.RV i < p.m) (hSG : PermOn (sgF p.d p.m p.mem) p.m)
    (hPD : ∀ l < p.k, p.PD l < p.m)
    (hfr : p.d + 4 + 7 * p.m ≤ A0) (hsg : p.PDb + p.k ≤ A0)
    (hW1 : p.Qb A0 + 15 * p.k + 2 ≤ W)
    (hW2 : ∑ i ∈ range p.m, p.FLW i + p.K + p.m * p.Z ≤ W) :
    ∃ c' t, Exec P W proP3b c c' t ∧ t ≤ 38 * p.k + 3 ∧
      (∀ l < p.k, c'.nmem (p.Qb A0 + l) = p.CP (p.PD l) ∧
        c'.nmem (p.Qb A0 + p.k + l) = p.CP (p.RV (p.PD l)) ∧
        c'.nmem (p.Qb A0 + p.k + p.k + l) = p.FLW (p.PD l) + p.K - p.Z ∧
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + l) = p.FLW (p.PD l) + p.K - p.Z ∧
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + l) = p.DVw l) ∧
      (∀ a, ¬ (p.Qb A0 ≤ a ∧ a < p.Qb A0 + p.k + p.k + p.k) →
        ¬ (p.Qb A0 + p.k + p.k + p.k + p.k + p.k ≤ a ∧
          a < p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9461 ∨ 9470 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨g00, -, g36, g21, g01, -, g02, g30, -, g34, g35, -, -, -, -, g08, -, -, -, g74, g75,
    g76, -, g12, g13, -⟩ := hR
  have hPDm : ∀ l < p.k, c.nmem (p.PDb + l) = p.PD l := fun l hl => hlo _ (by omega)
  have hRVm : ∀ i < p.m, c.nmem (p.d + 4 + p.m + i) = p.RV i := fun i hi => hlo _ (by omega)
  have hCPm : ∀ i < p.m, c.nmem (p.d + 4 + p.m + p.m + p.m + i) = p.CP i := fun i hi =>
    hlo _ (by omega)
  have hFWm : ∀ i < p.m, c.nmem (p.d + 4 + p.m + p.m + p.m + p.m + p.m + p.m + i) = p.FLW i :=
    fun i hi => hlo _ (by omega)
  have hFLle : ∀ i < p.m, p.FLW i ≤ ∑ j ∈ range p.m, p.FLW j := fun i hi =>
    single_le_sum (fun j _ => Nat.zero_le _) (mem_range.2 hi)
  have hvl : ∀ i < p.m, p.vl i < p.m := fun i hi => olab_lt hSG hi
  have hQ : p.Qb A0 = A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m + p.m := rfl
  obtain ⟨c₃, t₃, e₃, ht₃, sA, sk, sn, sr, srm, so⟩ :=
    fsaProg_execW (P := P) c hc (k := p.k) (m := p.m) (K := p.K) (Z := p.Z)
      (PDb := p.PDb) (RVb := p.d + 4 + p.m) (CPb := p.d + 4 + p.m + p.m + p.m)
      (FLWb := p.d + 4 + p.m + p.m + p.m + p.m + p.m + p.m)
      (DVA := A0 + p.m + p.m + p.m + p.m + 1) (CWb := p.Qb A0) (CRb := p.Qb A0 + p.k)
      (FWb := p.Qb A0 + p.k + p.k) (F0b := p.Qb A0 + p.k + p.k + p.k + p.k + p.k)
      (DVb := p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k)
      g01 g00 g02 g30 g34 g35 g08 r10 g21 g36 g74 g75 g76 g12 g13
      (fun l hl => by rw [hPDm l hl]; exact hPD l hl)
      (fun i hi => by rw [hRVm i hi]; exact hRV i hi)
      (fun i hi => by rw [hLAB i hi]; have := hvl i hi; omega)
      (fun i hi => by rw [hFWm i hi]; have := hFLle i hi; omega)
      (fun v hv => by
        rw [(hDV v hv).1]
        have := dvS_le_sum p.vl p.FLW p.m v; omega)
      (fun v hv => by
        rw [(hDV v hv).2]
        have := dvC_le p.vl p.m v
        have := Nat.mul_le_mul_right p.Z this; omega)
      ⟨by omega, by omega, by omega, by omega, by omega⟩
      ⟨by omega, by omega, by omega, by omega⟩ (by omega)
  refine ⟨c₃, _, e₃, by omega, fun l hl => ?_, fun a h1 h2 => ?_, sn, sr,
    srm, so⟩
  · obtain ⟨s1, s2, s3, s4, s5⟩ := sA l hl
    have := hPD l hl
    have hv := hvl _ this
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [s1, hPDm l hl, hCPm _ this]
    · rw [s2, hPDm l hl, hRVm _ this, hCPm _ (hRV _ this)]
    · rw [s3]; simp only [fsaFW]; rw [hPDm l hl, hFWm _ this]
    · rw [s4]; simp only [fsaFW]; rw [hPDm l hl, hFWm _ this]
    · rw [s5]; simp only [fsaDV]
      rw [hPDm l hl, hLAB _ this, Nat.add_sub_cancel, (hDV _ hv).1, (hDV _ hv).2]
      rfl
  · exact sk a (by omega) (by omega) (by omega) (by omega) (by omega)

set_option maxHeartbeats 1600000 in
theorem proP3c_execW (p : FpIn) (c : Config) (hc : WordsBounded W c) {A0 : ℕ}
    (hR : RegP1 p A0 c) (r10 : c.nreg 9310 = p.K)
    (hlo : ∀ a < A0, c.nmem a = p.mem a)
    (hFLm : ∀ i < p.m, c.nmem (A0 + p.m + i) = p.lab i)
    (hMKm : ∀ a ≤ p.m, c.nmem (A0 + p.m + p.m + p.m + a) = p.cw.mks a)
    (hRV : ∀ i < p.m, p.RV i < p.m) (hNX : PermOn (nxF p.d p.m p.mem) p.m)
    (hPD : ∀ l < p.k, p.PD l < p.m)
    (hfr : p.d + 4 + 7 * p.m ≤ A0) (hsg : p.PDb + p.k ≤ A0)
    (hW1 : p.Qb A0 + 15 * p.k + 2 ≤ W) :
    ∃ c' t, Exec P W proP3c c c' t ∧ t ≤ 46 * p.k + 8 ∧
      (∀ l < p.k,
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + 2 * l) = p.ix (p.PD l) ∧
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + 2 * l + 1) =
          p.ix (p.RV (p.PD l)) ∧
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + 2 * l) =
          p.ix (p.RV (p.PD l)) ∧
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + 2 * l + 1) =
          p.ix (p.PD l)) ∧
      (∀ x < 2 * p.k,
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + x) =
          0 ∧
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k +
          p.k + x) = p.K ∧
        c'.nmem (p.Qb A0 + p.k + p.k + p.k + x) = p.K) ∧
      (∀ a, ¬ (p.Qb A0 + p.k + p.k + p.k ≤ a ∧ a < p.Qb A0 + p.k + p.k + p.k + p.k + p.k) →
        ¬ (p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k ≤ a ∧ a < p.Qb A0 + 15 * p.k) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9471 ∨ 9477 < r) → (r < 9480 ∨ 9483 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨g00, -, g36, -, g01, -, g02, g30, -, -, -, -, g05, -, g07, -, -, -, -, -, -, -, g77,
    -, -, g14, g15, g16, g17, -⟩ := hR
  have hPDm : ∀ l < p.k, c.nmem (p.PDb + l) = p.PD l := fun l hl => hlo _ (by omega)
  have hRVm : ∀ i < p.m, c.nmem (p.d + 4 + p.m + i) = p.RV i := fun i hi => hlo _ (by omega)
  have hQ : p.Qb A0 = A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m + p.m := rfl
  obtain ⟨c₄, t₄, e₄, ht₄, bA, bk4, bn, br4, brm4, bo4⟩ :=
    fsbProg_execW (P := P) c hc (k := p.k) (m := p.m) (PDb := p.PDb)
      (RVb := p.d + 4 + p.m) (FLb := A0 + p.m) (MKb := A0 + p.m + p.m + p.m)
      (ETb := p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k)
      (EHb := p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k)
      g01 g02 g30 g05 g07 g14 g15 g36
      (fun l hl => by rw [hPDm l hl]; exact hPD l hl)
      (fun i hi => by rw [hRVm i hi]; exact hRV i hi)
      (fun i hi => by rw [hFLm i hi]; have := olab_lt hNX hi; simp only [FpIn.lab]; omega)
      ⟨by omega, by omega, by omega, by omega⟩ (by omega) (by omega)
  have hI : ∀ x < p.m, fsbI c.nmem (A0 + p.m) (A0 + p.m + p.m + p.m) x = p.ix x := fun x hx => by
    have := olab_lt hNX hx
    simp only [fsbI]
    rw [hFLm x hx, hMKm _ (by simp only [FpIn.lab]; omega)]
    rfl
  have n4 : ∀ r, (r < 9471 ∨ 9477 < r) → c₄.nreg r = c.nreg r := bn
  obtain ⟨c₅, t₅, e₅, ht₅, cA, ck, cn, cr, crm, co⟩ :=
    fscProg_execW (P := P) c₄ e₄.wb_right (k := p.k)
      (PWb := p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k)
      (PRb := p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k)
      (ELb := p.Qb A0 + p.k + p.k + p.k) (K := p.K)
      (by rw [n4 _ (by omega), g01]) (by rw [n4 _ (by omega), g16])
      (by rw [n4 _ (by omega), g17]) (by rw [n4 _ (by omega), g77]) (by rw [n4 _ (by omega), r10])
      (by rw [n4 _ (by omega), g36])
      ⟨Or.inl (by omega), Or.inr (by omega), Or.inr (by omega)⟩ (by omega)
  refine ⟨c₅, _, e₄.seq e₅, by omega, fun l hl => ?_, cA, fun a h1 h2 => ?_,
    fun r h1 h2 => by rw [cn r h2, n4 r h1], by rw [cr, br4], by rw [crm, brm4], by rw [co, bo4]⟩
  · obtain ⟨s1, s2, s3, s4⟩ := bA l hl
    have := hPD l hl
    have hr := hRV _ this
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ck _ (by omega) (by omega) (by omega), s1, hPDm l hl, hI _ this]
    · rw [ck _ (by omega) (by omega) (by omega), s2, hPDm l hl, hRVm _ this, hI _ hr]
    · rw [ck _ (by omega) (by omega) (by omega), s3, hPDm l hl, hRVm _ this, hI _ hr]
    · rw [ck _ (by omega) (by omega) (by omega), s4, hPDm l hl, hI _ this]
  · rw [ck _ (by omega) (by omega) (by omega), bk4 _ (by omega) (by omega)]

end BKMNW

end PlanarFlow
