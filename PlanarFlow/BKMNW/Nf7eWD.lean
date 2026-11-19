module

public import PlanarFlow.BKMNW.Nf7cE

/-!
# Per-address word bounds for the final-step loops

Copies of `lnABody_exec`, `lnA_exec`, `lnBBody_exec`, `lnB_exec`, `potBody_exec`, `potP_exec`,
`flqBody_exec`, `flP_exec` (suffix `W`) whose word-bound hypotheses bound each address separately
(or the top address, given the layout hypotheses) instead of a sum of addresses. The programs and
conclusions are unchanged.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1000000 in
theorem lnABody_execW (c : Config) (hc : WordsBounded W c) {CPb FLWb Z K LNb i : ℕ}
    (r34 : c.nreg 9434 = CPb) (r35 : c.nreg 9435 = FLWb) (r21 : c.nreg 9421 = Z)
    (r10 : c.nreg 9310 = K) (r77 : c.nreg 9477 = LNb) (r36 : c.nreg 9436 = 1)
    (r84 : c.nreg 9484 = i) (hb : CPb + i ≤ W ∧ FLWb + i ≤ W ∧ LNb + i ≤ W ∧ i + 1 ≤ W)
    (hv : c.nmem (CPb + i) + Z + K ≤ W) :
    ∃ c' t, Exec P W lnABody c c' t ∧ t = 10 ∧ c'.nreg 9484 = i + 1 ∧
      c'.nmem = upd c.nmem (LNb + i) (c.nmem (CPb + i) + Z + K - c.nmem (FLWb + i)) ∧
      (∀ r, (r < 9484 ∨ 9486 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  unfold lnABody
  exec_block
  all_goals try ((try config_simp) <;> (try simp only [r34, r35, r21, r10, r77, r36, r84]) <;>
    first | omega | exact Nat.le_trans (Nat.sub_le _ _) (by omega))
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r34, r35, r21, r10, r77, r36, r84])
  all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

theorem lnA_execW (c : Config) (hc : WordsBounded W c) {m CPb FLWb Z K LNb : ℕ}
    (r00 : c.nreg 9400 = m) (r34 : c.nreg 9434 = CPb) (r35 : c.nreg 9435 = FLWb)
    (r21 : c.nreg 9421 = Z) (r10 : c.nreg 9310 = K) (r77 : c.nreg 9477 = LNb)
    (r36 : c.nreg 9436 = 1) (hd : CPb + m ≤ LNb ∧ FLWb + m ≤ LNb)
    (hb : LNb + m + 1 ≤ W) (hv : ∀ i < m, c.nmem (CPb + i) + Z + K ≤ W) :
    ∃ c' t, Exec P W lnA c c' t ∧ t ≤ 12 * m + 3 ∧
      (∀ i < m, c'.nmem (LNb + i) = c.nmem (CPb + i) + Z + K - c.nmem (FLWb + i)) ∧
      (∀ a, (a < LNb ∨ LNb + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9484 ∨ 9486 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a84, ak, am, ar, arm, ao⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 9484 0]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 9484 = 0 ∧
      (∀ r, r ≠ 9484 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ i' < i, c'.nmem (LNb + i') = c.nmem (CPb + i') + Z + K - c.nmem (FLWb + i')) ∧
    (∀ a, (a < LNb ∨ LNb + i ≤ a) → c'.nmem a = c.nmem a) ∧
    (∀ r, (r < 9484 ∨ 9486 < r) → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h84, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 9484) (b := 9400) (body := lnABody) J (lo := 0) (hi := m) (B := 10) c₁ e₁.wb_right a84
    (by rw [ak _ (by omega), r00]) (Nat.zero_le _)
    ⟨fun i hi => absurd hi (by omega), fun a _ => by rw [am], fun r hr => ak r (by omega), ar,
      arm, ao⟩
    (fun i c' _ hi hw h84 h00 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have eC : c'.nmem (CPb + i) = c.nmem (CPb + i) := j2 _ (Or.inl (by omega))
      have eF : c'.nmem (FLWb + i) = c.nmem (FLWb + i) := j2 _ (Or.inl (by omega))
      obtain ⟨c'', t, ex, htt, b84, bm, bk, br, brm, bo⟩ :=
        lnABody_execW (P := P) c' hw (CPb := CPb) (FLWb := FLWb) (Z := Z) (K := K) (LNb := LNb)
          (by rw [j3 _ (by omega), r34]) (by rw [j3 _ (by omega), r35])
          (by rw [j3 _ (by omega), r21]) (by rw [j3 _ (by omega), r10])
          (by rw [j3 _ (by omega), r77]) (by rw [j3 _ (by omega), r36]) h84 (by omega)
          (by rw [eC]; exact hv i hi)
      rw [eC, eF] at bm
      refine ⟨c'', t, ex, htt.le, b84, by rw [bk _ (by omega)]; exact h00,
        fun i' hi' => ?_, fun a ha => ?_, fun r hr => by rw [bk r hr]; exact j3 r hr,
        by rw [br, j4], by rw [brm, j5], by rw [bo, j6]⟩
      · rw [bm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j1 i' h
        · rw [upd_same]
      · rw [bm, upd_other _ _ _ (by omega)]; exact j2 a (by omega))
  refine ⟨c₂, _, e₁.seq e₂, by rw [hk₁]; simp only [Nat.sub_zero] at hk₂; omega, j1, j2, j3,
    j4, j5, j6⟩

set_option maxHeartbeats 1600000 in
theorem lnBBody_execW (c : Config) (hc : WordsBounded W c) {PDb RVb CWb CRb FWb LNb K l : ℕ}
    (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = RVb) (r74 : c.nreg 9374 = CWb)
    (r75 : c.nreg 9375 = CRb) (r76 : c.nreg 9376 = FWb) (r77 : c.nreg 9477 = LNb)
    (r10 : c.nreg 9310 = K) (r36 : c.nreg 9436 = 1) (r84 : c.nreg 9484 = l)
    (hb : PDb + l ≤ W ∧ CWb + l ≤ W ∧ CRb + l ≤ W ∧ FWb + l ≤ W ∧ l + 1 ≤ W)
    (ht : LNb + c.nmem (PDb + l) ≤ W ∧ RVb + c.nmem (PDb + l) ≤ W)
    (hr : LNb + c.nmem (RVb + c.nmem (PDb + l)) ≤ W)
    (hx : c.nmem (CWb + l) + K + K ≤ W) (hy : c.nmem (CRb + l) + c.nmem (FWb + l) ≤ W) :
    ∃ c' t, Exec P W lnBBody c c' t ∧ t = 19 ∧ c'.nreg 9484 = l + 1 ∧
      c'.nmem = upd (upd c.nmem (LNb + c.nmem (PDb + l))
        (c.nmem (CWb + l) + K + K - c.nmem (FWb + l)))
        (LNb + c.nmem (RVb + c.nmem (PDb + l))) (c.nmem (CRb + l) + c.nmem (FWb + l)) ∧
      (∀ r, (r < 9484 ∨ 9490 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  obtain ⟨ht1, ht2⟩ := ht
  have hc' := hc
  unfold lnBBody
  exec_block
  all_goals try ((try config_simp) <;>
    (try simp only [r02, r30, r74, r75, r76, r77, r10, r36, r84]) <;>
    first | omega | exact Nat.le_trans (Nat.sub_le _ _) (by omega))
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r02, r30, r74, r75, r76, r77, r10, r36, r84])
  all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

theorem lnB_execW (c : Config) (hc : WordsBounded W c) {k m PDb RVb CWb CRb FWb LNb K : ℕ}
    (r01 : c.nreg 9401 = k)
    (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = RVb) (r74 : c.nreg 9374 = CWb)
    (r75 : c.nreg 9375 = CRb) (r76 : c.nreg 9376 = FWb) (r77 : c.nreg 9477 = LNb)
    (r10 : c.nreg 9310 = K) (r36 : c.nreg 9436 = 1)
    (hPD : ∀ l < k, c.nmem (PDb + l) < m) (hRV : ∀ i < m, c.nmem (RVb + i) < m)
    (hd : PDb + k ≤ LNb ∧ RVb + m ≤ LNb ∧ CWb + k ≤ LNb ∧ CRb + k ≤ LNb ∧ FWb + k ≤ LNb)
    (hb : LNb + m + 1 ≤ W)
    (hx : ∀ l < k, c.nmem (CWb + l) + K + K ≤ W)
    (hy : ∀ l < k, c.nmem (CRb + l) + c.nmem (FWb + l) ≤ W) :
    ∃ c' t, Exec P W lnB c c' t ∧ t ≤ 21 * k + 3 ∧
      c'.nmem = lnBM c.nmem PDb RVb CWb CRb FWb LNb K k ∧
      (∀ r, (r < 9484 ∨ 9490 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a84, ak, am, ar, arm, ao⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 9484 0]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 9484 = 0 ∧
      (∀ r, r ≠ 9484 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun l c' =>
    c'.nmem = lnBM c.nmem PDb RVb CWb CRb FWb LNb K l ∧
    (∀ r, (r < 9484 ∨ 9490 < r) → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h84, j1, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 9484) (b := 9401) (body := lnBBody) J (lo := 0) (hi := k) (B := 19) c₁ e₁.wb_right a84
    (by rw [ak _ (by omega), r01]) (Nat.zero_le _)
    ⟨am, fun r hr => ak r (by omega), ar, arm, ao⟩
    (fun l c' _ hl hw h84 h01 ⟨j1, j3, j4, j5, j6⟩ => by
      have L : ∀ a, (a < LNb ∨ LNb + m ≤ a) → c'.nmem a = c.nmem a := fun a ha => by
        rw [j1]; exact lnBM_out _ (fun l' hl' => hPD l' (by omega)) hRV ha
      have ht := hPD l hl
      have hr := hRV _ ht
      have eT : c'.nmem (PDb + l) = c.nmem (PDb + l) := L _ (Or.inl (by omega))
      have eR : c'.nmem (RVb + c.nmem (PDb + l)) = c.nmem (RVb + c.nmem (PDb + l)) :=
        L _ (Or.inl (by omega))
      have eCW : c'.nmem (CWb + l) = c.nmem (CWb + l) := L _ (Or.inl (by omega))
      have eCR : c'.nmem (CRb + l) = c.nmem (CRb + l) := L _ (Or.inl (by omega))
      have eFW : c'.nmem (FWb + l) = c.nmem (FWb + l) := L _ (Or.inl (by omega))
      obtain ⟨c'', t, ex, htt, b84, bm, bk, br, brm, bo⟩ :=
        lnBBody_execW (P := P) c' hw (PDb := PDb) (RVb := RVb) (CWb := CWb) (CRb := CRb)
          (FWb := FWb) (LNb := LNb) (K := K)
          (by rw [j3 _ (by omega), r02]) (by rw [j3 _ (by omega), r30])
          (by rw [j3 _ (by omega), r74]) (by rw [j3 _ (by omega), r75])
          (by rw [j3 _ (by omega), r76]) (by rw [j3 _ (by omega), r77])
          (by rw [j3 _ (by omega), r10]) (by rw [j3 _ (by omega), r36]) h84 (by omega)
          (by rw [eT]; omega) (by rw [eT, eR]; omega) (by rw [eCW]; exact hx l hl)
          (by rw [eCR, eFW]; exact hy l hl)
      rw [eT, eR, eCW, eCR, eFW, j1] at bm
      exact ⟨c'', t, ex, htt.le, b84, by rw [bk _ (by omega)]; exact h01, bm,
        fun r hr => by rw [bk r hr]; exact j3 r hr, by rw [br, j4], by rw [brm, j5],
        by rw [bo, j6]⟩)
  refine ⟨c₂, _, e₁.seq e₂, by rw [hk₁]; simp only [Nat.sub_zero] at hk₂; omega, j1, j3, j4, j5,
    j6⟩

set_option maxHeartbeats 1000000 in
theorem potBody_execW (c : Config) (hc : WordsBounded W c) {IDb VLb POTb v : ℕ}
    (r89 : c.nreg 9489 = IDb) (r90 : c.nreg 9490 = VLb) (r79 : c.nreg 9479 = POTb)
    (r36 : c.nreg 9436 = 1) (r91 : c.nreg 9491 = v) (hb : IDb + v ≤ W ∧ VLb + v ≤ W ∧ v + 1 ≤ W)
    (hp : POTb + c.nmem (IDb + v) + 1 ≤ W) :
    ∃ c' t, Exec P W potBody c c' t ∧ t = 8 ∧ c'.nreg 9491 = v + 1 ∧
      c'.nmem = upd c.nmem (POTb + c.nmem (IDb + v) + 1) (c.nmem (VLb + v)) ∧
      (∀ r, (r < 9491 ∨ 9494 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hb1, hb2, hb3⟩ := hb
  have hc' := hc
  unfold potBody
  exec_block
  all_goals try ((try config_simp) <;> (try simp only [r89, r90, r79, r36, r91]) <;> omega)
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r89, r90, r79, r36, r91])
  all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

theorem potP_execW (c : Config) (hc : WordsBounded W c) {w G IDb VLb POTb : ℕ}
    (r88 : c.nreg 9488 = w) (r89 : c.nreg 9489 = IDb) (r90 : c.nreg 9490 = VLb)
    (r79 : c.nreg 9479 = POTb) (r36 : c.nreg 9436 = 1)
    (hid : ∀ v < w, c.nmem (IDb + v) < G)
    (hd : (IDb + w ≤ POTb ∨ POTb + G + 1 ≤ IDb) ∧ (VLb + w ≤ POTb ∨ POTb + G + 1 ≤ VLb))
    (hb : IDb + w ≤ W ∧ VLb + w ≤ W ∧ POTb + G + 1 ≤ W ∧ w + 1 ≤ W) :
    ∃ c' t, Exec P W potP c c' t ∧ t ≤ 10 * w + 3 ∧
      c'.nmem = potM c.nmem IDb VLb POTb w ∧
      (∀ r, (r < 9491 ∨ 9494 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  obtain ⟨c₁, k₁, e₁, hk₁, a91, ak, am, ar, arm, ao⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 9491 0]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 9491 = 0 ∧
      (∀ r, r ≠ 9491 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun v c' =>
    c'.nmem = potM c.nmem IDb VLb POTb v ∧
    (∀ r, (r < 9491 ∨ 9494 < r) → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h91, j1, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 9491) (b := 9488) (body := potBody) J (lo := 0) (hi := w) (B := 8) c₁ e₁.wb_right a91
    (by rw [ak _ (by omega), r88]) (Nat.zero_le _)
    ⟨am, fun r hr => ak r (by omega), ar, arm, ao⟩
    (fun v c' _ hv hw h91 h88 ⟨j1, j3, j4, j5, j6⟩ => by
      have L : ∀ a, (a < POTb ∨ POTb + G + 1 ≤ a) → c'.nmem a = c.nmem a := fun a ha => by
        rw [j1]; exact potM_out _ (fun v' hv' => hid v' (by omega)) ha
      have eI : c'.nmem (IDb + v) = c.nmem (IDb + v) := L _ (by omega)
      have eV : c'.nmem (VLb + v) = c.nmem (VLb + v) := L _ (by omega)
      have hi := hid v hv
      obtain ⟨c'', t, ex, htt, b91, bm, bk, br, brm, bo⟩ :=
        potBody_execW (P := P) c' hw (IDb := IDb) (VLb := VLb) (POTb := POTb)
          (by rw [j3 _ (by omega), r89]) (by rw [j3 _ (by omega), r90])
          (by rw [j3 _ (by omega), r79]) (by rw [j3 _ (by omega), r36]) h91 (by omega)
          (by rw [eI]; omega)
      rw [eI, eV, j1] at bm
      exact ⟨c'', t, ex, htt.le, b91, by rw [bk _ (by omega)]; exact h88, bm,
        fun r hr => by rw [bk r hr]; exact j3 r hr, by rw [br, j4], by rw [brm, j5],
        by rw [bo, j6]⟩)
  refine ⟨c₂, _, e₁.seq e₂, by rw [hk₁]; simp only [Nat.sub_zero] at hk₂; omega, j1, j3, j4, j5,
    j6⟩

set_option maxHeartbeats 2000000 in
theorem flqBody_execW (c : Config) (hc : WordsBounded W c) {CPb RVb LABb POTb LNb FLb Z K i : ℕ}
    (r34 : c.nreg 9434 = CPb) (r30 : c.nreg 9430 = RVb) (r05 : c.nreg 9405 = LABb)
    (r79 : c.nreg 9479 = POTb) (r77 : c.nreg 9477 = LNb) (r35 : c.nreg 9435 = FLb)
    (r21 : c.nreg 9421 = Z) (r10 : c.nreg 9310 = K) (r36 : c.nreg 9436 = 1)
    (r91 : c.nreg 9491 = i) (hb : CPb + i ≤ W ∧ RVb + i ≤ W ∧ LABb + i ≤ W ∧ LNb + i ≤ W ∧ FLb + i ≤ W ∧
      i + 1 ≤ W)
    (h1 : LABb + c.nmem (RVb + i) ≤ W)
    (h2 : POTb + c.nmem (LABb + c.nmem (RVb + i)) ≤ W)
    (h3 : POTb + c.nmem (LABb + i) ≤ W)
    (h4 : c.nmem (CPb + i) + Z + K + K + c.nmem (POTb + c.nmem (LABb + c.nmem (RVb + i))) ≤ W)
    (h5 : c.nmem (POTb + c.nmem (LABb + i)) + K ≤ W) :
    ∃ c' t, Exec P W flqBody c c' t ∧ t = 24 ∧ c'.nreg 9491 = i + 1 ∧
      c'.nmem = upd c.nmem (FLb + i) (flV c.nmem CPb RVb LABb POTb LNb Z K i) ∧
      (∀ r, (r < 9491 ∨ 9496 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := hb
  have hc' := hc
  unfold flqBody
  exec_block
  all_goals try ((try config_simp) <;>
    (try simp only [r34, r30, r05, r79, r77, r35, r21, r10, r36, r91]) <;>
    first | omega | exact Nat.le_trans (Nat.sub_le _ _) (by omega) |
      exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans (Nat.sub_le _ _) (by omega)))
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r34, r30, r05, r79, r77, r35, r21, r10, r36, r91])
  all_goals first | omega | rfl | (repeat rw [upd_other _ _ _ (by omega)])

set_option maxHeartbeats 1000000 in
theorem flP_execW (c : Config) (hc : WordsBounded W c) {m CPb RVb LABb POTb LNb FLb Z K G : ℕ}
    (r00 : c.nreg 9400 = m)
    (r34 : c.nreg 9434 = CPb) (r30 : c.nreg 9430 = RVb) (r05 : c.nreg 9405 = LABb)
    (r79 : c.nreg 9479 = POTb) (r77 : c.nreg 9477 = LNb) (r35 : c.nreg 9435 = FLb)
    (r21 : c.nreg 9421 = Z) (r10 : c.nreg 9310 = K) (r36 : c.nreg 9436 = 1)
    (hRV : ∀ i < m, c.nmem (RVb + i) < m) (hLAB : ∀ i < m, c.nmem (LABb + i) ≤ G)
    (hd : ∀ a, FLb ≤ a → a < FLb + m → ¬ (CPb ≤ a ∧ a < CPb + m) ∧ ¬ (RVb ≤ a ∧ a < RVb + m) ∧
      ¬ (LABb ≤ a ∧ a < LABb + m) ∧ ¬ (POTb ≤ a ∧ a < POTb + G + 1) ∧
      ¬ (LNb ≤ a ∧ a < LNb + m))
    (hb : CPb + m ≤ W ∧ RVb + m ≤ W ∧ LABb + m ≤ W ∧ LNb + m ≤ W ∧ FLb + m + 1 ≤ W ∧
      POTb + G + 1 ≤ W)
    (h4 : ∀ i < m, c.nmem (CPb + i) + Z + K + K +
      c.nmem (POTb + c.nmem (LABb + c.nmem (RVb + i))) ≤ W)
    (h5 : ∀ i < m, c.nmem (POTb + c.nmem (LABb + i)) + K ≤ W) :
    ∃ c' t, Exec P W flP c c' t ∧ t ≤ 26 * m + 3 ∧
      (∀ i < m, c'.nmem (FLb + i) = flV c.nmem CPb RVb LABb POTb LNb Z K i) ∧
      (∀ a, (a < FLb ∨ FLb + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9491 ∨ 9496 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := hb
  obtain ⟨c₁, k₁, e₁, hk₁, a91, ak, am, ar, arm, ao⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 9491 0]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 9491 = 0 ∧
      (∀ r, r ≠ 9491 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ i' < i, c'.nmem (FLb + i') = flV c.nmem CPb RVb LABb POTb LNb Z K i') ∧
    (∀ a, (a < FLb ∨ FLb + i ≤ a) → c'.nmem a = c.nmem a) ∧
    (∀ r, (r < 9491 ∨ 9496 < r) → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h91, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 9491) (b := 9400) (body := flqBody) J (lo := 0) (hi := m) (B := 24) c₁ e₁.wb_right a91
    (by rw [ak _ (by omega), r00]) (Nat.zero_le _)
    ⟨fun i hi => absurd hi (by omega), fun a _ => by rw [am], fun r hr => ak r (by omega), ar,
      arm, ao⟩
    (fun i c' _ hi hw h91 h00 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      -- every cell read is off `FL`, so it is unchanged
      have R : ∀ a, (¬ (FLb ≤ a ∧ a < FLb + m)) → c'.nmem a = c.nmem a := fun a ha =>
        j2 a (by omega)
      have nR : ∀ a, (CPb ≤ a ∧ a < CPb + m) ∨ (RVb ≤ a ∧ a < RVb + m) ∨
          (LABb ≤ a ∧ a < LABb + m) ∨ (POTb ≤ a ∧ a < POTb + G + 1) ∨ (LNb ≤ a ∧ a < LNb + m) →
          ¬ (FLb ≤ a ∧ a < FLb + m) := fun a ha hf => by
        have := hd a hf.1 hf.2; tauto
      have hr := hRV i hi
      have eR : c'.nmem (RVb + i) = c.nmem (RVb + i) := R _ (nR _ (by omega))
      have eLR : c'.nmem (LABb + c.nmem (RVb + i)) = c.nmem (LABb + c.nmem (RVb + i)) :=
        R _ (nR _ (by omega))
      have eLI : c'.nmem (LABb + i) = c.nmem (LABb + i) := R _ (nR _ (by omega))
      have hl1 := hLAB _ hr
      have hl2 := hLAB _ hi
      have ePR : c'.nmem (POTb + c.nmem (LABb + c.nmem (RVb + i))) =
          c.nmem (POTb + c.nmem (LABb + c.nmem (RVb + i))) := R _ (nR _ (by omega))
      have ePI : c'.nmem (POTb + c.nmem (LABb + i)) = c.nmem (POTb + c.nmem (LABb + i)) :=
        R _ (nR _ (by omega))
      have eC : c'.nmem (CPb + i) = c.nmem (CPb + i) := R _ (nR _ (by omega))
      have eL : c'.nmem (LNb + i) = c.nmem (LNb + i) := R _ (nR _ (by omega))
      have fV : flV c'.nmem CPb RVb LABb POTb LNb Z K i = flV c.nmem CPb RVb LABb POTb LNb Z K i :=
        by simp only [flV, eR, eLR, eLI, ePR, ePI, eC, eL]
      obtain ⟨c'', t, ex, htt, b91, bm, bk, br, brm, bo⟩ :=
        flqBody_execW (P := P) c' hw (CPb := CPb) (RVb := RVb) (LABb := LABb) (POTb := POTb)
          (LNb := LNb) (FLb := FLb) (Z := Z) (K := K)
          (by rw [j3 _ (by omega), r34]) (by rw [j3 _ (by omega), r30])
          (by rw [j3 _ (by omega), r05]) (by rw [j3 _ (by omega), r79])
          (by rw [j3 _ (by omega), r77]) (by rw [j3 _ (by omega), r35])
          (by rw [j3 _ (by omega), r21]) (by rw [j3 _ (by omega), r10])
          (by rw [j3 _ (by omega), r36]) h91 (by omega) (by rw [eR]; omega)
          (by rw [eR, eLR]; omega) (by rw [eLI]; omega)
          (by rw [eC, eR, eLR, ePR]; exact h4 i hi) (by rw [eLI, ePI]; exact h5 i hi)
      rw [fV] at bm
      refine ⟨c'', t, ex, htt.le, b91, by rw [bk _ (by omega)]; exact h00,
        fun i' hi' => ?_, fun a ha => ?_, fun r hr => by rw [bk r hr]; exact j3 r hr,
        by rw [br, j4], by rw [brm, j5], by rw [bo, j6]⟩
      · rw [bm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j1 i' h
        · rw [upd_same]
      · rw [bm, upd_other _ _ _ (by omega)]; exact j2 a (by omega))
  refine ⟨c₂, _, e₁.seq e₂, by rw [hk₁]; simp only [Nat.sub_zero] at hk₂; omega, j1, j2, j3,
    j4, j5, j6⟩

end BKMNW

end PlanarFlow
