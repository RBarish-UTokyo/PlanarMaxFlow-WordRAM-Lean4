module

public import PlanarFlow.BKMNW.Nf7cD

/-!
# The final step of `fixP`: the loops

The final step of FixConservationOnPath (after the `k` stages): the lengths
`ℓ = U − s.1` of the final negative-length call as words `LN[i] = ℓ (en i) + K`, the call, the
potential `χ` read from its outcome, and the flow `FL[i] = Z + (s.1 + cob χ)(en i)`. The loops
(registers `9477 … 9499`; `9477 = T` the base of `LN`):

* **`lnA`** (`lnA_exec`, `12 m + 3`): `LN[i] = CP[i] + Z + K − FLW[i]` (`= (U − f₀)(en i) + K`);
* **`lnB`** (`lnB_exec`, `19 k + 3`): for `l < k`, `t = PD[l]`: `LN[t] = CW[l] + 2K − FW[l]`,
  `LN[RV[t]] = CR[l] + FW[l]` (the darts of the path: `ℓ = U − s.1`); the memory is
  `lnBM … k` (the updates in order);
* **`potP`** (`potP_exec`, `9 w + 3`): `POT[ID[v] + 1] = VL[v]` for `v < w` (`potM`);
* **`flP`** (`flP_exec`, `26 m + 3`): `FL[i] = ((CP[i] + Z + 2K + POT[LAB[RV[i]]]) − LN[i]) −
  (POT[LAB[i]] + K)` (`flV`).
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

/-! ### `lnA` -/

/-- One step of `lnA`. -/
def lnABody : Stmt := block [.addN 9485 9434 9484, .loadN 9485 9485, .addN 9485 9485 9421,
  .addN 9485 9485 9310, .addN 9486 9435 9484, .loadN 9486 9486, .subN 9485 9485 9486,
  .addN 9486 9477 9484, .storeN 9486 9485, .addN 9484 9484 9436]

/-- **The lengths off the path**: `LN[i] = CP[i] + Z + K − FLW[i]`. -/
def lnA : Stmt := .seq (block [.constN 9484 0]) (.whileLtN 9484 9400 lnABody)

set_option maxHeartbeats 1000000 in
theorem lnABody_exec (c : Config) (hc : WordsBounded W c) {CPb FLWb Z K LNb i : ℕ}
    (r34 : c.nreg 9434 = CPb) (r35 : c.nreg 9435 = FLWb) (r21 : c.nreg 9421 = Z)
    (r10 : c.nreg 9310 = K) (r77 : c.nreg 9477 = LNb) (r36 : c.nreg 9436 = 1)
    (r84 : c.nreg 9484 = i) (hb : CPb + FLWb + LNb + i + 1 ≤ W)
    (hv : c.nmem (CPb + i) + Z + K ≤ W) :
    ∃ c' t, Exec P W lnABody c c' t ∧ t = 10 ∧ c'.nreg 9484 = i + 1 ∧
      c'.nmem = upd c.nmem (LNb + i) (c.nmem (CPb + i) + Z + K - c.nmem (FLWb + i)) ∧
      (∀ r, (r < 9484 ∨ 9486 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lnABody
  exec_block
  all_goals try ((try config_simp) <;> (try simp only [r34, r35, r21, r10, r77, r36, r84]) <;>
    first | omega | exact Nat.le_trans (Nat.sub_le _ _) (by omega))
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r34, r35, r21, r10, r77, r36, r84])
  all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

theorem lnA_exec (c : Config) (hc : WordsBounded W c) {m CPb FLWb Z K LNb : ℕ}
    (r00 : c.nreg 9400 = m) (r34 : c.nreg 9434 = CPb) (r35 : c.nreg 9435 = FLWb)
    (r21 : c.nreg 9421 = Z) (r10 : c.nreg 9310 = K) (r77 : c.nreg 9477 = LNb)
    (r36 : c.nreg 9436 = 1) (hd : CPb + m ≤ LNb ∧ FLWb + m ≤ LNb)
    (hb : CPb + FLWb + LNb + m + 1 ≤ W) (hv : ∀ i < m, c.nmem (CPb + i) + Z + K ≤ W) :
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
        lnABody_exec (P := P) c' hw (CPb := CPb) (FLWb := FLWb) (Z := Z) (K := K) (LNb := LNb)
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

/-! ### `lnB` -/

/-- The memory after `l` steps of `lnB`. -/
def lnBM (nm : ℕ → ℕ) (PDb RVb CWb CRb FWb LNb K : ℕ) : ℕ → ℕ → ℕ
  | 0 => nm
  | l + 1 => upd (upd (lnBM nm PDb RVb CWb CRb FWb LNb K l) (LNb + nm (PDb + l))
      (nm (CWb + l) + K + K - nm (FWb + l))) (LNb + nm (RVb + nm (PDb + l)))
      (nm (CRb + l) + nm (FWb + l))

lemma lnBM_out (nm : ℕ → ℕ) {PDb RVb CWb CRb FWb LNb K m l : ℕ}
    (hPD : ∀ l' < l, nm (PDb + l') < m) (hRV : ∀ i < m, nm (RVb + i) < m) {a : ℕ}
    (ha : a < LNb ∨ LNb + m ≤ a) : lnBM nm PDb RVb CWb CRb FWb LNb K l a = nm a := by
  induction l with
  | zero => rfl
  | succ l ih =>
    have h1 := hPD l (by omega)
    have h2 := hRV _ h1
    simp only [lnBM]
    rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
    exact ih fun l' hl' => hPD l' (by omega)

/-- One step of `lnB`. -/
def lnBBody : Stmt := block [.addN 9485 9402 9484, .loadN 9485 9485,
  .addN 9489 9430 9485, .loadN 9489 9489,
  .addN 9486 9374 9484, .loadN 9486 9486, .addN 9486 9486 9310, .addN 9486 9486 9310,
  .addN 9487 9376 9484, .loadN 9487 9487, .subN 9486 9486 9487,
  .addN 9490 9375 9484, .loadN 9490 9490, .addN 9490 9490 9487,
  .addN 9488 9477 9485, .storeN 9488 9486,
  .addN 9488 9477 9489, .storeN 9488 9490, .addN 9484 9484 9436]

/-- **The lengths on the darts of the path.** -/
def lnB : Stmt := .seq (block [.constN 9484 0]) (.whileLtN 9484 9401 lnBBody)

set_option maxHeartbeats 1600000 in
theorem lnBBody_exec (c : Config) (hc : WordsBounded W c) {PDb RVb CWb CRb FWb LNb K l : ℕ}
    (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = RVb) (r74 : c.nreg 9374 = CWb)
    (r75 : c.nreg 9375 = CRb) (r76 : c.nreg 9376 = FWb) (r77 : c.nreg 9477 = LNb)
    (r10 : c.nreg 9310 = K) (r36 : c.nreg 9436 = 1) (r84 : c.nreg 9484 = l)
    (hb : PDb + RVb + CWb + CRb + FWb + l + 1 ≤ W)
    (ht : LNb + c.nmem (PDb + l) + RVb ≤ W)
    (hr : LNb + c.nmem (RVb + c.nmem (PDb + l)) ≤ W)
    (hx : c.nmem (CWb + l) + K + K ≤ W) (hy : c.nmem (CRb + l) + c.nmem (FWb + l) ≤ W) :
    ∃ c' t, Exec P W lnBBody c c' t ∧ t = 19 ∧ c'.nreg 9484 = l + 1 ∧
      c'.nmem = upd (upd c.nmem (LNb + c.nmem (PDb + l))
        (c.nmem (CWb + l) + K + K - c.nmem (FWb + l)))
        (LNb + c.nmem (RVb + c.nmem (PDb + l))) (c.nmem (CRb + l) + c.nmem (FWb + l)) ∧
      (∀ r, (r < 9484 ∨ 9490 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
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

theorem lnB_exec (c : Config) (hc : WordsBounded W c) {k m PDb RVb CWb CRb FWb LNb K : ℕ}
    (r01 : c.nreg 9401 = k)
    (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = RVb) (r74 : c.nreg 9374 = CWb)
    (r75 : c.nreg 9375 = CRb) (r76 : c.nreg 9376 = FWb) (r77 : c.nreg 9477 = LNb)
    (r10 : c.nreg 9310 = K) (r36 : c.nreg 9436 = 1)
    (hPD : ∀ l < k, c.nmem (PDb + l) < m) (hRV : ∀ i < m, c.nmem (RVb + i) < m)
    (hd : PDb + k ≤ LNb ∧ RVb + m ≤ LNb ∧ CWb + k ≤ LNb ∧ CRb + k ≤ LNb ∧ FWb + k ≤ LNb)
    (hb : PDb + RVb + CWb + CRb + FWb + k + LNb + m + 1 ≤ W)
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
        lnBBody_exec (P := P) c' hw (PDb := PDb) (RVb := RVb) (CWb := CWb) (CRb := CRb)
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

/-! ### `potP` -/

/-- The memory after `v` steps of `potP`. -/
def potM (nm : ℕ → ℕ) (IDb VLb POTb : ℕ) : ℕ → ℕ → ℕ
  | 0 => nm
  | v + 1 => upd (potM nm IDb VLb POTb v) (POTb + nm (IDb + v) + 1) (nm (VLb + v))

lemma potM_out (nm : ℕ → ℕ) {IDb VLb POTb G v : ℕ} (hid : ∀ v' < v, nm (IDb + v') < G) {a : ℕ}
    (ha : a < POTb ∨ POTb + G + 1 ≤ a) : potM nm IDb VLb POTb v a = nm a := by
  induction v with
  | zero => rfl
  | succ v ih =>
    have h1 := hid v (by omega)
    simp only [potM]
    rw [upd_other _ _ _ (by omega)]
    exact ih fun v' hv' => hid v' (by omega)

/-- **The scattered values, when equal identifiers carry equal values.** -/
lemma potM_val (nm : ℕ → ℕ) {IDb VLb POTb v : ℕ}
    (hc : ∀ v' < v, ∀ v'' < v, nm (IDb + v') = nm (IDb + v'') → nm (VLb + v') = nm (VLb + v''))
    {u : ℕ} (hu : u < v) :
    potM nm IDb VLb POTb v (POTb + nm (IDb + u) + 1) = nm (VLb + u) := by
  induction v with
  | zero => omega
  | succ v ih =>
    simp only [potM, upd_apply]
    split_ifs with h
    · exact hc v (by omega) u hu (by omega)
    · exact ih (fun a ha b hb e => hc a (by omega) b (by omega) e)
        (by rcases Nat.lt_succ_iff_lt_or_eq.1 hu with h' | rfl
            · exact h'
            · exact absurd rfl h)

/-- One step of `potP`. -/
def potBody : Stmt := block [.addN 9492 9489 9491, .loadN 9492 9492, .addN 9493 9490 9491,
  .loadN 9493 9493, .addN 9494 9479 9492, .addN 9494 9494 9436, .storeN 9494 9493,
  .addN 9491 9491 9436]

/-- **The potentials by face label**: `POT[ID[v] + 1] = VL[v]` (`v < w = r9488`). -/
def potP : Stmt := .seq (block [.constN 9491 0]) (.whileLtN 9491 9488 potBody)

set_option maxHeartbeats 1000000 in
theorem potBody_exec (c : Config) (hc : WordsBounded W c) {IDb VLb POTb v : ℕ}
    (r89 : c.nreg 9489 = IDb) (r90 : c.nreg 9490 = VLb) (r79 : c.nreg 9479 = POTb)
    (r36 : c.nreg 9436 = 1) (r91 : c.nreg 9491 = v) (hb : IDb + VLb + v + 1 ≤ W)
    (hp : POTb + c.nmem (IDb + v) + 1 ≤ W) :
    ∃ c' t, Exec P W potBody c c' t ∧ t = 8 ∧ c'.nreg 9491 = v + 1 ∧
      c'.nmem = upd c.nmem (POTb + c.nmem (IDb + v) + 1) (c.nmem (VLb + v)) ∧
      (∀ r, (r < 9491 ∨ 9494 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hc' := hc
  unfold potBody
  exec_block
  all_goals try ((try config_simp) <;> (try simp only [r89, r90, r79, r36, r91]) <;> omega)
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r89, r90, r79, r36, r91])
  all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

theorem potP_exec (c : Config) (hc : WordsBounded W c) {w G IDb VLb POTb : ℕ}
    (r88 : c.nreg 9488 = w) (r89 : c.nreg 9489 = IDb) (r90 : c.nreg 9490 = VLb)
    (r79 : c.nreg 9479 = POTb) (r36 : c.nreg 9436 = 1)
    (hid : ∀ v < w, c.nmem (IDb + v) < G)
    (hd : (IDb + w ≤ POTb ∨ POTb + G + 1 ≤ IDb) ∧ (VLb + w ≤ POTb ∨ POTb + G + 1 ≤ VLb))
    (hb : IDb + VLb + w + POTb + G + 1 ≤ W) :
    ∃ c' t, Exec P W potP c c' t ∧ t ≤ 10 * w + 3 ∧
      c'.nmem = potM c.nmem IDb VLb POTb w ∧
      (∀ r, (r < 9491 ∨ 9494 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
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
        potBody_exec (P := P) c' hw (IDb := IDb) (VLb := VLb) (POTb := POTb)
          (by rw [j3 _ (by omega), r89]) (by rw [j3 _ (by omega), r90])
          (by rw [j3 _ (by omega), r79]) (by rw [j3 _ (by omega), r36]) h91 (by omega)
          (by rw [eI]; omega)
      rw [eI, eV, j1] at bm
      exact ⟨c'', t, ex, htt.le, b91, by rw [bk _ (by omega)]; exact h88, bm,
        fun r hr => by rw [bk r hr]; exact j3 r hr, by rw [br, j4], by rw [brm, j5],
        by rw [bo, j6]⟩)
  refine ⟨c₂, _, e₁.seq e₂, by rw [hk₁]; simp only [Nat.sub_zero] at hk₂; omega, j1, j3, j4, j5,
    j6⟩

/-! ### `flP` -/

/-- The flow word of the frame dart `i`. -/
def flV (nm : ℕ → ℕ) (CPb RVb LABb POTb LNb Z K i : ℕ) : ℕ :=
  (nm (CPb + i) + Z + K + K + nm (POTb + nm (LABb + nm (RVb + i))) - nm (LNb + i)) -
    (nm (POTb + nm (LABb + i)) + K)

/-- One step of `flP`. -/
def flqBody : Stmt := block [.addN 9492 9430 9491, .loadN 9492 9492, .addN 9492 9405 9492,
  .loadN 9492 9492, .addN 9492 9479 9492, .loadN 9492 9492,
  .addN 9493 9434 9491, .loadN 9493 9493, .addN 9493 9493 9421, .addN 9493 9493 9310,
  .addN 9493 9493 9310, .addN 9493 9493 9492,
  .addN 9494 9477 9491, .loadN 9494 9494, .subN 9493 9493 9494,
  .addN 9495 9405 9491, .loadN 9495 9495, .addN 9495 9479 9495, .loadN 9495 9495,
  .addN 9495 9495 9310, .subN 9493 9493 9495,
  .addN 9496 9435 9491, .storeN 9496 9493, .addN 9491 9491 9436]

/-- **The final flow**: `FL[i] = flV …` for `i < m`. -/
def flP : Stmt := .seq (block [.constN 9491 0]) (.whileLtN 9491 9400 flqBody)

set_option maxHeartbeats 2000000 in
theorem flqBody_exec (c : Config) (hc : WordsBounded W c) {CPb RVb LABb POTb LNb FLb Z K i : ℕ}
    (r34 : c.nreg 9434 = CPb) (r30 : c.nreg 9430 = RVb) (r05 : c.nreg 9405 = LABb)
    (r79 : c.nreg 9479 = POTb) (r77 : c.nreg 9477 = LNb) (r35 : c.nreg 9435 = FLb)
    (r21 : c.nreg 9421 = Z) (r10 : c.nreg 9310 = K) (r36 : c.nreg 9436 = 1)
    (r91 : c.nreg 9491 = i) (hb : CPb + RVb + LABb + LNb + FLb + i + 1 ≤ W)
    (h1 : LABb + c.nmem (RVb + i) ≤ W)
    (h2 : POTb + c.nmem (LABb + c.nmem (RVb + i)) ≤ W)
    (h3 : POTb + c.nmem (LABb + i) ≤ W)
    (h4 : c.nmem (CPb + i) + Z + K + K + c.nmem (POTb + c.nmem (LABb + c.nmem (RVb + i))) ≤ W)
    (h5 : c.nmem (POTb + c.nmem (LABb + i)) + K ≤ W) :
    ∃ c' t, Exec P W flqBody c c' t ∧ t = 24 ∧ c'.nreg 9491 = i + 1 ∧
      c'.nmem = upd c.nmem (FLb + i) (flV c.nmem CPb RVb LABb POTb LNb Z K i) ∧
      (∀ r, (r < 9491 ∨ 9496 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
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

theorem flP_exec (c : Config) (hc : WordsBounded W c) {m CPb RVb LABb POTb LNb FLb Z K G : ℕ}
    (r00 : c.nreg 9400 = m)
    (r34 : c.nreg 9434 = CPb) (r30 : c.nreg 9430 = RVb) (r05 : c.nreg 9405 = LABb)
    (r79 : c.nreg 9479 = POTb) (r77 : c.nreg 9477 = LNb) (r35 : c.nreg 9435 = FLb)
    (r21 : c.nreg 9421 = Z) (r10 : c.nreg 9310 = K) (r36 : c.nreg 9436 = 1)
    (hRV : ∀ i < m, c.nmem (RVb + i) < m) (hLAB : ∀ i < m, c.nmem (LABb + i) ≤ G)
    (hd : ∀ a, FLb ≤ a → a < FLb + m → ¬ (CPb ≤ a ∧ a < CPb + m) ∧ ¬ (RVb ≤ a ∧ a < RVb + m) ∧
      ¬ (LABb ≤ a ∧ a < LABb + m) ∧ ¬ (POTb ≤ a ∧ a < POTb + G + 1) ∧
      ¬ (LNb ≤ a ∧ a < LNb + m))
    (hb : CPb + RVb + LABb + LNb + FLb + m + POTb + G + 1 ≤ W)
    (h4 : ∀ i < m, c.nmem (CPb + i) + Z + K + K +
      c.nmem (POTb + c.nmem (LABb + c.nmem (RVb + i))) ≤ W)
    (h5 : ∀ i < m, c.nmem (POTb + c.nmem (LABb + i)) + K ≤ W) :
    ∃ c' t, Exec P W flP c c' t ∧ t ≤ 26 * m + 3 ∧
      (∀ i < m, c'.nmem (FLb + i) = flV c.nmem CPb RVb LABb POTb LNb Z K i) ∧
      (∀ a, (a < FLb ∨ FLb + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9491 ∨ 9496 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
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
        flqBody_exec (P := P) c' hw (CPb := CPb) (RVb := RVb) (LABb := LABb) (POTb := POTb)
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
