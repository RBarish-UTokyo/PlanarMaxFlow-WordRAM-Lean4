module

public import PlanarFlow.BKMNW.Nf7aP2

/-!
# Per-address word bounds for the prologue, part 1

Copies of `pinA_exec`, `proP1a_exec`, `fmkProg_exec`, `cwProg_exec`, `cwProg_exec'`, `proP2_exec`
(suffix `W`) whose word-bound hypotheses bound each address separately (a conjunction of
`base + offset ≤ W`, or a single top `Top + c ≤ W` given the layout hypotheses) instead of a sum of
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
theorem pinA_execW (c : Config) (hc : WordsBounded W c) {d A0 Gb j m Z ns off k : ℕ}
    (r04 : c.nreg 3004 = d) (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = Gb)
    (r00 : c.nreg 6800 = j) (hm : c.nmem d = m) (hZ : c.nmem (d + 3) = Z)
    (hns : c.nmem Gb = ns) (hoff : c.nmem (Gb + 1 + j) = off) (hk : c.nmem (Gb + 1 + j + ns) = k)
    (hW : d + 6 * m + 8 ≤ W ∧ Gb + 1 + j + ns ≤ W ∧ Gb + 1 + ns + ns + off ≤ W) :
    ∃ c' t, Exec P W pinA c c' t ∧ t = 24 ∧ c'.nreg 9400 = m ∧ c'.nreg 9403 = A0 ∧
      c'.nreg 9436 = 1 ∧ c'.nreg 9421 = Z ∧ c'.nreg 9401 = k ∧ c'.nreg 9371 = k ∧
      c'.nreg 9402 = Gb + 1 + ns + ns + off ∧ c'.nreg 9430 = d + 4 + m ∧
      c'.nreg 9431 = d + 4 + m + m ∧ c'.nreg 9434 = d + 4 + m + m + m ∧
      c'.nreg 9435 = d + 4 + m + m + m + m + m + m ∧
      (∀ r, r ≠ 9371 → (r < 9400 ∨ 9438 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hWa, hWb, hWc⟩ := hW
  unfold pinA
  exec_block
  all_goals try ((try config_simp) <;>
    (try simp only [r04, r06, r07, r00, hm, hZ, hns, hoff, hk]) <;> omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r04, r06, r07, r00, hm, hZ, hns, hoff, hk])
  all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

set_option maxHeartbeats 1600000 in
theorem proP1a_execW (p : FpIn) (c : Config) (hc : WordsBounded W c) {A0 j : ℕ}
    (r04 : c.nreg 3004 = p.d) (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = p.Gb)
    (r00 : c.nreg 6800 = j)
    (hm : c.nmem p.d = p.m) (hZ : c.nmem (p.d + 3) = p.Z) (hns : c.nmem p.Gb = p.ns)
    (hoff : c.nmem (p.Gb + 1 + j) = p.off) (hk : c.nmem (p.Gb + 1 + j + p.ns) = p.k)
    (hW1 : A0 + 9 * p.m + 15 * p.k + 1 ≤ W ∧ p.d + 6 * p.m + 8 ≤ W ∧
      p.Gb + 1 + j + p.ns ≤ W ∧ p.Gb + 1 + p.ns + p.ns + p.off ≤ W) :
    ∃ c' t, Exec P W proP1a c c' t ∧ t = 63 ∧ RegP1 p A0 c' ∧
      c'.nreg 5030 = 3 * p.m + 1 ∧ c'.nreg 5031 = A0 + p.m ∧ c'.nreg 4470 = p.m ∧
      c'.nreg 4471 = p.d + 4 + p.m ∧ c'.nreg 4472 = p.d + 4 + p.m + p.m ∧ c'.nreg 4473 = A0 ∧
      c'.nreg 7350 = A0 ∧ c'.nreg 7351 = A0 + p.m ∧ c'.nreg 7352 = p.m ∧
      c'.nreg 8430 = A0 + p.m + p.m + p.m + p.m + 1 ∧
      (∀ r, ¬ scr1 r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hWa, hWb, hWc, hWd⟩ := hW1
  obtain ⟨c₁, t₁, e₁, ht₁, a00, a03, a36, a21, a01, a71, a02, a30, a31, a34, a35, ak, am, ar,
      arm, ao⟩ := pinA_execW (P := P) c hc r04 r06 r07 r00 hm hZ hns hoff hk ⟨hWb, hWc, hWd⟩
  obtain ⟨c₂, t₂, e₂, ht₂, b04, b05, b06, b07, b08, b09, b10, b11, b74, b75, b76, b77, b12, b13,
      b14, b15, b16, b17, b18, bk, bm, br, brm, bo⟩ :=
    pinB_exec (P := P) c₁ e₁.wb_right a03 a00 a01 a36 (by omega)
  have q2 : ∀ r, (r < 9374 ∨ 9377 < r) → (r < 9404 ∨ 9418 < r) → c₂.nreg r = c₁.nreg r := bk
  obtain ⟨c₃, t₃, e₃, ht₃, d5030, d5031, d4470, d4471, d4472, d4473, d7350, d7351, d7352, d8430,
      dk, dm, dr, drm, do'⟩ :=
    pinC_exec (P := P) c₂ e₂.wb_right (m := p.m) (by rw [q2 _ (by omega) (by omega), a00])
      (by rw [q2 _ (by omega) (by omega), a36]) (by omega)
  have q3 : ∀ r, (r = 9371 ∨ (9374 ≤ r ∧ r ≤ 9377) ∨ (9400 ≤ r ∧ r ≤ 9438)) →
      c₃.nreg r = c₂.nreg r := fun r hr => dk r (by omega) (by omega) (by omega) (by omega)
        (by omega)
  have R2 : RegP1 p A0 c₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first | assumption | (rw [q2 _ (by omega) (by omega)]; assumption)
  refine ⟨c₃, _, e₁.seq (e₂.seq e₃), by omega, R2.congr fun r hr _ _ _ => q3 r hr, d5030, by rw [d5031, b05], d4470,
    by rw [d4471, q2 _ (by omega) (by omega), a30], by rw [d4472, q2 _ (by omega) (by omega), a31],
    by rw [d4473, b04], by rw [d7350, b04], by rw [d7351, b05], d7352, by rw [d8430, b08],
    fun r hr => ?_, by rw [dm, bm, am], by rw [dr, br, ar], by rw [drm, brm, arm],
    by rw [do', bo, ao]⟩
  simp only [scr1] at hr
  rw [dk r (by omega) (by omega) (by omega) (by omega) (by omega), q2 r (by omega) (by omega),
    ak r (by omega) (by omega)]

/-- **The marks on the machine**: from the dart indices `PD[l] < m` (`l < k`), the reverses
`RV[i] < m` and the labels `FL[i] ≤ m` (`i < m`), the regions `[ON, ON + m)` and `[MK, MK + m]`
disjoint from each other and from the read arrays: within `19 k + 3` steps the marks
`ON[i] = fmk2 ON₀ PD RP k i` (`i < m`) and `MK[a] = fmk2 MK₀ FT FR k a` (`a ≤ m`), all other
memory kept. -/
theorem fmkProg_execW (c : Config) (hc : WordsBounded W c) {k m PDb RVb FLb ONb MKb : ℕ}
    (r01 : c.nreg 9401 = k) (r02 : c.nreg 9402 = PDb) (r05 : c.nreg 9405 = FLb)
    (r06 : c.nreg 9406 = ONb) (r07 : c.nreg 9407 = MKb) (r30 : c.nreg 9430 = RVb)
    (r36 : c.nreg 9436 = 1)
    (hPD : ∀ l < k, c.nmem (PDb + l) < m) (hRV : ∀ i < m, c.nmem (RVb + i) < m)
    (hFL : ∀ i < m, c.nmem (FLb + i) ≤ m)
    (dW : ∀ a, (ONb ≤ a ∧ a < ONb + m) ∨ (MKb ≤ a ∧ a ≤ MKb + m) →
      (a < PDb ∨ PDb + k ≤ a) ∧ (a < RVb ∨ RVb + m ≤ a) ∧ (a < FLb ∨ FLb + m ≤ a))
    (dOM : ONb + m ≤ MKb ∨ MKb + m < ONb)
    (hW : PDb + k ≤ W ∧ RVb + m ≤ W ∧ FLb + m ≤ W ∧ ONb + m ≤ W ∧ MKb + m ≤ W ∧
      k + 1 ≤ W) :
    ∃ c' t, Exec P W fmkProg c c' t ∧ t ≤ 19 * k + 3 ∧
      (∀ i < m, c'.nmem (ONb + i) = fmk2 (fun i => c.nmem (ONb + i)) (fun l => c.nmem (PDb + l))
      (fun l => c.nmem (RVb + c.nmem (PDb + l))) k i) ∧
      (∀ a ≤ m, c'.nmem (MKb + a) = fmk2 (fun a => c.nmem (MKb + a))
        (fun l => c.nmem (FLb + c.nmem (PDb + l)))
      (fun l => c.nmem (FLb + c.nmem (RVb + c.nmem (PDb + l)))) k a) ∧
      (∀ a, ¬ (ONb ≤ a ∧ a < ONb + m) → ¬ (MKb ≤ a ∧ a ≤ MKb + m) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9450 ∨ 9455 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hWa, hWb, hWc, hWd, hWe, hWf⟩ := hW
  obtain ⟨c₁, k₁, e₁, hk₁, a50, ak, am, ar, arm, ao⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 9450 0]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 9450 = 0 ∧
      (∀ r, r ≠ 9450 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  have hRP : ∀ l < k, c.nmem (RVb + c.nmem (PDb + l)) < m := fun l hl => hRV _ (hPD l hl)
  let J : ℕ → Config → Prop := fun l c' =>
    (∀ i < m, c'.nmem (ONb + i) = fmk2 (fun i => c.nmem (ONb + i)) (fun l => c.nmem (PDb + l))
      (fun l => c.nmem (RVb + c.nmem (PDb + l))) l i) ∧
    (∀ a ≤ m, c'.nmem (MKb + a) = fmk2 (fun a => c.nmem (MKb + a))
      (fun l => c.nmem (FLb + c.nmem (PDb + l)))
      (fun l => c.nmem (FLb + c.nmem (RVb + c.nmem (PDb + l)))) l a) ∧
    (∀ a, ¬ (ONb ≤ a ∧ a < ONb + m) → ¬ (MKb ≤ a ∧ a ≤ MKb + m) → c'.nmem a = c.nmem a) ∧
    (∀ r, (r < 9450 ∨ 9455 < r) → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h50, j1, j2, j3, j4, j5, j6, j7⟩ := tgRange (P := P)
    (a := 9450) (b := 9401) (body := fmkBody) J (lo := 0) (hi := k) (B := 17) c₁ e₁.wb_right a50
    (by rw [ak _ (by omega), r01]) (Nat.zero_le _)
    ⟨fun i _ => by rw [am]; rfl, fun a _ => by rw [am]; rfl, fun a _ _ => by rw [am],
      fun r hr => ak r (by omega), ar, arm, ao⟩
    (fun l c' _ hl hw h50 h01 ⟨j1, j2, j3, j4, j5, j6, j7⟩ => by
      have ePD : c'.nmem (PDb + l) = c.nmem (PDb + l) :=
        j3 _ (fun h => by have := (dW _ (Or.inl h)).1; omega)
          (fun h => by have := (dW _ (Or.inr h)).1; omega)
      have ht := hPD l hl
      have hr := hRP l hl
      have eRV : c'.nmem (RVb + c.nmem (PDb + l)) = c.nmem (RVb + c.nmem (PDb + l)) :=
        j3 _ (fun h => by have := (dW _ (Or.inl h)).2.1; omega)
          (fun h => by have := (dW _ (Or.inr h)).2.1; omega)
      have eFT : c'.nmem (FLb + c.nmem (PDb + l)) = c.nmem (FLb + c.nmem (PDb + l)) :=
        j3 _ (fun h => by have := (dW _ (Or.inl h)).2.2; omega)
          (fun h => by have := (dW _ (Or.inr h)).2.2; omega)
      have eFR : c'.nmem (FLb + c.nmem (RVb + c.nmem (PDb + l))) =
          c.nmem (FLb + c.nmem (RVb + c.nmem (PDb + l))) :=
        j3 _ (fun h => by have := (dW _ (Or.inl h)).2.2; omega)
          (fun h => by have := (dW _ (Or.inr h)).2.2; omega)
      have hft := hFL _ ht
      have hfr := hFL _ hr
      obtain ⟨c'', t, ex, htt, b50, bm, bk, br, brm, bo⟩ :=
        fmkBody_exec (P := P) c' hw (PDb := PDb) (RVb := RVb) (FLb := FLb) (ONb := ONb)
          (MKb := MKb) (l := l) (by rw [j4 _ (by omega), r02])
          (by rw [j4 _ (by omega), r05])
          (by rw [j4 _ (by omega), r06])
          (by rw [j4 _ (by omega), r07])
          (by rw [j4 _ (by omega), r30])
          (by rw [j4 _ (by omega), r36]) h50
          (by omega) (by rw [ePD]; omega) (by rw [ePD]; omega) (by rw [ePD, eRV]; omega)
          (by rw [ePD]; omega) (by rw [ePD, eRV]; omega) (by rw [ePD, eFT]; omega)
          (by rw [ePD, eRV, eFR]; omega) (by omega)
      rw [ePD, eRV, eFT, eFR] at bm
      refine ⟨c'', t, ex, htt.le, b50, by rw [bk _ (by omega)]; exact h01,
        fun i hi => ?_, fun a ha => ?_, fun a h1 h2 => ?_, fun r hr => by rw [bk r hr]; exact j4 r hr,
        by rw [br, j5], by rw [brm, j6], by rw [bo, j7]⟩
      · rw [bm]
        have d1 := dOM
        simp only [upd_apply, fmk2]
        rw [← j1 i hi]
        split_ifs <;> first | rfl | omega
      · rw [bm]
        have d1 := dOM
        simp only [upd_apply, fmk2]
        rw [← j2 a ha]
        split_ifs <;> first | rfl | omega
      · rw [bm]
        simp only [upd_apply]
        split_ifs <;> first | omega | exact j3 a h1 h2)
  refine ⟨c₂, _, e₁.seq e₂, by rw [hk₁]; simp only [Nat.sub_zero] at hk₂; omega, j1, j2, j3,
    fun r hr => by rw [j4 r hr], j5, j6, j7⟩

/-- **The corner walk on the machine.** The labels `FL[i] ≤ m`, the next indices `NX[i]`,
`SG[i] < m` (`i < m`), the marks in `[MK, MK + m]`, the corners in `[BT, BT + m)`, the arrays
`NX`, `SG`, `ON`, `FL` and the start disjoint from the two written regions, `N ≤ m`. -/
theorem cwProg_execW (c : Config) (hc : WordsBounded W c)
    {N m NXb SGb ONb FLb MKb BTb t₀b : ℕ}
    (r00 : c.nreg 9400 = N) (r02 : c.nreg 9402 = t₀b) (r04 : c.nreg 9404 = NXb)
    (r05 : c.nreg 9405 = FLb) (r06 : c.nreg 9406 = ONb) (r07 : c.nreg 9407 = MKb)
    (r10 : c.nreg 9410 = BTb) (r31 : c.nreg 9431 = SGb) (hNm : N ≤ m)
    (ht₀ : c.nmem t₀b < m) (hMK : ∀ a ≤ m, c.nmem (MKb + a) ≤ 1)
    (hFL : ∀ i < m, c.nmem (FLb + i) ≤ m) (hNX : ∀ i < m, c.nmem (NXb + i) < m)
    (hSG : ∀ i < m, c.nmem (SGb + i) < m)
    (dMK : ∀ a, MKb ≤ a → a ≤ MKb + m → (a < FLb ∨ FLb + m ≤ a) ∧ (a < ONb ∨ ONb + m ≤ a) ∧
      (a < NXb ∨ NXb + m ≤ a) ∧ (a < SGb ∨ SGb + m ≤ a) ∧ a ≠ t₀b)
    (dBT : ∀ a, BTb ≤ a → a < BTb + m → (a < FLb ∨ FLb + m ≤ a) ∧ (a < ONb ∨ ONb + m ≤ a) ∧
      (a < NXb ∨ NXb + m ≤ a) ∧ (a < SGb ∨ SGb + m ≤ a) ∧ (a < MKb ∨ MKb + m < a))
    (hW : FLb + m ≤ W ∧ MKb + m ≤ W ∧ ONb + m ≤ W ∧ NXb + m ≤ W ∧ SGb + m ≤ W ∧
      BTb + m ≤ W ∧ m + 3 ≤ W) :
    let tt : ℕ → ℕ := fun n => (twF NXb SGb ONb c.nmem)^[n] (c.nmem t₀b)
    let g : ℕ → ℕ := fun n => c.nmem (FLb + tt n)
    let mk0 : ℕ → ℕ := fun a => if a ≤ m then c.nmem (MKb + a) else 0
    ∃ c' k, Exec P W cwProg c c' k ∧ k ≤ 26 * N + 10 ∧
      c'.nreg 9441 = tt N ∧ c'.nreg 9442 = (cwRun g tt mk0 N).cnt ∧
      (∀ a ≤ m, c'.nmem (MKb + a) = (cwRun g tt mk0 N).mks a) ∧
      (∀ x < (cwRun g tt mk0 N).cnt, c'.nmem (BTb + x) = (cwRun g tt mk0 N).bt x) ∧
      (∀ a, ¬ (MKb ≤ a ∧ a ≤ MKb + m) → ¬ (BTb ≤ a ∧ a < BTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9439 ∨ 9449 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  intro tt g mk0
  obtain ⟨hWa, hWb, hWc, hWd, hWe, hWf, hWg⟩ := hW
  obtain ⟨c₁, k₁, e₁, hk₁, a40, a41, a42, a43, a44, a45, ak, am, ar, arm, ao⟩ : ∃ c₁ k₁,
      Exec P W cwInit c c₁ k₁ ∧ k₁ = 6 ∧ c₁.nreg 9440 = 0 ∧ c₁.nreg 9441 = c.nmem t₀b ∧
      c₁.nreg 9442 = 0 ∧ c₁.nreg 9443 = 1 ∧ c₁.nreg 9444 = 2 ∧ c₁.nreg 9445 = 0 ∧
      (∀ r, (r < 9440 ∨ 9445 < r) → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold cwInit
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r02])
    simp only [upd_apply]; split_ifs <;> omega
  have q1 : ∀ r, (r < 9440 ∨ 9445 < r) → c₁.nreg r = c.nreg r := ak
  -- the iterates stay below `m`
  have htt : ∀ n, tt n < m := by
    intro n
    induction n with
    | zero => exact ht₀
    | succ n ih =>
      show (twF NXb SGb ONb c.nmem)^[n + 1] (c.nmem t₀b) < m
      rw [Function.iterate_succ_apply']
      unfold twF
      split_ifs
      · exact hNX _ ih
      · exact hSG _ ih
  have hg : ∀ n, g n ≤ m := fun n => hFL _ (htt n)
  let J : ℕ → Config → Prop := fun n c' =>
    c'.nreg 9441 = tt n ∧ c'.nreg 9442 = (cwRun g tt mk0 n).cnt ∧
    (∀ a ≤ m, c'.nmem (MKb + a) = (cwRun g tt mk0 n).mks a) ∧
    (∀ x < (cwRun g tt mk0 n).cnt, c'.nmem (BTb + x) = (cwRun g tt mk0 n).bt x) ∧
    (∀ a, ¬ (MKb ≤ a ∧ a ≤ MKb + m) → ¬ (BTb ≤ a ∧ a < BTb + m) → c'.nmem a = c.nmem a) ∧
    (∀ r, (r < 9440 ∨ 9441 < r) → (r < 9446 ∨ 9449 < r) → r ≠ 9439 → r ≠ 9442 →
      c'.nreg r = c₁.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have hJ0 : J 0 c₁ := by
    refine ⟨a41, a42, fun a ha => ?_, fun x hx => absurd hx (by simp [cwRun]), fun a _ _ => by
      rw [am], fun _ _ _ _ _ => rfl, ar, arm, ao⟩
    simp only [cwRun, mk0, ha, ↓reduceIte, am]
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h40, j1, j2, j3, j4, j5, j6, j7, j8, j9⟩ := tgRange (P := P)
    (a := 9440) (b := 9400) (body := cwBody) J (lo := 0) (hi := N) (B := 24) c₁ e₁.wb_right a40
    (by rw [q1 _ (by omega), r00]) (Nat.zero_le _) hJ0
    (fun n c' _ hn hw h40 h00 ⟨j1, j2, j3, j4, j5, j6, j7, j8, j9⟩ => by
      have f : ∀ r, (r < 9439 ∨ 9449 < r) → r ≠ 9440 → r ≠ 9441 → c'.nreg r = c.nreg r :=
        fun r h1 h2 h3 => by rw [j6 r (by omega) (by omega) (by omega) (by omega),
          q1 r (by omega)]
      have g43 : c'.nreg 9443 = 1 := by
        rw [j6 _ (by omega) (by omega) (by omega) (by omega), a43]
      have g44 : c'.nreg 9444 = 2 := by
        rw [j6 _ (by omega) (by omega) (by omega) (by omega), a44]
      have g45 : c'.nreg 9445 = 0 := by
        rw [j6 _ (by omega) (by omega) (by omega) (by omega), a45]
      have ht := htt n
      set s := cwRun g tt mk0 n with hs
      have hI := cwRun_inv g tt mk0 (fun a => by
        simp only [mk0]; split_ifs with ha
        · exact hMK a ha
        · omega) n
      rw [← hs] at hI
      have hcnt : s.cnt ≤ n := hI.cnt_le
      -- the reads
      have eFL : c'.nmem (FLb + tt n) = g n :=
        j5 _ (fun h => by have := dMK _ h.1 h.2; omega) (fun h => by have := dBT _ h.1 h.2; omega)
      have eON : c'.nmem (ONb + tt n) = c.nmem (ONb + tt n) :=
        j5 _ (fun h => by have := dMK _ h.1 h.2; omega) (fun h => by have := dBT _ h.1 h.2; omega)
      have eNX : c'.nmem (NXb + tt n) = c.nmem (NXb + tt n) :=
        j5 _ (fun h => by have := dMK _ h.1 h.2; omega) (fun h => by have := dBT _ h.1 h.2; omega)
      have eSG : c'.nmem (SGb + tt n) = c.nmem (SGb + tt n) :=
        j5 _ (fun h => by have := dMK _ h.1 h.2; omega) (fun h => by have := dBT _ h.1 h.2; omega)
      have eMK : c'.nmem (MKb + g n) = s.mks (g n) := j3 _ (hg n)
      obtain ⟨c'', t, ex, hk, b40, b41, b42, bm, bk, br, brm, bo⟩ :=
        cwBody_exec (P := P) c' hw (NXb := NXb) (SGb := SGb) (ONb := ONb) (FLb := FLb)
          (MKb := MKb) (BTb := BTb) (n := n) (t := tt n) (cnt := s.cnt)
          (by rw [f _ (by omega) (by omega) (by omega), r04])
          (by rw [f _ (by omega) (by omega) (by omega), r05])
          (by rw [f _ (by omega) (by omega) (by omega), r06])
          (by rw [f _ (by omega) (by omega) (by omega), r07])
          (by rw [f _ (by omega) (by omega) (by omega), r10])
          (by rw [f _ (by omega) (by omega) (by omega), r31]) h40 j1 j2 g43 g44 g45
          (by omega) (by rw [eFL]; have := hg n; omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)
      rw [eFL, eMK] at b42 bm
      have hstep : cwRun g tt mk0 (n + 1) = cwStep (g n) (tt n) n s := rfl
      refine ⟨c'', t, ex, hk, b40, by rw [bk _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h00, ?_⟩
      refine ⟨?_, ?_, fun a ha => ?_, fun x hx => ?_, fun a h1 h2 => ?_,
        fun r h1 h2 h3 h4 => ?_, by rw [br, j7], by rw [brm, j8], by rw [bo, j9]⟩
      · rw [b41]
        show twF NXb SGb ONb c'.nmem (tt n) = (twF NXb SGb ONb c.nmem)^[n + 1] (c.nmem t₀b)
        rw [Function.iterate_succ_apply']
        show twF NXb SGb ONb c'.nmem (tt n) = twF NXb SGb ONb c.nmem (tt n)
        unfold twF; rw [eON, eNX, eSG]
      · rw [b42, hstep]; unfold cwStep
        split_ifs <;> rfl
      · rw [bm, hstep]; unfold cwStep
        by_cases hv : s.mks (g n) = 1
        · simp only [hv, ↓reduceIte]
          rw [upd_other _ _ _ (fun h => by
            have := dBT (BTb + s.cnt) (by omega) (by omega); omega)]
          by_cases hag : a = g n
          · subst hag; rw [upd_same]; simp
          · rw [upd_other _ _ _ (by omega), j3 a ha]; simp [hag]
        · simp only [hv, ↓reduceIte]; exact j3 a ha
      · rw [bm, hstep]; unfold cwStep
        rw [hstep] at hx; unfold cwStep at hx
        by_cases hv : s.mks (g n) = 1
        · simp only [hv, ↓reduceIte] at hx ⊢
          by_cases hxc : x = s.cnt
          · subst hxc; rw [upd_same]; simp
          · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (fun h => by
              have := dBT (BTb + x) (by omega) (by omega); have := hg n; omega), j4 x (by omega)]
            simp [hxc]
        · simp only [hv, ↓reduceIte] at hx ⊢; exact j4 x hx
      · rw [bm]
        split_ifs
        · rw [upd_other _ _ _ (fun h => h2 ⟨by omega, by omega⟩),
            upd_other _ _ _ (fun h => h1 ⟨by omega, by have := hg n; omega⟩)]
          exact j5 a h1 h2
        · exact j5 a h1 h2
      · rw [bk r (by omega) (by omega) (by omega) h4 (by omega)]; exact j6 r h1 h2 h3 h4)
  refine ⟨c₂, _, e₁.seq e₂, by rw [hk₁]; simp only [Nat.sub_zero] at hk₂; omega, j1, j2, j3, j4, j5, fun r hr => ?_, j7, j8,
    j9⟩
  rcases Nat.lt_or_ge r 9440 with h | h
  · rw [j6 r (Or.inl h) (by omega) (by omega) (by omega), q1 r (Or.inl h)]
  · rw [j6 r (by omega) (by omega) (by omega) (by omega), q1 r (by omega)]

/-- `cwProg_execW` with the model functions given by equations. -/
theorem cwProg_execW' (c : Config) (hc : WordsBounded W c)
    {N m NXb SGb ONb FLb MKb BTb t₀b : ℕ}
    (r00 : c.nreg 9400 = N) (r02 : c.nreg 9402 = t₀b) (r04 : c.nreg 9404 = NXb)
    (r05 : c.nreg 9405 = FLb) (r06 : c.nreg 9406 = ONb) (r07 : c.nreg 9407 = MKb)
    (r10 : c.nreg 9410 = BTb) (r31 : c.nreg 9431 = SGb) (hNm : N ≤ m)
    (ht₀ : c.nmem t₀b < m) (hMK : ∀ a ≤ m, c.nmem (MKb + a) ≤ 1)
    (hFL : ∀ i < m, c.nmem (FLb + i) ≤ m) (hNX : ∀ i < m, c.nmem (NXb + i) < m)
    (hSG : ∀ i < m, c.nmem (SGb + i) < m)
    (dMK : ∀ a, MKb ≤ a → a ≤ MKb + m → (a < FLb ∨ FLb + m ≤ a) ∧ (a < ONb ∨ ONb + m ≤ a) ∧
      (a < NXb ∨ NXb + m ≤ a) ∧ (a < SGb ∨ SGb + m ≤ a) ∧ a ≠ t₀b)
    (dBT : ∀ a, BTb ≤ a → a < BTb + m → (a < FLb ∨ FLb + m ≤ a) ∧ (a < ONb ∨ ONb + m ≤ a) ∧
      (a < NXb ∨ NXb + m ≤ a) ∧ (a < SGb ∨ SGb + m ≤ a) ∧ (a < MKb ∨ MKb + m < a))
    (hW : FLb + m ≤ W ∧ MKb + m ≤ W ∧ ONb + m ≤ W ∧ NXb + m ≤ W ∧ SGb + m ≤ W ∧
      BTb + m ≤ W ∧ m + 3 ≤ W)
    {tt g mk0 : ℕ → ℕ} (htt : ∀ n, tt n = (twF NXb SGb ONb c.nmem)^[n] (c.nmem t₀b))
    (hg : ∀ n, g n = c.nmem (FLb + tt n))
    (hmk : ∀ a, mk0 a = if a ≤ m then c.nmem (MKb + a) else 0) :
    ∃ c' k, Exec P W cwProg c c' k ∧ k ≤ 26 * N + 10 ∧
      c'.nreg 9441 = tt N ∧ c'.nreg 9442 = (cwRun g tt mk0 N).cnt ∧
      (∀ a ≤ m, c'.nmem (MKb + a) = (cwRun g tt mk0 N).mks a) ∧
      (∀ x < (cwRun g tt mk0 N).cnt, c'.nmem (BTb + x) = (cwRun g tt mk0 N).bt x) ∧
      (∀ a, ¬ (MKb ≤ a ∧ a ≤ MKb + m) → ¬ (BTb ≤ a ∧ a < BTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9439 ∨ 9449 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain rfl : tt = _ := funext htt
  obtain rfl : g = _ := funext hg
  obtain rfl : mk0 = _ := funext hmk
  exact cwProg_execW (P := P) c hc r00 r02 r04 r05 r06 r07 r10 r31 hNm ht₀ hMK hFL hNX hSG dMK dBT
    hW

set_option maxHeartbeats 1600000 in
/-- **The prologue, part 2, on the machine.** -/
theorem proP2_execW (p : FpIn) (c : Config) (hc : WordsBounded W c) {A0 : ℕ}
    (hR : RegP1 p A0 c) (hlo : ∀ a < A0, c.nmem a = p.mem a)
    (hNXm : ∀ i < p.m, c.nmem (A0 + i) = nxF p.d p.m p.mem i)
    (hFLm : ∀ i < p.m, c.nmem (A0 + p.m + i) = p.lab i)
    (hONm : ∀ i < p.m, c.nmem (A0 + p.m + p.m + i) = 0)
    (hMKm : ∀ a ≤ p.m, c.nmem (A0 + p.m + p.m + p.m + a) = 0)
    (hRV : ∀ i < p.m, p.RV i < p.m) (hSG : PermOn (sgF p.d p.m p.mem) p.m)
    (hNX : PermOn (nxF p.d p.m p.mem) p.m) (hPD : ∀ l < p.k, p.PD l < p.m) (hk0 : 0 < p.k)
    (hfr : p.d + 4 + 7 * p.m ≤ A0) (hsg : p.PDb + p.k ≤ A0)
    (hW : A0 + 9 * p.m + p.k + 4 ≤ W) :
    ∃ c' t, Exec P W proP2 c c' t ∧ t ≤ 19 * p.k + 26 * p.m + 16 ∧
      (∀ i < p.m, c'.nmem (A0 + p.m + p.m + i) = p.ON i) ∧
      (∀ a ≤ p.m, c'.nmem (A0 + p.m + p.m + p.m + a) = p.cw.mks a) ∧
      (∀ x < p.cw.cnt, c'.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m + x) =
        p.cw.bt x) ∧
      c'.nreg 9419 = p.cw.cnt ∧
      (∀ a, ¬ (A0 + p.m + p.m ≤ a ∧ a < A0 + p.m + p.m + p.m) →
        ¬ (A0 + p.m + p.m + p.m ≤ a ∧ a ≤ A0 + p.m + p.m + p.m + p.m) →
        ¬ (A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m ≤ a ∧
          a < A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m + p.m) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9439 ∨ 9449 < r) → (r < 9450 ∨ 9455 < r) → r ≠ 9419 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨g00, g03, g36, g21, g01, g71, g02, g30, g31, g34, g35, g04, g05, g06, g07, g08, g09,
    g10, -⟩ := hR
  have hPDm : ∀ l < p.k, c.nmem (p.PDb + l) = p.PD l := fun l hl => hlo _ (by omega)
  have hRVm : ∀ i < p.m, c.nmem (p.d + 4 + p.m + i) = p.RV i := fun i hi => hlo _ (by omega)
  have hlab : ∀ i < p.m, p.lab i ≤ p.m := fun i hi => by
    have := olab_lt hNX hi; simp only [FpIn.lab]; omega
  -- marks
  obtain ⟨c₁, t₁, e₁, ht₁, mON, mMK, mk, mn, mr, mrm, mo⟩ :=
    fmkProg_execW (P := P) c hc (k := p.k) (m := p.m) (PDb := p.PDb) (RVb := p.d + 4 + p.m)
      (FLb := A0 + p.m) (ONb := A0 + p.m + p.m) (MKb := A0 + p.m + p.m + p.m) g01 g02 g05 g06
      g07 g30 g36 (fun l hl => by rw [hPDm l hl]; exact hPD l hl)
      (fun i hi => by rw [hRVm i hi]; exact hRV i hi)
      (fun i hi => by rw [hFLm i hi]; exact hlab i hi)
      (fun a ha => ⟨by omega, by omega, by omega⟩) (by omega) (by omega)
  have eON : ∀ i < p.m, c₁.nmem (A0 + p.m + p.m + i) = p.ON i := fun i hi => by
    rw [mON i hi]
    exact fmk2_congr (fun l hl => hPDm l hl)
      (fun l hl => by rw [hPDm l hl, hRVm _ (hPD l hl)]) (hONm i hi)
  have eMK : ∀ a ≤ p.m, c₁.nmem (A0 + p.m + p.m + p.m + a) = p.MK0 a := fun a ha => by
    rw [mMK a ha]
    simp only [FpIn.MK0, ha, ↓reduceIte]
    exact fmk2_congr (fun l hl => by rw [hPDm l hl, hFLm _ (hPD l hl)])
      (fun l hl => by rw [hPDm l hl, hRVm _ (hPD l hl), hFLm _ (hRV _ (hPD l hl))]) (hMKm a ha)
  have k1 : ∀ a, (a < A0 + p.m + p.m ∨ A0 + p.m + p.m + p.m + p.m < a) → c₁.nmem a = c.nmem a :=
    fun a ha => mk a (by omega) (by omega)
  -- the walk
  have hsg1 : ∀ i < p.m, c₁.nmem (p.d + 4 + p.m + p.m + i) = sgF p.d p.m p.mem i := fun i hi => by
    rw [k1 _ (Or.inl (by omega)), hlo _ (by omega)]; simp only [sgF]; congr 1; ring
  have hnx1 : ∀ i < p.m, c₁.nmem (A0 + i) = nxF p.d p.m p.mem i := fun i hi => by
    rw [k1 _ (Or.inl (by omega)), hNXm i hi]
  have htw : ∀ i < p.m, twF A0 (p.d + 4 + p.m + p.m) (A0 + p.m + p.m) c₁.nmem i = p.tw i :=
    fun i hi => by
      simp only [twF, FpIn.tw, eON i hi, hnx1 i hi, hsg1 i hi]
  have h0 : p.PD 0 < p.m := hPD 0 hk0
  have htt := FpIn.tt_lt p hSG hNX h0
  have e0 : c₁.nmem p.PDb = p.PD 0 := by rw [k1 _ (Or.inl (by omega)), ← hPDm 0 hk0]; rfl
  have hit : ∀ n, p.tt n = (twF A0 (p.d + 4 + p.m + p.m) (A0 + p.m + p.m) c₁.nmem)^[n]
      (c₁.nmem p.PDb) := fun n => by
    rw [e0]
    exact (iter_congr_on (fun i hi => (htw i hi).symm)
      (fun i hi => by unfold FpIn.tw; split_ifs
                      · exact hNX.lt _ hi
                      · exact hSG.lt _ hi) n _ h0)
  have n1 : ∀ r, (r < 9450 ∨ 9455 < r) → c₁.nreg r = c.nreg r := mn
  obtain ⟨c₂, t₂, e₂, ht₂, w41, w42, wMK, wBT, wk, wn, wr, wrm, wo⟩ :=
    cwProg_execW' (P := P) c₁ e₁.wb_right (N := p.m) (m := p.m) (NXb := A0)
      (SGb := p.d + 4 + p.m + p.m) (ONb := A0 + p.m + p.m) (FLb := A0 + p.m)
      (MKb := A0 + p.m + p.m + p.m) (BTb := A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m)
      (t₀b := p.PDb) (by rw [n1 _ (by omega), g00]) (by rw [n1 _ (by omega), g02])
      (by rw [n1 _ (by omega), g04]) (by rw [n1 _ (by omega), g05])
      (by rw [n1 _ (by omega), g06]) (by rw [n1 _ (by omega), g07])
      (by rw [n1 _ (by omega), g10]) (by rw [n1 _ (by omega), g31]) le_rfl (by rw [e0]; exact h0)
      (fun a ha => by rw [eMK a ha]; simp only [FpIn.MK0, ha, ↓reduceIte]; exact fmk2_le_one)
      (fun i hi => by rw [k1 _ (Or.inl (by omega)), hFLm i hi]; exact hlab i hi)
      (fun i hi => by rw [hnx1 i hi]; exact hNX.lt _ hi)
      (fun i hi => by rw [hsg1 i hi]; exact hSG.lt _ hi)
      (fun a h1 h2 => ⟨by omega, by omega, by omega, by omega, by omega⟩)
      (fun a h1 h2 => ⟨by omega, by omega, by omega, by omega, by omega⟩) (by omega)
      (tt := p.tt) (g := fun n => p.lab (p.tt n)) (mk0 := p.MK0) hit
      (fun n => by rw [k1 _ (Or.inl (by have := htt n; omega)), hFLm _ (htt n)])
      (fun a => by
        by_cases ha : a ≤ p.m
        · simp only [ha, ↓reduceIte]; exact (eMK a ha).symm
        · simp only [FpIn.MK0, ha, ↓reduceIte])
  have n2 : ∀ r, (r < 9439 ∨ 9449 < r) → c₂.nreg r = c₁.nreg r := wn
  obtain ⟨c₃, t₃, e₃, ht₃, d19, dk, dm, dr, drm, do'⟩ := pinD_exec (P := P) c₂ e₂.wb_right
  refine ⟨c₃, _, e₁.seq (e₂.seq e₃), by omega, fun i hi => ?_, fun a ha => ?_, fun x hx => ?_,
    by rw [d19, w42]; rfl, fun a h1 h2 h3 => ?_, fun r h1 h2 h3 => ?_, by rw [dr, wr, mr],
    by rw [drm, wrm, mrm], by rw [do', wo, mo]⟩
  · rw [dm, wk _ (by omega) (by omega)]; exact eON i hi
  · rw [dm, wMK a ha]; rfl
  · rw [dm, wBT x hx]; rfl
  · rw [dm, wk _ (by omega) h3, mk a h1 (by omega)]
  · rw [dk r h3, n2 r h1, n1 r h2]

end BKMNW

end PlanarFlow
