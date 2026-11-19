module

public import PlanarFlow.BKMNW.Nf7eWI

/-!
# The query darts of the MSSP call on the base map, and the register swaps

The MSSP call of `fixP` asks for the distances between the corners `β x` of the path. The
prologue records for each corner the frame index `BT[x]` of a dart of that face met by the walk;
on the frame of the map with pendant edges that dart may be a pendant dart, which the base map does
not have. **`qbP`** writes instead, for every arc `a < 2k` of the path (`ET[a]` its corner),
`QB[ET[a]] := ` the index of the dart `dartAt a` (`PD[l]` for `a = 2l`, `RV[PD[l]]` for
`a = 2l + 1`): a dart of the path, i.e. of the base map, on the face `β (ET a)`.

* `qbM` (the memory after `l` steps), `qbM_out`, **`qbM_val`** (every corner that occurs among the
  `ET[a]` gets the index of some arc `a` with that corner);
* `qbBody`, **`qbP`** (registers `9650 … 9657`), `qbBody_exec`, **`qbP_exec`** (`16 k + 3` steps);
* **`swF`** (`r9400 := mem[r9998]`, `r9431 := r9998 + 4 + 2m`: the size and the rotation `SG` of
  the base frame, for the MSSP call and the negative-length call; the reverse stays the pendant
  `RV = r9430`, whose first `m` cells are the base reverse), **`swB = swF ; r9410 := r9418`** (the
  queries `QB` at `S1 = r9418`); `swF_exec`, `swB_exec`.
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

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The memory model -/

/-- The index of the dart `dartAt a` read from the arrays `PD`, `RV`. -/
def qv (nm : ℕ → ℕ) (PDb RVb a : ℕ) : ℕ :=
  if a % 2 = 0 then nm (PDb + a / 2) else nm (RVb + nm (PDb + a / 2))

/-- The memory after `l` steps of `qbP`. -/
def qbM (nm : ℕ → ℕ) (PDb RVb ETb QBb : ℕ) : ℕ → ℕ → ℕ
  | 0 => nm
  | l + 1 => upd (upd (qbM nm PDb RVb ETb QBb l) (QBb + nm (ETb + (l + l))) (nm (PDb + l)))
      (QBb + nm (ETb + (l + l) + 1)) (nm (RVb + nm (PDb + l)))

lemma qbM_out (nm : ℕ → ℕ) {PDb RVb ETb QBb b l : ℕ} (hET : ∀ a < 2 * l, nm (ETb + a) < b)
    {x : ℕ} (hx : x < QBb ∨ QBb + b ≤ x) : qbM nm PDb RVb ETb QBb l x = nm x := by
  induction l with
  | zero => rfl
  | succ l ih =>
    have h1 := hET (l + l) (by omega)
    have h2 := hET (l + l + 1) (by omega)
    rw [← Nat.add_assoc] at h2
    simp only [qbM]
    rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
    exact ih fun a ha => hET a (by omega)

/-- **Every corner among the arcs gets the index of an arc with that corner.** -/
theorem qbM_val (nm : ℕ → ℕ) (PDb RVb ETb QBb : ℕ) :
    ∀ l x, (∃ a < 2 * l, nm (ETb + a) = x) →
      ∃ a < 2 * l, nm (ETb + a) = x ∧ qbM nm PDb RVb ETb QBb l (QBb + x) = qv nm PDb RVb a
  | 0, x, ⟨a, ha, _⟩ => absurd ha (by omega)
  | l + 1, x, hx => by
    simp only [qbM]
    by_cases h1 : nm (ETb + (l + l) + 1) = x
    · refine ⟨l + l + 1, by omega, by rw [← Nat.add_assoc]; exact h1, ?_⟩
      rw [h1, upd_same]
      unfold qv
      rw [if_neg (by omega), show (l + l + 1) / 2 = l by omega]
    · rw [upd_other _ _ _ (by omega)]
      by_cases h0 : nm (ETb + (l + l)) = x
      · refine ⟨l + l, by omega, h0, ?_⟩
        rw [h0, upd_same]
        unfold qv
        rw [if_pos (by omega), show (l + l) / 2 = l by omega]
      · rw [upd_other _ _ _ (by omega)]
        obtain ⟨a, ha, e⟩ := hx
        have ha' : a < 2 * l := by
          rcases Nat.lt_or_ge a (2 * l) with h | h
          · exact h
          · exfalso
            rcases (show a = l + l ∨ a = l + l + 1 by omega) with rfl | rfl
            · exact h0 e
            · rw [← Nat.add_assoc] at e; exact h1 e
        obtain ⟨a', ha'', e', hv⟩ := qbM_val nm PDb RVb ETb QBb l x ⟨a, ha', e⟩
        exact ⟨a', by omega, e', hv⟩

/-! ### The programs -/

/-- One step of `qbP`: `QB[ET[2l]] := PD[l]`, `QB[ET[2l+1]] := RV[PD[l]]`. -/
def qbBody : Stmt := block [.addN 9651 9402 9650, .loadN 9651 9651, .addN 9652 9430 9651,
  .loadN 9652 9652, .addN 9653 9650 9650, .addN 9654 9414 9653, .loadN 9655 9654,
  .addN 9654 9654 9436, .loadN 9656 9654, .addN 9657 9418 9655, .storeN 9657 9651,
  .addN 9657 9418 9656, .storeN 9657 9652, .addN 9650 9650 9436]

/-- **The query darts of the MSSP call** at `QB = r9418`. -/
def qbP : Stmt := .seq (block [.constN 9650 0]) (.whileLtN 9650 9401 qbBody)

/-- The base frame (`r9998`) for the calls on the base map: `m` and the rotation `SG` of the base
frame (the reverse is read from the first `m` cells of the pendant `RV`). -/
def swF : Stmt := block [.loadN 9400 9998, .constN 9650 4, .addN 9651 9998 9650,
  .addN 9431 9651 9400, .addN 9431 9431 9400]

/-- The base frame and the queries `QB` for the MSSP call. -/
def swB : Stmt := .seq swF (block [.copyN 9410 9418])

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1600000 in
theorem qbBody_exec (c : Config) (hc : WordsBounded W c) {PDb RVb ETb QBb l : ℕ}
    (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = RVb) (r14 : c.nreg 9414 = ETb)
    (r18 : c.nreg 9418 = QBb) (r36 : c.nreg 9436 = 1) (r50 : c.nreg 9650 = l)
    (hb : PDb + l + 1 ≤ W) (hr : RVb + c.nmem (PDb + l) ≤ W) (he : ETb + (l + l) + 1 ≤ W)
    (hq0 : QBb + c.nmem (ETb + (l + l)) ≤ W) (hq1 : QBb + c.nmem (ETb + (l + l) + 1) ≤ W) :
    ∃ c' t, Exec P W qbBody c c' t ∧ t = 14 ∧ c'.nreg 9650 = l + 1 ∧
      c'.nmem = upd (upd c.nmem (QBb + c.nmem (ETb + (l + l))) (c.nmem (PDb + l)))
        (QBb + c.nmem (ETb + (l + l) + 1)) (c.nmem (RVb + c.nmem (PDb + l))) ∧
      (∀ r, (r < 9650 ∨ 9657 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hc' := hc
  unfold qbBody
  exec_block
  all_goals try ((try config_simp) <;>
    (try simp only [r02, r30, r14, r18, r36, r50]) <;> omega)
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r02, r30, r14, r18, r36, r50])
  all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

theorem qbP_exec (c : Config) (hc : WordsBounded W c) {k m b PDb RVb ETb QBb : ℕ}
    (r01 : c.nreg 9401 = k) (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = RVb)
    (r14 : c.nreg 9414 = ETb) (r18 : c.nreg 9418 = QBb) (r36 : c.nreg 9436 = 1)
    (hPD : ∀ l < k, c.nmem (PDb + l) < m) (hRV : ∀ i < m, c.nmem (RVb + i) < m)
    (hET : ∀ a < 2 * k, c.nmem (ETb + a) < b)
    (hd : PDb + k ≤ QBb ∧ RVb + m ≤ QBb ∧ ETb + 2 * k ≤ QBb)
    (hW : QBb + b + 1 ≤ W) :
    ∃ c' t, Exec P W qbP c c' t ∧ t ≤ 16 * k + 3 ∧
      c'.nmem = qbM c.nmem PDb RVb ETb QBb k ∧
      (∀ r, (r < 9650 ∨ 9657 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a50, ak, am, ar, arm, ao⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 9650 0]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 9650 = 0 ∧
      (∀ r, r ≠ 9650 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun l c' =>
    c'.nmem = qbM c.nmem PDb RVb ETb QBb l ∧
    (∀ r, (r < 9650 ∨ 9657 < r) → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h50, j1, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 9650) (b := 9401) (body := qbBody) J (lo := 0) (hi := k) (B := 14) c₁ e₁.wb_right a50
    (by rw [ak _ (by omega), r01]) (Nat.zero_le _)
    ⟨am, fun r hr => ak r (by omega), ar, arm, ao⟩
    (fun l c' _ hl hw h50 h01 ⟨j1, j3, j4, j5, j6⟩ => by
      have L : ∀ a, (a < QBb ∨ QBb + b ≤ a) → c'.nmem a = c.nmem a := fun a ha => by
        rw [j1]; exact qbM_out _ (fun a' ha' => hET a' (by omega)) ha
      have ht := hPD l hl
      have hr := hRV _ ht
      have h0 := hET (l + l) (by omega)
      have h1 := hET (l + l + 1) (by omega)
      rw [← Nat.add_assoc] at h1
      have eT : c'.nmem (PDb + l) = c.nmem (PDb + l) := L _ (Or.inl (by omega))
      have eR : c'.nmem (RVb + c.nmem (PDb + l)) = c.nmem (RVb + c.nmem (PDb + l)) :=
        L _ (Or.inl (by omega))
      have eE0 : c'.nmem (ETb + (l + l)) = c.nmem (ETb + (l + l)) := L _ (Or.inl (by omega))
      have eE1 : c'.nmem (ETb + (l + l) + 1) = c.nmem (ETb + (l + l) + 1) :=
        L _ (Or.inl (by omega))
      obtain ⟨c'', t, ex, htt, b50, bm, bk, br, brm, bo⟩ :=
        qbBody_exec (P := P) c' hw (PDb := PDb) (RVb := RVb) (ETb := ETb) (QBb := QBb)
          (by rw [j3 _ (by omega), r02]) (by rw [j3 _ (by omega), r30])
          (by rw [j3 _ (by omega), r14]) (by rw [j3 _ (by omega), r18])
          (by rw [j3 _ (by omega), r36]) h50 (by omega)
          (by rw [eT]; omega) (by omega) (by rw [eE0]; omega) (by rw [eE1]; omega)
      rw [eT, eR, eE0, eE1, j1] at bm
      exact ⟨c'', t, ex, htt.le, b50, by rw [bk _ (by omega)]; exact h01, bm,
        fun r hr => by rw [bk r hr]; exact j3 r hr, by rw [br, j4], by rw [brm, j5],
        by rw [bo, j6]⟩)
  refine ⟨c₂, _, e₁.seq e₂, by rw [hk₁]; simp only [Nat.sub_zero] at hk₂; omega, j1, j3, j4, j5,
    j6⟩

set_option maxHeartbeats 1600000 in
theorem swF_exec (c : Config) (hc : WordsBounded W c) {d m : ℕ} (r98 : c.nreg 9998 = d)
    (hm : c.nmem d = m) (hW : d + 4 + 2 * m ≤ W) :
    ∃ c' t, Exec P W swF c c' t ∧ t = 5 ∧ c'.nreg 9400 = m ∧ c'.nreg 9431 = d + 4 + m + m ∧
      (∀ r, r ≠ 9400 → r ≠ 9431 → r ≠ 9650 → r ≠ 9651 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hc' := hc
  unfold swF
  exec_block
  all_goals try ((try config_simp) <;> (try simp only [r98, hm]) <;>
    first | omega | exact hc.2.1 _)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r98, hm])
  all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

theorem swB_exec (c : Config) (hc : WordsBounded W c) {d m : ℕ} (r98 : c.nreg 9998 = d)
    (hm : c.nmem d = m) (hW : d + 4 + 2 * m ≤ W) :
    ∃ c' t, Exec P W swB c c' t ∧ t = 6 ∧ c'.nreg 9400 = m ∧ c'.nreg 9431 = d + 4 + m + m ∧
      c'.nreg 9410 = c.nreg 9418 ∧
      (∀ r, r ≠ 9400 → r ≠ 9431 → r ≠ 9650 → r ≠ 9651 → r ≠ 9410 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a00, a31, ak, am, ar, arm, ao⟩ := swF_exec (P := P) c hc r98 hm hW
  obtain ⟨c₂, t₂, e₂, ht₂, b10, bk, bm, br, brm, bo⟩ : ∃ c₂ t₂,
      Exec P W (block [.copyN 9410 9418]) c₁ c₂ t₂ ∧ t₂ = 1 ∧ c₂.nreg 9410 = c₁.nreg 9418 ∧
      (∀ r, r ≠ 9410 → c₂.nreg r = c₁.nreg r) ∧
      c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have := e₁.wb_right
    exec_block
    refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₂, _, e₁.seq e₂, by omega, by rw [bk _ (by omega), a00],
    by rw [bk _ (by omega), a31],
    by rw [b10, ak _ (by omega) (by omega) (by omega) (by omega)],
    fun r h1 h2 h3 h4 h5 => by rw [bk r h5, ak r h1 h2 h3 h4], by rw [bm, am],
    by rw [br, ar], by rw [brm, arm], by rw [bo, ao]⟩

end F9b

end BKMNW

end PlanarFlow
