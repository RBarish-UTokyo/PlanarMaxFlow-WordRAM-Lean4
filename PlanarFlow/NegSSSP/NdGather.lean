module

public import PlanarFlow.NegSSSP.Enc.StoreLog

/-!
# The node step: the values of a child read in the node's numbering

A child's outcome region (`Res`) lists `w_c` global vertex identifiers `ID u` and values
`VL u`; the node numbers its vertices `v < w` with identifiers `I v`. **`cgProg`** (registers
`2460 … 2471`) writes, for every `v < w`, `OUT v = VL u + 1` if some `u` has `ID u = I v`, and
`0` otherwise, through a scratch table `T` indexed by the identifiers (`[Gt, Gt + G)`, zero
before and **zero again after**): fill `T[ID u] := VL u + 1`, read `OUT v := T[I v]`, clear
`T[ID u] := 0`. Within `17 w_c + 9 w + 11` steps (`cgProg_exec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- Fill: `T[Gt + ID[i]] := VL[i] + 1`. -/
def cgFillB : Stmt := block [.addN 2469 2461 2467, .loadN 2469 2469, .addN 2469 2463 2469,
  .addN 2470 2462 2467, .loadN 2470 2470, .addN 2470 2470 2468, .storeN 2469 2470,
  .addN 2467 2467 2468]

/-- Read: `OUT[i] := T[Gt + I[i]]`. -/
def cgReadB : Stmt := block [.addN 2469 2465 2467, .loadN 2469 2469, .addN 2469 2463 2469,
  .loadN 2469 2469, .addN 2470 2466 2467, .storeN 2470 2469, .addN 2467 2467 2468]

/-- Clear: `T[Gt + ID[i]] := 0`. -/
def cgClrB : Stmt := block [.addN 2469 2461 2467, .loadN 2469 2469, .addN 2469 2463 2469,
  .storeN 2469 2471, .addN 2467 2467 2468]

/-- **The values of a child in the node's numbering** (registers: `wc = r2460`,
`IDb = r2461`, `VLb = r2462`, `Gt = r2463`, `w = r2464`, `Ib = r2465`, `Ob = r2466`;
scratch `2467 … 2471`). -/
def cgProg : Stmt :=
  .seq (block [.constN 2468 1, .constN 2471 0, .constN 2467 0]) <|
  .seq (.whileLtN 2467 2460 cgFillB) <|
  .seq (.instr (.constN 2467 0)) <|
  .seq (.whileLtN 2467 2464 cgReadB) <|
  .seq (.instr (.constN 2467 0)) (.whileLtN 2467 2460 cgClrB)

theorem cgProg_natOnly : Klein.natOnly cgProg = true := by decide

variable {P : Input} {W : ℕ}

/-- The registers of `cgProg`. -/
structure CgIn (wc IDb VLb Gt w Ib Ob : ℕ) (c : Config) : Prop where
  r60 : c.nreg 2460 = wc
  r61 : c.nreg 2461 = IDb
  r62 : c.nreg 2462 = VLb
  r63 : c.nreg 2463 = Gt
  r64 : c.nreg 2464 = w
  r65 : c.nreg 2465 = Ib
  r66 : c.nreg 2466 = Ob

theorem CgIn.of {wc IDb VLb Gt w Ib Ob : ℕ} {c c' : Config} (h : CgIn wc IDb VLb Gt w Ib Ob c)
    (hr : ∀ r, 2460 ≤ r → r ≤ 2466 → c'.nreg r = c.nreg r) : CgIn wc IDb VLb Gt w Ib Ob c' :=
  ⟨(hr _ (by omega) (by omega)).trans h.r60, (hr _ (by omega) (by omega)).trans h.r61,
    (hr _ (by omega) (by omega)).trans h.r62, (hr _ (by omega) (by omega)).trans h.r63,
    (hr _ (by omega) (by omega)).trans h.r64, (hr _ (by omega) (by omega)).trans h.r65,
    (hr _ (by omega) (by omega)).trans h.r66⟩

/-! ### The bodies -/

theorem cgFillB_exec (c : Config) (hc : WordsBounded W c) {IDb VLb Gt i x y : ℕ}
    (r61 : c.nreg 2461 = IDb) (r62 : c.nreg 2462 = VLb) (r63 : c.nreg 2463 = Gt)
    (r67 : c.nreg 2467 = i) (r68 : c.nreg 2468 = 1) (mx : c.nmem (IDb + i) = x)
    (my : c.nmem (VLb + i) = y) (w1 : IDb + i ≤ W) (w2 : VLb + i ≤ W) (w3 : Gt + x ≤ W)
    (w4 : y + 1 ≤ W) (w5 : i + 1 ≤ W) :
    ∃ c'' t, Exec P W cgFillB c c'' t ∧ t = 8 ∧ c''.nmem = upd c.nmem (Gt + x) (y + 1) ∧
      c''.nreg 2467 = i + 1 ∧ (∀ r, r ≠ 2467 → r ≠ 2469 → r ≠ 2470 → c''.nreg r = c.nreg r) ∧
      c''.rreg = c.rreg ∧ c''.rmem = c.rmem ∧ c''.output = c.output := by
  unfold cgFillB
  exec_block
  all_goals try ((try config_simp); (try simp only [r61, r62, r63, r67, r68, mx, my]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r61, r62, r63, r67, r68, mx, my])
  simp only [upd_apply]; split_ifs <;> omega

theorem cgReadB_exec (c : Config) (hc : WordsBounded W c) {Ib Ob Gt i x y : ℕ}
    (r65 : c.nreg 2465 = Ib) (r66 : c.nreg 2466 = Ob) (r63 : c.nreg 2463 = Gt)
    (r67 : c.nreg 2467 = i) (r68 : c.nreg 2468 = 1) (mx : c.nmem (Ib + i) = x)
    (my : c.nmem (Gt + x) = y) (w1 : Ib + i ≤ W) (w2 : Ob + i ≤ W) (w3 : Gt + x ≤ W)
    (w5 : i + 1 ≤ W) :
    ∃ c'' t, Exec P W cgReadB c c'' t ∧ t = 7 ∧ c''.nmem = upd c.nmem (Ob + i) y ∧
      c''.nreg 2467 = i + 1 ∧ (∀ r, r ≠ 2467 → r ≠ 2469 → r ≠ 2470 → c''.nreg r = c.nreg r) ∧
      c''.rreg = c.rreg ∧ c''.rmem = c.rmem ∧ c''.output = c.output := by
  unfold cgReadB
  exec_block
  all_goals try ((try config_simp); (try simp only [r65, r66, r63, r67, r68, mx, my]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r65, r66, r63, r67, r68, mx, my])
  simp only [upd_apply]; split_ifs <;> omega

theorem cgClrB_exec (c : Config) (hc : WordsBounded W c) {IDb Gt i x : ℕ}
    (r61 : c.nreg 2461 = IDb) (r63 : c.nreg 2463 = Gt) (r67 : c.nreg 2467 = i)
    (r68 : c.nreg 2468 = 1) (r71 : c.nreg 2471 = 0) (mx : c.nmem (IDb + i) = x)
    (w1 : IDb + i ≤ W) (w3 : Gt + x ≤ W) (w5 : i + 1 ≤ W) :
    ∃ c'' t, Exec P W cgClrB c c'' t ∧ t = 5 ∧ c''.nmem = upd c.nmem (Gt + x) 0 ∧
      c''.nreg 2467 = i + 1 ∧ (∀ r, r ≠ 2467 → r ≠ 2469 → r ≠ 2470 → c''.nreg r = c.nreg r) ∧
      c''.rreg = c.rreg ∧ c''.rmem = c.rmem ∧ c''.output = c.output := by
  unfold cgClrB
  exec_block
  all_goals try ((try config_simp); (try simp only [r61, r63, r67, r68, r71, mx]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r61, r63, r67, r68, r71, mx])
  simp only [upd_apply]; split_ifs <;> omega

theorem cgFill_exec (c : Config) (hc : WordsBounded W c) {wc IDb VLb Gt w Ib Ob G : ℕ}
    (hI : CgIn wc IDb VLb Gt w Ib Ob c) (r67 : c.nreg 2467 = 0) (r68 : c.nreg 2468 = 1)
    (hid : ∀ u < wc, c.nmem (IDb + u) < G)
    (hcons : ∀ u < wc, ∀ u' < wc, c.nmem (IDb + u) = c.nmem (IDb + u') →
      c.nmem (VLb + u) = c.nmem (VLb + u'))
    (hT0 : ∀ x < G, c.nmem (Gt + x) = 0) (wID : IDb + wc ≤ W) (wVL : VLb + wc ≤ W)
    (wG : Gt + G ≤ W) (wv : ∀ u < wc, c.nmem (VLb + u) + 1 ≤ W)
    (dID : IDb + wc ≤ Gt ∨ Gt + G ≤ IDb) (dVL : VLb + wc ≤ Gt ∨ Gt + G ≤ VLb) :
    ∃ c' t, Exec P W (.whileLtN 2467 2460 cgFillB) c c' t ∧ t ≤ 10 * wc + 2 ∧
      (∀ x < G, (c'.nmem (Gt + x) = 0 ↔ ∀ u < wc, c.nmem (IDb + u) ≠ x) ∧
        ∀ u < wc, c.nmem (IDb + u) = x → c'.nmem (Gt + x) = c.nmem (VLb + u) + 1) ∧
      (∀ a, (a < Gt ∨ Gt + G ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2467 → r ≠ 2469 → r ≠ 2470 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x < G, (c'.nmem (Gt + x) = 0 ↔ ∀ u < i, c.nmem (IDb + u) ≠ x) ∧
        ∀ u < i, c.nmem (IDb + u) = x → c'.nmem (Gt + x) = c.nmem (VLb + u) + 1) ∧
      (∀ a, (a < Gt ∨ Gt + G ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2467 → r ≠ 2469 → r ≠ 2470 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2467) (bR := 2460)
    (body := cgFillB) J (K := 8) (n := wc) c hc r67 hI.r60
    ⟨fun x hx => ⟨⟨fun _ u hu => absurd hu (by omega), fun _ => hT0 x hx⟩,
      fun u hu => absurd hu (by omega)⟩, fun _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
      have hI' := hI.of fun r h1 h2 => jn r (by omega) (by omega) (by omega)
      have hidi := hid i hi
      have hvi := wv i hi
      obtain ⟨c'', t, ex, ht, hm, h67, hn, hr, hrm, ho⟩ :=
        cgFillB_exec (P := P) c' hw hI'.r61 hI'.r62 hI'.r63 ha
          ((jn 2468 (by omega) (by omega) (by omega)).trans r68) (j2 (IDb + i) (by omega)) (j2 (VLb + i) (by omega))
          (by omega) (by omega) (by omega) hvi (by omega)
      refine ⟨c'', t, ex, by omega, h67, (hn 2460 (by omega) (by omega) (by omega)).trans hb,
        ⟨fun x hx => ⟨?_, fun u hu hux => ?_⟩, fun a ha' => ?_,
          fun r h1 h2 h3 => (hn r h1 h2 h3).trans (jn r h1 h2 h3), by rw [hr, jr], by rw [hrm, jrm],
          by rw [ho, jo]⟩⟩
      · rw [hm, upd_apply]
        split_ifs with h
        · constructor
          · intro h'; first | exact h'.elim | exact absurd h' (by omega)
          · intro h'; exact absurd (by omega) (h' i (by omega))
        · rw [(j1 x hx).1]
          constructor
          · intro h' u hu
            rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
            · exact h' u hu
            · intro e; exact h (by rw [e])
          · intro h' u hu; exact h' u (by omega)
      · rw [hm, upd_apply]
        split_ifs with h
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
          · have := hcons u (by omega) i hi (by omega)
            rw [this]
          · rfl
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
          · exact (j1 x hx).2 u hu hux
          · exact absurd (by omega) h
      · rw [hm, upd_other _ _ _ (by omega)]; exact j2 a ha')
  obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₂, e₂, by omega, j1, j2, jn, jr, jrm, jo⟩

theorem cgRead_exec (c : Config) (hc : WordsBounded W c) {wc IDb VLb Gt w Ib Ob G : ℕ}
    {T : ℕ → ℕ} (hI : CgIn wc IDb VLb Gt w Ib Ob c) (r67 : c.nreg 2467 = 0)
    (r68 : c.nreg 2468 = 1) (hT : ∀ x < G, c.nmem (Gt + x) = T x)
    (hIv : ∀ v < w, c.nmem (Ib + v) < G) (wI : Ib + w ≤ W) (wO : Ob + w ≤ W)
    (wG : Gt + G ≤ W) (dOG : Ob + w ≤ Gt ∨ Gt + G ≤ Ob) (dOI : Ob + w ≤ Ib ∨ Ib + w ≤ Ob) :
    ∃ c' t, Exec P W (.whileLtN 2467 2464 cgReadB) c c' t ∧ t ≤ 9 * w + 2 ∧
      (∀ v < w, c'.nmem (Ob + v) = T (c.nmem (Ib + v))) ∧
      (∀ a, (a < Ob ∨ Ob + w ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2467 → r ≠ 2469 → r ≠ 2470 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ v < i, c'.nmem (Ob + v) = T (c.nmem (Ib + v))) ∧
      (∀ a, (a < Ob ∨ Ob + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2467 → r ≠ 2469 → r ≠ 2470 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2467) (bR := 2464)
    (body := cgReadB) J (K := 7) (n := w) c hc r67 hI.r64
    ⟨fun v hv => absurd hv (by omega), fun _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
      have hI' := hI.of fun r h1 h2 => jn r (by omega) (by omega) (by omega)
      have hii := hIv i hi
      obtain ⟨c'', t, ex, ht, hm, h67, hn, hr, hrm, ho⟩ :=
        cgReadB_exec (P := P) (y := T (c.nmem (Ib + i))) c' hw hI'.r65 hI'.r66 hI'.r63 ha
          ((jn 2468 (by omega) (by omega) (by omega)).trans r68) (j2 (Ib + i) (by omega))
          (by rw [j2 (Gt + c.nmem (Ib + i)) (by omega)]; exact hT _ hii) (by omega) (by omega)
          (by omega) (by omega)
      refine ⟨c'', t, ex, by omega, h67, (hn 2464 (by omega) (by omega) (by omega)).trans hb,
        ⟨fun v hv => ?_, fun a ha' => ?_, fun r h1 h2 h3 => (hn r h1 h2 h3).trans (jn r h1 h2 h3),
          by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩⟩
      · rw [hm, upd_apply]
        split_ifs with h
        · have : v = i := by omega
          subst this; rfl
        · exact j1 v (by omega)
      · rw [hm, upd_other _ _ _ (by omega)]; exact j2 a (by omega))
  obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₂, e₂, by omega, j1, j2, jn, jr, jrm, jo⟩

theorem cgClr_exec (c : Config) (hc : WordsBounded W c) {wc IDb VLb Gt w Ib Ob G : ℕ}
    (hI : CgIn wc IDb VLb Gt w Ib Ob c) (r67 : c.nreg 2467 = 0) (r68 : c.nreg 2468 = 1)
    (r71 : c.nreg 2471 = 0) (hid : ∀ u < wc, c.nmem (IDb + u) < G)
    (wID : IDb + wc ≤ W) (wG : Gt + G ≤ W) (dID : IDb + wc ≤ Gt ∨ Gt + G ≤ IDb) :
    ∃ c' t, Exec P W (.whileLtN 2467 2460 cgClrB) c c' t ∧ t ≤ 7 * wc + 2 ∧
      (∀ x, (∃ u < wc, c.nmem (IDb + u) = x) → c'.nmem (Gt + x) = 0) ∧
      (∀ a, (∀ u < wc, a ≠ Gt + c.nmem (IDb + u)) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2467 → r ≠ 2469 → r ≠ 2470 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (∃ u < i, c.nmem (IDb + u) = x) → c'.nmem (Gt + x) = 0) ∧
      (∀ a, (∀ u < i, a ≠ Gt + c.nmem (IDb + u)) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2467 → r ≠ 2469 → r ≠ 2470 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2467) (bR := 2460)
    (body := cgClrB) J (K := 5) (n := wc) c hc r67 hI.r60
    ⟨fun x ⟨u, hu, _⟩ => absurd hu (by omega), fun _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
      have hI' := hI.of fun r h1 h2 => jn r (by omega) (by omega) (by omega)
      have hidi := hid i hi
      have mid : c'.nmem (IDb + i) = c.nmem (IDb + i) := j2 _ fun u _ => by
        have := hid u (by omega); omega
      obtain ⟨c'', t, ex, ht, hm, h67, hn, hr, hrm, ho⟩ :=
        cgClrB_exec (P := P) c' hw hI'.r61 hI'.r63 ha ((jn 2468 (by omega) (by omega) (by omega)).trans r68)
          ((jn 2471 (by omega) (by omega) (by omega)).trans r71) mid (by omega) (by omega) (by omega)
      refine ⟨c'', t, ex, by omega, h67, (hn 2460 (by omega) (by omega) (by omega)).trans hb,
        ⟨fun x ⟨u, hu, hux⟩ => ?_, fun a ha' => ?_, fun r h1 h2 h3 => (hn r h1 h2 h3).trans (jn r h1 h2 h3),
          by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩⟩
      · rw [hm, upd_apply]
        split_ifs with h
        · rfl
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
          · exact j1 x ⟨u, hu, hux⟩
          · exact absurd (by rw [hux]) h
      · rw [hm, upd_other _ _ _ (ha' i (by omega))]
        exact j2 a fun u hu => ha' u (by omega))
  obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₂, e₂, by omega, j1, j2, jn, jr, jrm, jo⟩

/-- **The values of a child in the node's numbering.** For every `v < w`: `OUT[v] = 0` iff no
`u < wc` has `ID u = I v`, and `OUT[v] = VL u + 1` for every such `u` (the values agree on equal
identifiers); the table is zero again; memory outside `[Ob, Ob + w)` kept. -/
theorem cgProg_exec (c : Config) (hc : WordsBounded W c) {wc IDb VLb Gt w Ib Ob G : ℕ}
    (hI : CgIn wc IDb VLb Gt w Ib Ob c)
    (hid : ∀ u < wc, c.nmem (IDb + u) < G)
    (hcons : ∀ u < wc, ∀ u' < wc, c.nmem (IDb + u) = c.nmem (IDb + u') →
      c.nmem (VLb + u) = c.nmem (VLb + u'))
    (hT0 : ∀ x < G, c.nmem (Gt + x) = 0) (hIv : ∀ v < w, c.nmem (Ib + v) < G)
    (wID : IDb + wc ≤ W) (wVL : VLb + wc ≤ W) (wI : Ib + w ≤ W) (wO : Ob + w ≤ W)
    (wG : Gt + G ≤ W) (wv : ∀ u < wc, c.nmem (VLb + u) + 1 ≤ W)
    (dID : IDb + wc ≤ Gt ∨ Gt + G ≤ IDb) (dVL : VLb + wc ≤ Gt ∨ Gt + G ≤ VLb)
    (dOG : Ob + w ≤ Gt ∨ Gt + G ≤ Ob) (dOI : Ob + w ≤ Ib ∨ Ib + w ≤ Ob)
    (dOD : Ob + w ≤ IDb ∨ IDb + wc ≤ Ob) (dIG : Ib + w ≤ Gt ∨ Gt + G ≤ Ib) (hW1 : 1 ≤ W) :
    ∃ c' t, Exec P W cgProg c c' t ∧ t ≤ 17 * wc + 9 * w + 11 ∧
      (∀ v < w, (c'.nmem (Ob + v) = 0 ↔ ∀ u < wc, c.nmem (IDb + u) ≠ c.nmem (Ib + v)) ∧
        ∀ u < wc, c.nmem (IDb + u) = c.nmem (Ib + v) →
          c'.nmem (Ob + v) = c.nmem (VLb + u) + 1) ∧
      (∀ a, (a < Ob ∨ Ob + w ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2467 ∨ 2471 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- the constants
  obtain ⟨c₁, k₁, e₁, hk₁, g68, g71, g67, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2468 1, .constN 2471 0, .constN 2467 0]) c c₁ k₁ ∧
      k₁ = 3 ∧ c₁.nreg 2468 = 1 ∧ c₁.nreg 2471 = 0 ∧ c₁.nreg 2467 = 0 ∧
      (∀ r, r ≠ 2467 → r ≠ 2468 → r ≠ 2471 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  have hI₁ := hI.of fun r h1 h2 => gn₁ r (by omega) (by omega) (by omega)
  -- fill
  obtain ⟨c₂, k₂, e₂, hk₂, tab, m₂, n₂, r₂, rm₂, o₂⟩ := cgFill_exec (P := P) c₁ e₁.wb_right hI₁
    g67 g68 (G := G) (by rw [gm₁]; exact hid) (by rw [gm₁]; exact hcons)
    (by rw [gm₁]; exact hT0) wID wVL wG (by rw [gm₁]; exact wv) dID dVL
  rw [gm₁] at tab m₂
  -- read
  have e₃ := Exec.constN (P := P) e₂.wb_right 2467 0 (by omega)
  have hI₃ : CgIn wc IDb VLb Gt w Ib Ob { c₂ with nreg := upd c₂.nreg 2467 0 } :=
    hI₁.of fun r h1 h2 => by
      show upd c₂.nreg 2467 0 r = _
      rw [upd_other _ _ _ (by omega), n₂ r (by omega) (by omega) (by omega)]
  obtain ⟨c₄, k₄, e₄, hk₄, rd, m₄, n₄, r₄, rm₄, o₄⟩ := cgRead_exec (P := P) (G := G)
    (T := fun x => c₂.nmem (Gt + x)) _ e₃.wb_right hI₃ (by config_simp)
    (by show upd c₂.nreg 2467 0 2468 = 1; rw [upd_other _ _ _ (by omega), n₂ 2468 (by omega) (by omega) (by omega)]
        exact g68)
    (fun x _ => rfl) (fun v hv => by
      show c₂.nmem (Ib + v) < G
      rw [m₂ _ (by omega)]; exact hIv v hv) wI wO wG dOG dOI
  simp only at rd m₄
  -- clear
  have hI₅ : CgIn wc IDb VLb Gt w Ib Ob { c₄ with nreg := upd c₄.nreg 2467 0 } :=
    hI₃.of fun r h1 h2 => by
      show upd c₄.nreg 2467 0 r = _
      rw [upd_other _ _ _ (by omega), n₄ r (by omega) (by omega) (by omega)]
  have mid₄ : ∀ u < wc, c₄.nmem (IDb + u) = c.nmem (IDb + u) := fun u hu => by
    rw [m₄ _ (by omega), m₂ _ (by omega)]
  have e₅ := Exec.constN (P := P) e₄.wb_right 2467 0 (by omega)
  obtain ⟨c₆, k₆, e₆, hk₆, z₆, m₆, n₆, r₆, rm₆, o₆⟩ := cgClr_exec (P := P) (G := G)
    { c₄ with nreg := upd c₄.nreg 2467 0 } e₅.wb_right hI₅ (by config_simp)
    (by
      show upd c₄.nreg 2467 0 2468 = 1
      rw [upd_other _ _ _ (by omega), n₄ 2468 (by omega) (by omega) (by omega)]
      show upd c₂.nreg 2467 0 2468 = 1
      rw [upd_other _ _ _ (by omega), n₂ 2468 (by omega) (by omega) (by omega)]; exact g68)
    (by
      show upd c₄.nreg 2467 0 2471 = 0
      rw [upd_other _ _ _ (by omega), n₄ 2471 (by omega) (by omega) (by omega)]
      show upd c₂.nreg 2467 0 2471 = 0
      rw [upd_other _ _ _ (by omega), n₂ 2471 (by omega) (by omega) (by omega)]; exact g71)
    (fun u hu => by show c₄.nmem (IDb + u) < G; rw [mid₄ u hu]; exact hid u hu) wID wG dID
  simp only at z₆ m₆
  refine ⟨c₆, k₁ + (k₂ + (1 + (k₄ + (1 + k₆)))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))),
    by omega, fun v hv => ?_, fun a ha => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have hO : c₆.nmem (Ob + v) = c₂.nmem (Gt + c.nmem (Ib + v)) := by
      rw [m₆ _ (fun u hu => ?_), rd v hv, m₂ (Ib + v) (by omega)]
      rw [mid₄ u hu]; have := hid u hu; omega
    have hIvv := hIv v hv
    rw [hO]
    exact ⟨(tab _ hIvv).1, fun u hu e => (tab _ hIvv).2 u hu e⟩
  · by_cases hG : Gt ≤ a ∧ a < Gt + G
    · obtain ⟨x, rfl⟩ : ∃ x, a = Gt + x := ⟨a - Gt, by omega⟩
      by_cases hx : ∃ u < wc, c.nmem (IDb + u) = x
      · rw [z₆ x (by obtain ⟨u, hu, e⟩ := hx; exact ⟨u, hu, by rw [mid₄ u hu, e]⟩)]
        exact (hT0 x (by omega)).symm
      · push Not at hx
        rw [m₆ _ (fun u hu e => hx u hu (by rw [mid₄ u hu] at e; omega)),
          m₄ _ (by omega)]
        rw [show c₂.nmem (Gt + x) = 0 from ((tab x (by omega)).1).2 hx, hT0 x (by omega)]
    · rw [m₆ _ (fun u hu e => by have := hid u hu; rw [mid₄ u hu] at e; omega), m₄ _ ha,
        m₂ _ (by omega)]
  · rw [n₆ r (by omega) (by omega) (by omega)]
    show upd c₄.nreg 2467 0 r = _
    rw [upd_other _ _ _ (by omega), n₄ r (by omega) (by omega) (by omega)]
    show upd c₂.nreg 2467 0 r = _
    rw [upd_other _ _ _ (by omega), n₂ r (by omega) (by omega) (by omega), gn₁ r (by omega) (by omega) (by omega)]
  · rw [r₆]; show c₄.rreg = c.rreg; rw [r₄]; show c₂.rreg = c.rreg; rw [r₂, gr₁]
  · rw [rm₆]; show c₄.rmem = c.rmem; rw [rm₄]; show c₂.rmem = c.rmem; rw [rm₂, grm₁]
  · rw [o₆]; show c₄.output = c.output; rw [o₄]; show c₂.output = c.output; rw [o₂, go₁]

end NegSSSP

end PlanarFlow
