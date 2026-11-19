module

public import PlanarFlow.BKMNW.SgP

/-!
# The parts of the separator on the machine: the three stages of `sgProg`

* pure: `sg_cnt_pd` (the count of the nonzero `PD` cells is `ρ.k + 1`), `cnt_le_n`,
  **`runIdx_sum_len`** (`Σ (e - a) + 2 · #runs ≤ k + 2 - s`), **`runIdx_pair_le`**
  (`a ≤ e ≤ k` for every pair);
* **`sgP1_exec`** (steps 1–3: `k`, the hole labels `HF` of the path's vertices, the inverse `FXI`
  of `FX`; `23 n' + 7 m + 30` steps);
* **`sgP2_exec`** (steps 4–5: the runs, `Gb := s`, offsets and lengths; `37 n' + 30` steps);
* **`sgP3_exec`** (steps 6–8: the darts of the runs, then their start vertices, as frame
  indices; `40 n' + 30` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

lemma sg_cnt_pd {F : ℕ → ℕ} {n k : ℕ} (hk : k < n) (h1 : ∀ j ≤ k, 0 < F j)
    (h0 : ∀ j < n, k < j → F j = 0) : cnt F n = k + 1 := by
  unfold cnt
  have : (range n).filter (fun j => 0 < F j) = range (k + 1) := by
    ext j
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨h, hp⟩
      by_contra hc
      have := h0 j h (by omega)
      omega
    · intro h
      exact ⟨by omega, h1 j (by omega)⟩
  rw [this, card_range]

lemma cnt_le_n (F : ℕ → ℕ) (n : ℕ) : cnt F n ≤ n := by
  unfold cnt
  exact (card_filter_le _ _).trans (card_range n).le

/-- **The lengths and the number of the runs**: `Σ (e - a) + 2 · #runs ≤ k + 2 - s`. -/
lemma runIdx_sum_len (H : ℕ → Bool) (k : ℕ) : ∀ s,
    ((runIdx H k s).map fun p => p.2 - p.1).sum + 2 * (runIdx H k s).length ≤ k + 2 - s := by
  intro s
  induction hn : k + 1 - s using Nat.strong_induction_on generalizing s with
  | _ N ih =>
    by_cases hks : k < s
    · rw [runIdx_of_lt H hks]; simp
    by_cases hHs : H s = true
    · rw [runIdx_of_mem H (by omega) hHs]
      have := ih (k + 1 - (s + 1)) (by omega) (s + 1) rfl
      omega
    · have hHs' : H s = false := by simpa using hHs
      rw [runIdx_of_not_mem H (by omega) hHs']
      have hsb := runEndF_ge H k s
      have hbk := runEndF_le_k H (k := k) (s := s) (by omega)
      have := ih (k + 1 - (runEndF H k s + 2)) (by omega) _ rfl
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- **The pairs of the runs**: `s ≤ a ≤ e ≤ k`. -/
lemma runIdx_pair_le (H : ℕ → Bool) (k : ℕ) : ∀ s, ∀ p ∈ runIdx H k s,
    s ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ k := by
  intro s
  induction hn : k + 1 - s using Nat.strong_induction_on generalizing s with
  | _ N ih =>
    intro p hp
    by_cases hks : k < s
    · rw [runIdx_of_lt H hks] at hp; simp at hp
    by_cases hHs : H s = true
    · rw [runIdx_of_mem H (by omega) hHs] at hp
      have := ih (k + 1 - (s + 1)) (by omega) (s + 1) rfl p hp
      omega
    · have hHs' : H s = false := by simpa using hHs
      rw [runIdx_of_not_mem H (by omega) hHs'] at hp
      have hsb := runEndF_ge H k s
      have hbk := runEndF_le_k H (k := k) (s := s) (by omega)
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨le_rfl, hsb, hbk⟩
      · have := ih (k + 1 - (runEndF H k s + 2)) (by omega) _ rfl p hp
        omega

lemma runIdx_getD_le (H : ℕ → Bool) (k : ℕ) {j : ℕ} (hj : j < (runIdx H k 0).length) :
    ((runIdx H k 0).getD j (0, 0)).1 ≤ ((runIdx H k 0).getD j (0, 0)).2 ∧
      ((runIdx H k 0).getD j (0, 0)).2 ≤ k := by
  rw [List.getD_eq_getElem _ _ hj]
  have := runIdx_pair_le H k 0 _ (List.getElem_mem hj)
  omega

section Exec

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **Steps 1–3 of `sgProg`**: `k = r7219`, `HF[j] = HP[IX[PD[j] - 1]]` at `Z + 2 n'`, the
inverse of `FX` at `Z + 3 n'`. -/
theorem sgP1_exec (c : Config) (hc : WordsBounded W c) {n' PDb IXb HPb m FXb Z Gb n k : ℕ}
    (r00 : c.nreg 7200 = n') (r01 : c.nreg 7201 = PDb) (r02 : c.nreg 7202 = IXb)
    (r03 : c.nreg 7203 = HPb) (r04 : c.nreg 7204 = m) (r05 : c.nreg 7205 = FXb)
    (r06 : c.nreg 7206 = Z) (r07 : c.nreg 7207 = Gb) (r08 : c.nreg 7208 = n)
    (r21 : c.nreg 6521 = 1)
    (hk : k < n') (hpd : ∀ j ≤ k, 1 ≤ c.nmem (PDb + j) ∧ c.nmem (PDb + j) ≤ n')
    (hpd0 : ∀ j < n', k < j → c.nmem (PDb + j) = 0)
    (hix : ∀ q < n', c.nmem (IXb + q) < n) (hfx : ∀ f < m, c.nmem (FXb + f) < n)
    (hinj : ∀ i < m, ∀ j < m, c.nmem (FXb + i) = c.nmem (FXb + j) → i = j)
    (lay : PDb + n' ≤ Z ∧ IXb + n' ≤ Z ∧ HPb + n ≤ Z ∧ FXb + m ≤ Z ∧ Z + 8 * n' + n + 2 ≤ W)
    (hm : m + 1 ≤ W) :
    ∃ c' t, Exec P W sgP1 c c' t ∧ t ≤ 23 * n' + 7 * m + 30 ∧
      SgRegs c' n' PDb IXb HPb m FXb Z Gb n ∧ c'.nreg 7219 = k ∧
      (∀ j < n', c'.nmem (Z + 2 * n' + j) =
        c.nmem (HPb + c.nmem (IXb + (c.nmem (PDb + j) - 1)))) ∧
      (∀ f < m, c'.nmem (Z + 3 * n' + c.nmem (FXb + f)) = f) ∧
      (∀ a, ¬ (Z ≤ a ∧ a < Z + 3 * n' + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4600 ∨ (4605 < x ∧ x < 6300) ∨ (6309 < x ∧ x < 6520) ∨ x = 6521 ∨
        (6529 < x ∧ x < 7210) ∨ 7219 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := lay
  have hp1 : ∀ j < n', c.nmem (PDb + j) - 1 < n' := fun j hj => by
    by_cases h : j ≤ k
    · have := hpd j h; omega
    · rw [hpd0 j hj (by omega)]; omega
  unfold sgP1
  obtain ⟨c₁, t₁, e₁, ht₁, R1, a0, a1, a2, a3, m1, n1, rr1, rm1, o1⟩ := sqA_exec (P := P) c hc
    r00 r01 r02 r03 r04 r05 r06 r07 r08 r21 (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, b6, -, bm, bn, br, brm, bo⟩ := lkProg_exec (P := P) c₁ e₁.wb_right
    a0 a1 a2 a3 (by omega) (by omega) (by omega) (by omega)
  have hcnt : cnt (fun j => c₁.nmem (PDb + j)) n' = k + 1 := by
    rw [m1]; exact sg_cnt_pd hk (fun j hj => by have := hpd j hj; omega) hpd0
  have R2 := R1.congr fun x hx => bn x (by unfold sgReg at hx; omega)
  have m2 : ∀ a, a < Z → c₂.nmem a = c.nmem a := fun a ha => by rw [bm a (by omega), m1]
  obtain ⟨c₃, t₃, e₃, ht₃, d19, d00, d01, d02, m3, n3, rr3, rm3, o3⟩ := sqB_exec (P := P) c₂
    e₂.wb_right (by rw [b6, hcnt]) R2.r21 R2.r04 R2.r05 R2.r12
  have R3 := R2.congr fun x hx => n3 x (by unfold sgReg at hx; omega)
    (by unfold sgReg at hx; omega)
  -- the hole labels of the path's vertices
  obtain ⟨c₄, t₄, e₄, ht₄, f4, fm4, fn4, fr4, frm4, fo4⟩ := mapRun_exec (P := P) c₃ e₃.wb_right
    (vb := vbSHF) (bnd := 7200) (ob := 7211) (m := n') (Ob := Z + 2 * n') (B := 7)
    (fun j => c.nmem (HPb + c.nmem (IXb + (c.nmem (PDb + j) - 1)))) R3.r00 R3.r21 R3.r11
    (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega)
    (by omega) (by omega)
    (fun j hj c' hw h20 hr hm => by
      have g : ∀ x, sgReg x → c'.nreg x = c₃.nreg x := fun x hx =>
        hr x (by unfold vscr; unfold sgReg at hx; omega) (by unfold sgReg at hx; omega)
          (by unfold sgReg at hx; omega)
      have R' := R3.congr g
      have mm : ∀ a, a < Z → c'.nmem a = c.nmem a := fun a ha => by
        rw [hm a (by omega), m3, m2 a ha]
      have hq := hp1 j hj
      have hx := hix _ hq
      obtain ⟨c'', k', e', hk', v, nn, mm', rr, rm, oo⟩ := vbSHF_exec (P := P) c' hw h20
        R'.r01 R'.r02 R'.r03 R'.r21 (mm _ (by omega)) (mm _ (by omega)) (mm _ (by omega))
        (by omega) (by omega) (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm', rr, rm, oo⟩)
  have q4 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₄.nreg x = c₃.nreg x := fn4
  have m4 : ∀ a, a < Z → c₄.nmem a = c.nmem a := fun a ha => by
    rw [fm4 a (by omega), m3, m2 a ha]
  -- the inverse of `FX`
  obtain ⟨c₅, t₅, e₅, ht₅, g5, gm5, gn5, gr5, grm5, go5⟩ := invProg_exec (P := P) c₄ e₄.wb_right
    (m := m) (Pb := FXb) (OUTb := Z + 3 * n')
    (by rw [q4 _ (by unfold vscr; omega) (by omega) (by omega)]; exact d00)
    (by rw [q4 _ (by unfold vscr; omega) (by omega) (by omega)]; exact d01)
    (by rw [q4 _ (by unfold vscr; omega) (by omega) (by omega)]; exact d02)
    (by omega) hm (fun j hj => by rw [m4 _ (by omega)]; have := hfx j hj; omega)
    (fun i hi j hj h => hinj i hi j hj (by rw [m4 _ (by omega), m4 _ (by omega)] at h; exact h))
    (fun i hi j hj => by rw [m4 _ (by omega)]; omega)
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_, R3.congr fun x hx => ?_, ?_,
    fun j hj => ?_, fun f hf => ?_, fun a ha => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · clear * - ht₁ ht₂ ht₃ ht₄ ht₅; omega
  · rw [gn5 x (by unfold sgReg at hx; omega), q4 x (by unfold vscr; unfold sgReg at hx; omega)
      (by unfold sgReg at hx; omega) (by unfold sgReg at hx; omega)]
  · rw [gn5 _ (by omega), q4 _ (by unfold vscr; omega) (by omega) (by omega)]; exact d19
  · rw [gm5 _ (fun i hi => by rw [m4 _ (by omega)]; omega)]; exact f4 j hj
  · have := g5 f hf; rw [m4 _ (by omega)] at this; exact this
  · rw [gm5 _ (fun i hi => by rw [m4 _ (by omega)]; have := hfx i hi; omega),
      fm4 a (by omega), m3, bm a (by omega), m1]
  · rw [gn5 x (by omega), q4 x (by unfold vscr; omega) (by omega) (by omega),
      n3 x (by omega) (by omega), bn x (by omega), n1 x (by omega)]
  · rw [gr5, fr4, rr3, br, rr1]
  · rw [grm5, frm4, rm3, brm, rm1]
  · rw [go5, fo4, o3, bo, o1]

set_option maxHeartbeats 2000000 in
/-- **Steps 4–5 of `sgProg`**: the runs `R` of the flags `HF` (at `Z + 2 n'`) as pairs at
`Ob = Z + 3 n' + n`, `Gb := #R`, the offsets `sgOff R j` at `Gb + 1 + j` and the lengths
`sgLen R j` at `Gb + 1 + #R + j`. -/
theorem sgP2_exec (c : Config) (hc : WordsBounded W c) {n' PDb IXb HPb m FXb Z Gb n k : ℕ}
    (hR : SgRegs c n' PDb IXb HPb m FXb Z Gb n) (r19 : c.nreg 7219 = k) (hk : k < n')
    (hn : 1 ≤ n) (lay : Gb + 2 * n' + 3 ≤ Z ∧ Z + 8 * n' + n + 2 ≤ W) (R : List (ℕ × ℕ))
    (hRd : R = runIdx (fun j => decide (0 < c.nmem (Z + 2 * n' + j))) k 0) :
    ∃ c' t, Exec P W sgP2 c c' t ∧ t ≤ 37 * n' + 30 ∧
      SgRegs c' n' PDb IXb HPb m FXb Z Gb n ∧ c'.nreg 7219 = k ∧ c'.nreg 7220 = R.length ∧
      c'.nreg 7224 = Gb + 1 + R.length ∧ c'.nreg 7222 = sgOff R R.length ∧
      c'.nmem Gb = R.length ∧
      (∀ j < R.length, c'.nmem (Gb + 1 + j) = sgOff R j ∧
        c'.nmem (Gb + 1 + R.length + j) = sgLen R j) ∧
      RnMem c'.nmem (Z + 3 * n' + n) R ∧
      (∀ a, ¬ (Gb ≤ a ∧ a < Gb + 1 + 2 * R.length) →
        ¬ (Z + 3 * n' + n ≤ a ∧ a < Z + 3 * n' + n + 2 * R.length) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4100 ∨ (4113 < x ∧ x < 7220) ∨ 7228 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2⟩ := lay
  have hsl := runIdx_sum_len (fun j => decide (0 < c.nmem (Z + 2 * n' + j))) k 0
  rw [← hRd] at hsl
  unfold sgP2
  obtain ⟨c₁, t₁, e₁, ht₁, a0, a1, a2, m1, n1, rr1, rm1, o1⟩ := sqC_exec (P := P) c hc r19
    hR.r11 hR.r13
  obtain ⟨c₂, t₂, e₂, ht₂, b8, bR, bm, bn, br, brm, bo⟩ := rnProg_exec (P := P) c₁ e₁.wb_right
    a0 a1 a2 (by omega) (by omega)
  rw [m1, ← hRd] at b8 bR
  have R2 := hR.congr fun x hx => by rw [bn x (by unfold sgReg at hx; omega),
    n1 x (by unfold sgReg at hx; omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, d20, d21, d22, d23, d24, dm, dn, dr, drm, do'⟩ := sqD_exec (P := P) c₂
    e₂.wb_right b8 R2.r07 R2.r21 (by omega)
  have R3 := R2.congr fun x hx => dn x (by unfold sgReg at hx; omega)
  have hR3 : RnMem c₃.nmem (Z + 3 * n' + n) R := fun j hj => by
    rw [dm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact bR j hj
  obtain ⟨c₄, t₄, e₄, ht₄, g22, g, gm, gn, gr, grm, go⟩ := sgL_exec (P := P) c₃ e₃.wb_right
    (s := R.length) (Ob := Z + 3 * n' + n) (Gb := Gb) R d20 d21 d22 R3.r13 d23 d24 R3.r21 rfl hR3
    (by omega) (by omega) (by omega)
  have q4 : ∀ x, sgReg x → c₄.nreg x = c₃.nreg x := fun x hx =>
    gn x (by unfold sgReg at hx; omega)
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_, R3.congr q4, ?_, ?_, ?_, g22, ?_, g,
    fun j hj => ?_, fun a h1 h2 => ?_, fun x hx => ?_, by rw [gr, dr, br, rr1],
    by rw [grm, drm, brm, rm1], by rw [go, do', bo, o1]⟩
  · clear * - ht₁ ht₂ ht₃ ht₄ hsl hk; omega
  · rw [gn _ (by omega), dn _ (by omega), bn _ (by omega), n1 _ (by omega)]; exact r19
  · rw [gn _ (by omega)]; exact d20
  · rw [gn _ (by omega)]; exact d24
  · rw [gm _ (by omega), dm, upd_same]
  · rw [gm (Z + 3 * n' + n + 2 * j) (by omega), gm (Z + 3 * n' + n + 2 * j + 1) (by omega)]
    exact hR3 j hj
  · rw [gm _ (by omega), dm, upd_other _ _ _ (by omega), bm _ (by omega), m1]
  · rw [gn _ (by omega), dn _ (by omega), bn _ (by omega), n1 _ (by omega)]

set_option maxHeartbeats 4000000 in
/-- **Steps 6–8 of `sgProg`**: with `F t = rfV HF[t] HF[t+1]` (the darts of the runs), the frame
index `FXI[IX[PD[t] - 1]]` of a flagged dart `t < k` at `Gb + 1 + 2 s + cnt F t` (when
`cnt F t < L`), and the start vertex `FXI[IX[PD[a_j] - 1]]` of the run `j` at
`Gb + 1 + 2 s + L + j`; `r6502 = Gb`. -/
theorem sgP3_exec (c : Config) (hc : WordsBounded W c) {n' PDb IXb HPb m FXb Z Gb n k s L : ℕ}
    (hR : SgRegs c n' PDb IXb HPb m FXb Z Gb n) (r19 : c.nreg 7219 = k) (r20 : c.nreg 7220 = s)
    (r22 : c.nreg 7222 = L) (r24 : c.nreg 7224 = Gb + 1 + s) (hk : k < n') (hL : L + 2 * s ≤ k + 2)
    (hpd : ∀ j ≤ k, 1 ≤ c.nmem (PDb + j) ∧ c.nmem (PDb + j) ≤ n')
    (hix : ∀ q < n', c.nmem (IXb + q) < n) (ha : ∀ j < s, c.nmem (Z + 3 * n' + n + 2 * j) ≤ k)
    (lay : PDb + n' ≤ Gb ∧ IXb + n' ≤ Gb ∧ Gb + 2 * n' + 3 ≤ Z ∧ Z + 8 * n' + n + 2 ≤ W) :
    ∃ c' t, Exec P W sgP3 c c' t ∧ t ≤ 50 * n' + 40 ∧
      (∀ t < k, 0 < rfV (c.nmem (Z + 2 * n' + t)) (c.nmem (Z + 2 * n' + t + 1)) →
        cnt (fun j => rfV (c.nmem (Z + 2 * n' + j)) (c.nmem (Z + 2 * n' + j + 1))) t < L →
        c'.nmem (Gb + 1 + 2 * s +
          cnt (fun j => rfV (c.nmem (Z + 2 * n' + j)) (c.nmem (Z + 2 * n' + j + 1))) t) =
          c.nmem (Z + 3 * n' + c.nmem (IXb + (c.nmem (PDb + t) - 1)))) ∧
      (∀ j < s, c'.nmem (Gb + 1 + 2 * s + L + j) = c.nmem (Z + 3 * n' +
        c.nmem (IXb + (c.nmem (PDb + c.nmem (Z + 3 * n' + n + 2 * j)) - 1)))) ∧
      c'.nreg 6502 = Gb ∧
      (∀ a, ¬ (Gb + 1 + 2 * s ≤ a ∧ a < Gb + 2 * n' + 3) →
        ¬ (Z + 5 * n' + n + 1 ≤ a ∧ a < Z + 8 * n' + n + 1) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6300 ∨ (6309 < x ∧ x < 6502) ∨ (6502 < x ∧ x < 6520) ∨ x = 6521 ∨
        (6529 < x ∧ x < 7217) ∨ (7218 < x ∧ x < 7229) ∨ 7229 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4⟩ := lay
  set F : ℕ → ℕ := fun j => rfV (c.nmem (Z + 2 * n' + j)) (c.nmem (Z + 2 * n' + j + 1)) with hF
  unfold sgP3
  -- the flags of the darts of the runs
  obtain ⟨c₁, t₁, e₁, ht₁, f1, fm1, fn1, fr1, frm1, fo1⟩ := mapRun_exec (P := P) c hc
    (vb := vbSRF) (bnd := 7219) (ob := 7214) (m := k) (Ob := Z + 5 * n' + n + 1) (B := 9) F
    r19 hR.r21 hR.r14 (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega)
    (by omega) (by omega) (by omega) (by omega)
    (fun t ht c' hw h20 hr hm => by
      have g : ∀ x, sgReg x → c'.nreg x = c.nreg x := fun x hx =>
        hr x (by unfold vscr; unfold sgReg at hx; omega) (by unfold sgReg at hx; omega)
          (by unfold sgReg at hx; omega)
      have R' := hR.congr g
      obtain ⟨c'', k', e', hk', v, nn, mm', rr, rm, oo⟩ := vbSRF_exec (P := P) c' hw h20
        R'.r11 R'.r21 (hm _ (by omega)) (hm _ (by omega)) (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm', rr, rm, oo⟩)
  have q1 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₁.nreg x = c.nreg x := fn1
  have R1 := hR.congr fun x hx => q1 x (by unfold vscr; unfold sgReg at hx; omega)
    (by unfold sgReg at hx; omega) (by unfold sgReg at hx; omega)
  have s19 : c₁.nreg 7219 = k := (q1 7219 (by unfold vscr; omega) (by omega) (by omega)).trans r19
  have s20 : c₁.nreg 7220 = s := (q1 7220 (by unfold vscr; omega) (by omega) (by omega)).trans r20
  have s22 : c₁.nreg 7222 = L := (q1 7222 (by unfold vscr; omega) (by omega) (by omega)).trans r22
  have s24 : c₁.nreg 7224 = Gb + 1 + s :=
    (q1 7224 (by unfold vscr; omega) (by omega) (by omega)).trans r24
  obtain ⟨c₂, t₂, e₂, ht₂, b0, b1, b2, b3, bm, bn, br, brm, bo⟩ := sqE_exec (P := P) c₁
    e₁.wb_right s19 R1.r14 R1.r15 R1.r16
  -- the compaction of the darts
  obtain ⟨c₃, t₃, e₃, ht₃, d6, dIX, dm, dn, dr, drm, do'⟩ := lkProg_exec (P := P) c₂ e₂.wb_right
    b0 b1 b2 b3 (by omega) (by omega) (by omega) (by omega)
  have hFe : ∀ j < k, c₂.nmem (Z + 5 * n' + n + 1 + j) = F j := fun j hj => by
    rw [bm]; exact f1 j hj
  have hcnt : ∀ i ≤ k, cnt (fun j => c₂.nmem (Z + 5 * n' + n + 1 + j)) i = cnt F i := fun i hi =>
    cnt_ext fun j hj => hFe j (by omega)
  have htot : cnt F k ≤ k := cnt_le_n F k
  have hIX : ∀ i < k, 0 < F i → c₃.nmem (Z + 7 * n' + n + 1 + cnt F i) = i := fun i hi hpos => by
    have := (dIX i hi (by rw [hFe i hi]; exact hpos)).2
    rw [hcnt i hi.le] at this; exact this
  have hIXl : ∀ q < cnt F k, c₃.nmem (Z + 7 * n' + n + 1 + q) < k := fun q hq => by
    obtain ⟨i, hi, hpos, rfl⟩ := cnt_surj F k q hq
    rw [hIX i hi hpos]; exact hi
  have q3 : ∀ x, (x < 6300 ∨ 6309 < x) → c₃.nreg x = c₁.nreg x := fun x hx => by
    rw [dn x (by omega), bn x (by omega)]
  have m3 : ∀ a, (a < Z + 6 * n' + n + 1 ∨ Z + 8 * n' + n + 1 ≤ a) → c₃.nmem a = c₁.nmem a :=
    fun a ha => by rw [dm a (by omega), bm]
  have R3 := R1.congr fun x hx => q3 x (by unfold sgReg at hx; omega)
  obtain ⟨c₄, t₄, e₄, ht₄, g17, g18, g02, g29, gm, gn, gr, grm, go⟩ := sqF_exec (P := P) c₃
    e₃.wb_right ((q3 7224 (by omega)).trans s24) ((q3 7220 (by omega)).trans s20)
    (by rw [d6, hcnt k le_rfl]) R3.r07 ((q3 7222 (by omega)).trans s22) (by omega)
  have R4 := R3.congr fun x hx => gn x (by unfold sgReg at hx; omega)
    (by unfold sgReg at hx; omega) (by unfold sgReg at hx; omega) (by unfold sgReg at hx; omega)
  have m4 : ∀ a, (a < Z + 5 * n' + n + 1 ∨ Z + 8 * n' + n + 1 ≤ a) → c₄.nmem a = c.nmem a :=
    fun a ha => by rw [gm, m3 a (by omega), fm1 a (by omega)]
  -- the darts
  obtain ⟨c₅, t₅, e₅, ht₅, h5, hm5, hn5, hr5, hrm5, ho5⟩ := mapRun_exec (P := P) c₄ e₄.wb_right
    (vb := vbSDT) (bnd := 7218) (ob := 7217) (m := cnt F k) (Ob := Gb + 1 + s + s) (B := 9)
    (fun q => c.nmem (Z + 3 * n' + c.nmem (IXb + (c.nmem (PDb +
      c₄.nmem (Z + 7 * n' + n + 1 + q)) - 1)))) g18 R4.r21 g17 (by omega) (by omega)
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun q hq c' hw h20 hr hm => by
      have g : ∀ x, sgReg x → c'.nreg x = c₄.nreg x := fun x hx =>
        hr x (by unfold vscr; unfold sgReg at hx; omega) (by unfold sgReg at hx; omega)
          (by unfold sgReg at hx; omega)
      have R' := R4.congr g
      have ht := hIXl q hq
      have e1 : c₄.nmem (Z + 7 * n' + n + 1 + q) = c₃.nmem (Z + 7 * n' + n + 1 + q) := by rw [gm]
      rw [← e1] at ht
      have hp := hpd (c₄.nmem (Z + 7 * n' + n + 1 + q)) ht.le
      have hx := hix (c.nmem (PDb + c₄.nmem (Z + 7 * n' + n + 1 + q)) - 1) (by omega)
      obtain ⟨c'', k', e', hk', v, nn, mm', rr, rm, oo⟩ := vbSDT_exec (P := P) c' hw h20
        (t := c₄.nmem (Z + 7 * n' + n + 1 + q))
        (p := c.nmem (PDb + c₄.nmem (Z + 7 * n' + n + 1 + q)))
        (x := c.nmem (IXb + (c.nmem (PDb + c₄.nmem (Z + 7 * n' + n + 1 + q)) - 1)))
        (f := c.nmem (Z + 3 * n' +
          c.nmem (IXb + (c.nmem (PDb + c₄.nmem (Z + 7 * n' + n + 1 + q)) - 1))))
        R'.r16 R'.r01 R'.r02 R'.r12 R'.r21 (hm _ (by omega))
        (by rw [hm _ (by omega), m4 _ (by omega)])
        (by rw [hm _ (by omega), m4 _ (by omega)])
        (by rw [hm _ (by omega), m4 _ (by omega)]) (by omega) (by omega) (by omega) (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm', rr, rm, oo⟩)
  have q5 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₅.nreg x = c₄.nreg x := hn5
  have R5 := R4.congr fun x hx => q5 x (by unfold vscr; unfold sgReg at hx; omega)
    (by unfold sgReg at hx; omega) (by unfold sgReg at hx; omega)
  have m5 : ∀ a, (a < Gb + 1 + s + s ∨ Gb + 1 + s + s + k ≤ a) →
      (a < Z + 5 * n' + n + 1 ∨ Z + 8 * n' + n + 1 ≤ a) → c₅.nmem a = c.nmem a :=
    fun a h1 h2 => by rw [hm5 a (by omega), m4 a h2]
  -- the start vertices
  obtain ⟨c₆, t₆, e₆, ht₆, h6, hm6, hn6, hr6, hrm6, ho6⟩ := mapRun_exec (P := P) c₅ e₅.wb_right
    (vb := vbSPV) (bnd := 7220) (ob := 7229) (m := s) (Ob := Gb + 1 + s + s + L) (B := 10)
    (fun j => c.nmem (Z + 3 * n' +
      c.nmem (IXb + (c.nmem (PDb + c.nmem (Z + 3 * n' + n + 2 * j)) - 1))))
    ((q5 7220 (by unfold vscr; omega) (by omega) (by omega)).trans
      ((gn 7220 (by omega) (by omega) (by omega) (by omega)).trans ((q3 7220 (by omega)).trans s20)))
    R5.r21 ((q5 7229 (by unfold vscr; omega) (by omega) (by omega)).trans g29) (by omega) (by omega)
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun j hj c' hw h20 hr hm => by
      have g : ∀ x, sgReg x → c'.nreg x = c₅.nreg x := fun x hx =>
        hr x (by unfold vscr; unfold sgReg at hx; omega) (by unfold sgReg at hx; omega)
          (by unfold sgReg at hx; omega)
      have R' := R5.congr g
      have haj := ha j hj
      have hp := hpd _ haj
      have hx := hix (c.nmem (PDb + c.nmem (Z + 3 * n' + n + 2 * j)) - 1) (by omega)
      obtain ⟨c'', k', e', hk', v, nn, mm', rr, rm, oo⟩ := vbSPV_exec (P := P) c' hw h20
        (a := c.nmem (Z + 3 * n' + n + 2 * j))
        (p := c.nmem (PDb + c.nmem (Z + 3 * n' + n + 2 * j)))
        (x := c.nmem (IXb + (c.nmem (PDb + c.nmem (Z + 3 * n' + n + 2 * j)) - 1)))
        (f := c.nmem (Z + 3 * n' +
          c.nmem (IXb + (c.nmem (PDb + c.nmem (Z + 3 * n' + n + 2 * j)) - 1))))
        R'.r13 R'.r01 R'.r02 R'.r12 R'.r21
        (by rw [hm _ (by omega), m5 _ (by omega) (by omega)])
        (by rw [hm _ (by omega), m5 _ (by omega) (by omega)])
        (by rw [hm _ (by omega), m5 _ (by omega) (by omega)])
        (by rw [hm _ (by omega), m5 _ (by omega) (by omega)]) (by omega) (by omega) (by omega)
        (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm', rr, rm, oo⟩)
  refine ⟨c₆, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ?_, fun t ht hpos hlt => ?_,
    fun j hj => ?_, ?_, fun a h1 h2 => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ htot hL hk; omega
  · have hct : cnt F t < cnt F k := cnt_lt_of F ht hpos
    rw [show Gb + 1 + 2 * s + cnt F t = Gb + 1 + s + s + cnt F t by omega,
      hm6 _ (by omega), h5 _ hct, gm, hIX t ht hpos]
  · rw [show Gb + 1 + 2 * s + L + j = Gb + 1 + s + s + L + j by omega]; exact h6 j hj
  · rw [hn6 6502 (by unfold vscr; omega) (by omega) (by omega),
      q5 6502 (by unfold vscr; omega) (by omega) (by omega)]; exact g02
  · rw [hm6 a (by omega), m5 a (by omega) (by omega)]
  · rw [hn6 x (by unfold vscr; omega) (by omega) (by omega), q5 x (by unfold vscr; omega)
      (by omega) (by omega), gn x (by omega) (by omega) (by omega) (by omega), q3 x (by omega),
      q1 x (by unfold vscr; omega) (by omega) (by omega)]
  · rw [hr6, hr5, gr, dr, br, fr1]
  · rw [hrm6, hrm5, grm, drm, brm, frm1]
  · rw [ho6, ho5, go, do', bo, fo1]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
