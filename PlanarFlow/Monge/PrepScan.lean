module

public import PlanarFlow.Monge.DDGBF2O

/-!
# Building the tables of a dense distance graph with missing arcs: scans and half blocks

Pieces of the machine pass `PlanarFlow.Monge.prepO` (`PlanarFlow/Monge/PrepO.lean`), which
computes the static tables `tVal`, `tMul`, `finB` read by `bfDDG2O`:

* `scanDBody`, `scanUBody`: **the first flagged index**, scanning the natural memory downward
  (`A, A - S, A - 2S, …`) or upward (`A, A + S, …`) for a word `≥ 1` among `n` words of
  `0`/`1` flags (`scanD_exec`, `scanU_exec`, within `7 n + 2` steps).
* `hbT b sz t`: the half block of the target `t` at the level `sz` (its targets and sources), as
  the program `bpar` computes it (`bpar_exec`); `hbOf_eq_hbT`: it is the half block `hbOf` of
  every pair `(s, t)` with `s` among its sources; `lev_range`: every pair `s ≠ t` is met at the
  level `2 ^ levOf s t`, with `s` among the sources of the half block of `t`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### Scans -/

/-- One step of the downward scan (`r70` the index, `r72` the address, `r73` the stride, `r74`
the result). -/
def scanDBody : Stmt :=
  .seq (.instr (.loadN 75 72)) (.ifLtN 75 10 (.seq (.instr (.addN 70 70 10))
    (.instr (.subN 72 72 73))) (block [.copyN 74 70, .copyN 70 71]))

/-- One step of the upward scan. -/
def scanUBody : Stmt :=
  .seq (.instr (.loadN 75 72)) (.ifLtN 75 10 (.seq (.instr (.addN 70 70 10))
    (.instr (.addN 72 72 73))) (block [.copyN 74 70, .copyN 70 71]))

/-- The state of a scan of the flags `f` from `c₀`, the `j`-th at `ad j`. -/
structure ISc (W n : ℕ) (ad f : ℕ → ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  nreg : ∀ r, r ≠ 70 → r ≠ 72 → r ≠ 74 → r ≠ 75 → c.nreg r = c₀.nreg r
  rreg : c.rreg = c₀.rreg
  nmem : c.nmem = c₀.nmem
  rmem : c.rmem = c₀.rmem
  out : c.output = c₀.output
  le : c.nreg 70 ≤ n
  st : (c.nreg 74 = n ∧ c.nreg 72 = ad (c.nreg 70) ∧ ∀ j < c.nreg 70, f j = 0) ∨
    (c.nreg 70 = n ∧ c.nreg 74 < n ∧ f (c.nreg 74) = 1 ∧ ∀ j < c.nreg 74, f j = 0)

/-- The end of a scan. -/
theorem ISc.done {n : ℕ} {ad f : ℕ → ℕ} {c₀ c : Config} (h : ISc W n ad f c₀ c)
    (hn : ¬ c.nreg 70 < n) :
    (c.nreg 74 < n ∧ f (c.nreg 74) = 1 ∧ ∀ j < c.nreg 74, f j = 0) ∨
      (c.nreg 74 = n ∧ ∀ j < n, f j = 0) := by
  have := h.le
  rcases h.st with ⟨h1, -, h3⟩ | ⟨-, h2, h3, h4⟩
  · exact Or.inr ⟨h1, fun j hj => h3 j (by omega)⟩
  · exact Or.inl ⟨h2, h3, h4⟩

/-- One step of a scan, generic in the move of the address. -/
theorem scan_step {n : ℕ} {ad f : ℕ → ℕ} {c₀ : Config} (h10 : c₀.nreg 10 = 1)
    (h71 : c₀.nreg 71 = n) (hf : ∀ j < n, c₀.nmem (ad j) = f j) (hf1 : ∀ j < n, f j ≤ 1)
    {mv : Instr} (hmv : ∀ c : Config, WordsBounded W c → ∀ j < n, c.nreg 72 = ad j →
      c.nreg 73 = c₀.nreg 73 →
      Exec P W (.instr mv) c { c with nreg := upd c.nreg 72 (ad (j + 1)) } 1)
    (c : Config) (hI : ISc W n ad f c₀ c) (hlt : c.nreg 70 < c.nreg 71) :
    ∃ c' k', Exec P W (.seq (.instr (.loadN 75 72))
        (.ifLtN 75 10 (.seq (.instr (.addN 70 70 10)) (.instr mv))
          (block [.copyN 74 70, .copyN 70 71]))) c c' k' ∧ ISc W n ad f c₀ c' ∧
      7 * (n - c'.nreg 70) + k' + 2 ≤ 7 * (n - c.nreg 70) := by
  have hc := hI.wb
  have g10 : c.nreg 10 = 1 := (hI.nreg 10 (by omega) (by omega) (by omega) (by omega)).trans h10
  have g71 : c.nreg 71 = n := (hI.nreg 71 (by omega) (by omega) (by omega) (by omega)).trans h71
  rw [g71] at hlt
  generalize hj : c.nreg 70 = j at hlt
  have hst : c.nreg 74 = n ∧ c.nreg 72 = ad j ∧ ∀ j' < j, f j' = 0 := by
    rcases hI.st with h | ⟨h, -⟩
    · rw [hj] at h; exact h
    · omega
  obtain ⟨s74, s72, s0⟩ := hst
  have hfl : c.nmem (c.nreg 72) = f j := by rw [s72, hI.nmem]; exact hf j hlt
  refine spec_seq ?_
  refine spec_instr (Exec.loadN hc 75 72) fun hw₁ => ?_
  by_cases hz : f j = 0
  · refine spec_ifLtN_true (by config_simp; rw [hfl, hz, g10]; omega) ?_
    refine spec_seq ?_
    refine spec_instr (Exec.addN hw₁ 70 70 10 (by
      config_simp; rw [hj, g10]; have := hc.1 71; rw [g71] at this; omega)) fun hw₂ => ?_
    refine spec_instr (hmv _ hw₂ j hlt (by config_simp; exact s72)
      (by config_simp; exact hI.nreg 73 (by omega) (by omega) (by omega) (by omega))) fun hw => ?_
    refine ⟨⟨hw, fun r h1 h2 h3 h4 => ?_, hI.rreg, hI.nmem, hI.rmem, hI.out, ?_,
      Or.inl ⟨?_, ?_, ?_⟩⟩,
      ?_⟩
    · config_simp; simp only [upd_apply]
      split_ifs <;> first | omega | exact hI.nreg r h1 h2 h3 h4
    · config_simp; rw [hj, g10]; omega
    · config_simp; exact s74
    · config_simp; rw [hj, g10]
    · config_simp; rw [hj, g10]
      intro j' hj'
      rcases Nat.lt_or_ge j' j with h | h
      · exact s0 j' h
      · rw [show j' = j by omega]; exact hz
    · config_simp; rw [hj, g10]; omega
  · have h1 : f j = 1 := by have := hf1 j hlt; omega
    refine spec_ifLtN_false (by config_simp; rw [hfl, h1, g10]; omega) ?_
    exec_block
    refine ⟨⟨‹_›, fun r h1 h2 h3 h4 => ?_, hI.rreg, hI.nmem, hI.rmem, hI.out, ?_,
      Or.inr ⟨?_, ?_, ?_, ?_⟩⟩,
      ?_⟩
    · config_simp; simp only [upd_apply]
      split_ifs <;> first | omega | exact hI.nreg r h1 h2 h3 h4
    · config_simp; rw [g71]
    · config_simp; rw [g71]
    · config_simp; rw [hj]; exact hlt
    · config_simp; rw [hj]; exact h1
    · config_simp; rw [hj]; exact s0
    · config_simp; rw [g71]; omega

/-- **The downward scan**: the first `j < n` with the flag at `A - j S` set, or `n`. -/
theorem scanD_exec (c : Config) (hc : WordsBounded W c) {n A S : ℕ} {f : ℕ → ℕ}
    (h10 : c.nreg 10 = 1) (h70 : c.nreg 70 = 0) (h71 : c.nreg 71 = n) (h72 : c.nreg 72 = A)
    (h73 : c.nreg 73 = S) (h74 : c.nreg 74 = n) (hf : ∀ j < n, c.nmem (A - j * S) = f j)
    (hf1 : ∀ j < n, f j ≤ 1) :
    ∃ c' k, Exec P W (.whileLtN 70 71 scanDBody) c c' k ∧ k ≤ 7 * n + 2 ∧
      (((c'.nreg 74 < n ∧ f (c'.nreg 74) = 1 ∧ ∀ j < c'.nreg 74, f j = 0) ∨
        (c'.nreg 74 = n ∧ ∀ j < n, f j = 0)) ∧
      (∀ r, r ≠ 70 → r ≠ 72 → r ≠ 74 → r ≠ 75 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  refine spec_while (ISc W n (fun j => A - j * S) f c) (fun c => 7 * (n - c.nreg 70))
    (fun c h => h.wb) (fun c' hc' hlt => scan_step h10 h71 hf hf1 (fun c hc j _ h72' h73' => by
      have e : c.nreg 72 - c.nreg 73 = A - (j + 1) * S := by
        rw [h72', h73', h73, Nat.sub_sub, Nat.add_mul, Nat.one_mul]
      show Exec P W _ c { c with nreg := upd c.nreg 72 (A - (j + 1) * S) } 1
      rw [← e]; exact Exec.subN hc 72 72 73) c' hc' hlt)
    ⟨hc, fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl, by omega,
      Or.inl ⟨h74, by rw [h72, h70]; simp, fun j hj => by omega⟩⟩ ?_
  intro c' k hI hn hk
  rw [hI.nreg 71 (by omega) (by omega) (by omega) (by omega), h71] at hn
  exact ⟨by rw [h70] at hk; omega, hI.done hn, hI.nreg, hI.rreg, hI.nmem, hI.rmem, hI.out⟩

/-- **The upward scan**: the first `j < n` with the flag at `A + j S` set, or `n`. -/
theorem scanU_exec (c : Config) (hc : WordsBounded W c) {n A S : ℕ} {f : ℕ → ℕ}
    (h10 : c.nreg 10 = 1) (h70 : c.nreg 70 = 0) (h71 : c.nreg 71 = n) (h72 : c.nreg 72 = A)
    (h73 : c.nreg 73 = S) (h74 : c.nreg 74 = n) (hf : ∀ j < n, c.nmem (A + j * S) = f j)
    (hf1 : ∀ j < n, f j ≤ 1) (hW : A + n * S ≤ W) :
    ∃ c' k, Exec P W (.whileLtN 70 71 scanUBody) c c' k ∧ k ≤ 7 * n + 2 ∧
      (((c'.nreg 74 < n ∧ f (c'.nreg 74) = 1 ∧ ∀ j < c'.nreg 74, f j = 0) ∨
        (c'.nreg 74 = n ∧ ∀ j < n, f j = 0)) ∧
      (∀ r, r ≠ 70 → r ≠ 72 → r ≠ 74 → r ≠ 75 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  refine spec_while (ISc W n (fun j => A + j * S) f c) (fun c => 7 * (n - c.nreg 70))
    (fun c h => h.wb) (fun c' hc' hlt => scan_step h10 h71 hf hf1 (fun c hc j hj h72' h73' => by
      have e : c.nreg 72 + c.nreg 73 = A + (j + 1) * S := by
        rw [h72', h73', h73, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      have hjS : (j + 1) * S ≤ n * S := Nat.mul_le_mul_right S (by omega)
      show Exec P W _ c { c with nreg := upd c.nreg 72 (A + (j + 1) * S) } 1
      rw [← e]; exact Exec.addN hc 72 72 73 (by rw [e]; omega)) c' hc' hlt)
    ⟨hc, fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl, by omega,
      Or.inl ⟨h74, by rw [h72, h70]; simp, fun j hj => by omega⟩⟩ ?_
  intro c' k hI hn hk
  rw [hI.nreg 71 (by omega) (by omega) (by omega) (by omega), h71] at hn
  exact ⟨by rw [h70] at hk; omega, hI.done hn, hI.nreg, hI.rreg, hI.nmem, hI.rmem, hI.out⟩

/-! ### The half block of a target at a level -/

/-- `r := min r r1`. -/
theorem minR_exec (r : ℕ) (_hr : r ≠ 1) (c : Config) (hc : WordsBounded W c) :
    ∃ c' k', Exec P W (.ifLtN 1 r (.instr (.copyN r 1)) .skip) c c' k' ∧ k' ≤ 2 ∧
      (c'.nreg r = min (c.nreg r) (c.nreg 1) ∧ (∀ r', r' ≠ r → c'.nreg r' = c.nreg r') ∧
        c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  by_cases h : c.nreg 1 < c.nreg r
  · refine spec_ifLtN_true h ?_
    refine spec_instr (Exec.copyN hc r 1) fun _ => ?_
    refine ⟨le_refl _, ?_, fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; omega
    · config_simp; rw [upd_other _ _ _ hr']
  · refine spec_ifLtN_false h ?_
    refine spec_skip hc ?_
    exact ⟨by omega, by omega, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-- The half block `(r0, nr, c1, nc)` of the target `t` at the level `sz`: the block
`[base, base + 2 sz)` holding `t`, `t` among its targets, the other half its sources. -/
def hbT (b sz t : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  if t < t / (sz + sz) * (sz + sz) + sz then
    (t / (sz + sz) * (sz + sz), sz, min (t / (sz + sz) * (sz + sz) + sz + sz) b,
      min (t / (sz + sz) * (sz + sz) + sz + sz) b - (t / (sz + sz) * (sz + sz) + sz))
  else
    (t / (sz + sz) * (sz + sz) + sz,
      min (t / (sz + sz) * (sz + sz) + sz + sz) b - (t / (sz + sz) * (sz + sz) + sz),
      t / (sz + sz) * (sz + sz) + sz, sz)

/-- The half block of the target `r45` at the level `r44`, into `r46 … r49`. -/
def bpar : Stmt :=
  .seq (block [.addN 51 44 44, .divN 52 45 51, .mulN 52 52 51, .addN 53 52 44, .addN 54 53 44]) <|
  .seq (.ifLtN 1 54 (.instr (.copyN 54 1)) .skip) <|
  .ifLtN 45 53 (block [.copyN 46 52, .copyN 47 44, .copyN 48 54, .subN 49 54 53])
    (block [.copyN 46 53, .subN 47 54 53, .copyN 48 53, .copyN 49 44])

/-- **The half block of a target.** -/
theorem bpar_exec (c : Config) (hc : WordsBounded W c) {b sz t : ℕ} (h1 : c.nreg 1 = b)
    (h44 : c.nreg 44 = sz) (h45 : c.nreg 45 = t) (hW : t + sz + sz ≤ W) :
    ∃ c' k, Exec P W bpar c c' k ∧ k ≤ 13 ∧
      (c'.nreg 46 = (hbT b sz t).1 ∧ c'.nreg 47 = (hbT b sz t).2.1 ∧
        c'.nreg 48 = (hbT b sz t).2.2.1 ∧ c'.nreg 49 = (hbT b sz t).2.2.2 ∧
        (∀ r, r < 46 ∨ 54 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hq := Nat.div_mul_le_self t (sz + sz)
  unfold bpar
  refine spec_seq ?_
  exec_block
  · rw [h44]; omega
  · config_simp; rw [h44, h45]; omega
  · config_simp; rw [h44, h45]; omega
  · config_simp; rw [h44, h45]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded W c₁ := hc₁ ▸ ‹_›
  have g : ∀ r, r < 51 ∨ 54 < r → c₁.nreg r = c.nreg r := fun r hr => by
    rw [← hc₁]; config_simp; upd_tac
  have g53 : c₁.nreg 53 = t / (sz + sz) * (sz + sz) + sz := by
    rw [← hc₁]; config_simp; rw [h44, h45]
  have g52 : c₁.nreg 52 = t / (sz + sz) * (sz + sz) := by rw [← hc₁]; config_simp; rw [h44, h45]
  have g54 : c₁.nreg 54 = t / (sz + sz) * (sz + sz) + sz + sz := by
    rw [← hc₁]; config_simp; rw [h44, h45]
  refine spec_seq ?_
  refine spec_use (minR_exec (P := P) 54 (by omega) c₁ hw₁) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨m54, mn, mr, mnm, mrm, mo⟩
  rw [g54, g 1 (by omega), h1] at m54
  have e2 : ∀ r, r ≠ 54 → r < 51 ∨ 54 < r → c₂.nreg r = c.nreg r := fun r h h' => by
    rw [mn r h, g r h']
  have g53' : c₂.nreg 53 = t / (sz + sz) * (sz + sz) + sz := by rw [mn 53 (by omega), g53]
  have g52' : c₂.nreg 52 = t / (sz + sz) * (sz + sz) := by rw [mn 52 (by omega), g52]
  have g45 : c₂.nreg 45 = t := by rw [e2 45 (by omega) (by omega), h45]
  have g44 : c₂.nreg 44 = sz := by rw [e2 44 (by omega) (by omega), h44]
  unfold hbT
  by_cases hlo : t < t / (sz + sz) * (sz + sz) + sz
  · refine spec_ifLtN_true (by rw [g45, g53']; exact hlo) ?_
    exec_block
    rw [ite_eq_left_of_eq_true _ _ (eq_true hlo)]
    refine ⟨by omega, by config_simp; exact g52', by config_simp; exact g44,
      by config_simp; exact m54, by config_simp; rw [m54, g53'], fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · config_simp; simp only [upd_apply]
      split_ifs <;> first | omega | exact e2 r (by omega) (by omega)
    · rw [mr, ← hc₁]
    · rw [mnm, ← hc₁]
    · rw [mrm, ← hc₁]
    · rw [mo, ← hc₁]
  · refine spec_ifLtN_false (by rw [g45, g53']; exact hlo) ?_
    exec_block
    rw [ite_eq_right_of_eq_false _ _ (eq_false hlo)]
    refine ⟨by omega, by config_simp; exact g53', by config_simp; rw [m54, g53'],
      by config_simp; exact g53', by config_simp; exact g44, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · config_simp; simp only [upd_apply]
      split_ifs <;> first | omega | exact e2 r (by omega) (by omega)
    · rw [mr, ← hc₁]
    · rw [mnm, ← hc₁]
    · rw [mrm, ← hc₁]
    · rw [mo, ← hc₁]

/-! ### The pairs met at a level -/

/-- The level of a pair `s ≠ t` splits them. -/
lemma levOf_spec {s t : ℕ} (h : s ≠ t) :
    s / 2 ^ (levOf s t + 1) = t / 2 ^ (levOf s t + 1) ∧ s / 2 ^ levOf s t ≠ t / 2 ^ levOf s t := by
  classical
  have hex : ∃ T, s / 2 ^ (T + 1) = t / 2 ^ (T + 1) := by
    refine ⟨s + t, ?_⟩
    have h1 : s < 2 ^ (s + t + 1) := lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : t < 2 ^ (s + t + 1) := lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h2]
  have e : levOf s t = Nat.find hex := by unfold levOf; rw [dite_eq_left_of_eq_true (eq_true hex)]
  rw [e]
  refine ⟨Nat.find_spec hex, fun h' => ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0] at h'; simp at h'; exact h h'
  · exact Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      (by rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]; exact h')

/-- The block facts of a target at a level. -/
lemma blk_of {sz t : ℕ} (hsz : 0 < sz) :
    t / (sz + sz) * (sz + sz) ≤ t ∧ t < t / (sz + sz) * (sz + sz) + sz + sz ∧
      t / (sz + sz) * (sz + sz) = 2 * sz * (t / (sz + sz)) := by
  have h1 := Nat.div_add_mod t (sz + sz)
  have h2 := Nat.mod_lt t (show 0 < sz + sz by omega)
  refine ⟨Nat.div_mul_le_self t _, ?_, by ring⟩
  rw [Nat.mul_comm] at h1
  omega

/-- **A source of the half block of `t` at the level `2 ^ T`**: the pair is at that level, and
its half block (`hbOf`) is that of `t` (`hbT`). -/
theorem hbOf_eq_hbT {b sz T t κ : ℕ} (hT : sz = 2 ^ T) (ht : t < b)
    (hκ : κ < (hbT b sz t).2.2.2) :
    hbOf b ((hbT b sz t).2.2.1 - 1 - κ) t = hbT b sz t ∧
      (hbT b sz t).2.2.1 - 1 - κ < b ∧ (hbT b sz t).2.2.1 - 1 - κ ≠ t ∧
      levOf ((hbT b sz t).2.2.1 - 1 - κ) t = T := by
  have hpos : 0 < sz := by rw [hT]; exact Nat.two_pow_pos T
  obtain ⟨h1, h2, h3⟩ := blk_of (t := t) hpos
  generalize hB : t / (sz + sz) * (sz + sz) = base at h1 h2 h3
  generalize hq : t / (sz + sz) = q at h3
  have hm := min_le_left (base + sz + sz) b
  have hm' := min_le_right (base + sz + sz) b
  unfold hbT at hκ ⊢
  rw [hB] at hκ ⊢
  by_cases hlo : t < base + sz
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hlo)] at hκ ⊢
    simp only at hκ ⊢
    have hs := hbOf_second (b := b) (s := min (base + sz + sz) b - 1 - κ) hT h3 h1 hlo
      (by omega) (by omega)
    refine ⟨hs, by omega, by omega, ?_⟩
    have hpos2 : 0 < 2 * sz := by omega
    refine (levOf_block (q := q) hT (by omega) (by omega) (by omega) (by omega) ?_).1
    have e0 : sz * (2 * q) = base := by rw [h3]; ring
    have e1 : sz * (2 * q + 1) = base + sz := by rw [h3]; ring
    rw [div_of_mem hpos (q := 2 * q + 1) (by rw [e1]; omega) (by rw [e1]; omega),
      div_of_mem hpos (q := 2 * q) (by rw [e0]; omega) (by rw [e0]; omega)]
    omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hlo)] at hκ ⊢
    simp only at hκ ⊢
    have hs := hbOf_first (b := b) (s := base + sz - 1 - κ) (t := t) hT h3 (by omega)
      (by omega) (by omega) (by omega)
    refine ⟨hs, by omega, by omega, ?_⟩
    refine (levOf_block (q := q) hT (by omega) (by omega) (by omega) (by omega) ?_).1
    have e0 : sz * (2 * q) = base := by rw [h3]; ring
    have e1 : sz * (2 * q + 1) = base + sz := by rw [h3]; ring
    rw [div_of_mem hpos (q := 2 * q) (by rw [e0]; omega) (by rw [e0]; omega),
      div_of_mem hpos (q := 2 * q + 1) (by rw [e1]; omega) (by rw [e1]; omega)]
    omega

/-- **Every pair `s ≠ t` is met at the level `2 ^ levOf s t < b`**, `s` a source of the half
block of `t`. -/
theorem lev_range {b s t : ℕ} (hs : s < b) (ht : t < b) (hst : s ≠ t) :
    2 ^ levOf s t < b ∧ ∃ κ < (hbT b (2 ^ levOf s t) t).2.2.2,
      s = (hbT b (2 ^ levOf s t) t).2.2.1 - 1 - κ := by
  obtain ⟨h1, h2⟩ := levOf_spec hst
  generalize hsz : 2 ^ levOf s t = sz at h1 h2
  have hpos : 0 < sz := by rw [← hsz]; exact Nat.two_pow_pos _
  have e2 : 2 ^ (levOf s t + 1) = sz + sz := by rw [pow_succ, hsz]; ring
  rw [e2] at h1
  obtain ⟨b1, b2, b3⟩ := blk_of (t := t) hpos
  obtain ⟨c1', c2', -⟩ := blk_of (t := s) hpos
  rw [h1] at c1' c2'
  generalize hB : t / (sz + sz) * (sz + sz) = base at b1 b2 b3 c1' c2'
  generalize hq : t / (sz + sz) = q at b3
  have hsb : sz < b := by
    by_contra hc
    exact h2 (by
      rw [Nat.div_eq_of_lt (show s < sz by omega), Nat.div_eq_of_lt (show t < sz by omega)])
  refine ⟨hsb, ?_⟩
  unfold hbT
  rw [hB]
  have e0 : sz * (2 * q) = base := by rw [b3]; ring
  have e1 : sz * (2 * q + 1) = base + sz := by rw [b3]; ring
  have hdiv : ∀ x, base ≤ x → x < base + sz → x / sz = 2 * q := fun x h h' =>
    div_of_mem hpos (by rw [e0]; omega) (by rw [e0]; omega)
  have hdiv' : ∀ x, base + sz ≤ x → x < base + sz + sz → x / sz = 2 * q + 1 := fun x h h' =>
    div_of_mem hpos (by rw [e1]; omega) (by rw [e1]; omega)
  by_cases hlo : t < base + sz
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hlo)]
    simp only
    have hs2 : base + sz ≤ s := by
      by_contra hc; exact h2 (by rw [hdiv s c1' (by omega), hdiv t b1 hlo])
    exact ⟨min (base + sz + sz) b - 1 - s, by omega, by omega⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hlo)]
    simp only
    have hs2 : s < base + sz := by
      by_contra hc; exact h2 (by rw [hdiv' s (by omega) c2', hdiv' t (by omega) b2])
    exact ⟨base + sz - 1 - s, by omega, by omega⟩

end Monge

end PlanarFlow
