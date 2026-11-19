module

public import PlanarFlow.NegSSSP.Enc.VTree

/-!
# Small natural-word programs for the composed encoder

Programs whose constants (addresses, lengths, values) are fixed in the program text, as for the
node's `kPartN`:

* `feSet l`: the registers `r` of the pairs `(r, v) ∈ l` set to `v` (`feSet_exec`).
* `feFill Dst len v`: `nmem[Dst + e] := v` for `e < len` (`feFill_exec`, `5 len + 7`
  steps). With `v = 1` it writes the **array of ones** (the keep flags of all the darts) that the
  search of `vtSearch_exec` reads.
* `feClamp Dst len B`: `nmem[Dst + e] := min (nmem[Dst + e]) B` for `e < len`
  (`feClamp_exec`, `8 len + 7` steps): every word of a window bounded by `B`, the words already
  `≤ B` kept.
* `feGather Out In Mk len`: `nmem[Out + i] := nmem[Mk + nmem[In + i]]` for `i < len`
  (`feGather_exec`, `9 len + 7` steps): the reach bits of the targets (`XR`) or of the tails of
  the darts, from the marks of a search.
* `feCpyCell dst src`, `feStore a v`: one word copied, one constant stored.

Registers: natural `2450 … 2459`. No real register or real memory is touched; all programs are
natural-only (`*_natOnly`, by `kernel_rfl`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### Setting registers -/

/-- The block setting the registers of the pairs of `l`. -/
def feSet (l : List (ℕ × ℕ)) : Stmt := block (l.map fun p => .constN p.1 p.2)

/-- The value of the register `r` after `feSet l` from the value `x`. -/
def feSetV : List (ℕ × ℕ) → ℕ → ℕ → ℕ
  | [], _, x => x
  | p :: l, r, x => feSetV l r (if r = p.1 then p.2 else x)

theorem feSet_natOnly (l : List (ℕ × ℕ)) : Klein.natOnly (feSet l) = true := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [feSet, List.map_cons] at ih ⊢
    simpa [block, Klein.natOnly, Instr.isReal] using ih

theorem feSet_exec (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.2 ≤ W) (c : Config)
    (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (feSet l) c c' k ∧ k = l.length ∧
      (∀ r, c'.nreg r = feSetV l r (c.nreg r)) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  induction l generalizing c with
  | nil => exact ⟨c, 0, Exec.block_nil hc, rfl, fun r => rfl, rfl, rfl, rfl, rfl⟩
  | cons p l ih =>
    have e₁ := Exec.constN (P := P) hc p.1 p.2 (hl p (List.mem_cons_self ..))
    obtain ⟨c', k, e, hk, hn, hr, hm, hrm, ho⟩ :=
      ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ e₁.wb_right
    refine ⟨c', k + 1, Exec.block_cons e₁ e, by simp [hk], fun r => ?_, hr, hm, hrm, ho⟩
    rw [hn r]
    simp only [feSetV]
    congr 1

/-! ### Filling a window with a constant -/

/-- For `e = r2454 < r2450`: `nmem[r2451 + e] := r2452`. -/
def feFillBody : Stmt := block [.addN 2455 2451 2454, .storeN 2455 2452, .addN 2454 2454 2453]

/-- **`nmem[Dst + e] := v` for `e < len`.** -/
def feFill (Dst len v : ℕ) : Stmt :=
  .seq (block [.constN 2450 len, .constN 2451 Dst, .constN 2452 v, .constN 2453 1,
    .constN 2454 0]) (.whileLtN 2454 2450 feFillBody)

theorem feFill_natOnly (Dst len v : ℕ) : Klein.natOnly (feFill Dst len v) = true := by
  kernel_rfl

theorem feFillBody_exec (c : Config) (hc : WordsBounded W c) {Dst v e : ℕ}
    (r51 : c.nreg 2451 = Dst) (r52 : c.nreg 2452 = v) (r54 : c.nreg 2454 = e)
    (r53 : c.nreg 2453 = 1) (w1 : Dst + e ≤ W) (w3 : e + 1 ≤ W) :
    ∃ c' k, Exec P W feFillBody c c' k ∧ k = 3 ∧
      c'.nmem = upd c.nmem (Dst + e) v ∧ c'.nreg 2454 = e + 1 ∧
      (∀ r, r ≠ 2454 → r ≠ 2455 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold feFillBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r51, r52, r53, r54]); omega)
  refine ⟨rfl, ?_, ?_, fun r hr1 hr2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r51, r52, r54]
  · config_simp; simp only [r53, r54]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **Filling a window with a constant.** -/
theorem feFill_exec {Dst len v : ℕ} (hW1 : Dst + len ≤ W) (h1 : 1 ≤ W) (hv : v ≤ W)
    (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (feFill Dst len v) c c' k ∧ k ≤ 5 * len + 7 ∧
      (∀ e < len, c'.nmem (Dst + e) = v) ∧
      (∀ a, (a < Dst ∨ Dst + len ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2450 ∨ 2459 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold feFill
  obtain ⟨c₁, k₁, e₁, hk₁, g50, g51, g52, g53, g54, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2450 len, .constN 2451 Dst, .constN 2452 v, .constN 2453 1,
        .constN 2454 0]) c c₁ k₁ ∧ k₁ = 5 ∧ c₁.nreg 2450 = len ∧ c₁.nreg 2451 = Dst ∧
      c₁.nreg 2452 = v ∧ c₁.nreg 2453 = 1 ∧ c₁.nreg 2454 = 0 ∧
      (∀ r, r < 2450 ∨ 2459 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Dst + e) = v) ∧
      (∀ a, (a < Dst ∨ Dst + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2450 ∨ 2459 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 2451 = Dst ∧
      c'.nreg 2452 = v ∧ c'.nreg 2453 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2454) (bR := 2450)
    (body := feFillBody) J (K := 3) (n := len) c₁ e₁.wb_right g54 g50
    ⟨fun e he => absurd he (by omega), fun a _ => by rw [gm₁], gn₁, g51, g52, g53, gr₁,
      grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j51, j52, j53, jr, jrm, jo⟩ := hJ
      obtain ⟨c'', k, ex, hk, hm, h54, hn, hr, hrm, ho⟩ := feFillBody_exec (P := P) c' hw j51 j52
        ha j53 (by omega) (by omega)
      refine ⟨c'', k, ex, by omega, h54, by rw [hn 2450 (by omega) (by omega)]; exact hb,
        fun e he => ?_, fun a h => ?_, fun r hr' => ?_,
        by rw [hn 2451 (by omega) (by omega)]; exact j51,
        by rw [hn 2452 (by omega) (by omega)]; exact j52,
        by rw [hn 2453 (by omega) (by omega)]; exact j53,
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact j1 e he
        · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega)
      · rw [hn r (by omega) (by omega)]; exact j3 r hr')
  obtain ⟨j1, j2, j3, -, -, -, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, j3, jr, jrm, jo⟩

/-! ### Clamping a window -/

/-- For `e = r2454 < r2450`: `nmem[r2451 + e] := min (nmem[r2451 + e]) r2452`
(`x - (x - B)`). -/
def feClampBody : Stmt :=
  block [.addN 2455 2451 2454, .loadN 2456 2455, .subN 2457 2456 2452, .subN 2456 2456 2457,
    .storeN 2455 2456, .addN 2454 2454 2453]

/-- **Every word of `[Dst, Dst + len)` clamped to `B`.** -/
def feClamp (Dst len B : ℕ) : Stmt :=
  .seq (block [.constN 2450 len, .constN 2451 Dst, .constN 2452 B, .constN 2453 1,
    .constN 2454 0]) (.whileLtN 2454 2450 feClampBody)

theorem feClamp_natOnly (Dst len B : ℕ) : Klein.natOnly (feClamp Dst len B) = true := by
  kernel_rfl

theorem feClampBody_exec (c : Config) (hc : WordsBounded W c) {Dst B e : ℕ}
    (r51 : c.nreg 2451 = Dst) (r52 : c.nreg 2452 = B) (r54 : c.nreg 2454 = e)
    (r53 : c.nreg 2453 = 1) (w1 : Dst + e ≤ W) (w3 : e + 1 ≤ W) :
    ∃ c' k, Exec P W feClampBody c c' k ∧ k = 6 ∧
      c'.nmem = upd c.nmem (Dst + e) (min (c.nmem (Dst + e)) B) ∧ c'.nreg 2454 = e + 1 ∧
      (∀ r, r ≠ 2454 → r ≠ 2455 → r ≠ 2456 → r ≠ 2457 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold feClampBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r51, r52, r53, r54]); omega)
  refine ⟨rfl, ?_, ?_, fun r hr1 hr2 hr3 hr4 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r51, r52, r54]
    congr 1; omega
  · config_simp; simp only [r53, r54]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **Clamping a window.** -/
theorem feClamp_exec {Dst len B : ℕ} (hW1 : Dst + len ≤ W) (h1 : 1 ≤ W) (hB : B ≤ W)
    (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (feClamp Dst len B) c c' k ∧ k ≤ 8 * len + 7 ∧
      (∀ e < len, c'.nmem (Dst + e) = min (c.nmem (Dst + e)) B) ∧
      (∀ a, (a < Dst ∨ Dst + len ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2450 ∨ 2459 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold feClamp
  obtain ⟨c₁, k₁, e₁, hk₁, g50, g51, g52, g53, g54, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2450 len, .constN 2451 Dst, .constN 2452 B, .constN 2453 1,
        .constN 2454 0]) c c₁ k₁ ∧ k₁ = 5 ∧ c₁.nreg 2450 = len ∧ c₁.nreg 2451 = Dst ∧
      c₁.nreg 2452 = B ∧ c₁.nreg 2453 = 1 ∧ c₁.nreg 2454 = 0 ∧
      (∀ r, r < 2450 ∨ 2459 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Dst + e) = min (c.nmem (Dst + e)) B) ∧
      (∀ a, (a < Dst ∨ Dst + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2450 ∨ 2459 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 2451 = Dst ∧
      c'.nreg 2452 = B ∧ c'.nreg 2453 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2454) (bR := 2450)
    (body := feClampBody) J (K := 6) (n := len) c₁ e₁.wb_right g54 g50
    ⟨fun e he => absurd he (by omega), fun a _ => by rw [gm₁], gn₁, g51, g52, g53, gr₁,
      grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j51, j52, j53, jr, jrm, jo⟩ := hJ
      obtain ⟨c'', k, ex, hk, hm, h54, hn, hr, hrm, ho⟩ := feClampBody_exec (P := P) c' hw j51 j52
        ha j53 (by omega) (by omega)
      refine ⟨c'', k, ex, by omega, h54,
        by rw [hn 2450 (by omega) (by omega) (by omega) (by omega)]; exact hb,
        fun e he => ?_, fun a h => ?_, fun r hr' => ?_,
        by rw [hn 2451 (by omega) (by omega) (by omega) (by omega)]; exact j51,
        by rw [hn 2452 (by omega) (by omega) (by omega) (by omega)]; exact j52,
        by rw [hn 2453 (by omega) (by omega) (by omega) (by omega)]; exact j53,
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact j1 e he
        · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), j2 _ (by omega)]
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega)
      · rw [hn r (by omega) (by omega) (by omega) (by omega)]; exact j3 r hr')
  obtain ⟨j1, j2, j3, -, -, -, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, j3, jr, jrm, jo⟩

/-! ### Gathering marks -/

/-- For `i = r2454 < r2450`: `nmem[r2451 + i] := nmem[r2458 + nmem[r2452 + i]]`. -/
def feGatherBody : Stmt :=
  block [.addN 2455 2452 2454, .loadN 2456 2455, .addN 2456 2458 2456, .loadN 2456 2456,
    .addN 2455 2451 2454, .storeN 2455 2456, .addN 2454 2454 2453]

/-- **`nmem[Out + i] := nmem[Mk + nmem[In + i]]` for `i < len`.** -/
def feGather (Out In Mk len : ℕ) : Stmt :=
  .seq (block [.constN 2450 len, .constN 2451 Out, .constN 2452 In, .constN 2458 Mk,
    .constN 2453 1, .constN 2454 0]) (.whileLtN 2454 2450 feGatherBody)

theorem feGather_natOnly (Out In Mk len : ℕ) :
    Klein.natOnly (feGather Out In Mk len) = true := by
  kernel_rfl

theorem feGatherBody_exec (c : Config) (hc : WordsBounded W c) {Out In Mk e : ℕ}
    (r51 : c.nreg 2451 = Out) (r52 : c.nreg 2452 = In) (r58 : c.nreg 2458 = Mk)
    (r54 : c.nreg 2454 = e) (r53 : c.nreg 2453 = 1) (w1 : Out + e ≤ W) (w2 : In + e ≤ W)
    (w3 : e + 1 ≤ W) (w4 : Mk + c.nmem (In + e) ≤ W) :
    ∃ c' k, Exec P W feGatherBody c c' k ∧ k = 7 ∧
      c'.nmem = upd c.nmem (Out + e) (c.nmem (Mk + c.nmem (In + e))) ∧ c'.nreg 2454 = e + 1 ∧
      (∀ r, r ≠ 2454 → r ≠ 2455 → r ≠ 2456 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold feGatherBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r51, r52, r53, r54, r58]); omega)
  refine ⟨rfl, ?_, ?_, fun r hr1 hr2 hr3 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r51, r52, r54, r58]
  · config_simp; simp only [r53, r54]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **Gathering marks**: the input indices `In[i] < nMk` read before the outputs are written
(the window `[Out, Out + len)` apart from `[In, In + len)` and `[Mk, Mk + nMk)`). -/
theorem feGather_exec {Out In Mk len nMk : ℕ} (hW1 : Out + len ≤ W) (hW2 : In + len ≤ W)
    (hW3 : Mk + nMk ≤ W) (h1 : 1 ≤ W) (hd1 : Out + len ≤ In ∨ In + len ≤ Out)
    (hd2 : Out + len ≤ Mk ∨ Mk + nMk ≤ Out)
    (c : Config) (hc : WordsBounded W c) (hIn : ∀ i < len, c.nmem (In + i) < nMk) :
    ∃ c' k, Exec P W (feGather Out In Mk len) c c' k ∧ k ≤ 9 * len + 8 ∧
      (∀ i < len, c'.nmem (Out + i) = c.nmem (Mk + c.nmem (In + i))) ∧
      (∀ a, (a < Out ∨ Out + len ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2450 ∨ 2459 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold feGather
  obtain ⟨c₁, k₁, e₁, hk₁, g50, g51, g52, g58, g53, g54, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2450 len, .constN 2451 Out, .constN 2452 In, .constN 2458 Mk,
        .constN 2453 1, .constN 2454 0]) c c₁ k₁ ∧ k₁ = 6 ∧ c₁.nreg 2450 = len ∧
      c₁.nreg 2451 = Out ∧ c₁.nreg 2452 = In ∧ c₁.nreg 2458 = Mk ∧ c₁.nreg 2453 = 1 ∧
      c₁.nreg 2454 = 0 ∧
      (∀ r, r < 2450 ∨ 2459 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Out + e) = c.nmem (Mk + c.nmem (In + e))) ∧
      (∀ a, (a < Out ∨ Out + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2450 ∨ 2459 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 2451 = Out ∧
      c'.nreg 2452 = In ∧ c'.nreg 2458 = Mk ∧ c'.nreg 2453 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2454) (bR := 2450)
    (body := feGatherBody) J (K := 7) (n := len) c₁ e₁.wb_right g54 g50
    ⟨fun e he => absurd he (by omega), fun a _ => by rw [gm₁], gn₁, g51, g52, g58, g53, gr₁,
      grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j51, j52, j58, j53, jr, jrm, jo⟩ := hJ
      have eIn : c'.nmem (In + i) = c.nmem (In + i) := j2 _ (by omega)
      have hlt := hIn i hi
      have eMk : c'.nmem (Mk + c.nmem (In + i)) = c.nmem (Mk + c.nmem (In + i)) :=
        j2 _ (by omega)
      obtain ⟨c'', k, ex, hk, hm, h54, hn, hr, hrm, ho⟩ := feGatherBody_exec (P := P) c' hw j51
        j52 j58 ha j53 (by omega) (by omega) (by omega) (by rw [eIn]; omega)
      refine ⟨c'', k, ex, by omega, h54,
        by rw [hn 2450 (by omega) (by omega) (by omega)]; exact hb,
        fun e he => ?_, fun a h => ?_, fun r hr' => ?_,
        by rw [hn 2451 (by omega) (by omega) (by omega)]; exact j51,
        by rw [hn 2452 (by omega) (by omega) (by omega)]; exact j52,
        by rw [hn 2458 (by omega) (by omega) (by omega)]; exact j58,
        by rw [hn 2453 (by omega) (by omega) (by omega)]; exact j53,
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact j1 e he
        · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), eIn, eMk]
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega)
      · rw [hn r (by omega) (by omega) (by omega)]; exact j3 r hr')
  obtain ⟨j1, j2, j3, -, -, -, -, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, j3, jr, jrm, jo⟩

/-! ### One word -/

/-- **`nmem[dst] := nmem[src]`.** -/
def feCpyCell (dst src : ℕ) : Stmt :=
  block [.constN 2455 src, .loadN 2456 2455, .constN 2455 dst, .storeN 2455 2456]

theorem feCpyCell_natOnly (dst src : ℕ) : Klein.natOnly (feCpyCell dst src) = true := by
  kernel_rfl

theorem feCpyCell_exec {dst src : ℕ} (h1 : dst ≤ W) (h2 : src ≤ W) (c : Config)
    (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (feCpyCell dst src) c c' k ∧ k = 4 ∧
      c'.nmem = upd c.nmem dst (c.nmem src) ∧
      (∀ r, r < 2450 ∨ 2459 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold feCpyCell
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · config_simp
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **`nmem[a] := v`.** -/
def feStore (a v : ℕ) : Stmt := block [.constN 2455 a, .constN 2456 v, .storeN 2455 2456]

theorem feStore_natOnly (a v : ℕ) : Klein.natOnly (feStore a v) = true := by
  kernel_rfl

theorem feStore_exec {a v : ℕ} (h1 : a ≤ W) (h2 : v ≤ W) (c : Config)
    (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (feStore a v) c c' k ∧ k = 3 ∧ c'.nmem = upd c.nmem a v ∧
      (∀ r, r < 2450 ∨ 2459 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold feStore
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · config_simp
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

end NegSSSP

end PlanarFlow
