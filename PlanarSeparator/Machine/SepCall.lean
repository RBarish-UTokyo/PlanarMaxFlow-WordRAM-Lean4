module

public import PlanarSeparator.Machine.SubCall

/-!
# The separator program as a subroutine

* `SepProg.sepProg_exec_sepOut`: the separator program as a structured execution from the
  initial configuration (the form of `SepProg.sepProg_sepOut` before compilation), so that it can
  be embedded in a larger program.
* `ltProg_exec`: the same on the input `sepInput R w di`, with the output `ltOut`.
* `sepProg_regsOK`, `sepProg_noRand`: the separator program names only registers `< 1000` and
  draws no random words.
* **`ltSub_exec`**: the separator program run as a subroutine of a larger program
  (`ltSub rp ro tmp β len = (sepProg.outMem rp ro).toMem tmp β len`): with the words of
  `sepInput R w di` in memory at `β`, the registers `< 1000` and the memory up to
  `p + 320 m + 191 n + 403` zero (`p` the value of the register `rp`), it runs within
  `6 (320 m + 191 n + 403)` steps and leaves `ltOut (sepInput R w di)`, a separation of the
  graph as in `SeparatorMachine` (`ltProg_spec`), in memory at `p, p + 1, …`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

open Finset WordRAM WordRAM.Machine

namespace SepProg

open WordRAM.Machine.Stmt

/-- **The separator program as a structured execution** (`SepProg.sepProg_sepOut` before
compilation). -/
theorem sepProg_exec_sepOut {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) (w : V → ℕ) {n m : ℕ}
    {vi : V ≃ Fin n} {di : G.Dart ≃ Fin m} {ofs wN tl rv ro : ℕ → ℕ}
    (hE : Enc R w n m vi di ofs wN tl rv ro) {P : Input} (hIn : InHolds P n m ofs wN tl rv ro)
    {W : ℕ} (hW : memTop n m + 3 * ∑ v ∈ range n, wN v + 2 * n + 3 * m + 10 ≤ W)
    (hPW : ∀ j, P.data.getD j 0 ≤ W) :
    ∃ c' k, Exec P W sepProg initConfig c' k ∧ k + 1 ≤ 320 * m + 191 * n + 403 ∧
      SepOut G w vi c'.output := by
  classical
  have hN := hE.nwf
  have hn : 0 < n := by
    obtain ⟨v⟩ := hR.connected.nonempty
    exact lt_of_le_of_lt (Nat.zero_le _) (vi v).2
  obtain ⟨c₀, k₀, e₀, rfl, hL₀, hR₀, hz₀, ho₀⟩ := setup_exec (n := n) (m := m) hIn hW
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- no darts: a single vertex, printed `0`
    have hn1 : n = 1 := by
      by_contra hne
      have h1 : 1 < n := by omega
      have hne' : vi.symm ⟨0, hn⟩ ≠ vi.symm ⟨1, h1⟩ := fun e => by
        have := congrArg (fun x => (vi x : ℕ)) e; simp at this
      have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1
        (hR.connected.preconnected (vi.symm ⟨0, hn⟩) (vi.symm ⟨1, h1⟩))
      rcases hr.cases_head with h | ⟨z, hz, -⟩
      · exact hne' h
      · exact absurd (di ⟨(_, z), hz⟩).2 (by omega)
    subst hn1
    have h0 : ¬ c₀.nreg 100 < c₀.nreg 105 := by rw [hL₀.r100, hL₀.r105]; omega
    refine ⟨_, 39 + (1 + 2), .seq e₀ (.ifLtN_false h0 (Exec.outN e₀.wb_right 100)),
      by omega, ?_⟩
    have hout : c₀.output ++ [c₀.nreg 100] = [0] := by
      simp only [ho₀, hL₀.r100, List.nil_append]
    simp only [hout]
    have hv : ∀ v : V, (vi v : ℕ) = 0 := fun v => by have := (vi v).2; omega
    have hc : Fintype.card V = 1 := by rw [Fintype.card_congr vi, Fintype.card_fin]
    unfold SepOut
    simp only [hv, List.getD_cons_zero]
    refine ⟨⟨by simp, by simp, by simp, by simp, by simp⟩, ?_, by simp, by simp⟩
    norm_num [hc]
  · have h0 : c₀.nreg 100 < c₀.nreg 105 := by rw [hL₀.r100, hL₀.r105]; omega
    obtain ⟨c₁, k₁, e₁, hk₁, L, pr, l₁, j, j', hF⟩ :=
      front_exec hN hIn hW hPW hn (hE.nconn hR.connected hn) (hE.ofs_lt hR.connected hm) c₀
        e₀.wb_right hL₀ hR₀ hz₀ ho₀
    obtain ⟨c₂, k₂, e₂, hk₂, hΦ⟩ := back_sepOut hR w hE hIn hW hPW hm hF
    exact ⟨c₂, _, .seq e₀ (.ifLtN_true h0 (.seq e₁ e₂)), by omega, hΦ⟩

end SepProg

/-- The separator program names only registers `< 1000`. -/
theorem sepProg_regsOK : SepProg.sepProg.regsOK (fun r => decide (r < 1000)) = true := by
  decide +kernel

/-- The separator program draws no random words. -/
theorem sepProg_noRand : SepProg.sepProg.noRand = true := by
  decide +kernel

/-- **The separator program on `sepInput` as a structured execution**, with the output
`ltOut`. -/
theorem ltProg_exec {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G) (hR : R.IsPlane) (w : Fin n → ℕ) (di : G.Dart ≃ Fin m)
    (hdi : ∀ d d' : G.Dart, d.fst < d'.fst → di d < di d') (W : ℕ)
    (hW : 16 * m + 12 * n + 3 * ∑ v, w v + 22 ≤ W) :
    ∃ c' k, Exec (sepInput R w di) W SepProg.sepProg initConfig c' k ∧
      k + 1 ≤ 320 * m + 191 * n + 403 ∧ c'.output = ltOut (sepInput R w di) := by
  have hE := SepProg.enc_sepInput R w di hdi
  have hIn := SepProg.inHolds_sepInput R w di
  have hsum : ∑ v ∈ range n, SepProg.wI w v = ∑ v, w v := by
    rw [← Fin.sum_univ_eq_sum_range]; simp [SepProg.wI]
  have hW' : SepProg.memTop n m + 3 * ∑ v ∈ range n, SepProg.wI w v + 2 * n + 3 * m + 10 ≤ W := by
    rw [hsum]; unfold SepProg.memTop; omega
  obtain ⟨c', k, e, hk, -⟩ :=
    SepProg.sepProg_exec_sepOut hR w hE hIn hW' (SepProg.sepInput_le R w di hW)
  exact ⟨c', k, e, hk, (ltOut_eq (runsWithin_of_exec_output e rfl)).symm⟩

/-- **The separator program as a subroutine.** -/
def ltSub (rp ro tmp β len : ℕ) : Stmt := (SepProg.sepProg.outMem rp ro).toMem tmp β len

/-- **The separator program run as a subroutine on `sepInput R w di` held in memory**: from a
configuration `d` with the registers `< 1000` (and the real registers `< 1000`, `rp`, `ro`) and
the natural and real memory up to `p + 320 m + 191 n + 403` zero (`p` the value of `rp`, larger
than the bound `W = 16 m + 12 n + 3 Σ w + 22`), `1` in `ro`, and the input words `i ≤ W₂` at
`β + i`, `ltSub` writes `ltOut (sepInput R w di)` (the separation of `ltProg_spec`) at `p, …`
within `6 (320 m + 191 n + 403)` steps. -/
theorem ltSub_exec {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G) (hR : R.IsPlane) (w : Fin n → ℕ) (di : G.Dart ≃ Fin m)
    (hdi : ∀ d d' : G.Dart, d.fst < d'.fst → di d < di d') {P' : Input} {rp ro tmp β len W' : ℕ}
    (hrp : 1000 ≤ rp) (hro : 1000 ≤ ro) (htmp : 1000 ≤ tmp) (hpo : rp ≠ ro) (hpt : rp ≠ tmp)
    (hot : ro ≠ tmp) {d : Config} (hd : WordsBounded W' d)
    (hz : ∀ r < 1000, d.nreg r = 0) (hzr : ∀ r, r < 1000 ∨ r = rp ∨ r = ro → d.rreg r = 0)
    (hm : ∀ a ≤ d.nreg rp + (320 * m + 191 * n + 403), d.nmem a = 0)
    (hmr : ∀ a ≤ d.nreg rp + (320 * m + 191 * n + 403), d.rmem a = 0)
    (h1 : d.nreg ro = 1) (hpW : 16 * m + 12 * n + 3 * ∑ v, w v + 22 < d.nreg rp)
    (hI : InData (sepInput R w di) (d.nreg rp + (320 * m + 191 * n + 403)) β len W' d) :
    ∃ d' k', Exec P' W' (ltSub rp ro tmp β len) d d' k' ∧
      k' ≤ 6 * (320 * m + 191 * n + 403) ∧
      d'.nreg rp = d.nreg rp + (ltOut (sepInput R w di)).length ∧
      (∀ i (hi : i < (ltOut (sepInput R w di)).length),
        d'.nmem (d.nreg rp + i) = (ltOut (sepInput R w di))[i]) ∧
      (∀ r, 1000 ≤ r → r ≠ rp → r ≠ tmp → d'.nreg r = d.nreg r) ∧
      (∀ a, d.nreg rp + (320 * m + 191 * n + 403) < a → d'.nmem a = d.nmem a) ∧
      d'.output = d.output := by
  obtain ⟨c', k, e, hk, hout⟩ := ltProg_exec G R hR w di hdi _ le_rfl
  have hI' : InData (sepInput R w di) (d.nreg rp + k) β len W' d :=
    ⟨by have := hI.lt; omega, by have := hI.le; omega, hI.len,
      fun i hi => hI.mem i (by omega)⟩
  obtain ⟨d', k', e', hk', hp', hmem, hreg, hkeep, ho⟩ := Exec.subcall (P' := P') e sepProg_regsOK
    sepProg_noRand hrp hro htmp hpo hpt hot hd hz hzr (fun a ha => hm a (by omega))
    (fun a ha => hmr a (by omega)) h1 hpW hI'
  rw [hout] at hp' hmem
  exact ⟨d', k', e', by omega, hp', hmem, hreg, fun a ha => hkeep a (by omega), ho⟩

end PlanarSeparator
