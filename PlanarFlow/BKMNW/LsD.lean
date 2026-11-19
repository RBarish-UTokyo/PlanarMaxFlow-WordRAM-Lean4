module

public import PlanarFlow.BKMNW.LsC2

/-!
# `sepL`: `lsB` writes the certificate's path (`PathPD` for the later stages)

**`lsB_path`**: after stage 5, in each of its three outcomes (Miller's path `PathPD` at
`Hb' + 6 #B`; the cut vertex `point (e' r4902)`; the empty core's point of `pemptyD`, for a
choice `pk` meeting `PkMin`), `lsB` leaves `n'` in `8557` (`1 ≤ n' ≤ n`), the record indices
`IX'` at `E` (`n'` cells; their darts are piece-map darts when `0 < m`; the first `#B` enumerate
the core's piece map `B`) and **`PathPD M (g ∘ IX') n' (E + n) c' ρ`**.
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

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **`lsB` writes the certificate's path** (see the module docstring). -/
theorem lsB_path {gid : D → ℕ} {ν : V → ℕ} {S T Q : Finset V} {xc : MCall M} {g : ℕ → D}
    (c : Config) (hc : WordsBounded W c) {m k R n Sb nB : ℕ} (hR : LsR c m k R n Sb)
    (hA : RArr M gid ν S T xc m n R g c.nmem) (hk : xc.2.1.length = k)
    (hB : nB = (pdarts M (core M Q xc.1.piece) xc.2.1).card) (r03 : c.nreg 3103 = nB)
    (hIX : ∀ j < nB, c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 2 * n + j) < n ∧
      g (c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 2 * n + j)) ∈
        pdarts M (core M Q xc.1.piece) xc.2.1)
    (hIXs : ∀ y ∈ pdarts M (core M Q xc.1.piece) xc.2.1, ∃ j < nB,
      g (c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 2 * n + j)) = y)
    {ρ : HPath M}
    (hcase : (0 < nB ∧ c.nreg 4900 = 0 ∧ PathPD M
        (fun j => g (c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 2 * n + j))) nB
        (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 42 * n + 5 * k + 34 * nB + c.nreg 3109 +
          3 * c.nreg 3108 + 47 + 6 * nB) c ρ) ∨
      (0 < nB ∧ c.nreg 4900 = 2 ∧ c.nreg 4902 < nB ∧
        ρ = (SPath.point (M' := M)
          (g (c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 2 * n + c.nreg 4902)))
          (M.tail (g (c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 2 * n +
            c.nreg 4902))))).toH) ∨
      (nB = 0 ∧ ∃ pk : Finset D → D, PkMin gid pk ∧ Injective gid ∧ QPar Q ν ∧
        ρ = (SPath.point (M' := M)
          (if (pdarts M xc.1.piece xc.2.1).Nonempty then
            (if M.tail (pk (pdarts M xc.1.piece xc.2.1)) ∈ Q then
              M.rev (pk (pdarts M xc.1.piece xc.2.1)) else pk (pdarts M xc.1.piece xc.2.1))
            else pk xc.1.piece)
          (M.tail (if (pdarts M xc.1.piece xc.2.1).Nonempty then
            (if M.tail (pk (pdarts M xc.1.piece xc.2.1)) ∈ Q then
              M.rev (pk (pdarts M xc.1.piece xc.2.1)) else pk (pdarts M xc.1.piece xc.2.1))
            else pk xc.1.piece))).toH))
    (hrev : ∀ d ∈ xc.1.piece, M.rev d ∈ xc.1.piece) (hn : 1 ≤ n) (lR : R + 3 + 6 * n + m ≤ Sb)
    (wM : 0 < nB → c.nreg 4900 = 0 → Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 42 * n +
      5 * k + 40 * nB + c.nreg 3109 + 3 * c.nreg 3108 + 47 + nB ≤ W)
    (w : Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 3 * n ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsB c c' t ∧ t ≤ 30 * n + 120 ∧ LsR c' m k R n Sb ∧
      c'.nreg 8558 = nB ∧ c'.nreg 8559 = c.nreg 3105 ∧ c'.nreg 8560 = c.nreg 3106 ∧
      c'.nreg 8561 = c.nreg 3107 ∧ c'.nreg 8571 = Sb + 21 * m + 38 * n + 8 * k + 24 + n ∧
      1 ≤ c'.nreg 8557 ∧ c'.nreg 8557 ≤ n ∧ nB ≤ c'.nreg 8557 ∧
      (∀ q < c'.nreg 8557, c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q) < n) ∧
      (0 < m → ∀ q < c'.nreg 8557,
        g (c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q)) ∈ pdarts M xc.1.piece xc.2.1) ∧
      (∀ q < nB, g (c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q)) ∈
        pdarts M (core M Q xc.1.piece) xc.2.1) ∧
      (∀ y ∈ pdarts M (core M Q xc.1.piece) xc.2.1, ∃ q < nB,
        g (c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q)) = y) ∧
      PathPD M (fun q => g (c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q))) (c'.nreg 8557)
        (Sb + 21 * m + 38 * n + 8 * k + 24 + n) c' ρ ∧
      (∀ a, (a < Sb + 21 * m + 38 * n + 8 * k + 24 ∨
        Sb + 21 * m + 38 * n + 8 * k + 24 + 2 * n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4910 ∨ (4916 < x ∧ x < 6520) ∨ (6529 < x ∧ x < 8550)) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hnc : n = xc.1.piece.card := hA.card
  have hBn : nB ≤ n := by rw [hB, hnc]; exact card_le_card fun y hy => (mem_core.1 (mem_pdarts.1 hy).1).1
  have hmc : m = (pdarts M xc.1.piece xc.2.1).card := hA.card_m
  set E := Sb + 21 * m + 38 * n + 8 * k + 24 with hE
  set U := E + 4 * n + 3 with hU
  -- the empty case's index bound
  have hfn : nB = 0 → c.nmem (R + 3 + 6 * n) * (1 - (1 - m)) < n := fun _ => by
    rcases Nat.eq_zero_or_pos m with h0 | hm
    · rw [h0]; simp; omega
    · rw [show 1 - (1 - m) = 1 by omega, Nat.mul_one]
      have := hA.fx 0 hm; simpa using this
  have wC : 0 < nB → c.nreg 4900 ≠ 0 → c.nreg 4902 + 1 ≤ W := fun h1 h2 => by
    rcases hcase with ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨h, -⟩
    · exact absurd h h2
    · omega
    · omega
  obtain ⟨c', t, e, ht, hR', v58, v59, v60, v61, v71, hne, hMil, hCut, hEmp, mE, fr, rr, rm,
    oo⟩ := lsB_exec (I := I) c hc hR r03 hBn wM wC hfn (by omega) (by omega) w2
  -- the record's dart of a core index
  have hBsub : ∀ y ∈ pdarts M (core M Q xc.1.piece) xc.2.1, y ∈ pdarts M xc.1.piece xc.2.1 :=
    fun y hy => core_sub_pdarts hy
  rcases Nat.eq_zero_or_pos nB with h0 | hpos
  · -- empty core
    obtain ⟨n1, aE, aEn⟩ := hEmp h0
    have hB0 : pdarts M (core M Q xc.1.piece) xc.2.1 = ∅ := by
      rw [← card_eq_zero, ← hB, h0]
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, pk, hpk, hgid, hQ, hρ⟩
    · omega
    · omega
    set f := c.nmem (R + 3 + 6 * n) with hf
    set i0 := f * (1 - (1 - m)) with hi0
    have hi0n : i0 < n := hfn h0
    -- the dart written
    have hdart : g (lsIs f (c.nmem (R + 3 + 4 * n + i0)) (c.nmem (R + 3 + n + i0)) m) =
        (if (pdarts M xc.1.piece xc.2.1).Nonempty then
          (if M.tail (pk (pdarts M xc.1.piece xc.2.1)) ∈ Q then
            M.rev (pk (pdarts M xc.1.piece xc.2.1)) else pk (pdarts M xc.1.piece xc.2.1))
          else pk xc.1.piece) := by
      rcases Nat.eq_zero_or_pos m with hm0 | hm
      · have hpe : ¬ (pdarts M xc.1.piece xc.2.1).Nonempty := by
          rw [not_nonempty_iff_eq_empty, ← card_eq_zero, ← hmc, hm0]
        rw [iteF hpe, hm0, lsIs_zero]
        exact (pick_eq_min hgid hpk hn hA.g_mem hA.g_surj hA.g_mono).symm
      · have hpe : (pdarts M xc.1.piece xc.2.1).Nonempty := by
          rw [← card_pos, ← hmc]; exact hm
        rw [iteT hpe]
        have hi0f : i0 = f := by rw [hi0, show 1 - (1 - m) = 1 by omega, Nat.mul_one]
        have hfx := hA.fx 0 hm
        have hpick : pk (pdarts M xc.1.piece xc.2.1) = g f := by
          rw [pick_eq_min hgid hpk hm hA.fx_mem hA.fx_surj hA.fx_mono]; simp [hf]
        rw [hpick]
        rw [hi0f, hA.vp f (by simpa [hf] using hfx)]
        exact lsIs_dart hQ hm (hA.rp f (by simpa [hf] using hfx)).2
    have hlt : lsIs f (c.nmem (R + 3 + 4 * n + i0)) (c.nmem (R + 3 + n + i0)) m < n := by
      rcases Nat.eq_zero_or_pos m with hm0 | hm
      · rw [hm0, lsIs_zero]; omega
      · have hi0f : i0 = f := by rw [hi0, show 1 - (1 - m) = 1 by omega, Nat.mul_one]
        have hfn' : f < n := by rw [← hi0f]; exact hi0n
        have hrp := (hA.rp f hfn').1
        unfold lsIs
        rw [show 1 - (1 - m) = 1 by omega, Nat.mul_one, Nat.mul_one]
        rw [hi0f] at *
        have : c.nmem (R + 3 + 4 * n + f) % 2 < 2 := Nat.mod_lt _ (by norm_num)
        rcases Nat.lt_or_ge (c.nmem (R + 3 + 4 * n + f) % 2) 1 with h | h
        · have h' : c.nmem (R + 3 + 4 * n + f) % 2 = 0 := by omega
          rw [h']; simp; omega
        · have h' : c.nmem (R + 3 + 4 * n + f) % 2 = 1 := by omega
          rw [h']; simp; exact hrp
    refine ⟨c', t, e, ht, hR', v58, v59, v60, v61, v71, by omega, by omega, by omega,
      fun q hq => ?_, fun hm q hq => ?_, fun q hq => absurd hq (by omega),
      fun y hy => by rw [hB0] at hy; exact absurd hy (notMem_empty _), ?_, mE, fr, rr, rm, oo⟩
    · rw [n1] at hq
      rw [show q = 0 by omega, Nat.add_zero, aE]; exact hlt
    · rw [n1] at hq
      rw [show q = 0 by omega, Nat.add_zero, aE, hdart]
      have hpe : (pdarts M xc.1.piece xc.2.1).Nonempty := by rw [← card_pos, ← hmc]; exact hm
      rw [iteT hpe]
      have hp := (hpk _ hpe).1
      split_ifs
      · rw [mem_pdarts] at hp ⊢
        exact ⟨hrev _ hp.1, by rw [inner_rev]; exact hp.2⟩
      · exact hp
    · rw [n1, hρ]
      refine pathPD_point (by omega) (by omega : 0 < 1) ?_ (by rw [aEn]) (fun j h1 h2 => by omega)
      show g (c'.nmem (E + 0)) = _
      rw [Nat.add_zero, aE, hdart]
  · -- nonempty core
    obtain ⟨n1, aIX⟩ := hne hpos
    refine ⟨c', t, e, ht, hR', v58, v59, v60, v61, v71, by omega, by omega, by omega,
      fun q hq => ?_, fun _ q hq => ?_, fun q hq => ?_, fun y hy => ?_, ?_, mE, fr, rr, rm, oo⟩
    · rw [n1] at hq; rw [aIX q hq]; exact (hIX q hq).1
    · rw [n1] at hq; rw [aIX q hq]; exact hBsub _ (hIX q hq).2
    · rw [aIX q hq]; exact (hIX q hq).2
    · obtain ⟨j, hj, hy'⟩ := hIXs y hy
      exact ⟨j, hj, by rw [aIX j hj]; exact hy'⟩
    · rw [n1]
      rcases hcase with ⟨-, h49, hP⟩ | ⟨-, h49, h02, hρ⟩ | ⟨h, -⟩
      · refine pathPD_congr hP (fun j hj => ?_) (fun i hi => ?_)
        · rw [hMil hpos h49 j hj]; congr 1; omega
        · show g (c'.nmem (E + i)) = g (c.nmem (U + 2 * n + i))
          rw [aIX i hi]
      · obtain ⟨a0, az⟩ := hCut hpos (by omega)
        rw [hρ]
        exact pathPD_point (by omega) h02
          (show g (c'.nmem (E + c.nreg 4902)) = _ by rw [aIX _ h02]) a0 az
      · omega

end Exec

end MfDrv

end BKMNW

end PlanarFlow
