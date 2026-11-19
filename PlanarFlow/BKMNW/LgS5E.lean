module

public import PlanarFlow.BKMNW.LgS5D
public import PlanarFlow.BKMNW.DecGuard

/-!
# The large-piece separator, stage 5 composed: `lgS5_exec`

**`lgS5_exec`**: the program `lgS5 = s5Pre ; if 0 < n' then s5Body` on a record of a large
piece `P = x.1.piece` (holes `Hs = x.2.1`, `k = |Hs|`, `n = #P`), with the state `st` of the
decomposition a valid rotation of the core's piece map `B` (`CInvS`, given by the guard:
`decS_node_guard`), the input conventions `QPar Q ν`, `TailSorted M gid ν`, `ν` injective, at
most `6` touched holes, runs within

  `9700 n + 70 k + 5 log₂ (2 W₀) + mbT #B (encB' W₀) W₀ + 3800`

steps (`W₀ = #P + K nTouch = s5Wv`), keeps the memory below `U` and the registers
`700 … 3102`, `3110 … 4399`, `≥ 7000`, saves `#B`, `nTouch`, `[holeStep]`, `K`, `A`, `W₀` in
`3103 … 3108`, leaves the core's enumeration `g ∘ IX` (`IX` at `U + 2n`) and its rotation `SG`
(at `U + 3n`), and:
* if `B = ∅` (the `pemptyD` branch of `pcertF`): nothing more;
* otherwise `3109 = Bz = encB' W₀` and the outcome of **the headline's certificate**
  `scertD (s5sc M eG N Hs A W₀) Hs B st (s5ex M Q eG N d₀ P Hs K)` (the certificate inside
  `pcertD (pcChoiceE M Q eG N d₀) (s5sc …) Q P Hs K st`): `4970 = 0` and `none`, or `4970 = 1`,
  `some (ρ, I)` with the items `I` at `ITEMb = U + 42 n + 5 k + 7 #B + 32` (`ItemRep` on the
  enumeration) and the path (`4900 = 0`, `PathNH` at `NHb = ITEMb + #B`) or a point
  (`4900 = 2`, the dart index in `4902`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.rwaSuggestion false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The registers kept by the whole of stage 5. -/
def s5Keep (x : ℕ) : Prop := (700 ≤ x ∧ x < 3103) ∨ (3109 < x ∧ x < 4400) ∨ 7000 ≤ x

/-- **The state of a large node from its record** (phase `0`) in the guarded decomposition: the
rotation `st` stored in the record is valid (`CInvS`), the piece meets `PcOK`, at most `6` holes
are touched (the hypotheses of `lgS5_exec`, from `decS_node_guard`). -/
theorem s5_state_of_phOk {S T : Finset V} {κ : ℕ} {ds : DSys M}
    {spS spH : Finset D → List (Finset V) → Perm D → SplitAns M}
    {chS : Finset D → List (Finset V) → Perm D → HSep M → Finset D → Perm D}
    (hF : SplitFnsS M S T κ ds.s (CInvS M ds.Q) spS spH (smD M ds.pk S T) chS)
    (hsm : ∀ P Hs, RevClosed M P → (smD M ds.pk S T P Hs).piece = P)
    (hdS : ds.spS = guardS M (gSz M S T ds.s (CInvS M ds.Q)) spS)
    (hdH : ds.spH = guardS M (gHl M S T ds.s (CInvS M ds.Q)) spH) (hdC : ds.chS = chS)
    {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D} {n SPb bfl : ℕ}
    {g : ℕ → D} {mem : ℕ → ℕ} (hph : PhOk M ds S T (.node l r π, Hs, σ) 0 bfl n SPb g mem)
    (hs : ds.s < (ADec.node l r π).piece.card) :
    ∃ st : Perm D, PcOK M S T (ADec.node l r π).piece Hs ∧
      CInvS M ds.Q (ADec.node l r π).piece Hs st ∧ nTouch M (ADec.node l r π).piece Hs ≤ 6 ∧
      (∀ i < n, g i ∈ pdarts M (core M ds.Q (ADec.node l r π).piece) Hs →
        mem (SPb + i) < n ∧ g (mem (SPb + i)) = st (g i)) ∧
      ADec.node l r π = ds.dec S T (ADec.node l r π).piece Hs st (decide (bfl = 1)) := by
  rcases hph with ⟨-, st, hx, hsp⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · have h' : decS M (guardS M (gSz M S T ds.s (CInvS M ds.Q)) spS)
        (guardS M (gHl M S T ds.s (CInvS M ds.Q)) spH) (smD M ds.pk S T) chS ds.s
        (ADec.node l r π).piece Hs st (decide (bfl = 1)) = .node l r π := by
      have := hx.symm
      unfold DSys.dec at this
      rw [hdS, hdH, hdC] at this
      exact this
    obtain ⟨hPc, hI, h6, h5, -⟩ := decS_node_guard hF hsm hs h'
    refine ⟨st, hPc, hI, ?_, hsp, hx⟩
    cases hb : holeStep M (ADec.node l r π).piece Hs (decide (bfl = 1))
    · have := h5 hb; omega
    · have := h6 hb; omega
  · omega
  · omega

section Exec

variable {I : Input} {W : ℕ}

/-- **Stage 5 of the large-piece separator, composed** (see the module docstring). -/
theorem lgS5_exec (hloopM : ∀ d, M.head d ≠ M.tail d) {gid : D → ℕ} {ν : V → ℕ}
    {S T Q : Finset V} {x : MCall M} {m n R : ℕ} {g : ℕ → D} (c : Config) (hc : WordsBounded W c)
    (hA : RArr M gid ν S T x m n R g c.nmem) (hTS : TailSorted M gid ν) (hQ : QPar Q ν)
    (hν : Injective ν) (hP : PcOK M S T x.1.piece x.2.1)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {st : Perm D}
    (hCI : CInvS M Q x.1.piece x.2.1 st) (hnt : nTouch M x.1.piece x.2.1 ≤ 6)
    (hSP : ∀ i < n, g i ∈ pdarts M (core M Q x.1.piece) x.2.1 →
      c.nmem (R + 3 + 5 * n + i) < n ∧ g (c.nmem (R + 3 + 5 * n + i)) = st (g i))
    {eG : ℕ → D} {N : ℕ} (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d)
    (d₀ : D) {U bfl : ℕ} {bb : Bool} (r0 : c.nreg 3100 = R) (r1 : c.nreg 3101 = U)
    (r2 : c.nreg 3102 = x.2.1.length) (hRn : c.nmem R = n) (hRb : c.nmem (R + 2) = bfl)
    (hb : bfl ≤ 1) (hbb : bfl = 1 ↔ bb = true) (l0 : R + 3 + 6 * n + m ≤ U)
    (w : U + R + 600 * n + 10 * x.2.1.length + 2 * encB' (s5Wv M x.1.piece x.2.1 bb) +
      20 * s5Wv M x.1.piece x.2.1 bb + s5Kv M x.1.piece x.2.1 bb + s5Av M x.1.piece x.2.1 bb +
      400 ≤ W) :
    ∃ c' t, Exec I W lgS5 c c' t ∧
      t ≤ 9700 * n + 70 * x.2.1.length + 5 * Nat.log 2 (2 * s5Wv M x.1.piece x.2.1 bb) +
        mbT (pdarts M (core M Q x.1.piece) x.2.1).card (encB' (s5Wv M x.1.piece x.2.1 bb))
          (s5Wv M x.1.piece x.2.1 bb) + 3800 ∧
      (∀ a < U, c'.nmem a = c.nmem a) ∧ (∀ y, s5Keep y → c'.nreg y = c.nreg y) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 3103 = (pdarts M (core M Q x.1.piece) x.2.1).card ∧
      c'.nreg 3104 = nTouch M x.1.piece x.2.1 ∧
      c'.nreg 3105 = bf (holeStep M x.1.piece x.2.1 bb = true) ∧
      c'.nreg 3106 = s5Kv M x.1.piece x.2.1 bb ∧ c'.nreg 3107 = s5Av M x.1.piece x.2.1 bb ∧
      c'.nreg 3108 = s5Wv M x.1.piece x.2.1 bb ∧
      (∀ j < (pdarts M (core M Q x.1.piece) x.2.1).card, c'.nmem (U + 2 * n + j) < n ∧
        g (c'.nmem (U + 2 * n + j)) ∈ pdarts M (core M Q x.1.piece) x.2.1) ∧
      (∀ y ∈ pdarts M (core M Q x.1.piece) x.2.1,
        ∃ j < (pdarts M (core M Q x.1.piece) x.2.1).card, g (c'.nmem (U + 2 * n + j)) = y) ∧
      (∀ i j, i < j → j < (pdarts M (core M Q x.1.piece) x.2.1).card →
        gid (g (c'.nmem (U + 2 * n + i))) < gid (g (c'.nmem (U + 2 * n + j)))) ∧
      (∀ j < (pdarts M (core M Q x.1.piece) x.2.1).card,
        c'.nmem (U + 3 * n + j) < (pdarts M (core M Q x.1.piece) x.2.1).card ∧
        g (c'.nmem (U + 2 * n + c'.nmem (U + 3 * n + j))) = st (g (c'.nmem (U + 2 * n + j)))) ∧
      ((pdarts M (core M Q x.1.piece) x.2.1).card = 0 ∨
       (0 < (pdarts M (core M Q x.1.piece) x.2.1).card ∧
        c'.nreg 3109 = encB' (s5Wv M x.1.piece x.2.1 bb) ∧
        ((c'.nreg 4970 = 0 ∧ scertD (s5sc M eG N x.2.1 (s5Av M x.1.piece x.2.1 bb)
            (s5Wv M x.1.piece x.2.1 bb)) x.2.1 (pdarts M (core M Q x.1.piece) x.2.1) st
            (s5ex M Q eG N d₀ x.1.piece x.2.1 (s5Kv M x.1.piece x.2.1 bb)) = none) ∨
         (c'.nreg 4970 = 1 ∧ ∃ ρ I, scertD (s5sc M eG N x.2.1 (s5Av M x.1.piece x.2.1 bb)
            (s5Wv M x.1.piece x.2.1 bb)) x.2.1 (pdarts M (core M Q x.1.piece) x.2.1) st
            (s5ex M Q eG N d₀ x.1.piece x.2.1 (s5Kv M x.1.piece x.2.1 bb)) = some (ρ, I) ∧
           ∃ e' : ℕ → D, (∀ j < (pdarts M (core M Q x.1.piece) x.2.1).card,
             e' j = g (c'.nmem (U + 2 * n + j))) ∧
           ItemRep e' (pdarts M (core M Q x.1.piece) x.2.1).card I
             (fun i => c'.nmem (U + 42 * n + 5 * x.2.1.length +
               7 * (pdarts M (core M Q x.1.piece) x.2.1).card + 32 + i)) ∧
           ((c'.nreg 4900 = 0 ∧ PathNH M e' (pdarts M (core M Q x.1.piece) x.2.1).card
               (U + 42 * n + 5 * x.2.1.length + 8 * (pdarts M (core M Q x.1.piece) x.2.1).card +
                 32) x.2.1 c' ρ) ∨
            (c'.nreg 4900 = 2 ∧ c'.nreg 4902 < (pdarts M (core M Q x.1.piece) x.2.1).card ∧
              ρ = (SPath.point (M' := M) (e' (c'.nreg 4902))
                (M.tail (e' (c'.nreg 4902)))).toH)))))) := by
  obtain ⟨c₁, t₁, e₁, ht₁, z00, z01, z02, z03, z06, z07, z09, z10, z14, z70, z11, z910, z911,
    z912, z47, s03, s04, s05, s06, s07, s08, hS₁, mem₁, q₁, rr₁, rm₁, o₁⟩ :=
    s5Pre_exec (I := I) (bb := bb) hQ hP.disj hCI.pmap.stable c hc hA hSP r0 r1 r2 hRn hRb hb
      hbb l0 (by clear * - w; omega)
  have hA₁ : RArr M gid ν S T x m n R g c₁.nmem := hA.congr fun a h1 h2 =>
    mem₁ a (by clear * - h2 l0; omega)
  rcases Nat.eq_zero_or_pos (pdarts M (core M Q x.1.piece) x.2.1).card with h0 | hpos
  · -- the empty piece map of the core: skip
    refine ⟨c₁, t₁ + 2, .seq e₁ (.ifLtN_false (by rw [z47, z11, h0]; omega) (.skip e₁.wb_right)),
      ?_, mem₁, fun y hy => q₁ y ?_, rr₁, rm₁, o₁, s03, s04, s05, s06, s07, s08, hS₁.ix, hS₁.ixs,
      hS₁.ixm, hS₁.sg, Or.inl h0⟩
    · clear * - ht₁
      omega
    · unfold s5Keep at hy; unfold s5Fr; clear * - hy; omega
  · obtain ⟨c₂, t₂, e₂, ht₂, mem₂, v3109, q₂, rr₂, rm₂, o₂, hout⟩ := s5Body_exec (I := I) hloopM
      c₁ e₁.wb_right hA₁ hTS hQ hν hP hQdeg hQ5 hCI hnt he hesurj d₀ rfl rfl hpos hS₁ z00 z01
      z02 z03 z06 z07 z09 z10 z14 z70 ((q₁ 3102 (by unfold s5Fr; decide)).trans r2) z11 z910
      z911 z912 l0 (by clear * - w; omega)
    have hS₂ : ∀ a < U + 4 * n, c₂.nmem a = c₁.nmem a := mem₂
    have hn'n := hS₁.le
    have keep : ∀ y, s5Keep y → c₂.nreg y = c₁.nreg y := fun y hy =>
      q₂ y (by unfold s5Keep at hy; unfold s5BFr; clear * - hy; omega)
    refine ⟨c₂, t₁ + (t₂ + 1), .seq e₁ (.ifLtN_true (by rw [z47, z11]; exact hpos) e₂), ?_,
      fun a ha => ?_, fun y hy => ?_, by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁], ?_, ?_,
      ?_, ?_, ?_, ?_, fun j hj => ?_, fun y hy => ?_, fun i j hij hj => ?_, fun j hj => ?_,
      Or.inr ⟨hpos, v3109, ?_⟩⟩
    · clear * - ht₁ ht₂ hn'n
      omega
    · rw [hS₂ a (by clear * - ha; omega), mem₁ a ha]
    · rw [keep y hy, q₁ y (by unfold s5Keep at hy; unfold s5Fr; clear * - hy; omega)]
    · rw [q₂ 3103 (by unfold s5BFr; decide)]; exact s03
    · rw [q₂ 3104 (by unfold s5BFr; decide)]; exact s04
    · rw [q₂ 3105 (by unfold s5BFr; decide)]; exact s05
    · rw [q₂ 3106 (by unfold s5BFr; decide)]; exact s06
    · rw [q₂ 3107 (by unfold s5BFr; decide)]; exact s07
    · rw [q₂ 3108 (by unfold s5BFr; decide)]; exact s08
    · rw [hS₂ _ (by clear * - hj hn'n; omega)]; exact hS₁.ix j hj
    · obtain ⟨j, hj, hy'⟩ := hS₁.ixs y hy
      exact ⟨j, hj, by rw [hS₂ _ (by clear * - hj hn'n; omega)]; exact hy'⟩
    · rw [hS₂ _ (by clear * - hj hij hn'n; omega), hS₂ _ (by clear * - hj hn'n; omega)]
      exact hS₁.ixm i j hij hj
    · have h1 := hS₁.sg j hj
      rw [hS₂ (U + 3 * n + j) (by clear * - hj hn'n; omega),
        hS₂ (U + 2 * n + c₁.nmem (U + 3 * n + j)) (by clear * - h1 hn'n; omega),
        hS₂ (U + 2 * n + j) (by clear * - hj hn'n; omega)]
      exact h1
    · rcases hout with ⟨h1, h2⟩ | ⟨h1, ρ, I, h2, h3, h4⟩
      · exact Or.inl ⟨h1, h2⟩
      · refine Or.inr ⟨h1, ρ, I, h2, fun j => g (c₁.nmem (U + 2 * n + j)), fun j hj => ?_, h3, h4⟩
        rw [hS₂ _ (by clear * - hj hn'n; omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
