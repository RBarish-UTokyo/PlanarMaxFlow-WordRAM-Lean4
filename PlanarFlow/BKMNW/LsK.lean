module

public import PlanarFlow.BKMNW.LsJ

/-!
# `sepL`: the set-up, stage 5 and the path (`lsA ; lgS5D ; lsB`)

**`lsPath_exec`**: on a record (`RArr`) of a large piece with the state `st` of the headline's
decomposition, for the headline's choices (`pcChoiceE M Q eG N d₀`, `s5sc M eG N`) and the
certificate `pcertF … = some (Nf, ρ, I)` of the split (as given by `ls_split`): within
`9700 n + 70 k + 5 log₂ (2 W₀) + mbTD #B (encB' W₀) W₀ + 30 n + 3990` steps, `LsR`, the saved
parameters (`8558 = #B`, `8559 = [holeStep]`, `8560 = K`, `8561 = A`), and the output of
`lsB_path` for `ρ` (`PathPD` of `g ∘ IX'` at `E + n`); memory below `E` kept.
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

/-- The set-up, stage 5 and the path. -/
def lsP : Stmt := .seq lsA (.seq lgS5D lsB)

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 8000000 in
/-- **The set-up, stage 5 and the path** (see the module docstring). -/
theorem lsPath_exec (hloopM : ∀ d, M.head d ≠ M.tail d) {gid : D → ℕ} {ν : V → ℕ}
    {S T Q : Finset V} {xc : MCall M} {g : ℕ → D} (c : Config) (hc : WordsBounded W c)
    {d m k R n Sb bfl : ℕ} (r4 : c.nreg 3004 = d) (r50 : c.nreg 6500 = Sb) (hm : c.nmem d = m)
    (hk : c.nmem (d + 1) = k) (hRm : c.nmem (d + 7 * m + 4) = R) (hRn : c.nmem R = n)
    (hA : RArr M gid ν S T xc m n R g c.nmem) (hk' : xc.2.1.length = k)
    (lR : R + 3 + 6 * n + m ≤ Sb) (o2 : d + 7 * m + 4 < R)
    (hTS : TailSorted M gid ν) (hQ : QPar Q ν) (hν : Injective ν)
    (hP : PcOK M S T xc.1.piece xc.2.1)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {st : Perm D}
    (hCI : CInvS M Q xc.1.piece xc.2.1 st) (hnt : nTouch M xc.1.piece xc.2.1 ≤ 6)
    (hSP : ∀ i < n, g i ∈ pdarts M (core M Q xc.1.piece) xc.2.1 →
      c.nmem (R + 3 + 5 * n + i) < n ∧ g (c.nmem (R + 3 + 5 * n + i)) = st (g i))
    {eG : ℕ → D} {N : ℕ} (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d)
    (d₀ : D) (hRb : c.nmem (R + 2) = bfl) (hb : bfl ≤ 1)
    (hgid : Injective gid) (hpk : PkMin gid (pcChoiceE M Q eG N d₀).pick)
    {Nf : Finset D} {ρ : HPath M} {Ic : Finset (Finset D)}
    (hcert : pcertF M (pcChoiceE M Q eG N d₀)
      (s5sc M eG N xc.2.1 (s5Av M xc.1.piece xc.2.1 (decide (bfl = 1)))
        (s5Wv M xc.1.piece xc.2.1 (decide (bfl = 1)))) Q xc.1.piece xc.2.1
        (s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1))) st = some (Nf, ρ, Ic))
    (hn : 1 ≤ n)
    (w5 : Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 600 * n + 10 * k +
      2 * encB' (s5Wv M xc.1.piece xc.2.1 (decide (bfl = 1))) +
      20 * s5Wv M xc.1.piece xc.2.1 (decide (bfl = 1)) +
      s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1)) + s5Av M xc.1.piece xc.2.1 (decide (bfl = 1)) +
      400 ≤ W) (w2 : 100 ≤ W) :
    ∃ c' t, Exec I W lsP c c' t ∧
      t ≤ 9700 * n + 70 * k + 5 * Nat.log 2 (2 * s5Wv M xc.1.piece xc.2.1 (decide (bfl = 1))) +
        mbTD (pdarts M (core M Q xc.1.piece) xc.2.1).card
          (encB' (s5Wv M xc.1.piece xc.2.1 (decide (bfl = 1))))
          (s5Wv M xc.1.piece xc.2.1 (decide (bfl = 1))) + 30 * n + 3990 ∧
      LsR c' m k R n Sb ∧ c'.nreg 3100 = R ∧ c'.nreg 3102 = k ∧
      c'.nreg 8558 = (pdarts M (core M Q xc.1.piece) xc.2.1).card ∧
      c'.nreg 8559 = bf (holeStep M xc.1.piece xc.2.1 (decide (bfl = 1)) = true) ∧
      c'.nreg 8560 = s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1)) ∧
      c'.nreg 8561 = s5Av M xc.1.piece xc.2.1 (decide (bfl = 1)) ∧
      c'.nreg 8571 = Sb + 21 * m + 38 * n + 8 * k + 24 + n ∧
      1 ≤ c'.nreg 8557 ∧ c'.nreg 8557 ≤ n ∧
      (pdarts M (core M Q xc.1.piece) xc.2.1).card ≤ c'.nreg 8557 ∧
      (∀ q < c'.nreg 8557, c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q) < n) ∧
      (0 < m → ∀ q < c'.nreg 8557,
        g (c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q)) ∈ pdarts M xc.1.piece xc.2.1) ∧
      (∀ q < (pdarts M (core M Q xc.1.piece) xc.2.1).card,
        g (c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q)) ∈
          pdarts M (core M Q xc.1.piece) xc.2.1) ∧
      (∀ y ∈ pdarts M (core M Q xc.1.piece) xc.2.1,
        ∃ q < (pdarts M (core M Q xc.1.piece) xc.2.1).card,
          g (c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q)) = y) ∧
      PathPD M (fun q => g (c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q))) (c'.nreg 8557)
        (Sb + 21 * m + 38 * n + 8 * k + 24 + n) c' ρ ∧
      (∀ a, a < Sb + 21 * m + 38 * n + 8 * k + 24 → c'.nmem a = c.nmem a) ∧
      (∀ x, 3000 ≤ x → x ≤ 3012 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set E := Sb + 21 * m + 38 * n + 8 * k + 24 with hE
  set U := E + 4 * n + 3 with hU
  have hnc : n = xc.1.piece.card := hA.card
  have hBn : (pdarts M (core M Q xc.1.piece) xc.2.1).card ≤ n := by rw [hnc]; exact card_le_card fun y hy => (mem_core.1 (mem_pdarts.1 hy).1).1
  have hKA := ls_KA_le (b := decide (bfl = 1)) hnt
  -- the set-up
  obtain ⟨c₁, t₁, e₁, ht₁, hR1, a00, a01, a02, n1, m1, rr1, rm1, o1⟩ := lsA_exec (I := I) c hc
    r4 r50 hm hk hRm hRn (by omega) (by omega) (by omega) (by omega)
  -- stage 5
  obtain ⟨c₂, t₂, e₂, ht₂, M2, K2, rr2, rm2, o2, s03, s04, s05, s06, s07, s08, ix, ixs, ixm, -,
    hout⟩ := lgS5D_execW (I := I) hloopM (Q := Q) (x := xc) (bb := decide (bfl = 1)) c₁ e₁.wb_right
      (by rw [m1]; exact hA) hTS hQ hν hP hQdeg hQ5 hCI hnt (by rw [m1]; exact hSP) he hesurj d₀
      a00 a01 (by rw [a02, hk']) (by rw [m1]; exact hRn) (by rw [m1]; exact hRb) hb
      (by simp) (by omega) (by omega)
  have hR2 : LsR c₂ m k R n Sb := hR1.congr fun x hx => K2 x (by unfold s5Keep; omega)
  -- the outcome of stage 5 for `ρ`
  have hcase : (0 < (pdarts M (core M Q xc.1.piece) xc.2.1).card ∧ c₂.nreg 4900 = 0 ∧ PathPD M
        (fun j => g (c₂.nmem (U + 2 * n + j))) (pdarts M (core M Q xc.1.piece) xc.2.1).card
        (U + 42 * n + 5 * k + 34 * (pdarts M (core M Q xc.1.piece) xc.2.1).card + c₂.nreg 3109 + 3 * c₂.nreg 3108 + 47 + 6 * (pdarts M (core M Q xc.1.piece) xc.2.1).card)
        c₂ ρ) ∨
      (0 < (pdarts M (core M Q xc.1.piece) xc.2.1).card ∧ c₂.nreg 4900 = 2 ∧ c₂.nreg 4902 < (pdarts M (core M Q xc.1.piece) xc.2.1).card ∧
        ρ = (SPath.point (M' := M) (g (c₂.nmem (U + 2 * n + c₂.nreg 4902)))
          (M.tail (g (c₂.nmem (U + 2 * n + c₂.nreg 4902))))).toH) ∨
      ((pdarts M (core M Q xc.1.piece) xc.2.1).card = 0 ∧ ∃ pk : Finset D → D, PkMin gid pk ∧ Injective gid ∧ QPar Q ν ∧
        ρ = (SPath.point (M' := M)
          (if (pdarts M xc.1.piece xc.2.1).Nonempty then
            (if M.tail (pk (pdarts M xc.1.piece xc.2.1)) ∈ Q then M.rev (pk (pdarts M xc.1.piece xc.2.1))
              else pk (pdarts M xc.1.piece xc.2.1)) else pk xc.1.piece)
          (M.tail (if (pdarts M xc.1.piece xc.2.1).Nonempty then
            (if M.tail (pk (pdarts M xc.1.piece xc.2.1)) ∈ Q then M.rev (pk (pdarts M xc.1.piece xc.2.1))
              else pk (pdarts M xc.1.piece xc.2.1)) else pk xc.1.piece))).toH) := by
    rcases ls_cert_cases hcert with ⟨hne, -, I', hsc⟩ | ⟨h0, -, hρ⟩
    · have hpos : 0 < (pdarts M (core M Q xc.1.piece) xc.2.1).card := card_pos.2 hne
      rcases hout with h0 | ⟨-, v09, ⟨-, hnone⟩ | ⟨-, ρ', I'', hsome, e', he', -, hpath⟩⟩
      · omega
      · exfalso
        have : scertD (s5sc M eG N xc.2.1 (s5Av M xc.1.piece xc.2.1 (decide (bfl = 1))) (s5Wv M xc.1.piece xc.2.1 (decide (bfl = 1)))) xc.2.1 (pdarts M (core M Q xc.1.piece) xc.2.1) st
            (s5ex M Q eG N d₀ xc.1.piece xc.2.1 (s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1)))) = some (ρ, I') := hsc
        rw [this] at hnone; cases hnone
      · have : scertD (s5sc M eG N xc.2.1 (s5Av M xc.1.piece xc.2.1 (decide (bfl = 1))) (s5Wv M xc.1.piece xc.2.1 (decide (bfl = 1)))) xc.2.1 (pdarts M (core M Q xc.1.piece) xc.2.1) st
            (s5ex M Q eG N d₀ xc.1.piece xc.2.1 (s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1)))) = some (ρ, I') := hsc
        rw [this] at hsome
        injection hsome with hsome
        have hρρ : ρ = ρ' := (Prod.mk.inj hsome).1
        rcases hpath with ⟨h49, hNHD⟩ | ⟨h49, h02, hpt⟩
        · refine Or.inl ⟨hpos, h49, ?_⟩
          rw [hρρ, v09, s08]
          refine pathPD_congr hNHD.2 (fun j hj => by congr 1; omega) (fun i hi => ?_)
          exact (he' i hi).symm
        · refine Or.inr (Or.inl ⟨hpos, h49, h02, ?_⟩)
          rw [hρρ, hpt, he' _ h02]
    · refine Or.inr (Or.inr ⟨by rw [h0]; rfl, _, hpk, hgid, hQ, ?_⟩)
      rw [hρ, pemptyD_path]
  have h3109 : 0 < (pdarts M (core M Q xc.1.piece) xc.2.1).card →
      c₂.nreg 3109 = encB' (s5Wv M xc.1.piece xc.2.1 (decide (bfl = 1))) := fun h => by
    rcases hout with h0 | ⟨-, v09, -⟩
    · omega
    · exact v09
  -- the path
  obtain ⟨c₃, t₃, e₃, ht₃, hR3, v58, v59, v60, v61, v71, n1', n2', n3', ix3, pd3, B3, Bs3, PD3,
    M3, F3, rr3, rm3, o3⟩ := lsB_path (I := I) (Q := Q) (xc := xc) c₂ e₂.wb_right hR2
      (hA.congr fun a h1 h2 => by rw [M2 a (by omega), m1]) hk' rfl s03 ix ixs hcase hP.rev hn lR
      (fun h _ => by rw [s08, h3109 h]; have := hKA; omega) (by omega) (by omega)
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, hR3, ?_, ?_, v58, ?_, ?_, ?_, v71,
    n1', n2', n3', ix3, pd3, B3, Bs3, PD3, fun a ha => ?_, fun x h1 h2 => ?_,
    by rw [rr3, rr2, rr1], by rw [rm3, rm2, rm1], by rw [o3, o2, o1]⟩
  · rw [F3 _ (by omega), K2 _ (by unfold s5Keep; omega)]; exact a00
  · rw [F3 _ (by omega), K2 _ (by unfold s5Keep; omega)]; exact a02
  · rw [v59, s05]
  · rw [v60, s06]
  · rw [v61, s07]
  · rw [M3 a (Or.inl ha), M2 a (by omega), m1]
  · rw [F3 x (by omega), K2 x (by unfold s5Keep; omega), n1 x (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
