module

public import PlanarFlow.BKMNW.LsK

/-!
# `sepL`, first half: `lsP ; ls6 ; ls7`

**`lsHalf1_exec`**: `lsPath_exec`, `ls6_exec` and `ls7_exec` in a row: from the record of a
large piece, the state `st`, the certificate `(Nf, ρ, I)` of the split (`Nf = pcNf`) with the
facts of `s7_exec`: the scratch flags `LF = [g i ∈ l]` (`l` the `twoGroupsL` union),
`DF = [g i ∈ ρ.darts]`, `VF = [tail (g i) ∈ ρ.mverts]`, `CC = [g i ∈ B]`, the hole flags, the
path `PathPD` of `g ∘ IX'` at `E + n`; memory below `Sb` kept.
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

/-- The first half of `sepL`. -/
def lsH1 : Stmt := .seq lsP (.seq ls6 ls7)

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 8000000 in
/-- **The first half of `sepL`** (see the module docstring). -/
theorem lsHalf1_exec (hloopM : ∀ d, M.head d ≠ M.tail d) {gid : D → ℕ} {ν : V → ℕ}
    {S T Q : Finset V} {xc : MCall M} {g en : ℕ → D} (c : Config) (hc : WordsBounded W c)
    {d m k R n Sb bfl : ℕ} (r4 : c.nreg 3004 = d) (r50 : c.nreg 6500 = Sb) (hm : c.nmem d = m)
    (hk : c.nmem (d + 1) = k) (hRm : c.nmem (d + 7 * m + 4) = R) (hRn : c.nmem R = n)
    (hA : RArr M gid ν S T xc m n R g c.nmem) (hk' : xc.2.1.length = k)
    (hFX : ∀ i < m, g (c.nmem (R + 3 + 6 * n + i)) = en i)
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
    (hNfe : Nf = pcNf M Q xc.1.piece xc.2.1)
    (hY : HClosed xc.2.1 (newHole xc.2.1 ρ.mverts))
    (hC : IsCls xc.1.piece (clsF M xc.1.piece Nf xc.2.1
      (s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1))) ρ)) (hNf : Nf ⊆ xc.1.piece)
    (hAw : ∀ X ∈ xc.1.piece.image (clsF M xc.1.piece Nf xc.2.1
      (s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1))) ρ),
      hw M (s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1))) xc.2.1 ρ.mverts X ≤
        s5Av M xc.1.piece xc.2.1 (decide (bfl = 1)))
    (htH : s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1)) ≠ 0 → ∀ d ∈ xc.1.piece, ∀ d' ∈ xc.1.piece,
      clsF M xc.1.piece Nf xc.2.1 (s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1))) ρ d ≠
        clsF M xc.1.piece Nf xc.2.1 (s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1))) ρ d' →
      Disjoint (tH M xc.2.1 ρ.mverts (clsF M xc.1.piece Nf xc.2.1
          (s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1))) ρ d))
        (tH M xc.2.1 ρ.mverts (clsF M xc.1.piece Nf xc.2.1
          (s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1))) ρ d')))
    (hn : 1 ≤ n)
    (w5 : Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 600 * n + 10 * k +
      2 * encB' (s5Wv M xc.1.piece xc.2.1 (decide (bfl = 1))) +
      20 * s5Wv M xc.1.piece xc.2.1 (decide (bfl = 1)) +
      s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1)) + s5Av M xc.1.piece xc.2.1 (decide (bfl = 1)) +
      400 ≤ W) (w : Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 55 * n + 9 * k + 17 ≤ W)
    (wK : s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1)) * nTouch M xc.1.piece xc.2.1 ≤ W)
    (wA : 3 * s5Av M xc.1.piece xc.2.1 (decide (bfl = 1)) ≤ W) (w2 : 100 ≤ W) :
    ∃ c' t, Exec I W lsH1 c c' t ∧
      t ≤ 9700 * n + 70 * k + 5 * Nat.log 2 (2 * s5Wv M xc.1.piece xc.2.1 (decide (bfl = 1))) +
        mbTD (pdarts M (core M Q xc.1.piece) xc.2.1).card
          (encB' (s5Wv M xc.1.piece xc.2.1 (decide (bfl = 1))))
          (s5Wv M xc.1.piece xc.2.1 (decide (bfl = 1))) + 930 * n + 30 * m + 90 * k + 4890 ∧
      LsR c' m k R n Sb ∧ LsL c' n k (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3) ∧
      c'.nreg 8559 = bf (holeStep M xc.1.piece xc.2.1 (decide (bfl = 1)) = true) ∧
      c'.nreg 8571 = Sb + 21 * m + 38 * n + 8 * k + 24 + n ∧
      1 ≤ c'.nreg 8557 ∧ c'.nreg 8557 ≤ n ∧
      (∀ q < c'.nreg 8557, c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q) < n) ∧
      (0 < m → ∀ q < c'.nreg 8557,
        g (c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q)) ∈ pdarts M xc.1.piece xc.2.1) ∧
      PathPD M (fun q => g (c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q))) (c'.nreg 8557)
        (Sb + 21 * m + 38 * n + 8 * k + 24 + n) c' ρ ∧
      (∀ i < n, c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 44 * n + 9 * k + 14 + i) =
        bf (g i ∈ (twoGroupsL (hw M (s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1))) xc.2.1
          ρ.mverts) (s5Av M xc.1.piece xc.2.1 (decide (bfl = 1)))
          (ordE eG N (xc.1.piece.image (clsF M xc.1.piece Nf xc.2.1
            (s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1))) ρ)))).toFinset.biUnion _root_.id)) ∧
      (∀ i < n, c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 4 * n + k + 2 + i) =
        bf (g i ∈ ρ.darts.toFinset)) ∧
      (∀ i < n, c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 5 * n + k + 3 + i) =
        bf (M.tail (g i) ∈ ρ.mverts)) ∧
      (∀ i < n, c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 45 * n + 9 * k + 15 + i) =
        bf (g i ∈ pdarts M (core M Q xc.1.piece) xc.2.1)) ∧
      (∀ j < k, c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 11 * n + k + 4 + j) =
        bf (¬ Disjoint (xc.2.1.getD j ∅) ρ.mverts)) ∧
      (∀ a, a < Sb → c'.nmem a = c.nmem a) ∧
      (∀ x, 3000 ≤ x → x ≤ 3012 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hKA := ls_KA_le (b := decide (bfl = 1)) hnt
  unfold lsH1
  obtain ⟨c₁, t₁, e₁, ht₁, hR1, a00, a02, v58, v59, v60, v61, v71, n1, n2, n3, ix, ixp, ixB,
    ixBs, hPD, M1, F1, rr1, rm1, o1⟩ := lsPath_exec (I := I) hloopM c hc r4 r50 hm hk hRm hRn hA
      hk' lR o2 hTS hQ hν hP hQdeg hQ5 hCI hnt hSP he hesurj d₀ hRb hb hgid hpk hcert hn w5
      (by omega)
  have hA1 : RArr M gid ν S T xc m n R g c₁.nmem := hA.congr fun a h1 h2 => M1 a (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, hR2, hL2, NF, CC, VK, DF, VF, tl, M2, F2, rr2, rm2, o2'⟩ :=
    ls6_exec (I := I) (Q := Q) c₁ e₁.wb_right hR1 rfl hA1 hk' (by rw [M1 _ (by omega)]; exact hRn)
      hQ hP.disj hTS hν a00 a02 v58 rfl rfl n1 n2 n3 v71 ix ixB ixBs hPD hn lR (by omega)
      (by omega)
  have hA2 : RArr M gid ν S T xc m n R g c₂.nmem := hA1.congr fun a h1 h2 => M2 a (by omega)
  have g60 : c₂.nreg 8560 = s5Kv M xc.1.piece xc.2.1 (decide (bfl = 1)) := by
    rw [F2 _ (by omega)]; exact v60
  have g61 : c₂.nreg 8561 = s5Av M xc.1.piece xc.2.1 (decide (bfl = 1)) := by
    rw [F2 _ (by omega)]; exact v61
  obtain ⟨c₃, t₃, e₃, ht₃, hR3, hL3, LF, hlr, HT, M3, F3, rr3, rm3, o3⟩ := ls7_exec (I := I)
    (en := en) (Nf := Nf) (ρ := ρ) c₂ e₂.wb_right hR2 hL2 rfl hA2 hk' hP.disj
    (fun i hi => by rw [M2 _ (by omega), M1 _ (by omega)]; exact hFX i hi)
    (fun i hi => by rw [NF i hi, hNfe]) VK DF VF tl g60 g61 he hesurj hY hC hNf hAw htH wK wA lR
    (by omega) (by omega)
  have M23 : ∀ a, (Sb + 3 * m + k ≤ a ∧ a < Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 +
      10 * n + k + 3) → c₃.nmem a = c₂.nmem a := fun a ha => M3 a (by omega) (by omega)
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, hR3, hL3, ?_, ?_, ?_, ?_,
    fun q hq => ?_, fun hm q hq => ?_, ?_, LF, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    HT, fun a ha => ?_, fun x h1 h2 => ?_, by rw [rr3, rr2, rr1], by rw [rm3, rm2, rm1],
    by rw [o3, o2', o1]⟩
  · rw [F3 _ (by omega), F2 _ (by omega)]; exact v59
  · rw [F3 _ (by omega), F2 _ (by omega)]; exact v71
  · rw [F3 _ (by omega), F2 _ (by omega)]; exact n1
  · rw [F3 _ (by omega), F2 _ (by omega)]; exact n2
  · rw [F3 _ (by omega), F2 _ (by omega)] at hq
    rw [M23 _ (by omega), M2 _ (by omega)]; exact ix q hq
  · rw [F3 _ (by omega), F2 _ (by omega)] at hq
    rw [M23 _ (by omega), M2 _ (by omega)]; exact ixp hm q hq
  · rw [F3 _ (by omega), F2 _ (by omega)]
    refine pathPD_congr hPD (fun j hj => ?_) (fun i hi => ?_)
    · rw [M23 _ (by omega), M2 _ (by omega)]
    · show g (c₃.nmem _) = g (c₁.nmem _)
      rw [M23 _ (by omega), M2 _ (by omega)]
  · rw [M23 _ (by omega)]; exact DF i hi
  · rw [M23 _ (by omega)]; exact VF i hi
  · rw [M3 _ (by omega) (by omega)]; exact CC i hi
  · rw [M3 a (by omega) (by omega), M2 a (by omega), M1 a (by omega)]
  · rw [F3 x (by omega), F2 x (by omega)]; exact F1 x h1 h2

end Exec

end MfDrv

end BKMNW

end PlanarFlow
