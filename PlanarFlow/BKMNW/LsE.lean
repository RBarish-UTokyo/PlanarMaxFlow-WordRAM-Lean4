module

public import PlanarFlow.BKMNW.LsD

/-!
# `sepL`: stage 6, the core's flags and the path's flags (`lsC ; nfProg ; lsCC ; lsD ; lgPF`)

**`ls6_exec`**: from the path written by `lsB` (`PathPD` of `g ∘ IX'`), within
`300 n + 20 k + 300` steps: `NF[i] = [g i ∈ pcNf]` at `U + n + k + 1`, `CC[i] = [g i ∈ B]` at
`CCb`, the vertex keys at `Yb` (`< n`, equal iff the tails are), `DF[i] = [g i ∈ ρ.darts]` at
`Yb + 2 n + 1`, `VF[i] = [tail (g i) ∈ ρ.mverts]` at `Yb + 3 n + 2`, every vertex of `ρ` a tail
of the record; memory below `U` kept.
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

/-- Stage 6 of `sepL` with the flags of the path. -/
def ls6 : Stmt := .seq lsC (.seq nfProg (.seq lsCC (.seq lsD lgPF)))

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **Stage 6 and the path's flags** (see the module docstring). -/
theorem ls6_exec {gid : D → ℕ} {ν : V → ℕ} {S T Q : Finset V} {xc : MCall M} {g : ℕ → D}
    (c : Config) (hc : WordsBounded W c) {m k R n Sb nB n' U : ℕ} (hR : LsR c m k R n Sb)
    (hU : U = Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3)
    (hA : RArr M gid ν S T xc m n R g c.nmem) (hk : xc.2.1.length = k) (hRn : c.nmem R = n)
    (hQ : QPar Q ν) (hd : xc.2.1.Pairwise Disjoint) (hTS : TailSorted M gid ν)
    (hν : Injective ν) (r00 : c.nreg 3100 = R) (r02 : c.nreg 3102 = k)
    (r58 : c.nreg 8558 = nB) (hB : nB = (pdarts M (core M Q xc.1.piece) xc.2.1).card)
    (r57 : c.nreg 8557 = n') (hn'1 : 1 ≤ n') (hn' : n' ≤ n) (hnB : nB ≤ n')
    (r71 : c.nreg 8571 = Sb + 21 * m + 38 * n + 8 * k + 24 + n)
    (hIX : ∀ q < n', c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q) < n)
    (hIXB : ∀ q < nB, g (c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q)) ∈
      pdarts M (core M Q xc.1.piece) xc.2.1)
    (hIXs : ∀ y ∈ pdarts M (core M Q xc.1.piece) xc.2.1, ∃ q < nB,
      g (c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q)) = y)
    {ρ : HPath M}
    (hPD : PathPD M (fun q => g (c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q))) n'
      (Sb + 21 * m + 38 * n + 8 * k + 24 + n) c ρ)
    (hn : 1 ≤ n) (lR : R + 3 + 6 * n + m ≤ Sb) (w : U + 46 * n + 9 * k + 15 ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W ls6 c c' t ∧ t ≤ 300 * n + 20 * k + 300 ∧ LsR c' m k R n Sb ∧
      LsL c' n k U ∧
      (∀ i < n, c'.nmem (U + n + k + 1 + i) = bf (g i ∈ pcNf M Q xc.1.piece xc.2.1)) ∧
      (∀ i < n, c'.nmem (U + 45 * n + 9 * k + 15 + i) =
        bf (g i ∈ pdarts M (core M Q xc.1.piece) xc.2.1)) ∧
      (∀ i < n, c'.nmem (U + 2 * n + k + 1 + i) < n ∧ ∀ j < n,
        (c'.nmem (U + 2 * n + k + 1 + i) = c'.nmem (U + 2 * n + k + 1 + j) ↔
          M.tail (g i) = M.tail (g j))) ∧
      (∀ i < n, c'.nmem (U + 4 * n + k + 2 + i) = bf (g i ∈ ρ.darts.toFinset)) ∧
      (∀ i < n, c'.nmem (U + 5 * n + k + 3 + i) = bf (M.tail (g i) ∈ ρ.mverts)) ∧
      (∀ v ∈ ρ.mverts, ∃ i < n, M.tail (g i) = v) ∧
      (∀ a, a < U → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 3100 ∨ (8550 ≤ x ∧ x < 8564) ∨ (8564 < x ∧ x < 8582) ∨ 8586 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set E := Sb + 21 * m + 38 * n + 8 * k + 24 with hE
  unfold ls6
  -- the bases
  obtain ⟨c₁, t₁, e₁, ht₁, hL1, a3111, n1, m1, rr1, rm1, o1⟩ := lsC_exec (I := I) c hc hR hU w w2
  have hR1 : LsR c₁ m k R n Sb := hR.congr fun x hx => n1 x (by omega)
  -- stage 6
  obtain ⟨c₂, t₂, e₂, ht₂, NF2, m2, n2, rr2, rm2, o2⟩ := nfProg_recW (I := I) (Q := Q) hQ hd c₁
    e₁.wb_right (by rw [m1]; exact hA) (Y := U) (by rw [n1 _ (by omega)]; exact r00)
    (by rw [n1 _ (by omega), hk]; exact r02) a3111 (by rw [m1]; exact hRn) (by omega)
    (by rw [hk]; omega)
  rw [hk] at NF2 m2
  have q2 : ∀ x, ¬ nfW x → c₂.nreg x = c₁.nreg x := n2
  have hR2 : LsR c₂ m k R n Sb := hR1.congr fun x hx => q2 x (by unfold nfW; omega)
  have hL2 : LsL c₂ n k U := hL1.congr fun x hx => q2 x (by unfold nfW; omega)
  have M2 : ∀ a, a < U → c₂.nmem a = c.nmem a := fun a ha => by
    rw [m2 a (by omega), m1]
  -- the core's flags
  obtain ⟨c₃, t₃, e₃, ht₃, CC3, m3, n3, rr3, rm3, o3⟩ := lsCC_exec (I := I) c₂ e₂.wb_right hR2
    hL2 (nB := nB) (by rw [q2 _ (by unfold nfW; omega), n1 _ (by omega)]; exact r58)
    (by omega) hU.symm (fun q hq => by rw [M2 _ (by omega)]; exact hIX q (by omega)) w w2
  have hR3 : LsR c₃ m k R n Sb := hR2.congr fun x hx => n3 x (by omega)
  have hL3 : LsL c₃ n k U := hL2.congr fun x hx => n3 x (by omega)
  have M3 : ∀ a, a < U + 45 * n + 9 * k + 15 → c₃.nmem a = c₂.nmem a := fun a ha =>
    m3 a (by omega)
  -- the registers of `lgPF`
  obtain ⟨c₄, t₄, e₄, ht₄, d00, d17, d01, d02, d03, d11, d12, n4, m4, rr4, rm4, o4⟩ :=
    lsD_exec (I := I) c₃ e₃.wb_right hR3 hL3 (by omega) w2
  have e57 : c₃.nreg 8557 = n' := by
    rw [n3 _ (by omega), q2 _ (by unfold nfW; omega), n1 _ (by omega)]; exact r57
  have e55 : c₃.nreg 8555 = E := hR3.r55
  have e71 : c₃.nreg 8571 = E + n := by
    rw [n3 _ (by omega), q2 _ (by unfold nfW; omega), n1 _ (by omega)]; exact r71
  rw [e57] at d17; rw [e55] at d02; rw [e71] at d03
  have M4 : ∀ a, a < U → c₄.nmem a = c.nmem a := fun a ha => by
    rw [m4, M3 a (by omega), M2 a ha]
  -- `lgPF`
  obtain ⟨c₅, t₅, e₅, ht₅, DF5, VF5, VK5, m5, n5, rr5, rm5, o5⟩ := lgPF_execK (P := I) c₄
    e₄.wb_right (n' := n') d00 d17 d01 d02 d03 d11 d12 hn hn'1 hn'1 hn'
    (fun i hi => by rw [M4 _ (by omega)]; exact (hA.rp i hi).1)
    (fun q hq => by rw [M4 _ (by omega)]; exact hIX q hq)
    (fun j hj => by
      rw [M4 _ (by omega)]
      obtain ⟨hk', hd', hz⟩ := hPD
      by_cases hj' : j ≤ ρ.k
      · obtain ⟨i, hi, h1, -⟩ := hd' j hj'; omega
      · rw [hz j hj (by omega)]; omega)
    ⟨by omega, by omega, by omega, by omega, by omega⟩
  -- the semantics
  have hvp : ∀ i < n, c₄.nmem (R + 3 + 4 * n + i) = ν (M.tail (g i)) := fun i hi => by
    rw [M4 _ (by omega)]; exact hA.vp i hi
  have hmono : ∀ i j, i < j → j < n → c₄.nmem (R + 3 + 4 * n + i) ≤ c₄.nmem (R + 3 + 4 * n + j) :=
    fun i j hij hj => by
      rw [hvp i (by omega), hvp j hj]; exact hTS _ _ (hA.g_mono i j hij hj)
  have hPD4 : PathPD M (fun q => g (c₄.nmem (E + q))) n' (E + n) c₄ ρ :=
    pathPD_congr hPD (fun j hj => M4 _ (by omega)) (fun i hi => by
      show g (c₄.nmem (E + i)) = g (c.nmem (E + i)); rw [M4 _ (by omega)])
  obtain ⟨hPf, hSh, hkn, -⟩ := pfIn_of (M := M) (g := g) (n := n)
    (rp := fun i => c₄.nmem (R + 3 + n + i)) (vp := fun i => c₄.nmem (R + 3 + 4 * n + i))
    (ix := fun q => c₄.nmem (E + q)) (fun i hi j hj h => hA.g_inj hi hj h)
    (fun i hi => by rw [M4 _ (by omega)]; exact hA.rp i hi) hvp hmono hν
    (fun q hq => ⟨by rw [M4 _ (by omega)]; exact hIX q hq, rfl⟩) hn' hPD4
  have hvkn : ∀ i < n, vkF (fun j => c₄.nmem (R + 3 + 4 * n + j)) i < n := fun i hi =>
    lt_of_le_of_lt (vkF_le _ i) hi
  have M5 : ∀ a, a < U + 2 * n + k + 1 → c₅.nmem a = c₄.nmem a := fun a ha => m5 a (by omega)
  refine ⟨c₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))),
    by omega, hR3.congr fun x hx => ?_, hL3.congr fun x hx => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun v hv => pf_mverts_tail hPf hv,
    fun a ha => ?_, fun x hx => ?_, by rw [rr5, rr4, rr3, rr2, rr1], by rw [rm5, rm4, rm3, rm2, rm1],
    by rw [o5, o4, o3, o2, o1]⟩
  · rw [n5 x (by unfold pfKeepR; omega), n4 x (by omega)]
  · rw [n5 x (by unfold pfKeepR; omega), n4 x (by omega)]
  · rw [M5 _ (by omega), m4, M3 _ (by omega)]; exact NF2 i hi
  · rw [m5 _ (by omega), m4, CC3 i hi]
    classical
    by_cases h : g i ∈ pdarts M (core M Q xc.1.piece) xc.2.1
    · obtain ⟨q, hq, hq'⟩ := hIXs _ h
      have hex : ∃ q < nB, c₂.nmem (E + q) = i := ⟨q, hq, by
        rw [M2 _ (by omega)]; exact hA.g_inj (hIX q (by omega)) hi hq'⟩
      rw [iteT hex]
      unfold bf; rw [iteT h]
    · rw [iteF ?_]
      · unfold bf; rw [iteF h]
      · rintro ⟨q, hq, hq'⟩
        rw [M2 _ (by omega)] at hq'
        exact h (hq' ▸ hIXB q hq)
  · rw [VK5 i hi]
    refine ⟨hvkn i hi, fun j hj => ?_⟩
    rw [VK5 j hj, vkF_eq_iff hmono hi hj, hvp i hi, hvp j hj]
    exact hν.eq_iff
  · rw [show U + 4 * n + k + 2 + i = U + 2 * n + k + 1 + 2 * n + 1 + i by omega, DF5 i hi]
    exact (lgPF_flags hPf hSh hkn hi (hvkn i hi)).1
  · rw [show U + 5 * n + k + 3 + i = U + 2 * n + k + 1 + 3 * n + 2 + i by omega, VF5 i hi]
    exact (lgPF_flags hPf hSh hkn hi (hvkn i hi)).2
  · rw [M5 a (by omega)]; exact M4 a ha
  · rw [n5 x (by unfold pfKeepR; omega), n4 x (by omega), n3 x (by omega),
      q2 x (by unfold nfW; omega), n1 x (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
