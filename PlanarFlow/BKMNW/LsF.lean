module

public import PlanarFlow.BKMNW.LsE

/-!
# `sepL`: stage 7 (`lsE ; s7`)

**`ls7_exec`**: from the flags of `ls6_exec`, the certificate's facts (`HClosed`, `IsCls` of
`clsF`, `Nf ⊆ P`, `hw ≤ A`, disjoint `tH` for `K ≠ 0`) and `K = r8560`, `A = r8561`: within
`600 n + 30 m + 70 k + 600` steps the flags `LF[i] = [g i ∈ l]` of the left piece
`l = (twoGroupsL … (ordE eG N …)).toFinset.biUnion id` at `U + 44 n + 9 k + 14`, the hole flags
at `U + 11 n + k + 4`; memory outside `[Sb, Sb + 3 m + k)` and `[Z, Z + 35 n + 8 k + 11)` kept.
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

/-- Stage 7 of `sepL`. -/
def ls7 : Stmt := .seq lsE s7

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **Stage 7** (see the module docstring). -/
theorem ls7_exec {gid : D → ℕ} {ν : V → ℕ} {S T : Finset V} {xc : MCall M} {g en : ℕ → D}
    (c : Config) (hc : WordsBounded W c) {m k R n Sb U K A : ℕ} (hR : LsR c m k R n Sb)
    (hL : LsL c n k U) (hU : U = Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3)
    (hA : RArr M gid ν S T xc m n R g c.nmem) (hk : xc.2.1.length = k)
    (hd : xc.2.1.Pairwise Disjoint) (hFX : ∀ i < m, g (c.nmem (R + 3 + 6 * n + i)) = en i)
    {Nf : Finset D} {ρ : HPath M}
    (hNF : ∀ i < n, c.nmem (U + n + k + 1 + i) = bf (g i ∈ Nf))
    (hVK : ∀ i < n, c.nmem (U + 2 * n + k + 1 + i) < n ∧ ∀ j < n,
      (c.nmem (U + 2 * n + k + 1 + i) = c.nmem (U + 2 * n + k + 1 + j) ↔
        M.tail (g i) = M.tail (g j)))
    (hDF : ∀ i < n, c.nmem (U + 4 * n + k + 2 + i) = bf (g i ∈ ρ.darts.toFinset))
    (hVF : ∀ i < n, c.nmem (U + 5 * n + k + 3 + i) = bf (M.tail (g i) ∈ ρ.mverts))
    (htail : ∀ v ∈ ρ.mverts, ∃ i < n, M.tail (g i) = v)
    (r60 : c.nreg 8560 = K) (r61 : c.nreg 8561 = A)
    {eG : ℕ → D} {N : ℕ} (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d)
    (hY : HClosed xc.2.1 (newHole xc.2.1 ρ.mverts))
    (hC : IsCls xc.1.piece (clsF M xc.1.piece Nf xc.2.1 K ρ)) (hNf : Nf ⊆ xc.1.piece)
    (hAw : ∀ X ∈ xc.1.piece.image (clsF M xc.1.piece Nf xc.2.1 K ρ),
      hw M K xc.2.1 ρ.mverts X ≤ A)
    (htH : K ≠ 0 → ∀ d ∈ xc.1.piece, ∀ d' ∈ xc.1.piece,
      clsF M xc.1.piece Nf xc.2.1 K ρ d ≠ clsF M xc.1.piece Nf xc.2.1 K ρ d' →
      Disjoint (tH M xc.2.1 ρ.mverts (clsF M xc.1.piece Nf xc.2.1 K ρ d))
        (tH M xc.2.1 ρ.mverts (clsF M xc.1.piece Nf xc.2.1 K ρ d')))
    (hnt : K * nTouch M xc.1.piece xc.2.1 ≤ W) (hA3 : 3 * A ≤ W)
    (lR : R + 3 + 6 * n + m ≤ Sb) (w : U + 46 * n + 9 * k + 15 ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W ls7 c c' t ∧ t ≤ 600 * n + 30 * m + 70 * k + 600 ∧ LsR c' m k R n Sb ∧
      LsL c' n k U ∧
      (∀ i < n, c'.nmem (U + 44 * n + 9 * k + 14 + i) = bf (g i ∈
        (twoGroupsL (hw M K xc.2.1 ρ.mverts) A
          (ordE eG N (xc.1.piece.image (clsF M xc.1.piece Nf xc.2.1 K ρ)))).toFinset.biUnion
            _root_.id)) ∧
      (∀ i < n, (g i ∈ (xc.1.piece.image (clsF M xc.1.piece Nf xc.2.1 K ρ) \
          (twoGroupsL (hw M K xc.2.1 ρ.mverts) A
            (ordE eG N (xc.1.piece.image (clsF M xc.1.piece Nf xc.2.1 K ρ)))).toFinset).biUnion
              _root_.id ↔
        g i ∉ (twoGroupsL (hw M K xc.2.1 ρ.mverts) A
          (ordE eG N (xc.1.piece.image (clsF M xc.1.piece Nf xc.2.1 K ρ)))).toFinset.biUnion
            _root_.id)) ∧
      (∀ j < k, c'.nmem (U + 11 * n + k + 4 + j) = bf (¬ Disjoint (xc.2.1.getD j ∅) ρ.mverts)) ∧
      (∀ a, ¬ (U + 10 * n + k + 3 ≤ a ∧ a < U + 45 * n + 9 * k + 14) →
        ¬ (Sb ≤ a ∧ a < Sb + 3 * m + k) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4000 ∨ 8588 < x ∨ (8550 ≤ x ∧ x < 8564) ∨ (8564 < x ∧ x < 8587)) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ls7
  obtain ⟨c₁, t₁, e₁, ht₁, a00, a05, a99, a93, a30, a21, a01, a02, a06, a09, a42, a43, a53,
    a31, a32, n1, m1, rr1, rm1, o1⟩ := lsE_exec (I := I) c hc hR hL hU.symm (by omega) w w2
  rw [r60] at a43; rw [r61] at a53
  have hI : S7In M xc.1.piece xc.2.1 ρ.mverts Nf g n (fun i => c.nmem (R + 3 + n + i))
      (fun i => c.nmem (R + 3 + 2 * n + i)) (fun i => c.nmem (U + 2 * n + k + 1 + i))
      (fun i => c.nmem (U + 5 * n + k + 3 + i)) (fun i => c.nmem (U + n + k + 1 + i)) :=
    { mem := hA.g_mem, surj := hA.g_surj, inj := fun i hi j hj h => hA.g_inj hi hj h,
      rp := hA.rp, hp := hA.hp, vk := hVK, vf := hVF, nf := hNF, tail := htail, hd := hd }
  obtain ⟨c₂, t₂, e₂, ht₂, -, -, -, -, LF, hlr, HT, m2, n2, rr2, rm2, o2⟩ :=
    s7_exec (P := I) (K := K) (A := A) (en := en) (eG := eG) (N := N) c₁ e₁.wb_right hI hk
      hA.g_mono he hesurj hY hC hNf hAw htH hnt hA3 a00 a05 a99 a93 a30 a21 a01 a02 a06 a09 a42
      a43 a53 a31 a32 (fun i hi => by rw [m1]) (fun i hi => by rw [m1]) (fun i hi => by rw [m1])
      (fun i hi => by rw [m1]) (fun i hi => by rw [m1])
      (fun i hi => by rw [m1, show U + 4 * n + k + 2 + i = U + 4 * n + k + 2 + i from rfl]; exact hDF i hi)
      (fun i hi => by rw [m1]; exact ⟨hA.fx i hi, hFX i hi⟩)
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega, by omega⟩ (by omega) (by omega)
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, hR.congr fun x hx => ?_, hL.congr fun x hx => ?_,
    fun i hi => ?_, hlr, fun j hj => ?_, fun a h1 h2 => ?_, fun x hx => ?_,
    by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
  · rw [n2 x (by omega), n1 x (by omega)]
  · rw [n2 x (by omega), n1 x (by omega)]
  · rw [show U + 44 * n + 9 * k + 14 + i = U + 10 * n + k + 3 + 34 * n + 8 * k + 11 + i by omega]
    exact LF i hi
  · rw [show U + 11 * n + k + 4 + j = U + 10 * n + k + 3 + n + 1 + j by omega]
    exact HT j hj
  · rw [m2 a (by omega) h2, m1]
  · rw [n2 x (by omega), n1 x (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
