module

public import PlanarFlow.BKMNW.SmXE

/-!
# The small separator program meets the outputs of `SepPSpecX` at a node of `smD`

**`sepSm_exec`** (see `SmXE.lean`): `sepSm = smXA ; smXB1 ; smXB2` at a node call of the small
decomposition, within `560 n + 27 m + 50 k + 520` steps and the room `smR n m k`.
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

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {ds : DSys M}

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 8000000 in
/-- **The small separator program at a node of `smD`** (see the module docstring). -/
theorem sepSm_exec {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    {m n d R Sb : ℕ} {en g : ℕ → D} (c : Config) (hc : WordsBounded W c)
    (hok : CallOk M S T ((.node l r π, Hs, σ) : MCall M))
    (hL : Lay M gid u S T Z ((.node l r π, Hs, σ) : MCall M) m en d c.nmem)
    (hpR : c.nmem (d + fsz m) = R) (o2 : d + fsz m < R)
    (hA : RArr M gid ν S T ((.node l r π, Hs, σ) : MCall M) m n R g c.nmem) (hn : c.nmem R = n)
    (hsm : smD M ds.pk S T (l.piece ∪ r.piece) Hs = .node l r π)
    (hpk : PkMin gid ds.pk) (hν : Injective ν) (hloop : ∀ y, M.head y ≠ M.tail y)
    (r4 : c.nreg 3004 = d) (r50 : c.nreg 6500 = Sb) (o1 : R + 3 + 6 * n + m ≤ Sb)
    (w : Sb + smR n m Hs.length ≤ W) (hW : 21 ≤ W) :
    ∃ c' t, Exec I W sepSm c c' t ∧ t ≤ 560 * n + 27 * m + 50 * Hs.length + 520 ∧
      DRegKeep c c' ∧ (∀ a < Sb, c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      c'.output = c.output ∧
      (∀ i < m, c'.nmem (Sb + i) = bf (en i ∈ l.piece)) ∧
      (∀ i < m, c'.nmem (Sb + m + i) = bf (en i ∈ π.path.darts.toFinset)) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = bf (M.tail (en i) ∈ π.path.mverts)) ∧
      (∀ j < Hs.length, c'.nmem (Sb + 3 * m + j) =
        bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
      c'.nmem (Sb + 3 * m + Hs.length) = ntag l ∧ c'.nmem (Sb + 3 * m + Hs.length + 1) = ntag r ∧
      RecsOut M ds gid ν S T l r π Hs σ (Sb + 21 * m + 4 * Hs.length + 2)
        (Sb + smR n m Hs.length) (c'.nreg 6501) c'.nmem := by
  have hR : smR n m Hs.length = 22 * m + 24 * n + 8 * Hs.length + 30 := rfl
  have hrc : RevClosed M (l.piece ∪ r.piece) := hok.pieceInv.rev
  have hpw : Hs.Pairwise Disjoint := hok.2.2.2.2.2.2
  obtain ⟨-, ⟨gl, -, -⟩, -⟩ := id hok
  have hlrev : ∀ y ∈ l.piece, M.rev y ∈ l.piece := gl.revClosed
  obtain ⟨⟨-, -, -⟩, ⟨-, -, -, -, hC, -⟩, -, -, hSA, hTA, -⟩ := id hok
  have hSC : Disjoint S π.path.mverts := (disjoint_of_subset_right subset_union_left hC).symm
  have hTC : Disjoint T π.path.mverts := (disjoint_of_subset_right subset_union_right hC).symm
  obtain ⟨hlsm, Q, hrl⟩ := smD_children (fun X hX => (hpk X hX).1) hloop hrc hsm
  -- stage A
  obtain ⟨c₁, t₁, e₁, ht₁, hR1, o21, s1, s2, s3, s4, s5, s6, LPv, CVv, HMv, K1, K1', dk1, rr1,
    rm1, oo1⟩ := smXA_exec (I := I) c hc hpw hrc hL hpR hA hn hsm hpk hν hloop r4 r50 o1 o2
      (by clear * - w hR; omega) hW
  have hA1 : RArr M gid ν S T ((.node l r π, Hs, σ) : MCall M) m n R g c₁.nmem :=
    hA.congr fun a _ h2 => K1 a (by clear * - h2 o1; omega)
  obtain ⟨HCv, KCv, CFv⟩ := smSem_vals (x := ((.node l r π, Hs, σ) : MCall M))
    (A := Sb + 21 * m + 4 * Hs.length + 2) (L := l.piece) hA1 hpw hSC hTC hSA LPv CVv HMv
  -- stage B, first part
  obtain ⟨c₂, t₂, e₂, ht₂, hR2, r21', r33, r34, fKC, fHC, v40, fCI, v41, fIX2, K2, dk2, rr2, rm2,
    oo2⟩ := smXB1_exec (I := I) c₁ e₁.wb_right hR1 o21 (fun i hi => (hA1.rp i hi).1)
      (fun i hi => by rw [hA1.hp i hi]; exact hlab_le _ _) o1 (by clear * - w hR; omega) hW
  -- the flags in the record's order
  have LPc : ∀ i ≤ n, cnt (fun j => c₁.nmem (Sb + 21 * m + 4 * Hs.length + 2 + n + j)) i =
      cnt (fun j => bf (g j ∈ l.piece)) i := fun i hi =>
    cnt_congr fun j hj => LPv j (by clear * - hi hj; omega)
  have CFc : ∀ i ≤ n, cnt (fun j => smCF c₁.nmem (Sb + 21 * m + 4 * Hs.length + 2) R n
      Hs.length j) i =
      cnt (fun j => bf (g j ∈ pdarts M l.piece (childHoles Hs π.path.mverts))) i := fun i hi =>
    cnt_congr fun j hj => CFv j (by clear * - hi hj; omega)
  have hnl := cnt_le (fun j => bf (g j ∈ l.piece)) n
  have hml := cnt_le (fun j => bf (g j ∈ pdarts M l.piece (childHoles Hs π.path.mverts))) n
  have K21 : ∀ a, a < Sb + 21 * m + 4 * Hs.length + 2 + 4 * n + Hs.length + 2 →
      c₂.nmem a = c₁.nmem a := K2
  have LP2 : ∀ i < n, c₂.nmem (Sb + 21 * m + 4 * Hs.length + 2 + n + i) =
      bf (g i ∈ l.piece) := fun i hi => by rw [K21 _ (by clear * - hi; omega)]; exact LPv i hi
  have RP2 : ∀ i < n, c₂.nmem (R + 3 + n + i) = c₁.nmem (R + 3 + n + i) := fun i hi =>
    K21 _ (by clear * - hi o1; omega)
  -- the compactions
  have CI1 : ∀ i < n, g i ∈ l.piece →
      c₂.nmem (Sb + 21 * m + 4 * Hs.length + 2 + 11 * n + 4 * Hs.length + 2 + i) =
        cnt (fun j => bf (g j ∈ l.piece)) i ∧
      c₂.nmem (Sb + 21 * m + 4 * Hs.length + 2 + 12 * n + 4 * Hs.length + 2 +
        cnt (fun j => bf (g j ∈ l.piece)) i) = i := fun i hi hx => by
    have hf : 0 < c₁.nmem (Sb + 21 * m + 4 * Hs.length + 2 + n + i) := by
      rw [LPv i hi]; exact (bf_pos).2 hx
    obtain ⟨a1, a2⟩ := fCI i hi hf
    rw [LPc i (by clear * - hi; omega)] at a1 a2
    exact ⟨a1, a2⟩
  have IX2 : ∀ i < n, g i ∈ pdarts M l.piece (childHoles Hs π.path.mverts) →
      c₂.nmem (Sb + 21 * m + 4 * Hs.length + 2 + 15 * n + 4 * Hs.length + 2 +
        cnt (fun j => bf (g j ∈ pdarts M l.piece (childHoles Hs π.path.mverts))) i) = i :=
    fun i hi hx => by
      have hf : 0 < smCF c₁.nmem (Sb + 21 * m + 4 * Hs.length + 2) R n Hs.length i := by
        rw [CFv i hi]; exact (bf_pos).2 hx
      have a2 := fIX2 i hi hf
      rw [CFc i (by clear * - hi; omega)] at a2
      exact a2
  rw [LPc n le_rfl] at v40
  rw [CFc n le_rfl] at v41
  have hix : ∀ j < cnt (fun j => bf (g j ∈ l.piece)) n,
      c₂.nmem (Sb + 21 * m + 4 * Hs.length + 2 + 12 * n + 4 * Hs.length + 2 + j) < n :=
    fun j hj => by
      obtain ⟨i, hi, hfi, rfl⟩ := cnt_surj _ n j hj
      rw [(CI1 i hi ((bf_pos).1 hfi)).2]; exact hi
  have hix2 : ∀ j < cnt (fun j => bf (g j ∈ pdarts M l.piece (childHoles Hs π.path.mverts))) n,
      c₂.nmem (Sb + 21 * m + 4 * Hs.length + 2 + 15 * n + 4 * Hs.length + 2 + j) < n :=
    fun j hj => by
      obtain ⟨i, hi, hfi, rfl⟩ := cnt_surj _ n j hj
      rw [IX2 i hi ((bf_pos).1 hfi)]; exact hi
  -- stage B, second part
  obtain ⟨c₃, t₃, e₃, ht₃, x01, m0, m1, m2, m3, m4, m5, m6, m7, h_gp, h_rp, h_hp, h_kp, h_vp,
    h_fx, K3, dk3, rr3, rm3, oo3⟩ := smXB2_exec (I := I) c₂ e₂.wb_right hR2 v40 v41 r33 r34 hnl
    hml hix hix2
    (fun i hi hf => by rw [RP2 i hi]; exact (hA1.rp i hi).1)
    (fun i hi hf => by
      rw [LP2 i hi] at hf
      rw [(CI1 i hi ((bf_pos).1 hf)).1]; exact cnt_lt_of _ hi hf)
    (fun i hi j hj hfi hfj e => by
      rw [LP2 i hi] at hfi; rw [LP2 j hj] at hfj
      rw [(CI1 i hi ((bf_pos).1 hfi)).1, (CI1 j hj ((bf_pos).1 hfj)).1] at e
      rcases lt_trichotomy i j with h | h | h
      · have := cnt_lt_of (fun j => bf (g j ∈ l.piece)) h hfi; omega
      · exact h
      · have := cnt_lt_of (fun j => bf (g j ∈ l.piece)) h hfj; omega)
    o1 (by clear * - w hR; omega) hW
  have K31 : ∀ a, a < Sb + 21 * m + 4 * Hs.length + 2 + 4 * n + Hs.length + 2 →
      c₃.nmem a = c₁.nmem a := fun a ha => by
    rw [K3 a (by clear * - ha; omega), K21 a ha]
  -- the records
  have hRO : RecsOut M ds gid ν S T l r π Hs σ (Sb + 21 * m + 4 * Hs.length + 2)
      (Sb + smR n m Hs.length) (Sb + 21 * m + 4 * Hs.length + 2 + 16 * n + 4 * Hs.length + 2)
      c₃.nmem := by
    refine recsOut_sm (g := g) (n := n) (fun i hi j hj e => hA1.g_inj hi hj e) hA1.g_surj
      hA1.g_mono hlrev hlsm hrl
      (CI := fun i => c₂.nmem (Sb + 21 * m + 4 * Hs.length + 2 + 11 * n + 4 * Hs.length + 2 + i))
      (IX := fun j => c₂.nmem (Sb + 21 * m + 4 * Hs.length + 2 + 12 * n + 4 * Hs.length + 2 + j))
      (IX2 := fun j => c₂.nmem (Sb + 21 * m + 4 * Hs.length + 2 + 15 * n + 4 * Hs.length + 2 + j))
      (RPf := fun i => c₁.nmem (R + 3 + n + i)) CI1 IX2 hA1.rp (by clear * -; omega)
      (by rw [hR]; clear * - hnl hml; omega) m0 m1 m2 m3 m4 (by rw [m0]; exact m5)
      (by rw [m0]; exact m6) (by rw [m0]; exact m7) (fun j hj => ?_) (fun i hi hx => ?_)
      (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_) h_fx
    · have hx := hix j hj
      rw [h_gp j hj, K21 _ (by clear * - hx o1; omega)]; exact hA1.gp _ hx
    · have hf : 0 < c₂.nmem (Sb + 21 * m + 4 * Hs.length + 2 + n + i) := by
        rw [LP2 i hi]; exact (bf_pos).2 hx
      rw [h_rp i hi hf, RP2 i hi]
    · have hx := hix j hj
      rw [h_hp j hj, fHC _ hx]; exact HCv _ hx
    · have hx := hix j hj
      rw [h_kp j hj, fKC _ hx]; exact KCv _ hx
    · have hx := hix j hj
      rw [h_vp j hj, K21 _ (by clear * - hx o1; omega)]; exact hA1.vp _ hx
  have ht : t₁ + (t₂ + t₃) ≤ 560 * n + 27 * m + 50 * Hs.length + 520 := by
    clear * - ht₁ ht₂ ht₃; omega
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), ht, fun x h1 h2 => ?_, fun a ha => ?_,
    by rw [oo3, oo2, oo1], fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, ?_, ?_,
    by rw [x01]; exact hRO⟩
  · rw [dk3 x (by clear * - h2; omega), dk2 x (by clear * - h2; omega)]; exact dk1 x h1 h2
  · refine ⟨by rw [K31 a (by clear * - ha; omega)]; exact K1 a ha, by rw [rm3, rm2, rm1]⟩
  · rw [K31 _ (by clear * - hi; omega)]; exact s1 i hi
  · rw [K31 _ (by clear * - hi; omega)]; exact s2 i hi
  · rw [K31 _ (by clear * - hi; omega)]; exact s3 i hi
  · rw [K31 _ (by clear * - hj; omega)]; exact s4 j hj
  · rw [K31 _ (by clear * -; omega)]; exact s5
  · rw [K31 _ (by clear * -; omega)]; exact s6

end Exec

end MfDrv

end BKMNW

end PlanarFlow
