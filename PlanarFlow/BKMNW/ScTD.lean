module

public import PlanarFlow.BKMNW.MbDSpec
public import PlanarFlow.BKMNW.ScFrame

/-!
# The certificate program with the path decoded

`scProgT_execK` (`ScFrame.lean`) with Miller's base `mbBaseD` (`mbBase` plus the decoding `mbD`):

* **`scProg_exec_sepCKD`**, **`scProgT_execKD`**: in Miller's case (`r4900 = 0`) the path is given
  by its new hole and **by its darts** (`PathNHD`: `PD[j] = i + 1`, `e i = ρ.d j` at
  `Hb + 6n + j`, `j ≤ ρ.k < n`, then zeros); in the cut case (`r4900 = 2`) it is the point
  `tail (e r4902)` as before; cost `mbTD n Bz T₀ = mbT n Bz T₀ + 180 n + 50` in place of `mbT`;
* `wrOK_scProgTD`, `noEmit_scProgTD` (`decide +kernel`), **`scProgT_frameD`** (registers outside
  `scU`, reals, output kept).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv

/-- **`tfProg ; scProg mbBaseD` writes only registers in `scU` and no reals.** -/
theorem wrOK_scProgTD : Stmt.wrOK scU (.seq tfProg (scProg mbBaseD)) = true := by decide +kernel

/-- **`tfProg ; scProg mbBaseD` has no output instruction.** -/
theorem noEmit_scProgTD : Stmt.noEmit (.seq tfProg (scProg mbBaseD)) = true := by decide +kernel

/-- **The syntactic frame of `tfProg ; scProg mbBaseD`**: registers outside `scU`, reals,
output. -/
theorem scProgT_frameD {P : Input} {W : ℕ} {c c' : Config} {t : ℕ}
    (h : Exec P W (.seq tfProg (scProg mbBaseD)) c c' t) :
    (∀ x, scU x = false → c'.nreg x = c.nreg x) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  obtain ⟨h1, h2, h3⟩ := Exec.wr_frame h wrOK_scProgTD
  exact ⟨h1, h2, h3, Exec.output_eq h noEmit_scProgTD⟩

section Full

open Equiv Orbit

variable {P : Input} {W : ℕ}
variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

open Classical in
/-- **`scertD` under the choices `scChoiceE` with Miller's separator `sepC` (the one the machine
computes), as one program `scProg mbBaseD`, unconditionally.** From a piece map `PMap M N Hs τ`
(`N` nonempty, `Σ_N (1 + ex) ≤ T₀`) on a loopless map, the level input `LvIn` at `b`, the
rotation array of `τ` (stable on the enumerated darts `B`) at `SGb` below `b`, the base registers
`5200 … 5203 = SGb, Hb, Bz, SVb` (`encB' n ≤ Bz`), within
`(L + 1) (|Hs| (160 n + 36) + 244 n + 110) + mbTD n Bz T₀ + L (7 n + 40) + 22 n + 40` steps
(`mbTD n Bz T₀ = mbT n Bz T₀ + 180 n + 50`): either `r4970 = 0` and `scertD … = none`, or
`r4970 = 1`, `scertD … = some (ρ, I)` with the items `I` on the labels at `ITEMb`, and (Miller's
case, `r4900 = 0`) the flags of the new hole of `ρ` at `NHb` and its darts at `Hb + 6n`
(`PathNHD`), or (the cut, `r4900 = 2`) `ρ` the one vertex `tail (e r4902)`. -/
theorem scProg_exec_sepCKD (hloopM : ∀ d, M.head d ≠ M.tail d) {e : ℕ → D} {B N : Finset D}
    {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {τ : Perm D} {ex : D → ℕ}
    {n b A W₀ RECb IX0 L ITEMb NHb T₀ SGb Hb Bz SVb : ℕ} (c : Config)
    (hPN : PMap M N Hs τ) (hNne : N.Nonempty) (hT₀ : ∑ d ∈ N, (1 + ex d) ≤ T₀)
    (hc : WordsBounded W c) (hR : LvRegs c n b Hs.length A W₀)
    (hI : LvIn M c.nmem n b e B N Hs ex) (r36 : c.nreg 4936 = RECb) (r37 : c.nreg 4937 = IX0)
    (r55 : c.nreg 4955 = ITEMb) (r56 : c.nreg 4956 = NHb)
    (s0 : c.nreg 5200 = SGb) (s1 : c.nreg 5201 = Hb) (s2 : c.nreg 5202 = Bz)
    (s3 : c.nreg 5203 = SVb)
    (hSG : ∀ i < n, c.nmem (SGb + i) < n ∧ e (c.nmem (SGb + i)) = τ (e i)) (hτB : Stable τ B)
    (hBz : encB' n ≤ Bz) (hHW : Hs.length + 1 ≤ W)
    (hL : scDepth (scChoiceE M (sepC M e n Bz) e n Hs A W₀) Hs N τ ex ≤ L)
    (lay : b + 20 * n + 3 ≤ RECb ∧ RECb + 3 * L ≤ IX0 ∧ IX0 + L * n + n + 1 ≤ ITEMb ∧
      ITEMb + n ≤ NHb ∧ n + 2 + L ≤ W ∧ SGb + n ≤ b ∧ NHb + n ≤ Hb ∧
      Bz + 25 * n + 3 * T₀ + 15 ≤ Hb ∧ Hb + 13 * n ≤ SVb ∧ SVb + Bz + 25 * n + 3 * T₀ + 16 ≤ W)
    (hS : A + 2 * ((L + 1) * ∑ j ∈ range n, (1 + c.nmem (b + 3 * n + j))) ≤ W) :
    ∃ c' t, Exec P W (scProg mbBaseD) c c' t ∧
      t ≤ (L + 1) * (Hs.length * (160 * n + 36) + 244 * n + 110) + mbTD n Bz T₀ +
        L * (7 * n + 40) + 22 * n + 40 ∧ (∀ a < b, c'.nmem a = c.nmem a) ∧
      ((c'.nreg 4970 = 0 ∧ scertD (scChoiceE M (sepC M e n Bz) e n Hs A W₀) Hs N τ ex = none) ∨
       (c'.nreg 4970 = 1 ∧ ∃ ρ I,
         scertD (scChoiceE M (sepC M e n Bz) e n Hs A W₀) Hs N τ ex = some (ρ, I) ∧
         ItemRep e n I (fun i => c'.nmem (ITEMb + i)) ∧
         ((c'.nreg 4900 = 0 ∧ PathNHD M e n NHb Hb Hs c' ρ) ∨
          (c'.nreg 4900 = 2 ∧ c'.nreg 4902 < n ∧
            ρ = (SPath.point (M' := M) (e (c'.nreg 4902)) (M.tail (e (c'.nreg 4902)))).toH)))) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lay
  have hL1 : L * n + n + 1 ≤ ITEMb := by omega
  exact scProg_execK (P := P) (W := W) (sepC M e n Bz) hd mbBaseD (PathNHD M e n NHb Hb Hs) c
    (mbBaseD_spec (P := P) (W := W) hloopM hd e n Bz τ N B c.nmem c.nreg s0 s1 s2 s3 hSG hτB hBz
      ⟨l6, by omega, l4, l7, l8, l9, l10⟩)
    hPN hNne hT₀ (pathStable_NHD l4 l7) hc hR hI r36 r37 r55 r56 hHW hL
    ⟨l1, l2, l3, l4, by omega, l5⟩ hS


set_option maxHeartbeats 2000000 in
open Classical in
/-- **`scProgT_execK` with the path decoded** (Miller's base `mbBaseD`): the pre-filter
`tfProg` (scratch `[Zb, Zb + 3 |Hs| + n + 2)`, `Zb = r5830`), then `scProg mbBaseD` on the holes
touching `B` (at most `L` of them); the outcome is that of `scProg_exec_sepC` for the holes `Hs`,
with, in Miller's case, the darts of the path at `Hb + 6n` (`PathNHD`); memory below `b` kept. -/
theorem scProgT_execKD (hloopM : ∀ d, M.head d ≠ M.tail d) {e : ℕ → D} {B N : Finset D}
    {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {τ : Perm D} {ex : D → ℕ}
    {n b A W₀ RECb IX0 L ITEMb NHb T₀ SGb Hb Bz SVb Zb : ℕ} (c : Config)
    (hPN : PMap M N Hs τ) (hNne : N.Nonempty) (hT₀ : ∑ d ∈ N, (1 + ex d) ≤ T₀)
    (hc : WordsBounded W c) (hR : LvRegs c n b Hs.length A W₀)
    (hI : LvIn M c.nmem n b e B N Hs ex) (hTHle : ∀ i < n, c.nmem (b + n + i) ≤ Hs.length)
    (r36 : c.nreg 4936 = RECb) (r37 : c.nreg 4937 = IX0)
    (r55 : c.nreg 4955 = ITEMb) (r56 : c.nreg 4956 = NHb)
    (s0 : c.nreg 5200 = SGb) (s1 : c.nreg 5201 = Hb) (s2 : c.nreg 5202 = Bz)
    (s3 : c.nreg 5203 = SVb) (r30 : c.nreg 5830 = Zb)
    (hSG : ∀ i < n, c.nmem (SGb + i) < n ∧ e (c.nmem (SGb + i)) = τ (e i)) (hτB : Stable τ B)
    (hBz : encB' n ≤ Bz) (hHW : Hs.length + 1 ≤ W) (hL : (tHs M B Hs).length ≤ L)
    (lay : b + 20 * n + 3 ≤ RECb ∧ RECb + 3 * L ≤ IX0 ∧ IX0 + L * n + n + 1 ≤ ITEMb ∧
      ITEMb + n ≤ NHb ∧ n + 2 + L ≤ W ∧ SGb + n ≤ b ∧ NHb + n ≤ Hb ∧
      Bz + 25 * n + 3 * T₀ + 15 ≤ Hb ∧ Hb + 13 * n ≤ SVb ∧ SVb + Bz + 25 * n + 3 * T₀ + 16 ≤ W)
    (lZ : b + 7 * n ≤ Zb) (wZ : Zb + 3 * Hs.length + n + 2 ≤ W) (wk : n + Hs.length + 2 ≤ W)
    (hS : A + 2 * ((L + 1) * ∑ j ∈ range n, (1 + c.nmem (b + 3 * n + j))) ≤ W) :
    ∃ c' t, Exec P W (.seq tfProg (scProg mbBaseD)) c c' t ∧
      t ≤ 32 * n + 17 * Hs.length + 62 + ((L + 1) * (L * (160 * n + 36) + 244 * n + 110) +
        mbTD n Bz T₀ + L * (7 * n + 40) + 22 * n + 40) ∧ (∀ a < b, c'.nmem a = c.nmem a) ∧
      ((c'.nreg 4970 = 0 ∧ scertD (scChoiceE M (sepC M e n Bz) e n Hs A W₀) Hs N τ ex = none) ∨
       (c'.nreg 4970 = 1 ∧ ∃ ρ I,
         scertD (scChoiceE M (sepC M e n Bz) e n Hs A W₀) Hs N τ ex = some (ρ, I) ∧
         ItemRep e n I (fun i => c'.nmem (ITEMb + i)) ∧
         ((c'.nreg 4900 = 0 ∧ PathNHD M e n NHb Hb Hs c' ρ) ∨
          (c'.nreg 4900 = 2 ∧ c'.nreg 4902 < n ∧
            ρ = (SPath.point (M' := M) (e (c'.nreg 4902)) (M.tail (e (c'.nreg 4902)))).toH)))) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lay
  -- the pre-filter
  obtain ⟨c₁, t₁, e₁, ht₁, Fl, hFl, k1, TH1, M1, q1, rr1, rm1, o1⟩ := tfProg_exec (P := P) c hc
    hR.p0 hR.p2 hR.v4 r30 hTHle (by omega) wZ wk
  obtain ⟨hlen, hth⟩ := tf_th (M := M) (B := B) (Hs := Hs) hI.mem hI.surj hTHle
    (fun i hi j hj => hI.th i hi j hj) (fun j hj => hFl j)
  have hk1 : c₁.nreg 4874 = (tHs M B Hs).length := by rw [k1, hlen]
  have hR₁ : LvRegs c₁ n b (tHs M B Hs).length A W₀ := hR.tf q1 hk1
  have he : ∀ a, ¬ (b + n ≤ a ∧ a < b + 2 * n) → b ≤ a → a < b + 7 * n →
      c₁.nmem a = c.nmem a := fun a h1 h2 h3 => M1 a (by omega) (by omega)
  have hI₁ : LvIn M c₁.nmem n b e B N (tHs M B Hs) ex := hI.tHs he fun i hi j => by
    rw [TH1 i hi]; exact hth i hi j
  have hSG₁ : ∀ i < n, c₁.nmem (SGb + i) < n ∧ e (c₁.nmem (SGb + i)) = τ (e i) := fun i hi => by
    rw [M1 _ (by omega) (by omega)]; exact hSG i hi
  have hS₁ : A + 2 * ((L + 1) * ∑ j ∈ range n, (1 + c₁.nmem (b + 3 * n + j))) ≤ W := by
    rw [sum_congr rfl fun j hj => by rw [M1 _ (by have := mem_range.1 hj; omega)
      (by have := mem_range.1 hj; omega)]]
    exact hS
  have hd' := tHs_pairwise (M := M) (B := B) hd
  have hPN' : PMap M N (tHs M B Hs) τ := hPN.tHs hI.sub
  have hdep := scDepth_tHs_le (sepC M e n Bz) e n A W₀ hI.sub hd ex hPN.rev hPN.conn (τ := τ)
  obtain ⟨c₂, t₂, e₂, ht₂, Mk, hout⟩ := scProg_exec_sepCKD (P := P) (W := W) hloopM hd' c₁ hPN' hNne
    hT₀ e₁.wb_right hR₁ hI₁ (by rw [q1 _ (by unfold tfW; omega)]; exact r36)
    (by rw [q1 _ (by unfold tfW; omega)]; exact r37) (by rw [q1 _ (by unfold tfW; omega)]; exact r55)
    (by rw [q1 _ (by unfold tfW; omega)]; exact r56) (by rw [q1 _ (by unfold tfW; omega)]; exact s0)
    (by rw [q1 _ (by unfold tfW; omega)]; exact s1) (by rw [q1 _ (by unfold tfW; omega)]; exact s2)
    (by rw [q1 _ (by unfold tfW; omega)]; exact s3) hSG₁ hτB hBz
    (by have := length_tHs_le (M := M) B Hs; omega) (hdep.trans hL)
    ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ hS₁
  have heq := scertD_tHs (M := M) (sepC M e n Bz) e n A W₀ (B := B) hd _ N τ ex rfl hI.sub
    hPN.conn
  have hc2 : (tHs M B Hs).length * (160 * n + 36) ≤ L * (160 * n + 36) :=
    Nat.mul_le_mul_right _ hL
  have hc3 : (L + 1) * ((tHs M B Hs).length * (160 * n + 36) + 244 * n + 110) ≤
      (L + 1) * (L * (160 * n + 36) + 244 * n + 110) := Nat.mul_le_mul_left _ (by omega)
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega,
    fun a ha => by rw [Mk a ha, M1 a (by omega) (by omega)], ?_⟩
  rw [heq]
  rcases hout with ⟨h0, h1⟩ | ⟨h0, ρ, I, h1, h2, h3⟩
  · exact Or.inl ⟨h0, h1⟩
  · refine Or.inr ⟨h0, ρ, I, h1, h2, ?_⟩
    rcases h3 with ⟨h4, h5⟩ | h4
    · refine Or.inl ⟨h4, fun i hi => ?_, h5.2⟩
      rw [h5.1 i hi]
      exact (newHole_tHs (hI.mem i hi) ρ.mverts).symm
    · exact Or.inr h4

end Full

end BKMNW

end PlanarFlow
