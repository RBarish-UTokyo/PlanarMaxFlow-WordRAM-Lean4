module

public import PlanarFlow.BKMNW.NcHdA
public import PlanarFlow.BKMNW.NcRbM
public import PlanarFlow.BKMNW.NcScanM

/-!
# The head of `c2sP`, stages C and D: the residual reachability, the capacities, the excesses

* `rb_adj_congr` (the dart graph depends on the rotation and reverse arrays only below `m`);
* **`hdMK_exec`**: `rbGl ; rbP` writes at `b + 14 m + 5` the marks `MK` with
  `MK[i] = 1 ∧ tail ∈ C ↔ tail ∈ fwdReach U g (posSet g C) C` (`C⁺` of `c2sBeta`, `delSet`);
* stage D in `NcHdC.lean`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap MfDrv NsStep StCall OrbLab Relation NegSSSP WordRAM
  WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

universe w

/-- **The dart graph depends on the rotation and reverse arrays only below `m`.** -/
lemma rb_adj_congr {m : ℕ} {res sg rv src sg' rv' : ℕ → ℕ} (hres : ∀ i < m, res i ≤ 1)
    (hsg : ∀ i < m, sg i = sg' i) (hrv : ∀ i < m, rv i = rv' i) :
    BfsAdj (rbOb m) (rbOe m res) id (rbHd m sg rv src) =
      BfsAdj (rbOb m) (rbOe m res) id (rbHd m sg' rv' src) := by
  funext u v
  apply propext
  rw [rb_adj_iff hres, rb_adj_iff hres]
  constructor
  · rintro (⟨hu, h⟩ | h)
    · left; rw [← hsg u hu, ← hrv u hu]; exact ⟨hu, h⟩
    · right; exact h
  · rintro (⟨hu, h⟩ | h)
    · left; rw [hsg u hu, hrv u hu]; exact ⟨hu, h⟩
    · right; exact h

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Stage C, the run**: `rbGl ; rbP` at the head's addresses. -/
theorem hdMK0_exec {m d b CPb Z : ℕ} (c : Config) (hc : WordsBounded W c)
    (r32 : c.nreg 9832 = m) (r40 : c.nreg 9840 = b + 6 * m + 1) (r76 : c.nreg 9876 = d + 4 + 6 * m)
    (r30 : c.nreg 9830 = CPb) (r33 : c.nreg 9833 = Z) (r39 : c.nreg 9839 = b + 5 * m + 1)
    (r35 : c.nreg 9835 = b + m) (r36 : c.nreg 9836 = b + 2 * m) (r37 : c.nreg 9837 = b + 3 * m)
    (r75 : c.nreg 9875 = d + 4 + 2 * m) (r74 : c.nreg 9874 = d + 4 + m)
    (hb : d + 4 + 7 * m ≤ b) (hCPl : CPb + m ≤ b + 6 * m + 1)
    (w : b + 6 * m + 1 + 4 * (m + 2) + 6 * m + 1 ≤ W)
    (hlab : ∀ i < m, 1 ≤ c.nmem (b + m + i) ∧ c.nmem (b + m + i) ≤ m)
    (hcf : ∀ i < m, c.nmem (b + 5 * m + 1 + i) ≤ 1)
    (hsg : ∀ i < m, c.nmem (d + 4 + 2 * m + i) < m) (hrv : ∀ i < m, c.nmem (d + 4 + m + i) < m)
    (wcp : ∀ i < m, c.nmem (CPb + i) + Z ≤ W)
    (wdg : ∀ v < m, c.nmem (b + 3 * m + v) * Z ≤ W) :
    ∃ c' k, Exec P W (.seq rbGl rbP) c c' k ∧ k ≤ 22 + rbCost m ∧
      (∀ u < m, c'.nmem (b + 14 * m + 5 + u) =
        @ite ℕ (ReflTransGen (BfsAdj (rbOb m) (rbOe m (rbRes c.nmem (d + 4 + 6 * m) CPb Z)) id
          (rbHd m (fun i => c.nmem (d + 4 + 2 * m + i)) (fun i => c.nmem (d + 4 + m + i))
            (rbSrc c.nmem Z (b + 5 * m + 1) (b + m) (b + 2 * m) (b + 3 * m)))) m u)
          (Classical.propDecidable _) 1 0) ∧
      (∀ a, (a < b + 6 * m + 1 ∨ b + 6 * m + 1 + 4 * (m + 2) + 6 * m ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ RbGo r → r ≠ 9860 → r ≠ 9879 → (r < 1400 ∨ (1419 < r ∧ r < 9620) ∨ 9646 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have iFL : d + 4 + 6 * m + m ≤ b + 6 * m + 1 := by omega
  have iCF : b + 5 * m + 1 + m ≤ b + 6 * m + 1 := by omega
  have iLAB : b + m + m ≤ b + 6 * m + 1 := by omega
  have iDV : b + 2 * m + m ≤ b + 6 * m + 1 := by omega
  have iDG : b + 3 * m + m ≤ b + 6 * m + 1 := by omega
  have iSG : d + 4 + 2 * m + m ≤ b + 6 * m + 1 := by omega
  have iRV : d + 4 + m + m ≤ b + 6 * m + 1 := by omega
  have w' : b + 6 * m + 1 + 3 * (m + 2) + 6 * m ≤ W := by omega
  obtain ⟨c₁, k₁, e₁, hk₁, a00, a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11, a12, a13,
    a14, a15, f₁, m₁, rr₁, rm₁, o₁⟩ := rbGl_exec (P := P) c hc r32 r40 w'
  rw [r76] at a01; rw [r30] at a02; rw [r33] at a03; rw [r39] at a04; rw [r35] at a05
  rw [r36] at a06; rw [r37] at a07; rw [r75] at a08; rw [r74] at a09
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂, g₂, rr₂, rm₂, o₂⟩ := rbP_exec (P := P) c₁ e₁.wb_right
    (m := m) (FLb := d + 4 + 6 * m) (CPb := CPb) (Z := Z) (CFb := b + 5 * m + 1) (LABb := b + m)
    (DVb := b + 2 * m) (DGb := b + 3 * m) (SGb := d + 4 + 2 * m) (RVb := d + 4 + m)
    (S := b + 6 * m + 1)
    a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15
    iFL hCPl iCF iLAB iDV iDG iSG iRV w (by rw [m₁]; exact hlab) (by rw [m₁]; exact hcf)
    (by rw [m₁]; exact hsg) (by rw [m₁]; exact hrv) (by rw [m₁]; exact wcp)
    (by rw [m₁]; exact wdg)
  refine ⟨c₂, k₁ + k₂, e₁.seq e₂, by omega, fun i hi => ?_, fun a ha => ?_,
    fun r h1 h2 h3 h4 => ?_, by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
  · have hv := v₂ i (by omega)
    rw [show b + 6 * m + 1 + 2 * (m + 2) + 6 * m + i = b + 14 * m + 5 + i by omega, m₁] at hv
    exact hv
  · rw [f₂ a ha, m₁]
  · rw [g₂ r h4, f₁ r h1 h2 h3]

set_option maxHeartbeats 1000000 in
/-- **Stage C, the meaning**: the marks of `hdMK0_exec` are those of `C⁺ = fwdReach U g
(posSet g C) C` (with the tail in `C`). -/
theorem hdMK_sem {x : MCall M} (hP : PieceInv M x.1.piece x.2.1 x.2.2) {m : ℕ} {en : ℕ → D}
    {d b : ℕ} {mem : ℕ → ℕ} (hL : Lay M gid u S T Z x m en d mem)
    (hm : 0 < m) (hrot : (pmap hP).RotTrans)
    {U g : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    {C : Finset (SVert x.2.2 (pdarts M x.1.piece x.2.1))} {CPb : ℕ}
    (hFL : ∀ i < m, (mem (d + 4 + 6 * m + i) : ℤ) =
      Z + g (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i))
    (hCP : ∀ i < m, (mem (CPb + i) : ℤ) = U (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i))
    (hCF : ∀ i < m, mem (b + 5 * m + 1 + i) =
      flagX (pmap hP) (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm) C i)
    (hl1 : ∀ i < m, 1 ≤ mem (b + m + i))
    (hDV : ∀ i < m, (mem (b + 2 * m + (mem (b + m + i) - 1)) : ℤ) -
          Z * mem (b + 3 * m + (mem (b + m + i) - 1)) =
        (pmap hP).div g ((pmap hP).tail (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i)))
    {mk : ℕ → ℕ}
    (hv : ∀ i < m, mk i =
        @ite ℕ (ReflTransGen (BfsAdj (rbOb m) (rbOe m (rbRes mem (d + 4 + 6 * m) CPb Z)) id
          (rbHd m (fun i => mem (d + 4 + 2 * m + i)) (fun i => mem (d + 4 + m + i))
            (rbSrc mem Z (b + 5 * m + 1) (b + m) (b + 2 * m) (b + 3 * m)))) m i)
          (Classical.propDecidable _) 1 0) :
    ∀ i < m, mk i ≤ 1 ∧
      (mk i = 1 ∧ (pmap hP).tail (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i) ∈ C ↔
        (pmap hP).tail (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i) ∈
          fwdReach (pmap hP) U g (posSet (pmap hP) g C) C) := by
  classical
  have hft := pmap_faceTrans hP
  have hE := lay_enumOK hP hL hm hft
  set en' := layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm with hen'
  have hres : ∀ i < m, rbRes mem (d + 4 + 6 * m) CPb Z i =
      if g (en' i) < U (en' i) then 1 else 0 := fun i hi =>
    rbRes_eq (hFL i hi) (hCP i hi)
  have hres1 : ∀ i < m, rbRes mem (d + 4 + 6 * m) CPb Z i ≤ 1 := fun i hi => by
    rw [hres i hi]; split_ifs <;> omega
  have hsrc : ∀ i < m, rbSrc mem Z (b + 5 * m + 1) (b + m) (b + 2 * m) (b + 3 * m) i =
      if (pmap hP).tail (en' i) ∈ posSet (pmap hP) g C then 1 else 0 := fun i hi => by
    have hl := hl1 i hi
    exact rbSrc_eq (hCF i hi) (show mem (b + m + i) = (mem (b + m + i) - 1) + 1 by omega)
      (hDV i hi)
  have hadj := rb_adj_congr (src := rbSrc mem Z (b + 5 * m + 1) (b + m) (b + 2 * m) (b + 3 * m))
    hres1 (sg := fun i => mem (d + 4 + 2 * m + i)) (sg' := sgI (pmap hP) en' m)
    (rv := fun i => mem (d + 4 + m + i)) (rv' := rvI (pmap hP) en' m)
    (fun i hi => lay_rt hP hL hm hft hi) (fun i hi => lay_rv hP hL hm hft hi)
  intro i hi
  have key := rb_fwdReach hE hrot (pmap_tail_surj hP) hres hsrc hi
  rw [hv i hi]
  simp only [hadj]
  constructor
  · split_ifs <;> omega
  · constructor
    · rintro ⟨h1, h2⟩
      by_cases hn : ReflTransGen (BfsAdj (rbOb m) (rbOe m (rbRes mem (d + 4 + 6 * m) CPb Z)) id
          (rbHd m (sgI (pmap hP) en' m) (rvI (pmap hP) en' m)
            (rbSrc mem Z (b + 5 * m + 1) (b + m) (b + 2 * m) (b + 3 * m)))) m i
      · exact key.1 ⟨hn, h2⟩
      · rw [iteF hn] at h1; omega
    · intro h
      obtain ⟨h1, h2⟩ := key.2 h
      exact ⟨by rw [iteT h1], h2⟩

end NcStep

end BKMNW

end PlanarFlow
