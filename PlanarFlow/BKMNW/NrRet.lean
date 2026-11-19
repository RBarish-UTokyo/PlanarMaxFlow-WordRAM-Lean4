module

public import PlanarFlow.BKMNW.NrFr

/-!
# The push-back steps `frmP` and `retP` at a call

* `negS = fN1 ; fN2 ; negL` (`FL := 2Z - FL`), **`negS_exec`** (the flow array of `g` becomes
  that of `-g`, `|g| ≤ Z`);
* **`frmP = fFrm ; fcore`** (`kfr = 2`: the free vertices are the sinks `vimg T`),
  **`frmP_exec`**: the flow array becomes
  `Z + frmG (pmap h) (pchCall gid x h) g (vimg T) (negSet g (vimg segs[j].verts))`;
* **`retP = fRet ; negS ; fcore ; negS`** (`kfr = 0`: the free vertices are the sources
  `vimg S`, on the reversed flow), **`retP_exec`**: the flow array becomes
  `Z + retG (pmap h) (pchCall gid x h) g (posSet g (vimg segs[j].verts)) (vimg S)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv Orbit

/-- `FL := 2Z - FL`. -/
def negS : Stmt := .seq fN1 (.seq fN2 negL)

/-- **The push-back from the sinks.** -/
def frmP : Stmt := .seq fFrm fcore

/-- **The push-back of the excess to the sources.** -/
def retP : Stmt := .seq fRet (.seq negS (.seq fcore negS))

theorem frmP_natOnly : Klein.natOnly frmP = true := by kernel_rfl

theorem retP_natOnly : Klein.natOnly retP = true := by kernel_rfl

theorem negS_dests : (Stmt.nDests negS).all
    (fun x => decide (x < 3000 ∨ (3012 < x ∧ x < 6800) ∨ 6819 < x)) = true := by decide +kernel

theorem frmP_dests : (Stmt.nDests frmP).all
    (fun x => decide (x < 3000 ∨ (3012 < x ∧ x < 6800) ∨ 6819 < x)) = true := by decide +kernel

theorem retP_dests : (Stmt.nDests retP).all
    (fun x => decide (x < 3000 ∨ (3012 < x ∧ x < 6800) ∨ 6819 < x)) = true := by decide +kernel

/-- The steps of `frmP` and `retP`. -/
def frmCost (m n : ℕ) : ℕ := fcCost m n + 1

def retCost (m n : ℕ) : ℕ := fcCost m n + 14 * m + 60

namespace MfDrv

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

variable {P : Input} {W : ℕ}

/-- **The negation of the flow array** `FL := 2Z - FL`. -/
theorem negS_exec {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} (c : Config)
    (hc : WordsBounded W c) (hL : Lay M gid u S T Z x m en d c.nmem)
    {g : SDart (pdarts M x.1.piece x.2.1) → ℤ} (hZ : ∀ e, -(Z : ℤ) ≤ g e ∧ g e ≤ Z)
    (hfl : FLHas Z m d en c.nmem g) (r3004 : c.nreg 3004 = d) (w : d + 7 * m + 10 ≤ W)
    (wZ : 2 * Z ≤ W) :
    ∃ c' t, Exec P W negS c c' t ∧ t ≤ 7 * m + 17 ∧ FLHas Z m d en c'.nmem (-g) ∧
      (∀ a, (a < d + 4 + 6 * m ∨ d + 4 + 7 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) → c'.nreg r = c.nreg r) ∧
      (∀ r, 9180 ≤ r → r ≤ 9191 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hm := hL.hm
  have hz := hL.hz
  obtain ⟨c₁, t₁, e₁, ht₁, a99, a81, a82, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    fN1_exec (P := P) c hc (by rw [r3004]; clear * - w wZ; omega) (by clear * - w wZ; omega)
      (by rw [r3004]; clear * - w wZ; omega) (by rw [r3004, hm]; clear * - w wZ; omega)
      (by rw [r3004, hm]; clear * - w wZ; omega) (by rw [r3004, hm]; clear * - w wZ; omega)
      (by rw [r3004, hm]; clear * - w wZ; omega) (by rw [r3004, hm]; clear * - w wZ; omega)
      (by rw [r3004, hm]; clear * - w wZ; omega)
  simp only [r3004, hm] at a81 a82
  obtain ⟨c₂, t₂, e₂, ht₂, b98, b99, b83, f₂, m₂, rr₂, rm₂, o₂⟩ :=
    fN2_exec (P := P) c₁ e₁.wb_right (by clear * - w wZ; omega)
      (by rw [f₁ _ (by decide) (by decide) (by decide), r3004]; clear * - w wZ; omega)
      (by rw [f₁ _ (by decide) (by decide) (by decide), r3004]; clear * - w wZ; omega)
      (by rw [f₁ _ (by decide) (by decide) (by decide), r3004, m₁, hz]; clear * - w wZ; omega)
  rw [f₁ _ (by decide) (by decide) (by decide), r3004, m₁, hz] at b83
  obtain ⟨c₃, t₃, e₃, ht₃, v₃, k₃, f₃, rr₃, rm₃, o₃⟩ := negL_exec (P := P) c₂ e₂.wb_right
    (n := m) (FLb := d + 4 + m + m + m + m + m + m) (tw := Z + Z)
    (by rw [f₂ _ (by decide) (by decide) (by decide)]; exact a81)
    (by rw [f₂ _ (by decide) (by decide) (by decide)]; exact a82) b83
    (by clear * - w wZ; omega) (by clear * - w wZ; omega)
  have ex : Exec P W negS c c₃ (t₁ + (t₂ + t₃)) := .seq e₁ (.seq e₂ e₃)
  refine ⟨c₃, _, ex, by clear * - ht₁ ht₂ ht₃; omega, fun i hi => ?_, fun a ha => ?_,
    sreg_keepW ex negS_dests, fun r h1 h2 => ?_, by rw [rr₃, rr₂, rr₁], by rw [rm₃, rm₂, rm₁],
    by rw [o₃, o₂, o₁]⟩
  · rw [show d + 4 + 6 * m + i = d + 4 + m + m + m + m + m + m + i by clear * -; omega, v₃ i hi,
      m₂, m₁, show d + 4 + m + m + m + m + m + m + i = d + 4 + 6 * m + i by clear * -; omega]
    have h1 := hfl i hi
    have h2 := hZ ⟨en i, hL.en_mem i hi⟩
    rw [fext_mem g (hL.en_mem i hi)] at h1
    rw [fext_mem (-g) (hL.en_mem i hi)]
    simp only [Pi.neg_apply]
    omega
  · rw [k₃ a (by clear * - ha; omega), m₂, m₁]
  · exact Exec.nreg_keepW ex (nWrites_eq_false_of _ (by
      simp only [negS, Stmt.nDests, fN1, fN2, negL, negB, block, Instr.nDest, Option.toList,
        List.nil_append, List.cons_append, List.mem_cons, List.mem_nil_iff, or_false]
      clear * - h1 h2; omega))

/-- `lrk` of a terminal off the holes. -/
lemma lrk_T_iff {S T A : Finset V} (hST : Disjoint S T) (hTA : Disjoint T A) (v : V) :
    lrk S T A v = 2 ↔ v ∈ T := by
  unfold lrk
  by_cases h1 : v ∈ S
  · rw [iteT h1]; simp only [OfNat.zero_ne_ofNat, false_iff]
    exact disjoint_left.1 hST h1
  · rw [iteF h1]
    by_cases h2 : v ∈ A
    · rw [iteT h2]; simp only [OfNat.one_ne_ofNat, false_iff]
      exact fun h => disjoint_left.1 hTA h h2
    · rw [iteF h2]
      by_cases h3 : v ∈ T
      · rw [iteT h3]; simp [h3]
      · rw [iteF h3]; simp [h3]

lemma lrk_S_iff {S T A : Finset V} (v : V) : lrk S T A v = 0 ↔ v ∈ S := by
  unfold lrk; split_ifs <;> simp_all

set_option maxHeartbeats 4000000 in
/-- **The push-back from the sinks at a call.** -/
theorem frmP_exec {x : MCall M} {m : ℕ} {en : ℕ → D} {d b e j : ℕ} (c : Config)
    (hc : WordsBounded W c) (hL : Lay M gid u S T Z x m en d c.nmem)
    (h : PieceInv M x.1.piece x.2.1 x.2.2) (hpl : (pmap h).IsPlane) (hm : 0 < m)
    (hST : Disjoint S T) (hTh : Disjoint T (hunion x.2.1))
    {g : SDart (pdarts M x.1.piece x.2.1) → ℤ} (hg : (pmap h).IsAntisymm g)
    (hfl : FLHas Z m d en c.nmem g) (r3004 : c.nreg 3004 = d) (r3006 : c.nreg 3006 = b + 5)
    {π : HSep M} (hS : SegsAtV M en m π e b c) (r6800 : c.nreg 6800 = j)
    (hj : j < π.segs.length) (hP : Disjoint (π.segs[j]).verts (hunion x.2.1))
    (hde : d + fsz m ≤ e) (heb : e ≤ b) (w : b + 40 * m + 10 ≤ W)
    (wK : 3 * (m * Z) + 3 * Z + 1 ≤ W) :
    ∃ c' t, Exec P W frmP c c' t ∧ t ≤ frmCost m (rcnt (olab (nxFP d m c.nmem)) m) ∧
      FLHas Z m d en c'.nmem (frmG (pmap h) (NsStep.pchCall gid x h) g
        (vimg M x.2.2 (pdarts M x.1.piece x.2.1) T)
        (negSet (pmap h) g (vimg M x.2.2 (pdarts M x.1.piece x.2.1) (π.segs[j]).verts))) ∧
      (∀ a, (a < d + 4 + 6 * m ∨ d + 4 + 7 * m ≤ a) → (a < b ∨ b + 40 * m + 1 ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a85, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    fFrm_exec (P := P) c hc (by clear * - w; omega)
  have hL₁ : Lay M gid u S T Z x m en d c₁.nmem := by rw [m₁]; exact hL
  have hfl₁ : FLHas Z m d en c₁.nmem g := by rw [m₁]; exact hfl
  have hS₁ : SegsAtV M en m π e b c₁ :=
    hS.congr (f₁ _ (by decide)) (fun a _ _ => by rw [m₁])
  obtain ⟨c₂, t₂, e₂, ht₂, FL₂, k₂, s₂, rr₂, rm₂, o₂⟩ :=
    fcore_exec (P := P) (gid := gid) c₁ e₁.wb_right hL₁ h hpl hm hg hfl₁
      (by rw [f₁ _ (by decide)]; exact r3004) (by rw [f₁ _ (by decide)]; exact r3006) a85
      (Fr := vimg M x.2.2 (pdarts M x.1.piece x.2.1) T)
      (fun i hi => by
        rw [lrk_T_iff hST hTh]
        exact (hL₁.tail_mem_vimg h hTh hi).symm)
      hS₁ (by rw [f₁ _ (by decide)]; exact r6800) hj hP hde heb w wK
  have ex : Exec P W frmP c c₂ (t₁ + t₂) := .seq e₁ e₂
  refine ⟨c₂, _, ex, ?_, FL₂, fun a h1 h2 => by rw [k₂ a h1 h2, m₁], sreg_keepW ex frmP_dests,
    by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
  rw [m₁] at ht₂; unfold frmCost; clear * - ht₁ ht₂; omega

set_option maxHeartbeats 4000000 in
/-- **The push-back of the excess to the sources at a call.** -/
theorem retP_exec {x : MCall M} {m : ℕ} {en : ℕ → D} {d b e j : ℕ} (c : Config)
    (hc : WordsBounded W c) (hL : Lay M gid u S T Z x m en d c.nmem)
    (h : PieceInv M x.1.piece x.2.1 x.2.2) (hpl : (pmap h).IsPlane) (hm : 0 < m)
    (hSh : Disjoint S (hunion x.2.1))
    {g : SDart (pdarts M x.1.piece x.2.1) → ℤ} (hg : (pmap h).IsAntisymm g)
    (hfl : FLHas Z m d en c.nmem g) (r3004 : c.nreg 3004 = d) (r3006 : c.nreg 3006 = b + 5)
    {π : HSep M} (hS : SegsAtV M en m π e b c) (r6800 : c.nreg 6800 = j)
    (hj : j < π.segs.length) (hP : Disjoint (π.segs[j]).verts (hunion x.2.1))
    (hde : d + fsz m ≤ e) (heb : e ≤ b) (w : b + 40 * m + 10 ≤ W)
    (wK : 3 * (m * Z) + 3 * Z + 1 ≤ W) :
    ∃ c' t, Exec P W retP c c' t ∧ t ≤ retCost m (rcnt (olab (nxFP d m c.nmem)) m) ∧
      FLHas Z m d en c'.nmem (retG (pmap h) (NsStep.pchCall gid x h) g
        (posSet (pmap h) g (vimg M x.2.2 (pdarts M x.1.piece x.2.1) (π.segs[j]).verts))
        (vimg M x.2.2 (pdarts M x.1.piece x.2.1) S)) ∧
      (∀ a, (a < d + 4 + 6 * m ∨ d + 4 + 7 * m ≤ a) → (a < b ∨ b + 40 * m + 1 ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hZg := flHas_bnd hL h hg hfl
  have hA : d + 4 + 7 * m ≤ b := by unfold fsz at hde; omega
  obtain ⟨c₁, t₁, e₁, ht₁, a85, f₁, m₁, rr₁, rm₁, o₁⟩ := fRet_exec (P := P) c hc
  have hL₁ : Lay M gid u S T Z x m en d c₁.nmem := by rw [m₁]; exact hL
  have hfl₁ : FLHas Z m d en c₁.nmem g := by rw [m₁]; exact hfl
  -- negate
  obtain ⟨c₂, t₂, e₂, ht₂, FL₂, k₂, s₂, q₂, rr₂, rm₂, o₂⟩ :=
    negS_exec (P := P) c₁ e₁.wb_right hL₁ hZg hfl₁ (by rw [f₁ _ (by decide)]; exact r3004)
      (by clear * - w hA; omega) (by clear * - wK; omega)
  have lo₂ : ∀ a, a < b → c₂.nmem a = c.nmem a ∨ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 7 * m) :=
    fun a ha => by
      by_cases h' : d + 4 + 6 * m ≤ a ∧ a < d + 4 + 7 * m
      · exact Or.inr h'
      · left; rw [k₂ a (by clear * - h'; omega), m₁]
  have hL₂ : Lay M gid u S T Z x m en d c₂.nmem :=
    hL.congr fun a h1 h2 => by
      rw [k₂ a (by clear * - h2; omega), m₁]
  have hS₂ : SegsAtV M en m π e b c₂ :=
    hS.congr (by rw [s₂ _ (by decide), f₁ _ (by decide)])
      (fun a h1 h2 => by rw [k₂ a (by unfold fsz at hde; clear * - h1 hde; omega), m₁])
  have hg' : (pmap h).IsAntisymm (-g) := fun e => by simp only [Pi.neg_apply, hg e]
  have hZg' : ∀ e, -(Z : ℤ) ≤ (-g) e ∧ (-g) e ≤ Z := fun e => by
    have := hZg e; simp only [Pi.neg_apply]; omega
  have hSv : ∀ i (hi : i < m), lrk S T (hunion x.2.1) (M.tail (en i)) = 0 ↔
      (pmap h).tail (vDart hL₂ hi) ∈ vimg M x.2.2 (pdarts M x.1.piece x.2.1) S := fun i hi => by
    rw [lrk_S_iff]; exact (hL₂.tail_mem_vimg h hSh hi).symm
  obtain ⟨c₃, t₃, e₃, ht₃, FL₃, k₃, s₃, rr₃, rm₃, o₃⟩ :=
    fcore_exec (P := P) (gid := gid) c₂ e₂.wb_right hL₂ h hpl hm hg' FL₂
      (by rw [s₂ _ (by decide), f₁ _ (by decide)]; exact r3004)
      (by rw [s₂ _ (by decide), f₁ _ (by decide)]; exact r3006)
      (by rw [q₂ _ (by decide) (by decide)]; exact a85)
      (Fr := vimg M x.2.2 (pdarts M x.1.piece x.2.1) S) hSv hS₂
      (by rw [s₂ _ (by decide), f₁ _ (by decide)]; exact r6800) hj hP hde heb w wK
  -- negate back
  have hL₃ : Lay M gid u S T Z x m en d c₃.nmem :=
    hL₂.congr fun a h1 h2 => k₃ a (by clear * - h2; omega) (by clear * - h2 hA; omega)
  obtain ⟨hb1, hb2⟩ := pchCall_bnd (gid := gid) hL₂ h hpl hm hg' hZg'
    (fun v => if v ∈ negSet (pmap h) (-g)
        (vimg M x.2.2 (pdarts M x.1.piece x.2.1) (π.segs[j]).verts) then 0
      else (pmap h).div (-g) v) (vimg M x.2.2 (pdarts M x.1.piece x.2.1) S)
  obtain ⟨c₄, t₄, e₄, ht₄, FL₄, k₄, s₄, q₄, rr₄, rm₄, o₄⟩ :=
    negS_exec (P := P) c₃ e₃.wb_right hL₃ hb2 FL₃
      (by rw [s₃ _ (by decide), s₂ _ (by decide), f₁ _ (by decide)]; exact r3004)
      (by clear * - w hA; omega) (by clear * - wK; omega)
  have ex : Exec P W retP c c₄ (t₁ + (t₂ + (t₃ + t₄))) := .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have hnx : rcnt (olab (nxFP d m c₂.nmem)) m = rcnt (olab (nxFP d m c.nmem)) m := by
    have hp2 : PermOn (nxFP d m c₂.nmem) m := hL₂.permOn_face hL₂.faceArr_nx
    refine rcnt_olab_congr hp2 fun i hi => ?_
    have := (hL.rv i hi).1
    unfold nxFP
    rw [k₂ (d + 4 + m + i) (by clear * - hi; omega), m₁,
      k₂ _ (by clear * - this; omega), m₁]
  rw [hnx] at ht₃
  refine ⟨c₄, _, ex, ?_, ?_, fun a h1 h2 => ?_, sreg_keepW ex retP_dests,
    by rw [rr₄, rr₃, rr₂, rr₁], by rw [rm₄, rm₃, rm₂, rm₁], by rw [o₄, o₃, o₂, o₁]⟩
  · unfold retCost; clear * - ht₁ ht₂ ht₃ ht₄; omega
  · have e : posSet (pmap h) g (vimg M x.2.2 (pdarts M x.1.piece x.2.1) (π.segs[j]).verts) =
        negSet (pmap h) (-g) (vimg M x.2.2 (pdarts M x.1.piece x.2.1) (π.segs[j]).verts) := by
      rw [← posSet_neg, neg_neg]
    unfold retG frmG
    rw [e]
    exact FL₄
  · rw [k₄ a h1, k₃ a h1 h2, k₂ a h1, m₁]

end MfDrv

end BKMNW

end PlanarFlow
