module

public import PlanarFlow.BKMNW.NcHdB
public import PlanarFlow.BKMNW.NcHdD
public import PlanarFlow.BKMNW.NcHdF

/-!
# The head of `c2sP`, stages A–C composed

**`hdP = (r8430 := LAB ; dvP) ; (tfGl 6800 9838 9839 ; tfP) ; (rbGl ; rbP)`** and
**`hd1_exec`**: from the frame holding `Z + g` and the capacities `U` at `CPb`, with the registers
of `hdF` (`HdRegs`), the labels `LAB`, the net outflows `DV`, `DG`, the flags `CF` of the part `πj`
and the marks `MK` of `C⁺`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap MfDrv NsStep StCall OrbLab WordRAM WordRAM.Machine
  WordRAM.Machine.Stmt WordRAM.Programs

universe w

/-- **Stages A–C of the head.** -/
def hdP : Stmt :=
  .seq (.seq (block [.copyN 8430 9835]) dvP) (.seq (.seq (tfGl 6800 9838 9839) tfP) (.seq rbGl rbP))

/-- The registers kept by `hdP`. -/
def Keep1 (r : ℕ) : Prop :=
  r < 1400 ∨ (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) ∨ (9757 ≤ r ∧ r ≤ 9855) ∨
    (9872 ≤ r ∧ r ≤ 9878)

lemma keep1_a {r : ℕ} (h : Keep1 r) :
    (r < 7350 ∨ 7352 < r) ∧ (r < 7400 ∨ 7405 < r) ∧ (r < 8430 ∨ 8447 < r) := by
  unfold Keep1 at h; omega

lemma keep1_b {r : ℕ} (h : Keep1 r) :
    ¬ TfGo r ∧ ¬ (9856 ≤ r ∧ r ≤ 9871) ∧ ¬ TfScr r := by
  unfold Keep1 at h; unfold TfGo TfScr; omega

lemma keep1_c {r : ℕ} (h : Keep1 r) :
    ¬ RbGo r ∧ r ≠ 9860 ∧ r ≠ 9879 ∧ (r < 1400 ∨ (1419 < r ∧ r < 9620) ∨ 9646 < r) := by
  unfold Keep1 at h; unfold RbGo; omega

lemma keep1_hd {r : ℕ} (h : (9813 ≤ r ∧ r ≤ 9819) ∨ (9830 ≤ r ∧ r ≤ 9855) ∨ (9872 ≤ r ∧ r ≤ 9878)) :
    Keep1 r := by
  unfold Keep1; omega

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

variable {P : Input} {W : ℕ}

/-- `HdRegs` through a run keeping `Keep1` and the registers `9856 … 9878` is not needed: only
`9813 … 9819`, `9830 … 9855`, `9874 … 9878` matter. -/
lemma HdRegs.keep1 {c c' : Config} {d b m : ℕ} (hR : HdRegs c d b m Z)
    (hk : ∀ r, Keep1 r → c'.nreg r = c.nreg r) : HdRegs c' d b m Z :=
  hR.congr fun r hr => hk r (by unfold Keep1; omega)

set_option maxHeartbeats 4000000 in
/-- **Stages A–C of the head.** -/
theorem hd1_exec {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    (h : SCond M l r π Hs σ) (hrot : (pmap h.1).RotTrans) {m : ℕ} {en : ℕ → D} {d e b : ℕ}
    (hm : 0 < m) (c : Config) (hc : WordsBounded W c)
    (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem) (hSeg : SegsAt' M en m π e b c)
    (hde : d + fsz m ≤ e) (heb : e ≤ b) {j : ℕ} {πj : SPath (pmap h.1)}
    (hj : (segsP h.1 π.segs h.2)[j]? = some πj)
    {U g : SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ} {CPb : ℕ}
    (hFL : ∀ i < m, (c.nmem (d + 4 + 6 * m + i) : ℤ) =
      Z + g (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i))
    (hCP : ∀ i < m, (c.nmem (CPb + i) : ℤ) =
      U (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i))
    (hCPZ : ∀ i < m, c.nmem (CPb + i) ≤ Z) (hgZ : ∀ y, g y ≤ Z)
    (hR : HdRegs c d b m Z) (r30 : c.nreg 9830 = CPb) (r04 : c.nreg 3004 = d)
    (r00 : c.nreg 6800 = j) (hCPl : CPb + m ≤ b + m)
    (wW : b + 28 * m + 10 + stRm m ≤ W) (wZ : 2 * Z ≤ W) (wmZ : 2 * Z * m ≤ W) (w6 : 6 ≤ W) :
    ∃ c' k, Exec P W hdP c c' k ∧
      k ≤ 48 * m + 31 + (25 + (5 * (m + 1) + 15 * m + 9 * m + 25) + (22 + rbCost m)) ∧
      (∀ i < m, c'.nmem (b + m + i) = olab (sgF d m c.nmem) i + 1) ∧
      (∀ i < m, (c'.nmem (b + 2 * m + (c'.nmem (b + m + i) - 1)) : ℤ) -
          Z * c'.nmem (b + 3 * m + (c'.nmem (b + m + i) - 1)) =
        (pmap h.1).div g ((pmap h.1).tail
          (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i))) ∧
      (∀ v < m, c'.nmem (b + 3 * m + v) ≤ m) ∧
      (∀ i < m, c'.nmem (b + 5 * m + 1 + i) = flagX (pmap h.1)
        (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm) πj.verts i) ∧
      (∀ i < m, c'.nmem (b + 14 * m + 5 + i) ≤ 1 ∧
        (c'.nmem (b + 14 * m + 5 + i) = 1 ∧
            (pmap h.1).tail (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i) ∈
              πj.verts ↔
          (pmap h.1).tail (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i) ∈
            fwdReach (pmap h.1) U g (posSet (pmap h.1) g πj.verts) πj.verts)) ∧
      (∀ a, (a < b + m ∨ b + 16 * m + 9 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, Keep1 r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- arithmetic first
  have hfz : d + 4 + 7 * m ≤ b := by unfold fsz at hde; omega
  have v1 : b + 4 * m + 1 ≤ W := by omega
  have v2 : b + m + m ≤ b + 4 * m := by omega
  have v3 : b + 4 * m + m + 1 ≤ b + 5 * m + 1 := by omega
  have v4 : b + 5 * m + 1 + m ≤ W := by omega
  have v5 : CPb + m ≤ b + 6 * m + 1 := by omega
  have v6 : b + 6 * m + 1 + 4 * (m + 2) + 6 * m + 1 ≤ W := by omega
  have v7 : m * Z ≤ W := by
    have : m * Z ≤ 2 * Z * m := by nlinarith
    omega
  have hjl : j < (segsP h.1 π.segs h.2).length := by
    by_contra hc'; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  have hπj : (segsP h.1 π.segs h.2)[j] = πj := by
    rw [List.getElem?_eq_getElem hjl] at hj; exact Option.some_inj.1 hj
  -- stage A
  obtain ⟨c₁, k₁, e₁, hk₁, l₁, d₁, g₁, f₁, q₁, rr₁, rm₁, o₁⟩ := hdLab_exec (P := P) h.1 c hc hL hm
    hFL hgZ r04 hR.r35 hfz v1 wmZ w6
  have K₁ : ∀ r, Keep1 r → c₁.nreg r = c.nreg r := fun r hr => by
    obtain ⟨a1, a2, a3⟩ := keep1_a hr; exact q₁ r a1 a2 a3
  have hR₁ : HdRegs c₁ d b m Z := hR.keep1 K₁
  have mem₁ : ∀ a, a < b + m → c₁.nmem a = c.nmem a := fun a ha => f₁ a (Or.inl ha)
  have hL₁ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₁.nmem :=
    hL.congr fun a h1 h2 => mem₁ a (by omega)
  have hsg₁ : ∀ i < m, olab (sgF d m c.nmem) i = olab (sgF d m c₁.nmem) i := fun i hi =>
    olab_congr hL.permOn_sg (fun t ht => by unfold sgF; exact (mem₁ _ (by omega)).symm) hi
  have hSeg₁ : SegsAt' M en m π e b c₁ := by
    unfold SegsAt' at hSeg ⊢
    rw [K₁ 6807 (by unfold Keep1; omega)]
    exact hSeg.congr fun a h1 h2 => mem₁ a (by have := hSeg.1.1; omega)
  -- stage B
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂, g₂, rr₂, rm₂, o₂⟩ := hdTf_exec (P := P) h hm c₁ e₁.wb_right
    hL₁ hSeg₁ hde heb (rj := 6800) (Vr := 9838) (Fr := 9839) (jj := j) (Vb := b + 4 * m)
    (Fb := b + 5 * m + 1) (Or.inr (by decide)) (by decide) (by decide) (by decide)
    (by rw [K₁ 6800 (by unfold Keep1; omega)]; exact r00) hR₁.r38 hR₁.r39 hjl hR₁.r32 hR₁.r35
    hR₁.r74 (fun i hi => by rw [l₁ i hi, hsg₁ i hi]) v2 v3 v4
  rw [hπj] at v₂
  have K₂ : ∀ r, Keep1 r → c₂.nreg r = c₁.nreg r := fun r hr => by
    obtain ⟨a1, a2, a3⟩ := keep1_b hr; exact g₂ r a1 a2 a3
  have hR₂ : HdRegs c₂ d b m Z := hR₁.keep1 K₂
  have mem₂ : ∀ a, (a < b + 4 * m ∨ b + 6 * m + 1 ≤ a) → c₂.nmem a = c₁.nmem a := fun a ha =>
    f₂ a (by omega)
  have mem₂c : ∀ a, a < b + m → c₂.nmem a = c.nmem a := fun a ha => by
    rw [mem₂ a (by omega), mem₁ a ha]
  have hL₂ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₂.nmem :=
    hL.congr fun a h1 h2 => mem₂c a (by omega)
  have hsg₂ : ∀ i < m, olab (sgF d m c.nmem) i = olab (sgF d m c₂.nmem) i := fun i hi =>
    olab_congr hL.permOn_sg (fun t ht => by unfold sgF; exact (mem₂c _ (by omega)).symm) hi
  -- the arrays at `c₂`
  have lab₂ : ∀ i < m, c₂.nmem (b + m + i) = olab (sgF d m c.nmem) i + 1 := fun i hi => by
    rw [mem₂ _ (by omega), l₁ i hi]
  have hl1 : ∀ i < m, 1 ≤ c₂.nmem (b + m + i) ∧ c₂.nmem (b + m + i) ≤ m := fun i hi => by
    rw [lab₂ i hi]; have := olab_lt hL.permOn_sg hi; omega
  have dv₂ : ∀ i < m, (c₂.nmem (b + 2 * m + (c₂.nmem (b + m + i) - 1)) : ℤ) -
      Z * c₂.nmem (b + 3 * m + (c₂.nmem (b + m + i) - 1)) =
      (pmap h.1).div g ((pmap h.1).tail
        (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm i)) := fun i hi => by
    have hl := hl1 i hi
    have e1 : c₂.nmem (b + m + i) = c₁.nmem (b + m + i) := mem₂ _ (Or.inl (by omega))
    rw [e1] at hl ⊢
    rw [mem₂ (b + 2 * m + (c₁.nmem (b + m + i) - 1)) (Or.inl (by omega)),
      mem₂ (b + 3 * m + (c₁.nmem (b + m + i) - 1)) (Or.inl (by omega))]
    exact d₁ i hi
  have dg₂ : ∀ v < m, c₂.nmem (b + 3 * m + v) ≤ m := fun v hv => by
    rw [mem₂ _ (by omega)]; exact g₁ v hv
  have fl₂ : ∀ i < m, (c₂.nmem (d + 4 + 6 * m + i) : ℤ) =
      Z + g (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL₂.en_mem hm i) := fun i hi => by
    rw [mem₂c _ (by omega)]; exact hFL i hi
  have cp₂ : ∀ i < m, (c₂.nmem (CPb + i) : ℤ) =
      U (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL₂.en_mem hm i) := fun i hi => by
    rw [mem₂c _ (by omega)]; exact hCP i hi
  have cf₂ : ∀ i < m, c₂.nmem (b + 5 * m + 1 + i) = flagX (pmap h.1)
      (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL₂.en_mem hm) πj.verts i := v₂
  -- stage C
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃, g₃, rr₃, rm₃, o₃⟩ := hdMK0_exec (P := P) c₂ e₂.wb_right
    hR₂.r32 hR₂.r40 hR₂.r76 (by rw [K₂ 9830 (by unfold Keep1; omega),
      K₁ 9830 (by unfold Keep1; omega)]; exact r30) hR₂.r33 hR₂.r39 hR₂.r35 hR₂.r36 hR₂.r37
    hR₂.r75 hR₂.r74 hfz v5 v6 hl1
    (fun i hi => by rw [cf₂ i hi]; unfold flagX; split_ifs <;> omega)
    (fun i hi => (hL₂.sg i hi).1) (fun i hi => (hL₂.rv i hi).1)
    (fun i hi => by rw [mem₂c _ (by omega)]; have := hCPZ i hi; omega)
    (fun v hv => by have := Nat.mul_le_mul_right Z (dg₂ v hv); omega)
  have hmk := hdMK_sem h.1 hL₂ hm hrot (U := U) (g := g) (C := πj.verts) fl₂ cp₂ cf₂
    (fun i hi => (hl1 i hi).1) dv₂ (mk := fun i => c₃.nmem (b + 14 * m + 5 + i)) v₃
  have mem₃ : ∀ a, (a < b + 6 * m + 1 ∨ b + 16 * m + 9 ≤ a) → c₃.nmem a = c₂.nmem a := fun a ha =>
    f₃ a (by omega)
  have K₃ : ∀ r, Keep1 r → c₃.nreg r = c₂.nreg r := fun r hr => by
    obtain ⟨a1, a2, a3, a4⟩ := keep1_c hr; exact g₃ r a1 a2 a3 a4
  refine ⟨c₃, k₁ + (k₂ + k₃), e₁.seq (e₂.seq e₃), by omega, fun i hi => ?_, fun i hi => ?_,
    fun v hv => ?_, fun i hi => ?_, hmk, fun a ha => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [mem₃ _ (by omega)]; exact lab₂ i hi
  · have hl := hl1 i hi
    have e1 : c₃.nmem (b + m + i) = c₂.nmem (b + m + i) := mem₃ _ (Or.inl (by omega))
    rw [e1, mem₃ (b + 2 * m + (c₂.nmem (b + m + i) - 1)) (Or.inl (by omega)),
      mem₃ (b + 3 * m + (c₂.nmem (b + m + i) - 1)) (Or.inl (by omega))]
    exact dv₂ i hi
  · rw [mem₃ _ (by omega)]; exact dg₂ v hv
  · rw [mem₃ _ (by omega)]; exact cf₂ i hi
  · rcases ha with ha | ha
    · rw [mem₃ a (Or.inl (by omega)), mem₂c a ha]
    · rw [mem₃ a (Or.inr ha), mem₂ a (Or.inr (by omega)), f₁ a (Or.inr (by omega))]
  · rw [K₃ r hr, K₂ r hr, K₁ r hr]
  · rw [rr₃, rr₂, rr₁]
  · rw [rm₃, rm₂, rm₁]
  · rw [o₃, o₂, o₁]

end NcStep

end BKMNW

end PlanarFlow
