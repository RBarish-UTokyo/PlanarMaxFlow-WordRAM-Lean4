module

public import PlanarFlow.BKMNW.MsCutE

/-!
# The cut map of the path on the machine, part F: the preparation run

**`cutPre_exec`** (on arrays): from `RV = rv`, `RT = rt` (a permutation of `[0, m)`), the path
flags `LF = lf` (`≤ 1`) and the tour array `TA = ta` (a permutation), all below the scratch
`Z`, within `cpCost m = 78 m + 70` steps:

* `TF[i] = tfF lf rt m i` at `Z + 2m` (`1` iff a dart of the path has the vertex label of `i`);
* `RE[i] = reF lf i`, `RK[i] = rkF lf rt m i` at `Z + 3m`, `Z + 4m` (the ranks);
* `TI[ta i] = i` at `Z + 5m`;
* the registers of the value blocks (`VRegs`, `nE = reF lf m`, `nT = rkF lf rt m m`) and of the
  write loops (`r8200 = m`, `r8201 = RVo`, `r8202 = RTo`);
* the memory outside `[Z, Z + 6m)`, the registers outside `CpScr`, reals and output kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab

variable {P : Input} {W : ℕ}

/-- The flag of a dart whose tail is a vertex of the path (by the vertex labels). -/
noncomputable def tfF (lf rt : ℕ → ℕ) (m i : ℕ) : ℕ :=
  if ∃ i' < m, 0 < lf i' ∧ olab rt i' + 1 = olab rt i + 1 then 1 else 0

/-- The rank of a copy. -/
noncomputable def reF (lf : ℕ → ℕ) (i : ℕ) : ℕ := ((range i).filter fun j => lf j = 0).card

/-- The rank of a root. -/
noncomputable def rkF (lf rt : ℕ → ℕ) (m i : ℕ) : ℕ :=
  ((range i).filter fun j => 0 < tfF lf rt m j).card

/-- The step bound of `cutPre`. -/
def cpCost (m : ℕ) : ℕ := 78 * m + 70

set_option maxHeartbeats 2000000 in
/-- **The preparation run.** -/
theorem cutPre_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb LFb TAb Z RVo RTo : ℕ}
    (hI : CpIn c m RVb RTb LFb TAb Z RVo RTo) {rv rt lf ta : ℕ → ℕ}
    (hrv : ∀ i < m, c.nmem (RVb + i) = rv i ∧ rv i < m)
    (hrt : ∀ i < m, c.nmem (RTb + i) = rt i) (prt : PermOn rt m)
    (hlf : ∀ i < m, c.nmem (LFb + i) = lf i ∧ lf i ≤ 1)
    (hta : ∀ i < m, c.nmem (TAb + i) = ta i) (pta : PermOn ta m)
    (dRV : RVb + m ≤ Z) (dRT : RTb + m ≤ Z) (dLF : LFb + m ≤ Z) (dTA : TAb + m ≤ Z)
    (hw : Z + 6 * m + 1 ≤ W) :
    ∃ c' t, Exec P W cutPre c c' t ∧ t ≤ cpCost m ∧
      (∀ i < m, c'.nmem (Z + 2 * m + i) = tfF lf rt m i) ∧
      (∀ i < m, c'.nmem (Z + 3 * m + i) = reF lf i ∧ c'.nmem (Z + 4 * m + i) = rkF lf rt m i) ∧
      (∀ i < m, c'.nmem (Z + 5 * m + ta i) = i) ∧
      VRegs c' LFb (Z + 2 * m) (Z + 3 * m) (Z + 4 * m) TAb (Z + 5 * m) RVb RTb (reF lf m)
        (rkF lf rt m m) ∧
      c'.nreg 8200 = m ∧ c'.nreg 8201 = RVo ∧ c'.nreg 8202 = RTo ∧
      (∀ a, (a < Z ∨ Z + 6 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ CpScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- 1. registers
  obtain ⟨c₁, k₁, e₁, hk₁, a36, a33, a34, a40, a35, aR, am, ar, arm, ao⟩ :=
    cpA_exec (P := P) c hc hI hw
  have I₁ : CpIn c₁ m RVb RTb LFb TAb Z RVo RTo :=
    hI.of fun r h1 h2 => aR r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, b42, b43, b44, b47, b30, b31, bR, bm, br, brm, bo⟩ :=
    cpB_exec (P := P) c₁ e₁.wb_right I₁.r50 I₁.r55 a40 hw
  have I₂ : CpIn c₂ m RVb RTb LFb TAb Z RVo RTo :=
    I₁.of fun r h1 h2 => bR r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have q₂ : ∀ r, 8233 ≤ r → r ≤ 8236 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    bR r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  -- 2. zero `[Z, Z + 2m)`
  obtain ⟨c₃, k₃, e₃, hk₃, z0, zm, zR, zr, zrm, zo⟩ :=
    mzFill_exec (P := P) c₂ e₂.wb_right b30 b31 (by omega) (by omega)
  -- 3. the vertex labels
  obtain ⟨c₄, k₄, e₄, hk₄, d50, d51, d52, dR, dm, dr, drm, dout⟩ := cpC_exec (P := P) c₃
    e₃.wb_right
  have s₄ : ∀ r, 8200 ≤ r → c₄.nreg r = c₂.nreg r := fun r hr => by
    rw [dR r (by omega), zR r (by omega)]
  obtain ⟨c₅, k₅, e₅, hk₅, lv, lm, lR, lr, lrm, lo⟩ := olProg_exec (P := P) prt (Pb := RTb)
    (Lb := Z) dRT (by omega) (by omega) c₄ e₄.wb_right
    (by rw [d50, zR _ (by omega), I₂.r52]) (by rw [d51, zR _ (by omega), I₂.r55])
    (by rw [d52, zR _ (by omega), I₂.r50])
    (fun x hx => by rw [dm, zm _ (by omega), bm, am]; exact hrt x hx)
    (fun x hx => by rw [dm]; exact z0 x (by omega))
  have s₅ : ∀ r, 8200 ≤ r → c₅.nreg r = c₂.nreg r := fun r hr => by
    rw [lR r (by omega), s₄ r hr]
  have m₅ : ∀ a, (a < Z ∨ Z + 2 * m ≤ a) → c₅.nmem a = c.nmem a := fun a ha => by
    rw [lm a (by omega), dm, zm a (by omega), bm, am]
  -- 4. the marks of the vertices of the path
  have hvl : ∀ i < m, c₅.nmem (Z + i) = olab rt i + 1 ∧ 1 ≤ olab rt i + 1 ∧
      olab rt i + 1 ≤ m := fun i hi => ⟨lv i hi, by omega, by have := olab_lt prt hi; omega⟩
  obtain ⟨c₆, k₆, e₆, hk₆, vv, vm, vR, vr, vrm, vo⟩ := vpMk_exec (P := P) c₅ e₅.wb_right
    (LFb := LFb) (VLb := Z) (VPb := Z + m - 1) (m := m) (lf := lf)
    (by rw [s₅ _ (by omega), q₂ _ (by omega) (by omega), a33])
    (by rw [s₅ _ (by omega), q₂ _ (by omega) (by omega), a34])
    (by rw [s₅ _ (by omega), q₂ _ (by omega) (by omega), a35])
    (by rw [s₅ _ (by omega), q₂ _ (by omega) (by omega), a36]) hvl
    (fun i hi => by rw [m₅ _ (by omega)]; exact (hlf i hi).1)
    (fun l h1 h2 => by
      rw [lm (Z + m - 1 + l) (by omega), dm]
      have := z0 (m - 1 + l) (by omega)
      rwa [show Z + (m - 1 + l) = Z + m - 1 + l by omega] at this)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have s₆ : ∀ r, 8200 ≤ r → (r < 8237 ∨ 8241 < r) → c₆.nreg r = c₂.nreg r := fun r h1 h2 => by
    rw [vR r h2, s₅ r h1]
  -- 5. the root flags
  obtain ⟨c₇, k₇, e₇, hk₇, f10, f11, f12, f13, fR, fm, fr, frm, fo⟩ := cpD_exec (P := P) c₆
    e₆.wb_right
  obtain ⟨c₈, k₈, e₈, hk₈, gv, gm, gR, gr, grm, go⟩ := lgProg_exec (P := P) c₇ e₇.wb_right
    (m := m) (IXb := Z) (Ab := Z + m - 1) (OUTb := Z + 2 * m)
    (by rw [f10, s₆ _ (by omega) (by omega), I₂.r50])
    (by rw [f11, s₆ _ (by omega) (by omega), I₂.r55])
    (by rw [f12, s₆ _ (by omega) (by omega), q₂ _ (by omega) (by omega), a35])
    (by rw [f13, s₆ _ (by omega) (by omega), b42]) (by omega) (by omega) (by omega)
    (fun j hj => by rw [fm, vm _ (by omega), (hvl j hj).1]; have := (hvl j hj).2.2; omega)
    (fun j hj h => by omega)
    (fun j hj h => by rw [fm, vm _ (by omega), (hvl j hj).1] at h; have := (hvl j hj).2.2; omega)
  have vTF : ∀ i < m, c₈.nmem (Z + 2 * m + i) = tfF lf rt m i := fun i hi => by
    rw [gv i hi, fm, vm (Z + i) (by omega), (hvl i hi).1,
      vv (olab rt i + 1) (by omega) (by have := (hvl i hi).2.2; omega)]
    rfl
  have s₈ : ∀ r, 8200 ≤ r → (r < 8237 ∨ 8241 < r) → c₈.nreg r = c₂.nreg r := fun r h1 h2 => by
    rw [gR r (by omega), fR r (by omega), s₆ r h1 h2]
  have m₈ : ∀ a, (a < Z ∨ Z + 3 * m ≤ a) → c₈.nmem a = c.nmem a := fun a ha => by
    rw [gm a (by omega), fm, vm a (by omega), m₅ a (by omega)]
  -- 6. the ranks
  obtain ⟨c₉, k₉, e₉, hk₉, rv9, r45, r46, rm, rR, rr, rrm, ro⟩ := rkLoop_exec (P := P) c₈
    e₈.wb_right (LFb := LFb) (TFb := Z + 2 * m) (REb := Z + 3 * m) (RKb := Z + 4 * m) (m := m)
    (lf := lf) (tf := tfF lf rt m)
    (by rw [s₈ _ (by omega) (by omega), q₂ _ (by omega) (by omega), a33])
    (by rw [s₈ _ (by omega) (by omega), q₂ _ (by omega) (by omega), a36])
    (by rw [s₈ _ (by omega) (by omega), b42]) (by rw [s₈ _ (by omega) (by omega), b43])
    (by rw [s₈ _ (by omega) (by omega), b44])
    (fun i hi => by rw [m₈ _ (by omega)]; exact hlf i hi) vTF (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have s₉ : ∀ r, 8200 ≤ r → (r < 8237 ∨ 8241 < r) → r ≠ 8245 → r ≠ 8246 →
      c₉.nreg r = c₂.nreg r := fun r h1 h2 h3 h4 => by rw [rR r h2 h3 h4, s₈ r h1 h2]
  -- 7. the inverse tour
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, i20, i21, i22, i23, i24, iR, im, ir, irm, io⟩ :=
    cpE_exec (P := P) c₉ e₉.wb_right
  have hta₁₀ : ∀ i < m, c₁₀.nmem (TAb + i) = ta i := fun i hi => by
    rw [im, rm _ (by omega) (by omega), m₈ _ (by omega)]; exact hta i hi
  obtain ⟨c₁₁, k₁₁, e₁₁, hk₁₁, tv, tm, tR, tr, trm, tout⟩ := lsProg_exec (P := P) c₁₀
    e₁₀.wb_right (m := m) (IXb := TAb) (FLb := TAb) (thr := m) (OUTb := Z + 5 * m)
    (by rw [i20, s₉ _ (by omega) (by omega) (by omega) (by omega), I₂.r50])
    (by rw [i21, s₉ _ (by omega) (by omega) (by omega) (by omega), I₂.r54])
    (by rw [i22, s₉ _ (by omega) (by omega) (by omega) (by omega), I₂.r54])
    (by rw [i23, s₉ _ (by omega) (by omega) (by omega) (by omega), I₂.r50])
    (by rw [i24, s₉ _ (by omega) (by omega) (by omega) (by omega), b47])
    (by omega) (by omega) (by omega)
    (fun j hj _ => by rw [hta₁₀ j hj]; have := pta.lt j hj; omega)
    (fun i hi j hj _ _ e => pta.inj i hi j hj (by rw [← hta₁₀ i hi, ← hta₁₀ j hj, e]))
    (fun i hi _ j hj => by rw [hta₁₀ i hi]; omega)
    (fun i hi _ j hj => by rw [hta₁₀ i hi]; omega)
  have vTI : ∀ i < m, c₁₁.nmem (Z + 5 * m + ta i) = i := fun i hi => by
    have := tv i hi (by rw [hta₁₀ i hi]; exact pta.lt i hi)
    rwa [hta₁₀ i hi] at this
  have m₁₁ : ∀ a, (a < Z + 5 * m ∨ Z + 6 * m ≤ a) → c₁₁.nmem a = c₉.nmem a := fun a ha => by
    rw [tm a (fun i hi _ => by rw [hta₁₀ i hi]; have := pta.lt i hi; omega), im]
  -- 8. the registers of the value blocks and of the loops
  obtain ⟨c₁₂, k₁₂, e₁₂, hk₁₂, h20, h21, h22, h23, h24, h25, hR₁₂, hm₁₂, hr₁₂, hrm₁₂, ho₁₂⟩ :=
    cpF_exec (P := P) c₁₁ e₁₁.wb_right
  have hnE : reF lf m ≤ m := cnt_le_self _ m
  have hnT : rkF lf rt m m ≤ m := cnt_le_self _ m
  obtain ⟨c₁₃, k₁₃, e₁₃, hk₁₃, g26, g27, g28, g30, g31, g32, gR₁₃, gm₁₃, gr₁₃, grm₁₃, go₁₃⟩ :=
    cpG_exec (P := P) c₁₂ e₁₂.wb_right (nE := reF lf m) (nT := rkF lf rt m m)
      (by rw [hR₁₂ _ (by omega), tR _ (by omega), iR _ (by omega), r45]; rfl)
      (by rw [hR₁₂ _ (by omega), tR _ (by omega), iR _ (by omega), r46]; rfl) (by omega)
  obtain ⟨c₁₄, k₁₄, e₁₄, hk₁₄, h00, h01, h02, hR₁₄, hm₁₄, hr₁₄, hrm₁₄, ho₁₄⟩ :=
    cpH_exec (P := P) c₁₃ e₁₃.wb_right
  -- the registers `≥ 8250` are the inputs
  have sIn11 : ∀ r, 8250 ≤ r → r ≤ 8257 → c₁₁.nreg r = c.nreg r := fun r h1 h2 => by
    rw [tR r (by omega), iR r (by omega),
      s₉ r (by omega) (by omega) (by omega) (by omega), bR r (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), aR r (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]
  have sIn : ∀ r, 8250 ≤ r → r ≤ 8257 → c₁₃.nreg r = c.nreg r := fun r h1 h2 => by
    rw [gR₁₃ r (by omega), hR₁₂ r (by omega), sIn11 r h1 h2]
  -- the registers `8242 … 8247` of the bases
  have sB : ∀ r, 8242 ≤ r → r ≤ 8247 → r ≠ 8245 → r ≠ 8246 → c₁₁.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 h4 => by
      rw [tR r (by omega), iR r (by omega), s₉ r (by omega) (by omega) h3 h4]
  refine ⟨c₁₄, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + (k₈ + (k₉ + (k₁₀ + (k₁₁ + (k₁₂ + (k₁₃ +
    k₁₄)))))))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉ (.seq e₁₀
      (.seq e₁₁ (.seq e₁₂ (.seq e₁₃ e₁₄)))))))))))), ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · unfold cpCost; omega
  · rw [hm₁₄, gm₁₃, hm₁₂, m₁₁ _ (by omega), rm _ (by omega) (by omega)]; exact vTF i hi
  · rw [hm₁₄, gm₁₃, hm₁₂, m₁₁ _ (by omega), m₁₁ _ (by omega)]; exact rv9 i hi
  · rw [hm₁₄, gm₁₃, hm₁₂]; exact vTI i hi
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals rw [hR₁₄ _ (by omega)]
    · rw [gR₁₃ _ (by omega), h20, sIn11 _ (by omega) (by omega), hI.r53]
    · rw [gR₁₃ _ (by omega), h21, sB _ (by omega) (by omega) (by omega) (by omega), b42]
    · rw [gR₁₃ _ (by omega), h22, sB _ (by omega) (by omega) (by omega) (by omega), b43]
    · rw [gR₁₃ _ (by omega), h23, sB _ (by omega) (by omega) (by omega) (by omega), b44]
    · rw [gR₁₃ _ (by omega), h24, tR _ (by omega), iR _ (by omega),
        s₉ _ (by omega) (by omega) (by omega) (by omega), I₂.r54]
    · rw [gR₁₃ _ (by omega), h25, sB _ (by omega) (by omega) (by omega) (by omega), b47]
    · rw [g26, hR₁₂ _ (by omega), tR _ (by omega), iR _ (by omega),
        s₉ _ (by omega) (by omega) (by omega) (by omega), I₂.r51]
    · rw [g27, hR₁₂ _ (by omega), tR _ (by omega), iR _ (by omega),
        s₉ _ (by omega) (by omega) (by omega) (by omega), I₂.r52]
    · exact g28
    · exact g30
    · exact g31
    · exact g32
  · rw [h00, sIn _ (by omega) (by omega), hI.r50]
  · rw [h01, sIn _ (by omega) (by omega), hI.r56]
  · rw [h02, sIn _ (by omega) (by omega), hI.r57]
  · rw [hm₁₄, gm₁₃, hm₁₂, m₁₁ _ (by omega), rm _ (by omega) (by omega), m₈ _ (by omega)]
  · simp only [CpScr, not_or, not_and, not_le] at hr
    rw [hR₁₄ r (by omega), gR₁₃ r (by omega), hR₁₂ r (by omega), tR r (by omega),
      iR r (by omega), rR r (by omega) (by omega) (by omega), gR r (by omega), fR r (by omega),
      vR r (by omega), lR r (by omega), dR r (by omega), zR r (by omega),
      bR r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      aR r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  · rw [hr₁₄, gr₁₃, hr₁₂, tr, ir, rr, gr, fr, vr, lr, dr, zr, br, ar]
  · rw [hrm₁₄, grm₁₃, hrm₁₂, trm, irm, rrm, grm, frm, vrm, lrm, drm, zrm, brm, arm]
  · rw [ho₁₄, go₁₃, ho₁₂, tout, io, ro, go, fo, vo, lo, dout, zo, bo, ao]

end MsEnc

end BKMNW

end PlanarFlow
