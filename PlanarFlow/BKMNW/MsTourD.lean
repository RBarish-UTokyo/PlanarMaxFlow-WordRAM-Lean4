module

public import PlanarFlow.BKMNW.MsTourC

/-!
# The corner order on the machine, part D: the whole program on arrays

**`fcProg`** `= ftSet ; ftZ ; ftNX ; ftFL ; ftMk ; ftTA ; ftW ; ftS`. **`fcProg_run`** states
what it computes for arbitrary arrays `RV = rv`, `RT = rt` (values `< m`) and path indices
`P = pm`: `NX = rt ∘ rv`, the labels `FL = olab NX + 1`, the flags `LF` of the path darts, the
tour array `TA`, the walk `TR` from `pm 0` with its period in `r8156`, and the selected corners
(`selL`) in `r8157`, `CS`, `CD`, `CN'`, within `fcCost m k = 96 m + 11 k + 60` steps.
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

/-- **The corner order program.** -/
def fcProg : Stmt :=
  .seq ftSet (.seq ftZ (.seq ftNX (.seq ftFL (.seq ftMk (.seq ftTA (.seq ftW ftS))))))

/-- The scratch registers of `fcProg`. -/
def FcScr (r : ℕ) : Prop :=
  (5030 ≤ r ∧ r ≤ 5035) ∨ (6210 ≤ r ∧ r ≤ 6217) ∨ (7350 ≤ r ∧ r ≤ 7352) ∨
    (7400 ≤ r ∧ r ≤ 7405) ∨ (8156 ≤ r ∧ r ≤ 8177)

/-- The step bound of `fcProg`. -/
def fcCost (m k : ℕ) : ℕ := 96 * m + 11 * k + 60

/-- The tour on the indices: `rt (rv i)` (next) on the darts of the path, `rt i` (rotation)
elsewhere. -/
def taF (rv rt pm : ℕ → ℕ) (k : ℕ) (i : ℕ) : ℕ := if mkSet pm rv k i then rt (rv i) else rt i

/-- The labels of the faces. -/
noncomputable def flF (rv rt : ℕ → ℕ) (x : ℕ) : ℕ := olab (fun i => rt (rv i)) x + 1

/-- The labels of the faces along the path: `1` at the label of a dart of the path. -/
noncomputable def fpF (rv rt pm : ℕ → ℕ) (m k : ℕ) (l : ℕ) : ℕ :=
  if ∃ i < m, mkSet pm rv k i ∧ flF rv rt i = l then 1 else 0

/-- **The corner order program on arrays.** -/
theorem fcProg_run (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb S : ℕ}
    (r50 : c.nreg 8150 = m) (r51 : c.nreg 8151 = RVb) (r52 : c.nreg 8152 = RTb)
    (r53 : c.nreg 8153 = k) (r54 : c.nreg 8154 = Pb) (r55 : c.nreg 8155 = S)
    {rv rt pm : ℕ → ℕ} (hk : 0 < k)
    (hrv : ∀ i < m, c.nmem (RVb + i) = rv i ∧ rv i < m)
    (hrt : ∀ i < m, c.nmem (RTb + i) = rt i ∧ rt i < m)
    (hpm : ∀ j < k, c.nmem (Pb + j) = pm j ∧ pm j < m)
    (pNX : PermOn (fun i => rt (rv i)) m) (pTA : PermOn (taF rv rt pm k) m)
    (dRV : RVb + m ≤ S ∨ S + 10 * m ≤ RVb) (dRT : RTb + m ≤ S ∨ S + 10 * m ≤ RTb)
    (dP : Pb + k ≤ S ∨ S + 10 * m ≤ Pb)
    (hW : S + 10 * m + 2 ≤ W) (wRV : RVb + m ≤ W) (wRT : RTb + m ≤ W) (wP : Pb + k ≤ W)
    (wk : k + 1 ≤ W) :
    ∃ c' u per, Exec P W fcProg c c' u ∧ u ≤ fcCost m k ∧
      c'.nreg 8156 = per ∧ 0 < per ∧ per ≤ m ∧ (taF rv rt pm k)^[per] (pm 0) = pm 0 ∧
      (∀ s, 0 < s → s < per → (taF rv rt pm k)^[s] (pm 0) ≠ pm 0) ∧
      (∀ s < per, c'.nmem (S + 6 * m + s) = (taF rv rt pm k)^[s] (pm 0)) ∧
      (∀ i < m, c'.nmem (S + m + i) = flF rv rt i) ∧
      (∀ i < m, c'.nmem (S + 2 * m + i) = if mkSet pm rv k i then 1 else 0) ∧
      (∀ i < m, c'.nmem (S + 5 * m + i) = taF rv rt pm k i) ∧
      c'.nreg 8157 = (selL (fun s => (taF rv rt pm k)^[s] (pm 0)) (flF rv rt)
        (fpF rv rt pm m k) per).length ∧
      (∀ r < (selL (fun s => (taF rv rt pm k)^[s] (pm 0)) (flF rv rt)
          (fpF rv rt pm m k) per).length,
        c'.nmem (S + 8 * m + r) = (selL (fun s => (taF rv rt pm k)^[s] (pm 0)) (flF rv rt)
          (fpF rv rt pm m k) per).getD r 0 ∧
        c'.nmem (S + 7 * m + r) = (taF rv rt pm k)^[(selL (fun s => (taF rv rt pm k)^[s] (pm 0))
          (flF rv rt) (fpF rv rt pm m k) per).getD r 0] (pm 0) ∧
        c'.nmem (S + 9 * m - 1 + flF rv rt ((taF rv rt pm k)^[(selL
          (fun s => (taF rv rt pm k)^[s] (pm 0)) (flF rv rt) (fpF rv rt pm m k) per).getD r 0]
          (pm 0))) = r) ∧
      (∀ a, (a < S ∨ S + 10 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ FcScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set ta := taF rv rt pm k with hta
  have hx0 : pm 0 < m := (hpm 0 hk).2
  have hW9 : S + 9 * m + 2 ≤ W := by omega
  -- set-up
  obtain ⟨c₁, k₁, e₁, hk₁, hR₁, aR, am, ar, arm, ao⟩ :=
    ftSet_exec (P := P) c hc r50 r51 r52 r53 r54 r55 hW9
  -- zero
  obtain ⟨c₂, k₂, e₂, hk₂, bz, bm, bR, br, brm, bo⟩ := ftZ_exec (P := P) c₁ e₁.wb_right hR₁ hW9
  have hR₂ : FtRegs c₂ m RVb RTb k Pb S := hR₁.of fun r h1 h2 _ _ => bR r (by omega)
  have m2 : ∀ a, (a < S + m ∨ S + 5 * m ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [bm a ha, am]
  -- NX
  obtain ⟨c₃, k₃, e₃, hk₃, cv, cm, cR, cr, crm, co⟩ := ftNX_exec (P := P) c₂ e₂.wb_right hR₂
    hW9 (fun i hi => by rw [m2 _ (by omega), (hrv i hi).1]; exact (hrv i hi).2) wRV wRT
    (by omega) (by omega)
  have hR₃ : FtRegs c₃ m RVb RTb k Pb S := hR₂.of fun r h1 h2 _ _ => cR r (by omega)
  have m3 : ∀ a, (a < S ∨ S + 5 * m ≤ a) → c₃.nmem a = c.nmem a := fun a ha => by
    rw [cm a (by omega), m2 a (by omega)]
  have vNX : ∀ i < m, c₃.nmem (S + i) = rt (rv i) := fun i hi => by
    have h1 := (hrv i hi).2
    rw [cv i hi, m2 (RVb + i) (by omega), (hrv i hi).1, m2 (RTb + rv i) (by omega),
      (hrt _ h1).1]
  have z3 : ∀ i < 4 * m, c₃.nmem (S + m + i) = 0 := fun i hi => by
    rw [cm _ (by omega)]; exact bz i hi
  -- FL
  obtain ⟨c₄, k₄, e₄, hk₄, dv, dm, dR, dr, drm, dout⟩ := ftFL_exec (P := P) c₃ e₃.wb_right hR₃
    hW9 pNX vNX (fun i hi => z3 i (by omega))
  have hR₄ : FtRegs c₄ m RVb RTb k Pb S := hR₃.of fun r h1 h2 _ _ => dR r (by omega) (by omega)
  have m4 : ∀ a, (a < S ∨ S + 5 * m ≤ a) → c₄.nmem a = c.nmem a := fun a ha => by
    rw [dm a (by omega), m3 a ha]
  -- the flags of the path
  obtain ⟨c₅, k₅, e₅, hk₅, ev, em, eR, er, erm, eo⟩ := ftMk_exec (P := P) c₄ e₄.wb_right hR₄
    (pm := pm) (rv := rv)
    (fun j hj => by rw [m4 _ (by omega)]; exact hpm j hj)
    (fun i hi => by rw [m4 _ (by omega)]; exact hrv i hi) (by omega) (by omega)
    (fun i hi => by
      rw [dm _ (by omega)]
      have := z3 (m + i) (by omega)
      rwa [show S + m + (m + i) = S + 2 * m + i by omega] at this) wP (by omega) wRV wk
  have hR₅ : FtRegs c₅ m RVb RTb k Pb S := hR₄.of fun r h1 h2 _ _ => eR r (by omega)
  have m5 : ∀ a, (a < S ∨ S + 5 * m ≤ a) → c₅.nmem a = c.nmem a := fun a ha => by
    rw [em a (by omega), m4 a ha]
  -- the tour array
  have lf_pos : ∀ i < m, (0 < (if mkSet pm rv k i then 1 else 0)) ↔ mkSet pm rv k i :=
    fun i _ => by split_ifs with h <;> simp [h]
  obtain ⟨c₆, k₆, e₆, hk₆, fv, ffp, fm, fR, fr, frm, fo⟩ := ftTA_exec (P := P) c₅ e₅.wb_right
    hR₅ (nx := fun i => rt (rv i)) (fl := flF rv rt) (lf := fun i => if mkSet pm rv k i then 1 else 0)
    (rt := rt)
    (fun i hi => by rw [em _ (by omega), dm _ (by omega)]; exact vNX i hi)
    (fun i hi => by rw [em _ (by omega)]; exact dv i hi)
    (fun i hi => ⟨by unfold flF; omega, by have := olab_lt pNX hi; unfold flF; omega⟩)
    ev (fun i hi => by rw [m5 _ (by omega)]; exact (hrt i hi).1) (by omega)
    (fun l h1 h2 => by
      rw [em _ (by omega), dm _ (by omega)]
      have := z3 (2 * m - 1 + l) (by omega)
      rwa [show S + m + (2 * m - 1 + l) = S + 3 * m - 1 + l by omega] at this)
    (by omega) wRT
  have hR₆ : FtRegs c₆ m RVb RTb k Pb S := hR₅.of fun r h1 h2 _ _ => fR r (by omega)
  have vTA : ∀ i < m, c₆.nmem (S + 5 * m + i) = ta i := fun i hi => by
    rw [fv i hi, hta, taF]
    by_cases h : mkSet pm rv k i <;> simp [h]
  -- the walk
  obtain ⟨c₇, k₇, per, e₇, hk₇, g56, gper, gperm, gfix, gmin, gtr, gm, gR, gr, grm, go⟩ :=
    ftW_exec (P := P) c₆ e₆.wb_right hR₆ pTA vTA
      (by rw [fm _ (by omega) (by omega), em _ (by omega), dm _ (by omega), m3 _ (by omega),
        (hpm 0 hk).1.symm, Nat.add_zero]) hx0
      (fun i hi => by
        rw [fm _ (by omega) (by omega), em _ (by omega), dm _ (by omega)]
        have := z3 (3 * m + i) (by omega)
        rwa [show S + m + (3 * m + i) = S + 4 * m + i by omega] at this) hW9
  have hR₇ : FtRegs c₇ m RVb RTb k Pb S := hR₆.of fun r h1 h2 h3 h4 => gR r (by omega) h3
  -- the selection
  obtain ⟨c₈, k₈, e₈, hk₈, s57, sL, sm, sR, sr, srm, so⟩ := ftS_exec (P := P) c₇ e₇.wb_right hR₇
    (tr := fun s => ta^[s] (pm 0)) (fl := flF rv rt) (fp0 := fpF rv rt pm m k) g56 gperm
    (fun s hs => ⟨gtr s hs, OrbLab.iter_lt pTA hx0 s⟩)
    (fun x hx => ⟨by rw [gm _ (by omega) (by omega), fm _ (by omega) (by omega),
        em _ (by omega)]; exact dv x hx,
      by unfold flF; omega, by have := olab_lt pNX hx; unfold flF; omega⟩)
    (fun l h1 h2 => ⟨by
      rw [gm _ (by omega) (by omega), ffp l h1 h2, fpF]
      refine if_congr ?_ rfl rfl
      exact exists_congr fun i => and_congr_right fun _ => and_congr_left fun _ => lf_pos i
        ‹_›, by unfold fpF; split_ifs <;> omega⟩) hW
  refine ⟨c₈, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + k₈)))))), per,
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈)))))), ?_,
    by rw [sR _ (by omega) (by omega), g56], gper, gperm, gfix, gmin,
    fun s hs => by rw [sm _ (by omega) (by omega)]; exact gtr s hs,
    fun i hi => by
      rw [sm _ (by omega) (by omega), gm _ (by omega) (by omega), fm _ (by omega) (by omega),
        em _ (by omega)]; exact dv i hi,
    fun i hi => by
      rw [sm _ (by omega) (by omega), gm _ (by omega) (by omega), fm _ (by omega) (by omega)]
      exact ev i hi,
    fun i hi => by
      rw [sm _ (by omega) (by omega), gm _ (by omega) (by omega)]
      exact vTA i hi,
    s57, sL, fun a ha => ?_, fun r hr => ?_, by rw [sr, gr, fr, er, dr, cr, br, ar],
    by rw [srm, grm, frm, erm, drm, crm, brm, arm], by rw [so, go, fo, eo, dout, co, bo, ao]⟩
  · have : per ≤ m := gperm
    unfold fcCost; omega
  · rw [sm a (by omega) (by omega), gm a (by omega) (by omega), fm a (by omega) (by omega),
      m5 a (by omega)]
  · simp only [FcScr, not_or, not_and, not_le] at hr
    rw [sR r (by omega) (by omega), gR r (by omega) (by omega), fR r (by omega),
      eR r (by omega), dR r (by omega) (by omega), cR r (by omega), bR r (by omega),
      aR r (by omega)]

end MsEnc

end BKMNW

end PlanarFlow
