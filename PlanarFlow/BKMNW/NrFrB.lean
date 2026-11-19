module

public import PlanarFlow.BKMNW.NrFrA

/-!
# The core of `retP`/`frmP`, phase B: the flags of the vertices of the part

**`fcB = fF ; cstL ; fG1 ; fG2 ; fG3 ; fH ; mkL ; fI ; lgProg`**: from the parts of the separator
(`SegsOutV` layout at `Gb = r6807`, part `j = r6800`): the marks `MK` (`b + 7m`) of the labels of
the start vertex and of the heads of the darts of the part, and the flags `PV[i] = MK[VL[i]]`
(`b + 8m`).

**`fcB_exec`**: within `14 m + 11 k + 60` steps; memory changed only in `[b + 7m, b + 9m)`;
`r9190 = b + 7m`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv

/-- **Phase B of the core**: the flags of the vertices of the part. -/
def fcB : Stmt :=
  .seq fF (.seq cstL (.seq fG1 (.seq fG2 (.seq fG3 (.seq fH (.seq mkL (.seq fI lgProg)))))))

section Exec

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **Phase B of the core** (see the module docstring). -/
theorem fcB_exec (c : Config) (hc : WordsBounded W c) {d b m Z kfr Gb j s o k L st : ℕ}
    (R : FcR c d b m Z kfr) (r07 : c.nreg 6807 = Gb) (r00 : c.nreg 6800 = j)
    (hs : c.nmem Gb = s) (hjs : j < s) (ho : c.nmem (Gb + 1 + j) = o)
    (hk : c.nmem (Gb + 1 + s + j) = k) (hL : c.nmem (Gb + s) + c.nmem (Gb + s + s) = L)
    (hst : c.nmem (Gb + 1 + 2 * s + L + j) = st) (hstm : st < m) (hok : o + k ≤ L)
    (hD : ∀ l < k, c.nmem (Gb + 1 + 2 * s + o + l) < m)
    (hRV : ∀ i < m, c.nmem (d + 4 + m + i) < m) (hvl : ∀ i < m, c.nmem (b + 3 * m + i) < m)
    (hreg : Gb + 1 + 2 * s + L + s ≤ b) (hdG : d + 4 + 2 * m ≤ Gb) (hA : d + 4 + 7 * m ≤ b)
    (w : b + 40 * m + 10 ≤ W) :
    ∃ c' t, Exec P W fcB c c' t ∧ t ≤ 14 * m + 11 * k + 60 ∧ FcR c' d b m Z kfr ∧
      c'.nreg 9190 = b + 7 * m ∧
      (∀ i < m, c'.nmem (b + 8 * m + i) =
        mkv (c.nmem (b + 3 * m + st))
          (fun l => c.nmem (b + 3 * m + c.nmem (d + 4 + m + c.nmem (Gb + 1 + 2 * s + o + l))))
          k (c.nmem (b + 3 * m + i))) ∧
      (∀ a, (a < b + 7 * m ∨ b + 9 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hsG : s ≤ Gb + s := by omega
  -- `fF ; cstL`: `MK := 0`
  obtain ⟨c₁, t₁, e₁, ht₁, a90, a51, a52, a53, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    fF_exec (P := P) c hc (by rw [R.r89, R.r81]; clear * - w hA; omega)
  simp only [R.r89, R.r81] at a90 a51 a52
  obtain ⟨c₂, t₂, e₂, ht₂, v₂, k₂, f₂, rr₂, rm₂, o₂⟩ := cstL_exec (P := P) c₁ e₁.wb_right
    a51 a52 a53 (by clear * - w hA; omega) (by clear * - w hA; omega)
  have q₂ : ∀ x, (9180 ≤ x ∧ x ≤ 9199) ∨ (6800 ≤ x ∧ x ≤ 6819) → c₂.nreg x = c.nreg x ∨ x = 9190 :=
    fun x hx => by
      by_cases h90 : x = 9190
      · exact Or.inr h90
      · left; rw [f₂ x (by clear * - hx; omega), f₁ x h90 (by clear * - hx; omega)
          (by clear * - hx; omega) (by clear * - hx; omega)]
  have g2 : ∀ x, (9180 ≤ x ∧ x ≤ 9189) ∨ (6800 ≤ x ∧ x ≤ 6819) → c₂.nreg x = c.nreg x :=
    fun x hx => (q₂ x (by clear * - hx; omega)).resolve_right (by clear * - hx; omega)
  have r90₂ : c₂.nreg 9190 = b + 6 * m + m := by rw [f₂ _ (by decide)]; exact a90
  have mem₂ : ∀ a, (a < b + 6 * m + m ∨ b + 6 * m + m + m ≤ a) → c₂.nmem a = c.nmem a :=
    fun a ha => by rw [k₂ a ha, m₁]
  -- `fG1 ; fG2`: the part
  have g07 : c₂.nreg 6807 = Gb := by rw [g2 _ (by decide)]; exact r07
  have g00 : c₂.nreg 6800 = j := by rw [g2 _ (by decide)]; exact r00
  have mG : ∀ a, a < b → c₂.nmem a = c.nmem a := fun a ha => mem₂ a (by clear * - ha; omega)
  obtain ⟨c₃, t₃, e₃, ht₃, b91, b92, b93, b94, b95, b96, b98, b99, f₃, m₃, rr₃, rm₃, o₃⟩ :=
    fG1_exec (P := P) c₂ e₂.wb_right (by rw [g07]; clear * - hreg w hA; omega)
      (by clear * - w hA; omega) (by rw [g07]; clear * - hreg w hA; omega)
      (by rw [g07, g00]; clear * - hreg hjs w hA; omega) (by rw [g07, g00]; clear * - hreg hjs w hA; omega)
      (by rw [g07, mG _ (by clear * - hreg; omega), hs]; clear * - hreg w hA; omega)
      (by rw [g07, g00, mG _ (by clear * - hreg; omega), hs]; clear * - hreg hjs w hA; omega)
      (by rw [g07, g00, mG _ (by clear * - hreg; omega), hs]; clear * - hreg hjs w hA; omega)
      (by rw [g07, mG _ (by clear * - hreg; omega), hs]; clear * - hreg w hA; omega)
  simp only [g07, g00, mG Gb (by clear * - hreg; omega), hs] at b91 b92 b93 b94 b95 b96 b98
  rw [mG _ (by clear * - hreg hjs; omega), ho] at b93
  rw [mG _ (by clear * - hreg hjs; omega), show Gb + 1 + s + j = Gb + 1 + s + j from rfl, hk] at b95
  have mem₃ : c₃.nmem = c₂.nmem := m₃
  obtain ⟨c₄, t₄, e₄, ht₄, g97, g98, g99, f₄, m₄, rr₄, rm₄, o₄⟩ :=
    fG2_exec (P := P) c₃ e₃.wb_right
      (by rw [b96, b93]; clear * - hreg hok w hA; omega) (by rw [b91, b92]; clear * - hreg w hA; omega)
      (by rw [b91, b92]; clear * - hreg w hA; omega) (by rw [b91, b92]; clear * - hreg w hA; omega)
      (by rw [b91, b92]; clear * - hreg w hA; omega)
      (by rw [b91, b92, mem₃, mG _ (by clear * - hreg hjs; omega), mG _ (by clear * - hreg hjs; omega),
        hL]; clear * - hreg w hA; omega)
      (by rw [b91, b92, b96, mem₃, mG _ (by clear * - hreg hjs; omega),
        mG _ (by clear * - hreg hjs; omega), hL]; clear * - hreg w hA; omega)
      (by rw [b91, b92, b96, mem₃, mG _ (by clear * - hreg hjs; omega),
        mG _ (by clear * - hreg hjs; omega), hL, f₃ 6800 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), g00]; clear * - hreg hjs w hA; omega)
      (by rw [b91, b92, b96, mem₃, mG _ (by clear * - hreg hjs; omega),
        mG _ (by clear * - hreg hjs; omega), hL, f₃ 6800 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), g00]; clear * - hreg hjs w hA; omega)
  have r00₃ : c₃.nreg 6800 = j := by
    rw [f₃ 6800 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), g00]
  rw [b96, b93] at g97
  have e1 : c₂.nmem (Gb + s) = c.nmem (Gb + s) := mG _ (by clear * - hreg hjs; omega)
  have e2 : c₂.nmem (Gb + s + s) = c.nmem (Gb + s + s) := mG _ (by clear * - hreg hjs; omega)
  rw [b91, b92, b96, mem₃, e1, e2, hL, r00₃,
    show Gb + 1 + s + s + L + j = Gb + 1 + 2 * s + L + j by clear * -; omega,
    mG _ (by clear * - hreg hjs; omega), hst] at g98
  -- `fG3`: `MK[VL[st]] := 1`
  have K3 : ∀ x, 9180 ≤ x → x ≤ 9190 → c₄.nreg x = c₂.nreg x := fun x h1 h2 => by
    rw [f₄ x (by clear * - h2; omega) (by clear * - h2; omega) (by clear * - h2; omega),
      f₃ x (by clear * - h2; omega) (by clear * - h2; omega) (by clear * - h2; omega)
      (by clear * - h2; omega) (by clear * - h2; omega) (by clear * - h2; omega)
      (by clear * - h2; omega) (by clear * - h2; omega)]
  have r86₄ : c₄.nreg 9186 = b + 3 * m := by rw [K3 _ (by decide) (by decide), g2 _ (by decide)]; exact R.r86
  have r90₄ : c₄.nreg 9190 = b + 6 * m + m := by rw [K3 _ (by decide) (by decide)]; exact r90₂
  have m4 : c₄.nmem = c₂.nmem := by rw [m₄, m₃]
  have vst : c₄.nmem (b + 3 * m + st) = c.nmem (b + 3 * m + st) := by
    rw [m4, mem₂ _ (by clear * - hstm; omega)]
  have hv0 := hvl st hstm
  obtain ⟨c₅, t₅, e₅, ht₅, h98, h99, f₅, m₅, rr₅, rm₅, o₅⟩ :=
    fG3_exec (P := P) c₄ e₄.wb_right (by rw [r86₄, g98]; clear * - hstm w hA; omega)
      (by rw [r86₄, g98]; clear * - hstm w hA; omega)
      (by rw [r90₄, r86₄, g98, vst]; clear * - hv0 w hA; omega) (by clear * - w hA; omega)
      (by rw [r90₄, r86₄, g98, vst]; clear * - hv0 w hA; omega)
  rw [r86₄, g98, vst, r90₄] at m₅
  -- `fH ; mkL`
  obtain ⟨c₆, t₆, e₆, ht₆, i98, i99, i88, i89, i90, i91, i92, f₆, m₆, rr₆, rm₆, o₆⟩ :=
    fH_exec (P := P) c₅ e₅.wb_right (by clear * - w hA; omega)
      (by rw [f₅ _ (by decide) (by decide), K3 _ (by decide) (by decide), g2 _ (by decide), R.r80]; clear * - w hA; omega)
      (by rw [f₅ _ (by decide) (by decide), K3 _ (by decide) (by decide), g2 _ (by decide), R.r80,
        f₅ _ (by decide) (by decide), K3 _ (by decide) (by decide), g2 _ (by decide), R.r81]; clear * - w hA; omega)
  have K5 : ∀ x, 9180 ≤ x → x ≤ 9197 → c₅.nreg x = c₄.nreg x := fun x h1 h2 =>
    f₅ x (by clear * - h2; omega) (by clear * - h2; omega)
  have K5' : ∀ x, 9180 ≤ x → x ≤ 9197 → c₆.nreg x = c₄.nreg x := fun x h1 h2 => by
    rw [f₆ x (by clear * - h2; omega) (by clear * - h2; omega) (by clear * - h2; omega)
      (by clear * - h2; omega) (by clear * - h2; omega) (by clear * - h2; omega)
      (by clear * - h2; omega), K5 x h1 h2]
  rw [K5 _ (by decide) (by decide), f₄ 9195 (by decide) (by decide) (by decide), b95] at i88
  rw [K5 _ (by decide) (by decide), g97] at i89
  rw [K5 _ (by decide) (by decide), K3 _ (by decide) (by decide), g2 _ (by decide), R.r80,
    K5 _ (by decide) (by decide), K3 _ (by decide) (by decide), g2 _ (by decide), R.r81] at i90
  rw [K5 _ (by decide) (by decide), r86₄] at i91
  rw [K5 _ (by decide) (by decide), r90₄] at i92
  have mem₅ : ∀ a, a ≠ b + 6 * m + m + c.nmem (b + 3 * m + st) → c₆.nmem a = c₂.nmem a :=
    fun a ha => by rw [m₆, m₅, upd_other _ _ _ ha, m4]
  have mm : ∀ a, (a < b + 6 * m + m ∨ b + 6 * m + m + m ≤ a) → c₆.nmem a = c.nmem a :=
    fun a ha => by rw [mem₅ a (by clear * - ha hv0; omega), mem₂ a ha]
  have hDm : ∀ l < k, Gb + 1 + 2 * s + o + l < b := fun l hl => by clear * - hl hok hreg; omega
  have rd : ∀ l < k, c₆.nmem (Gb + 1 + s + s + o + l) = c.nmem (Gb + 1 + 2 * s + o + l) :=
    fun l hl => by
      rw [show Gb + 1 + s + s + o + l = Gb + 1 + 2 * s + o + l by clear * -; omega]
      exact mm _ (by have := hDm l hl; clear * - this; omega)
  have rr : ∀ x < m, c₆.nmem (d + 4 + m + x) = c.nmem (d + 4 + m + x) := fun x hx =>
    mm _ (by clear * - hx hA; omega)
  have rv : ∀ x < m, c₆.nmem (b + 3 * m + x) = c.nmem (b + 3 * m + x) := fun x hx =>
    mm _ (by clear * - hx; omega)
  obtain ⟨c₇, t₇, e₇, ht₇, v₇, k₇, f₇, rr₇, rm₇, o₇⟩ := mkL_exec (P := P) c₆ e₆.wb_right
    (m := m) (v₀ := c.nmem (b + 3 * m + st)) i88 i89 i90 i91 i92
    (fun l hl => by
      rw [rd l hl, rr _ (hD l hl), rv _ (hRV _ (hD l hl))]; exact hvl _ (hRV _ (hD l hl)))
    (fun l hl => by have := hDm l hl; clear * - this; omega)
    (fun l hl => by rw [rd l hl]; have := hD l hl; clear * - this hA; omega)
    (fun l hl => by
      rw [rd l hl, rr _ (hD l hl)]; have := hRV _ (hD l hl); clear * - this; omega)
    (fun v hv => by
      rw [m₆, m₅]
      by_cases e : v = c.nmem (b + 3 * m + st)
      · rw [e, upd_same, iteT rfl]
      · rw [upd_other _ _ _ (by clear * - e; omega), iteF e, m4, v₂ v hv])
    (by clear * - hreg hok w hA; omega)
    (fun l hl => by rw [rd l hl]; have := hD l hl; clear * - this hA w; omega)
    (fun l hl => by
      rw [rd l hl, rr _ (hD l hl)]; have := hRV _ (hD l hl); clear * - this w hA; omega)
    (by clear * - w hA; omega) (by clear * - hreg hok w hA; omega)
  have hval7 : ∀ l < k, c₆.nmem (b + 3 * m + c₆.nmem (d + 4 + m + c₆.nmem (Gb + 1 + s + s + o + l))) =
      c.nmem (b + 3 * m + c.nmem (d + 4 + m + c.nmem (Gb + 1 + 2 * s + o + l))) := fun l hl => by
    rw [rd l hl, rr _ (hD l hl), rv _ (hRV _ (hD l hl))]
  have mk7 : ∀ v < m, c₇.nmem (b + 6 * m + m + v) = mkv (c.nmem (b + 3 * m + st))
      (fun l => c.nmem (b + 3 * m + c.nmem (d + 4 + m + c.nmem (Gb + 1 + 2 * s + o + l)))) k v :=
    fun v hv => by
      rw [v₇ v hv]; unfold mkv
      congr 1; apply propext
      apply or_congr Iff.rfl
      constructor
      · rintro ⟨l', hl', e⟩; exact ⟨l', hl', (hval7 l' hl').symm.trans e⟩
      · rintro ⟨l', hl', e⟩; exact ⟨l', hl', (hval7 l' hl').trans e⟩
  -- `fI ; lgProg`: `PV[i] = MK[VL[i]]`
  obtain ⟨c₈, t₈, e₈, ht₈, j10, j11, j12, j13, f₈, m₈, rr₈, rm₈, o₈⟩ := fI_exec (P := P) c₇
    e₇.wb_right (by rw [f₇ _ (by decide), K5' 9190 (by decide) (by decide), r90₄, f₇ _ (by decide), K5' 9181 (by decide) (by decide),
      K3 _ (by decide) (by decide), g2 _ (by decide), R.r81]; clear * - w hA; omega)
  have K7 : ∀ x, 9180 ≤ x → x ≤ 9197 → c₇.nreg x = c₄.nreg x := fun x h1 h2 => by
    rw [f₇ x (by clear * - h2; omega), K5' x h1 h2]
  have r81₇ : c₇.nreg 9181 = m := by
    rw [K7 _ (by decide) (by decide), K3 _ (by decide) (by decide), g2 _ (by decide), R.r81]
  have r86₇ : c₇.nreg 9186 = b + 3 * m := by rw [K7 _ (by decide) (by decide), r86₄]
  have r90₇ : c₇.nreg 9190 = b + 6 * m + m := by rw [K7 _ (by decide) (by decide), r90₄]
  rw [r81₇] at j10; rw [r86₇] at j11; rw [r90₇] at j12; rw [r90₇, r81₇] at j13
  have vl₈ : ∀ i < m, c₈.nmem (b + 3 * m + i) = c.nmem (b + 3 * m + i) := fun i hi => by
    rw [m₈, k₇ _ (by clear * - hi; omega), rv i hi]
  obtain ⟨c₉, t₉, e₉, ht₉, v₉, k₉, f₉, rr₉, rm₉, o₉⟩ := lgProg_exec (P := P) c₈ e₈.wb_right
    j10 j11 j12 j13 (by clear * - w hA; omega) (by clear * - w hA; omega) (by clear * - w hA; omega)
    (fun i hi => by rw [vl₈ i hi]; have := hvl i hi; clear * - this w hA; omega)
    (fun i hi => by clear * - hi; omega)
    (fun i hi => by rw [vl₈ i hi]; have := hvl i hi; clear * - this; omega)
  have K9 : ∀ x, 9180 ≤ x → x ≤ 9197 → c₉.nreg x = c₄.nreg x := fun x h1 h2 => by
    rw [f₉ x (by clear * - h1; omega), f₈ x (by clear * - h1; omega) (by clear * - h1; omega)
      (by clear * - h1; omega) (by clear * - h1; omega), K7 x h1 h2]
  have hR : FcR c₉ d b m Z kfr := R.congr fun x h1 h2 => by
    rw [K9 x h1 (by clear * - h2; omega), K3 x h1 (by clear * - h2; omega),
      g2 x (by clear * - h1 h2; omega)]
  refine ⟨c₉, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + (t₈ + t₉))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉))))))),
    by clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ ht₇ ht₈ ht₉; omega, hR,
    by rw [K9 _ (by decide) (by decide), r90₄]; clear * -; omega, fun i hi => ?_, fun a ha => ?_,
    by rw [rr₉, rr₈, rr₇, rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₉, rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₉, o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · rw [show b + 8 * m + i = b + 6 * m + m + m + i by clear * -; omega, v₉ i hi, vl₈ i hi, m₈]
    exact mk7 _ (hvl i hi)
  · rw [k₉ a (by clear * - ha; omega), m₈, k₇ a (by clear * - ha; omega)]
    exact mm a (by clear * - ha; omega)

end Exec

end BKMNW

end PlanarFlow
