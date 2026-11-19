module

public import PlanarFlow.BKMNW.NcHdA

/-!
# The head of `c2sP`, stage E: the flags of the sink

The sink of `c2s`/`s2c` on the hole `i` of the part `j` is the `i`-th of
`sHoles (pholes …) (segsP …) j`: a hole of the piece map when `i < #pholes`, otherwise the later
part `j + 1 + (i − #pholes)`. **`hdHF`** runs `hfP` (which also counts the holes of the piece map,
`r9780 = #pholes`), then, when `i ≥ #pholes`, `tfP` on that part:

`hdHF = hfGl ; hfP ; if i < r9780 then skip else (jjGl ; tfGl 9872 9847 9848 ; tfP)`.

**`hdHF_exec`**: the flags `flagX (pmap h) (layEn …) H` at `b + 22 m + 10`.
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

/-- **The flags of the sink.** -/
def hdHF : Stmt :=
  .seq hfGl (.seq hfP (.ifLtN 6802 9780 .skip (.seq jjGl (.seq (tfGl 9872 9847 9848) tfP))))

/-- The orbit label depends only on the values of `f` below `m`. -/
lemma olab_congr {f g : ℕ → ℕ} {m : ℕ} (h : PermOn f m) (hfg : ∀ x < m, f x = g x) {i : ℕ}
    (hi : i < m) : olab f i = olab g i := by
  have it : ∀ t, f^[t] i = g^[t] i := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih,
        hfg _ (OrbLab.iter_lt h hi t)]
  obtain ⟨t, ht⟩ := olab_mem f i
  obtain ⟨t', ht'⟩ := olab_mem g i
  have a := olab_min g i t
  have b := olab_min f i t'
  rw [← it t, ht] at a
  rw [it t', ht'] at b
  omega

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **Stage E: the flags of the sink `H` (the hole `i` of the part `j`).** -/
theorem hdHF_exec {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    (h : SCond M l r π Hs σ) {m : ℕ} {en : ℕ → D} {d e b : ℕ} (hm : 0 < m)
    (c : Config) (hc : WordsBounded W c)
    (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem) (hSeg : SegsAt' M en m π e b c)
    (hde : d + fsz m ≤ e) (heb : e ≤ b) (hd : Hs.Pairwise Disjoint)
    {j i : ℕ} {H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))}
    (hH : (sHoles (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs) (segsP h.1 π.segs h.2) j)[i]? =
      some H)
    (r00 : c.nreg 6800 = j) (r02 : c.nreg 6802 = i)
    (r32 : c.nreg 9832 = m) (r35 : c.nreg 9835 = b + m) (r74 : c.nreg 9874 = d + 4 + m)
    (r77 : c.nreg 9877 = d + 4 + 5 * m) (r45 : c.nreg 9845 = b + 19 * m + 9)
    (r46 : c.nreg 9846 = b + 20 * m + 9) (r47 : c.nreg 9847 = b + 21 * m + 9)
    (r48 : c.nreg 9848 = b + 22 * m + 10)
    (hLAB : ∀ i < m, c.nmem (b + m + i) = olab (sgF d m c.nmem) i + 1)
    (w1 : b + 23 * m + 10 ≤ W) :
    ∃ c' k, Exec P W hdHF c c' k ∧
      k ≤ 6 + (hfCost m + (2 + (4 + (25 + (5 * (m + 1) + 15 * m + 9 * m + 25))))) ∧
      (∀ t < m, c'.nmem (b + 22 * m + 10 + t) = flagX (pmap h.1)
        (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm) H t) ∧
      (∀ a, (a < b + 19 * m + 9 ∨ b + 23 * m + 10 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9700 ∨ (9783 ≤ r ∧ r ≤ 9855) ∨ 9874 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hfz : d + 4 + 7 * m ≤ b := by unfold fsz at hde; omega
  have l1 : d + 4 + 5 * m + m ≤ b + 19 * m + 9 := by omega
  have l2 : b + 19 * m + 9 + m ≤ b + 20 * m + 9 := by omega
  have l3 : b + 20 * m + 9 + m ≤ b + 22 * m + 10 := by omega
  have l4 : b + 22 * m + 10 + m ≤ W := by omega
  have l5 : 3 * m + 1 ≤ W := by omega
  obtain ⟨c₁, k₁, e₁, hk₁, a57, a58, a59, a60, a61, a62, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    hfGl_exec (P := P) c hc
  rw [r32] at a57; rw [r77] at a58; rw [r02] at a59; rw [r45] at a60; rw [r46] at a61
  rw [r48] at a62
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, n₂, F₂, f₂, g₂, rr₂, rm₂, o₂⟩ := hfP_exec' (P := P) c₁ e₁.wb_right
    a57 a58 a59 a60 a61 a62 l1 l2 l3 l4 l5
  rw [m₁] at n₂ F₂
  have hnp := pholes_length_hfN (x := (.node l r π, Hs, σ)) hL hd
  rw [← hnp] at n₂
  have q₂ : ∀ r, (r < 9700 ∨ (9783 ≤ r ∧ r ≤ 9855) ∨ 9874 ≤ r) → c₂.nreg r = c.nreg r :=
    fun r hr => by rw [g₂ r (by unfold HfScr; omega), f₁ r (by omega)]
  have mem₂ : ∀ a, (a < b + 19 * m + 9 ∨ b + 23 * m + 10 ≤ a) → c₂.nmem a = c.nmem a :=
    fun a ha => by rw [f₂ a (by omega), m₁]
  set np := (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length with hnpd
  by_cases hi : i < np
  · -- a hole of the piece map
    have hHi : (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs)[i]? = some H := by
      rw [← hH]; unfold sHoles; rw [List.getElem?_append_left hi]
    have hlt : c₂.nreg 6802 < c₂.nreg 9780 := by rw [q₂ 6802 (by omega), r02, n₂]; exact hi
    refine ⟨c₂, k₁ + (k₂ + (0 + 1)), e₁.seq (e₂.seq (.ifLtN_true hlt (.skip e₂.wb_right))),
      by omega, fun t ht => ?_, mem₂, q₂,
      by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
    rw [F₂ t ht]
    exact hfFlag_hole (x := (.node l r π, Hs, σ)) hL h.1 hd hm hHi ht
  · -- a later part
    have hlenL := length_segsP h.1 π.segs h.2
    have hHi : (((segsP h.1 π.segs h.2).drop (j + 1)).map SPath.verts)[i - np]? = some H := by
      rw [← hH]; unfold sHoles
      rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_map, List.getElem?_drop] at hHi
    have hjj : j + 1 + (i - np) < (segsP h.1 π.segs h.2).length := by
      by_contra hc'
      rw [show j + 1 + (i - np) = (j + 1) + (i - np) by rfl,
        List.getElem?_eq_none (by omega)] at hHi
      cases hHi
    rw [List.getElem?_eq_getElem hjj, Option.map_some, Option.some.injEq] at hHi
    have wj : j + 1 + (i - np) ≤ W := by
      have h1 := hc.2 (c.nreg 6807)
      have h2 := hSeg.1.2.1
      rw [length_segsP] at hjj
      omega
    obtain ⟨c₃, k₃, e₃, hk₃, a72, g₃, m₃, rr₃, rm₃, o₃⟩ := jjGl_exec (P := P) c₂ e₂.wb_right
      (j := j) (i := i) (n := np) (by rw [q₂ 6800 (by omega), r00]) (by rw [q₂ 6802 (by omega), r02])
      n₂ wj
    have q₃ : ∀ r, r ≠ 9860 → r ≠ 9872 → r ≠ 9873 →
        (r < 9700 ∨ (9783 ≤ r ∧ r ≤ 9855) ∨ 9874 ≤ r) → c₃.nreg r = c.nreg r :=
      fun r h1 h2 h3 h4 => by rw [g₃ r h1 h2 h3, q₂ r h4]
    have hLAB₃ : ∀ i < m, c₃.nmem (b + m + i) = olab (sgF d m c₃.nmem) i + 1 := fun i hi => by
      rw [m₃, mem₂ _ (by omega)]
      rw [← olab_congr hL.permOn_sg (g := sgF d m c₂.nmem)
        (fun t ht => by unfold sgF; exact (mem₂ _ (by omega)).symm) hi]
      exact hLAB i hi
    have hL₃ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₃.nmem :=
      hL.congr fun a h1 h2 => by rw [m₃]; exact mem₂ a (by omega)
    have hSeg₃ : SegsAt' M en m π e b c₃ := by
      unfold SegsAt' at hSeg ⊢
      rw [q₃ 6807 (by omega) (by omega) (by omega) (by omega)]
      exact hSeg.congr fun a h1 h2 => by rw [m₃]; exact mem₂ a (by omega)
    obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄, g₄, rr₄, rm₄, o₄⟩ := hdTf_exec (P := P) h hm c₃ e₃.wb_right
      hL₃ hSeg₃ hde heb (rj := 9872) (Vr := 9847) (Fr := 9848) (Or.inl (by omega))
      (by omega) (by omega) (by omega) a72
      ((q₃ 9847 (by omega) (by omega) (by omega) (by omega)).trans r47)
      ((q₃ 9848 (by omega) (by omega) (by omega) (by omega)).trans r48) hjj
      ((q₃ 9832 (by omega) (by omega) (by omega) (by omega)).trans r32)
      ((q₃ 9835 (by omega) (by omega) (by omega) (by omega)).trans r35)
      ((q₃ 9874 (by omega) (by omega) (by omega) (by omega)).trans r74)
      hLAB₃ (by omega) (by omega) l4
    have hlt : ¬ c₂.nreg 6802 < c₂.nreg 9780 := by rw [q₂ 6802 (by omega), r02, n₂]; exact hi
    refine ⟨c₄, k₁ + (k₂ + ((k₃ + k₄) + 2)), e₁.seq (e₂.seq (.ifLtN_false hlt (e₃.seq e₄))),
      by omega, fun t ht => ?_,
      fun a ha => ?_, fun r hr => ?_, by rw [rr₄, rr₃, rr₂, rr₁], by rw [rm₄, rm₃, rm₂, rm₁],
      by rw [o₄, o₃, o₂, o₁]⟩
    · rw [v₄ t ht]
      have e1 : layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL₃.en_mem hm =
          layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm := rfl
      rw [e1, hHi]
    · rw [f₄ a (by omega), m₃, mem₂ a ha]
    · rw [g₄ r (by unfold TfGo; omega) (by omega) (by unfold TfScr; omega),
        q₃ r (by omega) (by omega) (by omega) hr]

end NcStep

end BKMNW

end PlanarFlow
