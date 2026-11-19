module

public import PlanarFlow.NegSSSP.NodeRunB

/-!
# The run of one part of a node

`part_exec`: the run of `NegSSSP.partProg` (see `PlanarFlow/NegSSSP/NodeRunB.lean`) on a node in
the plain encoding held above the work space computes, for the part `s`, the data of `minProg`
(`NegSSSP.minIn_of_run`) of the call `dijk` of `NegSSSP.step` with the boundary values `E`
lowered by the value `C` read from the slot `21`, within
`cNegMach.dij (w + 1) (m + w) + 100 m + 200 w + 20 b + 1300` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Monge.FR BKMNW

section Node

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

theorem dij_mono (C x p p' : ℕ) (h : p ≤ p') : (cNegMach C).dij x p ≤ (cNegMach C).dij x p' := by
  simp only [cNegMach]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))

set_option maxHeartbeats 4000000 in
/-- **The run of one part of a node** (see the module docstring of
`PlanarFlow/NegSSSP/NodeRunB.lean` for the layout). -/
theorem part_exec (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr) {P₀ P₁ : Finset D}
    {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} (h : NodeEnc N P₀ P₁ m w e ν ι)
    {β : ℕ → V} (hβ : IsEnum b β (bdry N P₀ P₁)) {s : ℕ} (hs : s ≤ 1)
    (hXn : (partOf P₀ P₁ s).Nonempty) (ℓ : D → ℤ) (E δ : V → ℤ) (Cz : ℤ)
    (hδ : (pg N (partOf P₀ P₁ s) ℓ).IsPot δ)
    {Z M₀ δb Fs Vs W' : ℕ} (hM₀ : M₀ = m + w + 1) (hZ : loB m w ≤ Z) (hW : Z + 22 * M₀ ≤ W')
    (hδb : δb = Z + 4 * M₀ ∨ δb = Z + 5 * M₀)
    (hFs : Z + 16 * M₀ ≤ Fs) (hFs' : Fs + M₀ ≤ Z + 21 * M₀)
    (hVs : Z + 16 * M₀ ≤ Vs) (hVs' : Vs + M₀ ≤ Z + 21 * M₀)
    (I : Input) (c : Config) (hc : WordsBounded W' c) (hctx : NCtx m w b Z M₀ c)
    (h830 : c.nreg 830 = s) (h831 : c.nreg 831 = δb) (h832 : c.nreg 832 = Fs)
    (h833 : c.nreg 833 = Vs)
    (hTm : ∀ d < m, c.nmem (Z + 0 * M₀ + d) = encT N e ν d)
    (hHm : ∀ d < m, c.nmem (Z + 1 * M₀ + d) = encH N e ν d)
    (hSm : ∀ d < m, c.nmem (Z + 2 * M₀ + d) = encS P₀ e d)
    (hLm : ∀ d < m, c.rmem (Z + 3 * M₀ + d) = ℓ (e d))
    (hDm : ∀ v < w, c.rmem (δb + v) = δ (ι v))
    (hNm : ∀ i < b, c.nmem (Z + 6 * M₀ + i) = ν (β i))
    (hEm : ∀ i < b, c.rmem (Z + 7 * M₀ + i) = E (β i))
    (hCm : c.rmem (Z + 21 * M₀) = Cz) :
    ∃ c' k, Exec I W' partProg c c' k ∧
      k ≤ (cNegMach C).dij (w + 1) (m + w) + 100 * m + 200 * w + 20 * b + 1300 ∧
      (∀ v < w, c'.nmem (Fs + v) = if (oNum N P₀ P₁ ν ι (dijk N fr (partOf P₀ P₁ s) ℓ
        (bdry N P₀ P₁) (fun y => E y - Cz) δ) v).isSome then 1 else 0) ∧
      (∀ v < w, ∀ z, oNum N P₀ P₁ ν ι (dijk N fr (partOf P₀ P₁ s) ℓ (bdry N P₀ P₁)
        (fun y => E y - Cz) δ) v = some z → c'.rmem (Vs + v) = z) ∧
      (∀ r, 800 ≤ r → r < 900 → c'.nreg r = c.nreg r) ∧
      (∀ a, Z ≤ a → (a < Z + 9 * M₀ ∨ Z + 16 * M₀ ≤ a) → (a < Fs ∨ Fs + w ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ a, Z ≤ a → (a < Z + 8 * M₀ ∨ Z + 16 * M₀ ≤ a) → (a < Vs ∨ Vs + w ≤ a) →
        c'.rmem a = c.rmem a) ∧
      c'.output = c.output := by
  classical
  have hA : loB m w = 4 * m + 18 * w + 175 := rfl
  have hbw : b ≤ w := by rw [hβ.card]; exact card_bdry_le h
  have hends := enc_ends h
  have hnlt : ∀ i < b, ν (β i) < w := fun i hi => h.lt _ (bdry_sub_verts (hβ.mem i hi))
  have hninj : ∀ i < b, ∀ j < b, ν (β i) = ν (β j) → i = j := fun i hi j hj hij =>
    hβ.inj i hi j hj (by rw [← h.inv _ (bdry_sub_verts (hβ.mem i hi)), hij,
      h.inv _ (bdry_sub_verts (hβ.mem j hj))])
  have HS : SlotH m w b Z M₀ W' := ⟨hM₀, hZ, hW, hbw⟩
  have sl : ∀ k < 22, ∀ c' : Config, (∀ r, 800 ≤ r → r < 900 → c'.nreg r = c.nreg r) →
      c'.nreg (803 + k) = Z + k * M₀ := fun k hk c' hr =>
    (hr (803 + k) (by pomega) (by pomega)).trans (hctx.slot k hk)
  -- 1. the bound of the clearing
  obtain ⟨c₁, k₁, e₁, hk₁, r900₁, hn₁, hrr₁, hnm₁, hrm₁, ho₁⟩ := clrSet_exec (P := I) c hc
  have hR₁ : ∀ r, 800 ≤ r → r < 900 → c₁.nreg r = c.nreg r := fun r _ _ => hn₁ r (by pomega)
  -- 2. the clearing
  obtain ⟨c₂, k₂, e₂, hk₂, z₂, hkp₂, hn₂, hrr₂, hrm₂, ho₂⟩ := clrProg_exec (P := I)
    (L := loB m w) (by pomega) c₁ e₁.wb_right (by rw [r900₁, hctx.r825])
  have hR₂ : ∀ r, 800 ≤ r → r < 900 → c₂.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₂ r (by pomega)).trans (hR₁ r h1 h2)
  have hm₂ : ∀ a, loB m w ≤ a → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hkp₂ a ha, hnm₁]
  -- 3., 4. the initial lengths and the prices
  obtain ⟨c₃, k₃, e₃, hk₃, p500, p501, p502, p505, p506, p507, p508, pC, hn₃, hnm₃, hrm₃, ho₃⟩ :=
    pSet_exec (P := I) c₂ e₂.wb_right (by pomega)
  have hR₃ : ∀ r, 800 ≤ r → r < 900 → c₃.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₃ r (by pomega) (by pomega)).trans (hR₂ r h1 h2)
  have hrm₃' : c₃.rmem = c.rmem := by rw [hrm₃, hrm₂, hrm₁]
  have hPL : PLay b w (Z + 7 * M₀) (Z + 6 * M₀) δb (Z + 8 * M₀) 1 W' (fun i => ν (β i)) :=
    pLay_slot HS hδb hnlt hninj
  have hPI : PIn b w (Z + 7 * M₀) (Z + 6 * M₀) δb (Z + 8 * M₀) 1 (fun i => ν (β i))
      (fun i => (E (β i) : ℝ)) (fun v => (δ (ι v) : ℝ)) (Cz : ℝ) c₃ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, p508, ?_, fun i hi => ?_, fun i hi => ?_, fun v hv => ?_⟩
    · rw [p500, hR₂ 802 (by pomega) (by pomega), hctx.r802]
    · rw [p501, sl 7 (by pomega) c₂ hR₂]
    · rw [p502, sl 6 (by pomega) c₂ hR₂]
    · rw [p505, hR₂ 801 (by pomega) (by pomega), hctx.r801]
    · rw [p506, hR₂ 831 (by pomega) (by pomega), h831]
    · rw [p507, sl 8 (by pomega) c₂ hR₂]
    · rw [pC, sl 21 (by pomega) c₂ hR₂, hrm₂, hrm₁, hCm]
    · rw [hnm₃, hm₂ _ (by pomega)]; exact hNm i hi
    · rw [hrm₃']; exact hEm i hi
    · rw [hrm₃']; exact hDm v hv
  obtain ⟨c₄, k₄, e₄, hk₄, q1, q2, q3, q4, hrm₄, hnm₄, hn₄, ho₄⟩ :=
    pProg_exec (P := I) hPL c₃ e₃.wb_right hPI
  have hR₄ : ∀ r, 800 ≤ r → r < 900 → c₄.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₄ r (by pomega)).trans (hR₃ r h1 h2)
  -- 5., 6. the candidate arcs
  obtain ⟨c₅, k₅, e₅, hk₅, a700, a701, a702, a703, a704, a705, a706, a707, a708, a709, a710,
    a711, hn₅, hrr₅, hnm₅, hrm₅, ho₅⟩ := aSet_exec (P := I) c₄ e₄.wb_right
  have hR₅ : ∀ r, 800 ≤ r → r < 900 → c₅.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₅ r (by pomega)).trans (hR₄ r h1 h2)
  have hAL : ALay m w s (Z + 0 * M₀) (Z + 1 * M₀) (Z + 2 * M₀) (Z + 3 * M₀) (Z + 8 * M₀)
      (Z + 9 * M₀) (Z + 10 * M₀) (Z + 11 * M₀) (Z + 12 * M₀) W' (encT N e ν) (encH N e ν)
      (encS P₀ e) := aLay_slot HS hends hs
  have hm₄ : ∀ a, Z ≤ a → c₄.nmem a = c.nmem a := fun a ha => by
    rw [hnm₄, hnm₃, hm₂ a (by pomega)]
  have hAI : AIn m w s (Z + 0 * M₀) (Z + 1 * M₀) (Z + 2 * M₀) (Z + 3 * M₀) (Z + 8 * M₀)
      (Z + 9 * M₀) (Z + 10 * M₀) (Z + 11 * M₀) (Z + 12 * M₀) (encT N e ν) (encH N e ν)
      (encS P₀ e) (fun d => (ℓ (e d) : ℝ)) (fun v => c₄.rmem (Z + 8 * M₀ + v)) c₅ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun d hd => ?_, fun d hd => ?_,
      fun d hd => ?_, fun d hd => ?_, fun v hv => ?_⟩
    · rw [a700, hR₄ 800 (by pomega) (by pomega), hctx.r800]
    · rw [a701, hR₄ 801 (by pomega) (by pomega), hctx.r801]
    · rw [a702, sl 0 (by pomega) c₄ hR₄]
    · rw [a703, sl 1 (by pomega) c₄ hR₄]
    · rw [a704, sl 2 (by pomega) c₄ hR₄]
    · rw [a705, sl 3 (by pomega) c₄ hR₄]
    · rw [a706, sl 8 (by pomega) c₄ hR₄]
    · rw [a707, sl 9 (by pomega) c₄ hR₄]
    · rw [a708, sl 10 (by pomega) c₄ hR₄]
    · rw [a709, sl 11 (by pomega) c₄ hR₄]
    · rw [a710, sl 12 (by pomega) c₄ hR₄]
    · rw [a711, hR₄ 830 (by pomega) (by pomega), h830]
    · rw [hnm₅, hm₄ _ (by pomega)]; exact hTm d hd
    · rw [hnm₅, hm₄ _ (by pomega)]; exact hHm d hd
    · rw [hnm₅, hm₄ _ (by pomega)]; exact hSm d hd
    · rw [hrm₅, hrm₄ _ (Or.inl (by pomega)) (Or.inr (by pomega)), hrm₃']; exact hLm d hd
    · rw [hrm₅]
  obtain ⟨c₆, k₆, e₆, hk₆, hd₆, hv₆, hnm₆, hrm₆, hn₆, hrr₆, ho₆⟩ :=
    aProg_exec (P := I) hAL c₅ e₅.wb_right hAI
  have hR₆ : ∀ r, 800 ≤ r → r < 900 → c₆.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₆ r (by pomega)).trans (hR₅ r h1 h2)
  -- the candidate arcs as written
  have hd₆' : ∀ i < m, c₆.nmem (Z + 9 * M₀ + i) = encT N e ν i + 1 ∧
      c₆.nmem (Z + 10 * M₀ + i) = encH N e ν i + 1 ∧
      (c₆.nmem (Z + 11 * M₀ + i) ≠ 0 ↔ encS P₀ e i = s) := fun i hi =>
    ⟨(hd₆ i hi).1, (hd₆ i hi).2.1, by rw [(hd₆ i hi).2.2.1]; exact flag_ne_zero (hends i hi).2.2 hs⟩
  obtain ⟨hEs, hEs', hhd⟩ := arcs_part h hs ℓ (bdry N P₀ P₁) (fun y => E y - Cz) δ
    (fun i => c₆.nmem (Z + 9 * M₀ + i)) (fun i => c₆.nmem (Z + 10 * M₀ + i))
    (fun i => c₆.nmem (Z + 11 * M₀ + i)) hd₆' (fun v hv => ⟨(hv₆ v hv).1, (hv₆ v hv).2.1,
      (hv₆ v hv).2.2.1⟩)
  have htl : ∀ i < m + w, c₆.nmem (Z + 9 * M₀ + i) < w + 1 := by
    intro i hi
    by_cases him : i < m
    · rw [(hd₆ i him).1]; have := (hends i him).1; pomega
    · obtain ⟨v, rfl⟩ : ∃ v, i = m + v := ⟨i - m, by pomega⟩
      rw [(hv₆ v (by pomega)).1]; pomega
  -- the lengths of the candidate arcs
  have hlz : ∀ i < m + w, c₆.rmem (Z + 12 * M₀ + i) =
      (lzF N P₀ P₁ m e ν ι ℓ (bdry N P₀ P₁) (fun y => E y - Cz) δ i : ℝ) := by
    intro i hi
    by_cases him : i < m
    · rw [(hd₆ i him).2.2.2]; unfold lzF; rw [ite_eq_left_of_eq_true _ _ (eq_true him)]
    · obtain ⟨v, rfl⟩ : ∃ v, i = m + v := ⟨i - m, by pomega⟩
      rw [(hv₆ v (by pomega)).2.2.2]
      refine lzF_init h hβ ℓ E δ Cz (fun v => c₄.rmem (Z + 8 * M₀ + v)) (fun j hj => ?_)
        (fun v hv hv' => q2 v hv hv') (by pomega)
      rw [q1 j hj]
  -- 7., 8. the counting sort
  obtain ⟨c₇, k₇, e₇, hk₇, s400, s401, s402, s403, s404, s405, s406, s407, s408, s409, hn₇, hrr₇,
    hnm₇, hrm₇, ho₇⟩ := csSet_exec (P := I) c₆ e₆.wb_right
      (by rw [hR₆ 800 (by pomega) (by pomega), hR₆ 801 (by pomega) (by pomega), hctx.r800,
        hctx.r801]; pomega)
      (by rw [hR₆ 801 (by pomega) (by pomega), hctx.r801]; pomega)
  have hR₇ : ∀ r, 800 ≤ r → r < 900 → c₇.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₇ r (by pomega) (by pomega)).trans (hR₆ r h1 h2)
  have e801₆ : c₆.nreg 801 = w := by rw [hR₆ 801 (by pomega) (by pomega), hctx.r801]
  have hCL : CsLay (m + w) (w + 1) (Z + 9 * M₀) (Z + 10 * M₀) (Z + 11 * M₀) (w + 2)
      (Z + 13 * M₀) (Z + 15 * M₀) (Z + 12 * M₀) (Z + 14 * M₀) W'
      (fun i => c₆.nmem (Z + 9 * M₀ + i)) (fun i => c₆.nmem (Z + 10 * M₀ + i))
      (fun i => c₆.nmem (Z + 11 * M₀ + i)) := csLay_slot HS fun i hi _ => htl i hi
  have hCI : CsIn (m + w) (w + 1) (Z + 9 * M₀) (Z + 10 * M₀) (Z + 11 * M₀) (w + 2)
      (Z + 13 * M₀) (Z + 15 * M₀) (Z + 12 * M₀) (Z + 14 * M₀)
      (fun i => c₆.nmem (Z + 9 * M₀ + i)) (fun i => c₆.nmem (Z + 10 * M₀ + i))
      (fun i => c₆.nmem (Z + 11 * M₀ + i))
      (lzF N P₀ P₁ m e ν ι ℓ (bdry N P₀ P₁) (fun y => E y - Cz) δ) c₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i _ => by rw [hnm₇],
      fun i _ => by rw [hnm₇], fun i _ => by rw [hnm₇], fun i hi => by rw [hrm₇]; exact hlz i hi⟩
    · rw [s400, hR₆ 800 (by pomega) (by pomega), hctx.r800, e801₆]
    · rw [s401, e801₆]
    · rw [s402, sl 9 (by pomega) c₆ hR₆]
    · rw [s403, sl 10 (by pomega) c₆ hR₆]
    · rw [s404, sl 11 (by pomega) c₆ hR₆]
    · rw [s405, e801₆]
    · rw [s406, sl 13 (by pomega) c₆ hR₆]
    · rw [s407, sl 15 (by pomega) c₆ hR₆]
    · rw [s408, sl 12 (by pomega) c₆ hR₆]
    · rw [s409, sl 14 (by pomega) c₆ hR₆]
  obtain ⟨c₈, k₈, e₈, hk₈, hoff₈, harc₈, hnm₈, hrm₈, hn₈, hrr₈, ho₈⟩ :=
    csProg_exec (P := I) hCL c₇ e₇.wb_right hCI
  have hR₈ : ∀ r, 800 ≤ r → r < 900 → c₈.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₈ r (by pomega)).trans (hR₇ r h1 h2)
  generalize hEsdef : csList (fun i => c₆.nmem (Z + 9 * M₀ + i))
    (fun i => c₆.nmem (Z + 10 * M₀ + i)) (fun i => c₆.nmem (Z + 11 * M₀ + i))
    (lzF N P₀ P₁ m e ν ι ℓ (bdry N P₀ P₁) (fun y => E y - Cz) δ) (m + w) = Es
    at hEs hEs' hhd hoff₈ harc₈
  have hm'E : (arcList (w + 1) Es).length = Es.length := by
    rw [← hEsdef]; exact length_arcList_csList fun i hi _ => htl i hi
  have hEl : Es.length ≤ m + w := by rw [← hEsdef]; exact length_csList_le _
  generalize hm'def : (arcList (w + 1) Es).length = m' at harc₈ hm'E
  have hoffN : c₈.nmem (2 * w + 3) = m' := by
    have := hoff₈ (w + 1) le_rfl
    rw [show w + 2 + (w + 1) = 2 * w + 3 by pomega] at this
    rw [this, ← hm'def]; rfl
  -- 9., 10. the copy into the layout of `mkPrm`
  have e801₈ : c₈.nreg 801 = w := by rw [hR₈ 801 (by pomega) (by pomega), hctx.r801]
  obtain ⟨c₉, k₉, e₉, hk₉, t940, t941, t942, t943, t910, t911, t912, t913, t914, hn₉, hrr₉,
    hnm₉, hrm₉, ho₉⟩ := cpSet_exec (P := I) c₈ e₈.wb_right (by rw [e801₈, hoffN]; pomega)
  rw [e801₈, hoffN] at t942 t943 t910 t913
  rw [e801₈] at t940 t941 t911
  have hR₉ : ∀ r, 800 ≤ r → r < 900 → c₉.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₉ r h2).trans (hR₈ r h1 h2)
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, hcp, hnm₁₀, hrm₁₀, hn₁₀, hrr₁₀, ho₁₀⟩ :=
    cpyProg_exec (P := I) (n := m') (Dn := 2 * w + 4) (Sn := Z + 14 * M₀)
      (Dr := 2 * w + 4 + m') (Sr := Z + 15 * M₀)
      (cpyLay_slot HS (by pomega)) c₉ e₉.wb_right
      t910 t911 (by rw [t912, sl 14 (by pomega) c₈ hR₈]) t913
      (by rw [t914, sl 15 (by pomega) c₈ hR₈])
  have hR₁₀ : ∀ r, 800 ≤ r → r < 900 → c₁₀.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₁₀ r (by pomega)).trans (hR₉ r h1 h2)
  -- 11., 12. the registers of `frProg`
  obtain ⟨c₁₁, k₁₁, e₁₁, hk₁₁, hn₁₁, hrr₁₁, hnm₁₁, hrm₁₁, ho₁₁⟩ :=
    zeroRegs_exec (P := I) lowRegs c₁₀ e₁₀.wb_right
  have hk₁₁' : k₁₁ = 372 := by rw [hk₁₁, lowRegs, List.length_range]
  clear hk₁₁
  have hn₁₁' : ∀ r, 372 ≤ r → c₁₁.nreg r = c₁₀.nreg r := fun r hr => by
    rw [hn₁₁ r, ite_eq_right_of_eq_false _ _ (eq_false fun h' => by
      have := mem_lowRegs.1 h'; pomega)]
  have v940 : c₁₁.nreg 940 = w + 1 := by rw [hn₁₁' _ (by pomega), hn₁₀ _ (by pomega), t940]
  have v941 : c₁₁.nreg 941 = w + 2 := by rw [hn₁₁' _ (by pomega), hn₁₀ _ (by pomega), t941]
  have v942 : c₁₁.nreg 942 = m' := by rw [hn₁₁' _ (by pomega), hn₁₀ _ (by pomega), t942]
  have v943 : c₁₁.nreg 943 = 2 * w + 4 + m' := by
    rw [hn₁₁' _ (by pomega), hn₁₀ _ (by pomega), t943]
  have hR₁₁ : ∀ r, 800 ≤ r → r < 900 → c₁₁.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₁₁' r (by pomega)).trans (hR₁₀ r h1 h2)
  obtain ⟨c₁₂, k₁₂, e₁₂, hk₁₂, u944, u945, u946, u100, u101, u102, u103, u104, u105, u106, u107,
    u108, u109, hn₁₂, hnm₁₂, hrm0₁₂, hrm₁₂, ho₁₂⟩ := inpBlk_exec (P := I) c₁₁ e₁₁.wb_right
      (by rw [v940, v942, v943]; pomega) (by pomega)
  simp only [v943, v942, v940, v941] at u944 u945 u946 u107 u108 u109 u105 u100 u104
  have hR₁₂ : ∀ r, 800 ≤ r → r < 900 → c₁₂.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₁₂ r (by pomega) (by pomega)).trans (hR₁₁ r h1 h2)
  -- 13. FR-Dijkstra
  set pf : ℕ → ℤ := fun x => if x = 0 then price (bdry N P₀ P₁) (fun y => E y - Cz) δ none
    else δ (ι (x - 1)) with hpf
  obtain ⟨hPW, hPlb, hPpb, hPob, hPsb, hPdb, hPwb⟩ := mkPrm_one (w + 1) (fun _ _ => 0) pf 0 Es
  rw [hm'def] at hPW hPlb hPsb hPdb hPwb
  have hPN : (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es).N = w + 1 := rfl
  have hPm : (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es).m = m' := hm'def
  have hin : Inp (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es) c₁₂ :=
    ⟨u100, u101, u102, by rw [u103, hPpb], by rw [u104, hPob], by rw [u105, hPlb]; pomega, u106,
      by rw [u107, hPsb]; pomega, by rw [u108, hPdb]; pomega, by rw [u109, hPwb]; pomega⟩
  have hrlow : ∀ a, a < 2 * w + 4 → c₁₂.rmem a = c₄.rmem a ∨ a = 0 := by
    intro a ha
    by_cases h0 : a = 0
    · exact Or.inr h0
    · left
      rw [hrm₁₂ a h0, hrm₁₁, hrm₁₀ a (Or.inl (by pomega)), hrm₉, hrm₈ a (Or.inl (by pomega)), hrm₇,
        hrm₆ a (Or.inl (by pomega)), hrm₅]
  have hDa : Data (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es) c₁₂ := by
    refine ⟨fun i j hi hj => ?_, fun x hx => ?_, fun x hx => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · have hb1 : (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es).b = 1 := rfl
      obtain rfl : i = 0 := by pomega
      obtain rfl : j = 0 := by pomega
      show c₁₂.rmem (0 + 0 * 1 + 0) = ((0 : ℤ) : ℝ)
      simp [hrm0₁₂]
    · rw [hPN] at hx
      rw [hPpb]
      rcases hrlow (1 + x) (by pomega) with h' | h'
      · rw [h']
        show c₄.rmem (1 + x) = ((pf x : ℤ) : ℝ)
        rcases Nat.eq_zero_or_pos x with rfl | hx0
        · rw [Nat.add_zero, q4]
          simp only [hpf, ↓reduceIte]
          rw [← (arith_node h hβ E δ δ δ Cz (fun v => c₄.rmem (Z + 8 * M₀ + v))
            (fun j hj => by rw [q1 j hj]) (fun v hv hv' => q2 v hv hv')).2.1]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [h.inv _ (bdry_sub_verts (hβ.mem i (Finset.mem_range.1 hi)))]
        · obtain ⟨v, rfl⟩ : ∃ v, x = v + 1 := ⟨x - 1, by pomega⟩
          rw [q3 v (by pomega)]
          simp only [hpf, Nat.add_sub_cancel, Nat.add_one_ne_zero, ↓reduceIte]
      · pomega
    · rw [hPob]
      rw [hnm₁₂, hnm₁₁, hnm₁₀ _ (Or.inl (by pomega)), hnm₉,
        show w + 1 + 1 + x = w + 2 + x by pomega]
      exact hoff₈ x hx
    · rw [hPm] at ht
      rw [hPob, hPN]
      rw [hnm₁₂, hnm₁₁, show w + 1 + 1 + (w + 1) + 1 + t = 2 * w + 4 + t by pomega,
        (hcp t ht).1, hnm₉, (harc₈ t ht).1]
      rfl
    · rw [hPm] at ht
      rw [hPlb, hrm₁₂ _ (by pomega), hrm₁₁, show 2 * (w + 1) + 2 + m' + t = 2 * w + 4 + m' + t by pomega,
        (hcp t ht).2, hrm₉, (harc₈ t ht).2]
      rfl
  have hrb : ∀ r < 372, c₁₂.nreg r ≤ (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es).W := by
    intro r hr
    by_cases h1 : r < 100 ∨ 109 < r
    · rw [hn₁₂ r h1 (by pomega), hn₁₁ r, ite_eq_left_of_eq_true _ _ (eq_true (mem_lowRegs.2 hr))]
      pomega
    · rw [hPW]
      obtain ⟨h1, h2⟩ : 100 ≤ r ∧ r ≤ 109 := by pomega
      interval_cases r <;> simp only [u100, u101, u102, u103, u104, u105, u106, u107, u108, u109] <;>
        pomega
  have hmb : ∀ a ≤ (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es).W,
      c₁₂.nmem a ≤ (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es).W := by
    intro a ha
    rw [hPW] at ha ⊢
    rw [hnm₁₂, hnm₁₁]
    by_cases hD : 2 * w + 4 ≤ a ∧ a < 2 * w + 4 + m'
    · obtain ⟨t, rfl⟩ : ∃ t, a = 2 * w + 4 + t := ⟨a - (2 * w + 4), by pomega⟩
      have ht : t < m' := by pomega
      rw [(hcp t ht).1, hnm₉, (harc₈ t ht).1]
      have hmem : (arcList (w + 1) Es).getD t (0, 0, 0) ∈ Es := by
        have ht' : t < (arcList (w + 1) Es).length := by rw [hm'def]; exact ht
        rw [List.getD_eq_getElem _ _ ht']
        exact (mem_arcList.1 (List.getElem_mem ht')).1
      have := hhd _ hmem
      pomega
    · rw [hnm₁₀ a (by pomega), hnm₉]
      by_cases hO : w + 2 ≤ a ∧ a < w + 2 + (w + 1) + 1
      · obtain ⟨x, rfl⟩ : ∃ x, a = w + 2 + x := ⟨a - (w + 2), by pomega⟩
        rw [hoff₈ x (by pomega)]
        have := length_pre_le Es x
        pomega
      · rw [hnm₈ a (by pomega) (Or.inl (by pomega)) (Or.inl (by pomega)), hnm₇,
          hnm₆ a (Or.inl (by pomega)) (Or.inl (by pomega)) (Or.inl (by pomega)), hnm₅, hnm₄, hnm₃,
          z₂ a (by pomega)]
        pomega
  have hX : partOf P₀ P₁ s ⊆ P₀ ∪ P₁ := by
    unfold partOf; split_ifs
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  obtain ⟨c₁₃, k₁₃, e₁₃, hk₁₃, ho₁₃, hfl₁₃, hval₁₃, hn₁₃, hrr₁₃, hnm₁₃, hrm₁₃⟩ :=
    dijk_exec_emb C hfr h hX hXn ℓ (bdry N P₀ P₁) (fun y => E y - Cz) δ hδ Es hEs hEs' hhd
      (fun _ _ => 0) pf (by simp [hpf]) (fun x hx => by simp [hpf, h.inv x hx]) I
      (by rw [hPW]; pomega) c₁₂ e₁₂.wb_right hin hDa hrb hmb
  have hR₁₃ : ∀ r, 800 ≤ r → r < 900 → c₁₃.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₁₃ r (by pomega)).trans (hR₁₂ r h1 h2)
  -- 14., 15. the normalization of the flags
  have w944 : c₁₃.nreg 944 = 2 * w + 4 + m' + m' := by rw [hn₁₃ _ (by pomega), u944]
  have w945 : c₁₃.nreg 945 = 2 * w + 4 + m' + m' + (w + 1) := by rw [hn₁₃ _ (by pomega), u945]
  obtain ⟨c₁₄, k₁₄, e₁₄, hk₁₄, n600, n601, n602, n603, n604, hn₁₄, hrr₁₄, hnm₁₄, hrm₁₄, ho₁₄⟩ :=
    nSet_exec (P := I) c₁₃ e₁₃.wb_right (by rw [w944]; pomega) (by rw [w945]; pomega)
  have hR₁₄ : ∀ r, 800 ≤ r → r < 900 → c₁₄.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₁₄ r (by pomega) (by pomega)).trans (hR₁₃ r h1 h2)
  have hNL : NrmLay w ((mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es).sb + 1)
      ((mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es).db + 1) Fs Vs W' := by
    rw [hPsb, hPdb]
    exact ⟨by pomega, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega⟩
  obtain ⟨c₁₅, k₁₅, e₁₅, hk₁₅, hout₁₅, hnm₁₅, hrm₁₅, hn₁₅, hrr₁₅, ho₁₅⟩ :=
    nrmProg_exec (P := I) hNL c₁₄ e₁₄.wb_right
      (by rw [n600, hR₁₃ 801 (by pomega) (by pomega), hctx.r801])
      (by rw [n601, w944, hPsb]; pomega) (by rw [n602, w945, hPdb]; pomega)
      (by rw [n603, hR₁₃ 832 (by pomega) (by pomega), h832])
      (by rw [n604, hR₁₃ 833 (by pomega) (by pomega), h833])
  have hR₁₅ : ∀ r, 800 ≤ r → r < 900 → c₁₅.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₁₅ r (by pomega)).trans (hR₁₄ r h1 h2)
  obtain ⟨hF, hV⟩ := minIn_of_run h hfl₁₃ hval₁₃ (cm := c₁₅) (Fb := Fs) (Vb := Vs)
    (fun v hv => by
      rw [(hout₁₅ v hv).1, hnm₁₄, Nat.add_assoc, Nat.add_comm 1 v])
    (fun v hv => by
      rw [(hout₁₅ v hv).2, hrm₁₄, Nat.add_assoc, Nat.add_comm 1 v])
  -- the run
  have hdij := dij_mono C (w + 1) _ _ hEl
  unfold csCost at hk₈
  refine ⟨c₁₅, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + (k₈ + (k₉ + (k₁₀ + (k₁₁ + (k₁₂ +
    (k₁₃ + (k₁₄ + k₁₅))))))))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉ (.seq e₁₀
      (.seq e₁₁ (.seq e₁₂ (.seq e₁₃ (.seq e₁₄ e₁₅))))))))))))),
    by rw [hA] at hk₂; pomega, hF, hV, hR₁₅, fun a ha h1 h2 => ?_, fun a ha h1 h2 => ?_, ?_⟩
  · rw [hnm₁₅ a h2, hnm₁₄, hnm₁₃ a (by pomega), hnm₁₂, hnm₁₁, hnm₁₀ a (Or.inr (by pomega)), hnm₉,
      hnm₈ a (Or.inr (by pomega)) (by pomega) (by pomega), hnm₇, hnm₆ a (by pomega) (by pomega)
        (by pomega), hnm₅, hm₄ a ha]
  · rw [hrm₁₅ a h2, hrm₁₄, hrm₁₃ a (by pomega), hrm₁₂ a (by pomega), hrm₁₁,
      hrm₁₀ a (Or.inr (by pomega)), hrm₉, hrm₈ a (by pomega), hrm₇, hrm₆ a (by pomega), hrm₅,
      hrm₄ a (by pomega) (Or.inr (by pomega)), hrm₃']
  · rw [ho₁₅, ho₁₄, ho₁₃, ho₁₂, ho₁₁, ho₁₀, ho₉, ho₈, ho₇, ho₆, ho₅, ho₄, ho₃, ho₂, ho₁]

end Node

end NegSSSP

end PlanarFlow
