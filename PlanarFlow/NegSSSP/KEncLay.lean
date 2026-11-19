module

public import PlanarFlow.NegSSSP.KEncCotAsm

/-!
# A concrete layout of the nodes and the edge arrays of the one-face encoding, on the machine

The encoding of a one-face instance (`Klein.KVal`) is given for a layout of the nodes
(`Klein.Layout`). Here a concrete one, from numberings `νv`, `σ`, `τ` of the vertices, darts and
faces (as `Klein.exists_layout`, with `σ` in place of `Fintype.equivFin`):

* `eIx σ d = min (σ d) (σ (rev d))`, the index of the edge of `d`;
* `cLayout`: `ιv = νv`, `ιg = a + eIx σ`, `ιf = a + b + τ`, `ιe = a + b + c + eIx σ` (`a`, `b`,
  `c` the numbers of vertices, darts, faces) is a `Klein.Layout` on `2 (a + b + c)` nodes; the
  nodes of the faces are `of + τ` with `of = a + b`, as `cotProg_exec` reads them.

The arrays `NE`, `NG`, `NH`, `ED` of the encoding (`Klein.KInput`) for this layout are written
from `RV` and `NT` by one loop over the darts (`edgProg`, natural words only):

* `edgProg_exec`: within `19 nD + 4` steps, `NH[x] = NT[RV[x]]`, `NG[x] = ag + min x RV[x]`,
  `NE[x] = ae + min x RV[x]`, and the word of `ED` at the node `ae + min x RV[x]` one of the darts
  `x'` with the same edge index.
* `edgProg_kinput`: **the fields `ne`, `ng`, `nh`, `ed` of `Klein.KInput`** in memory form, for
  the layout `cLayout`.

Registers: natural `1800 … 1808` (inputs `nD`, `RVb`, `NTb`, `NHb`, `ag`, `NGb`, `ae`, `NEb`,
`EDb`), `1810 … 1816` (scratch).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge

variable {P : Input} {W : ℕ}

/-! ### The layout -/

section Layout

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- The index of the edge of a dart for the numbering `σ`: the least number of its two darts. -/
def eIx {nD : ℕ} (σ : D ≃ Fin nD) (d : D) : ℕ := min (σ d : ℕ) (σ (M.rev d) : ℕ)

lemma eIx_rev {nD : ℕ} (σ : D ≃ Fin nD) (d : D) : eIx M σ (M.rev d) = eIx M σ d := by
  unfold eIx; rw [M.rev_rev, min_comm]

lemma eIx_lt {nD : ℕ} (σ : D ≃ Fin nD) (d : D) : eIx M σ d < nD :=
  lt_of_le_of_lt (min_le_left _ _) (σ d).2

lemma eIx_eq {nD : ℕ} (σ : D ≃ Fin nD) {d d' : D} (h : eIx M σ d = eIx M σ d') :
    d' = d ∨ d' = M.rev d := by
  have key : ∀ d : D, ∃ x, (x = d ∨ x = M.rev d) ∧ (σ x : ℕ) = eIx M σ d := by
    intro d
    rcases min_choice (σ d : ℕ) (σ (M.rev d) : ℕ) with h | h
    · exact ⟨d, Or.inl rfl, h.symm⟩
    · exact ⟨M.rev d, Or.inr rfl, h.symm⟩
  obtain ⟨x, hx, hx'⟩ := key d
  obtain ⟨y, hy, hy'⟩ := key d'
  have hxy : x = y := σ.injective (Fin.ext (by rw [hx', hy', h]))
  subst hxy
  rcases hx with rfl | rfl <;> rcases hy with h1 | h1
  · exact Or.inl h1.symm
  · exact Or.inr (by rw [h1, M.rev_rev])
  · exact Or.inr h1.symm
  · left
    have := congrArg M.rev h1
    rwa [M.rev_rev, M.rev_rev, eq_comm] at this

/-- **A concrete layout of the nodes**: the vertices `νv`, the edges of the spanning tree
`a + eIx σ`, the faces `a + b + τ`, the edges of the cotree `a + b + c + eIx σ`, on
`2 (a + b + c)` nodes. -/
theorem cLayout {a b c : ℕ} (νv : V ≃ Fin a) (σ : D ≃ Fin b) (τ : F ≃ Fin c) :
    Klein.Layout M (2 * (a + b + c)) (fun x => νv x) (fun d => a + eIx M σ d)
      (fun y => a + b + τ y) (fun d => a + b + c + eIx M σ d) := by
  have hv : ∀ x : V, (νv x : ℕ) < a := fun x => (νv x).2
  have hf : ∀ y : F, (τ y : ℕ) < c := fun y => (τ y).2
  have he : ∀ d : D, eIx M σ d < b := eIx_lt σ
  have cV : Fintype.card V = a := by rw [Fintype.card_congr νv, Fintype.card_fin]
  have cF : Fintype.card F = c := by rw [Fintype.card_congr τ, Fintype.card_fin]
  refine ⟨⟨fun x y h => νv.injective (Fin.ext h), fun d => ?_, fun d d' h => ?_,
      fun x d => ?_, fun x => ?_, fun d => ?_⟩,
    ⟨fun x y h => τ.injective (Fin.ext (by simpa using h)), fun d => ?_,
      fun d d' h => ?_, fun x d => ?_, fun x => ?_, fun d => ?_⟩,
    by omega, by omega, fun x y => ?_, fun x d => ?_, fun d y => ?_, fun d d' => ?_⟩
  · show a + eIx M σ (M.rev d) = _; rw [eIx_rev]
  · exact eIx_eq (M := M) σ (by simpa using h)
  · have := hv x; omega
  · have := hv x; omega
  · have := he d; omega
  · show a + b + c + eIx M σ (M.rev d) = _; rw [eIx_rev]
  · exact eIx_eq σ (by simpa using h)
  · have := hf x; omega
  · have := hf x; omega
  · have := he d; omega
  · have := hv x; omega
  · have := hv x; omega
  · have := he d; omega
  · have := he d; omega

end Layout

/-! ### The program -/

/-- The dart `i = r1811`: `r = RV[i]`, `NH[i] := NT[r]`, `e = i - (i - r) = min i r`,
`NG[i] := ag + e`, `NE[i] := ae + e`, `ED[ae + e] := i`. -/
def edgBody : Stmt :=
  block [.addN 1812 1801 1811, .loadN 1813 1812, .addN 1812 1802 1813, .loadN 1814 1812,
    .addN 1812 1803 1811, .storeN 1812 1814, .subN 1815 1811 1813, .subN 1815 1811 1815,
    .addN 1816 1804 1815, .addN 1812 1805 1811, .storeN 1812 1816, .addN 1816 1806 1815,
    .addN 1812 1807 1811, .storeN 1812 1816, .addN 1812 1808 1816, .storeN 1812 1811,
    .addN 1811 1811 1810]

/-- **The edge arrays.** -/
def edgProg : Stmt :=
  .seq (block [.constN 1810 1, .constN 1811 0]) (.whileLtN 1811 1800 edgBody)

variable {nD RVb NTb NHb ag NGb ae NEb EDb : ℕ}

theorem edgBody_exec (c : Config) (hc : WordsBounded W c) {i : ℕ}
    (r01 : c.nreg 1801 = RVb) (r02 : c.nreg 1802 = NTb) (r03 : c.nreg 1803 = NHb)
    (r04 : c.nreg 1804 = ag) (r05 : c.nreg 1805 = NGb) (r06 : c.nreg 1806 = ae)
    (r07 : c.nreg 1807 = NEb) (r08 : c.nreg 1808 = EDb)
    (r10 : c.nreg 1810 = 1) (r11 : c.nreg 1811 = i) (hi : i < nD)
    (hrv : c.nmem (RVb + i) < nD) (w1 : RVb + nD ≤ W) (w2 : NTb + nD ≤ W) (w3 : NHb + nD ≤ W)
    (w4 : NGb + nD ≤ W) (w5 : NEb + nD ≤ W) (w6 : EDb + ae + nD ≤ W) (w7 : ag + nD ≤ W) :
    ∃ c' k, Exec P W edgBody c c' k ∧ k = 17 ∧
      c'.nmem = upd (upd (upd (upd c.nmem (NHb + i) (c.nmem (NTb + c.nmem (RVb + i))))
        (NGb + i) (ag + (i - (i - c.nmem (RVb + i))))) (NEb + i)
        (ae + (i - (i - c.nmem (RVb + i))))) (EDb + (ae + (i - (i - c.nmem (RVb + i))))) i ∧
      c'.nreg 1811 = i + 1 ∧
      (∀ r, r < 1811 ∨ 1816 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold edgBody
  exec_block
  all_goals try
    ((try config_simp); (try simp only [r01, r02, r03, r04, r05, r06, r07, r08, r10, r11]); omega)
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r01, r02, r03, r04, r05, r06, r07, r08, r10, r11]
  · config_simp; simp only [r10, r11]
  · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl

/-- The state of the edge loop after the darts `x < r1811`, from `c₀`. -/
structure IEg (W nD RVb NTb NHb ag NGb ae NEb EDb : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ r, r < 1811 ∨ 1816 < r → c.nreg r = c₀.nreg r
  r11 : c.nreg 1811 ≤ nD
  done : ∀ x < c.nreg 1811, c.nmem (NHb + x) = c₀.nmem (NTb + c₀.nmem (RVb + x)) ∧
    c.nmem (NGb + x) = ag + min x (c₀.nmem (RVb + x)) ∧
    c.nmem (NEb + x) = ae + min x (c₀.nmem (RVb + x))
  ed : ∀ x < c.nreg 1811, ∃ x' < c.nreg 1811,
    min x' (c₀.nmem (RVb + x')) = min x (c₀.nmem (RVb + x)) ∧
    c.nmem (EDb + (ae + min x (c₀.nmem (RVb + x)))) = x'
  keep : ∀ a, a < NHb ∨ EDb + ae + nD ≤ a → c.nmem a = c₀.nmem a
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output

theorem edgStep_exec {c₀ : Config} (hrv : ∀ x < nD, c₀.nmem (RVb + x) < nD)
    (r00 : c₀.nreg 1800 = nD) (r01 : c₀.nreg 1801 = RVb) (r02 : c₀.nreg 1802 = NTb)
    (r03 : c₀.nreg 1803 = NHb) (r04 : c₀.nreg 1804 = ag) (r05 : c₀.nreg 1805 = NGb)
    (r06 : c₀.nreg 1806 = ae) (r07 : c₀.nreg 1807 = NEb) (r08 : c₀.nreg 1808 = EDb)
    (r10 : c₀.nreg 1810 = 1)
    (l1 : RVb + nD ≤ NHb) (l2 : NTb + nD ≤ NHb) (l3 : NHb + nD ≤ NGb) (l4 : NGb + nD ≤ NEb)
    (l5 : NEb + nD ≤ EDb + ae) (w4 : ag + nD ≤ W) (w6 : EDb + ae + nD ≤ W)
    (c : Config) (hI : IEg W nD RVb NTb NHb ag NGb ae NEb EDb c₀ c)
    (hlt : c.nreg 1811 < c.nreg 1800) :
    ∃ c' k, Exec P W edgBody c c' k ∧ IEg W nD RVb NTb NHb ag NGb ae NEb EDb c₀ c' ∧
      (nD - c'.nreg 1811) * 19 + k + 2 ≤ (nD - c.nreg 1811) * 19 := by
  have g : ∀ r, 1800 ≤ r → r ≤ 1810 → c.nreg r = c₀.nreg r := fun r h1 h2 =>
    hI.regs r (by omega)
  rw [g 1800 le_rfl (by omega), r00] at hlt
  generalize hi : c.nreg 1811 = i at hlt
  have hrvi : c.nmem (RVb + i) = c₀.nmem (RVb + i) := hI.keep _ (by omega)
  have hr := hrv i hlt
  obtain ⟨c', k, e, hk, hm, h11, hrg, hrr, hrm, ho⟩ := edgBody_exec (P := P) (W := W) c hI.wb
    (nD := nD) (RVb := RVb) (NTb := NTb) (NHb := NHb) (ag := ag) (NGb := NGb) (ae := ae)
    (NEb := NEb) (EDb := EDb) ((g 1801 (by omega) (by omega)).trans r01)
    ((g 1802 (by omega) (by omega)).trans r02) ((g 1803 (by omega) (by omega)).trans r03)
    ((g 1804 (by omega) (by omega)).trans r04) ((g 1805 (by omega) (by omega)).trans r05)
    ((g 1806 (by omega) (by omega)).trans r06) ((g 1807 (by omega) (by omega)).trans r07)
    ((g 1808 (by omega) (by omega)).trans r08) ((g 1810 (by omega) le_rfl).trans r10) hi hlt
    (by rw [hrvi]; exact hr) (by omega) (by omega) (by omega) (by omega) (by omega) w6 w4
  have hnt : c.nmem (NTb + c.nmem (RVb + i)) = c₀.nmem (NTb + c₀.nmem (RVb + i)) := by
    rw [hrvi]; exact hI.keep _ (by omega)
  have hmin : i - (i - c.nmem (RVb + i)) = min i (c₀.nmem (RVb + i)) := by rw [hrvi]; omega
  rw [hnt, hmin] at hm
  have hmin_lt : min i (c₀.nmem (RVb + i)) < nD := by omega
  refine ⟨c', k, e, ⟨e.wb_right, fun r hr' => ?_, by omega, fun x hx => ?_, fun x hx => ?_,
    fun a ha => ?_, by rw [hrr]; exact hI.rr, by rw [hrm]; exact hI.rm,
    by rw [ho]; exact hI.out⟩, ?_⟩
  · rw [hrg r (by omega)]; exact hI.regs r hr'
  · rw [h11] at hx
    rw [hm]
    simp only [upd_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
    · obtain ⟨d1, d2, d3⟩ := hI.done x (by omega)
      refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> first | omega | assumption
    · refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega
  · rw [h11] at hx
    have hed : ∀ a, EDb + ae ≤ a → c'.nmem a =
        if a = EDb + (ae + min i (c₀.nmem (RVb + i))) then i else c.nmem a := fun a ha => by
      rw [hm]; simp only [upd_apply]; split_ifs <;> first | rfl | omega
    rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
    · by_cases he : min x (c₀.nmem (RVb + x)) = min i (c₀.nmem (RVb + i))
      · exact ⟨i, by omega, he.symm, by rw [hed _ (by omega), he]; simp⟩
      · obtain ⟨x', hx', h1, h2⟩ := hI.ed x (by omega)
        refine ⟨x', by omega, h1, ?_⟩
        rw [hed _ (by omega)]
        split_ifs with h
        · omega
        · exact h2
    · exact ⟨x, by omega, rfl, by rw [hed _ (by omega)]; simp⟩
  · rw [hm]; simp only [upd_apply]
    split_ifs <;> first | omega | exact hI.keep a ha
  · rw [h11, hk]
    have : nD - i = nD - (i + 1) + 1 := by omega
    rw [this, Nat.add_mul]

/-- **The edge arrays on the machine**: within `19 nD + 4` steps, `NH[x] = NT[RV[x]]`,
`NG[x] = ag + min x RV[x]`, `NE[x] = ae + min x RV[x]`, and the word of `ED` at the node
`ae + min x RV[x]` is one of the darts with the same edge index; the memory below `NH` and above
`ED` is kept. -/
theorem edgProg_exec (c : Config) (hc : WordsBounded W c)
    (hrv : ∀ x < nD, c.nmem (RVb + x) < nD)
    (r00 : c.nreg 1800 = nD) (r01 : c.nreg 1801 = RVb) (r02 : c.nreg 1802 = NTb)
    (r03 : c.nreg 1803 = NHb) (r04 : c.nreg 1804 = ag) (r05 : c.nreg 1805 = NGb)
    (r06 : c.nreg 1806 = ae) (r07 : c.nreg 1807 = NEb) (r08 : c.nreg 1808 = EDb)
    (l1 : RVb + nD ≤ NHb) (l2 : NTb + nD ≤ NHb) (l3 : NHb + nD ≤ NGb) (l4 : NGb + nD ≤ NEb)
    (l5 : NEb + nD ≤ EDb + ae) (w4 : ag + nD ≤ W) (w6 : EDb + ae + nD ≤ W) (hW1 : 1 ≤ W) :
    ∃ c' k, Exec P W edgProg c c' k ∧ k ≤ 19 * nD + 4 ∧
      (∀ x < nD, c'.nmem (NHb + x) = c.nmem (NTb + c.nmem (RVb + x)) ∧
        c'.nmem (NGb + x) = ag + min x (c.nmem (RVb + x)) ∧
        c'.nmem (NEb + x) = ae + min x (c.nmem (RVb + x))) ∧
      (∀ x < nD, ∃ x' < nD, min x' (c.nmem (RVb + x')) = min x (c.nmem (RVb + x)) ∧
        c'.nmem (EDb + (ae + min x (c.nmem (RVb + x)))) = x') ∧
      (∀ a, a < NHb ∨ EDb + ae + nD ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1810 ∨ 1816 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hw₁, hr₁, h10, h11, hm₁, hrr₁, hrm₁, ho₁, rfl⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 1810 1, .constN 1811 0]) c c₁ k₁ ∧ WordsBounded W c₁ ∧
      (∀ r, r ≠ 1810 → r ≠ 1811 → c₁.nreg r = c.nreg r) ∧ c₁.nreg 1810 = 1 ∧ c₁.nreg 1811 = 0 ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output ∧
      k₁ = 2 := by
    exec_block
    · omega
    · omega
    refine ⟨‹_›, fun r h1 h2 => ?_, by config_simp, by config_simp, rfl, rfl, rfl, rfl, rfl⟩
    config_simp; rw [upd_other _ _ _ h2, upd_other _ _ _ h1]
  have g : ∀ r, r ≠ 1810 → r ≠ 1811 → ∀ v, c.nreg r = v → c₁.nreg r = v :=
    fun r h1 h2 v e => (hr₁ r h1 h2).trans e
  have hI₁ : IEg W nD RVb NTb NHb ag NGb ae NEb EDb c₁ c₁ :=
    ⟨hw₁, fun _ _ => rfl, by omega, fun x hx => by omega, fun x hx => by omega, fun _ _ => rfl,
      rfl, rfl, rfl⟩
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 1811)
    (b := 1800) (body := edgBody) (IEg W nD RVb NTb NHb ag NGb ae NEb EDb c₁)
    (fun c => (nD - c.nreg 1811) * 19) (fun c h => h.wb)
    (fun c' hc' hlt' => edgStep_exec (by rw [hm₁]; exact hrv) (g _ (by omega) (by omega) _ r00)
      (g _ (by omega) (by omega) _ r01) (g _ (by omega) (by omega) _ r02)
      (g _ (by omega) (by omega) _ r03) (g _ (by omega) (by omega) _ r04)
      (g _ (by omega) (by omega) _ r05) (g _ (by omega) (by omega) _ r06)
      (g _ (by omega) (by omega) _ r07) (g _ (by omega) (by omega) _ r08) h10 l1 l2 l3 l4 l5
      w4 w6 c' hc' hlt') hI₁
  have h1800 : c₂.nreg 1800 = nD := by
    rw [hI₂.regs 1800 (by omega)]; exact g _ (by omega) (by omega) _ r00
  have h1811 : c₂.nreg 1811 = nD := by have := hI₂.r11; rw [h1800] at hn₂; omega
  refine ⟨c₂, _, .seq e₁ e₂, ?_, fun x hx => ?_, fun x hx => ?_, fun a ha => ?_,
    fun r hr => ?_, by rw [hI₂.rr, hrr₁], by rw [hI₂.rm, hrm₁], by rw [hI₂.out, ho₁]⟩
  · beta_reduce at hk₂; rw [h11, Nat.sub_zero] at hk₂; omega
  · have := hI₂.done x (by omega); rw [hm₁] at this; exact this
  · obtain ⟨x', hx', h1, h2⟩ := hI₂.ed x (by omega)
    rw [hm₁] at h1 h2; exact ⟨x', by omega, h1, h2⟩
  · rw [hI₂.keep a ha, hm₁]
  · rw [hI₂.regs r (by omega), hr₁ r (by omega) (by omega)]

end NegSSSP

end PlanarFlow
