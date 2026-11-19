module

public import PlanarFlow.NegSSSP.NodeCmpA

/-!
# The node run on natural words: the composition, the Dijkstra half

`node_dij_cmp`: every run of `nodeDij` from the start of `node_dij_exec` with `NInv W' B` and
integer reals compares within `512 dijB b w B` and ends with `NInv W' (dijB b w B)`,
`dijB b w B = partB b w (partB b w ((4 b + 2) B))`: `cProg` (`cProg_cmp`, `(4 b + 2) B`), the
two parts (`part_cmp`, the start of the second from the frame of `part_exec` of the first),
the glue (`good_glue`, `good_nat`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Monge.FR BKMNW
  CmpAbs ModNat

/-- The bound of the invariant after the Dijkstra half: `cProg`, then the two parts. -/
def dijB (b w B : ℕ) : ℕ := partB b w (partB b w ((4 * b + 2) * B))

theorem dijB_le {b w B : ℕ} : B ≤ (4 * b + 2) * B ∧ (4 * b + 2) * B ≤ partB b w ((4 * b + 2) * B) ∧
    partB b w ((4 * b + 2) * B) ≤ dijB b w B :=
  ⟨Nat.le_mul_of_pos_left B (by omega), le_partB, le_partB⟩

theorem le_dijB {b w B : ℕ} : B ≤ dijB b w B := by
  obtain ⟨h1, h2, h3⟩ := dijB_le (b := b) (w := w) (B := B)
  omega

section Node

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

set_option maxHeartbeats 4000000 in
/-- **Every run of the Dijkstra half is compare-bounded** (see the module docstring). -/
theorem node_dij_cmp {fr : FRFun (Option V)} (hfr : FRSpec fr) {P₀ P₁ : Finset D}
    {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} (h : NodeEnc N P₀ P₁ m w e ν ι)
    {β : ℕ → V} (hβ : IsEnum b β (bdry N P₀ P₁)) (hP₀ : P₀.Nonempty) (hP₁ : P₁.Nonempty)
    (ℓ : D → ℤ) (E δ₀ δ₁ : V → ℤ) (hδ₀ : (pg N P₀ ℓ).IsPot δ₀) (hδ₁ : (pg N P₁ ℓ).IsPot δ₁)
    {Z M₀ W' : ℕ} (hM₀ : M₀ = m + w + 1) (hZ : loB m w ≤ Z) (hW : Z + 22 * M₀ ≤ W')
    (I : Input) (c : Config) (hctx : NCtx m w b Z M₀ c)
    (hTm : ∀ d < m, c.nmem (Z + 0 * M₀ + d) = encT N e ν d)
    (hHm : ∀ d < m, c.nmem (Z + 1 * M₀ + d) = encH N e ν d)
    (hSm : ∀ d < m, c.nmem (Z + 2 * M₀ + d) = encS P₀ e d)
    (hLm : ∀ d < m, c.rmem (Z + 3 * M₀ + d) = ℓ (e d))
    (hD₀ : ∀ v < w, c.rmem (Z + 4 * M₀ + v) = δ₀ (ι v))
    (hD₁ : ∀ v < w, c.rmem (Z + 5 * M₀ + v) = δ₁ (ι v))
    (hNm : ∀ i < b, c.nmem (Z + 6 * M₀ + i) = ν (β i))
    (hEm : ∀ i < b, c.rmem (Z + 7 * M₀ + i) = E (β i))
    {B : ℕ} (hI : NInv W' B c) (hZi : IntAll c) {c' : Config} {k : ℕ}
    (ex : Exec I W' nodeDij c c' k) :
    NGood I W' (512 * dijB b w B) (dijB b w B) nodeDij c c' := by
  have hc : WordsBounded W' c := ex.wb_left
  classical
  have hA : loB m w = 4 * m + 18 * w + 175 := rfl
  have hbw : b ≤ w := by rw [hβ.card]; exact card_bdry_le h
  have hnlt : ∀ i < b, ν (β i) < w := fun i hi => h.lt _ (bdry_sub_verts (hβ.mem i hi))
  set Cz : ℤ := ∑ v ∈ bdry N P₀ P₁, (|E v - δ₀ v| + |E v - δ₁ v|) with hCz
  -- the lowering
  obtain ⟨c₁, k₁, e₁, hk₁, g500, g501, g502, g503, g504, hn₁, hrr₁, hnm₁, hrm₁, ho₁⟩ :=
    cSet_exec (P := I) c hc
  have hCL : CLay b w (Z + 7 * M₀) (Z + 6 * M₀) (Z + 4 * M₀) (Z + 5 * M₀) W'
      (fun i => ν (β i)) := ⟨hnlt, by pomega, by pomega, by pomega, by pomega, by pomega⟩
  have hCI : CIn b w (Z + 7 * M₀) (Z + 6 * M₀) (Z + 4 * M₀) (Z + 5 * M₀) (fun i => ν (β i))
      (fun i => (E (β i) : ℝ)) (fun v => (δ₀ (ι v) : ℝ)) (fun v => (δ₁ (ι v) : ℝ)) c₁ := by
    refine ⟨by rw [g500, hctx.r802], by rw [g501, hctx.slot 7 (by pomega)],
      by rw [g502, hctx.slot 6 (by pomega)], by rw [g503, hctx.slot 4 (by pomega)],
      by rw [g504, hctx.slot 5 (by pomega)], fun i hi => ?_, fun i hi => ?_, fun v hv => ?_,
      fun v hv => ?_⟩
    · rw [hnm₁]; exact hNm i hi
    · rw [hrm₁]; exact hEm i hi
    · rw [hrm₁]; exact hD₀ v hv
    · rw [hrm₁]; exact hD₁ v hv
  obtain ⟨c₂, k₂, e₂, hk₂, hC₂, hn₂, hnm₂, hrm₂, ho₂⟩ :=
    cProg_exec (P := I) hCL c₁ e₁.wb_right hCI
  have hCv : c₂.rreg 500 = (Cz : ℝ) := by
    rw [hC₂, hCz]
    have := sum_enum hβ (fun v => |(E v : ℝ) - δ₀ v| + |(E v : ℝ) - δ₁ v|)
    push_cast
    rw [← this]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [h.inv _ (bdry_sub_verts (hβ.mem i (Finset.mem_range.1 hi)))]
  obtain ⟨c₃, k₃, e₃, hk₃, hst₃, hrm₃, hn₃, hnm₃, ho₃⟩ := cStore_exec (P := I) c₂ e₂.wb_right
  have hR₃ : ∀ r, 800 ≤ r → r < 900 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    rw [hn₃ r (by pomega), hn₂ r (by pomega), hn₁ r (by pomega)]
  have h824 : c₂.nreg 824 = Z + 21 * M₀ := by
    rw [hn₂ _ (by pomega), hn₁ _ (by pomega)]; exact hctx.slot 21 (by pomega)
  rw [h824, hCv] at hst₃
  rw [h824] at hrm₃
  have hm₃ : c₃.nmem = c.nmem := by rw [hnm₃, hnm₂, hnm₁]
  have hr₃ : ∀ a, a ≠ Z + 21 * M₀ → c₃.rmem a = c.rmem a := fun a ha => by
    rw [hrm₃ a ha, hrm₂, hrm₁]
  have hctx₃ : NCtx m w b Z M₀ c₃ := hctx.of hR₃
  -- the part `0`
  obtain ⟨c₄, k₄, e₄, hk₄, s830, s831, s832, s833, hn₄, hnm₄, hrm₄, ho₄⟩ :=
    sideSet_exec (P := I) (s := 0) (δr := 807) (Fr := 819) (Vr := 820) (by pomega) (by pomega) (by pomega) (by pomega) c₃
      e₃.wb_right
  have hctx₄ : NCtx m w b Z M₀ c₄ := hctx₃.of' fun r h1 h2 => hn₄ r (by pomega)
  obtain ⟨c₅, k₅, e₅, hk₅, hF₅, hV₅, hR₅, hnm₅, hrm₅, ho₅⟩ :=
    part_exec 0 hfr h hβ (s := 0) (by pomega) (by simpa [partOf] using hP₀) ℓ E δ₀ Cz
      (by simpa [partOf] using hδ₀) hM₀ hZ hW (δb := Z + 4 * M₀) (Fs := Z + 16 * M₀)
      (Vs := Z + 17 * M₀) (Or.inl rfl) le_rfl (by pomega) (by pomega) (by pomega) I c₄ e₄.wb_right
      hctx₄ s830 (by rw [s831, hctx₃.slot 4 (by pomega)])
      (by rw [s832, hctx₃.slot 16 (by pomega)]) (by rw [s833, hctx₃.slot 17 (by pomega)])
      (fun d hd => by rw [hnm₄, hm₃]; exact hTm d hd)
      (fun d hd => by rw [hnm₄, hm₃]; exact hHm d hd)
      (fun d hd => by rw [hnm₄, hm₃]; exact hSm d hd)
      (fun d hd => by rw [hrm₄, hr₃ _ (by pomega)]; exact hLm d hd)
      (fun v hv => by rw [hrm₄, hr₃ _ (by pomega)]; exact hD₀ v hv)
      (fun i hi => by rw [hnm₄, hm₃]; exact hNm i hi)
      (fun i hi => by rw [hrm₄, hr₃ _ (by pomega)]; exact hEm i hi)
      (by rw [hrm₄, hst₃])
  have hctx₅ : NCtx m w b Z M₀ c₅ := hctx₄.of hR₅
  -- the part `1`
  obtain ⟨c₆, k₆, e₆, hk₆, t830, t831, t832, t833, hn₆, hnm₆, hrm₆, ho₆⟩ :=
    sideSet_exec (P := I) (s := 1) (δr := 808) (Fr := 821) (Vr := 822) (by pomega) (by pomega) (by pomega) (by pomega) c₅
      e₅.wb_right
  have hctx₆ : NCtx m w b Z M₀ c₆ := hctx₅.of' fun r h1 h2 => hn₆ r (by pomega)
  have hn₅₄ : ∀ a, Z ≤ a → a < Z + 9 * M₀ → c₅.nmem a = c.nmem a := fun a h1 h2 => by
    rw [hnm₅ a h1 (Or.inl h2) (Or.inl (by pomega)), hnm₄, hm₃]
  have hr₅₄ : ∀ a, Z ≤ a → (a < Z + 8 * M₀ ∨ a = Z + 21 * M₀) → c₅.rmem a = c₃.rmem a :=
    fun a h1 h2 => by
      rw [hrm₅ a h1 (by pomega) (by pomega), hrm₄]
  -- the actual run
  have hDd : nodeDij.noDivR = true := by decide +kernel
  simp only [nodeDij, Stmt.noDivR, Bool.and_eq_true] at hDd
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := hDd
  unfold nodeDij at ex
  obtain ⟨_, _, _, x₁, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₁ x₁
  obtain ⟨_, _, _, x₂, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₂ x₂
  obtain ⟨_, _, _, x₃, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₃ x₃
  obtain ⟨_, _, _, x₄, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₄ x₄
  obtain ⟨_, _, _, x₅, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₅ x₅
  obtain ⟨_, _, _, x₆, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₆ x₆
  obtain ⟨c₇, _, _, x₇, ex⟩ := seq_parts ex
  obtain ⟨c₈, _, _, x₈, x₉⟩ := seq_parts ex
  -- the bounds
  obtain ⟨hB1, hB2, hB3⟩ := dijB_le (b := b) (w := w) (B := B)
  have hP3 := le_partB (b := b) (w := w) (B := partB b w ((4 * b + 2) * B))
  have h500 : c₁.nreg 500 = b := by rw [g500, hctx.r802]
  have G₁ := good_glue (H := 512 * dijB b w B) cSet_glueOK d1 e₁ hI hZi (by omega)
  have G₂ : NGood I W' (512 * dijB b w B) ((4 * b + 2) * B) cProg c₁ c₂ := by
    obtain ⟨C, hI'⟩ := cProg_cmp e₂ G₁.2.1 G₁.2.2
    rw [h500] at C hI'
    exact ⟨⟨_, C.mono_H (by omega)⟩, hI', Exec.intAll e₂ d2 G₁.2.2⟩
  have G₃ := good_glue (H := 512 * dijB b w B) cStore_glueOK d3 e₃ G₂.2.1 G₂.2.2 (by omega)
  have G₄ := good_nat (H := 512 * dijB b w B) (sideSet_natOnly _ _ _ _) d4 e₄ G₃.2.1 G₃.2.2
  have G₅ := part_cmp h hβ (s := 0) (by pomega) ℓ E δ₀ Cz
      (by simpa [partOf] using hδ₀) hM₀ hZ hW (δb := Z + 4 * M₀) (Or.inl rfl) I c₄
      hctx₄ s830 (by rw [s831, hctx₃.slot 4 (by pomega)])
      (fun d hd => by rw [hnm₄, hm₃]; exact hTm d hd)
      (fun d hd => by rw [hnm₄, hm₃]; exact hHm d hd)
      (fun d hd => by rw [hnm₄, hm₃]; exact hSm d hd)
      (fun d hd => by rw [hrm₄, hr₃ _ (by pomega)]; exact hLm d hd)
      (fun v hv => by rw [hrm₄, hr₃ _ (by pomega)]; exact hD₀ v hv)
      (fun i hi => by rw [hnm₄, hm₃]; exact hNm i hi)
      (fun i hi => by rw [hrm₄, hr₃ _ (by pomega)]; exact hEm i hi)
      (by rw [hrm₄, hst₃]) G₄.2.1 G₄.2.2 e₅
  have G₆ := good_nat (H := 512 * dijB b w B) (sideSet_natOnly _ _ _ _) d6 e₆ G₅.2.1 G₅.2.2
  have G₇ := part_cmp h hβ (s := 1) le_rfl ℓ E δ₁ Cz
      (by simpa [partOf] using hδ₁) hM₀ hZ hW (δb := Z + 5 * M₀) (Or.inr rfl) I c₆
      hctx₆ t830 (by rw [t831, hctx₅.slot 5 (by pomega)])
      (fun d hd => by rw [hnm₆, hn₅₄ _ (by pomega) (by pomega)]; exact hTm d hd)
      (fun d hd => by rw [hnm₆, hn₅₄ _ (by pomega) (by pomega)]; exact hHm d hd)
      (fun d hd => by rw [hnm₆, hn₅₄ _ (by pomega) (by pomega)]; exact hSm d hd)
      (fun d hd => by
        rw [hrm₆, hr₅₄ _ (by pomega) (Or.inl (by pomega)), hr₃ _ (by pomega)]; exact hLm d hd)
      (fun v hv => by
        rw [hrm₆, hr₅₄ _ (by pomega) (Or.inl (by pomega)), hr₃ _ (by pomega)]; exact hD₁ v hv)
      (fun i hi => by rw [hnm₆, hn₅₄ _ (by pomega) (by pomega)]; exact hNm i hi)
      (fun i hi => by
        rw [hrm₆, hr₅₄ _ (by pomega) (Or.inl (by pomega)), hr₃ _ (by pomega)]; exact hEm i hi)
      (by rw [hrm₆, hr₅₄ _ (by pomega) (Or.inr rfl), hst₃]) G₆.2.1 G₆.2.2 x₇
  have G₈ := good_glue (H := 512 * dijB b w B) mSet_glueOK d8 x₈ G₇.2.1 G₇.2.2 (by unfold dijB; omega)
  have G₉ := good_glue (H := 512 * dijB b w B) minProg_glueOK d9 x₉ G₈.2.1 G₈.2.2 (by unfold dijB; omega)
  exact G₁.seq (G₂.seq (G₃.seq (G₄.seq ((G₅.mono (by omega) le_rfl).seq (G₆.seq
    ((G₇.mono (by unfold dijB; omega) le_rfl).seq (G₈.seq G₉)))))))

end Node

end NegSSSP

end PlanarFlow
