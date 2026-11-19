module

public import PlanarFlow.NegSSSP.NodeCmpB

/-!
# The node run on natural words: the composition, the end of a node

`rest_cmp`: every run of `restProg` from the start of `rest_exec` (`b ≥ 1`) with `NInv W' B` and
integer reals compares within `512 restB b w B` and ends with `NInv W' (restB b w B)`,
`restB b w B = dijB b w (bfB b B)`: the glue, Bellman–Ford (`bfStage_cmp`, from the start of
`bfStage_exec`, the lengths bounded by `B` from the invariant), the Dijkstra half
(`node_dij_cmp`, from the end of `bfStage_exec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge Monge.FR
  CmpAbs ModNat

/-- The bound of the invariant after the end of a node: Bellman–Ford, the Dijkstra half. -/
def restB (b w B : ℕ) : ℕ := dijB b w (bfB b B)

theorem le_restB {b w B : ℕ} (hb : 1 ≤ b) : B ≤ bfB b B ∧ bfB b B ≤ restB b w B :=
  ⟨le_bfB hb, le_dijB⟩

section Rest

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

set_option maxHeartbeats 4000000 in
/-- **Every run of the end of a node is compare-bounded** (see the module docstring). -/
theorem rest_cmp {I : Input} {fr : FRFun (Option V)} (hfr : FRSpec fr)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}
    {P₀ P₁ : Finset D} {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}
    (h : NodeEnc N P₀ P₁ m w e ν ι) (hP₀ : P₀.Nonempty) (hP₁ : P₁.Nonempty) (hb : 1 ≤ b)
    (ℓ : D → ℤ) (δ₀ δ₁ : V → ℤ) (hδ₀ : (pg N P₀ ℓ).IsPot δ₀) (hδ₁ : (pg N P₁ ℓ).IsPot δ₁)
    {β₀ β₁ : ℕ → V} (e₀ : IsEnum b β₀ (bdry N P₀ P₁)) (e₁ : IsEnum b β₁ (bdry N P₀ P₁))
    (cr₀ : CrossingO b (fun i j => (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).len (β₀ i) (β₀ j)))
    (cr₁ : CrossingO b (fun i j => (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)).len (β₁ i) (β₁ j)))
    {Z M₀ Y S W' : ℕ} (hM₀ : M₀ = m + w + 1) (hZ : loB m w ≤ Z) (hbZ : bfWP b < Z)
    (hY : Z + 22 * M₀ ≤ Y) (hSw : w ≤ S) (hSb : b * b ≤ S) (hW : Y + 16 * S ≤ W')
    (c : Config) (hctx : NCtx m w b Z M₀ c) (hx : XCtx Y S c)
    (hTm : ∀ d < m, c.nmem (Z + 0 * M₀ + d) = encT N e ν d)
    (hHm : ∀ d < m, c.nmem (Z + 1 * M₀ + d) = encH N e ν d)
    (hSm : ∀ d < m, c.nmem (Z + 2 * M₀ + d) = encS P₀ e d)
    (hLm : ∀ d < m, c.rmem (Z + 3 * M₀ + d) = ℓ (e d))
    (hD₀ : ∀ v < w, c.rmem (Z + 4 * M₀ + v) = δ₀ (ι v))
    (hD₁ : ∀ v < w, c.rmem (Z + 5 * M₀ + v) = δ₁ (ι v))
    (hO₀ : ∀ x < b, c.nmem (Y + 4 * S + x) = ν (β₀ x))
    (hO₁ : ∀ x < b, c.nmem (Y + 9 * S + x) = ν (β₁ x))
    (hF₀ : ∀ s < b, ∀ t < b,
      c.nmem (Y + 6 * S + (s * b + t)) =
          finB (arcOf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) β₀) s t ∧
        c.rmem (Y + 6 * S + (s * b + t)) =
          (matOf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) β₀ s t : ℝ))
    (hF₁ : ∀ s < b, ∀ t < b,
      c.nmem (Y + 11 * S + (s * b + t)) =
          finB (arcOf (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) β₁) s t ∧
        c.rmem (Y + 11 * S + (s * b + t)) =
          (matOf (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) β₁ s t : ℝ))
    {B : ℕ} (hI : NInv W' B c) (hZi : IntAll c) {c' : Config} {k : ℕ}
    (ex : Exec I W' restProg c c' k) :
    NGood I W' (512 * restB b w B) (restB b w B) restProg c c' := by
  have hc : WordsBounded W' c := ex.wb_left
  classical
  have hbw : b ≤ w := by rw [e₀.card]; exact card_bdry_le h
  have hA : loB m w = 4 * m + 18 * w + 175 := rfl
  have hWb : bfWP b = 8 * (b * b) + 14 * b + 12 := rfl
  have hx' := hx.reg
  -- 1. the registers of `permProg`
  obtain ⟨c₁, k₁, e₁', hk₁, g10, g220, g221, g222, g223, g224, gn₁, gnm₁, grm₁, go₁⟩ :=
    restSet_exec (I := I) c hc (by pomega)
  -- 2. `π`
  have hv : ∀ i < b, ∀ β : ℕ → V, IsEnum b β (bdry N P₀ P₁) →
      ν (β i) < w ∧ ι (ν (β i)) = β i := fun i hi β hβ =>
    ⟨h.lt _ (bdry_sub_verts (hβ.mem i hi)), h.inv _ (bdry_sub_verts (hβ.mem i hi))⟩
  have hPL : PermLay b w (Y + 4 * S) (Y + 9 * S) (Y + 13 * S) (Y + 14 * S) W'
      (fun i => ν (β₀ i)) (fun i => ν (β₁ i)) := by
    refine ⟨fun i hi => (hv i hi β₀ e₀).1, fun i hi => (hv i hi β₁ e₁).1,
      fun i hi j hj hij => e₀.inj i hi j hj (by
        rw [← (hv i hi β₀ e₀).2, ← (hv j hj β₀ e₀).2]; exact congrArg ι hij),
      fun i hi => ?_, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega,
      by pomega, by pomega, by pomega⟩
    obtain ⟨j, hj, hjj⟩ := e₀.surj (β₁ i) (e₁.mem i hi)
    exact ⟨j, hj, by rw [hjj]⟩
  have hPI : PermIn b (Y + 4 * S) (Y + 9 * S) (Y + 13 * S) (Y + 14 * S)
      (fun i => ν (β₀ i)) (fun i => ν (β₁ i)) c₁ :=
    ⟨g10, by rw [g220, hctx.r802], by rw [g221, hx' 4 (by omega)],
      by rw [g222, hx' 9 (by omega)], by rw [g223, hx' 13 (by omega)],
      by rw [g224, hx' 14 (by omega)], fun i hi => by rw [gnm₁]; exact hO₀ i hi,
      fun i hi => by rw [gnm₁]; exact hO₁ i hi⟩
  obtain ⟨c₂, k₂, e₂', hk₂, hπ₂, hm₂, hf₂⟩ :=
    permProg_node (I := I) h e₀ e₁ hPL c₁ e₁'.wb_right hPI
  have hR₂ : ∀ r, (800 ≤ r ∧ r < 900) ∨ (919 ≤ r ∧ r < 990) → c₂.nreg r = c.nreg r :=
    fun r hr => by rw [hf₂.nreg r (by pomega), gn₁ r (by pomega) (by pomega)]
  have hmY : ∀ a, a < Y + 13 * S → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hm₂ a (Or.inl ha) (Or.inl (by pomega)), gnm₁]
  -- 3., 4. Bellman–Ford
  obtain ⟨c₃, k₃, e₃', hk₃, b970, b971, b972, b973, b974, gn₃, gnm₃, grm₃, go₃⟩ :=
    bfIn_exec (I := I) c₂ e₂'.wb_right
  have hR₃ : ∀ r, (800 ≤ r ∧ r < 900) ∨ (919 ≤ r ∧ r < 970) → c₃.nreg r = c.nreg r :=
    fun r hr => by rw [gn₃ r (by pomega), hR₂ r (by pomega)]
  have hBL : BLay b (Y + 14 * S) (Y + 6 * S) (Y + 11 * S) (Y + 4 * S) (Y + 15 * S) (Z + 6 * M₀)
      (Z + 7 * M₀) W' :=
    ⟨by pomega, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega,
      by pomega, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega,
      by pomega, by pomega⟩
  obtain ⟨c₄, k₄, E, e₄', hk₄, hE₄, hout₄, hN₄, hn₄, hm₄, hr₄, ho₄⟩ :=
    bfStage_exec (I := I) (isPermB_permOf e₀ e₁) cr₀.crossingX cr₁.crossingX hBL c₃ e₃'.wb_right
      (by rw [hR₃ 802 (by pomega), hctx.r802])
      (by rw [hR₃ 809 (by pomega), hctx.slot 6 (by pomega)])
      (by rw [hR₃ 810 (by pomega), hctx.slot 7 (by pomega)])
      (by rw [b970, hR₂ 944 (by pomega), hx' 14 (by omega)])
      (by rw [b971, hR₂ 936 (by pomega), hx' 6 (by omega)])
      (by rw [b972, hR₂ 941 (by pomega), hx' 11 (by omega)])
      (by rw [b973, hR₂ 934 (by pomega), hx' 4 (by omega)])
      (by rw [b974, hR₂ 945 (by pomega), hx' 15 (by omega)])
      (fun i hi => by rw [gnm₃]; exact hπ₂ i hi)
      (fun s hs t ht => by
        rw [gnm₃, grm₃, hmY _ (by have := rmLt hs ht; pomega), hf₂.rmem, grm₁]
        exact hF₀ s hs t ht)
      (fun s hs t ht => by
        rw [gnm₃, grm₃, hmY _ (by have := rmLt hs ht; pomega), hf₂.rmem, grm₁]
        exact hF₁ s hs t ht)
  -- 5. the Dijkstra half
  set E' : V → ℤ := fun v => E (enumInv b β₀ v) with hE'
  have hctx₄ : NCtx m w b Z M₀ c₄ :=
    hctx.of fun r h1 h2 => by rw [hn₄ r (by pomega), hR₃ r (by pomega)]
  have hm₄' : ∀ a, Z ≤ a → a < Z + 6 * M₀ → c₄.nmem a = c.nmem a := fun a h1 h2 => by
    rw [hm₄ a (by pomega) (by pomega), gnm₃, hmY a (by pomega)]
  have hr₄' : ∀ a, Z ≤ a → a < Z + 6 * M₀ → c₄.rmem a = c.rmem a := fun a h1 h2 => by
    rw [hr₄ a (by pomega) (by pomega) (by pomega), grm₃, hf₂.rmem, grm₁]
  -- the actual run
  have hDr : restProg.noDivR = true := by decide +kernel
  simp only [restProg, Stmt.noDivR, Bool.and_eq_true] at hDr
  obtain ⟨d1, d2, d3, d4, d5⟩ := hDr
  unfold restProg at ex
  obtain ⟨_, _, _, x₁, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₁' x₁
  obtain ⟨_, _, _, x₂, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₂' x₂
  obtain ⟨_, _, _, x₃, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₃' x₃
  obtain ⟨_, _, _, x₄, x₅⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₄' x₄
  obtain ⟨hB1, hB2⟩ := le_restB (w := w) (B := B) hb
  have hrm₃c : c₃.rmem = c.rmem := by rw [grm₃, hf₂.rmem, grm₁]
  have G₁ := good_glue (H := 512 * restB b w B) restSet_glueOK d1 e₁' hI hZi (by omega)
  have G₂ := good_glue (H := 512 * restB b w B) permProg_glueOK d2 e₂' G₁.2.1 G₁.2.2 (by omega)
  have G₃ := good_glue (H := 512 * restB b w B) bfIn_glueOK d3 e₃' G₂.2.1 G₂.2.2 (by omega)
  have G₄ : NGood I W' (512 * restB b w B) (bfB b B) bfStage c₃ c₄ := by
    obtain ⟨C, hI'⟩ := bfStage_cmp hb (isPermB_permOf e₀ e₁) cr₀.crossingX cr₁.crossingX hBL c₃
      e₃'.wb_right
      (by rw [hR₃ 802 (by pomega), hctx.r802])
      (by rw [b970, hR₂ 944 (by pomega), hx' 14 (by omega)])
      (by rw [b971, hR₂ 936 (by pomega), hx' 6 (by omega)])
      (by rw [b972, hR₂ 941 (by pomega), hx' 11 (by omega)])
      (by rw [b974, hR₂ 945 (by pomega), hx' 15 (by omega)])
      (fun i hi => by rw [gnm₃]; exact hπ₂ i hi)
      (fun s hs t ht => by
        rw [gnm₃, grm₃, hmY _ (by have := rmLt hs ht; pomega), hf₂.rmem, grm₁]
        exact hF₀ s hs t ht)
      (fun s hs t ht => by
        rw [gnm₃, grm₃, hmY _ (by have := rmLt hs ht; pomega), hf₂.rmem, grm₁]
        exact hF₁ s hs t ht)
      (fun s hs t ht => by
        have := rmLt hs ht
        have h1 := G₃.2.1.1 (Y + 6 * S + (s * b + t)) (by pomega)
        rwa [hrm₃c, (hF₀ s hs t ht).2] at h1)
      (fun s hs t ht => by
        have := rmLt hs ht
        have h1 := G₃.2.1.1 (Y + 11 * S + (s * b + t)) (by pomega)
        rwa [hrm₃c, (hF₁ s hs t ht).2] at h1)
      G₃.2.1 G₃.2.2 e₄'
    exact ⟨⟨_, C.mono_H (by omega)⟩, hI', Exec.intAll e₄' d4 G₃.2.2⟩
  have G₅ := node_dij_cmp hfr h e₀ hP₀ hP₁ ℓ E' δ₀ δ₁ hδ₀ hδ₁ hM₀ hZ (by pomega) I c₄ hctx₄
    (fun d hd => by rw [hm₄' _ (by pomega) (by pomega)]; exact hTm d hd)
    (fun d hd => by rw [hm₄' _ (by pomega) (by pomega)]; exact hHm d hd)
    (fun d hd => by rw [hm₄' _ (by pomega) (by pomega)]; exact hSm d hd)
    (fun d hd => by rw [hr₄' _ (by pomega) (by pomega)]; exact hLm d hd)
    (fun v hv => by rw [hr₄' _ (by pomega) (by pomega)]; exact hD₀ v hv)
    (fun v hv => by rw [hr₄' _ (by pomega) (by pomega)]; exact hD₁ v hv)
    (fun i hi => by
      rw [hN₄ i hi, gnm₃, hmY _ (by pomega)]; exact hO₀ i hi)
    (fun i hi => by rw [hE₄ i hi]; simp only [hE', enumInv_apply e₀ hi])
    G₄.2.1 G₄.2.2 x₅
  exact G₁.seq (G₂.seq (G₃.seq (G₄.seq G₅)))

end Rest

end NegSSSP

end PlanarFlow
