module

public import PlanarFlow.NegSSSP.NodeRunC

/-!
# The Dijkstra half of a node as one run

After Bellman–Ford, a step of the recursion (`NegSSSP.step`) lowers the boundary values `E` by
`C = Σ_B |E - δ₀| + |E - δ₁|`, runs Dijkstra with a price function in each part, and takes the
least of the two distances at every vertex. `nodeDij` does all of it in **one run** on the plain
encoding of the node (`NegSSSP.NodeEnc`) held in the slots of `PlanarFlow/NegSSSP/NodeRunB.lean`
(the potentials `δ₀`, `δ₁` at the slots `4`, `5`, the vertex numbers and the values `E` of the
boundary at the slots `6`, `7`), FR-Dijkstra running twice in the low memory below the slots:

`cProg` (the lowering `C`, stored at the slot `21`) ; `partProg` for the part `0` ; `partProg`
for the part `1` ; `minProg` (the minima, written at the slot `20`).

* `node_dij_exec`: within `2 cNegMach.dij (w + 1) (m + w) + 200 m + 450 w + 70 b + 2700` steps,
  the value of `NegSSSP.step`'s `some`-branch, `(omin (dijk … P₀ …) (dijk … P₁ …)).getD 0` with
  the lowered values, at `Z + 20 M₀ + ν x` for every vertex `x` of the node; the input slots are
  kept.
* `node_dij_step`: when Bellman–Ford returns `some E` (any `mssp`, `bf`), `NegSSSP.step` is
  `some f` and the run writes `f x` at `Z + 20 M₀ + ν x`.
* `node_dij_cost_node`: the bound is at most `400 · NegCosts.node m b m₀ w₀ m₁ w₁ + 2700`
  under `cNegMach C` (`m = m₀ + m₁`, nonempty parts): the calls at the size of the node are paid
  by the terms `m lg m` of the two calls of `mssp`.
* `node_dij_cost_le`: the bound is at most `2 cNegMach.dij (w + 1) (m + w) + 1240 m + 2700`
  (`w ≤ 2m`, `b ≤ w`).

The registers of the context (`NCtx`: `m`, `w`, `b`, the slots, the bound of the work space) are
an input of the run, as is the layout of the slots above `loB m w`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Monge.FR BKMNW

variable {P : Input} {W : ℕ}

/-- Before `cProg`. -/
def cSet : Stmt := block [.copyN 500 802, .copyN 501 810, .copyN 502 809, .copyN 503 807,
  .copyN 504 808]

/-- After `cProg`: `C` stored at the slot `21`. -/
def cStore : Stmt := block [.copyN 947 824, .storeR 947 500]

/-- Before a part: the side, the base of its potential, the bases of its flags and distances. -/
def sideSet (s δr Fr Vr : ℕ) : Stmt :=
  block [.constN 830 s, .copyN 831 δr, .copyN 832 Fr, .copyN 833 Vr]

/-- Before `minProg`. -/
def mSet : Stmt := block [.constN 10 1, .copyN 230 801, .copyN 231 819, .copyN 232 820,
  .copyN 233 821, .copyN 234 822, .copyN 235 823]

/-- **The Dijkstra half of a node.** -/
def nodeDij : Stmt :=
  .seq cSet <| .seq cProg <| .seq cStore <| .seq (sideSet 0 807 819 820) <| .seq partProg <|
  .seq (sideSet 1 808 821 822) <| .seq partProg <| .seq mSet minProg

theorem cSet_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W cSet c c' k ∧ k = 5 ∧ c'.nreg 500 = c.nreg 802 ∧
      c'.nreg 501 = c.nreg 810 ∧ c'.nreg 502 = c.nreg 809 ∧ c'.nreg 503 = c.nreg 807 ∧
      c'.nreg 504 = c.nreg 808 ∧ (∀ r, (r < 500 ∨ 504 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cSet
  exec_block
  config_simp
  intro r h1; simp (disch := omega) only [upd_other]

theorem cStore_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W cStore c c' k ∧ k = 2 ∧ c'.rmem (c.nreg 824) = c.rreg 500 ∧
      (∀ a, a ≠ c.nreg 824 → c'.rmem a = c.rmem a) ∧ (∀ r, r ≠ 947 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.output = c.output := by
  unfold cStore
  exec_block
  config_simp
  exact ⟨fun a ha => by simp (disch := omega) only [upd_other],
    fun r h1 => by simp (disch := omega) only [upd_other]⟩

theorem sideSet_exec {s δr Fr Vr : ℕ} (hs : s ≤ W) (hδr : δr < 830) (hFr : Fr < 830)
    (hVr : Vr < 830) (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (sideSet s δr Fr Vr) c c' k ∧ k = 4 ∧ c'.nreg 830 = s ∧
      c'.nreg 831 = c.nreg δr ∧ c'.nreg 832 = c.nreg Fr ∧ c'.nreg 833 = c.nreg Vr ∧
      (∀ r, (r < 830 ∨ 833 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sideSet
  refine spec_step (Exec.constN hc 830 s hs) fun hw₁ => ?_
  refine spec_step (Exec.copyN hw₁ 831 δr) fun hw₂ => ?_
  refine spec_step (Exec.copyN hw₂ 832 Fr) fun hw₃ => ?_
  refine spec_step (Exec.copyN hw₃ 833 Vr) fun hw₄ => ?_
  refine spec_nil hw₄ ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals simp only [upd_apply]
  all_goals split_ifs <;> first | omega | rfl

theorem mSet_exec (c : Config) (hc : WordsBounded W c) (h1 : 1 ≤ W) :
    ∃ c' k, Exec P W mSet c c' k ∧ k = 7 ∧ c'.nreg 10 = 1 ∧ c'.nreg 230 = c.nreg 801 ∧
      c'.nreg 231 = c.nreg 819 ∧ c'.nreg 232 = c.nreg 820 ∧ c'.nreg 233 = c.nreg 821 ∧
      c'.nreg 234 = c.nreg 822 ∧ c'.nreg 235 = c.nreg 823 ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mSet
  exec_block
  all_goals try omega
  config_simp

theorem NCtx.of' {m w b Z M₀ : ℕ} {c c' : Config} (h : NCtx m w b Z M₀ c)
    (hr : ∀ r, 800 ≤ r → r < 826 → c'.nreg r = c.nreg r) : NCtx m w b Z M₀ c' :=
  ⟨(hr 800 (by omega) (by omega)).trans h.r800, (hr 801 (by omega) (by omega)).trans h.r801,
    (hr 802 (by omega) (by omega)).trans h.r802,
    fun k hk => (hr (803 + k) (by omega) (by omega)).trans (h.slot k hk),
    (hr 825 (by omega) (by omega)).trans h.r825⟩

section Node

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

set_option maxHeartbeats 4000000 in
/-- **The Dijkstra half of a node as one run** (see the module docstring). -/
theorem node_dij_exec (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr) {P₀ P₁ : Finset D}
    {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} (h : NodeEnc N P₀ P₁ m w e ν ι)
    {β : ℕ → V} (hβ : IsEnum b β (bdry N P₀ P₁)) (hP₀ : P₀.Nonempty) (hP₁ : P₁.Nonempty)
    (ℓ : D → ℤ) (E δ₀ δ₁ : V → ℤ) (hδ₀ : (pg N P₀ ℓ).IsPot δ₀) (hδ₁ : (pg N P₁ ℓ).IsPot δ₁)
    {Z M₀ W' : ℕ} (hM₀ : M₀ = m + w + 1) (hZ : loB m w ≤ Z) (hW : Z + 22 * M₀ ≤ W')
    (I : Input) (c : Config) (hc : WordsBounded W' c) (hctx : NCtx m w b Z M₀ c)
    (hTm : ∀ d < m, c.nmem (Z + 0 * M₀ + d) = encT N e ν d)
    (hHm : ∀ d < m, c.nmem (Z + 1 * M₀ + d) = encH N e ν d)
    (hSm : ∀ d < m, c.nmem (Z + 2 * M₀ + d) = encS P₀ e d)
    (hLm : ∀ d < m, c.rmem (Z + 3 * M₀ + d) = ℓ (e d))
    (hD₀ : ∀ v < w, c.rmem (Z + 4 * M₀ + v) = δ₀ (ι v))
    (hD₁ : ∀ v < w, c.rmem (Z + 5 * M₀ + v) = δ₁ (ι v))
    (hNm : ∀ i < b, c.nmem (Z + 6 * M₀ + i) = ν (β i))
    (hEm : ∀ i < b, c.rmem (Z + 7 * M₀ + i) = E (β i)) :
    ∃ c' k, Exec I W' nodeDij c c' k ∧
      k ≤ 2 * (cNegMach C).dij (w + 1) (m + w) + 200 * m + 450 * w + 70 * b + 2700 ∧
      (∀ x ∈ verts N (P₀ ∪ P₁), c'.rmem (Z + 20 * M₀ + ν x) =
        ((omin (dijk N fr P₀ ℓ (bdry N P₀ P₁)
            (fun y => E y - ∑ v ∈ bdry N P₀ P₁, (|E v - δ₀ v| + |E v - δ₁ v|)) δ₀ (some x))
          (dijk N fr P₁ ℓ (bdry N P₀ P₁)
            (fun y => E y - ∑ v ∈ bdry N P₀ P₁, (|E v - δ₀ v| + |E v - δ₁ v|)) δ₁ (some x))).getD 0
          : ℤ)) ∧
      (∀ a, Z ≤ a → a < Z + 8 * M₀ → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      c'.output = c.output := by
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
    part_exec C hfr h hβ (s := 0) (by pomega) (by simpa [partOf] using hP₀) ℓ E δ₀ Cz
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
  obtain ⟨c₇, k₇, e₇, hk₇, hF₇, hV₇, hR₇, hnm₇, hrm₇, ho₇⟩ :=
    part_exec C hfr h hβ (s := 1) le_rfl (by simpa [partOf] using hP₁) ℓ E δ₁ Cz
      (by simpa [partOf] using hδ₁) hM₀ hZ hW (δb := Z + 5 * M₀) (Fs := Z + 18 * M₀)
      (Vs := Z + 19 * M₀) (Or.inr rfl) (by pomega) (by pomega) (by pomega) (by pomega) I c₆
      e₆.wb_right hctx₆ t830 (by rw [t831, hctx₅.slot 5 (by pomega)])
      (by rw [t832, hctx₅.slot 18 (by pomega)]) (by rw [t833, hctx₅.slot 19 (by pomega)])
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
      (by rw [hrm₆, hr₅₄ _ (by pomega) (Or.inr rfl), hst₃])
  have hctx₇ : NCtx m w b Z M₀ c₇ := hctx₆.of hR₇
  -- the minima
  obtain ⟨c₈, k₈, e₈, hk₈, m10, m230, m231, m232, m233, m234, m235, hnm₈, hrm₈, ho₈⟩ :=
    mSet_exec (P := I) c₇ e₇.wb_right (by pomega)
  have hML : MinLay w (Z + 16 * M₀) (Z + 17 * M₀) (Z + 18 * M₀) (Z + 19 * M₀) (Z + 20 * M₀) W' :=
    ⟨by pomega, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega⟩
  have hMI : MinIn w (Z + 16 * M₀) (Z + 17 * M₀) (Z + 18 * M₀) (Z + 19 * M₀) (Z + 20 * M₀)
      (oNum N P₀ P₁ ν ι (dijk N fr (partOf P₀ P₁ 0) ℓ (bdry N P₀ P₁) (fun y => E y - Cz) δ₀))
      (oNum N P₀ P₁ ν ι (dijk N fr (partOf P₀ P₁ 1) ℓ (bdry N P₀ P₁) (fun y => E y - Cz) δ₁))
      c₈ := by
    refine ⟨m10, by rw [m230, hctx₇.r801], by rw [m231, hctx₇.slot 16 (by pomega)],
      by rw [m232, hctx₇.slot 17 (by pomega)], by rw [m233, hctx₇.slot 18 (by pomega)],
      by rw [m234, hctx₇.slot 19 (by pomega)], by rw [m235, hctx₇.slot 20 (by pomega)],
      fun v hv => ?_, fun v hv => ?_, fun v hv z hz => ?_, fun v hv z hz => ?_⟩
    · rw [hnm₈, hnm₇ _ (by pomega) (Or.inr (by pomega)) (Or.inl (by pomega)), hnm₆]
      exact hF₅ v hv
    · rw [hnm₈]; exact hF₇ v hv
    · rw [hrm₈, hrm₇ _ (by pomega) (Or.inr (by pomega)) (Or.inl (by pomega)), hrm₆]
      exact hV₅ v hv z hz
    · rw [hrm₈]; exact hV₇ v hv z hz
  obtain ⟨c₉, k₉, e₉, hk₉, hv₉, hrm₉, hnm₉, -, ho₉⟩ := minProg_exec (P := I) hML c₈ e₈.wb_right hMI
  have hout : ∀ x ∈ verts N (P₀ ∪ P₁), c₉.rmem (Z + 20 * M₀ + ν x) =
      ((omin (dijk N fr (partOf P₀ P₁ 0) ℓ (bdry N P₀ P₁) (fun y => E y - Cz) δ₀ (some x))
        (dijk N fr (partOf P₀ P₁ 1) ℓ (bdry N P₀ P₁) (fun y => E y - Cz) δ₁ (some x))).getD 0
        : ℤ) := by
    intro x hx
    have e : ∀ Dk : Option V → Option ℤ, oNum N P₀ P₁ ν ι Dk (ν x) = Dk (some x) := fun Dk => by
      unfold oNum; rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨x, hx, rfl⟩), h.inv x hx]
    rw [hv₉ _ (h.lt x hx), e, e]
  refine ⟨c₉, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + (k₈ + k₉))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉))))))),
    by pomega, fun x hx => ?_, fun a h1 h2 => ⟨?_, ?_⟩, ?_⟩
  · rw [hout x hx]
    simp [partOf]
  · rw [hnm₉, hnm₈, hnm₇ a h1 (Or.inl (by pomega)) (Or.inl (by pomega)), hnm₆,
      hn₅₄ a h1 (by pomega)]
  · rw [hrm₉ a (Or.inl (by pomega)), hrm₈, hrm₇ a h1 (Or.inl h2) (Or.inl (by pomega)), hrm₆,
      hr₅₄ a h1 (Or.inl h2), hr₃ a (by pomega)]
  · rw [ho₉, ho₈, ho₇, ho₆, ho₅, ho₄, ho₃, ho₂, ho₁]

/-- **With Bellman–Ford's answer `some E`, the run writes `NegSSSP.step`'s potential.** -/
theorem node_dij_step (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr) {P₀ P₁ : Finset D}
    {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} (h : NodeEnc N P₀ P₁ m w e ν ι)
    {β : ℕ → V} (hβ : IsEnum b β (bdry N P₀ P₁)) (hP₀ : P₀.Nonempty) (hP₁ : P₁.Nonempty)
    (mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ)
    (bf : DDG V → DDG V → Option (V → ℤ))
    (ℓ : D → ℤ) (E δ₀ δ₁ : V → ℤ) (hδ₀ : (pg N P₀ ℓ).IsPot δ₀) (hδ₁ : (pg N P₁ ℓ).IsPot δ₁)
    (hbf : bf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁))
      (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) = some E)
    {Z M₀ W' : ℕ} (hM₀ : M₀ = m + w + 1) (hZ : loB m w ≤ Z) (hW : Z + 22 * M₀ ≤ W')
    (I : Input) (c : Config) (hc : WordsBounded W' c) (hctx : NCtx m w b Z M₀ c)
    (hTm : ∀ d < m, c.nmem (Z + 0 * M₀ + d) = encT N e ν d)
    (hHm : ∀ d < m, c.nmem (Z + 1 * M₀ + d) = encH N e ν d)
    (hSm : ∀ d < m, c.nmem (Z + 2 * M₀ + d) = encS P₀ e d)
    (hLm : ∀ d < m, c.rmem (Z + 3 * M₀ + d) = ℓ (e d))
    (hD₀ : ∀ v < w, c.rmem (Z + 4 * M₀ + v) = δ₀ (ι v))
    (hD₁ : ∀ v < w, c.rmem (Z + 5 * M₀ + v) = δ₁ (ι v))
    (hNm : ∀ i < b, c.nmem (Z + 6 * M₀ + i) = ν (β i))
    (hEm : ∀ i < b, c.rmem (Z + 7 * M₀ + i) = E (β i)) :
    ∃ f, step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = some f ∧
      ∃ c' k, Exec I W' nodeDij c c' k ∧
        k ≤ 2 * (cNegMach C).dij (w + 1) (m + w) + 200 * m + 450 * w + 70 * b + 2700 ∧
        (∀ x ∈ verts N (P₀ ∪ P₁), c'.rmem (Z + 20 * M₀ + ν x) = f x) ∧
        c'.output = c.output := by
  obtain ⟨c', k, ex, hk, hout, -, ho⟩ := node_dij_exec C hfr h hβ hP₀ hP₁ ℓ E δ₀ δ₁ hδ₀ hδ₁
    hM₀ hZ hW I c hc hctx hTm hHm hSm hLm hD₀ hD₁ hNm hEm
  refine ⟨fun v => (omin (dijk N fr P₀ ℓ (bdry N P₀ P₁)
      (fun x => E x - ∑ b ∈ bdry N P₀ P₁, (|E b - δ₀ b| + |E b - δ₁ b|)) δ₀ (some v))
      (dijk N fr P₁ ℓ (bdry N P₀ P₁)
      (fun x => E x - ∑ b ∈ bdry N P₀ P₁, (|E b - δ₀ b| + |E b - δ₁ b|)) δ₁ (some v))).getD 0,
    by simp only [step, hbf], c', k, ex, hk, fun x hx => hout x hx, ho⟩

/-- The bound of `node_dij_exec` against the size of the node. -/
theorem node_dij_cost_le (C : ℕ) {m w b : ℕ} (hw : w ≤ 2 * m) (hb : b ≤ w) :
    2 * (cNegMach C).dij (w + 1) (m + w) + 200 * m + 450 * w + 70 * b + 2700 ≤
      2 * (cNegMach C).dij (w + 1) (m + w) + 1240 * m + 2700 := by
  omega

lemma lg_two_mul_le (n : ℕ) : lg (2 * n) ≤ lg n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lg]
  · unfold lg
    rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]

lemma mul_lg_split {m m₀ m₁ : ℕ} (hm : m = m₀ + m₁) :
    m * lg m ≤ 2 * (m₀ * lg m₀ + m₁ * lg m₁) + 2 * m := by
  rcases le_total m₁ m₀ with h | h
  · have hl : lg m ≤ lg m₀ + 1 := (lg_mono (by omega : m ≤ 2 * m₀)).trans (lg_two_mul_le m₀)
    have h1 : m * lg m ≤ m * (lg m₀ + 1) := Nat.mul_le_mul_left _ hl
    have h2 : m₁ * lg m₀ ≤ m₀ * lg m₀ := Nat.mul_le_mul_right _ h
    have e : m * (lg m₀ + 1) = m₀ * lg m₀ + m₁ * lg m₀ + m := by rw [hm]; ring
    omega
  · have hl : lg m ≤ lg m₁ + 1 := (lg_mono (by omega : m ≤ 2 * m₁)).trans (lg_two_mul_le m₁)
    have h1 : m * lg m ≤ m * (lg m₁ + 1) := Nat.mul_le_mul_left _ hl
    have h2 : m₀ * lg m₁ ≤ m₁ * lg m₁ := Nat.mul_le_mul_right _ h
    have e : m * (lg m₁ + 1) = m₀ * lg m₁ + m₁ * lg m₁ + m := by rw [hm]; ring
    omega

/-- **The bound of `node_dij_exec` against the charge of the node**: at a node of
`m = m₀ + m₁` darts with nonempty parts (`w ≤ 2m` vertex numbers, `b ≤ w`), at most
`400 · NegCosts.node` under `cNegMach C` (any `w₀`, `w₁`), plus `2700`: the calls of Dijkstra
at the size of the node are paid by the terms `m lg m` of the two calls of `mssp`. -/
theorem node_dij_cost_node (C : ℕ) {m b m₀ w₀ m₁ w₁ w : ℕ} (hm : m = m₀ + m₁)
    (h₀ : 1 ≤ m₀) (h₁ : 1 ≤ m₁) (hw : w ≤ 2 * m) (hb : b ≤ w) :
    2 * (cNegMach C).dij (w + 1) (m + w) + 200 * m + 450 * w + 70 * b + 2700 ≤
      400 * (cNegMach C).node m b m₀ w₀ m₁ w₁ + 2700 := by
  have hl : lg (w + 1) ≤ lg m + 2 := by
    have h1 := lg_mono (show w + 1 ≤ 2 * (2 * m) by omega)
    have h2 := lg_two_mul_le (2 * m)
    have h3 := lg_two_mul_le m
    omega
  have hdij : (cNegMach C).dij (w + 1) (m + w) ≤ 37800 * (m * lg m) + 75600 * m := by
    simp only [cNegMach]
    calc 6300 * (w + 1 + (m + w)) * lg (w + 1) ≤ 6300 * (6 * m) * (lg m + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hl
      _ = 37800 * (m * lg m) + 75600 * m := by ring
  have hsplit := mul_lg_split hm
  have hnode : 1000 * m + 32886 * 2372500000 * (m₀ * lg m₀) +
      32886 * 2372500000 * (m₁ * lg m₁) ≤ (cNegMach C).node m b m₀ w₀ m₁ w₁ := by
    simp only [NegCosts.node, cNegMach]
    have a := Nat.mul_le_mul_left (32886 * 2372500000)
      (Nat.le_add_right (m₀ * lg m₀) (b ^ 2 * lg m₀))
    have b' := Nat.mul_le_mul_left (32886 * 2372500000)
      (Nat.le_add_right (m₁ * lg m₁) (b ^ 2 * lg m₁))
    omega
  omega

end Node

end NegSSSP

end PlanarFlow
