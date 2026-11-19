module

public import PlanarFlow.NegSSSP.NodeRun
public import PlanarFlow.NegSSSP.NodeRunD
public import PlanarFlow.NegSSSP.NodeRunE

/-!
# The pieces of the whole node of the negative-length recursion as one run

`nodeProg` runs one step of the recursion (`NegSSSP.step`) at a node of the decomposition by
simple cycles (`SplitF`) **in one configuration**: the plain encoding of the node (`NodeEnc`)
in the slots of `PlanarFlow/NegSSSP/NodeRunB.lean` (`NCtx`), and a scratch area of sixteen
regions `Y + j S` (`XCtx`, registers `930 + j`) above the slots:

1. `bdSet ; bdryProg`: the boundary, listed by vertex number (`bdryProg_node'`);
2. the two parts (`kPart`, `PlanarFlow/NegSSSP/NodeRunD.lean`), each after `partSet`: the
   corners, Klein's program from the encoding of the one-face instance in a slot, the reading
   into the matrices of `bfStartP`; the part with the smaller work space of Klein's program runs
   first, so that the natural memory left by the first run is bounded by the work space of the
   second;
3. `restProg`: `permProg` (the order `π`), `bfStage` (Bellman–Ford from the matrices,
   `PlanarFlow/NegSSSP/NodeRunE.lean`, the values `E` written at the slot `7`, the vertex
   numbers of the order of the part `0` at the slot `6`, the flag in `r990`), and `nodeDij` (the
   Dijkstra half, `PlanarFlow/NegSSSP/NodeRun.lean`).

* `rest_exec`: the run of `restProg` from the matrices and orders of the two parts: an
  outcome `o`, a `PotOut` output of the union of the two dense distance graphs, and for every
  `bf` answering `o` the output of `NegSSSP.step` (`none` and `r990 ≠ 0`, or `some f` with
  `r990 = 0` and `f x` at the slot `20`); `nodeDij` names only the registers `< 950`
  (`nodeDij_regsOK`), so the flag survives it (`exec_frame`).
* `bdryProg_node'`: the boundary listed by the vertex numbers of an enumeration.
* `kpair_exec`: the two parts as one run (`KPartRun` twice), the part with the smaller work space
  of Klein's program first (the natural memory left below its bound is then below the bound of
  the second run, as `Klein.klein_exec_of_enc` requires; `kleinProgMem` leaves its work space
  bounded).
* `klay_of`: the layout of a part from the global layout of a node; `nodeProg`: the whole node.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge Monge.FR

variable {I : Input} {W : ℕ}

/-- **The scratch area of a node**: the registers `930 + j` (`j < 16`) hold `Y + j S`. -/
structure XCtx (Y S : ℕ) (c : Config) : Prop where
  reg : ∀ j < 16, c.nreg (930 + j) = Y + j * S

theorem XCtx.of {Y S : ℕ} {c c' : Config} (h : XCtx Y S c)
    (hr : ∀ r, 930 ≤ r → r < 946 → c'.nreg r = c.nreg r) : XCtx Y S c' :=
  ⟨fun j hj => (hr (930 + j) (by omega) (by omega)).trans (h.reg j hj)⟩

/-- `nodeDij` names only the registers below `950`. -/
theorem nodeDij_regsOK : nodeDij.regsOK (fun r => decide (r < 950)) = true := by kernel_rfl

theorem nodeDij_noInp : nodeDij.noInp = true := by kernel_rfl

theorem nodeDij_noRand : nodeDij.noRand = true := by kernel_rfl

/-- Before `permProg`: `b`, the orders of the two parts (`Y + 4 S`, `Y + 9 S`), the inverse
table (`Y + 13 S`), `π` (`Y + 14 S`). -/
def restSet : Stmt :=
  block [.constN 10 1, .copyN 220 802, .copyN 221 934, .copyN 222 939, .copyN 223 943,
    .copyN 224 944]

/-- Before `bfStage`: `π`, the matrices of the two parts (`Y + 6 S`, `Y + 11 S`), the order of
the part `0`, the real scratch (`Y + 15 S`). -/
def bfIn : Stmt :=
  block [.copyN 970 944, .copyN 971 936, .copyN 972 941, .copyN 973 934, .copyN 974 945]

/-- **The end of a node**: `π`, Bellman–Ford, the Dijkstra half. -/
def restProg : Stmt := .seq restSet <| .seq permProg <| .seq bfIn <| .seq bfStage nodeDij

theorem restSet_exec (c : Config) (hc : WordsBounded W c) (h1 : 1 ≤ W) :
    ∃ c' k, Exec I W restSet c c' k ∧ k = 6 ∧ c'.nreg 10 = 1 ∧ c'.nreg 220 = c.nreg 802 ∧
      c'.nreg 221 = c.nreg 934 ∧ c'.nreg 222 = c.nreg 939 ∧ c'.nreg 223 = c.nreg 943 ∧
      c'.nreg 224 = c.nreg 944 ∧ (∀ r, r ≠ 10 → (r < 220 ∨ 224 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold restSet
  exec_block
  all_goals try omega
  config_simp
  intro r h1 h2; simp (disch := omega) only [upd_other]

theorem bfIn_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec I W bfIn c c' k ∧ k = 5 ∧ c'.nreg 970 = c.nreg 944 ∧
      c'.nreg 971 = c.nreg 936 ∧ c'.nreg 972 = c.nreg 941 ∧ c'.nreg 973 = c.nreg 934 ∧
      c'.nreg 974 = c.nreg 945 ∧ (∀ r, (r < 970 ∨ 974 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bfIn
  exec_block
  config_simp
  intro r h1; simp (disch := omega) only [upd_other]

section Rest

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

set_option maxHeartbeats 4000000 in
/-- **The end of a node as one run.** From the orders `β₀`, `β₁` of the boundary (vertex
numbers at `Y + 4 S`, `Y + 9 S`) in which the dense distance graphs `H₀`, `H₁` of the parts
cross, and their matrices of `bfStartP` (at `Y + 6 S`, `Y + 11 S`), `restProg` computes `π`, runs
Bellman–Ford and the Dijkstra half: there is an outcome `o`, a `PotOut` output of
`H₀.join H₁` (as `BFDDGSpec` requires of `bf`), such that for every `bf` answering `o` on the
node, `NegSSSP.step` is `none` and `r990 ≠ 0`, or `some f` with `r990 = 0` and `f x` at
`Z + 20 M₀ + ν x` for every vertex `x` of the node. -/
theorem rest_exec (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {P₀ P₁ : Finset D} {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}
    (h : NodeEnc N P₀ P₁ m w e ν ι) (hP₀ : P₀.Nonempty) (hP₁ : P₁.Nonempty)
    (ℓ : D → ℤ) (δ₀ δ₁ : V → ℤ) (hδ₀ : (pg N P₀ ℓ).IsPot δ₀) (hδ₁ : (pg N P₁ ℓ).IsPot δ₁)
    {β₀ β₁ : ℕ → V} (e₀ : IsEnum b β₀ (bdry N P₀ P₁)) (e₁ : IsEnum b β₁ (bdry N P₀ P₁))
    (cr₀ : CrossingO b (fun i j => (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).len (β₀ i) (β₀ j)))
    (cr₁ : CrossingO b (fun i j => (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)).len (β₁ i) (β₁ j)))
    {Z M₀ Y S W' : ℕ} (hM₀ : M₀ = m + w + 1) (hZ : loB m w ≤ Z) (hbZ : bfWP b < Z)
    (hY : Z + 22 * M₀ ≤ Y) (hSw : w ≤ S) (hSb : b * b ≤ S) (hW : Y + 16 * S ≤ W')
    (c : Config) (hc : WordsBounded W' c) (hctx : NCtx m w b Z M₀ c) (hx : XCtx Y S c)
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
          (matOf (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) β₁ s t : ℝ)) :
    ∃ c' k, ∃ o : Option (V → ℤ), Exec I W' restProg c c' k ∧
      k ≤ bfCostP b + 4 * bfWP b + 22 * (b * b) + 2 * (cNegMach C).dij (w + 1) (m + w) +
        232 * m + 450 * w + 92 * b + 2917 ∧
      PotOut ((childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).join
        (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁))) o ∧
      (∀ bf : DDG V → DDG V → Option (V → ℤ),
        bf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) =
          o →
        (step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = none ∧ c'.nreg 990 ≠ 0) ∨
        (∃ f, step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = some f ∧ c'.nreg 990 = 0 ∧
          ∀ x ∈ verts N (P₀ ∪ P₁), c'.rmem (Z + 20 * M₀ + ν x) = f x)) ∧
      c'.output = c.output := by
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
  obtain ⟨c₅, k₅, e₅, hk₅, hout₅, -, ho₅'⟩ := node_dij_exec C hfr h e₀ hP₀ hP₁ ℓ E' δ₀ δ₁ hδ₀ hδ₁
    hM₀ hZ (by pomega) I c₄ e₄'.wb_right hctx₄
    (fun d hd => by rw [hm₄' _ (by pomega) (by pomega)]; exact hTm d hd)
    (fun d hd => by rw [hm₄' _ (by pomega) (by pomega)]; exact hHm d hd)
    (fun d hd => by rw [hm₄' _ (by pomega) (by pomega)]; exact hSm d hd)
    (fun d hd => by rw [hr₄' _ (by pomega) (by pomega)]; exact hLm d hd)
    (fun v hv => by rw [hr₄' _ (by pomega) (by pomega)]; exact hD₀ v hv)
    (fun v hv => by rw [hr₄' _ (by pomega) (by pomega)]; exact hD₁ v hv)
    (fun i hi => by
      rw [hN₄ i hi, gnm₃, hmY _ (by pomega)]; exact hO₀ i hi)
    (fun i hi => by rw [hE₄ i hi]; simp only [hE', enumInv_apply e₀ hi])
  obtain ⟨d, e₅', hA₅, hK₅, ho₅⟩ := exec_frame e₅ nodeDij_regsOK nodeDij_noInp nodeDij_noRand
  have h990 : d.nreg 990 = c₄.nreg 990 := hK₅.nreg 990 (by decide)
  -- the outcome
  have hnn₀ := redLen_nonneg hδ₀
  have hnn₁ := redLen_nonneg hδ₁
  have hpot := potOut_join_of_outcomeO (H₁ := childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁))
    (H₂ := childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) rfl rfl e₀ e₁
    (fun v hv => childDDG_loop_nonneg hmssp hnn₀ hv)
    (fun v hv => childDDG_loop_nonneg hmssp hnn₁ hv) hout₄
  refine ⟨d, k₁ + (k₂ + (k₃ + (k₄ + k₅))), if c₄.nreg 990 = 0 then some E' else none,
    Exec.seq e₁' (Exec.seq e₂' (Exec.seq e₃' (Exec.seq e₄' e₅'))), ?_, hpot, fun bf hbf => ?_,
    by rw [ho₅, ho₅', ho₄, go₃, hf₂.out, go₁]⟩
  · have := node_dij_cost_le C (m := m) (w := w) (b := b) h.w2 hbw
    pomega
  · by_cases hF : c₄.nreg 990 = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hF)] at hbf
      refine Or.inr ⟨fun v => (omin (dijk N fr P₀ ℓ (bdry N P₀ P₁)
          (fun x => E' x - ∑ b ∈ bdry N P₀ P₁, (|E' b - δ₀ b| + |E' b - δ₁ b|)) δ₀ (some v))
          (dijk N fr P₁ ℓ (bdry N P₀ P₁)
          (fun x => E' x - ∑ b ∈ bdry N P₀ P₁, (|E' b - δ₀ b| + |E' b - δ₁ b|)) δ₁ (some v))).getD 0,
        by simp only [step, hbf], by rw [h990]; exact hF, fun x hx => ?_⟩
      rw [hA₅.rmem _ (by have := h.lt x hx; pomega)]
      exact hout₅ x hx
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hF)] at hbf
      exact Or.inl ⟨by simp only [step, hbf], by rw [h990]; exact hF⟩

end Rest

/-! ### The boundary -/

/-- Before `bdryProg`: `r10 = 1`, `m`, the slots of the tails, heads and sides, `w`, the marks
(`Y`) and the list (`Y + 2 S`). -/
def bdSet : Stmt :=
  block [.constN 10 1, .copyN 200 800, .copyN 201 803, .copyN 202 804, .copyN 206 805,
    .copyN 207 801, .copyN 208 930, .copyN 209 932]

theorem bdSet_exec (c : Config) (hc : WordsBounded W c) (h1 : 1 ≤ W) :
    ∃ c' k, Exec I W bdSet c c' k ∧ k = 8 ∧ c'.nreg 10 = 1 ∧ c'.nreg 200 = c.nreg 800 ∧
      c'.nreg 201 = c.nreg 803 ∧ c'.nreg 202 = c.nreg 804 ∧ c'.nreg 206 = c.nreg 805 ∧
      c'.nreg 207 = c.nreg 801 ∧ c'.nreg 208 = c.nreg 930 ∧ c'.nreg 209 = c.nreg 932 ∧
      (∀ r, r ≠ 10 → (r < 200 ∨ 209 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bdSet
  exec_block
  all_goals try omega
  config_simp
  intro r h1 h2; simp (disch := omega) only [upd_other]

section Bdry

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

/-- **The boundary of a node on the machine, by vertex numbers**: as `bdryProg_node`, with the
cells of the list the vertex numbers `ν (src j)` of an enumeration `src` of the boundary. -/
theorem bdryProg_node' {P₀ P₁ : Finset D} {m w : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}
    (h : NodeEnc N P₀ P₁ m w e ν ι) {Tb Hb Sb Mb Bb : ℕ}
    (hL : BdLay m w Tb Hb Sb Mb Bb W (encT N e ν) (encH N e ν) (encS P₀ e)) (c : Config)
    (hc : WordsBounded W c) (hI : BdIn m w Tb Hb Sb Mb Bb (encT N e ν) (encH N e ν) (encS P₀ e) c) :
    ∃ c' k, ∃ src : ℕ → V, Exec I W bdryProg c c' k ∧ k ≤ 61 * m + 12 ∧
      IsEnum (bdry N P₀ P₁).card src (bdry N P₀ P₁) ∧
      (∀ j < (bdry N P₀ P₁).card, c'.nmem (Bb + j) = ν (src j)) ∧
      (∀ a, (a < Mb ∨ Mb + 2 * w ≤ a) → (a < Bb ∨ Bb + w ≤ a) → c'.nmem a = c.nmem a) ∧
      BFr c c' := by
  classical
  obtain ⟨c', k, hex, hk, -, hl, hm, hf⟩ := bdryProg_exec (P := I) hL c hc hI
  set L := bList (encT N e ν) (encH N e ν) (encS P₀ e) m w with hLdef
  have hen := bdry_enum h
  have hcard : L.length = (bdry N P₀ P₁).card := hen.card
  have hmem : ∀ v, v ∈ L ↔ v < w ∧ IsBd (encT N e ν) (encH N e ν) (encS P₀ e) m v := by
    intro v; simp [L, bList, IsBd]
  have hget : ∀ j < L.length, L.getD j 0 ∈ L := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
  have hnum : ∀ j < L.length, ν (ι (L.getD j 0)) = L.getD j 0 := fun j hj => by
    obtain ⟨-, hb⟩ := (hmem _).1 (hget j hj)
    obtain ⟨x, hx, hxv⟩ := inSide_num h hb.1
    rw [← hxv, h.inv x hx]
  have := h.w2
  refine ⟨c', k, fun j => ι (L.getD j 0), hex, by omega, hcard ▸ hen, fun j hj => ?_, hm, hf⟩
  rw [hl j (hcard ▸ hj), hnum j (hcard ▸ hj)]

end Bdry

/-! ### The two parts -/

/-- Before a part: the list (`Y + 2 S`), the zone `z` of the part (`Y + (3 + 5 z + i) S`),
the base of its potential (`r δr`). -/
def partSet (z δr : ℕ) : Stmt :=
  block [.copyN 960 932, .copyN 961 (933 + 5 * z), .copyN 962 (934 + 5 * z),
    .copyN 963 (935 + 5 * z), .copyN 964 (936 + 5 * z), .copyN 965 (937 + 5 * z),
    .copyN 966 δr]

theorem partSet_exec {z δr : ℕ} (hz : z ≤ 1) (hδr : δr < 930) (c : Config)
    (hc : WordsBounded W c) :
    ∃ c' k, Exec I W (partSet z δr) c c' k ∧ k = 7 ∧ c'.nreg 960 = c.nreg 932 ∧
      c'.nreg 961 = c.nreg (933 + 5 * z) ∧ c'.nreg 962 = c.nreg (934 + 5 * z) ∧
      c'.nreg 963 = c.nreg (935 + 5 * z) ∧ c'.nreg 964 = c.nreg (936 + 5 * z) ∧
      c'.nreg 965 = c.nreg (937 + 5 * z) ∧ c'.nreg 966 = c.nreg δr ∧
      (∀ r, (r < 960 ∨ 966 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold partSet
  exec_block
  simp (disch := omega) only [Config.nmem_mk, Config.rmem_mk, Config.output_mk, upd_other,
    upd_same]
  and_intros
  all_goals first | trivial | rfl | (intro r hr; simp (disch := omega) only [upd_other])

/-- The encoding in a slot survives a run keeping its cells. -/
theorem KSlot.of {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D}
    {ℓ : D → ℤ} {nD : ℕ} {σ : D ≃ Fin nD} {B n β Rk W' : ℕ} {P : Input} {c d : Config}
    (h : KSlot M k g S ℓ σ B n β Rk W' P c)
    (hr : ∀ i < 3 * nD + 3, d.rmem (Rk + i) = c.rmem (Rk + i))
    (hn : ∀ i ≤ B + 16 * (n + 1), d.nmem (β + i) = c.nmem (β + i)) :
    KSlot M k g S ℓ σ B n β Rk W' P d where
  dat := ⟨h.dat.lt, h.dat.le, h.dat.len, fun i hi => (hn i hi).trans (h.dat.mem i hi)⟩
  wt x := by
    have := (σ x).2
    rw [hr _ (by unfold Klein.aWT; omega)]; exact h.wt x
  ph x := by
    have := (σ x).2
    rw [hr _ (by unfold Klein.aPH; omega)]; exact h.ph x
  tl := by rw [hr _ (by unfold Klein.aTL; omega)]; exact h.tl
  th := by rw [hr _ (by unfold Klein.aTH; omega)]; exact h.th
  h0 := by rw [hr _ (by unfold Klein.aH0; omega)]; exact h.h0

/-- **The two parts**: `partSet` and `kPart` for the part run first (zone `zf`), then for the
other one (zone `zs`). -/
def kPair (zf δrf kf nDf nf Bwf lenf βf Rkf Pbf Lf : ℕ) (Wrf : ℤ)
    (zs δrs ks nDs ns Bws lens βs Rks Pbs Ls : ℕ) (Wrs : ℤ) : Stmt :=
  .seq (partSet zf δrf) <| .seq (kPart kf nDf nf Bwf lenf βf Rkf Pbf Lf Wrf) <|
  .seq (partSet zs δrs) (kPart ks nDs ns Bws lens βs Rks Pbs Ls Wrs)

section Pair

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

set_option maxHeartbeats 4000000 in
/-- **The two parts of a node as one run.** Two runs of `kPart` (`KPartRun`, from
`kpart_exec`), in the zones `zf ≠ zs` of the scratch area, the first with the smaller work
space of Klein's program (`Kwf ≤ Kws`): the orders and the matrices of both parts, in their
zones. -/
theorem kpair_exec {P P₀ P₁ : Finset D} {ℓ : D → ℤ}
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}
    {Xf Xs : Finset D} {δf δs : V → ℤ}
    {fdf : FaceData N Xf (bdry N P₀ P₁)} {nf Bwf : ℕ}
    {σf : Klein.SrcD fdf.DQ fdf.k ≃ Fin (Fintype.card (Klein.SrcD fdf.DQ fdf.k))} {Pkf : Input}
    (hf : KPartRun N P P₀ P₁ Xf ℓ δf mssp fdf nf Bwf σf Pkf)
    {fds : FaceData N Xs (bdry N P₀ P₁)} {ns Bws : ℕ}
    {σs : Klein.SrcD fds.DQ fds.k ≃ Fin (Fintype.card (Klein.SrcD fds.DQ fds.k))} {Pks : Input}
    (hs : KPartRun N P P₀ P₁ Xs ℓ δs mssp fds ns Bws σs Pks)
    {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} (hN : NodeEnc N P₀ P₁ m w e ν ι)
    {src : ℕ → V} (hsrc : IsEnum b src (bdry N P₀ P₁))
    {zf zs δrf δrs : ℕ} (hzf : zf ≤ 1) (hzs : zs ≤ 1) (hz : zf ≠ zs)
    (hδrf : 752 ≤ δrf ∧ δrf < 900) (hδrs : 752 ≤ δrs ∧ δrs < 900)
    (Lf Pbf βf Rkf δbf Ls Pbs βs Rks δbs Y S W' : ℕ) (I : Input) (c : Config)
    (hKf : KLay b w fdf.k (Fintype.card (Klein.SrcD fdf.DQ fdf.k)) nf (Bwf + 16 * (nf + 1)) Lf
      (Y + 2 * S) Pbf δbf (Y + (3 + 5 * zf) * S) S βf Rkf W')
    (hKs : KLay b w fds.k (Fintype.card (Klein.SrcD fds.DQ fds.k)) ns (Bws + 16 * (ns + 1)) Ls
      (Y + 2 * S) Pbs δbs (Y + (3 + 5 * zs) * S) S βs Rks W')
    (hWLf : ((Klein.srcW (fdf.P'.image fdf.e) (faceLen fdf.P' fdf.e (redLen N ℓ δf)) : ℤ) : ℝ) ≤
      2 ^ Lf)
    (hWLs : ((Klein.srcW (fds.P'.image fds.e) (faceLen fds.P' fds.e (redLen N ℓ δs)) : ℤ) : ℝ) ≤
      2 ^ Ls)
    (hKK : Bwf + 16 * (nf + 1) ≤ Bws + 16 * (ns + 1)) (hKY : Bws + 16 * (ns + 1) < Y)
    (hnY : 3 * Fintype.card (Klein.SrcD fdf.DQ fdf.k) + 3 ≤ Y ∧
      3 * Fintype.card (Klein.SrcD fds.DQ fds.k) + 3 ≤ Y)
    (hIn : Y + 13 * S ≤ Pbs ∧ Y + 13 * S ≤ βs ∧ Y + 13 * S ≤ Rks)
    (hδbs : δbs + w ≤ Y ∧ 3 * Fintype.card (Klein.SrcD fdf.DQ fdf.k) + 3 ≤ δbs)
    (hc : WordsBounded W' c) (h802 : c.nreg 802 = b) (hx : XCtx Y S c)
    (hrf : c.nreg δrf = δbf) (hrs : c.nreg δrs = δbs)
    (hsl : ∀ i < b, c.nmem (Y + 2 * S + i) = ν (src i))
    (hposf : ∀ x ∈ bdry N P₀ P₁, c.nmem (Pbf + ν x) < fdf.k ∧
      fdf.Q.tail (fdf.g (c.nmem (Pbf + ν x))) = fdf.j x)
    (hposs : ∀ x ∈ bdry N P₀ P₁, c.nmem (Pbs + ν x) < fds.k ∧
      fds.Q.tail (fds.g (c.nmem (Pbs + ν x))) = fds.j x)
    (hδf : ∀ v < w, c.rmem (δbf + v) = δf (ι v)) (hδs : ∀ v < w, c.rmem (δbs + v) = δs (ι v))
    (hEf : KSlot (Klein.srcMap fdf.inst.cycle) fdf.k (Klein.srcG fdf.inst.cycle)
      (Klein.srcPiece fdf.k (fdf.P'.image fdf.e))
      (MSSP.pert (Klein.srcLen (faceLen fdf.P' fdf.e (redLen N ℓ δf))
        (Klein.srcW (fdf.P'.image fdf.e) (faceLen fdf.P' fdf.e (redLen N ℓ δf))))) σf Bwf nf βf
      Rkf W' Pkf c)
    (hEs : KSlot (Klein.srcMap fds.inst.cycle) fds.k (Klein.srcG fds.inst.cycle)
      (Klein.srcPiece fds.k (fds.P'.image fds.e))
      (MSSP.pert (Klein.srcLen (faceLen fds.P' fds.e (redLen N ℓ δs))
        (Klein.srcW (fds.P'.image fds.e) (faceLen fds.P' fds.e (redLen N ℓ δs))))) σs Bws ns βs
      Rks W' Pks c)
    (hlow : ∀ a ≤ Bws + 16 * (ns + 1), c.nmem a ≤ Bwf + 16 * (nf + 1)) :
    ∃ c' t, ∃ βf' βs' : ℕ → V,
      Exec I W' (kPair zf δrf fdf.k (Fintype.card (Klein.SrcD fdf.DQ fdf.k)) nf Bwf
        Pkf.data.length βf Rkf Pbf Lf
        (Klein.srcW (fdf.P'.image fdf.e) (faceLen fdf.P' fdf.e (redLen N ℓ δf)))
        zs δrs fds.k (Fintype.card (Klein.SrcD fds.DQ fds.k)) ns Bws Pks.data.length βs Rks Pbs
        Ls (Klein.srcW (fds.P'.image fds.e) (faceLen fds.P' fds.e (redLen N ℓ δs)))) c c' t ∧
      t ≤ (3 * (32886 * 2372500000 * P.card * lg P.card) +
            rdCost b Lf (Fintype.card (Klein.SrcD fdf.DQ fdf.k)) + 19 * fdf.k + 10 * b +
            33 * Fintype.card (Klein.SrcD fdf.DQ fdf.k) + 300) +
          (3 * (32886 * 2372500000 * P.card * lg P.card) +
            rdCost b Ls (Fintype.card (Klein.SrcD fds.DQ fds.k)) + 19 * fds.k + 10 * b +
            33 * Fintype.card (Klein.SrcD fds.DQ fds.k) + 300) + 14 ∧
      IsEnum b βf' (bdry N P₀ P₁) ∧
      (∀ x < b, c'.nmem (Y + (3 + 5 * zf) * S + S + x) = ν (βf' x)) ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp Xf ℓ δf (bdry N P₀ P₁)).len (βf' i)
        (βf' i')) ∧
      (∀ s < b, ∀ t < b,
        c'.nmem (Y + (3 + 5 * zf) * S + 3 * S + (s * b + t)) =
            finB (arcOf (childDDG N mssp Xf ℓ δf (bdry N P₀ P₁)) βf') s t ∧
          c'.rmem (Y + (3 + 5 * zf) * S + 3 * S + (s * b + t)) =
            (matOf (childDDG N mssp Xf ℓ δf (bdry N P₀ P₁)) βf' s t : ℝ)) ∧
      IsEnum b βs' (bdry N P₀ P₁) ∧
      (∀ x < b, c'.nmem (Y + (3 + 5 * zs) * S + S + x) = ν (βs' x)) ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp Xs ℓ δs (bdry N P₀ P₁)).len (βs' i)
        (βs' i')) ∧
      (∀ s < b, ∀ t < b,
        c'.nmem (Y + (3 + 5 * zs) * S + 3 * S + (s * b + t)) =
            finB (arcOf (childDDG N mssp Xs ℓ δs (bdry N P₀ P₁)) βs') s t ∧
          c'.rmem (Y + (3 + 5 * zs) * S + 3 * S + (s * b + t)) =
            (matOf (childDDG N mssp Xs ℓ δs (bdry N P₀ P₁)) βs' s t : ℝ)) ∧
      (∀ r, (800 ≤ r ∧ r < 900) ∨ (919 ≤ r ∧ r < 960) ∨ 967 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, Bws + 16 * (ns + 1) < a → (a < Y + 3 * S ∨ Y + 13 * S ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ a, Bws + 16 * (ns + 1) < a → 3 * Fintype.card (Klein.SrcD fdf.DQ fdf.k) + 3 ≤ a →
        3 * Fintype.card (Klein.SrcD fds.DQ fds.k) + 3 ≤ a →
        (a < Y + 3 * S ∨ Y + 13 * S ≤ a) → c'.rmem a = c.rmem a) ∧
      c'.output = c.output := by
  have hx' := hx.reg
  obtain ⟨hδrf1, hδrf2⟩ := hδrf
  obtain ⟨hδrs1, hδrs2⟩ := hδrs
  obtain ⟨hnY1, hnY2⟩ := hnY
  obtain ⟨hIn1, hIn2, hIn3⟩ := hIn
  obtain ⟨hδbs1, hδbs2⟩ := hδbs
  have hKf' := hKf
  have hKs' := hKs
  obtain ⟨sk, sb, sbb, snD, kY, rbY, outY, yW, lK, lY, lW, pK, pY, pW, dK, dnD, dY, dW, bY, rK,
    rnD, rY, rW, bbW, lLW, wW⟩ := hKf'
  obtain ⟨sk', sb', sbb', snD', kY', rbY', outY', yW', lK', lY', lW', pK', pY', pW', dK', dnD',
    dY', dW', bY', rK', rnD', rY', rW', bbW', lLW', wW'⟩ := hKs'
  -- 1., 2. the first part
  obtain ⟨c₁, k₁, e₁, hk₁, a960, a961, a962, a963, a964, a965, a966, an₁, anm₁, arm₁, ao₁⟩ :=
    partSet_exec (I := I) (δr := δrf) hzf (by omega) c hc
  have z1 : ∀ i ≤ 4, c.nreg (933 + 5 * zf + i) = Y + (3 + 5 * zf) * S + i * S := fun i hi => by
    rw [show 933 + 5 * zf + i = 930 + (3 + 5 * zf + i) by omega, hx' _ (by omega)]; ring
  obtain ⟨c₂, k₂, βf', e₂, hk₂, hen₂, hO₂, hcr₂, hF₂, hn₂, hm₂, hr₂, hl₂, ho₂⟩ :=
    hf hN hsrc Lf (Y + 2 * S) Pbf δbf (Y + (3 + 5 * zf) * S) S βf Rkf W' I c₁ hKf hWLf
      e₁.wb_right (by rw [an₁ 802 (by omega), h802])
      (by rw [a960, hx' 2 (by omega)])
      (by rw [a961, show 933 + 5 * zf = 933 + 5 * zf + 0 by rfl, z1 0 (by omega)]; ring)
      (by rw [a962, show 934 + 5 * zf = 933 + 5 * zf + 1 by omega, z1 1 (by omega)]; ring)
      (by rw [a963, show 935 + 5 * zf = 933 + 5 * zf + 2 by omega, z1 2 (by omega)])
      (by rw [a964, show 936 + 5 * zf = 933 + 5 * zf + 3 by omega, z1 3 (by omega)])
      (by rw [a965, show 937 + 5 * zf = 933 + 5 * zf + 4 by omega, z1 4 (by omega)])
      (by rw [a966, hrf])
      (fun i hi => by rw [anm₁]; exact hsl i hi)
      (fun x hx => by rw [anm₁]; exact hposf x hx)
      (fun v hv => by rw [arm₁]; exact hδf v hv)
      (hEf.of (fun i _ => by rw [arm₁]) (fun i _ => by rw [anm₁]))
      (fun a ha => by rw [anm₁]; exact (hlow a (by omega)).trans le_rfl |>.trans (by omega))
  have z2 : ∀ i ≤ 4, c.nreg (933 + 5 * zs + i) = Y + (3 + 5 * zs) * S + i * S := fun i hi => by
    rw [show 933 + 5 * zs + i = 930 + (3 + 5 * zs + i) by omega, hx' _ (by pomega)]; ring
  have hx2 := hx' 2 (by pomega)
  -- 3., 4. the second part
  obtain ⟨c₃, k₃, e₃, hk₃, b960, b961, b962, b963, b964, b965, b966, bn₃, bnm₃, brm₃, bo₃⟩ :=
    partSet_exec (I := I) (δr := δrs) hzs (by pomega) c₂ e₂.wb_right
  obtain ⟨Af, As, hAf, hAs, hA⟩ : ∃ Af As, Y + (3 + 5 * zf) * S = Y + 3 * S + Af ∧
      Y + (3 + 5 * zs) * S = Y + 3 * S + As ∧ ((Af = 0 ∧ As = 5 * S) ∨ (Af = 5 * S ∧ As = 0)) := by
    rcases (by omega : (zf = 0 ∧ zs = 1) ∨ (zf = 1 ∧ zs = 0)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, 5 * S, by ring, by ring, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨5 * S, 0, by ring, by ring, Or.inr ⟨rfl, rfl⟩⟩
  simp only [hAf, hAs] at *
  have hR₂ : ∀ r, (800 ≤ r ∧ r < 900) ∨ (919 ≤ r ∧ r < 960) ∨ 967 ≤ r ∨ r = δrs →
      c₂.nreg r = c.nreg r := fun r hr => by rw [hn₂ r (by pomega), an₁ r (by pomega)]
  have hm₂' : ∀ a, Bwf + 16 * (nf + 1) < a → (a < Y + 3 * S + Af ∨ Y + 3 * S + Af + 5 * S ≤ a) →
      c₂.nmem a = c.nmem a := fun a h1 h2 => by rw [hm₂ a h1 h2, anm₁]
  have hr₂' : ∀ a, Bwf + 16 * (nf + 1) < a → 3 * Fintype.card (Klein.SrcD fdf.DQ fdf.k) + 3 ≤ a →
      (a < Y + 3 * S + Af ∨ Y + 3 * S + Af + 5 * S ≤ a) → c₂.rmem a = c.rmem a :=
    fun a h1 h2 h3 => by rw [hr₂ a h1 h2 h3, arm₁]
  obtain ⟨c₄, k₄, βs', e₄, hk₄, hen₄, hO₄, hcr₄, hF₄, hn₄, hm₄, hr₄, hl₄, ho₄⟩ :=
    hs hN hsrc Ls (Y + 2 * S) Pbs δbs (Y + 3 * S + As) S βs Rks W' I c₃ hKs hWLs
      e₃.wb_right (by rw [bn₃ 802 (by pomega), hR₂ 802 (by pomega), h802])
      (by rw [b960, hR₂ 932 (by pomega), hx2])
      (by rw [b961, show 933 + 5 * zs = 933 + 5 * zs + 0 by rfl, hR₂ _ (by pomega),
        z2 0 (by pomega)]; ring)
      (by rw [b962, show 934 + 5 * zs = 933 + 5 * zs + 1 by omega, hR₂ _ (by pomega),
        z2 1 (by pomega)]; ring)
      (by rw [b963, show 935 + 5 * zs = 933 + 5 * zs + 2 by omega, hR₂ _ (by pomega),
        z2 2 (by pomega)])
      (by rw [b964, show 936 + 5 * zs = 933 + 5 * zs + 3 by omega, hR₂ _ (by pomega),
        z2 3 (by pomega)])
      (by rw [b965, show 937 + 5 * zs = 933 + 5 * zs + 4 by omega, hR₂ _ (by pomega),
        z2 4 (by pomega)])
      (by rw [b966, hR₂ δrs (by pomega), hrs])
      (fun i hi => by rw [bnm₃, hm₂' _ (by pomega) (by pomega)]; exact hsl i hi)
      (fun x hx => by
        have := hN.lt _ (bdry_sub_verts hx)
        rw [bnm₃, hm₂' _ (by pomega) (by pomega)]; exact hposs x hx)
      (fun v hv => by rw [brm₃, hr₂' _ (by pomega) (by pomega) (by pomega)]; exact hδs v hv)
      (hEs.of (fun i _ => by rw [brm₃, hr₂' _ (by pomega) (by pomega) (by pomega)])
        (fun i _ => by rw [bnm₃, hm₂' _ (by pomega) (by pomega)]))
      (fun a ha => by
        rw [bnm₃]
        by_cases h1 : a ≤ Bwf + 16 * (nf + 1)
        · exact (hl₂ a h1).trans hKK
        · rw [hm₂' a (by pomega) (by pomega)]; exact (hlow a ha).trans hKK)
  clear hlow hposs hposf hsl hδf hδs hEf hEs hf hs
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), βf', βs', Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ e₄)), ?_,
    hen₂, fun x hx => ?_, hcr₂, fun s' hs' t ht => ?_, hen₄, hO₄, hcr₄, hF₄, fun r hr => ?_,
    fun a h1 h2 => ?_, fun a h1 h2 h2' h3 => ?_, by rw [ho₄, bo₃, ho₂, ao₁]⟩
  · pomega
  · rw [hm₄ _ (by pomega) (by pomega), bnm₃]; exact hO₂ x hx
  · have := rmLt hs' ht
    rw [hm₄ _ (by pomega) (by pomega), bnm₃, hr₄ _ (by pomega) (by pomega) (by pomega), brm₃]
    exact hF₂ s' hs' t ht
  · rw [hn₄ r (by pomega), bn₃ r (by pomega), hR₂ r (by pomega)]
  · rw [hm₄ a (by pomega) (by pomega), bnm₃, hm₂' a (by pomega) (by pomega)]
  · rw [hr₄ a (by pomega) (by pomega) (by pomega), brm₃, hr₂' a (by pomega) (by pomega) (by pomega)]

end Pair

/-! ### The node -/

/-- The layout of a part in the zone `z` of the scratch area, from the global layout of a
node. -/
theorem klay_of {b w k nD n Kw L Pb δb β Rk Z Y S W' z : ℕ} (hz : z ≤ 1) (h1 : b ≤ S)
    (h2 : b * b ≤ S) (h3 : k ≤ S) (h4 : 3 * nD + 3 ≤ S) (h5 : Kw < Z) (h6 : n + k * k ≤ Z)
    (h7 : 3 * nD + 3 + k * k ≤ Z) (h8 : Z ≤ δb) (h9 : δb + w ≤ Y) (h10 : Y + 16 * S ≤ Pb)
    (h11 : Y + 16 * S ≤ β) (h12 : Y + 16 * S ≤ Rk) (h13 : Y + 16 * S ≤ W') (h14 : Pb + w ≤ W')
    (h15 : Rk + (3 * nD + 3) ≤ W') (h16 : L + 1 ≤ W') (h17 : w + 1 ≤ W') (h18 : Z ≤ Y) :
    KLay b w k nD n Kw L (Y + 2 * S) Pb δb (Y + (3 + 5 * z) * S) S β Rk W' := by
  obtain ⟨A, hA, hA'⟩ : ∃ A, Y + (3 + 5 * z) * S = Y + 3 * S + A ∧ A ≤ 5 * S := by
    rcases (by omega : z = 0 ∨ z = 1) with rfl | rfl
    · exact ⟨0, by ring, by omega⟩
    · exact ⟨5 * S, by ring, le_rfl⟩
  rw [hA]
  exact ⟨h3, h1, h2, h4, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- The constants of the program of one part (from its one-face instance and its encoding). -/
structure KP where
  k : ℕ
  nD : ℕ
  n : ℕ
  Bw : ℕ
  len : ℕ
  β : ℕ
  Rk : ℕ
  Pb : ℕ
  L : ℕ
  Wr : ℤ

/-- The work space of Klein's program of a part. -/
def KP.Kw (p : KP) : ℕ := p.Bw + 16 * (p.n + 1)

/-- `kPair` from the constants of the two parts. -/
def kPairOf (zf δrf : ℕ) (pf : KP) (zs δrs : ℕ) (ps : KP) : Stmt :=
  kPair zf δrf pf.k pf.nD pf.n pf.Bw pf.len pf.β pf.Rk pf.Pb pf.L pf.Wr
    zs δrs ps.k ps.nD ps.n ps.Bw ps.len ps.β ps.Rk ps.Pb ps.L ps.Wr

/-- **The whole node** (see the module docstring): the part with the smaller work space of
Klein's program first. -/
def nodeProg (p₀ p₁ : KP) : Stmt :=
  .seq bdSet <| .seq bdryProg <|
  .seq (if p₀.Kw ≤ p₁.Kw then kPairOf 0 807 p₀ 1 808 p₁ else kPairOf 1 808 p₁ 0 807 p₀)
    restProg

end NegSSSP

end PlanarFlow
