module

public import PlanarFlow.NegSSSP.FaceWalk
public import PlanarFlow.NegSSSP.DecM
public import WordRAM.Machine.WordMono

/-!
# The separator run inside a larger configuration

`sepRun_exec` (and so `sep_run_cyc`, `sep_run_cutOK`) states no frame for the memory outside the
separator's output, in particular none for the plain encoding at `B₀` that `faceWalk` reads
afterwards. Here the run is moved, by `WordRAM.Machine.Exec.lift_trunc`, into any configuration
agreeing on the registers `< 700` and the memory `≤ W₁` (bounded there by `W₁`): it keeps the
registers from `700` on and the memory above `W₁`, so data kept above `W₁` survive it.

* `stmt_exec_det`: structured runs are deterministic.
* `sepRun10_regsOK`, `sepRun10_noInp`, `sepRun10_noRand`: `sepRun prog10` names registers `< 700`
  only and reads no input and no random word (kernel evaluation).
* `enc_congr`: the plain encoding depends only on the memory of its five arrays.
* `sep_run_lift`: **the separator run with its cycle exposed, its cut (`CutOK`) and a frame**:
  as `sep_run_cyc` on any configuration bounded by `W ≥ W₁` whose registers `< 700` and memory
  `≤ W₁` are bounded by `W₁`; the side `Z` is the set of the darts marked `1` (`markSet`) and
  meets `CutOK`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv CombMap PlanarSeparator PlanarSeparator.Map PlanarSeparator.StDart
  PlanarSeparator.MillerProg WordRAM WordRAM.Machine

universe u v w

open Lean Elab Tactic Meta in
/-- Clear every hypothesis that mentions a machine configuration or is an implication (as
`pclear` of `NodeRunA`). -/
elab "spclear" : tactic => do
  liftMetaTactic fun g => do
    let g' ← g.withContext do
      let mut fvs : Array FVarId := #[]
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        if (← isProp t) then
          let bad := t.foldConsts false fun c b => b || c.components.contains `Config
          if bad || t.isForall then fvs := fvs.push d.fvarId
      g.tryClearMany fvs
    return [g']

/-- `omega` after `spclear`. -/
macro "spomega" : tactic => `(tactic| (spclear; omega))

/-! ### Determinism -/

/-- **Structured runs are deterministic.** -/
theorem stmt_exec_det {P : Input} {W : ℕ} {s : Stmt} {c c₁ c₂ : Config} {k₁ k₂ : ℕ}
    (h₁ : Exec P W s c c₁ k₁) (h₂ : Exec P W s c c₂ k₂) : c₁ = c₂ ∧ k₁ = k₂ := by
  induction h₁ generalizing c₂ k₂ with
  | skip _ => cases h₂; exact ⟨rfl, rfl⟩
  | instr _ he _ _ =>
    cases h₂ with
    | instr _ he' _ _ => rw [he] at he'; cases he'; exact ⟨rfl, rfl⟩
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq e₁ e₂ =>
      obtain ⟨rfl, rfl⟩ := ih₁ e₁
      obtain ⟨rfl, rfl⟩ := ih₂ e₂
      exact ⟨rfl, rfl⟩
  | ifLtN_true ht _ ih =>
    cases h₂ with
    | ifLtN_true _ e => obtain ⟨rfl, rfl⟩ := ih e; exact ⟨rfl, rfl⟩
    | ifLtN_false hf _ => exact absurd ht hf
  | ifLtN_false ht _ ih =>
    cases h₂ with
    | ifLtN_true hf _ => exact absurd hf ht
    | ifLtN_false _ e => obtain ⟨rfl, rfl⟩ := ih e; exact ⟨rfl, rfl⟩
  | ifLtR_true ht _ ih =>
    cases h₂ with
    | ifLtR_true _ e => obtain ⟨rfl, rfl⟩ := ih e; exact ⟨rfl, rfl⟩
    | ifLtR_false hf _ => exact absurd ht hf
  | ifLtR_false ht _ ih =>
    cases h₂ with
    | ifLtR_true hf _ => exact absurd hf ht
    | ifLtR_false _ e => obtain ⟨rfl, rfl⟩ := ih e; exact ⟨rfl, rfl⟩
  | whileLtN_false ht _ =>
    cases h₂ with
    | whileLtN_false _ _ => exact ⟨rfl, rfl⟩
    | whileLtN_true hf _ _ => exact absurd hf ht
  | whileLtN_true ht _ _ ih₁ ih₂ =>
    cases h₂ with
    | whileLtN_false hf _ => exact absurd ht hf
    | whileLtN_true _ e₁ e₂ =>
      obtain ⟨rfl, rfl⟩ := ih₁ e₁
      obtain ⟨rfl, rfl⟩ := ih₂ e₂
      exact ⟨rfl, rfl⟩
  | whileLtR_false ht _ =>
    cases h₂ with
    | whileLtR_false _ _ => exact ⟨rfl, rfl⟩
    | whileLtR_true hf _ _ => exact absurd hf ht
  | whileLtR_true ht _ _ ih₁ ih₂ =>
    cases h₂ with
    | whileLtR_false hf _ => exact absurd ht hf
    | whileLtR_true _ e₁ e₂ =>
      obtain ⟨rfl, rfl⟩ := ih₁ e₁
      obtain ⟨rfl, rfl⟩ := ih₂ e₂
      exact ⟨rfl, rfl⟩

/-! ### The registers of the separator run -/

/-- `sepRun prog10` names registers `< 700` only (kernel evaluation). -/
theorem sepRun10_regsOK : (sepRun prog10).regsOK (fun r => decide (r < 700)) = true := by
  decide +kernel

/-- `sepRun prog10` reads no input (kernel evaluation). -/
theorem sepRun10_noInp : (sepRun prog10).noInp = true := by decide +kernel

/-- `sepRun prog10` draws no random word (kernel evaluation). -/
theorem sepRun10_noRand : (sepRun prog10).noRand = true := by decide +kernel

/-! ### The plain encoding depends only on its arrays -/

/-- **The plain encoding depends only on the memory of its five arrays.** -/
theorem enc_congr {D Q : Type*} [Fintype D] [DecidableEq D] [DecidableEq Q] {M : Map D Q}
    {m nV nF : ℕ} {c : D ≃ Fin m} {vn : Q ≃ Fin nV} {fn : M.Face ≃ Fin nF} {mem mem' : ℕ → ℕ}
    {bα bφ bφi bvn bfn : ℕ} (hE : Enc M c vn fn mem bα bφ bφi bvn bfn)
    {bα' bφ' bφi' bvn' bfn' : ℕ}
    (h : ∀ i < m, mem' (bα' + i) = mem (bα + i) ∧ mem' (bφ' + i) = mem (bφ + i) ∧
      mem' (bφi' + i) = mem (bφi + i) ∧ mem' (bvn' + i) = mem (bvn + i) ∧
      mem' (bfn' + i) = mem (bfn + i)) :
    Enc M c vn fn mem' bα' bφ' bφi' bvn' bfn' :=
  ⟨fun d => by rw [(h _ (c d).2).1, hE.α], fun d => by rw [(h _ (c d).2).2.1, hE.φ],
    fun d => by rw [(h _ (c d).2).2.2.1, hE.φi], fun d => by rw [(h _ (c d).2).2.2.2.1, hE.vn],
    fun d => by rw [(h _ (c d).2).2.2.2.2, hE.fn]⟩

/-! ### The lifted separator run -/

section Lift

open Orbit BKMNW Classical

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}

lemma markSet_congr {K : Finset D} {m : ℕ} {c : SDart (rcl N K) ≃ Fin m} {f g : ℕ → ℕ}
    (h : ∀ i < m, f i = g i) : markSet N K c f = markSet N K c g := by
  ext d
  simp only [mem_markSet]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [← h _ (c _).2]; exact h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [h _ (c _).2]; exact h3⟩

set_option maxHeartbeats 4000000 in
/-- **The separator run inside a larger configuration, with its cycle exposed and its cut.**
From a configuration `d` bounded by `W ≥ W₁`, its registers `< 700` and its memory `≤ W₁`
bounded by `W₁`, holding the plain encoding of the piece map `kmap N K` of a connected piece at
`B₀` and the flags of `K` at `B₀ + 5 m` (as in `sep_run_cyc`, with `W₁` for the word bound),
`sepRun prog10` ends within the bound of `sep_run_cyc`, keeps the registers from `700` on and
the memory above `W₁`, the darts it marks `1` at `B₀ + 22 m` form a cut of `K` meeting `CutOK`,
and the conclusions of `sep_run_cyc` hold, the side `Z` being that cut. -/
theorem sep_run_lift (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {K : Finset D} (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K)
    {ψ : V → SVert (kσ N K) (rcl N K)}
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    {m nV nF : ℕ} (c : SDart (rcl N K) ≃ Fin m) (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF) (hm1 : 1 ≤ m)
    {W W₁ : ℕ} {P : Input} {B₀ : ℕ} {d : Config}
    (hE : Enc (kmap N K) c vn fn d.nmem B₀ (B₀ + m) (B₀ + 2 * m) (B₀ + 3 * m) (B₀ + 4 * m))
    (hfl : ∀ x, d.nmem (B₀ + 5 * m + c x) = flK N K x)
    (hB : aEnd10 (3 * m) (nV + nF + m) ≤ B₀) (hW₁ : B₀ + 23 * m + nV + nF + 2 ≤ W₁)
    (hW : W₁ ≤ W) (hd : WordsBounded W d) (hr : ∀ r < 700, d.nreg r ≤ W₁)
    (hmem : ∀ a ≤ W₁, d.nmem a ≤ W₁) (h390 : d.nreg 390 = m) (h391 : d.nreg 391 = nV)
    (h392 : d.nreg 392 = nF) (h393 : d.nreg 393 = B₀) :
    ∃ d' t, Exec P W (sepRun prog10) d d' t ∧
      t ≤ (1746 * K.card + 156) * (Nat.log 2 K.card + 3) + 16772 * K.card + 1849 ∧
      (∀ r, 700 ≤ r → d'.nreg r = d.nreg r) ∧ (∀ a, W₁ < a → d'.nmem a = d.nmem a) ∧
      CutOK N K (markSet N K c fun i => d'.nmem (B₀ + 22 * m + i)) ∧
      ∃ (C : (kst N K).SCycle) (Z : Finset (kst N K).Face),
        side N K Z = markSet N K c (fun i => d'.nmem (B₀ + 22 * m + i)) ∧
        (∀ x, (kst N K).face (old x) ∈ Z ↔ d'.nmem (B₀ + 22 * m + c x) = 1) ∧
        (∀ x, (kst N K).face (old x) ∈ Zᶜ ↔ d'.nmem (B₀ + 22 * m + c x) = 0) ∧
        (∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ) ∧
        (∀ δ, ((kst N K).face δ ∈ Zᶜ ↔ (kst N K).face ((kst N K).α δ) ∈ Zᶜ) ↔ ¬ C.Mem δ) ∧
        (∀ b ∈ bdry N (side N K Z) (side N K Zᶜ), b ∈ verts N (side N K Z) ∧
          b ∈ verts N (side N K Zᶜ) ∧ Sum.inl (ψ b) ∈ C.verts) ∧
        side N K Z ∪ side N K Zᶜ = K ∧ Disjoint (side N K Z) (side N K Zᶜ) ∧
        C.k ≤ 6 * Nat.sqrt (12 * K.card) + 4 ∧
        3 * (side N K Z).card ≤ 2 * K.card + 12 * C.k ∧
        3 * (side N K Zᶜ).card ≤ 2 * K.card + 12 * C.k ∧
        (bdry N (side N K Z) (side N K Zᶜ)).card ≤ C.k := by
  set U : ℕ → Bool := fun r => decide (r < 700) with hU
  set c₁ := trunc U W₁ d with hc₁def
  have hA₁ := agree_trunc U W₁ d
  have hc₁ : WordsBounded W₁ c₁ :=
    wordsBounded_trunc (fun r h => hr r (by simpa [hU] using h)) hmem
  have hm₁ : ∀ a ≤ W₁, c₁.nmem a = d.nmem a := fun a ha => (hA₁.nmem a ha).symm
  have hr₁ : ∀ r < 700, c₁.nreg r = d.nreg r := fun r hr' =>
    (hA₁.nreg r (by simpa [hU] using hr')).symm
  have hE₁ : Enc (kmap N K) c vn fn c₁.nmem B₀ (B₀ + m) (B₀ + 2 * m) (B₀ + 3 * m)
      (B₀ + 4 * m) := enc_congr hE fun i hi =>
    ⟨hm₁ _ (by omega), hm₁ _ (by omega), hm₁ _ (by omega), hm₁ _ (by omega), hm₁ _ (by omega)⟩
  have hfl₁ : ∀ x, c₁.nmem (B₀ + 5 * m + c x) = flK N K x := fun x => by
    rw [hm₁ _ (by have := (c x).2; omega)]; exact hfl x
  have g390 : c₁.nreg 390 = m := (hr₁ 390 (by omega)).trans h390
  have g391 : c₁.nreg 391 = nV := (hr₁ 391 (by omega)).trans h391
  have g392 : c₁.nreg 392 = nF := (hr₁ 392 (by omega)).trans h392
  have g393 : c₁.nreg 393 = B₀ := (hr₁ 393 (by omega)).trans h393
  obtain ⟨c', t, e, ht, C, Z, z1, z2, hb1, hb2, hbs, hu, hdj, hck, hc1, hc2, hbc⟩ :=
    sep_run_cyc (P := P) hM hrot hface hKr hK0 hK hψ c vn fn hm1 hE₁ hfl₁ hB hW₁ hc₁ g390 g391
      g392 g393
  -- the cut, on the same run
  obtain ⟨x₀, hx₀⟩ := hK0
  have hx₀' : x₀ ∈ rcl N K := subset_rcl K hx₀
  have hfl0 : 0 < flK N K ⟨x₀, hx₀'⟩ := by simp [flK, hx₀]
  have hX := prog10_spec10 (P := P) (W := W₁) (kmap N K) c vn fn (flK N K) hm1
    (kmap_isPlane hM hrot hface ⟨x₀, hx₀⟩ hK) (kmap_loopless hrot hKr) (flK_le K) hfl0 hB
    (by omega)
  have hB' : aEnd (3 * m) (nV + nF + m) ≤ B₀ := by unfold aEnd10 at hB; omega
  obtain ⟨c'', t', e', -, hcut⟩ :=
    sep_run_cutOK hM hrot hface hKr ⟨x₀, hx₀⟩ hK c vn fn hm1 hE₁ hfl₁ hB' hW₁ hc₁ g390 g391
      g392 g393 hX
  obtain ⟨hcc, -⟩ := stmt_exec_det e' e
  rw [hcc] at hcut
  -- the lift
  obtain ⟨d', e₂, hA, hKp, -⟩ :=
    Exec.lift_trunc (P' := P) e sepRun10_regsOK sepRun10_noInp sepRun10_noRand hW hd
  have hz : ∀ i < m, d'.nmem (B₀ + 22 * m + i) = c'.nmem (B₀ + 22 * m + i) := fun i hi =>
    hA.nmem _ (by omega)
  have hms := markSet_congr (N := N) (K := K) (c := c) hz
  have hzc : ∀ x : SDart (rcl N K), d'.nmem (B₀ + 22 * m + c x) =
      c'.nmem (B₀ + 22 * m + c x) := fun x => hz _ (c x).2
  have hside : side N K Z = markSet N K c (fun i => c'.nmem (B₀ + 22 * m + i)) := by
    ext y
    rw [mem_side, mem_markSet]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (z1 _).1 h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (z1 _).2 h3⟩
  refine ⟨d', t, e₂, ht, fun r hr' => hKp.nreg r (by simp [hU]; omega), hKp.nmem,
    by rw [hms]; exact hcut, C, Z, by rw [hms]; exact hside, fun x => by rw [hzc]; exact z1 x,
    fun x => by rw [hzc]; exact z2 x, hb1, hb2, hbs, hu, hdj, hck, hc1, hc2, hbc⟩

end Lift

/-! ### Sizes of the encoding, the walk with positions -/

section Pos

open Orbit BKMNW Classical

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}

lemma aEnd10_mono {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') : aEnd10 a b ≤ aEnd10 a' b' := by
  unfold aEnd10 aEnd
  have := Nat.mul_le_mul (Nat.add_le_add_right (Nat.log_mono_right (b := 2) hb) 2) hb
  omega

/-- The numbers of darts, vertices and faces of the piece map. -/
lemma enc_card {K : Finset D} {m nV nF : ℕ} (c : SDart (rcl N K) ≃ Fin m)
    (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV) (fn : (kmap N K).Face ≃ Fin nF) :
    m = (rcl N K).card ∧ nV + nF ≤ 2 * m ∧ K.card ≤ m ∧ m ≤ 2 * K.card := by
  have hc1 : Fintype.card (SVert (kσ N K) (rcl N K)) + Fintype.card (kmap N K).Face ≤
      2 * (rcl N K).card := card_pieceSep_le _ _
  have hc2 := card_rcl_le (N := N) K
  have hcm : m = (rcl N K).card := by
    rw [← Fintype.card_fin m, ← Fintype.card_congr c]; exact Fintype.card_coe _
  have hcV : nV = Fintype.card (SVert (kσ N K) (rcl N K)) := by
    rw [← Fintype.card_fin nV, ← Fintype.card_congr vn]
  have hcF : nF = Fintype.card (kmap N K).Face := by
    rw [← Fintype.card_fin nF, ← Fintype.card_congr fn]
  have hK := card_le_card (subset_rcl (N := N) K)
  omega

/-- The words of the plain encoding and the flags are small. -/
lemma enc_vals {K : Finset D} {m nV nF : ℕ} {c : SDart (rcl N K) ≃ Fin m}
    {vn : SVert (kσ N K) (rcl N K) ≃ Fin nV} {fn : (kmap N K).Face ≃ Fin nF} {mem : ℕ → ℕ}
    {B₀ : ℕ} (hE : Enc (kmap N K) c vn fn mem B₀ (B₀ + m) (B₀ + 2 * m) (B₀ + 3 * m) (B₀ + 4 * m))
    (hfl : ∀ d, mem (B₀ + 5 * m + c d) = flK N K d) :
    ∀ a, B₀ ≤ a → a < B₀ + 6 * m → mem a ≤ m + nV + nF + 1 := by
  intro a h1 h2
  have key : ∀ j < 6, ∀ i < m, a = B₀ + j * m + i → mem a ≤ m + nV + nF + 1 := by
    intro j hj i hi ha
    set d := c.symm ⟨i, hi⟩
    have hd : (c d : ℕ) = i := by simp [d]
    interval_cases j
    · have := hE.α d; rw [hd] at this
      rw [ha, show B₀ + 0 * m = B₀ by ring, this]; have := (c ((kmap N K).α d)).2; omega
    · have := hE.φ d; rw [hd] at this
      rw [ha, show B₀ + 1 * m = B₀ + m by ring, this]; have := (c ((kmap N K).φ d)).2; omega
    · have := hE.φi d; rw [hd] at this
      rw [ha, this]; have := (c ((kmap N K).φ.symm d)).2; omega
    · have := hE.vn d; rw [hd] at this
      rw [ha, this]; have := (vn ((kmap N K).vert d)).2; omega
    · have := hE.fn d; rw [hd] at this
      rw [ha, this]; have := (fn ((kmap N K).face d)).2; omega
    · have := hfl d; rw [hd] at this
      rw [ha, this]; have := flK_le K d; omega
  have hm : 0 < m := by omega
  refine key ((a - B₀) / m) (by
    rw [Nat.div_lt_iff_lt_mul hm]; omega) ((a - B₀) % m) (Nat.mod_lt _ hm) ?_
  have := Nat.div_add_mod (a - B₀) m
  rw [Nat.mul_comm] at this
  omega

/-- **The positions on the face of a part**: a one-face instance of the part `X` with the
sources `B` (`FaceInst`, along a face of `k` darts of a plane map of at most `q` vertices, faces
and darts) such that the word at `Pb + ν b`, for a source `b`, is the position on the face of a
dart leaving `b`: the hypothesis `hpos` of `cornerProg_face`. -/
def PosInst (N : CombMap D V F) (X : Finset D) (B : Finset V) (q k : ℕ) (mem : ℕ → ℕ)
    (Pb : ℕ) (ν : V → ℕ) : Prop :=
  ∃ (DQ VQ FQ : Type u) (_ : Fintype DQ) (_ : DecidableEq DQ) (_ : Fintype VQ)
    (_ : DecidableEq VQ) (_ : Fintype FQ) (_ : DecidableEq FQ) (Q : CombMap DQ VQ FQ)
    (g : ℕ → DQ) (P' : Finset D) (e : D → DQ) (j : V → VQ),
    FaceInst N X B q k Q g P' e j ∧
      ∀ b ∈ B, mem (Pb + ν b) < k ∧ Q.tail (g (mem (Pb + ν b))) = j b

lemma PosInst.congr {X X' : Finset D} {B : Finset V} {q k : ℕ} {mem mem' : ℕ → ℕ} {Pb : ℕ}
    {ν : V → ℕ} (h : PosInst N X B q k mem Pb ν) (hX : X = X')
    (hm : ∀ b ∈ B, mem' (Pb + ν b) = mem (Pb + ν b)) : PosInst N X' B q k mem' Pb ν := by
  subst hX
  obtain ⟨DQ, VQ, FQ, i1, i2, i3, i4, i5, i6, Q, g, P', e, j, hF, hp⟩ := h
  exact ⟨DQ, VQ, FQ, i1, i2, i3, i4, i5, i6, Q, g, P', e, j, hF, fun b hb => by
    rw [hm b hb]; exact hp b hb⟩

/-- `faceWalk_faceInst` with the encoding at `Y, Y + m, …` and the positions as `PosInst`. -/
theorem faceWalk_pos (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {K : Finset D} (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K)
    {ψ : V → SVert (kσ N K) (rcl N K)}
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    {C : (kst N K).SCycle} {Z : Finset (kst N K).Face}
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    {Bs : Finset V} (hBs : ∀ b ∈ Bs, b ∈ verts N (side N K Z) ∧ Sum.inl (ψ b) ∈ C.verts)
    {R : Finset D} (hR : Disjoint (verts N R) (verts N K))
    {m nV nF : ℕ} (c : SDart (rcl N K) ≃ Fin m) (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF) {P : Input} {W Y bz sv T₀ : ℕ} {c₀ : Config}
    (hE : Enc (kmap N K) c vn fn c₀.nmem Y (Y + m) (Y + 2 * m) (Y + 3 * m) (Y + 4 * m))
    (hz : ∀ x, ((kst N K).face (old x) ∈ Z ↔ c₀.nmem (bz + c x) = sv))
    (hlay : Y + 5 * m ≤ T₀) (hlay' : bz + m ≤ T₀)
    (hW : T₀ + 3 * (nV + nF) + 6 * m + 3 ≤ W) (hw : WordsBounded W c₀)
    (h10 : c₀.nreg 10 = 1) (h800 : c₀.nreg 800 = m) (h801 : c₀.nreg 801 = Y)
    (h802 : c₀.nreg 802 = Y + m) (h803 : c₀.nreg 803 = Y + 2 * m)
    (h804 : c₀.nreg 804 = Y + 3 * m) (h805 : c₀.nreg 805 = Y + 4 * m)
    (h806 : c₀.nreg 806 = bz) (h807 : c₀.nreg 807 = nV)
    (h808 : c₀.nreg 808 = nF) (h809 : c₀.nreg 809 = sv) (h810 : c₀.nreg 810 = T₀) :
    ∃ c' t, Exec P W faceWalk c₀ c' t ∧ t ≤ 72 * m + 13 * C.k + 18 ∧ SFr 820 840 c₀ c' ∧
      (∀ a, a < T₀ ∨ T₀ + 3 * (nV + nF) + 6 * m ≤ a → c'.nmem a = c₀.nmem a) ∧
      PosInst N (side N K Z ∪ R) Bs (18 * K.card) C.k c'.nmem (T₀ + 2 * (nV + nF))
        (fun v => vn (ψ v)) := by
  obtain ⟨c', t, ex, ht, -, fr, fm, -, -, -, -, -, -, -, DQ, VQ, FQ, i1, i2, i3, i4, i5, i6, Q, g, P',
      e, j, hF, -, hp⟩ :=
    faceWalk_faceInst (P := P) hM hrot hface hKr hK0 hK hψ hbd hBs hR c vn fn hE hz
      ⟨by omega, by omega, by omega, by omega, by omega, hlay'⟩ hW hw h10 h800 h801 h802 h803
      h804 h805 h806 h807 h808 h809 h810
  exact ⟨c', t, ex, ht, fr, fm, DQ, VQ, FQ, i1, i2, i3, i4, i5, i6, Q, g, P', e, j, hF, hp⟩

end Pos

end NegSSSP

end PlanarFlow
