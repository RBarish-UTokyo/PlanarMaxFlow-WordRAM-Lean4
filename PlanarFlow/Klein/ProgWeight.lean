module

public import PlanarFlow.Klein.ProgNext
public import PlanarFlow.Klein.DartOps

/-!
# Klein's algorithm on the machine: the changes of the weights between two moves

**The out-darts of the piece in the input** (`KOut`): after the boundary `GB`, the arrays `OB`
at `8 nD + n + k` and `OE` at `8 nD + 2 n + k`, indexed by the nodes, and `OL` at
`8 nD + 3 n + k`: for a vertex `x`, the words `OL[OB[ιv x]] … OL[OE[ιv x] - 1]` are the numbers
of the darts of the piece leaving `x`, each once, with `OE[ιv x] ≤ nD` (a compressed adjacency
list).

**The constants in the real memory**: `TL` at `3 nD` holds `tripL`, the weight of the darts that
are not eligible (`KConst`, with the threshold and the value at the nodes of the faces of the
initialisation).

* `wBodyS`, `wLoopS`: for each dart `d` of a list in `OL`, the new weight (computed by a block
  `nw`) into the real `r140`, the amount `δ = new - WT[d]`, `WT[d] := new`, the parent `p` of the
  node of the edge of `d` (`regParentS`), compared with `n` and with the node of the face of `d`
  (`NF`), and the four operations `dartOps` (`ropsS`).
* `wLoop_orun`: **the loop on a list of darts** as an `ORun` performing at most four operations
  per dart (`dart_ops_stored`), counted five operations and `30` further steps per dart: the
  values and the weights `WT` move by `new - old` on the darts of the list.
* `wtS`, `wt_orun`: **the changes of the weights between the moves `j` and `j + 1`**: the darts
  of the piece leaving the target `tripDst j` of the move `j` get the weight `tripL`, those
  leaving `tripDst (j + 1)` their length (`tripWt_succ`: no other weight changes).
* `nx_orun`: **from the end of the move `j` to the start of the move `j + 1` on the machine**
  (`nxAS`, then `wtS`): the operations of `next_stored`, the data at the start of the move
  `j + 1` (`StartOK`) stored, `WT` holding `tripWt (j + 1)`.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs

/-- The offset of the array `OB` (the first out-dart of a vertex, by its node). -/
def iOB (nD n k : ℕ) : ℕ := 8 * nD + n + k
/-- The offset of the array `OE` (the end of the out-darts of a vertex, by its node). -/
def iOE (nD n k : ℕ) : ℕ := 8 * nD + 2 * n + k
/-- The offset of the array `OL` (the out-darts of the piece). -/
def iOL (nD n k : ℕ) : ℕ := 8 * nD + 3 * n + k

/-- The real word holding `tripL`. -/
def aTL (nD : ℕ) : ℕ := 3 * nD

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **The out-darts of the piece in the input**: for every vertex `x`, the words of `OL` from
`OB[ιv x]` to `OE[ιv x]` are the numbers of the darts of `S` leaving `x`, each once. -/
def KOut (M : CombMap D V F) (S : Finset D) {nD : ℕ} (σ : D ≃ Fin nD) (ιv : V → ℕ) (n k : ℕ)
    (P : Input) : Prop :=
  ∀ x : V, ∃ ds : List D, ds.Nodup ∧ (∀ d, d ∈ ds ↔ d ∈ S ∧ M.tail d = x) ∧
    P.data.getD (iOE nD n k + ιv x) 0 = P.data.getD (iOB nD n k + ιv x) 0 + ds.length ∧
    P.data.getD (iOE nD n k + ιv x) 0 ≤ nD ∧ ∀ i (h : i < ds.length),
      P.data.getD (iOL nD n k + (P.data.getD (iOB nD n k + ιv x) 0 + i)) 0 = σ ds[i]

/-! ### The loop on a list of darts -/

/-- The operations on the first values (the parent of the node of the edge is not the face). -/
def opsWA : List ROp := [.add 143 142, .add 145 144, .add2 143 143, .add2 145 143]
/-- The operations on the second values (the parent of the node of the edge is the face). -/
def opsWB : List ROp := [.add 143 143, .add 145 143, .add2 143 142, .add2 145 144]

/-- The body of the loop on the darts: `r140` the index in `OL`, the new weight from the block
`nw` (from the number of the dart in `r142`). -/
def wBodyS (B nD n k : ℕ) (nw : List Instr) : Stmt :=
  .seq (block [.constN 142 (iOL nD n k), .addN 142 142 140, .readIn 142 142,
    .constN 143 (iNE nD), .addN 143 143 142, .readIn 143 143,
    .constN 146 (iNF nD), .addN 146 146 142, .readIn 146 146]) <|
  .seq (block nw) <|
  .seq (block [.constN 144 aWT, .addN 144 144 142, .loadR 141 144, .subR 142 140 141,
    .constR 143 0, .subR 144 143 142, .storeR 144 140]) <|
  .seq (regParentS B 143) <|
  .seq (.instr (.copyN 145 195)) <|
  .seq (.ifLtN 145 151 (.ifLtN 145 146 (ropsS B opsWA)
    (.ifLtN 146 145 (ropsS B opsWA) (ropsS B opsWB))) .skip) <|
  block [.constN 147 1, .addN 140 140 147]

/-- **The loop on the darts** `OL[r140] … OL[r141 - 1]`. -/
def wLoopS (B nD n k : ℕ) (nw : List Instr) : Stmt := .whileLtN 140 141 (wBodyS B nD n k nw)

variable {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ} {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ}
  {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

/-- The values after the first `i` darts of the list. -/
def wVal (ds : List D) (val₀ nwv w₀ : D → ℤ) (i : ℕ) (d : D) : ℤ :=
  if d ∈ ds.take i then val₀ d + nwv d - w₀ d else val₀ d

/-- The weights after the first `i` darts of the list. -/
def wWt (ds : List D) (nwv w₀ : D → ℤ) (i : ℕ) (d : D) : ℤ :=
  if d ∈ ds.take i then nwv d else w₀ d

lemma take_succ_mem {ds : List D} {i : ℕ} (hi : i < ds.length) (d : D) :
    d ∈ ds.take (i + 1) ↔ d ∈ ds.take i ∨ d = ds[i] := by
  rw [List.take_add_one, List.mem_append, List.getElem?_eq_getElem hi]
  simp

lemma not_mem_take_get {ds : List D} (hnd : ds.Nodup) {i : ℕ} (hi : i < ds.length) :
    ds[i] ∉ ds.take i := by
  intro h
  obtain ⟨j, hj, hji⟩ := List.getElem_of_mem h
  rw [List.getElem_take] at hji
  have hjl : j < i := (by simpa using hj : j < i ∧ j < ds.length).1
  exact absurd ((List.Nodup.getElem_inj_iff hnd).1 hji) (by omega)

lemma wVal_succ {ds : List D} (hnd : ds.Nodup) (val₀ nwv w₀ : D → ℤ) {i : ℕ}
    (hi : i < ds.length) :
    Function.update (wVal ds val₀ nwv w₀ i) ds[i]
        (wVal ds val₀ nwv w₀ i ds[i] + (nwv ds[i] - wWt ds nwv w₀ i ds[i])) =
      wVal ds val₀ nwv w₀ (i + 1) := by
  have hn := not_mem_take_get hnd hi
  funext d
  by_cases hd : d = ds[i]
  · subst hd
    rw [Function.update_self]
    simp only [wVal, wWt, hn, ↓reduceIte, (take_succ_mem hi _).2 (Or.inr rfl)]
    ring
  · rw [Function.update_of_ne hd]
    simp only [wVal, take_succ_mem hi, hd, or_false]

lemma wWt_succ {ds : List D} (nwv w₀ : D → ℤ) {i : ℕ} (hi : i < ds.length) :
    Function.update (wWt ds nwv w₀ i) ds[i] (nwv ds[i]) = wWt ds nwv w₀ (i + 1) := by
  funext d
  by_cases hd : d = ds[i]
  · subst hd
    rw [Function.update_self]
    simp only [wWt, (take_succ_mem hi _).2 (Or.inr rfl), ↓reduceIte]
  · rw [Function.update_of_ne hd]
    simp only [wWt, take_succ_mem hi, hd, or_false]

lemma wVal_zero (ds : List D) (val₀ nwv w₀ : D → ℤ) : wVal ds val₀ nwv w₀ 0 = val₀ := by
  funext d; simp [wVal]

lemma wWt_zero (ds : List D) (nwv w₀ : D → ℤ) : wWt ds nwv w₀ 0 = w₀ := by
  funext d; simp [wWt]

lemma wVal_length (ds : List D) (val₀ nwv w₀ : D → ℤ) : wVal ds val₀ nwv w₀ ds.length =
    fun d => if d ∈ ds then val₀ d + nwv d - w₀ d else val₀ d := by
  funext d; simp [wVal]

lemma wWt_length (ds : List D) (nwv w₀ : D → ℤ) :
    wWt ds nwv w₀ ds.length = fun d => if d ∈ ds then nwv d else w₀ d := by
  funext d; simp [wWt]

variable (M σ ιv ιg ιf ιe n) in
/-- **The invariant of the loop on the darts** `ds` (at `OL[a] …`), from the configuration `c₀`
and the forest `Fo₀`. -/
structure WInv (B W k a : ℕ) (ds : List D) (φ : D → ℤ) (fe : F) (Lo : ℝ) (T : DTree M.dual)
    (val₀ nwv w₀ : D → ℤ) (Fo₀ : Forest) (c₀ : Config) (i : ℕ) (hs : List EOp) (G : List VT)
    (c : Config) : Prop where
  lcte : LCTE B n (runOpsE n Fo₀ hs).1 G c
  wb : WordsBounded W c
  st : Stored M n ιv ιg ιf ιe φ fe Lo (runOpsE n Fo₀ hs).1 T (wVal ds val₀ nwv w₀ i)
  out : (runOpsE n Fo₀ hs).2 = []
  len : hs.length ≤ 4 * i
  ile : i ≤ ds.length
  r140 : c.nreg 140 = a + i
  r141 : c.nreg 141 = a + ds.length
  kmem : KMem M σ ιv T (wWt ds nwv w₀ i) φ c
  regs : ∀ r, r < 140 → c.nreg r = c₀.nreg r ∧ c.rreg r = c₀.rreg r
  output : c.output = c₀.output
  nm : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c.nmem a = c₀.nmem a
  rm : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (∀ d : D, a ≠ aWT + σ d) → c.rmem a = c₀.rmem a

/-- The hypothesis on the block `nw` computing the new weight `nwv d` of the dart `d` (number in
`r142`) into the real `r140`, writing only `r147` and the real `r140`, from any configuration
whose real memory outside the structure and `WT` is that of `c₀`. -/
def NwOK (P : Input) (W B : ℕ) (σ : D ≃ Fin nD) (n : ℕ) (nw : List Instr) (ds : List D)
    (nwv : D → ℤ) (c₀ : Config) : Prop :=
  ∀ (c : Config) (d : D), d ∈ ds → WordsBounded W c → c.nreg 142 = σ d →
    (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (∀ d' : D, a ≠ aWT + σ d') → c.rmem a = c₀.rmem a) →
    ∃ c' k', Exec P W (block nw) c c' k' ∧ k' ≤ 3 ∧ c'.rreg 140 = (nwv d : ℝ) ∧
      (∀ r, r ≠ 147 → c'.nreg r = c.nreg r) ∧ (∀ r, r ≠ 140 → c'.rreg r = c.rreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output

section
variable {P : Input} {W B : ℕ}

/-- **One iteration of the loop on the darts.** -/
theorem wBody_orun (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 8 * nD + 4 * n + k ≤ W)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {a : ℕ} {ds : List D} (hnd : ds.Nodup)
    (hds : ∀ i (h : i < ds.length), P.data.getD (iOL nD n k + (a + i)) 0 = σ ds[i])
    (hWo : iOL nD n k + (a + ds.length) ≤ W) {nw : List Instr} {nwv : D → ℤ} {c₀ : Config}
    (hnw : NwOK P W B σ n nw ds nwv c₀)
    {φ : D → ℤ} {fe : F} {Lo : ℝ} {T : DTree M.dual} {val₀ w₀ : D → ℤ} {Fo₀ : Forest} (i : ℕ)
    (hs : List EOp) (G : List VT) (c : Config)
    (h : WInv M σ n ιv ιg ιf ιe B W k a ds φ fe Lo T val₀ nwv w₀ Fo₀ c₀ i hs G c)
    (ht : i < ds.length) :
    ∃ c' os G', ORun P W B n (wBodyS B nD n k nw) c (runOpsE n Fo₀ hs).1 G c' os G' 5 28 ∧
      WInv M σ n ιv ιg ιf ιe B W k a ds φ fe Lo T val₀ nwv w₀ Fo₀ c₀ (i + 1) (hs ++ os) G'
        c' := by
  classical
  set Fo := (runOpsE n Fo₀ hs).1 with hFo
  set d := ds[i] with hd
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hdi := hds i ht
  have hc := h.wb
  have hσd := hσ d
  -- the dart, the node of its edge, the node of its face
  obtain ⟨c₁, k₁, e₁, hk₁, p142, p143, p146, g₁⟩ : ∃ c' k', Exec P W (block [.constN 142
      (iOL nD n k), .addN 142 142 140, .readIn 142 142, .constN 143 (iNE nD),
      .addN 143 143 142, .readIn 143 143, .constN 146 (iNF nD), .addN 146 146 142,
      .readIn 146 146]) c c' k' ∧ k' = 9 ∧ c'.nreg 142 = σ d ∧ c'.nreg 143 = ιe d ∧
      c'.nreg 146 = ιf (M.face d) ∧ GFr 142 147 c c' := by
    exec_block
    all_goals try (first
      | exact hP _
      | (config_simp; rw [h.r140]; have := h.ile; omega)
      | (simp only [iOL, iNE, iNF]; omega)
      | (config_simp; simp only [h.r140, hdi]; simp only [iNE, iNF]; omega))
    refine ⟨rfl, by config_simp; rw [h.r140, hdi], ?_, ?_, by gfr_tac⟩
    · config_simp; rw [h.r140, hdi, hK.ne]
    · config_simp; rw [h.r140, hdi, hK.nf]
  have o₁ := ORun.ofGFr e₁ h.lcte g₁ (by omega)
  -- the new weight
  have hdm : d ∈ ds := List.getElem_mem ht
  obtain ⟨c₂, k₂, e₂, hk₂, q140, n₂, r₂, nm₂, rm₂, out₂⟩ := hnw c₁ d hdm e₁.wb_right p142
    (fun a ha hne => by rw [g₁.2.2.1]; exact h.rm a ha hne)
  have o₂ : ORun P W B n _ c₁ Fo G c₂ [] G 0 k₂ := ORun.glue e₂ o₁.2.lcte
    (fun a _ _ => by rw [nm₂, rm₂]; exact ⟨rfl, rfl⟩) (n₂ 151 (by omega))
  -- the amount, the old weight, the new weight stored
  have hc₂ := e₂.wb_right
  have s142 : c₂.nreg 142 = σ d := by rw [n₂ 142 (by omega), p142]
  have hwd : c₂.rmem (aWT + σ d) = (w₀ d : ℝ) := by
    rw [rm₂, g₁.2.2.1, h.kmem.wt d]
    simp only [wWt, not_mem_take_get hnd ht, ↓reduceIte, hd]
  obtain ⟨c₃, k₃, e₃, hk₃, t142, t143, t144, tm, tnm, tn, tr, tout⟩ : ∃ c' k', Exec P W
      (block [.constN 144 aWT, .addN 144 144 142, .loadR 141 144, .subR 142 140 141,
        .constR 143 0, .subR 144 143 142, .storeR 144 140]) c₂ c' k' ∧ k' = 7 ∧
      c'.rreg 142 = ((nwv d - w₀ d : ℤ) : ℝ) ∧ c'.rreg 143 = ((0 : ℤ) : ℝ) ∧
      c'.rreg 144 = ((-(nwv d - w₀ d) : ℤ) : ℝ) ∧
      c'.rmem = upd c₂.rmem (aWT + σ d) (nwv d : ℝ) ∧ c'.nmem = c₂.nmem ∧
      (∀ r, r ≠ 144 → c'.nreg r = c₂.nreg r) ∧
      (∀ r, r ≠ 141 → r ≠ 142 → r ≠ 143 → r ≠ 144 → c'.rreg r = c₂.rreg r) ∧
      c'.output = c₂.output := by
    exec_block
    · unfold aWT; omega
    · config_simp; rw [s142]; unfold aWT; omega
    · refine ⟨rfl, ?_, by config_simp, ?_, ?_, rfl, fun r hr => ?_, fun r h1 h2 h3 h4 => ?_,
        rfl⟩
      · config_simp; rw [s142, hwd, q140]; push_cast; ring
      · config_simp; rw [s142, hwd, q140]; push_cast; ring
      · config_simp; rw [s142, q140]
      · config_simp; simp only [upd_other _ _ _ hr]
      · config_simp; simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3,
          upd_other _ _ _ h4]
  have o₃ : ORun P W B n _ c₂ Fo G c₃ [] G 0 k₃ := ORun.glue e₃ o₂.2.lcte
    (fun a ha _ => ⟨by rw [tnm], by rw [tm, upd_other _ _ _ (by unfold aWT; omega)]⟩)
    (by rw [tn 151 (by omega)])
  -- the parent of the node of the edge
  have hc₃ := e₃.wb_right
  have s143 : c₃.nreg 143 = ιe d := by
    rw [tn 143 (by omega), n₂ 143 (by omega), p143]
  obtain ⟨c₄, G₄, o₄, u195, -, m₄, f₄⟩ := regParent_orun (P := P) hW hc₃ o₃.2.lcte s143
    (hL.dual.e_lt d)
  have e₅ := Exec.copyN (P := P) o₄.2.wb 145 195
  have g₅ : GFr 145 146 c₄ { c₄ with nreg := upd c₄.nreg 145 (c₄.nreg 195) } := by gfr_tac
  have o₅ := ORun.ofGFr e₅ o₄.2.lcte g₅ (by omega)
  set c₅ := { c₄ with nreg := upd c₄.nreg 145 (c₄.nreg 195) } with hc₅
  have v145 : c₅.nreg 145 = Fo.par (ιe d) := by rw [hc₅]; config_simp; exact u195
  have v143 : c₅.nreg 143 = ιe d := by
    rw [(g₅.1 143 (by omega)).1, f₄.1 143 (by omega), s143]
  have v146 : c₅.nreg 146 = ιf (M.face d) := by
    rw [(g₅.1 146 (by omega)).1, f₄.1 146 (by omega), tn 146 (by omega), n₂ 146 (by omega),
      p146]
  have v151 : c₅.nreg 151 = n := o₅.2.lcte.hn
  set δ : ℤ := nwv d - w₀ d with hδ
  set zr : ℕ → ℤ := fun r => if r = 142 then δ else if r = 144 then -δ else 0 with hzr
  have w142 : c₅.rreg 142 = (zr 142 : ℝ) := by
    rw [(g₅.1 142 (by omega)).2, f₄.2.1 142 (by omega), t142]; simp [hzr]
  have w143 : c₅.rreg 143 = (zr 143 : ℝ) := by
    rw [(g₅.1 143 (by omega)).2, f₄.2.1 143 (by omega), t143]; simp [hzr]
  have w144 : c₅.rreg 144 = (zr 144 : ℝ) := by
    rw [(g₅.1 144 (by omega)).2, f₄.2.1 144 (by omega), t144]; simp [hzr]
  -- the operations
  have hSt := h.st
  obtain ⟨hv, ho, hSt'⟩ := dart_ops_stored hL hSt d δ
  have hc₅w : WordsBounded W c₅ := e₅.wb_right
  have hmid : ∃ c₆ G₆, ORun P W B n (.ifLtN 145 151 (.ifLtN 145 146 (ropsS B opsWA)
      (.ifLtN 146 145 (ropsS B opsWA) (ropsS B opsWB))) .skip) c₅ Fo G₄ c₆
      (dartOps Fo n ιf ιe M d δ) G₆ 4 5 ∧ MemFrame B n (mem c₅) (mem c₆) ∧ RegFr c₅ c₆ := by
    have hokA : ∀ o ∈ opsWA, o.Ok c₅ zr := by
      intro o ho
      simp only [opsWA, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl
      · exact ⟨by norm_num, by norm_num, w142⟩
      · exact ⟨by norm_num, by norm_num, w144⟩
      · exact ⟨by norm_num, by norm_num, w143⟩
      · exact ⟨by norm_num, by norm_num, w143⟩
    have hokB : ∀ o ∈ opsWB, o.Ok c₅ zr := by
      intro o ho
      simp only [opsWB, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl
      · exact ⟨by norm_num, by norm_num, w143⟩
      · exact ⟨by norm_num, by norm_num, w143⟩
      · exact ⟨by norm_num, by norm_num, w142⟩
      · exact ⟨by norm_num, by norm_num, w144⟩
    have hfl := hL.dual.f_lt (M.face d)
    by_cases hp : Fo.par (ιe d) < n
    · have hlt : c₅.nreg 145 < c₅.nreg 151 := by rw [v145, v151]; exact hp
      by_cases hf : Fo.par (ιe d) = ιf (M.face d)
      · have e : dartOps Fo n ιf ιe M d δ = opsWB.map (ROp.eop c₅ zr) := by
          simp only [dartOps, hf, hfl, ↓reduceIte, opsWB, List.map, ROp.eop, v143, v145,
            hzr]
          simp
        rw [e] at hv ⊢
        obtain ⟨c₆, G₆, o, hm, hr⟩ := ropsS_orun (P := P) hW zr opsWB hc₅w o₅.2.lcte
          hokB hv
        have n1 : ¬ c₅.nreg 145 < c₅.nreg 146 := by rw [v145, v146, hf]; omega
        have n2 : ¬ c₅.nreg 146 < c₅.nreg 145 := by rw [v145, v146, hf]; omega
        exact ⟨c₆, G₆, ((((o.ifLtN_false (t := ropsS B opsWA) n2).ifLtN_false
          (t := ropsS B opsWA) n1).ifLtN_true (e := .skip) hlt)).mono (by simp [opsWB])
          (by omega), hm, hr⟩
      · have e : dartOps Fo n ιf ιe M d δ = opsWA.map (ROp.eop c₅ zr) := by
          simp only [dartOps, hp, hf, ↓reduceIte, opsWA, List.map, ROp.eop, v143, v145,
            hzr]
          simp
        rw [e] at hv ⊢
        obtain ⟨c₆, G₆, o, hm, hr⟩ := ropsS_orun (P := P) hW zr opsWA hc₅w o₅.2.lcte
          hokA hv
        have hne : c₅.nreg 145 ≠ c₅.nreg 146 := by rw [v145, v146]; exact hf
        refine ⟨c₆, G₆, ?_, hm, hr⟩
        rcases Nat.lt_or_gt_of_ne hne with h1 | h1
        · exact ((o.ifLtN_true (e := .ifLtN 146 145 (ropsS B opsWA) (ropsS B opsWB))
            h1).ifLtN_true (e := .skip) hlt).mono (by simp [opsWA]) (by omega)
        · exact (((o.ifLtN_true (e := ropsS B opsWB) h1).ifLtN_false (t := ropsS B opsWA)
            (by omega)).ifLtN_true (e := .skip) hlt).mono (by simp [opsWA]) (by omega)
    · have e : dartOps Fo n ιf ιe M d δ = [] := by simp only [dartOps, hp, ↓reduceIte]
      rw [e]
      have hge : ¬ c₅.nreg 145 < c₅.nreg 151 := by rw [v145, v151]; exact hp
      exact ⟨c₅, G₄, (ORun.ifLtN_false (t := .ifLtN 145 146 (ropsS B opsWA)
        (.ifLtN 146 145 (ropsS B opsWA) (ropsS B opsWB))) hge
        (⟨trivial, LRun.skip hc₅w o₅.2.lcte⟩ : ORun P W B n .skip c₅ Fo G₄ c₅ [] G₄ 0 0)).mono
        (by omega) (by omega),
        MemFrame.refl B n _, RegFr.refl _⟩
  obtain ⟨c₆, G₆, o₆, m₆, f₆⟩ := hmid
  -- the next index
  have hc₆ := o₆.2.wb
  have x140 : c₆.nreg 140 = a + i := by
    rw [f₆.1 140 (by omega), (g₅.1 140 (by omega)).1, f₄.1 140 (by omega), tn 140 (by omega),
      n₂ 140 (by omega), (g₁.1 140 (by omega)).1, h.r140]
  obtain ⟨c₇, k₇, e₇, hk₇, y140, g₇⟩ : ∃ c' k', Exec P W (block [.constN 147 1,
      .addN 140 140 147]) c₆ c' k' ∧ k' = 2 ∧ c'.nreg 140 = a + (i + 1) ∧
      (∀ r, r ≠ 140 → r ≠ 147 → c'.nreg r = c₆.nreg r) ∧ c'.rreg = c₆.rreg ∧
      c'.nmem = c₆.nmem ∧ c'.rmem = c₆.rmem ∧ c'.output = c₆.output := by
    exec_block
    · omega
    · config_simp; rw [x140]; have := h.ile; omega
    · refine ⟨rfl, by config_simp; rw [x140]; ring, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      config_simp; simp only [upd_other _ _ _ h1, upd_other _ _ _ h2]
  have o₇ : ORun P W B n _ c₆ _ G₆ c₇ [] G₆ 0 k₇ := ORun.glue e₇ o₆.2.lcte
    (fun a _ _ => by rw [g₇.2.2.1, g₇.2.2.2.1]; exact ⟨rfl, rfl⟩) (g₇.1 151 (by omega)
      (by omega))
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq (o₆.seq o₇)))))
  simp only [List.nil_append, List.append_nil] at o
  -- the invariant
  have hrun : (runOpsE n Fo₀ (hs ++ dartOps Fo n ιf ιe M d δ)).1 =
      (runOpsE n Fo (dartOps Fo n ιf ιe M d δ)).1 := by rw [runOpsE_fst_append]
  have hmem6 : ∀ a', (a' < B ∨ B + 16 * (n + 1) ≤ a') → c₇.nmem a' = c₃.nmem a' ∧
      c₇.rmem a' = c₃.rmem a' := fun a' ha' => by
    have h6 := m₆ a' ha'
    have h4 := m₄ a' ha'
    simp only [DynTree.mem] at h6 h4
    rw [g₇.2.2.1, g₇.2.2.2.1, h6.1, h6.2, h4.1, h4.2]; exact ⟨rfl, rfl⟩
  have hreg : ∀ r, r < 140 → c₇.nreg r = c.nreg r ∧ c₇.rreg r = c.rreg r := fun r hr => by
    rw [g₇.1 r (by omega) (by omega), g₇.2.1, f₆.1 r (by omega), f₆.2.1 r (by omega),
      (g₅.1 r (by omega)).1, (g₅.1 r (by omega)).2, f₄.1 r (by omega), f₄.2.1 r (by omega),
      tn r (by omega), tr r (by omega) (by omega) (by omega) (by omega), n₂ r (by omega),
      r₂ r (by omega), (g₁.1 r (by omega)).1, (g₁.1 r (by omega)).2]
    exact ⟨rfl, rfl⟩
  have hlen := dartOps_length_le (n := n) (ιf := ιf) (ιe := ιe) (M := M) Fo d δ
  refine ⟨c₇, dartOps Fo n ιf ιe M d δ, G₆, ⟨o.1, ?_⟩, ⟨?_, e₇.wb_right, ?_, ?_, ?_, ht,
    y140, ?_, ⟨fun x hx => ?_, fun d' => ?_, fun d' => ?_⟩, fun r hr => ?_, ?_,
    fun a' ha' => ?_, fun a' ha' hne => ?_⟩⟩
  · exact o.2.mono (by omega) (by omega)
  · rw [hrun]; exact o₇.2.lcte
  · rw [hrun, ← wVal_succ hnd val₀ nwv w₀ ht]
    have hww : wWt ds nwv w₀ i ds[i] = w₀ d := by
      simp only [wWt, not_mem_take_get hnd ht, ↓reduceIte, hd]
    rw [hww]
    have hv' : wVal ds val₀ nwv w₀ i ds[i] = wVal ds val₀ nwv w₀ i d := rfl
    rw [hv']; exact hSt'
  · rw [runOpsE_append, h.out, ho]; rfl
  · rw [List.length_append]; have := h.len; omega
  · rw [g₇.1 141 (by omega) (by omega), f₆.1 141 (by omega), (g₅.1 141 (by omega)).1,
      f₄.1 141 (by omega), tn 141 (by omega), n₂ 141 (by omega), (g₁.1 141 (by omega)).1,
      h.r141]
  · rw [(hmem6 _ (Or.inl (by have := hL.prim.f_lt x; unfold aTP; omega))).1, tnm, nm₂,
      g₁.2.1]
    exact h.kmem.tp x hx
  · rw [(hmem6 _ (Or.inl (by have := hσ d'; unfold aWT; omega))).2, tm,
      ← wWt_succ nwv w₀ ht]
    by_cases hdd : d' = d
    · rw [hdd, upd_same, Function.update_self]
    · rw [upd_other _ _ _ (fun h' => hdd (σ.injective (Fin.ext (by unfold aWT at h'; omega)))),
        Function.update_of_ne hdd, rm₂, g₁.2.2.1]
      exact h.kmem.wt d'
  · rw [(hmem6 _ (Or.inl (by have := hσ d'; unfold aPH; omega))).2, tm,
      upd_other _ _ _ (by unfold aPH aWT; omega), rm₂, g₁.2.2.1]
    exact h.kmem.ph d'
  · rw [(hreg r hr).1, (hreg r hr).2]; exact h.regs r hr
  · rw [g₇.2.2.2.2, f₆.2.2, g₅.2.2.2, f₄.2.2, tout, out₂, g₁.2.2.2]; exact h.output
  · rw [(hmem6 a' ha').1, tnm, nm₂, g₁.2.1]; exact h.nm a' ha'
  · rw [(hmem6 a' ha').2, tm, upd_other _ _ _ (hne d), rm₂, g₁.2.2.1]; exact h.rm a' ha' hne

/-- **The loop on the darts of a list** `ds` (at `OL[a] … OL[a + |ds| - 1]`, `r140 = a`,
`r141 = a + |ds|`): from the stored data with the values `val₀` and the weights `w₀` in `WT`,
it performs at most `4 |ds|` operations, printing nothing, counted `5 |ds|` operations and
`30 |ds| + 2` further steps; the values become `val₀ + nwv - w₀` and the weights `nwv` on the
darts of the list. -/
theorem wLoop_orun (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 8 * nD + 4 * n + k ≤ W)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {a : ℕ} {ds : List D} (hnd : ds.Nodup)
    (hds : ∀ i (h : i < ds.length), P.data.getD (iOL nD n k + (a + i)) 0 = σ ds[i])
    (hWo : iOL nD n k + (a + ds.length) ≤ W) {nw : List Instr} {nwv : D → ℤ} {c : Config}
    (hnw : NwOK P W B σ n nw ds nwv c)
    (hc : WordsBounded W c) {Fo : Forest} {G : List VT} (hS : LCTE B n Fo G c)
    {φ : D → ℤ} {fe : F} {Lo : ℝ} {T : DTree M.dual} {val₀ w₀ : D → ℤ}
    (hSt : Stored M n ιv ιg ιf ιe φ fe Lo Fo T val₀) (hKM : KMem M σ ιv T w₀ φ c)
    (h140 : c.nreg 140 = a) (h141 : c.nreg 141 = a + ds.length) :
    ∃ c' os G', ORun P W B n (wLoopS B nD n k nw) c Fo G c' os G' (5 * ds.length)
        (30 * ds.length + 2) ∧ os.length ≤ 4 * ds.length ∧ (runOpsE n Fo os).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ fe Lo (runOpsE n Fo os).1 T
        (fun d => if d ∈ ds then val₀ d + nwv d - w₀ d else val₀ d) ∧
      KMem M σ ιv T (fun d => if d ∈ ds then nwv d else w₀ d) φ c' ∧
      (∀ r, r < 140 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (∀ d : D, a ≠ aWT + σ d) →
        c'.rmem a = c.rmem a) := by
  have hI₀ : WInv M σ n ιv ιg ιf ιe B W k a ds φ fe Lo T val₀ nwv w₀ Fo c 0 [] G c :=
    ⟨hS, hc, by rw [wVal_zero]; exact hSt, rfl, by simp, Nat.zero_le _, by rw [h140]; rfl,
      h141, by rw [wWt_zero]; exact hKM, fun _ _ => ⟨rfl, rfl⟩, rfl, fun _ _ => rfl,
      fun _ _ _ => rfl⟩
  obtain ⟨i, os, c', G', hrun, hI, ht, -, -⟩ := ORun.whileLtN (α := ℕ) (P := P) (W := W)
    (B := B) (n := n) (a := 140) (b := 141) (body := wBodyS B nD n k nw) Fo
    (fun i hs G₁ c₁ => WInv M σ n ιv ιg ιf ιe B W k a ds φ fe Lo T val₀ nwv w₀ Fo c i hs G₁
      c₁) (fun i => 5 * i) (fun i => 30 * (ds.length - i)) (fun i hs G₁ c₁ h _ => ⟨h.lcte, h.wb⟩)
    (fun i hs G₁ c₁ h _ ht => by
      have hik : i < ds.length := by rw [h.r140, h.r141] at ht; omega
      obtain ⟨c₂, os, G₂, o, h'⟩ := wBody_orun hW hWa hB hP hL hK hnd hds hWo hnw i hs G₁ c₁ h hik
      exact ⟨i + 1, c₂, os, G₂, 5, 28, o, h', by ring, by omega⟩)
    (x := 0) (hs := []) hI₀ trivial
  simp only [List.nil_append] at hI
  have hik : i = ds.length := by
    have := hI.ile; rw [hI.r140, hI.r141] at ht; omega
  subst hik
  have htake : ds.take ds.length = ds := List.take_length
  refine ⟨c', os, G', hrun.mono (by omega) (by omega), by have := hI.len; omega, hI.out, ?_, ?_,
    hI.regs, hI.output, hI.nm, hI.rm⟩
  · have := hI.st; rw [wVal_length] at this; exact this
  · have := hI.kmem; rw [wWt_length] at this; exact this

/-! ### The changes of the weights between two moves -/

/-- The loop bounds of the out-darts of the vertex whose node is read from `off + σ b`,
`b = g r91`. -/
def wSetI (nD n k off : ℕ) : List Instr :=
  [.constN 148 (iGB nD n), .addN 148 148 91, .readIn 148 148,
    .constN 149 off, .addN 149 149 148, .readIn 149 149,
    .constN 140 (iOB nD n k), .addN 140 140 149, .readIn 140 140,
    .constN 141 (iOE nD n k), .addN 141 141 149, .readIn 141 141]

/-- The new weight `tripL` (from `TL`). -/
def nwA (nD : ℕ) : List Instr := [.constN 147 (aTL nD), .loadR 140 147]

/-- The new weight `ℓ d = φ d` (from `PH`). -/
def nwB (nD : ℕ) : List Instr := [.constN 147 (aPH nD), .addN 147 147 142, .loadR 140 147]

/-- **The changes of the weights between two moves**: the darts of the piece leaving the tail of
`b = g r91` get the weight `tripL`, those leaving its head their length. -/
def wtS (B nD n k : ℕ) : Stmt :=
  .seq (block (wSetI nD n k (iNT nD))) <| .seq (wLoopS B nD n k (nwA nD)) <|
  .seq (block (wSetI nD n k (iNH nD))) (wLoopS B nD n k (nwB nD))

theorem nwA_ok {ds : List D} {c₀ : Config} (hB3 : 3 * nD + 1 ≤ B) (hWa : 3 * nD ≤ W) {z : ℤ}
    (hz : c₀.rmem (aTL nD) = z) : NwOK P W B σ n (nwA nD) ds (fun _ => z) c₀ := by
  intro c d _ hc _ hrm
  have hz' : c.rmem (aTL nD) = z := by
    rw [hrm _ (Or.inl (by unfold aTL; omega)) (fun d' h => by
      have := (σ d').2; unfold aTL aWT at h; omega), hz]
  exec_block
  · unfold aTL; omega
  · refine ⟨by omega, by config_simp; exact hz', fun r hr => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [upd_other _ _ _ hr]
    · config_simp; simp only [upd_other _ _ _ hr]

theorem nwB_ok {ds : List D} {c₀ : Config} (hB : n + 2 * nD ≤ B) (hWa : 2 * nD ≤ W)
    {φ : D → ℤ} (hph : ∀ d, c₀.rmem (aPH nD + σ d) = φ d) :
    NwOK P W B σ n (nwB nD) ds φ c₀ := by
  intro c d _ hc h142 hrm
  have hσd := (σ d).2
  have hz' : c.rmem (aPH nD + σ d) = φ d := by
    rw [hrm _ (Or.inl (by unfold aPH; omega)) (fun d' h => by
      have := (σ d').2; unfold aPH aWT at h; omega), hph]
  exec_block
  · unfold aPH; omega
  · config_simp; rw [h142]; unfold aPH; omega
  · refine ⟨by omega, by config_simp; rw [h142]; exact hz', fun r hr => ?_, fun r hr => ?_, rfl,
      rfl, rfl⟩
    · config_simp; simp only [upd_other _ _ _ hr]
    · config_simp; simp only [upd_other _ _ _ hr]

/-- The loop bounds of the out-darts of a vertex. -/
theorem wSet_exec {k : ℕ} (hWa : 9 * nD + 4 * n + k ≤ W) (hP : ∀ i, P.data.getD i 0 ≤ W)
    (hL : Layout M n ιv ιg ιf ιe) {off : ℕ} (hoff : off + nD ≤ W) {b : D} {x : V}
    (hx : P.data.getD (off + σ b) 0 = ιv x) {c : Config} (hc : WordsBounded W c)
    (h91 : P.data.getD (iGB nD n + c.nreg 91) 0 = σ b) (h91' : iGB nD n + c.nreg 91 ≤ W) :
    ∃ c' k', Exec P W (block (wSetI nD n k off)) c c' k' ∧ k' = 12 ∧
      c'.nreg 140 = P.data.getD (iOB nD n k + ιv x) 0 ∧
      c'.nreg 141 = P.data.getD (iOE nD n k + ιv x) 0 ∧ GFr 140 150 c c' := by
  have hσ := (σ b).2
  have hxn := hL.prim.f_lt x
  unfold wSetI
  exec_block
  all_goals try (first
    | exact hP _
    | exact h91'
    | omega
    | (simp only [iGB, iOB, iOE]; omega)
    | (config_simp; simp only [h91, hx]; simp only [iOB, iOE]; omega)
    | (config_simp; simp only [h91]; omega))
  refine ⟨rfl, ?_, ?_, by gfr_tac⟩
  · config_simp; simp only [h91, hx]
  · config_simp; simp only [h91, hx]

/-- **The changes of the weights between the moves `j` and `j + 1` on the machine**: from the
stored data with the weights `tripWt j` in `WT` (and `tripL` in `TL`, `r91 = (j + 1) % k`), the
darts of `tripΔ j` get their new weights; at most `4 #(tripΔ j)` operations, printing nothing,
counted `5 #(tripΔ j)` operations and `30 #(tripΔ j) + 28` further steps; the values move by the
change of the weights, `WT` holds `tripWt (j + 1)`. -/
theorem wt_orun (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 4 * n + k ≤ W)
    (hB : n + 2 * nD ≤ B) (hB3 : 3 * nD + 1 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) {g : ℕ → D}
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    {j : ℕ} {c : Config} (hc : WordsBounded W c) {Fo : Forest} {G : List VT}
    (hS : LCTE B n Fo G c) {fe : F} {Lo : ℝ} {T : DTree M.dual} {val : D → ℤ}
    (hSt : Stored M n ιv ιg ιf ιe (tripφ S ℓ) fe Lo Fo T val)
    (hKM : KMem M σ ιv T (tripWt M k g S ℓ j) (tripφ S ℓ) c)
    (hTL : c.rmem (aTL nD) = tripL V S ℓ) (h91 : c.nreg 91 = (j + 1) % k) :
    ∃ c' os G', ORun P W B n (wtS B nD n k) c Fo G c' os G' (5 * (tripΔ M k g S j).card)
        (30 * (tripΔ M k g S j).card + 28) ∧ os.length ≤ 4 * (tripΔ M k g S j).card ∧
      (runOpsE n Fo os).2 = [] ∧
      Stored M n ιv ιg ιf ιe (tripφ S ℓ) fe Lo (runOpsE n Fo os).1 T
        (fun d => val d + tripWt M k g S ℓ (j + 1) d - tripWt M k g S ℓ j d) ∧
      KMem M σ ιv T (tripWt M k g S ℓ (j + 1)) (tripφ S ℓ) c' ∧
      (∀ r, r < 140 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (∀ d : D, a ≠ aWT + σ d) →
        c'.rmem a = c.rmem a) := by
  classical
  have hk := H.two_le_k
  set b := g ((j + 1) % k) with hb
  have hgb := hG _ (H.mod_lt (j + 1))
  have e1 : (j + 1 + 1) % k = ((j + 1) % k + 1) % k := (Nat.mod_add_mod _ _ _).symm
  have he'w : M.head b = tripDst M k g (j + 1) := by
    rw [hb, H.head_g _ (H.mod_lt _)]; unfold tripDst; rw [e1]
  have hwv : tripDst M k g (j + 1) ≠ tripDst M k g j := by
    intro h'
    exact H.mod_ne (j + 1) (H.face.inj _ (H.mod_lt (j + 1 + 1)) _ (H.mod_lt (j + 1)) h').symm
  have hmk := H.mod_lt (j + 1)
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  -- the darts leaving the target of the move `j`
  obtain ⟨ds₁, hnd₁, hm₁, he₁, hle₁, hds₁⟩ := hO (tripDst M k g j)
  obtain ⟨c₁, k₁, e₁, hk₁, p140, p141, g₁⟩ := wSet_exec (P := P) (k := k) hWa hP hL
    (off := iNT nD) (b := b) (x := tripDst M k g j) (by unfold iNT; omega) (hK.nt b) hc
    (by rw [h91, hgb]) (by rw [h91]; unfold iGB; omega)
  have o₁ := ORun.ofGFr e₁ hS g₁ (by omega)
  obtain ⟨c₂, os₂, G₂, o₂, hl₂, ho₂, hS₂, hKM₂, r₂, out₂, nm₂, rm₂⟩ := wLoop_orun (P := P) hW
    (by omega) hB hP hL hK hnd₁ (a := P.data.getD (iOB nD n k + ιv (tripDst M k g j)) 0)
    hds₁ (by rw [← he₁]; unfold iOL; omega)
    (nwA_ok (σ := σ) (n := n) (c₀ := c₁) hB3 (by omega) (by rw [g₁.2.2.1]; exact hTL))
    e₁.wb_right o₁.2.lcte hSt (hKM.congr g₁.memFrame hB hL) p140 (by rw [p141, he₁])
  -- the darts leaving the target of the move `j + 1`
  obtain ⟨ds₂, hnd₂, hm₂, he₂, hle₂, hds₂⟩ := hO (tripDst M k g (j + 1))
  have hc₂ := o₂.2.wb
  obtain ⟨c₃, k₃, e₃, hk₃, q140, q141, g₃⟩ := wSet_exec (P := P) (k := k) hWa hP hL
    (off := iNH nD) (b := b) (x := tripDst M k g (j + 1)) (by unfold iNH; omega)
    (by rw [hK.nh, he'w]) hc₂
    (by rw [(r₂ 91 (by omega)).1, (g₁.1 91 (by omega)).1, h91, hgb])
    (by rw [(r₂ 91 (by omega)).1, (g₁.1 91 (by omega)).1, h91]; unfold iGB; omega)
  have o₃ := ORun.ofGFr e₃ o₂.2.lcte g₃ (by omega)
  have hph : ∀ d, c₃.rmem (aPH nD + σ d) = tripφ S ℓ d := fun d => by
    rw [g₃.2.2.1]; exact hKM₂.ph d
  obtain ⟨c₄, os₄, G₄, o₄, hl₄, ho₄, hS₄, hKM₄, r₄, out₄, nm₄, rm₄⟩ := wLoop_orun (P := P) hW
    (by omega) hB hP hL hK hnd₂ (a := P.data.getD (iOB nD n k + ιv (tripDst M k g (j + 1))) 0)
    hds₂ (by rw [← he₂]; unfold iOL; omega)
    (nwB_ok (σ := σ) (n := n) (c₀ := c₃) (ds := ds₂) hB (by omega) hph)
    e₃.wb_right o₃.2.lcte hS₂ (hKM₂.congr g₃.memFrame hB hL) q140 (by rw [q141, he₂])
  -- the weights and the values
  have hΔ : ∀ d, d ∈ tripΔ M k g S j ↔ d ∈ ds₁ ∨ d ∈ ds₂ := fun d => by
    simp only [tripΔ, mem_filter, hm₁, hm₂]; tauto
  have hdisj : ∀ d, d ∈ ds₁ → d ∉ ds₂ := fun d h1 h2 =>
    hwv (((hm₂ d).1 h2).2.symm.trans ((hm₁ d).1 h1).2)
  have hcard : ds₁.length + ds₂.length = (tripΔ M k g S j).card := by
    have e : tripΔ M k g S j = (ds₁ ++ ds₂).toFinset := by
      ext d; rw [hΔ, List.mem_toFinset, List.mem_append]
    rw [e, List.toFinset_card_of_nodup (List.nodup_append.2 ⟨hnd₁, hnd₂,
      fun a ha b hb hab => hdisj a ha (hab ▸ hb)⟩), List.length_append]
  have hroot : IsRoot M k g (tripDst M k g j) := ⟨_, H.mod_lt (j + 1), rfl⟩
  have hw₁ : ∀ d ∈ ds₁, tripWt M k g S ℓ (j + 1) d = tripL V S ℓ := fun d hd => by
    have := (hm₁ d).1 hd
    unfold tripWt
    refine ite_eq_right_iff.2 ?_
    rintro ⟨-, hr⟩
    rw [this.2] at hr
    exact (hwv (H.eq_of_reach_root hr hroot).symm).elim
  have hw₂ : ∀ d ∈ ds₂, tripWt M k g S ℓ (j + 1) d = ℓ d := fun d hd => by
    have := (hm₂ d).1 hd
    exact tripWt_elig (j + 1) this.1 (by rw [this.2]; exact Reach.refl _)
  have hφ₂ : ∀ d ∈ ds₂, tripφ S ℓ d = ℓ d := fun d hd => tripφ_of_mem ((hm₂ d).1 hd).1
  have hwt : (fun d => if d ∈ ds₂ then tripφ S ℓ d else
      if d ∈ ds₁ then tripL V S ℓ else tripWt M k g S ℓ j d) = tripWt M k g S ℓ (j + 1) := by
    funext d
    by_cases h2 : d ∈ ds₂
    · simp only [h2, ↓reduceIte, hφ₂ d h2, hw₂ d h2]
    · simp only [h2, ↓reduceIte]
      by_cases h1 : d ∈ ds₁
      · simp only [h1, ↓reduceIte, hw₁ d h1]
      · simp only [h1, ↓reduceIte]
        rw [tripWt_succ H hR j (fun h => by rcases (hΔ d).1 h with h | h <;> tauto)]
  have hval : (fun d => if d ∈ ds₂ then
      (if d ∈ ds₁ then val d + tripL V S ℓ - tripWt M k g S ℓ j d else val d) + tripφ S ℓ d -
        (if d ∈ ds₁ then tripL V S ℓ else tripWt M k g S ℓ j d)
      else (if d ∈ ds₁ then val d + tripL V S ℓ - tripWt M k g S ℓ j d else val d)) =
      fun d => val d + tripWt M k g S ℓ (j + 1) d - tripWt M k g S ℓ j d := by
    funext d
    have := congrFun hwt d
    rw [← this]
    by_cases h2 : d ∈ ds₂
    · have h1 : d ∉ ds₁ := fun h1 => hdisj d h1 h2
      simp only [h2, h1, ↓reduceIte]
    · by_cases h1 : d ∈ ds₁ <;> simp only [h2, h1, ↓reduceIte]; ring
  have ho₂' : (runOpsE n Fo os₂).2 = [] := ho₂
  have ho₄' : (runOpsE n (runOpsE n Fo os₂).1 os₄).2 = [] := ho₄
  have o := o₁.seq (o₂.seq (o₃.seq o₄))
  simp only [List.nil_append] at o
  have hrun : (runOpsE n (runOpsE n Fo os₂).1 os₄).1 = (runOpsE n Fo (os₂ ++ os₄)).1 := by
    rw [runOpsE_fst_append]
  refine ⟨c₄, os₂ ++ os₄, G₄, o.mono (by omega) (by omega), by
    rw [List.length_append]; omega, by rw [runOpsE_append, ho₂', ho₄']; rfl, ?_, ?_,
    fun r hr => ?_, by rw [out₄, g₃.2.2.2, out₂, g₁.2.2.2], fun a ha => ?_,
    fun a ha hne => ?_⟩
  · rw [← hrun, ← hval]; exact hS₄
  · rw [← hwt]; exact hKM₄
  · rw [(r₄ r hr).1, (r₄ r hr).2, (g₃.1 r (by omega)).1, (g₃.1 r (by omega)).2, (r₂ r hr).1,
      (r₂ r hr).2, (g₁.1 r (by omega)).1, (g₁.1 r (by omega)).2]
    exact ⟨rfl, rfl⟩
  · rw [nm₄ a ha, g₃.2.1, nm₂ a ha, g₁.2.1]
  · rw [rm₄ a ha hne, g₃.2.2.1, rm₂ a ha hne, g₁.2.2.1]

/-- **From the end of the move `j` to the start of the move `j + 1` on the machine**: the trees
(`nxAS`, `nxA_orun`) and the weights (`wtS`, `wt_orun`): the operations of `next_stored`, at most
`18 + 4 #(tripΔ j)`, printing nothing, counted `29 + 5 #(tripΔ j)` operations and
`30 #(tripΔ j) + 153` further steps; the forest stores data at the start of the move `j + 1`
(`StartOK`) linked to the end of the move `j` as in `IsTrip`, `TP` and `WT` hold the tree and the
weights `tripWt (j + 1)`, and `r100`, `r101` the query nodes of the move `j + 1`. -/
theorem nx_orun (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 4 * n + k ≤ W)
    (hB : n + 2 * nD ≤ B) (hB3 : 3 * nD + 1 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) {g : ℕ → D}
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    {j : ℕ} {R : MoveData M S} (h : MoveSpec M k g S ℓ j R) {c : Config} (hc : WordsBounded W c)
    {Fo : Forest} {G : List VT} (hS : LCTE B n Fo G c) {Lo : ℝ}
    (hSt : Stored M n ιv ιg ιf ιe (tripφ S ℓ) (M.face (g (j % k))) Lo Fo (R.T R.m) (R.val R.m))
    (hKM : KMem M σ ιv (R.T R.m) (tripWt M k g S ℓ j) (tripφ S ℓ) c)
    (hTL : c.rmem (aTL nD) = tripL V S ℓ) (h90 : c.nreg 90 = j % k)
    (h91 : c.nreg 91 = (j + 1) % k) (h101 : c.nreg 101 = ιf (M.face (g (j % k)))) :
    ∃ (c' : Config) (G' : List VT) (os : List EOp) (T' : DTree M.dual) (val' : D → ℤ),
      ORun P W B n (.seq (nxAS B nD n) (wtS B nD n k)) c Fo G c' os G'
        (29 + 5 * (tripΔ M k g S j).card) (30 * (tripΔ M k g S j).card + 153) ∧
      os.length ≤ 18 + 4 * (tripΔ M k g S j).card ∧ (runOpsE n Fo os).2 = [] ∧
      Stored M n ιv ιg ιf ιe (tripφ S ℓ) (M.face (g ((j + 1) % k))) (Lo - tripK V S ℓ)
        (runOpsE n Fo os).1 T' val' ∧
      StartOK M k g S ℓ (j + 1) T' val' ∧ T'.root = tripDst M k g j ∧
      T'.par (tripDst M k g (j + 1)) = g ((j + 1) % k) ∧
      (tripDst M k g (j + 1) ≠ tripSrc M k g j →
        T'.par (tripSrc M k g j) = M.rev (g (j % k))) ∧
      (∀ x, x ≠ tripSrc M k g j → x ≠ tripDst M k g (j + 1) → T'.par x = (R.T R.m).par x) ∧
      KMem M σ ιv T' (tripWt M k g S ℓ (j + 1)) (tripφ S ℓ) c' ∧
      c'.nreg 100 = ιf (M.face (M.rev (g ((j + 1) % k)))) ∧
      c'.nreg 101 = ιf (M.face (g ((j + 1) % k))) ∧
      (∀ r, r < 100 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (∀ d : D, a ≠ aWT + σ d) →
        c'.rmem a = c.rmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → n ≤ a → c'.nmem a = c.nmem a) := by
  classical
  have hC := h.1.compat R.m le_rfl
  rw [end_tpar H hR h] at hC
  obtain ⟨c₁, G₁, os₁, T', val₂, o₁, hl₁, ho₁, hS₁, hV₁, hr₁, hpw, hpu, hpx, hKM₁, x100, x101,
    r₁, out₁, rm₁, nm₁⟩ := nxA_orun hW (by omega) hB hP H hR hL hK hG h hc hS hSt hKM h90 h91 h101
  have hTL₁ : c₁.rmem (aTL nD) = tripL V S ℓ := by
    rw [rm₁ _ (Or.inl (by unfold aTL; omega))]; exact hTL
  obtain ⟨c₂, os₂, G₂, o₂, hl₂, ho₂, hS₂, hKM₂, r₂, out₂, nm₂, rm₂⟩ := wt_orun hW hWa hB hB3 hP
    H hR hL hK hG hO o₁.2.wb o₁.2.lcte hS₁ hKM₁ hTL₁ (by rw [(r₁ 91 (by omega)).1, h91])
  have o := o₁.seq o₂
  have hrun : (runOpsE n (runOpsE n Fo os₁).1 os₂).1 = (runOpsE n Fo (os₁ ++ os₂)).1 := by
    rw [runOpsE_fst_append]
  rw [hrun] at hS₂
  refine ⟨c₂, G₂, os₁ ++ os₂, T', _, o.mono (by omega) (by omega), by
    rw [List.length_append]; omega, by rw [runOpsE_append, ho₁, ho₂]; rfl, hS₂,
    ⟨⟨hr₁, hpw, rfl, ?_⟩, ?_⟩, hr₁, hpw, hpu, hpx, hKM₂, by rw [(r₂ 100 (by omega)).1, x100],
    by rw [(r₂ 101 (by omega)).1, x101], fun r hr => ?_, by rw [out₂, out₁],
    fun a ha hne => ?_, fun a ha han => ?_⟩
  · intro x a hx
    obtain ⟨-, hd, -⟩ := tpar_spec hx
    have hnr : ∀ i < k, x ≠ M.tail (g i) := fun i hi h' =>
      H.noIn a.1 a.2 ⟨i, hi, by rw [← h', ← hd]; rfl⟩
    rw [hpx x (hnr _ (H.mod_lt j)) (hnr _ (H.mod_lt (j + 1 + 1)))]
    exact hC.par x a hx
  · intro d hd
    show val₂ d + _ - _ = _
    rw [hV₁ d hd]; ring
  · rw [(r₂ r (by omega)).1, (r₂ r (by omega)).2]; exact r₁ r hr
  · rw [rm₂ a ha hne]; exact rm₁ a ha
  · rw [nm₂ a ha]; exact nm₁ a ha han

end

end Klein

end PlanarFlow
