module

public import PlanarFlow.Dijkstra.Heap
public import PlanarFlow.NegSSSP.Enc.NodeBFA

/-!
# Dijkstra's algorithm in memory, on natural words: the program and the heap routines

The heap Dijkstra of `PlanarFlow/Dijkstra/` reads its graph from the input tape and keeps its
arrays at fixed addresses. Here the same algorithm (a tournament tree over the `n` nodes with
decrease-key, `O((n + m) log n)`) runs **on arrays in memory at base addresses given in
registers**, reading the graph from **out-lists**: the arcs of the node `y < n` are the
indices `i ∈ [ob y, oe y)`; the arc `i` is the dart `a = ol i` (word at `OLb + i`), of head
`nh a` (at `NHb + a`) and length `ln a` (at `Lb + a`). This is the layout of the out-lists of a
piece written by `osProg` (`FeOut`, `outMem_snd`) and of the dart arrays of the encoder.

`DkP`: the bases and the arcs (as functions); `DkG`: well-formedness for the word bound `W`
(every address read below `W` and outside the written region `[Db, Db + n) ∪ [Xb, Xb + 3n)`);
`DkMem`: the memory holds the arcs. Memory written: the distances `D[y]` at `Db + y`, the done
marks at `Xb + y`, the tree at `Xb + n + i` (`1 ≤ i < 2n`, leaf of `y` at `i = n + y`).

Registers: natural `2500 … 2510` (inputs `n`, `Db`, `Xb`, `Xb + n` (set), `OBb`, `OEb`, `OLb`,
`NHb`, `Lb`, `Inf`, the source `s`), `2511 … 2514` (constants `0`, `1`, `2`, `2n`),
`2520 … 2547` (scratch). Natural instructions only.

This file: the program `dkProg`, the registers `DkRegs`, the recomputation of a path of the tree
(`dkUpd_exec`) and the descent to the minimum (`dkDesc_exec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset Heap

/-- **The parameters of Dijkstra in memory**: the bases and the arcs. -/
structure DkP where
  n : ℕ
  Db : ℕ
  Xb : ℕ
  OBb : ℕ
  OEb : ℕ
  OLb : ℕ
  NHb : ℕ
  Lb : ℕ
  Inf : ℕ
  s : ℕ
  ob : ℕ → ℕ
  oe : ℕ → ℕ
  ol : ℕ → ℕ
  nh : ℕ → ℕ
  ln : ℕ → ℕ

/-- The region written by the program. -/
def DkOut (p : DkP) (a : ℕ) : Prop :=
  (p.Db ≤ a ∧ a < p.Db + p.n) ∨ (p.Xb ≤ a ∧ a < p.Xb + 3 * p.n)

/-- **Well-formed parameters** for the word bound `W`. -/
structure DkG (p : DkP) (W : ℕ) : Prop where
  n_pos : 1 ≤ p.n
  s_lt : p.s < p.n
  wD : p.Db + p.n ≤ W
  wX : p.Xb + 3 * p.n ≤ W
  dDX : p.Db + p.n ≤ p.Xb ∨ p.Xb + 3 * p.n ≤ p.Db
  infW : p.Inf ≤ W
  ob_le : ∀ y < p.n, p.ob y ≤ p.oe y
  aOB : ∀ y < p.n, p.OBb + y ≤ W ∧ ¬ DkOut p (p.OBb + y)
  aOE : ∀ y < p.n, p.OEb + y ≤ W ∧ ¬ DkOut p (p.OEb + y)
  aOL : ∀ y < p.n, ∀ i, p.ob y ≤ i → i < p.oe y → p.OLb + i ≤ W ∧ ¬ DkOut p (p.OLb + i)
  aNH : ∀ y < p.n, ∀ i, p.ob y ≤ i → i < p.oe y →
    p.NHb + p.ol i ≤ W ∧ ¬ DkOut p (p.NHb + p.ol i)
  aL : ∀ y < p.n, ∀ i, p.ob y ≤ i → i < p.oe y → p.Lb + p.ol i ≤ W ∧ ¬ DkOut p (p.Lb + p.ol i)
  nh_lt : ∀ y < p.n, ∀ i, p.ob y ≤ i → i < p.oe y → p.nh (p.ol i) < p.n
  inf_le : ∀ y < p.n, ∀ i, p.ob y ≤ i → i < p.oe y → p.Inf + p.ln (p.ol i) ≤ W

/-- **The arcs in memory.** -/
structure DkMem (p : DkP) (m : ℕ → ℕ) : Prop where
  ob : ∀ y < p.n, m (p.OBb + y) = p.ob y
  oe : ∀ y < p.n, m (p.OEb + y) = p.oe y
  ol : ∀ y < p.n, ∀ i, p.ob y ≤ i → i < p.oe y → m (p.OLb + i) = p.ol i
  nh : ∀ y < p.n, ∀ i, p.ob y ≤ i → i < p.oe y → m (p.NHb + p.ol i) = p.nh (p.ol i)
  ln : ∀ y < p.n, ∀ i, p.ob y ≤ i → i < p.oe y → m (p.Lb + p.ol i) = p.ln (p.ol i)

theorem DkMem.of {p : DkP} {W : ℕ} (hG : DkG p W) {m m' : ℕ → ℕ} (h : DkMem p m)
    (hf : ∀ a, ¬ DkOut p a → m' a = m a) : DkMem p m' :=
  ⟨fun y hy => (hf _ (hG.aOB y hy).2).trans (h.ob y hy),
    fun y hy => (hf _ (hG.aOE y hy).2).trans (h.oe y hy),
    fun y hy i h1 h2 => (hf _ (hG.aOL y hy i h1 h2).2).trans (h.ol y hy i h1 h2),
    fun y hy i h1 h2 => (hf _ (hG.aNH y hy i h1 h2).2).trans (h.nh y hy i h1 h2),
    fun y hy i h1 h2 => (hf _ (hG.aL y hy i h1 h2).2).trans (h.ln y hy i h1 h2)⟩

/-- **The walks from the source** along the out-lists: `DkReach p y L` if some walk from `s`
to `y` has length `L`. -/
inductive DkReach (p : DkP) : ℕ → ℕ → Prop
  | src : DkReach p p.s 0
  | step {u L i : ℕ} : DkReach p u L → u < p.n → p.ob u ≤ i → i < p.oe u →
      DkReach p (p.nh (p.ol i)) (L + p.ln (p.ol i))

/-! ### The program -/

/-- Constants: `0`, `1`, `2`, `2n`, the base `Xb + n` of the tree, the counter. -/
def dkSetup : Stmt := block [.constN 2511 0, .constN 2512 1, .constN 2513 2, .addN 2514 2500 2500,
  .addN 2503 2502 2500, .constN 2520 0]

/-- One node: `D[y] := Inf`, `done[y] := 0`. -/
def dkInitStep : Stmt := block [.addN 2521 2501 2520, .storeN 2521 2509, .addN 2521 2502 2520,
  .storeN 2521 2511, .addN 2520 2520 2512]

/-- One tree node set to `Inf`. -/
def dkTreeStep : Stmt := block [.addN 2521 2503 2520, .storeN 2521 2509, .addN 2520 2520 2512]

/-- One step of the recomputation of the path from `r2530` to the root. -/
def dkUpdBody : Stmt :=
  .seq (block [.mulN 2531 2530 2513, .addN 2532 2503 2531, .loadN 2533 2532,
      .addN 2532 2532 2512, .loadN 2534 2532, .addN 2535 2503 2530])
    (.seq (.ifLtN 2534 2533 (.instr (.storeN 2535 2534)) (.instr (.storeN 2535 2533)))
      (.instr (.divN 2530 2530 2513)))

/-- Recompute the path from `r2530` to the root. -/
def dkUpd : Stmt := .whileLtN 2511 2530 dkUpdBody

/-- One step down from `r2536` towards the smaller child. -/
def dkDescBody : Stmt :=
  .seq (block [.mulN 2531 2536 2513, .addN 2532 2503 2531, .loadN 2533 2532,
      .addN 2532 2532 2512, .loadN 2534 2532])
    (.ifLtN 2534 2533 (block [.mulN 2536 2536 2513, .addN 2536 2536 2512])
      (.instr (.mulN 2536 2536 2513)))

/-- Follow the minimum from the root down to a leaf `r2536`. -/
def dkDesc : Stmt := .seq (.instr (.copyN 2536 2512)) (.whileLtN 2536 2500 dkDescBody)

/-- Relax the arc `r2540` of the node being processed, of key `r2537`. -/
def dkRelax : Stmt :=
  .seq (block [.addN 2542 2506 2540, .loadN 2542 2542, .addN 2543 2507 2542, .loadN 2543 2543,
      .addN 2544 2508 2542, .loadN 2544 2544, .addN 2544 2544 2537, .addN 2545 2501 2543,
      .loadN 2546 2545])
    (.seq (.ifLtN 2544 2546 (.seq (block [.storeN 2545 2544, .addN 2530 2500 2543,
        .addN 2547 2503 2530, .storeN 2547 2544, .divN 2530 2530 2513]) dkUpd) .skip)
      (.instr (.addN 2540 2540 2512)))

/-- One round: extract the node of least key and relax its arcs. -/
def dkRound : Stmt :=
  .seq dkDesc <| .seq (block [.subN 2539 2536 2500, .addN 2547 2502 2539, .storeN 2547 2512,
    .addN 2547 2503 2536, .storeN 2547 2509, .divN 2530 2536 2513]) <| .seq dkUpd <|
  .seq (block [.addN 2547 2504 2539, .loadN 2540 2547, .addN 2547 2505 2539, .loadN 2541 2547]) <|
  .seq (.whileLtN 2540 2541 dkRelax) (block [.addN 2547 2503 2512, .loadN 2537 2547])

/-- The initialization, followed by `t`. -/
def dkInitPart (t : Stmt) : Stmt := .seq dkSetup <| .seq (.whileLtN 2520 2500 dkInitStep) <|
  .seq (.instr (.constN 2520 1)) <| .seq (.whileLtN 2520 2514 dkTreeStep) <|
  .seq (block [.addN 2547 2501 2510, .storeN 2547 2511, .addN 2530 2500 2510,
    .addN 2547 2503 2530, .storeN 2547 2511, .divN 2530 2530 2513]) <|
  .seq dkUpd <| .seq (block [.addN 2547 2503 2512, .loadN 2537 2547]) t

/-- **Dijkstra's algorithm in memory.** -/
def dkProg : Stmt := dkInitPart (.whileLtN 2537 2509 dkRound)

/-- **No real instruction** (checked by the kernel). -/
theorem dkProg_natOnly : Klein.natOnly dkProg = true := by kernel_rfl

/-- **Only the registers `2500 … 2547` are written** (checked by the kernel). -/
theorem dkProg_keeps : nbKeepsBelow 2500 dkProg = true := by kernel_rfl

/-- The natural instructions without input, output or randomness. -/
def dkPure : Instr → Bool
  | .constN _ _ | .copyN _ _ | .addN _ _ _ | .subN _ _ _ | .mulN _ _ _ | .divN _ _ _
  | .modN _ _ _ | .loadN _ _ | .storeN _ _ => true
  | _ => false

/-- **A run of pure natural instructions keeps the reals and the output.** -/
theorem dk_exec_pure {P : Input} {W : ℕ} {s : Stmt} {c d : Config} {k : ℕ}
    (e : Exec P W s c d k) (h : s.allI dkPure = true) :
    d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output := by
  refine Exec.of_steps (R := fun c d => d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output)
    (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ _ _ h₁ h₂ => ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1,
      h₂.2.2.trans h₁.2.2⟩) (fun i c c' _ hi he => ?_) e h
  cases i <;> simp only [dkPure, Bool.false_eq_true] at hi <;>
    simp only [Instr.effect, Option.some.injEq] at he <;>
    (try split_ifs at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;>
    subst he <;> exact ⟨rfl, rfl, rfl⟩

theorem dkProg_pure : dkProg.allI dkPure = true := by kernel_rfl

/-- Registers outside `[2500, 2548)` are kept. -/
theorem dk_exec_keep {P : Input} {W : ℕ} {c d : Config} {k : ℕ} (e : Exec P W dkProg c d k) :
    ∀ r, r < 2500 ∨ 2548 ≤ r → d.nreg r = c.nreg r := by
  intro r hr
  rcases hr with hr | hr
  · exact nb_exec_keep e dkProg_keeps r hr
  · refine e.nreg_keep (nb_allI_mono (f := fun i => match i.wN with
      | some r => decide (r < 2548) | none => true) (fun i hi => ?_) _ (by kernel_rfl))
    simp only [decide_eq_true_eq]
    intro hw; rw [hw] at hi; simp only [decide_eq_true_eq] at hi; omega

/-! ### Registers and memory -/

/-- The constant registers. -/
def DkRegs (p : DkP) (c : Config) : Prop :=
  c.nreg 2500 = p.n ∧ c.nreg 2501 = p.Db ∧ c.nreg 2502 = p.Xb ∧ c.nreg 2503 = p.Xb + p.n ∧
    c.nreg 2504 = p.OBb ∧ c.nreg 2505 = p.OEb ∧ c.nreg 2506 = p.OLb ∧ c.nreg 2507 = p.NHb ∧
    c.nreg 2508 = p.Lb ∧ c.nreg 2509 = p.Inf ∧ c.nreg 2510 = p.s ∧ c.nreg 2511 = 0 ∧
    c.nreg 2512 = 1 ∧ c.nreg 2513 = 2 ∧ c.nreg 2514 = 2 * p.n

theorem dkRegs_of {p : DkP} {c c' : Config} (hR : DkRegs p c)
    (h : ∀ r, 2500 ≤ r → r < 2515 → c'.nreg r = c.nreg r) : DkRegs p c' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | exact (h _ (by norm_num) (by norm_num)).trans ‹_›

/-- The tree, on the memory `m`. -/
def dkT (p : DkP) (m : ℕ → ℕ) (i : ℕ) : ℕ := m (p.Xb + p.n + i)

/-! ### The heap routines -/

variable {P : Input} {W : ℕ}

/-- The state of `dkUpd`, started from `c₀`. -/
structure DkIU (p : DkP) (W : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  keep : ∀ r, (r < 2530 ∨ 2536 ≤ r) → c.nreg r = c₀.nreg r
  r30 : c.nreg 2530 < p.n
  exc : IsTourExc p.n (dkT p c.nmem) (c.nreg 2530)
  frame : ∀ a, (a < p.Xb + p.n + 1 ∨ p.Xb + 2 * p.n ≤ a) → c.nmem a = c₀.nmem a

theorem dkUpdBody_exec {p : DkP} (hG : DkG p W) {c₀ : Config} (hR : DkRegs p c₀) (c : Config)
    (hI : DkIU p W c₀ c) (hlt : c.nreg 2511 < c.nreg 2530) :
    ∃ c' k, Exec P W dkUpdBody c c' k ∧ DkIU p W c₀ c' ∧ lg (c'.nreg 2530) * 13 + k + 2 ≤
      lg (c.nreg 2530) * 13 := by
  have hc := hI.wb
  have hX := hG.wX
  have hR' := dkRegs_of hR fun r h1 h2 => hI.keep r (Or.inl (by omega))
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hR'
  rw [h11] at hlt
  have hj := hI.r30
  unfold dkUpdBody
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h13]; omega
  · config_simp; rw [h13, h3]; omega
  · config_simp; rw [h13, h3, h12]; omega
  · config_simp; rw [h3]; omega
  config_simp
  refine spec_seq ?_
  have hlg := lg_pos (show 1 ≤ c.nreg 2530 by omega)
  have hmin : ∀ x : ℕ, x = min (dkT p c.nmem (2 * c.nreg 2530))
      (dkT p c.nmem (2 * c.nreg 2530 + 1)) →
      ∀ c' : Config, WordsBounded W c' → (∀ r, (r < 2530 ∨ 2536 ≤ r) → c'.nreg r = c.nreg r) →
      c'.nreg 2530 = c.nreg 2530 / 2 →
      c'.nmem = upd c.nmem (p.Xb + p.n + c.nreg 2530) x → DkIU p W c₀ c' := by
    intro x hx c' hw hK h40 hm
    refine ⟨hw, fun r hr => (hK r hr).trans (hI.keep r hr), by omega, ?_, fun a ha => ?_⟩
    · rw [h40]
      refine isTourExc_step hI.exc (by omega) hj (fun a ha => ?_) ?_
      · simp only [dkT, hm]; rw [upd_other _ _ _ (by omega)]
      · simp only [dkT, hm, upd_same]; exact hx
    · rw [hm, upd_other _ _ _ (by omega)]; exact hI.frame a ha
  by_cases hcmp : c.nmem (c.nreg 2503 + c.nreg 2530 * c.nreg 2513 + c.nreg 2512) <
      c.nmem (c.nreg 2503 + c.nreg 2530 * c.nreg 2513)
  · refine spec_ifLtN_true (by config_simp; exact hcmp) ?_
    refine spec_instr (Exec.storeN ‹_› _ _) fun hw => ?_
    refine spec_instr (Exec.divN hw _ _ _) fun hw' => ?_
    have hcmp' : dkT p c.nmem (2 * c.nreg 2530 + 1) < dkT p c.nmem (2 * c.nreg 2530) := by
      simp only [dkT]; rw [h3, h13, h12] at hcmp; convert hcmp using 2 <;> ring
    refine ⟨hmin (c.nmem (c.nreg 2503 + c.nreg 2530 * c.nreg 2513 + c.nreg 2512)) ?_ _ hw'
      (fun r hr => ?_) (by config_simp; rw [h13]) (by config_simp; rw [h3]), ?_⟩
    · rw [min_eq_right hcmp'.le]; simp only [dkT]; rw [h3, h13, h12]; congr 1; ring
    · config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega
    · config_simp; rw [h13, hlg]; have := lg_mono (Nat.div_le_self (c.nreg 2530) 2); omega
  · refine spec_ifLtN_false (by config_simp; exact hcmp) ?_
    refine spec_instr (Exec.storeN ‹_› _ _) fun hw => ?_
    refine spec_instr (Exec.divN hw _ _ _) fun hw' => ?_
    have hcmp' : ¬ dkT p c.nmem (2 * c.nreg 2530 + 1) < dkT p c.nmem (2 * c.nreg 2530) := by
      simp only [dkT]; rw [h3, h13, h12] at hcmp; convert hcmp using 3 <;> ring
    refine ⟨hmin (c.nmem (c.nreg 2503 + c.nreg 2530 * c.nreg 2513)) ?_ _ hw' (fun r hr => ?_)
      (by config_simp; rw [h13]) (by config_simp; rw [h3]), ?_⟩
    · rw [min_eq_left (not_lt.1 hcmp')]; simp only [dkT]; rw [h3, h13]; congr 1; ring
    · config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega
    · config_simp; rw [h13, hlg]; omega

/-- **The recomputation of a path.** From `r2530 = j < n` with the tournament property broken
only at the ancestors of `j`, `dkUpd` restores it within `13 lg j + 2` steps, changing only the
internal nodes of the tree and the registers `2530 … 2535`. -/
theorem dkUpd_exec {p : DkP} (hG : DkG p W) (c : Config) (hc : WordsBounded W c)
    (hR : DkRegs p c) (hj : c.nreg 2530 < p.n) (hexc : IsTourExc p.n (dkT p c.nmem) (c.nreg 2530)) :
    ∃ c' k, Exec P W dkUpd c c' k ∧ WordsBounded W c' ∧
      (∀ r, (r < 2530 ∨ 2536 ≤ r) → c'.nreg r = c.nreg r) ∧
      IsTour p.n (dkT p c'.nmem) ∧
      (∀ a, (a < p.Xb + p.n + 1 ∨ p.Xb + 2 * p.n ≤ a) → c'.nmem a = c.nmem a) ∧
      k ≤ lg (c.nreg 2530) * 13 + 2 := by
  obtain ⟨c', k, e, hI, hn, hk⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 2511)
    (b := 2530) (body := dkUpdBody) (DkIU p W c) (fun c => lg (c.nreg 2530) * 13)
    (fun c h => h.wb)
    (fun c' hc' hlt => dkUpdBody_exec hG hR c' hc' hlt)
    ⟨hc, fun _ _ => rfl, hj, hexc, fun _ _ => rfl⟩
  have h0 : c'.nreg 2511 = 0 := (hI.keep 2511 (Or.inl (by omega))).trans hR.2.2.2.2.2.2.2.2.2.2.2.1
  have h40 : c'.nreg 2530 = 0 := by rw [h0] at hn; omega
  have := hI.exc
  rw [h40] at this
  exact ⟨c', k, e, hI.wb, hI.keep, isTour_of_exc this, hI.frame, hk⟩

/-- The state of the descent. -/
structure DkIDs (p : DkP) (W : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  keep : ∀ r, (r < 2531 ∨ (2536 < r)) → c.nreg r = c₀.nreg r
  mem : c.nmem = c₀.nmem
  r36 : 1 ≤ c.nreg 2536 ∧ c.nreg 2536 < 2 * p.n
  val : dkT p c.nmem (c.nreg 2536) = dkT p c.nmem 1

theorem dkDescBody_exec {p : DkP} (hG : DkG p W) {c₀ : Config} (hR : DkRegs p c₀)
    (hT : IsTour p.n (dkT p c₀.nmem)) (c : Config) (hI : DkIDs p W c₀ c)
    (hlt : c.nreg 2536 < c.nreg 2500) :
    ∃ c' k, Exec P W dkDescBody c c' k ∧ DkIDs p W c₀ c' ∧
      (lg (2 * p.n) - lg (c'.nreg 2536)) * 10 + k + 2 ≤ (lg (2 * p.n) - lg (c.nreg 2536)) * 10 := by
  have hc := hI.wb
  have hX := hG.wX
  have hR' := dkRegs_of hR fun r h1 h2 => hI.keep r (by omega)
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hR'
  rw [h0] at hlt
  have hi := hI.r36
  have hmin := hT (c.nreg 2536) hi.1 hlt
  rw [← hI.mem] at hmin
  have hval := hI.val
  have hL : lg (2 * c.nreg 2536 + 1) ≤ lg (2 * p.n) := lg_mono (by omega)
  have hL2 := lg_two_mul hi.1
  have hL3 := lg_two_mul_add_one (c.nreg 2536)
  unfold dkDescBody
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h13]; omega
  · config_simp; rw [h13, h3]; omega
  · config_simp; rw [h13, h3, h12]; omega
  config_simp
  by_cases hcmp : c.nmem (c.nreg 2503 + c.nreg 2536 * c.nreg 2513 + c.nreg 2512) <
      c.nmem (c.nreg 2503 + c.nreg 2536 * c.nreg 2513)
  · refine spec_ifLtN_true (by config_simp; exact hcmp) ?_
    exec_block
    · config_simp; rw [h13]; omega
    · config_simp; rw [h13, h12]; omega
    have hcmp' : dkT p c.nmem (2 * c.nreg 2536 + 1) < dkT p c.nmem (2 * c.nreg 2536) := by
      simp only [dkT]; rw [h3, h13, h12] at hcmp; convert hcmp using 2 <;> ring
    refine ⟨⟨‹_›, fun r hr => ?_, by config_simp; exact hI.mem,
      by config_simp; rw [h13, h12]; omega, ?_⟩, ?_⟩
    · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hI.keep r hr
    · config_simp; rw [h13, h12, ← hval, hmin, min_eq_right hcmp'.le]
      simp only [dkT]; congr 1; ring
    · config_simp; rw [h13, h12, show c.nreg 2536 * 2 + 1 = 2 * c.nreg 2536 + 1 by ring, hL3]
      omega
  · refine spec_ifLtN_false (by config_simp; exact hcmp) ?_
    refine spec_instr (Exec.mulN ‹_› _ _ _ (by config_simp; rw [h13]; omega)) fun hw => ?_
    have hcmp' : ¬ dkT p c.nmem (2 * c.nreg 2536 + 1) < dkT p c.nmem (2 * c.nreg 2536) := by
      simp only [dkT]; rw [h3, h13, h12] at hcmp; convert hcmp using 3 <;> ring
    refine ⟨⟨hw, fun r hr => ?_, by config_simp; exact hI.mem, by config_simp; rw [h13]; omega,
      ?_⟩, ?_⟩
    · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hI.keep r hr
    · config_simp; rw [h13, ← hval, hmin, min_eq_left (not_lt.1 hcmp')]
      simp only [dkT]; congr 1; ring
    · config_simp; rw [h13, show c.nreg 2536 * 2 = 2 * c.nreg 2536 by ring, hL2]; omega

/-- **The descent.** Following the smaller child from the root reaches a leaf holding the
minimum, within `10 lg (2n) + 3` steps. -/
theorem dkDesc_exec {p : DkP} (hG : DkG p W) (c : Config) (hc : WordsBounded W c)
    (hR : DkRegs p c) (hT : IsTour p.n (dkT p c.nmem)) :
    ∃ c' k, Exec P W dkDesc c c' k ∧ WordsBounded W c' ∧
      (∀ r, (r < 2531 ∨ 2536 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ p.n ≤ c'.nreg 2536 ∧ c'.nreg 2536 < 2 * p.n ∧
      dkT p c.nmem (c'.nreg 2536) = dkT p c.nmem 1 ∧ k ≤ lg (2 * p.n) * 10 + 3 := by
  have hn := hG.n_pos
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hR
  have e₁ := Exec.copyN (P := P) hc 2536 2512
  have hI : DkIDs p W c { c with nreg := upd c.nreg 2536 (c.nreg 2512) } := by
    refine ⟨e₁.wb_right, fun r hr => ?_, rfl, ?_, ?_⟩
    · config_simp; rw [upd_other _ _ _ (by omega)]
    · config_simp; rw [h12]; omega
    · config_simp; rw [h12]
  obtain ⟨c', k, e, hI', hn', hk⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 2536)
    (b := 2500) (body := dkDescBody) (DkIDs p W c)
    (fun c' => (lg (2 * p.n) - lg (c'.nreg 2536)) * 10) (fun c h => h.wb)
    (fun c' hc' hlt => dkDescBody_exec hG ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      h13, h14⟩ hT c' hc' hlt) hI
  have h0' : c'.nreg 2500 = p.n := (hI'.keep 2500 (by omega)).trans h0
  have hge : p.n ≤ c'.nreg 2536 := by rw [h0'] at hn'; omega
  refine ⟨c', 1 + k, .seq e₁ e, hI'.wb, fun r hr => hI'.keep r hr, hI'.mem, hge, hI'.r36.2,
    by rw [← hI'.mem]; exact hI'.val, ?_⟩
  beta_reduce at hk; config_simp at hk; omega

end NegSSSP

end PlanarFlow
