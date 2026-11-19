module

public import PlanarFlow.Monge.FRQuery
public import PlanarFlow.Monge.FRMongeHeap
public import PlanarFlow.Monge.FRHeap

/-!
# FR-Dijkstra on the machine: the triplets of a half block

The bipartite Monge heap of a half block (`PlanarFlow.Monge.FR.MHInv`) is kept as its
*triplets*: intervals of rows not extracted with one owner each. A triplet is recorded at its
first row `x` (its *start*), in the record of the row `x` at `Q + 8 x` (`Q` the base of the
structure of the half block, `s = 2 ^ T` rows):

* the start flag `tPr` (`+0`, `1` for a start), the owner `tOwn` (`+1`), the last row `tEnd`
  (`+2`), the row of the least entry `tMin` (`+5`), and the least entry `tKey` (real memory,
  `+0`); the neighbouring starts are found by searches in the tournament of the first starts.

Over the rows, a complete binary tree (node `v` with `1 ≤ v < 2 s`, the leaf `s + x` for the
row `x`) holds two tournaments of winners (`PlanarFlow.Monge.FR.WinOK`) over the starts:

* `tWn v` (at `Q + 8 s + 2 v`): a start below `v` with the least entry (the heap over the
  triplets; the item of the half block is at the root);
* `tWl v` (at `Q + 8 s + 2 v + 1`): the first start below `v` (the key is the row itself), used
  to search the triplets by their owners.

The routines take the base `Q` in `r208` and `Q + 8 s` in `r209` (`TCtx`).

* `twWin_exec`, `twLm_exec`: recompute a node of the two tournaments, within `23` steps each;
* `tUp_exec`: recompute the path from a node to the root (`tUpCost i = 49 lg i + 2` steps), which
  restores both tournaments after a change of the records of one row
  (`PlanarFlow.Monge.FR.WinOK.set`);
* `tBnd_exec`: the first start whose owner is before a given source `a` (`s` if none), by one
  descent of the tournament of the first starts, within `18 T + 20` steps, when the owners of the
  starts are antitone in the rows (`StartAnti`; the owners of a bipartite Monge heap are,
  `PlanarFlow.Monge.FR.OwnOK.anti`). This is where the rows that a new source beats are
  (`PlanarFlow.Monge.FR.own_order_left`, `own_order_right`): next to this start.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

/-! ### The records -/

/-- The start flag of the row `x`. -/
def tPr (Q : ℕ) (nm : ℕ → ℕ) (x : ℕ) : ℕ := nm (Q + 8 * x)
/-- The least entry of the triplet starting at `x`. -/
def tKey (Q : ℕ) (rm : ℕ → ℝ) (x : ℕ) : ℝ := rm (Q + 8 * x)
/-- The owner of the triplet starting at `x`. -/
def tOwn (Q : ℕ) (nm : ℕ → ℕ) (x : ℕ) : ℕ := nm (Q + 8 * x + 1)
/-- The last row of the triplet starting at `x`. -/
def tEnd (Q : ℕ) (nm : ℕ → ℕ) (x : ℕ) : ℕ := nm (Q + 8 * x + 2)
/-- The row of the least entry of the triplet starting at `x`. -/
def tMin (Q : ℕ) (nm : ℕ → ℕ) (x : ℕ) : ℕ := nm (Q + 8 * x + 5)
/-- The winner of the heap over the triplets at the node `i`. -/
def tWn (Q s : ℕ) (nm : ℕ → ℕ) (i : ℕ) : ℕ := nm (Q + 8 * s + 2 * i)
/-- The first start below the node `i` (when there is one). -/
def tWl (Q s : ℕ) (nm : ℕ → ℕ) (i : ℕ) : ℕ := nm (Q + 8 * s + 2 * i + 1)

/-- The registers of the structure of the current half block. -/
structure TCtx (Q s : ℕ) (c : Config) : Prop where
  r208 : c.nreg 208 = Q
  r209 : c.nreg 209 = Q + 8 * s

theorem TCtx.of {Q s : ℕ} {c c' : Config} (h : TCtx Q s c)
    (hr : ∀ r, 208 ≤ r → r < 210 → c'.nreg r = c.nreg r) : TCtx Q s c' :=
  ⟨(hr 208 (by omega) (by omega)).trans h.r208, (hr 209 (by omega) (by omega)).trans h.r209⟩

/-! ### The programs -/

/-- **Recompute the winner** of the heap over the triplets at the node `r210`. -/
def twWin : Stmt :=
  .seq (block [.mulN 211 210 116, .addN 211 211 209, .loadN 213 211, .addN 211 211 111,
    .loadN 214 211, .mulN 215 213 118, .addN 215 215 208, .loadN 216 215, .mulN 217 214 118,
    .addN 217 217 208, .loadN 218 217]) <|
  .seq (.ifLtN 216 110 (.instr (.copyN 219 214))
    (.ifLtN 218 110 (.instr (.copyN 219 213))
      (.seq (block [.loadR 210 215, .loadR 211 217])
        (.ifLtR 210 211 (.instr (.copyN 219 213)) (.instr (.copyN 219 214)))))) <|
  block [.mulN 212 210 111, .addN 212 212 209, .storeN 212 219]

/-- **Recompute the first start** below the node `r210`. -/
def twLm : Stmt :=
  .seq (block [.mulN 211 210 116, .addN 211 211 209, .addN 211 211 110, .loadN 213 211,
    .addN 211 211 111, .loadN 214 211, .mulN 215 213 118, .addN 215 215 208, .loadN 216 215,
    .mulN 217 214 118, .addN 217 217 208, .loadN 218 217]) <|
  .seq (.ifLtN 216 110 (.instr (.copyN 219 214))
    (.ifLtN 218 110 (.instr (.copyN 219 213))
      (.ifLtN 213 214 (.instr (.copyN 219 213)) (.instr (.copyN 219 214))))) <|
  block [.mulN 212 210 111, .addN 212 212 209, .addN 212 212 110, .storeN 212 219]

/-- One step of the search at the internal node `r223`: the first start `b` below the right
child; to the right child if `b` is a start with an owner not before `a = r221`, to the left
child otherwise (with the candidate `r222 := b` when `b` is a start). -/
def tbBody : Stmt :=
  .seq (block [.mulN 224 223 116, .addN 224 224 209, .addN 224 224 111, .addN 224 224 110,
    .loadN 225 224, .mulN 226 225 118, .addN 226 226 208, .loadN 227 226, .addN 226 226 110,
    .loadN 228 226, .mulN 223 223 111]) <|
  .ifLtN 227 110 .skip
    (.ifLtN 228 221 (.instr (.copyN 222 225)) (.instr (.addN 223 223 110)))

/-- **The first start with an owner before `a = r221`** (in `r222`; `s` if there is none). -/
def tBnd : Stmt :=
  .seq (block [.copyN 223 110, .copyN 222 121]) <|
  .seq (.whileLtN 223 121 tbBody) <|
  .seq (block [.subN 224 223 121, .mulN 226 224 118, .addN 226 226 208, .loadN 227 226,
    .addN 226 226 110, .loadN 228 226]) <|
  .ifLtN 227 110 .skip (.ifLtN 228 221 (.instr (.copyN 222 224)) .skip)

/-- **Recompute a node** of the two tournaments. -/
def tFix : Stmt := .seq twWin twLm

/-- **Recompute the nodes from `r210` up to the root.** -/
def tUp : Stmt := .whileLtN 117 210 (.seq tFix (.instr (.divN 210 210 111)))

/-- **Make the row `r230` a start**: owner `r231`, last row `r232`, row of the least entry
`r233`, least entry the real `r230`; then recompute the tournaments. -/
def tSet : Stmt :=
  .seq (block [.mulN 234 230 118, .addN 234 234 208, .storeN 234 110, .storeR 234 230,
    .addN 234 234 110, .storeN 234 231, .addN 234 234 110, .storeN 234 232,
    .addN 234 234 111, .addN 234 234 110, .storeN 234 233, .addN 210 121 230,
    .divN 210 210 111]) tUp

/-- **The row `r230` is no longer a start**; then recompute the tournaments. -/
def tClr : Stmt :=
  .seq (block [.mulN 234 230 118, .addN 234 234 208, .storeN 234 117, .addN 210 121 230,
    .divN 210 210 111]) tUp

variable {P : Prm} {I : Input}

/-! ### Recomputing a node -/

theorem twWin_exec {Q s : ℕ} (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hT : TCtx Q s c) (hQ : Q + 16 * s ≤ P.W) (hi1 : 1 ≤ c.nreg 210) (hi2 : c.nreg 210 < s)
    (hWa : tWn Q s c.nmem (2 * c.nreg 210) < s) (hWb : tWn Q s c.nmem (2 * c.nreg 210 + 1) < s)
    (hpr : ∀ x < s, tPr Q c.nmem x ≤ 1) :
    ∃ c' k', Exec I P.W twWin c c' k' ∧ k' ≤ 23 ∧
      c'.nmem = upd c.nmem (Q + 8 * s + 2 * c.nreg 210)
          (better (tPr Q c.nmem) (tKey Q c.rmem) (tWn Q s c.nmem (2 * c.nreg 210))
            (tWn Q s c.nmem (2 * c.nreg 210 + 1))) ∧
        c'.rmem = c.rmem ∧ (∀ r, (r < 211 ∨ 220 ≤ r) → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 210 → r ≠ 211 → c'.rreg r = c.rreg r) ∧ c'.output = c.output := by
  have g110 := hG.r110
  have g111 := hG.r111
  have g116 := hG.r116
  have g118 := hG.r118
  have g208 := hT.r208
  have g209 := hT.r209
  generalize hi : c.nreg 210 = i at hi1 hi2 hWa hWb
  generalize ha : tWn Q s c.nmem (2 * i) = a at hWa
  generalize hb : tWn Q s c.nmem (2 * i + 1) = bb at hWb
  have ea : c.nmem (c.nreg 210 * c.nreg 116 + c.nreg 209) = a := by
    rw [hi, g116, g209, ← ha]; unfold tWn; congr 1; ring
  have eb : c.nmem (c.nreg 210 * c.nreg 116 + c.nreg 209 + c.nreg 111) = bb := by
    rw [hi, g116, g209, g111, ← hb]; unfold tWn; congr 1; ring
  have hpa := hpr a hWa
  have hpb := hpr bb hWb
  have fin : ∀ (w : ℕ) (c' : Config), WordsBounded P.W c' → c'.nreg 219 = w →
      w = better (tPr Q c.nmem) (tKey Q c.rmem) a bb →
      (∀ r, (r < 211 ∨ 220 ≤ r) → c'.nreg r = c.nreg r) →
      (∀ r, r ≠ 210 → r ≠ 211 → c'.rreg r = c.rreg r) → c'.nmem = c.nmem →
      c'.rmem = c.rmem → c'.output = c.output →
      ∃ c'' k', Exec I P.W (block [.mulN 212 210 111, .addN 212 212 209, .storeN 212 219]) c'
        c'' k' ∧ k' = 3 ∧
        c''.nmem = upd c.nmem (Q + 8 * s + 2 * i) (better (tPr Q c.nmem) (tKey Q c.rmem) a bb) ∧
        c''.rmem = c.rmem ∧ (∀ r, (r < 211 ∨ 220 ≤ r) → c''.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 210 → r ≠ 211 → c''.rreg r = c.rreg r) ∧ c''.output = c.output := by
    intro w c' hw' h219 hwb hK hR hN hM hO
    have h209 : c'.nreg 209 = Q + 8 * s := (hK 209 (by omega)).trans g209
    have h210 : c'.nreg 210 = i := (hK 210 (by omega)).trans hi
    have h111 : c'.nreg 111 = 2 := (hK 111 (by omega)).trans g111
    exec_block
    · rw [h210, h111]; omega
    · config_simp; rw [h210, h111, h209]; omega
    refine ⟨rfl, ?_, by config_simp; exact hM, fun r hr => ?_, hR, hO⟩
    · config_simp; rw [h210, h111, h209, h219, hN, hwb]
      congr 1; ring
    · config_simp; rw [upd_other _ _ _ (by omega)]; exact hK r hr
  unfold twWin
  refine spec_seq ?_
  exec_block
  · rw [hi, g116]; omega
  · config_simp; rw [hi, g116, g209]; omega
  · config_simp; rw [hi, g116, g209, g111]; omega
  · config_simp; rw [ea, g118]; omega
  · config_simp; rw [ea, g118, g208]; omega
  · config_simp; rw [eb, g118]; omega
  · config_simp; rw [eb, g118, g208]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f213 : c₁.nreg 213 = a := by rw [← hc₁]; config_simp; exact ea
  have f214 : c₁.nreg 214 = bb := by rw [← hc₁]; config_simp; exact eb
  have f215 : c₁.nreg 215 = Q + 8 * a := by rw [← hc₁]; config_simp; rw [ea, g118, g208]; ring
  have f217 : c₁.nreg 217 = Q + 8 * bb := by
    rw [← hc₁]; config_simp; rw [eb, g118, g208]; ring
  have f216 : c₁.nreg 216 = tPr Q c.nmem a := by
    rw [← hc₁]; config_simp; rw [ea, g118, g208]; unfold tPr; congr 1; ring
  have f218 : c₁.nreg 218 = tPr Q c.nmem bb := by
    rw [← hc₁]; config_simp; rw [eb, g118, g208]; unfold tPr; congr 1; ring
  have fK : ∀ r, (r < 211 ∨ 220 ≤ r) → c₁.nreg r = c.nreg r := fun r hr => by
    rw [← hc₁]; config_simp; upd_tac
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fR : c₁.rreg = c.rreg := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have k110 : c₁.nreg 110 = 1 := (fK 110 (by omega)).trans g110
  have kc : ∀ x y : ℕ, ∀ c' : Config, c' = { c₁ with nreg := upd c₁.nreg 219 y } →
      ∀ r, (r < 211 ∨ 220 ≤ r) → c'.nreg r = c.nreg r := fun x y c' e r hr => by
    subst e; config_simp; rw [upd_other _ _ _ (by omega)]; exact fK r hr
  refine spec_seq ?_
  by_cases hA : tPr Q c.nmem a < 1
  · refine spec_ifLtN_true (by rw [f216, k110]; exact hA) ?_
    refine spec_instr (Exec.copyN hw₁ 219 214) fun hw₂ => ?_
    obtain ⟨c'', k', e', hk', post⟩ := fin bb _ hw₂ (by config_simp; exact f214)
      (by rw [better_eq_right (by omega)]) (kc 0 _ _ rfl)
      (fun r _ _ => by config_simp; rw [fR]) (by config_simp; exact fN) (by config_simp; exact fM)
      (by config_simp; exact fO)
    exact ⟨c'', k', e', by omega, post⟩
  refine spec_ifLtN_false (by rw [f216, k110]; exact hA) ?_
  by_cases hB : tPr Q c.nmem bb < 1
  · refine spec_ifLtN_true (by rw [f218, k110]; exact hB) ?_
    refine spec_instr (Exec.copyN hw₁ 219 213) fun hw₂ => ?_
    obtain ⟨c'', k', e', hk', post⟩ := fin a _ hw₂ (by config_simp; exact f213)
      (by rw [better_eq_left ⟨by omega, Or.inl (by omega)⟩]) (kc 0 _ _ rfl)
      (fun r _ _ => by config_simp; rw [fR]) (by config_simp; exact fN) (by config_simp; exact fM)
      (by config_simp; exact fO)
    exact ⟨c'', k', e', by omega, post⟩
  refine spec_ifLtN_false (by rw [f218, k110]; exact hB) ?_
  refine spec_seq ?_
  exec_block
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
  have hw₂ : WordsBounded P.W c₂ := hc₂ ▸ ‹_›
  have r210 : c₂.rreg 210 = tKey Q c.rmem a := by
    rw [← hc₂]; config_simp; rw [f215, fM]; rfl
  have r211 : c₂.rreg 211 = tKey Q c.rmem bb := by
    rw [← hc₂]; config_simp; rw [f217, fM]; rfl
  have c2n : c₂.nreg = c₁.nreg := by rw [← hc₂]
  have c2r : ∀ r, r ≠ 210 → r ≠ 211 → c₂.rreg r = c.rreg r := fun r h1 h2 => by
    rw [← hc₂]; config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rw [fR]
  have c2N : c₂.nmem = c.nmem := by rw [← hc₂]; exact fN
  have c2M : c₂.rmem = c.rmem := by rw [← hc₂]; exact fM
  have c2O : c₂.output = c.output := by rw [← hc₂]; exact fO
  have hpa1 : tPr Q c.nmem a = 1 := by omega
  have hpb1 : tPr Q c.nmem bb = 1 := by omega
  have kc2 : ∀ y : ℕ, ∀ r, (r < 211 ∨ 220 ≤ r) →
      ({ c₂ with nreg := upd c₂.nreg 219 y } : Config).nreg r = c.nreg r := fun y r hr => by
    config_simp; rw [upd_other _ _ _ (by omega), c2n]; exact fK r hr
  by_cases hC : tKey Q c.rmem a < tKey Q c.rmem bb
  · refine spec_ifLtR_true (by rw [r210, r211]; exact hC) ?_
    refine spec_instr (Exec.copyN hw₂ 219 213) fun hw₃ => ?_
    obtain ⟨c'', k', e', hk', post⟩ := fin a _ hw₃ (by config_simp; rw [c2n]; exact f213)
      (by rw [better_eq_left ⟨hpa1, Or.inr hC⟩]) (kc2 _)
      (fun r h1 h2 => by config_simp; exact c2r r h1 h2) (by config_simp; exact c2N)
      (by config_simp; exact c2M) (by config_simp; exact c2O)
    exact ⟨c'', k', e', by omega, post⟩
  · refine spec_ifLtR_false (by rw [r210, r211]; exact hC) ?_
    refine spec_instr (Exec.copyN hw₂ 219 214) fun hw₃ => ?_
    obtain ⟨c'', k', e', hk', post⟩ := fin bb _ hw₃ (by config_simp; rw [c2n]; exact f214)
      (by rw [better_eq_right (fun h => h.2.elim (fun h' => h' hpb1) hC)]) (kc2 _)
      (fun r h1 h2 => by config_simp; exact c2r r h1 h2) (by config_simp; exact c2N)
      (by config_simp; exact c2M) (by config_simp; exact c2O)
    exact ⟨c'', k', e', by omega, post⟩

theorem twLm_exec {Q s : ℕ} (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hT : TCtx Q s c) (hQ : Q + 16 * s ≤ P.W) (hi1 : 1 ≤ c.nreg 210) (hi2 : c.nreg 210 < s)
    (hWa : tWl Q s c.nmem (2 * c.nreg 210) < s) (hWb : tWl Q s c.nmem (2 * c.nreg 210 + 1) < s)
    (hpr : ∀ x < s, tPr Q c.nmem x ≤ 1) :
    ∃ c' k', Exec I P.W twLm c c' k' ∧ k' ≤ 23 ∧
      c'.nmem = upd c.nmem (Q + 8 * s + 2 * c.nreg 210 + 1)
          (better (tPr Q c.nmem) (fun x => (x : ℝ)) (tWl Q s c.nmem (2 * c.nreg 210))
            (tWl Q s c.nmem (2 * c.nreg 210 + 1))) ∧
        c'.rmem = c.rmem ∧ (∀ r, (r < 211 ∨ 220 ≤ r) → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.output = c.output := by
  have g110 := hG.r110
  have g111 := hG.r111
  have g116 := hG.r116
  have g118 := hG.r118
  have g208 := hT.r208
  have g209 := hT.r209
  generalize hi : c.nreg 210 = i at hi1 hi2 hWa hWb
  generalize ha : tWl Q s c.nmem (2 * i) = a at hWa
  generalize hb : tWl Q s c.nmem (2 * i + 1) = bb at hWb
  have ea : c.nmem (c.nreg 210 * c.nreg 116 + c.nreg 209 + c.nreg 110) = a := by
    rw [hi, g116, g209, g110, ← ha]; unfold tWl; congr 1; ring
  have eb : c.nmem (c.nreg 210 * c.nreg 116 + c.nreg 209 + c.nreg 110 + c.nreg 111) = bb := by
    rw [hi, g116, g209, g110, g111, ← hb]; unfold tWl; congr 1; ring
  have hpa := hpr a hWa
  have hpb := hpr bb hWb
  have fin : ∀ (w : ℕ) (c' : Config), WordsBounded P.W c' → c'.nreg 219 = w →
      w = better (tPr Q c.nmem) (fun x => (x : ℝ)) a bb →
      (∀ r, (r < 211 ∨ 220 ≤ r) → c'.nreg r = c.nreg r) →
      c'.rreg = c.rreg → c'.nmem = c.nmem →
      c'.rmem = c.rmem → c'.output = c.output →
      ∃ c'' k', Exec I P.W (block [.mulN 212 210 111, .addN 212 212 209, .addN 212 212 110,
        .storeN 212 219]) c' c'' k' ∧ k' = 4 ∧
        c''.nmem = upd c.nmem (Q + 8 * s + 2 * i + 1)
          (better (tPr Q c.nmem) (fun x => (x : ℝ)) a bb) ∧
        c''.rmem = c.rmem ∧ (∀ r, (r < 211 ∨ 220 ≤ r) → c''.nreg r = c.nreg r) ∧
        c''.rreg = c.rreg ∧ c''.output = c.output := by
    intro w c' hw' h219 hwb hK hR hN hM hO
    have h209 : c'.nreg 209 = Q + 8 * s := (hK 209 (by omega)).trans g209
    have h210 : c'.nreg 210 = i := (hK 210 (by omega)).trans hi
    have h111 : c'.nreg 111 = 2 := (hK 111 (by omega)).trans g111
    have h110 : c'.nreg 110 = 1 := (hK 110 (by omega)).trans g110
    exec_block
    · rw [h210, h111]; omega
    · config_simp; rw [h210, h111, h209]; omega
    · config_simp; rw [h210, h111, h209, h110]; omega
    refine ⟨rfl, ?_, by config_simp; exact hM, fun r hr => ?_, hR, hO⟩
    · config_simp; rw [h210, h111, h209, h110, h219, hN, hwb]
      congr 1; ring
    · config_simp; rw [upd_other _ _ _ (by omega)]; exact hK r hr
  unfold twLm
  refine spec_seq ?_
  exec_block
  · rw [hi, g116]; omega
  · config_simp; rw [hi, g116, g209]; omega
  · config_simp; rw [hi, g116, g209, g110]; omega
  · config_simp; rw [hi, g116, g209, g110, g111]; omega
  · config_simp; rw [ea, g118]; omega
  · config_simp; rw [ea, g118, g208]; omega
  · config_simp; rw [eb, g118]; omega
  · config_simp; rw [eb, g118, g208]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f213 : c₁.nreg 213 = a := by rw [← hc₁]; config_simp; exact ea
  have f214 : c₁.nreg 214 = bb := by rw [← hc₁]; config_simp; exact eb
  have f215 : c₁.nreg 215 = Q + 8 * a := by rw [← hc₁]; config_simp; rw [ea, g118, g208]; ring
  have f217 : c₁.nreg 217 = Q + 8 * bb := by
    rw [← hc₁]; config_simp; rw [eb, g118, g208]; ring
  have f216 : c₁.nreg 216 = tPr Q c.nmem a := by
    rw [← hc₁]; config_simp; rw [ea, g118, g208]; unfold tPr; congr 1; ring
  have f218 : c₁.nreg 218 = tPr Q c.nmem bb := by
    rw [← hc₁]; config_simp; rw [eb, g118, g208]; unfold tPr; congr 1; ring
  have fK : ∀ r, (r < 211 ∨ 220 ≤ r) → c₁.nreg r = c.nreg r := fun r hr => by
    rw [← hc₁]; config_simp; upd_tac
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fR : c₁.rreg = c.rreg := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have k110 : c₁.nreg 110 = 1 := (fK 110 (by omega)).trans g110
  have kc : ∀ x y : ℕ, ∀ c' : Config, c' = { c₁ with nreg := upd c₁.nreg 219 y } →
      ∀ r, (r < 211 ∨ 220 ≤ r) → c'.nreg r = c.nreg r := fun x y c' e r hr => by
    subst e; config_simp; rw [upd_other _ _ _ (by omega)]; exact fK r hr
  refine spec_seq ?_
  by_cases hA : tPr Q c.nmem a < 1
  · refine spec_ifLtN_true (by rw [f216, k110]; exact hA) ?_
    refine spec_instr (Exec.copyN hw₁ 219 214) fun hw₂ => ?_
    obtain ⟨c'', k', e', hk', post⟩ := fin bb _ hw₂ (by config_simp; exact f214)
      (by rw [better_eq_right (by omega)]) (kc 0 _ _ rfl)
      (by config_simp; exact fR) (by config_simp; exact fN) (by config_simp; exact fM)
      (by config_simp; exact fO)
    exact ⟨c'', k', e', by omega, post⟩
  refine spec_ifLtN_false (by rw [f216, k110]; exact hA) ?_
  by_cases hB : tPr Q c.nmem bb < 1
  · refine spec_ifLtN_true (by rw [f218, k110]; exact hB) ?_
    refine spec_instr (Exec.copyN hw₁ 219 213) fun hw₂ => ?_
    obtain ⟨c'', k', e', hk', post⟩ := fin a _ hw₂ (by config_simp; exact f213)
      (by rw [better_eq_left ⟨by omega, Or.inl (by omega)⟩]) (kc 0 _ _ rfl)
      (by config_simp; exact fR) (by config_simp; exact fN) (by config_simp; exact fM)
      (by config_simp; exact fO)
    exact ⟨c'', k', e', by omega, post⟩
  refine spec_ifLtN_false (by rw [f218, k110]; exact hB) ?_
  have hpa1 : tPr Q c.nmem a = 1 := by omega
  have hpb1 : tPr Q c.nmem bb = 1 := by omega
  by_cases hC : a < bb
  · refine spec_ifLtN_true (by rw [f213, f214]; exact hC) ?_
    refine spec_instr (Exec.copyN hw₁ 219 213) fun hw₂ => ?_
    obtain ⟨c'', k', e', hk', post⟩ := fin a _ hw₂ (by config_simp; exact f213)
      (by rw [better_eq_left ⟨hpa1, Or.inr (by exact_mod_cast hC)⟩]) (kc 0 _ _ rfl)
      (by config_simp; exact fR) (by config_simp; exact fN) (by config_simp; exact fM)
      (by config_simp; exact fO)
    exact ⟨c'', k', e', by omega, post⟩
  · refine spec_ifLtN_false (by rw [f213, f214]; exact hC) ?_
    refine spec_instr (Exec.copyN hw₁ 219 214) fun hw₂ => ?_
    obtain ⟨c'', k', e', hk', post⟩ := fin bb _ hw₂ (by config_simp; exact f214)
      (by rw [better_eq_right (fun h => h.2.elim (fun h' => h' hpb1)
        (fun h' => hC (by exact_mod_cast h')))]) (kc 0 _ _ rfl)
      (by config_simp; exact fR) (by config_simp; exact fN) (by config_simp; exact fM)
      (by config_simp; exact fO)
    exact ⟨c'', k', e', by omega, post⟩

/-! ### Recomputing a path -/

lemma tWn_upd {Q s J w : ℕ} (nm : ℕ → ℕ) :
    tWn Q s (upd nm (Q + 8 * s + 2 * J) w) = Function.update (tWn Q s nm) J w := by
  funext i; unfold tWn
  by_cases h : i = J
  · subst h; rw [upd_same, Function.update_self]
  · rw [upd_other _ _ _ (by omega), Function.update_of_ne h]

lemma tWl_upd {Q s J w : ℕ} (nm : ℕ → ℕ) :
    tWl Q s (upd nm (Q + 8 * s + 2 * J + 1) w) = Function.update (tWl Q s nm) J w := by
  funext i; unfold tWl
  by_cases h : i = J
  · subst h; rw [upd_same, Function.update_self]
  · rw [upd_other _ _ _ (by omega), Function.update_of_ne h]

lemma tWl_upd_even {Q s J w : ℕ} (nm : ℕ → ℕ) :
    tWl Q s (upd nm (Q + 8 * s + 2 * J) w) = tWl Q s nm := by
  funext i; unfold tWl; rw [upd_other _ _ _ (by omega)]

lemma tPr_congr {Q s : ℕ} {nm nm' : ℕ → ℕ} (h : ∀ a, a < Q + 8 * s → nm' a = nm a) {x : ℕ}
    (hx : x < s) : tPr Q nm' x = tPr Q nm x := h _ (by omega)

/-- The state of `tUp`. -/
structure IUp (P : Prm) (Q s : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded P.W c
  glob : Glob P c
  tctx : TCtx Q s c
  keepN : ∀ r, (r < 210 ∨ 220 ≤ r) → c.nreg r = c₀.nreg r
  keepR : ∀ r, r ≠ 210 → r ≠ 211 → c.rreg r = c₀.rreg r
  out : c.output = c₀.output
  nm : ∀ a, (a < Q + 8 * s ∨ Q + 12 * s ≤ a) → c.nmem a = c₀.nmem a
  rm : c.rmem = c₀.rmem
  lt : c.nreg 210 < s
  win : WinOK s (tPr Q c₀.nmem) (tKey Q c₀.rmem) (tWn Q s c.nmem) (c.nreg 210)
  wl : WinOK s (tPr Q c₀.nmem) (fun x => (x : ℝ)) (tWl Q s c.nmem) (c.nreg 210)

theorem tUpBody_exec {Q s : ℕ} {c₀ : Config} (hQ : Q + 16 * s ≤ P.W)
    (hpr : ∀ x < s, tPr Q c₀.nmem x ≤ 1) (c : Config) (hI : IUp P Q s c₀ c)
    (hlt : c.nreg 117 < c.nreg 210) :
    ∃ c' k', Exec I P.W (.seq tFix (.instr (.divN 210 210 111))) c c' k' ∧ IUp P Q s c₀ c' ∧
      lg (c'.nreg 210) * 49 + k' + 2 ≤ lg (c.nreg 210) * 49 := by
  have hc := hI.wb
  have hG := hI.glob
  rw [hG.r117] at hlt
  have hlt' := hI.lt
  have hn : ∀ a, a < Q + 8 * s → c.nmem a = c₀.nmem a := fun a ha => hI.nm a (Or.inl ha)
  have hpr' : ∀ x < s, tPr Q c.nmem x ≤ 1 := fun x hx => by
    rw [tPr_congr hn hx]; exact hpr x hx
  generalize hJ : c.nreg 210 = J at hlt hlt'
  have hW := hI.win; rw [hJ] at hW
  have hL' := hI.wl; rw [hJ] at hL'
  unfold tFix
  refine spec_seq ?_
  refine spec_seq ?_
  refine spec_use (twWin_exec (I := I) c hc hG hI.tctx hQ (by omega) (by omega)
    (by rw [hJ]; exact (hW.under _ (by omega) (by omega)).1)
    (by rw [hJ]; exact (hW.under _ (by omega) (by omega)).1) hpr') ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hN₁, hM₁, hK₁, hR₁, hO₁⟩
  rw [hJ] at hN₁
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => hK₁ r (by omega)
  have hT₁ : TCtx Q s c₁ := hI.tctx.of fun r h1 h2 => hK₁ r (by omega)
  have e210 : c₁.nreg 210 = J := (hK₁ 210 (by omega)).trans hJ
  have hpr₁ : ∀ x < s, tPr Q c₁.nmem x ≤ 1 := fun x hx => by
    rw [tPr_congr (nm := c.nmem) (fun a ha => by rw [hN₁, upd_other _ _ _ (by omega)]) hx]
    exact hpr' x hx
  have hwl₁ : tWl Q s c₁.nmem = tWl Q s c.nmem := by rw [hN₁, tWl_upd_even]
  refine spec_use (twLm_exec (I := I) c₁ hw₁ hG₁ hT₁ hQ (by omega) (by omega)
    (by rw [e210, hwl₁]; exact (hL'.under _ (by omega) (by omega)).1)
    (by rw [e210, hwl₁]; exact (hL'.under _ (by omega) (by omega)).1) hpr₁) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hN₂, hM₂, hK₂, hR₂, hO₂⟩
  rw [e210, hwl₁] at hN₂
  refine spec_instr (Exec.divN hw₂ 210 210 111) fun hw₃ => ?_
  have g210 : c₂.nreg 210 = J := (hK₂ 210 (by omega)).trans e210
  have g111 : c₂.nreg 111 = 2 := (hK₂ 111 (by omega)).trans hG₁.r111
  have kN : ∀ r, (r < 211 ∨ 220 ≤ r) → c₂.nreg r = c.nreg r := fun r hr =>
    (hK₂ r hr).trans (hK₁ r hr)
  have hkey : tKey Q c.rmem = tKey Q c₀.rmem := by funext x; unfold tKey; rw [hI.rm]
  have hprc : ∀ x < s, tPr Q c.nmem x = tPr Q c₀.nmem x := fun x hx => tPr_congr hn hx
  have a1 : Glob P { c₂ with nreg := upd c₂.nreg 210 (c₂.nreg 210 / c₂.nreg 111) } :=
    hG.of fun r h1 h2 => by config_simp; rw [upd_other _ _ _ (by omega)]; exact kN r (by omega)
  have a2 : TCtx Q s { c₂ with nreg := upd c₂.nreg 210 (c₂.nreg 210 / c₂.nreg 111) } :=
    hI.tctx.of fun r h1 h2 => by
      config_simp; rw [upd_other _ _ _ (by omega)]; exact kN r (by omega)
  have a3 : ∀ r, (r < 210 ∨ 220 ≤ r) →
      upd c₂.nreg 210 (c₂.nreg 210 / c₂.nreg 111) r = c₀.nreg r := fun r hr => by
    rw [upd_other _ _ _ (by omega), kN r (by omega)]; exact hI.keepN r hr
  have a4 : ∀ a, (a < Q + 8 * s ∨ Q + 12 * s ≤ a) → c₂.nmem a = c₀.nmem a := fun a ha => by
    rw [hN₂, upd_other _ _ _ (by omega), hN₁, upd_other _ _ _ (by omega)]
    exact hI.nm a ha
  refine ⟨⟨hw₃, a1, a2, fun r hr => by config_simp; exact a3 r hr,
    fun r h1 h2 => by config_simp; rw [hR₂, hR₁ r h1 h2]; exact hI.keepR r h1 h2,
    by config_simp; rw [hO₂, hO₁, hI.out], fun a ha => by config_simp; exact a4 a ha,
    by config_simp; rw [hM₂, hM₁, hI.rm], by config_simp; rw [g210, g111]; omega, ?_, ?_⟩, ?_⟩
  · config_simp; rw [g210, g111]
    have hst := hW.step (by omega) hlt'
    refine hst.congr_wn fun i h1 h2 => ?_
    rw [hN₂]
    have : tWn Q s (upd (upd c.nmem (Q + 8 * s + 2 * J) (better (tPr Q c.nmem) (tKey Q c.rmem)
        (tWn Q s c.nmem (2 * J)) (tWn Q s c.nmem (2 * J + 1)))) (Q + 8 * s + 2 * J + 1)
        (better (tPr Q c₁.nmem) (fun x => (x : ℝ)) (tWl Q s c.nmem (2 * J))
          (tWl Q s c.nmem (2 * J + 1)))) i = Function.update (tWn Q s c.nmem) J
        (better (tPr Q c.nmem) (tKey Q c.rmem) (tWn Q s c.nmem (2 * J))
          (tWn Q s c.nmem (2 * J + 1))) i := by
      rw [← tWn_upd]; unfold tWn; rw [upd_other _ _ _ (by omega)]
    rw [hN₁] at this ⊢
    rw [this]
    by_cases hie : i = J
    · subst hie; rw [Function.update_self, Function.update_self, hkey]
      exact better_congr (hprc _ (hW.under _ (by omega) (by omega)).1)
        (hprc _ (hW.under _ (by omega) (by omega)).1) rfl rfl
    · rw [Function.update_of_ne hie, Function.update_of_ne hie]
  · config_simp; rw [g210, g111]
    have hst := hL'.step (by omega) hlt'
    refine hst.congr_wn fun i h1 h2 => ?_
    rw [hN₂, tWl_upd]
    by_cases hie : i = J
    · subst hie; rw [Function.update_self, Function.update_self]
      exact better_congr (by
          rw [tPr_congr (nm := c.nmem) (fun a ha => by rw [hN₁, upd_other _ _ _ (by omega)])
            (hL'.under _ (by omega) (by omega)).1]
          exact hprc _ (hL'.under _ (by omega) (by omega)).1)
        (by
          rw [tPr_congr (nm := c.nmem) (fun a ha => by rw [hN₁, upd_other _ _ _ (by omega)])
            (hL'.under _ (by omega) (by omega)).1]
          exact hprc _ (hL'.under _ (by omega) (by omega)).1) rfl rfl
    · rw [Function.update_of_ne hie, Function.update_of_ne hie, hwl₁]
  · config_simp; rw [g210, g111]
    rw [lg_pos (show 1 ≤ J by omega)]
    omega

/-- The cost of recomputing the path from the node `i`. -/
def tUpCost (i : ℕ) : ℕ := lg i * 49 + 2

/-- **Recomputing the two tournaments from the node `r210` up to the root**, after a change
of the records below it. -/
theorem tUp_exec {Q s : ℕ} (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hT : TCtx Q s c) (hQ : Q + 16 * s ≤ P.W) (hlt : c.nreg 210 < s)
    (hpr : ∀ x < s, tPr Q c.nmem x ≤ 1)
    (hW : WinOK s (tPr Q c.nmem) (tKey Q c.rmem) (tWn Q s c.nmem) (c.nreg 210))
    (hWl : WinOK s (tPr Q c.nmem) (fun x => (x : ℝ)) (tWl Q s c.nmem) (c.nreg 210)) :
    ∃ c' k', Exec I P.W tUp c c' k' ∧ k' ≤ tUpCost (c.nreg 210) ∧
      WinOK s (tPr Q c.nmem) (tKey Q c.rmem) (tWn Q s c'.nmem) 0 ∧
      WinOK s (tPr Q c.nmem) (fun x => (x : ℝ)) (tWl Q s c'.nmem) 0 ∧
      (∀ r, (r < 210 ∨ 220 ≤ r) → c'.nreg r = c.nreg r) ∧
      (∀ r, r ≠ 210 → r ≠ 211 → c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < Q + 8 * s ∨ Q + 12 * s ≤ a) → c'.nmem a = c.nmem a) ∧ c'.rmem = c.rmem := by
  obtain ⟨c', k', e, hI, hn, hk⟩ := Exec.whileLtN_potential (P := I) (W := P.W) (a := 117)
    (b := 210) (body := .seq tFix (.instr (.divN 210 210 111))) (IUp P Q s c)
    (fun c => lg (c.nreg 210) * 49) (fun _ h => h.wb)
    (fun c' hI hlt => tUpBody_exec hQ hpr c' hI hlt)
    ⟨hc, hG, hT, fun _ _ => rfl, fun _ _ _ => rfl, rfl, fun _ _ => rfl, rfl, hlt, hW, hWl⟩
  have h0 : c'.nreg 210 = 0 := by rw [hI.glob.r117] at hn; omega
  have h1 := hI.win; rw [h0] at h1
  have h2 := hI.wl; rw [h0] at h2
  exact ⟨c', k', e, hk, h1, h2, hI.keepN, hI.keepR, hI.out, hI.nm, hI.rm⟩

/-! ### The first triplet with an owner before a source -/

/-- **A node holds a present leaf below it of least key**, when there is one. -/
theorem win_node {n : ℕ} {pr : ℕ → ℕ} {key : ℕ → ℝ} {wn : ℕ → ℕ} (h : WinOK n pr key wn 0) :
    ∀ l, 1 ≤ l → l < 2 * n → ∀ x < n, Anc l (n + x) → pr x = 1 →
      pr (wn l) = 1 ∧ key (wn l) ≤ key x := by
  intro l
  induction hm : 2 * n - l using Nat.strong_induction_on generalizing l with
  | _ m ih =>
    intro hl1 hl2 x hx ha hpx
    rcases Nat.lt_or_ge l n with hln | hln
    · have hne : l ≠ n + x := by omega
      have hW := h.eq l hl1 hln (not_anc_zero hl1)
      have i0 := fun hA => ih (2 * n - 2 * l) (by omega) (2 * l) rfl (by omega) (by omega) x hx
        hA hpx
      have i1 := fun hA => ih (2 * n - (2 * l + 1)) (by omega) (2 * l + 1) rfl (by omega)
        (by omega) x hx hA hpx
      by_cases hc : pr (wn (2 * l)) = 1 ∧
          (pr (wn (2 * l + 1)) ≠ 1 ∨ key (wn (2 * l)) < key (wn (2 * l + 1)))
      · rw [hW, better_eq_left hc]
        rcases anc_child ha hne with hA | hA
        · exact i0 hA
        · obtain ⟨a1, a2⟩ := i1 hA
          rcases hc.2 with hc2 | hc2
          · exact absurd a1 hc2
          · exact ⟨hc.1, hc2.le.trans a2⟩
      · rw [hW, better_eq_right hc]
        rcases anc_child ha hne with hA | hA
        · obtain ⟨a1, a2⟩ := i0 hA
          have : pr (wn (2 * l + 1)) = 1 ∧ key (wn (2 * l + 1)) ≤ key (wn (2 * l)) := by
            by_contra hc'
            apply hc
            refine ⟨a1, ?_⟩
            by_cases hp : pr (wn (2 * l + 1)) = 1
            · exact Or.inr (not_le.1 fun hle => hc' ⟨hp, hle⟩)
            · exact Or.inl hp
          exact ⟨this.1, this.2.trans a2⟩
        · exact i1 hA
    · obtain ⟨k, hk⟩ := ha
      rcases k with _ | k
      · simp at hk
        rw [← hk, h.leaf x hx]; exact ⟨hpx, le_rfl⟩
      · exfalso
        have : (n + x) / 2 ^ (k + 1) ≤ (n + x) / 2 := Nat.div_le_div_left
          (by have := Nat.one_le_two_pow (n := k); rw [pow_succ]; omega) (by norm_num)
        omega

/-- An ancestor of a leaf at a known height is the node of the leaf at this height. -/
lemma anc_nd {T j v y : ℕ} (hy : y < 2 ^ T) (hv : Valid (2 ^ T) j v) (h : Anc v (2 ^ T + y)) :
    nd (2 ^ T) j y = v := by
  obtain ⟨k, hk⟩ := h
  have hv1 := hv.1
  have hkT : k ≤ T := by
    by_contra hc
    have : 2 ^ (T + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 ^ T + y) / 2 ^ k = 0 := Nat.div_eq_of_lt (by rw [pow_succ] at this; omega)
    omega
  have hk' : nd (2 ^ T) k y = v := hk
  have hvk : Valid (2 ^ T) k v := hk' ▸ valid_nd Nat.one_le_two_pow (Nat.pow_dvd_pow 2 hkT) hy
  rw [← valid_unique hvk hv]; exact hk'

/-- A start with an owner before `a`. -/
def Bd (Q s a : ℕ) (nm : ℕ → ℕ) (y : ℕ) : Prop := y < s ∧ tPr Q nm y = 1 ∧ tOwn Q nm y < a

/-- **The invariant of the search** at the node `v` of height `j`, with the candidate `cd`. -/
structure BdInv (Q s a : ℕ) (nm : ℕ → ℕ) (j v cd : ℕ) : Prop where
  cand : cd = s ∨ Bd Q s a nm cd
  out : ∀ y, Bd Q s a nm y → nd s j y ≠ v → cd ≤ y
  inn : ∀ y, Bd Q s a nm y → nd s j y = v → y < cd

/-- The owners of the starts are antitone in the rows. -/
def StartAnti (Q s : ℕ) (nm : ℕ → ℕ) : Prop :=
  ∀ y z, y < z → z < s → tPr Q nm y = 1 → tPr Q nm z = 1 → tOwn Q nm z ≤ tOwn Q nm y

section bnd

variable {Q T a : ℕ} {nm : ℕ → ℕ}

lemma bdInv_root : BdInv Q (2 ^ T) a nm T 1 (2 ^ T) :=
  ⟨Or.inl rfl, fun _ hy hn => absurd (nd_root hy.1) hn, fun _ hy _ => hy.1⟩

/-- One step of the search, at the node `v` of height `j + 1`, with `b` the first start below
the right child. -/
theorem bdInv_step (hW : WinOK (2 ^ T) (tPr Q nm) (fun x => (x : ℝ)) (tWl Q (2 ^ T) nm) 0)
    (hA : StartAnti Q (2 ^ T) nm) {j v cd : ℕ} (hv : Valid (2 ^ T) (j + 1) v)
    (h : BdInv Q (2 ^ T) a nm (j + 1) v cd) :
    let b := tWl Q (2 ^ T) nm (2 * v + 1)
    (tPr Q nm b = 1 → ¬ tOwn Q nm b < a → BdInv Q (2 ^ T) a nm j (2 * v + 1) cd) ∧
    (tPr Q nm b = 1 → tOwn Q nm b < a → BdInv Q (2 ^ T) a nm j (2 * v) b) ∧
    (tPr Q nm b ≠ 1 → BdInv Q (2 ^ T) a nm j (2 * v) cd) := by
  intro b
  obtain ⟨hv0, hv1⟩ := valid_child hv
  have hvs := valid_lt hv
  have hbu := hW.under (2 * v + 1) (by omega) (by omega)
  have hb_lt : b < 2 ^ T := hbu.1
  have hb_nd : nd (2 ^ T) j b = 2 * v + 1 := anc_nd hb_lt hv1 hbu.2
  -- the first start below the right child
  have hfirst : ∀ y, y < 2 ^ T → nd (2 ^ T) j y = 2 * v + 1 → tPr Q nm y = 1 →
      tPr Q nm b = 1 ∧ b ≤ y := fun y hy hn hp => by
    have := win_node hW (2 * v + 1) (by omega) (by omega) y hy
      ⟨j, by rw [← hn]; rfl⟩ hp
    exact ⟨this.1, by exact_mod_cast this.2⟩
  have hup : ∀ y, nd (2 ^ T) (j + 1) y = v ↔ nd (2 ^ T) j y = 2 * v ∨
      nd (2 ^ T) j y = 2 * v + 1 := fun y => nd_child
  refine ⟨fun hpb hnb => ⟨h.cand, fun y hy hn => ?_, fun y hy hn => ?_⟩,
    fun hpb hb => ⟨Or.inr ⟨hb_lt, hpb, hb⟩, fun y hy hn => ?_, fun y hy hn => ?_⟩,
    fun hpb => ⟨h.cand, fun y hy hn => ?_, fun y hy hn => ?_⟩⟩
  · -- to the right: no start of the left child has an owner before `a`
    by_cases hyv : nd (2 ^ T) (j + 1) y = v
    · rcases (hup y).1 hyv with e | e
      · exfalso
        have hyb := nd_order e hb_nd
        have := hA y b hyb hb_lt hy.2.1 hpb
        exact hnb (lt_of_le_of_lt this hy.2.2)
      · exact absurd e hn
    · exact h.out y hy hyv
  · exact h.inn y hy ((hup y).2 (Or.inr hn))
  · -- to the left with the candidate `b`
    by_cases hyv : nd (2 ^ T) (j + 1) y = v
    · rcases (hup y).1 hyv with e | e
      · exact absurd e hn
      · exact (hfirst y hy.1 e hy.2.1).2
    · have h1 := h.out y hy hyv
      have h2 := h.inn b ⟨hb_lt, hpb, hb⟩ ((hup b).2 (Or.inr hb_nd))
      omega
  · exact nd_order hn hb_nd
  · -- to the left, the right child has no start
    by_cases hyv : nd (2 ^ T) (j + 1) y = v
    · rcases (hup y).1 hyv with e | e
      · exact absurd e hn
      · exact absurd (hfirst y hy.1 e hy.2.1).1 hpb
    · exact h.out y hy hyv
  · exact h.inn y hy ((hup y).2 (Or.inl hn))

/-- **The end of the search** at the leaf of the row `x`: the answer is `x` if it is a start
with an owner before `a`, the candidate otherwise. -/
theorem bdInv_leaf {x cd : ℕ} (hx : x < 2 ^ T)
    (h : BdInv Q (2 ^ T) a nm 0 (2 ^ T + x) cd) :
    let r := if tPr Q nm x = 1 ∧ tOwn Q nm x < a then x else cd
    (r = 2 ^ T ∨ Bd Q (2 ^ T) a nm r) ∧ ∀ y, Bd Q (2 ^ T) a nm y → r ≤ y := by
  intro r
  have hnd : ∀ y, nd (2 ^ T) 0 y = 2 ^ T + x ↔ y = x := fun y => by rw [nd_zero]; omega
  by_cases hb : tPr Q nm x = 1 ∧ tOwn Q nm x < a
  · have e : r = x := iteT hb
    rw [e]
    refine ⟨Or.inr ⟨hx, hb⟩, fun y hy => ?_⟩
    by_cases hyx : y = x
    · omega
    · have h1 := h.out y hy (fun hn => hyx ((hnd y).1 hn))
      have h2 := h.inn x ⟨hx, hb⟩ ((hnd x).2 rfl)
      omega
  · have e : r = cd := iteF hb
    rw [e]
    refine ⟨h.cand, fun y hy => h.out y hy fun hn => hb ?_⟩
    rw [(hnd y).1 hn] at hy; exact hy.2

end bnd

/-- The state of the search. -/
structure IBd (P : Prm) (Q s a : ℕ) (c₀ : Config) (j : ℕ) (c : Config) : Prop where
  wb : WordsBounded P.W c
  keepN : ∀ r, (r < 222 ∨ 229 ≤ r) → c.nreg r = c₀.nreg r
  rr : c.rreg = c₀.rreg
  nm : c.nmem = c₀.nmem
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
  valid : Valid s j (c.nreg 223)
  inv : BdInv Q s a c₀.nmem j (c.nreg 223) (c.nreg 222)

theorem tbBody_exec {Q T a : ℕ} {c₀ : Config} (hG : Glob P c₀) (hT : TCtx Q (2 ^ T) c₀)
    (hQ : Q + 16 * 2 ^ T ≤ P.W) (h121 : c₀.nreg 121 = 2 ^ T) (h221 : c₀.nreg 221 = a)
    (hpr : ∀ x < 2 ^ T, tPr Q c₀.nmem x ≤ 1) (hA : StartAnti Q (2 ^ T) c₀.nmem)
    (hW : WinOK (2 ^ T) (tPr Q c₀.nmem) (fun x => (x : ℝ)) (tWl Q (2 ^ T) c₀.nmem) 0)
    {j : ℕ} (c : Config) (hI : IBd P Q (2 ^ T) a c₀ j c) (hlt : c.nreg 223 < c.nreg 121) :
    ∃ c' k', Exec I P.W tbBody c c' k' ∧ IBd P Q (2 ^ T) a c₀ (j - 1) c' ∧ 1 ≤ j ∧
      k' ≤ 16 := by
  have hc := hI.wb
  have g : ∀ r, (r < 222 ∨ 229 ≤ r) → c.nreg r = c₀.nreg r := hI.keepN
  have g110 : c.nreg 110 = 1 := (g 110 (by omega)).trans hG.r110
  have g111 : c.nreg 111 = 2 := (g 111 (by omega)).trans hG.r111
  have g116 : c.nreg 116 = 4 := (g 116 (by omega)).trans hG.r116
  have g118 : c.nreg 118 = 8 := (g 118 (by omega)).trans hG.r118
  have g208 : c.nreg 208 = Q := (g 208 (by omega)).trans hT.r208
  have g209 : c.nreg 209 = Q + 8 * 2 ^ T := (g 209 (by omega)).trans hT.r209
  have g221 : c.nreg 221 = a := (g 221 (by omega)).trans h221
  rw [(g 121 (by omega)).trans h121] at hlt
  have hv := hI.valid
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := (valid_lt_iff hv).1 hlt; omega⟩
  generalize hvv : c.nreg 223 = v at hv hlt
  have hbu := hW.under (2 * v + 1) (by have := valid_lt hv; omega) (by omega)
  generalize hb : tWl Q (2 ^ T) c₀.nmem (2 * v + 1) = b at hbu
  have hstep := bdInv_step hW hA hv (hvv ▸ hI.inv)
  rw [hb] at hstep
  obtain ⟨st1, st2, st3⟩ := hstep
  have eb : c.nmem (c.nreg 223 * c.nreg 116 + c.nreg 209 + c.nreg 111 + c.nreg 110) = b := by
    rw [hvv, g116, g209, g111, g110, hI.nm, ← hb]; unfold tWl; congr 1; ring
  have epb : c.nmem (b * c.nreg 118 + c.nreg 208) = tPr Q c₀.nmem b := by
    rw [g118, g208, hI.nm]; unfold tPr; congr 1; ring
  have eob : c.nmem (b * c.nreg 118 + c.nreg 208 + c.nreg 110) = tOwn Q c₀.nmem b := by
    rw [g118, g208, g110, hI.nm]; unfold tOwn; congr 1; ring
  unfold tbBody
  refine spec_seq ?_
  exec_block
  · rw [hvv, g116]; omega
  · config_simp; rw [hvv, g116, g209]; omega
  · config_simp; rw [hvv, g116, g209, g111]; omega
  · config_simp; rw [hvv, g116, g209, g111, g110]; omega
  · config_simp; rw [eb, g118]; omega
  · config_simp; rw [eb, g118, g208]; omega
  · config_simp; rw [eb, g118, g208, g110]; omega
  · config_simp; rw [hvv, g111]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f223 : c₁.nreg 223 = 2 * v := by rw [← hc₁]; config_simp; rw [hvv, g111]; ring
  have f225 : c₁.nreg 225 = b := by rw [← hc₁]; config_simp; exact eb
  have f227 : c₁.nreg 227 = tPr Q c₀.nmem b := by rw [← hc₁]; config_simp; rw [eb, epb]
  have f228 : c₁.nreg 228 = tOwn Q c₀.nmem b := by rw [← hc₁]; config_simp; rw [eb, eob]
  have fK : ∀ r, (r < 222 ∨ 229 ≤ r) → c₁.nreg r = c₀.nreg r := fun r hr => by
    rw [← hc₁]; config_simp; rw [← g r hr]; upd_tac
  have f222 : c₁.nreg 222 = c.nreg 222 := by rw [← hc₁]; config_simp
  have fR : c₁.rreg = c₀.rreg := by rw [← hc₁, ← hI.rr]
  have fN : c₁.nmem = c₀.nmem := by rw [← hc₁, ← hI.nm]
  have fM : c₁.rmem = c₀.rmem := by rw [← hc₁, ← hI.rm]
  have fO : c₁.output = c₀.output := by rw [← hc₁, ← hI.out]
  have k110 : c₁.nreg 110 = 1 := (fK 110 (by omega)).trans hG.r110
  have k221 : c₁.nreg 221 = a := (fK 221 (by omega)).trans h221
  obtain ⟨hv0, hv1⟩ := valid_child hv
  by_cases hp : tPr Q c₀.nmem b < 1
  · refine spec_ifLtN_true (by rw [f227, k110]; exact hp) ?_
    refine spec_skip hw₁ ⟨⟨hw₁, fK, fR, fN, fM, fO, by rw [f223]; exact hv0, ?_⟩, by omega,
      by omega⟩
    rw [f223, f222, ← hvv]
    exact hvv ▸ st3 (by omega)
  · refine spec_ifLtN_false (by rw [f227, k110]; exact hp) ?_
    have hpb : tPr Q c₀.nmem b = 1 := by have := hpr b hbu.1; omega
    by_cases ho : tOwn Q c₀.nmem b < a
    · refine spec_ifLtN_true (by rw [f228, k221]; exact ho) ?_
      refine spec_instr (Exec.copyN hw₁ 222 225) fun hw₂ => ?_
      refine ⟨⟨hw₂, fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]; exact fK r hr,
        by config_simp; exact fR, by config_simp; exact fN, by config_simp; exact fM,
        by config_simp; exact fO, by config_simp; rw [f223]; exact hv0, ?_⟩, by omega, by omega⟩
      config_simp; rw [f223, f225]
      exact st2 hpb ho
    · refine spec_ifLtN_false (by rw [f228, k221]; exact ho) ?_
      refine spec_instr (Exec.addN hw₁ 223 223 110 (by rw [f223, k110]; omega)) fun hw₂ => ?_
      refine ⟨⟨hw₂, fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]; exact fK r hr,
        by config_simp; exact fR, by config_simp; exact fN, by config_simp; exact fM,
        by config_simp; exact fO, by config_simp; rw [f223, k110]; exact hv1, ?_⟩, by omega,
        by omega⟩
      config_simp; rw [f223, k110, f222, ← hvv]
      exact hvv ▸ st1 hpb ho

/-- The cost of the search in a half block with `2 ^ T` rows. -/
def tBndCost (T : ℕ) : ℕ := 18 * T + 20

/-- **The first triplet with an owner before `a`**: with the tournament of the first starts
correct and the owners of the starts antitone in the rows, `tBnd` leaves in `r222` the first
start whose owner is before `a = r221`, or `s` if there is none. -/
theorem tBnd_exec {Q T a : ℕ} (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hT : TCtx Q (2 ^ T) c) (hQ : Q + 16 * 2 ^ T ≤ P.W) (h121 : c.nreg 121 = 2 ^ T)
    (h221 : c.nreg 221 = a) (hpr : ∀ x < 2 ^ T, tPr Q c.nmem x ≤ 1)
    (hA : StartAnti Q (2 ^ T) c.nmem)
    (hW : WinOK (2 ^ T) (tPr Q c.nmem) (fun x => (x : ℝ)) (tWl Q (2 ^ T) c.nmem) 0) :
    ∃ c' k', Exec I P.W tBnd c c' k' ∧ k' ≤ tBndCost T ∧
      (c'.nreg 222 = 2 ^ T ∨ Bd Q (2 ^ T) a c.nmem (c'.nreg 222)) ∧
      (∀ y, Bd Q (2 ^ T) a c.nmem y → c'.nreg 222 ≤ y) ∧
      (∀ r, (r < 222 ∨ 229 ≤ r) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hs : 1 ≤ 2 ^ T := Nat.one_le_two_pow
  unfold tBnd
  refine spec_seq ?_
  exec_block
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have hI₁ : IBd P Q (2 ^ T) a c₁ T c₁ :=
    ⟨hw₁, fun _ _ => rfl, rfl, rfl, rfl, rfl, by
      rw [← hc₁]; config_simp; rw [hG.r110]; exact valid_root T, by
      rw [← hc₁]; config_simp; rw [hG.r110, h121]; exact bdInv_root⟩
  have e₁ : ∀ r, (r < 222 ∨ 229 ≤ r) → c₁.nreg r = c.nreg r := fun r hr => by
    rw [← hc₁]; config_simp; upd_tac
  have hN₁ : c₁.nmem = c.nmem := by rw [← hc₁]
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => e₁ r (by omega)
  have hT₁ : TCtx Q (2 ^ T) c₁ := hT.of fun r h1 h2 => e₁ r (by omega)
  obtain ⟨j, c₂, k₂, ex₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_ghost (P := I) (W := P.W) (a := 223)
    (b := 121) (body := tbBody) (fun j c => IBd P Q (2 ^ T) a c₁ j c) (fun j _ => 18 * j)
    (fun _ _ h => h.wb)
    (fun j c hI hlt => by
      obtain ⟨c', k', e, hI', hj, hk⟩ := tbBody_exec (I := I) hG₁ hT₁ hQ
        (by rw [e₁ 121 (by omega), h121]) (by rw [e₁ 221 (by omega), h221])
        (by rw [hN₁]; exact hpr) (by rw [hN₁]; exact hA) (by rw [hN₁]; exact hW) c hI hlt
      exact ⟨j - 1, c', k', e, hI', by omega⟩) hI₁
  refine spec_seq ⟨c₂, k₂, ex₂, ?_⟩
  have k121 : c₂.nreg 121 = 2 ^ T := by rw [hI₂.keepN 121 (by omega), e₁ 121 (by omega), h121]
  rw [k121] at hn₂
  have hj0 : j = 0 := by
    by_contra h; exact hn₂ ((valid_lt_iff hI₂.valid).2 (by omega))
  subst hj0
  obtain ⟨-, hv2, hv3⟩ := valid_zero.1 hI₂.valid
  obtain ⟨x, hx⟩ : ∃ x, c₂.nreg 223 = 2 ^ T + x := ⟨c₂.nreg 223 - 2 ^ T, by omega⟩
  have hxs : x < 2 ^ T := by omega
  have hleaf := bdInv_leaf hxs (hx ▸ hI₂.inv)
  rw [hN₁] at hleaf
  have hc₂ := hI₂.wb
  have g : ∀ r, (r < 222 ∨ 229 ≤ r) → c₂.nreg r = c.nreg r := fun r hr =>
    (hI₂.keepN r hr).trans (e₁ r hr)
  have g110 : c₂.nreg 110 = 1 := (g 110 (by omega)).trans hG.r110
  have g118 : c₂.nreg 118 = 8 := (g 118 (by omega)).trans hG.r118
  have g208 : c₂.nreg 208 = Q := (g 208 (by omega)).trans hT.r208
  have g221 : c₂.nreg 221 = a := (g 221 (by omega)).trans h221
  have hN₂ : c₂.nmem = c.nmem := hI₂.nm.trans hN₁
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hx, k121, g118]; omega
  · config_simp; rw [hx, k121, g118, g208]; omega
  · config_simp; rw [hx, k121, g118, g208, g110]; omega
  generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃
  have hw₃ : WordsBounded P.W c₃ := hc₃ ▸ ‹_›
  have f224 : c₃.nreg 224 = x := by rw [← hc₃]; config_simp; rw [hx, k121]; omega
  have f227 : c₃.nreg 227 = tPr Q c.nmem x := by
    rw [← hc₃]; config_simp; rw [hx, k121, g118, g208, hN₂]; unfold tPr; congr 1; omega
  have f228 : c₃.nreg 228 = tOwn Q c.nmem x := by
    rw [← hc₃]; config_simp; rw [hx, k121, g118, g208, g110, hN₂]; unfold tOwn; congr 1; omega
  have fK : ∀ r, (r < 222 ∨ 229 ≤ r) → c₃.nreg r = c.nreg r := fun r hr => by
    rw [← hc₃]; config_simp; rw [← g r hr]; upd_tac
  have f222 : c₃.nreg 222 = c₂.nreg 222 := by rw [← hc₃]; config_simp
  have fR : c₃.rreg = c.rreg := by rw [← hc₃]; config_simp; rw [hI₂.rr, ← hc₁]
  have fN : c₃.nmem = c.nmem := by rw [← hc₃]; config_simp; exact hN₂
  have fM : c₃.rmem = c.rmem := by rw [← hc₃]; config_simp; rw [hI₂.rm, ← hc₁]
  have fO : c₃.output = c.output := by rw [← hc₃]; config_simp; rw [hI₂.out, ← hc₁]
  have k110 : c₃.nreg 110 = 1 := (fK 110 (by omega)).trans hG.r110
  have k221 : c₃.nreg 221 = a := (fK 221 (by omega)).trans h221
  have hcost : ∀ k, k ≤ 5 → 0 + 1 + 1 + (k₂ + (0 + 1 + 1 + 1 + 1 + 1 + 1 + k)) ≤ tBndCost T :=
    fun k hk => by unfold tBndCost; omega
  by_cases hp : tPr Q c.nmem x < 1
  · refine spec_ifLtN_true (by rw [f227, k110]; exact hp) ?_
    have e : (if tPr Q c.nmem x = 1 ∧ tOwn Q c.nmem x < a then x else c₂.nreg 222) =
        c₂.nreg 222 := iteF (by omega)
    rw [e] at hleaf
    refine spec_skip hw₃ ⟨hcost _ (by omega), ?_, ?_, fK, fR, fN, fM, fO⟩
    · rw [f222]; exact hleaf.1
    · rw [f222]; exact hleaf.2
  · refine spec_ifLtN_false (by rw [f227, k110]; exact hp) ?_
    have hpx : tPr Q c.nmem x = 1 := by have := hpr x hxs; omega
    by_cases ho : tOwn Q c.nmem x < a
    · refine spec_ifLtN_true (by rw [f228, k221]; exact ho) ?_
      refine spec_instr (Exec.copyN hw₃ 222 224) fun hw₄ => ?_
      have e : (if tPr Q c.nmem x = 1 ∧ tOwn Q c.nmem x < a then x else c₂.nreg 222) = x :=
        iteT ⟨hpx, ho⟩
      rw [e] at hleaf
      refine ⟨hcost _ (by omega), ?_, ?_, fun r hr => ?_, by config_simp; exact fR,
        by config_simp; exact fN, by config_simp; exact fM, by config_simp; exact fO⟩
      · config_simp; rw [f224]; exact hleaf.1
      · config_simp; rw [f224]; exact hleaf.2
      · config_simp; rw [upd_other _ _ _ (by omega)]; exact fK r hr
    · refine spec_ifLtN_false (by rw [f228, k221]; exact ho) ?_
      have e : (if tPr Q c.nmem x = 1 ∧ tOwn Q c.nmem x < a then x else c₂.nreg 222) =
          c₂.nreg 222 := iteF (fun h => ho h.2)
      rw [e] at hleaf
      refine spec_skip hw₃ ⟨hcost _ (by omega), ?_, ?_, fK, fR, fN, fM, fO⟩
      · rw [f222]; exact hleaf.1
      · rw [f222]; exact hleaf.2

/-! ### The representation of a bipartite Monge heap -/

/-- **The memory at `Q` holds the triplets of an owner map** `own` (rows `< nr`, `s` the number
of leaves of the tree, entries `e σ + F ρ σ`), except the extracted rows `X` and the rows of the
*hole* `H` (rows not extracted, not recorded yet): the triplets
(the starts, `tPr = 1`) are disjoint intervals `[x, tEnd x]` with the owner `tOwn x`, covering
exactly the other rows; each records a least entry of its interval (`tMin`, `tKey`), and both
tournaments are correct. -/
structure TMem (s nr : ℕ) (F : ℕ → ℕ → ℝ) (e : ℕ → ℝ) (own : ℕ → ℕ) (X : ℕ → Prop)
    (H : ℕ → Prop) (Q : ℕ) (nm : ℕ → ℕ) (rm : ℕ → ℝ) : Prop where
  nr_le : nr ≤ s
  pr01 : ∀ x < s, tPr Q nm x ≤ 1
  st : ∀ x < s, tPr Q nm x = 1 → x ≤ tEnd Q nm x ∧ tEnd Q nm x < nr
  cover : ∀ ρ < nr, (¬ X ρ ∧ ¬ H ρ ↔ ∃ x < s, tPr Q nm x = 1 ∧ x ≤ ρ ∧ ρ ≤ tEnd Q nm x)
  hole : ∀ ρ, H ρ → ρ < nr ∧ ¬ X ρ
  disj : ∀ x y, x < y → y < s → tPr Q nm x = 1 → tPr Q nm y = 1 → tEnd Q nm x < y
  own : ∀ x < s, tPr Q nm x = 1 → ∀ ρ, x ≤ ρ → ρ ≤ tEnd Q nm x → own ρ = tOwn Q nm x
  mn : ∀ x < s, tPr Q nm x = 1 → x ≤ tMin Q nm x ∧ tMin Q nm x ≤ tEnd Q nm x ∧
    tKey Q rm x = e (tOwn Q nm x) + F (tMin Q nm x) (tOwn Q nm x) ∧
    ∀ ρ, x ≤ ρ → ρ ≤ tEnd Q nm x → F (tMin Q nm x) (tOwn Q nm x) ≤ F ρ (tOwn Q nm x)
  win : WinOK s (tPr Q nm) (tKey Q rm) (tWn Q s nm) 0
  wl : WinOK s (tPr Q nm) (fun x => (x : ℝ)) (tWl Q s nm) 0

/-- **The memory at `Q` represents the bipartite Monge heap** of a half block (rows `< nr`,
`s` the number of leaves of its tree, sources `< nc`, entries `e σ + F ρ σ`, active sources
`Act`, owner map `own`, extracted rows `X`, popped key `κ`, `PlanarFlow.Monge.FR.MHInv`): the
triplets of `own` cover exactly the rows not extracted (`TMem` without a hole). -/
structure TRep (s nr nc : ℕ) (F : ℕ → ℕ → ℝ) (e : ℕ → ℝ) (Act : ℕ → Prop) (own : ℕ → ℕ)
    (X : ℕ → Prop) (κ : ℝ) (Q : ℕ) (nm : ℕ → ℕ) (rm : ℕ → ℝ) : Prop where
  heap : MHInv nr nc (fun ρ σ => e σ + F ρ σ) Act own X κ
  mem : TMem s nr F e own X (fun _ => False) Q nm rm

section rep

variable {s nr nc : ℕ} {F : ℕ → ℕ → ℝ} {e : ℕ → ℝ} {Act : ℕ → Prop} {own : ℕ → ℕ}
  {X : ℕ → Prop} {κ : ℝ} {Q : ℕ} {nm : ℕ → ℕ} {rm : ℕ → ℝ}

/-- Without a hole, the triplets cover exactly the rows not extracted. -/
lemma TMem.cover0 {H : ℕ → Prop} (h : TMem s nr F e own X H Q nm rm) (hH : ∀ ρ, ¬ H ρ)
    {ρ : ℕ} (hρ : ρ < nr) : ¬ X ρ ↔ ∃ x < s, tPr Q nm x = 1 ∧ x ≤ ρ ∧ ρ ≤ tEnd Q nm x := by
  rw [← h.cover ρ hρ]; constructor
  · intro h'; exact ⟨h', hH ρ⟩
  · exact fun h' => h'.1

/-- **The owners of the starts are antitone** (for the search `tBnd`), when they are the owners
of an owner map. -/
theorem TMem.anti {H : ℕ → Prop} (h : TMem s nr F e own X H Q nm rm)
    (ha : ∀ ρ ρ', ρ ≤ ρ' → ρ' < nr → own ρ' ≤ own ρ) : StartAnti Q s nm := by
  intro y z hyz hz hy hz'
  have hy' := h.st y (by omega) hy
  have hz'' := h.st z hz hz'
  rw [← h.own y (by omega) hy y le_rfl hy'.1, ← h.own z hz hz' z le_rfl hz''.1]
  exact ha y z hyz.le (by omega)

theorem TRep.anti (h : TRep s nr nc F e Act own X κ Q nm rm) : StartAnti Q s nm :=
  h.mem.anti h.heap.ok.anti

/-- **The item of the half block**: the least entry `tKey w` of the winner `w` at the root is
an entry at a row not extracted, and it is at most every entry from an active source to a row
not extracted (`PlanarFlow.Monge.FR.MHInv.lower`). -/
theorem TRep.item (h : TRep s nr nc F e Act own X κ Q nm rm) (hs : 1 ≤ s) {x : ℕ} (hx : x < s)
    (hpx : tPr Q nm x = 1) :
    let w := tWn Q s nm 1
    w < s ∧ tPr Q nm w = 1 ∧ ¬ X (tMin Q nm w) ∧ tMin Q nm w < nr ∧
      own (tMin Q nm w) = tOwn Q nm w ∧
      tKey Q rm w = e (tOwn Q nm w) + F (tMin Q nm w) (tOwn Q nm w) ∧
      ∀ ρ < nr, ¬ X ρ → ∀ σ, Act σ → tKey Q rm w ≤ e σ + F ρ σ := by
  intro w
  have hm := h.mem
  obtain ⟨hw, hmin⟩ := win_root hm.win hs
  obtain ⟨hpw, -⟩ := hmin x hx hpx
  obtain ⟨m1, m2, m3, -⟩ := hm.mn w hw hpw
  have hst := hm.st w hw hpw
  refine ⟨hw, hpw, (hm.cover0 (fun _ h => h) (by omega)).2 ⟨w, hw, hpw, m1, m2⟩, by omega,
    hm.own w hw hpw _ m1 m2, m3, fun ρ hρ hX σ hσ => ?_⟩
  refine h.heap.lower (m := tKey Q rm w) (fun ρ' hρ' hX' => ?_) hρ hX hσ
  obtain ⟨y, hy, hpy, hy1, hy2⟩ := (hm.cover0 (fun _ h => h) hρ').1 hX'
  obtain ⟨-, hle⟩ := hmin y hy hpy
  obtain ⟨n1, n2, n3, n4⟩ := hm.mn y hy hpy
  rw [hm.own y hy hpy ρ' hy1 hy2]
  refine hle.trans ?_
  rw [n3]
  have := n4 ρ' hy1 hy2
  linarith

end rep

/-! ### Writing a start -/

/-- After a change of the record of the row `x` only, the tournaments are correct except at the
ancestors of the parent of the leaf of `x`. -/
lemma winOK_rec {Q s x : ℕ} {nm nm' : ℕ → ℕ} {rm rm' : ℕ → ℝ}
    (hW : WinOK s (tPr Q nm) (tKey Q rm) (tWn Q s nm) 0)
    (hWl : WinOK s (tPr Q nm) (fun x => (x : ℝ)) (tWl Q s nm) 0)
    (hn : ∀ a, a ≠ Q + 8 * x → a ≠ Q + 8 * x + 1 → a ≠ Q + 8 * x + 2 →
      a ≠ Q + 8 * x + 5 → nm' a = nm a)
    (hr : ∀ a, a ≠ Q + 8 * x → rm' a = rm a) (hx : x < s) :
    WinOK s (tPr Q nm') (tKey Q rm') (tWn Q s nm') ((s + x) / 2) ∧
      WinOK s (tPr Q nm') (fun x => (x : ℝ)) (tWl Q s nm') ((s + x) / 2) := by
  have hwn : tWn Q s nm' = tWn Q s nm := by
    funext i; unfold tWn
    exact hn _ (by omega) (by omega) (by omega) (by omega)
  have hwl : tWl Q s nm' = tWl Q s nm := by
    funext i; unfold tWl
    exact hn _ (by omega) (by omega) (by omega) (by omega)
  have hp : ∀ y, y ≠ x → tPr Q nm' y = tPr Q nm y := fun y hy => by
    unfold tPr; exact hn _ (by omega) (by omega) (by omega) (by omega)
  have hk : ∀ y, y ≠ x → tKey Q rm' y = tKey Q rm y := fun y hy => by
    unfold tKey; exact hr _ (by omega)
  rw [hwn, hwl]
  exact ⟨hW.set hp hk, hWl.set hp fun _ _ => rfl⟩

lemma lg_lt_pow {T i : ℕ} (h : i < 2 ^ T) : lg i ≤ T := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [lg_zero]; omega
  · rw [lg_eq_log hi]
    have := Nat.log_lt_of_lt_pow (b := 2) (by omega) h
    omega

/-- **Making a row a start**, with its record, and recomputing the tournaments. -/
theorem tSet_exec {Q T x : ℕ} (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hT : TCtx Q (2 ^ T) c) (hQ : Q + 16 * 2 ^ T ≤ P.W) (h121 : c.nreg 121 = 2 ^ T)
    (h230 : c.nreg 230 = x) (hx : x < 2 ^ T) (hpr : ∀ y < 2 ^ T, tPr Q c.nmem y ≤ 1)
    (hW : WinOK (2 ^ T) (tPr Q c.nmem) (tKey Q c.rmem) (tWn Q (2 ^ T) c.nmem) 0)
    (hWl : WinOK (2 ^ T) (tPr Q c.nmem) (fun x => (x : ℝ)) (tWl Q (2 ^ T) c.nmem) 0) :
    ∃ c' k', Exec I P.W tSet c c' k' ∧ k' ≤ 49 * T + 15 ∧
      (∀ y < 2 ^ T, tPr Q c'.nmem y = if y = x then 1 else tPr Q c.nmem y) ∧
      tOwn Q c'.nmem x = c.nreg 231 ∧ tEnd Q c'.nmem x = c.nreg 232 ∧
      tMin Q c'.nmem x = c.nreg 233 ∧ c'.rmem = upd c.rmem (Q + 8 * x) (c.rreg 230) ∧
      (∀ a, a < Q + 8 * 2 ^ T → a ≠ Q + 8 * x → a ≠ Q + 8 * x + 1 → a ≠ Q + 8 * x + 2 →
        a ≠ Q + 8 * x + 5 → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < Q ∨ Q + 12 * 2 ^ T ≤ a) → c'.nmem a = c.nmem a) ∧
      WinOK (2 ^ T) (tPr Q c'.nmem) (tKey Q c'.rmem) (tWn Q (2 ^ T) c'.nmem) 0 ∧
      WinOK (2 ^ T) (tPr Q c'.nmem) (fun x => (x : ℝ)) (tWl Q (2 ^ T) c'.nmem) 0 ∧
      (∀ r, (r < 210 ∨ (220 ≤ r ∧ r ≠ 234)) → c'.nreg r = c.nreg r) ∧
      (∀ r, r ≠ 210 → r ≠ 211 → c'.rreg r = c.rreg r) ∧ c'.output = c.output := by
  have g110 := hG.r110
  have g111 := hG.r111
  have g118 := hG.r118
  have g208 := hT.r208
  unfold tSet
  refine spec_seq ?_
  exec_block
  · rw [h230, g118]; omega
  · config_simp; rw [h230, g118, g208]; omega
  · config_simp; rw [h230, g118, g208, g110]; omega
  · config_simp; rw [h230, g118, g208, g110]; omega
  · config_simp; rw [h230, g118, g208, g110, g111]; omega
  · config_simp; rw [h230, g118, g208, g110, g111]; omega
  · config_simp; rw [h121, h230]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have e8 : x * 8 + Q = Q + 8 * x := by ring
  have hN₁ : c₁.nmem = upd (upd (upd (upd c.nmem (Q + 8 * x) 1) (Q + 8 * x + 1) (c.nreg 231))
      (Q + 8 * x + 2) (c.nreg 232)) (Q + 8 * x + 5) (c.nreg 233) := by
    rw [← hc₁]; config_simp; rw [h230, g118, g208, g110, g111, e8]
  have hM₁ : c₁.rmem = upd c.rmem (Q + 8 * x) (c.rreg 230) := by
    rw [← hc₁]; config_simp; rw [h230, g118, g208, e8]
  have hK₁ : ∀ r, (r < 210 ∨ (220 ≤ r ∧ r ≠ 234)) → c₁.nreg r = c.nreg r := fun r hr => by
    rw [← hc₁]; config_simp; upd_tac
  have h210 : c₁.nreg 210 = (2 ^ T + x) / 2 := by
    rw [← hc₁]; config_simp; rw [h121, h230, g111]
  have hR₁ : c₁.rreg = c.rreg := by rw [← hc₁]
  have hO₁ : c₁.output = c.output := by rw [← hc₁]
  have hn : ∀ a, a ≠ Q + 8 * x → a ≠ Q + 8 * x + 1 → a ≠ Q + 8 * x + 2 →
      a ≠ Q + 8 * x + 5 → c₁.nmem a = c.nmem a := fun a h1 h2 h3 h4 => by
    rw [hN₁]; simp only [upd_apply]; split_ifs <;> first | rfl | omega
  obtain ⟨hW₁, hWl₁⟩ := winOK_rec (rm' := c₁.rmem) hW hWl hn
    (fun a ha => by rw [hM₁, upd_other _ _ _ ha]) hx
  have hpr₁ : ∀ y < 2 ^ T, tPr Q c₁.nmem y = if y = x then 1 else tPr Q c.nmem y := fun y hy => by
    unfold tPr; rw [hN₁]; simp only [upd_apply]; split_ifs <;> first | rfl | omega
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => hK₁ r (by omega)
  have hT₁ : TCtx Q (2 ^ T) c₁ := hT.of fun r h1 h2 => hK₁ r (by omega)
  refine spec_use (tUp_exec (I := I) c₁ hw₁ hG₁ hT₁ hQ (by rw [h210]; omega)
    (fun y hy => by rw [hpr₁ y hy]; split_ifs <;> first | omega | exact hpr y hy)
    (by rw [h210]; exact hW₁) (by rw [h210]; exact hWl₁)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hW₂, hWl₂, hK₂, hR₂, hO₂, hN₂, hM₂⟩
  have hs2 : ∀ a, a < Q + 8 * 2 ^ T → c₂.nmem a = c₁.nmem a := fun a ha => hN₂ a (Or.inl ha)
  refine ⟨?_, fun y hy => ?_, ?_, ?_, ?_, by rw [hM₂, hM₁], fun a ha h1 h2 h3 h4 => ?_,
    fun a ha => ?_, ?_, ?_, fun r hr => ?_, fun r h1 h2 => ?_, by rw [hO₂, hO₁]⟩
  · rw [h210] at hk₂
    have := lg_lt_pow (show (2 ^ T + x) / 2 < 2 ^ T by omega)
    unfold tUpCost at hk₂
    omega
  · unfold tPr; rw [hs2 _ (by omega)]; exact hpr₁ y hy
  · unfold tOwn; rw [hs2 _ (by omega), hN₁]; simp only [upd_apply]
    split_ifs <;> first | rfl | omega
  · unfold tEnd; rw [hs2 _ (by omega), hN₁]; simp only [upd_apply]
    split_ifs <;> first | rfl | omega
  · unfold tMin; rw [hs2 _ (by omega), hN₁]; simp only [upd_apply]
    split_ifs <;> first | rfl
  · rw [hs2 a ha]; exact hn a h1 h2 h3 h4
  · rw [hN₂ a (by omega)]; exact hn a (by omega) (by omega) (by omega) (by omega)
  · refine hW₂.congr (fun y hy => ?_) (fun y hy => by unfold tKey; rw [hM₂])
    unfold tPr; rw [hs2 _ (by omega)]
  · refine hWl₂.congr (fun y hy => ?_) (fun _ _ => rfl)
    unfold tPr; rw [hs2 _ (by omega)]
  · rw [hK₂ r (by omega)]; exact hK₁ r hr
  · rw [hR₂ r h1 h2, hR₁]

/-- **A row is no longer a start**, and recomputing the tournaments. -/
theorem tClr_exec {Q T x : ℕ} (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hT : TCtx Q (2 ^ T) c) (hQ : Q + 16 * 2 ^ T ≤ P.W) (h121 : c.nreg 121 = 2 ^ T)
    (h230 : c.nreg 230 = x) (hx : x < 2 ^ T) (hpr : ∀ y < 2 ^ T, tPr Q c.nmem y ≤ 1)
    (hW : WinOK (2 ^ T) (tPr Q c.nmem) (tKey Q c.rmem) (tWn Q (2 ^ T) c.nmem) 0)
    (hWl : WinOK (2 ^ T) (tPr Q c.nmem) (fun x => (x : ℝ)) (tWl Q (2 ^ T) c.nmem) 0) :
    ∃ c' k', Exec I P.W tClr c c' k' ∧ k' ≤ 49 * T + 7 ∧
      (∀ y < 2 ^ T, tPr Q c'.nmem y = if y = x then 0 else tPr Q c.nmem y) ∧
      c'.rmem = c.rmem ∧
      (∀ a, a < Q + 8 * 2 ^ T → a ≠ Q + 8 * x → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < Q ∨ Q + 12 * 2 ^ T ≤ a) → c'.nmem a = c.nmem a) ∧
      WinOK (2 ^ T) (tPr Q c'.nmem) (tKey Q c'.rmem) (tWn Q (2 ^ T) c'.nmem) 0 ∧
      WinOK (2 ^ T) (tPr Q c'.nmem) (fun x => (x : ℝ)) (tWl Q (2 ^ T) c'.nmem) 0 ∧
      (∀ r, (r < 210 ∨ (220 ≤ r ∧ r ≠ 234)) → c'.nreg r = c.nreg r) ∧
      (∀ r, r ≠ 210 → r ≠ 211 → c'.rreg r = c.rreg r) ∧ c'.output = c.output := by
  have g111 := hG.r111
  have g117 := hG.r117
  have g118 := hG.r118
  have g208 := hT.r208
  unfold tClr
  refine spec_seq ?_
  exec_block
  · rw [h230, g118]; omega
  · config_simp; rw [h230, g118, g208]; omega
  · config_simp; rw [h121, h230]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have e8 : x * 8 + Q = Q + 8 * x := by ring
  have hN₁ : c₁.nmem = upd c.nmem (Q + 8 * x) 0 := by
    rw [← hc₁]; config_simp; rw [h230, g118, g208, g117, e8]
  have hM₁ : c₁.rmem = c.rmem := by rw [← hc₁]
  have hK₁ : ∀ r, (r < 210 ∨ (220 ≤ r ∧ r ≠ 234)) → c₁.nreg r = c.nreg r := fun r hr => by
    rw [← hc₁]; config_simp; upd_tac
  have h210 : c₁.nreg 210 = (2 ^ T + x) / 2 := by
    rw [← hc₁]; config_simp; rw [h121, h230, g111]
  have hR₁ : c₁.rreg = c.rreg := by rw [← hc₁]
  have hO₁ : c₁.output = c.output := by rw [← hc₁]
  have hn : ∀ a, a ≠ Q + 8 * x → c₁.nmem a = c.nmem a := fun a h1 => by
    rw [hN₁, upd_other _ _ _ h1]
  obtain ⟨hW₁, hWl₁⟩ := winOK_rec (rm' := c₁.rmem) hW hWl (fun a h1 _ _ _ => hn a h1)
    (fun a _ => by rw [hM₁]) hx
  have hpr₁ : ∀ y < 2 ^ T, tPr Q c₁.nmem y = if y = x then 0 else tPr Q c.nmem y := fun y hy => by
    unfold tPr; rw [hN₁]; simp only [upd_apply]; split_ifs <;> first | rfl | omega
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => hK₁ r (by omega)
  have hT₁ : TCtx Q (2 ^ T) c₁ := hT.of fun r h1 h2 => hK₁ r (by omega)
  refine spec_use (tUp_exec (I := I) c₁ hw₁ hG₁ hT₁ hQ (by rw [h210]; omega)
    (fun y hy => by rw [hpr₁ y hy]; split_ifs <;> first | omega | exact hpr y hy)
    (by rw [h210]; exact hW₁) (by rw [h210]; exact hWl₁)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hW₂, hWl₂, hK₂, hR₂, hO₂, hN₂, hM₂⟩
  have hs2 : ∀ a, a < Q + 8 * 2 ^ T → c₂.nmem a = c₁.nmem a := fun a ha => hN₂ a (Or.inl ha)
  refine ⟨?_, fun y hy => ?_, by rw [hM₂, hM₁], fun a ha h1 => ?_, fun a ha => ?_, ?_, ?_,
    fun r hr => ?_, fun r h1 h2 => ?_, by rw [hO₂, hO₁]⟩
  · rw [h210] at hk₂
    have := lg_lt_pow (show (2 ^ T + x) / 2 < 2 ^ T by omega)
    unfold tUpCost at hk₂
    omega
  · unfold tPr; rw [hs2 _ (by omega)]; exact hpr₁ y hy
  · rw [hs2 a ha]; exact hn a h1
  · rw [hN₂ a (by omega)]; exact hn a (by omega)
  · refine hW₂.congr (fun y hy => ?_) (fun y hy => by unfold tKey; rw [hM₂])
    unfold tPr; rw [hs2 _ (by omega)]
  · refine hWl₂.congr (fun y hy => ?_) (fun _ _ => rfl)
    unfold tPr; rw [hs2 _ (by omega)]
  · rw [hK₂ r (by omega)]; exact hK₁ r hr
  · rw [hR₂ r h1 h2, hR₁]

end FR

end Monge

end PlanarFlow
