module

public import PlanarFlow.Monge.FRTrip

/-!
# FR-Dijkstra on the machine: the neighbouring triplets

Two descents of the tournament of the first starts (`tWl`) of a half block (`s = 2 ^ T` rows),
in the style of `PlanarFlow.Monge.FR.tBnd`, each within `18 T + 20` steps:

* `tPv_exec`: the **last start before** a row `z = r221` (in `r222`; `s` if there is none). At a
  node, the first start `b` of the right child is before `z` exactly when the right child has a
  start before `z`; then the answer is in the right child (and `b` is a candidate), otherwise in
  the left child.
* `tNx_exec`: the **first start after** a row `e = r221` (in `r222`; `s` if there is none). At a
  node, if the first start `b` of the right child is after `e`, it is a candidate and the answer
  (if better) is in the left child; otherwise the answer is in the right child.

These find the neighbours of a triplet when a new source is activated
(`PlanarFlow.Monge.FR.own_order_left`, `own_order_right`): the triplets that it beats are next to
the first triplet whose owner is before it (`PlanarFlow.Monge.FR.tBnd_exec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

/-! ### The programs -/

/-- The loads of a step of a search at the node `r223`: the first start `b = r225` below the
right child, its start flag `r227`, and `r223 := 2 r223`. -/
def srchLoad : Stmt :=
  block [.mulN 224 223 116, .addN 224 224 209, .addN 224 224 111, .addN 224 224 110,
    .loadN 225 224, .mulN 226 225 118, .addN 226 226 208, .loadN 227 226, .mulN 223 223 111]

/-- One step of the search for the last start before `z = r221`. -/
def pvBody : Stmt :=
  .seq srchLoad <|
  .ifLtN 227 110 .skip (.ifLtN 225 221 (block [.copyN 222 225, .addN 223 223 110]) .skip)

/-- One step of the search for the first start after `e = r221`. -/
def nxBody : Stmt :=
  .seq srchLoad <|
  .ifLtN 227 110 .skip (.ifLtN 221 225 (.instr (.copyN 222 225)) (.instr (.addN 223 223 110)))

/-- The loads at the leaf `r223`: the row `r224` and its start flag `r227`. -/
def srchLeaf : Stmt :=
  block [.subN 224 223 121, .mulN 226 224 118, .addN 226 226 208, .loadN 227 226]

/-- The descent from the root to a leaf (no candidate: `r222 := s`). -/
def srchDesc (body : Stmt) : Stmt :=
  .seq (block [.copyN 223 110, .copyN 222 121]) (.seq (.whileLtN 223 121 body) srchLeaf)

/-- **The last start before `z = r221`** (in `r222`; `s` if there is none). -/
def tPv : Stmt :=
  .seq (srchDesc pvBody) (.ifLtN 227 110 .skip (.ifLtN 224 221 (.instr (.copyN 222 224)) .skip))

/-- **The first start after `e = r221`** (in `r222`; `s` if there is none). -/
def tNx : Stmt :=
  .seq (srchDesc nxBody) (.ifLtN 227 110 .skip (.ifLtN 221 224 (.instr (.copyN 222 224)) .skip))

/-! ### The invariants -/

section inv

variable {Q T z : ℕ} {nm : ℕ → ℕ}

/-- A start before `z`. -/
def Pv (Q s z : ℕ) (nm : ℕ → ℕ) (y : ℕ) : Prop := y < s ∧ tPr Q nm y = 1 ∧ y < z

/-- A start after `z`. -/
def Nx (Q s z : ℕ) (nm : ℕ → ℕ) (y : ℕ) : Prop := y < s ∧ tPr Q nm y = 1 ∧ z < y

/-- The invariant of the search for the last start before `z`, at the node `v` of height `j`,
with the candidate `cd` (`s` for none). -/
structure PvInv (Q s z : ℕ) (nm : ℕ → ℕ) (j v cd : ℕ) : Prop where
  cand : cd = s ∨ Pv Q s z nm cd
  out : ∀ y, Pv Q s z nm y → nd s j y ≠ v → cd ≠ s ∧ y ≤ cd
  inn : ∀ y, Pv Q s z nm y → nd s j y = v → cd = s ∨ cd ≤ y

/-- The invariant of the search for the first start after `z`. -/
structure NxInv (Q s z : ℕ) (nm : ℕ → ℕ) (j v cd : ℕ) : Prop where
  cand : cd = s ∨ Nx Q s z nm cd
  out : ∀ y, Nx Q s z nm y → nd s j y ≠ v → cd ≤ y
  inn : ∀ y, Nx Q s z nm y → nd s j y = v → y < cd

lemma pvInv_root : PvInv Q (2 ^ T) z nm T 1 (2 ^ T) :=
  ⟨Or.inl rfl, fun _ hy hn => absurd (nd_root hy.1) hn, fun _ _ _ => Or.inl rfl⟩

lemma nxInv_root : NxInv Q (2 ^ T) z nm T 1 (2 ^ T) :=
  ⟨Or.inl rfl, fun _ hy hn => absurd (nd_root hy.1) hn, fun _ hy _ => hy.1⟩

/-- The facts on the first start `b` below the right child of a node of height `j + 1`. -/
lemma srch_first (hW : WinOK (2 ^ T) (tPr Q nm) (fun x => (x : ℝ)) (tWl Q (2 ^ T) nm) 0)
    {j v : ℕ} (hv : Valid (2 ^ T) (j + 1) v) :
    let b := tWl Q (2 ^ T) nm (2 * v + 1)
    b < 2 ^ T ∧ nd (2 ^ T) j b = 2 * v + 1 ∧
      ∀ y, y < 2 ^ T → nd (2 ^ T) j y = 2 * v + 1 → tPr Q nm y = 1 → tPr Q nm b = 1 ∧ b ≤ y := by
  intro b
  obtain ⟨-, hv1⟩ := valid_child hv
  have hvs := valid_lt hv
  have hbu := hW.under (2 * v + 1) (by omega) (by omega)
  refine ⟨hbu.1, anc_nd hbu.1 hv1 hbu.2, fun y hy hn hp => ?_⟩
  have := win_node hW (2 * v + 1) (by omega) (by omega) y hy ⟨j, by rw [← hn]; rfl⟩ hp
  exact ⟨this.1, by exact_mod_cast this.2⟩

/-- One step of the search for the last start before `z`. -/
theorem pvInv_step (hW : WinOK (2 ^ T) (tPr Q nm) (fun x => (x : ℝ)) (tWl Q (2 ^ T) nm) 0)
    {j v cd : ℕ} (hv : Valid (2 ^ T) (j + 1) v) (h : PvInv Q (2 ^ T) z nm (j + 1) v cd) :
    let b := tWl Q (2 ^ T) nm (2 * v + 1)
    (tPr Q nm b = 1 → b < z → PvInv Q (2 ^ T) z nm j (2 * v + 1) b) ∧
    (¬ (tPr Q nm b = 1 ∧ b < z) → PvInv Q (2 ^ T) z nm j (2 * v) cd) := by
  intro b
  obtain ⟨hb_lt, hb_nd, hfirst⟩ := srch_first hW hv
  have hup : ∀ y, nd (2 ^ T) (j + 1) y = v ↔ nd (2 ^ T) j y = 2 * v ∨
      nd (2 ^ T) j y = 2 * v + 1 := fun y => nd_child
  refine ⟨fun hpb hbz => ⟨Or.inr ⟨hb_lt, hpb, hbz⟩, fun y hy hn => ?_, fun y hy hn => ?_⟩,
    fun hnb => ⟨h.cand, fun y hy hn => ?_, fun y hy hn => ?_⟩⟩
  · refine ⟨by omega, ?_⟩
    by_cases hyv : nd (2 ^ T) (j + 1) y = v
    · rcases (hup y).1 hyv with e | e
      · exact (nd_order e hb_nd).le
      · exact absurd e hn
    · obtain ⟨h1, h2⟩ := h.out y hy hyv
      rcases h.inn b ⟨hb_lt, hpb, hbz⟩ ((hup b).2 (Or.inr hb_nd)) with h3 | h3
      · exact absurd h3 h1
      · omega
  · exact Or.inr (hfirst y hy.1 hn hy.2.1).2
  · by_cases hyv : nd (2 ^ T) (j + 1) y = v
    · rcases (hup y).1 hyv with e | e
      · exact absurd e hn
      · obtain ⟨h1, h2⟩ := hfirst y hy.1 e hy.2.1
        exact absurd ⟨h1, by have := hy.2.2; omega⟩ hnb
    · exact h.out y hy hyv
  · exact h.inn y hy ((hup y).2 (Or.inl hn))

/-- One step of the search for the first start after `z`. -/
theorem nxInv_step (hW : WinOK (2 ^ T) (tPr Q nm) (fun x => (x : ℝ)) (tWl Q (2 ^ T) nm) 0)
    {j v cd : ℕ} (hv : Valid (2 ^ T) (j + 1) v) (h : NxInv Q (2 ^ T) z nm (j + 1) v cd) :
    let b := tWl Q (2 ^ T) nm (2 * v + 1)
    (tPr Q nm b = 1 → ¬ z < b → NxInv Q (2 ^ T) z nm j (2 * v + 1) cd) ∧
    (tPr Q nm b = 1 → z < b → NxInv Q (2 ^ T) z nm j (2 * v) b) ∧
    (tPr Q nm b ≠ 1 → NxInv Q (2 ^ T) z nm j (2 * v) cd) := by
  intro b
  obtain ⟨hb_lt, hb_nd, hfirst⟩ := srch_first hW hv
  have hup : ∀ y, nd (2 ^ T) (j + 1) y = v ↔ nd (2 ^ T) j y = 2 * v ∨
      nd (2 ^ T) j y = 2 * v + 1 := fun y => nd_child
  refine ⟨fun hpb hnb => ⟨h.cand, fun y hy hn => ?_, fun y hy hn => ?_⟩,
    fun hpb hb => ⟨Or.inr ⟨hb_lt, hpb, hb⟩, fun y hy hn => ?_, fun y hy hn => ?_⟩,
    fun hpb => ⟨h.cand, fun y hy hn => ?_, fun y hy hn => ?_⟩⟩
  · by_cases hyv : nd (2 ^ T) (j + 1) y = v
    · rcases (hup y).1 hyv with e | e
      · exfalso
        have := nd_order e hb_nd
        have := hy.2.2
        omega
      · exact absurd e hn
    · exact h.out y hy hyv
  · exact h.inn y hy ((hup y).2 (Or.inr hn))
  · by_cases hyv : nd (2 ^ T) (j + 1) y = v
    · rcases (hup y).1 hyv with e | e
      · exact absurd e hn
      · exact (hfirst y hy.1 e hy.2.1).2
    · have h1 := h.out y hy hyv
      have h2 := h.inn b ⟨hb_lt, hpb, hb⟩ ((hup b).2 (Or.inr hb_nd))
      omega
  · exact nd_order hn hb_nd
  · by_cases hyv : nd (2 ^ T) (j + 1) y = v
    · rcases (hup y).1 hyv with e | e
      · exact absurd e hn
      · exact absurd (hfirst y hy.1 e hy.2.1).1 hpb
    · exact h.out y hy hyv
  · exact h.inn y hy ((hup y).2 (Or.inl hn))

/-- The end of the search for the last start before `z`. -/
theorem pvInv_leaf {x cd : ℕ} (hx : x < 2 ^ T) (h : PvInv Q (2 ^ T) z nm 0 (2 ^ T + x) cd) :
    let r := if tPr Q nm x = 1 ∧ x < z then x else cd
    (r = 2 ^ T ∨ Pv Q (2 ^ T) z nm r) ∧ ∀ y, Pv Q (2 ^ T) z nm y → r ≠ 2 ^ T ∧ y ≤ r := by
  intro r
  have hnd : ∀ y, nd (2 ^ T) 0 y = 2 ^ T + x ↔ y = x := fun y => by rw [nd_zero]; omega
  by_cases hb : tPr Q nm x = 1 ∧ x < z
  · have e : r = x := iteT hb
    rw [e]
    refine ⟨Or.inr ⟨hx, hb⟩, fun y hy => ⟨by omega, ?_⟩⟩
    by_cases hyx : y = x
    · omega
    · obtain ⟨h1, h2⟩ := h.out y hy (fun hn => hyx ((hnd y).1 hn))
      rcases h.inn x ⟨hx, hb⟩ ((hnd x).2 rfl) with h3 | h3
      · exact absurd h3 h1
      · omega
  · have e : r = cd := iteF hb
    rw [e]
    refine ⟨h.cand, fun y hy => h.out y hy fun hn => hb ?_⟩
    rw [(hnd y).1 hn] at hy; exact hy.2

/-- The end of the search for the first start after `z`. -/
theorem nxInv_leaf {x cd : ℕ} (hx : x < 2 ^ T) (h : NxInv Q (2 ^ T) z nm 0 (2 ^ T + x) cd) :
    let r := if tPr Q nm x = 1 ∧ z < x then x else cd
    (r = 2 ^ T ∨ Nx Q (2 ^ T) z nm r) ∧ ∀ y, Nx Q (2 ^ T) z nm y → r ≤ y := by
  intro r
  have hnd : ∀ y, nd (2 ^ T) 0 y = 2 ^ T + x ↔ y = x := fun y => by rw [nd_zero]; omega
  by_cases hb : tPr Q nm x = 1 ∧ z < x
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

end inv

/-! ### The executions -/

variable {P : Prm} {I : Input}

/-- The state of a search, with the invariant `inv j v cd`. -/
structure ISr (P : Prm) (s : ℕ) (inv : ℕ → ℕ → ℕ → Prop) (c₀ : Config) (j : ℕ) (c : Config) :
    Prop where
  wb : WordsBounded P.W c
  keepN : ∀ r, (r < 222 ∨ 229 ≤ r) → c.nreg r = c₀.nreg r
  rr : c.rreg = c₀.rreg
  nm : c.nmem = c₀.nmem
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
  valid : Valid s j (c.nreg 223)
  inv : inv j (c.nreg 223) (c.nreg 222)

/-- The loads of a step. -/
theorem srchLoad_exec {Q T : ℕ} {inv : ℕ → ℕ → ℕ → Prop} {c₀ : Config} (hG : Glob P c₀)
    (hT : TCtx Q (2 ^ T) c₀) (hQ : Q + 16 * 2 ^ T ≤ P.W)
    (hW : WinOK (2 ^ T) (tPr Q c₀.nmem) (fun x => (x : ℝ)) (tWl Q (2 ^ T) c₀.nmem) 0)
    {j v : ℕ} (c : Config) (hI : ISr P (2 ^ T) inv c₀ (j + 1) c) (hv : c.nreg 223 = v) :
    ∃ c' k', Exec I P.W srchLoad c c' k' ∧ k' ≤ 9 ∧
      c'.nreg 223 = 2 * v ∧ c'.nreg 225 = tWl Q (2 ^ T) c₀.nmem (2 * v + 1) ∧
      c'.nreg 227 = tPr Q c₀.nmem (tWl Q (2 ^ T) c₀.nmem (2 * v + 1)) ∧
      c'.nreg 222 = c.nreg 222 ∧ (∀ r, (r < 222 ∨ 229 ≤ r) → c'.nreg r = c₀.nreg r) ∧
      c'.rreg = c₀.rreg ∧ c'.nmem = c₀.nmem ∧ c'.rmem = c₀.rmem ∧ c'.output = c₀.output := by
  have hc := hI.wb
  have g : ∀ r, (r < 222 ∨ 229 ≤ r) → c.nreg r = c₀.nreg r := hI.keepN
  have g110 : c.nreg 110 = 1 := (g 110 (by omega)).trans hG.r110
  have g111 : c.nreg 111 = 2 := (g 111 (by omega)).trans hG.r111
  have g116 : c.nreg 116 = 4 := (g 116 (by omega)).trans hG.r116
  have g118 : c.nreg 118 = 8 := (g 118 (by omega)).trans hG.r118
  have g208 : c.nreg 208 = Q := (g 208 (by omega)).trans hT.r208
  have g209 : c.nreg 209 = Q + 8 * 2 ^ T := (g 209 (by omega)).trans hT.r209
  have hvv := hI.valid
  rw [hv] at hvv
  have hvs := valid_lt hvv
  have hbu := hW.under (2 * v + 1) (by omega) (by omega)
  generalize hb : tWl Q (2 ^ T) c₀.nmem (2 * v + 1) = b at hbu
  have eb : c.nmem (c.nreg 223 * c.nreg 116 + c.nreg 209 + c.nreg 111 + c.nreg 110) = b := by
    rw [hv, g116, g209, g111, g110, hI.nm, ← hb]; unfold tWl; congr 1; ring
  have epb : c.nmem (b * c.nreg 118 + c.nreg 208) = tPr Q c₀.nmem b := by
    rw [g118, g208, hI.nm]; unfold tPr; congr 1; ring
  unfold srchLoad
  exec_block
  · rw [hv, g116]; omega
  · config_simp; rw [hv, g116, g209]; omega
  · config_simp; rw [hv, g116, g209, g111]; omega
  · config_simp; rw [hv, g116, g209, g111, g110]; omega
  · config_simp; rw [eb, g118]; omega
  · config_simp; rw [eb, g118, g208]; omega
  · config_simp; rw [hv, g111]; omega
  refine ⟨le_of_eq rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · config_simp; rw [hv, g111]; ring
  · config_simp; exact eb
  · config_simp; rw [eb, epb]
  · config_simp
  · config_simp; rw [← g r hr]; upd_tac
  · config_simp; exact hI.rr
  · config_simp; exact hI.nm
  · config_simp; exact hI.rm
  · config_simp; exact hI.out

theorem pvBody_exec {Q T z : ℕ} {c₀ : Config} (hG : Glob P c₀) (hT : TCtx Q (2 ^ T) c₀)
    (hQ : Q + 16 * 2 ^ T ≤ P.W) (h121 : c₀.nreg 121 = 2 ^ T) (h221 : c₀.nreg 221 = z)
    (hpr : ∀ x < 2 ^ T, tPr Q c₀.nmem x ≤ 1)
    (hW : WinOK (2 ^ T) (tPr Q c₀.nmem) (fun x => (x : ℝ)) (tWl Q (2 ^ T) c₀.nmem) 0)
    {j : ℕ} (c : Config) (hI : ISr P (2 ^ T) (PvInv Q (2 ^ T) z c₀.nmem) c₀ j c)
    (hlt : c.nreg 223 < c.nreg 121) :
    ∃ c' k', Exec I P.W pvBody c c' k' ∧ ISr P (2 ^ T) (PvInv Q (2 ^ T) z c₀.nmem) c₀ (j - 1) c' ∧
      1 ≤ j ∧ k' ≤ 16 := by
  have hc := hI.wb
  rw [(hI.keepN 121 (by omega)).trans h121] at hlt
  have hv := hI.valid
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := (valid_lt_iff hv).1 hlt; omega⟩
  generalize hvv : c.nreg 223 = v at hv hlt
  have hbu := hW.under (2 * v + 1) (by have := valid_lt hv; omega) (by omega)
  obtain ⟨st1, st2⟩ := pvInv_step hW hv (hvv ▸ hI.inv)
  obtain ⟨hv0, hv1⟩ := valid_child hv
  unfold pvBody
  refine spec_seq ?_
  refine spec_use (srchLoad_exec (I := I) hG hT hQ hW c hI hvv) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨f223, f225, f227, f222, fK, fR, fN, fM, fO⟩
  generalize hb : tWl Q (2 ^ T) c₀.nmem (2 * v + 1) = b at hbu f225 f227 st1 st2
  have k110 : c₁.nreg 110 = 1 := (fK 110 (by omega)).trans hG.r110
  have k221 : c₁.nreg 221 = z := (fK 221 (by omega)).trans h221
  by_cases hp : tPr Q c₀.nmem b < 1
  · refine spec_ifLtN_true (by rw [f227, k110]; exact hp) ?_
    refine spec_skip hw₁ ⟨⟨hw₁, fK, fR, fN, fM, fO, by rw [f223]; exact hv0, ?_⟩, by omega,
      by omega⟩
    rw [f223, f222]
    exact st2 (fun h => by omega)
  · refine spec_ifLtN_false (by rw [f227, k110]; exact hp) ?_
    have hpb : tPr Q c₀.nmem b = 1 := by have := hpr b hbu.1; omega
    by_cases ho : b < z
    · refine spec_ifLtN_true (by rw [f225, k221]; exact ho) ?_
      exec_block
      · config_simp; rw [f223, k110]; omega
      refine ⟨⟨‹_›, fun r hr => by config_simp; rw [upd_other _ _ _ (by omega),
        upd_other _ _ _ (by omega)]; exact fK r hr,
        by config_simp; exact fR, by config_simp; exact fN, by config_simp; exact fM,
        by config_simp; exact fO, by config_simp; rw [f223, k110]; exact hv1, ?_⟩, by omega,
        by omega⟩
      config_simp; rw [f223, k110, f225]
      exact st1 hpb ho
    · refine spec_ifLtN_false (by rw [f225, k221]; exact ho) ?_
      refine spec_skip hw₁ ⟨⟨hw₁, fK, fR, fN, fM, fO, by rw [f223]; exact hv0, ?_⟩, by omega,
        by omega⟩
      rw [f223, f222]
      exact st2 (fun h => ho h.2)

theorem nxBody_exec {Q T z : ℕ} {c₀ : Config} (hG : Glob P c₀) (hT : TCtx Q (2 ^ T) c₀)
    (hQ : Q + 16 * 2 ^ T ≤ P.W) (h121 : c₀.nreg 121 = 2 ^ T) (h221 : c₀.nreg 221 = z)
    (hpr : ∀ x < 2 ^ T, tPr Q c₀.nmem x ≤ 1)
    (hW : WinOK (2 ^ T) (tPr Q c₀.nmem) (fun x => (x : ℝ)) (tWl Q (2 ^ T) c₀.nmem) 0)
    {j : ℕ} (c : Config) (hI : ISr P (2 ^ T) (NxInv Q (2 ^ T) z c₀.nmem) c₀ j c)
    (hlt : c.nreg 223 < c.nreg 121) :
    ∃ c' k', Exec I P.W nxBody c c' k' ∧ ISr P (2 ^ T) (NxInv Q (2 ^ T) z c₀.nmem) c₀ (j - 1) c' ∧
      1 ≤ j ∧ k' ≤ 16 := by
  have hc := hI.wb
  rw [(hI.keepN 121 (by omega)).trans h121] at hlt
  have hv := hI.valid
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := (valid_lt_iff hv).1 hlt; omega⟩
  generalize hvv : c.nreg 223 = v at hv hlt
  have hbu := hW.under (2 * v + 1) (by have := valid_lt hv; omega) (by omega)
  obtain ⟨st1, st2, st3⟩ := nxInv_step hW hv (hvv ▸ hI.inv)
  obtain ⟨hv0, hv1⟩ := valid_child hv
  unfold nxBody
  refine spec_seq ?_
  refine spec_use (srchLoad_exec (I := I) hG hT hQ hW c hI hvv) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨f223, f225, f227, f222, fK, fR, fN, fM, fO⟩
  generalize hb : tWl Q (2 ^ T) c₀.nmem (2 * v + 1) = b at hbu f225 f227 st1 st2 st3
  have k110 : c₁.nreg 110 = 1 := (fK 110 (by omega)).trans hG.r110
  have k221 : c₁.nreg 221 = z := (fK 221 (by omega)).trans h221
  by_cases hp : tPr Q c₀.nmem b < 1
  · refine spec_ifLtN_true (by rw [f227, k110]; exact hp) ?_
    refine spec_skip hw₁ ⟨⟨hw₁, fK, fR, fN, fM, fO, by rw [f223]; exact hv0, ?_⟩, by omega,
      by omega⟩
    rw [f223, f222]
    exact st3 (by omega)
  · refine spec_ifLtN_false (by rw [f227, k110]; exact hp) ?_
    have hpb : tPr Q c₀.nmem b = 1 := by have := hpr b hbu.1; omega
    by_cases ho : z < b
    · refine spec_ifLtN_true (by rw [f225, k221]; exact ho) ?_
      refine spec_instr (Exec.copyN hw₁ 222 225) fun hw₂ => ?_
      refine ⟨⟨hw₂, fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]; exact fK r hr,
        by config_simp; exact fR, by config_simp; exact fN, by config_simp; exact fM,
        by config_simp; exact fO, by config_simp; rw [f223]; exact hv0, ?_⟩, by omega, by omega⟩
      config_simp; rw [f223, f225]
      exact st2 hpb ho
    · refine spec_ifLtN_false (by rw [f225, k221]; exact ho) ?_
      refine spec_instr (Exec.addN hw₁ 223 223 110 (by rw [f223, k110]; omega)) fun hw₂ => ?_
      refine ⟨⟨hw₂, fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]; exact fK r hr,
        by config_simp; exact fR, by config_simp; exact fN, by config_simp; exact fM,
        by config_simp; exact fO, by config_simp; rw [f223, k110]; exact hv1, ?_⟩, by omega,
        by omega⟩
      config_simp; rw [f223, k110, f222]
      exact st1 hpb ho

/-- The loop of a search, from the root to a leaf, and the loads at the leaf. -/
theorem srchLoop_exec {Q T : ℕ} {inv : ℕ → ℕ → ℕ → Prop} {body : Stmt} (c : Config)
    (hc : WordsBounded P.W c) (hG : Glob P c) (hT : TCtx Q (2 ^ T) c) (hQ : Q + 16 * 2 ^ T ≤ P.W)
    (h121 : c.nreg 121 = 2 ^ T) (h0 : inv T 1 (2 ^ T))
    (hbody : ∀ (c₁ : Config) (j : ℕ) (c' : Config), ISr P (2 ^ T) inv c₁ j c' →
      (∀ r, (r < 222 ∨ 229 ≤ r) → c₁.nreg r = c.nreg r) → c₁.nmem = c.nmem →
      c'.nreg 223 < c'.nreg 121 →
      ∃ c'' k', Exec I P.W body c' c'' k' ∧ ISr P (2 ^ T) inv c₁ (j - 1) c'' ∧ 1 ≤ j ∧ k' ≤ 16) :
    ∃ c' k', Exec I P.W (srchDesc body) c c' k' ∧ k' ≤ 18 * T + 10 ∧
      ∃ x < 2 ^ T, inv 0 (2 ^ T + x) (c'.nreg 222) ∧ c'.nreg 224 = x ∧
        c'.nreg 227 = tPr Q c.nmem x ∧ (∀ r, (r < 222 ∨ 229 ≤ r) → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hs : 1 ≤ 2 ^ T := Nat.one_le_two_pow
  unfold srchDesc
  refine spec_seq ?_
  exec_block
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have hI₁ : ISr P (2 ^ T) inv c₁ T c₁ :=
    ⟨hw₁, fun _ _ => rfl, rfl, rfl, rfl, rfl, by
      rw [← hc₁]; config_simp; rw [hG.r110]; exact valid_root T, by
      rw [← hc₁]; config_simp; rw [hG.r110, h121]; exact h0⟩
  have e₁ : ∀ r, (r < 222 ∨ 229 ≤ r) → c₁.nreg r = c.nreg r := fun r hr => by
    rw [← hc₁]; config_simp; upd_tac
  have hN₁ : c₁.nmem = c.nmem := by rw [← hc₁]
  obtain ⟨j, c₂, k₂, ex₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_ghost (P := I) (W := P.W) (a := 223)
    (b := 121) (body := body) (fun j c => ISr P (2 ^ T) inv c₁ j c) (fun j _ => 18 * j)
    (fun _ _ h => h.wb)
    (fun j c' hI hlt => by
      obtain ⟨c'', k', e, hI', hj, hk⟩ := hbody c₁ j c' hI e₁ hN₁ hlt
      exact ⟨j - 1, c'', k', e, hI', by omega⟩) hI₁
  refine spec_seq ⟨c₂, k₂, ex₂, ?_⟩
  have k121 : c₂.nreg 121 = 2 ^ T := by rw [hI₂.keepN 121 (by omega), e₁ 121 (by omega), h121]
  rw [k121] at hn₂
  have hj0 : j = 0 := by
    by_contra h; exact hn₂ ((valid_lt_iff hI₂.valid).2 (by omega))
  subst hj0
  obtain ⟨-, hv2, hv3⟩ := valid_zero.1 hI₂.valid
  obtain ⟨x, hx⟩ : ∃ x, c₂.nreg 223 = 2 ^ T + x := ⟨c₂.nreg 223 - 2 ^ T, by omega⟩
  have hxs : x < 2 ^ T := by omega
  have hc₂ := hI₂.wb
  have g : ∀ r, (r < 222 ∨ 229 ≤ r) → c₂.nreg r = c.nreg r := fun r hr =>
    (hI₂.keepN r hr).trans (e₁ r hr)
  have g118 : c₂.nreg 118 = 8 := (g 118 (by omega)).trans hG.r118
  have g208 : c₂.nreg 208 = Q := (g 208 (by omega)).trans hT.r208
  have hN₂ : c₂.nmem = c.nmem := hI₂.nm.trans hN₁
  unfold srchLeaf
  exec_block
  · config_simp; rw [hx, k121, g118]; omega
  · config_simp; rw [hx, k121, g118, g208]; omega
  refine ⟨by omega, x, hxs, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · config_simp; rw [← hx]; exact hI₂.inv
  · config_simp; rw [hx, k121]; omega
  · config_simp; rw [hx, k121, g118, g208, hN₂]; unfold tPr; congr 1; omega
  · config_simp; rw [← g r hr]; upd_tac
  · config_simp; rw [hI₂.rr, ← hc₁]
  · config_simp; exact hN₂
  · config_simp; rw [hI₂.rm, ← hc₁]
  · config_simp; rw [hI₂.out, ← hc₁]

/-- The cost of a search in a half block with `2 ^ T` rows. -/
def srchCost (T : ℕ) : ℕ := 18 * T + 20

/-- **The last start before `z`**: `tPv` leaves in `r222` the last start before `z = r221`, or
`s` if there is none. -/
theorem tPv_exec {Q T z : ℕ} (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hT : TCtx Q (2 ^ T) c) (hQ : Q + 16 * 2 ^ T ≤ P.W) (h121 : c.nreg 121 = 2 ^ T)
    (h221 : c.nreg 221 = z) (hpr : ∀ x < 2 ^ T, tPr Q c.nmem x ≤ 1)
    (hW : WinOK (2 ^ T) (tPr Q c.nmem) (fun x => (x : ℝ)) (tWl Q (2 ^ T) c.nmem) 0) :
    ∃ c' k', Exec I P.W tPv c c' k' ∧ k' ≤ srchCost T ∧
      (c'.nreg 222 = 2 ^ T ∨ Pv Q (2 ^ T) z c.nmem (c'.nreg 222)) ∧
      (∀ y, Pv Q (2 ^ T) z c.nmem y → c'.nreg 222 ≠ 2 ^ T ∧ y ≤ c'.nreg 222) ∧
      (∀ r, (r < 222 ∨ 229 ≤ r) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tPv
  refine spec_seq ?_
  refine spec_use (srchLoop_exec (I := I) (inv := PvInv Q (2 ^ T) z c.nmem) (body := pvBody) c hc
    hG hT hQ h121 pvInv_root (fun c₁ j c' hI hK hN hlt => by
      rw [← hN] at hI ⊢
      exact pvBody_exec (hG.of fun r _ _ => hK r (by omega))
        (hT.of fun r _ _ => hK r (by omega)) hQ (by rw [hK 121 (by omega), h121])
        (by rw [hK 221 (by omega), h221]) (by rw [hN]; exact hpr) (by rw [hN]; exact hW) c' hI hlt))
    ?_
  intro c₁ k₁ hk₁ hw₁ ⟨x, hx, hinv, f224, f227, fK, fR, fN, fM, fO⟩
  have hleaf := pvInv_leaf hx hinv
  have k110 : c₁.nreg 110 = 1 := (fK 110 (by omega)).trans hG.r110
  have k221 : c₁.nreg 221 = z := (fK 221 (by omega)).trans h221
  by_cases hp : tPr Q c.nmem x < 1
  · refine spec_ifLtN_true (by rw [f227, k110]; exact hp) ?_
    have e : (if tPr Q c.nmem x = 1 ∧ x < z then x else c₁.nreg 222) = c₁.nreg 222 :=
      iteF (by omega)
    rw [e] at hleaf
    refine spec_skip hw₁ ⟨by unfold srchCost; omega, hleaf.1, hleaf.2, fK, fR, fN, fM, fO⟩
  · refine spec_ifLtN_false (by rw [f227, k110]; exact hp) ?_
    have hpx : tPr Q c.nmem x = 1 := by have := hpr x hx; omega
    by_cases ho : x < z
    · refine spec_ifLtN_true (by rw [f224, k221]; exact ho) ?_
      refine spec_instr (Exec.copyN hw₁ 222 224) fun hw₂ => ?_
      have e : (if tPr Q c.nmem x = 1 ∧ x < z then x else c₁.nreg 222) = x := iteT ⟨hpx, ho⟩
      rw [e] at hleaf
      refine ⟨by unfold srchCost; omega, by config_simp; rw [f224]; exact hleaf.1,
        by config_simp; rw [f224]; exact hleaf.2, fun r hr => ?_, by config_simp; exact fR,
        by config_simp; exact fN, by config_simp; exact fM, by config_simp; exact fO⟩
      config_simp; rw [upd_other _ _ _ (by omega)]; exact fK r hr
    · refine spec_ifLtN_false (by rw [f224, k221]; exact ho) ?_
      have e : (if tPr Q c.nmem x = 1 ∧ x < z then x else c₁.nreg 222) = c₁.nreg 222 :=
        iteF (fun h => ho h.2)
      rw [e] at hleaf
      refine spec_skip hw₁ ⟨by unfold srchCost; omega, hleaf.1, hleaf.2, fK, fR, fN, fM, fO⟩

/-- **The first start after `e`**: `tNx` leaves in `r222` the first start after `e = r221`, or
`s` if there is none. -/
theorem tNx_exec {Q T z : ℕ} (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hT : TCtx Q (2 ^ T) c) (hQ : Q + 16 * 2 ^ T ≤ P.W) (h121 : c.nreg 121 = 2 ^ T)
    (h221 : c.nreg 221 = z) (hpr : ∀ x < 2 ^ T, tPr Q c.nmem x ≤ 1)
    (hW : WinOK (2 ^ T) (tPr Q c.nmem) (fun x => (x : ℝ)) (tWl Q (2 ^ T) c.nmem) 0) :
    ∃ c' k', Exec I P.W tNx c c' k' ∧ k' ≤ srchCost T ∧
      (c'.nreg 222 = 2 ^ T ∨ Nx Q (2 ^ T) z c.nmem (c'.nreg 222)) ∧
      (∀ y, Nx Q (2 ^ T) z c.nmem y → c'.nreg 222 ≤ y) ∧
      (∀ r, (r < 222 ∨ 229 ≤ r) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tNx
  refine spec_seq ?_
  refine spec_use (srchLoop_exec (I := I) (inv := NxInv Q (2 ^ T) z c.nmem) (body := nxBody) c hc
    hG hT hQ h121 nxInv_root (fun c₁ j c' hI hK hN hlt => by
      rw [← hN] at hI ⊢
      exact nxBody_exec (hG.of fun r _ _ => hK r (by omega))
        (hT.of fun r _ _ => hK r (by omega)) hQ (by rw [hK 121 (by omega), h121])
        (by rw [hK 221 (by omega), h221]) (by rw [hN]; exact hpr) (by rw [hN]; exact hW) c' hI hlt))
    ?_
  intro c₁ k₁ hk₁ hw₁ ⟨x, hx, hinv, f224, f227, fK, fR, fN, fM, fO⟩
  have hleaf := nxInv_leaf hx hinv
  have k110 : c₁.nreg 110 = 1 := (fK 110 (by omega)).trans hG.r110
  have k221 : c₁.nreg 221 = z := (fK 221 (by omega)).trans h221
  by_cases hp : tPr Q c.nmem x < 1
  · refine spec_ifLtN_true (by rw [f227, k110]; exact hp) ?_
    have e : (if tPr Q c.nmem x = 1 ∧ z < x then x else c₁.nreg 222) = c₁.nreg 222 :=
      iteF (by omega)
    rw [e] at hleaf
    refine spec_skip hw₁ ⟨by unfold srchCost; omega, hleaf.1, hleaf.2, fK, fR, fN, fM, fO⟩
  · refine spec_ifLtN_false (by rw [f227, k110]; exact hp) ?_
    have hpx : tPr Q c.nmem x = 1 := by have := hpr x hx; omega
    by_cases ho : z < x
    · refine spec_ifLtN_true (by rw [f224, k221]; exact ho) ?_
      refine spec_instr (Exec.copyN hw₁ 222 224) fun hw₂ => ?_
      have e : (if tPr Q c.nmem x = 1 ∧ z < x then x else c₁.nreg 222) = x := iteT ⟨hpx, ho⟩
      rw [e] at hleaf
      refine ⟨by unfold srchCost; omega, by config_simp; rw [f224]; exact hleaf.1,
        by config_simp; rw [f224]; exact hleaf.2, fun r hr => ?_, by config_simp; exact fR,
        by config_simp; exact fN, by config_simp; exact fM, by config_simp; exact fO⟩
      config_simp; rw [upd_other _ _ _ (by omega)]; exact fK r hr
    · refine spec_ifLtN_false (by rw [f224, k221]; exact ho) ?_
      have e : (if tPr Q c.nmem x = 1 ∧ z < x then x else c₁.nreg 222) = c₁.nreg 222 :=
        iteF (fun h => ho h.2)
      rw [e] at hleaf
      refine spec_skip hw₁ ⟨by unfold srchCost; omega, hleaf.1, hleaf.2, fK, fR, fN, fM, fO⟩

end FR

end Monge

end PlanarFlow
