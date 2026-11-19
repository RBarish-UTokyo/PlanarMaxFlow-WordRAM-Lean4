module

public import PlanarFlow.NegSSSP.NodeNat

/-!
# The node run on natural words: the composition, generic tools and one part

The pieces of the node are compare-bounded one by one (`PlanarFlow/NegSSSP/NodeNat{A,B,C}.lean`);
here they are composed along the runs of `part_exec`, `node_dij_exec`, `rest_exec`, `node_exec`.

* `NCmp I W H s c c'`: a compare-bounded run of `s` from `c` to `c'` (any number of steps);
  `NCmp.seq`, `NCmp.mono`, `NCmp.exec` (with `Exec.det`: the given run itself is compare-bounded).
* `NGood I W H B s c c'`: `NCmp` and the invariant `NInv W B c'` and integer reals at the end;
  `good_glue`, `good_nat` for the glue (`glue_cmp`, `nat_cmp`).
* `seq_parts`: a run of `s ; t` splits; with `Exec.det` and the run of a piece given by its
  `*_exec` lemma, the intermediate configuration of **every** run is the one of the
  `*_exec` lemma, so the hypotheses of `dijk_cmp_emb`, `bfStage_cmp` hold there.
* `part_cmp`: every run of `partProg` (from the start of `part_exec`, with `NInv W' B` and
  integer reals) compares within `64 partB b w B` and ends with `NInv W' (partB b w B)`,
  `partB b w B = (w + 3) (2 b + 3) (b + 1) B` (`pProg`, then FR-Dijkstra, `dijk_cmp_emb`): the
  walk of `part_exec` up to FR-Dijkstra.
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

/-! ### Composing compare-bounded runs -/

/-- A compare-bounded run of `s` from `c` to `c'`. -/
def NCmp (I : Input) (W H : ℕ) (s : Stmt) (c c' : Config) : Prop := ∃ k, ExecCmp I W H s c c' k

theorem NCmp.seq {I : Input} {W H : ℕ} {s t : Stmt} {c c₁ c₂ : Config} (h₁ : NCmp I W H s c c₁)
    (h₂ : NCmp I W H t c₁ c₂) : NCmp I W H (.seq s t) c c₂ := by
  obtain ⟨_, a⟩ := h₁; obtain ⟨_, b⟩ := h₂; exact ⟨_, .seq a b⟩

theorem NCmp.mono {I : Input} {W H H' : ℕ} {s : Stmt} {c c' : Config} (h : NCmp I W H s c c')
    (hH : H ≤ H') : NCmp I W H' s c c' := by
  obtain ⟨k, a⟩ := h; exact ⟨k, a.mono_H hH⟩

/-- The given run itself is compare-bounded. -/
theorem NCmp.exec {I : Input} {W H : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : NCmp I W H s c c') (e : Exec I W s c c' k) : ExecCmp I W H s c c' k := by
  obtain ⟨k', a⟩ := h
  obtain ⟨-, rfl⟩ := Exec.det a.toExec e
  exact a

theorem seq_parts {I : Input} {W : ℕ} {s t : Stmt} {c c' : Config} {k : ℕ}
    (e : Exec I W (.seq s t) c c' k) : ∃ c₁ k₁ k₂, Exec I W s c c₁ k₁ ∧ Exec I W t c₁ c' k₂ := by
  cases e with | seq a b => exact ⟨_, _, _, a, b⟩

/-- A compare-bounded run ending with the invariant and integer reals. -/
def NGood (I : Input) (W H B : ℕ) (s : Stmt) (c c' : Config) : Prop :=
  NCmp I W H s c c' ∧ NInv W B c' ∧ IntAll c'

theorem NGood.seq {I : Input} {W H B B' : ℕ} {s t : Stmt} {c c₁ c₂ : Config}
    (h₁ : NGood I W H B s c c₁) (h₂ : NGood I W H B' t c₁ c₂) : NGood I W H B' (.seq s t) c c₂ :=
  ⟨h₁.1.seq h₂.1, h₂.2⟩

theorem NGood.mono {I : Input} {W H H' B B' : ℕ} {s : Stmt} {c c' : Config}
    (h : NGood I W H B s c c') (hH : H ≤ H') (hB : B ≤ B') : NGood I W H' B' s c c' :=
  ⟨h.1.mono hH, h.2.1.mono hB, h.2.2⟩

theorem good_glue {I : Input} {W H B k : ℕ} {s : Stmt} {c c' : Config} (h : glueOK 2 10 s = true)
    (hD : s.noDivR = true) (e : Exec I W s c c' k) (hI : NInv W B c) (hZ : IntAll c)
    (hH : 2 * B ≤ H) : NGood I W H B s c c' := by
  obtain ⟨C, hI'⟩ := glue_cmp h e hI
  exact ⟨⟨k, C.mono_H hH⟩, hI', Exec.intAll e hD hZ⟩

theorem good_nat {I : Input} {W H B k : ℕ} {s : Stmt} {c c' : Config} (h : natOnly s = true)
    (hD : s.noDivR = true) (e : Exec I W s c c' k) (hI : NInv W B c) (hZ : IntAll c) :
    NGood I W H B s c c' := by
  obtain ⟨C, hI'⟩ := nat_cmp (H := H) h e hI
  exact ⟨⟨k, C⟩, hI', Exec.intAll e hD hZ⟩

/-! ### One part -/

/-- The bound of the invariant after a part: `pProg`, then FR-Dijkstra. -/
def partB (b w B : ℕ) : ℕ := (w + 3) * ((2 * b + 3) * ((b + 1) * B))

theorem partB_le {b w B : ℕ} :
    B ≤ (2 * b + 3) * ((b + 1) * B) ∧ (2 * b + 3) * ((b + 1) * B) ≤ partB b w B := by
  unfold partB
  constructor
  · have : B ≤ (b + 1) * B := Nat.le_mul_of_pos_left B (by omega)
    exact this.trans (Nat.le_mul_of_pos_left _ (by omega))
  · exact Nat.le_mul_of_pos_left _ (by omega)

theorem le_partB {b w B : ℕ} : B ≤ partB b w B :=
  (partB_le (b := b) (w := w)).1.trans partB_le.2

section Node

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

set_option maxHeartbeats 4000000 in
/-- **Every run of one part is compare-bounded** (see the module docstring); the hypotheses are
those of `part_exec` used before FR-Dijkstra. -/
theorem part_cmp {P₀ P₁ : Finset D}
    {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} (h : NodeEnc N P₀ P₁ m w e ν ι)
    {β : ℕ → V} (hβ : IsEnum b β (bdry N P₀ P₁)) {s : ℕ} (hs : s ≤ 1)
    (ℓ : D → ℤ) (E δ : V → ℤ) (Cz : ℤ)
    (hδ : (pg N (partOf P₀ P₁ s) ℓ).IsPot δ)
    {Z M₀ δb W' : ℕ} (hM₀ : M₀ = m + w + 1) (hZ : loB m w ≤ Z) (hW : Z + 22 * M₀ ≤ W')
    (hδb : δb = Z + 4 * M₀ ∨ δb = Z + 5 * M₀)
    (I : Input) (c : Config) (hctx : NCtx m w b Z M₀ c)
    (h830 : c.nreg 830 = s) (h831 : c.nreg 831 = δb)
    (hTm : ∀ d < m, c.nmem (Z + 0 * M₀ + d) = encT N e ν d)
    (hHm : ∀ d < m, c.nmem (Z + 1 * M₀ + d) = encH N e ν d)
    (hSm : ∀ d < m, c.nmem (Z + 2 * M₀ + d) = encS P₀ e d)
    (hLm : ∀ d < m, c.rmem (Z + 3 * M₀ + d) = ℓ (e d))
    (hDm : ∀ v < w, c.rmem (δb + v) = δ (ι v))
    (hNm : ∀ i < b, c.nmem (Z + 6 * M₀ + i) = ν (β i))
    (hEm : ∀ i < b, c.rmem (Z + 7 * M₀ + i) = E (β i))
    (hCm : c.rmem (Z + 21 * M₀) = Cz)
    {B : ℕ} (hI : NInv W' B c) (hZi : IntAll c) {c' : Config} {k : ℕ}
    (ex : Exec I W' partProg c c' k) :
    NGood I W' (64 * partB b w B) (partB b w B) partProg c c' := by
  have hc : WordsBounded W' c := ex.wb_left
  classical
  have hA : loB m w = 4 * m + 18 * w + 175 := rfl
  have hbw : b ≤ w := by rw [hβ.card]; exact card_bdry_le h
  have hends := enc_ends h
  have hnlt : ∀ i < b, ν (β i) < w := fun i hi => h.lt _ (bdry_sub_verts (hβ.mem i hi))
  have hninj : ∀ i < b, ∀ j < b, ν (β i) = ν (β j) → i = j := fun i hi j hj hij =>
    hβ.inj i hi j hj (by rw [← h.inv _ (bdry_sub_verts (hβ.mem i hi)), hij,
      h.inv _ (bdry_sub_verts (hβ.mem j hj))])
  have HS : SlotH m w b Z M₀ W' := ⟨hM₀, hZ, hW, hbw⟩
  have sl : ∀ k < 22, ∀ c' : Config, (∀ r, 800 ≤ r → r < 900 → c'.nreg r = c.nreg r) →
      c'.nreg (803 + k) = Z + k * M₀ := fun k hk c' hr =>
    (hr (803 + k) (by pomega) (by pomega)).trans (hctx.slot k hk)
  -- 1. the bound of the clearing
  obtain ⟨c₁, k₁, e₁, hk₁, r900₁, hn₁, hrr₁, hnm₁, hrm₁, ho₁⟩ := clrSet_exec (P := I) c hc
  have hR₁ : ∀ r, 800 ≤ r → r < 900 → c₁.nreg r = c.nreg r := fun r _ _ => hn₁ r (by pomega)
  -- 2. the clearing
  obtain ⟨c₂, k₂, e₂, hk₂, z₂, hkp₂, hn₂, hrr₂, hrm₂, ho₂⟩ := clrProg_exec (P := I)
    (L := loB m w) (by pomega) c₁ e₁.wb_right (by rw [r900₁, hctx.r825])
  have hR₂ : ∀ r, 800 ≤ r → r < 900 → c₂.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₂ r (by pomega)).trans (hR₁ r h1 h2)
  have hm₂ : ∀ a, loB m w ≤ a → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hkp₂ a ha, hnm₁]
  -- 3., 4. the initial lengths and the prices
  obtain ⟨c₃, k₃, e₃, hk₃, p500, p501, p502, p505, p506, p507, p508, pC, hn₃, hnm₃, hrm₃, ho₃⟩ :=
    pSet_exec (P := I) c₂ e₂.wb_right (by pomega)
  have hR₃ : ∀ r, 800 ≤ r → r < 900 → c₃.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₃ r (by pomega) (by pomega)).trans (hR₂ r h1 h2)
  have hrm₃' : c₃.rmem = c.rmem := by rw [hrm₃, hrm₂, hrm₁]
  have hPL : PLay b w (Z + 7 * M₀) (Z + 6 * M₀) δb (Z + 8 * M₀) 1 W' (fun i => ν (β i)) :=
    pLay_slot HS hδb hnlt hninj
  have hPI : PIn b w (Z + 7 * M₀) (Z + 6 * M₀) δb (Z + 8 * M₀) 1 (fun i => ν (β i))
      (fun i => (E (β i) : ℝ)) (fun v => (δ (ι v) : ℝ)) (Cz : ℝ) c₃ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, p508, ?_, fun i hi => ?_, fun i hi => ?_, fun v hv => ?_⟩
    · rw [p500, hR₂ 802 (by pomega) (by pomega), hctx.r802]
    · rw [p501, sl 7 (by pomega) c₂ hR₂]
    · rw [p502, sl 6 (by pomega) c₂ hR₂]
    · rw [p505, hR₂ 801 (by pomega) (by pomega), hctx.r801]
    · rw [p506, hR₂ 831 (by pomega) (by pomega), h831]
    · rw [p507, sl 8 (by pomega) c₂ hR₂]
    · rw [pC, sl 21 (by pomega) c₂ hR₂, hrm₂, hrm₁, hCm]
    · rw [hnm₃, hm₂ _ (by pomega)]; exact hNm i hi
    · rw [hrm₃']; exact hEm i hi
    · rw [hrm₃']; exact hDm v hv
  obtain ⟨c₄, k₄, e₄, hk₄, q1, q2, q3, q4, hrm₄, hnm₄, hn₄, ho₄⟩ :=
    pProg_exec (P := I) hPL c₃ e₃.wb_right hPI
  have hR₄ : ∀ r, 800 ≤ r → r < 900 → c₄.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₄ r (by pomega)).trans (hR₃ r h1 h2)
  -- 5., 6. the candidate arcs
  obtain ⟨c₅, k₅, e₅, hk₅, a700, a701, a702, a703, a704, a705, a706, a707, a708, a709, a710,
    a711, hn₅, hrr₅, hnm₅, hrm₅, ho₅⟩ := aSet_exec (P := I) c₄ e₄.wb_right
  have hR₅ : ∀ r, 800 ≤ r → r < 900 → c₅.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₅ r (by pomega)).trans (hR₄ r h1 h2)
  have hAL : ALay m w s (Z + 0 * M₀) (Z + 1 * M₀) (Z + 2 * M₀) (Z + 3 * M₀) (Z + 8 * M₀)
      (Z + 9 * M₀) (Z + 10 * M₀) (Z + 11 * M₀) (Z + 12 * M₀) W' (encT N e ν) (encH N e ν)
      (encS P₀ e) := aLay_slot HS hends hs
  have hm₄ : ∀ a, Z ≤ a → c₄.nmem a = c.nmem a := fun a ha => by
    rw [hnm₄, hnm₃, hm₂ a (by pomega)]
  have hAI : AIn m w s (Z + 0 * M₀) (Z + 1 * M₀) (Z + 2 * M₀) (Z + 3 * M₀) (Z + 8 * M₀)
      (Z + 9 * M₀) (Z + 10 * M₀) (Z + 11 * M₀) (Z + 12 * M₀) (encT N e ν) (encH N e ν)
      (encS P₀ e) (fun d => (ℓ (e d) : ℝ)) (fun v => c₄.rmem (Z + 8 * M₀ + v)) c₅ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun d hd => ?_, fun d hd => ?_,
      fun d hd => ?_, fun d hd => ?_, fun v hv => ?_⟩
    · rw [a700, hR₄ 800 (by pomega) (by pomega), hctx.r800]
    · rw [a701, hR₄ 801 (by pomega) (by pomega), hctx.r801]
    · rw [a702, sl 0 (by pomega) c₄ hR₄]
    · rw [a703, sl 1 (by pomega) c₄ hR₄]
    · rw [a704, sl 2 (by pomega) c₄ hR₄]
    · rw [a705, sl 3 (by pomega) c₄ hR₄]
    · rw [a706, sl 8 (by pomega) c₄ hR₄]
    · rw [a707, sl 9 (by pomega) c₄ hR₄]
    · rw [a708, sl 10 (by pomega) c₄ hR₄]
    · rw [a709, sl 11 (by pomega) c₄ hR₄]
    · rw [a710, sl 12 (by pomega) c₄ hR₄]
    · rw [a711, hR₄ 830 (by pomega) (by pomega), h830]
    · rw [hnm₅, hm₄ _ (by pomega)]; exact hTm d hd
    · rw [hnm₅, hm₄ _ (by pomega)]; exact hHm d hd
    · rw [hnm₅, hm₄ _ (by pomega)]; exact hSm d hd
    · rw [hrm₅, hrm₄ _ (Or.inl (by pomega)) (Or.inr (by pomega)), hrm₃']; exact hLm d hd
    · rw [hrm₅]
  obtain ⟨c₆, k₆, e₆, hk₆, hd₆, hv₆, hnm₆, hrm₆, hn₆, hrr₆, ho₆⟩ :=
    aProg_exec (P := I) hAL c₅ e₅.wb_right hAI
  have hR₆ : ∀ r, 800 ≤ r → r < 900 → c₆.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₆ r (by pomega)).trans (hR₅ r h1 h2)
  -- the candidate arcs as written
  have hd₆' : ∀ i < m, c₆.nmem (Z + 9 * M₀ + i) = encT N e ν i + 1 ∧
      c₆.nmem (Z + 10 * M₀ + i) = encH N e ν i + 1 ∧
      (c₆.nmem (Z + 11 * M₀ + i) ≠ 0 ↔ encS P₀ e i = s) := fun i hi =>
    ⟨(hd₆ i hi).1, (hd₆ i hi).2.1, by rw [(hd₆ i hi).2.2.1]; exact flag_ne_zero (hends i hi).2.2 hs⟩
  obtain ⟨hEs, hEs', hhd⟩ := arcs_part h hs ℓ (bdry N P₀ P₁) (fun y => E y - Cz) δ
    (fun i => c₆.nmem (Z + 9 * M₀ + i)) (fun i => c₆.nmem (Z + 10 * M₀ + i))
    (fun i => c₆.nmem (Z + 11 * M₀ + i)) hd₆' (fun v hv => ⟨(hv₆ v hv).1, (hv₆ v hv).2.1,
      (hv₆ v hv).2.2.1⟩)
  have htl : ∀ i < m + w, c₆.nmem (Z + 9 * M₀ + i) < w + 1 := by
    intro i hi
    by_cases him : i < m
    · rw [(hd₆ i him).1]; have := (hends i him).1; pomega
    · obtain ⟨v, rfl⟩ : ∃ v, i = m + v := ⟨i - m, by pomega⟩
      rw [(hv₆ v (by pomega)).1]; pomega
  -- the lengths of the candidate arcs
  have hlz : ∀ i < m + w, c₆.rmem (Z + 12 * M₀ + i) =
      (lzF N P₀ P₁ m e ν ι ℓ (bdry N P₀ P₁) (fun y => E y - Cz) δ i : ℝ) := by
    intro i hi
    by_cases him : i < m
    · rw [(hd₆ i him).2.2.2]; unfold lzF; rw [ite_eq_left_of_eq_true _ _ (eq_true him)]
    · obtain ⟨v, rfl⟩ : ∃ v, i = m + v := ⟨i - m, by pomega⟩
      rw [(hv₆ v (by pomega)).2.2.2]
      refine lzF_init h hβ ℓ E δ Cz (fun v => c₄.rmem (Z + 8 * M₀ + v)) (fun j hj => ?_)
        (fun v hv hv' => q2 v hv hv') (by pomega)
      rw [q1 j hj]
  -- 7., 8. the counting sort
  obtain ⟨c₇, k₇, e₇, hk₇, s400, s401, s402, s403, s404, s405, s406, s407, s408, s409, hn₇, hrr₇,
    hnm₇, hrm₇, ho₇⟩ := csSet_exec (P := I) c₆ e₆.wb_right
      (by rw [hR₆ 800 (by pomega) (by pomega), hR₆ 801 (by pomega) (by pomega), hctx.r800,
        hctx.r801]; pomega)
      (by rw [hR₆ 801 (by pomega) (by pomega), hctx.r801]; pomega)
  have hR₇ : ∀ r, 800 ≤ r → r < 900 → c₇.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₇ r (by pomega) (by pomega)).trans (hR₆ r h1 h2)
  have e801₆ : c₆.nreg 801 = w := by rw [hR₆ 801 (by pomega) (by pomega), hctx.r801]
  have hCL : CsLay (m + w) (w + 1) (Z + 9 * M₀) (Z + 10 * M₀) (Z + 11 * M₀) (w + 2)
      (Z + 13 * M₀) (Z + 15 * M₀) (Z + 12 * M₀) (Z + 14 * M₀) W'
      (fun i => c₆.nmem (Z + 9 * M₀ + i)) (fun i => c₆.nmem (Z + 10 * M₀ + i))
      (fun i => c₆.nmem (Z + 11 * M₀ + i)) := csLay_slot HS fun i hi _ => htl i hi
  have hCI : CsIn (m + w) (w + 1) (Z + 9 * M₀) (Z + 10 * M₀) (Z + 11 * M₀) (w + 2)
      (Z + 13 * M₀) (Z + 15 * M₀) (Z + 12 * M₀) (Z + 14 * M₀)
      (fun i => c₆.nmem (Z + 9 * M₀ + i)) (fun i => c₆.nmem (Z + 10 * M₀ + i))
      (fun i => c₆.nmem (Z + 11 * M₀ + i))
      (lzF N P₀ P₁ m e ν ι ℓ (bdry N P₀ P₁) (fun y => E y - Cz) δ) c₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i _ => by rw [hnm₇],
      fun i _ => by rw [hnm₇], fun i _ => by rw [hnm₇], fun i hi => by rw [hrm₇]; exact hlz i hi⟩
    · rw [s400, hR₆ 800 (by pomega) (by pomega), hctx.r800, e801₆]
    · rw [s401, e801₆]
    · rw [s402, sl 9 (by pomega) c₆ hR₆]
    · rw [s403, sl 10 (by pomega) c₆ hR₆]
    · rw [s404, sl 11 (by pomega) c₆ hR₆]
    · rw [s405, e801₆]
    · rw [s406, sl 13 (by pomega) c₆ hR₆]
    · rw [s407, sl 15 (by pomega) c₆ hR₆]
    · rw [s408, sl 12 (by pomega) c₆ hR₆]
    · rw [s409, sl 14 (by pomega) c₆ hR₆]
  obtain ⟨c₈, k₈, e₈, hk₈, hoff₈, harc₈, hnm₈, hrm₈, hn₈, hrr₈, ho₈⟩ :=
    csProg_exec (P := I) hCL c₇ e₇.wb_right hCI
  have hR₈ : ∀ r, 800 ≤ r → r < 900 → c₈.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₈ r (by pomega)).trans (hR₇ r h1 h2)
  generalize hEsdef : csList (fun i => c₆.nmem (Z + 9 * M₀ + i))
    (fun i => c₆.nmem (Z + 10 * M₀ + i)) (fun i => c₆.nmem (Z + 11 * M₀ + i))
    (lzF N P₀ P₁ m e ν ι ℓ (bdry N P₀ P₁) (fun y => E y - Cz) δ) (m + w) = Es
    at hEs hEs' hhd hoff₈ harc₈
  have hm'E : (arcList (w + 1) Es).length = Es.length := by
    rw [← hEsdef]; exact length_arcList_csList fun i hi _ => htl i hi
  have hEl : Es.length ≤ m + w := by rw [← hEsdef]; exact length_csList_le _
  generalize hm'def : (arcList (w + 1) Es).length = m' at harc₈ hm'E
  have hoffN : c₈.nmem (2 * w + 3) = m' := by
    have := hoff₈ (w + 1) le_rfl
    rw [show w + 2 + (w + 1) = 2 * w + 3 by pomega] at this
    rw [this, ← hm'def]; rfl
  -- 9., 10. the copy into the layout of `mkPrm`
  have e801₈ : c₈.nreg 801 = w := by rw [hR₈ 801 (by pomega) (by pomega), hctx.r801]
  obtain ⟨c₉, k₉, e₉, hk₉, t940, t941, t942, t943, t910, t911, t912, t913, t914, hn₉, hrr₉,
    hnm₉, hrm₉, ho₉⟩ := cpSet_exec (P := I) c₈ e₈.wb_right (by rw [e801₈, hoffN]; pomega)
  rw [e801₈, hoffN] at t942 t943 t910 t913
  rw [e801₈] at t940 t941 t911
  have hR₉ : ∀ r, 800 ≤ r → r < 900 → c₉.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₉ r h2).trans (hR₈ r h1 h2)
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, hcp, hnm₁₀, hrm₁₀, hn₁₀, hrr₁₀, ho₁₀⟩ :=
    cpyProg_exec (P := I) (n := m') (Dn := 2 * w + 4) (Sn := Z + 14 * M₀)
      (Dr := 2 * w + 4 + m') (Sr := Z + 15 * M₀)
      (cpyLay_slot HS (by pomega)) c₉ e₉.wb_right
      t910 t911 (by rw [t912, sl 14 (by pomega) c₈ hR₈]) t913
      (by rw [t914, sl 15 (by pomega) c₈ hR₈])
  have hR₁₀ : ∀ r, 800 ≤ r → r < 900 → c₁₀.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₁₀ r (by pomega)).trans (hR₉ r h1 h2)
  -- 11., 12. the registers of `frProg`
  obtain ⟨c₁₁, k₁₁, e₁₁, hk₁₁, hn₁₁, hrr₁₁, hnm₁₁, hrm₁₁, ho₁₁⟩ :=
    zeroRegs_exec (P := I) lowRegs c₁₀ e₁₀.wb_right
  have hk₁₁' : k₁₁ = 372 := by rw [hk₁₁, lowRegs, List.length_range]
  clear hk₁₁
  have hn₁₁' : ∀ r, 372 ≤ r → c₁₁.nreg r = c₁₀.nreg r := fun r hr => by
    rw [hn₁₁ r, ite_eq_right_of_eq_false _ _ (eq_false fun h' => by
      have := mem_lowRegs.1 h'; pomega)]
  have v940 : c₁₁.nreg 940 = w + 1 := by rw [hn₁₁' _ (by pomega), hn₁₀ _ (by pomega), t940]
  have v941 : c₁₁.nreg 941 = w + 2 := by rw [hn₁₁' _ (by pomega), hn₁₀ _ (by pomega), t941]
  have v942 : c₁₁.nreg 942 = m' := by rw [hn₁₁' _ (by pomega), hn₁₀ _ (by pomega), t942]
  have v943 : c₁₁.nreg 943 = 2 * w + 4 + m' := by
    rw [hn₁₁' _ (by pomega), hn₁₀ _ (by pomega), t943]
  have hR₁₁ : ∀ r, 800 ≤ r → r < 900 → c₁₁.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₁₁' r (by pomega)).trans (hR₁₀ r h1 h2)
  obtain ⟨c₁₂, k₁₂, e₁₂, hk₁₂, u944, u945, u946, u100, u101, u102, u103, u104, u105, u106, u107,
    u108, u109, hn₁₂, hnm₁₂, hrm0₁₂, hrm₁₂, ho₁₂⟩ := inpBlk_exec (P := I) c₁₁ e₁₁.wb_right
      (by rw [v940, v942, v943]; pomega) (by pomega)
  simp only [v943, v942, v940, v941] at u944 u945 u946 u107 u108 u109 u105 u100 u104
  have hR₁₂ : ∀ r, 800 ≤ r → r < 900 → c₁₂.nreg r = c.nreg r := fun r h1 h2 =>
    (hn₁₂ r (by pomega) (by pomega)).trans (hR₁₁ r h1 h2)
  -- 13. FR-Dijkstra
  set pf : ℕ → ℤ := fun x => if x = 0 then price (bdry N P₀ P₁) (fun y => E y - Cz) δ none
    else δ (ι (x - 1)) with hpf
  obtain ⟨hPW, hPlb, hPpb, hPob, hPsb, hPdb, hPwb⟩ := mkPrm_one (w + 1) (fun _ _ => 0) pf 0 Es
  rw [hm'def] at hPW hPlb hPsb hPdb hPwb
  have hPN : (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es).N = w + 1 := rfl
  have hPm : (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es).m = m' := hm'def
  have hin : Inp (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es) c₁₂ :=
    ⟨u100, u101, u102, by rw [u103, hPpb], by rw [u104, hPob], by rw [u105, hPlb]; pomega, u106,
      by rw [u107, hPsb]; pomega, by rw [u108, hPdb]; pomega, by rw [u109, hPwb]; pomega⟩
  have hrlow : ∀ a, a < 2 * w + 4 → c₁₂.rmem a = c₄.rmem a ∨ a = 0 := by
    intro a ha
    by_cases h0 : a = 0
    · exact Or.inr h0
    · left
      rw [hrm₁₂ a h0, hrm₁₁, hrm₁₀ a (Or.inl (by pomega)), hrm₉, hrm₈ a (Or.inl (by pomega)), hrm₇,
        hrm₆ a (Or.inl (by pomega)), hrm₅]
  have hDa : Data (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es) c₁₂ := by
    refine ⟨fun i j hi hj => ?_, fun x hx => ?_, fun x hx => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · have hb1 : (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es).b = 1 := rfl
      obtain rfl : i = 0 := by pomega
      obtain rfl : j = 0 := by pomega
      show c₁₂.rmem (0 + 0 * 1 + 0) = ((0 : ℤ) : ℝ)
      simp [hrm0₁₂]
    · rw [hPN] at hx
      rw [hPpb]
      rcases hrlow (1 + x) (by pomega) with h' | h'
      · rw [h']
        show c₄.rmem (1 + x) = ((pf x : ℤ) : ℝ)
        rcases Nat.eq_zero_or_pos x with rfl | hx0
        · rw [Nat.add_zero, q4]
          simp only [hpf, ↓reduceIte]
          rw [← (arith_node h hβ E δ δ δ Cz (fun v => c₄.rmem (Z + 8 * M₀ + v))
            (fun j hj => by rw [q1 j hj]) (fun v hv hv' => q2 v hv hv')).2.1]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [h.inv _ (bdry_sub_verts (hβ.mem i (Finset.mem_range.1 hi)))]
        · obtain ⟨v, rfl⟩ : ∃ v, x = v + 1 := ⟨x - 1, by pomega⟩
          rw [q3 v (by pomega)]
          simp only [hpf, Nat.add_sub_cancel, Nat.add_one_ne_zero, ↓reduceIte]
      · pomega
    · rw [hPob]
      rw [hnm₁₂, hnm₁₁, hnm₁₀ _ (Or.inl (by pomega)), hnm₉,
        show w + 1 + 1 + x = w + 2 + x by pomega]
      exact hoff₈ x hx
    · rw [hPm] at ht
      rw [hPob, hPN]
      rw [hnm₁₂, hnm₁₁, show w + 1 + 1 + (w + 1) + 1 + t = 2 * w + 4 + t by pomega,
        (hcp t ht).1, hnm₉, (harc₈ t ht).1]
      rfl
    · rw [hPm] at ht
      rw [hPlb, hrm₁₂ _ (by pomega), hrm₁₁, show 2 * (w + 1) + 2 + m' + t = 2 * w + 4 + m' + t by pomega,
        (hcp t ht).2, hrm₉, (harc₈ t ht).2]
      rfl
  have hrb : ∀ r < 372, c₁₂.nreg r ≤ (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es).W := by
    intro r hr
    by_cases h1 : r < 100 ∨ 109 < r
    · rw [hn₁₂ r h1 (by pomega), hn₁₁ r, ite_eq_left_of_eq_true _ _ (eq_true (mem_lowRegs.2 hr))]
      pomega
    · rw [hPW]
      obtain ⟨h1, h2⟩ : 100 ≤ r ∧ r ≤ 109 := by pomega
      interval_cases r <;> simp only [u100, u101, u102, u103, u104, u105, u106, u107, u108, u109] <;>
        pomega
  have hmb : ∀ a ≤ (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es).W,
      c₁₂.nmem a ≤ (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es).W := by
    intro a ha
    rw [hPW] at ha ⊢
    rw [hnm₁₂, hnm₁₁]
    by_cases hD : 2 * w + 4 ≤ a ∧ a < 2 * w + 4 + m'
    · obtain ⟨t, rfl⟩ : ∃ t, a = 2 * w + 4 + t := ⟨a - (2 * w + 4), by pomega⟩
      have ht : t < m' := by pomega
      rw [(hcp t ht).1, hnm₉, (harc₈ t ht).1]
      have hmem : (arcList (w + 1) Es).getD t (0, 0, 0) ∈ Es := by
        have ht' : t < (arcList (w + 1) Es).length := by rw [hm'def]; exact ht
        rw [List.getD_eq_getElem _ _ ht']
        exact (mem_arcList.1 (List.getElem_mem ht')).1
      have := hhd _ hmem
      pomega
    · rw [hnm₁₀ a (by pomega), hnm₉]
      by_cases hO : w + 2 ≤ a ∧ a < w + 2 + (w + 1) + 1
      · obtain ⟨x, rfl⟩ : ∃ x, a = w + 2 + x := ⟨a - (w + 2), by pomega⟩
        rw [hoff₈ x (by pomega)]
        have := length_pre_le Es x
        pomega
      · rw [hnm₈ a (by pomega) (Or.inl (by pomega)) (Or.inl (by pomega)), hnm₇,
          hnm₆ a (Or.inl (by pomega)) (Or.inl (by pomega)) (Or.inl (by pomega)), hnm₅, hnm₄, hnm₃,
          z₂ a (by pomega)]
        pomega
  have hX : partOf P₀ P₁ s ⊆ P₀ ∪ P₁ := by
    unfold partOf; split_ifs
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  -- the actual run
  have hDp : partProg.noDivR = true := by decide +kernel
  have hZ' : IntAll c' := Exec.intAll ex hDp hZi
  simp only [partProg, Stmt.noDivR, Bool.and_eq_true] at hDp
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15⟩ := hDp
  unfold partProg at ex
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
  obtain ⟨_, _, _, x₇, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₇ x₇
  obtain ⟨_, _, _, x₈, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₈ x₈
  obtain ⟨_, _, _, x₉, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₉ x₉
  obtain ⟨_, _, _, x₁₀, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₁₀ x₁₀
  obtain ⟨_, _, _, x₁₁, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₁₁ x₁₁
  obtain ⟨_, _, _, x₁₂, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₁₂ x₁₂
  obtain ⟨c₁₃, _, _, x₁₃, ex⟩ := seq_parts ex
  obtain ⟨c₁₄, _, _, x₁₄, x₁₅⟩ := seq_parts ex
  -- the bounds
  obtain ⟨hB1, hB2⟩ := partB_le (b := b) (w := w) (B := B)
  have h500 : c₃.nreg 500 = b := by rw [p500, hR₂ 802 (by pomega) (by pomega), hctx.r802]
  set B₃ := (2 * b + 3) * ((b + 1) * B) with hB₃
  have G₁ := good_glue (H := 64 * partB b w B) clrSet_glueOK d1 e₁ hI hZi (by omega)
  have G₂ := good_glue (H := 64 * partB b w B) clrProg_glueOK d2 e₂ G₁.2.1 G₁.2.2 (by omega)
  have G₃ := good_glue (H := 64 * partB b w B) pSet_glueOK d3 e₃ G₂.2.1 G₂.2.2 (by omega)
  have G₄ : NGood I W' (64 * partB b w B) B₃ pProg c₃ c₄ := by
    obtain ⟨C, hI'⟩ := pProg_cmp e₄ G₃.2.1 G₃.2.2
    rw [h500] at C hI'
    exact ⟨⟨_, C.mono_H (by omega)⟩, hI', Exec.intAll e₄ d4 G₃.2.2⟩
  have G₅ := good_glue (H := 64 * partB b w B) aSet_glueOK d5 e₅ G₄.2.1 G₄.2.2 (by omega)
  have G₆ := good_glue (H := 64 * partB b w B) aProg_glueOK d6 e₆ G₅.2.1 G₅.2.2 (by omega)
  have G₇ := good_glue (H := 64 * partB b w B) csSet_glueOK d7 e₇ G₆.2.1 G₆.2.2 (by omega)
  have G₈ := good_glue (H := 64 * partB b w B) csProg_glueOK d8 e₈ G₇.2.1 G₇.2.2 (by omega)
  have G₉ := good_glue (H := 64 * partB b w B) cpSet_glueOK d9 e₉ G₈.2.1 G₈.2.2 (by omega)
  have G₁₀ := good_glue (H := 64 * partB b w B) cpyProg_glueOK d10 e₁₀ G₉.2.1 G₉.2.2 (by omega)
  have G₁₁ := good_glue (H := 64 * partB b w B) lowRegs_glueOK d11 e₁₁ G₁₀.2.1 G₁₀.2.2 (by omega)
  have G₁₂ := good_glue (H := 64 * partB b w B) inpBlk_glueOK d12 e₁₂ G₁₁.2.1 G₁₁.2.2 (by omega)
  -- 13. FR-Dijkstra
  have hBB : BB (mkPrm (w + 1) 1 (fun _ _ => 0) pf 0 Es) B₃ = partB b w B := by
    show (w + 1 + 2) * B₃ = (w + 3) * B₃; rfl
  have G₁₃ : NGood I W' (64 * partB b w B) (partB b w B) frProg c₁₂ c₁₃ := by
    obtain ⟨C, hI'⟩ := dijk_cmp_emb h hX ℓ (bdry N P₀ P₁) (fun y => E y - Cz) δ hδ Es hEs
      (fun _ _ => 0) pf (by simp [hpf]) (fun x hx => by simp [hpf, h.inv x hx]) I
      (by rw [hPW]; pomega) c₁₂ e₁₂.wb_right hin hDa hrb hmb G₁₂.2.1 x₁₃
    rw [hBB] at C hI'
    exact ⟨⟨_, C.mono_H (by omega)⟩, hI', Exec.intAll x₁₃ d13 G₁₂.2.2⟩
  have G₁₄ := good_glue (H := 64 * partB b w B) nSet_glueOK d14 x₁₄ G₁₃.2.1 G₁₃.2.2 (by omega)
  have G₁₅ := good_glue (H := 64 * partB b w B) nrmProg_glueOK d15 x₁₅ G₁₄.2.1 G₁₄.2.2 (by omega)
  exact G₁.seq (G₂.seq (G₃.seq (G₄.seq (G₅.seq (G₆.seq (G₇.seq (G₈.seq (G₉.seq (G₁₀.seq
    (G₁₁.seq (G₁₂.seq (G₁₃.seq (G₁₄.seq G₁₅)))))))))))))

end Node

end NegSSSP

end PlanarFlow
