module

public import PlanarFlow.BKMNW.LevelPrep
public import Mathlib.Data.List.GetD

/-!
# One level of `scertD` on the machine

One level of the certificate recursion (`scStep` / `scBase` of `ScertLoop.lean`) for the choices
`scChoiceE`, on the per-index arrays of the piece at the fixed layout of base `b`
(`NF | TH | RV0 | EX | GN | RV | TK | YF | LS | OFF | ADJ | LAB | Q | TG | TG2 | VAL | SUM | NF2`,
`b + 20 n + 3` words) and the record base `IXb` above:

1. the hole loop `hlProg` (the first cut-vertex hole, or `NoCut`: kind `0`);
2. on the chosen hole: its labels (`phCC`), the arrays `lpProg`, the component weights
   (`saProg`), the heavy scan `hvScan`;
3. no heavy component: the anchor of the cut (`acScan` on `TG2`; kind `2`);
4. else the anchor of the heavy component (`acScan` on `TG`, `LAB`, `LAB[z]`); none: kind `3`;
   else the prune update `kpScan` (kept flags `NF2`, the pruned indices at `IXb`); none pruned:
   kind `3`; else kind `1`: `EX[a₀] += Σ_N (1 + ex) − Σ_K (1 + ex)`, `NF := NF2` (`cpArr`).

* `cpArr` (copy loop), `cpArr_exec`;
* `LvRegs` (the fixed registers of the level), `LvFr` (the registers no part writes),
  `LvRegs.of_frame`;
* pure: `scStep_prune`, `scStep_none`, `scBase_cut`, …;
* **`lvProg`**, **`lvProg_exec`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### A copy loop -/

/-- `DST[i] := SRC[i]` for `i < r4910` (`4911 = SRCb`, `4912 = DSTb`; written `4913 … 4916`). -/
def cpBody : Stmt :=
  block [.addN 4916 4911 4914, .loadN 4915 4916, .addN 4916 4912 4914, .storeN 4916 4915,
    .addN 4914 4914 4913]

/-- **The copy loop.** -/
def cpArr : Stmt := .seq (block [.constN 4913 1, .constN 4914 0]) (.whileLtN 4914 4910 cpBody)

section Copy

variable {P : Input} {W : ℕ}

theorem cpBody_exec (c : Config) (hc : WordsBounded W c) {Sb Db i : ℕ}
    (r1 : c.nreg 4911 = Sb) (r2 : c.nreg 4912 = Db) (r3 : c.nreg 4913 = 1) (r4 : c.nreg 4914 = i)
    (w1 : Sb + i ≤ W) (w2 : Db + i ≤ W) (w3 : i + 1 ≤ W) :
    ∃ c' t, Exec P W cpBody c c' t ∧ t = 5 ∧ c'.nreg 4914 = i + 1 ∧
      c'.nmem = upd c.nmem (Db + i) (c.nmem (Sb + i)) ∧
      (∀ x, (x < 4914 ∨ 4916 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cpBody
  exec_block
  all_goals try (config_simp; (try simp only [r1, r2, r3, r4]); omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r3, r4]
  · config_simp; simp only [r1, r2, r3, r4]
  · obtain ⟨a1, a2, a3⟩ : x ≠ 4914 ∧ x ≠ 4915 ∧ x ≠ 4916 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3]

/-- **The copy loop on the machine**: within `7 n + 4` steps `DST[i] = SRC[i]` (`i < n`, the
arrays disjoint), memory outside `DST`, registers outside `4913 … 4916` kept. -/
theorem cpArr_exec (c : Config) (hc : WordsBounded W c) {n Sb Db : ℕ}
    (r0 : c.nreg 4910 = n) (r1 : c.nreg 4911 = Sb) (r2 : c.nreg 4912 = Db)
    (lay : (Sb + n ≤ Db ∨ Db + n ≤ Sb) ∧ Sb + n ≤ W ∧ Db + n ≤ W ∧ n + 1 ≤ W) :
    ∃ c' t, Exec P W cpArr c c' t ∧ t ≤ 7 * n + 4 ∧
      (∀ i < n, c'.nmem (Db + i) = c.nmem (Sb + i)) ∧
      (∀ a, (a < Db ∨ Db + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4913 ∨ 4916 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4⟩ := lay
  unfold cpArr
  obtain ⟨c₁, k₁, e₁, hk₁, g3, g4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4913 1, .constN 4914 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 4913 = 1 ∧ c₁.nreg 4914 = 0 ∧
      (∀ x, x ≠ 4913 → x ≠ 4914 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, by config_simp, by config_simp, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    simp only [Config.nreg_mk, upd_other _ _ _ h1, upd_other _ _ _ h2]
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 4913 ∨ 4916 < x) → c₁.nreg x = c.nreg x := fun x hx =>
    gn₁ x (by omega) (by omega)
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4914 ∨ 4916 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (Db + j) = m₀ (Sb + j)) ∧
    (∀ a, ¬ (Db ≤ a ∧ a < Db + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h14, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 4914) (b := 4910) (body := cpBody) J (B := 5) c₁ hw₁ g4
    (by rw [q _ (by omega), r0]) (Nat.zero_le n)
    ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega), fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h14 h10 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 4914 ∨ 4916 < x) → c'.nreg x = c₁.nreg x := j1
      have e1 : c'.nmem (Sb + i) = m₀ (Sb + i) := j3 _ (by omega)
      obtain ⟨c'', t, ex, ht, h14', hm', hn', hr', hrm', ho'⟩ :=
        cpBody_exec (P := P) c' hw (by rw [f _ (by omega), q _ (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega), r2]) (by rw [f _ (by omega), g3]) h14
        (by omega) (by omega) (by omega)
      rw [e1] at hm'
      refine ⟨c'', t, ex, ht.le, h14', by rw [hn' _ (by omega)]; exact h10,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (by omega)]; exact j3 a (by omega))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, fun a ha => j3 a (by omega),
    fun x hx => by rw [j1 x (by omega), q x hx], by rw [j4, gr₁], by rw [j5, grm₁],
    by rw [j6, go₁]⟩

end Copy

/-! ### The fixed registers of a level -/

/-- **The fixed registers of a level** for the layout of base `b` (`n` indices, `nH` holes, the
weight bounds `A`, `W₀` of the heavy test). -/
structure LvRegs (c : Config) (n b nH A W₀ : ℕ) : Prop where
  p0 : c.nreg 4840 = n
  p1 : c.nreg 4841 = b
  p2 : c.nreg 4842 = b + n
  p3 : c.nreg 4843 = b + 2 * n
  p6 : c.nreg 4846 = b + 7 * n
  p7 : c.nreg 4847 = b + 4 * n
  p8 : c.nreg 4848 = b + 5 * n
  p9 : c.nreg 4849 = b + 13 * n + 1
  p10 : c.nreg 4866 = b + 8 * n
  r0 : c.nreg 4420 = n
  r1 : c.nreg 4421 = b + 5 * n
  r2 : c.nreg 4422 = b + 6 * n
  r3 : c.nreg 4423 = b + 7 * n
  r4 : c.nreg 4424 = b + 8 * n
  r5 : c.nreg 4425 = b + 9 * n
  r6 : c.nreg 4426 = b + 10 * n + 1
  s0 : c.nreg 4400 = n
  s1 : c.nreg 4401 = b + 9 * n
  s2 : c.nreg 4402 = b + 10 * n + 1
  s3 : c.nreg 4403 = b + 13 * n + 1
  s4 : c.nreg 4404 = b + 14 * n + 1
  u0 : c.nreg 4760 = n
  u1 : c.nreg 4761 = b + 4 * n
  u2 : c.nreg 4762 = b + 13 * n + 1
  v4 : c.nreg 4874 = nH
  l0 : c.nreg 4880 = n
  l1 : c.nreg 4881 = b
  l2 : c.nreg 4882 = b + n
  l3 : c.nreg 4883 = b + 3 * n
  l5 : c.nreg 4885 = b + 15 * n + 2
  l6 : c.nreg 4886 = b + 16 * n + 2
  l7 : c.nreg 4887 = b + 17 * n + 2
  l8 : c.nreg 4888 = b + 18 * n + 2
  a0 : c.nreg 4630 = n
  a1 : c.nreg 4631 = b + 13 * n + 1
  a2 : c.nreg 4632 = b + 17 * n + 2
  a3 : c.nreg 4633 = 1
  a4 : c.nreg 4634 = b + 18 * n + 2
  h0 : c.nreg 4780 = n
  h1 : c.nreg 4781 = b
  h2 : c.nreg 4782 = b + 13 * n + 1
  h3 : c.nreg 4783 = b + 18 * n + 2
  h4 : c.nreg 4784 = A
  h5 : c.nreg 4785 = W₀
  c0 : c.nreg 4800 = n
  k0 : c.nreg 4820 = n
  k1 : c.nreg 4821 = b
  k2 : c.nreg 4822 = b + 13 * n + 1
  k4 : c.nreg 4824 = b + 19 * n + 3
  y0 : c.nreg 4910 = n
  y1 : c.nreg 4911 = b + 19 * n + 3
  y2 : c.nreg 4912 = b

/-- The registers written by no part of a level. -/
def LvFr (x : ℕ) : Prop :=
  x < 4405 ∨ (4416 < x ∧ x < 4427) ∨ (4436 < x ∧ x < 4635) ∨ (4639 < x ∧ x < 4763) ∨
    (4771 < x ∧ x < 4786) ∨ (4793 < x ∧ x < 4801) ∨ (4811 < x ∧ x < 4823) ∨ x = 4824 ∨
    (4832 < x ∧ x < 4845) ∨ (4845 < x ∧ x < 4853) ∨ (4865 < x ∧ x < 4870) ∨ x = 4874 ∨
    (4875 < x ∧ x < 4884) ∨ (4884 < x ∧ x < 4889) ∨ (4896 < x ∧ x < 4900) ∨
    (4909 < x ∧ x < 4913) ∨ 4920 < x

theorem LvRegs.of_frame {c c' : Config} {n b nH A W₀ : ℕ} (h : LvRegs c n b nH A W₀)
    (hf : ∀ x, LvFr x → c'.nreg x = c.nreg x) : LvRegs c' n b nH A W₀ := by
  have f : ∀ x, LvFr x → c'.nreg x = c.nreg x := hf
  obtain ⟨p0, p1, p2, p3, p6, p7, p8, p9, p10, r0, r1, r2, r3, r4, r5, r6, s0, s1, s2, s3, s4,
    u0, u1, u2, v4, l0, l1, l2, l3, l5, l6, l7, l8, a0, a1, a2, a3, a4, h0, h1, h2, h3, h4, h5,
    c0, k0, k1, k2, k4, y0, y1, y2⟩ := h
  exact ⟨by rw [f _ (by unfold LvFr; omega), p0], by rw [f _ (by unfold LvFr; omega), p1],
    by rw [f _ (by unfold LvFr; omega), p2], by rw [f _ (by unfold LvFr; omega), p3],
    by rw [f _ (by unfold LvFr; omega), p6], by rw [f _ (by unfold LvFr; omega), p7],
    by rw [f _ (by unfold LvFr; omega), p8], by rw [f _ (by unfold LvFr; omega), p9],
    by rw [f _ (by unfold LvFr; omega), p10], by rw [f _ (by unfold LvFr; omega), r0],
    by rw [f _ (by unfold LvFr; omega), r1], by rw [f _ (by unfold LvFr; omega), r2],
    by rw [f _ (by unfold LvFr; omega), r3], by rw [f _ (by unfold LvFr; omega), r4],
    by rw [f _ (by unfold LvFr; omega), r5], by rw [f _ (by unfold LvFr; omega), r6],
    by rw [f _ (by unfold LvFr; omega), s0], by rw [f _ (by unfold LvFr; omega), s1],
    by rw [f _ (by unfold LvFr; omega), s2], by rw [f _ (by unfold LvFr; omega), s3],
    by rw [f _ (by unfold LvFr; omega), s4], by rw [f _ (by unfold LvFr; omega), u0],
    by rw [f _ (by unfold LvFr; omega), u1], by rw [f _ (by unfold LvFr; omega), u2],
    by rw [f _ (by unfold LvFr; omega), v4], by rw [f _ (by unfold LvFr; omega), l0],
    by rw [f _ (by unfold LvFr; omega), l1], by rw [f _ (by unfold LvFr; omega), l2],
    by rw [f _ (by unfold LvFr; omega), l3], by rw [f _ (by unfold LvFr; omega), l5],
    by rw [f _ (by unfold LvFr; omega), l6], by rw [f _ (by unfold LvFr; omega), l7],
    by rw [f _ (by unfold LvFr; omega), l8], by rw [f _ (by unfold LvFr; omega), a0],
    by rw [f _ (by unfold LvFr; omega), a1], by rw [f _ (by unfold LvFr; omega), a2],
    by rw [f _ (by unfold LvFr; omega), a3], by rw [f _ (by unfold LvFr; omega), a4],
    by rw [f _ (by unfold LvFr; omega), h0], by rw [f _ (by unfold LvFr; omega), h1],
    by rw [f _ (by unfold LvFr; omega), h2], by rw [f _ (by unfold LvFr; omega), h3],
    by rw [f _ (by unfold LvFr; omega), h4], by rw [f _ (by unfold LvFr; omega), h5],
    by rw [f _ (by unfold LvFr; omega), c0], by rw [f _ (by unfold LvFr; omega), k0],
    by rw [f _ (by unfold LvFr; omega), k1], by rw [f _ (by unfold LvFr; omega), k2],
    by rw [f _ (by unfold LvFr; omega), k4], by rw [f _ (by unfold LvFr; omega), y0],
    by rw [f _ (by unfold LvFr; omega), y1], by rw [f _ (by unfold LvFr; omega), y2]⟩

/-! ### The level, purely -/

section Pure

open Equiv Orbit

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The weights after a prune at the anchor `a₀`. -/
def exP (N K : Finset D) (ex : D → ℕ) (a₀ : D) : D → ℕ :=
  fun d => ex d + if d = a₀ then ∑ d ∈ N \ K, (1 + ex d) else 0

open Classical in
/-- **A prune level.** -/
theorem scStep_prune {ch : ScChoice M} {Hs : List (Finset V)} {N : Finset D} {τ : Perm D}
    {ex : D → ℕ} {g : Finset V} {z a₀ : D} (hnc : ¬ NoCut M N Hs) (hh : ch.hole N = some g)
    (hz : ch.heavy N g ex = some z) (ha : ch.anchor (comp M N Hs g z) g = some a₀)
    (hK : (comp M N Hs g z).card < N.card) :
    scStep ch Hs (N, τ, ex) = some ((comp M N Hs g z, ret τ (comp M N Hs g z),
      exP N (comp M N Hs g z) ex a₀), (N, comp M N Hs g z, a₀)) := by
  simp only [scStep, hnc, ↓reduceIte, hh, hz, ha, hK]
  rfl

open Classical in
lemma scStep_noCut {ch : ScChoice M} {Hs : List (Finset V)} {s : ScSt D} (h : NoCut M s.1 Hs) :
    scStep ch Hs s = none := by
  simp only [scStep, h, ↓reduceIte]

open Classical in
/-- No heavy component: no prune level, and the base is the cut at the hole. -/
theorem scStep_cut {ch : ScChoice M} {Hs : List (Finset V)} {N : Finset D} {τ : Perm D}
    {ex : D → ℕ} {g : Finset V} (hnc : ¬ NoCut M N Hs) (hh : ch.hole N = some g)
    (hz : ch.heavy N g ex = none) :
    scStep ch Hs (N, τ, ex) = none ∧ scBase ch Hs (N, τ, ex) =
      (ch.anchor N g).map fun a₁ => cutCert M Hs N g a₁ := by
  refine ⟨by simp only [scStep, hnc, ↓reduceIte, hh, hz], ?_⟩
  simp only [scBase, hnc, ↓reduceIte, hh, hz]
  cases ch.anchor N g <;> rfl

open Classical in
/-- A heavy component without an anchor: failure. -/
theorem scStep_noAnchor {ch : ScChoice M} {Hs : List (Finset V)} {N : Finset D} {τ : Perm D}
    {ex : D → ℕ} {g : Finset V} {z : D} (hnc : ¬ NoCut M N Hs) (hh : ch.hole N = some g)
    (hz : ch.heavy N g ex = some z) (ha : ch.anchor (comp M N Hs g z) g = none) :
    scStep ch Hs (N, τ, ex) = none ∧ scBase ch Hs (N, τ, ex) = none := by
  refine ⟨by simp only [scStep, hnc, ↓reduceIte, hh, hz, ha], ?_⟩
  simp only [scBase, hnc, ↓reduceIte, hh, hz]

open Classical in
/-- A heavy component that is all of `N`: failure. -/
theorem scStep_noShrink {ch : ScChoice M} {Hs : List (Finset V)} {N : Finset D} {τ : Perm D}
    {ex : D → ℕ} {g : Finset V} {z a₀ : D} (hnc : ¬ NoCut M N Hs) (hh : ch.hole N = some g)
    (hz : ch.heavy N g ex = some z) (ha : ch.anchor (comp M N Hs g z) g = some a₀)
    (hK : ¬ (comp M N Hs g z).card < N.card) :
    scStep ch Hs (N, τ, ex) = none ∧ scBase ch Hs (N, τ, ex) = none := by
  refine ⟨by simp only [scStep, hnc, ↓reduceIte, hh, hz, ha, hK], ?_⟩
  simp only [scBase, hnc, ↓reduceIte, hh, hz]

/-- The kept component is smaller iff some dart is pruned. -/
lemma comp_card_lt_iff {N : Finset D} {Hs : List (Finset V)} {g : Finset V} {z : D} :
    (comp M N Hs g z).card < N.card ↔ (N \ comp M N Hs g z).Nonempty := by
  have hsub : comp M N Hs g z ⊆ N := fun d hd => (mem_comp.1 hd).1
  constructor
  · intro h
    by_contra hne
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at hne
    have := card_le_card hne
    omega
  · intro ⟨d, hd⟩
    exact card_lt_card ⟨hsub, fun h => (mem_sdiff.1 hd).2 (h (mem_sdiff.1 hd).1)⟩

end Pure

/-! ### The programs of a level -/

/-- The weight update and kind `1` (`4807 = a₀`, `4891 = Σ_N`, `4903 = LZ`). -/
def lvUpd : Stmt :=
  block [.constN 4900 1, .copyN 4902 4807, .addN 4904 4883 4807, .loadN 4905 4904,
    .addN 4905 4905 4891, .addN 4906 4888 4903, .loadN 4906 4906, .subN 4905 4905 4906,
    .storeN 4904 4905]

/-- The prune update: `kpScan`, then failure (nothing pruned) or the weight update and the copy
`NF := NF2`. -/
def lvKeep : Stmt :=
  .seq (block [.copyN 4823 4903])
    (.seq kpScan (.ifLtN 4828 4873 (block [.constN 4900 3]) (.seq lvUpd cpArr)))

/-- A heavy component: `LZ := LAB[z]`, its anchor, then the prune update (failure without an
anchor). -/
def lvPrune : Stmt :=
  .seq (block [.addN 4904 4849 4789, .loadN 4903 4904, .copyN 4801 4885, .copyN 4802 4849,
      .copyN 4803 4903])
    (.seq acScan (.ifLtN 4806 4873 (block [.constN 4900 3]) lvKeep))

/-- No heavy component: the anchor of the cut (kind `2`, found flag `4901`, index `4902`). -/
def lvCutB : Stmt :=
  .seq (block [.copyN 4801 4886, .copyN 4802 4886, .copyN 4803 4873])
    (.seq acScan (block [.constN 4900 2, .copyN 4901 4806, .copyN 4902 4807]))

/-- The level at a cut-vertex hole `J = r4872`. -/
def lvCut : Stmt :=
  .seq (block [.addN 4845 4872 4873, .copyN 4884 4845])
    (.seq phCC (.seq lpProg (.seq saProg (.seq hvScan (.ifLtN 4788 4873 lvCutB lvPrune)))))

/-- **One level of `scertD`.** -/
def lvProg : Stmt :=
  .seq hlProg (.seq (block [.constN 4873 1]) (.ifLtN 4871 4873 (block [.constN 4900 0]) lvCut))

section Exec

variable {P : Input} {W : ℕ}

/-- **`kpScan_exec` with the exact memory frame** (only `NF2` and the first `n` words of `IX` are
written). -/
theorem kpScan_exec' (c : Config) (hc : WordsBounded W c) {n NFb LABb LZ NF2b IXb : ℕ}
    (r0 : c.nreg 4820 = n) (r1 : c.nreg 4821 = NFb) (r2 : c.nreg 4822 = LABb)
    (r3 : c.nreg 4823 = LZ) (r4 : c.nreg 4824 = NF2b) (r5 : c.nreg 4825 = IXb)
    (lay : NFb + n ≤ NF2b ∧ LABb + n ≤ NF2b ∧ NF2b + n ≤ IXb ∧ IXb + n + 1 ≤ W)
    (hlab : ∀ j < n, c.nmem (LABb + j) + LZ ≤ W) :
    ∃ c' t, Exec P W kpScan c c' t ∧ t ≤ 20 * n + 5 ∧
      c'.nreg 4828 = (kpL (fun j => kpP (c.nmem (NFb + j)) (c.nmem (LABb + j)) LZ) n).length ∧
      (∀ i < n, c'.nmem (NF2b + i) = kpK (c.nmem (NFb + i)) (c.nmem (LABb + i)) LZ) ∧
      (∀ k (hk : k < (kpL (fun j => kpP (c.nmem (NFb + j)) (c.nmem (LABb + j)) LZ) n).length),
        c'.nmem (IXb + k) = (kpL (fun j => kpP (c.nmem (NFb + j)) (c.nmem (LABb + j)) LZ) n)[k]) ∧
      (∀ a, ¬ (NF2b ≤ a ∧ a < NF2b + n) → ¬ (IXb ≤ a ∧ a < IXb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4826 ∨ 4832 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4⟩ := lay
  unfold kpScan
  obtain ⟨c₁, k₁, e₁, hk₁, g6, g7, g8, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4826 1, .constN 4827 0, .constN 4828 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 4826 = 1 ∧ c₁.nreg 4827 = 0 ∧ c₁.nreg 4828 = 0 ∧
      (∀ x, (x < 4826 ∨ 4828 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    obtain ⟨a1, a2, a3⟩ : x ≠ 4826 ∧ x ≠ 4827 ∧ x ≠ 4828 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3]
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 4826 ∨ 4828 < x) → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  set pp : ℕ → ℕ := fun j => kpP (m₀ (NFb + j)) (m₀ (LABb + j)) LZ with hpp
  have hp : ∀ i, pp i ≤ 1 := fun i => kpP_le _ _ _
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4827 ∨ 4832 < x) → c'.nreg x = c₁.nreg x) ∧
    c'.nreg 4828 = (kpL pp i).length ∧
    (∀ j < i, c'.nmem (NF2b + j) = kpK (m₀ (NFb + j)) (m₀ (LABb + j)) LZ) ∧
    (∀ k (hk : k < (kpL pp i).length), c'.nmem (IXb + k) = (kpL pp i)[k]) ∧
    (∀ a, ¬ (NF2b ≤ a ∧ a < NF2b + i) → ¬ (IXb ≤ a ∧ a < IXb + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h27, j1, j2, j3, j4, j5, j6, j7, j8⟩ := tgRange (P := P)
    (a := 4827) (b := 4820) (body := kpBody) J (B := 18) c₁ hw₁ g7
    (by rw [q _ (by omega), r0]) (Nat.zero_le n)
    ⟨fun _ _ => rfl, by rw [g8]; rfl, fun j hj => absurd hj (by omega),
      fun k hk => absurd hk (by simp [kpL]), fun a _ _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h27 h20 ⟨j1, j2, j3, j4, j5, j6, j7, j8⟩ => by
      have f : ∀ x, (x < 4827 ∨ 4832 < x) → c'.nreg x = c₁.nreg x := j1
      have hlen : (kpL pp i).length ≤ i := by rw [← kpC_eq hp]; exact kpC_le hp i
      have e1 : c'.nmem (NFb + i) = m₀ (NFb + i) := j5 _ (by omega) (by omega)
      have e2 : c'.nmem (LABb + i) = m₀ (LABb + i) := j5 _ (by omega) (by omega)
      obtain ⟨c'', t, ex, ht, h27', h28', hm', hn', hr', hrm', ho'⟩ :=
        kpBody_exec (P := P) c' hw (by rw [f _ (by omega), q _ (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega), r2]) (by rw [f _ (by omega), q _ (by omega), r3])
        (by rw [f _ (by omega), q _ (by omega), r4]) (by rw [f _ (by omega), q _ (by omega), r5])
        (by rw [f _ (by omega), g6]) h27 j2 e1 e2 hlen (by omega) (by omega) (hlab i hhi)
        (by omega) (by omega) (by omega)
      have hL := kpL_succ pp i
      refine ⟨c'', t, ex, ht.le, h27', by rw [hn' _ (by omega)]; exact h20,
        fun x hx => by rw [hn' x hx, f x hx], ?_, fun j hj => ?_, fun k hk => ?_,
        fun a ha hb => ?_, by rw [hr', j6], by rw [hrm', j7], by rw [ho', j8]⟩
      · rw [h28', hL, List.length_append]
        show (kpL pp i).length + pp i = _
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hp i) with h | h <;> simp [h]
      · rw [hm']
        rw [upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j3 j hj
        · rw [upd_same]
      · rw [hm']
        simp only [hL] at hk ⊢
        by_cases hkl : k < (kpL pp i).length
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), j4 k hkl,
            List.getElem_append_left hkl]
        · have hpi : pp i = 1 := by
            by_contra h0
            have : pp i = 0 := by have := hp i; omega
            simp [this] at hk; omega
          have hk' : k = (kpL pp i).length := by simp [hpi] at hk; omega
          subst hk'
          rw [upd_same, List.getElem_append_right (le_refl _)]
          simp [hpi]
      · rw [hm', upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        exact j5 a (by omega) (by omega))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, j4, fun a ha hb => j5 a (by omega) (by omega),
    fun x hx => by rw [j1 x (by omega), q x (by omega)], by rw [j6, gr₁], by rw [j7, grm₁],
    by rw [j8, go₁]⟩


theorem lvUpd_exec (c : Config) (hc : WordsBounded W c) {EXb SUMb a tot LZ : ℕ}
    (r1 : c.nreg 4883 = EXb) (r2 : c.nreg 4807 = a) (r3 : c.nreg 4891 = tot)
    (r4 : c.nreg 4888 = SUMb) (r5 : c.nreg 4903 = LZ)
    (w1 : EXb + a ≤ W) (w2 : SUMb + LZ ≤ W) (w3 : c.nmem (EXb + a) + tot ≤ W) (w4 : 1 ≤ W) :
    ∃ c' t, Exec P W lvUpd c c' t ∧ t = 9 ∧ c'.nreg 4900 = 1 ∧ c'.nreg 4902 = a ∧
      c'.nmem = upd c.nmem (EXb + a) (c.nmem (EXb + a) + tot - c.nmem (SUMb + LZ)) ∧
      (∀ x, x ≠ 4900 → x ≠ 4902 → x ≠ 4904 → x ≠ 4905 → x ≠ 4906 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lvUpd
  exec_block
  all_goals try (config_simp; (try simp only [r1, r2, r3, r4, r5]); omega)
  refine ⟨rfl, by config_simp, by config_simp; exact r2, by config_simp; simp only [r1, r2, r3, r4, r5],
    fun x h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl⟩
  simp only [Config.nreg_mk, upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3,
    upd_other _ _ _ h4, upd_other _ _ _ h5]

/-- The outcome of the prune update from the memory `m₀` (layout of base `b`, records at `IXb`):
nothing pruned (kind `3`), or kind `1` with the kept flags in `NF`, the weight update at `a`
and the pruned indices at `IXb`. -/
def KeepOut (m₀ : ℕ → ℕ) (c' : Config) (n b IXb LZ a tot : ℕ) : Prop :=
  ((kpL (fun j => kpP (m₀ (b + j)) (m₀ (b + 13 * n + 1 + j)) LZ) n).length = 0 ∧
      c'.nreg 4900 = 3 ∧
      ∀ a', ¬ (b + 19 * n + 3 ≤ a' ∧ a' < b + 20 * n + 3) → ¬ (IXb ≤ a' ∧ a' < IXb + n) →
        c'.nmem a' = m₀ a') ∨
  ((kpL (fun j => kpP (m₀ (b + j)) (m₀ (b + 13 * n + 1 + j)) LZ) n).length ≠ 0 ∧
    c'.nreg 4900 = 1 ∧ c'.nreg 4902 = a ∧
    c'.nreg 4828 = (kpL (fun j => kpP (m₀ (b + j)) (m₀ (b + 13 * n + 1 + j)) LZ) n).length ∧
    (∀ i < n, c'.nmem (b + i) = kpK (m₀ (b + i)) (m₀ (b + 13 * n + 1 + i)) LZ) ∧
    c'.nmem (b + 3 * n + a) = m₀ (b + 3 * n + a) + tot - m₀ (b + 18 * n + 2 + LZ) ∧
    (∀ k (hk : k < (kpL (fun j => kpP (m₀ (b + j)) (m₀ (b + 13 * n + 1 + j)) LZ) n).length),
      c'.nmem (IXb + k) = (kpL (fun j => kpP (m₀ (b + j)) (m₀ (b + 13 * n + 1 + j)) LZ) n)[k]) ∧
    ∀ a', ¬ (b ≤ a' ∧ a' < b + n) → a' ≠ b + 3 * n + a →
      ¬ (b + 19 * n + 3 ≤ a' ∧ a' < b + 20 * n + 3) → ¬ (IXb ≤ a' ∧ a' < IXb + n) →
        c'.nmem a' = m₀ a')

/-- **The prune update on the machine.** -/
theorem lvKeep_exec (c : Config) (hc : WordsBounded W c) {n b nH A W₀ IXb LZ a tot : ℕ}
    (hR : LvRegs c n b nH A W₀) (r25 : c.nreg 4825 = IXb) (r03 : c.nreg 4903 = LZ)
    (r07 : c.nreg 4807 = a) (r91 : c.nreg 4891 = tot) (r73 : c.nreg 4873 = 1) (ha : a < n)
    (hLZ : LZ ≤ n) (lay : b + 20 * n + 3 ≤ IXb ∧ IXb + n + 1 ≤ W)
    (hlab : ∀ j < n, c.nmem (b + 13 * n + 1 + j) ≤ n)
    (hw : c.nmem (b + 3 * n + a) + tot ≤ W) :
    ∃ c' t, Exec P W lvKeep c c' t ∧ t ≤ 27 * n + 22 ∧ KeepOut c.nmem c' n b IXb LZ a tot ∧
      (∀ x, LvFr x → c'.nreg x = c.nreg x) ∧ c'.nreg 4825 = IXb ∧ c'.nreg 4873 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2⟩ := lay
  have hn2 : 2 * n + 2 ≤ W := by omega
  obtain ⟨c₁, k₁, e₁, hk₁, g23, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 4823 4903]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 4823 = LZ ∧
      (∀ x, x ≠ 4823 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    refine ⟨rfl, by config_simp; exact r03, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    simp only [Config.nreg_mk, upd_other _ _ _ h1]
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, K1, K2, K3, K4, K5, K6, K7, K8⟩ := kpScan_exec' (P := P) c₁ hw₁
    (n := n) (NFb := b) (LABb := b + 13 * n + 1) (LZ := LZ) (NF2b := b + 19 * n + 3) (IXb := IXb)
    (by rw [gn₁ _ (by omega), hR.k0]) (by rw [gn₁ _ (by omega), hR.k1])
    (by rw [gn₁ _ (by omega), hR.k2]) g23 (by rw [gn₁ _ (by omega), hR.k4])
    (by rw [gn₁ _ (by omega), r25]) ⟨by omega, by omega, by omega, by omega⟩
    (fun j hj => by rw [gm₁]; have := hlab j hj; omega)
  rw [gm₁] at K1 K2 K3 K4
  have hw₂ := e₂.wb_right
  have f₂ : ∀ x, x ≠ 4823 → (x < 4826 ∨ 4832 < x) → c₂.nreg x = c.nreg x := fun x h hx => by
    rw [K5 x hx, gn₁ x h]
  have m₂ : ∀ a', ¬ (b + 19 * n + 3 ≤ a' ∧ a' < b + 20 * n + 3) → ¬ (IXb ≤ a' ∧ a' < IXb + n) →
      c₂.nmem a' = c.nmem a' := fun a' ha' hb' => by rw [K4 a' (by omega) hb']
  set L := kpL (fun j => kpP (c.nmem (b + j)) (c.nmem (b + 13 * n + 1 + j)) LZ) n with hL
  have t73 : c₂.nreg 4873 = 1 := by rw [f₂ _ (by omega) (by omega), r73]
  by_cases h0 : L.length = 0
  · have hlt : c₂.nreg 4828 < c₂.nreg 4873 := by rw [K1, t73]; omega
    obtain ⟨c₃, k₃, e₃, hk₃, b00, bn, bm, br, brm, bo⟩ : ∃ c₃ k₃,
        Exec P W (block [.constN 4900 3]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 4900 = 3 ∧
        (∀ x, x ≠ 4900 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
        c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
      exec_block
      all_goals try ((try config_simp); omega)
      refine ⟨rfl, by config_simp, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
      simp only [Config.nreg_mk, upd_other _ _ _ h1]
    refine ⟨c₃, k₁ + (k₂ + (k₃ + 1)), .seq e₁ (.seq e₂ (.ifLtN_true hlt e₃)), by omega,
      Or.inl ⟨h0, b00, fun a' ha' hb' => by rw [bm, m₂ a' ha' hb']⟩, fun x hx => ?_,
      by rw [bn _ (by omega), f₂ _ (by omega) (by omega), r25],
      by rw [bn _ (by omega), t73], by rw [br, K6, gr₁], by rw [brm, K7, grm₁],
      by rw [bo, K8, go₁]⟩
    unfold LvFr at hx
    rw [bn x (by omega), f₂ x (by omega) (by omega)]
  · have hnlt : ¬ c₂.nreg 4828 < c₂.nreg 4873 := by rw [K1, t73]; omega
    have e₀ : c₂.nmem (b + 3 * n + a) = c.nmem (b + 3 * n + a) := m₂ _ (by omega) (by omega)
    have e₁' : c₂.nmem (b + 18 * n + 2 + LZ) = c.nmem (b + 18 * n + 2 + LZ) :=
      m₂ _ (by omega) (by omega)
    obtain ⟨c₄, k₄, e₄, hk₄, U0, U2, Um, Un, Ur, Urm, Uo⟩ := lvUpd_exec (P := P) c₂ hw₂
      (EXb := b + 3 * n) (SUMb := b + 18 * n + 2) (a := a) (tot := tot) (LZ := LZ)
      (by rw [f₂ _ (by omega) (by omega), hR.l3]) (by rw [f₂ _ (by omega) (by omega), r07])
      (by rw [f₂ _ (by omega) (by omega), r91]) (by rw [f₂ _ (by omega) (by omega), hR.l8])
      (by rw [f₂ _ (by omega) (by omega), r03]) (by omega) (by omega) (by rw [e₀]; exact hw)
      (by omega)
    rw [e₀, e₁'] at Um
    have hw₄ := e₄.wb_right
    have f₄ : ∀ x, x ≠ 4823 → x ≠ 4900 → x ≠ 4902 → x ≠ 4904 → x ≠ 4905 → x ≠ 4906 →
        (x < 4826 ∨ 4832 < x) → c₄.nreg x = c.nreg x := fun x h0 h1 h2 h3 h4 h5 hx => by
      rw [Un x h1 h2 h3 h4 h5, f₂ x h0 hx]
    obtain ⟨c₅, k₅, e₅, hk₅, C2, C3, C4, C4', C5', C6'⟩ := cpArr_exec (P := P) c₄ hw₄
      (n := n) (Sb := b + 19 * n + 3) (Db := b)
      (by rw [f₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        hR.y0])
      (by rw [f₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        hR.y1])
      (by rw [f₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        hR.y2]) ⟨by omega, by omega, by omega, by omega⟩
    have m₄ : ∀ a', a' ≠ b + 3 * n + a → c₄.nmem a' = c₂.nmem a' := fun a' h => by
      rw [Um, upd_other _ _ _ h]
    refine ⟨c₅, k₁ + (k₂ + ((k₄ + k₅) + 2)), .seq e₁ (.seq e₂ (.ifLtN_false hnlt (.seq e₄ e₅))),
      by omega, Or.inr ⟨h0, by rw [C4 _ (by omega), U0], by rw [C4 _ (by omega), U2],
        by rw [C4 _ (by omega), Un _ (by omega) (by omega) (by omega) (by omega) (by omega), K1],
        fun i hi => by rw [C2 i hi, m₄ _ (by omega), K2 i hi],
        by rw [C3 _ (by omega), Um, upd_same],
        fun k hk => by rw [C3 _ (by omega), m₄ _ (by omega), K3 k hk],
        fun a' h1 h2 h3 h4 => by rw [C3 _ (by omega), m₄ _ h2, m₂ a' h3 h4]⟩,
      fun x hx => ?_, ?_, ?_, by rw [C4', Ur, K6, gr₁], by rw [C5', Urm, K7, grm₁],
      by rw [C6', Uo, K8, go₁]⟩
    · unfold LvFr at hx
      rw [C4 x (by omega), f₄ x (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)]
    · rw [C4 _ (by omega), f₄ _ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), r25]
    · rw [C4 _ (by omega), f₄ _ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), r73]
/-- **A heavy component on the machine**: `LZ = LAB[z]`, the anchor scan, then failure (kind `3`,
memory kept) or the prune update at the anchor (`KeepOut`). -/
theorem lvPrune_exec (c : Config) (hc : WordsBounded W c) {n b nH A W₀ IXb z tot : ℕ}
    (hR : LvRegs c n b nH A W₀) (r25 : c.nreg 4825 = IXb) (r89 : c.nreg 4789 = z)
    (r91 : c.nreg 4891 = tot) (r73 : c.nreg 4873 = 1) (hz : z < n)
    (lay : b + 20 * n + 3 ≤ IXb ∧ IXb + n + 1 ≤ W)
    (hlab : ∀ j < n, c.nmem (b + 13 * n + 1 + j) ≤ n)
    (hw : ∀ i < n, c.nmem (b + 3 * n + i) + tot ≤ W) :
    ∃ c' t, Exec P W lvPrune c c' t ∧ t ≤ 46 * n + 36 ∧
      (((ffS (fun i => acP (c.nmem (b + 15 * n + 2 + i)) (c.nmem (b + 13 * n + 1 + i))
          (c.nmem (b + 13 * n + 1 + z))) n).1 = 0 ∧ c'.nreg 4900 = 3 ∧ c'.nmem = c.nmem) ∨
        ((ffS (fun i => acP (c.nmem (b + 15 * n + 2 + i)) (c.nmem (b + 13 * n + 1 + i))
          (c.nmem (b + 13 * n + 1 + z))) n).1 ≠ 0 ∧
          KeepOut c.nmem c' n b IXb (c.nmem (b + 13 * n + 1 + z))
            (ffS (fun i => acP (c.nmem (b + 15 * n + 2 + i)) (c.nmem (b + 13 * n + 1 + i))
              (c.nmem (b + 13 * n + 1 + z))) n).2 tot)) ∧
      (∀ x, LvFr x → c'.nreg x = c.nreg x) ∧ c'.nreg 4825 = IXb ∧ c'.nreg 4873 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2⟩ := lay
  set LZ := c.nmem (b + 13 * n + 1 + z) with hLZ
  have hLZn : LZ ≤ n := hlab z hz
  obtain ⟨c₁, k₁, e₁, hk₁, g03, g01, g02, g03', gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 4904 4849 4789, .loadN 4903 4904, .copyN 4801 4885,
        .copyN 4802 4849, .copyN 4803 4903]) c c₁ k₁ ∧ k₁ = 5 ∧ c₁.nreg 4903 = LZ ∧
      c₁.nreg 4801 = b + 15 * n + 2 ∧ c₁.nreg 4802 = b + 13 * n + 1 ∧ c₁.nreg 4803 = LZ ∧
      (∀ x, x ≠ 4801 → x ≠ 4802 → x ≠ 4803 → x ≠ 4903 → x ≠ 4904 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    have p9 := hR.p9
    have l5 := hR.l5
    exec_block
    all_goals try (config_simp; (try simp only [p9, r89]); omega)
    refine ⟨rfl, by config_simp; simp only [p9, r89, hLZ], by config_simp; exact l5,
      by config_simp; exact p9, by config_simp; simp only [p9, r89, hLZ],
      fun x h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl, rfl⟩
    simp only [Config.nreg_mk, upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3,
      upd_other _ _ _ h4, upd_other _ _ _ h5]
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, A1, A2, A3, A4, A5, A6⟩ := acScan_exec (P := P) c₁ hw₁
    (n := n) (TGb := b + 15 * n + 2) (LABb := b + 13 * n + 1) (LZ := LZ)
    (by rw [gn₁ _ (by omega) (by omega) (by omega) (by omega) (by omega), hR.c0]) g01 g02 g03'
    (fun j hj => by rw [gm₁]; have := hlab j hj; omega) (by omega) (by omega) (by omega)
  rw [gm₁] at A1
  have hw₂ := e₂.wb_right
  have f₂ : ∀ x, x ≠ 4801 → x ≠ 4802 → x ≠ 4803 → x ≠ 4903 → x ≠ 4904 → (x < 4804 ∨ 4811 < x) →
      c₂.nreg x = c.nreg x := fun x h1 h2 h3 h4 h5 hx => by rw [A2 x hx, gn₁ x h1 h2 h3 h4 h5]
  set F := ffS (fun i => acP (c.nmem (b + 15 * n + 2 + i)) (c.nmem (b + 13 * n + 1 + i)) LZ) n
    with hF
  have h06 : c₂.nreg 4806 = F.1 := congrArg Prod.fst A1
  have h07 : c₂.nreg 4807 = F.2 := congrArg Prod.snd A1
  have t03 : c₂.nreg 4903 = LZ := by rw [A2 _ (by omega)]; exact g03
  have t73 : c₂.nreg 4873 = 1 := by
    rw [f₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r73]
  have hFs := ffS_spec (fun i => acP_le (c.nmem (b + 15 * n + 2 + i))
    (c.nmem (b + 13 * n + 1 + i)) LZ) n
  by_cases h0 : F.1 = 0
  · have hlt : c₂.nreg 4806 < c₂.nreg 4873 := by rw [h06, t73]; omega
    obtain ⟨c₃, k₃, e₃, hk₃, b00, bn, bm, br, brm, bo⟩ : ∃ c₃ k₃,
        Exec P W (block [.constN 4900 3]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 4900 = 3 ∧
        (∀ x, x ≠ 4900 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
        c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
      exec_block
      all_goals try ((try config_simp); omega)
      refine ⟨rfl, by config_simp, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
      simp only [Config.nreg_mk, upd_other _ _ _ h1]
    refine ⟨c₃, k₁ + (k₂ + (k₃ + 1)), .seq e₁ (.seq e₂ (.ifLtN_true hlt e₃)), by omega,
      Or.inl ⟨h0, b00, by rw [bm, A3, gm₁]⟩, fun x hx => ?_, ?_, ?_, by rw [br, A4, gr₁],
      by rw [brm, A5, grm₁], by rw [bo, A6, go₁]⟩
    · unfold LvFr at hx
      rw [bn x (by omega), f₂ x (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)]
    · rw [bn _ (by omega), f₂ _ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), r25]
    · rw [bn _ (by omega), t73]
  · have hnlt : ¬ c₂.nreg 4806 < c₂.nreg 4873 := by rw [h06, t73]; omega
    have hFz : F.2 < n := by rcases hFs with ⟨h, -⟩ | ⟨-, h, -⟩ <;> [exact absurd h h0; exact h]
    have hR₂ : LvRegs c₂ n b nH A W₀ := hR.of_frame fun x hx => by
      unfold LvFr at hx
      exact f₂ x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have m₂ : c₂.nmem = c.nmem := by rw [A3, gm₁]
    obtain ⟨c₃, k₃, e₃, hk₃, KO, K1, K2, K3, K4, K5, K6⟩ := lvKeep_exec (P := P) c₂ hw₂ hR₂
      (IXb := IXb) (LZ := LZ) (a := F.2) (tot := tot)
      (by rw [f₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r25])
      t03 h07 (by rw [f₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r91])
      t73 hFz hLZn ⟨l1, l2⟩ (fun j hj => by rw [m₂]; exact hlab j hj)
      (by rw [m₂]; exact hw _ hFz)
    rw [m₂] at KO
    refine ⟨c₃, k₁ + (k₂ + (k₃ + 2)), .seq e₁ (.seq e₂ (.ifLtN_false hnlt e₃)), by omega,
      Or.inr ⟨h0, KO⟩, fun x hx => ?_, K2, K3, by rw [K4, A4, gr₁], by rw [K5, A5, grm₁],
      by rw [K6, A6, go₁]⟩
    have hx' := hx
    unfold LvFr at hx'
    rw [K1 x hx, f₂ x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]

/-- **No heavy component on the machine**: the anchor scan of the cut (`TG2`), kind `2`, the
found flag in `4901`, the index in `4902`; memory kept. -/
theorem lvCutB_exec (c : Config) (hc : WordsBounded W c) {n b nH A W₀ : ℕ}
    (hR : LvRegs c n b nH A W₀) (r73 : c.nreg 4873 = 1) (hW : b + 20 * n + 3 ≤ W)
    (htg : ∀ j < n, c.nmem (b + 16 * n + 2 + j) ≤ 1) :
    ∃ c' t, Exec P W lvCutB c c' t ∧ t ≤ 19 * n + 12 ∧ c'.nreg 4900 = 2 ∧
      (c'.nreg 4901, c'.nreg 4902) = ffS (fun i => acP (c.nmem (b + 16 * n + 2 + i))
        (c.nmem (b + 16 * n + 2 + i)) 1) n ∧ c'.nmem = c.nmem ∧
      (∀ x, LvFr x → c'.nreg x = c.nreg x) ∧ c'.nreg 4873 = 1 ∧
      (∀ x, (4911 < x ∨ x = 4825) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, g01, g02, g03, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 4801 4886, .copyN 4802 4886, .copyN 4803 4873]) c c₁ k₁ ∧
      k₁ = 3 ∧ c₁.nreg 4801 = b + 16 * n + 2 ∧ c₁.nreg 4802 = b + 16 * n + 2 ∧
      c₁.nreg 4803 = 1 ∧
      (∀ x, x ≠ 4801 → x ≠ 4802 → x ≠ 4803 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    have l6 := hR.l6
    exec_block
    refine ⟨rfl, by config_simp; exact l6, by config_simp; exact l6, by config_simp; exact r73,
      fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
    simp only [Config.nreg_mk, upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3]
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, A1, A2, A3, A4, A5, A6⟩ := acScan_exec (P := P) c₁ hw₁
    (n := n) (TGb := b + 16 * n + 2) (LABb := b + 16 * n + 2) (LZ := 1)
    (by rw [gn₁ _ (by omega) (by omega) (by omega), hR.c0]) g01 g02 g03
    (fun j hj => by rw [gm₁]; have := htg j hj; omega) (by omega) (by omega) (by omega)
  rw [gm₁] at A1
  have hw₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, b00, b01, b02, bn, bm, br, brm, bo⟩ : ∃ c₃ k₃,
      Exec P W (block [.constN 4900 2, .copyN 4901 4806, .copyN 4902 4807]) c₂ c₃ k₃ ∧
      k₃ = 3 ∧ c₃.nreg 4900 = 2 ∧ c₃.nreg 4901 = c₂.nreg 4806 ∧ c₃.nreg 4902 = c₂.nreg 4807 ∧
      (∀ x, x ≠ 4900 → x ≠ 4901 → x ≠ 4902 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, fun x h1 h2 h3 => ?_,
      rfl, rfl, rfl, rfl⟩
    simp only [Config.nreg_mk, upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3]
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, b00, by rw [b01, b02, A1],
    by rw [bm, A3, gm₁], fun x hx => ?_, ?_, fun x hx => ?_, by rw [br, A4, gr₁],
    by rw [brm, A5, grm₁], by rw [bo, A6, go₁]⟩
  · unfold LvFr at hx
    rw [bn x (by omega) (by omega) (by omega), A2 x (by omega),
      gn₁ x (by omega) (by omega) (by omega)]
  · rw [bn _ (by omega) (by omega) (by omega), A2 _ (by omega),
      gn₁ _ (by omega) (by omega) (by omega), r73]
  · rw [bn x (by omega) (by omega) (by omega), A2 x (by omega),
      gn₁ x (by omega) (by omega) (by omega)]

end Exec

/-! ### The level, semantically -/

section Sem

open Equiv Orbit

variable {P : Input} {W : ℕ}
variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **The input of a level** in the memory `m` (layout of base `b`): an enumeration `e` of
`B ⊇ N` by `[0, n)`, the reverse indices, the flags of `N`, the hole numbers of the tails, the
class keys, the weights `EX[i] = ex (e i)`. -/
structure LvIn (m : ℕ → ℕ) (n b : ℕ) (e : ℕ → D) (B N : Finset D) (Hs : List (Finset V))
    (ex : D → ℕ) : Prop where
  mem : ∀ i < n, e i ∈ B
  surj : ∀ d ∈ B, ∃ i < n, e i = d
  inj : ∀ i < n, ∀ j < n, e i = e j → i = j
  sub : N ⊆ B
  rv0 : ∀ i < n, m (b + 2 * n + i) < n ∧ e (m (b + 2 * n + i)) = M.rev (e i)
  nf : ∀ i < n, (m (b + i) ≠ 0 ↔ e i ∈ N)
  th : ∀ i < n, ∀ j < Hs.length, (m (b + n + i) = j + 1 ↔ M.tail (e i) ∈ Hs.getD j ∅)
  tk : ∀ i < n, m (b + 6 * n + i) < n
  key : ∀ i < n, ∀ j < n, (m (b + 6 * n + i) = m (b + 6 * n + j) ↔
    HRel Hs (M.tail (e i)) (M.tail (e j)))
  ex : ∀ i < n, m (b + 3 * n + i) = ex (e i)

/-- The memory cells every level keeps: below `b`, `TH`, `RV0`, `TK`, between the layout and the
records `IXb`, above `IXb + n + 1`. -/
def LvKept (n b IXb a : ℕ) : Prop :=
  a < b ∨ (b + n ≤ a ∧ a < b + 3 * n) ∨ (b + 6 * n ≤ a ∧ a < b + 7 * n) ∨
    (b + 20 * n + 3 ≤ a ∧ a < IXb) ∨ IXb + n + 1 ≤ a

open Classical in
variable (M) in
/-- **The outcome of a level** (kind in `4900`) for the choices `ch` and the state `s`:
`0` — no cut-vertex hole (`NoCut`); `1` — a prune: `scStep ch Hs s = some …`, the kept flags in
`NF`, the new weights in `EX`, the pruned indices (`r4828 > 0` of them) at `IXb`, the anchor index
in `4902`; `2` — no heavy component: `scStep = none`, `scBase` the cut at the hole `g` (anchor
flag `4901`, index `4902`), the labels of the components off `g` in `LAB`; `3` — failure. -/
def LvOut (ch : ScChoice M) (Hs : List (Finset V)) (s : ScSt D) (m₀ : ℕ → ℕ) (c' : Config)
    (n b IXb : ℕ) (e : ℕ → D) : Prop :=
  (c'.nreg 4900 = 0 ∧ NoCut M s.1 Hs ∧ (∀ i < n, c'.nmem (b + i) = m₀ (b + i)) ∧
    ∀ i < n, c'.nmem (b + 3 * n + i) = m₀ (b + 3 * n + i)) ∨
  (c'.nreg 4900 = 1 ∧ ∃ K : Finset D, ∃ a₀ < n, c'.nreg 4902 = a₀ ∧
    scStep ch Hs s = some ((K, ret s.2.1 K, exP s.1 K s.2.2 (e a₀)), (s.1, K, e a₀)) ∧
    (∀ i < n, (c'.nmem (b + i) ≠ 0 ↔ e i ∈ K)) ∧
    (∀ i < n, c'.nmem (b + 3 * n + i) = exP s.1 K s.2.2 (e a₀) (e i)) ∧
    0 < c'.nreg 4828 ∧ (∀ k < c'.nreg 4828, c'.nmem (IXb + k) < n) ∧
    ((range (c'.nreg 4828)).image fun k => c'.nmem (IXb + k)).image e = s.1 \ K) ∨
  (c'.nreg 4900 = 2 ∧ scStep ch Hs s = none ∧ ∃ g : Finset V,
    (∀ i < n, ∀ j < n, e i ∈ s.1 → (c'.nmem (b + 13 * n + 1 + i) = c'.nmem (b + 13 * n + 1 + j) ↔
      e j ∈ comp M s.1 Hs g (e i))) ∧
    (c'.nreg 4901 ≠ 0 → c'.nreg 4902 < n) ∧
    scBase ch Hs s = (if c'.nreg 4901 = 0 then none else some (cutCert M Hs s.1 g (e (c'.nreg 4902)))) ∧
    (∀ i < n, c'.nmem (b + i) = m₀ (b + i)) ∧
    ∀ i < n, c'.nmem (b + 3 * n + i) = m₀ (b + 3 * n + i)) ∨
  (c'.nreg 4900 = 3 ∧ scStep ch Hs s = none ∧ scBase ch Hs s = none ∧
    (∀ i < n, c'.nmem (b + i) = m₀ (b + i)) ∧
    ∀ i < n, c'.nmem (b + 3 * n + i) = m₀ (b + 3 * n + i))

lemma tg2_eq (th nf J1 : ℕ) :
    (1 - phNe th J1) * (nf / nf) = if th = J1 ∧ nf ≠ 0 then 1 else 0 := by
  rw [phNe_eq, sgn_eq]; split_ifs <;> simp_all

lemma tg_ne (th J1 : ℕ) : 1 - phNe th J1 ≠ 0 ↔ th = J1 := by
  rw [phNe_eq]; split_ifs <;> simp_all

open Classical in
/-- **The anchor of the cut from the scan of `TG2`.** -/
lemma anchor_cut_ffS (sepF : SepFn M) {e : ℕ → D} {n : ℕ} {Hs : List (Finset V)} {A W₀ : ℕ}
    {N : Finset D} {g : Finset V} {th nf : ℕ → ℕ} {J1 : ℕ}
    (hth : ∀ i < n, (th i = J1 ↔ M.tail (e i) ∈ g)) (hnf : ∀ i < n, (nf i ≠ 0 ↔ e i ∈ N)) :
    (scChoiceE M sepF e n Hs A W₀).anchor N g =
      if (ffS (fun i => acP ((1 - phNe (th i) J1) * (nf i / nf i))
        ((1 - phNe (th i) J1) * (nf i / nf i)) 1) n).1 = 0 then none
      else some (e (ffS (fun i => acP ((1 - phNe (th i) J1) * (nf i / nf i))
        ((1 - phNe (th i) J1) * (nf i / nf i)) 1) n).2) := by
  show findE e n _ = _
  refine findE_ffS (fun i => acP_le _ _ _) fun i hi => ?_
  rw [mem_filter, acP_eq, tg2_eq]
  have h1 := hth i hi
  have h2 := hnf i hi
  by_cases hA : th i = J1 <;> by_cases hB : nf i = 0 <;> simp_all

lemma saF_congr2 {key key' val val' : ℕ → ℕ} {n : ℕ} (hk : ∀ j < n, key j = key' j)
    (hv : ∀ j < n, val j = val' j) (k : ℕ) : saF key val n k = saF key' val' n k := by
  unfold saF
  rw [show (range n).filter (fun j => key j = k) = (range n).filter (fun j => key' j = k) from
    filter_congr fun j hj => by rw [hk j (mem_range.1 hj)]]
  exact sum_congr rfl fun j hj => hv j (mem_range.1 (mem_filter.1 hj).1)

lemma image_range_getElem {L : List ℕ} {f : ℕ → ℕ}
    (h : ∀ k (hk : k < L.length), f k = L[k]) :
    (range L.length).image f = L.toFinset := by
  ext x
  simp only [mem_image, mem_range, List.mem_toFinset]
  constructor
  · rintro ⟨k, hk, rfl⟩; rw [h k hk]; exact List.getElem_mem hk
  · intro hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact ⟨k, hk, h k hk⟩

/-- The total weight of `N` from the masked values. -/
lemma sum_lpV {e : ℕ → D} {n : ℕ} {N : Finset D} {nf exA : ℕ → ℕ} {ex : D → ℕ}
    (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) (hsurjN : ∀ d ∈ N, ∃ i < n, e i = d)
    (hnf : ∀ i < n, (nf i ≠ 0 ↔ e i ∈ N)) (hex : ∀ i < n, exA i = ex (e i)) :
    ∑ j ∈ range n, lpV (nf j) (exA j) = ∑ d ∈ N, (1 + ex d) := by
  rw [← sum_range_filter_reindex hinj hsurjN (fun d => 1 + ex d), sum_filter]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 hj
  rw [lpV_eq, hex j hj']
  by_cases h : e j ∈ N
  · simp [h, (hnf j hj').2 h]
  · have : ¬ nf j ≠ 0 := fun h' => h ((hnf j hj').1 h')
    simp [h, this]

/-- The weight of a component from the scatter-add by labels. -/
lemma saF_comp {e : ℕ → D} {n : ℕ} {Hs : List (Finset V)} {N : Finset D} {g : Finset V}
    {lab val : ℕ → ℕ} {ex : D → ℕ}
    (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) (hsurjN : ∀ d ∈ N, ∃ i < n, e i = d)
    (hlab : ∀ i < n, ∀ j < n, e i ∈ N → (lab i = lab j ↔ e j ∈ comp M N Hs g (e i)))
    (hval : ∀ j < n, val j = if e j ∈ N then 1 + ex (e j) else 0) {z : ℕ} (hz : z < n)
    (hzN : e z ∈ N) :
    saF lab val n (lab z) = ∑ d ∈ comp M N Hs g (e z), (1 + ex d) := by
  rw [saF]
  have hf : (range n).filter (fun j => lab j = lab z) =
      (range n).filter (fun j => e j ∈ comp M N Hs g (e z)) := by
    ext j
    simp only [mem_filter, mem_range]
    exact and_congr_right fun hj => by rw [eq_comm]; exact hlab z hz j hj hzN
  rw [hf, ← sum_range_filter_reindex hinj (fun d hd => hsurjN d (mem_comp.1 hd).1)
    (fun d => 1 + ex d)]
  refine sum_congr rfl fun j hj => ?_
  obtain ⟨hj1, hj2⟩ := mem_filter.1 hj
  rw [hval j (mem_range.1 hj1), if_pos (mem_comp.1 hj2).1]

set_option maxHeartbeats 1600000 in
open Classical in
/-- **A level at a cut-vertex hole on the machine** (the hole `Hs[J]` chosen by `hlProg`): the
outcome is `LvOut` of kind `1`, `2` or `3`. -/
theorem lvCut_exec (sepF : SepFn M) {e : ℕ → D} {B N : Finset D} {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) {τ : Perm D} {ex : D → ℕ} {n b nH A W₀ IXb J : ℕ}
    (c : Config) (hc : WordsBounded W c) (hR : LvRegs c n b nH A W₀)
    (hI : LvIn M c.nmem n b e B N Hs ex) (r25 : c.nreg 4825 = IXb) (r72 : c.nreg 4872 = J)
    (r73 : c.nreg 4873 = 1) (hJ : J < Hs.length) (hHW : Hs.length + 1 ≤ W)
    (hnc : ¬ NoCut M N Hs)
    (hhole : (scChoiceE M sepF e n Hs A W₀).hole N = some (Hs.getD J ∅))
    (lay : b + 20 * n + 3 ≤ IXb ∧ IXb + n + 1 ≤ W)
    (hS : A + 2 * ∑ j ∈ range n, (1 + c.nmem (b + 3 * n + j)) ≤ W) :
    ∃ c' t, Exec P W lvCut c c' t ∧ t ≤ 244 * n + 79 ∧
      LvOut M (scChoiceE M sepF e n Hs A W₀) Hs (N, τ, ex) c.nmem c' n b IXb e ∧
      (∀ a, LvKept n b IXb a → c'.nmem a = c.nmem a) ∧
      (∀ x, LvFr x → c'.nreg x = c.nreg x) ∧ c'.nreg 4825 = IXb ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2⟩ := lay
  set g := Hs.getD J ∅ with hg
  set ch := scChoiceE M sepF e n Hs A W₀ with hch
  have hgm : g ∈ Hs := by
    rw [hg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJ, Option.getD_some]
    exact List.getElem_mem hJ
  have hsurjN : ∀ d ∈ N, ∃ i < n, e i = d := fun d hd => hI.surj d (hI.sub hd)
  set m₀ := c.nmem with hm₀
  have hEX : ∀ j < n, 1 + m₀ (b + 3 * n + j) ≤ ∑ j ∈ range n, (1 + m₀ (b + 3 * n + j)) :=
    fun j hj => single_le_sum (f := fun j => 1 + m₀ (b + 3 * n + j)) (fun _ _ => Nat.zero_le _)
      (mem_range.2 hj)
  -- 1. the hole number
  obtain ⟨c₁, k₁, e₁, hk₁, g45, g84, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 4845 4872 4873, .copyN 4884 4845]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 4845 = J + 1 ∧ c₁.nreg 4884 = J + 1 ∧
      (∀ x, x ≠ 4845 → x ≠ 4884 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; (try simp only [r72, r73]); omega)
    refine ⟨rfl, by config_simp; simp only [r72, r73], by config_simp; simp only [r72, r73],
      fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    simp only [Config.nreg_mk, upd_other _ _ _ h1, upd_other _ _ _ h2]
  have hw₁ := e₁.wb_right
  have hR₁ : LvRegs c₁ n b nH A W₀ := hR.of_frame fun x hx => by
    unfold LvFr at hx; exact gn₁ x (by omega) (by omega)
  -- 2. the labels of the components off `g`
  obtain ⟨c₂, k₂, e₂, hk₂, L1, L2, L3, L4, L5, L6, L7⟩ := phCC_comp (P := P) (M := M) (B := B)
    (N := N) hd hgm (n := n) (NFb := b) (THb := b + n) (RV0b := b + 2 * n) (J1 := J + 1)
    (GNb := b + 4 * n) (RVb := b + 5 * n) (TKb := b + 6 * n) (YFb := b + 7 * n)
    (LSb := b + 8 * n) (OFFb := b + 9 * n) (ADJb := b + 10 * n + 1) (LABb := b + 13 * n + 1)
    (Qb := b + 14 * n + 1) hI.mem hI.surj hI.inj hI.sub c₁ hw₁
    ⟨by omega, by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega⟩
    (by omega) ⟨by omega, by omega, by omega⟩ (by omega)
    (fun i hi => by rw [gm₁]; exact hI.rv0 i hi) (fun i hi => by rw [gm₁]; exact hI.nf i hi)
    (fun i hi => by rw [gm₁]; exact hI.th i hi J hJ) (fun i hi => by rw [gm₁]; exact hI.tk i hi)
    (fun i hi j hj => by rw [gm₁]; exact hI.key i hi j hj)
    hR₁.p0 hR₁.p1 hR₁.p2 hR₁.p3 g45 hR₁.p6 hR₁.p7 hR₁.p8 hR₁.p9 hR₁.p10 hR₁.r0 hR₁.r1 hR₁.r2
    hR₁.r3 hR₁.r4 hR₁.r5 hR₁.r6 hR₁.s0 hR₁.s1 hR₁.s2 hR₁.s3 hR₁.s4
  have hw₂ := e₂.wb_right
  have f₂ : ∀ x, (x < 4405 ∨ (4436 < x ∧ x < 4853) ∨ 4865 < x) → c₂.nreg x = c₁.nreg x := L4
  have hmid : ∀ k < 10, phCC.wr (4417 + k) = false := by decide
  have hR₂ : LvRegs c₂ n b nH A W₀ := hR₁.of_frame fun x hx => by
    unfold LvFr at hx
    by_cases hm : 4416 < x ∧ x < 4427
    · obtain ⟨k, hk, rfl⟩ : ∃ k < 10, x = 4417 + k := ⟨x - 4417, by omega, by omega⟩
      exact e₂.nreg_of_wr (hmid k hk)
    · exact f₂ x (by omega)
  have m₂ : ∀ a, (a < b + 4 * n ∨ (b + 6 * n ≤ a ∧ a < b + 7 * n) ∨ b + 15 * n + 1 ≤ a) →
      c₂.nmem a = m₀ a := fun a ha => by rw [L3 a (by omega), gm₁]
  have hlabN : ∀ i < n, ∀ j < n, e i ∈ N → (c₂.nmem (b + 13 * n + 1 + i) =
      c₂.nmem (b + 13 * n + 1 + j) ↔ e j ∈ comp M N Hs g (e i)) := L1
  have hSm : ∑ j ∈ range n, (1 + c₂.nmem (b + 3 * n + j)) = ∑ j ∈ range n, (1 + m₀ (b + 3 * n + j)) :=
    sum_congr rfl fun j hj => by rw [m₂ _ (by have := mem_range.1 hj; omega)]
  -- 3. the arrays of the scans
  obtain ⟨c₃, k₃, e₃, hk₃, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11⟩ := lpProg_exec (P := P) c₂ hw₂
    (n := n) (NFb := b) (THb := b + n) (EXb := b + 3 * n) (J1 := J + 1) (TGb := b + 15 * n + 2)
    (TG2b := b + 16 * n + 2) (VALb := b + 17 * n + 2) (SUMb := b + 18 * n + 2)
    hR₂.l0 hR₂.l1 hR₂.l2 hR₂.l3 (by rw [f₂ _ (by omega)]; exact g84) hR₂.l5 hR₂.l6 hR₂.l7 hR₂.l8
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩ (by rw [hSm]; omega)
  have hw₃ := e₃.wb_right
  have hR₃ : LvRegs c₃ n b nH A W₀ := hR₂.of_frame fun x hx => by
    unfold LvFr at hx; exact P8 x (by omega)
  have m₃ : ∀ a, (a < b + 15 * n + 2 ∨ b + 19 * n + 3 ≤ a) → c₃.nmem a = c₂.nmem a :=
    fun a ha => P7 a (by omega)
  have eNF : ∀ i < n, c₂.nmem (b + i) = m₀ (b + i) := fun i hi => m₂ _ (by omega)
  have eEX : ∀ i < n, c₂.nmem (b + 3 * n + i) = m₀ (b + 3 * n + i) := fun i hi => m₂ _ (by omega)
  have eTH : ∀ i < n, c₂.nmem (b + n + i) = m₀ (b + n + i) := fun i hi => m₂ _ (by omega)
  have hval : ∀ j < n, c₃.nmem (b + 17 * n + 2 + j) = if e j ∈ N then 1 + ex (e j) else 0 :=
    fun j hj => by
      rw [P4 j hj, eNF j hj, eEX j hj, lpV_eq, hI.ex j hj]
      by_cases h : e j ∈ N
      · simp [h, (hI.nf j hj).2 h]
      · have : ¬ m₀ (b + j) ≠ 0 := fun h' => h ((hI.nf j hj).1 h')
        simp [h, this]
  have htot : c₃.nreg 4891 = ∑ d ∈ N, (1 + ex d) := by
    rw [P6]
    exact sum_lpV hI.inj hsurjN (fun i hi => by rw [eNF i hi]; exact hI.nf i hi)
      (fun i hi => by rw [eEX i hi]; exact hI.ex i hi)
  have hvalS : ∑ j ∈ range n, c₃.nmem (b + 17 * n + 2 + j) ≤ ∑ j ∈ range n, (1 + m₀ (b + 3 * n + j)) :=
    sum_le_sum fun j hj => by
      rw [P4 j (mem_range.1 hj), eEX j (mem_range.1 hj)]; exact lpV_le _ _
  -- 4. the weights of the components
  obtain ⟨c₄, k₄, e₄, hk₄, S1, S2, S3, S4, S5, S6⟩ := saProg_exec (P := P) c₃ hw₃
    (m := n) (nk := n + 1) (KEYb := b + 13 * n + 1) (VALb := b + 17 * n + 2) (st := 1)
    (Wb := b + 18 * n + 2) hR₃.a0 hR₃.a1 hR₃.a2 hR₃.a3 hR₃.a4
    (fun j hj => by rw [m₃ _ (by omega)]; have := (L2 j hj).2; omega)
    (fun k hk => P5 k (by omega)) (fun j hj => by omega) (fun j hj => by omega) (by omega)
    (by omega) (fun j hj => by omega) (by omega)
    (by simp only [one_mul]; omega)
  have hw₄ := e₄.wb_right
  have hR₄ : LvRegs c₄ n b nH A W₀ := hR₃.of_frame fun x hx => by
    unfold LvFr at hx; exact S3 x (by omega)
  have m₄ : ∀ a, (a < b + 18 * n + 2 ∨ b + 19 * n + 3 ≤ a) → c₄.nmem a = c₃.nmem a :=
    fun a ha => S2 a (by omega)
  have eLAB : ∀ i < n, c₄.nmem (b + 13 * n + 1 + i) = c₂.nmem (b + 13 * n + 1 + i) :=
    fun i hi => by rw [m₄ _ (by omega), m₃ _ (by omega)]
  have eNF4 : ∀ i < n, c₄.nmem (b + i) = m₀ (b + i) := fun i hi => by
    rw [m₄ _ (by omega), m₃ _ (by omega), eNF i hi]
  have eEX4 : ∀ i < n, c₄.nmem (b + 3 * n + i) = m₀ (b + 3 * n + i) := fun i hi => by
    rw [m₄ _ (by omega), m₃ _ (by omega), eEX i hi]
  have hsumL : ∀ i < n, c₄.nmem (b + 18 * n + 2 + c₄.nmem (b + 13 * n + 1 + i)) =
      saF (fun j => c₄.nmem (b + 13 * n + 1 + j)) (fun j => if e j ∈ N then 1 + ex (e j) else 0) n
        (c₄.nmem (b + 13 * n + 1 + i)) := fun i hi => by
    rw [S1 _ (by rw [eLAB i hi]; have := (L2 i hi).2; omega)]
    exact saF_congr2 (fun j hj => by rw [m₃ _ (by omega), eLAB j hj])
      (fun j hj => by rw [one_mul, hval j hj]) _
  have hSUMle : ∀ k < n + 1, A + c₄.nmem (b + 18 * n + 2 + k) ≤ W := fun k hk => by
    rw [S1 k hk]
    have := saF_le (fun j => c₃.nmem (b + 13 * n + 1 + j)) (fun j => c₃.nmem (b + 17 * n + 2 + 1 * j)) n k
    simp only [one_mul] at this ⊢
    omega
  -- 5. the heavy scan
  obtain ⟨c₅, k₅, e₅, hk₅, H1, H2, H3, H4, H5, H6⟩ := hvScan_exec (P := P) c₄ hw₄
    (n := n) (NFb := b) (LABb := b + 13 * n + 1) (SUMb := b + 18 * n + 2) (A := A) (W₀ := W₀)
    (nl := n + 1) hR₄.h0 hR₄.h1 hR₄.h2 hR₄.h3 hR₄.h4 hR₄.h5
    (fun j hj => by rw [eLAB j hj]; have := (L2 j hj).2; omega) hSUMle (by omega) (by omega)
    (by omega) (by omega)
  have hw₅ := e₅.wb_right
  have hR₅ : LvRegs c₅ n b nH A W₀ := hR₄.of_frame fun x hx => by
    unfold LvFr at hx; exact H2 x (by omega)
  set Fh := ffS (fun i => hvP (c₄.nmem (b + i)) (c₄.nmem (b + 18 * n + 2 + c₄.nmem (b + 13 * n + 1 + i)))
    A W₀) n with hFh
  have hheavy : ch.heavy N g ex = if Fh.1 = 0 then none else some (e Fh.2) :=
    hvScan_heavy sepF hI.inj hsurjN ex A W₀ (lab := fun j => c₄.nmem (b + 13 * n + 1 + j))
      (sum := fun k => c₄.nmem (b + 18 * n + 2 + k)) (nf := fun i => c₄.nmem (b + i))
      (fun i hi j hj hiN => by
      rw [eLAB i hi, eLAB j hj]; exact hlabN i hi j hj hiN) hsumL
      (fun i hi => by rw [eNF4 i hi]; exact hI.nf i hi)
  have h88 : c₅.nreg 4788 = Fh.1 := congrArg Prod.fst H1
  have h89 : c₅.nreg 4789 = Fh.2 := congrArg Prod.snd H1
  have t73 : c₅.nreg 4873 = 1 := by
    rw [H2 _ (by omega), S3 _ (by omega), P8 _ (by omega), f₂ _ (by omega),
      gn₁ _ (by omega) (by omega), r73]
  have t25 : c₅.nreg 4825 = IXb := by
    rw [H2 _ (by omega), S3 _ (by omega), P8 _ (by omega), f₂ _ (by omega),
      gn₁ _ (by omega) (by omega), r25]
  have t91 : c₅.nreg 4891 = ∑ d ∈ N, (1 + ex d) := by
    rw [H2 _ (by omega), S3 _ (by omega), htot]
  have m₅ : ∀ a, LvKept n b IXb a → c₅.nmem a = m₀ a := fun a ha => by
    unfold LvKept at ha
    rw [H3, m₄ a (by omega), m₃ a (by omega), m₂ a (by omega)]
  have hFrs : ∀ x, LvFr x → c₅.nreg x = c.nreg x := fun x hx => by
    have hx' := hx
    unfold LvFr at hx'
    by_cases hm : 4416 < x ∧ x < 4427
    · obtain ⟨k, hk, rfl⟩ : ∃ k < 10, x = 4417 + k := ⟨x - 4417, by omega, by omega⟩
      rw [H2 _ (by omega), S3 _ (by omega), P8 _ (by omega), e₂.nreg_of_wr (hmid k hk),
        gn₁ _ (by omega) (by omega)]
    · rw [H2 _ (by omega), S3 _ (by omega), P8 _ (by omega), f₂ _ (by omega),
        gn₁ _ (by omega) (by omega)]
  have hFhs := ffS_spec (fun i => hvP_le (c₄.nmem (b + i))
    (c₄.nmem (b + 18 * n + 2 + c₄.nmem (b + 13 * n + 1 + i))) A W₀) n
  have e5LAB : ∀ i < n, c₅.nmem (b + 13 * n + 1 + i) = c₂.nmem (b + 13 * n + 1 + i) :=
    fun i hi => by rw [H3, eLAB i hi]
  have e5NF : ∀ i < n, c₅.nmem (b + i) = m₀ (b + i) := fun i hi => by rw [H3, eNF4 i hi]
  have e5EX : ∀ i < n, c₅.nmem (b + 3 * n + i) = m₀ (b + 3 * n + i) := fun i hi => by
    rw [H3, eEX4 i hi]
  have hlab5 : ∀ i < n, ∀ j < n, e i ∈ N → (c₅.nmem (b + 13 * n + 1 + i) =
      c₅.nmem (b + 13 * n + 1 + j) ↔ e j ∈ comp M N Hs g (e i)) := fun i hi j hj hiN => by
    rw [e5LAB i hi, e5LAB j hj]; exact hlabN i hi j hj hiN
  have hthg : ∀ i < n, (c₂.nmem (b + n + i) = J + 1 ↔ M.tail (e i) ∈ g) := fun i hi => by
    rw [eTH i hi]; exact hI.th i hi J hJ
  have hfrK : ∀ (c' : Config), (∀ a, LvKept n b IXb a → c'.nmem a = c₅.nmem a) →
      ∀ a, LvKept n b IXb a → c'.nmem a = m₀ a := fun c' h a ha => by rw [h a ha, m₅ a ha]
  by_cases hF0 : Fh.1 = 0
  · -- no heavy component: the cut
    have hlt : c₅.nreg 4788 < c₅.nreg 4873 := by rw [h88, t73, hF0]; omega
    obtain ⟨c₆, k₆, e₆, hk₆, B0, B1, B2, B3, B4, B5, B6, B7, B8⟩ := lvCutB_exec (P := P) c₅ hw₅
      hR₅ t73 (by omega) (fun j hj => by
        rw [H3, m₄ _ (by omega), P3 j hj]
        rw [tg2_eq]; split_ifs <;> omega)
    have hz : ch.heavy N g ex = none := by rw [hheavy, if_pos hF0]
    obtain ⟨hst, hbase⟩ := scStep_cut (τ := τ) hnc hhole hz
    set Fa := ffS (fun i => acP (c₅.nmem (b + 16 * n + 2 + i)) (c₅.nmem (b + 16 * n + 2 + i)) 1) n
      with hFa
    have hanc : ch.anchor N g = if Fa.1 = 0 then none else some (e Fa.2) := by
      rw [hFa, ffS_congr (p' := fun i => acP ((1 - phNe (c₂.nmem (b + n + i)) (J + 1)) *
          (c₂.nmem (b + i) / c₂.nmem (b + i))) ((1 - phNe (c₂.nmem (b + n + i)) (J + 1)) *
          (c₂.nmem (b + i) / c₂.nmem (b + i))) 1) (fun j hj => by rw [H3, m₄ _ (by omega), P3 j hj])]
      exact anchor_cut_ffS sepF hthg (fun i hi => by rw [eNF i hi]; exact hI.nf i hi)
    have h01 : c₆.nreg 4901 = Fa.1 := congrArg Prod.fst B1
    have h02 : c₆.nreg 4902 = Fa.2 := congrArg Prod.snd B1
    have hFas := ffS_spec (fun i => acP_le (c₅.nmem (b + 16 * n + 2 + i))
      (c₅.nmem (b + 16 * n + 2 + i)) 1) n
    refine ⟨c₆, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + 1))))),
      .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.ifLtN_true hlt e₆))))), by omega,
      Or.inr (Or.inr (Or.inl ⟨B0, hst, g, fun i hi j hj hiN => by
        rw [B2]; exact hlab5 i hi j hj hiN, fun h => ?_, ?_, fun i hi => by rw [B2, e5NF i hi],
        fun i hi => by rw [B2, e5EX i hi]⟩)),
      hfrK c₆ (fun a _ => by rw [B2]), fun x hx => by rw [B3 x hx, hFrs x hx],
      by rw [B5 _ (Or.inr rfl), t25], by rw [B6, H4, S4, P9, L5, gr₁],
      by rw [B7, H5, S5, P10, L6, grm₁], by rw [B8, H6, S6, P11, L7, go₁]⟩
    · rw [h02]; rw [h01] at h
      rcases hFas with ⟨h', -⟩ | ⟨-, h', -⟩
      · exact absurd h' h
      · exact h'
    · rw [hbase, hanc, h01, h02]
      split_ifs <;> rfl
  · -- a heavy component
    have hnlt : ¬ c₅.nreg 4788 < c₅.nreg 4873 := by rw [h88, t73]; omega
    obtain ⟨hFh1, hz, hpz, -⟩ : Fh.1 = 1 ∧ Fh.2 < n ∧ _ ∧ _ := by
      rcases hFhs with ⟨h, -⟩ | h
      · exact absurd h hF0
      · exact h
    have hzN : e Fh.2 ∈ N := by
      rw [hvP_eq] at hpz
      split_ifs at hpz with h
      · exact (hI.nf _ hz).1 (by rw [← eNF4 _ hz]; exact h.1)
    have hheavy' : ch.heavy N g ex = some (e Fh.2) := by rw [hheavy, if_neg hF0]
    obtain ⟨c₆, k₆, e₆, hk₆, R1, R2, R3, R4, R5, R6, R7⟩ := lvPrune_exec (P := P) c₅ hw₅ hR₅
      (IXb := IXb) (z := Fh.2) (tot := ∑ d ∈ N, (1 + ex d)) t25 h89 t91 t73 hz ⟨l1, l2⟩
      (fun j hj => by rw [e5LAB j hj]; exact (L2 j hj).2)
      (fun i hi => by
        rw [e5EX i hi, ← sum_lpV hI.inj hsurjN hI.nf hI.ex]
        have h1 := hEX i hi
        have h2 : ∑ j ∈ range n, lpV (m₀ (b + j)) (m₀ (b + 3 * n + j)) ≤
            ∑ j ∈ range n, (1 + m₀ (b + 3 * n + j)) := sum_le_sum fun j _ => lpV_le _ _
        omega)
    set z := Fh.2 with hzdef
    set LZ := c₅.nmem (b + 13 * n + 1 + z) with hLZ
    set Fa := ffS (fun i => acP (c₅.nmem (b + 15 * n + 2 + i)) (c₅.nmem (b + 13 * n + 1 + i)) LZ) n
      with hFa
    have hanc : ch.anchor (comp M N Hs g (e z)) g = if Fa.1 = 0 then none else some (e Fa.2) :=
      acScan_anchor sepF (M := M) (e := e) (n := n) (Hs := Hs) (N := N) (g := g) A W₀
        (lab := fun j => c₅.nmem (b + 13 * n + 1 + j)) (tg := fun i => c₅.nmem (b + 15 * n + 2 + i))
        hz hzN hlab5 (fun i hi => by
        rw [H3, m₄ _ (by omega), P2 i hi, tg_ne]; exact hthg i hi)
    have hkp := kpScan_comp (M := M) (Hs := Hs) (g := g) (lab := fun j => c₅.nmem (b + 13 * n + 1 + j))
      hsurjN hz hzN hlab5 (nf := fun i => c₅.nmem (b + i)) (fun i hi => by rw [e5NF i hi]; exact hI.nf i hi)
    have hsub : comp M N Hs g (e z) ⊆ N := fun d hd => (mem_comp.1 hd).1
    have hrest : ∀ (c' : Config), c'.nreg 4900 = 3 → scStep ch Hs (N, τ, ex) = none →
        scBase ch Hs (N, τ, ex) = none → (∀ i < n, c'.nmem (b + i) = m₀ (b + i)) →
        (∀ i < n, c'.nmem (b + 3 * n + i) = m₀ (b + 3 * n + i)) →
        LvOut M ch Hs (N, τ, ex) m₀ c' n b IXb e := fun c' h1 h2 h3 h4 h5 =>
      Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, h4, h5⟩))
    refine ⟨c₆, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + 2))))),
      .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.ifLtN_false hnlt e₆))))), by omega, ?_,
      ?_, fun x hx => by rw [R2 x hx, hFrs x hx], R3, by rw [R5, H4, S4, P9, L5, gr₁],
      by rw [R6, H5, S5, P10, L6, grm₁], by rw [R7, H6, S6, P11, L7, go₁]⟩
    · rcases R1 with ⟨ha0, k3, hm⟩ | ⟨ha0, KO⟩
      · obtain ⟨h2, h3⟩ := scStep_noAnchor (τ := τ) hnc hhole hheavy'
          (by rw [hanc, if_pos ha0])
        exact hrest c₆ k3 h2 h3 (fun i hi => by rw [hm, e5NF i hi])
          (fun i hi => by rw [hm, e5EX i hi])
      · have hFas := ffS_spec (fun i => acP_le (c₅.nmem (b + 15 * n + 2 + i))
          (c₅.nmem (b + 13 * n + 1 + i)) LZ) n
        obtain ⟨-, ha, -, -⟩ : Fa.1 = 1 ∧ Fa.2 < n ∧ _ ∧ _ := by
          rcases hFas with ⟨h, -⟩ | h
          · exact absurd h ha0
          · exact h
        have hanc' : ch.anchor (comp M N Hs g (e z)) g = some (e Fa.2) := by
          rw [hanc, if_neg ha0]
        obtain ⟨hK1, hK2, hK3⟩ := hkp
        rcases KO with ⟨hl0, k3, hm⟩ | ⟨hl0, k1', k02, k28, kNF, kEX, kIX, km⟩
        · have hnK : ¬ (comp M N Hs g (e z)).card < N.card := by
            rw [comp_card_lt_iff, ← hK3, List.length_eq_zero_iff.1 hl0]
            simp
          obtain ⟨h2, h3⟩ := scStep_noShrink (τ := τ) hnc hhole hheavy' hanc' hnK
          exact hrest c₆ k3 h2 h3 (fun i hi => by rw [hm _ (by omega) (by omega), e5NF i hi])
            (fun i hi => by rw [hm _ (by omega) (by omega), e5EX i hi])
        · have hK : (comp M N Hs g (e z)).card < N.card := by
            rw [comp_card_lt_iff, ← hK3]
            obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero hl0)
            exact ⟨e x, mem_image.2 ⟨x, List.mem_toFinset.2 hx, rfl⟩⟩
          refine Or.inr (Or.inl ⟨k1', comp M N Hs g (e z), Fa.2, ha, k02,
            scStep_prune hnc hhole hheavy' hanc' hK, fun i hi => ?_, fun i hi => ?_,
            by rw [k28]; omega, fun k hk => ?_, ?_⟩)
          · rw [kNF i hi]; exact hK1 i hi
          · by_cases hia : i = Fa.2
            · subst hia
              have hSUMz : c₅.nmem (b + 18 * n + 2 + LZ) = ∑ d ∈ comp M N Hs g (e z), (1 + ex d) := by
                rw [hLZ, H3, hsumL z hz]
                exact saF_comp (M := M) hI.inj hsurjN (lab := fun j => c₄.nmem (b + 13 * n + 1 + j))
                  (fun i hi j hj hiN => by rw [eLAB i hi, eLAB j hj]; exact hlabN i hi j hj hiN)
                  (fun j _ => rfl) hz hzN
              rw [kEX, e5EX _ hi, hSUMz, hI.ex _ hi]
              unfold exP
              simp only [↓reduceIte]
              have := sum_sdiff hsub (f := fun d => 1 + ex d)
              omega
            · rw [km _ (by omega) (by omega) (by omega) (by omega), e5EX i hi, hI.ex i hi]
              unfold exP
              rw [if_neg (fun h => hia (hI.inj _ hi _ ha h))]
              simp
          · rw [k28] at hk
            rw [kIX k hk]; exact hK2 k hk
          · rw [k28, image_range_getElem (fun k hk => kIX k hk)]
            exact hK3
    · have hFa2 : Fa.2 ≤ n := (ffS_le (p := fun i => acP (c₅.nmem (b + 15 * n + 2 + i))
        (c₅.nmem (b + 13 * n + 1 + i)) LZ) (fun i => acP_le _ _ _) n).2
      exact hfrK c₆ fun a ha => by
        unfold LvKept at ha
        rcases R1 with ⟨-, -, hm⟩ | ⟨-, ⟨-, -, hm⟩ | ⟨-, -, -, -, -, -, -, km⟩⟩
        · rw [hm]
        · exact hm a (by omega) (by omega)
        · exact km a (by omega) (by omega) (by omega) (by omega)

lemma LvIn.congr {m m' : ℕ → ℕ} {n b : ℕ} {e : ℕ → D} {B N : Finset D} {Hs : List (Finset V)}
    {ex : D → ℕ} (h : LvIn M m n b e B N Hs ex)
    (hm : ∀ a, (a < b + 4 * n ∨ (b + 6 * n ≤ a ∧ a < b + 7 * n)) → m' a = m a) :
    LvIn M m' n b e B N Hs ex := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨h1, h2, h3, h4, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi j hj => ?_, fun i hi => ?_⟩
  · rw [hm _ (by omega)]; exact h5 i hi
  · rw [hm _ (by omega)]; exact h6 i hi
  · rw [hm _ (by omega)]; exact h7 i hi
  · rw [hm _ (by omega)]; exact h8 i hi
  · rw [hm _ (by omega), hm _ (by omega)]; exact h9 i hi j hj
  · rw [hm _ (by omega)]; exact h10 i hi

lemma LvOut.congr {ch : ScChoice M} {Hs : List (Finset V)} {s : ScSt D} {m₀ m₀' : ℕ → ℕ}
    {c' : Config} {n b IXb : ℕ} {e : ℕ → D} (h : LvOut M ch Hs s m₀ c' n b IXb e)
    (h1 : ∀ i < n, m₀ (b + i) = m₀' (b + i))
    (h2 : ∀ i < n, m₀ (b + 3 * n + i) = m₀' (b + 3 * n + i)) :
    LvOut M ch Hs s m₀' c' n b IXb e := by
  rcases h with ⟨a1, a2, a3, a4⟩ | h | ⟨a1, a2, g, a3, a4, a5, a6, a7⟩ | ⟨a1, a2, a3, a4, a5⟩
  · exact Or.inl ⟨a1, a2, fun i hi => by rw [a3 i hi, h1 i hi],
      fun i hi => by rw [a4 i hi, h2 i hi]⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨a1, a2, g, a3, a4, a5, fun i hi => by rw [a6 i hi, h1 i hi],
      fun i hi => by rw [a7 i hi, h2 i hi]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a1, a2, a3, fun i hi => by rw [a4 i hi, h1 i hi],
      fun i hi => by rw [a5 i hi, h2 i hi]⟩))

open Classical in
/-- **One level of `scertD` on the machine** (the choices `scChoiceE`, any separator `sepF`):
within `|Hs| · (160 n + 36) + 244 n + 89` steps the outcome `LvOut` (kind `0`: `NoCut`; `1`: the
prune `scStep … = some …` with the new flags, weights and the record at `IXb`; `2`: the cut base;
`3`: failure); the kept memory `LvKept`, the fixed registers `LvFr` and `IXb` in `4825` kept. -/
theorem lvProg_exec (sepF : SepFn M) {e : ℕ → D} {B N : Finset D} {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) {τ : Perm D} {ex : D → ℕ} {n b A W₀ IXb : ℕ}
    (c : Config) (hc : WordsBounded W c) (hR : LvRegs c n b Hs.length A W₀)
    (hI : LvIn M c.nmem n b e B N Hs ex) (r25 : c.nreg 4825 = IXb) (hHW : Hs.length + 1 ≤ W)
    (lay : b + 20 * n + 3 ≤ IXb ∧ IXb + n + 1 ≤ W)
    (hS : A + 2 * ∑ j ∈ range n, (1 + c.nmem (b + 3 * n + j)) ≤ W) :
    ∃ c' t, Exec P W lvProg c c' t ∧ t ≤ Hs.length * (160 * n + 36) + 244 * n + 89 ∧
      LvOut M (scChoiceE M sepF e n Hs A W₀) Hs (N, τ, ex) c.nmem c' n b IXb e ∧
      (∀ a, LvKept n b IXb a → c'.nmem a = c.nmem a) ∧
      (∀ x, LvFr x → c'.nreg x = c.nreg x) ∧ c'.nreg 4825 = IXb ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2⟩ := lay
  obtain ⟨c₁, k₁, e₁, hk₁, Hres, Hmem, Hregs, Hr, Hrm, Ho⟩ := hlProg_exec (P := P) (M := M)
    (B := B) (N := N) hd (n := n) (NFb := b) (THb := b + n) (RV0b := b + 2 * n)
    (GNb := b + 4 * n) (RVb := b + 5 * n) (TKb := b + 6 * n) (YFb := b + 7 * n)
    (LSb := b + 8 * n) (OFFb := b + 9 * n) (ADJb := b + 10 * n + 1) (LABb := b + 13 * n + 1)
    (Qb := b + 14 * n + 1) hI.mem hI.surj hI.inj hI.sub c hc
    ⟨by omega, by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega⟩
    (by omega) ⟨by omega, by omega, by omega⟩ (by omega) hHW hI.rv0 hI.nf hI.th hI.tk hI.key
    hR.p0 hR.p1 hR.p2 hR.p3 hR.p6 hR.p7 hR.p8 hR.p9 hR.p10 hR.r0 hR.r1 hR.r2 hR.r3 hR.r4 hR.r5
    hR.r6 hR.s0 hR.s1 hR.s2 hR.s3 hR.s4 hR.u0 hR.u1 hR.u2 hR.v4
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, g73, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (block [.constN 4873 1]) c₁ c₂ k₂ ∧ k₂ = 1 ∧ c₂.nreg 4873 = 1 ∧
      (∀ x, x ≠ 4873 → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, by config_simp, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    simp only [Config.nreg_mk, upd_other _ _ _ h1]
  have hw₂ := e₂.wb_right
  have f₂ : ∀ x, LvFr x → c₂.nreg x = c.nreg x := fun x hx => by
    unfold LvFr at hx
    rw [gn₂ x (by omega), Hregs x ⟨by unfold HlFr; omega, by omega, by omega⟩]
  have t25 : c₂.nreg 4825 = IXb := by
    rw [gn₂ _ (by omega), Hregs _ ⟨by unfold HlFr; omega, by omega, by omega⟩, r25]
  have m₂ : ∀ a, (a < b + 4 * n ∨ (b + 6 * n ≤ a ∧ a < b + 7 * n) ∨ b + 15 * n + 1 ≤ a) →
      c₂.nmem a = c.nmem a := fun a ha => by rw [gm₂, Hmem a (by omega)]
  have hkept : ∀ a, LvKept n b IXb a → c₂.nmem a = c.nmem a := fun a ha => by
    unfold LvKept at ha; exact m₂ a (by omega)
  rcases hl_hole sepF e n A W₀ Hres with ⟨h0, hnc, -⟩ | ⟨h1, hJ, hnc, -, hhole⟩
  · have hlt : c₂.nreg 4871 < c₂.nreg 4873 := by rw [gn₂ _ (by omega), h0, g73]; omega
    obtain ⟨c₃, k₃, e₃, hk₃, b00, bn, bm, br, brm, bo⟩ : ∃ c₃ k₃,
        Exec P W (block [.constN 4900 0]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 4900 = 0 ∧
        (∀ x, x ≠ 4900 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
        c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
      exec_block
      all_goals try ((try config_simp); omega)
      refine ⟨rfl, by config_simp, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
      simp only [Config.nreg_mk, upd_other _ _ _ h1]
    refine ⟨c₃, k₁ + (k₂ + (k₃ + 1)), .seq e₁ (.seq e₂ (.ifLtN_true hlt e₃)), by omega,
      Or.inl ⟨b00, hnc, fun i hi => by rw [bm, m₂ _ (by omega)],
        fun i hi => by rw [bm, m₂ _ (by omega)]⟩, fun a ha => by rw [bm, hkept a ha],
      fun x hx => ?_, by rw [bn _ (by omega), t25], by rw [br, gr₂, Hr], by rw [brm, grm₂, Hrm],
      by rw [bo, go₂, Ho]⟩
    have hx' := hx; unfold LvFr at hx'
    rw [bn x (by omega), f₂ x hx]
  · have hnlt : ¬ c₂.nreg 4871 < c₂.nreg 4873 := by rw [gn₂ _ (by omega), h1, g73]; omega
    have hR₂ : LvRegs c₂ n b Hs.length A W₀ := hR.of_frame f₂
    have hI₂ : LvIn M c₂.nmem n b e B N Hs ex := hI.congr fun a ha => m₂ a (by omega)
    have hS₂ : A + 2 * ∑ j ∈ range n, (1 + c₂.nmem (b + 3 * n + j)) ≤ W := by
      rw [sum_congr rfl fun j hj => by rw [m₂ _ (by have := mem_range.1 hj; omega)]]; exact hS
    obtain ⟨c₃, k₃, e₃, hk₃, C1, C2, C3, C4, C5, C6, C7⟩ := lvCut_exec (P := P) (τ := τ) sepF hd
      c₂ hw₂ hR₂ hI₂ t25 (by rw [gn₂ _ (by omega)]) g73 hJ hHW hnc hhole ⟨l1, l2⟩ hS₂
    refine ⟨c₃, k₁ + (k₂ + (k₃ + 2)), .seq e₁ (.seq e₂ (.ifLtN_false hnlt e₃)), by omega,
      C1.congr (fun i hi => m₂ _ (by omega)) (fun i hi => m₂ _ (by omega)),
      fun a ha => by rw [C2 a ha, hkept a ha], fun x hx => by rw [C3 x hx, f₂ x hx], C4,
      by rw [C5, gr₂, Hr], by rw [C6, grm₂, Hrm], by rw [C7, go₂, Ho]⟩

end Sem

end BKMNW

end PlanarFlow
