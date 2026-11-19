module

public import PlanarFlow.BKMNW.ThSpec
public import PlanarFlow.BKMNW.NpSeg
public import PlanarFlow.BKMNW.SmSegsW

/-!
# `segP'`: the parts of the separator with their start vertices at the node

`segP sepX` (`NpSeg.lean`) copies the block `[Gb, Gb + 1 + 2 s + Σ k)` of the separator's parts
below the heap top; `SegsOut'` stores after it, at `Gb + 1 + 2 s + Σ k + j`, a frame
dart whose tail is the start vertex of the part `j`. **`segP' sepX`** is `segP sepX` with the
block size `z = 1 + 3 s + Σ k` (`sgC3` in place of `sgC`), so the start vertices are copied too:

* `sgC3`, `sgC3_exec`; **`SegsOut'.shift`** (the layout with the start vertices is translation
  invariant);
* **`segP'_spec`**: `SepPSpecXS' sepX sT sR` (the separator with `SegsOut'`, e.g. `sepPXS'_spec`)
  ⇒ `SegPSpec' (segP' sepX) (segT M sT sR) (segR M sR)`: the same step bound
  **`sT n k + 13 sR n m k + 30`** and room **`1 + sR n m k`** as `segP_spec`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs NegSSSP.Driver NcStep

universe w

/-- `z := 3 s + sum + 1`, `j := 0`. -/
def sgC3 : Stmt := block [.addN 8410 8405 8405, .addN 8410 8410 8405, .addN 8410 8410 8407,
  .addN 8410 8410 8402, .constN 8408 0]

/-- **The parts of the separator with their start vertices at the node.** -/
def segP' (sepX : Stmt) : Stmt :=
  .seq sgA (.seq sepX (.seq sgB (.seq (.whileLtN 8408 8405 npSgK) (.seq sgC3
    (.seq (.whileLtN 8408 8410 sgM) sgD)))))

theorem sgC3_exec {P : Input} {W : ℕ} (c : Config) (hc : WordsBounded W c) {s sum : ℕ}
    (r5 : c.nreg 8405 = s) (r7 : c.nreg 8407 = sum) (r2 : c.nreg 8402 = 1)
    (w : 3 * s + sum + 1 ≤ W) :
    ∃ c' t, Exec P W sgC3 c c' t ∧ t = 5 ∧ c'.nreg 8410 = 3 * s + sum + 1 ∧ c'.nreg 8408 = 0 ∧
      (∀ x, x ≠ 8408 → x ≠ 8410 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sgC3
  exec_block
  all_goals try (config_simp; simp only [r5, r7, r2]; omega)
  all_goals try omega
  refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r5, r7, r2]; omega
  · config_simp
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

section Shift

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The layout of the parts with their start vertices is translation invariant.** -/
lemma SegsOut'.shift {en : ℕ → D} {m : ℕ} {π : HSep M} {lo hi Gb lo' hi' b : ℕ}
    {mem mem' : ℕ → ℕ} (h : SegsOut' M en m π lo hi Gb mem)
    (hz : ∀ a < 1 + 3 * π.segs.length + (π.segs.map SPath.k).sum, mem' (b + a) = mem (Gb + a))
    (hlo : lo' ≤ b) (hhi : b + 1 + 3 * π.segs.length + (π.segs.map SPath.k).sum ≤ hi') :
    SegsOut' M en m π lo' hi' b mem' := by
  obtain ⟨h1, -, h3⟩ := h
  refine ⟨SegsOut.shift h1 (fun a ha => hz a (by omega)) hlo (by omega), hhi, fun j hj => ?_⟩
  have e : mem' (b + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum + j) =
      mem (Gb + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum + j) := by
    rw [show b + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum + j =
      b + (1 + 2 * π.segs.length + (π.segs.map SPath.k).sum + j) by omega, hz _ (by omega)]
    congr 1; omega
  rw [e]
  exact h3 j hj

end Shift

section Spec

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {ds : DSys M} {Reach : MCall M → Prop} {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ}
  {S T : Finset V} {Z : ℕ} {I : Input} {W : ℕ} {sepX : Stmt} {sT : ℕ → ℕ → ℕ}
  {sR : ℕ → ℕ → ℕ → ℕ}

/-- **`segP'` meets `SegPSpec'`** (the parts with their start vertices), from the separator's
specification with `SegsOut'`; steps `sT n k + 13 sR n m k + 30`, room `1 + sR n m k`. -/
theorem segP'_spec (hsep : SepPSpecXS' M ds Reach gid ν u S T Z I W sepX sT sR) :
    SegPSpec' M ds Reach gid ν u S T Z I W (segP' sepX) (segT M sT sR) (segR M sR) := by
  intro l r π Hs σ d e b m en c hin hL hde heb hroom hc r4 r5 r6
  have hcard : m = (pdarts M (l.piece ∪ r.piece) Hs).card := hL.card
  have hroom' : b + 1 + sR (l.piece ∪ r.piece).card m Hs.length ≤ W := by
    have : segR M sR (.node l r π, Hs, σ) = 1 + sR (l.piece ∪ r.piece).card m Hs.length := by
      unfold segR; simp only [ADec.piece]; rw [← hcard]
    rw [this] at hroom; omega
  unfold fsz at hde
  -- the set-up
  obtain ⟨c₁, t₁, e₁, ht₁, a3, a65, m₁, f₁, rr₁, rm₁, o₁⟩ :=
    sgA_exec (P := I) c hc r6 (by omega)
  have hmem₁ : ∀ a, a ≠ b → c₁.nmem a = c.nmem a := fun a ha => by
    rw [m₁, upd_other _ _ _ ha]
  have hin₁ : FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c₁ :=
    hin.stab fun a h1 h2 => ⟨hmem₁ a (by omega), by rw [rm₁]⟩
  have hL₁ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₁.nmem :=
    hL.congr fun a h1 h2 => hmem₁ a (by omega)
  -- the separator
  obtain ⟨c₂, t₂, e₂, ht₂, dk₂, m₂, o₂, -, -, -, -, -, -, hrec, hseg⟩ :=
    hsep l r π Hs σ d e b (b + 1) m en c₁ hin₁ hL₁ e₁.wb_right
      (by rw [f₁ _ (by omega) (by omega) (by omega), r4])
      (by rw [f₁ _ (by omega) (by omega) (by omega), r5]) a3 a65 heb (by omega) hroom'
  have hseg' := hseg
  obtain ⟨⟨g1, g2, g3, g4⟩, g5, g6⟩ := hseg
  obtain ⟨x1, -⟩ := hrec
  have hGb' : b + 1 ≤ c₂.nreg 6502 := by omega
  have hsz : c₂.nreg 6502 + 1 + 3 * π.segs.length + (π.segs.map SPath.k).sum ≤
      b + 1 + sR (l.piece ∪ r.piece).card m Hs.length := g5
  have r6₂ : c₂.nreg 3006 = b + 5 := by
    rw [dk₂ _ (by omega) (by omega), f₁ _ (by omega) (by omega) (by omega), r6]
  have hb₂ : c₂.nmem b = c.nreg 3003 := by
    rw [(m₂ b (by omega)).1, m₁, upd_same]
  -- the reading
  obtain ⟨c₃, t₃, e₃, ht₃, b0, b1, b2, b3, b4, b5, b6, b7, b8, fb, mb, rb, rmb, ob⟩ :=
    sgB_exec (P := I) c₂ e₂.wb_right r6₂ (by rw [g2]; omega)
  rw [g2] at b5 b6
  -- the sum of the lengths
  have hfK : ∀ j < π.segs.length, c₃.nmem (c₂.nreg 6502 + 1 + π.segs.length + j) =
      (π.segs.map SPath.k).getD j 0 := fun j hj => by
    rw [mb, (g4 j hj).2.1, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have hsumK : ∑ j ∈ range π.segs.length, (π.segs.map SPath.k).getD j 0 =
      (π.segs.map SPath.k).sum := by
    have := sum_range_getD (π.segs.map SPath.k)
    rw [List.length_map] at this
    exact this
  obtain ⟨c₄, t₄, e₄, ht₄, k7, fk, mk, rk, rmk, ok⟩ := sgKL_exec (P := I) c₃ e₃.wb_right
    (fun j => (π.segs.map SPath.k).getD j 0) b6 b8 b5 b2 b7 (by omega) hfK (by rw [hsumK]; omega)
  rw [hsumK] at k7
  -- the size
  obtain ⟨c₅, t₅, e₅, ht₅, z10, z8, fz, mz, rz, rmz, oz⟩ := sgC3_exec (P := I) c₄ e₄.wb_right
    (by rw [fk _ (by omega) (by omega) (by omega), b5]) k7
    (by rw [fk _ (by omega) (by omega) (by omega), b2]) (by omega)
  -- the copy
  obtain ⟨c₆, t₆, e₆, ht₆, cp, co, fc, rc, rmc, oc⟩ := sgML_exec (P := I) c₅ e₅.wb_right
    (b := b) (Gb := c₂.nreg 6502)
    (by rw [fz _ (by omega) (by omega), fk _ (by omega) (by omega) (by omega), b0])
    (by rw [fz _ (by omega) (by omega), fk _ (by omega) (by omega) (by omega), b4]) z8 z10
    (by rw [fz _ (by omega) (by omega), fk _ (by omega) (by omega) (by omega), b2])
    (by omega) (by omega)
  -- the registers
  have r₆ : ∀ x, x ≠ 8408 → x ≠ 8410 → x ≠ 8411 → x ≠ 8412 → x ≠ 8407 → x ≠ 8409 →
      c₆.nreg x = c₃.nreg x := fun x h1 h2 h3 h4 h5 h6 => by
    rw [fc x h1 h3 h4, fz x h1 h2, fk x h5 h1 h6]
  obtain ⟨c₇, t₇, e₇, ht₇, d07, d08, d06, d03, fd, md, rd, rmd, od⟩ := sgD_exec (P := I) c₆
    e₆.wb_right (b := b) (z := 3 * π.segs.length + (π.segs.map SPath.k).sum + 1)
    (h₀ := c.nreg 3003)
    (by rw [r₆ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b0])
    (by rw [fc _ (by omega) (by omega) (by omega)]; exact z10)
    (by rw [r₆ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b1])
    (by rw [r₆ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b3, hb₂])
    (by omega)
  have hmem₂ : ∀ a, a < b → c₇.nmem a = c.nmem a := fun a ha => by
    rw [md, co a (by omega), mz, mk, mb, (m₂ a (by omega)).1, hmem₁ a (by omega)]
  refine ⟨c₇, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))),
    b + (3 * π.segs.length + (π.segs.map SPath.k).sum + 1),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), ?_, by omega, ?_,
    fun x h1 h2 h3 => ?_, d06, ?_, fun a ha => ⟨hmem₂ a ha, ?_⟩, ?_, ?_⟩
  · have ht₂' : t₂ ≤ sT (l.piece ∪ r.piece).card Hs.length := ht₂
    show _ ≤ segT M sT sR (.node l r π, Hs, σ)
    unfold segT; simp only [ADec.piece]; rw [← hcard]
    omega
  · unfold segR; simp only [ADec.piece]; rw [← hcard]; omega
  · by_cases hx : x = 3003
    · subst hx; rw [d03]
    · rw [fd x (by omega) (by omega) h3 hx (by omega),
        r₆ x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        fb x (by omega), dk₂ x h1 h2, f₁ x hx (by omega) (by omega)]
  · rw [d08, r₆ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      fb _ (by omega), r6₂]
  · rw [rmd, rmc, rmz, rmk, rmb, (m₂ a (by omega)).2, rm₁]
  · rw [od, oc, oz, ok, ob, o₂, o₁]
  · show SegsOut' M en m π e (b + (3 * π.segs.length + (π.segs.map SPath.k).sum + 1))
      (c₇.nreg 6807) c₇.nmem
    rw [d07]
    refine SegsOut'.shift hseg' (fun a ha => ?_) heb (by omega)
    rw [md, cp a (by omega), mz, mk, mb]

end Spec

end MfDrv

end BKMNW

end PlanarFlow
