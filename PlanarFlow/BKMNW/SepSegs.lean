module

public import PlanarFlow.BKMNW.SepPX

/-!
# The parts of the separator in the output of the separator program (layout for the node step)

The node step (`cntP`, the hole loop) needs, at a node call, the number of parts `π.segs.length`
of the separator and each part as frame dart indices. `SepPSpecX` does not output them.
**`SegsOut`** fixes their layout, from a base `Gb` (returned in `r6502`) placed after the
children's records (`Xb + 2 + zl + zr ≤ Gb`, `Xb = r6501`):

* `mem Gb = s = π.segs.length`;
* `mem (Gb + 1 + j)` = the offset `o_j = Σ_{j' < j} k_{j'}` of the part `j` (`j < s`);
* `mem (Gb + 1 + s + j) = k_j` (its number of darts);
* `mem (Gb + 1 + 2 s + o_j + l)` (`l < k_j`) = the frame index `i < m` of its `l`-th dart:
  `en i = (π.segs[j]).d l`;
* the whole block below `hi = Sb + sR n m k`.

* `SegsOut`, `SegsOut.congr`;
* **`SepPSpecXS`** / **`SepPSpecXLS`**: `SepPSpecX` / `SepPSpecXL` with the parts `SegsOut` in the
  output; `SepPSpecXS.toX`, `SepPSpecXLS.toXL` (forget them).

This file does not prove that `sepSm` or `sepL` meets the primed specifications:
it only fixes the interface that the node step uses.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **The parts of the separator as frame dart indices** from `Gb` (see the module docstring). -/
def SegsOut (en : ℕ → D) (m : ℕ) (π : HSep M) (lo hi Gb : ℕ) (mem : ℕ → ℕ) : Prop :=
  lo ≤ Gb ∧ mem Gb = π.segs.length ∧
    Gb + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum ≤ hi ∧
    ∀ (j : ℕ) (hj : j < π.segs.length),
      mem (Gb + 1 + j) = ((π.segs.take j).map SPath.k).sum ∧
      mem (Gb + 1 + π.segs.length + j) = (π.segs[j]).k ∧
      ∀ l < (π.segs[j]).k,
        mem (Gb + 1 + 2 * π.segs.length + ((π.segs.take j).map SPath.k).sum + l) < m ∧
        en (mem (Gb + 1 + 2 * π.segs.length + ((π.segs.take j).map SPath.k).sum + l)) =
          (π.segs[j]).d l

lemma sum_take_le_sum (L : List ℕ) (j : ℕ) : (L.take j).sum ≤ L.sum := by
  conv_rhs => rw [← List.take_append_drop j L]
  rw [List.sum_append]; omega

/-- `SegsOut` depends only on the memory in `[Gb, hi)`. -/
lemma SegsOut.congr {en : ℕ → D} {m : ℕ} {π : HSep M} {lo hi Gb : ℕ} {mem mem' : ℕ → ℕ}
    (h : SegsOut M en m π lo hi Gb mem) (he : ∀ a, Gb ≤ a → a < hi → mem' a = mem a) :
    SegsOut M en m π lo hi Gb mem' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, by rw [he _ le_rfl (by omega)]; exact h2, h3, fun j hj => ?_⟩
  obtain ⟨g1, g2, g3⟩ := h4 j hj
  have hk : ((π.segs.take j).map SPath.k).sum + (π.segs[j]).k ≤ (π.segs.map SPath.k).sum := by
    have e : π.segs.take (j + 1) = π.segs.take j ++ [π.segs[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    have := sum_take_le_sum (π.segs.map SPath.k) (j + 1)
    rw [← List.map_take, e, List.map_append, List.sum_append] at this
    simpa using this
  refine ⟨by rw [he _ (by omega) (by omega)]; exact g1, by rw [he _ (by omega) (by omega)]; exact g2,
    fun l hl => ?_⟩
  rw [he _ (by omega) (by omega)]
  exact g3 l hl

variable (M) in
/-- **`SepPSpecX` with the parts of the separator** (`SegsOut` from `r6502`, after the children's
records). -/
def SepPSpecXS (ds : DSys M) (Reach : MCall M → Prop) (gid : D → ℕ) (ν : V → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (sepP : Stmt) (sT : ℕ → ℕ → ℕ)
    (sR : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e h Sb m : ℕ)
    (en : ℕ → D) (c : Config),
    FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem → WordsBounded W c →
    c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3003 = h → c.nreg 6500 = Sb → e ≤ h → h < Sb →
    Sb + sR (l.piece ∪ r.piece).card m Hs.length ≤ W →
    ∃ c' t, Exec I W sepP c c' t ∧ t ≤ sT (l.piece ∪ r.piece).card Hs.length ∧ DRegKeep c c' ∧
      (∀ a < Sb, c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ i < m, c'.nmem (Sb + i) = bf (en i ∈ l.piece)) ∧
      (∀ i < m, c'.nmem (Sb + m + i) = bf (en i ∈ π.path.darts.toFinset)) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = bf (M.tail (en i) ∈ π.path.mverts)) ∧
      (∀ j < Hs.length, c'.nmem (Sb + 3 * m + j) =
        bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
      c'.nmem (Sb + 3 * m + Hs.length) = ntag l ∧ c'.nmem (Sb + 3 * m + Hs.length + 1) = ntag r ∧
      RecsOut M ds gid ν S T l r π Hs σ (Sb + 21 * m + 4 * Hs.length + 2)
        (Sb + sR (l.piece ∪ r.piece).card m Hs.length) (c'.nreg 6501) c'.nmem ∧
      SegsOut M en m π (c'.nreg 6501 + 2 + c'.nmem (c'.nreg 6501) +
        c'.nmem (c'.nreg 6501 + 1)) (Sb + sR (l.piece ∪ r.piece).card m Hs.length)
        (c'.nreg 6502) c'.nmem

variable (M) in
/-- **`SepPSpecXL` with the parts of the separator.** -/
def SepPSpecXLS (ds : DSys M) (Reach : MCall M → Prop) (gid : D → ℕ) (ν : V → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (sepL : Stmt) (sT : ℕ → ℕ → ℕ)
    (sR : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e h Sb m : ℕ)
    (en : ℕ → D) (c : Config),
    FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem →
    c.nmem (c.nmem (d + fsz m) + 1) = 0 → ds.s < c.nmem (c.nmem (d + fsz m)) →
    WordsBounded W c →
    c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3003 = h → c.nreg 6500 = Sb → e ≤ h → h < Sb →
    Sb + sR (l.piece ∪ r.piece).card m Hs.length ≤ W →
    ∃ c' t, Exec I W sepL c c' t ∧ t ≤ sT (l.piece ∪ r.piece).card Hs.length ∧ DRegKeep c c' ∧
      (∀ a < Sb, c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ i < m, c'.nmem (Sb + i) = bf (en i ∈ l.piece)) ∧
      (∀ i < m, c'.nmem (Sb + m + i) = bf (en i ∈ π.path.darts.toFinset)) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = bf (M.tail (en i) ∈ π.path.mverts)) ∧
      (∀ j < Hs.length, c'.nmem (Sb + 3 * m + j) =
        bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
      c'.nmem (Sb + 3 * m + Hs.length) = ntag l ∧ c'.nmem (Sb + 3 * m + Hs.length + 1) = ntag r ∧
      RecsOut M ds gid ν S T l r π Hs σ (Sb + 21 * m + 4 * Hs.length + 2)
        (Sb + sR (l.piece ∪ r.piece).card m Hs.length) (c'.nreg 6501) c'.nmem ∧
      SegsOut M en m π (c'.nreg 6501 + 2 + c'.nmem (c'.nreg 6501) +
        c'.nmem (c'.nreg 6501 + 1)) (Sb + sR (l.piece ∪ r.piece).card m Hs.length)
        (c'.nreg 6502) c'.nmem

variable {ds : DSys M} {Reach : MCall M → Prop} {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ}
  {S T : Finset V} {Z : ℕ} {I : Input} {W : ℕ} {sT : ℕ → ℕ → ℕ} {sR : ℕ → ℕ → ℕ → ℕ}

/-- Forgetting the parts. -/
lemma SepPSpecXS.toX {sepP : Stmt} (h : SepPSpecXS M ds Reach gid ν u S T Z I W sepP sT sR) :
    SepPSpecX M ds Reach gid ν u S T Z I W sepP sT sR := by
  intro l r π Hs σ d e h' Sb m en c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨c', t, e', ht, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -⟩ :=
    h l r π Hs σ d e h' Sb m en c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  exact ⟨c', t, e', ht, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩

/-- Forgetting the parts. -/
lemma SepPSpecXLS.toXL {sepL : Stmt} (h : SepPSpecXLS M ds Reach gid ν u S T Z I W sepL sT sR) :
    SepPSpecXL M ds Reach gid ν u S T Z I W sepL sT sR := by
  intro l r π Hs σ d e h' Sb m en c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  obtain ⟨c', t, e', ht, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -⟩ :=
    h l r π Hs σ d e h' Sb m en c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact ⟨c', t, e', ht, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩

end MfDrv

end BKMNW

end PlanarFlow
