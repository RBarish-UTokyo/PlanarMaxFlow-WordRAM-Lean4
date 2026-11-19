module

public import PlanarFlow.BKMNW.NcTfM
public import PlanarFlow.BKMNW.SgSem

/-!
# The flags of a part of the separator from its record `SegsOut'`

The record `SegsOut'` stores, with the darts of the parts (`SegsOut`), a frame dart with tail the first vertex
of every part (`SegsOut'`, `SgSem.lean`). With it, `tfP` run on the darts of the part `j`
(list base `Gb + 1 + 2 s + Σ_{j' < j} k_{j'}`, `K = k_j`) and the start dart
(`mem (Gb + 1 + 2 s + Σ k + j)`) gives the flags of the vertex set of the part in the piece map:

* `segsP_getElem_verts` (`(segsP h L hL)[j].verts = vimg … (L[j]).verts`);
* **`tfFlag_seg`** (the flag of `tfP` is `flagX (pmap h) (layEn …) (vimg … (π.segs[j]).verts)`),
  **`tfFlag_segsP`** (the same with the part of the piece map, `(segsP h π.segs hin)[j].verts`, the
  `πj` of `xCtxN`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap MfDrv NsStep StCall OrbLab

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- The vertex set of a part of the piece map. -/
lemma segsP_getElem_verts {P : Finset D} {Hs : List (Finset V)} {σ : Perm D}
    (h : PieceInv M P Hs σ) (L : List (SPath M)) (hL : ∀ π ∈ L, SegIn M P Hs π) {j : ℕ}
    (hj : j < (segsP h L hL).length) (hj' : j < L.length) :
    (segsP h L hL)[j].verts = vimg M σ (pdarts M P Hs) (L[j]).verts := by
  have e := congrArg (fun l => l[j]?) (segsP_verts h L hL)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj',
    Option.map_some, Option.some.injEq] at e
  exact e

/-- **The flags of `tfP` for the part `j` of the separator, from `SegsOut'`.** -/
theorem tfFlag_seg {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2) (hm : 0 < m)
    {π : HSep M} {lo hi Gb : ℕ} {mem' : ℕ → ℕ} (hS : SegsOut' M en m π lo hi Gb mem')
    {j : ℕ} (hj : j < π.segs.length) (hX : Disjoint (π.segs[j]).verts (hunion x.2.1))
    {LABb RVb : ℕ} (hLAB : ∀ i < m, mem' (LABb + i) = olab (sgF d m mem) i + 1)
    (hRV : ∀ i < m, mem' (RVb + i) = mem (d + 4 + m + i)) {i : ℕ} (hi : i < m) :
    tfFlag mem' LABb (Gb + 1 + 2 * π.segs.length + ((π.segs.take j).map SPath.k).sum) RVb
        (π.segs[j]).k
        (mem' (Gb + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum + j)) (mem' (LABb + i)) =
      flagX (pmap h) (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm)
        (vimg M x.2.2 (pdarts M x.1.piece x.2.1) (π.segs[j]).verts) i := by
  obtain ⟨⟨-, -, -, h4⟩, -, h6⟩ := hS
  obtain ⟨-, -, g3⟩ := h4 j hj
  obtain ⟨s1, s2⟩ := h6 j hj
  exact tfFlag_path hL h hm (π.segs[j]) hX hLAB g3 hRV s1 s2 hi

/-- **The flags of `tfP` for the part `j` are those of the part `πj` of the step** (`xCtxN`'s
`L = segsP h π.segs hin`). -/
theorem tfFlag_segsP {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2) (hm : 0 < m)
    {π : HSep M} (hin : ∀ s ∈ π.segs, SegIn M x.1.piece x.2.1 s)
    {lo hi Gb : ℕ} {mem' : ℕ → ℕ} (hS : SegsOut' M en m π lo hi Gb mem')
    {j : ℕ} (hj : j < (segsP h π.segs hin).length)
    {LABb RVb : ℕ} (hLAB : ∀ i < m, mem' (LABb + i) = olab (sgF d m mem) i + 1)
    (hRV : ∀ i < m, mem' (RVb + i) = mem (d + 4 + m + i)) {i : ℕ} (hi : i < m) :
    tfFlag mem' LABb (Gb + 1 + 2 * π.segs.length + ((π.segs.take j).map SPath.k).sum) RVb
        (π.segs[j]'(by rw [← length_segsP h π.segs hin]; exact hj)).k
        (mem' (Gb + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum + j)) (mem' (LABb + i)) =
      flagX (pmap h) (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm)
        ((segsP h π.segs hin)[j]).verts i := by
  have hj' : j < π.segs.length := by rw [← length_segsP h π.segs hin]; exact hj
  rw [segsP_getElem_verts h π.segs hin hj hj']
  exact tfFlag_seg hL h hm hS hj' (hin _ (List.getElem_mem hj')).2.2 hLAB hRV hi

end NcStep

end BKMNW

end PlanarFlow
