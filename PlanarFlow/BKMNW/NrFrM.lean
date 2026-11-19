module

public import PlanarFlow.BKMNW.NrFrL
public import PlanarFlow.BKMNW.NpStep

/-!
# The push-backs `retP`, `frmP`: the parts with their start vertex; the inputs of `pchP`

* **`SegsOutV`**, **`SegsAtV`**: `SegsOut`/`SegsAt` with the **start vertex of every part** (a frame
  dart index whose tail is `segs[j].p 0`, at `Gb + 1 + 2 s + L + j`, `L = Σ k`; the layout of
  `SegsOut'`, `SgX.lean` in `h_r4`); `SegsAtV.toS`, `SegsAtV.congr`;
* `Lay.tail_mem_vimg` (a vertex of the piece map is in `vimg X` iff the tail is in `X`, for `X` off
  the holes), `Lay.vl_eq_iff_tail` (same vertex label iff same tail, for a tail off the holes),
  `spath_mem_verts_iff`, `xCtxN_L_verts` (the part `j` of the step is `vimg` of `segs[j]`);
* **`Lay.mem_part_iff`**: the vertex of `en i` is on the part `j` iff its label is the label of the
  start dart or of the reverse of a dart of the part;
* **`btVal`**: the word `Kd + β` of the push-back from the sinks (`β = 0` on
  `negSet g πj.verts`, `div g` elsewhere) from `Kd + div g` and the part flag.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap OrbLab WordRAM WordRAM.Machine

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-! ### The parts with their start vertex -/

variable (M) in
/-- **`SegsOut` with the start vertex of every part**: at `Gb + 1 + 2 s + L + j` (`L` the number
of darts of all the parts) a frame dart index whose tail is the first vertex of the part `j`. -/
def SegsOutV (en : ℕ → D) (m : ℕ) (π : HSep M) (lo hi Gb : ℕ) (mem : ℕ → ℕ) : Prop :=
  SegsOut M en m π lo hi Gb mem ∧
    Gb + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum + π.segs.length ≤ hi ∧
    ∀ (j : ℕ) (hj : j < π.segs.length),
      mem (Gb + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum + j) < m ∧
      M.tail (en (mem (Gb + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum + j))) =
        (π.segs[j]).p 0

variable (M) in
/-- **`SegsAt` with the start vertex of every part** (base in `r6807`). -/
def SegsAtV (en : ℕ → D) (m : ℕ) (π : HSep M) (e b : ℕ) (c : Config) : Prop :=
  SegsOutV M en m π e b (c.nreg 6807) c.nmem

lemma SegsAtV.toS {en : ℕ → D} {m : ℕ} {π : HSep M} {e b : ℕ} {c : Config}
    (h : SegsAtV M en m π e b c) : SegsAt M en m π e b c := h.1

lemma SegsAtV.congr {en : ℕ → D} {m : ℕ} {π : HSep M} {e b : ℕ} {c c' : Config}
    (h : SegsAtV M en m π e b c) (hr : c'.nreg 6807 = c.nreg 6807)
    (he : ∀ a, e ≤ a → a < b → c'.nmem a = c.nmem a) : SegsAtV M en m π e b c' := by
  obtain ⟨h1, h2, h3⟩ := h
  have hS : SegsAt M en m π e b c' := SegsAt.congr (en := en) h1 hr he
  have hlo : e ≤ c.nreg 6807 := h1.1
  refine ⟨hS, by rw [hr]; exact h2, fun j hj => ?_⟩
  rw [hr, he _ (by omega) (by omega)]
  exact h3 j hj

/-! ### Vertices of the piece map from the frame -/

lemma hRel_symm' {Hs : List (Finset V)} {a b : V} (h : HRel Hs a b) : HRel Hs b a := by
  rcases h with rfl | ⟨H, hH, ha, hb⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨H, hH, hb, ha⟩

/-- **A vertex of the piece map is in `vimg X` iff the tail is in `X`** (`X` off the holes). -/
lemma Lay.tail_mem_vimg {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    {X : Finset V} (hX : Disjoint X (hunion x.2.1)) {i : ℕ} (hi : i < m) :
    (pmap h).tail (vDart hL hi) ∈ vimg M x.2.2 (pdarts M x.1.piece x.2.1) X ↔ M.tail (en i) ∈ X := by
  rw [pmap_tail, mk_mem_vimg h]
  constructor
  · rintro ⟨y, hyB, hy, hr⟩
    have := (hRel_of_not_mem (disjoint_left.1 hX hy)).1 hr
    show M.tail (en i) ∈ X
    have e : (vDart hL hi).1 = en i := rfl
    rw [e] at this; rw [this]; exact hy
  · intro hx
    exact ⟨en i, hL.en_mem i hi, hx, Or.inl rfl⟩

/-- **Same vertex label iff same tail**, for a tail off the holes. -/
lemma Lay.vl_eq_iff_tail {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    {i j : ℕ} (hi : i < m) (hj : j < m) (hn : M.tail (en j) ∉ hunion x.2.1) :
    olab (sgF d m mem) i = olab (sgF d m mem) j ↔ M.tail (en i) = M.tail (en j) := by
  rw [← hL.vert_eq_iff h hi hj, pmap_tail, pmap_tail, sVert_eq_iff]
  show x.2.2.SameCycle (en i) (en j) ↔ _
  rw [h.vert _ (hL.en_mem i hi) _ (hL.en_mem j hj)]
  constructor
  · intro hr; exact (hRel_of_not_mem hn).1 (hRel_symm' hr)
  · intro e; rw [e]; exact Or.inl rfl

lemma spath_mem_verts_iff (P : SPath M) {v : V} :
    v ∈ P.verts ↔ v = P.p 0 ∨ ∃ l < P.k, v = M.head (P.d l) := by
  rw [SPath.verts, SPath.mem_init]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases t with _ | l
    · exact Or.inl rfl
    · exact Or.inr ⟨l, by omega, (P.head_d l (by omega)).symm⟩
  · rintro (rfl | ⟨l, hl, rfl⟩)
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨l + 1, by omega, (P.head_d l hl).symm⟩

/-- **The part `j` of the step** is the image of `segs[j]`. -/
lemma xCtxN_L_verts (NF : NFam M) (u : D → ℤ) (S T : Finset V) {l r : ADec M} {π : HSep M}
    {Hs : List (Finset V)} {σ : Perm D} (h : SCond M l r π Hs σ) {j : ℕ}
    {πj : SPath (pmap h.1)} (hj : (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj) :
    ∃ hj' : j < π.segs.length,
      πj.verts = vimg M σ (pdarts M (l.piece ∪ r.piece) Hs) (π.segs[j]).verts := by
  have e1 := segsP_verts h.1 π.segs h.2
  have hlen := length_segsP h.1 π.segs h.2
  have hL : (xCtxN M NF u S T l r π Hs σ h).L = segsP h.1 π.segs h.2 := rfl
  rw [hL] at hj
  have hjl : j < (segsP h.1 π.segs h.2).length := by
    by_contra hn; rw [List.getElem?_eq_none (by omega)] at hj; simp at hj
  refine ⟨by omega, ?_⟩
  have e2 := congrArg (fun L => L[j]?) e1
  simp only [List.getElem?_map, hj, List.getElem?_eq_getElem (show j < π.segs.length by omega),
    Option.map_some, Option.some.injEq] at e2
  exact e2

/-- **The vertex of `en i` is on the part `j`** iff its label is the label of the start dart or
of the reverse of a dart of the part. -/
theorem Lay.mem_part_iff {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    {P : SPath M} (hP : Disjoint P.verts (hunion x.2.1)) {st : ℕ} (hst : st < m)
    (hst' : M.tail (en st) = P.p 0) {E : ℕ → ℕ} (hE : ∀ l < P.k, E l < m ∧ en (E l) = P.d l)
    {i : ℕ} (hi : i < m) :
    (pmap h).tail (vDart hL hi) ∈ vimg M x.2.2 (pdarts M x.1.piece x.2.1) P.verts ↔
      olab (sgF d m mem) i = olab (sgF d m mem) st ∨
        ∃ l < P.k, olab (sgF d m mem) i = olab (sgF d m mem) (mem (d + 4 + m + E l)) := by
  rw [hL.tail_mem_vimg h hP hi, spath_mem_verts_iff P]
  have h0 : M.tail (en st) ∉ hunion x.2.1 := by
    rw [hst']; exact disjoint_left.1 hP (P.p_mem_init (Nat.zero_le _))
  rw [hL.vl_eq_iff_tail h hi hst h0, hst']
  apply or_congr Iff.rfl
  apply exists_congr; intro l
  apply and_congr_right; intro hl
  obtain ⟨e1, e2⟩ := hE l hl
  obtain ⟨r1, r2⟩ := hL.rv _ e1
  have hh : M.tail (en (mem (d + 4 + m + E l))) = M.head (P.d l) := by
    rw [r2, e2]; rfl
  have hn : M.tail (en (mem (d + 4 + m + E l))) ∉ hunion x.2.1 := by
    rw [hh, P.head_d l hl]; exact disjoint_left.1 hP (P.p_mem_init (by omega))
  rw [hL.vl_eq_iff_tail h hi r1 hn, hh]

/-! ### The words of the bounds -/

/-- **The word of the bound of the push-back from the sinks**: from `a = Kd + div` and the part
flag `p`, `a - p (a - Kd) = Kd + (if p = 1 ∧ 0 < div then 0 else div)`. -/
lemma btVal {a Kd p : ℕ} {dv : ℤ} (ha : (a : ℤ) = Kd + dv) (hp : p ≤ 1) :
    ((a - p * (a - Kd) : ℕ) : ℤ) = Kd + (if p = 1 ∧ 0 < dv then 0 else dv) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hp with rfl | rfl
  · simp only [zero_mul, Nat.sub_zero, zero_ne_one, false_and, ite_false]; exact ha
  · simp only [one_mul, true_and]
    split_ifs with h <;> omega

end MfDrv

end BKMNW

end PlanarFlow
