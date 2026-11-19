module

public import PlanarFlow.BKMNW.PpLoop
public import PlanarFlow.BKMNW.StMapF

/-!
# The drawing's encoding: the index-level functions of the preprocessed map

The input of the maximum-flow pipeline is the encoding of a plane map of `PlanarFlow/Spec.lean`
(`Feas`: `nv`, `nf`, `nd`, for every dart `tl`, `rv`, `fc`, `nx`, `cp`, for every vertex `bp`, `bn`),
read as a maximum-flow instance: capacities `cp`, sources the vertices with `bp ≠ 0`, sinks those
with `bn ≠ 0` (`srcF`, `snkF`). `MEnc d W` asks for a plane map without loops with transitive
rotations and faces, disjoint terminals and words at most `W`.

For `M = Feas.map wf` without loops, the index-level functions of `PpIdx.lean` are those of the
words: `rvI = rv`, `sgI x = nx (rv x)`, `phI = nx`, `flI = olab nx`, `piI (nx y) = y`,
`vminI = olab (nx ∘ rv)` (by the transitivity of the rotations), and the flags.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Function Equiv Orbit CombMap Feas OrbLab

/-- The sources of the instance: the vertices with `bp ≠ 0`. -/
def srcF (d : List ℕ) : Finset (Fin (nv d)) := univ.filter fun v => bp d v ≠ 0

/-- The sinks of the instance: the vertices with `bn ≠ 0`. -/
def snkF (d : List ℕ) : Finset (Fin (nv d)) := univ.filter fun v => bn d v ≠ 0

/-- The rotation at index level: `rot x = nx (rv x)`. -/
def rotW (d : List ℕ) (x : ℕ) : ℕ := nx d (rv d x)

/-- **A maximum-flow instance in the drawing's encoding**, for the word bound `W`. -/
structure MEnc (d : List ℕ) (W : ℕ) : Prop where
  wf : Wf d
  plane : (map wf).IsPlane
  rotT : ∀ i < nd d, ∀ j < nd d, tl d i = tl d j → ∃ k, (rotW d)^[k] i = j
  faceT : ∀ i < nd d, ∀ j < nd d, fc d i = fc d j → ∃ k, (nx d)^[k] i = j
  loopless : ∀ i < nd d, tl d (rv d i) ≠ tl d i
  disj : ∀ v < nv d, bp d v = 0 ∨ bn d v = 0
  word_le : ∀ i, word d i ≤ W

section Map

variable {d : List ℕ} (wf : Wf d)

lemma map_rev_val (x : Fin (nd d)) : ((map wf).rev x).val = rv d x := rfl
lemma map_tail_val (x : Fin (nd d)) : ((map wf).tail x).val = tl d x := rfl
lemma map_next_val (x : Fin (nd d)) : ((map wf).next x).val = nx d x := rfl
lemma map_rot_val (x : Fin (nd d)) : ((map wf).rot x).val = rotW d x := rfl
lemma map_face_val (x : Fin (nd d)) : ((map wf).face x).val = fc d x := rfl

lemma map_rot_iter (x : Fin (nd d)) (k : ℕ) : (((map wf).rot)^[k] x).val = (rotW d)^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply, iterate_succ_apply, ih, map_rot_val]

lemma map_next_iter (x : Fin (nd d)) (k : ℕ) : (((map wf).next)^[k] x).val = (nx d)^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply, iterate_succ_apply, ih, map_next_val]

lemma map_rotTrans (h : ∀ i < nd d, ∀ j < nd d, tl d i = tl d j → ∃ k, (rotW d)^[k] i = j) :
    (map wf).RotTrans := fun a b hab => by
  obtain ⟨k, hk⟩ := h a a.2 b b.2 (congrArg Fin.val hab)
  exact ⟨k, Fin.ext (by rw [map_rot_iter, hk])⟩

lemma map_faceTrans (h : ∀ i < nd d, ∀ j < nd d, fc d i = fc d j → ∃ k, (nx d)^[k] i = j) :
    (map wf).FaceTrans := fun a b hab => by
  obtain ⟨k, hk⟩ := h a a.2 b b.2 (congrArg Fin.val hab)
  exact ⟨k, Fin.ext (by rw [map_next_iter, hk])⟩

omit wf in
lemma nx_permOn (wf' : Wf d) : PermOn (nx d) (nd d) :=
  ⟨fun x hx => wf'.nx_lt x hx, fun x hx y hy e => wf'.nx_inj x hx y hy e⟩

omit wf in
lemma rotW_permOn (wf' : Wf d) : PermOn (rotW d) (nd d) :=
  ⟨fun x hx => wf'.nx_lt _ (wf'.rv_lt x hx), fun x hx y hy e => by
    have := wf'.nx_inj _ (wf'.rv_lt x hx) _ (wf'.rv_lt y hy) e
    rw [← wf'.rv_rv x hx, ← wf'.rv_rv y hy, this]⟩

variable (hl : ∀ i < nd d, tl d (rv d i) ≠ tl d i)
include hl

lemma map_loopless (x : Fin (nd d)) : (map wf).head x ≠ (map wf).tail x := fun h =>
  hl x x.2 (congrArg Fin.val h)

lemma nlDarts_map : nlDarts (map wf) = univ := by
  ext x; simp only [mem_nlDarts, mem_univ, iff_true]; exact map_loopless wf hl x

lemma isNl_map {x : ℕ} : IsNl (map wf) x ↔ x < nd d :=
  ⟨fun h => h.1, fun h => ⟨h, by rw [nlDarts_map wf hl]; exact mem_univ _⟩⟩

lemma nlRot_map : nlRot (map wf) = rotPerm (map wf) := by
  unfold nlRot; rw [nlDarts_map wf hl, ret_univ]

lemma rvI_map {x : ℕ} (hx : x < nd d) : rvI (map wf) x = rv d x := by
  rw [show x = ((⟨x, hx⟩ : Fin (nd d)) : ℕ) from rfl, rvI_fin]; rfl

lemma sgI_map {x : ℕ} (hx : x < nd d) : sgI (map wf) x = rotW d x := by
  rw [show x = ((⟨x, hx⟩ : Fin (nd d)) : ℕ) from rfl,
    sgI_fin _ ((isNl_fin _).1 ((isNl_map wf hl).2 hx)), nlRot_map wf hl]; rfl

lemma phI_map {x : ℕ} (hx : x < nd d) : phI (map wf) x = nx d x := by
  rw [show x = ((⟨x, hx⟩ : Fin (nd d)) : ℕ) from rfl,
    phI_fin _ ((isNl_fin _).1 ((isNl_map wf hl).2 hx)), nlRot_map wf hl]
  show nx d (rv d (rv d x)) = nx d x
  rw [wf.rv_rv x hx]


lemma flI_map {x : ℕ} (hx : x < nd d) : flI (map wf) x = olab (nx d) x :=
  StEnc.olab_congr (phI_permOn _) (fun y hy => phI_map wf hl hy) hx

lemma piI_map {y : ℕ} (hy : y < nd d) : piI (map wf) (nx d y) = y := by
  have hx : nx d y < nd d := wf.nx_lt y hy
  have hn : IsNl (map wf) (nx d y) := (isNl_map wf hl).2 hx
  have hpl : piI (map wf) (nx d y) < nd d := by
    unfold piI; rw [ppDiteT hn]; exact Fin.isLt _
  have key : phI (map wf) (piI (map wf) (nx d y)) = nx d y := by
    unfold piI; rw [ppDiteT hn, phI_phi]
    simp
  rw [phI_map wf hl hpl] at key
  exact wf.nx_inj _ hpl _ hy key

lemma piI_lt_map {x : ℕ} (hx : x < nd d) : piI (map wf) x < nd d := by
  have hn : IsNl (map wf) x := (isNl_map wf hl).2 hx
  unfold piI; rw [ppDiteT hn]; exact Fin.isLt _

lemma vminI_map (hrot : (map wf).RotTrans) {x : ℕ} (hx : x < nd d) :
    vminI (map wf) x = olab (rotW d) x := by
  classical
  have hP := rotW_permOn wf
  unfold vminI; rw [ppDiteT hx]
  have hex := exists_nl_tail (map wf) ((nlMap (map wf)).tail ⟨⟨x, hx⟩, by
    rw [nlDarts_map wf hl]; exact mem_univ _⟩)
  rw [nlVert_tail] at hex
  obtain ⟨hv1, hv2⟩ := vminV_spec (map wf) hex
  apply le_antisymm
  · obtain ⟨t, ht⟩ := olab_mem (rotW d) x
    refine vminV_min (map wf) hex ((isNl_map wf hl).2 (olab_lt hP hx)) ?_
    have e : ((((map wf).rot)^[t] ⟨x, hx⟩ : Fin (nd d)) : ℕ) = (rotW d)^[t] x :=
      map_rot_iter wf _ t
    rw [← ht, ← e, tlF_fin]
    simp only [Option.some.injEq]
    exact tail_rot_iterate _ _
  · have hlt := hv1.lt
    have htl : (map wf).tail ⟨vminV (map wf) ((map wf).tail ⟨x, hx⟩), hlt⟩ =
        (map wf).tail ⟨x, hx⟩ := by
      have := hv2
      rw [show vminV (map wf) ((map wf).tail ⟨x, hx⟩) =
        ((⟨vminV (map wf) ((map wf).tail ⟨x, hx⟩), hlt⟩ : Fin (nd d)) : ℕ) from rfl,
        tlF_fin] at this
      exact Option.some.inj this
    obtain ⟨k, hk⟩ := hrot _ _ htl.symm
    have e1 := congrArg Fin.val hk
    rw [map_rot_iter] at e1
    have e2 : (rotW d)^[k] x = vminV (map wf) ((map wf).tail ⟨x, hx⟩) := e1
    rw [← e2]; exact olab_min _ _ _

lemma cvI_map (hrot : (map wf).RotTrans) {x : ℕ} (hx : x < nd d) :
    CvI (map wf) x ↔ olab (rotW d) x = x := by
  unfold CvI; rw [vminI_map wf hl hrot hx]
  exact ⟨fun h => h.2, fun h => ⟨(isNl_map wf hl).2 hx, h⟩⟩

lemma cfI_map {x : ℕ} (hx : x < nd d) : CfI (map wf) x ↔ olab (nx d) x = x := by
  unfold CfI; rw [flI_map wf hl hx]
  exact ⟨fun h => h.2, fun h => ⟨(isNl_map wf hl).2 hx, h⟩⟩

omit hl in
lemma tlIn_map (X : Finset (Fin (nv d))) {x : ℕ} (hx : x < nd d) :
    TlIn (map wf) X x ↔ (⟨tl d x, wf.tl_lt x hx⟩ : Fin (nv d)) ∈ X :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨hx, h⟩⟩

omit hl in
lemma tlIn_src {x : ℕ} (hx : x < nd d) : TlIn (map wf) (srcF d) x ↔ bp d (tl d x) ≠ 0 := by
  rw [tlIn_map wf _ hx]; simp [srcF]

omit hl in
lemma tlIn_snk {x : ℕ} (hx : x < nd d) : TlIn (map wf) (snkF d) x ↔ bn d (tl d x) ≠ 0 := by
  rw [tlIn_map wf _ hx]; simp [snkF]

omit hl in
lemma xt_tl {x : ℕ} (hx : x < nd d) :
    xt (fun e => ((map wf).tail e : ℕ)) x = tl d x := by
  rw [show x = ((⟨x, hx⟩ : Fin (nd d)) : ℕ) from rfl, xt_fin]; rfl

omit hl in
lemma xt_cp {x : ℕ} (hx : x < nd d) : xt (fun e : Fin (nd d) => cp d e) x = cp d x := by
  rw [show x = ((⟨x, hx⟩ : Fin (nd d)) : ℕ) from rfl, xt_fin]

end Map

end Pp

end BKMNW

end PlanarFlow
