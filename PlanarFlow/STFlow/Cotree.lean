module

public import PlanarFlow.STFlow.Tree
public import PlanarFlow.BKMNW.Hassin

/-!
# The cotree: the edges off a spanning tree of the dual

On a plane map the edges that are not in a spanning tree `T*` of the dual graph form a spanning
tree `C` of the graph (interdigitating trees; von Staudt). We need three consequences, all proved
from the duality between cuts and cycles:

* `sum_face_cross`: **a cut is a dual circulation**: for a set `U` of vertices, the function
  `cross U` (`1` on the darts leaving `U`, `-1` on the darts entering it) has zero net flow around
  every face, because the boundary walk of a face leaves `U` as often as it enters it.
* `cotree_conn`: **`C` is connected**: otherwise the cut of a component is a nonzero dual
  circulation on the edges of `T*`, which a tree does not support
  (`PlanarFlow.STFlow.DTree.eq_zero_of_dualCirc`).
* `circ_eq_zero`: **`C` is acyclic**: a circulation vanishing on the edges of `T*` is the
  coboundary of a face potential (`PlanarFlow.CombMap.exists_int_potential`) which is constant
  along `T*`, hence zero.

Hence the path of `C` from `s` to `t` exists and is unique: `chi T s t` is the unit flow from `s`
to `t` vanishing on the edges of `T*` (`chi_spec`), and its values are at most `1`
(`le_one_of_unit`): a dart `d` of `C` separates `C` into two parts, and the value of `chi` on `d`
is the net flow out of the part of the tail of `d`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
/-- The darts leaving `U` count `1`, the darts entering `U` count `-1`. -/
def cross (U : Finset V) (d : D) : ℤ :=
  (if M.tail d ∈ U then 1 else 0) - (if M.head d ∈ U then 1 else 0)

lemma cross_antisymm (U : Finset V) : M.IsAntisymm (cross M U) := by
  intro d
  show (if M.tail (M.rev d) ∈ U then (1 : ℤ) else 0) - (if M.head (M.rev d) ∈ U then 1 else 0) =
    -((if M.tail d ∈ U then 1 else 0) - (if M.head d ∈ U then 1 else 0))
  rw [M.tail_rev, M.head_rev]; ring

/-- **A cut is a dual circulation**: the boundary walk of a face leaves `U` as often as it enters
it. -/
theorem sum_face_cross (U : Finset V) (x : F) : ∑ d with M.face d = x, cross M U d = 0 := by
  have hbij : Function.Bijective M.next := M.next_injective.bijective_of_finite
  have h : ∑ d with M.face d = x, (if M.head d ∈ U then (1 : ℤ) else 0) =
      ∑ d with M.face d = x, (if M.tail d ∈ U then (1 : ℤ) else 0) := by
    refine sum_equiv (Equiv.ofBijective _ hbij) (fun d => ?_) (fun d _ => ?_)
    · simp [M.face_next]
    · simp only [Equiv.ofBijective_apply, M.tail_next]; rfl
  simp only [cross, sum_sub_distrib, h, sub_self]

namespace DTree

variable (T : DTree M)

/-- `χ` vanishes on the edges of the tree. -/
def OffT (χ : D → ℤ) : Prop := ∀ d, T.InT d → χ d = 0

/-- **The cotree is acyclic**: a circulation vanishing on the edges of a spanning tree of the dual
vanishes (on a plane map). -/
theorem circ_eq_zero (hM : M.IsPlane) {κ : D → ℤ} (hκ : M.IsCirc κ) (hoff : T.OffT κ) (d : D) :
    κ d = 0 := by
  obtain ⟨ψ, hψ⟩ := exists_int_potential hM hκ
  have hc : ∀ x, x ≠ T.root → M.cob ψ (T.par x) = 0 := fun x hx => by
    rw [← hψ]; exact hoff _ (T.inT_par hx)
  rw [hψ]
  simp only [cob, T.pot_const hc, sub_self]

/-- Adjacency through a dart off the tree. -/
def CAdj (a b : V) : Prop := ∃ d, ¬ T.InT d ∧ M.tail d = a ∧ M.head d = b

/-- **The cotree is connected** (on a plane map). -/
theorem cotree_conn (hM : M.IsPlane) (a b : V) : Relation.ReflTransGen T.CAdj a b := by
  classical
  let U : Finset V := univ.filter fun v => Relation.ReflTransGen T.CAdj a v
  have hU : ∀ v, v ∈ U ↔ Relation.ReflTransGen T.CAdj a v := fun v => by simp [U]
  have hsupp : ∀ d, cross M U d ≠ 0 → T.InT d := by
    intro d hd
    by_contra hT
    apply hd
    have h1 : M.tail d ∈ U → M.head d ∈ U := fun h =>
      (hU _).2 (((hU _).1 h).tail ⟨d, hT, rfl, rfl⟩)
    have h2 : M.head d ∈ U → M.tail d ∈ U := fun h =>
      (hU _).2 (((hU _).1 h).tail ⟨M.rev d, fun h' => hT (T.inT_rev_iff.1 h'), rfl,
        by simp⟩)
    simp only [cross]
    by_cases ht : M.tail d ∈ U
    · simp [ht, h1 ht]
    · have : M.head d ∉ U := fun h => ht (h2 h)
      simp [ht, this]
  have hz := T.eq_zero_of_dualCirc (cross_antisymm U) hsupp (sum_face_cross U)
  have hstep : ∀ d, M.tail d ∈ U → M.head d ∈ U := fun d h => by
    have := hz d
    simp only [cross, h, ite_true] at this
    by_contra h'
    simp [h'] at this
  have ha : a ∈ U := (hU a).2 Relation.ReflTransGen.refl
  have hb : b ∈ U := by
    induction hM.conn a b with
    | refl => exact ha
    | tail _ hxy ih =>
      obtain ⟨d, rfl, rfl⟩ := hxy
      exact hstep d ih
  exact (hU b).1 hb

/-- A path flow along darts satisfying `A` vanishes on the darts `e` with neither `A e` nor
`A (rev e)`. -/
lemma pathFlow_zero {χ : D → ℤ} (hχ : M.IsAntisymm χ) {A : D → Prop}
    (hpos : ∀ d, 0 < χ d → A d) {e : D} (h1 : ¬ A e) (h2 : ¬ A (M.rev e)) : χ e = 0 := by
  rcases lt_trichotomy (χ e) 0 with h | h | h
  · have : 0 < χ (M.rev e) := by rw [hχ]; omega
    exact absurd (hpos _ this) h2
  · exact h
  · exact absurd (hpos _ h) h1

/-- A walk through the darts satisfying `A` gives a unit path flow, positive only on such
darts. -/
lemma exists_pathFlow_of {A : D → Prop} {p q : V}
    (h : Relation.ReflTransGen (fun a b => ∃ d, A d ∧ M.tail d = a ∧ M.head d = b) p q) :
    ∃ χ : D → ℤ, M.IsAntisymm χ ∧
      (∀ v, M.div χ v = (if p = v then 1 else 0) - (if q = v then 1 else 0)) ∧
      ∀ d, 0 < χ d → A d := by
  classical
  let u : D → ℤ := fun d => if A d then 1 else 0
  have hmono : Relation.ReflTransGen (ResAdj M u 0) p q := by
    refine Relation.ReflTransGen.mono (fun a b hab => ?_) _ _ h
    obtain ⟨d, hd, h1, h2⟩ := hab
    exact ⟨d, h1, h2, by simp [u, hd]⟩
  obtain ⟨χ, hχ, hdiv, hpos⟩ := exists_pathFlow hmono
  refine ⟨χ, hχ, hdiv, fun d hd => ?_⟩
  have := hpos d hd
  by_contra h'
  simp [u, h'] at this

/-- **The unit flow from `s` to `t` in the cotree** exists (on a plane map, `s ≠ t`). -/
theorem exists_unit (hM : M.IsPlane) {s t : V} :
    ∃ χ : D → ℤ, M.IsAntisymm χ ∧
      (∀ v, M.div χ v = (if s = v then 1 else 0) - (if t = v then 1 else 0)) ∧ T.OffT χ := by
  obtain ⟨χ, hχ, hdiv, hpos⟩ := exists_pathFlow_of (A := fun d => ¬ T.InT d) (T.cotree_conn hM s t)
  refine ⟨χ, hχ, hdiv, fun d hd => pathFlow_zero hχ hpos (by simpa using hd)
    (by simpa [T.inT_rev_iff] using hd)⟩

/-- **The values of a unit flow in the cotree are at most `1`**: the dart `d` separates the
cotree, and the value on `d` is the net flow out of the part of its tail. -/
theorem le_one_of_unit (hM : M.IsPlane) {s t : V} {χ : D → ℤ} (hχ : M.IsAntisymm χ)
    (hdiv : ∀ v, M.div χ v = (if s = v then 1 else 0) - (if t = v then 1 else 0))
    (hoff : T.OffT χ) (d : D) : χ d ≤ 1 := by
  classical
  by_cases hd : T.InT d
  · rw [hoff d hd]; omega
  let A : D → Prop := fun e => ¬ T.InT e ∧ e ≠ d ∧ e ≠ M.rev d
  let R : V → V → Prop := fun a b => ∃ e, A e ∧ M.tail e = a ∧ M.head e = b
  let U : Finset V := univ.filter fun v => Relation.ReflTransGen R (M.tail d) v
  have hU : ∀ v, v ∈ U ↔ Relation.ReflTransGen R (M.tail d) v := fun v => by simp [U]
  have hdd : d ≠ M.rev d := (M.rev_ne d).symm
  by_cases hh : M.head d ∈ U
  · -- a cycle through `d` in the cotree: impossible
    exfalso
    obtain ⟨π, hπ, hπdiv, hπpos⟩ := exists_pathFlow_of ((hU _).1 hh)
    let κ : D → ℤ := π - (Pi.single d 1 - Pi.single (M.rev d) 1)
    have hcirc : M.IsCirc κ := by
      refine ⟨fun e => ?_, fun v => ?_⟩
      · have h1 := hπ e
        have h2 := isAntisymm_dart (M := M) d e
        simp only [κ, Pi.sub_apply] at h1 h2 ⊢
        rw [h1, h2]; ring
      · simp only [κ]
        rw [div_sub, hπdiv, div_dart]; ring
    have hoffκ : T.OffT κ := by
      intro e he
      have h1 : π e = 0 := pathFlow_zero hπ hπpos (fun h => h.1 he)
        (fun h => h.1 (T.inT_rev he))
      have h2 : e ≠ d := fun h => hd (h ▸ he)
      have h3 : e ≠ M.rev d := fun h => hd (T.inT_rev_iff.1 (h ▸ he))
      simp [κ, h1, h2, h3]
    have hκd := T.circ_eq_zero hM hcirc hoffκ d
    have hπd : π d ≤ 0 := by
      by_contra h
      exact (hπpos d (by omega)).2.1 rfl
    simp only [κ, Pi.sub_apply, Pi.single_apply, ite_true, hdd, ite_false] at hκd
    omega
  · -- the net flow out of `U` is the value on `d`
    have hout := sum_div_eq_out hχ U
    have hrhs : ∑ e with M.tail e ∈ U ∧ M.head e ∉ U, χ e = χ d := by
      refine sum_eq_single d (fun e he hne => ?_) (fun h => absurd (by
        simp [(hU _).2 Relation.ReflTransGen.refl, hh]) h)
      simp only [mem_filter, mem_univ, true_and] at he
      by_contra h0
      have hT : ¬ T.InT e := fun h => h0 (hoff e h)
      have hre : e ≠ M.rev d := by
        rintro rfl
        exact hh (by simpa using he.1)
      exact he.2 ((hU _).2 (((hU _).1 he.1).tail ⟨e, ⟨hT, hne, hre⟩, rfl, rfl⟩))
    rw [hrhs] at hout
    simp only [hdiv, sum_sub_distrib, sum_ite_eq] at hout
    split_ifs at hout <;> omega

open Classical in
/-- **The path of the cotree from `s` to `t`**, as a unit flow vanishing on the edges of `T*`. -/
noncomputable def chi (s t : V) : D → ℤ :=
  if h : ∃ χ : D → ℤ, M.IsAntisymm χ ∧
      (∀ v, M.div χ v = (if s = v then 1 else 0) - (if t = v then 1 else 0)) ∧ T.OffT χ then
    h.choose else 0

/-- The specification of `chi`. -/
theorem chi_spec (hM : M.IsPlane) (s t : V) :
    M.IsAntisymm (T.chi s t) ∧
      (∀ v, M.div (T.chi s t) v = (if s = v then 1 else 0) - (if t = v then 1 else 0)) ∧
      T.OffT (T.chi s t) ∧ ∀ d, T.chi s t d ≤ 1 := by
  have hex := T.exists_unit hM (s := s) (t := t)
  have h : T.chi s t = hex.choose := by simp [chi, hex]
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  rw [h]
  exact ⟨h1, h2, h3, T.le_one_of_unit hM h1 h2 h3⟩

end DTree

end STFlow

end PlanarFlow
