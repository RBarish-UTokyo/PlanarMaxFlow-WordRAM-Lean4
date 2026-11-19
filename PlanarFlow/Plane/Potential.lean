module

public import PlanarFlow.Plane.Map
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Cast.Order

/-!
# Circulations on a plane map are coboundaries of face potentials

On any combinatorial map the coboundary `cob φ d = φ (face (rev d)) - φ (face d)` of a function
`φ` on the faces is a circulation (`PlanarFlow.CombMap.isCirc_cob`). On a *plane* map the converse
holds: every circulation is the coboundary of a function on the faces, a *face potential*
(`PlanarFlow.CombMap.exists_potential`), with integer values when the circulation is integral
(`PlanarFlow.CombMap.exists_int_potential`). This is the duality between circulations in a plane
graph and potentials (tensions) in its dual which underlies the planar flow algorithms of
Hassin, Miller–Naor and Borradaile–Klein–Mozes–Nussbaum–Wulff-Nilsen.

The proof is a dimension count over `ℚ`. Choose one dart of every edge (the *positive* darts);
an antisymmetric function is determined by its values on them. The circulations form the kernel
of the divergence map from functions on the `E` positive darts to functions on the `V` vertices;
since the graph is connected its image contains every function of total sum zero, so the
circulations form a space of dimension at most `E - V + 1`. The coboundaries form a space of
dimension at least `F - 1`, since a function on the faces with zero coboundary is constant (the
dual is connected). Euler's formula `V + F = E + 2` says that these numbers agree, so every
circulation is a coboundary.

## References

* R. Hassin, *Maximum flow in (s,t) planar networks*, Inform. Process. Lett. 13 (1981), 107.
* G. L. Miller, J. Naor, *Flow in planar graphs with multiple sources and sinks*, SIAM J. Comput.
  24 (1995), 1002–1017.
* B. Mohar, C. Thomassen, *Graphs on Surfaces*, Johns Hopkins University Press (2001), §4.1.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

open Finset Module

namespace CombMap

variable {D V F : Type*} (M : CombMap D V F)
variable [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]

/-! ### Positive darts -/

/-- A dart is *positive* if it comes before its reverse in a fixed enumeration of the darts. -/
noncomputable def Pos (d : D) : Prop :=
  ((Fintype.equivFin D d : ℕ) < (Fintype.equivFin D (M.rev d) : ℕ))

noncomputable instance : DecidablePred M.Pos := fun _ => Nat.decLt _ _

lemma pos_rev_iff (d : D) : M.Pos (M.rev d) ↔ ¬ M.Pos d := by
  unfold Pos
  rw [M.rev_rev]
  have hne : (Fintype.equivFin D d : ℕ) ≠ (Fintype.equivFin D (M.rev d) : ℕ) := by
    intro h
    exact M.rev_ne d ((Fintype.equivFin D).injective (Fin.ext h)).symm
  omega

/-- The positive darts. -/
abbrev PDart := {d : D // M.Pos d}

/-- A sum over all darts, as a sum over the positive darts of the values on both darts of the
edge. -/
lemma sum_eq_sum_pdart {β : Type*} [AddCommMonoid β] (g : D → β) :
    ∑ d, g d = ∑ p : M.PDart, (g p.1 + g (M.rev p.1)) := by
  classical
  rw [← sum_filter_add_sum_filter_not univ M.Pos, sum_add_distrib]
  congr 1
  · exact (sum_subtype (univ.filter M.Pos) (by simp) g)
  · rw [← sum_subtype (univ.filter M.Pos) (p := M.Pos) (by simp) (fun d => g (M.rev d))]
    refine sum_nbij' M.rev M.rev ?_ ?_ ?_ ?_ ?_
    · intro d hd; simp only [mem_filter, mem_univ, true_and] at hd ⊢
      rw [← M.rev_rev d] at hd; rw [M.pos_rev_iff] at hd; exact not_not.1 hd
    · intro d hd; simp only [mem_filter, mem_univ, true_and] at hd ⊢
      rw [M.pos_rev_iff]; exact not_not.2 hd
    · intro d _; exact M.rev_rev d
    · intro d _; exact M.rev_rev d
    · intro d _; rw [M.rev_rev]

lemma card_eq_two_mul : Fintype.card D = 2 * Fintype.card M.PDart := by
  have := M.sum_eq_sum_pdart (fun _ => (1 : ℕ))
  simp only [sum_const, card_univ, smul_eq_mul, mul_one] at this
  omega

/-! ### The divergence and coboundary maps -/

/-- The divergence of a function on the positive darts (extended antisymmetrically). -/
noncomputable def divL : (M.PDart → ℚ) →ₗ[ℚ] (V → ℚ) where
  toFun g v := ∑ p : M.PDart, ((if M.tail p.1 = v then g p else 0) -
    (if M.head p.1 = v then g p else 0))
  map_add' a b := by
    funext v; simp only [Pi.add_apply, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    split_ifs <;> ring
  map_smul' r a := by
    funext v; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    split_ifs <;> ring

/-- The coboundary of a function on the faces, on the positive darts. -/
noncomputable def cobL : (F → ℚ) →ₗ[ℚ] (M.PDart → ℚ) where
  toFun φ p := M.cob φ p.1
  map_add' a b := by funext p; simp only [cob, Pi.add_apply]; ring
  map_smul' r a := by funext p; simp only [cob, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The net flow out of a vertex of an antisymmetric function is the divergence of its
restriction to the positive darts. -/
lemma sum_tail_eq_divL {h : D → ℚ} (hh : M.IsAntisymm h) (v : V) :
    ∑ d with M.tail d = v, h d = M.divL (fun p => h p.1) v := by
  rw [sum_filter, M.sum_eq_sum_pdart]
  simp only [divL, LinearMap.coe_mk, AddHom.coe_mk]
  refine sum_congr rfl fun p _ => ?_
  rw [hh, M.tail_rev]
  split_ifs <;> ring

/-- Coboundaries lie in the kernel of the divergence. -/
lemma range_cobL_le : LinearMap.range M.cobL ≤ LinearMap.ker M.divL := by
  rintro _ ⟨φ, rfl⟩
  rw [LinearMap.mem_ker]
  funext v
  have := M.sum_tail_eq_divL (M.cob_antisymm φ) v
  rw [M.div_cob φ v] at this
  exact this.symm

/-! ### Functions with total sum zero -/

/-- The sum of the values of a function on a finite type. -/
def sumLin (X : Type*) [Fintype X] : (X → ℚ) →ₗ[ℚ] ℚ where
  toFun p := ∑ x, p x
  map_add' a b := by simp [sum_add_distrib]
  map_smul' r a := by simp [mul_sum]

/-- The functions on a finite type with total sum zero. -/
def sumZero (X : Type*) [Fintype X] : Submodule ℚ (X → ℚ) :=
  LinearMap.ker (sumLin X)

lemma finrank_sumZero {X : Type*} [Fintype X] [Nonempty X] :
    finrank ℚ (sumZero X) + 1 = Fintype.card X := by
  classical
  have hφ : LinearMap.range (sumLin X) = ⊤ := by
    obtain ⟨x₀⟩ := ‹Nonempty X›
    rw [LinearMap.range_eq_top]
    intro r
    exact ⟨Pi.single x₀ r, by simp [sumLin]⟩
  have h := LinearMap.finrank_range_add_finrank_ker (sumLin X)
  rw [hφ, finrank_top, finrank_self, Module.finrank_fintype_fun_eq_card] at h
  change 1 + finrank ℚ (sumZero X) = _ at h
  omega

/-- The divergence of a single positive dart. -/
lemma divL_single (p : M.PDart) :
    M.divL (Pi.single p 1) = Pi.single (M.tail p.1) 1 - Pi.single (M.head p.1) 1 := by
  classical
  funext v
  simp only [divL, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
  rw [sum_eq_single p]
  · simp only [Pi.single_eq_same]
    rcases eq_or_ne (M.tail p.1) v with h1 | h1 <;> rcases eq_or_ne (M.head p.1) v with h2 | h2
    · subst h1; simp [h2]
    · subst h1; simp [h2, Ne.symm h2]
    · subst h2; simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · intro q _ hq; simp [hq]
  · simp

/-- If the graph is connected, the divergences are all the functions of total sum zero. -/
lemma sumZero_le_range_divL (hc : ∀ a b, Relation.ReflTransGen M.Adj a b) (v₀ : V) :
    sumZero V ≤ LinearMap.range M.divL := by
  classical
  set R := LinearMap.range M.divL
  have hdart : ∀ d : D, Pi.single (M.tail d) (1 : ℚ) - Pi.single (M.head d) 1 ∈ R := by
    intro d
    by_cases hd : M.Pos d
    · exact ⟨Pi.single ⟨d, hd⟩ 1, M.divL_single _⟩
    · have hd' : M.Pos (M.rev d) := (M.pos_rev_iff d).2 hd
      refine ⟨-Pi.single ⟨M.rev d, hd'⟩ 1, ?_⟩
      rw [map_neg, M.divL_single]
      simp only [M.tail_rev, M.head_rev]
      abel
  have hpair : ∀ y, Pi.single v₀ (1 : ℚ) - Pi.single y 1 ∈ R := by
    intro y
    induction hc v₀ y with
    | refl => simp [R.zero_mem]
    | @tail a b _ hab ih =>
      obtain ⟨d, rfl, rfl⟩ := hab
      have h := R.add_mem ih (hdart d)
      convert h using 1
      abel
  intro p hp
  have hp0 : ∑ x, p x = 0 := hp
  have hp' : p = -∑ y, p y • (Pi.single v₀ (1 : ℚ) - Pi.single y 1) := by
    funext z
    simp only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      mul_sub, sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero]
    by_cases hz : z = v₀
    · subst hz; simp [hp0]
    · simp [hz]
  rw [hp']
  exact R.neg_mem (R.sum_mem fun y _ => R.smul_mem _ (hpair y))

/-! ### The main theorem -/

variable {M}

/-- A function on the faces with zero coboundary is constant. -/
lemma const_of_cob_eq_zero (hd : ∀ x y, Relation.ReflTransGen M.DualAdj x y) {φ : F → ℚ}
    (h0 : M.cobL φ = 0) (x y : F) : φ x = φ y := by
  have hstep : ∀ d : D, φ (M.face (M.rev d)) = φ (M.face d) := by
    intro d
    by_cases hp : M.Pos d
    · have := congrFun h0 ⟨d, hp⟩
      simp only [cobL, LinearMap.coe_mk, AddHom.coe_mk, cob, Pi.zero_apply] at this
      linarith
    · have hp' : M.Pos (M.rev d) := (M.pos_rev_iff d).2 hp
      have := congrFun h0 ⟨M.rev d, hp'⟩
      simp only [cobL, LinearMap.coe_mk, AddHom.coe_mk, cob, Pi.zero_apply, M.rev_rev] at this
      linarith
  induction hd x y with
  | refl => rfl
  | @tail a b _ hab ih =>
    obtain ⟨d, rfl, rfl⟩ := hab
    rw [ih, hstep]

/-- **Circulations on a plane map are coboundaries** (rational version). -/
theorem exists_potential (hM : M.IsPlane) {f : D → ℚ} (hf : M.IsAntisymm f)
    (hdiv : ∀ v, ∑ d with M.tail d = v, f d = 0) :
    ∃ φ : F → ℚ, ∀ d, f d = M.cob φ d := by
  classical
  have : Nonempty V := hM.nonempty
  obtain ⟨v₀⟩ := hM.nonempty
  -- the circulations: dimension at most `E - V + 1`
  have hA := M.sumZero_le_range_divL hM.conn v₀
  have h1 := LinearMap.finrank_range_add_finrank_ker M.divL
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have h2 := Submodule.finrank_mono hA
  have h3 : finrank ℚ (sumZero V) + 1 = Fintype.card V := finrank_sumZero
  -- the coboundaries: dimension at least `F - 1`
  have h4 := LinearMap.finrank_range_add_finrank_ker M.cobL
  rw [Module.finrank_fintype_fun_eq_card] at h4
  have hker : LinearMap.ker M.cobL ≤ Submodule.span ℚ {fun _ => 1} := by
    intro φ hφ
    rw [Submodule.mem_span_singleton]
    by_cases hF : Nonempty F
    · obtain ⟨x₀⟩ := hF
      refine ⟨φ x₀, funext fun y => ?_⟩
      simp [const_of_cob_eq_zero hM.dualConn (LinearMap.mem_ker.1 hφ) x₀ y]
    · refine ⟨0, funext fun y => (hF ⟨y⟩).elim⟩
  have h5 := (Submodule.finrank_mono hker).trans (finrank_span_le_card _)
  rw [Set.toFinset_singleton, card_singleton] at h5
  have heq : LinearMap.range M.cobL = LinearMap.ker M.divL := by
    refine Submodule.eq_of_le_of_finrank_le M.range_cobL_le ?_
    have := hM.euler
    have := M.card_eq_two_mul
    omega
  have hfk : (fun p : M.PDart => f p.1) ∈ LinearMap.ker M.divL := by
    rw [LinearMap.mem_ker]
    funext v
    rw [← M.sum_tail_eq_divL hf v, hdiv v]
    rfl
  rw [← heq] at hfk
  obtain ⟨φ, hφ⟩ := hfk
  refine ⟨φ, fun d => ?_⟩
  by_cases hp : M.Pos d
  · have := congrFun hφ ⟨d, hp⟩
    simp only [cobL, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact this.symm
  · have hp' : M.Pos (M.rev d) := (M.pos_rev_iff d).2 hp
    have := congrFun hφ ⟨M.rev d, hp'⟩
    simp only [cobL, LinearMap.coe_mk, AddHom.coe_mk] at this
    have e1 : f d = - f (M.rev d) := by have := hf (M.rev d); rw [M.rev_rev] at this; exact this
    have e2 : M.cob φ d = - M.cob φ (M.rev d) := by
      have := M.cob_antisymm φ (M.rev d); rw [M.rev_rev] at this; exact this
    rw [e1, e2, this]

/-- **Circulations on a plane map are coboundaries of integer face potentials.** -/
theorem exists_int_potential (hM : M.IsPlane) {f : D → ℤ} (hf : M.IsCirc f) :
    ∃ φ : F → ℤ, ∀ d, f d = M.cob φ d := by
  classical
  obtain ⟨φ, hφ⟩ := exists_potential hM (f := fun d => (f d : ℚ))
    (fun d => by simp [hf.antisymm d])
    (fun v => by
      have := hf.div_eq v
      simp only [div] at this
      exact_mod_cast this)
  by_cases hF : Nonempty F
  · obtain ⟨x₀⟩ := hF
    have hint : ∀ y, ∃ z : ℤ, φ y - φ x₀ = z := by
      intro y
      induction hM.dualConn x₀ y with
      | refl => exact ⟨0, by simp⟩
      | @tail a b _ hab ih =>
        obtain ⟨d, rfl, rfl⟩ := hab
        obtain ⟨z, hz⟩ := ih
        refine ⟨z + f d, ?_⟩
        have := hφ d
        simp only [cob] at this
        push_cast
        linarith
    choose ψ hψ using hint
    refine ⟨ψ, fun d => ?_⟩
    have h1 := hφ d
    have h2 := hψ (M.face d)
    have h3 := hψ (M.face (M.rev d))
    simp only [cob] at h1 ⊢
    have : ((f d : ℤ) : ℚ) = ((ψ (M.face (M.rev d)) - ψ (M.face d) : ℤ) : ℚ) := by
      push_cast; linarith
    exact_mod_cast this
  · exact ⟨fun _ => 0, fun d => (hF ⟨M.face d⟩).elim⟩

end CombMap

end PlanarFlow
