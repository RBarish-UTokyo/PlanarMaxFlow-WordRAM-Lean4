module

public import PlanarFlow.BKMNW.Model
public import PlanarFlow.BKMNW.Dist
public import PlanarFlow.Plane.NegCycle
public import PlanarFlow.Plane.Potential

/-!
# Residual paths, and Hassin's step

This file contains the two flow-level facts on which the fixing procedure of Borradaile, Klein,
Mozes, Nussbaum and Wulff-Nilsen (SIAM J. Comput. 46(4), 2017, Section 3) rests.

## Residual paths and closed sets

The article states its invariants as the absence of residual paths (`A ↛ B`). With
`ResAdj M u f a b` (a dart from `a` to `b` with positive residual capacity `u - f`), the set
`resReach M u f p` of the vertices reachable from `p` is closed (`closed_resReach`: every dart
leaving it is saturated), and conversely no residual path leaves a closed set
(`Closed.not_reach`). So `A ↛ B` is the existence of a closed set containing `A` and no vertex
of `B` (`NoPath`, `noPath_iff`). Closed sets are closed under unions and intersections, and a
closed set stays closed when a flow is added that does not decrease its net outflow
(`Closed.of_sum_le`): this single fact is the *sources lemma* and the *sinks lemma* of the
article (Lemmas A.2, A.3), and contains Lemma A.1 (circulations).

## Hassin's step (Section 3.1.1 of the article)

Let `g` be a pseudoflow and `d` a saturated dart from `p` to `q`. Give every dart its residual
capacity as length, except `rev d`, which gets the limit `x ≥ 0`, and let `φ` be the distances in
the dual graph from the face of `rev d` (the head of `d` in the dual). Adding the circulation
`cob φ` and undoing it on `d` and `rev d` (`hassinFlow`) pushes `val = φ (face d)` units from `p`
to `q` (`hassin_step`):

* the result is a pseudoflow, its net outflow changes by `val` at `p` and by `-val` at `q`;
* `0 ≤ val ≤ x`;
* either `val = x`, or no residual path leads from `p` to `q`: the flow is a maximum flow from `p`
  to `q` with limit `x`.

The maximality is proved with the planar duality between cycles and cuts in the following form:
a residual path from `p` to `q`, closed by `rev d`, is a circulation, hence (on a plane map) the
coboundary of a face potential `ψ` (`PlanarFlow.CombMap.exists_int_potential`); summing it along
a shortest dual walk from the face of `rev d` to the face of `d` gives `1` by telescoping, while
every dart of that walk is saturated by the new flow, so the sum is at most `0`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable {M : CombMap D V F}

/-! ### Residual paths and closed sets -/

variable (M) in
/-- A dart from `a` to `b` with positive residual capacity. -/
def ResAdj (u f : D → ℤ) (a b : V) : Prop := ∃ d, M.tail d = a ∧ M.head d = b ∧ f d < u d

variable (M) in
/-- The vertices reachable from `p` by residual paths. -/
noncomputable def resReach (u f : D → ℤ) (p : V) : Finset V := by
  classical exact univ.filter fun v => Relation.ReflTransGen (ResAdj M u f) p v

lemma mem_resReach {u f : D → ℤ} {p v : V} :
    v ∈ resReach M u f p ↔ Relation.ReflTransGen (ResAdj M u f) p v := by
  classical
  unfold resReach; simp

/-- The vertices reachable by residual paths form a closed set. -/
lemma closed_resReach {u f : D → ℤ} (hf : IsPseudo M u f) (p : V) :
    Closed M u f (resReach M u f p) := by
  intro d hd1 hd2
  rw [mem_resReach] at hd1 hd2
  by_contra hne
  exact hd2 (hd1.tail ⟨d, rfl, rfl, lt_of_le_of_ne (hf.le_cap d) hne⟩)

/-- No residual path leaves a closed set. -/
lemma Closed.not_reach {u f : D → ℤ} {X : Finset V} (hX : Closed M u f X) {a b : V}
    (ha : a ∈ X) (h : Relation.ReflTransGen (ResAdj M u f) a b) : b ∈ X := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih =>
    obtain ⟨d, rfl, rfl, hlt⟩ := hbc
    by_contra hc
    exact absurd (hX d ih hc) (ne_of_lt hlt)

variable (M) in
/-- **No residual path from `A` to `B`**: a closed set contains `A` and no vertex of `B`. -/
def NoPath (u f : D → ℤ) (A B : Finset V) : Prop :=
  ∃ Y, A ⊆ Y ∧ Disjoint Y B ∧ Closed M u f Y

/-- `NoPath` is the absence of residual paths. -/
theorem noPath_iff {u f : D → ℤ} (hf : IsPseudo M u f) {A B : Finset V} :
    NoPath M u f A B ↔ ∀ a ∈ A, ∀ b ∈ B, ¬ Relation.ReflTransGen (ResAdj M u f) a b := by
  classical
  constructor
  · rintro ⟨Y, hAY, hYB, hY⟩ a ha b hb h
    exact disjoint_left.1 hYB (hY.not_reach (hAY ha) h) hb
  · intro h
    refine ⟨A.biUnion fun a => resReach M u f a, fun a ha => mem_biUnion.2 ⟨a, ha,
      mem_resReach.2 Relation.ReflTransGen.refl⟩, ?_, ?_⟩
    · rw [disjoint_left]
      intro v hv hvB
      obtain ⟨a, ha, hv⟩ := mem_biUnion.1 hv
      exact h a ha v hvB (mem_resReach.1 hv)
    · intro d hd1 hd2
      obtain ⟨a, ha, hd⟩ := mem_biUnion.1 hd1
      exact closed_resReach hf a d hd fun h' => hd2 (mem_biUnion.2 ⟨a, ha, h'⟩)

/-- The intersection of two closed sets is closed. -/
lemma Closed.inter {u f : D → ℤ} {X Y : Finset V} (hX : Closed M u f X) (hY : Closed M u f Y) :
    Closed M u f (X ∩ Y) := by
  intro d hd1 hd2
  rw [mem_inter] at hd1 hd2
  by_cases h : M.head d ∈ X
  · exact hY d hd1.2 fun h' => hd2 ⟨h, h'⟩
  · exact hX d hd1.1 h

/-- **The sources and sinks lemma.** A closed set stays closed when the flow changes to a
pseudoflow whose net outflow over the set is not smaller. -/
theorem Closed.of_sum_le {u f f' : D → ℤ} {X : Finset V} (hf : IsPseudo M u f)
    (hf' : IsPseudo M u f') (hX : Closed M u f X)
    (hle : ∑ v ∈ X, M.div f v ≤ ∑ v ∈ X, M.div f' v) : Closed M u f' X := by
  rw [← tight_iff_closed hf'] at *
  rw [← tight_iff_closed hf] at hX
  exact le_antisymm (sum_div_le_cutCap hf' X) (hX ▸ hle)

/-- A closed set stays closed when the residual capacities decrease. -/
lemma Closed.of_res_le {u f u' f' : D → ℤ} {X : Finset V} (hX : Closed M u f X)
    (hf' : IsPseudo M u' f') (hle : ∀ d, u' d - f' d ≤ u d - f d) : Closed M u' f' X := by
  intro d hd1 hd2
  have := hX d hd1 hd2; have := hle d; have := hf'.le_cap d; omega

/-! ### Path flows -/

variable [Fintype F] [DecidableEq F]

/-- A residual path gives a unit flow along it, positive only on residual darts. -/
theorem exists_pathFlow {u f : D → ℤ} {p q : V} (h : Relation.ReflTransGen (ResAdj M u f) p q) :
    ∃ χ : D → ℤ, M.IsAntisymm χ ∧
      (∀ v, M.div χ v = (if p = v then 1 else 0) - (if q = v then 1 else 0)) ∧
      ∀ d, 0 < χ d → f d < u d := by
  induction h with
  | refl => exact ⟨0, fun d => by simp, fun v => by simp [CombMap.div], fun d h => by simp at h⟩
  | @tail b c _ hbc ih =>
    obtain ⟨χ, hχ, hdiv, hpos⟩ := ih
    obtain ⟨e, rfl, rfl, he⟩ := hbc
    refine ⟨χ + (Pi.single e 1 - Pi.single (M.rev e) 1), fun d => ?_, fun v => ?_, fun d hd => ?_⟩
    · simp only [Pi.add_apply]
      rw [hχ d, isAntisymm_dart e d]; ring
    · rw [div_add', hdiv v, div_dart]; ring
    · by_cases hde : d = e
      · subst hde; exact he
      · apply hpos d
        have : (Pi.single e 1 - Pi.single (M.rev e) 1 : D → ℤ) d ≤ 0 := by
          simp only [Pi.sub_apply, Pi.single_apply, hde, ite_false]; split_ifs <;> simp
        simp only [Pi.add_apply] at hd; omega

/-! ### Hassin's step -/

lemma list_sum_nonpos {l : List ℤ} (h : ∀ x ∈ l, x ≤ 0) : l.sum ≤ 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons]
    have := h a (List.mem_cons_self ..)
    have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    omega

variable (M) in
/-- The lengths of Hassin's step: the residual capacities `u - g`, and the limit `x` on `rev d`. -/
def hassinLen (u g : D → ℤ) (d : D) (x : ℤ) (e : D) : ℤ := if e = M.rev d then x else u e - g e

variable (M) in
/-- The flow of Hassin's step: `g + cob φ`, left unchanged on `d` and `rev d`. -/
def hassinFlow (g : D → ℤ) (d : D) (φ : F → ℤ) (e : D) : ℤ :=
  if e = d ∨ e = M.rev d then g e else g e + M.cob φ e

/-- In a plane map every face is reachable in the dual graph. -/
lemma dual_reach (hM : M.IsPlane) (ℓ : D → ℤ) (r y : F) :
    ∃ l, IsWalk (M.dualGraph ℓ) r l y := by
  induction hM.dualConn r y with
  | refl => exact ⟨[], rfl⟩
  | tail _ hxy ih =>
    obtain ⟨l, hl⟩ := ih
    obtain ⟨d, rfl, rfl⟩ := hxy
    exact ⟨l ++ [d], hl.append (isWalk_singleton.2 ⟨rfl, rfl⟩)⟩

lemma div_smul (c : ℤ) (h : D → ℤ) (v : V) : M.div (fun e => c * h e) v = c * M.div h v := by
  simp [CombMap.div, Finset.mul_sum]

/-- The distances of Hassin's step exist and are finite at every face. -/
lemma exists_hassin_dist (hM : M.IsPlane) {u g : D → ℤ} (hg : IsPseudo M u g) (d : D) {x : ℤ}
    (hx : 0 ≤ x) : ∃ φ : F → ℤ,
      IsDist (M.dualGraph (hassinLen M u g d x)) (M.face (M.rev d)) fun y => some (φ y) := by
  have hnn : ∀ e, 0 ≤ (M.dualGraph (hassinLen M u g d x)).len e := fun e => by
    show 0 ≤ hassinLen M u g d x e
    unfold hassinLen; split_ifs
    · exact hx
    · linarith [hg.le_cap e]
  obtain ⟨δ, hδ⟩ := exists_isDist (p := fun _ => 0) (fun e => by have := hnn e; simp; omega)
    (M.face (M.rev d))
  have hreach : ∀ y, δ y ≠ none := fun y => by
    obtain ⟨l, hl⟩ := dual_reach hM (hassinLen M u g d x) (M.face (M.rev d)) y
    obtain ⟨ℓ, h1, -⟩ := hδ.exists_le hl
    simp [h1]
  refine ⟨fun y => (δ y).getD 0, ?_⟩
  convert hδ using 1
  funext y
  obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 (hreach y)
  simp [hℓ]

/-- **Hassin's step.** Let `g` be a pseudoflow, `d` a saturated dart, `x ≥ 0` a limit, and `φ` the
distances in the dual graph, with the lengths `hassinLen`, from the face of `rev d`. With
`val = φ (face d)`, `hassinFlow g d φ` is a pseudoflow, its net outflow is that of `g` plus `val`
at the tail of `d` and minus `val` at the head of `d`, `0 ≤ val ≤ x`, and either `val = x` or a
closed set contains the tail of `d` and not its head. -/
theorem hassin_step (hM : M.IsPlane) {u g : D → ℤ} (hg : IsPseudo M u g) {d : D}
    (hd : g d = u d) {x : ℤ} (hx : 0 ≤ x) {φ : F → ℤ}
    (hδ : IsDist (M.dualGraph (hassinLen M u g d x)) (M.face (M.rev d)) fun y => some (φ y)) :
    IsPseudo M u (hassinFlow M g d φ) ∧
      (∀ v, M.div (hassinFlow M g d φ) v = M.div g v +
        φ (M.face d) * ((if M.tail d = v then 1 else 0) - (if M.head d = v then 1 else 0))) ∧
      0 ≤ φ (M.face d) ∧ φ (M.face d) ≤ x ∧
      (φ (M.face d) = x ∨
        ∃ Y, M.tail d ∈ Y ∧ M.head d ∉ Y ∧ Closed M u (hassinFlow M g d φ) Y) := by
  classical
  generalize hG : M.dualGraph (hassinLen M u g d x) = G at hδ
  have hlen : ∀ e, G.len e = hassinLen M u g d x e := fun e => by rw [← hG]; rfl
  have hsrc : ∀ e, G.src e = M.face e := fun e => by rw [← hG]; rfl
  have hdst : ∀ e, G.dst e = M.face (M.rev e) := fun e => by rw [← hG]; rfl
  have hnn : ∀ e, 0 ≤ G.len e := fun e => by
    rw [hlen]; unfold hassinLen; split_ifs
    · exact hx
    · linarith [hg.le_cap e]
  have hpot : G.IsPot φ := hδ.isPot (by simp)
  have hroot : φ (M.face (M.rev d)) = 0 := by
    have := hδ.self (p := fun _ => 0) (fun e => by have := hnn e; simp; omega)
    simpa using this
  -- the reduced lengths are nonnegative
  have hcob : ∀ e, M.cob φ e ≤ G.len e := fun e => by
    have := hpot e; rw [hsrc, hdst] at this; simp only [cob]; omega
  have hval_le : φ (M.face d) ≤ x := by
    have hw : IsWalk G (M.face (M.rev d)) [M.rev d] (M.face d) :=
      isWalk_singleton.2 ⟨by rw [hsrc], by rw [hdst, M.rev_rev]⟩
    have := hδ.getD_le hw
    simpa [hlen, hassinLen] using this
  generalize hval : φ (M.face d) = val at hval_le
  have hdrev : d ≠ M.rev d := (M.rev_ne d).symm
  -- the flow
  have hflow : hassinFlow M g d φ =
      g + M.cob φ + fun e => val * ((Pi.single d 1 - Pi.single (M.rev d) 1 : D → ℤ) e) := by
    funext e
    simp only [hassinFlow, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : e = d
    · subst h1; simp [hdrev, cob, hroot, hval]
    · by_cases h2 : e = M.rev d
      · subst h2; simp [h1, cob, M.rev_rev, hroot, hval]
      · simp [h1, h2]
  have hps : IsPseudo M u (hassinFlow M g d φ) := by
    refine ⟨fun e => ?_, fun e => ?_⟩
    · rw [hflow]
      simp only [Pi.add_apply, hg.antisymm e, M.cob_antisymm φ e, isAntisymm_dart d e]; ring
    · simp only [hassinFlow]
      split_ifs with h
      · exact hg.le_cap e
      · have h2 : e ≠ M.rev d := fun h' => h (Or.inr h')
        have := hcob e; rw [hlen] at this; simp only [hassinLen, h2, ite_false] at this; omega
  refine ⟨hps, fun v => ?_, ?_, hval_le, ?_⟩
  · rw [hflow, div_add', div_add', div_smul, div_dart,
      show M.div (M.cob φ) v = 0 from M.div_cob φ v]
    ring
  · -- `val ≥ 0`
    obtain ⟨l, -, hl⟩ := hδ.some_walk _ val (by rw [hval])
    rw [← hl]
    exact List.sum_nonneg (by simpa using fun e _ => hnn e)
  · -- maximality
    by_cases hvx : val = x
    · exact Or.inl hvx
    right
    refine ⟨resReach M u (hassinFlow M g d φ) (M.tail d), mem_resReach.2 .refl, fun hq => ?_,
      closed_resReach hps _⟩
    obtain ⟨χ, hχ, hdivχ, hposχ⟩ := exists_pathFlow (mem_resReach.1 hq)
    -- close the path with `rev d`: a circulation
    let χ' : D → ℤ := χ - (Pi.single d 1 - Pi.single (M.rev d) 1)
    have hcirc : M.IsCirc χ' := ⟨fun e => by
      simp only [χ', Pi.sub_apply, hχ e]
      have := isAntisymm_dart (M := M) d e
      simp only [Pi.sub_apply] at this; rw [this]; ring, fun v => by
      simp only [χ']; rw [div_sub', hdivχ v, div_dart]; ring⟩
    obtain ⟨ψ, hψ⟩ := exists_int_potential hM hcirc
    -- a shortest dual walk from the face of `rev d` to the face of `d`
    obtain ⟨l, hl, hwl⟩ := hδ.some_walk _ val (by rw [hval])
    -- the sum of `χ'` along the walk is `1 - χ d ≥ 1`
    have hsum : (l.map χ').sum = 1 - χ d := by
      have h1 : (l.map χ') = l.map fun e => ψ (G.dst e) - ψ (G.src e) := by
        refine List.map_congr_left fun e _ => ?_
        rw [hψ e, hsrc, hdst]; rfl
      rw [h1, hl.sum_sub ψ]
      have h2 := hψ d
      simp only [χ', cob, Pi.sub_apply, Pi.single_apply, hdrev, ite_true, ite_false] at h2
      linarith
    have hχd : χ d ≤ 0 := by
      by_contra h
      have := hposχ d (by omega)
      simp only [hassinFlow, true_or, ite_true, hd] at this; omega
    -- every dart of the walk is saturated, and is not `rev d`
    have htight : ∀ e ∈ l, G.len e - M.cob φ e = 0 := by
      have hsum0 : wlen (G.addPot fun y => -φ y) l = 0 := by
        rw [wlen_addPot hl, hwl, hroot, hval]; ring
      have hl' : ∀ e, (G.addPot fun y => -φ y).len e = G.len e - M.cob φ e := fun e => by
        simp only [Digraph.addPot, cob, hsrc, hdst]; ring
      intro e he
      have h0 : ∀ y ∈ l.map (G.addPot fun y => -φ y).len, 0 ≤ y := by
        simp only [List.mem_map]; rintro _ ⟨e', _, rfl⟩; rw [hl']; have := hcob e'; omega
      have := List.single_le_sum h0 _ (List.mem_map.2 ⟨e, he, rfl⟩)
      rw [← wlen, hsum0, hl'] at this
      have := hcob e; omega
    have hnotrev : ∀ e ∈ l, e ≠ M.rev d := by
      rintro e he rfl
      have := le_wlen_of_mem hnn he
      rw [hwl, hlen] at this
      simp only [hassinLen, ite_true] at this
      exact hvx (le_antisymm hval_le this)
    have hle : ∀ e ∈ l, χ' e ≤ 0 := by
      intro e he
      by_cases hed : e = d
      · subst hed; simp only [χ', Pi.sub_apply, Pi.single_apply, ite_true, hdrev, ite_false]; omega
      · have hne := hnotrev e he
        simp only [χ', Pi.sub_apply, Pi.single_apply, hed, hne, ite_false, sub_zero]
        by_contra hpos
        have := hposχ e (by omega)
        have ht := htight e he
        rw [hlen] at ht
        simp only [hassinLen, hne, ite_false] at ht
        simp only [hassinFlow, hed, hne, or_self, ite_false] at this
        omega
    have := list_sum_nonpos (l := l.map χ') (by
      simp only [List.mem_map]; rintro _ ⟨e, he, rfl⟩; exact hle e he)
    omega

end BKMNW

end PlanarFlow
