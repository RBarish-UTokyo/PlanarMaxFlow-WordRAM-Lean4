module

public import PlanarFlow.BKMNW.SplitRot
public import PlanarFlow.BKMNW.LgS5C
public import PlanarFlow.BKMNW.PkMinE

/-!
# The split of a large piece in the form computed by `sepL` (pure)

The decomposition's split at a large piece is `(if holeStep then spHR else spSR) P Hs σ` for the
choices of the headline (`pcChoiceE M Q eG N d₀`, `s5sc M eG N`). This file unfolds it into the
form the stages of `sepL` compute:

* `pcNf_of_core_empty` (`pcNf = pdarts M P Hs` when the core's piece map is empty);
* **`splitHS_eq`**: the split is `splitD` with `K = s5Kv`, `A = s5Av`, `W = s5Wv` (the registers
  `3106 … 3108` of stage 5);
* **`ls_split`**: from the split answer `some (lp, rp, π)`: a certificate `(Nf, ρ, I)` of
  `pcertF` meeting `PCertOf`, `lp`, `rp` as computed by stage 7 (`twoGroupsL` of the classes
  listed by `ordE eG N`), `π = ⟨ρ, segsF ρ Hs⟩`, and the hypotheses of `s7_exec` (`HClosed`,
  `IsCls`, `hw ≤ A`, disjoint `tH` for `K ≠ 0`, `Nf ⊆ P`) and `2 ≤ A`;
* **`ls_cert_cases`**: the certificate is either the one of `scertD` (the core's piece map
  nonempty, `Nf = pcNf`; what `lgS5D_exec` decodes) or `pemptyD` (the core's piece map empty,
  `Nf = pdarts M P Hs`);
* `ls_KA_le` (bounds of `K`, `A`, `W₀` by `#P`, for the room).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation MfDrv

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

variable {M : CombMap D V F}

/-- With an empty piece map of the core, the attached darts are those of the piece map. -/
lemma pcNf_of_core_empty {Q : Finset V} {P : Finset D} {Hs : List (Finset V)}
    (h : pdarts M (core M Q P) Hs = ∅) : pcNf M Q P Hs = pdarts M P Hs := by
  classical
  ext d
  simp only [pcNf, h, notMem_empty, IsEmpty.forall_iff, implies_true, and_true, mem_sdiff,
    mem_filter, mem_pdarts]
  tauto

/-- **The split of a large piece is `splitD` with the parameters of stage 5.** -/
lemma splitHS_eq (pc : PcChoice D V) (sc : List (Finset V) → ℕ → ℕ → ScChoice M)
    (Q : Finset V) (P : Finset D) (Hs : List (Finset V)) (σ : Perm D) (b : Bool) :
    (if holeStep M P Hs b then spHR M pc sc Q P Hs σ else spSR M pc sc Q P Hs σ) =
      splitD M pc (sc Hs (s5Av M P Hs b) (s5Wv M P Hs b)) Q P Hs (s5Kv M P Hs b)
        (s5Av M P Hs b) σ := by
  unfold s5Av s5Wv s5Kv
  cases holeStep M P Hs b
  · simp only [Bool.false_eq_true, ↓reduceIte]; rfl
  · simp only [↓reduceIte]; rfl

/-- `2 ≤ A`, `K ≠ 0 → #P + K ≤ A`, `2 W₀ ≤ 3 A` and the other parameter facts of a large piece. -/
lemma ls_params {P : Finset D} {Hs : List (Finset V)} {b : Bool} (hs : 100000 < P.card)
    (h6 : holeStep M P Hs b = true → nTouch M P Hs = 6)
    (h5 : holeStep M P Hs b = false → nTouch M P Hs ≤ 5) :
    2 ≤ s5Av M P Hs b ∧ (s5Kv M P Hs b ≠ 0 → P.card + s5Kv M P Hs b ≤ s5Av M P Hs b) ∧
      2 * (P.card + s5Kv M P Hs b * nTouch M P Hs) + 2 + 9 * (6 * Nat.sqrt (2 * P.card) + 4) ≤
        3 * s5Av M P Hs b ∧
      2 * (P.card + s5Kv M P Hs b * nTouch M P Hs) ≤ 3 * s5Av M P Hs b ∧
      nTouch M P Hs ≤ 6 ∧
      (s5Kv M P Hs b = 0 → s5Av M P Hs b < P.card) ∧
      (s5Kv M P Hs b ≠ 0 → nTouch M P Hs = 6 ∧ s5Av M P Hs b < 5 * s5Kv M P Hs b) := by
  have hb := sqrt_bound hs
  have hL : lS P = 6 * Nat.sqrt (2 * P.card) + 4 := rfl
  unfold s5Av s5Kv
  cases hh : holeStep M P Hs b
  · have ht := h5 hh
    have hA : aS P = (2 * P.card + 2 + 9 * lS P) / 3 + 1 := rfl
    simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero, ne_eq, not_true_eq_false,
      IsEmpty.forall_iff, forall_const, true_and, and_true]
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
  · have ht := h6 hh
    have hK : kH P = P.card + 3 * lS P + 2 := rfl
    have hA : aH P = (2 * (P.card + 6 * kH P) + 2 + 9 * lS P) / 3 + 1 := rfl
    simp only [↓reduceIte]
    rw [ht]
    refine ⟨by omega, fun _ => by omega, by omega, by omega, by omega, fun h => by omega,
      fun _ => ⟨rfl, by omega⟩⟩

/-- **Bounds of the parameters of stage 5 by the size of the piece** (for the room). -/
lemma ls_KA_le {P : Finset D} {Hs : List (Finset V)} {b : Bool} (ht : nTouch M P Hs ≤ 6) :
    s5Kv M P Hs b ≤ 40 * P.card + 20 ∧ s5Av M P Hs b ≤ 200 * P.card + 100 ∧
      s5Wv M P Hs b ≤ 223 * P.card + 84 := by
  have hs : Nat.sqrt (2 * P.card) ≤ 2 * P.card := Nat.sqrt_le_self _
  have hL : lS P = 6 * Nat.sqrt (2 * P.card) + 4 := rfl
  have hK : kH P = P.card + 3 * lS P + 2 := rfl
  have hA : aH P = (2 * (P.card + 6 * kH P) + 2 + 9 * lS P) / 3 + 1 := rfl
  have hA' : aS P = (2 * P.card + 2 + 9 * lS P) / 3 + 1 := rfl
  unfold s5Wv s5Kv s5Av
  cases holeStep M P Hs b
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero]
    omega
  · simp only [↓reduceIte]
    have : kH P * nTouch M P Hs ≤ kH P * 6 := Nat.mul_le_mul_left _ ht
    omega

variable {S T Q : Finset V}

open Classical in
/-- **The split of a large piece, unfolded** (see the module docstring). -/
theorem ls_split (hSTQ : S ∪ T ⊆ Q) (hloopM : ∀ d, M.head d ≠ M.tail d)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) {σ : Perm D} (hI : CInvS M Q P Hs σ) (hs : 100000 < P.card)
    {b : Bool} (h6 : holeStep M P Hs b = true → nTouch M P Hs = 6)
    (h5 : holeStep M P Hs b = false → nTouch M P Hs ≤ 5)
    {eG : ℕ → D} {N : ℕ} (hesurj : ∀ d, ∃ i < N, eG i = d) (d₀ : D) {lp rp : Finset D}
    {π : HSep M}
    (hdec : (if holeStep M P Hs b then spHR M (pcChoiceE M Q eG N d₀) (s5sc M eG N) Q P Hs σ
      else spSR M (pcChoiceE M Q eG N d₀) (s5sc M eG N) Q P Hs σ) = some (lp, rp, π)) :
    ∃ Nf ρ I, pcertF M (pcChoiceE M Q eG N d₀) (s5sc M eG N Hs (s5Av M P Hs b)
        (s5Wv M P Hs b)) Q P Hs (s5Kv M P Hs b) σ = some (Nf, ρ, I) ∧
      PCertOf (M := M) Q P Hs (s5Kv M P Hs b) (s5Av M P Hs b) (6 * Nat.sqrt (2 * P.card) + 4)
        Nf ρ I ∧
      lp = (twoGroupsL (hw M (s5Kv M P Hs b) Hs ρ.mverts) (s5Av M P Hs b)
        (ordE eG N (P.image (clsF M P Nf Hs (s5Kv M P Hs b) ρ)))).toFinset.biUnion _root_.id ∧
      rp = (P.image (clsF M P Nf Hs (s5Kv M P Hs b) ρ) \
        (twoGroupsL (hw M (s5Kv M P Hs b) Hs ρ.mverts) (s5Av M P Hs b)
          (ordE eG N (P.image (clsF M P Nf Hs (s5Kv M P Hs b) ρ)))).toFinset).biUnion _root_.id ∧
      π = ⟨ρ, segsF ρ Hs⟩ ∧
      HClosed Hs (newHole Hs ρ.mverts) ∧ IsCls P (clsF M P Nf Hs (s5Kv M P Hs b) ρ) ∧ Nf ⊆ P ∧
      (∀ X ∈ P.image (clsF M P Nf Hs (s5Kv M P Hs b) ρ),
        hw M (s5Kv M P Hs b) Hs ρ.mverts X ≤ s5Av M P Hs b) ∧
      (s5Kv M P Hs b ≠ 0 → ∀ d ∈ P, ∀ d' ∈ P,
        clsF M P Nf Hs (s5Kv M P Hs b) ρ d ≠ clsF M P Nf Hs (s5Kv M P Hs b) ρ d' →
        Disjoint (tH M Hs ρ.mverts (clsF M P Nf Hs (s5Kv M P Hs b) ρ d))
          (tH M Hs ρ.mverts (clsF M P Nf Hs (s5Kv M P Hs b) ρ d'))) ∧
      2 ≤ s5Av M P Hs b := by
  obtain ⟨hA2, hKA, hAW, hAW', hnt, -, -⟩ := ls_params hs h6 h5
  have hP0 : P.Nonempty := card_pos.1 (by omega)
  have hpc := pcChoiceE_ok (M := M) hesurj d₀ Q P Hs
  have hsc : (s5sc M eG N Hs (s5Av M P Hs b) (s5Wv M P Hs b)).OK Hs (s5Av M P Hs b)
      (P.card + s5Kv M P Hs b * nTouch M P Hs) :=
    scChoiceE_ok hesurj (sepC_ok hloopM eG N _ Hs) _ _
  obtain ⟨c, hcD, hc⟩ := pcert' hloopM hQdeg hQ5 hP hI.cinv hP0 (s5Kv M P Hs b)
    (A := s5Av M P Hs b) hAW hA2 hI.pmap _ hpc _ hsc
  rw [splitHS_eq] at hdec
  unfold splitD at hdec
  rw [hcD, Option.map_some] at hdec
  injection hdec with hdec
  obtain ⟨Nf, ρ, I⟩ := c
  simp only [splitOf, Prod.mk.injEq] at hdec
  obtain ⟨e1, e2, e3⟩ := hdec
  obtain ⟨hNf, hout, hρ, -, -, -, -, -, hIc, hIcov, hIw⟩ := id hc
  obtain ⟨hcls, -, hwt, htdisj, -, -⟩ := exists_cls' hP hNf hout hρ hIc hIcov hIw hA2 hKA
  refine ⟨Nf, ρ, I, hcD, hc, e1.symm, e2.symm, e3.symm, hClosed_newHole hP.disj hρ, hcls, hNf,
    hwt, fun hK d hd d' hd' hne => htdisj hK _ (mem_image_of_mem _ hd) _ (mem_image_of_mem _ hd')
      hne, hA2⟩

/-- **The two cases of the certificate**: `scertD` on the core's piece map (nonempty), or
`pemptyD` (empty). -/
theorem ls_cert_cases {pc : PcChoice D V} {ch : ScChoice M} {P : Finset D}
    {Hs : List (Finset V)} {K : ℕ} {σ : Perm D} {Nf : Finset D} {ρ : HPath M}
    {I : Finset (Finset D)} (h : pcertF M pc ch Q P Hs K σ = some (Nf, ρ, I)) :
    ((pdarts M (core M Q P) Hs).Nonempty ∧ Nf = pcNf M Q P Hs ∧
      ∃ I', scertD ch Hs (pdarts M (core M Q P) Hs) σ
        (fun d => pcExf M pc Q P Hs K d + lmoved (pcExf M pc Q P Hs K) (pcLs M pc Q P Hs) d) =
          some (ρ, I')) ∨
    (pdarts M (core M Q P) Hs = ∅ ∧ Nf = pdarts M P Hs ∧ ρ = (pemptyD M pc Q P Hs).2.1) := by
  unfold pcertF at h
  by_cases hne : (pdarts M (core M Q P) Hs).Nonempty
  · rw [iteT hne] at h
    unfold pcertD at h
    obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1, e2, -⟩ := e
    refine Or.inl ⟨hne, e1.symm, r.2, ?_⟩
    rw [hr, ← e2]
  · rw [iteF hne] at h
    injection h with h
    have h0 : pdarts M (core M Q P) Hs = ∅ := not_nonempty_iff_eq_empty.1 hne
    refine Or.inr ⟨h0, ?_, ?_⟩
    · have : (pemptyD M pc Q P Hs).1 = Nf := by rw [h]
      rw [← this]
      unfold pemptyD
      split_ifs with hp
      all_goals first | rfl | exact (not_nonempty_iff_eq_empty.1 hp).symm
    · rw [h]

end BKMNW

end PlanarFlow
