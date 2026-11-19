module

public import PlanarFlow.BKMNW.FixPath

/-!
# FixConservationOnPath: the magnitudes of the implicit representation

A machine program for `PlanarFlow.BKMNW.fixPath` keeps the explicit flow `s.1` and the prices
`φX = s.2` of the faces along the path as words. This file bounds them, uniformly over the
stages, by numbers polynomial in the size of the map and the capacities:

* `IsWalk.exists_nodupSrc`, **`IsDist.le_sum_len`**: with nonnegative lengths, a distance is at
  most the sum of all the lengths (a shortest walk may be taken without repeated arcs);
* `hassinLen_sum_le`, `abs_div_le_sum`, `sum_cap_le`;
* **`Bst c`** `= 2 (absSum c + #D · (4 absSum c + 1))`: the increase of a price in one stage;
* **`fpStep_phi`**: one stage (from `EffInv`) changes the prices only on the faces along the path,
  and raises each by a value in `[0, Bst c]` (the distances of Hassin's step,
  `dist_correct`); copied from the proof of `fpStep_inv`;
* **`EffInvB`**, **`fpStep_invB`**, **`fixPath_invB`**: after `i` stages the prices are `0` off
  the faces along the path and in `[0, i · Bst c]` on them;
* **`EffInvB.flow_bound`**: the explicit flow is `f₀` off the path and at most
  `2 (absSum c + 4 absSum c + 1) + i · Bst c` in absolute value on it;
* **`fixPath_negPre`** (the `NegPre` condition of the final call: loops of the dual of
  nonnegative length for `c - s.1`) and **`fixPath_len_bound`** (`|c - s.1| ≤ …`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap SPath

/-! ### Distances are bounded by the sum of the lengths -/

section Walk

variable {X A : Type*} {G : Digraph X A}

/-- A suffix of a walk, from the tail of its first arc. -/
lemma IsWalk.drop {x y : X} {l : List A} (h : IsWalk G x l y) {j : ℕ} (hj : j < l.length) :
    IsWalk G (G.src l[j]) (l.drop j) y := by
  have he : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  rw [he] at h
  obtain ⟨z, -, hz⟩ := isWalk_append_iff.1 h
  rw [List.drop_eq_getElem_cons hj] at hz ⊢
  obtain ⟨-, h2⟩ := hz
  exact ⟨rfl, h2⟩

/-- **A walk without repeated tails** between the same ends. -/
lemma IsWalk.exists_nodupSrc {x y : X} {l : List A} (h : IsWalk G x l y) :
    ∃ l', IsWalk G x l' y ∧ (l'.map G.src).Nodup := by
  induction l generalizing x with
  | nil => exact ⟨[], h, List.nodup_nil⟩
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := h
    obtain ⟨l', hw, hnd⟩ := ih h2
    by_cases hx : x ∈ l'.map G.src
    · obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
      have hj' : j < l'.length := by simpa using hj
      have hsrc : G.src l'[j] = x := by simpa using hjx
      refine ⟨l'.drop j, hsrc ▸ hw.drop hj', ?_⟩
      rw [List.map_drop]; exact hnd.sublist (List.drop_sublist _ _)
    · refine ⟨a :: l', ⟨h1, hw⟩, ?_⟩
      simp only [List.map_cons, List.nodup_cons]
      exact ⟨h1 ▸ hx, hnd⟩

variable [Fintype A] [DecidableEq A]

/-- The length of a walk without repeated arcs is at most the sum of the (nonnegative)
lengths. -/
lemma wlen_le_sum_of_nodup (hG : ∀ a, 0 ≤ G.len a) {l : List A} (hl : l.Nodup) :
    wlen G l ≤ ∑ a, G.len a := by
  unfold wlen
  rw [← List.sum_toFinset _ hl]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun a _ _ => hG a

/-- **A distance with nonnegative lengths is at most the sum of all the lengths**, and is
nonnegative. -/
theorem IsDist.le_sum_len (hG : ∀ a, 0 ≤ G.len a) {r y : X} {δ : X → Option ℤ}
    (h : IsDist G r δ) {ℓ : ℤ} (hy : δ y = some ℓ) : 0 ≤ ℓ ∧ ℓ ≤ ∑ a, G.len a := by
  obtain ⟨l, hl, hlen⟩ := h.some_walk y ℓ hy
  obtain ⟨l', hl', hnd⟩ := hl.exists_nodupSrc
  refine ⟨?_, (h.some_le y ℓ hy l' hl').trans (wlen_le_sum_of_nodup hG (hnd.of_map _))⟩
  rw [← hlen]; exact List.sum_nonneg fun z hz => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hz; exact hG a

end Walk

/-! ### Sums of capacities and of Hassin's lengths -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The net outflow of a pseudoflow is at most the total of nonnegative capacities. -/
lemma abs_div_le_sum {u g : D → ℤ} (hu : ∀ d, 0 ≤ u d) (hg : IsPseudo M u g) (v : V) :
    |M.div g v| ≤ ∑ d, u d := by
  have h1 : M.div g v ≤ ∑ d, u d := by
    unfold CombMap.div
    exact (sum_le_sum fun d _ => hg.le_cap d).trans
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun d _ _ => hu d)
  have h2 : -M.div g v ≤ ∑ d, u d := by
    unfold CombMap.div
    rw [← sum_neg_distrib]
    have hr : ∀ d, -g d ≤ u (M.rev d) := fun d => by
      have := hg.le_cap (M.rev d); rw [hg.antisymm d] at this; exact this
    refine (sum_le_sum fun d _ => hr d).trans ?_
    refine (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun d _ _ => hu (M.rev d)).trans ?_
    exact (Equiv.sum_comp (Equiv.ofBijective _ M.rev_injective.bijective_of_finite) u).le
  exact abs_le.2 ⟨by linarith, h1⟩

/-- The sum of an antisymmetric function vanishes. -/
lemma sum_univ_antisymm {g : D → ℤ} (hg : M.IsAntisymm g) : ∑ d, g d = 0 :=
  sum_antisymm_eq_zero hg univ fun d _ => mem_univ _

/-- **The total of Hassin's lengths** is at most the total capacity plus the limit. -/
lemma hassinLen_sum_le {u g : D → ℤ} (hg : IsPseudo M u g) (e : D) {x : ℤ} (hx : 0 ≤ x) :
    ∑ d, hassinLen M u g e x d ≤ ∑ d, u d + x := by
  have hle : ∀ d, hassinLen M u g e x d ≤ (u d - g d) + if d = M.rev e then x else 0 := by
    intro d; unfold hassinLen
    split_ifs with h
    · have := hg.le_cap d; linarith
    · simp
  refine (sum_le_sum fun d _ => hle d).trans (le_of_eq ?_)
  rw [sum_add_distrib, sum_sub_distrib, sum_univ_antisymm hg.antisymm, sum_ite_eq']
  simp

/-- The boosted capacities sum to at most `absSum c + #D · Mb`. -/
lemma sum_cap_le (P : SPath M) (c : D → ℤ) {Mb : ℤ} (hMb : 0 ≤ Mb) (i : ℕ) :
    ∑ d, P.cap c Mb i d ≤ absSum c + Fintype.card D * Mb := by
  have : ∀ d, P.cap c Mb i d ≤ |c d| + Mb := fun d => by
    unfold SPath.cap; split_ifs
    · have := le_abs_self (c d); linarith
    · have := le_abs_self (c d); linarith
  refine (sum_le_sum fun d _ => this d).trans (le_of_eq ?_)
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]; rfl

variable (D) in
/-- **The bound of the increase of a price in one stage**:
`2 (absSum c + #D · (4 absSum c + 1))`. -/
def Bst (c : D → ℤ) : ℤ := 2 * (absSum c + Fintype.card D * (4 * absSum c + 1))

lemma Bst_nonneg (c : D → ℤ) : 0 ≤ Bst D c := by
  unfold Bst; have := absSum_nonneg c; positivity

/-! ### One stage -/

/-- **One stage changes the prices only on the faces along the path, by a value in
`[0, Bst c]`** (the distances of Hassin's step). Proof copied from `fpStep_inv`. -/
theorem fpStep_phi (hM : M.IsPlane) {c f₀ : D → ℤ} (hc : ∀ e, 0 ≤ c e) (hf₀ : IsPseudo M c f₀)
    {P : SPath M} {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P)
    {fr : FRFun F} (hfr : FRSpec fr) {i : ℕ} (hi : i < P.k) {s : (D → ℤ) × (F → ℤ)}
    (hs : EffInv c f₀ P i s) :
    (∀ y, y ∉ P.faces → (fpStep M c P ⟨P.faces, mssp P.darts (c - f₀)⟩ fr i s).2 y = s.2 y) ∧
    ∀ y ∈ P.faces, s.2 y ≤ (fpStep M c P ⟨P.faces, mssp P.darts (c - f₀)⟩ fr i s).2 y ∧
      (fpStep M c P ⟨P.faces, mssp P.darts (c - f₀)⟩ fr i s).2 y ≤ s.2 y + Bst D c := by
  classical
  obtain ⟨f, φX⟩ := s
  obtain ⟨Φ, hφ, hoff, hanti, hinv⟩ := hs
  simp only at hφ hoff hanti hinv ⊢
  have hd₀ : P.d i ∈ P.darts := P.d_mem i hi
  have hcob₀ : M.cob φX (P.d i) = M.cob Φ (P.d i) := cob_eq_of_faces hφ hd₀
  have hA0 := absSum_nonneg c
  have hsumu : ∑ d, P.cap c (4 * absSum c + 1) (i + 1) d ≤
      absSum c + Fintype.card D * (4 * absSum c + 1) := sum_cap_le P c (by omega) (i + 1)
  have hu0 : ∀ d, 0 ≤ P.cap c (4 * absSum c + 1) (i + 1) d := fun d =>
    (hc d).trans (P.le_cap_zero c (by omega) _ d)
  generalize hu : P.cap c (4 * absSum c + 1) (i + 1) = u at hsumu hu0
  have hu_off : ∀ e, e ∉ P.darts → u e = c e := fun e he => by
    rw [← hu, P.cap_of_not_mem c _ _ he]
  generalize hg : f + M.cob Φ = g at hinv
  have hgps := hinv.pseudo
  generalize hf₁ : setPair M f (P.d i) (max (min (f (P.d i) + M.cob φX (P.d i)) (c (P.d i)))
    (-c (M.rev (P.d i))) - M.cob φX (P.d i)) = f₁
  have hg₁ : f₁ + M.cob Φ = SPath.clip M c g (P.d i) := by
    rw [← hf₁, setPair_add _ _ _ _ (M.cob_antisymm Φ), SPath.clip, SPath.clipVal, ← hg, hcob₀]
    simp only [Pi.add_apply, sub_add_cancel]
  have hdivcob : ∀ h : D → ℤ, ∀ v, M.div (h + M.cob Φ) v = M.div h v := fun h v => by
    rw [div_add', show M.div (M.cob Φ) v = 0 from M.div_cob Φ v, add_zero]
  have hb : M.div f₁ (P.p i) = M.div (SPath.clip M c g (P.d i)) (P.p i) := by
    rw [← hg₁, hdivcob]
  generalize hbv : M.div (SPath.clip M c g (P.d i)) (P.p i) = b at hb
  generalize he : (if b < 0 then P.d i else M.rev (P.d i)) = e
  have hemem : e ∈ P.darts := by
    rw [← he]; split_ifs
    · exact hd₀
    · exact P.rev_mem_darts hd₀
  have hcobe : M.cob φX e = M.cob Φ e := cob_eq_of_faces hφ hemem
  generalize hx : |b| = x
  have hx0 : 0 ≤ x := hx ▸ abs_nonneg b
  generalize hg₁' : SPath.clip M c g (P.d i) = g₁ at hg₁ hbv
  have hanti₁ : M.IsAntisymm f₁ := hf₁ ▸ setPair_antisymm hanti _ _
  have hg₁ps : IsPseudo M u g₁ := by
    rw [← hg₁', ← hu, SPath.clip]
    refine ⟨setPair_antisymm hgps.antisymm _ _, fun e' => ?_⟩
    have hii : ¬ (i + 1 ≤ i) := by omega
    by_cases h1 : e' = P.d i
    · subst h1
      rw [setPair_self]; simp only [P.cap_d c _ hi, hii, ↓reduceIte, SPath.clipVal]
      have := hc (P.d i); have := hc (M.rev (P.d i)); omega
    · by_cases h2 : e' = M.rev (P.d i)
      · subst h2
        rw [setPair_rev]; simp only [P.cap_rev_d c _ hi, hii, ↓reduceIte, SPath.clipVal]
        have := hc (P.d i); have := hc (M.rev (P.d i)); omega
      · rw [setPair_of_ne _ _ h1 h2, P.cap_succ c _ hi h1 h2]; exact hgps.le_cap e'
  have hxle : x ≤ ∑ d, u d := by
    rw [← hx, ← hbv]; exact abs_div_le_sum hu0 hg₁ps _
  generalize hval₀ : min (u e - f₁ e - M.cob φX e) x = val₀
  have hres₀ : u e - f₁ e - M.cob φX e = u e - g₁ e := by
    rw [hcobe, ← hg₁]; simp only [Pi.add_apply]; ring
  generalize hf₂ : setPair M f₁ e (f₁ e + val₀) = f₂
  generalize hg₂ : setPair M g₁ e (g₁ e + val₀) = g₂
  have hfg₂ : f₂ + M.cob Φ = g₂ := by
    rw [← hf₂, ← hg₂, setPair_add _ _ _ _ (M.cob_antisymm Φ), ← hg₁]
    simp only [Pi.add_apply]; ring_nf
  have hval₀0 : 0 ≤ val₀ := by
    rw [← hval₀, hres₀]; have := hg₁ps.le_cap e; omega
  have hval₀x : val₀ ≤ x := hval₀ ▸ min_le_right _ _
  have hg₂ps : IsPseudo M u g₂ := by
    rw [← hg₂]
    refine ⟨setPair_antisymm hg₁ps.antisymm _ _, fun e' => ?_⟩
    by_cases h1 : e' = e
    · subst h1; rw [setPair_self]; have := min_le_left (u e' - f₁ e' - M.cob φX e') x
      rw [hval₀, hres₀] at this; omega
    · by_cases h2 : e' = M.rev e
      · subst h2; rw [setPair_rev]
        have := hg₁ps.le_cap (M.rev e); rw [hg₁ps.antisymm e] at this
        omega
      · rw [setPair_of_ne _ _ h1 h2]; exact hg₁ps.le_cap e'
  have hoff₁ : ∀ e', e' ∉ P.darts → f₁ e' = f₀ e' := fun e' h' => by
    rw [← hf₁, setPair_off hd₀ h']; exact hoff e' h'
  have hoff₂ : ∀ e', e' ∉ P.darts → f₂ e' = f₀ e' := fun e' h' => by
    rw [← hf₂, setPair_off hemem h']; exact hoff₁ e' h'
  generalize hδ : fr ⟨P.faces, mssp P.darts (c - f₀)⟩ (explicitArcs (M.dualGraph fun e' =>
    if e' = M.rev e then (x - val₀) + M.cob φX (M.rev e) else u e' - f₂ e') P.darts)
    (M.face (M.rev e)) φX = δ
  have hstep : fpStep M c P ⟨P.faces, mssp P.darts (c - f₀)⟩ fr i (f, φX) =
      if x - val₀ ≤ 0 then (f₂, φX) else
        (setPair M f₂ e (f₂ e + ((δ (M.face e)).getD 0 - φX (M.face e) + φX (M.face (M.rev e)))),
         fun y => if y ∈ P.faces then φX y + ((δ y).getD 0 - φX y + φX (M.face (M.rev e)))
          else φX y) := by
    simp only [fpStep, hu, hf₁, hb, he, hx, hval₀, hf₂, hδ]
  rw [hstep]
  have hB := Bst_nonneg c
  split_ifs with hle
  · exact ⟨fun y _ => rfl, fun y _ => ⟨le_rfl, by linarith⟩⟩
  · have hsat : g₂ e = u e := by
      have : val₀ = u e - g₁ e := by
        rw [← hval₀, hres₀]; rw [hres₀] at hval₀
        exact min_eq_left (by omega)
      rw [← hg₂, setPair_self]; omega
    have hx' : 0 ≤ x - val₀ := by omega
    obtain ⟨φt, ht⟩ := exists_hassin_dist hM hg₂ps e hx'
    have hdc := dist_correct hM hmssp hf₀ hfr (u := u) (f := f₂) (Φ := Φ) (φX := φX) hu_off hoff₂
      hφ (hfg₂ ▸ hg₂ps) hemem hx' (by rw [hfg₂]; exact ht)
    rw [hδ] at hdc
    -- the bound of the distances of Hassin's step
    have hnn : ∀ a, 0 ≤ (M.dualGraph (hassinLen M u g₂ e (x - val₀))).len a := fun a => by
      show 0 ≤ hassinLen M u g₂ e (x - val₀) a
      unfold hassinLen; split_ifs
      · exact hx'
      · linarith [hg₂ps.le_cap a]
    have hsumH := hassinLen_sum_le hg₂ps e hx'
    have hφt : ∀ y, 0 ≤ φt y ∧ φt y ≤ Bst D c := fun y => by
      obtain ⟨h1, h2⟩ := ht.le_sum_len hnn (y := y) rfl
      refine ⟨h1, h2.trans ?_⟩
      show ∑ a, hassinLen M u g₂ e (x - val₀) a ≤ Bst D c
      unfold Bst; linarith
    refine ⟨fun y hy => by simp [hy], fun y hy => ?_⟩
    simp only [hy, ↓reduceIte]
    rw [hdc y hy]
    have := hφt y
    constructor <;> linarith

/-! ### The stages -/

variable (M) in
/-- **The invariant of the implementation with bounds**: `EffInv`, the prices `0` off the faces
along the path and in `[0, i · Bst c]`. -/
def EffInvB (c f₀ : D → ℤ) (P : SPath M) (i : ℕ) (s : (D → ℤ) × (F → ℤ)) : Prop :=
  EffInv c f₀ P i s ∧ (∀ y, y ∉ P.faces → s.2 y = 0) ∧ ∀ y, 0 ≤ s.2 y ∧ s.2 y ≤ i * Bst D c

/-- **One stage preserves the bounded invariant.** -/
theorem fpStep_invB (hM : M.IsPlane) {c f₀ : D → ℤ} (hc : ∀ e, 0 ≤ c e) (hf₀ : IsPseudo M c f₀)
    {P : SPath M} {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P)
    {fr : FRFun F} (hfr : FRSpec fr) {i : ℕ} (hi : i < P.k) {s : (D → ℤ) × (F → ℤ)}
    (hs : EffInvB M c f₀ P i s) :
    EffInvB M c f₀ P (i + 1) (fpStep M c P ⟨P.faces, mssp P.darts (c - f₀)⟩ fr i s) := by
  obtain ⟨hinv, hz, hb⟩ := hs
  obtain ⟨h1, h2⟩ := fpStep_phi hM hc hf₀ hmssp hfr hi hinv
  refine ⟨fpStep_inv hM hc hf₀ hmssp hfr hi hinv, fun y hy => (h1 y hy).trans (hz y hy),
    fun y => ?_⟩
  have hB := Bst_nonneg c
  by_cases hy : y ∈ P.faces
  · obtain ⟨h3, h4⟩ := h2 y hy
    have := hb y
    push_cast
    constructor <;> nlinarith
  · have e1 := h1 y hy
    rw [hz y hy] at e1
    rw [e1]; exact ⟨le_rfl, mul_nonneg (by positivity) hB⟩

/-- The state of `fixPath` after `n` stages. -/
noncomputable def fpState (M : CombMap D V F) (c f₀ : D → ℤ) (P : SPath M)
    (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F) (n : ℕ) :
    (D → ℤ) × (F → ℤ) :=
  (List.range n).foldl (fun s i => fpStep M c P ⟨P.faces, mssp P.darts (c - f₀)⟩ fr i s) (f₀, 0)

lemma fpState_succ (M : CombMap D V F) (c f₀ : D → ℤ) (P : SPath M)
    (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F) (n : ℕ) :
    fpState M c f₀ P mssp fr (n + 1) =
      fpStep M c P ⟨P.faces, mssp P.darts (c - f₀)⟩ fr n (fpState M c f₀ P mssp fr n) := by
  unfold fpState
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `fixPath` is the final call on the state after the `k` stages. -/
lemma fixPath_eq_fpState (M : CombMap D V F) (c f₀ : D → ℤ) (P : SPath M)
    (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F)
    (negSSSP : (D → ℤ) → Option (F → ℤ)) :
    fixPath M c f₀ P mssp fr negSSSP =
      match negSSSP (c - (fpState M c f₀ P mssp fr P.k).1) with
      | some χ => (fpState M c f₀ P mssp fr P.k).1 + M.cob χ
      | none => (fpState M c f₀ P mssp fr P.k).1 := rfl

/-- **The bounded invariant holds after every stage.** -/
theorem fixPath_invB (hM : M.IsPlane) {c f₀ : D → ℤ} (hc : ∀ e, 0 ≤ c e) (hf₀ : IsPseudo M c f₀)
    {P : SPath M} {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P)
    {fr : FRFun F} (hfr : FRSpec fr) :
    ∀ n ≤ P.k, EffInvB M c f₀ P n (fpState M c f₀ P mssp fr n) := by
  intro n
  induction n with
  | zero =>
    intro _
    show EffInvB M c f₀ P 0 (f₀, 0)
    refine ⟨⟨0, fun y _ => rfl, fun e _ => rfl, hf₀.antisymm, ?_⟩, fun y _ => rfl,
      fun y => ⟨le_rfl, by simp⟩⟩
    have : f₀ + M.cob (0 : F → ℤ) = f₀ := by funext e; simp [cob]
    show P.FPInv c f₀ _ 0 (f₀ + M.cob 0)
    rw [this]
    exact P.fpInv_zero hf₀ (by have := absSum_nonneg c; omega)
  | succ n ih =>
    intro hn
    rw [fpState_succ]
    exact fpStep_invB hM hc hf₀ hmssp hfr (by omega) (ih (by omega))

/-- A pseudoflow is bounded by the boosted capacities. -/
lemma abs_le_capB (P : SPath M) {c g : D → ℤ} (hc : ∀ e, 0 ≤ c e) {Mb : ℤ} (hMb : 0 ≤ Mb)
    {i : ℕ} (hg : IsPseudo M (P.cap c Mb i) g) (e : D) : |g e| ≤ 2 * (absSum c + Mb) := by
  have hcap : ∀ d, |P.cap c Mb i d| ≤ absSum c + Mb := fun d => by
    have hle : P.cap c Mb i d ≤ c d + Mb := by unfold SPath.cap; split_ifs <;> omega
    have h0 : 0 ≤ P.cap c Mb i d := (hc d).trans (P.le_cap_zero c hMb i d)
    have hcd : c d ≤ absSum c :=
      (le_abs_self (c d)).trans (single_le_sum (f := fun d => |c d|)
        (fun d _ => abs_nonneg _) (mem_univ d))
    rw [abs_of_nonneg h0]; omega
  have := abs_le_of_pseudo hg e
  have := hcap e; have := hcap (M.rev e); linarith

/-- `|c e| ≤ absSum c`. -/
lemma abs_le_absSum (c : D → ℤ) (e : D) : |c e| ≤ absSum c :=
  single_le_sum (f := fun d => |c d|) (fun d _ => abs_nonneg _) (mem_univ e)

/-- **The explicit flow is bounded**: `f₀` off the path, and at most
`2 (absSum c + 4 absSum c + 1) + i · Bst c` in absolute value everywhere. -/
theorem EffInvB.flow_bound {c f₀ : D → ℤ} (hc : ∀ e, 0 ≤ c e) (hf₀ : IsPseudo M c f₀)
    {P : SPath M} {i : ℕ} {s : (D → ℤ) × (F → ℤ)} (h : EffInvB M c f₀ P i s) (e : D) :
    (e ∉ P.darts → s.1 e = f₀ e) ∧
      |s.1 e| ≤ 2 * (absSum c + (4 * absSum c + 1)) + i * Bst D c := by
  obtain ⟨⟨Φ, hφ, hoff, -, hinv⟩, hz, hb⟩ := h
  refine ⟨hoff e, ?_⟩
  have hA0 := absSum_nonneg c
  have hg := abs_le_capB P hc (by omega) hinv.pseudo e
  have hB := Bst_nonneg c
  have hi0 : (0 : ℤ) ≤ i * Bst D c := by positivity
  by_cases he : e ∈ P.darts
  · have hcob : M.cob s.2 e = M.cob Φ e := cob_eq_of_faces hφ he
    have h1 := hb (M.face (M.rev e)); have h2 := hb (M.face e)
    have hcb : |M.cob s.2 e| ≤ i * Bst D c := by
      unfold cob; rw [abs_le]; constructor <;> linarith
    rw [hcob] at hcb
    have : s.1 e = (s.1 + M.cob Φ) e - M.cob Φ e := by simp
    rw [this]
    calc |(s.1 + M.cob Φ) e - M.cob Φ e| ≤ |(s.1 + M.cob Φ) e| + |M.cob Φ e| := abs_sub _ _
      _ ≤ _ := by linarith
  · rw [hoff e he]
    have := abs_le_of_pseudo hf₀ e
    have := abs_le_absSum c e; have := abs_le_absSum c (M.rev e)
    linarith

/-! ### The final call -/

/-- **After the `k` stages, the explicit flow corrected by a potential is a pseudoflow for the
capacities `c`.** -/
theorem EffInvB.final {c f₀ : D → ℤ} {P : SPath M} {s : (D → ℤ) × (F → ℤ)}
    (h : EffInvB M c f₀ P P.k s) : ∃ Φ : F → ℤ, IsPseudo M c (s.1 + M.cob Φ) := by
  obtain ⟨⟨Φ, -, -, -, hinv⟩, -, -⟩ := h
  exact ⟨Φ, (SPath.FPInv.final P hinv).1⟩

/-- **The lengths `c - s.1` of the final call are nonnegative on the darts whose two sides are
the same face** (the loops of the dual). -/
theorem EffInvB.loop_nonneg {c f₀ : D → ℤ} {P : SPath M} {s : (D → ℤ) × (F → ℤ)}
    (h : EffInvB M c f₀ P P.k s) {d : D} (hd : M.face d = M.face (M.rev d)) :
    0 ≤ (c - s.1) d := by
  obtain ⟨Φ, hΦ⟩ := h.final
  have := hΦ.le_cap d
  have h0 : M.cob Φ d = 0 := by unfold cob; rw [hd]; ring
  simp only [Pi.add_apply, h0, add_zero] at this
  simp only [Pi.sub_apply]; linarith

/-- **The lengths of the final call are bounded.** -/
theorem EffInvB.len_bound {c f₀ : D → ℤ} (hc : ∀ e, 0 ≤ c e) (hf₀ : IsPseudo M c f₀)
    {P : SPath M} {i : ℕ} {s : (D → ℤ) × (F → ℤ)} (h : EffInvB M c f₀ P i s) (e : D) :
    |(c - s.1) e| ≤ 3 * absSum c + 2 * (4 * absSum c + 1) + i * Bst D c := by
  have h1 := (h.flow_bound hc hf₀ e).2
  have h2 := abs_le_absSum c e
  simp only [Pi.sub_apply]
  calc |c e - s.1 e| ≤ |c e| + |s.1 e| := abs_sub _ _
    _ ≤ _ := by linarith

end BKMNW

end PlanarFlow
