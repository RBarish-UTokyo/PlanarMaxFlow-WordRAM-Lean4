module

public import PlanarFlow.STFlow.ProgExec
public import PlanarFlow.STFlow.IsoCost

/-!
# The perturbed maximum flow on the machine with keys of polynomial size

The program `pstProg` (`PlanarFlow/STFlow/ProgExec.lean`) runs the perturbed algorithm for any
perturbation with the properties `PertOK` (nonnegative, separating the darts of the path of the
cotree, at most `m + 1` steps), storing one key per dart, `lkey N c ε g h = N (c - g) + (ε - h)`
with `N = 2 lexR F ε + 1`. With `lexEps` these keys have `O(m log m)` bits. With the word-size
perturbation `isoEps M t = isoL + isoW M t` (`PlanarFlow/STFlow/IsoEps.lean`, between `1` and
`(4 F + 6) #V`) every number the run handles is an integer of absolute value at most
`kH0 ≤ (m + 4) (2 R + 1) (Σ c + 1)`, `R = (F + 1) m (4 F + 6) #V`: polynomial in the size of
the map times the capacities (`Σ c ≤ m · max c`).

* `pertOK_iso`: **the word-size perturbation has the properties used by the program**
  (`lred_isoEps_inj`, `lstepsW_le`);
* `pstflowW_exec_exists`: **`pstflowW` on the machine**: an input and a starting configuration
  from which `pstProg` runs within `504 000 000 · m lg m` steps and ends with `pstflowW` in its
  output region; every real memory cell of the starting configuration (the lengths `N c + ε`,
  the capacities, the restriction, the constants `kTh`, `kH0`) is an integer of absolute value
  at most `isoW_bound`;
* `lkey_abs_le`, `isoKeys_bounded`: **along the run, the key of every dart, the length of every
  dart, the bottleneck amounts and the constants are integers of absolute value at most
  `kH0`**, and `kH0_iso_le`: `kH0 ≤ isoW_bound = (m + 4) (2 R + 1) (Σ c + 1)`.

**What remains of the real-RAM model.** The program keeps these integers in the real registers
of the machine (`WordRAM`), as the rest of the maximum-flow algorithm keeps its capacities and
lengths; the dynamic trees (`PlanarFlow/DynTree`) are written for real values. The bound proved
here is on the values of the run (keys, lengths, amounts, constants: what the dynamic trees store
as node values and add along paths); a bound on every intermediate register of the dynamic-tree
code (path aggregates of these values) is not stated.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW Klein DynTree WordRAM WordRAM.Machine

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-- **The word-size perturbation has the properties used by the program.** -/
theorem pertOK_iso (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {c : D → ℤ}
    (hc : ∀ d, 0 ≤ c d) {s t : V} (hst : s ≠ t) {d₀ : D} (hd₀ : M.tail d₀ = t) :
    PertOK M c (isoEps M t) s t d₀ where
  nonneg d := by have : Nonempty D := ⟨d₀⟩; exact isoEps_nonneg hM t d
  sep _ _ _ h₁ h₂ h := by have : Nonempty D := ⟨d₀⟩; exact lred_isoEps_inj hM h₁ h₂ h
  steps _ hI hroot n := lstepsW_le hM hrot hface hc hst hd₀ hI hroot n

lemma pstflowW_eq_E (c : D → ℤ) (X Y : Finset V) :
    pstflowW M c X Y = pstflowE M (isoEps M) c X Y := by
  unfold pstflowW pstflowE pcoreFlowW pcoreFlowE pcoreRunW
  split_ifs with h
  · cases linit M (capR M c X Y) (isoEps M (M.tail h.2.choose)) h.1.choose (M.tail h.2.choose)
      (M.face h.2.choose) <;> rfl
  · rfl

/-! ### The bound -/

variable (D V F) in
/-- `R = (F + 1) m (4 F + 6) #V`, a bound of `lexR F (isoEps M t)`. -/
def isoR : ℤ := (Fintype.card F + 1) * Fintype.card D * ((4 * Fintype.card F + 6) * Fintype.card V)

variable (D V F) in
/-- **The bound of the numbers of the run with the word-size perturbation**:
`(m + 4) (2 R + 1) (Σ c + 1)`. -/
def isoW_bound (c : D → ℤ) : ℤ := (Fintype.card D + 4) * (2 * isoR D V F + 1) * (∑ d, c d + 1)

lemma lexR_iso_le (hM : M.IsPlane) [Nonempty D] (t : V) :
    0 ≤ lexR F (isoEps M t) ∧ lexR F (isoEps M t) ≤ isoR D V F := by
  have h1 : ∑ d, isoEps M t d ≤ ∑ _d : D, (4 * Fintype.card F + 6) * (Fintype.card V : ℤ) :=
    sum_le_sum fun d _ => (isoEps_bounds hM t d).2
  have h0 : 0 ≤ ∑ d, isoEps M t d := sum_nonneg fun d _ => isoEps_nonneg hM t d
  simp only [sum_const, card_univ, nsmul_eq_mul] at h1
  unfold lexR isoR
  constructor
  · positivity
  · have : (0 : ℤ) ≤ Fintype.card F + 1 := by positivity
    nlinarith

/-- **`kH0` is polynomially bounded** for the word-size perturbation (`N = 2 lexR + 1`). -/
theorem kH0_iso_le (hM : M.IsPlane) [Nonempty D] (t : V) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) :
    kH0 D F (2 * lexR F (isoEps M t) + 1) c (isoEps M t) ≤ isoW_bound D V F c := by
  obtain ⟨h0, h1⟩ := lexR_iso_le hM t
  have hS : 0 ≤ ∑ d, c d := sum_nonneg fun d _ => hc d
  set R := lexR F (isoEps M t)
  have hZ : kZ D F (2 * R + 1) c (isoEps M t) ≤ (2 * isoR D V F + 1) * (∑ d, c d + 1) := by
    unfold kZ; nlinarith
  have hZ0 : 0 ≤ kZ D F (2 * R + 1) c (isoEps M t) := by unfold kZ; positivity
  unfold kH0 kTh isoW_bound
  have hR0 : 0 ≤ isoR D V F := le_trans h0 h1
  have : (0 : ℤ) ≤ (2 * isoR D V F + 1) * (∑ d, c d + 1) := by positivity
  nlinarith

/-! ### The machine -/

open Classical in
/-- **The single-source single-sink maximum flow with the word-size perturbation on the machine,
end to end**: for every plane map with transitive rotations and faces, nonnegative capacities,
`X` nonempty, a dart whose tail is in `Y`, and `X`, `Y` disjoint, there are an input, a word
bound and a starting configuration from which `pstProg` runs within `504 000 000 · m lg m` steps
(`m` darts) and ends with `OUT[d] = pstflowW M c X Y d` for every dart, printing nothing; every
real memory cell of the starting configuration is an integer of absolute value at most
`isoW_bound D V F (capR M c X Y) = (m + 4) (2 R + 1) (Σ capR c + 1)`. -/
theorem pstflowW_exec_exists (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) {X Y : Finset V} (hX : X.Nonempty)
    (hY : ∃ d, M.tail d ∈ Y) (hXY : Disjoint X Y) :
    ∃ (n B : ℕ) (P : Input) (c₀ c' : Config) (steps : ℕ),
      n = 2 * (Fintype.card F + Fintype.card V + Fintype.card D) ∧
      Exec P (B + 16 * (n + 1)) (pstProg B (Fintype.card D) n) c₀ c' steps ∧
      steps ≤ 504000000 * (Fintype.card D * lg (Fintype.card D)) ∧
      (∀ d, c'.rmem (aOT (Fintype.card D) + Fintype.equivFin D d) = pstflowW M c X Y d) ∧
      c'.output = c₀.output ∧
      ∀ a, ∃ z : ℤ, c₀.rmem a = z ∧ |z| ≤ isoW_bound D V F (capR M c X Y) := by
  have : Nonempty D := ⟨hY.choose⟩
  simp only [pstflowW_eq_E]
  obtain ⟨n, B, P, c₀, c', steps, h1, h2, h3, h4, h5, h6⟩ :=
    pstflowE_exec_exists hM hc hX hY hXY fun s t d₀ hst hd₀ =>
      pertOK_iso hM hrot hface (capR_nonneg hc X Y) hst hd₀
  refine ⟨n, B, P, c₀, c', steps, h1, h2, h3, h4, h5, fun a => ?_⟩
  obtain ⟨z, hz, hzle⟩ := h6 a
  exact ⟨z, hz, hzle.trans (kH0_iso_le hM _ (capR_nonneg hc X Y))⟩

/-! ### The numbers of the run -/

/-- **The key of every dart is at most `kZ = N Σ c + 2 lexR` in absolute value** under the
invariant, when `|μ| ≤ lexR` (not only on the path, `lkey_path_bound`). -/
theorem lkey_abs_le (hM : M.IsPlane) {c ε : D → ℤ} {s t : V} (hst : s ≠ t) {st : LSt M}
    (hI : LInv c ε s t st) (hε : ∀ d, 0 ≤ ε d) (hc : ∀ d, 0 ≤ c d)
    (hμ : |M.div st.h s| ≤ lexR F ε) {N : ℤ} (hN : 0 ≤ N) (d : D) :
    |lkey N c ε st.g st.h d| ≤ kZ D F N c ε := by
  have hle := hI.base.pseudo.le_cap d
  have hle' := hI.base.pseudo.le_cap (M.rev d)
  have hanti := hI.base.pseudo.antisymm d
  simp only [LSt.base_g] at hle hle' hanti
  have hpair : c d + c (M.rev d) ≤ ∑ d, c d := by
    have hdd : d ≠ M.rev d := (M.rev_ne d).symm
    rw [← sum_pair hdd]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => hc i
  have hx0 : 0 ≤ c d - st.g d := by linarith
  have hx1 : c d - st.g d ≤ ∑ d, c d := by have := hc (M.rev d); linarith
  -- the second coordinate: `lred - μ χ`
  have e := linv_h hM hst hI d
  have hl := abs_le.1 (abs_lred_le hε st.T d)
  obtain ⟨χa, -, -, χle⟩ := st.T.chi_spec hM s t
  have hχ1 := χle d
  have hχ2 := χle (M.rev d)
  rw [χa d] at hχ2
  have hy : |ε d - st.h d| ≤ 2 * lexR F ε := by
    have : ε d - st.h d = lred ε st.T d - M.div st.h s * st.T.chi s t d := by
      rw [e, lred]; ring
    rw [this]
    have hμχ : |M.div st.h s * st.T.chi s t d| ≤ lexR F ε := by
      rw [abs_mul]
      have : |st.T.chi s t d| ≤ 1 := abs_le.2 ⟨by omega, hχ1⟩
      nlinarith [abs_nonneg (M.div st.h s)]
    have := abs_sub (lred ε st.T d) (M.div st.h s * st.T.chi s t d)
    rw [abs_le] at hμχ ⊢
    constructor <;> linarith
  rw [abs_le] at hy ⊢
  unfold lkey kZ
  have h1 : N * (c d - st.g d) ≤ N * ∑ d, c d := mul_le_mul_of_nonneg_left hx1 hN
  have h2 : 0 ≤ N * (c d - st.g d) := mul_nonneg hN hx0
  have hR : 0 ≤ lexR F ε := (abs_nonneg _).trans hμ
  have h3 : 0 ≤ N * ∑ d, c d := mul_nonneg hN (sum_nonneg fun d _ => hc d)
  constructor <;> linarith

/-- **The numbers of the run with the word-size perturbation are polynomially bounded**: from the
initial state of `linit` (rooted at the face of a dart leaving `t`), at every step `i` of the run
and for every dart `d`, the key `lkey N c ε g h d` (`N = 2 lexR + 1`, the value stored for `d`
in the cotree structure; the bottleneck amount of a step is the key of the bottleneck), the
length `N c d + ε d` (stored in the dual tree) and the constants `kTh`, `kH0` are integers of
absolute value at most `isoW_bound D V F c = (m + 4) (2 R + 1) (Σ c + 1)`. -/
theorem isoKeys_bounded (hM : M.IsPlane) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) {s t : V}
    (hst : s ≠ t) {o : F} {st₀ : LSt M} (hlin : linit M c (isoEps M t) s t o = some st₀) (i : ℕ)
    (d : D) :
    |lkey (2 * lexR F (isoEps M t) + 1) c (isoEps M t)
        (ltraj M c (isoEps M t) s t st₀ i).g (ltraj M c (isoEps M t) s t st₀ i).h d| ≤
        isoW_bound D V F c ∧
      |wlen (2 * lexR F (isoEps M t) + 1) c (isoEps M t) d| ≤ isoW_bound D V F c ∧
      |kTh D F (2 * lexR F (isoEps M t) + 1) c (isoEps M t)| ≤ isoW_bound D V F c ∧
      |kH0 D F (2 * lexR F (isoEps M t) + 1) c (isoEps M t)| ≤ isoW_bound D V F c := by
  have : Nonempty D := ⟨d⟩
  obtain ⟨hR0, -⟩ := lexR_iso_le hM t
  have hW := kH0_iso_le hM t hc
  set ε := isoEps M t
  set N := 2 * lexR F ε + 1
  obtain ⟨-, hI₀⟩ := linit_inv _ _ hlin
  have hε : ∀ d, 0 ≤ ε d := fun d => isoEps_nonneg hM t d
  have hN : 0 ≤ N := by simp only [N]; omega
  have hμ₀ : |M.div st₀.h s| ≤ lexR F ε := by
    have e := (linit_eq hlin)
    rw [e]; simp only
    rw [show M.div (M.cob (st₀.T.psum ε)) s = 0 from M.div_cob _ s, abs_zero]; exact hR0
  have hμ := ltraj_mu hM hst hI₀ hε hμ₀ i
  have hS : 0 ≤ ∑ d, c d := sum_nonneg fun d _ => hc d
  have hZ0 : 0 ≤ kZ D F N c ε := by unfold kZ; positivity
  have hZH : kZ D F N c ε ≤ kH0 D F N c ε := by
    unfold kH0 kTh
    have : (0 : ℤ) ≤ (Fintype.card D + 2) * kZ D F N c ε := by positivity
    linarith
  have hTH : kTh D F N c ε ≤ kH0 D F N c ε := by
    unfold kH0
    have : (0 : ℤ) ≤ (Fintype.card D + 2) * kZ D F N c ε := by positivity
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (lkey_abs_le hM hst (ltraj_inv hM hI₀ i) hε hc hμ hN d).trans (hZH.trans hW)
  · have hεle : ε d ≤ lexR F ε := by
      have h1 : ε d ≤ ∑ d, ε d := single_le_sum (fun d _ => hε d) (mem_univ d)
      have h2 : (0 : ℤ) ≤ Fintype.card F * ∑ d, ε d :=
        mul_nonneg (by positivity) (sum_nonneg fun d _ => hε d)
      unfold lexR; linarith
    have hcle : c d ≤ ∑ d, c d := single_le_sum (fun d _ => hc d) (mem_univ d)
    have h2 : N * c d ≤ N * ∑ d, c d := mul_le_mul_of_nonneg_left hcle hN
    have h3 : 0 ≤ N * c d := mul_nonneg hN (hc d)
    have hwk : |wlen N c ε d| ≤ kZ D F N c ε := by
      rw [abs_le]; unfold wlen kZ
      have := hε d
      constructor <;> linarith
    exact hwk.trans (hZH.trans hW)
  · rw [abs_of_nonneg (by unfold kTh; omega)]; exact hTH.trans hW
  · rw [abs_of_nonneg (by linarith [show 0 ≤ kTh D F N c ε by unfold kTh; omega])]; exact hW

end STFlow

end PlanarFlow
