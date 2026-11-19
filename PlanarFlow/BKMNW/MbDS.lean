module

public import PlanarFlow.BKMNW.MbBaseSpec

/-!
# Miller's path decoded: the pure part

The certificate's path `corePath C` has the darts `(stE C j).1`, `j < stN C`, read off Miller's
cycle `C` of the stellar subdivision (`ExistMillerD.lean`). The machine has the cycle as the
codes `stNum cd (C.d l)` (`l < C.k`, `cd` the rank numbering). This file gives the natural-number
model of the decoding the program `mbD` (`MbDP.lean`) runs, and proves that it computes the darts:

* `pdUp` (the flag of an `up` code), `pdSel` (branch-free selection), `pdDec` (the rank of the
  dart of the map under a code), `pdS`, `pdStp`, `pdG`, `pdEq`, `pdLt`, **`pdOut`** (the rank of
  `stE C j` from the position `stG C j`), with their `if` forms;
* **`pd_dec`**, `pd_s`, `pd_stp`, **`pd_G`** (`pdG = stG`), **`lt_stN_iff`**
  (`j < stN C ↔ stG C j < C.k`), **`pd_out`** (`pdOut … (stG C j) = cd (stE C j)` for
  `j < stN C`);
* **`stN_le_card`** (the vertices of the path are distinct, so `stN C ≤` the number of vertices).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

/-! ### The natural-number model -/

/-- The flag of an `up` code (`v % 3 = 1`), branch-free. -/
def pdUp (v : ℕ) : ℕ := 1 - ((v % 3 - 1) + (1 - v % 3))

/-- Branch-free selection: `x` if `f = 1`, `y` if `f = 0`. -/
def pdSel (f x y : ℕ) : ℕ := f * x + (1 - f) * y

/-- The rank of the dart of the map under the code `v` (`cr`: reverses, `sr`: rotation). -/
def pdDec (cr sr : ℕ → ℕ) (v : ℕ) : ℕ := pdSel (pdUp v) (sr (cr (v / 3))) (v / 3)

/-- The start of the path: `1` if the first code is a `down` code. -/
def pdS (cy : ℕ → ℕ) : ℕ := cy 0 % 3 / 2

/-- The step from a position: `2` at an `up` code, else `1`. -/
def pdStp (cy : ℕ → ℕ) (k s g : ℕ) : ℕ := 1 + pdUp (cy ((s + g) % k))

/-- The positions of the vertices of the map. -/
def pdG (cy : ℕ → ℕ) (k s : ℕ) (j : ℕ) : ℕ := Nat.rec 0 (fun _ g => g + pdStp cy k s g) j

/-- The equality flag, branch-free. -/
def pdEq (a b : ℕ) : ℕ := 1 - ((a - b) + (b - a)) / ((a - b) + (b - a))

/-- The flag `g + 2 < k`, branch-free. -/
def pdLt (g k : ℕ) : ℕ := (k - (g + 2)) / (k - (g + 2))

/-- **The rank of the dart of the path from the position `g`** (as the machine computes it). -/
def pdOut (cy cr sr iv tk : ℕ → ℕ) (k s g : ℕ) : ℕ :=
  pdSel (pdUp (cy ((s + g) % k)) * pdLt g k)
    (pdSel (pdEq (tk (iv (sr (cr (pdDec cr sr (cy ((s + g) % k)))))))
        (tk (iv (pdDec cr sr (cy ((s + g + 1) % k))))))
      (pdDec cr sr (cy ((s + g) % k))) (cr (pdDec cr sr (cy ((s + g + 1) % k)))))
    (pdDec cr sr (cy ((s + g) % k)))

lemma pdUp_eq (v : ℕ) : pdUp v = if v % 3 = 1 then 1 else 0 := by
  unfold pdUp; have := Nat.mod_lt v (show 0 < 3 by norm_num); split_ifs <;> omega

lemma pdUp_le (v : ℕ) : pdUp v ≤ 1 := by unfold pdUp; omega

lemma pdSel_eq {f : ℕ} (hf : f ≤ 1) (x y : ℕ) : pdSel f x y = if f = 1 then x else y := by
  unfold pdSel
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hf with rfl | rfl <;> simp

lemma pdSel_one (x y : ℕ) : pdSel 1 x y = x := by simp [pdSel]

lemma pdSel_zero (x y : ℕ) : pdSel 0 x y = y := by simp [pdSel]

lemma pdSel_le {f x y W : ℕ} (hf : f ≤ 1) (hx : x ≤ W) (hy : y ≤ W) : pdSel f x y ≤ W := by
  rw [pdSel_eq hf]; split_ifs <;> assumption

lemma pdEq_eq (a b : ℕ) : pdEq a b = if a = b then 1 else 0 := by
  unfold pdEq
  split_ifs with h
  · subst h; simp
  · have : 0 < (a - b) + (b - a) := by omega
    rw [Nat.div_self this]

lemma pdEq_le (a b : ℕ) : pdEq a b ≤ 1 := by unfold pdEq; exact Nat.sub_le _ _

lemma pdLt_eq (g k : ℕ) : pdLt g k = if g + 2 < k then 1 else 0 := by
  unfold pdLt
  split_ifs with h
  · exact Nat.div_self (by omega)
  · simp [show k - (g + 2) = 0 by omega]

lemma pdLt_le (g k : ℕ) : pdLt g k ≤ 1 := by rw [pdLt_eq]; split_ifs <;> omega

lemma pdDec_eq (cr sr : ℕ → ℕ) (v : ℕ) :
    pdDec cr sr v = if v % 3 = 1 then sr (cr (v / 3)) else v / 3 := by
  unfold pdDec; rw [pdSel_eq (pdUp_le v), pdUp_eq]; split_ifs <;> simp_all

lemma pdG_succ (cy : ℕ → ℕ) (k s j : ℕ) :
    pdG cy k s (j + 1) = pdG cy k s j + pdStp cy k s (pdG cy k s j) := rfl

lemma pdG_zero (cy : ℕ → ℕ) (k s : ℕ) : pdG cy k s 0 = 0 := rfl

lemma pdG_lt_succ (cy : ℕ → ℕ) (k s j : ℕ) : pdG cy k s j < pdG cy k s (j + 1) := by
  rw [pdG_succ]; unfold pdStp; omega

lemma pdG_mono (cy : ℕ → ℕ) (k s : ℕ) : Monotone (pdG cy k s) :=
  monotone_nat_of_le_succ fun j => (pdG_lt_succ cy k s j).le

lemma pdG_ge (cy : ℕ → ℕ) (k s j : ℕ) : j ≤ pdG cy k s j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih => have := pdG_lt_succ cy k s j; omega

lemma pdStp_le (cy : ℕ → ℕ) (k s g : ℕ) : pdStp cy k s g ≤ 2 := by
  unfold pdStp; have := pdUp_le (cy ((s + g) % k)); omega

/-! ### The model computes the path -/

section Sem

open PlanarSeparator PlanarSeparator.Map PlanarSeparator.StDart

variable {X Q : Type*} [Fintype X] [DecidableEq X] [DecidableEq Q] {N : Map X Q} {m : ℕ}

lemma pd_up_iff (cd : X ≃ Fin m) (δ : StDart X) : N.stNum cd δ % 3 = 1 ↔ IsUp δ := by
  cases δ <;> simp [stNum, IsUp] <;> omega

lemma pd_dn_iff (cd : X ≃ Fin m) (δ : StDart X) : N.stNum cd δ % 3 / 2 = if IsDn δ then 1 else 0 := by
  cases δ <;> simp [stNum, IsDn] <;> omega

/-- **The decoding of a code**: the rank of the dart of the map under it. -/
lemma pd_dec (cd : X ≃ Fin m) {cr sr : ℕ → ℕ} (hcr : ∀ y, cr (cd y) = cd (N.α y))
    (hsr : ∀ y, sr (cd y) = cd (N.σ y)) (δ : StDart X) :
    pdDec cr sr (N.stNum cd δ) = cd (stU δ) := by
  rw [pdDec_eq]
  cases δ with
  | old d =>
    have h1 : (3 * (cd d : ℕ)) % 3 = 0 := by omega
    have h2 : (3 * (cd d : ℕ)) / 3 = cd d := by omega
    simp only [stNum, stU, h1, h2]; simp
  | up e =>
    have h1 : (3 * (cd (N.φ.symm e) : ℕ) + 1) % 3 = 1 := by omega
    have h2 : (3 * (cd (N.φ.symm e) : ℕ) + 1) / 3 = cd (N.φ.symm e) := by omega
    simp only [stNum, stU, h1, h2, ite_true, hcr, hsr]
    rw [← φ_apply, Equiv.apply_symm_apply]
  | down d =>
    have h1 : (3 * (cd d : ℕ) + 2) % 3 = 2 := by omega
    have h2 : (3 * (cd d : ℕ) + 2) / 3 = cd d := by omega
    simp only [stNum, stU, h1, h2]; simp

variable (cd : X ≃ Fin m) (C : N.stellar.SCycle) {cy cr sr iv tk : ℕ → ℕ}

lemma pd_s (hcy : ∀ l < C.k, cy l = N.stNum cd (C.d l)) : pdS cy = stS C := by
  unfold pdS stS
  rw [hcy 0 C.pos, pd_dn_iff]

lemma pd_cy (hcy : ∀ l < C.k, cy l = N.stNum cd (C.d l)) (g : ℕ) :
    cy ((stS C + g) % C.k) = N.stNum cd (stD C g) := hcy _ (Nat.mod_lt _ C.pos)

lemma pd_stp (hcy : ∀ l < C.k, cy l = N.stNum cd (C.d l)) (g : ℕ) :
    pdStp cy C.k (stS C) g = stStp (stD C g) := by
  unfold pdStp stStp
  rw [pd_cy cd C hcy, pdUp_eq]
  by_cases h : IsUp (stD C g)
  · rw [iteT ((pd_up_iff cd _).2 h), iteT h]
  · rw [iteF (fun h' => h ((pd_up_iff cd _).1 h')), iteF h]

/-- **The positions of the model are those of the path.** -/
lemma pd_G (hcy : ∀ l < C.k, cy l = N.stNum cd (C.d l)) (j : ℕ) :
    pdG cy C.k (stS C) j = stG C j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pdG_succ, ih, pd_stp cd C hcy]
    rfl

lemma stG_succ (j : ℕ) : stG C (j + 1) = stG C j + stStp (stD C (stG C j)) := rfl

lemma stG_mono' : Monotone (stG C) :=
  monotone_nat_of_le_succ fun j => by rw [stG_succ]; omega

/-- **The vertices of the path are the positions before the end.** -/
lemma lt_stN_iff (j : ℕ) : j < stN C ↔ stG C j < C.k := by
  unfold stN
  rw [Nat.lt_find_iff]
  constructor
  · intro h; exact not_le.1 (h j le_rfl)
  · intro h j' hj'; exact not_le.2 (lt_of_le_of_lt (stG_mono' C hj') h)

/-- **The model computes the darts of the path** (as ranks). -/
theorem pd_out (hcy : ∀ l < C.k, cy l = N.stNum cd (C.d l)) (hcr : ∀ y, cr (cd y) = cd (N.α y))
    (hsr : ∀ y, sr (cd y) = cd (N.σ y))
    (htk : ∀ y y', tk (iv (cd y)) = tk (iv (cd y')) ↔ N.vert y = N.vert y') {j : ℕ}
    (hj : j < stN C) :
    pdOut cy cr sr iv tk C.k (stS C) (stG C j) = cd (stE C j) := by
  have h0 := pd_cy cd C hcy (stG C j)
  have h1 : cy ((stS C + stG C j + 1) % C.k) = N.stNum cd (stD C (stG C j + 1)) := by
    rw [show stS C + stG C j + 1 = stS C + (stG C j + 1) by omega]; exact pd_cy cd C hcy _
  unfold pdOut
  rw [h0, h1, pd_dec cd hcr hsr, pd_dec cd hcr hsr, hcr, hsr, pdUp_eq, pdLt_eq]
  unfold stE
  by_cases hu : IsUp (stD C (stG C j))
  · rw [iteT ((pd_up_iff cd _).2 hu), one_mul]
    by_cases hlt : stG C j + 2 < C.k
    · have hj1 : j + 1 < stN C := by
        rw [lt_stN_iff, stG_succ]
        unfold stStp; rw [iteT hu]; exact hlt
      rw [iteT hlt, iteT ⟨hj1, hu⟩, pdSel_one, pdEq_eq, ← φ_apply]
      by_cases he : N.vert (N.φ (stU (stD C (stG C j)))) = N.vert (stU (stD C (stG C j + 1)))
      · rw [iteT ((htk _ _).2 he), iteT he, pdSel_one]
      · rw [iteF (fun h => he ((htk _ _).1 h)), iteF he, pdSel_zero, hcr]
    · have hj1 : ¬ (j + 1 < stN C ∧ IsUp (stD C (stG C j))) := by
        rintro ⟨h, -⟩
        rw [lt_stN_iff, stG_succ] at h
        unfold stStp at h; rw [iteT hu] at h; exact hlt h
      rw [iteF hlt, iteF hj1, pdSel_zero]
  · rw [iteF (fun h => hu ((pd_up_iff cd _).1 h)), zero_mul, pdSel_zero,
      iteF (fun h => hu h.2)]

/-- **The path has at most as many vertices as the map** (they are distinct). -/
lemma stN_le_card [Fintype Q] (hl : ∀ d, N.vert (N.α d) ≠ N.vert d)
    (hsm : ∀ x y, N.face x = N.face y → y = x ∨ y = N.φ x ∨ y = N.φ.symm x)
    (C : N.stellar.SCycle) : stN C ≤ Fintype.card Q := by
  obtain ⟨-, -, -, hinj, -⟩ := stellar_cycle_path' hl hsm C
  have := Fintype.card_le_of_injective (fun i : Fin (stN C) => N.vert (stE C i))
    (fun i j h => Fin.ext (hinj i i.2 j j.2 h))
  simpa using this

end Sem

section Psep

open Finset Function Equiv Orbit CombMap PlanarSeparator PlanarSeparator.Map

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The path of Miller's base has at most `#N` vertices.** -/
lemma stN_psep_le (hloopM : ∀ d, M.head d ≠ M.tail d) {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) {N : Finset D} {τ : Perm D} (hN : PMap M N Hs τ)
    (hne : N.Nonempty) (hnc : NoCut M N Hs) (C : (psep M hN.stable hN.rev).stellar.SCycle) :
    stN C ≤ #N := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  have hsmall := hN.small_of_noCut hd hloopM hx₀ hnc
  have hl : ∀ d, (psep M hN.stable hN.rev).vert ((psep M hN.stable hN.rev).α d) ≠
      (psep M hN.stable hN.rev).vert d := (psep_run_conds hloopM hN ⟨x₀, hx₀⟩).1
  have hsm : ∀ x y, (psep M hN.stable hN.rev).face x = (psep M hN.stable hN.rev).face y →
      y = x ∨ y = (psep M hN.stable hN.rev).φ x ∨ y = (psep M hN.stable hN.rev).φ.symm x := by
    intro x y h
    have hy : y.1 ∈ pface M τ N x.1 := mem_pface.2 ⟨y.2, (psep_face_eq hN.stable hN.rev).1 h⟩
    rcases hsmall x.1 x.2 y.1 hy with e | e | e
    · exact Or.inl (Subtype.ext e)
    · exact Or.inr (Or.inl (Subtype.ext (by rw [e, psep_φ]; rfl)))
    · exact Or.inr (Or.inr (Subtype.ext (by rw [e, psep_φ_symm])))
  exact (stN_le_card hl hsm C).trans card_sVert_le

end Psep

end BKMNW

end PlanarFlow
