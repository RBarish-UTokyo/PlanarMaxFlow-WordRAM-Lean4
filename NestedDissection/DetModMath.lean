module

public import NestedDissection.DetModSpec
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Determinants modulo a prime: row operations on a stored matrix

`DetMod.mat` is defined in `NestedDissection/DetModSpec.lean`.

An `n × n` matrix stored row by row in a memory `m : ℕ → ℕ` (`m (i * n + j)` is the entry
`(i, j)`), read in `ZMod p` (`DetMod.mat`). The facts behind Gaussian elimination with row
exchanges: a row exchange negates the determinant (`DetMod.det_swap`), subtracting a multiple
of another row keeps it (`DetMod.det_rowop`), a triangular matrix has the product of its
diagonal as determinant (`DetMod.det_triangular`), and the arithmetic of the machine
(`DetMod.cast_combo`, Fermat's little theorem `DetMod.fermat`).
-/

@[expose] public section

namespace NestedDissection

namespace DetMod

open Matrix Finset

/-- The product of the first `k` diagonal entries. -/
def diag (n p : ℕ) (m : ℕ → ℕ) (k : ℕ) : ZMod p := ∏ i ∈ range k, (m (i * n + i) : ZMod p)

variable {n p : ℕ}

theorem iteP {α : Type} {q : Prop} [Decidable q] (h : q) {a b : α} :
    (if q then a else b) = a := by simp [h]

theorem iteN {α : Type} {q : Prop} [Decidable q] (h : ¬ q) {a b : α} :
    (if q then a else b) = b := by simp [h]

theorem idx_lt {i j : ℕ} (hi : i < n) (hj : j < n) : i * n + j < n * n := by
  have : (i + 1) * n ≤ n * n := Nat.mul_le_mul_right _ hi
  rw [Nat.add_mul, Nat.one_mul] at this; omega

theorem idx_inj {i j i' j' : ℕ} (hj : j < n) (hj' : j' < n) (h : i * n + j = i' * n + j') :
    i = i' ∧ j = j' := by
  have h1 : (i * n + j) / n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have h2 : (i' * n + j') / n = i' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj', Nat.zero_add]
  have e : i = i' := by rw [← h1, ← h2, h]
  subst e; exact ⟨rfl, by omega⟩

/-- **A row exchange negates the determinant.** -/
theorem det_swap {m m' : ℕ → ℕ} {k r : ℕ} (hk : k < n) (hr : r < n) (hkr : k ≠ r)
    (h : ∀ i < n, ∀ j < n,
      m' (i * n + j) = m ((if i = k then r else if i = r then k else i) * n + j)) :
    (mat n p m').det = - (mat n p m).det := by
  have e : mat n p m' = (mat n p m).submatrix (Equiv.swap ⟨k, hk⟩ ⟨r, hr⟩) id := by
    ext i j
    simp only [mat, submatrix_apply, id]
    rw [h i i.2 j j.2]
    congr 3
    by_cases h1 : (i : ℕ) = k
    · have e : i = ⟨k, hk⟩ := Fin.ext h1
      subst e; simp
    · by_cases h2 : (i : ℕ) = r
      · have e : i = ⟨r, hr⟩ := Fin.ext h2
        subst e; simp [hkr.symm]
      · rw [Equiv.swap_apply_of_ne_of_ne (fun e => h1 (congrArg Fin.val e))
          (fun e => h2 (congrArg Fin.val e))]
        simp [h1, h2]
  rw [e, det_permute, Equiv.Perm.sign_swap (fun h => hkr (congrArg Fin.val h))]
  simp

/-- **Subtracting a multiple of another row keeps the determinant.** -/
theorem det_rowop {m m' : ℕ → ℕ} {i k : ℕ} (hi : i < n) (hk : k < n) (hik : i ≠ k) (f : ZMod p)
    (hrow : ∀ j < n, (m' (i * n + j) : ZMod p) = m (i * n + j) - f * m (k * n + j))
    (hoth : ∀ i' < n, i' ≠ i → ∀ j < n, m' (i' * n + j) = m (i' * n + j)) :
    (mat n p m').det = (mat n p m).det := by
  have e : mat n p m' = updateRow (mat n p m) ⟨i, hi⟩ (mat n p m ⟨i, hi⟩ + (-f) • mat n p m ⟨k, hk⟩) := by
    ext a j
    by_cases ha : (a : ℕ) = i
    · have e : a = ⟨i, hi⟩ := Fin.ext ha
      subst e
      simp only [updateRow_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mat]
      rw [hrow j j.2]; ring
    · rw [updateRow_ne (fun e => ha (congrArg Fin.val e))]
      simp only [mat]; rw [hoth a a.2 ha j j.2]
  rw [e, det_updateRow_add_smul_self _ (fun e => hik (congrArg Fin.val e))]

/-- **A triangular matrix has the product of its diagonal as determinant.** -/
theorem det_triangular {m : ℕ → ℕ} (h : ∀ i < n, ∀ j < i, (m (i * n + j) : ZMod p) = 0) :
    (mat n p m).det = diag n p m n := by
  have hU : (mat n p m).IsUpperTriangular := fun (i j : Fin n) (hij : j < i) => h i i.2 j hij
  rw [det_of_isUpperTriangular hU, diag,
    ← Fin.prod_univ_eq_prod_range (fun i => (m (i * n + i) : ZMod p)) n]
  rfl

theorem diag_succ (m : ℕ → ℕ) (k : ℕ) :
    diag n p m (k + 1) = diag n p m k * (m (k * n + k) : ZMod p) := by
  simp [diag, prod_range_succ]

theorem diag_congr {m m' : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, m' (i * n + i) = m (i * n + i)) :
    diag n p m' k = diag n p m k :=
  prod_congr rfl fun i hi => by rw [h i (mem_range.1 hi)]

/-- The arithmetic of a row operation on the machine. -/
theorem cast_combo {a b f : ℕ} (hf : f ≤ p) :
    (((a + (p - f) * b) % p : ℕ) : ZMod p) = a - f * b := by
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hf, ZMod.natCast_self]; ring

theorem cast_mulmod (a b : ℕ) : (((a * b) % p : ℕ) : ZMod p) = a * b := by
  rw [ZMod.natCast_mod, Nat.cast_mul]

/-- **Fermat's little theorem**, the inverse of a nonzero residue. -/
theorem fermat [Fact p.Prime] {a : ℕ} (ha : (a : ZMod p) ≠ 0) : (a : ZMod p) ^ (p - 2) * a = 1 := by
  have h2 := (Fact.out : p.Prime).two_le
  rw [← pow_succ, show p - 2 + 1 = p - 1 by omega]
  exact ZMod.pow_card_sub_one_eq_one ha

end DetMod

end NestedDissection
