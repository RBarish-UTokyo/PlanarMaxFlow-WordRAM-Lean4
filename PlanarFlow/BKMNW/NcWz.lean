module

public import PlanarFlow.BKMNW.StCallZB

/-!
# A polynomial bound of the zero area of the s-t flow call

`stCallZ` (inside `c2tP`) needs a base `ib` in the zero area with
`pstWN (101 m + 45) (stHb …) < ib`, `339 m + 128 ≤ ib`, `ib + pstWN (101 m + 45) (stHb …) ≤ Wz`
and `stWc … ≤ Wz`. The bound `stHb` depends on the numbers of vertices and faces of the piece map
and on the capacities. Here, with `q = m + Z + 100`:

* **`wzQ m Z = q ^ 32`**, **`wzc m Z = 3 · wzQ m Z`** (the lower bound of the zero area that
  the specifications of `c2sP` ask for);
* **`stWc_le_wzQ`**: on a map with `m` darts and at most `m` vertices and faces, for capacities in
  `[0, 2Z]` and `1 ≤ m`: `stWc … ≤ wzQ m Z` (the whole word bound of the canonical run, which
  includes `pstWN (101 m + 45) (stHb …) + 339 m + 128`);
* **`wz_ib`**: hence `ib = wzQ m Z + 339 m + 128` meets the four bounds when `wzc m Z ≤ Wz`.

The head of `c2sP` computes `ib` from `m` and `Z` (`q`, five squarings).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset STFlow StCall

/-- `q = m + Z + 100`. -/
def wzq (m Z : ℕ) : ℕ := m + Z + 100

/-- **The bound of the words of the s-t flow call**: `(m + Z + 100) ^ 32`. -/
def wzQ (m Z : ℕ) : ℕ := wzq m Z ^ 32

/-- **The lower bound of the zero area** asked by the specifications of `c2sP`, `s2cP`. -/
def wzc (m Z : ℕ) : ℕ := 3 * wzQ m Z

/-- The bound of the isolating weight bound, in `m` and `Z`. -/
def wzK (m Z : ℕ) : ℕ := (m + 4) * (2 * ((m + 1) * m * ((4 * m + 6) * m)) + 1) * (m * (2 * Z * m + 1) + 1)

lemma wzK_le (m Z : ℕ) : wzK m Z ≤ wzq m Z ^ 9 := by
  unfold wzK wzq
  set q := m + Z + 100 with hq
  have h1 : m + 4 ≤ q := by omega
  have h2 : 2 * ((m + 1) * m * ((4 * m + 6) * m)) + 1 ≤ q ^ 5 := by
    have a1 : m + 1 ≤ q := by omega
    have a2 : m ≤ q := by omega
    have a3 : 4 * m + 6 ≤ 4 * q := by omega
    have b : (m + 1) * m * ((4 * m + 6) * m) ≤ q * q * ((4 * q) * q) :=
      Nat.mul_le_mul (Nat.mul_le_mul a1 a2) (Nat.mul_le_mul a3 a2)
    have e : q * q * ((4 * q) * q) = 4 * q ^ 4 := by ring
    have e5 : q ^ 5 = q * q ^ 4 := by ring
    have hq4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
    have : 100 * q ^ 4 ≤ q * q ^ 4 := Nat.mul_le_mul_right _ (by omega)
    omega
  have h3 : m * (2 * Z * m + 1) + 1 ≤ q ^ 3 := by
    have a2 : m ≤ q := by omega
    have b1 : 2 * Z * m + 1 ≤ q * q := by
      have : (m + Z) * (m + Z) + 1 ≤ q * q := by
        have : m + Z + 1 ≤ q := by omega
        nlinarith
      nlinarith
    have b2 : m * (2 * Z * m + 1) ≤ m * (q * q) := Nat.mul_le_mul_left _ b1
    have b3 : m * (q * q) + 1 ≤ q * (q * q) := by
      have : m + 1 ≤ q := by omega
      have hqq : 1 ≤ q * q := Nat.one_le_iff_ne_zero.2 (by positivity)
      nlinarith
    have e : q ^ 3 = q * (q * q) := by ring
    omega
  have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have e : q * q ^ 5 * q ^ 3 = q ^ 9 := by ring
  omega

/-- `pstVb` is monotone in all its arguments. -/
lemma pstVb_mono4 {n cD cF cV K n' cD' cF' cV' K' : ℕ} (h1 : n ≤ n') (h2 : cD ≤ cD')
    (h3 : cF ≤ cF') (h4 : cV ≤ cV') (h5 : K ≤ K') :
    pstVb n cD cF cV K ≤ pstVb n' cD' cF' cV' K' := by
  unfold pstVb
  gcongr

/-- The value of `pstVb` at the bounds. -/
lemma pstVb_le_q {q t : ℕ} (hq : 100 ≤ q) (ht : 1 ≤ t) :
    pstVb (5 * q) q q q t ≤ q ^ 3 * t := by
  unfold pstVb
  have e : q ^ 3 * t = q * q * q * t := by ring
  rw [e]
  have h1 : 100 * (q * q * t) ≤ q * q * q * t := by
    have : 100 * (q * q * t) = 100 * q * (q * t) := by ring
    have h' : q * q * q * t = q * q * (q * t) := by ring
    rw [this, h']; exact Nat.mul_le_mul_right _ (by nlinarith)
  have h2 : q * t ≤ q * q * t := by
    have : q * t ≤ q * (q * t) := Nat.le_mul_of_pos_left _ (by omega)
    have e' : q * (q * t) = q * q * t := by ring
    omega
  have h3 : q ≤ q * t := Nat.le_mul_of_pos_right _ ht
  have h4 : t ≤ q * t := Nat.le_mul_of_pos_left _ (by omega)
  have e1 : 5 * q * (4 * (q + q) * t) = 40 * (q * q * t) := by ring
  have e2 : (q + 2) * (2 * (5 * q) * t + 5 * q + 4 * t) =
      10 * (q * q * t) + 5 * (q * q) + 4 * (q * t) + 20 * (q * t) + 10 * q + 8 * t := by ring
  have e3 : 5 * q * (8 * q * t) = 40 * (q * q * t) := by ring
  have h5 : q * q ≤ q * q * t := Nat.le_mul_of_pos_right _ ht
  have h6 : 100 * (q * t) ≤ q * q * t := by
    have : q * q * t = q * (q * t) := by ring
    rw [this]; exact Nat.mul_le_mul_right _ hq
  have h7 : 1 ≤ q * t := Nat.one_le_iff_ne_zero.2 (by positivity)
  rw [e1, e2, e3]
  omega

/-- **The bound of `pstWN` at the bounds of the s-t flow call**, as a polynomial in `m`, `Z`. -/
lemma pstWN_le_wz {m Z : ℕ} (hm : 1 ≤ m) :
    pstWN (101 * m + 45) (pstH (4 * m + 1) m m m (wzK m Z)) + 339 * m + 128 + (4 * m + 5) * m +
      2 * m + 2 * Z * m + 1 ≤ wzQ m Z := by
  unfold wzQ
  have hq : 100 ≤ wzq m Z := by unfold wzq; omega
  set q := wzq m Z with hqd
  have hmq : m + Z + 100 = q := by rw [hqd]; rfl
  have hK := wzK_le m Z
  rw [← hqd] at hK
  have ht : 1 ≤ q ^ 9 := Nat.one_le_pow _ _ (by omega)
  have hV : pstVb (4 * m + 1) m m m (wzK m Z) ≤ q ^ 3 * q ^ 9 :=
    (pstVb_mono4 (by omega) (by omega) (by omega) (by omega) hK).trans (pstVb_le_q hq ht)
  have e12 : q ^ 3 * q ^ 9 = q ^ 12 := by ring
  rw [e12] at hV
  have hH : pstH (4 * m + 1) m m m (wzK m Z) ≤ 2 * q ^ 12 := by unfold pstH; omega
  have hq12 : 100 * q ^ 12 ≤ q ^ 13 := by
    have : q ^ 13 = q * q ^ 12 := by ring
    rw [this]; exact Nat.mul_le_mul_right _ hq
  have hM : pstM (pstH (4 * m + 1) m m m (wzK m Z)) ≤ q ^ 13 := by
    unfold pstM
    have : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ (by omega)
    omega
  have hM2 : pstM (pstH (4 * m + 1) m m m (wzK m Z)) * pstM (pstH (4 * m + 1) m m m (wzK m Z)) ≤
      q ^ 13 * q ^ 13 := Nat.mul_le_mul hM hM
  have e26 : q ^ 13 * q ^ 13 = q ^ 26 := by ring
  rw [e26] at hM2
  have hsmall : 2 * (101 * m + 45) + 1 + 339 * m + 128 + (4 * m + 5) * m + 2 * m + 2 * Z * m + 1 ≤
      q ^ 3 := by
    have e3 : q ^ 3 = q * q * q := by ring
    rw [e3]
    have d0 : 100 * q ≤ q * q := Nat.mul_le_mul_right q hq
    have a : 543 * m + 220 ≤ 6 * (q * q) := by omega
    have b : (4 * m + 5) * m ≤ (5 * q) * q := Nat.mul_le_mul (by omega) (by omega)
    have b' : 2 * Z * m ≤ (2 * q) * q := Nat.mul_le_mul (by omega) (by omega)
    have e5 : (5 * q) * q = 5 * (q * q) := by ring
    have e2 : (2 * q) * q = 2 * (q * q) := by ring
    have d : q ≤ q * q := Nat.le_mul_of_pos_left _ (by omega)
    have c0 := Nat.mul_le_mul_right (q * q) hq
    have ec : q * (q * q) = q * q * q := by ring
    omega
  have h26 : q ^ 3 + q ^ 13 + q ^ 26 ≤ q ^ 32 := by
    have a1 : q ^ 3 ≤ q ^ 13 := Nat.pow_le_pow_right (by omega) (by omega)
    have a2 : q ^ 13 ≤ q ^ 26 := Nat.pow_le_pow_right (by omega) (by omega)
    have a3 : 3 * q ^ 26 ≤ q ^ 32 := by
      have : q ^ 32 = q ^ 6 * q ^ 26 := by ring
      rw [this]
      have : 3 ≤ q ^ 6 := le_trans (by omega) (Nat.le_self_pow (by omega) q)
      exact Nat.mul_le_mul_right _ this
    omega
  unfold pstWN
  omega

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- The contracted capacities are at most `Σ c + 1`. -/
lemma capR_le {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) (X Y : Finset V) (d : D) :
    capR M c X Y d ≤ ∑ e, c e + 1 := by
  unfold capR
  have h1 : c d ≤ ∑ e, c e := single_le_sum (fun e _ => hc e) (mem_univ d)
  have h0 : 0 ≤ ∑ e, c e := sum_nonneg fun e _ => hc e
  split_ifs <;> omega

/-- **The isolating weight bound at a call** is at most `wzK m Z`. -/
lemma isoW_bound_le {m Z : ℕ} (hD : Fintype.card D = m) (hF : Fintype.card F ≤ m)
    (hV : Fintype.card V ≤ m) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d ∧ c d ≤ 2 * Z) (X Y : Finset V) :
    (isoW_bound D V F (capR M c X Y)).toNat ≤ wzK m Z := by
  have hc0 : ∀ d, 0 ≤ c d := fun d => (hc d).1
  have hS : ∑ e, c e ≤ 2 * Z * m := by
    have := sum_le_sum (s := univ) fun e (_ : e ∈ univ) => (hc e).2
    simp only [sum_const, card_univ, hD, nsmul_eq_mul] at this
    linarith
  have hS0 : 0 ≤ ∑ e, c e := sum_nonneg fun e _ => hc0 e
  have hR : ∑ e, capR M c X Y e ≤ m * (2 * Z * m + 1) := by
    have := sum_le_sum (s := univ) fun e (_ : e ∈ univ) => capR_le (M := M) hc0 X Y e
    simp only [sum_const, card_univ, hD, nsmul_eq_mul] at this
    have h2 : (m : ℤ) * (∑ e, c e + 1) ≤ m * (2 * Z * m + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hR0 : 0 ≤ ∑ e, capR M c X Y e := sum_nonneg fun e _ => capR_nonneg hc0 X Y e
  have hiso : isoR D V F ≤ ((m + 1) * m * ((4 * m + 6) * m) : ℤ) := by
    unfold isoR
    rw [hD]
    have hF' : (Fintype.card F : ℤ) ≤ m := by exact_mod_cast hF
    have hV' : (Fintype.card V : ℤ) ≤ m := by exact_mod_cast hV
    have a : ((Fintype.card F : ℤ) + 1) * m ≤ (m + 1) * m :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have b : (4 * (Fintype.card F : ℤ) + 6) * Fintype.card V ≤ (4 * m + 6) * m :=
      mul_le_mul (by linarith) hV' (by positivity) (by positivity)
    exact mul_le_mul a b (by positivity) (by positivity)
  have hiso0 : 0 ≤ isoR D V F := by unfold isoR; positivity
  have key : isoW_bound D V F (capR M c X Y) ≤ (wzK m Z : ℤ) := by
    unfold isoW_bound wzK
    rw [hD]
    push_cast
    have a : (2 * isoR D V F + 1) ≤ 2 * (((m : ℤ) + 1) * m * ((4 * m + 6) * m)) + 1 := by linarith
    have b : ((m : ℤ) + 4) * (2 * isoR D V F + 1) ≤
        ((m : ℤ) + 4) * (2 * (((m : ℤ) + 1) * m * ((4 * m + 6) * m)) + 1) :=
      mul_le_mul_of_nonneg_left a (by positivity)
    exact mul_le_mul b (by linarith) (by linarith) (by positivity)
  have : (isoW_bound D V F (capR M c X Y)).toNat ≤ (wzK m Z : ℤ).toNat := Int.toNat_le_toNat key
  simpa using this

/-- **The word bound of the s-t flow call is at most `wzQ m Z`** (with its base offsets). -/
theorem stWc_le_wzQ {m Z : ℕ} (hm : 1 ≤ m) (hD : Fintype.card D = m) (hF : Fintype.card F ≤ m)
    (hV : Fintype.card V ≤ m) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d ∧ c d ≤ 2 * Z) (X Y : Finset V) :
    stWc M c X Y m ≤ wzQ m Z ∧
      pstWN (101 * m + 45) (stHb M c X Y m) + 339 * m + 128 ≤ wzQ m Z := by
  have hK := isoW_bound_le (M := M) hD hF hV hc X Y
  have hH : stHb M c X Y m ≤ pstH (4 * m + 1) m m m (wzK m Z) := by
    unfold stHb pstH
    rw [hD]
    exact Nat.mul_le_mul_left 2 (pstVb_mono4 le_rfl le_rfl hF hV hK)
  have hW : pstWN (101 * m + 45) (stHb M c X Y m) ≤
      pstWN (101 * m + 45) (pstH (4 * m + 1) m m m (wzK m Z)) := by
    unfold pstWN pstM
    have := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hH) 1)
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hH) 1)
    omega
  have hS : (∑ d, c d).toNat ≤ 2 * Z * m := by
    have := sum_le_sum (s := univ) fun e (_ : e ∈ univ) => (hc e).2
    simp only [sum_const, card_univ, hD, nsmul_eq_mul] at this
    have h2 : (∑ d, c d) ≤ ((2 * Z * m : ℕ) : ℤ) := by push_cast; linarith
    omega
  have hP := pstWN_le_wz (Z := Z) hm
  unfold stWc
  constructor <;> omega

/-- **The base of the zero area for the s-t flow call**: `ib = wzQ m Z + 339 m + 128` meets the
bounds of `c2tP_exec` when `wzc m Z ≤ Wz`. -/
theorem wz_ib {m Z Wz : ℕ} (hm : 1 ≤ m) (hD : Fintype.card D = m) (hF : Fintype.card F ≤ m)
    (hV : Fintype.card V ≤ m) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d ∧ c d ≤ 2 * Z) (X Y : Finset V)
    (hWz : wzc m Z ≤ Wz) :
    stWc M c X Y m ≤ Wz ∧
      pstWN (101 * m + 45) (stHb M c X Y m) < wzQ m Z + 339 * m + 128 ∧
      339 * m + 128 ≤ wzQ m Z + 339 * m + 128 ∧
      wzQ m Z + 339 * m + 128 + pstWN (101 * m + 45) (stHb M c X Y m) ≤ Wz := by
  obtain ⟨h1, h2⟩ := stWc_le_wzQ (M := M) hm hD hF hV hc X Y
  unfold wzc at hWz
  refine ⟨by omega, by omega, by omega, by omega⟩

end NcStep

end BKMNW

end PlanarFlow
