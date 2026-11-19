module

public import NestedDissection.DetModRun
public import NestedDissection.Sparse

/-!
# Sparse elimination modulo a prime on the random-access machine

A machine program (`SparseMod.sparseMod`, on the machine of `WordRAM`) that performs the sparse
elimination of `NestedDissection/Sparse.lean` modulo a prime `p` for a **given** elimination
order and **given** neighbour lists, and prints the product of the diagonal of the eliminated
matrix. Nothing is computed about the order or the pattern: the order (as a rank array) and the
neighbour lists (for nested dissection, the later neighbours in the filled graph of the separator
tree) are part of the input. The program does not check them: the correctness theorem assumes the
input is well formed (`SparseMod.SEnc`).

## The input

`[n, p, m] ++ [rk 0, …, rk (n-1)] ++ [u₀, v₀, a₀, …, u_{m-1}, v_{m-1}, a_{m-1}] ++ L₀ ++ ⋯`
(up to `L_{n-1}`)

* `rk u` is the position of the vertex `u` in the elimination order;
* the entries `(u_t, v_t, a_t)` say `A (rk u_t) (rk v_t) = a_t mod p` for the matrix `A` in
  elimination order (all other entries `0`; later entries overwrite earlier ones,
  `SparseMod.emem`); `SparseMod.sMat` is this matrix;
* `L_k = [d_k, w₀, …, w_{d_k - 1}]` lists the `d_k` neighbours `w` of the pivot `k` that are
  updated in step `k` (they must be distinct and larger than `k`); `SparseMod.nbSet d k` is the
  set they form, `SparseMod.lpos d k` the position of `L_k`.

## The program

Step `k` (for `k = 0, …, n - 1`): compute `π = A k k ^ (p - 2)` (Fermat; `0` if `A k k = 0`), then
for each listed `i` the multiplier `l = A i k · π` and for each listed `j` the update
`A i j ← A i j - l · A k j`, all modulo `p`, in place. Finally print `∏ k, A k k mod p`.
This is exactly `SparseMod.setStage` (`SparseMod.setStage_eq_sparseStage`: it is
`NestedDissection.sparseStage` when the lists are the later neighbours in `H`), so the value
printed is the value of the counted algorithm `sparseCounted`.

Memory: the matrix row by row at `0 … n² - 1` (memory starts at zero, so only the listed entries
are written). Registers: those of `DetMod.Regs` (`r0 = 0`, `r1 = 1`, `r2 = n`, `r3 = p`,
`r4 = n²`, `r5 = 2`, `r12 = p - 1`, `r13 = p - 2`), `r30 = 3`, `r31 = n + 3`, `r32 = m`; `r6` the
pivot `k`, `r7` the position of `L_k`, `r24 = k n`, `r26`/`r27` the first and past-the-last
position of the list of `k`, `r14` the inverse of the pivot, `r15`/`r16` the positions of `i` and
`j`, `r25 = i n`, `r18 = p - l`; the power loop of `DetMod` uses `r19 … r22`.

## Main results

* `SparseMod.sparseMod_exec`, `SparseMod.sparseMod_runsWithin`: the program prints
  `[(SparseMod.sVal d).val]` within `SparseMod.cost d + 1` steps, where
  `cost d = 18 m + 8 n + ∑ₖ (12 d_k² + 13 d_k + powPot (p - 2) + 20) + 23`.
* `SparseMod.sVal_eq_sparseCounted`: with neighbour lists equal to the later neighbours in `H`,
  `sVal d` is the product of the diagonal of `(sparseCounted H (sMat d) n).val`.
* `SparseMod.cost_le_counted`: then
  `cost d ≤ 13 · (sparseCounted H (sMat d) n).cost.total + n (powPot (p - 2) + 28) + 18 m + 23`,
  and `SparseMod.sparseMod_runsWithin_counted`: the program prints the value of the counted
  algorithm within `13 · ops + n (12 ⌊log₂ p⌋ + 40) + 18 m + 24` steps (`ops` its counted field
  operations). The term `n log p` is the cost of the `n` inversions by Fermat's little theorem
  (one counted operation each); `m` is the number of listed entries.
* `SparseMod.emem_rk`: the matrix in elimination order is the listed matrix permuted by the
  ranks.
-/

@[expose] public section

namespace NestedDissection

namespace SparseMod

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset
open DetMod (inp dim prm mat Regs DEnc IPw powStep powStep_exec powPot)

/-! ### Elimination over given neighbour sets -/

section Abstract

variable {K : Type*} [CommRing K] [Inv K] {n : ℕ}

/-- One elimination step with pivot `k`, restricted to the positions `(i, j)` with `i, j ∈ T`. -/
def setStep (T : Finset (Fin n)) (k : Fin n) (M : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if i ∈ T ∧ j ∈ T then M i j - M i k * (M k k)⁻¹ * M k j else M i j

/-- The stages of the elimination with the sets `T k`. -/
def setStage (T : ℕ → Finset (Fin n)) (A : Matrix (Fin n) (Fin n) K) :
    ℕ → Matrix (Fin n) (Fin n) K
  | 0 => A
  | k + 1 => if h : k < n then setStep (T k) ⟨k, h⟩ (setStage T A k) else setStage T A k

/-- With the later neighbours in `H` as the sets, these are the stages of `sparseStage`. -/
theorem setStage_eq_sparseStage {K : Type*} [Field K] (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (T : ℕ → Finset (Fin n)) (hT : ∀ k (h : k < n), T k = laterNbrs Fin.val H ⟨k, h⟩)
    (A : Matrix (Fin n) (Fin n) K) (k : ℕ) : setStage T A k = sparseStage H A k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < n
    · simp only [setStage, sparseStage, hk, ↓reduceDIte, ih, hT k hk]; rfl
    · simp only [setStage, sparseStage, hk, ↓reduceDIte, ih]

end Abstract

/-! ### The input -/

/-- The number of listed entries. -/
def em (d : List ℕ) : ℕ := d.getD 2 0
/-- The rank (position in the elimination order) of the vertex `u`. -/
def rk (d : List ℕ) (u : ℕ) : ℕ := d.getD (3 + u) 0
/-- The entry `t`: row, column and value. -/
def eu (d : List ℕ) (t : ℕ) : ℕ := d.getD (3 + dim d + 3 * t) 0
def ev (d : List ℕ) (t : ℕ) : ℕ := d.getD (4 + dim d + 3 * t) 0
def ea (d : List ℕ) (t : ℕ) : ℕ := d.getD (5 + dim d + 3 * t) 0

/-- The position of the neighbour list of the pivot `k`. -/
def lpos (d : List ℕ) : ℕ → ℕ
  | 0 => 3 + dim d + 3 * em d
  | k + 1 => lpos d k + 1 + d.getD (lpos d k) 0

/-- The length of the neighbour list of `k`, and its `t`-th element. -/
def deg (d : List ℕ) (k : ℕ) : ℕ := d.getD (lpos d k) 0
def nb (d : List ℕ) (k t : ℕ) : ℕ := d.getD (lpos d k + 1 + t) 0

/-- The address of the entry `t` in the matrix in elimination order. -/
def addr (d : List ℕ) (t : ℕ) : ℕ := rk d (eu d t) * dim d + rk d (ev d t)

/-- The memory after storing the first `t` entries. -/
def emem (d : List ℕ) : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | t + 1 => upd (emem d t) (addr d t) (ea d t % prm d)

/-- The matrix of the input, in elimination order, modulo `p`. -/
def sMat (d : List ℕ) : Matrix (Fin (dim d)) (Fin (dim d)) (ZMod (prm d)) :=
  mat (dim d) (prm d) (emem d (em d))

/-- The listed neighbours of the pivot `k`. -/
def nbSet (d : List ℕ) (k : ℕ) : Finset (Fin (dim d)) :=
  univ.filter fun i => ∃ t < deg d k, nb d k t = i

/-- The value printed: the product of the diagonal after elimination. -/
def sVal (d : List ℕ) : ZMod (prm d) := ∏ k, setStage (nbSet d) (sMat d) (dim d) k k

/-- Well-formed inputs and words: a prime modulus, words large enough for products of residues,
for the addresses and for the input positions; entries inside the matrix, ranks below `n`; the
neighbour lists of `k` without repetition and with entries in `(k, n)`. -/
structure SEnc (d : List ℕ) (W : ℕ) : Prop where
  prime : (prm d).Prime
  word_le : ∀ i, d.getD i 0 ≤ W
  sq : prm d * prm d + prm d ≤ W
  dim_sq : dim d * dim d + 2 ≤ W
  size : lpos d (dim d) + 2 ≤ W
  ent_lt : ∀ t < em d, eu d t < dim d ∧ ev d t < dim d
  rk_lt : ∀ u < dim d, rk d u < dim d
  nb_lt : ∀ k < dim d, ∀ t < deg d k, k < nb d k t ∧ nb d k t < dim d
  nb_inj : ∀ k < dim d, ∀ t < deg d k, ∀ t' < deg d k, nb d k t = nb d k t' → t = t'

theorem SEnc.toDEnc {d : List ℕ} {W : ℕ} (he : SEnc d W) : DEnc d W :=
  ⟨he.prime, he.word_le, he.sq, he.dim_sq⟩

theorem lpos_succ (d : List ℕ) (k : ℕ) : lpos d (k + 1) = lpos d k + 1 + deg d k := rfl

theorem lpos_mono (d : List ℕ) {k k' : ℕ} (h : k ≤ k') : lpos d k ≤ lpos d k' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [lpos_succ]; omega

/-! ### The program -/

/-- Set up the constants and `r7 = 0`. -/
def setup : Stmt := block [.constN 1 1, .readIn 2 0, .readIn 3 1, .mulN 4 2 2, .constN 5 2,
  .subN 12 3 1, .subN 13 3 5, .constN 30 3, .readIn 32 5, .addN 31 2 30, .copyN 7 0]

/-- Store the entry `r7`. -/
def loadStep : Stmt := block [.mulN 8 7 30, .addN 8 8 31, .readIn 9 8, .addN 8 8 1, .readIn 10 8,
  .addN 8 8 1, .readIn 11 8, .addN 9 9 30, .readIn 9 9, .addN 10 10 30, .readIn 10 10,
  .mulN 9 9 2, .addN 9 9 10, .modN 11 11 3, .storeN 9 11, .addN 7 7 1]

/-- Start the step of the pivot `k = r6`: `r24 = k n`, the list bounds `r26`, `r27`, and the
pivot `r9`. -/
def pivHead : Stmt := block [.mulN 24 6 2, .readIn 28 7, .addN 26 7 1, .addN 27 26 28,
  .addN 10 24 6, .loadN 9 10]

/-- The inverse `r14` of the pivot `r9` modulo `p` (`0` for `0`), by Fermat. -/
def invert : Stmt :=
  .ifLtN 0 9 (.seq (block [.copyN 19 9, .copyN 20 13, .copyN 21 1])
    (.seq (.whileLtN 0 20 powStep) (.instr (.copyN 14 21)))) (.instr (.copyN 14 0))

/-- The update of the entry `(i, j)`, `j` at position `r16`: `A i j ← A i j + (p - l) A k j`. -/
def colUpd : Stmt := block [.readIn 33 16, .addN 10 25 33, .loadN 9 10, .addN 23 24 33,
  .loadN 22 23, .mulN 22 22 18, .addN 9 9 22, .modN 9 9 3, .storeN 10 9, .addN 16 16 1]

/-- The updates of row `i`, at position `r15`: the multiplier `l = A i k · r14`, then the
listed columns. -/
def rowUpd : Stmt :=
  .seq (block [.readIn 29 15, .mulN 25 29 2, .addN 10 25 6, .loadN 9 10, .mulN 17 9 14,
      .modN 17 17 3, .subN 18 3 17, .copyN 16 26])
    (.seq (.whileLtN 16 27 colUpd) (.instr (.addN 15 15 1)))

/-- The step of the pivot `k = r6`. -/
def pivStep : Stmt :=
  .seq pivHead (.seq invert (.seq (.instr (.copyN 15 26))
    (.seq (.whileLtN 15 27 rowUpd) (block [.copyN 7 27, .addN 6 6 1]))))

/-- Multiply the diagonal entry `r6` into `r11`. -/
def diagStep : Stmt := block [.mulN 10 6 2, .addN 10 10 6, .loadN 9 10, .mulN 11 11 9,
  .modN 11 11 3, .addN 6 6 1]

/-- **Sparse elimination modulo `p`.** -/
def sparseMod : Stmt :=
  .seq setup <| .seq (.whileLtN 7 32 loadStep) <|
  .seq (block [.copyN 6 0, .mulN 7 32 30, .addN 7 7 31]) <| .seq (.whileLtN 6 2 pivStep) <|
  .seq (block [.copyN 6 0, .constN 11 1]) <| .seq (.whileLtN 6 2 diagStep) (.instr (.outN 11))

/-! ### The constant registers -/

/-- The constant registers. -/
def SRegs (d : List ℕ) (c : Config) : Prop :=
  Regs d c ∧ c.nreg 30 = 3 ∧ c.nreg 31 = dim d + 3 ∧ c.nreg 32 = em d

theorem sregs_of {d : List ℕ} {c c' : Config} (hR : SRegs d c)
    (h : ∀ x, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 12 ∨ x = 13 ∨ x = 30 ∨
      x = 31 ∨ x = 32 → c'.nreg x = c.nreg x) : SRegs d c' := by
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h12, h13⟩, h30, h31, h32⟩ := hR
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> rw [h _ (by omega)] <;> assumption

/-! ### The update of one entry -/

/-- The state of the column loop in row `i` with multiplier `l`, from `c₁`. -/
structure ICol (d : List ℕ) (W : ℕ) (k i l : ℕ) (c₁ c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ x, x ≠ 9 → x ≠ 10 → x ≠ 16 → x ≠ 22 → x ≠ 23 → x ≠ 33 → c.nreg x = c₁.nreg x
  r16_ge : lpos d k + 1 ≤ c.nreg 16
  r16_le : c.nreg 16 ≤ lpos d (k + 1)
  lt : ∀ a, c.nmem a < prm d
  new : ∀ t < c.nreg 16 - (lpos d k + 1), c.nmem (i * dim d + nb d k t) =
    (c₁.nmem (i * dim d + nb d k t) + (prm d - l) * c₁.nmem (k * dim d + nb d k t)) % prm d
  oth : ∀ a, (∀ t < c.nreg 16 - (lpos d k + 1), a ≠ i * dim d + nb d k t) →
    c.nmem a = c₁.nmem a
  out : c.output = c₁.output

section col
variable {d : List ℕ} {W : ℕ}

theorem colUpd_exec (he : SEnc d W) {k i l : ℕ} {c₁ : Config} (hR : SRegs d c₁)
    (hk : k < dim d) (hi : i < dim d) (hik : i ≠ k)
    (h24 : c₁.nreg 24 = k * dim d) (h25 : c₁.nreg 25 = i * dim d)
    (h18 : c₁.nreg 18 = prm d - l) (h27 : c₁.nreg 27 = lpos d (k + 1))
    (c : Config) (hI : ICol d W k i l c₁ c) (hlt : c.nreg 16 < c.nreg 27) :
    ∃ c' k', Exec (inp d) W colUpd c c' k' ∧ ICol d W k i l c₁ c' ∧
      (lpos d (k + 1) - c'.nreg 16) * 12 + k' + 2 ≤ (lpos d (k + 1) - c.nreg 16) * 12 := by
  have hc := hI.wb
  have hW := he.dim_sq; have hWp := he.sq; have hWs := he.size
  have hp2 := he.prime.two_le
  have hpos := lpos_mono d (show k + 1 ≤ dim d by omega)
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h12, h13⟩, h30, h31, h32⟩ := sregs_of hR fun x hx =>
    hI.regs x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have e24 : c.nreg 24 = k * dim d := by
    rw [hI.regs 24 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h24]
  have e25 : c.nreg 25 = i * dim d := by
    rw [hI.regs 25 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h25]
  have e18 : c.nreg 18 = prm d - l := by
    rw [hI.regs 18 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h18]
  have e27 : c.nreg 27 = lpos d (k + 1) := by
    rw [hI.regs 27 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h27]
  rw [e27] at hlt
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hI.r16_ge
  have hqD : q < deg d k := by rw [lpos_succ] at hlt; omega
  have hsub : c.nreg 16 - (lpos d k + 1) = q := by omega
  obtain ⟨hkj, hjn⟩ := he.nb_lt k hk q hqD
  have hjv : (inp d).data.getD (c.nreg 16) 0 = nb d k q := by rw [hq]; rfl
  have hii := DetMod.idx_lt hi hjn
  have hkk := DetMod.idx_lt hk hjn
  have hne : ∀ j j', j < dim d → j' < dim d → k * dim d + j ≠ i * dim d + j' := by
    intro j j' h1 h2 e; exact hik (DetMod.idx_inj h2 h1 e.symm).1
  have hmi : c.nmem (i * dim d + nb d k q) = c₁.nmem (i * dim d + nb d k q) := by
    refine hI.oth _ fun t ht e => ?_
    rw [hsub] at ht
    have := he.nb_inj k hk q hqD t (by omega)
      (DetMod.idx_inj hjn (he.nb_lt k hk t (by omega)).2 e).2
    omega
  have hmk : c.nmem (k * dim d + nb d k q) = c₁.nmem (k * dim d + nb d k q) :=
    hI.oth _ fun t ht => hne _ _ hjn (he.nb_lt k hk t (by omega)).2
  have ha := hI.lt (i * dim d + nb d k q); have hb := hI.lt (k * dim d + nb d k q)
  have hprod : c.nmem (k * dim d + nb d k q) * (prm d - l) ≤ prm d * prm d := by
    have := Nat.mul_le_mul hb.le (Nat.sub_le (prm d) l); omega
  unfold colUpd
  exec_block
  · exact he.word_le _
  · config_simp; rw [e25, hjv]; omega
  · config_simp; rw [e24, hjv]; omega
  · config_simp; rw [e18, e24, hjv]; omega
  · config_simp; rw [hjv, e25, e18, e24]; omega
  · config_simp; rw [h1]; omega
  simp only [hjv] at *
  refine ⟨⟨‹_›, fun x a b e f g h => ?_, by config_simp; rw [h1]; omega,
    by config_simp; rw [h1]; omega, fun a => ?_, fun t ht => ?_, fun a ha' => ?_,
    by config_simp; exact hI.out⟩, ?_⟩
  · config_simp; simp only [upd_apply, a, b, e, f, g, h, ↓reduceIte]
    exact hI.regs x a b e f g h
  · config_simp
    by_cases hA : a = c.nreg 25 + nb d k q
    · rw [hA, upd_same, h3]; exact Nat.mod_lt _ (by omega)
    · rw [upd_other _ _ _ hA]; exact hI.lt a
  · config_simp
    config_simp at ht
    rw [h1, show c.nreg 16 + 1 - (lpos d k + 1) = q + 1 by omega] at ht
    rw [e25, e24, e18, h3]
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · rw [upd_other _ _ _ ?_]
      · exact hI.new t (by omega)
      · intro e
        have := he.nb_inj k hk q hqD t (by omega)
          (DetMod.idx_inj hjn (he.nb_lt k hk t (by omega)).2 e.symm).2
        omega
    · rw [upd_same, hmi, hmk, Nat.mul_comm (c₁.nmem _)]
  · config_simp
    config_simp at ha'
    rw [h1, show c.nreg 16 + 1 - (lpos d k + 1) = q + 1 by omega] at ha'
    rw [e25, upd_other _ _ _ (ha' q (by omega))]
    exact hI.oth a fun t ht => ha' t (by omega)
  · config_simp; rw [h1]; omega

end col

/-! ### The updates of one row -/

/-- The value `t` is among the first `r` listed neighbours of `k`. -/
def InS (d : List ℕ) (k r x : ℕ) : Prop := ∃ t < r, nb d k t = x

instance (d : List ℕ) (k r x : ℕ) : Decidable (InS d k r x) := by unfold InS; infer_instance

theorem inS_succ {d : List ℕ} {k r x : ℕ} : InS d k (r + 1) x ↔ InS d k r x ∨ nb d k r = x := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · exact Or.inl ⟨t, ht, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨t, ht, rfl⟩ | rfl)
    · exact ⟨t, by omega, rfl⟩
    · exact ⟨r, by omega, rfl⟩

theorem not_inS_self {d : List ℕ} {W k r : ℕ} (he : SEnc d W) (hk : k < dim d)
    (hr : r ≤ deg d k) : ¬ InS d k r k := by
  rintro ⟨t, ht, e⟩
  have := (he.nb_lt k hk t (by omega)).1; omega

theorem not_inS_nb {d : List ℕ} {W k r : ℕ} (he : SEnc d W) (hk : k < dim d)
    (hr : r < deg d k) : ¬ InS d k r (nb d k r) := by
  rintro ⟨t, ht, e⟩
  have := he.nb_inj k hk t (by omega) r hr e; omega

/-- The updated entry `(i, j)` of the step of the pivot `k`, from the memory `m` and the inverse
`w` of the pivot. -/
def upv (d : List ℕ) (m : ℕ → ℕ) (w k i j : ℕ) : ZMod (prm d) :=
  (m (i * dim d + j) : ZMod (prm d)) -
    (m (i * dim d + k) : ZMod (prm d)) * (w : ZMod (prm d)) * (m (k * dim d + j) : ZMod (prm d))

/-- The state of the row loop of the pivot `k`, from `c₀`. -/
structure IRow (d : List ℕ) (W : ℕ) (k : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ x, x ≠ 9 → x ≠ 10 → x ≠ 15 → x ≠ 16 → x ≠ 17 → x ≠ 18 → x ≠ 22 → x ≠ 23 → x ≠ 25 →
    x ≠ 29 → x ≠ 33 → c.nreg x = c₀.nreg x
  r15_ge : lpos d k + 1 ≤ c.nreg 15
  r15_le : c.nreg 15 ≤ lpos d (k + 1)
  lt : ∀ a, c.nmem a < prm d
  ent : ∀ i < dim d, ∀ j < dim d, (c.nmem (i * dim d + j) : ZMod (prm d)) =
    if InS d k (c.nreg 15 - (lpos d k + 1)) i ∧ InS d k (deg d k) j then
      upv d c₀.nmem (c₀.nreg 14) k i j
    else (c₀.nmem (i * dim d + j) : ZMod (prm d))
  out : c.output = c₀.output

section row
variable {d : List ℕ} {W : ℕ}

theorem rowUpd_exec (he : SEnc d W) {k : ℕ} {c₀ : Config} (hR : SRegs d c₀) (hk : k < dim d)
    (h6 : c₀.nreg 6 = k) (h24 : c₀.nreg 24 = k * dim d) (h26 : c₀.nreg 26 = lpos d k + 1)
    (h27 : c₀.nreg 27 = lpos d (k + 1)) (h14 : c₀.nreg 14 < prm d)
    (c : Config) (hI : IRow d W k c₀ c) (hlt : c.nreg 15 < c.nreg 27) :
    ∃ c' k', Exec (inp d) W rowUpd c c' k' ∧ IRow d W k c₀ c' ∧
      (lpos d (k + 1) - c'.nreg 15) * (12 * deg d k + 13) + k' + 2 ≤
        (lpos d (k + 1) - c.nreg 15) * (12 * deg d k + 13) := by
  have hc := hI.wb
  have hW := he.dim_sq; have hWp := he.sq; have hWs := he.size
  have hp2 := he.prime.two_le
  have hpos := lpos_mono d (show k + 1 ≤ dim d by omega)
  have hfr : ∀ x, x ≠ 9 → x ≠ 10 → x ≠ 15 → x ≠ 16 → x ≠ 17 → x ≠ 18 → x ≠ 22 → x ≠ 23 →
      x ≠ 25 → x ≠ 29 → x ≠ 33 → c.nreg x = c₀.nreg x := hI.regs
  have hR' : SRegs d c := sregs_of hR fun x hx => by
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hfr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h12, h13⟩, h30, h31, h32⟩ := hR'
  have e6 : c.nreg 6 = k := by
    rw [hfr 6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), h6]
  have e14 : c.nreg 14 = c₀.nreg 14 := hfr 14 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have e24 : c.nreg 24 = k * dim d := by
    rw [hfr 24 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), h24]
  have e26 : c.nreg 26 = lpos d k + 1 := by
    rw [hfr 26 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), h26]
  have e27 : c.nreg 27 = lpos d (k + 1) := by
    rw [hfr 27 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), h27]
  rw [e27] at hlt
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hI.r15_ge
  have hrD : r < deg d k := by rw [lpos_succ] at hlt; omega
  have hsub : c.nreg 15 - (lpos d k + 1) = r := by omega
  obtain ⟨hki, hin⟩ := he.nb_lt k hk r hrD
  generalize hi_def : nb d k r = i at hki hin
  have hiv : (inp d).data.getD (c.nreg 15) 0 = i := by rw [hr, ← hi_def]; rfl
  have hik := DetMod.idx_lt hin hk
  have hmik : c.nmem (i * dim d + k) < prm d := hI.lt _
  have hprod : c.nmem (i * dim d + k) * c₀.nreg 14 ≤ W :=
    (Nat.mul_le_mul hmik.le h14.le).trans (by omega)
  generalize hl_def : c.nmem (i * dim d + k) * c₀.nreg 14 % prm d = l
  have hllt : l < prm d := by rw [← hl_def]; exact Nat.mod_lt _ (by omega)
  have e₁ : ∃ c₁ k₁, Exec (inp d) W (block [.readIn 29 15, .mulN 25 29 2, .addN 10 25 6,
      .loadN 9 10, .mulN 17 9 14, .modN 17 17 3, .subN 18 3 17, .copyN 16 26]) c c₁ k₁ ∧
      WordsBounded W c₁ ∧ k₁ = 8 ∧ c₁.nreg 25 = i * dim d ∧ c₁.nreg 18 = prm d - l ∧
      c₁.nreg 16 = lpos d k + 1 ∧
      (∀ x, x ≠ 9 → x ≠ 10 → x ≠ 16 → x ≠ 17 → x ≠ 18 → x ≠ 25 → x ≠ 29 →
        c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧ c₁.output = c.output := by
    exec_block
    · exact he.word_le _
    · config_simp; rw [hiv, h2]; exact (Nat.mul_le_mul_right _ hin.le).trans (by omega)
    · config_simp; rw [hiv, h2, e6]; omega
    · config_simp; rw [hiv, h2, e6, e14]; exact hprod
    refine ⟨‹_›, rfl, by config_simp; rw [hiv, h2], ?_, by config_simp; exact e26,
      fun x a b e f g h l => by config_simp; simp only [upd_apply, a, b, e, f, g, h, l, ↓reduceIte],
      rfl, rfl⟩
    config_simp; rw [h3, h2, e6, e14, hiv, hl_def]
  obtain ⟨c₁, k₁, e₁, hw₁, rfl, h25₁, h18₁, h16₁, hr₁, hm₁, ho₁⟩ := e₁
  have hfr₁ : ∀ x, x ≠ 9 → x ≠ 10 → x ≠ 15 → x ≠ 16 → x ≠ 17 → x ≠ 18 → x ≠ 22 → x ≠ 23 →
      x ≠ 25 → x ≠ 29 → x ≠ 33 → c₁.nreg x = c₀.nreg x := fun x a b e f g h l m n o q => by
    rw [hr₁ x a b f g h n o]; exact hfr x a b e f g h l m n o q
  have hR₁ : SRegs d c₁ := sregs_of hR fun x hx => by
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hfr₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
  have g24 : c₁.nreg 24 = k * dim d := by
    rw [hfr₁ 24 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), h24]
  have g27 : c₁.nreg 27 = lpos d (k + 1) := by
    rw [hfr₁ 27 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), h27]
  have hIC : ICol d W k i l c₁ c₁ := ⟨hw₁, fun _ _ _ _ _ _ _ => rfl, by rw [h16₁],
    by rw [h16₁, lpos_succ]; omega, fun a => by rw [hm₁]; exact hI.lt a,
    fun t ht => by rw [h16₁] at ht; omega, fun _ _ => rfl, rfl⟩
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 16)
    (b := 27) (body := colUpd) (ICol d W k i l c₁) (fun c => (lpos d (k + 1) - c.nreg 16) * 12)
    (fun c h => h.wb) (fun c' hc' hlt' => colUpd_exec he hR₁ hk hin (by omega) g24 h25₁ h18₁ g27
      c' hc' hlt') hIC
  have g27₂ : c₂.nreg 27 = lpos d (k + 1) := by
    rw [hI₂.regs 27 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g27]
  have h16₂ : c₂.nreg 16 = lpos d (k + 1) := by have := hI₂.r16_le; rw [g27₂] at hn₂; omega
  have hD : c₂.nreg 16 - (lpos d k + 1) = deg d k := by rw [h16₂, lpos_succ]; omega
  have hfr₂ : ∀ x, x ≠ 9 → x ≠ 10 → x ≠ 15 → x ≠ 16 → x ≠ 17 → x ≠ 18 → x ≠ 22 → x ≠ 23 →
      x ≠ 25 → x ≠ 29 → x ≠ 33 → c₂.nreg x = c₀.nreg x := fun x a b e f g h l m n o q => by
    rw [hI₂.regs x a b f l m q]; exact hfr₁ x a b e f g h l m n o q
  have g15 : c₂.nreg 15 = c.nreg 15 := by
    rw [hI₂.regs 15 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      hr₁ 15 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have g1 : c₂.nreg 1 = 1 := by
    rw [hI₂.regs 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      hr₁ 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h1]
  have e₃ := Exec.addN (P := inp d) hI₂.wb 15 15 1 (by rw [g15, g1]; omega)
  -- the entries of the step start
  have hkS : ¬ InS d k (deg d k) k := not_inS_self he hk le_rfl
  have hc0 : ∀ i' < dim d, ∀ j < dim d, ¬ (InS d k r i' ∧ InS d k (deg d k) j) →
      (c.nmem (i' * dim d + j) : ZMod (prm d)) = c₀.nmem (i' * dim d + j) := by
    intro i' hi' j hj hn
    rw [hI.ent i' hi' j hj, hsub]; simp only [hn, ↓reduceIte]
  refine ⟨_, _, .seq e₁ (.seq e₂ e₃), ⟨e₃.wb_right, fun x a b e f g h l m n o q => ?_, ?_, ?_,
    hI₂.lt, fun i' hi' j hj => ?_, ?_⟩, ?_⟩
  · config_simp; rw [upd_other _ _ _ e]; exact hfr₂ x a b e f g h l m n o q
  · config_simp; rw [g15, g1]; omega
  · config_simp; rw [g15, g1]; omega
  · config_simp
    rw [g15, g1, show c.nreg 15 + 1 - (lpos d k + 1) = r + 1 by omega]
    by_cases hcase : i' = i ∧ InS d k (deg d k) j
    · obtain ⟨rfl, q, hq, rfl⟩ := hcase
      have hc : InS d k (r + 1) i' ∧ InS d k (deg d k) (nb d k q) :=
        ⟨inS_succ.2 (Or.inr hi_def), q, hq, rfl⟩
      simp only [hc, and_self, ↓reduceIte]
      rw [hI₂.new q (by rw [hD]; exact hq), DetMod.cast_combo hllt.le, hm₁,
        hc0 _ hin _ (he.nb_lt k hk q hq).2 fun h => not_inS_nb he hk hrD (hi_def ▸ h.1),
        hc0 _ hk _ (he.nb_lt k hk q hq).2 fun h => not_inS_self he hk hrD.le h.1,
        ← hl_def, DetMod.cast_mulmod, hc0 _ hin _ hk fun h => hkS h.2, upv]
    · have hoth : c₂.nmem (i' * dim d + j) = c.nmem (i' * dim d + j) := by
        rw [hI₂.oth _ fun t ht e => hcase ?_, hm₁]
        obtain ⟨e1, e2⟩ := DetMod.idx_inj hj (he.nb_lt k hk t (by omega)).2 e
        exact ⟨e1, t, by rw [hD] at ht; exact ht, e2.symm⟩
      rw [hoth, hI.ent i' hi' j hj, hsub]
      by_cases hj' : InS d k (deg d k) j
      · have hne : i' ≠ i := fun e => hcase ⟨e, hj'⟩
        have : InS d k (r + 1) i' ↔ InS d k r i' := by
          rw [inS_succ, hi_def]; exact ⟨fun h => h.resolve_right (Ne.symm hne), Or.inl⟩
        simp only [this]
      · simp only [hj', and_false, ↓reduceIte]
  · config_simp; rw [hI₂.out, ho₁]; exact hI.out
  · config_simp; rw [g15, g1]
    rw [h16₁, lpos_succ] at hk₂
    have e : (lpos d (k + 1) - c.nreg 15) * (12 * deg d k + 13) =
        (lpos d (k + 1) - (c.nreg 15 + 1)) * (12 * deg d k + 13) + (12 * deg d k + 13) := by
      rw [← Nat.add_one_mul]; congr 1; omega
    rw [e]
    have : lpos d k + 1 + deg d k - (lpos d k + 1) = deg d k := by omega
    rw [this] at hk₂
    omega

end row

/-! ### The inverse of the pivot -/

section inverse
variable {d : List ℕ} {W : ℕ}

theorem invert_exec (he : SEnc d W) (c : Config) (hw : WordsBounded W c) (hR : Regs d c)
    (h9 : c.nreg 9 < prm d) :
    ∃ c' k', Exec (inp d) W invert c c' k' ∧ WordsBounded W c' ∧
      (∀ x, x ≠ 14 → x ≠ 19 → x ≠ 20 → x ≠ 21 → x ≠ 22 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.output = c.output ∧ c'.nreg 14 < prm d ∧
      (c'.nreg 14 : ZMod (prm d)) = ((c.nreg 9 : ℕ) : ZMod (prm d))⁻¹ ∧
      k' ≤ powPot (prm d - 2) + 7 := by
  have : Fact (prm d).Prime := ⟨he.prime⟩
  have hp2 := he.prime.two_le
  have hD := he.toDEnc
  obtain ⟨h0, h1, h2, h3, h4, h5, h12, h13⟩ := hR
  by_cases hz : c.nreg 9 = 0
  · have e := Exec.copyN (P := inp d) hw 14 0
    refine ⟨_, _, .ifLtN_false (by rw [h0, hz]; omega) e, e.wb_right, fun x a _ _ _ _ => ?_, rfl,
      rfl, ?_, ?_, by omega⟩
    · config_simp; rw [upd_other _ _ _ a]
    · config_simp; rw [h0]; omega
    · config_simp; rw [h0, hz]; simp
  · have e₁ : ∃ c₁ k₁, Exec (inp d) W (block [.copyN 19 9, .copyN 20 13, .copyN 21 1]) c c₁ k₁ ∧
        IPw d W (c.nreg 9) c₁ c₁ ∧ k₁ = 3 ∧ c₁.nreg 20 = prm d - 2 ∧
        (∀ x, x ≠ 19 → x ≠ 20 → x ≠ 21 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
        c₁.output = c.output := by
      exec_block
      refine ⟨⟨‹_›, fun _ _ _ _ _ => rfl, rfl, rfl, by config_simp; exact h9,
        by config_simp; rw [h1]; omega, ?_⟩, rfl, by config_simp; exact h13,
        fun x a b e => by config_simp; simp only [upd_apply, a, b, e, ↓reduceIte], rfl, rfl⟩
      config_simp; rw [h1, h13]; simp
    obtain ⟨c₁, k₁, e₁, hP₁, rfl, h20₁, hr₁, hm₁, ho₁⟩ := e₁
    have hR₁ : Regs d c₁ := DetMod.regs_of_keepsR ⟨h0, h1, h2, h3, h4, h5, h12, h13⟩ fun x hx =>
      hr₁ x (by omega) (by omega) (by omega)
    obtain ⟨c₂, k₂, e₂, hP₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 0)
      (b := 20) (body := powStep) (IPw d W (c.nreg 9) c₁) (fun c => powPot (c.nreg 20))
      (fun c h => h.wb) (fun c' hc' hlt' => powStep_exec hD hR₁ c' hc' hlt') hP₁
    have hr₂ : ∀ x, x ≠ 19 → x ≠ 20 → x ≠ 21 → x ≠ 22 → c₂.nreg x = c.nreg x := fun x a b e f =>
      (hP₂.regs x a b e f).trans (hr₁ x a b e)
    have h20₂ : c₂.nreg 20 = 0 := by
      rw [hr₂ 0 (by omega) (by omega) (by omega) (by omega), h0] at hn₂; omega
    have hpiv : ((c.nreg 9 : ℕ) : ZMod (prm d)) ≠ 0 := fun h => hz (DetMod.zero_of_cast h9 h)
    have hinv : (c₂.nreg 21 : ZMod (prm d)) = ((c.nreg 9 : ℕ) : ZMod (prm d))⁻¹ := by
      have := hP₂.inv; rw [h20₂, pow_zero, mul_one] at this
      rw [this]; exact eq_inv_of_mul_eq_one_left (DetMod.fermat hpiv)
    have e₃ := Exec.copyN (P := inp d) hP₂.wb 14 21
    refine ⟨_, _, .ifLtN_true (by rw [h0]; omega) (.seq e₁ (.seq e₂ e₃)), e₃.wb_right,
      fun x a b e f g => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · config_simp; rw [upd_other _ _ _ a]; exact hr₂ x b e f g
    · config_simp; rw [hP₂.mem, hm₁]
    · config_simp; rw [hP₂.out, ho₁]
    · config_simp; exact hP₂.res_lt
    · config_simp; exact hinv
    · rw [h20₁] at hk₂; omega

end inverse

/-! ### One pivot -/

/-- The state between pivots. -/
structure IPv (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : SRegs d c
  k_le : c.nreg 6 ≤ dim d
  r7 : c.nreg 7 = lpos d (c.nreg 6)
  lt : ∀ a, c.nmem a < prm d
  mat : mat (dim d) (prm d) c.nmem = setStage (nbSet d) (sMat d) (c.nreg 6)
  out : c.output = []

/-- The step bound of the pivot `k`. -/
def pivCost (d : List ℕ) (k : ℕ) : ℕ :=
  12 * deg d k * deg d k + 13 * deg d k + powPot (prm d - 2) + 20

theorem mem_nbSet {d : List ℕ} {k : ℕ} {i : Fin (dim d)} : i ∈ nbSet d k ↔ InS d k (deg d k) i := by
  simp [nbSet, InS]

section pivot
variable {d : List ℕ} {W : ℕ}

theorem pivStep_exec (he : SEnc d W) (c : Config) (hI : IPv d W c) (hk : c.nreg 6 < dim d) :
    ∃ c' k', Exec (inp d) W pivStep c c' k' ∧ IPv d W c' ∧
      (∑ j ∈ Ico (c'.nreg 6) (dim d), pivCost d j) + k' + 2 ≤
        ∑ j ∈ Ico (c.nreg 6) (dim d), pivCost d j := by
  have hc := hI.wb
  have hW := he.dim_sq; have hWp := he.sq; have hWs := he.size
  have hp2 := he.prime.two_le
  have hR := hI.regs
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h12, h13⟩, h30, h31, h32⟩ := hR
  have hmat := hI.mat
  have h7 := hI.r7
  generalize hk_def : c.nreg 6 = k at hk hmat h7 ⊢
  have hpos := lpos_mono d (show k + 1 ≤ dim d by omega)
  have hkk := DetMod.idx_lt hk hk
  -- the head
  have e₁ : ∃ c₁ k₁, Exec (inp d) W pivHead c c₁ k₁ ∧ WordsBounded W c₁ ∧ k₁ = 6 ∧
      c₁.nreg 24 = k * dim d ∧ c₁.nreg 26 = lpos d k + 1 ∧ c₁.nreg 27 = lpos d (k + 1) ∧
      c₁.nreg 9 = c.nmem (k * dim d + k) ∧
      (∀ x, x ≠ 9 → x ≠ 10 → x ≠ 24 → x ≠ 26 → x ≠ 27 → x ≠ 28 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.output = c.output := by
    have hrd : (inp d).data.getD (c.nreg 7) 0 = deg d k := by rw [h7]; rfl
    unfold pivHead
    exec_block
    · rw [hk_def, h2]; exact (Nat.mul_le_mul_right _ hk.le).trans (by omega)
    · exact he.word_le _
    · config_simp; rw [h7, h1]; rw [lpos_succ] at hpos; omega
    · config_simp; rw [hrd, h7, h1]; rw [lpos_succ] at hpos; omega
    · config_simp; rw [hk_def, h2]; omega
    refine ⟨‹_›, rfl, by config_simp; rw [hk_def, h2], by config_simp; rw [h7, h1],
      by config_simp; rw [hrd, h7, h1, lpos_succ], by config_simp; rw [hk_def, h2],
      fun x a b e f g h => by config_simp; simp only [upd_apply, a, b, e, f, g, h, ↓reduceIte],
      rfl, rfl⟩
  obtain ⟨c₁, k₁, e₁, hw₁, rfl, h24₁, h26₁, h27₁, h9₁, hr₁, hm₁, ho₁⟩ := e₁
  have hR₁ : SRegs d c₁ := sregs_of hI.regs fun x hx => by
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hr₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- the inverse
  obtain ⟨c₂, k₂, e₂, hw₂, hr₂, hm₂, ho₂, h14₂, hinv₂, hk₂⟩ := invert_exec he c₁ hw₁ hR₁.1
    (by rw [h9₁]; exact hI.lt _)
  have hR₂ : SRegs d c₂ := sregs_of hR₁ fun x hx => by
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hr₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  -- the rows
  have e₃ := Exec.copyN (P := inp d) hw₂ 15 26
  have hfr₃ : ∀ x, x ≠ 9 → x ≠ 10 → x ≠ 14 → x ≠ 15 → x ≠ 19 → x ≠ 20 → x ≠ 21 → x ≠ 22 →
      x ≠ 24 → x ≠ 26 → x ≠ 27 → x ≠ 28 →
      ({ c₂ with nreg := upd c₂.nreg 15 (c₂.nreg 26) } : Config).nreg x = c.nreg x := by
    intro x a b e f g h l m n o q r
    config_simp; rw [upd_other _ _ _ f, hr₂ x e g h l m, hr₁ x a b n o q r]
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 15 (c₂.nreg 26) } with hc₃
  have hR₃ : SRegs d c₃ := sregs_of hI.regs fun x hx => by
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hfr₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g6 : c₃.nreg 6 = k := by
    rw [hfr₃ 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hk_def]
  have g26 : c₂.nreg 26 = lpos d k + 1 := by
    rw [hr₂ 26 (by decide) (by decide) (by decide) (by decide) (by decide), h26₁]
  have g24 : c₃.nreg 24 = k * dim d := by
    rw [hc₃]; config_simp; rw [hr₂ 24 (by decide) (by decide) (by decide) (by decide) (by decide),
      h24₁]
  have g26₃ : c₃.nreg 26 = lpos d k + 1 := by rw [hc₃]; config_simp; exact g26
  have g27₃ : c₃.nreg 27 = lpos d (k + 1) := by
    rw [hc₃]; config_simp; rw [hr₂ 27 (by decide) (by decide) (by decide) (by decide) (by decide),
      h27₁]
  have g14₃ : c₃.nreg 14 = c₂.nreg 14 := by rw [hc₃]; config_simp
  have g15₃ : c₃.nreg 15 = lpos d k + 1 := by rw [hc₃]; config_simp; exact g26
  have hm₃ : c₃.nmem = c.nmem := by rw [hc₃]; config_simp; rw [hm₂, hm₁]
  have hlt₃ : ∀ a, c₃.nmem a < prm d := fun a => by rw [hm₃]; exact hI.lt a
  have hIR : IRow d W k c₃ c₃ := ⟨e₃.wb_right, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl, by rw [g15₃],
    by rw [g15₃, lpos_succ]; omega, hlt₃, fun i _ j _ => by
      rw [g15₃, Nat.sub_self]
      have : ¬ InS d k 0 i := fun ⟨t, ht, _⟩ => Nat.not_lt_zero t ht
      simp only [this, false_and, ↓reduceIte], rfl⟩
  obtain ⟨c₄, k₄, e₄, hI₄, hn₄, hk₄⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 15)
    (b := 27) (body := rowUpd) (IRow d W k c₃) (fun c => (lpos d (k + 1) - c.nreg 15) *
      (12 * deg d k + 13)) (fun c h => h.wb)
    (fun c' hc' hlt' => rowUpd_exec he hR₃ hk g6 g24 g26₃ g27₃ (by rw [g14₃]; exact h14₂) c' hc'
      hlt') hIR
  have hfr₄ := hI₄.regs
  have g27₄ : c₄.nreg 27 = lpos d (k + 1) := by
    rw [hfr₄ 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), g27₃]
  have h15₄ : c₄.nreg 15 = lpos d (k + 1) := by have := hI₄.r15_le; rw [g27₄] at hn₄; omega
  have g6₄ : c₄.nreg 6 = k := by
    rw [hfr₄ 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), g6]
  have g1₄ : c₄.nreg 1 = 1 := by
    rw [hfr₄ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hR₃.1.2.1]
  -- the tail
  have e₅ : ∃ c₅ k₅, Exec (inp d) W (block [.copyN 7 27, .addN 6 6 1]) c₄ c₅ k₅ ∧
      WordsBounded W c₅ ∧ k₅ = 2 ∧ c₅.nreg 6 = k + 1 ∧ c₅.nreg 7 = lpos d (k + 1) ∧
      (∀ x, x ≠ 6 → x ≠ 7 → c₅.nreg x = c₄.nreg x) ∧ c₅.nmem = c₄.nmem ∧
      c₅.output = c₄.output := by
    have hw₄ := hI₄.wb
    exec_block
    · config_simp; rw [g6₄, g1₄]; omega
    refine ⟨‹_›, rfl, by config_simp; rw [g6₄, g1₄], by config_simp; exact g27₄,
      fun x a b => by config_simp; simp only [upd_apply, a, b, ↓reduceIte], rfl, rfl⟩
  obtain ⟨c₅, k₅, e₅, hw₅, rfl, h6₅, h7₅, hr₅, hm₅, ho₅⟩ := e₅
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ⟨hw₅, ?_, by rw [h6₅]; omega,
    by rw [h6₅, h7₅], fun a => by rw [hm₅]; exact hI₄.lt a, ?_, ?_⟩, ?_⟩
  · refine sregs_of hR₃ fun x hx => ?_
    rw [hr₅ x (by omega) (by omega)]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hfr₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [h6₅, setStage, dite_eq_left hk, ← hmat]
    ext i j
    rw [hm₅]
    change (c₄.nmem (i * dim d + j) : ZMod (prm d)) = _
    rw [hI₄.ent i i.2 j j.2, h15₄, lpos_succ, show lpos d k + 1 + deg d k - (lpos d k + 1) =
      deg d k by omega]
    simp only [setStep, Matrix.of_apply, mem_nbSet]
    split_ifs
    · rw [upv, g14₃, hinv₂, h9₁, hm₃]; rfl
    · rw [hm₃]; rfl
  · rw [ho₅, hI₄.out, hc₃, ho₂, ho₁]; exact hI.out
  · rw [h6₅, Finset.sum_eq_sum_Ico_succ_bot hk]
    rw [g15₃, lpos_succ, show lpos d k + 1 + deg d k - (lpos d k + 1) = deg d k by omega] at hk₄
    have : deg d k * (12 * deg d k + 13) = 12 * deg d k * deg d k + 13 * deg d k := by ring
    unfold pivCost
    omega

end pivot

/-! ### Storing the entries -/

theorem emem_lt {d : List ℕ} (hp : 0 < prm d) (t a : ℕ) : emem d t a < prm d := by
  induction t with
  | zero => exact hp
  | succ t ih =>
    simp only [emem]
    by_cases h : a = addr d t
    · rw [h, upd_same]; exact Nat.mod_lt _ hp
    · rw [upd_other _ _ _ h]; exact ih

/-- The state of the loop storing the entries. -/
structure ILd (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : SRegs d c
  r7 : c.nreg 7 ≤ em d
  mem : c.nmem = emem d (c.nreg 7)
  out : c.output = []

section load
variable {d : List ℕ} {W : ℕ}

theorem loadStep_exec (he : SEnc d W) (c : Config) (hI : ILd d W c) (hlt : c.nreg 7 < em d) :
    ∃ c' k', Exec (inp d) W loadStep c c' k' ∧ ILd d W c' ∧
      (em d - c'.nreg 7) * 18 + k' + 2 ≤ (em d - c.nreg 7) * 18 := by
  have hc := hI.wb
  have hW := he.dim_sq; have hWs := he.size
  have hp2 := he.prime.two_le
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h12, h13⟩, h30, h31, h32⟩ := hI.regs
  have hpos := lpos_mono d (Nat.zero_le (dim d))
  have h0pos : lpos d 0 = 3 + dim d + 3 * em d := rfl
  generalize ht : c.nreg 7 = t at hlt
  obtain ⟨hu, hv⟩ := he.ent_lt t hlt
  have hru := he.rk_lt _ hu; have hrv := he.rk_lt _ hv
  have eu' : (inp d).data.getD (c.nreg 7 * c.nreg 30 + c.nreg 31) 0 = eu d t := by
    rw [ht, h30, h31]; show d.getD _ 0 = d.getD _ 0; congr 1; omega
  have ev' : (inp d).data.getD (c.nreg 7 * c.nreg 30 + c.nreg 31 + c.nreg 1) 0 = ev d t := by
    rw [ht, h30, h31, h1]; show d.getD _ 0 = d.getD _ 0; congr 1; omega
  have ea' : (inp d).data.getD (c.nreg 7 * c.nreg 30 + c.nreg 31 + c.nreg 1 + c.nreg 1) 0 =
      ea d t := by
    rw [ht, h30, h31, h1]; show d.getD _ 0 = d.getD _ 0; congr 1; omega
  have ru' : (inp d).data.getD (eu d t + c.nreg 30) 0 = rk d (eu d t) := by
    rw [h30]; show d.getD _ 0 = d.getD _ 0; congr 1; omega
  have rv' : (inp d).data.getD (ev d t + c.nreg 30) 0 = rk d (ev d t) := by
    rw [h30]; show d.getD _ 0 = d.getD _ 0; congr 1; omega
  have haddr := DetMod.idx_lt hru hrv
  unfold loadStep
  exec_block
  · rw [ht, h30]; omega
  · config_simp; rw [ht, h30, h31]; omega
  · exact he.word_le _
  · config_simp; rw [ht, h30, h31, h1]; omega
  · exact he.word_le _
  · config_simp; rw [ht, h30, h31, h1]; omega
  · exact he.word_le _
  · config_simp; rw [eu', h30]; omega
  · exact he.word_le _
  · config_simp; rw [ev', h30]; omega
  · exact he.word_le _
  · config_simp; rw [eu', ru', h2]; exact (Nat.mul_le_mul_right _ hru.le).trans (by omega)
  · config_simp; rw [eu', ru', ev', rv', h2]; omega
  · config_simp; rw [ht, h1]; omega
  refine ⟨⟨‹_›, sregs_of hI.regs fun x hx => ?_, ?_, ?_, ?_⟩, ?_⟩
  · config_simp
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · config_simp; rw [ht, h1]; omega
  · config_simp; rw [eu', ru', ev', rv', ea', hI.mem, ht, h1, h2, h3]; rfl
  · config_simp; exact hI.out
  · config_simp; rw [ht, h1]; omega

end load

/-! ### The product of the diagonal -/

/-- The state of the loop multiplying the diagonal of the memory `m`. -/
structure IDg (d : List ℕ) (W : ℕ) (m : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : SRegs d c
  r6 : c.nreg 6 ≤ dim d
  r11 : c.nreg 11 < prm d
  acc : (c.nreg 11 : ZMod (prm d)) = DetMod.diag (dim d) (prm d) m (c.nreg 6)
  mem : c.nmem = m
  out : c.output = []

section diag
variable {d : List ℕ} {W : ℕ}

theorem diagStep_exec (he : SEnc d W) {m : ℕ → ℕ} (hm : ∀ a, m a < prm d) (c : Config)
    (hI : IDg d W m c) (hlt : c.nreg 6 < dim d) :
    ∃ c' k', Exec (inp d) W diagStep c c' k' ∧ IDg d W m c' ∧
      (dim d - c'.nreg 6) * 8 + k' + 2 ≤ (dim d - c.nreg 6) * 8 := by
  have hc := hI.wb
  have hW := he.dim_sq; have hWp := he.sq
  have hp2 := he.prime.two_le
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h12, h13⟩, h30, h31, h32⟩ := hI.regs
  have hkk := DetMod.idx_lt hlt hlt
  have hmk := hm (c.nreg 6 * dim d + c.nreg 6)
  have hacc := hI.r11
  unfold diagStep
  exec_block
  · rw [h2]; exact (Nat.mul_le_mul_right _ hlt.le).trans (by omega)
  · config_simp; rw [h2]; omega
  · config_simp; rw [h2, hI.mem]; exact (Nat.mul_le_mul hacc.le hmk.le).trans (by omega)
  · config_simp; rw [h1]; omega
  refine ⟨⟨‹_›, sregs_of hI.regs fun x hx => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · config_simp
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · config_simp; rw [h1]; omega
  · config_simp; rw [h3]; exact Nat.mod_lt _ (by omega)
  · config_simp; rw [h1, h2, h3, hI.mem, DetMod.cast_mulmod, hI.acc, DetMod.diag_succ]
  · config_simp; exact hI.mem
  · config_simp; exact hI.out
  · config_simp; rw [h1]; omega

end diag

/-! ### The whole program -/

/-- The step bound of the program. -/
def cost (d : List ℕ) : ℕ := 18 * em d + 8 * dim d + ∑ k ∈ range (dim d), pivCost d k + 23

section main
variable {d : List ℕ} {W : ℕ}

/-- **Sparse elimination modulo `p` on the machine.** -/
theorem sparseMod_exec (he : SEnc d W) :
    ∃ c' k, Exec (inp d) W sparseMod initConfig c' k ∧ c'.output = [(sVal d).val] ∧
      k ≤ cost d := by
  have hW := he.dim_sq; have hWp := he.sq; have hWs := he.size
  have hp2 := he.prime.two_le
  have hpos := lpos_mono d (Nat.zero_le (dim d))
  have h0pos : lpos d 0 = 3 + dim d + 3 * em d := rfl
  have hw0 : WordsBounded W initConfig := ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  -- set up
  have e₁ : ∃ c₁ k₁, Exec (inp d) W setup initConfig c₁ k₁ ∧ ILd d W c₁ ∧ c₁.nreg 7 = 0 ∧
      k₁ = 11 := by
    unfold setup
    exec_block
    · omega
    · exact he.word_le _
    · exact he.word_le _
    · exact (Nat.le_add_right _ 2).trans hW
    · omega
    · omega
    · exact he.word_le _
    · config_simp; show dim d + 3 ≤ W; omega
    refine ⟨⟨‹_›, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, rfl⟩
    all_goals config_simp
    all_goals try rfl
    exact Nat.zero_le _
  obtain ⟨c₁, k₁, e₁, hL₁, h7₁, rfl⟩ := e₁
  -- the entries
  obtain ⟨c₂, k₂, e₂, hL₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 7)
    (b := 32) (body := loadStep) (ILd d W) (fun c => (em d - c.nreg 7) * 18) (fun c h => h.wb)
    (fun c hc hlt => loadStep_exec he c hc (by rw [hc.regs.2.2.2] at hlt; exact hlt)) hL₁
  have h7₂ : c₂.nreg 7 = em d := by have := hL₂.r7; rw [hL₂.regs.2.2.2] at hn₂; omega
  -- the pivots
  have e₃ : ∃ c₃ k₃, Exec (inp d) W (block [.copyN 6 0, .mulN 7 32 30, .addN 7 7 31]) c₂ c₃ k₃ ∧
      IPv d W c₃ ∧ c₃.nreg 6 = 0 ∧ k₃ = 3 := by
    have hw₂ := hL₂.wb
    obtain ⟨⟨h0, h1, h2, h3, h4, h5, h12, h13⟩, h30, h31, h32⟩ := hL₂.regs
    exec_block
    · config_simp; rw [h32, h30]; omega
    · config_simp; rw [h32, h30, h31]; omega
    refine ⟨⟨‹_›, sregs_of hL₂.regs fun x hx => ?_, ?_, ?_, fun a => ?_, ?_, ?_⟩,
      by config_simp; exact h0, rfl⟩
    · config_simp
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · config_simp; rw [h0]; omega
    · config_simp; rw [h0, h32, h30, h31, h0pos]; omega
    · config_simp; rw [hL₂.mem]; exact emem_lt (by omega) _ a
    · config_simp; rw [h0, hL₂.mem, h7₂]; rfl
    · config_simp; exact hL₂.out
  obtain ⟨c₃, k₃, e₃, hP₃, h6₃, rfl⟩ := e₃
  obtain ⟨c₄, k₄, e₄, hP₄, hn₄, hk₄⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 6)
    (b := 2) (body := pivStep) (IPv d W)
    (fun c => ∑ j ∈ Ico (c.nreg 6) (dim d), pivCost d j) (fun c h => h.wb)
    (fun c hc hlt => pivStep_exec he c hc (by rw [hc.regs.1.2.2.1] at hlt; exact hlt)) hP₃
  have h6₄ : c₄.nreg 6 = dim d := by have := hP₄.k_le; rw [hP₄.regs.1.2.2.1] at hn₄; omega
  -- the diagonal
  have e₅ : ∃ c₅ k₅, Exec (inp d) W (block [.copyN 6 0, .constN 11 1]) c₄ c₅ k₅ ∧
      IDg d W c₄.nmem c₅ ∧ k₅ = 2 := by
    have hw₄ := hP₄.wb
    obtain ⟨⟨h0, h1, h2, h3, h4, h5, h12, h13⟩, h30, h31, h32⟩ := hP₄.regs
    exec_block
    · omega
    refine ⟨⟨‹_›, sregs_of hP₄.regs fun x hx => ?_, ?_, ?_, ?_, rfl, ?_⟩, rfl⟩
    · config_simp
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · config_simp; rw [h0]; omega
    · config_simp; omega
    · config_simp; rw [h0]; simp [DetMod.diag]
    · config_simp; exact hP₄.out
  obtain ⟨c₅, k₅, e₅, hD₅, rfl⟩ := e₅
  obtain ⟨c₆, k₆, e₆, hD₆, hn₆, hk₆⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 6)
    (b := 2) (body := diagStep) (IDg d W c₄.nmem) (fun c => (dim d - c.nreg 6) * 8)
    (fun c h => h.wb) (fun c hc hlt => diagStep_exec he hP₄.lt c hc
      (by rw [hc.regs.1.2.2.1] at hlt; exact hlt)) hD₅
  have h6₆ : c₆.nreg 6 = dim d := by have := hD₆.r6; rw [hD₆.regs.1.2.2.1] at hn₆; omega
  have e₇ := Exec.outN (P := inp d) hD₆.wb 11
  refine ⟨_, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), ?_, ?_⟩
  · rw [hD₆.out]
    have hval : ((c₆.nreg 11 : ℕ) : ZMod (prm d)) = sVal d := by
      have hm := hP₄.mat
      rw [h6₄] at hm
      rw [hD₆.acc, h6₆, DetMod.diag, ← Fin.prod_univ_eq_prod_range
        (fun i => (c₄.nmem (i * dim d + i) : ZMod (prm d))) (dim d), sVal, ← hm]
      rfl
    simp only [List.nil_append, List.cons.injEq, and_true]
    have : NeZero (prm d) := ⟨by omega⟩
    rw [← hval, ZMod.val_natCast_of_lt hD₆.r11]
  · unfold cost
    rw [h6₃] at hk₄
    rw [h7₁] at hk₂
    have : (dim d - c₅.nreg 6) * 8 ≤ dim d * 8 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    rw [Finset.range_eq_Ico]
    omega

/-- **Sparse elimination modulo a prime on the machine.**  On a well-formed input (`SEnc d W`)
the compiled program halts within `cost d + 1` steps and prints the product of the diagonal of
the eliminated matrix, `sVal d`. -/
theorem sparseMod_runsWithin (he : SEnc d W) :
    RunsWithin (compile sparseMod 0 ++ [Instr.halt]) (inp d) W (cost d + 1) [(sVal d).val] := by
  obtain ⟨c', k, e, hout, hk⟩ := sparseMod_exec he
  exact RunsWithin.mono_steps (runsWithin_of_exec_output e hout) (by omega)

end main

/-! ### The relation to the counted algorithm -/

section counted
variable {d : List ℕ} {W : ℕ}

open WordRAM.Algebraic

/-- The neighbour list of `k` has `deg d k` distinct elements. -/
theorem card_nbSet (he : SEnc d W) {k : ℕ} (hk : k < dim d) : (nbSet d k).card = deg d k := by
  rw [← Finset.card_range (deg d k)]
  symm
  refine Finset.card_bij (fun t ht => (⟨nb d k t, (he.nb_lt k hk t (mem_range.1 ht)).2⟩ :
    Fin (dim d))) (fun t ht => ?_) (fun t₁ h₁ t₂ h₂ e => ?_) (fun i hi => ?_)
  · rw [mem_nbSet]; exact ⟨t, mem_range.1 ht, rfl⟩
  · exact he.nb_inj k hk t₁ (mem_range.1 h₁) t₂ (mem_range.1 h₂) (congrArg Fin.val e)
  · obtain ⟨t, ht, e⟩ := mem_nbSet.1 hi
    exact ⟨t, mem_range.2 ht, Fin.ext e⟩

/-- With neighbour lists equal to the later neighbours in `H`, the value printed is the value of
the counted algorithm: the product of the diagonal of `sparseCounted H (sMat d) n`. -/
theorem sVal_eq_sparseCounted [Fact (prm d).Prime] (H : SimpleGraph (Fin (dim d)))
    [DecidableRel H.Adj] (hT : ∀ k (h : k < dim d), nbSet d k = laterNbrs Fin.val H ⟨k, h⟩) :
    sVal d = ∏ k, (sparseCounted H (sMat d) (dim d)).val k k := by
  have h := setStage_eq_sparseStage (K := ZMod (prm d)) H (nbSet d) hT (sMat d) (dim d)
  rw [sparseCounted_val']
  exact Finset.prod_congr rfl fun k _ => congrFun (congrFun h k) k

/-- The operation count of the counted algorithm, per pivot. -/
theorem sparseCounted_total (H : SimpleGraph (Fin (dim d))) [Fact (prm d).Prime]
    [DecidableRel H.Adj] (A : Matrix (Fin (dim d)) (Fin (dim d)) (ZMod (prm d))) :
    (sparseCounted H A (dim d)).cost.total = ∑ k : Fin (dim d),
      (1 + (laterNbrs Fin.val H k).card + 2 * (laterNbrs Fin.val H k).card ^ 2) := by
  rw [sparseCounted_cost, ← Fin.sum_univ_eq_sum_range, OpCount.total, OpCount.adds_sum,
    OpCount.muls_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [stepCost, dite_eq_left v.2, Fin.eta]
  ring

theorem powPot_le_log (p : ℕ) : powPot (p - 2) ≤ 12 * Nat.log 2 p + 12 := by
  unfold powPot
  split_ifs with h
  · omega
  · have := Nat.log_mono_right (b := 2) (Nat.sub_le p 2); omega

/-- **The step count in terms of the counted operations**:
`cost d ≤ 13 · ops + n (powPot (p - 2) + 20) + 8 n + 18 m + 23`, where `ops` is the number of
field operations of `sparseCounted H (sMat d) n` in the counted model. -/
theorem cost_le_counted (he : SEnc d W) [Fact (prm d).Prime] (H : SimpleGraph (Fin (dim d)))
    [DecidableRel H.Adj] (hT : ∀ k (h : k < dim d), nbSet d k = laterNbrs Fin.val H ⟨k, h⟩) :
    cost d ≤ 13 * (sparseCounted H (sMat d) (dim d)).cost.total +
      dim d * (powPot (prm d - 2) + 28) + 18 * em d + 23 := by
  rw [sparseCounted_total, cost, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  have key : ∀ k : Fin (dim d), pivCost d k ≤
      13 * (1 + (laterNbrs Fin.val H k).card + 2 * (laterNbrs Fin.val H k).card ^ 2) +
        (powPot (prm d - 2) + 20) := by
    intro k
    rw [← Fin.eta k k.2, ← hT k k.2, card_nbSet he k.2, pivCost]
    nlinarith
  have := Finset.sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin (dim d)))) => key k
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at this
  nlinarith

/-- **Sparse elimination modulo a prime on the machine, against the counted algorithm.**
With neighbour lists equal to the later neighbours in `H`, the program prints the product of
the diagonal of `(sparseCounted H (sMat d) n).val` (the value of the counted algorithm) within
`13 · ops + n (12 ⌊log₂ p⌋ + 40) + 18 m + 24` steps, `ops` the number of field operations
counted for `sparseCounted H (sMat d) n`, `m` the number of listed entries. -/
theorem sparseMod_runsWithin_counted (he : SEnc d W) [Fact (prm d).Prime]
    (H : SimpleGraph (Fin (dim d))) [DecidableRel H.Adj]
    (hT : ∀ k (h : k < dim d), nbSet d k = laterNbrs Fin.val H ⟨k, h⟩) :
    RunsWithin (compile sparseMod 0 ++ [Instr.halt]) (inp d) W
      (13 * (sparseCounted H (sMat d) (dim d)).cost.total +
        dim d * (12 * Nat.log 2 (prm d) + 40) + 18 * em d + 24)
      [(∏ k, (sparseCounted H (sMat d) (dim d)).val k k).val] := by
  rw [← sVal_eq_sparseCounted H hT]
  refine RunsWithin.mono_steps (sparseMod_runsWithin he) ?_
  have h1 := cost_le_counted he H hT
  have h2 : dim d * (powPot (prm d - 2) + 28) ≤ dim d * (12 * Nat.log 2 (prm d) + 40) :=
    Nat.mul_le_mul_left _ (by have := powPot_le_log (prm d); omega)
  omega

end counted

/-! ### Entries in the original labels -/

/-- The memory after storing the first `t` entries at their original positions
`u n + v` (without the ranks). -/
def rmem (d : List ℕ) : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | t + 1 => upd (rmem d t) (eu d t * dim d + ev d t) (ea d t % prm d)

/-- With injective ranks, the matrix in elimination order is the matrix of the listed entries
with rows and columns moved to their ranks. -/
theorem emem_rk {d : List ℕ} {W : ℕ} (he : SEnc d W)
    (hinj : ∀ u < dim d, ∀ v < dim d, rk d u = rk d v → u = v) {t : ℕ} (ht : t ≤ em d)
    {u v : ℕ} (hu : u < dim d) (hv : v < dim d) :
    emem d t (rk d u * dim d + rk d v) = rmem d t (u * dim d + v) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    obtain ⟨hu', hv'⟩ := he.ent_lt t (by omega)
    have key : rk d u * dim d + rk d v = addr d t ↔ u * dim d + v = eu d t * dim d + ev d t := by
      constructor
      · intro h
        obtain ⟨e1, e2⟩ := DetMod.idx_inj (he.rk_lt v hv) (he.rk_lt _ hv') h
        rw [hinj u hu _ hu' e1, hinj v hv _ hv' e2]
      · intro h
        obtain ⟨e1, e2⟩ := DetMod.idx_inj hv hv' h
        rw [addr, e1, e2]
    simp only [emem, rmem, upd_apply, key]
    split_ifs
    · rfl
    · exact ih (by omega)

end SparseMod

end NestedDissection
