module

public import NestedDissection.DetModChain

/-!
# The entries of a Gram matrix modulo a prime, on the machine

The input `[n, p, m, u₀, v₀, s₀, …]` is the output of `DetMod.signs` (the input of
`DetMod.build`): it lists `m` entries of a skew matrix `M`, `M u v = sgn s` and `M v u = - sgn s`
(`DetMod.Listed`). The program `GramMod.gram` prints a list of triples `(i, j, g)` with
`g ≡ (Mᵀ M) i j mod p`, `g < p`, covering every position where `Mᵀ M` is nonzero, at most
`6 m` triples in all, within `O(m)` steps (`GramMod.gram_runsWithin`), provided every vertex is
the end of at most three listed entries.

Each listed entry gives two *half-edges* `h = 2k` (`u → v`, value `sgn s`) and `h = 2k + 1`
(`v → u`, value `-sgn s`), with source `src`, target `dst` and residue `res`. Then
`Kh l w = ∑ {res h | src h = l, dst h = w}` is `M l w` (`GramMod.Kh_eq`), and the Gram entry is
`Gz i j = ∑_h [dst h = i] res h · Kh (src h) j = ∑_l Kh l i · Kh l j` (`GramMod.Gz_eq_sum`).

## The program

1. Store the half-edges at `7n + 3h` (source, target, residue).
2. Build the rows: row `l` has `cnt l ≤ 3` slots `(target, residue)` at `n + 3l + c` and
   `4n + 3l + c`; `cnt l` is stored at `l`.
3. For every half-edge `h` and every slot `c` of the row of `src h`: add
   `res h · val (src h) c` to the Gram cell `(dst h, nbr (src h) c)` at `7n + 6m + i n + j`.
4. For every half-edge `h` and slot `c` again, print `dst h`, `nbr (src h) c` and the Gram cell.
-/

@[expose] public section

namespace NestedDissection

namespace GramMod

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset
open DetMod (inp dim prm bm bu bv bs sres sgn Listed Simple)

/-! ### Half-edges and the Gram entries -/

/-- Source, target and residue of the half-edge `h`. -/
def src (d : List ℕ) (h : ℕ) : ℕ := if h % 2 = 0 then bu d (h / 2) else bv d (h / 2)
def dst (d : List ℕ) (h : ℕ) : ℕ := if h % 2 = 0 then bv d (h / 2) else bu d (h / 2)
def res (d : List ℕ) (h : ℕ) : ℕ :=
  if h % 2 = 0 then sres (prm d) (bs d (h / 2)) else (prm d - sres (prm d) (bs d (h / 2))) % prm d

/-- The number of the first `h` half-edges with source `l`. -/
def hcnt (d : List ℕ) (h l : ℕ) : ℕ := ((range h).filter fun h' => src d h' = l).card

/-- The entry `(l, w)` of the listed matrix, from the half-edges. -/
def Kh (d : List ℕ) (l w : ℕ) : ZMod (prm d) :=
  ∑ h ∈ range (2 * bm d), if src d h = l ∧ dst d h = w then (res d h : ZMod (prm d)) else 0

/-- The Gram entry `(i, j)`, from the half-edges. -/
def Gz (d : List ℕ) (i j : ℕ) : ZMod (prm d) :=
  ∑ h ∈ range (2 * bm d), if dst d h = i then (res d h : ZMod (prm d)) * Kh d (src d h) j else 0

/-- Well-formed inputs: a modulus `p ≥ 2`, words large enough for the products of residues, the
addresses and the input positions; entries inside the matrix and off its diagonal; every vertex
the source of at most three half-edges. -/
structure GEnc (d : List ℕ) (W : ℕ) : Prop where
  two_le : 2 ≤ prm d
  word_le : ∀ i, d.getD i 0 ≤ W
  sq : prm d * prm d + prm d ≤ W
  size : 7 * dim d + 6 * bm d + dim d * dim d + 3 * bm d + 8 ≤ W
  ent_lt : ∀ k < bm d, bu d k < dim d ∧ bv d k < dim d ∧ bu d k ≠ bv d k
  deg_le : ∀ l, hcnt d (2 * bm d) l ≤ 3

section math
variable {d : List ℕ} {W : ℕ}

theorem src_even (k : ℕ) : src d (2 * k) = bu d k := by simp [src]
theorem src_odd (k : ℕ) : src d (2 * k + 1) = bv d k := by
  simp [src, Nat.add_mod, show (2 * k + 1) / 2 = k by omega]
theorem dst_even (k : ℕ) : dst d (2 * k) = bv d k := by simp [dst]
theorem dst_odd (k : ℕ) : dst d (2 * k + 1) = bu d k := by
  simp [dst, Nat.add_mod, show (2 * k + 1) / 2 = k by omega]
theorem res_even (k : ℕ) : res d (2 * k) = sres (prm d) (bs d k) := by simp [res]
theorem res_odd (k : ℕ) : res d (2 * k + 1) = (prm d - sres (prm d) (bs d k)) % prm d := by
  simp [res, Nat.add_mod, show (2 * k + 1) / 2 = k by omega]

theorem src_dst_lt (he : GEnc d W) {h : ℕ} (hh : h < 2 * bm d) :
    src d h < dim d ∧ dst d h < dim d := by
  obtain ⟨h1, h2, -⟩ := he.ent_lt (h / 2) (by omega)
  unfold src dst; split_ifs <;> exact ⟨by assumption, by assumption⟩

theorem res_lt (he : GEnc d W) (h : ℕ) : res d h < prm d := by
  have := he.two_le
  unfold res sres; split_ifs <;> first | omega | exact Nat.mod_lt _ (by omega)

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ h ∈ range (2 * m), f h = ∑ k ∈ range m, (f (2 * k) + f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- The Gram entry is `∑_l Kh l i · Kh l j`. -/
theorem Gz_eq_sum (he : GEnc d W) (i j : ℕ) :
    Gz d i j = ∑ l ∈ range (dim d), Kh d l i * Kh d l j := by
  have key : ∀ l, Kh d l i * Kh d l j = ∑ h ∈ range (2 * bm d),
      if src d h = l ∧ dst d h = i then (res d h : ZMod (prm d)) * Kh d l j else 0 := by
    intro l
    rw [Kh, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> simp
  simp only [key]
  rw [Finset.sum_comm, Gz]
  refine Finset.sum_congr rfl fun h hh => ?_
  have hs := (src_dst_lt he (mem_range.1 hh)).1
  rw [Finset.sum_eq_single (src d h)]
  · by_cases hd : dst d h = i <;> simp [hd]
  · intro l _ hl
    have : ¬ (src d h = l ∧ dst d h = i) := fun e => hl e.1.symm
    simp only [this, ↓reduceIte]
  · intro hn; exact absurd (mem_range.2 hs) hn

/-- **The half-edges give the listed matrix.** -/
theorem Kh_eq (he : GEnc d W) {n : ℕ} {M : Matrix (Fin n) (Fin n) (ZMod (prm d))}
    (hs : Simple (bm d) (bu d) (bv d)) (hM : Listed (bm d) (bu d) (bv d) (bs d) M)
    (l w : Fin n) : Kh d l w = M l w := by
  have hp : 1 ≤ prm d := by have := he.two_le; omega
  rw [Kh, sum_range_two_mul]
  simp only [src_even, src_odd, dst_even, dst_odd, res_even, res_odd, DetMod.sres_neg_cast hp,
    DetMod.sres_cast hp]
  by_cases hf : ∃ k < bm d, bu d k = l ∧ bv d k = w
  · obtain ⟨k₀, hk₀, hu, hv⟩ := hf
    rw [Finset.sum_eq_single k₀, hM.fwd k₀ hk₀ l w hu.symm hv.symm]
    · have hlw : (w : ℕ) ≠ l := by rw [← hu, ← hv]; exact Ne.symm (hs.1 k₀ hk₀)
      simp [hu, hv, hlw]
    · intro k hk hne
      obtain ⟨h1, h2⟩ := hs.2 k (mem_range.1 hk) k₀ hk₀ hne
      have e1 : ¬ (bu d k = l ∧ bv d k = w) := fun h => h1 ⟨by omega, by omega⟩
      have e2 : ¬ (bv d k = l ∧ bu d k = w) := fun h => h2 ⟨by omega, by omega⟩
      simp [e1, e2]
    · intro h; exact absurd (mem_range.2 hk₀) h
  by_cases hb : ∃ k < bm d, bv d k = l ∧ bu d k = w
  · obtain ⟨k₀, hk₀, hv, hu⟩ := hb
    rw [Finset.sum_eq_single k₀, hM.bwd k₀ hk₀ l w hv.symm hu.symm]
    · have hlw : (w : ℕ) ≠ l := by rw [← hu, ← hv]; exact hs.1 k₀ hk₀
      simp [hu, hv, hlw]
    · intro k hk hne
      obtain ⟨h1, h2⟩ := hs.2 k (mem_range.1 hk) k₀ hk₀ hne
      have e1 : ¬ (bu d k = l ∧ bv d k = w) := fun h => h2 ⟨by omega, by omega⟩
      have e2 : ¬ (bv d k = l ∧ bu d k = w) := fun h => h1 ⟨by omega, by omega⟩
      simp [e1, e2]
    · intro h; exact absurd (mem_range.2 hk₀) h
  · push Not at hf hb
    rw [hM.zero l w fun k hk => ⟨fun h => hf k hk h.1.symm h.2.symm,
      fun h => hb k hk h.1.symm h.2.symm⟩]
    refine Finset.sum_eq_zero fun k hk => ?_
    have e1 : ¬ (bu d k = l ∧ bv d k = w) := fun h => hf k (mem_range.1 hk) h.1 h.2
    have e2 : ¬ (bv d k = l ∧ bu d k = w) := fun h => hb k (mem_range.1 hk) h.1 h.2
    simp [e1, e2]

/-- **The Gram entries are those of `Mᵀ M`.** -/
theorem Gz_eq_gram (he : GEnc d W) {n : ℕ} (hn : dim d = n)
    {M : Matrix (Fin n) (Fin n) (ZMod (prm d))} (hs : Simple (bm d) (bu d) (bv d))
    (hM : Listed (bm d) (bu d) (bv d) (bs d) M) (i j : Fin n) :
    Gz d i j = (M.transpose * M) i j := by
  rw [Gz_eq_sum he, Matrix.mul_apply, hn, ← Fin.sum_univ_eq_sum_range
    (fun l => Kh d l i * Kh d l j) n]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Kh_eq he hs hM, Kh_eq he hs hM, Matrix.transpose_apply]

end math

/-! ### The program -/

/-- Set up the constants: `r1 = 1`, `r2 = n`, `r3 = p`, `r4 = 3`, `r5 = 2m`, `r6 = 3n`,
`r7 = 7n`, `r8 = 7n + 6m`, `r9 = 6`, `r12 = p - 1`, `r30 = m`; `r10 = 0`. -/
def setup : Stmt := block [.constN 1 1, .readIn 2 0, .readIn 3 1, .constN 4 3, .constN 9 6,
  .constN 31 2, .readIn 30 31, .mulN 5 30 31, .mulN 6 2 4, .constN 32 7, .mulN 7 2 32,
  .mulN 8 30 9, .addN 8 8 7, .subN 12 3 1, .copyN 10 0]

/-- Store the two half-edges of the entry `k = r10` at `7n + 6k`. -/
def hedge : Stmt :=
  .seq (.seq (block [.mulN 11 10 4, .addN 11 11 4, .readIn 13 11, .addN 11 11 1, .readIn 14 11,
      .addN 11 11 1, .readIn 15 11, .copyN 16 1]) (.ifLtN 0 15 (.instr (.copyN 16 12)) .skip))
      (block [.subN 17 3 16, .modN 17 17 3, .mulN 18 10 9, .addN 18 18 7, .storeN 18 13,
        .addN 18 18 1, .storeN 18 14, .addN 18 18 1, .storeN 18 16, .addN 18 18 1,
        .storeN 18 14, .addN 18 18 1, .storeN 18 13, .addN 18 18 1, .storeN 18 17,
        .addN 10 10 1])

/-- Add the half-edge `h = r10` to the row of its source. -/
def slot : Stmt := block [.mulN 11 10 4, .addN 11 11 7, .loadN 13 11, .addN 11 11 1,
  .loadN 14 11, .addN 11 11 1, .loadN 16 11, .loadN 19 13, .mulN 20 13 4, .addN 20 20 2,
  .addN 20 20 19, .storeN 20 14, .addN 21 20 6, .storeN 21 16, .addN 19 19 1, .storeN 13 19,
  .addN 10 10 1]

/-- Read the half-edge `h = r10`: source `r13`, target `r14`, residue `r16`; the Gram row base
`r23 = 7n + 6m + n · dst h`, the row base `r24 = n + 3 src h`, the slot count `r25`. -/
def head : Stmt := block [.mulN 11 10 4, .addN 11 11 7, .loadN 13 11, .addN 11 11 1,
  .loadN 14 11, .addN 11 11 1, .loadN 16 11, .mulN 23 14 2, .addN 23 23 8, .mulN 24 13 4,
  .addN 24 24 2, .loadN 25 13, .copyN 26 0]

/-- Add the product of the residues of `h` and of the slot `c = r26` to the Gram cell. -/
def accum : Stmt := block [.addN 27 24 26, .loadN 28 27, .addN 27 27 6, .loadN 29 27,
  .addN 27 23 28, .loadN 33 27, .mulN 29 16 29, .addN 33 33 29, .modN 33 33 3, .storeN 27 33,
  .addN 26 26 1]

/-- Print the Gram cell of `h` and the slot `c = r26`. -/
def emit : Stmt := block [.addN 27 24 26, .loadN 28 27, .addN 27 23 28, .loadN 33 27,
  .outN 14, .outN 28, .outN 33, .addN 26 26 1]

/-- **The Gram entries.** -/
def gram : Stmt :=
  .seq setup <| .seq (.whileLtN 10 30 hedge) <| .seq (.instr (.copyN 10 0)) <|
  .seq (.whileLtN 10 5 slot) <| .seq (.instr (.copyN 10 0)) <|
  .seq (.whileLtN 10 5 (.seq head (.seq (.whileLtN 26 25 accum) (.instr (.addN 10 10 1))))) <|
  .seq (.instr (.copyN 10 0))
    (.whileLtN 10 5 (.seq head (.seq (.whileLtN 26 25 emit) (.instr (.addN 10 10 1)))))

/-- The constant registers. -/
def GRegs (d : List ℕ) (c : Config) : Prop :=
  c.nreg 0 = 0 ∧ c.nreg 1 = 1 ∧ c.nreg 2 = dim d ∧ c.nreg 3 = prm d ∧ c.nreg 4 = 3 ∧
    c.nreg 5 = 2 * bm d ∧ c.nreg 6 = 3 * dim d ∧ c.nreg 7 = 7 * dim d ∧
    c.nreg 8 = 7 * dim d + 6 * bm d ∧ c.nreg 9 = 6 ∧ c.nreg 12 = prm d - 1 ∧ c.nreg 30 = bm d

theorem gregs_of {d : List ℕ} {c c' : Config} (hR : GRegs d c)
    (h : ∀ x, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 ∨
      x = 12 ∨ x = 30 → c'.nreg x = c.nreg x) : GRegs d c' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h30⟩ := hR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h _ (by omega)] <;> assumption

/-- Registers that the program writes outside the constants. -/
theorem gregs_upd {d : List ℕ} {c : Config} (hR : GRegs d c) {r : ℕ} (v : ℕ)
    (hr : r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 4 ∧ r ≠ 5 ∧ r ≠ 6 ∧ r ≠ 7 ∧ r ≠ 8 ∧ r ≠ 9 ∧
      r ≠ 12 ∧ r ≠ 30) : GRegs d { c with nreg := upd c.nreg r v } :=
  gregs_of hR fun x hx => by
    show upd c.nreg r v x = c.nreg x
    rw [upd_other]; omega

/-! ### Storing the half-edges -/

/-- The state of the loop storing the half-edges. -/
structure IA1 (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : GRegs d c
  r10 : c.nreg 10 ≤ bm d
  hc : ∀ h < 2 * c.nreg 10, c.nmem (7 * dim d + 3 * h) = src d h ∧
    c.nmem (7 * dim d + 3 * h + 1) = dst d h ∧ c.nmem (7 * dim d + 3 * h + 2) = res d h
  zero : ∀ a, (a < 7 * dim d ∨ 7 * dim d + 6 * c.nreg 10 ≤ a) → c.nmem a = 0
  out : c.output = []

/-- Six consecutive stores. -/
theorem upd6_eq (f : ℕ → ℕ) (A x₀ x₁ x₂ x₃ x₄ x₅ q : ℕ) :
    upd (upd (upd (upd (upd (upd f A x₀) (A + 1) x₁) (A + 1 + 1) x₂) (A + 1 + 1 + 1) x₃)
      (A + 1 + 1 + 1 + 1) x₄) (A + 1 + 1 + 1 + 1 + 1) x₅ q =
    if q < A ∨ A + 6 ≤ q then f q else if q = A then x₀ else if q = A + 1 then x₁
      else if q = A + 2 then x₂ else if q = A + 3 then x₃ else if q = A + 4 then x₄ else x₅ := by
  simp only [upd_apply]
  split_ifs <;> first | rfl | omega

/-- The memory after storing the half-edges of entry `k`. -/
theorem hedge_mem {d : List ℕ} {f : ℕ → ℕ} {k : ℕ}
    (hc : ∀ h < 2 * k, f (7 * dim d + 3 * h) = src d h ∧ f (7 * dim d + 3 * h + 1) = dst d h ∧
      f (7 * dim d + 3 * h + 2) = res d h)
    (hz : ∀ a, (a < 7 * dim d ∨ 7 * dim d + 6 * k ≤ a) → f a = 0) :
    let g := upd (upd (upd (upd (upd (upd f (k * 6 + 7 * dim d) (bu d k))
      (k * 6 + 7 * dim d + 1) (bv d k)) (k * 6 + 7 * dim d + 1 + 1) (sres (prm d) (bs d k)))
      (k * 6 + 7 * dim d + 1 + 1 + 1) (bv d k)) (k * 6 + 7 * dim d + 1 + 1 + 1 + 1) (bu d k))
      (k * 6 + 7 * dim d + 1 + 1 + 1 + 1 + 1) ((prm d - sres (prm d) (bs d k)) % prm d)
    (∀ h < 2 * (k + 1), g (7 * dim d + 3 * h) = src d h ∧ g (7 * dim d + 3 * h + 1) = dst d h ∧
      g (7 * dim d + 3 * h + 2) = res d h) ∧
    (∀ a, (a < 7 * dim d ∨ 7 * dim d + 6 * (k + 1) ≤ a) → g a = 0) := by
  intro g
  have hg : ∀ q, g q = _ := fun q => upd6_eq f (k * 6 + 7 * dim d) _ _ _ _ _ _ q
  refine ⟨fun h hh => ?_, fun a ha => ?_⟩
  · rcases Nat.lt_or_ge h (2 * k) with h' | h'
    · obtain ⟨q1, q2, q3⟩ := hc h h'
      simp only [hg, show 7 * dim d + 3 * h < k * 6 + 7 * dim d by omega,
        show 7 * dim d + 3 * h + 1 < k * 6 + 7 * dim d by omega,
        show 7 * dim d + 3 * h + 2 < k * 6 + 7 * dim d by omega, true_or, ↓reduceIte]
      exact ⟨q1, q2, q3⟩
    · rcases (show h = 2 * k ∨ h = 2 * k + 1 by omega) with rfl | rfl
      · rw [src_even, dst_even, res_even, hg, hg, hg]
        refine ⟨?_, ?_, ?_⟩ <;> (split_ifs <;> first | rfl | omega)
      · rw [src_odd, dst_odd, res_odd, hg, hg, hg]
        refine ⟨?_, ?_, ?_⟩ <;> (split_ifs <;> first | rfl | omega)
  · rw [hg]
    split_ifs <;> first | exact hz a (by omega) | omega

section A1
variable {d : List ℕ} {W : ℕ}

theorem hedge_exec (he : GEnc d W) (c : Config) (hI : IA1 d W c) (hlt : c.nreg 10 < c.nreg 30) :
    ∃ c' k', Exec (inp d) W hedge c c' k' ∧ IA1 d W c' ∧
      (bm d - c'.nreg 10) * 30 + k' + 2 ≤ (bm d - c.nreg 10) * 30 := by
  have hc := hI.wb
  have hW := he.size; have hWp := he.sq; have hp2 := he.two_le
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h30⟩ := hI.regs
  rw [h30] at hlt
  generalize hk : c.nreg 10 = k at hlt
  have hu : (inp d).data.getD (c.nreg 10 * c.nreg 4 + c.nreg 4) 0 = bu d k := by
    rw [hk, h4]; show d.getD _ 0 = d.getD _ 0; congr 1; omega
  have hv : (inp d).data.getD (c.nreg 10 * c.nreg 4 + c.nreg 4 + c.nreg 1) 0 = bv d k := by
    rw [hk, h4, h1]; show d.getD _ 0 = d.getD _ 0; congr 1; omega
  have hs : (inp d).data.getD (c.nreg 10 * c.nreg 4 + c.nreg 4 + c.nreg 1 + c.nreg 1) 0 =
      bs d k := by
    rw [hk, h4, h1]; show d.getD _ 0 = d.getD _ 0; congr 1; omega
  obtain ⟨hun, hvn, -⟩ := he.ent_lt k hlt
  -- the residue
  have e₁ : ∃ c₁ k₁, Exec (inp d) W (.seq (block [.mulN 11 10 4, .addN 11 11 4, .readIn 13 11,
      .addN 11 11 1, .readIn 14 11, .addN 11 11 1, .readIn 15 11, .copyN 16 1])
      (.ifLtN 0 15 (.instr (.copyN 16 12)) .skip)) c c₁ k₁ ∧ WordsBounded W c₁ ∧ k₁ ≤ 10 ∧
      c₁.nreg 13 = bu d k ∧ c₁.nreg 14 = bv d k ∧ c₁.nreg 16 = sres (prm d) (bs d k) ∧
      (∀ x, x ≠ 11 → x ≠ 13 → x ≠ 14 → x ≠ 15 → x ≠ 16 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.output = c.output := by
    refine spec_seq ?_
    exec_block
    · rw [hk, h4]; omega
    · config_simp; rw [hk, h4]; omega
    · exact he.word_le _
    · config_simp; rw [hk, h4, h1]; omega
    · exact he.word_le _
    · config_simp; rw [hk, h4, h1]; omega
    · exact he.word_le _
    by_cases hs0 : bs d k = 0
    · refine spec_ifLtN_false (by config_simp; rw [hs, hs0, h0]; omega) ?_
      refine spec_skip ‹_› ⟨‹_›, by omega, by config_simp; exact hu, by config_simp; exact hv, ?_,
        fun x a b e f g => ?_, rfl, rfl⟩
      · config_simp; rw [h1, sres]; simp [hs0]
      · config_simp; simp only [upd_apply, a, b, e, f, g, ↓reduceIte]
    · refine spec_ifLtN_true (by config_simp; rw [hs, h0]; omega) ?_
      refine spec_instr (Exec.copyN ‹_› _ _) fun hw => ⟨hw, by omega, by config_simp; exact hu,
        by config_simp; exact hv, ?_, fun x a b e f g => ?_, rfl, rfl⟩
      · config_simp; rw [h12, sres]; simp [hs0]
      · config_simp; simp only [upd_apply, a, b, e, f, g, ↓reduceIte]
  obtain ⟨c₁, k₁, e₁, hw₁, hk₁, g13, g14, g16, hr₁, hm₁, ho₁⟩ := e₁
  have f1 : c₁.nreg 1 = 1 := by
    rw [hr₁ 1 (by omega) (by omega) (by omega) (by omega) (by omega), h1]
  have f3 : c₁.nreg 3 = prm d := by
    rw [hr₁ 3 (by omega) (by omega) (by omega) (by omega) (by omega), h3]
  have f7 : c₁.nreg 7 = 7 * dim d := by
    rw [hr₁ 7 (by omega) (by omega) (by omega) (by omega) (by omega), h7]
  have f9 : c₁.nreg 9 = 6 := by
    rw [hr₁ 9 (by omega) (by omega) (by omega) (by omega) (by omega), h9]
  have f10 : c₁.nreg 10 = k := by
    rw [hr₁ 10 (by omega) (by omega) (by omega) (by omega) (by omega), hk]
  have hsres : sres (prm d) (bs d k) ≤ prm d := by unfold sres; split_ifs <;> omega
  have e₂ : ∃ c₂ k₂, Exec (inp d) W (block [.subN 17 3 16, .modN 17 17 3, .mulN 18 10 9,
      .addN 18 18 7, .storeN 18 13, .addN 18 18 1, .storeN 18 14, .addN 18 18 1, .storeN 18 16,
      .addN 18 18 1, .storeN 18 14, .addN 18 18 1, .storeN 18 13, .addN 18 18 1, .storeN 18 17,
      .addN 10 10 1]) c₁ c₂ k₂ ∧ IA1 d W c₂ ∧ c₂.nreg 10 = k + 1 ∧ k₂ = 16 := by
    exec_block
    · config_simp; rw [f10, f9]; omega
    · config_simp; rw [f10, f9, f7]; omega
    · config_simp; rw [f10, f9, f7, f1]; omega
    · config_simp; rw [f10, f9, f7, f1]; omega
    · config_simp; rw [f10, f9, f7, f1]; omega
    · config_simp; rw [f10, f9, f7, f1]; omega
    · config_simp; rw [f10, f9, f7, f1]; omega
    · config_simp; rw [f10, f1]; omega
    refine ⟨⟨‹_›, gregs_of hI.regs fun x hx => ?_, ?_, fun h hh => ?_, fun a ha => ?_, ?_⟩, ?_,
      rfl⟩
    · config_simp
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp <;> exact hr₁ _ (by omega) (by omega) (by omega) (by omega) (by omega)
    · config_simp; rw [f10, f1]; omega
    · config_simp
      config_simp at hh
      rw [f10, f1] at hh
      rw [f10, f9, f7, f1, f3, g13, g14, g16, hm₁]
      exact (hedge_mem (fun h hh => hI.hc h (by rw [hk]; exact hh))
        (fun a ha => hI.zero a (by rw [hk]; exact ha))).1 h hh
    · config_simp
      config_simp at ha
      rw [f10, f1] at ha
      rw [f10, f9, f7, f1, f3, g13, g14, g16, hm₁]
      exact (hedge_mem (fun h hh => hI.hc h (by rw [hk]; exact hh))
        (fun a ha => hI.zero a (by rw [hk]; exact ha))).2 a ha
    · config_simp; rw [ho₁]; exact hI.out
    · config_simp; rw [f10, f1]
  obtain ⟨c₂, k₂, e₂, hI₂, h10, rfl⟩ := e₂
  refine ⟨c₂, _, .seq e₁ e₂, hI₂, ?_⟩
  rw [h10]
  have : (bm d - k) * 30 = (bm d - (k + 1)) * 30 + 30 := by
    rw [← Nat.add_one_mul]; congr 1; omega
  omega

end A1

/-! ### The rows -/

/-- The sum of the residues of the slots of row `l` with target `j`, in the memory `m`. -/
def Srow (d : List ℕ) (m : ℕ → ℕ) (l j : ℕ) : ZMod (prm d) :=
  ∑ c ∈ range (m l), if m (dim d + 3 * l + c) = j then
    (m (dim d + 3 * l + c + 3 * dim d) : ZMod (prm d)) else 0

/-- The memory after adding the first `h` half-edges to the rows. -/
structure RowsOK (d : List ℕ) (m : ℕ → ℕ) (h : ℕ) : Prop where
  hc : ∀ h' < 2 * bm d, m (7 * dim d + 3 * h') = src d h' ∧
    m (7 * dim d + 3 * h' + 1) = dst d h' ∧ m (7 * dim d + 3 * h' + 2) = res d h'
  zeroG : ∀ a, 7 * dim d + 6 * bm d ≤ a → m a = 0
  cnt : ∀ l < dim d, m l = hcnt d h l
  nb_lt : ∀ l < dim d, ∀ c < m l, m (dim d + 3 * l + c) < dim d
  val_lt : ∀ l < dim d, ∀ c < m l, m (dim d + 3 * l + c + 3 * dim d) < prm d
  sum : ∀ l < dim d, ∀ j, Srow d m l j =
    ∑ h' ∈ range h, if src d h' = l ∧ dst d h' = j then (res d h' : ZMod (prm d)) else 0

theorem hcnt_succ (d : List ℕ) (h l : ℕ) :
    hcnt d (h + 1) l = hcnt d h l + if src d h = l then 1 else 0 := by
  unfold hcnt
  rw [range_add_one, filter_insert]
  split_ifs with e
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem hcnt_mono (d : List ℕ) {h h' : ℕ} (hh : h ≤ h') (l : ℕ) : hcnt d h l ≤ hcnt d h' l :=
  card_le_card (filter_subset_filter _ (range_subset_range.2 hh))

theorem hcnt_le {d : List ℕ} {W : ℕ} (he : GEnc d W) {h : ℕ} (hh : h ≤ 2 * bm d) (l : ℕ) :
    hcnt d h l ≤ 3 :=
  (hcnt_mono d hh l).trans (he.deg_le l)

/-- One half-edge added to its row. -/
theorem RowsOK.step {d : List ℕ} {W : ℕ} (he : GEnc d W) {m : ℕ → ℕ} {h : ℕ}
    (hR : RowsOK d m h) (hh : h < 2 * bm d) :
    RowsOK d (upd (upd (upd m (dim d + 3 * src d h + m (src d h)) (dst d h))
      (dim d + 3 * src d h + m (src d h) + 3 * dim d) (res d h)) (src d h) (m (src d h) + 1))
      (h + 1) := by
  obtain ⟨hl₀, hw₀⟩ := src_dst_lt he hh
  have ha₀ := res_lt he h
  generalize hl : src d h = l₀ at hl₀
  have hc₀ : m l₀ = hcnt d h l₀ := hR.cnt l₀ hl₀
  have hc3 : hcnt d (h + 1) l₀ ≤ 3 := hcnt_le he (by omega) l₀
  rw [hcnt_succ, hl] at hc3
  simp only [↓reduceIte] at hc3
  have hcnt3 : ∀ l < dim d, m l ≤ 3 := fun l hl' => by
    rw [hR.cnt l hl']; exact (hcnt_mono d (Nat.le_succ h) l).trans (hcnt_le he (by omega) l)
  generalize hc : m l₀ = c₀ at hc₀
  rw [← hc₀] at hc3
  refine ⟨fun h' hh' => ?_, fun a ha => ?_, fun l hl' => ?_, fun l hl' c hc' => ?_,
    fun l hl' c hc' => ?_, fun l hl' j => ?_⟩
  · simp only [upd_apply]
    have := hR.hc h' hh'
    refine ⟨?_, ?_, ?_⟩ <;> (split_ifs <;> omega)
  · simp only [upd_apply]
    split_ifs <;> first | omega | exact hR.zeroG a ha
  · rw [hcnt_succ, hl, ← hR.cnt l hl']
    simp only [upd_apply]
    by_cases e : l₀ = l
    · subst e; simp only [↓reduceIte, hc]
    · have e' : ¬ l = l₀ := fun h => e h.symm
      simp only [e, e', ↓reduceIte, show l ≠ dim d + 3 * l₀ + c₀ + 3 * dim d by omega,
        show l ≠ dim d + 3 * l₀ + c₀ by omega, add_zero]
  · have h3 := hcnt3 l hl'
    by_cases e : l₀ = l
    · subst e
      simp only [upd_apply, ↓reduceIte] at hc' ⊢
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc' with hlt | rfl
      · simp only [show dim d + 3 * l₀ + c ≠ dim d + 3 * l₀ + c₀ + 3 * dim d by omega,
          show dim d + 3 * l₀ + c ≠ l₀ by omega, show dim d + 3 * l₀ + c ≠ dim d + 3 * l₀ + c₀ by
          omega, ↓reduceIte]
        exact hR.nb_lt l₀ hl' c (by omega)
      · simp only [show dim d + 3 * l₀ + c ≠ dim d + 3 * l₀ + c + 3 * dim d by omega,
          show dim d + 3 * l₀ + c ≠ l₀ by omega, ↓reduceIte]
        exact hw₀
    · have e' : ¬ l = l₀ := fun h => e h.symm
      simp only [upd_apply, e', ↓reduceIte, show l ≠ dim d + 3 * l₀ + c₀ + 3 * dim d by omega,
        show l ≠ dim d + 3 * l₀ + c₀ by omega] at hc'
      simp only [upd_apply, show dim d + 3 * l + c ≠ l₀ by omega,
        show dim d + 3 * l + c ≠ dim d + 3 * l₀ + c₀ + 3 * dim d by omega,
        show dim d + 3 * l + c ≠ dim d + 3 * l₀ + c₀ by omega, ↓reduceIte]
      exact hR.nb_lt l hl' c hc'
  · have h3 := hcnt3 l hl'
    by_cases e : l₀ = l
    · subst e
      simp only [upd_apply, ↓reduceIte] at hc' ⊢
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc' with hlt | rfl
      · simp only [show dim d + 3 * l₀ + c + 3 * dim d ≠ l₀ by omega,
          show dim d + 3 * l₀ + c + 3 * dim d ≠ dim d + 3 * l₀ + c₀ + 3 * dim d by omega,
          show dim d + 3 * l₀ + c + 3 * dim d ≠ dim d + 3 * l₀ + c₀ by omega, ↓reduceIte]
        exact hR.val_lt l₀ hl' c (by omega)
      · simp only [show dim d + 3 * l₀ + c + 3 * dim d ≠ l₀ by omega, ↓reduceIte]
        exact ha₀
    · have e' : ¬ l = l₀ := fun h => e h.symm
      simp only [upd_apply, e', ↓reduceIte, show l ≠ dim d + 3 * l₀ + c₀ + 3 * dim d by omega,
        show l ≠ dim d + 3 * l₀ + c₀ by omega] at hc'
      simp only [upd_apply, show dim d + 3 * l + c + 3 * dim d ≠ l₀ by omega,
        show dim d + 3 * l + c + 3 * dim d ≠ dim d + 3 * l₀ + c₀ + 3 * dim d by omega,
        show dim d + 3 * l + c + 3 * dim d ≠ dim d + 3 * l₀ + c₀ by omega, ↓reduceIte]
      exact hR.val_lt l hl' c hc'
  · rw [sum_range_succ, ← hR.sum l hl' j, hl, Srow, Srow]
    have h3 := hcnt3 l hl'
    by_cases e : l₀ = l
    · subst e
      have hg : upd (upd (upd m (dim d + 3 * l₀ + c₀) (dst d h))
          (dim d + 3 * l₀ + c₀ + 3 * dim d) (res d h)) l₀ (c₀ + 1) l₀ = c₀ + 1 := by
        simp only [upd_apply, ↓reduceIte]
      rw [hg, hc, sum_range_succ]
      congr 1
      · refine sum_congr rfl fun c hcm => ?_
        have := mem_range.1 hcm
        simp only [upd_apply, show dim d + 3 * l₀ + c ≠ l₀ by omega,
          show dim d + 3 * l₀ + c ≠ dim d + 3 * l₀ + c₀ + 3 * dim d by omega,
          show dim d + 3 * l₀ + c ≠ dim d + 3 * l₀ + c₀ by omega,
          show dim d + 3 * l₀ + c + 3 * dim d ≠ l₀ by omega,
          show dim d + 3 * l₀ + c + 3 * dim d ≠ dim d + 3 * l₀ + c₀ + 3 * dim d by omega,
          show dim d + 3 * l₀ + c + 3 * dim d ≠ dim d + 3 * l₀ + c₀ by omega, ↓reduceIte]
      · simp only [upd_apply, show dim d + 3 * l₀ + c₀ ≠ l₀ by omega,
          show dim d + 3 * l₀ + c₀ ≠ dim d + 3 * l₀ + c₀ + 3 * dim d by omega,
          show dim d + 3 * l₀ + c₀ + 3 * dim d ≠ l₀ by omega, ↓reduceIte, true_and]
    · have e' : ¬ l = l₀ := fun h => e h.symm
      have hne : ¬ (l₀ = l ∧ dst d h = j) := fun h' => e h'.1
      have hg : upd (upd (upd m (dim d + 3 * l₀ + c₀) (dst d h))
          (dim d + 3 * l₀ + c₀ + 3 * dim d) (res d h)) l₀ (c₀ + 1) l = m l := by
        simp only [upd_apply, e', ↓reduceIte, show l ≠ dim d + 3 * l₀ + c₀ + 3 * dim d by omega,
          show l ≠ dim d + 3 * l₀ + c₀ by omega]
      simp only [hne, ↓reduceIte, add_zero, hg]
      refine sum_congr rfl fun c hcm => ?_
      have := mem_range.1 hcm
      simp only [upd_apply, show dim d + 3 * l + c ≠ l₀ by omega,
        show dim d + 3 * l + c ≠ dim d + 3 * l₀ + c₀ + 3 * dim d by omega,
        show dim d + 3 * l + c ≠ dim d + 3 * l₀ + c₀ by omega,
        show dim d + 3 * l + c + 3 * dim d ≠ l₀ by omega,
        show dim d + 3 * l + c + 3 * dim d ≠ dim d + 3 * l₀ + c₀ + 3 * dim d by omega,
        show dim d + 3 * l + c + 3 * dim d ≠ dim d + 3 * l₀ + c₀ by omega, ↓reduceIte]

/-- The state of the loop building the rows. -/
structure IA2 (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : GRegs d c
  r10 : c.nreg 10 ≤ 2 * bm d
  rows : RowsOK d c.nmem (c.nreg 10)
  out : c.output = []

section A2
variable {d : List ℕ} {W : ℕ}

theorem slot_exec (he : GEnc d W) (c : Config) (hI : IA2 d W c) (hlt : c.nreg 10 < c.nreg 5) :
    ∃ c' k', Exec (inp d) W slot c c' k' ∧ IA2 d W c' ∧
      (2 * bm d - c'.nreg 10) * 19 + k' + 2 ≤ (2 * bm d - c.nreg 10) * 19 := by
  have hc := hI.wb
  have hW := he.size; have hWp := he.sq; have hp2 := he.two_le
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h30⟩ := hI.regs
  rw [h5] at hlt
  generalize hk : c.nreg 10 = h at hlt
  have hR := hI.rows
  rw [hk] at hR
  obtain ⟨hl₀, hw₀⟩ := src_dst_lt he hlt
  obtain ⟨q1, q2, q3⟩ := hR.hc h hlt
  have a1 : c.nmem (c.nreg 10 * c.nreg 4 + c.nreg 7) = src d h := by
    rw [hk, h4, h7, ← q1]; congr 1; ring
  have a2 : c.nmem (c.nreg 10 * c.nreg 4 + c.nreg 7 + c.nreg 1) = dst d h := by
    rw [hk, h4, h7, h1, ← q2]; congr 1; ring
  have a3 : c.nmem (c.nreg 10 * c.nreg 4 + c.nreg 7 + c.nreg 1 + c.nreg 1) = res d h := by
    rw [hk, h4, h7, h1, ← q3]; congr 1; ring
  have hcl : c.nmem (src d h) ≤ 3 := by
    rw [hR.cnt _ hl₀]; exact (hcnt_mono d hlt.le _).trans (hcnt_le he le_rfl _)
  have hstep := hR.step he hlt
  unfold slot
  exec_block
  · rw [hk, h4]; omega
  · config_simp; rw [hk, h4, h7]; omega
  · config_simp; rw [hk, h4, h7, h1]; omega
  · config_simp; rw [hk, h4, h7, h1]; omega
  · config_simp; rw [a1, h4]; omega
  · config_simp; rw [a1, h4, h2]; omega
  · config_simp; rw [a1, h4, h2]; omega
  · config_simp; rw [a1, h4, h2, h6]; omega
  · config_simp; rw [a1, h1]; omega
  · config_simp; rw [hk, h1]; omega
  refine ⟨⟨‹_›, gregs_of hI.regs fun x hx => ?_, ?_, ?_, ?_⟩, ?_⟩
  · config_simp
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · config_simp; rw [hk, h1]; omega
  · config_simp
    rw [a1, a2, a3, h4, h2, h6, h1, hk,
      show src d h * 3 + dim d + c.nmem (src d h) = dim d + 3 * src d h + c.nmem (src d h) by ring]
    exact hstep
  · config_simp; exact hI.out
  · config_simp; rw [hk, h1]; omega

end A2

/-! ### Reading a half-edge -/

section head
variable {d : List ℕ} {W : ℕ}

theorem head_exec (he : GEnc d W) (c : Config) (hw : WordsBounded W c) (hR : GRegs d c)
    {h : ℕ} (hk : c.nreg 10 = h) (hlt : h < 2 * bm d)
    (hc : c.nmem (7 * dim d + 3 * h) = src d h ∧ c.nmem (7 * dim d + 3 * h + 1) = dst d h ∧
      c.nmem (7 * dim d + 3 * h + 2) = res d h) :
    ∃ c₁, Exec (inp d) W head c c₁ 13 ∧ WordsBounded W c₁ ∧ c₁.nreg 13 = src d h ∧
      c₁.nreg 14 = dst d h ∧ c₁.nreg 16 = res d h ∧
      c₁.nreg 23 = dst d h * dim d + (7 * dim d + 6 * bm d) ∧
      c₁.nreg 24 = src d h * 3 + dim d ∧ c₁.nreg 25 = c.nmem (src d h) ∧ c₁.nreg 26 = 0 ∧
      (∀ x, x ≠ 11 → x ≠ 13 → x ≠ 14 → x ≠ 16 → x ≠ 23 → x ≠ 24 → x ≠ 25 → x ≠ 26 →
        c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧ c₁.output = c.output := by
  have hW := he.size
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h30⟩ := hR
  obtain ⟨hl₀, hw₀⟩ := src_dst_lt he hlt
  obtain ⟨q1, q2, q3⟩ := hc
  have a1 : c.nmem (c.nreg 10 * c.nreg 4 + c.nreg 7) = src d h := by
    rw [hk, h4, h7, ← q1]; congr 1; ring
  have a2 : c.nmem (c.nreg 10 * c.nreg 4 + c.nreg 7 + c.nreg 1) = dst d h := by
    rw [hk, h4, h7, h1, ← q2]; congr 1; ring
  have a3 : c.nmem (c.nreg 10 * c.nreg 4 + c.nreg 7 + c.nreg 1 + c.nreg 1) = res d h := by
    rw [hk, h4, h7, h1, ← q3]; congr 1; ring
  have hin : dst d h * dim d ≤ dim d * dim d := Nat.mul_le_mul_right _ hw₀.le
  have e : ∃ c₁ k₁, Exec (inp d) W head c c₁ k₁ ∧ k₁ = 13 ∧ WordsBounded W c₁ ∧
      c₁.nreg 13 = src d h ∧
      c₁.nreg 14 = dst d h ∧ c₁.nreg 16 = res d h ∧
      c₁.nreg 23 = dst d h * dim d + (7 * dim d + 6 * bm d) ∧
      c₁.nreg 24 = src d h * 3 + dim d ∧ c₁.nreg 25 = c.nmem (src d h) ∧ c₁.nreg 26 = 0 ∧
      (∀ x, x ≠ 11 → x ≠ 13 → x ≠ 14 → x ≠ 16 → x ≠ 23 → x ≠ 24 → x ≠ 25 → x ≠ 26 →
        c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧ c₁.output = c.output := by
    unfold head
    exec_block
    · rw [hk, h4]; omega
    · config_simp; rw [hk, h4, h7]; omega
    · config_simp; rw [hk, h4, h7, h1]; omega
    · config_simp; rw [hk, h4, h7, h1]; omega
    · config_simp; rw [a2, h2]; omega
    · config_simp; rw [a2, h2, h8]; omega
    · config_simp; rw [a1, h4]; omega
    · config_simp; rw [a1, h4, h2]; omega
    refine ⟨rfl, ‹_›, by config_simp; exact a1, by config_simp; exact a2, by config_simp; exact a3,
      by config_simp; rw [a2, h2, h8], by config_simp; rw [a1, h4, h2],
      by config_simp; rw [a1], by config_simp; exact h0,
      fun x a b e f g h l m => by
        config_simp; simp only [upd_apply, a, b, e, f, g, h, l, m, ↓reduceIte], rfl, rfl⟩
  obtain ⟨c₁, k₁, e, rfl, rest⟩ := e
  exact ⟨c₁, e, rest⟩

end head

/-! ### Accumulating the Gram entries -/

/-- The Gram entries of the first `H` half-edges. -/
def GP (d : List ℕ) (H i j : ℕ) : ZMod (prm d) :=
  ∑ h ∈ range H, if dst d h = i then (res d h : ZMod (prm d)) * Kh d (src d h) j else 0

/-- The partial sum over the first `c` slots of the row `l`. -/
def Spart (d : List ℕ) (m : ℕ → ℕ) (l j c : ℕ) : ZMod (prm d) :=
  ∑ c' ∈ range c, if m (dim d + 3 * l + c') = j then
    (m (dim d + 3 * l + c' + 3 * dim d) : ZMod (prm d)) else 0

/-- The Gram cell `(i, j)`. -/
def gad (d : List ℕ) (i j : ℕ) : ℕ := 7 * dim d + 6 * bm d + i * dim d + j

/-- The state of the slot loop of the half-edge `h`, from `c₁`, over the memory `mA` of the
rows. -/
structure IBc (d : List ℕ) (W : ℕ) (mA : ℕ → ℕ) (h : ℕ) (c₁ c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ x, x ≠ 26 → x ≠ 27 → x ≠ 28 → x ≠ 29 → x ≠ 33 → c.nreg x = c₁.nreg x
  r26 : c.nreg 26 ≤ mA (src d h)
  low : ∀ a < 7 * dim d + 6 * bm d, c.nmem a = mA a
  glt : ∀ a, 7 * dim d + 6 * bm d ≤ a → c.nmem a < prm d
  G : ∀ i < dim d, ∀ j < dim d, (c.nmem (gad d i j) : ZMod (prm d)) = GP d h i j +
    if dst d h = i then (res d h : ZMod (prm d)) * Spart d mA (src d h) j (c.nreg 26) else 0
  out : c.output = c₁.output

section accum
variable {d : List ℕ} {W : ℕ}

theorem gad_inj {i j i' j' : ℕ} (hj : j < dim d) (hj' : j' < dim d) (h : gad d i j = gad d i' j') :
    i = i' ∧ j = j' := DetMod.idx_inj hj hj' (by unfold gad at h; omega)

theorem gad_lt {i j : ℕ} (hi : i < dim d) (hj : j < dim d) :
    gad d i j < 7 * dim d + 6 * bm d + dim d * dim d := by
  have := DetMod.idx_lt hi hj; unfold gad; omega

theorem accum_exec (he : GEnc d W) {mA : ℕ → ℕ} (hA : RowsOK d mA (2 * bm d)) {h : ℕ}
    (hh : h < 2 * bm d) {c₁ : Config} (hR : GRegs d c₁)
    (h14 : c₁.nreg 14 = dst d h) (h16 : c₁.nreg 16 = res d h)
    (h23 : c₁.nreg 23 = dst d h * dim d + (7 * dim d + 6 * bm d))
    (h24 : c₁.nreg 24 = src d h * 3 + dim d) (h25 : c₁.nreg 25 = mA (src d h))
    (c : Config) (hI : IBc d W mA h c₁ c) (hlt : c.nreg 26 < c.nreg 25) :
    ∃ c' k', Exec (inp d) W accum c c' k' ∧ IBc d W mA h c₁ c' ∧
      (mA (src d h) - c'.nreg 26) * 13 + k' + 2 ≤ (mA (src d h) - c.nreg 26) * 13 := by
  have hc := hI.wb
  have hW := he.size; have hWp := he.sq; have hp2 := he.two_le
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h30⟩ := gregs_of hR fun x hx =>
    hI.regs x (by omega) (by omega) (by omega) (by omega) (by omega)
  have g14 : c.nreg 14 = dst d h := by
    rw [hI.regs 14 (by omega) (by omega) (by omega) (by omega) (by omega), h14]
  have g16 : c.nreg 16 = res d h := by
    rw [hI.regs 16 (by omega) (by omega) (by omega) (by omega) (by omega), h16]
  have g23 : c.nreg 23 = dst d h * dim d + (7 * dim d + 6 * bm d) := by
    rw [hI.regs 23 (by omega) (by omega) (by omega) (by omega) (by omega), h23]
  have g24 : c.nreg 24 = src d h * 3 + dim d := by
    rw [hI.regs 24 (by omega) (by omega) (by omega) (by omega) (by omega), h24]
  have g25 : c.nreg 25 = mA (src d h) := by
    rw [hI.regs 25 (by omega) (by omega) (by omega) (by omega) (by omega), h25]
  rw [g25] at hlt
  obtain ⟨hl₀, hi₀⟩ := src_dst_lt he hh
  generalize hl : src d h = l at hl₀ hlt g24 g25 h24 h25
  generalize hcc : c.nreg 26 = cc at hlt
  have hcl : mA l ≤ 3 := by rw [hA.cnt l hl₀, ← hl]; exact hcnt_le he le_rfl _
  have hjn := hA.nb_lt l hl₀ cc hlt
  have hvp := hA.val_lt l hl₀ cc hlt
  have hap := res_lt he h
  generalize hj : mA (dim d + 3 * l + cc) = j at hjn
  have r1 : c.nmem (c.nreg 24 + c.nreg 26) = j := by
    rw [g24, hcc, hI.low _ (by omega), ← hj]; congr 1; ring
  have r2 : c.nmem (c.nreg 24 + c.nreg 26 + c.nreg 6) = mA (dim d + 3 * l + cc + 3 * dim d) := by
    rw [g24, hcc, h6, hI.low _ (by omega)]; congr 1; ring
  have hgad : c.nreg 23 + j = gad d (dst d h) j := by rw [g23, gad]; ring
  have hglt := hI.glt (gad d (dst d h) j) (by unfold gad; omega)
  have hgl := gad_lt (d := d) hi₀ hjn
  have hab : res d h * mA (dim d + 3 * l + cc + 3 * dim d) ≤ prm d * prm d :=
    Nat.mul_le_mul hap.le hvp.le
  unfold accum
  exec_block
  · rw [g24, hcc]; omega
  · config_simp; rw [g24, hcc, h6]; omega
  · config_simp; rw [r1]; omega
  · config_simp; rw [g16, r2]; omega
  · config_simp; rw [r1, hgad, g16, r2]; omega
  · config_simp; rw [hcc, h1]; omega
  refine ⟨⟨‹_›, fun x a b e f g => ?_, ?_, fun a ha => ?_, fun a ha => ?_, fun i hi j' hj' => ?_,
    by config_simp; exact hI.out⟩, ?_⟩
  · config_simp; simp only [upd_apply, a, b, e, f, g, ↓reduceIte]; exact hI.regs x a b e f g
  · config_simp; rw [hcc, h1, hl]; omega
  · config_simp; rw [r1, hgad, upd_other _ _ _ (by omega)]; exact hI.low a ha
  · config_simp; rw [r1, hgad]
    by_cases e : a = gad d (dst d h) j
    · rw [e, upd_same, h3]; exact Nat.mod_lt _ (by omega)
    · rw [upd_other _ _ _ e]; exact hI.glt a ha
  · config_simp
    rw [r1, hgad, g16, r2, h3, hcc, h1, Spart, sum_range_succ, ← Spart, hl]
    have hG := hI.G i hi j' hj'
    rw [hcc, hl] at hG
    by_cases e : gad d i j' = gad d (dst d h) j
    · obtain ⟨rfl, rfl⟩ := gad_inj hj' hjn e
      rw [upd_same, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, hG]
      simp only [↓reduceIte, hj, mul_add]
      ring
    · rw [upd_other _ _ _ e, hG]
      by_cases ei : dst d h = i
      · have : j ≠ j' := fun hh' => e (by rw [ei, hh'])
        simp only [ei, ↓reduceIte, hj, this, add_zero]
      · simp only [ei, ↓reduceIte]
  · config_simp; rw [hcc, h1]; try rw [hl]
    have : (mA l - cc) * 13 = (mA l - (cc + 1)) * 13 + 13 := by
      rw [← Nat.add_one_mul]; congr 1; omega
    omega

end accum

/-- The state of the accumulation loop over the half-edges, over the memory `mA` of the rows. -/
structure IB (d : List ℕ) (W : ℕ) (mA : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : GRegs d c
  r10 : c.nreg 10 ≤ 2 * bm d
  low : ∀ a < 7 * dim d + 6 * bm d, c.nmem a = mA a
  glt : ∀ a, 7 * dim d + 6 * bm d ≤ a → c.nmem a < prm d
  G : ∀ i < dim d, ∀ j < dim d, (c.nmem (gad d i j) : ZMod (prm d)) = GP d (c.nreg 10) i j
  out : c.output = []

/-- One half-edge of the accumulation. -/
def bstep : Stmt := .seq head (.seq (.whileLtN 26 25 accum) (.instr (.addN 10 10 1)))

/-- One half-edge of the printing. -/
def cstep : Stmt := .seq head (.seq (.whileLtN 26 25 emit) (.instr (.addN 10 10 1)))

theorem gram_eq : gram = (.seq setup <| .seq (.whileLtN 10 30 hedge) <|
    .seq (.instr (.copyN 10 0)) <| .seq (.whileLtN 10 5 slot) <| .seq (.instr (.copyN 10 0)) <|
    .seq (.whileLtN 10 5 bstep) <| .seq (.instr (.copyN 10 0)) (.whileLtN 10 5 cstep)) := rfl

section phaseB
variable {d : List ℕ} {W : ℕ}

theorem bstep_exec (he : GEnc d W) {mA : ℕ → ℕ} (hA : RowsOK d mA (2 * bm d)) (c : Config)
    (hI : IB d W mA c) (hlt : c.nreg 10 < c.nreg 5) :
    ∃ c' k', Exec (inp d) W bstep c c' k' ∧ IB d W mA c' ∧
      (2 * bm d - c'.nreg 10) * 57 + k' + 2 ≤ (2 * bm d - c.nreg 10) * 57 := by
  have hR := hI.regs
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h30⟩ := hR
  rw [h5] at hlt
  generalize hk : c.nreg 10 = h at hlt
  obtain ⟨hl₀, hi₀⟩ := src_dst_lt he hlt
  have hcells : c.nmem (7 * dim d + 3 * h) = src d h ∧ c.nmem (7 * dim d + 3 * h + 1) = dst d h ∧
      c.nmem (7 * dim d + 3 * h + 2) = res d h := by
    rw [hI.low _ (by omega), hI.low _ (by omega), hI.low _ (by omega)]; exact hA.hc h hlt
  obtain ⟨c₁, e₁, hw₁, g13, g14, g16, g23, g24, g25, g26, hr₁, hm₁, ho₁⟩ :=
    head_exec he c hI.wb hI.regs hk hlt hcells
  rw [hI.low _ (by omega)] at g25
  have hR₁ : GRegs d c₁ := gregs_of hI.regs fun x hx => hr₁ x (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hIc : IBc d W mA h c₁ c₁ := ⟨hw₁, fun _ _ _ _ _ _ => rfl, by rw [g26]; omega,
    fun a ha => by rw [hm₁]; exact hI.low a ha, fun a ha => by rw [hm₁]; exact hI.glt a ha,
    fun i hi j hj => by rw [hm₁, hI.G i hi j hj, hk, g26]; simp [Spart], rfl⟩
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 26)
    (b := 25) (body := accum) (IBc d W mA h c₁) (fun c => (mA (src d h) - c.nreg 26) * 13)
    (fun c h => h.wb) (fun c' hc' hlt' => accum_exec he hA hlt hR₁ g14 g16 g23 g24 g25 c' hc' hlt')
    hIc
  have g25₂ : c₂.nreg 25 = mA (src d h) := by
    rw [hI₂.regs 25 (by omega) (by omega) (by omega) (by omega) (by omega), g25]
  have h26₂ : c₂.nreg 26 = mA (src d h) := by have := hI₂.r26; rw [g25₂] at hn₂; omega
  have g10 : c₂.nreg 10 = h := by
    rw [hI₂.regs 10 (by omega) (by omega) (by omega) (by omega) (by omega),
      hr₁ 10 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), hk]
  have g1 : c₂.nreg 1 = 1 := by
    rw [hI₂.regs 1 (by omega) (by omega) (by omega) (by omega) (by omega), hR₁.2.1]
  have e₃ := Exec.addN (P := inp d) hI₂.wb 10 10 1 (by
    rw [g10, g1]; have := he.size; omega)
  refine ⟨_, _, .seq e₁ (.seq e₂ e₃), ⟨e₃.wb_right, ?_, ?_, fun a ha => ?_, fun a ha => ?_,
    fun i hi j hj => ?_, ?_⟩, ?_⟩
  · refine gregs_of hR₁ fun x hx => ?_
    config_simp
    rw [upd_other _ _ _ (by omega)]
    exact hI₂.regs x (by omega) (by omega) (by omega) (by omega) (by omega)
  · config_simp; rw [g10, g1]; omega
  · config_simp; exact hI₂.low a ha
  · config_simp; exact hI₂.glt a ha
  · config_simp
    rw [g10, g1, hI₂.G i hi j hj, h26₂, GP, GP, sum_range_succ]
    congr 1
    rw [show Spart d mA (src d h) j (mA (src d h)) = Kh d (src d h) j from
      hA.sum (src d h) hl₀ j]
  · config_simp; rw [hI₂.out, ho₁]; exact hI.out
  · config_simp; rw [g10, g1]
    rw [g26] at hk₂
    have h3 : mA (src d h) ≤ 3 := by rw [hA.cnt _ hl₀]; exact hcnt_le he le_rfl _
    have : (2 * bm d - h) * 57 = (2 * bm d - (h + 1)) * 57 + 57 := by
      rw [← Nat.add_one_mul]; congr 1; omega
    omega

end phaseB

/-! ### Printing the Gram entries -/

/-- The triple printed for the half-edge `h` and the slot `c`, from the memory `m`. -/
def trip (d : List ℕ) (m : ℕ → ℕ) (h c : ℕ) : ℕ × ℕ × ℕ :=
  (dst d h, m (dim d + 3 * src d h + c), m (gad d (dst d h) (m (dim d + 3 * src d h + c))))

/-- The triples of the first `H` half-edges. -/
def elist (d : List ℕ) (m : ℕ → ℕ) (H : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range H).flatMap fun h => (List.range (m (src d h))).map (trip d m h)

/-- The words of a list of triples. -/
def words (E : List (ℕ × ℕ × ℕ)) : List ℕ := E.flatMap fun x => [x.1, x.2.1, x.2.2]

theorem words_append (E F : List (ℕ × ℕ × ℕ)) : words (E ++ F) = words E ++ words F := by
  simp [words]

theorem words_singleton (x : ℕ × ℕ × ℕ) : words [x] = [x.1, x.2.1, x.2.2] := by simp [words]

theorem elist_succ (d : List ℕ) (m : ℕ → ℕ) (H : ℕ) :
    elist d m (H + 1) = elist d m H ++ (List.range (m (src d H))).map (trip d m H) := by
  simp [elist, List.range_succ, List.flatMap_append]

/-- The state of the printing loop of the half-edge `h`, from `c₁`. -/
structure ICc (d : List ℕ) (W : ℕ) (mB : ℕ → ℕ) (h : ℕ) (c₁ c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ x, x ≠ 26 → x ≠ 27 → x ≠ 28 → x ≠ 33 → c.nreg x = c₁.nreg x
  r26 : c.nreg 26 ≤ mB (src d h)
  mem : c.nmem = mB
  out : c.output = c₁.output ++ words ((List.range (c.nreg 26)).map (trip d mB h))

/-- The state of the printing loop over the half-edges. -/
structure IC (d : List ℕ) (W : ℕ) (mB : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : GRegs d c
  r10 : c.nreg 10 ≤ 2 * bm d
  mem : c.nmem = mB
  out : c.output = words (elist d mB (c.nreg 10))

section phaseC
variable {d : List ℕ} {W : ℕ}

theorem emit_exec (he : GEnc d W) {mA mB : ℕ → ℕ} (hA : RowsOK d mA (2 * bm d))
    (hlow : ∀ a < 7 * dim d + 6 * bm d, mB a = mA a) {h : ℕ}
    (hh : h < 2 * bm d) {c₁ : Config} (hR : GRegs d c₁)
    (h14 : c₁.nreg 14 = dst d h) (h23 : c₁.nreg 23 = dst d h * dim d + (7 * dim d + 6 * bm d))
    (h24 : c₁.nreg 24 = src d h * 3 + dim d) (h25 : c₁.nreg 25 = mB (src d h))
    (c : Config) (hI : ICc d W mB h c₁ c) (hlt : c.nreg 26 < c.nreg 25) :
    ∃ c' k', Exec (inp d) W emit c c' k' ∧ ICc d W mB h c₁ c' ∧
      (mB (src d h) - c'.nreg 26) * 10 + k' + 2 ≤ (mB (src d h) - c.nreg 26) * 10 := by
  have hc := hI.wb
  have hW := he.size
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h30⟩ := gregs_of hR fun x hx =>
    hI.regs x (by omega) (by omega) (by omega) (by omega)
  have g14 : c.nreg 14 = dst d h := by
    rw [hI.regs 14 (by omega) (by omega) (by omega) (by omega), h14]
  have g23 : c.nreg 23 = dst d h * dim d + (7 * dim d + 6 * bm d) := by
    rw [hI.regs 23 (by omega) (by omega) (by omega) (by omega), h23]
  have g24 : c.nreg 24 = src d h * 3 + dim d := by
    rw [hI.regs 24 (by omega) (by omega) (by omega) (by omega), h24]
  have g25 : c.nreg 25 = mB (src d h) := by
    rw [hI.regs 25 (by omega) (by omega) (by omega) (by omega), h25]
  rw [g25] at hlt
  obtain ⟨hl₀, hi₀⟩ := src_dst_lt he hh
  have hcl : mB (src d h) ≤ 3 := by
    rw [hlow _ (by omega), hA.cnt _ hl₀]; exact hcnt_le he le_rfl _
  have hjn : mB (dim d + 3 * src d h + c.nreg 26) < dim d := by
    rw [hlow _ (by omega)]
    exact hA.nb_lt _ hl₀ _ (by rw [← hlow _ (by omega)]; exact hlt)
  have r1 : c.nmem (c.nreg 24 + c.nreg 26) = mB (dim d + 3 * src d h + c.nreg 26) := by
    rw [g24, hI.mem]; congr 1; ring
  have hgad : c.nreg 23 + mB (dim d + 3 * src d h + c.nreg 26) =
      gad d (dst d h) (mB (dim d + 3 * src d h + c.nreg 26)) := by rw [g23, gad]; ring
  have hgl := gad_lt (d := d) hi₀ hjn
  unfold emit
  exec_block
  · rw [g24]; omega
  · config_simp; rw [r1, hgad]; omega
  · config_simp; rw [h1]; omega
  refine ⟨⟨‹_›, fun x a b e f => ?_, ?_, by config_simp; exact hI.mem, ?_⟩, ?_⟩
  · config_simp; simp only [upd_apply, a, b, e, f, ↓reduceIte]; exact hI.regs x a b e f
  · config_simp; rw [h1]; omega
  · config_simp
    rw [r1, hgad, g14, h1, hI.out, List.range_succ, List.map_append, words_append,
      List.append_assoc, hI.mem]
    simp [words, trip]
  · config_simp; rw [h1]
    have : (mB (src d h) - c.nreg 26) * 10 = (mB (src d h) - (c.nreg 26 + 1)) * 10 + 10 := by
      rw [← Nat.add_one_mul]; congr 1; omega
    omega

theorem cstep_exec (he : GEnc d W) {mA mB : ℕ → ℕ} (hA : RowsOK d mA (2 * bm d))
    (hlow : ∀ a < 7 * dim d + 6 * bm d, mB a = mA a) (c : Config)
    (hI : IC d W mB c) (hlt : c.nreg 10 < c.nreg 5) :
    ∃ c' k', Exec (inp d) W cstep c c' k' ∧ IC d W mB c' ∧
      (2 * bm d - c'.nreg 10) * 48 + k' + 2 ≤ (2 * bm d - c.nreg 10) * 48 := by
  have hR := hI.regs
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h30⟩ := hR
  rw [h5] at hlt
  generalize hk : c.nreg 10 = h at hlt
  obtain ⟨hl₀, hi₀⟩ := src_dst_lt he hlt
  have hcells : c.nmem (7 * dim d + 3 * h) = src d h ∧ c.nmem (7 * dim d + 3 * h + 1) = dst d h ∧
      c.nmem (7 * dim d + 3 * h + 2) = res d h := by
    rw [hI.mem, hlow _ (by omega), hlow _ (by omega), hlow _ (by omega)]; exact hA.hc h hlt
  obtain ⟨c₁, e₁, hw₁, g13, g14, g16, g23, g24, g25, g26, hr₁, hm₁, ho₁⟩ :=
    head_exec he c hI.wb hI.regs hk hlt hcells
  rw [hI.mem] at g25
  have hR₁ : GRegs d c₁ := gregs_of hI.regs fun x hx => hr₁ x (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hIc : ICc d W mB h c₁ c₁ := ⟨hw₁, fun _ _ _ _ _ => rfl, by rw [g26]; omega,
    by rw [hm₁, hI.mem], by rw [g26]; simp [words]⟩
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 26)
    (b := 25) (body := emit) (ICc d W mB h c₁) (fun c => (mB (src d h) - c.nreg 26) * 10)
    (fun c h => h.wb) (fun c' hc' hlt' => emit_exec he hA hlow hlt hR₁ g14 g23 g24 g25 c' hc'
      hlt') hIc
  have g25₂ : c₂.nreg 25 = mB (src d h) := by
    rw [hI₂.regs 25 (by omega) (by omega) (by omega) (by omega), g25]
  have h26₂ : c₂.nreg 26 = mB (src d h) := by have := hI₂.r26; rw [g25₂] at hn₂; omega
  have g10 : c₂.nreg 10 = h := by
    rw [hI₂.regs 10 (by omega) (by omega) (by omega) (by omega),
      hr₁ 10 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), hk]
  have g1 : c₂.nreg 1 = 1 := by
    rw [hI₂.regs 1 (by omega) (by omega) (by omega) (by omega), hR₁.2.1]
  have e₃ := Exec.addN (P := inp d) hI₂.wb 10 10 1 (by
    rw [g10, g1]; have := he.size; omega)
  have h3 : mB (src d h) ≤ 3 := by
    rw [hlow _ (by omega), hA.cnt _ hl₀]; exact hcnt_le he le_rfl _
  refine ⟨_, _, .seq e₁ (.seq e₂ e₃), ⟨e₃.wb_right, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine gregs_of hR₁ fun x hx => ?_
    config_simp
    rw [upd_other _ _ _ (by omega)]
    exact hI₂.regs x (by omega) (by omega) (by omega) (by omega)
  · config_simp; rw [g10, g1]; omega
  · config_simp; exact hI₂.mem
  · config_simp
    rw [g10, g1, hI₂.out, h26₂, ho₁, hI.out, hk, elist_succ, words_append]
  · config_simp; rw [g10, g1]
    rw [g26] at hk₂
    have : (2 * bm d - h) * 48 = (2 * bm d - (h + 1)) * 48 + 48 := by
      rw [← Nat.add_one_mul]; congr 1; omega
    omega

end phaseC

/-! ### The whole program -/

section main
variable {d : List ℕ} {W : ℕ}

theorem gram_exec (he : GEnc d W) :
    ∃ (c' : Config) (k : ℕ) (mA mB : ℕ → ℕ), Exec (inp d) W gram initConfig c' k ∧
      c'.output = words (elist d mB (2 * bm d)) ∧ RowsOK d mA (2 * bm d) ∧
      (∀ a < 7 * dim d + 6 * bm d, mB a = mA a) ∧
      (∀ a, 7 * dim d + 6 * bm d ≤ a → mB a < prm d) ∧
      (∀ i < dim d, ∀ j < dim d, (mB (gad d i j) : ZMod (prm d)) = Gz d i j) ∧
      k ≤ 278 * bm d + 26 := by
  have hW := he.size; have hWp := he.sq; have hp2 := he.two_le
  have hw0 : WordsBounded W initConfig := ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  -- set up
  have e₁ : ∃ c₁ k₁, Exec (inp d) W setup initConfig c₁ k₁ ∧ IA1 d W c₁ ∧ c₁.nreg 10 = 0 ∧
      k₁ = 15 := by
    unfold setup
    exec_block
    · omega
    · exact he.word_le _
    · exact he.word_le _
    · omega
    · omega
    · omega
    · exact he.word_le _
    · config_simp; show bm d * 2 ≤ W; omega
    · config_simp; show dim d * 3 ≤ W; omega
    · omega
    · config_simp; show dim d * 7 ≤ W; omega
    · config_simp; show bm d * 6 ≤ W; omega
    · config_simp; show bm d * 6 + dim d * 7 ≤ W; omega
    refine ⟨⟨‹_›, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun h hh => ?_,
      fun a _ => ?_, ?_⟩, ?_, rfl⟩
    all_goals config_simp
    all_goals try rfl
    · show bm d * 2 = 2 * bm d; ring
    · show dim d * 3 = 3 * dim d; ring
    · show dim d * 7 = 7 * dim d; ring
    · show bm d * 6 + dim d * 7 = 7 * dim d + 6 * bm d; ring
    · exact Nat.zero_le _
    · exact absurd hh (by show ¬ h < 2 * 0; omega)
  obtain ⟨c₁, k₁, e₁, hI₁, h10₁, rfl⟩ := e₁
  -- the half-edges
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 10)
    (b := 30) (body := hedge) (IA1 d W) (fun c => (bm d - c.nreg 10) * 30) (fun c h => h.wb)
    (fun c hc hlt => hedge_exec he c hc hlt) hI₁
  have h10₂ : c₂.nreg 10 = bm d := by
    have := hI₂.r10; rw [hI₂.regs.2.2.2.2.2.2.2.2.2.2.2] at hn₂; omega
  -- the rows
  have e₃ := Exec.copyN (P := inp d) hI₂.wb 10 0
  have hJ₃ : IA2 d W { c₂ with nreg := upd c₂.nreg 10 (c₂.nreg 0) } := by
    refine ⟨e₃.wb_right, gregs_upd hI₂.regs _ (by omega), by config_simp; rw [hI₂.regs.1]; omega,
      ⟨fun h hh => ?_, fun a ha => ?_, fun l hl => ?_, fun l hl c hc => ?_, fun l hl c hc => ?_,
        fun l hl j => ?_⟩, hI₂.out⟩
    · exact hI₂.hc h (by rw [h10₂]; exact hh)
    · exact hI₂.zero a (by rw [h10₂]; omega)
    · config_simp; rw [hI₂.regs.1, hI₂.zero l (by omega)]; rfl
    · config_simp at hc; rw [hI₂.zero l (by omega)] at hc; omega
    · config_simp at hc; rw [hI₂.zero l (by omega)] at hc; omega
    · config_simp; rw [hI₂.regs.1, Srow, hI₂.zero l (by omega)]; simp
  obtain ⟨c₄, k₄, e₄, hI₄, hn₄, hk₄⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 10)
    (b := 5) (body := slot) (IA2 d W) (fun c => (2 * bm d - c.nreg 10) * 19) (fun c h => h.wb)
    (fun c hc hlt => slot_exec he c hc hlt) hJ₃
  have h10₄ : c₄.nreg 10 = 2 * bm d := by
    have := hI₄.r10; rw [hI₄.regs.2.2.2.2.2.1] at hn₄; omega
  have hA : RowsOK d c₄.nmem (2 * bm d) := h10₄ ▸ hI₄.rows
  -- the accumulation
  have e₅ := Exec.copyN (P := inp d) hI₄.wb 10 0
  have hB₅ : IB d W c₄.nmem { c₄ with nreg := upd c₄.nreg 10 (c₄.nreg 0) } := by
    refine ⟨e₅.wb_right, gregs_upd hI₄.regs _ (by omega), by config_simp; rw [hI₄.regs.1]; omega,
      fun a _ => rfl, fun a ha => ?_, fun i hi j hj => ?_, hI₄.out⟩
    · config_simp; rw [hA.zeroG a ha]; omega
    · config_simp; rw [hI₄.regs.1, hA.zeroG _ (by unfold gad; omega)]; simp [GP]
  obtain ⟨c₆, k₆, e₆, hB₆, hn₆, hk₆⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 10)
    (b := 5) (body := bstep) (IB d W c₄.nmem) (fun c => (2 * bm d - c.nreg 10) * 57)
    (fun c h => h.wb) (fun c hc hlt => bstep_exec he hA c hc hlt) hB₅
  have h10₆ : c₆.nreg 10 = 2 * bm d := by
    have := hB₆.r10; rw [hB₆.regs.2.2.2.2.2.1] at hn₆; omega
  -- the printing
  have e₇ := Exec.copyN (P := inp d) hB₆.wb 10 0
  have hC₇ : IC d W c₆.nmem { c₆ with nreg := upd c₆.nreg 10 (c₆.nreg 0) } :=
    ⟨e₇.wb_right, gregs_upd hB₆.regs _ (by omega), by config_simp; rw [hB₆.regs.1]; omega, rfl,
      by config_simp; rw [hB₆.regs.1, hB₆.out]; rfl⟩
  obtain ⟨c₈, k₈, e₈, hC₈, hn₈, hk₈⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 10)
    (b := 5) (body := cstep) (IC d W c₆.nmem) (fun c => (2 * bm d - c.nreg 10) * 48)
    (fun c h => h.wb) (fun c hc hlt => cstep_exec he hA hB₆.low c hc hlt) hC₇
  have h10₈ : c₈.nreg 10 = 2 * bm d := by
    have := hC₈.r10; rw [hC₈.regs.2.2.2.2.2.1] at hn₈; omega
  refine ⟨c₈, _, c₄.nmem, c₆.nmem, by
      rw [gram_eq]
      exact .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈)))))),
    by rw [hC₈.out, h10₈], hA, hB₆.low, hB₆.glt, fun i hi j hj => by
      rw [hB₆.G i hi j hj, h10₆]; rfl, ?_⟩
  simp only [h10₁] at hk₂
  have q4 : ({ c₂ with nreg := upd c₂.nreg 10 (c₂.nreg 0) } : Config).nreg 10 = 0 := by
    config_simp; exact hI₂.regs.1
  have q6 : ({ c₄ with nreg := upd c₄.nreg 10 (c₄.nreg 0) } : Config).nreg 10 = 0 := by
    config_simp; exact hI₄.regs.1
  have q8 : ({ c₆ with nreg := upd c₆.nreg 10 (c₆.nreg 0) } : Config).nreg 10 = 0 := by
    config_simp; exact hB₆.regs.1
  rw [q4] at hk₄; rw [q6] at hk₆; rw [q8] at hk₈
  omega

theorem mem_elist {m : ℕ → ℕ} {H : ℕ} {x : ℕ × ℕ × ℕ} :
    x ∈ elist d m H ↔ ∃ h < H, ∃ c < m (src d h), trip d m h c = x := by
  simp [elist]

theorem length_elist (he : GEnc d W) {mA m : ℕ → ℕ} (hA : RowsOK d mA (2 * bm d))
    (hlow : ∀ a < 7 * dim d + 6 * bm d, m a = mA a) {H : ℕ} (hH : H ≤ 2 * bm d) :
    (elist d m H).length ≤ 3 * H := by
  induction H with
  | zero => simp [elist]
  | succ H ih =>
    rw [elist_succ, List.length_append, List.length_map, List.length_range]
    obtain ⟨hl₀, -⟩ := src_dst_lt he (show H < 2 * bm d by omega)
    have : m (src d H) ≤ 3 := by
      rw [hlow _ (by omega), hA.cnt _ hl₀]; exact hcnt_le he le_rfl _
    have := ih (by omega)
    omega

/-- **The Gram entries on the machine.** On a well-formed input (`GEnc d W`) the compiled
program halts within `278 m + 27` steps and prints the words of a list `E` of at most `6 m`
triples `(i, j, g)` with `i, j < n`, `g < p` and `g ≡ Gz i j`, covering every position `(i, j)`
where `Gz i j ≠ 0`. -/
theorem gram_runsWithin (he : GEnc d W) :
    ∃ E : List (ℕ × ℕ × ℕ),
      RunsWithin (compile gram 0 ++ [Instr.halt]) (inp d) W (278 * bm d + 27) (words E) ∧
      E.length ≤ 6 * bm d ∧
      (∀ x ∈ E, x.1 < dim d ∧ x.2.1 < dim d ∧ x.2.2 < prm d ∧
        (x.2.2 : ZMod (prm d)) = Gz d x.1 x.2.1) ∧
      (∀ i < dim d, ∀ j < dim d, Gz d i j ≠ 0 → ∃ x ∈ E, x.1 = i ∧ x.2.1 = j) := by
  obtain ⟨c', k, mA, mB, e, hout, hA, hlow, hglt, hG, hk⟩ := gram_exec he
  refine ⟨elist d mB (2 * bm d),
    RunsWithin.mono_steps (runsWithin_of_exec_output e hout) (by omega), ?_, ?_, ?_⟩
  · have := length_elist he hA hlow (le_refl (2 * bm d)); omega
  · intro x hx
    obtain ⟨h, hh, c, hc, rfl⟩ := mem_elist.1 hx
    obtain ⟨-, hi₀⟩ := src_dst_lt he hh
    obtain ⟨hl₀, -⟩ := src_dst_lt he hh
    have hc' : c < mA (src d h) := by rw [← hlow (src d h) (by omega)]; exact hc
    have hj := hA.nb_lt _ hl₀ c hc'
    have h3 : mA (src d h) ≤ 3 := by rw [hA.cnt _ hl₀]; exact hcnt_le he le_rfl _
    rw [← hlow (dim d + 3 * src d h + c) (by omega)] at hj
    refine ⟨hi₀, hj, hglt _ (by unfold gad; omega), hG _ hi₀ _ hj⟩
  · intro i hi j hj hne
    obtain ⟨h, hh, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hh' := mem_range.1 hh
    by_cases hd : dst d h = i
    · simp only [hd, ↓reduceIte] at hne'
      have hK : Kh d (src d h) j ≠ 0 := fun h0 => hne' (by rw [h0, mul_zero])
      obtain ⟨hl₀, -⟩ := src_dst_lt he hh'
      rw [Kh, ← hA.sum _ hl₀ j, Srow] at hK
      obtain ⟨c, hc, hne''⟩ := Finset.exists_ne_zero_of_sum_ne_zero hK
      have hc' := mem_range.1 hc
      have hcj : mA (dim d + 3 * src d h + c) = j := by
        by_contra hn; simp [hn] at hne''
      refine ⟨trip d mB h c,
        mem_elist.2 ⟨h, hh', c, by rw [hlow (src d h) (by omega)]; exact hc', rfl⟩,
        hd, ?_⟩
      show mB (dim d + 3 * src d h + c) = j
      have h3 : mA (src d h) ≤ 3 := by rw [hA.cnt _ hl₀]; exact hcnt_le he le_rfl _
      rw [hlow _ (by omega), hcj]
    · simp [hd] at hne'

end main

end GramMod

end NestedDissection
