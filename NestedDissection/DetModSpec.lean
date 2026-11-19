module

public import WordRAM.Spec
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Specification: the input of the determinant modulo a prime

The input format of the machine program computing a determinant modulo a prime
(`NestedDissection/DetModRun.lean`). This file imports only Mathlib and the machine model
`WordRAM/Spec.lean` (itself Mathlib-only).

* The input is the list `[n, p, a₀₀, a₀₁, …, a_{n-1,n-1}]` (`inp`, with an all-zero random
  tape): the dimension `dim d = n`, the modulus `prm d = p`, and the entries row by row
  (`ent d`).
* `mat n p m` is the `n × n` matrix stored row by row in `m`, read in `ZMod p`, and `inMat d` is
  the matrix of the input.
* `DEnc d W` says that the input is well formed for the word bound `W`: `p` is prime, every
  input word is at most `W`, and `W` is at least `p² + p` and `n² + 2`.
-/

@[expose] public section

namespace NestedDissection

namespace DetMod

open WordRAM Finset

/-- The input. -/
def inp (d : List ℕ) : Input := ⟨d, fun _ => 0⟩

/-- The dimension `n`, the modulus `p`, and the entries (row by row, from position `2`). -/
def dim (d : List ℕ) : ℕ := d.getD 0 0
def prm (d : List ℕ) : ℕ := d.getD 1 0
def ent (d : List ℕ) (t : ℕ) : ℕ := d.getD (t + 2) 0

/-- Well-formed inputs and words: a prime modulus, words large enough for products of residues
and for the addresses. -/
structure DEnc (d : List ℕ) (W : ℕ) : Prop where
  prime : (prm d).Prime
  word_le : ∀ i, d.getD i 0 ≤ W
  sq : prm d * prm d + prm d ≤ W
  dim_sq : dim d * dim d + 2 ≤ W

section Mat

open Matrix

/-- The `n × n` matrix stored row by row in `m`, read modulo `p`. -/
def mat (n p : ℕ) (m : ℕ → ℕ) : Matrix (Fin n) (Fin n) (ZMod p) :=
  fun i j => (m (i * n + j) : ZMod p)

end Mat

/-- The matrix of the input, modulo `p`. -/
def inMat (d : List ℕ) : Matrix (Fin (dim d)) (Fin (dim d)) (ZMod (prm d)) :=
  mat (dim d) (prm d) (ent d)

end DetMod

end NestedDissection

end
