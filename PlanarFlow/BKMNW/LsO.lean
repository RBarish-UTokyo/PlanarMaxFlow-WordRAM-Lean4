module

public import PlanarFlow.BKMNW.LsN

/-!
# **`sepL` composed; `SepPSpecXLS' sepL`**

* **`sepL = lsH1 ; lsH2`** (`lsA ; lgS5D ; lsB ; ls6 ; ls7 ; ls8 ; ls9 ; ls10`: set-up, stage 5,
  the path of the certificate in all three cases, stage 6 and the path's flags, stage 7, the
  children's records and tags, the outputs 1–4 written again, the parts);
* `sTL n k = 1010000 n lg n + 400 k`, `sRL n m k = 21 m + 6100 n + 20 k + 2 encB' (223 n + 84) +
  4000`; `lsEncB_mono`; **`sTL_le`** (`sTL n k ≤ 1010000 n lg n + 1010000 k`);
* **`sepL_spec`**: `SepPSpecXLS' M ds Reach gid ν u S T Z I W sepL sTL sRL` for the decomposition
  system of the headline (`ds.spS = guardS gSz (spSR (pcChoiceE M Q eG N d₀) (s5sc M eG N) Q)`,
  `ds.spH` likewise with `gHl`/`spHR`, `ds.chS = chRot M Q`, `ds.s = 100000`, `ds.Q = Q`,
  `ds.pk = (pcChoiceE …).pick`), given `SplitFnsS` of the guarded functions, `smD` keeping
  pieces, `S ∪ T ⊆ Q`, a loopless map, `hQdeg`, `hQ5`, `TailSorted`, `QPar`, `ν` and `gid`
  injective, the global enumeration `eG` (`gid (eG i) = i`), `100000 ≤ W`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The large-piece separator program.** -/
def sepL : Stmt := .seq lsH1 lsH2

/-- **The steps of `sepL`** (`n` darts of the piece, `k` holes). -/
def sTL (n k : ℕ) : ℕ := 1010000 * n * lg n + 400 * k

/-- **The room of `sepL`** above `Sb` (`m` darts of the piece map). -/
def sRL (n m k : ℕ) : ℕ := 21 * m + 6100 * n + 20 * k + 2 * encB' (223 * n + 84) + 4000

lemma lsEncB_mono {x y : ℕ} (h : x ≤ y) : encB' x ≤ encB' y := by
  rw [encB'_eq, encB'_eq]
  have h1 : Nat.log 2 (2 * x) ≤ Nat.log 2 (2 * y) := Nat.log_mono_right (by omega)
  have h2 : (Nat.log 2 (2 * x) + 2) * (2 * x) ≤ (Nat.log 2 (2 * y) + 2) * (2 * y) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-- `sTL` in `O(n lg n + k)`. -/
lemma sTL_le (n k : ℕ) : sTL n k ≤ 1010000 * n * lg n + 1010000 * k := by
  unfold sTL; omega

/-- The arithmetic of the steps. -/
lemma sepL_time {n m k nB W₀ t₁ t₂ : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) (hB : nB ≤ n)
    (hW : W₀ ≤ 223 * n + 84)
    (h1 : t₁ ≤ 9700 * n + 70 * k + 5 * Nat.log 2 (2 * W₀) + mbTD nB (encB' W₀) W₀ + 930 * n +
      30 * m + 90 * k + 4890) (h2 : t₂ ≤ 1720 * n + 37 * m + 107 * k + 1550) :
    t₁ + t₂ ≤ sTL n k := by
  have h := s5TD_le (k := k) hn hB hW
  have hl : n ≤ n * lg n := Nat.le_mul_of_pos_right n (by unfold lg; omega)
  have e1 : 1000300 * n * lg n = 1000300 * (n * lg n) := by ring
  have e2 : 1010000 * n * lg n = 1010000 * (n * lg n) := by ring
  rw [e1] at h
  unfold sTL; rw [e2]
  omega

end MfDrv

end BKMNW

end PlanarFlow
