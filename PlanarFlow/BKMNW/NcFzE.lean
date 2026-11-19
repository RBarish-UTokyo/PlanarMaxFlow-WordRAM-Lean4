module

public import PlanarFlow.BKMNW.NcFzD

/-!
# The pendant frame writer `pfP`: the loops of stages 3–4

Each loop of stages 3–4 as a lemma with the registers `Rg1`, `Rg2` and the few facts on its
input arrays (`d' = S + 12 + 16 m`, `m' = m + 2n`):

* `pfDV_exec` (`DVr[t] := DV[IX[t]]`), `pfZG_exec` (`ZG[t] := DG[IX[t]]·Z`), `t < n`;
* `pfRV0_exec` (`RV'[t] := RV[t]`, `t < m`), `pfRV1_exec` (`RV'[m + t] := t + (m + n)`),
  `pfRV2_exec` (`RV'[m + n + t] := t + m`);
* `pfSG0_exec` (`SG'[t] := sgV LAB[t] SG[t] m CI[LAB[t] − 1]`), `pfSG1_exec`
  (`SG'[m + t] := IX[t]`), `pfSG2_exec` (`SG'[m + n + t] := t + (m + n)`);
* `pfCP0_exec` (`CP'[t] := CP[t] ∸ CP[t]·Q[t]`), `pfCP1_exec` (`CP'[m + t] := DVr[t] ∸ ZG[t]`),
  `pfCP2_exec` (`CP'[m + n + t] := ZG[t] ∸ DVr[t]`);
* `pfFL0_exec` (`FL'[t] := F1[t] + Z' ∸ X0[t]`), `pfFL1_exec` (`FL'[m + t] := DVr[t] + Z' ∸ ZG[t]`),
  `pfFL2_exec` (`FL'[m + n + t] := ZG[t] + Z' ∸ DVr[t]`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcFz

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv

variable {P : Input} {W : ℕ}

lemma one_sub_mul_le (x y : ℕ) : (1 - x) * y ≤ y := by
  rcases Nat.eq_zero_or_pos x with h | h
  · simp [h]
  · rw [show 1 - x = 0 by omega]; simp

lemma sgV_le (lab s K ci : ℕ) : sgV lab s K ci ≤ s + (ci + K) := by
  unfold sgV
  have := one_sub_mul_le ((s - (lab - 1)) + ((lab - 1) - s)) (ci + K - s)
  omega

section Loops

variable {d m Z S F1b DFb CPb n : ℕ}

/-- `DVr[t] := DV[IX[t]]`. -/
theorem pfDV_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (wS : S + 40 * m + 20 ≤ W) (hix : ∀ t < n, c.nmem (S + 12 + 12 * m + t) < m) :
    ∃ c' k, Exec P W (lp 9963 9967 9969 9988 9972 9972 9931 bG) c c' k ∧ k ≤ 10 * n + 10 ∧
      LpOut c c' (S + 12 + 14 * m) n
        (fun t => c.nmem (S + 12 + 8 * m + c.nmem (S + 12 + 12 * m + t)) * 1) :=
  lp_exec (P := P) c hc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      have hix' : ∀ t < n, c'.nmem (S + 12 + 12 * m + t) < m := fun t ht => by
        rw [hm']; exact hix t ht
      obtain ⟨c'', k, ex, hk, hP⟩ := lG_exec (P := P) c' hw hW (bnd := 9931) (n := n)
        (X := S + 12 + 8 * m) (Y := S + 12 + 12 * m) (O := S + 12 + 14 * m) (K := 1)
        (by rw [g _ (by omega), R2.r31]) (by unfold PfScr; omega) (by rw [a23, R.r63])
        (by rw [a24, R.r67]) (by rw [a25, R.r69]) (by rw [a26, R.r88]) (by omega) (by omega)
        (by omega) (fun t ht => by have := hix' t ht; omega)
        (fun t ht => by
          have := hw.2 (S + 12 + 8 * m + c'.nmem (S + 12 + 12 * m + t)); omega)
        (fun t ht j hj => by omega) (fun t ht j hj => by have := hix' t ht; omega)
      rw [hm'] at hP
      exact ⟨c'', k, ex, hk, hP⟩)

/-- `ZG[t] := DG[IX[t]]·Z`. -/
theorem pfZG_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (wS : S + 40 * m + 20 ≤ W) (wZ : 4 * (m * Z) + 4 * Z + 4 ≤ W)
    (hix : ∀ t < n, c.nmem (S + 12 + 12 * m + t) < m)
    (hdg : ∀ t < n, c.nmem (S + 12 + 9 * m + c.nmem (S + 12 + 12 * m + t)) ≤ m) :
    ∃ c' k, Exec P W (lp 9964 9967 9970 9951 9972 9972 9931 bG) c c' k ∧ k ≤ 10 * n + 10 ∧
      LpOut c c' (S + 12 + 15 * m) n
        (fun t => c.nmem (S + 12 + 9 * m + c.nmem (S + 12 + 12 * m + t)) * Z) :=
  lp_exec (P := P) c hc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      have hix' : ∀ t < n, c'.nmem (S + 12 + 12 * m + t) < m := fun t ht => by
        rw [hm']; exact hix t ht
      have hdg' : ∀ t < n, c'.nmem (S + 12 + 9 * m + c'.nmem (S + 12 + 12 * m + t)) ≤ m :=
        fun t ht => by rw [hm']; exact hdg t ht
      obtain ⟨c'', k, ex, hk, hP⟩ := lG_exec (P := P) c' hw hW (bnd := 9931) (n := n)
        (X := S + 12 + 9 * m) (Y := S + 12 + 12 * m) (O := S + 12 + 15 * m) (K := Z)
        (by rw [g _ (by omega), R2.r31]) (by unfold PfScr; omega) (by rw [a23, R.r64])
        (by rw [a24, R.r67]) (by rw [a25, R.r70]) (by rw [a26, R.r51]) (by omega) (by omega)
        (by omega) (fun t ht => by have := hix' t ht; omega)
        (fun t ht => by
          have := Nat.mul_le_mul_right Z (hdg' t ht); omega)
        (fun t ht j hj => by omega) (fun t ht j hj => by have := hix' t ht; omega)
      rw [hm'] at hP
      exact ⟨c'', k, ex, hk, hP⟩)

/-- `RV'[t] := RV[t]`. -/
theorem pfRV0_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (lfr : d + 4 + 7 * m ≤ S) (wS : S + 40 * m + 20 ≤ W) :
    ∃ c' k, Exec P W (lp 9953 9972 9974 9972 9972 9972 9930 bAk) c c' k ∧ k ≤ 9 * m + 10 ∧
      LpOut c c' (S + 12 + 16 * m + 4 + (m + 2 * n)) m (fun t => c.nmem (d + 4 + m + t) + 0 - 0) :=
  lp_exec (P := P) c hc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      obtain ⟨c'', k, ex, hk, hP⟩ := lAk_exec (P := P) c' hw hW (bnd := 9930) (n := m)
        (X := d + 4 + m) (O := S + 12 + 16 * m + 4 + (m + 2 * n)) (K := 0) (K₂ := 0)
        (by rw [g _ (by omega), R.r30]) (by unfold PfScr; omega) (by rw [a23, R.r53])
        (by rw [a25, R2.r74]) (by rw [a26, R.r72]) (by rw [a27, R.r72]) (by omega) (by omega)
        (by omega) (fun t ht => by have := hw.2 (d + 4 + m + t); omega)
        (fun t ht j hj => by omega)
      rw [hm'] at hP
      exact ⟨c'', k, ex, hk, hP⟩)

/-- `RV'[m + t] := t + (m + n)`. -/
theorem pfRV1_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (wS : S + 40 * m + 20 ≤ W) :
    ∃ c' k, Exec P W (lp 9972 9972 9980 9978 9972 9972 9931 bId) c c' k ∧ k ≤ 6 * n + 10 ∧
      LpOut c c' (S + 12 + 16 * m + 4 + (m + 2 * n) + m) n (fun t => t + (m + n)) :=
  lp_exec (P := P) c hc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      obtain ⟨c'', k, ex, hk, hP⟩ := lId_exec (P := P) c' hw hW (bnd := 9931) (n := n)
        (O := S + 12 + 16 * m + 4 + (m + 2 * n) + m) (K := m + n)
        (by rw [g _ (by omega), R2.r31]) (by unfold PfScr; omega)
        (by rw [a25, R2.r80]) (by rw [a26, R2.r78]) (by omega) (by omega) (by omega)
      exact ⟨c'', k, ex, hk, hP⟩)

/-- `RV'[m + n + t] := t + m`. -/
theorem pfRV2_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (wS : S + 40 * m + 20 ≤ W) :
    ∃ c' k, Exec P W (lp 9972 9972 9981 9930 9972 9972 9931 bId) c c' k ∧ k ≤ 6 * n + 10 ∧
      LpOut c c' (S + 12 + 16 * m + 4 + (m + 2 * n) + (m + n)) n (fun t => t + m) :=
  lp_exec (P := P) c hc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      obtain ⟨c'', k, ex, hk, hP⟩ := lId_exec (P := P) c' hw hW (bnd := 9931) (n := n)
        (O := S + 12 + 16 * m + 4 + (m + 2 * n) + (m + n)) (K := m)
        (by rw [g _ (by omega), R2.r31]) (by unfold PfScr; omega)
        (by rw [a25, R2.r81]) (by rw [a26, R.r30]) (by omega) (by omega) (by omega)
      exact ⟨c'', k, ex, hk, hP⟩)

/-- `SG'[t] := sgV LAB[t] SG[t] m CI[LAB[t] − 1]`. -/
theorem pfSG0_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (lfr : d + 4 + 7 * m ≤ S) (wS : S + 40 * m + 20 ≤ W)
    (hlab : ∀ t < m, 1 ≤ c.nmem (S + 12 + 7 * m + t) ∧ c.nmem (S + 12 + 7 * m + t) ≤ m)
    (hsg : ∀ t < m, c.nmem (d + 4 + m + m + t) < m)
    (hci : ∀ t < m, c.nmem (S + 12 + 11 * m + (c.nmem (S + 12 + 7 * m + t) - 1)) ≤ m) :
    ∃ c' k, Exec P W (lp 9962 9954 9975 9930 9972 9966 9930 bSg) c c' k ∧ k ≤ 20 * m + 10 ∧
      LpOut c c' (S + 12 + 16 * m + 4 + 2 * (m + 2 * n)) m
        (fun t => sgV (c.nmem (S + 12 + 7 * m + t)) (c.nmem (d + 4 + m + m + t)) m
          (c.nmem (S + 12 + 11 * m + (c.nmem (S + 12 + 7 * m + t) - 1)))) :=
  lp_exec (P := P) c hc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      have hlab' : ∀ t < m, 1 ≤ c'.nmem (S + 12 + 7 * m + t) ∧ c'.nmem (S + 12 + 7 * m + t) ≤ m :=
        fun t ht => by rw [hm']; exact hlab t ht
      have hsg' : ∀ t < m, c'.nmem (d + 4 + m + m + t) < m := fun t ht => by
        rw [hm']; exact hsg t ht
      have hci' : ∀ t < m,
          c'.nmem (S + 12 + 11 * m + (c'.nmem (S + 12 + 7 * m + t) - 1)) ≤ m :=
        fun t ht => by rw [hm']; exact hci t ht
      obtain ⟨c'', k, ex, hk, hP⟩ := lSg_exec (P := P) c' hw hW (bnd := 9930) (n := m)
        (X := S + 12 + 7 * m) (Y := d + 4 + m + m) (O := S + 12 + 16 * m + 4 + 2 * (m + 2 * n))
        (K := m) (R := S + 12 + 11 * m)
        (by rw [g _ (by omega), R.r30]) (by unfold PfScr; omega) (by rw [a23, R.r62])
        (by rw [a24, R.r54]) (by rw [a25, R2.r75]) (by rw [a26, R.r30]) (by rw [a29, R.r66])
        (by omega) (by omega) (by omega) (by omega)
        (fun t ht => by have := hlab' t ht; omega)
        (fun t ht => by have := hci' t ht; omega)
        (fun t ht => by
          have := sgV_le (c'.nmem (S + 12 + 7 * m + t)) (c'.nmem (d + 4 + m + m + t)) m
            (c'.nmem (S + 12 + 11 * m + (c'.nmem (S + 12 + 7 * m + t) - 1)))
          have := hsg' t ht; have := hci' t ht; omega)
        (fun t ht => by
          have := one_sub_mul_le ((c'.nmem (d + 4 + m + m + t) - (c'.nmem (S + 12 + 7 * m + t) - 1)) +
            ((c'.nmem (S + 12 + 7 * m + t) - 1) - c'.nmem (d + 4 + m + m + t)))
            (c'.nmem (S + 12 + 11 * m + (c'.nmem (S + 12 + 7 * m + t) - 1)) + m -
              c'.nmem (d + 4 + m + m + t))
          have := hci' t ht; omega)
        (fun t ht => by have := hsg' t ht; have := hlab' t ht; omega)
        (fun t ht j hj => by omega) (fun t ht j hj => by omega)
        (fun t ht j hj => by have := hlab' t ht; omega)
      rw [hm'] at hP
      exact ⟨c'', k, ex, hk, hP⟩)

/-- `SG'[m + t] := IX[t]`. -/
theorem pfSG1_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (wS : S + 40 * m + 20 ≤ W) (hix : ∀ t < n, c.nmem (S + 12 + 12 * m + t) < m) :
    ∃ c' k, Exec P W (lp 9967 9972 9982 9972 9972 9972 9931 bAk) c c' k ∧ k ≤ 9 * n + 10 ∧
      LpOut c c' (S + 12 + 16 * m + 4 + 2 * (m + 2 * n) + m) n
        (fun t => c.nmem (S + 12 + 12 * m + t) + 0 - 0) :=
  lp_exec (P := P) c hc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      obtain ⟨c'', k, ex, hk, hP⟩ := lAk_exec (P := P) c' hw hW (bnd := 9931) (n := n)
        (X := S + 12 + 12 * m) (O := S + 12 + 16 * m + 4 + 2 * (m + 2 * n) + m) (K := 0) (K₂ := 0)
        (by rw [g _ (by omega), R2.r31]) (by unfold PfScr; omega) (by rw [a23, R.r67])
        (by rw [a25, R2.r82]) (by rw [a26, R.r72]) (by rw [a27, R.r72]) (by omega) (by omega)
        (by omega) (fun t ht => by have := hw.2 (S + 12 + 12 * m + t); omega)
        (fun t ht j hj => by omega)
      rw [hm'] at hP
      exact ⟨c'', k, ex, hk, hP⟩)

/-- `SG'[m + n + t] := t + (m + n)`. -/
theorem pfSG2_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (wS : S + 40 * m + 20 ≤ W) :
    ∃ c' k, Exec P W (lp 9972 9972 9983 9978 9972 9972 9931 bId) c c' k ∧ k ≤ 6 * n + 10 ∧
      LpOut c c' (S + 12 + 16 * m + 4 + 2 * (m + 2 * n) + (m + n)) n (fun t => t + (m + n)) :=
  lp_exec (P := P) c hc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      obtain ⟨c'', k, ex, hk, hP⟩ := lId_exec (P := P) c' hw hW (bnd := 9931) (n := n)
        (O := S + 12 + 16 * m + 4 + 2 * (m + 2 * n) + (m + n)) (K := m + n)
        (by rw [g _ (by omega), R2.r31]) (by unfold PfScr; omega)
        (by rw [a25, R2.r83]) (by rw [a26, R2.r78]) (by omega) (by omega) (by omega)
      exact ⟨c'', k, ex, hk, hP⟩)

/-- `CP'[t] := CP[t] ∸ CP[t]·Q[t]`. -/
theorem pfCP0_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (lC : CPb + m ≤ S) (wS : S + 40 * m + 20 ≤ W)
    (hq : ∀ t < m, c.nmem (S + 12 + 13 * m + t) ≤ 1) :
    ∃ c' k, Exec P W (lp 9955 9968 9976 9972 9972 9972 9930 bDf) c c' k ∧ k ≤ 11 * m + 10 ∧
      LpOut c c' (S + 12 + 16 * m + 4 + 3 * (m + 2 * n)) m
        (fun t => c.nmem (CPb + t) - c.nmem (CPb + t) * c.nmem (S + 12 + 13 * m + t)) :=
  lp_exec (P := P) c hc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      have hq' : ∀ t < m, c'.nmem (S + 12 + 13 * m + t) ≤ 1 := fun t ht => by
        rw [hm']; exact hq t ht
      obtain ⟨c'', k, ex, hk, hP⟩ := lDf_exec (P := P) c' hw hW (bnd := 9930) (n := m)
        (X := CPb) (Y := S + 12 + 13 * m) (O := S + 12 + 16 * m + 4 + 3 * (m + 2 * n))
        (by rw [g _ (by omega), R.r30]) (by unfold PfScr; omega) (by rw [a23, R.r55])
        (by rw [a24, R.r68]) (by rw [a25, R2.r76]) (by omega) (by omega) (by omega) (by omega)
        (fun t ht => by
          have := mul_le_of_le_one' (a := c'.nmem (CPb + t)) (hq' t ht)
          have := hw.2 (CPb + t); omega)
        (fun t ht j hj => by omega) (fun t ht j hj => by omega)
      rw [hm'] at hP
      exact ⟨c'', k, ex, hk, hP⟩)

/-- `OUT[t] := X[t] + K ∸ Y[t]` on two arrays of length `n` below the pendant frame. -/
theorem pfSx_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (wS : S + 40 * m + 20 ≤ W) {xr yr or kr X Y O K : ℕ} (hxr : c.nreg xr = X)
    (hyr : c.nreg yr = Y) (hor : c.nreg or = O) (hkr : c.nreg kr = K)
    (h1 : ¬ (9923 ≤ xr ∧ xr ≤ 9929)) (h2 : ¬ (9923 ≤ yr ∧ yr ≤ 9929))
    (h3 : ¬ (9923 ≤ or ∧ or ≤ 9929)) (h4 : ¬ (9923 ≤ kr ∧ kr ≤ 9929))
    (wX : X + n ≤ W) (wY : Y + n ≤ W) (wO : O + n ≤ W) (dXO : X + n ≤ O) (dYO : Y + n ≤ O)
    (w : ∀ t < n, c.nmem (X + t) + K ≤ W) :
    ∃ c' k, Exec P W (lp xr yr or kr 9972 9972 9931 bSx) c c' k ∧ k ≤ 11 * n + 10 ∧
      LpOut c c' O n (fun t => c.nmem (X + t) + K - c.nmem (Y + t)) :=
  lp_exec (P := P) c hc h1 h2 h3 h4 (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      obtain ⟨c'', k, ex, hk, hP⟩ := lSx_exec (P := P) c' hw hW (bnd := 9931) (n := n)
        (X := X) (Y := Y) (O := O) (K := K)
        (by rw [g _ (by omega), R2.r31]) (by unfold PfScr; omega) (by rw [a23, hxr])
        (by rw [a24, hyr]) (by rw [a25, hor]) (by rw [a26, hkr]) (by omega) wO wX wY
        (fun t ht => by rw [hm']; exact w t ht)
        (fun t ht j hj => by omega) (fun t ht j hj => by omega)
      rw [hm'] at hP
      exact ⟨c'', k, ex, hk, hP⟩)

/-- `FL'[t] := F1[t] + Z' ∸ X0[t]`. -/
theorem pfFL0_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (lF : F1b + m ≤ S) (wS : S + 40 * m + 20 ≤ W) (wZ : 4 * (m * Z) + 4 * Z + 4 ≤ W)
    (hf : ∀ t < m, c.nmem (F1b + t) ≤ 2 * Z) :
    ∃ c' k, Exec P W (lp 9956 9961 9977 9952 9972 9972 9930 bSx) c c' k ∧ k ≤ 11 * m + 10 ∧
      LpOut c c' (S + 12 + 16 * m + 4 + 6 * (m + 2 * n)) m
        (fun t => c.nmem (F1b + t) + m * Z - c.nmem (S + 12 + 6 * m + t)) :=
  lp_exec (P := P) c hc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      obtain ⟨c'', k, ex, hk, hP⟩ := lSx_exec (P := P) c' hw hW (bnd := 9930) (n := m)
        (X := F1b) (Y := S + 12 + 6 * m) (O := S + 12 + 16 * m + 4 + 6 * (m + 2 * n)) (K := m * Z)
        (by rw [g _ (by omega), R.r30]) (by unfold PfScr; omega) (by rw [a23, R.r56])
        (by rw [a24, R.r61]) (by rw [a25, R2.r77]) (by rw [a26, R.r52]) (by omega) (by omega)
        (by omega) (by omega)
        (fun t ht => by rw [hm']; have := hf t ht; omega)
        (fun t ht j hj => by omega) (fun t ht j hj => by omega)
      rw [hm'] at hP
      exact ⟨c'', k, ex, hk, hP⟩)

end Loops

end NcFz

end BKMNW

end PlanarFlow
