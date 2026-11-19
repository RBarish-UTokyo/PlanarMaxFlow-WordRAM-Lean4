module

public import PlanarFlow.BKMNW.NcFzE

/-!
# The pendant frame writer `pfP`: stages 3–4 in five blocks

`pfS3 = (DVr ; ZG) ; (RV'₀ ; RV'₁ ; RV'₂) ; (SG'₀ ; SG'₁ ; SG'₂)` and
`pfS4 = (CP'₀ ; CP'₁ ; CP'₂) ; (FL'₀ ; FL'₁ ; FL'₂)`: **`pf3a_exec`**, **`pf3b_exec`**,
**`pf3c_exec`**, **`pf4a_exec`**, **`pf4b_exec`**, each with its block of memory (`BlkOut`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcFz

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv

variable {P : Input} {W : ℕ}

/-- **A run writing only `[O, O + len)`** and the registers of the store loops. -/
structure BlkOut (c c' : Config) (O len : ℕ) : Prop where
  mem : ∀ a, (a < O ∨ O + len ≤ a) → c'.nmem a = c.nmem a
  reg : ∀ r, ¬ LpScr r → c'.nreg r = c.nreg r
  rr : c'.rreg = c.rreg
  rm : c'.rmem = c.rmem
  out : c'.output = c.output

section Blocks

variable {d m Z S F1b DFb CPb n : ℕ}

set_option maxHeartbeats 800000 in
/-- `DVr ; ZG`. -/
theorem pf3a_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (wS : S + 40 * m + 20 ≤ W) (wZ : 4 * (m * Z) + 4 * Z + 4 ≤ W)
    (hix : ∀ t < n, c.nmem (S + 12 + 12 * m + t) < m)
    (hdg : ∀ t < n, c.nmem (S + 12 + 9 * m + c.nmem (S + 12 + 12 * m + t)) ≤ m) :
    ∃ c' k, Exec P W (.seq (lp 9963 9967 9969 9988 9972 9972 9931 bG)
        (lp 9964 9967 9970 9951 9972 9972 9931 bG)) c c' k ∧ k ≤ 20 * n + 20 ∧
      (∀ t < n, c'.nmem (S + 12 + 14 * m + t) =
        c.nmem (S + 12 + 8 * m + c.nmem (S + 12 + 12 * m + t)) * 1) ∧
      (∀ t < n, c'.nmem (S + 12 + 15 * m + t) =
        c.nmem (S + 12 + 9 * m + c.nmem (S + 12 + 12 * m + t)) * Z) ∧
      BlkOut c c' (S + 12 + 14 * m) (m + m) := by
  obtain ⟨c₁, k₁, e₁, hk₁, L₁⟩ := pfDV_exec (P := P) c hc hW R R2 hnm wS hix
  have F1 : ∀ a, a < S + 12 + 14 * m → c₁.nmem a = c.nmem a := fun a ha =>
    L₁.mem a (Or.inl ha)
  obtain ⟨c₂, k₂, e₂, hk₂, L₂⟩ := pfZG_exec (P := P) c₁ e₁.wb_right hW (R.keepLp L₁.reg)
    (R2.keepLp L₁.reg) hnm wS wZ (fun t ht => by rw [F1 _ (by omega)]; exact hix t ht)
    (fun t ht => by
      have := hix t ht
      rw [F1 (S + 12 + 12 * m + t) (by omega), F1 _ (by omega)]; exact hdg t ht)
  refine ⟨c₂, k₁ + k₂, e₁.seq e₂, by omega, fun t ht => ?_, fun t ht => ?_,
    ⟨fun a ha => ?_, fun r hr => ?_, by rw [L₂.rr, L₁.rr], by rw [L₂.rm, L₁.rm],
      by rw [L₂.out, L₁.out]⟩⟩
  · rw [L₂.mem _ (Or.inl (by omega)), L₁.val t ht]
  · have := hix t ht
    rw [L₂.val t ht, F1 (S + 12 + 12 * m + t) (by omega), F1 _ (by omega)]
  · rw [L₂.mem _ (by omega), L₁.mem _ (by omega)]
  · rw [L₂.reg r hr, L₁.reg r hr]

set_option maxHeartbeats 800000 in
/-- `RV'₀ ; RV'₁ ; RV'₂`. -/
theorem pf3b_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (lfr : d + 4 + 7 * m ≤ S) (wS : S + 40 * m + 20 ≤ W) :
    ∃ c' k, Exec P W (.seq (lp 9953 9972 9974 9972 9972 9972 9930 bAk)
        (.seq (lp 9972 9972 9980 9978 9972 9972 9931 bId)
          (lp 9972 9972 9981 9930 9972 9972 9931 bId))) c c' k ∧ k ≤ 9 * m + 12 * n + 30 ∧
      (∀ t < m, c'.nmem (S + 12 + 16 * m + 4 + (m + 2 * n) + t) = c.nmem (d + 4 + m + t)) ∧
      (∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + (m + 2 * n) + m + t) = t + (m + n)) ∧
      (∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + (m + 2 * n) + (m + n) + t) = t + m) ∧
      BlkOut c c' (S + 12 + 16 * m + 4 + (m + 2 * n)) (m + 2 * n) := by
  obtain ⟨c₁, k₁, e₁, hk₁, L₁⟩ := pfRV0_exec (P := P) c hc hW R R2 hnm lfr wS
  obtain ⟨c₂, k₂, e₂, hk₂, L₂⟩ := pfRV1_exec (P := P) c₁ e₁.wb_right hW (R.keepLp L₁.reg)
    (R2.keepLp L₁.reg) hnm wS
  obtain ⟨c₃, k₃, e₃, hk₃, L₃⟩ := pfRV2_exec (P := P) c₂ e₂.wb_right hW
    ((R.keepLp L₁.reg).keepLp L₂.reg) ((R2.keepLp L₁.reg).keepLp L₂.reg) hnm wS
  refine ⟨c₃, k₁ + (k₂ + k₃), e₁.seq (e₂.seq e₃), by omega, fun t ht => ?_, fun t ht => ?_,
    fun t ht => ?_,
    ⟨fun a ha => ?_, fun r hr => ?_, by rw [L₃.rr, L₂.rr, L₁.rr], by rw [L₃.rm, L₂.rm, L₁.rm],
      by rw [L₃.out, L₂.out, L₁.out]⟩⟩
  · rw [L₃.mem _ (Or.inl (by omega)), L₂.mem _ (Or.inl (by omega)), L₁.val t ht]; simp
  · rw [L₃.mem _ (Or.inl (by omega)), L₂.val t ht]
  · rw [L₃.val t ht]
  · rw [L₃.mem _ (by omega), L₂.mem _ (by omega), L₁.mem _ (by omega)]
  · rw [L₃.reg r hr, L₂.reg r hr, L₁.reg r hr]

set_option maxHeartbeats 800000 in
/-- `SG'₀ ; SG'₁ ; SG'₂`. -/
theorem pf3c_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (lfr : d + 4 + 7 * m ≤ S) (wS : S + 40 * m + 20 ≤ W)
    (hlab : ∀ t < m, 1 ≤ c.nmem (S + 12 + 7 * m + t) ∧ c.nmem (S + 12 + 7 * m + t) ≤ m)
    (hsg : ∀ t < m, c.nmem (d + 4 + m + m + t) < m)
    (hci : ∀ t < m, c.nmem (S + 12 + 11 * m + (c.nmem (S + 12 + 7 * m + t) - 1)) ≤ m)
    (hix : ∀ t < n, c.nmem (S + 12 + 12 * m + t) < m) :
    ∃ c' k, Exec P W (.seq (lp 9962 9954 9975 9930 9972 9966 9930 bSg)
        (.seq (lp 9967 9972 9982 9972 9972 9972 9931 bAk)
          (lp 9972 9972 9983 9978 9972 9972 9931 bId))) c c' k ∧ k ≤ 20 * m + 15 * n + 30 ∧
      (∀ t < m, c'.nmem (S + 12 + 16 * m + 4 + 2 * (m + 2 * n) + t) =
        sgV (c.nmem (S + 12 + 7 * m + t)) (c.nmem (d + 4 + m + m + t)) m
          (c.nmem (S + 12 + 11 * m + (c.nmem (S + 12 + 7 * m + t) - 1)))) ∧
      (∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + 2 * (m + 2 * n) + m + t) =
        c.nmem (S + 12 + 12 * m + t)) ∧
      (∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + 2 * (m + 2 * n) + (m + n) + t) = t + (m + n)) ∧
      BlkOut c c' (S + 12 + 16 * m + 4 + 2 * (m + 2 * n)) (m + 2 * n) := by
  obtain ⟨c₁, k₁, e₁, hk₁, L₁⟩ := pfSG0_exec (P := P) c hc hW R R2 hnm lfr wS hlab hsg hci
  have F1 : ∀ a, a < S + 12 + 16 * m → c₁.nmem a = c.nmem a := fun a ha =>
    L₁.mem a (Or.inl (by omega))
  obtain ⟨c₂, k₂, e₂, hk₂, L₂⟩ := pfSG1_exec (P := P) c₁ e₁.wb_right hW (R.keepLp L₁.reg)
    (R2.keepLp L₁.reg) hnm wS (fun t ht => by rw [F1 _ (by omega)]; exact hix t ht)
  obtain ⟨c₃, k₃, e₃, hk₃, L₃⟩ := pfSG2_exec (P := P) c₂ e₂.wb_right hW
    ((R.keepLp L₁.reg).keepLp L₂.reg) ((R2.keepLp L₁.reg).keepLp L₂.reg) hnm wS
  refine ⟨c₃, k₁ + (k₂ + k₃), e₁.seq (e₂.seq e₃), by omega, fun t ht => ?_, fun t ht => ?_,
    fun t ht => ?_,
    ⟨fun a ha => ?_, fun r hr => ?_, by rw [L₃.rr, L₂.rr, L₁.rr], by rw [L₃.rm, L₂.rm, L₁.rm],
      by rw [L₃.out, L₂.out, L₁.out]⟩⟩
  · rw [L₃.mem _ (Or.inl (by omega)), L₂.mem _ (Or.inl (by omega)), L₁.val t ht]
  · rw [L₃.mem _ (Or.inl (by omega)), L₂.val t ht, F1 _ (by omega)]; simp
  · rw [L₃.val t ht]
  · rw [L₃.mem _ (by omega), L₂.mem _ (by omega), L₁.mem _ (by omega)]
  · rw [L₃.reg r hr, L₂.reg r hr, L₁.reg r hr]

set_option maxHeartbeats 800000 in
/-- `CP'₀ ; CP'₁ ; CP'₂`. -/
theorem pf4a_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (lC : CPb + m ≤ S) (wS : S + 40 * m + 20 ≤ W)
    (hq : ∀ t < m, c.nmem (S + 12 + 13 * m + t) ≤ 1) :
    ∃ c' k, Exec P W (.seq (lp 9955 9968 9976 9972 9972 9972 9930 bDf)
        (.seq (lp 9969 9970 9984 9972 9972 9972 9931 bSx)
          (lp 9970 9969 9985 9972 9972 9972 9931 bSx))) c c' k ∧ k ≤ 11 * m + 22 * n + 30 ∧
      (∀ t < m, c'.nmem (S + 12 + 16 * m + 4 + 3 * (m + 2 * n) + t) =
        c.nmem (CPb + t) - c.nmem (CPb + t) * c.nmem (S + 12 + 13 * m + t)) ∧
      (∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + 3 * (m + 2 * n) + m + t) =
        c.nmem (S + 12 + 14 * m + t) + 0 - c.nmem (S + 12 + 15 * m + t)) ∧
      (∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + 3 * (m + 2 * n) + (m + n) + t) =
        c.nmem (S + 12 + 15 * m + t) + 0 - c.nmem (S + 12 + 14 * m + t)) ∧
      BlkOut c c' (S + 12 + 16 * m + 4 + 3 * (m + 2 * n)) (m + 2 * n) := by
  obtain ⟨c₁, k₁, e₁, hk₁, L₁⟩ := pfCP0_exec (P := P) c hc hW R R2 hnm lC wS hq
  have F1 : ∀ a, a < S + 12 + 16 * m → c₁.nmem a = c.nmem a := fun a ha =>
    L₁.mem a (Or.inl (by omega))
  have R1 := R.keepLp L₁.reg
  have R21 := R2.keepLp L₁.reg
  obtain ⟨c₂, k₂, e₂, hk₂, L₂⟩ := pfSx_exec (P := P) c₁ e₁.wb_right hW R1 R21 hnm wS
    (xr := 9969) (yr := 9970) (or := 9984) (kr := 9972) (X := S + 12 + 14 * m)
    (Y := S + 12 + 15 * m) (O := S + 12 + 16 * m + 4 + 3 * (m + 2 * n) + m) (K := 0)
    R1.r69 R1.r70 R21.r84 R1.r72 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (fun t ht => by have := e₁.wb_right.2 (S + 12 + 14 * m + t); omega)
  have F2 : ∀ a, a < S + 12 + 16 * m → c₂.nmem a = c.nmem a := fun a ha => by
    rw [L₂.mem a (Or.inl (by omega)), F1 a ha]
  have R2' := R1.keepLp L₂.reg
  have R22 := R21.keepLp L₂.reg
  obtain ⟨c₃, k₃, e₃, hk₃, L₃⟩ := pfSx_exec (P := P) c₂ e₂.wb_right hW R2' R22 hnm wS
    (xr := 9970) (yr := 9969) (or := 9985) (kr := 9972) (X := S + 12 + 15 * m)
    (Y := S + 12 + 14 * m) (O := S + 12 + 16 * m + 4 + 3 * (m + 2 * n) + (m + n)) (K := 0)
    R2'.r70 R2'.r69 R22.r85 R2'.r72 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (fun t ht => by have := e₂.wb_right.2 (S + 12 + 15 * m + t); omega)
  refine ⟨c₃, k₁ + (k₂ + k₃), e₁.seq (e₂.seq e₃), by omega, fun t ht => ?_, fun t ht => ?_,
    fun t ht => ?_,
    ⟨fun a ha => ?_, fun r hr => ?_, by rw [L₃.rr, L₂.rr, L₁.rr], by rw [L₃.rm, L₂.rm, L₁.rm],
      by rw [L₃.out, L₂.out, L₁.out]⟩⟩
  · rw [L₃.mem _ (Or.inl (by omega)), L₂.mem _ (Or.inl (by omega)), L₁.val t ht]
  · rw [L₃.mem _ (Or.inl (by omega)), L₂.val t ht, F1 _ (by omega), F1 _ (by omega)]
  · rw [L₃.val t ht, F2 _ (by omega), F2 _ (by omega)]
  · rw [L₃.mem _ (by omega), L₂.mem _ (by omega), L₁.mem _ (by omega)]
  · rw [L₃.reg r hr, L₂.reg r hr, L₁.reg r hr]

set_option maxHeartbeats 800000 in
/-- `FL'₀ ; FL'₁ ; FL'₂`. -/
theorem pf4b_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    (R : Rg1 c d m Z S F1b DFb CPb) (R2 : Rg2 c m n (S + 12 + 16 * m)) (hnm : n ≤ m)
    (lF : F1b + m ≤ S) (wS : S + 40 * m + 20 ≤ W) (wZ : 4 * (m * Z) + 4 * Z + 4 ≤ W)
    (hf : ∀ t < m, c.nmem (F1b + t) ≤ 2 * Z)
    (hdv : ∀ t < n, c.nmem (S + 12 + 14 * m + t) ≤ 2 * (m * Z))
    (hzg : ∀ t < n, c.nmem (S + 12 + 15 * m + t) ≤ m * Z) :
    ∃ c' k, Exec P W (.seq (lp 9956 9961 9977 9952 9972 9972 9930 bSx)
        (.seq (lp 9969 9970 9986 9952 9972 9972 9931 bSx)
          (lp 9970 9969 9987 9952 9972 9972 9931 bSx))) c c' k ∧ k ≤ 11 * m + 22 * n + 30 ∧
      (∀ t < m, c'.nmem (S + 12 + 16 * m + 4 + 6 * (m + 2 * n) + t) =
        c.nmem (F1b + t) + m * Z - c.nmem (S + 12 + 6 * m + t)) ∧
      (∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + 6 * (m + 2 * n) + m + t) =
        c.nmem (S + 12 + 14 * m + t) + m * Z - c.nmem (S + 12 + 15 * m + t)) ∧
      (∀ t < n, c'.nmem (S + 12 + 16 * m + 4 + 6 * (m + 2 * n) + (m + n) + t) =
        c.nmem (S + 12 + 15 * m + t) + m * Z - c.nmem (S + 12 + 14 * m + t)) ∧
      BlkOut c c' (S + 12 + 16 * m + 4 + 6 * (m + 2 * n)) (m + 2 * n) := by
  obtain ⟨c₁, k₁, e₁, hk₁, L₁⟩ := pfFL0_exec (P := P) c hc hW R R2 hnm lF wS wZ hf
  have F1 : ∀ a, a < S + 12 + 16 * m → c₁.nmem a = c.nmem a := fun a ha =>
    L₁.mem a (Or.inl (by omega))
  have R1 := R.keepLp L₁.reg
  have R21 := R2.keepLp L₁.reg
  obtain ⟨c₂, k₂, e₂, hk₂, L₂⟩ := pfSx_exec (P := P) c₁ e₁.wb_right hW R1 R21 hnm wS
    (xr := 9969) (yr := 9970) (or := 9986) (kr := 9952) (X := S + 12 + 14 * m)
    (Y := S + 12 + 15 * m) (O := S + 12 + 16 * m + 4 + 6 * (m + 2 * n) + m) (K := m * Z)
    R1.r69 R1.r70 R21.r86 R1.r52 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (fun t ht => by rw [F1 _ (by omega)]; have := hdv t ht; omega)
  have F2 : ∀ a, a < S + 12 + 16 * m → c₂.nmem a = c.nmem a := fun a ha => by
    rw [L₂.mem a (Or.inl (by omega)), F1 a ha]
  have R2' := R1.keepLp L₂.reg
  have R22 := R21.keepLp L₂.reg
  obtain ⟨c₃, k₃, e₃, hk₃, L₃⟩ := pfSx_exec (P := P) c₂ e₂.wb_right hW R2' R22 hnm wS
    (xr := 9970) (yr := 9969) (or := 9987) (kr := 9952) (X := S + 12 + 15 * m)
    (Y := S + 12 + 14 * m) (O := S + 12 + 16 * m + 4 + 6 * (m + 2 * n) + (m + n)) (K := m * Z)
    R2'.r70 R2'.r69 R22.r87 R2'.r52 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (fun t ht => by rw [F2 _ (by omega)]; have := hzg t ht; omega)
  refine ⟨c₃, k₁ + (k₂ + k₃), e₁.seq (e₂.seq e₃), by omega, fun t ht => ?_, fun t ht => ?_,
    fun t ht => ?_,
    ⟨fun a ha => ?_, fun r hr => ?_, by rw [L₃.rr, L₂.rr, L₁.rr], by rw [L₃.rm, L₂.rm, L₁.rm],
      by rw [L₃.out, L₂.out, L₁.out]⟩⟩
  · rw [L₃.mem _ (Or.inl (by omega)), L₂.mem _ (Or.inl (by omega)), L₁.val t ht]
  · rw [L₃.mem _ (Or.inl (by omega)), L₂.val t ht, F1 _ (by omega), F1 _ (by omega)]
  · rw [L₃.val t ht, F2 _ (by omega), F2 _ (by omega)]
  · rw [L₃.mem _ (by omega), L₂.mem _ (by omega), L₁.mem _ (by omega)]
  · rw [L₃.reg r hr, L₂.reg r hr, L₁.reg r hr]

end Blocks

end NcFz

end BKMNW

end PlanarFlow
