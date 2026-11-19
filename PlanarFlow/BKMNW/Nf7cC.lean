module

public import PlanarFlow.BKMNW.Nf7cB

/-!
# Step 2 of `fixP`: the sorted arc indices and the registers of the loop

**`st2c = p7cD ; fiO ; fiS ; p7cE`** and **`st2c_exec`**: `fiO ; fiS` (the counting sort of
the explicit arcs by tail) with scratch base `S1`, leaving the sorted indices
`MsCall.sIdx ET (2k) b e` at `lySI S1 b k + e`, then the registers of `SLx.Regs` that are not
yet set (`p7cE`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The sorted arc indices and the registers of the loop. -/
def st2c : Stmt := .seq p7cD (.seq MsCall.fiO (.seq MsCall.fiS p7cE))

/-- The registers written by `st2c`. -/
def st2cScr (r : ℕ) : Prop :=
  (1500 ≤ r ∧ r ≤ 1520) ∨ r = 7861 ∨ r = 7865 ∨ (7873 ≤ r ∧ r ≤ 7875) ∨ r = 8111 ∨
    r = 8112 ∨ r = 8141 ∨ r = 8142 ∨ (9501 ≤ r ∧ r ≤ 9504) ∨ (9360 ≤ r ∧ r ≤ 9362) ∨
    r = 8113 ∨ r = 8124 ∨ r = 8125 ∨ r = 8115 ∨ r = 9476 ∨ (7614 ≤ r ∧ r ≤ 7616)

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The sorted arc indices and the registers of the loop.** -/
theorem st2c_exec (c : Config) (hc : WordsBounded W c) {S1 b k ETb K Mo : ℕ} {ET : ℕ → ℕ}
    (r60 : c.nreg 9460 = S1) (r00 : c.nreg 8100 = b) (r04 : c.nreg 8104 = 2 * k)
    (r05 : c.nreg 8105 = ETb) (r10 : c.nreg 9310 = K) (r7610 : c.nreg 7610 = Mo) (hMo : 0 < Mo)
    (het : ∀ a < 2 * k, c.nmem (ETb + a) = ET a) (hlt : ∀ a < 2 * k, ET a < b)
    (hET : ETb + 2 * k ≤ S1) (hW : S1 + lyT b k ≤ W) :
    ∃ c' t, Exec P W st2c c c' t ∧ t ≤ 70 * k + 32 * b + 70 ∧
      (∀ e < 2 * k, c'.nmem (lySI S1 b k + e) = MsCall.sIdx ET (2 * k) b e) ∧
      (∀ a, (a < S1 ∨ S1 + lyT b k ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.nreg 9501 = c.nreg 9416 ∧ c'.nreg 9502 = c.nreg 9412 ∧ c'.nreg 9503 = c.nreg 9413 ∧
      c'.nreg 9504 = c.nreg 9414 ∧ c'.nreg 9360 = c.nreg 7612 ∧ c'.nreg 9361 = c.nreg 9474 ∧
      c'.nreg 8113 = c.nreg 9461 ∧ c'.nreg 8124 = Mo ∧ c'.nreg 8125 = Mo - K % Mo ∧
      c'.nreg 8112 = 1 ∧ c'.nreg 8115 = c.nreg 7605 ∧ c'.nreg 9362 = c.nreg 9470 ∧
      c'.nreg 7614 = c.nreg 9468 ∧ c'.nreg 7615 = c.nreg 9469 ∧ c'.nreg 7616 = c.nreg 9471 ∧
      (∀ r, ¬ st2cScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hT : lyT b k = 4 * k + 4 * b + 2 := rfl
  have hW1 : 1 ≤ W := by omega
  obtain ⟨c₁, t₁, e₁, ht₁, a11, a12, ak, am, ar, arm, ao⟩ := p7cD_exec (P := P) c hc hW1
  obtain ⟨c₂, t₂, e₂, ht₂, b1, bk, bn, br, brm, bo⟩ :=
    MsCall.fiO_exec (P := P) c₁ e₁.wb_right (S := S1) (mE := 2 * k)
      (by rw [ak _ (by omega) (by omega), r04]) (by rw [a11, r60]) (by omega)
  have q00 : c₂.nreg 8100 = b := by rw [bn _ (by omega) (by omega) (by omega),
    ak _ (by omega) (by omega), r00]
  obtain ⟨c₃, t₃, e₃, ht₃, d41, d42, dOB, dSI, dk, dn, dr, drm, dO⟩ :=
    MsCall.fiS_exec (P := P) c₂ e₂.wb_right (ET := ET) q00
      (by rw [bn _ (by omega) (by omega) (by omega), ak _ (by omega) (by omega), r04])
      (by rw [bn _ (by omega) (by omega) (by omega), ak _ (by omega) (by omega), r05])
      (by rw [bn _ (by omega) (by omega) (by omega), a11, r60])
      (by rw [bn _ (by omega) (by omega) (by omega), a12])
      (fun a ha => by rw [bk _ (Or.inl (by omega)), am]; exact het a ha) b1 hlt hET (by omega)
  have hlen := MsCall.length_pre_fiL_b hlt
  obtain ⟨c₄, t₄, e₄, ht₄, f01, f02, f03, f04, f60, f61, f13, f24, f25, f12, f15, f62, f714,
      f715, f716, fk, fm, fr, frm, fo⟩ :=
    p7cE_exec (P := P) c₃ e₃.wb_right (K := K) (Mo := Mo)
      (by rw [dn _ (by omega) (by omega) (by omega), bn _ (by omega) (by omega) (by omega),
        ak _ (by omega) (by omega), r10])
      (by rw [dn _ (by omega) (by omega) (by omega), bn _ (by omega) (by omega) (by omega),
        ak _ (by omega) (by omega), r7610]) hMo hW1
  -- the registers kept by `p7cD ; fiO ; fiS`
  have k3 : ∀ r, (r < 1500 ∨ 1520 < r) → r ≠ 8141 → r ≠ 8142 → r ≠ 7861 → r ≠ 7865 →
      (r < 7873 ∨ 7876 ≤ r) → r ≠ 8111 → r ≠ 8112 → c₃.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 h5 h6 h7 h8 => by rw [dn r h1 h2 h3, bn r h4 h5 h6, ak r h7 h8]
  have ht3 : t₃ ≤ 29 * (2 * k) + 32 * b + 26 + 12 := ht₃
  refine ⟨c₄, _, e₁.seq (e₂.seq (e₃.seq e₄)), by omega, fun e he => ?_, fun a ha => ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, f24, f25, f12, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [fr, dr, br, ar],
    by rw [frm, drm, brm, arm], by rw [fo, dO, bo, ao]⟩
  · have := dSI e (by rw [hlen]; exact he)
    have e1 : lySI S1 b k + e = S1 + 2 * k + b + 1 + b + b + b + e := by
      simp only [lySI]; omega
    rw [fm, e1, this]
    rfl
  · rw [fm, dk a (by omega), bk a (by omega), am]
  all_goals try first
    | (rw [f01]; exact k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))
    | (rw [f02]; exact k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))
    | (rw [f03]; exact k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))
    | (rw [f04]; exact k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))
    | (rw [f60]; exact k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))
    | (rw [f61]; exact k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))
    | (rw [f13]; exact k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))
    | (rw [f15]; exact k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))
    | (rw [f62]; exact k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))
    | (rw [f714]; exact k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))
    | (rw [f715]; exact k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))
    | (rw [f716]; exact k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))
  · simp only [st2cScr, not_or, not_and, not_le] at hr
    rw [fk r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]
    exact k3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)

end BKMNW

end PlanarFlow
