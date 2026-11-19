module

public import PlanarFlow.BKMNW.SgS

/-!
# The parts of the separator on the machine (`SegsOut` of `sepL`), programs and blocks

From the path's darts `PD` (`PD[j] = i + 1` on the core's indices `i`, `j ≤ ρ.k`, then `0`; `n'`
cells), the core's enumeration through the record `IX` (`IX[i]` a record index), the record's
hole labels `HP` (`n` cells) and the frame's darts through the record `FX` (`m` cells),
**`sgProg`** writes the parts of the separator (`SegsOut`) from `Gb`:

1. `lkProg` on `PD` (`k + 1 = #{j : PD[j] ≠ 0}`), `k := r6306 - 1`;
2. `HF[j] = HP[IX[PD[j] - 1]]` (the hole label of the `j`-th vertex of the path), `j < n'`;
3. `invProg` of `FX` (`FXI[FX[f]] = f`);
4. `rnProg` on `HF` (the runs off the holes as pairs `(a, e)` at `Ob`, `s` of them);
5. `Gb := s`, a loop writing the offsets `Σ_{j' < j} (e' - a')` at `Gb + 1 + j` and the lengths
   `e - a` at `Gb + 1 + s + j`;
6. `RF[t] = [HF[t] = 0] · [HF[t + 1] = 0]` (`t < k`; the darts of the runs), `lkProg` on `RF`;
7. the darts: `Gb + 1 + 2 s + q := FXI[IX[PD[IX2[q]] - 1]]` (`q < cnt RF k`), `r6502 := Gb`.

Registers: inputs `7200 = n'`, `7201 = PDb`, `7202 = IXb`, `7203 = HPb`, `7204 = m`,
`7205 = FXb`, `7206 = Z` (scratch), `7207 = Gb`, `7208 = n`, `6521 = 1`; written `7210 … 7228`,
`6300 … 6309`, `6502`, `6520`, `6522 … 6529`, `4100 … 4113`, `4600 … 4605`.
Scratch from `Z`: `CI1 | IX1 | HF` (`n'` each) `| FXI` (`n`) `| Ob` (`2 n' + 1`) `| RF | CI2 | IX2`
(`n'` each): `[Z, Z + 8 n' + n + 1)`.

This file: the programs, the value blocks and the straight-line blocks with their exec lemmas,
the set-up registers `SgRegs`, and the loop of step 5 (`sgL_exec`).
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

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The set-up: the bases of the scratch and the registers of the first compaction. -/
def sqA : Stmt :=
  block [.addN 7210 7206 7200, .addN 7211 7210 7200, .addN 7212 7211 7200, .addN 7213 7212 7208,
    .addN 7214 7213 7200, .addN 7214 7214 7200, .addN 7214 7214 6521, .addN 7215 7214 7200,
    .addN 7216 7215 7200, .copyN 6300 7200, .copyN 6301 7201, .copyN 6302 7206,
    .copyN 6303 7210]

/-- `k := r6306 - 1` and the registers of the inverse of `FX`. -/
def sqB : Stmt := block [.subN 7219 6306 6521, .copyN 4600 7204, .copyN 4601 7205, .copyN 4602 7212]

/-- The registers of the runs. -/
def sqC : Stmt := block [.copyN 4100 7219, .copyN 4101 7211, .copyN 4102 7213]

/-- `s := r4108`, `Gb := s`, the registers of the loop. -/
def sqD : Stmt :=
  block [.copyN 7220 4108, .storeN 7207 7220, .constN 7221 0, .constN 7222 0,
    .addN 7223 7207 6521, .addN 7224 7223 7220]

/-- One run: its offset and its length. -/
def sgBody : Stmt :=
  block [.addN 7225 7221 7221, .addN 7226 7213 7225, .loadN 7227 7226, .addN 7226 7226 6521,
    .loadN 7228 7226, .subN 7228 7228 7227, .addN 7226 7223 7221, .storeN 7226 7222,
    .addN 7226 7224 7221, .storeN 7226 7228, .addN 7222 7222 7228, .addN 7221 7221 6521]

/-- **The offsets and the lengths of the runs.** -/
def sgL : Stmt := .whileLtN 7221 7220 sgBody

/-- The registers of the second compaction. -/
def sqE : Stmt := block [.copyN 6300 7219, .copyN 6301 7214, .copyN 6302 7215, .copyN 6303 7216]

/-- The base of the darts, their number, `r6502 := Gb`. -/
def sqF : Stmt := block [.addN 7217 7224 7220, .copyN 7218 6306, .copyN 6502 7207, .addN 7229 7217 7222]

/-- `HF[j] = HP[IX[PD[j] - 1]]`. -/
def vbSHF : Stmt :=
  block [.addN 6524 7201 6520, .loadN 6524 6524, .subN 6524 6524 6521, .addN 6524 7202 6524,
    .loadN 6524 6524, .addN 6524 7203 6524, .loadN 6523 6524]

/-- The value of `vbSRF`: `1` iff both labels are `0`. -/
def rfV (u v : ℕ) : ℕ := (1 - u / u) * (1 - v / v)

/-- `RF[t] = [HF[t] = 0] · [HF[t + 1] = 0]`. -/
def vbSRF : Stmt :=
  block [.addN 6524 7211 6520, .loadN 6525 6524, .addN 6524 6524 6521, .loadN 6526 6524,
    .divN 6525 6525 6525, .subN 6525 6521 6525, .divN 6526 6526 6526, .subN 6526 6521 6526,
    .mulN 6523 6525 6526]

/-- The frame index of the dart `IX2[q]` of the path: `FXI[IX[PD[IX2[q]] - 1]]`. -/
def vbSDT : Stmt :=
  block [.addN 6524 7216 6520, .loadN 6524 6524, .addN 6524 7201 6524, .loadN 6524 6524,
    .subN 6524 6524 6521, .addN 6524 7202 6524, .loadN 6524 6524, .addN 6524 7212 6524,
    .loadN 6523 6524]

/-- The start vertex of the run `j` as a frame index: `FXI[IX[PD[Ob[2 j]] - 1]]`. -/
def vbSPV : Stmt :=
  block [.addN 6524 6520 6520, .addN 6524 7213 6524, .loadN 6524 6524, .addN 6524 7201 6524,
    .loadN 6524 6524, .subN 6524 6524 6521, .addN 6524 7202 6524, .loadN 6524 6524,
    .addN 6524 7212 6524, .loadN 6523 6524]

/-- Steps 1–3: `k`, the hole labels of the path's vertices, the inverse of `FX`. -/
def sgP1 : Stmt := .seq sqA (.seq lkProg (.seq sqB (.seq (mapRunS vbSHF 7200 7211) invProg)))

/-- Steps 4–5: the runs, their offsets and lengths. -/
def sgP2 : Stmt := .seq sqC (.seq rnProg (.seq sqD sgL))

/-- Steps 6–8: the darts of the runs, then their start vertices. -/
def sgP3 : Stmt :=
  .seq (mapRunS vbSRF 7219 7214) (.seq sqE (.seq lkProg (.seq sqF
    (.seq (mapRunS vbSDT 7218 7217) (mapRunS vbSPV 7220 7229)))))

/-- **The parts of the separator** (see the module docstring). -/
def sgProg : Stmt := .seq sgP1 (.seq sgP2 sgP3)

lemma sg_nz_le (x : ℕ) : x / x ≤ 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | h
  · simp
  · rw [Nat.div_self h]

lemma rfV_le (u v : ℕ) : rfV u v ≤ 1 := by
  unfold rfV
  rcases Nat.eq_zero_or_pos u with rfl | hu <;> rcases Nat.eq_zero_or_pos v with rfl | hv <;>
    simp_all [Nat.div_self]

lemma rfV_pos (u v : ℕ) : 0 < rfV u v ↔ u = 0 ∧ v = 0 := by
  unfold rfV
  rcases Nat.eq_zero_or_pos u with rfl | hu <;> rcases Nat.eq_zero_or_pos v with rfl | hv <;>
    simp_all [Nat.div_self] <;> omega

/-- The registers after the set-up. -/
structure SgRegs (c : Config) (n' PDb IXb HPb m FXb Z Gb n : ℕ) : Prop where
  r00 : c.nreg 7200 = n'
  r01 : c.nreg 7201 = PDb
  r02 : c.nreg 7202 = IXb
  r03 : c.nreg 7203 = HPb
  r04 : c.nreg 7204 = m
  r05 : c.nreg 7205 = FXb
  r06 : c.nreg 7206 = Z
  r07 : c.nreg 7207 = Gb
  r08 : c.nreg 7208 = n
  r21 : c.nreg 6521 = 1
  r10 : c.nreg 7210 = Z + n'
  r11 : c.nreg 7211 = Z + 2 * n'
  r12 : c.nreg 7212 = Z + 3 * n'
  r13 : c.nreg 7213 = Z + 3 * n' + n
  r14 : c.nreg 7214 = Z + 5 * n' + n + 1
  r15 : c.nreg 7215 = Z + 6 * n' + n + 1
  r16 : c.nreg 7216 = Z + 7 * n' + n + 1

/-- The registers `SgRegs` reads. -/
def sgReg (x : ℕ) : Prop := (7200 ≤ x ∧ x ≤ 7216 ∧ x ≠ 7209) ∨ x = 6521

lemma SgRegs.congr {c c' : Config} {n' PDb IXb HPb m FXb Z Gb n : ℕ}
    (h : SgRegs c n' PDb IXb HPb m FXb Z Gb n) (e : ∀ x, sgReg x → c'.nreg x = c.nreg x) :
    SgRegs c' n' PDb IXb HPb m FXb Z Gb n := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rwa [e _ (by unfold sgReg; omega)]

section Exec

variable {P : Input} {W : ℕ}

theorem sqA_exec (c : Config) (hc : WordsBounded W c) {n' PDb IXb HPb m FXb Z Gb n : ℕ}
    (r00 : c.nreg 7200 = n') (r01 : c.nreg 7201 = PDb) (r02 : c.nreg 7202 = IXb)
    (r03 : c.nreg 7203 = HPb) (r04 : c.nreg 7204 = m) (r05 : c.nreg 7205 = FXb)
    (r06 : c.nreg 7206 = Z) (r07 : c.nreg 7207 = Gb) (r08 : c.nreg 7208 = n)
    (r21 : c.nreg 6521 = 1) (w : Z + 8 * n' + n + 1 ≤ W) :
    ∃ c' t, Exec P W sqA c c' t ∧ t = 13 ∧ SgRegs c' n' PDb IXb HPb m FXb Z Gb n ∧
      c'.nreg 6300 = n' ∧ c'.nreg 6301 = PDb ∧ c'.nreg 6302 = Z ∧ c'.nreg 6303 = Z + n' ∧
      c'.nmem = c.nmem ∧
      (∀ x, (x < 6300 ∨ (6303 < x ∧ x < 7210) ∨ 7216 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sqA
  exec_block
  all_goals try (config_simp; (try simp only [r00, r01, r06, r08, r21]); omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
    ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r00, r01, r02, r03, r04, r05, r06, r07, r08, r21]); done)
  all_goals try (config_simp; (try simp only [r00, r01, r02, r03, r04, r05, r06, r07, r08, r21]); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other])

theorem sqB_exec (c : Config) (hc : WordsBounded W c) {kk m FXb FXIb : ℕ}
    (r06 : c.nreg 6306 = kk) (r21 : c.nreg 6521 = 1) (r04 : c.nreg 7204 = m)
    (r05 : c.nreg 7205 = FXb) (r12 : c.nreg 7212 = FXIb) :
    ∃ c' t, Exec P W sqB c c' t ∧ t = 4 ∧ c'.nreg 7219 = kk - 1 ∧ c'.nreg 4600 = m ∧
      c'.nreg 4601 = FXb ∧ c'.nreg 4602 = FXIb ∧ c'.nmem = c.nmem ∧
      (∀ x, x ≠ 7219 → (x < 4600 ∨ 4602 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sqB
  exec_block
  all_goals try (config_simp; (try simp only [r06, r21]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp (disch := omega) only [upd_other, upd_same, r06, r21, r04, r05, r12]

theorem sqC_exec (c : Config) (hc : WordsBounded W c) {k HFb Ob : ℕ}
    (r19 : c.nreg 7219 = k) (r11 : c.nreg 7211 = HFb) (r13 : c.nreg 7213 = Ob) :
    ∃ c' t, Exec P W sqC c c' t ∧ t = 3 ∧ c'.nreg 4100 = k ∧ c'.nreg 4101 = HFb ∧
      c'.nreg 4102 = Ob ∧ c'.nmem = c.nmem ∧
      (∀ x, (x < 4100 ∨ 4102 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sqC
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp (disch := omega) only [upd_other, upd_same, r19, r11, r13]

theorem sqD_exec (c : Config) (hc : WordsBounded W c) {s Gb : ℕ}
    (r08 : c.nreg 4108 = s) (r07 : c.nreg 7207 = Gb) (r21 : c.nreg 6521 = 1)
    (w : Gb + 1 + s ≤ W) :
    ∃ c' t, Exec P W sqD c c' t ∧ t = 6 ∧ c'.nreg 7220 = s ∧ c'.nreg 7221 = 0 ∧
      c'.nreg 7222 = 0 ∧ c'.nreg 7223 = Gb + 1 ∧ c'.nreg 7224 = Gb + 1 + s ∧
      c'.nmem = upd c.nmem Gb s ∧
      (∀ x, (x < 7220 ∨ 7224 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sqD
  exec_block
  all_goals try (config_simp; (try simp only [r08, r07, r21]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp (disch := omega) only [upd_other, upd_same, r08, r07, r21]

theorem sqE_exec (c : Config) (hc : WordsBounded W c) {k RFb CIb IXb : ℕ}
    (r19 : c.nreg 7219 = k) (r14 : c.nreg 7214 = RFb) (r15 : c.nreg 7215 = CIb)
    (r16 : c.nreg 7216 = IXb) :
    ∃ c' t, Exec P W sqE c c' t ∧ t = 4 ∧ c'.nreg 6300 = k ∧ c'.nreg 6301 = RFb ∧
      c'.nreg 6302 = CIb ∧ c'.nreg 6303 = IXb ∧ c'.nmem = c.nmem ∧
      (∀ x, (x < 6300 ∨ 6303 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sqE
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp (disch := omega) only [upd_other, upd_same, r19, r14, r15, r16]

theorem sqF_exec (c : Config) (hc : WordsBounded W c) {b s tot Gb L : ℕ}
    (r24 : c.nreg 7224 = b) (r20 : c.nreg 7220 = s) (r06 : c.nreg 6306 = tot)
    (r07 : c.nreg 7207 = Gb) (r22 : c.nreg 7222 = L) (w : b + s + L ≤ W) :
    ∃ c' t, Exec P W sqF c c' t ∧ t = 4 ∧ c'.nreg 7217 = b + s ∧ c'.nreg 7218 = tot ∧
      c'.nreg 6502 = Gb ∧ c'.nreg 7229 = b + s + L ∧ c'.nmem = c.nmem ∧
      (∀ x, x ≠ 7217 → x ≠ 7218 → x ≠ 6502 → x ≠ 7229 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sqF
  exec_block
  all_goals try (config_simp; (try simp only [r24, r20, r22]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, fun x h1 h2 h3 h4 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp (disch := omega) only [upd_other, upd_same, r24, r20, r06, r07, r22]

theorem vbSHF_exec (c : Config) (hc : WordsBounded W c) {j PDb IXb HPb p x h : ℕ}
    (r20 : c.nreg 6520 = j) (r01 : c.nreg 7201 = PDb) (r02 : c.nreg 7202 = IXb)
    (r03 : c.nreg 7203 = HPb) (r21 : c.nreg 6521 = 1)
    (hp : c.nmem (PDb + j) = p) (hx : c.nmem (IXb + (p - 1)) = x) (hh : c.nmem (HPb + x) = h)
    (w1 : PDb + j ≤ W) (w2 : IXb + (p - 1) ≤ W) (w3 : HPb + x ≤ W) :
    ∃ c' k, Exec P W vbSHF c c' k ∧ k ≤ 7 ∧ c'.nreg 6523 = h ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold vbSHF
  exec_block
  all_goals try (config_simp; (try simp only [r20, r01, r02, r03, r21, hp, hx, hh]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r01, r02, r03, r21, hp, hx, hh]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbSRF_exec (c : Config) (hc : WordsBounded W c) {t HFb u v : ℕ}
    (r20 : c.nreg 6520 = t) (r11 : c.nreg 7211 = HFb) (r21 : c.nreg 6521 = 1)
    (hu : c.nmem (HFb + t) = u) (hv : c.nmem (HFb + t + 1) = v) (w1 : HFb + t + 1 ≤ W) :
    ∃ c' k, Exec P W vbSRF c c' k ∧ k ≤ 9 ∧ c'.nreg 6523 = rfV u v ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b1 := sg_nz_le u
  have b2 := sg_nz_le v
  have m1 : (1 - u / u) * (1 - v / v) ≤ W := by
    have := rfV_le u v; unfold rfV at this; have := hc.1 6521; omega
  unfold vbSRF
  exec_block
  all_goals try (config_simp; (try simp only [r20, r11, r21, hu, hv]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · have hv' : c.nmem (HFb + (t + 1)) = v := by rw [← Nat.add_assoc]; exact hv
    config_simp; simp only [r20, r11, r21, hu, hv, hv', rfV]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbSDT_exec (c : Config) (hc : WordsBounded W c) {q IX2b PDb IXb FXIb t p x f : ℕ}
    (r20 : c.nreg 6520 = q) (r16 : c.nreg 7216 = IX2b) (r01 : c.nreg 7201 = PDb)
    (r02 : c.nreg 7202 = IXb) (r12 : c.nreg 7212 = FXIb) (r21 : c.nreg 6521 = 1)
    (hq : c.nmem (IX2b + q) = t) (hp : c.nmem (PDb + t) = p) (hx : c.nmem (IXb + (p - 1)) = x)
    (hf : c.nmem (FXIb + x) = f)
    (w1 : IX2b + q ≤ W) (w2 : PDb + t ≤ W) (w3 : IXb + (p - 1) ≤ W) (w4 : FXIb + x ≤ W) :
    ∃ c' k, Exec P W vbSDT c c' k ∧ k ≤ 9 ∧ c'.nreg 6523 = f ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold vbSDT
  exec_block
  all_goals try (config_simp; (try simp only [r20, r16, r01, r02, r12, r21, hq, hp, hx, hf]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r16, r01, r02, r12, r21, hq, hp, hx, hf]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbSPV_exec (c : Config) (hc : WordsBounded W c) {j Ob PDb IXb FXIb a p x f : ℕ}
    (r20 : c.nreg 6520 = j) (r13 : c.nreg 7213 = Ob) (r01 : c.nreg 7201 = PDb)
    (r02 : c.nreg 7202 = IXb) (r12 : c.nreg 7212 = FXIb) (r21 : c.nreg 6521 = 1)
    (ha : c.nmem (Ob + 2 * j) = a) (hp : c.nmem (PDb + a) = p) (hx : c.nmem (IXb + (p - 1)) = x)
    (hf : c.nmem (FXIb + x) = f)
    (w1 : Ob + 2 * j ≤ W) (w2 : PDb + a ≤ W) (w3 : IXb + (p - 1) ≤ W) (w4 : FXIb + x ≤ W) :
    ∃ c' k, Exec P W vbSPV c c' k ∧ k ≤ 10 ∧ c'.nreg 6523 = f ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ha' : c.nmem (Ob + (j + j)) = a := by rw [← two_mul]; exact ha
  unfold vbSPV
  exec_block
  all_goals try (config_simp; (try simp only [r20, r13, r01, r02, r12, r21, ha', hp, hx, hf]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r13, r01, r02, r12, r21, ha', hp, hx, hf]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

/-- The offset of the run `j`: the lengths of the runs before it. -/
def sgOff (R : List (ℕ × ℕ)) (j : ℕ) : ℕ := ((R.take j).map fun p => p.2 - p.1).sum

/-- The length of the run `j`. -/
def sgLen (R : List (ℕ × ℕ)) (j : ℕ) : ℕ := (R.getD j (0, 0)).2 - (R.getD j (0, 0)).1

lemma sgOff_succ {R : List (ℕ × ℕ)} {j : ℕ} (hj : j < R.length) :
    sgOff R (j + 1) = sgOff R j + sgLen R j := by
  unfold sgOff sgLen
  have e : R.take (j + 1) = R.take j ++ [R[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  rw [e, List.map_append, List.sum_append, List.getD_eq_getElem _ _ hj]
  simp

lemma sgOff_le (R : List (ℕ × ℕ)) (j : ℕ) : sgOff R j ≤ (R.map fun p => p.2 - p.1).sum := by
  unfold sgOff
  conv_rhs => rw [← List.take_append_drop j R]
  rw [List.map_append, List.sum_append]; omega

lemma sgOff_zero (R : List (ℕ × ℕ)) : sgOff R 0 = 0 := by simp [sgOff]

theorem sgBody_exec (c : Config) (hc : WordsBounded W c) {j s Ob Gb o a e : ℕ}
    (q21 : c.nreg 7221 = j) (q22 : c.nreg 7222 = o) (q13 : c.nreg 7213 = Ob)
    (q23 : c.nreg 7223 = Gb + 1) (q24 : c.nreg 7224 = Gb + 1 + s) (one : c.nreg 6521 = 1)
    (ha : c.nmem (Ob + 2 * j) = a) (he : c.nmem (Ob + 2 * j + 1) = e)
    (w1 : Ob + 2 * j + 1 ≤ W) (w2 : Gb + 1 + s + j ≤ W) (w3 : o + (e - a) ≤ W)
    (w4 : j + 1 ≤ W) :
    ∃ c' t, Exec P W sgBody c c' t ∧ t = 12 ∧ c'.nreg 7221 = j + 1 ∧
      c'.nreg 7222 = o + (e - a) ∧
      c'.nmem = upd (upd c.nmem (Gb + 1 + j) o) (Gb + 1 + s + j) (e - a) ∧
      (∀ x, (x < 7221 ∨ x = 7223 ∨ x = 7224 ∨ 7228 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ha' : c.nmem (Ob + (j + j)) = a := by rw [← two_mul]; exact ha
  have he' : c.nmem (Ob + (j + j) + 1) = e := by rw [← two_mul]; exact he
  unfold sgBody
  exec_block
  all_goals try (config_simp; (try simp only [q21, q22, q13, q23, q24, one, ha', he']); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp (disch := omega) only [upd_other, upd_same, q21, q22, q13, q23, q24, one, ha',
    he']

set_option maxHeartbeats 1000000 in
/-- **The offsets and the lengths of the runs** (step 5). -/
theorem sgL_exec (c : Config) (hc : WordsBounded W c) {s Ob Gb : ℕ} (R : List (ℕ × ℕ))
    (q20 : c.nreg 7220 = s) (q21 : c.nreg 7221 = 0) (q22 : c.nreg 7222 = 0)
    (q13 : c.nreg 7213 = Ob) (q23 : c.nreg 7223 = Gb + 1) (q24 : c.nreg 7224 = Gb + 1 + s)
    (one : c.nreg 6521 = 1) (hs : R.length = s) (hR : RnMem c.nmem Ob R)
    (hsum : (R.map fun p => p.2 - p.1).sum ≤ W) (lay : Gb + 1 + 2 * s ≤ Ob)
    (w : Ob + 2 * s ≤ W) :
    ∃ c' t, Exec P W sgL c c' t ∧ t ≤ 14 * s + 2 ∧ c'.nreg 7222 = sgOff R s ∧
      (∀ j < s, c'.nmem (Gb + 1 + j) = sgOff R j ∧ c'.nmem (Gb + 1 + s + j) = sgLen R j) ∧
      (∀ a, ¬ (Gb + 1 ≤ a ∧ a < Gb + 1 + 2 * s) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 7221 ∨ x = 7223 ∨ x = 7224 ∨ 7228 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun j c' =>
    (∀ x, (x < 7221 ∨ x = 7223 ∨ x = 7224 ∨ 7228 < x) → c'.nreg x = c.nreg x) ∧ c'.nreg 7222 = sgOff R j ∧
    (∀ j' < j, c'.nmem (Gb + 1 + j') = sgOff R j' ∧ c'.nmem (Gb + 1 + s + j') = sgLen R j') ∧
    (∀ a, ¬ (Gb + 1 ≤ a ∧ a < Gb + 1 + j) → ¬ (Gb + 1 + s ≤ a ∧ a < Gb + 1 + s + j) →
      c'.nmem a = m₀ a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', k, e, hk, hw, h21, j1, j2, j3, j4, j5, j6, j7⟩ := lnRange (P := P) (a := 7221)
    (b := 7220) (body := sgBody) J (B := 12) c hc q21 q20 (Nat.zero_le s)
    ⟨fun _ _ => rfl, by rw [q22, sgOff_zero], fun j hj => absurd hj (by omega),
      fun a _ _ => rfl, rfl, rfl, rfl⟩
    (fun j c' _ hjs hw h21 h20 ⟨i1, i2, i3, i4, i5, i6, i7⟩ => by
      obtain ⟨g1, g2⟩ := hR j (by omega)
      have hlt : j < R.length := by omega
      have b1 := sgOff_le R (j + 1)
      rw [sgOff_succ hlt] at b1
      obtain ⟨c'', t, ex, ht, a21, a22, am, an, ar, arm, ao⟩ := sgBody_exec (P := P) c' hw
        (s := s) (Gb := Gb) (a := (R.getD j (0, 0)).1) (e := (R.getD j (0, 0)).2) h21 i2
        ((i1 7213 (by omega)).trans q13) ((i1 7223 (by omega)).trans q23)
        ((i1 7224 (by omega)).trans q24) ((i1 6521 (by omega)).trans one)
        (by rw [i4 (Ob + 2 * j) (by omega) (by omega)]; exact g1)
        (by rw [i4 (Ob + 2 * j + 1) (by omega) (by omega)]; exact g2) (by omega) (by omega)
        (by unfold sgLen at b1; omega) (by omega)
      refine ⟨c'', t, ex, by omega, a21, by rw [an _ (by omega), h20], fun x hx => by
        rw [an x hx, i1 x hx], by rw [a22, sgOff_succ hlt]; rfl, fun j' hj' => ?_,
        fun a h1 h2 => ?_, by rw [ar, i5], by rw [arm, i6], by rw [ao, i7]⟩
      · rw [am]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h | rfl
        · simp (disch := omega) only [upd_other]; exact i3 j' h
        · rw [upd_same, upd_other _ _ _ (by omega), upd_same]; exact ⟨rfl, rfl⟩
      · rw [am, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        exact i4 a (by omega) (by omega))
  refine ⟨c', k, e, by omega, j2, j3, fun a ha => j4 a (by omega) (by omega), j1, j5, j6, j7⟩

end Exec

end MfDrv

end BKMNW

end PlanarFlow
