module

public import PlanarFlow.BKMNW.NcLoop
public import PlanarFlow.BKMNW.NcMath

/-!
# `rbP`: the residual reachability of `c2sP` on the machine

The arrays of the dart graph of `NcMath.lean` written by store loops, then
`NegSSSP.bfsProg` from the node `m`. Registers `9600 … 9615` inputs (`m`, `FLb`, `CPb`, `Z`,
`CFb`, `LABb`, `DVb`, `DGb`, `SGb`, `RVb`, `OBb`, `OEb`, `OLb`, `HDb`, `MKb`, `Qb`), scratch
`9620 … 9646` and `bfsProg`'s `1400 … 1419`.

* `OB[u] = 2u` (`u ≤ m`), `OB[m+1] = 3m`; `OE[u] = 2u + 1 + res u` (`u < m`), `OE[m] = OE[m+1] =
  3m`, with `res u = [FL[u] < Z + CP[u]]`; `OL[k] = k` (`k < 3m`); `HD[2i] = SG[i]`,
  `HD[2i+1] = RV[i]`, `HD[2m+i] = i` if `src i = CF[i] · [DV[l] < Z · DG[l]]` (`l = LAB[i] - 1`)
  is `1`, else `m + 1`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The program -/

/-- Constants: `1`, `2`, `2m`, `3m`, `m + 1`, `m + 2`; counter `0`. -/
def rbH : Stmt :=
  block [.constN 9621 1, .constN 9622 2, .mulN 9623 9622 9600, .addN 9624 9623 9600,
    .addN 9625 9600 9621, .addN 9626 9625 9621, .constN 9620 0]

/-- `OB[i] := 2i`. -/
def bOB : Stmt := block [.mulN 9630 9622 9620, .addN 9631 9610 9620, .storeN 9631 9630,
  .addN 9620 9620 9621]

/-- `OB[m+1] := 3m`; counter `0`. -/
def tOB : Stmt := block [.addN 9631 9610 9625, .storeN 9631 9624, .constN 9620 0]

/-- `OE[i] := 2i + 1 + res i`, `res i = [FL[i] < Z + CP[i]]`. -/
def bOE : Stmt := block [.addN 9631 9601 9620, .loadN 9632 9631, .addN 9631 9602 9620,
  .loadN 9633 9631, .addN 9633 9633 9603, .subN 9633 9633 9632, .divN 9633 9633 9633,
  .mulN 9630 9622 9620, .addN 9630 9630 9621, .addN 9630 9630 9633, .addN 9631 9611 9620,
  .storeN 9631 9630, .addN 9620 9620 9621]

/-- `OE[m] := 3m`, `OE[m+1] := 3m`; counter `0`. -/
def tOE : Stmt := block [.addN 9631 9611 9600, .storeN 9631 9624, .addN 9631 9611 9625,
  .storeN 9631 9624, .constN 9620 0]

/-- `OL[k] := k`. -/
def bOL : Stmt := block [.addN 9631 9612 9620, .storeN 9631 9620, .addN 9620 9620 9621]

/-- Counter `0`. -/
def tZ : Stmt := block [.constN 9620 0]

/-- `HD[2i] := SG[i]`. -/
def bHE : Stmt := block [.addN 9631 9608 9620, .loadN 9632 9631, .mulN 9630 9622 9620,
  .addN 9631 9613 9630, .storeN 9631 9632, .addN 9620 9620 9621]

/-- `HD[2i+1] := RV[i]`. -/
def bHO : Stmt := block [.addN 9631 9609 9620, .loadN 9632 9631, .mulN 9630 9622 9620,
  .addN 9630 9630 9621, .addN 9631 9613 9630, .storeN 9631 9632, .addN 9620 9620 9621]

/-- The source bit, part 1: `r9640 := [DV[l] < Z · DG[l]]`, `l = LAB[i] - 1`. -/
def bHS1 : Stmt := block [.addN 9631 9605 9620, .loadN 9638 9631, .subN 9638 9638 9621,
  .addN 9631 9606 9638, .loadN 9639 9631, .addN 9631 9607 9638, .loadN 9640 9631,
  .mulN 9640 9640 9603, .subN 9640 9640 9639, .divN 9640 9640 9640]

/-- Part 2: `src = CF[i] · r9640`; `HD[2m+i] := src · i + (m+1) - src · (m+1)`; `i := i + 1`. -/
def bHS2 : Stmt := block [.addN 9631 9604 9620, .loadN 9641 9631, .mulN 9641 9641 9640,
  .mulN 9645 9641 9620, .addN 9645 9645 9625, .mulN 9646 9641 9625, .subN 9645 9645 9646,
  .addN 9630 9623 9620, .addN 9631 9613 9630, .storeN 9631 9645, .addN 9620 9620 9621]

/-- The source arcs. -/
def bHS : Stmt := .seq bHS1 bHS2

/-- The arguments of `bfsProg`. -/
def tB : Stmt := block [.copyN 1400 9626, .copyN 1401 9600, .copyN 1402 9610, .copyN 1403 9611,
  .copyN 1404 9612, .copyN 1405 9613, .copyN 1406 9614, .copyN 1407 9615]

/-- The arrays of the dart graph. -/
def rbA1 : Stmt :=
  .seq rbH (.seq (.whileLtN 9620 9625 bOB) (.seq tOB (.seq (.whileLtN 9620 9600 bOE)
    (.seq tOE (.seq (.whileLtN 9620 9624 bOL) tZ)))))

/-- The heads of the arcs. -/
def rbA2 : Stmt :=
  .seq (.whileLtN 9620 9600 bHE) (.seq tZ (.seq (.whileLtN 9620 9600 bHO)
    (.seq tZ (.whileLtN 9620 9600 bHS))))

/-- **The residual reachability** (see the module docstring). -/
def rbP : Stmt := .seq rbA1 (.seq rbA2 (.seq tB NegSSSP.bfsProg))

variable {P : Input} {W : ℕ}

theorem rbH_exec (c : Config) (hc : WordsBounded W c) {m : ℕ} (r0 : c.nreg 9600 = m)
    (w : 3 * m + 2 ≤ W) :
    ∃ c' t, Exec P W rbH c c' t ∧ t = 7 ∧ c'.nreg 9621 = 1 ∧ c'.nreg 9622 = 2 ∧
      c'.nreg 9623 = 2 * m ∧ c'.nreg 9624 = 3 * m ∧ c'.nreg 9625 = m + 1 ∧
      c'.nreg 9626 = m + 2 ∧ c'.nreg 9620 = 0 ∧
      (∀ x, (x < 9620 ∨ 9626 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rbH
  exec_block
  all_goals try (clear * - r0 w; config_simp; (try simp only [r0]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r0]
  all_goals try omega
  simp only [upd_apply]; split_ifs <;> omega

theorem bOB_exec (c : Config) (hc : WordsBounded W c) {OBb i : ℕ} (r10 : c.nreg 9610 = OBb)
    (r20 : c.nreg 9620 = i) (r21 : c.nreg 9621 = 1) (r22 : c.nreg 9622 = 2)
    (w : OBb + 2 * i + 2 ≤ W) :
    ∃ c' t, Exec P W bOB c c' t ∧ t = 4 ∧ c'.nreg 9620 = i + 1 ∧
      (∀ x, (x < 9620 ∨ 9646 < x ∨ (9621 ≤ x ∧ x ≤ 9629)) →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (OBb + 1 * i + 0) (2 * i) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bOB
  exec_block
  all_goals try (clear * - r10 r20 r21 r22 w; config_simp; (try simp only [r10, r20, r21, r22]); omega)
  refine ⟨rfl, ?_, fun x h1 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r10, r20, r21, r22]
  · simp only [upd_apply]; split_ifs <;> omega
  · congr 1 <;> omega

/-- A comparison bit. -/
lemma bit_le (a b : ℕ) : (a - b) / (a - b) ≤ 1 := by
  rcases Nat.eq_zero_or_pos (a - b) with h | h
  · simp [h]
  · rw [Nat.div_self h]

/-- The registers kept by the loop bodies. -/
def RbK (x : ℕ) : Prop := x < 9620 ∨ 9646 < x ∨ (9621 ≤ x ∧ x ≤ 9629)

theorem tOB_exec (c : Config) (hc : WordsBounded W c) {OBb m : ℕ} (r10 : c.nreg 9610 = OBb)
    (r24 : c.nreg 9624 = 3 * m) (r25 : c.nreg 9625 = m + 1) (w : OBb + m + 2 ≤ W) :
    ∃ c' t, Exec P W tOB c c' t ∧ t = 3 ∧ c'.nreg 9620 = 0 ∧ (∀ x, RbK x → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (OBb + (m + 1)) (3 * m) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tOB
  exec_block
  all_goals try (clear * - r10 r24 r25 w; config_simp; (try simp only [r10, r24, r25]); omega)
  refine ⟨rfl, ?_, fun x h1 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r10, r24, r25]
  unfold RbK at h1; simp only [upd_apply]; split_ifs <;> omega

theorem bOE_exec (c : Config) (hc : WordsBounded W c) {FLb CPb Z OEb i : ℕ}
    (r01 : c.nreg 9601 = FLb) (r02 : c.nreg 9602 = CPb) (r03 : c.nreg 9603 = Z)
    (r11 : c.nreg 9611 = OEb) (r20 : c.nreg 9620 = i) (r21 : c.nreg 9621 = 1)
    (r22 : c.nreg 9622 = 2) (w1 : FLb + i ≤ W) (w2 : CPb + i ≤ W)
    (w3 : Z + c.nmem (CPb + i) ≤ W) (w4 : OEb + 2 * i + 3 ≤ W) :
    ∃ c' t, Exec P W bOE c c' t ∧ t = 13 ∧ c'.nreg 9620 = i + 1 ∧
      (∀ x, RbK x → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (OEb + 1 * i + 0) (2 * i + 1 +
        (c.nmem (CPb + i) + Z - c.nmem (FLb + i)) / (c.nmem (CPb + i) + Z - c.nmem (FLb + i))) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hd1 := bit_le (c.nmem (CPb + i) + Z) (c.nmem (FLb + i))
  unfold bOE
  exec_block
  all_goals try (clear * - r01 r02 r03 r11 r20 r21 r22 w1 w2 w3 w4 hd1; config_simp; (try simp only [r01, r02, r03, r11, r20, r21, r22]); omega)
  refine ⟨rfl, ?_, fun x h1 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r01, r02, r03, r11, r20, r21, r22]
  · unfold RbK at h1; simp only [upd_apply]; split_ifs <;> omega
  · (congr 1) <;> omega

theorem tOE_exec (c : Config) (hc : WordsBounded W c) {OEb m : ℕ} (r00 : c.nreg 9600 = m)
    (r11 : c.nreg 9611 = OEb)
    (r24 : c.nreg 9624 = 3 * m) (r25 : c.nreg 9625 = m + 1) (w : OEb + m + 2 ≤ W) :
    ∃ c' t, Exec P W tOE c c' t ∧ t = 5 ∧ c'.nreg 9620 = 0 ∧ (∀ x, RbK x → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd (upd c.nmem (OEb + m) (3 * m)) (OEb + (m + 1)) (3 * m) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tOE
  exec_block
  all_goals try (clear * - r00 r11 r24 r25 w; config_simp; (try simp only [r00, r11, r24, r25]); omega)
  refine ⟨rfl, ?_, fun x h1 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r00, r11, r24, r25]
  unfold RbK at h1; simp only [upd_apply]; split_ifs <;> omega

theorem bOL_exec (c : Config) (hc : WordsBounded W c) {OLb i : ℕ} (r12 : c.nreg 9612 = OLb)
    (r20 : c.nreg 9620 = i) (r21 : c.nreg 9621 = 1) (w : OLb + i + 1 ≤ W) :
    ∃ c' t, Exec P W bOL c c' t ∧ t = 3 ∧ c'.nreg 9620 = i + 1 ∧
      (∀ x, RbK x → c'.nreg x = c.nreg x) ∧ c'.nmem = upd c.nmem (OLb + 1 * i + 0) i ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bOL
  exec_block
  all_goals try (clear * - r12 r20 r21 w; config_simp; (try simp only [r12, r20, r21]); omega)
  refine ⟨rfl, ?_, fun x h1 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r12, r20, r21]
  · unfold RbK at h1; simp only [upd_apply]; split_ifs <;> omega
  · (congr 1) <;> omega

theorem tZ_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W tZ c c' t ∧ t = 1 ∧ c'.nreg 9620 = 0 ∧ (∀ x, RbK x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tZ
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  unfold RbK at h1; simp only [upd_apply]; split_ifs <;> omega

theorem bHE_exec (c : Config) (hc : WordsBounded W c) {SGb HDb i : ℕ}
    (r08 : c.nreg 9608 = SGb) (r13 : c.nreg 9613 = HDb) (r20 : c.nreg 9620 = i)
    (r21 : c.nreg 9621 = 1) (r22 : c.nreg 9622 = 2) (w1 : SGb + i ≤ W)
    (w2 : HDb + 2 * i + 1 ≤ W) :
    ∃ c' t, Exec P W bHE c c' t ∧ t = 6 ∧ c'.nreg 9620 = i + 1 ∧
      (∀ x, RbK x → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (HDb + 2 * i + 0) (c.nmem (SGb + i)) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bHE
  exec_block
  all_goals try (clear * - r08 r13 r20 r21 r22 w1 w2; config_simp; (try simp only [r08, r13, r20, r21, r22]); omega)
  refine ⟨rfl, ?_, fun x h1 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r08, r13, r20, r21, r22]
  · unfold RbK at h1; simp only [upd_apply]; split_ifs <;> omega
  · (congr 1) <;> omega

theorem bHO_exec (c : Config) (hc : WordsBounded W c) {RVb HDb i : ℕ}
    (r09 : c.nreg 9609 = RVb) (r13 : c.nreg 9613 = HDb) (r20 : c.nreg 9620 = i)
    (r21 : c.nreg 9621 = 1) (r22 : c.nreg 9622 = 2) (w1 : RVb + i ≤ W)
    (w2 : HDb + 2 * i + 2 ≤ W) :
    ∃ c' t, Exec P W bHO c c' t ∧ t = 7 ∧ c'.nreg 9620 = i + 1 ∧
      (∀ x, RbK x → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (HDb + 2 * i + 1) (c.nmem (RVb + i)) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bHO
  exec_block
  all_goals try (clear * - r09 r13 r20 r21 r22 w1 w2; config_simp; (try simp only [r09, r13, r20, r21, r22]); omega)
  refine ⟨rfl, ?_, fun x h1 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r09, r13, r20, r21, r22]
  · unfold RbK at h1; simp only [upd_apply]; split_ifs <;> omega
  · (congr 1) <;> omega

theorem bHS1_exec (c : Config) (hc : WordsBounded W c) {Z LABb DVb DGb i l : ℕ}
    (r03 : c.nreg 9603 = Z) (r05 : c.nreg 9605 = LABb) (r06 : c.nreg 9606 = DVb)
    (r07 : c.nreg 9607 = DGb) (r20 : c.nreg 9620 = i) (r21 : c.nreg 9621 = 1)
    (hl : c.nmem (LABb + i) = l + 1) (w1 : LABb + i ≤ W) (w2 : DVb + l ≤ W) (w3 : DGb + l ≤ W)
    (w4 : c.nmem (DGb + l) * Z ≤ W) :
    ∃ c' t, Exec P W bHS1 c c' t ∧ t = 10 ∧
      c'.nreg 9640 = (c.nmem (DGb + l) * Z - c.nmem (DVb + l)) /
        (c.nmem (DGb + l) * Z - c.nmem (DVb + l)) ∧
      (∀ x, x ≠ 9631 → x ≠ 9638 → x ≠ 9639 → x ≠ 9640 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hd1 := bit_le (c.nmem (DGb + l) * Z) (c.nmem (DVb + l))
  unfold bHS1
  exec_block
  all_goals try (clear * - r03 r05 r06 r07 r20 r21 hl w1 w2 w3 w4 hd1; config_simp; (try simp only [r03, r05, r06, r07, r20, r21, hl, Nat.add_sub_cancel]); omega)
  refine ⟨rfl, ?_, fun x h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r03, r05, r06, r07, r20, r21, hl, Nat.add_sub_cancel]
  simp only [upd_apply]; split_ifs <;> omega

theorem bHS2_exec (c : Config) (hc : WordsBounded W c) {CFb HDb m i bt : ℕ}
    (r04 : c.nreg 9604 = CFb) (r13 : c.nreg 9613 = HDb) (r20 : c.nreg 9620 = i)
    (r21 : c.nreg 9621 = 1) (r23 : c.nreg 9623 = 2 * m) (r25 : c.nreg 9625 = m + 1)
    (r40 : c.nreg 9640 = bt) (hbt : bt ≤ 1) (hcf : c.nmem (CFb + i) ≤ 1) (w1 : CFb + i ≤ W)
    (w2 : HDb + 2 * m + i + 1 ≤ W) (w3 : m + 1 + i ≤ W) :
    ∃ c' t, Exec P W bHS2 c c' t ∧ t = 11 ∧ c'.nreg 9620 = i + 1 ∧
      (∀ x, RbK x → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (HDb + 1 * i + 2 * m)
        (c.nmem (CFb + i) * bt * i + (m + 1) - c.nmem (CFb + i) * bt * (m + 1)) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hs : c.nmem (CFb + i) * bt ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hbt with h | h <;> subst h <;> simp <;> omega
  have hs1 : c.nmem (CFb + i) * bt * i ≤ i := by
    calc c.nmem (CFb + i) * bt * i ≤ 1 * i := Nat.mul_le_mul_right _ hs
      _ = i := one_mul i
  have hs2 : c.nmem (CFb + i) * bt * (m + 1) ≤ m + 1 := by
    calc c.nmem (CFb + i) * bt * (m + 1) ≤ 1 * (m + 1) := Nat.mul_le_mul_right _ hs
      _ = m + 1 := one_mul _
  unfold bHS2
  exec_block
  all_goals try (clear * - r04 r13 r20 r21 r23 r25 r40 hs hs1 hs2 w1 w2 w3; config_simp; (try simp only [r04, r13, r20, r21, r23, r25, r40]); omega)
  refine ⟨rfl, ?_, fun x h1 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r04, r13, r20, r21, r23, r25, r40]
  · unfold RbK at h1; simp only [upd_apply]; split_ifs <;> omega
  · (congr 1) <;> omega

theorem bHS_exec (c : Config) (hc : WordsBounded W c) {Z LABb DVb DGb CFb HDb m i l : ℕ}
    (r03 : c.nreg 9603 = Z) (r04 : c.nreg 9604 = CFb) (r05 : c.nreg 9605 = LABb)
    (r06 : c.nreg 9606 = DVb) (r07 : c.nreg 9607 = DGb) (r13 : c.nreg 9613 = HDb)
    (r20 : c.nreg 9620 = i) (r21 : c.nreg 9621 = 1) (r23 : c.nreg 9623 = 2 * m)
    (r25 : c.nreg 9625 = m + 1)
    (hl : c.nmem (LABb + i) = l + 1) (w1 : LABb + i ≤ W) (w2 : DVb + l ≤ W) (w3 : DGb + l ≤ W)
    (w4 : c.nmem (DGb + l) * Z ≤ W) (hcf : c.nmem (CFb + i) ≤ 1) (w5 : CFb + i ≤ W)
    (w6 : HDb + 2 * m + i + 1 ≤ W) (w7 : m + 1 + i ≤ W) :
    ∃ c' t, Exec P W bHS c c' t ∧ t = 21 ∧ c'.nreg 9620 = i + 1 ∧
      (∀ x, RbK x → c'.nreg x = c.nreg x) ∧
      c'.nmem = upd c.nmem (HDb + 1 * i + 2 * m)
        (c.nmem (CFb + i) * ((c.nmem (DGb + l) * Z - c.nmem (DVb + l)) /
          (c.nmem (DGb + l) * Z - c.nmem (DVb + l))) * i + (m + 1) -
         c.nmem (CFb + i) * ((c.nmem (DGb + l) * Z - c.nmem (DVb + l)) /
          (c.nmem (DGb + l) * Z - c.nmem (DVb + l))) * (m + 1)) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g40, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    bHS1_exec (P := P) c hc r03 r05 r06 r07 r20 r21 hl w1 w2 w3 w4
  have q : ∀ x, RbK x → x ≠ 9640 → c₁.nreg x = c.nreg x := fun x hx h =>
    f₁ x (by unfold RbK at hx; omega) (by unfold RbK at hx; omega)
      (by unfold RbK at hx; omega) h
  obtain ⟨c₂, t₂, e₂, ht₂, g20, f₂, m₂, rr₂, rm₂, o₂⟩ := bHS2_exec (P := P) c₁ e₁.wb_right
    (by rw [q _ (by unfold RbK; omega) (by omega), r04])
    (by rw [q _ (by unfold RbK; omega) (by omega), r13])
    (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega), r20])
    (by rw [q _ (by unfold RbK; omega) (by omega), r21])
    (by rw [q _ (by unfold RbK; omega) (by omega), r23])
    (by rw [q _ (by unfold RbK; omega) (by omega), r25]) g40 (bit_le _ _)
    (by rw [m₁]; exact hcf) w5 w6 w7
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, g20, fun x hx => ?_, by rw [m₂, m₁],
    by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
  rw [f₂ x hx]
  exact q x hx (by unfold RbK at hx; omega)

theorem tB_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W tB c c' t ∧ t = 8 ∧ c'.nreg 1400 = c.nreg 9626 ∧
      c'.nreg 1401 = c.nreg 9600 ∧ c'.nreg 1402 = c.nreg 9610 ∧ c'.nreg 1403 = c.nreg 9611 ∧
      c'.nreg 1404 = c.nreg 9612 ∧ c'.nreg 1405 = c.nreg 9613 ∧ c'.nreg 1406 = c.nreg 9614 ∧
      c'.nreg 1407 = c.nreg 9615 ∧ (∀ x, (x < 1400 ∨ 1407 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tB
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

/-! ### The whole stage -/

/-- The residual bit of the dart `i` (`[FL[i] < CP[i] + Z]`). -/
def rbRes (mem : ℕ → ℕ) (FLb CPb Z i : ℕ) : ℕ :=
  (mem (CPb + i) + Z - mem (FLb + i)) / (mem (CPb + i) + Z - mem (FLb + i))

/-- The source bit of the dart `i` (`CF[i] · [DV[l] < Z · DG[l]]`, `l = LAB[i] - 1`). -/
def rbSrc (mem : ℕ → ℕ) (Z CFb LABb DVb DGb i : ℕ) : ℕ :=
  mem (CFb + i) * ((mem (DGb + (mem (LABb + i) - 1)) * Z - mem (DVb + (mem (LABb + i) - 1))) /
    (mem (DGb + (mem (LABb + i) - 1)) * Z - mem (DVb + (mem (LABb + i) - 1))))

/-- The step bound of `rbP`. -/
def rbCost (m : ℕ) : ℕ := 172 * m + 160

lemma rbSrc_le {mem : ℕ → ℕ} {Z CFb LABb DVb DGb i : ℕ} (h : mem (CFb + i) ≤ 1) :
    rbSrc mem Z CFb LABb DVb DGb i ≤ 1 := by
  unfold rbSrc
  have := bit_le (mem (DGb + (mem (LABb + i) - 1)) * Z) (mem (DVb + (mem (LABb + i) - 1)))
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with e | e <;> rw [e] <;> omega

lemma rbHd_src {m i s : ℕ} (hs : s ≤ 1) : s * i + (m + 1) - s * (m + 1) =
    if s = 1 then i else m + 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hs with e | e <;> subst e <;> simp

/-- `bfsProg` names only the registers `1400 … 1419`. -/
theorem bfsProg_regsOK : Stmt.regsOK (fun r => decide (1400 ≤ r ∧ r < 1420)) NegSSSP.bfsProg = true := by
  decide +kernel

theorem bfsProg_noRand : Stmt.noRand NegSSSP.bfsProg = true := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The out-arc bounds and the arc list** (`rbA1`): `OB`, `OE`, `OL` from `S`. -/
theorem rbA1_exec (c : Config) (hc : WordsBounded W c)
    {m FLb CPb Z CFb LABb DVb DGb SGb RVb S : ℕ}
    (r00 : c.nreg 9600 = m) (r01 : c.nreg 9601 = FLb) (r02 : c.nreg 9602 = CPb)
    (r03 : c.nreg 9603 = Z) (r04 : c.nreg 9604 = CFb) (r05 : c.nreg 9605 = LABb)
    (r06 : c.nreg 9606 = DVb) (r07 : c.nreg 9607 = DGb) (r08 : c.nreg 9608 = SGb)
    (r09 : c.nreg 9609 = RVb) (r10 : c.nreg 9610 = S) (r11 : c.nreg 9611 = S + (m + 2))
    (r12 : c.nreg 9612 = S + 2 * (m + 2)) (r13 : c.nreg 9613 = S + 2 * (m + 2) + 3 * m)
    (r14 : c.nreg 9614 = S + 2 * (m + 2) + 6 * m) (r15 : c.nreg 9615 = S + 3 * (m + 2) + 6 * m)
    (iFL : FLb + m ≤ S) (iCP : CPb + m ≤ S) (iCF : CFb + m ≤ S) (iLAB : LABb + m ≤ S)
    (iDV : DVb + m ≤ S) (iDG : DGb + m ≤ S) (iSG : SGb + m ≤ S) (iRV : RVb + m ≤ S)
    (wS : S + 4 * (m + 2) + 6 * m + 1 ≤ W)
    (hlab : ∀ i < m, 1 ≤ c.nmem (LABb + i) ∧ c.nmem (LABb + i) ≤ m)
    (hcf : ∀ i < m, c.nmem (CFb + i) ≤ 1)
    (hsg : ∀ i < m, c.nmem (SGb + i) < m) (hrv : ∀ i < m, c.nmem (RVb + i) < m)
    (wcp : ∀ i < m, c.nmem (CPb + i) + Z ≤ W)
    (wdg : ∀ v < m, c.nmem (DGb + v) * Z ≤ W) :
    ∃ c' t, Exec P W rbA1 c c' t ∧ t ≤ 36 * m + 28 ∧
      (∀ u < m + 2, c'.nmem (S + u) = rbOb m u) ∧
      (∀ u < m + 2, c'.nmem (S + (m + 2) + u) = rbOe m (rbRes c.nmem FLb CPb Z) u) ∧
      (∀ k < 3 * m, c'.nmem (S + 2 * (m + 2) + k) = id k) ∧
      (∀ a, (a < S ∨ S + 2 * (m + 2) + 3 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 9620 ∨ 9646 < x) → c'.nreg x = c.nreg x) ∧ c'.nreg 9620 = 0 ∧
      c'.nreg 9621 = 1 ∧ c'.nreg 9622 = 2 ∧ c'.nreg 9623 = 2 * m ∧ c'.nreg 9625 = m + 1 ∧
      c'.nreg 9626 = m + 2 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  set mem₀ := c.nmem with hmem₀
  -- 0. constants
  obtain ⟨c₁, t₁, e₁, ht₁, a21, a22, a23, a24, a25, a26, a20, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    rbH_exec (P := P) c hc r00 (by omega)
  have K1 : ∀ x, (x < 9620 ∨ 9626 < x) → c₁.nreg x = c.nreg x := f₁
  -- registers of `c₁` that every body keeps
  have k00 : RbK 9600 := by unfold RbK; omega
  -- 1. OB
  obtain ⟨c₂, t₂, e₂, ht₂, v₂, o₂, f₂, n₂, rr₂, rm₂, oo₂⟩ := lnStore (P := P) (W := W)
    (a := 9620) (b := 9625) (body := bOB) (Ob := S) (s := 1) (o := 0) (n := m + 1) (B := 4)
    Nat.one_pos (fun i => 2 * i) RbK c₁ e₁.wb_right a20 a25 (by unfold RbK; omega)
    (fun i c' hi hw h20 hk hm => by
      obtain ⟨c'', k, ex, hk', g20, gk, gm, gr, grm, go⟩ := bOB_exec (P := P) c' hw
        (by rw [hk _ (by unfold RbK; omega), K1 _ (by omega), r10]) h20
        (by rw [hk _ (by unfold RbK; omega), a21]) (by rw [hk _ (by unfold RbK; omega), a22])
        (by omega)
      exact ⟨c'', k, ex, hk'.le, g20, gk, gm, gr, grm, go⟩)
  have G2 : ∀ x, RbK x → c₂.nreg x = c₁.nreg x := f₂
  -- 2. OB[m+1]
  obtain ⟨c₃, t₃, e₃, ht₃, n₃, f₃, m₃, rr₃, rm₃, oo₃⟩ := tOB_exec (P := P) c₂ e₂.wb_right
    (by rw [G2 _ (by unfold RbK; omega), K1 _ (by omega), r10])
    (by rw [G2 _ (by unfold RbK; omega), a24]) (by rw [G2 _ (by unfold RbK; omega), a25])
    (by omega)
  have G3 : ∀ x, RbK x → c₃.nreg x = c₁.nreg x := fun x hx => by rw [f₃ x hx, G2 x hx]
  have L3 : ∀ a, a < S → c₃.nmem a = mem₀ a := fun a ha => by
    rw [m₃, upd_other _ _ _ (by omega), o₂ a (fun j hj => by omega), m₁]
  -- 3. OE
  obtain ⟨c₄, t₄, e₄, ht₄, v₄, o₄, f₄, n₄, rr₄, rm₄, oo₄⟩ := lnStore (P := P) (W := W)
    (a := 9620) (b := 9600) (body := bOE) (Ob := S + (m + 2)) (s := 1) (o := 0) (n := m)
    (B := 13) Nat.one_pos (fun i => 2 * i + 1 + rbRes mem₀ FLb CPb Z i) RbK c₃ e₃.wb_right n₃
    (by rw [G3 _ (by unfold RbK; omega), K1 _ (by omega), r00]) (by unfold RbK; omega)
    (fun i c' hi hw h20 hk hm => by
      have e1 : c'.nmem (FLb + i) = mem₀ (FLb + i) := by
        rw [hm _ (fun j hj => by omega), L3 _ (by omega)]
      have e2 : c'.nmem (CPb + i) = mem₀ (CPb + i) := by
        rw [hm _ (fun j hj => by omega), L3 _ (by omega)]
      obtain ⟨c'', k, ex, hk', g20, gk, gm, gr, grm, go⟩ := bOE_exec (P := P) c' hw
        (by rw [hk _ (by unfold RbK; omega), G3 _ (by unfold RbK; omega), K1 _ (by omega), r01])
        (by rw [hk _ (by unfold RbK; omega), G3 _ (by unfold RbK; omega), K1 _ (by omega), r02])
        (by rw [hk _ (by unfold RbK; omega), G3 _ (by unfold RbK; omega), K1 _ (by omega), r03])
        (by rw [hk _ (by unfold RbK; omega), G3 _ (by unfold RbK; omega), K1 _ (by omega), r11])
        h20 (by rw [hk _ (by unfold RbK; omega), G3 _ (by unfold RbK; omega), a21])
        (by rw [hk _ (by unfold RbK; omega), G3 _ (by unfold RbK; omega), a22]) (by omega)
        (by omega) (by rw [e2]; have := wcp i hi; omega) (by omega)
      refine ⟨c'', k, ex, hk'.le, g20, gk, ?_, gr, grm, go⟩
      rw [gm, e1, e2]; rfl)
  have G4 : ∀ x, RbK x → c₄.nreg x = c₁.nreg x := fun x hx => by rw [f₄ x hx, G3 x hx]
  -- 4. OE[m], OE[m+1]
  obtain ⟨c₅, t₅, e₅, ht₅, n₅, f₅, m₅, rr₅, rm₅, oo₅⟩ := tOE_exec (P := P) c₄ e₄.wb_right
    (by rw [G4 _ (by unfold RbK; omega), K1 _ (by omega), r00])
    (by rw [G4 _ (by unfold RbK; omega), K1 _ (by omega), r11])
    (by rw [G4 _ (by unfold RbK; omega), a24]) (by rw [G4 _ (by unfold RbK; omega), a25])
    (by omega)
  have G5 : ∀ x, RbK x → c₅.nreg x = c₁.nreg x := fun x hx => by rw [f₅ x hx, G4 x hx]
  have L5 : ∀ a, a < S → c₅.nmem a = mem₀ a := fun a ha => by
    rw [m₅, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), o₄ a (fun j hj => by omega),
      L3 a ha]
  -- 5. OL
  obtain ⟨c₆, t₆, e₆, ht₆, v₆, o₆, f₆, n₆, rr₆, rm₆, oo₆⟩ := lnStore (P := P) (W := W)
    (a := 9620) (b := 9624) (body := bOL) (Ob := S + 2 * (m + 2)) (s := 1) (o := 0)
    (n := 3 * m) (B := 3) Nat.one_pos (fun i => i) RbK c₅ e₅.wb_right n₅
    (by rw [G5 _ (by unfold RbK; omega), a24]) (by unfold RbK; omega)
    (fun i c' hi hw h20 hk hm => by
      obtain ⟨c'', k, ex, hk', g20, gk, gm, gr, grm, go⟩ := bOL_exec (P := P) c' hw
        (by rw [hk _ (by unfold RbK; omega), G5 _ (by unfold RbK; omega), K1 _ (by omega), r12])
        h20 (by rw [hk _ (by unfold RbK; omega), G5 _ (by unfold RbK; omega), a21]) (by omega)
      exact ⟨c'', k, ex, hk'.le, g20, gk, gm, gr, grm, go⟩)
  have G6 : ∀ x, RbK x → c₆.nreg x = c₁.nreg x := fun x hx => by rw [f₆ x hx, G5 x hx]
  have L6 : ∀ a, a < S → c₆.nmem a = mem₀ a := fun a ha => by
    rw [o₆ a (fun j hj => by omega), L5 a ha]
  -- 6. counter
  obtain ⟨c₇, t₇, e₇, ht₇, n₇, f₇, m₇, rr₇, rm₇, oo₇⟩ := tZ_exec (P := P) c₆ e₆.wb_right
  have G7 : ∀ x, RbK x → c₇.nreg x = c₁.nreg x := fun x hx => by rw [f₇ x hx, G6 x hx]
  have hOE : ∀ a, a < S + 2 * (m + 2) → c₆.nmem a = c₅.nmem a := fun a ha =>
    o₆ a (fun j hj => by omega)
  have hOB : ∀ a, a < S + (m + 2) → c₅.nmem a = c₃.nmem a := fun a ha => by
    rw [m₅, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), o₄ a (fun j hj => by omega)]
  have qOB : ∀ u < m + 2, c₇.nmem (S + u) = rbOb m u := fun u hu => by
    rw [m₇, hOE _ (by omega), hOB _ (by omega), m₃]
    unfold rbOb
    by_cases hum : u ≤ m
    · rw [upd_other _ _ _ (by omega), iteT hum]
      have h2 := v₂ u (by omega)
      simp only [one_mul, add_zero] at h2
      exact h2
    · obtain rfl : u = m + 1 := by omega
      rw [upd_same, iteF hum]
  have qOE : ∀ u < m + 2, c₇.nmem (S + (m + 2) + u) = rbOe m (rbRes mem₀ FLb CPb Z) u :=
    fun u hu => by
    rw [m₇, hOE _ (by omega), m₅]
    unfold rbOe
    by_cases hum : u < m
    · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), iteT hum]
      have h2 := v₄ u hum
      simp only [one_mul, add_zero] at h2
      exact h2
    · rw [iteF hum]
      by_cases e : u = m + 1
      · subst e; rw [upd_same]
      · obtain rfl : u = m := by omega
        rw [upd_other _ _ _ (by omega), upd_same]
  have qOL : ∀ k < 3 * m, c₇.nmem (S + 2 * (m + 2) + k) = id k := fun k hk => by
    rw [m₇]
    have h2 := v₆ k hk
    simp only [one_mul, add_zero] at h2
    exact h2
  refine ⟨c₇, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), ?_, qOB, qOE, qOL,
    fun a ha => ?_, fun x hx => ?_, n₇, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ ht₇; omega
  · rw [m₇, o₆ a (fun j hj => by omega), m₅, upd_other _ _ _ (by omega),
      upd_other _ _ _ (by omega), o₄ a (fun j hj => by omega), m₃, upd_other _ _ _ (by omega),
      o₂ a (fun j hj => by omega), m₁]
  · rw [G7 x (by unfold RbK; omega), K1 x (by omega)]
  · rw [G7 _ (by unfold RbK; omega), a21]
  · rw [G7 _ (by unfold RbK; omega), a22]
  · rw [G7 _ (by unfold RbK; omega), a23]
  · rw [G7 _ (by unfold RbK; omega), a25]
  · rw [G7 _ (by unfold RbK; omega), a26]
  · rw [rr₇, rr₆, rr₅, rr₄, rr₃, rr₂, rr₁]
  · rw [rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁]
  · rw [oo₇, oo₆, oo₅, oo₄, oo₃, oo₂, o₁]

set_option maxHeartbeats 4000000 in
/-- **The heads of the arcs** (`rbA2`): `HD` from `S + 2 (m + 2) + 3 m`. -/
theorem rbA2_exec (c₇ : Config) (hc : WordsBounded W c₇)
    {m Z CFb LABb DVb DGb SGb RVb S : ℕ}
    (r00 : c₇.nreg 9600 = m) (r03 : c₇.nreg 9603 = Z) (r04 : c₇.nreg 9604 = CFb)
    (r05 : c₇.nreg 9605 = LABb) (r06 : c₇.nreg 9606 = DVb) (r07 : c₇.nreg 9607 = DGb)
    (r08 : c₇.nreg 9608 = SGb) (r09 : c₇.nreg 9609 = RVb)
    (r13 : c₇.nreg 9613 = S + 2 * (m + 2) + 3 * m)
    (n₇ : c₇.nreg 9620 = 0) (a21 : c₇.nreg 9621 = 1) (a22 : c₇.nreg 9622 = 2)
    (a23 : c₇.nreg 9623 = 2 * m) (a25 : c₇.nreg 9625 = m + 1)
    (iCF : CFb + m ≤ S) (iLAB : LABb + m ≤ S)
    (iDV : DVb + m ≤ S) (iDG : DGb + m ≤ S) (iSG : SGb + m ≤ S) (iRV : RVb + m ≤ S)
    (wS : S + 4 * (m + 2) + 6 * m + 1 ≤ W)
    (hlab : ∀ i < m, 1 ≤ c₇.nmem (LABb + i) ∧ c₇.nmem (LABb + i) ≤ m)
    (hcf : ∀ i < m, c₇.nmem (CFb + i) ≤ 1)
    (wdg : ∀ v < m, c₇.nmem (DGb + v) * Z ≤ W) :
    ∃ c' t, Exec P W rbA2 c₇ c' t ∧ t ≤ 40 * m + 8 ∧
      (∀ a < 3 * m, c'.nmem (S + 2 * (m + 2) + 3 * m + a) =
        rbHd m (fun i => c₇.nmem (SGb + i)) (fun i => c₇.nmem (RVb + i))
          (rbSrc c₇.nmem Z CFb LABb DVb DGb) a) ∧
      (∀ a, (a < S + 2 * (m + 2) + 3 * m ∨ S + 2 * (m + 2) + 6 * m ≤ a) →
        c'.nmem a = c₇.nmem a) ∧
      (∀ x, RbK x → c'.nreg x = c₇.nreg x) ∧
      c'.rreg = c₇.rreg ∧ c'.rmem = c₇.rmem ∧ c'.output = c₇.output := by
  classical
  set mem₀ := c₇.nmem with hmem₀
  have G7 : ∀ x, RbK x → c₇.nreg x = c₇.nreg x := fun _ _ => rfl
  have K1 : ∀ x, (x < 9620 ∨ 9626 < x) → c₇.nreg x = c₇.nreg x := fun _ _ => rfl
  have L6 : ∀ a, a < S → c₇.nmem a = mem₀ a := fun _ _ => rfl
  have m₇ : c₇.nmem = c₇.nmem := rfl
  -- 7. HD even
  obtain ⟨c₈, t₈, e₈, ht₈, v₈, o₈, f₈, n₈, rr₈, rm₈, oo₈⟩ := lnStore (P := P) (W := W)
    (a := 9620) (b := 9600) (body := bHE) (Ob := S + 2 * (m + 2) + 3 * m) (s := 2) (o := 0)
    (n := m) (B := 6) (by omega) (fun i => mem₀ (SGb + i)) RbK c₇ hc n₇
    (by rw [G7 _ (by unfold RbK; omega), K1 _ (by omega), r00]) (by unfold RbK; omega)
    (fun i c' hi hw h20 hk hm => by
      have e1 : c'.nmem (SGb + i) = mem₀ (SGb + i) := by
        rw [hm _ (fun j hj => by omega), m₇, L6 _ (by omega)]
      obtain ⟨c'', k, ex, hk', g20, gk, gm, gr, grm, go⟩ := bHE_exec (P := P) c' hw
        (by rw [hk _ (by unfold RbK; omega), G7 _ (by unfold RbK; omega), K1 _ (by omega), r08])
        (by rw [hk _ (by unfold RbK; omega), G7 _ (by unfold RbK; omega), K1 _ (by omega), r13])
        h20 (by rw [hk _ (by unfold RbK; omega), G7 _ (by unfold RbK; omega), a21])
        (by rw [hk _ (by unfold RbK; omega), G7 _ (by unfold RbK; omega), a22]) (by omega)
        (by omega)
      refine ⟨c'', k, ex, hk'.le, g20, gk, ?_, gr, grm, go⟩
      rw [gm, e1])
  have G8 : ∀ x, RbK x → c₈.nreg x = c₇.nreg x := fun x hx => by rw [f₈ x hx, G7 x hx]
  have L8 : ∀ a, a < S → c₈.nmem a = mem₀ a := fun a ha => by
    rw [o₈ a (fun j hj => by omega), m₇, L6 a ha]
  obtain ⟨c₉, t₉, e₉, ht₉, n₉, f₉, m₉, rr₉, rm₉, oo₉⟩ := tZ_exec (P := P) c₈ e₈.wb_right
  have G9 : ∀ x, RbK x → c₉.nreg x = c₇.nreg x := fun x hx => by rw [f₉ x hx, G8 x hx]
  -- 9. HD odd
  obtain ⟨c₁₀, t₁₀, e₁₀, ht₁₀, v₁₀, o₁₀, f₁₀, n₁₀, rr₁₀, rm₁₀, oo₁₀⟩ := lnStore (P := P)
    (W := W) (a := 9620) (b := 9600) (body := bHO) (Ob := S + 2 * (m + 2) + 3 * m) (s := 2)
    (o := 1) (n := m) (B := 7) (by omega) (fun i => mem₀ (RVb + i)) RbK c₉ e₉.wb_right n₉
    (by rw [G9 _ (by unfold RbK; omega), K1 _ (by omega), r00]) (by unfold RbK; omega)
    (fun i c' hi hw h20 hk hm => by
      have e1 : c'.nmem (RVb + i) = mem₀ (RVb + i) := by
        rw [hm _ (fun j hj => by omega), m₉, L8 _ (by omega)]
      obtain ⟨c'', k, ex, hk', g20, gk, gm, gr, grm, go⟩ := bHO_exec (P := P) c' hw
        (by rw [hk _ (by unfold RbK; omega), G9 _ (by unfold RbK; omega), K1 _ (by omega), r09])
        (by rw [hk _ (by unfold RbK; omega), G9 _ (by unfold RbK; omega), K1 _ (by omega), r13])
        h20 (by rw [hk _ (by unfold RbK; omega), G9 _ (by unfold RbK; omega), a21])
        (by rw [hk _ (by unfold RbK; omega), G9 _ (by unfold RbK; omega), a22]) (by omega)
        (by omega)
      refine ⟨c'', k, ex, hk'.le, g20, gk, ?_, gr, grm, go⟩
      rw [gm, e1])
  have G10 : ∀ x, RbK x → c₁₀.nreg x = c₇.nreg x := fun x hx => by rw [f₁₀ x hx, G9 x hx]
  have L10 : ∀ a, a < S → c₁₀.nmem a = mem₀ a := fun a ha => by
    rw [o₁₀ a (fun j hj => by omega), m₉, L8 a ha]
  obtain ⟨c₁₁, t₁₁, e₁₁, ht₁₁, n₁₁, f₁₁, m₁₁, rr₁₁, rm₁₁, oo₁₁⟩ := tZ_exec (P := P) c₁₀
    e₁₀.wb_right
  have G11 : ∀ x, RbK x → c₁₁.nreg x = c₇.nreg x := fun x hx => by rw [f₁₁ x hx, G10 x hx]
  -- 11. the source arcs
  obtain ⟨c₁₂, t₁₂, e₁₂, ht₁₂, v₁₂, o₁₂, f₁₂, n₁₂, rr₁₂, rm₁₂, oo₁₂⟩ := lnStore (P := P)
    (W := W) (a := 9620) (b := 9600) (body := bHS) (Ob := S + 2 * (m + 2) + 3 * m) (s := 1)
    (o := 2 * m) (n := m) (B := 21) Nat.one_pos
    (fun i => rbSrc mem₀ Z CFb LABb DVb DGb i * i + (m + 1) -
      rbSrc mem₀ Z CFb LABb DVb DGb i * (m + 1)) RbK c₁₁ e₁₁.wb_right n₁₁
    (by rw [G11 _ (by unfold RbK; omega), K1 _ (by omega), r00]) (by unfold RbK; omega)
    (fun i c' hi hw h20 hk hm => by
      have L' : ∀ a, a < S → c'.nmem a = mem₀ a := fun a ha => by
        rw [hm _ (fun j hj => by omega), m₁₁, L10 a ha]
      obtain ⟨hl1, hl2⟩ := hlab i hi
      have hl : c'.nmem (LABb + i) = (mem₀ (LABb + i) - 1) + 1 := by
        rw [L' _ (by omega)]; omega
      obtain ⟨c'', k, ex, hk', g20, gk, gm, gr, grm, go⟩ := bHS_exec (P := P) c' hw
        (by rw [hk _ (by unfold RbK; omega), G11 _ (by unfold RbK; omega), K1 _ (by omega), r03])
        (by rw [hk _ (by unfold RbK; omega), G11 _ (by unfold RbK; omega), K1 _ (by omega), r04])
        (by rw [hk _ (by unfold RbK; omega), G11 _ (by unfold RbK; omega), K1 _ (by omega), r05])
        (by rw [hk _ (by unfold RbK; omega), G11 _ (by unfold RbK; omega), K1 _ (by omega), r06])
        (by rw [hk _ (by unfold RbK; omega), G11 _ (by unfold RbK; omega), K1 _ (by omega), r07])
        (by rw [hk _ (by unfold RbK; omega), G11 _ (by unfold RbK; omega), K1 _ (by omega), r13])
        h20 (by rw [hk _ (by unfold RbK; omega), G11 _ (by unfold RbK; omega), a21])
        (by rw [hk _ (by unfold RbK; omega), G11 _ (by unfold RbK; omega), a23])
        (by rw [hk _ (by unfold RbK; omega), G11 _ (by unfold RbK; omega), a25]) hl (by omega)
        (by omega) (by omega) (by rw [L' _ (by omega)]; exact wdg _ (by omega))
        (by rw [L' _ (by omega)]; exact hcf i hi) (by omega) (by omega) (by omega)
      refine ⟨c'', k, ex, hk'.le, g20, gk, ?_, gr, grm, go⟩
      rw [gm, L' _ (by omega), L' _ (by omega), L' _ (by omega)]
      rfl)
  have G12 : ∀ x, RbK x → c₁₂.nreg x = c₇.nreg x := fun x hx => by rw [f₁₂ x hx, G11 x hx]
  have qHD : ∀ a < 3 * m, c₁₂.nmem (S + 2 * (m + 2) + 3 * m + a) =
      rbHd m (fun i => mem₀ (SGb + i)) (fun i => mem₀ (RVb + i))
        (rbSrc mem₀ Z CFb LABb DVb DGb) a := fun a ha => by
    unfold rbHd
    by_cases h2 : a < 2 * m
    · rw [iteT h2, o₁₂ _ (fun j hj => by omega), m₁₁]
      rcases Nat.even_or_odd' a with ⟨i, rfl | rfl⟩
      · rw [iteT (show 2 * i % 2 = 0 by omega), show 2 * i / 2 = i by omega,
          o₁₀ _ (fun j hj => by omega), m₉]
        have h3 := v₈ i (by omega)
        simp only [add_zero] at h3
        exact h3
      · rw [iteF (show ¬ (2 * i + 1) % 2 = 0 by omega), show (2 * i + 1) / 2 = i by omega]
        have h3 := v₁₀ i (by omega)
        rw [← add_assoc]
        exact h3
    · rw [iteF h2]
      have h3 := v₁₂ (a - 2 * m) (by omega)
      have e : S + 2 * (m + 2) + 3 * m + 1 * (a - 2 * m) + 2 * m =
        S + 2 * (m + 2) + 3 * m + a := by omega
      rw [e] at h3
      rw [h3, rbHd_src (rbSrc_le (hcf _ (by omega)))]
  refine ⟨c₁₂, t₈ + (t₉ + (t₁₀ + (t₁₁ + t₁₂))), .seq e₈ (.seq e₉ (.seq e₁₀ (.seq e₁₁ e₁₂))),
    ?_, qHD, fun a ha => ?_, fun x hx => G12 x hx, ?_, ?_, ?_⟩
  · clear * - ht₈ ht₉ ht₁₀ ht₁₁ ht₁₂; omega
  · rw [o₁₂ a (fun j hj => by omega), m₁₁, o₁₀ a (fun j hj => by omega), m₉,
      o₈ a (fun j hj => by omega)]
  · rw [rr₁₂, rr₁₁, rr₁₀, rr₉, rr₈]
  · rw [rm₁₂, rm₁₁, rm₁₀, rm₉, rm₈]
  · rw [oo₁₂, oo₁₁, oo₁₀, oo₉, oo₈]

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The residual reachability on the machine**: the marks `MK[u]` (`u < m + 2`) are the reach
bits of the dart graph of `NcMath.lean` built from the residual bits `rbRes` and the source bits
`rbSrc`. Layout: inputs below `S`; `OB | OE | OL | HD | MK | Q` from `S`. -/
theorem rbP_exec (c : Config) (hc : WordsBounded W c)
    {m FLb CPb Z CFb LABb DVb DGb SGb RVb S : ℕ}
    (r00 : c.nreg 9600 = m) (r01 : c.nreg 9601 = FLb) (r02 : c.nreg 9602 = CPb)
    (r03 : c.nreg 9603 = Z) (r04 : c.nreg 9604 = CFb) (r05 : c.nreg 9605 = LABb)
    (r06 : c.nreg 9606 = DVb) (r07 : c.nreg 9607 = DGb) (r08 : c.nreg 9608 = SGb)
    (r09 : c.nreg 9609 = RVb) (r10 : c.nreg 9610 = S) (r11 : c.nreg 9611 = S + (m + 2))
    (r12 : c.nreg 9612 = S + 2 * (m + 2)) (r13 : c.nreg 9613 = S + 2 * (m + 2) + 3 * m)
    (r14 : c.nreg 9614 = S + 2 * (m + 2) + 6 * m) (r15 : c.nreg 9615 = S + 3 * (m + 2) + 6 * m)
    (iFL : FLb + m ≤ S) (iCP : CPb + m ≤ S) (iCF : CFb + m ≤ S) (iLAB : LABb + m ≤ S)
    (iDV : DVb + m ≤ S) (iDG : DGb + m ≤ S) (iSG : SGb + m ≤ S) (iRV : RVb + m ≤ S)
    (wS : S + 4 * (m + 2) + 6 * m + 1 ≤ W)
    (hlab : ∀ i < m, 1 ≤ c.nmem (LABb + i) ∧ c.nmem (LABb + i) ≤ m)
    (hcf : ∀ i < m, c.nmem (CFb + i) ≤ 1)
    (hsg : ∀ i < m, c.nmem (SGb + i) < m) (hrv : ∀ i < m, c.nmem (RVb + i) < m)
    (wcp : ∀ i < m, c.nmem (CPb + i) + Z ≤ W)
    (wdg : ∀ v < m, c.nmem (DGb + v) * Z ≤ W) :
    ∃ c' t, Exec P W rbP c c' t ∧ t ≤ rbCost m ∧
      (∀ u < m + 2, c'.nmem (S + 2 * (m + 2) + 6 * m + u) =
        if Relation.ReflTransGen (NegSSSP.BfsAdj (rbOb m) (rbOe m (rbRes c.nmem FLb CPb Z)) id
          (rbHd m (fun i => c.nmem (SGb + i)) (fun i => c.nmem (RVb + i))
            (rbSrc c.nmem Z CFb LABb DVb DGb))) m u then 1 else 0) ∧
      (∀ a, (a < S ∨ S + 4 * (m + 2) + 6 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 1400 ∨ (1419 < r ∧ r < 9620) ∨ 9646 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  obtain ⟨c₇, tA, eA, htA, qOB, qOE, qOL, LA, KA, n₇, a21, a22, a23, a25, a26, rrA, rmA, ooA⟩ :=
    rbA1_exec (P := P) c hc r00 r01 r02 r03 r04 r05 r06 r07 r08 r09 r10 r11 r12 r13 r14 r15 iFL
      iCP iCF iLAB iDV iDG iSG iRV wS hlab hcf hsg hrv wcp wdg
  have L7 : ∀ a, a < S → c₇.nmem a = c.nmem a := fun a ha => LA a (Or.inl ha)
  obtain ⟨c₁₂, tB', eB, htB, qHD', LB, KB, rrB, rmB, ooB⟩ := rbA2_exec (P := P) c₇ eA.wb_right
    (by rw [KA _ (by omega), r00]) (by rw [KA _ (by omega), r03]) (by rw [KA _ (by omega), r04])
    (by rw [KA _ (by omega), r05]) (by rw [KA _ (by omega), r06]) (by rw [KA _ (by omega), r07])
    (by rw [KA _ (by omega), r08]) (by rw [KA _ (by omega), r09]) (by rw [KA _ (by omega), r13])
    n₇ a21 a22 a23 a25 iCF iLAB iDV iDG iSG iRV wS
    (fun i hi => by rw [L7 _ (by omega)]; exact hlab i hi)
    (fun i hi => by rw [L7 _ (by omega)]; exact hcf i hi)
    (fun v hv => by rw [L7 _ (by omega)]; exact wdg v hv)
  have qHD : ∀ a < 3 * m, c₁₂.nmem (S + 2 * (m + 2) + 3 * m + a) =
      rbHd m (fun i => c.nmem (SGb + i)) (fun i => c.nmem (RVb + i))
        (rbSrc c.nmem Z CFb LABb DVb DGb) a := fun a ha => by
    rw [qHD' a ha]
    unfold rbHd rbSrc
    by_cases h2 : a < 2 * m
    · rw [iteT h2, iteT h2]
      split_ifs
      · exact L7 _ (by omega)
      · exact L7 _ (by omega)
    · rw [iteF h2, iteF h2, L7 (CFb + (a - 2 * m)) (by omega), L7 (LABb + (a - 2 * m)) (by omega),
        L7 _ (by have := hlab (a - 2 * m) (by omega); omega),
        L7 _ (by have := hlab (a - 2 * m) (by omega); omega)]
  have LH : ∀ a, (a < S ∨ S + 2 * (m + 2) + 6 * m ≤ a) → c₁₂.nmem a = c.nmem a := fun a ha => by
    rw [LB a (by omega), LA a (by omega)]
  have qOB' : ∀ u < m + 2, c₁₂.nmem (S + u) = rbOb m u := fun u hu => by
    rw [LB _ (by omega)]; exact qOB u hu
  have qOE' : ∀ u < m + 2, c₁₂.nmem (S + (m + 2) + u) = rbOe m (rbRes c.nmem FLb CPb Z) u :=
    fun u hu => by rw [LB _ (by omega)]; exact qOE u hu
  have qOL' : ∀ k < 3 * m, c₁₂.nmem (S + 2 * (m + 2) + k) = id k := fun k hk => by
    rw [LB _ (by omega)]; exact qOL k hk
  obtain ⟨c₁₃, t₁₃, e₁₃, ht₁₃, b0, b1, b2, b3, b4, b5, b6, b7, f₁₃, m₁₃, rr₁₃, rm₁₃, oo₁₃⟩ :=
    tB_exec (P := P) c₁₂ eB.wb_right
  have hres1 : ∀ u, rbRes c.nmem FLb CPb Z u ≤ 1 := fun u => bit_le _ _
  have hIn : NegSSSP.BfsIn (m + 2) (3 * m) (3 * m) m S (S + (m + 2)) (S + 2 * (m + 2))
      (S + 2 * (m + 2) + 3 * m) (rbOb m) (rbOe m (rbRes c.nmem FLb CPb Z)) id
      (rbHd m (fun i => c.nmem (SGb + i)) (fun i => c.nmem (RVb + i))
        (rbSrc c.nmem Z CFb LABb DVb DGb)) c₁₃.nmem := {
    s_lt := by omega,
    hob := fun u hu => by rw [m₁₃]; exact qOB' u hu,
    hoe := fun u hu => by rw [m₁₃]; exact qOE' u hu,
    ble := fun u hu => by
      unfold rbOb rbOe; split_ifs <;> omega,
    ole := fun u hu => by
      unfold rbOe; split_ifs
      · have := hres1 u; omega
      · omega,
    hol := fun i hi => by rw [m₁₃]; exact qOL' i hi,
    ol_lt := fun i hi => hi,
    hhd := fun a ha => by rw [m₁₃]; exact qHD a ha,
    hd_lt := fun a ha => by
      unfold rbHd; split_ifs
      · exact (hsg _ (by omega)).trans (by omega)
      · exact (hrv _ (by omega)).trans (by omega)
      · omega
      · omega,
    deg := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hb : ∑ u ∈ Finset.range m, (rbOe m (rbRes c.nmem FLb CPb Z) u - rbOb m u) ≤
          ∑ u ∈ Finset.range m, 2 := Finset.sum_le_sum fun u hu => by
        have := Finset.mem_range.1 hu
        have := hres1 u
        unfold rbOe rbOb; rw [iteT (by omega), iteT (by omega)]; omega
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hb
      have e1 : rbOe m (rbRes c.nmem FLb CPb Z) m - rbOb m m = m := by
        unfold rbOe rbOb; rw [iteF (show ¬ m < m by omega), iteT (le_refl m)]; omega
      have e2 : rbOe m (rbRes c.nmem FLb CPb Z) (m + 1) - rbOb m (m + 1) = 0 := by
        unfold rbOe rbOb; rw [iteF (by omega), iteF (by omega)]; omega
      rw [e1, e2]; omega }
  obtain ⟨c₁₄, t₁₄, e₁₄, ht₁₄, hMK, k₁₄, f₁₄, rr₁₄, rm₁₄, oo₁₄⟩ := NegSSSP.bfsProg_exec (P := P)
    (W := W) (Ib := S + 2 * (m + 2) + 6 * m) (Mb := S + 2 * (m + 2) + 6 * m)
    (Qb := S + 3 * (m + 2) + 6 * m) ⟨by omega, by omega, by omega, by omega, le_rfl, by omega,
      by omega⟩ c₁₃ e₁₃.wb_right
    (by rw [b0, KB _ (by unfold RbK; omega), a26]) (by rw [b1, KB _ (by unfold RbK; omega), KA _ (by omega), r00])
    (by rw [b2, KB _ (by unfold RbK; omega), KA _ (by omega), r10]) (by rw [b3, KB _ (by unfold RbK; omega), KA _ (by omega), r11])
    (by rw [b4, KB _ (by unfold RbK; omega), KA _ (by omega), r12]) (by rw [b5, KB _ (by unfold RbK; omega), KA _ (by omega), r13])
    (by rw [b6, KB _ (by unfold RbK; omega), KA _ (by omega), r14]) (by rw [b7, KB _ (by unfold RbK; omega), KA _ (by omega), r15]) hIn
  have FR := NcStep.Exec.nreg_frame e₁₄ bfsProg_regsOK bfsProg_noRand
  refine ⟨c₁₄, tA + (tB' + (t₁₃ + t₁₄)), .seq eA (.seq eB (.seq e₁₃ e₁₄)), ?_,
    fun u hu => hMK u hu,
    fun a ha => ?_, fun r hr => ?_, by rw [rr₁₄, rr₁₃, rrB, rrA], by rw [rm₁₄, rm₁₃, rmB, rmA],
    by rw [oo₁₄, oo₁₃, ooB, ooA]⟩
  · unfold rbCost; clear * - htA htB ht₁₃ ht₁₄; omega
  · rw [k₁₄ a (by omega), m₁₃, LH a (by omega)]
  · rw [FR r (by simp only [decide_eq_false_iff_not]; omega), f₁₃ r (by omega), KB r (by unfold RbK; omega), KA r (by omega)]


end NcStep

end BKMNW

end PlanarFlow
