module

public import PlanarFlow.BKMNW.StMapA

/-!
# The map part of the s-t flow encoding: the program and its stages

For a map `M` whose darts are numbered `0 … m-1` by `en` (`NsStep.EnumOK`), with the index
arrays `RV` (reverse) at `RVb` and `RT` (rotation) at `RTb`, the program **`smP`** writes at `β`
the words of Klein's encoding `Klein.KInput` of the **dual** `M.dual` (no piece: `IS = 0`) for the
node layout

* vertex of the dual (face `y` of `M`): `labI M en m i + 1` for a dart `en i` of `y`;
* edge of the spanning tree: `m + 1 + min i RV[i]`;
* face of the dual (vertex `v` of `M`): `2 m + 1 + labI M.dual en m i` for a dart `en i` at `v`;
* edge of the cotree: `3 m + 1 + min i RV[i]`;

with the offsets of `Klein.iRV … Klein.iED` for `nD = m`: `RV` at `β`, `NF` at `β + m`, `NE` at
`β + 2m`, `NG` at `β + 3m`, `NT` at `β + 4m`, `NH` at `β + 5m`, `IS`, `LN` at `β + 6m`, `β + 7m`
(zero), `ED` at `β + 8m` (indexed by the nodes). Scratch `[S, S + 3m)` (`NX`, `LABF`, `LABV`),
zero at the end.

Registers: inputs `7700 = m`, `7701 = RVb`, `7702 = RTb`, `7703 = S`, `7704 = β`; layout
`7705 … 7722`; the loops `cpArr` (`4910 … 4916`), `lgProg` (`6210 … 6217`), `mzFill`
(`5030 … 5035`), `olProg` (`7350 … 7352`, `7400 … 7405`), `laProg` (`7730 … 7737`), `edgProg`
(`1800 … 1816`).

This file: the program, the stages' register blocks and the first stages (`smA_exec`: layout,
`RV`, the face permutation `NX`; `smB_exec`: the two label arrays).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

open Finset Function CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  OrbLab NsStep

/-! ### The program -/

/-- The layout registers. -/
def smL : Stmt :=
  block [.constN 7721 1, .addN 7706 7703 7700, .addN 7707 7706 7700,
    .addN 7708 7704 7700, .addN 7719 7708 7700, .addN 7718 7719 7700, .addN 7709 7718 7700,
    .addN 7710 7709 7700, .addN 7711 7710 7700, .addN 7712 7711 7700, .addN 7713 7712 7700,
    .addN 7716 7700 7700, .addN 7714 7700 7721, .addN 7715 7716 7714, .addN 7720 7716 7700]

/-- `RV` copied to `β`. -/
def smRV : Stmt := .seq (block [.copyN 4910 7700, .copyN 4911 7701, .copyN 4912 7704]) cpArr

/-- The face permutation `NX[i] := RT[RV[i]]` at `S`. -/
def smNX : Stmt :=
  .seq (block [.copyN 6210 7700, .copyN 6211 7701, .copyN 6212 7702, .copyN 6213 7703]) lgProg

/-- Zero `[S + m, S + 3m)`. -/
def smZL : Stmt := .seq (block [.copyN 5030 7716, .copyN 5031 7706]) mzFill

/-- The face labels at `S + m`. -/
def smLF : Stmt := .seq (block [.copyN 7350 7703, .copyN 7351 7706, .copyN 7352 7700]) olProg

/-- The vertex labels at `S + 2m`. -/
def smLV : Stmt := .seq (block [.copyN 7350 7702, .copyN 7351 7707, .copyN 7352 7700]) olProg

/-- `NT` (the face labels) at `β + 4m`. -/
def smNT : Stmt := .seq (block [.copyN 4910 7700, .copyN 4911 7706, .copyN 4912 7709]) cpArr

/-- `NF` (the vertex labels plus `2m`) at `β + m`. -/
def smNF : Stmt :=
  .seq (block [.copyN 7730 7700, .copyN 7731 7707, .copyN 7732 7708, .copyN 7733 7716]) laProg

/-- The edge arrays: `NH` at `β + 5m`, `NG` at `β + 6m`, `NE` at `β + 7m`, `ED` at `β + 8m`. -/
def smED : Stmt :=
  .seq (block [.copyN 1800 7700, .copyN 1801 7704, .copyN 1802 7709, .copyN 1803 7710,
    .copyN 1804 7714, .copyN 1805 7711, .copyN 1806 7715, .copyN 1807 7712, .copyN 1808 7713])
    NegSSSP.edgProg

/-- `NG` moved to `β + 3m`. -/
def smNG : Stmt := .seq (block [.copyN 4910 7700, .copyN 4911 7711, .copyN 4912 7718]) cpArr

/-- `NE` moved to `β + 2m`. -/
def smNE : Stmt := .seq (block [.copyN 4910 7700, .copyN 4911 7712, .copyN 4912 7719]) cpArr

/-- `IS`, `LN` zero. -/
def smZI : Stmt := .seq (block [.copyN 5030 7716, .copyN 5031 7711]) mzFill

/-- The scratch zero again. -/
def smZS : Stmt := .seq (block [.copyN 5030 7720, .copyN 5031 7703]) mzFill

/-- Stage A: the layout, `RV`, `NX`. -/
def smA : Stmt := .seq smL (.seq smRV smNX)

/-- Stage B: the labels. -/
def smB : Stmt := .seq smZL (.seq smLF smLV)

/-- Stage C: `NT`, `NF`. -/
def smC : Stmt := .seq smNT smNF

/-- Stage E: `NG`, `NE` in place, `IS`, `LN`, scratch zero. -/
def smE : Stmt := .seq smNG (.seq smNE (.seq smZI smZS))

/-- **The map part of the s-t flow encoding.** -/
def smP : Stmt := .seq smA (.seq smB (.seq smC (.seq smED smE)))

/-- The registers `smP` may write. -/
def SmScr (r : ℕ) : Prop :=
  (7705 ≤ r ∧ r ≤ 7737) ∨ (4910 ≤ r ∧ r ≤ 4916) ∨ (6210 ≤ r ∧ r ≤ 6217) ∨
    (5030 ≤ r ∧ r ≤ 5035) ∨ (7350 ≤ r ∧ r ≤ 7352) ∨ (7400 ≤ r ∧ r ≤ 7405) ∨
    (1800 ≤ r ∧ r ≤ 1816)

/-! ### The layout registers -/

variable {P : Input} {W : ℕ}

/-- The layout registers after `smL`. -/
def SmRegs (c : Config) (m RVb RTb S β : ℕ) : Prop :=
  c.nreg 7700 = m ∧ c.nreg 7701 = RVb ∧ c.nreg 7702 = RTb ∧ c.nreg 7703 = S ∧ c.nreg 7704 = β ∧
    c.nreg 7706 = S + m ∧ c.nreg 7707 = S + 2 * m ∧ c.nreg 7708 = β + m ∧
    c.nreg 7719 = β + 2 * m ∧ c.nreg 7718 = β + 3 * m ∧ c.nreg 7709 = β + 4 * m ∧
    c.nreg 7710 = β + 5 * m ∧ c.nreg 7711 = β + 6 * m ∧ c.nreg 7712 = β + 7 * m ∧
    c.nreg 7713 = β + 8 * m ∧ c.nreg 7716 = 2 * m ∧ c.nreg 7714 = m + 1 ∧
    c.nreg 7715 = 3 * m + 1 ∧ c.nreg 7720 = 3 * m

lemma SmRegs.of {c d : Config} {m RVb RTb S β : ℕ} (h : SmRegs c m RVb RTb S β)
    (hd : ∀ r, 7700 ≤ r → r ≤ 7722 → d.nreg r = c.nreg r) : SmRegs d m RVb RTb S β := by
  obtain ⟨a0, a1, a2, a3, a4, a6, a7, a8, a19, a18, a9, a10, a11, a12, a13, a16, a14, a15,
    a20⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hd _ (by omega) (by omega)] <;> assumption

theorem smL_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb S β : ℕ}
    (r00 : c.nreg 7700 = m) (r01 : c.nreg 7701 = RVb) (r02 : c.nreg 7702 = RTb)
    (r03 : c.nreg 7703 = S) (r04 : c.nreg 7704 = β) (w1 : S + 3 * m ≤ W)
    (w2 : β + 8 * m ≤ W) (w3 : 3 * m + 1 ≤ W) :
    ∃ c' t, Exec P W smL c c' t ∧ t = 15 ∧ SmRegs c' m RVb RTb S β ∧
      (∀ r, (r < 7705 ∨ 7722 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smL
  exec_block
  all_goals try ((try config_simp); (try simp only [r00, r01, r02, r03, r04]); omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; simp only [r00, r01, r02, r03, r04]; try omega)
  all_goals try (config_simp; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

/-! ### The argument blocks -/

theorem setRV_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (block [.copyN 4910 7700, .copyN 4911 7701, .copyN 4912 7704]) c c' t ∧
      t = 3 ∧ c'.nreg 4910 = c.nreg 7700 ∧ c'.nreg 4911 = c.nreg 7701 ∧
      c'.nreg 4912 = c.nreg 7704 ∧
      (∀ r, (r < 4910 ∨ 4912 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

theorem setNX_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (block [.copyN 6210 7700, .copyN 6211 7701, .copyN 6212 7702,
      .copyN 6213 7703]) c c' t ∧ t = 4 ∧ c'.nreg 6210 = c.nreg 7700 ∧
      c'.nreg 6211 = c.nreg 7701 ∧ c'.nreg 6212 = c.nreg 7702 ∧ c'.nreg 6213 = c.nreg 7703 ∧
      (∀ r, (r < 6210 ∨ 6213 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

/-- A block setting the arguments of `mzFill` from two registers. -/
theorem setZ_exec (c : Config) (hc : WordsBounded W c) (a b : ℕ) :
    ∃ c' t, Exec P W (block [.copyN 5030 a, .copyN 5031 b]) c c' t ∧ t = 2 ∧
      c'.nreg 5030 = c.nreg a ∧ c'.nreg 5031 = (upd c.nreg 5030 (c.nreg a)) b ∧
      (∀ r, (r < 5030 ∨ 5031 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

/-- A block setting the arguments of `olProg` from three registers. -/
theorem setO3_exec (c : Config) (hc : WordsBounded W c) (a b e : ℕ) (ha : a ∉ [7350, 7351])
    (hb : b ∉ [7350, 7351]) (he : e ∉ [7350, 7351]) :
    ∃ c' t, Exec P W (block [.copyN 7350 a, .copyN 7351 b, .copyN 7352 e]) c c' t ∧ t = 3 ∧
      c'.nreg 7350 = c.nreg a ∧ c'.nreg 7351 = c.nreg b ∧ c'.nreg 7352 = c.nreg e ∧
      (∀ r, (r < 7350 ∨ 7352 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha hb he
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  all_goals try (config_simp; simp only [upd_apply]; split_ifs <;> simp_all; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

/-- A block setting the arguments of `cpArr` from three registers (none of them `4910 … 4912`). -/
theorem setC3_exec (c : Config) (hc : WordsBounded W c) (a b e : ℕ) (ha : 4912 < a)
    (hb : 4912 < b) (he : 4912 < e) :
    ∃ c' t, Exec P W (block [.copyN 4910 a, .copyN 4911 b, .copyN 4912 e]) c c' t ∧ t = 3 ∧
      c'.nreg 4910 = c.nreg a ∧ c'.nreg 4911 = c.nreg b ∧ c'.nreg 4912 = c.nreg e ∧
      (∀ r, (r < 4910 ∨ 4912 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

theorem setNF_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (block [.copyN 7730 7700, .copyN 7731 7707, .copyN 7732 7708,
      .copyN 7733 7716]) c c' t ∧ t = 4 ∧ c'.nreg 7730 = c.nreg 7700 ∧
      c'.nreg 7731 = c.nreg 7707 ∧ c'.nreg 7732 = c.nreg 7708 ∧ c'.nreg 7733 = c.nreg 7716 ∧
      (∀ r, (r < 7730 ∨ 7733 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

theorem setED_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (block [.copyN 1800 7700, .copyN 1801 7704, .copyN 1802 7709,
      .copyN 1803 7710, .copyN 1804 7714, .copyN 1805 7711, .copyN 1806 7715, .copyN 1807 7712,
      .copyN 1808 7713]) c c' t ∧ t = 9 ∧ c'.nreg 1800 = c.nreg 7700 ∧
      c'.nreg 1801 = c.nreg 7704 ∧ c'.nreg 1802 = c.nreg 7709 ∧ c'.nreg 1803 = c.nreg 7710 ∧
      c'.nreg 1804 = c.nreg 7714 ∧ c'.nreg 1805 = c.nreg 7711 ∧ c'.nreg 1806 = c.nreg 7715 ∧
      c'.nreg 1807 = c.nreg 7712 ∧ c'.nreg 1808 = c.nreg 7713 ∧
      (∀ r, (r < 1800 ∨ 1808 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

end StEnc

end BKMNW

end PlanarFlow
