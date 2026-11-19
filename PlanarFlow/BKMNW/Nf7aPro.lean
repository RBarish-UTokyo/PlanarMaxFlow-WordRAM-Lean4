module

public import PlanarFlow.BKMNW.Nf7aSt
public import PlanarFlow.BKMNW.Nf7aSem

/-!
# The prologue of `fixP`: the values and the register blocks

* **`FpIn`**: the input of the prologue as natural data (the frame at `d` with `m` darts, the
  parts of the separator at `Gb` (`ns` parts, the part `j` at offset `off` with `k` darts), the
  offset `Z` of the flow array, the memory); its derived values: `PD` (frame indices of the
  darts of the path), `RV`, `CP`, `FLW`, the face labels `lab` (`olab` of `NX`, plus `1`), the
  marks `ON`, `MK0`, the walk `tw`/`tt` and the corner walk **`cw`**, `AS` (sum of the
  capacities), `K`, the vertex labels `vl`, the net outflow words `DVw`, the corner numbers `ix`;
* the register blocks `pinA`, `pinB`, `pinC`, `pinD` of the prologue (`pinA_exec`, …).
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

/-- **The input of the prologue** as natural data. -/
structure FpIn where
  d : ℕ
  m : ℕ
  Gb : ℕ
  ns : ℕ
  off : ℕ
  k : ℕ
  Z : ℕ
  mem : ℕ → ℕ

namespace FpIn

variable (p : FpIn)

/-- The base of the frame indices of the darts of the path. -/
def PDb : ℕ := p.Gb + 1 + p.ns + p.ns + p.off
/-- The frame index of the dart `d l` of the path. -/
def PD (l : ℕ) : ℕ := p.mem (p.PDb + l)
/-- The reverse (frame indices). -/
def RV (i : ℕ) : ℕ := p.mem (p.d + 4 + p.m + i)
/-- The capacities. -/
def CP (i : ℕ) : ℕ := p.mem (p.d + 4 + p.m + p.m + p.m + i)
/-- The flow array (`Z + f₀`). -/
def FLW (i : ℕ) : ℕ := p.mem (p.d + 4 + p.m + p.m + p.m + p.m + p.m + p.m + i)
/-- The face labels plus one. -/
noncomputable def lab (i : ℕ) : ℕ := OrbLab.olab (MfDrv.nxF p.d p.m p.mem) i + 1
/-- The marks of the darts of the path. -/
def ON : ℕ → ℕ := fmk2 (fun _ => 0) p.PD (fun l => p.RV (p.PD l)) p.k
/-- The marks of the faces of the path (by label). -/
noncomputable def MK0 (a : ℕ) : ℕ :=
  if a ≤ p.m then fmk2 (fun _ => 0) (fun l => p.lab (p.PD l)) (fun l => p.lab (p.RV (p.PD l))) p.k a
  else 0
/-- The walk around the path on indices. -/
def tw (i : ℕ) : ℕ := if 0 < p.ON i then MfDrv.nxF p.d p.m p.mem i else MfDrv.sgF p.d p.m p.mem i
/-- The index after `n` steps of the walk. -/
def tt (n : ℕ) : ℕ := p.tw^[n] (p.PD 0)
/-- **The corner walk** (`m` steps). -/
noncomputable def cw : CwSt := cwRun (fun n => p.lab (p.tt n)) p.tt p.MK0 p.m
/-- The sum of the capacities. -/
def AS : ℕ := ∑ i ∈ range p.m, p.CP i
/-- The offset of the signed words. -/
def K : ℕ := 16 * fpB p.AS p.m p.k
/-- The vertex labels. -/
noncomputable def vl (i : ℕ) : ℕ := OrbLab.olab (MfDrv.sgF p.d p.m p.mem) i
/-- The net outflow word at the tail of `d l`. -/
noncomputable def DVw (l : ℕ) : ℕ :=
  MfDrv.dvS p.vl p.FLW p.m (p.vl (p.PD l)) + p.K - MfDrv.dvC p.vl p.m (p.vl (p.PD l)) * p.Z
/-- The corner number of the face of the frame dart `i`. -/
noncomputable def ix (i : ℕ) : ℕ := p.cw.mks (p.lab i) - 2

/-- The base of the arrays `Q = A0 + 9m + 1`. -/
def Qb (A0 : ℕ) : ℕ := A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m + p.m

end FpIn

/-! ### The register blocks -/

/-- The sizes, the offsets and the bases of the frame. -/
def pinA : Stmt :=
  block [.loadN 9400 3004, .copyN 9403 3006, .constN 9436 1, .constN 9437 3, .constN 9438 4,
    .addN 9425 3004 9437, .loadN 9421 9425, .loadN 9432 6807, .addN 9425 6807 9436,
    .addN 9426 9425 6800, .loadN 9433 9426, .addN 9426 9426 9432, .loadN 9401 9426,
    .addN 9402 9425 9432, .addN 9402 9402 9432, .addN 9402 9402 9433, .addN 9427 3004 9438,
    .addN 9430 9427 9400, .addN 9431 9430 9400, .addN 9434 9431 9400, .addN 9435 9434 9400,
    .addN 9435 9435 9400, .addN 9435 9435 9400, .copyN 9371 9401]

/-- The bases of the arrays. -/
def pinB : Stmt :=
  block [.copyN 9404 9403, .addN 9405 9404 9400, .addN 9406 9405 9400, .addN 9407 9406 9400,
    .addN 9408 9407 9400, .addN 9408 9408 9436, .addN 9409 9408 9400, .addN 9409 9409 9400,
    .addN 9409 9409 9400, .addN 9410 9409 9400, .addN 9411 9410 9400, .copyN 9374 9411,
    .addN 9375 9374 9401, .addN 9376 9375 9401, .addN 9377 9376 9401, .addN 9412 9377 9401,
    .addN 9412 9412 9401, .addN 9413 9412 9401, .addN 9414 9413 9401, .addN 9415 9414 9401,
    .addN 9415 9415 9401, .addN 9416 9415 9401, .addN 9416 9416 9401, .addN 9417 9416 9401,
    .addN 9417 9417 9401, .addN 9418 9417 9401, .addN 9418 9418 9401]

/-- The arguments of `mzFill`, `gaProg`, `olProg`, `dvP`. -/
def pinC : Stmt :=
  block [.addN 5030 9400 9400, .addN 5030 5030 9400, .addN 5030 5030 9436, .copyN 5031 9405,
    .copyN 4470 9400, .copyN 4471 9430, .copyN 4472 9431, .copyN 4473 9404, .copyN 7350 9404,
    .copyN 7351 9405, .copyN 7352 9400, .copyN 8430 9408]

/-- The number of corners. -/
def pinD : Stmt := block [.copyN 9419 9442]

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1600000 in
theorem pinA_exec (c : Config) (hc : WordsBounded W c) {d A0 Gb j m Z ns off k : ℕ}
    (r04 : c.nreg 3004 = d) (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = Gb)
    (r00 : c.nreg 6800 = j) (hm : c.nmem d = m) (hZ : c.nmem (d + 3) = Z)
    (hns : c.nmem Gb = ns) (hoff : c.nmem (Gb + 1 + j) = off) (hk : c.nmem (Gb + 1 + j + ns) = k)
    (hW : d + Gb + j + ns + ns + off + 6 * m + 8 ≤ W) :
    ∃ c' t, Exec P W pinA c c' t ∧ t = 24 ∧ c'.nreg 9400 = m ∧ c'.nreg 9403 = A0 ∧
      c'.nreg 9436 = 1 ∧ c'.nreg 9421 = Z ∧ c'.nreg 9401 = k ∧ c'.nreg 9371 = k ∧
      c'.nreg 9402 = Gb + 1 + ns + ns + off ∧ c'.nreg 9430 = d + 4 + m ∧
      c'.nreg 9431 = d + 4 + m + m ∧ c'.nreg 9434 = d + 4 + m + m + m ∧
      c'.nreg 9435 = d + 4 + m + m + m + m + m + m ∧
      (∀ r, r ≠ 9371 → (r < 9400 ∨ 9438 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pinA
  exec_block
  all_goals try ((try config_simp) <;>
    (try simp only [r04, r06, r07, r00, hm, hZ, hns, hoff, hk]) <;> omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r04, r06, r07, r00, hm, hZ, hns, hoff, hk])
  all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

set_option maxHeartbeats 1600000 in
theorem pinB_exec (c : Config) (hc : WordsBounded W c) {A0 m k : ℕ}
    (r03 : c.nreg 9403 = A0) (r00 : c.nreg 9400 = m) (r01 : c.nreg 9401 = k)
    (r36 : c.nreg 9436 = 1) (hW : A0 + 9 * m + 15 * k + 1 ≤ W) :
    ∃ c' t, Exec P W pinB c c' t ∧ t = 27 ∧ c'.nreg 9404 = A0 ∧ c'.nreg 9405 = A0 + m ∧
      c'.nreg 9406 = A0 + m + m ∧ c'.nreg 9407 = A0 + m + m + m ∧
      c'.nreg 9408 = A0 + m + m + m + m + 1 ∧
      c'.nreg 9409 = A0 + m + m + m + m + 1 + m + m + m ∧
      c'.nreg 9410 = A0 + m + m + m + m + 1 + m + m + m + m ∧
      c'.nreg 9411 = A0 + m + m + m + m + 1 + m + m + m + m + m ∧
      c'.nreg 9374 = A0 + m + m + m + m + 1 + m + m + m + m + m ∧
      c'.nreg 9375 = A0 + m + m + m + m + 1 + m + m + m + m + m + k ∧
      c'.nreg 9376 = A0 + m + m + m + m + 1 + m + m + m + m + m + k + k ∧
      c'.nreg 9377 = A0 + m + m + m + m + 1 + m + m + m + m + m + k + k + k ∧
      c'.nreg 9412 = A0 + m + m + m + m + 1 + m + m + m + m + m + k + k + k + k + k ∧
      c'.nreg 9413 = A0 + m + m + m + m + 1 + m + m + m + m + m + k + k + k + k + k + k ∧
      c'.nreg 9414 = A0 + m + m + m + m + 1 + m + m + m + m + m + k + k + k + k + k + k + k ∧
      c'.nreg 9415 = A0 + m + m + m + m + 1 + m + m + m + m + m + k + k + k + k + k + k + k + k +
        k ∧
      c'.nreg 9416 = A0 + m + m + m + m + 1 + m + m + m + m + m + k + k + k + k + k + k + k + k +
        k + k + k ∧
      c'.nreg 9417 = A0 + m + m + m + m + 1 + m + m + m + m + m + k + k + k + k + k + k + k + k +
        k + k + k + k + k ∧
      c'.nreg 9418 = A0 + m + m + m + m + 1 + m + m + m + m + m + k + k + k + k + k + k + k + k +
        k + k + k + k + k + k + k ∧
      (∀ r, (r < 9374 ∨ 9377 < r) → (r < 9404 ∨ 9418 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pinB
  exec_block
  all_goals try ((try config_simp) <;> (try simp only [r03, r00, r01, r36]) <;> omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r03, r00, r01, r36])
  all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

theorem pinC_exec (c : Config) (hc : WordsBounded W c) {m : ℕ}
    (r00 : c.nreg 9400 = m) (r36 : c.nreg 9436 = 1) (hW : 3 * m + 1 ≤ W) :
    ∃ c' t, Exec P W pinC c c' t ∧ t = 12 ∧ c'.nreg 5030 = 3 * m + 1 ∧
      c'.nreg 5031 = c.nreg 9405 ∧ c'.nreg 4470 = m ∧ c'.nreg 4471 = c.nreg 9430 ∧
      c'.nreg 4472 = c.nreg 9431 ∧ c'.nreg 4473 = c.nreg 9404 ∧ c'.nreg 7350 = c.nreg 9404 ∧
      c'.nreg 7351 = c.nreg 9405 ∧ c'.nreg 7352 = m ∧ c'.nreg 8430 = c.nreg 9408 ∧
      (∀ r, r ≠ 5030 → r ≠ 5031 → (r < 4470 ∨ 4473 < r) → (r < 7350 ∨ 7352 < r) →
        r ≠ 8430 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pinC
  exec_block
  all_goals try ((try config_simp) <;> (try simp only [r00, r36]) <;> omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl,
    rfl⟩
  all_goals config_simp
  all_goals try (simp only [r00, r36])
  all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

theorem pinD_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W pinD c c' t ∧ t = 1 ∧ c'.nreg 9419 = c.nreg 9442 ∧
      (∀ r, r ≠ 9419 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pinD
  exec_block
  refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

end BKMNW

end PlanarFlow
