module

public import PlanarFlow.BKMNW.Nf7bI
public import PlanarFlow.BKMNW.Nf7aCor
public import PlanarFlow.BKMNW.FrImE

/-!
# Step 2 of `fixP`: the register blocks

Step 2 of `fixP` (after the prologue `fpPro`): the MSSP call (`MsCall.MsspCallSpec`, a
hypothesis), the FR image of the stage family written once by `frImg` at a staging base `A`,
copied into the resident image `[0, sb)`, `[Wf + 1, Wf + 1 + sb)` and its shadow at `SH`, the
sorted arc indices `SI` (`fiO ; fiS`), and the registers of the stage loop (`SLx.Regs`).

**The layout above the prologue's arrays** (`S1 = r9418 = Q + 15 k`, `b` corners, `k` darts):
`S1` (`fiO`/`fiS` scratch, `4k + 4b + 2` cells, the sorted indices at `lySI = S1 + 2k + 4b + 1`),
`lyOm = S1 + lyT` (the MSSP output, `b²` cells), `lyA = lyOm + b²` (the staging image, `2 sb`),
`lyS = lyA + 2 sb` (`frImg`'s scratch, `lyT` cells), `lyOb = lyS + lyT` (the FR answers of the
loop, `2b`), `lyP = lyOb + 2b` (the MSSP scratch, then the log of the loop), with
`lyT = 4k + 4b + 2`, `lySb = b² + 2b + 1 + 4k` (`sb` of the FR inputs with `2k` arcs).

Blocks (scratch registers `9460 … 9476`): `p7cA` (the layout), `p7cM` (the MSSP inputs
`8000 … 8009`), `p7cB` (the `frImg` inputs `8100 … 8111`), `p7cC` (`SH`, the copy bases),
`p7cK rs rd` (copy `sb` cells), `p7cD` (the `fiO`/`fiS` inputs), `p7cE` (the registers of
`SLx.Regs` not yet set).
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

/-! ### The layout numbers -/

/-- The size of the `fiO`/`fiS` scratch and of `frImg`'s scratch: `4k + 4b + 2`. -/
def lyT (b k : ℕ) : ℕ := 4 * k + 4 * b + 2
/-- `sb` of an FR input with `b` corners and `2k` arcs. -/
def lySb (b k : ℕ) : ℕ := b * b + b + b + 1 + 2 * k + 2 * k
/-- The MSSP output. -/
def lyOm (S1 b k : ℕ) : ℕ := S1 + lyT b k
/-- The staging image. -/
def lyA (S1 b k : ℕ) : ℕ := lyOm S1 b k + b * b
/-- `frImg`'s scratch. -/
def lyS (S1 b k : ℕ) : ℕ := lyA S1 b k + lySb b k + lySb b k
/-- The FR answers of the loop. -/
def lyOb (S1 b k : ℕ) : ℕ := lyS S1 b k + lyT b k
/-- The MSSP scratch, then the log of the loop. -/
def lyP (S1 b k : ℕ) : ℕ := lyOb S1 b k + b + b
/-- The sorted arc indices. -/
def lySI (S1 b k : ℕ) : ℕ := S1 + 2 * k + b + b + b + b + 1

/-! ### The blocks -/

/-- The layout. -/
def p7cA : Stmt := block [.copyN 9460 9418, .mulN 9461 9419 9419, .addN 9462 9401 9401,
  .addN 9463 9462 9462, .addN 9463 9463 9419, .addN 9463 9463 9419, .addN 9463 9463 9419,
  .addN 9463 9463 9419, .addN 9463 9463 9436, .addN 9463 9463 9436,
  .addN 9464 9460 9463,
  .addN 9465 9461 9419, .addN 9465 9465 9419, .addN 9465 9465 9436, .addN 9465 9465 9462,
  .addN 9465 9465 9462,
  .addN 9466 9464 9461, .addN 9467 9466 9465, .addN 9467 9467 9465, .addN 9468 9467 9463,
  .addN 9469 9468 9419, .addN 9469 9469 9419,
  .addN 9470 9460 9462, .addN 9470 9470 9419, .addN 9470 9470 9419, .addN 9470 9470 9419,
  .addN 9470 9470 9419,
  .addN 9470 9470 9436]

/-- The inputs of the MSSP call. -/
def p7cM : Stmt := block [.copyN 8000 9400, .copyN 8001 9430, .copyN 8002 9431,
  .copyN 8003 9401, .copyN 8004 9402, .copyN 8005 9409, .copyN 8006 9419, .copyN 8007 9410,
  .copyN 8008 9464, .copyN 8009 9469]

/-- The inputs of `frImg` (prices `PR`, lengths `EL`, root `0`). -/
def p7cB : Stmt := block [.copyN 8100 9419, .copyN 8101 9464, .copyN 8102 9417, .constN 8103 0,
  .copyN 8104 9462, .copyN 8105 9414, .copyN 8106 9415, .copyN 8107 9377, .copyN 8108 9310,
  .copyN 8109 9422, .copyN 8110 9466, .copyN 8111 9467]

/-- `SH = 2 (Wf + 1) + Mo² + Mo` (`= WN + 1`), the copy bases. -/
def p7cC : Stmt := block [.addN 9471 7612 7612, .mulN 9472 7610 7610, .addN 9471 9471 9472,
  .addN 9471 9471 7610, .addN 9473 9466 7607, .addN 9474 9471 7612, .constN 9475 0]

/-- Copy `sb = r7607` cells from `r[rs]` to `r[rd]`. -/
def p7cK (rs rd : ℕ) : Stmt := .seq (block [.copyN 4910 7607, .copyN 4911 rs, .copyN 4912 rd])
  cpArr

/-- The inputs of `fiO`/`fiS`. -/
def p7cD : Stmt := block [.copyN 8111 9460, .constN 8112 1]

/-- The registers of the stage loop. -/
def p7cE : Stmt := block [.copyN 9501 9416, .copyN 9502 9412, .copyN 9503 9413,
  .copyN 9504 9414, .copyN 9360 7612, .copyN 9361 9474, .copyN 8113 9461, .copyN 8124 7610,
  .modN 9476 9310 7610, .subN 8125 7610 9476, .constN 8112 1, .copyN 8115 7605,
  .copyN 9362 9470, .copyN 7614 9468, .copyN 7615 9469, .copyN 7616 9471]

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 2000000 in
theorem p7cA_exec (c : Config) (hc : WordsBounded W c) {S1 b k : ℕ}
    (r18 : c.nreg 9418 = S1) (r19 : c.nreg 9419 = b) (r01 : c.nreg 9401 = k)
    (r36 : c.nreg 9436 = 1) (hW : lyP S1 b k ≤ W) :
    ∃ c' t, Exec P W p7cA c c' t ∧ t = 28 ∧ c'.nreg 9460 = S1 ∧ c'.nreg 9461 = b * b ∧
      c'.nreg 9462 = 2 * k ∧ c'.nreg 9463 = lyT b k ∧ c'.nreg 9464 = lyOm S1 b k ∧
      c'.nreg 9465 = lySb b k ∧ c'.nreg 9466 = lyA S1 b k ∧ c'.nreg 9467 = lyS S1 b k ∧
      c'.nreg 9468 = lyOb S1 b k ∧ c'.nreg 9469 = lyP S1 b k ∧ c'.nreg 9470 = lySI S1 b k ∧
      (∀ r, (r < 9460 ∨ 9470 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lyP lyOb lyS lyA lyOm lyT lySb at hW
  unfold p7cA
  exec_block
  all_goals try ((try config_simp) <;> (try simp only [r18, r19, r01, r36]) <;> omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r18, r19, r01, r36, lyP, lyOb, lyS, lyA, lyOm, lyT, lySb, lySI])
  all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

theorem p7cM_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W p7cM c c' t ∧ t = 10 ∧ c'.nreg 8000 = c.nreg 9400 ∧
      c'.nreg 8001 = c.nreg 9430 ∧ c'.nreg 8002 = c.nreg 9431 ∧ c'.nreg 8003 = c.nreg 9401 ∧
      c'.nreg 8004 = c.nreg 9402 ∧ c'.nreg 8005 = c.nreg 9409 ∧ c'.nreg 8006 = c.nreg 9419 ∧
      c'.nreg 8007 = c.nreg 9410 ∧ c'.nreg 8008 = c.nreg 9464 ∧ c'.nreg 8009 = c.nreg 9469 ∧
      (∀ r, (r < 8000 ∨ 8009 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold p7cM
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

theorem p7cB_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W p7cB c c' t ∧ t = 12 ∧ c'.nreg 8100 = c.nreg 9419 ∧
      c'.nreg 8101 = c.nreg 9464 ∧ c'.nreg 8102 = c.nreg 9417 ∧ c'.nreg 8103 = 0 ∧
      c'.nreg 8104 = c.nreg 9462 ∧ c'.nreg 8105 = c.nreg 9414 ∧ c'.nreg 8106 = c.nreg 9415 ∧
      c'.nreg 8107 = c.nreg 9377 ∧ c'.nreg 8108 = c.nreg 9310 ∧ c'.nreg 8109 = c.nreg 9422 ∧
      c'.nreg 8110 = c.nreg 9466 ∧ c'.nreg 8111 = c.nreg 9467 ∧
      (∀ r, (r < 8100 ∨ 8111 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold p7cB
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl,
    rfl⟩
  all_goals config_simp
  all_goals first | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

theorem p7cC_exec (c : Config) (hc : WordsBounded W c) {w1 Mo sb Ab : ℕ}
    (r12 : c.nreg 7612 = w1) (r10 : c.nreg 7610 = Mo) (r07 : c.nreg 7607 = sb)
    (r66 : c.nreg 9466 = Ab) (hW : w1 + w1 + Mo * Mo + Mo + w1 ≤ W) (hA : Ab + sb ≤ W) :
    ∃ c' t, Exec P W p7cC c c' t ∧ t = 7 ∧ c'.nreg 9471 = w1 + w1 + Mo * Mo + Mo ∧
      c'.nreg 9473 = Ab + sb ∧ c'.nreg 9474 = w1 + w1 + Mo * Mo + Mo + w1 ∧
      c'.nreg 9475 = 0 ∧
      (∀ r, (r < 9471 ∨ 9475 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold p7cC
  exec_block
  all_goals try ((try config_simp) <;> (try simp only [r12, r10, r07, r66]) <;> omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r12, r10, r07, r66])
  all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

/-- **A copy of `sb` cells.** -/
theorem p7cK_exec (c : Config) (hc : WordsBounded W c) {rs rd sb Sb Db : ℕ}
    (hrs : rs < 4910 ∨ 4916 < rs) (hrd : rd < 4910 ∨ 4916 < rd)
    (r07 : c.nreg 7607 = sb) (rS : c.nreg rs = Sb) (rD : c.nreg rd = Db)
    (lay : (Sb + sb ≤ Db ∨ Db + sb ≤ Sb) ∧ Sb + sb ≤ W ∧ Db + sb ≤ W ∧ sb + 1 ≤ W) :
    ∃ c' t, Exec P W (p7cK rs rd) c c' t ∧ t ≤ 7 * sb + 7 ∧
      (∀ i < sb, c'.nmem (Db + i) = c.nmem (Sb + i)) ∧
      (∀ a, (a < Db ∨ Db + sb ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4910 ∨ 4916 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a0, a1, a2, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.copyN 4910 7607, .copyN 4911 rs, .copyN 4912 rd]) c c₁ t₁ ∧ t₁ = 3 ∧
        c₁.nreg 4910 = sb ∧ c₁.nreg 4911 = Sb ∧ c₁.nreg 4912 = Db ∧
        (∀ x, (x < 4910 ∨ 4912 < x) → c₁.nreg x = c.nreg x) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals (try simp only [upd_apply]); all_goals (try split_ifs); all_goals omega
  obtain ⟨c₂, t₂, e₂, ht₂, b1, bk, bn, br, brm, bo⟩ :=
    cpArr_exec (P := P) c₁ e₁.wb_right a0 a1 a2 lay
  refine ⟨c₂, _, e₁.seq e₂, by omega, fun i hi => by rw [b1 i hi, am], fun a ha => by
    rw [bk a ha, am], fun x hx => ?_, by rw [br, ar], by rw [brm, arm], by rw [bo, ao]⟩
  rw [bn x (by omega), ak x (by omega)]

theorem p7cD_exec (c : Config) (hc : WordsBounded W c) (hW1 : 1 ≤ W) :
    ∃ c' t, Exec P W p7cD c c' t ∧ t = 2 ∧ c'.nreg 8111 = c.nreg 9460 ∧ c'.nreg 8112 = 1 ∧
      (∀ r, r ≠ 8111 → r ≠ 8112 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold p7cD
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

set_option maxHeartbeats 1000000 in
theorem p7cE_exec (c : Config) (hc : WordsBounded W c) {K Mo : ℕ} (r10 : c.nreg 9310 = K)
    (r7610 : c.nreg 7610 = Mo) (hMo : 0 < Mo) (hW1 : 1 ≤ W) :
    ∃ c' t, Exec P W p7cE c c' t ∧ t = 16 ∧ c'.nreg 9501 = c.nreg 9416 ∧
      c'.nreg 9502 = c.nreg 9412 ∧ c'.nreg 9503 = c.nreg 9413 ∧ c'.nreg 9504 = c.nreg 9414 ∧
      c'.nreg 9360 = c.nreg 7612 ∧ c'.nreg 9361 = c.nreg 9474 ∧ c'.nreg 8113 = c.nreg 9461 ∧
      c'.nreg 8124 = Mo ∧ c'.nreg 8125 = Mo - K % Mo ∧ c'.nreg 8112 = 1 ∧
      c'.nreg 8115 = c.nreg 7605 ∧ c'.nreg 9362 = c.nreg 9470 ∧ c'.nreg 7614 = c.nreg 9468 ∧
      c'.nreg 7615 = c.nreg 9469 ∧ c'.nreg 7616 = c.nreg 9471 ∧
      (∀ r, (r < 9501 ∨ 9504 < r) → (r < 9360 ∨ 9362 < r) → r ≠ 8113 → r ≠ 8124 → r ≠ 8125 →
        r ≠ 8112 → r ≠ 8115 → r ≠ 9476 → (r < 7614 ∨ 7616 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hc' := hc
  unfold p7cE
  exec_block
  all_goals try ((try config_simp) <;> (try simp only [r10, r7610]) <;>
    (first | omega | exact Nat.le_trans (Nat.sub_le _ _) (by have := hc.1 7610; omega) |
      exact Nat.le_trans (Nat.mod_le _ _) (hc.1 9310)))
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r10, r7610])
  all_goals first | omega | (repeat rw [upd_other _ _ _ (by omega)]) | rfl

/-- Save the driver's registers `3000 … 3012`, `6800 … 6819` in `9600 … 9632` (the MSSP program may
change every register below `8300` except its inputs). -/
def p7cSv : Stmt := block [
  .copyN 9600 3000, .copyN 9601 3001, .copyN 9602 3002, .copyN 9603 3003, .copyN 9604 3004,
  .copyN 9605 3005, .copyN 9606 3006, .copyN 9607 3007, .copyN 9608 3008, .copyN 9609 3009,
  .copyN 9610 3010, .copyN 9611 3011, .copyN 9612 3012, .copyN 9613 6800, .copyN 9614 6801,
  .copyN 9615 6802, .copyN 9616 6803, .copyN 9617 6804, .copyN 9618 6805, .copyN 9619 6806,
  .copyN 9620 6807, .copyN 9621 6808, .copyN 9622 6809, .copyN 9623 6810, .copyN 9624 6811,
  .copyN 9625 6812, .copyN 9626 6813, .copyN 9627 6814, .copyN 9628 6815, .copyN 9629 6816,
  .copyN 9630 6817, .copyN 9631 6818, .copyN 9632 6819]

/-- Restore the driver's registers. -/
def p7cRs : Stmt := block [
  .copyN 3000 9600, .copyN 3001 9601, .copyN 3002 9602, .copyN 3003 9603, .copyN 3004 9604,
  .copyN 3005 9605, .copyN 3006 9606, .copyN 3007 9607, .copyN 3008 9608, .copyN 3009 9609,
  .copyN 3010 9610, .copyN 3011 9611, .copyN 3012 9612, .copyN 6800 9613, .copyN 6801 9614,
  .copyN 6802 9615, .copyN 6803 9616, .copyN 6804 9617, .copyN 6805 9618, .copyN 6806 9619,
  .copyN 6807 9620, .copyN 6808 9621, .copyN 6809 9622, .copyN 6810 9623, .copyN 6811 9624,
  .copyN 6812 9625, .copyN 6813 9626, .copyN 6814 9627, .copyN 6815 9628, .copyN 6816 9629,
  .copyN 6817 9630, .copyN 6818 9631, .copyN 6819 9632]

set_option maxHeartbeats 4000000 in
theorem p7cSv_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W p7cSv c c' t ∧ t = 33 ∧
      (∀ r, 3000 ≤ r → r ≤ 3012 → c'.nreg (r + 6600) = c.nreg r) ∧
      (∀ r, 6800 ≤ r → r ≤ 6819 → c'.nreg (r + 2813) = c.nreg r) ∧
      (∀ r, (r < 9600 ∨ 9632 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold p7cSv
  exec_block
  refine ⟨rfl, fun r h1 h2 => ?_, fun r h1 h2 => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · interval_cases r <;> (config_simp <;> rfl)
  · interval_cases r <;> (config_simp <;> rfl)
  · config_simp
    repeat rw [upd_other _ _ _ (by omega)]

set_option maxHeartbeats 4000000 in
theorem p7cRs_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W p7cRs c c' t ∧ t = 33 ∧
      (∀ r, 3000 ≤ r → r ≤ 3012 → c'.nreg r = c.nreg (r + 6600)) ∧
      (∀ r, 6800 ≤ r → r ≤ 6819 → c'.nreg r = c.nreg (r + 2813)) ∧
      (∀ r, (r < 3000 ∨ 3012 < r) → (r < 6800 ∨ 6819 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold p7cRs
  exec_block
  refine ⟨rfl, fun r h1 h2 => ?_, fun r h1 h2 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  · interval_cases r <;> (config_simp <;> rfl)
  · interval_cases r <;> (config_simp <;> rfl)
  · config_simp
    repeat rw [upd_other _ _ _ (by omega)]

end BKMNW

end PlanarFlow
