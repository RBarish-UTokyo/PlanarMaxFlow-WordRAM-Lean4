module

public import PlanarFlow.BKMNW.FrImg
public import PlanarFlow.BKMNW.NegCall

/-!
# One in-place call of the fixed natural FR-Dijkstra, from zero memory to zero memory

**`frCall`** `= fcPre ; lgS 7620 7621 frNF ; fcOut ; fcClr` runs the fixed natural-word
FR-Dijkstra `frNF` inside the memory of a larger computation whose memory up to `Wz ≥ frWN P L`
is zero (`MemZ`-style) and whose data lives above `Wz`:

* `fcPre`: copy the image of the input (`frNM` at `[A, A + sb)`, the residues `frRS` at
  `[A + sb, A + 2 sb)`, `A = r7613`) to `[0, sb)` and `[β, β + sb)` (`β = P.W + 1 = r7612`,
  `cpArr`); zero the registers `< 763`; set the input registers `r100 … r109` from
  `r7600 … r7609`, the constants `r760 … r762` from `r7610 … r7612`, the log pointer
  `r7620 = p = r7615` and `r7621 = 1`;
* the logged run `lgS 7620 7621 frNF` (`frNF_lgRun` against the reference run `frNF_ref` from the
  image `frCfgN P L`);
* `fcOut`: copy the settled flags `[sb, sb + N)` to `[Ob, Ob + N)` and the residues of the
  distances `[β + db, β + db + N)` to `[Ob + N, Ob + 2 N)` (`Ob = r7614`);
* `fcClr`: clear the logged cells (`lgClr`), zero `[0, sb)` and `[β, β + sb)` (`mzFill`).

**`frCall_exec`**: within **`36 · frCost P + 24 · sb + 14 · N + 1000`** steps the memory `≤ Wz` is
**zero again**, the copy at `Ob` holds the result **`FResN P L K v dd · Ob (Ob + N)`** (a run of
Dijkstra's algorithm with the prices, the flags and the decoded distances), the memory above `Wz`
outside `[Ob, Ob + 2 N)` and the log `[p, p + 4 frCost P + 3)` is kept, the registers outside the
scratch `fcScr` (`< 763`, `2923 … 2929`, `4910 … 4916`, `5030 … 5035`, `7620`, `7621`) are kept,
reals and output kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace FrFix

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Machine.ModNat WordRAM.Programs
  Monge Monge.FR Monge.CmpAbs NegSSSP MfDrv

/-! ### The programs -/

/-- The arguments of the copy of the natural part of the image: `4910 = sb`, `4911 = A`,
`4912 = 0`. -/
def fcCp1 : Stmt := block [.copyN 4910 7607, .copyN 4911 7613, .constN 4912 0]

/-- The arguments of the copy of the residues: `4910 = sb`, `4911 = A + sb`, `4912 = β`. -/
def fcCp2 : Stmt := block [.copyN 4910 7607, .addN 4911 7613 7607, .copyN 4912 7612]

/-- **Write the image** into the low memory. -/
def fcImg : Stmt := .seq (.seq fcCp1 cpArr) (.seq fcCp2 cpArr)

/-- The registers of the run. -/
def fcSet : Stmt :=
  block [.copyN 100 7600, .copyN 101 7601, .copyN 102 7602, .copyN 103 7603, .copyN 104 7604,
    .copyN 105 7605, .copyN 106 7606, .copyN 107 7607, .copyN 108 7608, .copyN 109 7609,
    .copyN 760 7610, .copyN 761 7611, .copyN 762 7612, .constN 7621 1, .copyN 7620 7615]

/-- **Before the run.** -/
def fcPre : Stmt := .seq fcImg (.seq (mbZeroRegs (List.range 763)) fcSet)

/-- The arguments of the copy of the flags: `4910 = N`, `4911 = sb`, `4912 = Ob`. -/
def fcO1 : Stmt := block [.copyN 4910 7600, .copyN 4911 7607, .copyN 4912 7614]

/-- The arguments of the copy of the distances: `4910 = N`, `4911 = β + db`, `4912 = Ob + N`. -/
def fcO2 : Stmt := block [.copyN 4910 7600, .addN 4911 7612 7608, .addN 4912 7614 7600]

/-- **Copy the result out.** -/
def fcOut : Stmt := .seq (.seq fcO1 cpArr) (.seq fcO2 cpArr)

/-- The arguments of the clearing of the log: `2924 = p`, `2925 = LP`, `2926 = 1`. -/
def fcCl : Stmt := block [.copyN 2924 7615, .copyN 2925 7620, .constN 2926 1]

/-- The arguments of the zeroing of the natural part: `5030 = sb`, `5031 = 0`. -/
def fcZ1 : Stmt := block [.copyN 5030 7607, .constN 5031 0]

/-- The arguments of the zeroing of the residues: `5030 = sb`, `5031 = β`. -/
def fcZ2 : Stmt := block [.copyN 5030 7607, .copyN 5031 7612]

/-- **Clear the log and the image.** -/
def fcClr : Stmt := .seq (.seq fcCl lgClr) (.seq (.seq fcZ1 mzFill) (.seq fcZ2 mzFill))

/-- **One in-place call of the fixed natural FR-Dijkstra.** -/
def frCall : Stmt := .seq fcPre (.seq (lgS 7620 7621 frNF) (.seq fcOut fcClr))

/-- The scratch registers of `frCall`. -/
def fcScr (r : ℕ) : Prop :=
  r < 763 ∨ (2923 ≤ r ∧ r ≤ 2929) ∨ (4910 ≤ r ∧ r ≤ 4916) ∨ (5030 ≤ r ∧ r ≤ 5035) ∨ r = 7620 ∨
    r = 7621

/-! ### The blocks -/

section Blocks

variable {P : Input} {W : ℕ}

theorem fcCp1_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W fcCp1 c c' t ∧ t = 3 ∧ c'.nreg 4910 = c.nreg 7607 ∧
      c'.nreg 4911 = c.nreg 7613 ∧ c'.nreg 4912 = 0 ∧
      (∀ r, (r < 4910 ∨ 4912 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fcCp1
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

theorem fcCp2_exec (c : Config) (hc : WordsBounded W c) {A sb : ℕ} (r13 : c.nreg 7613 = A)
    (r07 : c.nreg 7607 = sb) (hW : A + sb ≤ W) :
    ∃ c' t, Exec P W fcCp2 c c' t ∧ t = 3 ∧ c'.nreg 4910 = sb ∧
      c'.nreg 4911 = A + sb ∧ c'.nreg 4912 = c.nreg 7612 ∧
      (∀ r, (r < 4910 ∨ 4912 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fcCp2
  exec_block
  all_goals try ((try config_simp); (try simp only [r13, r07]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r13, r07])
  simp only [upd_apply]; split_ifs <;> omega

/-- **Writing the image**: `[0, sb)` from `[A, A + sb)`, `[β, β + sb)` from `[A + sb, A + 2 sb)`. -/
theorem fcImg_exec (c : Config) (hc : WordsBounded W c) {A sb β : ℕ} (r13 : c.nreg 7613 = A)
    (r07 : c.nreg 7607 = sb) (r12 : c.nreg 7612 = β) (h0 : 0 < β) (h1 : sb ≤ β) (h2 : β + sb ≤ A)
    (hW : A + sb + sb ≤ W) :
    ∃ c' t, Exec P W fcImg c c' t ∧ t ≤ 14 * sb + 14 ∧
      (∀ i < sb, c'.nmem i = c.nmem (A + i)) ∧ (∀ i < sb, c'.nmem (β + i) = c.nmem (A + sb + i)) ∧
      (∀ a, sb ≤ a → (a < β ∨ β + sb ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 4910 ∨ 4916 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a10, a11, a12, ak, am, ar, arm, ao⟩ := fcCp1_exec (P := P) c hc
  obtain ⟨c₂, t₂, e₂, ht₂, bcp, bkeep, bregs, br, brm, bo⟩ :=
    cpArr_exec (P := P) (n := sb) (Sb := A) (Db := 0) c₁ e₁.wb_right (a10.trans r07)
      (a11.trans r13) a12 ⟨Or.inr (by omega), by omega, by omega, by omega⟩
  have k2 : ∀ r, (r < 4910 ∨ 4916 < r) → c₂.nreg r = c.nreg r := fun r hr => by
    rw [bregs r (by omega), ak r (by omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, c10, c11, c12, ck, cm, cr, crm, co⟩ :=
    fcCp2_exec (P := P) c₂ e₂.wb_right (by rw [k2 _ (by omega), r13]) (by rw [k2 _ (by omega), r07])
      (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, dcp, dkeep, dregs, dr, drm, do'⟩ :=
    cpArr_exec (P := P) (n := sb) (Sb := A + sb) (Db := β) c₃ e₃.wb_right c10 c11
      (by rw [c12, k2 _ (by omega), r12]) ⟨Or.inr (by omega), by omega, by omega, by omega⟩
  refine ⟨c₄, _, (e₁.seq e₂).seq (e₃.seq e₄), by omega, fun i hi => ?_, fun i hi => ?_,
    fun a ha hb => ?_, fun r hr => ?_, by rw [dr, cr, br, ar], by rw [drm, crm, brm, arm],
    by rw [do', co, bo, ao]⟩
  · have := bcp i hi
    rw [Nat.zero_add] at this
    rw [dkeep _ (Or.inl (by omega)), cm, this, am]
  · rw [dcp i hi, cm, bkeep _ (Or.inr (by omega)), am]
  · rw [dkeep a hb, cm, bkeep a (Or.inr (by omega)), am]
  · rw [dregs r (by omega), ck r (by omega), k2 r hr]

theorem fcSet_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' t, Exec P W fcSet c c' t ∧ t = 15 ∧
      c'.nreg = upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd c.nreg
        100 (c.nreg 7600)) 101 (c.nreg 7601)) 102 (c.nreg 7602)) 103 (c.nreg 7603))
        104 (c.nreg 7604)) 105 (c.nreg 7605)) 106 (c.nreg 7606)) 107 (c.nreg 7607))
        108 (c.nreg 7608)) 109 (c.nreg 7609)) 760 (c.nreg 7610)) 761 (c.nreg 7611))
        762 (c.nreg 7612)) 7621 1) 7620 (c.nreg 7615) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fcSet
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  config_simp

theorem fcO1_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W fcO1 c c' t ∧ t = 3 ∧ c'.nreg 4910 = c.nreg 7600 ∧
      c'.nreg 4911 = c.nreg 7607 ∧ c'.nreg 4912 = c.nreg 7614 ∧
      (∀ r, (r < 4910 ∨ 4912 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fcO1
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

theorem fcO2_exec (c : Config) (hc : WordsBounded W c) {N β db Ob : ℕ} (r00 : c.nreg 7600 = N)
    (r12 : c.nreg 7612 = β) (r08 : c.nreg 7608 = db) (r14 : c.nreg 7614 = Ob)
    (hW : β + db ≤ W) (hW' : Ob + N ≤ W) :
    ∃ c' t, Exec P W fcO2 c c' t ∧ t = 3 ∧ c'.nreg 4910 = N ∧
      c'.nreg 4911 = β + db ∧ c'.nreg 4912 = Ob + N ∧
      (∀ r, (r < 4910 ∨ 4912 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fcO2
  exec_block
  all_goals try ((try config_simp); (try simp only [r00, r12, r08, r14]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r00, r12, r08, r14])
  simp only [upd_apply]; split_ifs <;> omega

/-- **Copying the result out**: the flags `[sb, sb + N)` to `Ob`, the residues
`[β + db, β + db + N)` to `Ob + N`. -/
theorem fcOut_exec (c : Config) (hc : WordsBounded W c) {N sb β db Ob : ℕ}
    (r00 : c.nreg 7600 = N) (r07 : c.nreg 7607 = sb) (r12 : c.nreg 7612 = β)
    (r08 : c.nreg 7608 = db) (r14 : c.nreg 7614 = Ob) (h0 : 0 < Ob) (h1 : sb + N ≤ Ob)
    (h2 : β + db + N ≤ Ob)
    (hW : Ob + N + N ≤ W) :
    ∃ c' t, Exec P W fcOut c c' t ∧ t ≤ 14 * N + 14 ∧
      (∀ i < N, c'.nmem (Ob + i) = c.nmem (sb + i)) ∧
      (∀ i < N, c'.nmem (Ob + N + i) = c.nmem (β + db + i)) ∧
      (∀ a, (a < Ob ∨ Ob + N + N ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 4910 ∨ 4916 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a10, a11, a12, ak, am, ar, arm, ao⟩ := fcO1_exec (P := P) c hc
  obtain ⟨c₂, t₂, e₂, ht₂, bcp, bkeep, bregs, br, brm, bo⟩ :=
    cpArr_exec (P := P) (n := N) (Sb := sb) (Db := Ob) c₁ e₁.wb_right (a10.trans r00)
      (a11.trans r07) (a12.trans r14) ⟨Or.inl h1, by omega, by omega, by omega⟩
  have k2 : ∀ r, (r < 4910 ∨ 4916 < r) → c₂.nreg r = c.nreg r := fun r hr => by
    rw [bregs r (by omega), ak r (by omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, c10, c11, c12, ck, cm, cr, crm, co⟩ :=
    fcO2_exec (P := P) c₂ e₂.wb_right (by rw [k2 _ (by omega), r00]) (by rw [k2 _ (by omega), r12])
      (by rw [k2 _ (by omega), r08]) (by rw [k2 _ (by omega), r14]) (by omega) (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, dcp, dkeep, dregs, dr, drm, do'⟩ :=
    cpArr_exec (P := P) (n := N) (Sb := β + db) (Db := Ob + N) c₃ e₃.wb_right c10 c11 c12
      ⟨Or.inl (by omega), by omega, by omega, by omega⟩
  refine ⟨c₄, _, (e₁.seq e₂).seq (e₃.seq e₄), by omega, fun i hi => ?_, fun i hi => ?_,
    fun a ha => ?_, fun r hr => ?_, by rw [dr, cr, br, ar], by rw [drm, crm, brm, arm],
    by rw [do', co, bo, ao]⟩
  · rw [dkeep _ (Or.inl (by omega)), cm, bcp i hi, am]
  · rw [dcp i hi, cm, bkeep _ (Or.inl (by omega)), am]
  · rw [dkeep a (by omega), cm, bkeep a (by omega), am]
  · rw [dregs r (by omega), ck r (by omega), k2 r hr]

theorem fcCl_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' t, Exec P W fcCl c c' t ∧ t = 3 ∧ c'.nreg 2924 = c.nreg 7615 ∧
      c'.nreg 2925 = c.nreg 7620 ∧ c'.nreg 2926 = 1 ∧
      (∀ r, (r < 2924 ∨ 2926 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fcCl
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

theorem fcZ1_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W fcZ1 c c' t ∧ t = 2 ∧ c'.nreg 5030 = c.nreg 7607 ∧ c'.nreg 5031 = 0 ∧
      (∀ r, (r < 5030 ∨ 5031 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fcZ1
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

theorem fcZ2_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W fcZ2 c c' t ∧ t = 2 ∧ c'.nreg 5030 = c.nreg 7607 ∧
      c'.nreg 5031 = c.nreg 7612 ∧
      (∀ r, (r < 5030 ∨ 5031 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fcZ2
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

/-- **Clearing the log and the image**: every logged cell and `[0, sb)`, `[β, β + sb)` zero,
every other cell kept. -/
theorem fcClr_exec (c : Config) (hc : WordsBounded W c) {p j Ws sb β : ℕ}
    (r15 : c.nreg 7615 = p) (r20 : c.nreg 7620 = p + j) (r07 : c.nreg 7607 = sb)
    (r12 : c.nreg 7612 = β) (hlog : ∀ i < j, c.nmem (p + i) ≤ Ws) (hp : Ws < p)
    (h0 : 0 < β) (h1 : sb ≤ β) (hW : β + sb ≤ W) :
    ∃ c' t, Exec P W fcClr c c' t ∧ t ≤ 6 * j + 10 * sb + 22 ∧
      (∀ a, (∃ i < j, c.nmem (p + i) = a) ∨ a < sb ∨ (β ≤ a ∧ a < β + sb) → c'.nmem a = 0) ∧
      (∀ a, (∀ i < j, c.nmem (p + i) ≠ a) → sb ≤ a → (a < β ∨ β + sb ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2923 ∨ (2929 < r ∧ r < 5030) ∨ 5035 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a24, a25, a26, ak, am, ar, arm, ao⟩ :=
    fcCl_exec (P := P) c hc (by have := hc.1 7615; omega)
  obtain ⟨c₂, t₂, e₂, ht₂, bzero, bkeep, bregs, br, brm, bo⟩ :=
    lgClr_exec (P := P) c₁ e₁.wb_right (p := p) (j := j) (Ws := Ws) (by rw [a24, r15])
      (by rw [a25, r20]) a26 (fun i hi => by rw [am]; exact hlog i hi) hp
  have k2 : ∀ r, r < 2923 ∨ 2929 < r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [bregs r (by omega) (by omega), ak r (by omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, c30, c31, ck, cm, cr, crm, co⟩ := fcZ1_exec (P := P) c₂ e₂.wb_right
  obtain ⟨c₄, t₄, e₄, ht₄, dzero, dkeep, dregs, dr, drm, do'⟩ :=
    mzFill_exec (P := P) c₃ e₃.wb_right (len := sb) (Zb := 0) (by rw [c30, k2 _ (by omega), r07])
      c31 (by omega) (by omega)
  have k4 : ∀ r, r < 2923 ∨ (2929 < r ∧ r < 5030) ∨ 5035 < r → c₄.nreg r = c.nreg r :=
    fun r hr => by rw [dregs r (by omega), ck r (by omega), k2 r (by omega)]
  obtain ⟨c₅, t₅, e₅, ht₅, f30, f31, fk, fm, fr, frm, fo⟩ := fcZ2_exec (P := P) c₄ e₄.wb_right
  obtain ⟨c₆, t₆, e₆, ht₆, gzero, gkeep, gregs, gr, grm, go⟩ :=
    mzFill_exec (P := P) c₅ e₅.wb_right (len := sb) (Zb := β)
      (by rw [f30, k4 _ (by omega), r07]) (by rw [f31, k4 _ (by omega), r12]) hW (by omega)
  have m62 : ∀ a, sb ≤ a → (a < β ∨ β + sb ≤ a) → c₆.nmem a = c₂.nmem a := fun a h1 h2 => by
    rw [gkeep a h2, fm, dkeep a (by omega), cm]
  refine ⟨c₆, _, (e₁.seq e₂).seq ((e₃.seq e₄).seq (e₅.seq e₆)), by omega, fun a ha => ?_,
    fun a hl h1 h2 => ?_, fun r hr => ?_, by rw [gr, fr, dr, cr, br, ar],
    by rw [grm, frm, drm, crm, brm, arm], by rw [go, fo, do', co, bo, ao]⟩
  · rcases ha with ⟨i, hi, hia⟩ | ha | ⟨h1, h2⟩
    · by_cases hs : a < sb
      · rw [gkeep a (Or.inl (by omega)), fm]
        have := dzero a hs; rwa [Nat.zero_add] at this
      by_cases hb : β ≤ a ∧ a < β + sb
      · have := gzero (a - β) (by omega); rwa [show β + (a - β) = a by omega] at this
      rw [m62 a (by omega) (by omega)]
      exact bzero a ⟨i, hi, by rw [am]; exact hia⟩
    · by_cases hb : β ≤ a ∧ a < β + sb
      · have := gzero (a - β) (by omega); rwa [show β + (a - β) = a by omega] at this
      rw [gkeep a (by omega), fm]
      have := dzero a ha; rwa [Nat.zero_add] at this
    · have := gzero (a - β) (by omega); rwa [show β + (a - β) = a by omega] at this
  · rw [m62 a h1 h2, bkeep a (fun i hi => by rw [am]; exact hl i hi), am]
  · rw [gregs r (by omega), fk r (by omega), k4 r hr]

end Blocks

/-! ### The call -/

section Call

/-- The registers `< 763` after `fcSet` from zeroed registers are those of the image. -/
lemma fcRegs_eq {P : Prm} {L : ℕ} (f : ℕ → ℕ) (hz : ∀ r < 763, f r = 0)
    (v00 : f 7600 = P.N) (v01 : f 7601 = P.b) (v02 : f 7602 = P.Db) (v03 : f 7603 = P.pb)
    (v04 : f 7604 = P.ob) (v05 : f 7605 = P.lb) (v06 : f 7606 = P.r) (v07 : f 7607 = P.sb)
    (v08 : f 7608 = P.db) (v09 : f 7609 = P.wb) (v10 : f 7610 = frM P L)
    (v11 : f 7611 = frH P L) (v12 : f 7612 = P.W + 1) (r : ℕ) (hr : r < 763) :
    upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd f
        100 (f 7600)) 101 (f 7601)) 102 (f 7602)) 103 (f 7603))
        104 (f 7604)) 105 (f 7605)) 106 (f 7606)) 107 (f 7607))
        108 (f 7608)) 109 (f 7609)) 760 (f 7610)) 761 (f 7611))
        762 (f 7612)) 7621 1) 7620 (f 7615) r = (frCfgN P L).nreg r := by
  rw [frCfgN_nreg r hr]
  rcases (show (r ≠ 100 ∧ r ≠ 101 ∧ r ≠ 102 ∧ r ≠ 103 ∧ r ≠ 104 ∧ r ≠ 105 ∧ r ≠ 106 ∧ r ≠ 107 ∧
        r ≠ 108 ∧ r ≠ 109 ∧ r ≠ 760 ∧ r ≠ 761 ∧ r ≠ 762) ∨ r = 100 ∨ r = 101 ∨ r = 102 ∨
      r = 103 ∨ r = 104 ∨ r = 105 ∨ r = 106 ∨ r = 107 ∨ r = 108 ∨ r = 109 ∨ r = 760 ∨ r = 761 ∨
      r = 762 by omega) with
      h | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h60, h61, h62⟩ := h
    simp only [upd_apply, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h60, h61, h62,
      show r ≠ 7620 by omega, show r ≠ 7621 by omega, ↓reduceIte, hz r hr, frRegs]
    split_ifs <;> rfl
  all_goals simp [upd_apply, frRegs, v00, v01, v02, v03, v04, v05, v06, v07, v08, v09, v10, v11,
    v12]

theorem frCall_exec {P : Prm} {L : ℕ} (hL : Lay P) (hXB : XB P L) (hDc : Crossing P.b P.D)
    (hF : Feas P) (P' : Input) {W Wz A Ob p : ℕ} (c : Config) (hc : WordsBounded W c)
    (r00 : c.nreg 7600 = P.N) (r01 : c.nreg 7601 = P.b) (r02 : c.nreg 7602 = P.Db)
    (r03 : c.nreg 7603 = P.pb) (r04 : c.nreg 7604 = P.ob) (r05 : c.nreg 7605 = P.lb)
    (r06 : c.nreg 7606 = P.r) (r07 : c.nreg 7607 = P.sb) (r08 : c.nreg 7608 = P.db)
    (r09 : c.nreg 7609 = P.wb) (r10 : c.nreg 7610 = frM P L) (r11 : c.nreg 7611 = frH P L)
    (r12 : c.nreg 7612 = P.W + 1) (r13 : c.nreg 7613 = A) (r14 : c.nreg 7614 = Ob)
    (r15 : c.nreg 7615 = p)
    (hz : ∀ a ≤ Wz, c.nmem a = 0) (hWz : frWN P L ≤ Wz)
    (himg : ∀ a < P.sb, c.nmem (A + a) = frNM P a)
    (hres : ∀ a < P.sb, c.nmem (A + P.sb + a) = frRS P L a)
    (hA : Wz < A) (hAW : A + P.sb + P.sb ≤ W) (hO : Wz < Ob) (hOp : Ob + P.N + P.N ≤ p)
    (hpW : p + (4 * frCost P + 3) ≤ W) :
    ∃ c' t, Exec P' W frCall c c' t ∧ t ≤ 36 * frCost P + 24 * P.sb + 14 * P.N + 1000 ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      (∃ K v dd, FResN P L K v dd c'.nmem Ob (Ob + P.N)) ∧
      (∀ a, Wz < a → (a < Ob ∨ Ob + P.N + P.N ≤ a) → (a < p ∨ p + (4 * frCost P + 3) ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ fcScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hw := lay_w hL
  have hm5 := hL.m5
  have hm6 := hL.m6
  have hWN : 2 * P.W + 1 ≤ frWN P L := by unfold frWN; omega
  -- the reference run
  obtain ⟨dN', k', ex, hk', ho', K, v, dd, hR⟩ := frNF_ref hL hXB hDc hF P'
  -- before the run
  obtain ⟨c₁, t₁, e₁, ht₁, M1, M2, M3, R1, rr₁, rm₁, o₁⟩ :=
    fcImg_exec (P := P') c hc r13 r07 r12 (by omega) (by omega) (by omega) hAW
  obtain ⟨c₂, e₂, Z2, K2, nm₂, rr₂, rm₂, o₂⟩ := mbZeroRegs_exec' (P := P') (List.range 763) c₁
    e₁.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, N3, nm₃, rr₃, rm₃, o₃⟩ := fcSet_exec (P := P') c₂ e₂.wb_right
    (by omega)
  have q2 : ∀ r, 763 ≤ r → (r < 4910 ∨ 4916 < r) → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [K2 r (by simp; omega), R1 r h2]
  have key : ∀ r < 763, c₃.nreg r = (frCfgN P L).nreg r := fun r hr => by
    rw [N3]
    exact fcRegs_eq c₂.nreg (fun r hr => Z2 r (by simp; omega))
      (by rw [q2 _ (by omega) (by omega), r00]) (by rw [q2 _ (by omega) (by omega), r01])
      (by rw [q2 _ (by omega) (by omega), r02]) (by rw [q2 _ (by omega) (by omega), r03])
      (by rw [q2 _ (by omega) (by omega), r04]) (by rw [q2 _ (by omega) (by omega), r05])
      (by rw [q2 _ (by omega) (by omega), r06]) (by rw [q2 _ (by omega) (by omega), r07])
      (by rw [q2 _ (by omega) (by omega), r08]) (by rw [q2 _ (by omega) (by omega), r09])
      (by rw [q2 _ (by omega) (by omega), r10]) (by rw [q2 _ (by omega) (by omega), r11])
      (by rw [q2 _ (by omega) (by omega), r12]) r hr
  have q3 : ∀ r, 763 ≤ r → r ≠ 7620 → r ≠ 7621 → (r < 4910 ∨ 4916 < r) →
      c₃.nreg r = c.nreg r := fun r h1 h2 h3 h4 => by
    rw [N3]
    simp only [upd_apply, h2, h3, show r ≠ 762 by omega, show r ≠ 761 by omega,
      show r ≠ 760 by omega, show r ≠ 109 by omega, show r ≠ 108 by omega, show r ≠ 107 by omega,
      show r ≠ 106 by omega, show r ≠ 105 by omega, show r ≠ 104 by omega, show r ≠ 103 by omega,
      show r ≠ 102 by omega, show r ≠ 101 by omega, show r ≠ 100 by omega, ↓reduceIte]
    exact q2 r h1 h4
  have s20 : c₃.nreg 7620 = p := by
    rw [N3]; simp only [upd_apply, ↓reduceIte]; rw [q2 _ (by omega) (by omega), r15]
  have s21 : c₃.nreg 7621 = 1 := by
    rw [N3]; simp only [upd_apply, show (7621 : ℕ) ≠ 7620 by omega, ↓reduceIte]
  have hm3 : ∀ a ≤ frWN P L, c₃.nmem a = (frCfgN P L).nmem a := by
    intro a ha
    rw [nm₃, nm₂, frCfgN_nmem hL a]
    by_cases h1 : a < P.sb
    · simp only [h1, ↓reduceIte]; rw [M1 a h1, himg a h1]
    · by_cases h2 : P.W + 1 ≤ a ∧ a < P.W + 1 + P.sb
      · simp only [h1, h2, and_self, ↓reduceIte]
        have := M2 (a - (P.W + 1)) (by omega)
        rw [show P.W + 1 + (a - (P.W + 1)) = a by omega] at this
        rw [this, hres _ (by omega)]
      · simp only [h1, h2, ↓reduceIte]
        rw [M3 a (by omega) (by omega), hz a (by omega)]
  -- the run
  obtain ⟨c₄, k₄, j, ex₄, hk₄, hj, A4, Mm4, K4, rr₄, rm₄, L4, o41, o42⟩ :=
    frNF_lgRun (P' := P') ex (LP := 7620) (ONE := 7621) (by omega) (by omega) (by omega)
      (by omega) c₃ key hm3 e₃.wb_right s21 (by rw [s20]; omega) (by rw [s20]; omega)
  rw [s20] at K4
  have q4 : ∀ r, 763 ≤ r → r ≠ 7620 → r ≠ 7621 → (r < 4910 ∨ 4916 < r) →
      c₄.nreg r = c.nreg r := fun r h1 h2 h3 h4 => by
    rw [K4.nreg r (by simp; omega) h2, q3 r h1 h2 h3 h4]
  -- after the run
  obtain ⟨c₅, t₅, e₅, ht₅, O1, O2, O3, R5, rr₅, rm₅, o₅⟩ :=
    fcOut_exec (P := P') c₄ ex₄.wb_right (N := P.N) (sb := P.sb) (β := P.W + 1) (db := P.db)
      (Ob := Ob) (by rw [q4 _ (by omega) (by omega) (by omega) (by omega), r00])
      (by rw [q4 _ (by omega) (by omega) (by omega) (by omega), r07])
      (by rw [q4 _ (by omega) (by omega) (by omega) (by omega), r12])
      (by rw [q4 _ (by omega) (by omega) (by omega) (by omega), r08])
      (by rw [q4 _ (by omega) (by omega) (by omega) (by omega), r14]) (by omega) (by omega)
      (by omega) (by omega)
  have hlog5 : ∀ i < j, c₅.nmem (p + i) = c₄.nmem (p + i) := fun i hi =>
    O3 _ (Or.inr (by omega))
  obtain ⟨c₆, t₆, e₆, ht₆, Z6, F6, R6, rr₆, rm₆, o₆⟩ :=
    fcClr_exec (P := P') c₅ e₅.wb_right (p := p) (j := j) (Ws := frWN P L) (sb := P.sb)
      (β := P.W + 1) (by rw [R5 _ (by omega), q4 _ (by omega) (by omega) (by omega) (by omega), r15])
      (by rw [R5 _ (by omega), K4.lp])
      (by rw [R5 _ (by omega), q4 _ (by omega) (by omega) (by omega) (by omega), r07])
      (by rw [R5 _ (by omega), q4 _ (by omega) (by omega) (by omega) (by omega), r12])
      (fun i hi => by rw [hlog5 i hi]; exact K4.logle i hi) (by omega) (by omega) (by omega)
      (by omega)
  have notlog : ∀ a, frWN P L < a → ∀ i < j, c₅.nmem (p + i) ≠ a := fun a ha i hi e => by
    have := K4.logle i hi; rw [hlog5 i hi] at e; omega
  -- the memory above `Wz`
  have up : ∀ a, Wz < a → (a < Ob ∨ Ob + P.N + P.N ≤ a) →
      (a < p ∨ p + (4 * frCost P + 3) ≤ a) → c₆.nmem a = c.nmem a := by
    intro a h1 h2 h3
    rw [F6 a (notlog a (by omega)) (by omega) (by omega), O3 a h2,
      K4.nmem a (by omega) (by omega), nm₃, nm₂, M3 a (by omega) (by omega)]
  refine ⟨c₆, _, (e₁.seq (e₂.seq e₃)).seq (ex₄.seq (e₅.seq e₆)), ?_, fun a ha => ?_, ⟨K, v, dd,
    hR.congr (fun y hy => ?_) (fun y hy => ?_)⟩, up, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [List.length_range]
    omega
  · by_cases hl : (∃ i < j, c₅.nmem (p + i) = a) ∨ a < P.sb ∨ (P.W + 1 ≤ a ∧ a < P.W + 1 + P.sb)
    · exact Z6 a hl
    · simp only [not_or, not_exists, not_and, not_lt] at hl
      obtain ⟨hl1, hl2, hl3⟩ := hl
      rw [F6 a (fun i hi => hl1 i hi) hl2 (by omega), O3 a (Or.inl (by omega))]
      by_cases hW : a ≤ frWN P L
      · rw [K4.dirty a hW (fun i hi e => hl1 i hi (by rw [hlog5 i hi]; exact e)), nm₃, nm₂,
          M3 a hl2 (by omega), hz a ha]
      · rw [K4.nmem a (by omega) (Or.inl (by omega)), nm₃, nm₂, M3 a hl2 (by omega), hz a ha]
  · rw [F6 _ (notlog _ (by omega)) (by omega) (by omega), O1 y hy, Mm4 _ (by omega)]
  · rw [F6 _ (notlog _ (by omega)) (by omega) (by omega), O2 y hy, Mm4 _ (by omega)]
  · unfold fcScr at hr
    rw [R6 r (by omega), R5 r (by omega), q4 r (by omega) (by omega) (by omega) (by omega)]
  · rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁]
  · rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁]
  · have h0 : (frCfgN P L).output = [] := rfl
    rw [h0, ho'] at o41
    simp only [List.nil_append] at o41
    rw [o₆, o₅, o42, ← o41, List.append_nil, o₃, o₂, o₁]

end Call

end FrFix

end BKMNW

end PlanarFlow
