module

public import PlanarFlow.DynTree.RunE

/-!
# Dynamic trees with evert: operations with their operands in registers

The blocks of `PlanarFlow/DynTree/RunE.lean` (`EOp.stmt`) load their operands as compiled-in
constants. The blocks here read them from registers chosen by the caller, so that a program can
compute the operands and branch on the results:

* the node operands `v` (and `w`) are read from the natural registers `ra` (and `rb`);
* the numeric operand (the amount of an addition, the threshold of a comparison) is read from
  the real register `rz`.

The operands are first copied to the operand registers of `PlanarFlow/DynTree/OpsCode.lean`
(`r193`, `r194` and the real `r200`), then the block of the operation runs.

**Register interface** (`RegFr c c'`). Every block keeps the natural registers outside
`r160 … r199`, the real registers outside `r160 … r200`, and the output (nothing is printed);
it keeps `r151 = n` and the memory outside the structure (`MemFrame`). The natural registers
`r160 … r199` and the real registers `r160 … r200` are scratch: a caller keeps its state
elsewhere. The source registers `ra`, `rz` are arbitrary (they are read first); for `link`,
`rb ≠ 193`.

**Results.**

* `regQueryS`: `r195 := findRoot v`, `r196 := ` the argmin and real `r195 := ` the minimum on
  the root path of `v` (the node closest to the root among the minima), real
  `r196 := pathSum v`;
* `regQuery2S`: the same on the second values (no root);
* `regMinS` / `regMin2S`: the queries, and the comparison bit `r198 := 1` if the minimum is below
  the real register `rz`, `0` otherwise (compared on the machine, `ifLtR`);
* `regParentS`: `r195 := F.par v`.

Nothing is printed (the printing blocks of fixed operations remain `EOp.stmt`).

Each `…_exec` theorem has the amortised bound of the block it calls plus the steps of the
copies: `k + 16400 Φ' ≤ 16400 Φ + 147600 ⌊log₂ n⌋ + 21500 + …` (`311600 ⌊log₂ n⌋ + 42100 + 2`
for `link`), `Φ = potL G` the rank potential.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs VT

/-! ### The register frame -/

/-- The register frame of the register-operand blocks: the natural registers outside
`r160 … r199`, the real registers outside `r160 … r200` and the output are kept. -/
def RegFr (c c' : Config) : Prop :=
  (∀ r, (r < 160 ∨ 200 ≤ r) → c'.nreg r = c.nreg r) ∧
    (∀ r, (r < 160 ∨ 200 < r) → c'.rreg r = c.rreg r) ∧ c'.output = c.output

lemma RegFr.refl (c : Config) : RegFr c c := ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩

lemma RegFr.trans {c c' c'' : Config} (h : RegFr c c') (h' : RegFr c' c'') : RegFr c c'' :=
  ⟨fun r hr => (h'.1 r hr).trans (h.1 r hr), fun r hr => (h'.2.1 r hr).trans (h.2.1 r hr),
    h'.2.2.trans h.2.2⟩

lemma FrK.regFr {lo : ℕ} {c c' : Config} (h : FrK lo c c') : RegFr c c' :=
  ⟨fun r hr => (h.1 r hr).1, fun r hr => (h.1 r (by omega)).2, h.2.2⟩

lemma regFr_updN {r : ℕ} (hr : 160 ≤ r ∧ r < 200) (c : Config) (x : ℕ) :
    RegFr c { c with nreg := upd c.nreg r x } :=
  ⟨fun s hs => upd_ne_of _ _ _ (by omega), fun _ _ => rfl, rfl⟩

lemma regFr_updR {r : ℕ} (hr : 160 ≤ r ∧ r ≤ 200) (c : Config) (x : ℝ) :
    RegFr c { c with rreg := upd c.rreg r x } :=
  ⟨fun _ _ => rfl, fun s hs => upd_ne_of _ _ _ (by omega), rfl⟩

/-! ### The blocks -/

/-- `link`: `v = r ra` (a root), `w = r rb`. -/
def regLinkS (B ra rb : ℕ) : Stmt :=
  .seq (.instr (.copyN 193 ra)) <| .seq (.instr (.copyN 194 rb)) (opLinkS B)

/-- `cut`: `v = r ra` (not a root). -/
def regCutS (B ra : ℕ) : Stmt := .seq (.instr (.copyN 193 ra)) (opCutS B)

/-- `add`: add the real `r rz` to the values on the root path of `v = r ra`. -/
def regAddS (B ra rz : ℕ) : Stmt :=
  .seq (.instr (.copyN 193 ra)) <| .seq (.instr (.copyR 200 rz)) (opAddS B)

/-- `add2`: add the real `r rz` to the second values on the root path of `v = r ra`. -/
def regAdd2S (B ra rz : ℕ) : Stmt :=
  .seq (.instr (.copyN 193 ra)) <| .seq (.instr (.copyR 200 rz)) (opAdd2S B)

/-- `evert`: make `v = r ra` the root of its tree. -/
def regEvertS (B ra : ℕ) : Stmt := .seq (.instr (.copyN 193 ra)) (opEvertS B)

/-- The queries at `v = r ra`. -/
def regQueryS (B ra : ℕ) : Stmt := .seq (.instr (.copyN 193 ra)) (opQueryS B)

/-- The queries on the second values at `v = r ra`. -/
def regQuery2S (B ra : ℕ) : Stmt := .seq (.instr (.copyN 193 ra)) (opQuery2S B)

/-- The parent of `v = r ra`, read from the access. -/
def regParentS (B ra : ℕ) : Stmt := .seq (.instr (.copyN 193 ra)) (opParentAccS B)

section
variable {P : Input} {W : ℕ}

/-- The state after copying into a scratch natural register other than `r151`. -/
lemma LCTE.updN {B n : ℕ} {F : Forest} {G : List VT} {c : Config} (hS : LCTE B n F G c)
    (r x : ℕ) (hr : r ≠ 151) : LCTE B n F G { c with nreg := upd c.nreg r x } :=
  hS.lift rfl (upd_ne_of _ _ _ (by omega))

/-- The state after writing a real register. -/
lemma LCTE.updR {B n : ℕ} {F : Forest} {G : List VT} {c : Config} (hS : LCTE B n F G c)
    (r : ℕ) (x : ℝ) : LCTE B n F G { c with rreg := upd c.rreg r x } :=
  hS.lift rfl rfl

/-- **`link` with register operands.** -/
theorem regLink_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra rb v w : ℕ} (hrb : rb ≠ 193)
    (hv : c.nreg ra = v) (hw : c.nreg rb = w) (hvn : v < n) (hwn : w < n) (hp : F.par v = n)
    (hroot : findRoot F n w ≠ v) :
    ∃ c' k, Exec P W (regLinkS B ra rb) c c' k ∧ ∃ G', LCTE B n (link F v w) G' c' ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 311600 * Nat.log 2 n + 42102 := by
  have e1 := Exec.copyN (P := P) hc 193 ra
  have e2 := Exec.copyN (P := P) e1.wb_right 194 rb
  obtain ⟨c', k, G', e, hS', hmf, hfr, -, -, hk, -⟩ := opLink_execE (P := P) B n e2.wb_right hW
    ((hS.updN 193 _ (by omega)).updN 194 _ (by omega)) (by simp [hv])
    (by simp [upd_ne_of _ _ _ hrb, hw]) hvn hwn hp hroot
  exact ⟨c', 1 + (1 + k), .seq e1 (.seq e2 e), G', hS', hmf,
    ((regFr_updN (by omega) c _).trans (regFr_updN (by omega) _ _)).trans hfr.regFr, by omega⟩

/-- **`cut` with a register operand.** -/
theorem regCut_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra v : ℕ} (hv : c.nreg ra = v)
    (hvn : v < n) (hp : F.par v < n) :
    ∃ c' k, Exec P W (regCutS B ra) c c' k ∧ ∃ G', LCTE B n (cut F n v) G' c' ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21501 := by
  have e1 := Exec.copyN (P := P) hc 193 ra
  obtain ⟨c', k, G', e, hS', hmf, hfr, -, -, hk, -⟩ := opCut_execE (P := P) B n e1.wb_right hW
    (hS.updN 193 _ (by omega)) (by simp [hv]) hvn hp
  exact ⟨c', 1 + k, .seq e1 e, G', hS', hmf, (regFr_updN (by omega) c _).trans hfr.regFr,
    by omega⟩

/-- **`add` with register operands**: the real `r rz` is added on the root path of `v`. -/
theorem regAdd_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra rz v : ℕ} (hv : c.nreg ra = v)
    (hvn : v < n) :
    ∃ c' k, Exec P W (regAddS B ra rz) c c' k ∧ ∃ G', LCTE B n (addPath F n v (c.rreg rz)) G' c' ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21102 := by
  have e1 := Exec.copyN (P := P) hc 193 ra
  have e2 := Exec.copyR (P := P) e1.wb_right 200 rz
  obtain ⟨c', k, G', e, hS', hmf, hfr, -, -, hk, -⟩ := opAddC_execE (P := P) B n false
    e2.wb_right hW ((hS.updN 193 _ (by omega)).updR 200 _) (by simp [hv]) hvn
  refine ⟨c', 1 + (1 + k), .seq e1 (.seq e2 e), G', ?_, hmf,
    ((regFr_updN (by omega) c _).trans (regFr_updR (by omega) _ _)).trans hfr.regFr, by omega⟩
  simpa [addPathC] using hS'

/-- **`add2` with register operands**: the real `r rz` is added to the second values on the
root path of `v`. -/
theorem regAdd2_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra rz v : ℕ} (hv : c.nreg ra = v)
    (hvn : v < n) :
    ∃ c' k, Exec P W (regAdd2S B ra rz) c c' k ∧
      ∃ G', LCTE B n (addPath2 F n v (c.rreg rz)) G' c' ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21102 := by
  have e1 := Exec.copyN (P := P) hc 193 ra
  have e2 := Exec.copyR (P := P) e1.wb_right 200 rz
  obtain ⟨c', k, G', e, hS', hmf, hfr, -, -, hk⟩ := opAdd2_execE (P := P) B n
    e2.wb_right hW ((hS.updN 193 _ (by omega)).updR 200 _) (by simp [hv]) hvn
  refine ⟨c', 1 + (1 + k), .seq e1 (.seq e2 e), G', ?_, hmf,
    ((regFr_updN (by omega) c _).trans (regFr_updR (by omega) _ _)).trans hfr.regFr, by omega⟩
  simpa using hS'

/-- **`evert` with a register operand.** -/
theorem regEvert_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra v : ℕ} (hv : c.nreg ra = v)
    (hvn : v < n) :
    ∃ c' k, Exec P W (regEvertS B ra) c c' k ∧ ∃ G', LCTE B n (evert F n v) G' c' ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21301 := by
  have e1 := Exec.copyN (P := P) hc 193 ra
  obtain ⟨c', k, G', e, hS', hmf, hfr, -, -, hk⟩ := opEvert_exec (P := P) B n e1.wb_right hW
    (hS.updN 193 _ (by omega)) (by simp [hv]) hvn
  exact ⟨c', 1 + k, .seq e1 e, G', hS', hmf, (regFr_updN (by omega) c _).trans hfr.regFr,
    by omega⟩

/-- **The queries with a register operand**: the root, the minimum on the root path and the node
attaining it (closest to the root), and the path sum, left in registers. -/
theorem regQuery_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra v : ℕ} (hv : c.nreg ra = v)
    (hvn : v < n) :
    ∃ c' k, Exec P W (regQueryS B ra) c c' k ∧ ∃ G', LCTE B n F G' c' ∧
      c'.nreg 195 = findRoot F n v ∧ c'.nreg 196 = (pathMin F n v).2 ∧
      c'.rreg 195 = (pathMin F n v).1 ∧ c'.rreg 196 = pathSum F n v ∧
      c'.rreg 200 = c.rreg 200 ∧ MemFrame B n (mem c) (mem c') ∧ RegFr c c' ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21101 := by
  have e1 := Exec.copyN (P := P) hc 193 ra
  obtain ⟨c', k, G', e, hS', h1, h2, h3, h4, hmf, hfr, -, -, hk, -⟩ := opQuery_execE (P := P) B n
    e1.wb_right hW (hS.updN 193 _ (by omega)) (by simp [hv]) hvn
  exact ⟨c', 1 + k, .seq e1 e, G', hS', h1, h2, h3, h4, (hfr.1 200 (by omega)).2, hmf,
    (regFr_updN (by omega) c _).trans hfr.regFr, by omega⟩

/-- **The queries on the second values with a register operand.** -/
theorem regQuery2_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c)
    (hW : B + 16 * (n + 1) ≤ W) {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra v : ℕ}
    (hv : c.nreg ra = v) (hvn : v < n) :
    ∃ c' k, Exec P W (regQuery2S B ra) c c' k ∧ ∃ G', LCTE B n F G' c' ∧
      c'.nreg 196 = (pathMin2 F n v).2 ∧ c'.rreg 195 = (pathMin2 F n v).1 ∧
      c'.rreg 196 = pathSum2 F n v ∧
      c'.rreg 200 = c.rreg 200 ∧ MemFrame B n (mem c) (mem c') ∧ RegFr c c' ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21101 := by
  have e1 := Exec.copyN (P := P) hc 193 ra
  obtain ⟨c', k, G', e, hS', h2, h3, h4, hmf, hfr, -, -, hk⟩ := opQuery2_exec (P := P) B n
    e1.wb_right hW (hS.updN 193 _ (by omega)) (by simp [hv]) hvn
  exact ⟨c', 1 + k, .seq e1 e, G', hS', h2, h3, h4, (hfr.1 200 (by omega)).2, hmf,
    (regFr_updN (by omega) c _).trans hfr.regFr, by omega⟩

/-- **The parent with a register operand** (`n` for a root), read from the access. -/
theorem regParent_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c)
    (hW : B + 16 * (n + 1) ≤ W) {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra v : ℕ}
    (hv : c.nreg ra = v) (hvn : v < n) :
    ∃ c' k, Exec P W (regParentS B ra) c c' k ∧ ∃ G', LCTE B n F G' c' ∧
      c'.nreg 195 = F.par v ∧
      c'.rreg 200 = c.rreg 200 ∧ MemFrame B n (mem c) (mem c') ∧ RegFr c c' ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21101 := by
  have e1 := Exec.copyN (P := P) hc 193 ra
  obtain ⟨c', k, G', e, hS', h1, hmf, hfr, -, -, hk⟩ := opParentAcc_exec (P := P) B n
    e1.wb_right hW (hS.updN 193 _ (by omega)) (by simp [hv]) hvn
  exact ⟨c', 1 + k, .seq e1 e, G', hS', h1, (hfr.1 200 (by omega)).2, hmf,
    (regFr_updN (by omega) c _).trans hfr.regFr, by omega⟩

/-! ### The minimum with the comparison bit -/

/-- The comparison bit: `r198 := 1` if real `r195 < ` real `r200`, `0` otherwise. -/
def bitS : Stmt := .ifLtR 195 200 (.instr (.constN 198 1)) (.instr (.constN 198 0))

/-- `min`: the queries at `v = r ra`, then `r198 := 1` if the minimum on the root path is below
the real `r rz`, `0` otherwise. -/
def regMinS (B ra rz : ℕ) : Stmt :=
  .seq (.instr (.copyR 200 rz)) <| .seq (regQueryS B ra) bitS

/-- `min2`: the same on the second values. -/
def regMin2S (B ra rz : ℕ) : Stmt :=
  .seq (.instr (.copyR 200 rz)) <| .seq (regQuery2S B ra) bitS

theorem bitS_exec {c : Config} (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W bitS c c' k ∧ k ≤ 3 ∧
      c' = { c with nreg := upd c.nreg 198 (if c.rreg 195 < c.rreg 200 then 1 else 0) } := by
  by_cases h : c.rreg 195 < c.rreg 200
  · exact ⟨_, _, .ifLtR_true h (Exec.constN hc 198 1 hW), by omega, by simp [h]⟩
  · exact ⟨_, _, .ifLtR_false h (Exec.constN hc 198 0 (Nat.zero_le _)), by omega, by simp [h]⟩

/-- **`min` with register operands**: the results of the queries (`regQuery_exec`) and the
comparison bit in `r198`. -/
theorem regMin_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra rz v : ℕ} (hv : c.nreg ra = v)
    (hvn : v < n) :
    ∃ c' k, Exec P W (regMinS B ra rz) c c' k ∧ ∃ G', LCTE B n F G' c' ∧
      c'.nreg 196 = (pathMin F n v).2 ∧ c'.rreg 195 = (pathMin F n v).1 ∧
      c'.nreg 198 = (if (pathMin F n v).1 < c.rreg rz then 1 else 0) ∧
      c'.nreg 195 = findRoot F n v ∧ c'.rreg 196 = pathSum F n v ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21105 := by
  have e1 := Exec.copyR (P := P) hc 200 rz
  obtain ⟨c2, k2, e2, G2, hS2, r195, r196, q195, q196, q200, hmf, hfr, hk⟩ :=
    regQuery_exec (P := P) B n e1.wb_right hW (hS.updR 200 _) (by simpa using hv) hvn
  obtain ⟨c3, k3, e3, hk3, rfl⟩ := bitS_exec (P := P) e2.wb_right (by omega)
  refine ⟨_, 1 + (k2 + k3), .seq e1 (.seq e2 e3), G2, hS2.updN 198 _ (by omega), ?_, ?_, ?_, ?_,
    ?_, hmf, ((regFr_updR (by omega) c _).trans hfr).trans (regFr_updN (by omega) _ _),
    by omega⟩
  · simpa using r196
  · simpa using q195
  · simp [q195, q200]
  · simpa using r195
  · simpa using q196

/-- **`min2` with register operands**: the results of the queries on the second values
(`regQuery2_exec`) and the comparison bit in `r198`. -/
theorem regMin2_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra rz v : ℕ} (hv : c.nreg ra = v)
    (hvn : v < n) :
    ∃ c' k, Exec P W (regMin2S B ra rz) c c' k ∧ ∃ G', LCTE B n F G' c' ∧
      c'.nreg 196 = (pathMin2 F n v).2 ∧ c'.rreg 195 = (pathMin2 F n v).1 ∧
      c'.nreg 198 = (if (pathMin2 F n v).1 < c.rreg rz then 1 else 0) ∧
      c'.rreg 196 = pathSum2 F n v ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21105 := by
  have e1 := Exec.copyR (P := P) hc 200 rz
  obtain ⟨c2, k2, e2, G2, hS2, r196, q195, q196, q200, hmf, hfr, hk⟩ :=
    regQuery2_exec (P := P) B n e1.wb_right hW (hS.updR 200 _) (by simpa using hv) hvn
  obtain ⟨c3, k3, e3, hk3, rfl⟩ := bitS_exec (P := P) e2.wb_right (by omega)
  refine ⟨_, 1 + (k2 + k3), .seq e1 (.seq e2 e3), G2, hS2.updN 198 _ (by omega), ?_, ?_, ?_,
    ?_, hmf, ((regFr_updR (by omega) c _).trans hfr).trans (regFr_updN (by omega) _ _),
    by omega⟩
  · simpa using r196
  · simpa using q195
  · simp [q195, q200]
  · simpa using q196

end

end DynTree

end PlanarFlow
