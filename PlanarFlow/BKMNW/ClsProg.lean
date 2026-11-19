module

public import PlanarFlow.BKMNW.ClsIdD
public import PlanarFlow.BKMNW.CompGraphProg
public import PlanarFlow.BKMNW.PcNfProg

/-!
# The classes of a split on the machine

`clsF M P Nf Hs K ρ` (the class function of a split) as numbers on the machine: a scan writing
the input of the graph of the components of `Nf \ J` (`clsRv`, `clsYf`), the labelling `ccProg`
(`PlanarFlow/BKMNW/CompGraphProg.lean`), a scan writing `ID[i] = clsIdF … i`
(`PlanarFlow/BKMNW/ClsIdD.lean`). Straight-line bodies, branch-free (`nzF x = x / x`).

Registers: `4440 = n`, `4441 = RVb`, `4442 = YTb`, `4443 = YHb`, `4444 = NFb`, `4445 = R2b`,
`4446 = Y2b`, `4447 = TKb`, `4448 = LABb`, `4449 = IDb`, `4450 = K`; written `4451 … 4469`.

* `csCnF`, `csSelF` and their meaning; `csP` (scan 1 body), `csI` (scan 2 body), `csScan1`,
  `csScan2`, **`clsProg`**;
* **`csScan1_exec`**, **`csScan2_exec`**, **`clsProg_exec`**, **`clsProg_clsF`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine

/-! ### Branch-free values -/

/-- The flag "in `Nf`, not both ends in `Y`". -/
def csCnF (yt yh nf : ℕ) : ℕ := nzF nf * (1 - nzF yt * nzF yh)

lemma nzF_le1 (x : ℕ) : nzF x ≤ 1 := by rw [nzF_eq]; split_ifs <;> omega

lemma csCnF_eq (yt yh nf : ℕ) :
    csCnF yt yh nf = if 0 < nf ∧ ¬ (0 < yt ∧ 0 < yh) then 1 else 0 := by
  unfold csCnF; rw [nzF_eq, nzF_eq, nzF_eq]
  by_cases h1 : nf = 0 <;> by_cases h2 : yt = 0 <;> by_cases h3 : yh = 0 <;> simp [h1, h2, h3] <;>
    omega

lemma csCnF_le1 (yt yh nf : ℕ) : csCnF yt yh nf ≤ 1 := by rw [csCnF_eq]; split_ifs <;> omega

/-- Select `y` if `b = 1`, `x` if `b = 0`. -/
def csSelF (b x y : ℕ) : ℕ := (1 - b) * x + b * y

lemma csSelF_eq {b : ℕ} (hb : b ≤ 1) (x y : ℕ) : csSelF b x y = if b = 1 then y else x := by
  unfold csSelF; interval_cases b <;> simp

lemma csSelF_le {b x y B : ℕ} (hb : b ≤ 1) (hx : x ≤ B) (hy : y ≤ B) : csSelF b x y ≤ B := by
  rw [csSelF_eq hb]; split_ifs <;> assumption

lemma cs_mul_le {a b : ℕ} (ha : a ≤ 1) : a * b ≤ b := by
  interval_cases a <;> simp

/-! ### Scan 1: the input of the graph of the components -/

open WordRAM.Machine.Stmt WordRAM.Programs

/-- Scan 1 at the index `i`: `R2[i] := clsRv …`, `Y2[i] := clsYf …` (branch-free). -/
def csP : Stmt :=
  block [.addN 4453 4442 4452, .loadN 4453 4453, .addN 4454 4443 4452, .loadN 4454 4454,
    .addN 4455 4444 4452, .loadN 4455 4455, .divN 4453 4453 4453, .divN 4454 4454 4454,
    .divN 4455 4455 4455, .mulN 4456 4453 4454, .subN 4456 4451 4456, .mulN 4456 4455 4456,
    .addN 4457 4441 4452, .loadN 4457 4457, .addN 4458 4442 4457, .loadN 4458 4458,
    .addN 4459 4443 4457, .loadN 4459 4459, .addN 4460 4444 4457, .loadN 4460 4460,
    .divN 4458 4458 4458, .divN 4459 4459 4459, .divN 4460 4460 4460, .mulN 4461 4458 4459,
    .subN 4461 4451 4461, .mulN 4461 4460 4461, .mulN 4462 4456 4461, .subN 4463 4451 4462,
    .mulN 4463 4463 4452, .mulN 4464 4462 4457, .addN 4463 4463 4464, .addN 4465 4445 4452,
    .storeN 4465 4463, .subN 4464 4451 4456, .addN 4466 4453 4464, .mulN 4467 4453 4464,
    .subN 4466 4466 4467, .addN 4465 4446 4452, .storeN 4465 4466, .addN 4452 4452 4451]

/-- The value written at `R2[i]`. -/
def csV1 (m : ℕ → ℕ) (RVb YTb YHb NFb i : ℕ) : ℕ :=
  csSelF (csCnF (m (YTb + i)) (m (YHb + i)) (m (NFb + i)) *
    csCnF (m (YTb + m (RVb + i))) (m (YHb + m (RVb + i))) (m (NFb + m (RVb + i)))) i (m (RVb + i))

/-- The value written at `Y2[i]`. -/
def csV2 (m : ℕ → ℕ) (YTb YHb NFb i : ℕ) : ℕ :=
  orF (nzF (m (YTb + i))) (1 - csCnF (m (YTb + i)) (m (YHb + i)) (m (NFb + i)))

syntax "cs_le1" : tactic
macro_rules
  | `(tactic| cs_le1) =>
    `(tactic| first | exact pn_dsl _ | exact Nat.sub_le _ _ | (refine pn_m1 ?_ ?_ <;> cs_le1))

syntax "cs_side" : tactic
macro_rules
  | `(tactic| cs_side) => `(tactic| first
    | omega
    | exact le_trans (pn_dsl _) (by omega)
    | exact le_trans (Nat.sub_le _ _) (by omega)
    | exact le_trans (pn_m1 (by cs_le1) (by cs_le1)) (by omega)
    | exact le_trans (cs_mul_le (by cs_le1)) (by omega)
    | exact le_trans (Nat.add_le_add (cs_mul_le (by cs_le1)) (cs_mul_le (by cs_le1))) (by omega)
    | exact le_trans (Nat.add_le_add (by cs_le1) (by cs_le1)) (by omega)
    | exact le_trans (Nat.sub_le _ _) (le_trans (Nat.add_le_add (by cs_le1) (by cs_le1)) (by omega)))


lemma cs_sel_le' {b x y B : ℕ} (hb : b ≤ 1) (hx : x ≤ B) (hy : y ≤ B) :
    (1 - b) * x + b * y ≤ B := by
  interval_cases b <;> simp <;> omega

syntax "cs_bnd" : tactic
macro_rules
  | `(tactic| cs_bnd) => `(tactic| first
    | omega
    | exact le_trans (pn_dsl _) (by omega)
    | exact le_trans (Nat.sub_le _ _) (by omega)
    | (refine cs_sel_le' ?_ ?_ ?_ <;> first | cs_le1 | cs_bnd)
    | (refine le_trans (cs_mul_le ?_) ?_ <;> first | cs_le1 | cs_bnd))

/-! ### Scan 2: the numbers of the classes -/

/-- Scan 2 at the index `i`: `ID[i] := clsIdF …` (branch-free). -/
def csI : Stmt :=
  block [.addN 4453 4442 4452, .loadN 4453 4453, .divN 4453 4453 4453,
    .addN 4454 4443 4452, .loadN 4454 4454, .divN 4454 4454 4454, .mulN 4454 4453 4454,
    .addN 4455 4444 4452, .loadN 4455 4455, .divN 4455 4455 4455,
    .divN 4456 4450 4450, .subN 4456 4451 4456,
    .addN 4457 4441 4452, .loadN 4457 4457, .subN 4458 4452 4457, .subN 4458 4452 4458,
    .addN 4459 4458 4458, .addN 4459 4459 4458,
    .addN 4460 4447 4452, .loadN 4460 4460, .addN 4461 4460 4460, .addN 4461 4461 4460,
    .addN 4461 4461 4451, .addN 4461 4461 4451,
    .addN 4462 4448 4452, .loadN 4462 4462, .addN 4463 4462 4462, .addN 4463 4463 4462,
    .addN 4463 4463 4451,
    .subN 4464 4451 4456, .mulN 4464 4464 4461, .mulN 4465 4456 4459, .addN 4464 4464 4465,
    .subN 4465 4451 4455, .mulN 4465 4465 4464, .mulN 4466 4455 4463, .addN 4465 4465 4466,
    .subN 4466 4451 4454, .mulN 4466 4466 4465, .mulN 4467 4454 4459, .addN 4466 4466 4467,
    .addN 4467 4449 4452, .storeN 4467 4466, .addN 4452 4452 4451]

/-- The value written at `ID[i]`. -/
def csV3 (m : ℕ → ℕ) (RVb YTb YHb NFb TKb LABb K i : ℕ) : ℕ :=
  csSelF (nzF (m (YTb + i)) * nzF (m (YHb + i)))
    (csSelF (nzF (m (NFb + i)))
      (csSelF (1 - nzF K) (m (TKb + i) + m (TKb + i) + m (TKb + i) + 1 + 1)
        ((i - (i - m (RVb + i))) + (i - (i - m (RVb + i))) + (i - (i - m (RVb + i)))))
      (m (LABb + i) + m (LABb + i) + m (LABb + i) + 1))
    ((i - (i - m (RVb + i))) + (i - (i - m (RVb + i))) + (i - (i - m (RVb + i))))

/-! ### The values -/

section Values

variable {m m₀ : ℕ → ℕ} {RVb YTb YHb NFb TKb LABb K n i : ℕ}

lemma csCnF_cls (m : ℕ → ℕ) (YTb YHb NFb j : ℕ) :
    csCnF (m (YTb + j)) (m (YHb + j)) (m (NFb + j)) =
      if clsN (fun j => m (YTb + j)) (fun j => m (YHb + j)) (fun j => m (NFb + j)) j then 1
      else 0 := by
  rw [csCnF_eq]; rfl

lemma nzF_eq_one {x : ℕ} : nzF x = 1 ↔ 0 < x := by
  rw [nzF_eq]; by_cases h : x = 0 <;> simp [h] <;> omega

/-- The value of scan 1 at `R2[i]` is `clsRv`. -/
lemma csV1_eq (hfr : ∀ a < NFb + n, m a = m₀ a) (h1 : RVb + n ≤ YTb) (h2 : YTb + n ≤ YHb)
    (h3 : YHb + n ≤ NFb) (hi : i < n) (hr : m₀ (RVb + i) < n) :
    csV1 m RVb YTb YHb NFb i = clsRv (fun j => m₀ (RVb + j)) (fun j => m₀ (YTb + j))
      (fun j => m₀ (YHb + j)) (fun j => m₀ (NFb + j)) i := by
  have e1 : m (RVb + i) = m₀ (RVb + i) := hfr _ (by omega)
  unfold csV1
  rw [e1, hfr (YTb + i) (by omega), hfr (YHb + i) (by omega), hfr (NFb + i) (by omega),
    hfr (YTb + m₀ (RVb + i)) (by omega), hfr (YHb + m₀ (RVb + i)) (by omega),
    hfr (NFb + m₀ (RVb + i)) (by omega), csCnF_cls, csCnF_cls]
  unfold clsRv
  by_cases ha : clsN (fun j => m₀ (YTb + j)) (fun j => m₀ (YHb + j)) (fun j => m₀ (NFb + j)) i <;>
    by_cases hb : clsN (fun j => m₀ (YTb + j)) (fun j => m₀ (YHb + j))
      (fun j => m₀ (NFb + j)) (m₀ (RVb + i)) <;>
    simp [ha, hb, csSelF]

/-- The value of scan 1 at `Y2[i]` is nonzero exactly when `clsYf` holds. -/
lemma csV2_pos (hfr : ∀ a < NFb + n, m a = m₀ a) (h2 : YTb + n ≤ YHb) (h3 : YHb + n ≤ NFb)
    (hi : i < n) :
    (0 < csV2 m YTb YHb NFb i ↔ clsYf (fun j => m₀ (YTb + j)) (fun j => m₀ (YHb + j))
      (fun j => m₀ (NFb + j)) i = true) := by
  unfold csV2 clsYf
  rw [hfr (YTb + i) (by omega), hfr (YHb + i) (by omega), hfr (NFb + i) (by omega), csCnF_cls]
  by_cases ha : clsN (fun j => m₀ (YTb + j)) (fun j => m₀ (YHb + j)) (fun j => m₀ (NFb + j)) i <;>
    by_cases hy : m₀ (YTb + i) = 0 <;> simp [ha, hy, orF, nzF_eq] <;> omega

/-- The value of scan 2 at `ID[i]` is `clsIdF`. -/
lemma csV3_eq (hfr : ∀ a < NFb + n, m a = m₀ a) (htk : ∀ j < n, m (TKb + j) = m₀ (TKb + j))
    (h1 : RVb + n ≤ YTb) (h2 : YTb + n ≤ YHb) (h3 : YHb + n ≤ NFb) (hi : i < n) :
    csV3 m RVb YTb YHb NFb TKb LABb K i = clsIdF K (fun j => m₀ (RVb + j))
      (fun j => m₀ (TKb + j)) (fun j => m₀ (YTb + j)) (fun j => m₀ (YHb + j))
      (fun j => m₀ (NFb + j)) (fun j => m (LABb + j)) i := by
  unfold csV3 clsIdF clsJ
  rw [hfr (RVb + i) (by omega), hfr (YTb + i) (by omega), hfr (YHb + i) (by omega),
    hfr (NFb + i) (by omega), htk i hi]
  have hm : i - (i - m₀ (RVb + i)) = min i (m₀ (RVb + i)) := by omega
  rw [hm]
  have hJ : nzF (m₀ (YTb + i)) * nzF (m₀ (YHb + i)) =
      if 0 < m₀ (YTb + i) ∧ 0 < m₀ (YHb + i) then 1 else 0 := by
    rw [nzF_eq, nzF_eq]
    by_cases a : m₀ (YTb + i) = 0 <;> by_cases b : m₀ (YHb + i) = 0 <;> simp [a, b] <;> omega
  have hZ : 1 - nzF K = if K = 0 then 1 else 0 := by rw [nzF_eq]; split_ifs <;> omega
  rw [hJ, hZ, csSelF_eq (by split_ifs <;> omega), csSelF_eq (nzF_le1 _),
    csSelF_eq (by split_ifs <;> omega)]
  simp only [nzF_eq_one]
  split_ifs <;> first | contradiction | omega | rfl

end Values

/-- Scan 1. -/
def csScan1 : Stmt := .seq (block [.constN 4451 1, .constN 4452 0]) (.whileLtN 4452 4440 csP)

/-- Scan 2. -/
def csScan2 : Stmt := .seq (block [.constN 4451 1, .constN 4452 0]) (.whileLtN 4452 4440 csI)

/-- **The classes of a split on the machine.** -/
def clsProg : Stmt := .seq csScan1 (.seq ccProg csScan2)

lemma csV3_congr {m m' : ℕ → ℕ} {RVb YTb YHb NFb TKb LABb K i : ℕ}
    (e1 : m' (RVb + i) = m (RVb + i)) (e2 : m' (YTb + i) = m (YTb + i))
    (e3 : m' (YHb + i) = m (YHb + i)) (e4 : m' (NFb + i) = m (NFb + i))
    (e5 : m' (TKb + i) = m (TKb + i)) (e6 : m' (LABb + i) = m (LABb + i)) :
    csV3 m' RVb YTb YHb NFb TKb LABb K i = csV3 m RVb YTb YHb NFb TKb LABb K i := by
  unfold csV3; rw [e1, e2, e3, e4, e5, e6]

lemma CgEnumSub.congr {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} {B N : Finset D} {Hs : List (Finset V)}
    {Y : Finset V} {n : ℕ} {e : ℕ → D} {rv key rv' key' : ℕ → ℕ} {yf yf' : ℕ → Bool}
    (hE : CgEnumSub M B N Hs Y n e rv key yf) (h1 : ∀ i < n, rv' i = rv i)
    (h2 : ∀ i < n, key' i = key i) (h3 : ∀ i < n, yf' i = yf i) :
    CgEnumSub M B N Hs Y n e rv' key' yf' := by
  refine ⟨hE.mem, hE.surj, hE.inj, hE.sub, fun i hi => ?_, fun i hi a b => ?_,
    fun i hi a => ?_, fun i hi j hj => ?_, fun i hi => ?_⟩
  · rw [h1 i hi]; exact hE.rvlt i hi
  · rw [h1 i hi]; exact hE.rvin i hi a b
  · rw [h1 i hi]; exact hE.rvout i hi a
  · rw [h2 i hi, h2 j hj]; exact hE.key i hi j hj
  · rw [h3 i hi]; exact hE.yf i hi

/-- The layout of `clsProg`: `RV | YT | YH | NF | R2 | TK | Y2 | LS | OFF | ADJ | LAB | Q | ID`. -/
structure ClsLay (n nk RVb YTb YHb NFb R2b TKb Y2b LSb OFFb ADJb LABb Qb IDb W : ℕ) : Prop where
  a1 : RVb + n ≤ YTb
  a2 : YTb + n ≤ YHb
  a3 : YHb + n ≤ NFb
  a4 : NFb + n ≤ R2b
  cg : CgLay n nk R2b TKb Y2b LSb OFFb ADJb
  bf : BfLay n (3 * n) OFFb ADJb LABb Qb W
  a5 : Qb + n + 1 ≤ IDb
  a6 : IDb + n ≤ W
  a7 : 3 * (n + nk) + 2 ≤ W

/-- The frame of a body: the registers outside `4452 … 4467` are not written. -/
macro "cs_frame" x:ident : tactic => `(tactic| (
  have e4452 : $x ≠ 4452 := by omega
  have e4453 : $x ≠ 4453 := by omega
  have e4454 : $x ≠ 4454 := by omega
  have e4455 : $x ≠ 4455 := by omega
  have e4456 : $x ≠ 4456 := by omega
  have e4457 : $x ≠ 4457 := by omega
  have e4458 : $x ≠ 4458 := by omega
  have e4459 : $x ≠ 4459 := by omega
  have e4460 : $x ≠ 4460 := by omega
  have e4461 : $x ≠ 4461 := by omega
  have e4462 : $x ≠ 4462 := by omega
  have e4463 : $x ≠ 4463 := by omega
  have e4464 : $x ≠ 4464 := by omega
  have e4465 : $x ≠ 4465 := by omega
  have e4466 : $x ≠ 4466 := by omega
  have e4467 : $x ≠ 4467 := by omega
  simp only [Config.nreg_mk, upd_other _ _ _ e4452, upd_other _ _ _ e4453, upd_other _ _ _ e4454, upd_other _ _ _ e4455, upd_other _ _ _ e4456, upd_other _ _ _ e4457, upd_other _ _ _ e4458, upd_other _ _ _ e4459, upd_other _ _ _ e4460, upd_other _ _ _ e4461, upd_other _ _ _ e4462, upd_other _ _ _ e4463, upd_other _ _ _ e4464, upd_other _ _ _ e4465, upd_other _ _ _ e4466, upd_other _ _ _ e4467]))

section Exec

variable {P : Input} {W : ℕ}

theorem csP_exec (c : Config) (hc : WordsBounded W c) {RVb YTb YHb NFb R2b Y2b i n : ℕ}
    (r1 : c.nreg 4441 = RVb) (r2 : c.nreg 4442 = YTb) (r3 : c.nreg 4443 = YHb)
    (r4 : c.nreg 4444 = NFb) (r5 : c.nreg 4445 = R2b) (r6 : c.nreg 4446 = Y2b)
    (r11 : c.nreg 4451 = 1) (r12 : c.nreg 4452 = i)
    (hr : c.nmem (RVb + i) < n) (hi : i < n) (w1 : RVb + n ≤ W) (w2 : YTb + n ≤ W)
    (w3 : YHb + n ≤ W) (w4 : NFb + n ≤ W) (w5 : R2b + n ≤ W) (w6 : Y2b + n ≤ W)
    (w7 : 2 * n + 2 ≤ W) :
    ∃ c' k, Exec P W csP c c' k ∧ k = 40 ∧ c'.nreg 4452 = i + 1 ∧
      c'.nmem = upd (upd c.nmem (R2b + i) (csV1 c.nmem RVb YTb YHb NFb i)) (Y2b + i)
        (csV2 c.nmem YTb YHb NFb i) ∧
      (∀ x, (x < 4452 ∨ 4467 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold csP
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5, r6, r11, r12]; cs_side)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r11, r12]
  · config_simp; simp only [r1, r2, r3, r4, r5, r6, r11, r12, csV1, csV2, csSelF, csCnF, orF, nzF]
  · cs_frame x

theorem csI_exec (c : Config) (hc : WordsBounded W c) {RVb YTb YHb NFb TKb LABb IDb K i n nk : ℕ}
    (r1 : c.nreg 4441 = RVb) (r2 : c.nreg 4442 = YTb) (r3 : c.nreg 4443 = YHb)
    (r4 : c.nreg 4444 = NFb) (r7 : c.nreg 4447 = TKb) (r8 : c.nreg 4448 = LABb)
    (r9 : c.nreg 4449 = IDb) (r10 : c.nreg 4450 = K) (r11 : c.nreg 4451 = 1)
    (r12 : c.nreg 4452 = i)
    (hr : c.nmem (RVb + i) < n) (htk : c.nmem (TKb + i) < nk) (hlab : c.nmem (LABb + i) ≤ n)
    (hi : i < n) (w1 : RVb + n ≤ W) (w2 : YTb + n ≤ W)
    (w3 : YHb + n ≤ W) (w4 : NFb + n ≤ W) (w5 : TKb + n ≤ W) (w6 : LABb + n ≤ W)
    (w8 : IDb + n ≤ W) (w7 : 3 * (n + nk) + 2 ≤ W) :
    ∃ c' k, Exec P W csI c c' k ∧ k = 44 ∧ c'.nreg 4452 = i + 1 ∧
      c'.nmem = upd c.nmem (IDb + i) (csV3 c.nmem RVb YTb YHb NFb TKb LABb K i) ∧
      (∀ x, (x < 4452 ∨ 4467 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold csI
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r7, r8, r9, r10, r11, r12]; cs_bnd)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r11, r12]
  · config_simp; simp only [r1, r2, r3, r4, r7, r8, r9, r10, r11, r12, csV3, csSelF, nzF]
  · cs_frame x

/-- The constants of a scan. -/
theorem csInit_exec (c : Config) (hc : WordsBounded W c) (h1 : 1 ≤ W) :
    ∃ c' k, Exec P W (block [.constN 4451 1, .constN 4452 0]) c c' k ∧ k = 2 ∧
      c'.nreg 4451 = 1 ∧ c'.nreg 4452 = 0 ∧
      (∀ x, x ≠ 4451 → x ≠ 4452 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · config_simp
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **Scan 1**: `R2[j] = clsRv … j`, `0 < Y2[j] ↔ clsYf … j` for `j < n`. -/
theorem csScan1_exec (c : Config) (hc : WordsBounded W c) {n RVb YTb YHb NFb R2b Y2b : ℕ}
    (h1 : RVb + n ≤ YTb) (h2 : YTb + n ≤ YHb) (h3 : YHb + n ≤ NFb) (h4 : NFb + n ≤ R2b)
    (h5 : R2b + n ≤ Y2b) (h6 : Y2b + n ≤ W) (h7 : 2 * n + 2 ≤ W)
    (hRV : ∀ j < n, c.nmem (RVb + j) < n)
    (r0 : c.nreg 4440 = n) (r1 : c.nreg 4441 = RVb) (r2 : c.nreg 4442 = YTb)
    (r3 : c.nreg 4443 = YHb) (r4 : c.nreg 4444 = NFb) (r5 : c.nreg 4445 = R2b)
    (r6 : c.nreg 4446 = Y2b) :
    ∃ c' k, Exec P W csScan1 c c' k ∧ k ≤ 42 * n + 4 ∧
      (∀ j < n, c'.nmem (R2b + j) = clsRv (fun j => c.nmem (RVb + j))
        (fun j => c.nmem (YTb + j)) (fun j => c.nmem (YHb + j)) (fun j => c.nmem (NFb + j)) j) ∧
      (∀ j < n, (0 < c'.nmem (Y2b + j) ↔ clsYf (fun j => c.nmem (YTb + j))
        (fun j => c.nmem (YHb + j)) (fun j => c.nmem (NFb + j)) j = true)) ∧
      (∀ a, ¬ (R2b ≤ a ∧ a < R2b + n) → ¬ (Y2b ≤ a ∧ a < Y2b + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4451 ∨ 4467 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold csScan1
  obtain ⟨c₁, k₁, e₁, hk₁, g1, g2, gn₁, gm₁, gr₁, grm₁, go₁⟩ := csInit_exec (P := P) c hc
    (by omega)
  have hw₁ := e₁.wb_right
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4452 ∨ 4467 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (R2b + j) = clsRv (fun j => m₀ (RVb + j)) (fun j => m₀ (YTb + j))
      (fun j => m₀ (YHb + j)) (fun j => m₀ (NFb + j)) j ∧
      (0 < c'.nmem (Y2b + j) ↔ clsYf (fun j => m₀ (YTb + j)) (fun j => m₀ (YHb + j))
        (fun j => m₀ (NFb + j)) j = true)) ∧
    (∀ a, ¬ (R2b ≤ a ∧ a < R2b + i) → ¬ (Y2b ≤ a ∧ a < Y2b + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  have q : ∀ x, x ≠ 4451 → x ≠ 4452 → c₁.nreg x = c.nreg x := gn₁
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h52, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P) (a := 4452)
    (b := 4440) (body := csP) J (B := 40) c₁ hw₁ g2 (by rw [q _ (by omega) (by omega), r0])
    (Nat.zero_le n) ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega),
      fun a _ _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h52 h40 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 4452 ∨ 4467 < x) → c'.nreg x = c₁.nreg x := j1
      have hfr : ∀ a < NFb + n, c'.nmem a = m₀ a := fun a ha => j3 a (by omega) (by omega)
      have hri := hRV i hhi
      obtain ⟨c'', t, ex, ht, h52', hm', hn', hr', hrm', ho'⟩ := csP_exec (P := P) (n := n) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r3])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r4])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r5])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r6])
        (by rw [f _ (by omega), g1]) h52 (by rw [hfr _ (by omega)]; exact hri) hhi (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) h7
      have v1 := csV1_eq (m := c'.nmem) (m₀ := m₀) hfr h1 h2 h3 hhi hri
      have v2 := csV2_pos (m := c'.nmem) (m₀ := m₀) hfr h2 h3 hhi
      refine ⟨c'', t, ex, ht.le, h52', by rw [hn' _ (by omega)]; exact h40,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha1 ha2 => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
          exact j2 j hj
        · rw [upd_other _ _ _ (by omega), upd_same, upd_same, v1]
          exact ⟨rfl, v2⟩
      · rw [hm', upd_other _ _ _ (fun h => ha2 ⟨by omega, by omega⟩),
          upd_other _ _ _ (fun h => ha1 ⟨by omega, by omega⟩)]
        exact j3 a (fun h => ha1 ⟨h.1, by omega⟩) (fun h => ha2 ⟨h.1, by omega⟩))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fun j hj => (j2 j hj).1, fun j hj => (j2 j hj).2,
    j3, fun x hx => ?_, by rw [j4, gr₁], by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega)]

/-- **Scan 2**: `ID[j] = csV3 … j` for `j < n`. -/
theorem csScan2_exec (c : Config) (hc : WordsBounded W c)
    {n nk RVb YTb YHb NFb TKb LABb IDb K : ℕ}
    (h1 : RVb + n ≤ IDb) (h2 : YTb + n ≤ IDb) (h3 : YHb + n ≤ IDb) (h4 : NFb + n ≤ IDb)
    (h5 : TKb + n ≤ IDb) (h6 : LABb + n ≤ IDb) (h7 : IDb + n ≤ W) (h8 : 3 * (n + nk) + 2 ≤ W)
    (hRV : ∀ j < n, c.nmem (RVb + j) < n) (hTK : ∀ j < n, c.nmem (TKb + j) < nk)
    (hLAB : ∀ j < n, c.nmem (LABb + j) ≤ n)
    (r0 : c.nreg 4440 = n) (r1 : c.nreg 4441 = RVb) (r2 : c.nreg 4442 = YTb)
    (r3 : c.nreg 4443 = YHb) (r4 : c.nreg 4444 = NFb) (r7 : c.nreg 4447 = TKb)
    (r8 : c.nreg 4448 = LABb) (r9 : c.nreg 4449 = IDb) (r10 : c.nreg 4450 = K) :
    ∃ c' k, Exec P W csScan2 c c' k ∧ k ≤ 46 * n + 4 ∧
      (∀ j < n, c'.nmem (IDb + j) = csV3 c.nmem RVb YTb YHb NFb TKb LABb K j) ∧
      (∀ a, ¬ (IDb ≤ a ∧ a < IDb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4451 ∨ 4467 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold csScan2
  obtain ⟨c₁, k₁, e₁, hk₁, g1, g2, gn₁, gm₁, gr₁, grm₁, go₁⟩ := csInit_exec (P := P) c hc
    (by omega)
  have hw₁ := e₁.wb_right
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4452 ∨ 4467 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (IDb + j) = csV3 m₀ RVb YTb YHb NFb TKb LABb K j) ∧
    (∀ a, ¬ (IDb ≤ a ∧ a < IDb + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  have q : ∀ x, x ≠ 4451 → x ≠ 4452 → c₁.nreg x = c.nreg x := gn₁
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h52, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P) (a := 4452)
    (b := 4440) (body := csI) J (B := 44) c₁ hw₁ g2 (by rw [q _ (by omega) (by omega), r0])
    (Nat.zero_le n) ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h52 h40 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 4452 ∨ 4467 < x) → c'.nreg x = c₁.nreg x := j1
      have hfr : ∀ a < IDb, c'.nmem a = m₀ a := fun a ha => j3 a (by omega)
      obtain ⟨c'', t, ex, ht, h52', hm', hn', hr', hrm', ho'⟩ := csI_exec (P := P) (n := n)
        (nk := nk) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r3])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r4])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r7])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r8])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r9])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r10])
        (by rw [f _ (by omega), g1]) h52 (by rw [hfr _ (by omega)]; exact hRV i hhi)
        (by rw [hfr _ (by omega)]; exact hTK i hhi) (by rw [hfr _ (by omega)]; exact hLAB i hhi)
        hhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h8
      have v3 : csV3 c'.nmem RVb YTb YHb NFb TKb LABb K i =
          csV3 m₀ RVb YTb YHb NFb TKb LABb K i :=
        csV3_congr (hfr _ (by omega)) (hfr _ (by omega)) (hfr _ (by omega)) (hfr _ (by omega))
          (hfr _ (by omega)) (hfr _ (by omega))
      refine ⟨c'', t, ex, ht.le, h52', by rw [hn' _ (by omega)]; exact h40,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same, v3]
      · rw [hm', upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
        exact j3 a (fun h => ha ⟨h.1, by omega⟩))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, fun x hx => ?_, by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega)]

/-- **The classes of a split on the machine**: for an enumeration `e` of the darts of `Ps`
described by the input arrays (`ClsEnum`: reverse index, class numbers of the tails, flags of the
ends in the new hole `Y = newHole Hs ρ.mverts`, flags of `Nf`), `Nf ⊆ Ps`, `Y` closed under the
holes and `IsCls Ps (clsF …)` (the first conclusion of `exists_cls'`), with the table and the
labels zero, within `192 n + 24` steps,
`ID[i] = ID[j] ↔ e j ∈ clsF M Ps Nf Hs K ρ (e i)` for `i, j < n`. -/
theorem clsProg_clsF {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} {Ps Nf : Finset D} {Hs : List (Finset V)}
    {K : ℕ} {ρ : HPath M} {e : ℕ → D} (c : Config) (hc : WordsBounded W c)
    {n nk RVb YTb YHb NFb R2b TKb Y2b LSb OFFb ADJb LABb Qb IDb : ℕ}
    (hL : ClsLay n nk RVb YTb YHb NFb R2b TKb Y2b LSb OFFb ADJb LABb Qb IDb W)
    (hE : ClsEnum M Ps Nf Hs (newHole Hs ρ.mverts) n e (fun i => c.nmem (RVb + i))
      (fun i => c.nmem (TKb + i)) (fun i => c.nmem (YTb + i)) (fun i => c.nmem (YHb + i))
      (fun i => c.nmem (NFb + i)))
    (hNf : Nf ⊆ Ps) (hY : HClosed Hs (newHole Hs ρ.mverts)) (hC : IsCls Ps (clsF M Ps Nf Hs K ρ))
    (hTK : ∀ i < n, c.nmem (TKb + i) < nk)
    (hLS : ∀ k < nk, c.nmem (LSb + k) = 0) (hLAB : ∀ u < n, c.nmem (LABb + u) = 0)
    (r0 : c.nreg 4440 = n) (r1 : c.nreg 4441 = RVb) (r2 : c.nreg 4442 = YTb)
    (r3 : c.nreg 4443 = YHb) (r4 : c.nreg 4444 = NFb) (r5 : c.nreg 4445 = R2b)
    (r6 : c.nreg 4446 = Y2b) (r7 : c.nreg 4447 = TKb) (r8 : c.nreg 4448 = LABb)
    (r9 : c.nreg 4449 = IDb) (r10 : c.nreg 4450 = K)
    (t0 : c.nreg 4420 = n) (t1 : c.nreg 4421 = R2b) (t2 : c.nreg 4422 = TKb)
    (t3 : c.nreg 4423 = Y2b) (t4 : c.nreg 4424 = LSb) (t5 : c.nreg 4425 = OFFb)
    (t6 : c.nreg 4426 = ADJb) (s0 : c.nreg 4400 = n) (s1 : c.nreg 4401 = OFFb)
    (s2 : c.nreg 4402 = ADJb) (s3 : c.nreg 4403 = LABb) (s4 : c.nreg 4404 = Qb) :
    ∃ c' k, Exec P W clsProg c c' k ∧ k ≤ 192 * n + 24 ∧
      (∀ i < n, ∀ j < n, (c'.nmem (IDb + i) = c'.nmem (IDb + j) ↔
        e j ∈ clsF M Ps Nf Hs K ρ (e i))) ∧
      (∀ a, (a < R2b ∨ (TKb ≤ a ∧ a < TKb + n) ∨ IDb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4405 ∨ (4436 < x ∧ x < 4451) ∨ 4467 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨a1, a2, a3, a4, hcg, hbf, a5, a6, a7⟩ := hL
  have hcg' := hcg
  have hbf' := hbf
  obtain ⟨l1, l2, l3, l4, l5⟩ := hcg'
  obtain ⟨b1, b2, b3, b4⟩ := hbf'
  set m₀ := c.nmem with hm₀
  have hRV : ∀ j < n, m₀ (RVb + j) < n := fun j hj => hE.rvlt j hj
  unfold clsProg
  -- scan 1
  obtain ⟨c₁, k₁, e₁, hk₁, R1, R2, F1, n₁, gr₁, grm₁, go₁⟩ := csScan1_exec (P := P) c hc a1 a2 a3
    a4 (by omega) (by omega) (by omega) hRV r0 r1 r2 r3 r4 r5 r6
  have hw₁ := e₁.wb_right
  -- the input of the components
  have hsub := (hE.sub hNf).congr (rv' := fun i => c₁.nmem (R2b + i))
    (key' := cgKey c₁.nmem TKb) (yf' := cgYf c₁.nmem Y2b) (fun i hi => R1 i hi)
    (fun i hi => F1 _ (by omega) (by omega)) (fun i hi => by
      have := R2 i hi
      unfold cgYf
      cases h : clsYf (fun j => m₀ (YTb + j)) (fun j => m₀ (YHb + j)) (fun j => m₀ (NFb + j)) i
      · rw [h] at this; simp only [decide_eq_false_iff_not]; intro h'
        exact Bool.false_ne_true (this.1 h')
      · rw [h] at this; simp only [decide_eq_true_eq]; exact this.2 rfl)
  obtain ⟨c₂, k₂, e₂, hk₂, H1, H2, H3, n₂, gr₂, grm₂, go₂⟩ := ccProg_exec (P := P) c₁ hw₁ hcg hbf
    (fun i hi => by rw [F1 _ (by omega) (by omega)]; exact hTK i hi) hsub.rvOK
    (fun k hk => by rw [F1 _ (by omega) (by omega)]; exact hLS k hk)
    (fun u hu => by rw [F1 _ (by omega) (by omega)]; exact hLAB u hu)
    (by rw [n₁ _ (by omega), t0]) (by rw [n₁ _ (by omega), t1]) (by rw [n₁ _ (by omega), t2])
    (by rw [n₁ _ (by omega), t3]) (by rw [n₁ _ (by omega), t4]) (by rw [n₁ _ (by omega), t5])
    (by rw [n₁ _ (by omega), t6]) (by rw [n₁ _ (by omega), s0]) (by rw [n₁ _ (by omega), s1])
    (by rw [n₁ _ (by omega), s2]) (by rw [n₁ _ (by omega), s3]) (by rw [n₁ _ (by omega), s4])
  have hw₂ := e₂.wb_right
  -- reading the inputs after the components
  have fr2 : ∀ a, (a < R2b ∨ (TKb ≤ a ∧ a < TKb + n)) → c₂.nmem a = m₀ a := by
    intro a ha
    rw [H3 a (by omega) (by omega) (by omega), F1 a (by omega) (by omega)]
  -- the labels
  have hlab : ∀ i < n, ∀ j < n, clsN (fun j => m₀ (YTb + j)) (fun j => m₀ (YHb + j))
      (fun j => m₀ (NFb + j)) i → clsN (fun j => m₀ (YTb + j)) (fun j => m₀ (YHb + j))
      (fun j => m₀ (NFb + j)) j →
      ((fun j => c₂.nmem (LABb + j)) i = (fun j => c₂.nmem (LABb + j)) j ↔
        e j ∈ comp M (Nf \ clsJs (M := M) Ps (newHole Hs ρ.mverts)) Hs (newHole Hs ρ.mverts)
          (e i)) := by
    intro i hi j hj hci _
    rw [H1 i hi j hj, mem_comp_iff_cgAdj_sub hY hsub hi hj ((hE.memN hi).2 hci)]
  -- scan 2
  obtain ⟨c₃, k₃, e₃, hk₃, I1, I2, n₃, gr₃, grm₃, go₃⟩ := csScan2_exec (P := P) (nk := nk) (RVb := RVb) (YTb := YTb) (YHb := YHb)
    (NFb := NFb) (TKb := TKb) (LABb := LABb) (IDb := IDb) (K := K) c₂ hw₂
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) a6 a7
    (fun j hj => by rw [fr2 _ (by omega)]; exact hRV j hj)
    (fun j hj => by rw [fr2 _ (by omega)]; exact hTK j hj) (fun j hj => (H2 j hj).2)
    (by rw [n₂ _ (by omega), n₁ _ (by omega), r0]) (by rw [n₂ _ (by omega), n₁ _ (by omega), r1])
    (by rw [n₂ _ (by omega), n₁ _ (by omega), r2]) (by rw [n₂ _ (by omega), n₁ _ (by omega), r3])
    (by rw [n₂ _ (by omega), n₁ _ (by omega), r4]) (by rw [n₂ _ (by omega), n₁ _ (by omega), r7])
    (by rw [n₂ _ (by omega), n₁ _ (by omega), r8]) (by rw [n₂ _ (by omega), n₁ _ (by omega), r9])
    (by rw [n₂ _ (by omega), n₁ _ (by omega), r10])
  have hv : ∀ j < n, c₃.nmem (IDb + j) = clsIdF K (fun j => m₀ (RVb + j))
      (fun j => m₀ (TKb + j)) (fun j => m₀ (YTb + j)) (fun j => m₀ (YHb + j))
      (fun j => m₀ (NFb + j)) (fun j => c₂.nmem (LABb + j)) j := fun j hj => by
    rw [I1 j hj]
    exact csV3_eq (fun a ha => fr2 a (by omega)) (fun j' hj' => fr2 _ (by omega)) a1 a2 a3 hj
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, fun i hi j hj => ?_,
    fun a ha => ?_, fun x hx => ?_, by rw [gr₃, gr₂, gr₁], by rw [grm₃, grm₂, grm₁],
    by rw [go₃, go₂, go₁]⟩
  · rw [hv i hi, hv j hj]
    exact clsIdF_iff hE hlab hC hi hj
  · rw [I2 a (by omega)]
    rcases ha with ha | ha | ha
    · exact fr2 a (Or.inl ha)
    · exact fr2 a (Or.inr ha)
    · rw [H3 a (by omega) (by omega) (by omega), F1 a (by omega) (by omega)]
  · rw [n₃ x (by omega), n₂ x (by omega), n₁ x (by omega)]

end Exec

end BKMNW

end PlanarFlow
