module

public import PlanarFlow.BKMNW.MbDS
public import PlanarFlow.BKMNW.LgWtP

/-!
# Miller's path decoded: the program `mbD`

`mbD` runs after stages A, B of Miller's base (before stage C) and writes the darts of the path
`corePath C` (`MbDS.lean`) as `1 +` global dart indices at `PD = Hb + 6n` (followed by zeros):

* `dA` (set-up; registers `5230 … 5242`, `5265`, `5266`, `tks`'s `5110 … 5114`, `6521 = 1`;
  `s = pdS CY` in `5242`), `pdIdFill` (`ID[i] = i` at `Hb + 7n`), `tks` (`IV[RK[i]] := i` for the
  flagged `i`, at `Hb + 12n`: the inverse of the ranks), `zfill` (`PD` zeroed), `pdInit`
  (`g = 0`, `j = 0`), the loop `pdLoop` (`while g < k`: `PD[j] := IV[pdOut …] + 1`, `j += 1`,
  `g += pdStp`), the body `pdB1 ; pdB2 ; pdB3 ; pdB4` (branch-free);
* **`mbD`**, the block lemmas, **`pdLoop_exec`**, **`mbD_exec`**: within `24 n + 80 k + 80`
  steps, `PD[j] = IV[pdOut CY CR SR IV TK k s (pdG j)] + 1` if `pdG j < k`, else `0` (`j < n`);
  memory outside `[Hb + 6n, Hb + 8n)` and `[Hb + 12n, Hb + 13n)` kept.

Inputs: `5000 = n`, `5004 = Hb`, `641 = k`, `4841 = b`; arrays `NF` at `b`, `TK` at `b + 6n`,
`RK` at `Hb`, `CR` at `Hb + 4n`, `SR` at `Hb + 5n` (the rotation on ranks), `CY` at `Hb + 8n`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The program -/

/-- The bases of `mbD`. -/
def pdA1 : Stmt :=
  block [.copyN 5230 5000, .copyN 5231 641, .constN 5232 1, .constN 5233 2, .constN 5234 3,
    .constN 5265 6, .mulN 5266 5000 5265, .addN 5235 5004 5266,
    .constN 5265 7, .mulN 5266 5000 5265, .addN 5236 5004 5266,
    .constN 5265 12, .mulN 5266 5000 5265, .addN 5237 5004 5266,
    .constN 5265 8, .mulN 5266 5000 5265, .addN 5238 5004 5266]

/-- The other bases, the start `s`, the registers of the scatter and `6521 = 1`. -/
def pdA2 : Stmt :=
  block [.constN 5265 4, .mulN 5266 5000 5265, .addN 5239 5004 5266,
    .constN 5265 5, .mulN 5266 5000 5265, .addN 5240 5004 5266,
    .constN 5265 6, .mulN 5266 5000 5265, .addN 5241 4841 5266,
    .loadN 5242 5238, .modN 5242 5242 5234, .divN 5242 5242 5233,
    .constN 6521 1, .copyN 5110 5000, .copyN 5111 4841, .copyN 5112 5004, .copyN 5113 5236,
    .copyN 5114 5237]

/-- The identity array `ID[i] = i` at `Hb + 7n`. -/
def pdIdFill : Stmt := MfDrv.mapRunS (block [.copyN 6523 6520]) 5230 5236

/-- The start of the loop: `g = 0`, `j = 0`. -/
def pdInit : Stmt := block [.constN 5243 0, .constN 5244 0]

/-- The code at `g`, its `up` flag (`5249`) and the rank of its dart (`5252`). -/
def pdB1 : Stmt :=
  block [.addN 5245 5242 5243, .modN 5245 5245 5231, .addN 5245 5238 5245, .loadN 5246 5245,
    .modN 5247 5246 5234, .divN 5248 5246 5234,
    .subN 5250 5247 5232, .subN 5251 5232 5247, .addN 5250 5250 5251, .subN 5249 5232 5250,
    .addN 5251 5239 5248, .loadN 5251 5251, .addN 5251 5240 5251, .loadN 5251 5251,
    .mulN 5252 5249 5251, .subN 5250 5232 5249, .mulN 5250 5250 5248, .addN 5252 5252 5250]

/-- The rank of the dart of the code at `g + 1` (`5257`). -/
def pdB2 : Stmt :=
  block [.addN 5245 5242 5243, .addN 5245 5245 5232, .modN 5245 5245 5231,
    .addN 5245 5238 5245, .loadN 5253 5245,
    .modN 5254 5253 5234, .divN 5255 5253 5234,
    .subN 5250 5254 5232, .subN 5251 5232 5254, .addN 5250 5250 5251, .subN 5256 5232 5250,
    .addN 5251 5239 5255, .loadN 5251 5251, .addN 5251 5240 5251, .loadN 5251 5251,
    .mulN 5257 5256 5251, .subN 5250 5232 5256, .mulN 5250 5250 5255, .addN 5257 5257 5250]

/-- The comparison of the vertices and the selection (`5262 = pdOut …`). -/
def pdB3 : Stmt :=
  block [.addN 5258 5239 5252, .loadN 5258 5258, .addN 5258 5240 5258, .loadN 5258 5258,
    .addN 5258 5237 5258, .loadN 5258 5258, .addN 5258 5241 5258, .loadN 5258 5258,
    .addN 5259 5237 5257, .loadN 5259 5259, .addN 5259 5241 5259, .loadN 5259 5259,
    .subN 5260 5258 5259, .subN 5261 5259 5258, .addN 5260 5260 5261, .divN 5260 5260 5260,
    .subN 5260 5232 5260,
    .addN 5261 5239 5257, .loadN 5261 5261,
    .mulN 5262 5260 5252, .subN 5263 5232 5260, .mulN 5263 5263 5261, .addN 5262 5262 5263,
    .addN 5263 5243 5233, .subN 5263 5231 5263, .divN 5263 5263 5263, .mulN 5263 5249 5263,
    .mulN 5262 5263 5262, .subN 5264 5232 5263, .mulN 5264 5264 5252, .addN 5262 5262 5264]

/-- The write `PD[j] := IV[out] + 1` and the advance. -/
def pdB4 : Stmt :=
  block [.addN 5262 5237 5262, .loadN 5262 5262, .addN 5262 5262 5232,
    .addN 5264 5235 5244, .storeN 5264 5262,
    .addN 5244 5244 5232, .addN 5243 5243 5232, .addN 5243 5243 5249]

/-- The body of the loop. -/
def pdBody : Stmt := .seq pdB1 (.seq pdB2 (.seq pdB3 pdB4))

/-- **The decoding loop.** -/
def pdLoop : Stmt := .seq pdInit (.whileLtN 5243 5231 pdBody)

/-- **Miller's path decoded** (between stages B and C of the base). -/
def mbD : Stmt := .seq pdA1 (.seq pdA2 (.seq pdIdFill (.seq tks (.seq (MfDrv.zfill 5230 5235) pdLoop))))

section Exec

variable {P : Input} {W : ℕ}

lemma fmul_le {f x W : ℕ} (hf : f ≤ 1) (hx : x ≤ W) : f * x ≤ W := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hf with rfl | rfl <;> simp <;> omega

theorem pdA1_exec (c : Config) (hc : WordsBounded W c) {n Hb k : ℕ}
    (r00 : c.nreg 5000 = n) (r04 : c.nreg 5004 = Hb) (r641 : c.nreg 641 = k)
    (w : Hb + 12 * n ≤ W ∧ 12 ≤ W) :
    ∃ c' t, Exec P W pdA1 c c' t ∧ t = 17 ∧ c'.nreg 5230 = n ∧ c'.nreg 5231 = k ∧
      c'.nreg 5232 = 1 ∧ c'.nreg 5233 = 2 ∧ c'.nreg 5234 = 3 ∧ c'.nreg 5235 = Hb + 6 * n ∧
      c'.nreg 5236 = Hb + 7 * n ∧ c'.nreg 5237 = Hb + 12 * n ∧ c'.nreg 5238 = Hb + 8 * n ∧
      c'.nmem = c.nmem ∧ (∀ x, (x < 5230 ∨ (5238 < x ∧ x < 5265) ∨ 5266 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨w1, w2⟩ := w
  have h6 : n * 6 = 6 * n := by ring
  have h7 : n * 7 = 7 * n := by ring
  have h8 : n * 8 = 8 * n := by ring
  have h12 : n * 12 = 12 * n := by ring
  unfold pdA1
  exec_block
  all_goals try (config_simp; (try simp only [r00, r04, r641, h6, h7, h8, h12]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r00, r04, r641, h6, h7, h8, h12]); done)
  all_goals try (config_simp; (try simp only [r00, r04, r641, h6, h7, h8, h12]); omega)
  · config_simp; simp (disch := omega) only [upd_other]

theorem pdA2_exec (c : Config) (hc : WordsBounded W c) {n Hb b : ℕ}
    (r00 : c.nreg 5000 = n) (r04 : c.nreg 5004 = Hb) (r41 : c.nreg 4841 = b)
    (r33 : c.nreg 5233 = 2) (r34 : c.nreg 5234 = 3) (r36 : c.nreg 5236 = Hb + 7 * n)
    (r37 : c.nreg 5237 = Hb + 12 * n) (r38 : c.nreg 5238 = Hb + 8 * n)
    (w : Hb + 5 * n ≤ W ∧ b + 6 * n ≤ W ∧ 6 ≤ W) :
    ∃ c' t, Exec P W pdA2 c c' t ∧ t = 18 ∧ c'.nreg 5239 = Hb + 4 * n ∧
      c'.nreg 5240 = Hb + 5 * n ∧ c'.nreg 5241 = b + 6 * n ∧
      c'.nreg 5242 = c.nmem (Hb + 8 * n) % 3 / 2 ∧ c'.nreg 6521 = 1 ∧
      c'.nreg 5110 = n ∧ c'.nreg 5111 = b ∧ c'.nreg 5112 = Hb ∧ c'.nreg 5113 = Hb + 7 * n ∧
      c'.nreg 5114 = Hb + 12 * n ∧
      c'.nmem = c.nmem ∧ (∀ x, (x < 5110 ∨ (5114 < x ∧ x < 5239) ∨ (5242 < x ∧ x < 5265) ∨
        (5266 < x ∧ x < 6521) ∨ 6521 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨w1, w2, w3⟩ := w
  have h4 : n * 4 = 4 * n := by ring
  have h5 : n * 5 = 5 * n := by ring
  have h6 : n * 6 = 6 * n := by ring
  unfold pdA2
  exec_block
  all_goals try (config_simp; (try simp only [r00, r04, r41, h4, h5, h6]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r00, r04, r41, r33, r34, r36, r37, r38, h4, h5, h6]); done)
  all_goals try (config_simp; (try simp only [r00, r04, r41, r33, r34, r36, r37, r38, h4, h5, h6]); omega)
  · config_simp; simp (disch := omega) only [upd_other]

theorem pdInit_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W pdInit c c' t ∧ t = 2 ∧ c'.nreg 5243 = 0 ∧ c'.nreg 5244 = 0 ∧
      c'.nmem = c.nmem ∧ (∀ x, x ≠ 5243 → x ≠ 5244 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pdInit
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, rfl, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  config_simp; simp (disch := omega) only [upd_other]

theorem pdB1_exec (c : Config) (hc : WordsBounded W c) {s g k CYb CRb SRb v x1 x2 : ℕ}
    (r31 : c.nreg 5231 = k) (r32 : c.nreg 5232 = 1) (r34 : c.nreg 5234 = 3)
    (r38 : c.nreg 5238 = CYb) (r39 : c.nreg 5239 = CRb) (r40 : c.nreg 5240 = SRb)
    (r42 : c.nreg 5242 = s) (r43 : c.nreg 5243 = g)
    (hv : c.nmem (CYb + (s + g) % k) = v) (h1 : c.nmem (CRb + v / 3) = x1)
    (h2 : c.nmem (SRb + x1) = x2)
    (w1 : s + g ≤ W) (w2 : CYb + (s + g) % k ≤ W) (w3 : CRb + v / 3 ≤ W) (w4 : SRb + x1 ≤ W)
    (w5 : 3 ≤ W) :
    ∃ c' t, Exec P W pdB1 c c' t ∧ t = 18 ∧ c'.nreg 5249 = pdUp v ∧
      c'.nreg 5252 = pdDec (fun q => c.nmem (CRb + q)) (fun q => c.nmem (SRb + q)) v ∧
      (∀ x, (x < 5245 ∨ 5252 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have bv : v ≤ W := hv ▸ hc.2 _
  have bx2 : x2 ≤ W := h2 ▸ hc.2 _
  have hu : pdUp v ≤ 1 := pdUp_le v
  have m1 : pdUp v * x2 ≤ W := fmul_le hu bx2
  have m2 : (1 - pdUp v) * (v / 3) ≤ W := fmul_le (by omega) (by omega)
  have m3 : pdSel (pdUp v) x2 (v / 3) ≤ W := pdSel_le hu bx2 (by omega)
  unfold pdSel at m3
  unfold pdUp at hu m1 m2 m3
  have hdec : pdDec (fun q => c.nmem (CRb + q)) (fun q => c.nmem (SRb + q)) v =
      pdSel (pdUp v) x2 (v / 3) := by unfold pdDec; simp only [h1, h2]
  rw [hdec]
  unfold pdB1
  exec_block
  all_goals try (config_simp; (try simp only [r31, r32, r34, r38, r39, r40, r42, r43, hv, h1, h2]); omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r31, r32, r34, r38, r39, r40, r42, r43, hv, h1, h2, pdSel, pdUp]); done)
  · config_simp; simp (disch := omega) only [upd_other]

theorem pdB2_exec (c : Config) (hc : WordsBounded W c) {s g k CYb CRb SRb v x1 x2 : ℕ}
    (r31 : c.nreg 5231 = k) (r32 : c.nreg 5232 = 1) (r34 : c.nreg 5234 = 3)
    (r38 : c.nreg 5238 = CYb) (r39 : c.nreg 5239 = CRb) (r40 : c.nreg 5240 = SRb)
    (r42 : c.nreg 5242 = s) (r43 : c.nreg 5243 = g)
    (hv : c.nmem (CYb + (s + g + 1) % k) = v) (h1 : c.nmem (CRb + v / 3) = x1)
    (h2 : c.nmem (SRb + x1) = x2)
    (w1 : s + g + 1 ≤ W) (w2 : CYb + (s + g + 1) % k ≤ W) (w3 : CRb + v / 3 ≤ W)
    (w4 : SRb + x1 ≤ W) (w5 : 3 ≤ W) :
    ∃ c' t, Exec P W pdB2 c c' t ∧ t = 19 ∧
      c'.nreg 5257 = pdDec (fun q => c.nmem (CRb + q)) (fun q => c.nmem (SRb + q)) v ∧
      (∀ x, (x < 5245 ∨ (5245 < x ∧ x < 5250) ∨ x = 5252 ∨ 5257 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have bv : v ≤ W := hv ▸ hc.2 _
  have bx2 : x2 ≤ W := h2 ▸ hc.2 _
  have hu : pdUp v ≤ 1 := pdUp_le v
  have m1 : pdUp v * x2 ≤ W := fmul_le hu bx2
  have m2 : (1 - pdUp v) * (v / 3) ≤ W := fmul_le (by omega) (by omega)
  have m3 : pdSel (pdUp v) x2 (v / 3) ≤ W := pdSel_le hu bx2 (by omega)
  unfold pdSel at m3
  unfold pdUp at hu m1 m2 m3
  have hdec : pdDec (fun q => c.nmem (CRb + q)) (fun q => c.nmem (SRb + q)) v =
      pdSel (pdUp v) x2 (v / 3) := by unfold pdDec; simp only [h1, h2]
  rw [hdec]
  unfold pdB2
  exec_block
  all_goals try (config_simp; (try simp only [r31, r32, r34, r38, r39, r40, r42, r43, hv, h1, h2]); omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r31, r32, r34, r38, r39, r40, r42, r43, hv, h1, h2, pdSel, pdUp]); done)
  · config_simp; simp (disch := omega) only [upd_other]

theorem pdB3_exec (c : Config) (hc : WordsBounded W c)
    {g k up u w CRb SRb IVb TKb a1 a2 a3 ka b1 kw crw : ℕ}
    (r31 : c.nreg 5231 = k) (r32 : c.nreg 5232 = 1) (r33 : c.nreg 5233 = 2)
    (r37 : c.nreg 5237 = IVb) (r39 : c.nreg 5239 = CRb) (r40 : c.nreg 5240 = SRb)
    (r41 : c.nreg 5241 = TKb) (r43 : c.nreg 5243 = g) (r49 : c.nreg 5249 = up)
    (r52 : c.nreg 5252 = u) (r57 : c.nreg 5257 = w)
    (hA1 : c.nmem (CRb + u) = a1) (hA2 : c.nmem (SRb + a1) = a2) (hA3 : c.nmem (IVb + a2) = a3)
    (hA4 : c.nmem (TKb + a3) = ka) (hB1 : c.nmem (IVb + w) = b1) (hB2 : c.nmem (TKb + b1) = kw)
    (hC : c.nmem (CRb + w) = crw) (hup : up ≤ 1)
    (w1 : CRb + u ≤ W) (w2 : SRb + a1 ≤ W) (w3 : IVb + a2 ≤ W) (w4 : TKb + a3 ≤ W)
    (w5 : IVb + w ≤ W) (w6 : TKb + b1 ≤ W) (w7 : CRb + w ≤ W) (w8 : g + 2 ≤ W) :
    ∃ c' t, Exec P W pdB3 c c' t ∧ t = 31 ∧
      c'.nreg 5262 = pdSel (up * pdLt g k) (pdSel (pdEq ka kw) u crw) u ∧
      (∀ x, (x < 5258 ∨ 5264 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have bu : u ≤ W := r52 ▸ hc.1 _
  have bka : ka ≤ W := hA4 ▸ hc.2 _
  have bkw : kw ≤ W := hB2 ▸ hc.2 _
  have bcrw : crw ≤ W := hC ▸ hc.2 _
  have he : pdEq ka kw ≤ 1 := pdEq_le ka kw
  have hl : pdLt g k ≤ 1 := pdLt_le g k
  have hcn : up * pdLt g k ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hup with rfl | rfl <;> simp <;> omega
  have m1 : pdEq ka kw * u ≤ W := fmul_le he bu
  have m2 : (1 - pdEq ka kw) * crw ≤ W := fmul_le (by omega) bcrw
  have m3 : pdSel (pdEq ka kw) u crw ≤ W := pdSel_le he bu bcrw
  have m4 : up * pdLt g k ≤ W := by omega
  have m5 : up * pdLt g k * pdSel (pdEq ka kw) u crw ≤ W := fmul_le hcn m3
  have m6 : (1 - up * pdLt g k) * u ≤ W := fmul_le (by omega) bu
  have m7 : pdSel (up * pdLt g k) (pdSel (pdEq ka kw) u crw) u ≤ W := pdSel_le hcn m3 bu
  have m0 : (ka - kw) + (kw - ka) ≤ W := by omega
  unfold pdSel at m3 m5 m7
  unfold pdEq at he m1 m2 m3 m5 m7
  unfold pdLt at hl hcn m4 m5 m6 m7
  unfold pdB3
  exec_block
  all_goals try (config_simp; (try simp only [r31, r32, r33, r37, r39, r40, r41, r43, r49, r52, r57, hA1, hA2, hA3, hA4, hB1, hB2, hC]); omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r31, r32, r33, r37, r39, r40, r41, r43, r49, r52, r57, hA1, hA2, hA3, hA4, hB1, hB2, hC, pdSel, pdEq, pdLt]); done)
  · config_simp; simp (disch := omega) only [upd_other]

theorem pdB4_exec (c : Config) (hc : WordsBounded W c) {PDb IVb g j up out o : ℕ}
    (r32 : c.nreg 5232 = 1) (r35 : c.nreg 5235 = PDb) (r37 : c.nreg 5237 = IVb)
    (r43 : c.nreg 5243 = g) (r44 : c.nreg 5244 = j) (r49 : c.nreg 5249 = up)
    (r62 : c.nreg 5262 = out) (hO : c.nmem (IVb + out) = o)
    (w1 : IVb + out ≤ W) (w2 : o + 1 ≤ W) (w3 : PDb + j ≤ W) (w4 : j + 1 ≤ W)
    (w5 : g + 1 + up ≤ W) :
    ∃ c' t, Exec P W pdB4 c c' t ∧ t = 8 ∧ c'.nreg 5243 = g + 1 + up ∧ c'.nreg 5244 = j + 1 ∧
      c'.nmem = upd c.nmem (PDb + j) (o + 1) ∧
      (∀ x, (x < 5243 ∨ (5244 < x ∧ x < 5262) ∨ x = 5263 ∨ 5264 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pdB4
  exec_block
  all_goals try (config_simp; (try simp only [r32, r35, r37, r43, r44, r49, r62, hO]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r32, r35, r37, r43, r44, r49, r62, hO]); done)
  · config_simp; simp (disch := omega) only [upd_other]

lemma pdSel_lt {f x y B : ℕ} (hf : f ≤ 1) (hx : x < B) (hy : y < B) : pdSel f x y < B := by
  rw [pdSel_eq hf]; split_ifs <;> assumption

lemma pdDec_lt {cr sr : ℕ → ℕ} {mN v : ℕ} (hv : v < 3 * mN) (hcr : ∀ q < mN, cr q < mN)
    (hsr : ∀ q < mN, sr q < mN) : pdDec cr sr v < mN := by
  rw [pdDec_eq]; split_ifs
  · exact hsr _ (hcr _ (by omega))
  · omega

set_option maxHeartbeats 800000 in
/-- **One step of the decoding loop.** -/
theorem pdBody_exec (c : Config) (hc : WordsBounded W c)
    {n mN k s g j PDb IVb CYb CRb SRb TKb : ℕ} {cy cr sr iv tk : ℕ → ℕ}
    (r31 : c.nreg 5231 = k) (r32 : c.nreg 5232 = 1) (r33 : c.nreg 5233 = 2)
    (r34 : c.nreg 5234 = 3) (r35 : c.nreg 5235 = PDb) (r37 : c.nreg 5237 = IVb)
    (r38 : c.nreg 5238 = CYb) (r39 : c.nreg 5239 = CRb) (r40 : c.nreg 5240 = SRb)
    (r41 : c.nreg 5241 = TKb) (r42 : c.nreg 5242 = s) (r43 : c.nreg 5243 = g)
    (r44 : c.nreg 5244 = j) (hgk : g < k) (hs : s ≤ 1)
    (hcy : ∀ l < k, c.nmem (CYb + l) = cy l) (hcr : ∀ q < mN, c.nmem (CRb + q) = cr q)
    (hsr : ∀ q < mN, c.nmem (SRb + q) = sr q) (hiv : ∀ q < mN, c.nmem (IVb + q) = iv q)
    (htk : ∀ i < n, c.nmem (TKb + i) = tk i)
    (hCY : ∀ l < k, cy l < 3 * mN) (hCR : ∀ q < mN, cr q < mN) (hSR : ∀ q < mN, sr q < mN)
    (hIV : ∀ q < mN, iv q < n)
    (lay : CYb + k ≤ W ∧ CRb + mN ≤ W ∧ SRb + mN ≤ W ∧ IVb + mN ≤ W ∧ TKb + n ≤ W ∧
      PDb + j ≤ W ∧ k + 2 ≤ W ∧ j + 1 ≤ W ∧ n + 1 ≤ W ∧ 3 ≤ W) :
    ∃ c' t, Exec P W pdBody c c' t ∧ t = 76 ∧
      c'.nreg 5243 = g + pdStp cy k s g ∧ c'.nreg 5244 = j + 1 ∧
      c'.nmem = upd c.nmem (PDb + j) (iv (pdOut cy cr sr iv tk k s g) + 1) ∧
      (∀ x, (x < 5243 ∨ 5264 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lay
  have hk0 : 0 < k := by omega
  -- the first code
  have hp0 : (s + g) % k < k := Nat.mod_lt _ hk0
  have hp1 : (s + g + 1) % k < k := Nat.mod_lt _ hk0
  set v := cy ((s + g) % k) with hvdef
  have hv3 : v < 3 * mN := hCY _ hp0
  have hq : v / 3 < mN := by omega
  have hx1 := hCR _ hq
  obtain ⟨c₁, t₁, e₁, ht₁, u49, u52, un₁, um₁, ur₁, urm₁, uo₁⟩ :=
    pdB1_exec (P := P) c hc (x1 := cr (v / 3)) (x2 := sr (cr (v / 3))) r31 r32 r34 r38 r39 r40
      r42 r43 (hcy _ hp0) (hcr _ hq) (hsr _ hx1) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  have hw₁ := e₁.wb_right
  have hu : pdDec (fun q => c.nmem (CRb + q)) (fun q => c.nmem (SRb + q)) v = pdDec cr sr v := by
    simp only [pdDec, hcr _ hq, hsr _ hx1]
  rw [hu] at u52
  set u := pdDec cr sr v with hudef
  have huN : u < mN := pdDec_lt hv3 hCR hSR
  -- the second code
  set v' := cy ((s + g + 1) % k) with hv'def
  have hv3' : v' < 3 * mN := hCY _ hp1
  have hq' : v' / 3 < mN := by omega
  have hx1' := hCR _ hq'
  have k1 : ∀ x, (x < 5245 ∨ 5252 < x) → c₁.nreg x = c.nreg x := un₁
  obtain ⟨c₂, t₂, e₂, ht₂, v57, vn₂, vm₂, vr₂, vrm₂, vo₂⟩ :=
    pdB2_exec (P := P) c₁ hw₁ (v := v') (x1 := cr (v' / 3)) (x2 := sr (cr (v' / 3)))
      (by rw [k1 _ (by omega), r31]) (by rw [k1 _ (by omega), r32]) (by rw [k1 _ (by omega), r34])
      (by rw [k1 _ (by omega), r38]) (by rw [k1 _ (by omega), r39]) (by rw [k1 _ (by omega), r40])
      (by rw [k1 _ (by omega), r42]) (by rw [k1 _ (by omega), r43]) (by rw [um₁]; exact hcy _ hp1)
      (by rw [um₁]; exact hcr _ hq') (by rw [um₁]; exact hsr _ hx1') (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hw₂ := e₂.wb_right
  have hw : pdDec (fun q => c₁.nmem (CRb + q)) (fun q => c₁.nmem (SRb + q)) v' =
      pdDec cr sr v' := by
    simp only [pdDec, um₁, hcr _ hq', hsr _ hx1']
  rw [hw] at v57
  set w := pdDec cr sr v' with hwdef
  have hwN : w < mN := pdDec_lt hv3' hCR hSR
  -- the comparison
  have k2 : ∀ x, (x < 5245 ∨ 5252 < x) → (x < 5245 ∨ (5245 < x ∧ x < 5250) ∨ x = 5252 ∨ 5257 < x) →
      c₂.nreg x = c.nreg x := fun x h1 h2 => by rw [vn₂ x h2, k1 x h1]
  have m2 : c₂.nmem = c.nmem := by rw [vm₂, um₁]
  have ha1 := hCR _ huN
  have ha2 := hSR _ ha1
  have ha3 := hIV _ ha2
  have hb1 := hIV _ hwN
  have hcw := hCR _ hwN
  obtain ⟨c₃, t₃, e₃, ht₃, x62, xn₃, xm₃, xr₃, xrm₃, xo₃⟩ :=
    pdB3_exec (P := P) c₂ hw₂ (g := g) (k := k) (up := pdUp v) (u := u) (w := w)
      (a1 := cr u) (a2 := sr (cr u)) (a3 := iv (sr (cr u))) (ka := tk (iv (sr (cr u))))
      (b1 := iv w) (kw := tk (iv w)) (crw := cr w)
      (by rw [k2 _ (by omega) (by omega), r31]) (by rw [k2 _ (by omega) (by omega), r32])
      (by rw [k2 _ (by omega) (by omega), r33]) (by rw [k2 _ (by omega) (by omega), r37])
      (by rw [k2 _ (by omega) (by omega), r39]) (by rw [k2 _ (by omega) (by omega), r40])
      (by rw [k2 _ (by omega) (by omega), r41]) (by rw [k2 _ (by omega) (by omega), r43])
      (by rw [vn₂ _ (by omega), u49]) (by rw [vn₂ _ (by omega), u52]) v57
      (by rw [m2]; exact hcr _ huN) (by rw [m2]; exact hsr _ ha1) (by rw [m2]; exact hiv _ ha2)
      (by rw [m2]; exact htk _ ha3) (by rw [m2]; exact hiv _ hwN) (by rw [m2]; exact htk _ hb1)
      (by rw [m2]; exact hcr _ hwN) (pdUp_le v) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  have hw₃ := e₃.wb_right
  have hout : pdSel (pdUp v * pdLt g k) (pdSel (pdEq (tk (iv (sr (cr u)))) (tk (iv w))) u (cr w)) u =
      pdOut cy cr sr iv tk k s g := rfl
  rw [hout] at x62
  have hoN : pdOut cy cr sr iv tk k s g < mN := by
    rw [← hout]
    have hcn : pdUp v * pdLt g k ≤ 1 := by
      have := pdLt_le g k
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (pdUp_le v) with h | h <;> rw [h] <;> omega
    exact pdSel_lt hcn (pdSel_lt (pdEq_le _ _) huN (hCR _ hwN)) huN
  have hoI := hIV _ hoN
  -- the write
  have k3 : ∀ x, (x < 5245 ∨ 5252 < x) → (x < 5245 ∨ (5245 < x ∧ x < 5250) ∨ x = 5252 ∨ 5257 < x) →
      (x < 5258 ∨ 5264 < x) → c₃.nreg x = c.nreg x := fun x h1 h2 h3 => by
    rw [xn₃ x h3, k2 x h1 h2]
  have hupv : pdUp v ≤ 1 := pdUp_le v
  obtain ⟨c₄, t₄, e₄, ht₄, y43, y44, ym₄, yn₄, yr₄, yrm₄, yo₄⟩ :=
    pdB4_exec (P := P) c₃ hw₃ (PDb := PDb) (IVb := IVb) (g := g) (j := j) (up := pdUp v)
      (out := pdOut cy cr sr iv tk k s g) (o := iv (pdOut cy cr sr iv tk k s g))
      (by rw [k3 _ (by omega) (by omega) (by omega), r32])
      (by rw [k3 _ (by omega) (by omega) (by omega), r35])
      (by rw [k3 _ (by omega) (by omega) (by omega), r37])
      (by rw [k3 _ (by omega) (by omega) (by omega), r43])
      (by rw [k3 _ (by omega) (by omega) (by omega), r44])
      (by rw [xn₃ _ (by omega), vn₂ _ (by omega), u49]) x62
      (by rw [xm₃, m2]; exact hiv _ hoN) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, ?_, y44, ?_,
    fun x hx => ?_, by rw [yr₄, xr₃, vr₂, ur₁], by rw [yrm₄, xrm₃, vrm₂, urm₁],
    by rw [yo₄, xo₃, vo₂, uo₁]⟩
  · rw [y43]; show g + 1 + pdUp v = g + (1 + pdUp v); omega
  · rw [ym₄, xm₃, m2]
  · rw [yn₄ x (by omega), k3 x (by omega) (by omega) (by omega)]

set_option maxHeartbeats 800000 in
/-- **The decoding loop**: `PD[j] = IV[pdOut … (pdG j)] + 1` while `pdG j < k`, then `0`. -/
theorem pdLoop_exec (c : Config) (hc : WordsBounded W c)
    {n mN k s PDb IVb CYb CRb SRb TKb : ℕ} {cy cr sr iv tk : ℕ → ℕ}
    (r31 : c.nreg 5231 = k) (r32 : c.nreg 5232 = 1) (r33 : c.nreg 5233 = 2)
    (r34 : c.nreg 5234 = 3) (r35 : c.nreg 5235 = PDb) (r37 : c.nreg 5237 = IVb)
    (r38 : c.nreg 5238 = CYb) (r39 : c.nreg 5239 = CRb) (r40 : c.nreg 5240 = SRb)
    (r41 : c.nreg 5241 = TKb) (r42 : c.nreg 5242 = s) (hs : s ≤ 1)
    (hcy : ∀ l < k, c.nmem (CYb + l) = cy l) (hcr : ∀ q < mN, c.nmem (CRb + q) = cr q)
    (hsr : ∀ q < mN, c.nmem (SRb + q) = sr q) (hiv : ∀ q < mN, c.nmem (IVb + q) = iv q)
    (htk : ∀ i < n, c.nmem (TKb + i) = tk i)
    (hCY : ∀ l < k, cy l < 3 * mN) (hCR : ∀ q < mN, cr q < mN) (hSR : ∀ q < mN, sr q < mN)
    (hIV : ∀ q < mN, iv q < n) (hJ : ∀ j, pdG cy k s j < k → j < n)
    (hPD : ∀ j < n, c.nmem (PDb + j) = 0)
    (lay : TKb + n ≤ PDb ∧ CRb + mN ≤ PDb ∧ SRb + mN ≤ PDb ∧ PDb + n ≤ CYb ∧ PDb + n ≤ IVb ∧
      CYb + k ≤ W ∧ IVb + mN ≤ W ∧ k + 2 ≤ W ∧ n + 1 ≤ W ∧ 3 ≤ W) :
    ∃ c' t, Exec P W pdLoop c c' t ∧ t ≤ 78 * k + 4 ∧
      (∀ j < n, c'.nmem (PDb + j) = if pdG cy k s j < k then
        iv (pdOut cy cr sr iv tk k s (pdG cy k s j)) + 1 else 0) ∧
      (∀ a, ¬ (PDb ≤ a ∧ a < PDb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5243 ∨ 5264 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lay
  obtain ⟨c₁, t₁, e₁, ht₁, g43, g44, gm₁, gn₁, gr₁, grm₁, go₁⟩ := pdInit_exec (P := P) c hc
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 5243 ∨ 5264 < x) → c₁.nreg x = c.nreg x := fun x hx =>
    gn₁ x (by omega) (by omega)
  let I : Config → Prop := fun c' => WordsBounded W c' ∧ ∃ j, c'.nreg 5243 = pdG cy k s j ∧
    c'.nreg 5244 = j ∧ (∀ j' < j, pdG cy k s j' < k) ∧
    (∀ x, (x < 5243 ∨ 5264 < x) → c'.nreg x = c.nreg x) ∧
    (∀ j' < n, c'.nmem (PDb + j') = if j' < j then
      iv (pdOut cy cr sr iv tk k s (pdG cy k s j')) + 1 else 0) ∧
    (∀ a, ¬ (PDb ≤ a ∧ a < PDb + n) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have hI₁ : I c₁ := ⟨hw₁, 0, g43, g44, fun j' h => absurd h (by omega), q,
    fun j' hj' => by rw [gm₁, hPD j' hj']; simp, fun a _ => by rw [gm₁], gr₁, grm₁, go₁⟩
  obtain ⟨c₂, t₂, e₂, hI₂, hex, ht₂⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 5243)
    (b := 5231) (body := pdBody) I (fun c' => 78 * (k - c'.nreg 5243))
    (fun c' h => h.1) (fun c' hI hlt => by
      obtain ⟨hw, j, p43, p44, plt, pr, pPD, pm, prr, prm, po⟩ := hI
      have r31' : c'.nreg 5231 = k := by rw [pr _ (by omega), r31]
      rw [p43, r31'] at hlt
      have hjn : j < n := hJ j hlt
      have rd : ∀ a, ¬ (PDb ≤ a ∧ a < PDb + n) → c'.nmem a = c.nmem a := pm
      obtain ⟨c'', t, e, ht, s43, s44, sm, sn, srr, srm, so⟩ := pdBody_exec (P := P) c' hw
        (n := n) (mN := mN) (g := pdG cy k s j) (j := j) (cy := cy) (cr := cr) (sr := sr)
        (iv := iv) (tk := tk) r31'
        (by rw [pr _ (by omega), r32]) (by rw [pr _ (by omega), r33])
        (by rw [pr _ (by omega), r34]) (by rw [pr _ (by omega), r35])
        (by rw [pr _ (by omega), r37]) (by rw [pr _ (by omega), r38])
        (by rw [pr _ (by omega), r39]) (by rw [pr _ (by omega), r40])
        (by rw [pr _ (by omega), r41]) (by rw [pr _ (by omega), r42]) p43 p44 hlt hs
        (fun l hl => by rw [rd _ (by omega)]; exact hcy l hl)
        (fun q hq => by rw [rd _ (by omega)]; exact hcr q hq)
        (fun q hq => by rw [rd _ (by omega)]; exact hsr q hq)
        (fun q hq => by rw [rd _ (by omega)]; exact hiv q hq)
        (fun i hi => by rw [rd _ (by omega)]; exact htk i hi) hCY hCR hSR hIV
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
          by omega, by omega⟩
      have hstp : pdG cy k s j + pdStp cy k s (pdG cy k s j) = pdG cy k s (j + 1) := rfl
      have hge := pdG_lt_succ cy k s j
      refine ⟨c'', t, e, ⟨e.wb_right, j + 1, by rw [s43, hstp], s44, fun j' hj' => ?_,
        fun x hx => by rw [sn x hx, pr x hx], fun j' hj' => ?_, fun a ha => ?_, by rw [srr, prr],
        by rw [srm, prm], by rw [so, po]⟩, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h | rfl
        · exact plt j' h
        · exact hlt
      · rw [sm]
        rcases Nat.lt_trichotomy j' j with h | rfl | h
        · rw [upd_other _ _ _ (by omega), pPD j' hj', iteT h, iteT (by omega)]
        · rw [upd_same, iteT (by omega)]
        · rw [upd_other _ _ _ (by omega), pPD j' hj', iteF (by omega), iteF (by omega)]
      · rw [sm, upd_other _ _ _ (by omega)]; exact rd a ha
      · rw [s43, hstp, p43]
        have : pdG cy k s (j + 1) ≤ k ∨ k < pdG cy k s (j + 1) := le_or_gt _ _
        omega) hI₁
  obtain ⟨hw₂, j, p43, p44, plt, pr, pPD, pm, prr, prm, po⟩ := hI₂
  have r31' : c₂.nreg 5231 = k := by rw [pr _ (by omega), r31]
  rw [p43, r31'] at hex
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, ?_, fun j' hj' => ?_, pm, pr, prr, prm, po⟩
  · have : 78 * (k - c₁.nreg 5243) ≤ 78 * k := by omega
    omega
  · rw [pPD j' hj']
    by_cases h : j' < j
    · rw [iteT h, iteT (plt j' h)]
    · have hmono := pdG_mono cy k s (show j ≤ j' by omega)
      rw [iteF h, iteF (by omega)]

theorem pdIdFill_exec (c : Config) (hc : WordsBounded W c) {n IDb : ℕ}
    (r30 : c.nreg 5230 = n) (r21 : c.nreg 6521 = 1) (r36 : c.nreg 5236 = IDb)
    (w1 : IDb + n ≤ W) (w2 : n + 1 ≤ W) :
    ∃ c' t, Exec P W pdIdFill c c' t ∧ t ≤ 6 * n + 3 ∧
      (∀ j < n, c'.nmem (IDb + j) = j) ∧
      (∀ a, ¬ (IDb ≤ a ∧ a < IDb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ MfDrv.vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, f1, m1, n1, rr1, rm1, o1⟩ := MfDrv.mapRun_exec (P := P) c hc
    (vb := block [.copyN 6523 6520]) (bnd := 5230) (ob := 5236) (m := n) (Ob := IDb) (B := 1)
    (fun i => i) r30 r21 r36 w1 w2 (by unfold MfDrv.vscr; omega) (by unfold MfDrv.vscr; omega)
    (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ : ∃ c'' k',
          Exec P W (block [.copyN 6523 6520]) c' c'' k' ∧ k' = 1 ∧ c''.nreg 6523 = i ∧
          (∀ x, x ≠ 6523 → c''.nreg x = c'.nreg x) ∧ c''.nmem = c'.nmem ∧
          c''.rreg = c'.rreg ∧ c''.rmem = c'.rmem ∧ c''.output = c'.output := by
        exec_block
        refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; exact h20
        · config_simp; simp (disch := omega) only [upd_other]
      exact ⟨c'', k', e', by omega, v, fun x hx => nn x (by unfold MfDrv.vscr at hx; omega), mm,
        rr, rm, oo⟩)
  exact ⟨c₁, t₁, e₁, by omega, f1, m1, n1, rr1, rm1, o1⟩

set_option maxHeartbeats 1600000 in
/-- **Miller's path decoded on the machine**: within `24 n + 78 k + 50` steps, with `IV` the
inverse of the ranks (`IV[RK[i]] = i` for the flagged `i`), `PD[j] = IV[pdOut CY CR SR IV TK k s
(pdG j)] + 1` while `pdG j < k` and `0` after (`j < n`, `s = pdS CY`); memory outside
`[Hb + 6n, Hb + 8n)` and `[Hb + 12n, Hb + 13n)` kept; registers outside `5110 … 5120`,
`5230 … 5266`, `6520 … 6529` kept. -/
theorem mbD_exec (c : Config) (hc : WordsBounded W c) {n b Hb k mN : ℕ}
    (r00 : c.nreg 5000 = n) (r04 : c.nreg 5004 = Hb) (r641 : c.nreg 641 = k)
    (r41 : c.nreg 4841 = b)
    (lay : b + 7 * n ≤ Hb ∧ Hb + 13 * n ≤ W ∧ 0 < k ∧ k ≤ 3 * n ∧ mN ≤ n ∧ 13 ≤ W)
    (hRK : ∀ i < n, c.nmem (b + i) ≠ 0 → c.nmem (Hb + i) < mN)
    (hinj : ∀ i < n, ∀ j < n, c.nmem (b + i) ≠ 0 → c.nmem (b + j) ≠ 0 →
      c.nmem (Hb + i) = c.nmem (Hb + j) → i = j)
    (hsurj : ∀ q < mN, ∃ i < n, c.nmem (b + i) ≠ 0 ∧ c.nmem (Hb + i) = q)
    (hCY : ∀ l < k, c.nmem (Hb + 8 * n + l) < 3 * mN)
    (hCR : ∀ q < mN, c.nmem (Hb + 4 * n + q) < mN)
    (hSR : ∀ q < mN, c.nmem (Hb + 5 * n + q) < mN)
    (hJ : ∀ j, pdG (fun l => c.nmem (Hb + 8 * n + l)) k
      (pdS (fun l => c.nmem (Hb + 8 * n + l))) j < k → j < n) :
    ∃ c' t, Exec P W mbD c c' t ∧ t ≤ 24 * n + 78 * k + 50 ∧
      ∃ iv : ℕ → ℕ, (∀ i < n, c.nmem (b + i) ≠ 0 → iv (c.nmem (Hb + i)) = i) ∧
      (∀ j < n, c'.nmem (Hb + 6 * n + j) =
        if pdG (fun l => c.nmem (Hb + 8 * n + l)) k (pdS (fun l => c.nmem (Hb + 8 * n + l))) j < k
        then iv (pdOut (fun l => c.nmem (Hb + 8 * n + l)) (fun q => c.nmem (Hb + 4 * n + q))
          (fun q => c.nmem (Hb + 5 * n + q)) iv (fun i => c.nmem (b + 6 * n + i)) k
          (pdS (fun l => c.nmem (Hb + 8 * n + l)))
          (pdG (fun l => c.nmem (Hb + 8 * n + l)) k (pdS (fun l => c.nmem (Hb + 8 * n + l))) j)) + 1
        else 0) ∧
      (∀ a, ¬ (Hb + 6 * n ≤ a ∧ a < Hb + 8 * n) → ¬ (Hb + 12 * n ≤ a ∧ a < Hb + 13 * n) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5110 ∨ (5120 < x ∧ x < 5230) ∨ (5266 < x ∧ x < 6520) ∨ 6529 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lay
  have hn1 : 1 ≤ n := by omega
  -- the set-up
  obtain ⟨c₁, t₁, e₁, ht₁, a30, a31, a32, a33, a34, a35, a36, a37, a38, am₁, an₁, ar₁, arm₁,
    ao₁⟩ := pdA1_exec (P := P) c hc r00 r04 r641 ⟨by omega, by omega⟩
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, t₂, e₂, ht₂, b39, b40, b41, b42, b21, b10, b11, b12, b13, b14, bm₂, bn₂, br₂, brm₂,
    bo₂⟩ := pdA2_exec (P := P) c₁ hw₁ (n := n) (Hb := Hb) (b := b)
      (by rw [an₁ _ (by omega), r00]) (by rw [an₁ _ (by omega), r04])
      (by rw [an₁ _ (by omega), r41]) a33 a34 a36 a37 a38 ⟨by omega, by omega, by omega⟩
  have hw₂ := e₂.wb_right
  rw [am₁] at b42
  have q2 : ∀ x, (x < 5230 ∨ 5266 < x) → (x < 5110 ∨ (5114 < x ∧ x < 5239) ∨
      (5242 < x ∧ x < 5265) ∨ (5266 < x ∧ x < 6521) ∨ 6521 < x) → c₂.nreg x = c.nreg x :=
    fun x h1 h2 => by rw [bn₂ x h2, an₁ x (by omega)]
  have m2 : c₂.nmem = c.nmem := by rw [bm₂, am₁]
  -- the identity array
  obtain ⟨c₃, t₃, e₃, ht₃, f1, fm₃, fn₃, fr₃, frm₃, fo₃⟩ := pdIdFill_exec (P := P) c₂ hw₂
    (n := n) (IDb := Hb + 7 * n) (by rw [bn₂ _ (by omega), a30]) b21
    (by rw [bn₂ _ (by omega), a36]) (by omega) (by omega)
  have hw₃ := e₃.wb_right
  have k3 : ∀ x, ¬ MfDrv.vscr x → x ≠ 6522 → x ≠ 6520 → c₃.nreg x = c₂.nreg x := fn₃
  have m3 : ∀ a, ¬ (Hb + 7 * n ≤ a ∧ a < Hb + 7 * n + n) → c₃.nmem a = c.nmem a :=
    fun a h => by rw [fm₃ a h, m2]
  -- the inverse of the ranks
  obtain ⟨c₄, t₄, e₄, ht₄, g1, gm₄, gn₄, gr₄, grm₄, go₄⟩ := tks_exec (P := P) c₃ hw₃ (n := n)
    (m := mN) (NFb := b) (Kb := Hb) (Sb := Hb + 7 * n) (Db := Hb + 12 * n)
    (by rw [k3 _ (by unfold MfDrv.vscr; omega) (by omega) (by omega), b10])
    (by rw [k3 _ (by unfold MfDrv.vscr; omega) (by omega) (by omega), b11])
    (by rw [k3 _ (by unfold MfDrv.vscr; omega) (by omega) (by omega), b12])
    (by rw [k3 _ (by unfold MfDrv.vscr; omega) (by omega) (by omega), b13])
    (by rw [k3 _ (by unfold MfDrv.vscr; omega) (by omega) (by omega), b14])
    ⟨by omega, by omega, by omega, by omega, by omega⟩
    (fun i hi h => by
      rw [m3 _ (by omega)] at h ⊢; exact hRK i hi h)
    (fun i hi j hj h1 h2 h3 => by
      rw [m3 _ (by omega)] at h1 h2; rw [m3 _ (by omega), m3 _ (by omega)] at h3
      exact hinj i hi j hj h1 h2 h3)
  have hw₄ := e₄.wb_right
  set iv : ℕ → ℕ := fun q => c₄.nmem (Hb + 12 * n + q) with hivdef
  have hiv : ∀ i < n, c.nmem (b + i) ≠ 0 → iv (c.nmem (Hb + i)) = i := fun i hi h => by
    have h' : c₃.nmem (b + i) ≠ 0 := by rw [m3 _ (by omega)]; exact h
    have := g1 i hi h'
    rw [m3 (Hb + i) (by omega), f1 i hi] at this
    exact this
  have hIV : ∀ q < mN, iv q < n := fun q hq => by
    obtain ⟨i, hi, hf, rfl⟩ := hsurj q hq
    rw [hiv i hi hf]; exact hi
  have m4 : ∀ a, ¬ (Hb + 7 * n ≤ a ∧ a < Hb + 8 * n) → ¬ (Hb + 12 * n ≤ a ∧ a < Hb + 13 * n) →
      c₄.nmem a = c.nmem a := fun a h1 h2 => by
    rw [gm₄ a (by omega), m3 a (by omega)]
  have k4 : ∀ x, (x < 5115 ∨ 5120 < x) → ¬ MfDrv.vscr x → x ≠ 6522 → x ≠ 6520 →
      c₄.nreg x = c₂.nreg x := fun x h1 h2 h3 h4 => by rw [gn₄ x h1, k3 x h2 h3 h4]
  -- the zero fill of `PD`
  obtain ⟨c₅, t₅, e₅, ht₅, z1, zm₅, zn₅, zr₅, zrm₅, zo₅⟩ := MfDrv.zfill_exec (P := P) c₄ hw₄
    (bnd := 5230) (ob := 5235) (m := n) (Ob := Hb + 6 * n)
    (by rw [k4 _ (by omega) (by unfold MfDrv.vscr; omega) (by omega) (by omega), bn₂ _ (by omega),
      a30])
    (by rw [gn₄ _ (by omega), fn₃ _ (by unfold MfDrv.vscr; omega) (by omega) (by omega)]; exact b21)
    (by rw [k4 _ (by omega) (by unfold MfDrv.vscr; omega) (by omega) (by omega), bn₂ _ (by omega),
      a35])
    (by omega) (by omega) (by unfold MfDrv.vscr; omega) (by unfold MfDrv.vscr; omega) (by omega)
    (by omega) (by omega) (by omega)
  have hw₅ := e₅.wb_right
  have k5 : ∀ x, (x < 5115 ∨ 5120 < x) → ¬ MfDrv.vscr x → x ≠ 6522 → x ≠ 6520 →
      c₅.nreg x = c₂.nreg x := fun x h1 h2 h3 h4 => by rw [zn₅ x h2 h3 h4, k4 x h1 h2 h3 h4]
  have m5 : ∀ a, ¬ (Hb + 6 * n ≤ a ∧ a < Hb + 8 * n) → ¬ (Hb + 12 * n ≤ a ∧ a < Hb + 13 * n) →
      c₅.nmem a = c.nmem a := fun a h1 h2 => by rw [zm₅ a (by omega), m4 a (by omega) h2]
  have m5' : ∀ q < mN, c₅.nmem (Hb + 12 * n + q) = iv q := fun q hq => by
    rw [zm₅ _ (by omega)]
  -- the loop
  have kk : ∀ x, 5230 ≤ x → x ≤ 5242 → c₅.nreg x = c₂.nreg x := fun x h1 h2 =>
    k5 x (by omega) (by unfold MfDrv.vscr; omega) (by omega) (by omega)
  obtain ⟨c₆, t₆, e₆, ht₆, hPD, pm₆, pn₆, pr₆, prm₆, po₆⟩ := pdLoop_exec (P := P) c₅ hw₅
    (n := n) (mN := mN) (k := k) (s := pdS (fun l => c.nmem (Hb + 8 * n + l)))
    (PDb := Hb + 6 * n) (IVb := Hb + 12 * n) (CYb := Hb + 8 * n) (CRb := Hb + 4 * n)
    (SRb := Hb + 5 * n) (TKb := b + 6 * n) (cy := fun l => c.nmem (Hb + 8 * n + l))
    (cr := fun q => c.nmem (Hb + 4 * n + q)) (sr := fun q => c.nmem (Hb + 5 * n + q)) (iv := iv)
    (tk := fun i => c.nmem (b + 6 * n + i))
    (by rw [kk _ (by omega) (by omega), bn₂ _ (by omega), a31])
    (by rw [kk _ (by omega) (by omega), bn₂ _ (by omega), a32])
    (by rw [kk _ (by omega) (by omega), bn₂ _ (by omega), a33])
    (by rw [kk _ (by omega) (by omega), bn₂ _ (by omega), a34])
    (by rw [kk _ (by omega) (by omega), bn₂ _ (by omega), a35])
    (by rw [kk _ (by omega) (by omega), bn₂ _ (by omega), a37])
    (by rw [kk _ (by omega) (by omega), bn₂ _ (by omega), a38])
    (by rw [kk _ (by omega) (by omega), b39]) (by rw [kk _ (by omega) (by omega), b40])
    (by rw [kk _ (by omega) (by omega), b41]) (by rw [kk _ (by omega) (by omega), b42]; rfl)
    (by unfold pdS; omega)
    (fun l hl => m5 _ (by omega) (by omega)) (fun q hq => m5 _ (by omega) (by omega))
    (fun q hq => m5 _ (by omega) (by omega)) m5' (fun i hi => m5 _ (by omega) (by omega))
    hCY hCR hSR hIV hJ (fun j hj => z1 j hj)
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  refine ⟨c₆, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), by omega, iv, hiv, hPD,
    fun a h1 h2 => by rw [pm₆ a (by omega), m5 a h1 h2], fun x hx => ?_,
    by rw [pr₆, zr₅, gr₄, fr₃, br₂, ar₁], by rw [prm₆, zrm₅, grm₄, frm₃, brm₂, arm₁],
    by rw [po₆, zo₅, go₄, fo₃, bo₂, ao₁]⟩
  rw [pn₆ x (by omega), k5 x (by omega) (by unfold MfDrv.vscr; omega) (by omega) (by omega),
    bn₂ x (by omega), an₁ x (by omega)]

end Exec

end BKMNW

end PlanarFlow
