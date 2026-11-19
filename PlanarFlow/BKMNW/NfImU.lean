module

public import PlanarFlow.BKMNW.FrImB
public import PlanarFlow.BKMNW.FrImC
public import PlanarFlow.BKMNW.NfFrRun

/-!
# The update of the resident FR image between two stages

Between two stages of FixConservationOnPath, the FR input `MsCall.frPrm b Dm pm r ET EH Lz (2k)`
changes only in the prices `pm` and the lengths `Lz` (the tails and heads of the explicit arcs are
those of the darts of the path; the matrix is the dense distance graph): the offsets and heads of
the image (`frNM`) are the same, and of the residues (`frRS`) only `[pb, pb + b)` (prices) and
`[lb, lb + mE)` (lengths of the arcs sorted by tail) change (`frCfgN_mkPrm_stage`).

**`imU`** `= imS1 ; fiPr ; fiLn ; imS2 ; fiPr ; fiLn` writes these residues with the loops
`MsCall.fiPr`, `MsCall.fiLn` (`(w + Kp) mod Mo`, `Kp = Mo − K mod Mo`, `MsCall.res_off`) into the
live image at `Bl = r9360` and into its shadow at `Bs = r9361` (sorted indices at `r9362`).
**`imU_exec`**: within `18 b + 22 mE + 12` steps; nothing else written. `O(b + k)` per stage.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace MsCall

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Monge.FR NegSSSP

/-- The base of the live image. -/
def imS1 : Stmt := block [.copyN 8126 9360, .copyN 8142 9362]

/-- The base of the shadow. -/
def imS2 : Stmt := block [.copyN 8126 9361, .copyN 8142 9362]

/-- **The residues of the prices and the lengths, in the live image and in the shadow.** -/
def imU : Stmt := .seq (.seq imS1 (.seq fiPr fiLn)) (.seq imS2 (.seq fiPr fiLn))

variable {P : Input} {W : ℕ}

theorem imS_exec (c : Config) (hc : WordsBounded W c) {s : ℕ} (hs : s = 9360 ∨ s = 9361) :
    ∃ c' t, Exec P W (block [.copyN 8126 s, .copyN 8142 9362]) c c' t ∧ t = 2 ∧
      c'.nreg 8126 = c.nreg s ∧ c'.nreg 8142 = c.nreg 9362 ∧
      (∀ r, r ≠ 8126 → r ≠ 8142 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> first | rfl | omega)

/-- One pass: the prices and the lengths at the base `As`. -/
theorem imPass_exec (c : Config) (hc : WordsBounded W c) {b mE As pb lb PRb SIb ELb Kp Mo : ℕ}
    (r00 : c.nreg 8100 = b) (r26 : c.nreg 8126 = As) (r13 : c.nreg 8113 = pb)
    (r02 : c.nreg 8102 = PRb) (r25 : c.nreg 8125 = Kp) (r24 : c.nreg 8124 = Mo)
    (r12 : c.nreg 8112 = 1) (r04 : c.nreg 8104 = mE) (r15 : c.nreg 8115 = lb)
    (r42 : c.nreg 8142 = SIb) (r07 : c.nreg 8107 = ELb)
    (hpl : pb + b ≤ lb) (hAP : As + lb + mE ≤ PRb) (hAS : As + lb + mE ≤ SIb)
    (hEL : ∀ e < mE, As + lb + mE ≤ ELb + c.nmem (SIb + e) ∧ ELb + c.nmem (SIb + e) ≤ W ∧
      c.nmem (ELb + c.nmem (SIb + e)) + Kp ≤ W)
    (hPR : ∀ x < b, c.nmem (PRb + x) + Kp ≤ W) (hW2 : PRb + b ≤ W) (hW3 : SIb + mE ≤ W)
    (hW4 : b + mE + 1 ≤ W) :
    ∃ c' t, Exec P W (.seq fiPr fiLn) c c' t ∧ t ≤ 9 * b + 11 * mE + 8 ∧
      (∀ x < b, c'.nmem (As + pb + x) = (c.nmem (PRb + x) + Kp) % Mo) ∧
      (∀ e < mE, c'.nmem (As + lb + e) = (c.nmem (ELb + c.nmem (SIb + e)) + Kp) % Mo) ∧
      (∀ a, (a < As + pb ∨ As + lb + mE ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, As + pb + b ≤ a → a < As + lb → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 8140 ∨ 8149 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAW : As + lb + mE ≤ W := by have := hc.1 8102; omega
  obtain ⟨c₁, t₁, e₁, ht₁, P1, P2, P3, pr, prm, po⟩ :=
    fiPr_exec (P := P) c hc r00 r26 r13 r02 r25 r24 r12 (Or.inr (by omega)) hPR (by omega) hW2
      (by omega)
  have q : ∀ r, r ≠ 8140 → r ≠ 8145 → r ≠ 8146 → r ≠ 8148 → c₁.nreg r = c.nreg r := P3
  have hSI : ∀ e < mE, c₁.nmem (SIb + e) = c.nmem (SIb + e) := fun e he =>
    P2 _ (Or.inr (by omega))
  obtain ⟨c₂, t₂, e₂, ht₂, L1, L2, L3, lr, lrm, lo⟩ :=
    fiLn_exec (P := P) c₁ e₁.wb_right (mE := mE) (As := As) (lb := lb) (SIb := SIb) (ELb := ELb)
      (Kp := Kp) (Mo := Mo) (by rw [q _ (by omega) (by omega) (by omega) (by omega), r04])
      (by rw [q _ (by omega) (by omega) (by omega) (by omega), r26])
      (by rw [q _ (by omega) (by omega) (by omega) (by omega), r15])
      (by rw [q _ (by omega) (by omega) (by omega) (by omega), r42])
      (by rw [q _ (by omega) (by omega) (by omega) (by omega), r07])
      (by rw [q _ (by omega) (by omega) (by omega) (by omega), r25])
      (by rw [q _ (by omega) (by omega) (by omega) (by omega), r24])
      (by rw [q _ (by omega) (by omega) (by omega) (by omega), r12]) (Or.inr (by omega))
      (fun e he => by
        rw [hSI e he]
        obtain ⟨h1, h2, h3⟩ := hEL e he
        refine ⟨h2, ?_, Or.inr h1⟩
        rw [P2 _ (Or.inr (by omega))]; exact h3)
      (by omega) hW3 (by omega)
  refine ⟨c₂, _, .seq e₁ e₂, by omega, fun x hx => ?_, fun e he => ?_, fun a ha => ?_,
    fun a h1 h2 => ?_, fun r hr => ?_, by rw [lr, pr], by rw [lrm, prm], by rw [lo, po]⟩
  · rw [L2 _ (Or.inl (by omega)), P1 x hx]
  · rw [L1 e he, hSI e he, P2 _ (Or.inr (by have := (hEL e he).1; omega))]
  · rw [L2 a (by omega), P2 a (by omega)]
  · rw [L2 a (Or.inl h2), P2 a (Or.inr h1)]
  · rw [L3 r hr, q r (by omega) (by omega) (by omega) (by omega)]

/-- **The update of the live image and of its shadow.** -/
theorem imU_exec (c : Config) (hc : WordsBounded W c)
    {b mE Bl Bs pb lb PRb SIb ELb Kp Mo : ℕ}
    (r00 : c.nreg 8100 = b) (r60 : c.nreg 9360 = Bl) (r61 : c.nreg 9361 = Bs)
    (r13 : c.nreg 8113 = pb) (r02 : c.nreg 8102 = PRb) (r25 : c.nreg 8125 = Kp)
    (r24 : c.nreg 8124 = Mo) (r12 : c.nreg 8112 = 1) (r04 : c.nreg 8104 = mE)
    (r15 : c.nreg 8115 = lb) (r62 : c.nreg 9362 = SIb) (r07 : c.nreg 8107 = ELb)
    (hpl : pb + b ≤ lb) (hLS : Bl + lb + mE ≤ Bs + pb) (hAP : Bs + lb + mE ≤ PRb)
    (hAS : Bs + lb + mE ≤ SIb)
    (hEL : ∀ e < mE, Bs + lb + mE ≤ ELb + c.nmem (SIb + e) ∧ ELb + c.nmem (SIb + e) ≤ W ∧
      c.nmem (ELb + c.nmem (SIb + e)) + Kp ≤ W)
    (hPR : ∀ x < b, c.nmem (PRb + x) + Kp ≤ W) (hW2 : PRb + b ≤ W) (hW3 : SIb + mE ≤ W)
    (hW4 : b + mE + 1 ≤ W) :
    ∃ c' t, Exec P W imU c c' t ∧ t ≤ 18 * b + 22 * mE + 20 ∧
      (∀ x < b, c'.nmem (Bl + pb + x) = (c.nmem (PRb + x) + Kp) % Mo ∧
        c'.nmem (Bs + pb + x) = (c.nmem (PRb + x) + Kp) % Mo) ∧
      (∀ e < mE, c'.nmem (Bl + lb + e) = (c.nmem (ELb + c.nmem (SIb + e)) + Kp) % Mo ∧
        c'.nmem (Bs + lb + e) = (c.nmem (ELb + c.nmem (SIb + e)) + Kp) % Mo) ∧
      (∀ a, ¬ (Bl + pb ≤ a ∧ a < Bl + pb + b) → ¬ (Bl + lb ≤ a ∧ a < Bl + lb + mE) →
        ¬ (Bs + pb ≤ a ∧ a < Bs + pb + b) → ¬ (Bs + lb ≤ a ∧ a < Bs + lb + mE) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 8140 ∨ 8149 < r) → r ≠ 8126 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a26, a42, ak, am, ar, arm, ao⟩ :=
    imS_exec (P := P) c hc (s := 9360) (Or.inl rfl)
  have q1 : ∀ r, r ≠ 8126 → r ≠ 8142 → c₁.nreg r = c.nreg r := ak
  obtain ⟨c₂, t₂, e₂, ht₂, B1, B2, B3, B4, bk, br, brm, bo⟩ :=
    imPass_exec (P := P) c₁ e₁.wb_right (b := b) (mE := mE) (As := Bl) (pb := pb) (lb := lb)
      (PRb := PRb) (SIb := SIb) (ELb := ELb) (Kp := Kp) (Mo := Mo)
      (by rw [q1 _ (by omega) (by omega), r00]) (by rw [a26, r60])
      (by rw [q1 _ (by omega) (by omega), r13]) (by rw [q1 _ (by omega) (by omega), r02])
      (by rw [q1 _ (by omega) (by omega), r25]) (by rw [q1 _ (by omega) (by omega), r24])
      (by rw [q1 _ (by omega) (by omega), r12]) (by rw [q1 _ (by omega) (by omega), r04])
      (by rw [q1 _ (by omega) (by omega), r15]) (by rw [a42, r62])
      (by rw [q1 _ (by omega) (by omega), r07]) hpl (by omega) (by omega)
      (fun e he => by rw [am]; obtain ⟨h1, h2, h3⟩ := hEL e he; exact ⟨by omega, h2, h3⟩)
      (fun x hx => by rw [am]; exact hPR x hx) hW2 hW3 hW4
  -- the inputs are kept by the first pass
  have k2 : ∀ a, Bs + pb ≤ a → c₂.nmem a = c.nmem a := fun a ha => by
    rw [B3 a (Or.inr (by omega)), am]
  obtain ⟨c₃, t₃, e₃, ht₃, d26, d42, dk, dm, dr, drm, do'⟩ :=
    imS_exec (P := P) c₂ e₂.wb_right (s := 9361) (Or.inr rfl)
  have q3 : ∀ r, (r < 8140 ∨ 8149 < r) → r ≠ 8126 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    rw [dk r h2 (by omega), bk r h1, q1 r h2 (by omega)]
  obtain ⟨c₄, t₄, e₄, ht₄, C1, C2, C3, C4, ck, cr, crm, co⟩ :=
    imPass_exec (P := P) c₃ e₃.wb_right (b := b) (mE := mE) (As := Bs) (pb := pb) (lb := lb)
      (PRb := PRb) (SIb := SIb) (ELb := ELb) (Kp := Kp) (Mo := Mo)
      (by rw [q3 _ (by omega) (by omega), r00])
      (by rw [d26, bk _ (by omega), q1 _ (by omega) (by omega), r61])
      (by rw [q3 _ (by omega) (by omega), r13]) (by rw [q3 _ (by omega) (by omega), r02])
      (by rw [q3 _ (by omega) (by omega), r25]) (by rw [q3 _ (by omega) (by omega), r24])
      (by rw [q3 _ (by omega) (by omega), r12]) (by rw [q3 _ (by omega) (by omega), r04])
      (by rw [q3 _ (by omega) (by omega), r15])
      (by rw [d42, bk _ (by omega), q1 _ (by omega) (by omega), r62])
      (by rw [q3 _ (by omega) (by omega), r07]) hpl hAP hAS
      (fun e he => by
        rw [dm, k2 (SIb + e) (by omega),
          k2 (ELb + c.nmem (SIb + e)) (by have := (hEL e he).1; omega)]; exact hEL e he)
      (fun x hx => by rw [dm, k2 _ (by omega)]; exact hPR x hx) hW2 hW3 hW4
  have k4 : ∀ a, (a < Bs + pb ∨ Bs + lb + mE ≤ a) → ¬ (Bs + pb + b ≤ a ∧ a < Bs + lb) →
      c₄.nmem a = c₂.nmem a := fun a h1 _ => by rw [C3 a h1, dm]
  refine ⟨c₄, _, .seq (.seq e₁ e₂) (.seq e₃ e₄), by omega, fun x hx => ⟨?_, ?_⟩,
    fun e he => ⟨?_, ?_⟩, fun a h1 h2 h3 h4 => ?_, fun r h1 h2 => ?_,
    by rw [cr, dr, br, ar], by rw [crm, drm, brm, arm], by rw [co, do', bo, ao]⟩
  · rw [C3 _ (Or.inl (by omega)), dm, B1 x hx, am]
  · rw [C1 x hx, dm, k2 _ (by omega)]
  · rw [C3 _ (Or.inl (by omega)), dm, B2 e he, am]
  · rw [C2 e he, dm, k2 (SIb + e) (by omega),
      k2 (ELb + c.nmem (SIb + e)) (by have := (hEL e he).1; omega)]
  · have hc4 : c₄.nmem a = c₂.nmem a := by
      by_cases hs : Bs + pb + b ≤ a ∧ a < Bs + lb
      · rw [C4 a hs.1 hs.2, dm]
      · rw [C3 a (by omega), dm]
    have hc2 : c₂.nmem a = c.nmem a := by
      by_cases hs : Bl + pb + b ≤ a ∧ a < Bl + lb
      · rw [B4 a hs.1 hs.2, am]
      · rw [B3 a (by omega), am]
    rw [hc4, hc2]
  · rw [ck r h1, q3 r h1 h2]

end MsCall

end BKMNW

end PlanarFlow
