module

public import PlanarFlow.BKMNW.FrCall
public import PlanarFlow.BKMNW.NfRst

/-!
# FR-Dijkstra on a resident image, restored from a shadow

`FrFix.frCall` copies the whole image of the FR input (including the `b × b` dense distance
graph) into the low memory and clears it at every call: `Θ(b²)` per stage of FixConservationOnPath,
`Θ(k b²)` per path. Here the image stays **resident** in
the low memory `[0, frWN P L]` (exactly the memory of `frCfgN P L`), with a **shadow copy** at
`SH` (`[SH, SH + frWN P L]`); the run of the fixed natural FR-Dijkstra is logged, its result
copied out, and every logged cell restored from the shadow (`lgRst`). Between two stages only the
cells of the prices, the explicit arcs and the root change (in both copies), not the matrix.

**`frRun`** `= (mbZeroRegs (range 763) ; fcSet) ; lgS 7620 7621 frNF ; fcOut ; fkRs ; lgRst`
(arguments as for `frCall`, plus `r7616 = SH`).

**`frRun_exec`**: from the resident image and its shadow, within
**`108 · frCost P + 14 · N + 1000`** steps (no `sb` term), the result `FResN P L K v dd · Ob
(Ob + N)` at `Ob`, the memory `≤ frWN P L` **as before** (the resident image again), the memory
above `frWN P L` outside the result and the log kept (the shadow included), the registers outside
`frScr` kept, reals and output kept.
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

/-- The arguments of the restore: `2924 = p`, `2925 = LP`, `2926 = 1`, `9300 = SH`. -/
def fkRs : Stmt := block [.copyN 2924 7615, .copyN 2925 7620, .constN 2926 1, .copyN 9300 7616]

/-- **FR-Dijkstra on the resident image**, restored from the shadow. -/
def frRun : Stmt :=
  .seq (.seq (mbZeroRegs (List.range 763)) fcSet)
    (.seq (lgS 7620 7621 frNF) (.seq fcOut (.seq fkRs lgRst)))

/-- The scratch registers of `frRun`. -/
def frScr (r : ℕ) : Prop :=
  r < 763 ∨ (2923 ≤ r ∧ r ≤ 2929) ∨ (4910 ≤ r ∧ r ≤ 4916) ∨ r = 7620 ∨ r = 7621 ∨ r = 9300 ∨
    r = 9301

variable {P' : Input} {W : ℕ}

theorem fkRs_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' t, Exec P' W fkRs c c' t ∧ t = 4 ∧ c'.nreg 2924 = c.nreg 7615 ∧
      c'.nreg 2925 = c.nreg 7620 ∧ c'.nreg 2926 = 1 ∧ c'.nreg 9300 = c.nreg 7616 ∧
      (∀ r, r ≠ 2924 → r ≠ 2925 → r ≠ 2926 → r ≠ 9300 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fkRs
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp only [upd_apply]
  all_goals split_ifs <;> omega

theorem frRun_exec {P : Prm} {L : ℕ} (hL : Lay P) (hXB : XB P L) (hDc : Crossing P.b P.D)
    (hF : Feas P) {Ob p SH : ℕ} (c : Config) (hc : WordsBounded W c)
    (r00 : c.nreg 7600 = P.N) (r01 : c.nreg 7601 = P.b) (r02 : c.nreg 7602 = P.Db)
    (r03 : c.nreg 7603 = P.pb) (r04 : c.nreg 7604 = P.ob) (r05 : c.nreg 7605 = P.lb)
    (r06 : c.nreg 7606 = P.r) (r07 : c.nreg 7607 = P.sb) (r08 : c.nreg 7608 = P.db)
    (r09 : c.nreg 7609 = P.wb) (r10 : c.nreg 7610 = frM P L) (r11 : c.nreg 7611 = frH P L)
    (r12 : c.nreg 7612 = P.W + 1) (r14 : c.nreg 7614 = Ob) (r15 : c.nreg 7615 = p)
    (r16 : c.nreg 7616 = SH)
    (himg : ∀ a ≤ frWN P L, c.nmem a = (frCfgN P L).nmem a)
    (hsh : ∀ a ≤ frWN P L, c.nmem (SH + a) = (frCfgN P L).nmem a)
    (hSH : frWN P L < SH) (hSO : SH + frWN P L < Ob) (hOp : Ob + P.N + P.N ≤ p)
    (hpW : p + (4 * frCost P + 3) ≤ W) :
    ∃ c' t, Exec P' W frRun c c' t ∧ t ≤ 108 * frCost P + 14 * P.N + 1000 ∧
      (∀ a ≤ frWN P L, c'.nmem a = c.nmem a) ∧
      (∃ K v dd, FResN P L K v dd c'.nmem Ob (Ob + P.N)) ∧
      (∀ a, frWN P L < a → (a < Ob ∨ Ob + P.N + P.N ≤ a) →
        (a < p ∨ p + (4 * frCost P + 3) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ frScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hw := lay_w hL
  have hm5 := hL.m5
  have hm6 := hL.m6
  have hWN : 2 * P.W + 1 ≤ frWN P L := by unfold frWN; omega
  -- the reference run
  obtain ⟨dN', k', ex, hk', ho', K, v, dd, hR⟩ := frNF_ref hL hXB hDc hF P'
  -- before the run
  obtain ⟨c₂, e₂, Z2, K2, nm₂, rr₂, rm₂, o₂⟩ := mbZeroRegs_exec' (P := P') (List.range 763) c hc
  obtain ⟨c₃, t₃, e₃, ht₃, N3, nm₃, rr₃, rm₃, o₃⟩ := fcSet_exec (P := P') c₂ e₂.wb_right
    (by omega)
  have q2 : ∀ r, 763 ≤ r → c₂.nreg r = c.nreg r := fun r h1 => K2 r (by simp; omega)
  have key : ∀ r < 763, c₃.nreg r = (frCfgN P L).nreg r := fun r hr => by
    rw [N3]
    exact fcRegs_eq c₂.nreg (fun r hr => Z2 r (by simp; omega))
      (by rw [q2 _ (by omega), r00]) (by rw [q2 _ (by omega), r01])
      (by rw [q2 _ (by omega), r02]) (by rw [q2 _ (by omega), r03])
      (by rw [q2 _ (by omega), r04]) (by rw [q2 _ (by omega), r05])
      (by rw [q2 _ (by omega), r06]) (by rw [q2 _ (by omega), r07])
      (by rw [q2 _ (by omega), r08]) (by rw [q2 _ (by omega), r09])
      (by rw [q2 _ (by omega), r10]) (by rw [q2 _ (by omega), r11])
      (by rw [q2 _ (by omega), r12]) r hr
  have q3 : ∀ r, 763 ≤ r → r ≠ 7620 → r ≠ 7621 → c₃.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [N3]
    simp only [upd_apply, h2, h3, show r ≠ 762 by omega, show r ≠ 761 by omega,
      show r ≠ 760 by omega, show r ≠ 109 by omega, show r ≠ 108 by omega, show r ≠ 107 by omega,
      show r ≠ 106 by omega, show r ≠ 105 by omega, show r ≠ 104 by omega, show r ≠ 103 by omega,
      show r ≠ 102 by omega, show r ≠ 101 by omega, show r ≠ 100 by omega, ↓reduceIte]
    exact q2 r h1
  have s20 : c₃.nreg 7620 = p := by
    rw [N3]; simp only [upd_apply, ↓reduceIte]; rw [q2 _ (by omega), r15]
  have s21 : c₃.nreg 7621 = 1 := by
    rw [N3]; simp only [upd_apply, show (7621 : ℕ) ≠ 7620 by omega, ↓reduceIte]
  have hm3 : ∀ a ≤ frWN P L, c₃.nmem a = (frCfgN P L).nmem a := fun a ha => by
    rw [nm₃, nm₂, himg a ha]
  -- the run
  obtain ⟨c₄, k₄, j, ex₄, hk₄, hj, A4, Mm4, K4, rr₄, rm₄, L4, o41, o42⟩ :=
    frNF_lgRun (P' := P') ex (LP := 7620) (ONE := 7621) (by omega) (by omega) (by omega)
      (by omega) c₃ key hm3 e₃.wb_right s21 (by rw [s20]; omega) (by rw [s20]; omega)
  rw [s20] at K4
  have q4 : ∀ r, 763 ≤ r → r ≠ 7620 → r ≠ 7621 → c₄.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [K4.nreg r (by simp; omega) h2, q3 r h1 h2 h3]
  -- after the run
  obtain ⟨c₅, t₅, e₅, ht₅, O1, O2, O3, R5, rr₅, rm₅, o₅⟩ :=
    fcOut_exec (P := P') c₄ ex₄.wb_right (N := P.N) (sb := P.sb) (β := P.W + 1) (db := P.db)
      (Ob := Ob) (by rw [q4 _ (by omega) (by omega) (by omega), r00])
      (by rw [q4 _ (by omega) (by omega) (by omega), r07])
      (by rw [q4 _ (by omega) (by omega) (by omega), r12])
      (by rw [q4 _ (by omega) (by omega) (by omega), r08])
      (by rw [q4 _ (by omega) (by omega) (by omega), r14]) (by omega) (by omega)
      (by omega) (by omega)
  have q5 : ∀ r, 763 ≤ r → r ≠ 7620 → r ≠ 7621 → (r < 4910 ∨ 4916 < r) →
      c₅.nreg r = c.nreg r := fun r h1 h2 h3 h4 => by rw [R5 r h4, q4 r h1 h2 h3]
  obtain ⟨c₆, t₆, e₆, ht₆, f24, f25, f26, f00, fk, fm, fr, frm, fo⟩ :=
    fkRs_exec (P' := P') c₅ e₅.wb_right (by omega)
  have hlog6 : ∀ i < j, c₆.nmem (p + i) = c₄.nmem (p + i) := fun i hi => by
    rw [fm]; exact O3 _ (Or.inr (by omega))
  obtain ⟨c₇, t₇, e₇, ht₇, G1, G2, G7, rr₇, rm₇, o₇⟩ :=
    lgRst_exec (P := P') c₆ e₆.wb_right (p := p) (j := j) (Ws := frWN P L) (SH := SH)
      (by rw [f24, q5 _ (by omega) (by omega) (by omega) (by omega), r15])
      (by rw [f25, R5 _ (by omega), K4.lp]) f26
      (by rw [f00, q5 _ (by omega) (by omega) (by omega) (by omega), r16])
      (fun i hi => by rw [hlog6 i hi]; exact K4.logle i hi) (by omega) hSH (by omega)
  have notlog : ∀ a, frWN P L < a → ∀ i < j, c₆.nmem (p + i) ≠ a := fun a ha i hi e => by
    have := K4.logle i hi; rw [hlog6 i hi] at e; omega
  -- the memory above `frWN`
  have up6 : ∀ a, frWN P L < a → (a < Ob ∨ Ob + P.N + P.N ≤ a) →
      (a < p ∨ p + (4 * frCost P + 3) ≤ a) → c₆.nmem a = c.nmem a := by
    intro a h1 h2 h3
    rw [fm, O3 a h2, K4.nmem a (by omega) (by omega), nm₃, nm₂]
  have up : ∀ a, frWN P L < a → (a < Ob ∨ Ob + P.N + P.N ≤ a) →
      (a < p ∨ p + (4 * frCost P + 3) ≤ a) → c₇.nmem a = c.nmem a := by
    intro a h1 h2 h3
    rw [G2 a (notlog a h1), up6 a h1 h2 h3]
  refine ⟨c₇, _, (e₂.seq e₃).seq (ex₄.seq (e₅.seq (e₆.seq e₇))), ?_, fun a ha => ?_,
    ⟨K, v, dd, hR.congr (fun y hy => ?_) (fun y hy => ?_)⟩, up, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [List.length_range]
    omega
  · by_cases hl : ∃ i < j, c₆.nmem (p + i) = a
    · rw [G1 a hl, up6 (SH + a) (by omega) (Or.inl (by omega)) (Or.inl (by omega)), hsh a ha,
        himg a ha]
    · simp only [not_exists, not_and] at hl
      rw [G2 a (fun i hi => hl i hi), fm, O3 a (Or.inl (by omega)),
        K4.dirty a ha (fun i hi e => hl i hi (by rw [hlog6 i hi]; exact e)), nm₃, nm₂]
  · rw [G2 _ (notlog _ (by omega)), fm, O1 y hy, Mm4 _ (by omega)]
  · rw [G2 _ (notlog _ (by omega)), fm, O2 y hy, Mm4 _ (by omega)]
  · unfold frScr at hr
    rw [G7 r (by omega) (by omega) (by omega) (by omega), fk r (by omega) (by omega) (by omega)
      (by omega), q5 r (by omega) (by omega) (by omega) (by omega)]
  · rw [rr₇, fr, rr₅, rr₄, rr₃, rr₂]
  · rw [rm₇, frm, rm₅, rm₄, rm₃, rm₂]
  · have h0 : (frCfgN P L).output = [] := rfl
    rw [h0, ho'] at o41
    simp only [List.nil_append] at o41
    rw [o₇, fo, o₅, o42, ← o41, List.append_nil, o₃, o₂]

/-- **Between two stages the resident image changes only in the prices, the arcs, the root**:
two inputs laid out by `mkPrm` with the same corners, matrix and number of arcs have the same
image memory below `b²` (the natural part there is `0`), from `sb` to `β + b²` (the residues of
the matrix) and from `β + sb` on. -/
theorem frCfgN_mkPrm_stage {N b : ℕ} {D : ℕ → ℕ → ℤ} {p p' : ℕ → ℤ} {r r' : ℕ}
    {Es Es' : List (ℕ × ℕ × ℤ)} {L : ℕ} (hL : Lay (mkPrm N b D p r Es))
    (hL' : Lay (mkPrm N b D p' r' Es'))
    (hm : (arcList N Es).length = (arcList N Es').length) (a : ℕ)
    (ha : a < b * b ∨ ((mkPrm N b D p r Es).sb ≤ a ∧
      (a < (mkPrm N b D p r Es).W + 1 + b * b ∨
        (mkPrm N b D p r Es).W + 1 + (mkPrm N b D p r Es).sb ≤ a))) :
    (frCfgN (mkPrm N b D p r Es) L).nmem a = (frCfgN (mkPrm N b D p' r' Es') L).nmem a := by
  have esb : (mkPrm N b D p' r' Es').sb = (mkPrm N b D p r Es).sb := by simp [mkPrm, hm]
  have eW : (mkPrm N b D p' r' Es').W = (mkPrm N b D p r Es).W := by simp [mkPrm, hm]
  have eM : frM (mkPrm N b D p' r' Es') L = frM (mkPrm N b D p r Es) L := by
    simp [frM, frH, BB, mkPrm]
  rw [frCfgN_nmem hL, frCfgN_nmem hL', esb, eW]
  have hsb : b * b ≤ (mkPrm N b D p r Es).sb := by simp only [mkPrm]; omega
  rcases ha with ha | ⟨h1, h2⟩
  · have h0 : a < (mkPrm N b D p r Es).sb := by omega
    simp only [h0, ↓reduceIte, frNM]
    have e1 : (mkPrm N b D p r Es).ob = b * b + N := rfl
    have e2 : (mkPrm N b D p' r' Es').ob = b * b + N := rfl
    rw [e1, e2]
    have hx : ∀ X, ¬ (b * b + N + X + 1 ≤ a) := fun X => by omega
    simp only [show ¬ (b * b + N ≤ a) by omega, false_and, ↓reduceIte, hx]
  · have h0 : ¬ a < (mkPrm N b D p r Es).sb := by omega
    simp only [h0, ↓reduceIte]
    rcases h2 with h2 | h2
    · by_cases h3 : (mkPrm N b D p r Es).W + 1 ≤ a
      · have h4 : a < (mkPrm N b D p r Es).W + 1 + (mkPrm N b D p r Es).sb := by omega
        simp only [h3, h4, and_self, ↓reduceIte, frRS, frRZ, eM]
        have e1 : (mkPrm N b D p r Es).Db = 0 := rfl
        have e2 : (mkPrm N b D p' r' Es').Db = 0 := rfl
        have e3 : (mkPrm N b D p r Es).b = b := rfl
        have e4 : (mkPrm N b D p' r' Es').b = b := rfl
        have e5 : (mkPrm N b D p r Es).D = D := rfl
        have e6 : (mkPrm N b D p' r' Es').D = D := rfl
        have hx : a - ((mkPrm N b D p r Es).W + 1) < b * b := by omega
        simp only [e1, e2, e3, e4, e5, e6, Nat.zero_le, true_and, zero_add, hx, ↓reduceIte]
      · simp only [h3, false_and, ↓reduceIte]
    · simp only [show ¬ ((mkPrm N b D p r Es).W + 1 ≤ a ∧
        a < (mkPrm N b D p r Es).W + 1 + (mkPrm N b D p r Es).sb) by omega, ↓reduceIte]

end FrFix

end BKMNW

end PlanarFlow
