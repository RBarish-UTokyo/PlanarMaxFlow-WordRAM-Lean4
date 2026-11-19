module

public import PlanarFlow.BKMNW.SmXF

/-!
# The separator program `sepPX` on the extended frame, and `SepPSpecX`

**`sepPX s sepL`**: read the record (`R = mem (d + fsz m)`, `n = mem R`, `ph = mem (R + 1)`); if
`ph = 1` (a call of `smD`) or `n ≤ s` (a call of `decS` on a small piece, which is `smD` by
`decS_small`) run the small separator program `sepSm`, else the large-piece program `sepL`.

* `SepPSpecXL` (the specification `SepPSpecX` required of `sepL` only at the node calls whose record
  has phase `0` and more than `s` darts: the large pieces of `decS`);
* **`sepPX_spec`**: if `sepL` meets `SepPSpecXL`, then `sepPX ds.s sepL` meets **`SepPSpecX`** with
  steps `sT n k + 600 n + 50 k + 600` and room `sR n m k + smR n m k`, given `PkMin gid ds.pk`,
  `ν` injective and a loopless map;
* **`sepPX_spec_small`**: when no node call of `Reach` has a record of phase `0` with more than
  `s` darts (e.g. every piece has at most `s` darts), any `sepL` meets `SepPSpecXL` vacuously:
  `sepPX ds.s .skip` meets `SepPSpecX` unconditionally, steps `600 n + 50 k + 600`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {ds : DSys M}

/-- The test of the record: `r5610 = ((ph - 1) + (1 - ph)) * (n - s)`, `r5611 = 0`. -/
def sepD0 (s : ℕ) : Stmt := block [.copyN 5600 3004, .loadN 5601 5600, .constN 5602 7,
  .mulN 5603 5602 5601, .addN 5603 5603 5600, .constN 5602 4, .addN 5603 5603 5602,
  .loadN 5604 5603, .loadN 5605 5604, .constN 5602 1, .addN 5606 5604 5602, .loadN 5607 5606,
  .subN 5608 5607 5602, .subN 5609 5602 5607, .addN 5608 5608 5609, .constN 5602 s,
  .subN 5609 5605 5602, .mulN 5610 5608 5609, .constN 5611 0]

/-- **The separator program on the extended frame.** -/
def sepPX (s : ℕ) (sepL : Stmt) : Stmt := .seq (sepD0 s) (.ifLtN 5611 5610 sepL sepSm)

variable (M) in
/-- **`SepPSpecX` at the large pieces of `decS`** (records of phase `0` with more than `s` darts). -/
def SepPSpecXL (ds : DSys M) (Reach : MCall M → Prop) (gid : D → ℕ) (ν : V → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (sepL : Stmt) (sT : ℕ → ℕ → ℕ)
    (sR : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e h Sb m : ℕ)
    (en : ℕ → D) (c : Config),
    FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem →
    c.nmem (c.nmem (d + fsz m) + 1) = 0 → ds.s < c.nmem (c.nmem (d + fsz m)) →
    WordsBounded W c →
    c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3003 = h → c.nreg 6500 = Sb → e ≤ h → h < Sb →
    Sb + sR (l.piece ∪ r.piece).card m Hs.length ≤ W →
    ∃ c' t, Exec I W sepL c c' t ∧ t ≤ sT (l.piece ∪ r.piece).card Hs.length ∧ DRegKeep c c' ∧
      (∀ a < Sb, c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ i < m, c'.nmem (Sb + i) = bf (en i ∈ l.piece)) ∧
      (∀ i < m, c'.nmem (Sb + m + i) = bf (en i ∈ π.path.darts.toFinset)) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = bf (M.tail (en i) ∈ π.path.mverts)) ∧
      (∀ j < Hs.length, c'.nmem (Sb + 3 * m + j) =
        bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
      c'.nmem (Sb + 3 * m + Hs.length) = ntag l ∧ c'.nmem (Sb + 3 * m + Hs.length + 1) = ntag r ∧
      RecsOut M ds gid ν S T l r π Hs σ (Sb + 21 * m + 4 * Hs.length + 2)
        (Sb + sR (l.piece ∪ r.piece).card m Hs.length) (c'.nreg 6501) c'.nmem

lemma RecsOut.mono {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    {lo hi hi' Xb : ℕ} {mem : ℕ → ℕ} (h : RecsOut M ds gid ν S T l r π Hs σ lo hi Xb mem)
    (hh : hi ≤ hi') : RecsOut M ds gid ν S T l r π Hs σ lo hi' Xb mem :=
  ⟨h.1, h.2.1.trans hh, h.2.2.1, h.2.2.2⟩

section Exec

variable {I : Input} {W : ℕ}

theorem sepD0_exec (c : Config) (hc : WordsBounded W c) {s d m R n ph : ℕ}
    (r4 : c.nreg 3004 = d) (hm : c.nmem d = m) (hR : c.nmem (d + 7 * m + 4) = R)
    (hn : c.nmem R = n) (hph : c.nmem (R + 1) = ph) (hph2 : ph ≤ 2)
    (w : d + 7 * m + 4 ≤ W) (wR : R + 1 ≤ W) (ws : s ≤ W) (wn : 2 * n + 7 ≤ W) :
    ∃ c' t, Exec I W (sepD0 s) c c' t ∧ t = 19 ∧
      c'.nreg 5610 = ((ph - 1) + (1 - ph)) * (n - s) ∧ c'.nreg 5611 = 0 ∧
      (∀ x, (x < 5600 ∨ 5611 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hle : ((ph - 1) + (1 - ph)) * (n - s) ≤ 2 * n := by
    have : (ph - 1) + (1 - ph) ≤ 2 := by omega
    calc ((ph - 1) + (1 - ph)) * (n - s) ≤ 2 * (n - s) := Nat.mul_le_mul_right _ this
      _ ≤ 2 * n := by omega
  unfold sepD0
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r4, hm]; omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r4, hm,
    show 7 * m + d + 4 = d + 7 * m + 4 by omega, hR, hn, hph]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r4, hm,
      show 7 * m + d + 4 = d + 7 * m + 4 by omega, hR, hn, hph])
    try omega

end Exec

end MfDrv

end BKMNW

end PlanarFlow
