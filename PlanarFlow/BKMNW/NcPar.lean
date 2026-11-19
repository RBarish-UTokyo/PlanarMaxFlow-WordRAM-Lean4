module

public import PlanarFlow.BKMNW.NcIdent
public import PlanarFlow.BKMNW.NcAr
public import PlanarFlow.BKMNW.SgSem
public import PlanarFlow.BKMNW.StCallZA

/-!
# The parameter programs of `c2sP` and the tail of `c2sP`

The two subroutine calls of `c2s` that are written separately are taken as **parameter programs with
stated specifications**:

* **`FzPSpec`** (FixConservationOnPath with frozen vertices, `fixFrozen`; the machinery of `fixP`): at a node call with the frame (`Lay`), the parts of the separator with their start
  vertices (**`SegsAt'`**), the part `πj` (`segsP …[j]`), from the arrays `CP = U`,
  `F1 = Z + f₁` (`f₁` a pseudoflow for `0 ≤ U ≤ Z`) and `DF = [tail ∈ Del]` (registers `9800`
  `F1`, `9801` `DF`, `9802` `CP`, `9803` `FF`, `9804` scratch base `Sb`), within `fzT x j` steps,
  `FF = Z + fixFrozen (pmap h) e … U f₁ πj Del` (for every dart choice `e`); memory below `Sb`
  off `FF` kept; the registers `PKeep` kept;
* **`PbPSpec`** (the push-back `pchCall gid x h β ∅`, `pchP`): from `BT = β ∘ tail`
  (`β ≥ 0`), `G = 2Z + g'` (`|g'| ≤ 2Z`, the result also bounded by `2Z`; registers `9805` `BT`,
  `9806` `G`, `9807` `PB`, `9808` `Sb`), within `pbT x j` steps, `PB = 2Z + pchCall … β ∅ g'`.

The tail of `c2sP` (**`c2tP fzP pbP`**): `stCallZ` (the maximum flow on `c2sCap` from the part to
the hole), `F1 = FL + O − 2Z` (`axL`), `fzP`, `G = FF + 2Z − FL` (`sxL`), `pbP`,
`FL := FL + PB − 2Z` (`axL`), with the glue blocks `tgA … tgD`. Registers of the tail: `9810`
`CAP`, `9811` `CF`, `9812` `HF` (the flags of `C` and `H`), `9813` `ib` (base in the zero area for
`stCallZ`), `9814` `O`, `9815` `p` (scratch of `stCallZ`), `9816` `2Z`, `9818` `m`, `9819` `d`;
temporaries `9820 … 9822` (`9821 = FL` base).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap MfDrv NsStep StCall WordRAM WordRAM.Machine
  WordRAM.Machine.Stmt WordRAM.Programs

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **The parts of the separator with their start vertices** for the step (`SegsOut'` from
`r6807`; `SegsAt` with the start vertices recorded by `SegsOut'`). -/
def SegsAt' (en : ℕ → D) (m : ℕ) (π : HSep M) (e b : ℕ) (c : Config) : Prop :=
  SegsOut' M en m π e b (c.nreg 6807) c.nmem

/-- The registers the parameter programs keep: the driver's, the step's and `9757 … 9899`. -/
def PKeep (r : ℕ) : Prop :=
  (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) ∨ (9757 ≤ r ∧ r ≤ 9899)

variable (M) in
/-- **The specification of the program of FixConservationOnPath with frozen vertices** (see the
module docstring). -/
def FzPSpec (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ)
    (fzP : Stmt) (fzT : MCall M → ℕ → ℕ) (fzR : ℕ → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (hm : 0 < m) (j : ℕ) (πj : SPath (pmap h.1))
    (U f₁ : SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ)
    (Del : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs)))
    (e' : SVert σ (pdarts M (l.piece ∪ r.piece) Hs) → SDart (pdarts M (l.piece ∪ r.piece) Hs))
    (he' : ∀ v, (pmap h.1).tail (e' v) = v) (F1b DFb CPb FFb Sb Wz : ℕ) (c : Config)
    (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem),
    CallOk M S T (.node l r π, Hs, σ) → SegsAt' M en m π e b c →
    (segsP h.1 π.segs h.2)[j]? = some πj → d + fsz m ≤ e → e ≤ b →
    b ≤ F1b → b ≤ DFb → b ≤ CPb ∨ CPb + m ≤ d + 4 + 6 * m → b ≤ FFb →
    F1b + m ≤ Sb → DFb + m ≤ Sb → CPb + m ≤ Sb → FFb + m ≤ Sb →
    (F1b + m ≤ FFb ∨ FFb + m ≤ F1b) → (DFb + m ≤ FFb ∨ FFb + m ≤ DFb) →
    (CPb + m ≤ FFb ∨ FFb + m ≤ CPb) →
    Sb + fzR m ≤ W → Wz < d → MemZ Wz c → WordsBounded W c →
    c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = b + 5 → c.nreg 6800 = j →
    c.nreg 9800 = F1b → c.nreg 9801 = DFb → c.nreg 9802 = CPb → c.nreg 9803 = FFb →
    c.nreg 9804 = Sb →
    (∀ y, 0 ≤ U y ∧ U y ≤ Z) → IsPseudo (pmap h.1) U f₁ →
    (∀ i < m, (c.nmem (CPb + i) : ℤ) = U (layEn _ en m hL.en_mem hm i)) →
    (∀ i < m, (c.nmem (F1b + i) : ℤ) = Z + f₁ (layEn _ en m hL.en_mem hm i)) →
    (∀ i < m, c.nmem (DFb + i) =
      if (pmap h.1).tail (layEn _ en m hL.en_mem hm i) ∈ Del then 1 else 0) →
    ∃ c' t, Exec I W fzP c c' t ∧ t ≤ fzT (.node l r π, Hs, σ) j ∧
      (∀ i < m, (c'.nmem (FFb + i) : ℤ) = Z + fixFrozen (pmap h.1) e' he'
        (Klein.msspPlaneK (pmap h.1)) (frRef _) (negLay gid I (.node l r π, Hs, σ) h.1) U f₁ πj
        Del (layEn _ en m hL.en_mem hm i)) ∧
      (∀ a, a < Sb → (a < FFb ∨ FFb + m ≤ a) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      (∀ r, PKeep r → c'.nreg r = c.nreg r) ∧ c'.output = c.output

variable (M) in
/-- **The specification of the program of the push-back** `pchCall gid x h β ∅` (see the module
docstring). -/
def PbPSpec (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ)
    (pbP : Stmt) (pbT : MCall M → ℕ → ℕ) (pbR : ℕ → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (hm : 0 < m) (j : ℕ)
    (β : SVert σ (pdarts M (l.piece ∪ r.piece) Hs) → ℤ)
    (g' : SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ) (BTb Gb' PBb Sb Wz : ℕ) (c : Config)
    (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem),
    CallOk M S T (.node l r π, Hs, σ) → SegsAt' M en m π e b c → d + fsz m ≤ e → e ≤ b →
    b ≤ BTb → b ≤ Gb' → b ≤ PBb → BTb + m ≤ Sb → Gb' + m ≤ Sb → PBb + m ≤ Sb →
    (BTb + m ≤ PBb ∨ PBb + m ≤ BTb) → (Gb' + m ≤ PBb ∨ PBb + m ≤ Gb') →
    Sb + pbR m ≤ W → Wz < d → MemZ Wz c → WordsBounded W c →
    c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = b + 5 → c.nreg 6800 = j →
    c.nreg 9805 = BTb → c.nreg 9806 = Gb' → c.nreg 9807 = PBb → c.nreg 9808 = Sb →
    (∀ v, 0 ≤ β v) → (∀ y, -(2 * (Z : ℤ)) ≤ g' y ∧ g' y ≤ 2 * Z) →
    (∀ y, -(2 * (Z : ℤ)) ≤ pchCall gid (.node l r π, Hs, σ) h.1 β ∅ g' y ∧
      pchCall gid (.node l r π, Hs, σ) h.1 β ∅ g' y ≤ 2 * Z) →
    (∀ i < m, (c.nmem (BTb + i) : ℤ) = β ((pmap h.1).tail (layEn _ en m hL.en_mem hm i))) →
    (∀ i < m, (c.nmem (Gb' + i) : ℤ) = 2 * Z + g' (layEn _ en m hL.en_mem hm i)) →
    ∃ c' t, Exec I W pbP c c' t ∧ t ≤ pbT (.node l r π, Hs, σ) j ∧
      (∀ i < m, (c'.nmem (PBb + i) : ℤ) =
        2 * Z + pchCall gid (.node l r π, Hs, σ) h.1 β ∅ g' (layEn _ en m hL.en_mem hm i)) ∧
      (∀ a, a < Sb → (a < PBb ∨ PBb + m ≤ a) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      (∀ r, PKeep r → c'.nreg r = c.nreg r) ∧ c'.output = c.output

/-! ### The tail program -/

/-- The registers of `stCallZ` from the tail's registers. -/
def tgA : Stmt :=
  block [.constN 9820 4, .addN 9101 9819 9820, .addN 9101 9101 9818, .addN 9102 9101 9818,
    .copyN 9100 9818, .copyN 9103 9810, .copyN 9104 9811, .copyN 9105 9812, .copyN 9107 9813,
    .copyN 9108 9814, .copyN 9109 9816, .copyN 9110 9815]

/-- `FL` base, the registers of `axL` for `F1 = FL + O − 2Z`. -/
def tgB : Stmt :=
  block [.constN 9820 4, .addN 9821 9819 9820, .constN 9822 6, .mulN 9822 9822 9818,
    .addN 9821 9821 9822, .copyN 9792 9821, .copyN 9793 9814, .copyN 9794 9800,
    .copyN 9795 9816, .copyN 9796 9818]

/-- The registers of `sxL` for `G = FF + 2Z − FL`. -/
def tgC : Stmt := block [.copyN 9792 9803, .copyN 9793 9821, .copyN 9794 9806, .copyN 9795 9816]

/-- The registers of `axL` for `FL := FL + PB − 2Z`. -/
def tgD : Stmt := block [.copyN 9792 9821, .copyN 9793 9807, .copyN 9794 9821, .copyN 9795 9816]

/-- **The tail of `c2sP`** with the parameter programs `fzP`, `pbP`. -/
def c2tP (fzP pbP : Stmt) : Stmt :=
  .seq (.seq tgA (.seq stCallZ (.seq tgB axL)))
    (.seq (.seq fzP (.seq tgC sxL)) (.seq pbP (.seq tgD axL)))

variable {P : Input} {W : ℕ}

theorem tgA_exec (c : Config) (hc : WordsBounded W c) {m d : ℕ}
    (r18 : c.nreg 9818 = m) (r19 : c.nreg 9819 = d) (w : d + 4 + 2 * m ≤ W) :
    ∃ c' k, Exec P W tgA c c' k ∧ k = 12 ∧ c'.nreg 9100 = m ∧ c'.nreg 9101 = d + 4 + m ∧
      c'.nreg 9102 = d + 4 + 2 * m ∧ c'.nreg 9103 = c.nreg 9810 ∧ c'.nreg 9104 = c.nreg 9811 ∧
      c'.nreg 9105 = c.nreg 9812 ∧ c'.nreg 9107 = c.nreg 9813 ∧ c'.nreg 9108 = c.nreg 9814 ∧
      c'.nreg 9109 = c.nreg 9816 ∧ c'.nreg 9110 = c.nreg 9815 ∧
      (∀ r, ¬ (9100 ≤ r ∧ r < 9200) → r ≠ 9820 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tgA
  exec_block
  all_goals try ((try config_simp); (try simp only [r18, r19]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r18, r19, upd_apply]) <;> (try split_ifs) <;> omega

theorem tgB_exec (c : Config) (hc : WordsBounded W c) {m d : ℕ}
    (r18 : c.nreg 9818 = m) (r19 : c.nreg 9819 = d) (w : d + 4 + 6 * m ≤ W) (hm : 0 < m) :
    ∃ c' k, Exec P W tgB c c' k ∧ k = 10 ∧ c'.nreg 9821 = d + 4 + 6 * m ∧
      c'.nreg 9792 = d + 4 + 6 * m ∧ c'.nreg 9793 = c.nreg 9814 ∧ c'.nreg 9794 = c.nreg 9800 ∧
      c'.nreg 9795 = c.nreg 9816 ∧ c'.nreg 9796 = m ∧
      (∀ r, ¬ (9792 ≤ r ∧ r ≤ 9796) → ¬ (9820 ≤ r ∧ r ≤ 9822) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tgB
  exec_block
  all_goals try ((try config_simp); (try simp only [r18, r19]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r18, r19, upd_apply]) <;> (try split_ifs) <;> omega

theorem tgC_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W tgC c c' k ∧ k = 4 ∧ c'.nreg 9792 = c.nreg 9803 ∧
      c'.nreg 9793 = c.nreg 9821 ∧ c'.nreg 9794 = c.nreg 9806 ∧ c'.nreg 9795 = c.nreg 9816 ∧
      (∀ r, ¬ (9792 ≤ r ∧ r ≤ 9795) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tgC
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [upd_apply]); (try split_ifs) <;> omega

theorem tgD_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W tgD c c' k ∧ k = 4 ∧ c'.nreg 9792 = c.nreg 9821 ∧
      c'.nreg 9793 = c.nreg 9807 ∧ c'.nreg 9794 = c.nreg 9821 ∧ c'.nreg 9795 = c.nreg 9816 ∧
      (∀ r, ¬ (9792 ≤ r ∧ r ≤ 9795) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tgD
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [upd_apply]); (try split_ifs) <;> omega

end NcStep

end BKMNW

end PlanarFlow
