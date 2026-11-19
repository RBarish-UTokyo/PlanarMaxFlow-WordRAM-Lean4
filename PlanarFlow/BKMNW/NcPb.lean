module

public import PlanarFlow.BKMNW.NcPar
public import PlanarFlow.BKMNW.NrPch
public import PlanarFlow.BKMNW.NrWFrame

/-!
# The push-back parameter program `pbP` of `c2sP`: specification and glue

**Remark.** `PbPSpec` (`NcPar.lean`) cannot be met by a program built on the
push-back `pchP` (`MfDrv.pchP_exec`), for two reasons:

1. it does not assume that the input `g'` is **antisymmetric**, while `pchP` (and the meaning of
   the push-back, `cancelR` / Kahn's order) needs it (`hg : IsAntisymm g`);
2. it gives no **upper bound on `β`** (only `0 ≤ β`), while `pchP` reads the words `Kd + β`
   (`Kd ≥ (m + 1)·2Z`, the offset of the net outflows): they must fit in `W`.

**`PbPSpec'`** is `PbPSpec` with these two hypotheses added (`IsAntisymm g'`, `β v ≤ m Z`). At
the only use (the tail of `c2sP`, `g' = fixFrozen … − g`, `β = c2sBeta`) both hold (`NcPbC.lean`).
The word room needed by `pchP` (`6 m Z + 6 Z + 1 ≤ W`) is put in the room function: `pbP` meets
`PbPSpec' … (pbRZ Z)` with **`pbRZ Z m = 33 m + 20 + 6 (m Z) + 6 Z`** (for the fixed `Z` of the
specification), see `NcPbS.lean`.

The program (registers `9900 … 9915` for its own values, the loop registers of `dvL`
(`9260 … 9270`) and `cstL` (`9250 … 9255`), `pchP`'s registers; none of `PKeep` but `3004`, which
`pchP` restores):

* `pbS1 = pbG0 ; dvL ; pbG1 ; dvL ; pbG2 ; dvL ; pbG3 ; cstL ; pbG4`: save the frame's flow array
  `FL` to `SV = Sb + 32 m + 1`; copy `G` into `FL`; `BT' = Kd + BT` at `Sb + 30 m + 1`
  (`Kd = 2Z·m + 2Z`); `FR = 0` at `Sb + 31 m + 1`; the frame's header cell `d + 3` (the offset
  `Z`) set to `2Z`; `pchP`'s registers (`A = Sb`);
* `pchP` (the frame now reads as a frame at offset `2Z` holding `g'`);
* `pbS3 = pbG5 ; dvL ; pbG6 ; dvL ; pbG7`: `PB := FL`, `FL := SV`, the header cell back to `Z`.
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
/-- **The specification of the push-back program** `pchCall gid x h β ∅` (`PbPSpec` with an
antisymmetric input `g'` and `β ≤ m Z`; see the module docstring). -/
def PbPSpec' (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ)
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
    (∀ v, 0 ≤ β v ∧ β v ≤ (m : ℤ) * Z) → (pmap h.1).IsAntisymm g' →
    (∀ y, -(2 * (Z : ℤ)) ≤ g' y ∧ g' y ≤ 2 * Z) →
    (∀ y, -(2 * (Z : ℤ)) ≤ pchCall gid (.node l r π, Hs, σ) h.1 β ∅ g' y ∧
      pchCall gid (.node l r π, Hs, σ) h.1 β ∅ g' y ≤ 2 * Z) →
    (∀ i < m, (c.nmem (BTb + i) : ℤ) = β ((pmap h.1).tail (layEn _ en m hL.en_mem hm i))) →
    (∀ i < m, (c.nmem (Gb' + i) : ℤ) = 2 * Z + g' (layEn _ en m hL.en_mem hm i)) →
    ∃ c' t, Exec I W pbP c c' t ∧ t ≤ pbT (.node l r π, Hs, σ) j ∧
      (∀ i < m, (c'.nmem (PBb + i) : ℤ) =
        2 * Z + pchCall gid (.node l r π, Hs, σ) h.1 β ∅ g' (layEn _ en m hL.en_mem hm i)) ∧
      (∀ a, a < Sb → (a < PBb ∨ PBb + m ≤ a) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      (∀ r, PKeep r → c'.nreg r = c.nreg r) ∧ c'.output = c.output

variable (M) in
/-- **The specification of the program of FixConservationOnPath with frozen vertices** with a
zero area of at least `wzz m Z` words (`FzPSpec` + `wzz m Z ≤ Wz`; a program calling the
MSSP program needs a zero area). -/
def FzPSpec' (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ)
    (wzz : ℕ → ℕ → ℕ) (fzP : Stmt) (fzT : MCall M → ℕ → ℕ) (fzR : ℕ → ℕ) : Prop :=
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
    Sb + fzR m ≤ W → Wz < d → wzz m Z ≤ Wz → MemZ Wz c → WordsBounded W c →
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

/-- `FzPSpec` gives `FzPSpec'` for every zero-area function. -/
theorem FzPSpec.toP {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {I : Input} {W : ℕ}
    {fzP : Stmt} {fzT : MCall M → ℕ → ℕ} {fzR : ℕ → ℕ} (h : FzPSpec M gid u S T Z I W fzP fzT fzR)
    (wzz : ℕ → ℕ → ℕ) : FzPSpec' M gid u S T Z I W wzz fzP fzT fzR :=
  fun l r π Hs σ hs d e b m en hm j πj U f₁ Del e' he' F1b DFb CPb FFb Sb Wz c hL a1 a2 a3 a4 a5
    a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 _ =>
  h l r π Hs σ hs d e b m en hm j πj U f₁ Del e' he' F1b DFb CPb FFb Sb Wz c hL a1 a2 a3 a4 a5 a6
    a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18

/-! ### The glue blocks -/

/-- The values of `pbP` and the registers of `dvL` for `SV := FL`. -/
def pbG0 : Stmt :=
  block [.copyN 9900 3004, .loadN 9901 9900, .constN 9911 3, .addN 9912 9900 9911,
    .loadN 9902 9912, .addN 9903 9902 9902, .copyN 9904 9808,
    .constN 9911 30, .mulN 9905 9911 9901, .addN 9905 9905 9904, .constN 9911 1,
    .addN 9905 9905 9911, .addN 9913 9905 9901, .addN 9914 9913 9901,
    .constN 9911 6, .mulN 9906 9911 9901, .addN 9906 9906 9900, .constN 9911 4,
    .addN 9906 9906 9911, .mulN 9907 9903 9901, .addN 9907 9907 9903,
    .copyN 9908 9807, .copyN 9909 9806, .copyN 9910 9805,
    .copyN 9261 9901, .copyN 9262 9906, .copyN 9263 9906, .copyN 9264 9914, .constN 9265 0,
    .constN 9266 0]

/-- The registers of `dvL` for `FL := G`. -/
def pbG1 : Stmt :=
  block [.copyN 9261 9901, .copyN 9262 9909, .copyN 9263 9909, .copyN 9264 9906, .constN 9265 0,
    .constN 9266 0]

/-- The registers of `dvL` for `BT' := Kd + BT`. -/
def pbG2 : Stmt :=
  block [.copyN 9261 9901, .copyN 9262 9910, .copyN 9263 9910, .copyN 9264 9905,
    .copyN 9265 9907, .constN 9266 0]

/-- The registers of `cstL` for `FR := 0`. -/
def pbG3 : Stmt := block [.copyN 9251 9901, .copyN 9252 9913, .constN 9253 0]

/-- The header cell `d + 3 := 2Z` and the registers of `pchP`. -/
def pbG4 : Stmt :=
  block [.storeN 9912 9903, .copyN 9200 9904, .copyN 9201 9905, .copyN 9202 9913,
    .copyN 9203 9907]

/-- The registers of `dvL` for `PB := FL`. -/
def pbG5 : Stmt :=
  block [.copyN 9261 9901, .copyN 9262 9906, .copyN 9263 9906, .copyN 9264 9908, .constN 9265 0,
    .constN 9266 0]

/-- The registers of `dvL` for `FL := SV`. -/
def pbG6 : Stmt :=
  block [.copyN 9261 9901, .copyN 9262 9914, .copyN 9263 9914, .copyN 9264 9906, .constN 9265 0,
    .constN 9266 0]

/-- The header cell back: `d + 3 := Z`. -/
def pbG7 : Stmt := block [.storeN 9912 9902]

/-- The first part of the set-up: `SV := FL`, `FL := G`. -/
def pbS1v : Stmt := .seq dvL (.seq pbG1 dvL)

/-- The second part of the set-up: `BT' := Kd + BT`, `FR := 0`, `d + 3 := 2Z`. -/
def pbS1u : Stmt := .seq pbG2 (.seq dvL (.seq pbG3 (.seq cstL pbG4)))

/-- The set-up after `pbG0`. -/
def pbS1t : Stmt := .seq pbS1v pbS1u

/-- **The set-up before `pchP`** (`pbG0` then `pbS1t`). -/
def pbS1 : Stmt := .seq pbG0 pbS1t

/-- **The copy-out after `pchP`.** -/
def pbS3 : Stmt := .seq pbG5 (.seq dvL (.seq pbG6 (.seq dvL pbG7)))

/-- **The push-back parameter program of `c2sP`.** -/
def pbP : Stmt := .seq pbS1 (.seq pchP pbS3)

theorem pbP_natOnly : Klein.natOnly pbP = true := by kernel_rfl

theorem pbP_noEmit : Stmt.noEmit pbP = true := by decide +kernel

/-- The destinations of `pbP` lie outside `PKeep`, except `3004` (restored by `pchP`). -/
theorem pbP_dests : (Stmt.nDests pbP).all (fun x => decide (x = 3004 ∨ x < 3000 ∨
    (3012 < x ∧ x < 6800) ∨ (6819 < x ∧ x < 9757) ∨ 9899 < x)) = true := by decide +kernel

/-- The destinations of `pbS1` and `pbS3`: `9200 … 9203`, `9250 … 9270`, `9900 … 9915`. -/
theorem pbS1_dests : (Stmt.nDests pbS1).all (fun x => decide ((9200 ≤ x ∧ x ≤ 9203) ∨
    (9250 ≤ x ∧ x ≤ 9270) ∨ (9900 ≤ x ∧ x ≤ 9915))) = true := by decide +kernel

theorem pbS1t_dests : (Stmt.nDests pbS1t).all (fun x => decide ((9200 ≤ x ∧ x ≤ 9203) ∨
    (9250 ≤ x ∧ x ≤ 9270))) = true := by decide +kernel

theorem pbG1_dests : (Stmt.nDests pbG1).all (fun x => decide (9261 ≤ x ∧ x ≤ 9266)) = true := by
  decide +kernel

theorem pbG2_dests : (Stmt.nDests pbG2).all (fun x => decide (9261 ≤ x ∧ x ≤ 9266)) = true := by
  decide +kernel

theorem pbG3_dests : (Stmt.nDests pbG3).all (fun x => decide (9251 ≤ x ∧ x ≤ 9253)) = true := by
  decide +kernel

theorem pbG4_dests : (Stmt.nDests pbG4).all (fun x => decide (9200 ≤ x ∧ x ≤ 9203)) = true := by
  decide +kernel

theorem pbG5_dests : (Stmt.nDests pbG5).all (fun x => decide (9261 ≤ x ∧ x ≤ 9266)) = true := by
  decide +kernel

theorem pbG6_dests : (Stmt.nDests pbG6).all (fun x => decide (9261 ≤ x ∧ x ≤ 9266)) = true := by
  decide +kernel

theorem pbG7_dests : (Stmt.nDests pbG7).all (fun x => decide (9261 ≤ x ∧ x ≤ 9266)) = true := by
  decide +kernel

theorem pbS3_dests : (Stmt.nDests pbS3).all (fun x => decide ((9250 ≤ x ∧ x ≤ 9270))) = true := by
  decide +kernel

/-- A run keeps the registers its statement never writes (destination list checked). -/
theorem keepW_of_all {P : Input} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) {p : ℕ → Prop} [DecidablePred p]
    (hs : (Stmt.nDests s).all (fun x => decide (p x)) = true) :
    ∀ r, ¬ p r → c'.nreg r = c.nreg r := by
  intro r hr
  refine Exec.nreg_keepW h (nWrites_eq_false_of _ fun hm => ?_)
  have := List.all_eq_true.1 hs r hm
  simp only [decide_eq_true_eq] at this
  exact hr this

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1000000 in
theorem pbG0_exec (c : Config) (hc : WordsBounded W c) {d m Z Sb PBb Gb BTb : ℕ}
    (r04 : c.nreg 3004 = d) (hm : c.nmem d = m) (hZ : c.nmem (d + 3) = Z)
    (r05 : c.nreg 9805 = BTb) (r06 : c.nreg 9806 = Gb) (r07 : c.nreg 9807 = PBb)
    (r08 : c.nreg 9808 = Sb) (w1 : Sb + 33 * m + 2 ≤ W) (w2 : d + 4 + 6 * m ≤ W)
    (w3 : (Z + Z) * m + (Z + Z) ≤ W) (w4 : 30 ≤ W) :
    ∃ c' k, Exec P W pbG0 c c' k ∧ k = 30 ∧ c'.nreg 9900 = d ∧ c'.nreg 9901 = m ∧
      c'.nreg 9902 = Z ∧ c'.nreg 9903 = Z + Z ∧ c'.nreg 9904 = Sb ∧
      c'.nreg 9905 = 30 * m + Sb + 1 ∧ c'.nreg 9913 = 30 * m + Sb + 1 + m ∧
      c'.nreg 9914 = 30 * m + Sb + 1 + m + m ∧ c'.nreg 9906 = 6 * m + d + 4 ∧
      c'.nreg 9907 = (Z + Z) * m + (Z + Z) ∧ c'.nreg 9908 = PBb ∧ c'.nreg 9909 = Gb ∧
      c'.nreg 9910 = BTb ∧ c'.nreg 9912 = d + 3 ∧ c'.nreg 9261 = m ∧
      c'.nreg 9262 = 6 * m + d + 4 ∧ c'.nreg 9263 = 6 * m + d + 4 ∧
      c'.nreg 9264 = 30 * m + Sb + 1 + m + m ∧ c'.nreg 9265 = 0 ∧ c'.nreg 9266 = 0 ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have v1 : d + 3 ≤ W := by omega
  have v2 : Z + Z ≤ W := by have := hc.2 (d + 3); rw [hZ] at this; omega
  unfold pbG0
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, r05, r06, r07, r08, hm, hZ]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r04, r05, r06, r07, r08, hm, hZ])

theorem pbG1_exec (c : Config) (hc : WordsBounded W c) {m Gb FL : ℕ}
    (r01 : c.nreg 9901 = m) (r09 : c.nreg 9909 = Gb) (r06 : c.nreg 9906 = FL) :
    ∃ c' k, Exec P W pbG1 c c' k ∧ k = 6 ∧ c'.nreg 9261 = m ∧ c'.nreg 9262 = Gb ∧
      c'.nreg 9263 = Gb ∧ c'.nreg 9264 = FL ∧ c'.nreg 9265 = 0 ∧ c'.nreg 9266 = 0 ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pbG1
  exec_block
  all_goals try ((try config_simp); omega)

theorem pbG2_exec (c : Config) (hc : WordsBounded W c) {m BTb BT' Kd : ℕ}
    (r01 : c.nreg 9901 = m) (r10 : c.nreg 9910 = BTb) (r05 : c.nreg 9905 = BT')
    (r07 : c.nreg 9907 = Kd) :
    ∃ c' k, Exec P W pbG2 c c' k ∧ k = 6 ∧ c'.nreg 9261 = m ∧ c'.nreg 9262 = BTb ∧
      c'.nreg 9263 = BTb ∧ c'.nreg 9264 = BT' ∧ c'.nreg 9265 = Kd ∧ c'.nreg 9266 = 0 ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pbG2
  exec_block
  all_goals try ((try config_simp); omega)

theorem pbG3_exec (c : Config) (hc : WordsBounded W c) {m FR : ℕ}
    (r01 : c.nreg 9901 = m) (r13 : c.nreg 9913 = FR) :
    ∃ c' k, Exec P W pbG3 c c' k ∧ k = 3 ∧ c'.nreg 9251 = m ∧ c'.nreg 9252 = FR ∧
      c'.nreg 9253 = 0 ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pbG3
  exec_block
  all_goals try ((try config_simp); omega)

theorem pbG4_exec (c : Config) (hc : WordsBounded W c) {a v A BT' FR Kd : ℕ}
    (r12 : c.nreg 9912 = a) (r03 : c.nreg 9903 = v) (r04 : c.nreg 9904 = A)
    (r05 : c.nreg 9905 = BT') (r13 : c.nreg 9913 = FR) (r07 : c.nreg 9907 = Kd) :
    ∃ c' k, Exec P W pbG4 c c' k ∧ k = 5 ∧ c'.nreg 9200 = A ∧ c'.nreg 9201 = BT' ∧
      c'.nreg 9202 = FR ∧ c'.nreg 9203 = Kd ∧ c'.nmem = upd c.nmem a v ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ha : a ≤ W := by rw [← r12]; exact hc.1 _
  unfold pbG4
  exec_block
  all_goals try ((try config_simp); (try simp only [r12, r03]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r12, r03, r04, r05, r13, r07])

theorem pbG5_exec (c : Config) (hc : WordsBounded W c) {m FL PBb : ℕ}
    (r01 : c.nreg 9901 = m) (r06 : c.nreg 9906 = FL) (r08 : c.nreg 9908 = PBb) :
    ∃ c' k, Exec P W pbG5 c c' k ∧ k = 6 ∧ c'.nreg 9261 = m ∧ c'.nreg 9262 = FL ∧
      c'.nreg 9263 = FL ∧ c'.nreg 9264 = PBb ∧ c'.nreg 9265 = 0 ∧ c'.nreg 9266 = 0 ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pbG5
  exec_block
  all_goals try ((try config_simp); omega)

theorem pbG6_exec (c : Config) (hc : WordsBounded W c) {m SV FL : ℕ}
    (r01 : c.nreg 9901 = m) (r14 : c.nreg 9914 = SV) (r06 : c.nreg 9906 = FL) :
    ∃ c' k, Exec P W pbG6 c c' k ∧ k = 6 ∧ c'.nreg 9261 = m ∧ c'.nreg 9262 = SV ∧
      c'.nreg 9263 = SV ∧ c'.nreg 9264 = FL ∧ c'.nreg 9265 = 0 ∧ c'.nreg 9266 = 0 ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pbG6
  exec_block
  all_goals try ((try config_simp); omega)

theorem pbG7_exec (c : Config) (hc : WordsBounded W c) {a v : ℕ}
    (r12 : c.nreg 9912 = a) (r02 : c.nreg 9902 = v) :
    ∃ c' k, Exec P W pbG7 c c' k ∧ k = 1 ∧ c'.nmem = upd c.nmem a v ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ha : a ≤ W := by rw [← r12]; exact hc.1 _
  unfold pbG7
  exec_block
  all_goals try ((try config_simp); (try simp only [r12, r02]); omega)
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r12, r02])

/-- `dvL` as a copy (`Kd = 0`, `Z = 0`): `OUT[i] := X[i]`. -/
theorem cpyL_exec (c : Config) (hc : WordsBounded W c) {n Xb OUTb : ℕ}
    (r1 : c.nreg 9261 = n) (r2 : c.nreg 9262 = Xb) (r3 : c.nreg 9263 = Xb)
    (r4 : c.nreg 9264 = OUTb) (r5 : c.nreg 9265 = 0) (r6 : c.nreg 9266 = 0)
    (dS : Xb + n ≤ OUTb ∨ OUTb + n ≤ Xb) (w1 : Xb + n ≤ W) (w3 : OUTb + n ≤ W)
    (w6 : n + 1 ≤ W) :
    ∃ c' t, Exec P W dvL c c' t ∧ t ≤ 12 * n + 4 ∧
      (∀ i < n, c'.nmem (OUTb + i) = c.nmem (Xb + i)) ∧
      (∀ a, (a < OUTb ∨ OUTb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 9260 ∨ 9270 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, v, o, f, rr, rm, oo⟩ := dvL_exec (P := P) c hc r1 r2 r3 r4 r5 r6 dS dS
    w1 w1 w3 w6 (fun i hi => by have := hc.2 (Xb + i); omega) (fun i hi => by simp)
  refine ⟨c', t, ex, ht, fun i hi => by rw [v i hi]; simp, o, f, rr, rm, oo⟩

end NcStep

end BKMNW

end PlanarFlow
