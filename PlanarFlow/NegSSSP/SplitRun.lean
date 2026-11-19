module

public import PlanarFlow.NegSSSP.SplitRunA
public import PlanarFlow.NegSSSP.PieceEnc
public import PlanarFlow.NegSSSP.GroupProg
public import PlanarSeparator.Machine.SubCallR

/-!
# The split of a piece as one program

The split of the machine (`PlanarFlow.NegSSSP.splitM`) of a piece `Pc`, from the plain encoding
of the piece carrying its own rotation (`PEnc`), as one program:

`splitProg = spSetup ; compProg ; if no large component then grpSet ; grpProg else bigProg`,

`bigProg = encSet ; encProg ; copy of the encoding ; copy of the flags ; registers < 700 cleared ;
sepRun prog10 ; joinSet ; joinProg ; fw1Set ; faceWalk ; fw2Set ; faceWalk`.

The layout (`spSetup`, `k` half-edges, base `B₀`): the separator's scratch and output up to
`W₁ = B₀ + 25 k + 2` (the encoding of the piece map at `B₀`, the marks at `B₀ + 22 m'`), the index
array of `encProg` at `X = W₁ + 1`, the copy of the encoding at `Y = B₀ + 28 k + 3`, the copy of
the flags at `B₀ + 33 k + 3`, the scratch of `compProg` at `B₀ + 34 k + 3`, the sides at
`Ob = B₀ + 41 k + 4`, the scratch of the two face walks at `T₁ = B₀ + 42 k + 4` and
`T₂ = B₀ + 54 k + 7`, up to `B₀ + 66 k + 10`. The separator run has no frame of its own; it is
run lifted (`sep_run_lift`, by `Exec.lift_trunc`) so that everything above `W₁` and the registers
from `700` on survive it; the face walks read the copy of the encoding at `Y`.

* `bigProg_spec`: **the large-component case**: the cut `A₀` read off the marks meets `CutOK`,
  the sides at `Ob` are those of `cutPair Pc K A₀`, and the positions on the face of both parts
  (`PosInst`, the hypothesis `hpos` of `cornerProg_face`) are at `T₁ + 2 (nV + nF)` and
  `T₂ + 2 (nV + nF)`, within `bigT k = (1746 k + 156) (log₂ k + 3) + 17112 k + 156 √(12 k) + 2900`
  steps.
* `splitProg_splitM`: **the whole split**: the sides at `Ob` are those of `splitM N ord cut Pc`
  for `ord Pc = [δ 0, …, δ (m - 1)]` (any `cut` without a large component; in the large case any
  `cut` with `cut K = A₀`, `CutOK N K A₀`), with the positions on the face of both parts in the
  large case, within `splitT k = bigT k + 125 k + 64` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### The programs -/

/-- The layout (`r861 = k`, `r950 = B₀`): `r951 = X = B₀ + 25 k + 3` (the index array),
`r952 = Y = B₀ + 28 k + 3` (the copy of the encoding), `r953 = Fh = B₀ + 33 k + 3` (the copy of the flags),
`r954 = B = B₀ + 34 k + 3` (the scratch of `compProg`), `r955 = Ob = B₀ + 41 k + 4` (the sides),
`r956 = T₁ = B₀ + 42 k + 4`, `r957 = T₂ = B₀ + 54 k + 7` (the scratch of the two face walks);
`r864 = B` for `compProg`. -/
def spSetup : Stmt := block [.constN 970 25, .mulN 971 970 861, .addN 971 971 950,
  .constN 970 3, .addN 951 971 970, .constN 970 3, .mulN 971 970 861, .addN 952 951 971,
  .constN 970 5, .mulN 971 970 861, .addN 953 952 971, .addN 954 953 861,
  .constN 970 7, .mulN 971 970 861, .addN 955 954 971, .addN 955 955 10, .addN 956 955 861,
  .constN 970 12, .mulN 971 970 861, .addN 957 956 971, .constN 970 3, .addN 957 957 970,
  .copyN 864 954]

/-- The registers of `encProg`. -/
def encSet : Stmt := block [.copyN 910 861, .copyN 911 860, .copyN 912 862, .copyN 913 863,
  .copyN 914 865, .copyN 915 950, .copyN 916 951]

/-- The copy of the encoding (`5 m'` words from `B₀` to `Y`). -/
def cpySet : Stmt := block [.constN 307 1, .constN 970 5, .mulN 338 970 390, .copyN 339 950,
  .copyN 340 952]

/-- The copy of the flags (`m` words from `bF = r865` to `Fh`). -/
def cpfSet : Stmt := block [.constN 307 1, .copyN 338 860, .copyN 339 865, .copyN 340 953]

/-- Saving `r390 … r392`. -/
def saveSet : Stmt := block [.copyN 960 390, .copyN 961 391, .copyN 962 392]

/-- Restoring `r390 … r393`. -/
def spRestSet : Stmt := block [.copyN 390 960, .copyN 391 961, .copyN 392 962, .copyN 393 950]

/-- The registers of `joinProg`. -/
def joinSet : Stmt := block [.constN 10 1, .copyN 780 860, .copyN 781 953, .copyN 782 951,
  .copyN 783 955, .constN 970 22, .mulN 971 970 960, .addN 792 950 971]

/-- The registers of the first face walk (side `1`). -/
def fw1Set : Stmt := block [.copyN 800 960, .copyN 801 952, .addN 802 801 960,
  .addN 803 802 960, .addN 804 803 960, .addN 805 804 960, .copyN 806 792, .copyN 807 961,
  .copyN 808 962, .constN 809 1, .copyN 810 956]

/-- The registers of the second face walk (side `0`). -/
def fw2Set : Stmt := block [.constN 809 0, .copyN 810 957]

/-- The registers of `grpProg`. -/
def grpSet : Stmt := block [.copyN 880 860, .constN 970 4, .mulN 971 970 861,
  .addN 881 954 971, .constN 970 6, .mulN 971 970 861, .addN 882 954 971, .copyN 883 956,
  .copyN 884 955, .addN 885 861 10]

/-- **The large-component case**: the encoding of the piece map of the component, its copy above
the separator's word bound, the separator run (registers `< 700` cleared first), the join of the
sides, the walks of both sides of the cycle. -/
def bigProg : Stmt :=
  .seq (.seq encSet encProg) <| .seq (.seq cpySet PlanarSeparator.MillerProg.cpyN) <|
  .seq (.seq cpfSet PlanarSeparator.MillerProg.cpyN) <|
  .seq (.seq saveSet (.seq (WordRAM.Machine.zeroRegs 700) spRestSet)) <|
  .seq (PlanarSeparator.MillerProg.sepRun PlanarSeparator.MillerProg.prog10) <|
  .seq (.seq joinSet joinProg) <| .seq (.seq fw1Set faceWalk) (.seq fw2Set faceWalk)

/-- **The small-component case**: the grouping. -/
def smallProg : Stmt := .seq grpSet grpProg

/-- **The split of a piece** (`r10 = 1`, `r860 = m`, `r861 = k`, `r862 = bα`, `r863 = bσ`,
`r865 = bF`, `r950 = B₀`). -/
def splitProg : Stmt := .seq spSetup (.seq compProg (.ifLtN 856 10 smallProg bigProg))

/-! ### The blocks -/

theorem spSetup_exec {k B₀ : ℕ} (c : Config) (hc : WordsBounded W c) (r10 : c.nreg 10 = 1)
    (r861 : c.nreg 861 = k) (r950 : c.nreg 950 = B₀) (hW : B₀ + 66 * k + 35 ≤ W) :
    ∃ c' t, Exec P W spSetup c c' t ∧ t ≤ 24 ∧ c'.nreg 951 = B₀ + 25 * k + 3 ∧
      c'.nreg 952 = B₀ + 28 * k + 3 ∧ c'.nreg 953 = B₀ + 33 * k + 3 ∧
      c'.nreg 954 = B₀ + 34 * k + 3 ∧ c'.nreg 955 = B₀ + 41 * k + 4 ∧
      c'.nreg 956 = B₀ + 42 * k + 4 ∧ c'.nreg 957 = B₀ + 54 * k + 7 ∧
      c'.nreg 864 = B₀ + 34 * k + 3 ∧
      (∀ r, r ≠ 864 → (r < 951 ∨ 971 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold spSetup
  exec_block
  all_goals try ((try config_simp); (try simp only [r10, r861, r950]) <;> omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try ((try simp only [r10, r861, r950]) <;> omega)
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem encSet_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W encSet c c' t ∧ t ≤ 7 ∧ c'.nreg 910 = c.nreg 861 ∧
      c'.nreg 911 = c.nreg 860 ∧ c'.nreg 912 = c.nreg 862 ∧ c'.nreg 913 = c.nreg 863 ∧
      c'.nreg 914 = c.nreg 865 ∧ c'.nreg 915 = c.nreg 950 ∧ c'.nreg 916 = c.nreg 951 ∧
      (∀ r, (r < 910 ∨ 916 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold encSet
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try omega
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem cpySet_exec {m' : ℕ} (c : Config) (hc : WordsBounded W c) (r390 : c.nreg 390 = m')
    (hW : 5 * m' + 5 ≤ W) :
    ∃ c' t, Exec P W cpySet c c' t ∧ t ≤ 5 ∧ c'.nreg 307 = 1 ∧ c'.nreg 338 = 5 * m' ∧
      c'.nreg 339 = c.nreg 950 ∧ c'.nreg 340 = c.nreg 952 ∧
      (∀ r, r ≠ 307 → r ≠ 338 → r ≠ 339 → r ≠ 340 → r ≠ 970 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cpySet
  exec_block
  all_goals try ((try config_simp); (try simp only [r390]) <;> omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try ((try simp only [r390]) <;> omega)
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem saveSet_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W saveSet c c' t ∧ t ≤ 3 ∧ c'.nreg 960 = c.nreg 390 ∧
      c'.nreg 961 = c.nreg 391 ∧ c'.nreg 962 = c.nreg 392 ∧
      (∀ r, r ≠ 960 → r ≠ 961 → r ≠ 962 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold saveSet
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨by omega, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try omega
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem spRestSet_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W spRestSet c c' t ∧ t ≤ 4 ∧ c'.nreg 390 = c.nreg 960 ∧
      c'.nreg 391 = c.nreg 961 ∧ c'.nreg 392 = c.nreg 962 ∧ c'.nreg 393 = c.nreg 950 ∧
      (∀ r, (r < 390 ∨ 393 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold spRestSet
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try omega
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem joinSet_exec {B₀ m' : ℕ} (c : Config) (hc : WordsBounded W c) (r950 : c.nreg 950 = B₀)
    (r960 : c.nreg 960 = m') (hW : B₀ + 22 * m' + 22 ≤ W) :
    ∃ c' t, Exec P W joinSet c c' t ∧ t ≤ 8 ∧ c'.nreg 10 = 1 ∧ c'.nreg 780 = c.nreg 860 ∧
      c'.nreg 781 = c.nreg 953 ∧ c'.nreg 782 = c.nreg 951 ∧ c'.nreg 783 = c.nreg 955 ∧
      c'.nreg 792 = B₀ + 22 * m' ∧
      (∀ r, r ≠ 10 → (r < 780 ∨ 783 < r) → r ≠ 792 → r ≠ 970 → r ≠ 971 →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold joinSet
  exec_block
  all_goals try ((try config_simp); (try simp only [r950, r960]) <;> omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try ((try simp only [r950, r960]) <;> omega)
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem fw1Set_exec {Y m' : ℕ} (c : Config) (hc : WordsBounded W c) (r952 : c.nreg 952 = Y)
    (r960 : c.nreg 960 = m') (hW : Y + 4 * m' + 1 ≤ W) :
    ∃ c' t, Exec P W fw1Set c c' t ∧ t ≤ 11 ∧ c'.nreg 800 = m' ∧ c'.nreg 801 = Y ∧
      c'.nreg 802 = Y + m' ∧ c'.nreg 803 = Y + 2 * m' ∧ c'.nreg 804 = Y + 3 * m' ∧
      c'.nreg 805 = Y + 4 * m' ∧ c'.nreg 806 = c.nreg 792 ∧ c'.nreg 807 = c.nreg 961 ∧
      c'.nreg 808 = c.nreg 962 ∧ c'.nreg 809 = 1 ∧ c'.nreg 810 = c.nreg 956 ∧
      (∀ r, (r < 800 ∨ 810 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fw1Set
  exec_block
  all_goals try ((try config_simp); (try simp only [r952, r960]) <;> omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl,
    rfl⟩
  all_goals config_simp
  all_goals try ((try simp only [r952, r960]) <;> omega)
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem fw2Set_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W fw2Set c c' t ∧ t ≤ 2 ∧ c'.nreg 809 = 0 ∧ c'.nreg 810 = c.nreg 957 ∧
      (∀ r, r ≠ 809 → r ≠ 810 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fw2Set
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨by omega, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try omega
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem grpSet_exec {k B : ℕ} (c : Config) (hc : WordsBounded W c) (r10 : c.nreg 10 = 1)
    (r861 : c.nreg 861 = k) (r954 : c.nreg 954 = B) (hW : B + 6 * k + 7 ≤ W) :
    ∃ c' t, Exec P W grpSet c c' t ∧ t ≤ 10 ∧ c'.nreg 880 = c.nreg 860 ∧
      c'.nreg 881 = B + 4 * k ∧ c'.nreg 882 = B + 6 * k ∧ c'.nreg 883 = c.nreg 956 ∧
      c'.nreg 884 = c.nreg 955 ∧ c'.nreg 885 = k + 1 ∧
      (∀ r, (r < 880 ∨ 885 < r) → r ≠ 970 → r ≠ 971 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold grpSet
  exec_block
  all_goals try ((try config_simp); (try simp only [r10, r861, r954]) <;> omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try ((try simp only [r10, r861, r954]) <;> omega)
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-! ### The stages -/

theorem natS_cpyN : natS PlanarSeparator.MillerProg.cpyN = true := by decide

/-- The copy of `5 m'` words from `B₀` to `Y`. -/
theorem cpyStage_exec {m' B₀ Y : ℕ} (c : Config) (hc : WordsBounded W c)
    (r390 : c.nreg 390 = m') (r950 : c.nreg 950 = B₀) (r952 : c.nreg 952 = Y)
    (hd : B₀ + 5 * m' ≤ Y) (hW : Y + 5 * m' + 5 ≤ W) :
    ∃ c' t, Exec P W (.seq cpySet PlanarSeparator.MillerProg.cpyN) c c' t ∧ t ≤ 35 * m' + 8 ∧
      (∀ x < 5 * m', c'.nmem (Y + x) = c.nmem (B₀ + x)) ∧
      (∀ a, a < Y ∨ Y + 5 * m' ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 307 → r ≠ 337 → r ≠ 338 → r ≠ 339 → r ≠ 340 → r ≠ 341 → r ≠ 342 → r ≠ 970 →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g307, g338, g339, g340, fr₁, fm₁, frr₁, frm₁, fo₁⟩ :=
    cpySet_exec (P := P) c hc r390 (by omega)
  rw [r950] at g339; rw [r952] at g340
  obtain ⟨c₂, t₂, e₂, ht₂, cp, fr₂, fm₂, fo₂⟩ :=
    PlanarSeparator.MillerProg.cpyN_exec (P := P) (N := 5 * m') (bs := B₀) (bd := Y)
      (by omega) ⟨by omega, by omega⟩ c₁ e₁.wb_right g307 g338 g339 g340
  obtain ⟨rr, rm⟩ := Exec.natS_frame e₂ natS_cpyN
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, fun x hx => by rw [cp x hx, fm₁],
    fun a ha => by rw [fm₂ a ha, fm₁], fun r h1 h2 h3 h4 h5 h6 h7 h8 => ?_, by rw [rr, frr₁],
    by rw [rm, frm₁], by rw [fo₂, fo₁]⟩
  rw [fr₂ r h2 h6 h7, fr₁ r h1 h3 h4 h5 h8]

theorem cpfSet_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' t, Exec P W cpfSet c c' t ∧ t ≤ 4 ∧ c'.nreg 307 = 1 ∧ c'.nreg 338 = c.nreg 860 ∧
      c'.nreg 339 = c.nreg 865 ∧ c'.nreg 340 = c.nreg 953 ∧
      (∀ r, r ≠ 307 → r ≠ 338 → r ≠ 339 → r ≠ 340 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cpfSet
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try omega
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- The copy of the `m` flags from `bF` to `Fh`. -/
theorem cpfStage_exec {m bF Fh : ℕ} (c : Config) (hc : WordsBounded W c)
    (r860 : c.nreg 860 = m) (r865 : c.nreg 865 = bF) (r953 : c.nreg 953 = Fh)
    (hd : bF + m ≤ Fh) (hW : Fh + m + 1 ≤ W) :
    ∃ c' t, Exec P W (.seq cpfSet PlanarSeparator.MillerProg.cpyN) c c' t ∧ t ≤ 7 * m + 7 ∧
      (∀ x < m, c'.nmem (Fh + x) = c.nmem (bF + x)) ∧
      (∀ a, a < Fh ∨ Fh + m ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 307 → r ≠ 337 → r ≠ 338 → r ≠ 339 → r ≠ 340 → r ≠ 341 → r ≠ 342 →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g307, g338, g339, g340, fr₁, fm₁, frr₁, frm₁, fo₁⟩ :=
    cpfSet_exec (P := P) c hc (by omega)
  rw [r860] at g338; rw [r865] at g339; rw [r953] at g340
  obtain ⟨c₂, t₂, e₂, ht₂, cp, fr₂, fm₂, fo₂⟩ :=
    PlanarSeparator.MillerProg.cpyN_exec (P := P) (N := m) (bs := bF) (bd := Fh)
      (by omega) ⟨by omega, by omega⟩ c₁ e₁.wb_right g307 g338 g339 g340
  obtain ⟨rr, rm⟩ := Exec.natS_frame e₂ natS_cpyN
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, fun x hx => by rw [cp x hx, fm₁],
    fun a ha => by rw [fm₂ a ha, fm₁], fun r h1 h2 h3 h4 h5 h6 h7 => ?_, by rw [rr, frr₁],
    by rw [rm, frm₁], by rw [fo₂, fo₁]⟩
  rw [fr₂ r h2 h6 h7, fr₁ r h1 h3 h4 h5]

/-- The registers `< 700` cleared, `r390 … r393` kept (`r393 := r950`). -/
theorem zeroStage_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (.seq saveSet (.seq (WordRAM.Machine.zeroRegs 700) spRestSet)) c c' t ∧
      t ≤ 707 ∧ c'.nreg 390 = c.nreg 390 ∧ c'.nreg 391 = c.nreg 391 ∧
      c'.nreg 392 = c.nreg 392 ∧ c'.nreg 393 = c.nreg 950 ∧
      (∀ r < 700, (r < 390 ∨ 393 < r) → c'.nreg r = 0) ∧
      c'.nreg 960 = c.nreg 390 ∧ c'.nreg 961 = c.nreg 391 ∧ c'.nreg 962 = c.nreg 392 ∧
      (∀ r, 700 ≤ r → r ≠ 960 → r ≠ 961 → r ≠ 962 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g960, g961, g962, fr₁, fm₁, frr₁, frm₁, fo₁⟩ :=
    saveSet_exec (P := P) c hc
  have e₂ := Exec.zeroRegs (P := P) 700 e₁.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, h390, h391, h392, h393, fr₃, fm₃, frr₃, frm₃, fo₃⟩ :=
    spRestSet_exec (P := P) _ e₂.wb_right
  simp only at h390 h391 h392 h393 fr₃ fm₃ frr₃ frm₃ fo₃
  refine ⟨c₃, t₁ + (700 + t₃), .seq e₁ (.seq e₂ e₃), by omega, ?_, ?_, ?_, ?_,
    fun r hr h => ?_, ?_, ?_, ?_, fun r hr h1 h2 h3 => ?_, by rw [fm₃, fm₁], by rw [frr₃, frr₁],
    by rw [frm₃, frm₁], by rw [fo₃, fo₁]⟩
  · rw [h390]; simp only [show ¬ (960 < 700) by omega, ↓reduceIte, g960]
  · rw [h391]; simp only [show ¬ (961 < 700) by omega, ↓reduceIte, g961]
  · rw [h392]; simp only [show ¬ (962 < 700) by omega, ↓reduceIte, g962]
  · rw [h393]; simp only [show ¬ (950 < 700) by omega, ↓reduceIte]
    exact fr₁ 950 (by omega) (by omega) (by omega)
  · rw [fr₃ r h]; simp only [hr, ↓reduceIte]
  · rw [fr₃ 960 (by omega)]; simp only [show ¬ (960 < 700) by omega, ↓reduceIte, g960]
  · rw [fr₃ 961 (by omega)]; simp only [show ¬ (961 < 700) by omega, ↓reduceIte, g961]
  · rw [fr₃ 962 (by omega)]; simp only [show ¬ (962 < 700) by omega, ↓reduceIte, g962]
  · rw [fr₃ r (by omega)]; simp only [show ¬ (r < 700) by omega, ↓reduceIte]
    exact fr₁ r h1 h2 h3

section Sem

open Orbit CombMap BKMNW PlanarSeparator PlanarSeparator.MillerProg

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {N : CombMap D V F}
variable {Pc : Finset D} {m k : ℕ} {δ : ℕ → D} {α σ : ℕ → ℕ}

set_option maxHeartbeats 1000000 in
/-- The encoding of the piece map of a share-closed part `K` (`encSet ; encProg`), at `B₀`, with
the index array at `X = B₀ + 25 k + 3`. -/
theorem encStage_exec (he : PEnc N Pc m k δ α σ) {K : Finset D} (hK : ShareClosed N Pc K)
    {bα bσ B₀ : ℕ} (c : Config) (hc : WordsBounded W c) (r10 : c.nreg 10 = 1)
    (r860 : c.nreg 860 = m) (r861 : c.nreg 861 = k) (r862 : c.nreg 862 = bα)
    (r863 : c.nreg 863 = bσ) (r950 : c.nreg 950 = B₀) (r951 : c.nreg 951 = B₀ + 25 * k + 3)
    {bF : ℕ} (r865 : c.nreg 865 = bF)
    (hα : ∀ h < k, c.nmem (bα + h) = α h) (hσ : ∀ h < k, c.nmem (bσ + h) = σ h)
    (hF : ∀ x < m, (c.nmem (bF + x) ≠ 0 ↔ δ x ∈ K))
    (lα : bα + k ≤ B₀) (lσ : bσ + k ≤ B₀) (lF : bF + m ≤ B₀) (hW : B₀ + 66 * k + 35 ≤ W) :
    ∃ c' t, Exec P W (.seq encSet encProg) c c' t ∧ t ≤ 116 * k + 54 ∧
      ∃ (m' nV nF : ℕ) (cn : SDart (rcl N K) ≃ Fin m') (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
        (fn : (kmap N K).Face ≃ Fin nF),
        Enc (kmap N K) cn vn fn c'.nmem B₀ (B₀ + m') (B₀ + 2 * m') (B₀ + 3 * m') (B₀ + 4 * m') ∧
        (∀ d, c'.nmem (B₀ + 5 * m' + cn d) = flK N K d) ∧
        c'.nreg 390 = m' ∧ c'.nreg 391 = nV ∧ c'.nreg 392 = nF ∧ c'.nreg 393 = B₀ ∧ m' ≤ k ∧
        (∀ h < k, ∀ hm : δ h ∈ rcl N K, c'.nmem (B₀ + 25 * k + 3 + h) = cn ⟨δ h, hm⟩) ∧
        (∀ a, (a < B₀ ∨ (B₀ + 6 * m' ≤ a ∧ a < B₀ + 25 * k + 3) ∨ B₀ + 28 * k + 3 ≤ a) →
          c'.nmem a = c.nmem a) ∧
        (∀ r, r < 390 ∨ (393 < r ∧ r < 900) ∨ 937 < r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g910, g911, g912, g913, g914, g915, g916, fr₁, fm₁, frr₁, frm₁, fo₁⟩ :=
    encSet_exec (P := P) c hc
  rw [r861] at g910; rw [r860] at g911; rw [r862] at g912; rw [r863] at g913
  rw [r865] at g914; rw [r950] at g915; rw [r951] at g916
  have g10 : c₁.nreg 10 = 1 := (fr₁ 10 (by omega)).trans r10
  obtain ⟨c₂, t₂, e₂, ht₂, m', nV, nF, cn, vn, fn, hE, hfl, h390, h391, h392, h393, hm', hX, fm₂,
      fr₂, frr₂, frm₂, fo₂⟩ :=
    encProg_enc (P := P) he hK (Fl := fun x => c.nmem (bF + x)) hF c₁ e₁.wb_right
      g910 g911 g912 g913 g914 g915 g916 g10 (fun h hh => by rw [fm₁]; exact hα h hh)
      (fun h hh => by rw [fm₁]; exact hσ h hh) (fun x _ => by rw [fm₁]) lα lσ lF
      (by omega) (by omega)
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, m', nV, nF, cn, vn, fn, hE, hfl, h390, h391, h392,
    h393, hm', hX, fun a ha => ?_, fun r hr => ?_, by rw [frr₂, frr₁], by rw [frm₂, frm₁],
    by rw [fo₂, fo₁]⟩
  · rw [fm₂ a (by omega), fm₁]
  · rw [fr₂ r (by omega), fr₁ r (by omega)]

end Sem

/-! ### The large-component case -/

/-- The time bound of `bigProg` for `k` half-edges. -/
def bigT (k : ℕ) : ℕ :=
  (1746 * k + 156) * (Nat.log 2 k + 3) + 17112 * k + 156 * Nat.sqrt (12 * k) + 2900

section Big

open Orbit CombMap BKMNW PlanarSeparator PlanarSeparator.MillerProg PlanarSeparator.StDart

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}
variable {Pc : Finset D} {m k : ℕ} {δ : ℕ → D} {α σ : ℕ → ℕ}

set_option maxHeartbeats 16000000 in
open Classical in
/-- **The large-component case of the split on the machine.** From the plain encoding of the
piece `Pc` (`PEnc`: the reversal at `bα`, the rotation at `bσ`) and the flags at `bF` of the
darts of a component `K = pcomp N Pc x₀` of more than three quarters of the darts (as `compProg`
leaves them), with the layout registers of `spSetup`, `bigProg` ends within `bigT k` steps with
a cut `A₀` of `K` meeting `CutOK` (the darts marked `1` by the separator run), the side of every
dart `x < m` at `Ob + x` (`0` exactly on the first part of `cutPair Pc K A₀`), and the positions
on the face of both parts (`PosInst`, the hypothesis `hpos` of `cornerProg_face`, the sources
being the shared vertices of the cut) at `T₁ + 2 (nV + nF)` and `T₂ + 2 (nV + nF)`. -/
theorem bigProg_spec (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    (hPr : Pc ⊆ reps N) (he : PEnc N Pc m k δ α σ) {x₀ : D} (hx₀ : x₀ ∈ Pc)
    {bα bσ bF B₀ : ℕ} (c₀ : Config)
    (hc : WordsBounded W c₀) (r10 : c₀.nreg 10 = 1) (r860 : c₀.nreg 860 = m)
    (r861 : c₀.nreg 861 = k) (r862 : c₀.nreg 862 = bα) (r863 : c₀.nreg 863 = bσ)
    (r865 : c₀.nreg 865 = bF) (r950 : c₀.nreg 950 = B₀)
    (r951 : c₀.nreg 951 = B₀ + 25 * k + 3) (r952 : c₀.nreg 952 = B₀ + 28 * k + 3)
    (r953 : c₀.nreg 953 = B₀ + 33 * k + 3) (r955 : c₀.nreg 955 = B₀ + 41 * k + 4)
    (r956 : c₀.nreg 956 = B₀ + 42 * k + 4) (r957 : c₀.nreg 957 = B₀ + 54 * k + 7)
    (hα : ∀ h < k, c₀.nmem (bα + h) = α h) (hσ : ∀ h < k, c₀.nmem (bσ + h) = σ h)
    (hF : ∀ x < m, (c₀.nmem (bF + x) ≠ 0 ↔ δ x ∈ pcomp N Pc x₀))
    (lα : bα + k ≤ B₀) (lσ : bσ + k ≤ B₀) (lF : bF + m ≤ B₀)
    (hB : aEnd10 (3 * k) (3 * k) ≤ B₀) (hW : B₀ + 66 * k + 35 ≤ W)
    (hlo : ∀ a ≤ B₀ + 25 * k + 2, c₀.nmem a ≤ B₀ + 25 * k + 2) :
    ∃ c' t, Exec P W bigProg c₀ c' t ∧ t ≤ bigT k ∧
      (∀ a, B₀ + 66 * k + 10 ≤ a → c'.nmem a = c₀.nmem a) ∧
      (∀ r, 972 ≤ r → c'.nreg r = c₀.nreg r) ∧
      ∃ A₀, CutOK N (pcomp N Pc x₀) A₀ ∧
        (∀ x < m, c'.nmem (B₀ + 41 * k + 4 + x) =
          if δ x ∈ (cutPair Pc (pcomp N Pc x₀) A₀).1 then 0 else 1) ∧
        ∃ (nV nF q : ℕ) (ν : V → ℕ), (∀ v, ν v < nV) ∧ nV + nF ≤ 2 * k ∧
          q ≤ 6 * Nat.sqrt (12 * (pcomp N Pc x₀).card) + 4 ∧
          PosInst N (cutPair Pc (pcomp N Pc x₀) A₀).1 (bdry N A₀ (pcomp N Pc x₀ \ A₀))
            (18 * (pcomp N Pc x₀).card) q c'.nmem (B₀ + 42 * k + 4 + 2 * (nV + nF)) ν ∧
          PosInst N (cutPair Pc (pcomp N Pc x₀) A₀).2 (bdry N A₀ (pcomp N Pc x₀ \ A₀))
            (18 * (pcomp N Pc x₀).card) q c'.nmem (B₀ + 54 * k + 7 + 2 * (nV + nF)) ν := by
  set K := pcomp N Pc x₀ with hKdef
  have hKP : K ⊆ Pc := pcomp_subset Pc x₀
  have hx₀K : x₀ ∈ K := self_mem_pcomp hx₀
  have hKr : K ⊆ reps N := hKP.trans hPr
  have hK0 : K.Nonempty := ⟨x₀, hx₀K⟩
  have hKc : DConn N K := pcomp_dconn
  have hmk := he.mle
  have hKm : K.card ≤ m := by rw [he.enumP.card]; exact card_le_card hKP
  -- the encoding of the piece map of `K`
  obtain ⟨c₁, t₁, e₁, ht₁, m', nV, nF, cn, vn, fn, hE₁, hfl₁, g390, g391, g392, g393, hm'k, hX₁,
      fm₁, fr₁, -, -, -⟩ :=
    encStage_exec (P := P) he (shareClosed_pcomp Pc x₀) c₀ hc r10 r860 r861 r862 r863 r950 r951
      r865 hα hσ hF lα lσ lF hW
  obtain ⟨hcm, hnn, hKm', hm2⟩ := enc_card (N := N) (K := K) cn vn fn
  have hm1 : 1 ≤ m' := by have := card_pos.2 hK0; omega
  have R1 : ∀ r, (r = 10 ∨ r = 860 ∨ r = 861 ∨ r = 865 ∨ (950 ≤ r ∧ r ≤ 957) ∨ 972 ≤ r) →
      c₁.nreg r = c₀.nreg r := fun r hr => fr₁ r (by omega)
  -- the copy of the encoding
  obtain ⟨c₂, t₂, e₂, ht₂, cp₂, fm₂, fr₂, -, -, -⟩ :=
    cpyStage_exec (P := P) (m' := m') (B₀ := B₀) (Y := B₀ + 28 * k + 3) c₁ e₁.wb_right g390
      ((R1 950 (by omega)).trans r950) ((R1 952 (by omega)).trans r952) (by spomega)
      (by spomega)
  have R2 : ∀ r, (r = 10 ∨ r = 860 ∨ r = 861 ∨ r = 865 ∨ (950 ≤ r ∧ r ≤ 957) ∨ 972 ≤ r) →
      c₂.nreg r = c₀.nreg r := fun r hr =>
    (fr₂ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans (R1 r hr)
  -- the copy of the flags
  obtain ⟨c₃, t₃, e₃, ht₃, cp₃, fm₃, fr₃, -, -, -⟩ :=
    cpfStage_exec (P := P) (m := m) (bF := bF) (Fh := B₀ + 33 * k + 3) c₂ e₂.wb_right
      ((R2 860 (by omega)).trans r860) ((R2 865 (by omega)).trans r865)
      ((R2 953 (by omega)).trans r953) (by spomega) (by spomega)
  have R3 : ∀ r, (r = 10 ∨ r = 860 ∨ r = 861 ∨ r = 865 ∨ (950 ≤ r ∧ r ≤ 957) ∨ 972 ≤ r) →
      c₃.nreg r = c₀.nreg r := fun r hr =>
    (fr₃ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans (R2 r hr)
  have q390 : c₃.nreg 390 = m' := by
    rw [fr₃ 390 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      fr₂ 390 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), g390]
  have q391 : c₃.nreg 391 = nV := by
    rw [fr₃ 391 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      fr₂ 391 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), g391]
  have q392 : c₃.nreg 392 = nF := by
    rw [fr₃ 392 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      fr₂ 392 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), g392]
  -- the registers `< 700` cleared
  obtain ⟨c₄, t₄, e₄, ht₄, h390, h391, h392, h393, hz₄, h960, h961, h962, fr₄, fm₄, -, -, -⟩ :=
    zeroStage_exec (P := P) c₃ e₃.wb_right
  rw [q390] at h390 h960; rw [q391] at h391 h961; rw [q392] at h392 h962
  rw [R3 950 (by omega), r950] at h393
  have R4 : ∀ r, (r = 860 ∨ r = 861 ∨ r = 865 ∨ (950 ≤ r ∧ r ≤ 957) ∨ 972 ≤ r) →
      c₄.nreg r = c₀.nreg r := fun r hr => (fr₄ r (by omega) (by omega) (by omega)
        (by omega)).trans (R3 r (by omega))
  -- the memory before the separator run
  have M4 : ∀ a, a < B₀ + 28 * k + 3 → c₄.nmem a = c₁.nmem a := fun a ha => by
    rw [fm₄, fm₃ a (by omega), fm₂ a (by omega)]
  have MY4 : ∀ i < 5 * m', c₄.nmem (B₀ + 28 * k + 3 + i) = c₁.nmem (B₀ + i) := fun i hi => by
    rw [fm₄, fm₃ _ (by spomega), cp₂ i hi]
  have MF4 : ∀ x < m, c₄.nmem (B₀ + 33 * k + 3 + x) = c₀.nmem (bF + x) := fun x hx => by
    rw [fm₄, cp₃ x hx, fm₂ _ (by spomega), fm₁ _ (by spomega)]
  have MX4 : ∀ h < k, ∀ hm : δ h ∈ rcl N K, c₄.nmem (B₀ + 25 * k + 3 + h) = cn ⟨δ h, hm⟩ :=
    fun h hh hm => by rw [M4 _ (by spomega)]; exact hX₁ h hh hm
  -- the separator run
  obtain ⟨ψ, hψ⟩ := exists_kψ hrot hK0
  have hE₄ : Enc (kmap N K) cn vn fn c₄.nmem B₀ (B₀ + m') (B₀ + 2 * m') (B₀ + 3 * m')
      (B₀ + 4 * m') := enc_congr hE₁ fun i hi =>
    ⟨M4 _ (by spomega), M4 _ (by spomega), M4 _ (by spomega), M4 _ (by spomega),
      M4 _ (by spomega)⟩
  have hfl₄ : ∀ x, c₄.nmem (B₀ + 5 * m' + cn x) = flK N K x := fun x => by
    rw [M4 _ (by have := (cn x).2; spomega)]; exact hfl₁ x
  have hval := enc_vals hE₁ hfl₁
  obtain ⟨c₅, t₅, e₅, ht₅, F5r, F5m, hcut, C, Z, hside, z1, z2, hb1, hb2, hbs, hu, hdj, hck, -, -,
      -⟩ :=
    sep_run_lift (P := P) (W := W) (W₁ := B₀ + 25 * k + 2) hM hrot hface hKr hK0 hKc hψ cn vn fn
      hm1 hE₄ hfl₄ ((aEnd10_mono (by omega) (by omega)).trans hB) (by spomega) (by spomega)
      e₄.wb_right (fun r hr => by
        rcases (show r < 390 ∨ 393 < r ∨ r = 390 ∨ r = 391 ∨ r = 392 ∨ r = 393 by omega) with
          h | h | rfl | rfl | rfl | rfl
        · rw [hz₄ r hr (Or.inl h)]; omega
        · rw [hz₄ r hr (Or.inr h)]; omega
        · rw [h390]; spomega
        · rw [h391]; spomega
        · rw [h392]; spomega
        · rw [h393]; spomega)
      (fun a ha => by
        rw [M4 a (by spomega)]
        by_cases h1 : a < B₀
        · rw [fm₁ a (Or.inl h1)]; exact hlo a ha
        by_cases h2 : a < B₀ + 6 * m'
        · have := hval a (by omega) h2; generalize c₁.nmem a = z at this ⊢; spomega
        · rw [fm₁ a (Or.inr (Or.inl ⟨by omega, by spomega⟩))]; exact hlo a ha)
      h390 h391 h392 h393
  set A₀ := markSet N K cn (fun i => c₅.nmem (B₀ + 22 * m' + i)) with hA₀def
  have hA₀K : A₀ ⊆ K := fun d hd => (mem_markSet.1 hd).1
  have R5 : ∀ r, (r = 860 ∨ r = 861 ∨ r = 865 ∨ (950 ≤ r ∧ r ≤ 962) ∨ 972 ≤ r) →
      c₅.nreg r = c₄.nreg r := fun r hr => F5r r (by omega)
  -- the join of the sides
  obtain ⟨c₆, t₆, e₆, ht₆, j10, j780, j781, j782, j783, j792, fr₆, fm₆, -, -, -⟩ :=
    joinSet_exec (P := P) (B₀ := B₀) (m' := m') c₅ e₅.wb_right
      ((R5 950 (by omega)).trans ((R4 950 (by omega)).trans r950))
      ((R5 960 (by omega)).trans h960) (by spomega)
  rw [R5 860 (by omega), R4 860 (by omega), r860] at j780
  rw [R5 953 (by omega), R4 953 (by omega), r953] at j781
  rw [R5 951 (by omega), R4 951 (by omega), r951] at j782
  rw [R5 955 (by omega), R4 955 (by omega), r955] at j783
  have R6 : ∀ r, (r = 860 ∨ r = 861 ∨ r = 865 ∨ (950 ≤ r ∧ r ≤ 962) ∨ 972 ≤ r) →
      c₆.nreg r = c₄.nreg r := fun r hr =>
    (fr₆ r (by omega) (by omega) (by omega) (by omega) (by omega)).trans (R5 r hr)
  have MF6 : ∀ x < m, c₆.nmem (B₀ + 33 * k + 3 + x) = c₀.nmem (bF + x) := fun x hx => by
    rw [fm₆, F5m _ (by spomega), MF4 x hx]
  have MX6 : ∀ h < k, ∀ hm : δ h ∈ rcl N K, c₆.nmem (B₀ + 25 * k + 3 + h) = cn ⟨δ h, hm⟩ :=
    fun h hh hm => by rw [fm₆, F5m _ (by spomega)]; exact MX4 h hh hm
  have hKf : ∀ x < m, (c₆.nmem (B₀ + 33 * k + 3 + x) ≠ 0 ↔ δ x ∈ K) := fun x hx => by
    rw [MF6 x hx]; exact hF x hx
  have hidx : ∀ x < m, δ x ∈ K → c₆.nmem (B₀ + 25 * k + 3 + x) < m' := fun x hx hK => by
    rw [MX6 x (by omega) (subset_rcl K hK)]; exact (cn _).2
  obtain ⟨c₇, t₇, e₇, ht₇, hsd, fm₇, jfr⟩ :=
    joinProg_exec (P := P) (m := m) (Kb := B₀ + 33 * k + 3) (Ib := B₀ + 25 * k + 3)
      (Ob := B₀ + 41 * k + 4) (Zb := B₀ + 22 * m') c₆ e₆.wb_right
      ⟨by spomega, by spomega, fun x hx hf => by
          have := hidx x hx ((hKf x hx).1 hf)
          generalize c₆.nmem (B₀ + 25 * k + 3 + x) = z at this ⊢; left; spomega,
        fun x hx hf => by
          have := hidx x hx ((hKf x hx).1 hf)
          generalize c₆.nmem (B₀ + 25 * k + 3 + x) = z at this ⊢; spomega,
        by spomega, by spomega, by spomega, by spomega⟩
      ⟨j10, j780, j781, j782, j783, j792⟩
  have hsides : ∀ x < m, c₇.nmem (B₀ + 41 * k + 4 + x) =
      if δ x ∈ (cutPair Pc K A₀).1 then 0 else 1 := fun x hx => by
    rw [hsd x hx]
    refine joinProg_cutPair he.enumP hKP hA₀K hKf (fun y hy hyK => ?_) x hx
    rw [MX6 y (by omega) (subset_rcl K hyK), fm₆, hA₀def, mem_markSet]
    exact ⟨fun ⟨_, _, h1⟩ => h1, fun h1 => ⟨hyK, subset_rcl K hyK, h1⟩⟩
  have R7 : ∀ r, (r = 860 ∨ r = 861 ∨ r = 865 ∨ (950 ≤ r ∧ r ≤ 962) ∨ 972 ≤ r) →
      c₇.nreg r = c₄.nreg r := fun r hr => (jfr.nreg r (by omega)).trans (R6 r hr)
  -- the walk of the first side
  obtain ⟨c₈, t₈, e₈, ht₈, w800, w801, w802, w803, w804, w805, w806, w807, w808, w809, w810, fr₈,
      fm₈, -, -, -⟩ :=
    fw1Set_exec (P := P) (Y := B₀ + 28 * k + 3) (m' := m') c₇ e₇.wb_right
      ((R7 952 (by omega)).trans ((R4 952 (by omega)).trans r952))
      ((R7 960 (by omega)).trans h960) (by spomega)
  rw [jfr.nreg 792 (by omega), j792] at w806
  rw [R7 961 (by omega), h961] at w807
  rw [R7 962 (by omega), h962] at w808
  rw [R7 956 (by omega), R4 956 (by omega), r956] at w810
  have w10 : c₈.nreg 10 = 1 := by rw [fr₈ 10 (by omega), jfr.nreg 10 (by omega), j10]
  have MY8 : ∀ i < 5 * m', c₈.nmem (B₀ + 28 * k + 3 + i) = c₁.nmem (B₀ + i) := fun i hi => by
    rw [fm₈, fm₇ _ (Or.inl (by spomega)), fm₆, F5m _ (by spomega), MY4 i hi]
  have hE₈ : Enc (kmap N K) cn vn fn c₈.nmem (B₀ + 28 * k + 3) (B₀ + 28 * k + 3 + m')
      (B₀ + 28 * k + 3 + 2 * m') (B₀ + 28 * k + 3 + 3 * m') (B₀ + 28 * k + 3 + 4 * m') :=
    enc_congr hE₁ fun i hi =>
      ⟨MY8 i (by omega), by rw [Nat.add_assoc, MY8 _ (by omega), ← Nat.add_assoc],
        by rw [Nat.add_assoc, MY8 _ (by omega), ← Nat.add_assoc],
        by rw [Nat.add_assoc, MY8 _ (by omega), ← Nat.add_assoc],
        by rw [Nat.add_assoc, MY8 _ (by omega), ← Nat.add_assoc]⟩
  have hz₈ : ∀ x, (kst N K).face (old x) ∈ Z ↔ c₈.nmem (B₀ + 22 * m' + cn x) = 1 := fun x => by
    rw [fm₈, fm₇ _ (Or.inl (by have := (cn x).2; spomega)), fm₆]; exact z1 x
  set R₁ : Finset D := if A₀.card ≤ (K \ A₀).card then Pc \ K else ∅ with hR₁def
  set R₂ : Finset D := if A₀.card ≤ (K \ A₀).card then ∅ else Pc \ K with hR₂def
  have hv0 : verts N (∅ : Finset D) = ∅ := by simp [verts]
  have hR₁ : Disjoint (verts N R₁) (verts N K) := by
    rw [hR₁def]; split_ifs
    · exact disjoint_verts_pcomp Pc x₀
    · rw [hv0]; exact disjoint_empty_left _
  have hR₂ : Disjoint (verts N R₂) (verts N K) := by
    rw [hR₂def]; split_ifs
    · rw [hv0]; exact disjoint_empty_left _
    · exact disjoint_verts_pcomp Pc x₀
  obtain ⟨c₉, t₉, e₉, ht₉, sf₉, fm₉, pos₁⟩ :=
    faceWalk_pos (P := P) hM hrot hface hKr hK0 hKc hψ hb1
      (Bs := bdry N (side N K Z) (side N K Zᶜ)) (fun b hb => ⟨(hbs b hb).1, (hbs b hb).2.2⟩)
      hR₁ cn vn fn (Y := B₀ + 28 * k + 3) (bz := B₀ + 22 * m') (sv := 1)
      (T₀ := B₀ + 42 * k + 4) hE₈ hz₈ (by spomega) (by spomega) (by spomega) e₈.wb_right w10
      w800 w801 w802 w803 w804 w805 w806 w807 w808 w809 w810
  -- the walk of the second side
  obtain ⟨c₁₀, t₁₀, e₁₀, ht₁₀, v809, v810, fr₁₀, fm₁₀, -, -, -⟩ :=
    fw2Set_exec (P := P) c₉ e₉.wb_right
  rw [sf₉.nreg 957 (by omega), fr₈ 957 (by omega), R7 957 (by omega), R4 957 (by omega),
    r957] at v810
  have v8 : ∀ r, 800 ≤ r → r ≤ 808 → c₁₀.nreg r = c₈.nreg r := fun r h1 h2 => by
    rw [fr₁₀ r (by omega) (by omega), sf₉.nreg r (by omega)]
  have v10 : c₁₀.nreg 10 = 1 := by
    rw [fr₁₀ 10 (by omega) (by omega), sf₉.nreg 10 (by omega), w10]
  have MY10 : ∀ i < 5 * m', c₁₀.nmem (B₀ + 28 * k + 3 + i) = c₈.nmem (B₀ + 28 * k + 3 + i) :=
    fun i hi => by rw [fm₁₀, fm₉ _ (Or.inl (by spomega))]
  have hE₁₀ : Enc (kmap N K) cn vn fn c₁₀.nmem (B₀ + 28 * k + 3) (B₀ + 28 * k + 3 + m')
      (B₀ + 28 * k + 3 + 2 * m') (B₀ + 28 * k + 3 + 3 * m') (B₀ + 28 * k + 3 + 4 * m') :=
    enc_congr hE₈ fun i hi =>
      ⟨MY10 i (by omega), by rw [Nat.add_assoc, MY10 _ (by omega), ← Nat.add_assoc],
        by rw [Nat.add_assoc, MY10 _ (by omega), ← Nat.add_assoc],
        by rw [Nat.add_assoc, MY10 _ (by omega), ← Nat.add_assoc],
        by rw [Nat.add_assoc, MY10 _ (by omega), ← Nat.add_assoc]⟩
  have hz₁₀ : ∀ x, (kst N K).face (old x) ∈ Zᶜ ↔ c₁₀.nmem (B₀ + 22 * m' + cn x) = 0 :=
    fun x => by
      have := (cn x).2
      rw [fm₁₀, fm₉ _ (Or.inl (by spomega)), fm₈, fm₇ _ (Or.inl (by spomega)), fm₆]; exact z2 x
  obtain ⟨c₁₁, t₁₁, e₁₁, ht₁₁, sf₁₁, fm₁₁, pos₂⟩ :=
    faceWalk_pos (P := P) hM hrot hface hKr hK0 hKc hψ hb2
      (Bs := bdry N (side N K Z) (side N K Zᶜ)) (fun b hb => ⟨(hbs b hb).2.1, (hbs b hb).2.2⟩)
      hR₂ cn vn fn (Y := B₀ + 28 * k + 3) (bz := B₀ + 22 * m') (sv := 0)
      (T₀ := B₀ + 54 * k + 7) hE₁₀ hz₁₀ (by spomega) (by spomega) (by spomega) e₁₀.wb_right v10
      ((v8 800 (by omega) (by omega)).trans w800) ((v8 801 (by omega) (by omega)).trans w801)
      ((v8 802 (by omega) (by omega)).trans w802) ((v8 803 (by omega) (by omega)).trans w803)
      ((v8 804 (by omega) (by omega)).trans w804) ((v8 805 (by omega) (by omega)).trans w805)
      ((v8 806 (by omega) (by omega)).trans w806) ((v8 807 (by omega) (by omega)).trans w807)
      ((v8 808 (by omega) (by omega)).trans w808) v809 v810
  -- the parts
  have hsZ : side N K Z = A₀ := hside
  have hsZc : side N K Zᶜ = K \ A₀ := by rw [← hsZ]; exact eq_sdiff_of_union hu hdj
  rw [hsZ, hsZc] at pos₁ pos₂
  have hX1 : A₀ ∪ R₁ = (cutPair Pc K A₀).1 := by
    rw [hR₁def]; unfold cutPair; split_ifs <;> simp
  have hX2 : (K \ A₀) ∪ R₂ = (cutPair Pc K A₀).2 := by
    rw [hR₂def]; unfold cutPair; split_ifs <;> simp
  -- the time bound
  have hS : (1746 * K.card + 156) * (Nat.log 2 K.card + 3) ≤ (1746 * k + 156) * (Nat.log 2 k + 3) :=
    Nat.mul_le_mul (by omega)
      (by have := Nat.log_mono_right (b := 2) (show K.card ≤ k by omega); omega)
  have hsq : Nat.sqrt (12 * K.card) ≤ Nat.sqrt (12 * k) := Nat.sqrt_le_sqrt (by omega)
  refine ⟨c₁₁, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + ((t₆ + t₇) + ((t₈ + t₉) + (t₁₀ + t₁₁))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq (.seq e₆ e₇) (.seq (.seq e₈ e₉)
      (.seq e₁₀ e₁₁))))))), ?_, fun a ha => ?_, fun r hr => ?_, A₀, hcut, fun x hx => ?_, nV, nF,
    C.k, fun v => vn (ψ v), fun v => (vn _).2, by spomega, hck,
    PosInst.congr pos₁ hX1 fun b _ => ?_, PosInst.congr pos₂ hX2 fun b _ => rfl⟩
  · unfold bigT
    clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ ht₇ ht₈ ht₉ ht₁₀ ht₁₁ hck hS hsq hm'k hKm hmk
    generalize (1746 * K.card + 156) * (Nat.log 2 K.card + 3) = S₁ at ht₅ hS
    generalize (1746 * k + 156) * (Nat.log 2 k + 3) = S₂ at hS ⊢
    omega
  · rw [fm₁₁ a (Or.inr (by spomega)), fm₁₀, fm₉ a (Or.inr (by spomega)), fm₈,
      fm₇ a (Or.inr (by spomega)), fm₆, F5m a (by spomega), fm₄, fm₃ a (Or.inr (by spomega)),
      fm₂ a (Or.inr (by spomega)), fm₁ a (Or.inr (Or.inr (by spomega)))]
  · rw [sf₁₁.nreg r (by omega), fr₁₀ r (by omega) (by omega), sf₉.nreg r (by omega),
      fr₈ r (by omega), jfr.nreg r (by omega), R6 r (by omega), R4 r (by omega)]
  · rw [fm₁₁ _ (Or.inl (by spomega)), fm₁₀, fm₉ _ (Or.inl (by spomega)), fm₈]
    exact hsides x hx
  · have := (vn (ψ b)).2
    rw [fm₁₁ _ (Or.inl (by spomega)), fm₁₀]

/-! ### The whole split -/

/-- The time bound of `splitProg` for `k` half-edges. -/
def splitT (k : ℕ) : ℕ := bigT k + 125 * k + 64

/-- In the large case the split of the machine is the cut of the large component, for an order
listing the darts of the piece. -/
theorem splitM_big' {ord : Finset D → List D} {P : Finset D} (hL : ∀ d ∈ P, d ∈ ord P)
    (cut : Finset D → Finset D) {x : D} (hx : x ∈ P)
    (hb : 3 * P.card / 4 < (pcomp N P x).card) :
    splitM N ord cut P = cutPair P (pcomp N P x) (cut (pcomp N P x)) := by
  unfold splitM
  rcases hf : (ord P).find? (bigP N P) with _ | y
  · exact absurd (bigP_iff.2 ⟨hx, hb⟩) (by simpa using List.find?_eq_none.1 hf x (hL x hx))
  · simp only
    rw [pcomp_eq_of_big (bigP_iff.1 (List.find?_some hf)).2 hb]

set_option maxHeartbeats 16000000 in
open Classical in
/-- **The split of a piece as one program.** From the plain encoding of the piece `Pc`
(`PEnc`: the reversal at `bα`, the rotation at `bσ`, `k` half-edges of which the `m` darts of
`Pc` come first; `r860 = m`, `r861 = k`, `r862 = bα`, `r863 = bσ`, `r865 = bF` (the flags),
`r950 = B₀`, `r10 = 1`), `splitProg` (`spSetup ; compProg ;` then `grpProg` or `bigProg`) ends
within `splitT k` steps, `O(k log k)`, with the side of every dart `x < m` at
`Ob + x = B₀ + 41 k + 4 + x`, `0` exactly on the first part of `splitM N ord cut Pc` for the order
`ord Pc = [δ 0, …, δ (m - 1)]` of the darts on the machine and:
* without a component of more than three quarters of the darts, any `cut`;
* otherwise, for the large component `K = pcomp N Pc x₀`, any `cut` with `cut K = A₀`, the cut
  read off the marks of the separator run, which meets `CutOK` (so a cut function giving these
  cuts meets `CutsOK`, `negDecM_fDec`); then also the positions on the face of both parts
  (`PosInst`, the hypothesis `hpos` of `cornerProg_face` with `ν` the vertex numbers, the sources
  the shared vertices of the cut) at `B₀ + 42 k + 4 + 2 (nV + nF)` and
  `B₀ + 54 k + 7 + 2 (nV + nF)`.

The memory from `B₀ + 66 k + 10` on and the registers from `972` on are kept; the memory up to
`B₀ + 25 k + 2` is the separator's scratch, and must be bounded by `B₀ + 25 k + 2` at the start
(`hlo`). -/
theorem splitProg_splitM (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    (hPr : Pc ⊆ reps N) (he : PEnc N Pc m k δ α σ) {ord : Finset D → List D}
    (hord : ord Pc = (List.range m).map δ) {bα bσ bF B₀ : ℕ} (c₀ : Config)
    (hc : WordsBounded W c₀) (r10 : c₀.nreg 10 = 1) (r860 : c₀.nreg 860 = m)
    (r861 : c₀.nreg 861 = k) (r862 : c₀.nreg 862 = bα) (r863 : c₀.nreg 863 = bσ)
    (r865 : c₀.nreg 865 = bF) (r950 : c₀.nreg 950 = B₀)
    (hα : ∀ h < k, c₀.nmem (bα + h) = α h) (hσ : ∀ h < k, c₀.nmem (bσ + h) = σ h)
    (lα : bα + k ≤ B₀) (lσ : bσ + k ≤ B₀) (lF : bF + m ≤ B₀)
    (dα : bF + m ≤ bα ∨ bα + k ≤ bF) (dσ : bF + m ≤ bσ ∨ bσ + k ≤ bF)
    (hB : aEnd10 (3 * k) (3 * k) ≤ B₀) (hW : B₀ + 66 * k + 35 ≤ W)
    (hlo : ∀ a ≤ B₀ + 25 * k + 2, c₀.nmem a ≤ B₀ + 25 * k + 2) :
    ∃ c' t, Exec P W splitProg c₀ c' t ∧ t ≤ splitT k ∧
      (∀ a, B₀ + 66 * k + 10 ≤ a → c'.nmem a = c₀.nmem a) ∧
      (∀ r, 972 ≤ r → c'.nreg r = c₀.nreg r) ∧
      (((∀ d ∈ Pc, (pcomp N Pc d).card ≤ 3 * Pc.card / 4) ∧
          ∀ cut : Finset D → Finset D, ∀ x < m, c'.nmem (B₀ + 41 * k + 4 + x) =
            if δ x ∈ (splitM N ord cut Pc).1 then 0 else 1) ∨
        ∃ x₀ ∈ Pc, 3 * Pc.card / 4 < (pcomp N Pc x₀).card ∧ ∃ A₀, CutOK N (pcomp N Pc x₀) A₀ ∧
          ∀ cut : Finset D → Finset D, cut (pcomp N Pc x₀) = A₀ →
            (∀ x < m, c'.nmem (B₀ + 41 * k + 4 + x) =
              if δ x ∈ (splitM N ord cut Pc).1 then 0 else 1) ∧
            ∃ (nV nF q : ℕ) (ν : V → ℕ), (∀ v, ν v < nV) ∧ nV + nF ≤ 2 * k ∧
              q ≤ 6 * Nat.sqrt (12 * (pcomp N Pc x₀).card) + 4 ∧
              PosInst N (splitM N ord cut Pc).1 (bdry N A₀ (pcomp N Pc x₀ \ A₀))
                (18 * (pcomp N Pc x₀).card) q c'.nmem (B₀ + 42 * k + 4 + 2 * (nV + nF)) ν ∧
              PosInst N (splitM N ord cut Pc).2 (bdry N A₀ (pcomp N Pc x₀ \ A₀))
                (18 * (pcomp N Pc x₀).card) q c'.nmem (B₀ + 54 * k + 7 + 2 * (nV + nF)) ν) := by
  have hmk := he.mle
  have hL : ∀ d ∈ Pc, d ∈ ord Pc := fun d hd => by
    obtain ⟨x, hx, rfl⟩ := he.enumP.surj d hd
    rw [hord]; exact List.mem_map.2 ⟨x, List.mem_range.2 hx, rfl⟩
  -- the layout
  obtain ⟨c₁, t₁, e₁, ht₁, s951, s952, s953, s954, s955, s956, s957, s864, fr₁, fm₁, -, -, -⟩ :=
    spSetup_exec (P := P) c₀ hc r10 r861 r950 hW
  have S1 : ∀ r, (r = 10 ∨ (860 ≤ r ∧ r ≤ 863) ∨ r = 865 ∨ r = 950 ∨ 972 ≤ r) →
      c₁.nreg r = c₀.nreg r := fun r hr => fr₁ r (by omega) (by omega)
  -- the components
  have hI : CompIn m k bα bσ (B₀ + 34 * k + 3) bF c₁ :=
    ⟨(S1 10 (by omega)).trans r10, (S1 860 (by omega)).trans r860,
      (S1 861 (by omega)).trans r861, (S1 862 (by omega)).trans r862,
      (S1 863 (by omega)).trans r863, s864, (S1 865 (by omega)).trans r865⟩
  have hLy : CompLay m k bα bσ (B₀ + 34 * k + 3) bF W :=
    ⟨hmk, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hα₁ : ∀ h < k, c₁.nmem (bα + h) = α h := fun h hh => by rw [fm₁]; exact hα h hh
  have hσ₁ : ∀ h < k, c₁.nmem (bσ + h) = σ h := fun h hh => by rw [fm₁]; exact hσ h hh
  obtain ⟨c₂, t₂, e₂, ht₂, hlb, hlab, hC, hFl, h856, fr₂, -, -, -, fm₂⟩ :=
    compProg_spec (P := P) hrot he c₁ e₁.wb_right hI hLy hα₁ hσ₁
  obtain ⟨c₂', t₂', e₂', -, lb, -, -, -, -, hFv, -, -, -, -, -, -⟩ :=
    compProg_exec (P := P) he.hEnc c₁ e₁.wb_right hI hLy hα₁ hσ₁
  obtain ⟨hcc, -⟩ := stmt_exec_det e₂' e₂
  rw [hcc] at hFv
  have S2 : ∀ r, (r = 10 ∨ (860 ≤ r ∧ r ≤ 865) ∨ 880 ≤ r) → c₂.nreg r = c₁.nreg r :=
    fun r hr => fr₂ r (by omega)
  have M2 : ∀ a, a < bF ∨ (bF + m ≤ a ∧ a < B₀ + 34 * k + 3) ∨ B₀ + 41 * k + 4 ≤ a →
      c₂.nmem a = c₀.nmem a := fun a ha => by
    rw [fm₂ a (by omega) (by omega), fm₁]
  rcases h856 with ⟨h0, hsmall⟩ | ⟨h1, hlt, hbig⟩
  · -- the small case: the grouping
    obtain ⟨c₃, t₃, e₃, ht₃, g880, g881, g882, g883, g884, g885, fr₃, fm₃, -, -, -⟩ :=
      grpSet_exec (P := P) (k := k) (B := B₀ + 34 * k + 3) c₂ e₂.wb_right
        ((S2 10 (by omega)).trans hI.r10) ((S2 861 (by omega)).trans hI.r861)
        ((S2 954 (by omega)).trans s954) (by omega)
    rw [S2 860 (by omega), hI.r860] at g880
    rw [S2 956 (by omega), s956] at g883
    rw [S2 955 (by omega), s955] at g884
    have g10 : c₃.nreg 10 = 1 := by
      rw [fr₃ 10 (by omega) (by omega) (by omega), S2 10 (by omega), hI.r10]
    obtain ⟨c₄, t₄, e₄, ht₄, hO, fr₄, -, -, -, fm₄⟩ :=
      grpProg_splitM (P := P) hord (fun _ => ∅) hsmall he.enumP (k := k)
        (bL := B₀ + 34 * k + 3 + 4 * k) (bC := B₀ + 34 * k + 3 + 6 * k)
        (bG := B₀ + 42 * k + 4) (bO := B₀ + 41 * k + 4) c₃ e₃.wb_right
        ⟨g10, g880, g881, g882, g883, g884, g885⟩
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
          by omega, by omega⟩
        (fun x hx => by rw [fm₃]; exact hlb x hx)
        (fun x hx y hy => by rw [fm₃]; exact hlab x hx y hy)
        (fun x hx => by rw [fm₃]; exact hC x hx)
    refine ⟨c₄, t₁ + (t₂ + ((t₃ + t₄) + 1)), .seq e₁ (.seq e₂ (.ifLtN_true (by
        rw [h0, S2 10 (by omega), hI.r10]; omega) (.seq e₃ e₄))), ?_, fun a ha => ?_,
      fun r hr => ?_, Or.inl ⟨hsmall, fun cut x hx => ?_⟩⟩
    · unfold splitT bigT
      clear * - ht₁ ht₂ ht₃ ht₄ hmk
      generalize (1746 * k + 156) * (Nat.log 2 k + 3) = S
      omega
    · rw [fm₄ a (by omega) (by omega), fm₃, M2 a (by omega)]
    · rw [fr₄ r (by omega), fr₃ r (by omega) (by omega) (by omega), S2 r (by omega),
        fr₁ r (by omega) (by omega)]
    · rw [hO x hx]
      rw [splitM_small (fun _ => ∅) hsmall, splitM_small cut hsmall]
  · -- the large case
    set x₀ := δ (c₂.nreg 857)
    have hx₀ : x₀ ∈ Pc := he.enumP.mem _ hlt
    have hF₂ : ∀ x < m, (c₂.nmem (bF + x) ≠ 0 ↔ δ x ∈ pcomp N Pc x₀) :=
      flags_big hbig hFl he.enumP.mem
    obtain ⟨c₃, t₃, e₃, ht₃, F3m, F3r, A₀, hcut, hsd, nV, nF, q, ν, hν, hnn, hq, pos₁, pos₂⟩ :=
      bigProg_spec (P := P) hM hrot hface hPr he hx₀ c₂ e₂.wb_right
        ((S2 10 (by omega)).trans hI.r10) ((S2 860 (by omega)).trans hI.r860)
        ((S2 861 (by omega)).trans hI.r861) ((S2 862 (by omega)).trans hI.r862)
        ((S2 863 (by omega)).trans hI.r863) ((S2 865 (by omega)).trans hI.r865)
        ((S2 950 (by omega)).trans ((S1 950 (by omega)).trans r950))
        ((S2 951 (by omega)).trans s951) ((S2 952 (by omega)).trans s952)
        ((S2 953 (by omega)).trans s953) ((S2 955 (by omega)).trans s955)
        ((S2 956 (by omega)).trans s956) ((S2 957 (by omega)).trans s957)
        (fun h hh => by rw [M2 _ (by omega)]; exact hα h hh)
        (fun h hh => by rw [M2 _ (by omega)]; exact hσ h hh) hF₂ lα lσ lF hB hW
        (fun a ha => by
          by_cases h : bF ≤ a ∧ a < bF + m
          · obtain ⟨h1, h2⟩ := h
            have := hFv (a - bF) (by omega)
            rw [show bF + (a - bF) = a by omega] at this
            rw [this]; split_ifs <;> omega
          · rw [M2 a (by omega)]; exact hlo a ha)
    refine ⟨c₃, t₁ + (t₂ + (t₃ + 2)), .seq e₁ (.seq e₂ (.ifLtN_false (by
        rw [h1, S2 10 (by omega), hI.r10]; omega) e₃)), ?_, fun a ha => ?_,
      fun r hr => ?_, Or.inr ⟨x₀, hx₀, hbig, A₀, hcut, fun cut hcA => ?_⟩⟩
    · unfold splitT
      clear * - ht₁ ht₂ ht₃ hmk
      generalize bigT k = S at ht₃ ⊢
      omega
    · rw [F3m a (by omega), M2 a (by omega)]
    · rw [F3r r hr, S2 r (by omega), fr₁ r (by omega) (by omega)]
    · have hs : splitM N ord cut Pc = cutPair Pc (pcomp N Pc x₀) A₀ := by
        rw [splitM_big' hL cut hx₀ hbig, hcA]
      rw [hs]
      exact ⟨hsd, nV, nF, q, ν, hν, hnn, hq, pos₁, pos₂⟩

end Big

end NegSSSP

end PlanarFlow
