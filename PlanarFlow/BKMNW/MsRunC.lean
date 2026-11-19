module

public import PlanarFlow.BKMNW.MsRunB
public import PlanarFlow.BKMNW.KleinFix

/-!
# The MSSP call: `msspCall` from an encoder, and `MsspCallSpec`

**`msspCall encP`** `= encP ; mcSet ; lgS 8020 8021 kNFM ; mrRead ; mcClr`:

* `encP` (the encoder, assumed through **`MsEncSpec`**): from the call's input (`MsIn`) and the
  zero memory `≤ Wz`, it writes an explicit Klein start of the call (`KStart`: a cut along the
  path, an isolating weight, a numbering, the Klein data), the low memory `natCfg c₀` with the
  input words at `β' = kleinWN + 1` (`kMem`), the parameters `knVM` of `KleinFix.kNFM`, the slot of
  a flagged root of every query face (`SL`) and the target of every query face (`TI`), and the
  registers of the read-back and the clearing (`MsEncOut`);
* `mcSet`: the log registers; the logged in-place run of the fixed Klein program
  (`KleinFix.kNFM_lgRun`, against the reference run `KleinFix.kNFM_exec` of `KStart.run`);
* `mrRead`: the answers divided by `N₁` read back into the `q × q` matrix at `Ob`
  (`kAns_read`: they are the words `msW` of `msspPlaneK`);
* `mcClr`: the logged cells, `natCfg`'s region and the input words zeroed.

**`msspCall_spec`**: `MsEncSpec M encP EScr ecost KC ZC R wz` implies
`MsspCallSpec M (msspCall encP) (EScr ∨ msScr) (msCost …) R wz`, with
`msCost = ecost + 27 KC + 5 ZC + 23 q² + 28` (`KC` bounds Klein's natural run, `ZC` the regions
the encoder writes below `Wz`). **What remains for an unconditional `MsspCallSpec`** is an
encoder program meeting `MsEncSpec` (the cut map of the path from the frame, its numbering and
layout, an isolating weight, the initial trees and their orders, the real memory of the trip,
the flags and targets).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Klein MSSP STFlow
  DynTree NegSSSP NsStep

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- The low memory of the start: `natCfg c₀` up to `kleinWN`, then the input words at
`kleinWN + 1`. -/
noncomputable def kMem (B n Hc : ℕ) (c₀ : Config) (Pin : Input) (a : ℕ) : ℕ :=
  if a ≤ kleinWN B n Hc then
    (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀).nmem a
  else Pin.data.getD (a - (kleinWN B n Hc + 1)) 0

/-- **What the encoder leaves** (see the module docstring). -/
def MsEncOut (P : SPath M) (ℓ : D → ℤ) (q : ℕ) (ts : ℕ → D) (Wz Ob p R KC ZC : ℕ)
    (c e : Config) : Prop :=
  ∃ (C : Cut M ℓ P.darts (CutD M P.darts) (CutV M P.darts) (CutF M P.darts))
    (w : CutD M P.darts → ℤ) (nD : ℕ) (σ : CutD M P.darts ≃ Fin nD) (n B t : ℕ)
    (ιv : CutV M P.darts → ℕ) (ιg : CutD M P.darts → ℕ) (ιf : CutF M P.darts → ℕ)
    (ιe : CutD M P.darts → ℕ) (X : ℕ → CutV M P.darts) (fl : ℕ → Bool) (Pin : Input)
    (T : DTree C.map.dual) (C₀ : DTree C.map) (vs ts' : List (CutV M P.darts))
    (fs cs : List (CutF M P.darts)) (c₀ : Config) (Hc SLb TIb Lgb : ℕ),
    KStart P ℓ C w nD σ n B t ιv ιg ιf ιe X fl Pin T C₀ vs ts' fs cs c₀ Hc ∧
    kSteps (Fintype.card (CutV M P.darts)) (Fintype.card (CutF M P.darts)) nD C.piece.card n
      C.k (kRank fl C.k) t ≤ KC ∧
    1 ≤ Hc ∧ 2 * kleinWN B n Hc + 1 ≤ Wz ∧ Pin.data.length ≤ kleinWN B n Hc ∧
    2 * (B + 16 * (n + 1)) + 2 + Pin.data.length ≤ ZC ∧
    (∀ a ≤ Wz, e.nmem a = kMem B n Hc c₀ Pin a) ∧ (∀ a ≤ Wz, e.nmem a ≤ Wz) ∧
    (∀ r < 406, e.nreg r =
      (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀).nreg r) ∧
    (∀ j < 48, e.nreg (1000 + j) =
      KleinFix.knVM B nD n C.k t Hc (kleinWN B n Hc + 1) Pin.data.length j) ∧
    (∀ r < 1048, e.nreg r ≤ Wz) ∧
    e.nreg 8010 = t ∧ e.nreg 8011 = aRBM n C.k ∧
    e.nreg 8012 = B + 16 * (n + 1) + 1 + aOUT nD ∧ e.nreg 8013 = kN1 M P.darts ∧
    e.nreg 8014 = SLb ∧ e.nreg 8015 = TIb ∧ e.nreg 8016 = 2 * (B + 16 * (n + 1)) + 2 ∧
    e.nreg 8017 = kleinWN B n Hc + 1 ∧ e.nreg 8018 = Pin.data.length ∧ e.nreg 8019 = Lgb ∧
    (∀ i < q, ∃ j < C.k, fl j = true ∧ C.root j = M.face (ts i) ∧
      e.nmem (SLb + i) = kRank fl j) ∧
    (∀ i < q, e.nmem (TIb + i) < t ∧ X (e.nmem (TIb + i)) = C.vx (M.face (ts i))) ∧
    p ≤ SLb ∧ SLb + q ≤ Lgb ∧ p ≤ TIb ∧ TIb + q ≤ Lgb ∧ Wz < Lgb ∧ Lgb + 3 * KC + 1 ≤ p + R ∧
    (∀ a, Wz < a → (a < p ∨ p + R ≤ a) → e.nmem a = c.nmem a) ∧
    e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output

variable (M) in
/-- **The specification of the encoder of an MSSP call** (the hypotheses of `MsspCallSpec`, with
the conclusion `MsEncOut`, the registers outside `EScr` and `r8000 … r8009` kept). -/
def MsEncSpec (encP : Stmt) (EScr : ℕ → Prop) (ecost KC ZC R : ℕ → ℕ → ℕ → ℕ)
    (wz : ℕ → ℕ → ℕ) : Prop :=
  M.IsPlane → M.RotTrans →
  ∀ (en : ℕ → D) (m : ℕ) (P : SPath M) (ℓ : D → ℤ) (Lmax q : ℕ) (ts : ℕ → D)
    (RVb RTb Pb Lb Qb Ob p Wz W : ℕ) (I : Input) (c : Config),
    EnumOK M en m → 0 < P.k → (∀ e, 0 ≤ ℓ e) → (∀ i < q, M.face (ts i) ∈ P.faces) →
    WordsBounded W c → MsIn M en m P ℓ Lmax q ts RVb RTb Pb Lb Qb Ob p c →
    MsPlace m P.k q Wz W RVb RTb Pb Lb Qb Ob p (R m P.k q) →
    (∀ a ≤ Wz, c.nmem a = 0) → wz m Lmax ≤ Wz →
    ∃ e t, Exec I W encP c e t ∧ t ≤ ecost m P.k q ∧
      MsEncOut P ℓ q ts Wz Ob p (R m P.k q) (KC m P.k q) (ZC m P.k q) c e ∧
      (∀ r, ¬ EScr r → e.nreg r = c.nreg r) ∧ (∀ r, 8000 ≤ r → r ≤ 8009 → e.nreg r = c.nreg r)

/-- The log registers. -/
def mcSet : Stmt := block [.constN 8021 1, .copyN 8020 8019]

/-- **The MSSP call** with the encoder `encP`. -/
def msspCall (encP : Stmt) : Stmt :=
  .seq encP (.seq mcSet (.seq (lgS 8020 8021 KleinFix.kNFM) (.seq mrRead mcClr)))

/-- The scratch registers of the call after the encoder. -/
def msScr (r : ℕ) : Prop :=
  r < 1048 ∨ (2923 ≤ r ∧ r ≤ 2929) ∨ (5030 ≤ r ∧ r ≤ 5035) ∨ (8010 ≤ r ∧ r ≤ 8032)

/-- The step bound of the call. -/
def msCost (ecost KC ZC : ℕ → ℕ → ℕ → ℕ) (m k q : ℕ) : ℕ :=
  ecost m k q + 27 * KC m k q + 5 * ZC m k q + 23 * (q * q) + 28

/-! ### Small facts -/

lemma slot_lt {s t τ K : ℕ} (hs : s + 1 ≤ K) (hτ : τ < t) : s * t + τ < K * t := by
  have h1 : (s + 1) * t ≤ K * t := Nat.mul_le_mul_right t hs
  have h2 : s * t + τ < (s + 1) * t := by rw [Nat.succ_mul]; omega
  omega

lemma natCfg_hi {W Mo β : ℕ} {c₀ : Config} {a : ℕ} (hβ : β = W + 1) (ha : 2 * W + 2 ≤ a) :
    (natCfg 201 W Mo β c₀).nmem a = 0 := by
  simp only [natCfg]
  split_ifs <;> omega

lemma kMem_zero {B n Hc : ℕ} {c₀ : Config} {Pin : Input} {a : ℕ}
    (h1 : 2 * (B + 16 * (n + 1)) + 2 ≤ a)
    (h2 : a < kleinWN B n Hc + 1 ∨ kleinWN B n Hc + 1 + Pin.data.length ≤ a) :
    kMem B n Hc c₀ Pin a = 0 := by
  unfold kMem
  split_ifs with h
  · exact natCfg_hi rfl h1
  · rw [List.getD_eq_default]; omega

lemma div_mod_q {q i j : ℕ} (hj : j < q) : (i * q + j) / q = i ∧ (i * q + j) % q = j := by
  have hq : 0 < q := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- `mcSet`. -/
theorem mcSet_exec {P : Input} {W : ℕ} (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' u, Exec P W mcSet c c' u ∧ u = 2 ∧ c'.nreg 8021 = 1 ∧ c'.nreg 8020 = c.nreg 8019 ∧
      (∀ r, r ≠ 8020 → r ≠ 8021 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mcSet
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  repeat rw [upd_other _ _ _ (by omega)]

end MsCall

end BKMNW

end PlanarFlow
