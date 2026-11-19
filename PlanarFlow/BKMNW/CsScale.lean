module

public import PlanarFlow.BKMNW.CsGenF
public import PlanarFlow.BKMNW.NegInPlace
public import PlanarFlow.BKMNW.NfFrRun

/-!
# The scaled machine costs `cMachS` and the whole program for them

`cMach C C₀` (`MachCost.lean`) has the bare bounds of the reference runs in its fields, while the
in-place (logged) machine calls cost constant multiples of them (`negStep_lay_exec`:
`9 · negT C C₀ m + O(m)` with `negT ≈ 1.001 · 10¹² · negsssp`; `FrFix.frRun_exec`:
`108 · frCost + 14 N + 1000`; the MSSP call `ecost + 27 KC + 5 ZC + 23 q² + 28`). Here:

* **`csK = 10¹⁵`**, **`cMachS C C₀`**: the fields `mssp`, `fr`, `negsssp`, `stflow`, `lin` of
  `cMach C C₀` multiplied by `csK`; `leaf = C₀ m`, `sep = C m lg m` unchanged. Closed forms:
  `mssp m k = 10¹⁵ · 24637500000 (m lg m + k² lg m)`, `fr x p = 10¹⁵ · 6300 (x lg² x + p lg x)`,
  `negsssp m = 10¹⁵ (10920 negK C · m lg² m + 1000001 negK C · m)`,
  `stflow m = 10¹⁵ · 504000000 · m lg m`, `lin m = 10¹⁵ · C m`.
* **`machKS C = csK · machK C`**, **`cMachS_bounds : (cMachS C C₀).Bounds (machKS C) C₀`**, so the
  headline shape `O(n lg³ n)` is kept with the constant `10¹⁵ · machK C`.
* the scaling identities of the run budgets: **`cMachS_fixRun`**, **`cMachS_pushRun`**,
  **`cMachS_c2sRun`**, **`cMachS_lin`** (`= csK ·` the same budget of `cMach C C₀`);
* `cMachS_linLow` (the hypothesis `hlin` of the general chain, for `1 ≤ C`), `cMachS_sepLin`;
* budget lemmas for the node-step programs: `fsKC_eq` (`fsKC = 1000230256`), **`negT_le`**
  (`negT C C₀ n ≤ 1001000230338 · (cMach C C₀).negsssp n` for `1 ≤ n`), **`cMachS_negsssp_negT`**
  (`9 negT C C₀ n + 10¹⁴ · (cMach C C₀).negsssp n ≤ (cMachS C C₀).negsssp n`), `negsssp_ge`
  (`10¹⁹ n ≤ (cMach C C₀).negsssp n`), **`frRun_le_cMachS`** (`108 frCost P + 14 N + 1000 +
  10¹⁴ · (cMach C C₀).fr N m ≤ (cMachS C C₀).fr N m` for a laid-out FR input);
* **`mfMain_cMachSGEP`**: `mfMain_XGEPGen` for `cMachS C C₀`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

/-! ### The scaled cost family -/

/-- The scale of `cMachS`: `10¹⁵`. -/
def csK : ℕ := 10 ^ 15

/-- **The scaled machine costs**: the fields `mssp`, `fr`, `negsssp`, `stflow`, `lin` of
`cMach C C₀` multiplied by `csK = 10¹⁵` (room for the in-place, logged machine calls), the leaf
solver `C₀ m` and the separator `C m lg m` unchanged. -/
def cMachS (C C₀ : ℕ) : SubCosts where
  leaf m := C₀ * m
  sep m := C * m * lg m
  mssp m k := csK * (24637500000 * (m * lg m + k ^ 2 * lg m))
  fr x p := csK * (6300 * (x * lg x ^ 2 + p * lg x))
  negsssp m := csK * (10920 * NegSSSP.negK C * m * lg m ^ 2 + 1000001 * NegSSSP.negK C * m)
  stflow m := csK * (504000000 * (m * lg m))
  lin m := csK * (C * m)

/-- The constant of `cMachS C C₀`: `csK · machK C`. -/
def machKS (C : ℕ) : ℕ := csK * machK C

lemma cMachS_mssp (C C₀ m k : ℕ) : (cMachS C C₀).mssp m k = csK * (cMach C C₀).mssp m k := rfl
lemma cMachS_fr (C C₀ x p : ℕ) : (cMachS C C₀).fr x p = csK * (cMach C C₀).fr x p := rfl
lemma cMachS_negsssp (C C₀ m : ℕ) : (cMachS C C₀).negsssp m = csK * (cMach C C₀).negsssp m := rfl
lemma cMachS_stflow (C C₀ m : ℕ) : (cMachS C C₀).stflow m = csK * (cMach C C₀).stflow m := rfl
lemma cMachS_lin (C C₀ m : ℕ) : (cMachS C C₀).lin m = csK * (cMach C C₀).lin m := rfl

/-- **The scaled machine costs meet `SubCosts.Bounds`** with `K = machKS C = 10¹⁵ · machK C`,
`K₀ = C₀`. -/
theorem cMachS_bounds (C C₀ : ℕ) : (cMachS C C₀).Bounds (machKS C) C₀ where
  leaf m := le_rfl
  sep m := by
    have h1 := (le_machK C).1
    have h2 : machK C ≤ machKS C := by unfold machKS csK; omega
    show C * m * lg m ≤ machKS C * m * lg m
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (h1.trans h2))
  mssp m k := le_of_le_of_eq (Nat.mul_le_mul_left csK ((cMach_bounds C C₀).mssp m k))
    (by unfold machKS; ring)
  fr x p := le_of_le_of_eq (Nat.mul_le_mul_left csK ((cMach_bounds C C₀).fr x p))
    (by unfold machKS; ring)
  negsssp m := le_of_le_of_eq (Nat.mul_le_mul_left csK ((cMach_bounds C C₀).negsssp m))
    (by unfold machKS; ring)
  stflow m := le_of_le_of_eq (Nat.mul_le_mul_left csK ((cMach_bounds C C₀).stflow m))
    (by unfold machKS; ring)
  lin m := le_of_le_of_eq (Nat.mul_le_mul_left csK ((cMach_bounds C C₀).lin m))
    (by unfold machKS; ring)

/-! ### The run budgets of `cMachS` are `csK` times those of `cMach` -/

theorem cMachS_fixRun (C C₀ n x k L : ℕ) :
    (cMachS C C₀).fixRun n x k L = csK * (cMach C C₀).fixRun n x k L := by
  simp only [SubCosts.fixRun, cMachS_mssp, cMachS_fr, cMachS_negsssp, cMachS_lin]
  ring

theorem cMachS_pushRun (C C₀ n nf N : ℕ) :
    (cMachS C C₀).pushRun n nf N = csK * (cMach C C₀).pushRun n nf N := by
  simp only [SubCosts.pushRun, cMachS_fr, cMachS_lin]
  ring

theorem cMachS_c2sRun (C C₀ n nf N x k : ℕ) :
    (cMachS C C₀).c2sRun n nf N x k = csK * (cMach C C₀).c2sRun n nf N x k := by
  simp only [SubCosts.c2sRun, cMachS_stflow, cMachS_fixRun, cMachS_pushRun, cMachS_lin]
  ring

/-- **The lower bound `hlin` of the general chain** holds for `cMachS C C₀` when `1 ≤ C`. -/
theorem cMachS_linLow {C C₀ : ℕ} (hC : 1 ≤ C) (a b : ℕ) :
    200 * a + (cMachS C C₀).lin b ≤ (cMachS C C₀).lin (a + b) := by
  show 200 * a + csK * (C * b) ≤ csK * (C * (a + b))
  have h : 200 * a ≤ csK * (C * a) :=
    Nat.mul_le_mul (by unfold csK; norm_num) (Nat.le_mul_of_pos_left a hC)
  rw [Nat.mul_add, Nat.mul_add]
  omega

/-- The separator budget of `mfMain_cMachXGEP` fits that of the general chain for `cMachS`. -/
theorem cMachS_sepLin {C C₀ : ℕ} (hC : 1 ≤ C) (P h : ℕ) :
    C * P * lg P + C * h ≤ (cMachS C C₀).sep P + (cMachS C C₀).lin h := by
  show C * P * lg P + C * h ≤ C * P * lg P + csK * (C * h)
  have : C * h ≤ csK * (C * h) := Nat.le_mul_of_pos_left _ (by unfold csK; norm_num)
  omega

/-! ### Budget lemmas for the node-step programs -/

/-- The constant of the full branch of the negative-length recursion. -/
theorem fsKC_eq : NegSSSP.fsKC = 1000230256 := by decide +kernel

/-- `(cMach C C₀).negsssp n` is at least `10¹⁹ n`. -/
theorem negsssp_ge (C C₀ n : ℕ) : 10 ^ 19 * n ≤ (cMach C C₀).negsssp n := by
  show 10 ^ 19 * n ≤ 10920 * NegSSSP.negK C * n * lg n ^ 2 + 1000001 * NegSSSP.negK C * n
  have h1 : 32886 * 2372500000 ≤ NegSSSP.negK C := (NegSSSP.le_negK C).2
  have h2 : 10 ^ 19 ≤ 1000001 * NegSSSP.negK C := by omega
  have h3 := Nat.mul_le_mul_right n h2
  omega

/-- **The in-place negative-length call within the scaled budget**: for `1 ≤ n`,
`negT C C₀ n ≤ 1001000230338 · (cMach C C₀).negsssp n`. -/
theorem negT_le {C C₀ n : ℕ} (hn : 1 ≤ n) :
    MfDrv.negT C C₀ n ≤ 1001000230338 * (cMach C C₀).negsssp n := by
  unfold MfDrv.negT
  rw [fsKC_eq]
  have h := negsssp_ge C C₀ n
  have h2 : 10 ^ 19 ≤ 10 ^ 19 * n := Nat.le_mul_of_pos_right _ hn
  generalize (cMach C C₀).negsssp n = X at *
  norm_num at h h2 ⊢
  omega

/-- **Nine in-place negative-length calls and `10¹⁴ · negsssp` of room fit `cMachS.negsssp`**
(`negStep_lay_exec` costs `9 · negT C C₀ m` plus `O(m)`; `negsssp_ge` turns the room into
`10³³ m` steps). -/
theorem cMachS_negsssp_negT {C C₀ n : ℕ} (hn : 1 ≤ n) :
    9 * MfDrv.negT C C₀ n + 10 ^ 14 * (cMach C C₀).negsssp n ≤ (cMachS C C₀).negsssp n := by
  rw [cMachS_negsssp]
  have := negT_le (C := C) (C₀ := C₀) hn
  generalize MfDrv.negT C C₀ n = Y at *
  generalize (cMach C C₀).negsssp n = X at *
  unfold csK
  norm_num
  omega

open Monge.FR in
/-- **The resident FR-Dijkstra run within the scaled budget**: for a laid-out FR input,
`108 frCost P + 14 N + 1000` (`FrFix.frRun_exec`) plus `10¹⁴ · (cMach C C₀).fr N m` of room fit
`(cMachS C C₀).fr N m`. -/
theorem frRun_le_cMachS (C C₀ : ℕ) {P : Prm} (hL : Lay P) :
    108 * frCost P + 14 * P.N + 1000 + 10 ^ 14 * (cMach C C₀).fr P.N P.m ≤
      (cMachS C C₀).fr P.N P.m := by
  rw [cMachS_fr]
  have h1 : frCost P ≤ (cMach C C₀).fr P.N P.m := by
    refine (frCost_le_fr hL).trans ?_
    have := heap_lg_le P.N
    show _ ≤ 6300 * (P.N * lg P.N ^ 2 + P.m * lg P.N)
    gcongr
  have hN := hL.N_pos
  have h2 : 6300 * P.N ≤ (cMach C C₀).fr P.N P.m := by
    show 6300 * P.N ≤ 6300 * (P.N * lg P.N ^ 2 + P.m * lg P.N)
    have : P.N ≤ P.N * lg P.N ^ 2 := Nat.le_mul_of_pos_right _ (by have := one_le_lg P.N; positivity)
    omega
  unfold csK
  omega

/-! ### The whole program with the scaled machine costs -/

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver

universe w

section Head

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The whole program with the machine's node subroutines, the push-back of `NsStep.pchCall`
and the parts by `segP`, with the scaled machine costs `cMachS C C₀`** (`mfMain_XGEPGen` for
`c = cMachS C C₀`, `K = machKS C = 10¹⁵ · machK C`, `K₀ = C₀`): within
`95 N + 200 + ((100000+11)² · 448 · (27 · 102256 + 25) · machKS C · n · lg³ n +
(100000+11)² · 28 · C₀ · n · lg n + 2000 (2 N + 1) + 2)` steps (`n = #D`). The subroutine costs
are asked in the fields of `cMachS C C₀` (`10¹⁵` times those of `cMach C C₀`: `cMachS_fixRun`,
`cMachS_c2sRun`, `cMachS_pushRun`, `cMachS_lin`); the separator steps in `C n lg n + C h` as in
`mfMain_cMachXGEP`; `1 ≤ C` (no condition on `C₀`). -/
theorem mfMain_cMachSGEP (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) (I₀ : Input)
    {C C₀ : ℕ} (hC : 1 ≤ C) {I : Input} {W Hb Wz Z : ℕ} {gid : _ → ℕ} {ν : _ → ℕ}
    {sepL sepX fixP c2sP s2cP retP frmP : Stmt}
    {chs : (x : MCall (lpreMap M)) → (h : PieceInv (lpreMap M) x.1.piece x.2.1 x.2.2) →
      STFlow.StChoice (pmap h)}
    {sTL sTX : ℕ → ℕ → ℕ} {sRL sRX : ℕ → ℕ → ℕ → ℕ} {rO : MCall (lpreMap M) → ℕ}
    {fT rtT fmT : MCall (lpreMap M) → ℕ → ℕ} {cT s2T : MCall (lpreMap M) → ℕ → ℕ → ℕ}
    {RS RT : ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepC (lpreMap M) e n (encB' W)) e n Hs A W
    let gS := gSz (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMap M) (pendQ _))
    let gH := gHl (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 100000
      (CInvS (lpreMap M) (pendQ _))
    let ds : DSys (lpreMap M) := ⟨guardS (lpreMap M) gS (spSR (lpreMap M) pc sc (pendQ _)),
      guardS (lpreMap M) gH (spHR (lpreMap M) pc sc (pendQ _)),
      chRot (lpreMap M) (pendQ _), 100000, pendQ _, pc.pick⟩
    let τ := decS (lpreMap M) (guardS (lpreMap M) gS (spSR (lpreMap M) pc sc (pendQ _)))
      (guardS (lpreMap M) gH (spHR (lpreMap M) pc sc (pendQ _)))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMap M) τ [] (rotPerm (lpreMap M))
    let N := τ.piece.card
    let c := cMachS C C₀
    SepPSpecXL (lpreMap M) ds Reach gid ν u' S' T' Z I W sepL sTL sRL →
    SepPSpecXS (lpreMap M) ds Reach gid ν u' S' T' Z I W sepX sTX sRX →
    (∀ x, Reach x → ∀ h, (chs x h).OK) →
    FixPSpecN (lpreMap M) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz fixP fT rO →
    C2SPSpecN (lpreMap M) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz c2sP cT rO →
    S2CPSpecN (lpreMap M) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz s2cP s2T rO →
    RetPSpecN (lpreMap M) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz retP rtT rO →
    FrmPSpecN (lpreMap M) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))
      Reach gid u' S' T' Z I W Wz frmP fmT rO →
    (∀ x : MCall (lpreMap M), x.2.1.length + 1 ≤ rO x) →
    PkMin gid pc.pick → Injective ν → (∀ y, (lpreMap M).head y ≠ (lpreMap M).tail y) →
    100000 ≤ W →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      sTL (l.piece ∪ r.piece).card Hs.length + segT (lpreMap M) sTX sRX (.node l r π, Hs, σ) ≤
        C * (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card + C * Hs.length) →
    (∀ l r π Hs σ (h : SCond (lpreMap M) l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxN (lpreMap M) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid)) u' S' T' l r π Hs σ
        h).L[j]? = some πj →
      fT (.node l r π, Hs, σ) j ≤ c.fixRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
        πj.faces.card πj.k (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) ∧
      (∀ i, cT (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      (∀ i, s2T (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      rtT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) ∧
      fmT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))) →
    (∀ n m k, n ≤ N → m ≤ N → k ≤ N → sRL n m k ≤ RS) → (∀ x, Reach x → segR (lpreMap M) sRX x + rO x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb VTb RTb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 2 ≤ Hb → Wz + 2 < Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    MemZ Wz c₀ →
    c₀.nreg 6700 = N → c₀.nreg 6701 = REVb → c₀.nreg 6702 = SIGb → c₀.nreg 6703 = CAPb →
    c₀.nreg 6704 = KRb → c₀.nreg 6705 = ntag τ → c₀.nreg 6706 = Z → c₀.nreg 6707 = Hb →
    c₀.nmem (Hb - 1) = VTb → c₀.nmem (Hb - 1 - 1) = RTb →
    (∀ i < N, c₀.nmem (REVb + i) < N ∧ en (c₀.nmem (REVb + i)) = (lpreMap M).rev (en i)) →
    (∀ i < N, c₀.nmem (SIGb + i) < N ∧
      en (c₀.nmem (SIGb + i)) = rotPerm (lpreMap M) (en i)) →
    (∀ i < N, (c₀.nmem (CAPb + i) : ℤ) = u' (en i) ∧ c₀.nmem (CAPb + i) ≤ Z) →
    (∀ i < N, c₀.nmem (KRb + i) = lrk S' T' (hunion []) ((lpreMap M).tail (en i))) →
    (∀ i < N, c₀.nmem (VTb + i) = ν ((lpreMap M).tail (en i))) →
    (∀ i < N, en i ∈ pdarts (lpreMap M) (core (lpreMap M) (pendQ _) univ) [] →
      c₀.nmem (RTb + i) < N ∧ en (c₀.nmem (RTb + i)) = rootRot (lpreMap M) (pendQ _) (en i)) →
    REVb + N ≤ Hb → SIGb + N ≤ Hb → CAPb + N ≤ Hb → KRb + N ≤ Hb → VTb + N ≤ Hb - 2 →
    RTb + N ≤ Hb - 2 →
    Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N + (2 * N + 1) * (110 * N + 80 + RS + RT) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq (.seq rfProg rxProg) (driver mtProg mlProg
        (splitSX (sepPX 100000 sepL))
        (nodeSF (stepX (segP sepX) (stepPO cntP fixP c2sP s2cP retP frmP))))) c₀ c' t ∧
      t ≤ 95 * N + 200 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machKS C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        2000 * (2 * N + 1) + 2) ∧ MemZ Wz c' ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunLN (lpreMap M) (NsStep.machNF gid I₀ chs (NsStep.pchCall gid)) u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) (Hb + 5 + 4 + 7 * N + 1 + 3 + 7 * N) c' ∧
      IsMax M u S T (nlRunN M u S T τ (NsStep.machNF gid I₀ chs (NsStep.pchCall gid))) := by
  intro pc sc gS gH ds τ u' S' T' Reach N c hsL hsX hok hfx hc2 hs2 hrt hfm hrO hpk hν hloop
    hsW hsT
  exact mfMain_XGEPGen hM hrot hface hu hST e hsurj d₀ hx₀ I₀ (cMachS_bounds C C₀)
    (cMachS_linLow hC) hZ hsL hsX hok hfx hc2 hs2 hrt hfm hrO hpk hν hloop hsW
    (fun l r π Hs σ hx => (hsT l r π Hs σ hx).trans (cMachS_sepLin hC _ _))

end Head

end MfDrv

end BKMNW

end PlanarFlow
