module

public import PlanarFlow.BKMNW.Nf7bH
public import PlanarFlow.BKMNW.NpStep

/-!
# The program `fixP`: composition with the prologue and the final step

`fixP = preP ; loopP ; finP` where `preP` (prologue, MSSP call, image written once) and
`finP` (clear the images, final negative-length call, `FL`) are **hypotheses** here,
given as specifications against the stage
loop's interface (`SLx.Good`, `SLx.Regs`, `SLx.Fix`, `SLx.Stt (X.st 0)`, `SLx.Img` before the
loop; `SLx.Stt (X.st k)`, `SLx.Img`, the kept memory and registers after it).

* `loopT b k` (the cost of `loopP`), `SLx.loopP_exec'`;
* **`fixSeq_exec`**: the composition of the three runs, within `T₁ + loopT b k + T₃`;
* `FixPreSpec`, `FixFinSpec` (the specifications of `preP` and `finP` at a node call);
  **`fixP_specN`**: `FixPreSpec ∧ FixFinSpec ⇒ FixPSpecN … (preP ; loopP ; finP) fT rO` with
  **`fT x j = preT x j + loopT (bOf x j) (kOf x j) + finT x j`**;
* **`loopT_le_cMachS`**: `1 ≤ b → loopT b k ≤ k · (cMachS C C₀).fr b (2k) + 3`;
  **`fT_le_fixRun`**: if `preT + finT + 3 ≤ mssp n k + negsssp n + lin N` (of `cMachS C C₀`) and
  `1 ≤ b`, then `preT + loopT b k + finT ≤ (cMachS C C₀).fixRun n b k N`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap SPath WordRAM WordRAM.Machine Monge.FR

/-- **The cost of the `k` stages** (`b` corners). -/
def loopT (b k : ℕ) : ℕ :=
  (108 * (6300 * (b * lg b ^ 2 + 2 * k * lg b)) + 56 * b + 68 * k + 1200 + 2) * k + 3

section Seq

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The loop with its cost as `loopT`. -/
theorem SLx.loopP_exec' {X : SLx M} {W : ℕ} {I : Input} (hG : X.Good W) (c : Config)
    (hc : WordsBounded W c) (hR : X.Regs c) (hFx : X.Fix c.nmem) (hS : X.Stt (X.st 0) c.nmem)
    (hImg : X.Img c.nmem) :
    ∃ c' t, Exec I W loopP c c' t ∧ t ≤ loopT X.b X.P.k ∧
      X.Stt (X.st X.P.k) c'.nmem ∧ X.Img c'.nmem ∧
      (∀ a, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → ¬ X.Wr a → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ SLx.scr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, e, ht, h⟩ := SLx.loopP_exec (I := I) hG c hc hR hFx hS hImg
  exact ⟨c', t, e, by unfold loopT; unfold SLx.T at ht; exact ht, h⟩

/-- **The composition `preP ; loopP ; finP`.** -/
theorem fixSeq_exec {I : Input} {W : ℕ} (preP finP : Stmt) (pre : Config → Prop)
    (post : Config → Config → Prop) (Q : Config → SLx M → Config → Prop) (T₁ T₃ b k : ℕ)
    (hpre : ∀ c, pre c → WordsBounded W c → ∃ (c₁ : Config) (t₁ : ℕ) (X : SLx M),
      Exec I W preP c c₁ t₁ ∧
      t₁ ≤ T₁ ∧ X.Good W ∧ X.b = b ∧ X.P.k = k ∧ X.Regs c₁ ∧ X.Fix c₁.nmem ∧
      X.Stt (X.st 0) c₁.nmem ∧ X.Img c₁.nmem ∧ Q c X c₁)
    (hfin : ∀ c (X : SLx M) c₁ c₂, Q c X c₁ → X.Good W → WordsBounded W c₂ →
      X.Stt (X.st X.P.k) c₂.nmem → X.Img c₂.nmem →
      (∀ a, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → ¬ X.Wr a → c₂.nmem a = c₁.nmem a) →
      (∀ r, ¬ SLx.scr r → c₂.nreg r = c₁.nreg r) → c₂.rreg = c₁.rreg → c₂.rmem = c₁.rmem →
      c₂.output = c₁.output →
      ∃ c₃ t₃, Exec I W finP c₂ c₃ t₃ ∧ t₃ ≤ T₃ ∧ post c c₃)
    (c : Config) (hc : pre c) (hw : WordsBounded W c) :
    ∃ c₃ t, Exec I W (.seq preP (.seq loopP finP)) c c₃ t ∧ t ≤ T₁ + loopT b k + T₃ ∧
      post c c₃ := by
  obtain ⟨c₁, t₁, X, e₁, ht₁, hG, hb, hk, hR, hFx, hS, hI, hQ⟩ := hpre c hc hw
  obtain ⟨c₂, t₂, e₂, ht₂, S2, I2, K2, R2, r2, rm2, o2⟩ :=
    SLx.loopP_exec' (I := I) hG c₁ e₁.wb_right hR hFx hS hI
  obtain ⟨c₃, t₃, e₃, ht₃, hpost⟩ :=
    hfin c X c₁ c₂ hQ hG e₂.wb_right S2 I2 K2 R2 r2 rm2 o2
  rw [hb, hk] at ht₂
  exact ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, hpost⟩

end Seq

/-! ### `FixPSpecN` from the specification of the prologue and the final step -/

namespace MfDrv

open Function Equiv Orbit WordRAM.Machine.Stmt NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **The specification of the prologue `preP` and the final step `finP` of `fixP`** at a node
call, against the stage loop: from the precondition of `FixPSpecN`, `preP` runs within
`preT x j` steps to a configuration where some `X : SLx (pmap h.1)` (with `X.b = bOf x j`,
`X.P.k = kOf x j`) meets `Good`, `Regs`, `Fix`, `Stt (X.st 0)`, `Img`; and from any configuration
that the loop can leave (the state `X.st k`, an image, the memory above the shadow outside `Wr`, the
registers outside `scr`, reals and output as after `preP`) `finP` runs within `finT x j` steps to the
postcondition of `FixPSpecN` (the flow of `O.fix`). This is the prologue's part, as a hypothesis. -/
def FixPFSpec (NF : NFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (preP finP : Stmt)
    (preT finT bOf kOf : MCall M → ℕ → ℕ) (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j : ℕ) (πj : SPath (pmap h.1)),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d →
    (xCtxN M NF u S T l r π Hs σ h).L[j]? = some πj →
    ∀ c : Config, ((c.nreg 6800 = j ∧ MemZ Wz c) ∧ SegsAt M en m π e b c) →
      Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem →
      FLHas Z m d en c.nmem ((xCtxN M NF u S T l r π Hs σ h).seg j) →
      WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = b + 5 →
      ∃ (c₁ : Config) (t₁ : ℕ) (X : SLx (pmap h.1)), Exec I W preP c c₁ t₁ ∧
        t₁ ≤ preT (.node l r π, Hs, σ) j ∧ X.Good W ∧ X.b = bOf (.node l r π, Hs, σ) j ∧
        X.P.k = kOf (.node l r π, Hs, σ) j ∧ X.Regs c₁ ∧ X.Fix c₁.nmem ∧
        X.Stt (X.st 0) c₁.nmem ∧ X.Img c₁.nmem ∧
        ∀ c₂ : Config, WordsBounded W c₂ → X.Stt (X.st X.P.k) c₂.nmem → X.Img c₂.nmem →
          (∀ a, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → ¬ X.Wr a →
            c₂.nmem a = c₁.nmem a) →
          (∀ r, ¬ SLx.scr r → c₂.nreg r = c₁.nreg r) → c₂.rreg = c₁.rreg →
          c₂.rmem = c₁.rmem → c₂.output = c₁.output →
          ∃ c₃ t₃, Exec I W finP c₂ c₃ t₃ ∧ t₃ ≤ finT (.node l r π, Hs, σ) j ∧ SRegKeep c c₃ ∧
            (∀ a, a < b → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
              c₃.nmem a = c.nmem a ∧ c₃.rmem a = c.rmem a) ∧ c₃.output = c.output ∧
            FLHas Z m d en c₃.nmem ((xCtxN M NF u S T l r π Hs σ h).O.fix
              (xCtxN M NF u S T l r π Hs σ h).U ((xCtxN M NF u S T l r π Hs σ h).seg j) πj)

/-- **`FixPSpecN` for `fixP = preP ; loopP ; finP`**, with
`fT x j = preT x j + loopT (bOf x j) (kOf x j) + finT x j`. -/
theorem fixP_specN {NF : NFam M} {Reach : MCall M → Prop} {gid : D → ℕ} {u : D → ℤ}
    {S T : Finset V} {Z : ℕ} {I : Input} {W Wz : ℕ} {preP finP : Stmt}
    {preT finT bOf kOf : MCall M → ℕ → ℕ} {rO : MCall M → ℕ}
    (hPF : FixPFSpec M NF Reach gid u S T Z I W Wz preP finP preT finT bOf kOf rO) :
    FixPSpecN M NF Reach gid u S T Z I W Wz (.seq preP (.seq loopP finP))
      (fun x j => preT x j + loopT (bOf x j) (kOf x j) + finT x j) rO := by
  intro l r π Hs σ h d e b m en j πj hR hC hde heb hbW hWz hL c hpre hLay hFL hw h4 h5 h6
  obtain ⟨c₁, t₁, X, e₁, ht₁, hG, hb, hk, hRg, hFx, hS, hI, hfin⟩ :=
    hPF l r π Hs σ h d e b m en j πj hR hC hde heb hbW hWz hL c hpre hLay hFL hw h4 h5 h6
  obtain ⟨c₂, t₂, e₂, ht₂, S2, I2, K2, R2, r2, rm2, o2⟩ :=
    SLx.loopP_exec' (I := I) hG c₁ e₁.wb_right hRg hFx hS hI
  obtain ⟨c₃, t₃, e₃, ht₃, k3, m3, o3, f3⟩ := hfin c₂ e₂.wb_right S2 I2 K2 R2 r2 rm2 o2
  rw [hb, hk] at ht₂
  exact ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by beta_reduce; omega, k3, m3, o3, f3⟩

end MfDrv

/-! ### The cost -/

/-- **The loop fits the stages' part of the scaled budget.** -/
theorem loopT_le_cMachS (C C₀ : ℕ) {b k : ℕ} (hb : 1 ≤ b) :
    loopT b k ≤ k * (cMachS C C₀).fr b (2 * k) + 3 := by
  rw [cMachS_fr]
  show _ ≤ k * (csK * (6300 * (b * lg b ^ 2 + 2 * k * lg b))) + 3
  have hl : 1 ≤ lg b := by unfold lg; omega
  have h1 : b ≤ b * lg b ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have h2 : 2 * k ≤ 2 * k * lg b := Nat.le_mul_of_pos_right _ (by omega)
  have h0 : b + 2 * k ≤ b * lg b ^ 2 + 2 * k * lg b := by omega
  unfold loopT
  generalize b * lg b ^ 2 + 2 * k * lg b = X at h0 ⊢
  have hX : 108 * (6300 * X) + 56 * b + 68 * k + 1200 + 2 ≤ csK * (6300 * X) := by
    unfold csK; omega
  have := Nat.mul_le_mul_right k hX
  rw [Nat.mul_comm k]
  omega

/-- **`fT ≤ (cMachS C C₀).fixRun …`** from the budgets of the prologue and the final step. -/
theorem fT_le_fixRun (C C₀ : ℕ) {preT finT n b k N : ℕ} (hb : 1 ≤ b)
    (h : preT + finT + 3 ≤ (cMachS C C₀).mssp n k + (cMachS C C₀).negsssp n +
      (cMachS C C₀).lin N) :
    preT + loopT b k + finT ≤ (cMachS C C₀).fixRun n b k N := by
  have := loopT_le_cMachS C C₀ (k := k) hb
  unfold SubCosts.fixRun
  have : k * (cMachS C C₀).fr b (2 * k) ≤ k * ((cMachS C C₀).fr b (2 * k) + (cMachS C C₀).lin b) :=
    Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  omega

end BKMNW

end PlanarFlow
