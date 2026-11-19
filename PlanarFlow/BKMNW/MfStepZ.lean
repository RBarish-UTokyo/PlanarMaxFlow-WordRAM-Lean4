module

public import PlanarFlow.BKMNW.MfZero
public import PlanarFlow.BKMNW.MfStepO

/-!
# The step program `stepPO` with the zero-memory invariant

The specifications of `MfStepO.lean` (`FixPSpecO` … `FrmPSpecO`) quantify over all the
configurations holding the frame, with no hypothesis on the memory below the frames, so a
subroutine program calling the in-place `negCallZ` (which needs the memory `≤ Wz` zero) cannot
meet them. Here they are restated with the extra precondition **`MemZ Wz`** (and `Wz < d`):
**`FixPSpecO'`**, **`C2SPSpecO'`**, **`S2CPSpecO'`**, **`RetPSpecO'`**, **`FrmPSpecO'`** (the
`pre` of `FlowProg` is the old one `∧ MemZ Wz c`). Since `FlowProg` keeps the memory below `b`
outside the flow array, the invariant holds at every call of the step
(`StInv.memZ`). `CntPSpec` is unchanged.

* `holeLoopP_execO'`, `segBodyP_execO'`, **`stepPO_specO'`**: the six specifications ⇒ `stepPO`
  meets `StepPSpecC'` for the flows `cflowO` of `arunLO`, with the same steps `stTO` and room
  `rO`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs NegSSSP.Driver

universe w

/-- The state of the step keeps the zero memory below the frame. -/
lemma StInv.memZ {c₀ c : Config} {d m b Wz : ℕ} (hS : StInv c₀ c d m b) (hz : MemZ Wz c₀)
    (hWd : Wz < d) (hWb : Wz < b) : MemZ Wz c :=
  hz.of_eq fun a ha => (hS.2.1 a (by omega) (fun h => by omega)).1

section Spec

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **FixConservationOnPath on the part `j`** (`r6800 = j`), with the memory `≤ Wz` zero. -/
def FixPSpecO' (NO : MOFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (fixP : Stmt) (fT : MCall M → ℕ → ℕ)
    (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j : ℕ) (πj : SPath (pmap h.1)),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d →
    (xCtxO M NO u S T l r π Hs σ h).L[j]? = some πj →
    FlowProg M gid u S T Z I W fixP (.node l r π, Hs, σ) m en d e b
      (fun c => c.nreg 6800 = j ∧ MemZ Wz c)
      ((xCtxO M NO u S T l r π Hs σ h).seg j)
      ((xCtxO M NO u S T l r π Hs σ h).O.fix (xCtxO M NO u S T l r π Hs σ h).U
        ((xCtxO M NO u S T l r π Hs σ h).seg j) πj) (fT (.node l r π, Hs, σ) j)

variable (M) in
/-- **CycleToSingleSinkLimitedMaxFlow on the hole `i` of the part `j`** (`r6800 = j`,
`r6802 = i`), with the memory `≤ Wz` zero. -/
def C2SPSpecO' (NO : MOFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (c2sP : Stmt) (cT : MCall M → ℕ → ℕ → ℕ)
    (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j i : ℕ) (πj : SPath (pmap h.1))
    (H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d →
    (xCtxO M NO u S T l r π Hs σ h).L[j]? = some πj →
    ((xCtxO M NO u S T l r π Hs σ h).holes j)[i]? = some H →
    FlowProg M gid u S T Z I W c2sP (.node l r π, Hs, σ) m en d e b
      (fun c => (c.nreg 6800 = j ∧ c.nreg 6802 = i) ∧ MemZ Wz c)
      ((xCtxO M NO u S T l r π Hs σ h).hole j πj i)
      ((xCtxO M NO u S T l r π Hs σ h).c2s j πj i H) (cT (.node l r π, Hs, σ) j i)

variable (M) in
/-- **SingleSourceToCycleLimitedMaxFlow on the hole `i` of the part `j`** (`r6800 = j`,
`r6802 = i`), with the memory `≤ Wz` zero. -/
def S2CPSpecO' (NO : MOFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (s2cP : Stmt) (sT : MCall M → ℕ → ℕ → ℕ)
    (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j i : ℕ) (πj : SPath (pmap h.1))
    (H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d →
    (xCtxO M NO u S T l r π Hs σ h).L[j]? = some πj →
    ((xCtxO M NO u S T l r π Hs σ h).holes j)[i]? = some H →
    FlowProg M gid u S T Z I W s2cP (.node l r π, Hs, σ) m en d e b
      (fun c => (c.nreg 6800 = j ∧ c.nreg 6802 = i) ∧ MemZ Wz c)
      ((xCtxO M NO u S T l r π Hs σ h).c2s j πj i H)
      ((xCtxO M NO u S T l r π Hs σ h).O.s2c (xCtxO M NO u S T l r π Hs σ h).U
        ((xCtxO M NO u S T l r π Hs σ h).c2s j πj i H) πj H) (sT (.node l r π, Hs, σ) j i)

variable (M) in
/-- **The push-back of the excess to the sources** on the part `j` (`r6800 = j`), with the
memory `≤ Wz` zero. -/
def RetPSpecO' (NO : MOFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (retP : Stmt) (rtT : MCall M → ℕ → ℕ)
    (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j : ℕ) (πj : SPath (pmap h.1)),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d →
    (xCtxO M NO u S T l r π Hs σ h).L[j]? = some πj →
    FlowProg M gid u S T Z I W retP (.node l r π, Hs, σ) m en d e b
      (fun c => c.nreg 6800 = j ∧ MemZ Wz c)
      ((xCtxO M NO u S T l r π Hs σ h).hole j πj ((xCtxO M NO u S T l r π Hs σ h).holes j).length)
      ((xCtxO M NO u S T l r π Hs σ h).ret j πj) (rtT (.node l r π, Hs, σ) j)

variable (M) in
/-- **The push-back from the sinks** on the part `j` (`r6800 = j`), with the memory `≤ Wz` zero. -/
def FrmPSpecO' (NO : MOFam M) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (frmP : Stmt) (fmT : MCall M → ℕ → ℕ)
    (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j : ℕ) (πj : SPath (pmap h.1)),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → Wz < d →
    (xCtxO M NO u S T l r π Hs σ h).L[j]? = some πj →
    FlowProg M gid u S T Z I W frmP (.node l r π, Hs, σ) m en d e b
      (fun c => c.nreg 6800 = j ∧ MemZ Wz c)
      ((xCtxO M NO u S T l r π Hs σ h).ret j πj)
      ((xCtxO M NO u S T l r π Hs σ h).O.frm (xCtxO M NO u S T l r π Hs σ h).U
        ((xCtxO M NO u S T l r π Hs σ h).ret j πj) (xCtxO M NO u S T l r π Hs σ h).T
        (negSet (pmap h.1) ((xCtxO M NO u S T l r π Hs σ h).ret j πj) πj.verts))
      (fmT (.node l r π, Hs, σ) j)

end Spec

section Run

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {I : Input} {W Wz : ℕ}

variable {NO : MOFam M} {Reach : MCall M → Prop}
  {cntP fixP c2sP s2cP retP frmP : Stmt} {cnT rO : MCall M → ℕ}
  {fT rtT fmT : MCall M → ℕ → ℕ} {cT sT : MCall M → ℕ → ℕ → ℕ}

/-- **The hole loop of the part `j`** with the zero-memory invariant. -/
theorem holeLoopP_execO' (hc2 : C2SPSpecO' M NO Reach gid u S T Z I W Wz c2sP cT rO)
    (hs2 : S2CPSpecO' M NO Reach gid u S T Z I W Wz s2cP sT rO)
    {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D} (h : SCond M l r π Hs σ)
    {d e b m : ℕ} {en : ℕ → D} {j : ℕ} {πj : SPath (pmap h.1)}
    (hR : Reach (.node l r π, Hs, σ)) (hok : CallOk M S T (.node l r π, Hs, σ))
    (hde : d + fsz m ≤ e) (heb : e ≤ b) (hroom : b + rO (.node l r π, Hs, σ) ≤ W)
    (hWd : Wz < d)
    (hj : (xCtxO M NO u S T l r π Hs σ h).L[j]? = some πj) {c₀ : Config}
    (hz₀ : MemZ Wz c₀)
    (hL₀ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₀.nmem)
    (r4 : c₀.nreg 3004 = d) (r5 : c₀.nreg 3005 = e) (r6 : c₀.nreg 3006 = b + 5) (c : Config)
    (hc : WordsBounded W c) (hS : StInv c₀ c d m b) (q0 : c.nreg 6800 = j)
    (q2 : c.nreg 6802 = 0) (q3 : c.nreg 6803 = ((xCtxO M NO u S T l r π Hs σ h).holes j).length)
    (q5 : c.nreg 6805 = 1)
    (hfl : FLHas Z m d en c.nmem ((xCtxO M NO u S T l r π Hs σ h).hole j πj 0)) :
    ∃ c' t, Exec I W (.whileLtN 6802 6803 (holeBodyP c2sP s2cP)) c c' t ∧
      t ≤ hlCost cT sT (.node l r π, Hs, σ) j ((xCtxO M NO u S T l r π Hs σ h).holes j).length + 2 ∧
      StInv c₀ c' d m b ∧
      (∀ r, 6800 ≤ r → r ≤ 6819 → r ≠ 6802 → c'.nreg r = c.nreg r) ∧
      FLHas Z m d en c'.nmem
        ((xCtxO M NO u S T l r π Hs σ h).hole j πj
          ((xCtxO M NO u S T l r π Hs σ h).holes j).length) := by
  set C := xCtxO M NO u S T l r π Hs σ h with hC
  set nH := (C.holes j).length with hnH
  have hnW : nH ≤ W := by rw [← q3]; exact WordsBounded.nreg hc 6803
  have hWb : Wz < b := by unfold fsz at hde; omega
  let J : ℕ → Config → Prop := fun i c' =>
    StInv c₀ c' d m b ∧ (∀ r, 6800 ≤ r → r ≤ 6819 → r ≠ 6802 → c'.nreg r = c.nreg r) ∧
      FLHas Z m d en c'.nmem (C.hole j πj i)
  obtain ⟨c', k, ex, hk, -, -, hJ1, hJ2, hJ3⟩ := lnRangeV (P := I) (W := W) (a := 6802)
    (b := 6803) (body := holeBodyP c2sP s2cP) J (lo := 0) (hi := nH)
    (fun i => cT (.node l r π, Hs, σ) j i + sT (.node l r π, Hs, σ) j i + 1) c hc q2 q3
    (Nat.zero_le _) ⟨hS, fun _ _ _ _ => rfl, hfl⟩
    (fun i c₁ _ hi hw₁ a2 a3 ⟨S₁, K₁, F₁⟩ => by
      obtain ⟨H, hH⟩ : ∃ H, (C.holes j)[i]? = some H :=
        ⟨(C.holes j)[i], List.getElem?_eq_getElem hi⟩
      have p0 : c₁.nreg 6800 = j := by rw [K₁ _ (by omega) (by omega) (by omega), q0]
      obtain ⟨c₂, t₂, e₂, ht₂, S₂, K₂, F₂⟩ := flow_step
        (hc2 l r π Hs σ h d e b m en j i πj H hR hok hde heb hroom hWd hj hH) hL₀ hde heb r4 r5
        r6 c₁ hw₁ S₁ ⟨⟨p0, a2⟩, S₁.memZ hz₀ hWd hWb⟩ F₁
      obtain ⟨c₃, t₃, e₃, ht₃, S₃, K₃, F₃⟩ := flow_step
        (hs2 l r π Hs σ h d e b m en j i πj H hR hok hde heb hroom hWd hj hH) hL₀ hde heb r4 r5
        r6 c₂ e₂.wb_right S₂ ⟨⟨by rw [K₂ _ (by omega) (by omega), p0],
          by rw [K₂ _ (by omega) (by omega), a2]⟩, S₂.memZ hz₀ hWd hWb⟩ F₂
      have p2 : c₃.nreg 6802 = i := by
        rw [K₃ _ (by omega) (by omega), K₂ _ (by omega) (by omega), a2]
      have p5 : c₃.nreg 6805 = 1 := by
        rw [K₃ _ (by omega) (by omega), K₂ _ (by omega) (by omega),
          K₁ _ (by omega) (by omega) (by omega), q5]
      obtain ⟨c₄, t₄, e₄, ht₄, p2', K₄, m₄, rr₄, rm₄, o₄⟩ := stI_exec (P := I) c₃ e₃.wb_right p2 p5
        (by omega)
      refine ⟨c₄, t₂ + (t₃ + t₄), .seq e₂ (.seq e₃ e₄), by omega, p2', ?_, ?_⟩
      · rw [K₄ _ (by omega), K₃ _ (by omega) (by omega), K₂ _ (by omega) (by omega)]; exact a3
      · refine ⟨S₃.of_block (fun x h1 h2 => K₄ x (by omega)) m₄ rm₄ o₄, fun x h1 h2 h3 => ?_, ?_⟩
        · rw [K₄ x h3, K₃ x h1 h2, K₂ x h1 h2, K₁ x h1 h2 h3]
        · rw [m₄, C.hole_succ hH]; exact F₃)
  refine ⟨c', k, ex, ?_, hJ1, hJ2, hJ3⟩
  unfold hlCost; rw [range_eq_Ico]; exact hk

/-- **One part of the separator** with the zero-memory invariant. -/
theorem segBodyP_execO' (hfx : FixPSpecO' M NO Reach gid u S T Z I W Wz fixP fT rO)
    (hc2 : C2SPSpecO' M NO Reach gid u S T Z I W Wz c2sP cT rO)
    (hs2 : S2CPSpecO' M NO Reach gid u S T Z I W Wz s2cP sT rO)
    (hrt : RetPSpecO' M NO Reach gid u S T Z I W Wz retP rtT rO)
    (hfm : FrmPSpecO' M NO Reach gid u S T Z I W Wz frmP fmT rO)
    {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D} (h : SCond M l r π Hs σ)
    {d e b m : ℕ} {en : ℕ → D} {j : ℕ}
    (hR : Reach (.node l r π, Hs, σ)) (hok : CallOk M S T (.node l r π, Hs, σ))
    (hde : d + fsz m ≤ e) (heb : e ≤ b) (hroom : b + rO (.node l r π, Hs, σ) ≤ W)
    (hWd : Wz < d)
    (hj : j < (xCtxO M NO u S T l r π Hs σ h).L.length) {c₀ : Config} (hz₀ : MemZ Wz c₀)
    (hL₀ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₀.nmem)
    (r4 : c₀.nreg 3004 = d) (r5 : c₀.nreg 3005 = e) (r6 : c₀.nreg 3006 = b + 5) (c : Config)
    (hc : WordsBounded W c) (hS : StInv c₀ c d m b) (q0 : c.nreg 6800 = j)
    (q5 : c.nreg 6805 = 1)
    (q6 : c.nreg 6806 = (xCtxO M NO u S T l r π Hs σ h).Hs.length +
      (xCtxO M NO u S T l r π Hs σ h).L.length)
    (hfl : FLHas Z m d en c.nmem ((xCtxO M NO u S T l r π Hs σ h).seg j)) :
    ∃ c' t, Exec I W (segBodyP fixP c2sP s2cP retP frmP) c c' t ∧
      t ≤ sgCost fT cT sT rtT fmT (.node l r π, Hs, σ) j
        ((xCtxO M NO u S T l r π Hs σ h).Hs.length +
          ((xCtxO M NO u S T l r π Hs σ h).L.length - (j + 1))) ∧
      StInv c₀ c' d m b ∧ c'.nreg 6800 = j + 1 ∧
      (∀ x, 6800 ≤ x → x ≤ 6819 → x ≠ 6800 → x ≠ 6802 → x ≠ 6803 → c'.nreg x = c.nreg x) ∧
      FLHas Z m d en c'.nmem ((xCtxO M NO u S T l r π Hs σ h).seg (j + 1)) := by
  set C := xCtxO M NO u S T l r π Hs σ h with hC
  set πj := C.L[j] with hπj
  have hj' : C.L[j]? = some πj := List.getElem?_eq_getElem hj
  have hlen : (C.holes j).length = C.Hs.length + (C.L.length - (j + 1)) :=
    length_sHoles C.Hs C.L j
  have hWb : Wz < b := by unfold fsz at hde; omega
  -- FixConservationOnPath
  obtain ⟨c₁, t₁, e₁, ht₁, S₁, K₁, F₁⟩ := flow_step
    (hfx l r π Hs σ h d e b m en j πj hR hok hde heb hroom hWd hj') hL₀ hde heb r4 r5 r6 c hc hS
    ⟨q0, hS.memZ hz₀ hWd hWb⟩ hfl
  -- the bound of the hole loop
  obtain ⟨c₂, t₂, e₂, ht₂, p2, p3, K₂, m₂, rr₂, rm₂, o₂⟩ := stH_exec (P := I) c₁ e₁.wb_right
    (N := C.Hs.length + C.L.length) (j := j)
    (by rw [K₁ _ (by omega) (by omega), q6]) (by rw [K₁ _ (by omega) (by omega), q0])
    (by rw [K₁ _ (by omega) (by omega), q5])
  have S₂ := S₁.of_block (fun x h1 h2 => K₂ x (by omega) (by omega)) m₂ rm₂ o₂
  have p3' : c₂.nreg 6803 = (C.holes j).length := by rw [p3, hlen]; omega
  have k2 : ∀ x, 6800 ≤ x → x ≤ 6819 → x ≠ 6802 → x ≠ 6803 → c₂.nreg x = c.nreg x :=
    fun x h1 h2 h3 h4 => by rw [K₂ x h3 h4, K₁ x h1 h2]
  -- the hole loop
  obtain ⟨c₃, t₃, e₃, ht₃, S₃, K₃, F₃⟩ := holeLoopP_execO' hc2 hs2 h hR hok hde heb hroom hWd
    hj' hz₀ hL₀ r4 r5 r6 c₂ e₂.wb_right S₂
    (by rw [k2 _ (by omega) (by omega) (by omega) (by omega), q0])
    p2 p3' (by rw [k2 _ (by omega) (by omega) (by omega) (by omega), q5])
    (by rw [m₂]; exact F₁)
  have k3 : ∀ x, 6800 ≤ x → x ≤ 6819 → x ≠ 6802 → x ≠ 6803 → c₃.nreg x = c.nreg x :=
    fun x h1 h2 h3 h4 => by rw [K₃ x h1 h2 h3, k2 x h1 h2 h3 h4]
  -- the two push-backs
  obtain ⟨c₄, t₄, e₄, ht₄, S₄, K₄, F₄⟩ := flow_step
    (hrt l r π Hs σ h d e b m en j πj hR hok hde heb hroom hWd hj') hL₀ hde heb r4 r5 r6 c₃
    e₃.wb_right S₃ ⟨by rw [k3 _ (by omega) (by omega) (by omega) (by omega), q0],
      S₃.memZ hz₀ hWd hWb⟩ F₃
  obtain ⟨c₅, t₅, e₅, ht₅, S₅, K₅, F₅⟩ := flow_step
    (hfm l r π Hs σ h d e b m en j πj hR hok hde heb hroom hWd hj') hL₀ hde heb r4 r5 r6 c₄
    e₄.wb_right S₄ ⟨by rw [K₄ _ (by omega) (by omega), k3 _ (by omega) (by omega) (by omega)
      (by omega), q0], S₄.memZ hz₀ hWd hWb⟩ F₄
  have k5 : ∀ x, 6800 ≤ x → x ≤ 6819 → x ≠ 6802 → x ≠ 6803 → c₅.nreg x = c.nreg x :=
    fun x h1 h2 h3 h4 => by rw [K₅ x h1 h2, K₄ x h1 h2, k3 x h1 h2 h3 h4]
  have hjW : j + 1 ≤ W := by
    have := WordsBounded.nreg hc 6806
    rw [q6] at this; omega
  -- `j := j + 1`
  obtain ⟨c₆, t₆, e₆, ht₆, p0, K₆, m₆, rr₆, rm₆, o₆⟩ := stJ_exec (P := I) c₅ e₅.wb_right
    (by rw [k5 _ (by omega) (by omega) (by omega) (by omega), q0])
    (by rw [k5 _ (by omega) (by omega) (by omega) (by omega), q5]) hjW
  refine ⟨c₆, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ?_,
    S₅.of_block (fun x h1 h2 => K₆ x (by omega)) m₆ rm₆ o₆, p0,
    fun x h1 h2 h3 h4 h5 => by rw [K₆ x h3, k5 x h1 h2 h4 h5], ?_⟩
  · unfold sgCost
    rw [← hlen]
    rw [← hC] at ht₃
    omega
  · rw [m₆, C.seg_succ hj' (xCtxO_touch NO u S T h j)]
    exact F₅

/-- **The step program meets `StepPSpecC'` for the flows of `arunLO`** (`stepPO_specO` with the
zero-memory invariant: the five subroutine programs may assume the memory `≤ Wz` zero). -/
theorem stepPO_specO' (hcn : CntPSpec M Reach gid u S T Z I W cntP cnT rO)
    (hfx : FixPSpecO' M NO Reach gid u S T Z I W Wz fixP fT rO)
    (hc2 : C2SPSpecO' M NO Reach gid u S T Z I W Wz c2sP cT rO)
    (hs2 : S2CPSpecO' M NO Reach gid u S T Z I W Wz s2cP sT rO)
    (hrt : RetPSpecO' M NO Reach gid u S T Z I W Wz retP rtT rO)
    (hfm : FrmPSpecO' M NO Reach gid u S T Z I W Wz frmP fmT rO) :
    StepPSpecC' M (cflowO M NO u S T) Reach gid u S T Z I W Wz
      (stepPO cntP fixP c2sP s2cP retP frmP) (stTO M cnT fT cT sT rtT fmT) rO := by
  intro l r π Hs σ d e b m en c hR hok hL hde hfl hc r4 r5 r6 heb hroom hWd hz
  have h : SCond M l r π Hs σ := callOk_cond hok
  set C := xCtxO M NO u S T l r π Hs σ h with hC
  have hLs : C.L.length = π.segs.length := length_segsP h.1 π.segs h.2
  unfold fsz at hde
  -- the counts
  obtain ⟨c₁, t₁, e₁, ht₁, K₁, m₁, o₁, q1, q6⟩ := hcn l r π Hs σ d e b m en c hR hok hL
    (by unfold fsz; omega) heb hroom hc r4 r5 r6
  have S₁ : StInv c c₁ d m b :=
    ⟨fun x h1 h2 => K₁ x h1 h2, fun a h1 _ => m₁ a h1, o₁⟩
  have hfl₁ : FLHas Z m d en c₁.nmem (C.seg 0) := fun i hi => by
    rw [(m₁ _ (by omega)).1]; exact hfl i hi
  -- the initialization
  obtain ⟨c₂, t₂, e₂, ht₂, p5, p0, K₂, m₂, rr₂, rm₂, o₂⟩ := stA_exec (P := I) c₁ e₁.wb_right
    (by have := WordsBounded.nreg hc 3006; omega)
  have S₂ := S₁.of_block (fun x h1 h2 => K₂ x (by omega) (by omega)) m₂ rm₂ o₂
  -- the loop over the parts
  let J : ℕ → Config → Prop := fun j c' =>
    StInv c c' d m b ∧ c'.nreg 6805 = 1 ∧ c'.nreg 6806 = C.Hs.length + C.L.length ∧
      FLHas Z m d en c'.nmem (C.seg j)
  obtain ⟨c₃, t₃, e₃, ht₃, -, -, S₃, -, -, F₃⟩ := lnRangeV (P := I) (W := W) (a := 6800)
    (b := 6801) (body := segBodyP fixP c2sP s2cP retP frmP) J (lo := 0) (hi := C.L.length)
    (fun j => sgCost fT cT sT rtT fmT (.node l r π, Hs, σ) j
      (C.Hs.length + (C.L.length - (j + 1)))) c₂ e₂.wb_right p0
    (by rw [K₂ _ (by omega) (by omega), q1, hLs]) (Nat.zero_le _)
    ⟨S₂, p5, by rw [K₂ _ (by omega) (by omega), q6, hLs]; rfl, by rw [m₂]; exact hfl₁⟩
    (fun j c' _ hj hw a1 a2 ⟨Sj, s5, s6, Fj⟩ => by
      obtain ⟨c'', t, ex, ht, S', p0', K', F'⟩ := segBodyP_execO' hfx hc2 hs2 hrt hfm h hR hok
        (by unfold fsz; omega) heb hroom hWd hj hz hL r4 r5 r6 c' hw Sj a1 s5 s6 Fj
      exact ⟨c'', t, ex, ht, p0', by rw [K' _ (by omega) (by omega) (by omega) (by omega)
        (by omega), a2], S', by rw [K' _ (by omega) (by omega) (by omega) (by omega)
        (by omega), s5], by rw [K' _ (by omega) (by omega) (by omega) (by omega) (by omega),
        s6], F'⟩)
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), ?_, fun x h1 h2 => S₃.1 x h1 h2,
    fun a h1 h2 => S₃.2.1 a h1 h2, S₃.2.2, ?_⟩
  · show _ ≤ stCost cnT fT cT sT rtT fmT (.node l r π, Hs, σ) π.segs.length
      (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length
    unfold stCost
    rw [← hLs, range_eq_Ico]
    have : C.Hs = pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs := rfl
    rw [← this]
    omega
  · intro i hi
    rw [cflowO_node_eq NO u S T h, ← hLs]
    exact F₃ i hi

end Run

end MfDrv

end BKMNW

end PlanarFlow
