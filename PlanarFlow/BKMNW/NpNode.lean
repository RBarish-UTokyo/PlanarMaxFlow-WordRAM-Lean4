module

public import PlanarFlow.BKMNW.NpStep
public import PlanarFlow.BKMNW.MfDrvX

/-!
# The node step on the extended frame: the parts of the separator, then `stepPO`

The step `stepPO` needs the parts of the separator (`SegsAt`, `NpCntM.lean`). The split's output
does not survive the children's runs, and the field `node` of `MfSpecRC` receives only `FIn` of
the node, i.e. on the extended frame **`FInLX`** (frame and decomposition record). So the node
program reruns the separator (or anything else producing the parts) from `FInLX`:

* **`SegPSpec`**: a program `segP` which, at a node call with `FInLX`, writes `SegsAt` in
  `[e, b')` above the heap top `b` (`b ≤ b' ≤ b + sgR x`), sets the heap top of the step to `b'`
  (`r3006 = b' + 5`), saves `b + 5` in `r6808`, and keeps the memory below `b` (to be met from
  `SepPSpecXS`, the separator's specification with `SegsOut`, plus a copy loop);
* `rsP` (`r3006 := r6808`), **`stepX segP stepP = segP ; stepP ; rsP`**, `StepPSpecCX`
  (`StepPSpecC'` on the extended frame), **`stepX_spec`**: `SegPSpec segP` and
  `StepPSpecCS stepP` ⇒ `StepPSpecCX (stepX segP stepP)`, steps `sgT + stT + 1`, room `sgR + rT`;
* `FInLX.congrFL` (the extended frame does not depend on the flow array),
  **`nodeSF_specCX`**: `StepPSpecCX` ⇒ the field `NodeFieldZ` of `nodeSF stepP` with
  `FIn = FInLX`, `FOut = FOutL`, `G = MemZ Wz`.
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

/-- Restore the heap top of the node: `r3006 := r6808`. -/
def rsP : Stmt := block [.copyN 3006 6808]

/-- **The node step on the extended frame**: the parts of the separator, the step, the heap top
restored. -/
def stepX (segP stepP : Stmt) : Stmt := .seq segP (.seq stepP rsP)

theorem rsP_exec {P : Input} {W : ℕ} (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W rsP c c' t ∧ t = 1 ∧ c'.nreg 3006 = c.nreg 6808 ∧
      (∀ x, x ≠ 3006 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rsP
  exec_block
  refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

section Spec

variable (M) in
/-- **The parts of the separator at the node** (the program run before `stepPO`): from the
extended frame of a node call (`FInLX`, any flow array), within `sgT x` steps, the parts
`SegsAt` in `[e, b')` for a new heap top `b' ∈ [b, b + sgR x]` in `r3006` (`b' + 5`), the old one
saved in `r6808`; the memory and the reals below `b`, the other registers of the driver and the
output kept. -/
def SegPSpec (ds : DSys M) (Reach : MCall M → Prop) (gid : D → ℕ) (ν : V → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (segP : Stmt) (sgT sgR : MCall M → ℕ) :
    Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e b m : ℕ)
    (en : ℕ → D) (c : Config),
    FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem → d + fsz m ≤ e → e ≤ b →
    b + sgR (.node l r π, Hs, σ) ≤ W → WordsBounded W c → c.nreg 3004 = d →
    c.nreg 3005 = e → c.nreg 3006 = b + 5 →
    ∃ c' t b', Exec I W segP c c' t ∧ t ≤ sgT (.node l r π, Hs, σ) ∧ b ≤ b' ∧
      b' ≤ b + sgR (.node l r π, Hs, σ) ∧
      (∀ x, 3000 ≤ x → x ≤ 3012 → x ≠ 3006 → c'.nreg x = c.nreg x) ∧
      c'.nreg 3006 = b' + 5 ∧ c'.nreg 6808 = b + 5 ∧
      (∀ a, a < b → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      SegsAt M en m π e b' c'

variable (M) in
/-- **The step on the extended frame**: `StepPSpecC'` with `FInLX` of the node (instead of its
reachability and `CallOk`). -/
def StepPSpecCX (ds : DSys M) (cf : CFlow M) (Reach : MCall M → Prop) (gid : D → ℕ) (ν : V → ℕ)
    (u : D → ℤ) (S T : Finset V) (Z : ℕ) (I : Input) (W Wz : ℕ) (stepP : Stmt)
    (stT rT : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e b m : ℕ)
    (en : ℕ → D) (c : Config),
    FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem → d + fsz m ≤ e →
    (∀ i < m, (c.nmem (d + 4 + 6 * m + i) : ℤ) =
      Z + fext (joinFlow (B := pdarts M (l.piece ∪ r.piece) Hs)
        (cf (chL M l r π Hs σ)) (cf (chR M l r π Hs σ))) (en i)) →
    WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = b + 5 → e ≤ b →
    b + rT (.node l r π, Hs, σ) ≤ W → Wz < d → MemZ Wz c →
    ∃ c' t, Exec I W stepP c c' t ∧ t ≤ stT (.node l r π, Hs, σ) ∧ DRegKeep c c' ∧
      (∀ a, a < b → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      ∀ i < m, (c'.nmem (d + 4 + 6 * m + i) : ℤ) =
        Z + fext (cf (.node l r π, Hs, σ)) (en i)

end Spec

section Proofs

variable {ds : DSys M} {cf : CFlow M} {Reach : MCall M → Prop} {gid : D → ℕ} {ν : V → ℕ}
  {u : D → ℤ} {S T : Finset V} {Z : ℕ} {I : Input} {W Wz Hb : ℕ}
  {segP stepP : Stmt} {sgT sgR stT rT rS : MCall M → ℕ}

/-- **The parts, then the step, then the heap top restored.** -/
theorem stepX_spec (hsg : SegPSpec M ds Reach gid ν u S T Z I W segP sgT sgR)
    (hst : StepPSpecCS M cf Reach gid u S T Z I W Wz stepP stT rT) :
    StepPSpecCX M ds cf Reach gid ν u S T Z I W Wz (stepX segP stepP)
      (fun x => sgT x + stT x + 1) (fun x => sgR x + rT x) := by
  intro l r π Hs σ d e b m en c hin hL hde hfl hc r4 r5 r6 heb hroom hWd hz
  have hR := hin.1
  have hok := hin.2.1
  unfold fsz at hde
  obtain ⟨c₁, t₁, b', e₁, ht₁, hbb, hb', K₁, s6, s8, m₁, o₁, hsa⟩ :=
    hsg l r π Hs σ d e b m en c hin hL (by unfold fsz; omega) heb (by simp only at hroom; omega)
      hc r4 r5 r6
  have hL₁ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₁.nmem :=
    hL.congr fun a h1 h2 => (m₁ a (by omega)).1
  have hfl₁ : ∀ i < m, (c₁.nmem (d + 4 + 6 * m + i) : ℤ) =
      Z + fext (joinFlow (B := pdarts M (l.piece ∪ r.piece) Hs)
        (cf (chL M l r π Hs σ)) (cf (chR M l r π Hs σ))) (en i) := fun i hi => by
    rw [(m₁ _ (by omega)).1]; exact hfl i hi
  have hz₁ : MemZ Wz c₁ := hz.of_eq fun a ha => (m₁ a (by omega)).1
  obtain ⟨c₂, t₂, e₂, ht₂, dk₂, kr₂, m₂, o₂, fl₂⟩ := hst l r π Hs σ d e b' m en c₁ hR hok hL₁ hsa
    (by unfold fsz; omega) hfl₁ e₁.wb_right (by rw [K₁ _ (by omega) (by omega) (by omega), r4])
    (by rw [K₁ _ (by omega) (by omega) (by omega), r5]) s6 (by omega)
    (by simp only at hroom; omega) hWd hz₁
  obtain ⟨c₃, t₃, e₃, ht₃, q6, K₃, m₃, rr₃, rm₃, o₃⟩ := rsP_exec (P := I) c₂ e₂.wb_right
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by simp only; omega, fun x h1 h2 => ?_,
    fun a h1 h2 => ?_, by rw [o₃, o₂, o₁], fun i hi => by rw [m₃]; exact fl₂ i hi⟩
  · by_cases hx : x = 3006
    · subst hx; rw [q6, kr₂ _ (by omega) (by omega), s8, r6]
    · rw [K₃ x hx, dk₂ x h1 h2, K₁ x h1 h2 hx]
  · obtain ⟨a1, a2⟩ := m₂ a (by omega) h2
    obtain ⟨b1, b2⟩ := m₁ a h1
    exact ⟨by rw [m₃, a1, b1], by rw [rm₃, a2, b2]⟩

/-- **The extended frame does not depend on the flow array.** -/
lemma FInLX.congrFL {x : MCall M} {d e : ℕ} {c c' : Config}
    (h : FInLX M ds Reach gid ν u S T Z x d e c)
    (hm : ∀ a, d ≤ a → a < e → ¬ (d + 4 + 6 * c.nmem d ≤ a ∧ a < d + 4 + 6 * c.nmem d + c.nmem d) →
      c'.nmem a = c.nmem a) :
    FInLX M ds Reach gid ν u S T Z x d e c' := by
  obtain ⟨hr, ho, m, en, n, g, hL, h1, h2, hR⟩ := h
  have hmd : c.nmem d = m := hL.hm
  rw [hmd] at hm
  have hf : fsz m = 4 + 7 * m := rfl
  set R := c.nmem (d + fsz m) with hRdef
  have h3 := three_le_rszL (c.nmem (R + 1)) n m
  have hp : c'.nmem (d + fsz m) = R := hm _ (by omega) (by omega) (by omega)
  have hp1 : c'.nmem (R + 1) = c.nmem (R + 1) := hm _ (by omega) (by omega) (by omega)
  refine ⟨hr, ho, m, en, n, g, hL.congr fun a a1 a2 => hm a a1 (by omega) (by omega),
    by rw [hp]; exact h1, by rw [hp, hp1]; exact h2, ?_⟩
  rw [hp]
  exact hR.congrL fun a a1 a2 => hm a (by omega) (by omega) (by omega)

/-- **The combination on the extended frame with the zero-memory invariant** (`nodeSF_specC'`
with `FInLX`). -/
theorem nodeSF_specCX (hst : StepPSpecCX M ds cf Reach gid ν u S T Z I W Wz stepP stT rT)
    (hWz : Wz < Hb) :
    NodeFieldZ M cf I W Hb Wz (nodeSF stepP) (FInLX M ds Reach gid ν u S T Z)
      (FOutL M gid u S T Z) (ncF M stT) rS rT := by
  intro l r π Hs σ d e bl el er c hz hc r4 r5 r6 r7 r8 r9 r3 hd1 hde hebl hbl hel hroom hin hl hr
  obtain ⟨c₁, t₁, m, en, e₁, ht₁, hL₁, hfs, hfl₁, hm₁, hr₁, hrr₁, hrm₁, ho₁⟩ :=
    njProg_join (I := I) l r π Hs σ c hc r4 r6 r8 r9 hebl hbl hel hin.finL hl hr
  have hw₁ := e₁.wb_right
  have hmd : c.nmem d = m := by
    rw [← hm₁ d (by omega) (fun h => by unfold fsz at hfs; omega)]; exact hL₁.hm
  have hin₁ : FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c₁ :=
    hin.congrFL fun a h1 h2 h3 => hm₁ a (by omega) (by rw [hmd] at h3; exact h3)
  have hz₁ : MemZ Wz c₁ := hz.of_eq fun a ha => hm₁ a (by omega) (fun h => by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, dk₂, hm₂, ho₂, hfl₂⟩ := hst l r π Hs σ d e bl m en c₁ hin₁ hL₁ hfs
    hfl₁ hw₁ (by rw [hr₁ _ (by omega), r4]) (by rw [hr₁ _ (by omega), r5])
    (by rw [hr₁ _ (by omega), r6]) hebl (by omega) (by omega) hz₁
  have hm : m = (pdarts M (l.piece ∪ r.piece) Hs).card := hL₁.card
  unfold fsz at hfs
  have hz₂ : MemZ Wz c₂ := hz₁.of_eq fun a ha => (hm₂ a (by omega) (fun h => by omega)).1
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, ?_, hz₂, fun x hx1 hx2 => ?_, fun a ha1 ha2 ha3 => ?_,
    by rw [ho₂, ho₁], m, en, hL₁.congr fun a h1 h2 => (hm₂ a (by omega) (by omega)).1,
    by unfold fsz; omega, hfl₂⟩
  · unfold ncF; simp only [ADec.piece]; rw [← hm]; omega
  · rw [dk₂ x hx1 hx2, hr₁ x (by omega)]
  · have hnot : ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) := fun h => by omega
    obtain ⟨a1, a2⟩ := hm₂ a ha2 hnot
    exact ⟨by rw [a1, hm₁ a (by omega) hnot], by rw [a2, hrm₁]⟩

end Proofs

end MfDrv

end BKMNW

end PlanarFlow
