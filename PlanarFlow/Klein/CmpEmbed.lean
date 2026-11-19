module

public import WordRAM.Machine.RealsModNat
public import PlanarFlow.Klein.ModNat
public import PlanarFlow.Klein.ProgTripC

/-!
# Compare-bounded runs survive the embedding; Klein's program reading its encoding

* `ModNat.ExecCmp.embed`: **`Exec.embed` (`WordRAM/Machine/WordMono.lean`) for compare-bounded
  runs**: a run of `s` compare-bounded by `H` from `c` embeds into a run of `s.toMem tmp β len`
  from any `d` agreeing with `c` (registers in `U`, memory `≤ W`), compare-bounded by the same
  `H`: the real registers compared are those of `U`, on which `d` agrees with `c` along the
  run.
* `Klein.kleinProgMem_cmpOK`: **every run of `kleinProgMem` (Klein's program reading its
  encoding from memory, as at a node of the recursion) from a configuration holding the encoding
  (`KleinEnc`) is compare-bounded by `Hc ≥ kleinHI`** (`ModNat.CmpOK`), from
  `kleinProg_cmpOK`, the embedding and the determinism of the semantics.
-/

@[expose] public section

namespace WordRAM

namespace Machine

namespace ModNat

namespace ExecCmp

open Stmt

variable {P P' : Input} {W H : ℕ}

private lemma or_and {x y : Bool} {Q : Prop} (h : (x && y) = true ∨ Q) :
    (x = true ∨ Q) ∧ (y = true ∨ Q) := by
  rcases h with h | h
  · simp only [Bool.and_eq_true] at h; exact ⟨Or.inl h.1, Or.inl h.2⟩
  · exact ⟨Or.inr h, Or.inr h⟩

/-- **The embedding of a compare-bounded run** (`Exec.embed` for `ExecCmp`): the embedded run
of `s.toMem tmp β len` from `d` is compare-bounded by the same `H`. -/
theorem embed {s : Stmt} {c c' : Config} {k : ℕ} (h : ExecCmp P W H s c c' k) {U : ℕ → Bool}
    {W' tmp β len : ℕ} (hs : s.regsOK U = true) (hW : W ≤ W')
    (hrd : s.noRand = true ∨ P'.tape = P.tape) :
    ∀ d, Agree U W c d → WordsBounded W' d →
      (s.noInp = true ∨ (InData P W β len W' d ∧ U tmp = false)) →
      ∃ d' k', ExecCmp P' W' H (s.toMem tmp β len) d d' k' ∧ k ≤ k' ∧ k' ≤ 3 * k ∧
        (s.noInp = true → k' = k) ∧ Agree U W c' d' ∧ KeepT U W tmp s.noInp d d' ∧
        ∃ L, c'.output = c.output ++ L ∧ d'.output = d.output ++ L := by
  -- the data region survives a frame
  have hID : ∀ {ro : Bool} {d d' : Config}, KeepT U W tmp ro d d' →
      InData P W β len W' d ∧ U tmp = false → InData P W β len W' d' ∧ U tmp = false :=
    fun hK ⟨hI, ht⟩ => ⟨⟨hI.lt, hI.le, hI.len, fun i hi => by
      rw [hK.nmem _ (by have := hI.lt; omega)]; exact hI.mem i hi⟩, ht⟩
  induction h with
  | skip hw =>
    intro d hA hd _
    exact ⟨d, 0, .skip hd, le_rfl, by omega, fun _ => rfl, hA, (Keep.refl _ _ _).toT _ _, [],
      by simp, by simp⟩
  | @instr ins c c' hst he hw hw' =>
    intro d hA hd hD
    have hl : ∀ r ∈ ins.regs, U r = true := fun r hr => List.all_eq_true.1 hs r hr
    by_cases hri : ins.notInp = true
    · obtain ⟨d', hed, hA', hK, L, hL⟩ := effect_embed (P' := P') hs hri hrd he hw hA
      have hd' : WordsBounded W' d' := wordsBounded_of_agree hA' hw' hW
        (fun r hr => by rw [hK.nreg r hr]; exact WordsBounded.nreg hd r)
        (fun a ha => by rw [hK.nmem a ha]; exact WordsBounded.nmem hd a)
      refine ⟨d', 1, ?_, le_rfl, by omega, fun _ => rfl, hA', hK.toT _ _, L, hL⟩
      rw [show (Stmt.instr ins).toMem tmp β len = .instr ins from instrToMem_of_notInp hri]
      exact .instr hst hed hd hd'
    · have hnr : (Stmt.instr ins).noInp = false := by
        simp only [Bool.not_eq_true] at hri; exact hri
      obtain ⟨hI, htmp⟩ : InData P W β len W' d ∧ U tmp = false := by
        rcases hD with hD | hI
        · rw [hnr] at hD; cases hD
        · exact hI
      have hβ := hI.lt; have hβ' := hI.le
      cases ins with
      | readIn r a =>
        have hr := hl r (by simp [Instr.regs])
        have ha := hl a (by simp [Instr.regs])
        have hrt : r ≠ tmp := fun e => by rw [e, htmp] at hr; cases hr
        have hat : a ≠ tmp := fun e => by rw [e, htmp] at ha; cases ha
        simp only [Instr.effect, Option.some.injEq] at he; subst he
        have hca := WordsBounded.nreg hw a
        set d₁ : Config := { d with nreg := upd d.nreg tmp β } with hd₁
        have hw₁ : WordsBounded W' d₁ := ⟨upd_le hd.1 (by omega), hd.2⟩
        have e₁a : d₁.nreg a = c.nreg a := by
          rw [hd₁]; simp only [upd_other _ _ _ hat]; exact hA.nreg a ha
        set d₂ : Config := { d₁ with nreg := upd d₁.nreg tmp (d₁.nreg tmp + d₁.nreg a) }
          with hd₂
        have e₂ : d₂.nreg tmp = β + c.nreg a := by
          rw [hd₂]; simp only [upd_apply, ite_true]; rw [e₁a, hd₁]; simp
        have hw₂ : WordsBounded W' d₂ := ⟨upd_le hw₁.1 (by
          rw [e₁a, hd₁]; simp only [upd_apply, ite_true]; omega), hw₁.2⟩
        set d₃ : Config := { d₂ with nreg := upd d₂.nreg r (d₂.nmem (d₂.nreg tmp)) } with hd₃
        have hval : d₂.nmem (d₂.nreg tmp) = P.data.getD (c.nreg a) 0 := by
          rw [e₂]; exact hI.mem _ hca
        have hA₃ : Agree U W { c with nreg := upd c.nreg r (P.data.getD (c.nreg a) 0) } d₃ := by
          refine ⟨fun x hx => ?_, hA.rreg, hA.nmem, hA.rmem⟩
          have hxt : x ≠ tmp := fun e => by rw [e, htmp] at hx; cases hx
          rw [hd₃]; simp only [hval, upd_apply]
          split
          · rfl
          · rw [hd₂]; simp only [upd_apply, hxt, ite_false]
            rw [hd₁]; simp only [upd_apply, hxt, ite_false]; exact hA.nreg x hx
        have hK₃ : KeepT U W tmp false d d₃ := by
          refine ⟨fun x hx ht => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
          have hxt : x ≠ tmp := fun e => by simpa using ht e
          have hxr : x ≠ r := fun e => by rw [e, hr] at hx; cases hx
          rw [hd₃]; simp only [upd_other _ _ _ hxr]
          rw [hd₂]; simp only [upd_other _ _ _ hxt]
          rw [hd₁]; simp only [upd_other _ _ _ hxt]
        have hw₃ : WordsBounded W' d₃ := ⟨upd_le hw₂.1 (by
          rw [hval]; have := WordsBounded.nreg hw' r; simp only [upd_apply, ite_true] at this
          omega), hw₂.2⟩
        refine ⟨d₃, 1 + (1 + 1), ?_, by omega, by omega, (fun h => by rw [hnr] at h; cases h),
          hA₃, (by rw [hnr]; exact hK₃), [], by simp, by simp [hd₃, hd₂, hd₁]⟩
        exact .seq (.instr rfl rfl hd hw₁) (.seq (.instr rfl rfl hw₁ hw₂) (.instr rfl rfl hw₂ hw₃))
      | inputSize r =>
        have hr := hl r (by simp [Instr.regs])
        simp only [Instr.effect, Option.some.injEq] at he; subst he
        have hlen : len ≤ W' := by
          have := WordsBounded.nreg hw' r; simp only [upd_apply, ite_true] at this
          rw [hI.len]; omega
        have hw₁ : WordsBounded W' { d with nreg := upd d.nreg r len } :=
          ⟨upd_le hd.1 hlen, hd.2⟩
        refine ⟨_, 1, .instr rfl rfl hd hw₁, le_rfl, by omega, (fun _ => rfl), ⟨fun x hx => ?_, hA.rreg, hA.nmem, hA.rmem⟩,
          ⟨fun x hx _ => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, [],
          (List.append_nil _).symm, (List.append_nil _).symm⟩
        · simp only [upd_apply, hI.len]; split
          · rfl
          · exact hA.nreg x hx
        · exact upd_other _ _ _ (fun e => by rw [e, hr] at hx; cases hx)
      | _ => simp [Instr.notInp] at hri
  | @seq s t c c₁ c₂ k₁ k₂ _ _ ih₁ ih₂ =>
    intro d hA hd hD
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨hrd₁, hrd₂⟩ := or_and hrd
    obtain ⟨hD₁, hD₂'⟩ := or_and hD
    obtain ⟨d₁, k₁', e₁, a₁, b₁, c₁', hA₁, hK₁, L₁, o₁, o₁'⟩ := ih₁ hs.1 hrd₁ d hA hd hD₁
    have hD₂ : t.noInp = true ∨ (InData P W β len W' d₁ ∧ U tmp = false) := by
      rcases hD₂' with h | h
      · exact Or.inl h
      · exact Or.inr (hID hK₁ h)
    obtain ⟨d₂, k₂', e₂, a₂, b₂, c₂', hA₂, hK₂, L₂, o₂, o₂'⟩ :=
      ih₂ hs.2 hrd₂ d₁ hA₁ e₁.toExec.wb_right hD₂
    refine ⟨d₂, k₁' + k₂', .seq e₁ e₂, by omega, by omega, fun h => ?_, hA₂, hK₁.trans hK₂,
      L₁ ++ L₂, by rw [o₂, o₁, List.append_assoc], by rw [o₂', o₁', List.append_assoc]⟩
    simp only [Stmt.noInp, Bool.and_eq_true] at h; rw [c₁' h.1, c₂' h.2]
  | @ifLtN_true a b t e c c' k ht _ ih =>
    intro d hA hd hD
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', a', b', c'', hA', hK', L, o⟩ :=
      ih hst (or_and hrd).1 d hA hd (or_and hD).1
    refine ⟨d', k' + 1, .ifLtN_true (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) e',
      by omega, by omega, fun h => ?_, hA', hK'.weaken fun h' => ?_, L, o⟩
    · simp only [Stmt.noInp, Bool.and_eq_true] at h; rw [c'' h.1]
    · simp only [Stmt.noInp, Bool.and_eq_true] at h'; exact h'.1
  | @ifLtN_false a b t e c c' k ht _ ih =>
    intro d hA hd hD
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', a', b', c'', hA', hK', L, o⟩ :=
      ih hse (or_and hrd).2 d hA hd (or_and hD).2
    refine ⟨d', k' + 2, .ifLtN_false (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) e',
      by omega, by omega, fun h => ?_, hA', hK'.weaken fun h' => ?_, L, o⟩
    · simp only [Stmt.noInp, Bool.and_eq_true] at h; rw [c'' h.2]
    · simp only [Stmt.noInp, Bool.and_eq_true] at h'; exact h'.2
  | @ifLtR_true a b t e c c' k hH ht _ ih =>
    intro d hA hd hD
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', a', b', c'', hA', hK', L, o⟩ :=
      ih hst (or_and hrd).1 d hA hd (or_and hD).1
    refine ⟨d', k' + 1, .ifLtR_true (by rw [hA.rreg a ha, hA.rreg b hb]; exact hH)
      (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) e',
      by omega, by omega, fun h => ?_, hA', hK'.weaken fun h' => ?_, L, o⟩
    · simp only [Stmt.noInp, Bool.and_eq_true] at h; rw [c'' h.1]
    · simp only [Stmt.noInp, Bool.and_eq_true] at h'; exact h'.1
  | @ifLtR_false a b t e c c' k hH ht _ ih =>
    intro d hA hd hD
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', a', b', c'', hA', hK', L, o⟩ :=
      ih hse (or_and hrd).2 d hA hd (or_and hD).2
    refine ⟨d', k' + 2, .ifLtR_false (by rw [hA.rreg a ha, hA.rreg b hb]; exact hH)
      (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) e',
      by omega, by omega, fun h => ?_, hA', hK'.weaken fun h' => ?_, L, o⟩
    · simp only [Stmt.noInp, Bool.and_eq_true] at h; rw [c'' h.2]
    · simp only [Stmt.noInp, Bool.and_eq_true] at h'; exact h'.2
  | @whileLtN_false a b body c ht hw =>
    intro d hA hd _
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨ha, hb⟩, _⟩ := hs
    exact ⟨d, 2, .whileLtN_false (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) hd, le_rfl,
      by omega, fun _ => rfl, hA, (Keep.refl _ _ _).toT _ _, [], by simp, by simp⟩
  | @whileLtN_true a b body c c₁ c' k₁ k₂ ht _ _ ih₁ ih₂ =>
    intro d hA hd hD
    have hs' := hs
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs'
    obtain ⟨⟨ha, hb⟩, hsb⟩ := hs'
    obtain ⟨d₁, k₁', e₁, a₁, b₁, c₁', hA₁, hK₁, L₁, o₁, o₁'⟩ := ih₁ hsb hrd d hA hd hD
    have hD₂ : (Stmt.whileLtN a b body).noInp = true ∨ (InData P W β len W' d₁ ∧ U tmp = false) := by
      rcases hD with h | h
      · exact Or.inl h
      · exact Or.inr (hID hK₁ h)
    obtain ⟨d₂, k₂', e₂, a₂, b₂, c₂', hA₂, hK₂, L₂, o₂, o₂'⟩ := ih₂ hs hrd d₁ hA₁ e₁.toExec.wb_right hD₂
    refine ⟨d₂, k₁' + 2 + k₂',
      .whileLtN_true (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) e₁ e₂, by omega, by omega,
      fun h => ?_, hA₂, (hK₁.trans hK₂).weaken fun h => ?_, L₁ ++ L₂,
      by rw [o₂, o₁, List.append_assoc], by rw [o₂', o₁', List.append_assoc]⟩
    · have h' : body.noInp = true := h
      rw [c₁' h', c₂' h]
    · simp only [Bool.and_eq_true]; exact ⟨h, h⟩
  | @whileLtR_false a b body c hH ht hw =>
    intro d hA hd _
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨ha, hb⟩, _⟩ := hs
    exact ⟨d, 2, .whileLtR_false (by rw [hA.rreg a ha, hA.rreg b hb]; exact hH)
      (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) hd, le_rfl,
      by omega, fun _ => rfl, hA, (Keep.refl _ _ _).toT _ _, [], by simp, by simp⟩
  | @whileLtR_true a b body c c₁ c' k₁ k₂ hH ht _ _ ih₁ ih₂ =>
    intro d hA hd hD
    have hs' := hs
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs'
    obtain ⟨⟨ha, hb⟩, hsb⟩ := hs'
    obtain ⟨d₁, k₁', e₁, a₁, b₁, c₁', hA₁, hK₁, L₁, o₁, o₁'⟩ := ih₁ hsb hrd d hA hd hD
    have hD₂ : (Stmt.whileLtR a b body).noInp = true ∨ (InData P W β len W' d₁ ∧ U tmp = false) := by
      rcases hD with h | h
      · exact Or.inl h
      · exact Or.inr (hID hK₁ h)
    obtain ⟨d₂, k₂', e₂, a₂, b₂, c₂', hA₂, hK₂, L₂, o₂, o₂'⟩ := ih₂ hs hrd d₁ hA₁ e₁.toExec.wb_right hD₂
    refine ⟨d₂, k₁' + 2 + k₂',
      .whileLtR_true (by rw [hA.rreg a ha, hA.rreg b hb]; exact hH)
        (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) e₁ e₂, by omega, by omega,
      fun h => ?_, hA₂, (hK₁.trans hK₂).weaken fun h => ?_, L₁ ++ L₂,
      by rw [o₂, o₁, List.append_assoc], by rw [o₂', o₁', List.append_assoc]⟩
    · have h' : body.noInp = true := h
      rw [c₁' h', c₂' h]
    · simp only [Bool.and_eq_true]; exact ⟨h, h⟩

end ExecCmp

end ModNat

end Machine

end WordRAM

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ} {nD : ℕ}
  {σ : D ≃ Fin nD} {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} {t : ℕ}
  {X : ℕ → V}

local notation "𝒢" => pieceGraph M S ℓ

/-- **Every run of Klein's program reading its encoding is compare-bounded by `Hc`**
(`kleinHI ≤ Hc`): under the hypotheses of `klein_exec_of_enc`, every run of `kleinProgMem` on
any input from a configuration `d` holding the encoding (`KleinEnc`) compares only reals within
`Hc` of each other (`ModNat.CmpOK`). -/
theorem kleinProgMem_cmpOK {P P' : Input} {B : ℕ} (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ B)
    (hB : n + 2 * nD ≤ B) (hOUT : aOUT nD + k * t ≤ B) (hRB : aRB n + k * t ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1))
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    (hX : KTgt M k g S ℓ nD n ιv t X P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F}
    (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x))
    (hCr : C.root = M.face (g 0))
    (hT : Compat T (tripSrc M k g 0) (tripDst M k g 0) (g (0 % k)) (tpar 𝒢 (tripSrc M k g 0)))
    {W' β : ℕ} (d : Config) (hd : WordsBounded W' d)
    (hrb : ∀ r < 201, d.nreg r ≤ B + 16 * (n + 1))
    (hmb : ∀ a ≤ B + 16 * (n + 1), d.nmem a ≤ B + 16 * (n + 1))
    (hE : KleinEnc M k g S ℓ σ B n β W' P d) {Hc : ℕ} (hHc : kleinHI V F S ℓ k ≤ Hc) :
    ModNat.CmpOK P' W' Hc (kleinProgMem B nD n k t β P.data.length) d := by
  have hσ : ∀ x : D, (σ x : ℕ) < nD := fun x => (σ x).2
  have hW : B + 16 * (n + 1) ≤ W' := by have := hE.dat.le; omega
  set c := trunc kU (B + 16 * (n + 1)) d with hcdef
  have hA := agree_trunc kU (B + 16 * (n + 1)) d
  have hrm : ∀ a ≤ B + 16 * (n + 1), c.rmem a = d.rmem a := fun a ha => (hA.rmem a ha).symm
  have hw : WordsBounded (B + 16 * (n + 1)) c :=
    wordsBounded_trunc (fun r hr => hrb r (by simpa [kU] using hr)) hmb
  have hwt : ∀ x, c.rmem (aWT + σ x) = tripWt M k g S ℓ 0 x := fun x => by
    rw [hrm _ (by have := hσ x; unfold aWT; omega)]; exact hE.wt x
  have hph : ∀ x, c.rmem (aPH nD + σ x) = tripφ S ℓ x := fun x => by
    rw [hrm _ (by have := hσ x; unfold aPH; omega)]; exact hE.ph x
  have htl : c.rmem (aTL nD) = tripL V S ℓ := by rw [hrm _ (by unfold aTL; omega)]; exact hE.tl
  have hth : c.rmem (aTH nD) = tripTh V S ℓ := by
    rw [hrm _ (by unfold aTH; unfold aOUT at hOUT; omega)]; exact hE.th
  have hh0 : c.rmem (aH0 nD) = tripH0 V S ℓ k := by
    rw [hrm _ (by unfold aH0; unfold aOUT at hOUT; omega)]; exact hE.h0
  obtain ⟨c', steps, e, -, -, -, -⟩ := klein_exec hWa hB hOUT hRB hP H hR hL hK
    hG hO hX hI hoff hCr hT hw hwt hph htl hth hh0
  have ec := (kleinProg_cmpOK hWa hB hOUT hRB hP H hR hL hK hG hO hX hI hoff hCr hT hw hwt hph
    htl hth hh0 hHc).exec e
  obtain ⟨d', k', e', -⟩ :=
    ModNat.ExecCmp.embed (P' := P') (tmp := 201) ec (kleinProg_regsOK B nD n k t) hW
      (Or.inl (kleinProg_noRand B nD n k t)) d hA hd (Or.inr ⟨hE.dat, by decide⟩)
  intro d₂ k₂ e₂
  obtain ⟨rfl, rfl⟩ := Exec.det e₂ e'.toExec
  exact e'

end Klein

end PlanarFlow
