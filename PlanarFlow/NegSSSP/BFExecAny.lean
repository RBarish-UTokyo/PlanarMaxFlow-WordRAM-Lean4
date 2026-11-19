module

public import PlanarFlow.NegSSSP.BFExecP
public import WordRAM.Machine.WordMono

/-!
# Bellman–Ford of the recursion from any configuration holding its input

`PlanarFlow.NegSSSP.bfFull_exec` runs `bfFull` from the specific configuration `bfStartP`
(exact registers, everything else zero). Here:

* `bfFull_exec_any`: the same run from **any** configuration bounded by `bfWP b` whose registers
  read by `bfFull` (`BFRegs`) and whose memory regions (`BFMem`: the order `π`, the flags and the
  lengths of the two matrices in row-major order) hold the content of `bfStartP`; nothing has to
  be zero. The output is kept.
* `bfFull_exec_emb`: the same run **inside a larger configuration** `d` with any word bound
  `W' ≥ bfWP b`: `bfFull` names only the registers `< 85` and reads no input
  (`bfFull_regsOK`, `bfFull_noInp`, `bfFull_noRand`), so by `WordRAM.Machine.Exec.lift_trunc`
  it runs from `d` in the same number of steps with the same outcome, keeping every register
  `≥ 85` and all the memory above `bfWP b` (the frame), provided the registers `< 85` and the
  memory at addresses `≤ bfWP b` of `d` are bounded by `bfWP b`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Finset BKMNW

/-- The registers of `bfStartP` that `bfFull` reads (with `n = b²`). -/
structure BFRegs (b : ℕ) (c : Config) : Prop where
  r1 : c.nreg 1 = b
  r2 : c.nreg 2 = 10 * b + 2 + 4 * (b * b)
  r3 : c.nreg 3 = 5 * b + 2
  r4 : c.nreg 4 = 0
  r7 : c.nreg 7 = 10 * b + 2 + 6 * (b * b)
  r8 : c.nreg 8 = 6 * b + 2
  r9 : c.nreg 9 = 5 * b + 2
  r10 : c.nreg 10 = 1
  r40 : c.nreg 40 = 10 * b + 2 + 4 * (b * b)
  r41 : c.nreg 41 = 10 * b + 2 + 2 * (b * b)
  r42 : c.nreg 42 = 7 * b + 2
  r43 : c.nreg 43 = 7 * b + 2 + 2 * (b * b)
  r80 : c.nreg 80 = 10 * b + 2 + 3 * (b * b)
  r81 : c.nreg 81 = 7 * b + 2 + b * b

/-- The memory regions of `bfStartP`: `π` at `5b + 2`, the flags at `7b + 2` and
`7b + 2 + b²`, the lengths at `10b + 2 + 2b²` and `10b + 2 + 3b²` (row-major). -/
structure BFMem (b : ℕ) (X₁ : ℕ → ℕ → Prop) (D₁ : ℕ → ℕ → ℤ) (X₂ : ℕ → ℕ → Prop)
    (D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) (c : Config) : Prop where
  pm : ∀ i < b, c.nmem (5 * b + 2 + i) = π i
  f1 : ∀ s t, s < b → t < b → c.nmem (7 * b + 2 + s * b + t) = finB X₁ s t
  f2 : ∀ s t, s < b → t < b → c.nmem (7 * b + 2 + b * b + s * b + t) = finB X₂ s t
  d1 : ∀ s t, s < b → t < b → c.rmem (10 * b + 2 + 2 * (b * b) + s * b + t) = D₁ s t
  d2 : ∀ s t, s < b → t < b → c.rmem (10 * b + 2 + 3 * (b * b) + s * b + t) = D₂ s t

/-- `bfStartP` holds its registers. -/
theorem bfStartP_regs (b : ℕ) (X₁ : ℕ → ℕ → Prop) (D₁ : ℕ → ℕ → ℤ) (X₂ : ℕ → ℕ → Prop)
    (D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) : BFRegs b (bfStartP b X₁ D₁ X₂ D₂ π) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `bfStartP` holds its memory regions. -/
theorem bfStartP_mem {b : ℕ} {X₁ : ℕ → ℕ → Prop} {D₁ : ℕ → ℕ → ℤ} {X₂ : ℕ → ℕ → Prop}
    {D₂ : ℕ → ℕ → ℤ} {π : ℕ → ℕ} (hπ : IsPermB b π) :
    BFMem b X₁ D₁ X₂ D₂ π (bfStartP b X₁ D₁ X₂ D₂ π) := by
  obtain ⟨-, -, -, -, hI, hfl₂, hdv₂, hπm⟩ :=
    bfStartP_spec (X₁ := X₁) (D₁ := D₁) (X₂ := X₂) (D₂ := D₂) hπ
  exact ⟨hπm, hI.fl, hfl₂, hI.dv, hdv₂⟩

/-- `bfFull` names only the registers `< 85`. -/
theorem bfFull_regsOK : bfFull.regsOK (fun r => decide (r < 85)) = true := by decide

/-- `bfFull` reads no input. -/
theorem bfFull_noInp : bfFull.noInp = true := by decide

/-- `bfFull` uses no random word. -/
theorem bfFull_noRand : bfFull.noRand = true := by decide

variable {b : ℕ} {P : Input} {X₁ X₂ : ℕ → ℕ → Prop} {D₁ D₂ : ℕ → ℕ → ℤ} {π : ℕ → ℕ}

/-- **Bellman–Ford from any configuration holding the plain encoding.** As
`bfFull_exec`, from any configuration bounded by `bfWP b` with the registers `BFRegs` and the
memory regions `BFMem` of `bfStartP`; the output is kept. -/
theorem bfFull_exec_any (hπ : IsPermB b π) (hD₁ : CrossingX b X₁ D₁)
    (hD₂ : CrossingX b X₂ D₂) (c : Config) (hw : WordsBounded (bfWP b) c) (hR : BFRegs b c)
    (hM : BFMem b X₁ D₁ X₂ D₂ π c) :
    ∃ c' k, Exec P (bfWP b) bfFull c c' k ∧ k ≤ bfCostP b ∧
      (∃ E : ℕ → ℤ, (∀ v < b, c'.rmem (5 * b + 2 + v) = E v) ∧
        ((c'.nreg 30 = 0 ∧ Feas2O b X₁ D₁ X₂ D₂ π E) ∨
          (c'.nreg 30 = 1 ∧ ¬ ∃ E', Feas2O b X₁ D₁ X₂ D₂ π E')) ∧
        ((∃ E', Feas2O b X₁ D₁ X₂ D₂ π E') → ∀ v < b, E v = bfuO b X₁ D₁ X₂ D₂ π b v)) ∧
      c'.output = c.output := by
  obtain ⟨-, hL₁, hL₂, hL, -, -, -, -⟩ :=
    bfStartP_spec (X₁ := X₁) (D₁ := D₁) (X₂ := X₂) (D₂ := D₂) hπ
  have hI : InP b (10 * b + 2 + 4 * (b * b)) (10 * b + 2 + 2 * (b * b)) (7 * b + 2)
      (7 * b + 2 + 2 * (b * b)) X₁ D₁ c :=
    ⟨hR.r1, hR.r10, hR.r40, hR.r41, hR.r42, hR.r43, hM.f1, hM.d1⟩
  unfold bfFull
  refine spec_seq ?_
  refine spec_use (prepO_exec (P := P) hL₁ c hw hI) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hF₁, htab₁⟩
  refine spec_seq ?_
  refine spec_use (glueP_exec (P := P) c₁ hw₁) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨g40, g41, g42, gn, gr, gnm, grm, go⟩
  have e : ∀ r, (r < 40 ∨ (42 < r ∧ r < 44) ∨ 80 ≤ r) → c₂.nreg r = c.nreg r := fun r hr => by
    rw [gn r (by omega) (by omega) (by omega), hF₁.nreg r (by omega)]
  have hI₂ : InP b (10 * b + 2 + 6 * (b * b)) (10 * b + 2 + 3 * (b * b)) (7 * b + 2 + b * b)
      (7 * b + 2 + 2 * (b * b)) X₂ D₂ c₂ := by
    refine ⟨by rw [e 1 (by omega)]; exact hR.r1, by rw [e 10 (by omega)]; exact hR.r10,
      by rw [g40, hF₁.nreg 7 (by omega)]; exact hR.r7,
      by rw [g41, hF₁.nreg 80 (by omega)]; exact hR.r80,
      by rw [g42, hF₁.nreg 81 (by omega)]; exact hR.r81, by rw [e 43 (by omega)]; exact hR.r43,
      fun s t hs ht => ?_, fun s t hs ht => ?_⟩
    · obtain ⟨-, -, d3⟩ := rowcol hs ht
      rw [gnm, hF₁.nmem _ (Or.inl (by omega))]; exact hM.f2 s t hs ht
    · obtain ⟨-, -, d3⟩ := rowcol hs ht
      rw [grm, hF₁.rmem _ (Or.inl (by omega))]; exact hM.d2 s t hs ht
  have htab₂ := htab₁.of (c' := c₂) (fun a _ _ => by rw [gnm]) (fun a _ _ => by rw [grm])
  refine spec_seq ?_
  refine spec_use (prepO_exec (P := P) hL₂ c₂ hw₂ hI₂) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hF₃, htab₃⟩
  have htab₁' := htab₂.of (c' := c₃) (fun a _ h2 => hF₃.nmem a (Or.inr (Or.inl ⟨by omega,
    by omega⟩))) (fun a _ h2 => hF₃.rmem a (Or.inl (by omega)))
  have f : ∀ r, r < 40 → c₃.nreg r = c.nreg r := fun r hr => by
    rw [hF₃.nreg r (by omega), e r (by omega)]
  refine spec_use (bfDDG2O_exec (P := P) hπ hD₁ hD₂
    (fun s t hs ht _ => lt_Hb (D := D₁) hs ht) (fun s t hs ht _ => lt_Hb (D := D₂) hs ht) hL c₃
    hw₃ (by rw [f 1 (by omega)]; exact hR.r1) (by rw [f 2 (by omega)]; exact hR.r2)
    (by rw [f 3 (by omega)]; exact hR.r3) (by rw [f 4 (by omega)]; exact hR.r4)
    (by rw [f 7 (by omega)]; exact hR.r7)
    (by rw [f 8 (by omega)]; exact hR.r8) (by rw [f 9 (by omega)]; exact hR.r9)
    (fun s t hs ht hst => (htab₁' s t hs ht hst trivial).1)
    (fun s t hs ht hst => (htab₁' s t hs ht hst trivial).2.1)
    (fun s t hs ht hst => (htab₁' s t hs ht hst trivial).2.2)
    (fun s t hs ht hst => (htab₃ s t hs ht hst trivial).1)
    (fun s t hs ht hst => (htab₃ s t hs ht hst trivial).2.1)
    (fun s t hs ht hst => (htab₃ s t hs ht hst trivial).2.2) (fun i hi => ?_)) ?_
  · rw [hF₃.nmem _ (Or.inl (by omega)), gnm, hF₁.nmem _ (Or.inl (by omega))]
    exact hM.pm i hi
  intro c₄ k₄ hk₄ _ ⟨E, hv, hout, hbfu, ho⟩
  refine ⟨?_, ⟨E, hv, hout, hbfu⟩, ?_⟩
  · unfold bfCostP; omega
  · rw [ho, hF₃.out, go, hF₁.out]

/-- The register predicate of `bfFull`. -/
abbrev bfU : ℕ → Bool := fun r => decide (r < 85)

/-- **Bellman–Ford inside a larger configuration.** From any configuration `d` bounded by
`W' ≥ bfWP b` holding the registers `BFRegs` and the memory regions `BFMem` of `bfStartP`, with
its registers `< 85` and its memory at addresses `≤ bfWP b` bounded by `bfWP b`, `bfFull` runs
on any input within `bfCostP b` steps with the outcome of `bfFull_exec`, keeping the output,
every register `≥ 85` and the memory above `bfWP b`. -/
theorem bfFull_exec_emb (hπ : IsPermB b π) (hD₁ : CrossingX b X₁ D₁)
    (hD₂ : CrossingX b X₂ D₂) {W' : ℕ} (hW : bfWP b ≤ W') (d : Config)
    (hd : WordsBounded W' d) (hR : BFRegs b d) (hM : BFMem b X₁ D₁ X₂ D₂ π d)
    (hrb : ∀ r < 85, d.nreg r ≤ bfWP b) (hmb : ∀ a ≤ bfWP b, d.nmem a ≤ bfWP b) :
    ∃ d' k, Exec P W' bfFull d d' k ∧ k ≤ bfCostP b ∧
      (∃ E : ℕ → ℤ, (∀ v < b, d'.rmem (5 * b + 2 + v) = E v) ∧
        ((d'.nreg 30 = 0 ∧ Feas2O b X₁ D₁ X₂ D₂ π E) ∨
          (d'.nreg 30 = 1 ∧ ¬ ∃ E', Feas2O b X₁ D₁ X₂ D₂ π E')) ∧
        ((∃ E', Feas2O b X₁ D₁ X₂ D₂ π E') → ∀ v < b, E v = bfuO b X₁ D₁ X₂ D₂ π b v)) ∧
      d'.output = d.output ∧ (∀ r, 85 ≤ r → d'.nreg r = d.nreg r) ∧
      (∀ r, 85 ≤ r → d'.rreg r = d.rreg r) ∧ (∀ a, bfWP b < a → d'.nmem a = d.nmem a) ∧
      (∀ a, bfWP b < a → d'.rmem a = d.rmem a) := by
  set c := trunc bfU (bfWP b) d with hcdef
  have hA := agree_trunc bfU (bfWP b) d
  have hn : ∀ r < 85, c.nreg r = d.nreg r := fun r hr => (hA.nreg r (by simp [bfU, hr])).symm
  have hm : ∀ a ≤ bfWP b, c.nmem a = d.nmem a := fun a ha => (hA.nmem a ha).symm
  have hrm : ∀ a ≤ bfWP b, c.rmem a = d.rmem a := fun a ha => (hA.rmem a ha).symm
  have hw : WordsBounded (bfWP b) c :=
    wordsBounded_trunc (fun r hr => hrb r (by simpa [bfU] using hr)) hmb
  have hRc : BFRegs b c := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [hn _ (by omega)]
    exacts [hR.r1, hR.r2, hR.r3, hR.r4, hR.r7, hR.r8, hR.r9, hR.r10, hR.r40, hR.r41, hR.r42,
      hR.r43, hR.r80, hR.r81]
  have hWb : bfWP b = 8 * (b * b) + 14 * b + 12 := rfl
  have hMc : BFMem b X₁ D₁ X₂ D₂ π c := by
    refine ⟨fun i hi => ?_, fun s t hs ht => ?_, fun s t hs ht => ?_, fun s t hs ht => ?_,
      fun s t hs ht => ?_⟩
    · rw [hm _ (by omega)]; exact hM.pm i hi
    · obtain ⟨-, -, d3⟩ := rowcol hs ht
      rw [hm _ (by omega)]; exact hM.f1 s t hs ht
    · obtain ⟨-, -, d3⟩ := rowcol hs ht
      rw [hm _ (by omega)]; exact hM.f2 s t hs ht
    · obtain ⟨-, -, d3⟩ := rowcol hs ht
      rw [hrm _ (by omega)]; exact hM.d1 s t hs ht
    · obtain ⟨-, -, d3⟩ := rowcol hs ht
      rw [hrm _ (by omega)]; exact hM.d2 s t hs ht
  obtain ⟨c', k, e, hk, ⟨E, hv, hout, hbfu⟩, ho⟩ :=
    bfFull_exec_any (P := P) hπ hD₁ hD₂ c hw hRc hMc
  obtain ⟨d', e', hA', hK, ho'⟩ :=
    Exec.lift_trunc (P' := P) e bfFull_regsOK bfFull_noInp bfFull_noRand hW hd
  have h30 : d'.nreg 30 = c'.nreg 30 := hA'.nreg 30 (by decide)
  refine ⟨d', k, e', hk, ⟨E, fun v hv' => ?_, by rw [h30]; exact hout, hbfu⟩, ?_,
    fun r hr => hK.nreg r (by simp [bfU]; omega), fun r hr => hK.rreg r (by simp [bfU]; omega),
    hK.nmem, hK.rmem⟩
  · rw [hA'.rmem _ (by omega)]; exact hv v hv'
  · rw [ho', ho]; rfl

end NegSSSP

end PlanarFlow
