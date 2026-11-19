module

public import PlanarFlow.NegSSSP.BFExecAny
public import PlanarFlow.Monge.PrepCmp
public import PlanarFlow.Monge.DDGBF2OCmp
public import PlanarFlow.Monge.FRNat

/-!
# Bellman–Ford of the recursion on natural words

`bfFull_exec_nat`: the run of `PlanarFlow.NegSSSP.bfFull_exec_any` is simulated by the program on
natural words `constsS; ModNat.toNat 85 M bfFull` (`WordRAM/Machine/RealsModNat.lean`), which keeps
every real value modulo `M = bfM b L` in natural words, with the word bound
`bfWN b L = 2 bfWP b + 1 + M² + M` and at most `4 bfCostP b + 3` steps. Hypotheses beyond those of
`bfFull_exec_any`: the lengths of both matrices bounded by `L` (on all pairs `s, t < b`), every
real memory cell at an address `≤ bfWP b` bounded by `bfB b L` (`CmpAbs.MemB`), and a natural
configuration holding the residues of the (integer) reals of the start (`ModNat.Sim`). At the end
the values `E v`, of absolute value at most `bfB b L < M / 2`, are read back from their residues
(`ModNat.Res.signed`).

The bounds (`bfFull_good`): the two passes building the tables (`Monge.prepO_good`) and the
rounds (`Monge.bfDDG2O_good`) store only reals bounded by `B = bfB b L` and compare only reals
differing by at most `2 B`; the values stay above `-bfXm b L` (`bfXm b L = 4 b L (2 b + 1)(b + 1)`),
the table bounds `Hb b Dᵢ` are at most `b² L + b + 1`, the replacements `Hb ± κ` at most
`Hb + bfWP b`. So `B = bfXm b L + b² L + 2 b + 1 + bfWP b`, `M = 4 B + 1`.
`bfFull_exec_nat_of_int` starts from `ModNat.natOf` of an integer start, and `bfFull_exec_emb_nat`
runs inside a larger natural configuration (as `bfFull_exec_emb`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Machine.ModNat WordRAM.Programs Monge
  Finset BKMNW CmpAbs

/-- The bound of the stored reals. -/
def bfB (b L : ℕ) : ℕ := bfXm b L + b * b * L + 2 * b + 1 + bfWP b

/-- The bound of the compared differences. -/
def bfHc (b L : ℕ) : ℕ := 2 * bfB b L

/-- The modulus. -/
def bfM (b L : ℕ) : ℕ := 2 * bfHc b L + 1

/-- The word bound of the program on natural words. -/
def bfWN (b L : ℕ) : ℕ := 2 * bfWP b + 1 + bfM b L * bfM b L + bfM b L

variable {b L : ℕ} {P : Input} {X₁ X₂ : ℕ → ℕ → Prop} {D₁ D₂ : ℕ → ℕ → ℤ} {π : ℕ → ℕ}

/-- The table bound against `L`. -/
theorem Hb_le {D : ℕ → ℕ → ℤ} (hD : ∀ s t, s < b → t < b → |(D s t : ℝ)| ≤ L) :
    Hb b D ≤ (b * b * L : ℕ) + b + 1 := by
  unfold Hb
  have : ∑ s ∈ range b, ∑ t ∈ range b, |(D s t : ℝ)| ≤ ∑ s ∈ range b, ∑ t ∈ range b, (L : ℝ) :=
    sum_le_sum fun s hs => sum_le_sum fun t ht => hD s t (mem_range.1 hs) (mem_range.1 ht)
  simp only [sum_const, card_range, nsmul_eq_mul] at this
  push_cast
  nlinarith

theorem Hb_ge {D : ℕ → ℕ → ℤ} : (b : ℝ) ≤ Hb b D := by
  unfold Hb
  have : 0 ≤ ∑ s ∈ range b, ∑ t ∈ range b, |(D s t : ℝ)| := by positivity
  linarith

theorem bfFull_noDivR : bfFull.noDivR = true := by decide

/-- **Bellman–Ford with bounded comparisons and stores.** From a configuration as in
`bfFull_exec_any`, with the lengths bounded by `L`, every run of `bfFull` started with the real
memory bounded by `bfB b L` compares only reals differing by at most `bfHc b L` and stores only
reals bounded by `bfB b L`. -/
theorem bfFull_good (hπ : IsPermB b π) (hD₁ : CrossingX b X₁ D₁) (hD₂ : CrossingX b X₂ D₂)
    (hL₁ : ∀ s t, s < b → t < b → |(D₁ s t : ℝ)| ≤ L)
    (hL₂ : ∀ s t, s < b → t < b → |(D₂ s t : ℝ)| ≤ L) (c : Config)
    (hw : WordsBounded (bfWP b) c) (hR : BFRegs b c) (hM : BFMem b X₁ D₁ X₂ D₂ π c) :
    Good P (bfWP b) (bfB b L) (bfHc b L) bfFull c := by
  obtain ⟨-, hLy₁, hLy₂, hL, -, -, -, -⟩ :=
    bfStartP_spec (X₁ := X₁) (D₁ := D₁) (X₂ := X₂) (D₂ := D₂) hπ
  have hHW : ∀ {D : ℕ → ℕ → ℤ}, (∀ s t, s < b → t < b → |(D s t : ℝ)| ≤ L) →
      Hb b D + (bfWP b : ℕ) ≤ (bfB b L : ℕ) := fun hD => by
    have := Hb_le hD
    unfold bfB; push_cast at this ⊢
    have : (0 : ℝ) ≤ bfXm b L := Nat.cast_nonneg _
    linarith
  have hHX : ∀ {D : ℕ → ℕ → ℤ}, (∀ s t, s < b → t < b → |(D s t : ℝ)| ≤ L) →
      ((bfXm b L : ℕ) : ℝ) + Hb b D + b ≤ (bfB b L : ℕ) := fun hD => by
    have := Hb_le hD
    unfold bfB; push_cast at this ⊢
    have : (0 : ℝ) ≤ bfWP b := Nat.cast_nonneg _
    linarith
  have hB1 : 1 ≤ bfB b L := by unfold bfB; omega
  have hI : InP b (10 * b + 2 + 4 * (b * b)) (10 * b + 2 + 2 * (b * b)) (7 * b + 2)
      (7 * b + 2 + 2 * (b * b)) X₁ D₁ c :=
    ⟨hR.r1, hR.r10, hR.r40, hR.r41, hR.r42, hR.r43, hM.f1, hM.d1⟩
  unfold bfHc bfFull
  refine good_seq_use (prepO_exec (P := P) hLy₁ c hw hI) (prepO_good hLy₁ (hHW hL₁) hB1 c hw hI) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hF₁, htab₁⟩
  refine good_seq_use (glueP_exec (P := P) c₁ hw₁) (good_noRS (by decide) _) ?_
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
  refine good_seq_use (prepO_exec (P := P) hLy₂ c₂ hw₂ hI₂)
    (prepO_good hLy₂ (hHW hL₂) hB1 c₂ hw₂ hI₂) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hF₃, htab₃⟩
  have htab₁' := htab₂.of (c' := c₃) (fun a _ h2 => hF₃.nmem a (Or.inr (Or.inl ⟨by omega,
    by omega⟩))) (fun a _ h2 => hF₃.rmem a (Or.inl (by omega)))
  have f : ∀ r, r < 40 → c₃.nreg r = c.nreg r := fun r hr => by
    rw [hF₃.nreg r (by omega), e r (by omega)]
  exact bfDDG2O_good (P := P) hπ hD₁ hD₂
    (fun s t hs ht _ => lt_Hb (D := D₁) hs ht) (fun s t hs ht _ => lt_Hb (D := D₂) hs ht)
    (fun s t hs ht _ => hL₁ s t hs ht) (fun s t hs ht _ => hL₂ s t hs ht) Hb_ge Hb_ge
    (hHX hL₁) (hHX hL₂) hL c₃
    hw₃ (by rw [f 1 (by omega)]; exact hR.r1) (by rw [f 2 (by omega)]; exact hR.r2)
    (by rw [f 3 (by omega)]; exact hR.r3) (by rw [f 4 (by omega)]; exact hR.r4)
    (by rw [f 7 (by omega)]; exact hR.r7)
    (by rw [f 8 (by omega)]; exact hR.r8) (by rw [f 9 (by omega)]; exact hR.r9)
    (fun s t hs ht hst => (htab₁' s t hs ht hst trivial).1)
    (fun s t hs ht hst => (htab₁' s t hs ht hst trivial).2.1)
    (fun s t hs ht hst => (htab₁' s t hs ht hst trivial).2.2)
    (fun s t hs ht hst => (htab₃ s t hs ht hst trivial).1)
    (fun s t hs ht hst => (htab₃ s t hs ht hst trivial).2.1)
    (fun s t hs ht hst => (htab₃ s t hs ht hst trivial).2.2) (fun i hi => by
      rw [hF₃.nmem _ (Or.inl (by omega)), gnm, hF₁.nmem _ (Or.inl (by omega))]
      exact hM.pm i hi)

/-- **Bellman–Ford is compare-bounded.** -/
theorem bfFull_cmpOK (hπ : IsPermB b π) (hD₁ : CrossingX b X₁ D₁) (hD₂ : CrossingX b X₂ D₂)
    (hL₁ : ∀ s t, s < b → t < b → |(D₁ s t : ℝ)| ≤ L)
    (hL₂ : ∀ s t, s < b → t < b → |(D₂ s t : ℝ)| ≤ L) (c : Config)
    (hw : WordsBounded (bfWP b) c) (hR : BFRegs b c) (hM : BFMem b X₁ D₁ X₂ D₂ π c)
    (hMB : MemB (bfWP b) (bfB b L) c) : CmpOK P (bfWP b) (bfHc b L) bfFull c :=
  (bfFull_good hπ hD₁ hD₂ hL₁ hL₂ c hw hR hM).toCmp hMB

/-- **Bellman–Ford of the recursion on natural words.** As `bfFull_exec_any`, with the lengths
bounded by `L`, the real memory bounded by `bfB b L`, and a natural configuration `d` holding the
residues modulo `bfM b L` of the reals (`Sim`, registers `< 85`, real memory at `β + a` for
`β = bfWP b + 1`), bounded by `bfWN b L`: the run of `bfFull` is simulated by the natural program
`constsS 85 M H β; toNat 85 M bfFull` within `4 bfCostP b + 3` steps and the word bound
`bfWN b L`, ending in a configuration holding the residues of the final reals, from which the
values `E v` are read back; the natural registers `≥ 174` and the natural memory outside
`[0, W] ∪ [β, β + W]` are kept. -/
theorem bfFull_exec_nat (hπ : IsPermB b π) (hD₁ : CrossingX b X₁ D₁) (hD₂ : CrossingX b X₂ D₂)
    (hL₁ : ∀ s t, s < b → t < b → |(D₁ s t : ℝ)| ≤ L)
    (hL₂ : ∀ s t, s < b → t < b → |(D₂ s t : ℝ)| ≤ L) (c : Config)
    (hw : WordsBounded (bfWP b) c) (hR : BFRegs b c) (hM : BFMem b X₁ D₁ X₂ D₂ π c)
    (hMB : MemB (bfWP b) (bfB b L) c) {d : Config}
    (hS : Sim 85 (bfWP b) (bfM b L) (bfWP b + 1) c d) (hd : WordsBounded (bfWN b L) d) :
    ∃ c' k, Exec P (bfWP b) bfFull c c' k ∧ k ≤ bfCostP b ∧
      (∃ E : ℕ → ℤ, (∀ v < b, c'.rmem (5 * b + 2 + v) = E v) ∧
        ((c'.nreg 30 = 0 ∧ Feas2O b X₁ D₁ X₂ D₂ π E) ∨
          (c'.nreg 30 = 1 ∧ ¬ ∃ E', Feas2O b X₁ D₁ X₂ D₂ π E')) ∧
        ((∃ E', Feas2O b X₁ D₁ X₂ D₂ π E') → ∀ v < b, E v = bfuO b X₁ D₁ X₂ D₂ π b v) ∧
        ∀ v < b, |(E v : ℝ)| ≤ bfB b L) ∧
      c'.output = c.output ∧ MemB (bfWP b) (bfB b L) c' ∧
      ∃ d' k', Exec P (bfWN b L) (.seq (constsS 85 (bfM b L) (bfHc b L) (bfWP b + 1))
          (ModNat.toNat 85 (bfM b L) bfFull)) d d' k' ∧ k' ≤ 4 * bfCostP b + 3 ∧
        Sim 85 (bfWP b) (bfM b L) (bfWP b + 1) c' d' ∧
        (∀ r, 2 * 85 + 4 ≤ r → d'.nreg r = d.nreg r) ∧
        (∀ a, bfWP b < a → (a < bfWP b + 1 ∨ bfWP b + 1 + bfWP b < a) → d'.nmem a = d.nmem a) := by
  obtain ⟨c', k, e, hk, ⟨E, hv, hout, hbfu⟩, ho⟩ := bfFull_exec_any (P := P) hπ hD₁ hD₂ c hw hR hM
  have hg := bfFull_good (P := P) hπ hD₁ hD₂ hL₁ hL₂ c hw hR hM
  have hMB' := hg.mem e hMB
  have hWb : bfWP b = 8 * (b * b) + 14 * b + 12 := rfl
  obtain ⟨d', k', e', hk', hS', -, hK, hN, -, -⟩ := ((hg.toCmp hMB).exec e).toNat_consts
    bfFull_regsOK bfFull_noDivR (show 2 * bfHc b L < bfM b L by unfold bfM; omega) (by omega)
    (by unfold bfWN; omega) (by unfold bfWN; omega) (by unfold bfWN; omega) hS hd
  refine ⟨c', k, e, hk, ⟨E, hv, hout, hbfu, fun v hv' => ?_⟩, ho, hMB', d', k', e', by omega, hS',
    hK, hN⟩
  rw [← hv v hv']; exact hMB' _ (by omega)

/-- **The values on natural words**: in the final natural configuration of `bfFull_exec_nat`,
the residue at `β + (5b + 2 + v)` gives back the value `E v`. -/
theorem bfFull_val_nat {E : ℕ → ℤ} {c' d' : Config} {v : ℕ} (hv : c'.rmem (5 * b + 2 + v) = E v)
    (hE : |(E v : ℝ)| ≤ bfB b L) (hS' : Sim 85 (bfWP b) (bfM b L) (bfWP b + 1) c' d')
    (hvb : v < b) :
    ((E v : ℤ) : ℝ) = if d'.nmem (bfWP b + 1 + (5 * b + 2 + v)) ≤ bfHc b L then
      (d'.nmem (bfWP b + 1 + (5 * b + 2 + v)) : ℝ)
      else (d'.nmem (bfWP b + 1 + (5 * b + 2 + v)) : ℝ) - bfM b L := by
  have hWb : bfWP b = 8 * (b * b) + 14 * b + 12 := rfl
  have hres := hS'.rmem (5 * b + 2 + v) (by omega)
  rw [hv] at hres
  refine hres.signed (hE.trans ?_) (by unfold bfM; omega)
  unfold bfHc; push_cast; linarith [(Nat.cast_nonneg (bfB b L) : (0 : ℝ) ≤ _)]

/-- **Bellman–Ford on natural words from an integer start**: if the real registers `< 85` and
the real memory `≤ bfWP b` of the start are integers (the memory bounded by `bfB b L`), the
natural program runs from `natOf 85 (bfWP b) (bfM b L) (bfWP b + 1) c` as in
`bfFull_exec_nat`. -/
theorem bfFull_exec_nat_of_int (hπ : IsPermB b π) (hD₁ : CrossingX b X₁ D₁)
    (hD₂ : CrossingX b X₂ D₂) (hL₁ : ∀ s t, s < b → t < b → |(D₁ s t : ℝ)| ≤ L)
    (hL₂ : ∀ s t, s < b → t < b → |(D₂ s t : ℝ)| ≤ L) (c : Config)
    (hw : WordsBounded (bfWP b) c) (hR : BFRegs b c) (hM : BFMem b X₁ D₁ X₂ D₂ π c)
    (hMB : MemB (bfWP b) (bfB b L) c) (hri : ∀ r < 85, ∃ z : ℤ, c.rreg r = z)
    (hmi : ∀ a ≤ bfWP b, ∃ z : ℤ, c.rmem a = z) :
    ∃ c' k, Exec P (bfWP b) bfFull c c' k ∧ k ≤ bfCostP b ∧
      (∃ E : ℕ → ℤ, (∀ v < b, c'.rmem (5 * b + 2 + v) = E v) ∧
        ((c'.nreg 30 = 0 ∧ Feas2O b X₁ D₁ X₂ D₂ π E) ∨
          (c'.nreg 30 = 1 ∧ ¬ ∃ E', Feas2O b X₁ D₁ X₂ D₂ π E')) ∧
        ((∃ E', Feas2O b X₁ D₁ X₂ D₂ π E') → ∀ v < b, E v = bfuO b X₁ D₁ X₂ D₂ π b v) ∧
        ∀ v < b, |(E v : ℝ)| ≤ bfB b L) ∧
      c'.output = c.output ∧
      ∃ d' k', Exec P (bfWN b L) (.seq (constsS 85 (bfM b L) (bfHc b L) (bfWP b + 1))
          (ModNat.toNat 85 (bfM b L) bfFull)) (natOf 85 (bfWP b) (bfM b L) (bfWP b + 1) c) d' k' ∧
        k' ≤ 4 * bfCostP b + 3 ∧ Sim 85 (bfWP b) (bfM b L) (bfWP b + 1) c' d' := by
  have hM0 : 0 < bfM b L := by unfold bfM; omega
  obtain ⟨c', k, e, hk, a1, a2, -, d', k', e', hk', hS', -⟩ :=
    bfFull_exec_nat (P := P) hπ hD₁ hD₂ hL₁ hL₂ c hw hR hM hMB (sim_natOf (by omega) hM0 hri hmi)
      (natOf_wb hw (by unfold bfWN; omega) (by unfold bfWN; omega) hM0)
  exact ⟨c', k, e, hk, a1, a2, d', k', e', hk', hS'⟩

theorem bfNat_ok : (Stmt.seq (constsS 85 (bfM b L) (bfHc b L) (bfWP b + 1))
      (ModNat.toNat 85 (bfM b L) bfFull)).regsOK (fun r => decide (r < 174)) = true ∧
    (Stmt.seq (constsS 85 (bfM b L) (bfHc b L) (bfWP b + 1))
      (ModNat.toNat 85 (bfM b L) bfFull)).noInp = true ∧
    (Stmt.seq (constsS 85 (bfM b L) (bfHc b L) (bfWP b + 1))
      (ModNat.toNat 85 (bfM b L) bfFull)).noRand = true := by
  obtain ⟨a1, a2, a3⟩ := toNat_ok (M := bfM b L) bfFull_regsOK bfFull_noInp bfFull_noRand
  simp only [Stmt.regsOK, Stmt.noInp, Stmt.noRand, Bool.and_eq_true]
  refine ⟨⟨by simp [constsS, block, Stmt.regsOK, Instr.regsOK, Instr.regs], a1⟩,
    ⟨by simp [constsS, block, Stmt.noInp, Instr.notInp], a2⟩,
    ⟨by simp [constsS, block, Stmt.noRand, Instr.noRand], a3⟩⟩

/-- **Bellman–Ford on natural words, inside a larger configuration.** The real configuration `d`
is that of `bfFull_exec_emb`, its real memory `≤ bfWP b` bounded by `bfB b L`, the lengths
bounded by `L`; the natural configuration `dN`, with any word bound `WN ≥ bfWN b L`, holds the
residues of the reals of `d` (`Sim`) and has its registers `< 174` and its memory `≤ bfWN b L`
bounded by `bfWN b L`. Then `bfFull` runs from `d` as in `bfFull_exec_emb` (to `d'`), and the
natural program runs from `dN` within `4 bfCostP b + 3` steps to a configuration holding the
residues of the reals of `d'`, keeping the registers `≥ 174` and the memory above `bfWN b L`. -/
theorem bfFull_exec_emb_nat (hπ : IsPermB b π) (hD₁ : CrossingX b X₁ D₁)
    (hD₂ : CrossingX b X₂ D₂) (hL₁ : ∀ s t, s < b → t < b → |(D₁ s t : ℝ)| ≤ L)
    (hL₂ : ∀ s t, s < b → t < b → |(D₂ s t : ℝ)| ≤ L) {W' : ℕ} (hW : bfWP b ≤ W') (d : Config)
    (hd : WordsBounded W' d) (hR : BFRegs b d) (hM : BFMem b X₁ D₁ X₂ D₂ π d)
    (hrb : ∀ r < 85, d.nreg r ≤ bfWP b) (hmb : ∀ a ≤ bfWP b, d.nmem a ≤ bfWP b)
    (hMB : MemB (bfWP b) (bfB b L) d) {WN : ℕ} (hWN : bfWN b L ≤ WN) {dN : Config}
    (hS : Sim 85 (bfWP b) (bfM b L) (bfWP b + 1) d dN) (hdN : WordsBounded WN dN)
    (hdNr : ∀ r < 174, dN.nreg r ≤ bfWN b L) (hdNm : ∀ a ≤ bfWN b L, dN.nmem a ≤ bfWN b L) :
    ∃ d' k, Exec P W' bfFull d d' k ∧ k ≤ bfCostP b ∧
      (∃ E : ℕ → ℤ, (∀ v < b, d'.rmem (5 * b + 2 + v) = E v) ∧
        ((d'.nreg 30 = 0 ∧ Feas2O b X₁ D₁ X₂ D₂ π E) ∨
          (d'.nreg 30 = 1 ∧ ¬ ∃ E', Feas2O b X₁ D₁ X₂ D₂ π E')) ∧
        ((∃ E', Feas2O b X₁ D₁ X₂ D₂ π E') → ∀ v < b, E v = bfuO b X₁ D₁ X₂ D₂ π b v) ∧
        ∀ v < b, |(E v : ℝ)| ≤ bfB b L) ∧
      d'.output = d.output ∧ (∀ r, 85 ≤ r → d'.nreg r = d.nreg r) ∧
      (∀ r, 85 ≤ r → d'.rreg r = d.rreg r) ∧ (∀ a, bfWP b < a → d'.nmem a = d.nmem a) ∧
      (∀ a, bfWP b < a → d'.rmem a = d.rmem a) ∧ MemB (bfWP b) (bfB b L) d' ∧
      ∃ dN' k', Exec P WN (.seq (constsS 85 (bfM b L) (bfHc b L) (bfWP b + 1))
          (ModNat.toNat 85 (bfM b L) bfFull)) dN dN' k' ∧ k' ≤ 4 * bfCostP b + 3 ∧
        Sim 85 (bfWP b) (bfM b L) (bfWP b + 1) d' dN' ∧
        (∀ r, 174 ≤ r → dN'.nreg r = dN.nreg r) ∧ (∀ a, bfWN b L < a → dN'.nmem a = dN.nmem a) := by
  -- the real run, on the truncation
  set c := trunc bfU (bfWP b) d with hcdef
  have hA := agree_trunc bfU (bfWP b) d
  have hn : ∀ r < 85, c.nreg r = d.nreg r := fun r hr => (hA.nreg r (by simp [bfU, hr])).symm
  have hnr : ∀ r < 85, c.rreg r = d.rreg r := fun r hr => (hA.rreg r (by simp [bfU, hr])).symm
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
  have hMBc : MemB (bfWP b) (bfB b L) c := fun a ha => by rw [hrm a ha]; exact hMB a ha
  have hg := bfFull_good (P := P) hπ hD₁ hD₂ hL₁ hL₂ c hw hRc hMc
  have hMB' := hg.mem e hMBc
  -- the natural run, on the truncation of `dN`
  have hSc : Sim 85 (bfWP b) (bfM b L) (bfWP b + 1) c dN :=
    ⟨fun r hr => by rw [hS.nreg r hr, hn r hr], fun r hr => by rw [hnr r hr]; exact hS.rreg r hr,
      fun a ha => by rw [hS.nmem a ha, hm a ha], fun a ha => by rw [hrm a ha]; exact hS.rmem a ha,
      hS.output⟩
  set U : ℕ → Bool := fun r => decide (r < 174) with hU
  set dNt := trunc U (bfWN b L) dN with hdNt
  have hB := agree_trunc U (bfWN b L) dN
  have hWf : 2 * bfWP b + 1 ≤ bfWN b L := by unfold bfWN; omega
  have hSt : Sim 85 (bfWP b) (bfM b L) (bfWP b + 1) c dNt :=
    ⟨fun r hr => by rw [← hB.nreg r (by simp [hU]; omega)]; exact hSc.nreg r hr,
      fun r hr => by rw [← hB.nreg _ (by simp [hU]; omega)]; exact hSc.rreg r hr,
      fun a ha => by rw [← hB.nmem a (by omega)]; exact hSc.nmem a ha,
      fun a ha => by rw [← hB.nmem _ (by omega)]; exact hSc.rmem a ha, hSc.output⟩
  have hwt : WordsBounded (bfWN b L) dNt :=
    wordsBounded_trunc (fun r hr => hdNr r (by simpa [hU] using hr)) hdNm
  obtain ⟨dt', kt, et, hkt, hSt', -, -, -, -, -⟩ := ((hg.toCmp hMBc).exec e).toNat_consts
    bfFull_regsOK bfFull_noDivR (show 2 * bfHc b L < bfM b L by unfold bfM; omega) (by omega)
    (by unfold bfWN; omega) (by unfold bfWN; omega) (by unfold bfWN; omega) hSt hwt
  obtain ⟨ok1, ok2, ok3⟩ := bfNat_ok (b := b) (L := L)
  obtain ⟨dN', eN, hAN, hKN, hoN⟩ := Exec.lift_trunc (P' := P) et ok1 ok2 ok3 hWN hdN
  have h30 : d'.nreg 30 = c'.nreg 30 := hA'.nreg 30 (by decide)
  refine ⟨d', k, e', hk, ⟨E, fun v hv' => ?_, by rw [h30]; exact hout, hbfu, fun v hv' => ?_⟩,
    by rw [ho', ho]; rfl, fun r hr => hK.nreg r (by simp [bfU]; omega),
    fun r hr => hK.rreg r (by simp [bfU]; omega), hK.nmem, hK.rmem,
    fun a ha => by rw [hA'.rmem a ha]; exact hMB' a ha,
    dN', kt, eN, by omega, ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_,
      fun a ha => ?_, ?_⟩, fun r hr => hKN.nreg r (by simp [hU]; omega), hKN.nmem⟩
  · rw [hA'.rmem _ (by omega)]; exact hv v hv'
  · rw [← hv v hv']; exact hMB' _ (by omega)
  · rw [hAN.nreg r (by simp [hU]; omega), hSt'.nreg r hr, hA'.nreg r (by simp [bfU, hr])]
  · rw [hAN.nreg _ (by simp [hU]; omega), hA'.rreg r (by simp [bfU, hr])]; exact hSt'.rreg r hr
  · rw [hAN.nmem a (by omega), hSt'.nmem a ha, hA'.nmem a ha]
  · rw [hAN.nmem _ (by omega), hA'.rmem a ha]; exact hSt'.rmem a ha
  · rw [hoN, hSt'.output, ho']

end NegSSSP

end PlanarFlow
