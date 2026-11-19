module

public import PlanarFlow.NegSSSP.SplitRunY

/-!
# The split in the large case, exporting the data of the piece map

**`splitProg_big`**: `splitProg` (as `splitProg_splitM`, same hypotheses, same bound `splitT k`)
on a piece with a component of more than three quarters of its darts ends in the large case
(`bigProg`) with everything `bigProg_spec''` exports about the final configuration: for a dart
`x₁` of the large component `K = pcomp N Pc x₁`, the cut `A₀` (`CutOK`), the sides, the
positions (`PosInst`), the piece map's numberings `cn vn fn`, `ψ`, the cycle `C` and the faces
`Z` of the side, the plain encoding `Enc (kmap N K)` at `B₀ + 28k + 3`, the marks of `Z` at
`B₀ + 22m'`, the index array at `B₀ + 25k + 3`, the flags of `K` at `B₀ + 33k + 3`, the sizes in
registers. The proof is that of `splitProg_splitM`, with `bigProg_spec''` in the large case and
the small case excluded.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

section Big

open Orbit CombMap BKMNW PlanarSeparator PlanarSeparator.MillerProg PlanarSeparator.StDart

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}
variable {Pc : Finset D} {m k : ℕ} {δ : ℕ → D} {α σ : ℕ → ℕ}

open Classical in
/-- **What the split exports in the large case** (the conclusion of `bigProg_spec''` for the
component `pcomp N Pc x₁`, about the final configuration `c'`). -/
def BigOut (N : CombMap D V F) (Pc : Finset D) (m k : ℕ) (δ : ℕ → D) (B₀ : ℕ) (x₁ : D)
    (c' : Config) : Prop :=
  ∃ A₀, CutOK N (pcomp N Pc x₁) A₀ ∧
    (∀ x < m, c'.nmem (B₀ + 41 * k + 4 + x) =
      if δ x ∈ (cutPair Pc (pcomp N Pc x₁) A₀).1 then 0 else 1) ∧
    ∃ (nV nF q : ℕ) (ν : V → ℕ), (∀ v, ν v < nV) ∧ nV + nF ≤ 2 * k ∧
      q ≤ 6 * Nat.sqrt (12 * (pcomp N Pc x₁).card) + 4 ∧
      PosInst N (cutPair Pc (pcomp N Pc x₁) A₀).1 (bdry N A₀ (pcomp N Pc x₁ \ A₀))
        (18 * (pcomp N Pc x₁).card) q c'.nmem (B₀ + 42 * k + 4 + 2 * (nV + nF)) ν ∧
      PosInst N (cutPair Pc (pcomp N Pc x₁) A₀).2 (bdry N A₀ (pcomp N Pc x₁ \ A₀))
        (18 * (pcomp N Pc x₁).card) q c'.nmem (B₀ + 54 * k + 7 + 2 * (nV + nF)) ν ∧
      ∃ (m' : ℕ) (cn : SDart (rcl N (pcomp N Pc x₁)) ≃ Fin m')
        (vn : SVert (kσ N (pcomp N Pc x₁)) (rcl N (pcomp N Pc x₁)) ≃ Fin nV)
        (fn : (kmap N (pcomp N Pc x₁)).Face ≃ Fin nF)
        (ψ : V → SVert (kσ N (pcomp N Pc x₁)) (rcl N (pcomp N Pc x₁)))
        (C : (kst N (pcomp N Pc x₁)).SCycle) (Z : Finset (kst N (pcomp N Pc x₁)).Face),
        m' ≤ k ∧ (∀ v, ν v = vn (ψ v)) ∧ q = C.k ∧
        (∀ x : SDart (rcl N (pcomp N Pc x₁)),
          ψ (N.tail x.1) = (kmap N (pcomp N Pc x₁)).vert x) ∧
        side N (pcomp N Pc x₁) Z = A₀ ∧ side N (pcomp N Pc x₁) Zᶜ = pcomp N Pc x₁ \ A₀ ∧
        (∀ δ, ((kst N (pcomp N Pc x₁)).face δ ∈ Z ↔
          (kst N (pcomp N Pc x₁)).face ((kst N (pcomp N Pc x₁)).α δ) ∈ Z) ↔ ¬ C.Mem δ) ∧
        (∀ δ, ((kst N (pcomp N Pc x₁)).face δ ∈ Zᶜ ↔
          (kst N (pcomp N Pc x₁)).face ((kst N (pcomp N Pc x₁)).α δ) ∈ Zᶜ) ↔ ¬ C.Mem δ) ∧
        (∀ b ∈ bdry N A₀ (pcomp N Pc x₁ \ A₀), Sum.inl (ψ b) ∈ C.verts) ∧
        Enc (kmap N (pcomp N Pc x₁)) cn vn fn c'.nmem (B₀ + 28 * k + 3)
          (B₀ + 28 * k + 3 + m') (B₀ + 28 * k + 3 + 2 * m') (B₀ + 28 * k + 3 + 3 * m')
          (B₀ + 28 * k + 3 + 4 * m') ∧
        (∀ x, (kst N (pcomp N Pc x₁)).face (old x) ∈ Z ↔ c'.nmem (B₀ + 22 * m' + cn x) = 1) ∧
        (∀ x, (kst N (pcomp N Pc x₁)).face (old x) ∈ Zᶜ ↔
          c'.nmem (B₀ + 22 * m' + cn x) = 0) ∧
        (∀ h < k, ∀ hm : δ h ∈ rcl N (pcomp N Pc x₁),
          c'.nmem (B₀ + 25 * k + 3 + h) = cn ⟨δ h, hm⟩) ∧
        (∀ x < m, (c'.nmem (B₀ + 33 * k + 3 + x) ≠ 0 ↔ δ x ∈ pcomp N Pc x₁)) ∧
        c'.nreg 960 = m' ∧ c'.nreg 961 = nV ∧ c'.nreg 962 = nF ∧
        c'.nreg 800 = m' ∧ c'.nreg 801 = B₀ + 28 * k + 3 ∧
        c'.nreg 802 = B₀ + 28 * k + 3 + m' ∧ c'.nreg 803 = B₀ + 28 * k + 3 + 2 * m' ∧
        c'.nreg 804 = B₀ + 28 * k + 3 + 3 * m' ∧ c'.nreg 805 = B₀ + 28 * k + 3 + 4 * m' ∧
        c'.nreg 807 = nV ∧ c'.nreg 808 = nF

set_option maxHeartbeats 16000000 in
open Classical in
/-- **The split in the large case, exporting the data of the piece map.** -/
theorem splitProg_big (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    (hPr : Pc ⊆ reps N) (he : PEnc N Pc m k δ α σ) {bα bσ bF B₀ : ℕ} (c₀ : Config)
    (hc : WordsBounded W c₀) (r10 : c₀.nreg 10 = 1) (r860 : c₀.nreg 860 = m)
    (r861 : c₀.nreg 861 = k) (r862 : c₀.nreg 862 = bα) (r863 : c₀.nreg 863 = bσ)
    (r865 : c₀.nreg 865 = bF) (r950 : c₀.nreg 950 = B₀)
    (hα : ∀ h < k, c₀.nmem (bα + h) = α h) (hσ : ∀ h < k, c₀.nmem (bσ + h) = σ h)
    (lα : bα + k ≤ B₀) (lσ : bσ + k ≤ B₀) (lF : bF + m ≤ B₀)
    (dα : bF + m ≤ bα ∨ bα + k ≤ bF) (dσ : bF + m ≤ bσ ∨ bσ + k ≤ bF)
    (hB : aEnd10 (3 * k) (3 * k) ≤ B₀) (hW : B₀ + 66 * k + 35 ≤ W)
    (hlo : ∀ a ≤ B₀ + 25 * k + 2, c₀.nmem a ≤ B₀ + 25 * k + 2)
    (hbig0 : ∃ x ∈ Pc, 3 * Pc.card / 4 < (pcomp N Pc x).card) :
    ∃ c' t, Exec P W splitProg c₀ c' t ∧ t ≤ splitT k ∧
      (∀ a, B₀ + 66 * k + 10 ≤ a → c'.nmem a = c₀.nmem a) ∧
      (∀ r, 972 ≤ r → c'.nreg r = c₀.nreg r) ∧
      ∃ x₁ ∈ Pc, 3 * Pc.card / 4 < (pcomp N Pc x₁).card ∧ BigOut N Pc m k δ B₀ x₁ c' := by
  have hmk := he.mle
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
  · -- the small case is excluded
    exfalso
    obtain ⟨x, hx, hxb⟩ := hbig0
    have := hsmall x hx
    omega
  · -- the large case
    set x₁ := δ (c₂.nreg 857)
    have hx₁ : x₁ ∈ Pc := he.enumP.mem _ hlt
    have hF₂ : ∀ x < m, (c₂.nmem (bF + x) ≠ 0 ↔ δ x ∈ pcomp N Pc x₁) :=
      flags_big hbig hFl he.enumP.mem
    obtain ⟨c₃, t₃, e₃, ht₃, F3m, F3r, rest⟩ :=
      bigProg_spec'' (P := P) hM hrot hface hPr he hx₁ c₂ e₂.wb_right
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
      fun r hr => ?_, x₁, hx₁, hbig, rest⟩
    · unfold splitT
      clear * - ht₁ ht₂ ht₃ hmk
      generalize bigT k = S at ht₃ ⊢
      omega
    · rw [F3m a (by omega), M2 a (by omega)]
    · rw [F3r r hr, S2 r (by omega), fr₁ r (by omega) (by omega)]

end Big

end NegSSSP

end PlanarFlow
