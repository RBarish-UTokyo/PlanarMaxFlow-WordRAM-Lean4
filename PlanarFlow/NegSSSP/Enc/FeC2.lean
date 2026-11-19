module

public import PlanarFlow.NegSSSP.Enc.FeC

/-!
# The composed encoder, phase C: the search of the piece

* `feBfs`, **`feBfs_exec`**: `bfsProg` on the out-lists of the piece (`FeOut`) from the vertex
  `x`: the marks at `MK + τ y` are **the reach bits `[Reach (pieceGraph M' S' ℓ') x y]`** (any
  lengths `ℓ'`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Relation Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {σ₀ : D ≃ Fin (Fintype.card D)} {νv₀ : V ≃ Fin (Fintype.card V)}
  {τ₀ : F ≃ Fin (Fintype.card F)}

/-! ### The search of the piece -/

/-- The registers of `bfsProg` on the out-lists of the piece, from the vertex number `x0`. -/
def feBfsRegs (p : FeP) (x0 : ℕ) : List (ℕ × ℕ) :=
  [(1400, p.A), (1401, x0), (1402, p.β + iOB p.N p.NN p.k), (1403, p.β + iOE p.N p.NN p.k),
    (1404, p.β + iOL p.N p.NN p.k), (1405, p.β + 5 * p.N), (1406, p.MK), (1407, p.MK + p.A)]

/-- **The search of the piece from the vertex number `x0`.** -/
def feBfs (p : FeP) (x0 : ℕ) : Stmt := .seq (feSet (feBfsRegs p x0)) bfsProg

theorem feBfs_natOnly (p : FeP) (x0 : ℕ) : natOnly (feBfs p x0) = true := by
  have h : natOnly bfsProg = true := by kernel_rfl
  simp only [feBfs, natOnly, feSet_natOnly, h, Bool.and_self]

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The reach bits of the piece on the machine** (from the vertex `x`). -/
theorem feBfs_exec (hf : MSSP.FaceCycle M k g) (p : FeP) (hD : p.nD = Fintype.card D)
    (hk : p.k = k) (hV : p.nV = Fintype.card V) (hF : p.nF = Fintype.card F) (hW : p.END ≤ W)
    (ℓ' : SrcD D k → ℤ) (x : SrcV V k) (c : Config) (hc : WordsBounded W c)
    (hA : SrcArrM M k g S ℓ σ₀ νv₀ τ₀ p.β p.SL p.N p.A p.AE c.nmem)
    (hO : FeOut S σ₀ νv₀ hf p c.nmem) :
    ∃ c' t, Exec P W (feBfs p (srcVNum νv₀ x)) c c' t ∧ t ≤ 8 + (35 * p.A + 17 * p.N + 12) ∧
      (∀ y, c'.nmem (p.MK + srcVNum νv₀ y) =
        if MSSP.Reach (MSSP.pieceGraph (srcMap hf) (srcPiece k S) ℓ') x y then 1 else 0) ∧
      (∀ a, a < p.MK ∨ p.MK + 2 * p.A ≤ a → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨cD, cV, -⟩ := fe_cards p hD hk hV hF
  obtain ⟨hOM, mm, hmm, hbe, hol, hdeg⟩ := hO
  obtain ⟨l1, l2, l3⟩ : p.β + (8 * p.N + 3 * p.NN + p.k) + p.N ≤ p.MK ∧
      p.MK + 2 * p.A + 1 ≤ W ∧ p.A ≤ p.NN := by
    have hE := p.eqs; have hsl := p.slot_le; clear * - hE hsl hW; omega
  have hx : (srcVNum νv₀ x : ℕ) < p.A := by have := (srcVNum νv₀ x).2; omega
  obtain ⟨c₁, k₁, e₁, hk₁, hn₁, hr₁, hm₁, hrm₁, ho₁⟩ :=
    feSet_exec (P := P) (feBfsRegs p (srcVNum νv₀ x)) (by
      intro q hq; simp only [feBfsRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [iOB, iOE, iOL] <;> clear * - l1 l2 l3 hx <;> omega) c hc
  have hinj : Function.Injective fun x : SrcV V k => (srcVNum νv₀ x : ℕ) :=
    fun a b h => (srcVNum νv₀).injective (Fin.ext h)
  have hm' : ∀ a, c₁.nmem a = c.nmem a := fun a => by rw [hm₁]
  obtain ⟨hsnd, hcmp⟩ := outMem_snd hf hOM
  have hhd : ∀ d, (fun a => c₁.nmem (p.β + 5 * p.N + a)) (srcNum σ₀ d) =
      (srcVNum νv₀ ((srcMap hf).head d) : ℕ) := fun d => by
    simp only; rw [hm']; exact (hA.arrays hf d).2.2.2.1
  have hσs : ∀ j < Fintype.card (SrcD D k), ∃ d, (srcNum σ₀ d : ℕ) = j :=
    fun j hj => ⟨(srcNum σ₀).symm ⟨j, hj⟩, by simp⟩
  have hL : BfsLay p.A mm (Fintype.card (SrcD D k)) (p.β + iOB p.N p.NN p.k)
      (p.β + iOE p.N p.NN p.k) (p.β + iOL p.N p.NN p.k) (p.β + 5 * p.N) p.MK (p.MK + p.A) p.MK W :=
    ⟨by simp only [iOB, iOE, iOL]; clear * - l1 l2 l3; omega,
      by simp only [iOB, iOE, iOL]; clear * - l1 l2 l3; omega,
      by simp only [iOB, iOE, iOL]; clear * - l1 l2 l3 hmm; omega,
      by rw [cD]; clear * - l1 l2 l3; omega, le_rfl, le_rfl, by clear * - l2; omega⟩
  have hI : BfsIn p.A mm (Fintype.card (SrcD D k)) (srcVNum νv₀ x) (p.β + iOB p.N p.NN p.k)
      (p.β + iOE p.N p.NN p.k) (p.β + iOL p.N p.NN p.k) (p.β + 5 * p.N)
      (fun u => c₁.nmem (p.β + iOB p.N p.NN p.k + u)) (fun u => c₁.nmem (p.β + iOE p.N p.NN p.k + u))
      (fun i => c₁.nmem (p.β + iOL p.N p.NN p.k + i)) (fun a => c₁.nmem (p.β + 5 * p.N + a))
      c₁.nmem := by
    refine ⟨hx, fun _ _ => rfl, fun _ _ => rfl, fun u hu => ?_, fun u hu => ?_, fun _ _ => rfl,
      fun i hi => ?_, fun _ _ => rfl, fun a ha => ?_, ?_⟩
    · simp only [hm']; exact (hbe u hu).1
    · simp only [hm']; exact (hbe u hu).2
    · simp only [hm']; rw [cD]; exact hol i hi
    · obtain ⟨d, rfl⟩ := hσs a ha
      have e := hhd d; simp only at e; rw [e]; rw [← cV]; exact (srcVNum νv₀ _).2
    · simp only [hm']; exact hdeg
  obtain ⟨c₂, k₂, e₂, hk₂, hR, hm₂, -, hr₂, hrm₂, ho₂⟩ :=
    bfsProg_reach (P := P) (M := srcMap hf) (S := srcPiece k S) (ℓ := ℓ') (srcNum σ₀) hinj
      (ob := fun u => c₁.nmem (p.β + iOB p.N p.NN p.k + u))
      (oe := fun u => c₁.nmem (p.β + iOE p.N p.NN p.k + u))
      (ol := fun i => c₁.nmem (p.β + iOL p.N p.NN p.k + i))
      (hd := fun a => c₁.nmem (p.β + 5 * p.N + a))
      (fun y i h1 h2 => by simp only [hm'] at h1 h2 ⊢; exact hsnd y i h1 h2)
      (fun d hd => by simp only [hm']; exact hcmp d hd) hhd (x := x) hL c₁ e₁.wb_right
      (by rw [hn₁]; simp [feBfsRegs, feSetV]) (by rw [hn₁]; simp [feBfsRegs, feSetV])
      (by rw [hn₁]; simp [feBfsRegs, feSetV]) (by rw [hn₁]; simp [feBfsRegs, feSetV])
      (by rw [hn₁]; simp [feBfsRegs, feSetV]) (by rw [hn₁]; simp [feBfsRegs, feSetV])
      (by rw [hn₁]; simp [feBfsRegs, feSetV]) (by rw [hn₁]; simp [feBfsRegs, feSetV]) hI
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by simp [feBfsRegs] at hk₁; clear * - hk₁ hk₂ hmm; omega,
    fun y => hR y (by rw [← cV]; exact (srcVNum νv₀ y).2), fun a ha => ?_,
    by rw [hr₂, hr₁], by rw [hrm₂, hrm₁], by rw [ho₂, ho₁]⟩
  rw [hm₂ a (by clear * - ha; omega), hm']

end NegSSSP

end PlanarFlow
