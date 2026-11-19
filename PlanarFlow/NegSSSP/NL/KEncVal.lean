module

public import PlanarFlow.NegSSSP.KEncVal
public import PlanarFlow.Klein.NL.ExecEnc
public import PlanarFlow.Klein.NL.ProgInit
public import PlanarFlow.Klein.NL.ProgMove
public import PlanarFlow.Klein.NL.ProgNext
public import PlanarFlow.Klein.NL.ProgPivot
public import PlanarFlow.Klein.NL.ProgTrip
public import PlanarFlow.Klein.NL.ProgWeight
public import PlanarFlow.Klein.NL.Input

/-! Copy of `PlanarFlow.NegSSSP.KEncVal` for `KInputNL` (generated mechanically). -/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **The properties of an encoding**: the input words `P` meet the hypotheses of
`klein_exec_of_encNL` for some layout `ιv ιg ιf ιe` of the `n` nodes and some initial tree `T`
and cotree `C` with their orders, the word bound being `B` and the targets `X i`, `i < t`. -/
def KValNL (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ)
    (σ : D ≃ Fin (Fintype.card D)) (n B t : ℕ) (X : ℕ → V) (P : Input) : Prop :=
  ∃ (ιv : V → ℕ) (ιg : D → ℕ) (ιf : F → ℕ) (ιe : D → ℕ) (T : DTree M.dual) (C : DTree M)
    (vs ts : List V) (fs cs : List F),
    9 * Fintype.card D + 7 * n + k + 4 + 2 * t ≤ B ∧ n + 2 * Fintype.card D ≤ B ∧
    aOUT (Fintype.card D) + k * t ≤ B ∧ aRB n + k * t ≤ B ∧
    (∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1)) ∧
    Layout M n ιv ιg ιf ιe ∧ KInputNL M S ℓ σ ιv ιg ιf ιe P ∧ KBnd k g σ n P ∧
    KOut M S σ ιv n k P ∧ KTgt M k g S ℓ (Fintype.card D) n ιv t X P ∧
    KInit M σ ιv ιf n k T C vs ts fs cs P ∧
    (∀ x, x ≠ C.root → ¬ T.InT (C.par x)) ∧ C.root = M.face (g 0) ∧
    Compat T (tripSrc M k g 0) (tripDst M k g 0) (g (0 % k))
      (tpar (pieceGraph M S ℓ) (tripSrc M k g 0))

variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

/-- **Klein's program from any encoding meeting `KVal`** (the conclusion of
`klein_exec_enc_exists`, for the given encoding). -/
theorem klein_exec_valNL (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) {t : ℕ} {X : ℕ → V}
    {n B : ℕ} {σ : D ≃ Fin (Fintype.card D)} {Pk : Input}
    (hn : n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D))
    (hv : KValNL M k g S ℓ σ n B t X Pk) :
      ∀ (P' : Input) (W' β : ℕ) (d : Config), WordsBounded W' d →
        (∀ r < 201, d.nreg r ≤ B + 16 * (n + 1)) →
        (∀ a ≤ B + 16 * (n + 1), d.nmem a ≤ B + 16 * (n + 1)) →
        KleinEnc M k g S ℓ σ B n β W' Pk d →
        ∃ d' steps,
          Exec P' W' (kleinProgMem B (Fintype.card D) n k t β Pk.data.length) d d' steps ∧
          steps ≤ 3 * (36500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
              BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
            k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D))) ∧
          (∃ R : ℕ → MoveData M S, IsTripUpTo M k g S ℓ k R) ∧
          (∀ j < k, ∀ i < t, kOut (Fintype.card D) n t d' j i =
            (odist (pieceGraph M S ℓ) (tripSrc M k g j) (X i)).map ((↑) : ℤ → ℝ)) ∧
          d'.output = d.output ∧ (∀ r, 201 < r → d'.nreg r = d.nreg r) ∧
          (∀ r, 201 ≤ r → d'.rreg r = d.rreg r) ∧
          (∀ a, B + 16 * (n + 1) < a → d'.nmem a = d.nmem a) ∧
          (∀ a, B + 16 * (n + 1) < a → d'.rmem a = d.rmem a) ∧
          (∀ a ≤ B + 16 * (n + 1), d'.nmem a ≤ B + 16 * (n + 1)) := by
  obtain ⟨ιv, ιg, ιf, ιe, T, C, vs, ts, fs, cs, hWa, hB, hOUT, hRB, hP, hL, hK, hG, hO, hXT, hI,
    hoff, hCr, hT⟩ := hv
  intro P' W' β d hd hrb hmb hE
  obtain ⟨d', steps, e, hs, htrip, hdist, ho, h1, h2, h3, h4⟩ :=
    klein_exec_of_encNL (P := Pk) (P' := P') hWa hB hOUT hRB hP H hR hL hK hG hO hXT hI hoff hCr
      hT d hd hrb hmb hE
  refine ⟨d', steps, e, hs.trans ?_, htrip, hdist, ho, h1, h2, h3, h4⟩
  have hk := H.k_le_card
  have h2' := H.face.two_le
  have hS : S.card ≤ Fintype.card D := card_le_univ S
  rw [hn]
  have := klein_steps_le (by omega) hS hk (t := t) (nV := Fintype.card V)
    (nF := Fintype.card F)
  omega

section Src

variable (hf : FaceCycle M k g)

end Src

end Klein

namespace NegSSSP

open Finset BKMNW CombMap WordRAM WordRAM.Machine

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

variable {P : Finset D} {B : Finset V} {q k : ℕ} {DQ VQ FQ : Type u} [Fintype DQ]
  [DecidableEq DQ] [Fintype VQ] [DecidableEq VQ] [Fintype FQ] [DecidableEq FQ]
  {Q : CombMap DQ VQ FQ} {g : ℕ → DQ} {P' : Finset D} {e : D → DQ} {j : V → VQ}

open WordRAM.Machine.Stmt WordRAM.Programs Monge

open Monge.FR

end NegSSSP

end PlanarFlow
