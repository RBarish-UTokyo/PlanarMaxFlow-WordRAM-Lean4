module

public import PlanarFlow.Klein.CmpEmbed
public import PlanarFlow.Klein.NL.ExecEnc
public import PlanarFlow.Klein.NL.ProgInit
public import PlanarFlow.Klein.NL.ProgInitC
public import PlanarFlow.Klein.NL.ProgMove
public import PlanarFlow.Klein.NL.ProgMoveC
public import PlanarFlow.Klein.NL.ProgNext
public import PlanarFlow.Klein.NL.ProgNextC
public import PlanarFlow.Klein.NL.ProgPivot
public import PlanarFlow.Klein.NL.ProgPivotC
public import PlanarFlow.Klein.NL.ProgTrip
public import PlanarFlow.Klein.NL.ProgTripC
public import PlanarFlow.Klein.NL.ProgWeight
public import PlanarFlow.Klein.NL.ProgWeightC
public import PlanarFlow.Klein.NL.Input

/-! Copy of `PlanarFlow.Klein.CmpEmbed` for `KInputNL` (generated mechanically). -/

@[expose] public section

namespace WordRAM

namespace Machine

namespace ModNat

namespace ExecCmp

open Stmt

variable {P P' : Input} {W H : ℕ}

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
(`kleinHI ≤ Hc`): under the hypotheses of `klein_exec_of_encNL`, every run of `kleinProgMem` on
any input from a configuration `d` holding the encoding (`KleinEnc`) compares only reals within
`Hc` of each other (`ModNat.CmpOK`). -/
theorem kleinProgMem_cmpOKNL {P P' : Input} {B : ℕ} (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ B)
    (hB : n + 2 * nD ≤ B) (hOUT : aOUT nD + k * t ≤ B) (hRB : aRB n + k * t ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1))
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInputNL M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
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
  obtain ⟨c', steps, e, -, -, -, -⟩ := klein_execNL hWa hB hOUT hRB hP H hR hL hK
    hG hO hX hI hoff hCr hT hw hwt hph htl hth hh0
  have ec := (kleinProg_cmpOKNL hWa hB hOUT hRB hP H hR hL hK hG hO hX hI hoff hCr hT hw hwt hph
    htl hth hh0 hHc).exec e
  obtain ⟨d', k', e', -⟩ :=
    ModNat.ExecCmp.embed (P' := P') (tmp := 201) ec (kleinProg_regsOK B nD n k t) hW
      (Or.inl (kleinProg_noRand B nD n k t)) d hA hd (Or.inr ⟨hE.dat, by decide⟩)
  intro d₂ k₂ e₂
  obtain ⟨rfl, rfl⟩ := Exec.det e₂ e'.toExec
  exact e'

end Klein

end PlanarFlow
