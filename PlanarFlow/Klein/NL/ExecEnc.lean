module

public import PlanarFlow.Klein.ExecEnc
public import PlanarFlow.Klein.NL.ProgInit
public import PlanarFlow.Klein.NL.ProgMove
public import PlanarFlow.Klein.NL.ProgNext
public import PlanarFlow.Klein.NL.ProgPivot
public import PlanarFlow.Klein.NL.ProgTrip
public import PlanarFlow.Klein.NL.ProgWeight
public import PlanarFlow.Klein.NL.Input

/-! Copy of `PlanarFlow.Klein.ExecEnc` for `KInputNL` (generated mechanically). -/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ} {nD : ℕ}
  {σ : D ≃ Fin nD} {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} {t : ℕ}
  {X : ℕ → V}

local notation "𝒢" => pieceGraph M S ℓ

/-- **Klein's algorithm from any configuration holding the encoding.** Under the hypotheses of
`klein_execNL` on the input words `P`, from any configuration `d` bounded by `W'` holding the
encoding (`KleinEnc`), with its registers `< 201` and its memory at addresses
`≤ B + 16 (n + 1)` bounded by `B + 16 (n + 1)`, the program `kleinProgMem` runs on any input
`P'` within three times the bound of `klein_execNL`; it makes the `k` moves of the trip, leaves
the answers `kOut` (distances in the piece from the sources of the moves to the targets) in the
final configuration, keeps the output, the natural registers `> 201`, the real registers
`≥ 201`, and all the memory above `B + 16 (n + 1)` (hence the encoding); the natural memory at
addresses `≤ B + 16 (n + 1)` stays bounded by `B + 16 (n + 1)`. -/
theorem klein_exec_of_encNL {P P' : Input} {B : ℕ} (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ B)
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
    (hE : KleinEnc M k g S ℓ σ B n β W' P d) :
    ∃ d' steps, Exec P' W' (kleinProgMem B nD n k t β P.data.length) d d' steps ∧
      steps ≤ 3 * (140 * (n + 1) + 21 +
        kleinOps (Fintype.card V) (Fintype.card F) nD S.card k t * opCostE n +
        kleinExt (Fintype.card V) (Fintype.card F) nD S.card k t) ∧
      (∃ R : ℕ → MoveData M S, IsTripUpTo M k g S ℓ k R) ∧
      (∀ j < k, ∀ i < t,
        kOut nD n t d' j i = (odist 𝒢 (tripSrc M k g j) (X i)).map ((↑) : ℤ → ℝ)) ∧
      d'.output = d.output ∧ (∀ r, 201 < r → d'.nreg r = d.nreg r) ∧
      (∀ r, 201 ≤ r → d'.rreg r = d.rreg r) ∧
      (∀ a, B + 16 * (n + 1) < a → d'.nmem a = d.nmem a) ∧
      (∀ a, B + 16 * (n + 1) < a → d'.rmem a = d.rmem a) ∧
      (∀ a ≤ B + 16 * (n + 1), d'.nmem a ≤ B + 16 * (n + 1)) := by
  have hσ : ∀ x : D, (σ x : ℕ) < nD := fun x => (σ x).2
  have hW : B + 16 * (n + 1) ≤ W' := by have := hE.dat.le; omega
  set c := trunc kU (B + 16 * (n + 1)) d with hcdef
  have hA := agree_trunc kU (B + 16 * (n + 1)) d
  have hrm : ∀ a ≤ B + 16 * (n + 1), c.rmem a = d.rmem a := fun a ha => (hA.rmem a ha).symm
  have hw : WordsBounded (B + 16 * (n + 1)) c :=
    wordsBounded_trunc (fun r hr => hrb r (by simpa [kU] using hr)) hmb
  obtain ⟨c', steps, e, hsteps, htrip, hdist, hout⟩ := klein_execNL hWa hB hOUT hRB hP H hR hL hK
    hG hO hX hI hoff hCr hT hw
    (fun x => by rw [hrm _ (by have := hσ x; unfold aWT; omega)]; exact hE.wt x)
    (fun x => by rw [hrm _ (by have := hσ x; unfold aPH; omega)]; exact hE.ph x)
    (by rw [hrm _ (by unfold aTL; omega)]; exact hE.tl)
    (by rw [hrm _ (by unfold aTH; unfold aOUT at hOUT; omega)]; exact hE.th)
    (by rw [hrm _ (by unfold aH0; unfold aOUT at hOUT; omega)]; exact hE.h0)
  obtain ⟨d', k', e', -, hk', -, hA', hK', L, o, o'⟩ :=
    Exec.embed (P' := P') (tmp := 201) e (kleinProg_regsOK B nD n k t) hW
      (Or.inl (kleinProg_noRand B nD n k t)) d hA hd (Or.inr ⟨hE.dat, by decide⟩)
  have hLnil : L = [] := by
    have := o; rw [hout] at this
    simpa using this
  refine ⟨d', k', e', hk'.trans (by omega), htrip, fun j hj i hi => ?_, ?_,
    fun r hr => hK'.nreg r (by simp; omega) (fun h => by omega),
    fun r hr => hK'.rreg r (by simp; omega), hK'.nmem, hK'.rmem,
    fun a ha => by rw [hA'.nmem a ha]; exact WordsBounded.nmem e.wb_right a⟩
  · have hji : j * t + i < k * t := by
      have : (j + 1) * t ≤ k * t := Nat.mul_le_mul_right t hj
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    have h1 : aRB n + j * t + i ≤ B + 16 * (n + 1) := by omega
    have h2 : aOUT nD + j * t + i ≤ B + 16 * (n + 1) := by omega
    rw [← hdist j hj i hi]
    unfold kOut
    rw [hA'.nmem _ h1, hA'.rmem _ h2]
  · rw [o', hLnil, List.append_nil]

end Klein

end PlanarFlow
